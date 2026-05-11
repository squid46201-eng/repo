-- prometheus-test-deobfuscator -- straight-line block decompiler.
--
-- Translates a single dispatcher block (as returned by extract.lua) into a
-- sequence of IR statements (see ir.lua). Performs only *block-local*
-- analysis: no cross-block dataflow, no control-flow recovery. That is the
-- job of later passes (M3+).
--
-- The block decompiler is intentionally *non-destructive* with regard to
-- the AST: it reads the block's statements and produces a new IR list. We
-- never mutate the source AST.
--
-- Operations performed (in order):
--   1. Build a register-role table (POS/ARGS/UPVALS/GC/RETURN/helpers/
--      general).
--   2. Walk every statement, splitting AssignmentStatement / LocalVar
--      declarations into per-LHS IR statements. Pattern-match well-known
--      shapes (ARG_READ, UPVAL_READ/WRITE, GLOBAL_READ/WRITE,
--      CREATE_CLOSURE, ALLOC_UPVAL, JUMP_CONST, JUMP_COND, RETURN). The
--      remainder fall into LOAD / COPY / CALL / BINOP / UNOP / INDEX_*
--      via heuristics, with UNKNOWN as the fallback.
--   3. Apply intra-block forward inlining of single-use general registers
--      that are written exactly once and read exactly once before being
--      overwritten or reaching the block exit. POS, ARGS, UPVALS, GC are
--      *never* inlined (they have observable VM semantics); RETURN is also
--      never inlined (it is read implicitly at every block exit).
--
-- Output:
--   {
--     id            = blockId,
--     synthetic     = bool,
--     idLo, idHi    = block id range,
--     statements    = { <ir stmt>, ... },     -- final, after inlining
--     rawStatements = { <ir stmt>, ... },     -- before inlining
--     exitKind      = "jump_const" | "jump_cond" | "return" | "fallthrough",
--     exitTarget    = number?  (jump_const)
--     exitTargets   = {trueId, falseId}? (jump_cond)
--   }

local Ast = require("prometheus.ast")
local astu = require("deobfuscator.ast_utils")
local ir = require("deobfuscator.steps.vmify.ir")
local AstKind = Ast.AstKind

local K = ir.kinds

local M = {}

-- ----------------------------------------------------------------------------
-- Tiny helpers.

local function isVar(node)
    return node and node.kind == AstKind.VariableExpression
end

local function isAssignVar(node)
    return node and node.kind == AstKind.AssignmentVariable
end

local function isAssignIdx(node)
    return node and node.kind == AstKind.AssignmentIndexing
end

local function isCall(node)
    return node and node.kind == AstKind.FunctionCallExpression
end

local function isNumber(node)
    return node and node.kind == AstKind.NumberExpression
end

local function isString(node)
    return node and node.kind == AstKind.StringExpression
end

local function isTable(node)
    return node and node.kind == AstKind.TableConstructorExpression
end

local function isIndex(node)
    return node and node.kind == AstKind.IndexExpression
end

local function sameVar(a, b)
    if not a or not b then return false end
    return a.scope and b.scope and a.scope == b.scope and a.id == b.id
end

local function regKey(node)
    return tostring(node.scope) .. ":" .. tostring(node.id)
end

-- ----------------------------------------------------------------------------
-- Build the register-role classifier from a vm descriptor.
--
-- Returns:
--   roleOf(scope, id) -> string|nil
--   roleOfNode(astNode) -> string|nil

function M.buildRoleTable(vm)
    local map = {}
    local function set(node, role)
        if node and node.scope and node.id then
            map[tostring(node.scope) .. ":" .. tostring(node.id)] = role
        end
    end

    set(vm.containerFunc.args[1], "POS")
    set(vm.containerFunc.args[2], "ARGS")
    set(vm.containerFunc.args[3], "UPVALS")
    set(vm.containerFunc.args[4], "GC")
    set(vm.returnReg.regNode,     "RETURN")

    -- Outer wrap roles.
    set(vm.outer.ENV,      "ENV")
    set(vm.outer.NEWPROXY, "NEWPROXY")
    set(vm.outer.UNPACK,   "UNPACK")
    set(vm.outer.GETMT,    "GETMT")
    set(vm.outer.SELECT,   "SELECT")
    set(vm.outer.SETMT,    "SETMT")
    set(vm.outer.VARARG,   "VARARG")

    -- Helpers (single-instance ones).
    for kind, h in pairs(vm.helpers) do
        if kind == "CREATE_CLOSURES" then
            for _, hh in ipairs(h) do set(hh.lhs, "CREATE_CLOSURE") end
        elseif type(h) == "table" and h.lhs then
            set(h.lhs, kind)
        end
    end

    local function roleOf(scope, id)
        return map[tostring(scope) .. ":" .. tostring(id)]
    end
    local function roleOfNode(n)
        if not n or not n.scope or not n.id then return nil end
        return roleOf(n.scope, n.id)
    end
    return roleOf, roleOfNode, map
end

-- Build a quick set of the (scope, id) of every CREATE_CLOSURE helper and
-- whether it's the vararg variant.
local function buildClosureHelperSet(vm)
    local set = {}  -- key -> { isVararg = bool }
    for _, h in ipairs(vm.helpers.CREATE_CLOSURES or {}) do
        set[regKey(h.lhs)] = { isVararg = false }
    end
    if vm.helpers.CREATE_VARARG_CLOSURE then
        set[regKey(vm.helpers.CREATE_VARARG_CLOSURE.lhs)] = { isVararg = true }
    end
    return set
end

-- ----------------------------------------------------------------------------
-- Convert a raw operand expression into IR-friendly form.
--
-- For VariableExpression and AssignmentVariable nodes we produce a
-- registered ref tag (ir.regRef). All other expressions are returned
-- as-is (the IR stores them verbatim).

local function makeOperandConverter(roleOf)
    -- Recursively convert every VariableExpression / AssignmentVariable
    -- node anywhere inside `node` into a register-ref tag. We *clone* nodes
    -- whose internals we need to rewrite so we never mutate the source AST.
    local conv
    local function cloneNodeShallow(n)
        local r = {}
        for k, v in pairs(n) do r[k] = v end
        return r
    end
    conv = function(node)
        if node == nil then return nil end
        if type(node) ~= "table" then return node end
        if ir.isReg(node) then return node end
        if not node.kind then return node end

        if isVar(node) or isAssignVar(node) then
            local role = roleOf(node.scope, node.id) or "GENERAL"
            return ir.regRef(node.scope, node.id, role)
        end

        local k = node.kind
        if k == AstKind.NumberExpression
           or k == AstKind.StringExpression
           or k == AstKind.BooleanExpression
           or k == AstKind.NilExpression
           or k == AstKind.VarargExpression
           or k == AstKind.FunctionLiteralExpression then
            return node
        end

        local r = cloneNodeShallow(node)
        -- Common single-child fields.
        for _, fname in ipairs({ "lhs", "rhs", "base", "index", "condition", "value", "key" }) do
            if r[fname] ~= nil then r[fname] = conv(r[fname]) end
        end
        -- List fields.
        if type(r.args) == "table" then
            local na = {}
            for i, a in ipairs(r.args) do na[i] = conv(a) end
            r.args = na
        end
        if type(r.entries) == "table" then
            local ne = {}
            for i, e in ipairs(r.entries) do
                if type(e) == "table" and e.kind then
                    local ce = cloneNodeShallow(e)
                    if ce.value ~= nil then ce.value = conv(ce.value) end
                    if ce.key   ~= nil then ce.key   = conv(ce.key)   end
                    ne[i] = ce
                else
                    ne[i] = e
                end
            end
            r.entries = ne
        end
        return r
    end
    return conv
end

-- ----------------------------------------------------------------------------
-- Translate a single LHS/RHS pair into an IR statement (or nil if we
-- decided to skip it, e.g. `R = nil` register-clear in dead context).

local function classifyAssign(lhs, rhs, ctx, sourceStat, sourceIndex)
    -- ctx exposes:
    --   ctx.roleOf(scope, id) -> role
    --   ctx.conv(node) -> operand
    --   ctx.closureHelpers -> { regKey -> { isVararg } }
    --   ctx.vm
    --   ctx.lastExitStat / ctx.lastExitIdx -- ref to the block's true exit
    -- sourceStat/sourceIndex tell us which original statement we're emitting
    -- this IR for (so we can match against ctx.lastExitStat).

    local roleOf  = ctx.roleOf
    local conv    = ctx.conv
    local closureHelpers = ctx.closureHelpers
    local isExitSlot = (sourceStat == ctx.lastExitStat) and (sourceIndex == ctx.lastExitIdx)

    -- LHS: AssignmentVariable, AssignmentIndexing, or LocalVariableDeclaration target.
    local function asReg(n)
        if n.scope and n.id then
            return ir.regRef(n.scope, n.id, roleOf(n.scope, n.id) or "GENERAL")
        end
        return nil
    end

    -- 1) LHS is a register write.
    if isAssignVar(lhs) then
        local target = asReg(lhs)
        local trole  = target and target.role

        -- 1a) Writes to POS are *control flow* only when this is the
        --     final pos-write of the block (i.e. the exit slot). All
        --     intermediate pos-writes are scratch and fall through to the
        --     general-case classification.
        if trole == "POS" and isExitSlot then
            -- Pure constant: JUMP_CONST.
            if isNumber(rhs) then
                return { kind = K.JUMP_CONST, target = rhs.value, raw = { lhs = lhs, rhs = rhs } }
            end
            -- Conditional: (cond and N) or M.
            if rhs.kind == AstKind.OrExpression
               and rhs.lhs and rhs.lhs.kind == AstKind.AndExpression
               and isNumber(rhs.lhs.rhs) and isNumber(rhs.rhs) then
                return {
                    kind        = K.JUMP_COND,
                    cond        = conv(rhs.lhs.lhs),
                    trueTarget  = rhs.lhs.rhs.value,
                    falseTarget = rhs.rhs.value,
                    raw = { lhs = lhs, rhs = rhs },
                }
            end
            -- Return: pos = ENV[<random_string_literal>] (or any ENV indexing
            -- at the exit slot).
            if isIndex(rhs) and isVar(rhs.base)
               and roleOf(rhs.base.scope, rhs.base.id) == "ENV" then
                return { kind = K.RETURN, raw = { lhs = lhs, rhs = rhs } }
            end
            -- Anything else at the exit slot: fall through. (We may want
            -- to flag this as UNKNOWN.)
        end

        -- 1b) Writes to RETURN with a table constructor are the function-
        --     return-tuple form. We emit a regular LOAD for now; the RETURN
        --     marker is emitted separately by the POS = ENV.<rand> exit.
        --     We still emit it so M3+ can fold the return values cleanly.

        -- 1c) Generic register write classification of `target = rhs`:
        --
        --   target = ARGS[i]               -> ARG_READ
        --   target = UPVALS_TABLE[uvId]    -> UPVAL_READ (uvId can be a register that was
        --                                                 freshly allocated, OR an UPVALS[i] index)
        --   target = ENV[name]             -> GLOBAL_READ
        --   target = ALLOC_UPVAL()         -> UPVAL_ALLOC
        --   target = CREATE_CLOSURE_K(N, {ids}) -> CREATE_CLOSURE
        --   target = base[idx]             -> INDEX_READ
        --   target = SOME_CALL(args)       -> CALL (with single target)
        --   target = REG2                  -> COPY
        --   target = constant / expr       -> LOAD

        -- ARG_READ: target = ARGS[expr]
        if isIndex(rhs) and isVar(rhs.base)
           and roleOf(rhs.base.scope, rhs.base.id) == "ARGS" then
            return { kind = K.ARG_READ, target = target, index = conv(rhs.index),
                     raw = { lhs = lhs, rhs = rhs } }
        end

        -- UPVAL_READ: target = UPVALS_TABLE[expr]
        if isIndex(rhs) and isVar(rhs.base)
           and roleOf(rhs.base.scope, rhs.base.id) == "UPVALS_TABLE" then
            return { kind = K.UPVAL_READ, target = target, index = conv(rhs.index),
                     raw = { lhs = lhs, rhs = rhs } }
        end

        -- GLOBAL_READ: target = ENV[expr]
        if isIndex(rhs) and isVar(rhs.base)
           and roleOf(rhs.base.scope, rhs.base.id) == "ENV" then
            return { kind = K.GLOBAL_READ, target = target, name = conv(rhs.index),
                     raw = { lhs = lhs, rhs = rhs } }
        end

        -- UPVAL_ALLOC: target = ALLOC_UPVAL()
        if isCall(rhs) and isVar(rhs.base)
           and roleOf(rhs.base.scope, rhs.base.id) == "ALLOC_UPVAL"
           and (#rhs.args == 0) then
            return { kind = K.UPVAL_ALLOC, target = target, raw = { lhs = lhs, rhs = rhs } }
        end

        -- CREATE_CLOSURE: target = CREATE_CLOSURE_K(N, {ids})
        if isCall(rhs) and isVar(rhs.base) then
            local meta = closureHelpers[regKey(rhs.base)]
            if meta and #rhs.args >= 1 and isNumber(rhs.args[1]) then
                local upvalSlots = {}
                local upvTbl = rhs.args[2]
                if isTable(upvTbl) then
                    for _, e in ipairs(upvTbl.entries or {}) do
                        if e.kind == AstKind.TableEntry then
                            table.insert(upvalSlots, conv(e.value))
                        elseif e.kind == AstKind.KeyedTableEntry then
                            table.insert(upvalSlots, conv(e.value))  -- keyed shouldn't happen; treat as positional
                        end
                    end
                end
                return {
                    kind        = K.CREATE_CLOSURE,
                    target      = target,
                    entryId     = rhs.args[1].value,
                    upvalSlots  = upvalSlots,
                    isVararg    = meta.isVararg,
                    raw         = { lhs = lhs, rhs = rhs },
                }
            end
        end

        -- INDEX_READ: target = base[idx] (for any other base)
        if isIndex(rhs) then
            return { kind = K.INDEX_READ, target = target, base = conv(rhs.base),
                     index = conv(rhs.index), raw = { lhs = lhs, rhs = rhs } }
        end

        -- CALL: target = base(args)
        if isCall(rhs) then
            local args = {}
            for _, a in ipairs(rhs.args) do table.insert(args, conv(a)) end
            return { kind = K.CALL, targets = { target }, base = conv(rhs.base),
                     args = args, raw = { lhs = lhs, rhs = rhs } }
        end

        -- target = {call(...)} -> CALL with tableWrapped=true (multi-return capture)
        if isTable(rhs) and #rhs.entries == 1 then
            local e = rhs.entries[1]
            if e.kind == AstKind.TableEntry and isCall(e.value) then
                local args = {}
                for _, a in ipairs(e.value.args) do table.insert(args, conv(a)) end
                return {
                    kind    = K.CALL,
                    targets = { target },
                    base    = conv(e.value.base),
                    args    = args,
                    tableWrapped = true,
                    raw = { lhs = lhs, rhs = rhs },
                }
            end
        end

        -- COPY: target = REG2 (plain variable reference).
        if isVar(rhs) then
            return { kind = K.COPY, target = target, source = conv(rhs),
                     raw = { lhs = lhs, rhs = rhs } }
        end

        -- BINOP / UNOP / general LOAD.
        local binops = {
            [AstKind.AddExpression]    = "+",
            [AstKind.SubExpression]    = "-",
            [AstKind.MulExpression]    = "*",
            [AstKind.DivExpression]    = "/",
            [AstKind.ModExpression]    = "%",
            [AstKind.PowExpression]    = "^",
            [AstKind.StrCatExpression] = "..",
            [AstKind.LessThanExpression]    = "<",
            [AstKind.GreaterThanExpression] = ">",
            [AstKind.LessThanOrEqualsExpression]    = "<=",
            [AstKind.GreaterThanOrEqualsExpression] = ">=",
            [AstKind.EqualsExpression]    = "==",
            [AstKind.NotEqualsExpression] = "~=",
            [AstKind.AndExpression]       = "and",
            [AstKind.OrExpression]        = "or",
        }
        local unops = {
            [AstKind.NotExpression]    = "not ",
            [AstKind.NegateExpression] = "-",
            [AstKind.LenExpression]    = "#",
        }
        if rhs.kind and binops[rhs.kind] then
            return { kind = K.BINOP, target = target, op = binops[rhs.kind],
                     lhs = conv(rhs.lhs), rhs = conv(rhs.rhs),
                     raw = { lhs = lhs, rhs = rhs } }
        end
        if rhs.kind and unops[rhs.kind] then
            return { kind = K.UNOP, target = target, op = unops[rhs.kind],
                     rhs = conv(rhs.rhs), raw = { lhs = lhs, rhs = rhs } }
        end

        -- Fallback: LOAD (constant, table, function, vararg, ...).
        return { kind = K.LOAD, target = target, value = conv(rhs),
                 raw = { lhs = lhs, rhs = rhs } }
    end

    -- 2) LHS is base[idx] -- INDEX_WRITE / UPVAL_WRITE / GLOBAL_WRITE.
    if isAssignIdx(lhs) then
        if isVar(lhs.base) then
            local baseRole = roleOf(lhs.base.scope, lhs.base.id)
            if baseRole == "UPVALS_TABLE" then
                return { kind = K.UPVAL_WRITE, index = conv(lhs.index),
                         value = conv(rhs), raw = { lhs = lhs, rhs = rhs } }
            elseif baseRole == "ENV" then
                return { kind = K.GLOBAL_WRITE, name = conv(lhs.index),
                         value = conv(rhs), raw = { lhs = lhs, rhs = rhs } }
            end
        end
        return { kind = K.INDEX_WRITE, base = conv(lhs.base),
                 index = conv(lhs.index), value = conv(rhs),
                 raw = { lhs = lhs, rhs = rhs } }
    end

    return { kind = K.UNKNOWN, note = "unhandled LHS form",
             raw = { lhs = lhs, rhs = rhs } }
end

-- ----------------------------------------------------------------------------
-- Walk a block's statement list, splitting AssignmentStatement /
-- LocalVariableDeclaration into per-LHS IR statements.

local function decompileStatements(blockBody, ctx)
    local out = {}
    -- Helper: try to recognize multi-return CALL: `[l1, l2, ...] = call(...)`.
    -- Returns the CALL IR statement on match, or nil otherwise.
    local function tryMultiReturnCall(stat)
        if #stat.lhs <= 1 or #stat.rhs ~= 1 then return nil end
        local rhs = stat.rhs[1]
        if rhs.kind ~= AstKind.FunctionCallExpression
           and rhs.kind ~= AstKind.PassSelfFunctionCallExpression then
            return nil
        end
        for _, lhs in ipairs(stat.lhs) do
            if lhs.kind ~= AstKind.AssignmentVariable then return nil end
        end
        local targets = {}
        for _, lhs in ipairs(stat.lhs) do
            table.insert(targets, ir.regRef(lhs.scope, lhs.id, ctx.roleOfNode(lhs)))
        end
        local args = {}
        for _, a in ipairs(rhs.args) do table.insert(args, ctx.conv(a)) end
        return {
            kind        = K.CALL,
            targets     = targets,
            base        = ctx.conv(rhs.base),
            args        = args,
            passSelfName = (rhs.kind == AstKind.PassSelfFunctionCallExpression)
                           and rhs.passSelfFunctionName or nil,
            sourceStat  = stat,
            sourceIndex = 1,
            multiAssign = true,
            raw         = { lhs = stat.lhs, rhs = rhs },
        }
    end

    for _, stat in ipairs(blockBody.statements) do
        if stat.kind == AstKind.AssignmentStatement then
            -- Multi-return CALL pattern (e.g. for-in's `[var, varB] = iter(...)`).
            local mrc = tryMultiReturnCall(stat)
            if mrc then
                table.insert(out, mrc)
            else
            -- Split each LHS=RHS pair. Lua semantics evaluate all RHS
            -- BEFORE any LHS is written; for multi-assigns containing a
            -- control-flow exit (JUMP_CONST/JUMP_COND/RETURN), the other
            -- assignments must logically be visible to the dispatcher
            -- BEFORE it observes the new POS, so we always emit non-exit
            -- assignments first and any exit assignment last.
            local nonExits, exits = {}, {}
            for i, lhs in ipairs(stat.lhs) do
                local rhs = stat.rhs[i]
                if rhs == nil then
                    rhs = { kind = AstKind.NilExpression }
                end
                local s = classifyAssign(lhs, rhs, ctx, stat, i)
                if s then
                    s.sourceStat = stat
                    s.sourceIndex = i
                    s.multiAssign = (#stat.lhs > 1)
                    if s.kind == K.JUMP_CONST or s.kind == K.JUMP_COND or s.kind == K.RETURN then
                        table.insert(exits, s)
                    else
                        table.insert(nonExits, s)
                    end
                end
            end
            for _, s in ipairs(nonExits) do table.insert(out, s) end
            for _, s in ipairs(exits)    do table.insert(out, s) end
            end
        elseif stat.kind == AstKind.LocalVariableDeclaration then
            -- Local declarations of registers (these are usually only at the
            -- container's top level, not inside individual blocks; we still
            -- handle them defensively).
            for i, id in ipairs(stat.ids) do
                local lhs = { kind = AstKind.AssignmentVariable, scope = stat.scope, id = id }
                local rhs = (stat.expressions or {})[i] or { kind = AstKind.NilExpression }
                local s = classifyAssign(lhs, rhs, ctx, stat, i)
                if s then
                    s.sourceStat = stat
                    s.sourceIndex = i
                    table.insert(out, s)
                end
            end
        elseif stat.kind == AstKind.FunctionCallStatement
               or stat.kind == AstKind.PassSelfFunctionCallStatement then
            -- Bare function call (no result captured).
            local args = {}
            for _, a in ipairs(stat.args) do table.insert(args, ctx.conv(a)) end
            table.insert(out, {
                kind    = K.CALL,
                targets = {},
                base    = ctx.conv(stat.base),
                args    = args,
                sourceStat = stat,
            })
        else
            table.insert(out, {
                kind = K.UNKNOWN,
                note = "unsupported statement kind: " .. tostring(stat.kind),
                sourceStat = stat,
            })
        end
    end
    return out
end

-- ----------------------------------------------------------------------------
-- Single-use forward inliner.
--
-- Walks the IR list once. Maintains a map of (scope, id) -> { stmtIndex,
-- value }. When we see a register WRITE that we can inline (LOAD / COPY /
-- BINOP / UNOP / ARG_READ / UPVAL_READ / GLOBAL_READ / INDEX_READ /
-- CREATE_CLOSURE / CALL with exactly one capture), we store it. When we
-- see a register READ in an operand of a later statement, if the register
-- has a pending inline candidate AND the candidate hasn't been read yet
-- (i.e. it's still single-use as far as we know) AND the candidate is
-- still the most recent definition, we substitute the operand with the
-- candidate's value and remove the candidate's defining statement.
--
-- We bail out (preserve the original statement) for:
--   - registers with role POS, ARGS, UPVALS, GC, RETURN, helpers
--   - candidates that have side-effects (CALL with results other than
--     this register) -- we don't reorder calls
--   - reads from inside multi-target CALLs we've already committed
--
-- This is intentionally conservative; it gives us nice short blocks for
-- the common case without risking semantic divergence.

local INLINEABLE_KINDS = {
    [K.LOAD]           = true,
    [K.COPY]           = true,
    [K.BINOP]          = true,
    [K.UNOP]           = true,
    [K.ARG_READ]       = true,
    [K.UPVAL_READ]     = true,
    [K.GLOBAL_READ]    = true,
    [K.INDEX_READ]     = true,
    [K.CREATE_CLOSURE] = true,
    [K.CALL]           = true,
}

-- We never inline references to *outer* helper variables -- those have
-- distinct semantic meaning (they are the helper functions / tables of the
-- VM) and we want the IR to keep them visible. POS and RETURN are still
-- inlineable when used as *scratch* registers between control-flow exits;
-- their final writes are exit instructions (JUMP_CONST/JUMP_COND/RETURN),
-- which the inliner can't reach because exit instructions have no readers
-- (they are themselves terminal).
local PROTECTED_ROLES = {
    ARGS = true, UPVALS = true, GC = true,
    ENV = true, NEWPROXY = true, UNPACK = true, GETMT = true, SELECT = true,
    SETMT = true, VARARG = true,
    CONTAINER = true, ALLOC_UPVAL = true, FREE_UPVAL = true, PROXY_FN = true,
    GC_FN = true, CREATE_VARARG_CLOSURE = true, UPVALS_TABLE = true,
    REF_COUNTS = true, CURRENT_UPVAL_ID = true, CREATE_CLOSURE = true,
}

-- Build the value expression that an inlineable IR statement produces.
local function inlineValueOf(s)
    local k = s.kind
    if k == K.LOAD       then return s.value end
    if k == K.COPY       then return s.source end
    -- For non-trivial inlines we return a pseudo-AST node carrying enough
    -- info for the IR printer; the actual *expression* shape is stored
    -- under fields specific to each kind. Callers should look at the IR
    -- statement itself rather than re-converting.
    if k == K.BINOP      then return { kind = "_irBinop", op = s.op, lhs = s.lhs, rhs = s.rhs } end
    if k == K.UNOP       then return { kind = "_irUnop",  op = s.op, rhs = s.rhs } end
    if k == K.ARG_READ   then return { kind = "_irArgRead",   index = s.index } end
    if k == K.UPVAL_READ then return { kind = "_irUpvalRead", index = s.index } end
    if k == K.GLOBAL_READ then return { kind = "_irGlobalRead", name = s.name } end
    if k == K.INDEX_READ then return { kind = "_irIndexRead", base = s.base, index = s.index } end
    if k == K.CREATE_CLOSURE then return { kind = "_irClosure", entryId = s.entryId,
        upvalSlots = s.upvalSlots, isVararg = s.isVararg } end
    if k == K.CALL then
        return { kind = "_irCall", base = s.base, args = s.args, tableWrapped = s.tableWrapped }
    end
    return nil
end

-- Collect every register reference inside an operand expression.
local function regsInOperand(node, out)
    out = out or {}
    if not node then return out end
    if ir.isReg(node) then table.insert(out, node); return out end
    if type(node) ~= "table" or not node.kind then return out end
    -- Walk known fields recursively; this works for raw AST nodes and the
    -- _ir* synthetic nodes we attach via inlineValueOf.
    for k, v in pairs(node) do
        if k ~= "scope" and type(v) == "table" then
            if v._isReg then
                table.insert(out, v)
            elseif v.kind then
                regsInOperand(v, out)
            elseif #v > 0 then
                for _, vv in ipairs(v) do regsInOperand(vv, out) end
            end
        end
    end
    return out
end

local function operandsOf(s)
    -- Yield every operand expression of an IR statement (read positions only).
    local k = s.kind
    if k == K.LOAD          then return { s.value } end
    if k == K.COPY          then return { s.source } end
    if k == K.BINOP         then return { s.lhs, s.rhs } end
    if k == K.UNOP          then return { s.rhs } end
    if k == K.CALL          then
        local r = { s.base }
        for _, a in ipairs(s.args) do table.insert(r, a) end
        return r
    end
    if k == K.ARG_READ      then return { s.index } end
    if k == K.UPVAL_READ    then return { s.index } end
    if k == K.UPVAL_WRITE   then return { s.index, s.value } end
    if k == K.UPVAL_ALLOC   then return {} end
    if k == K.UPVAL_INIT    then return { s.slot, s.value } end
    if k == K.GLOBAL_READ   then return { s.name } end
    if k == K.GLOBAL_WRITE  then return { s.name, s.value } end
    if k == K.INDEX_READ    then return { s.base, s.index } end
    if k == K.INDEX_WRITE   then return { s.base, s.index, s.value } end
    if k == K.CREATE_CLOSURE then
        local r = {}
        for _, u in ipairs(s.upvalSlots) do table.insert(r, u) end
        return r
    end
    if k == K.JUMP_CONST    then return {} end
    if k == K.JUMP_COND     then return { s.cond } end
    if k == K.RETURN        then return {} end
    return {}
end

-- Replace a single register operand within a statement with `newExpr`.
-- Returns true if substitution happened.
local function substituteOperand(s, oldRegKey, newExpr)
    local function subst(field, value)
        if value == nil then return false, nil end
        if ir.isReg(value) then
            if regKey(value) == oldRegKey then return true, newExpr end
            return false, value
        end
        if type(value) ~= "table" or not value.kind then return false, value end
        local changed = false
        for k, v in pairs(value) do
            if k ~= "scope" and type(v) == "table" then
                if v._isReg then
                    if regKey(v) == oldRegKey then
                        value[k] = newExpr
                        changed = true
                    end
                elseif v.kind then
                    local ok = select(1, subst(k, v))
                    changed = changed or ok
                elseif #v > 0 then
                    for i, vv in ipairs(v) do
                        if ir.isReg(vv) then
                            if regKey(vv) == oldRegKey then
                                v[i] = newExpr
                                changed = true
                            end
                        elseif type(vv) == "table" and vv.kind then
                            local ok = select(1, subst(i, vv))
                            changed = changed or ok
                        end
                    end
                end
            end
        end
        return changed, value
    end
    local changed = false
    -- We can't iterate Lua tables and modify in place in the same loop;
    -- handle by rebuilding for known operand fields.
    local fieldMap = {
        [K.LOAD]         = { "value" },
        [K.COPY]         = { "source" },
        [K.BINOP]        = { "lhs", "rhs" },
        [K.UNOP]         = { "rhs" },
        [K.CALL]         = { "base", "args" },
        [K.ARG_READ]     = { "index" },
        [K.UPVAL_READ]   = { "index" },
        [K.UPVAL_WRITE]  = { "index", "value" },
        [K.UPVAL_INIT]   = { "slot", "value" },
        [K.GLOBAL_READ]  = { "name" },
        [K.GLOBAL_WRITE] = { "name", "value" },
        [K.INDEX_READ]   = { "base", "index" },
        [K.INDEX_WRITE]  = { "base", "index", "value" },
        [K.CREATE_CLOSURE] = { "upvalSlots" },
        [K.JUMP_COND]    = { "cond" },
    }
    local fields = fieldMap[s.kind] or {}
    for _, fname in ipairs(fields) do
        local v = s[fname]
        if v ~= nil then
            if ir.isReg(v) then
                if regKey(v) == oldRegKey then
                    s[fname] = newExpr
                    changed = true
                end
            elseif type(v) == "table" and v.kind then
                local ok = select(1, subst(fname, v))
                changed = changed or ok
            elseif type(v) == "table" and #v > 0 then
                for i, vv in ipairs(v) do
                    if ir.isReg(vv) then
                        if regKey(vv) == oldRegKey then
                            v[i] = newExpr
                            changed = true
                        end
                    elseif type(vv) == "table" and vv.kind then
                        local ok = select(1, subst(i, vv))
                        changed = changed or ok
                    end
                end
            end
        end
    end
    return changed
end

-- Returns the (single) target register of an inlineable statement,
-- or nil for non-inlineable statements.
local function singleTargetReg(s)
    if not INLINEABLE_KINDS[s.kind] then return nil end
    if s.kind == K.CALL then
        if s.targets and #s.targets == 1 then return s.targets[1] end
        return nil
    end
    return s.target
end

-- Local def-use chain inliner.
--
-- Walk forward through the IR list maintaining `liveDefs[regKey]`, the
-- most recent inlineable def of each register that has not yet been read.
-- When a statement reads register R:
--   - If liveDefs[R] is non-nil AND the def's value is inlineable AND R is
--     not a protected role, substitute the read with the def's value and
--     mark the def as NOP. We also need to ensure R is read EXACTLY ONCE
--     between def and the next overwrite -- we track this by counting reads
--     of R in the remaining-statement window from def_i to the position of
--     R's next write.
--
-- For simplicity we precompute, for each def position i and the register
-- it writes, the number of reads of that register strictly between i and
-- the next write of the same register (or end of block). We only inline
-- defs where this read-count is 1 AND the call ordering would not be
-- changed (no intervening side-effecting calls when the def is itself
-- side-effecting -- we conservatively skip inlining of CALL / ARG_READ /
-- UPVAL_READ / GLOBAL_READ / INDEX_READ across other side-effecting
-- statements).
--
-- A statement is "side-effecting" if it is a CALL, GLOBAL_WRITE,
-- UPVAL_WRITE, INDEX_WRITE, UPVAL_INIT, or UPVAL_ALLOC.

local function isSideEffecting(s)
    local k = s.kind
    return k == K.CALL or k == K.GLOBAL_WRITE or k == K.UPVAL_WRITE
        or k == K.INDEX_WRITE or k == K.UPVAL_INIT or k == K.UPVAL_ALLOC
end

-- Recursively scan an expression / IR-internal value for embedded
-- side-effecting subexpressions: function calls, global reads, upvalue
-- reads, table-index reads, arg reads. Closure construction and pure
-- arithmetic are NOT side-effecting.
local function valueHasSideEffect(node)
    if not node then return false end
    if ir.isReg(node) then return false end
    if type(node) ~= "table" or not node.kind then return false end
    local k = node.kind
    if k == AstKind.FunctionCallExpression
       or k == AstKind.PassSelfFunctionCallExpression then
        return true
    end
    if k == "_irGlobalRead" or k == "_irUpvalRead" or k == "_irIndexRead"
       or k == "_irArgRead" then
        return true
    end
    -- Recurse on common children fields.
    for _, fname in ipairs({ "lhs", "rhs", "base", "index", "value", "key", "name", "cond", "source" }) do
        local v = node[fname]
        if v ~= nil and valueHasSideEffect(v) then return true end
    end
    -- List fields.
    if type(node.args) == "table" then
        for _, a in ipairs(node.args) do
            if valueHasSideEffect(a) then return true end
        end
    end
    if type(node.upvalSlots) == "table" then
        for _, a in ipairs(node.upvalSlots) do
            if valueHasSideEffect(a) then return true end
        end
    end
    if type(node.entries) == "table" then
        for _, e in ipairs(node.entries) do
            if type(e) == "table" then
                if valueHasSideEffect(e.value) or valueHasSideEffect(e.key) then return true end
            end
        end
    end
    return false
end

local function defWritesReg(s)
    if s.kind == K.CALL then
        return s.targets and #s.targets > 0 and s.targets or nil
    end
    local tgt = s.target
    if tgt and ir.isReg(tgt) then return { tgt } end
    return nil
end

-- `liveOutSet`: optional set { regKey -> true } of registers known to be
-- read in some successor block. Inliner will refuse to drop a register's
-- definition if its target is in liveOutSet AND there's no later write
-- in the block that would overwrite it. Without `liveOutSet`, the inliner
-- assumes nothing is live-out (which is correct only for self-contained
-- blocks; cross-block users should pass liveOutSet for full correctness).
local function inlineSingleUseRegisters(stmts, liveOutSet)
    liveOutSet = liveOutSet or {}
    -- Compute, for each statement i and each regKey, where its next
    -- def is. We walk backwards.
    local n = #stmts
    local nextDef = {}  -- nextDef[i] = { regKey -> j } meaning the next
                        --     write of `regKey` strictly after i is at j
                        --     (or n+1 if there is none).

    -- Reads at each position: readPos[i] = { regKey -> count }
    local readsAt = {}
    -- Writes at each position: writesAt[i] = { regKey, ... }
    local writesAt = {}

    for i = 1, n do
        readsAt[i] = {}
        for _, op in ipairs(operandsOf(stmts[i])) do
            for _, r in ipairs(regsInOperand(op)) do
                local k = regKey(r)
                readsAt[i][k] = (readsAt[i][k] or 0) + 1
            end
        end
        local writes = defWritesReg(stmts[i]) or {}
        local ws = {}
        for _, w in ipairs(writes) do table.insert(ws, regKey(w)) end
        writesAt[i] = ws
    end

    -- For each register, find each def's next write position.
    local function findNextWrite(regK, fromIdx)
        for j = fromIdx + 1, n do
            for _, w in ipairs(writesAt[j]) do
                if w == regK then return j end
            end
        end
        return n + 1
    end

    -- Count reads of `regK` between (defIdx, nextWriteIdx]. Reads at the
    -- nextWriteIdx statement are *included* because, within a single
    -- statement, reads conceptually happen before writes (Lua semantics
    -- for assignment evaluate all RHS before any LHS gets stored), so a
    -- statement like `R = R + 1` reads R "before" overwriting it.
    local function countReadsBetween(regK, defIdx, nextWriteIdx)
        local total = 0
        for j = defIdx + 1, nextWriteIdx do
            if j <= n then
                total = total + (readsAt[j][regK] or 0)
            end
        end
        return total
    end

    -- Find the FIRST read of regK strictly after defIdx (up to and
    -- including nextWriteIdx). Returns its statement index, or nil.
    local function firstReadAfter(regK, defIdx, nextWriteIdx)
        for j = defIdx + 1, nextWriteIdx do
            if j <= n and (readsAt[j][regK] or 0) > 0 then return j end
        end
        return nil
    end

    -- Pass: at each def candidate, decide if we can inline.
    for i = 1, n do
        local s = stmts[i]
        if INLINEABLE_KINDS[s.kind] then
            local tgt = singleTargetReg(s)
            if tgt and not PROTECTED_ROLES[tgt.role or ""] then
                local rk = regKey(tgt)
                local nwIdx = findNextWrite(rk, i)
                -- Cross-block correctness: if the target is live-out of this
                -- block AND there's no in-block redefinition that masks our
                -- def, do NOT inline. Otherwise the def we'd remove is the
                -- one feeding successor blocks.
                local liveOutHere = liveOutSet[rk] and (nwIdx > n)
                local rdCount = countReadsBetween(rk, i, nwIdx)
                if rdCount == 1 and not liveOutHere then
                    local readIdx = firstReadAfter(rk, i, nwIdx)
                    if readIdx then
                        -- Side-effect ordering check: if def's RHS has
                        -- side effects (e.g. CALL, ARG_READ, GLOBAL_READ,
                        -- UPVAL_READ, INDEX_READ -- table reads can
                        -- raise errors via __index metamethods), we must
                        -- not move it past intervening side-effecting
                        -- statements. We detect this by checking whether
                        -- ANY statement strictly between i and readIdx is
                        -- side-effecting OR also reads/writes the same
                        -- backing storage we're about to move past.
                        local val = inlineValueOf(s)
                        -- Side-effect classification:
                        --   * CALL: must not be moved across other CALLs or
                        --     across stores/global reads (any potentially
                        --     observable effect).
                        --   * GLOBAL_READ / INDEX_READ (on a non-VM base):
                        --     could observe ordering with respect to other
                        --     CALLs or writes via metamethods. Treat as
                        --     "weakly side-effecting" -- moveable across
                        --     pure reads but not across stores or calls.
                        --   * ARG_READ / UPVAL_READ: read from VM-internal
                        --     tables (ARGS, UPVALS_TABLE) which we control.
                        --     Safe to reorder.
                        --   * Other (LOAD, COPY, BINOP, UNOP, CREATE_CLOSURE):
                        --     pure (no observable effects).
                        local defStrong = (s.kind == K.CALL)
                            or valueHasSideEffect(val)
                        local defWeak = defStrong
                            or (s.kind == K.GLOBAL_READ)
                            or (s.kind == K.INDEX_READ)
                        local safe = true
                        if defStrong then
                            for j = i + 1, readIdx - 1 do
                                if isSideEffecting(stmts[j]) then safe = false; break end
                                if stmts[j].kind == K.GLOBAL_READ
                                   or stmts[j].kind == K.INDEX_READ then
                                    safe = false; break
                                end
                            end
                        elseif defWeak then
                            for j = i + 1, readIdx - 1 do
                                if isSideEffecting(stmts[j]) then safe = false; break end
                            end
                        end
                        -- Stability check: every register the inline value
                        -- READS must not be WRITTEN between def_i and
                        -- readIdx. Otherwise the inline would silently
                        -- read a different value at the use site.
                        if safe and val ~= nil then
                            if s.kind == K.CALL and s.tableWrapped
                               and stmts[readIdx] and stmts[readIdx].kind == K.INDEX_READ then
                                safe = false
                            end
                        end
                        if safe and val ~= nil then
                            local valRegs = regsInOperand(val)
                            for _, vr in ipairs(valRegs) do
                                local vrk = regKey(vr)
                                for j = i + 1, readIdx - 1 do
                                    for _, w in ipairs(writesAt[j]) do
                                        if w == vrk then safe = false; break end
                                    end
                                    if not safe then break end
                                end
                                if not safe then break end
                            end
                        end
                        if safe and val ~= nil then
                            substituteOperand(stmts[readIdx], rk, val)
                            s.kind = K.NOP
                            -- Update readsAt/writesAt to reflect the
                            -- substitution: the old read of `rk` at
                            -- readIdx is gone; new reads for every
                            -- register inside `val` are now there at
                            -- readIdx. We don't bother recounting val's
                            -- own internal regs perfectly -- a single
                            -- read at readIdx is the dominant case.
                            local before = readsAt[readIdx][rk] or 0
                            if before > 0 then
                                readsAt[readIdx][rk] = before - 1
                            end
                            for _, vr in ipairs(regsInOperand(val)) do
                                local vrk = regKey(vr)
                                readsAt[readIdx][vrk] = (readsAt[readIdx][vrk] or 0) + 1
                            end
                            -- Also remove writes from def_i (we NOP'd it).
                            writesAt[i] = {}
                        end
                    end
                end
            end
        end
    end

    -- Filter out NOPs.
    local result = {}
    for _, s in ipairs(stmts) do
        if s.kind ~= K.NOP then table.insert(result, s) end
    end
    return result
end

-- ----------------------------------------------------------------------------
-- Liveness analysis (cross-block).
--
-- Computes per-block "liveOut" sets: for each block B, the set of register
-- keys that are read in some path starting at a successor of B before being
-- overwritten. We use rawStatements (pre-inline) for accuracy.
--
-- Standard backward dataflow:
--   gen[B]    = registers read in B before any write in B
--   kill[B]   = registers written somewhere in B
--   liveIn[B] = gen[B] U (liveOut[B] - kill[B])
--   liveOut[B] = U_{S in succs(B)} liveIn[S]
--
-- Iterate to fixed-point.
local function computeBlockGenKill(stmts)
    local gen, kill = {}, {}
    for _, s in ipairs(stmts) do
        for _, op in ipairs(operandsOf(s)) do
            for _, r in ipairs(regsInOperand(op)) do
                local k = regKey(r)
                if not kill[k] then gen[k] = true end
            end
        end
        for _, w in ipairs(defWritesReg(s) or {}) do
            kill[regKey(w)] = true
        end
    end
    return gen, kill
end

local function computeLiveness(fn, decompMap)
    -- For each block id in fn, compute liveOut.
    local genOf, killOf, liveIn, liveOut = {}, {}, {}, {}
    local blockIds = {}
    for id, _ in pairs(fn.succs) do
        if id ~= -1 and id ~= -2 then  -- skip ENTRY/EXIT
            table.insert(blockIds, id)
            local d = decompMap[id]
            if d then
                local gen, kill = computeBlockGenKill(d.rawStatements or {})
                genOf[id] = gen
                killOf[id] = kill
            else
                genOf[id] = {}
                killOf[id] = {}
            end
            liveIn[id] = {}
            liveOut[id] = {}
        end
    end
    -- Fixed-point iteration.
    local changed = true
    while changed do
        changed = false
        for _, id in ipairs(blockIds) do
            local newOut = {}
            for _, succ in ipairs(fn.succs[id] or {}) do
                if succ ~= -2 then  -- ignore EXIT
                    for k, _ in pairs(liveIn[succ] or {}) do
                        newOut[k] = true
                    end
                end
            end
            local newIn = {}
            -- liveIn = gen U (liveOut - kill)
            for k, _ in pairs(genOf[id] or {}) do newIn[k] = true end
            for k, _ in pairs(newOut) do
                if not (killOf[id] or {})[k] then newIn[k] = true end
            end
            -- Detect change.
            local function setEq(a, b)
                for k in pairs(a) do if not b[k] then return false end end
                for k in pairs(b) do if not a[k] then return false end end
                return true
            end
            if not setEq(newOut, liveOut[id]) or not setEq(newIn, liveIn[id]) then
                changed = true
                liveOut[id] = newOut
                liveIn[id] = newIn
            end
        end
    end
    return liveOut
end

-- Re-decompile every block in `graph` using cross-block liveness as a
-- correctness hint. Updates decomp.statements and exit fields in place.
function M.refineWithLiveness(graph, extracted, vm)
    local blockById = {}
    for _, b in ipairs(extracted.blocksOrdered) do
        blockById[b.id] = b
    end
    for _, fn in ipairs(graph.fns) do
        local liveOut = computeLiveness(fn, graph.decompMap)
        for _, blockId in ipairs(fn.blockIds or {}) do
            local b = blockById[blockId]
            local d = graph.decompMap[blockId]
            if b and d then
                local newD = M.decompile(b, vm, { liveOutSet = liveOut[blockId] })
                d.statements    = newD.statements
                d.exitKind      = newD.exitKind
                d.exitTarget    = newD.exitTarget
                d.exitTargets   = newD.exitTargets
                -- rawStatements is unchanged.
            end
        end
    end
end

-- ----------------------------------------------------------------------------
-- Public API.

function M.decompile(block, vm, opts)
    opts = opts or {}
    local roleOf, roleOfNode = M.buildRoleTable(vm)
    local conv = makeOperandConverter(roleOf)
    local closureHelpers = buildClosureHelperSet(vm)

    -- The actual block exit is the LAST pos-write encountered when
    -- walking statements top-down (extract.lua already classifies exits
    -- in source order). All earlier pos-writes are scratch uses of POS
    -- as a temporary register and must not be classified as JUMP / RETURN.
    local lastExitStat, lastExitIdx
    if block.exits and #block.exits > 0 then
        local le = block.exits[#block.exits]
        lastExitStat = le.statement
        lastExitIdx  = le.statementIndex
    end

    local ctx = {
        roleOf         = roleOf,
        roleOfNode     = roleOfNode,
        conv           = conv,
        closureHelpers = closureHelpers,
        vm             = vm,
        lastExitStat   = lastExitStat,
        lastExitIdx    = lastExitIdx,
    }

    local raw = decompileStatements(block.body, ctx)

    -- Determine the exit form from the original block.exits info.
    local exitKind, exitTarget, exitTargets
    if #block.exits == 0 then
        exitKind = "fallthrough"
    else
        local last = block.exits[#block.exits]
        if last.kind == "jump_const" then
            exitKind = "jump_const"; exitTarget = last.target
        elseif last.kind == "jump_cond" then
            exitKind = "jump_cond"; exitTargets = { last.trueTarget, last.falseTarget }
        elseif last.kind == "return" then
            exitKind = "return"
        else
            exitKind = "other"
        end
    end

    local cooked
    if opts.inline ~= false then
        cooked = inlineSingleUseRegisters(raw, opts.liveOutSet)
    else
        cooked = raw
    end

    -- ------------------------------------------------------------------
    -- Post-inline exit re-classification.
    --
    -- Vmify sometimes emits a JUMP_COND across multiple statements:
    --     POS = (cond and N1)            -- intermediate
    --     POS = (POS or N2)              -- final
    -- After inlining, the final statement collapses to
    --     POS = ((cond and N1) or N2)
    -- which is the canonical jump-cond shape. extract.lua can't see
    -- through the split, so the block is initially marked exit="other"
    -- with two pos-writes. We fix this here by looking at the *last*
    -- IR statement targeting POS and re-classifying.
    --
    -- Similarly for split JUMP_CONST (POS = scratch number assignments
    -- followed by POS = pos_scratch) and RETURN.
    -- Only run when extract.lua wasn't able to classify the exit; otherwise
    -- the canonical classification is already in place and we must not
    -- accidentally turn an intermediate POS scratch (e.g. R1@POS = ENV["print"]
    -- used as a scratch register in a multi-call block) into a RETURN.
    if exitKind == "other" then
        -- Find LAST IR stmt that writes POS (regardless of kind).
        local lastIdx
        for i = #cooked, 1, -1 do
            local st = cooked[i]
            if st.kind ~= K.NOP then
                local writes = defWritesReg(st)
                if writes then
                    for _, w in ipairs(writes) do
                        if w.role == "POS" then lastIdx = i; break end
                    end
                end
                if lastIdx then break end
            end
        end
        if lastIdx then
            local st = cooked[lastIdx]
            -- Helpers that decode either a raw AST or an _ir* synthetic node.
            local function isNum(n) return n and n.kind == AstKind.NumberExpression end

            -- Decode the (lhs, rhs, op) of an "or" expression in any form.
            -- Returns nil if not an "or".
            local function decodeOr(node)
                if not node then return nil end
                if node.kind == AstKind.OrExpression then
                    return node.lhs, node.rhs
                elseif node.kind == "_irBinop" and node.op == "or" then
                    return node.lhs, node.rhs
                end
                return nil
            end
            local function decodeAnd(node)
                if not node then return nil end
                if node.kind == AstKind.AndExpression then
                    return node.lhs, node.rhs
                elseif node.kind == "_irBinop" and node.op == "and" then
                    return node.lhs, node.rhs
                end
                return nil
            end

            -- Decode the "value" of the last POS write into a single
            -- expression, even when the IR kind is BINOP / UNOP / etc.
            local v
            if st.kind == K.LOAD then v = st.value
            elseif st.kind == K.COPY then v = st.source
            elseif st.kind == K.BINOP then
                v = { kind = "_irBinop", op = st.op, lhs = st.lhs, rhs = st.rhs }
            elseif st.kind == K.UNOP then
                v = { kind = "_irUnop",  op = st.op, rhs = st.rhs }
            elseif st.kind == K.GLOBAL_READ then
                -- POS = ENV[name] -> already handled by initial classifier
                -- in most cases; defensive RETURN reclassification here.
                v = { kind = AstKind.IndexExpression,
                      base = { kind = AstKind.VariableExpression,
                               scope = (st.raw and st.raw.rhs and st.raw.rhs.base and st.raw.rhs.base.scope),
                               id    = (st.raw and st.raw.rhs and st.raw.rhs.base and st.raw.rhs.base.id),
                             },
                      index = st.name }
            end

            if v then
                local orL, orR = decodeOr(v)
                if isNum(v) then
                    cooked[lastIdx] = {
                        kind = K.JUMP_CONST, target = v.value,
                        sourceStat = st.sourceStat, sourceIndex = st.sourceIndex,
                    }
                    exitKind = "jump_const"; exitTarget = v.value; exitTargets = nil
                elseif orL and orR and isNum(orR) then
                    -- Form: (X) or N. X must be (cond and M).
                    local andL, andR = decodeAnd(orL)
                    if andL and andR and isNum(andR) then
                        cooked[lastIdx] = {
                            kind = K.JUMP_COND,
                            cond = andL,
                            trueTarget  = andR.value,
                            falseTarget = orR.value,
                            sourceStat = st.sourceStat, sourceIndex = st.sourceIndex,
                        }
                        exitKind = "jump_cond"; exitTarget = nil
                        exitTargets = { andR.value, orR.value }
                    end
                elseif v.kind == AstKind.IndexExpression and v.base
                       and v.base.kind == AstKind.VariableExpression
                       and v.base.scope and roleOf(v.base.scope, v.base.id) == "ENV" then
                    cooked[lastIdx] = {
                        kind = K.RETURN,
                        sourceStat = st.sourceStat, sourceIndex = st.sourceIndex,
                    }
                    exitKind = "return"; exitTarget = nil; exitTargets = nil
                end
            end
        end
    end

    return {
        id            = block.id,
        synthetic     = block.synthetic,
        idLo          = block.idLo,
        idHi          = block.idHi,
        rawStatements = raw,
        statements    = cooked,
        exitKind      = exitKind,
        exitTarget    = exitTarget,
        exitTargets   = exitTargets,
    }
end

-- Convenience: decompile every block.
function M.decompileAll(extracted, vm, opts)
    local out = {}
    for _, b in ipairs(extracted.blocksOrdered) do
        local d = M.decompile(b, vm, opts)
        out[b.id] = d
        table.insert(out, d)  -- list-style index for ordered iteration
    end
    return out
end

-- Pretty-printer for a decompiled block.
function M.report(decomp, write)
    write = write or function(s) io.write(s); io.write("\n") end
    local kindTag = decomp.synthetic and "(synth)" or "       "
    local exitDesc
    if     decomp.exitKind == "jump_const" then exitDesc = ("-> %d"):format(decomp.exitTarget)
    elseif decomp.exitKind == "jump_cond"  then exitDesc = ("?-> %d / %d"):format(decomp.exitTargets[1], decomp.exitTargets[2])
    elseif decomp.exitKind == "return"     then exitDesc = "-> RETURN"
    else                                         exitDesc = "-> ?" end
    write(("block %-12d %s  (%d -> %d ir-stmts)  %s"):format(
        decomp.id, kindTag, #decomp.rawStatements, #decomp.statements, exitDesc))
    for i, s in ipairs(decomp.statements) do
        write(("  [%d] %s"):format(i, ir.statString(s)))
    end
end

function M.reportAll(decomps, write)
    write = write or function(s) io.write(s); io.write("\n") end
    for _, d in ipairs(decomps) do
        M.report(d, write)
        write("")
    end
end

return M
