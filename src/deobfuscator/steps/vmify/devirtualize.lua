-- prometheus-test-deobfuscator -- M6 devirtualization.
--
-- Final step of phase 2: takes the structured-tree representation produced by
-- M2-M5 and emits real Lua source. The reconstructed source replaces the
-- entire `return ((function(env, ...) <vm dispatcher> end)(getfenv, ...))`
-- top-level wrapper with the equivalent reconstructed program.
--
-- This is *source-level* emission (not AST-level). The reasons are:
--   * The structured tree is already 90% Lua-shaped (block/if/while/...).
--   * Emitting strings directly avoids round-tripping all expression nodes
--     through the Prometheus AST constructors and scope machinery.
--   * The result is parsed back into AST at the end so the unparser owns
--     pretty-printing and the rest of the pipeline (fold_numbers, etc.) can
--     run on it normally.

local Parser    = require("prometheus.parser")
local Enums     = require("prometheus.enums")

local recognize = require("deobfuscator.steps.vmify.recognize")
local extract   = require("deobfuscator.steps.vmify.extract")
local decompile = require("deobfuscator.steps.vmify.decompile_block")
local cfg       = require("deobfuscator.steps.vmify.cfg")
local closures  = require("deobfuscator.steps.vmify.closures")
local structure = require("deobfuscator.steps.vmify.structure")
local ir        = require("deobfuscator.steps.vmify.ir")

local Ast       = require("prometheus.ast")
local AstKind   = Ast.AstKind
local K         = ir.kinds
local isReg     = ir.isReg

local M = {}

-- ---------------------------------------------------------------------------
-- Identifier helpers.

local LUA51_RESERVED = {
    ["and"]=true, ["break"]=true, ["do"]=true, ["else"]=true, ["elseif"]=true,
    ["end"]=true, ["false"]=true, ["for"]=true, ["function"]=true, ["goto"]=true,
    ["if"]=true, ["in"]=true, ["local"]=true, ["nil"]=true, ["not"]=true,
    ["or"]=true, ["repeat"]=true, ["return"]=true, ["then"]=true, ["true"]=true,
    ["until"]=true, ["while"]=true,
}

local function isValidIdent(s)
    if type(s) ~= "string" then return false end
    if LUA51_RESERVED[s] then return false end
    return s:match("^[%a_][%w_]*$") ~= nil
end

-- Format a Lua string literal for emission. Uses %q which handles all
-- characters safely (newlines, quotes, control chars).
local function formatStringLiteral(s)
    return ("%q"):format(s)
end

local function wrapTableCapture(s)
    return "{" .. s .. "}"
end

local function wrapAsIndexBase(s)
    return "(function(...) return {...} end)(" .. s .. ")"
end

local function regName(r)
    return ("r%d"):format(r.id)
end

-- ---------------------------------------------------------------------------
-- Per-function context.

local Ctx = {}
Ctx.__index = Ctx

local function buildCtx(graph, structured, fn, parent)
    local self = setmetatable({
        graph        = graph,
        structured   = structured,
        fn           = fn,
        parent       = parent,
        -- Registers we've decided to emit as locals at the function top.
        regsToDeclare = {},
        regSeen      = {},
        -- Registers used as table bases without an in-function definition.
        -- These are usually VM register-array locals declared before the
        -- dispatcher loop (e.g. `local B_ = {}`), outside harvested blocks.
        indexedBasesToInit = {},
        indexedBaseSeen    = {},
        -- Track if the function uses ARG_READ (=> needs `local args = {...}`).
        usesArgs     = false,
        -- Track if the function references the ENV register (=> may need
        -- access to the global environment table). When the env register is
        -- read directly (e.g. as a value), we emit `_G` for it.
    }, Ctx)
    return self
end

-- Mark a register as one that needs to be declared at the function top.
function Ctx:noteWrite(reg)
    if not isReg(reg) then return end
    local role = reg.role or "GENERAL"
    -- Skip pseudo registers — they're not real variables in the source.
    -- POS is emitted by name (eg "r1") just like any register; we still need
    -- to declare it because devirt turns control-flow pos-writes into normal
    -- scratch-register assignments.
    if role == "ARGS" or role == "UPVALS" or role == "GC"
       or role == "ENV" or role == "UNPACK" or role == "SELECT"
       or role == "GETMT" or role == "SETMT" or role == "NEWPROXY"
       or role == "VARARG" or role == "CONTAINER" or role == "ALLOC_UPVAL"
       or role == "FREE_UPVAL" or role == "PROXY_FN" or role == "GC_FN"
       or role == "CREATE_VARARG_CLOSURE" or role == "UPVALS_TABLE"
       or role == "REF_COUNTS" or role == "CURRENT_UPVAL_ID"
       or role == "CREATE_CLOSURE" then
        return
    end
    local key = ("%s:%s"):format(tostring(reg.scope), tostring(reg.id))
    if self.regSeen[key] then return end
    self.regSeen[key] = true
    table.insert(self.regsToDeclare, reg)
end

function Ctx:noteIndexedBase(reg)
    if not isReg(reg) then return end
    if (reg.role or "GENERAL") ~= "GENERAL" then return end
    local key = ("%s:%s"):format(tostring(reg.scope), tostring(reg.id))
    if self.indexedBaseSeen[key] then return end
    self.indexedBaseSeen[key] = true
    table.insert(self.indexedBasesToInit, reg)
end

-- ---------------------------------------------------------------------------
-- Walk the structured tree to compute which registers are written. This
-- determines what we need to declare at the function top.

local function walkStmts(body, fn, visit)
    for _, node in ipairs(body) do
        if node.kind == "block" then
            for _, s in ipairs(node.statements) do visit(s) end
        elseif node.kind == "if" then
            for _, s in ipairs(node.cond.statements) do visit(s) end
            walkStmts(node.thenBody, fn, visit)
            if node.elseBody then walkStmts(node.elseBody, fn, visit) end
        elseif node.kind == "while" then
            if node.headerStmts then for _, s in ipairs(node.headerStmts) do visit(s) end end
            walkStmts(node.body, fn, visit)
        elseif node.kind == "for_num" or node.kind == "for_in" or node.kind == "loop" then
            walkStmts(node.body, fn, visit)
        end
    end
end

function Ctx:scanRegisters()
    walkStmts(self.fn.body, self.fn, function(s)
        local k = s.kind
        if k == K.LOAD or k == K.COPY or k == K.BINOP or k == K.UNOP
           or k == K.ARG_READ or k == K.UPVAL_READ
           or k == K.GLOBAL_READ or k == K.INDEX_READ or k == K.CREATE_CLOSURE then
            self:noteWrite(s.target)
        elseif k == K.CALL then
            for _, t in ipairs(s.targets or {}) do self:noteWrite(t) end
        end
        if k == K.INDEX_READ or k == K.INDEX_WRITE then
            self:noteIndexedBase(s.base)
        end
        if k == K.ARG_READ then self.usesArgs = true end
    end)
end

-- ---------------------------------------------------------------------------
-- Expression emission.

local exprText
local stmtText
local bodyText

-- Returns the canonical RETURN-register identity for this function (used to
-- recognize RETURN_REG = ... + return as the actual return-with-values site).
local function returnReg(fn)
    -- Each fn carries a vm reference indirectly via graph.vm.
    return fn._returnReg
end

-- Generate Lua source text for an expression.
exprText = function(e, ctx)
    if e == nil then return "nil" end
    if isReg(e) then
        local role = e.role or "GENERAL"
        if role == "ENV" then return "_G" end
        if role == "UNPACK" then return "(unpack or table.unpack)" end
        if role == "GETMT" then return "getmetatable" end
        if role == "SETMT" then return "setmetatable" end
        if role == "SELECT" then return "select" end
        if role == "NEWPROXY" then return "newproxy" end
        if role == "ARGS" then return "args" end
        return regName(e)
    end
    if type(e) ~= "table" or not e.kind then
        return tostring(e)
    end
    local k = e.kind

    -- IR-internal expression nodes.
    if k == "_irBinop" then
        return "(" .. exprText(e.lhs, ctx) .. " " .. e.op .. " " .. exprText(e.rhs, ctx) .. ")"
    end
    if k == "_irUnop" then
        local op = e.op
        if op == "not" then op = "not " end
        return "(" .. op .. exprText(e.rhs, ctx) .. ")"
    end
    if k == "_irArgRead" then
        ctx.usesArgs = true
        return "args[" .. exprText(e.index, ctx) .. "]"
    end
    if k == "_irUpvalRead" then
        if e.slotName then return e.slotName end
        return "(--[[ unresolved upval ]] nil)"
    end
    if k == "_irGlobalRead" then
        local nameExpr = e.name
        if nameExpr and nameExpr.kind == AstKind.StringExpression and isValidIdent(nameExpr.value) then
            return nameExpr.value
        end
        return "_G[" .. exprText(nameExpr, ctx) .. "]"
    end
    if k == "_irIndexRead" then
        local baseT = exprText(e.base, ctx)
        local isTableCapture = baseT:sub(1, 1) == "{" and baseT:sub(-1) == "}"
        if isTableCapture then
            baseT = wrapAsIndexBase(baseT:sub(2, -2))
            return baseT .. "[" .. exprText(e.index, ctx) .. "]"
        end
        local first = baseT:sub(1, 1)
        if first == "{" or first == '"' or first == "'" or first == "(" then
            baseT = "(" .. baseT .. ")"
        end
        return baseT .. "[" .. exprText(e.index, ctx) .. "]"
    end
    if k == "_irClosure" then
        return "(" .. M.functionLiteralText(ctx.graph, ctx.structured, e.entryId,
                                     ctx.fn, e.isVararg, e.upvalNames) .. ")"
    end
    if k == "_irCall" then
        local args = {}
        for _, a in ipairs(e.args or {}) do
            table.insert(args, exprText(a, ctx))
        end
        local callExpr = exprText(e.base, ctx) .. "(" .. table.concat(args, ", ") .. ")"
        if e.tableWrapped then callExpr = wrapTableCapture(callExpr) end
        return callExpr
    end

    -- Real AST primitives (constants, operators, etc).
    if k == AstKind.NumberExpression  then
        local v = e.value
        if v ~= v then return "(0/0)" end -- NaN
        if v == math.huge then return "(1/0)" end
        if v == -math.huge then return "(-1/0)" end
        return tostring(v)
    end
    if k == AstKind.StringExpression  then return formatStringLiteral(e.value) end
    if k == AstKind.BooleanExpression then return tostring(e.value) end
    if k == AstKind.NilExpression     then return "nil" end
    if k == AstKind.VarargExpression  then return "..." end

    if k == AstKind.VariableExpression or k == AstKind.AssignmentVariable then
        local ok, n = pcall(function() return e.scope:getVariableName(e.id) end)
        if ok and n then return n end
        return "_v" .. tostring(e.id)
    end

    if k == AstKind.IndexExpression then
        local baseT = exprText(e.base, ctx)
        local isTableCapture = baseT:sub(1, 1) == "{" and baseT:sub(-1) == "}"
        if isTableCapture then
            baseT = wrapAsIndexBase(baseT:sub(2, -2))
            return baseT .. "[" .. exprText(e.index, ctx) .. "]"
        end
        local first = baseT:sub(1, 1)
        if first == "{" or first == '"' or first == "'" or first == "(" then
            baseT = "(" .. baseT .. ")"
        end
        return baseT .. "[" .. exprText(e.index, ctx) .. "]"
    end
    if k == AstKind.FunctionCallExpression then
        local args = {}
        for _, a in ipairs(e.args) do table.insert(args, exprText(a, ctx)) end
        return exprText(e.base, ctx) .. "(" .. table.concat(args, ", ") .. ")"
    end
    if k == AstKind.PassSelfFunctionCallExpression then
        local args = {}
        for _, a in ipairs(e.args) do table.insert(args, exprText(a, ctx)) end
        return exprText(e.base, ctx) .. ":" .. e.passSelfFunctionName
            .. "(" .. table.concat(args, ", ") .. ")"
    end

    if k == AstKind.OrExpression                  then return "(" .. exprText(e.lhs, ctx) .. " or "  .. exprText(e.rhs, ctx) .. ")" end
    if k == AstKind.AndExpression                 then return "(" .. exprText(e.lhs, ctx) .. " and " .. exprText(e.rhs, ctx) .. ")" end
    if k == AstKind.LessThanExpression            then return "(" .. exprText(e.lhs, ctx) .. " < "   .. exprText(e.rhs, ctx) .. ")" end
    if k == AstKind.GreaterThanExpression         then return "(" .. exprText(e.lhs, ctx) .. " > "   .. exprText(e.rhs, ctx) .. ")" end
    if k == AstKind.LessThanOrEqualsExpression    then return "(" .. exprText(e.lhs, ctx) .. " <= "  .. exprText(e.rhs, ctx) .. ")" end
    if k == AstKind.GreaterThanOrEqualsExpression then return "(" .. exprText(e.lhs, ctx) .. " >= "  .. exprText(e.rhs, ctx) .. ")" end
    if k == AstKind.EqualsExpression              then return "(" .. exprText(e.lhs, ctx) .. " == "  .. exprText(e.rhs, ctx) .. ")" end
    if k == AstKind.NotEqualsExpression           then return "(" .. exprText(e.lhs, ctx) .. " ~= "  .. exprText(e.rhs, ctx) .. ")" end
    if k == AstKind.AddExpression                 then return "(" .. exprText(e.lhs, ctx) .. " + "   .. exprText(e.rhs, ctx) .. ")" end
    if k == AstKind.SubExpression                 then return "(" .. exprText(e.lhs, ctx) .. " - "   .. exprText(e.rhs, ctx) .. ")" end
    if k == AstKind.MulExpression                 then return "(" .. exprText(e.lhs, ctx) .. " * "   .. exprText(e.rhs, ctx) .. ")" end
    if k == AstKind.DivExpression                 then return "(" .. exprText(e.lhs, ctx) .. " / "   .. exprText(e.rhs, ctx) .. ")" end
    if k == AstKind.ModExpression                 then return "(" .. exprText(e.lhs, ctx) .. " % "   .. exprText(e.rhs, ctx) .. ")" end
    if k == AstKind.PowExpression                 then return "(" .. exprText(e.lhs, ctx) .. " ^ "   .. exprText(e.rhs, ctx) .. ")" end
    if k == AstKind.StrCatExpression              then return "(" .. exprText(e.lhs, ctx) .. " .. "  .. exprText(e.rhs, ctx) .. ")" end
    if k == AstKind.NotExpression                 then return "(not " .. exprText(e.rhs, ctx) .. ")" end
    if k == AstKind.NegateExpression              then return "(-" .. exprText(e.rhs, ctx) .. ")" end
    if k == AstKind.LenExpression                 then return "(#" .. exprText(e.rhs, ctx) .. ")" end

    if k == AstKind.TableConstructorExpression then
        if #e.entries == 0 then return "{}" end
        local parts = {}
        for _, en in ipairs(e.entries) do
            if en.kind == AstKind.KeyedTableEntry then
                local key = en.key
                if key.kind == AstKind.StringExpression and isValidIdent(key.value) then
                    table.insert(parts, key.value .. " = " .. exprText(en.value, ctx))
                else
                    table.insert(parts, "[" .. exprText(key, ctx) .. "] = " .. exprText(en.value, ctx))
                end
            else
                table.insert(parts, exprText(en.value, ctx))
            end
        end
        return "{ " .. table.concat(parts, ", ") .. " }"
    end

    return "(--[[ unhandled expr " .. tostring(k) .. " ]]nil)"
end

-- ---------------------------------------------------------------------------
-- Statement emission.

-- Common helper: emit `lhs = rhs` (or the equivalent decoration) for an IR
-- statement that targets a single register or slot.
local function targetText(reg, ctx)
    if not isReg(reg) then return "_unknown" end
    ctx:noteWrite(reg)
    local role = reg.role or "GENERAL"
    if role == "ARGS"   then return "args" end
    if role == "ENV"    then return "_G" end
    return regName(reg)
end

stmtText = function(s, ctx, indent)
    local k = s.kind

    if k == K.LOAD then
        return targetText(s.target, ctx) .. " = " .. exprText(s.value, ctx)
    end
    if k == K.COPY then
        return targetText(s.target, ctx) .. " = " .. exprText(s.source, ctx)
    end
    if k == K.BINOP then
        return targetText(s.target, ctx) .. " = " ..
            exprText(s.lhs, ctx) .. " " .. s.op .. " " .. exprText(s.rhs, ctx)
    end
    if k == K.UNOP then
        local op = s.op
        if op == "not" then op = "not " end
        return targetText(s.target, ctx) .. " = " .. op .. exprText(s.rhs, ctx)
    end
    if k == K.ARG_READ then
        ctx.usesArgs = true
        return targetText(s.target, ctx) .. " = args[" .. exprText(s.index, ctx) .. "]"
    end
    if k == K.UPVAL_READ then
        if s.slotName then
            return targetText(s.target, ctx) .. " = " .. s.slotName
        end
        return "-- unresolved UPVAL_READ at " .. tostring(s.target and s.target.id)
    end
    if k == K.UPVAL_WRITE then
        -- Slot allocations are hoisted to the function top, so UPVAL_WRITE
        -- always emits a plain assignment (never `local`).
        if s.initSlotName then
            return s.initSlotName .. " = " .. exprText(s.value, ctx)
        end
        if s.slotName then
            return s.slotName .. " = " .. exprText(s.value, ctx)
        end
        return "-- unresolved UPVAL_WRITE"
    end
    if k == K.UPVAL_ALLOC then
        -- Allocation is hoisted to the function top; the in-body alloc
        -- statement becomes a no-op.
        return nil
    end
    if k == K.UPVAL_INIT then
        return "-- UPVAL_INIT (unresolved)"
    end
    if k == K.GLOBAL_READ then
        local nameExpr = s.name
        if nameExpr and nameExpr.kind == AstKind.StringExpression and isValidIdent(nameExpr.value) then
            return targetText(s.target, ctx) .. " = " .. nameExpr.value
        end
        return targetText(s.target, ctx) .. " = _G[" .. exprText(nameExpr, ctx) .. "]"
    end
    if k == K.GLOBAL_WRITE then
        local nameExpr = s.name
        local lhs
        if nameExpr and nameExpr.kind == AstKind.StringExpression and isValidIdent(nameExpr.value) then
            lhs = nameExpr.value
        else
            lhs = "_G[" .. exprText(nameExpr, ctx) .. "]"
        end
        return lhs .. " = " .. exprText(s.value, ctx)
    end
    if k == K.INDEX_READ then
        return targetText(s.target, ctx) .. " = " ..
            exprText(s.base, ctx) .. "[" .. exprText(s.index, ctx) .. "]"
    end
    if k == K.INDEX_WRITE then
        return exprText(s.base, ctx) .. "[" .. exprText(s.index, ctx) .. "] = " ..
            exprText(s.value, ctx)
    end
    if k == K.CREATE_CLOSURE then
        local lit = M.functionLiteralText(ctx.graph, ctx.structured, s.entryId,
                                          ctx.fn, s.isVararg, s.upvalNames)
        return targetText(s.target, ctx) .. " = " .. lit
    end
    if k == K.CALL then
        -- Drop calls to VM bookkeeping helpers: FREE_UPVAL only releases the
        -- VM's upvalue refcount table, GC_FN bumps a global counter etc. They
        -- have no observable effect once the VM is gone.
        if isReg(s.base) then
            local r = s.base.role
            if r == "FREE_UPVAL" or r == "GC_FN" or r == "PROXY_FN" then
                return nil
            end
        end
        local args = {}
        for _, a in ipairs(s.args or {}) do
            table.insert(args, exprText(a, ctx))
        end
        local base = exprText(s.base, ctx)
        local callExpr
        if s.isPassSelf then
            callExpr = base .. ":" .. (s.passSelfName or "?") .. "(" .. table.concat(args, ", ") .. ")"
        else
            callExpr = base .. "(" .. table.concat(args, ", ") .. ")"
        end
        local nTargets = (s.targets and #s.targets) or 0
        if nTargets == 0 then
            return callExpr
        end
        local lhsParts = {}
        for _, t in ipairs(s.targets) do
            table.insert(lhsParts, targetText(t, ctx))
        end
        if s.tableWrapped then
            return table.concat(lhsParts, ", ") .. " = " .. wrapTableCapture(callExpr)
        end
        return table.concat(lhsParts, ", ") .. " = " .. callExpr
    end
    if k == K.JUMP_CONST or k == K.JUMP_COND or k == K.RETURN then
        return nil -- structure walker handles control flow
    end
    if k == K.NOP then return nil end
    if k == K.UNKNOWN then
        return "-- UNKNOWN: " .. tostring(s.note or "?")
    end
    return "-- (unhandled IR " .. tostring(k) .. ")"
end

-- ---------------------------------------------------------------------------
-- Block / structured-tree walker.

-- Detect and rewrite the "RETURN_REG = <expr>; return" pattern. For the LAST
-- assignment to RETURN_REG in `block.statements`, drops it from the emitted
-- list and stashes the value as the return expression.
local function extractReturnExpr(stmts, returnRegId, ctx)
    if not returnRegId then return stmts, nil end
    -- Walk stmts in reverse looking for an assignment to RETURN_REG.
    for i = #stmts, 1, -1 do
        local s = stmts[i]
        local k = s.kind
        if k == K.LOAD and isReg(s.target) and s.target.id == returnRegId then
            return _filterOut(stmts, i), { kind = "load", value = s.value }
        elseif k == K.COPY and isReg(s.target) and s.target.id == returnRegId then
            return _filterOut(stmts, i), { kind = "copy", value = s.source }
        elseif k == K.CALL and s.targets and #s.targets > 0
               and isReg(s.targets[1]) and s.targets[1].id == returnRegId
               and #s.targets == 1 then
            return _filterOut(stmts, i), { kind = "call", stmt = s }
        end
        -- If we hit any side-effecting statement, stop searching backwards
        -- (we can't safely commute it with the return).
        if k == K.CALL or k == K.GLOBAL_WRITE or k == K.INDEX_WRITE
           or k == K.UPVAL_WRITE then
            return stmts, nil
        end
    end
    return stmts, nil
end

-- Filter helper: returns a copy of stmts without index `dropIdx`.
function _filterOut(stmts, dropIdx)
    local out = {}
    for i, s in ipairs(stmts) do
        if i ~= dropIdx then table.insert(out, s) end
    end
    return out
end

-- Emit a `return` statement using the captured RETURN_REG payload.
local function emitReturn(payload, ctx, write, depthIndent)
    if not payload then
        write(depthIndent .. "return")
        return
    end
    if payload.kind == "load" then
        local v = payload.value
        if v and v.kind == AstKind.NilExpression then
            write(depthIndent .. "return")
            return
        end
        if v and v.kind == AstKind.TableConstructorExpression then
            local parts = {}
            local keyed = false
            for _, en in ipairs(v.entries) do
                if en.kind == AstKind.KeyedTableEntry then keyed = true break end
            end
            if not keyed then
                for _, en in ipairs(v.entries) do
                    table.insert(parts, exprText(en.value, ctx))
                end
                if #parts == 0 then
                    write(depthIndent .. "return")
                else
                    write(depthIndent .. "return " .. table.concat(parts, ", "))
                end
                return
            end
        end
        write(depthIndent .. "return " .. exprText(v, ctx))
        return
    end
    if payload.kind == "copy" then
        write(depthIndent .. "return " .. exprText(payload.value, ctx))
        return
    end
    if payload.kind == "call" then
        local s = payload.stmt
        local args = {}
        for _, a in ipairs(s.args or {}) do
            table.insert(args, exprText(a, ctx))
        end
        local base = exprText(s.base, ctx)
        local callExpr
        if s.isPassSelf then
            callExpr = base .. ":" .. (s.passSelfName or "?") .. "(" .. table.concat(args, ", ") .. ")"
        else
            callExpr = base .. "(" .. table.concat(args, ", ") .. ")"
        end
        write(depthIndent .. "return " .. callExpr)
        return
    end
    write(depthIndent .. "return")
end

local function indentStr(d)
    return string.rep("    ", d)
end

bodyText = function(body, ctx, depth, write, returnRegId)
    -- Walk node-by-node, but pair adjacent `block`+`return` siblings so that
    -- the trailing assignment to RETURN_REG materializes as `return values`.
    local i = 1
    while i <= #body do
        local node = body[i]
        local pad = indentStr(depth)
        if node.kind == "block" and body[i+1] and body[i+1].kind == "return" then
            local newStmts, payload = extractReturnExpr(node.statements, returnRegId, ctx)
            for _, s in ipairs(newStmts) do
                local txt = stmtText(s, ctx, pad)
                if txt then write(pad .. txt) end
            end
            emitReturn(payload, ctx, write, pad)
            i = i + 2
        elseif node.kind == "block" then
            for _, s in ipairs(node.statements) do
                local txt = stmtText(s, ctx, pad)
                if txt then write(pad .. txt) end
            end
            i = i + 1
        elseif node.kind == "if" then
            -- The cond block's non-control statements were already emitted as
            -- the immediately-preceding {kind="block"} sibling; we must NOT
            -- re-emit them here. Just pull the JUMP_COND's condition out.
            local condExpr = nil
            for j = #node.cond.statements, 1, -1 do
                local s = node.cond.statements[j]
                if s.kind == K.JUMP_COND then
                    condExpr = exprText(s.cond, ctx)
                    break
                end
            end
            write(pad .. "if " .. (condExpr or "false") .. " then")
            bodyText(node.thenBody, ctx, depth + 1, write, returnRegId)
            if node.elseBody and #node.elseBody > 0 then
                write(pad .. "else")
                bodyText(node.elseBody, ctx, depth + 1, write, returnRegId)
            end
            write(pad .. "end")
            i = i + 1
        elseif node.kind == "while" then
            local condStr = exprText(node.cond, ctx)
            if node.invert then condStr = "not (" .. condStr .. ")" end
            write(pad .. "while " .. condStr .. " do")
            if node.headerStmts then
                local pad2 = indentStr(depth + 1)
                for _, s in ipairs(node.headerStmts) do
                    local txt = stmtText(s, ctx, pad2)
                    if txt then write(pad2 .. txt) end
                end
            end
            bodyText(node.body, ctx, depth + 1, write, returnRegId)
            write(pad .. "end")
            i = i + 1
        elseif node.kind == "for_num" then
            ctx:noteWrite(node.varReg)
            write(pad .. ("for %s = %s, %s, %s do"):format(
                regName(node.varReg),
                exprText(node.initExpr, ctx),
                exprText(node.limitExpr, ctx),
                exprText(node.stepExpr, ctx)))
            bodyText(node.body, ctx, depth + 1, write, returnRegId)
            write(pad .. "end")
            i = i + 1
        elseif node.kind == "for_in" then
            ctx:noteWrite(node.varReg)
            local vars = { regName(node.varReg) }
            if node.secondVarReg then
                ctx:noteWrite(node.secondVarReg)
                table.insert(vars, regName(node.secondVarReg))
            end
            local exprStr
            if node.explistInfo.kind == "table" then
                local parts = {}
                for _, en in ipairs(node.explistInfo.value.entries) do
                    if en.kind == AstKind.TableEntry then
                        table.insert(parts, exprText(en.value, ctx))
                    end
                end
                exprStr = table.concat(parts, ", ")
            else
                local args = {}
                for _, a in ipairs(node.explistInfo.args) do
                    table.insert(args, exprText(a, ctx))
                end
                exprStr = exprText(node.explistInfo.base, ctx) .. "(" .. table.concat(args, ", ") .. ")"
            end
            write(pad .. ("for %s in %s do"):format(table.concat(vars, ", "), exprStr))
            bodyText(node.body, ctx, depth + 1, write, returnRegId)
            write(pad .. "end")
            i = i + 1
        elseif node.kind == "loop" then
            -- Skip empty `while true do end` — these are structuring artifacts
            -- from blocks with computed jumps that the structurer couldn't
            -- resolve, NOT real infinite loops. Code after them IS reachable.
            -- A loop is "empty" if it has no body or all its children are
            -- block nodes with 0 statements.
            local isEmpty = true
            if node.body then
                for _, child in ipairs(node.body) do
                    if child.kind ~= "block" or (child.statements and #child.statements > 0) then
                        isEmpty = false; break
                    end
                end
            end
            if isEmpty then
                i = i + 1  -- skip
            else
                write(pad .. "while true do")
                bodyText(node.body, ctx, depth + 1, write, returnRegId)
                write(pad .. "end")
                i = i + 1
            end
        elseif node.kind == "return" then
            emitReturn(nil, ctx, write, pad)
            i = i + 1
        elseif node.kind == "goto" then
            write(pad .. ("-- GOTO %s (%s)"):format(tostring(node.target), tostring(node.info or "?")))
            i = i + 1
        elseif node.kind == "loop_cond" then
            write(pad .. "-- LOOP_COND fallback")
            i = i + 1
        elseif node.kind == "break" then
            write(pad .. "break")
            i = i + 1
        else
            i = i + 1
        end
    end
end

-- Smarter walker that pairs "block" nodes with a following "return" node so
-- the trailing RETURN_REG assignment is converted into return-with-values.
local function bodyTextSmart(body, ctx, depth, write, returnRegId)
    local i = 1
    while i <= #body do
        local node = body[i]
        local pad = indentStr(depth)
        if node.kind == "block" and body[i+1] and body[i+1].kind == "return" then
            -- Try to extract the return payload from the trailing RETURN_REG
            -- assignment in this block.
            local newStmts, payload = extractReturnExpr(node.statements, returnRegId, ctx)
            for _, s in ipairs(newStmts) do
                local txt = stmtText(s, ctx, pad)
                if txt then write(pad .. txt) end
            end
            emitReturn(payload, ctx, write, pad)
            i = i + 2
        else
            -- Single-step: re-use the same machinery, but stop after one node
            -- so we can pair the next block+return correctly.
            bodyText({ node }, ctx, depth, write, returnRegId)
            i = i + 1
        end
    end
end

-- ---------------------------------------------------------------------------
-- Function literal.

-- Cache: { entryId => string source } so identical functions only get emitted
-- once (in their first appearance). Since closures.lua already binds upvalues
-- consistently per child, multiple CREATE_CLOSURE sites of the same fn share
-- text.
local _functionLiteralCache

-- Collect slot names allocated in this function (in stable order). These are
-- hoisted to the top of the function body so nested closures created earlier
-- in the body can still reference them as upvalues regardless of where the
-- ALLOC_UPVAL appears in the IR.
local function slotNamesForFn(graph, fn)
    local names = {}
    if not (graph and graph.slots) then return names end
    -- fn may be from structured.fns (different from graph.fns). Match via
    -- entryId to handle both objects correctly.
    local fnEntryId = fn.entryId
    local collected = {}
    for id, s in pairs(graph.slots) do
        if s and s.allocFn and s.allocFn.entryId == fnEntryId then
            table.insert(collected, s)
        end
    end
    table.sort(collected, function(a, b) return a.id < b.id end)
    for _, s in ipairs(collected) do
        table.insert(names, s.name)
    end
    return names
end

local function emitUndeclaredIndexedBaseInits(ctx, indent, w)
    for _, r in ipairs(ctx.indexedBasesToInit or {}) do
        local key = ("%s:%s"):format(tostring(r.scope), tostring(r.id))
        if not ctx.regSeen[key] then
            w(indent .. "local " .. regName(r) .. " = {}")
        end
    end
end

function M.functionLiteralText(graph, structured, entryId, parentFn, isVararg, upvalNames)
    local fn = structured.fns[entryId]
    if not fn then
        return "(function() error('missing fn " .. tostring(entryId) .. "') end)"
    end
    local cache = _functionLiteralCache
    if cache and cache[entryId] then
        return cache[entryId]
    end

    -- Note: each function emission uses a fresh ctx; we DO walk into nested
    -- closures recursively (their captured upval names refer to *outer* slots
    -- which are visible by Lua's normal lexical scoping when we emit them
    -- inline at the create-site of the parent).

    local ctx = buildCtx(graph, structured, fn, parentFn)
    -- Pre-scan: figure out which registers we need to declare.
    ctx:scanRegisters()

    -- Determine RETURN reg id (used by the smart walker to pair block+return).
    local returnRegId = nil
    if graph.vm and graph.vm.returnReg and graph.vm.returnReg.regNode then
        returnRegId = graph.vm.returnReg.regNode.id
    end

    local lines = {}
    local function w(line) table.insert(lines, line) end

    w("function(...)")

    if ctx.usesArgs or _scanForUsesArgs(fn) then
        ctx.usesArgs = true
        w(indentStr(1) .. "local args = {...}")
    end
    -- Declare all "real" registers as locals at function top.
    if #ctx.regsToDeclare > 0 then
        local names = {}
        for _, r in ipairs(ctx.regsToDeclare) do
            table.insert(names, regName(r))
        end
        w(indentStr(1) .. "local " .. table.concat(names, ", "))
    end
    emitUndeclaredIndexedBaseInits(ctx, indentStr(1), w)

    -- Hoist slot ("loc_N") declarations to the top of the function body so
    -- that nested closures created earlier in the body can reference them as
    -- upvalues regardless of the alloc point in the IR.
    do
        local slotNames = slotNamesForFn(graph, fn)
        if #slotNames > 0 then
            w(indentStr(1) .. "local " .. table.concat(slotNames, ", "))
        end
    end

    bodyTextSmart(fn.body, ctx, 1, w, returnRegId)

    -- Ensure body has a final `end` etc. We rely on bodyText emitting
    -- trailing `end` for control structures. Append a top-level `end`.
    w("end")

    local source = table.concat(lines, "\n")
    if cache then cache[entryId] = source end
    return source
end

-- Walk every value-position node in the body. cb(node) is called once per
-- node found in any expression slot.
function _scanExpr(node, cb)
    if type(node) ~= "table" then return end
    cb(node)
    for _, k in ipairs({ "lhs", "rhs", "base", "index", "value", "cond", "source", "name" }) do
        if node[k] then _scanExpr(node[k], cb) end
    end
    if node.args then for _, a in ipairs(node.args) do _scanExpr(a, cb) end end
    if node.entries then for _, e in ipairs(node.entries) do _scanExpr(e, cb) end end
    if node.upvalSlots then for _, u in ipairs(node.upvalSlots) do _scanExpr(u, cb) end end
end

local function visitStmtExprs(s, cb)
    -- Visit every expression-slot inside an IR statement.
    for _, k in ipairs({ "value", "source", "lhs", "rhs", "base", "index",
                        "name", "cond" }) do
        if s[k] then _scanExpr(s[k], cb) end
    end
    if s.args then
        for _, a in ipairs(s.args) do _scanExpr(a, cb) end
    end
    -- Targets are write positions; we still want to detect role-tagged regs
    -- (e.g. writing to ARGS or RETURN).
    if s.targets then
        for _, t in ipairs(s.targets) do _scanExpr(t, cb) end
    end
    if s.target then _scanExpr(s.target, cb) end
end

-- Pre-scan: does this function read ARGS anywhere? Either via the ARG_READ
-- IR kind, the inlined _irArgRead synthetic node, or via a direct reference
-- to a register with role=ARGS.
function _scanForUsesArgs(fn)
    local found = false
    walkStmts(fn.body, fn, function(s)
        if s.kind == K.ARG_READ then found = true end
        visitStmtExprs(s, function(e)
            if type(e) ~= "table" then return end
            if e.kind == "_irArgRead" then found = true; return end
            if isReg(e) and (e.role == "ARGS") then found = true; return end
        end)
    end)
    return found
end

-- ---------------------------------------------------------------------------
-- Top-level emission: produce the full program source.

-- Emit the body of the main function as the top-level program. We don't wrap
-- it in `function(...) ... end` -- it IS the chunk.
local function emitTopLevel(graph, structured)
    local mainFn
    for _, fn in ipairs(structured.fns) do
        if fn.isMain then mainFn = fn; break end
    end
    if not mainFn then
        return nil, "no main function"
    end

    local ctx = buildCtx(graph, structured, mainFn, nil)
    ctx:scanRegisters()

    local returnRegId = nil
    if graph.vm and graph.vm.returnReg and graph.vm.returnReg.regNode then
        returnRegId = graph.vm.returnReg.regNode.id
    end

    local lines = {}
    local function w(line) table.insert(lines, line) end

    if ctx.usesArgs or _scanForUsesArgs(mainFn) then
        ctx.usesArgs = true
        w("local args = {...}")
    end
    if #ctx.regsToDeclare > 0 then
        local names = {}
        for _, r in ipairs(ctx.regsToDeclare) do
            table.insert(names, regName(r))
        end
        w("local " .. table.concat(names, ", "))
    end
    emitUndeclaredIndexedBaseInits(ctx, "", w)

    -- Hoist slot ("loc_N") declarations for the main function.
    do
        local slotNames = slotNamesForFn(graph, mainFn)
        if #slotNames > 0 then
            w("local " .. table.concat(slotNames, ", "))
        end
    end

    bodyTextSmart(mainFn.body, ctx, 0, w, returnRegId)

    return table.concat(lines, "\n")
end

-- ---------------------------------------------------------------------------
-- In-VM AntiTamper stripping.
--
-- After devirtualization, the line-number / structure-based AntiTamper checks
-- that were embedded INSIDE the Vmify VM will fail because the dispatcher has
-- been removed. Detect the pattern and strip it from the structured tree so
-- the deobfuscated program runs correctly.
--
-- Detection heuristic:
--   1. Find all functions whose IR calls error("Tamper Detected!").
--   2. Find which closures/slots store those error functions.
--   3. In the main function's body tree, find the outermost if/else that gates
--      real code vs. the error path, and drop the error branch.

-- Return the set of entryIds for functions that call error("Tamper Detected!").
local function findAntiTamperErrorFns(graph)
    local errorFns = {}
    for _, fn in ipairs(graph.fns) do
        for _, blockId in ipairs(fn.blockIds or {}) do
            local d = graph.decompMap[blockId]
            if d then
                for _, s in ipairs(d.statements) do
                    if s.kind == K.CALL and s.args and #s.args >= 1 then
                        local base = s.base
                        -- Check if base is ENV["error"]
                        if s.kind == K.CALL and base and
                           ((isReg(base) and base.role == "ENV") or
                            (base.kind == "_irGlobalRead" and base.name and
                             base.name.kind == AstKind.StringExpression and
                             base.name.value == "error")) then
                            local arg1 = s.args[1]
                            if arg1 and arg1.kind == AstKind.StringExpression and
                               arg1.value and arg1.value:find("Tamper") then
                                errorFns[fn.entryId] = true
                            end
                        end
                        -- Also check inlined form: value is _irCall of ENV["error"]
                        if s.value and s.value.kind == "_irCall" then
                            local cv = s.value
                            if cv.base and cv.base.kind == "_irGlobalRead" and
                               cv.base.name and cv.base.name.kind == AstKind.StringExpression and
                               cv.base.name.value == "error" and
                               cv.args and #cv.args >= 1 then
                                local a1 = cv.args[1]
                                if a1 and a1.kind == AstKind.StringExpression and
                                   a1.value and a1.value:find("Tamper") then
                                    errorFns[fn.entryId] = true
                                end
                            end
                        end
                    end
                end
            end
        end
    end
    return errorFns
end

-- Find the slot name that stores an AntiTamper error function.
local function findAntiTamperSlot(graph, errorFns)
    for _, fn in ipairs(graph.fns) do
        for _, blockId in ipairs(fn.blockIds or {}) do
            local d = graph.decompMap[blockId]
            if d then
                for _, s in ipairs(d.statements) do
                    -- UPVAL_WRITE of a CREATE_CLOSURE whose entryId is an error fn
                    if s.kind == K.UPVAL_WRITE and s.value then
                        local v = s.value
                        if v.kind == "_irClosure" and errorFns[v.entryId] and s.slotName then
                            return s.slotName
                        end
                    end
                    if s.kind == K.CREATE_CLOSURE and errorFns[s.entryId] then
                        if s.initSlotName then return s.initSlotName end
                        if s.slotName then return s.slotName end
                    end
                end
            end
        end
    end
    return nil
end

-- Find closures that capture the error slot (they're the infinite-loop callers).
local function findAntiTamperLoopFns(graph, errorSlotName)
    local loopFns = {}
    -- Walk all expressions recursively looking for _irClosure nodes that
    -- capture the error slot.
    local function scan(e)
        if type(e) ~= "table" then return end
        if (e.kind == "_irClosure" or e.kind == K.CREATE_CLOSURE) and e.upvalNames then
            for _, uname in ipairs(e.upvalNames) do
                if uname == errorSlotName then
                    loopFns[e.entryId] = true
                    break
                end
            end
        end
        for _, k in ipairs({"lhs","rhs","base","index","value","source","name"}) do
            if e[k] then scan(e[k]) end
        end
        if e.args then for _, a in ipairs(e.args) do scan(a) end end
        if e.entries then for _, ent in ipairs(e.entries) do scan(ent) end end
    end
    for _, fn in ipairs(graph.fns) do
        for _, blockId in ipairs(fn.blockIds or {}) do
            local d = graph.decompMap[blockId]
            if d then
                for _, s in ipairs(d.statements) do
                    scan(s)
                    for _, k in ipairs({"value","source","base","index","name"}) do
                        if s[k] then scan(s[k]) end
                    end
                    if s.args then for _, a in ipairs(s.args) do scan(a) end end
                end
            end
        end
    end
    return loopFns
end

-- Check if a body (list of structured-tree nodes) references any of the given
-- function entryIds via closure calls in block statements.
local function bodyReferencesLoopFn(body, loopFns, graph)
    if not body then return false end
    for _, node in ipairs(body) do
        if node.kind == "block" and node.statements then
            for _, s in ipairs(node.statements) do
                -- Check for _irClosure or CREATE_CLOSURE referencing a loop fn.
                local function checkExpr(e)
                    if type(e) ~= "table" then return false end
                    if e.kind == "_irClosure" and loopFns[e.entryId] then return true end
                    for _, k in ipairs({"lhs","rhs","base","index","value","source","name"}) do
                        if e[k] and checkExpr(e[k]) then return true end
                    end
                    if e.args then
                        for _, a in ipairs(e.args) do
                            if checkExpr(a) then return true end
                        end
                    end
                    return false
                end
                for _, k in ipairs({"value","source","base","index","name"}) do
                    if s[k] and checkExpr(s[k]) then return true end
                end
                if s.args then
                    for _, a in ipairs(s.args) do
                        if checkExpr(a) then return true end
                    end
                end
            end
        end
        -- Recurse into nested if/else/loop bodies.
        if node.thenBody and bodyReferencesLoopFn(node.thenBody, loopFns, graph) then
            return true
        end
        if node.elseBody and bodyReferencesLoopFn(node.elseBody, loopFns, graph) then
            return true
        end
        if node.body and bodyReferencesLoopFn(node.body, loopFns, graph) then
            return true
        end
    end
    return false
end

-- Strip AntiTamper from the structured tree: find the `if` in the main fn
-- whose else branch leads to the error/loop functions and remove the else.
local function stripVmAntiTamper(graph, structured)
    local errorFns = findAntiTamperErrorFns(graph)
    local hasAny = false
    for _ in pairs(errorFns) do hasAny = true; break end
    if not hasAny then return false end

    local errorSlot = findAntiTamperSlot(graph, errorFns)
    if not errorSlot then return false end

    local loopFns = findAntiTamperLoopFns(graph, errorSlot)

    -- Walk the main fn's body tree. Find the outermost if whose else body
    -- references a loop fn, and strip the else (make the then unconditional).
    local mainFn
    for _, fn in ipairs(structured.fns) do
        if fn.isMain then mainFn = fn; break end
    end
    if not mainFn then return false end

    local stripped = false
    local function walkBody(body)
        for i, node in ipairs(body) do
            if node.kind == "if" and node.elseBody then
                if bodyReferencesLoopFn(node.elseBody, loopFns, graph) then
                    -- Replace the if/else with unconditional then body.
                    -- Remove the if node and splice the thenBody in place.
                    table.remove(body, i)
                    for j, thenNode in ipairs(node.thenBody) do
                        table.insert(body, i + j - 1, thenNode)
                    end
                    stripped = true
                    return
                end
            end
            -- Recurse into sub-bodies.
            if node.thenBody then walkBody(node.thenBody) end
            if node.elseBody then walkBody(node.elseBody) end
            if node.body then walkBody(node.body) end
        end
    end
    walkBody(mainFn.body)
    return stripped
end

-- ---------------------------------------------------------------------------
-- Public apply.

function M.apply(ast)
    local vm, errVm = recognize.recognize(ast)
    if not vm then
        return { note = "no Vmify VM detected" }
    end
    local extracted, errEx = extract.extract(vm)
    if not extracted then
        return { note = "block extraction failed: " .. tostring(errEx) }
    end
    local decomps = decompile.decompileAll(extracted, vm)
    local graph = cfg.build(decomps, extracted, vm)
    -- Cross-block liveness analysis to undo over-eager intra-block inlining
    -- of registers that are read in successor blocks.
    decompile.refineWithLiveness(graph, extracted, vm)
    closures.analyze(graph)
    local structured = structure.structure(graph)

    -- Strip in-VM AntiTamper (line-number / structure checks that fail after
    -- the dispatcher has been removed).
    stripVmAntiTamper(graph, structured)

    -- Per-function source caches.
    _functionLiteralCache = {}
    -- Stash RETURN reg id on graph for downstream lookups.
    graph.vm = vm

    local source, err = emitTopLevel(graph, structured)
    _functionLiteralCache = nil
    if not source then
        return { note = "devirtualize failed: " .. tostring(err) }
    end

    -- Always dump the emitted source if DEVIRT_DUMP is set, even when the
    -- parser accepts it. Useful for debugging the textual emission.
    do
        local dump = os.getenv("DEVIRT_DUMP")
        if dump then
            local fh = io.open(dump, "wb")
            if fh then fh:write(source); fh:close() end
        end
    end

    -- Parse the reconstructed source and graft it in place of ast.body.
    local newAst
    local okParse, parseErr = pcall(function()
        local parser = Parser:new({ LuaVersion = Enums.LuaVersion.Lua51 })
        newAst = parser:parse(source)
    end)
    if not okParse or not newAst then
        return {
            note = "devirtualize emitted source but parser rejected it: " .. tostring(parseErr),
            source = source,
        }
    end
    ast.body = newAst.body
    ast.globalScope = newAst.globalScope
    return { note = ("devirtualized %d function(s)"):format(#structured.fns) }
end

return M
