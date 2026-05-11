-- prometheus-test-deobfuscator -- Vmify IR (intermediate representation).
--
-- A block decompiled from the dispatcher container produces a sequence of
-- *IR statements*. An IR statement is a plain Lua table; the field set
-- depends on `kind`. See `M.kinds` for the enumeration.
--
-- IR statements are *register-level* but with VM machinery already pulled
-- out (so e.g. UPVALS_TABLE indexing becomes UPVAL_READ/UPVAL_WRITE; ENV
-- table indexing becomes GLOBAL_READ/GLOBAL_WRITE; ARGS[i] becomes
-- ARG_READ; CREATE_CLOSURE_K calls become CREATE_CLOSURE).
--
-- The control-flow exit of a block is also expressed as an IR statement
-- (JUMP_CONST / JUMP_COND / RETURN).
--
-- Operands are AST expressions. In the simplest "raw" form, they are the
-- exact AST nodes from the original dispatcher; after the inliner pass
-- they may be slightly synthesised (e.g. an inlined StrCatExpression that
-- replaces a register reference). Callers should treat operand AST as
-- read-only and not assume scope-uniqueness.
--
-- Register references in operands are tagged via `M.regRef(scope, id)`
-- (which returns a tagged proxy that the IR-printer recognises). Plain
-- AST VariableExpression nodes still appear for non-register variables
-- (e.g. helpers) but should be rare after decompilation.

local Ast = require("prometheus.ast")
local AstKind = Ast.AstKind

local M = {}

M.kinds = {
    -- Register-level operations.
    LOAD            = "LOAD",            -- target = expr (constant or pure expression)
    COPY            = "COPY",            -- target = source_register
    BINOP           = "BINOP",           -- target = lhs <op> rhs
    UNOP            = "UNOP",            -- target = <op> rhs
    -- Function/method invocation.
    CALL            = "CALL",            -- targets[] = base(args...)
    -- VM helpers.
    ARG_READ        = "ARG_READ",        -- target = ARGS[index]
    UPVAL_READ      = "UPVAL_READ",      -- target = UPVALS_TABLE[UPVALS[index]]
    UPVAL_WRITE     = "UPVAL_WRITE",     -- UPVALS_TABLE[UPVALS[index]] = value
    UPVAL_ALLOC     = "UPVAL_ALLOC",     -- target = ALLOC_UPVAL()        (allocates new slot id, used in parent scope)
    UPVAL_INIT      = "UPVAL_INIT",      -- UPVALS_TABLE[slot_reg] = value (parent scope writes to a freshly-allocated slot)
    GLOBAL_READ     = "GLOBAL_READ",     -- target = ENV[name]
    GLOBAL_WRITE    = "GLOBAL_WRITE",    -- ENV[name] = value
    INDEX_READ      = "INDEX_READ",      -- target = base[index]
    INDEX_WRITE     = "INDEX_WRITE",     -- base[index] = value
    CREATE_CLOSURE  = "CREATE_CLOSURE",  -- target = CREATE_CLOSURE_K(entryId, {upval_slots...}) ; isVararg if K is the vararg variant
    -- Control flow exits (one of these always terminates a block).
    JUMP_CONST      = "JUMP_CONST",      -- pos = N
    JUMP_COND       = "JUMP_COND",       -- pos = (cond and trueId) or falseId
    RETURN          = "RETURN",          -- pos = ENV.<random>; (logically: return UNPACK(returnReg))
    -- Misc.
    NOP             = "NOP",             -- placeholder (removed by inliner)
    UNKNOWN         = "UNKNOWN",         -- could not classify; carries raw AST for inspection
}

-- ----------------------------------------------------------------------------
-- Register reference tag.
--
-- A "register" in the IR is identified by its (scope, id). To distinguish
-- register references from arbitrary AST expressions we wrap them in a
-- dedicated table. Code that sees an operand should:
--   - check `node._isReg` to decide if it's a register or a raw AST expr
--   - register: read `node.scope` and `node.id`
--   - else: treat as a Prometheus AST expression
--
-- Constructed via M.regRef(scope, id) so the impl detail is centralised.

function M.regRef(scope, id, role)
    -- `role` (optional): one of "POS", "ARGS", "UPVALS", "GC", "RETURN",
    -- "GENERAL". Used for printing / classification.
    return {
        _isReg = true,
        scope  = scope,
        id     = id,
        role   = role or "GENERAL",
    }
end

function M.isReg(node)
    return type(node) == "table" and node._isReg == true
end

-- Compare two register refs (or AST variables) for identity.
function M.sameReg(a, b)
    if not a or not b then return false end
    if M.isReg(a) and M.isReg(b) then return a.scope == b.scope and a.id == b.id end
    -- Fall back to comparing by (scope, id) attributes; this lets us mix
    -- register tags with raw VariableExpression / AssignmentVariable nodes
    -- where useful.
    return a.scope and b.scope and a.scope == b.scope and a.id == b.id
end

-- ----------------------------------------------------------------------------
-- IR statement printers.

local function regString(reg)
    if not reg then return "?" end
    if M.isReg(reg) then
        local rolePrefix = reg.role and ("@" .. reg.role) or ""
        local name
        local ok, n = pcall(function() return reg.scope:getVariableName(reg.id) end)
        if ok and n then name = n end
        return ("R%d%s%s"):format(reg.id, rolePrefix, name and ("(" .. name .. ")") or "")
    end
    return "?"
end

local exprString
exprString = function(e)
    if e == nil then return "nil" end
    if M.isReg(e) then return regString(e) end
    if type(e) ~= "table" or not e.kind then return tostring(e) end
    local k = e.kind
    -- Synthetic IR-internal expression nodes (created by the inliner so we
    -- can carry "rich" inline values without round-tripping through real
    -- AST construction).
    if k == "_irBinop"      then return "(" .. exprString(e.lhs) .. " " .. e.op .. " " .. exprString(e.rhs) .. ")" end
    if k == "_irUnop"       then return "(" .. e.op .. exprString(e.rhs) .. ")" end
    if k == "_irArgRead"    then return "ARGS[" .. exprString(e.index) .. "]" end
    if k == "_irUpvalRead"  then
        if e.slotName then return e.slotName end
        return "UPVAL[" .. exprString(e.index) .. "]"
    end
    if k == "_irGlobalRead" then return "ENV[" .. exprString(e.name) .. "]" end
    if k == "_irIndexRead"  then return exprString(e.base) .. "[" .. exprString(e.index) .. "]" end
    if k == "_irClosure" then
        local nUpvals = (e.upvalSlots and #e.upvalSlots) or 0
        if nUpvals == 0 then
            return ("fn_%d%s"):format(e.entryId, e.isVararg and "[vararg]" or "")
        end
        local parts = {}
        for i = 1, nUpvals do
            local n = e.upvalNames and e.upvalNames[i]
            if n then
                table.insert(parts, n)
            else
                table.insert(parts, exprString(e.upvalSlots[i]))
            end
        end
        return ("fn_%d%s[%s]"):format(
            e.entryId,
            e.isVararg and "[vararg]" or "",
            table.concat(parts, ", "))
    end
    if k == "_irCall" then
        local args = {}
        for _, a in ipairs(e.args or {}) do table.insert(args, exprString(a)) end
        local prefix = e.tableWrapped and "{" or ""
        local suffix = e.tableWrapped and "}" or ""
        return prefix .. exprString(e.base) .. "(" .. table.concat(args, ", ") .. ")" .. suffix
    end
    if k == AstKind.NumberExpression  then return tostring(e.value) end
    if k == AstKind.StringExpression  then return ("%q"):format(e.value) end
    if k == AstKind.BooleanExpression then return tostring(e.value) end
    if k == AstKind.NilExpression     then return "nil" end
    if k == AstKind.VariableExpression or k == AstKind.AssignmentVariable then
        local name
        local ok, n = pcall(function() return e.scope:getVariableName(e.id) end)
        if ok and n then name = n end
        return ("V%d%s"):format(e.id, name and ("(" .. name .. ")") or "")
    end
    if k == AstKind.VarargExpression then return "..." end
    if k == AstKind.IndexExpression then return exprString(e.base) .. "[" .. exprString(e.index) .. "]" end
    if k == AstKind.FunctionCallExpression then
        local args = {}
        for _, a in ipairs(e.args) do table.insert(args, exprString(a)) end
        return exprString(e.base) .. "(" .. table.concat(args, ", ") .. ")"
    end
    if k == AstKind.PassSelfFunctionCallExpression then
        local args = {}
        for _, a in ipairs(e.args) do table.insert(args, exprString(a)) end
        return exprString(e.base) .. ":" .. (e.passSelfFunctionName or "?")
            .. "(" .. table.concat(args, ", ") .. ")"
    end
    if k == AstKind.OrExpression       then return "(" .. exprString(e.lhs) .. " or "  .. exprString(e.rhs) .. ")" end
    if k == AstKind.AndExpression      then return "(" .. exprString(e.lhs) .. " and " .. exprString(e.rhs) .. ")" end
    if k == AstKind.LessThanExpression then return "(" .. exprString(e.lhs) .. " < "   .. exprString(e.rhs) .. ")" end
    if k == AstKind.GreaterThanExpression then return "(" .. exprString(e.lhs) .. " > " .. exprString(e.rhs) .. ")" end
    if k == AstKind.LessThanOrEqualsExpression then return "(" .. exprString(e.lhs) .. " <= " .. exprString(e.rhs) .. ")" end
    if k == AstKind.GreaterThanOrEqualsExpression then return "(" .. exprString(e.lhs) .. " >= " .. exprString(e.rhs) .. ")" end
    if k == AstKind.EqualsExpression   then return "(" .. exprString(e.lhs) .. " == "  .. exprString(e.rhs) .. ")" end
    if k == AstKind.NotEqualsExpression then return "(" .. exprString(e.lhs) .. " ~= " .. exprString(e.rhs) .. ")" end
    if k == AstKind.AddExpression      then return "(" .. exprString(e.lhs) .. " + "   .. exprString(e.rhs) .. ")" end
    if k == AstKind.SubExpression      then return "(" .. exprString(e.lhs) .. " - "   .. exprString(e.rhs) .. ")" end
    if k == AstKind.MulExpression      then return "(" .. exprString(e.lhs) .. " * "   .. exprString(e.rhs) .. ")" end
    if k == AstKind.DivExpression      then return "(" .. exprString(e.lhs) .. " / "   .. exprString(e.rhs) .. ")" end
    if k == AstKind.ModExpression      then return "(" .. exprString(e.lhs) .. " % "   .. exprString(e.rhs) .. ")" end
    if k == AstKind.PowExpression      then return "(" .. exprString(e.lhs) .. " ^ "   .. exprString(e.rhs) .. ")" end
    if k == AstKind.StrCatExpression   then return "(" .. exprString(e.lhs) .. " .. "  .. exprString(e.rhs) .. ")" end
    if k == AstKind.NotExpression      then return "(not " .. exprString(e.rhs) .. ")" end
    if k == AstKind.NegateExpression   then return "(- "   .. exprString(e.rhs) .. ")" end
    if k == AstKind.LenExpression      then return "(# "   .. exprString(e.rhs) .. ")" end
    if k == AstKind.TableConstructorExpression then
        local entries = {}
        for _, en in ipairs(e.entries) do
            if en.kind == AstKind.KeyedTableEntry then
                table.insert(entries, "[" .. exprString(en.key) .. "]=" .. exprString(en.value))
            else
                table.insert(entries, exprString(en.value))
            end
        end
        return "{" .. table.concat(entries, ", ") .. "}"
    end
    if k == AstKind.FunctionLiteralExpression then return "<func>" end
    return "?<" .. tostring(k) .. ">"
end

M.exprString = exprString
M.regString  = regString

-- One-line summary for an IR statement, suitable for --vm-decompile output.
function M.statString(s)
    local k = s.kind
    if k == M.kinds.LOAD then
        return ("%s = %s"):format(regString(s.target), exprString(s.value))
    elseif k == M.kinds.COPY then
        return ("%s = %s"):format(regString(s.target), exprString(s.source))
    elseif k == M.kinds.BINOP then
        return ("%s = %s %s %s"):format(regString(s.target), exprString(s.lhs), s.op, exprString(s.rhs))
    elseif k == M.kinds.UNOP then
        return ("%s = %s%s"):format(regString(s.target), s.op, exprString(s.rhs))
    elseif k == M.kinds.CALL then
        local targets = {}
        for _, t in ipairs(s.targets) do table.insert(targets, regString(t)) end
        local args = {}
        for _, a in ipairs(s.args) do table.insert(args, exprString(a)) end
        local lhs = (#targets > 0 and (table.concat(targets, ", ") .. " = ")) or ""
        local prefix = s.tableWrapped and "{" or ""
        local suffix = s.tableWrapped and "}" or ""
        return ("%s%s%s(%s)%s"):format(lhs, prefix, exprString(s.base), table.concat(args, ", "), suffix)
    elseif k == M.kinds.ARG_READ then
        return ("%s = ARGS[%s]"):format(regString(s.target), exprString(s.index))
    elseif k == M.kinds.UPVAL_READ then
        if s.slotName then
            return ("%s = %s"):format(regString(s.target), s.slotName)
        end
        return ("%s = UPVAL[%s]"):format(regString(s.target), exprString(s.index))
    elseif k == M.kinds.UPVAL_WRITE then
        if s.initSlotName then
            return ("local %s = %s"):format(s.initSlotName, exprString(s.value))
        end
        if s.slotName then
            return ("%s = %s"):format(s.slotName, exprString(s.value))
        end
        return ("UPVAL[%s] = %s"):format(exprString(s.index), exprString(s.value))
    elseif k == M.kinds.UPVAL_ALLOC then
        if s.initStmt then
            -- Paired with an immediate UPVAL_WRITE init; the printer can
            -- safely drop this statement (the init line will emit
            -- `local <name> = ...`). We still return a string for callers
            -- that don't filter.
            return ("-- local %s = (init below)"):format(s.slotName or "<unnamed>")
        end
        if s.slotName then
            return ("local %s"):format(s.slotName)
        end
        return ("%s = ALLOC_UPVAL()"):format(regString(s.target))
    elseif k == M.kinds.UPVAL_INIT then
        return ("UPVAL_TABLE[%s] = %s"):format(exprString(s.slot), exprString(s.value))
    elseif k == M.kinds.GLOBAL_READ then
        return ("%s = ENV[%s]"):format(regString(s.target), exprString(s.name))
    elseif k == M.kinds.GLOBAL_WRITE then
        return ("ENV[%s] = %s"):format(exprString(s.name), exprString(s.value))
    elseif k == M.kinds.INDEX_READ then
        return ("%s = %s[%s]"):format(regString(s.target), exprString(s.base), exprString(s.index))
    elseif k == M.kinds.INDEX_WRITE then
        return ("%s[%s] = %s"):format(exprString(s.base), exprString(s.index), exprString(s.value))
    elseif k == M.kinds.CREATE_CLOSURE then
        local nUpvals = (s.upvalSlots and #s.upvalSlots) or 0
        local body
        if nUpvals == 0 then
            body = ("fn_%d%s"):format(s.entryId, s.isVararg and "[vararg]" or "")
        else
            local parts = {}
            for i = 1, nUpvals do
                local n = s.upvalNames and s.upvalNames[i]
                if n then
                    table.insert(parts, n)
                else
                    table.insert(parts, exprString(s.upvalSlots[i]))
                end
            end
            body = ("fn_%d%s[%s]"):format(s.entryId, s.isVararg and "[vararg]" or "",
                                           table.concat(parts, ", "))
        end
        return ("%s = %s"):format(regString(s.target), body)
    elseif k == M.kinds.JUMP_CONST then
        return ("JUMP %d"):format(s.target)
    elseif k == M.kinds.JUMP_COND then
        return ("JUMP_IF %s ? %d : %d"):format(exprString(s.cond), s.trueTarget, s.falseTarget)
    elseif k == M.kinds.RETURN then
        return "RETURN"
    elseif k == M.kinds.NOP then
        return "(nop)"
    elseif k == M.kinds.UNKNOWN then
        return ("UNKNOWN: %s"):format(s.note or "?")
    end
    return "?<"..tostring(k)..">"
end

return M
