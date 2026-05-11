-- prometheus-test-deobfuscator -- Vmify VM recognizer.
--
-- Detects the outer Vmify wrap of the form
--
--   return ((function(ENV, NEWPROXY, UNPACK, GETMT, SELECT, SETMT, VARARG, ...)
--       <multi-assign of all VM helpers>
--       return CREATE_VARARG_CLOSURE(ENTRY_ID, {})(UNPACK(VARARG))
--   end))(getfenv() or _ENV, newproxy, unpack or table.unpack,
--         getmetatable, select, setmetatable, {...})
--
-- and exposes structural references to every VM helper plus the entry block id.
-- Returns a `vm` descriptor table, or nil + reason if the script does not look
-- like a Vmify VM (e.g. the source was not actually obfuscated, or a future
-- Prometheus version changed the calling convention).
--
-- Used by extract.lua / decompile.lua / replace.lua.

local Ast = require("prometheus.ast")
local astu = require("deobfuscator.ast_utils")

local AstKind = Ast.AstKind
local M = {}

-- ----------------------------------------------------------------------------
-- Small structural helpers.

local function isFunctionLiteral(node)
    return node and node.kind == AstKind.FunctionLiteralExpression
end

local function isCall(node)
    return node and node.kind == AstKind.FunctionCallExpression
end

local function isVar(node)
    return node and node.kind == AstKind.VariableExpression
end

local function isNumber(node)
    return node and node.kind == AstKind.NumberExpression
end

local function functionBody(node)
    return node and node.body
end

local function statementsOf(block)
    return block and block.statements or {}
end

-- Returns the single element of a list-like table, else nil.
local function singleton(list)
    if type(list) ~= "table" then return nil end
    if #list == 1 then return list[1] end
    return nil
end

-- ----------------------------------------------------------------------------
-- Outer wrap: return ((function(...) BODY end))(getfenv,...)
--
-- After Phase 1 has unwrapped *its* WrapInFunction layer, what's left is the
-- VM-specific outer wrap. This is the single statement we expect to find at
-- the top of `ast.body`.

local function findOuterWrap(ast)
    if not ast or not ast.body then
        return nil, "no AST body"
    end
    local stats = statementsOf(ast.body)
    if #stats ~= 1 then
        return nil, "expected single top-level statement, got " .. tostring(#stats)
    end

    local ret = stats[1]
    if not ret or ret.kind ~= AstKind.ReturnStatement then
        return nil, "top-level statement is not a return"
    end
    if not ret.args or #ret.args ~= 1 then
        return nil, "top-level return takes "
            .. tostring(ret.args and #ret.args or 0) .. " value(s)"
    end

    local call = ret.args[1]
    if not isCall(call) then
        return nil, "top-level return is not a function call"
    end
    if not isFunctionLiteral(call.base) then
        return nil, "top-level call base is not a function literal"
    end

    return {
        returnStatement = ret,
        call            = call,
        wrapper         = call.base,
        wrapperArgs     = call.args or {},
        wrapperParams   = call.base.args or {},
        wrapperBody     = call.base.body,
    }
end

-- ----------------------------------------------------------------------------
-- Identify the canonical wrapper-arg expressions:
--   getfenv() or _ENV       -- ENV
--   newproxy                -- NEWPROXY
--   unpack or table.unpack  -- UNPACK
--   getmetatable            -- GETMT
--   select                  -- SELECT
--   setmetatable            -- SETMT
--   {...}                   -- VARARG (table holding the script's vararg)
--
-- The order produced by Prometheus is fixed (compiler.lua, see the call to
-- Ast.FunctionCallExpression that closes out the script). We just verify the
-- shapes.

-- ENV is expressed either as `getfenv() or _ENV` or as `(getfenv and getfenv()) or _ENV`,
-- depending on the Prometheus version. Both shapes share the OR with `_ENV` on the
-- right-hand side and a getfenv-call somewhere on the left.
local function isGetfenvOrEnv(node)
    if not node then return false end
    if node.kind ~= AstKind.OrExpression then return false end
    local rhs = node.rhs
    if not (isVar(rhs) and rhs.scope:getVariableName(rhs.id) == "_ENV") then
        return false
    end
    local lhs = node.lhs
    -- Direct call: getfenv()
    if isCall(lhs) and isVar(lhs.base)
            and lhs.base.scope:getVariableName(lhs.base.id) == "getfenv" then
        return true
    end
    -- Guarded: (getfenv and getfenv()) -- AndExpression(Var<getfenv>, Call(Var<getfenv>))
    if lhs and lhs.kind == AstKind.AndExpression then
        local a, b = lhs.lhs, lhs.rhs
        local aOk = isVar(a) and a.scope:getVariableName(a.id) == "getfenv"
        local bOk = isCall(b) and isVar(b.base)
            and b.base.scope:getVariableName(b.base.id) == "getfenv"
        if aOk and bOk then return true end
    end
    return false
end

local function isUnpackOrTableUnpack(node)
    if not node then return false end
    if node.kind ~= AstKind.OrExpression then return false end
    local lhs, rhs = node.lhs, node.rhs
    if not isVar(lhs) then return false end
    if lhs.scope:getVariableName(lhs.id) ~= "unpack" then return false end
    if rhs.kind ~= AstKind.IndexExpression then return false end
    if not isVar(rhs.base) then return false end
    if rhs.base.scope:getVariableName(rhs.base.id) ~= "table" then return false end
    if rhs.index.kind ~= AstKind.StringExpression then return false end
    return rhs.index.value == "unpack"
end

local function isPlainGlobal(node, name)
    return isVar(node) and node.scope:getVariableName(node.id) == name
end

local function isVarargTable(node)
    if not node then return false end
    if node.kind ~= AstKind.TableConstructorExpression then return false end
    if #node.entries ~= 1 then return false end
    local e = node.entries[1]
    if e.kind ~= AstKind.TableEntry then return false end
    return e.value and e.value.kind == AstKind.VarargExpression
end

local OUTER_ARG_VALIDATORS = {
    function(n) return isGetfenvOrEnv(n)        end, -- 1: ENV
    function(n) return isPlainGlobal(n,"newproxy")     end, -- 2: NEWPROXY
    function(n) return isUnpackOrTableUnpack(n) end, -- 3: UNPACK
    function(n) return isPlainGlobal(n,"getmetatable") end, -- 4: GETMT
    function(n) return isPlainGlobal(n,"select")       end, -- 5: SELECT
    function(n) return isPlainGlobal(n,"setmetatable") end, -- 6: SETMT
    function(n) return isVarargTable(n)         end, -- 7: VARARG
}
local OUTER_ARG_NAMES = {
    "ENV", "NEWPROXY", "UNPACK", "GETMT", "SELECT", "SETMT", "VARARG",
}

-- Prometheus shuffles the order of the 7 outer args (compiler.lua:301-304).
-- We therefore classify each of the first 7 args independently and permute.
local function classifyOuterArgs(wrapperArgs, wrapperParams)
    if #wrapperArgs < 7 then
        return nil, "wrapper takes "
            .. tostring(#wrapperArgs) .. " arg(s); expected >= 7"
    end

    local matched = {}      -- name -> slot (1..7)
    local takenSlot = {}    -- slot -> true
    for i = 1, 7 do
        local arg = wrapperArgs[i]
        local matches = {}
        for j, validator in ipairs(OUTER_ARG_VALIDATORS) do
            if validator(arg) then
                table.insert(matches, OUTER_ARG_NAMES[j])
            end
        end
        if #matches == 0 then
            return nil, ("wrapper arg #%d does not match any known outer-arg shape"):format(i)
        end
        if #matches > 1 then
            return nil, ("wrapper arg #%d ambiguous (%s)"):format(i, table.concat(matches, ","))
        end
        local name = matches[1]
        if matched[name] then
            return nil, ("wrapper arg #%d duplicates %s (already at slot %d)"):format(
                i, name, matched[name])
        end
        matched[name] = i
        takenSlot[i] = true
    end
    for _, name in ipairs(OUTER_ARG_NAMES) do
        if not matched[name] then
            return nil, ("wrapper missing outer arg %s"):format(name)
        end
    end

    local out = {}
    for _, name in ipairs(OUTER_ARG_NAMES) do
        local slot = matched[name]
        local param = wrapperParams[slot]
        if not isVar(param) then
            return nil, ("wrapper param #%d is not a variable"):format(slot)
        end
        out[name] = {
            scope = param.scope,
            id    = param.id,
            param = param,
            value = wrapperArgs[slot],
            slot  = slot,
        }
    end
    -- Extra params (after #7) are just internal locals introduced by the wrap;
    -- Prometheus declares 17 params total but only the first 7 are passed in.
    -- We capture the remaining param identifiers anyway because the helpers'
    -- multi-assign will reference them on the LHS.
    out._extraParams = {}
    for i = 8, #wrapperParams do
        local p = wrapperParams[i]
        if isVar(p) then
            table.insert(out._extraParams, { scope = p.scope, id = p.id, param = p })
        end
    end
    return out
end

-- ----------------------------------------------------------------------------
-- The single multi-assign that introduces all VM helpers.
--
-- After Phase 1, the wrapperBody contains exactly two top-level statements:
--   1. AssignmentStatement with N LHS variables (the wrap's extra params)
--      and N RHS expressions (the helper definitions).
--   2. ReturnStatement with the entry-closure call.

local function findHelpersAssignment(wrapperBody, outerArgs)
    if not wrapperBody or not wrapperBody.statements then
        return nil, "wrapper body has no statements"
    end
    local stats = wrapperBody.statements

    if #stats < 2 then
        return nil, "wrapper body needs >= 2 statements (multi-assign + return)"
    end

    -- The multi-assign should be the first statement and should target only
    -- variables declared as wrapper parameters (the "extras", i.e. params
    -- 8..#wrapperParams).
    local assign = stats[1]
    if not assign or assign.kind ~= AstKind.AssignmentStatement then
        return nil, "first wrapper-body statement is not an AssignmentStatement"
    end
    if #assign.lhs == 0 or #assign.lhs ~= #assign.rhs then
        return nil, "multi-assign LHS/RHS arity mismatch"
    end

    -- Map each LHS to one of the wrap's extra params.
    local extraSet = {}
    for _, p in ipairs(outerArgs._extraParams) do
        extraSet[p.scope] = extraSet[p.scope] or {}
        extraSet[p.scope][p.id] = true
    end
    for i, lhs in ipairs(assign.lhs) do
        if lhs.kind ~= AstKind.AssignmentVariable then
            return nil, ("multi-assign LHS #%d is not an AssignmentVariable"):format(i)
        end
        if not (extraSet[lhs.scope] and extraSet[lhs.scope][lhs.id]) then
            return nil, ("multi-assign LHS #%d targets a variable that is not a wrap-extra param"):format(i)
        end
    end

    return assign
end

-- ----------------------------------------------------------------------------
-- Helper classifier.
--
-- Each predicate consumes an RHS expression (one of the values in the
-- multi-assign) plus the surrounding outerArgs (so it can check that the
-- helper references the canonical NEWPROXY/SETMT/etc. params).
--
-- We classify by structure rather than name because Prometheus mangles
-- identifiers and shuffles the assign order. The classifiers are stricter
-- than strictly necessary -- if a future Prometheus version changes shape,
-- the recognizer will degrade gracefully (return nil, reason) instead of
-- producing wrong output.

local function refsGlobal(expr, name, outer)
    if not isVar(expr) then return false end
    -- Either references a wrap param classified as `name` (canonical), or a
    -- _global_ scope variable with that literal name (rare fallback).
    local entry = outer and outer[name]
    if entry then
        return expr.scope == entry.scope and expr.id == entry.id
    end
    return expr.scope:getVariableName(expr.id) == name
end

local function isEmptyTableConstructor(expr)
    return expr
        and expr.kind == AstKind.TableConstructorExpression
        and (not expr.entries or #expr.entries == 0)
end

local function isZeroLiteral(expr)
    return isNumber(expr) and expr.value == 0
end

-- Classifier predicates (pure-structure, no name lookups except into outer).
local CLASSIFIERS = {}

-- CONTAINER: function(POS, ARGS, UPVALS, GC) ... while POS do <bigif> end ...
function CLASSIFIERS.CONTAINER(expr)
    if not isFunctionLiteral(expr) then return false end
    if not expr.args or #expr.args ~= 4 then return false end
    local stats = statementsOf(expr.body)

    -- Look for a `while <var> do ... end` whose condition is the first
    -- function arg (POS). Allow some prefix statements (local register
    -- declarations etc.).
    local posVar = expr.args[1]
    if not isVar(posVar) then return false end

    local function refsPos(node)
        return isVar(node)
            and node.scope == posVar.scope and node.id == posVar.id
    end

    for _, s in ipairs(stats) do
        if s.kind == AstKind.WhileStatement then
            if refsPos(s.condition) then return true end
        end
    end
    return false
end

-- UPVALS_TABLE / REF_COUNTS: literal {} -- two helpers share the same shape.
function CLASSIFIERS.EMPTY_TABLE(expr)
    return isEmptyTableConstructor(expr)
end

-- CURRENT_UPVAL_ID: literal 0 (the upval-id counter, incremented by ALLOC_UPVAL).
function CLASSIFIERS.CURRENT_UPVAL_ID(expr)
    return isZeroLiteral(expr)
end

-- ALLOC_UPVAL: function() <id> = 1 + <id>; <ref_counts>[<id>] = 1; return <id> end
-- (or `<id> = <id> + 1`; Prometheus generates both orderings via shuffle).
function CLASSIFIERS.ALLOC_UPVAL(expr)
    if not isFunctionLiteral(expr) then return false end
    if not expr.args or #expr.args ~= 0 then return false end
    local stats = statementsOf(expr.body)
    if #stats < 3 then return false end

    -- Find an assignment that is x = 1 + x or x = x + 1
    local idVar
    for _, s in ipairs(stats) do
        if s.kind == AstKind.AssignmentStatement
                and #s.lhs == 1 and #s.rhs == 1
                and s.lhs[1].kind == AstKind.AssignmentVariable
                and s.rhs[1].kind == AstKind.AddExpression then
            local r = s.rhs[1]
            local lhs = s.lhs[1]
            local function isOne(n)
                return isNumber(n) and n.value == 1
            end
            local function isLhsVar(n)
                return isVar(n) and n.scope == lhs.scope and n.id == lhs.id
            end
            if (isOne(r.lhs) and isLhsVar(r.rhs))
                    or (isLhsVar(r.lhs) and isOne(r.rhs)) then
                idVar = lhs
                break
            end
        end
    end
    if not idVar then return false end

    -- Find a return that returns idVar.
    local lastRet = stats[#stats]
    if not lastRet or lastRet.kind ~= AstKind.ReturnStatement then return false end
    if #lastRet.args ~= 1 then return false end
    local r = lastRet.args[1]
    if not (isVar(r) and r.scope == idVar.scope and r.id == idVar.id) then
        return false
    end
    return true
end

-- FREE_UPVAL: function(x) ref[x] = ref[x] - 1; if ref[x] == 0 then upvals[x],
-- ref[x] = nil, nil end end
function CLASSIFIERS.FREE_UPVAL(expr)
    if not isFunctionLiteral(expr) then return false end
    if not expr.args or #expr.args ~= 1 then return false end
    local stats = statementsOf(expr.body)
    if #stats < 2 then return false end

    -- First statement: AssignmentStatement t[x] = t[x] - 1
    local s1 = stats[1]
    if s1.kind ~= AstKind.AssignmentStatement then return false end
    if #s1.lhs ~= 1 or #s1.rhs ~= 1 then return false end
    if s1.lhs[1].kind ~= AstKind.AssignmentIndexing then return false end
    if s1.rhs[1].kind ~= AstKind.SubExpression then return false end
    if not (isNumber(s1.rhs[1].rhs) and s1.rhs[1].rhs.value == 1) then
        return false
    end
    -- Some statement must be an IfStatement with `==`/`<=`-zero condition.
    for _, s in ipairs(stats) do
        if s.kind == AstKind.IfStatement then
            local c = s.condition
            if c and (c.kind == AstKind.EqualsExpression
                    or c.kind == AstKind.NotEqualsExpression) then
                if (isNumber(c.lhs) and c.lhs.value == 0)
                        or (isNumber(c.rhs) and c.rhs.value == 0) then
                    return true
                end
            end
        end
    end
    return false
end

-- Helpers: detect the canonical `function(s, f) local x = PROXY_FN(f); local n =
-- function(...) return CONTAINER(s, ARGS, f, x) end; return n end` shape used by
-- the closure factories. Both CREATE_CLOSURE and CREATE_VARARG_CLOSURE share the
-- same shell -- the only difference is whether the inner closure is vararg.
local function matchClosureFactory(expr, wantVararg)
    if not isFunctionLiteral(expr) then return false end
    if not expr.args or #expr.args ~= 2 then return false end
    local stats = statementsOf(expr.body)
    if #stats < 3 then return false end
    local sParam = expr.args[1]
    local fParam = expr.args[2]
    if not (isVar(sParam) and isVar(fParam)) then return false end

    -- Statement 1: local x = <call>(f)
    local s1 = stats[1]
    if s1.kind ~= AstKind.LocalVariableDeclaration then return false end
    if not s1.ids or #s1.ids ~= 1 then return false end
    if not s1.expressions or #s1.expressions ~= 1 then return false end
    local s1Rhs = s1.expressions[1]
    if not isCall(s1Rhs) then return false end
    if not isVar(s1Rhs.base) then return false end
    if not (s1Rhs.args and #s1Rhs.args == 1
            and isVar(s1Rhs.args[1])
            and s1Rhs.args[1].scope == fParam.scope
            and s1Rhs.args[1].id    == fParam.id) then
        return false
    end
    local xId, xScope = s1.ids[1], s1.scope or s1Rhs.base.scope
    -- xScope is the scope in which x was declared; we don't have a direct ref,
    -- but we can reach the variable via the inner function body.

    -- Statement 2: local n = function(args) return <CONTAINER>(s, ARGS_TBL, f, x) end
    local s2 = stats[2]
    if s2.kind ~= AstKind.LocalVariableDeclaration then return false end
    if not s2.expressions or #s2.expressions ~= 1 then return false end
    local fn = s2.expressions[1]
    if not isFunctionLiteral(fn) then return false end
    -- Vararg / non-vararg discrimination.
    local lastArg = fn.args[#fn.args]
    local hasVararg = lastArg and lastArg.kind == AstKind.VarargExpression
    if wantVararg and not hasVararg then return false end
    if not wantVararg and hasVararg then return false end

    -- Inside the inner closure, the body should be `return CONTAINER(s, ARGS_TBL, f, x)`.
    local innerStats = statementsOf(fn.body)
    if #innerStats ~= 1 then return false end
    local ret = innerStats[1]
    if ret.kind ~= AstKind.ReturnStatement then return false end
    if #ret.args ~= 1 then return false end
    local call = ret.args[1]
    if not isCall(call) then return false end
    if not isVar(call.base) then return false end
    if #call.args ~= 4 then return false end
    -- arg1 == s
    local a1 = call.args[1]
    if not (isVar(a1) and a1.scope == sParam.scope and a1.id == sParam.id) then
        return false
    end
    -- arg3 == f
    local a3 = call.args[3]
    if not (isVar(a3) and a3.scope == fParam.scope and a3.id == fParam.id) then
        return false
    end
    -- arg2 = ARGS_TBL: a TableConstructorExpression. For vararg variant the
    -- single entry is `...`; for non-vararg, every entry references a local
    -- closure parameter.
    local a2 = call.args[2]
    if not (a2 and a2.kind == AstKind.TableConstructorExpression) then
        return false
    end
    if wantVararg then
        if #a2.entries ~= 1 then return false end
        local e = a2.entries[1]
        if not (e.kind == AstKind.TableEntry
                and e.value
                and e.value.kind == AstKind.VarargExpression) then
            return false
        end
    end
    -- Statement 3: return n
    local s3 = stats[3]
    if s3.kind ~= AstKind.ReturnStatement then return false end
    if #s3.args ~= 1 then return false end
    return true
end

-- CREATE_CLOSURE: closure factory where the inner closure is non-vararg.
function CLASSIFIERS.CREATE_CLOSURE(expr)
    return matchClosureFactory(expr, false)
end

-- CREATE_VARARG_CLOSURE: same shell, vararg inner closure.
function CLASSIFIERS.CREATE_VARARG_CLOSURE(expr)
    return matchClosureFactory(expr, true)
end

-- PROXY_FN: function(s)
--              if N then ... else return SETMT({}, {__gc = ..., __index = s, __len = ...}) end
--           end
-- Recognized loosely by: 1 arg, body contains an `if-then-else` where one branch
-- returns a SETMT call with two args, the second being a __gc/__index/__len
-- table, or where the function calls NEWPROXY first.
function CLASSIFIERS.PROXY_FN(expr, outer)
    if not isFunctionLiteral(expr) then return false end
    if not expr.args or #expr.args ~= 1 then return false end
    -- Walk the body looking for a setmetatable call with a metatable
    -- containing __gc/__index keys (any subset of these counts).
    local found = false
    astu.walkExpressions(expr.body, function(node)
        if found then return end
        if isCall(node)
                and refsGlobal(node.base, "SETMT", outer)
                and node.args and #node.args == 2 then
            local mt = node.args[2]
            if mt and mt.kind == AstKind.TableConstructorExpression then
                for _, e in ipairs(mt.entries) do
                    if e.kind == AstKind.KeyedTableEntry
                            and e.key and e.key.kind == AstKind.StringExpression
                            and (e.key.value == "__gc"
                                or e.key.value == "__index"
                                or e.key.value == "__len") then
                        found = true
                        return
                    end
                end
            end
        end
    end)
    return found
end

-- GC_FN: function(s) local f, g = 1, s[1]; while g do ref[g], f = ref[g] - 1, f + 1; ... end end
function CLASSIFIERS.GC_FN(expr)
    if not isFunctionLiteral(expr) then return false end
    if not expr.args or #expr.args ~= 1 then return false end
    local stats = statementsOf(expr.body)
    if #stats < 2 then return false end

    -- Need a `local _, _ = 1, s[1]` introduction.
    local s1 = stats[1]
    if s1.kind ~= AstKind.LocalVariableDeclaration then return false end
    if not s1.expressions or #s1.expressions ~= 2 then return false end
    if not (isNumber(s1.expressions[1]) and s1.expressions[1].value == 1) then
        return false
    end
    if s1.expressions[2].kind ~= AstKind.IndexExpression then return false end

    -- Followed by a while loop.
    for _, s in ipairs(stats) do
        if s.kind == AstKind.WhileStatement then
            return true
        end
    end
    return false
end

-- Try every classifier on `expr`; return a list of every kind that matched.
local function classifyHelper(expr, outer)
    local matches = {}
    for kind, predicate in pairs(CLASSIFIERS) do
        if predicate(expr, outer) then
            table.insert(matches, kind)
        end
    end
    return matches
end

-- ----------------------------------------------------------------------------
-- Resolve helpers from the multi-assign.
--
-- Strategy:
--   1. Classify every RHS into a *set* of candidate kinds.
--   2. Solve a small assignment problem so that the unique helpers
--      (CONTAINER, ALLOC_UPVAL, FREE_UPVAL, CREATE_CLOSURE,
--      CREATE_VARARG_CLOSURE, PROXY_FN, GC_FN, CURRENT_UPVAL_ID) get
--      assigned to exactly one slot, and EMPTY_TABLE matches the two
--      remaining table slots (UPVALS_TABLE and REF_COUNTS).
--   3. Disambiguate UPVALS_TABLE / REF_COUNTS by usage in the wrap body's
--      return expression and the helpers themselves.

-- Helpers that occur exactly once in the wrap.
local UNIQUE_KINDS = {
    "CONTAINER",
    "ALLOC_UPVAL",
    "FREE_UPVAL",
    "CREATE_VARARG_CLOSURE",
    "PROXY_FN",
    "GC_FN",
    "CURRENT_UPVAL_ID",
}
-- Helpers that may occur multiple times: Prometheus emits one createClosureVar
-- per inner function arity it ever needs (compile_top.lua: getCreateClosureVar).
local MULTI_KINDS = {
    "CREATE_CLOSURE",
}

local function buildHelperMap(assign, outer)
    local n = #assign.lhs
    local candidates = {}
    for i = 1, n do
        candidates[i] = classifyHelper(assign.rhs[i], outer)
    end

    local resolved = {}      -- kind -> { lhs = lhsVar, rhs = rhsExpr, slot = i }
    local takenSlot = {}     -- slot -> true

    -- Greedy unique assignment: kinds with exactly one candidate slot first.
    local function tryAssign(kind)
        local hits = {}
        for slot, kinds in ipairs(candidates) do
            if not takenSlot[slot] then
                for _, k in ipairs(kinds) do
                    if k == kind then
                        table.insert(hits, slot)
                        break
                    end
                end
            end
        end
        if #hits == 1 then
            local slot = hits[1]
            resolved[kind] = {
                lhs  = assign.lhs[slot],
                rhs  = assign.rhs[slot],
                slot = slot,
            }
            takenSlot[slot] = true
            return true
        end
        return false, hits
    end

    -- Iterate until fixed point: every iteration may free up another kind.
    local progress = true
    while progress do
        progress = false
        for _, kind in ipairs(UNIQUE_KINDS) do
            if not resolved[kind] then
                if tryAssign(kind) then progress = true end
            end
        end
    end
    for _, kind in ipairs(UNIQUE_KINDS) do
        if not resolved[kind] then
            local _, hits = tryAssign(kind)
            return nil, ("could not uniquely identify helper %s (matched slots: %s)"):format(
                kind, table.concat(hits or {}, ","))
        end
    end

    -- MULTI_KINDS (CREATE_CLOSURE): collect every remaining slot that matches.
    -- After UNIQUE_KINDS are taken, all remaining slots that classify as
    -- CREATE_CLOSURE are bona-fide createClosureVars (one per used inner
    -- function arity).
    local createClosures = {}
    for slot, kinds in ipairs(candidates) do
        if not takenSlot[slot] then
            for _, k in ipairs(kinds) do
                if k == "CREATE_CLOSURE" then
                    table.insert(createClosures, {
                        lhs  = assign.lhs[slot],
                        rhs  = assign.rhs[slot],
                        slot = slot,
                    })
                    takenSlot[slot] = true
                    break
                end
            end
        end
    end
    if #createClosures == 0 then
        -- Some scripts have no nested user functions, in which case there
        -- might be zero CREATE_CLOSURE helpers. That's allowed.
    end
    -- Convenient single-helper alias for scripts with exactly one closure factory.
    if createClosures[1] then
        resolved.CREATE_CLOSURE = createClosures[1]
    end
    resolved.CREATE_CLOSURES = createClosures

    -- Two remaining slots should be EMPTY_TABLE -- one is UPVALS_TABLE, the
    -- other is REF_COUNTS. We disambiguate by checking which of them is
    -- referenced via numeric-index reads/writes in ALLOC_UPVAL / FREE_UPVAL
    -- (those touch REF_COUNTS).
    local emptySlots = {}
    for slot, kinds in ipairs(candidates) do
        if not takenSlot[slot] then
            local hasEmpty = false
            for _, k in ipairs(kinds) do
                if k == "EMPTY_TABLE" then hasEmpty = true break end
            end
            if hasEmpty then table.insert(emptySlots, slot) end
        end
    end
    if #emptySlots ~= 2 then
        return nil, ("expected exactly 2 empty-table helpers; found %d"):format(#emptySlots)
    end

    local function pickByUsage(funcExpr)
        -- Inspect the FunctionLiteralExpression's body and find which of the
        -- two empty-table LHS variables it indexes with [param].
        local found
        astu.walkExpressions(funcExpr.body, function(node)
            if found then return end
            if node.kind == AstKind.IndexExpression and isVar(node.base) then
                for _, slot in ipairs(emptySlots) do
                    local lhs = assign.lhs[slot]
                    if node.base.scope == lhs.scope and node.base.id == lhs.id then
                        found = slot
                        return
                    end
                end
            elseif node.kind == AstKind.AssignmentIndexing and isVar(node.base) then
                for _, slot in ipairs(emptySlots) do
                    local lhs = assign.lhs[slot]
                    if node.base.scope == lhs.scope and node.base.id == lhs.id then
                        found = slot
                        return
                    end
                end
            end
        end)
        return found
    end

    local refCountSlot = pickByUsage(resolved.ALLOC_UPVAL.rhs)
        or pickByUsage(resolved.FREE_UPVAL.rhs)
    if not refCountSlot then
        return nil, "could not disambiguate UPVALS_TABLE vs REF_COUNTS"
    end
    resolved.REF_COUNTS = {
        lhs  = assign.lhs[refCountSlot],
        rhs  = assign.rhs[refCountSlot],
        slot = refCountSlot,
    }
    takenSlot[refCountSlot] = true
    for _, slot in ipairs(emptySlots) do
        if slot ~= refCountSlot then
            resolved.UPVALS_TABLE = {
                lhs  = assign.lhs[slot],
                rhs  = assign.rhs[slot],
                slot = slot,
            }
            takenSlot[slot] = true
        end
    end

    return resolved
end

-- ----------------------------------------------------------------------------
-- Final return statement: return CREATE_VARARG_CLOSURE(ENTRY_ID, {})(UNPACK(VARARG))

local function findEntryReturn(wrapperBody, helpers, outer)
    local stats = statementsOf(wrapperBody)
    local ret = stats[#stats]
    if not ret or ret.kind ~= AstKind.ReturnStatement then
        return nil, "wrapper does not end in a return"
    end
    if #ret.args ~= 1 then
        return nil, ("wrapper return takes %d value(s); expected 1"):format(#ret.args)
    end
    local outerCall = ret.args[1]
    if not isCall(outerCall) then
        return nil, "wrapper return is not a function call"
    end
    -- outerCall = innerClosure(UNPACK(VARARG))
    -- innerClosure = CREATE_VARARG_CLOSURE(ENTRY_ID, {})
    local innerCall = outerCall.base
    if not isCall(innerCall) then
        return nil, "wrapper return base is not a function call"
    end
    if not isVar(innerCall.base) then
        return nil, "wrapper return base.base is not a variable reference"
    end
    -- Validate the innerCall is calling CREATE_VARARG_CLOSURE.
    local cv = helpers.CREATE_VARARG_CLOSURE
    if not cv then return nil, "no CREATE_VARARG_CLOSURE helper resolved" end
    if not (innerCall.base.scope == cv.lhs.scope
            and innerCall.base.id == cv.lhs.id) then
        return nil, "wrapper return is not calling CREATE_VARARG_CLOSURE"
    end
    if #innerCall.args ~= 2 then
        return nil, ("CREATE_VARARG_CLOSURE got %d arg(s); expected 2"):format(#innerCall.args)
    end
    local entryArg = innerCall.args[1]
    if not isNumber(entryArg) then
        return nil, "CREATE_VARARG_CLOSURE entry id is not a NumberExpression"
    end
    return {
        returnStat = ret,
        entryId    = entryArg.value,
        entryArgNode = entryArg,
        upvalArg   = innerCall.args[2],
        outerCall  = outerCall,
        innerCall  = innerCall,
    }
end

-- ----------------------------------------------------------------------------
-- Container return register: the container function ends with
--     return UNPACK(R)
-- where UNPACK is the outer `unpack` parameter and R is a local register.
-- That register is the per-VM RETURN_REGISTER -- every block that issues a
-- function-style return writes its return tuple table into it before
-- exiting the dispatcher.

local function findContainerReturnReg(containerFunc, outer)
    local stats = statementsOf(containerFunc.body)
    local ret = stats[#stats]
    if not ret or ret.kind ~= AstKind.ReturnStatement then
        return nil, "container does not end in a return statement"
    end
    if #ret.args ~= 1 then
        return nil, ("container return takes %d value(s); expected 1"):format(#ret.args)
    end
    local call = ret.args[1]
    if not isCall(call) then
        return nil, "container return value is not a function call"
    end
    if not isVar(call.base) then
        return nil, "container return call.base is not a variable"
    end
    -- The base must reference the outer UNPACK parameter.
    local unpackParam = outer.UNPACK
    if not unpackParam or not (call.base.scope == unpackParam.scope
            and call.base.id == unpackParam.id) then
        return nil, "container return is not calling UNPACK"
    end
    if #call.args ~= 1 then
        return nil, ("UNPACK call has %d arg(s); expected 1"):format(#call.args)
    end
    local regNode = call.args[1]
    if not isVar(regNode) then
        return nil, "UNPACK arg is not a variable reference"
    end
    return {
        returnStat = ret,
        unpackCall = call,
        regNode    = regNode,
    }
end

-- ----------------------------------------------------------------------------
-- Public entry point.

function M.recognize(ast)
    local wrap, err = findOuterWrap(ast)
    if not wrap then return nil, err end

    local outer
    outer, err = classifyOuterArgs(wrap.wrapperArgs, wrap.wrapperParams)
    if not outer then return nil, err end

    local assign
    assign, err = findHelpersAssignment(wrap.wrapperBody, outer)
    if not assign then return nil, err end

    local helpers
    helpers, err = buildHelperMap(assign, outer)
    if not helpers then return nil, err end

    local entry
    entry, err = findEntryReturn(wrap.wrapperBody, helpers, outer)
    if not entry then return nil, err end

    local containerFunc = helpers.CONTAINER.rhs
    local returnReg
    returnReg, err = findContainerReturnReg(containerFunc, outer)
    if not returnReg then return nil, err end

    return {
        ast              = ast,
        wrap             = wrap,
        outer            = outer,
        helpersAssign    = assign,
        helpers          = helpers,
        entry            = entry,
        returnReg        = returnReg,
        -- Convenience: container function literal.
        containerFunc    = containerFunc,
        containerLhs     = helpers.CONTAINER.lhs,
    }
end

-- Pretty-print a recognized VM for debugging.
function M.report(vm, write)
    write = write or function(s) io.write(s); io.write("\n") end
    write("Vmify VM detected:")
    write(("  entry block id: %d"):format(vm.entry.entryId))
    do
        local r = vm.returnReg.regNode
        local n = r.scope:getVariableName(r.id) or "?"
        write(("  return register: %s (scope-local id %d)"):format(n, r.id))
    end
    write("  outer wrap params:")
    for _, name in ipairs(OUTER_ARG_NAMES) do
        local e = vm.outer[name]
        write(("    %-9s = %s"):format(name, e.scope:getVariableName(e.id)))
    end
    write("  helpers:")
    local helperNames = {
        "CONTAINER", "ALLOC_UPVAL", "FREE_UPVAL", "PROXY_FN", "GC_FN",
        "CREATE_VARARG_CLOSURE",
        "UPVALS_TABLE", "REF_COUNTS", "CURRENT_UPVAL_ID",
    }
    for _, kind in ipairs(helperNames) do
        local h = vm.helpers[kind]
        if h then
            local lhsName = h.lhs.scope:getVariableName(h.lhs.id)
            write(("    %-22s = slot %2d  %s"):format(kind, h.slot, lhsName))
        else
            write(("    %-22s = (missing)"):format(kind))
        end
    end
    if vm.helpers.CREATE_CLOSURES and #vm.helpers.CREATE_CLOSURES > 0 then
        write(("    CREATE_CLOSURES (%d total):"):format(#vm.helpers.CREATE_CLOSURES))
        for i, h in ipairs(vm.helpers.CREATE_CLOSURES) do
            local lhsName = h.lhs.scope:getVariableName(h.lhs.id)
            write(("      [%d] slot %2d  %s"):format(i, h.slot, lhsName))
        end
    else
        write("    CREATE_CLOSURES (none)")
    end
end

return M
