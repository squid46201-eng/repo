-- prometheus-test-deobfuscator - generic copy-propagation and dead-store
-- elimination for devirtualized output.
--
-- The devirtualizer emits highly-tokenized, low-level register code where
-- almost every value passes through one or two scratch registers before
-- being used:
--
--     r37 = "Text";
--     r1[r37] = "...";
--
--     r19 = r23.GetService;
--     r19 = r19(r23, "Players");
--
--     r1 = math.random;
--     loc_7 = r1;
--     r1 = table.concat;
--
-- This pass performs per-function forward propagation of "propagatable"
-- right-hand sides and a cross-block dead-store elimination over the
-- post-substitution form.  Together they collapse the patterns above into:
--
--     r1["Text"] = "...";
--     r19 = r23.GetService(r23, "Players");
--     loc_7 = math.random;
--
-- Propagation rules:
--   * "Propagatable" RHS: constants (nil/bool/number/string), variable
--     references, index expressions, binary/unary expressions.  Function
--     calls, table constructors, function literals and vararg are NOT
--     propagated -- they have side effects (calls) or fresh identity
--     (tables) or are too expensive to duplicate (functions).
--   * Substitution is EAGER: when we record `valueOf[v] = rhs`, we first
--     substitute reads inside `rhs` using the current map.  This saturates
--     the recorded form, so subsequent invalidations of source variables
--     don't corrupt the propagated value.
--   * Substitution does NOT cross FunctionLiteralExpression boundaries:
--     captured upvalues see live values at call time, not at the time the
--     closure was created.
--   * Entering a nested control-flow block (if/while/for/repeat/do) drops
--     all entries that the nested block could write, and entries that the
--     nested block reads must be invalidated AFTER the block -- the
--     substitution map is therefore conservatively cleared on return from
--     a nested block.
--
-- Dead-store elimination uses next-use analysis identical in shape to the
-- one in decrypt_vm_strings.lua: walk the function-scope in source order
-- and remove the assignment if the LHS is not read before the next write
-- (or never read again).  Side-effecting RHS (function calls) are never
-- removed; only assignments with propagatable RHS are eligible.

local Ast = require("prometheus.ast")
local AstKind = Ast.AstKind

local M = {}

-- ---------------------------------------------------------------------------
-- Helpers.

local function vkey(node)
    if not node or not node.kind then return nil end
    if (node.kind == AstKind.VariableExpression
            or node.kind == AstKind.AssignmentVariable)
            and node.scope and node.id then
        return tostring(node.scope) .. "/" .. tostring(node.id)
    end
    return nil
end

local function isConstant(node)
    if not node then return false end
    local k = node.kind
    return k == AstKind.NilExpression
        or k == AstKind.BooleanExpression
        or k == AstKind.NumberExpression
        or k == AstKind.StringExpression
end

local BINARY_KINDS = {
    [AstKind.OrExpression] = true,
    [AstKind.AndExpression] = true,
    [AstKind.LessThanExpression] = true,
    [AstKind.GreaterThanExpression] = true,
    [AstKind.LessThanOrEqualsExpression] = true,
    [AstKind.GreaterThanOrEqualsExpression] = true,
    [AstKind.NotEqualsExpression] = true,
    [AstKind.EqualsExpression] = true,
    [AstKind.StrCatExpression] = true,
    [AstKind.AddExpression] = true,
    [AstKind.SubExpression] = true,
    [AstKind.MulExpression] = true,
    [AstKind.DivExpression] = true,
    [AstKind.ModExpression] = true,
    [AstKind.PowExpression] = true,
}

-- A node is "shape-propagatable" if its top-level kind is one we're willing
-- to duplicate.  This still needs to be combined with isPureSubtree() to
-- ensure the whole subtree is free of side-effecting subexpressions.
local function isShapePropagatable(node)
    if not node then return false end
    local k = node.kind
    if isConstant(node) then return true end
    if k == AstKind.VariableExpression then return true end
    if k == AstKind.IndexExpression then return true end
    if BINARY_KINDS[k] then return true end
    if k == AstKind.NotExpression or k == AstKind.LenExpression
            or k == AstKind.NegateExpression then return true end
    return false
end

-- True iff the expression tree contains no function call, table
-- constructor, function literal or vararg -- i.e., evaluating it is
-- side-effect-free and order-independent.  Duplicating or moving such an
-- expression preserves semantics regardless of context.  Stops at
-- VariableExpression (a leaf) and never descends into function literal
-- bodies (we treat those as opaque -- they'd never be propagated).
local function isPureSubtree(node)
    if type(node) ~= "table" then return true end
    if not node.kind then
        for _, v in ipairs(node) do
            if not isPureSubtree(v) then return false end
        end
        return true
    end
    local k = node.kind
    if k == AstKind.FunctionCallExpression
            or k == AstKind.PassSelfFunctionCallExpression
            or k == AstKind.TableConstructorExpression
            or k == AstKind.FunctionLiteralExpression
            or k == AstKind.VarargExpression then
        return false
    end
    -- Leaf-ish kinds: nothing to recurse into.
    if isConstant(node) or k == AstKind.VariableExpression
            or k == AstKind.AssignmentVariable then
        return true
    end
    -- Recurse over known structural fields.
    if k == AstKind.IndexExpression then
        return isPureSubtree(node.base) and isPureSubtree(node.index)
    elseif BINARY_KINDS[k] then
        return isPureSubtree(node.lhs) and isPureSubtree(node.rhs)
    elseif k == AstKind.NotExpression or k == AstKind.LenExpression
            or k == AstKind.NegateExpression then
        return isPureSubtree(node.rhs)
    elseif k == AstKind.IfElseExpression then
        return isPureSubtree(node.condition)
            and isPureSubtree(node.true_value)
            and isPureSubtree(node.false_value)
    end
    -- Unknown / unhandled kind: be conservative.
    return false
end

local function isPropagatable(node)
    return isShapePropagatable(node) and isPureSubtree(node)
end

-- A side-effecting RHS that we must NOT remove even if dead.  These also
-- can't be propagated, but they have an extra implication: if they appear
-- on an assignment we may still drop the LHS dead-store ONLY if we can
-- prove the LHS itself has no effect (we never can here, so we keep them).
local function isSideEffecting(node)
    if not node then return false end
    local k = node.kind
    if k == AstKind.FunctionCallExpression then return true end
    if k == AstKind.PassSelfFunctionCallExpression then return true end
    return false
end

-- Recursive AST deep-clone.  Variable / assignment-variable expressions
-- are re-created via the Prometheus factories so the scope's reference
-- counter stays consistent.  Function literals are NOT cloned (we never
-- propagate them); callers should not feed them into this function.
local clone
clone = function(node)
    if type(node) ~= "table" then return node end
    if not node.kind then
        local arr = {}
        for i, v in ipairs(node) do
            arr[i] = clone(v)
        end
        return arr
    end
    if node.kind == AstKind.VariableExpression then
        return Ast.VariableExpression(node.scope, node.id)
    end
    if node.kind == AstKind.AssignmentVariable then
        return Ast.AssignmentVariable(node.scope, node.id)
    end
    if node.kind == AstKind.FunctionLiteralExpression then
        -- Should never reach here for propagation; leave node as-is.
        return node
    end
    local copy = {}
    for k, v in pairs(node) do
        if type(v) == "table" then
            copy[k] = clone(v)
        else
            copy[k] = v
        end
    end
    return copy
end

-- Walk an expression subtree and collect all `varKey`s read.  Stops at
-- FunctionLiteralExpression boundaries (captured upvalues are not
-- block-local reads for our purposes).  Iterative to handle deep trees.
local function collectReads(node, reads)
    if type(node) ~= "table" then return end
    local stack = { node }
    local top = 1
    local seen = {}
    while top > 0 do
        local n = stack[top]
        stack[top] = nil
        top = top - 1
        if type(n) == "table" and not seen[n] then
            seen[n] = true
            if n.kind ~= AstKind.FunctionLiteralExpression then
                if n.kind == AstKind.VariableExpression then
                    local k = vkey(n)
                    if k then reads[k] = true end
                else
                    for k, v in pairs(n) do
                        if k ~= "kind" and k ~= "scope" and k ~= "parentScope"
                                and k ~= "baseScope" and k ~= "globalScope" then
                            if type(v) == "table" then
                                if v.kind then
                                    top = top + 1
                                    stack[top] = v
                                else
                                    for _, vv in ipairs(v) do
                                        if type(vv) == "table" and vv.kind then
                                            top = top + 1
                                            stack[top] = vv
                                        end
                                    end
                                end
                            end
                        end
                    end
                end
            end
        end
    end
end

-- ---------------------------------------------------------------------------
-- Substitution: given a `slot` table and field name pointing at an
-- expression value, recursively substitute reads matching valueMap entries.
-- Mutates `slot[field]` in place.

local substExpr  -- forward decl

local function substInPlace(parent, field, valueMap)
    if not parent then return end
    local v = parent[field]
    if type(v) ~= "table" then return end
    if v.kind then
        if v.kind == AstKind.VariableExpression then
            local k = vkey(v)
            if k and valueMap[k] then
                parent[field] = clone(valueMap[k])
                return
            end
        end
        if v.kind == AstKind.FunctionLiteralExpression then
            return  -- don't descend into function literals
        end
        substExpr(v, valueMap)
    elseif #v > 0 then
        for i = 1, #v do
            local item = v[i]
            if type(item) == "table" and item.kind then
                if item.kind == AstKind.VariableExpression then
                    local k = vkey(item)
                    if k and valueMap[k] then
                        v[i] = clone(valueMap[k])
                    else
                        substExpr(item, valueMap)
                    end
                elseif item.kind ~= AstKind.FunctionLiteralExpression then
                    substExpr(item, valueMap)
                end
            end
        end
    end
end

substExpr = function(node, valueMap)
    if type(node) ~= "table" or not node.kind then return end
    local k = node.kind
    if k == AstKind.IndexExpression
            or k == AstKind.AssignmentIndexing then
        substInPlace(node, "base", valueMap)
        substInPlace(node, "index", valueMap)
    elseif k == AstKind.FunctionCallExpression
            or k == AstKind.PassSelfFunctionCallExpression then
        substInPlace(node, "base", valueMap)
        substInPlace(node, "args", valueMap)
    elseif k == AstKind.TableConstructorExpression then
        substInPlace(node, "entries", valueMap)
    elseif k == AstKind.TableEntry then
        substInPlace(node, "value", valueMap)
    elseif k == AstKind.KeyedTableEntry then
        substInPlace(node, "key", valueMap)
        substInPlace(node, "value", valueMap)
    elseif BINARY_KINDS[k] then
        substInPlace(node, "lhs", valueMap)
        substInPlace(node, "rhs", valueMap)
    elseif k == AstKind.NotExpression or k == AstKind.LenExpression
            or k == AstKind.NegateExpression then
        substInPlace(node, "rhs", valueMap)
    elseif k == AstKind.IfElseExpression then
        substInPlace(node, "condition", valueMap)
        substInPlace(node, "true_value", valueMap)
        substInPlace(node, "false_value", valueMap)
    end
    -- VariableExpression handled by the parent's substInPlace at slot level.
    -- FunctionLiteralExpression is intentionally not descended into.
end

-- Convenience: substitute all reads in a single statement's expression
-- slots (per kind).  Does NOT recurse into nested blocks or function
-- literals; those are processed separately.
local function substituteStmtReads(stmt, valueMap)
    local k = stmt.kind
    if k == AstKind.AssignmentStatement then
        if stmt.rhs then
            for i = 1, #stmt.rhs do substInPlace(stmt.rhs, i, valueMap) end
        end
        if stmt.lhs then
            for i = 1, #stmt.lhs do
                local lhs = stmt.lhs[i]
                if lhs and lhs.kind == AstKind.AssignmentIndexing then
                    substInPlace(lhs, "base", valueMap)
                    substInPlace(lhs, "index", valueMap)
                end
            end
        end
    elseif k == AstKind.LocalVariableDeclaration then
        if stmt.expressions then
            for i = 1, #stmt.expressions do
                substInPlace(stmt.expressions, i, valueMap)
            end
        end
    elseif k == AstKind.FunctionCallStatement
            or k == AstKind.PassSelfFunctionCallStatement then
        substInPlace(stmt, "base", valueMap)
        if stmt.args then
            for i = 1, #stmt.args do substInPlace(stmt.args, i, valueMap) end
        end
    elseif k == AstKind.ReturnStatement then
        if stmt.args then
            for i = 1, #stmt.args do substInPlace(stmt.args, i, valueMap) end
        end
    elseif k == AstKind.IfStatement then
        -- Condition + elseif conditions are evaluated once on the way in.
        substInPlace(stmt, "condition", valueMap)
        if stmt.elseifs then
            for i = 1, #stmt.elseifs do
                substInPlace(stmt.elseifs[i], "condition", valueMap)
            end
        end
    elseif k == AstKind.WhileStatement or k == AstKind.RepeatStatement then
        -- Condition is re-evaluated each iteration; the body may write to
        -- variables the condition reads.  Substituting once with the
        -- pre-loop value would freeze the condition at its initial form
        -- (e.g. `while r17 ~= 5 do r17 = r17 + 1 end` becoming
        -- `while 1 ~= 5 do ...`).  Skip.
    elseif k == AstKind.ForStatement then
        -- Numeric-for bounds are evaluated exactly once before the loop.
        substInPlace(stmt, "initialValue", valueMap)
        substInPlace(stmt, "finalValue", valueMap)
        substInPlace(stmt, "incrementBy", valueMap)
    elseif k == AstKind.ForInStatement then
        -- For-in expressions form an iterator triple evaluated once at
        -- entry (the iterator function itself is then re-called).  The
        -- triple's *expressions* are safe to substitute, BUT only if the
        -- body doesn't mutate variables they read.  Be safe and skip.
    end
end

-- Compute the set of variable keys that a (possibly nested) block might
-- WRITE during execution.  Walks all sub-statements but does NOT enter
-- FunctionLiteralExpression bodies.
local function collectWrites(block, writes)
    if not block or block.kind ~= AstKind.Block or not block.statements then
        return
    end
    for _, s in ipairs(block.statements) do
        if s.kind == AstKind.AssignmentStatement and s.lhs then
            for _, lhs in ipairs(s.lhs) do
                local k = vkey(lhs)
                if k then writes[k] = true end
            end
        elseif s.kind == AstKind.LocalVariableDeclaration then
            -- Local declarations introduce new scope ids; can't collide
            -- with outer-scope keys so skipped.
        elseif s.kind == AstKind.ForStatement then
            -- Loop variable is a fresh local scope ID; not an outer write.
        elseif s.kind == AstKind.ForInStatement then
            -- Loop variables are fresh local scope IDs.
        end
        -- Recurse into nested blocks (NOT function literals).
        local k = s.kind
        if k == AstKind.IfStatement then
            collectWrites(s.body, writes)
            if s.elseifs then
                for _, ei in ipairs(s.elseifs) do
                    collectWrites(ei.body, writes)
                end
            end
            if s.elsebody then collectWrites(s.elsebody, writes) end
        elseif k == AstKind.WhileStatement or k == AstKind.RepeatStatement
                or k == AstKind.DoStatement or k == AstKind.ForStatement
                or k == AstKind.ForInStatement then
            collectWrites(s.body, writes)
        end
    end
end

-- ---------------------------------------------------------------------------
-- Cross-function-scope next-use analysis (mirrors the version in
-- decrypt_vm_strings.lua, but applies to ANY propagatable assignment).

local checkStmt

-- NB: this *descends into* function literal bodies.  Any read of `varKey`
-- inside a closure that is created during/after the scan window should be
-- treated as a possible future use, because the closure may be invoked
-- later (and captures the binding by reference, so subsequent writes to
-- the same name would be observed by the closure too).  Conservatively
-- treating every closure-internal read as a use keeps DCE sound for
-- variables captured as upvalues.
local function findReadInRoot(node, varKey)
    if type(node) ~= "table" then return false end
    local stack = { node }
    local top = 1
    local seen = {}
    while top > 0 do
        local n = stack[top]
        stack[top] = nil
        top = top - 1
        if type(n) == "table" and not seen[n] then
            seen[n] = true
            if n.kind == AstKind.VariableExpression then
                if vkey(n) == varKey then return true end
            else
                for k, v in pairs(n) do
                    if k ~= "kind" and k ~= "scope" and k ~= "parentScope"
                            and k ~= "baseScope" and k ~= "globalScope" then
                        if type(v) == "table" then
                            if v.kind then
                                top = top + 1
                                stack[top] = v
                            else
                                for _, vv in ipairs(v) do
                                    if type(vv) == "table" and vv.kind then
                                        top = top + 1
                                        stack[top] = vv
                                    end
                                end
                            end
                        end
                    end
                end
            end
        end
    end
    return false
end

local function nextUseInBlock(block, startIdx, varKey)
    if not block or not block.statements then return "neutral" end
    for i = startIdx, #block.statements do
        local s = block.statements[i]
        local r = checkStmt(s, varKey)
        if r == "read" then return "read" end
        if r == "write" then return "write" end
    end
    return "neutral"
end

-- Like nextUseInBlock but scans only block.statements[startIdx..endIdx].
local function rangeUseInBlock(block, startIdx, endIdx, varKey)
    if not block or not block.statements then return "neutral" end
    for i = startIdx, math.min(endIdx, #block.statements) do
        local s = block.statements[i]
        local r = checkStmt(s, varKey)
        if r == "read" then return "read" end
        if r == "write" then return "write" end
    end
    return "neutral"
end

checkStmt = function(stmt, varKey)
    local k = stmt.kind
    if k == AstKind.AssignmentStatement then
        if stmt.rhs then
            for _, e in ipairs(stmt.rhs) do
                if findReadInRoot(e, varKey) then return "read" end
            end
        end
        if stmt.lhs then
            for _, lhs in ipairs(stmt.lhs) do
                if lhs.kind == AstKind.AssignmentIndexing then
                    if findReadInRoot(lhs.base, varKey) then return "read" end
                    if findReadInRoot(lhs.index, varKey) then return "read" end
                end
            end
            for _, lhs in ipairs(stmt.lhs) do
                if lhs.kind == AstKind.AssignmentVariable
                        and vkey(lhs) == varKey then
                    return "write"
                end
            end
        end
        return "neutral"
    elseif k == AstKind.LocalVariableDeclaration then
        if stmt.expressions then
            for _, e in ipairs(stmt.expressions) do
                if findReadInRoot(e, varKey) then return "read" end
            end
        end
        return "neutral"
    elseif k == AstKind.FunctionCallStatement
            or k == AstKind.PassSelfFunctionCallStatement then
        if findReadInRoot(stmt.base, varKey) then return "read" end
        if stmt.args then
            for _, a in ipairs(stmt.args) do
                if findReadInRoot(a, varKey) then return "read" end
            end
        end
        return "neutral"
    elseif k == AstKind.ReturnStatement then
        if stmt.args then
            for _, a in ipairs(stmt.args) do
                if findReadInRoot(a, varKey) then return "read" end
            end
        end
        return "neutral"
    elseif k == AstKind.IfStatement then
        if findReadInRoot(stmt.condition, varKey) then return "read" end
        local anyLive = false
        local allDead = stmt.elsebody ~= nil
        local function visit(b)
            local r = nextUseInBlock(b, 1, varKey)
            if r == "read" then anyLive = true end
            if r ~= "write" then allDead = false end
        end
        visit(stmt.body)
        if stmt.elseifs then
            for _, ei in ipairs(stmt.elseifs) do
                if findReadInRoot(ei.condition, varKey) then return "read" end
                visit(ei.body)
            end
        end
        if stmt.elsebody then visit(stmt.elsebody) end
        if anyLive then return "read" end
        if allDead then return "write" end
        return "neutral"
    elseif k == AstKind.WhileStatement or k == AstKind.RepeatStatement then
        if findReadInRoot(stmt.condition, varKey) then return "read" end
        local r = nextUseInBlock(stmt.body, 1, varKey)
        if r == "read" then return "read" end
        return "neutral"
    elseif k == AstKind.ForStatement then
        if findReadInRoot(stmt.initialValue, varKey) then return "read" end
        if findReadInRoot(stmt.finalValue, varKey) then return "read" end
        if findReadInRoot(stmt.incrementBy, varKey) then return "read" end
        local r = nextUseInBlock(stmt.body, 1, varKey)
        if r == "read" then return "read" end
        return "neutral"
    elseif k == AstKind.ForInStatement then
        if stmt.expressions then
            for _, e in ipairs(stmt.expressions) do
                if findReadInRoot(e, varKey) then return "read" end
            end
        end
        local r = nextUseInBlock(stmt.body, 1, varKey)
        if r == "read" then return "read" end
        return "neutral"
    elseif k == AstKind.DoStatement then
        return nextUseInBlock(stmt.body, 1, varKey)
    elseif k == AstKind.FunctionDeclaration
            or k == AstKind.LocalFunctionDeclaration then
        -- Function body may reference upvalues at call time; treat as
        -- potentially live for safety.
        if findReadInRoot(stmt.body, varKey) then return "read" end
        return "neutral"
    end
    return "neutral"
end

-- ---------------------------------------------------------------------------
-- Driver.

local processFunction

-- Per-block forward propagation.  Updates the AST in place, then returns
-- the number of dead stores removed in this function.
local function processBlock(block, valueMap, depToOwners, ownerDeps, removedCounter)
    if not block or block.kind ~= AstKind.Block or not block.statements then
        return
    end

    -- Invalidate one valueMap entry and clean up the dep <-> owner indices.
    local function invalidate(vk)
        local deps = ownerDeps[vk]
        if deps then
            for d in pairs(deps) do
                local owners = depToOwners[d]
                if owners then
                    owners[vk] = nil
                    if not next(owners) then depToOwners[d] = nil end
                end
            end
            ownerDeps[vk] = nil
        end
        valueMap[vk] = nil
    end

    -- Invalidate every entry whose recorded value contains a read of `writeVar`.
    local function invalidateUsersOf(writeVar)
        local owners = depToOwners[writeVar]
        if not owners then return end
        -- Snapshot: invalidate mutates the table.
        local snap = {}
        for o in pairs(owners) do snap[#snap + 1] = o end
        for _, o in ipairs(snap) do invalidate(o) end
    end

    -- Record a new valueMap entry along with its dependency set.  Constants
    -- have no deps and never need invalidation.
    local function record(vk, expr)
        valueMap[vk] = expr
        if isConstant(expr) then return end
        local deps = {}
        collectReads(expr, deps)
        if next(deps) == nil then return end
        ownerDeps[vk] = deps
        for d in pairs(deps) do
            local owners = depToOwners[d]
            if not owners then
                owners = {}
                depToOwners[d] = owners
            end
            owners[vk] = true
        end
    end

    local i = 1
    while i <= #block.statements do
        local stmt = block.statements[i]
        local k = stmt.kind

        -- 1) Substitute reads in this statement's expressions before we
        --    consider what it writes.
        substituteStmtReads(stmt, valueMap)

        -- 2) Recurse into nested function literals appearing in this stmt's
        --    expressions, each with a fresh valueMap.
        local function recurseLits(node)
            if type(node) ~= "table" or not node.kind then return end
            if node.kind == AstKind.FunctionLiteralExpression then
                processFunction(node.body, removedCounter)
                return
            end
            for kk, v in pairs(node) do
                if kk ~= "kind" and kk ~= "scope" and kk ~= "parentScope"
                        and kk ~= "baseScope" and kk ~= "globalScope" then
                    if type(v) == "table" then
                        if v.kind then
                            recurseLits(v)
                        else
                            for _, vv in ipairs(v) do
                                if type(vv) == "table" and vv.kind then
                                    recurseLits(vv)
                                end
                            end
                        end
                    end
                end
            end
        end
        if k == AstKind.AssignmentStatement then
            if stmt.rhs then for _, e in ipairs(stmt.rhs) do recurseLits(e) end end
        elseif k == AstKind.LocalVariableDeclaration then
            if stmt.expressions then for _, e in ipairs(stmt.expressions) do recurseLits(e) end end
        elseif k == AstKind.FunctionCallStatement
                or k == AstKind.PassSelfFunctionCallStatement then
            recurseLits(stmt.base)
            if stmt.args then for _, a in ipairs(stmt.args) do recurseLits(a) end end
        elseif k == AstKind.ReturnStatement then
            if stmt.args then for _, a in ipairs(stmt.args) do recurseLits(a) end end
        end

        -- 3) If this is a structured statement, drop entries that the
        --    nested block could write or read (conservative) and recurse
        --    into nested blocks with a FRESH valueMap.
        local hasNestedBlock =
            k == AstKind.IfStatement
            or k == AstKind.WhileStatement
            or k == AstKind.RepeatStatement
            or k == AstKind.DoStatement
            or k == AstKind.ForStatement
            or k == AstKind.ForInStatement
            or k == AstKind.FunctionDeclaration
            or k == AstKind.LocalFunctionDeclaration

        if hasNestedBlock then
            local nestedWrites = {}
            collectWrites(stmt.body, nestedWrites)
            if k == AstKind.IfStatement then
                if stmt.elseifs then
                    for _, ei in ipairs(stmt.elseifs) do
                        collectWrites(ei.body, nestedWrites)
                    end
                end
                if stmt.elsebody then
                    collectWrites(stmt.elsebody, nestedWrites)
                end
            end
            -- Anything the nested block writes is no longer safe to
            -- propagate after the block.  Two invalidations:
            --   (a) drop direct entries valueMap[v] for v in nestedWrites
            --   (b) drop entries whose recorded value READS v in nestedWrites
            for vk in pairs(nestedWrites) do
                invalidate(vk)
                invalidateUsersOf(vk)
            end

            -- Recurse into nested bodies with fresh maps.
            if k == AstKind.IfStatement then
                processBlock(stmt.body, {}, {}, {}, removedCounter)
                if stmt.elseifs then
                    for _, ei in ipairs(stmt.elseifs) do
                        processBlock(ei.body, {}, {}, {}, removedCounter)
                    end
                end
                if stmt.elsebody then
                    processBlock(stmt.elsebody, {}, {}, {}, removedCounter)
                end
            elseif k == AstKind.WhileStatement
                    or k == AstKind.RepeatStatement
                    or k == AstKind.DoStatement
                    or k == AstKind.ForStatement
                    or k == AstKind.ForInStatement then
                processBlock(stmt.body, {}, {}, {}, removedCounter)
            elseif k == AstKind.FunctionDeclaration
                    or k == AstKind.LocalFunctionDeclaration then
                -- Function bodies get a totally fresh scope.
                processFunction(stmt.body, removedCounter)
            end
        end

        -- 4) Apply this statement's effects to valueMap.
        if k == AstKind.AssignmentStatement
                and stmt.lhs and #stmt.lhs == 1
                and stmt.rhs and #stmt.rhs == 1
                and stmt.lhs[1].kind == AstKind.AssignmentVariable then
            local lk = vkey(stmt.lhs[1])
            local rhs = stmt.rhs[1]
            if lk then
                -- The LHS variable's value is changing.  Invalidate the
                -- prior entry for `lk` and every entry whose recorded
                -- value references `lk`.
                invalidate(lk)
                invalidateUsersOf(lk)
                if isPropagatable(rhs) then
                    -- Eager substitution has already saturated rhs.
                    -- Self-assignment (`r1 = r1` after substitution) is
                    -- useless to record.  Same for ANY self-reference
                    -- inside a compound expression -- recording
                    -- `loc_11 = (loc_11 * 131) % 257` would cause future
                    -- reads of loc_11 to splice in this expression, which
                    -- would read the post-assignment value and incorrectly
                    -- re-apply the LCG step.
                    local readsInRhs = {}
                    collectReads(rhs, readsInRhs)
                    if not readsInRhs[lk] then
                        record(lk, rhs)
                    end
                end
            end
        elseif k == AstKind.AssignmentStatement and stmt.lhs then
            -- Multi-target or indexed LHS: invalidate any plain LHS keys
            -- and anything that depended on them.
            for _, lhs in ipairs(stmt.lhs) do
                if lhs.kind == AstKind.AssignmentVariable then
                    local lk = vkey(lhs)
                    if lk then
                        invalidate(lk)
                        invalidateUsersOf(lk)
                    end
                end
            end
        elseif k == AstKind.LocalVariableDeclaration then
            -- New locals: their keys are fresh ids, no collision possible.
        elseif k == AstKind.FunctionCallStatement
                or k == AstKind.PassSelfFunctionCallStatement then
            -- Side-effecting call: pessimistically clear non-constant
            -- entries -- the call may have written to globals / table
            -- fields that propagated expressions depend on.
            local snap = {}
            for vk, expr in pairs(valueMap) do
                if not isConstant(expr) then snap[#snap + 1] = vk end
            end
            for _, vk in ipairs(snap) do invalidate(vk) end
        elseif k == AstKind.ReturnStatement then
            valueMap = nil
        end

        if valueMap == nil then valueMap = {} end

        i = i + 1
    end
end

-- Cross-function-scope dead-store pass: for every propagatable assignment
-- in `funcBody`, run next-use analysis and remove the assignment if dead.
-- Recurses into nested function literals.
local function eliminateDeadStores(funcBody, removedCounter)
    if not funcBody or funcBody.kind ~= AstKind.Block
            or not funcBody.statements then
        return
    end

    -- Reads in the loop's "header" (condition for while/repeat, iterator
    -- expressions for for-in).  Numeric-for bounds are evaluated exactly
    -- once and never re-read.
    local function loopHeaderReads(loopStmt, varKey)
        local k = loopStmt.kind
        if k == AstKind.WhileStatement or k == AstKind.RepeatStatement then
            if loopStmt.condition and findReadInRoot(loopStmt.condition, varKey) then
                return true
            end
        elseif k == AstKind.ForInStatement then
            if loopStmt.expressions then
                for _, e in ipairs(loopStmt.expressions) do
                    if findReadInRoot(e, varKey) then return true end
                end
            end
        end
        return false
    end

    -- parentChain entries describe how the block we're scanning was
    -- entered:
    --   block:        the enclosing statement-list
    --   stmtIdx:      position of the enclosing statement in `block`
    --   loopOwner:    if non-nil, the enclosing statement is a loop whose
    --                 body re-executes (so back-edge reads matter)
    local function visitBlock(block, parentChain)
        if not block or not block.statements then return end
        local removeIdx = {}
        for i, stmt in ipairs(block.statements) do
            local rhs = nil
            local lhsKey = nil
            if stmt.kind == AstKind.AssignmentStatement
                    and stmt.lhs and #stmt.lhs == 1
                    and stmt.rhs and #stmt.rhs == 1
                    and stmt.lhs[1].kind == AstKind.AssignmentVariable then
                rhs = stmt.rhs[1]
                lhsKey = vkey(stmt.lhs[1])
            end
            if lhsKey and rhs and isPropagatable(rhs) and not isSideEffecting(rhs) then
                -- Step 1: scan rest of the current block.
                local result = nextUseInBlock(block, i + 1, lhsKey)
                -- The "back-edge target" we'd loop back to when exiting
                -- through the innermost enclosing loop body.  Starts at
                -- (block, i); as we walk up out of a loop, this shifts
                -- to the next outer body.
                local innerBlock = block
                local innerStop = i  -- statements 1..innerStop-1 re-execute
                local pidx = #parentChain
                while result == "neutral" and pidx > 0 do
                    local pb = parentChain[pidx]
                    if pb.loopOwner then
                        -- The block we're about to exit is a loop body
                        -- whose header is pb.loopOwner.  Back-edge: the
                        -- header re-evaluates and the body re-runs from
                        -- statement 1 up to (but not including) our
                        -- previous position.
                        if loopHeaderReads(pb.loopOwner, lhsKey) then
                            result = "read"
                            break
                        end
                        local back = rangeUseInBlock(innerBlock, 1, innerStop - 1, lhsKey)
                        if back ~= "neutral" then
                            result = back
                            break
                        end
                    end
                    -- Scan forward in the enclosing block past the
                    -- nesting statement.
                    local fwd = nextUseInBlock(pb.block, pb.stmtIdx + 1, lhsKey)
                    if fwd ~= "neutral" then
                        result = fwd
                        break
                    end
                    -- Climb: the next iteration's back-edge target is
                    -- this enclosing block.
                    innerBlock = pb.block
                    innerStop = pb.stmtIdx
                    pidx = pidx - 1
                end
                if result == "write" or result == "neutral" then
                    removeIdx[i] = true
                end
            end

            -- Recurse into nested blocks with extended parent chain.
            local k = stmt.kind
            if k == AstKind.IfStatement then
                local nested = {}
                for _, p in ipairs(parentChain) do nested[#nested + 1] = p end
                nested[#nested + 1] = { block = block, stmtIdx = i, loopOwner = nil }
                visitBlock(stmt.body, nested)
                if stmt.elseifs then
                    for _, ei in ipairs(stmt.elseifs) do
                        visitBlock(ei.body, nested)
                    end
                end
                if stmt.elsebody then visitBlock(stmt.elsebody, nested) end
            elseif k == AstKind.DoStatement then
                local nested = {}
                for _, p in ipairs(parentChain) do nested[#nested + 1] = p end
                nested[#nested + 1] = { block = block, stmtIdx = i, loopOwner = nil }
                visitBlock(stmt.body, nested)
            elseif k == AstKind.WhileStatement
                    or k == AstKind.RepeatStatement
                    or k == AstKind.ForStatement
                    or k == AstKind.ForInStatement then
                local nested = {}
                for _, p in ipairs(parentChain) do nested[#nested + 1] = p end
                nested[#nested + 1] = { block = block, stmtIdx = i, loopOwner = stmt }
                visitBlock(stmt.body, nested)
            end

            -- Recurse into nested function literals (fresh parent chain).
            local function recurseLits(node)
                if type(node) ~= "table" or not node.kind then return end
                if node.kind == AstKind.FunctionLiteralExpression then
                    eliminateDeadStores(node.body, removedCounter)
                    return
                end
                for kk, v in pairs(node) do
                    if kk ~= "kind" and kk ~= "scope" and kk ~= "parentScope"
                            and kk ~= "baseScope" and kk ~= "globalScope" then
                        if type(v) == "table" then
                            if v.kind then
                                recurseLits(v)
                            else
                                for _, vv in ipairs(v) do
                                    if type(vv) == "table" and vv.kind then
                                        recurseLits(vv)
                                    end
                                end
                            end
                        end
                    end
                end
            end
            if k == AstKind.AssignmentStatement then
                if stmt.rhs then for _, e in ipairs(stmt.rhs) do recurseLits(e) end end
            elseif k == AstKind.LocalVariableDeclaration then
                if stmt.expressions then for _, e in ipairs(stmt.expressions) do recurseLits(e) end end
            elseif k == AstKind.FunctionCallStatement
                    or k == AstKind.PassSelfFunctionCallStatement then
                recurseLits(stmt.base)
                if stmt.args then for _, a in ipairs(stmt.args) do recurseLits(a) end end
            elseif k == AstKind.ReturnStatement then
                if stmt.args then for _, a in ipairs(stmt.args) do recurseLits(a) end end
            end
        end
        if next(removeIdx) ~= nil then
            local kept = {}
            for i, s in ipairs(block.statements) do
                if not removeIdx[i] then kept[#kept + 1] = s
                else removedCounter.n = removedCounter.n + 1 end
            end
            block.statements = kept
        end
    end

    visitBlock(funcBody, {})
end

processFunction = function(funcBody, removedCounter)
    if not funcBody or funcBody.kind ~= AstKind.Block
            or not funcBody.statements then
        return
    end
    -- First: per-block propagation.  Establishes the post-substitution
    -- form.
    processBlock(funcBody, {}, {}, {}, removedCounter)
    -- Second: cross-block DCE for what remains.  Iterate until fixed
    -- point because removing one dead store can expose its predecessors
    -- (e.g. `r1 = expr; r1 = r2` where after removing the second, the
    -- first becomes dead too).
    local last = removedCounter.n - 1
    while removedCounter.n ~= last do
        last = removedCounter.n
        eliminateDeadStores(funcBody, removedCounter)
    end
end

function M.apply(ast)
    local removed = { n = 0 }
    if ast.kind == AstKind.TopNode then
        processFunction(ast.body, removed)
    elseif ast.kind == AstKind.Block then
        processFunction(ast, removed)
    end
    return { note = ("propagated and removed " .. tostring(removed.n)
        .. " dead store(s)") }
end

return M
