-- prometheus-test-deobfuscator - simplify post-devirt if-branches.
--
-- The devirtualizer (M6) often emits if-statements where one of the
-- branches is empty, e.g.
--
--     if r34 then
--         -- (empty)
--     else
--         r32 = unpack
--     end
--
-- These come from Vmify's choice of which branch is "fall-through" vs
-- "jump"; after structural reconstruction, an empty fall-through arm is
-- pure noise.  This pass performs two minimal, always-safe rewrites:
--
--   1. `if X then <empty> else <stuff> end`   ->  `if not X then <stuff> end`
--   2. `if X then <stuff> else <empty> end`   ->  `if X then <stuff> end`
--
-- Both transforms are local to a single statement, preserve evaluation
-- order, and don't change semantics (empty `else` is observationally
-- identical to no `else`).

local Ast = require("prometheus.ast")
local AstKind = Ast.AstKind
local astutil = require("deobfuscator.ast_utils")

local M = {}

local function isEmptyBlock(block)
    return block ~= nil
        and block.kind == AstKind.Block
        and (block.statements == nil or #block.statements == 0)
end

local function hasNoElseifs(stat)
    return stat.elseifs == nil or #stat.elseifs == 0
end

-- Build a `not <cond>` expression while letting Prometheus's NotExpression
-- constructor fold trivial double-negations away if it can.
local function negate(cond)
    -- If the existing condition is itself a NotExpression, just unwrap it.
    if cond.kind == AstKind.NotExpression then
        return cond.rhs
    end
    return Ast.NotExpression(cond, true)
end

local function rewriteIf(stat)
    if stat.kind ~= AstKind.IfStatement then return nil end
    if not hasNoElseifs(stat) then return nil end

    local thenEmpty = isEmptyBlock(stat.body)
    local elseEmpty = stat.elsebody ~= nil and isEmptyBlock(stat.elsebody)

    -- Case 1: empty `then`, non-empty `else`  ->  invert.
    if thenEmpty and stat.elsebody ~= nil and not elseEmpty then
        stat.condition = negate(stat.condition)
        stat.body = stat.elsebody
        stat.elsebody = nil
        return 1
    end

    -- Case 2: non-empty `then`, empty `else`  ->  drop the `else`.
    if elseEmpty and not thenEmpty then
        stat.elsebody = nil
        return 1
    end

    -- Case 3: both empty  ->  drop the elsebody (the if itself stays so
    -- side effects in the condition are preserved).
    if thenEmpty and elseEmpty then
        stat.elsebody = nil
        return 1
    end

    return nil
end

local function walkBlock(block, count_ref)
    if not block or block.kind ~= AstKind.Block or not block.statements then
        return
    end
    for _, stat in ipairs(block.statements) do
        if stat.kind == AstKind.IfStatement then
            local r = rewriteIf(stat)
            if r then count_ref.n = count_ref.n + r end
            -- Recurse into both branches (after rewrite).
            walkBlock(stat.body, count_ref)
            if stat.elseifs then
                for _, ei in ipairs(stat.elseifs) do
                    walkBlock(ei.body, count_ref)
                end
            end
            walkBlock(stat.elsebody, count_ref)
        elseif stat.kind == AstKind.WhileStatement
                or stat.kind == AstKind.RepeatStatement
                or stat.kind == AstKind.DoStatement
                or stat.kind == AstKind.ForStatement
                or stat.kind == AstKind.ForInStatement then
            walkBlock(stat.body, count_ref)
        elseif stat.kind == AstKind.FunctionDeclaration
                or stat.kind == AstKind.LocalFunctionDeclaration then
            walkBlock(stat.body, count_ref)
        end
        -- Also descend into FunctionLiteralExpression nested in expressions.
        astutil.walkExpressions(stat, function(node)
            if node.kind == AstKind.FunctionLiteralExpression then
                walkBlock(node.body, count_ref)
            end
        end)
    end
end

function M.apply(ast)
    local count_ref = { n = 0 }
    -- Run to a fixed point in case rewrites expose new opportunities
    -- (e.g. nested empty branches).  Each iteration only flips a finite
    -- amount, so this terminates.
    local last
    repeat
        last = count_ref.n
        if ast.kind == AstKind.TopNode then
            walkBlock(ast.body, count_ref)
        else
            walkBlock(ast, count_ref)
        end
    until count_ref.n == last
    return { note = ("simplified " .. tostring(count_ref.n) .. " branch(es)") }
end

return M
