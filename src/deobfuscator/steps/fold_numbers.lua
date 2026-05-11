-- prometheus-test-deobfuscator - reverse of NumbersToExpressions.
--
-- NumbersToExpressions replaces every `NumberExpression(N)` with a small
-- arithmetic tree built from random sub-numbers.  We just constant-fold any
-- arithmetic expression whose operands are all NumberExpression nodes.
--
-- Operators handled: + - * / % ^ and unary minus.

local Ast = require("prometheus.ast")
local AstKind = Ast.AstKind
local astutil = require("deobfuscator.ast_utils")

local M = {}

local function isNum(n) return n and n.kind == AstKind.NumberExpression end

local function fold(node)
    if not node or type(node) ~= "table" or not node.kind then return nil end
    local k = node.kind
    if k == AstKind.NegateExpression then
        if isNum(node.rhs) then
            return Ast.NumberExpression(-node.rhs.value)
        end
    elseif k == AstKind.AddExpression and isNum(node.lhs) and isNum(node.rhs) then
        return Ast.NumberExpression(node.lhs.value + node.rhs.value)
    elseif k == AstKind.SubExpression and isNum(node.lhs) and isNum(node.rhs) then
        return Ast.NumberExpression(node.lhs.value - node.rhs.value)
    elseif k == AstKind.MulExpression and isNum(node.lhs) and isNum(node.rhs) then
        return Ast.NumberExpression(node.lhs.value * node.rhs.value)
    elseif k == AstKind.DivExpression and isNum(node.lhs) and isNum(node.rhs) then
        if node.rhs.value ~= 0 then
            return Ast.NumberExpression(node.lhs.value / node.rhs.value)
        end
    elseif k == AstKind.ModExpression and isNum(node.lhs) and isNum(node.rhs) then
        if node.rhs.value ~= 0 then
            return Ast.NumberExpression(node.lhs.value % node.rhs.value)
        end
    elseif k == AstKind.PowExpression and isNum(node.lhs) and isNum(node.rhs) then
        return Ast.NumberExpression(node.lhs.value ^ node.rhs.value)
    end
    return nil
end

function M.apply(ast)
    -- Repeatedly transform until no changes occur.  Because the visitor in
    -- transformExpressions is called bottom-up (postorder), a single pass
    -- already folds entire constant trees, but more passes are cheap and
    -- ensure idempotence.
    local rounds = 0
    while true do
        rounds = rounds + 1
        local changed = false
        astutil.transformExpressions(ast, function(node)
            local replacement = fold(node)
            if replacement ~= nil then
                changed = true
                return replacement
            end
            return nil
        end)
        if not changed or rounds > 8 then break end
    end
    return { note = string.format("folded constant arithmetic in %d round(s)", rounds) }
end

return M
