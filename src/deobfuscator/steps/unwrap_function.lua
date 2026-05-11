-- prometheus-test-deobfuscator - reverse of WrapInFunction.
--
-- Pattern produced by WrapInFunction:
--
--     return ((function(...) BODY end)(...))
--
-- ie. the entire script body becomes a single ReturnStatement whose argument
-- is a FunctionCallExpression whose base is a FunctionLiteralExpression
-- (taking varargs) called with varargs.  Multiple iterations stack the same
-- pattern.
--
-- We peel each such layer off the top of `ast.body`, replacing the wrapping
-- ReturnStatement with the wrapped function's body's statements.

local Ast = require("prometheus.ast")
local AstKind = Ast.AstKind

local M = {}

local function isVarargCall(callExpr)
    if callExpr.kind ~= AstKind.FunctionCallExpression then return false end
    if callExpr.base.kind ~= AstKind.FunctionLiteralExpression then return false end
    -- Function literal must take exactly one parameter: ...
    local lit = callExpr.base
    if not lit.args or #lit.args ~= 1 then return false end
    if lit.args[1].kind ~= AstKind.VarargExpression then return false end
    -- Call must pass exactly one argument: ...
    if not callExpr.args or #callExpr.args ~= 1 then return false end
    if callExpr.args[1].kind ~= AstKind.VarargExpression then return false end
    return true
end

local function tryUnwrapOnce(astBody)
    if #astBody.statements ~= 1 then return false end
    local stat = astBody.statements[1]
    if stat.kind ~= AstKind.ReturnStatement then return false end
    if not stat.args or #stat.args ~= 1 then return false end
    local call = stat.args[1]
    if not isVarargCall(call) then return false end

    -- Replace the entire body's statements with the inner function's body.
    local innerBody = call.base.body
    -- Re-parent inner block's scope under astBody.scope's parent so name
    -- resolution still works through unparser.  The unparser only uses scope
    -- to resolve names to display strings, so this is mostly cosmetic; we keep
    -- the scope chain intact by leaving scopes alone.
    astBody.statements = {}
    for i, s in ipairs(innerBody.statements) do
        astBody.statements[i] = s
    end
    return true
end

function M.apply(ast)
    local layers = 0
    while tryUnwrapOnce(ast.body) do
        layers = layers + 1
    end
    return { note = string.format("unwrapped %d WrapInFunction layer(s)", layers) }
end

return M
