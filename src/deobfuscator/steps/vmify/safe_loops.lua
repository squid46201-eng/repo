-- prometheus-test-deobfuscator - make unconditional loops Roblox-safe.

local Ast = require("prometheus.ast")
local AstKind = Ast.AstKind

local M = {}

local function hasGlobal(ast, name)
    local scope = ast
        and ast.kind == AstKind.TopNode
        and ast.globalScope
    return scope
        and scope.variablesLookup
        and scope.variablesLookup[name] ~= nil
end

local function isConstantTrue(expr)
    return expr
        and expr.kind == AstKind.BooleanExpression
        and expr.value == true
end

local function isTaskWaitStatement(stmt)
    if not stmt or stmt.kind ~= AstKind.FunctionCallStatement then return false end
    local call = stmt.base
    return call
        and call.kind == AstKind.IndexExpression
        and call.base
        and call.base.kind == AstKind.VariableExpression
        and call.base.scope:getVariableName(call.base.id) == "task"
        and call.index
        and call.index.kind == AstKind.StringExpression
        and call.index.value == "wait"
end

local function makeTaskWaitStatement(scope)
    local taskScope, taskId = scope:resolve("task")
    local waitScope, waitId = scope:resolve("wait")
    return Ast.FunctionCallStatement(
        Ast.OrExpression(
            Ast.AndExpression(
                Ast.VariableExpression(taskScope, taskId),
                Ast.IndexExpression(
                    Ast.VariableExpression(taskScope, taskId),
                    Ast.StringExpression("wait")
                )
            ),
            Ast.VariableExpression(waitScope, waitId)
        ),
        {}
    )
end

local function processBlock(block, count)
    if not block or block.kind ~= AstKind.Block or not block.statements then
        return
    end
    for _, stmt in ipairs(block.statements) do
        if stmt.kind == AstKind.WhileStatement then
            if isConstantTrue(stmt.condition)
                    and stmt.body and stmt.body.statements
                    and not isTaskWaitStatement(stmt.body.statements[1]) then
                table.insert(stmt.body.statements, 1, makeTaskWaitStatement(stmt.body.scope or block.scope))
                count.n = count.n + 1
            end
            processBlock(stmt.body, count)
        elseif stmt.kind == AstKind.RepeatStatement
                or stmt.kind == AstKind.DoStatement
                or stmt.kind == AstKind.ForStatement
                or stmt.kind == AstKind.ForInStatement then
            processBlock(stmt.body, count)
        elseif stmt.kind == AstKind.IfStatement then
            processBlock(stmt.body, count)
            if stmt.elseifs then
                for _, elseifNode in ipairs(stmt.elseifs) do
                    processBlock(elseifNode.body, count)
                end
            end
            processBlock(stmt.elsebody, count)
        elseif stmt.kind == AstKind.FunctionDeclaration
                or stmt.kind == AstKind.LocalFunctionDeclaration then
            processBlock(stmt.body, count)
        end
    end
end

function M.apply(ast)
    if not hasGlobal(ast, "task") and not hasGlobal(ast, "game") then
        return { note = "inserted 0 task.wait() yield(s)" }
    end
    local count = { n = 0 }
    if ast.kind == AstKind.TopNode then
        processBlock(ast.body, count)
    else
        processBlock(ast, count)
    end
    return { note = ("inserted " .. tostring(count.n) .. " task.wait() yield(s)") }
end

return M
