-- prometheus-test-deobfuscator - AST utility helpers.

local Ast = require("prometheus.ast")
local AstKind = Ast.AstKind

local M = {}

-- Treat NumberExpression and BooleanExpression / StringExpression as primitives.
M.AstKind = AstKind

function M.isNumber(node)
    return node and node.kind == AstKind.NumberExpression
end

function M.isString(node)
    return node and node.kind == AstKind.StringExpression
end

function M.isVariable(node)
    return node and node.kind == AstKind.VariableExpression
end

function M.varName(node)
    if not M.isVariable(node) then return nil end
    return node.scope:getVariableName(node.id)
end

-- Compare two variable references by (scope, id).
function M.sameVar(a, b)
    if not (M.isVariable(a) and M.isVariable(b)) then return false end
    return a.scope == b.scope and a.id == b.id
end

-- Return numeric value of a NumberExpression node; nil otherwise.
function M.numberValue(node)
    if M.isNumber(node) then return node.value end
    return nil
end

-- Return string value of a StringExpression node; nil otherwise.
function M.stringValue(node)
    if M.isString(node) then return node.value end
    return nil
end

-- Walk a Block recursively, calling visitor(stat, block, index, parent_block_chain)
-- for every statement.  Visitor may return:
--   "remove"  - drop the statement
--   table     - replace the statement with the returned statements (a list of
--               new statement nodes; empty list = same as "remove")
--   nil       - keep statement as-is
function M.walkStatements(block, visitor, parents)
    parents = parents or {}
    table.insert(parents, block)

    local i = 1
    while i <= #block.statements do
        local stat = block.statements[i]
        local res = visitor(stat, block, i, parents)
        if res == "remove" then
            table.remove(block.statements, i)
        elseif type(res) == "table" then
            table.remove(block.statements, i)
            for k = #res, 1, -1 do
                table.insert(block.statements, i, res[k])
            end
            i = i + #res
        else
            i = i + 1
        end

        -- Recurse into nested blocks.  We re-fetch the statement because the
        -- visitor may have replaced it, in which case we already moved past.
        local newStat = block.statements[i - 1]
        if newStat then
            M.walkStatementChildren(newStat, visitor, parents)
        end
    end

    table.remove(parents)
end

local function walkBlock(b, visitor, parents)
    if b then M.walkStatements(b, visitor, parents) end
end

function M.walkStatementChildren(stat, visitor, parents)
    local k = stat.kind
    if k == AstKind.DoStatement then
        walkBlock(stat.body, visitor, parents)
    elseif k == AstKind.WhileStatement or k == AstKind.RepeatStatement then
        walkBlock(stat.body, visitor, parents)
    elseif k == AstKind.ForStatement or k == AstKind.ForInStatement then
        walkBlock(stat.body, visitor, parents)
    elseif k == AstKind.IfStatement then
        walkBlock(stat.body, visitor, parents)
        if stat.elseifs then
            for _, ei in ipairs(stat.elseifs) do
                walkBlock(ei.body, visitor, parents)
            end
        end
        if stat.elsebody then walkBlock(stat.elsebody, visitor, parents) end
    elseif k == AstKind.FunctionDeclaration or k == AstKind.LocalFunctionDeclaration then
        walkBlock(stat.body, visitor, parents)
    end
end

-- Like walkStatements, but also walks into FunctionLiteralExpression bodies in
-- expressions.  The walker visits expressions through a similar callback.
function M.walkExpressions(node, visitor)
    if type(node) ~= "table" or not node.kind then return end
    -- Visitor sees pre-order on this node.
    local replacement = visitor(node)
    if replacement ~= nil then
        -- Caller is responsible for handling rewrites at parent level via
        -- their own walking; this helper only descends.
    end

    local k = node.kind
    -- Generic descent based on common field names used in Prometheus AST.
    local descend = {
        TopNode      = { fields = { "body" } },
        Block        = { custom = function(n)
            for i, s in ipairs(n.statements) do M.walkExpressions(s, visitor) end
        end },
        ReturnStatement      = { fields = { "args" } },
        FunctionCallStatement = { fields = { "base", "args" } },
        PassSelfFunctionCallStatement = { fields = { "base", "args" } },
        AssignmentStatement   = { fields = { "lhs", "rhs" } },
        LocalVariableDeclaration = { fields = { "expressions" } },
        DoStatement           = { fields = { "body" } },
        WhileStatement        = { fields = { "condition", "body" } },
        RepeatStatement       = { fields = { "condition", "body" } },
        ForStatement          = { fields = { "initialValue", "finalValue", "incrementBy", "body" } },
        ForInStatement        = { fields = { "expressions", "body" } },
        IfStatement           = { custom = function(n)
            M.walkExpressions(n.condition, visitor)
            M.walkExpressions(n.body, visitor)
            if n.elseifs then
                for _, ei in ipairs(n.elseifs) do
                    M.walkExpressions(ei.condition, visitor)
                    M.walkExpressions(ei.body, visitor)
                end
            end
            if n.elsebody then M.walkExpressions(n.elsebody, visitor) end
        end },
        FunctionDeclaration       = { fields = { "body" } },
        LocalFunctionDeclaration  = { fields = { "body" } },
        FunctionLiteralExpression = { fields = { "body" } },
        FunctionCallExpression    = { fields = { "base", "args" } },
        PassSelfFunctionCallExpression = { fields = { "base", "args" } },
        IndexExpression           = { fields = { "base", "index" } },
        TableConstructorExpression = { fields = { "entries" } },
        TableEntry                = { fields = { "value" } },
        KeyedTableEntry           = { fields = { "key", "value" } },
        OrExpression              = { fields = { "lhs", "rhs" } },
        AndExpression             = { fields = { "lhs", "rhs" } },
        LessThanExpression        = { fields = { "lhs", "rhs" } },
        GreaterThanExpression     = { fields = { "lhs", "rhs" } },
        LessThanOrEqualsExpression= { fields = { "lhs", "rhs" } },
        GreaterThanOrEqualsExpression = { fields = { "lhs", "rhs" } },
        NotEqualsExpression       = { fields = { "lhs", "rhs" } },
        EqualsExpression          = { fields = { "lhs", "rhs" } },
        StrCatExpression          = { fields = { "lhs", "rhs" } },
        AddExpression             = { fields = { "lhs", "rhs" } },
        SubExpression             = { fields = { "lhs", "rhs" } },
        MulExpression             = { fields = { "lhs", "rhs" } },
        DivExpression             = { fields = { "lhs", "rhs" } },
        ModExpression             = { fields = { "lhs", "rhs" } },
        PowExpression             = { fields = { "lhs", "rhs" } },
        NotExpression             = { fields = { "rhs" } },
        LenExpression             = { fields = { "rhs" } },
        NegateExpression          = { fields = { "rhs" } },
        IfElseExpression          = { fields = { "condition", "true_value", "false_value" } },
    }

    local d = descend[k]
    if d then
        if d.custom then
            d.custom(node)
        else
            for _, f in ipairs(d.fields) do
                local v = node[f]
                if type(v) == "table" then
                    if v.kind then
                        M.walkExpressions(v, visitor)
                    else
                        for _, vv in ipairs(v) do M.walkExpressions(vv, visitor) end
                    end
                end
            end
        end
    end
end

-- A more useful variant that supports rewriting expression nodes.  visitor
-- receives a node and may return a new node to replace it (or nil to keep).
-- The walker takes care of placing the replacement back into the parent slot.
function M.transformExpressions(root, visitor)
    local transformValue, transformNode

    transformValue = function(value)
        if type(value) ~= "table" then return value end
        if value.kind then
            return transformNode(value)
        elseif value[1] ~= nil or #value > 0 then
            -- Treat as a list.  We still need to recurse into the list entries,
            -- but lists themselves aren't replaced wholesale by this helper.
            for i, v in ipairs(value) do
                value[i] = transformValue(v)
            end
            return value
        end
        return value
    end

    transformNode = function(node)
        if type(node) ~= "table" or not node.kind then return node end
        local k = node.kind

        local function tx(field)
            if node[field] ~= nil then
                node[field] = transformValue(node[field])
            end
        end

        if k == M.AstKind.TopNode then tx("body")
        elseif k == M.AstKind.Block then
            for i, s in ipairs(node.statements) do
                node.statements[i] = transformNode(s)
            end
        elseif k == M.AstKind.ReturnStatement then tx("args")
        elseif k == M.AstKind.FunctionCallStatement then tx("base"); tx("args")
        elseif k == M.AstKind.PassSelfFunctionCallStatement then tx("base"); tx("args")
        elseif k == M.AstKind.AssignmentStatement then tx("lhs"); tx("rhs")
        elseif k == M.AstKind.LocalVariableDeclaration then tx("expressions")
        elseif k == M.AstKind.DoStatement then tx("body")
        elseif k == M.AstKind.WhileStatement then tx("condition"); tx("body")
        elseif k == M.AstKind.RepeatStatement then tx("condition"); tx("body")
        elseif k == M.AstKind.ForStatement then
            tx("initialValue"); tx("finalValue"); tx("incrementBy"); tx("body")
        elseif k == M.AstKind.ForInStatement then
            tx("expressions"); tx("body")
        elseif k == M.AstKind.IfStatement then
            tx("condition"); tx("body")
            if node.elseifs then
                for _, ei in ipairs(node.elseifs) do
                    ei.condition = transformValue(ei.condition)
                    ei.body = transformValue(ei.body)
                end
            end
            tx("elsebody")
        elseif k == M.AstKind.FunctionDeclaration or k == M.AstKind.LocalFunctionDeclaration then
            tx("body")
        elseif k == M.AstKind.FunctionLiteralExpression then tx("body")
        elseif k == M.AstKind.FunctionCallExpression then tx("base"); tx("args")
        elseif k == M.AstKind.PassSelfFunctionCallExpression then tx("base"); tx("args")
        elseif k == M.AstKind.IndexExpression then tx("base"); tx("index")
        elseif k == M.AstKind.AssignmentIndexing then tx("base"); tx("index")
        elseif k == M.AstKind.AssignmentVariable then -- leaf-like; has scope/id only
        elseif k == M.AstKind.TableConstructorExpression then tx("entries")
        elseif k == M.AstKind.TableEntry then tx("value")
        elseif k == M.AstKind.KeyedTableEntry then tx("key"); tx("value")
        elseif k == M.AstKind.OrExpression or k == M.AstKind.AndExpression
                or k == M.AstKind.LessThanExpression or k == M.AstKind.GreaterThanExpression
                or k == M.AstKind.LessThanOrEqualsExpression or k == M.AstKind.GreaterThanOrEqualsExpression
                or k == M.AstKind.NotEqualsExpression or k == M.AstKind.EqualsExpression
                or k == M.AstKind.StrCatExpression or k == M.AstKind.AddExpression
                or k == M.AstKind.SubExpression or k == M.AstKind.MulExpression
                or k == M.AstKind.DivExpression or k == M.AstKind.ModExpression
                or k == M.AstKind.PowExpression then
            tx("lhs"); tx("rhs")
        elseif k == M.AstKind.NotExpression or k == M.AstKind.LenExpression
                or k == M.AstKind.NegateExpression then
            tx("rhs")
        elseif k == M.AstKind.IfElseExpression then
            tx("condition"); tx("true_value"); tx("false_value")
        elseif k == M.AstKind.CompoundAddStatement or k == M.AstKind.CompoundSubStatement
                or k == M.AstKind.CompoundMulStatement or k == M.AstKind.CompoundDivStatement
                or k == M.AstKind.CompoundModStatement or k == M.AstKind.CompoundPowStatement
                or k == M.AstKind.CompoundConcatStatement then
            tx("lhs"); tx("rhs")
        end

        local replacement = visitor(node)
        if replacement ~= nil then return replacement end
        return node
    end

    return transformNode(root)
end

return M
