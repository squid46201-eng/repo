-- prometheus-test-deobfuscator - reverse of AntiTamper (no-debug variant).
--
-- AntiTamper produces a `do ... end` block containing roughly:
--
--     do
--         local valid = '<random-string>';
--         for i = 0, N do
--             if i == 0 then
--                 if valid ~= '<random-string>' then while true do end end
--                 valid = <bool>;
--             elseif i == 1 then
--                 if valid == <bool> then else while true do end end
--                 valid = <bool>;
--             ...
--             elseif i == N then
--                 ...
--             end
--         end
--     end
--
-- The block has no real side effects on a non-tampered script -- it just
-- diverges if any of the integrity checks fail.  We can drop the entire block.

local Ast = require("prometheus.ast")
local AstKind = Ast.AstKind
local astutil = require("deobfuscator.ast_utils")

local M = {}

local function looksLikeAntiTamperBody(block)
    if not block or block.kind ~= AstKind.Block then return false end
    -- Expect: first statement is `local valid = '<string>'`; second statement
    -- is `for i = 0, N do ... end` whose body contains an IfStatement with a
    -- chain of `i == K` elseif arms guarding `while true do end` infinite loops.
    local stats = block.statements
    if #stats < 2 then return false end

    local s1 = stats[1]
    if s1.kind ~= AstKind.LocalVariableDeclaration then return false end
    if #s1.ids ~= 1 then return false end
    if not s1.expressions[1] or s1.expressions[1].kind ~= AstKind.StringExpression then
        return false
    end
    local validId, validScope = s1.ids[1], s1.scope
    local validName = validScope:getVariableName(validId)
    if validName ~= "valid" and not validName:match("^valid") then
        -- Variables get mangled, but we can also accept the structural match.
    end

    local s2 = stats[2]
    if s2.kind ~= AstKind.ForStatement then return false end
    if not (s2.initialValue and s2.initialValue.kind == AstKind.NumberExpression
            and s2.initialValue.value == 0) then
        return false
    end
    if not s2.body or s2.body.kind ~= AstKind.Block then return false end
    if #s2.body.statements ~= 1 then return false end
    local ifStat = s2.body.statements[1]
    if ifStat.kind ~= AstKind.IfStatement then return false end

    -- Heuristic: at least one arm should contain an infinite loop.
    local function hasInfiniteLoop(b)
        if not b or not b.statements then return false end
        for _, s in ipairs(b.statements) do
            if s.kind == AstKind.WhileStatement
                    and s.condition.kind == AstKind.BooleanExpression
                    and s.condition.value == true then
                return true
            end
            if s.kind == AstKind.IfStatement then
                if hasInfiniteLoop(s.body) then return true end
                if s.elseifs then
                    for _, ei in ipairs(s.elseifs) do
                        if hasInfiniteLoop(ei.body) then return true end
                    end
                end
                if hasInfiniteLoop(s.elsebody) then return true end
            end
        end
        return false
    end

    return hasInfiniteLoop(ifStat.body)
        or (ifStat.elseifs and (function()
            for _, ei in ipairs(ifStat.elseifs) do
                if hasInfiniteLoop(ei.body) then return true end
            end
            return false
        end)())
        or hasInfiniteLoop(ifStat.elsebody)
end

local function stripFromBlock(block)
    local removed = 0
    local i = 1
    while i <= #block.statements do
        local s = block.statements[i]
        if s.kind == AstKind.DoStatement and looksLikeAntiTamperBody(s.body) then
            table.remove(block.statements, i)
            removed = removed + 1
        else
            -- Recurse only into containers that could plausibly hold a
            -- top-level do-block.
            if s.kind == AstKind.DoStatement then
                removed = removed + stripFromBlock(s.body)
            end
            i = i + 1
        end
    end
    return removed
end

function M.apply(ast)
    local removed = stripFromBlock(ast.body)
    return { note = string.format("removed %d AntiTamper block(s)", removed) }
end

return M
