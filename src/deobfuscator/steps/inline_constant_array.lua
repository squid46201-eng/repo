-- prometheus-test-deobfuscator - reverse of ConstantArray.
--
-- ConstantArray emits something like (in pseudo-Lua):
--
--     local ARR = { "encoded1", "encoded2", ... }
--     for v1, v2 in ipairs({{1,LEN},{1,SHIFT},{SHIFT+1,LEN}}) do
--         while v2[1] < v2[2] do
--             ARR[v2[1]], ARR[v2[2]], v2[1], v2[2] =
--                 ARR[v2[2]], ARR[v2[1]], v2[1] + 1, v2[2] - 1
--         end
--     end
--     local function WRAPPER(idx) return ARR[idx + OFFSET] end
--     do  -- decoder block (base64 / base85 / mixed)
--         local lookup = { ["A"]=0, ... }
--         local arr = ARR
--         for i = 1, #arr do
--             local data = arr[i]
--             if type(data) == "string" then ... arr[i] = decoded end
--         end
--     end
--
-- Strings throughout the program become `WRAPPER(N)` (or, with local wrapper
-- expansion, table-indexed calls; we don't yet support that case).
--
-- This pass:
--
--   1. Locates the array, the rotate, the decoder, and the wrapper(s).
--   2. Applies the rotate + decode to a Lua-side copy of the array values.
--   3. Inlines every `WRAPPER(N)` call as a StringExpression literal.
--   4. Drops the array decl, rotate loop, decoder, and wrapper decl(s).
--
-- The pass is best-effort: if the structure isn't recognized it leaves the AST
-- alone and reports nothing.

local Ast = require("prometheus.ast")
local AstKind = Ast.AstKind
local astutil = require("deobfuscator.ast_utils")

local M = {}

-- ---------------------------------------------------------------------------
-- Pattern recognizers
-- ---------------------------------------------------------------------------

local function asNumber(node)
    if node and node.kind == AstKind.NumberExpression then return node.value end
    return nil
end

local function asString(node)
    if node and node.kind == AstKind.StringExpression then return node.value end
    return nil
end

local function isVar(node) return node and node.kind == AstKind.VariableExpression end
local function sameVar(a, b)
    return isVar(a) and isVar(b) and a.scope == b.scope and a.id == b.id
end

-- Match `local NAME = { "...", "...", ... }`  (StringExpression entries only)
-- Returns { scope, id, values, declStat } on match.
local function tryMatchArrayDecl(stat)
    if stat.kind ~= AstKind.LocalVariableDeclaration then return nil end
    if not stat.ids or #stat.ids ~= 1 then return nil end
    local rhs = stat.expressions and stat.expressions[1]
    if not rhs or rhs.kind ~= AstKind.TableConstructorExpression then return nil end

    local values = {}
    for i, entry in ipairs(rhs.entries) do
        -- Allow plain TableEntry containing StringExpression *or* an empty
        -- string -- ConstantArray sometimes produces empties that the decoder
        -- never touches, but we still want to track them.
        if entry.kind ~= AstKind.TableEntry then return nil end
        if entry.value.kind ~= AstKind.StringExpression then return nil end
        values[i] = entry.value.value
    end
    return {
        scope = stat.scope,
        id = stat.ids[1],
        values = values,
        decl = stat,
    }
end

-- Match the rotate pattern.  Returns { shift = SHIFT } on success, or false.
-- Pattern (after constant folding):
--     for v1, v2 in ipairs( {{1,LEN},{1,SHIFT},{SHIFT+1,LEN}} ) do
--         while v2[1] < v2[2] do <four parallel assignments> end
--     end
local function tryMatchRotate(stat, arrInfo)
    if stat.kind ~= AstKind.ForInStatement then return nil end
    if not stat.expressions or #stat.expressions ~= 1 then return nil end

    local call = stat.expressions[1]
    if call.kind ~= AstKind.FunctionCallExpression then return nil end
    if not (isVar(call.base) and call.base.scope:getVariableName(call.base.id) == "ipairs") then
        return nil
    end
    if not call.args or #call.args ~= 1 then return nil end
    local outer = call.args[1]
    if outer.kind ~= AstKind.TableConstructorExpression then return nil end
    if #outer.entries ~= 3 then return nil end

    local triples = {}
    for i, entry in ipairs(outer.entries) do
        if entry.kind ~= AstKind.TableEntry then return nil end
        local sub = entry.value
        if not sub or sub.kind ~= AstKind.TableConstructorExpression then return nil end
        if #sub.entries ~= 2 then return nil end
        local a = sub.entries[1] and sub.entries[1].value
        local b = sub.entries[2] and sub.entries[2].value
        a = asNumber(a); b = asNumber(b)
        if not a or not b then return nil end
        triples[i] = { a, b }
    end
    -- Expect: {1,LEN}, {1,SHIFT}, {SHIFT+1,LEN}
    local len = #arrInfo.values
    if triples[1][1] ~= 1 then return nil end
    if triples[1][2] ~= len then return nil end
    if triples[2][1] ~= 1 then return nil end
    if triples[3][2] ~= len then return nil end
    local shift = triples[2][2]
    if triples[3][1] ~= shift + 1 then return nil end

    return { shift = shift }
end

-- Match `local function NAME(arg) return ARR[arg + OFFSET] end`
-- Also accepts `arg - OFFSET`, plain `arg`, and `OFFSET + arg`.
-- Returns { scope, id, offset, decl } on match.
local function tryMatchWrapper(stat, arrInfo)
    if stat.kind ~= AstKind.LocalFunctionDeclaration then return nil end
    if not stat.args or #stat.args ~= 1 then return nil end
    local arg = stat.args[1]
    if arg.kind ~= AstKind.VariableExpression then return nil end
    local body = stat.body
    if not body or #body.statements ~= 1 then return nil end
    local ret = body.statements[1]
    if ret.kind ~= AstKind.ReturnStatement then return nil end
    if not ret.args or #ret.args ~= 1 then return nil end

    local idx = ret.args[1]
    if idx.kind ~= AstKind.IndexExpression then return nil end
    if not isVar(idx.base) then return nil end
    if not (idx.base.scope == arrInfo.scope and idx.base.id == arrInfo.id) then
        return nil
    end

    local indexExpr = idx.index
    -- Accept various forms.
    local function isArg(n) return isVar(n) and n.scope == stat.body.scope and n.id == arg.id end
    local offset = nil
    if indexExpr.kind == AstKind.AddExpression then
        if isArg(indexExpr.lhs) and asNumber(indexExpr.rhs) then
            offset = asNumber(indexExpr.rhs)
        elseif isArg(indexExpr.rhs) and asNumber(indexExpr.lhs) then
            offset = asNumber(indexExpr.lhs)
        end
    elseif indexExpr.kind == AstKind.SubExpression then
        if isArg(indexExpr.lhs) and asNumber(indexExpr.rhs) then
            offset = -asNumber(indexExpr.rhs)
        end
    elseif isArg(indexExpr) then
        offset = 0
    end

    if offset == nil then return nil end
    return {
        scope = stat.scope,
        id = stat.ids and stat.ids[1] or stat.id,
        offset = offset,
        decl = stat,
    }
end

-- Find the prefix characters in a mixed-mode decoder.  The decoder body
-- contains, somewhere inside the for loop, an `if first == "P0" then ...
-- elseif first == "P1" then ...` chain.  We pull those literals out by
-- walking the AST.
local function findFirstChars(node, seen)
    seen = seen or {}
    if type(node) ~= "table" or seen[node] then return nil, nil end
    seen[node] = true

    -- Pattern: EqualsExpression(VariableExpression("first"-ish), StringExpression).
    if node.kind == AstKind.IfStatement then
        local function literalEqRhs(cond)
            if cond and cond.kind == AstKind.EqualsExpression then
                if cond.rhs and cond.rhs.kind == AstKind.StringExpression then
                    return cond.rhs.value
                end
                if cond.lhs and cond.lhs.kind == AstKind.StringExpression then
                    return cond.lhs.value
                end
            end
            return nil
        end
        local p0 = literalEqRhs(node.condition)
        local p1
        if node.elseifs then
            for _, ei in ipairs(node.elseifs) do
                local lit = literalEqRhs(ei.condition)
                if lit then p1 = p1 or lit end
            end
        end
        if p0 and #p0 == 1 and p1 and #p1 == 1 then
            return p0, p1
        end
    end

    for k, v in pairs(node) do
        if k ~= "scope" and k ~= "parentScope" and k ~= "baseScope" then
            if type(v) == "table" then
                local p0, p1 = findFirstChars(v, seen)
                if p0 and p1 then return p0, p1 end
            end
        end
    end
    return nil, nil
end

-- Match the decoder DoStatement.  We look inside a `do ... end` for one or two
-- `local <name> = { [stringLit] = numLit, ... }` declarations.  The size of
-- the table tells us the encoding.
--
-- Returns { encoding = "base64"|"base85"|"mixed", alphabet64 = {char->idx},
--          alphabet85 = {char->idx}, doStat = stat, prefix0 = char|nil,
--          prefix1 = char|nil } on success.
local function extractAlphabets(stat)
    if stat.kind ~= AstKind.DoStatement then return nil end
    local body = stat.body
    if not body or not body.statements then return nil end

    local function alphabetFromTable(tbl)
        if not tbl or tbl.kind ~= AstKind.TableConstructorExpression then return nil end
        local map = {}
        for _, entry in ipairs(tbl.entries) do
            if entry.kind ~= AstKind.KeyedTableEntry then return nil end
            local k = asString(entry.key)
            local v = asNumber(entry.value)
            if not k or not v then return nil end
            if #k ~= 1 then return nil end
            map[k] = v
        end
        return map
    end

    local tables = {}
    for _, s in ipairs(body.statements) do
        if s.kind == AstKind.LocalVariableDeclaration then
            for i = 1, #s.ids do
                local rhs = s.expressions and s.expressions[i]
                if rhs and rhs.kind == AstKind.TableConstructorExpression then
                    local map = alphabetFromTable(rhs)
                    if map then
                        local n = 0
                        for _ in pairs(map) do n = n + 1 end
                        if n == 64 or n == 85 then
                            table.insert(tables, { size = n, map = map })
                        end
                    end
                end
            end
        end
    end

    if #tables == 0 then return nil end

    local result = { doStat = stat }
    local has64, has85
    for _, t in ipairs(tables) do
        if t.size == 64 then has64 = t.map end
        if t.size == 85 then has85 = t.map end
    end
    if has64 and has85 then
        result.encoding = "mixed"
        result.alphabet64 = has64
        result.alphabet85 = has85
        result.prefix0, result.prefix1 = findFirstChars(stat)
    elseif has64 then
        result.encoding = "base64"
        result.alphabet64 = has64
    elseif has85 then
        result.encoding = "base85"
        result.alphabet85 = has85
    else
        return nil
    end

    return result
end

-- ---------------------------------------------------------------------------
-- Decoders
-- ---------------------------------------------------------------------------

local function decodeBase64(data, alphabet)
    if data == "" then return "" end
    local parts = {}
    local value = 0
    local count = 0
    local i = 1
    local len = #data
    while i <= len do
        local ch = data:sub(i, i)
        local code = alphabet[ch]
        if code then
            value = value + code * (64 ^ (3 - count))
            count = count + 1
            if count == 4 then
                count = 0
                local c1 = math.floor(value / 65536)
                local c2 = math.floor((value % 65536) / 256)
                local c3 = value % 256
                table.insert(parts, string.char(c1, c2, c3))
                value = 0
            end
        elseif ch == "=" then
            table.insert(parts, string.char(math.floor(value / 65536)))
            if i >= len or data:sub(i + 1, i + 1) ~= "=" then
                table.insert(parts, string.char(math.floor((value % 65536) / 256)))
            end
            break
        end
        i = i + 1
    end
    return table.concat(parts)
end

local function decodeBase85(data, alphabet)
    if data == "" then return "" end
    local parts = {}
    local idx = 1
    local len = #data
    while idx <= len do
        local remain = len - idx + 1
        local count = remain >= 5 and 5 or remain
        local value = 0
        local valid = count > 1
        for j = 0, 4 do
            local code
            if j < count then
                local ch = data:sub(idx + j, idx + j)
                code = alphabet[ch]
                if not code then
                    valid = false
                    break
                end
            else
                code = 84
            end
            value = value * 85 + code
        end
        if valid then
            local b1 = math.floor(value / 16777216) % 256
            local b2 = math.floor(value / 65536) % 256
            local b3 = math.floor(value / 256) % 256
            local b4 = value % 256
            if count == 5 then
                table.insert(parts, string.char(b1, b2, b3, b4))
            elseif count == 4 then
                table.insert(parts, string.char(b1, b2, b3))
            elseif count == 3 then
                table.insert(parts, string.char(b1, b2))
            elseif count == 2 then
                table.insert(parts, string.char(b1))
            end
        end
        idx = idx + count
    end
    return table.concat(parts)
end

local function decodeArray(values, dec)
    local out = {}
    for i, v in ipairs(values) do
        if type(v) == "string" and v ~= "" then
            if dec.encoding == "base64" then
                out[i] = decodeBase64(v, dec.alphabet64)
            elseif dec.encoding == "base85" then
                out[i] = decodeBase85(v, dec.alphabet85)
            elseif dec.encoding == "mixed" then
                local first = v:sub(1, 1)
                local rest = v:sub(2)
                if dec.prefix0 and first == dec.prefix0 then
                    out[i] = decodeBase64(rest, dec.alphabet64)
                elseif dec.prefix1 and first == dec.prefix1 then
                    out[i] = decodeBase85(rest, dec.alphabet85)
                else
                    -- Fall back to alphabet-based heuristic when we couldn't
                    -- recover prefixes.
                    local function looks64(s)
                        for k = 1, #s do
                            local ch = s:sub(k, k)
                            if not (dec.alphabet64[ch] or ch == "=") then return false end
                        end
                        return true
                    end
                    if looks64(rest) then
                        out[i] = decodeBase64(rest, dec.alphabet64)
                    else
                        out[i] = decodeBase85(rest, dec.alphabet85)
                    end
                end
            else
                out[i] = v
            end
        else
            out[i] = v
        end
    end
    return out
end

local function rotateInPlace(t, shift)
    -- Implements the Prometheus rotate code: same as a rotate-left by `shift`.
    -- The three-pass reverse algorithm in the obfuscator is equivalent.
    local function reverse(arr, i, j)
        while i < j do
            arr[i], arr[j] = arr[j], arr[i]
            i, j = i + 1, j - 1
        end
    end
    local n = #t
    reverse(t, 1, n)
    reverse(t, 1, shift)
    reverse(t, shift + 1, n)
end

-- ---------------------------------------------------------------------------
-- Block-level driver
-- ---------------------------------------------------------------------------

local function tryProcessBlock(block)
    local stats = block.statements
    if not stats then return 0 end

    -- Step 1: find an array decl in this block.
    local arrInfo, arrIdx
    for i, s in ipairs(stats) do
        local info = tryMatchArrayDecl(s)
        if info and #info.values >= 4 then
            -- Heuristic to skip non-ConstantArray local tables -- the array
            -- usually has a sizeable number of entries.
            arrInfo = info
            arrIdx = i
            break
        end
    end
    if not arrInfo then return 0 end

    -- Step 2: scan the rest of the block for rotate / wrapper / decoder.
    local rotateStat, rotateInfo
    local wrapperInfo, wrapperStat
    local decoderInfo
    for i = arrIdx + 1, #stats do
        local s = stats[i]
        if not rotateInfo then
            local r = tryMatchRotate(s, arrInfo)
            if r then rotateStat = s; rotateInfo = r end
        end
        if not wrapperInfo then
            local w = tryMatchWrapper(s, arrInfo)
            if w then wrapperStat = s; wrapperInfo = w end
        end
        if not decoderInfo then
            local d = extractAlphabets(s)
            if d then decoderInfo = d end
        end
    end

    if not wrapperInfo then
        -- Without a wrapper we can't easily inline, bail.
        return 0
    end

    -- Step 3: apply rotate + decode to a Lua-side copy.
    local values = {}
    for i, v in ipairs(arrInfo.values) do values[i] = v end

    if rotateInfo then
        rotateInPlace(values, rotateInfo.shift)
    end
    if decoderInfo then
        values = decodeArray(values, decoderInfo)
    end

    -- Step 4: traverse the entire AST and replace every WRAPPER(N) with the
    -- corresponding StringExpression.
    local replacedCalls = 0
    local missing = 0
    astutil.transformExpressions(block, function(node)
        if node.kind == AstKind.FunctionCallExpression
                and isVar(node.base)
                and node.base.scope == wrapperInfo.scope
                and node.base.id == wrapperInfo.id
                and node.args and #node.args == 1
                and node.args[1].kind == AstKind.NumberExpression then
            local idx = node.args[1].value + wrapperInfo.offset
            local s = values[idx]
            if type(s) == "string" then
                replacedCalls = replacedCalls + 1
                return Ast.StringExpression(s)
            else
                missing = missing + 1
            end
        end
        return nil
    end)

    -- Step 5: drop the array decl, rotate, wrapper and decoder.  We do this in
    -- one pass over `stats` to avoid index drift.
    local toDrop = { [arrInfo.decl] = true }
    if rotateStat then toDrop[rotateStat] = true end
    if wrapperStat then toDrop[wrapperStat] = true end
    if decoderInfo and decoderInfo.doStat then toDrop[decoderInfo.doStat] = true end

    local i = 1
    while i <= #stats do
        if toDrop[stats[i]] then
            table.remove(stats, i)
        else
            i = i + 1
        end
    end

    return 1, replacedCalls, missing
end

function M.apply(ast)
    -- Run on the top-level body; we generally don't expect ConstantArray inside
    -- nested blocks, but recursing wouldn't hurt -- skip for now.
    local notes = {}
    local processed, replaced, missing = tryProcessBlock(ast.body)
    if processed and processed > 0 then
        table.insert(notes, string.format(
            "ConstantArray reversed: replaced %d wrapper call(s)%s",
            replaced or 0,
            (missing or 0) > 0 and (", " .. missing .. " unresolved") or ""))
    else
        table.insert(notes, "no ConstantArray pattern detected")
    end
    return { note = table.concat(notes, "; ") }
end

return M
