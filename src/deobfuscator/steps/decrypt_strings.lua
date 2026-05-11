-- prometheus-test-deobfuscator - reverse of EncryptStrings.
--
-- EncryptStrings emits a `do ... end` block that defines:
--
--     STRINGS = setmetatable({}, { __index = realStrings, __metatable = nil })
--     function DECRYPT(str, seed) ... end  -- real signature is global
--
-- where DECRYPT seeds an internal stream cipher (state_45 / state_8 LCG-ish)
-- with `seed`, decrypts `str` byte-by-byte, stores the plaintext in
-- realStrings[seed], and returns `seed` so that `STRINGS[seed]` then yields the
-- plaintext.
--
-- After ConstantArray has been reversed, every site that used a string ends
-- up looking like `STRINGS[DECRYPT("ciphertext-bytes", <seedNumber>)]`.
--
-- We:
--   1. Locate the `do ... end` block defining DECRYPT/STRINGS.
--   2. Extract the four magic constants from its source: `param_mul_45`,
--      `param_add_45`, `param_mul_8`, `secret_key_8`.
--   3. Re-implement DECRYPT in the deobfuscator process.
--   4. Walk the AST and replace every `STRINGS[DECRYPT(<lit>, <num>)]` with
--      `StringExpression(decrypted)`.
--   5. Remove the do-block and the residual STRINGS / DECRYPT references.
--
-- Variables are mangled, so we identify them by structure rather than name:
-- the `do` block contains a `function DECRYPT(str, seed) ... end` whose body
-- references `realStrings`, `state_45`, `state_8`, etc.; STRINGS is the
-- variable assigned `setmetatable(...)` with `__index = realStrings`.

local Ast = require("prometheus.ast")
local AstKind = Ast.AstKind
local astutil = require("deobfuscator.ast_utils")

local M = {}

local function asNumber(node)
    if node and node.kind == AstKind.NumberExpression then return node.value end
    return nil
end

local function asString(node)
    if node and node.kind == AstKind.StringExpression then return node.value end
    return nil
end

local function isVar(n) return n and n.kind == AstKind.VariableExpression end
local function sameVarRef(a, scope, id)
    return isVar(a) and a.scope == scope and a.id == id
end

-- Extract numeric assignment value from a statement of the form
-- `state_45 = (state_45 * NUMA + NUMB) % 35184372088832`.
-- We recognize the assignment by structural shape (parens, mul, add, mod).
local function tryExtractStateUpdate(stat)
    if stat.kind ~= AstKind.AssignmentStatement then return nil end
    if not stat.rhs or #stat.rhs ~= 1 then return nil end
    local rhs = stat.rhs[1]
    if rhs.kind ~= AstKind.ModExpression then return nil end
    local m = asNumber(rhs.rhs)
    if m ~= 35184372088832 then return nil end
    local addExpr = rhs.lhs
    if addExpr.kind ~= AstKind.AddExpression then return nil end
    local mulExpr = addExpr.lhs
    local addRhs = addExpr.rhs
    if mulExpr.kind ~= AstKind.MulExpression then return nil end
    local addNum = asNumber(addRhs)
    if not addNum then return nil end
    local mulNum = asNumber(mulExpr.rhs)
    if not mulNum then
        mulNum = asNumber(mulExpr.lhs)
        if not mulNum then return nil end
    end
    return { mul45 = mulNum, add45 = addNum }
end

-- Try to extract the multiplicative constant `param_mul_8` from
-- `state_8 = state_8 * NUMC % 257`.
local function tryExtractMul8(stat)
    if stat.kind ~= AstKind.AssignmentStatement then return nil end
    if not stat.rhs or #stat.rhs ~= 1 then return nil end
    local rhs = stat.rhs[1]
    if rhs.kind ~= AstKind.ModExpression then return nil end
    local m = asNumber(rhs.rhs)
    if m ~= 257 then return nil end
    local mulExpr = rhs.lhs
    if mulExpr.kind ~= AstKind.MulExpression then return nil end
    return asNumber(mulExpr.rhs) or asNumber(mulExpr.lhs)
end

-- Recursively find a child node satisfying predicate within an AST subtree.
local function findFirst(node, predicate, seen)
    seen = seen or {}
    if type(node) ~= "table" then return nil end
    if seen[node] then return nil end
    seen[node] = true
    if node.kind and predicate(node) then return node end
    for k, v in pairs(node) do
        if k ~= "scope" and k ~= "parentScope" and k ~= "baseScope" then
            local r = findFirst(v, predicate, seen)
            if r then return r end
        end
    end
    return nil
end

local function findAll(node, predicate, list, seen)
    list = list or {}
    seen = seen or {}
    if type(node) ~= "table" then return list end
    if seen[node] then return list end
    seen[node] = true
    if node.kind and predicate(node) then table.insert(list, node) end
    for k, v in pairs(node) do
        if k ~= "scope" and k ~= "parentScope" and k ~= "baseScope" then
            findAll(v, predicate, list, seen)
        end
    end
    return list
end

-- Find the "prevVal" variable in DECRYPT's body by structure: it's the LHS of
-- the assignment inside the per-byte loop that uses `string.byte(str, i)`.
local function findPrevValVar(decryptFunc)
    -- Walk DECRYPT's body looking for any AssignmentStatement of the form:
    --     <var> = (string.byte(<arg1>, <var2>) + ... + <var>) % 256
    -- and pull the LHS variable.
    local found
    local function walk(node, seen)
        if found then return end
        seen = seen or {}
        if type(node) ~= "table" or seen[node] then return end
        seen[node] = true
        if node.kind == AstKind.AssignmentStatement
                and node.lhs and #node.lhs == 1
                and node.lhs[1].kind == AstKind.AssignmentVariable
                and node.rhs and #node.rhs == 1 then
            local rhs = node.rhs[1]
            if rhs.kind == AstKind.ModExpression
                    and rhs.rhs and rhs.rhs.kind == AstKind.NumberExpression
                    and rhs.rhs.value == 256 then
                -- Look for string.byte inside.
                local hasStrByte = findFirst(rhs.lhs, function(n)
                    if n.kind == AstKind.FunctionCallExpression
                            and n.base and n.base.kind == AstKind.IndexExpression
                            and isVar(n.base.base)
                            and n.base.base.scope:getVariableName(n.base.base.id) == "string"
                            and n.base.index and n.base.index.kind == AstKind.StringExpression
                            and n.base.index.value == "byte" then
                        return true
                    end
                    -- Also handle pre-localized `byte = string.byte` style.
                    if n.kind == AstKind.FunctionCallExpression
                            and isVar(n.base)
                            and n.base.scope:getVariableName(n.base.id) == "byte" then
                        return true
                    end
                    return false
                end)
                if hasStrByte then
                    found = {
                        scope = node.lhs[1].scope,
                        id = node.lhs[1].id,
                    }
                    return
                end
            end
        end
        for k, v in pairs(node) do
            if k ~= "scope" and k ~= "parentScope" and k ~= "baseScope" then
                if type(v) == "table" then walk(v, seen) end
            end
        end
    end
    walk(decryptFunc.body)
    return found
end

-- Extract `secret_key_8` from `local <prevVal-var> = NUMBER` somewhere in the
-- DECRYPT function's body.  The prevVal var is identified by structure (see
-- findPrevValVar).
local function tryExtractSecretKey8(stat)
    local prevVar = findPrevValVar(stat)
    if not prevVar then return nil end

    local secret
    local function walk(node, seen)
        if secret ~= nil then return end
        seen = seen or {}
        if type(node) ~= "table" or seen[node] then return end
        seen[node] = true
        if node.kind == AstKind.LocalVariableDeclaration
                and node.scope == prevVar.scope
                and node.ids then
            for i, id in ipairs(node.ids) do
                if id == prevVar.id then
                    local rhs = node.expressions and node.expressions[i]
                    if rhs and rhs.kind == AstKind.NumberExpression then
                        secret = rhs.value
                        return
                    end
                end
            end
        end
        for k, v in pairs(node) do
            if k ~= "scope" and k ~= "parentScope" and k ~= "baseScope" then
                if type(v) == "table" then walk(v, seen) end
            end
        end
    end
    walk(stat.body)
    return secret
end

-- Identify the EncryptStrings do-block.  Returns:
--   { doStat = stat, decryptScope, decryptId, stringsScope, stringsId,
--     mul45, add45, mul8, secretKey8 }
local function findEncryptStringsBlock(astBlock)
    for _, stat in ipairs(astBlock.statements) do
        if stat.kind == AstKind.DoStatement then
            local body = stat.body

            -- The state update statements live anywhere inside the do-block
            -- (typically in a nested `local function n()` helper that is
            -- closed over by the DECRYPT function).
            local update = findFirst(body, function(n)
                return tryExtractStateUpdate(n) ~= nil
            end)
            local mulInfo = update and tryExtractStateUpdate(update)
            local mul8Stat = findFirst(body, function(n)
                return tryExtractMul8(n) ~= nil
            end)
            local mul8Info = mul8Stat and tryExtractMul8(mul8Stat)
            if not (mulInfo and mul8Info) then
                -- Doesn't match an EncryptStrings shape; try the next do-block.
                -- (the update test alone is highly specific so a false hit is
                -- unlikely.)
            end

            -- Find the DECRYPT FunctionDeclaration: takes 2 args, references
            -- `prevVal` somewhere inside, and is at the top level of the do.
            local decryptFunc
            for _, s2 in ipairs(body.statements) do
                if s2.kind == AstKind.FunctionDeclaration
                        and s2.args and #s2.args == 2 then
                    local secretKey8 = tryExtractSecretKey8(s2)
                    if secretKey8 then
                        decryptFunc = s2
                        break
                    end
                end
            end

            -- Find STRINGS = setmetatable(...) somewhere in the do-block.
            local stringsScope, stringsId
            local function findSetmeta(node, seen)
                seen = seen or {}
                if type(node) ~= "table" or seen[node] then return end
                seen[node] = true
                if node.kind == AstKind.AssignmentStatement
                        and node.lhs and node.lhs[1]
                        and node.lhs[1].kind == AstKind.AssignmentVariable then
                    local rhs = node.rhs and node.rhs[1]
                    if rhs and rhs.kind == AstKind.FunctionCallExpression
                            and isVar(rhs.base)
                            and rhs.base.scope:getVariableName(rhs.base.id) == "setmetatable" then
                        stringsScope = node.lhs[1].scope
                        stringsId = node.lhs[1].id
                        return
                    end
                end
                for k, v in pairs(node) do
                    if k ~= "scope" and k ~= "parentScope" and k ~= "baseScope" then
                        findSetmeta(v, seen)
                        if stringsScope then return end
                    end
                end
            end
            findSetmeta(body)

            if decryptFunc and mulInfo and mul8Info and stringsScope and stringsId then
                local secretKey8 = tryExtractSecretKey8(decryptFunc)
                if secretKey8 then
                    return {
                        doStat = stat,
                        decryptScope = decryptFunc.scope,
                        decryptId = decryptFunc.id,
                        stringsScope = stringsScope,
                        stringsId = stringsId,
                        mul45 = mulInfo.mul45,
                        add45 = mulInfo.add45,
                        mul8 = mul8Info,
                        secretKey8 = secretKey8,
                    }
                end
            end
        end
    end
    return nil
end

-- Reference implementation of the Prometheus DECRYPT routine, derived from
-- src/prometheus/steps/EncryptStrings.lua, ported to plain Lua.
local function makeDecryptor(info)
    local floor = math.floor
    local mul45, add45, mul8, secret8 = info.mul45, info.add45, info.mul8, info.secretKey8

    return function(cipher, seed)
        -- Reset state.
        local state_45 = seed % 35184372088832
        local state_8 = seed % 255 + 2
        local prev_values = {}

        local function get_next_pseudo_random_byte()
            if #prev_values == 0 then
                state_45 = (state_45 * mul45 + add45) % 35184372088832
                repeat
                    state_8 = state_8 * mul8 % 257
                until state_8 ~= 1
                local r = state_8 % 32
                local shift = 13 - (state_8 - r) / 32
                local n = floor(state_45 / 2 ^ shift) % 4294967296 / 2 ^ r
                local rnd = floor(n % 1 * 4294967296) + floor(n)
                local low_16 = rnd % 65536
                local high_16 = (rnd - low_16) / 65536
                prev_values = {
                    low_16 % 256,
                    (low_16 - low_16 % 256) / 256,
                    high_16 % 256,
                    (high_16 - high_16 % 256) / 256,
                }
            end
            local len = #prev_values
            local byte = prev_values[len]
            prev_values[len] = nil
            return byte
        end

        local len = #cipher
        local s = {}
        local prevVal = secret8
        for i = 1, len do
            prevVal = (string.byte(cipher, i) + get_next_pseudo_random_byte() + prevVal) % 256
            s[i] = string.char(prevVal)
        end
        return table.concat(s)
    end
end

-- ---------------------------------------------------------------------------

function M.apply(ast)
    local info = findEncryptStringsBlock(ast.body)
    if not info then
        return { note = "no EncryptStrings block detected" }
    end

    local decrypt = makeDecryptor(info)

    -- Replace every `STRINGS[DECRYPT(<lit>, <num>)]` with the literal string.
    local replaced = 0
    local errors = 0
    astutil.transformExpressions(ast, function(node)
        if node.kind == AstKind.IndexExpression
                and isVar(node.base)
                and node.base.scope == info.stringsScope
                and node.base.id == info.stringsId
                and node.index.kind == AstKind.FunctionCallExpression
                and isVar(node.index.base)
                and node.index.base.scope == info.decryptScope
                and node.index.base.id == info.decryptId
                and node.index.args and #node.index.args == 2 then
            local cipher = asString(node.index.args[1])
            local seed = asNumber(node.index.args[2])
            if cipher and seed then
                local ok, plain = pcall(decrypt, cipher, seed)
                if ok and type(plain) == "string" then
                    replaced = replaced + 1
                    return Ast.StringExpression(plain)
                else
                    errors = errors + 1
                end
            end
        end
        return nil
    end)

    -- Remove the do-block now that all references are inlined.  Also remove
    -- the `local STRINGS, DECRYPT;` forward declaration that EncryptStrings
    -- emits just before the do-block, plus any other local that's now a dead
    -- forward decl referencing the same scope/ids.
    local i = 1
    while i <= #ast.body.statements do
        local s = ast.body.statements[i]
        if s == info.doStat then
            table.remove(ast.body.statements, i)
        elseif s.kind == AstKind.LocalVariableDeclaration
                and (not s.expressions or #s.expressions == 0)
                and s.ids and #s.ids >= 1 then
            -- Check if this declares the STRINGS or DECRYPT vars (or both).
            local declares = {}
            for _, id in ipairs(s.ids) do declares[id] = true end
            if (s.scope == info.stringsScope and declares[info.stringsId])
                    or (s.scope == info.decryptScope and declares[info.decryptId]) then
                table.remove(ast.body.statements, i)
            else
                i = i + 1
            end
        else
            i = i + 1
        end
    end

    return { note = string.format(
        "EncryptStrings reversed: replaced %d call(s)%s",
        replaced, errors > 0 and (", " .. errors .. " errors") or "") }
end

return M
