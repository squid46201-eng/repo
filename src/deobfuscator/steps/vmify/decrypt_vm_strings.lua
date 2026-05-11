-- prometheus-test-deobfuscator - decrypt strings post-devirtualization.
--
-- After Vmify is devirtualized (M6), the EncryptStrings decoder that lived
-- inside the VM is restored to plain Lua source.  This pass:
--
--   1. Locates the in-VM decoder by structure (LCG over 2^45, key cycle
--      mod 257, and a per-byte loop calling string.byte on its first arg).
--   2. Extracts the four magic constants:
--          param_mul_45, param_add_45 (from `% 35184372088832`)
--          param_mul_8                (from `% 257`)
--          secret_key_8               (initial accumulator inside decoder)
--   3. Finds the proxy variable (assigned setmetatable({}, {__index=cache})).
--   4. Replays the decoder for every `proxy[decoder(c, n)]` call site and
--      replaces the index expression with a string literal.
--
-- The decoder algorithm is fixed in Prometheus's EncryptStrings (only the
-- four magic constants are randomized per-build), so once we find the
-- constants the decryption is purely arithmetic.

local Ast = require("prometheus.ast")
local AstKind = Ast.AstKind
local astutil = require("deobfuscator.ast_utils")

local M = {}

local function isVar(n) return n and n.kind == AstKind.VariableExpression end
local function asNumber(n)
    if n and n.kind == AstKind.NumberExpression then return n.value end
end
local function asString(n)
    if n and n.kind == AstKind.StringExpression then return n.value end
end
local function vkey(node)
    if not isVar(node) then return nil end
    return tostring(node.scope) .. "/" .. tostring(node.id)
end
local function akey(node)
    -- AssignmentVariable -> stable key.
    if not node or node.kind ~= AstKind.AssignmentVariable then return nil end
    return tostring(node.scope) .. "/" .. tostring(node.id)
end

local function nodeKey(node)
    if isVar(node) then return vkey(node) end
    return akey(node)
end

local function varName(node)
    if not isVar(node) then return nil end
    local ok, name = pcall(function()
        return node.scope:getVariableName(node.id)
    end)
    if ok then return name end
    return nil
end

-- Generic structural walk: visit every node table reachable from `root`.
local function walk(node, fn, seen)
    seen = seen or {}
    if type(node) ~= "table" or seen[node] then return end
    seen[node] = true
    if node.kind then fn(node) end
    for k, v in pairs(node) do
        if k ~= "scope" and k ~= "parentScope" and k ~= "baseScope" then
            walk(v, fn, seen)
        end
    end
end

-- `<v> = (<v> * NUMA + NUMB) % 35184372088832` -> NUMA, NUMB.
local function extractLCG45(rhs)
    if rhs.kind ~= AstKind.ModExpression then return nil end
    if asNumber(rhs.rhs) ~= 35184372088832 then return nil end
    local addExpr = rhs.lhs
    if addExpr.kind ~= AstKind.AddExpression then return nil end
    local mulExpr = addExpr.lhs
    if mulExpr.kind ~= AstKind.MulExpression then return nil end
    local addNum = asNumber(addExpr.rhs)
    if not addNum then return nil end
    local mulNum = asNumber(mulExpr.rhs) or asNumber(mulExpr.lhs)
    if not mulNum then return nil end
    return mulNum, addNum
end

-- `<v> = (<v> * NUMC) % 257` -> NUMC.
local function extractMul8(rhs)
    if rhs.kind ~= AstKind.ModExpression then return nil end
    if asNumber(rhs.rhs) ~= 257 then return nil end
    local mulExpr = rhs.lhs
    if mulExpr.kind ~= AstKind.MulExpression then return nil end
    return asNumber(mulExpr.rhs) or asNumber(mulExpr.lhs)
end

local function isStringByteCall(node, aliases)
    if not (node and node.kind == AstKind.FunctionCallExpression) then return false end
    local base = node.base
    if not (base and base.kind == AstKind.IndexExpression) then return false end
    if asString(base.index) ~= "byte" then return false end
    if isVar(base.base) then
        if varName(base.base) == "string" then return true end
        local k = vkey(base.base)
        if k and aliases and aliases[k] then return true end
    end
    return false
end

-- Pure-Lua replica of the decoder, parameterized by the four magic constants.
local function makeDecoder(mul45, add45, mul8, secret8)
    local floor = math.floor
    local chars = {}
    for k = 1, 256 do chars[k] = string.char(k - 1) end

    local state_45, state_8, prev_values

    local function gen32()
        state_45 = (state_45 * mul45 + add45) % 35184372088832
        repeat
            state_8 = state_8 * mul8 % 257
        until state_8 ~= 1
        local r = state_8 % 32
        local n = floor(state_45 / 2 ^ (13 - (state_8 - r) / 32))
                    % 4294967296 / 2 ^ r
        return floor(n % 1 * 4294967296) + floor(n)
    end

    local function nextByte()
        if #prev_values == 0 then
            local rnd = gen32()
            local low_16 = rnd % 65536
            local high_16 = (rnd - low_16) / 65536
            local b1 = low_16 % 256
            local b2 = (low_16 - b1) / 256
            local b3 = high_16 % 256
            local b4 = (high_16 - b3) / 256
            prev_values = { b1, b2, b3, b4 }
        end
        return table.remove(prev_values)
    end

    return function(cipher, seed)
        state_45 = seed % 35184372088832
        state_8 = (seed % 255) + 2
        prev_values = {}
        local out = {}
        local prev = secret8
        for i = 1, #cipher do
            local b = string.byte(cipher, i)
            prev = (b + nextByte() + prev) % 256
            out[i] = chars[prev + 1]
        end
        return table.concat(out)
    end
end

-- Locate the decoder & friends in the AST.  Returns nil if not present.
local function locateDecoder(ast)
    local stringAliases = {}
    walk(ast, function(node)
        if node.kind == AstKind.AssignmentStatement
                and node.lhs and node.rhs and #node.lhs == #node.rhs then
            for i, lhs in ipairs(node.lhs) do
                local rhs = node.rhs[i]
                if isVar(rhs) and varName(rhs) == "string" then
                    local k = akey(lhs)
                    if k then stringAliases[k] = true end
                end
            end
        elseif node.kind == AstKind.LocalVariableDeclaration
                and node.expressions and node.ids then
            for i, rhs in ipairs(node.expressions) do
                if isVar(rhs) and varName(rhs) == "string" and node.ids[i] then
                    stringAliases[tostring(node.scope) .. "/" .. tostring(node.ids[i])] = true
                end
            end
        end
    end)

    -- Pass 1: extract LCG constants from anywhere in the AST.
    local mul45, add45, mul8
    walk(ast, function(node)
        if node.kind == AstKind.AssignmentStatement
                and node.rhs and #node.rhs == 1 then
            local m, a = extractLCG45(node.rhs[1])
            if m then mul45, add45 = m, a end
            local m8 = extractMul8(node.rhs[1])
            if m8 then mul8 = m8 end
        end
    end)
    if not (mul45 and add45 and mul8) then return nil end

    -- Pass 2: find the PRNG function and the public decoder function. Some
    -- builds split EncryptStrings into get_next_byte() and DECRYPT().
    local prngFnNode, decoderFnNode, prngKeys = nil, nil, {}
    walk(ast, function(node)
        if prngFnNode then return end
        if node.kind ~= AstKind.FunctionLiteralExpression
                and node.kind ~= AstKind.FunctionDeclaration
                and node.kind ~= AstKind.LocalFunctionDeclaration then
            return
        end
        local body = node.body
        if not body then return end
        local hasLCG45, hasMul8 = false, false
        walk(body, function(b)
            if b.kind == AstKind.AssignmentStatement
                    and b.rhs and #b.rhs == 1
                    and b.rhs[1].kind == AstKind.ModExpression
                    and asNumber(b.rhs[1].rhs) == 35184372088832 then
                hasLCG45 = true
            end
            if b.kind == AstKind.AssignmentStatement
                    and b.rhs and #b.rhs == 1
                    and b.rhs[1].kind == AstKind.ModExpression
                    and asNumber(b.rhs[1].rhs) == 257 then
                hasMul8 = true
            end
        end)
        if hasLCG45 and hasMul8 then
            prngFnNode = node
        end
    end)
    if prngFnNode then
        walk(ast, function(node)
            if node.kind == AstKind.AssignmentStatement
                    and node.lhs and #node.lhs == 1
                    and node.rhs and #node.rhs == 1
                    and node.rhs[1] == prngFnNode then
                local k = akey(node.lhs[1])
                if k then prngKeys[k] = true end
            elseif node.kind == AstKind.LocalVariableDeclaration
                    and node.expressions and #node.expressions == 1
                    and node.expressions[1] == prngFnNode
                    and node.ids and node.ids[1] then
                prngKeys[tostring(node.scope) .. "/" .. tostring(node.ids[1])] = true
            elseif node.kind == AstKind.LocalFunctionDeclaration and node == prngFnNode then
                if node.scope and node.id then
                    prngKeys[tostring(node.scope) .. "/" .. tostring(node.id)] = true
                end
            end
        end)
    end

    walk(ast, function(node)
        if decoderFnNode then return end
        if node.kind ~= AstKind.FunctionLiteralExpression
                and node.kind ~= AstKind.FunctionDeclaration
                and node.kind ~= AstKind.LocalFunctionDeclaration then
            return
        end
        local body = node.body
        if not body then return end
        local hasSeedAssign, hasStrByte, hasPrngCall = false, false, false
        walk(body, function(b)
            if b.kind == AstKind.AssignmentStatement
                    and b.rhs and #b.rhs == 1
                    and b.rhs[1].kind == AstKind.ModExpression
                    and asNumber(b.rhs[1].rhs) == 35184372088832 then
                hasSeedAssign = true
            end
            if isStringByteCall(b, stringAliases) then
                hasStrByte = true
            end
            if b.kind == AstKind.FunctionCallExpression
                    and b.base and b.base.kind == AstKind.IndexExpression
                    and asString(b.base.index) == "len" then
                local baseKey = nodeKey(b.base.base)
                if varName(b.base.base) == "string"
                        or (baseKey and stringAliases[baseKey]) then
                    hasStrByte = true
                end
            end
            if b.kind == AstKind.FunctionCallExpression and isVar(b.base) then
                local k = vkey(b.base)
                if k and prngKeys[k] then hasPrngCall = true end
            end
        end)
        if (hasSeedAssign or hasPrngCall) and hasStrByte then
            decoderFnNode = node
        end
    end)
    if not decoderFnNode then return nil end
    if prngFnNode and prngFnNode.body then
        walk(prngFnNode.body, function(n)
            if isVar(n) then
                local k = vkey(n)
                if k then prngKeys[k] = true end
            end
        end)
    end

    -- Pass 3: extract secret_key_8 - the initial accumulator value.
    -- Inside the decoder body, find the `... % 256` mod expression that
    -- represents the per-byte accumulator update; collect all variable refs
    -- in its LHS.  Among those, find a variable that is initialised with a
    -- small numeric constant (0..255).  That's the accumulator init value.
    local mod256Vars = {}
    walk(decoderFnNode.body, function(b)
        if b.kind == AstKind.ModExpression and asNumber(b.rhs) == 256 then
            -- Collect variable references inside b.lhs.
            walk(b.lhs, function(v)
                if isVar(v) then
                    local k = vkey(v)
                    if k and not prngKeys[k] then mod256Vars[k] = true end
                end
            end)
        end
    end)
    local secret8
    walk(decoderFnNode.body, function(n)
        if secret8 then return end
        if n.kind == AstKind.AssignmentStatement
                and n.lhs and #n.lhs == 1
                and n.rhs and #n.rhs == 1
                and n.rhs[1].kind == AstKind.NumberExpression then
            local num = n.rhs[1].value
            if num == math.floor(num) and num >= 0 and num <= 255 then
                local lhs = n.lhs[1]
                if lhs.kind == AstKind.AssignmentVariable then
                    local k = akey(lhs)
                    if k and mod256Vars[k] then secret8 = num end
                end
            end
        end
    end)
    if not secret8 then return nil end

    local setmetatableAliases = {}
    walk(ast, function(node)
        if node.kind == AstKind.AssignmentStatement
                and node.lhs and node.rhs and #node.lhs == #node.rhs then
            for i, lhs in ipairs(node.lhs) do
                local rhs = node.rhs[i]
                if isVar(rhs) and varName(rhs) == "setmetatable" then
                    local k = akey(lhs)
                    if k then setmetatableAliases[k] = true end
                end
            end
        elseif node.kind == AstKind.LocalVariableDeclaration
                and node.expressions and node.ids then
            for i, rhs in ipairs(node.expressions) do
                if isVar(rhs) and varName(rhs) == "setmetatable" and node.ids[i] then
                    setmetatableAliases[tostring(node.scope) .. "/" .. tostring(node.ids[i])] = true
                end
            end
        end
    end)

    -- Pass 4: find the proxy variable.  Look for an assignment whose RHS is
    -- `setmetatable({}, { __index = <var>, ... })`.  The LHS is the proxy.
    local proxyKey, cacheKey
    walk(ast, function(node)
        if proxyKey then return end
        if node.kind ~= AstKind.AssignmentStatement
                and node.kind ~= AstKind.LocalVariableDeclaration then
            return
        end
        local rhs
        if node.kind == AstKind.AssignmentStatement then
            if not (node.lhs and #node.lhs == 1 and node.rhs and #node.rhs == 1) then return end
            rhs = node.rhs[1]
        else
            if not (node.expressions and #node.expressions == 1) then return end
            rhs = node.expressions[1]
        end
        if rhs.kind ~= AstKind.FunctionCallExpression then return end
        if not (isVar(rhs.base)
                and (varName(rhs.base) == "setmetatable"
                    or (vkey(rhs.base) and setmetatableAliases[vkey(rhs.base)]))
                and #rhs.args == 2
                and rhs.args[1].kind == AstKind.TableConstructorExpression
                and rhs.args[2].kind == AstKind.TableConstructorExpression) then
            return
        end
        local indexVar
        for _, e in ipairs(rhs.args[2].entries) do
            if e.kind == AstKind.KeyedTableEntry
                    and asString(e.key) == "__index"
                    and isVar(e.value) then
                indexVar = e.value
                break
            end
        end
        if not indexVar then return end
        if node.kind == AstKind.AssignmentStatement then
            local lhs = node.lhs[1]
            if lhs.kind == AstKind.AssignmentVariable then
                proxyKey = akey(lhs)
                cacheKey = vkey(indexVar)
            end
        else
            -- LocalVariableDeclaration: lhs vars are listed in node.ids.
            -- (Prometheus AST: LocalVariableDeclaration has .scope + .ids.)
            if node.scope and node.ids and node.ids[1] then
                proxyKey = tostring(node.scope) .. "/" .. tostring(node.ids[1])
                cacheKey = vkey(indexVar)
            end
        end
    end)
    if not proxyKey then return nil end

    -- Pass 5: find the variables that hold the decoder function (and any
    -- direct aliases via `<v2> = <v1>` chains).
    local decoderKeys = {}
    walk(ast, function(node)
        if node.kind == AstKind.AssignmentStatement
                and node.lhs and #node.lhs == 1
                and node.rhs and #node.rhs == 1
                and node.rhs[1] == decoderFnNode then
            local lhs = node.lhs[1]
            local k = akey(lhs)
            if k then decoderKeys[k] = true end
        end
        if node.kind == AstKind.LocalVariableDeclaration
                and node.expressions and #node.expressions == 1
                and node.expressions[1] == decoderFnNode then
            if node.scope and node.ids and node.ids[1] then
                decoderKeys[tostring(node.scope) .. "/" .. tostring(node.ids[1])] = true
            end
        end
        if node.kind == AstKind.LocalFunctionDeclaration and node == decoderFnNode then
            if node.scope and node.id then
                decoderKeys[tostring(node.scope) .. "/" .. tostring(node.id)] = true
            end
        end
    end)
    -- Alias propagation: <newVar> = <decVar>.
    local progress = true
    while progress do
        progress = false
        walk(ast, function(node)
            if node.kind == AstKind.AssignmentStatement
                    and node.lhs and #node.lhs == 1
                    and node.rhs and #node.rhs == 1
                    and isVar(node.rhs[1]) then
                local rk = vkey(node.rhs[1])
                if rk and decoderKeys[rk] then
                    local lk = akey(node.lhs[1])
                    if lk and not decoderKeys[lk] then
                        decoderKeys[lk] = true
                        progress = true
                    end
                end
            end
        end)
    end

    -- Pass 6: collect "infra slot keys" -- the union of decoderKeys, proxyKey,
    -- cacheKey and any slot referenced inside the decoder function body.  This
    -- is used by stripInfra() to wipe dead aliases (`<reg> = <infraSlot>`).
    --
    -- Note: var refs inside the decoder body include parameters and locals
    -- whose scope is the decoder itself; those keys never coincide with
    -- top-level slot keys, so including them in this set is harmless.
    local infraKeys = {}
    for k in pairs(decoderKeys) do infraKeys[k] = true end
    if proxyKey then infraKeys[proxyKey] = true end
    if cacheKey then infraKeys[cacheKey] = true end
    walk(decoderFnNode.body, function(n)
        if isVar(n) then
            local k = vkey(n)
            if k then infraKeys[k] = true end
        end
    end)

    return {
        decoderFnNode = decoderFnNode,
        decoderKeys = decoderKeys,
        proxyKey = proxyKey,
        cacheKey = cacheKey,
        infraKeys = infraKeys,
        constants = { mul45 = mul45, add45 = add45, mul8 = mul8, secret8 = secret8 },
    }
end

-- Replace `proxy[decoder(c, s)]` with a string literal.
--
-- The decoder writes the plaintext into `cache[seed]` and returns `seed`,
-- and `proxy = setmetatable({}, {__index = cache})` makes `proxy[seed]`
-- yield the plaintext.  Because the decoder algorithm is deterministic and
-- the plaintext depends only on (cipher, seed), we can replace any
-- `<base>[<decoderAlias>(<string>, <number>)]` with the literal regardless
-- of which alias of the proxy is used as `<base>` (the obfuscator only
-- emits this shape with a real proxy alias).
local function replaceInline(ast, info, decoder)
    local count = 0
    astutil.transformExpressions(ast, function(node)
        if node.kind == AstKind.IndexExpression
                and node.index
                and node.index.kind == AstKind.FunctionCallExpression then
            local call = node.index
            if isVar(call.base) and call.args and #call.args == 2 then
                local ck = vkey(call.base)
                if ck and info.decoderKeys[ck] then
                    local cipher = asString(call.args[1])
                    local seed = asNumber(call.args[2])
                    if cipher and seed then
                        local ok, plain = pcall(decoder, cipher, seed)
                        if ok and plain then
                            count = count + 1
                            return Ast.StringExpression(plain)
                        end
                    end
                end
            end
        end
        return nil
    end)
    return count
end

-- Replace `<base>[<v>]` where `<v>` was assigned `<decoder>(c, s)` earlier in
-- the same straight-line block AND, in the same pass, eliminate dead stores
-- of decoder-call results and infrastructure-slot aliases.
--
-- Examples handled by this pass:
--
--   1) Deferred decoder lookup -- substitute the index:
--        r21 = loc_9("...", N);
--        r25 = r27[r21];          -- becomes r25 = "fromRGB"
--
--   2) Dead decoder-call store -- remove the call, plaintext was inlined:
--        r10 = loc_12("...", N);  -- removed (r10 never read before reassign)
--        r37 = r23.FindFirstChild;
--        if r37(r23, "ToraScript") then ...
--
--   3) Dead infrastructure-slot alias -- remove copies of decoder/proxy/cache:
--        r38 = loc_11;            -- removed (loc_11 is the proxy slot)
--        r10 = loc_12;            -- removed (loc_12 is the decoder slot)
--
-- A "straight-line" region is a flat run of statements within a single
-- block.  We pessimistically reset the maps upon hitting any structured
-- control flow (if / while / for / repeat / do) and recurse into the
-- nested bodies with their own fresh map state.  Function literal bodies
-- are also analysed independently.
local function replaceDeferred(ast, info, decoder)
    local count = 0
    local deadStores = 0

    -- Try to substitute a single IndexExpression node in place: the index
    -- is a VariableExpression whose key is in `map`.  Returns a new node
    -- on success, or nil to leave unchanged.
    local function maybeSubstitute(node, map)
        if node.kind ~= AstKind.IndexExpression then return nil end
        if not isVar(node.index) then return nil end
        local k = vkey(node.index)
        if k and map[k] then
            count = count + 1
            return Ast.StringExpression(map[k])
        end
        return nil
    end

    -- Walk an expression node, substituting in place.  We DO NOT descend
    -- into FunctionLiteralExpression bodies here -- those are independent
    -- straight-line regions handled separately.
    local rewriteExpr
    rewriteExpr = function(node, map)
        if type(node) ~= "table" then return node end
        if node.kind == AstKind.FunctionLiteralExpression then
            return node
        end

        local repl = maybeSubstitute(node, map)
        if repl then return repl end

        for k, v in pairs(node) do
            if k ~= "kind" and k ~= "scope" and k ~= "parentScope"
                    and k ~= "baseScope" then
                if type(v) == "table" then
                    if v.kind then
                        node[k] = rewriteExpr(v, map)
                    else
                        for i, vv in ipairs(v) do
                            if type(vv) == "table" and vv.kind then
                                v[i] = rewriteExpr(vv, map)
                            end
                        end
                    end
                end
            end
        end
        return node
    end

    -- Detect whether `expr` is a decoder call literal `<decAlias>(<str>, <num>)`.
    local function decoderCallPlaintext(expr)
        if not expr then return nil end
        if expr.kind ~= AstKind.FunctionCallExpression then return nil end
        if not isVar(expr.base) then return nil end
        local k = vkey(expr.base)
        if not (k and info.decoderKeys[k]) then return nil end
        if not (expr.args and #expr.args == 2) then return nil end
        local cipher = asString(expr.args[1])
        local seed = asNumber(expr.args[2])
        if not (cipher and seed) then return nil end
        local ok, plain = pcall(decoder, cipher, seed)
        if not ok then return nil end
        return plain
    end

    -- Walk a Block (list of statements), maintaining a per-block map of
    -- live decoder-output variable bindings.
    local processBlock
    local function findFunctionLiterals(node, found)
        if type(node) ~= "table" then return end
        if node.kind == AstKind.FunctionLiteralExpression then
            table.insert(found, node)
            return
        end
        for k, v in pairs(node) do
            if k ~= "kind" and k ~= "scope" and k ~= "parentScope"
                    and k ~= "baseScope" then
                if type(v) == "table" then
                    if v.kind then
                        findFunctionLiterals(v, found)
                    else
                        for _, vv in ipairs(v) do
                            if type(vv) == "table" and vv.kind then
                                findFunctionLiterals(vv, found)
                            end
                        end
                    end
                end
            end
        end
    end

    -- Collect all VariableExpression var keys reachable from a node, NOT
    -- descending into nested function literals (their captures don't read
    -- through this block's bindings).  Iterative to handle the very deep
    -- expression trees produced by obfuscated code.
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

    -- Decide whether `<v> = <rhs>` is a candidate dead store.  Returns a
    -- truthy "candidate kind" string ("decoder_call" / "infra_alias") if
    -- this assignment can be safely removed when `<v>` is dead, otherwise
    -- nil.  Only the candidate kinds we recognise are eligible -- any other
    -- shape leaves the assignment alone.
    local function deadStoreKind(rhs)
        if not rhs then return nil end
        if decoderCallPlaintext(rhs) then return "decoder_call" end
        if isVar(rhs) then
            local rk = vkey(rhs)
            if rk and info.infraKeys and info.infraKeys[rk] then
                return "infra_alias"
            end
        end
        return nil
    end

    -- Single-LHS plain-variable assignment helper.
    local function singleVarLhs(stmt)
        if stmt.kind ~= AstKind.AssignmentStatement then return nil end
        if not (stmt.lhs and #stmt.lhs == 1) then return nil end
        if not (stmt.rhs and #stmt.rhs == 1) then return nil end
        if stmt.lhs[1].kind ~= AstKind.AssignmentVariable then return nil end
        return akey(stmt.lhs[1]), stmt.rhs[1]
    end

    processBlock = function(block)
        if not block or block.kind ~= AstKind.Block or not block.statements then
            return
        end
        -- substMap[varKey] = plaintext  (for index substitution)
        -- candIdx[varKey] = stmtIndex   (dead-store candidate position)
        local substMap = {}
        local candIdx = {}
        local removeIdx = {}

        local function consumeReads(stmt)
            local reads = {}
            if stmt.kind == AstKind.AssignmentStatement then
                if stmt.rhs then for _, e in ipairs(stmt.rhs) do collectReads(e, reads) end end
                -- LHS reads: only if LHS is an indexed assignment, the base
                -- and index are both reads.
                if stmt.lhs then
                    for _, lhs in ipairs(stmt.lhs) do
                        if lhs.kind == AstKind.AssignmentIndexing then
                            collectReads(lhs.base, reads)
                            collectReads(lhs.index, reads)
                        end
                    end
                end
            elseif stmt.kind == AstKind.LocalVariableDeclaration then
                if stmt.expressions then
                    for _, e in ipairs(stmt.expressions) do collectReads(e, reads) end
                end
            elseif stmt.kind == AstKind.FunctionCallStatement
                    or stmt.kind == AstKind.PassSelfFunctionCallStatement then
                collectReads(stmt.base, reads)
                if stmt.args then for _, a in ipairs(stmt.args) do collectReads(a, reads) end end
            elseif stmt.kind == AstKind.ReturnStatement then
                if stmt.args then for _, a in ipairs(stmt.args) do collectReads(a, reads) end end
            elseif stmt.kind == AstKind.IfStatement then
                collectReads(stmt.condition, reads)
            elseif stmt.kind == AstKind.WhileStatement
                    or stmt.kind == AstKind.RepeatStatement then
                collectReads(stmt.condition, reads)
            elseif stmt.kind == AstKind.ForStatement then
                collectReads(stmt.initialValue, reads)
                collectReads(stmt.finalValue, reads)
                collectReads(stmt.incrementBy, reads)
            elseif stmt.kind == AstKind.ForInStatement then
                if stmt.expressions then
                    for _, e in ipairs(stmt.expressions) do collectReads(e, reads) end
                end
            end
            for k, _ in pairs(reads) do
                if candIdx[k] then
                    -- The candidate's value is consumed by this read -- it's
                    -- live, drop the dead-store candidacy.
                    candIdx[k] = nil
                end
            end
        end

        for stmtIdx, stmt in ipairs(block.statements) do
            local k = stmt.kind

            -- 1) Substitute uses of live decoder-output vars in this stmt's
            --    expressions (without descending into nested function
            --    literals or nested blocks).
            if k == AstKind.AssignmentStatement then
                if stmt.rhs then
                    for i, e in ipairs(stmt.rhs) do
                        stmt.rhs[i] = rewriteExpr(e, substMap)
                    end
                end
                if stmt.lhs then
                    for i, e in ipairs(stmt.lhs) do
                        stmt.lhs[i] = rewriteExpr(e, substMap)
                    end
                end
            elseif k == AstKind.LocalVariableDeclaration then
                if stmt.expressions then
                    for i, e in ipairs(stmt.expressions) do
                        stmt.expressions[i] = rewriteExpr(e, substMap)
                    end
                end
            elseif k == AstKind.FunctionCallStatement
                    or k == AstKind.PassSelfFunctionCallStatement then
                stmt.base = rewriteExpr(stmt.base, substMap)
                if stmt.args then
                    for i, a in ipairs(stmt.args) do
                        stmt.args[i] = rewriteExpr(a, substMap)
                    end
                end
            elseif k == AstKind.ReturnStatement then
                if stmt.args then
                    for i, a in ipairs(stmt.args) do
                        stmt.args[i] = rewriteExpr(a, substMap)
                    end
                end
            elseif k == AstKind.IfStatement then
                stmt.condition = rewriteExpr(stmt.condition, substMap)
            elseif k == AstKind.WhileStatement
                    or k == AstKind.RepeatStatement then
                stmt.condition = rewriteExpr(stmt.condition, substMap)
            elseif k == AstKind.ForStatement then
                stmt.initialValue = rewriteExpr(stmt.initialValue, substMap)
                stmt.finalValue = rewriteExpr(stmt.finalValue, substMap)
                stmt.incrementBy = rewriteExpr(stmt.incrementBy, substMap)
            elseif k == AstKind.ForInStatement then
                if stmt.expressions then
                    for i, e in ipairs(stmt.expressions) do
                        stmt.expressions[i] = rewriteExpr(e, substMap)
                    end
                end
            end

            -- 1.5) Account for reads -- live candidates get retained.
            consumeReads(stmt)

            -- 2) Recurse into any nested function literals appearing in
            --    this statement's expressions.
            local lits = {}
            if k == AstKind.AssignmentStatement then
                if stmt.rhs then for _, e in ipairs(stmt.rhs) do findFunctionLiterals(e, lits) end end
            elseif k == AstKind.LocalVariableDeclaration then
                if stmt.expressions then for _, e in ipairs(stmt.expressions) do findFunctionLiterals(e, lits) end end
            elseif k == AstKind.FunctionCallStatement
                    or k == AstKind.PassSelfFunctionCallStatement then
                findFunctionLiterals(stmt.base, lits)
                if stmt.args then for _, a in ipairs(stmt.args) do findFunctionLiterals(a, lits) end end
            elseif k == AstKind.ReturnStatement then
                if stmt.args then for _, a in ipairs(stmt.args) do findFunctionLiterals(a, lits) end end
            end
            for _, lit in ipairs(lits) do
                processBlock(lit.body)
            end

            -- 3) Recurse into nested statement blocks.  Before recursing,
            --    inspect what variables the nested body reads or writes:
            --    - reads  -> consume any matching candidate (live).
            --    - writes -> drop the candidacy (we don't know if dead).
            --    Substitutions across a nested block boundary are unsafe so
            --    `substMap` is always cleared.
            local hasNestedBlock = false
            if k == AstKind.IfStatement
                    or k == AstKind.WhileStatement
                    or k == AstKind.RepeatStatement
                    or k == AstKind.DoStatement
                    or k == AstKind.ForStatement
                    or k == AstKind.ForInStatement
                    or k == AstKind.FunctionDeclaration
                    or k == AstKind.LocalFunctionDeclaration then
                hasNestedBlock = true
            end
            if hasNestedBlock then
                local nestedReads, nestedWrites = {}, {}
                local function scanBlock(b)
                    if not b or not b.statements then return end
                    for _, s2 in ipairs(b.statements) do
                        collectReads(s2, nestedReads)
                        if s2.kind == AstKind.AssignmentStatement and s2.lhs then
                            for _, lhs in ipairs(s2.lhs) do
                                local lhsKey = akey(lhs)
                                if lhsKey then nestedWrites[lhsKey] = true end
                            end
                        end
                    end
                end
                scanBlock(stmt.body)
                if k == AstKind.IfStatement then
                    if stmt.elseifs then
                        for _, ei in ipairs(stmt.elseifs) do scanBlock(ei.body) end
                    end
                    if stmt.elsebody then scanBlock(stmt.elsebody) end
                end
                for vk in pairs(nestedReads) do
                    candIdx[vk] = nil
                end
                for vk in pairs(nestedWrites) do
                    candIdx[vk] = nil
                end
                substMap = {}
            end
            if k == AstKind.IfStatement then
                processBlock(stmt.body)
                if stmt.elseifs then
                    for _, ei in ipairs(stmt.elseifs) do
                        processBlock(ei.body)
                    end
                end
                if stmt.elsebody then processBlock(stmt.elsebody) end
            elseif k == AstKind.WhileStatement
                    or k == AstKind.RepeatStatement
                    or k == AstKind.DoStatement
                    or k == AstKind.ForStatement
                    or k == AstKind.ForInStatement then
                processBlock(stmt.body)
            elseif k == AstKind.FunctionDeclaration
                    or k == AstKind.LocalFunctionDeclaration then
                processBlock(stmt.body)
            end

            -- 4) Update maps based on this stmt's effects.
            local lk, rhs = singleVarLhs(stmt)
            if lk then
                -- Reassignment of `lk`: any pending dead-store candidate for
                -- it is now confirmed dead (no read between def and reassign).
                if candIdx[lk] then
                    removeIdx[candIdx[lk]] = true
                    candIdx[lk] = nil
                end
                -- Update substitution map: decoder-call result is plaintext.
                local plain = decoderCallPlaintext(rhs)
                if plain then
                    substMap[lk] = plain
                else
                    substMap[lk] = nil
                end
                -- Register a new dead-store candidate if this RHS is a
                -- recognised pattern (decoder call result, infra-slot alias).
                if deadStoreKind(rhs) then
                    candIdx[lk] = stmtIdx
                end
            elseif k == AstKind.AssignmentStatement and stmt.lhs then
                -- Multi-target / index targets: invalidate any plain var LHS.
                for _, lhs in ipairs(stmt.lhs) do
                    local lhsKey = akey(lhs)
                    if lhsKey then
                        if candIdx[lhsKey] then
                            removeIdx[candIdx[lhsKey]] = true
                            candIdx[lhsKey] = nil
                        end
                        substMap[lhsKey] = nil
                    end
                end
            elseif k == AstKind.LocalVariableDeclaration then
                -- New locals: cannot collide with existing candidates.
            end
        end

        -- End-of-block: any remaining dead-store candidates were never
        -- read.  Mark for removal.
        for _, idx in pairs(candIdx) do
            removeIdx[idx] = true
        end

        -- Apply removals.
        if next(removeIdx) ~= nil then
            local kept = {}
            for i, s in ipairs(block.statements) do
                if not removeIdx[i] then
                    kept[#kept + 1] = s
                else
                    deadStores = deadStores + 1
                end
            end
            block.statements = kept
        end
    end

    if ast.kind == AstKind.TopNode then
        processBlock(ast.body)
    elseif ast.kind == AstKind.Block then
        processBlock(ast)
    end
    return count, deadStores
end

-- Global next-use analysis for dead-store elimination of patterns the
-- per-block forward pass could not resolve (e.g. when the candidate var
-- is reassigned inside a nested branch but is never read between).  We
-- look at each function-scope independently: for every remaining
-- `<reg> = <decoderCall>(c, s)` or `<reg> = <infraSlot>` assignment, we
-- scan the rest of that function in source order for the first "use" of
-- the register.  If that first use is a WRITE (or we never observe a
-- read before exiting the function), the candidate is dead.
local function stripCrossBlockDead(ast, info, decoder)
    local removed = 0

    -- Detect `<reg> = <RHS>` candidate; returns true if RHS is recognised.
    local function isCandidateRhs(rhs)
        if not rhs then return false end
        if rhs.kind == AstKind.FunctionCallExpression
                and isVar(rhs.base)
                and rhs.args and #rhs.args == 2
                and rhs.args[1].kind == AstKind.StringExpression
                and rhs.args[2].kind == AstKind.NumberExpression then
            local k = vkey(rhs.base)
            if k and info.decoderKeys[k] then
                local cipher = asString(rhs.args[1])
                local seed   = asNumber(rhs.args[2])
                if cipher and seed then
                    local ok, plain = pcall(decoder, cipher, seed)
                    if ok and plain then return true end
                end
            end
        end
        if isVar(rhs) then
            local rk = vkey(rhs)
            if rk and info.infraKeys and info.infraKeys[rk] then return true end
        end
        return false
    end

    -- "use" detection across an arbitrary node, NOT entering function
    -- literals.  Returns "read" if we find a VariableExpression matching
    -- varKey first, "write" if we find an AssignmentVariable matching
    -- first, or "neutral" if neither encountered.
    --
    -- For an AssignmentStatement, RHS is fully evaluated before LHS, so
    -- read-in-RHS wins over write-in-LHS.
    -- Iterative variant -- expression trees can be very deep in
    -- obfuscated code (chained ((((a + b) + c) + d) ...)), so a recursive
    -- walker easily blows past Lua's default ~200-deep stack.
    local checkStmt
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
                if n.kind ~= AstKind.FunctionLiteralExpression then
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
                            and akey(lhs) == varKey then
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
            -- Aggregate across branches: any "read" wins; "write" only if
            -- ALL branches confirm AND there's an else (otherwise the
            -- missing branch is "neutral" by default).
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
        elseif k == AstKind.WhileStatement
                or k == AstKind.RepeatStatement then
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
            local r = nextUseInBlock(stmt.body, 1, varKey)
            return r
        elseif k == AstKind.FunctionDeclaration
                or k == AstKind.LocalFunctionDeclaration then
            -- Captured slots may be read inside; pessimistically check.
            if findReadInRoot(stmt.body, varKey) then return "read" end
            return "neutral"
        end
        return "neutral"
    end

    -- Walk every function-scope (top-level + each FunctionLiteral body)
    -- and process its blocks for dead-store removal.
    local processFunction
    processFunction = function(funcBody)
        if not funcBody or funcBody.kind ~= AstKind.Block
                or not funcBody.statements then
            return
        end
        local function processBlock(block, parentBlocks)
            if not block or not block.statements then return end
            local removeIdx = {}
            for i, stmt in ipairs(block.statements) do
                if stmt.kind == AstKind.AssignmentStatement
                        and stmt.lhs and #stmt.lhs == 1
                        and stmt.rhs and #stmt.rhs == 1
                        and stmt.lhs[1].kind == AstKind.AssignmentVariable then
                    local lk = akey(stmt.lhs[1])
                    -- NOTE: we intentionally do NOT filter on
                    -- info.infraKeys[lk] here.  A register that ELSEWHERE
                    -- holds the decoder (e.g. `r10 = loc_12` somewhere
                    -- else in the function) is still a valid dead-store
                    -- target at this site if isCandidateRhs() recognises
                    -- *this* RHS and the next-use analysis below proves
                    -- the value is unused.  The canonical infra
                    -- definitions (`loc_12 = r15`, `loc_11 = setmetatable
                    -- (...)`, the decoder function literal itself) do
                    -- NOT match isCandidateRhs(), so they are never
                    -- considered for removal.
                    if lk and isCandidateRhs(stmt.rhs[1]) then
                        -- Check next-use globally within this function:
                        --   start at this block's i+1, then propagate to
                        --   parent blocks' continuations.
                        local result = nextUseInBlock(block, i + 1, lk)
                        local pidx = #parentBlocks
                        while result == "neutral" and pidx > 0 do
                            local pb = parentBlocks[pidx]
                            result = nextUseInBlock(pb.block, pb.idx + 1, lk)
                            pidx = pidx - 1
                        end
                        if result == "write" or result == "neutral" then
                            removeIdx[i] = true
                        end
                    end
                end
                -- Recurse into nested blocks (sharing parent stack).
                local k = stmt.kind
                local nestedParents = {}
                for _, p in ipairs(parentBlocks) do
                    nestedParents[#nestedParents + 1] = p
                end
                nestedParents[#nestedParents + 1] = { block = block, idx = i }
                if k == AstKind.IfStatement then
                    processBlock(stmt.body, nestedParents)
                    if stmt.elseifs then
                        for _, ei in ipairs(stmt.elseifs) do
                            processBlock(ei.body, nestedParents)
                        end
                    end
                    if stmt.elsebody then
                        processBlock(stmt.elsebody, nestedParents)
                    end
                elseif k == AstKind.WhileStatement
                        or k == AstKind.RepeatStatement
                        or k == AstKind.DoStatement
                        or k == AstKind.ForStatement
                        or k == AstKind.ForInStatement then
                    processBlock(stmt.body, nestedParents)
                end
                -- Recurse into nested function literal bodies (with a
                -- FRESH parent stack -- registers don't leak).
                local lits = {}
                local function findLits(node)
                    if type(node) ~= "table" then return end
                    if node.kind == AstKind.FunctionLiteralExpression then
                        table.insert(lits, node); return
                    end
                    for kk, v in pairs(node) do
                        if kk ~= "kind" and kk ~= "scope" and kk ~= "parentScope"
                                and kk ~= "baseScope" then
                            if type(v) == "table" then
                                if v.kind then findLits(v)
                                else
                                    for _, vv in ipairs(v) do
                                        if type(vv) == "table" and vv.kind then
                                            findLits(vv)
                                        end
                                    end
                                end
                            end
                        end
                    end
                end
                if k == AstKind.AssignmentStatement then
                    if stmt.rhs then for _, e in ipairs(stmt.rhs) do findLits(e) end end
                elseif k == AstKind.LocalVariableDeclaration then
                    if stmt.expressions then for _, e in ipairs(stmt.expressions) do findLits(e) end end
                elseif k == AstKind.FunctionCallStatement
                        or k == AstKind.PassSelfFunctionCallStatement then
                    findLits(stmt.base)
                    if stmt.args then for _, a in ipairs(stmt.args) do findLits(a) end end
                elseif k == AstKind.ReturnStatement then
                    if stmt.args then for _, a in ipairs(stmt.args) do findLits(a) end end
                end
                for _, lit in ipairs(lits) do
                    processFunction(lit.body)
                end
            end
            if next(removeIdx) ~= nil then
                local kept = {}
                for i, s in ipairs(block.statements) do
                    if not removeIdx[i] then kept[#kept + 1] = s
                    else removed = removed + 1 end
                end
                block.statements = kept
            end
        end
        processBlock(funcBody, {})
    end

    if ast.kind == AstKind.TopNode then
        processFunction(ast.body)
    elseif ast.kind == AstKind.Block then
        processFunction(ast)
    end
    return removed
end

local function replaceCalls(ast, info)
    local decoder = makeDecoder(
        info.constants.mul45, info.constants.add45,
        info.constants.mul8,  info.constants.secret8)
    local n1 = replaceInline(ast, info, decoder)
    local n2, deadStores = replaceDeferred(ast, info, decoder)
    local n3 = stripCrossBlockDead(ast, info, decoder)
    return n1, n2, deadStores + n3
end

-- Cache of decoder-identification results keyed by AST root.  Populated
-- on `apply`; consumed by strip_vm_infra (which runs later in the
-- pipeline, after `apply` has mutated the decoder skeleton, so a fresh
-- `locateDecoder` call would no longer find the structural match).
local astInfoCache = setmetatable({}, { __mode = "k" })

-- Exposed for strip_vm_infra: returns the decoder identification result
-- captured during `apply`, or nil if `apply` didn't find a decoder.
function M.cachedInfo(ast)
    return astInfoCache[ast]
end

function M.apply(ast)
    local info = locateDecoder(ast)
    if not info then
        return { note = "no in-VM decoder found (skipped)" }
    end
    astInfoCache[ast] = info
    local n1, n2, deadStores = replaceCalls(ast, info)
    return {
        note = ("decrypted " .. tostring(n1 + n2) .. " string(s) ("
            .. tostring(n1) .. " inline + " .. tostring(n2) .. " deferred), "
            .. "removed " .. tostring(deadStores) .. " dead infra store(s)"
            .. " (mul45=" .. tostring(info.constants.mul45)
            .. ", add45=" .. tostring(info.constants.add45)
            .. ", mul8=" .. tostring(info.constants.mul8)
            .. ", k8=" .. tostring(info.constants.secret8) .. ")"),
    }
end

return M
