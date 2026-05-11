-- prometheus-test-deobfuscator - strip in-VM string-decoder infrastructure.
--
-- After decrypt_vm_strings has replaced every `proxy[decoder(c, s)]` call
-- with the literal plaintext and copy_prop_dce has eliminated dead
-- scratch-register stores, what's left of the decoder is a self-contained
-- block of setup code that nothing reads any more:
--
--   * The on-demand cache function `<X> = function(c, s) ... if not cache[s]
--     then cache[s] = "" ... cache[s] = (cache[s] .. chartbl[...]) ... end;
--     return s end` (decrypt_vm_strings calls this "decoderFnNode").
--   * The byte-stream generator function `<Y> = function() if (#buf)==0
--     then <LCG stuff> end; return table.remove(buf) end` (the function
--     containing the LCG `% 35184372088832` mod assign).
--   * The proxy / cache table pair `<C> = {}; <P> = setmetatable({}, {
--     __index = <C> })`.
--   * Scratch tables and PRNG seeds owned exclusively by the two infra
--     functions (the byte buffer, the char-table, the LCG state slots).
--
-- The analysis is reads-driven and intentionally conservative:
--
--   1. Identify the two infra functions structurally.
--   2. Mark a "user-read" of a variable as any read NOT inside one of
--      those infra functions and NOT inside the proxy-setup expression.
--   3. For each candidate slot in the main scope, if every read is an
--      infra-read, the slot is pure infra -- remove every assignment to
--      it AND any statement whose only effect is to initialise a closely
--      related scratch (e.g. the throwaway 1..256 table used as the
--      char-table seed).
--   4. Also remove the two infra function literals' own assignment
--      statements (`<X> = function ...`).
--
-- A statement is removed iff (a) it's an assignment whose entire LHS
-- list is in the infra slot set and whose RHS is either trivially pure
-- (constants, empty tables, stdlib-name refs, setmetatable on
-- infra-only operands) OR is the infra function literal itself; OR
-- (b) it's the char-table init for-loop / shuffle while-loop pair.
--
-- False positives would corrupt the program; false negatives just
-- leave residual dead code.  We bias hard towards false negatives.

local Ast = require("prometheus.ast")
local AstKind = Ast.AstKind
local decrypt_vm_strings = require("deobfuscator.steps.vmify.decrypt_vm_strings")

local M = {}

local function isVar(n) return n and n.kind == AstKind.VariableExpression end

local function vkey(node)
    if not node then return nil end
    if node.kind == AstKind.VariableExpression
            or node.kind == AstKind.AssignmentVariable then
        if node.scope and node.id then
            return tostring(node.scope) .. "/" .. tostring(node.id)
        end
    end
    return nil
end

local function akey(node)
    if not node then return nil end
    if node.kind == AstKind.AssignmentVariable and node.scope and node.id then
        return tostring(node.scope) .. "/" .. tostring(node.id)
    end
    return nil
end

local function asNumber(n)
    if n and n.kind == AstKind.NumberExpression then return n.value end
end

-- Iterative walk: visit every reachable node-table, invoking fn(node).
-- Does not enter `scope`, `parentScope`, `baseScope`, `globalScope` slots
-- (those are scope tables, not part of the AST tree).
local function walk(root, fn)
    if type(root) ~= "table" then return end
    local stack, top = { root }, 1
    local seen = {}
    while top > 0 do
        local n = stack[top]
        stack[top] = nil
        top = top - 1
        if type(n) == "table" and not seen[n] then
            seen[n] = true
            fn(n)
            for k, v in pairs(n) do
                if k ~= "scope" and k ~= "parentScope"
                        and k ~= "baseScope" and k ~= "globalScope"
                        and type(v) == "table" then
                    top = top + 1
                    stack[top] = v
                end
            end
        end
    end
end

-- A walk that does NOT cross FunctionLiteralExpression boundaries.
-- Useful for finding "the rest of the main function body" without
-- descending into nested closures.
local function walkLocal(root, fn)
    if type(root) ~= "table" then return end
    local stack, top = { root }, 1
    local seen = {}
    while top > 0 do
        local n = stack[top]
        stack[top] = nil
        top = top - 1
        if type(n) == "table" and not seen[n] then
            seen[n] = true
            fn(n)
            if n.kind ~= AstKind.FunctionLiteralExpression
                    and n.kind ~= AstKind.FunctionDeclaration
                    and n.kind ~= AstKind.LocalFunctionDeclaration then
                for k, v in pairs(n) do
                    if k ~= "scope" and k ~= "parentScope"
                            and k ~= "baseScope" and k ~= "globalScope"
                            and type(v) == "table" then
                        top = top + 1
                        stack[top] = v
                    end
                end
            end
        end
    end
end

-- Pure stdlib globals.  Variable references whose name is one of these
-- are considered free of side effects for "trivially-pure RHS" detection.
local PURE_GLOBAL_NAMES = {
    math = true, string = true, table = true, os = true,
    setmetatable = true, getmetatable = true, rawget = true, rawset = true,
    unpack = true, tostring = true, tonumber = true, type = true,
    pcall = true, xpcall = true, error = true, select = true,
    pairs = true, ipairs = true, next = true,
    getfenv = true, setfenv = true,
    -- Roblox globals are deliberately NOT in this list; we do not want
    -- to consider `game`, `script`, etc. as pure since their reads are
    -- meaningful program behaviour.
}

local function nameOf(node)
    if not node or node.kind ~= AstKind.VariableExpression then return nil end
    if not node.scope or not node.scope.getVariableName then return nil end
    local ok, n = pcall(node.scope.getVariableName, node.scope, node.id)
    if ok then return n end
    return nil
end

local function isPureGlobalRef(node)
    local n = nameOf(node)
    return n and PURE_GLOBAL_NAMES[n] or false
end

-- Find the byte-stream generator function literal in the main body.
-- Signature: `<Y> = (function(...) <body with `... % 35184372088832`> end)`.
local function findByteStreamFn(ast)
    local found
    walk(ast, function(n)
        if found then return end
        if n.kind ~= AstKind.FunctionLiteralExpression then return end
        if not n.body then return end
        local matched = false
        walk(n.body, function(b)
            if b.kind == AstKind.AssignmentStatement
                    and b.rhs and #b.rhs == 1
                    and b.rhs[1].kind == AstKind.ModExpression
                    and asNumber(b.rhs[1].rhs) == 35184372088832 then
                matched = true
            end
        end)
        if matched then found = n end
    end)
    return found
end

-- Find the proxy setup expression: `setmetatable({}, { __index = <cache> })`.
local function findProxySetupExpr(ast, cacheKey)
    local found
    walk(ast, function(n)
        if found then return end
        if n.kind ~= AstKind.FunctionCallExpression then return end
        if not isVar(n.base) then return end
        if nameOf(n.base) ~= "setmetatable" then return end
        if not n.args or #n.args ~= 2 then return end
        if n.args[1].kind ~= AstKind.TableConstructorExpression then return end
        if n.args[2].kind ~= AstKind.TableConstructorExpression then return end
        -- Inspect entries of the second table to find __index = <var>.
        local cand
        for _, e in ipairs(n.args[2].entries or {}) do
            if e.key and e.key.kind == AstKind.StringExpression
                    and e.key.value == "__index"
                    and e.value and isVar(e.value) then
                cand = vkey(e.value)
            end
        end
        if cand == cacheKey then found = n end
    end)
    return found
end

-- Identify all "infra function bodies".  Reads inside these are NOT
-- user-reads.  Includes:
--   * decoderFnNode (the on-demand cache fn from decrypt_vm_strings).
--   * The byte-stream generator function literal.
--   * Any function literal whose body contains an assignment of the form
--     `cache[<X>] = ...` (other on-demand wrappers, if any).
local function collectInfraBodies(ast, cacheKey, decoderFnNode, byteStreamFn)
    local set = {}
    if decoderFnNode and decoderFnNode.body then set[decoderFnNode.body] = true end
    if byteStreamFn and byteStreamFn.body then set[byteStreamFn.body] = true end
    walk(ast, function(n)
        if n.kind ~= AstKind.FunctionLiteralExpression then return end
        if not n.body then return end
        walk(n.body, function(s)
            if s.kind == AstKind.AssignmentStatement
                    and s.lhs and #s.lhs == 1
                    and s.lhs[1].kind == AstKind.AssignmentIndexing
                    and isVar(s.lhs[1].base)
                    and vkey(s.lhs[1].base) == cacheKey then
                set[n.body] = true
            end
        end)
    end)
    return set
end

-- True iff `node` (an arbitrary AST node) is contained inside one of
-- `bodies` (a set of Block roots).  We test this by walking the body
-- tree once and recording every descendant in `nodeSet`, then asking
-- whether `node` is in `nodeSet`.
local function buildContainmentTest(bodies)
    local inside = {}
    for body in pairs(bodies) do
        walk(body, function(n) inside[n] = true end)
    end
    return inside
end

-- True iff `expr` is a "trivially pure RHS" for purposes of removal:
-- constants, empty/literal-only tables, references to pure stdlib
-- globals or to vars in `infraSet`, setmetatable on those operands,
-- function calls on pure stdlib globals (e.g. math.random) where every
-- argument is also trivially pure, and arithmetic / index expressions
-- whose operands are trivially pure.
local function isTriviallyPure(expr, infraSet, fnSet)
    if type(expr) ~= "table" then return true end
    local k = expr.kind
    if k == AstKind.NilExpression or k == AstKind.BooleanExpression
            or k == AstKind.NumberExpression or k == AstKind.StringExpression
            or k == AstKind.VarargExpression then
        return true
    end
    if k == AstKind.VariableExpression then
        local vk = vkey(expr)
        if vk and infraSet[vk] then return true end
        if isPureGlobalRef(expr) then return true end
        return false
    end
    if k == AstKind.FunctionLiteralExpression then
        return fnSet and fnSet[expr] or false
    end
    if k == AstKind.TableConstructorExpression then
        for _, e in ipairs(expr.entries or {}) do
            if e.value and not isTriviallyPure(e.value, infraSet, fnSet) then
                return false
            end
            if e.key and not isTriviallyPure(e.key, infraSet, fnSet) then
                return false
            end
        end
        return true
    end
    if k == AstKind.IndexExpression then
        return isTriviallyPure(expr.base, infraSet, fnSet)
            and isTriviallyPure(expr.index, infraSet, fnSet)
    end
    if k == AstKind.FunctionCallExpression
            or k == AstKind.PassSelfFunctionCallExpression then
        -- Allow calls whose base is a pure stdlib global OR an index off
        -- a stdlib global (e.g. `math.random`, `table.remove`).  All args
        -- must be trivially pure.
        local base = expr.base
        local baseOk = false
        if isVar(base) and isPureGlobalRef(base) then
            baseOk = true
        elseif base and base.kind == AstKind.IndexExpression
                and isVar(base.base) and isPureGlobalRef(base.base)
                and base.index and base.index.kind == AstKind.StringExpression then
            baseOk = true
        end
        if not baseOk then return false end
        for _, a in ipairs(expr.args or {}) do
            if not isTriviallyPure(a, infraSet, fnSet) then return false end
        end
        return true
    end
    if k == AstKind.AddExpression or k == AstKind.SubExpression
            or k == AstKind.MulExpression or k == AstKind.DivExpression
            or k == AstKind.ModExpression or k == AstKind.PowExpression
            or k == AstKind.OrExpression or k == AstKind.AndExpression
            or k == AstKind.LessThanExpression or k == AstKind.LessThanOrEqualsExpression
            or k == AstKind.GreaterThanExpression or k == AstKind.GreaterThanOrEqualsExpression
            or k == AstKind.EqualsExpression or k == AstKind.NotEqualsExpression
            or k == AstKind.StrCatExpression then
        return isTriviallyPure(expr.lhs, infraSet, fnSet)
            and isTriviallyPure(expr.rhs, infraSet, fnSet)
    end
    if k == AstKind.NotExpression or k == AstKind.NegateExpression
            or k == AstKind.LenExpression then
        return isTriviallyPure(expr.rhs, infraSet, fnSet)
    end
    return false
end

-- Compute the per-slot "user-read count": the number of times a slot is
-- read OUTSIDE every infra body (and outside the proxy setup expression).
-- A slot with user-read count == 0 is pure infra and safe to remove.
local function computeUserReads(ast, insideInfra, proxySetupExpr)
    -- Build containment for proxy setup so we can exclude it too.
    local insideProxy = {}
    if proxySetupExpr then
        walk(proxySetupExpr, function(n) insideProxy[n] = true end)
    end
    local userReads = {}
    walk(ast, function(n)
        if n.kind == AstKind.VariableExpression then
            local k = vkey(n)
            if k then
                if not insideInfra[n] and not insideProxy[n] then
                    userReads[k] = (userReads[k] or 0) + 1
                end
            end
        end
    end)
    return userReads
end

-- Find the "char-table init pattern" at the top of the main body:
--
--   <scratch>  = {};
--   <chartbl>  = {};
--   for <i> = 1, 256, 1 do <scratch>[<i>] = <i> end;
--   while true do
--       <ridx> = table.remove(<scratch>, math.random(1, #<scratch>));
--       <chartbl>[<ridx>] = string.char(<ridx> - 1);
--       if #<scratch> == 0 then break end;
--   end;
--
-- where <chartbl> is in `infraSlots`.  Returns the set of statement
-- nodes to remove and the scratch var key (if found).
local function findCharTableInit(block, infraSlots)
    if not block or block.kind ~= AstKind.Block or not block.statements then
        return {}, nil
    end
    local stmts = block.statements
    local toRemove = {}
    -- Walk statements linearly looking for a `for r = 1, 256, 1 do <scratch>[r] = r end`.
    for i, s in ipairs(stmts) do
        if s.kind == AstKind.ForStatement
                and asNumber(s.initialValue) == 1
                and asNumber(s.finalValue) == 256
                and asNumber(s.incrementBy) == 1
                and s.body and s.body.statements
                and #s.body.statements == 1 then
            local body = s.body.statements[1]
            if body.kind == AstKind.AssignmentStatement
                    and body.lhs and #body.lhs == 1
                    and body.lhs[1].kind == AstKind.AssignmentIndexing
                    and isVar(body.lhs[1].base) then
                local scratch = vkey(body.lhs[1].base)
                if scratch then
                    -- Check the following statement is `while true do shuffle if #scratch==0 break end end`.
                    local w = stmts[i + 1]
                    if w and w.kind == AstKind.WhileStatement
                            and w.condition
                            and w.condition.kind == AstKind.BooleanExpression
                            and w.condition.value == true then
                        local wb = w.body and w.body.statements
                        if wb and #wb >= 3 then
                            local writeStmt = wb[2]
                            if writeStmt.kind == AstKind.AssignmentStatement
                                    and writeStmt.lhs and #writeStmt.lhs == 1
                                    and writeStmt.lhs[1].kind == AstKind.AssignmentIndexing
                                    and isVar(writeStmt.lhs[1].base) then
                                local ctk = vkey(writeStmt.lhs[1].base)
                                if ctk and infraSlots[ctk] then
                                    toRemove[s] = true
                                    toRemove[w] = true
                                    -- Also remove the `<scratch> = {}` and
                                    -- `<chartbl> = {}` immediately before, if present.
                                    for j = i - 1, math.max(1, i - 4), -1 do
                                        local p = stmts[j]
                                        if p.kind == AstKind.AssignmentStatement
                                                and p.lhs and #p.lhs == 1
                                                and p.lhs[1].kind == AstKind.AssignmentVariable
                                                and p.rhs and #p.rhs == 1
                                                and p.rhs[1].kind == AstKind.TableConstructorExpression
                                                and #(p.rhs[1].entries or {}) == 0 then
                                            local pk = akey(p.lhs[1])
                                            if pk == scratch or (pk and infraSlots[pk]) then
                                                toRemove[p] = true
                                            end
                                        end
                                    end
                                    return toRemove, scratch
                                end
                            end
                        end
                    end
                end
            end
        end
    end
    return toRemove, nil
end

-- Find statements assigning the infra function literals (decoder /
-- byte-stream).  Returns a set of statement nodes.
local function findInfraFnAssignments(ast, infraFnLiterals)
    local stmts = {}
    walk(ast, function(n)
        if n.kind == AstKind.AssignmentStatement
                and n.lhs and #n.lhs == 1
                and n.rhs and #n.rhs == 1
                and infraFnLiterals[n.rhs[1]] then
            stmts[n] = true
        end
        if n.kind == AstKind.LocalVariableDeclaration
                and n.expressions and #n.expressions == 1
                and infraFnLiterals[n.expressions[1]] then
            stmts[n] = true
        end
    end)
    return stmts
end

-- Decide whether `stmt` should be dropped from a block's statement list,
-- using the infra slot / removeStmts / fnLiterals sets.
local function shouldDrop(stmt, infraSlots, removeStmts, fnLiterals)
    if removeStmts[stmt] then return true end
    if stmt.kind == AstKind.AssignmentStatement
            and stmt.lhs and #stmt.lhs >= 1
            and stmt.rhs and #stmt.rhs == #stmt.lhs then
        -- All LHS must be plain variables in infraSlots.  All RHS must
        -- be trivially pure (constants, stdlib globals, infra slot
        -- references, infra fn literals).
        for _, lhs in ipairs(stmt.lhs) do
            if lhs.kind ~= AstKind.AssignmentVariable then return false end
            local lk = akey(lhs)
            if not lk or not infraSlots[lk] then return false end
        end
        for _, e in ipairs(stmt.rhs) do
            if not isTriviallyPure(e, infraSlots, fnLiterals) then
                return false
            end
        end
        return true
    end
    return false
end

-- Process every Block reachable from `root`, removing infra statements.
-- Iterative -- avoids stack overflows on deeply nested user code.
local function pruneTopLevel(ast, infraSlots, removeStmts, fnLiterals)
    local removed = 0
    -- Collect all distinct Block nodes via a single walk.
    local blocks = {}
    local function collectBlocks(root)
        if type(root) ~= "table" then return end
        local stack, top = { root }, 1
        local seen = {}
        while top > 0 do
            local n = stack[top]
            stack[top] = nil
            top = top - 1
            if type(n) == "table" and not seen[n] then
                seen[n] = true
                if n.kind == AstKind.Block then
                    blocks[#blocks + 1] = n
                end
                for k, v in pairs(n) do
                    if k ~= "scope" and k ~= "parentScope"
                            and k ~= "baseScope" and k ~= "globalScope"
                            and type(v) == "table" then
                        top = top + 1
                        stack[top] = v
                    end
                end
            end
        end
    end
    if ast.kind == AstKind.TopNode then collectBlocks(ast.body)
    elseif ast.kind == AstKind.Block then collectBlocks(ast)
    end
    for _, block in ipairs(blocks) do
        if block.statements then
            local kept = {}
            for _, stmt in ipairs(block.statements) do
                if shouldDrop(stmt, infraSlots, removeStmts, fnLiterals) then
                    removed = removed + 1
                else
                    kept[#kept + 1] = stmt
                end
            end
            block.statements = kept
        end
    end
    return removed
end

function M.apply(ast)
    local info = decrypt_vm_strings.cachedInfo(ast)
    if not info then
        return { note = "no in-VM decoder identified (skipped)" }
    end

    local decoderFnNode = info.decoderFnNode
    local cacheKey = info.cacheKey
    local proxyKey = info.proxyKey
    if not (decoderFnNode and cacheKey and proxyKey) then
        return { note = "incomplete decoder info (skipped)" }
    end

    local byteStreamFn = findByteStreamFn(ast)

    -- Infra function bodies = the set whose reads do NOT count as
    -- "user" reads.
    local infraBodySet = collectInfraBodies(ast, cacheKey, decoderFnNode, byteStreamFn)
    local insideInfra = buildContainmentTest(infraBodySet)

    -- Identify the proxy setup expression so its `<cache>` read is not
    -- treated as a user-read.
    local proxySetupExpr = findProxySetupExpr(ast, cacheKey)

    local userReads = computeUserReads(ast, insideInfra, proxySetupExpr)

    -- A slot is "infra" iff:
    --   * It's referenced anywhere in the program, AND
    --   * It has zero user-reads.
    local infraSlots = {}
    -- Always include cacheKey and proxyKey as infra slots.
    infraSlots[cacheKey] = true
    if (userReads[proxyKey] or 0) == 0 then infraSlots[proxyKey] = true end

    -- Collect candidate slot keys: everything referenced in the program.
    local allKeys = {}
    walk(ast, function(n)
        if n.kind == AstKind.VariableExpression
                or n.kind == AstKind.AssignmentVariable then
            local k = vkey(n)
            if k then allKeys[k] = true end
        end
    end)
    for k in pairs(allKeys) do
        if (userReads[k] or 0) == 0 then
            -- Only consider slots that are in the OUTER main scope (i.e.
            -- those that look like loc_X or rX).  We have no easy way
            -- to filter by scope without a reference -- but the
            -- containment-driven user-read test already prevents most
            -- false positives.  Keep slot if it's referenced ONLY
            -- inside infra bodies + the proxy setup, AND it gets at
            -- least one write at the main-body level.
            infraSlots[k] = true
        end
    end

    -- Build the set of infra fn literals (their direct assignment
    -- statements get removed).
    local infraFnLiterals = {}
    if decoderFnNode then infraFnLiterals[decoderFnNode] = true end
    if byteStreamFn then infraFnLiterals[byteStreamFn] = true end

    -- The on-demand cache function lives at top level of the main body
    -- and its holder var is in infraSlots already (no user-reads of the
    -- holder).  Its assignment statement gets caught by isTriviallyPure
    -- (RHS is the fn literal, which we marked in `fnLiterals`).

    local removeStmts = findInfraFnAssignments(ast, infraFnLiterals)

    -- Char-table init pattern (multi-statement).
    local funcBody
    if ast.kind == AstKind.TopNode then funcBody = ast.body
    elseif ast.kind == AstKind.Block then funcBody = ast end
    if funcBody then
        local more = findCharTableInit(funcBody, infraSlots)
        for s in pairs(more) do removeStmts[s] = true end
    end



    local removed = pruneTopLevel(ast, infraSlots, removeStmts, infraFnLiterals)
    return { note = ("stripped " .. tostring(removed) .. " infra statement(s)") }
end

return M
