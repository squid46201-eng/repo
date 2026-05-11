-- prometheus-test-deobfuscator -- Vmify dispatcher extractor.
--
-- Given a recognized VM (recognize.lua), extracts the per-block bodies of the
-- dispatcher, recovers each block's numeric ID, and links every block to its
-- successors via the `pos = ...` assignments it contains.
--
-- Output (returned by extract.extract(vm)):
--   {
--     blocks         = { [id] = { id, body, statements, exits, kind } },
--     blocksOrdered  = { ... }                       -- ascending-id order
--     entryId        = number                        -- top-level entry block id
--     posVar         = { scope, id }                 -- POS register
--     posWrites      = { ... }                       -- raw pos writes encountered
--     containerLocal = ...                           -- references to special locals
--   }
--
-- Block IDs are recovered in two passes:
--   1. Walk every leaf of the dispatcher tree. Leaves are encountered in
--      ascending-id order (compiler/emit.lua:209) so we just need to know how
--      many leaves there are.
--   2. Collect every numeric literal that occurs in either:
--        - a `pos = NUMBER` assignment, or
--        - a `pos = (cond and X) or Y` assignment (X, Y are NUMBERS),
--        - a CREATE_CLOSURE(NUMBER, ...) call (NUMBER is the entry id of an
--          inner function),
--        - the entry id passed to CREATE_VARARG_CLOSURE.
--      Sort that set ascending; it pairs 1:1 with leaves.
--
-- Block IDs are 24-bit Prometheus randoms, so collisions between distinct
-- functions can theoretically happen but are extremely unlikely on real
-- programs. We assert uniqueness of recovered ids and report otherwise.

local Ast = require("prometheus.ast")
local astu = require("deobfuscator.ast_utils")
local AstKind = Ast.AstKind

local M = {}

-- ----------------------------------------------------------------------------
-- Tiny helpers.

local function isVar(node)
    return node and node.kind == AstKind.VariableExpression
end

local function isNumber(node)
    return node and node.kind == AstKind.NumberExpression
end

local function isCall(node)
    return node and node.kind == AstKind.FunctionCallExpression
end

local function isAssignVar(lhs)
    return lhs and lhs.kind == AstKind.AssignmentVariable
end

local function sameVar(a, b)
    if not (isVar(a) and isVar(b)) then return false end
    return a.scope == b.scope and a.id == b.id
end

local function sameLhsVar(a, b)
    return a and b and a.scope == b.scope and a.id == b.id
end

-- ----------------------------------------------------------------------------
-- Walk the dispatcher tree.
--
-- Returns the list of leaf blocks in the order they appear (which is
-- ascending-id order, per emit.lua), each represented as:
--   { body = <Ast.Block>, statements = body.statements }

local function isPosLessThanComparison(cond, posVar)
    -- Match `pos < N`, `N > pos`. Returns the bound and the polarity:
    --   "true_left"  -> the IfStatement's TRUE branch holds the lower-id range
    --   "true_right" -> the IfStatement's TRUE branch holds the higher-id range
    if not cond then return nil end
    local k = cond.kind
    if k == AstKind.LessThanExpression then
        if sameVar(cond.lhs, posVar) and isNumber(cond.rhs) then
            return cond.rhs.value, "true_left"
        end
    elseif k == AstKind.GreaterThanExpression then
        if isNumber(cond.lhs) and sameVar(cond.rhs, posVar) then
            -- N > pos is equivalent to pos < N
            return cond.lhs.value, "true_left"
        end
        if sameVar(cond.lhs, posVar) and isNumber(cond.rhs) then
            -- pos > N: TRUE branch holds higher-id range
            return cond.rhs.value, "true_right"
        end
    end
    return nil
end

-- Recursively walk a Block and harvest its dispatcher leaves.
-- Returns a list of leaf entries in left-to-right order. Each leaf is
-- `{ body = <Ast.Block> }`. Pure leaves are blocks whose only statements
-- are non-dispatch-IfStatement statements; dispatcher IfStatements at the
-- block level are recursed into.
-- Walk the dispatcher tree and record every leaf along with its [lo, hi) ID range.
-- The whole id space is [1, 2^24); each `if pos < bound` sub-divides it.
local ID_MAX = 16777216  -- 2^24

local function harvestLeaves(rootBlock, posVar)
    local leaves = {}
    local visitBlock, visitIf

    local function isDispatchIf(stat)
        if stat.kind ~= AstKind.IfStatement then return false end
        local bound, _polarity = isPosLessThanComparison(stat.condition, posVar)
        return bound ~= nil
    end

    visitBlock = function(block, lo, hi)
        if #block.statements == 1 and isDispatchIf(block.statements[1]) then
            local ifs = block.statements[1]
            visitIf(ifs, lo, hi)
        else
            -- Payload (leaf) block.
            table.insert(leaves, { body = block, idLo = lo, idHi = hi })
        end
    end

    visitIf = function(ifs, lo, hi)
        local bound, polarity = isPosLessThanComparison(ifs.condition, posVar)
        local primary, secondary = ifs.body, ifs.elsebody
        local elseifs = ifs.elseifs or {}

        if polarity == "true_left" then
            -- `pos < bound` is equivalent for both LessThan and `bound > pos`.
            -- TRUE branch holds the LOWER-id half. Sub-ranges:
            --   primary:    [lo, min(hi, bound))
            --   elseif #1:  [bound, ...) -- but only if its own condition matches a sub-bound
            --   elsebody:   [..., hi)
            -- For the small-range case (emit.lua: len <= 4) primary uses
            -- the firstCondition (bound between tb[l] and tb[l+1]); each
            -- elseif uses a bound between tb[i] and tb[i+1]; else holds the
            -- last block.
            local prevBound = lo
            visitBlock(primary, prevBound, math.min(hi, bound))
            prevBound = bound
            for _, ei in ipairs(elseifs) do
                local b2 = isPosLessThanComparison(ei.condition, posVar)
                if not b2 then
                    -- An elseif we don't understand -- treat as opaque leaf.
                    table.insert(leaves, { body = ei.body, idLo = prevBound, idHi = hi })
                    prevBound = hi
                else
                    visitBlock(ei.body, prevBound, math.min(hi, b2))
                    prevBound = b2
                end
            end
            if secondary then
                visitBlock(secondary, prevBound, hi)
            end
        else
            -- `pos > bound`: TRUE branch holds the HIGHER-id half.
            -- (emit.lua condStyle == 3 uses this with branches swapped; we
            -- reverse here so leaves remain in ascending-id order.)
            if secondary then visitBlock(secondary, lo, bound) end
            -- elseifs in this orientation are unusual; handle defensively.
            for i = #elseifs, 1, -1 do
                table.insert(leaves, { body = elseifs[i].body, idLo = lo, idHi = hi })
            end
            visitBlock(primary, bound, hi)
        end
    end

    visitBlock(rootBlock, 1, ID_MAX)
    return leaves
end

-- ----------------------------------------------------------------------------
-- Find the while loop in the container body.

local function findContainerWhile(containerFunc)
    local posVar = containerFunc.args[1]
    if not isVar(posVar) then
        return nil, "container function arg #1 (pos) is not a variable"
    end
    for _, stat in ipairs(containerFunc.body.statements) do
        if stat.kind == AstKind.WhileStatement and sameVar(stat.condition, posVar) then
            return stat, posVar
        end
    end
    return nil, "no `while pos do` loop in container body"
end

-- ----------------------------------------------------------------------------
-- Collect all numeric block IDs referenced within blocks.

-- Return the AssignmentVariable's (scope, id) tuple if `lhs` is exactly the
-- POS register; nil otherwise.
local function isAssignToPos(lhs, posVar)
    return isAssignVar(lhs) and posVar
        and lhs.scope == posVar.scope and lhs.id == posVar.id
end

-- Collect the *strict* candidate set: every block id we can prove flows into
-- a pos-write. We do this by intra-block forward propagation of constant
-- register loads (`R = NUMBER`), then substituting register references in
-- pos-write right-hand sides.
local function collectCandidateIds(leaves, posVar, vm)
    local ids = {}

    -- Recognize CREATE_CLOSURE / CREATE_VARARG_CLOSURE call sites; their first
    -- argument is always an inner-function entry block id.
    local closureLhsList = {}
    for _, h in ipairs(vm.helpers.CREATE_CLOSURES or {}) do
        table.insert(closureLhsList, h.lhs)
    end
    if vm.helpers.CREATE_VARARG_CLOSURE then
        table.insert(closureLhsList, vm.helpers.CREATE_VARARG_CLOSURE.lhs)
    end
    local function isClosureFactoryCall(call)
        if not isCall(call) then return false end
        if not isVar(call.base) then return false end
        for _, lhs in ipairs(closureLhsList) do
            if call.base.scope == lhs.scope and call.base.id == lhs.id then
                return true
            end
        end
        return false
    end

    local function takeNumber(v)
        if type(v) ~= "number" then return end
        if v < 1 or v >= ID_MAX then return end
        if v ~= math.floor(v) then return end
        ids[v] = true
    end

    -- Use scope tables AND ids as map keys via tostring of the scope and the
    -- numeric id, to avoid concatenating a table with `..`.
    local function regKey(scope, id)
        return tostring(scope) .. ":" .. tostring(id)
    end

    -- Resolve an expression to a *single* number value if it is structurally a
    -- constant-value chain. Returns a number, or nil if the expression isn't
    -- a clean constant.  The register table may also hold small control-flow
    -- expressions (not just numbers) so split `pos = cond and T; pos = pos or F`
    -- exits can be harvested from the final POS write only.
    local function resolveConst(expr, regTbl)
        if not expr then return nil end
        if isNumber(expr) then return expr.value end
        if isVar(expr) then
            local key = regKey(expr.scope, expr.id)
            local v = regTbl[key]
            if type(v) == "number" then return v end
            if type(v) == "table" and v ~= expr then
                regTbl.__resolving = regTbl.__resolving or {}
                if regTbl.__resolving[key] then return nil end
                regTbl.__resolving[key] = true
                local n = resolveConst(v, regTbl)
                regTbl.__resolving[key] = nil
                return n
            end
            return nil
        end
        return nil
    end

    -- Harvest candidate ids from a pos-write right-hand side. We support
    -- exactly the shapes Prometheus emits:
    --   pos = NUMBER                     (jump_const)
    --   pos = REG    where REG = NUMBER  (jump via register-load, e.g. for-loops)
    --   pos = (cond and TRUE) or FALSE   (jump_cond; both children resolve to numbers)
    --   pos = pos OR REG                 (for-loop tail merge -- harvest REG as a const)
    --   pos = (REG_T) AND (REG_F)        (for-loop check first half)
    --   pos = ENV.<global>               (return; nothing to harvest)
    -- For other shapes we do nothing to avoid leaking user-code constants.
    local function harvestExpr(expr, regTbl)
        if not expr then return end
        local n = resolveConst(expr, regTbl)
        if n then takeNumber(n); return end
        if isVar(expr) then
            local mapped = regTbl[regKey(expr.scope, expr.id)]
            if type(mapped) == "table" and mapped ~= expr then
                harvestExpr(mapped, regTbl)
            end
            return
        end
        if expr.kind == AstKind.OrExpression then
            harvestExpr(expr.lhs, regTbl)
            harvestExpr(expr.rhs, regTbl)
            return
        end
        if expr.kind == AstKind.AndExpression then
            -- In `cond AND X` the lhs is a boolean (typically a register),
            -- and X is a const-resolvable target id.
            harvestExpr(expr.rhs, regTbl)
            return
        end
        -- Anything else: skip silently (likely a return-style ENV.<global> or
        -- a function-call result; neither contributes a block-id literal).
    end

    local function isTrackableControlExpr(expr)
        if not expr then return false end
        if isNumber(expr) or isVar(expr) then return true end
        return expr.kind == AstKind.OrExpression or expr.kind == AstKind.AndExpression
    end

    for _, leaf in ipairs(leaves) do
        local regTbl = {}    -- regKey(scope, id) -> numberValue
        local lastPosStat, lastPosIndex
        for _, stat in ipairs(leaf.body.statements) do
            if stat.kind == AstKind.AssignmentStatement then
                for j, lhs in ipairs(stat.lhs) do
                    if isAssignToPos(lhs, posVar) then
                        lastPosStat, lastPosIndex = stat, j
                    end
                end
            end
        end
        for _, stat in ipairs(leaf.body.statements) do
            if stat.kind == AstKind.AssignmentStatement then
                for j, lhs in ipairs(stat.lhs) do
                    local rhs = stat.rhs[j]
                    local key = isAssignVar(lhs) and regKey(lhs.scope, lhs.id) or nil
                    if isAssignToPos(lhs, posVar) then
                        if stat == lastPosStat and j == lastPosIndex then
                            harvestExpr(rhs, regTbl)
                        elseif key then
                            regTbl[key] = isTrackableControlExpr(rhs) and rhs or nil
                        end
                    elseif isAssignVar(lhs) then
                        regTbl[key] = isTrackableControlExpr(rhs) and rhs or nil
                    end
                end
            elseif stat.kind == AstKind.LocalVariableDeclaration then
                for j, id in ipairs(stat.ids) do
                    local rhs = (stat.expressions or {})[j]
                    local key = regKey(stat.scope, id)
                    regTbl[key] = isTrackableControlExpr(rhs) and rhs or nil
                end
            end
        end
        -- Always also collect the entry id of any closure-factory call within the leaf.
        astu.walkExpressions(leaf.body, function(node)
            if isClosureFactoryCall(node) and node.args[1] then
                if isNumber(node.args[1]) then
                    takeNumber(node.args[1].value)
                end
            end
        end)
    end

    return ids
end

-- Intersect candidate-set with each leaf's [lo, hi) range. Each leaf must
-- end up with EXACTLY one id. If a leaf's range contains zero candidates we
-- assign it a deterministic synthetic id (midpoint of the range) -- such
-- blocks are reachable only via dynamic pos-writes (e.g. saved/restored pos
-- in `or.lua`), so the actual numeric id is unobservable to anyone but us.
local function assignIds(leaves, candidateSet, entryId)
    -- Always include the top-level entry id (we know it for certain).
    candidateSet[entryId] = true

    local sorted = {}
    for v, _ in pairs(candidateSet) do table.insert(sorted, v) end
    table.sort(sorted)

    local taken = {}
    for _, v in ipairs(sorted) do taken[v] = true end

    local result = {}
    local synthetic = {}
    for i, leaf in ipairs(leaves) do
        local matches = {}
        for _, v in ipairs(sorted) do
            if v >= leaf.idLo and v < leaf.idHi then
                table.insert(matches, v)
            end
        end
        if #matches > 1 then
            return nil, ("leaf #%d has %d candidate ids in range [%d, %d): %s"):format(
                i, #matches, leaf.idLo, leaf.idHi, table.concat(matches, ", "))
        elseif #matches == 1 then
            result[i] = matches[1]
        else
            -- No literal candidate found in this leaf's range; mint a
            -- synthetic id at the range midpoint that doesn't collide.
            local mid = math.floor((leaf.idLo + leaf.idHi) / 2)
            while taken[mid] and mid + 1 < leaf.idHi do mid = mid + 1 end
            if taken[mid] then
                return nil, ("could not mint synthetic id for leaf #%d"):format(i)
            end
            taken[mid] = true
            result[i] = mid
            synthetic[mid] = true
        end
    end
    return result, synthetic
end

-- ----------------------------------------------------------------------------
-- Classify a leaf's pos-exit:
--   "jump_const N"               -- pos = N
--   "jump_cond cond, T, F"       -- pos = (cond and T) or F  (block IDs)
--   "return"                     -- pos = ENV.<global> -- exits the while loop
--   "tail_call"                  -- pos = createClosure_call(...)(...args) -- 
--                                   the closure call returns a number ?? unlikely
-- We only classify the LAST pos-write; earlier ones (if any) would be unusual
-- but theoretically possible. We track them all.

local function classifyExit(rhs)
    if isNumber(rhs) then
        return { kind = "jump_const", target = rhs.value, expr = rhs }
    end
    if rhs.kind == AstKind.OrExpression
            and rhs.lhs and rhs.lhs.kind == AstKind.AndExpression
            and isNumber(rhs.lhs.rhs) and isNumber(rhs.rhs) then
        return {
            kind        = "jump_cond",
            condition   = rhs.lhs.lhs,
            trueTarget  = rhs.lhs.rhs.value,
            falseTarget = rhs.rhs.value,
            expr        = rhs,
        }
    end
    -- Returns are emitted by `setPos(scope, nil)` which becomes
    -- `pos = ENV.<random_string>` (an IndexExpression on the env table).
    if rhs.kind == AstKind.IndexExpression then
        return { kind = "return", expr = rhs }
    end
    -- Anything else: unknown / arbitrary; we still capture it.
    return { kind = "other", expr = rhs }
end

-- ----------------------------------------------------------------------------
-- Public API.

function M.extract(vm)
    local whileStat, posVar = findContainerWhile(vm.containerFunc)
    if not whileStat then
        return nil, posVar  -- second return holds the error message in this branch
    end

    local leaves = harvestLeaves(whileStat.body, posVar)
    if #leaves == 0 then
        return nil, "dispatcher has zero leaves"
    end

    local candidateSet = collectCandidateIds(leaves, posVar, vm)
    local ids, syntheticOrErr = assignIds(leaves, candidateSet, vm.entry.entryId)
    if not ids then return nil, syntheticOrErr end
    local synthetic = syntheticOrErr or {}

    local blocks = {}
    local blocksOrdered = {}
    for i, leaf in ipairs(leaves) do
        local id = ids[i]
        local exits = {}
        local stmts = leaf.body.statements
        for _, stat in ipairs(stmts) do
            if stat.kind == AstKind.AssignmentStatement then
                for j, lhs in ipairs(stat.lhs) do
                    if isAssignToPos(lhs, posVar) then
                        local exit = classifyExit(stat.rhs[j])
                        exit.statement = stat
                        exit.statementIndex = j
                        table.insert(exits, exit)
                    end
                end
            end
        end
        local block = {
            id         = id,
            body       = leaf.body,
            statements = stmts,
            exits      = exits,
            synthetic  = synthetic[id] or false,
            idLo       = leaf.idLo,
            idHi       = leaf.idHi,
        }
        blocks[id] = block
        table.insert(blocksOrdered, block)
    end

    return {
        blocks         = blocks,
        blocksOrdered  = blocksOrdered,
        entryId        = vm.entry.entryId,
        posVar         = { scope = posVar.scope, id = posVar.id, node = posVar },
        whileStat      = whileStat,
    }
end

-- Pretty report for debugging.
function M.report(extracted, write)
    write = write or function(s) io.write(s); io.write("\n") end
    write(("Dispatcher: %d block(s); entry id = %d"):format(#extracted.blocksOrdered, extracted.entryId))
    for _, b in ipairs(extracted.blocksOrdered) do
        local exitDesc
        if #b.exits == 0 then
            exitDesc = "(no pos-write -> falls off; assert ?)"
        else
            local last = b.exits[#b.exits]
            if last.kind == "jump_const" then
                exitDesc = ("-> %d"):format(last.target)
            elseif last.kind == "jump_cond" then
                exitDesc = ("?-> %d / %d"):format(last.trueTarget, last.falseTarget)
            elseif last.kind == "return" then
                exitDesc = "-> RETURN"
            else
                exitDesc = "-> ??"
            end
        end
        local idTag = b.synthetic and "(synth)" or "       "
        write(("  block %-12d %s  %3d stmts  %s"):format(b.id, idTag, #b.statements, exitDesc))
    end
end

return M
