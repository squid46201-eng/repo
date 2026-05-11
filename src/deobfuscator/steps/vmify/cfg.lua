-- prometheus-test-deobfuscator -- CFG / function partition / dominators.
--
-- This module operates on the output of decompile_block.decompileAll(...)
-- and the underlying extracted blocks. It does three things:
--
--   1. Partition all dispatcher blocks into FUNCTIONS. Every CREATE_CLOSURE
--      target is the entry of a separate function; the top-level function
--      starts at vm.entry.entryId. Blocks reachable from a function entry
--      via control-flow edges (POS = N, POS = (cond and X) or Y, etc.) --
--      but NOT via closure construction -- belong to that function.
--
--   2. Build a per-function CFG: succs[id], preds[id], plus a synthetic
--      EXIT node (-1) that every RETURN / fall-through block leads to.
--
--   3. Compute dominators (idom) and post-dominators (ipdom) for each
--      function. We use the simple iterative algorithm of Cooper-Harvey-
--      Kennedy "A Simple, Fast Dominance Algorithm". Block IDs are
--      arbitrary 24-bit numbers, so we work in a dense numbering space
--      (each function gets its own 1..N reverse-postorder numbering).
--
-- Output (returned by cfg.build(decomps, extracted, vm)):
--   {
--     fns = {                         -- list of functions (and table keyed by entryId)
--       { entryId = number, isMain = bool, blockIds = { ids... },
--         succs = {[id]={ids}}, preds = {[id]={ids}},
--         idom  = {[id]=parentId},    -- in this function's CFG (-1 = synthetic ENTRY)
--         ipdom = {[id]=childId},     -- in the reverse CFG (-2 = synthetic EXIT)
--         rpo   = { ids... },         -- reverse postorder numbering (incl. ENTRY)
--         postorder = { ids... },
--       }, ...
--     }
--   }

local ir = require("deobfuscator.steps.vmify.ir")
local K  = ir.kinds

local M = {}

-- Reserved synthetic node ids in a per-function CFG.
M.ENTRY = -1
M.EXIT  = -2

-- ----------------------------------------------------------------------------
-- 1) Partition.
--
-- Walk every block; collect the list of CREATE_CLOSURE entry ids referenced
-- from any block. Each such id starts a separate function. We DFS from each
-- function's entry following pos-edges only (jump_const, jump_cond) until
-- we hit a return/fallthrough leaf. Closure-creation does NOT cross.

local function collectClosureEntries(decomps)
    local set = {}
    for _, d in ipairs(decomps) do
        for _, s in ipairs(d.statements) do
            local function scan(node)
                if type(node) ~= "table" then return end
                if node.kind == "_irClosure" and node.entryId then
                    set[node.entryId] = true
                end
                for k, v in pairs(node) do
                    if k ~= "scope" and type(v) == "table" then
                        if v.kind then scan(v)
                        elseif #v > 0 then for _, vv in ipairs(v) do scan(vv) end end
                    end
                end
            end
            -- Also check the rawStatements (CREATE_CLOSURE may be split out).
            if s.kind == K.CREATE_CLOSURE and s.entryId then
                set[s.entryId] = true
            end
            -- Walk all operand-bearing fields for any embedded _irClosure.
            for _, f in ipairs({"value","source","lhs","rhs","base","index","cond"}) do
                if s[f] then scan(s[f]) end
            end
            if s.args then for _, a in ipairs(s.args) do scan(a) end end
            if s.upvalSlots then for _, u in ipairs(s.upvalSlots) do scan(u) end end
        end
        for _, s in ipairs(d.rawStatements or {}) do
            if s.kind == K.CREATE_CLOSURE and s.entryId then
                set[s.entryId] = true
            end
        end
    end
    return set
end

local function successorsOf(d)
    local out = {}
    if d.exitKind == "jump_const" then
        out[1] = d.exitTarget
    elseif d.exitKind == "jump_cond" then
        out[1] = d.exitTargets[1]
        out[2] = d.exitTargets[2]
    end
    -- "return" / "fallthrough" / "other" -> no successors.
    return out
end

local function dfsCollect(entryId, decompMap, stops, out)
    if out[entryId] then return end
    if not decompMap[entryId] then return end  -- defensive
    out[entryId] = true
    local d = decompMap[entryId]
    for _, succ in ipairs(successorsOf(d)) do
        if not stops[succ] then
            dfsCollect(succ, decompMap, stops, out)
        end
    end
end

local function partition(decomps, vm)
    -- decomps is a list (and a map by id). decompMap[id] -> decomp.
    local decompMap = {}
    for _, d in ipairs(decomps) do decompMap[d.id] = d end

    local closureEntries = collectClosureEntries(decomps)

    local fns = {}
    local seen = {}

    -- Closure functions first.
    for entryId in pairs(closureEntries) do
        if not seen[entryId] and decompMap[entryId] then
            local stops = {}
            for other in pairs(closureEntries) do
                if other ~= entryId then stops[other] = true end
            end
            local cover = {}
            dfsCollect(entryId, decompMap, stops, cover)
            local ids = {}
            for id in pairs(cover) do
                table.insert(ids, id)
                seen[id] = true
            end
            table.sort(ids)
            local fn = {
                entryId = entryId,
                isMain  = false,
                blockIds = ids,
            }
            table.insert(fns, fn)
            fns[entryId] = fn
        end
    end

    -- Main function.
    local mainEntry = vm.entry.entryId
    if not seen[mainEntry] then
        local stops = {}
        for other in pairs(closureEntries) do stops[other] = true end
        local cover = {}
        dfsCollect(mainEntry, decompMap, stops, cover)
        local ids = {}
        for id in pairs(cover) do
            table.insert(ids, id)
            seen[id] = true
        end
        table.sort(ids)
        local fn = {
            entryId = mainEntry,
            isMain  = true,
            blockIds = ids,
        }
        table.insert(fns, fn)
        fns[mainEntry] = fn
    end

    -- Synthetic / orphaned blocks are typically dead leaves the dispatcher
    -- emits to fill out its binary-search tree, but they can also be tail
    -- blocks reachable only via dynamic POS writes that we couldn't track
    -- statically. Attach them to the main function so they don't get lost.
    local unassigned = {}
    local mainFn = fns[mainEntry]
    for _, d in ipairs(decomps) do
        if not seen[d.id] then
            table.insert(unassigned, d.id)
            seen[d.id] = true
            if mainFn then
                table.insert(mainFn.blockIds, d.id)
            end
        end
    end
    if mainFn then table.sort(mainFn.blockIds) end

    return fns, decompMap, unassigned
end

-- ----------------------------------------------------------------------------
-- 2) Build CFG (succs / preds / synthetic ENTRY/EXIT).

local function buildCfg(fn, decompMap)
    local succs = {}
    local preds = {}
    for _, id in ipairs(fn.blockIds) do
        succs[id] = {}
        preds[id] = {}
    end
    succs[M.ENTRY] = { fn.entryId }
    preds[fn.entryId] = preds[fn.entryId] or {}
    table.insert(preds[fn.entryId], M.ENTRY)
    succs[M.EXIT] = {}
    preds[M.EXIT] = {}

    local function addEdge(a, b)
        if not succs[a] then succs[a] = {} end
        if not preds[b] then preds[b] = {} end
        table.insert(succs[a], b)
        table.insert(preds[b], a)
    end

    local blockSet = {}
    for _, id in ipairs(fn.blockIds) do blockSet[id] = true end

    for _, id in ipairs(fn.blockIds) do
        local d = decompMap[id]
        local kids = successorsOf(d)
        if #kids == 0 then
            addEdge(id, M.EXIT)
        else
            for _, k in ipairs(kids) do
                if blockSet[k] then
                    addEdge(id, k)
                else
                    -- Edge leaves this function (shouldn't happen for proper
                    -- partitions; treat as exit).
                    addEdge(id, M.EXIT)
                end
            end
        end
    end

    fn.succs = succs
    fn.preds = preds
end

-- ----------------------------------------------------------------------------
-- 3) Dominators (Cooper-Harvey-Kennedy).
--
-- We compute over a dense reverse-postorder numbering. The function
-- "buildRpo" produces:
--   rpo: list of node ids in reverse-postorder (start node first)
--   index[id] = position in rpo (1-based)

local function buildRpo(succs, start)
    local visited = {}
    local postorder = {}
    local function visit(n)
        if visited[n] then return end
        visited[n] = true
        for _, s in ipairs(succs[n] or {}) do visit(s) end
        table.insert(postorder, n)
    end
    visit(start)
    local rpo = {}
    for i = #postorder, 1, -1 do table.insert(rpo, postorder[i]) end
    local index = {}
    for i, n in ipairs(rpo) do index[n] = i end
    return rpo, postorder, index
end

local function intersect(b1, b2, idom, index)
    local f1, f2 = b1, b2
    while f1 ~= f2 do
        while index[f1] > index[f2] do f1 = idom[f1] end
        while index[f2] > index[f1] do f2 = idom[f2] end
    end
    return f1
end

local function computeIdom(succs, preds, start)
    local rpo, postorder, index = buildRpo(succs, start)
    local idom = {}
    idom[start] = start  -- conventional: start dominates itself

    local changed = true
    while changed do
        changed = false
        -- iterate in RPO, skipping start
        for i = 2, #rpo do
            local b = rpo[i]
            -- pick first defined predecessor as new_idom
            local new_idom
            for _, p in ipairs(preds[b] or {}) do
                if idom[p] then new_idom = p; break end
            end
            -- intersect with each remaining defined predecessor
            for _, p in ipairs(preds[b] or {}) do
                if p ~= new_idom and idom[p] then
                    new_idom = intersect(p, new_idom, idom, index)
                end
            end
            if idom[b] ~= new_idom then
                idom[b] = new_idom
                changed = true
            end
        end
    end

    -- Conventional: idom[start] is the start itself; null it out so that
    -- "is start" is detected via b == start, not idom[b] == b.
    return idom, rpo, postorder, index
end

-- ----------------------------------------------------------------------------
-- 4) Natural-loop detection.
--
-- A back-edge is an edge u->v where v dominates u (in the forward CFG). The
-- natural loop with header v consists of v itself plus every node that can
-- reach u without passing through v. We collect this via reverse BFS from u
-- staying within dom(v).
--
-- For each loop we record:
--   header     = v  (the dominator of every block in the loop body)
--   latches    = { u, ... }  (sources of back-edges to v)
--   body       = { id, ... } (set of blocks; header is always included)
--   bodySet    = {[id]=true}
--   exits      = { id, ... } (blocks NOT in body but reachable from a
--                             body-block via a single edge -- i.e. the
--                             loop's "post-condition" successors)
--   exitEdges  = { {from, to}, ... } (the edges that leave the loop)
--   preheader  = the unique block whose only successor is header AND is
--                NOT a latch (i.e. the block that "falls into" the loop);
--                or nil if there isn't a unique one.

local function dominates(fn, a, b)
    -- Does a dominate b?
    local cur = b
    while cur and cur ~= M.ENTRY do
        if cur == a then return true end
        local idom = fn.idom[cur]
        if not idom or idom == cur then break end
        cur = idom
    end
    -- ENTRY dominates everything.
    if a == M.ENTRY then return true end
    return false
end
M.dominates = dominates

local function findLoopBody(fn, header, latches)
    -- Reverse BFS from latches; walk preds, stop at header.
    local body = { [header] = true }
    local stack = {}
    for _, l in ipairs(latches) do
        if not body[l] then body[l] = true; table.insert(stack, l) end
    end
    while #stack > 0 do
        local n = table.remove(stack)
        for _, p in ipairs(fn.preds[n] or {}) do
            if p ~= M.ENTRY and not body[p] then
                body[p] = true
                table.insert(stack, p)
            end
        end
    end
    return body
end

local function findLoops(fn)
    -- 1) Find back-edges. (u, v) is a back-edge iff v dominates u.
    local headersToLatches = {}  -- header id -> { latch ids }
    for _, u in ipairs(fn.blockIds) do
        for _, v in ipairs(fn.succs[u] or {}) do
            if v ~= M.EXIT and dominates(fn, v, u) then
                headersToLatches[v] = headersToLatches[v] or {}
                table.insert(headersToLatches[v], u)
            end
        end
    end

    -- 2) Build a loop record per header.
    local loops = {}
    for header, latches in pairs(headersToLatches) do
        local bodySet = findLoopBody(fn, header, latches)
        local body = {}
        for id in pairs(bodySet) do table.insert(body, id) end
        table.sort(body)

        -- Exits: edges from body-block to non-body-block.
        local exits = {}
        local exitsSet = {}
        local exitEdges = {}
        for _, id in ipairs(body) do
            for _, k in ipairs(fn.succs[id] or {}) do
                if k ~= M.EXIT and not bodySet[k] then
                    if not exitsSet[k] then
                        exitsSet[k] = true
                        table.insert(exits, k)
                    end
                    table.insert(exitEdges, { from = id, to = k })
                elseif k == M.EXIT then
                    -- A return inside the loop also terminates it; record
                    -- as an exit-edge but not as an exit-block.
                    table.insert(exitEdges, { from = id, to = M.EXIT })
                end
            end
        end

        -- Preheader: the unique non-latch predecessor of header. If header
        -- has predecessors {ENTRY, latches...}, ENTRY is the preheader-
        -- proxy. Otherwise we look for a real block.
        local preheader = nil
        local nonLatchPreds = {}
        local latchSet = {}
        for _, l in ipairs(latches) do latchSet[l] = true end
        for _, p in ipairs(fn.preds[header] or {}) do
            if p ~= M.ENTRY and not latchSet[p] then
                table.insert(nonLatchPreds, p)
            end
        end
        if #nonLatchPreds == 1 then
            preheader = nonLatchPreds[1]
        end

        table.insert(loops, {
            header     = header,
            latches    = latches,
            body       = body,
            bodySet    = bodySet,
            exits      = exits,
            exitEdges  = exitEdges,
            preheader  = preheader,
        })
    end

    -- 3) Innermost-loop map: each block -> innermost containing loop.
    -- A loop A is *contained* in loop B if A.header is in B.bodySet and
    -- A != B. Innermost = the smallest containing loop by body size.
    local innermost = {}
    for _, blockId in ipairs(fn.blockIds) do
        local best, bestSize
        for _, loop in ipairs(loops) do
            if loop.bodySet[blockId] then
                if not best or #loop.body < bestSize then
                    best, bestSize = loop, #loop.body
                end
            end
        end
        innermost[blockId] = best
    end

    -- Also build header -> loop map for fast lookup.
    local byHeader = {}
    for _, loop in ipairs(loops) do byHeader[loop.header] = loop end

    fn.loops      = loops
    fn.loopOf     = innermost
    fn.loopHeader = byHeader
end
M.findLoops = findLoops

-- ----------------------------------------------------------------------------
-- Public API.

function M.build(decomps, extracted, vm)
    local fns, decompMap, unassigned = partition(decomps, vm)

    for _, fn in ipairs(fns) do
        buildCfg(fn, decompMap)

        -- Forward dominators rooted at synthetic ENTRY.
        local idom, rpo, postorder, index = computeIdom(fn.succs, fn.preds, M.ENTRY)
        fn.idom = idom
        fn.rpo = rpo
        fn.postorder = postorder
        fn.rpoIndex = index

        -- Reverse-graph dominators rooted at synthetic EXIT --> post-dominators.
        local rsuccs = {}  -- reverse succs == preds
        local rpreds = {}  -- reverse preds == succs
        for n, _ in pairs(fn.succs) do
            rsuccs[n] = {}
            rpreds[n] = {}
        end
        for n, kids in pairs(fn.succs) do
            for _, k in ipairs(kids) do
                table.insert(rsuccs[k], n)  -- reversed
                table.insert(rpreds[n], k)
            end
        end
        local ipdom, rrpo, _, rindex = computeIdom(rsuccs, rpreds, M.EXIT)
        fn.ipdom = ipdom
        fn.ipdomRpo = rrpo
        fn.ipdomIndex = rindex

        -- Natural-loop detection (M4).
        findLoops(fn)
    end

    return {
        fns         = fns,
        decompMap   = decompMap,
        unassigned  = unassigned,
    }
end

-- ----------------------------------------------------------------------------
-- Pretty report.

local function fmtNode(id)
    if id == M.ENTRY then return "ENTRY" end
    if id == M.EXIT  then return "EXIT"  end
    return tostring(id)
end

function M.report(cfg, write)
    write = write or function(s) io.write(s); io.write("\n") end
    write(("CFG: %d function(s) [%d unassigned blocks]"):format(#cfg.fns, #cfg.unassigned))
    for _, fn in ipairs(cfg.fns) do
        write(("  fn %s%d: %d block(s)"):format(fn.isMain and "(main) " or "", fn.entryId, #fn.blockIds))
        for _, id in ipairs(fn.blockIds) do
            local s = cfg.decompMap[id]
            local kids = {}
            for _, k in ipairs(fn.succs[id] or {}) do table.insert(kids, fmtNode(k)) end
            local idom = fn.idom[id]
            local ipdom = fn.ipdom[id]
            write(("    %-10d  succs=[%s]  idom=%s  ipdom=%s"):format(
                id, table.concat(kids, ","),
                fmtNode(idom or "?"), fmtNode(ipdom or "?")))
        end
    end
end

return M
