-- prometheus-test-deobfuscator -- closures + upvalues resolution.
--
-- Walks each function's IR to:
--   1. Catalogue ALLOC_UPVAL sites (each = a fresh "slot" representing a
--      captured local). A slot has a unique name used everywhere.
--   2. Walk CREATE_CLOSURE statements to resolve which slot each child
--      function's upvalue index refers to (slot allocated in this function,
--      or one of this function's own upvalues).
--   3. Detect ALLOC_UPVAL + immediate UPVAL_WRITE-init pairs so callers can
--      emit `local <name> = <init>` instead of two raw IR statements.
--
-- Result is attached to each function entry as `fn.closureInfo` and exposed
-- as resolver helpers used by structure.lua's pretty printer.

local ir       = require("deobfuscator.steps.vmify.ir")
local Ast      = require("prometheus.ast")
local AstKind  = Ast.AstKind
local K        = ir.kinds

local M = {}

local isReg = ir.isReg

local function regKey(r)
    if not isReg(r) then return nil end
    return tostring(r.scope) .. ":" .. tostring(r.id)
end

-- Detect if an expression is `R3[N]` where R3 is a register with role
-- "UPVALS" (the function's UPVALS parameter table). Returns N (1-based) on
-- success.
local function asUpvalIndex(expr)
    if not expr then return nil end
    if expr.kind == "_irIndexRead" or expr.kind == AstKind.IndexExpression then
        local base = expr.base
        local index = expr.index
        if isReg(base) and base.role == "UPVALS"
           and index and index.kind == AstKind.NumberExpression then
            return index.value
        end
    end
    return nil
end

-- Detect if an expression is a plain register reference. Returns the regKey.
local function asRegRef(expr)
    if isReg(expr) then return regKey(expr), expr end
    return nil
end

-- ----------------------------------------------------------------------------
-- First pass: catalogue allocations and determine each function's set of
-- upvalues actually used.

-- Walk all sub-expressions of a node, calling `cb(node)` for each table-typed
-- node (including the root). Used to find inlined _irClosure / _irUpvalRead
-- expressions and any embedded R3[N] references.
local function visitAll(node, cb)
    if type(node) ~= "table" then return end
    cb(node)
    for _, k in ipairs({ "lhs", "rhs", "base", "index", "value", "target",
                         "source", "cond" }) do
        if node[k] ~= nil then visitAll(node[k], cb) end
    end
    if node.args        then for _, a in ipairs(node.args)        do visitAll(a, cb) end end
    if node.entries     then for _, e in ipairs(node.entries)     do visitAll(e, cb) end end
    if node.upvalSlots  then for _, u in ipairs(node.upvalSlots)  do visitAll(u, cb) end end
    if node.targets     then for _, t in ipairs(node.targets)     do visitAll(t, cb) end end
end

local function catalogueFunction(fn, decompMap)
    -- Each allocation site gets its own slot, even when the same register is
    -- ALLOC_UPVAL'd multiple times in a function (e.g. inside loops). We
    -- forward-walk blocks (in fn.blockIds order which is RPO-ish) and track
    -- the *current* binding from each regKey to a slot index.
    local info = {
        allocs           = {},   -- list of { allocStmt, blockId, stmtIdx, key, localSlotIdx }
        usedUpvalIndices = {},   -- set: N -> true (from R3[N] reads/writes)
        creates          = {},   -- list of { stmt|expr, blockId, stmtIdx,
                                  --   isExpr, captureBindings = [{ kind, idx }] }
        initPair         = {},   -- localSlotIdx -> { writeStmt, blockId, stmtIdx }
        -- Per-IR-node bindings to resolve UPVAL_READ/WRITE indices.
        readWriteBindings    = {},  -- IR statement (table) -> localSlotIdx.
        embeddedReadBindings = {},  -- _irUpvalRead expr table -> localSlotIdx.
    }

    -- A capture-binding tuple has shape { kind, idx } where:
    --   kind == "local" -> idx is a localSlotIdx in this function
    --   kind == "upval" -> idx is an R3[N] index (1-based)
    local function bindingForExpr(expr, currentBinding)
        if isReg(expr) then
            local lsi = currentBinding[regKey(expr)]
            if lsi then return { kind = "local", idx = lsi } end
        end
        local n = asUpvalIndex(expr)
        if n then return { kind = "upval", idx = n } end
        return { kind = "unresolved" }
    end

    -- Walk blocks in reverse-postorder so that allocations happen before
    -- their uses in the linear traversal. The fn.rpo list (built off the
    -- forward CFG) approximates this; non-block synthetic nodes (ENTRY/EXIT)
    -- are filtered out.
    local order = fn.rpo or {}
    if #order == 0 then order = fn.blockIds end
    local currentBinding = {}

    for _, blockId in ipairs(order) do
        local d = decompMap[blockId]
        if d then
            local lastAlloc = nil
            for i, st in ipairs(d.statements) do
                if st.kind == K.UPVAL_ALLOC then
                    local key = regKey(st.target)
                    if key then
                        local rec = {
                            allocStmt   = st, blockId = blockId, stmtIdx = i,
                            key         = key,
                            localSlotIdx = #info.allocs + 1,
                        }
                        table.insert(info.allocs, rec)
                        currentBinding[key] = rec.localSlotIdx
                        lastAlloc = rec
                    end
                elseif st.kind == K.UPVAL_WRITE then
                    if isReg(st.index) then
                        local idxKey = regKey(st.index)
                        local lsi = currentBinding[idxKey]
                        if lsi then
                            info.readWriteBindings[st] = lsi
                            if lastAlloc
                               and lastAlloc.key == idxKey
                               and lastAlloc.blockId == blockId
                               and i == lastAlloc.stmtIdx + 1
                               and not info.initPair[lsi] then
                                info.initPair[lsi] = {
                                    writeStmt = st, blockId = blockId, stmtIdx = i,
                                }
                            end
                        end
                    end
                    local n = asUpvalIndex(st.index)
                    if n then info.usedUpvalIndices[n] = true end
                    lastAlloc = nil
                elseif st.kind == K.UPVAL_READ then
                    if isReg(st.index) then
                        local lsi = currentBinding[regKey(st.index)]
                        if lsi then info.readWriteBindings[st] = lsi end
                    end
                    local n = asUpvalIndex(st.index)
                    if n then info.usedUpvalIndices[n] = true end
                    lastAlloc = nil
                elseif st.kind == K.CREATE_CLOSURE then
                    local bindings = {}
                    for _, expr in ipairs(st.upvalSlots or {}) do
                        table.insert(bindings, bindingForExpr(expr, currentBinding))
                    end
                    table.insert(info.creates, {
                        stmt = st, blockId = blockId, stmtIdx = i, isExpr = false,
                        captureBindings = bindings,
                    })
                    lastAlloc = nil
                else
                    lastAlloc = nil
                end

                -- Always walk this statement's expressions to capture inlined
                -- _irClosure / _irUpvalRead with the binding active at this
                -- statement position.
                visitAll(st, function(node)
                    if node ~= st and node.kind == "_irClosure" then
                        local bindings = {}
                        for _, expr in ipairs(node.upvalSlots or {}) do
                            table.insert(bindings, bindingForExpr(expr, currentBinding))
                        end
                        table.insert(info.creates, {
                            stmt = node, blockId = blockId, stmtIdx = i, isExpr = true,
                            captureBindings = bindings,
                        })
                    end
                    if node.kind == "_irUpvalRead" then
                        if isReg(node.index) then
                            local lsi = currentBinding[regKey(node.index)]
                            if lsi then info.embeddedReadBindings[node] = lsi end
                        end
                        local n = asUpvalIndex(node.index)
                        if n then info.usedUpvalIndices[n] = true end
                    end
                end)
            end
        end
    end

    return info
end

-- ----------------------------------------------------------------------------
-- Second pass: assign global slot ids + resolve upval indices.

local function assignSlots(graph)
    local nextSlot = 0
    local slots = {}    -- slot_id -> { name, allocFn, allocLocalIdx }

    local function newSlot(allocFn, localIdx)
        nextSlot = nextSlot + 1
        local id = nextSlot
        slots[id] = {
            id            = id,
            name          = ("loc_%d"):format(id),
            allocFn       = allocFn,
            allocLocalIdx = localIdx,
        }
        return id
    end

    -- For each function, allocate one global slot per ALLOC_UPVAL in
    -- source order. The mapping is stored in info.localToGlobal[i] where i
    -- is the localSlotIdx (= position in info.allocs).
    for _, fn in ipairs(graph.fns) do
        local info = fn.closureInfo
        info.localToGlobal = {}
        for i, _ in ipairs(info.allocs) do
            info.localToGlobal[i] = newSlot(fn, i)
        end
    end

    -- Resolve a capture binding to a global slot id in fn's context.
    local function resolveBinding(fn, binding)
        if not binding or binding.kind == "unresolved" then return nil end
        local info = fn.closureInfo
        if binding.kind == "local" then
            return info.localToGlobal[binding.idx]
        elseif binding.kind == "upval" then
            return info.slotOfUpval and info.slotOfUpval[binding.idx]
        end
        return nil
    end

    for _, fn in ipairs(graph.fns) do
        fn.closureInfo.slotOfUpval = fn.closureInfo.slotOfUpval or {}
    end

    -- Iterate creates -> children to fixed point: each child fn's upval[i] is
    -- the slot bound at the create site for that capture.
    local changed = true
    local iterations = 0
    while changed do
        iterations = iterations + 1
        if iterations > 32 then break end
        changed = false
        for _, fn in ipairs(graph.fns) do
            for _, c in ipairs(fn.closureInfo.creates) do
                local entryId = c.stmt.entryId
                local childFn = graph.fns[entryId]
                if childFn then
                    childFn.closureInfo.slotOfUpval = childFn.closureInfo.slotOfUpval or {}
                    for i, b in ipairs(c.captureBindings or {}) do
                        if not childFn.closureInfo.slotOfUpval[i] then
                            local s = resolveBinding(fn, b)
                            if s then
                                childFn.closureInfo.slotOfUpval[i] = s
                                changed = true
                            end
                        end
                    end
                end
            end
        end
    end

    return slots
end

-- ----------------------------------------------------------------------------
-- Public API.

-- ----------------------------------------------------------------------------
-- IR rewriting: tag every closure-related IR node with the slot information
-- we just resolved, so the printer can present human-readable names without
-- having to traverse the closure graph again.

local function rewriteFunction(fn, slots, decompMap)
    local info = fn.closureInfo
    if not info then return end

    local function resolveLsi(lsi)
        if not lsi then return nil end
        return info.localToGlobal[lsi]
    end

    -- 1) UPVAL_ALLOC: tag every alloc with its slot name. If there's a paired
    --    immediate UPVAL_WRITE init, also tag the init with initSlotName so
    --    we can render `local <name> = <value>` and drop the alloc line.
    for _, rec in ipairs(info.allocs) do
        local sid = info.localToGlobal[rec.localSlotIdx]
        local slot = sid and slots[sid] or nil
        if slot and rec.allocStmt then
            rec.allocStmt.slotName = slot.name
            rec.allocStmt.slotId   = sid
            local p = info.initPair[rec.localSlotIdx]
            if p and p.writeStmt then
                p.writeStmt.initSlotName = slot.name
                p.writeStmt.initSlotId   = sid
                rec.allocStmt.initStmt   = p.writeStmt
            end
        end
    end

    -- 2) Walk all statements + sub-expressions and resolve UPVAL_READ /
    --    UPVAL_WRITE (and embedded _irUpvalRead) using readWriteBindings /
    --    embeddedReadBindings (regref case) or slotOfUpval (R3[N] case).
    --    Also tag _irClosure / CREATE_CLOSURE upvalSlot expressions with
    --    names, using captureBindings recorded at the create site.
    for _, blockId in ipairs(fn.blockIds) do
        local d = decompMap[blockId]
        if d then
            for _, st in ipairs(d.statements) do
                visitAll(st, function(e)
                    if type(e) ~= "table" then return end
                    if e.kind == "_irUpvalRead" then
                        local sid = resolveLsi(info.embeddedReadBindings[e])
                        if not sid then
                            local n = asUpvalIndex(e.index)
                            if n then sid = info.slotOfUpval[n] end
                        end
                        if sid then
                            e.slotId   = sid
                            e.slotName = slots[sid].name
                        end
                    end
                end)

                if st.kind == K.UPVAL_READ or st.kind == K.UPVAL_WRITE then
                    local sid = resolveLsi(info.readWriteBindings[st])
                    if not sid then
                        local n = asUpvalIndex(st.index)
                        if n then sid = info.slotOfUpval[n] end
                    end
                    if sid then
                        st.slotId   = sid
                        st.slotName = slots[sid].name
                    end
                end
            end
        end
    end

    -- 3) Tag every recorded create (statement and inlined-expression) with
    --    captured-slot names from its captureBindings.
    local function nameFor(fn_, binding)
        if not binding or binding.kind == "unresolved" then return nil end
        local i = fn_.closureInfo
        if binding.kind == "local" then
            local sid = i.localToGlobal[binding.idx]
            return sid and slots[sid].name or nil
        elseif binding.kind == "upval" then
            local sid = i.slotOfUpval[binding.idx]
            return sid and slots[sid].name or nil
        end
        return nil
    end

    for _, c in ipairs(info.creates) do
        local node = c.stmt
        local names = {}
        for i, b in ipairs(c.captureBindings or {}) do
            names[i] = nameFor(fn, b)
        end
        node.upvalNames = names
    end
end

function M.analyze(graph)
    -- Pass 1: per-function catalogue.
    for _, fn in ipairs(graph.fns) do
        fn.closureInfo = catalogueFunction(fn, graph.decompMap)
    end
    -- Pass 2: global slot assignment + per-function upval slot mapping.
    local slots = assignSlots(graph)
    graph.slots = slots
    -- Pass 3: IR rewrite -- tag nodes with slot names.
    for _, fn in ipairs(graph.fns) do
        rewriteFunction(fn, slots, graph.decompMap)
    end
    return graph
end

return M
