-- prometheus-test-deobfuscator -- structural recognition.
--
-- Walks each function's CFG and produces a tree of "structured statements":
--
--   { kind = "block",   id, statements = [ ir-stmts... ] }
--   { kind = "if",      cond = condStmt, thenBody = node, elseBody = node? }
--   { kind = "while",   cond = condExpr, invert = bool, body = node }
--   { kind = "for_num", varReg, initExpr, limitExpr, stepExpr, body = node }
--   { kind = "for_in",  varRegs, exprList, body = node }
--   { kind = "loop",    body = node }                          -- generic
--   { kind = "return"   }
--   { kind = "goto",    target = id, info = "<reason>" }       -- fallback
--   { kind = "loop_cond"... }                                  -- fallback
--
-- M4 adds while / for-num / for-in reconstruction. Any natural loop whose
-- header is a JUMP_COND becomes a `while` (or specialised `for_num` / `for_in`
-- if the canonical pattern matches). Back-edges become "implicit continue"
-- (i.e. the body just stops, since the next iteration starts from the header
-- again).

local cfg = require("deobfuscator.steps.vmify.cfg")
local ir  = require("deobfuscator.steps.vmify.ir")
local Ast = require("prometheus.ast")
local AstKind = Ast.AstKind
local K   = ir.kinds

local M = {}

local isReg = ir.isReg

-- --------------------------------------------------------------------------
-- Helpers.

local function regEq(a, b)
    if not a or not b then return false end
    if isReg(a) and isReg(b) then return a.scope == b.scope and a.id == b.id end
    if a.scope and b.scope then return a.scope == b.scope and a.id == b.id end
    return false
end

local function getDecomp(s, id)
    return s.decompMap[id]
end

local function findJumpCond(d)
    for i = #d.statements, 1, -1 do
        local st = d.statements[i]
        if st.kind == K.JUMP_COND then return st end
    end
    return nil
end

local function blockStmtsExceptControl(d)
    local out = {}
    for _, st in ipairs(d.statements) do
        if st.kind ~= K.NOP
           and st.kind ~= K.JUMP_CONST
           and st.kind ~= K.JUMP_COND
           and st.kind ~= K.RETURN then
            table.insert(out, st)
        end
    end
    return out
end

-- ----------------------------------------------------------------------------
-- For-num cond decoder.
--
-- Vmify's for_statement.lua emits the canonical "stay in loop" cond:
--
--   (signNeg AND var >= limit) OR ((not signNeg) AND limit >= var)
--
-- but it shuffles operand order via `math.random(1,2)` for both comparisons.
-- We accept either side of `>=` / `<=` for each variant.
--
-- Returns { signReg, varReg, limitReg } on success; nil on failure.

-- Decoders that accept BOTH raw Prometheus AST nodes (AstKind.OrExpression
-- etc.) AND the synthetic `_irBinop` / `_irUnop` nodes the inliner emits
-- when it folds register references into expressions.

local OP_AST_KIND = {
    ["or"]  = AstKind.OrExpression,
    ["and"] = AstKind.AndExpression,
    ["<"]   = AstKind.LessThanExpression,
    [">"]   = AstKind.GreaterThanExpression,
    ["<="]  = AstKind.LessThanOrEqualsExpression,
    [">="]  = AstKind.GreaterThanOrEqualsExpression,
    ["=="]  = AstKind.EqualsExpression,
    ["~="]  = AstKind.NotEqualsExpression,
}

local function decodeBinopAny(e, opName)
    if not e then return nil end
    if e.kind == "_irBinop" and e.op == opName then return e.lhs, e.rhs end
    if e.kind == OP_AST_KIND[opName] then return e.lhs, e.rhs end
    return nil
end

local function decodeOr(e)  return decodeBinopAny(e, "or")  end
local function decodeAnd(e) return decodeBinopAny(e, "and") end
local function decodeNot(e)
    if not e then return nil end
    if e.kind == "_irUnop" and (e.op == "not " or e.op == "not") then return e.rhs end
    if e.kind == AstKind.NotExpression then return e.rhs end
    return nil
end

local function decodeBinop(e, opName) return decodeBinopAny(e, opName) end

-- Match the for-num canonical cond.
local function matchForNumCond(cond)
    local lhs, rhs = decodeOr(cond)
    if not lhs then return nil end

    -- LEFT half: signNeg AND <neg-step continue cond>.
    -- Negative-step continue cond accepts:
    --     var >= limit  (canonical)
    --   | limit <= var  (shuffled)
    local sa, sb = decodeAnd(lhs)
    if not sa or not isReg(sa) then return nil end
    local sign = sa

    local function decodeNegStep(n)
        local v, l = decodeBinop(n, ">=")
        if v then return v, l end
        l, v = decodeBinop(n, "<=")
        if l then return v, l end
        return nil
    end
    local function decodePosStep(n)
        -- Positive-step continue cond accepts:
        --     limit >= var (canonical)  [post-shuffle: l, v]
        --   | var   <= limit (shuffled) [post-shuffle: v, l]
        local l, v = decodeBinop(n, ">=")
        if l then return v, l end
        v, l = decodeBinop(n, "<=")
        if v then return v, l end
        return nil
    end

    local var1, lim1 = decodeNegStep(sb)
    if not var1 then return nil end

    -- RIGHT half: (not signNeg) AND <pos-step continue cond>.
    local na, nb = decodeAnd(rhs)
    if not na then return nil end
    local naInner = decodeNot(na)
    if not naInner or not regEq(naInner, sign) then return nil end
    local var2, lim2 = decodePosStep(nb)
    if not var2 then return nil end

    if not regEq(var1, var2) or not regEq(lim1, lim2) then return nil end
    return { signReg = sign, varReg = var1, limitReg = lim1 }
end

-- ----------------------------------------------------------------------------
-- For-num pattern recognition.
--
-- For Vmify's for-num lowering:
--   - Pre-header sets:
--       limit  = <finalExpr>          -- LOAD or COPY into limitReg
--       step   = <stepExpr>           -- LOAD or COPY into stepReg
--       signNeg = (0 > step) OR (step < 0)  (both equivalent)
--       var    = init - step          -- BINOP "-"
--   - Header starts with `var = var + step` (BINOP "+")
--   - Header ends with the canonical JUMP_COND cond.
--
-- We extract:
--   varReg, limitExpr, stepExpr, initExpr (= varInit + stepReg)
-- by walking the pre-header backwards and matching the most recent writer
-- to each role-register.

local function isBinopReg(s, op, target)
    if s.kind ~= K.BINOP then return false end
    if s.op ~= op then return false end
    if not regEq(s.target, target) then return false end
    return true
end

-- Find the last write to a register in a list of stmts; return (index, stmt).
local function findLastWrite(stmts, reg)
    for i = #stmts, 1, -1 do
        local s = stmts[i]
        local writesReg = nil
        if s.kind == K.LOAD or s.kind == K.COPY or s.kind == K.BINOP
           or s.kind == K.UNOP or s.kind == K.ARG_READ or s.kind == K.UPVAL_READ
           or s.kind == K.UPVAL_ALLOC or s.kind == K.GLOBAL_READ
           or s.kind == K.INDEX_READ or s.kind == K.CREATE_CLOSURE then
            writesReg = s.target
        elseif s.kind == K.CALL then
            -- Only consider single-target captures here.
            if s.targets and #s.targets == 1 then writesReg = s.targets[1] end
        end
        if writesReg and regEq(writesReg, reg) then return i, s end
    end
    return nil
end

-- Get a "value expression" from an IR write-statement, suitable for
-- substituting where the target was used. Returns nil if not extractable.
local function valueOf(s)
    if s.kind == K.LOAD then return s.value end
    if s.kind == K.COPY then return s.source end
    if s.kind == K.BINOP then
        return { kind = "_irBinop", op = s.op, lhs = s.lhs, rhs = s.rhs }
    end
    if s.kind == K.UNOP then
        return { kind = "_irUnop", op = s.op, rhs = s.rhs }
    end
    if s.kind == K.ARG_READ then
        return { kind = "_irArgRead", index = s.index }
    end
    if s.kind == K.UPVAL_READ then
        return { kind = "_irUpvalRead", index = s.index }
    end
    if s.kind == K.GLOBAL_READ then
        return { kind = "_irGlobalRead", name = s.name }
    end
    if s.kind == K.INDEX_READ then
        return { kind = "_irIndexRead", base = s.base, index = s.index }
    end
    if s.kind == K.CALL and s.targets and #s.targets == 1 then
        return { kind = "_irCall", base = s.base, args = s.args,
                 tableWrapped = s.tableWrapped }
    end
    return nil
end

local function tryForNum(s, fn, loop, headerD, preHeaderD)
    local jc = findJumpCond(headerD)
    if not jc or not jc.cond then return nil end
    local matched = matchForNumCond(jc.cond)
    if not matched then return nil end

    -- Header should also contain `var = var + step` BEFORE the JUMP_COND.
    -- The inliner often turns this into the cond itself; if so, the BINOP
    -- target=varReg might appear inside the JUMP_COND lhs/rhs. We also
    -- tolerate a missing var-update statement if the inliner consumed it.
    local headerStmts = blockStmtsExceptControl(headerD)
    local stepReg
    -- Walk header for a `var = var + ?` or `var = ? + var` BINOP.
    for _, st in ipairs(headerStmts) do
        if st.kind == K.BINOP and st.op == "+" and regEq(st.target, matched.varReg) then
            if isReg(st.lhs) and regEq(st.lhs, matched.varReg) and isReg(st.rhs) then
                stepReg = st.rhs
            elseif isReg(st.rhs) and regEq(st.rhs, matched.varReg) and isReg(st.lhs) then
                stepReg = st.lhs
            end
            break
        end
    end

    if not preHeaderD then return nil end
    local preStmts = blockStmtsExceptControl(preHeaderD)

    -- The pre-header should:
    --   1. Write to varReg via `varReg = init - stepReg` (BINOP "-").
    --   2. Write to a sign register (signReg) via either `0 > stepReg` or
    --      `stepReg < 0` (both meaning step is negative).
    --   3. The stepReg has been written (LOAD / COPY) earlier with the step
    --      expression.
    --   4. The limitReg has been written with the limit expression.
    --
    -- We scan preStmts looking for these.
    local varInitStmt
    for i = #preStmts, 1, -1 do
        local st = preStmts[i]
        if st.kind == K.BINOP and st.op == "-" and regEq(st.target, matched.varReg) then
            varInitStmt = st
            break
        end
    end
    if not varInitStmt then return nil end

    -- step register: rhs of varInitStmt's BINOP "-", which is `init - step`.
    local stepReg2 = varInitStmt.rhs
    if not stepReg or not regEq(stepReg, stepReg2) then
        -- The header's step register should match.
        if isReg(stepReg2) then
            stepReg = stepReg2
        else
            return nil
        end
    end
    local initExpr = varInitStmt.lhs

    -- signReg detection: a BINOP > or < where one side is stepReg, other is 0.
    local foundSign = false
    for _, st in ipairs(preStmts) do
        if st.kind == K.BINOP and (st.op == ">" or st.op == "<")
           and regEq(st.target, matched.signReg) then
            local function isZero(e)
                return e and e.kind == AstKind.NumberExpression and e.value == 0
            end
            if (isZero(st.lhs) and isReg(st.rhs) and regEq(st.rhs, stepReg))
            or (isReg(st.lhs) and regEq(st.lhs, stepReg) and isZero(st.rhs)) then
                foundSign = true
                break
            end
        end
    end
    if not foundSign then return nil end

    -- Limit expression: last write to limitReg in preStmts.
    local _, limitStmt = findLastWrite(preStmts, matched.limitReg)
    local limitExpr
    if limitStmt then
        limitExpr = valueOf(limitStmt) or matched.limitReg
    else
        limitExpr = matched.limitReg
    end

    -- Step expression: last write to stepReg in preStmts.
    local _, stepStmt = findLastWrite(preStmts, stepReg)
    local stepExpr
    if stepStmt then
        stepExpr = valueOf(stepStmt) or stepReg
    else
        stepExpr = stepReg
    end

    return {
        varReg     = matched.varReg,
        limitReg   = matched.limitReg,
        stepReg    = stepReg,
        signReg    = matched.signReg,
        initExpr   = initExpr,
        limitExpr  = limitExpr,
        stepExpr   = stepExpr,
    }
end

-- ----------------------------------------------------------------------------
-- For-in pattern recognition.
--
-- For Vmify's for-in lowering:
--   - Pre-header contains `tmp = <explistResult>` where explistResult is
--     either:
--       (a) a TableConstructorExpression of three positional items
--           (when the explist is e.g. `iter, state, var` literal triples),
--       (b) a CALL with `tableWrapped=true` (when the explist is a single
--           expression returning multiple values, e.g. `pairs(t)` or
--           `next, t, nil`).
--   - Pre-header has three INDEX_READs: iterReg = tmp[1], stateReg = tmp[2],
--     varReg = tmp[3].
--   - Header has a CALL: `[varReg, secondVarReg?] = iterReg(stateReg, varReg)`.
--   - Header's JUMP_COND cond is just `varReg`.
--
-- We extract:
--   iterReg, stateReg, varReg, secondVarReg (or nil), explistInfo

local function regKey(r)
    if not isReg(r) then return nil end
    return tostring(r.scope) .. ":" .. tostring(r.id)
end

-- Forward-simulate the pre-header to track each register's "source": for an
-- INDEX_READ from a common tmp base, source = "tmp_idx_<N>". COPY propagates
-- the source. Other writes clear the source. Returns:
--   sources    : map regKey -> "tmp_idx_<N>" or nil
--   tmpBase    : the (presumed unique) tmp register; nil if ambiguous
--   tmpWriter  : the IR stmt that wrote tmpBase (LOAD or table-wrapped CALL)
local function trackPreheaderSources(preStmts)
    local sources = {}
    local tmpCounts = {}   -- regKey -> count of INDEX_READs pointing to it
    local tmpWriterByKey = {}  -- regKey -> writer stmt

    -- First pass: figure out which register acts as the "tmp" base. We pick
    -- the base used by the most INDEX_READs (with indices that are integer
    -- literals 1/2/3).
    for _, st in ipairs(preStmts) do
        if st.kind == K.INDEX_READ and isReg(st.base)
           and st.index and st.index.kind == AstKind.NumberExpression
           and (st.index.value == 1 or st.index.value == 2 or st.index.value == 3) then
            local k = regKey(st.base)
            tmpCounts[k] = (tmpCounts[k] or 0) + 1
        end
    end
    local tmpKey, tmpKeyCount
    for k, c in pairs(tmpCounts) do
        if not tmpKey or c > tmpKeyCount then tmpKey, tmpKeyCount = k, c end
    end
    if not tmpKey or tmpKeyCount < 3 then return nil end

    -- Forward simulate. Track regSource and capture the writer of the tmp.
    local tmpBase
    local tmpWriter
    for _, st in ipairs(preStmts) do
        local writeReg, writeSource = nil, nil
        if st.kind == K.INDEX_READ then
            if isReg(st.base) and regKey(st.base) == tmpKey
               and st.index and st.index.kind == AstKind.NumberExpression then
                writeReg = st.target
                writeSource = "tmp_idx_" .. tostring(st.index.value)
            else
                writeReg = st.target
                writeSource = nil
            end
        elseif st.kind == K.COPY then
            writeReg = st.target
            local srcKey = regKey(st.source)
            writeSource = srcKey and sources[srcKey] or nil
        elseif st.kind == K.LOAD then
            writeReg = st.target
            if isReg(st.target) and regKey(st.target) == tmpKey
               and st.value and st.value.kind == AstKind.TableConstructorExpression then
                tmpBase = st.target
                tmpWriter = { kind = "table", value = st.value }
            end
            writeSource = nil
        elseif st.kind == K.CALL then
            -- Single-target table-wrapped CALL into tmpKey is a candidate
            -- explist source; multi-target CALLs and others wipe sources.
            if st.targets then
                if #st.targets == 1 and isReg(st.targets[1])
                   and regKey(st.targets[1]) == tmpKey and st.tableWrapped then
                    tmpBase = st.targets[1]
                    tmpWriter = { kind = "call", base = st.base, args = st.args,
                                  passSelfName = st.passSelfName }
                end
                for _, t in ipairs(st.targets) do
                    sources[regKey(t)] = nil
                end
            end
            writeReg = nil  -- handled
        elseif st.kind == K.BINOP or st.kind == K.UNOP
               or st.kind == K.ARG_READ or st.kind == K.UPVAL_READ
               or st.kind == K.UPVAL_ALLOC or st.kind == K.GLOBAL_READ
               or st.kind == K.CREATE_CLOSURE then
            writeReg = st.target
            writeSource = nil
        end
        if writeReg then
            sources[regKey(writeReg)] = writeSource
        end
    end

    -- If the tmp register's writer wasn't found via LOAD/CALL pattern,
    -- bail out (we can't reconstruct the explist).
    if not tmpWriter then return nil end

    return {
        sources    = sources,
        tmpBase    = tmpBase,
        tmpWriter  = tmpWriter,
    }
end

local function tryForIn(s, fn, loop, headerD, preHeaderD)
    local jc = findJumpCond(headerD)
    if not jc or not jc.cond then return nil end
    if not isReg(jc.cond) then return nil end
    local condVarReg = jc.cond

    -- Header contains a CALL with first target = condVarReg.
    local headerStmts = blockStmtsExceptControl(headerD)
    local callStmt
    for _, st in ipairs(headerStmts) do
        if st.kind == K.CALL and st.targets and #st.targets >= 1
           and regEq(st.targets[1], condVarReg) then
            callStmt = st
            break
        end
    end
    if not callStmt then return nil end
    -- The CALL's base is iterReg, args are (stateReg, varReg).
    local iterReg = callStmt.base
    local args = callStmt.args
    if not isReg(iterReg) then return nil end
    if #args ~= 2 then return nil end
    local stateReg, varReg = args[1], args[2]
    if not isReg(stateReg) or not isReg(varReg) then return nil end
    if not regEq(varReg, condVarReg) then return nil end

    local secondVarReg = callStmt.targets[2]  -- may be nil

    if not preHeaderD then return nil end
    local preStmts = blockStmtsExceptControl(preHeaderD)
    local tracked = trackPreheaderSources(preStmts)
    if not tracked then return nil end

    -- After the pre-header runs, iterReg/stateReg/varReg should resolve to
    -- "tmp_idx_1" / "tmp_idx_2" / "tmp_idx_3" respectively.
    local function expect(reg, want)
        local k = regKey(reg)
        if not k then return false end
        return tracked.sources[k] == want
    end
    if not expect(iterReg, "tmp_idx_1")
       or not expect(stateReg, "tmp_idx_2")
       or not expect(varReg,  "tmp_idx_3") then
        return nil
    end

    return {
        iterReg      = iterReg,
        stateReg     = stateReg,
        varReg       = varReg,
        secondVarReg = secondVarReg,
        explistInfo  = tracked.tmpWriter,
    }
end

-- ----------------------------------------------------------------------------
-- Loop structuring.
--
-- For each natural loop, decide which branch of the header's JUMP_COND
-- enters the loop body (continue cond) vs exits (break cond), pattern-
-- match for-num / for-in, and emit a structured loop node.

local function isBackEdge(fn, fromId, toId)
    -- Back-edge if `toId` dominates `fromId`.
    return cfg.dominates(fn, toId, fromId)
end

-- Forward-declare structureRange (needed by structureLoop).
local structureRange

-- Structure the body of a loop. Walk from `bodyEntry` until we hit:
--   - a back-edge to `header`  -> stop (next iteration starts implicitly)
--   - an exit edge out of `loop.bodySet` -> stop (the post-loop code is
--                                            structured elsewhere by the caller)
--   - the header itself        -> stop
-- Returns the structured body.

local function structureLoopBody(s, fn, loop, bodyEntry, visited)
    local out = {}
    local id = bodyEntry

    while id and id ~= cfg.EXIT do
        if not loop.bodySet[id] then
            -- Stepped outside the loop -> stop here; the post-loop code is
            -- structured by the caller.
            return out, id
        end
        if id == loop.header then
            -- Reached header again: implicit continue.
            return out, id
        end
        if visited[id] then
            table.insert(out, { kind = "goto", target = id, info = "revisit" })
            return out, nil
        end
        visited[id] = true

        local d = getDecomp(s, id)
        if not d then
            table.insert(out, { kind = "goto", target = id, info = "unknown-block" })
            return out, nil
        end

        -- Emit IR statements (excluding control exits).
        local stmts = blockStmtsExceptControl(d)
        table.insert(out, {
            kind = "block", id = id, statements = stmts,
        })

        -- Follow exit.
        if d.exitKind == "return" then
            table.insert(out, { kind = "return" })
            return out, nil
        elseif d.exitKind == "fallthrough" or d.exitKind == "other" then
            return out, nil
        elseif d.exitKind == "jump_const" then
            local nxt = d.exitTarget
            if nxt == loop.header then
                return out, nil  -- implicit continue
            end
            if not loop.bodySet[nxt] then
                return out, nxt
            end
            id = nxt
        elseif d.exitKind == "jump_cond" then
            local trueId  = d.exitTargets[1]
            local falseId = d.exitTargets[2]

            -- Inner natural loop?
            local inner = fn.loopHeader[trueId] or fn.loopHeader[falseId]
            if inner and inner ~= loop and (trueId == inner.header or falseId == inner.header) then
                -- Defer to structureRange's loop-handling.
                -- Fall through to general structurer.
            end

            -- Detect back-edges.
            local trueBack  = isBackEdge(fn, id, trueId)
            local falseBack = isBackEdge(fn, id, falseId)
            if trueBack or falseBack then
                -- One side jumps back to a (possibly outer) loop header.
                -- For our innermost loop, treat as continue.
                if trueBack and trueId == loop.header then
                    -- True branch is implicit continue. Else branch may or
                    -- may not be in the loop; structure it accordingly.
                    if loop.bodySet[falseId] then
                        local elseBranch
                        elseBranch, id = structureLoopBody(s, fn, loop, falseId, visited)
                        table.insert(out, {
                            kind     = "if",
                            cond     = d,
                            thenBody = {},  -- continue
                            elseBody = elseBranch,
                        })
                    else
                        -- Exit is the FALSE branch -> emit `if not cond then break end`
                        table.insert(out, {
                            kind = "if",
                            cond = d,
                            thenBody = {},  -- continue
                            elseBody = { { kind = "break" } },
                        })
                        return out, falseId
                    end
                elseif falseBack and falseId == loop.header then
                    if loop.bodySet[trueId] then
                        local thenBranch
                        thenBranch, id = structureLoopBody(s, fn, loop, trueId, visited)
                        table.insert(out, {
                            kind     = "if",
                            cond     = d,
                            thenBody = thenBranch,
                            elseBody = {},  -- continue
                        })
                    else
                        -- Exit is the TRUE branch -> emit `if cond then break end`
                        table.insert(out, {
                            kind = "if",
                            cond = d,
                            thenBody = { { kind = "break" } },
                            elseBody = {},
                        })
                        return out, trueId
                    end
                else
                    -- Back-edge goes elsewhere (outer loop?). Treat as goto.
                    table.insert(out, { kind = "loop_cond",
                                        condRaw = d,
                                        trueTarget = trueId, falseTarget = falseId,
                                        trueBack = trueBack, falseBack = falseBack })
                    return out, nil
                end
            else
                -- Plain if inside the body. Use the existing if-then-else logic.
                -- We delegate to structureRange which handles the if pattern.
                -- But since we need to stay within the loop, we'll inline it here.
                local merge = fn.ipdom[id]
                local thenBranch, thenStop = structureLoopBody(s, fn, loop, trueId, visited)
                local elseBranch, elseStop = structureLoopBody(s, fn, loop, falseId, visited)
                table.insert(out, {
                    kind     = "if",
                    cond     = d,
                    thenBody = thenBranch,
                    elseBody = elseBranch,
                })
                -- Continue from the merge if it's still in the loop body.
                if merge == cfg.EXIT or merge == nil then
                    return out, nil
                elseif not loop.bodySet[merge] then
                    return out, merge
                else
                    id = merge
                end
            end
        else
            return out, nil
        end
    end

    return out, nil
end

local function structureLoop(s, fn, loop, visited)
    local headerD = getDecomp(s, loop.header)
    if not headerD then
        return { kind = "goto", target = loop.header, info = "loop-header-missing" }, nil
    end

    -- Mark header visited so structureRange won't re-enter.
    visited[loop.header] = true

    local jc = findJumpCond(headerD)
    if not jc then
        -- Header has no JUMP_COND -> the loop's exit (if any) is in the body.
        -- This typically arises from a "do-while" pattern where the body
        -- entry was a non-header block.  Emit the header's own statements
        -- first, then continue structuring the rest of the body.
        local body = {}
        local headerStmts = blockStmtsExceptControl(headerD)
        if headerStmts and #headerStmts > 0 then
            table.insert(body, { kind = "block", id = loop.header, statements = headerStmts })
        end
        local bodyEntry
        for _, k in ipairs(fn.succs[loop.header] or {}) do
            if loop.bodySet[k] and k ~= loop.header then bodyEntry = k; break end
        end
        local exitId
        if bodyEntry and bodyEntry ~= loop.header then
            local bodyVisited = {}
            for k, v in pairs(visited) do bodyVisited[k] = v end
            -- Clear loop body blocks so they can be emitted inside the loop.
            for id in pairs(loop.bodySet) do
                if id ~= loop.header then bodyVisited[id] = nil end
            end
            local rest
            rest, exitId = structureLoopBody(s, fn, loop, bodyEntry, bodyVisited)
            for _, n in ipairs(rest) do table.insert(body, n) end
        end
        for id in pairs(loop.bodySet) do visited[id] = true end
        return { kind = "loop", body = body }, exitId
    end

    local trueId  = jc.trueTarget
    local falseId = jc.falseTarget

    local trueInBody  = loop.bodySet[trueId]
    local falseInBody = loop.bodySet[falseId]

    local invert
    local bodyEntry, exitTarget
    if trueInBody and not falseInBody then
        bodyEntry = trueId; exitTarget = falseId; invert = false
    elseif falseInBody and not trueInBody then
        bodyEntry = falseId; exitTarget = trueId; invert = true
    elseif trueInBody and falseInBody then
        -- Both sides in loop -- treat as `while true` with internal break.
        bodyEntry = trueId; exitTarget = nil; invert = false
    else
        -- Neither side in loop -- shouldn't happen for a natural loop.
        return { kind = "goto", target = loop.header, info = "loop-header-degenerate" }, nil
    end

    -- Try for-num / for-in pattern matchers.
    local preHeaderD
    if loop.preheader then
        preHeaderD = getDecomp(s, loop.preheader)
    end

    local forNum = tryForNum(s, fn, loop, headerD, preHeaderD)
    local forIn  = tryForIn(s, fn, loop, headerD, preHeaderD)

    -- Statements emitted from the header BEFORE its var-update / iter-call
    -- (typically nothing for for-num, but for-in headers may emit nil-clears).
    local headerStmts = blockStmtsExceptControl(headerD)

    -- Body: structure starting from bodyEntry; mark all body blocks visited.
    local bodyVisited = {}
    for k, v in pairs(visited) do bodyVisited[k] = v end
    -- Reset header so the body block (which is downstream of header) doesn't
    -- "skip" the header-mark; we already set it above as visited.
    bodyVisited[loop.header] = true
    -- Clear visited status for loop body blocks so that blocks entered via
    -- a "do-while" pre-header path (visited before the loop was recognized)
    -- can still be emitted inside the loop body.
    for id in pairs(loop.bodySet) do
        if id ~= loop.header then bodyVisited[id] = nil end
    end

    local body = {}
    if bodyEntry and bodyEntry ~= loop.header then
        body, _ = structureLoopBody(s, fn, loop, bodyEntry, bodyVisited)
    end

    -- Mark body-set as visited globally so post-loop code doesn't re-enter.
    for id in pairs(loop.bodySet) do visited[id] = true end

    if forNum then
        return {
            kind       = "for_num",
            varReg     = forNum.varReg,
            initExpr   = forNum.initExpr,
            limitExpr  = forNum.limitExpr,
            stepExpr   = forNum.stepExpr,
            consumed   = {  -- registers whose pre-header writes were folded
                limitReg = forNum.limitReg,
                stepReg  = forNum.stepReg,
                signReg  = forNum.signReg,
                varReg   = forNum.varReg,
            },
            body       = body,
        }, exitTarget
    end

    if forIn then
        return {
            kind         = "for_in",
            varReg       = forIn.varReg,
            secondVarReg = forIn.secondVarReg,
            iterReg      = forIn.iterReg,
            stateReg     = forIn.stateReg,
            explistInfo  = forIn.explistInfo,
            body         = body,
        }, exitTarget
    end

    return {
        kind         = "while",
        cond         = jc.cond,
        invert       = invert,
        body         = body,
        headerStmts  = headerStmts,
    }, exitTarget
end

-- ----------------------------------------------------------------------------
-- General structuring driver.

structureRange = function(s, fn, startId, stopAt, visited)
    local out = {}
    local id = startId

    while id and id ~= stopAt and id ~= cfg.EXIT do
        if visited[id] then
            table.insert(out, { kind = "goto", target = id, info = "revisit" })
            return out
        end

        -- If `id` is a loop header, structure the loop.
        local loop = fn.loopHeader[id]
        if loop and not visited[id] then
            local node, exitTarget = structureLoop(s, fn, loop, visited)
            table.insert(out, node)
            id = exitTarget
            -- Continue from the loop's exit target (post-loop code).
        else
            visited[id] = true

            local d = getDecomp(s, id)
            if not d then
                table.insert(out, { kind = "goto", target = id, info = "unknown-block" })
                return out
            end

            local stmts = blockStmtsExceptControl(d)
            table.insert(out, {
                kind = "block", id = id, statements = stmts,
            })

            if d.exitKind == "return" then
                table.insert(out, { kind = "return" })
                id = nil

            elseif d.exitKind == "fallthrough" or d.exitKind == "other" then
                id = nil

            elseif d.exitKind == "jump_const" then
                local nxt = d.exitTarget
                if isBackEdge(fn, id, nxt) then
                    table.insert(out, { kind = "goto", target = nxt, info = "back-edge" })
                    id = nil
                else
                    id = nxt
                end

            elseif d.exitKind == "jump_cond" then
                local trueId  = d.exitTargets[1]
                local falseId = d.exitTargets[2]

                local trueBack  = isBackEdge(fn, id, trueId)
                local falseBack = isBackEdge(fn, id, falseId)
                if trueBack or falseBack then
                    table.insert(out, {
                        kind = "loop_cond",
                        condRaw  = d,
                        trueTarget = trueId, falseTarget = falseId,
                        trueBack = trueBack, falseBack = falseBack,
                    })
                    id = nil
                else
                    local merge = fn.ipdom[id]
                    local thenStop, elseStop = merge, merge

                    local thenBranch = structureRange(s, fn, trueId,  thenStop, visited)
                    local elseBranch = structureRange(s, fn, falseId, elseStop, visited)

                    table.insert(out, {
                        kind     = "if",
                        cond     = d,
                        thenBody = thenBranch,
                        elseBody = elseBranch,
                    })

                    if merge == cfg.EXIT or merge == nil then
                        id = nil
                    else
                        id = merge
                    end
                end
            else
                id = nil
            end
        end
    end

    return out
end

-- --------------------------------------------------------------------------
-- Public API.

function M.structure(graph)
    local out = { fns = {} }
    for _, fn in ipairs(graph.fns) do
        local visited = {}
        local body = structureRange({ decompMap = graph.decompMap }, fn,
                                    fn.entryId, nil, visited)
        local f = {
            entryId = fn.entryId,
            isMain  = fn.isMain,
            body    = body,
        }
        table.insert(out.fns, f)
        out.fns[fn.entryId] = f
    end
    return out
end

-- --------------------------------------------------------------------------
-- Pretty printer.

local function indent(n) return string.rep("  ", n) end

local function condString(d)
    for i = #d.statements, 1, -1 do
        local s = d.statements[i]
        if s.kind == K.JUMP_COND then
            return ir.exprString(s.cond)
        end
    end
    return "<no-cond>"
end

local printBody

local function printForNumExpr(node)
    return ("for %s = %s, %s, %s do"):format(
        ir.regString(node.varReg),
        ir.exprString(node.initExpr),
        ir.exprString(node.limitExpr),
        ir.exprString(node.stepExpr))
end

local function printForInExpr(node)
    local vars = { ir.regString(node.varReg) }
    if node.secondVarReg then table.insert(vars, ir.regString(node.secondVarReg)) end
    local exprStr
    if node.explistInfo.kind == "table" then
        local entries = {}
        for _, e in ipairs(node.explistInfo.value.entries) do
            if e.kind == AstKind.TableEntry then
                table.insert(entries, ir.exprString(e.value))
            end
        end
        exprStr = table.concat(entries, ", ")
    else
        local args = {}
        for _, a in ipairs(node.explistInfo.args) do
            table.insert(args, ir.exprString(a))
        end
        exprStr = ir.exprString(node.explistInfo.base) .. "(" .. table.concat(args, ", ") .. ")"
    end
    return ("for %s in %s do"):format(table.concat(vars, ", "), exprStr)
end

printBody = function(body, depth, write)
    for _, node in ipairs(body) do
        if node.kind == "block" then
            for _, st in ipairs(node.statements) do
                -- Drop the bare UPVAL_ALLOC line when it has a paired init;
                -- the upcoming UPVAL_WRITE will print the `local <name> =
                -- <init>` line and stand in for both.
                if st.kind == K.UPVAL_ALLOC and st.initStmt then
                    -- skip (no output)
                else
                    write(indent(depth) .. ir.statString(st))
                end
            end
        elseif node.kind == "if" then
            write(indent(depth) .. "if " .. condString(node.cond) .. " then")
            printBody(node.thenBody, depth + 1, write)
            if node.elseBody and #node.elseBody > 0 then
                write(indent(depth) .. "else")
                printBody(node.elseBody, depth + 1, write)
            end
            write(indent(depth) .. "end")
        elseif node.kind == "while" then
            local condStr = ir.exprString(node.cond)
            if node.invert then condStr = "not (" .. condStr .. ")" end
            write(indent(depth) .. "while " .. condStr .. " do")
            -- Header statements (if any) are emitted at the top of the body.
            if node.headerStmts then
                for _, st in ipairs(node.headerStmts) do
                    write(indent(depth + 1) .. ir.statString(st))
                end
            end
            printBody(node.body, depth + 1, write)
            write(indent(depth) .. "end")
        elseif node.kind == "for_num" then
            write(indent(depth) .. printForNumExpr(node))
            printBody(node.body, depth + 1, write)
            write(indent(depth) .. "end")
        elseif node.kind == "for_in" then
            write(indent(depth) .. printForInExpr(node))
            printBody(node.body, depth + 1, write)
            write(indent(depth) .. "end")
        elseif node.kind == "loop" then
            write(indent(depth) .. "while true do")
            printBody(node.body, depth + 1, write)
            write(indent(depth) .. "end")
        elseif node.kind == "return" then
            write(indent(depth) .. "return")
        elseif node.kind == "goto" then
            write(indent(depth) .. ("-- GOTO %d (%s)"):format(node.target, node.info or "?"))
        elseif node.kind == "loop_cond" then
            local d = node.condRaw
            write(indent(depth) .. ("-- LOOP_COND (back to %d / %d) cond = %s"):format(
                node.trueTarget, node.falseTarget, condString(d)))
        end
    end
end

function M.report(structured, write)
    write = write or function(s) io.write(s); io.write("\n") end
    write(("Structured: %d function(s)"):format(#structured.fns))
    for _, f in ipairs(structured.fns) do
        write("")
        write(("function fn_%d:%s"):format(f.entryId, f.isMain and " (main)" or ""))
        printBody(f.body, 1, write)
        write("end")
    end
end

return M
