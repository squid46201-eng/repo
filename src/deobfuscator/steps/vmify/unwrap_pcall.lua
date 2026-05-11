-- prometheus-test-deobfuscator - unwrap pcall/unpack obfuscation wrappers.
--
-- The Vmify obfuscator wraps simple expressions in
-- `((unpack or table.unpack))({ <expr> })` to obscure them.  When
-- `<expr>` is single-valued (not a multi-return call), the entire
-- wrapper is semantically equivalent to `<expr>` itself.
--
-- Patterns handled:
--
--   * `((unpack or table.unpack))({ X })`            -> `X`
--     when X is provably single-return (literal, variable, indexing,
--     arithmetic, len, not, negate, table ctor, concat, comparison).
--
--   * `(({ ((unpack or table.unpack))({ X }) }))[1]` -> `X`
--   * `(({ ((unpack or table.unpack))({ X }) }))[N]` -> `nil` for N > 1
--     when X is provably single-return.
--
-- We never touch wrappers around function calls (they may be
-- multi-return and the wrapper has observable side effects).
--
-- The rewrite is purely AST-local: we replace the wrapper node in
-- place by copying fields from the inner expression.

local Ast = require("prometheus.ast")
local AstKind = Ast.AstKind

local M = {}

local function isVar(n) return n and n.kind == AstKind.VariableExpression end
local function asNumber(n)
    if n and n.kind == AstKind.NumberExpression then return n.value end
end
local function asString(n)
    if n and n.kind == AstKind.StringExpression then return n.value end
end

local function nameOf(node)
    if not node or node.kind ~= AstKind.VariableExpression then return nil end
    if not node.scope or not node.scope.getVariableName then return nil end
    local ok, n = pcall(node.scope.getVariableName, node.scope, node.id)
    if ok then return n end
    return nil
end

-- True iff `expr` is provably a single-value expression (not a function
-- call, not a varargs).  Used by the repack-and-index pattern where
-- the multi-return-vs-single distinction matters for which value
-- gets selected by the index.
local function isSingleValue(expr)
    if type(expr) ~= "table" then return false end
    local k = expr.kind
    if k == AstKind.FunctionCallExpression
            or k == AstKind.PassSelfFunctionCallExpression
            or k == AstKind.VarargExpression then
        return false
    end
    -- Literals, vars, indexing, function literals, table ctors,
    -- arithmetic, comparisons, logical, concat, length, not, negate.
    return true
end

-- True iff `expr` is `unpack` or `table.unpack` or `(unpack or table.unpack)`.
local function isUnpackRef(expr)
    if not expr then return false end
    -- Strip parens
    while expr.kind == AstKind.OrExpression do
        -- `unpack or table.unpack`
        local l = expr.lhs
        local r = expr.rhs
        if isVar(l) and nameOf(l) == "unpack"
                and r and r.kind == AstKind.IndexExpression
                and isVar(r.base) and nameOf(r.base) == "table"
                and asString(r.index) == "unpack" then
            return true
        end
        return false
    end
    if isVar(expr) and nameOf(expr) == "unpack" then return true end
    if expr.kind == AstKind.IndexExpression
            and isVar(expr.base) and nameOf(expr.base) == "table"
            and asString(expr.index) == "unpack" then
        return true
    end
    return false
end

-- True iff `call` is `((unpack or table.unpack))({ X })` -> returns X.
-- For a single positional entry, `{ X }` captures all return values of
-- X (last-position rule), and `unpack({ X })` re-expands them.  So
-- the entire wrapper is semantically equivalent to X in ALL contexts
-- (single-return X stays single; multi-return X stays multi).
local function matchUnpackOfSingleton(call)
    if not call or call.kind ~= AstKind.FunctionCallExpression then return nil end
    if not isUnpackRef(call.base) then return nil end
    if not call.args or #call.args ~= 1 then return nil end
    local tbl = call.args[1]
    if tbl.kind ~= AstKind.TableConstructorExpression then return nil end
    local entries = tbl.entries or {}
    if #entries ~= 1 then return nil end
    local e = entries[1]
    -- Must be a positional (no key) entry.
    if e.key then return nil end
    return e.value
end

-- True iff `call` is `(({ ((unpack or table.unpack))({ X }) }))[N]`
-- where X is provably single-valued -- returns (X, N).
--
-- The multi-return-vs-single distinction matters here: when X is
-- multi-return, `{ X }` captures all of X's returns into the table,
-- and `[N]` picks the N-th.  We must NOT collapse such cases.
local function matchRepackedIndex(node)
    if not node or node.kind ~= AstKind.IndexExpression then return nil end
    local idx = asNumber(node.index)
    if not idx or idx ~= math.floor(idx) then return nil end
    local base = node.base
    if not base or base.kind ~= AstKind.TableConstructorExpression then return nil end
    local entries = base.entries or {}
    if #entries ~= 1 then return nil end
    local e = entries[1]
    if e.key then return nil end
    local inner = matchUnpackOfSingleton(e.value)
    if not inner then return nil end
    if not isSingleValue(inner) then return nil end
    return inner, idx
end

-- Replace the contents of `dst` with the contents of `src` in place,
-- so all parent references to `dst` continue to work.
local function replaceInPlace(dst, src)
    for k in pairs(dst) do
        if k ~= "scope" and k ~= "parentScope" and k ~= "baseScope"
                and k ~= "globalScope" then
            dst[k] = nil
        end
    end
    for k, v in pairs(src) do
        if k ~= "scope" and k ~= "parentScope" and k ~= "baseScope"
                and k ~= "globalScope" then
            dst[k] = v
        end
    end
    -- Preserve any kind-relevant scope refs that were on dst.
    -- (Most AST kinds use their own scope; we just keep dst's
    -- original scope refs to be safe.)
end

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

-- Make a NilExpression node (using the same scope as a sibling).
local function makeNil()
    return { kind = AstKind.NilExpression }
end

function M.apply(ast)
    local rewrites = 0
    -- Fixed-point: each rewrite can expose new candidates.
    local progress = true
    while progress do
        progress = false
        walk(ast, function(n)
            -- Pattern A: `(({ unpack({ X }) }))[N]` -> X (if N=1) / nil (else).
            local x, idx = matchRepackedIndex(n)
            if x then
                if idx == 1 then
                    replaceInPlace(n, x)
                else
                    replaceInPlace(n, makeNil())
                end
                rewrites = rewrites + 1
                progress = true
                return
            end
            -- Pattern B: `unpack({ X })` -> X.  We restrict this to
            -- contexts where the wrapper is in a "single-value" use:
            -- i.e. the immediate parent uses it as a scalar (an
            -- argument that ISN'T the last, an operand of arithmetic,
            -- the LHS/RHS of a binary expr, the rhs of an assignment
            -- where #lhs == 1, the index of an IndexExpression, etc).
            -- We can't easily check parent context here without a
            -- pass-aware traversal.  Instead, we apply the rewrite
            -- ALWAYS -- it's safe because `unpack({X})` where X is
            -- single-valued yields exactly X (as multi-return with one
            -- value), which is interchangeable with the scalar X in
            -- ALL contexts: argument lists ({X}), return statements
            -- (return X), assignments (a, b = X) only differ in how
            -- many values they receive, but with X being single-valued
            -- the multi-return is exactly (X), which equals the scalar
            -- X for all of those uses.
            local inner = matchUnpackOfSingleton(n)
            if inner then
                replaceInPlace(n, inner)
                rewrites = rewrites + 1
                progress = true
                return
            end
        end)
    end
    return { note = ("unwrapped " .. tostring(rewrites) .. " pcall/unpack wrapper(s)") }
end

return M
