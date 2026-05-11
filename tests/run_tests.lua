-- prometheus-test-deobfuscator - end-to-end tests.
--
-- For each fixture in tests/fixtures/, this script:
--   1. Runs the deobfuscator on the obfuscated input.
--   2. Verifies the output parses as valid Lua.
--   3. (Optionally) executes both the original obfuscated file and the
--      deobfuscated output and checks their stdout matches.
--
-- The fixtures are pre-generated; see tests/fixtures/regenerate.sh for how to
-- regenerate them with a particular Prometheus checkout.

local function script_path()
    local str = debug.getinfo(2, "S").source:sub(2)
    return str:match("(.*[/%\\])") or "./"
end

package.path = script_path() .. "../src/?.lua;" .. package.path

local deobfuscator = require("deobfuscator.deobfuscator")
local Parser       = require("prometheus.parser")
local recognize    = require("deobfuscator.steps.vmify.recognize")
local extract      = require("deobfuscator.steps.vmify.extract")

local TESTS = {
    -- Each entry:
    --   name           - human-readable label
    --   path           - relative to tests/
    --   runtime_check  - run obf and deob, compare stdout
    --   vm_check       - run phase-2 recognize+extract on the deob output
    --
    -- runtime_check = false for cases that include Vmify or AntiTamper,
    -- because phase 1 of the deobfuscator can't yet make those equivalent
    -- (Vmify is a stage-2 problem, and AntiTamper inside a Vmify VM detects
    -- structural changes).
    { name = "weak_hello",      path = "fixtures/sample.weak.lua",   runtime_check = true,  vm_check = false },
    { name = "encrypt_only",    path = "fixtures/sample.enc.lua",    runtime_check = true,  vm_check = false },
    { name = "encrypt_const",   path = "fixtures/sample.ec.lua",     runtime_check = true,  vm_check = false },
    -- test.lua includes AntiTamper which throws "Tamper Detected!" when run.
    -- Devirtualization preserves the AntiTamper logic, so the deob also
    -- raises the same error -- check via runtime_check (stdout equality).
    { name = "test_lua",        path = "test.lua",                   runtime_check = true,  vm_check = false },
    -- Per-construct Vmify fixtures (M6 end-to-end devirtualization).
    { name = "vmify_if",        path = "fixtures/vmify_constructs/sample.if.vmify.lua",       runtime_check = true,  vm_check = false },
    { name = "vmify_while",     path = "fixtures/vmify_constructs/sample.while.vmify.lua",    runtime_check = true,  vm_check = false },
    { name = "vmify_for_num",   path = "fixtures/vmify_constructs/sample.for_num.vmify.lua",  runtime_check = true,  vm_check = false },
    { name = "vmify_for_in",    path = "fixtures/vmify_constructs/sample.for_in.vmify.lua",   runtime_check = true,  vm_check = false },
    { name = "vmify_closures",  path = "fixtures/vmify_constructs/sample.closures.vmify.lua", runtime_check = true,  vm_check = false },
    { name = "vmify_vararg",    path = "fixtures/vmify_constructs/sample.vararg.vmify.lua",   runtime_check = true,  vm_check = false },
}

local function readFile(path)
    local f = io.open(path, "rb")
    if not f then return nil, "cannot open: " .. path end
    local s = f:read("*all")
    f:close()
    return s
end

local function tmpFile(suffix)
    return os.tmpname() .. suffix
end

local function run(cmd)
    local p = io.popen(cmd .. " 2>&1")
    local out = p:read("*all")
    -- pclose returns the exit status as second/third return.
    local _, _, code = p:close()
    return out, code
end

local failed = 0
local passed = 0
local skipped = 0

local base = script_path()

for _, t in ipairs(TESTS) do
    local fullPath = base .. t.path
    local src, err = readFile(fullPath)
    if not src then
        io.stderr:write("SKIP " .. t.name .. ": " .. err .. "\n")
        skipped = skipped + 1
    else
        io.write(string.format("[ %s ] running ... ", t.name))
        io.flush()

        local ok, cleaned = pcall(deobfuscator.run, src, { pretty = false })
        if not ok then
            io.write("DEOB FAIL: " .. tostring(cleaned) .. "\n")
            failed = failed + 1
        else
            -- Parse-check the output.
            local f = loadstring or load
            local chunk, perr = f(cleaned, "@" .. t.name)
            if not chunk then
                io.write("PARSE FAIL: " .. tostring(perr) .. "\n")
                failed = failed + 1
            else
                local stages = {}
                local stageFail = nil

                if t.runtime_check then
                    local tmp = tmpFile(".lua")
                    local fh = io.open(tmp, "w")
                    fh:write(cleaned); fh:close()
                    local origOut = run("lua5.1 " .. fullPath)
                    local deobOut = run("lua5.1 " .. tmp)
                    os.remove(tmp)
                    if origOut == deobOut then
                        table.insert(stages, "runtime_eq")
                    else
                        stageFail = "runtime DIFF\n  orig: " .. tostring(origOut) .. "\n  deob: " .. tostring(deobOut)
                    end
                end

                if not stageFail and t.vm_check then
                    local pok, ast = pcall(function()
                        return Parser:new({ LuaVersion = "Lua51" }):parse(cleaned)
                    end)
                    if not pok then
                        stageFail = "vm parse FAIL: " .. tostring(ast)
                    else
                        local vm, vmErr = recognize.recognize(ast)
                        if not vm then
                            stageFail = "vm recognize FAIL: " .. tostring(vmErr)
                        else
                            local ext, exErr = extract.extract(vm)
                            if not ext then
                                stageFail = "vm extract FAIL: " .. tostring(exErr)
                            else
                                table.insert(stages, ("vm_extract(%d blocks)"):format(#ext.blocksOrdered))
                            end
                        end
                    end
                end

                if stageFail then
                    io.write(stageFail .. "\n")
                    failed = failed + 1
                else
                    if #stages == 0 then
                        io.write("OK (parse-only)\n")
                    else
                        io.write("OK [" .. table.concat(stages, ", ") .. "]\n")
                    end
                    passed = passed + 1
                end
            end
        end
    end
end

io.write(string.format("\n%d passed, %d failed, %d skipped\n", passed, failed, skipped))
os.exit(failed > 0 and 1 or 0)
