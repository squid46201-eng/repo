-- prometheus-test-deobfuscator - CLI entry point
--
-- Usage:
--   lua5.1 deobfuscate.lua --in input.lua [--out output.lua] [--no-pretty]
--   lua5.1 deobfuscate.lua --in input.lua --vm-report

local function script_path()
    local str = debug.getinfo(2, "S").source:sub(2)
    return str:match("(.*[/%\\])") or "./"
end

package.path = script_path() .. "src/?.lua;" .. package.path

local deobfuscator = require("deobfuscator.deobfuscator")

-- Argument parsing
local inFile, outFile
local pretty = true
local vmReport = false
local vmDecompile = false
local vmStructure = false
local i = 1
while i <= #arg do
    local a = arg[i]
    if a == "--in" or a == "-i" then
        i = i + 1
        inFile = arg[i]
    elseif a == "--out" or a == "-o" then
        i = i + 1
        outFile = arg[i]
    elseif a == "--no-pretty" then
        pretty = false
    elseif a == "--pretty" then
        pretty = true
    elseif a == "--vm-report" then
        vmReport = true
    elseif a == "--vm-decompile" then
        vmDecompile = true
    elseif a == "--vm-structure" then
        vmStructure = true
    elseif a == "--help" or a == "-h" then
        io.stderr:write([[Usage: lua5.1 deobfuscate.lua --in INPUT [--out OUTPUT] [options]

Options:
  --in, -i FILE       Input (obfuscated) Lua source.
  --out, -o FILE      Output path (defaults to stdout).
  --pretty            Pretty-print output (default).
  --no-pretty         Compact, single-line output.
  --vm-report         After phase-1 deobfuscation, print the recognized
                      Vmify VM structure and dispatcher block listing to
                      stderr. Doesn't write the output file.
  --vm-decompile      After --vm-report, additionally run the per-block
                      straight-line decompiler and print the resulting
                      IR to stderr.
  --vm-structure      After --vm-decompile, additionally build the
                      per-function CFG, recover dominators, and
                      reconstruct if/elseif/else structure. Loops are
                      flagged for the M4 pass.
  --help, -h          Show this help and exit.
]])
        os.exit(0)
    elseif not inFile then
        inFile = a
    elseif not outFile then
        outFile = a
    else
        io.stderr:write("Unknown argument: " .. tostring(a) .. "\n")
        os.exit(2)
    end
    i = i + 1
end

if not inFile then
    io.stderr:write("Missing --in argument\n")
    os.exit(2)
end

local f = io.open(inFile, "rb")
if not f then
    io.stderr:write("Cannot open input file: " .. inFile .. "\n")
    os.exit(2)
end
local source = f:read("*all")
f:close()

if vmStructure then vmDecompile = true end
if vmDecompile then vmReport = true end
if vmReport then
    -- Phase-1 deobfuscation in-memory, then run the recognizer/extractor on the AST.
    local Parser    = require("prometheus.parser")
    local recognize = require("deobfuscator.steps.vmify.recognize")
    local extract   = require("deobfuscator.steps.vmify.extract")

    local cleaned = deobfuscator.run(source, { pretty = false, log = true, skipPhase2 = true })
    local ast = Parser:new({ LuaVersion = "Lua51" }):parse(cleaned)

    local function out(s) io.stderr:write(s); io.stderr:write("\n") end

    local vm, errVm = recognize.recognize(ast)
    if not vm then
        out("[vm-report] No Vmify VM detected: " .. tostring(errVm))
        os.exit(0)
    end
    recognize.report(vm, out)

    out("")
    local extracted, errEx = extract.extract(vm)
    if not extracted then
        out("[vm-report] Block extraction failed: " .. tostring(errEx))
        os.exit(1)
    end
    extract.report(extracted, out)

    if vmDecompile then
        local decompile = require("deobfuscator.steps.vmify.decompile_block")
        out("")
        out("==== Block IR ====")
        local decomps = decompile.decompileAll(extracted, vm)
        decompile.reportAll(decomps, out)

        if vmStructure then
            local cfg       = require("deobfuscator.steps.vmify.cfg")
            local closures  = require("deobfuscator.steps.vmify.closures")
            local structure = require("deobfuscator.steps.vmify.structure")
            out("")
            out("==== CFG ====")
            local graph = cfg.build(decomps, extracted, vm)
            cfg.report(graph, out)
            closures.analyze(graph)
            out("")
            out("==== Structured ====")
            local structured = structure.structure(graph)
            structure.report(structured, out)
        end
    end
    os.exit(0)
end

local cleaned = deobfuscator.run(source, { pretty = pretty })

if outFile then
    local out = io.open(outFile, "wb")
    if not out then
        io.stderr:write("Cannot open output file for writing: " .. outFile .. "\n")
        os.exit(2)
    end
    out:write(cleaned)
    out:close()
    io.stderr:write("[deob] Wrote " .. outFile .. " (" .. #cleaned .. " bytes)\n")
else
    io.write(cleaned)
end
