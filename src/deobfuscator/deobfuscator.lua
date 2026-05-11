-- prometheus-test-deobfuscator - pipeline entry point.
--
-- Loads source code with the (vendored) Prometheus parser, runs each reverse
-- pass in order, and produces cleaned source code via the Prometheus unparser.

local Parser = require("prometheus.parser")
local Unparser = require("prometheus.unparser")
local Enums = require("prometheus.enums")

local unwrap_function = require("deobfuscator.steps.unwrap_function")
local fold_numbers = require("deobfuscator.steps.fold_numbers")
local strip_anti_tamper = require("deobfuscator.steps.strip_anti_tamper")
local inline_constant_array = require("deobfuscator.steps.inline_constant_array")
local decrypt_strings = require("deobfuscator.steps.decrypt_strings")
local devirtualize = require("deobfuscator.steps.vmify.devirtualize")
local decrypt_vm_strings = require("deobfuscator.steps.vmify.decrypt_vm_strings")
local simplify_branches = require("deobfuscator.steps.vmify.simplify_branches")
local copy_prop_dce = require("deobfuscator.steps.vmify.copy_prop_dce")
local strip_vm_infra = require("deobfuscator.steps.vmify.strip_vm_infra")
local unwrap_pcall = require("deobfuscator.steps.vmify.unwrap_pcall")
local safe_loops = require("deobfuscator.steps.vmify.safe_loops")

local M = {}

local function log(msg)
    io.stderr:write("[deob] " .. msg .. "\n")
end

local PHASE1 = {
    { name = "unwrap_function",        fn = unwrap_function.apply        },
    { name = "fold_numbers",           fn = fold_numbers.apply           },
    { name = "inline_constant_array",  fn = inline_constant_array.apply  },
    { name = "strip_anti_tamper",      fn = strip_anti_tamper.apply      },
    { name = "decrypt_strings",        fn = decrypt_strings.apply        },
    -- Run a final fold pass to clean up anything we synthesized.
    { name = "fold_numbers",           fn = fold_numbers.apply           },
}

local PHASE2 = {
    { name = "devirtualize",           fn = devirtualize.apply           },
    { name = "decrypt_vm_strings",     fn = decrypt_vm_strings.apply     },
    { name = "simplify_branches",      fn = simplify_branches.apply      },
    { name = "copy_prop_dce",          fn = copy_prop_dce.apply          },
    { name = "strip_vm_infra",         fn = strip_vm_infra.apply         },
    -- One more DCE pass: stripping the infra removes the last readers of
    -- many scratch registers, which only now show up as dead.
    { name = "copy_prop_dce (post-strip)", fn = copy_prop_dce.apply      },
    -- Pass #4: unwrap `((unpack or table.unpack))({ X })` and the
    -- `(({ unpack({ X }) }))[N]` repack-and-index variant.
    { name = "unwrap_pcall",           fn = unwrap_pcall.apply           },
    -- The unwrap can expose new dead stores (e.g. when the only use of
    -- a temp was inside an unpack wrapper that's now a direct ref).
    { name = "copy_prop_dce (post-unwrap)", fn = copy_prop_dce.apply     },
    { name = "safe_loops",             fn = safe_loops.apply             },
}

function M.run(source, opts)
    opts = opts or {}
    local pretty = opts.pretty
    if pretty == nil then pretty = true end
    local skipPhase2 = opts.skipPhase2

    log("Parsing input ...")
    local parser = Parser:new({ LuaVersion = Enums.LuaVersion.Lua51 })
    local ast = parser:parse(source)
    log("Parsed.")

    for _, step in ipairs(PHASE1) do
        log("Running pass: " .. step.name)
        local ok, info = pcall(step.fn, ast)
        if not ok then
            log("Pass " .. step.name .. " failed: " .. tostring(info))
        elseif type(info) == "table" and info.note then
            log("  -> " .. info.note)
        end
    end

    if not skipPhase2 then
        for _, step in ipairs(PHASE2) do
            log("Running pass: " .. step.name)
            local ok, info = pcall(step.fn, ast)
            if not ok then
                log("Pass " .. step.name .. " failed: " .. tostring(info))
            elseif type(info) == "table" and info.note then
                log("  -> " .. info.note)
            end
        end
        -- Run fold_numbers once more to clean up any constants emitted by
        -- the devirtualizer (e.g. unfolded NumberExpression trees in the
        -- structured tree).
        log("Running pass: fold_numbers (final)")
        pcall(fold_numbers.apply, ast)
    end

    log("Generating output ...")
    local unparser = Unparser:new({
        LuaVersion = Enums.LuaVersion.Lua51,
        PrettyPrint = pretty,
        Highlight = false,
    })
    return unparser:unparse(ast)
end

return M
