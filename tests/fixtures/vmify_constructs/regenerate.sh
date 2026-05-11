#!/usr/bin/env bash
# Regenerate the per-construct Vmify-only fixtures using a local Prometheus checkout.
#
# Usage: PROMETHEUS_DIR=/path/to/Prometheus-master ./regenerate.sh
set -euo pipefail

cd "$(dirname "$0")"

: "${PROMETHEUS_DIR:?set PROMETHEUS_DIR to your Prometheus-master checkout}"

# Vmify-only config: gives us a clean VM body with no other layers wrapped
# around it. We deliberately skip ConstantArray / EncryptStrings so that the
# recognizer test suite is decoupled from phase-1 reverse passes.
cat > /tmp/vmify_only.cfg <<'CFG'
return {
    LuaVersion = "Lua51", VarNamePrefix = "", NameGenerator = "MangledShuffled",
    PrettyPrint = false, Seed = 0,
    Steps = { { Name = "Vmify", Settings = {} } },
}
CFG

FIX_DIR="$PWD"
for src in sample.if.lua sample.while.lua sample.for_num.lua \
           sample.for_in.lua sample.closures.lua sample.vararg.lua; do
    out="${src%.lua}.vmify.lua"
    echo "$src -> $out"
    ( cd "$PROMETHEUS_DIR" && lua5.1 cli.lua --config /tmp/vmify_only.cfg --Lua51 \
        --out "$FIX_DIR/$out" "$FIX_DIR/$src" )
done

echo "vmify construct fixtures regenerated."
