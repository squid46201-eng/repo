#!/usr/bin/env bash
# Regenerate fixtures using a local Prometheus checkout.
#
# Usage: PROMETHEUS_DIR=/path/to/Prometheus-master ./regenerate.sh
set -euo pipefail

cd "$(dirname "$0")"

: "${PROMETHEUS_DIR:?set PROMETHEUS_DIR to your Prometheus-master checkout}"
SRC="sample.lua"

# Weak preset: Vmify + ConstantArray + WrapInFunction.
( cd "$PROMETHEUS_DIR" && lua5.1 cli.lua --preset Weak --Lua51 \
    --out "$PWD/sample.weak.lua" "$PWD/$SRC" )

# Encrypt-only.
cat > /tmp/encstr_only.cfg <<'CFG'
return {
    LuaVersion = "Lua51", VarNamePrefix = "", NameGenerator = "MangledShuffled",
    PrettyPrint = false, Seed = 0,
    Steps = { { Name = "EncryptStrings", Settings = {} } },
}
CFG
( cd "$PROMETHEUS_DIR" && lua5.1 cli.lua --config /tmp/encstr_only.cfg --Lua51 \
    --out "$PWD/sample.enc.lua" "$PWD/$SRC" )

# EncryptStrings + ConstantArray + WrapInFunction (no Vmify).
cat > /tmp/enc_const.cfg <<'CFG'
return {
    LuaVersion = "Lua51", VarNamePrefix = "", NameGenerator = "MangledShuffled",
    PrettyPrint = false, Seed = 0,
    Steps = {
        { Name = "EncryptStrings", Settings = {} },
        { Name = "ConstantArray", Settings = { Threshold = 1, StringsOnly = true } },
        { Name = "WrapInFunction", Settings = {} },
    },
}
CFG
( cd "$PROMETHEUS_DIR" && lua5.1 cli.lua --config /tmp/enc_const.cfg --Lua51 \
    --out "$PWD/sample.ec.lua" "$PWD/$SRC" )

echo "fixtures regenerated."
