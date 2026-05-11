# prometheus-test-deobfuscator

Educational / research deobfuscator for Lua 5.1 code obfuscated with
[Prometheus](https://github.com/prometheus-lua/Prometheus) (Levno_710).

The goal is to reverse the AST-level transformations Prometheus applies and
recover something close to the original source.

## Status — work in progress

Phase 1 (simple transformations) is the current focus:

| Step in obfuscator           | Reverse pass                       | Status        |
|------------------------------|------------------------------------|---------------|
| `WrapInFunction`             | `unwrap_function`                  | implemented   |
| `NumbersToExpressions`       | `fold_numbers`                     | implemented   |
| `ConstantArray`              | `inline_constant_array`            | implemented   |
| `AntiTamper`                 | `strip_anti_tamper`                | implemented   |
| `EncryptStrings`             | `decrypt_strings`                  | implemented   |
| `Vmify`                      | `devirtualize_vmify` (phase 2)     | not started   |

Phase 1 reduces an obfuscated script to "just the Vmify VM" (the bytecode
dispatcher). Phase 2 then needs to decompile that VM back into the original
AST, which is significantly more involved and tracked separately.

## Layout

```
src/
  prometheus/         # vendored Prometheus parser/unparser/ast/visitast/scope
  logger.lua          # vendored Prometheus logger
  colors.lua          # vendored Prometheus color helper
  deobfuscator/
    deobfuscator.lua  # pipeline entry point
    ast_utils.lua     # AST pattern-matching helpers
    steps/
      unwrap_function.lua
      fold_numbers.lua
      inline_constant_array.lua
      strip_anti_tamper.lua
      decrypt_strings.lua
deobfuscate.lua       # CLI: lua5.1 deobfuscate.lua --in input.lua --out clean.lua
tests/
  test.lua            # the original obfuscated sample
  fixtures/           # smaller fixtures + regenerate.sh
  run_tests.lua       # end-to-end test harness
```

## Usage

Requires `lua5.1` (or LuaJIT).

```sh
lua5.1 deobfuscate.lua --in tests/test.lua --out tests/test.deob.lua
```

Optional flags:

* `--no-pretty` — compact output (default is pretty-printed).

## Tests

```sh
lua5.1 tests/run_tests.lua
```

Each fixture is a small program obfuscated with a different combination of
Prometheus steps:

| Fixture                 | Steps applied                                           | Runtime check |
|-------------------------|---------------------------------------------------------|---------------|
| `sample.weak.lua`       | Vmify + ConstantArray + WrapInFunction (Weak preset)    | yes           |
| `sample.enc.lua`        | EncryptStrings only                                     | yes           |
| `sample.ec.lua`         | EncryptStrings + ConstantArray + WrapInFunction         | yes           |
| `test.lua`              | Medium preset (incl. Vmify + AntiTamper inside the VM)  | parse-only    |

Runtime check = the deobfuscated output is executed and its stdout compared
to the obfuscated input's stdout.  test.lua and similar Medium/Strong-preset
inputs are parse-only because Vmify is still embedded after phase 1 and the
VM contains AntiTamper sanity checks that detect any structural change to
the surrounding source.

## License

MIT. See `LICENSE`.

The vendored `src/prometheus/`, `src/logger.lua` and `src/colors.lua` are taken
from upstream Prometheus (Prometheus License — credit to Elias Oelschner /
Levno_710, https://github.com/prometheus-lua/Prometheus).
