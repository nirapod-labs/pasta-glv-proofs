# Differential test

Runs pasta_curves' real `wnaf_digits` and the Lean model on the same 75,223 magnitudes, each
with `negate` false and true, and checks that they agree exactly: the same digits and length, or
a panic in both. It does this once for each combination of debug assertions and overflow checks,
since those decide where the Rust panics and where it wraps silently.

- `src/main.rs` is the Rust driver. The function is copied verbatim from `src/glv.rs` (lines
  392-419 at `e3c0f0246f`) between `BEGIN VERBATIM` and `END VERBATIM`; CI checks that the copy
  matches the pinned file byte for byte.
- The four builds are Cargo's `dev` profile (both checks on, pasta's default; mode `debug`) and
  three profiles in `Cargo.toml`: `release` (both off), `release-ovf` (overflow checks only) and
  `debug-noovf` (debug assertions only).
- `Difftest.lean` is the Lean runner, `lake exe difftest MODE FILE`. It prints what the model
  says the build in MODE returns, in the driver's format.

The inputs are every magnitude below `2^16`; `2^k - 1`, `2^k` and `2^k + 1` for every `k`; every
repeated-nibble value; the neighbourhoods of `2^127`, of `0x88888888888888888888888888888889`
(the least magnitude that needs a 129th digit) and of `u128::MAX`; and 10,000 magnitudes of
random bit length from a fixed seed.

## Running it

After `lake exe cache get && lake build` at the repository root, from this folder (Cargo picks up
the 1.85.0 toolchain from `rust-toolchain.toml` here, the one pasta pins):

```bash
mkdir -p out
lake -d .. build difftest
cargo run -q -- inputs > out/inputs.txt
for profile in dev release release-ovf debug-noovf; do
  mode=${profile/dev/debug}
  cargo run -q --profile $profile -- run out/inputs.txt > out/rust-$mode.txt
  lake -d .. exe difftest $mode "$PWD/out/inputs.txt" > out/lean-$mode.txt
  cmp out/rust-$mode.txt out/lean-$mode.txt && echo "$mode: identical"
done
```

It passes if all four modes print `identical`. CI runs the same loop. In our runs, out of
150,446 lines (each magnitude once per sign), `debug` had 606 panicking lines, `release` 196,
`release-ovf` 204 and `debug-noovf` 606. `debug` and `debug-noovf` first panic at `2^127`, on
the assertion; `release` and `release-ovf` at `0x8888...89`, on the bounds check of the 129th
digit. The 8 extra lines of `release-ovf` are `2^128 - 7`, `-5`, `-3` and `-1`, each with both
signs. Without overflow checks the `u128` addition wraps there, and the function returns the
digits of `a - 2^128` instead of panicking.
