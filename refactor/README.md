# The glv.rs refactor

The proofs of the ladder and the tables are about `Model.lean`, a hand-written model of the Rust,
because Charon and Aeneas at the versions pasta pins cannot translate that part of `src/glv.rs`.
It is written over the curve traits: Charon cannot resolve an associated type of
`group::CurveAffine` and leaves out every item bounded by `GlvParams`, and Aeneas rejects the
mutually recursive `CurveExt`, `CurveAffine` and `Coordinates`.

`glv-traits.diff` is a refactor of `src/glv.rs` at `e3c0f0246f` (+260/-66 lines) that gets
around this without changing what the code does:

- Two private traits, `LadderOps` (identity, doubling, mixed addition, affine negation) and
  `GlvOps` (the other curve operations the GLV path uses, and the decomposition), each with a
  blanket impl for every `GlvParams` curve.
- The bodies of `mul_glv`, `Table::new`, `Table::mul`, `mul_decomposed`, `add_digit`,
  `window_proj`, `from_window` and `Decomposed::new` move line for line into generic `_with`
  functions over those traits, which the methods call. pasta already uses this pattern for its
  inversion (`invert_with`). Two lines change inside a body: in `from_window`,
  `try_into().expect(...)` becomes `try_into().ok().unwrap()`. Aeneas' library handles `expect`'s
  message with `decide +native` and its `Debug` bound with an axiom, and either would bring in a
  non-standard axiom. Both forms panic on the same condition, which the slice lengths rule out.
- `Table::batch` keeps its own body, because Aeneas' library does not model `map` and `collect`.

The public API does not change. With the refactor, those eight functions translated in our trial
at pasta's pinned Charon and Aeneas, and the translation uses only the standard axioms. The
refactor is not part of the pull request to pasta_curves, and no proof here depends on it.

## How we checked that it changes nothing

Apply it with `patch src/glv.rs glv-traits.diff` in a checkout of pasta_curves at the pin.

Tests and lints: `cargo test --features glv`, `cargo test`, `cargo fmt --check`,
`cargo clippy --features glv --all-targets -- -D warnings`, and `cargo doc --no-deps --features glv`
with `RUSTDOCFLAGS="-D warnings"`, with and without `--document-private-items`.

Machine code, before and after, on aarch64 macOS with Rust 1.85.0:

1. A small probe crate depends on pasta_curves with the `glv` feature and exports one
   `#[no_mangle] #[inline(never)]` wrapper per public entry point (`mul_glv`, `Table::new`,
   `Table::batch`, `Table::mul`, `mul_decomposed`, `Decomposed::new`,
   `batch_mul_same_scalar_vartime`), for Pallas and for Vesta, so the compiler must keep all 14.
2. Release assembly of pasta's library and of the probe:
   `cargo rustc --release --features glv --lib -- --emit asm -C codegen-units=1`, and again
   with `codegen-units=16`.
3. The probe linked as a `cdylib` with cargo's default release profile, disassembled with
   `objdump -d --no-show-raw-insn`.
4. Each pair compared function by function, after dropping the legacy symbol hashes, mapping
   each moved function to its new `_with` name, and renumbering local labels in order of first
   use. In the disassembly, addresses become offsets within the function or symbol names.

## What we found

- All the tests pass: 136 and 1 doctest with `--features glv`, 105 and 1 without. fmt, clippy
  and rustdoc are clean.
- With `codegen-units=1`, every function is the same, instruction for instruction: 239 in
  pasta's library and 22 in the probe. The only data that changes is the panic-location
  records, because line numbers in `glv.rs` moved.
- With `codegen-units=16` (309 and 40 functions), no instruction changes; in a few functions
  the `.globl`, `.private_extern` and `.p2align` directives fall in different places.
- In the linked `cdylib`, 543 of 547 functions are identical. The other four, `mul_decomposed`
  and `Table::batch` for each curve, differ only in which panic-location record an instruction
  points at: one `add` immediate in `mul_decomposed`, three in `Table::batch`.
