# pasta-glv-proofs

A machine-checked Lean 4 proof of the wNAF recoding and the Straus ladder in the GLV scalar
multiplication of [zcash/pasta_curves](https://github.com/zcash/pasta_curves). It covers part 3 of
[pasta_curves#174](https://github.com/zcash/pasta_curves/issues/174): `wnaf_digits` and the ladder
over the two tables, in `src/glv.rs` at commit `e3c0f0246f`.

Maintained by Athex and Rifat Ahmed at [Nirapod](https://github.com/nirapod-labs).

## Results

Below `2^127`, `wnaf_digits` never panics and writes at most 128 digits, each zero or odd with
absolute value at most 7, that encode the signed input (`Σ dᵢ2ⁱ = ±a`). This holds of a Lean
model of the function and of Aeneas' translation of the Rust. The rest of the path is proved
about the model only: there, the ladder and the four entry points turn those digits into `[k]P`,
provided the group order, the curve primitives, the endomorphism and the scalar decomposition
meet their specifications (H0 to H3 below).

The statements are in `PastaCurves/Glv/Spec.lean`, about the model, and
`PastaCurves/Glv/SpecA.lean`, about Aeneas' translation of `wnaf_digits`:

| Statement | Content |
|---|---|
| W1 | Below `2^127`, `wnaf_digits` does not panic and no checked operation fails. |
| W2 | A `u128` magnitude `a` gets at most `⌊log₂ a⌋ + 2` digits, so at most 128 below `2^127`. |
| W3 | Every digit is zero or odd, with absolute value at most 7. |
| W4 | Below `2^127`, the digits encode the signed magnitude and are zero past the returned length. |
| W5 | `0x88888888888888888888888888888889` is the least magnitude that needs a 129th digit. The length is not monotone: the next magnitude needs only 128 (`Tests/Kernel.lean`). |
| W6 | Over all of `u128`, the assertion fails exactly from `2^127` on, and the `u128` addition overflows exactly at `2^128 − 7`, `−5`, `−3` and `−1`. |
| D | On two halves below `2^127`, `Decomposed::new` does not panic, its arrays are the halves' digits, `len = max(len1, len2) ≤ 128`, and both arrays are zero from `len` on. |
| L1 | In any abelian group, the ladder computes `(Σ d1ᵢ2ⁱ)·P + (Σ d2ᵢ2ⁱ)·Q` for digits of wNAF shape. |
| L2 | `Table::new` and `Table::batch` build the odd multiples `(2j+1)·P` and their images under the endomorphism. |
| C, C-batch | `mul_glv`, `Table::mul`, `mul_decomposed` on `Decomposed::new(k)`, and `batch_mul_same_scalar_vartime` return valid points that represent `[k]P`, under the hypotheses H0 to H3 below. |
| WAx, WA, WAok | Aeneas' translation of `wnaf_digits` fails exactly where the model says a debug build panics, at the assertion, and otherwise returns the model's digits. |

Every statement is proved. `#print axioms` on the two conjunctions, `PastaCurves.Glv.Final.all`
and `PastaCurves.Glv.FinalA.all`, lists only `propext`, `Classical.choice` and `Quot.sound`.
There is no `sorry`, no `native_decide` and no new axiom.

W5 and W6 are about magnitudes from `2^127` up, outside `decompose`'s contract, so a correct
caller never passes one. The four magnitudes of W6 are still worth a note: a build with neither
debug assertions nor overflow checks wraps silently there and returns the digits of `a − 2^128`
instead of panicking (`Tests/Kernel.lean` for the model; the differential test shows the Rust
does the same). We think this deserves a one-line comment in the Rust.

## Scope and assumptions

pasta_curves#174 asks for a proof of whichever recoding the crate settles on.
[pasta_curves#125](https://github.com/zcash/pasta_curves/pull/125) proposes a different one, based
on Eisenstein integers, with its own ladder. If it replaces the current code, the recoding and
ladder proofs would have to be redone.

The ladder, the tables and the four entry points are proved about `Model.lean`, a hand-written
model that follows the Rust line by line and was checked against it by reading. Only
`wnaf_digits` is also proved against Aeneas' translation of the real code. The rest of the path is
generic over the curve traits, which the Charon and Aeneas versions pasta pins cannot translate as
written; `refactor/` shows a change to `src/glv.rs` that would make most of it translatable. The
model of `wnaf_digits` was also tested against the Rust function itself (`difftest/`).

C and C-batch take four hypotheses, never axioms:

- H0 `OrderSpec`: the group order annihilates valid points.
- H1 `EndoSpec`: the endomorphism is multiplication by `λ` (part 1 of pasta_curves#174).
- H2 `DecomposeSpec`: `decompose` returns halves below `2^127` that recombine to the scalar
  (part 2 of pasta_curves#174).
- H3 `CurveOps.Spec`: the curve primitives implement the group operations. This one is trusted.

The proof also assumes that allocation succeeds. It concerns variable-time code only and makes no
claim about constant-time behaviour.

## Building

You need [elan](https://github.com/leanprover/elan). The Lean toolchain, Mathlib and Aeneas are the
versions pasta_curves pins at `e3c0f0246f`.

```bash
git clone https://github.com/nirapod-labs/pasta-glv-proofs
cd pasta-glv-proofs
lake exe cache get
lake build
lake env lean Tests/Axioms.lean
```

`lake build` builds the proofs and the tests; the last command prints the axioms of `Final.all`
and `FinalA.all`. `sha256sum -c FROZEN.sha256` checks that the model, the statements, the lemma
statements and the translation are the published versions. `difftest/README.md` explains how to run
the differential test, and `refactor/README.md` how the refactor was checked. CI runs the hash
check, the build, the axiom check, the edge cases and the differential test on every push to `main`
and every pull request.

The package requires Mathlib and Aeneas directly rather than pasta_curves itself: its modules live
under `PastaCurves.Glv`, the prefix the pull request uses, and with pasta_curves as a dependency
Lake would look for them inside pasta's package. They import nothing from pasta_curves.

`Types.lean` and `Funs.lean` are the output of pasta's `lean/scripts/gen_aeneas.sh` with one added
line, `translate Glv "" glv crate::glv::wnaf_digits`.

## Layout

In the Lean files, "Level M" marks a result about the model and "Level A" one about Aeneas'
translation.

```
PastaCurves/Glv/
  Model.lean       the Lean model of the GLV path in src/glv.rs
  Spec.lean        the statements about the model
  SpecA.lean       the statements about the translation of wnaf_digits
  Blueprint.lean   the lemmas the proof of Spec.lean is split into, and how they imply it
  BlueprintA.lean  the same for SpecA.lean
  Types.lean       Aeneas' translation of wnaf_digits (generated)
  Funs.lean
  Proofs/          one file per lemma, 41 in all
  Final.lean       Spec.lean, assembled from the lemmas
  FinalA.lean      SpecA.lean, assembled from the lemmas
Tests/
  Mutants.lean     10 broken variants of the model, refuted by the statements they break
  EdgeCases.lean   the model on the boundary inputs (lake exe edgecases)
  Kernel.lean      evaluation of the model by the kernel (decide +kernel)
  NonVacuity.lean  one instance that satisfies H0 to H3 at once
  Axioms.lean      the axiom check
difftest/          the model of wnaf_digits against the real function, in four build profiles
refactor/          a change to src/glv.rs that lets Charon and Aeneas translate the ladder
FROZEN.sha256      hashes of the model, the statements, the lemma statements and the translation
```

The same proofs, arranged in pasta_curves' own layout, are proposed as a pull request to
pasta_curves.

## License

Licensed under either of the Apache License, Version 2.0 (`LICENSE-APACHE`) or the MIT license
(`LICENSE-MIT`), at your option, as pasta_curves is. Copyright the authors listed in `AUTHORS`,
except for the code taken from pasta_curves (the copy of `wnaf_digits` in `difftest/src/main.rs`,
the code in `refactor/glv-traits.diff`, and the generated `Types.lean` and `Funs.lean`), which is
Copyright (c) 2020-2025 The Electric Coin Company and Copyright (c) 2020-2026 The pasta_curves
contributors, under the same licenses.
