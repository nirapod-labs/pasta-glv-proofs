import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.Forall2
import PastaCurves.Glv.Model

/-!
# The statements about the GLV path's wNAF recoding and ladder

The theorems to prove about the model of `Model.lean`, each as the definition of a proposition:
W1–W6 about `wnaf_digits`, D about `Decomposed::new`, L1 about the ladder, L2 about the tables,
and C and C-batch end to end. W1–W6, D, L1 and L2 are stated for any model of the functions they
are about (`W1Of exec`, …), so that a deliberately broken model can be checked against the very
same statement; the Spec applies them to the model (`W1_stmt := W1Of Wnaf.exec`).

The curve's points stand for elements of a group `G` through an abstraction `CurveAbs`, and its
scalars stand for natural numbers through an abstraction `ScalarAbs`. C and C-batch take both as
arguments, with four hypotheses about them (arguments too, never axioms):

- H0: `n` kills every valid point (`OrderSpec`);
- H1: `endo` keeps points valid and acts as multiplication by `λ` (`EndoSpec`), assumed here,
  for a formalization of the endomorphism to discharge;
- H2: `decompose` meets `DecomposeSpec`, assumed here, for a formalization of the decomposition
  to discharge;
- H3: the curve primitives meet `CurveOps.Spec`. H3 is trusted, and stays so.

The model leaves allocation out and so assumes it succeeds (`Table.batch`).
-/

namespace PastaCurves.Glv

open Aeneas Aeneas.Std

/-- A width-4 wNAF digit: zero, or odd and between `-7` and `7`. -/
def IsWnafDigit (d : ℤ) : Prop := d = 0 ∨ (Odd d ∧ -7 ≤ d ∧ d ≤ 7)

/-! ## `wnaf_digits` -/

/-- **W1** (no panic, no overflow), for a model `exec` of `wnaf_digits`: below `2^127` the
assertion holds, no write is out of bounds, and no `u128` or `i8` operation overflows. -/
def W1Of (exec : ℕ → Bool → Wnaf.State) : Prop :=
  ∀ (a : ℕ) (neg : Bool), a < 2 ^ 127 →
    (exec a neg).assertFailed = false ∧ (exec a neg).outOfBounds = false ∧
    (exec a neg).u128Overflow = false ∧ (exec a neg).i8Overflow = false

/-- **W2** (length): on a `u128` magnitude `a` the loop makes at most `⌊log₂ a⌋ + 2` passes, the
count it returns as `n`, so at most 128 below `2^127`. The bound is on the passes themselves, so
it also holds where a build panics: a debug build from `2^127` on, at its assertion, and every
build at `leastFailing` (W5) and at some magnitudes above it, at a write past the array. -/
def W2Of (exec : ℕ → Bool → Wnaf.State) : Prop :=
  (∀ (a : ℕ) (neg : Bool), a < 2 ^ 128 → (exec a neg).n ≤ Nat.log2 a + 2) ∧
  ∀ (a : ℕ) (neg : Bool), a < 2 ^ 127 → (exec a neg).n ≤ 128

/-- **W3** (digit shape): every digit of a `u128` magnitude is a width-4 wNAF digit, so
`|d| / 2` indexes a table of four entries. -/
def W3Of (exec : ℕ → Bool → Wnaf.State) : Prop :=
  ∀ (a : ℕ) (neg : Bool), a < 2 ^ 128 → ∀ i : Fin 128,
    IsWnafDigit ((exec a neg).digits i) ∧ ((exec a neg).digits i).natAbs / 2 < 4

/-- **W4** (value): below `2^127` the digits encode `a`, or `-a` when `neg`, and they are zero
from position `n` on. -/
def W4Of (exec : ℕ → Bool → Wnaf.State) : Prop :=
  ∀ (a : ℕ) (neg : Bool), a < 2 ^ 127 →
    ∑ i : Fin 128, (exec a neg).digits i * 2 ^ (i : ℕ) = (if neg then -(a : ℤ) else a) ∧
    ∀ i : Fin 128, (exec a neg).n ≤ i → (exec a neg).digits i = 0

/-- `0x8888…8889` (32 hex digits), the least magnitude whose wNAF needs a 129th digit. -/
def leastFailing : ℕ := 0x88888888888888888888888888888889

/-- **W5** (least failing magnitude): below `leastFailing` there are at most 128 digits, no write
out of bounds and no overflow, so a build without debug assertions returns, with or without
overflow checks; `leastFailing` gets 129 digits, the last written to `digits[128]`, which panics
in every build. Below `2^127` a debug build returns as well (W1). The length is not monotone in
the magnitude (`leastFailing + 1` gets 128 digits), so this is no "iff". -/
def W5Of (exec : ℕ → Bool → Wnaf.State) : Prop :=
  (∀ (a : ℕ) (neg : Bool), a < leastFailing →
    (exec a neg).n ≤ 128 ∧ (exec a neg).outOfBounds = false ∧
    (exec a neg).u128Overflow = false ∧ (exec a neg).i8Overflow = false) ∧
  ∀ neg : Bool, (exec leastFailing neg).n = 129 ∧ (exec leastFailing neg).outOfBounds = true

/-- **W6** (where each check fires): on every `u128` magnitude, the assertion fails exactly from
`2^127` on, no `i8` operation overflows, and a `u128` operation overflows exactly on
`2^128 - 7`, `2^128 - 5`, `2^128 - 3` and `2^128 - 1`, in the first pass's `k += (-d) as u128`,
which a release build wraps without a panic. -/
def W6Of (exec : ℕ → Bool → Wnaf.State) : Prop :=
  ∀ (a : ℕ) (neg : Bool), a < 2 ^ 128 →
    ((exec a neg).assertFailed = true ↔ 2 ^ 127 ≤ a) ∧ (exec a neg).i8Overflow = false ∧
    ((exec a neg).u128Overflow = true ↔
      a = 2 ^ 128 - 7 ∨ a = 2 ^ 128 - 5 ∨ a = 2 ^ 128 - 3 ∨ a = 2 ^ 128 - 1)

/-- W1 for the model. -/
def W1_stmt : Prop := W1Of Wnaf.exec

/-- W2 for the model. -/
def W2_stmt : Prop := W2Of Wnaf.exec

/-- W3 for the model. -/
def W3_stmt : Prop := W3Of Wnaf.exec

/-- W4 for the model. -/
def W4_stmt : Prop := W4Of Wnaf.exec

/-- W5 for the model. -/
def W5_stmt : Prop := W5Of Wnaf.exec

/-- W6 for the model. -/
def W6_stmt : Prop := W6Of Wnaf.exec

/-! ## `Decomposed::new` -/

/-- **D** (`Decomposed::new` on two halves below `2^127`), for a model `ofHalves` of its lines after
the call to `decompose`: no panic; the digit arrays are the halves' wNAF digits, `len` is the
larger of their lengths and at most 128, and both arrays are zero from `len` on. -/
def DOf (ofHalves : Bool × ℕ → Bool × ℕ → Option Decomposed) : Prop :=
  ∀ (neg1 neg2 : Bool) (a1 a2 : ℕ), a1 < 2 ^ 127 → a2 < 2 ^ 127 →
    ∃ D, ofHalves (neg1, a1) (neg2, a2) = some D ∧
      D.digits1 = (Wnaf.run a1 neg1).1 ∧ D.digits2 = (Wnaf.run a2 neg2).1 ∧
      D.len = max (Wnaf.run a1 neg1).2 (Wnaf.run a2 neg2).2 ∧ D.len ≤ 128 ∧
      ∀ i : Fin 128, D.len ≤ i → D.digits1 i = 0 ∧ D.digits2 i = 0

/-- D for the model. -/
def D_stmt : Prop := DOf Decomposed.ofHalves

/-! ## The ladder -/

/-- The odd multiples `{1, 3, 5, 7}·p` of a group element. -/
def oddMultiples {G : Type} [AddCommGroup G] (p : G) : Fin 4 → G :=
  fun j => (2 * (j : ℕ) + 1) • p

/-- **L1** (the ladder), for a model `mulDec` of `mul_decomposed`: in any additive group, over the
tables of `p` and `q`, digits of wNAF shape that are zero from `len ≤ 128` on give
`(Σ d1ᵢ 2ⁱ)·p + (Σ d2ᵢ 2ⁱ)·q`, without a panic. With `len = 0` that is the identity. -/
def L1Of (mulDec : ∀ {P A : Type}, LadderOps P A → Table A → Decomposed → Option P) : Prop :=
  ∀ {G : Type} [AddCommGroup G] (p q : G) (D : Decomposed),
    (∀ i, IsWnafDigit (D.digits1 i)) → (∀ i, IsWnafDigit (D.digits2 i)) → D.len ≤ 128 →
    (∀ i : Fin 128, D.len ≤ i → D.digits1 i = 0 ∧ D.digits2 i = 0) →
    mulDec (groupOps G) ⟨oddMultiples p, oddMultiples q⟩ D =
      some ((∑ i : Fin 128, D.digits1 i * 2 ^ (i : ℕ)) • p +
        (∑ i : Fin 128, D.digits2 i * 2 ^ (i : ℕ)) • q)

/-- L1 for the model. -/
def L1_stmt : Prop := L1Of fun O t D => Table.mulDecomposed O t D

/-! ## The abstraction and the hypotheses -/

/-- What the curve's points stand for: validity predicates on projective and affine points, and
maps `α`, `αA` into a group `G`. This is data, not an assumption: the hypotheses are stated
against it, and a use of C names it. For Pasta, valid means on the curve, and `α` takes the
Jacobian `(X : Y : Z)` to the affine point `(X/Z², Y/Z³)`, and `Z = 0` to the identity. -/
structure CurveAbs (P A G : Type) where
  /-- A projective point that the arithmetic accepts (on the curve, Rust's `C`). -/
  valid : P → Prop
  /-- An affine point that the arithmetic accepts (`C::AffineExt`). -/
  validA : A → Prop
  /-- The group element a projective point stands for; Rust's `==` is equality under `α`. -/
  α : P → G
  /-- The group element an affine point stands for. -/
  αA : A → G

/-- **H0**: `n` kills every valid point, as the order of a group of order `n` does. Primality is
not needed. -/
def OrderSpec {P A G : Type} [AddCommGroup G] (V : CurveAbs P A G) (n : ℕ) : Prop :=
  ∀ p, V.valid p → n • V.α p = 0

/-- **H1**, about Rust's `endo` itself (`(ζX, Y, Z)` with `ζ = Base::ZETA`): it keeps points
valid and acts as multiplication by `lam`. -/
def EndoSpec {P A G : Type} [AddCommGroup G] (O : CurveOps P A) (V : CurveAbs P A G)
    (lam : ℕ) : Prop :=
  ∀ p, V.valid p → V.valid (O.endo p) ∧ V.α (O.endo p) = lam • V.α p

/-- What the scalars stand for: which values of the scalar type are scalars the crate can hold, and
the number each stands for. Data, like `CurveAbs`. For Pasta, valid means canonical Montgomery
limbs, as in every scalar the crate builds, and `val` is the canonical value in `[0, n)`. -/
structure ScalarAbs (Sc : Type) where
  /-- A value of the scalar type that the crate can hold. -/
  valid : Sc → Prop
  /-- The number a scalar stands for. -/
  val : Sc → ℕ

/-- A half `(negative, magnitude)` as an integer. -/
def decode (h : Bool × Std.U128) : ℤ := if h.1 then -(h.2.val : ℤ) else h.2.val

/-- **H2**, per curve: on a valid scalar `k`, `decompose(k)` succeeds, with both magnitudes below
`2^127` and `k1 + k2·λ ≡ k (mod n)`. -/
def DecomposeSpec {Sc : Type} (n lam : ℕ) (S : ScalarAbs Sc) (f : DecomposeFn Sc) : Prop :=
  ∀ k, S.valid k → ∃ r, f k = .ok r ∧ r.1.2.val < 2 ^ 127 ∧ r.2.2.val < 2 ^ 127 ∧
    decode r.1 + decode r.2 * lam ≡ S.val k [ZMOD n]

/-- **H3**, the trusted curve primitives. The model takes them as total functions (`CurveOps`), so
that each returns rather than panics is assumed there; H3 adds that, under the abstraction `V`,
each keeps validity and is the group operation. It is stated for all valid operands, so it covers
each case the path produces: identity operands, equal operands (`acc += a` where `acc` and `a`
stand for the same point), negated operands, and `batch_normalize` on points with `Z = 0`.
`batch_normalize`'s `assert_eq!` on its two lengths is not modelled: both callers pass equal
lengths (8, and `8 n`), and nothing is assumed of other lengths. `AffineExt::identity()` only
fills the buffer that `batch_normalize` overwrites, so nothing is assumed of it either. -/
structure CurveOps.Spec {P A G : Type} [AddCommGroup G] (O : CurveOps P A)
    (V : CurveAbs P A G) : Prop where
  /-- `C::identity()`. -/
  identity : V.valid O.identity ∧ V.α O.identity = 0
  /-- `is_identity`: a point it accepts stands for the identity. -/
  isIdentity : ∀ p, V.valid p → O.isIdentity p = true → V.α p = 0
  /-- `double`. -/
  double : ∀ p, V.valid p → V.valid (O.double p) ∧ V.α (O.double p) = 2 • V.α p
  /-- `C + C`. -/
  add : ∀ p q, V.valid p → V.valid q →
    V.valid (O.add p q) ∧ V.α (O.add p q) = V.α p + V.α q
  /-- `C += AffineExt`. -/
  addMixed : ∀ p a, V.valid p → V.validA a →
    V.valid (O.addMixed p a) ∧ V.α (O.addMixed p a) = V.α p + V.αA a
  /-- `-AffineExt`. -/
  negA : ∀ a, V.validA a → V.validA (O.negA a) ∧ V.αA (O.negA a) = -V.αA a
  /-- `batch_normalize(&ps, &mut qs)` on slices of equal length: entry by entry, the normalized
  point. Its `invert().unwrap()` inverts a product of nonzero `Z`s. -/
  batchNormalize : ∀ (ps : List P) (qs : List A), (∀ p ∈ ps, V.valid p) →
    ps.length = qs.length →
    List.Forall₂ (fun p a => V.validA a ∧ V.αA a = V.α p) ps (O.batchNormalize ps qs)
  /-- `CurveAffine::to_curve`. -/
  toCurve : ∀ a, V.validA a → V.valid (O.toCurve a) ∧ V.α (O.toCurve a) = V.αA a

/-! ## The tables and the entry points -/

/-- `t` is the table of the point `p`: its entries are valid and stand for `(2j + 1)·p` (`t1`) and
`(2j + 1)·(λ·p)` (`t2`). -/
def TableOf {P A G : Type} [AddCommGroup G] (V : CurveAbs P A G) (lam : ℕ) (p : P)
    (t : Table A) : Prop :=
  ∀ j : Fin 4, V.validA (t.t1 j) ∧ V.αA (t.t1 j) = oddMultiples (V.α p) j ∧
    V.validA (t.t2 j) ∧ V.αA (t.t2 j) = oddMultiples (lam • V.α p) j

/-- **L2** (the tables), for models `window`, `tableNew` and `tableBatch` of `window_proj`,
`Table::new` and `Table::batch`, under H3 and H1: `window_proj p` holds eight points, valid ones
standing for `(2j + 1)·p` followed by `endo` of each; `Table::new(p)` is the table of `p`; and
`Table::batch(ps)` is one table per point, in order (the `chunks_exact(8)` ordering). Valid
points include the identity, whose table stands for the identity throughout. -/
def L2Of (window : ∀ {P A : Type}, CurveOps P A → P → List P)
    (tableNew : ∀ {P A : Type}, CurveOps P A → P → Option (Table A))
    (tableBatch : ∀ {P A : Type}, CurveOps P A → List P → Option (List (Table A))) : Prop :=
  ∀ {P A G : Type} [AddCommGroup G] (O : CurveOps P A) (V : CurveAbs P A G) (lam : ℕ),
    CurveOps.Spec O V → EndoSpec O V lam →
    (∀ p, V.valid p → (window O p).length = 8 ∧ ∀ j : Fin 4, ∃ w,
      (window O p)[(j : ℕ)]? = some w ∧ V.valid w ∧ V.α w = oddMultiples (V.α p) j ∧
      (window O p)[(j : ℕ) + 4]? = some (O.endo w)) ∧
    (∀ p, V.valid p → ∃ t, tableNew O p = some t ∧ TableOf V lam p t) ∧
    (∀ ps : List P, (∀ p ∈ ps, V.valid p) →
      ∃ ts, tableBatch O ps = some ts ∧ List.Forall₂ (TableOf V lam) ps ts)

/-- L2 for the model. -/
def L2_stmt : Prop :=
  L2Of (fun O p => windowProj O p) (fun O p => Table.new O p) (fun O ps => Table.batch O ps)

/-- **C** (end to end), under H0–H3: for every valid scalar `k`, `Decomposed::new(k)` does not
panic, and `mul_decomposed` with its result takes the table of any valid point `p` to a valid
point standing for `val k · p`, which is the reuse of one `Decomposed` across tables that the
module is for; and `mul_glv`, `Table::new(p).mul(k)` and `Table::batch(ps)[i].mul(k)` do not
panic and return valid points standing for `val k · p`. Only `Decomposed::new` builds a
`Decomposed`, and L2 gives the tables of `Table::new` and `Table::batch`. -/
def C_stmt : Prop :=
  ∀ {P A G Sc : Type} [AddCommGroup G] (O : CurveOps P A) (V : CurveAbs P A G)
    (S : ScalarAbs Sc) (n lam : ℕ) (f : DecomposeFn Sc),
    OrderSpec V n → EndoSpec O V lam → DecomposeSpec n lam S f → CurveOps.Spec O V →
    ∀ k : Sc, S.valid k →
      (∃ D, Decomposed.new f k = some D ∧ ∀ p t, V.valid p → TableOf V lam p t →
        ∃ r, t.mulDecomposed O.toLadderOps D = some r ∧ V.valid r ∧
          V.α r = S.val k • V.α p) ∧
      (∀ p, V.valid p → ∃ r, mulGlv O f p k = some r ∧ V.valid r ∧
        V.α r = S.val k • V.α p) ∧
      (∀ p, V.valid p → ∃ t r, Table.new O p = some t ∧ t.mul O f k = some r ∧
        V.valid r ∧ V.α r = S.val k • V.α p) ∧
      (∀ ps : List P, (∀ p ∈ ps, V.valid p) → ∃ ts, Table.batch O ps = some ts ∧
        List.Forall₂ (fun p t => ∃ r, t.mul O f k = some r ∧ V.valid r ∧
          V.α r = S.val k • V.α p) ps ts)

/-- **C-batch** (end to end), under H0–H3: for a valid scalar `k` and slices of equal length,
`batch_mul_same_scalar_vartime(points, k, output)` does not panic and leaves in each `output[i]` a
valid point standing for `val k · points[i]`. -/
def CBatch_stmt : Prop :=
  ∀ {P A G Sc : Type} [AddCommGroup G] (O : CurveOps P A) (V : CurveAbs P A G)
    (S : ScalarAbs Sc) (n lam : ℕ) (f : DecomposeFn Sc),
    OrderSpec V n → EndoSpec O V lam → DecomposeSpec n lam S f → CurveOps.Spec O V →
    ∀ k : Sc, S.valid k → ∀ (points : List A) (output : List P), (∀ a ∈ points, V.validA a) →
      points.length = output.length →
      ∃ rs, batchMulSameScalar O f points k output = some rs ∧
        List.Forall₂ (fun a r => V.valid r ∧ V.α r = S.val k • V.αA a) points rs

end PastaCurves.Glv
