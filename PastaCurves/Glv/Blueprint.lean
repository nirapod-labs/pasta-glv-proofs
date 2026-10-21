import PastaCurves.Glv.Spec

/-!
# The Blueprint: lemmas that imply the Spec

The proofs of the statements of `Spec.lean` are cut into lemmas, each the definition of a
proposition (`foo_stmt`) that is proved on its own, in `Proofs/Foo.lean`. A lemma that rests on
others takes their statements as hypotheses, so no proof file needs another; when such a
statement has hypotheses of its own, the lemma takes those too, so that it can use it. The second
half of this file proves every statement of the Spec from the lemmas (`W1_of`, …, and all at once
`spec_of`): Lean checks here that the lemmas imply the Spec, and `Final.lean` only applies
`spec_of` to the proofs.

The recoding's arithmetic is read through three functions of `k` alone: the digit `wdigit k`
written for an odd `k`, the next value `knext k`, and the number of passes `passes k`. The bound
`gmin m` on the magnitudes whose loop makes at least `m` passes comes with its recurrence; the
key lemma (`kl_stmt`) gives W2's length bound and W5's least failing magnitude.
-/

namespace PastaCurves.Glv.Blueprint

open PastaCurves.Glv Aeneas Aeneas.Std

/-! ## The recoding's arithmetic -/

/-- The digit `wnaf_digits` writes for an odd `k`, before the sign: `k mod 16`, taken in
`[-8, 8)`. -/
def wdigit (k : ℕ) : ℤ := if k % 16 < 8 then ((k % 16 : ℕ) : ℤ) else ((k % 16 : ℕ) : ℤ) - 16

/-- `k` after one pass of the loop: an odd `k` loses its digit, wrapped as a `u128`, and then
`k` is halved. -/
def knext (k : ℕ) : ℕ := if k % 2 = 1 then wrapU128 ((k : ℤ) - wdigit k) / 2 else k / 2

/-- A pass lowers a nonzero `k`. -/
theorem knext_lt (k : ℕ) (h : k ≠ 0) : knext k < k := by
  have hp : (2 : ℤ) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
  simp only [knext, wdigit, wrapU128, hp]
  split_ifs <;> omega

/-- The number of passes the loop makes from `k` until `k = 0`. -/
def passes (k : ℕ) : ℕ := if h : k = 0 then 0 else passes (knext k) + 1
termination_by k
decreasing_by exact knext_lt k h

/-- No pass from `0`. -/
@[simp] theorem passes_zero : passes 0 = 0 := by
  rw [passes]; simp

/-- From a nonzero `k`, one pass and then the passes from `knext k`. -/
theorem passes_of_ne (k : ℕ) (h : k ≠ 0) : passes k = passes (knext k) + 1 := by
  rw [passes]; simp [h]

/-- `k` four passes after an odd `k`, when none of them reaches `0`: `(k - d) / 16`, read through
the `u128` wrap. -/
def kq (k : ℕ) : ℕ := wrapU128 ((k : ℤ) - wdigit k) / 16

/-- The window `(gmin (j + 4), gmin (j + 3), gmin (j + 2), gmin (j + 1))` of the recurrence
below. -/
def gminW : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (8, 4, 2, 1)
  | j + 1 => match gminW j with
    | (a, b, c, d) => (min (2 * a) (16 * d - 7), a, b, c)

/-- A lower bound on every magnitude whose loop makes at least `m` passes (`kl_stmt`): `1, 2, 4,
8`, then `gmin m = min (2 · gmin (m - 1)) (16 · gmin (m - 4) - 7)`. A pass halves an even `k`;
an odd `k` takes four passes to reach `(k - d) / 16`, with `|d| ≤ 7`. -/
def gmin (m : ℕ) : ℕ := if m = 0 then 0 else if m ≤ 4 then 2 ^ (m - 1) else (gminW (m - 4)).1

/-- At 129 passes the bound is the least failing magnitude itself. -/
theorem gmin_129 : gmin 129 = leastFailing := by decide +kernel

/-- What a run on `a < 2^127` keeps: `k` stays below `2^127`, the passes end by position 128, the
digits are zero from `n` on, and the digits written so far and what `k` still holds make `±a`. -/
def ValInv (a : ℕ) (neg : Bool) (s : Wnaf.State) : Prop :=
  s.k < 2 ^ 127 ∧ s.n + passes s.k ≤ 128 ∧ (∀ i : Fin 128, s.n ≤ (i : ℕ) → s.digits i = 0) ∧
    ∑ i : Fin 128, s.digits i * 2 ^ (i : ℕ) + (if neg then -(s.k : ℤ) else s.k) * 2 ^ s.n =
      if neg then -(a : ℤ) else a

/-! ## Lemmas: one pass of `wnaf_digits` -/

/-- A pass takes `k` to `knext k`. -/
def step_k_stmt : Prop := ∀ (neg : Bool) (s : Wnaf.State), (Wnaf.step neg s).k = knext s.k

/-- A pass adds one to `n`. -/
def step_n_stmt : Prop := ∀ (neg : Bool) (s : Wnaf.State), (Wnaf.step neg s).n = s.n + 1

/-- A pass leaves the assertion and `i8` flags alone; it sets the `u128` flag exactly when `k` is
odd and `k - d` reaches `2^128`, and the bounds flag exactly when `k` is odd and `n ≥ 128`. -/
def step_flags_stmt : Prop :=
  ∀ (neg : Bool) (s : Wnaf.State),
    (Wnaf.step neg s).assertFailed = s.assertFailed ∧
    (Wnaf.step neg s).i8Overflow = s.i8Overflow ∧
    (Wnaf.step neg s).u128Overflow = (s.u128Overflow ||
      (decide (s.k % 2 = 1) && decide (2 ^ 128 ≤ (s.k : ℤ) - wdigit s.k))) ∧
    (Wnaf.step neg s).outOfBounds =
      (s.outOfBounds || (decide (s.k % 2 = 1) && decide (128 ≤ s.n)))

/-- A pass on an odd `k` writes its signed digit at position `n`, and changes no other digit. -/
def step_digits_stmt : Prop :=
  ∀ (neg : Bool) (s : Wnaf.State) (i : Fin 128),
    (Wnaf.step neg s).digits i =
      if s.k % 2 = 1 ∧ (i : ℕ) = s.n then (if neg then -wdigit s.k else wdigit s.k)
      else s.digits i

/-! ## Lemmas: the loop -/

/-- The loop adds `passes k` to `n`. -/
def loop_n_stmt : Prop :=
  step_k_stmt → step_n_stmt → ∀ (neg : Bool) (fuel : ℕ) (s : Wnaf.State), s.k ≤ fuel →
    (Wnaf.loop neg fuel s).n = s.n + passes s.k

/-- The loop leaves the assertion and `i8` flags alone, and sets the `u128` flag from no `k`
below `2^128 - 16`. -/
def loop_flags_stmt : Prop :=
  step_k_stmt → step_flags_stmt → ∀ (neg : Bool) (fuel : ℕ) (s : Wnaf.State),
    (Wnaf.loop neg fuel s).assertFailed = s.assertFailed ∧
    (Wnaf.loop neg fuel s).i8Overflow = s.i8Overflow ∧
    (s.k < 2 ^ 128 - 16 → (Wnaf.loop neg fuel s).u128Overflow = s.u128Overflow)

/-- The loop writes nothing out of bounds when its passes end by position 128. -/
def loop_oob_stmt : Prop :=
  step_k_stmt → step_n_stmt → step_flags_stmt → ∀ (neg : Bool) (fuel : ℕ) (s : Wnaf.State),
    s.k ≤ fuel → s.n + passes s.k ≤ 128 → (Wnaf.loop neg fuel s).outOfBounds = s.outOfBounds

/-- The loop keeps every digit a width-4 wNAF digit. -/
def loop_shape_stmt : Prop :=
  step_digits_stmt → ∀ (neg : Bool) (fuel : ℕ) (s : Wnaf.State),
    (∀ i, IsWnafDigit (s.digits i)) → ∀ i, IsWnafDigit ((Wnaf.loop neg fuel s).digits i)

/-- Writing `x` over a zero digit at position `m` adds `x·2^m` to the digits' value. -/
def sum_point_stmt : Prop :=
  ∀ (f g : Fin 128 → ℤ) (m : Fin 128) (x : ℤ), f m = 0 → g m = x → (∀ i, i ≠ m → g i = f i) →
    ∑ i : Fin 128, g i * 2 ^ (i : ℕ) = ∑ i : Fin 128, f i * 2 ^ (i : ℕ) + x * 2 ^ (m : ℕ)

/-- A pass from a nonzero `k` keeps the value invariant. -/
def step_value_stmt : Prop :=
  sum_point_stmt → step_k_stmt → step_n_stmt → step_digits_stmt →
    ∀ (a : ℕ) (neg : Bool) (s : Wnaf.State), s.k ≠ 0 → ValInv a neg s →
      ValInv a neg (Wnaf.step neg s)

/-- The loop keeps the value invariant. -/
def loop_value_stmt : Prop :=
  sum_point_stmt → step_k_stmt → step_n_stmt → step_digits_stmt → step_value_stmt →
    ∀ (a : ℕ) (neg : Bool) (fuel : ℕ) (s : Wnaf.State),
      ValInv a neg s → ValInv a neg (Wnaf.loop neg fuel s)

/-! ## Lemmas: the number of passes -/

/-- The recurrence of `gmin`. -/
def gmin_rec_stmt : Prop := ∀ m, 5 ≤ m → gmin m = min (2 * gmin (m - 1)) (16 * gmin (m - 4) - 7)

/-- `15 · gmin m ≥ 2^(m+2) + 7`, so `gmin m ≥ 2^(m-2)` (`gmin_ge`). The bound is tight at every
`m ≡ 1 (mod 4)`, `m = 129` among them, and it goes through an induction on the recurrence, where
the plain `2^(m-2)` does not: its second branch would only give `2^(m-2) - 7`. -/
def gmin_lower_stmt : Prop := gmin_rec_stmt → ∀ m, 1 ≤ m → 2 ^ (m + 2) + 7 ≤ 15 * gmin m

/-- From an odd `k` below `2^128`, either the next pass reaches `0` (one pass in all), or
`k = 16 q + d` with `q = kq k ≥ 1`, and four passes reach `q`. -/
def passes_odd_stmt : Prop :=
  ∀ k, k < 2 ^ 128 → k % 2 = 1 →
    (kq k = 0 ∧ passes k = 1) ∨
      (kq k ≠ 0 ∧ (k : ℤ) = 16 * kq k + wdigit k ∧ passes k = passes (kq k) + 4)

/-- The key lemma: a magnitude whose loop makes at least `m` passes is at least `gmin m`. -/
def kl_stmt : Prop :=
  gmin_rec_stmt → passes_odd_stmt → ∀ k, k < 2 ^ 128 → ∀ m, m ≤ passes k → gmin m ≤ k

/-! ## Lemmas: the ladder -/

/-- `add_digit` in a group, over the odd multiples of `p`, adds `d·p`. -/
def addDigit_group_stmt : Prop :=
  ∀ {G : Type} [AddCommGroup G] (acc p : G) (d : ℤ), IsWnafDigit d →
    addDigit (groupOps G) acc (oddMultiples p) d = some (acc + d • p)

/-- The positions below `j + 1` are those below `j`, and `j`. -/
def sum_below_succ_stmt : Prop :=
  ∀ (f : Fin 128 → ℤ) (j : ℕ) (hj : j < 128),
    (∑ i : Fin 128, if (i : ℕ) < j + 1 then f i else 0) =
      (∑ i : Fin 128, if (i : ℕ) < j then f i else 0) + f ⟨j, hj⟩

/-- The ladder's loop in a group, from position `j ≤ len`: the accumulator is doubled `j` times,
and the digits at positions `i < j` count `2^i` times. At `j = len` the skipped doubling acts on
`acc = 0`. -/
def ladderLoop_group_stmt : Prop :=
  sum_below_succ_stmt → addDigit_group_stmt →
    ∀ {G : Type} [AddCommGroup G] (p q : G) (D : Decomposed),
      (∀ i, IsWnafDigit (D.digits1 i)) → (∀ i, IsWnafDigit (D.digits2 i)) → D.len ≤ 128 →
      ∀ (j : ℕ) (acc : G), j ≤ D.len → (j < D.len ∨ acc = 0) →
        ladderLoop (groupOps G) ⟨oddMultiples p, oddMultiples q⟩ D j acc =
          some ((2 ^ j : ℕ) • acc +
            (∑ i : Fin 128, if (i : ℕ) < j then D.digits1 i * 2 ^ (i : ℕ) else 0) • p +
            (∑ i : Fin 128, if (i : ℕ) < j then D.digits2 i * 2 ^ (i : ℕ) else 0) • q)

/-- One `add_digit` over the curve follows `add_digit` over the group under `α`. -/
def addDigit_transport_stmt : Prop :=
  ∀ {P A G : Type} [AddCommGroup G] (O : CurveOps P A) (V : CurveAbs P A G),
    CurveOps.Spec O V → ∀ (acc : P) (tab : Fin 4 → A) (d : ℤ), V.valid acc →
    (∀ j, V.validA (tab j)) →
      (addDigit O.toLadderOps acc tab d).map V.α =
        addDigit (groupOps G) (V.α acc) (fun j => V.αA (tab j)) d ∧
      ∀ r, addDigit O.toLadderOps acc tab d = some r → V.valid r

/-- The ladder over the curve operations follows the ladder over the group under `α`: the same
outcome, through valid points. -/
def transport_stmt : Prop :=
  addDigit_transport_stmt →
    ∀ {P A G : Type} [AddCommGroup G] (O : CurveOps P A) (V : CurveAbs P A G),
      CurveOps.Spec O V → ∀ (t : Table A) (D : Decomposed),
      (∀ j, V.validA (t.t1 j) ∧ V.validA (t.t2 j)) → ∀ (j : ℕ) (acc : P), V.valid acc →
        (ladderLoop O.toLadderOps t D j acc).map V.α =
          ladderLoop (groupOps G) ⟨fun j => V.αA (t.t1 j), fun j => V.αA (t.t2 j)⟩ D j
            (V.α acc) ∧
        ∀ r, ladderLoop O.toLadderOps t D j acc = some r → V.valid r

/-! ## Lemmas: the tables -/

/-- L2's first part: the window of a valid point. -/
def window_stmt : Prop :=
  ∀ {P A G : Type} [AddCommGroup G] (O : CurveOps P A) (V : CurveAbs P A G) (lam : ℕ),
    CurveOps.Spec O V → EndoSpec O V lam → ∀ p, V.valid p →
      (windowProj O p).length = 8 ∧ ∀ j : Fin 4, ∃ w,
        (windowProj O p)[(j : ℕ)]? = some w ∧ V.valid w ∧ V.α w = oddMultiples (V.α p) j ∧
        (windowProj O p)[(j : ℕ) + 4]? = some (O.endo w)

/-- Every point of the window of a valid point is valid. -/
def windowValid_stmt : Prop :=
  ∀ {P A G : Type} [AddCommGroup G] (O : CurveOps P A) (V : CurveAbs P A G) (lam : ℕ),
    CurveOps.Spec O V → EndoSpec O V lam → ∀ p, V.valid p → ∀ q ∈ windowProj O p, V.valid q

/-- Affine points that normalize the window of a valid point, entry by entry, make its table. -/
def ofWindow_stmt : Prop :=
  ∀ {P A G : Type} [AddCommGroup G] (O : CurveOps P A) (V : CurveAbs P A G) (lam : ℕ),
    CurveOps.Spec O V → EndoSpec O V lam → ∀ p, V.valid p → ∀ c : List A,
      List.Forall₂ (fun q a => V.validA a ∧ V.αA a = V.α q) (windowProj O p) c →
      ∃ t, Table.ofWindow c = some t ∧ TableOf V lam p t

/-- `Table::new` on a valid point builds its table. -/
def tableNew_stmt : Prop :=
  windowValid_stmt → ofWindow_stmt →
    ∀ {P A G : Type} [AddCommGroup G] (O : CurveOps P A) (V : CurveAbs P A G) (lam : ℕ),
      CurveOps.Spec O V → EndoSpec O V lam → ∀ p, V.valid p →
        ∃ t, Table.new O p = some t ∧ TableOf V lam p t

/-- `chunks_exact(8)` after a map that gives eight entries per element: chunk `i` is related, entry
by entry, to the eight entries of element `i`. -/
def chunks_stmt : Prop :=
  ∀ {X Y Z : Type} (R : Y → Z → Prop) (g : X → List Y) (xs : List X) (zs : List Z),
    (∀ x, (g x).length = 8) → List.Forall₂ R (xs.flatMap g) zs →
      List.Forall₂ (fun x c => List.Forall₂ R (g x) c) xs (chunksExact8 zs)

/-- `Table::batch` on valid points builds their tables, in order. -/
def tableBatch_stmt : Prop :=
  windowValid_stmt → ofWindow_stmt → chunks_stmt →
    ∀ {P A G : Type} [AddCommGroup G] (O : CurveOps P A) (V : CurveAbs P A G) (lam : ℕ),
      CurveOps.Spec O V → EndoSpec O V lam → ∀ ps : List P, (∀ p ∈ ps, V.valid p) →
        ∃ ts, Table.batch O ps = some ts ∧ List.Forall₂ (TableOf V lam) ps ts

/-! ## Lemmas: the entry points -/

/-- `Decomposed::new` on a valid scalar: no panic, digits of wNAF shape that are zero from
`len ≤ 128` on, and the two halves' values combine to `k` modulo `n`. -/
def decomposedNew_stmt : Prop :=
  W3_stmt → D_stmt → W4_stmt → ∀ {Sc : Type} (S : ScalarAbs Sc) (n lam : ℕ)
    (f : DecomposeFn Sc), DecomposeSpec n lam S f → ∀ k, S.valid k →
    ∃ D, Decomposed.new f k = some D ∧
      (∀ i, IsWnafDigit (D.digits1 i)) ∧ (∀ i, IsWnafDigit (D.digits2 i)) ∧ D.len ≤ 128 ∧
      (∀ i : Fin 128, D.len ≤ i → D.digits1 i = 0 ∧ D.digits2 i = 0) ∧
      (∑ i : Fin 128, D.digits1 i * 2 ^ (i : ℕ)) +
        (∑ i : Fin 128, D.digits2 i * 2 ^ (i : ℕ)) * lam ≡ S.val k [ZMOD n]

/-- In a group, `n • x = 0` makes an integer multiple of `x` depend on the integer modulo `n`
only. -/
def smul_congr_stmt : Prop :=
  ∀ {G : Type} [AddCommGroup G] (x : G) (n : ℕ) (a b : ℤ), n • x = 0 → a ≡ b [ZMOD n] →
    a • x = b • x

/-- The last loop of `batch_mul_same_scalar_vartime`, over lists of equal length, each table
related to an element of `xs`. -/
def mulEach_stmt : Prop :=
  ∀ {P A X : Type} (O : LadderOps P A) (D : Decomposed) (R : X → P → Prop) (xs : List X)
    (outs : List P) (ts : List (Table A)), outs.length = xs.length →
    List.Forall₂ (fun x t => ∃ r, t.mulDecomposed O D = some r ∧ R x r) xs ts →
    ∃ rs, mulEach O D outs ts = some rs ∧ List.Forall₂ R xs rs

/-! ## The Spec from the lemmas -/

/-- `leastFailing` lies between `2^127` and `2^128 - 16`. -/
theorem leastFailing_bounds : 2 ^ 127 < leastFailing ∧ leastFailing < 2 ^ 128 - 16 := by
  unfold leastFailing; norm_num

/-- `gmin m ≥ 2^(m-2)`, from the lemma's sharper bound. -/
theorem gmin_ge (hrec : gmin_rec_stmt) (hlow : gmin_lower_stmt) (m : ℕ) (hm : 2 ≤ m) :
    2 ^ (m - 2) ≤ gmin m := by
  have h := hlow hrec m (by omega)
  have e : 2 ^ (m + 2) = 16 * 2 ^ (m - 2) := by
    rw [show m + 2 = (m - 2) + 4 by omega, pow_add]; ring
  omega

/-- Below `leastFailing` the loop makes at most 128 passes. -/
theorem passes_le_128 (hrec : gmin_rec_stmt) (hodd : passes_odd_stmt) (hkl : kl_stmt) (a : ℕ)
    (ha : a < leastFailing) : passes a ≤ 128 := by
  have hb := leastFailing_bounds
  by_contra h
  have h129 := hkl hrec hodd a (by omega) 129 (by omega)
  rw [gmin_129] at h129
  omega

/-- On a `u128` the loop makes at most `⌊log₂ a⌋ + 2` passes. -/
theorem passes_le_log (hrec : gmin_rec_stmt) (hlow : gmin_lower_stmt) (hodd : passes_odd_stmt)
    (hkl : kl_stmt) (a : ℕ) (ha : a < 2 ^ 128) : passes a ≤ Nat.log2 a + 2 := by
  by_cases hm : passes a ≤ 1
  · omega
  · have h := (gmin_ge hrec hlow (passes a) (by omega)).trans
      (hkl hrec hodd a ha (passes a) le_rfl)
    have h1 : 1 ≤ 2 ^ (passes a - 2) := Nat.one_le_two_pow
    have h2 := (Nat.le_log2 (by omega)).2 h
    omega

/-- `exec` returns the number of passes as `n`. -/
theorem exec_n (hk : step_k_stmt) (hn : step_n_stmt) (hln : loop_n_stmt) (a : ℕ) (neg : Bool) :
    (Wnaf.exec a neg).n = passes a := by
  show (Wnaf.loop neg a (Wnaf.init a)).n = passes a
  rw [hln hk hn neg a (Wnaf.init a) le_rfl]
  simp [Wnaf.init]

/-- W2 from the lemmas. -/
theorem W2_of (hk : step_k_stmt) (hn : step_n_stmt) (hln : loop_n_stmt) (hrec : gmin_rec_stmt)
    (hlow : gmin_lower_stmt) (hodd : passes_odd_stmt) (hkl : kl_stmt) : W2_stmt := by
  unfold W2_stmt W2Of
  have hb := leastFailing_bounds
  refine ⟨fun a neg ha => ?_, fun a neg ha => ?_⟩
  · rw [exec_n hk hn hln]; exact passes_le_log hrec hlow hodd hkl a ha
  · rw [exec_n hk hn hln]; exact passes_le_128 hrec hodd hkl a (by omega)

set_option maxRecDepth 100000 in
/-- W5's second half, evaluated by the kernel. -/
theorem exec_leastFailing : ∀ neg : Bool,
    (Wnaf.exec leastFailing neg).n = 129 ∧ (Wnaf.exec leastFailing neg).outOfBounds = true := by
  decide +kernel

/-- W5 from the lemmas. -/
theorem W5_of (hk : step_k_stmt) (hn : step_n_stmt) (hf : step_flags_stmt) (hln : loop_n_stmt)
    (hlf : loop_flags_stmt) (hlo : loop_oob_stmt) (hrec : gmin_rec_stmt)
    (hodd : passes_odd_stmt) (hkl : kl_stmt) : W5_stmt := by
  unfold W5_stmt W5Of
  have hb := leastFailing_bounds
  refine ⟨fun a neg ha => ?_, exec_leastFailing⟩
  have hp := passes_le_128 hrec hodd hkl a ha
  obtain ⟨-, hi8, hu⟩ := hlf hk hf neg a (Wnaf.init a)
  refine ⟨by rw [exec_n hk hn hln]; exact hp, ?_, hu (by show a < _; omega), hi8⟩
  exact hlo hk hn hf neg a (Wnaf.init a) le_rfl (by simpa [Wnaf.init] using hp)

set_option maxRecDepth 100000 in
/-- The `u128` flag on the last sixteen magnitudes, evaluated by the kernel. -/
theorem exec_top16 : ∀ (i : Fin 16) (neg : Bool),
    (Wnaf.exec (2 ^ 128 - 16 + i) neg).u128Overflow =
      decide ((i : ℕ) = 9 ∨ (i : ℕ) = 11 ∨ (i : ℕ) = 13 ∨ (i : ℕ) = 15) := by
  decide +kernel

/-- W6 from the lemmas. -/
theorem W6_of (hk : step_k_stmt) (hf : step_flags_stmt) (hlf : loop_flags_stmt) : W6_stmt := by
  unfold W6_stmt W6Of
  intro a neg ha
  obtain ⟨has, hi8, hu⟩ := hlf hk hf neg a (Wnaf.init a)
  refine ⟨?_, hi8, ?_⟩
  · show (Wnaf.loop neg a (Wnaf.init a)).assertFailed = true ↔ _
    rw [has]
    simp only [Wnaf.init, Nat.shiftRight_eq_div_pow, bne_iff_ne, ne_eq, Nat.div_eq_zero_iff]
    omega
  · by_cases hlo : a < 2 ^ 128 - 16
    · show (Wnaf.loop neg a (Wnaf.init a)).u128Overflow = true ↔ _
      rw [hu hlo]
      simp only [Wnaf.init, Bool.false_eq_true, false_iff]
      omega
    · obtain ⟨i, rfl⟩ : ∃ i : Fin 16, a = 2 ^ 128 - 16 + i :=
        ⟨⟨a - (2 ^ 128 - 16), by omega⟩, by dsimp only; omega⟩
      have hi := i.isLt
      rw [exec_top16 i neg, decide_eq_true_iff]
      omega

/-- W1 from W5 and W6. -/
theorem W1_of (hW5 : W5_stmt) (hW6 : W6_stmt) : W1_stmt := by
  unfold W1_stmt W1Of
  unfold W5_stmt W5Of at hW5
  unfold W6_stmt W6Of at hW6
  intro a neg ha
  have hb := leastFailing_bounds
  obtain ⟨-, ho, hu, hi⟩ := hW5.1 a neg (by omega)
  have has := (hW6 a neg (by omega)).1
  refine ⟨?_, ho, hu, hi⟩
  cases h : (Wnaf.exec a neg).assertFailed
  · rfl
  · have := has.1 h
    omega

/-- W3 from the lemmas. -/
theorem W3_of (hd : step_digits_stmt) (hls : loop_shape_stmt) : W3_stmt := by
  unfold W3_stmt W3Of
  intro a neg _ i
  have h := hls hd neg a (Wnaf.init a) (fun _ => Or.inl rfl) i
  refine ⟨h, ?_⟩
  show ((Wnaf.loop neg a (Wnaf.init a)).digits i).natAbs / 2 < 4
  rcases h with h | ⟨-, h1, h2⟩
  · rw [h]; decide
  · omega

/-- W4 from the lemmas. -/
theorem W4_of (hsp : sum_point_stmt) (hk : step_k_stmt) (hn : step_n_stmt)
    (hd : step_digits_stmt) (hsv : step_value_stmt) (hlv : loop_value_stmt)
    (hrec : gmin_rec_stmt) (hodd : passes_odd_stmt) (hkl : kl_stmt) : W4_stmt := by
  unfold W4_stmt W4Of
  intro a neg ha
  have hb := leastFailing_bounds
  have hinit : ValInv a neg (Wnaf.init a) := by
    unfold ValInv
    refine ⟨ha, ?_, fun _ _ => rfl, ?_⟩
    · simpa [Wnaf.init] using passes_le_128 hrec hodd hkl a (by omega)
    · simp [Wnaf.init]
  obtain ⟨-, -, hz, hsum⟩ := hlv hsp hk hn hd hsv a neg a (Wnaf.init a) hinit
  have hk0 : (Wnaf.loop neg a (Wnaf.init a)).k = 0 := Wnaf.exec_k a neg
  rw [hk0] at hsum
  simp only [Nat.cast_zero, neg_zero, ite_self, zero_mul, add_zero] at hsum
  exact ⟨hsum, hz⟩

/-- D from W1, W2 and W4. -/
theorem D_of (hW1 : W1_stmt) (hW2 : W2_stmt) (hW4 : W4_stmt) : D_stmt := by
  unfold D_stmt DOf
  unfold W1_stmt W1Of at hW1
  unfold W2_stmt W2Of at hW2
  unfold W4_stmt W4Of at hW4
  intro neg1 neg2 a1 a2 h1 h2
  obtain ⟨af1, o1, u1, i1⟩ := hW1 a1 neg1 h1
  obtain ⟨af2, o2, u2, i2⟩ := hW1 a2 neg2 h2
  have hz1 := (hW4 a1 neg1 h1).2
  have hz2 := (hW4 a2 neg2 h2).2
  refine ⟨⟨(Wnaf.exec a1 neg1).digits, (Wnaf.exec a2 neg2).digits,
      max (Wnaf.exec a1 neg1).n (Wnaf.exec a2 neg2).n⟩, ?_, rfl, rfl, rfl,
    max_le (hW2.2 a1 neg1 h1) (hW2.2 a2 neg2 h2),
    fun i hi => ⟨hz1 i (le_of_max_le_left hi), hz2 i (le_of_max_le_right hi)⟩⟩
  simp [Decomposed.ofHalves, Wnaf.State.panics, Wnaf.State.panicsIn, af1, o1, u1, i1, af2, o2,
    u2, i2]

/-- L1 from the lemmas. -/
theorem L1_of (hsb : sum_below_succ_stmt) (had : addDigit_group_stmt)
    (hll : ladderLoop_group_stmt) : L1_stmt := by
  unfold L1_stmt L1Of
  intro G _ p q D h1 h2 hlen hz
  show ladderLoop (groupOps G) ⟨oddMultiples p, oddMultiples q⟩ D D.len 0 = _
  have e1 : (∑ i : Fin 128, if (i : ℕ) < D.len then D.digits1 i * 2 ^ (i : ℕ) else 0) =
      ∑ i : Fin 128, D.digits1 i * 2 ^ (i : ℕ) :=
    Finset.sum_congr rfl fun i _ => by
      split_ifs with h
      · rfl
      · rw [(hz i (by omega)).1, zero_mul]
  have e2 : (∑ i : Fin 128, if (i : ℕ) < D.len then D.digits2 i * 2 ^ (i : ℕ) else 0) =
      ∑ i : Fin 128, D.digits2 i * 2 ^ (i : ℕ) :=
    Finset.sum_congr rfl fun i _ => by
      split_ifs with h
      · rfl
      · rw [(hz i (by omega)).2, zero_mul]
  rw [hll hsb had p q D h1 h2 hlen D.len 0 le_rfl (Or.inr rfl), smul_zero, zero_add, e1, e2]

/-- L2 from the lemmas. -/
theorem L2_of (hw : window_stmt) (hwv : windowValid_stmt) (hov : ofWindow_stmt)
    (hc : chunks_stmt) (htn : tableNew_stmt) (htb : tableBatch_stmt) : L2_stmt := by
  unfold L2_stmt L2Of
  intro P A G _ O V lam hO hE
  exact ⟨hw O V lam hO hE, htn hwv hov O V lam hO hE, htb hwv hov hc O V lam hO hE⟩

/-- The ladder over the curve, from the table of a valid point `p` and digits that encode `kv`
modulo `n`, returns a valid point standing for `kv · p`: the step that C and C-batch share. -/
theorem mulDecomposed_of (hL1 : L1_stmt) (hat : addDigit_transport_stmt) (htr : transport_stmt)
    (hsc : smul_congr_stmt)
    {P A G : Type} [AddCommGroup G] (O : CurveOps P A) (V : CurveAbs P A G) (n lam kv : ℕ)
    (hord : OrderSpec V n) (hO : CurveOps.Spec O V) (D : Decomposed)
    (h1 : ∀ i, IsWnafDigit (D.digits1 i)) (h2 : ∀ i, IsWnafDigit (D.digits2 i))
    (hlen : D.len ≤ 128) (hz : ∀ i : Fin 128, D.len ≤ i → D.digits1 i = 0 ∧ D.digits2 i = 0)
    (hcong : (∑ i : Fin 128, D.digits1 i * 2 ^ (i : ℕ)) +
      (∑ i : Fin 128, D.digits2 i * 2 ^ (i : ℕ)) * lam ≡ kv [ZMOD n])
    (p : P) (t : Table A) (hp : V.valid p) (ht : TableOf V lam p t) :
    ∃ r, t.mulDecomposed O.toLadderOps D = some r ∧ V.valid r ∧ V.α r = kv • V.α p := by
  obtain ⟨hmap, hvalid⟩ := htr hat O V hO t D (fun j => ⟨(ht j).1, (ht j).2.2.1⟩) D.len O.identity
    hO.identity.1
  have htab : (⟨fun j => V.αA (t.t1 j), fun j => V.αA (t.t2 j)⟩ : Table G) =
      ⟨oddMultiples (V.α p), oddMultiples (lam • V.α p)⟩ := by
    congr 1 <;> funext j
    · exact (ht j).2.1
    · exact (ht j).2.2.2
  have hL : ladderLoop (groupOps G) ⟨oddMultiples (V.α p), oddMultiples (lam • V.α p)⟩ D D.len 0 =
      some ((∑ i : Fin 128, D.digits1 i * 2 ^ (i : ℕ)) • V.α p +
        (∑ i : Fin 128, D.digits2 i * 2 ^ (i : ℕ)) • (lam • V.α p)) :=
    hL1 (V.α p) (lam • V.α p) D h1 h2 hlen hz
  rw [hO.identity.2, htab, hL] at hmap
  cases hr : ladderLoop O.toLadderOps t D D.len O.identity with
  | none => simp [hr] at hmap
  | some r =>
    rw [hr, Option.map_some, Option.some.injEq] at hmap
    refine ⟨r, hr, hvalid r hr, ?_⟩
    rw [hmap]
    calc _ = ((∑ i : Fin 128, D.digits1 i * 2 ^ (i : ℕ)) +
          (∑ i : Fin 128, D.digits2 i * 2 ^ (i : ℕ)) * (lam : ℤ)) • V.α p := by
          rw [add_smul, mul_smul, natCast_zsmul]
      _ = (kv : ℤ) • V.α p := hsc (V.α p) n _ _ (hord p hp) hcong
      _ = kv • V.α p := natCast_zsmul _ _

/-- C from the lemmas and the Spec's other statements. -/
theorem C_of (hW3 : W3_stmt) (hD : D_stmt) (hW4 : W4_stmt) (hL1 : L1_stmt) (hL2 : L2_stmt)
    (hdn : decomposedNew_stmt) (hat : addDigit_transport_stmt) (htr : transport_stmt)
    (hsc : smul_congr_stmt) : C_stmt := by
  unfold C_stmt
  intro P A G Sc _ O V S n lam f hord hE hdec hO k hk
  obtain ⟨D, hDnew, h1, h2, hlen, hz, hcong⟩ := hdn hW3 hD hW4 S n lam f hdec k hk
  have hcore : ∀ p t, V.valid p → TableOf V lam p t →
      ∃ r, t.mulDecomposed O.toLadderOps D = some r ∧ V.valid r ∧ V.α r = S.val k • V.α p :=
    fun p t hp ht =>
      mulDecomposed_of hL1 hat htr hsc O V n lam (S.val k) hord hO D h1 h2 hlen hz hcong p t hp
        ht
  have hmul : ∀ (t : Table A) r, t.mulDecomposed O.toLadderOps D = some r →
      t.mul O f k = some r := by
    intro t r hr; simp [Table.mul, hDnew, hr]
  unfold L2_stmt L2Of at hL2
  obtain ⟨-, hnew, hbatch⟩ := hL2 O V lam hO hE
  have hnew' : ∀ p, V.valid p → ∃ t, Table.new O p = some t ∧ TableOf V lam p t := hnew
  have hbatch' : ∀ ps : List P, (∀ p ∈ ps, V.valid p) →
      ∃ ts, Table.batch O ps = some ts ∧ List.Forall₂ (TableOf V lam) ps ts := hbatch
  refine ⟨⟨D, hDnew, hcore⟩, fun p hp => ?_, fun p hp => ?_, fun ps hps => ?_⟩
  · unfold mulGlv
    split
    · rename_i hid
      exact ⟨O.identity, rfl, hO.identity.1,
        by rw [hO.identity.2, hO.isIdentity p hp hid, smul_zero]⟩
    · obtain ⟨t, ht, htab⟩ := hnew' p hp
      obtain ⟨r, hr, hv, hα⟩ := hcore p t hp htab
      exact ⟨r, by simp [ht, hmul t r hr], hv, hα⟩
  · obtain ⟨t, ht, htab⟩ := hnew' p hp
    obtain ⟨r, hr, hv, hα⟩ := hcore p t hp htab
    exact ⟨t, r, ht, hmul t r hr, hv, hα⟩
  · obtain ⟨ts, hts, hall⟩ := hbatch' ps hps
    refine ⟨ts, hts, ((List.forall₂_and_left _ _).2 ⟨hps, hall⟩).imp fun p t h => ?_⟩
    obtain ⟨r, hr, hv, hα⟩ := hcore p t h.1 h.2
    exact ⟨r, hmul t r hr, hv, hα⟩

/-- C-batch from the lemmas and the Spec's other statements. -/
theorem CBatch_of (hW3 : W3_stmt) (hD : D_stmt) (hW4 : W4_stmt) (hL1 : L1_stmt)
    (hL2 : L2_stmt) (hdn : decomposedNew_stmt) (hat : addDigit_transport_stmt)
    (htr : transport_stmt) (hsc : smul_congr_stmt) (hme : mulEach_stmt) : CBatch_stmt := by
  unfold CBatch_stmt
  intro P A G Sc _ O V S n lam f hord hE hdec hO k hk points output hpts hlen
  obtain ⟨D, hDnew, h1, h2, hl, hz, hcong⟩ := hdn hW3 hD hW4 S n lam f hdec k hk
  unfold L2_stmt L2Of at hL2
  obtain ⟨-, -, hbatch⟩ := hL2 O V lam hO hE
  have hbatch' : ∀ ps : List P, (∀ p ∈ ps, V.valid p) →
      ∃ ts, Table.batch O ps = some ts ∧ List.Forall₂ (TableOf V lam) ps ts := hbatch
  unfold batchMulSameScalar
  rw [if_neg (not_not.mpr hlen)]
  split
  · rename_i he
    obtain rfl := List.isEmpty_iff.mp he
    obtain rfl := List.eq_nil_of_length_eq_zero hlen.symm
    exact ⟨[], rfl, List.Forall₂.nil⟩
  · have hv : ∀ q ∈ points.map O.toCurve, V.valid q := by
      intro q hq
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
      exact (hO.toCurve a (hpts a ha)).1
    obtain ⟨ts, hts, hall⟩ := hbatch' _ hv
    rw [List.forall₂_map_left_iff] at hall
    have hall' : List.Forall₂ (fun a t => ∃ r, t.mulDecomposed O.toLadderOps D = some r ∧
        (V.valid r ∧ V.α r = S.val k • V.αA a)) points ts :=
      ((List.forall₂_and_left _ _).2 ⟨hpts, hall⟩).imp fun a t h => by
        obtain ⟨r, hr, hvr, hα⟩ := mulDecomposed_of hL1 hat htr hsc O V n lam (S.val k) hord hO
          D h1 h2 hl hz hcong _ t (hO.toCurve a h.1).1 h.2
        exact ⟨r, hr, hvr, by rw [hα, (hO.toCurve a h.1).2]⟩
    obtain ⟨rs, hrs, hR⟩ := hme O.toLadderOps D (fun a r => V.valid r ∧ V.α r = S.val k • V.αA a)
      points (points.map O.toCurve) ts (by simp) hall'
    exact ⟨rs, by simp [hDnew, hts, hrs], hR⟩

/-- Every statement of the Spec from the 29 lemmas: what `Final.lean` applies to their proofs. -/
theorem spec_of (hk : step_k_stmt) (hn : step_n_stmt) (hf : step_flags_stmt)
    (hd : step_digits_stmt) (hln : loop_n_stmt) (hlf : loop_flags_stmt) (hlo : loop_oob_stmt)
    (hls : loop_shape_stmt) (hsp : sum_point_stmt) (hsv : step_value_stmt)
    (hlv : loop_value_stmt) (hrec : gmin_rec_stmt) (hlow : gmin_lower_stmt)
    (hodd : passes_odd_stmt) (hkl : kl_stmt) (had : addDigit_group_stmt)
    (hsb : sum_below_succ_stmt) (hll : ladderLoop_group_stmt) (hat : addDigit_transport_stmt)
    (htr : transport_stmt) (hw : window_stmt) (hwv : windowValid_stmt) (hov : ofWindow_stmt)
    (htn : tableNew_stmt) (hc : chunks_stmt) (htb : tableBatch_stmt) (hdn : decomposedNew_stmt)
    (hsc : smul_congr_stmt) (hme : mulEach_stmt) :
    W1_stmt ∧ W2_stmt ∧ W3_stmt ∧ W4_stmt ∧ W5_stmt ∧ W6_stmt ∧ D_stmt ∧ L1_stmt ∧ L2_stmt ∧
      C_stmt ∧ CBatch_stmt := by
  have hW2 : W2_stmt := W2_of hk hn hln hrec hlow hodd hkl
  have hW3 : W3_stmt := W3_of hd hls
  have hW4 : W4_stmt := W4_of hsp hk hn hd hsv hlv hrec hodd hkl
  have hW5 : W5_stmt := W5_of hk hn hf hln hlf hlo hrec hodd hkl
  have hW6 : W6_stmt := W6_of hk hf hlf
  have hW1 : W1_stmt := W1_of hW5 hW6
  have hD : D_stmt := D_of hW1 hW2 hW4
  have hL1 : L1_stmt := L1_of hsb had hll
  have hL2 : L2_stmt := L2_of hw hwv hov hc htn htb
  exact ⟨hW1, hW2, hW3, hW4, hW5, hW6, hD, hL1, hL2, C_of hW3 hD hW4 hL1 hL2 hdn hat htr hsc,
    CBatch_of hW3 hD hW4 hL1 hL2 hdn hat htr hsc hme⟩

end PastaCurves.Glv.Blueprint
