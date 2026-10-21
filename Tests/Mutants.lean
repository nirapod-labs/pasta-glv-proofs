import PastaCurves.Glv.Spec

/-!
# Mutation tests

Each mutant changes the model in one place, and the theorems below prove that the statements
of `Spec.lean`, applied to the mutant (`W4Of (execK noCarry)`, …), are false. So the statements
are not vacuous: they notice these bugs. Every counterexample is checked by the kernel
(`decide +kernel`, never `native_decide`).

The `wnaf_digits` mutants come from one copy of the model with eight knobs (`Knobs`).
`execK_default` proves that with the default knobs the copy is the model, so each mutant differs
from the model in exactly the knob it sets. Two of them break only the checks, which only W6
looks at: below `2^127` the flags are false anyway, and on the four magnitudes where the `u128`
check fires, a debug build's assertion panics first.

D and L2 take their model as an argument too, and each has a mutant that breaks it. C and C-batch
are built from the others; `Tests/NonVacuity.lean` shows that they pin the result down
exactly on an instance with an injective abstraction.

One natural mutant, "an extra first doubling" in the ladder, is equivalent to the model: dropping
the skip of the first doubling only doubles the identity, and `noSkip_eq` proves the two equal in
every group. No statement can fail on it. The ladder is tested instead with a doubling
that does change the result: the doubling moved after the additions, which doubles the final
accumulator once too often (`mulDecLate`).
-/

open PastaCurves.Glv PastaCurves.Glv.Wnaf

namespace Mutation

/-! ## `wnaf_digits` with knobs -/

/-- Where a mutant departs from the model; the defaults are the model. -/
structure Knobs where
  /-- `k & mask`: `0xF` is width 4, `0x1F` width 5. -/
  mask : ℕ := 0xF
  /-- `low >= half`. -/
  half : ℤ := 8
  /-- `low - full`. -/
  full : ℤ := 16
  /-- `let mut n = n0;`. -/
  n0 : ℕ := 0
  /-- Whether `k += (-d) as u128;` is kept. -/
  carry : Bool := true
  /-- Whether the two branches of `if negate { -d } else { d }` are swapped. -/
  flip : Bool := false
  /-- Whether the `u128` check looks at the wrapped result, where it never fires. -/
  flagAfterWrap : Bool := false
  /-- Whether `debug_assert!(a >> 127 == 0, …)` is gone. -/
  noAssert : Bool := false

/-- `init` with the mutant's first `n`, and the assertion unless it is removed. -/
def initK (m : Knobs) (a : ℕ) : State :=
  { init a with n := m.n0, assertFailed := !m.noAssert && (a >>> 127 != 0) }

/-- `emit` with the knobs applied. -/
def emitK (m : Knobs) (neg : Bool) (s : State) : State :=
  let low : ℤ := wrapI8 (s.k &&& m.mask : ℕ)
  let d : ℤ := if m.half ≤ low then wrapI8 (low - m.full) else low
  let s' := write s (if neg != m.flip then wrapI8 (-d) else d)
  let x : ℤ := if 0 ≤ d then (s'.k : ℤ) - wrapU128 d
    else if m.carry then (s'.k : ℤ) + wrapU128 (wrapI8 (-d)) else s'.k
  { s' with
    k := wrapU128 x
    u128Overflow := s'.u128Overflow || overU128 (if m.flagAfterWrap then (wrapU128 x : ℤ) else x)
    i8Overflow := s'.i8Overflow || (decide (m.half ≤ low) && overI8 (low - m.full)) ||
      (neg && overI8 (-d)) || (!decide (0 ≤ d) && overI8 (-d)) }

/-- `step` over `emitK`. -/
def stepK (m : Knobs) (neg : Bool) (s : State) : State :=
  let s := if s.k &&& 1 = 1 then emitK m neg s else s
  { s with n := s.n + 1, k := s.k >>> 1 }

/-- `loop` over `stepK`. -/
def loopK (m : Knobs) (neg : Bool) : ℕ → State → State
  | 0, s => s
  | fuel + 1, s => if s.k = 0 then s else loopK m neg fuel (stepK m neg s)

/-- `exec` with the knobs applied. -/
def execK (m : Knobs) (a : ℕ) (neg : Bool) : State := loopK m neg a (initK m a)

/-- With the default knobs a pass is the model's pass. -/
theorem stepK_default : stepK {} = step := by
  funext neg s
  cases neg <;> rfl

/-- With the default knobs the loop is the model's loop. -/
theorem loopK_default (neg : Bool) : ∀ fuel s, loopK {} neg fuel s = loop neg fuel s
  | 0, _ => rfl
  | fuel + 1, s => by
    simp only [loopK, loop, stepK_default, loopK_default neg fuel]

/-- With the default knobs the copy is the model. -/
theorem execK_default : execK {} = exec := by
  funext a neg
  exact loopK_default neg a (init a)

/-! ## Mutant 1: width 5 -/

/-- `k & 0x1F`, `low >= 16`, `low - 32`. -/
def width5 : Knobs := { mask := 0x1F, half := 16, full := 32 }

/-- W3 fails: the lowest digit of `15` is `15`, not a width-4 wNAF digit. -/
theorem width5_breaks_W3 : ¬ W3Of (execK width5) := by
  intro h
  have := (h 15 false (by norm_num) 0).1
  revert this
  unfold IsWnafDigit
  decide +kernel

/-! ## Mutant 2: off-by-one on `n` -/

/-- `let mut n = 1;`. -/
def offByOne : Knobs := { n0 := 1 }

/-- W4 fails: `1` is encoded as `2` (the digit lands one position up). -/
theorem offByOne_breaks_W4 : ¬ W4Of (execK offByOne) := by
  intro h
  have := (h 1 false (by norm_num)).1
  revert this
  decide +kernel

/-- W1 fails too: `2^127 - 1` writes `digits[128]`. -/
theorem offByOne_breaks_W1 : ¬ W1Of (execK offByOne) := by
  intro h
  have := (h (2 ^ 127 - 1) false (by norm_num)).2.1
  revert this
  decide +kernel

/-- And W2: `2^127 - 1` gets 129 digits. -/
theorem offByOne_breaks_W2 : ¬ W2Of (execK offByOne) := by
  intro h
  have := h.2 (2 ^ 127 - 1) false (by norm_num)
  revert this
  decide +kernel

/-! ## Mutant 3: a dropped carry -/

/-- `k += (-d) as u128;` deleted. -/
def noCarry : Knobs := { carry := false }

/-- W4 fails: `15` is encoded as `13` (digits `-1` and `7`). -/
theorem noCarry_breaks_W4 : ¬ W4Of (execK noCarry) := by
  intro h
  have := (h 15 false (by norm_num)).1
  revert this
  decide +kernel

/-! ## Mutant 4: a sign flip -/

/-- `if negate { d } else { -d }`. -/
def signFlip : Knobs := { flip := true }

/-- W4 fails: `1` with `negate = false` is encoded as `-1`. -/
theorem signFlip_breaks_W4 : ¬ W4Of (execK signFlip) := by
  intro h
  have := (h 1 false (by norm_num)).1
  revert this
  decide +kernel

/-! ## Mutants 5 and 6: the checks -/

/-- The overflow check on the wrapped value: `overU128 (wrapU128 x)`. -/
def flagAfterWrap : Knobs := { flagAfterWrap := true }

/-- W6 fails: on `2^128 - 1`, `k += 1` overflows, but the mutant does not see it. -/
theorem flagAfterWrap_breaks_W6 : ¬ W6Of (execK flagAfterWrap) := by
  intro h
  have := (h (2 ^ 128 - 1) false (by norm_num)).2.2.mpr (Or.inr (Or.inr (Or.inr rfl)))
  revert this
  decide +kernel

/-- The assertion removed. -/
def noAssert : Knobs := { noAssert := true }

/-- W6 fails: the assertion must fail on `2^127`. -/
theorem noAssert_breaks_W6 : ¬ W6Of (execK noAssert) := by
  intro h
  have := (h (2 ^ 127) false (by norm_num)).1.mpr le_rfl
  revert this
  decide +kernel

/-! ## Mutant 7: `min` for `max` in `Decomposed::new` -/

/-- `len: len1.min(len2)`. -/
def ofHalvesMin (h1 h2 : Bool × ℕ) : Option Decomposed :=
  let s1 := Wnaf.exec h1.2 h1.1
  let s2 := Wnaf.exec h2.2 h2.1
  if s1.panics || s2.panics then none
  else some ⟨s1.digits, s2.digits, min s1.n s2.n⟩

/-- D fails: the halves `1` and `16` have 1 and 5 digits, so `len` must be 5. -/
theorem min_breaks_D : ¬ DOf ofHalvesMin := by
  intro h
  obtain ⟨D, hD, -, -, hlen, -⟩ := h false false 1 16 (by norm_num) (by norm_num)
  have h1 : (ofHalvesMin (false, 1) (false, 16)).map Decomposed.len = some D.len := by
    rw [hD]; rfl
  have h2 : (ofHalvesMin (false, 1) (false, 16)).map Decomposed.len = some 1 := by
    decide +kernel
  have h3 : max (Wnaf.run 1 false).2 (Wnaf.run 16 false).2 = 5 := by decide +kernel
  rw [h2, Option.some_inj] at h1
  omega

/-! ## Mutant 8: a table read one entry off -/

variable {P A : Type}

/-- `t2: w[3..7]` for `w[4..8]` in `from_window`. -/
def ofWindowOff (w : List A) : Option (Table A) :=
  if h : 8 ≤ w.length then
    some ⟨fun j => w[j.val]'(by omega), fun j => w[j.val + 3]'(by omega)⟩
  else none

/-- `Table::new` over the mutant `from_window`. -/
def newOff (O : CurveOps P A) (p : P) : Option (Table A) :=
  let proj := windowProj O p
  let affine := O.batchNormalize proj (List.replicate 8 O.identityA)
  ofWindowOff affine

/-- `Table::batch` over the mutant `from_window`. -/
def batchOff (O : CurveOps P A) (points : List P) : Option (List (Table A)) :=
  let n := points.length
  if n = 0 then some []
  else
    let proj := points.flatMap (windowProj O)
    let affine := O.batchNormalize proj (List.replicate (n * 8) O.identityA)
    (chunksExact8 affine).mapM ofWindowOff

/-- The integers as their own curve, with `λ = 1000`. -/
def OZ : CurveOps ℤ ℤ where
  identity := 0
  double x := 2 • x
  addMixed x a := x + a
  negA a := -a
  isIdentity x := decide (x = 0)
  add x y := x + y
  endo x := 1000 • x
  identityA := 0
  batchNormalize ps _ := ps
  toCurve a := a

/-- Every integer valid, standing for itself. -/
def VZ : CurveAbs ℤ ℤ ℤ where
  valid _ := True
  validA _ := True
  α x := x
  αA x := x

/-- `OZ` meets `CurveOps.Spec` under `VZ`. -/
theorem OZ_spec : CurveOps.Spec OZ VZ where
  identity := ⟨trivial, rfl⟩
  isIdentity := fun _ _ h => of_decide_eq_true h
  double := fun _ _ => ⟨trivial, rfl⟩
  add := fun _ _ _ _ => ⟨trivial, rfl⟩
  addMixed := fun _ _ _ _ => ⟨trivial, rfl⟩
  negA := fun _ _ => ⟨trivial, rfl⟩
  batchNormalize := fun _ _ _ _ => List.forall₂_same.mpr fun _ _ => ⟨trivial, rfl⟩
  toCurve := fun _ _ => ⟨trivial, rfl⟩

/-- `OZ`'s endomorphism is multiplication by `1000`. -/
theorem OZ_endo : EndoSpec OZ VZ 1000 := fun _ _ => ⟨trivial, rfl⟩

/-- L2 fails: `t2[0]` of the point `1` must stand for `λ·1 = 1000`, but the mutant reads `7`. -/
theorem off_breaks_L2 :
    ¬ L2Of (fun O p => windowProj O p) (fun O p => newOff O p) (fun O ps => batchOff O ps) := by
  intro h
  obtain ⟨-, h2, -⟩ := h OZ VZ 1000 OZ_spec OZ_endo
  obtain ⟨t, ht, htab⟩ := h2 1 trivial
  have h7 : (newOff OZ 1).map (fun t => t.t2 0) = some 7 := by decide +kernel
  have h1000 : oddMultiples (1000 • VZ.α 1) 0 = 1000 := by decide +kernel
  have ht' : newOff OZ 1 = some t := ht
  rw [ht'] at h7
  have h7' : t.t2 0 = 7 := Option.some.inj h7
  have := (htab 0).2.2.2
  rw [h1000] at this
  exact absurd (h7'.symm.trans this) (by decide)

/-! ## Mutant 9: the second half added from the first table -/

/-- `Self::add_digit(&mut acc, &self.t1, k.digits2[i]);` -/
def ladderLoopSwap (O : LadderOps P A) (t : Table A) (D : Decomposed) : ℕ → P → Option P
  | 0, acc => some acc
  | i + 1, acc => do
    let acc := if i + 1 < D.len then O.double acc else acc
    let d1 ← digitAt D.digits1 i
    let acc ← addDigit O acc t.t1 d1
    let d2 ← digitAt D.digits2 i
    let acc ← addDigit O acc t.t1 d2
    ladderLoopSwap O t D i acc

/-- `mul_decomposed` over `ladderLoopSwap`. -/
def mulDecSwap (O : LadderOps P A) (t : Table A) (D : Decomposed) : Option P :=
  ladderLoopSwap O t D D.len O.identity

/-- One digit `1` at position 0 of the second half, `len = 1`. -/
def oneDigit2 : Decomposed := ⟨fun _ => 0, fun i => if i = 0 then 1 else 0, 1⟩

/-- L1 fails: over the integers with `p = 1`, `q = 0`, the second half's digit `1` gives `1`,
not `0`. -/
theorem swap_breaks_L1 : ¬ L1Of fun O t D => mulDecSwap O t D := by
  intro h
  have := @h ℤ _ 1 0 oneDigit2 (by unfold IsWnafDigit oneDigit2; decide +kernel)
    (by unfold IsWnafDigit oneDigit2; decide +kernel) (by decide +kernel)
    (by unfold oneDigit2; decide +kernel)
  revert this
  decide +kernel

/-! ## Mutant 10: the ladder's doubling -/

/-- The "extra first doubling": the skip `if i + 1 < k.len` removed, so the first pass doubles
too. -/
def ladderLoopNoSkip (O : LadderOps P A) (t : Table A) (D : Decomposed) : ℕ → P → Option P
  | 0, acc => some acc
  | i + 1, acc => do
    let acc := O.double acc
    let d1 ← digitAt D.digits1 i
    let acc ← addDigit O acc t.t1 d1
    let d2 ← digitAt D.digits2 i
    let acc ← addDigit O acc t.t2 d2
    ladderLoopNoSkip O t D i acc

/-- `mul_decomposed` over `ladderLoopNoSkip`. -/
def mulDecNoSkip (O : LadderOps P A) (t : Table A) (D : Decomposed) : Option P :=
  ladderLoopNoSkip O t D D.len O.identity

/-- Past the first pass the loop without the skip is the model's loop. -/
theorem noSkip_eq_aux (O : LadderOps P A) (t : Table A) (D : Decomposed) :
    ∀ i acc, i < D.len → ladderLoopNoSkip O t D i acc = ladderLoop O t D i acc
  | 0, _, _ => rfl
  | i + 1, acc, h => by
    have ih : ∀ acc, ladderLoopNoSkip O t D i acc = ladderLoop O t D i acc :=
      fun acc => noSkip_eq_aux O t D i acc (by omega)
    simp only [ladderLoopNoSkip, ladderLoop, if_pos h, ih]

/-- The extra first doubling is an equivalent mutant: in every group it computes what the model
computes, because the extra doubling doubles the identity. -/
theorem noSkip_eq (G : Type) [AddCommGroup G] (t : Table G) (D : Decomposed) :
    mulDecNoSkip (groupOps G) t D = Table.mulDecomposed (groupOps G) t D := by
  unfold mulDecNoSkip Table.mulDecomposed
  rcases h : D.len with _ | m
  · rfl
  · have h1 : ¬ (m + 1 < D.len) := by omega
    have ih : ∀ acc, ladderLoopNoSkip (groupOps G) t D m acc = ladderLoop (groupOps G) t D m acc :=
      fun acc => noSkip_eq_aux _ t D m acc (by omega)
    simp only [ladderLoopNoSkip, ladderLoop, if_neg h1, ih]
    simp only [groupOps, smul_zero]

/-- The doubling moved after the additions: one doubling too many. -/
def ladderLoopLate (O : LadderOps P A) (t : Table A) (D : Decomposed) : ℕ → P → Option P
  | 0, acc => some acc
  | i + 1, acc => do
    let d1 ← digitAt D.digits1 i
    let acc ← addDigit O acc t.t1 d1
    let d2 ← digitAt D.digits2 i
    let acc ← addDigit O acc t.t2 d2
    let acc := O.double acc
    ladderLoopLate O t D i acc

/-- `mul_decomposed` over `ladderLoopLate`. -/
def mulDecLate (O : LadderOps P A) (t : Table A) (D : Decomposed) : Option P :=
  ladderLoopLate O t D D.len O.identity

/-- One digit `1` at position 0, `len = 1`. -/
def oneDigit : Decomposed := ⟨fun i => if i = 0 then 1 else 0, fun _ => 0, 1⟩

/-- L1 fails: over the integers with `p = 1`, `q = 0`, the digit string `1` gives `2`, not `1`. -/
theorem late_breaks_L1 : ¬ L1Of fun O t D => mulDecLate O t D := by
  intro h
  have := @h ℤ _ 1 0 oneDigit (by unfold IsWnafDigit oneDigit; decide +kernel)
    (by unfold IsWnafDigit oneDigit; decide +kernel) (by decide +kernel)
    (by unfold oneDigit; decide +kernel)
  revert this
  decide +kernel

end Mutation

/-! ## The counterexamples, printed -/

open Mutation in
#eval
  let digitsOf (s : State) := ((List.finRange 128).take 8).map s.digits
  [ s!"model    15: n={(exec 15 false).n} digits[0..8]={digitsOf (exec 15 false)}",
    s!"width5   15: n={(execK width5 15 false).n} digits[0..8]={digitsOf (execK width5 15 false)}",
    s!"model     1: n={(exec 1 false).n} digits[0..8]={digitsOf (exec 1 false)}",
    s!"offByOne  1: n={(execK offByOne 1 false).n} digits[0..8]={digitsOf (execK offByOne 1 false)}",
    s!"offByOne 2^127-1: n={(execK offByOne (2 ^ 127 - 1) false).n} outOfBounds={(execK offByOne (2 ^ 127 - 1) false).outOfBounds}",
    s!"noCarry  15: n={(execK noCarry 15 false).n} digits[0..8]={digitsOf (execK noCarry 15 false)}",
    s!"signFlip  1: n={(execK signFlip 1 false).n} digits[0..8]={digitsOf (execK signFlip 1 false)}",
    s!"ladder  model: {Table.mulDecomposed (groupOps ℤ) ⟨oddMultiples 1, oddMultiples 0⟩ oneDigit}",
    s!"ladder   late: {mulDecLate (groupOps ℤ) ⟨oddMultiples 1, oddMultiples 0⟩ oneDigit}",
    s!"ladder noSkip: {mulDecNoSkip (groupOps ℤ) ⟨oddMultiples 1, oddMultiples 0⟩ oneDigit}",
    s!"ladder   swap: {mulDecSwap (groupOps ℤ) ⟨oddMultiples 1, oddMultiples 0⟩ oneDigit2} (model {Table.mulDecomposed (groupOps ℤ) ⟨oddMultiples 1, oddMultiples 0⟩ oneDigit2})",
    s!"model    2^128-1: u128Overflow={(exec (2 ^ 128 - 1) false).u128Overflow}",
    s!"flagAfterWrap 2^128-1: u128Overflow={(execK flagAfterWrap (2 ^ 128 - 1) false).u128Overflow}",
    s!"model    2^127: assertFailed={(exec (2 ^ 127) false).assertFailed}",
    s!"noAssert 2^127: assertFailed={(execK noAssert (2 ^ 127) false).assertFailed}",
    s!"D len of halves 1, 16: model {(Decomposed.ofHalves (false, 1) (false, 16)).map Decomposed.len}, min {(ofHalvesMin (false, 1) (false, 16)).map Decomposed.len}",
    s!"t2[0] of the point 1 (λ = 1000): model {(Table.new OZ 1).map (fun t => t.t2 0)}, off {(newOff OZ 1).map (fun t => t.t2 0)}" ]

#print axioms Mutation.execK_default
#print axioms Mutation.width5_breaks_W3
#print axioms Mutation.offByOne_breaks_W4
#print axioms Mutation.offByOne_breaks_W1
#print axioms Mutation.offByOne_breaks_W2
#print axioms Mutation.noCarry_breaks_W4
#print axioms Mutation.signFlip_breaks_W4
#print axioms Mutation.flagAfterWrap_breaks_W6
#print axioms Mutation.noAssert_breaks_W6
#print axioms Mutation.min_breaks_D
#print axioms Mutation.off_breaks_L2
#print axioms Mutation.swap_breaks_L1
#print axioms Mutation.noSkip_eq
#print axioms Mutation.late_breaks_L1
