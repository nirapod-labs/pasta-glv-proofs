import PastaCurves.Glv.Spec

/-!
# C's hypotheses can all hold, and H2 means the usual triple

C is an implication, so hypotheses that contradict each other would make it true for nothing.
`hyps_ok` builds one instance that meets H0 to H3 at once with an injective abstraction (`α` is the
identity on `ZMod 2^100`, a scalar is a `u128` split into its 64-bit halves, `λ = 2^64`). On it C
pins `mul_glv`'s result to `k·p` (`C_consequence`) and C-batch pins every output of
`batch_mul_same_scalar_vartime` (`CBatch_consequence`), and the model computes exactly those
results on a scalar whose halves are both nonzero (checked by the kernel).

`DecomposeSpec_iff_triple`: H2 is written with `f k = .ok r`, as pasta's `Portable.Succeeds`
writes success, so its meaning does not depend on how Aeneas defines its triples. At the Aeneas
version pasta pins, it says exactly what the triple `f k ⦃ r => ... ⦄` says.
-/

open PastaCurves.Glv Aeneas Aeneas.Std Aeneas.Std.WP

namespace NonVacuity

/-- The order of the instance's group. -/
abbrev nT : ℕ := 2 ^ 100
/-- The instance's group. -/
abbrev GT := ZMod nT
/-- The instance's `λ`. -/
abbrev lamT : ℕ := 2 ^ 64

/-- The group as its own curve: every primitive is the group operation. (`endo` multiplies, since
the kernel would compute `2^64 • x` as `2^64` additions.) -/
def OT : CurveOps GT GT where
  identity := 0
  double x := 2 • x
  addMixed x a := x + a
  negA a := -a
  isIdentity x := decide (x = 0)
  add x y := x + y
  endo x := (lamT : GT) * x
  identityA := 0
  batchNormalize ps _ := ps
  toCurve a := a

/-- Every point valid; `α` and `αA` the identity map, so injective. -/
def VT : CurveAbs GT GT GT where
  valid _ := True
  validA _ := True
  α x := x
  αA x := x

/-- A scalar is any `u128`, standing for its value. -/
def ST : ScalarAbs Std.U128 where
  valid _ := True
  val k := k.val

/-- The halves of `k` are its low and its high 64 bits: `k = k1 + k2 · 2^64`. -/
def fT : DecomposeFn Std.U128 := fun k =>
  Result.ok ((false, ⟨BitVec.ofNat 128 (k.val % 2 ^ 64)⟩),
    (false, ⟨BitVec.ofNat 128 (k.val / 2 ^ 64)⟩))

/-- H0 to H3 hold at once, with an injective `α`. -/
theorem hyps_ok :
    OrderSpec VT nT ∧ EndoSpec OT VT lamT ∧ DecomposeSpec nT lamT ST fT ∧
      CurveOps.Spec OT VT ∧ Function.Injective VT.α := by
  refine ⟨?_, ?_, ?_, ?_, fun _ _ h => h⟩
  · intro x _
    show nT • x = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  · intro x _
    refine ⟨trivial, ?_⟩
    show (lamT : GT) * x = lamT • x
    rw [nsmul_eq_mul]
  · intro k _
    have hk := k.hBounds
    refine ⟨_, rfl, ?_⟩
    simp only [decode, ST, UScalar.val, UScalarTy.numBits, BitVec.toNat_ofNat,
      Bool.false_eq_true, if_false] at hk ⊢
    refine ⟨by omega, by omega, ?_⟩
    have : ((k.bv.toNat % 2 ^ 64 % 2 ^ 128 : ℕ) : ℤ) +
        ((k.bv.toNat / 2 ^ 64 % 2 ^ 128 : ℕ) : ℤ) * ((2 ^ 64 : ℕ) : ℤ) = (k.bv.toNat : ℤ) := by
      omega
    rw [this]
  · exact {
      identity := ⟨trivial, rfl⟩
      isIdentity := fun _ _ h => of_decide_eq_true h
      double := fun _ _ => ⟨trivial, rfl⟩
      add := fun _ _ _ _ => ⟨trivial, rfl⟩
      addMixed := fun _ _ _ _ => ⟨trivial, rfl⟩
      negA := fun _ _ => ⟨trivial, rfl⟩
      batchNormalize := fun _ _ _ _ => List.forall₂_same.mpr fun _ _ => ⟨trivial, rfl⟩
      toCurve := fun _ _ => ⟨trivial, rfl⟩ }

/-- C is not vacuous: on this instance it fixes `mul_glv`'s result. -/
theorem C_consequence (hC : C_stmt) (k : Std.U128) :
    mulGlv OT fT (3 : GT) k = some (k.val • (3 : GT)) := by
  obtain ⟨-, h1, -, -⟩ :=
    hC OT VT ST nT lamT fT hyps_ok.1 hyps_ok.2.1 hyps_ok.2.2.1 hyps_ok.2.2.2.1 k trivial
  obtain ⟨r, hr, -, hα⟩ := h1 3 trivial
  rw [hr]
  exact congrArg some hα

/-- The model computes that result, on a scalar whose halves are both nonzero. -/
example : mulGlv OT fT (3 : GT) ⟨BitVec.ofNat 128 (0xdeadbeefcafef00d + 2 ^ 64 * 0xfeedface1)⟩ =
    some (((0xdeadbeefcafef00d + 2 ^ 64 * 0xfeedface1 : ℕ) : GT) * 3) := by
  decide +kernel

/-- C-batch is not vacuous: on this instance it fixes every output. -/
theorem CBatch_consequence (hC : CBatch_stmt) (k : Std.U128) :
    batchMulSameScalar OT fT [(1 : GT), 2] k [0, 0] = some [k.val • (1 : GT), k.val • 2] := by
  obtain ⟨rs, hrs, hF⟩ := hC OT VT ST nT lamT fT hyps_ok.1 hyps_ok.2.1 hyps_ok.2.2.1
    hyps_ok.2.2.2.1 k trivial [1, 2] [0, 0] (fun _ _ => trivial) rfl
  rw [hrs]
  obtain _ | ⟨⟨-, h1⟩, hF⟩ := hF
  obtain _ | ⟨⟨-, h2⟩, hF⟩ := hF
  obtain _ | _ := hF
  exact congrArg some (congrArg₂ List.cons h1 (congrArg₂ List.cons h2 rfl))

/-- The model computes those outputs. -/
example : batchMulSameScalar OT fT [(1 : GT), 2]
    ⟨BitVec.ofNat 128 (0xdeadbeefcafef00d + 2 ^ 64 * 0xfeedface1)⟩ [0, 0] =
    some [((0xdeadbeefcafef00d + 2 ^ 64 * 0xfeedface1 : ℕ) : GT) * 1,
      ((0xdeadbeefcafef00d + 2 ^ 64 * 0xfeedface1 : ℕ) : GT) * 2] := by
  decide +kernel

/-- H2 in the `.ok` form is the Aeneas triple, at the Aeneas version pasta pins. -/
theorem DecomposeSpec_iff_triple {Sc : Type} (n lam : ℕ) (S : ScalarAbs Sc)
    (f : DecomposeFn Sc) :
    DecomposeSpec n lam S f ↔ ∀ k, S.valid k → f k ⦃ r => r.1.2.val < 2 ^ 127 ∧
      r.2.2.val < 2 ^ 127 ∧ decode r.1 + decode r.2 * lam ≡ S.val k [ZMOD n] ⦄ :=
  forall_congr' fun k => imp_congr_right fun _ => (spec_equiv_exists (f k) _).symm

end NonVacuity

#print axioms NonVacuity.hyps_ok
#print axioms NonVacuity.C_consequence
#print axioms NonVacuity.CBatch_consequence
#print axioms NonVacuity.DecomposeSpec_iff_triple
