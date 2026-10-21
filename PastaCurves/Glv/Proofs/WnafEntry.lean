import PastaCurves.Glv.BlueprintA

/-! # The entry of `wnaf_digits`: the assertion, then the loop -/

namespace PastaCurves.Glv.Proofs

open Aeneas Aeneas.Std

/-- From `2^127` on the assertion fails; below it the loop starts from `[0; 128]`, `0` and `a`. -/
theorem wnaf_entry : BlueprintA.wnaf_entry_stmt := by
  intro a neg
  unfold pasta_curves.glv.wnaf_digits
  simp only [HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight]
  simp only [massert, UScalar.eq_equiv]
  simp
  split_ifs with h1 h2 h2
  · simp
  · unfold UScalar.val at h1
    rw [BitVec.toNat_ushiftRight, UScalar.bv_toNat, Nat.shiftRight_eq_div_pow] at h1
    omega
  · unfold UScalar.val at h1
    rw [BitVec.toNat_ushiftRight, UScalar.bv_toNat, Nat.shiftRight_eq_div_pow] at h1
    omega
  · simp

end PastaCurves.Glv.Proofs
