import PastaCurves.Glv.BlueprintA

/-! # The loop's three readings of `k` -/

namespace PastaCurves.Glv.Proofs

open Aeneas Aeneas.Std

/-- `k != 0` holds exactly when `k ≠ 0`, `k & 1 == 1` exactly when `k` is odd, and
`(k & 0xF) as i8` is `k mod 16`. -/
theorem kbits : BlueprintA.kbits_stmt := by
  intro k
  refine ⟨?_, ?_, ?_⟩
  · rw [bne_iff_ne, ne_eq, ne_eq, not_iff_not]
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      exact UScalar.eq_of_val_eq (by rw [h]; rfl)
  · constructor
    · intro h
      have h2 := UScalar.val_eq_of_eq h
      simp [Nat.and_one_is_mod] at h2
      exact h2
    · intro h
      apply UScalar.eq_of_val_eq
      simp [Nat.and_one_is_mod, h]
  · have h15 : k.val &&& 15 = k.val % 16 := Nat.and_two_pow_sub_one_eq_mod k.val 4
    have hlt : k.val % 16 < 16 := Nat.mod_lt _ (by norm_num)
    rw [UScalar.hcast_val_eq, UScalar.val_and, UScalar.ofNatCore_val_eq, h15,
      IScalarTy.I8_numBits_eq, Int.bmod_def]
    split_ifs <;> omega

end PastaCurves.Glv.Proofs
