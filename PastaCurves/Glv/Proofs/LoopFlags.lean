import PastaCurves.Glv.Blueprint

/-! # What the loop of `wnaf_digits` does to the assertion, `i8` and `u128` flags -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- The loop leaves the assertion and `i8` flags alone, and sets the `u128` flag from no `k`
below `2^128 - 16`. -/
theorem loop_flags : Blueprint.loop_flags_stmt := by
  intro hk hf neg fuel
  induction fuel with
  | zero => intro s; simp [Wnaf.loop]
  | succ f ih =>
    intro s
    simp only [Wnaf.loop]
    split
    · exact ⟨rfl, rfl, fun _ => rfl⟩
    · rename_i h0
      obtain ⟨ha, hi, hu⟩ := ih (Wnaf.step neg s)
      obtain ⟨fa, fi, fu, -⟩ := hf neg s
      refine ⟨by rw [ha, fa], by rw [hi, fi], fun hlt => ?_⟩
      have hl := knext_lt s.k h0
      rw [hu (by rw [hk]; omega), fu]
      have : -8 ≤ wdigit s.k := by unfold wdigit; split_ifs <;> omega
      have hp : (2 : ℤ) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
      have : ¬ ((2 : ℤ) ^ 128 ≤ (s.k : ℤ) - wdigit s.k) := by
        rw [hp]; omega
      rw [hp] at this
      simp; intro _ h; omega

end PastaCurves.Glv.Proofs
