import PastaCurves.Glv.Blueprint

/-! # The loop of `wnaf_digits` writes nothing out of bounds when its passes end by 128 -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- The loop writes nothing out of bounds when its passes end by position 128. -/
theorem loop_oob : Blueprint.loop_oob_stmt := by
  intro hk hn hf neg fuel
  induction fuel with
  | zero => intro s _ _; simp [Wnaf.loop]
  | succ f ih =>
    intro s hle hp
    simp only [Wnaf.loop]
    split
    · rfl
    · rename_i h0
      have hl := knext_lt s.k h0
      have hps := passes_of_ne s.k h0
      rw [ih (Wnaf.step neg s) (by rw [hk]; omega) (by rw [hn, hk]; omega), (hf neg s).2.2.2]
      have : ¬ (128 ≤ s.n) := by omega
      simp [this]

end PastaCurves.Glv.Proofs
