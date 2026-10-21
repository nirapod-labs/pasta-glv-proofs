import PastaCurves.Glv.Blueprint

/-! # The loop of `wnaf_digits` adds `passes k` to `n` -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- The loop adds `passes k` to `n`. -/
theorem loop_n : Blueprint.loop_n_stmt := by
  intro hk hn neg fuel
  induction fuel with
  | zero => intro s h; simp [Wnaf.loop, show s.k = 0 by omega]
  | succ f ih =>
    intro s h
    simp only [Wnaf.loop]
    split
    · rename_i h0; simp [h0]
    · rename_i h0
      have hl := knext_lt s.k h0
      rw [ih (Wnaf.step neg s) (by rw [hk]; omega), hn, hk, passes_of_ne s.k h0]
      omega

end PastaCurves.Glv.Proofs
