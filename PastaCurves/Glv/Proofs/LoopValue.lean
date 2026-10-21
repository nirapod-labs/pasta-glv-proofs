import PastaCurves.Glv.Blueprint

/-! # The loop of `wnaf_digits` keeps the value invariant -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- The loop keeps the value invariant. -/
theorem loop_value : Blueprint.loop_value_stmt := by
  intro hsp hk hn hd hsv a neg fuel
  induction fuel with
  | zero => intro s h; simpa [Wnaf.loop] using h
  | succ f ih =>
    intro s h
    simp only [Wnaf.loop]
    split
    · exact h
    · rename_i h0; exact ih _ (hsv hsp hk hn hd a neg s h0 h)

end PastaCurves.Glv.Proofs
