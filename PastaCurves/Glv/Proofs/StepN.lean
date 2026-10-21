import PastaCurves.Glv.Blueprint

/-! # A pass of `wnaf_digits` adds one to `n` -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- A pass adds one to `n`. -/
theorem step_n : Blueprint.step_n_stmt := by
  intro neg s
  unfold Wnaf.step
  split <;> simp [Wnaf.emit]

end PastaCurves.Glv.Proofs
