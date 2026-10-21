import PastaCurves.Glv.BlueprintA

/-! # The loop's body at `k = 0` -/

namespace PastaCurves.Glv.Proofs

open Aeneas Aeneas.Std

/-- At `k = 0` the body is done and returns `(digits, n)`. -/
theorem body_zero : BlueprintA.body_zero_stmt := by
  intro hb neg digits n k hk
  unfold pasta_curves.glv.wnaf_digits_loop.body
  rw [if_neg (fun h => (hb k).1.mp h hk)]

end PastaCurves.Glv.Proofs
