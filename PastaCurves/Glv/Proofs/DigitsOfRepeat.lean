import PastaCurves.Glv.BlueprintA

/-! # The initial digit array -/

namespace PastaCurves.Glv.Proofs

open Aeneas Aeneas.Std

/-- `[0i8; 128]` reads as the model's initial digits, all zero. -/
theorem digitsOf_repeat : BlueprintA.digitsOf_repeat_stmt := by
  funext i
  simp only [digitsOf, Array.repeat_val]
  rw [List.getD_replicate _ (by simp)]
  rfl

end PastaCurves.Glv.Proofs
