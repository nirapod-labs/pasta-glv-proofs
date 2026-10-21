import PastaCurves.Glv.BlueprintA

/-! # One unfolding of the translated loop -/

namespace PastaCurves.Glv.Proofs

open Aeneas Aeneas.Std

/-- A body that continues makes the loop go on from its new state; a body that is done makes the
loop return its value. -/
theorem loop_unfold : BlueprintA.loop_unfold_stmt := by
  intro neg digits n k
  constructor
  · intro neg' digits' n' k' h
    conv_lhs => unfold pasta_curves.glv.wnaf_digits_loop
    rw [Aeneas.Std.loop]
    simp only [h, bind_ok]
    rfl
  · intro v h
    unfold pasta_curves.glv.wnaf_digits_loop
    rw [Aeneas.Std.loop]
    simp only [h, bind_ok]

end PastaCurves.Glv.Proofs
