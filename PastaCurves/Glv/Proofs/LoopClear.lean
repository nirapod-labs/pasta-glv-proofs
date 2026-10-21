import PastaCurves.Glv.BlueprintA

/-! # The model's flags are sticky along the loop -/

namespace PastaCurves.Glv.Proofs

/-- A pass keeps every flag that is set, so a state from which the loop ends with no flag set has
none set itself. -/
theorem loop_clear : BlueprintA.loop_clear_stmt := by
  intro hf neg fuel
  induction fuel with
  | zero => intro s h; simpa [Wnaf.loop] using h
  | succ f ih =>
    intro s h
    simp only [Wnaf.loop] at h
    split at h
    · exact h
    · have h2 := ih (Wnaf.step neg s) h
      obtain ⟨ha, hi, hu, ho⟩ := hf neg s
      simp only [Wnaf.State.panicsIn, Bool.true_and, Bool.or_eq_false_iff] at h2 ⊢
      rw [ha, hi, hu, ho] at h2
      simp only [Bool.or_eq_false_iff] at h2
      tauto

end PastaCurves.Glv.Proofs
