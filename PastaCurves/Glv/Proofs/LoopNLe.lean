import PastaCurves.Glv.BlueprintA

/-! # The model's loop never lowers `n` -/

namespace PastaCurves.Glv.Proofs

/-- Each pass adds one to `n`, so the loop never lowers it. -/
theorem loop_n_le : BlueprintA.loop_n_le_stmt := by
  intro hn neg fuel
  induction fuel with
  | zero => intro s; simp [Wnaf.loop]
  | succ f ih =>
    intro s
    simp only [Wnaf.loop]
    split
    · exact le_rfl
    · have h := ih (Wnaf.step neg s)
      rw [hn] at h
      omega

end PastaCurves.Glv.Proofs
