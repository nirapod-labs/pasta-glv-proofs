import PastaCurves.Glv.Blueprint

/-! # L2's first part: the window of a valid point -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- The window of a valid point has eight entries: the odd multiples `p, 3p, 5p, 7p`, valid, and
their images under the endomorphism. -/
theorem window : Blueprint.window_stmt := by
  intro P A G _ O V lam hO hE p hp
  have hd := hO.double p hp
  have h1 := hO.add p (O.double p) hp hd.1
  have h2 := hO.add _ (O.double p) h1.1 hd.1
  have h3 := hO.add _ (O.double p) h2.1 hd.1
  refine ⟨rfl, fun j => ?_⟩
  fin_cases j
  · exact ⟨p, rfl, hp, by simp [oddMultiples], rfl⟩
  · refine ⟨_, rfl, h1.1, ?_, rfl⟩
    rw [h1.2, hd.2]; simp [oddMultiples]; abel
  · refine ⟨_, rfl, h2.1, ?_, rfl⟩
    rw [h2.2, h1.2, hd.2]; simp [oddMultiples]; abel
  · refine ⟨_, rfl, h3.1, ?_, rfl⟩
    rw [h3.2, h2.2, h1.2, hd.2]; simp [oddMultiples]; abel

end PastaCurves.Glv.Proofs
