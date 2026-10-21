import PastaCurves.Glv.Blueprint

/-! # The window's validity -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- Every point of the window of a valid point is valid. -/
theorem windowValid : Blueprint.windowValid_stmt := by
  intro P A G _ O V lam hO hE p hp
  have hd := hO.double p hp
  have h1 := hO.add p (O.double p) hp hd.1
  have h2 := hO.add _ (O.double p) h1.1 hd.1
  have h3 := hO.add _ (O.double p) h2.1 hd.1
  intro q hq
  simp only [windowProj, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hp, h1.1, h2.1, h3.1, (hE _ hp).1, (hE _ h1.1).1, (hE _ h2.1).1, (hE _ h3.1).1]

end PastaCurves.Glv.Proofs
