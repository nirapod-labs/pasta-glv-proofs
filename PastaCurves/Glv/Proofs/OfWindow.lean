import PastaCurves.Glv.Blueprint

/-! # Affine points that normalize the window of a valid point make its table -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- Affine points that normalize the window of a valid point, entry by entry, make its table. -/
theorem ofWindow : Blueprint.ofWindow_stmt := by
  intro P A G _ O V lam hO hE p hp c hc
  have hd := hO.double p hp
  have h1 := hO.add p (O.double p) hp hd.1
  have h2 := hO.add _ (O.double p) h1.1 hd.1
  have h3 := hO.add _ (O.double p) h2.1 hd.1
  simp only [windowProj] at hc
  obtain ⟨a0, c0, r0, hc0, rfl⟩ := List.forall₂_cons_left_iff.mp hc
  obtain ⟨a1, c1, r1, hc1, rfl⟩ := List.forall₂_cons_left_iff.mp hc0
  obtain ⟨a2, c2, r2, hc2, rfl⟩ := List.forall₂_cons_left_iff.mp hc1
  obtain ⟨a3, c3, r3, hc3, rfl⟩ := List.forall₂_cons_left_iff.mp hc2
  obtain ⟨a4, c4, r4, hc4, rfl⟩ := List.forall₂_cons_left_iff.mp hc3
  obtain ⟨a5, c5, r5, hc5, rfl⟩ := List.forall₂_cons_left_iff.mp hc4
  obtain ⟨a6, c6, r6, hc6, rfl⟩ := List.forall₂_cons_left_iff.mp hc5
  obtain ⟨a7, c7, r7, hc7, rfl⟩ := List.forall₂_cons_left_iff.mp hc6
  obtain rfl := List.forall₂_nil_left_iff.mp hc7
  refine ⟨_, rfl, fun j => ?_⟩
  have e0 := (hE p hp).2
  have e1 := (hE _ h1.1).2
  have e2 := (hE _ h2.1).2
  have e3 := (hE _ h3.1).2
  fin_cases j <;> simp [oddMultiples] at *
  · exact ⟨r0.1, r0.2, r4.1, by rw [r4.2, e0]⟩
  · refine ⟨r1.1, by rw [r1.2, h1.2, hd.2]; abel, r5.1, ?_⟩
    rw [r5.2, e1, h1.2, hd.2]; simp only [smul_add, smul_comm lam 2]; abel
  · refine ⟨r2.1, by rw [r2.2, h2.2, h1.2, hd.2]; abel, r6.1, ?_⟩
    rw [r6.2, e2, h2.2, h1.2, hd.2]; simp only [smul_add, smul_comm lam 2]; abel
  · refine ⟨r3.1, by rw [r3.2, h3.2, h2.2, h1.2, hd.2]; abel, r7.1, ?_⟩
    rw [r7.2, e3, h3.2, h2.2, h1.2, hd.2]; simp only [smul_add, smul_comm lam 2]; abel

end PastaCurves.Glv.Proofs
