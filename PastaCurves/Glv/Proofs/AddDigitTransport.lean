import PastaCurves.Glv.Blueprint

/-! # One `add_digit` over the curve follows `add_digit` over the group -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- One `add_digit` over the curve follows `add_digit` over the group under `α`, through valid
points. -/
theorem addDigit_transport : Blueprint.addDigit_transport_stmt := by
  intro P A G _ O V hO acc tab d hacc htab
  unfold addDigit
  split
  · split
    · rename_i _ hlt
      have hv := htab ⟨d.natAbs / 2, hlt⟩
      split
      · have hn := hO.negA _ hv
        have hm := hO.addMixed _ _ hacc hn.1
        exact ⟨by simp [groupOps, hm.2, hn.2], by intro r hr; simp at hr; rw [← hr]; exact hm.1⟩
      · have hm := hO.addMixed _ _ hacc hv
        exact ⟨by simp [groupOps, hm.2], by intro r hr; simp at hr; rw [← hr]; exact hm.1⟩
    · simp
  · exact ⟨by simp, by intro r hr; simp at hr; rw [← hr]; exact hacc⟩

end PastaCurves.Glv.Proofs
