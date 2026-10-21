import PastaCurves.Glv.Blueprint

/-! # The recurrence of `gmin` -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- The window `gminW j` holds `gmin (j + 4), …, gmin (j + 1)`. -/
private theorem gminW_eq :
    ∀ j, gminW j = (gmin (j + 4), gmin (j + 3), gmin (j + 2), gmin (j + 1))
  | 0 => by decide
  | j + 1 => by
    have ih := gminW_eq j
    have e : gmin (j + 1 + 4) = (gminW (j + 1)).1 := by
      simp [gmin]
    rw [e]
    simp only [gminW, ih]

/-- The recurrence of `gmin`. -/
theorem gmin_rec : Blueprint.gmin_rec_stmt := by
  intro m hm
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 5 := ⟨m - 5, by omega⟩
  have h1 : gmin (j + 5) = (gminW (j + 1)).1 := by simp [gmin]
  rw [h1]
  simp only [gminW, gminW_eq j]
  simp

end PastaCurves.Glv.Proofs
