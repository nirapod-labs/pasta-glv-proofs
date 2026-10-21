import PastaCurves.Glv.Blueprint

/-! # The sum over the positions below `j + 1` splits off position `j` -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- The positions below `j + 1` are those below `j`, and `j`. -/
theorem sum_below_succ : Blueprint.sum_below_succ_stmt := by
  intro f j hj
  have : ∀ i : Fin 128, (if (i : ℕ) < j + 1 then f i else 0) =
      (if (i : ℕ) < j then f i else 0) + (if i = ⟨j, hj⟩ then f i else 0) := by
    intro i
    by_cases h : (i : ℕ) = j
    · have : i = ⟨j, hj⟩ := Fin.ext h
      subst this; simp
    · have : i ≠ ⟨j, hj⟩ := fun e => h (by rw [e])
      simp only [this, if_false, add_zero]
      by_cases h' : (i : ℕ) < j
      · simp [h', show (i : ℕ) < j + 1 by omega]
      · simp [h', show ¬ (i : ℕ) < j + 1 by omega]
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib]
  simp

end PastaCurves.Glv.Proofs
