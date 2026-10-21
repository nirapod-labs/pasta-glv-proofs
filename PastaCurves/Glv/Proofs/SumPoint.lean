import PastaCurves.Glv.Blueprint

/-! # Writing a digit over a zero digit adds its weighted value to the digits' sum -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- Writing `x` over a zero digit at position `m` adds `x·2^m` to the digits' value. -/
theorem sum_point : Blueprint.sum_point_stmt := by
  intro f g m x hf hg hne
  have : ∀ i : Fin 128, g i * 2 ^ (i : ℕ) =
      f i * 2 ^ (i : ℕ) + (if m = i then x * 2 ^ (m : ℕ) else 0) := by
    intro i
    by_cases h : m = i
    · subst h; rw [hg, hf]; simp
    · rw [hne i (Ne.symm h), if_neg h, add_zero]
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

end PastaCurves.Glv.Proofs
