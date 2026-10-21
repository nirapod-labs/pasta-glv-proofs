import PastaCurves.Glv.Blueprint

/-! # The key lemma: at least `m` passes need a magnitude of at least `gmin m` -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- A magnitude whose loop makes at least `m` passes is at least `gmin m`. -/
theorem kl : Blueprint.kl_stmt := by
  intro hrec hodd k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk m hm
    have g1 : gmin 1 = 1 := by decide
    have g4 : ∀ m, m ≤ 4 → gmin m ≤ 8 := by
      intro m h
      obtain rfl | rfl | rfl | rfl | rfl : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
      all_goals decide
    by_cases hk0 : k = 0
    · subst hk0; simp at hm; subst hm; decide
    by_cases hm0 : m = 0
    · subst hm0; simp [gmin]
    rcases Nat.mod_two_eq_zero_or_one k with he | ho
    · -- An even `k`: one pass halves it.
      have hn : knext k = k / 2 := by simp [knext, he]
      rw [passes_of_ne k hk0, hn] at hm
      by_cases hm1 : m = 1
      · subst hm1; rw [g1]; omega
      have h := ih (k / 2) (by omega) (by omega) (m - 1) (by omega)
      have hdbl : gmin m ≤ 2 * gmin (m - 1) := by
        by_cases h5 : 5 ≤ m
        · rw [hrec m h5]; exact min_le_left _ _
        · obtain rfl | rfl | rfl : m = 2 ∨ m = 3 ∨ m = 4 := by omega
          all_goals decide
      omega
    · rcases hodd k hk ho with ⟨hq, h1⟩ | ⟨hq, hv, hpq⟩
      · rw [h1] at hm
        have : m = 1 := by omega
        subst this; rw [g1]; omega
      · have hdb : -7 ≤ wdigit k := by unfold wdigit; split_ifs <;> omega
        by_cases h5 : 5 ≤ m
        · have h := ih (kq k) (by omega) (by omega) (m - 4) (by omega)
          rw [hrec m h5]
          have := min_le_right (2 * gmin (m - 1)) (16 * gmin (m - 4) - 7)
          omega
        · have := g4 m (by omega)
          omega

end PastaCurves.Glv.Proofs
