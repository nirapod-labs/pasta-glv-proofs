import PastaCurves.Glv.Blueprint

/-! # The lower bound `15 · gmin m ≥ 2^(m+2) + 7` -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- `15 · gmin m ≥ 2^(m+2) + 7` for every `m ≥ 1`, by strong induction on the recurrence. -/
theorem gmin_lower : Blueprint.gmin_lower_stmt := by
  intro hrec m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases h4 : m ≤ 4
    · obtain rfl | rfl | rfl | rfl : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
      all_goals decide
    · rw [hrec m (by omega)]
      have a := ih (m - 1) (by omega) (by omega)
      have b := ih (m - 4) (by omega) (by omega)
      have e1 : 2 ^ (m - 1 + 2) = 2 * 2 ^ (m - 2) * 4 := by
        rw [show m - 1 + 2 = (m - 2) + 1 + 2 by omega]; ring
      have e2 : 2 ^ (m - 4 + 2) = 2 ^ (m - 2) := by
        rw [show m - 4 + 2 = m - 2 by omega]
      have e3 : 2 ^ (m + 2) = 2 ^ (m - 2) * 16 := by
        rw [show m + 2 = (m - 2) + 4 by omega, pow_add]; norm_num
      rw [e1] at a; rw [e2] at b; rw [e3]
      omega

end PastaCurves.Glv.Proofs
