import PastaCurves.Glv.Blueprint

/-! # `add_digit` in a group -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- `add_digit` in a group, over the odd multiples of `p`, adds `d·p`. -/
theorem addDigit_group : Blueprint.addDigit_group_stmt := by
  intro G _ acc p d hd
  rcases hd with rfl | ⟨hodd, h1, h2⟩
  · simp [addDigit]
  · rw [Int.odd_iff] at hodd
    have cases : d = -7 ∨ d = -5 ∨ d = -3 ∨ d = -1 ∨ d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 7 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [addDigit, groupOps, oddMultiples] <;> abel

end PastaCurves.Glv.Proofs
