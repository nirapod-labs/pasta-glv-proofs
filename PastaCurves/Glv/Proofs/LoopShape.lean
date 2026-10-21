import PastaCurves.Glv.Blueprint

/-! # The loop of `wnaf_digits` keeps every digit a width-4 wNAF digit -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- The loop keeps every digit a width-4 wNAF digit. -/
theorem loop_shape : Blueprint.loop_shape_stmt := by
  intro hd neg fuel
  induction fuel with
  | zero => intro s h; simpa [Wnaf.loop] using h
  | succ f ih =>
    intro s h
    simp only [Wnaf.loop]
    split
    · exact h
    · apply ih
      intro i
      rw [hd]
      split
      · have hw : IsWnafDigit (wdigit s.k) ∧ IsWnafDigit (-wdigit s.k) := by
          unfold IsWnafDigit; simp only [Int.odd_iff]
          unfold wdigit; split_ifs <;> omega
        split
        · exact hw.2
        · exact hw.1
      · exact h i

end PastaCurves.Glv.Proofs
