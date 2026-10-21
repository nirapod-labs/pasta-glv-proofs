import PastaCurves.Glv.Blueprint

/-! # The passes from an odd `k`: one, or four down to `kq k` -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- From an odd `k` below `2^128`, either the next pass reaches `0`, or `k = 16 q + d` with
`q = kq k ≥ 1`, and four passes reach `q`. -/
theorem passes_odd : Blueprint.passes_odd_stmt := by
  intro k hk hodd
  have hp : (2 : ℤ) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
  have hk0 : k ≠ 0 := by omega
  have hnext : knext k = wrapU128 ((k : ℤ) - wdigit k) / 2 := by simp [knext, hodd]
  by_cases hq : kq k = 0
  · left
    refine ⟨hq, ?_⟩
    have : knext k = 0 := by
      rw [hnext]; unfold kq at hq; unfold wrapU128 wdigit at *; split_ifs at * <;> omega
    rw [passes_of_ne k hk0, this, passes_zero]
  · right
    have hval : (k : ℤ) = 16 * kq k + wdigit k := by
      unfold kq at *; unfold wrapU128 wdigit at *; split_ifs at * <;> omega
    have h8 : knext k = 8 * kq k := by
      rw [hnext]; unfold kq at *; unfold wrapU128 wdigit at *; split_ifs at * <;> omega
    have hev : ∀ x, x ≠ 0 → knext (2 * x) = x := by
      intro x hx; simp only [knext]; split_ifs <;> omega
    refine ⟨hq, hval, ?_⟩
    rw [passes_of_ne k hk0, h8, show 8 * kq k = 2 * (4 * kq k) by ring,
      passes_of_ne _ (by omega), hev _ (by omega), show 4 * kq k = 2 * (2 * kq k) by ring,
      passes_of_ne _ (by omega), hev _ (by omega), passes_of_ne _ (by omega), hev _ hq]

end PastaCurves.Glv.Proofs
