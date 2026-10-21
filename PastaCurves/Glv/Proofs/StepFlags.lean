import PastaCurves.Glv.Blueprint

/-! # What a pass of `wnaf_digits` does to the panic flags -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- The digit of an odd `k` lies in `[-7, 7]`, and `k - d` is not negative. -/
private theorem wdigit_bounds (k : ℕ) (h : k % 2 = 1) :
    -7 ≤ wdigit k ∧ wdigit k ≤ 7 ∧ 0 ≤ (k : ℤ) - wdigit k := by
  unfold wdigit; split_ifs <;> omega

/-- A pass leaves the assertion and `i8` flags alone; it sets the `u128` flag exactly when `k` is
odd and `k - d` reaches `2^128`, and the bounds flag exactly when `k` is odd and `n ≥ 128`. -/
theorem step_flags : Blueprint.step_flags_stmt := by
  intro neg s
  have h1 : s.k &&& 1 = s.k % 2 := Nat.and_one_is_mod s.k
  have h15 : s.k &&& 0xF = s.k % 16 := Nat.and_two_pow_sub_one_eq_mod s.k 4
  simp only [Wnaf.step, h1]
  split
  · rename_i hodd
    have hlow : wrapI8 ((s.k &&& 0xF : ℕ) : ℤ) = ((s.k % 16 : ℕ) : ℤ) := by
      rw [h15]; unfold wrapI8; omega
    have hd : (if 8 ≤ ((s.k % 16 : ℕ) : ℤ) then wrapI8 (((s.k % 16 : ℕ) : ℤ) - 16)
        else ((s.k % 16 : ℕ) : ℤ)) = wdigit s.k := by
      unfold wdigit wrapI8; split_ifs <;> omega
    obtain ⟨hb1, hb2, hb3⟩ := wdigit_bounds s.k hodd
    have e1 : overI8 (((s.k % 16 : ℕ) : ℤ) - 16) = false := by unfold overI8; simp; omega
    have e2 : overI8 (-wdigit s.k) = false := by unfold overI8; simp; omega
    have hx : ∀ s' : Wnaf.State, s'.k = s.k →
        (if 0 ≤ wdigit s.k then (s'.k : ℤ) - wrapU128 (wdigit s.k)
          else (s'.k : ℤ) + wrapU128 (wrapI8 (-wdigit s.k))) = (s.k : ℤ) - wdigit s.k := by
      intro s' hs; rw [hs]; unfold wrapU128 wrapI8; split_ifs <;> omega
    have ho : overU128 ((s.k : ℤ) - wdigit s.k) = decide (2 ^ 128 ≤ (s.k : ℤ) - wdigit s.k) := by
      unfold overU128; simp; omega
    simp only [Wnaf.emit, hlow, hd, e1, e2, Bool.and_false, Bool.or_false,
      hx _ (Wnaf.write_k _ _), ho, hodd, decide_true, Bool.true_and]
    unfold Wnaf.write
    split <;> simp <;> omega
  · rename_i hev
    have : ¬ (s.k % 2 = 1) := hev
    simp [this]

end PastaCurves.Glv.Proofs
