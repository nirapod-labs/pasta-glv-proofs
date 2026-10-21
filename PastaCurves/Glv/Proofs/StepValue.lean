import PastaCurves.Glv.Blueprint

/-! # A pass of `wnaf_digits` from a nonzero `k` keeps the value invariant -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- A pass from a nonzero `k` keeps the value invariant. -/
theorem step_value : Blueprint.step_value_stmt := by
  intro hsp hk hn hd a neg s hk0 ⟨hlt, hpass, hzero, hsum⟩
  unfold step_digits_stmt at hd
  have hl := knext_lt s.k hk0
  have hps := passes_of_ne s.k hk0
  have hn128 : s.n < 128 := by omega
  refine ⟨by rw [hk]; omega, by rw [hn, hk]; omega, ?_, ?_⟩
  · intro i hi
    rw [hn] at hi
    rw [hd, if_neg (by omega)]
    exact hzero i (by omega)
  · rw [hn, hk]
    simp only [hd]
    rcases Nat.mod_two_eq_zero_or_one s.k with he | ho
    · have hkn : (s.k : ℤ) = 2 * (knext s.k : ℤ) := by
        have : knext s.k = s.k / 2 := by simp [knext, he]
        omega
      simp only [he, zero_ne_one, false_and, if_false]
      rw [← hsum, hkn, pow_succ]
      split <;> ring
    · have hp : (2 : ℤ) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
      have hkn : (s.k : ℤ) = 2 * (knext s.k : ℤ) + wdigit s.k := by
        simp only [knext, ho, if_true, wrapU128, hp]
        unfold wdigit; split_ifs <;> omega
      set m : Fin 128 := ⟨s.n, hn128⟩
      set x : ℤ := if neg then -wdigit s.k else wdigit s.k
      have hs := hsp s.digits
        (fun i => if s.k % 2 = 1 ∧ (i : ℕ) = s.n then x else s.digits i) m x
        (hzero m le_rfl) (if_pos ⟨ho, rfl⟩) (fun i hi => if_neg (fun hc => hi (Fin.ext hc.2)))
      rw [hs, ← hsum, hkn, pow_succ]
      simp only [x]
      split <;> ring

end PastaCurves.Glv.Proofs
