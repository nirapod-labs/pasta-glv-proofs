import PastaCurves.Glv.Blueprint

/-! # A pass of `wnaf_digits` writes one signed digit at position `n` -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- A pass on an odd `k` writes its signed digit at position `n`, and changes no other digit. -/
theorem step_digits : Blueprint.step_digits_stmt := by
  intro neg s i
  have h1 : s.k &&& 1 = s.k % 2 := Nat.and_one_is_mod s.k
  have h15 : s.k &&& 0xF = s.k % 16 := Nat.and_two_pow_sub_one_eq_mod s.k 4
  simp only [Wnaf.step, h1]
  split
  · rename_i hodd
    simp only [Wnaf.emit, Wnaf.write]
    split
    · simp only [Function.update_apply, Fin.ext_iff]
      by_cases hi : (i : ℕ) = s.n
      · simp only [hi, hodd, and_self, if_true, wdigit, wrapI8, h15]
        split_ifs <;> omega
      · simp [hi]
    · rename_i hn
      have : ¬ ((i : ℕ) = s.n) := by omega
      simp [this]
  · rename_i hev
    have : ¬ (s.k % 2 = 1) := hev
    simp [this]

end PastaCurves.Glv.Proofs
