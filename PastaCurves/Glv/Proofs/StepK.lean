import PastaCurves.Glv.Blueprint

/-! # A pass of `wnaf_digits` takes `k` to `knext k` -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- A pass takes `k` to `knext k`. -/
theorem step_k : Blueprint.step_k_stmt := by
  intro neg s
  have h1 : s.k &&& 1 = s.k % 2 := Nat.and_one_is_mod s.k
  have h15 : s.k &&& 0xF = s.k % 16 := Nat.and_two_pow_sub_one_eq_mod s.k 4
  have hp : (2 : ℤ) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
  simp only [Wnaf.step, knext, wdigit, Nat.shiftRight_eq_div_pow, pow_one, h1]
  split
  · simp only [Wnaf.emit, Wnaf.write_k, wrapU128, wrapI8, h15, hp]
    split_ifs <;> omega
  · simp

end PastaCurves.Glv.Proofs
