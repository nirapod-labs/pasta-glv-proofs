import PastaCurves.Glv.BlueprintA

/-! # The loop's body on an odd `k` -/

namespace PastaCurves.Glv.Proofs

open Aeneas Aeneas.Std Aeneas.Std.WP PastaCurves.Glv.Blueprint

/-- On an odd `k` with `n < 128` and `k - d < 2^128` the body writes the signed digit at `n` and
continues with `n + 1` and `knext k`. The proof splits on the three tests (`low >= 8`,
`negate`, `d >= 0`) and ends each feasible branch in arithmetic on `k mod 16`. -/
theorem body_odd : BlueprintA.body_odd_stmt := by
  intro hb neg digits n k hn hk hover
  have hk0 := (hb k).1.mpr (by omega)
  have h1 := (hb k).2.1.mpr hk
  have hlow := (hb k).2.2
  have hp : (2 : ℤ) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
  suffices H : pasta_curves.glv.wnaf_digits_loop.body neg digits n k ⦃ r =>
      ∃ (d : Std.I8) (n' : Std.Usize) (k' : Std.U128), r = .cont (neg, digits.set n d, n', k') ∧
      d.val = (if neg then -wdigit k.val else wdigit k.val) ∧
      n'.val = n.val + 1 ∧ k'.val = knext k.val ⦄ by
    obtain ⟨r, hr, d, n', k', rfl, h⟩ := WP.spec_imp_exists H
    exact ⟨d, n', k', hr, h⟩
  unfold pasta_curves.glv.wnaf_digits_loop.body
  rw [if_pos hk0]
  simp only [lift, bind_ok]
  rw [if_pos h1]
  step*
  all_goals (try split)
  all_goals (try step*)
  all_goals (try split)
  all_goals (try step*)
  all_goals (try split)
  all_goals (try step*)
  all_goals (try subst_vars)
  all_goals (try refine ⟨_, _, _, rfl, ?_, ?_, ?_⟩)
  all_goals (simp only [IScalar.hcast_val_eq, UScalarTy.U128_numBits_eq, U128.max_eq,
    Nat.shiftRight_eq_div_pow, knext, wdigit, wrapU128, pow_one, hp, ge_iff_le, IScalar.le_equiv,
    IScalar.ofInt_val_eq, not_le] at *)
  all_goals (split_ifs at * <;> omega)

end PastaCurves.Glv.Proofs
