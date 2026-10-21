import PastaCurves.Glv.BlueprintA

/-! # The loop's body on an even nonzero `k` -/

namespace PastaCurves.Glv.Proofs

open Aeneas Aeneas.Std Aeneas.Std.WP

/-- On an even nonzero `k` with `n < 128` the body writes nothing and continues with `n + 1` and
`k / 2`. -/
theorem body_even : BlueprintA.body_even_stmt := by
  intro hb neg digits n k hk0 hk hn
  suffices H : pasta_curves.glv.wnaf_digits_loop.body neg digits n k ⦃ r =>
      ∃ (n' : Std.Usize) (k' : Std.U128), r = .cont (neg, digits, n', k') ∧
        n'.val = n.val + 1 ∧ k'.val = k.val / 2 ⦄ by
    obtain ⟨r, hr, n', k', rfl, h⟩ := WP.spec_imp_exists H
    exact ⟨n', k', hr, h⟩
  unfold pasta_curves.glv.wnaf_digits_loop.body
  rw [if_pos ((hb k).1.mpr hk0)]
  simp only [lift, bind_ok]
  rw [if_neg (fun h => by have := (hb k).2.1.mp h; omega)]
  step*
  refine ⟨_, _, rfl, ?_, ?_⟩
  · scalar_tac
  · simp only [Nat.shiftRight_eq_div_pow, pow_one] at *
    omega

end PastaCurves.Glv.Proofs
