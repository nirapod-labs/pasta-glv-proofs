import PastaCurves.Glv.BlueprintA

/-! # One pass of the translated loop against `Wnaf.step` -/

namespace PastaCurves.Glv.Proofs

open Aeneas Aeneas.Std PastaCurves.Glv.Blueprint

/-- From a state related to `s` with `k ≠ 0` and `n < 128`, where the model's pass sets no flag,
the body continues to a state related to `Wnaf.step neg s`: an even `k` by `body_even`, an odd one
by `body_odd`, whose bound on `k - d` is the model's clear `u128` flag. -/
theorem body_step : BlueprintA.body_step_stmt := by
  intro hk hn hf hd hb hs he ho neg digits n k s hrel hk0 hn128 hp
  obtain ⟨hdig, hnn, hkk⟩ := hrel
  rcases Nat.mod_two_eq_zero_or_one k.val with hev | hod
  · obtain ⟨n', k', hbody, hn', hk'⟩ := he hb neg digits n k hk0 hev hn128
    refine ⟨digits, n', k', hbody, ?_, ?_, ?_⟩
    · funext i
      rw [hd neg s i, if_neg (by omega), hdig]
    · rw [hn neg s]
      omega
    · rw [hk neg s, knext, if_neg (by omega), hk', hkk]
  · have hover : (k.val : ℤ) - wdigit k.val < 2 ^ 128 := by
      obtain ⟨-, -, hu, -⟩ := hf neg s
      simp only [Wnaf.State.panicsIn, Bool.true_and, Bool.or_eq_false_iff] at hp
      have h2 := hp.1.2.1
      rw [hu] at h2
      simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at h2
      rw [← hkk] at h2
      omega
    obtain ⟨d, n', k', hbody, hdv, hn', hk'⟩ := ho hb neg digits n k hn128 hod hover
    refine ⟨digits.set n d, n', k', hbody, ?_, ?_, ?_⟩
    · rw [hs digits n d hn128]
      funext i
      rw [hd neg s i]
      by_cases hi : i = ⟨n.val, hn128⟩
      · subst hi
        rw [Function.update_self, if_pos ⟨by omega, hnn⟩, hdv, hkk]
      · rw [Function.update_of_ne hi,
          if_neg (fun ⟨_, h2⟩ => hi (Fin.ext (show i.val = n.val by omega))), hdig]
    · rw [hn neg s]
      omega
    · rw [hk neg s, hk', hkk]

end PastaCurves.Glv.Proofs
