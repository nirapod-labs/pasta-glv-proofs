import PastaCurves.Glv.BlueprintA

/-! # The translated loop returns the model's `(digits, n)` -/

namespace PastaCurves.Glv.Proofs

/-- From a state related to `s`, with fuel at least `k`, where the model's loop from `s` ends
with no flag set and `n ≤ 128`, the translated loop returns the model's `(digits, n)`. By
induction on the fuel: at `k = 0` both loops stop, and otherwise one body run is one model pass
(`body_step`), after which the loop goes on (`loop_unfold`). The model's run from the next state
still ends with no flag and `n ≤ 128`, so the pass itself sets no flag (`loop_clear`) and starts
below position 128 (`loop_n_le`). -/
theorem loop_ok : BlueprintA.loop_ok_stmt := by
  intro hk hn hf hd hb hs he ho hbs hz hu hnl hc neg fuel
  induction fuel with
  | zero =>
    intro s digits n k hle hrel _ _
    obtain ⟨hdig, hnn, hkk⟩ := hrel
    rw [(hu neg digits n k).2 _ (hz hb neg digits n k (by omega))]
    exact ⟨_, rfl, by simp [Wnaf.loop, readOut, hdig, hnn]⟩
  | succ f ih =>
    intro s digits n k hle hrel hp hn128
    obtain ⟨hdig, hnn, hkk⟩ := hrel
    by_cases hs0 : s.k = 0
    · rw [(hu neg digits n k).2 _ (hz hb neg digits n k (by omega))]
      exact ⟨_, rfl, by simp [Wnaf.loop, hs0, readOut, hdig, hnn]⟩
    · have hloop : Wnaf.loop neg (f + 1) s = Wnaf.loop neg f (Wnaf.step neg s) := by
        simp [Wnaf.loop, hs0]
      rw [hloop] at hp hn128 ⊢
      have hsp := hc hf neg f (Wnaf.step neg s) hp
      have hsn := hnl hn neg f (Wnaf.step neg s)
      rw [hn neg s] at hsn
      obtain ⟨digits', n', k', hbody, hrel'⟩ :=
        hbs hk hn hf hd hb hs he ho neg digits n k s ⟨hdig, hnn, hkk⟩ (by omega) (by omega) hsp
      rw [(hu neg digits n k).1 _ _ _ _ hbody]
      exact ih (Wnaf.step neg s) digits' n' k' (by have := Wnaf.step_k_lt neg s hs0; omega)
        hrel' hp hn128

end PastaCurves.Glv.Proofs
