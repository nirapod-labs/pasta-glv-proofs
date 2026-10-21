import PastaCurves.Glv.SpecA
import PastaCurves.Glv.Blueprint

/-!
# The Level-A Blueprint: lemmas that imply WA and WAok

The proofs of `SpecA.lean`'s statements are cut into lemmas, each the definition of a proposition
(`foo_stmt`) proved on its own, in `Proofs/Foo.lean`, as in `Blueprint.lean`: a lemma that rests on
others takes their statements as hypotheses, and when such a statement has hypotheses of its own,
the lemma takes those too. Level M's lemma statements (`Blueprint.step_k_stmt`, …) and the Spec's
statements (`W1_stmt`, `W2_stmt`, `W6_stmt`) appear as hypotheses where they are used. The second
half of this file proves WAx, WA and WAok from the lemmas (`WAx_of`, `WA_of`, `WAok_of`, and all
at once `specA_of`); `FinalA.lean` only applies `specA_of` to the proofs.

The route. Below `2^127` the model sets no flag (W1), so the translation's checks inside the loop
never fire there, and the loop needs only a success argument; the model's `n` ends at most at 128
(W2), so the unchecked-in-the-model `n += 1` stays far from `usize::MAX`. From `2^127` on, the
translation fails at its first statement, the `debug_assert!`, and the model's assertion flag is
set (W6). So the debug build of `wnaf_digits` panics only at the assertion, which is SpecA's
`WAx_stmt`: it names the error and rules out divergence, and implies WA (whose
`Option.ofResult` maps a failure and a divergence alike to `none`).

The loop is related to the model pass by pass: `LoopRel` reads the translation's state
`(digits, n, k)` as a model state, flags aside; one run of the body is one `Wnaf.step`
(`body_step_stmt`), and an induction on the model's fuel, unfolding Aeneas' `loop` once per pass,
gives the whole loop (`loop_ok_stmt`).
-/

namespace PastaCurves.Glv.BlueprintA

open PastaCurves.Glv Aeneas Aeneas.Std

/-- The translation's loop state `(digits, n, k)` read as the model state `s`, flags aside. -/
def LoopRel (digits : Std.Array Std.I8 128#usize) (n : Std.Usize) (k : Std.U128)
    (s : Wnaf.State) : Prop :=
  digitsOf digits = s.digits ∧ n.val = s.n ∧ k.val = s.k

/-! ## Lemmas: the translation's primitives -/

/-- The loop's three readings of `k` (lines 404–406): `k != 0` holds exactly when `k ≠ 0`,
`k & 1 == 1` exactly when `k` is odd, and `(k & 0xF) as i8` is `k mod 16`. -/
def kbits_stmt : Prop :=
  ∀ k : Std.U128, ((k != 0#u128) = true ↔ k.val ≠ 0) ∧ (k &&& 1#u128 = 1#u128 ↔ k.val % 2 = 1) ∧
    (UScalar.hcast IScalarTy.I8 (k &&& 15#u128)).val = ((k.val % 16 : ℕ) : ℤ)

/-- Writing `x` at a position `n < 128` of the digit array (line 408) changes the model's digit
`n` to `x` and no other digit. -/
def digitsOf_set_stmt : Prop :=
  ∀ (digits : Std.Array Std.I8 128#usize) (n : Std.Usize) (x : Std.I8) (h : n.val < 128),
    digitsOf (digits.set n x) = Function.update (digitsOf digits) ⟨n.val, h⟩ x.val

/-- `[0i8; 128]` (line 401) reads as the model's initial digits, all zero. -/
def digitsOf_repeat_stmt : Prop :=
  digitsOf (Std.Array.repeat 128#usize 0#i8) = fun _ => 0

/-- Lines 400–403: from `2^127` on the assertion fails; below it the loop starts from
`digits = [0; 128]`, `n = 0` and `k = a`. -/
def wnaf_entry_stmt : Prop :=
  ∀ (a : Std.U128) (neg : Bool), pasta_curves.glv.wnaf_digits a neg =
    if a.val < 2 ^ 127 then
      pasta_curves.glv.wnaf_digits_loop neg (Std.Array.repeat 128#usize 0#i8) 0#usize a
    else .fail .assertionFailure

/-- One unfolding of Aeneas' `loop`: when the body continues, the loop goes on from the body's
new state; when the body is done, the loop returns the body's value. -/
def loop_unfold_stmt : Prop :=
  ∀ (neg : Bool) (digits : Std.Array Std.I8 128#usize) (n : Std.Usize) (k : Std.U128),
    (∀ (neg' : Bool) (digits' : Std.Array Std.I8 128#usize) (n' : Std.Usize) (k' : Std.U128),
      pasta_curves.glv.wnaf_digits_loop.body neg digits n k =
          .ok (.cont (neg', digits', n', k')) →
        pasta_curves.glv.wnaf_digits_loop neg digits n k =
          pasta_curves.glv.wnaf_digits_loop neg' digits' n' k') ∧
    (∀ v, pasta_curves.glv.wnaf_digits_loop.body neg digits n k = .ok (.done v) →
      pasta_curves.glv.wnaf_digits_loop neg digits n k = .ok v)

/-- The body at `k = 0` (line 404): the loop is done and returns `(digits, n)`. -/
def body_zero_stmt : Prop :=
  kbits_stmt →
    ∀ (neg : Bool) (digits : Std.Array Std.I8 128#usize) (n : Std.Usize) (k : Std.U128),
      k.val = 0 → pasta_curves.glv.wnaf_digits_loop.body neg digits n k = .ok (.done (digits, n))

/-- The body on an even nonzero `k` with `n < 128` (lines 405, 415, 416): no write, then
`n + 1` and `k >> 1`, neither of which fails. -/
def body_even_stmt : Prop :=
  kbits_stmt →
    ∀ (neg : Bool) (digits : Std.Array Std.I8 128#usize) (n : Std.Usize) (k : Std.U128),
      k.val ≠ 0 → k.val % 2 = 0 → n.val < 128 →
      ∃ (n' : Std.Usize) (k' : Std.U128),
        pasta_curves.glv.wnaf_digits_loop.body neg digits n k = .ok (.cont (neg, digits, n', k')) ∧
        n'.val = n.val + 1 ∧ k'.val = k.val / 2

/-- The body on an odd `k` with `n < 128` and `k - d < 2^128` (lines 405–416): it writes the
digit `d = wdigit k`, negated when `neg`, at position `n`, and continues with `n + 1` and
`knext k`; none of its checked operations fails. -/
def body_odd_stmt : Prop :=
  kbits_stmt →
    ∀ (neg : Bool) (digits : Std.Array Std.I8 128#usize) (n : Std.Usize) (k : Std.U128),
      n.val < 128 → k.val % 2 = 1 → (k.val : ℤ) - Blueprint.wdigit k.val < 2 ^ 128 →
      ∃ (d : Std.I8) (n' : Std.Usize) (k' : Std.U128),
        pasta_curves.glv.wnaf_digits_loop.body neg digits n k =
          .ok (.cont (neg, digits.set n d, n', k')) ∧
        d.val = (if neg then -Blueprint.wdigit k.val else Blueprint.wdigit k.val) ∧
        n'.val = n.val + 1 ∧ k'.val = Blueprint.knext k.val

/-! ## Lemmas: the model -/

/-- The model's loop never lowers `n`. -/
def loop_n_le_stmt : Prop :=
  Blueprint.step_n_stmt →
    ∀ (neg : Bool) (fuel : ℕ) (s : Wnaf.State), s.n ≤ (Wnaf.loop neg fuel s).n

/-- The model's flags are sticky: a state from which the loop ends with no flag set has no flag
set itself. -/
def loop_clear_stmt : Prop :=
  Blueprint.step_flags_stmt →
    ∀ (neg : Bool) (fuel : ℕ) (s : Wnaf.State),
      (Wnaf.loop neg fuel s).panicsIn true true = false → s.panicsIn true true = false

/-! ## Lemmas: the loop -/

/-- One pass: from a state related to `s` with `k ≠ 0` and `n < 128`, where the model's pass sets
no flag, the body continues to a state related to `Wnaf.step neg s`. -/
def body_step_stmt : Prop :=
  Blueprint.step_k_stmt → Blueprint.step_n_stmt → Blueprint.step_flags_stmt →
    Blueprint.step_digits_stmt → kbits_stmt → digitsOf_set_stmt → body_even_stmt →
    body_odd_stmt →
    ∀ (neg : Bool) (digits : Std.Array Std.I8 128#usize) (n : Std.Usize) (k : Std.U128)
      (s : Wnaf.State), LoopRel digits n k s → k.val ≠ 0 → n.val < 128 →
      (Wnaf.step neg s).panicsIn true true = false →
      ∃ (digits' : Std.Array Std.I8 128#usize) (n' : Std.Usize) (k' : Std.U128),
        pasta_curves.glv.wnaf_digits_loop.body neg digits n k =
          .ok (.cont (neg, digits', n', k')) ∧
        LoopRel digits' n' k' (Wnaf.step neg s)

/-- The loop: from a state related to `s`, with fuel at least `k`, where the model's loop from `s`
ends with no flag set and `n ≤ 128`, the translated loop returns the model's `(digits, n)`. -/
def loop_ok_stmt : Prop :=
  Blueprint.step_k_stmt → Blueprint.step_n_stmt → Blueprint.step_flags_stmt →
    Blueprint.step_digits_stmt → kbits_stmt → digitsOf_set_stmt → body_even_stmt →
    body_odd_stmt → body_step_stmt → body_zero_stmt → loop_unfold_stmt → loop_n_le_stmt →
    loop_clear_stmt →
    ∀ (neg : Bool) (fuel : ℕ) (s : Wnaf.State) (digits : Std.Array Std.I8 128#usize)
      (n : Std.Usize) (k : Std.U128), s.k ≤ fuel → LoopRel digits n k s →
      (Wnaf.loop neg fuel s).panicsIn true true = false → (Wnaf.loop neg fuel s).n ≤ 128 →
      ∃ r, pasta_curves.glv.wnaf_digits_loop neg digits n k = .ok r ∧
        readOut r = ((Wnaf.loop neg fuel s).digits, (Wnaf.loop neg fuel s).n)

/-! ## WA and WAok from the lemmas -/

/-- Below `2^127` the model sets no flag, by W1. -/
theorem panics_false (hW1 : W1_stmt) (a : ℕ) (neg : Bool) (ha : a < 2 ^ 127) :
    (Wnaf.exec a neg).panicsIn true true = false := by
  obtain ⟨af, oob, u, i8⟩ := hW1 a neg ha
  simp [Wnaf.State.panicsIn, af, oob, u, i8]

/-- WAx from the lemmas, W1, W2 and W6. -/
theorem WAx_of (hW1 : W1_stmt) (hW2 : W2_stmt) (hW6 : W6_stmt) (hk : Blueprint.step_k_stmt)
    (hn : Blueprint.step_n_stmt) (hf : Blueprint.step_flags_stmt)
    (hd : Blueprint.step_digits_stmt) (hb : kbits_stmt) (hs : digitsOf_set_stmt)
    (hr : digitsOf_repeat_stmt) (hen : wnaf_entry_stmt) (hu : loop_unfold_stmt)
    (hz : body_zero_stmt) (he : body_even_stmt) (ho : body_odd_stmt) (hbs : body_step_stmt)
    (hnl : loop_n_le_stmt) (hc : loop_clear_stmt) (hlo : loop_ok_stmt) : WAx_stmt := by
  intro a neg
  by_cases ha : a.val < 2 ^ 127
  · have hp := panics_false hW1 a.val neg ha
    refine ⟨fun h => by rw [hp] at h; exact absurd h Bool.false_ne_true, fun _ => ?_⟩
    rw [hen a neg, if_pos ha]
    have hrel : LoopRel (Std.Array.repeat 128#usize 0#i8) 0#usize a (Wnaf.init a.val) :=
      ⟨hr, rfl, rfl⟩
    exact hlo hk hn hf hd hb hs he ho hbs hz hu hnl hc neg a.val (Wnaf.init a.val) _ _ _ le_rfl
      hrel hp (hW2.2 a.val neg ha)
  · have ha128 : a.val < 2 ^ 128 := by scalar_tac
    have haf : (Wnaf.exec a.val neg).assertFailed = true :=
      ((hW6 a.val neg ha128).1).2 (by omega)
    have hp : (Wnaf.exec a.val neg).panicsIn true true = true := by
      simp [Wnaf.State.panicsIn, haf]
    refine ⟨fun _ => by rw [hen a neg, if_neg ha], fun h => ?_⟩
    rw [hp] at h
    exact absurd h.symm Bool.false_ne_true

/-- WA from WAx. -/
theorem WA_of_WAx (h : WAx_stmt) : WA_stmt := by
  intro a neg
  obtain ⟨h1, h2⟩ := h a neg
  cases hp : (Wnaf.exec a.val neg).panicsIn true true
  · obtain ⟨r, hr, hro⟩ := h2 hp
    simp [hr, Option.ofResult, hro]
  · simp [h1 hp, Option.ofResult]

/-- WA from the lemmas, W1, W2 and W6. -/
theorem WA_of (hW1 : W1_stmt) (hW2 : W2_stmt) (hW6 : W6_stmt) (hk : Blueprint.step_k_stmt)
    (hn : Blueprint.step_n_stmt) (hf : Blueprint.step_flags_stmt)
    (hd : Blueprint.step_digits_stmt) (hb : kbits_stmt) (hs : digitsOf_set_stmt)
    (hr : digitsOf_repeat_stmt) (hen : wnaf_entry_stmt) (hu : loop_unfold_stmt)
    (hz : body_zero_stmt) (he : body_even_stmt) (ho : body_odd_stmt) (hbs : body_step_stmt)
    (hnl : loop_n_le_stmt) (hc : loop_clear_stmt) (hlo : loop_ok_stmt) : WA_stmt :=
  WA_of_WAx (WAx_of hW1 hW2 hW6 hk hn hf hd hb hs hr hen hu hz he ho hbs hnl hc hlo)

/-- WAok from WA and W1: below `2^127` the model does not panic, so WA's right side is
`some (Wnaf.run a neg)`, and `Option.ofResult` is `some` only on `ok`. -/
theorem WAok_of_WA (hWA : WA_stmt) (hW1 : W1_stmt) : WAok_stmt := by
  intro a neg ha
  have h := hWA a neg
  rw [panics_false hW1 a.val neg ha] at h
  obtain ⟨r, hr, hro⟩ := Option.map_eq_some_iff.mp h
  refine ⟨r, ?_, hro⟩
  unfold Option.ofResult at hr
  split at hr
  · rename_i r' hm
    obtain rfl := Option.some.inj hr
    exact Result.match.isOk.mp hm
  · exact absurd hr (by simp)

/-- WAok from the lemmas, W1, W2 and W6. -/
theorem WAok_of (hW1 : W1_stmt) (hW2 : W2_stmt) (hW6 : W6_stmt) (hk : Blueprint.step_k_stmt)
    (hn : Blueprint.step_n_stmt) (hf : Blueprint.step_flags_stmt)
    (hd : Blueprint.step_digits_stmt) (hb : kbits_stmt) (hs : digitsOf_set_stmt)
    (hr : digitsOf_repeat_stmt) (hen : wnaf_entry_stmt) (hu : loop_unfold_stmt)
    (hz : body_zero_stmt) (he : body_even_stmt) (ho : body_odd_stmt) (hbs : body_step_stmt)
    (hnl : loop_n_le_stmt) (hc : loop_clear_stmt) (hlo : loop_ok_stmt) : WAok_stmt :=
  WAok_of_WA (WA_of hW1 hW2 hW6 hk hn hf hd hb hs hr hen hu hz he ho hbs hnl hc hlo) hW1

/-- WAx, WA and WAok from the 12 lemmas and Level M's W1, W2, W6 and pass lemmas: what
`FinalA.lean` applies to their proofs. -/
theorem specA_of (hW1 : W1_stmt) (hW2 : W2_stmt) (hW6 : W6_stmt) (hk : Blueprint.step_k_stmt)
    (hn : Blueprint.step_n_stmt) (hf : Blueprint.step_flags_stmt)
    (hd : Blueprint.step_digits_stmt) (hb : kbits_stmt) (hs : digitsOf_set_stmt)
    (hr : digitsOf_repeat_stmt) (hen : wnaf_entry_stmt) (hu : loop_unfold_stmt)
    (hz : body_zero_stmt) (he : body_even_stmt) (ho : body_odd_stmt) (hbs : body_step_stmt)
    (hnl : loop_n_le_stmt) (hc : loop_clear_stmt) (hlo : loop_ok_stmt) :
    WAx_stmt ∧ WA_stmt ∧ WAok_stmt :=
  have hWAx := WAx_of hW1 hW2 hW6 hk hn hf hd hb hs hr hen hu hz he ho hbs hnl hc hlo
  have hWA := WA_of_WAx hWAx
  ⟨hWAx, hWA, WAok_of_WA hWA hW1⟩

end PastaCurves.Glv.BlueprintA
