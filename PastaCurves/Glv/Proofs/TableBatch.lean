import PastaCurves.Glv.Blueprint

/-! # `Table::batch` on valid points -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- `mapM` over a list related entry by entry to `xs` succeeds when `f` succeeds on each related
pair, and relates its results to `xs`. -/
private theorem mapM_of {X Y Z : Type} (f : Y → Option Z) (Q : X → Y → Prop) (R : X → Z → Prop)
    (xs : List X) (ys : List Y) (h : List.Forall₂ Q xs ys)
    (hf : ∀ x y, Q x y → ∃ z, f y = some z ∧ R x z) :
    ∃ zs, ys.mapM f = some zs ∧ List.Forall₂ R xs zs := by
  induction h with
  | nil => exact ⟨[], rfl, List.Forall₂.nil⟩
  | cons hq _ ih =>
    obtain ⟨z, hz, hR⟩ := hf _ _ hq
    obtain ⟨zs, hzs, hR'⟩ := ih
    exact ⟨z :: zs, by simp [hz, hzs], List.Forall₂.cons hR hR'⟩

/-- `Table::batch` on valid points builds their tables, in order. -/
theorem tableBatch : Blueprint.tableBatch_stmt := by
  intro hwv hov hch P A G _ O V lam hO hE ps hps
  unfold Table.batch
  dsimp only
  split
  · rename_i h0
    obtain rfl := List.eq_nil_of_length_eq_zero h0
    exact ⟨[], rfl, List.Forall₂.nil⟩
  · have hv : ∀ q ∈ ps.flatMap (windowProj O), V.valid q := by
      intro q hq
      obtain ⟨p, hp, hq⟩ := List.mem_flatMap.mp hq
      exact hwv O V lam hO hE p (hps p hp) q hq
    have hlen : (ps.flatMap (windowProj O)).length =
        (List.replicate (ps.length * 8) O.identityA).length := by
      rw [List.length_replicate, List.length_flatMap]
      have : ∀ p, (windowProj O p).length = 8 := fun p => rfl
      simp [this]
    have hb := hO.batchNormalize _ _ hv hlen
    have hc := hch _ (windowProj O) ps _ (fun p => rfl) hb
    obtain ⟨ts, hts, hR⟩ := mapM_of Table.ofWindow
      (fun p c => V.valid p ∧
        List.Forall₂ (fun q a => V.validA a ∧ V.αA a = V.α q) (windowProj O p) c)
      (TableOf V lam) ps _ ((List.forall₂_and_left _ _).2 ⟨hps, hc⟩)
      (fun p c h => hov O V lam hO hE p h.1 c h.2)
    exact ⟨ts, hts, hR⟩

end PastaCurves.Glv.Proofs
