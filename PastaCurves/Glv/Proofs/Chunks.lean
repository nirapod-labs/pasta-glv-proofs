import PastaCurves.Glv.Blueprint

/-! # `chunks_exact(8)` after a map that gives eight entries per element -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- `chunksExact8` on a list that starts with an eight-entry chunk. -/
private theorem chunks_append {Z : Type} (c : List Z) (rest : List Z) (hc : c.length = 8) :
    chunksExact8 (c ++ rest) = c :: chunksExact8 rest := by
  match c, hc with
  | [a0, a1, a2, a3, a4, a5, a6, a7], _ => simp [chunksExact8]

/-- `chunks_exact(8)` after a map that gives eight entries per element: chunk `i` is related,
entry by entry, to the eight entries of element `i`. -/
theorem chunks : Blueprint.chunks_stmt := by
  intro X Y Z R g xs zs hg hF
  induction xs generalizing zs with
  | nil =>
    simp at hF
    subst hF
    simp [chunksExact8]
  | cons x xs ih =>
    simp only [List.flatMap_cons] at hF
    have h8 := hg x
    have hc : List.Forall₂ R (g x) (zs.take 8) := by
      have := List.forall₂_take 8 hF
      rwa [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at this
    have hr : List.Forall₂ R (xs.flatMap g) (zs.drop 8) := by
      have := List.forall₂_drop 8 hF
      rwa [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
        List.nil_append] at this
    have hlen : (zs.take 8).length = 8 := by rw [← hc.length_eq, h8]
    rw [← List.take_append_drop 8 zs, chunks_append _ _ hlen]
    exact List.Forall₂.cons hc (ih _ hr)

end PastaCurves.Glv.Proofs
