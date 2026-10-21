import PastaCurves.Glv.Blueprint

/-! # The last loop of `batch_mul_same_scalar_vartime` -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- The last loop of `batch_mul_same_scalar_vartime`, over lists of equal length, each table
related to an element of `xs`, succeeds and relates its results to `xs`. -/
theorem mulEach : Blueprint.mulEach_stmt := by
  intro P A X O D R xs outs ts hlen hall
  induction hall generalizing outs with
  | nil =>
    obtain rfl : outs = [] := List.eq_nil_of_length_eq_zero hlen
    exact ⟨[], by simp [PastaCurves.Glv.mulEach], List.Forall₂.nil⟩
  | cons h _ ih =>
    obtain ⟨r, hr, hR⟩ := h
    cases outs with
    | nil => simp at hlen
    | cons o outs =>
      obtain ⟨rs, hrs, hR'⟩ := ih outs (by simpa using hlen)
      exact ⟨r :: rs, by simp [PastaCurves.Glv.mulEach, hr, hrs], List.Forall₂.cons hR hR'⟩

end PastaCurves.Glv.Proofs
