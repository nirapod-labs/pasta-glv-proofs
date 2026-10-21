import PastaCurves.Glv.Blueprint

/-! # `Decomposed::new` on a valid scalar -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- `Decomposed::new` on a valid scalar: no panic, digits of wNAF shape that are zero from
`len ≤ 128` on, and the two halves' values combine to `k` modulo `n`. -/
theorem decomposedNew : Blueprint.decomposedNew_stmt := by
  intro hW3 hD hW4 Sc S n lam f hdec k hk
  obtain ⟨⟨⟨neg1, a1⟩, ⟨neg2, a2⟩⟩, hf, h1, h2, hcong⟩ := hdec k hk
  dsimp only at h1 h2 hcong
  unfold D_stmt DOf at hD
  unfold W3_stmt W3Of at hW3
  unfold W4_stmt W4Of at hW4
  obtain ⟨D, hD1, hdig1, hdig2, -, hlen, hz⟩ := hD neg1 neg2 a1.val a2.val h1 h2
  have hnew : Decomposed.new f k = some D := by
    simp [Decomposed.new, hf, Aeneas.Std.Option.ofResult, hD1]
  refine ⟨D, hnew, ?_, ?_, hlen, hz, ?_⟩
  · intro i; rw [hdig1]; exact (hW3 a1.val neg1 (by omega) i).1
  · intro i; rw [hdig2]; exact (hW3 a2.val neg2 (by omega) i).1
  · rw [hdig1, hdig2]
    simp only [Wnaf.run]
    rw [(hW4 a1.val neg1 h1).1, (hW4 a2.val neg2 h2).1]
    simpa [decode] using hcong

end PastaCurves.Glv.Proofs
