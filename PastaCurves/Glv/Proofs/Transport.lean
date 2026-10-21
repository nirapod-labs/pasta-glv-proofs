import PastaCurves.Glv.Blueprint

/-! # The ladder over the curve operations follows the ladder over the group -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- The ladder over the curve operations follows the ladder over the group under `α`: the same
outcome, through valid points. -/
theorem transport : Blueprint.transport_stmt := by
  intro hat P A G _ O V hO t D ht j
  induction j with
  | zero =>
    intro acc hacc
    exact ⟨by simp [ladderLoop], by intro r hr; simp [ladderLoop] at hr; rw [← hr]; exact hacc⟩
  | succ j ih =>
    intro acc hacc
    have hd : V.valid (if j + 1 < D.len then O.double acc else acc) := by
      split
      · exact (hO.double acc hacc).1
      · exact hacc
    have hdα : V.α (if j + 1 < D.len then O.double acc else acc) =
        (if j + 1 < D.len then (groupOps G).double (V.α acc) else V.α acc) := by
      split
      · exact (hO.double acc hacc).2
      · rfl
    simp only [ladderLoop]
    cases hd1 : digitAt D.digits1 j with
    | none => simp
    | some d1 =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      obtain ⟨e1, v1⟩ := hat O V hO _ t.t1 d1 hd (fun i => (ht i).1)
      rw [hdα] at e1
      cases ha1 : addDigit O.toLadderOps (if j + 1 < D.len then O.double acc else acc) t.t1 d1 with
      | none =>
        rw [ha1] at e1; simp at e1
        simp [← e1]
      | some r1 =>
        rw [ha1] at e1; simp at e1
        rw [← e1]
        simp only [Option.bind_some]
        cases hd2 : digitAt D.digits2 j with
        | none => simp
        | some d2 =>
          simp only [Option.bind_some]
          obtain ⟨e2, v2⟩ := hat O V hO r1 t.t2 d2 (v1 r1 ha1) (fun i => (ht i).2)
          cases ha2 : addDigit O.toLadderOps r1 t.t2 d2 with
          | none => rw [ha2] at e2; simp at e2; simp [← e2]
          | some r2 =>
            rw [ha2] at e2; simp at e2
            rw [← e2]
            simp only [Option.bind_some]
            exact ih r2 (v2 r2 ha2)

end PastaCurves.Glv.Proofs
