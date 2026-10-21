import PastaCurves.Glv.Blueprint

/-! # The ladder's loop in a group doubles the accumulator and adds the digits' values -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- One step of the ladder's loop, rearranged in the group. -/
private theorem alg {G : Type} [AddCommGroup G] (a p q : G) (d1 d2 S1 S2 : ℤ) (j : ℕ) :
    (2 ^ j : ℕ) • (2 • a + d1 • p + d2 • q) + S1 • p + S2 • q =
      (2 ^ (j + 1) : ℕ) • a + (S1 + d1 * 2 ^ j) • p + (S2 + d2 * 2 ^ j) • q := by
  rw [smul_add, smul_add, smul_smul, ← pow_succ, add_smul, add_smul]
  rw [← natCast_zsmul (d1 • p) (2 ^ j), ← natCast_zsmul (d2 • q) (2 ^ j), smul_smul, smul_smul]
  push_cast
  rw [mul_comm ((2 : ℤ) ^ j) d1, mul_comm ((2 : ℤ) ^ j) d2]
  abel

/-- The ladder's loop in a group, from position `j ≤ len`: the accumulator is doubled `j` times,
and the digits at positions `i < j` count `2^i` times. -/
theorem ladderLoop_group : Blueprint.ladderLoop_group_stmt := by
  intro hsb had G _ p q D h1 h2 hlen j
  induction j with
  | zero => intro acc _ _; simp [ladderLoop]
  | succ j ih =>
    intro acc hj hor
    have hj128 : j < 128 := by omega
    have hdbl : (if j + 1 < D.len then (groupOps G).double acc else acc) = 2 • acc := by
      split
      · rfl
      · rcases hor with h | h
        · omega
        · subst h; simp
    simp only [ladderLoop, hdbl, digitAt, hj128, dif_pos]
    simp only [Option.bind_eq_bind, Option.bind_some, had _ _ _ (h1 _), had _ _ _ (h2 _)]
    rw [ih _ (by omega) (Or.inl (by omega)), hsb _ j hj128, hsb _ j hj128]
    congr 1
    exact alg acc p q _ _ _ _ j

end PastaCurves.Glv.Proofs
