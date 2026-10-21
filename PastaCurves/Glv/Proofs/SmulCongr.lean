import PastaCurves.Glv.Blueprint

/-! # An integer multiple of an element of order dividing `n` depends on the integer mod `n` -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- In a group, `n • x = 0` makes an integer multiple of `x` depend on the integer modulo `n`
only. -/
theorem smul_congr : Blueprint.smul_congr_stmt := by
  intro G _ x n a b hx hab
  obtain ⟨c, hc⟩ := (Int.ModEq.dvd hab)
  have : b = a + n * c := by omega
  rw [this, add_smul, mul_comm, mul_smul, natCast_zsmul, hx, smul_zero, add_zero]

end PastaCurves.Glv.Proofs
