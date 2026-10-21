import PastaCurves.Glv.Blueprint

/-! # `Table::new` on a valid point builds its table -/

namespace PastaCurves.Glv.Proofs

open PastaCurves.Glv.Blueprint

/-- `Table::new` on a valid point builds its table: the window is valid, the batch normalization
relates it entry by entry to affine points, and those make the table. -/
theorem tableNew : Blueprint.tableNew_stmt := by
  intro hwv hov P A G _ O V lam hO hE p hp
  have hb := hO.batchNormalize (windowProj O p) (List.replicate 8 O.identityA)
    (hwv O V lam hO hE p hp) (by simp [windowProj])
  exact hov O V lam hO hE p hp _ hb

end PastaCurves.Glv.Proofs
