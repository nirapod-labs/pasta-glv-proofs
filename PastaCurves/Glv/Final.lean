import PastaCurves.Glv.Proofs.StepK
import PastaCurves.Glv.Proofs.StepN
import PastaCurves.Glv.Proofs.StepFlags
import PastaCurves.Glv.Proofs.StepDigits
import PastaCurves.Glv.Proofs.LoopN
import PastaCurves.Glv.Proofs.LoopFlags
import PastaCurves.Glv.Proofs.LoopOob
import PastaCurves.Glv.Proofs.LoopShape
import PastaCurves.Glv.Proofs.SumPoint
import PastaCurves.Glv.Proofs.StepValue
import PastaCurves.Glv.Proofs.LoopValue
import PastaCurves.Glv.Proofs.GminRec
import PastaCurves.Glv.Proofs.GminLower
import PastaCurves.Glv.Proofs.PassesOdd
import PastaCurves.Glv.Proofs.Kl
import PastaCurves.Glv.Proofs.AddDigitGroup
import PastaCurves.Glv.Proofs.SumBelowSucc
import PastaCurves.Glv.Proofs.LadderLoopGroup
import PastaCurves.Glv.Proofs.AddDigitTransport
import PastaCurves.Glv.Proofs.Transport
import PastaCurves.Glv.Proofs.Window
import PastaCurves.Glv.Proofs.WindowValid
import PastaCurves.Glv.Proofs.OfWindow
import PastaCurves.Glv.Proofs.TableNew
import PastaCurves.Glv.Proofs.Chunks
import PastaCurves.Glv.Proofs.TableBatch
import PastaCurves.Glv.Proofs.DecomposedNew
import PastaCurves.Glv.Proofs.SmulCongr
import PastaCurves.Glv.Proofs.MulEach

/-! # Every statement of the Spec, from the proofs of the Blueprint's lemmas -/

namespace PastaCurves.Glv.Final

/-- Every statement of the Spec at once: `Blueprint.spec_of` applied to the 29 lemma proofs. -/
theorem all : W1_stmt ∧ W2_stmt ∧ W3_stmt ∧ W4_stmt ∧ W5_stmt ∧ W6_stmt ∧ D_stmt ∧ L1_stmt ∧
    L2_stmt ∧ C_stmt ∧ CBatch_stmt :=
  Blueprint.spec_of Proofs.step_k Proofs.step_n Proofs.step_flags Proofs.step_digits
    Proofs.loop_n Proofs.loop_flags Proofs.loop_oob Proofs.loop_shape Proofs.sum_point
    Proofs.step_value Proofs.loop_value Proofs.gmin_rec Proofs.gmin_lower Proofs.passes_odd
    Proofs.kl Proofs.addDigit_group Proofs.sum_below_succ Proofs.ladderLoop_group
    Proofs.addDigit_transport Proofs.transport Proofs.window Proofs.windowValid Proofs.ofWindow
    Proofs.tableNew Proofs.chunks Proofs.tableBatch Proofs.decomposedNew Proofs.smul_congr
    Proofs.mulEach

/-- W1 for the model: below `2^127`, `wnaf_digits` does not panic. -/
theorem W1 : W1_stmt := all.1

/-- W2 for the model: at most `⌊log₂ a⌋ + 2` digits on a `u128`, and 128 below `2^127`. -/
theorem W2 : W2_stmt := all.2.1

/-- W3 for the model: every digit is a width-4 wNAF digit. -/
theorem W3 : W3_stmt := all.2.2.1

/-- W4 for the model: the digits encode the signed magnitude, and are zero from `n` on. -/
theorem W4 : W4_stmt := all.2.2.2.1

/-- W5 for the model: below `leastFailing` no panic and at most 128 digits; at it, 129. -/
theorem W5 : W5_stmt := all.2.2.2.2.1

/-- W6 for the model: which magnitudes set the assertion, `i8` and `u128` flags. -/
theorem W6 : W6_stmt := all.2.2.2.2.2.1

/-- D for the model: `Decomposed` from two halves below `2^127`. -/
theorem D : D_stmt := all.2.2.2.2.2.2.1

/-- L1 for the model: the ladder over the group computes the digits' combination. -/
theorem L1 : L1_stmt := all.2.2.2.2.2.2.2.1

/-- L2 for the model: the window and the tables of `Table::new` and `Table::batch`. -/
theorem L2 : L2_stmt := all.2.2.2.2.2.2.2.2.1

/-- C for the model: the entry points compute `val k · p` without panicking, under H0 to H3. -/
theorem C : C_stmt := all.2.2.2.2.2.2.2.2.2.1

/-- C-batch for the model: `batch_mul_same_scalar_vartime`, under H0 to H3. -/
theorem CBatch : CBatch_stmt := all.2.2.2.2.2.2.2.2.2.2

end PastaCurves.Glv.Final
