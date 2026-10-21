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
import PastaCurves.Glv.Proofs.Kbits
import PastaCurves.Glv.Proofs.DigitsOfSet
import PastaCurves.Glv.Proofs.DigitsOfRepeat
import PastaCurves.Glv.Proofs.WnafEntry
import PastaCurves.Glv.Proofs.LoopUnfold
import PastaCurves.Glv.Proofs.BodyZero
import PastaCurves.Glv.Proofs.BodyEven
import PastaCurves.Glv.Proofs.BodyOdd
import PastaCurves.Glv.Proofs.LoopNLe
import PastaCurves.Glv.Proofs.LoopClear
import PastaCurves.Glv.Proofs.BodyStep
import PastaCurves.Glv.Proofs.LoopOk

/-! # WAx, WA and WAok, from the proofs of the lemmas of both levels -/

namespace PastaCurves.Glv.FinalA

/-- Level M's statements, from its 29 lemma proofs, as `Final.all` gives them. -/
theorem levelM : W1_stmt ∧ W2_stmt ∧ W3_stmt ∧ W4_stmt ∧ W5_stmt ∧ W6_stmt ∧ D_stmt ∧ L1_stmt ∧
    L2_stmt ∧ C_stmt ∧ CBatch_stmt :=
  Blueprint.spec_of Proofs.step_k Proofs.step_n Proofs.step_flags Proofs.step_digits
    Proofs.loop_n Proofs.loop_flags Proofs.loop_oob Proofs.loop_shape Proofs.sum_point
    Proofs.step_value Proofs.loop_value Proofs.gmin_rec Proofs.gmin_lower Proofs.passes_odd
    Proofs.kl Proofs.addDigit_group Proofs.sum_below_succ Proofs.ladderLoop_group
    Proofs.addDigit_transport Proofs.transport Proofs.window Proofs.windowValid Proofs.ofWindow
    Proofs.tableNew Proofs.chunks Proofs.tableBatch Proofs.decomposedNew Proofs.smul_congr
    Proofs.mulEach

/-- WAx, WA and WAok at once: `BlueprintA.specA_of` applied to Level M's W1, W2, W6 and pass
lemmas and to the 12 Level-A lemma proofs. -/
theorem all : WAx_stmt ∧ WA_stmt ∧ WAok_stmt :=
  BlueprintA.specA_of levelM.1 levelM.2.1 levelM.2.2.2.2.2.1 Proofs.step_k Proofs.step_n
    Proofs.step_flags Proofs.step_digits Proofs.kbits Proofs.digitsOf_set Proofs.digitsOf_repeat
    Proofs.wnaf_entry Proofs.loop_unfold Proofs.body_zero Proofs.body_even Proofs.body_odd
    Proofs.body_step Proofs.loop_n_le Proofs.loop_clear Proofs.loop_ok

/-- WAx: where the model says a debug build panics, the translation of `wnaf_digits` fails at the
assertion; elsewhere it returns the model's `(digits, n)`. -/
theorem WAx : WAx_stmt := all.1

/-- WA: Aeneas' translation of `wnaf_digits` fails exactly where the model says a debug build
panics, and otherwise returns the model's `(digits, n)`. -/
theorem WA : WA_stmt := all.2.1

/-- WAok: below `2^127` the translation returns the model's `(digits, n)`. -/
theorem WAok : WAok_stmt := all.2.2

end PastaCurves.Glv.FinalA
