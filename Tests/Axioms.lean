import PastaCurves.Glv.Final
import PastaCurves.Glv.FinalA

/-!
# The axiom check

`Final.all` is the conjunction of the statements in `Spec.lean`, and `FinalA.all` that of
`SpecA.lean`. Both must list only `propext`, `Classical.choice` and `Quot.sound`; CI checks this
output.
-/

#print axioms PastaCurves.Glv.Final.all
#print axioms PastaCurves.Glv.FinalA.all
