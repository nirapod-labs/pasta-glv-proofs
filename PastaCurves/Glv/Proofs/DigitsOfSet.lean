import PastaCurves.Glv.BlueprintA

/-! # Writing one entry of the digit array -/

namespace PastaCurves.Glv.Proofs

open Aeneas Aeneas.Std

/-- Writing `x` at a position `n < 128` changes the model's digit `n` to `x` and no other digit. -/
theorem digitsOf_set : BlueprintA.digitsOf_set_stmt := by
  intro digits n x h
  funext i
  have hl : (digits.val).length = 128 := by simp
  by_cases hi : i = ⟨n.val, h⟩
  · subst hi
    simp only [digitsOf, Array.set_val_eq, Function.update_self]
    rw [List.getD_eq_getElem?_getD, List.getElem?_set]
    simp [hl, h]
  · rw [Function.update_of_ne hi]
    have hne : n.val ≠ i.val := fun e => hi (Fin.ext e.symm)
    simp only [digitsOf, Array.set_val_eq]
    rw [List.getD_eq_getElem?_getD, List.getElem?_set, if_neg hne, ← List.getD_eq_getElem?_getD]

end PastaCurves.Glv.Proofs
