import PastaCurves.Glv.Spec

/-!
# Kernel evaluation of the model

The kernel evaluates the model directly (`decide +kernel`, no `native_decide`): digits, sums,
flags, one ladder run, the length at `leastFailing + 1`, which shows that the length is not
monotone, and the wrapped result on the four magnitudes where the `u128` addition overflows.
-/

open PastaCurves.Glv

set_option maxRecDepth 100000

example : (Wnaf.exec leastFailing false).n = 129 := by decide +kernel
example : (Wnaf.exec (leastFailing - 1) true).n = 128 := by decide +kernel
example : (Wnaf.exec 15 false).digits 0 = -1 := by decide +kernel
example : ∑ i : Fin 128, (Wnaf.exec 15 false).digits i * 2 ^ (i : ℕ) = 15 := by decide +kernel
example : ∑ i : Fin 128, (Wnaf.exec (2 ^ 127 - 1) true).digits i * 2 ^ (i : ℕ) = -(2 ^ 127 - 1) := by
  decide +kernel
example : (Wnaf.exec (2 ^ 128 - 7) false).u128Overflow = true := by decide +kernel
example : IsWnafDigit ((Wnaf.exec 15 false).digits 4) := by unfold IsWnafDigit; decide +kernel

-- W5's second conjunct, by the kernel:
example : ∀ neg : Bool, (Wnaf.exec leastFailing neg).n = 129 ∧
    (Wnaf.exec leastFailing neg).outOfBounds = true := by decide +kernel

-- W6 at its boundaries: the last 16 magnitudes, where the `u128` check fires exactly on the
-- four odd ones from `2^128 - 7`, and the assertion either side of `2^127`.
example : ∀ i : Fin 16, ∀ neg : Bool, (Wnaf.exec (2 ^ 128 - 16 + i) neg).u128Overflow =
    decide (i.val ∈ [9, 11, 13, 15]) := by decide +kernel
example : (Wnaf.exec (2 ^ 127 - 1) false).assertFailed = false ∧
    (Wnaf.exec (2 ^ 127) false).assertFailed = true := by decide +kernel

-- A ladder example (L1 over the integers): digits [-1, 0, 0, 0, 1] give 15.
example : Table.mulDecomposed (groupOps ℤ) ⟨oddMultiples 1, oddMultiples 0⟩
    ⟨fun i => if i = 0 then -1 else if i = 4 then 1 else 0, fun _ => 0, 5⟩ = some 15 := by
  decide +kernel

-- W5's remark that the length is not monotone: the magnitude after `leastFailing` needs only 128
-- digits.
example : ∀ neg : Bool, (Wnaf.exec (leastFailing + 1) neg).n = 128 := by decide +kernel

-- On the four magnitudes where the `u128` addition overflows, nothing is written past `digits`,
-- and the digits encode `a - 2^128`, negated when `neg`: what a build without debug assertions or
-- overflow checks returns there.
example : ∀ (i : Fin 4) (neg : Bool),
    (Wnaf.exec (2 ^ 128 - 7 + 2 * i.val) neg).outOfBounds = false ∧
    ∑ j : Fin 128, (Wnaf.exec (2 ^ 128 - 7 + 2 * i.val) neg).digits j * 2 ^ (j : ℕ) =
      if neg then 2 ^ 128 - ((2 ^ 128 - 7 + 2 * i.val : ℕ) : ℤ)
      else ((2 ^ 128 - 7 + 2 * i.val : ℕ) : ℤ) - 2 ^ 128 := by decide +kernel
