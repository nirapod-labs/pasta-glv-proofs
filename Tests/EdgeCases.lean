import PastaCurves.Glv.Spec

/-!
# The model on the edge cases

`lake exe edgecases` prints every flag, the digit count and the encoded value for `0`, `1`, `2`,
`15`, both sides of `2^127`, the least magnitude that needs a 129th digit (`s`) and its
neighbours, and the top of the `u128` range, where the addition overflows.
-/

open PastaCurves.Glv

/-- The value the digits encode, computed directly. -/
def valueOf (d : Fin 128 → ℤ) : ℤ := (List.finRange 128).foldr (fun i acc => d i * 2 ^ (i : ℕ) + acc) 0

/-- Prints, for `a` and `neg`, the flags, `n`, `k`, whether a debug and a release build panic, the
encoded value beside the expected one, and the count and top three of the nonzero digits. -/
def report (label : String) (a : ℕ) (neg : Bool) : IO Unit := do
  let s := Wnaf.exec a neg
  let nz := (List.finRange 128).filterMap fun i => if s.digits i ≠ 0 then some (i.val, s.digits i) else none
  let top := nz.reverse.take 3
  IO.println s!"{label} neg={neg}: n={s.n} k={s.k} assert={s.assertFailed} oob={s.outOfBounds} u128={s.u128Overflow} i8={s.i8Overflow} debugPanics={s.panicsIn true true} releasePanics={s.panicsIn false false} value={valueOf s.digits} expect={if neg then -(a : ℤ) else a} nonzero={nz.length} top={top}"

/-- Runs `report` on every edge case, with both signs. -/
def main : IO Unit := do
  let s := leastFailing
  let cases : List (String × ℕ) :=
    [("0", 0), ("1", 1), ("2", 2), ("15", 15), ("2^127-1", 2^127 - 1), ("2^127", 2^127),
     ("s-1", s - 1), ("s", s), ("s+1", s + 1),
     ("2^128-7", 2^128 - 7), ("2^128-5", 2^128 - 5), ("2^128-3", 2^128 - 3), ("2^128-1", 2^128 - 1),
     ("2^128-9", 2^128 - 9), ("2^128-2", 2^128 - 2)]
  for (label, a) in cases do
    for neg in [false, true] do
      report label a neg
