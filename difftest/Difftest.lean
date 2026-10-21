import PastaCurves.Glv.Model

/-!
# The model's side of the differential test

`lake exe difftest MODE FILE` prints, for each input `a` of FILE and each `negate` in {0, 1}, what
the model says a build in MODE returns: `a negate panic`, or `a negate n d0 d1 …` with the digits
up to the last nonzero one. The format is the Rust driver's (`src/main.rs`), so the two outputs
can be compared with `cmp`. MODE `debug` has debug assertions and overflow checks, `release`
neither, `release-ovf` overflow checks only, and `debug-noovf` debug assertions only.
-/

open PastaCurves.Glv

/-- The output line for `a` and `neg` in a build with the given checks. -/
def line (debugAssertions overflowChecks : Bool) (a : ℕ) (neg : Bool) : String :=
  let s := Wnaf.exec a neg
  let negS := if neg then "1" else "0"
  if s.panicsIn debugAssertions overflowChecks then s!"{a} {negS} panic"
  else
    let ds := (((List.finRange 128).map s.digits).reverse.dropWhile (· == 0)).reverse
    s!"{a} {negS} {s.n}" ++ String.join (ds.map fun d => s!" {d}")

/-- Prints the line of every magnitude in FILE, with both signs. -/
def main (args : List String) : IO Unit := do
  let (mode, file) ← match args with
    | [m, f] => pure (m, f)
    | _ => throw <| IO.userError "usage: Difftest.lean debug|release|release-ovf|debug-noovf FILE"
  let flags ← match mode with
    | "debug" => pure (true, true)
    | "release" => pure (false, false)
    | "release-ovf" => pure (false, true)
    | "debug-noovf" => pure (true, false)
    | _ => throw <| IO.userError s!"unknown mode {mode}"
  let out ← IO.getStdout
  for l in (← IO.FS.lines file) do
    if l.isEmpty then continue
    let a := l.toNat!
    for neg in [false, true] do
      out.putStrLn (line flags.1 flags.2 a neg)
