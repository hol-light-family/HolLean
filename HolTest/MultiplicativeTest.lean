/- File: HolTest/MultiplicativeTest.lean
Runtime test suite: Library/multiplicative.ml (HolLibrary/Multiplicative.lean, wired by
SessionLibrary/Multiplicative.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/multiplicative.ml"`, then `string_of_thm`, newlines joined).
tools/multiplicativediff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Multiplicative.ensureMultiplicative

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def check (lbl : String) (r : IO (Except String thm)) (expected : String) :
    IO Unit := do
  let got ← match ← r with
    | .ok th => pure (squash (← HolCore.Printer.string_of_thm th))
    | .error e => pure s!"FAIL {e}"
  if got == squash expected || got == expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

private unsafe def thm' (lbl : String) (th : thm) (expected : String) : IO Unit :=
  check lbl (pure (.ok th)) expected

namespace T
open Session SessionLibrary.Multiplicative HolLight.Syntax

#eval thm' "multiplicative" multiplicative
  "|- forall f.        multiplicative f <=>        f 1 = 1 /\\ (forall m n. coprime (m,n) ==> f (m * n) = f m * f n)"
#eval thm' "MULTIPLICATIVE_IGNOREZERO" MULTIPLICATIVE_IGNOREZERO
  "|- forall f g.        (forall n. ~(n = 0) ==> g n = f n) /\\ multiplicative f        ==> multiplicative g"
#eval thm' "MULTIPLICATIVE_CONST" MULTIPLICATIVE_CONST
  "|- forall c. multiplicative (\\n. c) <=> c = 1"
#eval thm' "MULTIPLICATIVE_ID" MULTIPLICATIVE_ID
  "|- multiplicative (\\n. n)"
#eval thm' "tau" tau
  "|- forall n. tau n = (if n = 0 then 0 else CARD {d | d divides n})"
#eval thm' "MULTIPLICATIVE_PHI" MULTIPLICATIVE_PHI
  "|- multiplicative phi"
#eval thm' "MULTIPLICATIVE_UNIQUE" MULTIPLICATIVE_UNIQUE
  "|- forall f g.        multiplicative f /\\        multiplicative g /\\        (forall p k. prime p ==> f (p EXP k) = g (p EXP k))        ==> (forall n. ~(n = 0) ==> f n = g n)"
#eval thm' "REAL_MULTIPLICATIVE" REAL_MULTIPLICATIVE
  "|- real_multiplicative f <=>    f 1 = &1 /\\    (forall m n.         ~(m = 0) /\\ ~(n = 0) /\\ coprime (m,n) ==> f (m * n) = f m * f n)"
#eval thm' "REAL_MULTIPLICATIVE_IGNOREZERO" REAL_MULTIPLICATIVE_IGNOREZERO
  "|- forall f g.        (forall n. ~(n = 0) ==> g n = f n) /\\ real_multiplicative f        ==> real_multiplicative g"
#eval thm' "mobius" mobius
  "|- forall n.        mobius n =        (if squarefree n         then -- &1 pow CARD {p | prime p /\\ p divides n}         else &0)"
#eval thm' "MOBIUS_1" MOBIUS_1
  "|- mobius 1 = &1"
#eval thm' "REAL_MULTIPLICATIVE_MOBIUS" REAL_MULTIPLICATIVE_MOBIUS
  "|- real_multiplicative mobius"
#eval thm' "DIVISORSUM_MOBIUS" DIVISORSUM_MOBIUS
  "|- forall n.        1 <= n        ==> sum {d | d divides n} (\\d. mobius d) = (if n = 1 then &1 else &0)"
#eval thm' "MOBIUS_INVERSION" MOBIUS_INVERSION
  "|- forall f g.        (forall n. 1 <= n ==> g n = sum {d | d divides n} f)        ==> (forall n.                 1 <= n                 ==> f n = sum {d | d divides n} (\\d. mobius d * g (n DIV d)))"

end T
