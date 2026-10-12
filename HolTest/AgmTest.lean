/- File: HolTest/AgmTest.lean
Runtime test suite: Library/agm.ml (HolLibrary/Agm.lean, wired by
SessionLibrary/Agm.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/agm.ml"`, `set_margin 1000`, then `string_of_thm`).  agm.ml
defines no conversions or rules, only theorems, and none of them print with
invented type variables, so each is checked directly. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Agm.ensureAgm

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thm' (lbl : String) (th : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm th)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

namespace A
open Session SessionLibrary.Agm HolLight.Syntax

#eval thm' "FORALL_2" FORALL_2
  "|- forall P. (forall i. 1 <= i /\\ i <= 2 ==> P i) <=> P 1 /\\ P 2"
#eval thm' "NUMSEG_2" NUMSEG_2
  "|- 1..2 = {1, 2}"
#eval thm' "AGM_2" AGM_2
  "|- forall x y. x * y <= ((x + y) / &2) pow 2"
#eval thm' "SUM_SPLIT_2" SUM_SPLIT_2
  "|- sum (1..2 * n) f = sum (1..n) f + sum (n + 1..2 * n) f"
#eval thm' "PRODUCT_SPLIT_2" PRODUCT_SPLIT_2
  "|- product (1..2 * n) f = product (1..n) f * product (n + 1..2 * n) f"
#eval thm' "CAUCHY_INDUCT" CAUCHY_INDUCT
  "|- forall P. P 2 /\\ (forall n. P n ==> P (2 * n)) /\\ (forall n. P (n + 1) ==> P n) ==> (forall n. P n)"
#eval thm' "AGM" AGM
  "|- forall n a. 1 <= n /\\ (forall i. 1 <= i /\\ i <= n ==> &0 <= a i) ==> product (1..n) a <= (sum (1..n) a / &n) pow n"

end A
