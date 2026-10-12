/- File: HolTest/FloorTest.lean
Runtime test suite: Library/floor.ml (HolLibrary/Floor.lean, wired by
SessionLibrary/Floor.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/floor.ml"`, then `string_of_thm`).  The whole file is also
compared with HOL Light by tools/floordiff/check.sh: all 102 theorems
structurally, REAL_INTEGER_TAC on sample goals, constants and definitions.

Loading floor.ml (`ensureFloor`) builds every bundle in file order; a proof
that failed would `panic!`, which the `make verify` PANIC gate catches. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel Session SessionLibrary.Floor HolTest.CommonTest

#eval ensureFloor

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/-- Prove a goal with REAL_INTEGER_TAC; compare the theorem, or `FAIL msg`. -/
private unsafe def tacCheck (lbl : String) (s expected : String) : IO Unit := do
  let got ← match ← HolCore.Parser.parse_term s with
    | Except.error e => pure s!"FAIL parse: {e}"
    | Except.ok tm => do
      match ← Session.prove tm REAL_INTEGER_TAC with
      | Except.ok th => pure (squash (← HolCore.Printer.string_of_thm th))
      | Except.error e => pure s!"FAIL {e}"
  if got == squash expected || got == expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- Theorem statements (floor.ml), as HOL Light prints them.               -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "floor.ml INTEGER_CLOSED" INTEGER_CLOSED
  "|- (forall n. integer (&n)) /\\ (forall x y. integer x /\\ integer y ==> integer (x + y)) /\\ (forall x y. integer x /\\ integer y ==> integer (x - y)) /\\ (forall x y. integer x /\\ integer y ==> integer (x * y)) /\\ (forall x r. integer x ==> integer (x pow r)) /\\ (forall x. integer x ==> integer (--x)) /\\ (forall x. integer x ==> integer (abs x)) /\\ (forall x y. integer x /\\ integer y ==> integer (max x y)) /\\ (forall x y. integer x /\\ integer y ==> integer (min x y))"
#eval thmCheck "floor.ml rational" rational
  "|- forall x. rational x <=> (exists m n. integer m /\\ integer n /\\ ~(n = &0) /\\ x = m / n)"
#eval thmCheck "floor.ml FLOOR_FRAC" FLOOR_FRAC
  "|- forall x. integer (floor x) /\\ &0 <= frac x /\\ frac x < &1 /\\ x = floor x + frac x"
#eval thmCheck "floor.ml FLOOR" FLOOR
  "|- forall x. integer (floor x) /\\ floor x <= x /\\ x < floor x + &1"
#eval thmCheck "floor.ml REAL_FLOOR_ADD" REAL_FLOOR_ADD
  "|- forall x y. floor (x + y) = (if frac x + frac y < &1 then floor x + floor y else (floor x + floor y) + &1)"
#eval thmCheck "floor.ml FRAC_DIV_MOD" FRAC_DIV_MOD
  "|- forall m n. ~(n = 0) ==> frac (&m / &n) = &(m MOD n) / &n"
#eval thmCheck "floor.ml CARD_INTSEG_INT" CARD_INTSEG_INT
  "|- forall a b. integer a /\\ integer b ==> CARD {x | integer x /\\ a <= x /\\ x <= b} = (if b < a then 0 else num_of_int (int_of_real (b - a + &1)))"
#eval thmCheck "floor.ml INFINITE_RATIONAL" INFINITE_RATIONAL
  "|- INFINITE rational"
#eval thmCheck "floor.ml PADIC_RATIONAL_APPROXIMATION_STRADDLE_POS_LE" PADIC_RATIONAL_APPROXIMATION_STRADDLE_POS_LE
  "|- forall p x e. &0 < e /\\ &1 < p /\\ &0 <= x ==> (exists n q r. &q / p pow n <= x /\\ x < &r / p pow n /\\ abs (&q / p pow n - &r / p pow n) < e)"
#eval thmCheck "floor.ml RATIONAL_BETWEEN" RATIONAL_BETWEEN
  "|- forall a b. a < b ==> (exists q. rational q /\\ a < q /\\ q < b)"
#eval thmCheck "floor.ml REAL_INT_CONGRUENCE" REAL_INT_CONGRUENCE
  "|- forall a b n. (a == b) (mod n) <=> (if n = &0 then real_of_int a = real_of_int b else integer ((real_of_int a - real_of_int b) / real_of_int n))"

/- ---------------------------------------------------------------------- -/
/- REAL_INTEGER_TAC (floor.ml 850), as HOL Light runs it, with failures.  -/
/- ---------------------------------------------------------------------- -/
#eval tacCheck "REAL_INTEGER_TAC integer(&2 + &3 * &4)" "integer(&2 + &3 * &4)"
  "|- integer (&2 + &3 * &4)"
#eval tacCheck "REAL_INTEGER_TAC integer(abs(&3 - &5) pow 2)" "integer(abs(&3 - &5) pow 2)"
  "|- integer (abs (&3 - &5) pow 2)"
#eval tacCheck "REAL_INTEGER_TAC integer((&1 + &2) * (&3 - &4))" "integer((&1 + &2) * (&3 - &4))"
  "|- integer ((&1 + &2) * (&3 - &4))"
#eval tacCheck "REAL_INTEGER_TAC integer(x * &2)" "integer(x * &2)"
  "FAIL ACCEPT_TAC"
#eval tacCheck "REAL_INTEGER_TAC x = &1" "x = &1"
  "FAIL REAL_INTEGER_TAC: Goal not of expected form"
