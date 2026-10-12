/- File: HolTest/WoTest.lean
Runtime test suite: Library/wo.ml (HolLibrary/Wo.lean, wired by
SessionLibrary/Wo.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/wo.ml"`, then `string_of_thm`, or the failure message).
tools/wodiff/check.sh compares far more structurally: all 159 theorems,
the constants and definitions and all 817 load messages. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Wo.ensureWo

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

namespace W
open Session SessionLibrary.Wo HolLight.Syntax

#eval thm' "fld" fld
  "|- forall R. fld R = {x | exists y. R x y \\/ R y x}"
#eval thm' "IN_FLD" IN_FLD
  "|- forall l x. x IN fld l <=> (exists y. l x y \\/ l y x)"
#eval thm' "woset" woset
  "|- forall l. woset l <=> (forall x. x IN fld l ==> l x x) /\\ (forall x y z. l x y /\\ l y z ==> l x z) /\\ (forall x y. l x y /\\ l y x ==> x = y) /\\ (forall x y. x IN fld l /\\ y IN fld l ==> l x y \\/ l y x) /\\ (forall s. s SUBSET fld l /\\ ~(s = {}) ==> (exists x. x IN s /\\ (forall y. y IN s ==> l x y)))"
#eval thm' "WOSET_WF" WOSET_WF
  "|- forall l. woset l <=> (forall x y. x IN fld l /\\ y IN fld l ==> l x y \\/ l y x) /\\ WF (properly l)"
#eval thm' "WQOSET_NOBAD" WQOSET_NOBAD
  "|- forall l. wqoset l <=> qoset l /\\ (forall x. (forall n. x n IN fld l) ==> (exists i j. i < j /\\ l (x i) (x j)))"
#eval thm' "QOSET_MIN" QOSET_MIN
  "|- forall l s. qoset l /\\ FINITE s /\\ ~(s = {}) /\\ s SUBSET fld l ==> (exists a. a IN s /\\ (forall x. x IN s ==> ~strictly l x a))"
#eval thm' "TOSET_MAX" TOSET_MAX
  "|- forall l s. toset l /\\ FINITE s /\\ ~(s = {}) /\\ s SUBSET fld l ==> (exists a. a IN s /\\ (forall x. x IN s ==> l x a))"
#eval thm' "WOSET_num" WOSET_num
  "|- woset (<=)"
#eval thm' "DICKSON" DICKSON
  "|- forall n x. exists i j. i < j /\\ (forall k. k < n ==> x i k <= x j k)"
#eval thm' "inseg" inseg
  "|- forall m l. l inseg m <=> (forall x y. l x y <=> m x y /\\ fld l y)"
#eval thm' "INSEG_LINSEG" INSEG_LINSEG
  "|- forall l m. woset l ==> (m inseg l <=> m = l \\/ (exists a. fld l a /\\ m = linseg l a))"
#eval thm' "POSET_ANTISYM" POSET_ANTISYM
  "|- forall l. poset l ==> (forall x y. l x y /\\ l y x ==> x = y)"
#eval thm' "WOSET_WELL" WOSET_WELL
  "|- forall l. woset l ==> (forall s. (forall x. s x ==> fld l x) /\\ (exists x. s x) ==> (exists x. s x /\\ (forall y. s y ==> l x y)))"
#eval thm' "ORDINAL_CHAINED" ORDINAL_CHAINED
  "|- forall l m. ordinal l /\\ ordinal m ==> m inseg l \\/ l inseg m"
#eval thm' "WO_ORDINAL" WO_ORDINAL
  "|- exists l. ordinal l /\\ (forall x. fld l x)"
#eval thm' "WO" WO
  "|- forall P. exists l. woset l /\\ fld l = P"
#eval thm' "WF_INSEG_WOSET" WF_INSEG_WOSET
  "|- WF (\\x y. woset x /\\ woset y /\\ x inseg y /\\ ~(x = y))"
#eval thm' "HP" HP
  "|- forall l. qoset l ==> (exists P. chain l P /\\ (forall Q. chain l Q /\\ P SUBSET Q ==> Q = P))"
#eval thm' "ZL" ZL
  "|- forall l. poset l /\\ (forall P. chain l P ==> (exists y. fld l y /\\ (forall x. P x ==> l x y))) ==> (exists y. fld l y /\\ (forall x. l y x ==> y = x))"
#eval thm' "KL" KL
  "|- forall l. poset l ==> (forall C. chain l C ==> (exists P. (chain l P /\\ C SUBSET P) /\\ (forall R. chain l R /\\ P SUBSET R ==> R = P)))"
#eval thm' "ZL_SUBSETS_UNIONS" ZL_SUBSETS_UNIONS
  "|- forall P. (forall c. (forall x. x IN c ==> P x) /\\ (forall x y. x IN c /\\ y IN c ==> x SUBSET y \\/ y SUBSET x) ==> P (UNIONS c)) ==> (exists a. P a /\\ (forall x. P x /\\ a SUBSET x ==> a = x))"
#eval thm' "TUKEY" TUKEY
  "|- forall s. ~(s = {}) /\\ (forall t. (forall c. FINITE c /\\ c SUBSET t ==> c IN s) <=> t IN s) ==> (exists u. u IN s /\\ (forall v. v IN s /\\ u SUBSET v ==> u = v))"
#eval thm' "OEP" OEP
  "|- forall p. poset p ==> (exists t. toset t /\\ fld t = fld p /\\ (forall x y. p x y ==> t x y))"
#eval thm' "TOSET_COFINAL_WOSET" TOSET_COFINAL_WOSET
  "|- forall l. toset l ==> (exists w. (forall x y. w x y ==> l x y) /\\ woset w /\\ (forall x. x IN fld l ==> (exists y. y IN fld w /\\ l x y)))"

-- PBETA_TAC in a proof, and a goal it leaves unproved; `inseg` parses as infix.
#eval check "PBETA_TAC"
  (HolLight.prove r"(\(x:num,y:num). x + y) (1,2) = 1 + 2" (PBETA_TAC THEN REFL_TAC)).run
  "|- (\\(x,y). x + y) (1,2) = 1 + 2"
#eval check "PBETA_TAC fail"
  (HolLight.prove r"(\(x:num,y:num). x + y) (1,2) = 3" (PBETA_TAC THEN REFL_TAC)).run
  "FAIL REFL_TAC"
#eval check "inseg parse" (do
    match ← HolCore.Parser.parse_term "(l:num->num->bool) inseg m" with
    | .ok t => pure (.ok (HolCore.Kernel.REFL t)) | .error e => pure (.error e))
  "|- l inseg m <=> l inseg m"

end W
