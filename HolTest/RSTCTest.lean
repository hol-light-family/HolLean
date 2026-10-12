/- File: HolTest/RSTCTest.lean
Runtime test suite: Library/rstc.ml (HolLibrary/RSTC.lean, wired by
SessionLibrary/RSTC.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/rstc.ml"`, then `string_of_thm`, or the failure message).
tools/rstcdiff/check.sh compares far more structurally: all 134 theorems,
the constants and definitions and all 249 load messages. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.RSTC.ensureRSTC

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

namespace R
open Session SessionLibrary.RSTC HolLight.Syntax

-- Reflexive, symmetric and transitive closures.
#eval thm' "RC_RULES" RC_RULES "|- forall R. (forall x y. R x y ==> RC R x y) /\\ (forall x. RC R x x)"
#eval thm' "SC_EXPLICIT" SC_EXPLICIT "|- forall R. SC R x y <=> R x y \\/ R y x"
#eval thm' "TC_CASES_L" TC_CASES_L
  "|- forall R x z. TC R x z <=> R x z \\/ (exists y. TC R x y /\\ R y z)"
#eval thm' "WF_TC" WF_TC "|- forall R. WF (TC R) <=> WF R"

-- Composite closures.
#eval thm' "RSC" RSC "|- forall R. RSC R = RC (SC R)"
#eval thm' "RTC_CASES_R" RTC_CASES_R
  "|- forall R x z. RTC R x z <=> x = z \\/ (exists y. R x y /\\ RTC R y z)"
#eval thm' "STC_CLOSED" STC_CLOSED
  "|- forall R. STC R = R <=> (forall x y. R x y ==> R y x) /\\ (forall x y z. R x y /\\ R y z ==> R x z)"
#eval thm' "RSTC_INDUCT" RSTC_INDUCT
  "|- forall R P. (forall x y. R x y ==> P x y) /\\ (forall x. P x x) /\\ (forall x y. P x y ==> P y x) /\\ (forall x y z. P x y /\\ P y z ==> P x z) ==> (forall x y. RSTC R x y ==> P x y)"
#eval thm' "RSTC_INC_RTC" RSTC_INC_RTC "|- forall R x y. RTC R x y ==> RSTC R x y"

-- Reverse relations and RELPOW.
#eval thm' "INV" INV "|- forall R y x. INV R x y <=> R y x"
#eval thm' "RELPOW" RELPOW
  "|- (RELPOW 0 R x y <=> x = y) /\\ (RELPOW (SUC n) R x y <=> (exists z. RELPOW n R x z /\\ R z y))"
#eval thm' "TC_RELPOW" TC_RELPOW "|- forall R x y. TC R x y <=> (exists n. RELPOW (SUC n) R x y)"
#eval thm' "RELPOW_SEQUENCE" RELPOW_SEQUENCE
  "|- forall R n x y. RELPOW n R x y <=> (exists f. f 0 = x /\\ f n = y /\\ (forall i. i < n ==> R (f i) (f (SUC i))))"

-- RULE_INDUCT_TAC: a proof that uses it, and a goal it does not match.
#eval check "RULE_INDUCT_TAC"
  (HolLight.prove r"!R:num->num->bool x y. SC R x y ==> R x y \/ R y x"
     (REPEAT GEN_TAC THEN RULE_INDUCT_TAC SC_INDUCT THEN MESON_TAC [])).run
  "|- forall R x y. SC R x y ==> R x y \\/ R y x"
#eval check "RULE_INDUCT_TAC no match"
  (HolLight.prove r"!R:num->num->bool. (!x y. R x y ==> R y x) ==> (!x y. TC R x y ==> TC R y x)"
     (GEN_TAC THEN DISCH_TAC THEN RULE_INDUCT_TAC TC_INDUCT THEN ASM_MESON_TAC [TC_RULES])).run
  "FAIL MATCH_MP_TAC: No match"

end R
