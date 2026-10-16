/- File: HolTest/QTest.lean
Runtime test suite: Library/q.ml (HolLibrary/Q.lean, wired by
SessionLibrary/Q.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/q.ml"`, then `string_of_thm` / `string_of_term`, newlines
joined; tools/qdiff/qprt.ml).  tools/qdiff/check.sh compares 25 cases
structurally. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Q.ensureQ

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private def report (lbl got expected : String) : IO Unit :=
  if squash got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

private unsafe def rule (lbl : String) (r : IO (Except String thm)) (expected : String) :
    IO Unit := do
  let got ← match ← r with
    | .ok th => HolCore.Printer.string_of_thm th
    | .error e => pure s!"FAIL {e}"
  report lbl got expected

/-- The subgoals a tactic leaves on goal `w`, joined with ` ;; `. -/
private unsafe def tac (lbl : String) (tc : HolCore.Tactics.tactic) (w : String)
    (expected : String) : IO Unit := do
  let got ← match ← HolCore.Parser.parse_term w with
    | .error e => pure s!"FAIL {e}"
    | .ok t => match ← tc ([], t) with
      | .error e => pure s!"FAIL {e}"
      | .ok (_, gl, _) => do
        let ss ← gl.mapM (fun (_, c) => HolCore.Printer.string_of_term c)
        pure (" ;; ".intercalate ss)
  report lbl got expected

unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

namespace T
open SessionLibrary.Q HolLight.Syntax
open HolLight (REPEAT STRIP_TAC GEN_TAC)

#eval rule "Pa.SPEC" (Pa.SPEC "x + 1" Session.ADD_SYM)
  "|- forall n. (x + 1) + n = n + x + 1"
#eval rule "Pa.SPECL" (Pa.SPECL ["a", "b"] Session.REAL_ADD_SYM)
  "|- a + b = b + a"
#eval rule "Pa.SPECL fail" (Pa.SPECL ["a", "b", "c"] Session.REAL_ADD_SYM)
  "FAIL SPECL"
#eval rule "Pa.GENL fail" (do
    match ← HolCore.Parser.parse_term "x + y = y + (x:num)" with
    | .error e => pure (.error e)
    | .ok t => match HolCore.Kernel.ASSUME t with
      | .error e => pure (.error e)
      | .ok th => Pa.GENL ["x", "y"] th)
  "FAIL ABS"
#eval rule "Pa.REAL_ARITH" (Pa.REAL_ARITH "x + y = y + x") "|- x + y = y + x"
#eval rule "Pa.ARITH_RULE" (Pa.ARITH_RULE "x + y = y + x") "|- x + y = y + x"
#eval rule "Pa.INT_ARITH" (Pa.INT_ARITH "x + y = y + x") "|- x + y = y + x"
#eval rule "Pa.REAL_FIELD" (Pa.REAL_FIELD "~(x = &0) ==> x * inv x = &1")
  "|- ~(x = &0) ==> x * inv x = &1"
#eval tac "Pa.EXISTS_TAC" (REPEAT STRIP_TAC THEN Pa.EXISTS_TAC "x")
  "!x:real. P x ==> ?y. P y" "P x"
#eval tac "Pa.X_GEN_TAC" (Pa.X_GEN_TAC "z") "!x:num. x + 0 = x" "z + 0 = z"
#eval tac "Pa.ASM_CASES_TAC" (REPEAT GEN_TAC THEN Pa.ASM_CASES_TAC "x < y")
  "!x y:int. x < y \\/ ~(x < y)" "x < y \\/ ~(x < y) ;; x < y \\/ ~(x < y)"
#eval tac "Pa.EXISTS_TAC fail" (Pa.EXISTS_TAC "x") "!x:real. P x" "FAIL dest_binder"

end T
