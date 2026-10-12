/- File: HolTest/BDDTest.lean
Runtime test suite: Library/bdd.ml (HolLibrary/BDD.lean, wired by
SessionLibrary/BDD.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/bdd.ml"`, then `string_of_thm`, or the failure message).
tools/bdddiff/check.sh compares a larger set structurally, with the
`bdd_stats` remarks that show the BDD tables are built in the same order. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel Session SessionLibrary.BDD HolTest.CommonTest

#eval ensureBDD

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def check (lbl : String) (r : IO (Except String thm)) (expected : String) :
    IO Unit := do
  let got ← match ← r with
    | .ok th => pure (squash (← HolCore.Printer.string_of_thm th))
    | .error e => pure s!"FAIL {e}"
  if got == squash expected || got == expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

private unsafe def tm (s : String) : IO term := do
  match ← HolCore.Parser.parse_term s with
  | .ok t => pure t | .error e => throw (IO.userError e)

private unsafe def taut (s expected : String) : IO Unit := do
  check s!"BDD_TAUT {s}" (do BDD_TAUT (← tm s)) expected

private unsafe def deftaut (vs : List String) (s expected : String) : IO Unit := do
  check s!"BDD_DEFTAUT {vs} {s}"
    (do BDD_DEFTAUT (← vs.mapM (fun v => tm (v ++ ":bool"))) (← tm s)) expected

#eval taut "(p ==> q) /\\ (q ==> r) ==> (p ==> r)" "|- (p ==> q) /\\ (q ==> r) ==> p ==> r"
#eval taut "~(p /\\ q) <=> ~p \\/ ~q" "|- ~(p /\\ q) <=> ~p \\/ ~q"
#eval taut "((p ==> q) ==> p) ==> p" "|- ((p ==> q) ==> p) ==> p"
#eval taut "f(a:bool) \\/ ~f(a)" "|- f a \\/ ~f a"
#eval taut "p /\\ q" "FAIL EQT_ELIM"
#eval taut "T" "|- true"
#eval deftaut [] "(s <=> x /\\ y) /\\ (c <=> x \\/ y) ==> (s ==> c)"
  "|- (s <=> x /\\ y) /\\ (c <=> x \\/ y) ==> s ==> c"
#eval deftaut ["q", "p"] "(a <=> p /\\ q) ==> (a ==> p)" "|- (a <=> p /\\ q) ==> a ==> p"
#eval deftaut [] "(a <=> a /\\ p) ==> p" "FAIL EQT_ELIM"
#eval deftaut [] "~a /\\ (b <=> c) ==> (b ==> c) /\\ ~a" "|- ~a /\\ (b <=> c) ==> (b ==> c) /\\ ~a"
