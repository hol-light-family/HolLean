/- File: HolTest/BoolTest.lean
Runtime test suite: bool.ml - derived rules of the logical connectives.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

FAITHFULNESS BASIS.  Where a worked EXAMPLE in HOL Light's reference docs is
purely propositional it is pinned VERBATIM (gate on `MISMATCH`):
  hol-light/Help/CONJUNCT1.hlp   CONJUNCT1(ASSUME `p /\ q`) = p /\ q |- p
  hol-light/Help/DISJ1.hlp       DISJ1 TRUTH `F`            = |- T \/ F
Other examples in those docs use arithmetic or TAUT (not available at this
bootstrap layer); for those the DERIVED propositional analogue is checked with
`DIFFERS` (soft).  FAILURE cases pin the exact `failwith`/`mapError` strings
read from bool.ml's Lean port (Bool.lean).

All terms are bool-only, so no arithmetic layer needs forcing (gotcha #2); the
`/\`, `\/`, `==>`, `~` infix/prefix status is established by `setupBool` during
Session initialization, which CommonTest imports.

VERIFIED SIGNATURES (read from Bool.lean / Session.lean):
  ASSUME       : term -> Except String thm                    (Fusion/Kernel)
  Session.TRUTH: thm                                          (Session.lean 240)
  Session.CONJ     : thm -> thm -> Except String thm         (Bool.lean; Session 241)
  Session.CONJUNCT1: thm -> Except String thm  (mapError "CONJUNCT1")
  Session.DISJ1    : thm -> term -> Except String thm  (mapError "DISJ1")
  Session.DISCH    : term -> thm -> Except String thm
  Session.MP       : thm -> thm -> Except String thm  (failwith "MP: theorems do not agree")
  Session.SPEC     : term -> thm -> Except String thm  (mapError "SPEC")
  Session.CONTR    : term -> thm -> Except String thm  (failwith "CONTR")
  Session.NOT_ELIM : thm -> Except String thm  (mapError "NOT_ELIM")
  HolCore.Printer.string_of_thm : thm -> IO String
  concl : thm -> term ; hyp : thm -> List term  (Kernel) -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

namespace HolTest.BoolTest

/- ---------------------------------------------------------------------- -/
/- Reporting helpers.                                                     -/
/- ---------------------------------------------------------------------- -/

/-- Run an `Except String thm`, print its theorem space-stripped, compare to
    `exp`; gate on `MISMATCH` (VERBATIM Help expectation). -/
private unsafe def okThmVerbatim (lbl : String) (got : Except String thm) (exp : String) :
    IO Unit := do
  match got with
  | .error e => IO.println s!"{lbl} -> MISMATCH unexpected error: {e}"
  | .ok th =>
    let s := ((← HolCore.Printer.string_of_thm th).replace " " "").replace "\n" ""
    let e := exp.replace " " ""
    if s == e then IO.println s!"{lbl} -> OK"
    else IO.println s!"{lbl} -> MISMATCH got \"{s}\" expected \"{e}\""

/-- As `okThmVerbatim` but soft (`DIFFERS`) for a DERIVED expectation. -/
private unsafe def okThmDerived (lbl : String) (got : Except String thm) (exp : String) :
    IO Unit := do
  match got with
  | .error e => IO.println s!"{lbl} -> DIFFERS unexpected error: {e}"
  | .ok th =>
    let s := ((← HolCore.Printer.string_of_thm th).replace " " "").replace "\n" ""
    let e := exp.replace " " ""
    if s == e then IO.println s!"{lbl} -> OK"
    else IO.println s!"{lbl} -> DIFFERS got \"{s}\" expected \"{e}\""

/-- An `Except String α` MUST be `.error` with EXACTLY `expMsg`. -/
private def failMsg {α : Type} (lbl : String) (got : Except String α) (expMsg : String) :
    IO Unit :=
  match got with
  | .error e => if e == expMsg then IO.println s!"{lbl} -> OK (correctly rejected)"
                else IO.println s!"{lbl} -> MISMATCH msg=\"{e}\" expected=\"{expMsg}\""
  | .ok _    => IO.println s!"{lbl} -> MISMATCH unexpectedly succeeded"

/- ---------------------------------------------------------------------- -/
/- VERBATIM Help expectations (gate on MISMATCH).                          -/
/- ---------------------------------------------------------------------- -/

-- Help/CONJUNCT1.hlp: CONJUNCT1(ASSUME `p /\ q`) = `p /\ q |- p`.
#eval (do
  match (do ASSUME ([[ p /\ q ]])) with
  | .error e => IO.println s!"CONJUNCT1 setup ERR: {e}"
  | .ok ath => okThmVerbatim "Help/CONJUNCT1.hlp CONJUNCT1(p/\\q)"
                 (CONJUNCT1 ath) "p /\\ q |- p")

-- Help/DISJ1.hlp: DISJ1 TRUTH `F` = `|- T \/ F`.  The .hlp predates
-- `set_verbose_symbols` (bool.ml 504, CHANGES 24 Sep 2024), which is on by
-- default, so current HOL Light prints `T`/`F` as `true`/`false`.
#eval (do okThmVerbatim "Help/DISJ1.hlp DISJ1 TRUTH F"
            (DISJ1 TRUTH fF) "|- true \\/ false")

/- ---------------------------------------------------------------------- -/
/- DERIVED propositional analogues (print `DIFFERS`).                      -/
/- ---------------------------------------------------------------------- -/

-- CONJ (ASSUME p) (ASSUME q) = `p, q |- p /\ q`.  (Help/CONJ.hlp's own example
-- is arithmetic; this is the propositional analogue.)
#eval (do
  match (do ASSUME p), (do ASSUME q) with
  | .ok ap, .ok aq => okThmDerived "CONJ (ASSUME p)(ASSUME q)"
                        (CONJ ap aq) "p, q |- p /\\ q"
  | _, _ => IO.println "CONJ setup ERR")

-- DISCH p (ASSUME p) = `|- p ==> p` (the discharged hypothesis leaves no asm).
#eval (do
  match (do ASSUME p) with
  | .error e => IO.println s!"DISCH setup ERR: {e}"
  | .ok ap => okThmDerived "DISCH p (ASSUME p)" (DISCH p ap) "|- p ==> p")

-- NOT_ELIM(ASSUME `~p`) = `~p |- p ==> F` (Help/NOT_ELIM.hlp SHAPE, bool-only).
#eval (do
  match (do ASSUME ([[ ~p ]])) with
  | .error e => IO.println s!"NOT_ELIM setup ERR: {e}"
  | .ok ath => okThmDerived "NOT_ELIM(ASSUME ~p)" (NOT_ELIM ath) "~p |- p ==> false")

-- MP: from `|- p ==> p` (DISCH) and `p |- p` (ASSUME p) derive `p |- p`.
-- Non-commutative shape: MP needs the antecedent to match, so this pins the
-- direction (swapping the args would fail).
#eval (do
  match (do ASSUME p) with
  | .error e => IO.println s!"MP setup ERR: {e}"
  | .ok ap =>
    match DISCH p ap with
    | .error e => IO.println s!"MP setup2 ERR: {e}"
    | .ok imp => okThmDerived "MP (|- p==>p)(p|-p)" (MP imp ap) "p |- p")

/- ---------------------------------------------------------------------- -/
/- FAILURE cases: exact messages from Bool.lean.                           -/
/- ---------------------------------------------------------------------- -/

-- CONJUNCT1 on a non-conjunction (ASSUME p) fails with exactly "CONJUNCT1".
#eval (do
  match (do ASSUME p) with
  | .error e => IO.println s!"CONJUNCT1-fail setup ERR: {e}"
  | .ok ap => failMsg "CONJUNCT1 on non-conjunction" (CONJUNCT1 ap) "CONJUNCT1")

-- MP with a mismatched antecedent: `|- q ==> q` and `p |- p`.  The antecedent
-- `q` does not `aconv` `p`, so MP fails with "MP: theorems do not agree".
#eval (do
  match (do ASSUME p), (do ASSUME q) with
  | .ok ap, .ok aq =>
    match DISCH q aq with
    | .error e => IO.println s!"MP-fail setup ERR: {e}"
    | .ok qimp => failMsg "MP mismatched antecedent" (MP qimp ap)
                    "MP: theorems do not agree"
  | _, _ => IO.println "MP-fail setup ERR")

-- CONTR requires its theorem's conclusion to be `F`; `p |- p` is not, so
-- CONTR fails with exactly "CONTR".
#eval (do
  match (do ASSUME p) with
  | .error e => IO.println s!"CONTR-fail setup ERR: {e}"
  | .ok ap => failMsg "CONTR on non-F theorem" (CONTR q ap) "CONTR")

-- SPEC on a theorem that is not universally quantified (`p |- p`) fails with
-- exactly "SPEC" (the rule wraps every internal failure to that token).
#eval (do
  match (do ASSUME p) with
  | .error e => IO.println s!"SPEC-fail setup ERR: {e}"
  | .ok ap => failMsg "SPEC on non-forall" (SPEC q ap) "SPEC")

end HolTest.BoolTest
