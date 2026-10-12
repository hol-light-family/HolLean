/- File: HolTest/EqualTest.lean
Runtime test suite: equal.ml - basic equality reasoning and conversionals.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

FAITHFULNESS BASIS.  Successes are checked STRUCTURALLY (via `dest_eq`/`aconv`),
NOT by printed string: the printer renders `=` at `:bool` as `<=>`, so pinning a
printed equation would entangle this test with a printer concern.  Structural
checks isolate the equal.ml behaviour.  FAILURE cases pin the exact `failwith`
strings read from equal.ml's Lean port (Equal.lean).

Terms carry the type variable `:A` for the conversion successes so the derived
equation is genuinely `=` (not the boolean `<=>`), and `:A` is a NAMED type
variable (not an invented `?NNNN`), so it is stable across runs (gotcha #4).

VERIFIED SIGNATURES (read from Equal.lean):
  BETA_CONV   : term -> Except String thm  (failwith "BETA_CONV: Not a beta-redex")
  SYM         : thm  -> Except String thm
  AP_TERM     : term -> thm -> Except String thm  (failwith "AP_TERM")
  ALPHA_CONV  : term -> term -> Except String thm
  NO_CONV     : conv  (= term -> Except String thm)  (failwith "NO_CONV")
  ALL_CONV    : conv
  CHANGED_CONV: conv -> term -> Except String thm  (failwith "CHANGED_CONV")
  RATOR_CONV  : conv -> term -> Except String thm  (failwith "RATOR_CONV: Not a combination")
  THENC/ORELSEC : conv -> conv -> conv
  concl : thm -> term ; dest_eq : term -> Except String (term × term) ; aconv (Kernel) -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

namespace HolTest.EqualTest

/- Fixed atoms of type `:A`, hand-built so the derived equations are `=`. -/
private def aA : term := .Var "a" aty
private def idA : term := .Abs (.Var "x" aty) (.Var "x" aty)   -- \x:A. x

/- ---------------------------------------------------------------------- -/
/- Reporting helpers.                                                     -/
/- ---------------------------------------------------------------------- -/

/-- The theorem's conclusion must be an equation whose sides `aconv` `expL`,
    `expR`.  Structural, so the printer is not involved. -/
private unsafe def okEqn (lbl : String) (got : Except String thm) (expL expR : term) :
    IO Unit :=
  match got with
  | .error e => IO.println s!"{lbl} -> DIFFERS unexpected error: {e}"
  | .ok th =>
    match dest_eq (concl th) with
    | .error _ => IO.println s!"{lbl} -> DIFFERS conclusion not an equation"
    | .ok (l, r) =>
      if aconv l expL && aconv r expR then IO.println s!"{lbl} -> OK"
      else IO.println s!"{lbl} -> DIFFERS got sides {reprStr l} / {reprStr r}"

/-- An `Except String α` MUST be `.error` with EXACTLY `expMsg`. -/
private def failMsg {α : Type} (lbl : String) (got : Except String α) (expMsg : String) :
    IO Unit :=
  match got with
  | .error e => if e == expMsg then IO.println s!"{lbl} -> OK (correctly rejected)"
                else IO.println s!"{lbl} -> MISMATCH msg=\"{e}\" expected=\"{expMsg}\""
  | .ok _    => IO.println s!"{lbl} -> MISMATCH unexpectedly succeeded"

/- ---------------------------------------------------------------------- -/
/- Conversion SUCCESSES (structural).                                     -/
/- ---------------------------------------------------------------------- -/

-- BETA_CONV `(\x:A. x) a` = `|- (\x. x) a = a`.  RHS must be `a` (Help/
-- BETA_CONV.hlp shape, at type A so the equation is a genuine `=`).
#eval (do
  let redex := term.Comb idA aA           -- (\x:A. x) a
  okEqn "BETA_CONV (\\x. x) a" (BETA_CONV redex) redex aA)

-- SYM of that: `|- a = (\x. x) a`.  Sides swapped; discriminates from a
-- no-op SYM (which would leave the redex on the left).
#eval (do
  let redex := term.Comb idA aA
  match BETA_CONV redex with
  | .error e => IO.println s!"SYM setup ERR: {e}"
  | .ok bth => okEqn "SYM (BETA_CONV ...)" (SYM bth) aA redex)

-- ALPHA_CONV renames the bound variable: `|- (\x. x) = (\y. y)`.  Both sides
-- are alpha-equivalent identity functions; a broken ALPHA_CONV that failed to
-- rename would leave a NON-alpha result or error.
#eval (do
  let yA : term := .Var "y" aty
  let idY : term := .Abs yA yA
  okEqn "ALPHA_CONV y (\\x. x)" (ALPHA_CONV yA idA) idA idY)

/- ---------------------------------------------------------------------- -/
/- Conversion combinators.                                                -/
/- ---------------------------------------------------------------------- -/

-- ORELSEC NO_CONV ALL_CONV behaves as ALL_CONV: `|- a = a`.  Pins that the
-- first (always-failing) conversion is skipped and the second runs.
#eval (do okEqn "ORELSEC NO_CONV ALL_CONV" (ORELSEC NO_CONV ALL_CONV aA) aA aA)

-- THENC ALL_CONV ALL_CONV on `a` = `|- a = a`.  Pins the transitive
-- composition path (both stages identity).
#eval (do okEqn "THENC ALL_CONV ALL_CONV" (THENC ALL_CONV ALL_CONV aA) aA aA)

/- ---------------------------------------------------------------------- -/
/- FAILURE cases: exact messages from Equal.lean.                         -/
/- ---------------------------------------------------------------------- -/

-- NO_CONV always fails with exactly "NO_CONV".
#eval (do failMsg "NO_CONV always fails" (NO_CONV aA) "NO_CONV")

-- BETA_CONV on a non-redex (a bare variable) fails with the exact message
-- "BETA_CONV: Not a beta-redex".
#eval (do failMsg "BETA_CONV non-redex" (BETA_CONV aA) "BETA_CONV: Not a beta-redex")

-- RATOR_CONV on a non-combination (a bare variable) fails with the exact
-- message "RATOR_CONV: Not a combination".
#eval (do failMsg "RATOR_CONV non-comb" (RATOR_CONV ALL_CONV aA)
            "RATOR_CONV: Not a combination")

-- CHANGED_CONV wrapping ALL_CONV must fail (nothing changed) with exactly
-- "CHANGED_CONV".
#eval (do failMsg "CHANGED_CONV on no-op" (CHANGED_CONV ALL_CONV aA) "CHANGED_CONV")

-- AP_TERM with a non-function operator applied to an equation fails with
-- exactly "AP_TERM".  `a:A` is not a function, so `MK_COMB (REFL a) ...` is
-- ill-typed and AP_TERM catches it.
#eval (do
  let redex := term.Comb idA aA
  match BETA_CONV redex with
  | .error e => IO.println s!"AP_TERM setup ERR: {e}"
  | .ok bth => failMsg "AP_TERM non-function operator" (AP_TERM aA bth) "AP_TERM")

end HolTest.EqualTest
