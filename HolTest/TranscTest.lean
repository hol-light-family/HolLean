/- File: HolTest/TranscTest.lean
Runtime test suite: Library/transc.ml (HolLibrary/Transc.lean, wired by
SessionLibrary/Transc.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/transc.ml"`, then `string_of_thm`, or the failure message).
tools/transcdiff/check.sh compares far more structurally: all 323 theorems,
the constants and definitions, the conversion tests in its convs.txt and all
152 load messages.

Names that transc.ml rebinds (DIVISION_0, REAL_DIV_SQRT, SQRT_EVEN_POW2,
SUM_DIFFS, SYM_CANON_CONV, EXT_CONV) are qualified with
`SessionLibrary.Transc.`, since `Session` and SessionLibrary.Analysis have
their own. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Transc.ensureTransc

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

private unsafe def thm' (lbl : String) (th : thm) (expected : String) : IO Unit :=
  check lbl (pure (.ok th)) expected

private unsafe def conv (lbl : String) (c : term → IO (Except String thm)) (s expected : String) :
    IO Unit := do
  check s!"{lbl} {s}" (do c (← tm s)) expected

namespace T
open SessionLibrary.Transc HolLight.Syntax

-- exp, ln, sqrt, pi, trig, atn.
#eval thm' "DIFF_EXP" DIFF_EXP "|- forall x. (exp diffl exp x) x"
#eval thm' "REAL_EXP_ADD" REAL_EXP_ADD "|- forall x y. exp (x + y) = exp x * exp y"
#eval thm' "LN_MUL" LN_MUL "|- forall x y. &0 < x /\\ &0 < y ==> ln (x * y) = ln x + ln y"
#eval thm' "SQRT_EVEN_POW2" SessionLibrary.Transc.SQRT_EVEN_POW2
  "|- forall n. EVEN n ==> sqrt (&2 pow n) = &2 pow (n DIV 2)"
#eval thm' "REAL_DIV_SQRT" SessionLibrary.Transc.REAL_DIV_SQRT
  "|- forall x. &0 <= x ==> x / sqrt x = sqrt x"
#eval thm' "PI2_BOUNDS" PI2_BOUNDS "|- &0 < pi / &2 /\\ pi / &2 < &2"
#eval thm' "SIN_PI" SIN_PI "|- sin pi = &0"
#eval thm' "TAN_ATN" TAN_ATN "|- forall x. --(pi / &2) < x /\\ x < pi / &2 ==> atn (tan x) = x"
#eval thm' "DIFF_ATN" DIFF_ATN "|- forall x. (atn diffl inv (&1 + x pow 2)) x"

-- Gauge integrals.
#eval thm' "DIVISION_0" SessionLibrary.Transc.DIVISION_0
  "|- forall a b. a = b ==> dsize (\\n. if n = 0 then a else b) = 0"
#eval thm' "DINT_UNIQ" DINT_UNIQ
  "|- forall a b f k1 k2. a <= b /\\ defint (a,b) f k1 /\\ defint (a,b) f k2 ==> k1 = k2"
#eval thm' "FTC1" FTC1
  "|- forall f f' a b. a <= b /\\ (forall x. a <= x /\\ x <= b ==> (f diffl f' x) x) ==> defint (a,b) f' (f b - f a)"
#eval thm' "DEFINT_COMBINE" DEFINT_COMBINE
  "|- forall f a b c i j. a <= b /\\ b <= c /\\ defint (a,b) f i /\\ defint (b,c) f j ==> defint (a,c) f (i + j)"
#eval thm' "integral" integral "|- forall a b f. integral (a,b) f = (@i. defint (a,b) f i)"
#eval thm' "INTEGRABLE_CONTINUOUS" INTEGRABLE_CONTINUOUS
  "|- forall f a b. (forall x. a <= x /\\ x <= b ==> f contl x) ==> integrable (a,b) f"
#eval thm' "SUM_DIFFS" SessionLibrary.Transc.SUM_DIFFS
  "|- forall m n. sum (m,n) (\\i. d (SUC i) - d i) = d (m + n) - d m"

-- Taylor series.
#eval thm' "MCLAURIN_EXP_LE" MCLAURIN_EXP_LE
  "|- forall x n. exists t. abs t <= abs x /\\ exp x = sum (0,n) (\\m. x pow m / &(FACT m)) + exp t / &(FACT n) * x pow n"
#eval thm' "MCLAURIN_ATN" MCLAURIN_ATN
  "|- forall x n. abs x < &1 ==> abs (atn x - sum (0,n) (\\m. (if EVEN m then &0 else -- &1 pow ((m - 1) DIV 2) / &m) * x pow m)) <= abs x pow n / (&1 - abs x)"

-- Conversions and DIFF_TAC.
#eval conv "DIFF_CONV" DIFF_CONV "\\x. sin(x) * exp(x)"
  "|- forall x. ((\\x. sin x * exp x) diffl (cos x * &1) * exp x + (exp x * &1) * sin x) x"
#eval conv "DIFF_CONV" DIFF_CONV "\\x. ln(x pow 2 + &1)"
  "|- forall x. &0 < x pow 2 + &1 ==> ((\\x. ln (x pow 2 + &1)) diffl inv (x pow 2 + &1) * ((&2 * x pow (2 - 1)) * &1 + &0)) x"
#eval conv "DIFFERENTIABLE_CONV" DIFFERENTIABLE_CONV "(\\x. exp(x) - sin x) differentiable y"
  "|- (\\x. exp x - sin x) differentiable y <=> true"
#eval conv "CONTINUOUS_CONV" CONTINUOUS_CONV "(\\x. x pow 3 * cos(x)) contl &1"
  "|- (\\x. x pow 3 * cos x) contl &1 <=> true"
#eval conv "INTEGRABLE_CONV" INTEGRABLE_CONV "integrable(&0,&1) (\\x. sin(x) * exp(x))"
  "|- integrable (&0,&1) (\\x. sin x * exp x) <=> true"
#eval conv "INTEGRABLE_CONV" INTEGRABLE_CONV "integrable(&0,&1) (\\x. inv x)"
  "FAIL MATCH_MP: No match"
#eval conv "EXT_CONV" SessionLibrary.Transc.EXT_CONV
  "!x:num. (f:num->bool) x = g x" "|- (forall x. f x <=> g x) <=> f = g"
#eval do
  let one ← tm "1"
  conv "SYM_CANON_CONV" (SessionLibrary.Transc.SYM_CANON_CONV Session.ADD_SYM (fun (a, _) => a == one))
    "x + 1" "|- x + 1 = 1 + x"
#eval check "DIFF_TAC"
  (HolLight.prove r"((\x. exp(x) * sin(x)) diffl (exp(x) * cos(x) + sin(x) * exp(x))) x"
     (DIFF_TAC THEN Session.REAL_ARITH_TAC)).run
  "|- ((\\x. exp x * sin x) diffl exp x * cos x + sin x * exp x) x"

end T
