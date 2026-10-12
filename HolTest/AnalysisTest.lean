/- File: HolTest/AnalysisTest.lean
Runtime test suite: Library/analysis.ml (HolLibrary/Analysis.lean, wired by
SessionLibrary/Analysis.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/analysis.ml"`, then `string_of_thm`, or the failure message).
tools/analysisdiff/check.sh compares far more structurally: all 515 theorems,
the constants and definitions, the conversion tests in its convs.txt and all
97 load messages.

Names are qualified with `SessionLibrary.Analysis.` because about 100 of
analysis.ml's names (e.g. REAL_LE_ANTISYM, SUM_TWO) are also core names in
`Session`. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Analysis.ensureAnalysis

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

namespace A
open SessionLibrary.Analysis

-- Renamed HOL88 theorems, reals, abs, pow, sup, sums.
#eval thm' "LESS_SUC_REFL" LESS_SUC_REFL "|- forall n. n < SUC n"
#eval thm' "REAL_LE_TRANS" SessionLibrary.Analysis.REAL_LE_TRANS
  "|- forall x y z. x <= y /\\ y <= z ==> x <= z"
#eval thm' "REAL_LT_HALF1" REAL_LT_HALF1 "|- forall d. &0 < d / &2 <=> &0 < d"
#eval thm' "ABS_TRIANGLE" ABS_TRIANGLE "|- forall x y. abs (x + y) <= abs x + abs y"
#eval thm' "POW_2" POW_2 "|- forall x. x pow 2 = x * x"
#eval thm' "REAL_SUP" SessionLibrary.Analysis.REAL_SUP
  "|- forall P. (exists x. P x) /\\ (exists z. forall x. P x ==> x < z) ==> (forall y. (exists x. P x /\\ y < x) <=> y < sup P)"
#eval thm' "SUM_TWO" SessionLibrary.Analysis.SUM_TWO
  "|- forall f n p. sum (0,n) f + sum (n,p) f = sum (0,n + p) f"

-- Topologies and metric spaces.
#eval thm' "METRIC_TRIANGLE" METRIC_TRIANGLE
  "|- forall m x y z. mdist m (x,z) <= mdist m (x,y) + mdist m (y,z)"
#eval thm' "MTOP_LIMPT" MTOP_LIMPT
  "|- forall m x S. limpt (mtop m) x S <=> (forall e. &0 < e ==> (exists y. ~(x = y) /\\ S y /\\ mdist m (x,y) < e))"

-- Sequences and series.  After `remove_interface "-->"` HOL Light prints the
-- underlying constants (tends_num_real, tends_real_real).
#eval thm' "SEQ" SEQ
  "|- forall x x0. x tends_num_real x0 <=> (forall e. &0 < e ==> (exists N. forall n. n >= N ==> abs (x n - x0) < e))"
#eval thm' "SEQ_CAUCHY" SEQ_CAUCHY "|- forall f. cauchy f <=> convergent f"
#eval thm' "GP" GP "|- forall x. abs x < &1 ==> (\\n. x pow n) sums inv (&1 - x)"
#eval thm' "SER_RATIO" SER_RATIO
  "|- forall f c N. c < &1 /\\ (forall n. n >= N ==> abs (f (SUC n)) <= c * abs (f n)) ==> summable f"

-- Limits, continuity, derivatives.
#eval thm' "LIM" LIM
  "|- forall f y0 x0. (f tends_real_real y0) x0 <=> (forall e. &0 < e ==> (exists d. &0 < d /\\ (forall x. &0 < abs (x - x0) /\\ abs (x - x0) < d ==> abs (f x - y0) < e)))"
#eval thm' "DIFF_CHAIN" DIFF_CHAIN
  "|- forall f g l m x. (f diffl l) (g x) /\\ (g diffl m) x ==> ((\\x. f (g x)) diffl l * m) x"
#eval thm' "IVT" IVT
  "|- forall f a b y. a <= b /\\ (f a <= y /\\ y <= f b) /\\ (forall x. a <= x /\\ x <= b ==> f contl x) ==> (exists x. a <= x /\\ x <= b /\\ f x = y)"
#eval thm' "ROLLE" ROLLE
  "|- forall f a b. a < b /\\ f a = f b /\\ (forall x. a <= x /\\ x <= b ==> f contl x) /\\ (forall x. a < x /\\ x < b ==> f differentiable x) ==> (exists z. a < z /\\ z < b /\\ (f diffl &0) z)"
#eval thm' "MVT" MVT
  "|- forall f a b. a < b /\\ (forall x. a <= x /\\ x <= b ==> f contl x) /\\ (forall x. a < x /\\ x < b ==> f differentiable x) ==> (exists l z. a < z /\\ z < b /\\ (f diffl l) z /\\ f b - f a = (b - a) * l)"
#eval thm' "DIFF_INVERSE" DIFF_INVERSE
  "|- forall f g l x d. &0 < d /\\ (forall z. abs (z - x) <= d ==> g (f z) = z) /\\ (forall z. abs (z - x) <= d ==> f contl z) /\\ (f diffl l) x /\\ ~(l = &0) ==> (g diffl inv l) (f x)"
#eval thm' "CONT_UNIFORM" CONT_UNIFORM
  "|- forall f a b. a <= b /\\ (forall x. a <= x /\\ x <= b ==> f contl x) ==> (forall e. &0 < e ==> (exists d. &0 < d /\\ (forall x y. a <= x /\\ x <= b /\\ a <= y /\\ y <= b /\\ abs (x - y) < d ==> abs (f x - f y) < e)))"
#eval thm' "INTERVAL_ABS" INTERVAL_ABS
  "|- forall x z d. x - d <= z /\\ z <= x + d <=> abs (z - x) <= d"

-- Conversions.
#eval conv "REAL_SUM_CONV" REAL_SUM_CONV "sum(0,3) f"
  "|- sum (0,3) f = (f 0 + f (0 + 1)) + f (0 + 2)"
#eval conv "REAL_SUM_CONV" REAL_SUM_CONV "sum(1,2) f"
  "|- sum (1,2) f = (&0 + f (1 + 0)) + f (1 + 1)"
#eval conv "REAL_HORNER_SUM_CONV" REAL_HORNER_SUM_CONV "sum(0,3) (\\i. a i * x pow i)"
  "|- sum (0,3) (\\i. a i * x pow i) = a 0 + x * (a (SUC 0) + x * (\\i. a (SUC (SUC i)) * x pow i) 0)"
#eval do conv "X_BETA_CONV" (X_BETA_CONV (← tm "x:num")) "x + 1" "|- x + 1 = (\\x. x + 1) x"
#eval conv "EXISTS_UNIQUE_CONV" EXISTS_UNIQUE_CONV "?!x:num. x = 1"
  "|- (existsunique x. x = 1) <=> (exists x. x = 1) /\\ (forall x x'. x = 1 /\\ x' = 1 ==> x = x')"
#eval conv "OLD_SKOLEM_CONV" OLD_SKOLEM_CONV "!x:num. ?y:num. x < y"
  "|- (forall x. exists y. x < y) <=> (exists y. forall x. x < y x)"

end A
