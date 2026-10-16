/- File: HolTest/CalcRealTest.lean
Runtime test suite: Library/calc_real.ml (HolLibrary/CalcReal.lean, wired by
SessionLibrary/CalcReal.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/calc_real.ml"`, then `string_of_thm`, newlines joined).
tools/calc_realdiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.CalcReal.ensureCalcReal

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

namespace T
open Session SessionLibrary.CalcReal HolLight.Syntax

#eval thm' "REAL_SUB_SUM0" REAL_SUB_SUM0
  "|- forall x y m. sum (0,m) x - sum (0,m) y = sum (0,m) (\\i. x i - y i)"
#eval thm' "REAL_MONO_POW2" REAL_MONO_POW2
  "|- forall m n. m <= n ==> &2 pow m <= &2 pow n"
#eval thm' "REAL_NDIV_LEMMA1b" REAL_NDIV_LEMMA1b
  "|- forall a m n. ~(&2 * abs (--(&2 pow m * &a) - &2 pow (m + n)) <= &2 pow m)"
#eval thm' "REALCALC_NEG" REALCALC_NEG
  "|- abs (a - &2 pow n * x) < &1 ==> abs (--a - &2 pow n * --x) < &1"
#eval thm' "REALCALC_MUL" REALCALC_MUL
  "|- abs (a - &2 pow k * x) < &1    ==> abs (b - &2 pow l * y) < &1    ==> n + m = k + l    ==> &2 * (abs a + abs b + &1) <= &2 pow m    ==> &2 * abs (&2 pow m * c - a * b) <= &2 pow m    ==> abs (c - &2 pow n * x * y) < &1"
#eval thm' "STEP_SIN" STEP_SIN
  "|- abs x <= &1 /\\    abs (s - &2 pow n * --(x pow 2)) <= &1 /\\    abs (t - &2 pow n * x pow (2 * i + 1) / &(FACT (2 * i + 1))) <= &1 /\\    &2 * abs (u * &2 pow n * &(2 * i + 2) * &(2 * i + 3) - s * t) <=    &2 pow n * &(2 * i + 2) * &(2 * i + 3)    ==> abs        (u - &2 pow n * --(x pow (2 * SUC i + 1)) / &(FACT (2 * SUC i + 1))) <=        &1"
#eval thm' "STEP_EXP_1" STEP_EXP_1
  "abs x <= &1 /\\ abs (s - &2 pow n * x) < &1 /\\ t 0 = &2 pow n, &2 * abs (t 1 * &2 pow n * &1 - s * t 0) <= &2 pow n * &1 |- abs x <= &1 /\\    abs (s - &2 pow n * x) < &1 /\\    abs (t 1 - &2 pow n * x pow 1 / &(FACT 1)) <= &3 / &2"
#eval thm' "STEP_EXP_4_PLUS" STEP_EXP_4_PLUS
  "|- 4 <= m /\\    abs x <= &1 /\\    abs (s - &2 pow n * x) < &1 /\\    t 0 = &2 pow n /\\    (forall k.         SUC k < SUC m         ==> &2 * abs (t (SUC k) * &2 pow n * &(SUC k) - s * t k) <=             &2 pow n * &(SUC k))    ==> abs (t m - &2 pow n * x pow m / &(FACT m)) <= &2"
#eval thm' "STEPS_EXP_4" STEPS_EXP_4
  "|- abs x <= &1 /\\    abs (s - &2 pow n * x) < &1 /\\    t 0 = &2 pow n /\\    (forall k.         SUC k < 4         ==> &2 * abs (t (SUC k) * &2 pow n * &(SUC k) - s * t k) <=             &2 pow n * &(SUC k))    ==> abs (sum (0,4) t - &2 pow n * sum (0,4) (\\i. x pow i / &(FACT i))) <=        &2 * &4"
#eval thm' "REAL_EXP_15" REAL_EXP_15
  "|- exp (&1) < &5"
#eval thm' "APPROX_LEMMA1" APPROX_LEMMA1
  "|- abs (f x - sum (0,m) (\\i. P i x)) < inv (&2 pow (n + 2)) /\\    abs (u - &2 pow (n + e + 2) * sum (0,m) (\\i. P i x)) <= &k * &m /\\    &k * &m <= &2 pow e /\\    abs (s * &2 pow (e + 2) - u) <= &2 pow (e + 1)    ==> abs (s - &2 pow n * f x) < &1"
#eval thm' "REALCALC_GT" REALCALC_GT
  "|- abs (a - &2 pow n * x) < &1 /\\ abs (b - &2 pow n * y) < &1    ==> &2 <= abs (a - b)    ==> (x > y <=> a > b)"
#eval thm' "REALCALC_EQ" REALCALC_EQ
  "|- abs (a - &2 pow n * x) < &1 /\\ abs (b - &2 pow n * y) < &1    ==> &2 <= abs (a - b)    ==> (x = y <=> false)"

-- The conversions on sample inputs (expected values printed by HOL Light;
-- a failure is expected as `FAIL <message>`).
#eval check "REALCALC_REL_CONV exp(&1) < &3" (do
    match ← HolCore.Parser.parse_term "exp(&1) < &3" with
    | .ok tm => REALCALC_REL_CONV tm
    | .error e => pure (.error e))
  "|- exp (&1) < &3 <=> true"
#eval check "REALCALC_REL_CONV exp(&1) > &2" (do
    match ← HolCore.Parser.parse_term "exp(&1) > &2" with
    | .ok tm => REALCALC_REL_CONV tm
    | .error e => pure (.error e))
  "|- exp (&1) > &2 <=> true"
#eval check "REALCALC_REL_CONV ln(&2) > &1 / &2" (do
    match ← HolCore.Parser.parse_term "ln(&2) > &1 / &2" with
    | .ok tm => REALCALC_REL_CONV tm
    | .error e => pure (.error e))
  "FAIL Can only do logs like ln(&1 + x) for small rational x"
#eval check "REALCALC_REL_CONV sqrt(&2) < &3 / &2" (do
    match ← HolCore.Parser.parse_term "sqrt(&2) < &3 / &2" with
    | .ok tm => REALCALC_REL_CONV tm
    | .error e => pure (.error e))
  "|- sqrt (&2) < &3 / &2 <=> true"
#eval check "REALCALC_REL_CONV sqrt(&2) * sqrt(&3) <= &5 / &2" (do
    match ← HolCore.Parser.parse_term "sqrt(&2) * sqrt(&3) <= &5 / &2" with
    | .ok tm => REALCALC_REL_CONV tm
    | .error e => pure (.error e))
  "|- sqrt (&2) * sqrt (&3) <= &5 / &2 <=> true"
#eval check "REALCALC_REL_CONV &1 / &3 + exp(&1 / &2) >= &1" (do
    match ← HolCore.Parser.parse_term "&1 / &3 + exp(&1 / &2) >= &1" with
    | .ok tm => REALCALC_REL_CONV tm
    | .error e => pure (.error e))
  "|- &1 / &3 + exp (&1 / &2) >= &1 <=> true"
#eval check "REALCALC_REL_CONV ln(&3) = &1" (do
    match ← HolCore.Parser.parse_term "ln(&3) = &1" with
    | .ok tm => REALCALC_REL_CONV tm
    | .error e => pure (.error e))
  "FAIL Can only do logs like ln(&1 + x) for small rational x"
#eval check "REALCALC_REL_CONV exp(&0) = &1" (do
    match ← HolCore.Parser.parse_term "exp(&0) = &1" with
    | .ok tm => REALCALC_REL_CONV tm
    | .error e => pure (.error e))
  "FAIL realcalc_rel_conv: too close to discriminate"
#eval check "REALCALC_REL_CONV --(&2) < abs(--(&3))" (do
    match ← HolCore.Parser.parse_term "--(&2) < abs(--(&3))" with
    | .ok tm => REALCALC_REL_CONV tm
    | .error e => pure (.error e))
  "|- -- &2 < abs (-- &3) <=> true"
#eval check "REALCALC_REL_CONV ln(&1 + &1 / &10) < &1 / &5" (do
    match ← HolCore.Parser.parse_term "ln(&1 + &1 / &10) < &1 / &5" with
    | .ok tm => REALCALC_REL_CONV tm
    | .error e => pure (.error e))
  "|- ln (&1 + &1 / &10) < &1 / &5 <=> true"
#eval check "REALCALC_REL_CONV ln(&1 + &1 / &2) > &1 / &3" (do
    match ← HolCore.Parser.parse_term "ln(&1 + &1 / &2) > &1 / &3" with
    | .ok tm => REALCALC_REL_CONV tm
    | .error e => pure (.error e))
  "FAIL ln of number not provably <= 1/2"

end T
