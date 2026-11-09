/- File: HolTest/BertrandTest.lean
Runtime test suite: 100/bertrand.ml (HolLibrary/Bertrand.lean, wired by
SessionLibrary/Bertrand.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "100/bertrand.ml"`, then `string_of_thm`, newlines joined).
tools/bertranddiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary.Bertrand

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Bertrand.ensureBertrand

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
open Session SessionLibrary.Bertrand HolLight.Syntax

#eval thm' "BINOM_CENTRAL_STEP" BINOM_CENTRAL_STEP
  "|- forall n.        (n + 1) * binom (2 * n + 2,n + 1) = 2 * (2 * n + 1) * binom (2 * n,n)"
#eval thm' "BINOM_CENTRAL_LOWER" BINOM_CENTRAL_LOWER
  "|- forall n. 4 EXP n <= (2 * n + 1) * binom (2 * n,n)"
#eval thm' "BINOM_ODD_UPPER" BINOM_ODD_UPPER
  "|- forall k. binom (2 * k + 1,k) <= 4 EXP k"
#eval thm' "PRIME_DIVIDES_BINOM_ODD" PRIME_DIVIDES_BINOM_ODD
  "|- forall k p.        prime p /\\ k + 2 <= p /\\ p <= 2 * k + 1        ==> p divides binom (2 * k + 1,k)"
#eval thm' "NPRODUCT_PRIMES_DIVIDES" NPRODUCT_PRIMES_DIVIDES
  "|- forall s x.        FINITE s /\\ (forall p. p IN s ==> prime p /\\ p divides x)        ==> nproduct s (\\p. p) divides x"
#eval thm' "FINITE_PRIMES_LE" FINITE_PRIMES_LE
  "|- forall m P. FINITE {p | prime p /\\ P p /\\ p <= m}"
#eval thm' "PRIMORIAL_LE_4_EXP" PRIMORIAL_LE_4_EXP
  "|- forall m. nproduct {p | prime p /\\ p <= m} (\\p. p) <= 4 EXP m"
#eval thm' "DIV_DOUBLE_LE" DIV_DOUBLE_LE
  "|- forall n q. ~(q = 0) ==> (2 * n) DIV q <= 2 * n DIV q + 1"
#eval thm' "INDEX_BINOM_CENTRAL" INDEX_BINOM_CENTRAL
  "|- forall n p.        prime p        ==> index p (FACT n) + index p (FACT n) + index p (binom (2 * n,n)) =            index p (FACT (2 * n))"
#eval thm' "INDEX_BINOM_CENTRAL_CARD" INDEX_BINOM_CENTRAL_CARD
  "|- forall n p.        prime p        ==> index p (binom (2 * n,n)) <= CARD {j | 1 <= j /\\ p EXP j <= 2 * n}"
#eval thm' "INDEX_BINOM_CENTRAL_LE" INDEX_BINOM_CENTRAL_LE
  "|- forall n p. prime p /\\ 1 <= n ==> p EXP index p (binom (2 * n,n)) <= 2 * n"
#eval thm' "INDEX_BINOM_CENTRAL_SQRT" INDEX_BINOM_CENTRAL_SQRT
  "|- forall n p. prime p /\\ 2 * n < p * p ==> index p (binom (2 * n,n)) <= 1"
#eval thm' "PRIMEPOW_INDICES_SING" PRIMEPOW_INDICES_SING
  "|- forall p m.        2 <= p /\\ p <= m /\\ m < p * p ==> {j | 1 <= j /\\ p EXP j <= m} = {1}"
#eval thm' "INDEX_BINOM_CENTRAL_ZERO" INDEX_BINOM_CENTRAL_ZERO
  "|- forall n p.        prime p /\\ 3 <= p /\\ p <= n /\\ 2 * n < 3 * p        ==> index p (binom (2 * n,n)) = 0"
#eval thm' "BINOM_CENTRAL_UPPER" BINOM_CENTRAL_UPPER
  "|- forall n s.        3 <= n /\\ 2 * n < s * s /\\ (forall p. prime p /\\ n < p ==> 2 * n < p)        ==> binom (2 * n,n) <=            (2 * n) EXP s *            nproduct {p | prime p /\\ p <= (2 * n) DIV 3} (\\p. p)"
#eval thm' "EXP_4_BRACKET" EXP_4_BRACKET
  "|- forall m. 1 <= m ==> (exists t. 4 EXP t <= m /\\ m < 4 EXP (t + 1))"
#eval thm' "BERTRAND_THRESHOLD" BERTRAND_THRESHOLD
  "|- forall t. 7 <= t ==> 6 * (t + 1) * (2 EXP (t + 1) + 1) + 1 < 4 EXP t"
#eval thm' "BERTRAND_LARGE" BERTRAND_LARGE
  "|- forall n. 8192 <= n ==> (exists p. prime p /\\ n < p /\\ p <= 2 * n)"
#eval thm' "PRIME_TRIAL_DIVISION" PRIME_TRIAL_DIVISION
  "|- forall p m.        2 <= p /\\        p < m * m /\\        (forall d. d < m ==> 2 <= d /\\ d * d <= p ==> ~(d divides p))        ==> prime p"
#eval thm' "BERTRAND" BERTRAND
  "|- forall n. ~(n = 0) ==> (exists p. prime p /\\ n < p /\\ p <= 2 * n)"

end T
