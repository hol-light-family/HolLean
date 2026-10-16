/- File: HolTest/PrattTest.lean
Runtime test suite: Library/pratt.ml (HolLibrary/Pratt.lean, wired by
SessionLibrary/Pratt.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/pratt.ml"`, then `string_of_thm`, newlines joined).
tools/prattdiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Pratt.ensurePratt

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
open Session SessionLibrary.Pratt HolLight.Syntax

#eval thm' "nat_mod_lemma" nat_mod_lemma
  "|- forall x y n. (x == y) (mod n) /\\ y <= x ==> (exists q. x = y + n * q)"
#eval thm' "FINITE_NUMBER_SEGMENT" FINITE_NUMBER_SEGMENT
  "|- forall n. {m | 0 < m /\\ m < n} HAS_SIZE n - 1"
#eval thm' "CONG_0" CONG_0
  "|- forall x n. (x == 0) (mod n) <=> n divides x"
#eval thm' "CONG_REFL" CONG_REFL
  "|- forall x n. (x == x) (mod n)"
#eval thm' "phi" phi
  "|- forall n. phi n = CARD {m | 0 < m /\\ m <= n /\\ coprime (m,n)}"
#eval thm' "PHI_LIMIT" PHI_LIMIT
  "|- forall n. phi n <= n"
#eval thm' "PHI_1" PHI_1
  "|- phi 1 = 1"
#eval thm' "PHI_LOWERBOUND_2" PHI_LOWERBOUND_2
  "|- forall n. 3 <= n ==> 2 <= phi n"
#eval thm' "DIFFERENCE_POS_LEMMA" DIFFERENCE_POS_LEMMA
  "|- b <= a /\\ (exists x1 x2. x1 * n + a = x2 * n + b)    ==> (exists x. a = x * n + b)"
#eval thm' "FERMAT_LITTLE" FERMAT_LITTLE
  "|- forall a n. coprime (a,n) ==> (a EXP phi n == 1) (mod n)"
#eval thm' "LUCAS_WEAK" LUCAS_WEAK
  "|- forall a n.        2 <= n /\\        (a EXP (n - 1) == 1) (mod n) /\\        (forall m. 0 < m /\\ m < n - 1 ==> ~(a EXP m == 1) (mod n))        ==> prime n"
#eval thm' "PRIMEFACT" PRIMEFACT
  "|- forall n. ~(n = 0) ==> (exists ps. primefact ps n)"
#eval thm' "LUCAS_PRIMEFACT" LUCAS_PRIMEFACT
  "|- 2 <= n /\\    (a EXP (n - 1) == 1) (mod n) /\\    ITLIST (*) ps 1 = n - 1 /\\    ALL (\\p. prime p /\\ ~(a EXP ((n - 1) DIV p) == 1) (mod n)) ps    ==> prime n"

-- The conversions on sample inputs (expected values printed by HOL Light;
-- a failure is expected as `FAIL <message>`).
#eval check "PRIME_CONV prime 97" (do
    match ← HolCore.Parser.parse_term "prime 97" with
    | .ok tm => PRIME_CONV tm
    | .error e => pure (.error e))
  "|- prime 97 <=> true"
#eval check "PRIME_CONV prime 91" (do
    match ← HolCore.Parser.parse_term "prime 91" with
    | .ok tm => PRIME_CONV tm
    | .error e => pure (.error e))
  "|- prime 91 <=> false"
#eval check "PRIME_CONV prime 65537" (do
    match ← HolCore.Parser.parse_term "prime 65537" with
    | .ok tm => PRIME_CONV tm
    | .error e => pure (.error e))
  "|- prime 65537 <=> true"
#eval check "PRIME_CONV prime 1" (do
    match ← HolCore.Parser.parse_term "prime 1" with
    | .ok tm => PRIME_CONV tm
    | .error e => pure (.error e))
  "|- prime 1 <=> false"
#eval check "PRIME_CONV prime 2" (do
    match ← HolCore.Parser.parse_term "prime 2" with
    | .ok tm => PRIME_CONV tm
    | .error e => pure (.error e))
  "|- prime 2 <=> true"
#eval check "PRIME_CONV prime 1000003" (do
    match ← HolCore.Parser.parse_term "prime 1000003" with
    | .ok tm => PRIME_CONV tm
    | .error e => pure (.error e))
  "|- prime 1000003 <=> true"
#eval check "PRIME_CONV coprime(2,3)" (do
    match ← HolCore.Parser.parse_term "coprime(2,3)" with
    | .ok tm => PRIME_CONV tm
    | .error e => pure (.error e))
  "FAIL expected term of form prime(n)"
#eval check "EXP_EQ_MOD_CONV (2 EXP 10 == 1) (mod 11)" (do
    match ← HolCore.Parser.parse_term "(2 EXP 10 == 1) (mod 11)" with
    | .ok tm => EXP_EQ_MOD_CONV tm
    | .error e => pure (.error e))
  "|- (2 EXP 10 == 1) (mod 11) <=> true"
#eval check "EXP_EQ_MOD_CONV (3 EXP 5 == 1) (mod 7)" (do
    match ← HolCore.Parser.parse_term "(3 EXP 5 == 1) (mod 7)" with
    | .ok tm => EXP_EQ_MOD_CONV tm
    | .error e => pure (.error e))
  "|- (3 EXP 5 == 1) (mod 7) <=> false"

end T
