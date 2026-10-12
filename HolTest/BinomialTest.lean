/- File: HolTest/BinomialTest.lean
Runtime test suite: Library/binomial.ml (HolLibrary/Binomial.lean, wired by
SessionLibrary/Binomial.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/binomial.ml"`, `set_margin 1000`, then `string_of_thm`).
tools/binomialdiff/check.sh compares far more structurally and runs the
NUM_BINOM_CONV cases in tools/binomialdiff/convs.txt.  CARD_RESTRICTED_POWERSET
prints with `?NNN` invented type variables so it is omitted here. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Binomial.ensureBinomial

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

namespace B
open Session SessionLibrary.Binomial HolLight.Syntax

#eval thm' "binom" binom
  "|- (forall n. binom (n,0) = 1) /\\ (forall k. binom (0,SUC k) = 0) /\\ (forall n k. binom (SUC n,SUC k) = binom (n,SUC k) + binom (n,k))"
#eval thm' "BINOM_REFL" BINOM_REFL
  "|- forall n. binom (n,n) = 1"
#eval thm' "BINOM_1" BINOM_1
  "|- forall n. binom (n,1) = n"
#eval thm' "BINOM_FACT" BINOM_FACT
  "|- forall n k. FACT n * FACT k * binom (n + k,k) = FACT (n + k)"
#eval thm' "BINOM_EQ_0" BINOM_EQ_0
  "|- forall n k. binom (n,k) = 0 <=> n < k"
#eval thm' "BINOMIAL_THEOREM" BINOMIAL_THEOREM
  "|- forall n x y. (x + y) EXP n = nsum (0..n) (\\k. binom (n,k) * x EXP k * y EXP (n - k))"
#eval thm' "REAL_BINOMIAL_THEOREM" REAL_BINOMIAL_THEOREM
  "|- forall n x y. (x + y) pow n = sum (0..n) (\\k. &(binom (n,k)) * x pow k * y pow (n - k))"
#eval thm' "BINOM_SYM" BINOM_SYM
  "|- forall n k. binom (n,n - k) = (if k <= n then binom (n,k) else 1)"
#eval thm' "REAL_OF_NUM_BINOM" REAL_OF_NUM_BINOM
  "|- forall n k. &(binom (n,k)) = (if k <= n then &(FACT n) / (&(FACT (n - k)) * &(FACT k)) else &0)"
#eval thm' "DIVIDES_PRIME_BINOM" DIVIDES_PRIME_BINOM
  "|- forall n p. prime p /\\ 0 < n /\\ n < p ==> p divides binom (p,n)"
#eval thm' "APPELL_SEQUENCE" APPELL_SEQUENCE
  "|- forall c n x y. sum (0..n) (\\k. &(binom (n,k)) * sum (0..k) (\\l. &(binom (k,l)) * c l * x pow (k - l)) * y pow (n - k)) = sum (0..n) (\\k. &(binom (n,k)) * c k * (x + y) pow (n - k))"

-- The NUM_BINOM_CONV conversion on numerals (expected values printed by HOL
-- Light); the last is the `n < k` failure branch (binom = 0).
#eval check "NUM_BINOM_CONV 6,2"
  (do match ← HolCore.Parser.parse_term r"binom(6,2)" with
      | .ok t => NUM_BINOM_CONV t | .error e => pure (.error e))
  "|- binom (6,2) = 15"
#eval check "NUM_BINOM_CONV 10,3"
  (do match ← HolCore.Parser.parse_term r"binom(10,3)" with
      | .ok t => NUM_BINOM_CONV t | .error e => pure (.error e))
  "|- binom (10,3) = 120"
#eval check "NUM_BINOM_CONV 5,5"
  (do match ← HolCore.Parser.parse_term r"binom(5,5)" with
      | .ok t => NUM_BINOM_CONV t | .error e => pure (.error e))
  "|- binom (5,5) = 1"
#eval check "NUM_BINOM_CONV 3,7"
  (do match ← HolCore.Parser.parse_term r"binom(3,7)" with
      | .ok t => NUM_BINOM_CONV t | .error e => pure (.error e))
  "|- binom (3,7) = 0"
#eval check "NUM_BINOM_CONV 52,5"
  (do match ← HolCore.Parser.parse_term r"binom(52,5)" with
      | .ok t => NUM_BINOM_CONV t | .error e => pure (.error e))
  "|- binom (52,5) = 2598960"

end B
