/- File: HolTest/PrimeTest.lean
Runtime test suite: Library/prime.ml (HolLibrary/Prime.lean, wired by
SessionLibrary/Prime.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/prime.ml"`, then `string_of_thm`).  The whole file is also
compared with HOL Light by tools/primediff/check.sh: all 279 theorems
structurally, the conversions on 28 inputs, constants and definitions.

Loading prime.ml (`ensurePrime`) builds every bundle in file order; a proof
that failed would `panic!`, which the `make verify` PANIC gate catches. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel Session SessionLibrary.Prime HolTest.CommonTest

#eval ensurePrime

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/-- Apply a conversion to a parsed term; compare the printed theorem, or the
    failure message as `FAIL msg`. -/
private unsafe def convCheck (lbl : String) (c : HolCore.Equal.ioconv) (s expected : String) :
    IO Unit := do
  let got ← match ← HolCore.Parser.parse_term s with
    | Except.error e => pure s!"FAIL parse: {e}"
    | Except.ok tm => do
      match ← c tm with
      | Except.ok th => pure (squash (← HolCore.Printer.string_of_thm th))
      | Except.error e => pure s!"FAIL {e}"
  if got == squash expected || got == expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- Theorem statements (prime.ml), as HOL Light prints them.               -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "prime.ml DIVIDES_0" DIVIDES_0
  "|- forall x. x divides 0"
#eval thmCheck "prime.ml GCD_BEZOUT" GCD_BEZOUT
  "|- forall a b d. (exists x y. a * x - b * y = d \\/ b * x - a * y = d) <=> gcd (a,b) divides d"
#eval thmCheck "prime.ml COPRIME_SYM" COPRIME_SYM
  "|- forall a b. coprime (a,b) <=> coprime (b,a)"
#eval thmCheck "prime.ml PRIME_DIVPROD" PRIME_DIVPROD
  "|- forall p a b. prime p /\\ p divides a * b ==> p divides a \\/ p divides b"
#eval thmCheck "prime.ml PRIMES_INFINITE" PRIMES_INFINITE
  "|- INFINITE {p | prime p}"
#eval thmCheck "prime.ml CHINESE_REMAINDER" CHINESE_REMAINDER
  "|- forall a b u v. coprime (a,b) /\\ ~(a = 0) /\\ ~(b = 0) ==> (exists x q1 q2. x = u + q1 * a /\\ x = v + q2 * b)"
#eval thmCheck "prime.ml index_def" index_def
  "|- forall p n. index p n = (if p <= 1 \\/ n = 0 then 0 else CARD {j | 1 <= j /\\ p EXP j divides n})"
#eval thmCheck "prime.ml INDEX_MUL" INDEX_MUL
  "|- forall m n. prime p /\\ ~(m = 0) /\\ ~(n = 0) ==> index p (m * n) = index p m + index p n"
#eval thmCheck "prime.ml lcm" lcm
  "|- lcm (m,n) = (if m * n = 0 then 0 else (m * n) DIV gcd (m,n))"
#eval thmCheck "prime.ml LCM_DIVIDES" LCM_DIVIDES
  "|- forall m n d. lcm (m,n) divides d <=> m divides d /\\ n divides d"
#eval thmCheck "prime.ml PRIMEPOW_DIVIDES_LCM" PRIMEPOW_DIVIDES_LCM
  "|- forall m n p k. prime p ==> (p EXP k divides lcm (m,n) <=> p EXP k divides m \\/ p EXP k divides n)"
#eval thmCheck "prime.ml INDUCT_COPRIME_ALT" INDUCT_COPRIME_ALT
  "|- forall P. P 0 /\\ (forall a b. 1 < a /\\ 1 < b /\\ coprime (a,b) /\\ P a /\\ P b ==> P (a * b)) /\\ (forall p k. prime p ==> P (p EXP k)) ==> (forall n. P n)"

/- ---------------------------------------------------------------------- -/
/- The conversions (prime.ml 2358-2472), as HOL Light computes them,      -/
/- including their failure messages.                                      -/
/- ---------------------------------------------------------------------- -/
#eval convCheck "DIVIDES_CONV 3 divides 12" DIVIDES_CONV "3 divides 12"
  "|- 3 divides 12 <=> true"
#eval convCheck "DIVIDES_CONV 4 divides 10" DIVIDES_CONV "4 divides 10"
  "|- 4 divides 10 <=> false"
#eval convCheck "DIVIDES_CONV 0 divides 5" DIVIDES_CONV "0 divides 5"
  "|- 0 divides 5 <=> false"
#eval convCheck "DIVIDES_CONV 0 divides 0" DIVIDES_CONV "0 divides 0"
  "|- 0 divides 0 <=> true"
#eval convCheck "DIVIDES_CONV x divides 2" DIVIDES_CONV "x divides 2"
  "FAIL NUM_EQ_CONV"
#eval convCheck "COPRIME_CONV coprime(12,35)" COPRIME_CONV "coprime(12,35)"
  "|- coprime (12,35) <=> true"
#eval convCheck "COPRIME_CONV coprime(35,12)" COPRIME_CONV "coprime(35,12)"
  "|- coprime (35,12) <=> true"
#eval convCheck "COPRIME_CONV coprime(6,9)" COPRIME_CONV "coprime(6,9)"
  "|- coprime (6,9) <=> false"
#eval convCheck "COPRIME_CONV coprime(0,0)" COPRIME_CONV "coprime(0,0)"
  "|- coprime (0,0) <=> false"
#eval convCheck "COPRIME_CONV x + 1" COPRIME_CONV "x + 1"
  "FAIL COPRIME_CONV"
#eval convCheck "GCD_CONV gcd(12,18)" GCD_CONV "gcd(12,18)"
  "|- gcd (12,18) = 6"
#eval convCheck "GCD_CONV gcd(0,0)" GCD_CONV "gcd(0,0)"
  "|- gcd (0,0) = 0"
#eval convCheck "GCD_CONV gcd(17,5)" GCD_CONV "gcd(17,5)"
  "|- gcd (17,5) = 1"
#eval convCheck "GCD_CONV gcd(x,1)" GCD_CONV "gcd(x,1)"
  "FAIL dest_numeral"
#eval convCheck "GCD_CONV lcm(1,2)" GCD_CONV "lcm(1,2)"
  "FAIL GCD_CONV"
#eval convCheck "LCM_CONV lcm(4,6)" LCM_CONV "lcm(4,6)"
  "|- lcm (4,6) = 12"
#eval convCheck "LCM_CONV lcm(0,3)" LCM_CONV "lcm(0,3)"
  "|- lcm (0,3) = 0"
#eval convCheck "LCM_CONV lcm(0,0)" LCM_CONV "lcm(0,0)"
  "|- lcm (0,0) = 0"
