/- File: HolTest/PocklingtonTest.lean
Runtime test suite: Library/pocklington.ml (HolLibrary/Pocklington.lean,
wired by SessionLibrary/Pocklington.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/pocklington.ml"`, `set_margin 1000`, then `string_of_thm`,
`string_of_num`, or the failure message).  tools/pocklingtondiff/check.sh
compares far more structurally: all 199 theorems, 12 conversion results,
the constants and definitions and all 2,553 load messages (including the
`proving that N is prime` remarks of the load-time examples). -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Pocklington.ensurePocklington

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private def report (lbl got expected : String) : IO Unit :=
  if got == squash expected || got == expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

private unsafe def check (lbl : String) (r : IO (Except String thm)) (expected : String) :
    IO Unit := do
  let got ← match ← r with
    | .ok th => pure (squash (← HolCore.Printer.string_of_thm th))
    | .error e => pure s!"FAIL {e}"
  report lbl got expected

private unsafe def thm' (lbl : String) (th : thm) (expected : String) : IO Unit :=
  check lbl (pure (.ok th)) expected

/-- A conversion on a parsed quotation. -/
private unsafe def onTerm (c : term → IO (Except String thm)) (s : String) :
    IO (Except String thm) := do
  match ← HolCore.Parser.parse_term s with
  | .ok t => c t
  | .error e => pure (.error e)

/-- A non-theorem value, compared as a string. -/
private def val (lbl : String) (r : ExceptT String IO String) (expected : String) : IO Unit := do
  let got ← match ← r.run with
    | .ok s => pure s
    | .error e => pure s!"FAIL {e}"
  if got == expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/-- `string_of_num` of an integral `Rat`. -/
private def son (r : Rat) : String := toString r.num

namespace K
open Session SessionLibrary.Pocklington HolLight.Syntax

#eval thm' "FERMAT_LITTLE" FERMAT_LITTLE
  "|- forall a n. coprime (a,n) ==> (a EXP phi n == 1) (mod n)"
#eval thm' "LUCAS" LUCAS
  "|- forall a n. 2 <= n /\\ (a EXP (n - 1) == 1) (mod n) /\\ (forall p. prime p /\\ p divides n - 1 ==> ~(a EXP ((n - 1) DIV p) == 1) (mod n)) ==> prime n"
#eval thm' "POCKLINGTON" POCKLINGTON
  "|- forall a n q r. 2 <= n /\\ n - 1 = q * r /\\ n <= q EXP 2 /\\ (a EXP (n - 1) == 1) (mod n) /\\ (forall p. prime p /\\ p divides q ==> coprime (a EXP ((n - 1) DIV p) - 1,n)) ==> prime n"
#eval thm' "PHI_MULTIPLICATIVE" PHI_MULTIPLICATIVE
  "|- forall a b. coprime (a,b) ==> phi (a * b) = phi a * phi b"
#eval thm' "PHI_PRIME_EQ" PHI_PRIME_EQ
  "|- forall n. phi n = n - 1 /\\ ~(n = 0) /\\ ~(n = 1) <=> prime n"
#eval thm' "ORDER_DIVIDES" ORDER_DIVIDES
  "|- forall n a d. (a EXP d == 1) (mod n) <=> order n a divides d"
#eval thm' "INVERSE_MOD_RMUL_EQ" INVERSE_MOD_RMUL_EQ
  "|- forall n x. (x * inverse_mod n x == 1) (mod n) <=> coprime (n,x)"
#eval thm' "SQUAREFREE_PRIME" SQUAREFREE_PRIME
  "|- forall n. squarefree n <=> (forall p. prime p ==> ~(p EXP 2 divides n))"
#eval thm' "CONG_CHINESE" CONG_CHINESE
  "|- coprime (a,b) /\\ (x == y) (mod a) /\\ (x == y) (mod b) ==> (x == y) (mod (a * b))"
#eval thm' "POCKLINGTON_PRIMEFACT" POCKLINGTON_PRIMEFACT
  "|- 2 <= n /\\ q * r = n - 1 /\\ n <= q * q ==> a EXP r MOD n = b ==> ITLIST (*) ps 1 = q ==> b EXP q MOD n = 1 ==> ALL (\\p. prime p /\\ coprime (b EXP (q DIV p) MOD n - 1,n)) ps ==> prime n"

-- The conversions and rules.
#eval check "CONG_CONV" (onTerm CONG_CONV "(12 == 5) (mod 7)")
  "|- (12 == 5) (mod 7) <=> true"
#eval check "INVERSE_MOD_CONV" (onTerm INVERSE_MOD_CONV "inverse_mod 17 5")
  "|- inverse_mod 17 5 = 7"
-- gcdex gives a negative coefficient here; mod_num must be Euclidean
#eval check "INVERSE_MOD_CONV neg" (onTerm INVERSE_MOD_CONV "inverse_mod 7 3")
  "|- inverse_mod 7 3 = 5"
#eval check "INVERSE_MOD_CONV fail" (onTerm INVERSE_MOD_CONV "inverse_mod 12 8")
  "FAIL INVERSE_MOD_CONV: not coprime"
#eval check "PRIME_CONV 65537" (onTerm PRIME_CONV "prime 65537")
  "|- prime 65537 <=> true"
#eval check "PRIME_CONV 91" (onTerm PRIME_CONV "prime 91")
  "|- prime 91 <=> false"
-- above PARI_THRESHOLD: `factor` calls gp, which is not installed in either
-- system, so multifactor falls back to trial division, as in HOL Light
#eval check "PRIME_CONV big" (onTerm PRIME_CONV "prime 33554467")
  "|- prime 33554467 <=> true"
#eval check "PRIME_CONV fail" (onTerm PRIME_CONV "coprime(2,3)")
  "FAIL expected term of form prime(n)"
#eval check "PRIME_TEST 2" (onTerm PRIME_TEST "2")
  "|- prime 2 <=> true"
#eval check "PROVE_PRIME 1009" (PROVE_PRIME 1009).run
  "|- prime 1009"
#eval check "PROVE_PRIME 1000" (PROVE_PRIME 1000).run
  "FAIL guided_certify_prime: input is not a prime"
#eval check "PROVE_PRIMEFACT 360" (PROVE_PRIMEFACT 360).run
  "|- primefact [2; 2; 2; 3; 3; 5] 360"
#eval check "PRIME_RULE" (onTerm (fun t => (PRIME_RULE ["2", "3", "5"] t).run) "prime 31")
  "|- prime 31"

-- The numeric utilities.
#eval val "extract_primes_from_certificate"
  (do return ",".intercalate (← extract_primes_from_certificate 1009)) "2,3,7,1009"
#eval val "multifactor" (do return ",".intercalate ((← multifactor 360).map son))
  "2,2,2,3,3,5"
#eval val "powermod" (pure (son (powermod 3 100 101))) "1"
#eval val "log2" (pure (son (log2 1025))) "11"

end K
