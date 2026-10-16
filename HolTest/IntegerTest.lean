/- File: HolTest/IntegerTest.lean
Runtime test suite: Library/integer.ml (HolLibrary/Integer.lean, wired by
SessionLibrary/Integer.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/integer.ml"`, then `string_of_thm`, newlines joined).
tools/integerdiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Integer.ensureInteger

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
open Session SessionLibrary.Integer HolLight.Syntax

#eval thm' "INT_DIVIDES_REFL" INT_DIVIDES_REFL
  "|- forall d. d divides d"
#eval thm' "INT_DIVIDES_LMUL2_EQ" INT_DIVIDES_LMUL2_EQ
  "|- forall a b c. ~(c = &0) ==> (c * a divides c * b <=> a divides b)"
#eval thm' "INT_ABS_GCD" INT_ABS_GCD
  "|- forall a b. abs (gcd (a,b)) = gcd (a,b)"
#eval thm' "INT_DIVIDES_GCD_RIGHT" INT_DIVIDES_GCD_RIGHT
  "|- forall m n. n divides m <=> gcd (m,n) = abs n"
#eval thm' "INT_LCM_1" INT_LCM_1
  "|- (forall n. lcm (&1,n) = abs n) /\\ (forall n. lcm (n,&1) = abs n)"
#eval thm' "INT_COPRIME_DIVPROD" INT_COPRIME_DIVPROD
  "|- forall d a b. d divides a * b /\\ coprime (d,a) ==> d divides b"
#eval thm' "INT_LCM_POW" INT_LCM_POW
  "|- forall a b n. lcm (a pow n,b pow n) = lcm (a,b) pow n"
#eval thm' "INT_CONG_MULT_LCANCEL_ALL" INT_CONG_MULT_LCANCEL_ALL
  "|- forall a x y n.        (a * x == a * y) (mod (a * n)) <=> a = &0 \\/ (x == y) (mod n)"
#eval thm' "INT_CONG_ADD_LCANCEL" INT_CONG_ADD_LCANCEL
  "|- forall a n x y. (a + x == a + y) (mod n) ==> (x == y) (mod n)"
#eval thm' "INT_CHINESE_REMAINDER_COPRIME_UNIQUE" INT_CHINESE_REMAINDER_COPRIME_UNIQUE
  "|- forall a b m n x y.        coprime (a,b) /\\        (x == m) (mod a) /\\        (x == n) (mod b) /\\        (y == m) (mod a) /\\        (y == n) (mod b)        ==> (x == y) (mod (a * b))"
#eval thm' "INT_PRIME_1" INT_PRIME_1
  "|- ~int_prime (&1)"
#eval thm' "INT_PRIME_DIVPROD_EQ" INT_PRIME_DIVPROD_EQ
  "|- forall p a b.        int_prime p ==> (p divides a * b <=> p divides a \\/ p divides b)"
#eval thm' "INT_EQ_PRIME_POW_POS" INT_EQ_PRIME_POW_POS
  "|- forall p q m n.        int_prime p /\\ int_prime q /\\ &0 <= p /\\ &0 <= q        ==> (p pow m = q pow n <=> m = 0 /\\ n = 0 \\/ p = q /\\ m = n)"
#eval thm' "INT_DIVIDES_FACT_PRIME" INT_DIVIDES_FACT_PRIME
  "|- forall p. int_prime p ==> (forall n. p divides &(FACT n) <=> abs p <= &n)"

end T
