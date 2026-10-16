/- File: HolTest/PrimitiveTest.lean
Runtime test suite: Library/primitive.ml (HolLibrary/Primitive.lean, wired by
SessionLibrary/Primitive.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/primitive.ml"`, then `string_of_thm`, newlines joined).
tools/primitivediff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Primitive.ensurePrimitive

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
open Session SessionLibrary.Primitive HolLight.Syntax

#eval thm' "INT_PRIME" INT_PRIME
  "|- forall p. int_prime (&p) <=> prime p"
#eval thm' "NUM_LAGRANGE_LEMMA" NUM_LAGRANGE_LEMMA
  "|- forall p d.        prime p /\\ 1 <= d        ==> CARD {x | x IN 1..p - 1 /\\ (x EXP d == 1) (mod p)} <= d"
#eval thm' "COPRIME_1_PLUS_POWER" COPRIME_1_PLUS_POWER
  "|- forall p z k.        prime p /\\ coprime (z,p) /\\ 3 <= p        ==> (exists w.                 coprime (w,p) /\\                 (1 + z * p) EXP (p EXP k) = 1 + w * p EXP (k + 1))"
#eval thm' "POWER_RESIDUE_MODULO_EQ_ALT" POWER_RESIDUE_MODULO_EQ_ALT
  "|- forall n k.        ~(n = 0)        ==> ((forall a.                  coprime (n,a)                  ==> (exists x. coprime (n,x) /\\ (x EXP k == a) (mod n))) <=>             coprime (k,phi n))"
#eval thm' "PRIMITIVE_ROOT_MODULO_DOUBLE_PRIMEPOW" PRIMITIVE_ROOT_MODULO_DOUBLE_PRIMEPOW
  "|- forall p k.        prime p /\\ 3 <= p /\\ 1 <= k        ==> (exists x.                 x IN 1..2 * p EXP k - 1 /\\                 order (2 * p EXP k) x = phi (2 * p EXP k))"
#eval thm' "NO_PRIMITIVE_ROOT_MODULO_COMPOSITE" NO_PRIMITIVE_ROOT_MODULO_COMPOSITE
  "|- forall a b.        3 <= a /\\ 3 <= b /\\ coprime (a,b)        ==> ~(exists x. order (a * b) x = phi (a * b))"
#eval thm' "COUNT_ROOTS_MODULO_PRIMITIVE_GEN_ALT" COUNT_ROOTS_MODULO_PRIMITIVE_GEN_ALT
  "|- forall n a k.        ~(n = 0) /\\ (exists x. order n x = phi n)        ==> {x | x < n /\\ coprime (n,x) /\\ (x EXP k == a) (mod n)} HAS_SIZE            (if (a EXP (phi n DIV gcd (k,phi n)) == 1) (mod n)             then gcd (k,phi n)             else 0)"
#eval thm' "POWER_RESIDUE_MODULO_PRIMITIVE_ORDER" POWER_RESIDUE_MODULO_PRIMITIVE_ORDER
  "|- forall n a k.        coprime (n,a) /\\ (exists x. order n x = phi n)        ==> ((exists x. (x EXP k == a) (mod n)) <=>             gcd (k,phi n) divides phi n DIV order n a)"
#eval thm' "COUNT_QUADRATIC_RESIDUES_MODULO_PRIMITIVE" COUNT_QUADRATIC_RESIDUES_MODULO_PRIMITIVE
  "|- forall n.        3 <= n /\\ (exists g. order n g = phi n)        ==> {a | a < n /\\ coprime (n,a) /\\ (exists x. (x EXP 2 == a) (mod n))} HAS_SIZE            phi n DIV 2"
#eval thm' "GENERALIZED_EULER_CRITERION" GENERALIZED_EULER_CRITERION
  "|- forall n a k.        (n = 0 \\/         n = 1 \\/         n = 2 \\/         n = 4 \\/         (exists p k. prime p /\\ 3 <= p /\\ (n = p EXP k \\/ n = 2 * p EXP k))) /\\        coprime (n,a)        ==> ((exists x. (x EXP k == a) (mod n)) <=>             (a EXP (phi n DIV gcd (k,phi n)) == 1) (mod n))"
#eval thm' "POWER_RESIDUE_MODULO_ODD" POWER_RESIDUE_MODULO_ODD
  "|- forall n a k.        ODD n /\\ ~(k = 0) /\\ coprime (n,a)        ==> ((exists x. (x EXP k == a) (mod n)) <=>             (forall p.                  prime p /\\ p divides n                  ==> (a EXP                       ((p EXP (index p n - 1) * (p - 1)) DIV                        gcd (k,p EXP (index p n - 1) * (p - 1))) ==                       1)                      (mod (p EXP index p n))))"
#eval thm' "POWER_RESIDUE_EXISTS" POWER_RESIDUE_EXISTS
  "|- forall n k.        ~(n = 0)        ==> (exists a.                 a < n /\\ coprime (n,a) /\\ (exists x. (x EXP k == a) (mod n)))"
#eval thm' "QUADRATIC_NONRESIDUE_EXISTS" QUADRATIC_NONRESIDUE_EXISTS
  "|- forall n.        (exists a.             a < n /\\ coprime (n,a) /\\ ~(exists x. (x EXP 2 == a) (mod n))) <=>        3 <= n"

end T
