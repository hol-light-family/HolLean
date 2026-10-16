/- File: HolTest/JacobiTest.lean
Runtime test suite: Library/jacobi.ml (HolLibrary/Jacobi.lean, wired by
SessionLibrary/Jacobi.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/jacobi.ml"`, then `string_of_thm`, newlines joined).
tools/jacobidiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Jacobi.ensureJacobi

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
open Session SessionLibrary.Jacobi HolLight.Syntax

#eval thm' "COPRIME_IPRODUCT" COPRIME_IPRODUCT
  "|- forall s a n.        (forall i. i IN s ==> coprime (n,a i)) ==> coprime (n,iproduct s a)"
#eval thm' "JACOBI_PRIME" JACOBI_PRIME
  "|- forall a p.        prime p        ==> jacobi (a,p) =            (if p divides a             then &0             else if exists x. (x EXP 2 == a) (mod p) then &1 else -- &1)"
#eval thm' "JACOBI_1" JACOBI_1
  "|- (forall n. jacobi (1,n) = &1) /\\ (forall a. jacobi (a,1) = &1)"
#eval thm' "JACOBI_EULER_ALT" JACOBI_EULER_ALT
  "|- forall a p.        prime p        ==> (jacobi (a,p) == &a pow (if p = 2 then 1 else (p - 1) DIV 2))            (mod &p)"
#eval thm' "JACOBI_EXP_2" JACOBI_EXP_2
  "|- forall a k. jacobi (a,2 EXP k) = (if k = 0 then &1 else &(a MOD 2))"
#eval thm' "JACOBI_MOD_GEN" JACOBI_MOD_GEN
  "|- forall a m n. n divides m ==> jacobi (a MOD m,n) = jacobi (a,n)"
#eval thm' "JACOBI_GAUSS_LEMMA" JACOBI_GAUSS_LEMMA
  "|- forall a p.        prime p /\\ ~(p = 2)        ==> jacobi (a,p) =            (if coprime (a,p)             then -- &1 pow                  CARD                  {x | x IN 1..(p - 1) DIV 2 /\\ (p - 1) DIV 2 < (a * x) MOD p}             else &0)"
#eval thm' "JACOBI_EQ_1" JACOBI_EQ_1
  "|- forall n a.        coprime (a,n) /\\ (exists x. (x EXP 2 == a) (mod n))        ==> jacobi (a,n) = &1"
#eval thm' "INT_JACOBI_NUMS" INT_JACOBI_NUMS
  "|- forall a n.        int_jacobi (&a,&n) = (if n = 0 /\\ a = 1 then &0 else jacobi (a,n))"
#eval thm' "INT_JACOBI_REM" INT_JACOBI_REM
  "|- forall a n. int_jacobi (a rem n,n) = int_jacobi (a,n)"
#eval thm' "INT_JACOBI_RPOW" INT_JACOBI_RPOW
  "|- forall a n k. int_jacobi (a,n pow k) = int_jacobi (a,n) pow k"
#eval thm' "INT_JACOBI_MINUS1" INT_JACOBI_MINUS1
  "|- forall n.        ~(&2 divides n)        ==> int_jacobi (-- &1,n) =            (if (abs n == &1) (mod &4) then &1 else -- &1)"
#eval thm' "INT_JACOBI_SQUARED" INT_JACOBI_SQUARED
  "|- (forall a n.         int_jacobi (a pow 2,n) =         (if coprime (a,n) /\\ ~(n = &0) then &1 else &0)) /\\    (forall a n.         int_jacobi (a,n pow 2) =         (if coprime (a,n) /\\ ~(n = &0) then &1 else &0))"

end T
