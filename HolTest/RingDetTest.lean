/- File: HolTest/RingDetTest.lean
Runtime test suite: Library/ring_det.ml (HolLibrary/RingDet.lean, wired by
SessionLibrary/RingDet.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/ring_det.ml"`, then `string_of_thm`).
tools/ringdetdiff/check.sh compares far more structurally: all 270 theorems,
the constants and definitions and all load messages. -/

import HolTest.CommonTest
import SessionLibrary.RingDet

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.RingDet.ensureRingDet

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

namespace K
open Session SessionLibrary.RingDet HolLight.Syntax

-- Theorems and definitions from across the file.
#eval thm' "RING_SIGN_COMPOSE" RING_SIGN_COMPOSE
  "|- forall r p q. permutation p /\\ permutation q ==> ring_sign r (p o q) = ring_mul r (ring_sign r p) (ring_sign r q)"
#eval thm' "RING_DET_TRANSP" RING_DET_TRANSP
  "|- forall r s f. FINITE s ==> ring_det r s (\\i j. f j i) = ring_det r s f"
#eval thm' "RING_DET_MUL" RING_DET_MUL
  "|- forall r s a b. FINITE s /\\ (forall i j. i IN s /\\ j IN s ==> a i j IN ring_carrier r) /\\ (forall i j. i IN s /\\ j IN s ==> b i j IN ring_carrier r) ==> ring_det r s (\\i j. ring_sum r s (\\k. ring_mul r (a i k) (b k j))) = ring_mul r (ring_det r s a) (ring_det r s b)"
#eval thm' "RING_DET_COFACTOR_EXPANSION" RING_DET_COFACTOR_EXPANSION
  "|- forall r s f i. FINITE s /\\ i IN s /\\ (forall i j. i IN s /\\ j IN s ==> f i j IN ring_carrier r) ==> ring_det r s f = ring_sum r s (\\j. ring_mul r (f i j) (ring_cofactor r s f i j))"
#eval thm' "RING_DET_UPPERTRIANGULAR" RING_DET_UPPERTRIANGULAR
  "|- forall r s f. FINITE s /\\ (forall i j. i IN s /\\ j IN s /\\ j < i ==> f i j = ring_0 r) ==> ring_det r s f = ring_product r s (\\i. f i i)"
#eval thm' "RING_CHARPOLY_MONIC" RING_CHARPOLY_MONIC
  "|- forall r s f. FINITE s /\\ (forall i j. i IN s /\\ j IN s ==> f i j IN ring_carrier r) ==> monic r (ring_charpoly r s f) /\\ (~(ring_1 r = ring_0 r) ==> poly_deg r (ring_charpoly r s f) = CARD s)"
#eval thm' "RING_DET_VANDERMONDE" RING_DET_VANDERMONDE
  "|- forall r n x. (forall i. i < n ==> x i IN ring_carrier r) ==> ring_det r {i | i < n} (\\i j. ring_pow r (x i) j) = ring_product r {j | j < n} (\\j. ring_product r {i | i < j} (\\i. ring_sub r (x j) (x i)))"
#eval thm' "ALGEBRA_TRACE_FREE_BASIS" ALGEBRA_TRACE_FREE_BASIS
  "|- forall h k l n g x. ring_homomorphism (k,l) h /\\ free_basis (k,l) h n g /\\ x IN ring_carrier l ==> algebra_trace (k,l) h x = ring_sum k {i | i < n} (\\i. mul_matrix (k,l) h n g x i i)"
#eval thm' "ALGEBRA_NORM_MUL" ALGEBRA_NORM_MUL
  "|- forall h k l x y. ring_homomorphism (k,l) h /\\ x IN ring_carrier l /\\ y IN ring_carrier l ==> algebra_norm (k,l) h (ring_mul l x y) = ring_mul k (algebra_norm (k,l) h x) (algebra_norm (k,l) h y)"
#eval thm' "BASIS_DISCRIMINANT_NILPOTENT" BASIS_DISCRIMINANT_NILPOTENT
  "|- forall h k l n g x. integral_domain k /\\ ring_homomorphism (k,l) h /\\ free_basis (k,l) h n g /\\ ring_nilpotent l x /\\ ~(x = ring_0 l) ==> basis_discriminant (k,l) h n g = ring_0 k"
#eval thm' "poly_resultant" poly_resultant
  "|- forall p q r. poly_resultant r p q = ring_det r {i | i < poly_deg r p + poly_deg r q} (\\i j. if i < poly_deg r q then if i <= j /\\ j <= i + poly_deg r p then coeff ((poly_deg r p + i) - j) p else ring_0 r else if i - poly_deg r q <= j /\\ j <= i then coeff (i - j) q else ring_0 r)"
#eval thm' "POLY_RESULTANT_SYM" POLY_RESULTANT_SYM
  "|- forall r p q. poly_resultant r q p = ring_mul r (ring_pow r (ring_neg r (ring_1 r)) (poly_deg r p * poly_deg r q)) (poly_resultant r p q)"
#eval thm' "POLY_RESULTANT_X_MINUS" POLY_RESULTANT_X_MINUS
  "|- forall r c q. c IN ring_carrier r /\\ q IN ring_carrier (poly_ring r (:1)) ==> poly_resultant r (poly_sub r (poly_var r one) (poly_const r c)) q = poly_eval r q c"
#eval thm' "POLY_RESULTANT_EQ_0" POLY_RESULTANT_EQ_0
  "|- forall k p q. field k /\\ p IN ring_carrier (poly_ring k (:1)) /\\ q IN ring_carrier (poly_ring k (:1)) /\\ ~(p = poly_0 k /\\ q = poly_0 k) ==> (poly_resultant k p q = ring_0 k <=> ~ring_coprime (poly_ring k (:1)) (p,q))"
#eval thm' "POLY_DISCRIMINANT_ROOTS" POLY_DISCRIMINANT_ROOTS
  "|- forall r p a x. p IN ring_carrier (poly_ring r (:1)) /\\ a IN ring_carrier r /\\ (forall i. i < poly_deg r p ==> x i IN ring_carrier r) /\\ p = ring_mul (poly_ring r (:1)) (poly_const r a) (ring_product (poly_ring r (:1)) {i | i < poly_deg r p} (\\i. poly_sub r (poly_var r one) (poly_const r (x i)))) ==> poly_discriminant r p = ring_mul r (ring_pow r a (2 * poly_deg r p - 2)) (ring_product r {i,j | i < j /\\ j < poly_deg r p} (\\(i,j). ring_pow r (ring_sub r (x i) (x j)) 2))"
#eval thm' "POLY_DISCRIMINANT_EQ_0" POLY_DISCRIMINANT_EQ_0
  "|- forall k p. field k /\\ p IN ring_carrier (poly_ring k (:1)) /\\ 1 <= poly_deg k p ==> (poly_discriminant k p = ring_0 k <=> ~poly_separable k p)"

-- A proof using the library at run time.
#eval check "prove with RING_DET_TRANSP"
  (HolLight.prove r"!r f:num->num->A. ring_det r {i | i < 2} (\i j. f j i) = ring_det r {i | i < 2} f"
     (SIMP_TAC [RING_DET_TRANSP, FINITE_NUMSEG_LT])).run
  "|- forall r f. ring_det r {i | i < 2} (\\i j. f j i) = ring_det r {i | i < 2} f"

end K
