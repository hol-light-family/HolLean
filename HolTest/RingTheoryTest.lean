/- File: HolTest/RingTheoryTest.lean
Runtime test suite: Library/ringtheory.ml (HolLibrary/RingTheory.lean,
wired by SessionLibrary/RingTheory.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/ringtheory.ml"`, `set_margin 1000`, then `string_of_thm` or
the failure message).  tools/ringtheorydiff/check.sh compares far more
structurally: all 2153 theorems, the conversion results in convs.txt, the
constants and definitions and all load messages. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.RingTheory.ensureRingTheory

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

namespace K
open Session SessionLibrary.RingTheory HolLight.Syntax

-- Theorems from across the file.
#eval thm' "RING_ADD_SYM" RING_ADD_SYM
  "|- forall r x y. x IN ring_carrier r /\\ y IN ring_carrier r ==> ring_add r x y = ring_add r y x"
#eval thm' "RING_MUL_LID" RING_MUL_LID
  "|- forall r x. x IN ring_carrier r ==> ring_mul r (ring_1 r) x = x"
#eval thm' "INTEGRAL_DOMAIN_MUL_EQ_0" INTEGRAL_DOMAIN_MUL_EQ_0
  "|- forall r a b. integral_domain r /\\ a IN ring_carrier r /\\ b IN ring_carrier r ==> (ring_mul r a b = ring_0 r <=> a = ring_0 r \\/ b = ring_0 r)"
#eval thm' "RING_CHAR_EQ_0" RING_CHAR_EQ_0
  "|- forall r. ring_char r = 0 <=> (forall n. ring_of_num r n = ring_0 r <=> n = 0)"
#eval thm' "PID_IMP_UFD" PID_IMP_UFD
  "|- forall r. PID r ==> UFD r"
#eval thm' "REAL_RING_CLAUSES" REAL_RING_CLAUSES
  "|- ring_carrier real_ring = (:real) /\\ ring_0 real_ring = &0 /\\ ring_1 real_ring = &1 /\\ ring_neg real_ring = (--) /\\ ring_add real_ring = (+) /\\ ring_mul real_ring = (*)"
#eval thm' "MONOMIAL_MUL_SYM" MONOMIAL_MUL_SYM
  "|- forall m1 m2. monomial_mul m1 m2 = monomial_mul m2 m1"
#eval thm' "POLY_DEG_MUL" POLY_DEG_MUL
  "|- forall r p q. integral_domain r /\\ ring_polynomial r p /\\ ring_polynomial r q /\\ (p = poly_0 r <=> q = poly_0 r) ==> poly_deg r (poly_mul r p q) = poly_deg r p + poly_deg r q"
#eval thm' "UFD_POLY_RING" UFD_POLY_RING
  "|- forall r s. UFD r ==> UFD (poly_ring r s)"
#eval thm' "NOETHERIAN_POLY_RING" NOETHERIAN_POLY_RING
  "|- forall r s. noetherian_ring (poly_ring r s) <=> noetherian_ring r /\\ (FINITE s \\/ trivial_ring r)"
#eval thm' "EISENSTEIN_IRREDUCIBILITY" EISENSTEIN_IRREDUCIBILITY
  "|- forall r p f. UFD r /\\ ring_prime r p /\\ f IN ring_carrier (poly_ring r (:1)) /\\ 1 <= poly_deg r f /\\ ~ring_divides r p (coeff (poly_deg r f) f) /\\ (forall k. k < poly_deg r f ==> ring_divides r p (coeff k f)) /\\ ~ring_divides r (ring_pow r p 2) (f monomial_1) /\\ (forall q. ring_prime r q ==> ~ring_divides (poly_ring r (:1)) (poly_const r q) f) ==> ring_irreducible (poly_ring r (:1)) f"
#eval thm' "FIELD_INV_EQ_0" FIELD_INV_EQ_0
  "|- forall f x. field f /\\ x IN ring_carrier f ==> (ring_inv f x = ring_0 f <=> x = ring_0 f)"
#eval thm' "FROBENIUS_FIXED" FROBENIUS_FIXED
  "|- forall r. integral_domain r /\\ prime (ring_char r) ==> {x | x IN ring_carrier r /\\ ring_pow r x (ring_char r) = x} = {ring_of_int r n | n IN (:int)}"
#eval thm' "RING_ORDER_MUL" RING_ORDER_MUL
  "|- forall r x y. x IN ring_carrier r /\\ y IN ring_carrier r /\\ coprime (ring_order r x,ring_order r y) ==> ring_order r (ring_mul r x y) = ring_order r x * ring_order r y"
#eval thm' "POLY_ROOT_BOUND" POLY_ROOT_BOUND
  "|- forall r p. integral_domain r /\\ p IN ring_carrier (poly_ring r (:1)) /\\ ~(p = ring_0 (poly_ring r (:1))) ==> FINITE {x | x IN ring_carrier r /\\ poly_eval r p x = ring_0 r} /\\ CARD {x | x IN ring_carrier r /\\ poly_eval r p x = ring_0 r} <= poly_deg r p"

-- The decision procedures and tactics.
#eval check "RING_RULE" (onTerm RING_RULE
  "!r x y:A. x IN ring_carrier r /\\ y IN ring_carrier r ==> ring_mul r (ring_add r x y) (ring_add r x y) = ring_add r (ring_pow r x 2) (ring_add r (ring_mul r (ring_of_num r 2) (ring_mul r x y)) (ring_pow r y 2))")
  "|- forall r x y. x IN ring_carrier r /\\ y IN ring_carrier r ==> ring_mul r (ring_add r x y) (ring_add r x y) = ring_add r (ring_pow r x 2) (ring_add r (ring_mul r (ring_of_num r 2) (ring_mul r x y)) (ring_pow r y 2))"
#eval check "INTEGRAL_DOMAIN_RULE" (onTerm INTEGRAL_DOMAIN_RULE
  "!r x y:A. integral_domain r /\\ x IN ring_carrier r /\\ y IN ring_carrier r /\\ ring_mul r x x = ring_mul r y y ==> x = y \\/ x = ring_neg r y")
  "|- forall r x y. integral_domain r /\\ x IN ring_carrier r /\\ y IN ring_carrier r /\\ ring_mul r x x = ring_mul r y y ==> x = y \\/ x = ring_neg r y"
#eval check "FIELD_TAC"
  (HolLight.prove r"!f x:A. field f /\ x IN ring_carrier f /\ ~(x = ring_0 f) ==> ring_mul f x (ring_inv f x) = ring_1 f"
     FIELD_TAC).run
  "|- forall f x. field f /\\ x IN ring_carrier f /\\ ~(x = ring_0 f) ==> ring_mul f x (ring_inv f x) = ring_1 f"

-- The conversions.
#eval check "INTEGER_MOD_RING_RED_CONV mul"
  (onTerm INTEGER_MOD_RING_RED_CONV "ring_mul (integer_mod_ring 7) (&3) (&5)")
  "|- ring_mul (integer_mod_ring 7) (&3) (&5) = &1"
#eval check "INTEGER_MOD_RING_RED_CONV inv"
  (onTerm INTEGER_MOD_RING_RED_CONV "ring_inv (integer_mod_ring 7) (&3)")
  "|- ring_inv (integer_mod_ring 7) (&3) = &5"
-- 3 is not a unit mod 6, so its ring_inv is ring_0
#eval check "INTEGER_MOD_RING_RED_CONV inv nonunit"
  (onTerm INTEGER_MOD_RING_RED_CONV "ring_inv (integer_mod_ring 6) (&3)")
  "|- ring_inv (integer_mod_ring 6) (&3) = &0"
#eval check "RING_PULL_DIV_CONV" (do
  let asm ← ["x IN ring_carrier (f:A ring)", "y IN ring_carrier (f:A ring)", "field (f:A ring)"].mapM
    (fun s => do match ← HolCore.Parser.parse_term s with
      | .ok t => match HolCore.Kernel.ASSUME t with
        | .ok th => pure th
        | .error e => throw (IO.userError e)
      | .error e => throw (IO.userError e))
  onTerm (RING_PULL_DIV_CONV asm) "ring_pow (f:A ring) (ring_div f (x:A) y) 2")
  "field f, x IN ring_carrier f, y IN ring_carrier f |- ring_pow f (ring_div f x y) 2 = ring_div f (ring_pow f x 2) (ring_pow f y 2)"
-- the pulled-up goal needs RING_RULE, not just RING_CARRIER_TAC
#eval check "RING_PULL_DIV_TAC fail"
  (HolLight.prove r"!f x y:A. field f /\ x IN ring_carrier f /\ y IN ring_carrier f /\ ~(y = ring_0 f) ==> ring_add f (ring_div f x y) (ring_1 f) = ring_div f (ring_add f x y) y"
     (REPEAT STRIP_TAC THEN RING_PULL_DIV_TAC THEN RING_CARRIER_TAC)).run
  "FAIL NO_TAC"

end K
