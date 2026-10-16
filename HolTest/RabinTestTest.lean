/- File: HolTest/RabinTestTest.lean
Runtime test suite: Library/rabin_test.ml (HolLibrary/RabinTest.lean, wired by
SessionLibrary/RabinTest.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/rabin_test.ml"`, then `string_of_thm`, newlines joined).
tools/rabin_testdiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.RabinTest.ensureRabinTest

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
open Session SessionLibrary.RabinTest HolLight.Syntax

#eval thm' "RING_DIVIDES_POW_ITERATE" RING_DIVIDES_POW_ITERATE
  "|- forall r p x m k.        integral_domain r /\\        p IN ring_carrier r /\\        x IN ring_carrier r /\\        ring_divides r p (ring_sub r (ring_pow r x m) x) /\\        ~(k = 0) /\\        1 <= m        ==> ring_divides r p (ring_sub r (ring_pow r x (m EXP k)) x)"
#eval thm' "POLY_NONUNIT_DEGREE_GE_1" POLY_NONUNIT_DEGREE_GE_1
  "|- forall f p s.        field f /\\        p IN ring_carrier (poly_ring f s) /\\        ~(p = ring_0 (poly_ring f s)) /\\        ~ring_unit (poly_ring f s) p        ==> 1 <= poly_deg f p"
#eval thm' "RING_DIVIDES_REDUCE" RING_DIVIDES_REDUCE
  "|- forall r p u x m.        u IN ring_carrier r /\\        x IN ring_carrier r /\\        ring_divides r p (ring_sub r u x) /\\        ring_divides r p (ring_sub r (ring_pow r u m) x) /\\        ~(m = 0)        ==> ring_divides r p (ring_sub r (ring_pow r x m) x)"
#eval thm' "FIELD_NONZERO_PRODUCT_PERMUTE" FIELD_NONZERO_PRODUCT_PERMUTE
  "|- forall f x.        field f /\\        FINITE (ring_carrier f) /\\        x IN ring_carrier f /\\        ~(x = ring_0 f)        ==> ring_product f (ring_carrier f DELETE ring_0 f)            (\\y. ring_mul f x y) =            ring_product f (ring_carrier f DELETE ring_0 f) (\\y. y)"
#eval thm' "FINITE_FIELD_ELEMENT_POW" FINITE_FIELD_ELEMENT_POW
  "|- forall f.        field f /\\ FINITE (ring_carrier f)        ==> (forall x.                 x IN ring_carrier f                 ==> ring_pow f x (CARD (ring_carrier f)) = x)"
#eval thm' "QUOTIENT_POLY_RING_FINITE_CARD" QUOTIENT_POLY_RING_FINITE_CARD
  "|- forall f p.        field f /\\        FINITE (ring_carrier f) /\\        ring_irreducible (poly_ring f (:1)) p        ==> field            (quotient_ring (poly_ring f (:1))            (ideal_generated (poly_ring f (:1)) {p})) /\\            FINITE            (ring_carrier            (quotient_ring (poly_ring f (:1))            (ideal_generated (poly_ring f (:1)) {p}))) /\\            CARD            (ring_carrier            (quotient_ring (poly_ring f (:1))            (ideal_generated (poly_ring f (:1)) {p}))) =            CARD (ring_carrier f) EXP poly_deg f p"
#eval thm' "IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN" IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN
  "|- forall f p n.        field f /\\        FINITE (ring_carrier f) /\\        ring_irreducible (poly_ring f (:1)) p /\\        poly_deg f p divides n        ==> ring_divides (poly_ring f (:1)) p            (ring_sub (poly_ring f (:1))             (ring_pow (poly_ring f (:1)) (poly_var f one)             (CARD (ring_carrier f) EXP n))            (poly_var f one))"
#eval thm' "IRREDUCIBLE_DIVIDES_XQ_MINUS_X" IRREDUCIBLE_DIVIDES_XQ_MINUS_X
  "|- forall f p.        field f /\\        FINITE (ring_carrier f) /\\        ring_irreducible (poly_ring f (:1)) p        ==> ring_divides (poly_ring f (:1)) p            (ring_sub (poly_ring f (:1))             (ring_pow (poly_ring f (:1)) (poly_var f one)             (CARD (ring_carrier f) EXP poly_deg f p))            (poly_var f one))"
#eval thm' "FINITE_FIELD_POW_ITERATE" FINITE_FIELD_POW_ITERATE
  "|- forall f x r.        field f /\\ FINITE (ring_carrier f) /\\ x IN ring_carrier f        ==> ring_pow f x (CARD (ring_carrier f) EXP r) = x"
#eval thm' "RING_ENDOMORPHISM_FROBENIUS_ITERATE" RING_ENDOMORPHISM_FROBENIUS_ITERATE
  "|- forall r k.        prime (ring_char r)        ==> ring_endomorphism r (\\x. ring_pow r x (ring_char r EXP k))"
#eval thm' "FIELD_ROOTS_BOUND" FIELD_ROOTS_BOUND
  "|- forall r n.        field r /\\        FINITE (ring_carrier r) /\\        2 <= n /\\        (forall a. a IN ring_carrier r ==> ring_pow r a n = a)        ==> CARD (ring_carrier r) <= n"
#eval thm' "FINITE_FIELD_CARD_CHAR_POWER" FINITE_FIELD_CARD_CHAR_POWER
  "|- forall f.        field f /\\ FINITE (ring_carrier f)        ==> (exists e. ~(e = 0) /\\ CARD (ring_carrier f) = ring_char f EXP e)"
#eval thm' "IRREDUCIBLE_DIVIDES_DEGREE_BOUND" IRREDUCIBLE_DIVIDES_DEGREE_BOUND
  "|- forall f p n.        field f /\\        FINITE (ring_carrier f) /\\        ring_irreducible (poly_ring f (:1)) p /\\        ring_divides (poly_ring f (:1)) p        (ring_sub (poly_ring f (:1))         (ring_pow (poly_ring f (:1)) (poly_var f one)         (CARD (ring_carrier f) EXP n))        (poly_var f one)) /\\        1 <= n        ==> poly_deg f p <= n"
#eval thm' "IRREDUCIBLE_DIVIDES_DEGREE" IRREDUCIBLE_DIVIDES_DEGREE
  "|- forall f p n.        field f /\\        FINITE (ring_carrier f) /\\        ring_irreducible (poly_ring f (:1)) p /\\        ring_divides (poly_ring f (:1)) p        (ring_sub (poly_ring f (:1))         (ring_pow (poly_ring f (:1)) (poly_var f one)         (CARD (ring_carrier f) EXP n))        (poly_var f one))        ==> poly_deg f p divides n"
#eval thm' "RABIN_IRREDUCIBILITY_NECESSARY" RABIN_IRREDUCIBILITY_NECESSARY
  "|- forall f p n.        field f /\\        FINITE (ring_carrier f) /\\        p IN ring_carrier (poly_ring f (:1)) /\\        poly_deg f p = n /\\        ~(n = 0) /\\        ring_irreducible (poly_ring f (:1)) p        ==> ring_divides (poly_ring f (:1)) p            (ring_sub (poly_ring f (:1))             (ring_pow (poly_ring f (:1)) (poly_var f one)             (CARD (ring_carrier f) EXP n))            (poly_var f one)) /\\            (forall q.                 prime q /\\ q divides n                 ==> ring_coprime (poly_ring f (:1))                     (p,                      ring_sub (poly_ring f (:1))                      (ring_pow (poly_ring f (:1)) (poly_var f one)                      (CARD (ring_carrier f) EXP (n DIV q)))                      (poly_var f one)))"
#eval thm' "RABIN_IRREDUCIBILITY_SUFFICIENT" RABIN_IRREDUCIBILITY_SUFFICIENT
  "|- forall f p n.        field f /\\        FINITE (ring_carrier f) /\\        p IN ring_carrier (poly_ring f (:1)) /\\        ~(p = ring_0 (poly_ring f (:1))) /\\        poly_deg f p = n /\\        ~(n = 0) /\\        ring_divides (poly_ring f (:1)) p        (ring_sub (poly_ring f (:1))         (ring_pow (poly_ring f (:1)) (poly_var f one)         (CARD (ring_carrier f) EXP n))        (poly_var f one)) /\\        (forall q.             prime q /\\ q divides n             ==> ring_coprime (poly_ring f (:1))                 (p,                  ring_sub (poly_ring f (:1))                  (ring_pow (poly_ring f (:1)) (poly_var f one)                  (CARD (ring_carrier f) EXP (n DIV q)))                  (poly_var f one)))        ==> ring_irreducible (poly_ring f (:1)) p"
#eval thm' "RABIN_IRREDUCIBILITY_TEST" RABIN_IRREDUCIBILITY_TEST
  "|- forall f p n.        field f /\\        FINITE (ring_carrier f) /\\        p IN ring_carrier (poly_ring f (:1)) /\\        ~(p = ring_0 (poly_ring f (:1))) /\\        ~ring_unit (poly_ring f (:1)) p /\\        poly_deg f p = n /\\        ~(n = 0)        ==> (ring_irreducible (poly_ring f (:1)) p <=>             ring_divides (poly_ring f (:1)) p             (ring_sub (poly_ring f (:1))              (ring_pow (poly_ring f (:1)) (poly_var f one)              (CARD (ring_carrier f) EXP n))             (poly_var f one)) /\\             (forall q.                  prime q /\\ q divides n                  ==> ring_coprime (poly_ring f (:1))                      (p,                       ring_sub (poly_ring f (:1))                       (ring_pow (poly_ring f (:1)) (poly_var f one)                       (CARD (ring_carrier f) EXP (n DIV q)))                       (poly_var f one))))"

end T
