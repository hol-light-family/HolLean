/- File: HolTest/FiniteFieldsTest.lean
Runtime test suite: Library/finite_fields.ml (HolLibrary/FiniteFields.lean, wired by
SessionLibrary/FiniteFields.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/finite_fields.ml"`, then `string_of_thm`, newlines joined).
tools/finitefieldsdiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary.FiniteFields

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.FiniteFields.ensureFiniteFields

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
open Session SessionLibrary.FiniteFields HolLight.Syntax

#eval thm' "FINITE_FIELD_ELEMENT_POW" FINITE_FIELD_ELEMENT_POW
  "|- forall f.        field f /\\ FINITE (ring_carrier f)        ==> (forall x.                 x IN ring_carrier f                 ==> ring_pow f x (CARD (ring_carrier f)) = x)"
#eval thm' "FINITE_FIELD_CARD_CHAR_POWER" FINITE_FIELD_CARD_CHAR_POWER
  "|- forall f.        field f /\\ FINITE (ring_carrier f)        ==> (exists e. ~(e = 0) /\\ CARD (ring_carrier f) = ring_char f EXP e)"
#eval thm' "FINITE_FIELD_ROOTS_OF_UNITY" FINITE_FIELD_ROOTS_OF_UNITY
  "|- forall k d.        field k /\\ FINITE (ring_carrier k)        ==> ({x | x IN ring_carrier k /\\ ring_pow k x d = ring_1 k} HAS_SIZE d <=>             d divides CARD (ring_carrier k) - 1)"
#eval thm' "FINITE_FIELD_CYCLIC_UNIT_GROUP" FINITE_FIELD_CYCLIC_UNIT_GROUP
  "|- forall k.        field k /\\ FINITE (ring_carrier k) ==> cyclic_group (unit_group k)"
#eval thm' "FINITE_FIELD_HOMOMORPHISM_IMAGE" FINITE_FIELD_HOMOMORPHISM_IMAGE
  "|- forall h k l.        field k /\\        FINITE (ring_carrier k) /\\        integral_domain l /\\        ring_homomorphism (k,l) h        ==> IMAGE h (ring_carrier k) =            {x | x IN ring_carrier l /\\                 ring_pow l x (CARD (ring_carrier k)) = x}"
#eval thm' "ALGEBRA_NORM_FINITE_FIELD_POW" ALGEBRA_NORM_FINITE_FIELD_POW
  "|- forall h k l x.        field_extension (k,l) h /\\        FINITE (ring_carrier l) /\\        x IN ring_carrier l        ==> h (algebra_norm (k,l) h x) =            ring_pow l x            ((CARD (ring_carrier l) - 1) DIV (CARD (ring_carrier k) - 1))"
#eval thm' "ALGEBRA_NORM_SURJECTIVE_FINITE" ALGEBRA_NORM_SURJECTIVE_FINITE
  "|- forall h k l.        field_extension (k,l) h /\\ FINITE (ring_carrier l)        ==> IMAGE (algebra_norm (k,l) h) (ring_carrier l DELETE ring_0 l) =            ring_carrier k DELETE ring_0 k"
#eval thm' "ALGEBRA_TRACE_FIBRE_FINITE" ALGEBRA_TRACE_FIBRE_FINITE
  "|- forall h k l a.        field_extension (k,l) h /\\        FINITE (ring_carrier l) /\\        a IN ring_carrier k        ==> {x | x IN ring_carrier l /\\ algebra_trace (k,l) h x = a} HAS_SIZE            CARD (ring_carrier l) DIV CARD (ring_carrier k)"
#eval thm' "HILBERT_90_FINITE_FIELD" HILBERT_90_FINITE_FIELD
  "|- forall h k l x.        field_extension (k,l) h /\\        FINITE (ring_carrier l) /\\        x IN ring_carrier l        ==> (algebra_norm (k,l) h x = ring_1 k <=>             (exists y.                  y IN ring_carrier l /\\                  ~(y = ring_0 l) /\\                  x = ring_pow l y (CARD (ring_carrier k) - 1)))"
#eval thm' "FINITE_FIELD_POW_CARD_EXP" FINITE_FIELD_POW_CARD_EXP
  "|- forall h k l n.        field_extension (k,l) h /\\ FINITE (ring_carrier l)        ==> ((forall x.                  x IN ring_carrier l                  ==> ring_pow l x (CARD (ring_carrier k) EXP n) = x) <=>             extension_degree (k,l) h divides n)"
#eval thm' "FINITE_FIELD_IRREDUCIBLE_ROOTS" FINITE_FIELD_IRREDUCIBLE_ROOTS
  "|- forall h k l p x.        field_extension (k,l) h /\\        FINITE (ring_carrier k) /\\        ring_irreducible (poly_ring k (:1)) p /\\        x IN ring_carrier l /\\        poly_eval l (h o p) x = ring_0 l        ==> {y | y IN ring_carrier l /\\ poly_eval l (h o p) y = ring_0 l} =            IMAGE (\\i. ring_pow l x (CARD (ring_carrier k) EXP i))            {i | i < poly_deg k p} /\\            {y | y IN ring_carrier l /\\ poly_eval l (h o p) y = ring_0 l} HAS_SIZE            poly_deg k p"
#eval thm' "X_POW_SUB_X_FINITE_FIELD" X_POW_SUB_X_FINITE_FIELD
  "|- forall k n.        field k /\\ FINITE (ring_carrier k) /\\ ~(n = 0)        ==> poly_sub k            (poly_pow k (poly_var k one) (CARD (ring_carrier k) EXP n))            (poly_var k one) IN            ring_carrier (poly_ring k (:1)) /\\            ~(poly_sub k              (poly_pow k (poly_var k one) (CARD (ring_carrier k) EXP n))              (poly_var k one) =              poly_0 k) /\\            poly_deg k            (poly_sub k             (poly_pow k (poly_var k one) (CARD (ring_carrier k) EXP n))            (poly_var k one)) =            CARD (ring_carrier k) EXP n /\\            monic k            (poly_sub k             (poly_pow k (poly_var k one) (CARD (ring_carrier k) EXP n))            (poly_var k one)) /\\            poly_separable k            (poly_sub k             (poly_pow k (poly_var k one) (CARD (ring_carrier k) EXP n))            (poly_var k one))"
#eval thm' "FINITE_FIELD_IRREDUCIBLE_COUNT" FINITE_FIELD_IRREDUCIBLE_COUNT
  "|- forall k n.        field k /\\ FINITE (ring_carrier k) /\\ ~(n = 0)        ==> nsum {d | d divides n}            (\\d.                 d *                 CARD                 {p | p IN ring_carrier (poly_ring k (:1)) /\\                      monic k p /\\                      ring_irreducible (poly_ring k (:1)) p /\\                      poly_deg k p = d}) =            CARD (ring_carrier k) EXP n"
#eval thm' "FINITE_FIELD_IRREDUCIBLE_EXISTS" FINITE_FIELD_IRREDUCIBLE_EXISTS
  "|- forall k n.        field k /\\ FINITE (ring_carrier k) /\\ ~(n = 0)        ==> (exists p.                 p IN ring_carrier (poly_ring k (:1)) /\\                 monic k p /\\                 ring_irreducible (poly_ring k (:1)) p /\\                 poly_deg k p = n)"
#eval thm' "FINITE_FIELD_POW_ITERATE" FINITE_FIELD_POW_ITERATE
  "|- forall k x n.        field k /\\ FINITE (ring_carrier k) /\\ x IN ring_carrier k        ==> ring_pow k x (CARD (ring_carrier k) EXP n) = x"
#eval thm' "FINITE_FIELD_IRREDUCIBLE_ROOT_EXISTS" FINITE_FIELD_IRREDUCIBLE_ROOT_EXISTS
  "|- forall k l h p.        field_extension (k,l) h /\\        FINITE (ring_carrier l) /\\        p IN ring_carrier (poly_ring k (:1)) /\\        ring_irreducible (poly_ring k (:1)) p /\\        poly_deg k p divides extension_degree (k,l) h        ==> (exists x.                 x IN ring_carrier l /\\ poly_eval l (h o p) x = ring_0 l)"
#eval thm' "FINITE_GALOIS_SUBFIELDS_FINITE_FIELD" FINITE_GALOIS_SUBFIELDS_FINITE_FIELD
  "|- forall h k l e.        FINITE (ring_carrier k) /\\        field l /\\        e IN finite_galois_subfields (k,l) h        ==> FINITE e /\\            ~(extension_degree (k,subfield_generated l e) h = 0) /\\            e =            {x | x IN ring_carrier l /\\                 ring_pow l x                 (CARD (ring_carrier k) EXP                  extension_degree (k,subfield_generated l e) h) =                 x}"
#eval thm' "FINITE_FIELD_LAYER_POW" FINITE_FIELD_LAYER_POW
  "|- forall l q n x.        x IN ring_carrier l /\\ ring_pow l x (q EXP n) = x        ==> (forall a. ring_pow l x (q EXP (a * n)) = x) /\\            (forall j.                 ~(n = 0)                 ==> ring_pow l x (q EXP j) = ring_pow l x (q EXP (j MOD n))) /\\            (forall m. ring_pow l (ring_pow l x m) (q EXP n) = ring_pow l x m)"
#eval thm' "GALOIS_GROUP_FINITE_FIELD_EXPONENT" GALOIS_GROUP_FINITE_FIELD_EXPONENT
  "|- forall h k l n f.        FINITE (ring_carrier k) /\\        field_extension (k,l) h /\\        algebraically_closed_field l /\\        ~(n = 0) /\\        f IN group_carrier (galois_group (k,l) h)        ==> (existsunique j.                 j < n /\\                 (forall x.                      x IN ring_carrier l /\\                      ring_pow l x (CARD (ring_carrier k) EXP n) = x                      ==> f x = ring_pow l x (CARD (ring_carrier k) EXP j)))"
#eval thm' "RABIN_IRREDUCIBILITY_SUFFICIENT" RABIN_IRREDUCIBILITY_SUFFICIENT
  "|- forall k p n.        field k /\\        FINITE (ring_carrier k) /\\        p IN ring_carrier (poly_ring k (:1)) /\\        ~(p = ring_0 (poly_ring k (:1))) /\\        poly_deg k p = n /\\        ~(n = 0) /\\        ring_divides (poly_ring k (:1)) p        (ring_sub (poly_ring k (:1))         (ring_pow (poly_ring k (:1)) (poly_var k one)         (CARD (ring_carrier k) EXP n))        (poly_var k one)) /\\        (forall q.             prime q /\\ q divides n             ==> ring_coprime (poly_ring k (:1))                 (p,                  ring_sub (poly_ring k (:1))                  (ring_pow (poly_ring k (:1)) (poly_var k one)                  (CARD (ring_carrier k) EXP (n DIV q)))                  (poly_var k one)))        ==> ring_irreducible (poly_ring k (:1)) p"

end T
