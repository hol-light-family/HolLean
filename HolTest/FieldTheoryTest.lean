/- File: HolTest/FieldTheoryTest.lean
Runtime test suite: Library/fieldtheory.ml (HolLibrary/FieldTheory.lean, wired by
SessionLibrary/FieldTheory.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/fieldtheory.ml"`, then `string_of_thm`, newlines joined).
tools/fieldtheorydiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.FieldTheory.ensureFieldTheory

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
open Session SessionLibrary.FieldTheory HolLight.Syntax

#eval thm' "subfield_of" subfield_of
  "|- forall r s.        s subfield_of r <=> s subring_of r /\\ field (subring_generated r s)"
#eval thm' "CARRIER_SUBFIELD_GENERATED_SUBFIELD" CARRIER_SUBFIELD_GENERATED_SUBFIELD
  "|- forall r s. s subfield_of r ==> ring_carrier (subfield_generated r s) = s"
#eval thm' "SUBFIELD_GENERATED_INC" SUBFIELD_GENERATED_INC
  "|- forall r s x.        s SUBSET ring_carrier r /\\ x IN s        ==> x IN ring_carrier (subfield_generated r s)"
#eval thm' "RING_INV_SUBFIELD_GENERATED" RING_INV_SUBFIELD_GENERATED
  "|- forall r s x.        field (subfield_generated r s) /\\        x IN ring_carrier (subfield_generated r s) /\\        ~(x = ring_0 r)        ==> ring_inv (subfield_generated r s) x = ring_inv r x"
#eval thm' "FIELD_EXTENSION_INTO_SUBRING_GENERATED" FIELD_EXTENSION_INTO_SUBRING_GENERATED
  "|- forall h k l s.        field_extension (k,l) h /\\        s subfield_of l /\\        IMAGE h (ring_carrier k) SUBSET s        ==> field_extension (k,subring_generated l s) h"
#eval thm' "RING_SPAN_UNION" RING_SPAN_UNION
  "|- forall h k l s t.        ring_homomorphism (k,l) h        ==> ring_span (k,l) h (s UNION t) =            {ring_add l x y | x,y | x IN ring_span (k,l) h s /\\                                    y IN ring_span (k,l) h t}"
#eval thm' "RING_INDEPENDENT_FINITARY" RING_INDEPENDENT_FINITARY
  "|- forall h k l s.        ring_independent (k,l) h s <=>        s SUBSET ring_carrier l /\\        (forall t. FINITE t /\\ t SUBSET s ==> ring_independent (k,l) h t)"
#eval thm' "FINITE_IMP_FINITELY_GENERATED_EXTENSION" FINITE_IMP_FINITELY_GENERATED_EXTENSION
  "|- forall h k l.        finite_extension (k,l) h ==> finitely_generated_extension (k,l) h"
#eval thm' "RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN" RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN
  "|- forall h k l p a.        field k /\\        ring_homomorphism (k,l) h /\\        a IN ring_carrier l /\\        p IN ring_carrier (poly_ring k (:1)) /\\        ~(p = ring_0 (poly_ring k (:1))) /\\        poly_extend (k,l) h (\\v. a) p = ring_0 l        ==> ring_carrier            (subring_generated l (a INSERT IMAGE h (ring_carrier k))) =            ring_span (k,l) h {ring_pow l a n | n < poly_deg k p}"
#eval thm' "ALGEBRAIC_OVER_POW" ALGEBRAIC_OVER_POW
  "|- forall h k l a n.        field_extension (k,l) h /\\ algebraic_over (k,l) h a        ==> algebraic_over (k,l) h (ring_pow l a n)"
#eval thm' "ALGEBRAIC_SPAN_RESTRICT" ALGEBRAIC_SPAN_RESTRICT
  "|- forall h k l s.        algebraic_span (k,l) h s =        algebraic_span (k,l) h (ring_carrier l INTER s)"
#eval thm' "algebraic_matroid" algebraic_matroid
  "|- forall k l h.        algebraic_matroid (k,l) h =        matroid (ring_carrier l,algebraic_span (k,l) h)"
#eval thm' "TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_INDEPENDENT" TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_INDEPENDENT
  "|- forall h k l s.        transcendence_basis (k,l) h s ==> algebraically_independent (k,l) h s"
#eval thm' "ALGEBRAIC_CLOSURE_UNIQUE" ALGEBRAIC_CLOSURE_UNIQUE
  "|- forall k l l' f g.        algebraic_extension (k,l) f /\\        algebraically_closed_field l /\\        algebraic_extension (k,l') g /\\        algebraically_closed_field l'        ==> l isomorphic_ring l'"

end T
