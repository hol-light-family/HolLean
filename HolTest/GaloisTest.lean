/- File: HolTest/GaloisTest.lean
Runtime test suite: Library/galois.ml (HolLibrary/Galois.lean, wired by
SessionLibrary/Galois.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/galois.ml"`, then `string_of_thm`, newlines joined).
tools/galoisdiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary.Galois

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Galois.ensureGalois

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
open Session SessionLibrary.Galois HolLight.Syntax

#eval thm' "galois_group" galois_group
  "|- forall l k h.        galois_group (k,l) h =        subgroup_generated (symmetric_group (ring_carrier l))        {f | ring_automorphism l f /\\             (forall x. x IN ring_carrier k ==> f (h x) = h x)}"
#eval thm' "GALOIS_GROUP_IN_CARRIER" GALOIS_GROUP_IN_CARRIER
  "|- forall h f k l x.        f IN group_carrier (galois_group (k,l) h) /\\ x IN ring_carrier l        ==> f x IN ring_carrier l"
#eval thm' "GALOIS_GROUP_BIJ_RING_HOMOMORPHISM_EXTENSIONS" GALOIS_GROUP_BIJ_RING_HOMOMORPHISM_EXTENSIONS
  "|- forall h k l.        algebraic_extension (k,l) h        ==> BIJ (RESTRICTION (ring_carrier l))            (group_carrier (galois_group (k,l) h))            (ring_homomorphism_extensions (k,l,l) (h,h))"
#eval thm' "GALOIS_IMP_ALGEBRAIC_EXTENSION" GALOIS_IMP_ALGEBRAIC_EXTENSION
  "|- forall h k l. galois_extension (k,l) h ==> algebraic_extension (k,l) h"
#eval thm' "FIXED_FIELD_EMPTY" FIXED_FIELD_EMPTY
  "|- forall l. fixed_field l {} = ring_carrier l"
#eval thm' "ISOMORPHIC_GALOIS_GROUPS" ISOMORPHIC_GALOIS_GROUPS
  "|- forall h h' f k l l'.        ring_homomorphism (k,l) h /\\        ring_isomorphism (l,l') f /\\        (forall x. x IN ring_carrier k ==> f (h x) = h' x)        ==> galois_group (k,l) h isomorphic_group galois_group (k,l') h'"
#eval thm' "GALOIS_GROUP_ANTIMONO_EQ" GALOIS_GROUP_ANTIMONO_EQ
  "|- forall h k l s t.        galois_extension (k,l) h /\\        s subfield_of l /\\        IMAGE h (ring_carrier k) SUBSET s /\\        t subfield_of l /\\        IMAGE h (ring_carrier k) SUBSET t        ==> (group_carrier (galois_group (subfield_generated l t,l) I) SUBSET             group_carrier (galois_group (subfield_generated l s,l) I) <=>             s SUBSET t)"
#eval thm' "GALOIS_GROUP_RESTRICTION" GALOIS_GROUP_RESTRICTION
  "|- forall h k l s.        normal_extension (k,l) h /\\        s subfield_of l /\\        IMAGE h (ring_carrier k) SUBSET s /\\        normal_extension (k,subfield_generated l s) h        ==> group_epimorphism            (galois_group (k,l) h,galois_group (k,subfield_generated l s) h)            (\\f x. if x IN s then f x else x) /\\            group_kernel            (galois_group (k,l) h,galois_group (k,subfield_generated l s) h)            (\\f x. if x IN s then f x else x) =            group_carrier (galois_group (subfield_generated l s,l) I)"
#eval thm' "GALOIS_GROUP_INTER" GALOIS_GROUP_INTER
  "|- forall h k l s t.        finite_extension (k,l) h /\\        galois_extension (k,l) h /\\        s subfield_of l /\\        t subfield_of l /\\        IMAGE h (ring_carrier k) SUBSET s /\\        IMAGE h (ring_carrier k) SUBSET t        ==> group_carrier            (galois_group (subfield_generated l (s INTER t),l) I) =            group_carrier            (subgroup_generated (galois_group (k,l) h)            (group_carrier (galois_group (subfield_generated l s,l) I) UNION             group_carrier (galois_group (subfield_generated l t,l) I)))"
#eval thm' "GALOIS_COMPOSITUM_PROD_GROUP" GALOIS_COMPOSITUM_PROD_GROUP
  "|- forall h k l s t.        field l /\\        s subfield_of l /\\        t subfield_of l /\\        finite_extension (k,subfield_generated l s) h /\\        galois_extension (k,subfield_generated l s) h /\\        finite_extension (k,subfield_generated l t) h /\\        galois_extension (k,subfield_generated l t) h /\\        s INTER t = IMAGE h (ring_carrier k)        ==> group_isomorphism            (galois_group (k,subfield_generated l (s UNION t)) h,             prod_group (galois_group (k,subfield_generated l s) h)             (galois_group (k,subfield_generated l t) h))            (\\f.                 (\\x. if x IN s then f x else x),                 (\\x. if x IN t then f x else x))"
#eval thm' "GALOIS_GROUP_ACTION_ON_ROOTS_TRANSITIVE" GALOIS_GROUP_ACTION_ON_ROOTS_TRANSITIVE
  "|- forall h k l p.        splitting_extension (k,l) h p /\\ ring_irreducible (poly_ring k (:1)) p        ==> (forall a b.                 a IN ring_carrier l /\\                 poly_eval l (h o p) a = ring_0 l /\\                 b IN ring_carrier l /\\                 poly_eval l (h o p) b = ring_0 l                 ==> (exists g.                          g IN                          group_image                          (galois_group (k,l) h,                           symmetric_group                           {x | x IN ring_carrier l /\\                                poly_eval l (h o p) x = ring_0 l})                          (\\f x.                               if x IN ring_carrier l /\\                                  poly_eval l (h o p) x = ring_0 l                               then f x                               else x) /\\                          g a = b))"
#eval thm' "GALOIS_GROUP_FINITE_FIELD" GALOIS_GROUP_FINITE_FIELD
  "|- forall h k l.        field_extension (k,l) h /\\ FINITE (ring_carrier l)        ==> (\\x.                 if x IN ring_carrier l                 then ring_pow l x (CARD (ring_carrier k))                 else x) IN            group_carrier (galois_group (k,l) h) /\\            subgroup_generated (galois_group (k,l) h)            {(\\x.                  if x IN ring_carrier l                  then ring_pow l x (CARD (ring_carrier k))                  else x)} =            galois_group (k,l) h /\\            CARD (group_carrier (galois_group (k,l) h)) =            extension_degree (k,l) h"
#eval thm' "GALOIS_SUM_ADD" GALOIS_SUM_ADD
  "|- forall h k l x y.        finite_extension (k,l) h /\\ x IN ring_carrier l /\\ y IN ring_carrier l        ==> ring_sum l (group_carrier (galois_group (k,l) h))            (\\f. f (ring_add l x y)) =            ring_add l            (ring_sum l (group_carrier (galois_group (k,l) h)) (\\f. f x))            (ring_sum l (group_carrier (galois_group (k,l) h)) (\\f. f y))"
#eval thm' "HILBERT_90_CYCLIC_EQ" HILBERT_90_CYCLIC_EQ
  "|- forall h k l g x.        finite_extension (k,l) h /\\        g IN group_carrier (galois_group (k,l) h) /\\        subgroup_generated (galois_group (k,l) h) {g} = galois_group (k,l) h /\\        x IN ring_carrier l        ==> (ring_product l (group_carrier (galois_group (k,l) h)) (\\f. f x) =             ring_1 l <=>             (exists y.                  y IN ring_carrier l /\\                  ~(y = ring_0 l) /\\                  x = ring_div l y (g y)))"
#eval thm' "RADICAL_EXTENSION_INTERMEDIATE" RADICAL_EXTENSION_INTERMEDIATE
  "|- forall f g k l m.        field_extension (k,l) f /\\        field_extension (l,m) g /\\        radical_extension (k,m) (g o f)        ==> radical_extension (l,m) g"
#eval thm' "RADICAL_ELEMENT_INV" RADICAL_ELEMENT_INV
  "|- forall h k l x.        radical_element (k,l) h x ==> radical_element (k,l) h (ring_inv l x)"
#eval thm' "RADICAL_EXTENSION_EQ_RADICAL_ELEMENTS" RADICAL_EXTENSION_EQ_RADICAL_ELEMENTS
  "|- forall h k l.        radical_extension (k,l) h <=>        finite_extension (k,l) h /\\        (forall x. x IN ring_carrier l ==> radical_element (k,l) h x)"
#eval thm' "GALOIS_GROUP_KUMMER_ROOT_OF_UNITY" GALOIS_GROUP_KUMMER_ROOT_OF_UNITY
  "|- forall h f k l a n.        field_extension (k,l) h /\\        {x | x IN ring_carrier k /\\ ring_pow k x n = ring_1 k} HAS_SIZE n /\\        a IN ring_carrier l /\\        ring_pow l a n IN IMAGE h (ring_carrier k) /\\        f IN group_carrier (galois_group (k,l) h)        ==> (exists c.                 c IN ring_carrier k /\\                 ring_pow k c n = ring_1 k /\\                 f a = ring_mul l (h c) a)"
#eval thm' "ARTIN_SCHREIER_CYCLIC" ARTIN_SCHREIER_CYCLIC
  "|- forall h k l a p.        field_extension (k,l) h /\\        prime p /\\        ring_char k = p /\\        a IN ring_carrier l /\\        ~(a IN IMAGE h (ring_carrier k)) /\\        ring_sub l (ring_pow l a p) a IN IMAGE h (ring_carrier k) /\\        subfield_generated l (a INSERT IMAGE h (ring_carrier k)) = l        ==> finite_extension (k,l) h /\\            galois_extension (k,l) h /\\            cyclic_group (galois_group (k,l) h) /\\            CARD (group_carrier (galois_group (k,l) h)) = p"
#eval thm' "NOT_SOLVABLE_IMP_NO_RADICAL_ROOT" NOT_SOLVABLE_IMP_NO_RADICAL_ROOT
  "|- forall h g k l m p.        ring_char k = 0 /\\        splitting_extension (k,l) h p /\\        ring_irreducible (poly_ring k (:1)) p /\\        ~solvable_group (galois_group (k,l) h) /\\        field_extension (k,m) g        ==> ~(exists x.                  radical_element (k,m) g x /\\                  poly_eval m (g o p) x = ring_0 m)"

end T
