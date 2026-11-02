/- File: HolTest/RingGroupsTest.lean
Runtime test suite: Library/ring_groups.ml (HolLibrary/RingGroups.lean, wired by
SessionLibrary/RingGroups.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/ring_groups.ml"`, then `string_of_thm`, newlines joined).
tools/ringgroupsdiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary.RingGroups

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.RingGroups.ensureRingGroups

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
open Session SessionLibrary.RingGroups HolLight.Syntax

#eval thm' "ring_additive_group" ring_additive_group
  "|- forall r.        ring_additive_group r =        group (ring_carrier r,ring_0 r,ring_neg r,ring_add r)"
#eval thm' "RING_ADDITIVE_GROUP" RING_ADDITIVE_GROUP
  "|- (forall r. group_carrier (ring_additive_group r) = ring_carrier r) /\\    (forall r. group_id (ring_additive_group r) = ring_0 r) /\\    (forall r. group_inv (ring_additive_group r) = ring_neg r) /\\    (forall r. group_mul (ring_additive_group r) = ring_add r)"
#eval thm' "ABELIAN_RING_ADDITIVE_GROUP" ABELIAN_RING_ADDITIVE_GROUP
  "|- forall r. abelian_group (ring_additive_group r)"
#eval thm' "GROUP_HOMOMORPHISM_RING_ADDITIVE_GROUP" GROUP_HOMOMORPHISM_RING_ADDITIVE_GROUP
  "|- forall r r' f.        ring_homomorphism (r,r') f        ==> group_homomorphism (ring_additive_group r,ring_additive_group r')            f"
#eval thm' "RING_IDEAL_IMP_SUBGROUP" RING_IDEAL_IMP_SUBGROUP
  "|- forall r j. ring_ideal r j ==> j subgroup_of ring_additive_group r"
#eval thm' "SUBRING_IMP_SUBGROUP_ADDITIVE" SUBRING_IMP_SUBGROUP_ADDITIVE
  "|- forall r s. s subring_of r ==> s subgroup_of ring_additive_group r"
#eval thm' "RING_ADDITIVE_GROUP_PRODUCT_RING" RING_ADDITIVE_GROUP_PRODUCT_RING
  "|- forall k r.        ring_additive_group (product_ring k r) =        product_group k (\\i. ring_additive_group (r i))"
#eval thm' "unit_group" unit_group
  "|- forall r.        unit_group r =        group ({x | ring_unit r x},ring_1 r,ring_inv r,ring_mul r)"
#eval thm' "UNIT_GROUP" UNIT_GROUP
  "|- (forall r. group_carrier (unit_group r) = {x | ring_unit r x}) /\\    (forall r. group_id (unit_group r) = ring_1 r) /\\    (forall r. group_inv (unit_group r) = ring_inv r) /\\    (forall r. group_mul (unit_group r) = ring_mul r)"
#eval thm' "ABELIAN_UNIT_GROUP" ABELIAN_UNIT_GROUP
  "|- forall r. abelian_group (unit_group r)"
#eval thm' "UNIT_GROUP_SUM" UNIT_GROUP_SUM
  "|- forall r s f.        FINITE s /\\ (forall i. i IN s ==> ring_unit r (f i))        ==> group_sum (unit_group r) s f = ring_product r s f"
#eval thm' "FIELD_UNIT_GROUP" FIELD_UNIT_GROUP
  "|- forall k.        field k        ==> group_carrier (unit_group k) = ring_carrier k DIFF {ring_0 k}"
#eval thm' "SUBGROUP_POSITIVE_REALS" SUBGROUP_POSITIVE_REALS
  "|- {x | &0 < x} subgroup_of unit_group real_ring"
#eval thm' "GROUP_HOMOMORPHISM_UNIT_GROUP" GROUP_HOMOMORPHISM_UNIT_GROUP
  "|- forall r r' f.        ring_homomorphism (r,r') f        ==> group_homomorphism (unit_group r,unit_group r') f"
#eval thm' "RING_MONOMORPHISM_UNITS_IMAGE" RING_MONOMORPHISM_UNITS_IMAGE
  "|- forall r r' f.        ring_monomorphism (r,r') f        ==> {y | ring_unit (subring_generated r' (IMAGE f (ring_carrier r))) y} =            IMAGE f {u | ring_unit r u}"
#eval thm' "RING_UNIT_PROD_RING" RING_UNIT_PROD_RING
  "|- forall r r' x y.        ring_unit (prod_ring r r') (x,y) <=> ring_unit r x /\\ ring_unit r' y"
#eval thm' "UNIT_GROUP_PROD_RING" UNIT_GROUP_PROD_RING
  "|- forall r r'.        group_isomorphism        (unit_group (prod_ring r r'),         prod_group (unit_group r) (unit_group r'))        I"
#eval thm' "UNIT_GROUP_RESTRICTED_PRODUCT_RING" UNIT_GROUP_RESTRICTED_PRODUCT_RING
  "|- forall k r s.        (forall i. i IN k ==> s i subring_of r i)        ==> group_isomorphism            (unit_group (restricted_product_ring k r s),             restricted_product_group k (\\i. unit_group (r i))             (\\i. {x | ring_unit (subring_generated (r i) (s i)) x}))            I"
#eval thm' "GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT_LEMMA" GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT_LEMMA
  "|- forall f G l s d a y.        FINITE s /\\        (forall i. i IN s ==> group_homomorphism (G,unit_group l) (f i)) /\\        (forall i. i IN s ==> d i IN ring_carrier l) /\\        a IN s /\\        y IN group_carrier G /\\        (forall x.             x IN group_carrier G             ==> ring_sum l s (\\i. ring_mul l (d i) (f i x)) = ring_0 l)        ==> (forall x.                 x IN group_carrier G                 ==> ring_sum l s                     (\\i.                          ring_mul l                          (ring_mul l (d i) (ring_sub l (f i y) (f a y)))                          (f i x)) =                     ring_0 l)"
#eval thm' "GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT" GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT
  "|- forall f G l s c.        integral_domain l /\\        FINITE s /\\        (forall i. i IN s ==> group_homomorphism (G,unit_group l) (f i)) /\\        (forall i j.             i IN s /\\ j IN s /\\ ~(i = j)             ==> (exists x. x IN group_carrier G /\\ ~(f i x = f j x))) /\\        (forall i. i IN s ==> c i IN ring_carrier l) /\\        (forall x.             x IN group_carrier G             ==> ring_sum l s (\\i. ring_mul l (c i) (f i x)) = ring_0 l)        ==> (forall i. i IN s ==> c i = ring_0 l)"

end T
