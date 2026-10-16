/- File: HolTest/GroupTheoryTest.lean
Runtime test suite: Library/grouptheory.ml (HolLibrary/GroupTheory.lean, wired by
SessionLibrary/GroupTheory.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/grouptheory.ml"`, then `string_of_thm`, newlines joined).
tools/grouptheorydiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.GroupTheory.ensureGroupTheory

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
open Session SessionLibrary.GroupTheory HolLight.Syntax

#eval thm' "group_tybij" group_tybij
  "|- (forall a. group (group_operations a) = a) /\\    (forall r.         FST (SND r) IN FST r /\\         (forall x. x IN FST r ==> FST (SND (SND r)) x IN FST r) /\\         (forall x y.              x IN FST r /\\ y IN FST r ==> SND (SND (SND r)) x y IN FST r) /\\         (forall x y z.              x IN FST r /\\ y IN FST r /\\ z IN FST r              ==> SND (SND (SND r)) x (SND (SND (SND r)) y z) =                  SND (SND (SND r)) (SND (SND (SND r)) x y) z) /\\         (forall x.              x IN FST r              ==> SND (SND (SND r)) (FST (SND r)) x = x /\\                  SND (SND (SND r)) x (FST (SND r)) = x) /\\         (forall x.              x IN FST r              ==> SND (SND (SND r)) (FST (SND (SND r)) x) x = FST (SND r) /\\                  SND (SND (SND r)) x (FST (SND (SND r)) x) = FST (SND r)) <=>         group_operations (group r) = r)"
#eval thm' "GROUP_INV_ID" GROUP_INV_ID
  "|- forall G. group_inv G (group_id G) = group_id G"
#eval thm' "ABELIAN_GROUP_DIV_ZPOW" ABELIAN_GROUP_DIV_ZPOW
  "|- forall G x y n.        abelian_group G /\\ x IN group_carrier G /\\ y IN group_carrier G        ==> group_zpow G (group_div G x y) n =            group_div G (group_zpow G x n) (group_zpow G y n)"
#eval thm' "GROUP_PRODUCT_ID" GROUP_PRODUCT_ID
  "|- forall G (<<=) s. group_product G (<<=) s (\\x. group_id G) = group_id G"
#eval thm' "IN_SUBGROUP_CONJUGATION" IN_SUBGROUP_CONJUGATION
  "|- forall G h a x.        h subgroup_of G /\\ a IN h /\\ x IN h ==> group_conjugation G a x IN h"
#eval thm' "SUBGROUP_GENERATED_INC_GEN" SUBGROUP_GENERATED_INC_GEN
  "|- forall G s x.        x IN group_carrier G /\\ x IN s        ==> x IN group_carrier (subgroup_generated G s)"
#eval thm' "TRIVIAL_SUM_GROUP" TRIVIAL_SUM_GROUP
  "|- forall k G.        trivial_group (sum_group k G) <=>        (forall i. i IN k ==> trivial_group (G i))"
#eval thm' "GROUP_MONOMORPHISM_FROM_SUBGROUP_GENERATED" GROUP_MONOMORPHISM_FROM_SUBGROUP_GENERATED
  "|- forall f G H s.        group_monomorphism (G,H) f        ==> group_monomorphism (subgroup_generated G s,H) f"
#eval thm' "GROUP_MONOMORPHISM_TO_TRIVIAL_GROUP" GROUP_MONOMORPHISM_TO_TRIVIAL_GROUP
  "|- forall f G H.        trivial_group H        ==> (group_monomorphism (G,H) f <=>             group_homomorphism (G,H) f /\\ trivial_group G)"
#eval thm' "ISOMORPHIC_TRIVIAL_GROUPS" ISOMORPHIC_TRIVIAL_GROUPS
  "|- forall G H. trivial_group G /\\ trivial_group H ==> G isomorphic_group H"
#eval thm' "GROUP_SETINV" GROUP_SETINV
  "|- forall G g.        g SUBSET group_carrier G ==> group_setinv G g SUBSET group_carrier G"
#eval thm' "GROUP_ORBIT_ON_SUBSET" GROUP_ORBIT_ON_SUBSET
  "|- forall G s t a.        t SUBSET s /\\ x IN t        ==> group_orbit G t a x = t INTER group_orbit G s a x"
#eval thm' "IN_RIGHT_COSET" IN_RIGHT_COSET
  "|- forall G h x a.        h SUBSET group_carrier G /\\        a IN group_carrier G /\\        x IN group_carrier G        ==> (x IN right_coset G h a <=> group_mul G x (group_inv G a) IN h)"
#eval thm' "GROUP_ORBIT_SUBGROUP_TRANSLATION" GROUP_ORBIT_SUBGROUP_TRANSLATION
  "|- forall G h a.        h subgroup_of G /\\ a IN group_carrier G        ==> group_orbit (subgroup_generated G h) (group_carrier G)            (group_mul G)            a =            right_coset G h a"
#eval thm' "GROUP_SETINV_RIGHT_COSET" GROUP_SETINV_RIGHT_COSET
  "|- forall G n a.        n normal_subgroup_of G /\\ a IN group_carrier G        ==> group_setinv G (right_coset G n a) =            right_coset G n (group_inv G a)"
#eval thm' "NORMAL_SUBGROUP_NORMALIZER_EQ_CARRIER" NORMAL_SUBGROUP_NORMALIZER_EQ_CARRIER
  "|- forall G n.        n normal_subgroup_of G <=>        n subgroup_of G /\\ group_normalizer G n = group_carrier G"
#eval thm' "QUOTIENT_GROUP_SUBGROUP_GENERATED" QUOTIENT_GROUP_SUBGROUP_GENERATED
  "|- forall G h n.        n normal_subgroup_of G /\\ h subgroup_of G /\\ n SUBSET h        ==> quotient_group (subgroup_generated G h) n =            subgroup_generated (quotient_group G n)            {right_coset G n x | x IN h}"
#eval thm' "GROUP_CONJUGATE_NORMAL_SUBGROUP_OF" GROUP_CONJUGATE_NORMAL_SUBGROUP_OF
  "|- forall G s t.        group_conjugate G s t        ==> (s normal_subgroup_of G <=> t normal_subgroup_of G)"
#eval thm' "ABELIAN_GROUP_ELEMENT_ORDER_MUL_DIVIDES" ABELIAN_GROUP_ELEMENT_ORDER_MUL_DIVIDES
  "|- forall G x y.        abelian_group G /\\ x IN group_carrier G /\\ y IN group_carrier G        ==> group_element_order G (group_mul G x y) divides            group_element_order G x * group_element_order G y"
#eval thm' "CYCLIC_GROUP_EPIMORPHIC_IMAGE" CYCLIC_GROUP_EPIMORPHIC_IMAGE
  "|- forall G H f.        group_epimorphism (G,H) f /\\ cyclic_group G ==> cyclic_group H"
#eval thm' "MAXIMAL_NORMAL_SUBGROUP_EXISTS" MAXIMAL_NORMAL_SUBGROUP_EXISTS
  "|- forall G.        finitely_generated_group G /\\ ~trivial_group G        ==> (exists h.                 h normal_subgroup_of G /\\                 ~(h = group_carrier G) /\\                 (forall h'.                      h' normal_subgroup_of G /\\ h PSUBSET h'                      ==> h' = group_carrier G))"
#eval thm' "ISOMORPHIC_PROD_INTEGER_MOD_GROUP" ISOMORPHIC_PROD_INTEGER_MOD_GROUP
  "|- forall m n.        prod_group (integer_mod_group m) (integer_mod_group n) isomorphic_group        integer_mod_group (m * n) <=>        coprime (m,n)"
#eval thm' "SYLOW_THEOREM_COUNT_DIVISOR" SYLOW_THEOREM_COUNT_DIVISOR
  "|- forall G p k.        FINITE (group_carrier G) /\\        prime p /\\        index p (CARD (group_carrier G)) = k        ==> CARD {h | h subgroup_of G /\\ CARD h = p EXP k} divides            CARD (group_carrier G) DIV p EXP k"
#eval thm' "SUBGROUP_ISOMORPHISM_GROUP_SUM_EQ" SUBGROUP_ISOMORPHISM_GROUP_SUM_EQ
  "|- forall k G h.        (forall i. i IN k ==> h i subgroup_of G)        ==> (group_isomorphism             (sum_group k (\\i. subgroup_generated G (h i)),              subgroup_generated G (UNIONS {h i | i IN k}))             (group_sum G k) <=>             pairwise             (\\i j.                  forall x y.                      x IN h i /\\ y IN h j                      ==> group_mul G x y = group_mul G y x)             k /\\             (forall i.                  i IN k                  ==> h i INTER                      group_carrier                      (subgroup_generated G (UNIONS {h j | j IN k DELETE i})) =                      {group_id G}))"
#eval thm' "ISOMORPHIC_GROUP_INTEGER_FREE_ABELIAN_GROUP_SING" ISOMORPHIC_GROUP_INTEGER_FREE_ABELIAN_GROUP_SING
  "|- forall x. integer_group isomorphic_group free_abelian_group {x}"
#eval thm' "SPLITTING_LEMMA_RIGHT_PROD_GROUP" SPLITTING_LEMMA_RIGHT_PROD_GROUP
  "|- forall f g g' A B C.        short_exact_sequence (A,B,C) (f,g) /\\        abelian_group B /\\        group_homomorphism (C,B) g' /\\        (forall z. z IN group_carrier C ==> g (g' z) = z)        ==> B isomorphic_group prod_group A C"
#eval thm' "EXACT_SEQUENCE_HEXAGON_LEMMA" EXACT_SEQUENCE_HEXAGON_LEMMA
  "|- forall f g h h' i j k k' a b c d l m A B C D W X Y.        abelian_group X /\\        group_homomorphism (A,Y) a /\\        group_homomorphism (B,Y) b /\\        group_homomorphism (W,C) c /\\        group_homomorphism (W,D) d /\\        group_isomorphisms (A,C) (h,h') /\\        group_isomorphisms (B,D) (k,k') /\\        group_exactness (A,X,D) (i,g) /\\        group_exactness (B,X,C) (j,f) /\\        group_exactness (W,X,Y) (l,m) /\\        (forall x. x IN group_carrier W ==> f (l x) = c x) /\\        (forall x. x IN group_carrier W ==> g (l x) = d x) /\\        (forall x. x IN group_carrier A ==> f (i x) = h x) /\\        (forall x. x IN group_carrier A ==> m (i x) = a x) /\\        (forall x. x IN group_carrier B ==> g (j x) = k x) /\\        (forall x. x IN group_carrier B ==> m (j x) = b x)        ==> (forall x.                 x IN group_carrier W                 ==> group_inv Y (a (h' (c x))) = b (k' (d x)))"

end T
