/- ========================================================================= -/
/- The additive group and the unit group of a ring.                          -/
/-                                                                           -/
/-   ring_additive_group r = the group of r under ring_add r, with identity  -/
/-                           ring_0 r and inverse ring_neg r                 -/
/-   unit_group r          = the group of the units of r under ring_mul r,   -/
/-                           with identity ring_1 r and inverse ring_inv r   -/
/- ========================================================================= -/
/- File: HolLibrary/RingGroups.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/ring_groups.ml`, by hand, in file
  order, in the style of HolLibrary/ModmulGroup.lean (see there and
  HolMath/Base.lean for the conventions).  ring_groups.ml begins with
  `needs "Library/ringtheory.ml"` and `needs "Library/grouptheory.ml"`; the
  theorems it uses from them (and from the files they need) and from the
  core library are supplied via the CoreThms structures
  (SessionLibrary.RingGroups fills them).  Each section is a bundle (a
  `structure`) built by a `setup` function; SessionLibrary/RingGroups.lean
  builds the bundles in order and exports every name under its HOL Light
  name.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, SET_RULE, RING_RULE, TAUT) they are bound first, in
  OCaml's order.
-/

import HolLibrary.RingTheory
import HolLibrary.GroupTheory

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolLibrary.RingGroups

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ABELIAN_GROUP_MUL_ZPOW ABELIAN_GROUP_SUM_CLAUSES
   AND_FORALL_THM CARD_CROSS CARD_IMAGE_INJ CARRIER_SUBGROUP_GENERATED_SUBGROUP
   EQ_TRANS EXISTS_PAIR_THM EXTENSION
   FIELD_REAL_RING FIELD_UNIT FINITELY_GENERATED_ABELIAN_GROUP_POW
   FINITE_INDUCT_STRONG FINITE_INSERT
   FINITE_RESTRICT FINITE_SUBSET FORALL_INT_CASES FORALL_IN_IMAGE
   FORALL_IN_INSERT FORALL_PAIR_THM GROUPS_EQ GROUP_HOMOMORPHISM
   GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ GROUP_HOMOMORPHISM_MUL
   GROUP_HOMOMORPHISM_OF_ID GROUP_ID GROUP_INV
   GROUP_ISOMORPHISM GROUP_MUL GROUP_MUL_LID GROUP_MUL_RINV GROUP_POW GROUP_SUM
   GROUP_SUM_CLAUSES_EXISTS GROUP_ZPOW GROUP_ZPOW_POW
   IMAGE_I IMAGE_ID IMP_CONJ INSERT_SUBSET
   INTEGRAL_DOMAIN_MUL_EQ_0 IN_CROSS IN_DIFF IN_ELIM_THM IN_IMAGE IN_INSERT
   IN_SING IN_SUBGROUP_POW IN_SUBGROUP_SUM IN_UNIV I_DEF
   I_THM MONO_EXISTS NOT_IN_EMPTY
   PAIR_EQ PRODUCT_CLAUSES PRODUCT_GROUP PRODUCT_RING
   PROD_GROUP PROD_RING REAL_LT_01 REAL_LT_IMP_NZ REAL_LT_INV REAL_LT_MUL
   REAL_RING_CLAUSES REAL_RING_INV REAL_ZPOW_POW RESTRICTED_PRODUCT_GROUP
   RESTRICTED_PRODUCT_RING RIGHT_FORALL_IMP_THM RING_0 RING_1 RING_ADD
   RING_ADD_ASSOC RING_ADD_LNEG RING_ADD_LZERO RING_ADD_RNEG : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (RING_ADD_RZERO RING_ADD_SYM RING_HOMOMORPHISM_1 RING_HOMOMORPHISM_INCLUSION
   RING_HOMOMORPHISM_INV RING_HOMOMORPHISM_MUL
   RING_INV RING_INV_1 RING_ISOMORPHISM_IMP_MONOMORPHISM
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MONOMORPHISM_INJECTIVE_EQ
   RING_MUL RING_MUL_ASSOC RING_MUL_LID
   RING_MUL_LINV RING_MUL_LNEG RING_MUL_LZERO
   RING_MUL_RID RING_MUL_RINV RING_MUL_RNEG RING_MUL_RZERO
   RING_MUL_SYM RING_NEG RING_NEG_NEG
   RING_POW_NEG RING_POW_ONE RING_PRODUCT_CLAUSES
   RING_RINV_UNIQUE RING_SUB RING_SUB_EQ_0
   RING_SUB_REFL RING_SUM RING_SUM_0 RING_SUM_CLAUSES RING_SUM_EQ RING_SUM_EQ_0
   RING_SUM_LMUL RING_SUM_SUB RING_UNIT_1 RING_UNIT_HOMOMORPHIC_IMAGE
   RING_UNIT_INV RING_UNIT_IN_CARRIER
   RING_UNIT_MUL RING_UNIT_NEG RING_UNIT_POW RING_UNIT_PRODUCT_RING
   RING_UNIT_RESTRICTED_PRODUCT_RING
   RING_UNIT_SUBRING_GENERATED
   SUBGROUP_GENERATED_INC_GEN SUBGROUP_GENERATED_SUPERSET
   SUBGROUP_GROUP_IMAGE SUBGROUP_SUBGROUP_GENERATED SUBRING_RING_IMAGE
   SUBSET SUBSET_REFL SWAP_FORALL_THM
   abelian_group finitely_generated_group group_carrier
   group_homomorphism group_id group_image group_inv
   group_mul group_pow group_tybij
   isomorphic_ring real_pow ring_homomorphism
   ring_ideal ring_image ring_isomorphism ring_isomorphisms
   ring_monomorphism ring_pow ring_unit subgroup_of subring_of : thm)
  deriving Inhabited

/-- What ring_groups.ml uses from Session besides theorems. -/
structure RingGroupsDeps where
  -- definitions
  new_definition : String → ExceptT String IO thm
  -- decision procedures and tactics
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  INDUCT_TAC : tactic
  RING_RULE : term → ExceptT String IO thm  -- ringtheory.ml's RING_RULE
  REAL_FIELD : term → ExceptT String IO thm
  TAUT : term → ExceptT String IO thm
  core1 : CoreThms1
  core2 : CoreThms2

/-- RingTheory's `wPart` (copied verbatim).  `W(MP_TAC o PART_MATCH f th o g
    o snd)`: match `th`'s part `f` against the part `g` of the goal, and
    MP_TAC the instance. -/
def wPart [HolBase] (g : term → Except String term) (f : term → Except String term)
    (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (g gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)

/- ------------------------------------------------------------------------- -/
/- The additive group of a ring. Finite sums in it are ring sums             -/
/- (GROUP_SUM_RING_ADDITIVE_GROUP).                                          -/
/- ------------------------------------------------------------------------- -/

structure AdditiveGroup where
  -- @@FIELDS
  ring_additive_group : thm
  RING_ADDITIVE_GROUP : thm
  ABELIAN_RING_ADDITIVE_GROUP : thm
  GROUP_HOMOMORPHISM_RING_ADDITIVE_GROUP : thm
  GROUP_SUM_RING_ADDITIVE_GROUP : thm
  RING_IDEAL_IMP_SUBGROUP : thm
  SUBRING_IMP_SUBGROUP_ADDITIVE : thm
  RING_ADDITIVE_GROUP_PRODUCT_RING : thm
  RING_ADDITIVE_GROUP_RESTRICTED_PRODUCT_RING : thm
  deriving Inhabited

@[nospecialize]
def setupAdditiveGroup [HolBase] (D : RingGroupsDeps) :
    ExceptT String IO AdditiveGroup := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, new_definition, .. } := D
  let { ABELIAN_GROUP_SUM_CLAUSES, AND_FORALL_THM, FINITE_INDUCT_STRONG,
        FINITE_RESTRICT, GROUPS_EQ, GROUP_HOMOMORPHISM, GROUP_SUM_CLAUSES_EXISTS,
        PRODUCT_GROUP, PRODUCT_RING, RESTRICTED_PRODUCT_GROUP, RESTRICTED_PRODUCT_RING,
        RIGHT_FORALL_IMP_THM, RING_0, RING_ADD, RING_ADD_ASSOC, RING_ADD_LNEG,
        RING_ADD_LZERO, RING_ADD_RNEG, .. } := D.core1
  let { RING_ADD_RZERO, RING_ADD_SYM, RING_NEG, RING_SUM_CLAUSES, abelian_group,
        group_carrier, group_id, group_inv, group_mul, group_tybij, ring_homomorphism,
        ring_ideal, subgroup_of, subring_of, .. } := D.core2
  -- @@SCOPE END

  let ring_additive_group ← new_definition
   r"ring_additive_group (r:A ring) =
        group(ring_carrier r,ring_0 r,ring_neg r,ring_add r)"

  let RING_ADDITIVE_GROUP ← prove
   r"(!r:A ring. group_carrier(ring_additive_group r) = ring_carrier r) /\
   (!r:A ring. group_id(ring_additive_group r) = ring_0 r) /\
   (!r:A ring. group_inv(ring_additive_group r) = ring_neg r) /\
   (!r:A ring. group_mul(ring_additive_group r) = ring_add r)"
   (REWRITE_TAC [AND_FORALL_THM] THEN GEN_TAC THEN
    MP_TAC (← EQ_IMP_RULE
     (← ISPEC (← liftExcept (do rand (← rand (strip_forall (concl ring_additive_group)).2)))
       (← CONJUNCT2 group_tybij))).1 THEN
    REWRITE_TAC [← GSYM ring_additive_group] THEN ANTS_TAC THENL
     [SIMP_TAC [RING_0, RING_NEG, RING_ADD, RING_ADD_ASSOC, RING_ADD_LZERO,
                RING_ADD_RZERO, RING_ADD_LNEG, RING_ADD_RNEG],
      SIMP_TAC [group_carrier, group_id, group_inv, group_mul]])

  let ABELIAN_RING_ADDITIVE_GROUP ← prove
   r"!r:A ring. abelian_group(ring_additive_group r)"
   (REWRITE_TAC [abelian_group, RING_ADDITIVE_GROUP] THEN
    MESON_TAC [RING_ADD_SYM])

  let GROUP_HOMOMORPHISM_RING_ADDITIVE_GROUP ← prove
   r"!r r' (f:A->B).
        ring_homomorphism(r,r') f
        ==> group_homomorphism(ring_additive_group r,ring_additive_group r') f"
   (SIMP_TAC [ring_homomorphism, GROUP_HOMOMORPHISM, RING_ADDITIVE_GROUP])

  let GROUP_SUM_RING_ADDITIVE_GROUP ← prove
   r"!r s (f:K->A).
        FINITE s ==> group_sum (ring_additive_group r) s f = ring_sum r s f"
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [← CONJUNCT1 (← SPEC_ALL GROUP_SUM_CLAUSES_EXISTS),
                 RING_SUM_CLAUSES, RING_ADDITIVE_GROUP] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [ABELIAN_GROUP_SUM_CLAUSES, ABELIAN_RING_ADDITIVE_GROUP,
                  FINITE_RESTRICT, RING_SUM_CLAUSES, RING_ADDITIVE_GROUP])

  let RING_IDEAL_IMP_SUBGROUP ← prove
   r"!r j:A->bool. ring_ideal r j ==> j subgroup_of ring_additive_group r"
   (SIMP_TAC [ring_ideal, subgroup_of, RING_ADDITIVE_GROUP])

  let SUBRING_IMP_SUBGROUP_ADDITIVE ← prove
   r"!r s:A->bool. s subring_of r ==> s subgroup_of ring_additive_group r"
   (SIMP_TAC [subring_of, subgroup_of, RING_ADDITIVE_GROUP])

  let RING_ADDITIVE_GROUP_PRODUCT_RING ← prove
   r"!k (r:K->A ring).
        ring_additive_group(product_ring k r) =
        product_group k (\i. ring_additive_group(r i))"
   (REWRITE_TAC [GROUPS_EQ, RING_ADDITIVE_GROUP, PRODUCT_GROUP, PRODUCT_RING])

  let RING_ADDITIVE_GROUP_RESTRICTED_PRODUCT_RING ← prove
   r"!k (r:K->A ring) s.
        (!i. i IN k ==> s i subring_of r i)
        ==> ring_additive_group(restricted_product_ring k r s) =
            restricted_product_group k (\i. ring_additive_group(r i)) s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [GROUPS_EQ] THEN
    ASM_SIMP_TAC [RING_ADDITIVE_GROUP, RESTRICTED_PRODUCT_GROUP,
                  RESTRICTED_PRODUCT_RING, SUBRING_IMP_SUBGROUP_ADDITIVE])

  -- @@RETURN BEGIN
  return { ring_additive_group, RING_ADDITIVE_GROUP, ABELIAN_RING_ADDITIVE_GROUP,
           GROUP_HOMOMORPHISM_RING_ADDITIVE_GROUP, GROUP_SUM_RING_ADDITIVE_GROUP,
           RING_IDEAL_IMP_SUBGROUP, SUBRING_IMP_SUBGROUP_ADDITIVE,
           RING_ADDITIVE_GROUP_PRODUCT_RING, RING_ADDITIVE_GROUP_RESTRICTED_PRODUCT_RING }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- The unit group and its basic properties.                                  -/
/- ------------------------------------------------------------------------- -/

structure UnitGroup where
  -- @@FIELDS
  unit_group : thm
  UNIT_GROUP : thm
  ABELIAN_UNIT_GROUP : thm
  UNIT_GROUP_POW : thm
  UNIT_GROUP_SUM : thm
  UNIT_GROUP_ZPOW_RING_NEG : thm
  FINITELY_GENERATED_UNIT_GROUP : thm
  FIELD_UNIT_GROUP : thm
  SUBGROUP_POSITIVE_REALS : thm
  GROUP_REAL_MULTIPLICATIVE_ID_INV_POW : thm
  GROUP_REAL_MULTIPLICATIVE_ZPOW : thm
  GROUP_REAL_MULTIPLICATIVE_SUM : thm
  deriving Inhabited

@[nospecialize]
def setupUnitGroup [HolBase] (D : RingGroupsDeps) :
    ExceptT String IO UnitGroup := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, REAL_FIELD, TAUT, new_definition, .. } := D
  let { ABELIAN_GROUP_MUL_ZPOW, ABELIAN_GROUP_SUM_CLAUSES, AND_FORALL_THM, EXTENSION,
        FIELD_REAL_RING, FIELD_UNIT, FINITELY_GENERATED_ABELIAN_GROUP_POW,
        FINITE_INDUCT_STRONG, FINITE_RESTRICT, FORALL_INT_CASES, FORALL_IN_INSERT,
        GROUP_ID, GROUP_INV, GROUP_MUL_LID, GROUP_MUL_RINV, GROUP_POW, GROUP_SUM,
        GROUP_SUM_CLAUSES_EXISTS, GROUP_ZPOW, GROUP_ZPOW_POW, IMP_CONJ, IN_DIFF,
        IN_ELIM_THM, IN_SING, IN_SUBGROUP_POW, IN_SUBGROUP_SUM, IN_UNIV, MONO_EXISTS,
        PRODUCT_CLAUSES, REAL_LT_01, REAL_LT_IMP_NZ, REAL_LT_INV, REAL_LT_MUL,
        REAL_RING_CLAUSES, REAL_RING_INV, REAL_ZPOW_POW, RING_1, .. } := D.core1
  let { RING_INV_1, RING_MUL_ASSOC, RING_MUL_LID, RING_MUL_LINV, RING_MUL_LNEG,
        RING_MUL_RID, RING_MUL_RINV, RING_MUL_RNEG, RING_MUL_SYM, RING_NEG,
        RING_NEG_NEG, RING_POW_NEG, RING_POW_ONE, RING_PRODUCT_CLAUSES,
        RING_RINV_UNIQUE, RING_UNIT_1, RING_UNIT_INV, RING_UNIT_IN_CARRIER,
        RING_UNIT_MUL, RING_UNIT_NEG, RING_UNIT_POW, SUBGROUP_GENERATED_INC_GEN,
        SUBGROUP_GENERATED_SUPERSET, SUBGROUP_SUBGROUP_GENERATED, SUBSET,
        SWAP_FORALL_THM, abelian_group, finitely_generated_group, group_carrier,
        group_id, group_inv, group_mul, group_pow, group_tybij, real_pow, ring_pow,
        subgroup_of, .. } := D.core2
  -- @@SCOPE END

  let unit_group ← new_definition
   r"unit_group (r:A ring) =
  group({x | ring_unit r x},ring_1 r,ring_inv r,ring_mul r)"

  let UNIT_GROUP ← prove
   r"(!r:A ring. group_carrier(unit_group r) = {x | ring_unit r x}) /\
   (!r:A ring. group_id(unit_group r) = ring_1 r) /\
   (!r:A ring. group_inv(unit_group r) = ring_inv r) /\
   (!r:A ring. group_mul(unit_group r) = ring_mul r)"
   (REWRITE_TAC [AND_FORALL_THM] THEN GEN_TAC THEN
    MP_TAC (← EQ_IMP_RULE
     (← ISPEC (← liftExcept (do rand (← rand (strip_forall (concl unit_group)).2)))
       (← CONJUNCT2 group_tybij))).1 THEN
    REWRITE_TAC [← GSYM unit_group] THEN ANTS_TAC THENL
     [REWRITE_TAC [IN_ELIM_THM] THEN
      SIMP_TAC [RING_UNIT_1, RING_UNIT_INV, RING_UNIT_MUL] THEN
      SIMP_TAC [RING_MUL_LINV, RING_MUL_RINV] THEN
      MESON_TAC [RING_MUL_ASSOC, RING_MUL_LID, RING_MUL_RID,
                 RING_UNIT_IN_CARRIER],
      SIMP_TAC [group_carrier, group_id, group_inv, group_mul]])

  let ABELIAN_UNIT_GROUP ← prove
   r"!r:A ring. abelian_group(unit_group r)"
   (REWRITE_TAC [abelian_group, UNIT_GROUP, IN_ELIM_THM] THEN
    MESON_TAC [RING_MUL_SYM, RING_UNIT_IN_CARRIER])

  let UNIT_GROUP_POW ← prove
   r"!r:A ring x n. group_pow (unit_group r) x n = ring_pow r x n"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [group_pow, ring_pow, UNIT_GROUP])

  let UNIT_GROUP_SUM ← prove
   r"!r:A ring s (f:K->A).
        FINITE s /\ (!i. i IN s ==> ring_unit r (f i))
        ==> group_sum (unit_group r) s f = ring_product r s f"
   (GEN_TAC THEN GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC THEN
    REWRITE_TAC [IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [← CONJUNCT1 (← SPEC_ALL GROUP_SUM_CLAUSES_EXISTS), FINITE_RESTRICT,
              ABELIAN_GROUP_SUM_CLAUSES, ABELIAN_UNIT_GROUP, FORALL_IN_INSERT,
              RING_PRODUCT_CLAUSES, UNIT_GROUP, IN_ELIM_THM,
              RING_UNIT_IN_CARRIER])

  let UNIT_GROUP_ZPOW_RING_NEG ← prove
   r"!r (x:A) n.
        ring_unit r x
        ==> group_zpow (unit_group r) (ring_neg r x) n =
            group_zpow (unit_group r) x n \/
            group_zpow (unit_group r) (ring_neg r x) n =
            ring_neg r (group_zpow (unit_group r) x n)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"group_zpow (unit_group r) (ring_neg r (ring_1 r)) n = ring_1 r \/
    group_zpow (unit_group r) (ring_neg r (ring_1 r)) n =
    ring_neg r (ring_1 (r:A ring))")
    MP_TAC THENL
     [SPEC_TAC (← q r"n:int", ← q r"n:int") THEN
      REWRITE_TAC [FORALL_INT_CASES, GROUP_ZPOW_POW, UNIT_GROUP_POW] THEN
      SIMP_TAC [RING_POW_NEG, RING_1, RING_POW_ONE, UNIT_GROUP] THEN
      CONJ_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC [RING_INV_1] THEN DISJ2_TAC THEN
      MATCH_MP_TAC RING_RINV_UNIQUE THEN
      SIMP_TAC [RING_MUL_LNEG, RING_MUL_RNEG, RING_NEG_NEG, RING_MUL_LID,
                RING_1, RING_NEG],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_neg r x = ring_mul r (ring_neg r (ring_1 r)) (x:A)")
    SUBST1_TAC THENL
     [ASM_SIMP_TAC [RING_MUL_LNEG, RING_MUL_LID, RING_UNIT_IN_CARRIER, RING_1],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"unit_group r:A group", ← q r"ring_neg r (ring_1 r):A", ← q r"x:A",
                      ← q r"n:int"] ABELIAN_GROUP_MUL_ZPOW) THEN
    REWRITE_TAC [ABELIAN_UNIT_GROUP, UNIT_GROUP, IN_ELIM_THM] THEN
    ASM_SIMP_TAC [RING_UNIT_NEG, RING_UNIT_1] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN (← q r"group_zpow (unit_group r) (x:A) n IN ring_carrier r")
    ASSUME_TAC THENL
     [MATCH_MP_TAC RING_UNIT_IN_CARRIER THEN
      MP_TAC (← ISPECL [← q r"unit_group r:A group", ← q r"x:A", ← q r"n:int"] GROUP_ZPOW) THEN
      ASM_REWRITE_TAC [UNIT_GROUP, IN_ELIM_THM],
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [RING_MUL_LID, RING_MUL_LNEG, RING_1])

  let FINITELY_GENERATED_UNIT_GROUP ← prove
   r"!r:A ring.
        finitely_generated_group(unit_group r) <=>
        ?t. FINITE t /\ (!u. u IN t ==> ring_unit r u) /\
            !u. ring_unit r u
                ==> ?n. u = ring_product r t (\v. ring_pow r v (n v))"
   (GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN MP_TAC (← ISPEC (← q r"unit_group(r:A ring)")
        FINITELY_GENERATED_ABELIAN_GROUP_POW) THEN
      ASM_REWRITE_TAC [ABELIAN_UNIT_GROUP, UNIT_GROUP, SUBSET, IN_ELIM_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:A->bool") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"u:A") THEN
      DISCH_THEN (fun th => FIRST_X_ASSUM (MP_TAC o C MATCH_MP th)) THEN
      ASM_SIMP_TAC [UNIT_GROUP_POW, UNIT_GROUP_SUM, RING_UNIT_POW],
      REWRITE_TAC [finitely_generated_group, SUBGROUP_GENERATED_SUPERSET] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:A->bool") THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [SUBSET, UNIT_GROUP, IN_ELIM_THM] THEN
      X_GEN_TAC (← q r"u:A") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"n:A->num") SUBST1_TAC o C MATCH_MP
       (← ASSUME (← q r"ring_unit r (u:A)"))) THEN
      wPart lhand (fun t => do rand (← rand t)) UNIT_GROUP_SUM THEN
      ASM_SIMP_TAC [RING_UNIT_POW] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC IN_SUBGROUP_SUM THEN
      REWRITE_TAC [SUBGROUP_SUBGROUP_GENERATED, ← GSYM UNIT_GROUP_POW] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBGROUP_POW THEN
      ASM_SIMP_TAC [SUBGROUP_SUBGROUP_GENERATED, SUBGROUP_GENERATED_INC_GEN,
                    UNIT_GROUP, IN_ELIM_THM]])

  let FIELD_UNIT_GROUP ← prove
   r"!k:A ring.
        field k
        ==> group_carrier(unit_group k) = ring_carrier k DIFF {ring_0 k}"
   (SIMP_TAC [UNIT_GROUP, FIELD_UNIT, EXTENSION, IN_ELIM_THM, IN_DIFF,
              IN_SING])

  let SUBGROUP_POSITIVE_REALS ← prove
   r"{x:real | &0 < x} subgroup_of unit_group real_ring"
   (REWRITE_TAC [subgroup_of, UNIT_GROUP, REAL_RING_INV, SUBSET, IN_ELIM_THM] THEN
    SIMP_TAC [FIELD_UNIT, FIELD_REAL_RING, REAL_RING_CLAUSES, IN_UNIV] THEN
    SIMP_TAC [REAL_LT_IMP_NZ, REAL_LT_01, REAL_LT_INV, REAL_LT_MUL])

  let GROUP_REAL_MULTIPLICATIVE_ID_INV_POW ← prove
   r"!G (g:A->real).
        (!x. x IN group_carrier G ==> &0 < g x) /\
        (!x y. x IN group_carrier G /\ y IN group_carrier G
               ==> g(group_mul G x y) = g x * g y)
        ==> g(group_id G) = &1 /\
            (!x. x IN group_carrier G ==> g(group_inv G x) = inv(g x)) /\
            (!x n. x IN group_carrier G ==> g(group_pow G x n) = g x pow n)"
   (← do
    let f2 ← REAL_FIELD (← q r"x * y = &1 ==> y = inv x")
    let f1 ← REAL_FIELD (← q r"&0:real < x /\ x * x = x ==> x = &1")
    let t1 ← TAUT (← q r"p /\ (p ==> q /\ r) ==> p /\ q /\ r")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC t1 THEN CONJ_TAC THENL
     [MATCH_MP_TAC f1 THEN
      ASM_MESON_TAC [GROUP_ID, GROUP_MUL_LID],
      DISCH_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
       [MATCH_MP_TAC f2 THEN
        ASM_MESON_TAC [GROUP_INV, GROUP_MUL_RINV],
        SPEC_TAC (← q r"n:num", ← q r"n:num") THEN INDUCT_TAC THEN
        ASM_SIMP_TAC [group_pow, real_pow, GROUP_POW]]]))

  let GROUP_REAL_MULTIPLICATIVE_ZPOW ← prove
   r"!G (g:A->real) x n.
        (!x. x IN group_carrier G ==> &0 < g x) /\
        (!x y. x IN group_carrier G /\ y IN group_carrier G
               ==> g(group_mul G x y) = g x * g y) /\
        x IN group_carrier G
        ==> g(group_zpow G x n) = g x zpow n"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"G:A group", ← q r"g:A->real"]
      GROUP_REAL_MULTIPLICATIVE_ID_INV_POW) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SPEC_TAC (← q r"n:int", ← q r"n:int") THEN
    REWRITE_TAC [FORALL_INT_CASES, GROUP_ZPOW_POW, REAL_ZPOW_POW] THEN
    ASM_SIMP_TAC [GROUP_POW])

  let GROUP_REAL_MULTIPLICATIVE_SUM ← prove
   r"!G (g:A->real) (x:K->A) t.
        abelian_group G /\
        (!x y. x IN group_carrier G /\ y IN group_carrier G
               ==> g(group_mul G x y) = g x * g y) /\
        g(group_id G) = &1 /\
        FINITE t /\ (!i. i IN t ==> x i IN group_carrier G)
        ==> g(group_sum G t x) = product t (\i. g(x i))"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
    REWRITE_TAC [IMP_CONJ] THEN SPEC_TAC (← q r"t:K->bool", ← q r"t:K->bool") THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [← CONJUNCT1 (← SPEC_ALL GROUP_SUM_CLAUSES_EXISTS), PRODUCT_CLAUSES,
                  ABELIAN_GROUP_SUM_CLAUSES, FINITE_RESTRICT, FORALL_IN_INSERT,
                  GROUP_SUM])

  -- @@RETURN BEGIN
  return { unit_group, UNIT_GROUP, ABELIAN_UNIT_GROUP, UNIT_GROUP_POW, UNIT_GROUP_SUM,
           UNIT_GROUP_ZPOW_RING_NEG, FINITELY_GENERATED_UNIT_GROUP, FIELD_UNIT_GROUP,
           SUBGROUP_POSITIVE_REALS, GROUP_REAL_MULTIPLICATIVE_ID_INV_POW,
           GROUP_REAL_MULTIPLICATIVE_ZPOW, GROUP_REAL_MULTIPLICATIVE_SUM }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Homomorphisms and subrings.                                               -/
/- ------------------------------------------------------------------------- -/

structure UnitHomomorphisms where
  -- @@FIELDS
  GROUP_HOMOMORPHISM_UNIT_GROUP : thm
  UNIT_GROUP_SUBRING_GENERATED : thm
  RING_MONOMORPHISM_UNITS_IMAGE : thm
  RING_ISOMORPHISM_IMAGE_UNITS : thm
  ISOMORPHIC_RING_CARD_UNITS : thm
  RING_UNIT_PROD_RING : thm
  UNIT_GROUP_PROD_RING : thm
  CARD_UNITS_PROD_RING : thm
  UNIT_GROUP_PRODUCT_RING : thm
  UNIT_GROUP_RESTRICTED_PRODUCT_RING : thm
  deriving Inhabited

@[nospecialize]
def setupUnitHomomorphisms [HolBase] (D : RingGroupsDeps) (BUnitGroup : UnitGroup) :
    ExceptT String IO UnitHomomorphisms := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, .. } := D
  let { CARD_CROSS, CARD_IMAGE_INJ, CARRIER_SUBGROUP_GENERATED_SUBGROUP,
        EXISTS_PAIR_THM, EXTENSION, FINITE_SUBSET, FORALL_IN_IMAGE, FORALL_PAIR_THM,
        GROUP_HOMOMORPHISM, GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ, GROUP_ISOMORPHISM,
        IMAGE_I, IMAGE_ID, IN_CROSS, IN_ELIM_THM, IN_IMAGE, I_DEF, I_THM, PAIR_EQ,
        PRODUCT_GROUP, PRODUCT_RING, PROD_GROUP, PROD_RING, RESTRICTED_PRODUCT_GROUP,
        RESTRICTED_PRODUCT_RING, RING_1, .. } := D.core1
  let { RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_INCLUSION, RING_HOMOMORPHISM_INV,
        RING_HOMOMORPHISM_MUL, RING_INV, RING_ISOMORPHISM_IMP_MONOMORPHISM,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MONOMORPHISM_INJECTIVE_EQ, RING_MUL,
        RING_MUL_RINV, RING_UNIT_HOMOMORPHIC_IMAGE, RING_UNIT_IN_CARRIER,
        RING_UNIT_PRODUCT_RING, RING_UNIT_RESTRICTED_PRODUCT_RING,
        RING_UNIT_SUBRING_GENERATED, SUBGROUP_GROUP_IMAGE, SUBRING_RING_IMAGE, SUBSET,
        SUBSET_REFL, group_image, isomorphic_ring, ring_image, ring_isomorphism,
        ring_isomorphisms, ring_monomorphism, ring_unit, .. } := D.core2
  let { UNIT_GROUP, .. } := BUnitGroup
  -- @@SCOPE END

  let GROUP_HOMOMORPHISM_UNIT_GROUP ← prove
   r"!r r' (f:A->B).
        ring_homomorphism(r,r') f
        ==> group_homomorphism(unit_group r,unit_group r') f"
   (REWRITE_TAC [GROUP_HOMOMORPHISM, UNIT_GROUP, SUBSET, FORALL_IN_IMAGE,
                 IN_ELIM_THM] THEN
    MESON_TAC [RING_UNIT_HOMOMORPHIC_IMAGE, RING_HOMOMORPHISM_MUL,
               RING_UNIT_IN_CARRIER])

  let UNIT_GROUP_SUBRING_GENERATED ← prove
   r"!r:A ring s.
        {x | ring_unit (subring_generated r s) x} subgroup_of unit_group r /\
        group_isomorphism
         (unit_group(subring_generated r s),
          subgroup_generated (unit_group r)
                             {x | ring_unit (subring_generated r s) x}) I"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"r:A ring", ← q r"s:A->bool"] RING_HOMOMORPHISM_INCLUSION) THEN
    DISCH_THEN (MP_TAC o MATCH_MP GROUP_HOMOMORPHISM_UNIT_GROUP) THEN
    DISCH_THEN (fun th => tactic_of do
      pure (ASSUME_TAC th THEN MP_TAC (← MATCH_MP SUBGROUP_GROUP_IMAGE th))) THEN
    REWRITE_TAC [group_image, IMAGE_ID, UNIT_GROUP] THEN DISCH_TAC THEN
    ASM_SIMP_TAC [GROUP_ISOMORPHISM, GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ,
                  CARRIER_SUBGROUP_GENERATED_SUBGROUP, I_DEF, IMAGE_ID,
                  UNIT_GROUP, SUBSET_REFL])

  let RING_MONOMORPHISM_UNITS_IMAGE ← prove
   r"!r r' (f:A->B).
        ring_monomorphism(r,r') f
        ==> {y | ring_unit (subring_generated r' (IMAGE f (ring_carrier r)))
                           y} =
            IMAGE f {u | ring_unit r u}"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    SUBGOAL_THEN (← q r"IMAGE (f:A->B) (ring_carrier r) subring_of r'") ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"r:A ring", ← q r"r':B ring", ← q r"f:A->B"] SUBRING_RING_IMAGE) THEN
      ASM_REWRITE_TAC [ring_image],
      ALL_TAC] THEN
    ASM_SIMP_TAC [RING_UNIT_SUBRING_GENERATED] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM, IN_IMAGE] THEN
    X_GEN_TAC (← q r"y:B") THEN EQ_TAC THENL
     [DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"a:A") STRIP_ASSUME_TAC)
       (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"b:A") STRIP_ASSUME_TAC))) THEN
      EXISTS_TAC (← q r"a:A") THEN ASM_REWRITE_TAC [ring_unit] THEN
      EXISTS_TAC (← q r"b:A") THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC (← q r"ring_monomorphism(r,r') (f:A->B)") THEN
      REWRITE_TAC [ring_monomorphism] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_MUL, RING_1] THEN
      FIRST_ASSUM (fun th => tactic_of do
        pure (ASM_SIMP_TAC [← MATCH_MP RING_HOMOMORPHISM_MUL th,
                            ← MATCH_MP RING_HOMOMORPHISM_1 th])) THEN
      UNDISCH_TAC (← q r"ring_inv r' y = (f:A->B) b") THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      UNDISCH_TAC (← q r"y = (f:A->B) a") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC [RING_MUL_RINV],
      DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN (← q r"(a:A) IN ring_carrier r") ASSUME_TAC THENL
       [ASM_MESON_TAC [ring_unit], ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [EXISTS_TAC (← q r"a:A") THEN ASM_REWRITE_TAC [],
        ASM_MESON_TAC [RING_UNIT_HOMOMORPHIC_IMAGE],
        EXISTS_TAC (← q r"ring_inv r a:A") THEN ASM_SIMP_TAC [RING_INV] THEN
        CONV_TAC SYM_CONV THEN
        FIRST_ASSUM (fun th => tactic_of do
          pure (ASM_SIMP_TAC [← MATCH_MP RING_HOMOMORPHISM_INV th]))]])

  let RING_ISOMORPHISM_IMAGE_UNITS ← prove
   r"!r r' (f:A->B).
        ring_isomorphism(r,r') f
        ==> IMAGE f {x | ring_unit r x} = {y | ring_unit r' y}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [ring_isomorphism, ring_isomorphisms] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"g:B->A") STRIP_ASSUME_TAC) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"y:B") THEN EQ_TAC THENL
     [ASM_MESON_TAC [RING_UNIT_HOMOMORPHIC_IMAGE],
      DISCH_TAC THEN EXISTS_TAC (← q r"(g:B->A) y") THEN
      ASM_MESON_TAC [RING_UNIT_HOMOMORPHIC_IMAGE, RING_UNIT_IN_CARRIER]])

  let ISOMORPHIC_RING_CARD_UNITS ← prove
   r"!r r'.
        (r:A ring) isomorphic_ring (r':B ring) /\ FINITE(ring_carrier r)
        ==> CARD {y | ring_unit r' y} = CARD {x | ring_unit r x}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [isomorphic_ring] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"f:A->B")) ASSUME_TAC) THEN
    FIRST_ASSUM (SUBST1_TAC o SYM o MATCH_MP RING_ISOMORPHISM_IMAGE_UNITS) THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC [IN_ELIM_THM] THEN
      ASM_MESON_TAC [RING_ISOMORPHISM_IMP_MONOMORPHISM,
                     RING_MONOMORPHISM_INJECTIVE_EQ, RING_UNIT_IN_CARRIER],
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"ring_carrier r:A->bool") THEN
      ASM_REWRITE_TAC [SUBSET, IN_ELIM_THM, RING_UNIT_IN_CARRIER]])

  let RING_UNIT_PROD_RING ← prove
   r"!(r:A ring) (r':B ring) x y.
        ring_unit (prod_ring r r') (x,y) <=> ring_unit r x /\ ring_unit r' y"
   (REWRITE_TAC [ring_unit, PROD_RING, EXISTS_PAIR_THM, IN_CROSS, PAIR_EQ] THEN
    MESON_TAC [])

  let UNIT_GROUP_PROD_RING ← prove
   r"!(r:A ring) (r':B ring).
        group_isomorphism
         (unit_group(prod_ring r r'),prod_group (unit_group r) (unit_group r'))
         I"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [GROUP_ISOMORPHISM, GROUP_HOMOMORPHISM, IMAGE_I, I_THM] THEN
    REWRITE_TAC [UNIT_GROUP, PROD_GROUP, PROD_RING] THEN
    REWRITE_TAC [EXTENSION, SUBSET, FORALL_PAIR_THM, IN_ELIM_THM, IN_CROSS,
                 RING_UNIT_PROD_RING] THEN
    MESON_TAC [])

  let CARD_UNITS_PROD_RING ← prove
   r"!(r:A ring) (r':B ring).
        FINITE(ring_carrier r) /\ FINITE(ring_carrier r')
        ==> CARD {z | ring_unit (prod_ring r r') z} =
            CARD {x | ring_unit r x} * CARD {y | ring_unit r' y}"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"{z | ring_unit (prod_ring r r') z} =
    {x:A | ring_unit r x} CROSS {y:B | ring_unit r' y}")
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_CROSS, IN_ELIM_THM,
                   RING_UNIT_PROD_RING],
      MATCH_MP_TAC CARD_CROSS THEN CONJ_TAC THEN
      MATCH_MP_TAC FINITE_SUBSET THENL
       [EXISTS_TAC (← q r"ring_carrier r:A->bool"),
        EXISTS_TAC (← q r"ring_carrier r':B->bool")] THEN
      ASM_REWRITE_TAC [SUBSET, IN_ELIM_THM, RING_UNIT_IN_CARRIER]])

  let UNIT_GROUP_PRODUCT_RING ← prove
   r"!k (r:K->A ring).
        group_isomorphism
         (unit_group(product_ring k r),product_group k (\i. unit_group(r i)))
         I"
   (← do
    let s1 ← SET_RULE (← q r"{x | x IN s} = s:(K->A)->bool")
    pure (REPEAT GEN_TAC THEN
    REWRITE_TAC [GROUP_ISOMORPHISM, GROUP_HOMOMORPHISM, IMAGE_I, I_THM] THEN
    REWRITE_TAC [UNIT_GROUP, PRODUCT_GROUP, PRODUCT_RING] THEN
    REWRITE_TAC [RING_UNIT_PRODUCT_RING, s1] THEN
    REWRITE_TAC [SUBSET_REFL] THEN MESON_TAC []))

  let UNIT_GROUP_RESTRICTED_PRODUCT_RING ← prove
   r"!k (r:K->A ring) s.
        (!i. i IN k ==> s i subring_of r i)
        ==> group_isomorphism
             (unit_group(restricted_product_ring k r s),
              restricted_product_group k (\i. unit_group(r i))
               (\i. {x | ring_unit (subring_generated (r i) (s i)) x})) I"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"group_carrier(restricted_product_group k (\i. unit_group((r:K->A ring) i))
      (\i. {x | ring_unit (subring_generated (r i) (s i)) x})) =
    group_carrier(unit_group(restricted_product_ring k r s))")
    ASSUME_TAC THENL
     [wPart lhand (fun t => do lhand (← rand t)) (← CONJUNCT1 RESTRICTED_PRODUCT_GROUP) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [UNIT_GROUP_SUBRING_GENERATED], DISCH_THEN SUBST1_TAC] THEN
      ASM_SIMP_TAC [UNIT_GROUP, RING_UNIT_RESTRICTED_PRODUCT_RING] THEN
      REWRITE_TAC [IN_ELIM_THM],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [GROUP_ISOMORPHISM, GROUP_HOMOMORPHISM, IMAGE_I, I_THM] THEN
    REWRITE_TAC [SUBSET_REFL, UNIT_GROUP, RESTRICTED_PRODUCT_GROUP,
                 RESTRICTED_PRODUCT_RING] THEN
    MESON_TAC [])

  -- @@RETURN BEGIN
  return { GROUP_HOMOMORPHISM_UNIT_GROUP, UNIT_GROUP_SUBRING_GENERATED,
           RING_MONOMORPHISM_UNITS_IMAGE, RING_ISOMORPHISM_IMAGE_UNITS,
           ISOMORPHIC_RING_CARD_UNITS, RING_UNIT_PROD_RING, UNIT_GROUP_PROD_RING,
           CARD_UNITS_PROD_RING, UNIT_GROUP_PRODUCT_RING,
           UNIT_GROUP_RESTRICTED_PRODUCT_RING }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Dedekind's independence of characters: distinct homomorphisms from a      -/
/- group into the units of an integral domain l are linearly independent     -/
/- over l.                                                                   -/
/- ------------------------------------------------------------------------- -/

structure UnitsIndependent where
  -- @@FIELDS
  GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT_LEMMA : thm
  GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT : thm
  GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT_SET : thm
  deriving Inhabited

@[nospecialize]
def setupUnitsIndependent [HolBase] (D : RingGroupsDeps) (BUnitGroup : UnitGroup) :
    ExceptT String IO UnitsIndependent := do
  -- @@SCOPE BEGIN
  let { RING_RULE, SET_TAC, .. } := D
  let { EQ_TRANS, FINITE_INDUCT_STRONG, FINITE_INSERT, FORALL_IN_IMAGE,
        FORALL_IN_INSERT, GROUP_HOMOMORPHISM_MUL, GROUP_HOMOMORPHISM_OF_ID, GROUP_ID,
        GROUP_MUL, INSERT_SUBSET, INTEGRAL_DOMAIN_MUL_EQ_0, IN_ELIM_THM, IN_INSERT,
        NOT_IN_EMPTY, RING_0, RING_ADD_LZERO, .. } := D.core1
  let { RING_ADD_RZERO, RING_MUL, RING_MUL_LZERO, RING_MUL_RID, RING_MUL_RZERO,
        RING_SUB, RING_SUB_EQ_0, RING_SUB_REFL, RING_SUM, RING_SUM_0, RING_SUM_CLAUSES,
        RING_SUM_EQ, RING_SUM_EQ_0, RING_SUM_LMUL, RING_SUM_SUB, RING_UNIT_IN_CARRIER,
        SUBSET, SUBSET_REFL, group_homomorphism, .. } := D.core2
  let { UNIT_GROUP, .. } := BUnitGroup
  -- @@SCOPE END

  let GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT_LEMMA ← prove
   r"!(f:K->A->B) G l s d a y.
        FINITE s /\
        (!i. i IN s ==> group_homomorphism(G,unit_group l) (f i)) /\
        (!i. i IN s ==> d i IN ring_carrier l) /\
        a IN s /\ y IN group_carrier G /\
        (!x. x IN group_carrier G
             ==> ring_sum l s (\i. ring_mul l (d i) (f i x)) = ring_0 l)
        ==> !x. x IN group_carrier G
                ==> ring_sum l s
                     (\i. ring_mul l
                           (ring_mul l (d i) (ring_sub l (f i y) (f a y)))
                           (f i x)) = ring_0 l"
   (← do
    let r1 ← RING_RULE
     (← q r"!r c u v w:B.
        c IN ring_carrier r /\ u IN ring_carrier r /\
        v IN ring_carrier r /\ w IN ring_carrier r
        ==> ring_mul r (ring_mul r c (ring_sub r u v)) w =
            ring_sub r (ring_mul r c (ring_mul r u w))
                       (ring_mul r v (ring_mul r c w))")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"!i x. i IN s /\ x IN group_carrier G
          ==> (f:K->A->B) i x IN ring_carrier l /\
              ring_mul l (d i) (f i x) IN ring_carrier l")
    ASSUME_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q r"i:K", ← q r"z:A"] THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"(f:K->A->B) i z IN ring_carrier l")
        (fun th => ASM_SIMP_TAC [th, RING_MUL]) THEN
      SUBGOAL_THEN (← q r"group_homomorphism(G,unit_group l) ((f:K->A->B) i)")
      MP_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN
      REWRITE_TAC [group_homomorphism, SUBSET, FORALL_IN_IMAGE] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"z:A") o CONJUNCT1) THEN
      ASM_SIMP_TAC [UNIT_GROUP, IN_ELIM_THM, RING_UNIT_IN_CARRIER],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"group_mul G (y:A) x IN group_carrier G") ASSUME_TAC THENL
     [ASM_SIMP_TAC [GROUP_MUL], ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     (← q r"ring_sum l s
      (\i. ring_sub l (ring_mul l (d i) ((f:K->A->B) i (group_mul G y x)))
                      (ring_mul l (f a y) (ring_mul l (d i) (f i x))))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN
      REWRITE_TAC [] THEN
      SUBGOAL_THEN
       (← q r"(f:K->A->B) i (group_mul G y x) = ring_mul l (f i y) (f i x)")
      SUBST1_TAC THENL
       [SUBGOAL_THEN (← q r"group_homomorphism(G,unit_group l) ((f:K->A->B) i)")
        MP_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN
        DISCH_THEN (fun th => tactic_of do
          pure (ASM_SIMP_TAC [← MATCH_MP GROUP_HOMOMORPHISM_MUL th]))
          THEN
        REWRITE_TAC [UNIT_GROUP],
        ALL_TAC] THEN
      MATCH_MP_TAC r1 THEN
      ASM_SIMP_TAC [],
      ASM_SIMP_TAC [RING_SUM_SUB, RING_SUM_LMUL, RING_MUL, RING_MUL_RZERO,
                    RING_SUB_REFL, RING_0]]))

  let GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT ← prove
   r"!(f:K->A->B) G l s c.
        integral_domain l /\ FINITE s /\
        (!i. i IN s ==> group_homomorphism(G,unit_group l) (f i)) /\
        (!i j. i IN s /\ j IN s /\ ~(i = j)
               ==> ?x. x IN group_carrier G /\ ~(f i x = f j x)) /\
        (!i. i IN s ==> c i IN ring_carrier l) /\
        (!x. x IN group_carrier G
             ==> ring_sum l s (\i. ring_mul l (c i) (f i x)) = ring_0 l)
        ==> !i. i IN s ==> c i = ring_0 l"
   (REPEAT GEN_TAC THEN DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN
     (← q r"!t. FINITE t
        ==> t SUBSET (s:K->bool)
            ==> !d. (!i. i IN t ==> d i IN ring_carrier l) /\
                    (!x. x IN group_carrier G
                         ==> ring_sum l t
                               (\i. ring_mul l (d i) ((f:K->A->B) i x)) =
                             ring_0 l)
                    ==> !i. i IN t ==> d i = ring_0 l")
     (fun th => tactic_of do
       pure (MP_TAC (← SPEC (← q r"s:K->bool") th) THEN
             ASM_REWRITE_TAC [SUBSET_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
             ASM_REWRITE_TAC [])) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [NOT_IN_EMPTY, INSERT_SUBSET] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:K", ← q r"t:K->bool"] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    DISCH_THEN (fun ih => tactic_of do
      pure (STRIP_TAC THEN X_GEN_TAC (← q r"d:K->B") THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sum")) THEN
        MP_TAC (← MP ih (← ASSUME (← q r"(t:K->bool) SUBSET s"))))) THEN
    SUBGOAL_THEN
     (← q r"!i. i IN a INSERT t
        ==> group_homomorphism(G,unit_group l) ((f:K->A->B) i)")
    ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!i x. i IN a INSERT t /\ x IN group_carrier G
          ==> (f:K->A->B) i x IN ring_carrier l")
    ASSUME_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q r"i:K", ← q r"z:A"] THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"group_homomorphism(G,unit_group l) ((f:K->A->B) i)")
      MP_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN
      REWRITE_TAC [group_homomorphism, SUBSET, FORALL_IN_IMAGE] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"z:A") o CONJUNCT1) THEN
      ASM_SIMP_TAC [UNIT_GROUP, IN_ELIM_THM, RING_UNIT_IN_CARRIER],
      ALL_TAC] THEN
    DISCH_THEN (fun ih => tactic_of do
      pure (SUBGOAL_THEN (← q r"!i. i IN t ==> (d:K->B) i = ring_0 l") ASSUME_TAC THENL
       [X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPECL [← q r"i:K", ← q r"a:K"]) THEN
        ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"y:A") STRIP_ASSUME_TAC) THEN
        MP_TAC (← SPEC
         (← q r"\j. ring_mul l (d j) (ring_sub l ((f:K->A->B) j y) (f a y))") ih) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC [RING_MUL, RING_SUB, IN_INSERT] THEN
          X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN
          MP_TAC (← ISPECL [← q r"f:K->A->B", ← q r"G:A group", ← q r"l:B ring",
                            ← q r"(a:K) INSERT t", ← q r"d:K->B", ← q r"a:K", ← q r"y:A"]
              GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT_LEMMA) THEN
          ASM_SIMP_TAC [FINITE_INSERT, IN_INSERT] THEN
          DISCH_THEN (MP_TAC o SPEC (← q r"x:A")) THEN
          ASM_SIMP_TAC [RING_SUM_CLAUSES, RING_MUL, RING_SUB, RING_0, IN_INSERT,
                        RING_SUB_REFL, RING_MUL_LZERO, RING_MUL_RZERO,
                        RING_ADD_LZERO, RING_SUM],
          DISCH_THEN (MP_TAC o SPEC (← q r"i:K")) THEN
          ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0, RING_SUB, RING_SUB_EQ_0,
                        IN_INSERT]],
        ALL_TAC])) THEN
    ASM_REWRITE_TAC [FORALL_IN_INSERT] THEN
    SUBGOAL_THEN
     (← q r"ring_sum l t
      (\i. ring_mul l (d i) ((f:K->A->B) i (group_id G))) =
    ring_0 l")
    ASSUME_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ_0 THEN
      ASM_SIMP_TAC [RING_MUL_LZERO, GROUP_ID, IN_INSERT],
      ALL_TAC] THEN
    REMOVE_THEN "sum" (MP_TAC o SPEC (← q r"group_id G:A")) THEN
    SUBGOAL_THEN (← q r"group_homomorphism(G,unit_group l) ((f:K->A->B) a)")
    MP_TAC THENL [ASM_SIMP_TAC [IN_INSERT], ALL_TAC] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (ASM_SIMP_TAC [RING_SUM_CLAUSES, RING_MUL, GROUP_ID,
        IN_INSERT, RING_MUL_LZERO, RING_SUM_0, RING_ADD_RZERO, RING_MUL_RID,
        ← REWRITE_RULE [UNIT_GROUP] (← MATCH_MP GROUP_HOMOMORPHISM_OF_ID th)])))

  let GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT_SET ← prove
   r"!G l:B ring s c.
        integral_domain l /\ FINITE s /\
        (!f. f IN s ==> group_homomorphism(G,unit_group l) f) /\
        (!f g. f IN s /\ g IN s /\ ~(f = g)
               ==> ?x:A. x IN group_carrier G /\ ~(f x = g x)) /\
        (!f. f IN s ==> c f IN ring_carrier l) /\
        (!x. x IN group_carrier G
             ==> ring_sum l s (\f. ring_mul l (c f) (f x)) = ring_0 l)
        ==> !f. f IN s ==> c f = ring_0 l"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"\f:A->B. f", ← q r"G:A group", ← q r"l:B ring", ← q r"s:(A->B)->bool",
                      ← q r"c:(A->B)->B"] GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT) THEN
    REWRITE_TAC [])

  -- @@RETURN BEGIN
  return { GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT_LEMMA,
           GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT,
           GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT_SET }
  -- @@RETURN END

end HolLibrary.RingGroups
