/- ========================================================================= -/
/- Topological groups and profinite groups.                                  -/
/- ========================================================================= -/
/- File: HolMultiLib/ProfiniteGroups.lean

  Original (c) Copyright, John Harrison 1998-2008 (see profinite_groups.ml).
  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/profinite_groups.ml`, in the style of
  HolMultiLib/Measure.lean: pure, the proofs translated by hand, one `let`
  per OCaml `let`, in file order.  The load-time effects are at their file
  positions.  What profinite_groups.ml uses from earlier files is passed in `ProfiniteGroupsDeps`.
  SessionMultiLib/ProfiniteGroups.lean supplies it.
-/

import HolMultiLib.Metric

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolMultiLib.ProfiniteGroups

/- The theorems profinite_groups.ml uses that the deps chain does not carry, grouped by the
   file that proves them. -/

structure QMetricThms where
  (CLOSED_COMPACT_IN closed_in CLOSED_IN_COMPACT_SPACE
   CLOSED_IN_CONTINUOUS_MAP_PREIMAGE CLOSED_IN_CONTINUOUS_MAPS_EQ CLOSED_IN_DIFF
   CLOSED_IN_INTERS CLOSED_IN_POINTWISE_PRODUCT CLOSED_IN_POINTWISE_TOPOLOGY_AGREE
   CLOSED_IN_QUOTIENT_TOPOLOGY CLOSED_IN_SUBSET CLOSED_IN_TOPSPACE CLOSED_IN_UNIONS
   CLOSURE_OF_CROSS CLOSURE_OF_MONO CLOSURE_OF_SUBSET CLOSURE_OF_SUBSET_TOPSPACE
   COMPACT_IMP_LOCALLY_COMPACT_SPACE compact_in COMPACT_IN_CARTESIAN_PRODUCT
   COMPACT_IN_DISCRETE_TOPOLOGY compact_space COMPACT_SPACE_DISCRETE_TOPOLOGY
   COMPACT_SPACE_FIP COMPACT_SPACE_PRODUCT_TOPOLOGY COMPACT_SPACE_QUOTIENT_MAP_IMAGE
   COMPACT_SPACE_SUBTOPOLOGY CONNECTED_COMPONENT_IN_CONNECTED_COMPONENTS_OF
   CONNECTED_COMPONENT_OF_REFL CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE
   CONNECTED_IN_CLOPEN_CASES CONNECTED_IN_CONNECTED_COMPONENT_OF
   CONTINUOUS_CLOSED_IMP_QUOTIENT_MAP CONTINUOUS_COMPOSE_QUOTIENT_MAP
   CONTINUOUS_IMP_CLOSED_MAP CONTINUOUS_IMP_HOMEOMORPHIC_MAP CONTINUOUS_MAP
   CONTINUOUS_MAP_COMPONENTWISE CONTINUOUS_MAP_COMPOSE CONTINUOUS_MAP_CONST
   CONTINUOUS_MAP_EQ CONTINUOUS_MAP_FROM_DISCRETE_TOPOLOGY
   CONTINUOUS_MAP_FROM_SUBTOPOLOGY CONTINUOUS_MAP_FST CONTINUOUS_MAP_ID
   CONTINUOUS_MAP_IMAGE_CLOSURE_SUBSET CONTINUOUS_MAP_IN_SUBTOPOLOGY
   CONTINUOUS_MAP_INTO_DISCRETE_TOPOLOGY_FIBRES CONTINUOUS_MAP_PAIRED
   CONTINUOUS_MAP_PAIRWISE CONTINUOUS_MAP_POINTWISE_TOPOLOGY CONTINUOUS_MAP_PROD
   CONTINUOUS_MAP_PRODUCT_PROJECTION CONTINUOUS_MAP_QUOTIENT_TOPOLOGY
   CONTINUOUS_MAP_SND CONTINUOUS_OPEN_IMP_QUOTIENT_MAP FINITE_IMP_COMPACT_IN
   FINITE_T1_SPACE_IMP_DISCRETE_TOPOLOGY HAUSDORFF_IMP_T1_SPACE
   HAUSDORFF_SPACE_CLOSED_IN_DIAGONAL HAUSDORFF_SPACE_DISCRETE_TOPOLOGY
   HAUSDORFF_SPACE_POINTWISE_TOPOLOGY HAUSDORFF_SPACE_PRODUCT_TOPOLOGY
   HAUSDORFF_SPACE_SUBTOPOLOGY HOMEOMORPHIC_COMPACT_SPACE
   HOMEOMORPHIC_HAUSDORFF_SPACE HOMEOMORPHIC_IMP_CONTINUOUS_MAP
   HOMEOMORPHIC_MAP_CLOSEDNESS HOMEOMORPHIC_MAP_CLOSURE_OF
   HOMEOMORPHIC_MAP_IMP_HOMEOMORPHIC_SPACE HOMEOMORPHIC_MAP_MAPS
   HOMEOMORPHIC_MAP_OPENNESS homeomorphic_maps neighbourhood_base_at
   OPEN_IN_CARTESIAN_PRODUCT_GEN OPEN_IN_CONTINUOUS_MAP_PREIMAGE OPEN_IN_CROSS
   OPEN_IN_DIFF OPEN_IN_DISCRETE_TOPOLOGY OPEN_IN_EMPTY OPEN_IN_INTER OPEN_IN_INTERS
   OPEN_IN_POINTWISE_TOPOLOGY_AGREE OPEN_IN_POINTWISE_TOPOLOGY_POINT
   OPEN_IN_PROD_TOPOLOGY_ALT OPEN_IN_PRODUCT_TOPOLOGY_ALT OPEN_IN_QUOTIENT_TOPOLOGY
   OPEN_IN_SUBOPEN OPEN_IN_SUBSET OPEN_IN_SUBTOPOLOGY OPEN_IN_SUBTOPOLOGY_REFL
   OPEN_IN_TOPSPACE OPEN_IN_UNIONS open_map OPEN_MAP_PROD pointwise_topology
   POINTWISE_TOPOLOGY_NEIGHBOURHOOD PROD_TOPOLOGY_DISCRETE_TOPOLOGY quotient_map
   QUOTIENT_MAP_QUOTIENT_TOPOLOGY T1_SPACE_CLOSED_IN_SING TOPOLOGY_EQ
   TOPSPACE_DISCRETE_TOPOLOGY TOPSPACE_POINTWISE_TOPOLOGY TOPSPACE_PROD_TOPOLOGY
   TOPSPACE_PRODUCT_TOPOLOGY TOPSPACE_QUOTIENT_TOPOLOGY TOPSPACE_SUBTOPOLOGY
   WILDER_LOCALLY_COMPACT_COMPONENT_THM : thm)
  deriving Inhabited

structure QGroupTheoryThms where
  (CARD_EQ_LEFT_COSETS_GROUP_COSETS CARRIER_NORMAL_SUBGROUP_OF
   CARRIER_SUBGROUP_GENERATED_SUBGROUP CARRIER_SUBGROUP_OF
   CARTESIAN_PRODUCT_NORMAL_SUBGROUP_OF_PRODUCT_GROUP FINITE_INTEGER_MOD_GROUP
   FIRST_GROUP_ISOMORPHISM_THEOREM_GEN GROUP_ACTION_KERNEL_POINTWISE
   GROUP_ACTION_LEFT_COSET_MULTIPLICATION group_conjugation group_cosets GROUP_DIV
   group_div GROUP_DIV_EQ_ID group_epimorphism GROUP_EPIMORPHISM_IMP_HOMOMORPHISM
   GROUP_EPIMORPHISM_RIGHT_COSET GROUP_HOMOMORPHISM group_homomorphism
   GROUP_HOMOMORPHISM_INTEGER_MOD_GROUP_REM GROUP_ID GROUP_INV GROUP_INV_ID
   GROUP_INV_INV GROUP_INV_MUL GROUP_ISOMORPHISM group_kernel GROUP_MUL
   GROUP_MUL_ASSOC GROUP_MUL_LID GROUP_MUL_LINV GROUP_MUL_RID GROUP_MUL_RINV
   GROUP_SETMUL_INC GROUP_SETMUL_NORMAL_SUBGROUP GROUP_SETMUL_NORMAL_SUBGROUP_RIGHT
   GROUP_STABILIZER_LEFT_COSET_MULTIPLICATION IN_GROUP_SETMUL IN_RIGHT_COSET_SELF
   IN_SUBGROUP_ID IN_SUBGROUP_INV IN_SUBGROUP_MUL INTEGER_MOD_GROUP_1R
   INVERSE_LIMIT_GROUP inverse_limit_group INVERSE_LIMIT_SUBGROUP_OF_PRODUCT_GROUP
   ISOMORPHIC_GROUP_SYM LEFT_COSET_AS_IMAGE LEFT_COSET_ID
   NORMAL_SUBGROUP_ACTION_KERNEL NORMAL_SUBGROUP_CONJUGATION
   NORMAL_SUBGROUP_IMP_SUBGROUP NORMAL_SUBGROUP_INTER_SUBGROUP_GENERATED
   normal_subgroup_of NORMAL_SUBGROUP_OF_EPIMORPHIC_IMAGE
   NORMAL_SUBGROUP_OF_HOMOMORPHIC_PREIMAGE NORMAL_SUBGROUP_OF_INTERS
   NORMAL_SUBGROUP_QUOTIENT_GROUP_IMAGE PROD_GROUP PRODUCT_GROUP QUOTIENT_GROUP
   QUOTIENT_GROUP_CARRIER QUOTIENT_GROUP_ID QUOTIENT_GROUP_INV QUOTIENT_GROUP_MUL
   RIGHT_COSET RIGHT_COSET_AS_IMAGE RIGHT_COSET_EQ RIGHT_COSET_EQ_SUBGROUP
   RIGHT_COSET_ID RIGHT_COSET_PREIMAGE RIGHT_COSETS_EQ
   SUBGROUP_COMPLEMENT_RIGHT_COSETS SUBGROUP_GENERATED SUBGROUP_GROUP_KERNEL
   subgroup_of SUBGROUP_OF_IMP_SUBSET THIRD_GROUP_ISOMORPHISM_THEOREM
   TRIVIAL_NORMAL_SUBGROUP_OF UNIONS_RIGHT_COSETS : thm)
  deriving Inhabited

structure QSymmetricGroupThms where
  (SYMMETRIC_GROUP : thm)
  deriving Inhabited

structure QPermutationsThms where
  (permutes PERMUTES_IN_IMAGE PERMUTES_INJECTIVE PERMUTES_INVERSE_EQ
   PERMUTES_INVERSES : thm)
  deriving Inhabited

structure QSessionThms where
  (SURJECTIVE_IFF_INJECTIVE : thm)
  deriving Inhabited

structure ProfiniteGroupsDeps where
  mt : HolMultiLib.Metric.MetricDeps
  -- theorems
  qmetric : QMetricThms
  qgrouptheory : QGroupTheoryThms
  qsymmetricgroup : QSymmetricGroupThms
  qpermutations : QPermutationsThms
  qsession : QSessionThms


/- ------------------------------------------------------------------------- -/
/- Topological groups: translations and inversion are homeomorphisms, open   -/
/- and closed subgroups, closures of subgroups, Hausdorff iff {1} closed,    -/
/- and transfer along homeomorphic isomorphisms.  (profinite_groups.ml       -/
/- 98-408)                                                                   -/
/- ------------------------------------------------------------------------- -/

structure PGA where
  topological_group : thm
  CONTINUOUS_MAP_GROUP_MUL : thm
  CONTINUOUS_MAP_GROUP_INV : thm
  TOPOLOGICAL_GROUP_HOMEOMORPHIC_MAPS : thm
  OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES : thm
  CLOSED_IN_TOPOLOGICAL_GROUP_TRANSLATES : thm
  CLOSED_IN_OPEN_SUBGROUP : thm
  OPEN_IN_CLOSED_SUBGROUP_FINITE_INDEX : thm
  OPEN_IN_SUBGROUP_NEIGHBOURHOOD : thm
  SUBGROUP_OF_CLOSURE_OF : thm
  NORMAL_SUBGROUP_OF_CLOSURE_OF : thm
  TOPOLOGICAL_GROUP_DISCRETE_TOPOLOGY : thm
  HAUSDORFF_SPACE_TOPOLOGICAL_GROUP : thm
  TOPOLOGICAL_GROUP_HOMEOMORPHIC_ISOMORPHISM : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPGA [HolBase] (D : ProfiniteGroupsDeps) : ExceptT String IO PGA := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, new_definition, SET_RULE, SET_TAC, .. } := D.mt
  let { closed_in, CLOSED_IN_CONTINUOUS_MAP_PREIMAGE, CLOSED_IN_SUBSET, CLOSED_IN_UNIONS,
        CLOSURE_OF_CROSS, CLOSURE_OF_MONO, CLOSURE_OF_SUBSET, CLOSURE_OF_SUBSET_TOPSPACE,
        CONTINUOUS_MAP_COMPOSE, CONTINUOUS_MAP_CONST, CONTINUOUS_MAP_EQ,
        CONTINUOUS_MAP_FROM_DISCRETE_TOPOLOGY, CONTINUOUS_MAP_FST, CONTINUOUS_MAP_ID,
        CONTINUOUS_MAP_IMAGE_CLOSURE_SUBSET, CONTINUOUS_MAP_PAIRED, CONTINUOUS_MAP_SND,
        HAUSDORFF_IMP_T1_SPACE, HAUSDORFF_SPACE_CLOSED_IN_DIAGONAL,
        HOMEOMORPHIC_MAP_CLOSEDNESS, HOMEOMORPHIC_MAP_CLOSURE_OF, HOMEOMORPHIC_MAP_MAPS,
        HOMEOMORPHIC_MAP_OPENNESS, homeomorphic_maps, OPEN_IN_DIFF, OPEN_IN_SUBSET,
        OPEN_IN_TOPSPACE, OPEN_IN_UNIONS, PROD_TOPOLOGY_DISCRETE_TOPOLOGY,
        T1_SPACE_CLOSED_IN_SING, TOPSPACE_DISCRETE_TOPOLOGY, TOPSPACE_PROD_TOPOLOGY,
        .. } := D.qmetric
  let { group_cosets, group_div, GROUP_DIV_EQ_ID, group_homomorphism, GROUP_ID, GROUP_INV,
        GROUP_INV_INV, GROUP_ISOMORPHISM, GROUP_MUL, GROUP_MUL_ASSOC, GROUP_MUL_LID,
        GROUP_MUL_LINV, GROUP_MUL_RID, GROUP_MUL_RINV, LEFT_COSET_AS_IMAGE,
        NORMAL_SUBGROUP_IMP_SUBGROUP, normal_subgroup_of, RIGHT_COSET_AS_IMAGE,
        SUBGROUP_COMPLEMENT_RIGHT_COSETS, subgroup_of, SUBGROUP_OF_IMP_SUBSET,
        .. } := D.qgrouptheory
  let { ETA_AX, EXTENSION, FINITE_SUBSET, FORALL_IN_GSPEC, FORALL_IN_IMAGE,
        .. } := D.mt.core1
  let { IN_CROSS, IN_DIFF, IN_ELIM_THM, IN_IMAGE, IN_SING, IN_UNIONS, LEFT_IMP_EXISTS_THM,
        .. } := D.mt.core2
  let { o_DEF, SUBSET, .. } := D.mt.core4
  let { FORALL_PAIR_THM, FST, LEFT_AND_EXISTS_THM, PAIR_EQ, SND, .. } := D.mt.core5
  -- @@SCOPE END

  let topological_group ← new_definition
   r"topological_group (G:A group) (top:A topology) <=>
        topspace top = group_carrier G /\
        continuous_map (prod_topology top top,top)
                       (\z. group_mul G (FST z) (SND z)) /\
        continuous_map (top,top) (group_inv G)"

  let CONTINUOUS_MAP_GROUP_MUL ← prove
   r"!G (top:A topology) (top':B topology) f g.
        topological_group G top /\
        continuous_map (top',top) f /\ continuous_map (top',top) g
        ==> continuous_map (top',top) (\x. group_mul G (f x) (g x))"
   (REWRITE_TAC [topological_group] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"(\x. group_mul G ((f:B->A) x) (g x)) =
      (\z. group_mul G (FST z) (SND z)) o (\x. f x,g x)")
    SUBST1_TAC THENL [REWRITE_TAC [o_DEF], ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC (← q r"prod_topology (top:A topology) top") THEN
    ASM_REWRITE_TAC [CONTINUOUS_MAP_PAIRED])

  let CONTINUOUS_MAP_GROUP_INV ← prove
   r"!G (top:A topology) (top':B topology) f.
        topological_group G top /\ continuous_map (top',top) f
        ==> continuous_map (top',top) (\x. group_inv G (f x))"
   (REWRITE_TAC [topological_group] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(\x. group_inv G ((f:B->A) x)) = group_inv G o f")
    SUBST1_TAC THENL [REWRITE_TAC [o_DEF], ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC (← q r"top:A topology") THEN ASM_REWRITE_TAC [])

  let TOPOLOGICAL_GROUP_HOMEOMORPHIC_MAPS ← prove
   r"!G (top:A topology) a.
        topological_group G top /\ a IN group_carrier G
        ==> homeomorphic_map (top,top) (group_mul G a) /\
            homeomorphic_map (top,top) (\x. group_mul G x a) /\
            homeomorphic_map (top,top) (group_inv G)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [topological_group]) THEN
    SUBGOAL_THEN
     (← q r"!b. b IN group_carrier G
          ==> continuous_map (top,top) (group_mul G b) /\
              continuous_map (top,top) (\x:A. group_mul G x b)")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"b:A") THEN DISCH_TAC THEN CONJ_TAC THENL
       [MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"top:A topology",
                          ← q r"\x:A. b:A", ← q r"\x:A. x"] CONTINUOUS_MAP_GROUP_MUL),
        MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"top:A topology",
                          ← q r"\x:A. x", ← q r"\x:A. b:A"] CONTINUOUS_MAP_GROUP_MUL)] THEN
      ASM_REWRITE_TAC [CONTINUOUS_MAP_ID, CONTINUOUS_MAP_CONST, ETA_AX],
      ALL_TAC] THEN
    REWRITE_TAC [HOMEOMORPHIC_MAP_MAPS, homeomorphic_maps] THEN
    ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC (← q r"group_mul G (group_inv G a):A->A"),
      EXISTS_TAC (← q r"\x:A. group_mul G x (group_inv G a)"),
      EXISTS_TAC (← q r"group_inv G:A->A")] THEN
    ASM_SIMP_TAC [GROUP_INV, GROUP_INV_INV] THEN
    ASM_SIMP_TAC [GROUP_MUL_ASSOC, GROUP_MUL_LINV, GROUP_MUL_RINV,
                  GROUP_MUL_LID, GROUP_INV, GROUP_MUL] THEN
    ASM_SIMP_TAC [← GSYM GROUP_MUL_ASSOC, GROUP_MUL_LINV, GROUP_MUL_RINV,
                  GROUP_MUL_RID, GROUP_INV])

  let OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES ← prove
   r"!G (top:A topology) a u.
        topological_group G top /\ a IN group_carrier G /\ open_in top u
        ==> open_in top (left_coset G a u) /\
            open_in top (right_coset G u a) /\
            open_in top (IMAGE (group_inv G) u)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"a:A"]
                     TOPOLOGICAL_GROUP_HOMEOMORPHIC_MAPS) THEN
    ASM_REWRITE_TAC [LEFT_COSET_AS_IMAGE, RIGHT_COSET_AS_IMAGE] THEN
    ASM_MESON_TAC [HOMEOMORPHIC_MAP_OPENNESS])

  let CLOSED_IN_TOPOLOGICAL_GROUP_TRANSLATES ← prove
   r"!G (top:A topology) a c.
        topological_group G top /\ a IN group_carrier G /\ closed_in top c
        ==> closed_in top (left_coset G a c) /\
            closed_in top (right_coset G c a) /\
            closed_in top (IMAGE (group_inv G) c)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP CLOSED_IN_SUBSET) THEN
    MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"a:A"]
                     TOPOLOGICAL_GROUP_HOMEOMORPHIC_MAPS) THEN
    ASM_REWRITE_TAC [LEFT_COSET_AS_IMAGE, RIGHT_COSET_AS_IMAGE] THEN
    ASM_MESON_TAC [HOMEOMORPHIC_MAP_CLOSEDNESS])

  let CLOSED_IN_OPEN_SUBGROUP ← prove
   r"!G (top:A topology) h.
        topological_group G top /\ h subgroup_of G /\ open_in top h
        ==> closed_in top h"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
    THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
    ASM_REWRITE_TAC [closed_in] THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP SUBGROUP_COMPLEMENT_RIGHT_COSETS) THEN
    MATCH_MP_TAC OPEN_IN_UNIONS THEN
    REWRITE_TAC [FORALL_IN_GSPEC, IN_DIFF] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES])

  let OPEN_IN_CLOSED_SUBGROUP_FINITE_INDEX ← prove
   r"!G (top:A topology) h.
        topological_group G top /\ h subgroup_of G /\ closed_in top h /\
        FINITE(group_cosets G h)
        ==> open_in top h"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
    THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
    SUBGOAL_THEN (← q r"h = topspace top DIFF (group_carrier G DIFF h:A->bool)")
    SUBST1_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC [OPEN_IN_TOPSPACE] THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP SUBGROUP_COMPLEMENT_RIGHT_COSETS) THEN
    MATCH_MP_TAC CLOSED_IN_UNIONS THEN
    REWRITE_TAC [FORALL_IN_GSPEC, IN_DIFF] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC (← q r"group_cosets G (h:A->bool)") THEN
      ASM_REWRITE_TAC [group_cosets] THEN SET_TAC [],
      REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC [CLOSED_IN_TOPOLOGICAL_GROUP_TRANSLATES]])

  let OPEN_IN_SUBGROUP_NEIGHBOURHOOD ← prove
   r"!G (top:A topology) h w.
        topological_group G top /\ h subgroup_of G /\
        open_in top w /\ group_id G IN w /\ w SUBSET h
        ==> open_in top h"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
    SUBGOAL_THEN (← q r"h = UNIONS {left_coset G x w | x | (x:A) IN h}")
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC [IN_UNIONS, IN_ELIM_THM, LEFT_COSET_AS_IMAGE, IN_IMAGE] THEN
      X_GEN_TAC (← q r"y:A") THEN EQ_TAC THENL
       [DISCH_TAC THEN EXISTS_TAC (← q r"IMAGE (group_mul G y) (w:A->bool)") THEN
        CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        REWRITE_TAC [IN_IMAGE] THEN
        EXISTS_TAC (← q r"group_id G:A") THEN ASM_REWRITE_TAC [] THEN
        ASM_MESON_TAC [GROUP_MUL_RID, SUBSET],
        REWRITE_TAC [LEFT_IMP_EXISTS_THM, LEFT_AND_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [← q r"c:A->bool", ← q r"x:A"] THEN STRIP_TAC THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN
        FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"z:A") STRIP_ASSUME_TAC o
          GEN_REWRITE_RULE I [IN_IMAGE]) THEN
        ASM_MESON_TAC [subgroup_of, SUBSET]],
      MATCH_MP_TAC OPEN_IN_UNIONS THEN
      REWRITE_TAC [FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"x:A", ← q r"w:A->bool"]
                       OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES) THEN
      ASM_SIMP_TAC [] THEN ASM_MESON_TAC [SUBSET]])

  let SUBGROUP_OF_CLOSURE_OF ← prove
   r"!G (top:A topology) h.
        topological_group G top /\ h subgroup_of G
        ==> (top closure_of h) subgroup_of G"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [topological_group]) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [subgroup_of]) THEN
    SUBGOAL_THEN (← q r"(h:A->bool) SUBSET top closure_of h") ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    REWRITE_TAC [subgroup_of] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [CLOSURE_OF_SUBSET_TOPSPACE],
      ASM SET_TAC [],
      MP_TAC (← ISPECL [← q r"top:A topology", ← q r"top:A topology", ← q r"group_inv G:A->A",
                        ← q r"h:A->bool"] CONTINUOUS_MAP_IMAGE_CLOSURE_SUBSET) THEN
      ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC (← SET_RULE
       (← q r"(t:A->bool) SUBSET u
        ==> IMAGE (f:A->A) s SUBSET t ==> !x. x IN s ==> f x IN u")) THEN
      MATCH_MP_TAC CLOSURE_OF_MONO THEN ASM SET_TAC [],
      MP_TAC (← ISPECL [← q r"prod_topology (top:A topology) top", ← q r"top:A topology",
                        ← q r"\z. group_mul G (FST z) (SND z):A",
                        ← q r"(h:A->bool) CROSS h"]
                       CONTINUOUS_MAP_IMAGE_CLOSURE_SUBSET) THEN
      ASM_REWRITE_TAC [CLOSURE_OF_CROSS] THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_PAIR_THM, IN_CROSS] THEN
      DISCH_TAC THEN MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"top closure_of (IMAGE (\z. group_mul G (FST z) (SND z))
                              ((h:A->bool) CROSS h)) SUBSET
        top closure_of h")
      MP_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_MONO THEN
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_PAIR_THM, IN_CROSS] THEN
        ASM_SIMP_TAC [],
        REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPECL [← q r"x:A", ← q r"y:A"]) THEN
        ASM_REWRITE_TAC []]])

  let NORMAL_SUBGROUP_OF_CLOSURE_OF ← prove
   r"!G (top:A topology) h.
        topological_group G top /\ h normal_subgroup_of G
        ==> (top closure_of h) normal_subgroup_of G"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
    THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
    REWRITE_TAC [normal_subgroup_of] THEN
    ASM_SIMP_TAC [SUBGROUP_OF_CLOSURE_OF] THEN
    X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"a:A"]
                     TOPOLOGICAL_GROUP_HOMEOMORPHIC_MAPS) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    REWRITE_TAC [LEFT_COSET_AS_IMAGE, RIGHT_COSET_AS_IMAGE] THEN
    MP_TAC (← ISPECL [← q r"group_mul G a:A->A", ← q r"top:A topology", ← q r"top:A topology",
                      ← q r"h:A->bool"] HOMEOMORPHIC_MAP_CLOSURE_OF) THEN
    MP_TAC (← ISPECL [← q r"\x:A. group_mul G x a", ← q r"top:A topology",
                      ← q r"top:A topology", ← q r"h:A->bool"]
                     HOMEOMORPHIC_MAP_CLOSURE_OF) THEN
    ASM_REWRITE_TAC [] THEN REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN
    AP_TERM_TAC THEN
    REWRITE_TAC [← GSYM LEFT_COSET_AS_IMAGE, ← GSYM RIGHT_COSET_AS_IMAGE] THEN
    ASM_MESON_TAC [normal_subgroup_of])

  let TOPOLOGICAL_GROUP_DISCRETE_TOPOLOGY ← prove
   r"!G:A group. topological_group G (discrete_topology(group_carrier G))"
   (GEN_TAC THEN
    REWRITE_TAC [topological_group, TOPSPACE_DISCRETE_TOPOLOGY,
                 PROD_TOPOLOGY_DISCRETE_TOPOLOGY,
                 CONTINUOUS_MAP_FROM_DISCRETE_TOPOLOGY] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_PAIR_THM, IN_CROSS] THEN
    SIMP_TAC [GROUP_MUL, GROUP_INV])

  let HAUSDORFF_SPACE_TOPOLOGICAL_GROUP ← prove
   r"!G (top:A topology).
        topological_group G top
        ==> (hausdorff_space top <=> closed_in top {group_id G})"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
    THEN EQ_TAC THENL
     [DISCH_THEN (MP_TAC o MATCH_MP HAUSDORFF_IMP_T1_SPACE) THEN
      REWRITE_TAC [T1_SPACE_CLOSED_IN_SING] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC [GROUP_ID],
      DISCH_TAC] THEN
    REWRITE_TAC [HAUSDORFF_SPACE_CLOSED_IN_DIAGONAL] THEN
    SUBGOAL_THEN
     (← q r"{(x,x) | x IN topspace top} =
      {z | z IN topspace(prod_topology top top) /\
           (\z. group_mul G (FST z) (group_inv G (SND z))) z IN
           {group_id G:A}}")
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC [TOPSPACE_PROD_TOPOLOGY, EXTENSION, FORALL_PAIR_THM,
                       IN_ELIM_THM, IN_CROSS, IN_SING, PAIR_EQ, FST, SND] THEN
      REWRITE_TAC [← GSYM group_div] THEN
      MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN
      ASM_CASES_TAC (← q r"(x:A) IN group_carrier G /\ y IN group_carrier G") THEN
      ASM_SIMP_TAC [GROUP_DIV_EQ_ID] THEN ASM_MESON_TAC [],
      MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC (← q r"top:A topology") THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_GROUP_MUL THEN
      ASM_REWRITE_TAC [CONTINUOUS_MAP_FST] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_GROUP_INV THEN
      ASM_REWRITE_TAC [CONTINUOUS_MAP_SND]])

  let TOPOLOGICAL_GROUP_HOMEOMORPHIC_ISOMORPHISM ← prove
   r"!G H (top:A topology) (top':B topology) f.
        topological_group H top' /\ topspace top = group_carrier G /\
        group_isomorphism (G,H) f /\ homeomorphic_map (top,top') f
        ==> topological_group G top"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [topological_group]) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [GROUP_ISOMORPHISM]) THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_MAP_MAPS]) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"g:B->A") MP_TAC) THEN
    REWRITE_TAC [homeomorphic_maps] THEN STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [group_homomorphism]) THEN
    REWRITE_TAC [topological_group] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
      EXISTS_TAC
       (← q r"\z:A#A. (g:B->A) (group_mul H ((f:A->B)(FST z)) (f(SND z)))") THEN
      CONJ_TAC THENL
       [REWRITE_TAC [FORALL_PAIR_THM, TOPSPACE_PROD_TOPOLOGY, IN_CROSS] THEN
        MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN STRIP_TAC THEN
        SUBGOAL_THEN (← q r"group_mul H ((f:A->B) x) (f y) = f(group_mul G x y)")
        SUBST1_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        MAP_EVERY UNDISCH_TAC
         [← q r"(x:A) IN topspace top", ← q r"(y:A) IN topspace top"] THEN
        ASM_SIMP_TAC [GROUP_MUL],
        GEN_REWRITE_TAC RAND_CONV [← GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
        EXISTS_TAC (← q r"top':B topology") THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_GROUP_MUL THEN ASM_REWRITE_TAC [] THEN
        CONJ_TAC THEN GEN_REWRITE_TAC RAND_CONV [← GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC (← q r"top:A topology") THEN
        ASM_REWRITE_TAC [CONTINUOUS_MAP_FST, CONTINUOUS_MAP_SND]],
      MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
      EXISTS_TAC (← q r"\x. (g:B->A) (group_inv H ((f:A->B) x))") THEN CONJ_TAC THENL
       [X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN BETA_TAC THEN
        SUBGOAL_THEN (← q r"group_inv H ((f:A->B) x) = f(group_inv G x)")
        SUBST1_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC (← q r"(x:A) IN topspace top") THEN ASM_SIMP_TAC [GROUP_INV],
        GEN_REWRITE_TAC RAND_CONV [← GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
        EXISTS_TAC (← q r"top':B topology") THEN ASM_REWRITE_TAC [] THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
        EXISTS_TAC (← q r"top':B topology") THEN ASM_REWRITE_TAC []]])

  pure { topological_group, CONTINUOUS_MAP_GROUP_MUL, CONTINUOUS_MAP_GROUP_INV,
         TOPOLOGICAL_GROUP_HOMEOMORPHIC_MAPS, OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES,
         CLOSED_IN_TOPOLOGICAL_GROUP_TRANSLATES, CLOSED_IN_OPEN_SUBGROUP,
         OPEN_IN_CLOSED_SUBGROUP_FINITE_INDEX, OPEN_IN_SUBGROUP_NEIGHBOURHOOD,
         SUBGROUP_OF_CLOSURE_OF, NORMAL_SUBGROUP_OF_CLOSURE_OF,
         TOPOLOGICAL_GROUP_DISCRETE_TOPOLOGY, HAUSDORFF_SPACE_TOPOLOGICAL_GROUP,
         TOPOLOGICAL_GROUP_HOMEOMORPHIC_ISOMORPHISM }

/- ------------------------------------------------------------------------- -/
/- Homomorphisms of topological groups: continuity at 1, kernels, and open   -/
/- epimorphic images.  (profinite_groups.ml 409-586)                         -/
/- ------------------------------------------------------------------------- -/

structure PGB where
  CONTINUOUS_MAP_GROUP_HOMOMORPHISM : thm
  CONTINUOUS_MAP_GROUP_HOMOMORPHISM_DISCRETE : thm
  CLOSED_IN_GROUP_KERNEL : thm
  TOPOLOGICAL_GROUP_OPEN_EPIMORPHIC_IMAGE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPGB [HolBase] (D : ProfiniteGroupsDeps) (BPGA : PGA) : ExceptT String IO PGB := do
  -- @@SCOPE BEGIN
  let { OPEN_IN_SUBGROUP_NEIGHBOURHOOD, OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES,
        topological_group, TOPOLOGICAL_GROUP_DISCRETE_TOPOLOGY, .. } := BPGA
  let { ASM_MESON_TAC, SET_TAC, .. } := D.mt
  let { CLOSED_IN_CONTINUOUS_MAP_PREIMAGE, CONTINUOUS_COMPOSE_QUOTIENT_MAP, CONTINUOUS_MAP,
        CONTINUOUS_MAP_COMPOSE, CONTINUOUS_MAP_EQ, CONTINUOUS_MAP_PROD,
        CONTINUOUS_OPEN_IMP_QUOTIENT_MAP, HAUSDORFF_IMP_T1_SPACE,
        OPEN_IN_CONTINUOUS_MAP_PREIMAGE, OPEN_IN_DISCRETE_TOPOLOGY, OPEN_IN_SUBOPEN,
        OPEN_IN_SUBSET, OPEN_MAP_PROD, T1_SPACE_CLOSED_IN_SING, TOPSPACE_PROD_TOPOLOGY,
        .. } := D.qmetric
  let { group_epimorphism, group_homomorphism, GROUP_ID, GROUP_INV, group_kernel,
        GROUP_MUL, GROUP_MUL_ASSOC, GROUP_MUL_LID, GROUP_MUL_LINV, GROUP_MUL_RID,
        GROUP_MUL_RINV, LEFT_COSET_AS_IMAGE, SUBGROUP_GROUP_KERNEL, .. } := D.qgrouptheory
  let { ETA_AX, FORALL_IN_IMAGE, .. } := D.mt.core1
  let { IMAGE_PAIRED_CROSS, IN_CROSS, IN_ELIM_THM, IN_IMAGE, IN_SING, .. } := D.mt.core2
  let { o_THM, SING_SUBSET, SUBSET, .. } := D.mt.core4
  let { FORALL_PAIR_THM, .. } := D.mt.core5
  -- @@SCOPE END

  let CONTINUOUS_MAP_GROUP_HOMOMORPHISM ← prove
   r"!G H (top:A topology) (top':B topology) f.
        topological_group G top /\ topological_group H top' /\
        group_homomorphism(G,H) f
        ==> (continuous_map (top,top') f <=>
             !v. open_in top' v /\ group_id H IN v
                 ==> ?u. open_in top u /\ group_id G IN u /\
                         IMAGE f u SUBSET v)"
   (REPEAT STRIP_TAC THEN
    MAP_EVERY (fun t => FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o
      GEN_REWRITE_RULE I [topological_group] o check (fun th => concl th == t)))
     [← q r"topological_group G (top:A topology)",
      ← q r"topological_group H (top':B topology)"] THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o
      REWRITE_RULE [SUBSET, FORALL_IN_IMAGE] o
      GEN_REWRITE_RULE I [group_homomorphism]) THEN
    EQ_TAC THENL
     [DISCH_TAC THEN X_GEN_TAC (← q r"v:B->bool") THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"{x | x IN topspace top /\ (f:A->B) x IN v}") THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
        EXISTS_TAC (← q r"top':B topology") THEN ASM_REWRITE_TAC [],
        ASM_REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [GROUP_ID],
        SET_TAC []],
      DISCH_TAC] THEN
    REWRITE_TAC [CONTINUOUS_MAP] THEN ASM_REWRITE_TAC [] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE], ALL_TAC] THEN
    X_GEN_TAC (← q r"w:B->bool") THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC [OPEN_IN_SUBOPEN] THEN
    X_GEN_TAC (← q r"x:A") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(f:A->B) x IN group_carrier H") ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"left_coset H (group_inv H ((f:A->B) x)) w")) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC (← ISPECL [← q r"H:B group", ← q r"top':B topology",
                          ← q r"group_inv H ((f:A->B) x)", ← q r"w:B->bool"]
                         OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES) THEN
        ASM_SIMP_TAC [GROUP_INV],
        REWRITE_TAC [LEFT_COSET_AS_IMAGE, IN_IMAGE] THEN
        EXISTS_TAC (← q r"(f:A->B) x") THEN ASM_SIMP_TAC [GROUP_MUL_LINV]],
      DISCH_THEN (X_CHOOSE_THEN (← q r"u:A->bool") STRIP_ASSUME_TAC)] THEN
    -- `check (fun th -> concl th = `..`)`: the quotation is parsed at each
    -- call of the test, as in OCaml.
    FIRST_ASSUM (fun th => tactic_of do
      let t ← q r"open_in top (u:A->bool)"
      pure (ASSUME_TAC (← MATCH_MP OPEN_IN_SUBSET
        (← liftExcept (check (fun th => concl th == t) th))))) THEN
    FIRST_ASSUM (fun th => tactic_of do
      let t ← q r"open_in top' (w:B->bool)"
      pure (ASSUME_TAC (← MATCH_MP OPEN_IN_SUBSET
        (← liftExcept (check (fun th => concl th == t) th))))) THEN
    EXISTS_TAC (← q r"left_coset G x (u:A->bool)") THEN REPEAT CONJ_TAC THENL
     [MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"x:A", ← q r"u:A->bool"]
                       OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES) THEN
      ASM_SIMP_TAC [],
      REWRITE_TAC [LEFT_COSET_AS_IMAGE, IN_IMAGE] THEN
      EXISTS_TAC (← q r"group_id G:A") THEN ASM_SIMP_TAC [GROUP_MUL_RID],
      REWRITE_TAC [LEFT_COSET_AS_IMAGE, SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
      X_GEN_TAC (← q r"z:A") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"(z:A) IN group_carrier G") ASSUME_TAC THENL
       [UNDISCH_TAC (← q r"(u:A->bool) SUBSET topspace top") THEN
        ASM_REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        FIRST_ASSUM ACCEPT_TAC,
        ALL_TAC] THEN
      ASM_SIMP_TAC [GROUP_MUL] THEN
      UNDISCH_TAC
       (← q r"IMAGE (f:A->B) u SUBSET left_coset H (group_inv H (f x)) w") THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, LEFT_COSET_AS_IMAGE, IN_IMAGE] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"z:A")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"y:B") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"(y:B) IN group_carrier H") ASSUME_TAC THENL
       [UNDISCH_TAC (← q r"(w:B->bool) SUBSET topspace top'") THEN
        ASM_REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        FIRST_ASSUM ACCEPT_TAC,
        ALL_TAC] THEN
      ASM_SIMP_TAC [GROUP_MUL_ASSOC, GROUP_INV, GROUP_MUL_RINV,
                    GROUP_MUL_LID]])

  let CONTINUOUS_MAP_GROUP_HOMOMORPHISM_DISCRETE ← prove
   r"!G H (top:A topology) (f:A->B).
        topological_group G top /\ group_homomorphism(G,H) f
        ==> (continuous_map (top,discrete_topology(group_carrier H)) f <=>
             open_in top (group_kernel (G,H) f))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"G:A group", ← q r"H:B group", ← q r"top:A topology",
                      ← q r"discrete_topology(group_carrier(H:B group))", ← q r"f:A->B"]
                     CONTINUOUS_MAP_GROUP_HOMOMORPHISM) THEN
    ASM_REWRITE_TAC [TOPOLOGICAL_GROUP_DISCRETE_TOPOLOGY] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o
      GEN_REWRITE_RULE I [topological_group]) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [SUBSET, FORALL_IN_IMAGE] o
      GEN_REWRITE_RULE I [group_homomorphism]) THEN
    REWRITE_TAC [OPEN_IN_DISCRETE_TOPOLOGY] THEN EQ_TAC THENL
     [DISCH_THEN (MP_TAC o SPEC (← q r"{group_id H:B}")) THEN
      REWRITE_TAC [SING_SUBSET, IN_SING, GROUP_ID] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"u:A->bool") STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC OPEN_IN_SUBGROUP_NEIGHBOURHOOD THEN
      MAP_EVERY EXISTS_TAC [← q r"G:A group", ← q r"u:A->bool"] THEN
      ASM_SIMP_TAC [SUBGROUP_GROUP_KERNEL] THEN
      FIRST_ASSUM (fun th => tactic_of do
        let t ← q r"open_in top (u:A->bool)"
        pure (MP_TAC (← MATCH_MP OPEN_IN_SUBSET
          (← liftExcept (check (fun th => concl th == t) th))))) THEN
      UNDISCH_TAC (← q r"IMAGE (f:A->B) u SUBSET {group_id H}") THEN
      ASM_REWRITE_TAC [group_kernel] THEN SET_TAC [],
      DISCH_TAC THEN X_GEN_TAC (← q r"v:B->bool") THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"group_kernel (G,H) (f:A->B)") THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [group_kernel, IN_ELIM_THM] THEN
      ASM_REWRITE_TAC [GROUP_ID] THEN
      UNDISCH_TAC (← q r"group_id H IN (v:B->bool)") THEN SET_TAC []])

  let CLOSED_IN_GROUP_KERNEL ← prove
   r"!G H (top:A topology) (top':B topology) f.
        topological_group G top /\ topological_group H top' /\
        hausdorff_space top' /\
        group_homomorphism(G,H) f /\ continuous_map (top,top') f
        ==> closed_in top (group_kernel (G,H) f)"
   (REPEAT STRIP_TAC THEN
    MAP_EVERY (fun t => FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o
      GEN_REWRITE_RULE I [topological_group] o check (fun th => concl th == t)))
     [← q r"topological_group G (top:A topology)",
      ← q r"topological_group H (top':B topology)"] THEN
    SUBGOAL_THEN
     (← q r"group_kernel (G,H) (f:A->B) =
      {x | x IN topspace top /\ f x IN {group_id H}}")
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC [group_kernel, IN_SING],
      MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC (← q r"top':B topology") THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [T1_SPACE_CLOSED_IN_SING, HAUSDORFF_IMP_T1_SPACE,
                     GROUP_ID]])

  let TOPOLOGICAL_GROUP_OPEN_EPIMORPHIC_IMAGE ← prove
   r"!G H (top:A topology) (top':B topology) f.
        topological_group G top /\ topspace top' = group_carrier H /\
        group_epimorphism(G,H) f /\
        continuous_map (top,top') f /\ open_map (top,top') f
        ==> topological_group H top'"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [topological_group]) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [group_epimorphism]) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [group_homomorphism]) THEN
    SUBGOAL_THEN (← q r"IMAGE (f:A->B) (topspace top) = topspace top'") ASSUME_TAC THENL
     [ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"quotient_map (top,top') (f:A->B)") ASSUME_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_IMP_QUOTIENT_MAP THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [topological_group] THEN CONJ_TAC THENL
     [MATCH_MP_TAC (← ISPEC (← q r"prod_topology (top:A topology) top")
                     CONTINUOUS_COMPOSE_QUOTIENT_MAP) THEN
      EXISTS_TAC (← q r"\(x,y). (f:A->B) x,(f:A->B) y") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_OPEN_IMP_QUOTIENT_MAP THEN
        ASM_REWRITE_TAC [CONTINUOUS_MAP_PROD, OPEN_MAP_PROD, ETA_AX,
                         TOPSPACE_PROD_TOPOLOGY, IMAGE_PAIRED_CROSS],
        MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
        EXISTS_TAC (← q r"(f:A->B) o (\z:A#A. group_mul G (FST z) (SND z))") THEN
        CONJ_TAC THENL
         [ASM_SIMP_TAC [FORALL_PAIR_THM, TOPSPACE_PROD_TOPOLOGY, IN_CROSS,
                        o_THM],
          MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
          EXISTS_TAC (← q r"top:A topology") THEN ASM_REWRITE_TAC []]],
      MATCH_MP_TAC (← ISPEC (← q r"top:A topology") CONTINUOUS_COMPOSE_QUOTIENT_MAP) THEN
      EXISTS_TAC (← q r"f:A->B") THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
      EXISTS_TAC (← q r"(f:A->B) o (group_inv G:A->A)") THEN CONJ_TAC THENL
       [ASM_SIMP_TAC [o_THM],
        MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
        EXISTS_TAC (← q r"top:A topology") THEN ASM_REWRITE_TAC []]])

  pure { CONTINUOUS_MAP_GROUP_HOMOMORPHISM, CONTINUOUS_MAP_GROUP_HOMOMORPHISM_DISCRETE,
         CLOSED_IN_GROUP_KERNEL, TOPOLOGICAL_GROUP_OPEN_EPIMORPHIC_IMAGE }

/- ------------------------------------------------------------------------- -/
/- Subgroups and quotient groups of topological groups.                      -/
/- (profinite_groups.ml 588-717)                                             -/
/- ------------------------------------------------------------------------- -/

structure PGC where
  TOPOLOGICAL_GROUP_SUBGROUP : thm
  OPEN_MAP_RIGHT_COSET : thm
  TOPOLOGICAL_GROUP_QUOTIENT_GROUP : thm
  QUOTIENT_TOPOLOGY_OPEN_NORMAL_SUBGROUP : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPGC [HolBase] (D : ProfiniteGroupsDeps) (BPGA : PGA) : ExceptT String IO PGC := do
  -- @@SCOPE BEGIN
  let { CONTINUOUS_MAP_GROUP_MUL, OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES, topological_group,
        .. } := BPGA
  let { SET_TAC, .. } := D.mt
  let { CONTINUOUS_COMPOSE_QUOTIENT_MAP, CONTINUOUS_MAP_COMPOSE, CONTINUOUS_MAP_EQ,
        CONTINUOUS_MAP_FROM_SUBTOPOLOGY, CONTINUOUS_MAP_FST, CONTINUOUS_MAP_IN_SUBTOPOLOGY,
        CONTINUOUS_MAP_PROD, CONTINUOUS_MAP_QUOTIENT_TOPOLOGY, CONTINUOUS_MAP_SND,
        CONTINUOUS_OPEN_IMP_QUOTIENT_MAP, OPEN_IN_DISCRETE_TOPOLOGY,
        OPEN_IN_QUOTIENT_TOPOLOGY, OPEN_IN_SUBSET, OPEN_IN_UNIONS, open_map, OPEN_MAP_PROD,
        QUOTIENT_MAP_QUOTIENT_TOPOLOGY, TOPOLOGY_EQ, TOPSPACE_PROD_TOPOLOGY,
        TOPSPACE_QUOTIENT_TOPOLOGY, TOPSPACE_SUBTOPOLOGY, .. } := D.qmetric
  let { CARRIER_SUBGROUP_GENERATED_SUBGROUP, LEFT_COSET_AS_IMAGE,
        NORMAL_SUBGROUP_IMP_SUBGROUP, QUOTIENT_GROUP, QUOTIENT_GROUP_INV,
        QUOTIENT_GROUP_MUL, RIGHT_COSET_AS_IMAGE, RIGHT_COSET_PREIMAGE, SUBGROUP_GENERATED,
        subgroup_of, SUBGROUP_OF_IMP_SUBSET, .. } := D.qgrouptheory
  let { ETA_AX, FORALL_IN_IMAGE, .. } := D.mt.core1
  let { IMAGE_PAIRED_CROSS, IN_CROSS, IN_INTER, .. } := D.mt.core2
  let { o_THM, SUBSET, UNIONS_IMAGE, .. } := D.mt.core4
  let { FORALL_PAIR_THM, FST, SND, .. } := D.mt.core5
  -- @@SCOPE END

  let TOPOLOGICAL_GROUP_SUBGROUP ← prove
   r"!G (top:A topology) h.
        topological_group G top /\ h subgroup_of G
        ==> topological_group (subgroup_generated G h) (subtopology top h)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do
      let t ← q r"(h:A->bool) subgroup_of G"
      pure (STRIP_ASSUME_TAC (← GEN_REWRITE_RULE I [subgroup_of]
        (← liftExcept (check (fun th => concl th == t) th))))) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [topological_group]) THEN
    REWRITE_TAC [topological_group, TOPSPACE_SUBTOPOLOGY,
                 ← CONJUNCT2 SUBGROUP_GENERATED] THEN
    ASM_SIMP_TAC [CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC [],
      REWRITE_TAC [CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_GROUP_MUL THEN ASM_REWRITE_TAC [] THEN
        MP_TAC (← ISPECL [← q r"subtopology top (h:A->bool)",
                          ← q r"subtopology top (h:A->bool)"] CONTINUOUS_MAP_FST) THEN
        MP_TAC (← ISPECL [← q r"subtopology top (h:A->bool)",
                          ← q r"subtopology top (h:A->bool)"] CONTINUOUS_MAP_SND) THEN
        SIMP_TAC [CONTINUOUS_MAP_IN_SUBTOPOLOGY],
        REWRITE_TAC [TOPSPACE_PROD_TOPOLOGY, TOPSPACE_SUBTOPOLOGY, SUBSET,
                     FORALL_IN_IMAGE, FORALL_PAIR_THM, IN_CROSS, IN_INTER,
                     FST, SND] THEN
        ASM_SIMP_TAC []],
      REWRITE_TAC [CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN ASM_REWRITE_TAC [],
        REWRITE_TAC [TOPSPACE_SUBTOPOLOGY, SUBSET, FORALL_IN_IMAGE, IN_INTER] THEN
        ASM_SIMP_TAC []]])

  let OPEN_MAP_RIGHT_COSET ← prove
   r"!G (top:A topology) n.
        topological_group G top /\ n normal_subgroup_of G
        ==> open_map (top,quotient_topology (top,right_coset G n))
                     (right_coset G n)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
    THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
    REWRITE_TAC [open_map, OPEN_IN_QUOTIENT_TOPOLOGY] THEN
    X_GEN_TAC (← q r"u:A->bool") THEN DISCH_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    CONJ_TAC THENL [ASM SET_TAC [], ASM_REWRITE_TAC []] THEN
    MP_TAC (← ISPECL [← q r"G:A group", ← q r"n:A->bool",
                      ← q r"IMAGE (right_coset G n) (u:A->bool)"]
                     RIGHT_COSET_PREIMAGE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [QUOTIENT_GROUP] THEN ASM SET_TAC [],
      DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN
     (← q r"UNIONS (IMAGE (right_coset G n) (u:A->bool)) =
      UNIONS (IMAGE (\a. left_coset G a u) n)")
    SUBST1_TAC THENL
     [REWRITE_TAC [UNIONS_IMAGE, LEFT_COSET_AS_IMAGE, RIGHT_COSET_AS_IMAGE] THEN
      SET_TAC [],
      MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC [FORALL_IN_IMAGE]] THEN
    X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"(a:A) IN group_carrier G") ASSUME_TAC THENL
     [ASM SET_TAC [], ASM_SIMP_TAC [OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES]])

  let TOPOLOGICAL_GROUP_QUOTIENT_GROUP ← prove
   r"!G (top:A topology) n.
        topological_group G top /\ n normal_subgroup_of G
        ==> topological_group (quotient_group G n)
                              (quotient_topology (top,right_coset G n))"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [topological_group]) THEN
    MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"n:A->bool"]
                     OPEN_MAP_RIGHT_COSET) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"top:A topology", ← q r"right_coset G (n:A->bool)"]
                     QUOTIENT_MAP_QUOTIENT_TOPOLOGY) THEN
    DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"top:A topology", ← q r"right_coset G (n:A->bool)"]
                     CONTINUOUS_MAP_QUOTIENT_TOPOLOGY) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"IMAGE (right_coset G n) (group_carrier G) =
      group_carrier(quotient_group G (n:A->bool))")
    ASSUME_TAC THENL [ASM_SIMP_TAC [QUOTIENT_GROUP] THEN SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"topspace(quotient_topology (top,right_coset G n)) =
      group_carrier(quotient_group G (n:A->bool))")
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC [TOPSPACE_QUOTIENT_TOPOLOGY], ALL_TAC] THEN
    ASM_REWRITE_TAC [topological_group] THEN CONJ_TAC THENL
     [MATCH_MP_TAC (← ISPEC (← q r"prod_topology (top:A topology) top")
                     CONTINUOUS_COMPOSE_QUOTIENT_MAP) THEN
      EXISTS_TAC (← q r"\(x,y). right_coset G n (x:A),right_coset G n (y:A)") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_OPEN_IMP_QUOTIENT_MAP THEN
        ASM_REWRITE_TAC [CONTINUOUS_MAP_PROD, OPEN_MAP_PROD, ETA_AX,
                         TOPSPACE_PROD_TOPOLOGY, IMAGE_PAIRED_CROSS],
        MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
        EXISTS_TAC (← q r"right_coset G n o (\z:A#A. group_mul G (FST z) (SND z))") THEN
        CONJ_TAC THENL
         [ASM_SIMP_TAC [FORALL_PAIR_THM, TOPSPACE_PROD_TOPOLOGY, IN_CROSS,
                        o_THM, QUOTIENT_GROUP_MUL],
          MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
          EXISTS_TAC (← q r"top:A topology") THEN ASM_REWRITE_TAC []]],
      MATCH_MP_TAC (← ISPEC (← q r"top:A topology") CONTINUOUS_COMPOSE_QUOTIENT_MAP) THEN
      EXISTS_TAC (← q r"right_coset G (n:A->bool)") THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
      EXISTS_TAC (← q r"right_coset G n o (group_inv G:A->A)") THEN CONJ_TAC THENL
       [ASM_SIMP_TAC [o_THM, QUOTIENT_GROUP_INV],
        MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
        EXISTS_TAC (← q r"top:A topology") THEN ASM_REWRITE_TAC []]])

  let QUOTIENT_TOPOLOGY_OPEN_NORMAL_SUBGROUP ← prove
   r"!G (top:A topology) u.
        topological_group G top /\ u normal_subgroup_of G /\ open_in top u
        ==> quotient_topology (top,right_coset G u) =
            discrete_topology(group_carrier(quotient_group G u))"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
    THEN SUBGOAL_THEN
     (← q r"IMAGE (right_coset G u) (group_carrier G) =
      group_carrier(quotient_group G (u:A->bool))")
    ASSUME_TAC THENL [ASM_SIMP_TAC [QUOTIENT_GROUP] THEN SET_TAC [], ALL_TAC] THEN
    REWRITE_TAC [TOPOLOGY_EQ, OPEN_IN_QUOTIENT_TOPOLOGY,
                 OPEN_IN_DISCRETE_TOPOLOGY] THEN
    X_GEN_TAC (← q r"v:(A->bool)->bool") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"v SUBSET group_carrier(quotient_group G (u:A->bool))") THEN
    ASM_SIMP_TAC [RIGHT_COSET_PREIMAGE] THEN
    MATCH_MP_TAC OPEN_IN_UNIONS THEN
    X_GEN_TAC (← q r"X:A->bool") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"?g:A. g IN group_carrier G /\ X = right_coset G u g")
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"v SUBSET group_carrier(quotient_group G (u:A->bool))") THEN
      ASM_SIMP_TAC [QUOTIENT_GROUP] THEN ASM SET_TAC [],
      ASM_SIMP_TAC [OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES]])

  pure { TOPOLOGICAL_GROUP_SUBGROUP, OPEN_MAP_RIGHT_COSET, TOPOLOGICAL_GROUP_QUOTIENT_GROUP,
         QUOTIENT_TOPOLOGY_OPEN_NORMAL_SUBGROUP }

/- ------------------------------------------------------------------------- -/
/- Open normal subgroups of quotients, Hausdorff quotients, and products.    -/
/- (profinite_groups.ml 718-890)                                             -/
/- ------------------------------------------------------------------------- -/

structure PGD where
  OPEN_NORMAL_SUBGROUP_QUOTIENT_IMAGE : thm
  OPEN_NORMAL_SUBGROUP_QUOTIENT_PREIMAGE : thm
  HAUSDORFF_SPACE_QUOTIENT_GROUP : thm
  TOPOLOGICAL_GROUP_PRODUCT_GROUP : thm
  TOPOLOGICAL_GROUP_PROD_GROUP : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPGD [HolBase] (D : ProfiniteGroupsDeps) (BPGA : PGA) (BPGC : PGC) : ExceptT String IO PGD := do
  -- @@SCOPE BEGIN
  let { CONTINUOUS_MAP_GROUP_INV, CONTINUOUS_MAP_GROUP_MUL,
        HAUSDORFF_SPACE_TOPOLOGICAL_GROUP, topological_group, .. } := BPGA
  let { TOPOLOGICAL_GROUP_QUOTIENT_GROUP, .. } := BPGC
  let { ASM_MESON_TAC, MESON_TAC, SET_TAC, .. } := D.mt
  let { CLOSED_IN_QUOTIENT_TOPOLOGY, CONTINUOUS_MAP_COMPONENTWISE, CONTINUOUS_MAP_COMPOSE,
        CONTINUOUS_MAP_FST, CONTINUOUS_MAP_PAIRWISE, CONTINUOUS_MAP_PRODUCT_PROJECTION,
        CONTINUOUS_MAP_SND, OPEN_IN_QUOTIENT_TOPOLOGY, TOPSPACE_PROD_TOPOLOGY,
        TOPSPACE_PRODUCT_TOPOLOGY, .. } := D.qmetric
  let { FIRST_GROUP_ISOMORPHISM_THEOREM_GEN, group_div, GROUP_EPIMORPHISM_IMP_HOMOMORPHISM,
        GROUP_EPIMORPHISM_RIGHT_COSET, GROUP_ID, GROUP_INV, GROUP_MUL_ASSOC,
        GROUP_MUL_LINV, GROUP_MUL_RID, IN_SUBGROUP_ID, IN_SUBGROUP_MUL,
        ISOMORPHIC_GROUP_SYM, NORMAL_SUBGROUP_IMP_SUBGROUP,
        NORMAL_SUBGROUP_OF_HOMOMORPHIC_PREIMAGE, NORMAL_SUBGROUP_QUOTIENT_GROUP_IMAGE,
        PROD_GROUP, PRODUCT_GROUP, QUOTIENT_GROUP, RIGHT_COSET_EQ, RIGHT_COSET_EQ_SUBGROUP,
        RIGHT_COSET_ID, SUBGROUP_OF_IMP_SUBSET, THIRD_GROUP_ISOMORPHISM_THEOREM,
        .. } := D.qgrouptheory
  let { ETA_AX, EXTENSION, FORALL_IN_IMAGE, FUN_EQ_THM, .. } := D.mt.core1
  let { IMAGE_SUBSET, IN_ELIM_THM, IN_IMAGE, IN_SING, .. } := D.mt.core2
  let { cartesian_product, o_DEF, o_THM, RESTRICTION, RESTRICTION_IN_EXTENSIONAL,
        SING_SUBSET, SUBSET, .. } := D.mt.core4
  let { LAMBDA_PAIR, .. } := D.mt.core5
  -- @@SCOPE END

  let OPEN_NORMAL_SUBGROUP_QUOTIENT_IMAGE ← prove
   r"!G (top:A topology) N U.
        topological_group G top /\ N normal_subgroup_of G /\
        U normal_subgroup_of G /\ open_in top U /\ N SUBSET U
        ==> IMAGE (right_coset G N) U normal_subgroup_of quotient_group G N /\
            open_in (quotient_topology(top,right_coset G N))
                    (IMAGE (right_coset G N) U) /\
            quotient_group G U isomorphic_group
            quotient_group (quotient_group G N) (IMAGE (right_coset G N) U)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"(N:A->bool) subgroup_of G /\ (U:A->bool) subgroup_of G /\
      U SUBSET group_carrier G /\ topspace top = group_carrier G")
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC [NORMAL_SUBGROUP_IMP_SUBGROUP, SUBGROUP_OF_IMP_SUBSET] THEN
      ASM_MESON_TAC [topological_group],
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC NORMAL_SUBGROUP_QUOTIENT_GROUP_IMAGE THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [OPEN_IN_QUOTIENT_TOPOLOGY] THEN ASM_REWRITE_TAC [] THEN
      CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC [],
                      ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"{x | x IN group_carrier G /\
             right_coset G N x IN IMAGE (right_coset G N) U} = (U:A->bool)")
       (fun th => ASM_REWRITE_TAC [th]) THEN
      REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_IMAGE] THEN X_GEN_TAC (← q r"x:A") THEN
      EQ_TAC THENL
       [DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN (← q r"y:A") STRIP_ASSUME_TAC)) THEN
        SUBGOAL_THEN (← q r"(y:A) IN group_carrier G") ASSUME_TAC THENL
         [ASM SET_TAC [], ALL_TAC] THEN
        MP_TAC (← ISPECL [← q r"G:A group", ← q r"N:A->bool", ← q r"x:A", ← q r"y:A"]
               RIGHT_COSET_EQ) THEN
        ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
        SUBGOAL_THEN (← q r"x:A = group_mul G (group_div G x y) y") SUBST1_TAC THENL
         [ASM_SIMP_TAC [group_div, ← GSYM GROUP_MUL_ASSOC, GROUP_INV,
                        GROUP_MUL_LINV, GROUP_MUL_RID],
          ALL_TAC] THEN
        MATCH_MP_TAC IN_SUBGROUP_MUL THEN ASM SET_TAC [],
        DISCH_TAC THEN CONJ_TAC THENL
         [ASM SET_TAC [], EXISTS_TAC (← q r"x:A") THEN ASM_REWRITE_TAC []]],
      ONCE_REWRITE_TAC [ISOMORPHIC_GROUP_SYM] THEN
      MATCH_MP_TAC THIRD_GROUP_ISOMORPHISM_THEOREM THEN ASM_REWRITE_TAC []])

  let OPEN_NORMAL_SUBGROUP_QUOTIENT_PREIMAGE ← prove
   r"!G (top:A topology) N V.
        topological_group G top /\ N normal_subgroup_of G /\
        V normal_subgroup_of quotient_group G N /\
        open_in (quotient_topology(top,right_coset G N)) V
        ==> {x | x IN group_carrier G /\ right_coset G N x IN V}
            normal_subgroup_of G /\
            open_in top {x | x IN group_carrier G /\ right_coset G N x IN V} /\
            N SUBSET {x | x IN group_carrier G /\ right_coset G N x IN V} /\
            quotient_group G
              {x | x IN group_carrier G /\ right_coset G N x IN V}
            isomorphic_group quotient_group (quotient_group G N) V"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"(N:A->bool) subgroup_of G /\ N SUBSET group_carrier G /\
      topspace top = group_carrier G")
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC [NORMAL_SUBGROUP_IMP_SUBGROUP, SUBGROUP_OF_IMP_SUBSET] THEN
      ASM_MESON_TAC [topological_group],
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC NORMAL_SUBGROUP_OF_HOMOMORPHIC_PREIMAGE THEN
      EXISTS_TAC (← q r"quotient_group G (N:A->bool)") THEN REWRITE_TAC [ETA_AX] THEN
      ASM_SIMP_TAC [GROUP_EPIMORPHISM_RIGHT_COSET,
                    GROUP_EPIMORPHISM_IMP_HOMOMORPHISM],
      UNDISCH_TAC
       (← q r"open_in (quotient_topology(top,right_coset G N)) (V:(A->bool)->bool)") THEN
      ASM_REWRITE_TAC [OPEN_IN_QUOTIENT_TOPOLOGY] THEN SIMP_TAC [],
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"(x:A) IN group_carrier G") ASSUME_TAC THENL
       [ASM SET_TAC [], ASM_REWRITE_TAC []] THEN
      MP_TAC (← ISPECL [← q r"G:A group", ← q r"N:A->bool", ← q r"x:A"]
             RIGHT_COSET_EQ_SUBGROUP) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC (← ISPECL [← q r"quotient_group G (N:A->bool)", ← q r"V:(A->bool)->bool"]
        IN_SUBGROUP_ID) THEN
      ASM_SIMP_TAC [NORMAL_SUBGROUP_IMP_SUBGROUP, QUOTIENT_GROUP],
      MATCH_MP_TAC FIRST_GROUP_ISOMORPHISM_THEOREM_GEN THEN
      EXISTS_TAC (← q r"right_coset G (N:A->bool)") THEN
      ASM_SIMP_TAC [GROUP_EPIMORPHISM_RIGHT_COSET]])

  let HAUSDORFF_SPACE_QUOTIENT_GROUP ← prove
   r"!G (top:A topology) n.
        topological_group G top /\ n normal_subgroup_of G /\ closed_in top n
        ==> hausdorff_space (quotient_topology (top,right_coset G n))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"n:A->bool"]
      TOPOLOGICAL_GROUP_QUOTIENT_GROUP) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (REWRITE_TAC [← MATCH_MP HAUSDORFF_SPACE_TOPOLOGICAL_GROUP th])) THEN
    ASM_SIMP_TAC [QUOTIENT_GROUP, CLOSED_IN_QUOTIENT_TOPOLOGY] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
    SUBGOAL_THEN (← q r"topspace top = group_carrier(G:A group)") ASSUME_TAC THENL
     [ASM_MESON_TAC [topological_group], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [REWRITE_TAC [SING_SUBSET, IN_IMAGE] THEN EXISTS_TAC (← q r"group_id G:A") THEN
      ASM_SIMP_TAC [RIGHT_COSET_ID, GROUP_ID],
      SUBGOAL_THEN
       (← q r"{x | x IN group_carrier G /\ right_coset G n x IN {n}} = n:A->bool")
       (fun th => ASM_REWRITE_TAC [th]) THEN
      REWRITE_TAC [IN_SING] THEN
      GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN
      ASM_MESON_TAC [RIGHT_COSET_EQ_SUBGROUP, SUBSET]])

  let TOPOLOGICAL_GROUP_PRODUCT_GROUP ← prove
   r"!k (G:K->A group) (top:K->A topology).
        (!i. i IN k ==> topological_group (G i) (top i))
        ==> topological_group (product_group k G) (product_topology k top)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"!i. i IN k ==> topspace((top:K->A topology) i) = group_carrier(G i)")
    ASSUME_TAC THENL [ASM_MESON_TAC [topological_group], ALL_TAC] THEN
    REWRITE_TAC [topological_group, TOPSPACE_PRODUCT_TOPOLOGY, PRODUCT_GROUP] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [cartesian_product, o_THM] THEN ASM_SIMP_TAC [],
      REWRITE_TAC [CONTINUOUS_MAP_COMPONENTWISE] THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, RESTRICTION_IN_EXTENSIONAL] THEN
      X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN ASM_REWRITE_TAC [RESTRICTION] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_GROUP_MUL THEN ASM_SIMP_TAC [] THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN (← q r"(\x:(K->A)#(K->A). FST x i) = (\y. y i) o FST")
        SUBST1_TAC THENL [REWRITE_TAC [FUN_EQ_THM, o_THM], ALL_TAC],
        SUBGOAL_THEN (← q r"(\x:(K->A)#(K->A). SND x i) = (\y. y i) o SND")
        SUBST1_TAC THENL [REWRITE_TAC [FUN_EQ_THM, o_THM], ALL_TAC]] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC (← q r"product_topology k (top:K->A topology)") THEN
      ASM_SIMP_TAC [CONTINUOUS_MAP_FST, CONTINUOUS_MAP_SND,
                    CONTINUOUS_MAP_PRODUCT_PROJECTION],
      REWRITE_TAC [CONTINUOUS_MAP_COMPONENTWISE] THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, RESTRICTION_IN_EXTENSIONAL] THEN
      X_GEN_TAC (← q r"i:K") THEN DISCH_TAC THEN ASM_REWRITE_TAC [RESTRICTION] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_GROUP_INV THEN
      ASM_SIMP_TAC [CONTINUOUS_MAP_PRODUCT_PROJECTION]])

  let TOPOLOGICAL_GROUP_PROD_GROUP ← prove
   r"!(G:A group) (H:B group) top top'.
        topological_group G top /\ topological_group H top'
        ==> topological_group (prod_group G H) (prod_topology top top')"
   (REPEAT GEN_TAC THEN REWRITE_TAC [topological_group] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [TOPSPACE_PROD_TOPOLOGY, PROD_GROUP] THEN
    REWRITE_TAC [LAMBDA_PAIR] THEN
    REWRITE_TAC [CONTINUOUS_MAP_PAIRWISE, o_DEF] THEN
    REPEAT CONJ_TAC THEN
    (MATCH_MP_TAC CONTINUOUS_MAP_GROUP_MUL ORELSE
     MATCH_MP_TAC CONTINUOUS_MAP_GROUP_INV) THEN
    ASM_REWRITE_TAC [topological_group] THEN
    REWRITE_TAC [CONTINUOUS_MAP_FST, CONTINUOUS_MAP_SND] THEN
    REPEAT CONJ_TAC THEN
    REWRITE_TAC [← GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    MESON_TAC [CONTINUOUS_MAP_FST, CONTINUOUS_MAP_SND])

  pure { OPEN_NORMAL_SUBGROUP_QUOTIENT_IMAGE, OPEN_NORMAL_SUBGROUP_QUOTIENT_PREIMAGE,
         HAUSDORFF_SPACE_QUOTIENT_GROUP, TOPOLOGICAL_GROUP_PRODUCT_GROUP,
         TOPOLOGICAL_GROUP_PROD_GROUP }

/- ------------------------------------------------------------------------- -/
/- Profinite groups: the definition, coset neighbourhoods, finite discrete   -/
/- groups, and finite index of open subgroups of compact groups.             -/
/- (profinite_groups.ml 892-1006)                                            -/
/- ------------------------------------------------------------------------- -/

structure PGE where
  profinite_group : thm
  PROFINITE_GROUP_NEIGHBOURHOOD_BASE : thm
  PROFINITE_GROUP_COSET_NEIGHBOURHOOD : thm
  PROFINITE_GROUP_FINITE_DISCRETE : thm
  COMPACT_TOPOLOGICAL_GROUP_FINITE_INDEX : thm
  OPEN_IN_COMPACT_TOPOLOGICAL_GROUP_SUBGROUP : thm
  PROFINITE_GROUP_FINITE_QUOTIENT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPGE [HolBase] (D : ProfiniteGroupsDeps) (BPGA : PGA) : ExceptT String IO PGE := do
  -- @@SCOPE BEGIN
  let { CLOSED_IN_OPEN_SUBGROUP, OPEN_IN_CLOSED_SUBGROUP_FINITE_INDEX,
        OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES, topological_group,
        TOPOLOGICAL_GROUP_DISCRETE_TOPOLOGY, .. } := BPGA
  let { ASM_MESON_TAC, MESON_TAC, new_definition, .. } := D.mt
  let { compact_in, compact_space, COMPACT_SPACE_DISCRETE_TOPOLOGY,
        HAUSDORFF_SPACE_DISCRETE_TOPOLOGY, neighbourhood_base_at,
        OPEN_IN_DISCRETE_TOPOLOGY, OPEN_IN_SUBSET, .. } := D.qmetric
  let { group_cosets, GROUP_ID, GROUP_INV, GROUP_MUL_ASSOC, GROUP_MUL_LID, GROUP_MUL_LINV,
        GROUP_MUL_RINV, IN_RIGHT_COSET_SELF, LEFT_COSET_AS_IMAGE,
        NORMAL_SUBGROUP_IMP_SUBGROUP, normal_subgroup_of, QUOTIENT_GROUP_CARRIER,
        RIGHT_COSETS_EQ, subgroup_of, SUBGROUP_OF_IMP_SUBSET, TRIVIAL_NORMAL_SUBGROUP_OF,
        UNIONS_RIGHT_COSETS, .. } := D.qgrouptheory
  let { DISJOINT, FINITE_SUBSET, FORALL_IN_GSPEC, FORALL_IN_IMAGE, .. } := D.mt.core1
  let { IN_ELIM_THM, IN_IMAGE, IN_INTER, IN_UNIONS, MEMBER_NOT_EMPTY, MONO_EXISTS,
        .. } := D.mt.core2
  let { SING_SUBSET, SUBSET, SUBSET_REFL, .. } := D.mt.core4
  -- @@SCOPE END

  let profinite_group ← new_definition
   r"profinite_group (G:A group) (top:A topology) <=>
        topological_group G top /\ compact_space top /\ hausdorff_space top /\
        !w. open_in top w /\ group_id G IN w
            ==> ?u. u normal_subgroup_of G /\ open_in top u /\ u SUBSET w"

  let PROFINITE_GROUP_NEIGHBOURHOOD_BASE ← prove
   r"!G (top:A topology).
        profinite_group G top
        ==> neighbourhood_base_at (group_id G)
             (\u. u normal_subgroup_of G /\ open_in top u) top"
   (REWRITE_TAC [profinite_group, neighbourhood_base_at] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"w:A->bool")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:A->bool") STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [← q r"u:A->bool", ← q r"u:A->bool"] THEN
    ASM_REWRITE_TAC [SUBSET_REFL] THEN
    ASM_MESON_TAC [normal_subgroup_of, subgroup_of])

  let PROFINITE_GROUP_COSET_NEIGHBOURHOOD ← prove
   r"!G (top:A topology) w x.
        profinite_group G top /\ open_in top w /\ x IN w
        ==> ?u. u normal_subgroup_of G /\ open_in top u /\
                right_coset G u x SUBSET w"
   (REWRITE_TAC [profinite_group] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
    THEN SUBGOAL_THEN (← q r"(x:A) IN group_carrier G") ASSUME_TAC THENL
     [ASM_MESON_TAC [OPEN_IN_SUBSET, SUBSET], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"left_coset G (group_inv G x) (w:A->bool)")) THEN
    MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"group_inv G x:A",
                      ← q r"w:A->bool"] OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES) THEN
    ASM_SIMP_TAC [GROUP_INV] THEN DISCH_THEN (K ALL_TAC : thm → tactic) THEN ANTS_TAC THENL
     [REWRITE_TAC [LEFT_COSET_AS_IMAGE, IN_IMAGE] THEN EXISTS_TAC (← q r"x:A") THEN
      ASM_SIMP_TAC [GROUP_MUL_LINV],
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"u:A->bool") THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"x:A") o CONJUNCT2 o
      GEN_REWRITE_RULE I [normal_subgroup_of]) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    UNDISCH_TAC (← q r"u SUBSET left_coset G (group_inv G x) (w:A->bool)") THEN
    REWRITE_TAC [LEFT_COSET_AS_IMAGE, SUBSET, FORALL_IN_IMAGE] THEN
    DISCH_TAC THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"y:A")) THEN ASM_REWRITE_TAC [IN_IMAGE] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"z:A") STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"(z:A) IN group_carrier G") ASSUME_TAC THENL
     [ASM_MESON_TAC [OPEN_IN_SUBSET, SUBSET], ALL_TAC] THEN
    ASM_SIMP_TAC [GROUP_MUL_ASSOC, GROUP_MUL_RINV, GROUP_MUL_LID, GROUP_INV])

  let PROFINITE_GROUP_FINITE_DISCRETE ← prove
   r"!G:A group.
        FINITE(group_carrier G)
        ==> profinite_group G (discrete_topology(group_carrier G))"
   (REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [profinite_group, TOPOLOGICAL_GROUP_DISCRETE_TOPOLOGY,
                     COMPACT_SPACE_DISCRETE_TOPOLOGY,
                     HAUSDORFF_SPACE_DISCRETE_TOPOLOGY] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"{group_id G:A}") THEN
    ASM_REWRITE_TAC [TRIVIAL_NORMAL_SUBGROUP_OF, OPEN_IN_DISCRETE_TOPOLOGY,
                     SING_SUBSET, GROUP_ID])

  let COMPACT_TOPOLOGICAL_GROUP_FINITE_INDEX ← prove
   r"!G (top:A topology) h.
        topological_group G top /\ compact_space top /\
        h subgroup_of G /\ open_in top h
        ==> FINITE(group_cosets G h)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
    THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"group_cosets G (h:A->bool)") o CONJUNCT2 o
      GEN_REWRITE_RULE I [compact_in] o GEN_REWRITE_RULE I [compact_space]) THEN
    ASM_SIMP_TAC [group_cosets, FORALL_IN_GSPEC, UNIONS_RIGHT_COSETS,
                  SUBSET_REFL] THEN
    ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"x:A", ← q r"h:A->bool"]
                       OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES) THEN
      ASM_SIMP_TAC [],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"v:(A->bool)->bool") STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"v:(A->bool)->bool") THEN
    ASM_REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN
    X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN
    UNDISCH_TAC (← q r"group_carrier G SUBSET UNIONS (v:(A->bool)->bool)") THEN
    REWRITE_TAC [SUBSET, IN_UNIONS] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"x:A")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"c:A->bool") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"?y:A. y IN group_carrier G /\ c = right_coset G h y")
    (X_CHOOSE_THEN (← q r"y:A") (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THENL
     [UNDISCH_TAC (← q r"(v:(A->bool)->bool) SUBSET
                   {right_coset G h x | x | (x:A) IN group_carrier G}") THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"right_coset G h (x:A) = right_coset G h y")
     (fun th => ASM_REWRITE_TAC [th]) THEN
    MP_TAC (← ISPECL [← q r"G:A group", ← q r"h:A->bool", ← q r"x:A", ← q r"y:A"] RIGHT_COSETS_EQ) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [DISJOINT, ← GSYM MEMBER_NOT_EMPTY, IN_INTER] THEN
    EXISTS_TAC (← q r"x:A") THEN ASM_SIMP_TAC [IN_RIGHT_COSET_SELF])

  let OPEN_IN_COMPACT_TOPOLOGICAL_GROUP_SUBGROUP ← prove
   r"!G (top:A topology) h.
        topological_group G top /\ compact_space top /\ h subgroup_of G
        ==> (open_in top h <=> closed_in top h /\ FINITE(group_cosets G h))"
   (MESON_TAC [CLOSED_IN_OPEN_SUBGROUP, COMPACT_TOPOLOGICAL_GROUP_FINITE_INDEX,
               OPEN_IN_CLOSED_SUBGROUP_FINITE_INDEX])

  let PROFINITE_GROUP_FINITE_QUOTIENT ← prove
   r"!G (top:A topology) u.
        profinite_group G top /\ u normal_subgroup_of G /\ open_in top u
        ==> FINITE(group_carrier(quotient_group G u))"
   (SIMP_TAC [QUOTIENT_GROUP_CARRIER, profinite_group] THEN
    MESON_TAC [COMPACT_TOPOLOGICAL_GROUP_FINITE_INDEX,
               NORMAL_SUBGROUP_IMP_SUBGROUP])

  pure { profinite_group, PROFINITE_GROUP_NEIGHBOURHOOD_BASE,
         PROFINITE_GROUP_COSET_NEIGHBOURHOOD, PROFINITE_GROUP_FINITE_DISCRETE,
         COMPACT_TOPOLOGICAL_GROUP_FINITE_INDEX, OPEN_IN_COMPACT_TOPOLOGICAL_GROUP_SUBGROUP,
         PROFINITE_GROUP_FINITE_QUOTIENT }

/- ------------------------------------------------------------------------- -/
/- Intersections of open normal subgroups; closed, open and quotient         -/
/- subgroups of profinite groups.  (profinite_groups.ml 1008-1162)           -/
/- ------------------------------------------------------------------------- -/

structure PGF where
  OPEN_NORMAL_SUBGROUP_INTERS : thm
  PROFINITE_GROUP_HOMEOMORPHIC_ISOMORPHISM : thm
  PROFINITE_GROUP_CLOSED_SUBGROUP : thm
  PROFINITE_GROUP_OPEN_SUBGROUP : thm
  PROFINITE_GROUP_QUOTIENT_GROUP : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPGF [HolBase] (D : ProfiniteGroupsDeps) (BPGA : PGA) (BPGC : PGC) (BPGD : PGD) (BPGE : PGE) : ExceptT String IO PGF := do
  -- @@SCOPE BEGIN
  let { CLOSED_IN_OPEN_SUBGROUP, topological_group,
        TOPOLOGICAL_GROUP_HOMEOMORPHIC_ISOMORPHISM, .. } := BPGA
  let { OPEN_MAP_RIGHT_COSET, TOPOLOGICAL_GROUP_QUOTIENT_GROUP, TOPOLOGICAL_GROUP_SUBGROUP,
        .. } := BPGC
  let { HAUSDORFF_SPACE_QUOTIENT_GROUP, .. } := BPGD
  let { profinite_group, .. } := BPGE
  let { ASM_MESON_TAC, SET_TAC, .. } := D.mt
  let { CLOSED_IN_COMPACT_SPACE, COMPACT_SPACE_QUOTIENT_MAP_IMAGE,
        COMPACT_SPACE_SUBTOPOLOGY, HAUSDORFF_SPACE_SUBTOPOLOGY, HOMEOMORPHIC_COMPACT_SPACE,
        HOMEOMORPHIC_HAUSDORFF_SPACE, HOMEOMORPHIC_IMP_CONTINUOUS_MAP,
        HOMEOMORPHIC_MAP_IMP_HOMEOMORPHIC_SPACE, HOMEOMORPHIC_MAP_OPENNESS,
        OPEN_IN_CONTINUOUS_MAP_PREIMAGE, OPEN_IN_INTERS, OPEN_IN_QUOTIENT_TOPOLOGY,
        OPEN_IN_SUBSET, OPEN_IN_SUBTOPOLOGY, OPEN_IN_TOPSPACE, open_map,
        QUOTIENT_MAP_QUOTIENT_TOPOLOGY, .. } := D.qmetric
  let { CARRIER_NORMAL_SUBGROUP_OF, GROUP_EPIMORPHISM_RIGHT_COSET, group_homomorphism,
        GROUP_ID, GROUP_ISOMORPHISM, NORMAL_SUBGROUP_IMP_SUBGROUP,
        NORMAL_SUBGROUP_INTER_SUBGROUP_GENERATED, NORMAL_SUBGROUP_OF_EPIMORPHIC_IMAGE,
        NORMAL_SUBGROUP_OF_HOMOMORPHIC_PREIMAGE, NORMAL_SUBGROUP_OF_INTERS,
        QUOTIENT_GROUP_ID, RIGHT_COSET_ID, SUBGROUP_GENERATED, SUBGROUP_OF_IMP_SUBSET,
        .. } := D.qgrouptheory
  let { FINITE_INSERT, FORALL_IN_INSERT, FUN_IN_IMAGE, .. } := D.mt.core1
  let { IN_ELIM_THM, IN_IMAGE, INTERS_INSERT, NOT_INSERT_EMPTY, .. } := D.mt.core2
  let { SUBSET, .. } := D.mt.core4
  -- @@SCOPE END

  let OPEN_NORMAL_SUBGROUP_INTERS ← prove
   r"!G (top:A topology) f.
        topological_group G top /\ FINITE f /\
        (!u. u IN f ==> u normal_subgroup_of G /\ open_in top u)
        ==> (group_carrier G INTER INTERS f) normal_subgroup_of G /\
            open_in top (group_carrier G INTER INTERS f)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
    THEN REWRITE_TAC [← GSYM INTERS_INSERT] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NORMAL_SUBGROUP_OF_INTERS,
      MATCH_MP_TAC OPEN_IN_INTERS] THEN
    ASM_REWRITE_TAC [FINITE_INSERT, NOT_INSERT_EMPTY, FORALL_IN_INSERT] THEN
    ASM_MESON_TAC [CARRIER_NORMAL_SUBGROUP_OF, OPEN_IN_TOPSPACE])

  let PROFINITE_GROUP_HOMEOMORPHIC_ISOMORPHISM ← prove
   r"!G H (top:A topology) (top':B topology) f.
        profinite_group H top' /\ topspace top = group_carrier G /\
        group_isomorphism (G,H) f /\ homeomorphic_map (top,top') f
        ==> profinite_group G top"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [profinite_group]) THEN
    SUBGOAL_THEN (← q r"topological_group G (top:A topology)") ASSUME_TAC THENL
     [MATCH_MP_TAC TOPOLOGICAL_GROUP_HOMEOMORPHIC_ISOMORPHISM THEN
      MAP_EVERY EXISTS_TAC [← q r"H:B group", ← q r"top':B topology", ← q r"f:A->B"] THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [GROUP_ISOMORPHISM]) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [group_homomorphism]) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
    REWRITE_TAC [profinite_group] THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (ASSUME_TAC o
      MATCH_MP HOMEOMORPHIC_MAP_IMP_HOMEOMORPHIC_SPACE) THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (REWRITE_TAC [← MATCH_MP HOMEOMORPHIC_COMPACT_SPACE th,
                         ← MATCH_MP HOMEOMORPHIC_HAUSDORFF_SPACE th])) THEN
    ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"w:A->bool") THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"IMAGE (f:A->B) w")) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC [HOMEOMORPHIC_MAP_OPENNESS, OPEN_IN_SUBSET],
        SUBGOAL_THEN (← q r"group_id H = (f:A->B)(group_id G)") SUBST1_TAC THENL
         [ASM_REWRITE_TAC [],
          MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC []]],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:B->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"{x | x IN group_carrier G /\ (f:A->B) x IN u}") THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC NORMAL_SUBGROUP_OF_HOMOMORPHIC_PREIMAGE THEN
      EXISTS_TAC (← q r"H:B group") THEN ASM_REWRITE_TAC [],
      MP_TAC (← ISPECL [← q r"f:A->B", ← q r"top:A topology", ← q r"top':B topology",
                        ← q r"u:B->bool"] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"(f:A->B) x IN IMAGE f w") MP_TAC THENL
       [ASM SET_TAC [], ALL_TAC] THEN
      REWRITE_TAC [IN_IMAGE] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"y:A") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"(x:A) = y") (fun th => ASM_REWRITE_TAC [th]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [OPEN_IN_SUBSET, SUBSET]])

  let PROFINITE_GROUP_CLOSED_SUBGROUP ← prove
   r"!G (top:A topology) h.
        profinite_group G top /\ h subgroup_of G /\ closed_in top h
        ==> profinite_group (subgroup_generated G h) (subtopology top h)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [profinite_group] THEN STRIP_TAC THEN
    ASM_SIMP_TAC [TOPOLOGICAL_GROUP_SUBGROUP, HAUSDORFF_SPACE_SUBTOPOLOGY] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
      MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    X_GEN_TAC (← q r"w:A->bool") THEN
    REWRITE_TAC [OPEN_IN_SUBTOPOLOGY, ← CONJUNCT2 SUBGROUP_GENERATED] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:A->bool")
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"t:A->bool")) THEN
    ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:A->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"(h:A->bool) INTER u") THEN
    ASM_SIMP_TAC [NORMAL_SUBGROUP_INTER_SUBGROUP_GENERATED] THEN
    CONJ_TAC THENL
     [EXISTS_TAC (← q r"u:A->bool") THEN ASM_REWRITE_TAC [] THEN SET_TAC [],
      ASM SET_TAC []])

  let PROFINITE_GROUP_OPEN_SUBGROUP ← prove
   r"!G (top:A topology) h.
        profinite_group G top /\ h subgroup_of G /\ open_in top h
        ==> profinite_group (subgroup_generated G h) (subtopology top h)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC PROFINITE_GROUP_CLOSED_SUBGROUP THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC CLOSED_IN_OPEN_SUBGROUP THEN
    EXISTS_TAC (← q r"G:A group") THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [profinite_group]))

  let PROFINITE_GROUP_QUOTIENT_GROUP ← prove
   r"!G (top:A topology) n.
        profinite_group G top /\ n normal_subgroup_of G /\ closed_in top n
        ==> profinite_group (quotient_group G n)
                            (quotient_topology (top,right_coset G n))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [profinite_group] THEN STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
    THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
    ASM_SIMP_TAC [TOPOLOGICAL_GROUP_QUOTIENT_GROUP,
                  HAUSDORFF_SPACE_QUOTIENT_GROUP] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC (← ISPEC (← q r"top:A topology") COMPACT_SPACE_QUOTIENT_MAP_IMAGE) THEN
      EXISTS_TAC (← q r"right_coset G (n:A->bool)") THEN
      ASM_REWRITE_TAC [QUOTIENT_MAP_QUOTIENT_TOPOLOGY],
      ALL_TAC] THEN
    X_GEN_TAC (← q r"w:(A->bool)->bool") THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (REWRITE_TAC [← MATCH_MP QUOTIENT_GROUP_ID th])) THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [OPEN_IN_QUOTIENT_TOPOLOGY] THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC
     (← q r"{x | x IN group_carrier G /\ right_coset G n (x:A) IN w}")) THEN
    ASM_REWRITE_TAC [IN_ELIM_THM] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC [GROUP_ID, RIGHT_COSET_ID], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:A->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"IMAGE (right_coset G n) (u:A->bool)") THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC NORMAL_SUBGROUP_OF_EPIMORPHIC_IMAGE THEN
      EXISTS_TAC (← q r"G:A group") THEN ASM_SIMP_TAC [GROUP_EPIMORPHISM_RIGHT_COSET],
      MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"n:A->bool"]
                       OPEN_MAP_RIGHT_COSET) THEN
      ASM_REWRITE_TAC [open_map] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [],
      ASM SET_TAC []])

  pure { OPEN_NORMAL_SUBGROUP_INTERS, PROFINITE_GROUP_HOMEOMORPHIC_ISOMORPHISM,
         PROFINITE_GROUP_CLOSED_SUBGROUP, PROFINITE_GROUP_OPEN_SUBGROUP,
         PROFINITE_GROUP_QUOTIENT_GROUP }

/- ------------------------------------------------------------------------- -/
/- Continuous epimorphisms of profinite groups, and open subgroups inside    -/
/- closed and open neighbourhoods of 1.  (profinite_groups.ml 1164-1359)     -/
/- ------------------------------------------------------------------------- -/

structure PGG where
  PROFINITE_GROUP_CONTINUOUS_EPIMORPHISM : thm
  COMPACT_TOPOLOGICAL_GROUP_CLOPEN_SUBGROUP : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPGG [HolBase] (D : ProfiniteGroupsDeps) (BPGA : PGA) (BPGB : PGB) (BPGE : PGE) : ExceptT String IO PGG := do
  -- @@SCOPE BEGIN
  let { OPEN_IN_SUBGROUP_NEIGHBOURHOOD, OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES,
        topological_group, .. } := BPGA
  let { TOPOLOGICAL_GROUP_OPEN_EPIMORPHIC_IMAGE, .. } := BPGB
  let { profinite_group, .. } := BPGE
  let { ASM_MESON_TAC, MESON_TAC, SET_TAC, .. } := D.mt
  let { CLOSED_IN_COMPACT_SPACE, compact_in, COMPACT_SPACE_QUOTIENT_MAP_IMAGE,
        CONTINUOUS_CLOSED_IMP_QUOTIENT_MAP, CONTINUOUS_IMP_CLOSED_MAP,
        OPEN_IN_CONTINUOUS_MAP_PREIMAGE, OPEN_IN_INTER, OPEN_IN_INTERS,
        OPEN_IN_PROD_TOPOLOGY_ALT, OPEN_IN_SUBSET, OPEN_IN_TOPSPACE, OPEN_IN_UNIONS,
        open_map, quotient_map, TOPSPACE_PROD_TOPOLOGY, .. } := D.qmetric
  let { group_epimorphism, group_homomorphism, GROUP_ID, GROUP_INV, GROUP_INV_ID,
        GROUP_INV_INV, GROUP_INV_MUL, group_kernel, GROUP_MUL, GROUP_MUL_ASSOC,
        GROUP_MUL_LID, GROUP_MUL_LINV, GROUP_MUL_RID, GROUP_MUL_RINV,
        NORMAL_SUBGROUP_OF_EPIMORPHIC_IMAGE, RIGHT_COSET_AS_IMAGE, subgroup_of,
        .. } := D.qgrouptheory
  let { EXISTS_IN_IMAGE, EXTENSION, FINITE_IMAGE, FINITE_INSERT, FINITE_SUBSET_IMAGE,
        FORALL_IN_IMAGE, FORALL_IN_INSERT, .. } := D.mt.core1
  let { IN_CROSS, IN_ELIM_THM, IN_IMAGE, IN_INTER, IN_UNIONS, INTERS_IMAGE, INTERS_INSERT,
        LEFT_IMP_EXISTS_THM, MONO_EXISTS, NOT_INSERT_EMPTY, .. } := D.mt.core2
  let { SKOLEM_THM, SUBSET, .. } := D.mt.core4
  let { FORALL_PAIR_THM, .. } := D.mt.core5
  -- @@SCOPE END
  let lastc : thm → ExceptT String IO thm := fun th =>
    liftExcept (HolCore.Lib.last (CONJUNCTS th))

  let PROFINITE_GROUP_CONTINUOUS_EPIMORPHISM ← prove
   r"!G H (top:A topology) (top':B topology) f.
        profinite_group G top /\ hausdorff_space top' /\
        topspace top' = group_carrier H /\
        group_epimorphism(G,H) f /\ continuous_map (top,top') f
        ==> open_map (top,top') f /\ quotient_map (top,top') f /\
            profinite_group H top'"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [profinite_group]) THEN
    FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
    THEN FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [group_epimorphism])
    THEN FIRST_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [SUBSET, FORALL_IN_IMAGE] o
      GEN_REWRITE_RULE I [group_homomorphism])
    THEN SUBGOAL_THEN (← q r"quotient_map (top,top') (f:A->B)") ASSUME_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_CLOSED_IMP_QUOTIENT_MAP THEN
      ASM_SIMP_TAC [CONTINUOUS_IMP_CLOSED_MAP],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"open_map (top,top') (f:A->B)") ASSUME_TAC THENL
     [REWRITE_TAC [open_map] THEN X_GEN_TAC (← q r"u:A->bool") THEN DISCH_TAC THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
      FIRST_ASSUM (MP_TAC o SPEC (← q r"IMAGE (f:A->B) u") o CONJUNCT2 o
        GEN_REWRITE_RULE I [quotient_map]) THEN
      ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN
      SUBGOAL_THEN
       (← q r"{x | x IN topspace top /\ (f:A->B) x IN IMAGE f u} =
        UNIONS (IMAGE (right_coset G u) (group_kernel (G,H) f))")
      SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_UNIONS, EXISTS_IN_IMAGE,
                     RIGHT_COSET_AS_IMAGE, IN_IMAGE, group_kernel] THEN
        X_GEN_TAC (← q r"x:A") THEN ASM_REWRITE_TAC [] THEN EQ_TAC THENL
         [DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
            (X_CHOOSE_THEN (← q r"y:A") STRIP_ASSUME_TAC)) THEN
          SUBGOAL_THEN (← q r"(y:A) IN group_carrier G") ASSUME_TAC THENL
           [ASM SET_TAC [], ALL_TAC] THEN
          EXISTS_TAC (← q r"group_mul G (group_inv G y) x:A") THEN
          REPEAT CONJ_TAC THENL
           [ASM_SIMP_TAC [GROUP_MUL, GROUP_INV],
            ASM_SIMP_TAC [GROUP_MUL, GROUP_INV, GROUP_MUL_LINV],
            EXISTS_TAC (← q r"y:A") THEN
            ASM_SIMP_TAC [GROUP_MUL_ASSOC, GROUP_INV, GROUP_MUL_RINV,
                          GROUP_MUL_LID]],
          DISCH_THEN (X_CHOOSE_THEN (← q r"k:A") (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
            (X_CHOOSE_THEN (← q r"y:A") STRIP_ASSUME_TAC))) THEN
          SUBGOAL_THEN (← q r"(y:A) IN group_carrier G") ASSUME_TAC THENL
           [ASM SET_TAC [], ALL_TAC] THEN
          CONJ_TAC THENL
           [ASM_SIMP_TAC [GROUP_MUL],
            EXISTS_TAC (← q r"y:A") THEN ASM_SIMP_TAC [GROUP_MUL_RID]]],
        MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN
        REWRITE_TAC [group_kernel, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC [OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES]],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [profinite_group] THEN
    SUBGOAL_THEN (← q r"topological_group H (top':B topology)") ASSUME_TAC THENL
     [MATCH_MP_TAC TOPOLOGICAL_GROUP_OPEN_EPIMORPHIC_IMAGE THEN
      MAP_EVERY EXISTS_TAC [← q r"G:A group", ← q r"top:A topology", ← q r"f:A->B"] THEN
      ASM_REWRITE_TAC [],
      ASM_REWRITE_TAC []] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC (← ISPEC (← q r"top:A topology") COMPACT_SPACE_QUOTIENT_MAP_IMAGE) THEN
      EXISTS_TAC (← q r"f:A->B") THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    X_GEN_TAC (← q r"w:B->bool") THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC
     (← q r"{x | x IN topspace top /\ (f:A->B) x IN w}")) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
        EXISTS_TAC (← q r"top':B topology") THEN ASM_REWRITE_TAC [],
        ASM_REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [GROUP_ID]],
      DISCH_THEN (X_CHOOSE_THEN (← q r"n:A->bool") STRIP_ASSUME_TAC)] THEN
    EXISTS_TAC (← q r"IMAGE (f:A->B) n") THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC NORMAL_SUBGROUP_OF_EPIMORPHIC_IMAGE THEN
      EXISTS_TAC (← q r"G:A group") THEN ASM_REWRITE_TAC [],
      UNDISCH_TAC (← q r"open_map (top,top') (f:A->B)") THEN
      REWRITE_TAC [open_map] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [],
      ASM SET_TAC []])

  let COMPACT_TOPOLOGICAL_GROUP_CLOPEN_SUBGROUP ← prove
   r"!G (top:A topology) k.
        topological_group G top /\ compact_space top /\
        open_in top k /\ closed_in top k /\ group_id G IN k
        ==> ?h. h subgroup_of G /\ open_in top h /\ h SUBSET k"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [topological_group]) THEN
    FIRST_ASSUM (fun th => tactic_of do
      let t ← q r"open_in top (k:A->bool)"
      pure (ASSUME_TAC (← MATCH_MP OPEN_IN_SUBSET
        (← liftExcept (check (fun th => concl th == t) th))))) THEN
    SUBGOAL_THEN
     (← q r"!x. ?a b. x IN k
                ==> open_in top a /\ open_in top b /\ x IN a /\
                    group_id G IN b /\
                    !y z:A. y IN a /\ z IN b ==> group_mul G y z IN k")
    MP_TAC THENL
     [X_GEN_TAC (← q r"x:A") THEN ASM_CASES_TAC (← q r"(x:A) IN k") THEN ASM_REWRITE_TAC [] THEN
      MP_TAC (← ISPECL [← q r"\z. group_mul G (FST z) (SND z):A",
                        ← q r"prod_topology (top:A topology) top", ← q r"top:A topology",
                        ← q r"k:A->bool"] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
      ASM_REWRITE_TAC [OPEN_IN_PROD_TOPOLOGY_ALT] THEN
      DISCH_THEN (MP_TAC o SPECL [← q r"x:A", ← q r"group_id G:A"]) THEN
      ASM_REWRITE_TAC [IN_ELIM_THM, TOPSPACE_PROD_TOPOLOGY, IN_CROSS] THEN
      SUBGOAL_THEN (← q r"(x:A) IN group_carrier G") ASSUME_TAC THENL
       [ASM SET_TAC [], ALL_TAC] THEN
      ASM_SIMP_TAC [GROUP_ID, GROUP_MUL_RID] THEN
      REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
      REWRITE_TAC [SUBSET, FORALL_PAIR_THM, IN_CROSS, IN_ELIM_THM] THEN
      MESON_TAC [],
      REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:A->A->bool", ← q r"b:A->A->bool"] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"compact_in top (k:A->bool)") MP_TAC THENL
     [ASM_SIMP_TAC [CLOSED_IN_COMPACT_SPACE], ALL_TAC] THEN
    REWRITE_TAC [compact_in] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"IMAGE (a:A->A->bool) k") o CONJUNCT2) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [FORALL_IN_IMAGE, SUBSET, IN_UNIONS, EXISTS_IN_IMAGE] THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"v:(A->bool)->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"a:A->A->bool", ← q r"k:A->bool", ← q r"v:(A->bool)->bool"]
                     FINITE_SUBSET_IMAGE) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"f:A->bool") STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC (← q r"k SUBSET UNIONS (v:(A->bool)->bool)") THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    ABBREV_TAC
     (← q r"w = INTERS (topspace (top:A topology) INSERT IMAGE (b:A->A->bool) f)") THEN
    SUBGOAL_THEN
     (← q r"open_in top (w:A->bool) /\ group_id G IN w /\
      !y z. y IN k /\ z IN w ==> group_mul G y z IN k")
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_INTERS THEN
        ASM_SIMP_TAC [FINITE_INSERT, FINITE_IMAGE, NOT_INSERT_EMPTY] THEN
        REWRITE_TAC [FORALL_IN_INSERT, FORALL_IN_IMAGE, OPEN_IN_TOPSPACE] THEN
        CONJ_TAC THENL [ASM_MESON_TAC [OPEN_IN_TOPSPACE], ALL_TAC] THEN
        ASM_MESON_TAC [SUBSET],
        REWRITE_TAC [INTERS_INSERT, IN_INTER, INTERS_IMAGE, IN_ELIM_THM] THEN
        ASM_SIMP_TAC [GROUP_ID] THEN ASM_MESON_TAC [SUBSET],
        MAP_EVERY X_GEN_TAC [← q r"y:A", ← q r"z:A"] THEN
        REWRITE_TAC [INTERS_INSERT, IN_INTER, INTERS_IMAGE, IN_ELIM_THM] THEN
        STRIP_TAC THEN
        UNDISCH_TAC (← q r"k SUBSET UNIONS (IMAGE (a:A->A->bool) f)") THEN
        REWRITE_TAC [SUBSET, IN_UNIONS, EXISTS_IN_IMAGE] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"y:A")) THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"x:A") STRIP_ASSUME_TAC) THEN
        -- `check (fun th -> is_forall(concl th) && can (find_term ((=)
        -- `a:A->A->bool`)) (concl th))`: the quotation is parsed only when
        -- `is_forall` holds, as `&&`.
        FIRST_X_ASSUM (fun th => tactic_of do
          let ok ← if HolCore.Basics.is_forall (concl th) then do
              let a ← q r"a:A->A->bool"
              pure (HolCore.Lib.can (HolCore.Basics.find_term (fun t => t == a)) (concl th))
            else pure false
          pure (MP_TAC (← SPEC (← q r"x:A") (← liftExcept (check (fun _ => ok) th))))) THEN
        ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
        DISCH_THEN (MATCH_MP_TAC o lastc) THEN
        ASM_SIMP_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!y:A. y IN k ==> y IN group_carrier G") ASSUME_TAC THENL
     [ASM SET_TAC [], ALL_TAC] THEN
    ABBREV_TAC
     (← q r"h = {g:A | g IN group_carrier G /\
                 !y. y IN k ==> group_mul G y g IN k /\
                                group_mul G y (group_inv G g) IN k}") THEN
    SUBGOAL_THEN (← q r"(h:A->bool) subgroup_of G") ASSUME_TAC THENL
     [EXPAND_TAC "h" THEN
      REWRITE_TAC [subgroup_of, SUBSET, IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
       [SIMP_TAC [],
        REWRITE_TAC [GROUP_ID],
        ASM_SIMP_TAC [GROUP_ID, GROUP_MUL_RID, GROUP_INV_ID],
        X_GEN_TAC (← q r"g:A") THEN STRIP_TAC THEN
        ASM_SIMP_TAC [GROUP_INV, GROUP_INV_INV],
        MAP_EVERY X_GEN_TAC [← q r"g:A", ← q r"g':A"] THEN STRIP_TAC THEN
        ASM_SIMP_TAC [GROUP_MUL, GROUP_INV_MUL, GROUP_INV] THEN
        X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN
        ASM_SIMP_TAC [GROUP_MUL_ASSOC, GROUP_INV, GROUP_MUL]],
      ALL_TAC] THEN
    EXISTS_TAC (← q r"h:A->bool") THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_SUBGROUP_NEIGHBOURHOOD THEN
      EXISTS_TAC (← q r"G:A group") THEN
      EXISTS_TAC (← q r"(w:A->bool) INTER IMAGE (group_inv G) w") THEN
      ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC [] THEN
        MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"group_id G:A",
                          ← q r"w:A->bool"] OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES) THEN
        ASM_SIMP_TAC [GROUP_ID],
        REWRITE_TAC [IN_INTER, IN_IMAGE] THEN ASM_REWRITE_TAC [] THEN
        EXISTS_TAC (← q r"group_id G:A") THEN ASM_REWRITE_TAC [GROUP_INV_ID],
        FIRST_ASSUM (fun th => tactic_of do
          let t ← q r"open_in top (w:A->bool)"
          pure (ASSUME_TAC (← MATCH_MP OPEN_IN_SUBSET
            (← liftExcept (check (fun th => concl th == t) th))))) THEN
        EXPAND_TAC "h" THEN
        REWRITE_TAC [SUBSET, IN_INTER, IN_IMAGE, IN_ELIM_THM] THEN
        X_GEN_TAC (← q r"g:A") THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN (← q r"z:A") STRIP_ASSUME_TAC)) THEN
        SUBGOAL_THEN (← q r"(z:A) IN group_carrier G") ASSUME_TAC THENL
         [ASM SET_TAC [], ALL_TAC] THEN
        ASM_SIMP_TAC [GROUP_INV, GROUP_INV_INV] THEN ASM SET_TAC []],
      EXPAND_TAC "h" THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"g:A") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"group_id G:A")) THEN
      ASM_SIMP_TAC [GROUP_MUL_LID]])

  pure { PROFINITE_GROUP_CONTINUOUS_EPIMORPHISM, COMPACT_TOPOLOGICAL_GROUP_CLOPEN_SUBGROUP }

/- ------------------------------------------------------------------------- -/
/- Open subgroups suffice for the base; profinite groups are the compact     -/
/- Hausdorff totally disconnected topological groups.                        -/
/- (profinite_groups.ml 1361-1506)                                           -/
/- ------------------------------------------------------------------------- -/

structure PGH where
  PROFINITE_GROUP_OPEN_SUBGROUPS : thm
  PROFINITE_GROUP_TOTALLY_DISCONNECTED : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPGH [HolBase] (D : ProfiniteGroupsDeps) (BPGA : PGA) (BPGE : PGE) (BPGG : PGG) : ExceptT String IO PGH := do
  -- @@SCOPE BEGIN
  let { CLOSED_IN_OPEN_SUBGROUP, CLOSED_IN_TOPOLOGICAL_GROUP_TRANSLATES,
        OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES, topological_group, .. } := BPGA
  let { COMPACT_TOPOLOGICAL_GROUP_FINITE_INDEX, profinite_group,
        PROFINITE_GROUP_COSET_NEIGHBOURHOOD, .. } := BPGE
  let { COMPACT_TOPOLOGICAL_GROUP_CLOPEN_SUBGROUP, .. } := BPGG
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, .. } := D.mt
  let { CLOSED_IN_DIFF, CLOSED_IN_TOPSPACE, COMPACT_IMP_LOCALLY_COMPACT_SPACE,
        CONNECTED_COMPONENT_IN_CONNECTED_COMPONENTS_OF, CONNECTED_COMPONENT_OF_REFL,
        CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE, CONNECTED_IN_CLOPEN_CASES,
        CONNECTED_IN_CONNECTED_COMPONENT_OF, FINITE_IMP_COMPACT_IN, HAUSDORFF_IMP_T1_SPACE,
        OPEN_IN_DIFF, OPEN_IN_INTERS, OPEN_IN_TOPSPACE, T1_SPACE_CLOSED_IN_SING,
        WILDER_LOCALLY_COMPACT_COMPONENT_THM, .. } := D.qmetric
  let { CARD_EQ_LEFT_COSETS_GROUP_COSETS, GROUP_ACTION_KERNEL_POINTWISE,
        GROUP_ACTION_LEFT_COSET_MULTIPLICATION, group_conjugation, GROUP_ID, GROUP_INV,
        GROUP_MUL_ASSOC, GROUP_MUL_RID, GROUP_STABILIZER_LEFT_COSET_MULTIPLICATION,
        IN_RIGHT_COSET_SELF, IN_SUBGROUP_ID, LEFT_COSET_AS_IMAGE, LEFT_COSET_ID,
        NORMAL_SUBGROUP_ACTION_KERNEL, NORMAL_SUBGROUP_IMP_SUBGROUP, RIGHT_COSET_AS_IMAGE,
        SUBGROUP_OF_IMP_SUBSET, .. } := D.qgrouptheory
  let { DISJOINT, ETA_AX, FINITE_IMAGE, FINITE_SING, FORALL_IN_GSPEC, FORALL_IN_IMAGE,
        IMAGE_EQ_EMPTY, .. } := D.mt.core1
  let { IMAGE_o, IN, IN_DIFF, IN_ELIM_THM, IN_IMAGE, IN_INTER, IN_SING, MEMBER_NOT_EMPTY,
        MONO_EXISTS, .. } := D.mt.core2
  let { o_THM, SIMPLE_IMAGE, SING_SUBSET, SUBSET, SUBSET_ANTISYM, SUBSET_TRANS,
        .. } := D.mt.core4
  let { CARD_FINITE_CONG, .. } := D.mt.lib
  -- @@SCOPE END

  let PROFINITE_GROUP_OPEN_SUBGROUPS ← prove
   r"!G (top:A topology).
        profinite_group G top <=>
        topological_group G top /\ compact_space top /\ hausdorff_space top /\
        !w. open_in top w /\ group_id G IN w
            ==> ?h. h subgroup_of G /\ open_in top h /\ h SUBSET w"
   (REPEAT GEN_TAC THEN REWRITE_TAC [profinite_group] THEN
    MATCH_MP_TAC (← TAUT
     (← q r"(a /\ b /\ c ==> (p <=> q)) ==> (a /\ b /\ c /\ p <=> a /\ b /\ c /\ q)"))
    THEN STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
    THEN EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC (← q r"w:A->bool") THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"w:A->bool")) THEN ASM_REWRITE_TAC [] THENL
     [MESON_TAC [NORMAL_SUBGROUP_IMP_SUBGROUP],
      DISCH_THEN (X_CHOOSE_THEN (← q r"h:A->bool") STRIP_ASSUME_TAC)] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
    MP_TAC (← ISPECL [← q r"G:A group", ← q r"h:A->bool"]
                     GROUP_ACTION_LEFT_COSET_MULTIPLICATION) THEN
    ASM_REWRITE_TAC [] THEN
    ABBREV_TAC (← q r"L = {left_coset G x h | x | x IN group_carrier (G:A group)}") THEN
    DISCH_TAC THEN
    SUBGOAL_THEN (← q r"(h:A->bool) IN L") ASSUME_TAC THENL
     [EXPAND_TAC "L" THEN REWRITE_TAC [IN_ELIM_THM] THEN
      EXISTS_TAC (← q r"group_id G:A") THEN ASM_SIMP_TAC [GROUP_ID, LEFT_COSET_ID],
      ALL_TAC] THEN
    EXISTS_TAC
     (← q r"{g | g IN group_carrier G /\
           !c. c IN L ==> (IMAGE o group_mul (G:A group)) g c = c}") THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC NORMAL_SUBGROUP_ACTION_KERNEL THEN
      REWRITE_TAC [ETA_AX] THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [GROUP_ACTION_KERNEL_POINTWISE] THEN
      COND_CASES_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      MATCH_MP_TAC OPEN_IN_INTERS THEN
      REWRITE_TAC [SIMPLE_IMAGE, IMAGE_EQ_EMPTY, FORALL_IN_IMAGE] THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_IMAGE THEN
        MP_TAC (← ISPECL [← q r"G:A group", ← q r"h:A->bool"]
                         CARD_EQ_LEFT_COSETS_GROUP_COSETS) THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (SUBST1_TAC o MATCH_MP CARD_FINITE_CONG) THEN
        MATCH_MP_TAC COMPACT_TOPOLOGICAL_GROUP_FINITE_INDEX THEN
        EXISTS_TAC (← q r"top:A topology") THEN ASM_REWRITE_TAC [],
        EXPAND_TAC "L" THEN REWRITE_TAC [FORALL_IN_GSPEC, ETA_AX] THEN
        X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN
        ASM_SIMP_TAC [GROUP_STABILIZER_LEFT_COSET_MULTIPLICATION] THEN
        SUBGOAL_THEN
         (← q r"IMAGE (group_conjugation G a) h =
          right_coset G (left_coset G a h) (group_inv G (a:A))")
        SUBST1_TAC THENL
         [REWRITE_TAC [LEFT_COSET_AS_IMAGE, RIGHT_COSET_AS_IMAGE, ← GSYM IMAGE_o]
          THEN MATCH_MP_TAC (← SET_RULE
           (← q r"(!x:A. x IN s ==> (f:A->A) x = g x) ==> IMAGE f s = IMAGE g s")) THEN
          X_GEN_TAC (← q r"k:A") THEN DISCH_TAC THEN
          SUBGOAL_THEN (← q r"(k:A) IN group_carrier G") ASSUME_TAC THENL
           [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
          ASM_SIMP_TAC [o_THM, group_conjugation, GROUP_MUL_ASSOC, GROUP_INV],
          ASM_SIMP_TAC [OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES, GROUP_INV]]],
      TRANS_TAC SUBSET_TRANS (← q r"h:A->bool") THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM, o_THM] THEN
      X_GEN_TAC (← q r"g:A") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"h:A->bool")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (fun th => tactic_of do
        pure (GEN_REWRITE_TAC RAND_CONV [← SYM th])) THEN
      REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"group_id G:A") THEN
      ASM_SIMP_TAC [GROUP_MUL_RID, IN_SUBGROUP_ID]])

  let PROFINITE_GROUP_TOTALLY_DISCONNECTED ← prove
   r"!G (top:A topology).
        profinite_group G top <=>
        topological_group G top /\ compact_space top /\ hausdorff_space top /\
        !x. x IN topspace top ==> connected_component_of top x = {x}"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN
      FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [profinite_group]) THEN
      FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o
        GEN_REWRITE_RULE I [topological_group]) THEN
      ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"(x:A) IN connected_component_of top x") ASSUME_TAC THENL
       [REWRITE_TAC [IN] THEN ASM_REWRITE_TAC [CONNECTED_COMPONENT_OF_REFL],
        ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC [SING_SUBSET] THEN
      REWRITE_TAC [SUBSET, IN_SING] THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN
      ASM_CASES_TAC (← q r"y:A = x") THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"(y:A) IN topspace top") ASSUME_TAC THENL
       [ASM_MESON_TAC [CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE, SUBSET],
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"topspace top DIFF {y:A}",
                        ← q r"x:A"] PROFINITE_GROUP_COSET_NEIGHBOURHOOD) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC,
          MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC [OPEN_IN_TOPSPACE] THEN
          ASM_MESON_TAC [T1_SPACE_CLOSED_IN_SING, HAUSDORFF_IMP_T1_SPACE],
          REWRITE_TAC [IN_DIFF, IN_SING] THEN ASM_MESON_TAC []],
        DISCH_THEN (X_CHOOSE_THEN (← q r"u:A->bool") STRIP_ASSUME_TAC)] THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
      SUBGOAL_THEN (← q r"(x:A) IN group_carrier G") ASSUME_TAC THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"top:A topology", ← q r"connected_component_of top (x:A)",
                        ← q r"right_coset G u (x:A)"] CONNECTED_IN_CLOPEN_CASES) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [CONNECTED_IN_CONNECTED_COMPONENT_OF] THEN CONJ_TAC THENL
         [MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"x:A", ← q r"u:A->bool"]
                          CLOSED_IN_TOPOLOGICAL_GROUP_TRANSLATES) THEN
          ASM_MESON_TAC [CLOSED_IN_OPEN_SUBGROUP],
          MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"x:A", ← q r"u:A->bool"]
                          OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES) THEN
          ASM_SIMP_TAC []],
        ALL_TAC] THEN
      MATCH_MP_TAC (← TAUT (← q r"~q /\ (p ==> r) ==> p \/ q ==> r")) THEN CONJ_TAC THENL
       [REWRITE_TAC [DISJOINT, ← GSYM MEMBER_NOT_EMPTY, IN_INTER] THEN
        EXISTS_TAC (← q r"x:A") THEN ASM_SIMP_TAC [IN_RIGHT_COSET_SELF],
        UNDISCH_TAC (← q r"right_coset G u x SUBSET topspace top DIFF {y:A}") THEN
        UNDISCH_TAC (← q r"(y:A) IN connected_component_of top x") THEN SET_TAC []],
      STRIP_TAC THEN REWRITE_TAC [PROFINITE_GROUP_OPEN_SUBGROUPS] THEN
      ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"w:A->bool") THEN STRIP_TAC THEN
      FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o
        GEN_REWRITE_RULE I [topological_group]) THEN
      SUBGOAL_THEN (← q r"(group_id G:A) IN topspace top") ASSUME_TAC THENL
       [ASM_REWRITE_TAC [GROUP_ID], ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"top:A topology", ← q r"{group_id G:A}", ← q r"w:A->bool"]
                       WILDER_LOCALLY_COMPACT_COMPONENT_THM) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC [COMPACT_IMP_LOCALLY_COMPACT_SPACE, SING_SUBSET] THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN (← q r"connected_component_of top (group_id G:A) =
                        {group_id G}") (SUBST1_TAC o SYM) THENL
           [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC,
            ASM_REWRITE_TAC [CONNECTED_COMPONENT_IN_CONNECTED_COMPONENTS_OF]],
          MATCH_MP_TAC FINITE_IMP_COMPACT_IN THEN
          ASM_REWRITE_TAC [SING_SUBSET, FINITE_SING]],
        DISCH_THEN (X_CHOOSE_THEN (← q r"u:A->bool")
         (X_CHOOSE_THEN (← q r"v:A->bool") STRIP_ASSUME_TAC))] THEN
      MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"u:A->bool"]
                       COMPACT_TOPOLOGICAL_GROUP_CLOPEN_SUBGROUP) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
         [SUBGOAL_THEN (← q r"u = topspace top DIFF (v:A->bool)") SUBST1_TAC THENL
           [MAP_EVERY UNDISCH_TAC
             [← q r"DISJOINT (u:A->bool) v",
              ← q r"(u:A->bool) UNION v = topspace top"] THEN
            SET_TAC [],
            ASM_SIMP_TAC [CLOSED_IN_DIFF, CLOSED_IN_TOPSPACE]],
          UNDISCH_TAC (← q r"{group_id G:A} SUBSET u") THEN SET_TAC []],
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"h:A->bool") THEN
        UNDISCH_TAC (← q r"(u:A->bool) SUBSET w") THEN SET_TAC []]])

  pure { PROFINITE_GROUP_OPEN_SUBGROUPS, PROFINITE_GROUP_TOTALLY_DISCONNECTED }

/- ------------------------------------------------------------------------- -/
/- Closed subgroups are intersections of open subgroups (normal ones of      -/
/- open normal subgroups).  (profinite_groups.ml 1508-1637)                  -/
/- ------------------------------------------------------------------------- -/

structure PGI where
  PROFINITE_GROUP_CLOSED_SUBSET_SEPARATION : thm
  PROFINITE_GROUP_CLOSED_SUBGROUP_INTERS : thm
  PROFINITE_GROUP_CLOSED_NORMAL_SUBGROUP_INTERS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPGI [HolBase] (D : ProfiniteGroupsDeps) (BPGA : PGA) (BPGE : PGE) : ExceptT String IO PGI := do
  -- @@SCOPE BEGIN
  let { OPEN_IN_SUBGROUP_NEIGHBOURHOOD, topological_group, .. } := BPGA
  let { profinite_group, PROFINITE_GROUP_COSET_NEIGHBOURHOOD, .. } := BPGE
  let { ASM_MESON_TAC, SET_TAC, .. } := D.mt
  let { CLOSED_IN_SUBSET, OPEN_IN_DIFF, OPEN_IN_TOPSPACE, .. } := D.qmetric
  let { CARRIER_NORMAL_SUBGROUP_OF, CARRIER_SUBGROUP_OF, GROUP_INV, GROUP_MUL_ASSOC,
        GROUP_MUL_RID, GROUP_MUL_RINV, GROUP_SETMUL_INC, GROUP_SETMUL_NORMAL_SUBGROUP,
        GROUP_SETMUL_NORMAL_SUBGROUP_RIGHT, IN_GROUP_SETMUL, IN_SUBGROUP_ID,
        IN_SUBGROUP_INV, LEFT_COSET_AS_IMAGE, NORMAL_SUBGROUP_IMP_SUBGROUP,
        normal_subgroup_of, SUBGROUP_OF_IMP_SUBSET, .. } := D.qgrouptheory
  let { IN_DIFF, IN_ELIM_THM, IN_IMAGE, IN_INTERS, MONO_EXISTS, .. } := D.mt.core2
  let { SUBSET, SUBSET_ANTISYM, SUBSET_INTERS, .. } := D.mt.core4
  let { NOT_EXISTS_THM, .. } := D.mt.core5
  -- @@SCOPE END

  let PROFINITE_GROUP_CLOSED_SUBSET_SEPARATION ← prove
   r"!G (top:A topology) h x.
        profinite_group G top /\ closed_in top h /\
        x IN group_carrier G /\ ~(x IN h)
        ==> ?u. u normal_subgroup_of G /\ open_in top u /\
                ~(x IN group_setmul G h u)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [profinite_group]) THEN
    FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o
      GEN_REWRITE_RULE I [topological_group]) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP CLOSED_IN_SUBSET) THEN
    MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology",
                      ← q r"topspace top DIFF h:A->bool", ← q r"x:A"]
                     PROFINITE_GROUP_COSET_NEIGHBOURHOOD) THEN
    ASM_SIMP_TAC [OPEN_IN_DIFF, OPEN_IN_TOPSPACE, IN_DIFF] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"u:A->bool") THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [IN_GROUP_SETMUL, NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:A", ← q r"b:A"] THEN STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
    SUBGOAL_THEN (← q r"(a:A) IN group_carrier G /\ (b:A) IN group_carrier G")
    STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(a:A) IN right_coset G u x") MP_TAC THENL
     [FIRST_ASSUM (MP_TAC o SPEC (← q r"x:A") o CONJUNCT2 o
        GEN_REWRITE_RULE I [normal_subgroup_of]) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      REWRITE_TAC [LEFT_COSET_AS_IMAGE, IN_IMAGE] THEN
      EXISTS_TAC (← q r"group_inv G b:A") THEN CONJ_TAC THENL
       [ASM_SIMP_TAC [← GSYM GROUP_MUL_ASSOC, GROUP_MUL_RINV, GROUP_MUL_RID,
                      GROUP_INV],
        ASM_MESON_TAC [IN_SUBGROUP_INV]],
      ASM SET_TAC []])

  let PROFINITE_GROUP_CLOSED_SUBGROUP_INTERS ← prove
   r"!G (top:A topology) h.
        profinite_group G top /\ h subgroup_of G /\ closed_in top h
        ==> INTERS {u | u subgroup_of G /\ open_in top u /\ h SUBSET u} = h"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC, SIMP_TAC [SUBSET_INTERS, IN_ELIM_THM]] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC [IN_INTERS, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"x:A") THEN DISCH_THEN (LABEL_TAC "x") THEN
    FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o
      GEN_REWRITE_RULE I [profinite_group]) THEN
    FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o
      GEN_REWRITE_RULE I [topological_group]) THEN
    SUBGOAL_THEN (← q r"(x:A) IN group_carrier G") ASSUME_TAC THENL
     [USE_THEN "x" MATCH_MP_TAC THEN REWRITE_TAC [CARRIER_SUBGROUP_OF] THEN
      FIRST_ASSUM (fun th => tactic_of do
        let t ← q r"topspace top = group_carrier (G:A group)"
        pure (SUBST1_TAC (← SYM (← liftExcept (check (fun th => concl th == t) th))))) THEN
      ASM_SIMP_TAC [OPEN_IN_TOPSPACE, CLOSED_IN_SUBSET],
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"p <=> ~ ~p")] THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"h:A->bool", ← q r"x:A"]
                     PROFINITE_GROUP_CLOSED_SUBSET_SEPARATION) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:A->bool") STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
    SUBGOAL_THEN
     (← q r"group_setmul G h u subgroup_of G /\
      open_in top (group_setmul G h u) /\
      (h:A->bool) SUBSET group_setmul G h u")
    MP_TAC THENL
     [ASM_SIMP_TAC [GROUP_SETMUL_NORMAL_SUBGROUP_RIGHT, GROUP_SETMUL_INC] THEN
      MATCH_MP_TAC OPEN_IN_SUBGROUP_NEIGHBOURHOOD THEN
      MAP_EVERY EXISTS_TAC [← q r"G:A group", ← q r"u:A->bool"] THEN
      ASM_SIMP_TAC [GROUP_SETMUL_NORMAL_SUBGROUP_RIGHT, GROUP_SETMUL_INC,
                    IN_SUBGROUP_ID],
      ASM_MESON_TAC []])

  let PROFINITE_GROUP_CLOSED_NORMAL_SUBGROUP_INTERS ← prove
   r"!G (top:A topology) h.
        profinite_group G top /\ h normal_subgroup_of G /\ closed_in top h
        ==> INTERS {u | u normal_subgroup_of G /\ open_in top u /\
                        h SUBSET u} = h"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC, SIMP_TAC [SUBSET_INTERS, IN_ELIM_THM]] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC [IN_INTERS, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"x:A") THEN DISCH_THEN (LABEL_TAC "x") THEN
    FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o
      GEN_REWRITE_RULE I [profinite_group]) THEN
    FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o
      GEN_REWRITE_RULE I [topological_group]) THEN
    FIRST_ASSUM (fun th => tactic_of do
      let t ← q r"(h:A->bool) normal_subgroup_of G"
      pure (ASSUME_TAC (← MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP
        (← liftExcept (check (fun th => concl th == t) th))))) THEN
    SUBGOAL_THEN (← q r"(x:A) IN group_carrier G") ASSUME_TAC THENL
     [USE_THEN "x" MATCH_MP_TAC THEN REWRITE_TAC [CARRIER_NORMAL_SUBGROUP_OF] THEN
      FIRST_ASSUM (fun th => tactic_of do
        let t ← q r"topspace top = group_carrier (G:A group)"
        pure (SUBST1_TAC (← SYM (← liftExcept (check (fun th => concl th == t) th))))) THEN
      ASM_SIMP_TAC [OPEN_IN_TOPSPACE, CLOSED_IN_SUBSET],
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"p <=> ~ ~p")] THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"h:A->bool", ← q r"x:A"]
                     PROFINITE_GROUP_CLOSED_SUBSET_SEPARATION) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:A->bool") STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (fun th => tactic_of do
      let t ← q r"(u:A->bool) normal_subgroup_of G"
      pure (ASSUME_TAC (← MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP
        (← liftExcept (check (fun th => concl th == t) th))))) THEN
    SUBGOAL_THEN
     (← q r"group_setmul G h u normal_subgroup_of G /\
      open_in top (group_setmul G h u) /\
      (h:A->bool) SUBSET group_setmul G h u")
    MP_TAC THENL
     [ASM_SIMP_TAC [GROUP_SETMUL_NORMAL_SUBGROUP, GROUP_SETMUL_INC] THEN
      MATCH_MP_TAC OPEN_IN_SUBGROUP_NEIGHBOURHOOD THEN
      MAP_EVERY EXISTS_TAC [← q r"G:A group", ← q r"u:A->bool"] THEN
      ASM_SIMP_TAC [GROUP_SETMUL_NORMAL_SUBGROUP_RIGHT, GROUP_SETMUL_INC,
                    IN_SUBGROUP_ID],
      ASM_MESON_TAC []])

  pure { PROFINITE_GROUP_CLOSED_SUBSET_SEPARATION, PROFINITE_GROUP_CLOSED_SUBGROUP_INTERS,
         PROFINITE_GROUP_CLOSED_NORMAL_SUBGROUP_INTERS }

/- ------------------------------------------------------------------------- -/
/- Products and inverse limits of profinite groups.                          -/
/- (profinite_groups.ml 1639-1768)                                           -/
/- ------------------------------------------------------------------------- -/

structure PGJ where
  PROFINITE_GROUP_PRODUCT_GROUP : thm
  PROFINITE_GROUP_INVERSE_LIMIT : thm
  PROFINITE_GROUP_INVERSE_LIMIT_INTEGER_MOD_GROUP : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPGJ [HolBase] (D : ProfiniteGroupsDeps) (BPGA : PGA) (BPGD : PGD) (BPGE : PGE) (BPGF : PGF) : ExceptT String IO PGJ := do
  -- @@SCOPE BEGIN
  let { topological_group, .. } := BPGA
  let { TOPOLOGICAL_GROUP_PRODUCT_GROUP, .. } := BPGD
  let { profinite_group, PROFINITE_GROUP_FINITE_DISCRETE, .. } := BPGE
  let { PROFINITE_GROUP_CLOSED_SUBGROUP, .. } := BPGF
  let { ASM_MESON_TAC, MESON_TAC, .. } := D.mt
  let { CLOSED_IN_CONTINUOUS_MAPS_EQ, CLOSED_IN_INTERS, CLOSED_IN_TOPSPACE,
        COMPACT_SPACE_PRODUCT_TOPOLOGY, CONTINUOUS_MAP_COMPOSE,
        CONTINUOUS_MAP_FROM_DISCRETE_TOPOLOGY, CONTINUOUS_MAP_PRODUCT_PROJECTION,
        HAUSDORFF_SPACE_PRODUCT_TOPOLOGY, OPEN_IN_CARTESIAN_PRODUCT_GEN,
        OPEN_IN_PRODUCT_TOPOLOGY_ALT, OPEN_IN_TOPSPACE, TOPSPACE_DISCRETE_TOPOLOGY,
        TOPSPACE_PRODUCT_TOPOLOGY, .. } := D.qmetric
  let { CARRIER_NORMAL_SUBGROUP_OF, CARRIER_SUBGROUP_GENERATED_SUBGROUP,
        CARTESIAN_PRODUCT_NORMAL_SUBGROUP_OF_PRODUCT_GROUP, FINITE_INTEGER_MOD_GROUP,
        GROUP_HOMOMORPHISM_INTEGER_MOD_GROUP_REM, INTEGER_MOD_GROUP_1R,
        inverse_limit_group, INVERSE_LIMIT_SUBGROUP_OF_PRODUCT_GROUP, PRODUCT_GROUP,
        .. } := D.qgrouptheory
  let { EXTENSION, FINITE_SUBSET, FORALL_IN_GSPEC, FORALL_IN_IMAGE, FORALL_IN_INSERT,
        FUN_EQ_THM, .. } := D.mt.core1
  let { IMP_CONJ, IN_ELIM_THM, IN_INTER, IN_INTERS, INTERS_INSERT, NOT_INSERT_EMPTY,
        .. } := D.mt.core2
  let { cartesian_product, o_THM, RESTRICTION_IN_CARTESIAN_PRODUCT, SKOLEM_THM, SUBSET,
        SUBSET_CARTESIAN_PRODUCT, SUBSET_REFL, SUBSET_TRANS, .. } := D.mt.core4
  let { RIGHT_IMP_EXISTS_THM, .. } := D.mt.core5
  -- @@SCOPE END
  -- `can (find_term (fun t -> is_const t && fst(dest_const t) = c)) (concl th)`
  let hasConst : String → thm → Bool := fun c th =>
    HolCore.Lib.can (HolCore.Basics.find_term (fun t => HolCore.Kernel.is_const t &&
      (match HolCore.Kernel.dest_const t with
       | .ok (n, _) => n == c | .error _ => false))) (concl th)

  let PROFINITE_GROUP_PRODUCT_GROUP ← prove
   r"!k (G:I->A group) (top:I->A topology).
        (!i. i IN k ==> profinite_group (G i) (top i))
        ==> profinite_group (product_group k G) (product_topology k top)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [profinite_group] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC TOPOLOGICAL_GROUP_PRODUCT_GROUP THEN
      ASM_MESON_TAC [profinite_group],
      REWRITE_TAC [COMPACT_SPACE_PRODUCT_TOPOLOGY] THEN DISJ2_TAC THEN
      ASM_MESON_TAC [profinite_group],
      REWRITE_TAC [HAUSDORFF_SPACE_PRODUCT_TOPOLOGY] THEN DISJ2_TAC THEN
      ASM_MESON_TAC [profinite_group],
      ALL_TAC] THEN
    X_GEN_TAC (← q r"w:(I->A)->bool") THEN REWRITE_TAC [PRODUCT_GROUP] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [OPEN_IN_PRODUCT_TOPOLOGY_ALT] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"RESTRICTION k (\i. group_id((G:I->A group) i))"))
    THEN ASM_REWRITE_TAC [RESTRICTION_IN_CARTESIAN_PRODUCT] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:I->A->bool") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     (← q r"!i. i IN k
          ==> ?v. v normal_subgroup_of (G:I->A group) i /\
                  open_in ((top:I->A topology) i) v /\ v SUBSET u i /\
                  (u i = topspace(top i) ==> v = group_carrier(G i))")
    MP_TAC THENL
     [X_GEN_TAC (← q r"i:I") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"i:I") o check (hasConst "profinite_group"))
      THEN
      ASM_REWRITE_TAC [profinite_group] THEN STRIP_TAC THEN
      ASM_CASES_TAC (← q r"(u:I->A->bool) i = topspace((top:I->A topology) i)") THEN
      ASM_REWRITE_TAC [] THENL
       [EXISTS_TAC (← q r"group_carrier((G:I->A group) i)") THEN
        ASM_MESON_TAC [CARRIER_NORMAL_SUBGROUP_OF, OPEN_IN_TOPSPACE,
                       topological_group, SUBSET_REFL],
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC []],
      DISCH_THEN (X_CHOOSE_TAC (← q r"v:I->A->bool") o
        REWRITE_RULE [RIGHT_IMP_EXISTS_THM, SKOLEM_THM])] THEN
    EXISTS_TAC (← q r"cartesian_product k (v:I->A->bool)") THEN
    ASM_SIMP_TAC [CARTESIAN_PRODUCT_NORMAL_SUBGROUP_OF_PRODUCT_GROUP] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [OPEN_IN_CARTESIAN_PRODUCT_GEN] THEN DISJ2_TAC THEN
      ASM_SIMP_TAC [] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
        FINITE_SUBSET) o check (hasConst "FINITE")) THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [topological_group,
        profinite_group],
      TRANS_TAC SUBSET_TRANS (← q r"cartesian_product k (u:I->A->bool)") THEN
      ASM_REWRITE_TAC [SUBSET_CARTESIAN_PRODUCT] THEN DISJ2_TAC THEN
      ASM_SIMP_TAC []])

  let PROFINITE_GROUP_INVERSE_LIMIT ← prove
   r"!k (le:I->I->bool) (G:I->A group) (f:I->I->A->A) (top:I->A topology).
        (!i. i IN k ==> profinite_group (G i) (top i)) /\
        (!i j. i IN k /\ j IN k /\ le i j
               ==> group_homomorphism (G j,G i) (f i j) /\
                   continuous_map (top j,top i) (f i j))
        ==> profinite_group (inverse_limit_group k le G f)
             (subtopology (product_topology k top)
                          (group_carrier(inverse_limit_group k le G f)))"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"k:I->bool", ← q r"le:I->I->bool", ← q r"G:I->A group",
                      ← q r"f:I->I->A->A"] INVERSE_LIMIT_SUBGROUP_OF_PRODUCT_GROUP) THEN
    ASM_SIMP_TAC [] THEN DISCH_TAC THEN
    ASM_SIMP_TAC [inverse_limit_group, CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
    MATCH_MP_TAC PROFINITE_GROUP_CLOSED_SUBGROUP THEN
    ASM_SIMP_TAC [PROFINITE_GROUP_PRODUCT_GROUP] THEN
    SUBGOAL_THEN
     (← q r"topspace(product_topology k (top:I->A topology)) =
      group_carrier(product_group k (G:I->A group))")
    ASSUME_TAC THENL
     [REWRITE_TAC [TOPSPACE_PRODUCT_TOPOLOGY, PRODUCT_GROUP] THEN
      REWRITE_TAC [cartesian_product, o_THM] THEN
      SUBGOAL_THEN
       (← q r"!i. i IN k ==> topspace((top:I->A topology) i) = group_carrier(G i)")
       (fun th => SIMP_TAC [th]) THEN
      ASM_MESON_TAC [profinite_group, topological_group],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"{x | x IN group_carrier(product_group k G) /\
           !i j. i IN k /\ j IN k /\ le i j ==> f i j (x j) = x i} =
      INTERS (topspace(product_topology k (top:I->A topology)) INSERT
              {{x | x IN topspace(product_topology k top) /\
                    (f:I->I->A->A) i j (x j) = x i} |i,j|
               i IN k /\ j IN k /\ (le:I->I->bool) i j})")
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC [INTERS_INSERT] THEN
      GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC [IN_INTER, IN_INTERS, FORALL_IN_GSPEC, IN_ELIM_THM] THEN
      MESON_TAC [],
      MATCH_MP_TAC CLOSED_IN_INTERS THEN
      REWRITE_TAC [NOT_INSERT_EMPTY, FORALL_IN_INSERT, CLOSED_IN_TOPSPACE] THEN
      REWRITE_TAC [FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [← q r"i:I", ← q r"j:I"] THEN STRIP_TAC THEN
      MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAPS_EQ THEN
      EXISTS_TAC (← q r"(top:I->A topology) i") THEN
      ASM_SIMP_TAC [CONTINUOUS_MAP_PRODUCT_PROJECTION] THEN CONJ_TAC THENL
       [ASM_MESON_TAC [profinite_group], ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"(\x. (f:I->I->A->A) i j (x j)) = f i j o (\x. x j)")
      SUBST1_TAC THENL [REWRITE_TAC [FUN_EQ_THM, o_THM], ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC (← q r"(top:I->A topology) j") THEN
      ASM_SIMP_TAC [CONTINUOUS_MAP_PRODUCT_PROJECTION]])

  let PROFINITE_GROUP_INVERSE_LIMIT_INTEGER_MOD_GROUP ← prove
   r"!k (le:I->I->bool) (n:I->num).
        (!i. i IN k ==> ~(n i = 0)) /\
        (!i j. i IN k /\ j IN k /\ le i j ==> n i divides n j)
        ==> profinite_group
             (inverse_limit_group k le (\i. integer_mod_group(n i))
                                  (\i j x. x rem &(n i)))
             (subtopology
               (product_topology k
                 (\i. discrete_topology(group_carrier(integer_mod_group(n i)))))
               (group_carrier
                 (inverse_limit_group k le (\i. integer_mod_group(n i))
                                      (\i j x. x rem &(n i)))))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC PROFINITE_GROUP_INVERSE_LIMIT THEN
    REWRITE_TAC [] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC PROFINITE_GROUP_FINITE_DISCRETE THEN
      ASM_SIMP_TAC [FINITE_INTEGER_MOD_GROUP],
      MAP_EVERY X_GEN_TAC [← q r"i:I", ← q r"j:I"] THEN STRIP_TAC THEN
      ASM_SIMP_TAC [GROUP_HOMOMORPHISM_INTEGER_MOD_GROUP_REM] THEN
      REWRITE_TAC [CONTINUOUS_MAP_FROM_DISCRETE_TOPOLOGY] THEN
      REWRITE_TAC [TOPSPACE_DISCRETE_TOPOLOGY, SUBSET, FORALL_IN_IMAGE] THEN
      REWRITE_TAC [INTEGER_MOD_GROUP_1R]])

  pure { PROFINITE_GROUP_PRODUCT_GROUP, PROFINITE_GROUP_INVERSE_LIMIT,
         PROFINITE_GROUP_INVERSE_LIMIT_INTEGER_MOD_GROUP }

/- ------------------------------------------------------------------------- -/
/- A profinite group is the inverse limit of its finite quotients, as a      -/
/- group and as a space.  (profinite_groups.ml 1770-2146)                    -/
/- ------------------------------------------------------------------------- -/

structure PGK where
  PROFINITE_GROUP_INVERSE_LIMIT_QUOTIENTS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPGK [HolBase] (D : ProfiniteGroupsDeps) (BPGA : PGA) (BPGC : PGC) (BPGE : PGE) (BPGF : PGF) : ExceptT String IO PGK := do
  -- @@SCOPE BEGIN
  let { CLOSED_IN_OPEN_SUBGROUP, topological_group, TOPOLOGICAL_GROUP_HOMEOMORPHIC_MAPS,
        .. } := BPGA
  let { QUOTIENT_TOPOLOGY_OPEN_NORMAL_SUBGROUP, .. } := BPGC
  let { profinite_group, .. } := BPGE
  let { OPEN_NORMAL_SUBGROUP_INTERS, .. } := BPGF
  let { ASM_MESON_TAC, MESON_TAC, SELECT_CONV, SET_TAC, .. } := D.mt
  let { COMPACT_SPACE_FIP, CONTINUOUS_IMP_HOMEOMORPHIC_MAP, CONTINUOUS_MAP_COMPONENTWISE,
        CONTINUOUS_MAP_IN_SUBTOPOLOGY, CONTINUOUS_MAP_QUOTIENT_TOPOLOGY,
        HAUSDORFF_IMP_T1_SPACE, HAUSDORFF_SPACE_DISCRETE_TOPOLOGY,
        HAUSDORFF_SPACE_PRODUCT_TOPOLOGY, HAUSDORFF_SPACE_SUBTOPOLOGY,
        HOMEOMORPHIC_MAP_CLOSEDNESS, OPEN_IN_DIFF, OPEN_IN_TOPSPACE,
        T1_SPACE_CLOSED_IN_SING, TOPSPACE_DISCRETE_TOPOLOGY, TOPSPACE_PRODUCT_TOPOLOGY,
        TOPSPACE_SUBTOPOLOGY, .. } := D.qmetric
  let { CARRIER_NORMAL_SUBGROUP_OF, GROUP_DIV, GROUP_DIV_EQ_ID, GROUP_HOMOMORPHISM,
        GROUP_ID, GROUP_ISOMORPHISM, GROUP_MUL, IN_RIGHT_COSET_SELF, INVERSE_LIMIT_GROUP,
        NORMAL_SUBGROUP_IMP_SUBGROUP, QUOTIENT_GROUP, QUOTIENT_GROUP_MUL, RIGHT_COSET,
        RIGHT_COSET_AS_IMAGE, RIGHT_COSET_EQ, RIGHT_COSETS_EQ, SUBGROUP_OF_IMP_SUBSET,
        .. } := D.qgrouptheory
  let { DISJOINT, ETA_AX, EXTENSIONAL, FINITE_SUBSET_IMAGE, FORALL_IN_GSPEC,
        FORALL_IN_IMAGE, FUN_EQ_THM, .. } := D.mt.core1
  let { IMAGE_SUBSET, IMP_CONJ, IN_DIFF, IN_ELIM_THM, IN_IMAGE, IN_INTER, IN_SING,
        INTERS_IMAGE, MEMBER_NOT_EMPTY, .. } := D.mt.core2
  let { cartesian_product, o_DEF, RESTRICTION, RESTRICTION_IN_CARTESIAN_PRODUCT,
        RESTRICTION_IN_EXTENSIONAL, RIGHT_FORALL_IMP_THM, SKOLEM_THM, SUBSET,
        SUBSET_ANTISYM, SUBSET_ANTISYM_EQ, .. } := D.mt.core4
  let { RIGHT_EXISTS_IMP_THM, .. } := D.mt.core5
  -- @@SCOPE END

  let PROFINITE_GROUP_INVERSE_LIMIT_QUOTIENTS ← prove
   r"!G (top:A topology).
        profinite_group G top
        ==> group_isomorphism
             (G,inverse_limit_group
                 {u | u normal_subgroup_of G /\ open_in top u}
                 (\u v. v SUBSET u) (quotient_group G)
                 (\u v x. right_coset G u (@g. g IN x)))
             (\g. RESTRICTION {u | u normal_subgroup_of G /\ open_in top u}
                    (\u. right_coset G u g)) /\
            homeomorphic_map
             (top,
              subtopology
               (product_topology {u | u normal_subgroup_of G /\ open_in top u}
                  (\u. discrete_topology(group_carrier(quotient_group G u))))
               (group_carrier
                 (inverse_limit_group
                   {u | u normal_subgroup_of G /\ open_in top u}
                   (\u v. v SUBSET u) (quotient_group G)
                   (\u v x. right_coset G u (@g. g IN x)))))
             (\g. RESTRICTION {u | u normal_subgroup_of G /\ open_in top u}
                    (\u. right_coset G u g))"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [profinite_group]) THEN
    FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [topological_group])
    THEN
    ABBREV_TAC (← q r"k = {u | u normal_subgroup_of G /\ open_in (top:A topology) u}")
    THEN
    SUBGOAL_THEN
     (← q r"!u v x:A. u IN k /\ v IN k /\ v SUBSET u /\ x IN group_carrier G
                ==> right_coset G u (@g. g IN right_coset G v x) =
                    right_coset G u x")
    ASSUME_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q r"u:A->bool", ← q r"v:A->bool", ← q r"x:A"] THEN
      EXPAND_TAC "k" THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN
      MAP_EVERY (fun t => FIRST_ASSUM (ASSUME_TAC o MATCH_MP
        NORMAL_SUBGROUP_IMP_SUBGROUP o check (fun th => concl th == t)))
       [← q r"(u:A->bool) normal_subgroup_of G", ← q r"(v:A->bool) normal_subgroup_of G"]
      THEN
      SUBGOAL_THEN (← q r"(@g:A. g IN right_coset G v x) IN right_coset G v x")
      ASSUME_TAC THENL
       [CONV_TAC SELECT_CONV THEN EXISTS_TAC (← q r"x:A") THEN
        ASM_SIMP_TAC [IN_RIGHT_COSET_SELF],
        ALL_TAC] THEN
      ABBREV_TAC (← q r"y = @g:A. g IN right_coset G v x") THEN
      SUBGOAL_THEN (← q r"(y:A) IN group_carrier G /\ y IN right_coset G u x")
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MP_TAC (← ISPECL [← q r"G:A group", ← q r"v:A->bool", ← q r"x:A"] RIGHT_COSET) THEN
          ASM_SIMP_TAC [SUBGROUP_OF_IMP_SUBSET] THEN ASM SET_TAC [],
          UNDISCH_TAC (← q r"(y:A) IN right_coset G v x") THEN
          SPEC_TAC (← q r"y:A", ← q r"y:A") THEN
          REWRITE_TAC [← GSYM SUBSET, RIGHT_COSET_AS_IMAGE] THEN
          MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC []],
        ALL_TAC] THEN
      ASM_SIMP_TAC [RIGHT_COSETS_EQ] THEN
      REWRITE_TAC [DISJOINT, ← GSYM MEMBER_NOT_EMPTY, IN_INTER] THEN
      EXISTS_TAC (← q r"y:A") THEN ASM_SIMP_TAC [IN_RIGHT_COSET_SELF],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!u v. u IN k /\ v IN k /\ v SUBSET u
            ==> group_homomorphism (quotient_group G v,quotient_group G u)
                                   (\X. right_coset G u (@g:A. g IN X))")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"(u:A->bool) normal_subgroup_of G /\ (v:A->bool) normal_subgroup_of G")
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [← q r"(u:A->bool) IN k", ← q r"(v:A->bool) IN k"] THEN
        EXPAND_TAC "k" THEN SIMP_TAC [IN_ELIM_THM],
        ALL_TAC] THEN
      REWRITE_TAC [GROUP_HOMOMORPHISM, SUBSET, FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC [← CONJUNCT1 QUOTIENT_GROUP] THEN
      REWRITE_TAC [FORALL_IN_GSPEC, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
      ASM_SIMP_TAC [QUOTIENT_GROUP_MUL, GROUP_MUL] THEN
      REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [],
      ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"k:(A->bool)->bool", ← q r"\u v:A->bool. v SUBSET u",
      ← q r"quotient_group (G:A group)",
      ← q r"\u (v:A->bool) (x:A->bool). right_coset G u (@g:A. g IN x)"]
     INVERSE_LIMIT_GROUP) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC [], STRIP_TAC] THEN
    ABBREV_TAC
     (← q r"L = inverse_limit_group k (\u v:A->bool. v SUBSET u)
           (quotient_group (G:A group))
           (\u (v:A->bool) (x:A->bool). right_coset G u (@g:A. g IN x))") THEN
    SUBGOAL_THEN
     (← q r"!u. u IN k ==> (u:A->bool) normal_subgroup_of G /\ open_in top u")
    ASSUME_TAC THENL [EXPAND_TAC "k" THEN SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"group_carrier(G:A group) IN (k:(A->bool)->bool)")
    ASSUME_TAC THENL
     [EXPAND_TAC "k" THEN REWRITE_TAC [IN_ELIM_THM] THEN
      REWRITE_TAC [CARRIER_NORMAL_SUBGROUP_OF] THEN
      ASM_MESON_TAC [OPEN_IN_TOPSPACE],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!g:A. g IN group_carrier G
            ==> RESTRICTION k (\u. right_coset G u g) IN group_carrier L")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"g:A") THEN DISCH_TAC THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN
      REWRITE_TAC [RESTRICTION_IN_CARTESIAN_PRODUCT] THEN CONJ_TAC THENL
       [X_GEN_TAC (← q r"u:A->bool") THEN DISCH_TAC THEN
        ASM_REWRITE_TAC [RESTRICTION] THEN
        UNDISCH_TAC
         (← q r"!u. u IN k ==> (u:A->bool) normal_subgroup_of G /\ open_in top u") THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"u:A->bool")) THEN
        ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
        ASM_SIMP_TAC [QUOTIENT_GROUP, IN_ELIM_THM] THEN ASM_MESON_TAC [],
        ASM_SIMP_TAC [RESTRICTION]],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!y. y IN group_carrier L
          ==> ?g:A. g IN group_carrier G /\
                    RESTRICTION k (\u. right_coset G u g) = y")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"y:(A->bool)->(A->bool)") THEN
      ASM_REWRITE_TAC [IN_ELIM_THM, cartesian_product] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"?a:(A->bool)->A.
          !u. u IN k ==> a u IN group_carrier G /\ y u = right_coset G u (a u)")
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC [← GSYM SKOLEM_THM, RIGHT_EXISTS_IMP_THM] THEN
        X_GEN_TAC (← q r"u:A->bool") THEN DISCH_TAC THEN
        UNDISCH_TAC
         (← q r"!u. u IN k ==> (y:(A->bool)->(A->bool)) u IN
                         group_carrier(quotient_group G u)") THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"u:A->bool")) THEN
        UNDISCH_TAC
         (← q r"!u. u IN k ==> (u:A->bool) normal_subgroup_of G /\ open_in top u") THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"u:A->bool")) THEN
        ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
        ASM_SIMP_TAC [QUOTIENT_GROUP, IN_ELIM_THM] THEN MESON_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!u v. u IN k /\ v IN k /\ v SUBSET u
              ==> (y:(A->bool)->(A->bool)) u = right_coset G u (a v)")
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN
        UNDISCH_TAC
         (← q r"!u v. u IN k /\ v IN k /\ v SUBSET u
                ==> right_coset G u (@g:A. g IN (y:(A->bool)->(A->bool)) v) =
                    y u") THEN
        DISCH_THEN (MP_TAC o SPECL [← q r"u:A->bool", ← q r"v:A->bool"]) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
        UNDISCH_TAC
         (← q r"!u. u IN k ==> (a:(A->bool)->A) u IN group_carrier G /\
                         (y:(A->bool)->(A->bool)) u = right_coset G u (a u)") THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"v:A->bool")) THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o check (fun th =>
          (HolCore.Basics.strip_forall (concl th)).1.length == 3)) THEN
        ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"~(INTERS (IMAGE (y:(A->bool)->(A->bool)) k) = {})")
      MP_TAC THENL
       [UNDISCH_TAC (← q r"compact_space(top:A topology)") THEN
        REWRITE_TAC [COMPACT_SPACE_FIP] THEN DISCH_THEN MATCH_MP_TAC THEN
        CONJ_TAC THENL
         [REWRITE_TAC [FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"u:A->bool") THEN
          DISCH_TAC THEN
          UNDISCH_TAC
           (← q r"!u. u IN k ==> (u:A->bool) normal_subgroup_of G /\ open_in top u")
          THEN DISCH_THEN (MP_TAC o SPEC (← q r"u:A->bool")) THEN
          UNDISCH_TAC
           (← q r"!u. u IN k ==> (a:(A->bool)->A) u IN group_carrier G /\
                           (y:(A->bool)->(A->bool)) u = right_coset G u (a u)")
          THEN DISCH_THEN (MP_TAC o SPEC (← q r"u:A->bool")) THEN
          ASM_REWRITE_TAC [] THEN
          DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN STRIP_TAC THEN
          FIRST_ASSUM (ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
          MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology",
                            ← q r"(a:(A->bool)->A) u"]
                           TOPOLOGICAL_GROUP_HOMEOMORPHIC_MAPS) THEN
          ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
          REWRITE_TAC [RIGHT_COSET_AS_IMAGE] THEN
          MP_TAC (← ISPECL [← q r"\x:A. group_mul G x ((a:(A->bool)->A) u)",
                            ← q r"top:A topology", ← q r"top:A topology", ← q r"u:A->bool"]
                           HOMEOMORPHIC_MAP_CLOSEDNESS) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUBGROUP_OF_IMP_SUBSET THEN
            ASM_REWRITE_TAC [],
            DISCH_THEN SUBST1_TAC] THEN
          MATCH_MP_TAC CLOSED_IN_OPEN_SUBGROUP THEN
          EXISTS_TAC (← q r"G:A group") THEN ASM_REWRITE_TAC [],
          ALL_TAC] THEN
        X_GEN_TAC (← q r"f':(A->bool)->bool") THEN REWRITE_TAC [FINITE_SUBSET_IMAGE] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"s:(A->bool)->bool")
         (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))
        THEN
        MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"s:(A->bool)->bool"]
                         OPEN_NORMAL_SUBGROUP_INTERS) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC [] THEN
          UNDISCH_TAC (← q r"(s:(A->bool)->bool) SUBSET k") THEN
          UNDISCH_TAC
           (← q r"!u. u IN k ==> (u:A->bool) normal_subgroup_of G /\ open_in top u")
          THEN SET_TAC [],
          STRIP_TAC] THEN
        ABBREV_TAC (← q r"v = group_carrier G INTER INTERS (s:(A->bool)->bool)") THEN
        SUBGOAL_THEN (← q r"(v:A->bool) IN k") ASSUME_TAC THENL
         [EXPAND_TAC "k" THEN ASM_REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN
        REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN
        EXISTS_TAC (← q r"(a:(A->bool)->A) v") THEN
        REWRITE_TAC [INTERS_IMAGE, IN_ELIM_THM] THEN
        X_GEN_TAC (← q r"w:A->bool") THEN DISCH_TAC THEN
        SUBGOAL_THEN (← q r"(w:A->bool) IN k /\ v SUBSET w") STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC (← q r"(w:A->bool) IN s") THEN
          UNDISCH_TAC (← q r"(s:(A->bool)->bool) SUBSET k") THEN
          EXPAND_TAC "v" THEN SET_TAC [],
          ALL_TAC] THEN
        UNDISCH_TAC
         (← q r"!u v. u IN k /\ v IN k /\ v SUBSET u
                ==> (y:(A->bool)->(A->bool)) u =
                    right_coset G u ((a:(A->bool)->A) v)") THEN
        DISCH_THEN (MP_TAC o SPECL [← q r"w:A->bool", ← q r"v:A->bool"]) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC IN_RIGHT_COSET_SELF THEN CONJ_TAC THENL
         [MATCH_MP_TAC NORMAL_SUBGROUP_IMP_SUBGROUP THEN
          UNDISCH_TAC
           (← q r"!u. u IN k ==> (u:A->bool) normal_subgroup_of G /\ open_in top u")
          THEN DISCH_THEN (MP_TAC o SPEC (← q r"w:A->bool")) THEN
          ASM_SIMP_TAC [],
          UNDISCH_TAC
           (← q r"!u. u IN k ==> (a:(A->bool)->A) u IN group_carrier G /\
                           (y:(A->bool)->(A->bool)) u = right_coset G u (a u)")
          THEN DISCH_THEN (MP_TAC o SPEC (← q r"v:A->bool")) THEN ASM_SIMP_TAC []],
        ALL_TAC] THEN
      REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, INTERS_IMAGE, IN_ELIM_THM] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"g:A")) THEN
      SUBGOAL_THEN
       (← q r"!u. u IN k ==> (g:A) IN group_carrier G /\
                       right_coset G u g = (y:(A->bool)->(A->bool)) u")
      ASSUME_TAC THENL
       [X_GEN_TAC (← q r"u:A->bool") THEN DISCH_TAC THEN
        UNDISCH_TAC
         (← q r"!u. u IN k ==> (u:A->bool) normal_subgroup_of G /\ open_in top u")
        THEN DISCH_THEN (MP_TAC o SPEC (← q r"u:A->bool")) THEN
        UNDISCH_TAC
         (← q r"!u. u IN k ==> (a:(A->bool)->A) u IN group_carrier G /\
                         (y:(A->bool)->(A->bool)) u = right_coset G u (a u)")
        THEN DISCH_THEN (MP_TAC o SPEC (← q r"u:A->bool")) THEN
        UNDISCH_TAC (← q r"!x. x IN k ==> (g:A) IN (y:(A->bool)->(A->bool)) x") THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"u:A->bool")) THEN
        ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN STRIP_TAC THEN
        FIRST_ASSUM (ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
        SUBGOAL_THEN (← q r"(g:A) IN group_carrier G") ASSUME_TAC THENL
         [MP_TAC (← ISPECL [← q r"G:A group", ← q r"u:A->bool", ← q r"(a:(A->bool)->A) u"]
                          RIGHT_COSET) THEN
          ASM_SIMP_TAC [SUBGROUP_OF_IMP_SUBSET] THEN ASM SET_TAC [],
          ASM_SIMP_TAC [RIGHT_COSETS_EQ]] THEN
        REWRITE_TAC [DISJOINT, ← GSYM MEMBER_NOT_EMPTY, IN_INTER] THEN
        EXISTS_TAC (← q r"g:A") THEN ASM_SIMP_TAC [IN_RIGHT_COSET_SELF],
        ALL_TAC] THEN
      EXISTS_TAC (← q r"g:A") THEN CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC (← q r"u:A->bool") THEN
      REWRITE_TAC [RESTRICTION] THEN COND_CASES_TAC THENL
       [ASM_MESON_TAC [],
        UNDISCH_TAC (← q r"EXTENSIONAL k (y:(A->bool)->(A->bool))") THEN
        REWRITE_TAC [EXTENSIONAL, IN_ELIM_THM] THEN ASM_MESON_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"group_carrier L SUBSET
      topspace(product_topology k
       (\u. discrete_topology(group_carrier(quotient_group G (u:A->bool)))))")
    ASSUME_TAC THENL
     [REWRITE_TAC [TOPSPACE_PRODUCT_TOPOLOGY, o_DEF,
                   TOPSPACE_DISCRETE_TOPOLOGY] THEN
      ASM_REWRITE_TAC [SUBSET, cartesian_product, IN_ELIM_THM] THEN MESON_TAC [],
      ALL_TAC] THEN
    -- `K ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `..`)`:
    -- the quotation is parsed only when `is_eq` holds, as `&&`.
    FIRST_X_ASSUM (fun th => tactic_of do
      let ok ← if is_eq (concl th) then do
          let z ← q r"group_carrier(L:((A->bool)->(A->bool)) group)"
          pure (match lhs (concl th) with | .ok r => r == z | .error _ => false)
        else pure false
      let _ ← liftExcept (check (fun _ => ok) th)
      pure ALL_TAC) THEN
    SUBGOAL_THEN
     (← q r"!g h:A. g IN group_carrier G /\ h IN group_carrier G
              ==> (RESTRICTION k (\u. right_coset G u g) =
                   RESTRICTION k (\u. right_coset G u h) <=> g = h)")
    ASSUME_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q r"g:A", ← q r"h:A"] THEN STRIP_TAC THEN
      EQ_TAC THENL [DISCH_TAC, SIMP_TAC []] THEN
      MP_TAC (← ISPECL [← q r"G:A group", ← q r"g:A", ← q r"h:A"] GROUP_DIV_EQ_ID) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      ABBREV_TAC (← q r"x = group_div G g (h:A)") THEN
      SUBGOAL_THEN (← q r"(x:A) IN group_carrier G") ASSUME_TAC THENL
       [EXPAND_TAC "x" THEN ASM_SIMP_TAC [GROUP_DIV], ALL_TAC] THEN
      ONCE_REWRITE_TAC [← TAUT (← q r"p <=> ~ ~p")] THEN DISCH_TAC THEN
      UNDISCH_TAC
       (← q r"!w. open_in top w /\ group_id G IN w
            ==> ?u:A->bool. u normal_subgroup_of G /\ open_in top u /\
                            u SUBSET w") THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"topspace top DIFF {x:A}")) THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC [OPEN_IN_TOPSPACE] THEN
          MP_TAC (← ISPEC (← q r"top:A topology") T1_SPACE_CLOSED_IN_SING) THEN
          ASM_SIMP_TAC [HAUSDORFF_IMP_T1_SPACE],
          ASM_REWRITE_TAC [IN_DIFF, IN_SING, GROUP_ID] THEN
          UNDISCH_TAC (← q r"~(x:A = group_id G)") THEN MESON_TAC []],
        DISCH_THEN (X_CHOOSE_THEN (← q r"u:A->bool") STRIP_ASSUME_TAC)] THEN
      SUBGOAL_THEN (← q r"(u:A->bool) IN k") ASSUME_TAC THENL
       [EXPAND_TAC "k" THEN ASM_REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN
      UNDISCH_TAC
       (← q r"RESTRICTION k (\u. right_coset G u (g:A)) =
        RESTRICTION k (\u. right_coset G u h)") THEN
      DISCH_THEN (MP_TAC o C AP_THM (← q r"u:A->bool")) THEN
      ASM_REWRITE_TAC [RESTRICTION] THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_IMP_SUBGROUP) THEN
      ASM_SIMP_TAC [RIGHT_COSET_EQ] THEN
      UNDISCH_TAC (← q r"(u:A->bool) SUBSET topspace top DIFF {x:A}") THEN
      SET_TAC [],
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [GROUP_ISOMORPHISM] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC [GROUP_HOMOMORPHISM, SUBSET, FORALL_IN_IMAGE] THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
        MAP_EVERY X_GEN_TAC [← q r"g:A", ← q r"h:A"] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
        X_GEN_TAC (← q r"u:A->bool") THEN REWRITE_TAC [RESTRICTION] THEN
        COND_CASES_TAC THEN REWRITE_TAC [] THEN
        MATCH_MP_TAC (← GSYM QUOTIENT_GROUP_MUL) THEN ASM_SIMP_TAC [],
        REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, SUBSET, FORALL_IN_IMAGE] THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
        REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC [],
        ASM_MESON_TAC []],
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_IMP_HOMEOMORPHIC_MAP THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC [],
      MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN
      REWRITE_TAC [HAUSDORFF_SPACE_PRODUCT_TOPOLOGY,
                   HAUSDORFF_SPACE_DISCRETE_TOPOLOGY],
      REWRITE_TAC [CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [ALL_TAC,
        ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE]] THEN
      REWRITE_TAC [CONTINUOUS_MAP_COMPONENTWISE] THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, RESTRICTION_IN_EXTENSIONAL] THEN
      X_GEN_TAC (← q r"u:A->bool") THEN DISCH_TAC THEN
      ASM_REWRITE_TAC [RESTRICTION] THEN
      UNDISCH_TAC
       (← q r"!u. u IN k ==> (u:A->bool) normal_subgroup_of G /\ open_in top u") THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"u:A->bool")) THEN ASM_REWRITE_TAC [] THEN
      STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"G:A group", ← q r"top:A topology", ← q r"u:A->bool"]
                       QUOTIENT_TOPOLOGY_OPEN_NORMAL_SUBGROUP) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      REWRITE_TAC [ETA_AX, CONTINUOUS_MAP_QUOTIENT_TOPOLOGY],
      REWRITE_TAC [TOPSPACE_SUBTOPOLOGY] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
      UNDISCH_TAC
       (← q r"group_carrier L SUBSET
        topspace(product_topology k
         (\u. discrete_topology(group_carrier(quotient_group G (u:A->bool)))))")
      THEN ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_INTER, IN_IMAGE] THEN
      ASM_MESON_TAC [],
      ASM_REWRITE_TAC [] THEN ASM_MESON_TAC []])

  pure { PROFINITE_GROUP_INVERSE_LIMIT_QUOTIENTS }

/- ------------------------------------------------------------------------- -/
/- Groups of permutations with the pointwise topology: a topological group;  -/
/- pointwise stabilizers; open subgroups.  (profinite_groups.ml 2147-2321)   -/
/- ------------------------------------------------------------------------- -/

structure PGL where
  TOPOLOGICAL_GROUP_POINTWISE_TOPOLOGY : thm
  SUBGROUP_OF_POINTWISE_STABILIZER : thm
  OPEN_IN_POINTWISE_STABILIZER : thm
  CLOSED_IN_POINTWISE_STABILIZER : thm
  NORMAL_SUBGROUP_OF_POINTWISE_STABILIZER : thm
  POINTWISE_TOPOLOGY_NEIGHBOURHOOD_STABILIZER : thm
  OPEN_IN_POINTWISE_TOPOLOGY_SUBGROUP : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPGL [HolBase] (D : ProfiniteGroupsDeps) (BPGA : PGA) : ExceptT String IO PGL := do
  -- @@SCOPE BEGIN
  let { OPEN_IN_SUBGROUP_NEIGHBOURHOOD, topological_group, .. } := BPGA
  let { ASM_MESON_TAC, MESON_TAC, .. } := D.mt
  let { CLOSED_IN_POINTWISE_TOPOLOGY_AGREE, CONTINUOUS_MAP_POINTWISE_TOPOLOGY,
        OPEN_IN_CROSS, OPEN_IN_POINTWISE_TOPOLOGY_AGREE, OPEN_IN_POINTWISE_TOPOLOGY_POINT,
        OPEN_IN_UNIONS, POINTWISE_TOPOLOGY_NEIGHBOURHOOD, TOPSPACE_POINTWISE_TOPOLOGY,
        TOPSPACE_PROD_TOPOLOGY, .. } := D.qmetric
  let { CARRIER_SUBGROUP_GENERATED_SUBGROUP, group_conjugation, IN_SUBGROUP_ID,
        IN_SUBGROUP_INV, IN_SUBGROUP_MUL, NORMAL_SUBGROUP_CONJUGATION, SUBGROUP_GENERATED,
        subgroup_of, SUBGROUP_OF_IMP_SUBSET, .. } := D.qgrouptheory
  let { SYMMETRIC_GROUP, .. } := D.qsymmetricgroup
  let { permutes, PERMUTES_INVERSE_EQ, PERMUTES_INVERSES, .. } := D.qpermutations
  let { EXTENSION, FINITE_INTER, FORALL_IN_GSPEC, FORALL_IN_IMAGE, .. } := D.mt.core1
  let { IN_CROSS, IN_ELIM_THM, IN_INTER, IN_UNIV, INTER_SUBSET, .. } := D.mt.core2
  let { o_THM, SUBSET, SUBSET_TRANS, UNIONS_GSPEC, .. } := D.mt.core4
  let { FORALL_PAIR_THM, I_THM, .. } := D.mt.core5
  -- @@SCOPE END

  let TOPOLOGICAL_GROUP_POINTWISE_TOPOLOGY ← prove
   r"!X G:(A->A)->bool.
        G subgroup_of symmetric_group X
        ==> topological_group (subgroup_generated (symmetric_group X) G)
                              (pointwise_topology G)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
    SUBGOAL_THEN (← q r"!g:A->A. g IN G ==> g permutes X") ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"(G:(A->A)->bool) SUBSET group_carrier(symmetric_group X)") THEN
      REWRITE_TAC [SYMMETRIC_GROUP, SUBSET, IN_ELIM_THM],
      ALL_TAC] THEN
    ASM_SIMP_TAC [topological_group, TOPSPACE_POINTWISE_TOPOLOGY,
                  CARRIER_SUBGROUP_GENERATED_SUBGROUP,
                  ← CONJUNCT2 SUBGROUP_GENERATED] THEN
    REWRITE_TAC [SYMMETRIC_GROUP, CONTINUOUS_MAP_POINTWISE_TOPOLOGY] THEN
    REWRITE_TAC [TOPSPACE_PROD_TOPOLOGY, TOPSPACE_POINTWISE_TOPOLOGY] THEN
    REWRITE_TAC [FORALL_PAIR_THM, IN_CROSS] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q r"f:A->A", ← q r"g:A->A"] THEN STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"symmetric_group (X:A->bool)", ← q r"G:(A->A)->bool",
                        ← q r"f:A->A", ← q r"g:A->A"] IN_SUBGROUP_MUL) THEN
      ASM_REWRITE_TAC [SYMMETRIC_GROUP],
      MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN
      SUBGOAL_THEN
       (← q r"{z | z IN (G:(A->A)->bool) CROSS G /\ (FST z o SND z) x = y} =
        UNIONS {{f | f IN G /\ f w = y} CROSS {f | f IN G /\ f x = w} |
                w IN (:A)}")
      SUBST1_TAC THENL
       [REWRITE_TAC [UNIONS_GSPEC, EXTENSION, FORALL_PAIR_THM, IN_ELIM_THM,
                     IN_CROSS, o_THM, IN_UNIV] THEN
        MESON_TAC [],
        MATCH_MP_TAC OPEN_IN_UNIONS THEN
        REWRITE_TAC [FORALL_IN_GSPEC, IN_UNIV, OPEN_IN_CROSS] THEN
        REWRITE_TAC [OPEN_IN_POINTWISE_TOPOLOGY_POINT]],
      X_GEN_TAC (← q r"f:A->A") THEN DISCH_TAC THEN
      MP_TAC (← ISPECL [← q r"symmetric_group (X:A->bool)", ← q r"G:(A->A)->bool",
                        ← q r"f:A->A"] IN_SUBGROUP_INV) THEN
      ASM_REWRITE_TAC [SYMMETRIC_GROUP],
      MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN
      SUBGOAL_THEN
       (← q r"{f:A->A | f IN G /\ inverse f x = y} = {f | f IN G /\ f y = x}")
      SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
        ASM_MESON_TAC [PERMUTES_INVERSE_EQ],
        REWRITE_TAC [OPEN_IN_POINTWISE_TOPOLOGY_POINT]]])

  let SUBGROUP_OF_POINTWISE_STABILIZER ← prove
   r"!X G (k:A->bool).
        G subgroup_of symmetric_group X
        ==> {g | g IN G /\ !x. x IN k ==> g x = x} subgroup_of
            subgroup_generated (symmetric_group X) G"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
    SUBGOAL_THEN (← q r"!g:A->A. g IN G ==> g permutes X") ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"(G:(A->A)->bool) SUBSET group_carrier(symmetric_group X)") THEN
      REWRITE_TAC [SYMMETRIC_GROUP, SUBSET, IN_ELIM_THM],
      ALL_TAC] THEN
    ASM_SIMP_TAC [subgroup_of, CARRIER_SUBGROUP_GENERATED_SUBGROUP,
                  ← CONJUNCT2 SUBGROUP_GENERATED] THEN
    REWRITE_TAC [SYMMETRIC_GROUP, SUBSET, IN_ELIM_THM, I_THM, o_THM] THEN
    REPEAT CONJ_TAC THENL
     [SIMP_TAC [],
      MP_TAC (← ISPECL [← q r"symmetric_group (X:A->bool)", ← q r"G:(A->A)->bool"]
                       IN_SUBGROUP_ID) THEN
      ASM_REWRITE_TAC [SYMMETRIC_GROUP],
      X_GEN_TAC (← q r"f:A->A") THEN STRIP_TAC THEN CONJ_TAC THENL
       [MP_TAC (← ISPECL [← q r"symmetric_group (X:A->bool)", ← q r"G:(A->A)->bool",
                          ← q r"f:A->A"] IN_SUBGROUP_INV) THEN
        ASM_REWRITE_TAC [SYMMETRIC_GROUP],
        ASM_MESON_TAC [PERMUTES_INVERSE_EQ]],
      MAP_EVERY X_GEN_TAC [← q r"f:A->A", ← q r"g:A->A"] THEN STRIP_TAC THEN
      ASM_SIMP_TAC [] THEN
      MP_TAC (← ISPECL [← q r"symmetric_group (X:A->bool)", ← q r"G:(A->A)->bool",
                        ← q r"f:A->A", ← q r"g:A->A"] IN_SUBGROUP_MUL) THEN
      ASM_REWRITE_TAC [SYMMETRIC_GROUP]])

  let OPEN_IN_POINTWISE_STABILIZER ← prove
   r"!G (k:A->bool).
        FINITE k
        ==> open_in (pointwise_topology G)
                    {g | g IN G /\ !x. x IN k ==> g x = x}"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"G:(A->A)->bool", ← q r"k:A->bool", ← q r"I:A->A"]
                     OPEN_IN_POINTWISE_TOPOLOGY_AGREE) THEN
    ASM_REWRITE_TAC [I_THM])

  let CLOSED_IN_POINTWISE_STABILIZER ← prove
   r"!G (k:A->bool).
        closed_in (pointwise_topology G)
                  {g | g IN G /\ !x. x IN k ==> g x = x}"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"G:(A->A)->bool", ← q r"k:A->bool", ← q r"I:A->A"]
                     CLOSED_IN_POINTWISE_TOPOLOGY_AGREE) THEN
    REWRITE_TAC [I_THM])

  let NORMAL_SUBGROUP_OF_POINTWISE_STABILIZER ← prove
   r"!X G (k:A->bool).
        G subgroup_of symmetric_group X /\
        (!g x. g IN G /\ x IN k ==> g x IN k)
        ==> {g | g IN G /\ !x. x IN k ==> g x = x} normal_subgroup_of
            subgroup_generated (symmetric_group X) G"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
    SUBGOAL_THEN (← q r"!g:A->A. g IN G ==> g permutes X") ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"(G:(A->A)->bool) SUBSET group_carrier(symmetric_group X)") THEN
      REWRITE_TAC [SYMMETRIC_GROUP, SUBSET, IN_ELIM_THM],
      ALL_TAC] THEN
    ASM_SIMP_TAC [NORMAL_SUBGROUP_CONJUGATION,
                  SUBGROUP_OF_POINTWISE_STABILIZER] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, group_conjugation] THEN
    ASM_SIMP_TAC [CARRIER_SUBGROUP_GENERATED_SUBGROUP,
                  ← CONJUNCT2 SUBGROUP_GENERATED] THEN
    REWRITE_TAC [SYMMETRIC_GROUP, IN_ELIM_THM, o_THM] THEN
    X_GEN_TAC (← q r"a:A->A") THEN DISCH_TAC THEN X_GEN_TAC (← q r"h:A->A") THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"inverse (a:A->A) IN G") ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"symmetric_group (X:A->bool)", ← q r"G:(A->A)->bool",
                        ← q r"a:A->A"] IN_SUBGROUP_INV) THEN
      ASM_REWRITE_TAC [SYMMETRIC_GROUP],
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC (← ISPECL [← q r"symmetric_group (X:A->bool)", ← q r"G:(A->A)->bool"]
                       IN_SUBGROUP_MUL) THEN
      ASM_REWRITE_TAC [SYMMETRIC_GROUP] THEN
      DISCH_THEN (fun th => ASM_MESON_TAC [th]),
      X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"(h:A->A)(inverse a x) = inverse (a:A->A) x") SUBST1_TAC THENL
       [ASM_MESON_TAC [], ASM_MESON_TAC [PERMUTES_INVERSES]]])

  let POINTWISE_TOPOLOGY_NEIGHBOURHOOD_STABILIZER ← prove
   r"!X G w:(A->A)->bool.
        G subgroup_of symmetric_group X /\
        open_in (pointwise_topology G) w /\ I IN w
        ==> ?k. FINITE k /\ k SUBSET X /\
                {g | g IN G /\ !x. x IN k ==> g x = x} SUBSET w"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
    SUBGOAL_THEN (← q r"!g:A->A. g IN G ==> g permutes X") ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"(G:(A->A)->bool) SUBSET group_carrier(symmetric_group X)") THEN
      REWRITE_TAC [SYMMETRIC_GROUP, SUBSET, IN_ELIM_THM],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"G:(A->A)->bool", ← q r"w:(A->A)->bool", ← q r"I:A->A"]
                     POINTWISE_TOPOLOGY_NEIGHBOURHOOD) THEN
    ASM_REWRITE_TAC [I_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"k:A->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"k INTER (X:A->bool)") THEN
    ASM_SIMP_TAC [FINITE_INTER, INTER_SUBSET] THEN
    TRANS_TAC SUBSET_TRANS (← q r"{g | g IN G /\ !x:A. x IN k ==> g x = x}") THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_INTER] THEN
    X_GEN_TAC (← q r"g:A->A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"(x:A) IN X") THEN
    ASM_SIMP_TAC [] THEN ASM_MESON_TAC [permutes])

  let OPEN_IN_POINTWISE_TOPOLOGY_SUBGROUP ← prove
   r"!X G h:(A->A)->bool.
        G subgroup_of symmetric_group X /\
        h subgroup_of subgroup_generated (symmetric_group X) G
        ==> (open_in (pointwise_topology G) h <=>
             ?k. FINITE k /\ k SUBSET X /\
                 {g | g IN G /\ !x. x IN k ==> g x = x} SUBSET h)"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC POINTWISE_TOPOLOGY_NEIGHBOURHOOD_STABILIZER THEN
      ASM_REWRITE_TAC [] THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP IN_SUBGROUP_ID) THEN
      REWRITE_TAC [← CONJUNCT2 SUBGROUP_GENERATED, SYMMETRIC_GROUP],
      DISCH_THEN (X_CHOOSE_THEN (← q r"k:A->bool") STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC OPEN_IN_SUBGROUP_NEIGHBOURHOOD THEN
      MAP_EVERY EXISTS_TAC
       [← q r"subgroup_generated (symmetric_group X) (G:(A->A)->bool)",
        ← q r"{g | g IN G /\ !x:A. x IN k ==> g x = x}"] THEN
      ASM_SIMP_TAC [TOPOLOGICAL_GROUP_POINTWISE_TOPOLOGY,
                    OPEN_IN_POINTWISE_STABILIZER] THEN
      REWRITE_TAC [← CONJUNCT2 SUBGROUP_GENERATED, SYMMETRIC_GROUP] THEN
      REWRITE_TAC [IN_ELIM_THM, I_THM] THEN
      MP_TAC (← ISPECL [← q r"symmetric_group (X:A->bool)", ← q r"G:(A->A)->bool"]
                       IN_SUBGROUP_ID) THEN
      ASM_REWRITE_TAC [SYMMETRIC_GROUP]])

  pure { TOPOLOGICAL_GROUP_POINTWISE_TOPOLOGY, SUBGROUP_OF_POINTWISE_STABILIZER,
         OPEN_IN_POINTWISE_STABILIZER, CLOSED_IN_POINTWISE_STABILIZER,
         NORMAL_SUBGROUP_OF_POINTWISE_STABILIZER,
         POINTWISE_TOPOLOGY_NEIGHBOURHOOD_STABILIZER, OPEN_IN_POINTWISE_TOPOLOGY_SUBGROUP }

/- ------------------------------------------------------------------------- -/
/- The pointwise topology as a subspace of a product of discrete spaces;     -/
/- pointwise limits of permutations; profinite permutation groups.           -/
/- (profinite_groups.ml 2323-2525)                                           -/
/- ------------------------------------------------------------------------- -/

structure PGM where
  HOMEOMORPHIC_MAP_POINTWISE_RESTRICTION : thm
  PERMUTES_POINTWISE_LIMIT : thm
  PROFINITE_GROUP_POINTWISE_TOPOLOGY : thm
  PROFINITE_GROUP_POINTWISE_TOPOLOGY_LOCAL : thm
  POINTWISE_TOPOLOGY_FINITE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupPGM [HolBase] (D : ProfiniteGroupsDeps) (BPGH : PGH) (BPGL : PGL) : ExceptT String IO PGM := do
  -- @@SCOPE BEGIN
  let { PROFINITE_GROUP_OPEN_SUBGROUPS, .. } := BPGH
  let { OPEN_IN_POINTWISE_STABILIZER, POINTWISE_TOPOLOGY_NEIGHBOURHOOD_STABILIZER,
        SUBGROUP_OF_POINTWISE_STABILIZER, TOPOLOGICAL_GROUP_POINTWISE_TOPOLOGY, .. } := BPGL
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, .. } := D.mt
  let { CLOSED_COMPACT_IN, CLOSED_IN_POINTWISE_PRODUCT, COMPACT_IN_CARTESIAN_PRODUCT,
        COMPACT_IN_DISCRETE_TOPOLOGY, COMPACT_SPACE_SUBTOPOLOGY,
        CONTINUOUS_MAP_COMPONENTWISE, CONTINUOUS_MAP_IN_SUBTOPOLOGY,
        CONTINUOUS_MAP_INTO_DISCRETE_TOPOLOGY_FIBRES, CONTINUOUS_MAP_POINTWISE_TOPOLOGY,
        CONTINUOUS_MAP_PRODUCT_PROJECTION, FINITE_T1_SPACE_IMP_DISCRETE_TOPOLOGY,
        HAUSDORFF_IMP_T1_SPACE, HAUSDORFF_SPACE_POINTWISE_TOPOLOGY, HOMEOMORPHIC_MAP_MAPS,
        homeomorphic_maps, OPEN_IN_CONTINUOUS_MAP_PREIMAGE, OPEN_IN_DISCRETE_TOPOLOGY,
        OPEN_IN_EMPTY, OPEN_IN_POINTWISE_TOPOLOGY_POINT, OPEN_IN_SUBTOPOLOGY,
        OPEN_IN_SUBTOPOLOGY_REFL, pointwise_topology, TOPSPACE_DISCRETE_TOPOLOGY,
        TOPSPACE_POINTWISE_TOPOLOGY, TOPSPACE_PRODUCT_TOPOLOGY, TOPSPACE_SUBTOPOLOGY,
        .. } := D.qmetric
  let { IN_SUBGROUP_ID, IN_SUBGROUP_MUL, SUBGROUP_GENERATED, SUBGROUP_OF_IMP_SUBSET,
        .. } := D.qgrouptheory
  let { SYMMETRIC_GROUP, .. } := D.qsymmetricgroup
  let { permutes, PERMUTES_IN_IMAGE, PERMUTES_INJECTIVE, .. } := D.qpermutations
  let { SURJECTIVE_IFF_INJECTIVE, .. } := D.qsession
  let { EMPTY_GSPEC, EXTENSION, EXTENSIONAL_UNIV, FINITE_EMPTY, FINITE_INSERT, FINITE_SING,
        FINITE_SUBSET, FORALL_IN_GSPEC, FORALL_IN_IMAGE, FORALL_IN_INSERT, FUN_EQ_THM,
        FUN_IN_IMAGE, .. } := D.mt.core1
  let { IN, IN_CARTESIAN_PRODUCT, IN_ELIM_THM, IN_IMAGE, IN_SING, IN_UNIV, NOT_IN_EMPTY,
        .. } := D.mt.core2
  let { o_DEF, o_THM, RESTRICTION, RESTRICTION_IN_EXTENSIONAL, SING_SUBSET, SUBSET,
        SUBSET_UNIV, .. } := D.mt.core4
  let { EXISTS_UNIQUE_THM, FORALL_UNWIND_THM2, I_THM, .. } := D.mt.core5
  -- @@SCOPE END

  let HOMEOMORPHIC_MAP_POINTWISE_RESTRICTION ← prove
   r"!X G:(A->A)->bool.
        G subgroup_of symmetric_group X
        ==> homeomorphic_map
             (pointwise_topology G,
              subtopology (product_topology X (\x. discrete_topology X))
                          (IMAGE (RESTRICTION X) G))
             (RESTRICTION X)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
    SUBGOAL_THEN (← q r"!g:A->A. g IN G ==> g permutes X") ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"(G:(A->A)->bool) SUBSET group_carrier(symmetric_group X)") THEN
      REWRITE_TAC [SYMMETRIC_GROUP, SUBSET, IN_ELIM_THM],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!g:A->A. g IN G ==> (\x. if x IN X then RESTRICTION X g x else x) = g")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM, RESTRICTION] THEN
      ASM_MESON_TAC [permutes],
      ALL_TAC] THEN
    ABBREV_TAC (← q r"P = product_topology X (\x:A. discrete_topology X)") THEN
    SUBGOAL_THEN
     (← q r"IMAGE (RESTRICTION X) (G:(A->A)->bool) SUBSET topspace P")
    ASSUME_TAC THENL
     [EXPAND_TAC "P" THEN
      REWRITE_TAC [TOPSPACE_PRODUCT_TOPOLOGY, o_DEF, TOPSPACE_DISCRETE_TOPOLOGY]
      THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_CARTESIAN_PRODUCT] THEN
      REWRITE_TAC [← REWRITE_RULE [IN] RESTRICTION_IN_EXTENSIONAL, RESTRICTION] THEN
      ASM_MESON_TAC [PERMUTES_IN_IMAGE],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"topspace(subtopology P (IMAGE (RESTRICTION X) G)) =
      IMAGE (RESTRICTION X) (G:(A->A)->bool)")
    ASSUME_TAC THENL
     [REWRITE_TAC [TOPSPACE_SUBTOPOLOGY] THEN
      UNDISCH_TAC (← q r"IMAGE (RESTRICTION X) (G:(A->A)->bool) SUBSET topspace P") THEN
      SET_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [HOMEOMORPHIC_MAP_MAPS] THEN
    EXISTS_TAC (← q r"\f:A->A x. if x IN X then f x else x") THEN
    ASM_REWRITE_TAC [homeomorphic_maps, TOPSPACE_POINTWISE_TOPOLOGY] THEN
    ASM_SIMP_TAC [FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [REWRITE_TAC [CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, TOPSPACE_POINTWISE_TOPOLOGY] THEN
      SIMP_TAC [FUN_IN_IMAGE] THEN EXPAND_TAC "P" THEN
      REWRITE_TAC [CONTINUOUS_MAP_COMPONENTWISE] THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, RESTRICTION_IN_EXTENSIONAL] THEN
      X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN
      REWRITE_TAC [CONTINUOUS_MAP_INTO_DISCRETE_TOPOLOGY_FIBRES] THEN
      ASM_REWRITE_TAC [TOPSPACE_POINTWISE_TOPOLOGY, RESTRICTION] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC [PERMUTES_IN_IMAGE],
        REWRITE_TAC [OPEN_IN_POINTWISE_TOPOLOGY_POINT]],
      ALL_TAC] THEN
    REWRITE_TAC [CONTINUOUS_MAP_POINTWISE_TOPOLOGY] THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [FORALL_IN_IMAGE] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN
    ASM_CASES_TAC (← q r"(x:A) IN X") THEN ASM_REWRITE_TAC [] THENL
     [ASM_CASES_TAC (← q r"(y:A) IN X") THENL
       [REWRITE_TAC [OPEN_IN_SUBTOPOLOGY] THEN
        EXISTS_TAC (← q r"{f | f IN topspace P /\ (\f:A->A. f x) f IN {y:A}}") THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
          EXISTS_TAC (← q r"discrete_topology (X:A->bool)") THEN
          ASM_REWRITE_TAC [OPEN_IN_DISCRETE_TOPOLOGY, SING_SUBSET] THEN
          EXPAND_TAC "P" THEN
          MP_TAC (← ISPECL [← q r"\x:A. discrete_topology (X:A->bool)", ← q r"X:A->bool",
                            ← q r"x:A"] CONTINUOUS_MAP_PRODUCT_PROJECTION) THEN
          ASM_REWRITE_TAC [],
          UNDISCH_TAC
           (← q r"IMAGE (RESTRICTION X) (G:(A->A)->bool) SUBSET topspace P") THEN
          REWRITE_TAC [IN_SING] THEN SET_TAC []],
        SUBGOAL_THEN
         (← q r"{z | z IN IMAGE (RESTRICTION X) (G:(A->A)->bool) /\ z x = (y:A)} =
          {}")
        SUBST1_TAC THENL
         [REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY, IN_IMAGE] THEN
          X_GEN_TAC (← q r"z:A->A") THEN
          DISCH_THEN (CONJUNCTS_THEN2
           (X_CHOOSE_THEN (← q r"g:A->A") STRIP_ASSUME_TAC) MP_TAC) THEN
          ASM_REWRITE_TAC [RESTRICTION] THEN ASM_MESON_TAC [PERMUTES_IN_IMAGE],
          REWRITE_TAC [OPEN_IN_EMPTY]]],
      ASM_CASES_TAC (← q r"x:A = y") THEN
      ASM_REWRITE_TAC [EMPTY_GSPEC, OPEN_IN_EMPTY] THEN
      ASM_REWRITE_TAC [← SET_RULE (← q r"{x:A->A | x IN s} = s"),
                       OPEN_IN_SUBTOPOLOGY_REFL]])

  let PERMUTES_POINTWISE_LIMIT ← prove
   r"!X G f:A->A.
        G subgroup_of symmetric_group X /\
        (!x. x IN X ==> FINITE {g x | g IN G}) /\
        (!k. FINITE k ==> ?g. g IN G /\ !x. x IN k ==> g x = f x)
        ==> f permutes X"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
    SUBGOAL_THEN (← q r"!g:A->A. g IN G ==> g permutes X") ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"(G:(A->A)->bool) SUBSET group_carrier(symmetric_group X)") THEN
      REWRITE_TAC [SYMMETRIC_GROUP, SUBSET, IN_ELIM_THM],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x:A. ?g. g IN G /\ g x = (f:A->A) x") ASSUME_TAC THENL
     [X_GEN_TAC (← q r"x:A") THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"{x:A}")) THEN
      REWRITE_TAC [FINITE_SING, IN_SING, FORALL_UNWIND_THM2],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x y:A. (f:A->A) x = f y ==> x = y") ASSUME_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"{x:A,y}") o check (fun th =>
        HolCore.Lib.can (HolCore.Basics.find_term (fun t => HolCore.Kernel.is_const t &&
          (match HolCore.Kernel.dest_const t with
           | .ok (n, _) => n == "FINITE" | .error _ => false)))
            (concl th))) THEN
      REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY, FORALL_IN_INSERT] THEN
      REWRITE_TAC [NOT_IN_EMPTY] THEN
      ASM_MESON_TAC [PERMUTES_INJECTIVE],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x:A. ~(x IN X) ==> (f:A->A) x = x") ASSUME_TAC THENL
     [ASM_MESON_TAC [permutes], ALL_TAC] THEN
    REWRITE_TAC [permutes] THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"y:A") THEN REWRITE_TAC [EXISTS_UNIQUE_THM] THEN
    CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
    ASM_CASES_TAC (← q r"(y:A) IN X") THENL [ALL_TAC, ASM_MESON_TAC []] THEN
    ABBREV_TAC (← q r"orb = {g y | g IN (G:(A->A)->bool)}") THEN
    SUBGOAL_THEN (← q r"FINITE(orb:A->bool) /\ (y:A) IN orb") STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "orb" THEN ASM_SIMP_TAC [IN_ELIM_THM] THEN
      EXISTS_TAC (← q r"I:A->A") THEN REWRITE_TAC [I_THM] THEN
      MP_TAC (← ISPECL [← q r"symmetric_group (X:A->bool)", ← q r"G:(A->A)->bool"]
                       IN_SUBGROUP_ID) THEN
      ASM_REWRITE_TAC [SYMMETRIC_GROUP],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"IMAGE (f:A->A) orb SUBSET orb") ASSUME_TAC THENL
     [EXPAND_TAC "orb" THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
      REWRITE_TAC [FORALL_IN_GSPEC, IN_ELIM_THM] THEN
      X_GEN_TAC (← q r"g:A->A") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"h:A->A") STRIP_ASSUME_TAC o
        SPEC (← q r"(g:A->A) y") o check (fun th =>
          HolCore.Basics.is_forall (concl th) &&
          (match HolCore.Basics.dest_forall (concl th) with
           | .ok (_, b) => HolCore.Basics.is_exists b | .error _ => false))) THEN
      EXISTS_TAC (← q r"(h:A->A) o (g:A->A)") THEN ASM_REWRITE_TAC [o_THM] THEN
      MP_TAC (← ISPECL [← q r"symmetric_group (X:A->bool)", ← q r"G:(A->A)->bool",
                        ← q r"h:A->A", ← q r"g:A->A"] IN_SUBGROUP_MUL) THEN
      ASM_REWRITE_TAC [SYMMETRIC_GROUP],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"orb:A->bool", ← q r"f:A->A"] SURJECTIVE_IFF_INJECTIVE) THEN
    ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [])

  let PROFINITE_GROUP_POINTWISE_TOPOLOGY ← prove
   r"!X G:(A->A)->bool.
        G subgroup_of symmetric_group X /\
        (!x. x IN X ==> FINITE {g x | g IN G}) /\
        closed_in (product_topology (:A) (\x. discrete_topology (:A))) G
        ==> profinite_group (subgroup_generated (symmetric_group X) G)
                            (pointwise_topology G)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
    SUBGOAL_THEN (← q r"!g:A->A. g IN G ==> g permutes X") ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"(G:(A->A)->bool) SUBSET group_carrier(symmetric_group X)") THEN
      REWRITE_TAC [SYMMETRIC_GROUP, SUBSET, IN_ELIM_THM],
      ALL_TAC] THEN
    REWRITE_TAC [PROFINITE_GROUP_OPEN_SUBGROUPS] THEN
    ASM_SIMP_TAC [TOPOLOGICAL_GROUP_POINTWISE_TOPOLOGY,
                  HAUSDORFF_SPACE_POINTWISE_TOPOLOGY] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [pointwise_topology] THEN
      MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
      MATCH_MP_TAC CLOSED_COMPACT_IN THEN
      EXISTS_TAC (← q r"cartesian_product (:A) (\x. {g x | g IN (G:(A->A)->bool)})") THEN
      ASM_REWRITE_TAC [COMPACT_IN_CARTESIAN_PRODUCT] THEN CONJ_TAC THENL
       [DISJ2_TAC THEN
        REWRITE_TAC [COMPACT_IN_DISCRETE_TOPOLOGY, SUBSET_UNIV, IN_UNIV] THEN
        X_GEN_TAC (← q r"x:A") THEN ASM_CASES_TAC (← q r"(x:A) IN X") THEN ASM_SIMP_TAC [] THEN
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{x:A}") THEN
        REWRITE_TAC [FINITE_SING, SUBSET, FORALL_IN_GSPEC, IN_SING] THEN
        ASM_MESON_TAC [permutes],
        REWRITE_TAC [SUBSET, IN_CARTESIAN_PRODUCT, EXTENSIONAL_UNIV, IN_UNIV] THEN
        REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC []],
      ALL_TAC] THEN
    ASM_SIMP_TAC [← CONJUNCT2 SUBGROUP_GENERATED, SYMMETRIC_GROUP] THEN
    X_GEN_TAC (← q r"w:(A->A)->bool") THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"X:A->bool", ← q r"G:(A->A)->bool", ← q r"w:(A->A)->bool"]
                     POINTWISE_TOPOLOGY_NEIGHBOURHOOD_STABILIZER) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"k:A->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"{g | g IN G /\ !x:A. x IN k ==> g x = x}") THEN
    ASM_SIMP_TAC [SUBGROUP_OF_POINTWISE_STABILIZER,
                  OPEN_IN_POINTWISE_STABILIZER])

  let PROFINITE_GROUP_POINTWISE_TOPOLOGY_LOCAL ← prove
   r"!X G:(A->A)->bool.
        G subgroup_of symmetric_group X /\
        (!x. x IN X ==> FINITE {g x | g IN G}) /\
        (!f. f permutes X /\
             (!k. FINITE k ==> ?g. g IN G /\ !x. x IN k ==> g x = f x)
             ==> f IN G)
        ==> profinite_group (subgroup_generated (symmetric_group X) G)
                            (pointwise_topology G)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC PROFINITE_GROUP_POINTWISE_TOPOLOGY THEN
    ASM_REWRITE_TAC [CLOSED_IN_POINTWISE_PRODUCT] THEN
    X_GEN_TAC (← q r"f:A->A") THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC PERMUTES_POINTWISE_LIMIT THEN
    EXISTS_TAC (← q r"G:(A->A)->bool") THEN ASM_REWRITE_TAC [])

  let POINTWISE_TOPOLOGY_FINITE ← prove
   r"!s:(A->B)->bool. FINITE s ==> pointwise_topology s = discrete_topology s"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_T1_SPACE_IMP_DISCRETE_TOPOLOGY THEN
    ASM_SIMP_TAC [TOPSPACE_POINTWISE_TOPOLOGY, HAUSDORFF_IMP_T1_SPACE,
                  HAUSDORFF_SPACE_POINTWISE_TOPOLOGY])

  pure { HOMEOMORPHIC_MAP_POINTWISE_RESTRICTION, PERMUTES_POINTWISE_LIMIT,
         PROFINITE_GROUP_POINTWISE_TOPOLOGY, PROFINITE_GROUP_POINTWISE_TOPOLOGY_LOCAL,
         POINTWISE_TOPOLOGY_FINITE }
end HolMultiLib.ProfiniteGroups
