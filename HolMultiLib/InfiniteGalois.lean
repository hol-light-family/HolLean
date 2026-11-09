/- ========================================================================= -/
/- Infinite Galois theory.                                                   -/
/- ========================================================================= -/
/- File: HolMultiLib/InfiniteGalois.lean

  Original (c) Copyright, John Harrison 1998-2008 (see infinite_galois.ml).
  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/infinite_galois.ml`, in the style of
  HolMultiLib/Measure.lean: pure, the proofs translated by hand, one `let`
  per OCaml `let`, in file order.  The load-time effects are at their file
  positions.  What infinite_galois.ml uses from earlier files is passed in `InfiniteGaloisDeps`.
  SessionMultiLib/InfiniteGalois.lean supplies it.
-/

import HolMultiLib.ProfiniteGroups

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolMultiLib.InfiniteGalois

/- The theorems infinite_galois.ml uses that the deps chain does not carry, grouped by the
   file that proves them. -/

structure QProfiniteGroupsThms where
  (CLOSED_IN_POINTWISE_STABILIZER OPEN_IN_POINTWISE_TOPOLOGY_SUBGROUP
   POINTWISE_TOPOLOGY_FINITE POINTWISE_TOPOLOGY_NEIGHBOURHOOD_STABILIZER
   profinite_group PROFINITE_GROUP_CONTINUOUS_EPIMORPHISM
   PROFINITE_GROUP_POINTWISE_TOPOLOGY_LOCAL TOPOLOGICAL_GROUP_POINTWISE_TOPOLOGY : thm)
  deriving Inhabited

structure QGaloisThms where
  (FINITE_GALOIS_GROUP FINITE_GALOIS_SUBFIELDS_ELEMENT FINITE_GALOIS_SUBFIELDS_FINITE
   FINITE_GALOIS_SUBFIELDS_UPPER_BOUND FINITE_GALOIS_SUBFIELDS_UPPER_BOUNDS
   FIXED_FIELD_ANTIMONO FIXED_FIELD_GALOIS_GROUP_INTERMEDIATE
   FIXED_FIELD_GALOIS_SUBSET FIXED_FIELD_SUBGROUP_GENERATED FIXED_FIELD_UNION
   GALOIS_CORRESPONDENCE_INDEX GALOIS_CORRESPONDENCE_NORMAL
   GALOIS_EXTENSION_FIXED_FIELD_FINITE_ORBITS GALOIS_EXTENSION_NORMAL_SUBGROUP
   GALOIS_GROUP_COMPOSITUM GALOIS_GROUP_EQ_IMAGE GALOIS_GROUP_FIXED_FIELD
   GALOIS_GROUP_FIXES GALOIS_GROUP_I GALOIS_GROUP_INTERMEDIATE_SUBGROUP
   GALOIS_GROUP_LOCAL GALOIS_GROUP_ORBIT_FINITE GALOIS_GROUP_PERMUTES
   GALOIS_GROUP_RESTRICTION GALOIS_GROUP_RESTRICTION_HOMOMORPHISM
   GALOIS_GROUP_RESTRICTION_NORMAL GALOIS_GROUP_RING_AUTOMORPHISM
   GALOIS_GROUP_RING_HOMOMORPHISM GALOIS_GROUP_SUBGROUP
   GALOIS_IMP_ALGEBRAIC_EXTENSION GALOIS_IMP_FIELD_EXTENSION
   GALOIS_IMP_NORMAL_EXTENSION IN_FINITE_GALOIS_SUBFIELDS IN_FIXED_FIELD
   IN_GALOIS_GROUP IN_GALOIS_GROUP_INTERMEDIATE SUBFIELD_OF_FIXED_FIELD
   SUBGROUP_GENERATED_GALOIS_GROUP SUBGROUP_OF_GALOIS_GROUP
   SUBSET_GALOIS_GROUP_FIXED_FIELD : thm)
  deriving Inhabited

structure QFieldTheoryThms where
  (algebraic_extension ALGEBRAIC_IMP_FIELD_EXTENSION
   CARRIER_SUBFIELD_GENERATED_SUBFIELD CARRIER_SUBFIELD_OF field_extension
   FIELD_SUBFIELD_GENERATED FINITE_EXTENSION_SUBFIELD_GENERATED
   FINITE_EXTENSION_SUBFIELD_GENERATORS FINITE_FINITE_FIELD_EXTENSION
   NORMAL_IMP_ALGEBRAIC_EXTENSION RING_CARRIER_SUBFIELD_GENERATED_SUBSET
   RING_ENDOMORPHISM_POW_CARD RING_POW_FIXPOINTS_BOUND RING_POW_SUBFIELD_GENERATED
   SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED SUBFIELD_GENERATED_IDEMPOT_GEN
   SUBFIELD_GENERATED_MINIMAL SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC
   SUBFIELD_GENERATED_SUBFIELD_GENERATED SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET
   SUBFIELD_OF_IMP_SUBSET SUBFIELD_OF_MONOMORPHIC_IMAGE
   SUBFIELD_OF_SUBFIELD_GENERATED SUBFIELD_SUBFIELD_GENERATED : thm)
  deriving Inhabited

structure QMetricThms where
  (CLOSED_IN_DISCRETE_TOPOLOGY CLOSURE_OF_EQ CLOSURE_OF_POINTWISE_TOPOLOGY : thm)
  deriving Inhabited

structure QGroupTheoryThms where
  (CARD_EQ_GROUP_COSETS_PREIMAGE FINITE_GROUP_COSETS NORMAL_SUBGROUP_GROUP_KERNEL
   SUBGROUP_OF_HOMOMORPHIC_IMAGE SUBGROUP_SUBGROUP_GENERATED : thm)
  deriving Inhabited

structure QRingTheoryThms where
  (FIELD_HOMOMORPHISM_IMP_MONOMORPHISM FIELD_IMP_INTEGRAL_DOMAIN FIELD_NONTRIVIAL
   FINITE_FIELD_CARD_GE_2 RING_1 ring_automorphism ring_endomorphism
   ring_homomorphism RING_HOMOMORPHISM_EQ RING_HOMOMORPHISM_IN_CARRIER
   RING_ISOMORPHISM ring_monomorphism RING_MONOMORPHISM_IMP_HOMOMORPHISM
   RING_MONOMORPHISM_INJECTIVE_EQ RING_POW RING_POW_ONE : thm)
  deriving Inhabited

structure QCardThms where
  (CARD_EQ_CARD_IMP : thm)
  deriving Inhabited

structure QPermutationsThms where
  (PERMUTES_ALT : thm)
  deriving Inhabited

structure QSessionThms where
  (CARD_IMAGE_INJ CARD_SUBSET CARD_SUBSET_EQ EXP_1 IMAGE_I LE_ANTISYM : thm)
  deriving Inhabited

structure InfiniteGaloisDeps where
  pg : HolMultiLib.ProfiniteGroups.ProfiniteGroupsDeps
  -- theorems
  qprofinitegroups : QProfiniteGroupsThms
  qgalois : QGaloisThms
  qfieldtheory : QFieldTheoryThms
  qmetric : QMetricThms
  qgrouptheory : QGroupTheoryThms
  qringtheory : QRingTheoryThms
  qcard : QCardThms
  qpermutations : QPermutationsThms
  qsession : QSessionThms


/- ------------------------------------------------------------------------- -/
/- The Krull topology; closures of subgroups and Artin's theorem for groups  -/
/- with finite orbits; the infinite Galois correspondence.                   -/
/- (infinite_galois.ml 96-413)                                               -/
/- ------------------------------------------------------------------------- -/

structure IGA where
  TOPOLOGICAL_GROUP_GALOIS_GROUP : thm
  PROFINITE_GROUP_GALOIS_GROUP : thm
  OPEN_IN_GALOIS_GROUP_SUBGROUP : thm
  CLOSED_IN_GALOIS_GROUP_INTERMEDIATE : thm
  POINTWISE_TOPOLOGY_GALOIS_GROUP_FINITE : thm
  GALOIS_GROUP_NEIGHBOURHOOD_BASE : thm
  CLOSURE_OF_GALOIS_GROUP_SUBGROUP_GALOIS : thm
  ARTIN_FIXED_FIELD_FINITE_ORBITS : thm
  CLOSURE_OF_GALOIS_GROUP_SUBGROUP : thm
  CLOSED_IN_GALOIS_GROUP_SUBGROUP : thm
  INFINITE_GALOIS_CORRESPONDENCE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIGA [HolBase] (D : InfiniteGaloisDeps) : ExceptT String IO IGA := do
  -- @@SCOPE BEGIN
  let { CLOSED_IN_POINTWISE_STABILIZER, OPEN_IN_POINTWISE_TOPOLOGY_SUBGROUP,
        POINTWISE_TOPOLOGY_FINITE, POINTWISE_TOPOLOGY_NEIGHBOURHOOD_STABILIZER,
        PROFINITE_GROUP_POINTWISE_TOPOLOGY_LOCAL, TOPOLOGICAL_GROUP_POINTWISE_TOPOLOGY,
        .. } := D.qprofinitegroups
  let { FINITE_GALOIS_GROUP, FINITE_GALOIS_SUBFIELDS_FINITE,
        FIXED_FIELD_GALOIS_GROUP_INTERMEDIATE, FIXED_FIELD_GALOIS_SUBSET,
        GALOIS_EXTENSION_FIXED_FIELD_FINITE_ORBITS, GALOIS_GROUP_FIXED_FIELD,
        GALOIS_GROUP_INTERMEDIATE_SUBGROUP, GALOIS_GROUP_LOCAL, GALOIS_GROUP_ORBIT_FINITE,
        GALOIS_GROUP_PERMUTES, GALOIS_GROUP_RESTRICTION_HOMOMORPHISM,
        GALOIS_GROUP_RING_AUTOMORPHISM, GALOIS_GROUP_SUBGROUP,
        GALOIS_IMP_ALGEBRAIC_EXTENSION, GALOIS_IMP_FIELD_EXTENSION,
        GALOIS_IMP_NORMAL_EXTENSION, IN_FINITE_GALOIS_SUBFIELDS, IN_FIXED_FIELD,
        IN_GALOIS_GROUP_INTERMEDIATE, SUBGROUP_GENERATED_GALOIS_GROUP,
        SUBGROUP_OF_GALOIS_GROUP, SUBSET_GALOIS_GROUP_FIXED_FIELD, .. } := D.qgalois
  let { ALGEBRAIC_IMP_FIELD_EXTENSION, CARRIER_SUBFIELD_GENERATED_SUBFIELD,
        field_extension, SUBFIELD_OF_IMP_SUBSET, .. } := D.qfieldtheory
  let { CLOSURE_OF_EQ, CLOSURE_OF_POINTWISE_TOPOLOGY, .. } := D.qmetric
  let { SUBGROUP_OF_HOMOMORPHIC_IMAGE, .. } := D.qgrouptheory
  let { ASM_MESON_TAC, MESON_TAC, SET_TAC, .. } := D.pg.mt
  let { group_homomorphism, subgroup_of, SUBGROUP_OF_IMP_SUBSET, .. } := D.pg.qgrouptheory
  let { SYMMETRIC_GROUP, .. } := D.pg.qsymmetricgroup
  let { permutes, .. } := D.pg.qpermutations
  let { EXTENSION, FINITE_INTER, FINITE_SING, FINITE_SUBSET, FORALL_IN_IMAGE,
        .. } := D.pg.mt.core1
  let { IN_ELIM_THM, IN_IMAGE, IN_SING, INTER_SUBSET, MONO_EXISTS, .. } := D.pg.mt.core2
  let { SUBSET, SUBSET_TRANS, .. } := D.pg.mt.core4
  let { FORALL_UNWIND_THM2, .. } := D.pg.mt.core5
  -- @@SCOPE END

  let TOPOLOGICAL_GROUP_GALOIS_GROUP ← prove
   r"!(h:A->B) k l.
        topological_group (galois_group(k,l) h)
         (pointwise_topology(group_carrier(galois_group(k,l) h)))"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"ring_carrier(l:B ring)",
                      ← q r"group_carrier(galois_group(k,l) (h:A->B))"]
                     TOPOLOGICAL_GROUP_POINTWISE_TOPOLOGY) THEN
    REWRITE_TAC [GALOIS_GROUP_SUBGROUP, SUBGROUP_GENERATED_GALOIS_GROUP])

  let PROFINITE_GROUP_GALOIS_GROUP ← prove
   r"!(h:A->B) k l.
        algebraic_extension(k,l) h
        ==> profinite_group (galois_group(k,l) h)
             (pointwise_topology(group_carrier(galois_group(k,l) h)))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"ring_carrier(l:B ring)",
                      ← q r"group_carrier(galois_group(k,l) (h:A->B))"]
                     PROFINITE_GROUP_POINTWISE_TOPOLOGY_LOCAL) THEN
    REWRITE_TAC [GALOIS_GROUP_SUBGROUP, SUBGROUP_GENERATED_GALOIS_GROUP] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [GALOIS_GROUP_ORBIT_FINITE],
      REPEAT STRIP_TAC THEN MATCH_MP_TAC GALOIS_GROUP_LOCAL THEN
      ASM_REWRITE_TAC []])

  let OPEN_IN_GALOIS_GROUP_SUBGROUP ← prove
   r"!(h:A->B) k l H.
        H subgroup_of galois_group(k,l) h
        ==> (open_in (pointwise_topology(group_carrier(galois_group(k,l) h)))
                     H <=>
             ?s. FINITE s /\ s SUBSET ring_carrier l /\
                 {f | f IN group_carrier(galois_group(k,l) h) /\
                      !x. x IN s ==> f x = x} SUBSET H)"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC OPEN_IN_POINTWISE_TOPOLOGY_SUBGROUP THEN
    ASM_REWRITE_TAC [GALOIS_GROUP_SUBGROUP, SUBGROUP_GENERATED_GALOIS_GROUP])

  let CLOSED_IN_GALOIS_GROUP_INTERMEDIATE ← prove
   r"!(h:A->B) k l s.
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s
        ==> closed_in (pointwise_topology(group_carrier(galois_group(k,l) h)))
             (group_carrier(galois_group(subfield_generated l s,l) I))"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"group_carrier(galois_group(subfield_generated l s,l) I) =
      {f | f IN group_carrier(galois_group(k,l) (h:A->B)) /\
           !x. x IN s ==> f x = x}")
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN
      ASM_MESON_TAC [IN_GALOIS_GROUP_INTERMEDIATE],
      REWRITE_TAC [CLOSED_IN_POINTWISE_STABILIZER]])

  let POINTWISE_TOPOLOGY_GALOIS_GROUP_FINITE ← prove
   r"!(h:A->B) k l.
        finite_extension(k,l) h
        ==> pointwise_topology(group_carrier(galois_group(k,l) h)) =
            discrete_topology(group_carrier(galois_group(k,l) h))"
   (SIMP_TAC [POINTWISE_TOPOLOGY_FINITE, FINITE_GALOIS_GROUP])

  let GALOIS_GROUP_NEIGHBOURHOOD_BASE ← prove
   r"!(h:A->B) k l w.
        galois_extension(k,l) h /\
        open_in (pointwise_topology(group_carrier(galois_group(k,l) h))) w /\
        I IN w
        ==> ?e. e IN finite_galois_subfields(k,l) h /\
                group_carrier(galois_group(subfield_generated l e,l) I)
                SUBSET w"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"ring_carrier l:B->bool",
                      ← q r"group_carrier(galois_group(k,l) (h:A->B))",
                      ← q r"w:(B->B)->bool"]
                     POINTWISE_TOPOLOGY_NEIGHBOURHOOD_STABILIZER) THEN
    ASM_REWRITE_TAC [GALOIS_GROUP_SUBGROUP] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"s:B->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"s:B->bool"]
      FINITE_GALOIS_SUBFIELDS_FINITE) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"e:B->bool") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    TRANS_TAC SUBSET_TRANS
     (← q r"{f | f IN group_carrier(galois_group(k,l) (h:A->B)) /\
           !x. x IN s ==> f x = x}") THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o
      GEN_REWRITE_RULE I [IN_FINITE_GALOIS_SUBFIELDS]) THEN
    ASM_SIMP_TAC [SUBSET, IN_ELIM_THM, IN_GALOIS_GROUP_INTERMEDIATE] THEN
    ASM SET_TAC [])

  let CLOSURE_OF_GALOIS_GROUP_SUBGROUP_GALOIS ← prove
   r"!(h:A->B) k l H.
        galois_extension(k,l) h /\ H subgroup_of galois_group(k,l) h
        ==> (pointwise_topology(group_carrier(galois_group(k,l) h)))
            closure_of H =
            group_carrier
             (galois_group(subfield_generated l (fixed_field l H),l) I)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"H:(B->B)->bool"]
                     FIXED_FIELD_GALOIS_SUBSET) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    ASM_SIMP_TAC [CLOSURE_OF_POINTWISE_TOPOLOGY] THEN
    ASM_SIMP_TAC [EXTENSION, IN_ELIM_THM, IN_GALOIS_GROUP_INTERMEDIATE,
                  IN_FIXED_FIELD] THEN
    X_GEN_TAC (← q r"f:B->B") THEN
    ASM_CASES_TAC (← q r"(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))") THEN
    ASM_REWRITE_TAC [] THEN EQ_TAC THENL
     [DISCH_TAC THEN X_GEN_TAC (← q r"x:B") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"{x:B}")) THEN
      REWRITE_TAC [FINITE_SING, IN_SING, FORALL_UNWIND_THM2] THEN
      ASM_MESON_TAC [],
      DISCH_TAC THEN X_GEN_TAC (← q r"t:B->bool") THEN DISCH_TAC] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring",
                      ← q r"t INTER ring_carrier(l:B ring)"]
                     FINITE_GALOIS_SUBFIELDS_FINITE) THEN
    ASM_SIMP_TAC [FINITE_INTER, INTER_SUBSET, IN_FINITE_GALOIS_SUBFIELDS] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"e:B->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"e:B->bool"]
                     GALOIS_GROUP_RESTRICTION_HOMOMORPHISM) THEN
    ASM_SIMP_TAC [GALOIS_IMP_NORMAL_EXTENSION] THEN
    DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN
    MP_TAC (← ISPECL
     [← q r"h:A->B", ← q r"k:A ring", ← q r"subfield_generated l (e:B->bool)",
      ← q r"IMAGE (\(g:B->B) x. if x IN e then g x else x) H"]
     GALOIS_GROUP_FIXED_FIELD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUBGROUP_OF_HOMOMORPHIC_IMAGE THEN
      EXISTS_TAC (← q r"galois_group(k,l) (h:A->B)") THEN ASM_REWRITE_TAC [],
      STRIP_TAC] THEN
    SUBGOAL_THEN
     (← q r"(\x. if x IN e then (f:B->B) x else x) IN
      IMAGE (\(g:B->B) x. if x IN e then g x else x) H")
    MP_TAC THENL
     [FIRST_X_ASSUM (fun th => tactic_of do
        pure (GEN_REWRITE_TAC RAND_CONV [← SYM th])) THEN
      W (MP_TAC o PART_MATCH (lhand o rand) IN_GALOIS_GROUP_INTERMEDIATE o
        snd) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC
         (← q r"group_homomorphism
           (galois_group(k,l) (h:A->B),galois_group(k,subfield_generated l e) h)
           (\(g:B->B) x. if x IN e then g x else x)") THEN
        REWRITE_TAC [group_homomorphism, SUBSET, FORALL_IN_IMAGE] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"f:B->B") o CONJUNCT1) THEN
        ASM_REWRITE_TAC [],
        REWRITE_TAC [IN_FIXED_FIELD, FORALL_IN_IMAGE] THEN
        ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
        X_GEN_TAC (← q r"y:B") THEN
        ASM_CASES_TAC (← q r"(y:B) IN e") THEN ASM_REWRITE_TAC [] THEN
        ASM_MESON_TAC [SUBFIELD_OF_IMP_SUBSET, SUBSET]],
      ALL_TAC] THEN
    REWRITE_TAC [IN_IMAGE] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"g:B->B") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"g:B->B") THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN
    ASM_CASES_TAC (← q r"(x:B) IN ring_carrier l") THENL
     [FIRST_X_ASSUM (MP_TAC o C AP_THM (← q r"x:B")) THEN
      SUBGOAL_THEN (← q r"(x:B) IN e") (fun th => REWRITE_TAC [th]) THENL
       [ASM SET_TAC [], MESON_TAC []],
      SUBGOAL_THEN
       (← q r"(f:B->B) permutes ring_carrier l /\ (g:B->B) permutes ring_carrier l")
      MP_TAC THENL
       [ASM_MESON_TAC [GALOIS_GROUP_PERMUTES, SUBSET],
        DISCH_THEN (CONJUNCTS_THEN
         (MP_TAC o SPEC (← q r"x:B") o CONJUNCT1 o GEN_REWRITE_RULE I [permutes])) THEN
        ASM_REWRITE_TAC [] THEN MESON_TAC []]])

  let ARTIN_FIXED_FIELD_FINITE_ORBITS ← prove
   r"!(l:B ring) G.
        field l /\ G subgroup_of symmetric_group(ring_carrier l) /\
        (!f. f IN G ==> ring_automorphism l f) /\
        (!x. x IN ring_carrier l ==> FINITE {f x | f IN G})
        ==> galois_extension(subfield_generated l (fixed_field l G),l) I /\
            (pointwise_topology
              (group_carrier
                (galois_group(subfield_generated l (fixed_field l G),l) I)))
            closure_of G =
            group_carrier
             (galois_group(subfield_generated l (fixed_field l G),l) I)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"l:B ring", ← q r"G:(B->B)->bool"]
      GALOIS_EXTENSION_FIXED_FIELD_FINITE_ORBITS) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"!f:B->B. f IN G ==> f permutes ring_carrier l") ASSUME_TAC THENL
     [FIRST_ASSUM (MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [subgroup_of] o
        check (fun th => HolCore.Basics.is_binary "subgroup_of" (concl th))) THEN
      REWRITE_TAC [SYMMETRIC_GROUP, SUBSET, IN_ELIM_THM],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"G SUBSET
      group_carrier(galois_group(subfield_generated l (fixed_field l G),l)
                                 (I:B->B))")
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_GALOIS_GROUP_FIXED_FIELD THEN ASM_SIMP_TAC [],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"I:B->B",
                      ← q r"subfield_generated l (fixed_field l (G:(B->B)->bool))",
                      ← q r"l:B ring", ← q r"G:(B->B)->bool"]
      CLOSURE_OF_GALOIS_GROUP_SUBGROUP_GALOIS) THEN
    ASM_REWRITE_TAC [SUBGROUP_OF_GALOIS_GROUP])

  let CLOSURE_OF_GALOIS_GROUP_SUBGROUP ← prove
   r"!(h:A->B) k l H.
        algebraic_extension(k,l) h /\ H subgroup_of galois_group(k,l) h
        ==> (pointwise_topology(group_carrier(galois_group(k,l) h)))
            closure_of H =
            group_carrier
             (galois_group(subfield_generated l (fixed_field l H),l) I)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o
      GEN_REWRITE_RULE I [SUBGROUP_OF_GALOIS_GROUP]) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"H:(B->B)->bool"]
                     FIXED_FIELD_GALOIS_SUBSET) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"l:B ring", ← q r"H:(B->B)->bool"]
                     ARTIN_FIXED_FIELD_FINITE_ORBITS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [ASM_MESON_TAC [SUBSET, GALOIS_GROUP_RING_AUTOMORPHISM],
        REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC (← q r"{f x | f IN group_carrier(galois_group(k,l) (h:A->B))}") THEN
        ASM_SIMP_TAC [GALOIS_GROUP_ORBIT_FINITE] THEN ASM SET_TAC []],
      DISCH_THEN (SUBST1_TAC o SYM o CONJUNCT2)] THEN
    SUBGOAL_THEN
     (← q r"group_carrier
       (galois_group(subfield_generated l (fixed_field l H),l) (I:B->B))
      SUBSET group_carrier(galois_group(k,l) (h:A->B))")
    ASSUME_TAC THENL
     [ASM_SIMP_TAC [SUBSET, IN_GALOIS_GROUP_INTERMEDIATE], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"(H:(B->B)->bool) SUBSET
      group_carrier
       (galois_group(subfield_generated l (fixed_field l H),l) (I:B->B))")
    ASSUME_TAC THENL
     [ASM_SIMP_TAC [SUBSET, IN_GALOIS_GROUP_INTERMEDIATE, IN_FIXED_FIELD] THEN
      ASM SET_TAC [],
      ALL_TAC] THEN
    ASM_SIMP_TAC [CLOSURE_OF_POINTWISE_TOPOLOGY] THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"f:B->B") THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
     [ASM_SIMP_TAC [IN_GALOIS_GROUP_INTERMEDIATE, IN_FIXED_FIELD] THEN
      X_GEN_TAC (← q r"x:B") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"{x:B}")) THEN
      REWRITE_TAC [FINITE_SING, IN_SING, FORALL_UNWIND_THM2] THEN
      ASM_MESON_TAC [],
      ASM SET_TAC []])

  let CLOSED_IN_GALOIS_GROUP_SUBGROUP ← prove
   r"!(h:A->B) k l H.
        algebraic_extension(k,l) h /\ H subgroup_of galois_group(k,l) h
        ==> (closed_in (pointwise_topology(group_carrier(galois_group(k,l) h)))
                       H <=>
             group_carrier
              (galois_group(subfield_generated l (fixed_field l H),l) I) =
             H)"
   (MESON_TAC [CLOSURE_OF_GALOIS_GROUP_SUBGROUP, CLOSURE_OF_EQ])

  let INFINITE_GALOIS_CORRESPONDENCE ← prove
   r"!(h:A->B) k l.
     galois_extension(k,l) h
     ==> (!H. H subgroup_of galois_group(k,l) h /\
              closed_in (pointwise_topology(group_carrier(galois_group(k,l) h)))
                        H
              ==> fixed_field l H subfield_of l /\
                  IMAGE h (ring_carrier k) SUBSET fixed_field l H /\
                  group_carrier(galois_group
                    (subfield_generated l (fixed_field l H),l) I) = H) /\
         (!s. s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s
              ==> group_carrier(galois_group(subfield_generated l s,l) I)
                  subgroup_of galois_group(k,l) h /\
                  closed_in
                   (pointwise_topology(group_carrier(galois_group(k,l) h)))
                   (group_carrier(galois_group(subfield_generated l s,l) I)) /\
                  fixed_field l
                   (group_carrier(galois_group(subfield_generated l s,l) I)) =
                  s)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP GALOIS_IMP_ALGEBRAIC_EXTENSION) THEN
    CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
     [ASM_SIMP_TAC [← GSYM CLOSED_IN_GALOIS_GROUP_SUBGROUP] THEN
      MATCH_MP_TAC FIXED_FIELD_GALOIS_SUBSET THEN
      ASM_SIMP_TAC [GALOIS_IMP_FIELD_EXTENSION, SUBGROUP_OF_IMP_SUBSET],
      ASM_SIMP_TAC [GALOIS_GROUP_INTERMEDIATE_SUBGROUP,
                    CLOSED_IN_GALOIS_GROUP_INTERMEDIATE] THEN
      ASM_MESON_TAC [FIXED_FIELD_GALOIS_GROUP_INTERMEDIATE]])

  pure { TOPOLOGICAL_GROUP_GALOIS_GROUP, PROFINITE_GROUP_GALOIS_GROUP,
         OPEN_IN_GALOIS_GROUP_SUBGROUP, CLOSED_IN_GALOIS_GROUP_INTERMEDIATE,
         POINTWISE_TOPOLOGY_GALOIS_GROUP_FINITE, GALOIS_GROUP_NEIGHBOURHOOD_BASE,
         CLOSURE_OF_GALOIS_GROUP_SUBGROUP_GALOIS, ARTIN_FIXED_FIELD_FINITE_ORBITS,
         CLOSURE_OF_GALOIS_GROUP_SUBGROUP, CLOSED_IN_GALOIS_GROUP_SUBGROUP,
         INFINITE_GALOIS_CORRESPONDENCE }

/- ------------------------------------------------------------------------- -/
/- Open Galois groups of intermediate fields, normality, and the lattice     -/
/- operations up to closure.  (infinite_galois.ml 415-611)                   -/
/- ------------------------------------------------------------------------- -/

structure IGB where
  OPEN_IN_GALOIS_GROUP_INTERMEDIATE : thm
  INFINITE_GALOIS_CORRESPONDENCE_NORMAL : thm
  GALOIS_GROUP_INTER_CLOSURE : thm
  FIXED_FIELD_INTER_CLOSED : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIGB [HolBase] (D : InfiniteGaloisDeps) (BIGA : IGA) : ExceptT String IO IGB := do
  -- @@SCOPE BEGIN
  let { CLOSURE_OF_GALOIS_GROUP_SUBGROUP, INFINITE_GALOIS_CORRESPONDENCE,
        OPEN_IN_GALOIS_GROUP_SUBGROUP, .. } := BIGA
  let { FINITE_GALOIS_SUBFIELDS_FINITE, FIXED_FIELD_ANTIMONO,
        FIXED_FIELD_GALOIS_GROUP_INTERMEDIATE, FIXED_FIELD_SUBGROUP_GENERATED,
        FIXED_FIELD_UNION, GALOIS_CORRESPONDENCE_NORMAL, GALOIS_EXTENSION_NORMAL_SUBGROUP,
        GALOIS_GROUP_COMPOSITUM, GALOIS_GROUP_FIXES, GALOIS_GROUP_INTERMEDIATE_SUBGROUP,
        GALOIS_GROUP_RING_HOMOMORPHISM, GALOIS_IMP_ALGEBRAIC_EXTENSION,
        GALOIS_IMP_FIELD_EXTENSION, GALOIS_IMP_NORMAL_EXTENSION,
        IN_FINITE_GALOIS_SUBFIELDS, IN_FIXED_FIELD, IN_GALOIS_GROUP_INTERMEDIATE,
        SUBFIELD_OF_FIXED_FIELD, .. } := D.qgalois
  let { CARRIER_SUBFIELD_GENERATED_SUBFIELD, field_extension,
        FINITE_EXTENSION_SUBFIELD_GENERATED, FINITE_EXTENSION_SUBFIELD_GENERATORS,
        SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED, SUBFIELD_GENERATED_IDEMPOT_GEN,
        SUBFIELD_GENERATED_MINIMAL, SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET,
        SUBFIELD_OF_IMP_SUBSET, SUBFIELD_SUBFIELD_GENERATED, .. } := D.qfieldtheory
  let { SUBGROUP_SUBGROUP_GENERATED, .. } := D.qgrouptheory
  let { ring_endomorphism, ring_homomorphism, ring_monomorphism, .. } := D.qringtheory
  let { ASM_MESON_TAC, MESON_TAC, SET_TAC, .. } := D.pg.mt
  let { subgroup_of, .. } := D.pg.qgrouptheory
  let { FORALL_IN_IMAGE, .. } := D.pg.mt.core1
  let { IN_ELIM_THM, IN_SING, .. } := D.pg.mt.core2
  let { SUBSET, SUBSET_TRANS, UNION_SUBSET, .. } := D.pg.mt.core4
  let { FORALL_UNWIND_THM2, .. } := D.pg.mt.core5
  -- @@SCOPE END

  let OPEN_IN_GALOIS_GROUP_INTERMEDIATE ← prove
   r"!(h:A->B) k l s.
        galois_extension(k,l) h /\
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s
        ==> (open_in (pointwise_topology(group_carrier(galois_group(k,l) h)))
              (group_carrier(galois_group(subfield_generated l s,l) I)) <=>
             finite_extension(k,subfield_generated l s) h)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
      MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
    ASM_SIMP_TAC [OPEN_IN_GALOIS_GROUP_SUBGROUP,
                  GALOIS_GROUP_INTERMEDIATE_SUBGROUP] THEN
    EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"t:B->bool") STRIP_ASSUME_TAC) THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"t:B->bool"]
                       FINITE_GALOIS_SUBFIELDS_FINITE) THEN
      ASM_REWRITE_TAC [IN_FINITE_GALOIS_SUBFIELDS] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"e:B->bool") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"(s:B->bool) SUBSET e") ASSUME_TAC THENL
       [MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"s:B->bool"]
                         FIXED_FIELD_GALOIS_GROUP_INTERMEDIATE) THEN
        MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"e:B->bool"]
                         FIXED_FIELD_GALOIS_GROUP_INTERMEDIATE) THEN
        ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN
        MP_TAC (← ISPECL
         [← q r"l:B ring",
          ← q r"group_carrier(galois_group(subfield_generated l (e:B->bool),l) I)",
          ← q r"group_carrier(galois_group(subfield_generated l (s:B->bool),l) I)"]
         FIXED_FIELD_ANTIMONO) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
        TRANS_TAC SUBSET_TRANS
         (← q r"{f | f IN group_carrier(galois_group(k,l) (h:A->B)) /\
               !x. x IN t ==> f x = x}") THEN
        ASM_REWRITE_TAC [] THEN
        ASM_SIMP_TAC [SUBSET, IN_ELIM_THM, IN_GALOIS_GROUP_INTERMEDIATE] THEN
        ASM_MESON_TAC [SUBSET],
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"l:B ring", ← q r"s:B->bool", ← q r"e:B->bool"]
                       SUBFIELD_GENERATED_IDEMPOT_GEN) THEN
      ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"subfield_generated l (e:B->bool)",
                        ← q r"s:B->bool"] FINITE_EXTENSION_SUBFIELD_GENERATED) THEN
      ASM_SIMP_TAC [],
      DISCH_TAC] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"s:B->bool"]
                     FINITE_EXTENSION_SUBFIELD_GENERATORS) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:B->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"b:B->bool") THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [ASM_MESON_TAC [SUBFIELD_OF_IMP_SUBSET, SUBSET_TRANS], ALL_TAC] THEN
    ASM_SIMP_TAC [SUBSET, IN_ELIM_THM, IN_GALOIS_GROUP_INTERMEDIATE] THEN
    X_GEN_TAC (← q r"f:B->B") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"(s:B->bool) SUBSET fixed_field l {f:B->B}") MP_TAC THENL
     [UNDISCH_THEN
       (← q r"ring_carrier(subfield_generated l
          (IMAGE (h:A->B) (ring_carrier k) UNION b)) = s")
       (fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [← SYM th])) THEN
      MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN CONJ_TAC THENL
       [REWRITE_TAC [UNION_SUBSET, SUBSET, FORALL_IN_IMAGE, IN_FIXED_FIELD,
                     IN_SING, FORALL_UNWIND_THM2] THEN
        CONJ_TAC THENL
         [X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN
          CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [GALOIS_GROUP_FIXES]] THEN
          UNDISCH_TAC (← q r"ring_monomorphism(k:A ring,l:B ring) h") THEN
          REWRITE_TAC [ring_monomorphism, ring_homomorphism, SUBSET,
                       FORALL_IN_IMAGE] THEN
          ASM_MESON_TAC [],
          ASM_MESON_TAC [SUBFIELD_OF_IMP_SUBSET, SUBSET]],
        MATCH_MP_TAC SUBFIELD_OF_FIXED_FIELD THEN
        ASM_REWRITE_TAC [IN_SING, FORALL_UNWIND_THM2] THEN
        ASM_MESON_TAC [GALOIS_GROUP_RING_HOMOMORPHISM, ring_endomorphism]],
      REWRITE_TAC [SUBSET, IN_FIXED_FIELD, IN_SING, FORALL_UNWIND_THM2] THEN
      MESON_TAC []])

  let INFINITE_GALOIS_CORRESPONDENCE_NORMAL ← prove
   r"!(h:A->B) k l H.
        galois_extension(k,l) h /\ H subgroup_of galois_group(k,l) h /\
        closed_in (pointwise_topology(group_carrier(galois_group(k,l) h))) H
        ==> (H normal_subgroup_of galois_group(k,l) h <=>
             galois_extension(k,subfield_generated l (fixed_field l H)) h)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"]
                     INFINITE_GALOIS_CORRESPONDENCE) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"H:(B->B)->bool") o CONJUNCT1) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [← SYM th])) THEN
    EQ_TAC THEN DISCH_TAC THENL
     [MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring",
                        ← q r"fixed_field l (H:(B->B)->bool)"]
                       GALOIS_EXTENSION_NORMAL_SUBGROUP) THEN
      ASM_SIMP_TAC [],
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring",
                        ← q r"fixed_field l (H:(B->B)->bool)"]
                       GALOIS_CORRESPONDENCE_NORMAL) THEN
      ASM_SIMP_TAC [GALOIS_IMP_NORMAL_EXTENSION]])

  let GALOIS_GROUP_INTER_CLOSURE ← prove
   r"!(h:A->B) k l s t.
        galois_extension(k,l) h /\
        s subfield_of l /\ t subfield_of l /\
        IMAGE h (ring_carrier k) SUBSET s /\ IMAGE h (ring_carrier k) SUBSET t
        ==> group_carrier(galois_group(subfield_generated l (s INTER t),l) I) =
            (pointwise_topology(group_carrier(galois_group(k,l) h)))
            closure_of
            group_carrier(subgroup_generated (galois_group(k,l) h)
              (group_carrier(galois_group(subfield_generated l s,l) I) UNION
               group_carrier(galois_group(subfield_generated l t,l) I)))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"s:B->bool"]
      GALOIS_GROUP_INTERMEDIATE_SUBGROUP) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"t:B->bool"]
      GALOIS_GROUP_INTERMEDIATE_SUBGROUP) THEN
    ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN
    MP_TAC (← ISPECL
     [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring",
      ← q r"group_carrier(subgroup_generated (galois_group(k,l) (h:A->B))
        (group_carrier(galois_group(subfield_generated l s,l) I) UNION
         group_carrier(galois_group(subfield_generated l t,l) I)))"]
     CLOSURE_OF_GALOIS_GROUP_SUBGROUP) THEN
    ASM_SIMP_TAC [GALOIS_IMP_ALGEBRAIC_EXTENSION, SUBGROUP_SUBGROUP_GENERATED] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC (← ISPECL
     [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring",
      ← q r"group_carrier(galois_group(subfield_generated l s,l) (I:B->B)) UNION
       group_carrier(galois_group(subfield_generated l t,l) I)"]
     FIXED_FIELD_SUBGROUP_GENERATED) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [UNION_SUBSET] THEN ASM_MESON_TAC [subgroup_of],
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC [FIXED_FIELD_UNION] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"s:B->bool"]
                     FIXED_FIELD_GALOIS_GROUP_INTERMEDIATE) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"t:B->bool"]
                     FIXED_FIELD_GALOIS_GROUP_INTERMEDIATE) THEN
    ASM_SIMP_TAC [])

  let FIXED_FIELD_INTER_CLOSED ← prove
   r"!(h:A->B) k l G H.
        galois_extension(k,l) h /\
        G subgroup_of galois_group(k,l) h /\
        closed_in (pointwise_topology(group_carrier(galois_group(k,l) h))) G /\
        H subgroup_of galois_group(k,l) h /\
        closed_in (pointwise_topology(group_carrier(galois_group(k,l) h))) H
        ==> fixed_field l (G INTER H) =
            ring_carrier(subfield_generated l
              (fixed_field l G UNION fixed_field l H))"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"]
                     INFINITE_GALOIS_CORRESPONDENCE) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← SPEC (← q r"G:(B->B)->bool") (← CONJUNCT1 th)) THEN
            MP_TAC (← SPEC (← q r"H:(B->B)->bool") (← CONJUNCT1 th)) THEN
            ASSUME_TAC (← CONJUNCT2 th))) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    ABBREV_TAC (← q r"s = fixed_field l (G:(B->B)->bool)") THEN
    ABBREV_TAC (← q r"t = fixed_field l (H:(B->B)->bool)") THEN
    MAP_EVERY EXPAND_TAC ["G", "H"] THEN
    ASM_SIMP_TAC [← GSYM GALOIS_GROUP_COMPOSITUM] THEN
    ONCE_REWRITE_TAC [← GSYM SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC
     (← q r"ring_carrier(subfield_generated l (s UNION t:B->bool))")) THEN
    ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC (← q r"s UNION t:B->bool") THEN
      CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      MATCH_MP_TAC SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET THEN
      ASM_SIMP_TAC [UNION_SUBSET, SUBFIELD_OF_IMP_SUBSET],
      SIMP_TAC [SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED]])

  pure { OPEN_IN_GALOIS_GROUP_INTERMEDIATE, INFINITE_GALOIS_CORRESPONDENCE_NORMAL,
         GALOIS_GROUP_INTER_CLOSURE, FIXED_FIELD_INTER_CLOSED }

/- ------------------------------------------------------------------------- -/
/- Restriction to normal subextensions: continuity, quotient maps, finite    -/
/- Galois subextensions and the index.  (infinite_galois.ml 613-822)         -/
/- ------------------------------------------------------------------------- -/

structure IGC where
  CONTINUOUS_MAP_GALOIS_GROUP_RESTRICTION : thm
  GALOIS_GROUP_RESTRICTION_QUOTIENT_MAP : thm
  CONTINUOUS_MAP_GALOIS_GROUP_RESTRICTION_FINITE : thm
  GALOIS_GROUP_RESTRICTION_FINITE_GALOIS : thm
  INFINITE_GALOIS_CORRESPONDENCE_INDEX : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIGC [HolBase] (D : InfiniteGaloisDeps) (BIGA : IGA) (BIGB : IGB) : ExceptT String IO IGC := do
  -- @@SCOPE BEGIN
  let { POINTWISE_TOPOLOGY_GALOIS_GROUP_FINITE, PROFINITE_GROUP_GALOIS_GROUP, .. } := BIGA
  let { OPEN_IN_GALOIS_GROUP_INTERMEDIATE, .. } := BIGB
  let { PROFINITE_GROUP_CONTINUOUS_EPIMORPHISM, .. } := D.qprofinitegroups
  let { FINITE_GALOIS_GROUP, FINITE_GALOIS_SUBFIELDS_FINITE, GALOIS_CORRESPONDENCE_INDEX,
        GALOIS_GROUP_INTERMEDIATE_SUBGROUP, GALOIS_GROUP_RESTRICTION,
        GALOIS_GROUP_RESTRICTION_NORMAL, GALOIS_IMP_FIELD_EXTENSION,
        GALOIS_IMP_NORMAL_EXTENSION, IN_FINITE_GALOIS_SUBFIELDS,
        IN_GALOIS_GROUP_INTERMEDIATE, .. } := D.qgalois
  let { ALGEBRAIC_IMP_FIELD_EXTENSION, CARRIER_SUBFIELD_GENERATED_SUBFIELD,
        field_extension, FINITE_EXTENSION_SUBFIELD_GENERATORS,
        NORMAL_IMP_ALGEBRAIC_EXTENSION, SUBFIELD_GENERATED_IDEMPOT_GEN,
        SUBFIELD_GENERATED_MINIMAL, SUBFIELD_OF_IMP_SUBSET, SUBFIELD_OF_SUBFIELD_GENERATED,
        .. } := D.qfieldtheory
  let { CARD_EQ_GROUP_COSETS_PREIMAGE, FINITE_GROUP_COSETS, NORMAL_SUBGROUP_GROUP_KERNEL,
        .. } := D.qgrouptheory
  let { CARD_EQ_CARD_IMP, .. } := D.qcard
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, .. } := D.pg.mt
  let { CONTINUOUS_MAP_POINTWISE_TOPOLOGY, HAUSDORFF_SPACE_POINTWISE_TOPOLOGY,
        OPEN_IN_EMPTY, OPEN_IN_POINTWISE_TOPOLOGY_POINT, OPEN_IN_TOPSPACE,
        TOPSPACE_POINTWISE_TOPOLOGY, .. } := D.pg.qmetric
  let { group_cosets, group_epimorphism, group_homomorphism, .. } := D.pg.qgrouptheory
  let { EMPTY_GSPEC, EQ_TRANS, EXTENSION, FORALL_IN_IMAGE, .. } := D.pg.mt.core1
  let { IN_ELIM_THM, .. } := D.pg.mt.core2
  let { SUBSET, SUBSET_TRANS, UNION_SUBSET, .. } := D.pg.mt.core4
  -- @@SCOPE END

  let CONTINUOUS_MAP_GALOIS_GROUP_RESTRICTION ← prove
   r"!(h:A->B) k l s.
        field_extension(k,l) h /\ s subfield_of l /\
        normal_extension(k,subfield_generated l s) h
        ==> continuous_map
             (pointwise_topology(group_carrier(galois_group(k,l) h)),
              pointwise_topology
               (group_carrier(galois_group(k,subfield_generated l s) h)))
             (\f x. if x IN s then f x else x)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"s:B->bool"]
                     GALOIS_GROUP_RESTRICTION_NORMAL) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC [group_homomorphism, SUBSET, FORALL_IN_IMAGE] THEN
    DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC [CONTINUOUS_MAP_POINTWISE_TOPOLOGY,
                     TOPSPACE_POINTWISE_TOPOLOGY] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:B", ← q r"y:B"] THEN
    ASM_CASES_TAC (← q r"(x:B) IN s") THEN
    ASM_REWRITE_TAC [OPEN_IN_POINTWISE_TOPOLOGY_POINT] THEN
    ASM_CASES_TAC (← q r"x:B = y") THEN
    ASM_REWRITE_TAC [EMPTY_GSPEC, OPEN_IN_EMPTY] THEN
    REWRITE_TAC [← SET_RULE (← q r"{x:B->B | x IN s} = s")] THEN
    MESON_TAC [OPEN_IN_TOPSPACE, TOPSPACE_POINTWISE_TOPOLOGY])

  let GALOIS_GROUP_RESTRICTION_QUOTIENT_MAP ← prove
   r"!(h:A->B) k l s.
        normal_extension(k,l) h /\ s subfield_of l /\
        normal_extension(k,subfield_generated l s) h
        ==> open_map
             (pointwise_topology(group_carrier(galois_group(k,l) h)),
              pointwise_topology
               (group_carrier(galois_group(k,subfield_generated l s) h)))
             (\f x. if x IN s then f x else x) /\
            quotient_map
             (pointwise_topology(group_carrier(galois_group(k,l) h)),
              pointwise_topology
               (group_carrier(galois_group(k,subfield_generated l s) h)))
             (\f x. if x IN s then f x else x)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do
      let t ← q r"normal_extension(k:A ring,l:B ring) h"
      pure (ASSUME_TAC (← MATCH_MP NORMAL_IMP_ALGEBRAIC_EXTENSION
        (← liftExcept (check (fun th => concl th == t) th))))) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
    MP_TAC (← ISPECL
     [← q r"galois_group(k:A ring,l:B ring) h",
      ← q r"galois_group(k:A ring,subfield_generated l s) (h:A->B)",
      ← q r"pointwise_topology(group_carrier(galois_group(k:A ring,l:B ring) h))",
      ← q r"pointwise_topology(group_carrier
        (galois_group(k:A ring,subfield_generated l s) (h:A->B)))",
      ← q r"\(f:B->B) x. if x IN s then f x else x"]
     PROFINITE_GROUP_CONTINUOUS_EPIMORPHISM) THEN
    ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN
    ASM_SIMP_TAC [PROFINITE_GROUP_GALOIS_GROUP,
                  HAUSDORFF_SPACE_POINTWISE_TOPOLOGY,
                  TOPSPACE_POINTWISE_TOPOLOGY,
                  CONTINUOUS_MAP_GALOIS_GROUP_RESTRICTION] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"s:B->bool"]
                     GALOIS_GROUP_RESTRICTION_NORMAL) THEN
    ASM_SIMP_TAC [])

  let CONTINUOUS_MAP_GALOIS_GROUP_RESTRICTION_FINITE ← prove
   r"!(h:A->B) k l e.
        field_extension(k,l) h /\ e IN finite_galois_subfields(k,l) h
        ==> continuous_map
             (pointwise_topology(group_carrier(galois_group(k,l) h)),
              discrete_topology
               (group_carrier(galois_group(k,subfield_generated l e) h)))
             (\f x. if x IN e then f x else x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [IN_FINITE_GALOIS_SUBFIELDS] THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"subfield_generated l (e:B->bool)"]
                     POINTWISE_TOPOLOGY_GALOIS_GROUP_FINITE) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC CONTINUOUS_MAP_GALOIS_GROUP_RESTRICTION THEN
    ASM_SIMP_TAC [GALOIS_IMP_NORMAL_EXTENSION])

  let GALOIS_GROUP_RESTRICTION_FINITE_GALOIS ← prove
   r"!(h:A->B) k l e.
        galois_extension(k,l) h /\ e IN finite_galois_subfields(k,l) h
        ==> group_epimorphism
             (galois_group(k,l) h,galois_group(k,subfield_generated l e) h)
             (\f x. if x IN e then f x else x) /\
            continuous_map
             (pointwise_topology(group_carrier(galois_group(k,l) h)),
              discrete_topology
               (group_carrier(galois_group(k,subfield_generated l e) h)))
             (\f x. if x IN e then f x else x) /\
            group_kernel
             (galois_group(k,l) h,galois_group(k,subfield_generated l e) h)
             (\f x. if x IN e then f x else x) =
            group_carrier(galois_group(subfield_generated l e,l) I) /\
            group_carrier(galois_group(subfield_generated l e,l) I)
            normal_subgroup_of galois_group(k,l) h /\
            open_in (pointwise_topology(group_carrier(galois_group(k,l) h)))
                    (group_carrier(galois_group(subfield_generated l e,l) I))"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC [CONTINUOUS_MAP_GALOIS_GROUP_RESTRICTION_FINITE,
                  GALOIS_IMP_FIELD_EXTENSION] THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o
      GEN_REWRITE_RULE I [IN_FINITE_GALOIS_SUBFIELDS]) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"e:B->bool"]
                     GALOIS_GROUP_RESTRICTION) THEN
    ASM_SIMP_TAC [GALOIS_IMP_NORMAL_EXTENSION] THEN STRIP_TAC THEN
    ASM_SIMP_TAC [OPEN_IN_GALOIS_GROUP_INTERMEDIATE] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC NORMAL_SUBGROUP_GROUP_KERNEL THEN
    ASM_MESON_TAC [group_epimorphism])

  let INFINITE_GALOIS_CORRESPONDENCE_INDEX ← prove
   r"!(h:A->B) k l s.
        galois_extension(k,l) h /\
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
        finite_extension(k,subfield_generated l s) h
        ==> CARD(group_cosets (galois_group(k,l) h)
                  (group_carrier(galois_group(subfield_generated l s,l) I))) =
            extension_degree(k,subfield_generated l s) h"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"s:B->bool"]
      FINITE_EXTENSION_SUBFIELD_GENERATORS) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:B->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"b:B->bool"]
      FINITE_GALOIS_SUBFIELDS_FINITE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [SUBFIELD_OF_IMP_SUBSET, SUBSET_TRANS],
      DISCH_THEN (X_CHOOSE_THEN (← q r"e:B->bool") STRIP_ASSUME_TAC)] THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o
      GEN_REWRITE_RULE I [IN_FINITE_GALOIS_SUBFIELDS]) THEN
    SUBGOAL_THEN (← q r"(s:B->bool) SUBSET e") ASSUME_TAC THENL
     [-- `(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) o check (fun th ->
      -- is_eq(concl th) && rhs(concl th) = `s:B->bool`)`: the quotation is
      -- parsed only when `is_eq` holds, as `&&`.
      FIRST_X_ASSUM (fun th => tactic_of do
        let ok ← if is_eq (concl th) then do
            let z ← q r"s:B->bool"
            pure (match rhs (concl th) with | .ok r => r == z | .error _ => false)
          else pure false
        let th' ← liftExcept (check (fun _ => ok) th)
        pure (GEN_REWRITE_TAC LAND_CONV [← SYM th'])) THEN
      MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN
      ASM_REWRITE_TAC [UNION_SUBSET],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"e:B->bool"]
      GALOIS_GROUP_RESTRICTION_FINITE_GALOIS) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(s:B->bool) subfield_of subfield_generated l e") ASSUME_TAC THENL
     [ASM_SIMP_TAC [SUBFIELD_OF_SUBFIELD_GENERATED], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"group_carrier(galois_group(subfield_generated l s,l) I) =
      {f | f IN group_carrier(galois_group(k,l) (h:A->B)) /\
           (\x. if x IN e then f x else x) IN
           group_carrier(galois_group(subfield_generated
                           (subfield_generated l e) s,
                          subfield_generated l e) I)}")
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC (← q r"f:B->B") THEN
      REWRITE_TAC [IN_ELIM_THM] THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"f:B->B", ← q r"k:A ring", ← q r"l:B ring",
                        ← q r"s:B->bool"] IN_GALOIS_GROUP_INTERMEDIATE) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_CASES_TAC (← q r"(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))") THEN
      ASM_REWRITE_TAC [] THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"\x. if x IN e then (f:B->B) x else x",
                        ← q r"k:A ring", ← q r"subfield_generated l (e:B->bool)",
                        ← q r"s:B->bool"] IN_GALOIS_GROUP_INTERMEDIATE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM SET_TAC [], ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN
       (← q r"(\x. if x IN e then (f:B->B) x else x) IN
        group_carrier(galois_group(k,subfield_generated l e) (h:A->B))")
      (fun th => REWRITE_TAC [th]) THENL
       [UNDISCH_TAC
         (← q r"group_epimorphism
           (galois_group(k,l) (h:A->B),galois_group(k,subfield_generated l e) h)
           (\f x. if x IN e then f x else x)") THEN
        REWRITE_TAC [group_epimorphism, group_homomorphism, SUBSET,
                     FORALL_IN_IMAGE] THEN
        ASM_SIMP_TAC [],
        ALL_TAC] THEN
      EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:B")) THEN
      SUBGOAL_THEN (← q r"(x:B) IN e") (fun th => SIMP_TAC [th]) THEN ASM SET_TAC [],
      ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"galois_group(k:A ring,l:B ring) h",
      ← q r"galois_group(k:A ring,subfield_generated l e) (h:A->B)",
      ← q r"\(f:B->B) x. if x IN e then f x else x",
      ← q r"group_carrier(galois_group(subfield_generated
                      (subfield_generated l e) s,
                     subfield_generated l e) (I:B->B))"]
     CARD_EQ_GROUP_COSETS_PREIMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC GALOIS_GROUP_INTERMEDIATE_SUBGROUP THEN
      ASM_REWRITE_TAC [] THEN ASM SET_TAC [],
      ALL_TAC] THEN
    DISCH_THEN (ASSUME_TAC o BETA_RULE) THEN
    TRANS_TAC EQ_TRANS
     (← q r"CARD(group_cosets (galois_group(k,subfield_generated l e) (h:A->B))
            (group_carrier(galois_group(subfield_generated
                                          (subfield_generated l e) s,
                                        subfield_generated l e) I)))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_EQ_CARD_IMP THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC FINITE_GROUP_COSETS THEN
      MATCH_MP_TAC FINITE_GALOIS_GROUP THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [group_cosets] THEN
      SUBGOAL_THEN (← q r"subfield_generated (subfield_generated l e) s =
                    subfield_generated l (s:B->bool)")
      ASSUME_TAC THENL
       [MATCH_MP_TAC SUBFIELD_GENERATED_IDEMPOT_GEN THEN
        ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD],
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"subfield_generated l (e:B->bool)",
                        ← q r"s:B->bool"] GALOIS_CORRESPONDENCE_INDEX) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC [], ASM_REWRITE_TAC []]])

  pure { CONTINUOUS_MAP_GALOIS_GROUP_RESTRICTION, GALOIS_GROUP_RESTRICTION_QUOTIENT_MAP,
         CONTINUOUS_MAP_GALOIS_GROUP_RESTRICTION_FINITE,
         GALOIS_GROUP_RESTRICTION_FINITE_GALOIS, INFINITE_GALOIS_CORRESPONDENCE_INDEX }

/- ------------------------------------------------------------------------- -/
/- Compactness: compatible nonempty sets of restrictions come from one       -/
/- element of the Galois group.  (infinite_galois.ml 824-926)                -/
/- ------------------------------------------------------------------------- -/

structure IGD where
  GALOIS_GROUP_COMPATIBLE_RESTRICTIONS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIGD [HolBase] (D : InfiniteGaloisDeps) (BIGA : IGA) (BIGC : IGC) : ExceptT String IO IGD := do
  -- @@SCOPE BEGIN
  let { PROFINITE_GROUP_GALOIS_GROUP, .. } := BIGA
  let { CONTINUOUS_MAP_GALOIS_GROUP_RESTRICTION_FINITE, .. } := BIGC
  let { profinite_group, .. } := D.qprofinitegroups
  let { FINITE_GALOIS_SUBFIELDS_UPPER_BOUNDS, GALOIS_GROUP_I, GALOIS_GROUP_RESTRICTION,
        GALOIS_IMP_NORMAL_EXTENSION, IN_FINITE_GALOIS_SUBFIELDS, .. } := D.qgalois
  let { ALGEBRAIC_IMP_FIELD_EXTENSION, field_extension, NORMAL_IMP_ALGEBRAIC_EXTENSION,
        .. } := D.qfieldtheory
  let { CLOSED_IN_DISCRETE_TOPOLOGY, .. } := D.qmetric
  let { ASM_MESON_TAC, SET_TAC, .. } := D.pg.mt
  let { CLOSED_IN_CONTINUOUS_MAP_PREIMAGE, COMPACT_SPACE_FIP, TOPSPACE_POINTWISE_TOPOLOGY,
        .. } := D.pg.qmetric
  let { group_epimorphism, .. } := D.pg.qgrouptheory
  let { EXTENSION, FINITE_SUBSET_IMAGE, FORALL_IN_IMAGE, FUN_EQ_THM, IMAGE_CLAUSES,
        .. } := D.pg.mt.core1
  let { IN_ELIM_THM, IN_IMAGE, INTERS_0, INTERS_IMAGE, MEMBER_NOT_EMPTY, NOT_IN_EMPTY,
        .. } := D.pg.mt.core2
  let { SUBSET, UNIV_NOT_EMPTY, .. } := D.pg.mt.core4
  -- @@SCOPE END

  let GALOIS_GROUP_COMPATIBLE_RESTRICTIONS ← prove
   r"!(h:A->B) k l S.
        normal_extension(k,l) h /\
        (!e. e IN finite_galois_subfields(k,l) h
             ==> ~(S e = {}) /\
                 S e SUBSET
                 group_carrier(galois_group(k,subfield_generated l e) h)) /\
        (!e e'. e IN finite_galois_subfields(k,l) h /\
                e' IN finite_galois_subfields(k,l) h /\ e SUBSET e'
                ==> IMAGE (\f x. if x IN e then f x else x) (S e') SUBSET S e)
        ==> ?f. f IN group_carrier(galois_group(k,l) h) /\
                !e. e IN finite_galois_subfields(k,l) h
                    ==> (\x. if x IN e then f x else x) IN S e"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "S") (LABEL_TAC "c"))) THEN
    ASM_CASES_TAC (← q r"finite_galois_subfields(k,l) (h:A->B) = {}") THENL
     [EXISTS_TAC (← q r"I:B->B") THEN ASM_REWRITE_TAC [NOT_IN_EMPTY, GALOIS_GROUP_I],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"field_extension(k:A ring,l:B ring) h") ASSUME_TAC THENL
     [ASM_MESON_TAC [NORMAL_IMP_ALGEBRAIC_EXTENSION,
                     ALGEBRAIC_IMP_FIELD_EXTENSION],
      ALL_TAC] THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP NORMAL_IMP_ALGEBRAIC_EXTENSION) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"]
                     PROFINITE_GROUP_GALOIS_GROUP) THEN
    ASM_REWRITE_TAC [profinite_group, COMPACT_SPACE_FIP] THEN
    DISCH_THEN (MP_TAC o SPEC
     (← q r"IMAGE (\e. {f | f IN group_carrier(galois_group(k,l) (h:A->B)) /\
                      (\x. if x IN e then f x else x) IN
                      (S:(B->bool)->(B->B)->bool) e})
            (finite_galois_subfields(k,l) h)") o CONJUNCT1 o CONJUNCT2) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [FORALL_IN_IMAGE] THEN CONJ_TAC THENL
       [X_GEN_TAC (← q r"e:B->bool") THEN DISCH_TAC THEN
        MP_TAC (← ISPECL
         [← q r"\(f:B->B) x. if x IN e then f x else x",
          ← q r"pointwise_topology(group_carrier(galois_group(k,l) (h:A->B)))",
          ← q r"discrete_topology
            (group_carrier(galois_group(k,subfield_generated l e) (h:A->B)))",
          ← q r"(S:(B->bool)->(B->B)->bool) e"]
         CLOSED_IN_CONTINUOUS_MAP_PREIMAGE) THEN
        ASM_SIMP_TAC [CONTINUOUS_MAP_GALOIS_GROUP_RESTRICTION_FINITE,
                      CLOSED_IN_DISCRETE_TOPOLOGY] THEN
        REWRITE_TAC [TOPSPACE_POINTWISE_TOPOLOGY],
        ALL_TAC] THEN
      X_GEN_TAC (← q r"u:((B->B)->bool)->bool") THEN
      DISCH_THEN (MP_TAC o GEN_REWRITE_RULE I [FINITE_SUBSET_IMAGE]) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"c:(B->bool)->bool") STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC (← q r"c:(B->bool)->bool = {}") THEN
      ASM_REWRITE_TAC [IMAGE_CLAUSES, INTERS_0, UNIV_NOT_EMPTY] THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"c:(B->bool)->bool"]
                       FINITE_GALOIS_SUBFIELDS_UPPER_BOUNDS) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"e:B->bool") STRIP_ASSUME_TAC) THEN
      USE_THEN "S" (MP_TAC o SPEC (← q r"e:B->bool")) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
      REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"p:B->B")) ASSUME_TAC) THEN
      SUBGOAL_THEN
       (← q r"(e:B->bool) subfield_of l /\ IMAGE (h:A->B) (ring_carrier k) SUBSET e /\
        normal_extension(k,subfield_generated l e) h")
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC [IN_FINITE_GALOIS_SUBFIELDS, GALOIS_IMP_NORMAL_EXTENSION],
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"e:B->bool"]
                       GALOIS_GROUP_RESTRICTION) THEN
      ASM_REWRITE_TAC [group_epimorphism] THEN
      DISCH_THEN (MP_TAC o CONJUNCT2 o CONJUNCT1) THEN
      REWRITE_TAC [EXTENSION, IN_IMAGE] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"p:B->B")) THEN
      SUBGOAL_THEN
       (← q r"(p:B->B) IN
        group_carrier(galois_group(k,subfield_generated l e) (h:A->B))")
      (fun th => REWRITE_TAC [th]) THENL [ASM SET_TAC [], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:B->B") STRIP_ASSUME_TAC) THEN
      REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, INTERS_IMAGE, IN_ELIM_THM] THEN
      EXISTS_TAC (← q r"g:B->B") THEN X_GEN_TAC (← q r"e':B->bool") THEN DISCH_TAC THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"(e':B->bool) SUBSET e /\
                    e' IN finite_galois_subfields(k,l) (h:A->B)")
      STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"(\x. if x IN e' then (g:B->B) x else x) =
        (\x. if x IN e' then p x else x)")
      SUBST1_TAC THENL
       [ASM_REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"x:B") THEN
        ASM_CASES_TAC (← q r"(x:B) IN e'") THEN ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN (← q r"(x:B) IN e") (fun th => REWRITE_TAC [th]) THEN
        ASM SET_TAC [],
        ALL_TAC] THEN
      USE_THEN "c" (MP_TAC o SPECL [← q r"e':B->bool", ← q r"e:B->bool"]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [], REWRITE_TAC [SUBSET, FORALL_IN_IMAGE]] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, INTERS_IMAGE, IN_ELIM_THM] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"f:B->B")) THEN EXISTS_TAC (← q r"f:B->B") THEN
    ASM_SIMP_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
    ASM_MESON_TAC [])

  pure { GALOIS_GROUP_COMPATIBLE_RESTRICTIONS }

/- ------------------------------------------------------------------------- -/
/- The Galois group is the inverse limit of the Galois groups of the finite  -/
/- Galois subextensions, as a group and as a space.                          -/
/- (infinite_galois.ml 928-1263)                                             -/
/- ------------------------------------------------------------------------- -/

structure IGE where
  GALOIS_GROUP_INVERSE_LIMIT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIGE [HolBase] (D : InfiniteGaloisDeps) (BIGA : IGA) (BIGC : IGC) : ExceptT String IO IGE := do
  -- @@SCOPE BEGIN
  let { PROFINITE_GROUP_GALOIS_GROUP, .. } := BIGA
  let { CONTINUOUS_MAP_GALOIS_GROUP_RESTRICTION_FINITE,
        GALOIS_GROUP_RESTRICTION_FINITE_GALOIS, .. } := BIGC
  let { profinite_group, .. } := D.qprofinitegroups
  let { FINITE_GALOIS_SUBFIELDS_ELEMENT, FINITE_GALOIS_SUBFIELDS_FINITE,
        FINITE_GALOIS_SUBFIELDS_UPPER_BOUND, GALOIS_GROUP_LOCAL, GALOIS_GROUP_PERMUTES,
        GALOIS_GROUP_RESTRICTION_HOMOMORPHISM, GALOIS_IMP_ALGEBRAIC_EXTENSION,
        GALOIS_IMP_FIELD_EXTENSION, GALOIS_IMP_NORMAL_EXTENSION,
        IN_FINITE_GALOIS_SUBFIELDS, .. } := D.qgalois
  let { CARRIER_SUBFIELD_GENERATED_SUBFIELD, field_extension, FIELD_SUBFIELD_GENERATED,
        SUBFIELD_GENERATED_SUBFIELD_GENERATED, SUBFIELD_OF_IMP_SUBSET,
        SUBFIELD_OF_SUBFIELD_GENERATED, .. } := D.qfieldtheory
  let { PERMUTES_ALT, .. } := D.qpermutations
  let { ASM_MESON_TAC, MESON_TAC, SELECT_CONV, SET_RULE, SET_TAC, .. } := D.pg.mt
  let { CONTINUOUS_IMP_HOMEOMORPHIC_MAP, CONTINUOUS_MAP_COMPONENTWISE,
        CONTINUOUS_MAP_IN_SUBTOPOLOGY, HAUSDORFF_SPACE_DISCRETE_TOPOLOGY,
        HAUSDORFF_SPACE_PRODUCT_TOPOLOGY, HAUSDORFF_SPACE_SUBTOPOLOGY,
        TOPSPACE_DISCRETE_TOPOLOGY, TOPSPACE_POINTWISE_TOPOLOGY, TOPSPACE_PRODUCT_TOPOLOGY,
        TOPSPACE_SUBTOPOLOGY, .. } := D.pg.qmetric
  let { group_epimorphism, group_homomorphism, GROUP_HOMOMORPHISM, GROUP_ISOMORPHISM,
        INVERSE_LIMIT_GROUP, .. } := D.pg.qgrouptheory
  let { permutes, PERMUTES_IN_IMAGE, PERMUTES_INJECTIVE, .. } := D.pg.qpermutations
  let { EMPTY_SUBSET, EXTENSION, EXTENSIONAL, FINITE_EMPTY, FINITE_INSERT, FINITE_INTER,
        FORALL_IN_IMAGE, FUN_EQ_THM, .. } := D.pg.mt.core1
  let { IN_ELIM_THM, IN_IMAGE, INSERT_SUBSET, INTER_SUBSET, MONO_EXISTS,
        .. } := D.pg.mt.core2
  let { cartesian_product, o_DEF, RESTRICTION, RESTRICTION_IN_CARTESIAN_PRODUCT,
        RESTRICTION_IN_EXTENSIONAL, SUBSET, SUBSET_ANTISYM_EQ, .. } := D.pg.mt.core4
  let { EXISTS_UNIQUE_THM, .. } := D.pg.mt.core5
  -- @@SCOPE END
  let lastc : thm → ExceptT String IO thm := fun th =>
    liftExcept (HolCore.Lib.last (CONJUNCTS th))

  let GALOIS_GROUP_INVERSE_LIMIT ← prove
   r"!(h:A->B) k l.
        galois_extension(k,l) h
        ==> group_isomorphism
             (galois_group(k,l) h,
              inverse_limit_group (finite_galois_subfields(k,l) h) (SUBSET)
               (\e. galois_group(k,subfield_generated l e) h)
               (\e e' f x. if x IN e then f x else x))
             (\f. RESTRICTION (finite_galois_subfields(k,l) h)
                              (\e x. if x IN e then f x else x)) /\
            homeomorphic_map
             (pointwise_topology(group_carrier(galois_group(k,l) h)),
              subtopology
               (product_topology (finite_galois_subfields(k,l) h)
                 (\e. discrete_topology
                       (group_carrier
                         (galois_group(k,subfield_generated l e) h))))
               (group_carrier
                 (inverse_limit_group (finite_galois_subfields(k,l) h)
                   (SUBSET)
                   (\e. galois_group(k,subfield_generated l e) h)
                   (\e e' f x. if x IN e then f x else x))))
             (\f. RESTRICTION (finite_galois_subfields(k,l) h)
                              (\e x. if x IN e then f x else x))"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
      MATCH_MP GALOIS_IMP_FIELD_EXTENSION) THEN
    SUBGOAL_THEN
     (← q r"!e e'. e IN finite_galois_subfields(k,l) h /\
             e' IN finite_galois_subfields(k,l) h /\ e SUBSET e'
             ==> group_homomorphism
                  (galois_group(k,subfield_generated l e') (h:A->B),
                   galois_group(k,subfield_generated l e) h)
                  (\f x. if x IN e then f x else x)")
    ASSUME_TAC THENL
     [REWRITE_TAC [IN_FINITE_GALOIS_SUBFIELDS] THEN REPEAT STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"subfield_generated l (e':B->bool)",
                        ← q r"e:B->bool"] GALOIS_GROUP_RESTRICTION_HOMOMORPHISM) THEN
      ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, SUBFIELD_OF_SUBFIELD_GENERATED,
                    SUBFIELD_GENERATED_SUBFIELD_GENERATED,
                    GALOIS_IMP_NORMAL_EXTENSION,
                    ← SET_RULE (← q r"(e:C->bool) SUBSET e' ==> e' INTER e = e")],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!e. e IN finite_galois_subfields(k,l) h
          ==> group_homomorphism
               (galois_group(k,l) (h:A->B),
                galois_group(k,subfield_generated l e) h)
               (\f x. if x IN e then f x else x)")
    (LABEL_TAC "res") THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"e:B->bool"]
                       GALOIS_GROUP_RESTRICTION_FINITE_GALOIS) THEN
      ASM_SIMP_TAC [group_epimorphism],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!e g. e IN finite_galois_subfields(k,l) (h:A->B) /\
            g IN group_carrier(galois_group(k,subfield_generated l e) h)
            ==> g permutes e")
    (LABEL_TAC "perm") THENL
     [REWRITE_TAC [IN_FINITE_GALOIS_SUBFIELDS] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o MATCH_MP GALOIS_GROUP_PERMUTES) THEN
      ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!e. e IN finite_galois_subfields(k,l) (h:A->B)
          ==> e SUBSET ring_carrier l")
    (LABEL_TAC "sub") THENL
     [SIMP_TAC [IN_FINITE_GALOIS_SUBFIELDS, SUBFIELD_OF_IMP_SUBSET],
      ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"finite_galois_subfields(k,l) (h:A->B)",
      ← q r"(SUBSET):(B->bool)->(B->bool)->bool",
      ← q r"\e. galois_group(k,subfield_generated l e) (h:A->B)",
      ← q r"\(e:B->bool) (e':B->bool) (f:B->B) x. if x IN e then f x else x"]
     INVERSE_LIMIT_GROUP) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC [], STRIP_TAC] THEN
    ABBREV_TAC
     (← q r"L = inverse_limit_group (finite_galois_subfields(k,l) h) (SUBSET)
           (\e. galois_group(k,subfield_generated l e) (h:A->B))
           (\(e:B->bool) (e':B->bool) (f:B->B) x. if x IN e then f x else x)")
    THEN
    SUBGOAL_THEN
     (← q r"!f. f IN group_carrier(galois_group(k,l) (h:A->B))
          ==> RESTRICTION (finite_galois_subfields(k,l) h)
                (\e x. if x IN e then f x else x) IN group_carrier L")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN
      ASM_REWRITE_TAC [IN_ELIM_THM, RESTRICTION_IN_CARTESIAN_PRODUCT] THEN
      CONJ_TAC THENL
       [X_GEN_TAC (← q r"e:B->bool") THEN DISCH_TAC THEN
        USE_THEN "res" (MP_TAC o SPEC (← q r"e:B->bool")) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
        REWRITE_TAC [group_homomorphism, SUBSET, FORALL_IN_IMAGE] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"f:B->B") o CONJUNCT1) THEN
        ASM_REWRITE_TAC [],
        MAP_EVERY X_GEN_TAC [← q r"e:B->bool", ← q r"e':B->bool"] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC [RESTRICTION, FUN_EQ_THM] THEN X_GEN_TAC (← q r"x:B") THEN
        ASM_CASES_TAC (← q r"(x:B) IN e") THEN ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN (← q r"(x:B) IN e'") (fun th => REWRITE_TAC [th]) THEN
        ASM SET_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!y. y IN group_carrier L
          ==> ?f. f IN group_carrier(galois_group(k,l) (h:A->B)) /\
                  RESTRICTION (finite_galois_subfields(k,l) h)
                    (\e x. if x IN e then f x else x) = y")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"y:(B->bool)->B->B") THEN
      ASM_REWRITE_TAC [IN_ELIM_THM, cartesian_product] THEN
      DISCH_THEN (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "in"))
                                 (LABEL_TAC "compat")) THEN
      SUBGOAL_THEN
       (← q r"!e e' x. e IN finite_galois_subfields(k,l) (h:A->B) /\
                 e' IN finite_galois_subfields(k,l) h /\ x IN e /\ x IN e'
                 ==> (y:(B->bool)->B->B) e x = y e' x")
      (LABEL_TAC "agree") THENL
       [REPEAT STRIP_TAC THEN
        MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"e:B->bool",
                          ← q r"e':B->bool"] FINITE_GALOIS_SUBFIELDS_UPPER_BOUND) THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"e'':B->bool") STRIP_ASSUME_TAC) THEN
        USE_THEN "compat" (MP_TAC o SPECL [← q r"e:B->bool", ← q r"e'':B->bool"]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC [], DISCH_THEN (MP_TAC o C AP_THM (← q r"x:B"))] THEN
        USE_THEN "compat" (MP_TAC o SPECL [← q r"e':B->bool", ← q r"e'':B->bool"]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC [], DISCH_THEN (MP_TAC o C AP_THM (← q r"x:B"))] THEN
        ASM_REWRITE_TAC [] THEN MESON_TAC [],
        ALL_TAC] THEN
      ABBREV_TAC
       (← q r"f = \x:B. if x IN ring_carrier l
                  then (y:(B->bool)->B->B)
                        (@e. e IN finite_galois_subfields(k,l) (h:A->B) /\
                             x IN e) x
                  else x") THEN
      SUBGOAL_THEN
       (← q r"!e x. e IN finite_galois_subfields(k,l) (h:A->B) /\ x IN e
              ==> (f:B->B) x = (y:(B->bool)->B->B) e x")
      (LABEL_TAC "f") THENL
       [REPEAT STRIP_TAC THEN EXPAND_TAC "f" THEN
        SUBGOAL_THEN (← q r"(x:B) IN ring_carrier l") (fun th => REWRITE_TAC [th]) THENL
         [USE_THEN "sub" (MP_TAC o SPEC (← q r"e:B->bool")) THEN ASM SET_TAC [],
          ALL_TAC] THEN
        USE_THEN "agree" MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
        CONV_TAC SELECT_CONV THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!x:B. ~(x IN ring_carrier l) ==> f x = x")
      (LABEL_TAC "out") THENL
       [EXPAND_TAC "f" THEN SIMP_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!e. e IN finite_galois_subfields(k,l) (h:A->B)
            ==> (y:(B->bool)->B->B) e permutes e")
      (LABEL_TAC "yperm") THENL
       [REPEAT STRIP_TAC THEN USE_THEN "perm" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC [] THEN USE_THEN "in" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))")
      ASSUME_TAC THENL
       [MATCH_MP_TAC GALOIS_GROUP_LOCAL THEN CONJ_TAC THENL
         [REWRITE_TAC [PERMUTES_ALT] THEN REPEAT CONJ_TAC THENL
           [X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN
            MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"x:B"]
                             FINITE_GALOIS_SUBFIELDS_ELEMENT) THEN
            ASM_REWRITE_TAC [] THEN
            DISCH_THEN (X_CHOOSE_THEN (← q r"e:B->bool") STRIP_ASSUME_TAC) THEN
            USE_THEN "f" (MP_TAC o SPECL [← q r"e:B->bool", ← q r"x:B"]) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN
            SUBGOAL_THEN
             (← q r"(y:(B->bool)->B->B) e permutes e /\ e SUBSET ring_carrier l")
            STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
            FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:B") o MATCH_MP PERMUTES_IN_IMAGE) THEN
            ASM SET_TAC [],
            USE_THEN "out" ACCEPT_TAC,
            X_GEN_TAC (← q r"z:B") THEN DISCH_TAC THEN
            REWRITE_TAC [EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
             [MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"z:B"]
                               FINITE_GALOIS_SUBFIELDS_ELEMENT) THEN
              ASM_REWRITE_TAC [] THEN
              DISCH_THEN (X_CHOOSE_THEN (← q r"e:B->bool") STRIP_ASSUME_TAC) THEN
              SUBGOAL_THEN (← q r"(y:(B->bool)->B->B) e permutes e") MP_TAC THENL
               [ASM_MESON_TAC [], REWRITE_TAC [PERMUTES_ALT]] THEN
              DISCH_THEN (MP_TAC o SPEC (← q r"z:B") o CONJUNCT2 o CONJUNCT2) THEN
              ASM_REWRITE_TAC [EXISTS_UNIQUE_THM] THEN
              DISCH_THEN (X_CHOOSE_THEN (← q r"x:B") STRIP_ASSUME_TAC o CONJUNCT1) THEN
              EXISTS_TAC (← q r"x:B") THEN
              SUBGOAL_THEN
               (← q r"(f:B->B) x = (y:(B->bool)->B->B) e x /\
                e SUBSET ring_carrier l")
              STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ASM SET_TAC []],
              MAP_EVERY X_GEN_TAC [← q r"x1:B", ← q r"x2:B"] THEN STRIP_TAC THEN
              MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"{x1:B,x2}"]
                               FINITE_GALOIS_SUBFIELDS_FINITE) THEN
              ASM_REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY, INSERT_SUBSET,
                               EMPTY_SUBSET] THEN
              DISCH_THEN (X_CHOOSE_THEN (← q r"e:B->bool") STRIP_ASSUME_TAC) THEN
              SUBGOAL_THEN
               (← q r"(y:(B->bool)->B->B) e permutes e /\
                (f:B->B) x1 = y e x1 /\ f x2 = y e x2")
              STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
              FIRST_ASSUM (MP_TAC o MATCH_MP PERMUTES_INJECTIVE) THEN
              DISCH_THEN (fun th => tactic_of do
                pure (ONCE_REWRITE_TAC [← GSYM th])) THEN
              ASM_MESON_TAC []]],
          X_GEN_TAC (← q r"s:B->bool") THEN DISCH_TAC THEN
          MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring",
                            ← q r"s INTER ring_carrier(l:B ring)"]
                           FINITE_GALOIS_SUBFIELDS_FINITE) THEN
          ASM_SIMP_TAC [FINITE_INTER, INTER_SUBSET] THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"e:B->bool") STRIP_ASSUME_TAC) THEN
          MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"e:B->bool"]
                           GALOIS_GROUP_RESTRICTION_FINITE_GALOIS) THEN
          ASM_REWRITE_TAC [group_epimorphism] THEN
          DISCH_THEN (MP_TAC o CONJUNCT2 o CONJUNCT1) THEN
          REWRITE_TAC [EXTENSION, IN_IMAGE] THEN
          DISCH_THEN (MP_TAC o SPEC (← q r"(y:(B->bool)->B->B) e")) THEN
          USE_THEN "in" (fun th => ASM_SIMP_TAC [th]) THEN
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"g:B->B") THEN
          STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
          X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN
          ASM_CASES_TAC (← q r"(x:B) IN ring_carrier l") THENL
           [SUBGOAL_THEN (← q r"(x:B) IN e") ASSUME_TAC THENL
             [ASM SET_TAC [], ALL_TAC] THEN
            USE_THEN "f" (MP_TAC o SPECL [← q r"e:B->bool", ← q r"x:B"]) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN
            ASM_REWRITE_TAC [],
            SUBGOAL_THEN (← q r"(f:B->B) x = x") SUBST1_TAC THENL
             [ASM_MESON_TAC [], ALL_TAC] THEN
            MP_TAC (← ISPECL [← q r"h:A->B", ← q r"g:B->B", ← q r"k:A ring", ← q r"l:B ring"]
                             GALOIS_GROUP_PERMUTES) THEN
            ASM_REWRITE_TAC [] THEN
            DISCH_THEN (MP_TAC o SPEC (← q r"x:B") o CONJUNCT1 o
              GEN_REWRITE_RULE I [permutes]) THEN
            ASM_REWRITE_TAC []]],
        ALL_TAC] THEN
      EXISTS_TAC (← q r"f:B->B") THEN ASM_REWRITE_TAC [] THEN
      GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC (← q r"e:B->bool") THEN
      REWRITE_TAC [RESTRICTION] THEN COND_CASES_TAC THENL
       [REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"x:B") THEN
        COND_CASES_TAC THENL
         [USE_THEN "f" MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
          SUBGOAL_THEN (← q r"(y:(B->bool)->B->B) e permutes e") MP_TAC THENL
           [ASM_MESON_TAC [], REWRITE_TAC [permutes]] THEN
          DISCH_THEN (MP_TAC o SPEC (← q r"x:B") o CONJUNCT1) THEN
          ASM_REWRITE_TAC [] THEN MESON_TAC []],
        UNDISCH_TAC
         (← q r"EXTENSIONAL (finite_galois_subfields(k,l) (h:A->B))
                      (y:(B->bool)->B->B)") THEN
        REWRITE_TAC [EXTENSIONAL, IN_ELIM_THM] THEN ASM_MESON_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"group_carrier L SUBSET
      topspace(product_topology (finite_galois_subfields(k,l) h)
       (\e. discrete_topology
             (group_carrier(galois_group(k,subfield_generated l e)
                             (h:A->B)))))")
    ASSUME_TAC THENL
     [REWRITE_TAC [TOPSPACE_PRODUCT_TOPOLOGY, o_DEF,
                   TOPSPACE_DISCRETE_TOPOLOGY] THEN
      ASM_REWRITE_TAC [SUBSET, cartesian_product, IN_ELIM_THM] THEN
      MESON_TAC [],
      ALL_TAC] THEN
    -- `K ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `..`)`:
    -- the quotation is parsed only when `is_eq` holds, as `&&`.
    FIRST_X_ASSUM (fun th => tactic_of do
      let ok ← if is_eq (concl th) then do
          let z ← q r"group_carrier(L:((B->bool)->B->B) group)"
          pure (match lhs (concl th) with | .ok r => r == z | .error _ => false)
        else pure false
      let _ ← liftExcept (check (fun _ => ok) th)
      pure ALL_TAC) THEN
    SUBGOAL_THEN
     (← q r"!f g. f IN group_carrier(galois_group(k,l) (h:A->B)) /\
            g IN group_carrier(galois_group(k,l) h) /\
            RESTRICTION (finite_galois_subfields(k,l) h)
              (\e x. if x IN e then f x else x) =
            RESTRICTION (finite_galois_subfields(k,l) h)
              (\e x. if x IN e then g x else x)
            ==> f = g")
    ASSUME_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q r"f:B->B", ← q r"g:B->B"] THEN STRIP_TAC THEN
      GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC (← q r"x:B") THEN
      ASM_CASES_TAC (← q r"(x:B) IN ring_carrier l") THENL
       [MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"x:B"]
                        FINITE_GALOIS_SUBFIELDS_ELEMENT) THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"e:B->bool") STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM (MP_TAC o C AP_THM (← q r"x:B") o C AP_THM (← q r"e:B->bool") o
          check (fun th => is_eq (concl th))) THEN
        ASM_REWRITE_TAC [RESTRICTION],
        SUBGOAL_THEN (← q r"(f:B->B) x = x /\ (g:B->B) x = x")
         (fun th => REWRITE_TAC [th]) THEN
        CONJ_TAC THENL
         [MP_TAC (← ISPECL [← q r"h:A->B", ← q r"f:B->B", ← q r"k:A ring", ← q r"l:B ring"]
                          GALOIS_GROUP_PERMUTES),
          MP_TAC (← ISPECL [← q r"h:A->B", ← q r"g:B->B", ← q r"k:A ring", ← q r"l:B ring"]
                          GALOIS_GROUP_PERMUTES)] THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"x:B") o CONJUNCT1 o
          GEN_REWRITE_RULE I [permutes]) THEN
        ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
     [REWRITE_TAC [GROUP_ISOMORPHISM] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC [GROUP_HOMOMORPHISM, SUBSET, FORALL_IN_IMAGE] THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
        MAP_EVERY X_GEN_TAC [← q r"f:B->B", ← q r"g:B->B"] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
        X_GEN_TAC (← q r"e:B->bool") THEN REWRITE_TAC [RESTRICTION] THEN
        COND_CASES_TAC THEN REWRITE_TAC [] THEN
        USE_THEN "res" (MP_TAC o SPEC (← q r"e:B->bool")) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC [], REWRITE_TAC [group_homomorphism]] THEN
        DISCH_THEN (MP_TAC o SPECL [← q r"f:B->B", ← q r"g:B->B"] o lastc) THEN
        ASM_REWRITE_TAC [],
        REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, SUBSET, FORALL_IN_IMAGE] THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
        REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC [],
        ASM_MESON_TAC []],
      DISCH_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_IMP_HOMEOMORPHIC_MAP THEN REPEAT CONJ_TAC THENL
     [MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"]
                      PROFINITE_GROUP_GALOIS_GROUP) THEN
      ASM_SIMP_TAC [GALOIS_IMP_ALGEBRAIC_EXTENSION, profinite_group],
      MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN
      REWRITE_TAC [HAUSDORFF_SPACE_PRODUCT_TOPOLOGY,
                   HAUSDORFF_SPACE_DISCRETE_TOPOLOGY],
      REWRITE_TAC [CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [REWRITE_TAC [CONTINUOUS_MAP_COMPONENTWISE] THEN
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, RESTRICTION_IN_EXTENSIONAL] THEN
        X_GEN_TAC (← q r"e:B->bool") THEN DISCH_TAC THEN
        ASM_REWRITE_TAC [RESTRICTION] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_GALOIS_GROUP_RESTRICTION_FINITE THEN
        ASM_SIMP_TAC [GALOIS_IMP_FIELD_EXTENSION],
        REWRITE_TAC [TOPSPACE_POINTWISE_TOPOLOGY] THEN
        ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE]],
      REWRITE_TAC [TOPSPACE_SUBTOPOLOGY,
                   TOPSPACE_POINTWISE_TOPOLOGY] THEN
      ASM_SIMP_TAC [← SET_RULE (← q r"(s:C->bool) SUBSET t ==> t INTER s = s")] THEN
      REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, SUBSET, FORALL_IN_IMAGE] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
      REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC [],
      REWRITE_TAC [TOPSPACE_POINTWISE_TOPOLOGY] THEN
      ASM_MESON_TAC []])

  pure { GALOIS_GROUP_INVERSE_LIMIT }

/- ------------------------------------------------------------------------- -/
/- Algebraic extensions of finite fields: the Frobenius map generates a      -/
/- dense subgroup of the Galois group.  (infinite_galois.ml 1278-1433)       -/
/- ------------------------------------------------------------------------- -/

structure IGF where
  GALOIS_GROUP_FROBENIUS_DENSE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupIGF [HolBase] (D : InfiniteGaloisDeps) (BIGA : IGA) : ExceptT String IO IGF := do
  -- @@SCOPE BEGIN
  let { CLOSURE_OF_GALOIS_GROUP_SUBGROUP, .. } := BIGA
  let { FIXED_FIELD_SUBGROUP_GENERATED, GALOIS_GROUP_EQ_IMAGE, IN_FIXED_FIELD,
        IN_GALOIS_GROUP, .. } := D.qgalois
  let { algebraic_extension, ALGEBRAIC_IMP_FIELD_EXTENSION,
        CARRIER_SUBFIELD_GENERATED_SUBFIELD, CARRIER_SUBFIELD_OF, field_extension,
        FINITE_FINITE_FIELD_EXTENSION, RING_CARRIER_SUBFIELD_GENERATED_SUBSET,
        RING_ENDOMORPHISM_POW_CARD, RING_POW_FIXPOINTS_BOUND, RING_POW_SUBFIELD_GENERATED,
        SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC, SUBFIELD_OF_MONOMORPHIC_IMAGE,
        .. } := D.qfieldtheory
  let { SUBGROUP_SUBGROUP_GENERATED, .. } := D.qgrouptheory
  let { FIELD_HOMOMORPHISM_IMP_MONOMORPHISM, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_NONTRIVIAL,
        FINITE_FIELD_CARD_GE_2, RING_1, ring_automorphism, ring_endomorphism,
        RING_HOMOMORPHISM_EQ, RING_HOMOMORPHISM_IN_CARRIER, RING_ISOMORPHISM,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MONOMORPHISM_INJECTIVE_EQ, RING_POW,
        RING_POW_ONE, .. } := D.qringtheory
  let { PERMUTES_ALT, .. } := D.qpermutations
  let { CARD_IMAGE_INJ, CARD_SUBSET, CARD_SUBSET_EQ, EXP_1, IMAGE_I, LE_ANTISYM,
        .. } := D.qsession
  let { ASM_MESON_TAC, SET_TAC, .. } := D.pg.mt
  let { SURJECTIVE_IFF_INJECTIVE, .. } := D.pg.qsession
  let { EXTENSION, FORALL_IN_IMAGE, .. } := D.pg.mt.core1
  let { IN_ELIM_THM, IN_SING, LE_REFL, LE_TRANS, MONO_EXISTS, .. } := D.pg.mt.core2
  let { SING_SUBSET, SUBSET, .. } := D.pg.mt.core4
  let { EXISTS_UNIQUE_THM, FORALL_UNWIND_THM2, .. } := D.pg.mt.core5
  -- @@SCOPE END

  let GALOIS_GROUP_FROBENIUS_DENSE ← prove
   r"!(h:A->B) k l.
        algebraic_extension(k,l) h /\ FINITE(ring_carrier k)
        ==> (\x. if x IN ring_carrier l
                 then ring_pow l x (CARD(ring_carrier k)) else x)
            IN group_carrier(galois_group(k,l) h) /\
            (pointwise_topology(group_carrier(galois_group(k,l) h)))
            closure_of
            group_carrier
             (subgroup_generated (galois_group(k,l) h)
               {\x. if x IN ring_carrier l
                    then ring_pow l x (CARD(ring_carrier k)) else x}) =
            group_carrier(galois_group(k,l) h)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    MP_TAC (← ISPECL [← q r"k:A ring", ← q r"l:B ring", ← q r"h:A->B", ← q r"1"]
      RING_ENDOMORPHISM_POW_CARD) THEN
    ASM_REWRITE_TAC [EXP_1, ring_endomorphism] THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"2 <= CARD(ring_carrier(k:A ring))") ASSUME_TAC THENL
     [ASM_SIMP_TAC [FINITE_FIELD_CARD_GE_2], ALL_TAC] THEN
    ABBREV_TAC (← q r"q = CARD(ring_carrier(k:A ring))") THEN
    ABBREV_TAC
     (← q r"f = \x:B. if x IN ring_carrier l then ring_pow l x q else x") THEN
    SUBGOAL_THEN
     (← q r"(!x:B. x IN ring_carrier l ==> f x = ring_pow l x q) /\
      (!x:B. ~(x IN ring_carrier l) ==> f x = x)")
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "f" THEN SIMP_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"ring_monomorphism(l:B ring,l) f") ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"l:B ring", ← q r"l:B ring", ← q r"f:B->B"]
        FIELD_HOMOMORPHISM_IMP_MONOMORPHISM) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_HOMOMORPHISM_EQ THEN
        EXISTS_TAC (← q r"\x:B. ring_pow l x q") THEN ASM_SIMP_TAC [],
        ALL_TAC] THEN
      MATCH_MP_TAC (← TAUT (← q r"~p ==> p \/ q ==> q")) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"ring_1 l:B")) THEN
      ASM_SIMP_TAC [RING_1, RING_POW_ONE] THEN
      ASM_MESON_TAC [FIELD_NONTRIVIAL],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!y:B. y IN ring_carrier l ==> ?x. x IN ring_carrier l /\ f x = y")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"algebraic_over(k,l) (h:A->B) y") ASSUME_TAC THENL
       [ASM_MESON_TAC [algebraic_extension], ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"y:B"]
        SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC) THEN
      ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
      ABBREV_TAC
       (← q r"s = ring_carrier
             (subfield_generated l
               (y INSERT IMAGE (h:A->B) (ring_carrier k)))") THEN
      SUBGOAL_THEN (← q r"FINITE(s:B->bool) /\ s SUBSET ring_carrier l")
      STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "s" THEN
        REWRITE_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET] THEN
        MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring",
                          ← q r"subfield_generated l (y INSERT IMAGE (h:A->B)
                                               (ring_carrier k))"]
          FINITE_FINITE_FIELD_EXTENSION) THEN
        ASM_SIMP_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"IMAGE (f:B->B) s SUBSET s") ASSUME_TAC THENL
       [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"x:B") THEN
        DISCH_TAC THEN
        SUBGOAL_THEN (← q r"(x:B) IN ring_carrier l") ASSUME_TAC THENL
         [ASM SET_TAC [], ASM_SIMP_TAC []] THEN
        MP_TAC (← ISPECL
         [← q r"subfield_generated l (y INSERT IMAGE (h:A->B) (ring_carrier k))",
          ← q r"x:B", ← q r"q:num"] RING_POW) THEN
        REWRITE_TAC [RING_POW_SUBFIELD_GENERATED] THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"s:B->bool", ← q r"f:B->B"] SURJECTIVE_IFF_INJECTIVE) THEN
      ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC (← TAUT (← q r"q /\ (p ==> r) ==> (p <=> q) ==> r")) THEN
      CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN
        MP_TAC (← ISPECL [← q r"l:B ring", ← q r"l:B ring", ← q r"f:B->B", ← q r"x:B", ← q r"y':B"]
          RING_MONOMORPHISM_INJECTIVE_EQ) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC [],
        DISCH_THEN (MP_TAC o SPEC (← q r"y:B")) THEN
        ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))")
    ASSUME_TAC THENL
     [REWRITE_TAC [IN_GALOIS_GROUP] THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
      SUBGOAL_THEN (← q r"!x:B. x IN ring_carrier l ==> f x IN ring_carrier l")
      ASSUME_TAC THENL
       [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC [PERMUTES_ALT] THEN ASM_REWRITE_TAC [] THEN
        X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN REWRITE_TAC [EXISTS_UNIQUE_THM] THEN
        CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        ASM_MESON_TAC [RING_MONOMORPHISM_INJECTIVE_EQ],
        REWRITE_TAC [ring_automorphism, RING_ISOMORPHISM] THEN
        ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
         [ASM SET_TAC [], ASM_MESON_TAC [RING_MONOMORPHISM_INJECTIVE_EQ]],
        X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN
        SUBGOAL_THEN (← q r"(h:A->B) a IN ring_carrier l") ASSUME_TAC THENL
         [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ASM_SIMP_TAC []]],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN
     (← q r"fixed_field l
       (group_carrier(subgroup_generated (galois_group(k,l) h) {f})) =
      IMAGE (h:A->B) (ring_carrier k)")
    ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"{f:B->B}"]
        FIXED_FIELD_SUBGROUP_GENERATED) THEN
      ASM_REWRITE_TAC [SING_SUBSET] THEN DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN
       (← q r"fixed_field l {f:B->B} =
        {x | x IN ring_carrier l /\ ring_pow l x q = x}")
      SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_FIXED_FIELD, IN_SING, FORALL_UNWIND_THM2,
                     IN_ELIM_THM] THEN
        X_GEN_TAC (← q r"x:B") THEN
        ASM_CASES_TAC (← q r"(x:B) IN ring_carrier l") THEN ASM_SIMP_TAC [],
        ALL_TAC] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
      MP_TAC (← ISPECL [← q r"l:B ring", ← q r"q:num"] RING_POW_FIXPOINTS_BOUND) THEN
      ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"CARD(IMAGE (h:A->B) (ring_carrier k)) = q") ASSUME_TAC THENL
       [EXPAND_TAC "q" THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
        ASM_REWRITE_TAC [] THEN
        ASM_MESON_TAC [RING_MONOMORPHISM_INJECTIVE_EQ],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"IMAGE (h:A->B) (ring_carrier k) SUBSET
        {x | x IN ring_carrier l /\ ring_pow l x q = x}")
      ASSUME_TAC THENL
       [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
        ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER],
        ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [← GSYM LE_ANTISYM] THEN ASM_REWRITE_TAC [] THEN
      TRANS_TAC LE_TRANS (← q r"CARD(IMAGE (h:A->B) (ring_carrier k))") THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC [LE_REFL],
        MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring",
                      ← q r"group_carrier(subgroup_generated
                         (galois_group(k,l) (h:A->B)) {f:B->B})"]
      CLOSURE_OF_GALOIS_GROUP_SUBGROUP) THEN
    ASM_REWRITE_TAC [SUBGROUP_SUBGROUP_GENERATED] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC GALOIS_GROUP_EQ_IMAGE THEN
    REWRITE_TAC [IMAGE_I] THEN
    MATCH_MP_TAC CARRIER_SUBFIELD_GENERATED_SUBFIELD THEN
    MATCH_MP_TAC SUBFIELD_OF_MONOMORPHIC_IMAGE THEN
    EXISTS_TAC (← q r"k:A ring") THEN ASM_REWRITE_TAC [CARRIER_SUBFIELD_OF])

  pure { GALOIS_GROUP_FROBENIUS_DENSE }
end HolMultiLib.InfiniteGalois
