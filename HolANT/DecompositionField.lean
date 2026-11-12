/- ========================================================================= -/
/- ANT: Complements to the Hilbert theory of ANT/decomposition.ml ...      -/
/- ========================================================================= -/
/- File: HolANT/DecompositionField.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/decomposition_field.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antdecompositionfielddiff; the rest is by hand.  Its `needs` closure is
  Library/frag.ml, Library/wo.ml, Library/card.ml, Library/prime.ml, Library/grouptheory.ml, Library/matroids.ml, Library/binomial.ml, Library/iter.ml, Library/pocklington.ml, Library/ringtheory.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/ideal_arith.ml, ANT/decomposition.ml, Library/isum.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/nf_valuation.ml, ANT/prime_split.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/relative_degree.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/splitting_types.ml, ANT/nf_decomposition.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.DecompositionField fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left; where a proof applies rules that print or use
  counters (MESON, ARITH_RULE, ...) they are bound first, in OCaml's order.
-/

import HolANT.Prelude
import HolLibrary.Frag
import HolLibrary.Wo
import HolLibrary.Card
import HolLibrary.Prime
import HolLibrary.GroupTheory
import HolLibrary.Matroids
import HolLibrary.Binomial
import HolLibrary.Iter
import HolLibrary.Pocklington
import HolLibrary.RingTheory
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolLibrary.FieldTheory
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolANT.IdealArith
import HolANT.Decomposition
import HolLibrary.Isum
import HolLibrary.Products
import HolANT.Algmisc
import HolANT.Integral
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolANT.RingOfIntegers
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.NormIndex
import HolANT.Classgroup
import HolANT.NfValuation
import HolANT.PrimeSplit
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.RelativeDegree
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.SplittingTypes
import HolANT.NfDecomposition

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.IdealArith
open HolANT.Decomposition
open HolANT.Algmisc
open HolANT.Integral
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.RingOfIntegers
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.NormIndex
open HolANT.Classgroup
open HolANT.NfValuation
open HolANT.PrimeSplit
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.RelativeDegree
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.SplittingTypes
open HolANT.NfDecomposition

namespace HolANT.DecompositionField

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CARD_EQ_0 CARD_IMAGE_SUBGROUP_KERNEL CARD_SING CARD_SUBSET_EQ
   CARRIER_SUBFIELD_GENERATED_SUBFIELD CARRIER_SUBGROUP_GENERATED_BY_SING
   CONJ_ASSOC DECOMPOSITION_GROUP DECOMPOSITION_GROUP_CONGRUENT_EQ
   DECOMPOSITION_GROUP_CONJUGATE DECOMPOSITION_GROUP_INTERMEDIATE
   DECOMPOSITION_GROUP_POW_CONGRUENCE DECOMPOSITION_GROUP_RING_OF_INTEGERS
   EQ_MULT_LCANCEL EQ_MULT_RCANCEL EQ_TRANS EXISTS_IN_GSPEC EXISTS_UNIQUE_THM
   EXTENSION EXTENSION_DEGREE_TOWER_LAW FIELD_IMP_NONTRIVIAL_RING
   FIELD_RING_HOMOMORPHISM_MONOMORPHISM FIELD_SUBFIELD_GENERATED
   FINITE_DECOMPOSITION_INERTIA_GROUPS FINITE_GALOIS_GROUP FINITE_INTER
   FIXED_FIELD_ANTIMONO FIXED_FIELD_SUBGROUP_GENERATED FORALL_AND_THM
   FORALL_IN_GSPEC FORALL_IN_IMAGE FORALL_UNWIND_THM2
   FROBENIUS_ELEMENT_IN_DECOMPOSITION_GROUP FUN_EQ_THM
   GALOIS_CORRESPONDENCE_DEGREE GALOIS_EXTENSION_EQ_CARD
   GALOIS_EXTENSION_SUBFIELD_GENERATED GALOIS_GROUP GALOIS_GROUP_FIXED_FIELD
   GALOIS_GROUP_FIXES GALOIS_GROUP_I GALOIS_GROUP_IMAGE_NORMAL_INTERMEDIATE
   GALOIS_GROUP_INTERMEDIATE_SUBGROUP_GENERATED GALOIS_GROUP_INVERSE
   GALOIS_GROUP_IN_CARRIER GALOIS_GROUP_PERMUTES GALOIS_GROUP_PRIME_IDEAL_IMAGE
   GALOIS_GROUP_RESTRICTION GALOIS_GROUP_RING_OF_INTEGERS
   GALOIS_IMP_FIELD_EXTENSION GALOIS_IMP_NORMAL_EXTENSION
   GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET GROUP_ID GROUP_NPOW GROUP_POW
   GROUP_POW_MUL GROUP_POW_SUBGROUP_GENERATED GROUP_ZPOW_EQ GROUP_ZPOW_MUL
   IDEAL_NORM_RESIDUE_DEGREE IDEAL_NORM_RESIDUE_IMAGE IMAGE_EQ IMAGE_I IMAGE_ID
   IMAGE_INTER_INJ IMP_CONJ INERTIA_GROUP INERTIA_GROUP_CONJUGATE
   INERTIA_GROUP_INTERMEDIATE INERTIA_GROUP_SUBGROUP_OF_DECOMPOSITION_GROUP
   INERT_RESIDUE_DEGREE INTER_IDEMPOT INTER_SUBSET INT_OF_NUM_MUL IN_ELIM_THM
   IN_FIXED_FIELD IN_GALOIS_GROUP IN_GALOIS_GROUP_SUBFIELD_GENERATED IN_IMAGE
   IN_INTER IN_RING_IDEAL_0 IN_RING_IDEAL_SUB IN_SING IN_UNION IN_UNIONS IN_UNIV
   I_O_ID I_THM : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (LEFT_IMP_EXISTS_THM MEMBER_NOT_EMPTY MULT_AC MULT_ASSOC MULT_CLAUSES
   MULT_EQ_0 MULT_EQ_1 NORMAL_IMP_ALGEBRAIC_EXTENSION
   NUMBER_FIELD_DECOMPOSITION_GROUP NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS
   NUMBER_FIELD_FROBENIUS_ELEMENT NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE
   NUMBER_FIELD_HOMOMORPHIC_PREIMAGE NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_PRIME_IDEALS_ABOVE NUMBER_FIELD_PRIME_IDEAL_ABOVE
   NUMBER_FIELD_RAMIFICATION_INDEX_CONJUGATE
   NUMBER_FIELD_RAMIFICATION_INDEX_TOWER
   NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS NUMBER_FIELD_RESIDUE_DEGREE_TOWER
   NUMBER_FIELD_SUBFIELD_GENERATED NUMBER_FIELD_TOWER_LAW
   NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED
   NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP PERMUTES_IMAGE PERMUTES_INJECTIVE
   PERMUTES_INVERSES PERMUTES_INVERSES_o PERMUTES_INVERSE_INVERSE
   PRIME_IDEAL_HOMOMORPHIC_PREIMAGE PRIME_IDEAL_IMP_SUBSET PRIME_IMP_RING_IDEAL
   PRIME_SUBFIELD_MINIMAL PRIME_SUBFIELD_SUBFIELD_GENERATED RIGHT_AND_EXISTS_THM
   RIGHT_FORALL_IMP_THM RING_HOMOMORPHISM_INTO_SUBRING
   RING_HOMOMORPHISM_RING_OF_INTEGERS RING_HOMOMORPHISM_SUBFIELD_INCLUSION
   RING_MONOMORPHISM_EQ_0 RING_MONOMORPHISM_IMP_HOMOMORPHISM
   RING_MONOMORPHISM_INTO_SUBRING RING_OF_INTEGERS
   RING_OF_INTEGERS_PRIME_IDEAL_BELOW RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION
   RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL RING_OF_INTEGERS_SUBFIELD_GENERATED
   RING_OF_INTEGERS_SUBRING RING_OF_INTEGERS_SUBSET
   RING_OF_NUM_SUBFIELD_GENERATED RING_POW RING_POW_SUBFIELD_GENERATED RING_SUB
   RING_SUB_SUBFIELD_GENERATED SEPARABLE_EXTENSION_CHAR0 SING_SUBSET
   SUBFIELD_GENERATED SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED
   SUBFIELD_GENERATED_INC SUBFIELD_SUBFIELD_GENERATED
   SUBGROUP_SUBGROUP_GENERATED SUBRING_GENERATED_BY_SUBFIELD_GENERATED SUBSET
   SUBSET_TRANS SWAP_FORALL_THM TOTALLY_RAMIFIED_RAMIFICATION_INDEX
   TOTALLY_SPLIT_CARD UNIONS_SUBSET UNION_SUBSET UNWIND_THM2 abelian_group
   decomposition_group divides field_extension galois_extension
   group_epimorphism group_homomorphism group_pow group_zpow inertia_group
   num_divides number_field o_ASSOC o_THM subgroup_of totally_split
   weakly_unramified : thm)
  deriving Inhabited

/-- What decomposition_field.ml uses from Session besides theorems. -/
structure DecompositionFieldDeps where
  new_definition : String → ExceptT String IO thm
  define : String → ExceptT String IO thm
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  new_recursive_definition : thm → String → ExceptT String IO thm
  LIST_INDUCT_TAC : tactic
  ASM_ARITH_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  METIS_TAC : List thm → tactic
  ASM_METIS_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  TAUT : term → ExceptT String IO thm
  ITAUT : term → ExceptT String IO thm
  REAL_ARITH : term → ExceptT String IO thm
  REAL_FIELD : term → ExceptT String IO thm
  REAL_ARITH_TAC : tactic
  ASM_REAL_ARITH_TAC : tactic
  INDUCT_TAC : tactic
  INT_ARITH : term → ExceptT String IO thm
  INT_ARITH_TAC : tactic
  ASM_INT_ARITH_TAC : tactic
  INTEGER_RULE : term → ExceptT String IO thm  -- ints.ml's INTEGER_RULE
  INTEGER_TAC : tactic
  NUMBER_RULE : ioconv  -- ints.ml's NUMBER_RULE
  NUM_REDUCE_CONV : ioconv
  INT_REDUCE_CONV : ioconv
  INT_RED_CONV : ioconv
  INT_REM_DOWN_CONV : ioconv
  HAS_SIZE_CONV : ioconv  -- card.ml's HAS_SIZE_CONV
  let_CONV : ioconv
  num_CONV : ioconv
  mk_numeral : Rat → Except String term
  PRIME_CONV : term → ExceptT String IO thm  -- pocklington.ml's PRIME_CONV
  PRIME_RULE : List String → term → ExceptT String IO thm  -- pocklington.ml's PRIME_RULE
  RING_RULE : term → ExceptT String IO thm  -- ringtheory.ml's RING_RULE
  INTEGRAL_DOMAIN_RULE : term → ExceptT String IO thm
  FIELD_TAC : tactic  -- ringtheory.ml's FIELD_TAC
  RING_CARRIER_TAC : tactic
  RING_TAC : tactic
  RING_PULL_DIV_TAC : tactic
  LET_TAC : tactic
  GROUP_RULE : term → ExceptT String IO thm  -- grouptheory.ml's GROUP_RULE
  basic_ss : List thm → IO (Except String HolCore.Simp.simpset)
  INTEGER_MOD_RING_RED_CONV : ioconv
  NUM_SUB_CONV : ioconv
  REAL_RAT_REDUCE_CONV : ioconv
  NUM_EQ_CONV : ioconv
  NUM_DIV_CONV : ioconv
  EXP_MOD_CONV : ioconv
  EXPAND_CASES_CONV : ioconv
  DIVIDES_CONV : ioconv  -- prime.ml's DIVIDES_CONV
  COPRIME_CONV : ioconv
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



/- ---------------------------------------------------------------------- -/
/- decomposition_field.ml phrases from line 133 to 625                    -/
/- ---------------------------------------------------------------------- -/

structure DecompositionField01 where
  -- @@FIELDS
  NUMBER_FIELD_INTERMEDIATE_FIELD : thm
  NUMBER_FIELD_GALOIS_INTERMEDIATE : thm
  NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE : thm
  NUMBER_FIELD_PRIME_IDEALS_INTERMEDIATE : thm
  NUMBER_FIELD_SUBFIELD_PRIME_IDEALS_ABOVE : thm
  NUMBER_FIELD_DECOMPOSITION_GROUP_INTERMEDIATE : thm
  NUMBER_FIELD_INTERMEDIATE_SPLITTING : thm
  NUMBER_FIELD_INTERMEDIATE_SPLITTING_TYPES : thm
  NUMBER_FIELD_GENERATED_SPLITTING_TYPES : thm
  NUMBER_FIELD_GALOIS_UNRAMIFIED_MONO : thm
  NUMBER_FIELD_GALOIS_SPLITTING_TYPES : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDecompositionField01 [HolBase] (D : DecompositionFieldDeps) :
    ExceptT String IO DecompositionField01 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, TAUT, .. } := D
  let { CARD_EQ_0, CARD_SING, CARD_SUBSET_EQ, CARRIER_SUBFIELD_GENERATED_SUBFIELD,
        CONJ_ASSOC, DECOMPOSITION_GROUP, DECOMPOSITION_GROUP_INTERMEDIATE,
        EQ_MULT_LCANCEL, EXTENSION, FIELD_IMP_NONTRIVIAL_RING,
        FIELD_RING_HOMOMORPHISM_MONOMORPHISM, FIELD_SUBFIELD_GENERATED,
        FINITE_DECOMPOSITION_INERTIA_GROUPS, FINITE_GALOIS_GROUP, FORALL_UNWIND_THM2,
        FUN_EQ_THM, GALOIS_EXTENSION_EQ_CARD, GALOIS_EXTENSION_SUBFIELD_GENERATED,
        GALOIS_GROUP_RING_OF_INTEGERS, GALOIS_IMP_FIELD_EXTENSION,
        GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET, GROUP_ID, IMAGE_I, IMP_CONJ,
        INERTIA_GROUP, INERTIA_GROUP_INTERMEDIATE, INERT_RESIDUE_DEGREE, INTER_SUBSET,
        IN_ELIM_THM, IN_GALOIS_GROUP, IN_GALOIS_GROUP_SUBFIELD_GENERATED,
        IN_RING_IDEAL_0, IN_SING, I_O_ID, I_THM, .. } := D.core1
  let { LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY, MULT_AC, MULT_ASSOC, MULT_CLAUSES,
        MULT_EQ_0, MULT_EQ_1, NORMAL_IMP_ALGEBRAIC_EXTENSION,
        NUMBER_FIELD_DECOMPOSITION_GROUP, NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE,
        NUMBER_FIELD_HOMOMORPHIC_PREIMAGE, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_PRIME_IDEALS_ABOVE, NUMBER_FIELD_PRIME_IDEAL_ABOVE,
        NUMBER_FIELD_RAMIFICATION_INDEX_CONJUGATE,
        NUMBER_FIELD_RAMIFICATION_INDEX_TOWER,
        NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS, NUMBER_FIELD_RESIDUE_DEGREE_TOWER,
        NUMBER_FIELD_SUBFIELD_GENERATED, NUMBER_FIELD_TOWER_LAW,
        NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED, PRIME_IDEAL_HOMOMORPHIC_PREIMAGE,
        PRIME_IDEAL_IMP_SUBSET, PRIME_IMP_RING_IDEAL, PRIME_SUBFIELD_MINIMAL,
        PRIME_SUBFIELD_SUBFIELD_GENERATED, RIGHT_AND_EXISTS_THM, RIGHT_FORALL_IMP_THM,
        RING_HOMOMORPHISM_RING_OF_INTEGERS, RING_HOMOMORPHISM_SUBFIELD_INCLUSION,
        RING_MONOMORPHISM_EQ_0, RING_MONOMORPHISM_IMP_HOMOMORPHISM,
        RING_MONOMORPHISM_INTO_SUBRING, RING_OF_INTEGERS,
        RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION,
        RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL, RING_OF_INTEGERS_SUBFIELD_GENERATED,
        RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET,
        RING_OF_NUM_SUBFIELD_GENERATED, SEPARABLE_EXTENSION_CHAR0, SING_SUBSET,
        SUBFIELD_GENERATED, SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED,
        SUBFIELD_GENERATED_INC, SUBFIELD_SUBFIELD_GENERATED,
        SUBRING_GENERATED_BY_SUBFIELD_GENERATED, SUBSET, SUBSET_TRANS, SWAP_FORALL_THM,
        TOTALLY_RAMIFIED_RAMIFICATION_INDEX, TOTALLY_SPLIT_CARD, UNWIND_THM2,
        decomposition_group, field_extension, galois_extension, inertia_group,
        number_field, totally_split, weakly_unramified, .. } := D.core2
  -- @@SCOPE END

  let NUMBER_FIELD_INTERMEDIATE_FIELD ← prove
    r"!(h:A->B) k l s.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s
        ==> field(subfield_generated l s) /\
            ring_carrier(subfield_generated l s) = s /\
            number_field(subfield_generated l s) /\
            ring_monomorphism(k,subfield_generated l s) h /\
            ring_monomorphism(subfield_generated l s,l) I /\
            ring_homomorphism(k,subfield_generated l s) h /\
            ring_homomorphism(subfield_generated l s,l) I /\
            ring_carrier(ring_of_integers(subfield_generated l s)) =
            ring_carrier(ring_of_integers l) INTER s"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"field(subfield_generated l (s:B->bool)) /\
    ring_carrier(subfield_generated l s) = s /\
    ring_homomorphism(subfield_generated l s,l) (I:B->B)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, CARRIER_SUBFIELD_GENERATED_SUBFIELD, RING_HOMOMORPHISM_SUBFIELD_INCLUSION], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_monomorphism(k:A ring,l:B ring) h") ASSUME_TAC THENL [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_monomorphism(k,subfield_generated l s) (h:A->B)") ASSUME_TAC THENL [ONCE_REWRITE_TAC [(← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED)] THEN MATCH_MP_TAC RING_MONOMORPHISM_INTO_SUBRING THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_HOMOMORPHIC_PREIMAGE THEN MAP_EVERY EXISTS_TAC [(← q r"l:B ring"), (← q r"I:B->B")] THEN ASM_REWRITE_TAC [], MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING], ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBFIELD_GENERATED]])

  let NUMBER_FIELD_GALOIS_INTERMEDIATE ← prove
    r"!(h:A->B) k l s.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
        normal_extension(k,subfield_generated l s) h
        ==> galois_extension(k,subfield_generated l s) h"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [galois_extension] THEN MATCH_MP_TAC SEPARABLE_EXTENSION_CHAR0 THEN ASM_SIMP_TAC [NORMAL_IMP_ALGEBRAIC_EXTENSION] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_SIMP_TAC [number_field])

  let NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(z:A) IN s ==> ~(s = {z}) ==> ?a. a IN s /\ ~(a = z)")
    let r2 ← TAUT (← q r"p /\ (p ==> q) /\ r /\ s ==> p /\ q /\ r /\ s")
    prove
      r"!(h:A->B) k l s p Q.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
          ==> Q INTER ring_carrier(ring_of_integers(subfield_generated l s)) =
              Q INTER s /\
              prime_ideal (ring_of_integers(subfield_generated l s))
                          (Q INTER s) /\
              ~(Q INTER s = {ring_0 l}) /\
              IMAGE h p SUBSET Q INTER s"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool")] NUMBER_FIELD_INTERMEDIATE_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(Q:B->bool) SUBSET ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [ASM_SIMP_TAC [PRIME_IDEAL_IMP_SUBSET], ALL_TAC] THEN MATCH_MP_TAC r2 THEN REPEAT CONJ_TAC THENL [ASM SET_TAC [], DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"Q INTER ring_carrier(ring_of_integers(subfield_generated l s)) =
        {x | x IN ring_carrier(ring_of_integers(subfield_generated l s)) /\
             (I:B->B) x IN Q}") SUBST1_TAC THENL [REWRITE_TAC [I_THM] THEN SET_TAC [], ALL_TAC] THEN MATCH_MP_TAC PRIME_IDEAL_HOMOMORPHIC_PREIMAGE THEN EXISTS_TAC (← q r"ring_of_integers l:B ring") THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS], SUBGOAL_THEN (← q r"?a:A. a IN p /\ ~(a = ring_0 k)") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"~(p = {ring_0(k:A ring)})") THEN MATCH_MP_TAC r1 THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool")] IN_RING_IDEAL_0) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool")] PRIME_IDEAL_IMP_SUBSET) THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET) THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC [], ALL_TAC] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(h:A->B) a IN Q INTER s") MP_TAC THENL [ASM SET_TAC [], ASM_REWRITE_TAC [IN_SING]] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"a:A")] RING_MONOMORPHISM_EQ_0) THEN ANTS_TAC THENL [ALL_TAC, ASM_REWRITE_TAC []] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING, NUMBER_FIELD_IMP_FIELD], MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool")] PRIME_IDEAL_IMP_SUBSET) THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET) THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC []])

  let NUMBER_FIELD_PRIME_IDEALS_INTERMEDIATE ← prove
    r"!(h:A->B) k l s p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> {P | prime_ideal (ring_of_integers(subfield_generated l s)) P /\
                 IMAGE h p SUBSET P} =
            {Q INTER s | Q | prime_ideal (ring_of_integers l) Q /\
                             IMAGE h p SUBSET Q}"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool")] NUMBER_FIELD_INTERMEDIATE_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ABBREV_TAC (← q r"M = subfield_generated l (s:B->bool)") THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"P:B->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN EQ_TAC THENL [STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"M:B ring"), (← q r"p:A->bool"), (← q r"P:B->bool")] NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"M:B ring"), (← q r"l:B ring"), (← q r"I:B->B"), (← q r"P:B->bool")] NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN ASM_REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM, IMAGE_I] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"Q:B->bool") STRIP_ASSUME_TAC) o CONJUNCT2) THEN EXISTS_TAC (← q r"Q:B->bool") THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"M:B ring"), (← q r"l:B ring"), (← q r"I:B->B"), (← q r"P:B->bool"), (← q r"Q:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN ASM_REWRITE_TAC [IMAGE_I, I_THM] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool")] PRIME_IDEAL_IMP_SUBSET) THEN ASM_REWRITE_TAC [] THEN SET_TAC [], DISCH_THEN (X_CHOOSE_THEN (← q r"Q:B->bool") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE) THEN ASM_REWRITE_TAC [] THEN SIMP_TAC []])

  let NUMBER_FIELD_SUBFIELD_PRIME_IDEALS_ABOVE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(!P:A->bool. A P ==> (B P <=> C P)) /\
    (!P:A->bool. A' P ==> (B' P <=> C' P))
    ==> {P | A P /\ B P} = {(g:(A->bool)->(A->bool)) P | P | A' P /\ B' P}
        ==> {P | A P /\ C P} = {g P | P | A' P /\ C' P}")
    prove
      r"!(k:A ring) s p.
          number_field k /\ prime p
          ==> {P | prime_ideal (ring_of_integers(subfield_generated k s)) P /\
                   ring_of_num (subfield_generated k s) p IN P} =
              {Q INTER ring_carrier(subfield_generated k s) | Q |
               prime_ideal (ring_of_integers k) Q /\ ring_of_num k p IN Q}"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [RING_OF_NUM_SUBFIELD_GENERATED] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL) THEN MP_TAC (← ISPECL [(← q r"subfield_generated k (s:A->bool)"), (← q r"p:num")] RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL) THEN ASM_SIMP_TAC [NUMBER_FIELD_SUBFIELD_GENERATED, PRIME_SUBFIELD_SUBFIELD_GENERATED, RING_OF_NUM_SUBFIELD_GENERATED] THEN ABBREV_TAC (← q r"p0 = ideal_generated (ring_of_integers(subfield_generated k {ring_0 k}))
                           {ring_of_num k p:A}") THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"ring_carrier(subfield_generated k (s:A->bool))"), (← q r"p0:A->bool")] NUMBER_FIELD_PRIME_IDEALS_INTERMEDIATE) THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, SUBFIELD_SUBFIELD_GENERATED, IMAGE_I, PRIME_SUBFIELD_MINIMAL, SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED, (← CONJUNCT2 SUBFIELD_GENERATED)] THEN MATCH_MP_TAC r1 THEN RULE_ASSUM_TAC (REWRITE_RULE [IMAGE_I]) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL])

  let NUMBER_FIELD_DECOMPOSITION_GROUP_INTERMEDIATE ← prove
    r"!(h:A->B) k l s p Q.
        number_field l /\ galois_extension(k,l) h /\
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
        ==> CARD(group_carrier(decomposition_group(k,l) h Q) INTER
                 group_carrier(galois_group(subfield_generated l s,l) I)) =
            ramification_index
              (ring_of_integers(subfield_generated l s),ring_of_integers l)
              I Q *
            residue_degree
              (ring_of_integers(subfield_generated l s),ring_of_integers l)
              I Q /\
            CARD(group_carrier(inertia_group(k,l) h (ring_of_integers l) Q)
                 INTER
                 group_carrier(galois_group(subfield_generated l s,l) I)) =
            ramification_index
              (ring_of_integers(subfield_generated l s),ring_of_integers l)
              I Q /\
            CARD(group_carrier(decomposition_group(k,l) h Q) INTER
                 group_carrier(galois_group(subfield_generated l s,l) I)) *
            ramification_index
              (ring_of_integers k,ring_of_integers(subfield_generated l s)) h
              (Q INTER s) *
            residue_degree
              (ring_of_integers k,ring_of_integers(subfield_generated l s)) h
              (Q INTER s) =
            CARD(group_carrier(decomposition_group(k,l) h Q)) /\
            CARD(group_carrier(inertia_group(k,l) h (ring_of_integers l) Q)
                 INTER
                 group_carrier(galois_group(subfield_generated l s,l) I)) *
            ramification_index
              (ring_of_integers k,ring_of_integers(subfield_generated l s)) h
              (Q INTER s) =
            CARD(group_carrier(inertia_group(k,l) h (ring_of_integers l) Q))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool")] NUMBER_FIELD_INTERMEDIATE_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ABBREV_TAC (← q r"M = subfield_generated l (s:B->bool)") THEN SUBGOAL_THEN (← q r"galois_extension(M,l) (I:B->B)") ASSUME_TAC THENL [EXPAND_TAC "M" THEN MATCH_MP_TAC GALOIS_EXTENSION_SUBFIELD_GENERATED THEN MAP_EVERY EXISTS_TAC [(← q r"h:A->B"), (← q r"k:A ring")] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"group_carrier(decomposition_group(M,l) (I:B->B) Q) =
    group_carrier(decomposition_group(k,l) (h:A->B) Q) INTER
    group_carrier(galois_group(M,l) I) /\
    group_carrier(inertia_group(M,l) (I:B->B) (ring_of_integers l) Q) =
    group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q) INTER
    group_carrier(galois_group(M,l) I)") (CONJUNCTS_THEN (SUBST1_TAC o SYM)) THENL [EXPAND_TAC "M" THEN CONJ_TAC THENL [MATCH_MP_TAC DECOMPOSITION_GROUP_INTERMEDIATE THEN ASM_REWRITE_TAC [], MATCH_MP_TAC INERTIA_GROUP_INTERMEDIATE THEN ASM_SIMP_TAC [RING_OF_INTEGERS_SUBRING, PRIME_IMP_RING_IDEAL] THEN MESON_TAC [GALOIS_GROUP_RING_OF_INTEGERS]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:B->B"), (← q r"M:B ring"), (← q r"l:B ring"), (← q r"Q INTER (s:B->bool)"), (← q r"Q:B->bool")] NUMBER_FIELD_DECOMPOSITION_GROUP) THEN ASM_REWRITE_TAC [IMAGE_I, INTER_SUBSET] THEN ANTS_TAC THENL [EXPAND_TAC "M" THEN REWRITE_TAC [SUBFIELD_GENERATED] THEN ASM_REWRITE_TAC [], DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC (SUBST1_TAC o CONJUNCT1))] THEN REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_DECOMPOSITION_GROUP) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC (SUBST1_TAC o CONJUNCT1)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"M:B ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"I:B->B"), (← q r"Q INTER (s:B->bool)"), (← q r"Q:B->bool")] NUMBER_FIELD_RAMIFICATION_INDEX_TOWER) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"M:B ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"I:B->B"), (← q r"Q INTER (s:B->bool)"), (← q r"Q:B->bool")] NUMBER_FIELD_RESIDUE_DEGREE_TOWER) THEN ASM_REWRITE_TAC [I_O_ID, IMAGE_I, INTER_SUBSET] THEN SUBGOAL_THEN (← q r"~(Q INTER s = {ring_0(M:B ring)})") (fun th => REWRITE_TAC [th]) THENL [EXPAND_TAC "M" THEN REWRITE_TAC [SUBFIELD_GENERATED] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC [MULT_AC])

  let NUMBER_FIELD_INTERMEDIATE_SPLITTING ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"s INTER t:A->bool = s"
    let p2 ← prove r"!s t:A->bool. FINITE s ==> (s SUBSET t <=> CARD(s INTER t) = CARD s)" (REPEAT STRIP_TAC THEN EQ_TAC THENL [DISCH_TAC THEN AP_TERM_TAC THEN ASM SET_TAC [], DISCH_TAC THEN SUBGOAL_THEN q1 MP_TAC THENL [MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC [INTER_SUBSET], SET_TAC []]])
    let lemma := p2
    let q3 ← q r"1"
    let q4 ← q r"e:num"
    let q5 ← q r"i:num"
    let v6 ← SPECL [q5, q4, q3] EQ_MULT_LCANCEL
    let p7 ← prove r"!c e i. ~(i = 0) /\ c * e = i ==> (e = 1 <=> c = i)" (REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN ASM_ARITH_TAC, DISCH_THEN SUBST_ALL_TAC THEN MP_TAC v6 THEN ASM_REWRITE_TAC [MULT_CLAUSES]])
    let arith := p7
    let v8 ← GSYM MULT_EQ_1
    let q9 ← q r"Q:B->bool"
    let q10 ← q r"ring_of_integers l:B ring"
    let q11 ← q r"l:B ring"
    let q12 ← q r"k:A ring"
    let q13 ← q r"h:A->B"
    let v14 ← ISPECL [q13, q12, q11, q10, q9] FINITE_DECOMPOSITION_INERTIA_GROUPS
    let q15 ← q r"finite_extension(k,l) (h:A->B)"
    let q16 ← q r"Q:B->bool"
    let q17 ← q r"p:A->bool"
    let q18 ← q r"s:B->bool"
    let q19 ← q r"l:B ring"
    let q20 ← q r"k:A ring"
    let q21 ← q r"h:A->B"
    let v22 ← ISPECL [q21, q20, q19, q18, q17, q16] NUMBER_FIELD_DECOMPOSITION_GROUP_INTERMEDIATE
    let q23 ← q r"field k /\ ring_homomorphism(k,l) (h:A->B)"
    prove
      r"!(h:A->B) k l s p Q.
          number_field l /\ galois_extension(k,l) h /\
          s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
          ==> (ramification_index
                (ring_of_integers k,ring_of_integers(subfield_generated l s)) h
                (Q INTER s) = 1 <=>
               group_carrier(inertia_group(k,l) h (ring_of_integers l) Q) SUBSET
               group_carrier(galois_group(subfield_generated l s,l) I)) /\
              (ramification_index
                (ring_of_integers k,ring_of_integers(subfield_generated l s)) h
                (Q INTER s) = 1 /\
               residue_degree
                (ring_of_integers k,ring_of_integers(subfield_generated l s)) h
                (Q INTER s) = 1 <=>
               group_carrier(decomposition_group(k,l) h Q) SUBSET
               group_carrier(galois_group(subfield_generated l s,l) I))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN q23 STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC v22 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 (fun (_ : thm) => ALL_TAC) (CONJUNCTS_THEN2 (fun (_ : thm) => ALL_TAC) STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN q15 ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_TOWER_LAW], ALL_TAC] THEN MP_TAC v14 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_SIMP_TAC [lemma, v8] THEN CONJ_TAC THEN MATCH_MP_TAC arith THEN ASM_REWRITE_TAC [MULT_ASSOC] THEN ASM_SIMP_TAC [CARD_EQ_0])

  let NUMBER_FIELD_INTERMEDIATE_SPLITTING_TYPES ← prove
    r"!(h:A->B) k l s p.
        number_field l /\ galois_extension(k,l) h /\
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> (unramified
              (ring_of_integers k,ring_of_integers(subfield_generated l s)) h
              p <=>
             !Q. prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
                 ==> group_carrier(inertia_group(k,l) h (ring_of_integers l) Q)
                     SUBSET
                     group_carrier(galois_group(subfield_generated l s,l) I)) /\
            (totally_split
              (ring_of_integers k,ring_of_integers(subfield_generated l s)) h
              p <=>
             !Q. prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
                 ==> group_carrier(decomposition_group(k,l) h Q) SUBSET
                     group_carrier(galois_group(subfield_generated l s,l) I))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_IDEALS_INTERMEDIATE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (GEN_REWRITE_RULE id [EXTENSION])) THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"unramified
     (ring_of_integers k,ring_of_integers(subfield_generated l s)) (h:A->B)
     p <=>
    weakly_unramified
     (ring_of_integers k,ring_of_integers(subfield_generated l s)) h p") SUBST1_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN ASM_MESON_TAC [NUMBER_FIELD_INTERMEDIATE_FIELD], ALL_TAC] THEN SUBGOAL_THEN (← q r"!Q. prime_ideal (ring_of_integers l) Q /\ IMAGE (h:A->B) p SUBSET Q
        ==> (ramification_index
              (ring_of_integers k,ring_of_integers(subfield_generated l s)) h
              (Q INTER s) = 1 <=>
             group_carrier(inertia_group(k,l) h (ring_of_integers l) Q) SUBSET
             group_carrier(galois_group(subfield_generated l s,l) I)) /\
            (ramification_index
              (ring_of_integers k,ring_of_integers(subfield_generated l s)) h
              (Q INTER s) = 1 /\
             residue_degree
              (ring_of_integers k,ring_of_integers(subfield_generated l s)) h
              (Q INTER s) = 1 <=>
             group_carrier(decomposition_group(k,l) h Q) SUBSET
             group_carrier(galois_group(subfield_generated l s,l) I))") (LABEL_TAC "*") THENL [X_GEN_TAC (← q r"Q:B->bool") THEN STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_INTERMEDIATE_SPLITTING THEN EXISTS_TAC (← q r"p:A->bool") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [weakly_unramified, totally_split] THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_UNWIND_THM2] THEN REWRITE_TAC [(← GSYM IMP_CONJ)] THEN CONJ_TAC THEN AP_TERM_TAC THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN X_GEN_TAC (← q r"Q:B->bool") THEN REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"prime_ideal (ring_of_integers l) (Q:B->bool) /\ IMAGE (h:A->B) p SUBSET Q") THEN ASM_REWRITE_TAC [] THEN USE_THEN "*" (MP_TAC o (SPEC (← q r"Q:B->bool"))) THEN ASM_SIMP_TAC [])

  let NUMBER_FIELD_GENERATED_SPLITTING_TYPES ← prove
    r"!(h:A->B) k l X p.
        number_field l /\ galois_extension(k,l) h /\
        X SUBSET ring_carrier l /\ IMAGE h (ring_carrier k) SUBSET X /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> (unramified
              (ring_of_integers k,ring_of_integers(subfield_generated l X)) h
              p <=>
             !Q f x. prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
                     f IN group_carrier
                           (inertia_group(k,l) h (ring_of_integers l) Q) /\
                     x IN X
                     ==> f x = x) /\
            (totally_split
              (ring_of_integers k,ring_of_integers(subfield_generated l X)) h
              p <=>
             !Q f x. prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
                     f IN group_carrier(decomposition_group(k,l) h Q) /\
                     x IN X
                     ==> f x = x)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_carrier(subfield_generated l (X:B->bool))"), (← q r"p:A->bool")] NUMBER_FIELD_INTERMEDIATE_SPLITTING_TYPES) THEN ANTS_TAC THENL [ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED] THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC (← q r"X:B->bool") THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN ASM_REWRITE_TAC [], REWRITE_TAC [SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN DISCH_THEN (fun th => REWRITE_TAC [th])] THEN SUBGOAL_THEN (← q r"!Q. group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q)
        SUBSET group_carrier(galois_group(k,l) h) /\
        group_carrier(decomposition_group(k,l) h Q) SUBSET
        group_carrier(galois_group(k,l) h)") ASSUME_TAC THENL [REWRITE_TAC [inertia_group, decomposition_group, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!H. H SUBSET group_carrier(galois_group(k,l) (h:A->B))
        ==>
          (H SUBSET group_carrier(galois_group(subfield_generated l X,l) I) <=>
             !f x. f IN H /\ x IN X ==> f x = x)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN ASM_SIMP_TAC [SUBSET, IN_GALOIS_GROUP_SUBFIELD_GENERATED] THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [] THEN RULE_ASSUM_TAC (REWRITE_RULE [SUBSET, IN_GALOIS_GROUP]) THEN ASM_SIMP_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [] THEN MESON_TAC [])

  let NUMBER_FIELD_GALOIS_UNRAMIFIED_MONO ← prove
    r"!(h:A->B) k l X Y p.
        number_field l /\ galois_extension(k,l) h /\
        X SUBSET Y /\ Y SUBSET ring_carrier l /\
        IMAGE h (ring_carrier k) SUBSET X /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        unramified (ring_of_integers k,ring_of_integers(subfield_generated l Y))
          h p
        ==> unramified
              (ring_of_integers k,ring_of_integers(subfield_generated l X))
              h p"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"Y:B->bool"), (← q r"p:A->bool")] NUMBER_FIELD_GENERATED_SPLITTING_TYPES) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"X:B->bool"), (← q r"p:A->bool")] NUMBER_FIELD_GENERATED_SPLITTING_TYPES) THEN ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN (SUBST1_TAC o CONJUNCT1)] THEN ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN (MP_TAC o CONJUNCT1)] THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC [])

  let NUMBER_FIELD_GALOIS_SPLITTING_TYPES ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"1"
    let q2 ← q r"e:num"
    let q3 ← q r"i:num"
    let v4 ← SPECL [q3, q2, q1] EQ_MULT_LCANCEL
    let p5 ← prove r"!c e i:num. ~(i = 0) /\ c * e = i ==> (e = 1 <=> c = i)" (REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN ASM_ARITH_TAC, DISCH_THEN SUBST_ALL_TAC THEN MP_TAC v4 THEN ASM_REWRITE_TAC [MULT_CLAUSES]])
    let arith := p5
    let p6 ← prove r"!s a:A. FINITE s /\ a IN s ==> (s = {a} <=> CARD s = 1)" (REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC [CARD_SING] THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC [SING_SUBSET, CARD_SING])
    let card1 := p6
    let p7 ← prove r"!s t:A->bool. FINITE t /\ s SUBSET t ==> (s = t <=> CARD s = CARD t)" (MESON_TAC [CARD_SUBSET_EQ])
    let cardeq := p7
    let q8 ← q r"CARD(S:(B->bool)->bool) * e * f:num = n"
    let q9 ← q r"n:num"
    let q10 ← q r"CARD(S:(B->bool)->bool) * f"
    let q11 ← q r"e:num"
    let v12 ← SPECL [q11, q10, q9] arith
    let v13 ← GSYM CONJ_ASSOC
    let q14 ← q r"p:A->bool"
    let q15 ← q r"h:A->B"
    let q16 ← q r"l:B ring"
    let q17 ← q r"k:A ring"
    let v18 ← ISPECL [q17, q16, q15, q14] TOTALLY_RAMIFIED_RAMIFICATION_INDEX
    let q19 ← q r"e * f:num = n"
    let q20 ← q r"e * f:num = n"
    let q21 ← q r"CARD(S:(B->bool)->bool) * e * f:num = n"
    let q22 ← q r"n:num"
    let q23 ← q r"CARD(S:(B->bool)->bool)"
    let q24 ← q r"e * f:num"
    let v25 ← SPECL [q24, q23, q22] arith
    let v26 ← GSYM CONJ_ASSOC
    let q27 ← q r"p:A->bool"
    let q28 ← q r"h:A->B"
    let q29 ← q r"l:B ring"
    let q30 ← q r"k:A ring"
    let v31 ← ISPECL [q30, q29, q28, q27] INERT_RESIDUE_DEGREE
    let q32 ← q r"p:A->bool"
    let q33 ← q r"h:A->B"
    let q34 ← q r"l:B ring"
    let q35 ← q r"k:A ring"
    let v36 ← ISPECL [q35, q34, q33, q32] TOTALLY_SPLIT_CARD
    let q37 ← q r"Q:B->bool"
    let q38 ← q r"p:A->bool"
    let q39 ← q r"h:A->B"
    let q40 ← q r"l:B ring"
    let q41 ← q r"k:A ring"
    let v42 ← ISPECL [q41, q40, q39, q38, q37] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION
    let q43 ← q r"Q:B->bool"
    let q44 ← q r"g:B->B"
    let q45 ← q r"l:B ring"
    let q46 ← q r"k:A ring"
    let q47 ← q r"h:A->B"
    let v48 ← ISPECL [q47, q46, q45, q44, q43] NUMBER_FIELD_RAMIFICATION_INDEX_CONJUGATE
    let q49 ← q r"g:B->B"
    let q50 ← q r"P:B->bool"
    let q51 ← q r"Q:B->bool"
    let q52 ← q r"p:A->bool"
    let q53 ← q r"l:B ring"
    let q54 ← q r"k:A ring"
    let q55 ← q r"h:A->B"
    let v56 ← ISPECL [q55, q54, q53, q52, q51, q50] NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE
    let q57 ← q r"P:B->bool"
    let q58 ← q r"Q:B->bool"
    let q59 ← q r"(Q:B->bool) IN S"
    let q60 ← q r"P:B->bool"
    let q61 ← q r"!P. (S = {P:B->bool} <=> P = Q /\ CARD S = 1)"
    let q62 ← q r"CARD(S:(B->bool)->bool) * e * f:num = n"
    let q63 ← q r"~(n:num = 0)"
    let q64 ← q r"(Q:B->bool) IN S"
    let q65 ← q r"S = {P | prime_ideal (ring_of_integers l) P /\ IMAGE (h:A->B) p SUBSET P}"
    let q66 ← q r"n = extension_degree(k:A ring,l:B ring) h"
    let q67 ← q r"f = residue_degree (ring_of_integers k,ring_of_integers l) (h:A->B) Q"
    let q68 ← q r"e = ramification_index (ring_of_integers k,ring_of_integers l) (h:A->B) Q"
    let q69 ← q r"(group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q) = {I}
     <=> CARD(group_carrier(inertia_group(k,l) h (ring_of_integers l) Q)) =
         1) /\
    (group_carrier(decomposition_group(k,l) h Q) = {I} <=>
     CARD(group_carrier(decomposition_group(k,l) h Q)) = 1) /\
    (group_carrier(decomposition_group(k,l) h Q) =
     group_carrier(galois_group(k,l) h) <=>
     CARD(group_carrier(decomposition_group(k,l) h Q)) =
     CARD(group_carrier(galois_group(k,l) h))) /\
    (group_carrier(inertia_group(k,l) h (ring_of_integers l) Q) =
     group_carrier(galois_group(k,l) h) <=>
     CARD(group_carrier(inertia_group(k,l) h (ring_of_integers l) Q)) =
     CARD(group_carrier(galois_group(k,l) h)))"
    let q70 ← q r"I IN group_carrier(decomposition_group(k,l) (h:A->B) Q) /\
    I IN group_carrier(inertia_group(k,l) h (ring_of_integers l) Q) /\
    group_carrier(decomposition_group(k,l) h Q) SUBSET
    group_carrier(galois_group(k,l) h) /\
    group_carrier(inertia_group(k,l) h (ring_of_integers l) Q) SUBSET
    group_carrier(galois_group(k,l) h) /\
    FINITE(group_carrier(galois_group(k,l) h)) /\
    CARD(group_carrier(galois_group(k,l) h)) = extension_degree(k,l) h"
    let q71 ← q r"Q:B->bool"
    let q72 ← q r"ring_of_integers l:B ring"
    let q73 ← q r"l:B ring"
    let q74 ← q r"k:A ring"
    let q75 ← q r"h:A->B"
    let v76 ← ISPECL [q75, q74, q73, q72, q71] FINITE_DECOMPOSITION_INERTIA_GROUPS
    let q77 ← q r"p:A->bool"
    let q78 ← q r"h:A->B"
    let q79 ← q r"l:B ring"
    let q80 ← q r"k:A ring"
    let v81 ← ISPECL [q80, q79, q78, q77] NUMBER_FIELD_PRIME_IDEALS_ABOVE
    let q82 ← q r"Q:B->bool"
    let q83 ← q r"p:A->bool"
    let q84 ← q r"h:A->B"
    let q85 ← q r"l:B ring"
    let q86 ← q r"k:A ring"
    let v87 ← ISPECL [q86, q85, q84, q83, q82] NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS
    let q88 ← q r"Q:B->bool"
    let q89 ← q r"p:A->bool"
    let q90 ← q r"l:B ring"
    let q91 ← q r"k:A ring"
    let q92 ← q r"h:A->B"
    let v93 ← ISPECL [q92, q91, q90, q89, q88] NUMBER_FIELD_DECOMPOSITION_GROUP
    let q94 ← q r"ring_monomorphism(k:A ring,l:B ring) h"
    let q95 ← q r"finite_extension(k,l) (h:A->B)"
    let q96 ← q r"unramified (ring_of_integers k,ring_of_integers l) (h:A->B) p <=>
    weakly_unramified (ring_of_integers k,ring_of_integers l) h p"
    let q97 ← q r"field k /\ ring_homomorphism(k,l) (h:A->B)"
    prove
      r"!(h:A->B) k l p Q.
          number_field l /\ galois_extension(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
          ==> (unramified (ring_of_integers k,ring_of_integers l) h p <=>
               group_carrier(inertia_group(k,l) h (ring_of_integers l) Q) =
               {I}) /\
              (totally_split (ring_of_integers k,ring_of_integers l) h p <=>
               group_carrier(decomposition_group(k,l) h Q) = {I}) /\
              (inert (ring_of_integers k,ring_of_integers l) h p <=>
               group_carrier(decomposition_group(k,l) h Q) =
               group_carrier(galois_group(k,l) h) /\
               group_carrier(inertia_group(k,l) h (ring_of_integers l) Q) =
               {I}) /\
              (totally_ramified (ring_of_integers k,ring_of_integers l) h p <=>
               group_carrier(inertia_group(k,l) h (ring_of_integers l) Q) =
               group_carrier(galois_group(k,l) h))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN q97 STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN SUBGOAL_THEN q96 SUBST1_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN q95 ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_TOWER_LAW], ALL_TAC] THEN SUBGOAL_THEN q94 ASSUME_TAC THENL [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING, NUMBER_FIELD_IMP_FIELD], ALL_TAC] THEN MP_TAC v93 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC v87 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC v81 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC v76 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN q70 STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THENL [MESON_TAC [GROUP_ID, DECOMPOSITION_GROUP], MESON_TAC [GROUP_ID, INERTIA_GROUP], REWRITE_TAC [decomposition_group, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET], REWRITE_TAC [inertia_group, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET], ASM_SIMP_TAC [FINITE_GALOIS_GROUP], ASM_MESON_TAC [GALOIS_EXTENSION_EQ_CARD]], ALL_TAC] THEN SUBGOAL_THEN q69 (fun th => REWRITE_TAC [th]) THENL [REPEAT CONJ_TAC THEN (MATCH_MP_TAC card1 ORELSE MATCH_MP_TAC cardeq) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ABBREV_TAC q68 THEN ABBREV_TAC q67 THEN ABBREV_TAC q66 THEN ABBREV_TAC q65 THEN SUBGOAL_THEN q64 ASSUME_TAC THENL [EXPAND_TAC "S" THEN ASM_REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN q63 ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC q62 THEN ASM_REWRITE_TAC [MULT_EQ_0] THEN ASM_SIMP_TAC [CARD_EQ_0] THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN q61 ASSUME_TAC THENL [X_GEN_TAC q60 THEN EQ_TAC THENL [DISCH_TAC THEN ASM_REWRITE_TAC [CARD_SING] THEN UNDISCH_TAC q59 THEN ASM_REWRITE_TAC [IN_SING] THEN MESON_TAC [], STRIP_TAC THEN ASM_MESON_TAC [card1]], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [weakly_unramified] THEN EQ_TAC THENL [DISCH_THEN (MP_TAC o (SPEC q58)) THEN ASM_REWRITE_TAC [], DISCH_TAC THEN X_GEN_TAC q57 THEN STRIP_TAC THEN MP_TAC v56 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q49 STRIP_ASSUME_TAC) THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN MP_TAC v48 THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [MP_TAC v42 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []]], MP_TAC v36 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC arith THEN ASM_REWRITE_TAC [], MP_TAC v31 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [RIGHT_AND_EXISTS_THM, v26, UNWIND_THM2] THEN MP_TAC v25 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN UNDISCH_TAC q21 THEN ARITH_TAC, DISCH_THEN SUBST1_TAC] THEN ASM_CASES_TAC q20 THEN ASM_REWRITE_TAC [] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC arith THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC q19 THEN ARITH_TAC, MP_TAC v18 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [RIGHT_AND_EXISTS_THM, v13, UNWIND_THM2] THEN MP_TAC v12 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN UNDISCH_TAC q8 THEN REWRITE_TAC [MULT_AC], DISCH_THEN (SUBST1_TAC o SYM)] THEN REWRITE_TAC [MULT_EQ_1] THEN CONV_TAC TAUT])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_INTERMEDIATE_FIELD, NUMBER_FIELD_GALOIS_INTERMEDIATE,
           NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE, NUMBER_FIELD_PRIME_IDEALS_INTERMEDIATE,
           NUMBER_FIELD_SUBFIELD_PRIME_IDEALS_ABOVE,
           NUMBER_FIELD_DECOMPOSITION_GROUP_INTERMEDIATE,
           NUMBER_FIELD_INTERMEDIATE_SPLITTING,
           NUMBER_FIELD_INTERMEDIATE_SPLITTING_TYPES,
           NUMBER_FIELD_GENERATED_SPLITTING_TYPES, NUMBER_FIELD_GALOIS_UNRAMIFIED_MONO,
           NUMBER_FIELD_GALOIS_SPLITTING_TYPES }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- decomposition_field.ml phrases from line 800 to 1097                   -/
/- ---------------------------------------------------------------------- -/

structure DecompositionField02 where
  -- @@FIELDS
  NUMBER_FIELD_ABELIAN_DECOMPOSITION_GROUP : thm
  NUMBER_FIELD_DECOMPOSITION_FIELD : thm
  NUMBER_FIELD_INERTIA_DECOMPOSITION_TOWER : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDecompositionField02 [HolBase] (D : DecompositionFieldDeps) (BDecompositionField01 : DecompositionField01) :
    ExceptT String IO DecompositionField02 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, SET_TAC, .. } := D
  let { CARD_EQ_0, CARD_SING, CARD_SUBSET_EQ, DECOMPOSITION_GROUP,
        DECOMPOSITION_GROUP_CONJUGATE, DECOMPOSITION_GROUP_RING_OF_INTEGERS,
        EQ_MULT_LCANCEL, EQ_MULT_RCANCEL, EQ_TRANS, EXTENSION,
        EXTENSION_DEGREE_TOWER_LAW, FIELD_IMP_NONTRIVIAL_RING,
        FIELD_RING_HOMOMORPHISM_MONOMORPHISM, FINITE_DECOMPOSITION_INERTIA_GROUPS,
        FIXED_FIELD_ANTIMONO, GALOIS_CORRESPONDENCE_DEGREE,
        GALOIS_EXTENSION_SUBFIELD_GENERATED, GALOIS_GROUP, GALOIS_GROUP_FIXED_FIELD,
        GALOIS_GROUP_PERMUTES, GALOIS_GROUP_RING_OF_INTEGERS,
        GALOIS_IMP_FIELD_EXTENSION, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET, IMAGE_EQ,
        IMAGE_I, IMAGE_ID, INERTIA_GROUP, INERTIA_GROUP_CONJUGATE,
        INERTIA_GROUP_SUBGROUP_OF_DECOMPOSITION_GROUP, INERT_RESIDUE_DEGREE,
        INTER_IDEMPOT, INTER_SUBSET, IN_ELIM_THM, IN_SING, I_O_ID, .. } := D.core1
  let { MULT_CLAUSES, MULT_EQ_1, NUMBER_FIELD_DECOMPOSITION_GROUP,
        NUMBER_FIELD_FROBENIUS_ELEMENT, NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_PRIME_IDEALS_ABOVE,
        NUMBER_FIELD_RAMIFICATION_INDEX_TOWER, NUMBER_FIELD_RESIDUE_DEGREE_TOWER,
        NUMBER_FIELD_TOWER_LAW, PERMUTES_INVERSES_o, PRIME_IMP_RING_IDEAL,
        RING_HOMOMORPHISM_INTO_SUBRING, RING_MONOMORPHISM_IMP_HOMOMORPHISM,
        RING_OF_INTEGERS_SUBRING, SING_SUBSET, SUBFIELD_GENERATED,
        SUBGROUP_SUBGROUP_GENERATED, SUBRING_GENERATED_BY_SUBFIELD_GENERATED,
        TOTALLY_RAMIFIED_RAMIFICATION_INDEX, UNWIND_THM2, abelian_group,
        decomposition_group, field_extension, inertia_group, o_ASSOC, subgroup_of, .. } := D.core2
  let { NUMBER_FIELD_DECOMPOSITION_GROUP_INTERMEDIATE, NUMBER_FIELD_INTERMEDIATE_FIELD,
        NUMBER_FIELD_PRIME_IDEALS_INTERMEDIATE, NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE, .. } := BDecompositionField01
  -- @@SCOPE END

  let NUMBER_FIELD_ABELIAN_DECOMPOSITION_GROUP ← prove
    r"!(h:A->B) k l p Q Q'.
        number_field l /\ galois_extension(k,l) h /\
        abelian_group(galois_group(k,l) h) /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
        prime_ideal (ring_of_integers l) Q' /\ IMAGE h p SUBSET Q'
        ==> decomposition_group(k,l) h Q' = decomposition_group(k,l) h Q /\
            inertia_group(k,l) h (ring_of_integers l) Q' =
            inertia_group(k,l) h (ring_of_integers l) Q /\
            (ramification_index (ring_of_integers k,ring_of_integers l) h Q = 1
             ==> frobenius_element (k,l) h (ring_of_integers l) Q' =
                 frobenius_element (k,l) h (ring_of_integers l) Q)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool"), (← q r"Q':B->bool")] NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:B->B") (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM))) THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier(galois_group(k,l) (h:A->B))
        ==> (g:B->B) o f o inverse g = f") ASSUME_TAC THENL [X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN UNDISCH_TAC (← q r"abelian_group(galois_group(k,l) (h:A->B))") THEN REWRITE_TAC [abelian_group, GALOIS_GROUP] THEN DISCH_THEN (MP_TAC o (SPECL [(← q r"g:B->B"), (← q r"f:B->B")])) THEN ANTS_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP], DISCH_TAC] THEN ASM_REWRITE_TAC [o_ASSOC] THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP GALOIS_GROUP_PERMUTES) o (checkM (fun th => (do let z17 ← (q r"g IN group_carrier(galois_group(k,l) (h:A->B))"); let z16 ← (do let z15 ← (pure th); pure (concl z15)); pure (z16 == z17)))))) THEN DISCH_THEN (MP_TAC o (MATCH_MP PERMUTES_INVERSES_o)) THEN SIMP_TAC [(← GSYM o_ASSOC), I_O_ID], ALL_TAC] THEN SUBGOAL_THEN (← q r"!S. S SUBSET group_carrier(galois_group(k,l) (h:A->B))
        ==> IMAGE (\f. (g:B->B) o f o inverse g) S = S") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"IMAGE (\f:B->B. f) S") THEN CONJ_TAC THENL [MATCH_MP_TAC IMAGE_EQ THEN ASM SET_TAC [], REWRITE_TAC [IMAGE_ID]], ALL_TAC] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [decomposition_group] THEN AP_TERM_TAC THEN REWRITE_TAC [(← GSYM (← CONJUNCT1 DECOMPOSITION_GROUP))] THEN ASM_SIMP_TAC [DECOMPOSITION_GROUP_CONJUGATE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [decomposition_group, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET], REWRITE_TAC [inertia_group] THEN AP_TERM_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"IMAGE (g:B->B) Q")] (← CONJUNCT1 INERTIA_GROUP)) THEN ANTS_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING, DECOMPOSITION_GROUP_RING_OF_INTEGERS] THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool")] (← CONJUNCT1 INERTIA_GROUP)) THEN ANTS_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING, DECOMPOSITION_GROUP_RING_OF_INTEGERS] THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"g:B->B"), (← q r"Q:B->bool")] INERTIA_GROUP_CONJUGATE) THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING, GALOIS_GROUP_RING_OF_INTEGERS] THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN DISCH_THEN SUBST1_TAC THEN REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [inertia_group, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET], DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_FROBENIUS_ELEMENT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"g:B->B")) o (CONJUNCT2 o CONJUNCT2))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); canM (fun z3 => (do let z4 ← (pure z3); find_termM (fun z5 => (do let z7 ← (pure z5); let z6 ← (q r"inverse(g:B->B)"); pure (z6 == z7))) z4)) z1) then (do pure !(← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); canM (fun z10 => (do let z11 ← (pure z10); find_termM (fun z12 => (do let z14 ← (pure z12); let z13 ← (q r"IMAGE:((B->B)->(B->B))->((B->B)->bool)->                                  ((B->B)->bool)"); pure (z13 == z14))) z11)) z8))) else pure false)))) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_FROBENIUS_ELEMENT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN SIMP_TAC []])

  let NUMBER_FIELD_DECOMPOSITION_FIELD ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"1"
    let q2 ← q r"e:num"
    let q3 ← q r"i:num"
    let v4 ← SPECL [q3, q2, q1] EQ_MULT_LCANCEL
    let p5 ← prove r"!c e i:num. ~(i = 0) /\ c * e = i ==> (e = 1 <=> c = i)" (REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN ASM_ARITH_TAC, DISCH_THEN SUBST_ALL_TAC THEN MP_TAC v4 THEN ASM_REWRITE_TAC [MULT_CLAUSES]])
    let arith := p5
    let q6 ← q r"~(e * f:num = 0)"
    let q7 ← q r"CARD {P | prime_ideal (ring_of_integers l) P /\
                IMAGE (h:A->B) p SUBSET P} * e * f =
                  extension_degree(k,l) h"
    let q8 ← q r"l:B ring"
    let q9 ← q r"M:B ring"
    let q10 ← q r"k:A ring"
    let q11 ← q r"I:B->B"
    let q12 ← q r"h:A->B"
    let v13 ← ISPECL [q12, q11, q10, q9, q8] EXTENSION_DEGREE_TOWER_LAW
    let q14 ← q r"FINITE(S:(B->bool)->bool)"
    let q15 ← q r"(Q:B->bool) IN S"
    let q16 ← q r"Q INTER (z:B->bool)"
    let q17 ← q r"I:B->B"
    let q18 ← q r"l:B ring"
    let q19 ← q r"M:B ring"
    let v20 ← ISPECL [q19, q18, q17, q16] NUMBER_FIELD_PRIME_IDEALS_ABOVE
    let q21 ← q r"CARD(S:(B->bool)->bool) * e * f = e * f"
    let q22 ← q r"e * f:num"
    let q23 ← q r"CARD(S:(B->bool)->bool)"
    let q24 ← q r"e * f:num"
    let v25 ← SPECL [q24, q23, q22] arith
    let q26 ← q r"CARD(S:(B->bool)->bool) = 1"
    let q27 ← q r"S = {P | prime_ideal (ring_of_integers l) P /\
               Q INTER (z:B->bool) SUBSET P}"
    let q30 ← q r"Q:B->bool"
    let q31 ← q r"Q INTER (z:B->bool)"
    let q32 ← q r"l:B ring"
    let q33 ← q r"M:B ring"
    let q34 ← q r"I:B->B"
    let v35 ← ISPECL [q34, q33, q32, q31, q30] NUMBER_FIELD_DECOMPOSITION_GROUP
    let q36 ← q r"CARD(D:(B->B)->bool) = e * f"
    let q37 ← q r"~(CARD(D:(B->B)->bool) = 0)"
    let q38 ← q r"~(e * f:num = 0)"
    let q39 ← q r"CARD(D:(B->B)->bool) = e * f"
    let q40 ← q r"CARD(D:(B->B)->bool) = e * f1"
    let q41 ← q r"f:num"
    let q42 ← q r"f1:num"
    let q43 ← q r"e:num"
    let v44 ← SPECL [q43, q42, q41] EQ_MULT_LCANCEL
    let q45 ← q r"f1:num = f"
    let q46 ← q r"CARD(J:(B->B)->bool) = e"
    let q47 ← q r"CARD(J:(B->B)->bool) = e1"
    let q48 ← q r"e1:num = e"
    let q49 ← q r"CARD(D:(B->B)->bool)"
    let q50 ← q r"e0 * f0:num"
    let q51 ← q r"CARD(D:(B->B)->bool)"
    let v52 ← SPECL [q51, q50, q49] arith
    let v53 ← GSYM MULT_EQ_1
    let q54 ← q r"e0:num = 1 /\ f0:num = 1"
    let q55 ← q r"CARD(J:(B->B)->bool) = e"
    let q56 ← q r"~(CARD(D:(B->B)->bool) = 0) /\ ~(e:num = 0)"
    let q57 ← q r"f0 = residue_degree (ring_of_integers k,ring_of_integers M) (h:A->B)
           (Q INTER z)"
    let q58 ← q r"e0 = ramification_index (ring_of_integers k,ring_of_integers M) (h:A->B)
           (Q INTER z)"
    let q59 ← q r"f1 = residue_degree (ring_of_integers M,ring_of_integers l) (I:B->B) Q"
    let q60 ← q r"e1 = ramification_index (ring_of_integers M,ring_of_integers l) (I:B->B) Q"
    let q61 ← q r"f = residue_degree (ring_of_integers k,ring_of_integers l) (h:A->B) Q"
    let q62 ← q r"e = ramification_index (ring_of_integers k,ring_of_integers l) (h:A->B) Q"
    let q63 ← q r"M = subfield_generated l (z:B->bool)"
    let q64 ← q r"z:B->bool"
    let q65 ← q r"l:B ring"
    let q66 ← q r"k:A ring"
    let q67 ← q r"h:A->B"
    let v68 ← ISPECL [q67, q66, q65, q64] GALOIS_CORRESPONDENCE_DEGREE
    let q69 ← q r"extension_degree(subfield_generated l z,l) (I:B->B) = CARD(D:(B->B)->bool)"
    let q70 ← q r"k:A ring"
    let q71 ← q r"h:A->B"
    let q72 ← q r"galois_extension(subfield_generated l z,l) (I:B->B)"
    let q73 ← q r"(J:(B->B)->bool) SUBSET D"
    let q74 ← q r"(J:(B->B)->bool) INTER D = J"
    let q75 ← q r"group_carrier(galois_group(subfield_generated l z,l) (I:B->B)) =
           D"
    let v76 ← ASSUME q75
    let q77 ← q r"group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q) = J"
    let v78 ← ASSUME q77
    let q79 ← q r"group_carrier(decomposition_group(k,l) (h:A->B) Q) = D"
    let v80 ← ASSUME q79
    let q81 ← q r"Q:B->bool"
    let q82 ← q r"p:A->bool"
    let q83 ← q r"z:B->bool"
    let q84 ← q r"l:B ring"
    let q85 ← q r"k:A ring"
    let q86 ← q r"h:A->B"
    let v87 ← ISPECL [q86, q85, q84, q83, q82, q81] NUMBER_FIELD_DECOMPOSITION_GROUP_INTERMEDIATE
    let q88 ← q r"Q:B->bool"
    let q89 ← q r"p:A->bool"
    let q90 ← q r"z:B->bool"
    let q91 ← q r"l:B ring"
    let q92 ← q r"k:A ring"
    let q93 ← q r"h:A->B"
    let v94 ← ISPECL [q93, q92, q91, q90, q89, q88] NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE
    let q95 ← q r"z:B->bool"
    let q96 ← q r"l:B ring"
    let q97 ← q r"k:A ring"
    let q98 ← q r"h:A->B"
    let v99 ← ISPECL [q98, q97, q96, q95] NUMBER_FIELD_INTERMEDIATE_FIELD
    let q100 ← q r"J = group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q)"
    let q101 ← q r"D = group_carrier(decomposition_group(k,l) (h:A->B) Q)"
    let q102 ← q r"group_carrier(decomposition_group(k,l) (h:A->B) Q)"
    let q103 ← q r"l:B ring"
    let q104 ← q r"k:A ring"
    let q105 ← q r"h:A->B"
    let v106 ← ISPECL [q105, q104, q103, q102] GALOIS_GROUP_FIXED_FIELD
    let q107 ← q r"Q:B->bool"
    let q108 ← q r"ring_of_integers l:B ring"
    let q109 ← q r"l:B ring"
    let q110 ← q r"k:A ring"
    let q111 ← q r"h:A->B"
    let v112 ← ISPECL [q111, q110, q109, q108, q107] INERTIA_GROUP_SUBGROUP_OF_DECOMPOSITION_GROUP
    let q113 ← q r"group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q) SUBSET
    group_carrier(decomposition_group(k,l) h Q)"
    let q114 ← q r"Q:B->bool"
    let q115 ← q r"ring_of_integers l:B ring"
    let q116 ← q r"l:B ring"
    let q117 ← q r"k:A ring"
    let q118 ← q r"h:A->B"
    let v119 ← ISPECL [q118, q117, q116, q115, q114] FINITE_DECOMPOSITION_INERTIA_GROUPS
    let q120 ← q r"Q:B->bool"
    let q121 ← q r"p:A->bool"
    let q122 ← q r"l:B ring"
    let q123 ← q r"k:A ring"
    let q124 ← q r"h:A->B"
    let v125 ← ISPECL [q124, q123, q122, q121, q120] NUMBER_FIELD_DECOMPOSITION_GROUP
    let q126 ← q r"finite_extension(k,l) (h:A->B)"
    let q127 ← q r"field k /\ ring_homomorphism(k,l) (h:A->B)"
    prove
      r"!(h:A->B) k l p Q z.
          number_field l /\ galois_extension(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
          fixed_field l (group_carrier(decomposition_group(k,l) h Q)) = z
          ==> z subfield_of l /\ IMAGE h (ring_carrier k) SUBSET z /\
              group_carrier(galois_group(subfield_generated l z,l) I) =
              group_carrier(decomposition_group(k,l) h Q) /\
              prime_ideal (ring_of_integers(subfield_generated l z))
                          (Q INTER z) /\
              IMAGE h p SUBSET Q INTER z /\
              ramification_index
                (ring_of_integers k,ring_of_integers(subfield_generated l z)) h
                (Q INTER z) = 1 /\
              residue_degree
                (ring_of_integers k,ring_of_integers(subfield_generated l z)) h
                (Q INTER z) = 1 /\
              ramification_index
                (ring_of_integers(subfield_generated l z),ring_of_integers l)
                I Q =
              ramification_index (ring_of_integers k,ring_of_integers l) h Q /\
              residue_degree
                (ring_of_integers(subfield_generated l z),ring_of_integers l)
                I Q =
              residue_degree (ring_of_integers k,ring_of_integers l) h Q /\
              {P | prime_ideal (ring_of_integers l) P /\ Q INTER z SUBSET P} =
              {Q} /\
              extension_degree(k,subfield_generated l z) h =
              CARD {P | prime_ideal (ring_of_integers l) P /\
                        IMAGE h p SUBSET P}"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN q127 STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN SUBGOAL_THEN q126 ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_TOWER_LAW], ALL_TAC] THEN MP_TAC v125 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC v119 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN q113 ASSUME_TAC THENL [MP_TAC v112 THEN ANTS_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING, GALOIS_GROUP_RING_OF_INTEGERS] THEN MATCH_MP_TAC PRIME_IMP_RING_IDEAL THEN FIRST_ASSUM ACCEPT_TAC, SIMP_TAC [subgroup_of]], ALL_TAC] THEN MP_TAC v106 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [decomposition_group, SUBGROUP_SUBGROUP_GENERATED], ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC []] THEN ABBREV_TAC q101 THEN ABBREV_TAC q100 THEN MP_TAC v99 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC v94 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC v87 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [v80, v78, v76, INTER_IDEMPOT] THEN SUBGOAL_THEN q74 SUBST1_TAC THENL [UNDISCH_TAC q73 THEN SET_TAC [], ALL_TAC] THEN STRIP_TAC THEN SUBGOAL_THEN q72 ASSUME_TAC THENL [MATCH_MP_TAC GALOIS_EXTENSION_SUBFIELD_GENERATED THEN MAP_EVERY EXISTS_TAC [q71, q70] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q69 ASSUME_TAC THENL [MP_TAC v68 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o CONJUNCT1)] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ABBREV_TAC q63 THEN ABBREV_TAC q62 THEN ABBREV_TAC q61 THEN ABBREV_TAC q60 THEN ABBREV_TAC q59 THEN ABBREV_TAC q58 THEN ABBREV_TAC q57 THEN SUBGOAL_THEN q56 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [CARD_EQ_0] THEN UNDISCH_TAC q55 THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [CARD_EQ_0], ALL_TAC] THEN SUBGOAL_THEN q54 (CONJUNCTS_THEN SUBST_ALL_TAC) THENL [REWRITE_TAC [v53] THEN MP_TAC v52 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q48 SUBST_ALL_TAC THENL [MAP_EVERY UNDISCH_TAC [q47, q46] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN q45 SUBST_ALL_TAC THENL [MP_TAC v44 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MAP_EVERY UNDISCH_TAC [q40, q39] THEN ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [] THEN SUBGOAL_THEN q38 ASSUME_TAC THENL [UNDISCH_TAC q37 THEN UNDISCH_TAC q36 THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [], ALL_TAC] THEN CONJ_TAC THENL [MP_TAC v35 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [IMAGE_I, INTER_SUBSET] THEN EXPAND_TAC "M" THEN REWRITE_TAC [SUBFIELD_GENERATED] THEN ASM_REWRITE_TAC [], DISCH_THEN (fun z28 => tactic_of do pure (MP_TAC (← (do let z29 ← (pure (CONJUNCTS z28)); liftExcept (last z29)))))] THEN ASM_REWRITE_TAC [IMAGE_I] THEN ABBREV_TAC q27 THEN DISCH_TAC THEN SUBGOAL_THEN q26 MP_TAC THENL [MP_TAC v25 THEN REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC q21 THEN ARITH_TAC, ALL_TAC] THEN MP_TAC v20 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN EXPAND_TAC "M" THEN REWRITE_TAC [SUBFIELD_GENERATED] THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC [IMAGE_I] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1)] THEN SUBGOAL_THEN q15 MP_TAC THENL [EXPAND_TAC "S" THEN ASM_REWRITE_TAC [IN_ELIM_THM, INTER_SUBSET], ALL_TAC] THEN UNDISCH_TAC q14 THEN POP_ASSUM_LIST (fun _ => ALL_TAC) THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC [SING_SUBSET, CARD_SING], MP_TAC v13 THEN REWRITE_TAC [field_extension, I_O_ID] THEN ANTS_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC q7 THEN DISCH_THEN (SUBST1_TAC o SYM) THEN UNDISCH_TAC q6 THEN POP_ASSUM_LIST (fun _ => ALL_TAC) THEN MESON_TAC [EQ_MULT_RCANCEL]])

  let NUMBER_FIELD_INERTIA_DECOMPOSITION_TOWER ← prove
    r"!(h:A->B) k l p Q z t.
        number_field l /\ galois_extension(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
        fixed_field l (group_carrier(decomposition_group(k,l) h Q)) = z /\
        fixed_field l
          (group_carrier(inertia_group(k,l) h (ring_of_integers l) Q)) = t
        ==> z SUBSET t /\ t subfield_of l /\
          IMAGE h (ring_carrier k) SUBSET t /\
            group_carrier(galois_group(subfield_generated l t,l) I) =
            group_carrier(inertia_group(k,l) h (ring_of_integers l) Q) /\
            ring_homomorphism(subfield_generated l z,subfield_generated l t) I
              /\
            extension_degree(subfield_generated l z,subfield_generated l t) I =
            residue_degree (ring_of_integers k,ring_of_integers l) h Q /\
            extension_degree(subfield_generated l t,l) I =
            ramification_index (ring_of_integers k,ring_of_integers l) h Q /\
            prime_ideal (ring_of_integers(subfield_generated l t))
                        (Q INTER t) /\
            inert (ring_of_integers(subfield_generated l z),
                   ring_of_integers(subfield_generated l t)) I (Q INTER z) /\
            ramification_index
              (ring_of_integers(subfield_generated l z),
               ring_of_integers(subfield_generated l t)) I (Q INTER t) = 1 /\
            residue_degree
              (ring_of_integers(subfield_generated l z),
               ring_of_integers(subfield_generated l t)) I (Q INTER t) =
            residue_degree (ring_of_integers k,ring_of_integers l) h Q /\
            totally_ramified
              (ring_of_integers(subfield_generated l t),ring_of_integers l) I
              (Q INTER t) /\
            ramification_index
              (ring_of_integers(subfield_generated l t),ring_of_integers l)
              I Q =
            ramification_index (ring_of_integers k,ring_of_integers l) h Q /\
            residue_degree
              (ring_of_integers(subfield_generated l t),ring_of_integers l)
              I Q = 1"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN SUBGOAL_THEN (← q r"finite_extension(k,l) (h:A->B)") ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_TOWER_LAW], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool"), (← q r"z:B->bool")] NUMBER_FIELD_DECOMPOSITION_FIELD) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_DECOMPOSITION_GROUP) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool")] FINITE_DECOMPOSITION_INERTIA_GROUPS) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q) SUBSET
    group_carrier(decomposition_group(k,l) h Q)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool")] INERTIA_GROUP_SUBGROUP_OF_DECOMPOSITION_GROUP) THEN ANTS_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING, GALOIS_GROUP_RING_OF_INTEGERS] THEN MATCH_MP_TAC PRIME_IMP_RING_IDEAL THEN FIRST_ASSUM ACCEPT_TAC, SIMP_TAC [subgroup_of]], ALL_TAC] THEN SUBGOAL_THEN (← q r"group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q)
    subgroup_of galois_group(k,l) h") ASSUME_TAC THENL [REWRITE_TAC [inertia_group, SUBGROUP_SUBGROUP_GENERATED], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q)")] GALOIS_GROUP_FIXED_FIELD) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC []] THEN SUBGOAL_THEN (← q r"(z:B->bool) SUBSET t") ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["z", "t"] THEN MATCH_MP_TAC FIXED_FIELD_ANTIMONO THEN FIRST_ASSUM ACCEPT_TAC, ASM_REWRITE_TAC []] THEN ABBREV_TAC (← q r"D = group_carrier(decomposition_group(k,l) (h:A->B) Q)") THEN ABBREV_TAC (← q r"J = group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q)") THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"t:B->bool")] NUMBER_FIELD_INTERMEDIATE_FIELD) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"z:B->bool")] NUMBER_FIELD_INTERMEDIATE_FIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism(subfield_generated l z,subfield_generated l t) (I:B->B)") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"subfield_generated l (t:B->bool) = subring_generated l t") SUBST1_TAC THENL [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [(← SYM (← ASSUME (← q r"ring_carrier(subfield_generated l (t:B->bool)) = t")))] THEN REWRITE_TAC [SUBRING_GENERATED_BY_SUBFIELD_GENERATED], MATCH_MP_TAC RING_HOMOMORPHISM_INTO_SUBRING THEN ASM_REWRITE_TAC [IMAGE_I]], ASM_REWRITE_TAC []] THEN ABBREV_TAC (← q r"Mz = subfield_generated l (z:B->bool)") THEN ABBREV_TAC (← q r"Mt = subfield_generated l (t:B->bool)") THEN SUBGOAL_THEN (← q r"ring_monomorphism(Mz,Mt) (I:B->B)") ASSUME_TAC THENL [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"t:B->bool")] GALOIS_CORRESPONDENCE_DEGREE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"z:B->bool")] GALOIS_CORRESPONDENCE_DEGREE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"I:B->B"), (← q r"I:B->B"), (← q r"Mz:B ring"), (← q r"Mt:B ring"), (← q r"l:B ring")] EXTENSION_DEGREE_TOWER_LAW) THEN ANTS_TAC THENL [ASM_SIMP_TAC [field_extension, NUMBER_FIELD_IMP_FIELD], ALL_TAC] THEN ASM_REWRITE_TAC [I_O_ID] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"t:B->bool"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ASM_REWRITE_TAC [] THEN STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"t:B->bool"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_DECOMPOSITION_GROUP_INTERMEDIATE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [(← ASSUME (← q r"group_carrier(decomposition_group(k,l) (h:A->B) Q) = D")), (← ASSUME (← q r"group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q) = J")), (← ASSUME (← q r"subfield_generated l (t:B->bool) = Mt")), (← ASSUME (← q r"group_carrier(galois_group(Mt,l) (I:B->B)) = J")), INTER_IDEMPOT] THEN SUBGOAL_THEN (← q r"(D:(B->B)->bool) INTER J = J") SUBST1_TAC THENL [UNDISCH_TAC (← q r"(J:(B->B)->bool) SUBSET D") THEN SET_TAC [], ALL_TAC] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"Mz:B ring"), (← q r"Mt:B ring"), (← q r"l:B ring"), (← q r"I:B->B"), (← q r"I:B->B"), (← q r"Q INTER (t:B->bool)"), (← q r"Q:B->bool")] NUMBER_FIELD_RAMIFICATION_INDEX_TOWER) THEN MP_TAC (← ISPECL [(← q r"Mz:B ring"), (← q r"Mt:B ring"), (← q r"l:B ring"), (← q r"I:B->B"), (← q r"I:B->B"), (← q r"Q INTER (t:B->bool)"), (← q r"Q:B->bool")] NUMBER_FIELD_RESIDUE_DEGREE_TOWER) THEN SUBGOAL_THEN (← q r"~(Q INTER t = {ring_0(Mt:B ring)})") ASSUME_TAC THENL [EXPAND_TAC "Mt" THEN REWRITE_TAC [SUBFIELD_GENERATED] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [I_O_ID, IMAGE_I, INTER_SUBSET] THEN REPEAT DISCH_TAC THEN ABBREV_TAC (← q r"e = ramification_index (ring_of_integers k,ring_of_integers l) (h:A->B) Q") THEN ABBREV_TAC (← q r"f = residue_degree (ring_of_integers k,ring_of_integers l) (h:A->B) Q") THEN ABBREV_TAC (← q r"e1 = ramification_index (ring_of_integers Mt,ring_of_integers l) (I:B->B) Q") THEN ABBREV_TAC (← q r"f1 =
     residue_degree (ring_of_integers Mt,ring_of_integers l) (I:B->B) Q") THEN ABBREV_TAC (← q r"e2 = ramification_index (ring_of_integers Mz,ring_of_integers Mt) (I:B->B)
           (Q INTER t)") THEN ABBREV_TAC (← q r"f2 = residue_degree (ring_of_integers Mz,ring_of_integers Mt) (I:B->B)
           (Q INTER t)") THEN SUBGOAL_THEN (← q r"~(e:num = 0)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"CARD(J:(B->B)->bool) = e") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [CARD_EQ_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"e1:num = e") SUBST_ALL_TAC THENL [MAP_EVERY UNDISCH_TAC [(← q r"CARD(J:(B->B)->bool) = e1"), (← q r"CARD(J:(B->B)->bool) = e")] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"f1 = 1") SUBST_ALL_TAC THENL [MP_TAC (← SPECL [(← q r"e:num"), (← q r"f1:num"), (← q r"1")] EQ_MULT_LCANCEL) THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MAP_EVERY UNDISCH_TAC [(← q r"CARD(J:(B->B)->bool) = e * f1"), (← q r"CARD(J:(B->B)->bool) = e")] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"e2 = 1") SUBST_ALL_TAC THENL [MP_TAC (← SPECL [(← q r"e:num"), (← q r"e2:num"), (← q r"1")] EQ_MULT_LCANCEL) THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN UNDISCH_TAC (← q r"e:num = e * e2") THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"f2:num = f") SUBST_ALL_TAC THENL [UNDISCH_TAC (← q r"f:num = 1 * f2") THEN ARITH_TAC, ALL_TAC] THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"extension_degree(Mz,Mt) (I:B->B) = f") ASSUME_TAC THENL [MP_TAC (← SPECL [(← q r"e:num"), (← q r"extension_degree(Mz,Mt) (I:B->B)"), (← q r"f:num")] EQ_MULT_LCANCEL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN UNDISCH_TAC (← q r"e * f = extension_degree(Mz,Mt) (I:B->B) * e") THEN ARITH_TAC, ASM_REWRITE_TAC []] THEN SUBGOAL_THEN (← q r"!P. prime_ideal (ring_of_integers l) P /\ Q INTER z SUBSET P <=>
        P = (Q:B->bool)") (LABEL_TAC "uniq") THENL [X_GEN_TAC (← q r"P:B->bool") THEN UNDISCH_TAC (← q r"{P | prime_ideal (ring_of_integers l) P /\ Q INTER z SUBSET P} =
      {Q:B->bool}") THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"(IN) (P:B->bool)"))) THEN REWRITE_TAC [IN_ELIM_THM, IN_SING], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"z:B->bool"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ASM_REWRITE_TAC [] THEN STRIP_TAC] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"Mz:B ring"), (← q r"Mt:B ring"), (← q r"I:B->B"), (← q r"Q INTER (z:B->bool)")] INERT_RESIDUE_DEGREE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN EXPAND_TAC "Mz" THEN REWRITE_TAC [SUBFIELD_GENERATED] THEN ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN EXISTS_TAC (← q r"Q INTER (t:B->bool)") THEN ASM_REWRITE_TAC [IMAGE_I] THEN MP_TAC (← ISPECL [(← q r"I:B->B"), (← q r"Mz:B ring"), (← q r"l:B ring"), (← q r"t:B->bool"), (← q r"Q INTER (z:B->bool)")] NUMBER_FIELD_PRIME_IDEALS_INTERMEDIATE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [IMAGE_I] THEN EXPAND_TAC "Mz" THEN REWRITE_TAC [SUBFIELD_GENERATED] THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC [IMAGE_I] THEN DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM, IN_SING, UNWIND_THM2], MP_TAC (← ISPECL [(← q r"Mt:B ring"), (← q r"l:B ring"), (← q r"I:B->B"), (← q r"Q INTER (t:B->bool)")] TOTALLY_RAMIFIED_RAMIFICATION_INDEX) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN EXISTS_TAC (← q r"Q:B->bool") THEN ASM_REWRITE_TAC [IMAGE_I] THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM, IN_SING] THEN X_GEN_TAC (← q r"P:B->bool") THEN EQ_TAC THENL [STRIP_TAC THEN USE_THEN "uniq" (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN UNDISCH_TAC (← q r"Q INTER t SUBSET (P:B->bool)") THEN UNDISCH_TAC (← q r"(z:B->bool) SUBSET t") THEN SET_TAC [], DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [INTER_SUBSET]]])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_ABELIAN_DECOMPOSITION_GROUP, NUMBER_FIELD_DECOMPOSITION_FIELD,
           NUMBER_FIELD_INERTIA_DECOMPOSITION_TOWER }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- decomposition_field.ml phrases from line 1350 to 1954                  -/
/- ---------------------------------------------------------------------- -/

structure DecompositionField03 where
  -- @@FIELDS
  NUMBER_FIELD_FROBENIUS_ELEMENT_INTERMEDIATE : thm
  NUMBER_FIELD_INTERMEDIATE_FROBENIUS_ORDER : thm
  NUMBER_FIELD_DECOMPOSITION_GROUP_RESTRICTION : thm
  NUMBER_FIELD_FROBENIUS_ELEMENT_RESTRICTION : thm
  NUMBER_FIELD_COMPOSITUM_SPLITTING_TYPES : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDecompositionField03 [HolBase] (D : DecompositionFieldDeps) (BDecompositionField01 : DecompositionField01) :
    ExceptT String IO DecompositionField03 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, INTEGER_RULE, MESON_TAC,
        RING_RULE, SET_TAC, TAUT, .. } := D
  let { CARD_EQ_0, CARD_IMAGE_SUBGROUP_KERNEL, CARD_SUBSET_EQ,
        CARRIER_SUBGROUP_GENERATED_BY_SING, DECOMPOSITION_GROUP,
        DECOMPOSITION_GROUP_CONGRUENT_EQ, DECOMPOSITION_GROUP_INTERMEDIATE,
        DECOMPOSITION_GROUP_POW_CONGRUENCE, DECOMPOSITION_GROUP_RING_OF_INTEGERS,
        EQ_MULT_LCANCEL, EQ_TRANS, FINITE_DECOMPOSITION_INERTIA_GROUPS, FINITE_INTER,
        FORALL_AND_THM, FORALL_IN_IMAGE, FROBENIUS_ELEMENT_IN_DECOMPOSITION_GROUP,
        GALOIS_EXTENSION_SUBFIELD_GENERATED, GALOIS_GROUP, GALOIS_GROUP_I,
        GALOIS_GROUP_IMAGE_NORMAL_INTERMEDIATE,
        GALOIS_GROUP_INTERMEDIATE_SUBGROUP_GENERATED, GALOIS_GROUP_IN_CARRIER,
        GALOIS_GROUP_PERMUTES, GALOIS_GROUP_RESTRICTION, GALOIS_GROUP_RING_OF_INTEGERS,
        GALOIS_IMP_FIELD_EXTENSION, GALOIS_IMP_NORMAL_EXTENSION, GROUP_ID, GROUP_NPOW,
        GROUP_POW, GROUP_POW_MUL, GROUP_POW_SUBGROUP_GENERATED, GROUP_ZPOW_EQ,
        GROUP_ZPOW_MUL, IDEAL_NORM_RESIDUE_DEGREE, IDEAL_NORM_RESIDUE_IMAGE, IMAGE_EQ,
        IMAGE_I, IMAGE_INTER_INJ, INERTIA_GROUP, INTER_SUBSET, INT_OF_NUM_MUL,
        IN_ELIM_THM, IN_INTER, IN_RING_IDEAL_SUB, IN_UNION, IN_UNIV, I_O_ID, .. } := D.core1
  let { MEMBER_NOT_EMPTY, MULT_EQ_1, NUMBER_FIELD_DECOMPOSITION_GROUP,
        NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS, NUMBER_FIELD_FROBENIUS_ELEMENT,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_PRIME_IDEAL_ABOVE,
        NUMBER_FIELD_RAMIFICATION_INDEX_TOWER, NUMBER_FIELD_RESIDUE_DEGREE_TOWER,
        NUMBER_FIELD_TOWER_LAW, NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP,
        PERMUTES_INJECTIVE, PRIME_IMP_RING_IDEAL, RING_HOMOMORPHISM_RING_OF_INTEGERS,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_OF_INTEGERS,
        RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION, RING_OF_INTEGERS_SUBRING,
        RING_OF_INTEGERS_SUBSET, RING_POW, RING_POW_SUBFIELD_GENERATED, RING_SUB,
        RING_SUB_SUBFIELD_GENERATED, SUBFIELD_GENERATED, SUBGROUP_SUBGROUP_GENERATED,
        SUBSET, UNION_SUBSET, decomposition_group, divides, field_extension,
        group_epimorphism, group_homomorphism, group_pow, group_zpow, inertia_group,
        num_divides, .. } := D.core2
  let { NUMBER_FIELD_DECOMPOSITION_GROUP_INTERMEDIATE,
        NUMBER_FIELD_GALOIS_INTERMEDIATE, NUMBER_FIELD_GENERATED_SPLITTING_TYPES,
        NUMBER_FIELD_INTERMEDIATE_FIELD, NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE, .. } := BDecompositionField01
  -- @@SCOPE END

  let NUMBER_FIELD_FROBENIUS_ELEMENT_INTERMEDIATE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_sub r (ring_sub r a c) (ring_sub r b c) = ring_sub r a (b:B)")
    let r13 ← ARITH_RULE (← q r"1 = (n:num) <=> n = 1")
    prove
      r"!(h:A->B) k l s p Q.
          number_field l /\ galois_extension(k,l) h /\
          s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
          ramification_index (ring_of_integers k,ring_of_integers l) h Q = 1
          ==> frobenius_element (subfield_generated l s,l) I
                (ring_of_integers l) Q =
              group_pow (galois_group(k,l) h)
                (frobenius_element (k,l) h (ring_of_integers l) Q)
                (residue_degree
                  (ring_of_integers k,ring_of_integers(subfield_generated l s))
                  h (Q INTER s))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN SUBGOAL_THEN (← q r"finite_extension(k,l) (h:A->B)") ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_TOWER_LAW], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool")] NUMBER_FIELD_INTERMEDIATE_FIELD) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool"), (← q r"Q:B->bool")] DECOMPOSITION_GROUP_INTERMEDIATE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ABBREV_TAC (← q r"M = subfield_generated l (s:B->bool)") THEN SUBGOAL_THEN (← q r"galois_extension(M,l) (I:B->B)") ASSUME_TAC THENL [EXPAND_TAC "M" THEN MATCH_MP_TAC GALOIS_EXTENSION_SUBFIELD_GENERATED THEN MAP_EVERY EXISTS_TAC [(← q r"h:A->B"), (← q r"k:A ring")] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(Q INTER s = {ring_0(M:B ring)})") ASSUME_TAC THENL [EXPAND_TAC "M" THEN REWRITE_TAC [SUBFIELD_GENERATED] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ramification_index (ring_of_integers M,ring_of_integers l) (I:B->B) Q = 1") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"M:B ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"I:B->B"), (← q r"Q INTER (s:B->bool)"), (← q r"Q:B->bool")] NUMBER_FIELD_RAMIFICATION_INDEX_TOWER) THEN ASM_REWRITE_TAC [I_O_ID, IMAGE_I, INTER_SUBSET] THEN REWRITE_TAC [r13, MULT_EQ_1] THEN SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_FROBENIUS_ELEMENT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fk") (fun (_ : thm) => ALL_TAC)))] THEN MP_TAC (← ISPECL [(← q r"I:B->B"), (← q r"M:B ring"), (← q r"l:B ring"), (← q r"Q INTER (s:B->bool)"), (← q r"Q:B->bool")] NUMBER_FIELD_FROBENIUS_ELEMENT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [IMAGE_I, INTER_SUBSET], DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fm") (fun (_ : thm) => ALL_TAC)))] THEN ABBREV_TAC (← q r"fk = frobenius_element (k,l) (h:A->B) (ring_of_integers l) Q") THEN ABBREV_TAC (← q r"fm = frobenius_element (M,l) (I:B->B) (ring_of_integers l) Q") THEN ABBREV_TAC (← q r"d = residue_degree (ring_of_integers k,ring_of_integers M) (h:A->B)
            (Q INTER s)") THEN SUBGOAL_THEN (← q r"ideal_norm (ring_of_integers M) ((Q:B->bool) INTER s) =
      ideal_norm (ring_of_integers k) (p:A->bool) EXP d") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"M:B ring"), (← q r"p:A->bool"), (← q r"Q INTER (s:B->bool)")] NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"M:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"Q INTER (s:B->bool)")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN EXPAND_TAC "d" THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers M:B ring"), (← q r"h:A->B"), (← q r"Q INTER (s:B->bool)")] IDEAL_NORM_RESIDUE_DEGREE) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS], DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []], ALL_TAC] THEN ABBREV_TAC (← q r"g = group_pow (galois_group(k,l) (h:A->B)) fk d") THEN SUBGOAL_THEN (← q r"g IN group_carrier(decomposition_group(k,l) (h:A->B) Q)") ASSUME_TAC THENL [EXPAND_TAC "g" THEN SUBGOAL_THEN (← q r"group_pow (galois_group(k,l) h) fk d =
        group_pow (decomposition_group(k,l) (h:A->B) Q) fk d") SUBST1_TAC THENL [REWRITE_TAC [decomposition_group, GROUP_POW_SUBGROUP_GENERATED], MATCH_MP_TAC GROUP_POW THEN FIRST_ASSUM ACCEPT_TAC], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x. x IN ring_carrier(ring_of_integers l)
          ==> ring_sub l ((g:B->B) x)
                (ring_pow l x (ideal_norm (ring_of_integers M) (Q INTER s))) IN
              Q") (LABEL_TAC "gc") THENL [ASM_REWRITE_TAC [] THEN EXPAND_TAC "g" THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"fk:B->B"), (← q r"ideal_norm (ring_of_integers k) (p:A->bool)")] DECOMPOSITION_GROUP_POW_CONGRUENCE) THEN ANTS_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING, GALOIS_GROUP_RING_OF_INTEGERS] THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN USE_THEN "fk" (MP_TAC o (SPEC (← q r"fk:B->B"))) THEN REWRITE_TAC [] THEN SIMP_TAC [], DISCH_THEN (ACCEPT_TAC o (SPEC (← q r"d:num")))], ALL_TAC] THEN SUBGOAL_THEN (← q r"fm IN group_carrier(decomposition_group(k,l) (h:A->B) Q)") ASSUME_TAC THENL [FIRST_X_ASSUM (MP_TAC o ((AP_TERM (← q r"(IN) (fm:B->B)")) o (checkM (fun th => (do if ← (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_eq z2)) then (do let z4 ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); liftExcept (lhs z5)); pure (is_comb z4)) else pure false) then (do let z12 ← (pure "group_carrier"); let z11 ← (do pure (Prod.fst (← (do let z7 ← (do let z8 ← (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); liftExcept (lhs z9)); liftExcept (rator z8)); liftExcept (dest_const z7))))); pure (z11 == z12)) else pure false))))) THEN ASM_REWRITE_TAC [IN_INTER] THEN SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q) = {I}") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"fm:B->B"), (← q r"g:B->B")] DECOMPOSITION_GROUP_CONGRUENT_EQ) THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING, GALOIS_GROUP_RING_OF_INTEGERS] THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier l") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"l:B ring") RING_OF_INTEGERS_SUBSET) THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"(fm:B->B) IN group_carrier(galois_group(k,l) (h:A->B)) /\
      (g:B->B) IN group_carrier(galois_group(k,l) h)") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"fm IN group_carrier(decomposition_group(k,l) (h:A->B) Q)") THEN UNDISCH_TAC (← q r"g IN group_carrier(decomposition_group(k,l) (h:A->B) Q)") THEN REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"fm:B->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"x:B")] GALOIS_GROUP_IN_CARRIER) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"g:B->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"x:B")] GALOIS_GROUP_IN_CARRIER) THEN ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN REMOVE_THEN "fm" (MP_TAC o (SPEC (← q r"fm:B->B"))) THEN REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"x:B")) o CONJUNCT2)) THEN REMOVE_THEN "gc" (MP_TAC o (SPEC (← q r"x:B"))) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"c = ring_pow l (x:B) (ideal_norm (ring_of_integers k) (p:A->bool) EXP d)") THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN (← q r"(c:B) IN ring_carrier l") ASSUME_TAC THENL [EXPAND_TAC "c" THEN ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub l ((fm:B->B) x) (g x) =
      ring_sub l (ring_sub l (fm x) c) (ring_sub l (g x) c)") SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"ring_sub l ((fm:B->B) x) c"), (← q r"ring_sub l ((g:B->B) x) c")] IN_RING_IDEAL_SUB) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS])

  let NUMBER_FIELD_INTERMEDIATE_FROBENIUS_ORDER ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r16 ← ARITH_RULE (← q r"1 = (n:num) <=> n = 1")
    prove
      r"!(h:A->B) k l s p Q.
          number_field l /\ galois_extension(k,l) h /\
          s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
          ramification_index (ring_of_integers k,ring_of_integers l) h Q = 1
          ==> ramification_index
                (ring_of_integers k,ring_of_integers(subfield_generated l s)) h
                (Q INTER s) = 1 /\
              !d. group_pow (galois_group(k,l) h)
                    (frobenius_element (k,l) h (ring_of_integers l) Q) d IN
                  group_carrier(galois_group(subfield_generated l s,l) I) <=>
                  residue_degree
                    (ring_of_integers k,ring_of_integers(subfield_generated l s))
                    h (Q INTER s) divides d"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN SUBGOAL_THEN (← q r"finite_extension(k,l) (h:A->B)") ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_TOWER_LAW], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool")] NUMBER_FIELD_INTERMEDIATE_FIELD) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool"), (← q r"Q:B->bool")] DECOMPOSITION_GROUP_INTERMEDIATE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool")] GALOIS_GROUP_INTERMEDIATE_SUBGROUP_GENERATED) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_FROBENIUS_ELEMENT_INTERMEDIATE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ABBREV_TAC (← q r"M = subfield_generated l (s:B->bool)") THEN SUBGOAL_THEN (← q r"galois_extension(M,l) (I:B->B)") ASSUME_TAC THENL [EXPAND_TAC "M" THEN MATCH_MP_TAC GALOIS_EXTENSION_SUBFIELD_GENERATED THEN MAP_EVERY EXISTS_TAC [(← q r"h:A->B"), (← q r"k:A ring")] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(Q INTER s = {ring_0(M:B ring)})") ASSUME_TAC THENL [EXPAND_TAC "M" THEN REWRITE_TAC [SUBFIELD_GENERATED] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"M:B ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"I:B->B"), (← q r"Q INTER (s:B->bool)"), (← q r"Q:B->bool")] NUMBER_FIELD_RAMIFICATION_INDEX_TOWER) THEN ASM_REWRITE_TAC [I_O_ID, IMAGE_I, INTER_SUBSET] THEN REWRITE_TAC [r16, MULT_EQ_1] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"M:B ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"I:B->B"), (← q r"Q INTER (s:B->bool)"), (← q r"Q:B->bool")] NUMBER_FIELD_RESIDUE_DEGREE_TOWER) THEN ASM_REWRITE_TAC [I_O_ID, IMAGE_I, INTER_SUBSET] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:B->B"), (← q r"M:B ring"), (← q r"l:B ring"), (← q r"Q INTER (s:B->bool)"), (← q r"Q:B->bool")] NUMBER_FIELD_DECOMPOSITION_GROUP_FROBENIUS) THEN ASM_REWRITE_TAC [IMAGE_I, INTER_SUBSET] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_FROBENIUS_ELEMENT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"I:B->B"), (← q r"M:B ring"), (← q r"l:B ring"), (← q r"Q INTER (s:B->bool)"), (← q r"Q:B->bool")] NUMBER_FIELD_FROBENIUS_ELEMENT) THEN ASM_REWRITE_TAC [IMAGE_I, INTER_SUBSET] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN ABBREV_TAC (← q r"fk = frobenius_element (k,l) (h:A->B) (ring_of_integers l) Q") THEN ABBREV_TAC (← q r"fm = frobenius_element (M,l) (I:B->B) (ring_of_integers l) Q") THEN ABBREV_TAC (← q r"m = residue_degree (ring_of_integers k,ring_of_integers M) (h:A->B)
            (Q INTER s)") THEN ABBREV_TAC (← q r"G = galois_group(k,l) (h:A->B)") THEN SUBGOAL_THEN (← q r"(fk:B->B) IN group_carrier G") ASSUME_TAC THENL [UNDISCH_TAC (← q r"fk IN group_carrier(decomposition_group(k,l) (h:A->B) Q)") THEN EXPAND_TAC "G" THEN REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"group_pow G (fk:B->B) m IN group_carrier(galois_group(M,l) I)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"group_pow G (fk:B->B) m IN
        group_carrier(decomposition_group(k,l) (h:A->B) Q) INTER
        group_carrier(galois_group(M,l) I)") THEN REWRITE_TAC [IN_INTER] THEN SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!(x:B->B) n. group_pow (galois_group(M,l) I) x n = group_pow G x n") ASSUME_TAC THENL [EXPAND_TAC "G" THEN GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [group_pow, GALOIS_GROUP], ALL_TAC] THEN SUBGOAL_THEN (← q r"!(x:B->B) n. group_zpow (galois_group(M,l) I) x n = group_zpow G x n") ASSUME_TAC THENL [ASM_REWRITE_TAC [group_zpow] THEN EXPAND_TAC "G" THEN REWRITE_TAC [GALOIS_GROUP], ALL_TAC] THEN X_GEN_TAC (← q r"d:num") THEN EQ_TAC THENL [DISCH_TAC THEN SUBGOAL_THEN (← q r"group_pow G (fk:B->B) d IN
        group_carrier(decomposition_group(k,l) (h:A->B) Q) INTER
        group_carrier(galois_group(M,l) I)") MP_TAC THENL [ASM_REWRITE_TAC [IN_INTER] THEN SUBGOAL_THEN (← q r"group_pow G (fk:B->B) d =
          group_pow (decomposition_group(k,l) (h:A->B) Q) fk d") SUBST1_TAC THENL [EXPAND_TAC "G" THEN REWRITE_TAC [decomposition_group, GROUP_POW_SUBGROUP_GENERATED], MATCH_MP_TAC GROUP_POW THEN FIRST_ASSUM ACCEPT_TAC], ALL_TAC] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z10 ← (do let z11 ← (pure th); pure (concl z11)); pure (is_eq z10)) then (do let z15 ← (q r"group_carrier(subgroup_generated (galois_group(M,l) (I:B->B))                          {group_pow G (fk:B->B) m})"); let z14 ← (do let z12 ← (do let z13 ← (pure th); pure (concl z13)); liftExcept (lhs z12)); pure (z14 == z15)) else pure false))))) THEN MP_TAC (← ISPECL [(← q r"galois_group(M,l) (I:B->B)"), (← q r"group_pow G (fk:B->B) m")] CARRIER_SUBGROUP_GENERATED_BY_SING) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"j:int")) THEN SUBGOAL_THEN (← q r"group_zpow G (fk:B->B) (&d) = group_zpow G fk (&m * j)") MP_TAC THENL [ASM_SIMP_TAC [GROUP_ZPOW_MUL, GROUP_NPOW], ASM_SIMP_TAC [GROUP_ZPOW_EQ]] THEN REWRITE_TAC [num_divides, (← GSYM INT_OF_NUM_MUL)] THEN CONV_TAC INTEGER_RULE, REWRITE_TAC [divides] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"j:num") SUBST1_TAC) THEN ASM_SIMP_TAC [GROUP_POW_MUL] THEN FIRST_X_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [(← GSYM th)])) o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); canM (fun z5 => (do let z6 ← (pure z5); find_termM (fun z7 => (do let z9 ← (pure z7); let z8 ← (q r"group_pow:(B->B)group->(B->B)->num->B->B"); pure (z8 == z9))) z6)) z3) else pure false)))) THEN MATCH_MP_TAC GROUP_POW THEN FIRST_ASSUM ACCEPT_TAC])

  let NUMBER_FIELD_DECOMPOSITION_GROUP_RESTRICTION ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"c:num"
    let q2 ← q r"a:num"
    let q3 ← q r"b:num"
    let v4 ← SPECL [q3, q2, q1] EQ_MULT_LCANCEL
    let p5 ← prove r"!a b c d:num. a * b = d /\ b * c = d /\ ~(b = 0) ==> a = c" (REPEAT STRIP_TAC THEN MP_TAC v4 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_ARITH_TAC)
    let cancel := p5
    let q6 ← q r"CARD(group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q))"
    let q7 ← q r"CARD(group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q)
           INTER group_carrier(galois_group(M,l) I))"
    let v8 ← GSYM inertia_group
    let q9 ← q r"group_carrier(inertia_group(k,l) (h:A->B)
                                   (ring_of_integers l) Q)"
    let q10 ← q r"rho:(B->B)->B->B"
    let q11 ← q r"galois_group(k,M) (h:A->B)"
    let q12 ← q r"galois_group(k,l) (h:A->B)"
    let v13 ← ISPECL [q12, q11, q10, q9] CARD_IMAGE_SUBGROUP_KERNEL
    let q14 ← q r"x:B"
    let q15 ← q r"(f:B->B) x"
    let q16 ← q r"M:B ring"
    let v17 ← ISPECL [q16, q15, q14] RING_SUB
    let q18 ← q r"(x:B) IN s /\ x IN ring_carrier(ring_of_integers l)"
    let q19 ← q r"x:B"
    let q29 ← q r"f:B->B"
    let q30 ← q r"f:B->B"
    let v31 ← CONJUNCT1 INERTIA_GROUP
    let q32 ← q r"Q:B->bool"
    let q33 ← q r"ring_of_integers l:B ring"
    let q34 ← q r"l:B ring"
    let q35 ← q r"k:A ring"
    let q36 ← q r"h:A->B"
    let v37 ← ISPECL [q36, q35, q34, q33, q32] v31
    let v38 ← CONJUNCT1 INERTIA_GROUP
    let q39 ← q r"Q INTER (s:B->bool)"
    let q40 ← q r"ring_of_integers M:B ring"
    let q41 ← q r"M:B ring"
    let q42 ← q r"k:A ring"
    let q43 ← q r"h:A->B"
    let v44 ← ISPECL [q43, q42, q41, q40, q39] v38
    let q45 ← q r"CARD(group_carrier(decomposition_group(k,l) (h:A->B) Q))"
    let q46 ← q r"CARD(group_carrier(decomposition_group(k,l) (h:A->B) Q) INTER
           group_carrier(galois_group(M,l) I))"
    let v47 ← GSYM decomposition_group
    let q48 ← q r"group_carrier(decomposition_group(k,l) (h:A->B) Q)"
    let q49 ← q r"rho:(B->B)->B->B"
    let q50 ← q r"galois_group(k,M) (h:A->B)"
    let q51 ← q r"galois_group(k,l) (h:A->B)"
    let v52 ← ISPECL [q51, q50, q49, q48] CARD_IMAGE_SUBGROUP_KERNEL
    let q62 ← q r"f:B->B"
    let q63 ← q r"f:B->B"
    let q64 ← q r"I:B->B"
    let v65 ← GSYM MEMBER_NOT_EMPTY
    let q66 ← q r"~(CARD(group_carrier(decomposition_group(k,l) (h:A->B) Q) INTER
           group_carrier(galois_group(M,l) I)) = 0) /\
    ~(CARD(group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q)
           INTER group_carrier(galois_group(M,l) I)) = 0)"
    let q67 ← q r"Q INTER (s:B->bool)"
    let q68 ← q r"ring_of_integers M:B ring"
    let q69 ← q r"M:B ring"
    let q70 ← q r"k:A ring"
    let q71 ← q r"h:A->B"
    let v72 ← ISPECL [q71, q70, q69, q68, q67] FINITE_DECOMPOSITION_INERTIA_GROUPS
    let q73 ← q r"Q:B->bool"
    let q74 ← q r"ring_of_integers l:B ring"
    let q75 ← q r"l:B ring"
    let q76 ← q r"k:A ring"
    let q77 ← q r"h:A->B"
    let v78 ← ISPECL [q77, q76, q75, q74, q73] FINITE_DECOMPOSITION_INERTIA_GROUPS
    let q79 ← q r"Q:B->bool"
    let q80 ← q r"p:A->bool"
    let q81 ← q r"s:B->bool"
    let q82 ← q r"l:B ring"
    let q83 ← q r"k:A ring"
    let q84 ← q r"h:A->B"
    let v85 ← ISPECL [q84, q83, q82, q81, q80, q79] NUMBER_FIELD_DECOMPOSITION_GROUP_INTERMEDIATE
    let q86 ← q r"Q INTER (s:B->bool)"
    let q87 ← q r"p:A->bool"
    let q88 ← q r"M:B ring"
    let q89 ← q r"k:A ring"
    let q90 ← q r"h:A->B"
    let v91 ← ISPECL [q90, q89, q88, q87, q86] NUMBER_FIELD_DECOMPOSITION_GROUP
    let q92 ← q r"finite_extension(k,M) (h:A->B)"
    let q93 ← q r"IMAGE (f:B->B) (Q INTER s)"
    let q94 ← q r"k:A ring"
    let q95 ← q r"h:A->B"
    let q96 ← q r"ring_carrier(l:B ring)"
    let q97 ← q r"!x y. (f:B->B) x = f y <=> x = y"
    let q98 ← q r"group_homomorphism (galois_group(k,l) (h:A->B),galois_group(k,M) h)
          (rho:(B->B)->B->B)"
    let q99 ← q r"p /\ q /\ (q ==> r) ==> p /\ q /\ r"
    let r100 ← TAUT q99
    let q101 ← q r"l:B ring"
    let q102 ← q r"k:A ring"
    let q103 ← q r"h:A->B"
    let q104 ← q r"IMAGE (f:B->B) s = s"
    let q105 ← q r"f:B->B"
    let q106 ← q r"!f. f IN group_carrier(galois_group(k,l) (h:A->B))
        ==> rho f IN group_carrier(galois_group(k,M) h) /\
            IMAGE f s = s /\
            (!x. x IN s ==> (rho:(B->B)->B->B) f x = f x) /\
            IMAGE (rho f) (Q INTER s) = IMAGE f Q INTER s"
    let q107 ← q r"M = subfield_generated l (s:B->bool)"
    let q108 ← q r"rho = \f (x:B). if x IN s then f x else x"
    let q109 ← q r"s:B->bool"
    let q110 ← q r"l:B ring"
    let q111 ← q r"k:A ring"
    let q112 ← q r"h:A->B"
    let v113 ← ISPECL [q112, q111, q110, q109] GALOIS_GROUP_RESTRICTION
    let q114 ← q r"Q:B->bool"
    let q115 ← q r"p:A->bool"
    let q116 ← q r"s:B->bool"
    let q117 ← q r"l:B ring"
    let q118 ← q r"k:A ring"
    let q119 ← q r"h:A->B"
    let v120 ← ISPECL [q119, q118, q117, q116, q115, q114] NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE
    let q121 ← q r"s:B->bool"
    let q122 ← q r"l:B ring"
    let q123 ← q r"k:A ring"
    let q124 ← q r"h:A->B"
    let v125 ← ISPECL [q124, q123, q122, q121] NUMBER_FIELD_INTERMEDIATE_FIELD
    let q126 ← q r"s:B->bool"
    let q127 ← q r"l:B ring"
    let q128 ← q r"k:A ring"
    let q129 ← q r"h:A->B"
    let v130 ← ISPECL [q129, q128, q127, q126] NUMBER_FIELD_GALOIS_INTERMEDIATE
    let q131 ← q r"finite_extension(k,l) (h:A->B)"
    let q132 ← q r"field k /\ ring_homomorphism(k,l) (h:A->B)"
    prove
      r"!(h:A->B) k l s p Q.
          number_field l /\ galois_extension(k,l) h /\
          s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
          normal_extension(k,subfield_generated l s) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
          ==> IMAGE (\f x. if x IN s then f x else x)
                    (group_carrier(decomposition_group(k,l) h Q)) =
              group_carrier(decomposition_group(k,subfield_generated l s) h
                              (Q INTER s)) /\
              IMAGE (\f x. if x IN s then f x else x)
                    (group_carrier(inertia_group(k,l) h (ring_of_integers l) Q)) =
              group_carrier(inertia_group(k,subfield_generated l s) h
                              (ring_of_integers(subfield_generated l s))
                              (Q INTER s))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN q132 STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN SUBGOAL_THEN q131 ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_TOWER_LAW], ALL_TAC] THEN MP_TAC v130 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN MP_TAC v125 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC v120 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC v113 THEN ANTS_TAC THENL [ASM_SIMP_TAC [GALOIS_IMP_NORMAL_EXTENSION], ALL_TAC] THEN REWRITE_TAC [group_epimorphism] THEN STRIP_TAC THEN ABBREV_TAC q108 THEN ABBREV_TAC q107 THEN SUBGOAL_THEN q106 ASSUME_TAC THENL [X_GEN_TAC q105 THEN DISCH_TAC THEN SUBGOAL_THEN q104 ASSUME_TAC THENL [MATCH_MP_TAC GALOIS_GROUP_IMAGE_NORMAL_INTERMEDIATE THEN MAP_EVERY EXISTS_TAC [q103, q102, q101] THEN EXPAND_TAC "M" THEN ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r100 THEN REPEAT CONJ_TAC THENL [UNDISCH_TAC q98 THEN REWRITE_TAC [group_homomorphism, SUBSET, FORALL_IN_IMAGE] THEN ASM_SIMP_TAC [], EXPAND_TAC "rho" THEN SIMP_TAC [], DISCH_TAC THEN SUBGOAL_THEN q97 ASSUME_TAC THENL [MATCH_MP_TAC PERMUTES_INJECTIVE THEN EXISTS_TAC q96 THEN MATCH_MP_TAC GALOIS_GROUP_PERMUTES THEN MAP_EVERY EXISTS_TAC [q95, q94] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN TRANS_TAC EQ_TRANS q93 THEN CONJ_TAC THENL [MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC [IN_INTER], ASM_SIMP_TAC [IMAGE_INTER_INJ]]], ALL_TAC] THEN SUBGOAL_THEN q92 ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_TOWER_LAW], ALL_TAC] THEN MP_TAC v91 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN EXPAND_TAC "M" THEN REWRITE_TAC [SUBFIELD_GENERATED] THEN ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC v85 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ASM_REWRITE_TAC [] THEN STRIP_TAC] THEN MP_TAC v78 THEN MP_TAC v72 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN SUBGOAL_THEN q66 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [CARD_EQ_0, FINITE_INTER, v65] THEN CONJ_TAC THEN EXISTS_TAC q64 THEN REWRITE_TAC [IN_INTER, GALOIS_GROUP_I] THEN MESON_TAC [GROUP_ID, DECOMPOSITION_GROUP, INERTIA_GROUP], ALL_TAC] THEN CONJ_TAC THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC [] THENL [CONJ_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, DECOMPOSITION_GROUP, IN_ELIM_THM] THEN X_GEN_TAC q63 THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q62) o (checkM (fun th => (do if ← (do let z53 ← (do let z54 ← (pure th); pure (concl z54)); pure (is_forall z53)) then (do let z55 ← (do let z56 ← (pure th); pure (concl z56)); canM (fun z57 => (do let z58 ← (pure z57); find_termM (fun z59 => (do let z61 ← (pure z59); let z60 ← (q r"rho:(B->B)->B->B"); pure (z60 == z61))) z58)) z55) else pure false))))) THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC v52 THEN ASM_REWRITE_TAC [decomposition_group, SUBGROUP_SUBGROUP_GENERATED] THEN REWRITE_TAC [v47] THEN DISCH_TAC THEN MATCH_MP_TAC cancel THEN EXISTS_TAC q46 THEN EXISTS_TAC q45 THEN ASM_REWRITE_TAC [], CONJ_TAC THENL [MP_TAC v44 THEN ANTS_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING, DECOMPOSITION_GROUP_RING_OF_INTEGERS] THEN MATCH_MP_TAC PRIME_IMP_RING_IDEAL THEN FIRST_ASSUM ACCEPT_TAC, DISCH_THEN SUBST1_TAC] THEN MP_TAC v37 THEN ANTS_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING, DECOMPOSITION_GROUP_RING_OF_INTEGERS] THEN MATCH_MP_TAC PRIME_IMP_RING_IDEAL THEN FIRST_ASSUM ACCEPT_TAC, DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN X_GEN_TAC q30 THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q29) o (checkM (fun th => (do if ← (do let z20 ← (do let z21 ← (pure th); pure (concl z21)); pure (is_forall z20)) then (do let z22 ← (do let z23 ← (pure th); pure (concl z23)); canM (fun z24 => (do let z25 ← (pure z24); find_termM (fun z26 => (do let z28 ← (pure z26); let z27 ← (q r"rho:(B->B)->B->B"); pure (z27 == z28))) z25)) z22) else pure false))))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC q19 THEN DISCH_TAC THEN SUBGOAL_THEN q18 STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [] THEN EXPAND_TAC "M" THEN REWRITE_TAC [RING_SUB_SUBFIELD_GENERATED, IN_INTER] THEN ASM_SIMP_TAC [] THEN MP_TAC v17 THEN ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN EXPAND_TAC "M" THEN REWRITE_TAC [RING_SUB_SUBFIELD_GENERATED] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC v13 THEN ASM_REWRITE_TAC [inertia_group, SUBGROUP_SUBGROUP_GENERATED] THEN REWRITE_TAC [v8] THEN DISCH_TAC THEN MATCH_MP_TAC cancel THEN EXISTS_TAC q7 THEN EXISTS_TAC q6 THEN ASM_REWRITE_TAC []])

  let NUMBER_FIELD_FROBENIUS_ELEMENT_RESTRICTION ← prove
    r"!(h:A->B) k l s p Q.
        number_field l /\ galois_extension(k,l) h /\
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
        normal_extension(k,subfield_generated l s) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
        ramification_index
         (ring_of_integers k,ring_of_integers(subfield_generated l s)) h
         (Q INTER s) = 1
        ==> (\x. if x IN s
                 then frobenius_element (k,l) h (ring_of_integers l) Q x
                 else x) =
            frobenius_element (k,subfield_generated l s) h
              (ring_of_integers(subfield_generated l s)) (Q INTER s)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN SUBGOAL_THEN (← q r"finite_extension(k,l) (h:A->B)") ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_TOWER_LAW], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool")] NUMBER_FIELD_GALOIS_INTERMEDIATE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool")] NUMBER_FIELD_INTERMEDIATE_FIELD) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool")] FROBENIUS_ELEMENT_IN_DECOMPOSITION_GROUP) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING, GALOIS_GROUP_RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] IDEAL_NORM_RESIDUE_IMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN ABBREV_TAC (← q r"fr = frobenius_element (k,l) (h:A->B) (ring_of_integers l) Q") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"subfield_generated l (s:B->bool)"), (← q r"p:A->bool"), (← q r"Q INTER (s:B->bool)")] NUMBER_FIELD_FROBENIUS_ELEMENT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBFIELD_GENERATED] THEN ASM_REWRITE_TAC [], DISCH_THEN (MP_TAC o (CONJUNCT1 o CONJUNCT2))] THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool")] GALOIS_GROUP_RESTRICTION) THEN ANTS_TAC THENL [ASM_SIMP_TAC [GALOIS_IMP_NORMAL_EXTENSION], ALL_TAC] THEN REWRITE_TAC [group_epimorphism, group_homomorphism, SUBSET, FORALL_IN_IMAGE] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"fr:B->B")) o (CONJUNCT1 o (CONJUNCT1 o CONJUNCT1)))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:B) IN s /\ x IN ring_carrier(ring_of_integers l)") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [RING_SUB_SUBFIELD_GENERATED, RING_POW_SUBFIELD_GENERATED, IN_INTER] THEN CONJ_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(fr:B->B) x IN s") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"fr:B->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool")] GALOIS_GROUP_IMAGE_NORMAL_INTERMEDIATE) THEN ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD] THEN ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"subfield_generated l (s:B->bool)"), (← q r"(fr:B->B) x"), (← q r"ring_pow (subfield_generated l s) (x:B)
                    (ideal_norm (ring_of_integers k) (p:A->bool))")] RING_SUB) THEN ASM_REWRITE_TAC [RING_SUB_SUBFIELD_GENERATED, RING_POW_SUBFIELD_GENERATED] THEN DISCH_THEN MATCH_MP_TAC THEN MP_TAC (← ISPECL [(← q r"subfield_generated l (s:B->bool)"), (← q r"x:B"), (← q r"ideal_norm (ring_of_integers k) (p:A->bool)")] RING_POW) THEN ASM_REWRITE_TAC [RING_POW_SUBFIELD_GENERATED])

  let NUMBER_FIELD_COMPOSITUM_SPLITTING_TYPES ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(a /\ b /\ c /\ (d \/ e) ==> f) <=>
    (a /\ b /\ c /\ d ==> f) /\ (a /\ b /\ c /\ e ==> f)")
    prove
      r"!(h:A->B) k l s t p.
          number_field l /\ galois_extension(k,l) h /\
          s SUBSET ring_carrier l /\ t SUBSET ring_carrier l /\
          IMAGE h (ring_carrier k) SUBSET s /\
            IMAGE h (ring_carrier k) SUBSET t /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
          ==> (unramified
                (ring_of_integers k,
                 ring_of_integers(subfield_generated l (s UNION t))) h p <=>
               unramified
                (ring_of_integers k,ring_of_integers(subfield_generated l s)) h
                p /\
               unramified
                (ring_of_integers k,ring_of_integers(subfield_generated l t)) h
                p) /\
              (totally_split
                (ring_of_integers k,
                 ring_of_integers(subfield_generated l (s UNION t))) h p <=>
               totally_split
                (ring_of_integers k,ring_of_integers(subfield_generated l s)) h
                p /\
               totally_split
                (ring_of_integers k,ring_of_integers(subfield_generated l t)) h
                p)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"IMAGE (h:A->B) (ring_carrier k) SUBSET s UNION t") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s UNION t:B->bool"), (← q r"p:A->bool")] NUMBER_FIELD_GENERATED_SPLITTING_TYPES) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [UNION_SUBSET], DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC)] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"t:B->bool"), (← q r"p:A->bool")] NUMBER_FIELD_GENERATED_SPLITTING_TYPES) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC)] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool"), (← q r"p:A->bool")] NUMBER_FIELD_GENERATED_SPLITTING_TYPES) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC)] THEN REWRITE_TAC [IN_UNION, r1] THEN REWRITE_TAC [FORALL_AND_THM])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_FROBENIUS_ELEMENT_INTERMEDIATE,
           NUMBER_FIELD_INTERMEDIATE_FROBENIUS_ORDER,
           NUMBER_FIELD_DECOMPOSITION_GROUP_RESTRICTION,
           NUMBER_FIELD_FROBENIUS_ELEMENT_RESTRICTION,
           NUMBER_FIELD_COMPOSITUM_SPLITTING_TYPES }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- decomposition_field.ml phrases from line 2000 to 2134                  -/
/- ---------------------------------------------------------------------- -/

structure DecompositionField04 where
  -- @@FIELDS
  NUMBER_FIELD_NORMAL_CLOSURE_SPLITTING_TYPES : thm
  NUMBER_FIELD_UNRAMIFIED_INERTIA_FIXED_FIELD : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDecompositionField04 [HolBase] (D : DecompositionFieldDeps) (BDecompositionField01 : DecompositionField01) :
    ExceptT String IO DecompositionField04 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, SET_TAC, .. } := D
  let { DECOMPOSITION_GROUP_CONJUGATE, EXISTS_IN_GSPEC, EXISTS_UNIQUE_THM,
        FIXED_FIELD_SUBGROUP_GENERATED, FORALL_IN_GSPEC, FORALL_IN_IMAGE,
        GALOIS_GROUP_FIXES, GALOIS_GROUP_I, GALOIS_GROUP_INVERSE,
        GALOIS_GROUP_PERMUTES, GALOIS_GROUP_PRIME_IDEAL_IMAGE,
        GALOIS_GROUP_RING_OF_INTEGERS, GALOIS_IMP_FIELD_EXTENSION,
        GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET, IMAGE_I, INERTIA_GROUP_CONJUGATE,
        IN_ELIM_THM, IN_FIXED_FIELD, IN_IMAGE, IN_UNIONS, .. } := D.core1
  let { NUMBER_FIELD_PRIME_IDEAL_ABOVE, PERMUTES_IMAGE, PERMUTES_INVERSES,
        PERMUTES_INVERSE_INVERSE, PRIME_IDEAL_IMP_SUBSET, PRIME_IMP_RING_IDEAL,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_OF_INTEGERS_PRIME_IDEAL_BELOW,
        RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET, SUBSET, SUBSET_TRANS,
        UNIONS_SUBSET, decomposition_group, field_extension, inertia_group, o_THM, .. } := D.core2
  let { NUMBER_FIELD_GENERATED_SPLITTING_TYPES, .. } := BDecompositionField01
  -- @@SCOPE END

  let NUMBER_FIELD_NORMAL_CLOSURE_SPLITTING_TYPES ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"f:B->B"
    let q2 ← q r"g:B->B"
    let q10 ← q r"inverse(f:B->B)"
    let q11 ← q r"Q:B->bool"
    let q21 ← q r"y:B"
    let q22 ← q r"inverse(f:B->B) o g o f"
    let q23 ← q r"IMAGE (inverse(f:B->B)) Q"
    let q24 ← q r"k:A ring"
    let v25 ← ISPEC q24 RING_OF_INTEGERS_SUBSET
    let q26 ← q r"p:A->bool"
    let q27 ← q r"ring_of_integers k:A ring"
    let v28 ← ISPECL [q27, q26] PRIME_IDEAL_IMP_SUBSET
    let q29 ← q r"l:B ring"
    let q30 ← q r"k:A ring"
    let v31 ← GSYM GALOIS_GROUP_FIXES
    let q32 ← q r"(h:A->B) a"
    let q33 ← q r"a:A"
    let q34 ← q r"IMAGE (h:A->B) p SUBSET Q"
    let q35 ← q r"Q:B->bool"
    let q36 ← q r"inverse(f:B->B)"
    let q37 ← q r"ring_of_integers l:B ring"
    let q38 ← q r"l:B ring"
    let q39 ← q r"k:A ring"
    let q40 ← q r"h:A->B"
    let v41 ← ISPECL [q40, q39, q38, q37, q36, q35] GALOIS_GROUP_PRIME_IDEAL_IMAGE
    let q42 ← q r"prime_ideal (ring_of_integers l) (IMAGE (inverse(f:B->B)) Q) /\
      IMAGE (h:A->B) p SUBSET IMAGE (inverse f) Q"
    let q43 ← q r"inverse(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))"
    let q47 ← q r"y:B"
    let q48 ← q r"f:B->B"
    let q49 ← q r"(x:B) IN UNIONS {IMAGE f s |
                       f IN group_carrier(galois_group(k,l) (h:A->B))}"
    let q50 ← q r"x:B"
    let q51 ← q r"g:B->B"
    let q52 ← q r"Q:B->bool"
    let q53 ← q r"I:B->B"
    let q54 ← q r"Q:B->bool"
    let p55 ← prove r"!(h:A->B) k l s p (H:(B->bool)->(B->B)->bool).
        number_field l /\ galois_extension(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        (!Q. prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
             ==> H Q SUBSET group_carrier(galois_group(k,l) h)) /\
        (!Q f. prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
               f IN group_carrier(galois_group(k,l) h)
               ==> H(IMAGE f Q) = IMAGE (\g. f o g o inverse f) (H Q))
        ==> ((!Q g x. prime_ideal (ring_of_integers l) Q /\
                      IMAGE h p SUBSET Q /\ g IN H Q /\
                      x IN UNIONS {IMAGE f s |
                                   f IN group_carrier(galois_group(k,l) h)}
                      ==> g x = x) <=>
             (!Q g x. prime_ideal (ring_of_integers l) Q /\
                      IMAGE h p SUBSET Q /\ g IN H Q /\ x IN s
                      ==> g x = x))" (REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC q54 THEN ASM_REWRITE_TAC [IN_UNIONS, EXISTS_IN_GSPEC] THEN EXISTS_TAC q53 THEN ASM_REWRITE_TAC [GALOIS_GROUP_I, IMAGE_I], ALL_TAC] THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [q52, q51, q50] THEN STRIP_TAC THEN UNDISCH_TAC q49 THEN REWRITE_TAC [IN_UNIONS, EXISTS_IN_GSPEC, IN_IMAGE] THEN DISCH_THEN (X_CHOOSE_THEN q48 (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN q47 (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP GALOIS_GROUP_PERMUTES) o (checkM (fun th => (do let z46 ← (q r"f IN group_carrier(galois_group(k,l) (h:A->B))"); let z45 ← (do let z44 ← (pure th); pure (concl z44)); pure (z45 == z46)))))) THEN DISCH_THEN (fun th => tactic_of do pure (STRIP_ASSUME_TAC (← MATCH_MP PERMUTES_INVERSES th) THEN ASSUME_TAC (← MATCH_MP PERMUTES_INVERSE_INVERSE th))) THEN SUBGOAL_THEN q43 ASSUME_TAC THENL [ASM_SIMP_TAC [GALOIS_GROUP_INVERSE], ALL_TAC] THEN SUBGOAL_THEN q42 STRIP_ASSUME_TAC THENL [MP_TAC v41 THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_OF_INTEGERS_SUBRING, PRIME_IDEAL_IMP_SUBSET] THEN REWRITE_TAC [GALOIS_GROUP_RING_OF_INTEGERS], SIMP_TAC []] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC q34 THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_IMAGE] THEN DISCH_TAC THEN X_GEN_TAC q33 THEN DISCH_TAC THEN EXISTS_TAC q32 THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC v31 THEN MAP_EVERY EXISTS_TAC [q30, q29] THEN ASM_REWRITE_TAC [] THEN MP_TAC v28 THEN MP_TAC v25 THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((SPECL [q23, q22, q21]) o (checkM (fun th => (do if ← (do let z12 ← (do let z13 ← (pure th); pure (concl z13)); canM (fun z14 => (do let z15 ← (pure z14); find_termM (fun z16 => (do let z18 ← (pure z16); let z17 ← (q r"s:B->bool"); pure (z17 == z18))) z15)) z12) then (do let z19 ← (do let z20 ← (pure th); pure (concl z20)); pure (is_forall z19)) else pure false))))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o ((SPECL [q11, q10]) o (checkM (fun th => (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); canM (fun z5 => (do let z6 ← (pure z5); find_termM (fun z7 => (do let z9 ← (pure z7); let z8 ← (q r"IMAGE:((B->B)->(B->B))->                  ((B->B)->bool)->((B->B)->bool)"); pure (z8 == z9))) z6)) z3))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC q2 THEN ASM_REWRITE_TAC [], REWRITE_TAC [o_THM] THEN DISCH_THEN (MP_TAC o (AP_TERM q1)) THEN ASM_REWRITE_TAC []])
    let lemma := p55
    let q56 ← q r"p:A->bool"
    let q57 ← q r"s:B->bool"
    let q58 ← q r"l:B ring"
    let q59 ← q r"k:A ring"
    let q60 ← q r"h:A->B"
    let v61 ← ISPECL [q60, q59, q58, q57, q56] NUMBER_FIELD_GENERATED_SPLITTING_TYPES
    let q62 ← q r"p:A->bool"
    let q63 ← q r"X:B->bool"
    let q64 ← q r"l:B ring"
    let q65 ← q r"k:A ring"
    let q66 ← q r"h:A->B"
    let v67 ← ISPECL [q66, q65, q64, q63, q62] NUMBER_FIELD_GENERATED_SPLITTING_TYPES
    let q68 ← q r"f:B->B"
    let q69 ← q r"I:B->B"
    let q70 ← q r"x:B"
    let q71 ← q r"(s:B->bool) SUBSET X /\ X SUBSET ring_carrier l"
    let q72 ← q r"X =
     UNIONS {IMAGE f s | f IN group_carrier(galois_group(k,l) (h:A->B))}"
    prove
      r"!(h:A->B) k l s p.
          number_field l /\ galois_extension(k,l) h /\
          s SUBSET ring_carrier l /\ IMAGE h (ring_carrier k) SUBSET s /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
          ==> (unramified
                (ring_of_integers k,
                 ring_of_integers(subfield_generated l
                  (UNIONS {IMAGE f s | f IN group_carrier(galois_group(k,l) h)})))
                h p <=>
               unramified
                (ring_of_integers k,ring_of_integers(subfield_generated l s)) h
                p) /\
              (totally_split
                (ring_of_integers k,
                 ring_of_integers(subfield_generated l
                  (UNIONS {IMAGE f s | f IN group_carrier(galois_group(k,l) h)})))
                h p <=>
               totally_split
                (ring_of_integers k,ring_of_integers(subfield_generated l s)) h
                p)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC q72 THEN SUBGOAL_THEN q71 STRIP_ASSUME_TAC THENL [EXPAND_TAC "X" THEN REWRITE_TAC [UNIONS_SUBSET, FORALL_IN_GSPEC] THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET, IN_UNIONS, EXISTS_IN_GSPEC] THEN X_GEN_TAC q70 THEN DISCH_TAC THEN EXISTS_TAC q69 THEN ASM_REWRITE_TAC [GALOIS_GROUP_I, IMAGE_I], X_GEN_TAC q68 THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_GROUP_PERMUTES)) THEN DISCH_THEN (MP_TAC o (MATCH_MP PERMUTES_IMAGE)) THEN ASM SET_TAC []], ALL_TAC] THEN MP_TAC v67 THEN ANTS_TAC THENL [ASM_MESON_TAC [SUBSET_TRANS], DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC)] THEN MP_TAC v61 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC)] THEN EXPAND_TAC "X" THEN CONJ_TAC THEN MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [REWRITE_TAC [inertia_group, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET], REPEAT STRIP_TAC THEN MATCH_MP_TAC INERTIA_GROUP_CONJUGATE THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING, GALOIS_GROUP_RING_OF_INTEGERS] THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], REWRITE_TAC [decomposition_group, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET], REPEAT STRIP_TAC THEN MATCH_MP_TAC DECOMPOSITION_GROUP_CONJUGATE THEN ASM_REWRITE_TAC []])

  let NUMBER_FIELD_UNRAMIFIED_INERTIA_FIXED_FIELD ← prove
    r"!(h:A->B) k l s.
        number_field l /\ galois_extension(k,l) h /\
        s SUBSET ring_carrier l /\ IMAGE h (ring_carrier k) SUBSET s
        ==> ((!p. prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
                  ==> unramified
                       (ring_of_integers k,
                        ring_of_integers(subfield_generated l s)) h p) <=>
             s SUBSET
             fixed_field l
              (group_carrier(subgroup_generated (galois_group(k,l) h)
                (UNIONS {group_carrier
                          (inertia_group(k,l) h (ring_of_integers l) Q) |
                         Q | prime_ideal (ring_of_integers l) Q /\
                             ~(Q = {ring_0 l})}))))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN wPart (rand o rand) (lhand o rand) FIXED_FIELD_SUBGROUP_GENERATED THEN ANTS_TAC THENL [REWRITE_TAC [UNIONS_SUBSET, FORALL_IN_GSPEC] THEN REWRITE_TAC [inertia_group, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET], DISCH_THEN SUBST1_TAC] THEN SUBGOAL_THEN (← q r"!p. prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> (unramified
              (ring_of_integers k,ring_of_integers(subfield_generated l s))
              (h:A->B) p <=>
             !Q f x. prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
                     f IN group_carrier
                           (inertia_group(k,l) h (ring_of_integers l) Q) /\
                     x IN s
                     ==> f x = x)") (fun th => SIMP_TAC [th]) THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"s:B->bool"), (← q r"p:A->bool")] NUMBER_FIELD_GENERATED_SPLITTING_TYPES) THEN ASM_SIMP_TAC [], ALL_TAC] THEN EQ_TAC THENL [DISCH_TAC THEN REWRITE_TAC [SUBSET, IN_FIXED_FIELD, IN_UNIONS, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN X_GEN_TAC (← q r"f:B->B") THEN DISCH_THEN (X_CHOOSE_THEN (← q r"J:(B->B)->bool") (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"Q:B->bool") STRIP_ASSUME_TAC) ASSUME_TAC)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"Q:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_BELOW) THEN ASM_REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"p:A->bool") STRIP_ASSUME_TAC) o CONJUNCT1) THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"p:A->bool")) o (checkM (fun z9 => (do let z10 ← (do let z11 ← (pure z9); pure (concl z11)); pure (is_forall z10)))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC (← q r"Q:B->bool") THEN ASM_MESON_TAC [], DISCH_TAC THEN X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"Q:B->bool"), (← q r"f:B->B"), (← q r"x:B")] THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"x:B")) o ((REWRITE_RULE [SUBSET, IN_FIXED_FIELD]) o (checkM (fun th => (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); canM (fun z3 => (do let z4 ← (pure z3); find_termM (fun t => (do if ← (do let z5 ← (pure t); pure (is_const z5)) then (do let z8 ← (pure "fixed_field"); let z7 ← (do pure (Prod.fst (← (do let z6 ← (pure t); liftExcept (dest_const z6))))); pure (z7 == z8)) else pure false)) z4)) z1)))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN REWRITE_TAC [IN_UNIONS, IN_ELIM_THM] THEN EXISTS_TAC (← q r"group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l) Q)") THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"Q:B->bool") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN ASM_SIMP_TAC []])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_NORMAL_CLOSURE_SPLITTING_TYPES,
           NUMBER_FIELD_UNRAMIFIED_INERTIA_FIXED_FIELD }
  -- @@RETURN END

end HolANT.DecompositionField
