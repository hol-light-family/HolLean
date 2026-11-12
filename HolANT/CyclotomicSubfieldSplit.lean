/- ========================================================================= -/
/- ANT: The decomposition law in subfields of cyclotomic fields            -/
/- ========================================================================= -/
/- File: HolANT/CyclotomicSubfieldSplit.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/cyclotomic_subfield_split.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antcyclotomicsubfieldsplitdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/integer.ml, Library/isum.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/modmul_group.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/relative_degree.ml, ANT/splitting_types.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/decomposition.ml, ANT/nf_valuation.ml, ANT/nf_decomposition.ml, ANT/decomposition_field.ml, Library/cyclotomic.ml, ANT/integrality.ml, ANT/dedekind_kummer.ml, ANT/cyclotomic_poly.ml, ANT/power_basis.ml, ANT/cyclotomic_field.ml, ANT/cyclotomic_galois.ml, ANT/cyclotomic_frobenius.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.CyclotomicSubfieldSplit fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left; where a proof applies rules that print or use
  counters (MESON, ARITH_RULE, ...) they are bound first, in OCaml's order.
-/

import HolANT.Prelude
import HolLibrary.Binomial
import HolLibrary.Iter
import HolLibrary.Prime
import HolLibrary.Pocklington
import HolLibrary.Wo
import HolLibrary.Card
import HolLibrary.RingTheory
import HolLibrary.Matroids
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolLibrary.FieldTheory
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolLibrary.Integer
import HolLibrary.Isum
import HolLibrary.Products
import HolLibrary.Multiplicative
import HolLibrary.Primitive
import HolLibrary.ModmulGroup
import HolANT.Algmisc
import HolANT.Integral
import HolANT.IdealArith
import HolANT.Dedekind
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolANT.RingOfIntegers
import HolANT.PrimeSplit
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.NormIndex
import HolANT.Classgroup
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.RelativeDegree
import HolANT.SplittingTypes
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolANT.Decomposition
import HolANT.NfValuation
import HolANT.NfDecomposition
import HolANT.DecompositionField
import HolLibrary.Cyclotomic
import HolANT.Integrality
import HolANT.DedekindKummer
import HolANT.CyclotomicPoly
import HolANT.PowerBasis
import HolANT.CyclotomicField
import HolANT.CyclotomicGalois
import HolANT.CyclotomicFrobenius

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Algmisc
open HolANT.Integral
open HolANT.IdealArith
open HolANT.Dedekind
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.RingOfIntegers
open HolANT.PrimeSplit
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.NormIndex
open HolANT.Classgroup
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.RelativeDegree
open HolANT.SplittingTypes
open HolANT.Decomposition
open HolANT.NfValuation
open HolANT.NfDecomposition
open HolANT.DecompositionField
open HolANT.Integrality
open HolANT.DedekindKummer
open HolANT.CyclotomicPoly
open HolANT.PowerBasis
open HolANT.CyclotomicField
open HolANT.CyclotomicGalois
open HolANT.CyclotomicFrobenius

namespace HolANT.CyclotomicSubfieldSplit

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CARD_IMAGE_INJ CONG_REFL COPRIME_LEXP CYCLOTOMIC_FIELD_FROBENIUS_ELEMENT
   CYCLOTOMIC_FIELD_GALOIS_EXTENSION CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ
   CYCLOTOMIC_FIELD_GALOIS_GROUP_EXISTS CYCLOTOMIC_FIELD_GALOIS_GROUP_HAS_SIZE
   CYCLOTOMIC_FIELD_GALOIS_GROUP_MODMUL CYCLOTOMIC_FIELD_INERTIA_GROUP
   DECOMPOSITION_GROUP DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL
   DEDEKIND_RING_OF_INTEGERS DIVIDES_ANTISYM DIVIDES_ONE DIVIDES_REFL
   DIVIDES_ZERO EQ_TRANS EXP_1 EXTENSION FIELD_SUBFIELD_GENERATED FINITE_SUBSET
   FORALL_IN_IMAGE GALOIS_CORRESPONDENCE_DEGREE GALOIS_GROUP_FIXED_FIELD
   GALOIS_GROUP_POW_ROOT GROUP_ISOMORPHISM GROUP_ISOMORPHISM_IMP_HOMOMORPHISM
   GROUP_POW HAS_SIZE IMAGE_I IN_ELIM_THM IN_FIXED_FIELD IN_GALOIS_GROUP
   IN_GALOIS_GROUP_INTERMEDIATE IN_GALOIS_GROUP_SUBFIELD_GENERATED IN_INTER
   IN_SING MAXIMAL_IMP_PRIME_IDEAL MEMBER_NOT_EMPTY MODMUL_GROUP_CONG_EQ
   MULT_CLAUSES NSUM_CONST NSUM_EQ NUMBER_FIELD_FROBENIUS_ELEMENT
   NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_INTERMEDIATE_FROBENIUS_ORDER NUMBER_FIELD_PRIME_DECOMPOSITION_Q
   NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE NUMBER_FIELD_SUBFIELD_GENERATED
   NUMBER_FIELD_SUBFIELD_PRIME_IDEALS_ABOVE NUMBER_FIELD_TOWER_LAW
   NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_Q
   NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP PRIME_COPRIME_EQ PRIME_IMP_NZ
   PRIME_IMP_RING_IDEAL PRIME_SUBFIELD_MINIMAL PRIME_SUBFIELD_SUBFIELD_GENERATED
   RAMIFICATION_INDEX_PRIME_SUBFIELD RESIDUE_DEGREE_PRIME_SUBFIELD
   RING_HOMOMORPHISM_SUBFIELD_INCLUSION RING_OF_INTEGERS
   RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL RING_OF_NUM RING_OF_NUM_EQ_0
   RING_OF_NUM_SUBFIELD_GENERATED RING_POW_EQ_GEN SPLITTING_TYPES_INTEGER_RING
   SUBFIELD_GENERATED SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED
   SUBFIELD_SUBFIELD_GENERATED SUBGROUP_OF_HOMOMORPHIC_PREIMAGE
   SUBGROUP_OF_IMP_SUBSET SUBSET group_homomorphism number_field subgroup_of : thm)
  deriving Inhabited

/-- What cyclotomic_subfield_split.ml uses from Session besides theorems. -/
structure CyclotomicSubfieldSplitDeps where
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

/-- RingTheory's `wPart` (copied verbatim).  `W(MP_TAC o PART_MATCH f th o g
    o snd)`: match `th`'s part `f` against the part `g` of the goal, and
    MP_TAC the instance. -/
def wPart [HolBase] (g : term → Except String term) (f : term → Except String term)
    (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (g gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)



/- ---------------------------------------------------------------------- -/
/- cyclotomic_subfield_split.ml phrases from line 91 to 566               -/
/- ---------------------------------------------------------------------- -/

structure CyclotomicSubfieldSplit where
  -- @@FIELDS
  CYCLOTOMIC_SUBFIELD_RESIDUE_DEGREE : thm
  CYCLOTOMIC_SUBFIELD_PRIME_DECOMPOSITION : thm
  CYCLOTOMIC_SUBFIELD_SPLITTING_TYPES : thm
  CYCLOTOMIC_FIXED_FIELD_PRIME_DECOMPOSITION : thm
  CYCLOTOMIC_FIXED_FIELD_TOTALLY_SPLIT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupCyclotomicSubfieldSplit [HolBase] (D : CyclotomicSubfieldSplitDeps) :
    ExceptT String IO CyclotomicSubfieldSplit := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, NUMBER_RULE, SET_TAC, .. } := D
  let { CARD_IMAGE_INJ, CONG_REFL, COPRIME_LEXP, CYCLOTOMIC_FIELD_FROBENIUS_ELEMENT,
        CYCLOTOMIC_FIELD_GALOIS_EXTENSION, CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ,
        CYCLOTOMIC_FIELD_GALOIS_GROUP_EXISTS, CYCLOTOMIC_FIELD_GALOIS_GROUP_HAS_SIZE,
        CYCLOTOMIC_FIELD_GALOIS_GROUP_MODMUL, CYCLOTOMIC_FIELD_INERTIA_GROUP,
        DECOMPOSITION_GROUP, DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL,
        DEDEKIND_RING_OF_INTEGERS, DIVIDES_ANTISYM, DIVIDES_ONE, DIVIDES_REFL,
        DIVIDES_ZERO, EQ_TRANS, EXP_1, EXTENSION, FIELD_SUBFIELD_GENERATED,
        FINITE_SUBSET, FORALL_IN_IMAGE, GALOIS_CORRESPONDENCE_DEGREE,
        GALOIS_GROUP_FIXED_FIELD, GALOIS_GROUP_POW_ROOT, GROUP_ISOMORPHISM,
        GROUP_ISOMORPHISM_IMP_HOMOMORPHISM, GROUP_POW, HAS_SIZE, IMAGE_I, IN_ELIM_THM,
        IN_FIXED_FIELD, IN_GALOIS_GROUP, IN_GALOIS_GROUP_INTERMEDIATE,
        IN_GALOIS_GROUP_SUBFIELD_GENERATED, IN_INTER, IN_SING, MAXIMAL_IMP_PRIME_IDEAL,
        MEMBER_NOT_EMPTY, MODMUL_GROUP_CONG_EQ, MULT_CLAUSES, NSUM_CONST, NSUM_EQ,
        NUMBER_FIELD_FROBENIUS_ELEMENT, NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_INTERMEDIATE_FROBENIUS_ORDER,
        NUMBER_FIELD_PRIME_DECOMPOSITION_Q, NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE,
        NUMBER_FIELD_SUBFIELD_GENERATED, NUMBER_FIELD_SUBFIELD_PRIME_IDEALS_ABOVE,
        NUMBER_FIELD_TOWER_LAW, NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_Q,
        NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP, PRIME_COPRIME_EQ, PRIME_IMP_NZ,
        PRIME_IMP_RING_IDEAL, PRIME_SUBFIELD_MINIMAL,
        PRIME_SUBFIELD_SUBFIELD_GENERATED, RAMIFICATION_INDEX_PRIME_SUBFIELD,
        RESIDUE_DEGREE_PRIME_SUBFIELD, RING_HOMOMORPHISM_SUBFIELD_INCLUSION,
        RING_OF_INTEGERS, RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL, RING_OF_NUM,
        RING_OF_NUM_EQ_0, RING_OF_NUM_SUBFIELD_GENERATED, RING_POW_EQ_GEN,
        SPLITTING_TYPES_INTEGER_RING, SUBFIELD_GENERATED,
        SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED, SUBFIELD_SUBFIELD_GENERATED,
        SUBGROUP_OF_HOMOMORPHIC_PREIMAGE, SUBGROUP_OF_IMP_SUBSET, SUBSET,
        group_homomorphism, number_field, subgroup_of, .. } := D.core1
  -- @@SCOPE END

  let CYCLOTOMIC_SUBFIELD_RESIDUE_DEGREE ← prove
    r"!(k:A ring) z n s p Q.
        number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
        subfield_generated k {z} = k /\ prime p /\ ~(p divides n) /\
        prime_ideal (ring_of_integers k) Q /\ ring_of_num k p IN Q
        ==> prime_ideal (ring_of_integers(subfield_generated k s))
              (Q INTER ring_carrier(subfield_generated k s)) /\
            ring_of_num (subfield_generated k s) p IN
            Q INTER ring_carrier(subfield_generated k s) /\
            ramification_index
              (integer_ring,ring_of_integers(subfield_generated k s))
              (ring_of_int(subfield_generated k s))
              (Q INTER ring_carrier(subfield_generated k s)) = 1 /\
            !d. residue_degree
                  (integer_ring,ring_of_integers(subfield_generated k s))
                  (ring_of_int(subfield_generated k s))
                  (Q INTER ring_carrier(subfield_generated k s)) divides d <=>
                !g x. g IN group_carrier(galois_group
                                   (subfield_generated k {ring_0 k},k) I) /\
                      g z = ring_pow k z (p EXP d) /\ x IN s
                      ==> g x = x"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [RING_OF_NUM_SUBFIELD_GENERATED] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"~(n:num = 0)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~((p:num) divides 0)") THEN CONV_TAC NUMBER_RULE, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_GALOIS_EXTENSION) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"p0 = ideal_generated (ring_of_integers(subfield_generated k {ring_0 k}))
                         {ring_of_num k p:A}") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"IMAGE (I:A->A) p0 SUBSET Q") ASSUME_TAC THENL [ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(Q = {ring_0(k:A ring)})") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"ring_of_num k p IN {ring_0 k:A}") THEN REWRITE_TAC [IN_SING, RING_OF_NUM_EQ_0] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← CONJUNCT1 (← REWRITE_RULE [number_field] th))])) THEN ASM_SIMP_TAC [DIVIDES_ZERO, PRIME_IMP_NZ], ALL_TAC] THEN SUBGOAL_THEN (← q r"maximal_ideal (ring_of_integers k) (Q:A->bool)") ASSUME_TAC THENL [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num"), (← q r"p:num"), (← q r"Q:A->bool")] CYCLOTOMIC_FIELD_INERTIA_GROUP) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num"), (← q r"p:num"), (← q r"Q:A->bool")] CYCLOTOMIC_FIELD_FROBENIUS_ELEMENT) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ABBREV_TAC (← q r"Q0 = subfield_generated k {ring_0 k:A}") THEN SUBGOAL_THEN (← q r"field(Q0:A ring) /\ ring_homomorphism(Q0,k) (I:A->A) /\
    ring_0 Q0 = ring_0 k") STRIP_ASSUME_TAC THENL [EXPAND_TAC "Q0" THEN SIMP_TAC [FIELD_SUBFIELD_GENERATED, (← ASSUME (← q r"field(k:A ring)")), RING_HOMOMORPHISM_SUBFIELD_INCLUSION, (← CONJUNCT2 SUBFIELD_GENERATED)], ALL_TAC] THEN SUBGOAL_THEN (← q r"ramification_index (ring_of_integers Q0,ring_of_integers k) (I:A->A) Q =
    1") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"Q0:A ring"), (← q r"k:A ring"), (← q r"p0:A->bool"), (← q r"Q:A->bool")] NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP) THEN ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"Q0:A ring"), (← q r"k:A ring"), (← q r"p0:A->bool"), (← q r"Q:A->bool")] NUMBER_FIELD_FROBENIUS_ELEMENT) THEN ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN ABBREV_TAC (← q r"fr = frobenius_element (Q0,k) (I:A->A) (ring_of_integers k) Q") THEN SUBGOAL_THEN (← q r"fr IN group_carrier(galois_group(Q0,k) (I:A->A))") ASSUME_TAC THENL [UNDISCH_TAC (← q r"fr IN group_carrier(decomposition_group(Q0,k) (I:A->A) Q)") THEN REWRITE_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM] THEN SIMP_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"K = subfield_generated k (s:A->bool)") THEN ABBREV_TAC (← q r"t = ring_carrier(K:A ring)") THEN SUBGOAL_THEN (← q r"t subfield_of (k:A ring) /\ IMAGE (I:A->A) (ring_carrier Q0) SUBSET t /\
    subfield_generated k t = K") STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["t", "K", "Q0"] THEN SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED, IMAGE_I, PRIME_SUBFIELD_MINIMAL, SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED, (← ASSUME (← q r"field(k:A ring)"))], ALL_TAC] THEN SUBGOAL_THEN (← q r"subfield_generated K {ring_0 K} = (Q0:A ring) /\
    ring_0 K = ring_0(k:A ring) /\ ring_of_num K = ring_of_num(k:A ring) /\
    number_field(K:A ring)") STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["K", "Q0"] THEN SIMP_TAC [PRIME_SUBFIELD_SUBFIELD_GENERATED, (← CONJUNCT2 SUBFIELD_GENERATED), RING_OF_NUM_SUBFIELD_GENERATED, NUMBER_FIELD_SUBFIELD_GENERATED, (← ASSUME (← q r"number_field(k:A ring)"))], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"Q0:A ring"), (← q r"k:A ring"), (← q r"t:A->bool"), (← q r"p0:A->bool"), (← q r"Q:A->bool")] NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE) THEN ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"Q0:A ring"), (← q r"k:A ring"), (← q r"t:A->bool"), (← q r"p0:A->bool"), (← q r"Q:A->bool")] NUMBER_FIELD_INTERMEDIATE_FROBENIUS_ORDER) THEN ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"K:A ring"), (← q r"Q INTER (t:A->bool)")] RAMIFICATION_INDEX_PRIME_SUBFIELD) THEN MP_TAC (← ISPECL [(← q r"K:A ring"), (← q r"Q INTER (t:A->bool)")] RESIDUE_DEGREE_PRIME_SUBFIELD) THEN ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD, PRIME_IMP_RING_IDEAL] THEN REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN CONJ_TAC THENL [REWRITE_TAC [IN_INTER] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"K:A ring"), (← q r"p:num")] RING_OF_NUM) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN X_GEN_TAC (← q r"d:num") THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"d:num")) o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); canM (fun z5 => (do let z6 ← (pure z5); find_termM (fun t => (do if ← (do let z7 ← (pure t); pure (is_const z7)) then (do let z10 ← (pure "group_pow"); let z9 ← (do pure (Prod.fst (← (do let z8 ← (pure t); liftExcept (dest_const z8))))); pure (z9 == z10)) else pure false)) z6)) z3) else pure false))))) THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ABBREV_TAC (← q r"gd = group_pow (galois_group(Q0,k) (I:A->A)) fr d") THEN SUBGOAL_THEN (← q r"(gd:A->A) IN group_carrier(galois_group(Q0,k) I) /\
    gd z = ring_pow k z (p EXP d)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "gd" THEN CONJ_TAC THENL [MATCH_MP_TAC GROUP_POW THEN FIRST_ASSUM ACCEPT_TAC, MATCH_MP_TAC GALOIS_GROUP_POW_ROOT THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBST1_TAC (← SYM (← ASSUME (← q r"subfield_generated k s = (K:A ring)"))) THEN SIMP_TAC [IN_GALOIS_GROUP_SUBFIELD_GENERATED, (← ASSUME (← q r"field(k:A ring)"))] THEN SUBGOAL_THEN (← q r"(gd:A->A) permutes ring_carrier k /\ ring_automorphism k gd") (fun th => REWRITE_TAC [th]) THENL [UNDISCH_TAC (← q r"(gd:A->A) IN group_carrier(galois_group(Q0,k) I)") THEN SIMP_TAC [IN_GALOIS_GROUP], ALL_TAC] THEN EQ_TAC THENL [DISCH_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"g:A->A"), (← q r"x:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"g:A->A = gd") SUBST1_TAC THENL [MATCH_MP_TAC CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"z:A")] THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC []], DISCH_TAC THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []])

  let CYCLOTOMIC_SUBFIELD_PRIME_DECOMPOSITION ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"nsum {P | prime_ideal (ring_of_integers K) P /\ ring_of_num k p IN P}
         (\P:A->bool. f)"
    let q2 ← q r"p:num"
    let q3 ← q r"K:A ring"
    let v4 ← ISPECL [q3, q2] NUMBER_FIELD_PRIME_DECOMPOSITION_Q
    let q5 ← q r"p:num"
    let q6 ← q r"K:A ring"
    let v7 ← ISPECL [q6, q5] NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q
    let q8 ← q r"number_field(k:A ring)"
    let v9 ← ASSUME q8
    let q10 ← q r"number_field(K:A ring) /\ ring_of_num K = ring_of_num(k:A ring) /\
    subfield_generated K {ring_0 K} = subfield_generated k {ring_0 k}"
    let q11 ← q r"!a b:num. (!d. a divides d <=> b divides d) ==> a = b"
    let r12 ← MESON [DIVIDES_ANTISYM, DIVIDES_REFL] q11
    let q13 ← q r"Q:A->bool"
    let q14 ← q r"p:num"
    let q15 ← q r"s:A->bool"
    let q16 ← q r"n:num"
    let q17 ← q r"z:A"
    let q18 ← q r"k:A ring"
    let v19 ← ISPECL [q18, q17, q16, q15, q14, q13] CYCLOTOMIC_SUBFIELD_RESIDUE_DEGREE
    let q20 ← q r"Q:A->bool"
    let q21 ← q r"(IN) (P:A->bool)"
    let q22 ← q r"p:num"
    let q23 ← q r"s:A->bool"
    let q24 ← q r"k:A ring"
    let v25 ← ISPECL [q24, q23, q22] NUMBER_FIELD_SUBFIELD_PRIME_IDEALS_ABOVE
    let q26 ← q r"P:A->bool"
    let q27 ← q r"!P. prime_ideal (ring_of_integers K) P /\ ring_of_num k p IN P
        ==> ramification_index (integer_ring,ring_of_integers K)
              (ring_of_int K) P = 1 /\
            residue_degree (integer_ring,ring_of_integers K)
              (ring_of_int (K:A ring)) P = f"
    let q28 ← q r"f = residue_degree (integer_ring,ring_of_integers K) (ring_of_int K)
          (Q1 INTER ring_carrier(K:A ring))"
    let q29 ← q r"residue_degree (integer_ring,ring_of_integers K) (ring_of_int K)
      (Q1 INTER ring_carrier(K:A ring))"
    let q30 ← q r"K = subfield_generated k (s:A->bool)"
    let q31 ← q r"Q1:A->bool"
    let q32 ← q r"p:num"
    let q33 ← q r"s:A->bool"
    let q34 ← q r"n:num"
    let q35 ← q r"z:A"
    let q36 ← q r"k:A ring"
    let v37 ← ISPECL [q36, q35, q34, q33, q32, q31] CYCLOTOMIC_SUBFIELD_RESIDUE_DEGREE
    let q38 ← q r"Q1:A->bool"
    let v39 ← GSYM MEMBER_NOT_EMPTY
    let q40 ← q r"p:num"
    let q41 ← q r"k:A ring"
    let v42 ← ISPECL [q41, q40] NUMBER_FIELD_PRIME_DECOMPOSITION_Q
    prove
      r"!(k:A ring) z n s p.
          number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
          subfield_generated k {z} = k /\ prime p /\ ~(p divides n)
          ==> ?f. (!d. f divides d <=>
                       !g x. g IN group_carrier(galois_group
                                       (subfield_generated k {ring_0 k},k) I) /\
                             g z = ring_pow k z (p EXP d) /\ x IN s
                             ==> g x = x) /\
                  (!P. prime_ideal (ring_of_integers(subfield_generated k s)) P /\
                       ring_of_num (subfield_generated k s) p IN P
                       ==> ramification_index
                             (integer_ring,
                              ring_of_integers(subfield_generated k s))
                             (ring_of_int(subfield_generated k s)) P = 1 /\
                           residue_degree
                             (integer_ring,
                              ring_of_integers(subfield_generated k s))
                             (ring_of_int(subfield_generated k s)) P = f) /\
                  CARD {P | prime_ideal
                              (ring_of_integers(subfield_generated k s)) P /\
                            ring_of_num (subfield_generated k s) p IN P} * f =
                  extension_degree(subfield_generated k {ring_0 k},
                                   subfield_generated k s) I"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [RING_OF_NUM_SUBFIELD_GENERATED] THEN MP_TAC v42 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (CONJUNCT1 o CONJUNCT2)) THEN REWRITE_TAC [v39, IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_THEN q38 STRIP_ASSUME_TAC) THEN MP_TAC v37 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ABBREV_TAC q30 THEN EXISTS_TAC q29 THEN ABBREV_TAC q28 THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN q27 ASSUME_TAC THENL [X_GEN_TAC q26 THEN STRIP_TAC THEN MP_TAC v25 THEN ASM_REWRITE_TAC [RING_OF_NUM_SUBFIELD_GENERATED] THEN DISCH_THEN (MP_TAC o (AP_TERM q21)) THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_THEN q20 (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST_ALL_TAC)) THEN MP_TAC v19 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r12 THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC []] THEN SUBGOAL_THEN q10 STRIP_ASSUME_TAC THENL [EXPAND_TAC "K" THEN SIMP_TAC [PRIME_SUBFIELD_SUBFIELD_GENERATED, RING_OF_NUM_SUBFIELD_GENERATED, NUMBER_FIELD_SUBFIELD_GENERATED, v9], ALL_TAC] THEN MP_TAC v7 THEN MP_TAC v4 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN DISCH_THEN (SUBST1_TAC o SYM) THEN TRANS_TAC EQ_TRANS q1 THEN CONJ_TAC THENL [ASM_SIMP_TAC [NSUM_CONST], MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM, MULT_CLAUSES]])

  let CYCLOTOMIC_SUBFIELD_SPLITTING_TYPES ← prove
    r"!(k:A ring) z n s p.
        number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
        subfield_generated k {z} = k /\ prime p /\ ~(p divides n)
        ==> unramified (integer_ring,ring_of_integers(subfield_generated k s))
              (ring_of_int(subfield_generated k s))
              (ideal_generated integer_ring {&p}) /\
            (totally_split
              (integer_ring,ring_of_integers(subfield_generated k s))
              (ring_of_int(subfield_generated k s))
              (ideal_generated integer_ring {&p}) <=>
             !g x. g IN group_carrier(galois_group
                             (subfield_generated k {ring_0 k},k) I) /\
                   g z = ring_pow k z p /\ x IN s
                   ==> g x = x)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num"), (← q r"s:A->bool"), (← q r"p:num")] CYCLOTOMIC_SUBFIELD_PRIME_DECOMPOSITION) THEN ASM_REWRITE_TAC [RING_OF_NUM_SUBFIELD_GENERATED] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"f:num") (CONJUNCTS_THEN2 (MP_TAC o (SPEC (← q r"1:num"))) (CONJUNCTS_THEN2 ASSUME_TAC (fun (_ : thm) => ALL_TAC)))) THEN REWRITE_TAC [DIVIDES_ONE, EXP_1] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"subfield_generated k (s:A->bool)"), (← q r"p:num")] NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_Q) THEN ASM_SIMP_TAC [NUMBER_FIELD_SUBFIELD_GENERATED, PRIME_IMP_NZ] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers(subfield_generated k s):A ring"), (← q r"p:num")] SPLITTING_TYPES_INTEGER_RING) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_OF_NUM_SUBFIELD_GENERATED] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN SUBGOAL_THEN (← q r"?P. prime_ideal (ring_of_integers(subfield_generated k s)) P /\
        ring_of_num k p IN (P:A->bool)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"subfield_generated k (s:A->bool)"), (← q r"p:num")] NUMBER_FIELD_PRIME_DECOMPOSITION_Q) THEN ANTS_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_SUBFIELD_GENERATED], ALL_TAC] THEN DISCH_THEN (MP_TAC o (CONJUNCT1 o CONJUNCT2)) THEN REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM, RING_OF_NUM_SUBFIELD_GENERATED] THEN MESON_TAC [], ALL_TAC] THEN CONJ_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN EQ_TAC THENL [DISCH_THEN (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ASM_SIMP_TAC [], ASM_SIMP_TAC []])

  let CYCLOTOMIC_FIXED_FIELD_PRIME_DECOMPOSITION ← prove
    r"!(k:A ring) z n H s p.
        number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
        subfield_generated k {z} = k /\ H subgroup_of modmul_group n /\
        fixed_field k
          {g | g IN group_carrier(galois_group
                                   (subfield_generated k {ring_0 k},k) I) /\
               ?c. c IN H /\ g z = ring_pow k z c} = s /\
        prime p /\ ~(p divides n)
        ==> extension_degree(subfield_generated k {ring_0 k},
                             subfield_generated k s) I * CARD H = phi n /\
            ?f. (!d. f divides d <=> ?c. c IN H /\ (p EXP d == c) (mod n)) /\
                (!P. prime_ideal (ring_of_integers(subfield_generated k s)) P /\
                     ring_of_num (subfield_generated k s) p IN P
                     ==> ramification_index
                           (integer_ring,
                            ring_of_integers(subfield_generated k s))
                           (ring_of_int(subfield_generated k s)) P = 1 /\
                         residue_degree
                           (integer_ring,
                            ring_of_integers(subfield_generated k s))
                           (ring_of_int(subfield_generated k s)) P = f) /\
                CARD {P | prime_ideal
                            (ring_of_integers(subfield_generated k s)) P /\
                          ring_of_num (subfield_generated k s) p IN P} * f =
                extension_degree(subfield_generated k {ring_0 k},
                                 subfield_generated k s) I"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"~(n:num = 0)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~((p:num) divides 0)") THEN CONV_TAC NUMBER_RULE, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_GALOIS_GROUP_MODMUL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:(A->A)->num") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_GALOIS_GROUP_HAS_SIZE) THEN ASM_REWRITE_TAC [HAS_SIZE] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_GALOIS_EXTENSION) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ABBREV_TAC (← q r"Hg = {g | g IN group_carrier(galois_group
                                   (subfield_generated k {ring_0 k},k) I) /\
              ?c. c IN H /\ g z = ring_pow k (z:A) c}") THEN SUBGOAL_THEN (← q r"!a b. ring_pow k z a = ring_pow k (z:A) b <=> (a == b) (mod n)") ASSUME_TAC THENL [REPEAT GEN_TAC THEN UNDISCH_TAC (← q r"ring_order k (z:A) = n") THEN DISCH_THEN (fun th => tactic_of do pure (SUBST1_TAC (← SYM th) THEN ASSUME_TAC th)) THEN MATCH_MP_TAC RING_POW_EQ_GEN THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"Hg = {g | g IN group_carrier(galois_group
                                   (subfield_generated k {ring_0 k},k) I) /\
              (e:(A->A)->num) g IN H}") ASSUME_TAC THENL [EXPAND_TAC "Hg" THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"g:A->A") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"(g:A->A) IN group_carrier(galois_group
                                 (subfield_generated k {ring_0 k},k) I)") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(e:(A->A)->num) g IN group_carrier(modmul_group n)") ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GROUP_ISOMORPHISM_IMP_HOMOMORPHISM)) THEN REWRITE_TAC [group_homomorphism, SUBSET, FORALL_IN_IMAGE] THEN ASM_SIMP_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [] THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"c:num") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(e:(A->A)->num) g = c") (fun th => ASM_REWRITE_TAC [th]) THEN MATCH_MP_TAC MODMUL_GROUP_CONG_EQ THEN EXISTS_TAC (← q r"n:num") THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [subgroup_of, SUBSET], DISCH_TAC THEN EXISTS_TAC (← q r"(e:(A->A)->num) g") THEN ASM_REWRITE_TAC [CONG_REFL]], ALL_TAC] THEN SUBGOAL_THEN (← q r"finite_extension(subfield_generated k {ring_0 k},k) (I:A->A)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"I:A->A")] NUMBER_FIELD_TOWER_LAW) THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION], ALL_TAC] THEN SUBGOAL_THEN (← q r"(Hg:(A->A)->bool) subgroup_of
    galois_group(subfield_generated k {ring_0 k},k) I /\
    CARD Hg = CARD(H:num->bool)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z66 ← (do let z67 ← (pure th); pure (concl z67)); pure (is_eq z66)) then (do let z71 ← (q r"Hg:(A->A)->bool"); let z70 ← (do let z68 ← (do let z69 ← (pure th); pure (concl z69)); liftExcept (lhs z68)); pure (z70 == z71)) else pure false)))) THEN CONJ_TAC THENL [MATCH_MP_TAC SUBGROUP_OF_HOMOMORPHIC_PREIMAGE THEN EXISTS_TAC (← q r"modmul_group n") THEN ASM_SIMP_TAC [GROUP_ISOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((GEN_REWRITE_RULE id [GROUP_ISOMORPHISM]) o (checkM (fun th => (do if ← (do let z58 ← (do pure (Prod.fst (← (do let z59 ← (do let z60 ← (pure th); pure (concl z60)); pure (strip_comb z59))))); pure (is_const z58)) then (do let z65 ← (pure "group_isomorphism"); let z64 ← (do pure (Prod.fst (← (do let z61 ← (do pure (Prod.fst (← (do let z62 ← (do let z63 ← (pure th); pure (concl z63)); pure (strip_comb z62))))); liftExcept (dest_const z61))))); pure (z64 == z65)) else pure false))))) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP SUBGROUP_OF_IMP_SUBSET) o (checkM (fun th => (do let z57 ← (q r"H subgroup_of modmul_group n"); let z56 ← (do let z55 ← (pure th); pure (concl z55)); pure (z56 == z57)))))) THEN TRANS_TAC EQ_TRANS (← q r"CARD(IMAGE (e:(A->A)->num)
        {g | g IN group_carrier(galois_group
                                 (subfield_generated k {ring_0 k},k) I) /\
             e g IN H})") THEN CONJ_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"group_carrier(galois_group
                         (subfield_generated k {ring_0 k},k) (I:A->A))") THEN ASM_REWRITE_TAC [] THEN SET_TAC []], AP_TERM_TAC THEN UNDISCH_TAC (← q r"IMAGE (e:(A->A)->num)
          (group_carrier(galois_group
                          (subfield_generated k {ring_0 k},k) I)) =
        group_carrier(modmul_group n)") THEN UNDISCH_TAC (← q r"H SUBSET group_carrier(modmul_group n)") THEN SET_TAC []], ALL_TAC] THEN FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun th => (do if ← (do let z49 ← (do let z50 ← (pure th); pure (concl z50)); pure (is_eq z49)) then (do let z54 ← (q r"Hg:(A->A)->bool"); let z53 ← (do let z51 ← (do let z52 ← (pure th); pure (concl z52)); liftExcept (lhs z51)); pure (z53 == z54)) else pure false)))) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"Hg:(A->A)->bool")] GALOIS_GROUP_FIXED_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"s:A->bool")] GALOIS_CORRESPONDENCE_DEGREE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT2) THEN CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num"), (← q r"s:A->bool"), (← q r"p:num")] CYCLOTOMIC_SUBFIELD_PRIME_DECOMPOSITION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!d. (!g x. g IN group_carrier(galois_group
                                  (subfield_generated k {ring_0 k},k) I) /\
               g z = ring_pow k (z:A) (p EXP d) /\ x IN s
               ==> g x = x) <=>
        (?c. c IN H /\ (p EXP d == c) (mod n))") (fun th => REWRITE_TAC [th]) THEN X_GEN_TAC (← q r"d:num") THEN EQ_TAC THENL [DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num"), (← q r"p EXP d")] CYCLOTOMIC_FIELD_GALOIS_GROUP_EXISTS) THEN ASM_SIMP_TAC [COPRIME_LEXP, PRIME_COPRIME_EQ] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g0:A->A") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(g0:A->A) IN Hg") MP_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z43 ← (do let z44 ← (pure th); pure (concl z44)); pure (is_eq z43)) then (do let z48 ← (q r"group_carrier(galois_group(subfield_generated k s,k) (I:A->A))"); let z47 ← (do let z45 ← (do let z46 ← (pure th); pure (concl z46)); liftExcept (lhs z45)); pure (z47 == z48)) else pure false))))) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"g0:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"s:A->bool")] IN_GALOIS_GROUP_INTERMEDIATE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [CONG_REFL], ALL_TAC] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do if ← (do let z29 ← (do let z30 ← (pure th); pure (concl z30)); pure (is_eq z29)) then (do let z34 ← (q r"Hg:(A->A)->bool"); let z33 ← (do let z31 ← (do let z32 ← (pure th); pure (concl z32)); liftExcept (rhs z31)); pure (z33 == z34)) else pure false) then (do let z35 ← (do let z36 ← (do let z37 ← (pure th); pure (concl z37)); liftExcept (lhs z36)); canM (fun z38 => (do let z39 ← (pure z38); find_termM (fun z40 => (do let z42 ← (pure z40); let z41 ← (q r"ring_pow:A ring->A->num->A"); pure (z41 == z42))) z39)) z35) else pure false))))) THEN ASM_REWRITE_TAC [IN_ELIM_THM], DISCH_THEN (X_CHOOSE_THEN (← q r"c:num") STRIP_ASSUME_TAC) THEN MAP_EVERY X_GEN_TAC [(← q r"g:A->A"), (← q r"x:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(g:A->A) IN Hg") ASSUME_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do if ← (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); pure (is_eq z15)) then (do let z20 ← (q r"Hg:(A->A)->bool"); let z19 ← (do let z17 ← (do let z18 ← (pure th); pure (concl z18)); liftExcept (rhs z17)); pure (z19 == z20)) else pure false) then (do let z21 ← (do let z22 ← (do let z23 ← (pure th); pure (concl z23)); liftExcept (lhs z22)); canM (fun z24 => (do let z25 ← (pure z24); find_termM (fun z26 => (do let z28 ← (pure z26); let z27 ← (q r"ring_pow:A ring->A->num->A"); pure (z27 == z28))) z25)) z21) else pure false))))) THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"c:num") THEN ASM_REWRITE_TAC [], UNDISCH_TAC (← q r"(x:A) IN s") THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"s:A->bool"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (rhs z3)); pure (z5 == z6)) else pure false) then (do let z7 ← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); liftExcept (lhs z8)); canM (fun z10 => (do let z11 ← (pure z10); find_termM (fun z12 => (do let z14 ← (pure z12); let z13 ← (q r"fixed_field:A ring->((A->A)->bool)->A->bool"); pure (z13 == z14))) z11)) z7) else pure false))))) THEN REWRITE_TAC [IN_FIXED_FIELD] THEN ASM_SIMP_TAC []]])

  let CYCLOTOMIC_FIXED_FIELD_TOTALLY_SPLIT ← prove
    r"!(k:A ring) z n H s p.
        number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
        subfield_generated k {z} = k /\ H subgroup_of modmul_group n /\
        fixed_field k
          {g | g IN group_carrier(galois_group
                                   (subfield_generated k {ring_0 k},k) I) /\
               ?c. c IN H /\ g z = ring_pow k z c} = s /\
        prime p /\ ~(p divides n)
        ==> (totally_split
              (integer_ring,ring_of_integers(subfield_generated k s))
              (ring_of_int(subfield_generated k s))
              (ideal_generated integer_ring {&p}) <=>
             ?c. c IN H /\ (p == c) (mod n))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num"), (← q r"H:num->bool"), (← q r"s:A->bool"), (← q r"p:num")] CYCLOTOMIC_FIXED_FIELD_PRIME_DECOMPOSITION) THEN ASM_REWRITE_TAC [RING_OF_NUM_SUBFIELD_GENERATED] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"f:num") (CONJUNCTS_THEN2 (MP_TAC o (SPEC (← q r"1:num"))) (CONJUNCTS_THEN2 ASSUME_TAC (fun (_ : thm) => ALL_TAC)))) o CONJUNCT2) THEN REWRITE_TAC [DIVIDES_ONE, EXP_1] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers(subfield_generated k s):A ring"), (← q r"p:num")] SPLITTING_TYPES_INTEGER_RING) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_OF_NUM_SUBFIELD_GENERATED] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN SUBGOAL_THEN (← q r"?P. prime_ideal (ring_of_integers(subfield_generated k s)) P /\
        ring_of_num k p IN (P:A->bool)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"subfield_generated k (s:A->bool)"), (← q r"p:num")] NUMBER_FIELD_PRIME_DECOMPOSITION_Q) THEN ANTS_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_SUBFIELD_GENERATED], ALL_TAC] THEN DISCH_THEN (MP_TAC o (CONJUNCT1 o CONJUNCT2)) THEN REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM, RING_OF_NUM_SUBFIELD_GENERATED] THEN MESON_TAC [], ALL_TAC] THEN EQ_TAC THENL [DISCH_THEN (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ASM_SIMP_TAC [], ASM_SIMP_TAC []])

  -- @@RETURN BEGIN
  return { CYCLOTOMIC_SUBFIELD_RESIDUE_DEGREE, CYCLOTOMIC_SUBFIELD_PRIME_DECOMPOSITION,
           CYCLOTOMIC_SUBFIELD_SPLITTING_TYPES,
           CYCLOTOMIC_FIXED_FIELD_PRIME_DECOMPOSITION,
           CYCLOTOMIC_FIXED_FIELD_TOTALLY_SPLIT }
  -- @@RETURN END

end HolANT.CyclotomicSubfieldSplit
