/- ========================================================================= -/
/- ANT: Maps of ideal class groups for an extension of number fields       -/
/- ========================================================================= -/
/- File: HolANT/ClassGroupMaps.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/class_group_maps.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antclassgroupmapsdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/permutations.ml, Library/ring_det.ml, Library/matroids.ml, Library/fieldtheory.ml, Library/symmetric_group.ml, Library/galois.ml, ANT/ideal_arith.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/classgroup_group.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/prime_split.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/relative_degree.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/decomposition.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/splitting_types.ml, ANT/nf_decomposition.ml, ANT/conjugate_ideals.ml, Library/integer.ml, Library/multiplicative.ml, Library/primitive.ml, ANT/dedekind_kummer.ml, ANT/decomposition_field.ml, ANT/split_primes.ml, ANT/ideal_norm_extension.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.ClassGroupMaps fills them).

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
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolLibrary.Matroids
import HolLibrary.FieldTheory
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolANT.IdealArith
import HolLibrary.Products
import HolANT.Algmisc
import HolANT.Integral
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolLibrary.Isum
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.IdealNorm
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.Classgroup
import HolANT.ClassgroupGroup
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.PrimeSplit
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.NfValuation
import HolANT.Integrality
import HolANT.RelativeDegree
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolANT.Decomposition
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.SplittingTypes
import HolANT.NfDecomposition
import HolANT.ConjugateIdeals
import HolLibrary.Integer
import HolLibrary.Multiplicative
import HolLibrary.Primitive
import HolANT.DedekindKummer
import HolANT.DecompositionField
import HolANT.SplitPrimes
import HolANT.IdealNormExtension

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.IdealArith
open HolANT.Algmisc
open HolANT.Integral
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.IdealNorm
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.Classgroup
open HolANT.ClassgroupGroup
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.PrimeSplit
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.NfValuation
open HolANT.Integrality
open HolANT.RelativeDegree
open HolANT.Decomposition
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.SplittingTypes
open HolANT.NfDecomposition
open HolANT.ConjugateIdeals
open HolANT.DedekindKummer
open HolANT.DecompositionField
open HolANT.SplitPrimes
open HolANT.IdealNormExtension

namespace HolANT.ClassGroupMaps

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CARD_DIVIDES_GROUP_EPIMORPHIC_IMAGE CLASS_GROUP
   CLASS_GROUP_HOMOMORPHISM_IDEAL_MAP CLASS_GROUP_POW CONG_DIVIDES_MODULUS
   CONG_SOLVE CONG_SYM DEDEKIND_CLASS_GROUP_EXTENSION
   DEDEKIND_PRINCIPAL_IDEAL_POW_COPRIME DEDEKIND_RING_OF_INTEGERS EQ_TRANS
   EXTENSION FIELD_IMP_NONTRIVIAL_RING FIELD_RING_HOMOMORPHISM_MONOMORPHISM
   FINITE_CLASS_GROUP FORALL_IN_GSPEC FUN_IN_IMAGE GALOIS_IMP_FIELD_EXTENSION
   GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER GROUP_HOMOMORPHISM_OF_ID GROUP_ID
   GROUP_MONOMORPHISM GROUP_POW GROUP_POW_1 GROUP_POW_EQ GROUP_POW_MUL HAS_SIZE
   HAS_SIZE_CLASS_GROUP IDEAL_CLASS_EQ_ID IDEAL_GENERATED_IMAGE_IDEAL_GENERATED
   IMAGE_CLAUSES IMP_CONJ IN_ELIM_THM IN_IMAGE IN_SING MONO_EXISTS MULT_SYM
   NUMBER_FIELD_CLASS_GROUP_FINITE NUMBER_FIELD_GALOIS_PRODUCT_IDEAL_NORM
   NUMBER_FIELD_HOMOMORPHIC_PREIMAGE NUMBER_FIELD_IDEAL_NORM_EQ_0
   NUMBER_FIELD_IDEAL_NORM_EXTENSION NUMBER_FIELD_IDEAL_NORM_IDEAL
   NUMBER_FIELD_IDEAL_NORM_MUL NUMBER_FIELD_IDEAL_NORM_PRINCIPAL
   NUMBER_FIELD_IMP_FIELD NUMBER_FIELD_NORM_INTEGRAL
   RING_HOMOMORPHISM_IN_CARRIER RING_HOMOMORPHISM_RING_OF_INTEGERS
   RING_IDEAL_IDEAL_GENERATED RING_MONOMORPHISM_IMP_HOMOMORPHISM
   RING_MONOMORPHISM_RING_OF_INTEGERS RING_OF_INTEGERS
   RING_OF_INTEGERS_IDEAL_EXTENSION SING_SUBSET SUBSET SUBSET_ANTISYM
   class_number field_extension group_epimorphism group_homomorphism
   group_kernel ideal_classes principal_ideal : thm)
  deriving Inhabited

/-- What class_group_maps.ml uses from Session besides theorems. -/
structure ClassGroupMapsDeps where
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
/- class_group_maps.ml phrases from line 82 to 342                        -/
/- ---------------------------------------------------------------------- -/

structure ClassGroupMaps where
  -- @@FIELDS
  NUMBER_FIELD_CLASS_GROUP_EXTENSION : thm
  NUMBER_FIELD_CLASS_GROUP_NORM : thm
  NUMBER_FIELD_CLASS_GROUP_NORM_EXTENSION : thm
  NUMBER_FIELD_CLASS_GROUP_EXTENSION_NORM_GALOIS : thm
  NUMBER_FIELD_IDEAL_EXTENSION_PRINCIPAL_POW : thm
  NUMBER_FIELD_IDEAL_EXTENSION_PRINCIPAL_COPRIME : thm
  NUMBER_FIELD_CLASS_GROUP_EXTENSION_MONOMORPHISM : thm
  NUMBER_FIELD_CLASS_GROUP_NORM_EPIMORPHISM : thm
  NUMBER_FIELD_CLASS_NUMBER_DIVIDES : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupClassGroupMaps [HolBase] (D : ClassGroupMapsDeps) :
    ExceptT String IO ClassGroupMaps := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, .. } := D
  let { CARD_DIVIDES_GROUP_EPIMORPHIC_IMAGE, CLASS_GROUP,
        CLASS_GROUP_HOMOMORPHISM_IDEAL_MAP, CLASS_GROUP_POW, CONG_DIVIDES_MODULUS,
        CONG_SOLVE, CONG_SYM, DEDEKIND_CLASS_GROUP_EXTENSION,
        DEDEKIND_PRINCIPAL_IDEAL_POW_COPRIME, DEDEKIND_RING_OF_INTEGERS, EQ_TRANS,
        EXTENSION, FIELD_IMP_NONTRIVIAL_RING, FIELD_RING_HOMOMORPHISM_MONOMORPHISM,
        FINITE_CLASS_GROUP, FORALL_IN_GSPEC, FUN_IN_IMAGE, GALOIS_IMP_FIELD_EXTENSION,
        GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER, GROUP_HOMOMORPHISM_OF_ID, GROUP_ID,
        GROUP_MONOMORPHISM, GROUP_POW, GROUP_POW_1, GROUP_POW_EQ, GROUP_POW_MUL,
        HAS_SIZE, HAS_SIZE_CLASS_GROUP, IDEAL_CLASS_EQ_ID,
        IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, IMAGE_CLAUSES, IMP_CONJ, IN_ELIM_THM,
        IN_IMAGE, IN_SING, MONO_EXISTS, MULT_SYM, NUMBER_FIELD_CLASS_GROUP_FINITE,
        NUMBER_FIELD_GALOIS_PRODUCT_IDEAL_NORM, NUMBER_FIELD_HOMOMORPHIC_PREIMAGE,
        NUMBER_FIELD_IDEAL_NORM_EQ_0, NUMBER_FIELD_IDEAL_NORM_EXTENSION,
        NUMBER_FIELD_IDEAL_NORM_IDEAL, NUMBER_FIELD_IDEAL_NORM_MUL,
        NUMBER_FIELD_IDEAL_NORM_PRINCIPAL, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_NORM_INTEGRAL, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MONOMORPHISM_RING_OF_INTEGERS,
        RING_OF_INTEGERS, RING_OF_INTEGERS_IDEAL_EXTENSION, SING_SUBSET, SUBSET,
        SUBSET_ANTISYM, class_number, field_extension, group_epimorphism,
        group_homomorphism, group_kernel, ideal_classes, principal_ideal, .. } := D.core1
  -- @@SCOPE END

  let NUMBER_FIELD_CLASS_GROUP_EXTENSION ← prove
    r"!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> ?f. group_homomorphism(class_group(ring_of_integers k),
                                   class_group(ring_of_integers l)) f /\
                !j. ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
                    ==> f(ideal_class (ring_of_integers k) j) =
                        ideal_class (ring_of_integers l)
                          (ideal_generated (ring_of_integers l) (IMAGE h j))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B")] DEDEKIND_CLASS_GROUP_EXTENSION) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS] THEN DISCH_TAC THEN MATCH_MP_TAC RING_MONOMORPHISM_RING_OF_INTEGERS THEN MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING, NUMBER_FIELD_IMP_FIELD])

  let NUMBER_FIELD_CLASS_GROUP_NORM ← prove
    r"!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> ?g. group_homomorphism(class_group(ring_of_integers l),
                                   class_group(ring_of_integers k)) g /\
                !J. ring_ideal (ring_of_integers l) J /\ ~(J = {ring_0 l})
                    ==> g(ideal_class (ring_of_integers l) J) =
                        ideal_class (ring_of_integers k)
                          (number_field_ideal_norm (k,l) h J)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"ring_of_integers k:A ring"), (← q r"number_field_ideal_norm (k:A ring,l:B ring) h")] CLASS_GROUP_HOMOMORPHISM_IDEAL_MAP) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS] THEN DISCH_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_IDEAL, NUMBER_FIELD_IDEAL_NORM_EQ_0, NUMBER_FIELD_IDEAL_NORM_MUL] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_PRINCIPAL] THEN REWRITE_TAC [principal_ideal] THEN EXISTS_TAC (← q r"algebra_norm (k,l) (h:A->B) a") THEN REWRITE_TAC [] THEN MATCH_MP_TAC NUMBER_FIELD_NORM_INTEGRAL THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_CLASS_GROUP_NORM_EXTENSION ← prove
    r"!k:A ring l:B ring h f g.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        (!j. ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
             ==> f(ideal_class (ring_of_integers k) j) =
                 ideal_class (ring_of_integers l)
                   (ideal_generated (ring_of_integers l) (IMAGE h j))) /\
        (!J. ring_ideal (ring_of_integers l) J /\ ~(J = {ring_0 l})
             ==> g(ideal_class (ring_of_integers l) J) =
                 ideal_class (ring_of_integers k)
                   (number_field_ideal_norm (k,l) h J))
        ==> !c. c IN group_carrier(class_group(ring_of_integers k))
                ==> g(f c) = group_pow (class_group(ring_of_integers k)) c
                               (extension_degree(k,l) h)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_SIMP_TAC [CLASS_GROUP, DEDEKIND_RING_OF_INTEGERS, ideal_classes, FORALL_IN_GSPEC, RING_OF_INTEGERS] THEN X_GEN_TAC (← q r"j:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"j:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT2) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, NUMBER_FIELD_IDEAL_NORM_EXTENSION] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CLASS_GROUP_POW THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS])

  let NUMBER_FIELD_CLASS_GROUP_EXTENSION_NORM_GALOIS ← prove
    r"!k:A ring l:B ring h f g J.
        number_field l /\ galois_extension(k,l) h /\
        (!j. ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
             ==> f(ideal_class (ring_of_integers k) j) =
                 ideal_class (ring_of_integers l)
                   (ideal_generated (ring_of_integers l) (IMAGE h j))) /\
        (!J. ring_ideal (ring_of_integers l) J /\ ~(J = {ring_0 l})
             ==> g(ideal_class (ring_of_integers l) J) =
                 ideal_class (ring_of_integers k)
                   (number_field_ideal_norm (k,l) h J)) /\
        ring_ideal (ring_of_integers l) J /\ ~(J = {ring_0 l})
        ==> f(g(ideal_class (ring_of_integers l) J)) =
            ideal_class (ring_of_integers l)
              (ideal_product (ring_of_integers l)
                 (group_carrier(galois_group (k,l) h)) (\s. IMAGE s J))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN ASM_SIMP_TAC [NUMBER_FIELD_GALOIS_PRODUCT_IDEAL_NORM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_IDEAL, NUMBER_FIELD_IDEAL_NORM_EQ_0])

  let NUMBER_FIELD_IDEAL_EXTENSION_PRINCIPAL_POW ← prove
    r"!k:A ring l:B ring h j.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        ring_ideal (ring_of_integers k) j /\
        principal_ideal (ring_of_integers l)
          (ideal_generated (ring_of_integers l) (IMAGE h j))
        ==> principal_ideal (ring_of_integers k)
              (ideal_pow (ring_of_integers k) j (extension_degree(k,l) h))"
    (REPEAT GEN_TAC THEN REWRITE_TAC [principal_ideal, IMP_CONJ] THEN REPEAT DISCH_TAC THEN FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"x:B") STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC [(← GSYM NUMBER_FIELD_IDEAL_NORM_EXTENSION)] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_PRINCIPAL] THEN EXISTS_TAC (← q r"algebra_norm (k,l) (h:A->B) x") THEN REWRITE_TAC [] THEN MATCH_MP_TAC NUMBER_FIELD_NORM_INTEGRAL THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_IDEAL_EXTENSION_PRINCIPAL_COPRIME ← prove
    r"!k:A ring l:B ring h j.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        ring_ideal (ring_of_integers k) j /\
        coprime(extension_degree(k,l) h,class_number(ring_of_integers k))
        ==> (principal_ideal (ring_of_integers l)
               (ideal_generated (ring_of_integers l) (IMAGE h j)) <=>
             principal_ideal (ring_of_integers k) j)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN EQ_TAC THENL [DISCH_TAC THEN MATCH_MP_TAC DEDEKIND_PRINCIPAL_IDEAL_POW_COPRIME THEN EXISTS_TAC (← q r"extension_degree(k:A ring,l:B ring) h") THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, NUMBER_FIELD_CLASS_GROUP_FINITE] THEN MATCH_MP_TAC NUMBER_FIELD_IDEAL_EXTENSION_PRINCIPAL_POW THEN ASM_REWRITE_TAC [], REWRITE_TAC [principal_ideal] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") (STRIP_ASSUME_TAC o GSYM)) THEN EXISTS_TAC (← q r"(h:A->B) a") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_homomorphism(ring_of_integers k,ring_of_integers l) (h:A->B)") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS], ALL_TAC] THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN ASM_SIMP_TAC [IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, SING_SUBSET] THEN REWRITE_TAC [IMAGE_CLAUSES]])

  let NUMBER_FIELD_CLASS_GROUP_EXTENSION_MONOMORPHISM ← prove
    r"!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        coprime(extension_degree(k,l) h,class_number(ring_of_integers k))
        ==> ?f. group_monomorphism(class_group(ring_of_integers k),
                                   class_group(ring_of_integers l)) f /\
                !j. ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
                    ==> f(ideal_class (ring_of_integers k) j) =
                        ideal_class (ring_of_integers l)
                          (ideal_generated (ring_of_integers l) (IMAGE h j))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_CLASS_GROUP_EXTENSION) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f:((A->bool)->bool)->((B->bool)->bool)") THEN STRIP_TAC THEN ASM_REWRITE_TAC [GROUP_MONOMORPHISM] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"!c. c IN group_carrier(class_group(ring_of_integers k))
        ==> (f:((A->bool)->bool)->((B->bool)->bool)) c =
            group_id(class_group(ring_of_integers l))
            ==> c = group_id(class_group(ring_of_integers k))") ASSUME_TAC THENL [ASM_SIMP_TAC [(← CONJUNCT1 CLASS_GROUP), DEDEKIND_RING_OF_INTEGERS, ideal_classes, FORALL_IN_GSPEC, RING_OF_INTEGERS] THEN X_GEN_TAC (← q r"j:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"j:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT2) THEN ASM_SIMP_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"ideal_generated (ring_of_integers l) (IMAGE (h:A->B) j)")] IDEAL_CLASS_EQ_ID) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool")] IDEAL_CLASS_EQ_ID) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN ASM_MESON_TAC [NUMBER_FIELD_IDEAL_EXTENSION_PRINCIPAL_COPRIME], ALL_TAC] THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [group_kernel, IN_ELIM_THM, IN_SING] THEN X_GEN_TAC (← q r"c:(A->bool)->bool") THEN EQ_TAC THENL [ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [GROUP_ID] THEN ASM_MESON_TAC [GROUP_HOMOMORPHISM_OF_ID]])

  let NUMBER_FIELD_CLASS_GROUP_NORM_EPIMORPHISM ← prove
    r"!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        coprime(extension_degree(k,l) h,class_number(ring_of_integers k))
        ==> ?g. group_epimorphism(class_group(ring_of_integers l),
                                  class_group(ring_of_integers k)) g /\
                !J. ring_ideal (ring_of_integers l) J /\ ~(J = {ring_0 l})
                    ==> g(ideal_class (ring_of_integers l) J) =
                        ideal_class (ring_of_integers k)
                          (number_field_ideal_norm (k,l) h J)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_CLASS_GROUP_EXTENSION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"f:((A->bool)->bool)->((B->bool)->bool)") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_CLASS_GROUP_NORM) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"g:((B->bool)->bool)->((A->bool)->bool)") THEN STRIP_TAC THEN ASM_REWRITE_TAC [group_epimorphism] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"f:((A->bool)->bool)->((B->bool)->bool)"), (← q r"g:((B->bool)->bool)->((A->bool)->bool)")] NUMBER_FIELD_CLASS_GROUP_NORM_EXTENSION) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ASM_MESON_TAC [group_homomorphism], ALL_TAC] THEN REWRITE_TAC [SUBSET, IN_IMAGE] THEN X_GEN_TAC (← q r"c:(A->bool)->bool") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"extension_degree(k:A ring,l:B ring) h"), (← q r"1"), (← q r"class_number(ring_of_integers k:A ring)")] CONG_SOLVE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"m:num")) THEN EXISTS_TAC (← q r"(f:((A->bool)->bool)->((B->bool)->bool))
      (group_pow (class_group(ring_of_integers k)) c m)") THEN CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [group_homomorphism, GROUP_POW, SUBSET, FUN_IN_IMAGE]] THEN ASM_SIMP_TAC [GROUP_POW] THEN ASM_SIMP_TAC [(← GSYM GROUP_POW_MUL)] THEN TRANS_TAC EQ_TRANS (← q r"group_pow (class_group(ring_of_integers k)) (c:(A->bool)->bool) 1") THEN CONJ_TAC THENL [ASM_SIMP_TAC [GROUP_POW_1], ALL_TAC] THEN ASM_SIMP_TAC [GROUP_POW_EQ] THEN MATCH_MP_TAC CONG_DIVIDES_MODULUS THEN EXISTS_TAC (← q r"class_number(ring_of_integers k:A ring)") THEN CONJ_TAC THENL [ONCE_REWRITE_TAC [CONG_SYM] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN ASM_REWRITE_TAC [], MP_TAC (← ISPECL [(← q r"class_group(ring_of_integers k:A ring)"), (← q r"c:(A->bool)->bool")] GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER) THEN MP_TAC (← ISPEC (← q r"k:A ring") HAS_SIZE_CLASS_GROUP) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_SIMP_TAC [HAS_SIZE]])

  let NUMBER_FIELD_CLASS_NUMBER_DIVIDES ← prove
    r"!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        coprime(extension_degree(k,l) h,class_number(ring_of_integers k))
        ==> class_number(ring_of_integers k) divides
            class_number(ring_of_integers l)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_CLASS_GROUP_NORM_EPIMORPHISM) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:((B->bool)->bool)->((A->bool)->bool)") (MP_TAC o CONJUNCT1)) THEN DISCH_THEN (MP_TAC o (MATCH_MP (← REWRITE_RULE [IMP_CONJ] CARD_DIVIDES_GROUP_EPIMORPHIC_IMAGE))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_SIMP_TAC [FINITE_CLASS_GROUP] THEN DISCH_TAC THEN ASM_SIMP_TAC [CLASS_GROUP, DEDEKIND_RING_OF_INTEGERS, class_number])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_CLASS_GROUP_EXTENSION, NUMBER_FIELD_CLASS_GROUP_NORM,
           NUMBER_FIELD_CLASS_GROUP_NORM_EXTENSION,
           NUMBER_FIELD_CLASS_GROUP_EXTENSION_NORM_GALOIS,
           NUMBER_FIELD_IDEAL_EXTENSION_PRINCIPAL_POW,
           NUMBER_FIELD_IDEAL_EXTENSION_PRINCIPAL_COPRIME,
           NUMBER_FIELD_CLASS_GROUP_EXTENSION_MONOMORPHISM,
           NUMBER_FIELD_CLASS_GROUP_NORM_EPIMORPHISM, NUMBER_FIELD_CLASS_NUMBER_DIVIDES }
  -- @@RETURN END

end HolANT.ClassGroupMaps
