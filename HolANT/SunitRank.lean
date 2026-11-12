/- ========================================================================= -/
/- ANT: The S-unit theorem with the rank                                   -/
/- ========================================================================= -/
/- File: HolANT/SunitRank.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/sunit_rank.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antsunitrankdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/products.ml, ANT/algmisc.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, ANT/integral.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/nf_valuation.ml, ANT/classgroup_group.ml, Library/ring_groups.ml, ANT/fingen_group.ml, ANT/prime_split.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/integrality.ml, Multivariate/misc.ml, Multivariate/metric.ml, Multivariate/homology.ml, Multivariate/vectors.ml, Multivariate/determinants.ml, Multivariate/topology.ml, Multivariate/convex.ml, Multivariate/paths.ml, Multivariate/polytope.ml, Multivariate/degree.ml, Multivariate/derivatives.ml, Multivariate/integration.ml, Multivariate/measure.ml, Multivariate/complex_algebra.ml, Multivariate/complexes.ml, Multivariate/canal.ml, Multivariate/transcendentals.ml, Multivariate/realanalysis.ml, Multivariate/moretop.ml, Multivariate/cauchy.ml, Multivariate/complex_ring.ml, Multivariate/complex_field.ml, ANT/complex_embeddings.ml, ANT/fractional_ideals.ml, ANT/dedekind_criteria.ml, ANT/s_integers.ml, ANT/sunits.ml, ANT/power_basis.ml, ANT/infinite_places.ml, ANT/linear_forms.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/quadratic.ml, ANT/minkowski_theory.ml, ANT/unit_theorem.ml, ANT/valuation_ring.ml, ANT/dedekind_absolute.ml, ANT/product_formula.ml, ANT/regulator.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.SunitRank fills them).

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
import HolLibrary.Products
import HolANT.Algmisc
import HolLibrary.Matroids
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolLibrary.FieldTheory
import HolANT.Integral
import HolANT.IdealArith
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolLibrary.Isum
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.RingOfIntegers
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.NormIndex
import HolANT.Classgroup
import HolANT.NfValuation
import HolANT.ClassgroupGroup
import HolLibrary.RingGroups
import HolANT.FingenGroup
import HolANT.PrimeSplit
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.Integrality
import HolMultiLib.Misc
import HolMultiLib.Metric
import HolMultiLib.Homology
import HolMultiLib.Vectors
import HolMultiLib.Determinants
import HolMultiLib.Topology
import HolMultiLib.Convex
import HolMultiLib.Paths
import HolMultiLib.Polytope
import HolMultiLib.Degree
import HolMultiLib.Derivatives
import HolMultiLib.Integration
import HolMultiLib.Measure
import HolMultiLib.ComplexAlgebra
import HolMultiLib.Complexes
import HolMultiLib.Canal
import HolMultiLib.Transcendentals
import HolMultiLib.RealAnalysis
import HolMultiLib.MoreTop
import HolMultiLib.Cauchy
import HolMultiLib.ComplexRing
import HolMultiLib.ComplexField
import HolANT.ComplexEmbeddings
import HolANT.FractionalIdeals
import HolANT.DedekindCriteria
import HolANT.SIntegers
import HolANT.Sunits
import HolANT.PowerBasis
import HolANT.InfinitePlaces
import HolANT.LinearForms
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.Quadratic
import HolANT.MinkowskiTheory
import HolANT.UnitTheorem
import HolANT.ValuationRing
import HolANT.DedekindAbsolute
import HolANT.ProductFormula
import HolANT.Regulator

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
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.RingOfIntegers
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.NormIndex
open HolANT.Classgroup
open HolANT.NfValuation
open HolANT.ClassgroupGroup
open HolANT.FingenGroup
open HolANT.PrimeSplit
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.Integrality
open HolANT.ComplexEmbeddings
open HolANT.FractionalIdeals
open HolANT.DedekindCriteria
open HolANT.SIntegers
open HolANT.Sunits
open HolANT.PowerBasis
open HolANT.InfinitePlaces
open HolANT.LinearForms
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.Quadratic
open HolANT.MinkowskiTheory
open HolANT.UnitTheorem
open HolANT.ValuationRing
open HolANT.DedekindAbsolute
open HolANT.ProductFormula
open HolANT.Regulator

namespace HolANT.SunitRank

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ABELIAN_GROUP_DISCRETE_DEPENDENT ABELIAN_S_UNIT_GROUP ABELIAN_UNIT_GROUP
   CARD_DELETE CARD_EQ_0 CARD_IMAGE_INJ CARD_IMAGE_LE CARD_SUBSET CARD_UNION
   CARD_UNION_LE COMPLEX_EMBEDDINGS_NONEMPTY COMPLEX_EMBEDDINGS_NORM_MUL
   COMPLEX_NORM_CX COMPLEX_RING_OF_NUM DEDEKIND_RING_OF_INTEGERS DISJOINT
   DIVIDES_REFL EMPTY_SUBSET EQ_SYM_EQ EQ_TRANS EXP_EQ_0 EXTENSION
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_MUL_LINV
   FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS
   FINITELY_GENERATED_S_UNIT_GROUP FINITE_COMPLEX_EMBEDDINGS FINITE_DELETE
   FINITE_IMAGE FINITE_INFINITE_PLACES FINITE_RESTRICT FINITE_SUBSET
   FINITE_UNION FORALL_IN_IMAGE FUN_EQ_THM FUN_IN_IMAGE GROUP_HOMOMORPHISM
   GROUP_HOMOMORPHISM_ZPOW GROUP_POW_EQ_ID
   GROUP_REAL_MULTIPLICATIVE_LOG_SUM_ZPOW GROUP_SUM_EQ
   GROUP_SUM_HOMOMORPHIC_IMAGE GROUP_SUM_SUPERSET GROUP_ZPOW GROUP_ZPOW_0
   HAS_SIZE IDEAL_GENERATED_EQ_0 IDEAL_NORM_GT_1 IDEAL_NORM_IN_IDEAL
   IDEAL_NORM_POS IDEAL_POW_EQ_ZERO IDEAL_VALUATION_IDEAL_POW
   IDEAL_VALUATION_PRIME IMAGE_EQ_EMPTY IMAGE_I INFINITE_PLACES_MUL
   INFINITE_PLACES_POS INTEGRAL_DOMAIN_MUL_EQ_0 INTEGRAL_DOMAIN_RING_OF_INTEGERS
   INT_ABS_NEG INT_ABS_NUM INT_IMAGE INT_LE_LMUL INT_LE_REFL INT_MUL_RID
   INT_OF_NUM_EQ INT_OF_NUM_LT INT_POS IN_DELETE IN_ELIM_THM IN_IMAGE IN_INTER
   IN_RING_IDEAL_RMUL IN_UNION I_THM LET_TRANS LE_ANTISYM LOG_1 LOG_POS_LT
   LOG_ZPOW LT_NZ MEMBER_NOT_EMPTY MONO_EXISTS NORM_POS_LE NOT_IN_EMPTY NOT_LE
   NOT_LT NPRODUCT_DELETE NPRODUCT_POS_LT NUMBER_FIELD_CLASS_NUMBER_POS : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (NUMBER_FIELD_FUNDAMENTAL_UNITS NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2
   NUMBER_FIELD_PRINCIPAL_IDEAL_POW_CLASS_NUMBER NUMBER_FIELD_PRODUCT_FORMULA
   NUMBER_FIELD_RING_OF_NUM_EQ_0 NUMBER_FIELD_VALUATION_1
   NUMBER_FIELD_VALUATION_INTEGRAL NUMBER_FIELD_VALUATION_MUL
   NUMBER_FIELD_VALUATION_POW NUMBER_FIELD_VALUATION_PRIME_IDEAL
   NUMBER_FIELD_VALUATION_RING_OF_INTEGERS NUMBER_FIELD_VALUATION_UNIT
   PRIME_IMP_PROPER_IDEAL PRIME_IMP_RING_IDEAL PRODUCT_CONST
   PRODUCT_FACTOR_BOUND PRODUCT_INV PRODUCT_LE PRODUCT_POS_LT PRODUCT_SUPERSET
   PSUBSET REAL_ABS_NUM REAL_ARCH_POW2 REAL_ENTIRE REAL_INV_1 REAL_LE_LMUL
   REAL_LE_MUL2 REAL_LE_REFL REAL_LE_TRANS REAL_LTE_TRANS REAL_LT_IMP_LE
   REAL_LT_IMP_NZ REAL_LT_INV2 REAL_LT_INV_EQ REAL_MUL_ASSOC REAL_MUL_LID
   REAL_MUL_RID REAL_MUL_RINV REAL_NOT_LE REAL_NOT_LT REAL_OF_NUM_EQ
   REAL_OF_NUM_LE REAL_OF_NUM_LT REAL_POS REAL_POW_1 REAL_POW_ADD REAL_POW_LE2
   REAL_POW_LT REAL_POW_MONO REAL_ZPOW_0 REAL_ZPOW_ADD REAL_ZPOW_LT
   REAL_ZPOW_NEG REAL_ZPOW_NUM RIGHT_IMP_EXISTS_THM RING_0
   RING_HOMOMORPHISM_RING_OF_NUM RING_INV RING_MUL RING_MUL_ASSOC RING_MUL_LID
   RING_MUL_RZERO RING_OF_INTEGERS RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE
   RING_OF_INTEGERS_FINITE_QUOTIENT RING_OF_INTEGERS_SUBSET
   RING_OF_INTEGERS_UNIT_NONZERO RING_OF_NUM RING_OF_NUM_EXP RING_OF_NUM_MUL
   SKOLEM_THM SUBSET SUBSET_UNION SUM_DELTA SUM_EQ S_UNIT_GROUP
   S_UNIT_GROUP_EMPTY S_UNIT_GROUP_MONO S_UNIT_GROUP_POW UNION_SUBSET UNIT_GROUP
   complex_embeddings infinite_places int_eq int_of_num_th lemma o_DEF
   principal_ideal proper_ideal : thm)
  deriving Inhabited

/-- What sunit_rank.ml uses from Session besides theorems. -/
structure SunitRankDeps where
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
/- sunit_rank.ml phrases from line 86 to 676                              -/
/- ---------------------------------------------------------------------- -/

structure SunitRank01 where
  -- @@FIELDS
  GROUP_HOMOMORPHISM_UNIT_GROUP_S_UNIT_GROUP : thm
  S_UNIT_GROUP_INFINITE_PLACES : thm
  S_UNIT_GROUP_PRIME_SIZE : thm
  NUMBER_FIELD_VALUATION_DENOMINATOR : thm
  S_UNIT_GROUP_PRODUCT_FORMULA : thm
  S_UNIT_GROUP_BOUNDED_EMBEDDINGS : thm
  S_UNIT_GROUP_BOUNDED_FINITE : thm
  S_UNIT_GROUP_DEPENDENT : thm
  NUMBER_FIELD_PRIME_POW_GENERATOR : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupSunitRank01 [HolBase] (D : SunitRankDeps) :
    ExceptT String IO SunitRank01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC,
        INT_ARITH, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV,
        SET_TAC, .. } := D
  let { ABELIAN_GROUP_DISCRETE_DEPENDENT, ABELIAN_S_UNIT_GROUP, CARD_DELETE, CARD_EQ_0,
        CARD_IMAGE_LE, CARD_SUBSET, CARD_UNION_LE, COMPLEX_EMBEDDINGS_NONEMPTY,
        COMPLEX_EMBEDDINGS_NORM_MUL, COMPLEX_NORM_CX, COMPLEX_RING_OF_NUM,
        DEDEKIND_RING_OF_INTEGERS, EMPTY_SUBSET, EXP_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_MUL_LINV, FINITE_COMPLEX_EMBEDDINGS, FINITE_DELETE, FINITE_IMAGE,
        FINITE_INFINITE_PLACES, FINITE_RESTRICT, FINITE_SUBSET, FINITE_UNION,
        FUN_EQ_THM, GROUP_HOMOMORPHISM, IDEAL_GENERATED_EQ_0, IDEAL_NORM_IN_IDEAL,
        IDEAL_NORM_POS, IDEAL_POW_EQ_ZERO, IDEAL_VALUATION_IDEAL_POW,
        IDEAL_VALUATION_PRIME, IMAGE_EQ_EMPTY, IMAGE_I, INFINITE_PLACES_MUL,
        INFINITE_PLACES_POS, INTEGRAL_DOMAIN_MUL_EQ_0,
        INTEGRAL_DOMAIN_RING_OF_INTEGERS, INT_ABS_NEG, INT_ABS_NUM, INT_IMAGE,
        INT_LE_LMUL, INT_LE_REFL, INT_MUL_RID, INT_OF_NUM_EQ, INT_OF_NUM_LT, INT_POS,
        IN_DELETE, IN_ELIM_THM, IN_IMAGE, IN_RING_IDEAL_RMUL, IN_UNION, I_THM,
        LET_TRANS, LT_NZ, MEMBER_NOT_EMPTY, MONO_EXISTS, NORM_POS_LE, NOT_LE,
        NPRODUCT_DELETE, NPRODUCT_POS_LT, .. } := D.core1
  let { NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2,
        NUMBER_FIELD_PRINCIPAL_IDEAL_POW_CLASS_NUMBER, NUMBER_FIELD_PRODUCT_FORMULA,
        NUMBER_FIELD_RING_OF_NUM_EQ_0, NUMBER_FIELD_VALUATION_INTEGRAL,
        NUMBER_FIELD_VALUATION_MUL, NUMBER_FIELD_VALUATION_POW,
        NUMBER_FIELD_VALUATION_PRIME_IDEAL, NUMBER_FIELD_VALUATION_RING_OF_INTEGERS,
        PRIME_IMP_RING_IDEAL, PRODUCT_CONST, PRODUCT_FACTOR_BOUND, PRODUCT_INV,
        PRODUCT_LE, PRODUCT_POS_LT, PRODUCT_SUPERSET, REAL_ABS_NUM, REAL_ARCH_POW2,
        REAL_INV_1, REAL_LE_LMUL, REAL_LE_MUL2, REAL_LE_REFL, REAL_LE_TRANS,
        REAL_LTE_TRANS, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_INV2, REAL_LT_INV_EQ,
        REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_RID, REAL_MUL_RINV, REAL_NOT_LE,
        REAL_NOT_LT, REAL_OF_NUM_EQ, REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_POS,
        REAL_POW_1, REAL_POW_ADD, REAL_POW_LE2, REAL_POW_LT, REAL_POW_MONO,
        REAL_ZPOW_0, REAL_ZPOW_ADD, REAL_ZPOW_LT, REAL_ZPOW_NEG, REAL_ZPOW_NUM, RING_0,
        RING_HOMOMORPHISM_RING_OF_NUM, RING_INV, RING_MUL, RING_MUL_ASSOC,
        RING_MUL_LID, RING_MUL_RZERO, RING_OF_INTEGERS,
        RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE, RING_OF_INTEGERS_FINITE_QUOTIENT,
        RING_OF_NUM, RING_OF_NUM_EXP, RING_OF_NUM_MUL, SUBSET, S_UNIT_GROUP,
        S_UNIT_GROUP_EMPTY, S_UNIT_GROUP_MONO, UNIT_GROUP, complex_embeddings,
        infinite_places, principal_ideal, .. } := D.core2
  -- @@SCOPE END

  let GROUP_HOMOMORPHISM_UNIT_GROUP_S_UNIT_GROUP ← prove
    r"!k:A ring S.
        number_field k
        ==> group_homomorphism(unit_group(ring_of_integers k),s_unit_group k S)
                              I"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [GROUP_HOMOMORPHISM, I_THM, IMAGE_I] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{}:(A->bool)->bool"), (← q r"S:(A->bool)->bool")] S_UNIT_GROUP_MONO) THEN ASM_SIMP_TAC [EMPTY_SUBSET, S_UNIT_GROUP_EMPTY, UNIT_GROUP], ASM_SIMP_TAC [S_UNIT_GROUP, UNIT_GROUP, RING_OF_INTEGERS]])

  let S_UNIT_GROUP_INFINITE_PLACES ← prove
    r"!k S v:A->real.
        number_field k /\ v IN infinite_places k
        ==> (!x. x IN group_carrier(s_unit_group k S) ==> &0 < v x) /\
            (!x y. x IN group_carrier(s_unit_group k S) /\
                   y IN group_carrier(s_unit_group k S)
                   ==> v(group_mul (s_unit_group k S) x y) = v x * v y)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN ASM_SIMP_TAC [S_UNIT_GROUP, IN_ELIM_THM] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL [MATCH_MP_TAC INFINITE_PLACES_POS, MATCH_MP_TAC INFINITE_PLACES_MUL] THEN ASM_MESON_TAC [])

  let S_UNIT_GROUP_PRIME_SIZE ← prove
    r"!k S P:A->bool.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})
        ==> (!x. x IN group_carrier(s_unit_group k S)
                 ==> &0 < &(ideal_norm (ring_of_integers k) P) zpow
                          dedekind_valuation (ring_of_integers k,k) I P x) /\
            (!x y. x IN group_carrier(s_unit_group k S) /\
                   y IN group_carrier(s_unit_group k S)
                   ==> &(ideal_norm (ring_of_integers k) P) zpow
                        dedekind_valuation (ring_of_integers k,k) I P
                          (group_mul (s_unit_group k S) x y) =
                       &(ideal_norm (ring_of_integers k) P) zpow
                        dedekind_valuation (ring_of_integers k,k) I P x *
                       &(ideal_norm (ring_of_integers k) P) zpow
                        dedekind_valuation (ring_of_integers k,k) I P y)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"1 <= ideal_norm (ring_of_integers k) (P:A->bool)") ASSUME_TAC THENL [MATCH_MP_TAC IDEAL_NORM_POS THEN MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN ASM_SIMP_TAC [S_UNIT_GROUP, IN_ELIM_THM] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL [MATCH_MP_TAC REAL_ZPOW_LT THEN REWRITE_TAC [REAL_OF_NUM_LT] THEN ASM_ARITH_TAC, ASM_SIMP_TAC [NUMBER_FIELD_VALUATION_MUL] THEN MATCH_MP_TAC REAL_ZPOW_ADD THEN REWRITE_TAC [REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC])

  let NUMBER_FIELD_VALUATION_DENOMINATOR ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INT_ARITH (← q r"&0:int <= a /\ &0 <= b ==> &0 <= a + b")
    let r2 ← INT_ARITH (← q r"!n:int. n <= a /\ --n <= b ==> &0 <= a + b")
    let r3 ← INT_ARITH (← q r"&0:int < x <=> &1 <= x")
    let r4 ← ARITH_RULE (← q r"2 <= n ==> 0 < n")
    prove
      r"!k (S:(A->bool)->bool) n.
          number_field k /\ FINITE S
          ==> ?d. ~(d = 0) /\
                  !x. x IN ring_carrier k /\
                      (!P. P IN S /\ prime_ideal (ring_of_integers k) P /\
                           ~(P = {ring_0 k})
                           ==> --(&n) <=
                               dedekind_valuation (ring_of_integers k,k) I P x) /\
                      (!P. prime_ideal (ring_of_integers k) P /\
                           ~(P = {ring_0 k}) /\ ~(P IN S)
                           ==> &0 <=
                               dedekind_valuation (ring_of_integers k,k) I P x)
                      ==> ring_mul k (ring_of_num k d) x
                          IN ring_carrier(ring_of_integers k)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN ABBREV_TAC (← q r"S' = {P | P IN S /\ prime_ideal (ring_of_integers k) P /\
                          ~(P = {ring_0 k:A})}") THEN SUBGOAL_THEN (← q r"FINITE(S':(A->bool)->bool)") ASSUME_TAC THENL [EXPAND_TAC "S'" THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!P. P IN S' <=>
          P IN S /\ prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k:A})") ASSUME_TAC THENL [EXPAND_TAC "S'" THEN SET_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"m = nproduct S' (\P. ideal_norm (ring_of_integers k) (P:A->bool))") THEN SUBGOAL_THEN (← q r"~(m = 0)") ASSUME_TAC THENL [EXPAND_TAC "m" THEN REWRITE_TAC [(← GSYM LT_NZ)] THEN MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2, r4], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_num k m IN ring_carrier(ring_of_integers k) /\
      ~(ring_of_num k m = ring_0 (k:A ring))") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_RING_OF_NUM_EQ_0] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"m:num")] RING_OF_NUM) THEN REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"!P. P IN S'
          ==> &1 <= dedekind_valuation (ring_of_integers k,k) I P
                      (ring_of_num k m:A)") ASSUME_TAC THENL [X_GEN_TAC (← q r"P:A->bool") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"prime_ideal (ring_of_integers k) (P:A->bool) /\ ~(P = {ring_0 k}) /\
        FINITE(ring_carrier(quotient_ring (ring_of_integers k) P))") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool"), (← q r"ring_of_num k m:A")] NUMBER_FIELD_VALUATION_PRIME_IDEAL) THEN ASM_REWRITE_TAC [r3] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"\P. ideal_norm (ring_of_integers k) (P:A->bool)"), (← q r"S':(A->bool)->bool"), (← q r"P:A->bool")] NPRODUCT_DELETE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"ring_of_num k (ideal_norm (ring_of_integers k) P):A"), (← q r"ring_of_num k (nproduct (S' DELETE P)
                         (\P. ideal_norm (ring_of_integers k) P)):A")] IN_RING_IDEAL_RMUL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, (← GSYM RING_OF_NUM_MUL)] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool")] IDEAL_NORM_IN_IDEAL) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS], MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"nproduct ((S':(A->bool)->bool) DELETE P)
                    (\P. ideal_norm (ring_of_integers (k:A ring)) P)")] RING_OF_NUM) THEN REWRITE_TAC [RING_OF_INTEGERS]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!P. P IN S'
          ==> &n <= dedekind_valuation (ring_of_integers k,k) I P
                      (ring_of_num k (m EXP n):A)") ASSUME_TAC THENL [X_GEN_TAC (← q r"P:A->bool") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"prime_ideal (ring_of_integers k) (P:A->bool) /\ ~(P = {ring_0 k})") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [RING_OF_NUM_EXP, NUMBER_FIELD_VALUATION_POW, RING_OF_NUM] THEN GEN_REWRITE_TAC LAND_CONV [(← GSYM INT_MUL_RID)] THEN MATCH_MP_TAC INT_LE_LMUL THEN ASM_SIMP_TAC [INT_POS], ALL_TAC] THEN EXISTS_TAC (← q r"m EXP n") THEN ASM_REWRITE_TAC [EXP_EQ_0] THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"x = ring_0(k:A ring)") THENL [ASM_SIMP_TAC [RING_MUL_RZERO, RING_OF_NUM] THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_0) THEN REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_num k (m EXP n) IN ring_carrier(ring_of_integers k) /\
      ring_of_num k (m EXP n) IN ring_carrier k /\
      ~(ring_of_num k (m EXP n) = ring_0 (k:A ring))") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_RING_OF_NUM_EQ_0, RING_OF_NUM, EXP_EQ_0] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"m EXP n")] RING_OF_NUM) THEN REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_mul k (ring_of_num k (m EXP n)) (x:A)")] NUMBER_FIELD_VALUATION_INTEGRAL) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_MUL, FIELD_IMP_INTEGRAL_DOMAIN, INTEGRAL_DOMAIN_MUL_EQ_0], DISCH_THEN SUBST1_TAC] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_VALUATION_MUL] THEN ASM_CASES_TAC (← q r"(P:A->bool) IN S") THENL [MATCH_MP_TAC r2 THEN EXISTS_TAC (← q r"&n:int") THEN ASM_SIMP_TAC [], MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_of_num k (m EXP n):A")] NUMBER_FIELD_VALUATION_INTEGRAL) THEN ASM_SIMP_TAC []])

  let S_UNIT_GROUP_PRODUCT_FORMULA ← prove
    r"!k (S:(A->bool)->bool) x.
        number_field k /\ x IN group_carrier(s_unit_group k S)
        ==> product (complex_embeddings k) (\g. norm(g x)) =
            product {P | P IN S /\ prime_ideal (ring_of_integers k) P /\
                         ~(P = {ring_0 k})}
                    (\P. &(ideal_norm (ring_of_integers k) P) zpow
                         dedekind_valuation (ring_of_integers k,k) I P x)"
    (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"number_field(k:A ring)") THEN ASM_SIMP_TAC [S_UNIT_GROUP] THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] NUMBER_FIELD_PRODUCT_FORMULA) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"V = {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
             ~(dedekind_valuation (ring_of_integers k,k) I P (x:A) = &0)}") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!P:A->bool. P IN V ==> (&0:real) < &(ideal_norm (ring_of_integers k) P)") ASSUME_TAC THENL [EXPAND_TAC "V" THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool")] NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2) THEN ASM_REWRITE_TAC [REAL_OF_NUM_LT] THEN DISCH_THEN (MP_TAC o CONJUNCT2) THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 < product V (\P. &(ideal_norm (ring_of_integers k) P) zpow
                        dedekind_valuation (ring_of_integers k,k) I P (x:A))") ASSUME_TAC THENL [MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_SIMP_TAC [REAL_ZPOW_LT], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_eq z2))))) THEN ASM_SIMP_TAC [REAL_ZPOW_NEG, PRODUCT_INV] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"( * ) (product V (\P. &(ideal_norm (ring_of_integers k) P) zpow
            dedekind_valuation (ring_of_integers k,k) I P (x:A)))"))) THEN ASM_SIMP_TAC [REAL_MUL_ASSOC, REAL_MUL_RINV, REAL_LT_IMP_NZ, REAL_MUL_LID, REAL_MUL_RID] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC PRODUCT_SUPERSET THEN EXPAND_TAC "V" THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"dedekind_valuation (ring_of_integers k,k) I P (x:A) = &0") (fun th => REWRITE_TAC [th, REAL_ZPOW_0]) THEN ASM_MESON_TAC [])

  let S_UNIT_GROUP_BOUNDED_EMBEDDINGS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"(y:real) <= z ==> x <= y ==> x <= z")
    let r2 ← REAL_ARITH (← q r"&1 <= (b:real) ==> ~(b = &0)")
    let r17 ← ARITH_RULE (← q r"~(n = 0) ==> 1 <= s + n")
    prove
      r"!k (S:(A->bool)->bool) v0 b x.
          number_field k /\ FINITE S /\ v0 IN infinite_places k /\ &1 <= b /\
          x IN group_carrier(s_unit_group k S) /\
          (!v. v IN infinite_places k /\ ~(v = v0)
               ==> inv b <= v x /\ v x <= b) /\
          (!P. P IN S /\ prime_ideal (ring_of_integers k) P /\
               ~(P = {ring_0 k})
               ==> &(ideal_norm (ring_of_integers k) P) zpow
                   dedekind_valuation (ring_of_integers k,k) I P x <= b)
          ==> !g. g IN complex_embeddings k
                  ==> norm(g x) <= b pow (CARD S + CARD(complex_embeddings k))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_COMPLEX_EMBEDDINGS)) THEN SUBGOAL_THEN (← q r"product (complex_embeddings k) (\g. norm((g:A->complex) x)) <=
      b pow CARD(S:(A->bool)->bool)") ASSUME_TAC THENL [ASM_SIMP_TAC [S_UNIT_GROUP_PRODUCT_FORMULA] THEN TRANS_TAC REAL_LE_TRANS (← q r"product {P | P IN S /\ prime_ideal (ring_of_integers k) P /\
                     ~(P = {ring_0 k:A})} (\P. b)") THEN CONJ_TAC THENL [MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC [FINITE_RESTRICT, IN_ELIM_THM] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_ZPOW_LT THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool")] NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2) THEN ASM_REWRITE_TAC [REAL_OF_NUM_LT] THEN DISCH_THEN (MP_TAC o CONJUNCT2) THEN ARITH_TAC, ASM_SIMP_TAC [PRODUCT_CONST, FINITE_RESTRICT] THEN MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC [] THEN SET_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"(b:real) <= b pow (CARD(S:(A->bool)->bool) +
                         CARD(complex_embeddings(k:A ring)))") ASSUME_TAC THENL [GEN_REWRITE_TAC LAND_CONV [(← GSYM REAL_POW_1)] THEN MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r17 THEN ASM_SIMP_TAC [CARD_EQ_0, COMPLEX_EMBEDDINGS_NONEMPTY], ALL_TAC] THEN SUBGOAL_THEN (← q r"!h:A->complex. h IN complex_embeddings k
                     ==> (\y. norm(h y)) IN infinite_places k") ASSUME_TAC THENL [REWRITE_TAC [infinite_places, IN_IMAGE] THEN MESON_TAC [], ALL_TAC] THEN X_GEN_TAC (← q r"g:A->complex") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"(\y. norm((g:A->complex) y)) = v0") THENL [ALL_TAC, TRANS_TAC REAL_LE_TRANS (← q r"b:real") THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"\y:A. norm((g:A->complex) y)")) o (checkM (fun th => (do let z10 ← (do let z11 ← (pure th); pure (concl z11)); canM (fun z12 => (do let z13 ← (pure z12); find_termM (fun z14 => (do let z16 ← (pure z14); let z15 ← (q r"inv(b:real)"); pure (z15 == z16))) z13)) z10))))) THEN ASM_SIMP_TAC []] THEN ASM_CASES_TAC (← q r"norm((g:A->complex) x) <= &1") THENL [TRANS_TAC REAL_LE_TRANS (← q r"b:real") THEN ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC, RULE_ASSUM_TAC (REWRITE_RULE [REAL_NOT_LE])] THEN MP_TAC (← ISPECL [(← q r"\h:A->complex. norm(h(x:A))"), (← q r"complex_embeddings(k:A ring)"), (← q r"g:A->complex"), (← q r"b:real"), (← q r"(b:real) pow CARD(S:(A->bool)->bool)")] PRODUCT_FACTOR_BOUND) THEN ASM_REWRITE_TAC [NORM_POS_LE] THEN ANTS_TAC THENL [X_GEN_TAC (← q r"h:A->complex") THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"(\y. norm((h:A->complex) y)) = v0") THENL [SUBGOAL_THEN (← q r"norm((h:A->complex) x) = norm((g:A->complex) x)") SUBST1_TAC THENL [UNDISCH_TAC (← q r"(\y. norm((h:A->complex) y)) = v0") THEN UNDISCH_TAC (← q r"(\y. norm((g:A->complex) y)) = v0") THEN REWRITE_TAC [FUN_EQ_THM] THEN MESON_TAC [], ALL_TAC] THEN TRANS_TAC REAL_LE_TRANS (← q r"(&1:real) * &1") THEN CONJ_TAC THENL [REAL_ARITH_TAC, MATCH_MP_TAC REAL_LE_MUL2] THEN ASM_REAL_ARITH_TAC, FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"\y:A. norm((h:A->complex) y)")) o (checkM (fun th => (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); canM (fun z5 => (do let z6 ← (pure z5); find_termM (fun z7 => (do let z9 ← (pure z7); let z8 ← (q r"inv(b:real)"); pure (z8 == z9))) z6)) z3))))) THEN ASM_SIMP_TAC [] THEN STRIP_TAC THEN TRANS_TAC REAL_LE_TRANS (← q r"(b:real) * inv b") THEN CONJ_TAC THENL [ASM_SIMP_TAC [REAL_MUL_RINV, r2, REAL_LE_REFL], MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]], ALL_TAC] THEN REWRITE_TAC [(← GSYM REAL_POW_ADD)] THEN MATCH_MP_TAC r1 THEN MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC [] THEN ARITH_TAC)

  let S_UNIT_GROUP_BOUNDED_FINITE ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"(a:real) pow m"
    let q2 ← q r"b:real"
    let v3 ← ISPECL [q2, q1] REAL_LT_INV2
    let v4 ← GSYM REAL_NOT_LT
    let q5 ← q r"inv((a:real) pow m)"
    let q6 ← q r"&0 < (a:real) pow m /\ &0 < (b:real)"
    let q7 ← q r"v:int"
    let v8 ← SPEC q7 INT_IMAGE
    let q9 ← q r"m:num"
    let q10 ← q r"(&2:real) pow m"
    let q11 ← q r"&2 pow N <= (a:real) pow m"
    let v12 ← GSYM NOT_LE
    let q13 ← q r"m:num"
    let q14 ← q r"!m. (a:real) pow m <= b ==> m < N"
    let p15 ← prove r"!a b v N. &2 <= a /\ inv b <= a zpow v /\ a zpow v <= b /\ b < &2 pow N
               ==> abs v < &N" (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN q14 ASSUME_TAC THENL [X_GEN_TAC q13 THEN DISCH_TAC THEN REWRITE_TAC [v12] THEN DISCH_TAC THEN SUBGOAL_THEN q11 MP_TAC THENL [TRANS_TAC REAL_LE_TRANS q10 THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC [] THEN CONV_TAC REAL_RAT_REDUCE_CONV, MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC], ASM_REAL_ARITH_TAC], ALL_TAC] THEN DISJ_CASES_THEN (X_CHOOSE_THEN q9 SUBST_ALL_TAC) v8 THEN REWRITE_TAC [INT_ABS_NEG, INT_ABS_NUM, INT_OF_NUM_LT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [REAL_ZPOW_NUM, REAL_ZPOW_NEG]) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN q6 STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC, MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC q5 THEN ASM_REWRITE_TAC [REAL_LT_INV_EQ] THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC], ALL_TAC] THEN REWRITE_TAC [v4] THEN DISCH_TAC THEN MP_TAC v3 THEN ASM_REAL_ARITH_TAC)
    let valbound := p15
    let q16 ← q r"x:A"
    let q17 ← q r"b:real"
    let q18 ← q r"v0:A->real"
    let q19 ← q r"S:(A->bool)->bool"
    let q20 ← q r"k:A ring"
    let v21 ← ISPECL [q20, q19, q18, q17, q16] S_UNIT_GROUP_BOUNDED_EMBEDDINGS
    let q22 ← q r"(g:A->complex) IN complex_embeddings k"
    let q23 ← q r"norm((g:A->complex) D) = &d"
    let q24 ← q r"x:A"
    let q25 ← q r"D:A"
    let q26 ← q r"g:A->complex"
    let q27 ← q r"k:A ring"
    let v28 ← ISPECL [q27, q26, q25, q24] COMPLEX_EMBEDDINGS_NORM_MUL
    let q29 ← q r"g:A->complex"
    let q30 ← q r"P:A->bool"
    let q31 ← q r"b:real"
    let q32 ← q r"&(ideal_norm (ring_of_integers k) (P:A->bool)):real"
    let q33 ← q r"abs(v:int) < &N ==> --(&N) <= v"
    let r34 ← INT_ARITH q33
    let q35 ← q r"P:A->bool"
    let q36 ← q r"ring_mul k D (x:A)"
    let q37 ← q r"(x:A) IN group_carrier(s_unit_group k S)"
    let q38 ← q r"(x:A) IN ring_carrier k /\ ~(x = ring_0 k) /\
      !P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
          ~(P IN S)
          ==> dedekind_valuation (ring_of_integers k,k) I P x = &0"
    let q39 ← q r"x:A"
    let q40 ← q r"IMAGE (\y. ring_mul k (ring_inv k D) y)
       {y | y IN ring_carrier(ring_of_integers k) /\
            !g. g IN complex_embeddings k
                ==> norm((g:A->complex) y) <=
                    &d * b pow (CARD(S:(A->bool)->bool) +
                                CARD(complex_embeddings k))}"
    let q41 ← q r"(D:A) IN ring_carrier k /\ ~(D = ring_0 k)"
    let q42 ← q r"D = ring_of_num k d:A"
    let q43 ← q r"d:num"
    let q44 ← q r"N:num"
    let q45 ← q r"S:(A->bool)->bool"
    let q46 ← q r"k:A ring"
    let v47 ← ISPECL [q46, q45, q44] NUMBER_FIELD_VALUATION_DENOMINATOR
    let q48 ← q r"b:real"
    let v49 ← SPEC q48 REAL_ARCH_POW2
    let q50 ← q r"N:num"
    prove
      r"!k (S:(A->bool)->bool) v0 b.
            number_field k /\ FINITE S /\ v0 IN infinite_places k /\ &1 <= b
            ==> FINITE
                 {x | x IN group_carrier(s_unit_group k S) /\
                      (!v. v IN infinite_places k /\ ~(v = v0)
                           ==> inv b <= v x /\ v x <= b) /\
                      (!P. P IN S /\ prime_ideal (ring_of_integers k) P /\
                           ~(P = {ring_0 k})
                           ==> inv b <= &(ideal_norm (ring_of_integers k) P) zpow
                                        dedekind_valuation
                                          (ring_of_integers k,k) I P x /\
                               &(ideal_norm (ring_of_integers k) P) zpow
                               dedekind_valuation (ring_of_integers k,k) I P x
                               <= b)}"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN X_CHOOSE_TAC q50 v49 THEN MP_TAC v47 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q43 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "den"))) THEN ABBREV_TAC q42 THEN SUBGOAL_THEN q41 STRIP_ASSUME_TAC THENL [EXPAND_TAC "D" THEN ASM_SIMP_TAC [RING_OF_NUM, NUMBER_FIELD_RING_OF_NUM_EQ_0], ALL_TAC] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC q40 THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC [RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE], ALL_TAC] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_IMAGE] THEN X_GEN_TAC q39 THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pl") (LABEL_TAC "pr"))) THEN SUBGOAL_THEN q38 STRIP_ASSUME_TAC THENL [UNDISCH_TAC q37 THEN ASM_SIMP_TAC [S_UNIT_GROUP, IN_ELIM_THM], ALL_TAC] THEN EXISTS_TAC q36 THEN REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [RING_MUL_ASSOC, RING_INV, FIELD_MUL_LINV, RING_MUL_LID], USE_THEN "den" MATCH_MP_TAC THEN ASM_SIMP_TAC [INT_LE_REFL] THEN X_GEN_TAC q35 THEN STRIP_TAC THEN MATCH_MP_TAC r34 THEN MATCH_MP_TAC valbound THEN EXISTS_TAC q32 THEN EXISTS_TAC q31 THEN USE_THEN "pr" (MP_TAC o (SPEC q30)) THEN ASM_SIMP_TAC [REAL_OF_NUM_LE, NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2], X_GEN_TAC q29 THEN DISCH_TAC THEN MP_TAC v28 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN q23 SUBST1_TAC THENL [EXPAND_TAC "D" THEN UNDISCH_TAC q22 THEN REWRITE_TAC [complex_embeddings, IN_ELIM_THM] THEN STRIP_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th)])) THEN REWRITE_TAC [COMPLEX_RING_OF_NUM, COMPLEX_NORM_CX, REAL_ABS_NUM], ALL_TAC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_POS] THEN MP_TAC v21 THEN ASM_SIMP_TAC []])

  let S_UNIT_GROUP_DEPENDENT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"max (&1) (b:real) = b"
    let q2 ← q r"(&1:real)"
    let q3 ← q r"b:real"
    let v4 ← ISPECL [q3, q2] REAL_LT_INV2
    let v5 ← GSYM REAL_NOT_LT
    let q6 ← q r"&0 < (b:real)"
    let q7 ← q r"&1 <= (b:real)"
    let p8 ← prove r"!y b. &0 < y /\ inv b <= y /\ y <= b
           ==> inv(max (&1) b) <= y /\ y <= max (&1) b" (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN q7 ASSUME_TAC THENL [SUBGOAL_THEN q6 ASSUME_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [v5] THEN DISCH_TAC THEN MP_TAC v4 THEN ASM_REWRITE_TAC [REAL_INV_1] THEN ASM_REAL_ARITH_TAC, SUBGOAL_THEN q1 SUBST1_TAC THENL [ASM_REAL_ARITH_TAC, ASM_REWRITE_TAC []]])
    let lemma := p8
    let q9 ← q r"S':(A->bool)->bool"
    let q10 ← q r"\P (x:A). &(ideal_norm (ring_of_integers k) P) zpow
                   dedekind_valuation (ring_of_integers k,k) I P x"
    let v11 ← ISPECL [q10, q9] CARD_IMAGE_LE
    let q12 ← q r"CARD(infinite_places(k:A ring) DELETE v0) +
        CARD(IMAGE (\P (x:A). &(ideal_norm (ring_of_integers k) P) zpow
                              dedekind_valuation (ring_of_integers k,k) I P x)
                   (S':(A->bool)->bool))"
    let q13 ← q r"P:A->bool"
    let q14 ← q r"\x:A. &(ideal_norm (ring_of_integers k) P) zpow
                  dedekind_valuation (ring_of_integers k,k) I P x"
    let q15 ← q r"P:A->bool"
    let q16 ← q r"S:(A->bool)->bool"
    let q17 ← q r"k:A ring"
    let v18 ← ISPECL [q17, q16, q15] S_UNIT_GROUP_PRIME_SIZE
    let q19 ← q r"P:A->bool"
    let q20 ← q r"v:A->real"
    let q21 ← q r"S:(A->bool)->bool"
    let q22 ← q r"k:A ring"
    let v23 ← ISPECL [q22, q21, q20] S_UNIT_GROUP_INFINITE_PLACES
    let q24 ← q r"v:A->real"
    let q25 ← q r"x:A"
    let q26 ← q r"{x | x IN group_carrier(s_unit_group k S) /\
             (!v. v IN infinite_places k /\ ~(v = v0)
                  ==> inv(max (&1) b) <= v x /\ v x <= max (&1) b) /\
             (!P. P IN S /\ prime_ideal (ring_of_integers k) P /\
                  ~(P = {ring_0 k})
                  ==> inv(max (&1) b) <=
                      &(ideal_norm (ring_of_integers k) P) zpow
                      dedekind_valuation (ring_of_integers k,k) I P (x:A) /\
                      &(ideal_norm (ring_of_integers k) P) zpow
                      dedekind_valuation (ring_of_integers k,k) I P x
                      <= max (&1) b)}"
    let q27 ← q r"b:real"
    let q28 ← q r"(P:A->bool) IN S'"
    let q29 ← q r"P:A->bool"
    let q30 ← q r"S:(A->bool)->bool"
    let q31 ← q r"k:A ring"
    let v32 ← ISPECL [q31, q30, q29] S_UNIT_GROUP_PRIME_SIZE
    let q33 ← q r"P:A->bool"
    let q34 ← q r"i:A->real"
    let q35 ← q r"S:(A->bool)->bool"
    let q36 ← q r"k:A ring"
    let v37 ← ISPECL [q36, q35, q34] S_UNIT_GROUP_INFINITE_PLACES
    let q38 ← q r"y:A"
    let q39 ← q r"x:A"
    let q40 ← q r"i:A->real"
    let q41 ← q r"(P:A->bool) IN S'"
    let q42 ← q r"P:A->bool"
    let q43 ← q r"S:(A->bool)->bool"
    let q44 ← q r"k:A ring"
    let v45 ← ISPECL [q44, q43, q42] S_UNIT_GROUP_PRIME_SIZE
    let q46 ← q r"P:A->bool"
    let q47 ← q r"i:A->real"
    let q48 ← q r"S:(A->bool)->bool"
    let q49 ← q r"k:A ring"
    let v50 ← ISPECL [q49, q48, q47] S_UNIT_GROUP_INFINITE_PLACES
    let q51 ← q r"x:A"
    let q52 ← q r"i:A->real"
    let q53 ← q r"t:A->bool"
    let q54 ← q r"\(i:A->real) (x:A). i x"
    let q55 ← q r"(infinite_places k DELETE v0) UNION
       IMAGE (\P (x:A). &(ideal_norm (ring_of_integers k) P) zpow
                        dedekind_valuation (ring_of_integers k,k) I P x)
             (S':(A->bool)->bool)"
    let q56 ← q r"s_unit_group k (S:(A->bool)->bool)"
    let v57 ← ISPECL [q56, q55, q54, q53] ABELIAN_GROUP_DISCRETE_DEPENDENT
    let q58 ← q r"group_id(s_unit_group k (S:(A->bool)->bool)) = ring_1 k"
    let q59 ← q r"FINITE(S':(A->bool)->bool) /\ CARD S' <= CARD(S:(A->bool)->bool)"
    let q60 ← q r"S' = {P | P IN S /\ prime_ideal (ring_of_integers k) P /\
                          ~(P = {ring_0 k:A})}"
    let q61 ← q r"?v0:A->real. v0 IN infinite_places k"
    prove
      r"!k (S:(A->bool)->bool) t.
          number_field k /\ FINITE S /\ FINITE t /\
          t SUBSET group_carrier(s_unit_group k S) /\
          (CARD(infinite_places k) - 1) + CARD S < CARD t
          ==> ?n. (?x. x IN t /\ ~(n x = &0)) /\
                  group_sum (s_unit_group k S) t
                    (\x. group_zpow (s_unit_group k S) x (n x)) =
                  ring_1 k"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_INFINITE_PLACES)) THEN SUBGOAL_THEN q61 STRIP_ASSUME_TAC THENL [REWRITE_TAC [MEMBER_NOT_EMPTY, infinite_places, IMAGE_EQ_EMPTY] THEN ASM_SIMP_TAC [COMPLEX_EMBEDDINGS_NONEMPTY], ALL_TAC] THEN ABBREV_TAC q60 THEN SUBGOAL_THEN q59 STRIP_ASSUME_TAC THENL [EXPAND_TAC "S'" THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC [], MATCH_MP_TAC CARD_SUBSET THEN ASM_SIMP_TAC [SUBSET, IN_ELIM_THM]], ALL_TAC] THEN SUBGOAL_THEN q58 (SUBST1_TAC o SYM) THENL [ASM_SIMP_TAC [S_UNIT_GROUP], ALL_TAC] THEN MP_TAC v57 THEN REWRITE_TAC [ABELIAN_S_UNIT_GROUP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [FINITE_UNION, FINITE_DELETE, FINITE_IMAGE] THEN REWRITE_TAC [IN_UNION, IN_DELETE] THEN REPEAT CONJ_TAC THENL [MAP_EVERY X_GEN_TAC [q52, q51] THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL [STRIP_TAC THEN MP_TAC v50 THEN ASM_SIMP_TAC [], REWRITE_TAC [IN_IMAGE] THEN DISCH_THEN (X_CHOOSE_THEN q46 (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN REWRITE_TAC [] THEN MP_TAC v45 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN UNDISCH_TAC q41 THEN EXPAND_TAC "S'" THEN SIMP_TAC [IN_ELIM_THM], ASM_SIMP_TAC []]], MAP_EVERY X_GEN_TAC [q40, q39, q38] THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL [STRIP_TAC THEN MP_TAC v37 THEN ASM_SIMP_TAC [], REWRITE_TAC [IN_IMAGE] THEN DISCH_THEN (X_CHOOSE_THEN q33 (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN REWRITE_TAC [] THEN MP_TAC v32 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN UNDISCH_TAC q28 THEN EXPAND_TAC "S'" THEN SIMP_TAC [IN_ELIM_THM], ASM_SIMP_TAC []]], X_GEN_TAC q27 THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC q26 THEN CONJ_TAC THENL [MATCH_MP_TAC S_UNIT_GROUP_BOUNDED_FINITE THEN ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC q25 THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd")) THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [X_GEN_TAC q24 THEN STRIP_TAC THEN MATCH_MP_TAC lemma THEN CONJ_TAC THENL [MP_TAC v23 THEN ASM_SIMP_TAC [], USE_THEN "bd" MATCH_MP_TAC THEN ASM_REWRITE_TAC []], X_GEN_TAC q19 THEN STRIP_TAC THEN MATCH_MP_TAC lemma THEN CONJ_TAC THENL [MP_TAC v18 THEN ASM_SIMP_TAC [], USE_THEN "bd" (MP_TAC o (SPEC q14)) THEN REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN DISJ2_TAC THEN REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC q13 THEN REWRITE_TAC [] THEN EXPAND_TAC "S'" THEN ASM_REWRITE_TAC [IN_ELIM_THM]]], TRANS_TAC LET_TRANS q12 THEN CONJ_TAC THENL [MATCH_MP_TAC CARD_UNION_LE THEN ASM_SIMP_TAC [FINITE_DELETE, FINITE_IMAGE], ALL_TAC] THEN ASM_SIMP_TAC [CARD_DELETE] THEN MP_TAC v11 THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC])

  let NUMBER_FIELD_PRIME_POW_GENERATOR ← prove
    r"!k P:A->bool.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})
        ==> ?a. a IN ring_carrier(ring_of_integers k) /\ ~(a = ring_0 k) /\
                !Q. prime_ideal (ring_of_integers k) Q /\ ~(Q = {ring_0 k})
                    ==> dedekind_valuation (ring_of_integers k,k) I Q a =
                        &(if Q = P then class_number(ring_of_integers k)
                          else 0)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_RING_OF_INTEGERS)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool")] NUMBER_FIELD_PRINCIPAL_IDEAL_POW_CLASS_NUMBER) THEN ASM_REWRITE_TAC [principal_ideal] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"~(a:A = ring_0 k)") ASSUME_TAC THENL [DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"class_number(ring_of_integers(k:A ring))")] IDEAL_POW_EQ_ZERO) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_RING_OF_INTEGERS, NUMBER_FIELD_IMP_FIELD] THEN UNDISCH_TAC (← q r"ideal_generated (ring_of_integers k) {a:A} =
      ideal_pow (ring_of_integers k) P (class_number(ring_of_integers k))") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [IDEAL_GENERATED_EQ_0, RING_OF_INTEGERS], ASM_REWRITE_TAC []] THEN X_GEN_TAC (← q r"Q:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_VALUATION_RING_OF_INTEGERS] THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_POW, IDEAL_VALUATION_PRIME, RING_OF_INTEGERS] THEN REWRITE_TAC [INT_OF_NUM_EQ] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ARITH_TAC)

  -- @@RETURN BEGIN
  return { GROUP_HOMOMORPHISM_UNIT_GROUP_S_UNIT_GROUP, S_UNIT_GROUP_INFINITE_PLACES,
           S_UNIT_GROUP_PRIME_SIZE, NUMBER_FIELD_VALUATION_DENOMINATOR,
           S_UNIT_GROUP_PRODUCT_FORMULA, S_UNIT_GROUP_BOUNDED_EMBEDDINGS,
           S_UNIT_GROUP_BOUNDED_FINITE, S_UNIT_GROUP_DEPENDENT,
           NUMBER_FIELD_PRIME_POW_GENERATOR }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- sunit_rank.ml phrases from line 712 to 988                             -/
/- ---------------------------------------------------------------------- -/

structure SunitRank02 where
  -- @@FIELDS
  S_UNIT_GROUP_INDEPENDENT : thm
  S_UNIT_GROUP_FUNDAMENTAL : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupSunitRank02 [HolBase] (D : SunitRankDeps) (BSunitRank01 : SunitRank01) :
    ExceptT String IO SunitRank02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, REAL_ARITH_TAC, .. } := D
  let { ABELIAN_S_UNIT_GROUP, ABELIAN_UNIT_GROUP, CARD_IMAGE_INJ, CARD_UNION, DISJOINT,
        DIVIDES_REFL, EQ_SYM_EQ, EQ_TRANS, EXTENSION,
        FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS,
        FINITELY_GENERATED_S_UNIT_GROUP, FINITE_IMAGE, FINITE_RESTRICT, FINITE_UNION,
        FORALL_IN_IMAGE, FUN_IN_IMAGE, GROUP_HOMOMORPHISM_ZPOW, GROUP_POW_EQ_ID,
        GROUP_REAL_MULTIPLICATIVE_LOG_SUM_ZPOW, GROUP_SUM_EQ,
        GROUP_SUM_HOMOMORPHIC_IMAGE, GROUP_SUM_SUPERSET, GROUP_ZPOW, GROUP_ZPOW_0,
        HAS_SIZE, IDEAL_NORM_GT_1, INT_OF_NUM_EQ, IN_ELIM_THM, IN_IMAGE, IN_INTER,
        IN_UNION, I_THM, LE_ANTISYM, LOG_1, LOG_POS_LT, LOG_ZPOW, MONO_EXISTS,
        NOT_IN_EMPTY, NOT_LT, NUMBER_FIELD_CLASS_NUMBER_POS, .. } := D.core1
  let { NUMBER_FIELD_FUNDAMENTAL_UNITS, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_VALUATION_1, NUMBER_FIELD_VALUATION_UNIT, PRIME_IMP_PROPER_IDEAL,
        PRIME_IMP_RING_IDEAL, PSUBSET, REAL_ENTIRE, REAL_LT_IMP_NZ, REAL_OF_NUM_EQ,
        REAL_OF_NUM_LT, REAL_ZPOW_0, RIGHT_IMP_EXISTS_THM,
        RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS_SUBSET,
        RING_OF_INTEGERS_UNIT_NONZERO, SKOLEM_THM, SUBSET, SUBSET_UNION, SUM_DELTA,
        SUM_EQ, S_UNIT_GROUP, S_UNIT_GROUP_POW, UNION_SUBSET, UNIT_GROUP, int_eq,
        int_of_num_th, o_DEF, proper_ideal, .. } := D.core2
  let { GROUP_HOMOMORPHISM_UNIT_GROUP_S_UNIT_GROUP, NUMBER_FIELD_PRIME_POW_GENERATOR,
        S_UNIT_GROUP_DEPENDENT, S_UNIT_GROUP_PRIME_SIZE, .. } := BSunitRank01
  -- @@SCOPE END

  let S_UNIT_GROUP_INDEPENDENT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"2 <= n <=> 1 < n")
    prove
      r"!k (S:(A->bool)->bool).
          number_field k /\ FINITE S /\
          (!P. P IN S ==> prime_ideal (ring_of_integers k) P /\
                          ~(P = {ring_0 k}))
          ==> ?t. t HAS_SIZE ((CARD(infinite_places k) - 1) + CARD S) /\
                  t SUBSET group_carrier(s_unit_group k S) /\
                  !n. group_sum (s_unit_group k S) t
                        (\x. group_zpow (s_unit_group k S) x (n x)) = ring_1 k
                      ==> !x. x IN t ==> n x = &0"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP NUMBER_FIELD_FUNDAMENTAL_UNITS)) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t0:A->bool") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ind") (fun (_ : thm) => ALL_TAC))))) THEN SUBGOAL_THEN (← q r"?x. !P. P IN (S:(A->bool)->bool)
              ==> (x P) IN ring_carrier(ring_of_integers(k:A ring)) /\
                  ~(x P = ring_0 k) /\
                  !Q. prime_ideal (ring_of_integers k) Q /\ ~(Q = {ring_0 k})
                      ==> dedekind_valuation (ring_of_integers k,k) I Q (x P) =
                          &(if Q = P then class_number(ring_of_integers k)
                            else 0)") (X_CHOOSE_THEN (← q r"x:(A->bool)->A") (LABEL_TAC "x")) THENL [REWRITE_TAC [(← GSYM SKOLEM_THM), (← GSYM RIGHT_IMP_EXISTS_THM)] THEN X_GEN_TAC (← q r"P:A->bool") THEN DISCH_TAC THEN MATCH_MP_TAC NUMBER_FIELD_PRIME_POW_GENERATOR THEN ASM_SIMP_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"h = class_number(ring_of_integers(k:A ring))") THEN SUBGOAL_THEN (← q r"1 <= h") ASSUME_TAC THENL [EXPAND_TAC "h" THEN ASM_SIMP_TAC [NUMBER_FIELD_CLASS_NUMBER_POS], ALL_TAC] THEN SUBGOAL_THEN (← q r"!u:A. u IN t0 ==> u IN ring_carrier k /\ ~(u = ring_0 k) /\
                       !Q. prime_ideal (ring_of_integers k) Q /\
                           ~(Q = {ring_0 k})
                           ==> dedekind_valuation (ring_of_integers k,k) I Q u =
                               &0") ASSUME_TAC THENL [X_GEN_TAC (← q r"u:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_unit (ring_of_integers k) (u:A)") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"u:A")] RING_OF_INTEGERS_UNIT_NONZERO) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"u:A")] NUMBER_FIELD_VALUATION_UNIT) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!P Q. P IN S /\ prime_ideal (ring_of_integers k) Q /\ ~(Q = {ring_0 k})
            ==> dedekind_valuation (ring_of_integers k,k) I Q
                  ((x:(A->bool)->A) P) = &(if Q = P then h else 0)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN USE_THEN "x" (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN DISCH_THEN (MATCH_MP_TAC o (CONJUNCT2 o CONJUNCT2)) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!P. P IN S ==> (x:(A->bool)->A) P IN group_carrier(s_unit_group k S)") ASSUME_TAC THENL [X_GEN_TAC (← q r"P:A->bool") THEN DISCH_TAC THEN ASM_SIMP_TAC [S_UNIT_GROUP, IN_ELIM_THM] THEN USE_THEN "x" (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, STRIP_TAC] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN X_GEN_TAC (← q r"Q:A->bool") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPECL [(← q r"P:A->bool"), (← q r"Q:A->bool")]) o (checkM (fun th => (do if ← (do let z48 ← (do let z49 ← (pure th); pure (concl z49)); pure (is_forall z48)) then (do let z50 ← (do let z51 ← (pure th); pure (concl z51)); canM (fun z52 => (do let z53 ← (pure z52); find_termM (fun z54 => (do let z56 ← (pure z54); let z55 ← (q r"h:num"); pure (z55 == z56))) z53)) z50) else pure false))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!P Q. P IN S /\ Q IN S /\ (x:(A->bool)->A) P = x Q ==> P = Q") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o ((SPECL [(← q r"P:A->bool"), (← q r"P:A->bool")]) o (checkM (fun th => (do if ← (do let z39 ← (do let z40 ← (pure th); pure (concl z40)); pure (is_forall z39)) then (do let z41 ← (do let z42 ← (pure th); pure (concl z42)); canM (fun z43 => (do let z44 ← (pure z43); find_termM (fun z45 => (do let z47 ← (pure z45); let z46 ← (q r"h:num"); pure (z46 == z47))) z44)) z41) else pure false))))) THEN FIRST_ASSUM (MP_TAC o ((SPECL [(← q r"Q:A->bool"), (← q r"P:A->bool")]) o (checkM (fun th => (do if ← (do let z30 ← (do let z31 ← (pure th); pure (concl z31)); pure (is_forall z30)) then (do let z32 ← (do let z33 ← (pure th); pure (concl z33)); canM (fun z34 => (do let z35 ← (pure z34); find_termM (fun z36 => (do let z38 ← (pure z36); let z37 ← (q r"h:num"); pure (z37 == z38))) z35)) z32) else pure false))))) THEN ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_TAC] THEN ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_TAC] THEN ASM_CASES_TAC (← q r"P:A->bool = Q") THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"dedekind_valuation (ring_of_integers k,k) I P ((x:(A->bool)->A) P) =
        &(if P = P then h else 0)") THEN UNDISCH_TAC (← q r"dedekind_valuation (ring_of_integers k,k) I P ((x:(A->bool)->A) Q) =
        &(if P = Q then h else 0)") THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [INT_OF_NUM_EQ] THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"DISJOINT (t0:A->bool) (IMAGE (x:(A->bool)->A) S)") ASSUME_TAC THENL [REWRITE_TAC [DISJOINT, EXTENSION, IN_INTER, IN_IMAGE, NOT_IN_EMPTY] THEN X_GEN_TAC (← q r"u:A") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"P:A->bool") STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"prime_ideal (ring_of_integers k) (P:A->bool) /\
                    ~(P = {ring_0 k})") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"dedekind_valuation (ring_of_integers k,k) I P (u:A) = &0") MP_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"dedekind_valuation (ring_of_integers k,k) I P (u:A) = &h") (fun th => REWRITE_TAC [th, INT_OF_NUM_EQ]) THENL [FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun z27 => (do let z28 ← (do let z29 ← (pure z27); pure (concl z29)); pure (is_eq z28))))) THEN FIRST_X_ASSUM (MP_TAC o ((SPECL [(← q r"P:A->bool"), (← q r"P:A->bool")]) o (checkM (fun th => (do if ← (do let z18 ← (do let z19 ← (pure th); pure (concl z19)); pure (is_forall z18)) then (do let z20 ← (do let z21 ← (pure th); pure (concl z21)); canM (fun z22 => (do let z23 ← (pure z22); find_termM (fun z24 => (do let z26 ← (pure z24); let z25 ← (q r"h:num"); pure (z25 == z26))) z23)) z20) else pure false))))) THEN ASM_REWRITE_TAC [], ASM_ARITH_TAC], ALL_TAC] THEN EXISTS_TAC (← q r"(t0:A->bool) UNION IMAGE (x:(A->bool)->A) S") THEN REPEAT CONJ_TAC THENL [UNDISCH_TAC (← q r"(t0:A->bool) HAS_SIZE CARD(infinite_places(k:A ring)) - 1") THEN REWRITE_TAC [HAS_SIZE] THEN STRIP_TAC THEN ASM_SIMP_TAC [FINITE_UNION, FINITE_IMAGE, CARD_UNION, (← GSYM DISJOINT)] THEN AP_TERM_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC [], REWRITE_TAC [UNION_SUBSET, SUBSET, FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"u:A") THEN DISCH_TAC THEN ASM_SIMP_TAC [S_UNIT_GROUP, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN X_GEN_TAC (← q r"n:A->int") THEN DISCH_THEN (LABEL_TAC "rel") THEN ABBREV_TAC (← q r"t = (t0:A->bool) UNION IMAGE (x:(A->bool)->A) S") THEN SUBGOAL_THEN (← q r"FINITE(t:A->bool) /\ t SUBSET group_carrier(s_unit_group k S) /\
      (t0:A->bool) SUBSET t /\ !P. P IN S ==> (x:(A->bool)->A) P IN t") STRIP_ASSUME_TAC THENL [EXPAND_TAC "t" THEN UNDISCH_TAC (← q r"(t0:A->bool) HAS_SIZE CARD(infinite_places(k:A ring)) - 1") THEN SIMP_TAC [HAS_SIZE, FINITE_UNION, FINITE_IMAGE] THEN STRIP_TAC THEN ASM_REWRITE_TAC [SUBSET_UNION, IN_UNION, UNION_SUBSET] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN ASM_SIMP_TAC [FUN_IN_IMAGE, FINITE_IMAGE] THEN X_GEN_TAC (← q r"u:A") THEN DISCH_TAC THEN ASM_SIMP_TAC [S_UNIT_GROUP, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!Q y. Q IN S /\ y IN t
            ==> dedekind_valuation (ring_of_integers k,k) I Q y =
                &(if y = (x:(A->bool)->A) Q then h else 0)") ASSUME_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"Q:A->bool"), (← q r"y:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"prime_ideal (ring_of_integers k) (Q:A->bool) /\
                    ~(Q = {ring_0 k})") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN UNDISCH_TAC (← q r"(y:A) IN t") THEN EXPAND_TAC "t" THEN REWRITE_TAC [IN_UNION, IN_IMAGE] THEN STRIP_TAC THENL [SUBGOAL_THEN (← q r"~(y = (x:(A->bool)->A) Q)") (fun th => REWRITE_TAC [th]) THENL [UNDISCH_TAC (← q r"DISJOINT (t0:A->bool) (IMAGE (x:(A->bool)->A) S)") THEN REWRITE_TAC [DISJOINT, EXTENSION, IN_INTER, IN_IMAGE, NOT_IN_EMPTY] THEN ASM_MESON_TAC [], ASM_MESON_TAC []], FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPECL [(← q r"x':A->bool"), (← q r"Q:A->bool")]) o (checkM (fun th => (do if ← (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_forall z2)) then (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); canM (fun z6 => (do let z7 ← (pure z6); find_termM (fun z8 => (do let z10 ← (pure z8); let z9 ← (q r"h:num"); pure (z9 == z10))) z7)) z4) else pure false) then (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); canM (fun z13 => (do let z14 ← (pure z13); find_termM (fun z15 => (do let z17 ← (pure z15); let z16 ← (q r"ring_0:A ring->A"); pure (z16 == z17))) z14)) z11) else pure false))))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN AP_TERM_TAC THEN ASM_CASES_TAC (← q r"Q:A->bool = x'") THEN ASM_REWRITE_TAC [] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"!Q. Q IN S ==> (n:A->int)((x:(A->bool)->A) Q) = &0") ASSUME_TAC THENL [X_GEN_TAC (← q r"Q:A->bool") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"prime_ideal (ring_of_integers k) (Q:A->bool) /\
                    ~(Q = {ring_0 k})") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"2 <= ideal_norm (ring_of_integers k) (Q:A->bool)") ASSUME_TAC THENL [REWRITE_TAC [r1] THEN MATCH_MP_TAC IDEAL_NORM_GT_1 THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS_FINITE_QUOTIENT] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP PRIME_IMP_PROPER_IDEAL)) THEN SIMP_TAC [proper_ideal, PSUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(&0:real) < &(ideal_norm (ring_of_integers k) (Q:A->bool))") ASSUME_TAC THENL [REWRITE_TAC [REAL_OF_NUM_LT] THEN ASM_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"S:(A->bool)->bool"), (← q r"Q:A->bool")] S_UNIT_GROUP_PRIME_SIZE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"s_unit_group k (S:(A->bool)->bool)"), (← q r"\y:A. &(ideal_norm (ring_of_integers k) (Q:A->bool)) zpow
               dedekind_valuation (ring_of_integers k,k) I Q y"), (← q r"\y:A. y"), (← q r"n:A->int"), (← q r"t:A->bool")] GROUP_REAL_MULTIPLICATIVE_LOG_SUM_ZPOW) THEN ANTS_TAC THENL [REWRITE_TAC [ABELIAN_S_UNIT_GROUP] THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [SUBSET], ALL_TAC] THEN REWRITE_TAC [] THEN USE_THEN "rel" SUBST1_TAC THEN SIMP_TAC [NUMBER_FIELD_VALUATION_1, (← ASSUME (← q r"field(k:A ring)")), REAL_ZPOW_0, LOG_1] THEN SUBGOAL_THEN (← q r"!i:A. i IN t
              ==> real_of_int(n i) *
                  log(&(ideal_norm (ring_of_integers k) (Q:A->bool)) zpow
                      dedekind_valuation (ring_of_integers k,k) I Q i) =
                  if i = (x:(A->bool)->A) Q
                  then real_of_int(n i) *
                       (&h * log(&(ideal_norm (ring_of_integers k) Q)))
                  else &0") MP_TAC THENL [X_GEN_TAC (← q r"i:A") THEN DISCH_TAC THEN ASM_SIMP_TAC [LOG_ZPOW] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [int_of_num_th] THEN REAL_ARITH_TAC, ALL_TAC] THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP SUM_EQ th)])) THEN ASM_SIMP_TAC [SUM_DELTA] THEN GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN REWRITE_TAC [REAL_ENTIRE] THEN SUBGOAL_THEN (← q r"~(&h:real = &0) /\
        ~(log(&(ideal_norm (ring_of_integers k) (Q:A->bool))) = &0)") (fun th => REWRITE_TAC [th]) THENL [CONJ_TAC THENL [REWRITE_TAC [REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC, MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC [REAL_OF_NUM_LT] THEN ASM_ARITH_TAC], REWRITE_TAC [int_eq, int_of_num_th]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!u:A. u IN t0 ==> (n:A->int) u = &0") ASSUME_TAC THENL [USE_THEN "ind" MATCH_MP_TAC THEN MP_TAC (← ISPECL [(← q r"unit_group(ring_of_integers k):A group"), (← q r"s_unit_group k (S:(A->bool)->bool)"), (← q r"I:A->A"), (← q r"t0:A->bool"), (← q r"\y:A. group_zpow (unit_group(ring_of_integers k)) y (n y)")] GROUP_SUM_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [ABELIAN_UNIT_GROUP, ABELIAN_S_UNIT_GROUP, GROUP_HOMOMORPHISM_UNIT_GROUP_S_UNIT_GROUP] THEN ANTS_TAC THENL [CONJ_TAC THENL [MATCH_MP_TAC FINITE_RESTRICT THEN UNDISCH_TAC (← q r"(t0:A->bool) HAS_SIZE CARD(infinite_places(k:A ring)) - 1") THEN SIMP_TAC [HAS_SIZE], X_GEN_TAC (← q r"u:A") THEN DISCH_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC GROUP_ZPOW THEN REWRITE_TAC [UNIT_GROUP, IN_ELIM_THM] THEN ASM_MESON_TAC []], ALL_TAC] THEN REWRITE_TAC [I_THM, o_DEF] THEN DISCH_THEN SUBST1_TAC THEN USE_THEN "rel" (SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN TRANS_TAC EQ_TRANS (← q r"group_sum (s_unit_group k S) t0
          (\x:A. group_zpow (s_unit_group k S) x ((n:A->int) x))") THEN CONJ_TAC THENL [MATCH_MP_TAC GROUP_SUM_SUPERSET THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"y:A") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"?Q. Q IN S /\ y = (x:(A->bool)->A) Q") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"(y:A) IN t") THEN EXPAND_TAC "t" THEN REWRITE_TAC [IN_UNION, IN_IMAGE] THEN ASM_MESON_TAC [], ASM_SIMP_TAC [GROUP_ZPOW_0]], MATCH_MP_TAC GROUP_SUM_EQ THEN X_GEN_TAC (← q r"u:A") THEN DISCH_TAC THEN REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"unit_group(ring_of_integers k):A group"), (← q r"s_unit_group k (S:(A->bool)->bool)"), (← q r"I:A->A")] GROUP_HOMOMORPHISM_ZPOW) THEN ASM_SIMP_TAC [GROUP_HOMOMORPHISM_UNIT_GROUP_S_UNIT_GROUP, I_THM] THEN DISCH_THEN (MATCH_MP_TAC o GSYM) THEN REWRITE_TAC [UNIT_GROUP, IN_ELIM_THM] THEN ASM_MESON_TAC []], ALL_TAC] THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN UNDISCH_TAC (← q r"(y:A) IN t") THEN EXPAND_TAC "t" THEN REWRITE_TAC [IN_UNION, IN_IMAGE] THEN STRIP_TAC THEN ASM_SIMP_TAC [])

  let S_UNIT_GROUP_FUNDAMENTAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r4 ← ARITH_RULE (← q r"~(n = 0) ==> 1 <= n")
    prove
      r"!k (S:(A->bool)->bool).
          number_field k /\ FINITE S /\
          (!P. P IN S ==> prime_ideal (ring_of_integers k) P /\
                          ~(P = {ring_0 k}))
          ==> ?t. t HAS_SIZE ((CARD(infinite_places k) - 1) + CARD S) /\
                  t SUBSET group_carrier(s_unit_group k S) /\
                  (!n. group_sum (s_unit_group k S) t
                         (\u. group_zpow (s_unit_group k S) u (n u)) =
                       ring_1 k
                       ==> !u. u IN t ==> n u = &0) /\
                  !x. x IN group_carrier(s_unit_group k S)
                      ==> ?z n. z IN ring_carrier k /\
                                (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                                x = ring_mul k z
                                     (group_sum (s_unit_group k S) t
                                       (\u. group_zpow (s_unit_group k S) u
                                                       (n u)))"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"s_unit_group k (S:(A->bool)->bool)") FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS) THEN ASM_SIMP_TAC [ABELIAN_S_UNIT_GROUP, FINITELY_GENERATED_S_UNIT_GROUP] THEN SUBGOAL_THEN (← q r"group_id(s_unit_group k (S:(A->bool)->bool)) = ring_1 k") (fun th => REWRITE_TAC [th]) THENL [ASM_SIMP_TAC [S_UNIT_GROUP], ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:A->bool") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ind") (CONJUNCTS_THEN2 (LABEL_TAC "rep") (LABEL_TAC "rank"))))) THEN ASM_REWRITE_TAC [HAS_SIZE] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [(← GSYM LE_ANTISYM)] THEN CONJ_TAC THENL [REWRITE_TAC [(← GSYM NOT_LT)] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"S:(A->bool)->bool"), (← q r"t:A->bool")] S_UNIT_GROUP_DEPENDENT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"n:A->int") (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"u:A") STRIP_ASSUME_TAC) ASSUME_TAC)) THEN UNDISCH_TAC (← q r"~((n:A->int) u = &0)") THEN REWRITE_TAC [] THEN USE_THEN "ind" (MP_TAC o (SPEC (← q r"n:A->int"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"S:(A->bool)->bool")] S_UNIT_GROUP_INDEPENDENT) THEN ASM_REWRITE_TAC [HAS_SIZE] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"s:A->bool") (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) STRIP_ASSUME_TAC)) THEN USE_THEN "rank" MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [S_UNIT_GROUP, (← ASSUME (← q r"number_field(k:A ring)"))] THEN FIRST_ASSUM ACCEPT_TAC], X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN USE_THEN "rep" (MP_TAC o (SPEC (← q r"x:A"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"z:A") THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"n:A->int") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier k") ASSUME_TAC THENL [UNDISCH_TAC (← q r"(z:A) IN group_carrier(s_unit_group k S)") THEN SIMP_TAC [S_UNIT_GROUP, IN_ELIM_THM, (← ASSUME (← q r"number_field(k:A ring)"))], ALL_TAC] THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN CONJ_TAC THENL [EXISTS_TAC (← q r"group_element_order (s_unit_group k (S:(A->bool)->bool)) (z:A)") THEN CONJ_TAC THENL [MATCH_MP_TAC r4 THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"s_unit_group k (S:(A->bool)->bool)"), (← q r"z:A"), (← q r"group_element_order (s_unit_group k (S:(A->bool)->bool)) (z:A)")] GROUP_POW_EQ_ID) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN SIMP_TAC [S_UNIT_GROUP_POW, S_UNIT_GROUP, DIVIDES_REFL, (← ASSUME (← q r"number_field(k:A ring)"))], FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_eq z2))))) THEN SIMP_TAC [S_UNIT_GROUP, (← ASSUME (← q r"number_field(k:A ring)"))]]])

  -- @@RETURN BEGIN
  return { S_UNIT_GROUP_INDEPENDENT, S_UNIT_GROUP_FUNDAMENTAL }
  -- @@RETURN END

end HolANT.SunitRank
