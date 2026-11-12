/- ========================================================================= -/
/- ANT: The Dirichlet unit theorem for a number field k with ring of ...   -/
/- ========================================================================= -/
/- File: HolANT/UnitTheorem.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/unit_theorem.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antunittheoremdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/products.ml, Library/frag.ml, Library/grouptheory.ml, ANT/algmisc.ml, Library/permutations.ml, Library/ring_det.ml, ANT/ideal_arith.ml, Library/matroids.ml, Library/fieldtheory.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/discriminant.ml, Library/ring_groups.ml, ANT/fingen_group.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/nf_valuation.ml, ANT/prime_split.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/integrality.ml, Multivariate/misc.ml, Multivariate/metric.ml, Multivariate/homology.ml, Multivariate/vectors.ml, Multivariate/determinants.ml, Multivariate/topology.ml, Multivariate/convex.ml, Multivariate/paths.ml, Multivariate/polytope.ml, Multivariate/degree.ml, Multivariate/derivatives.ml, Multivariate/integration.ml, Multivariate/measure.ml, Multivariate/complex_algebra.ml, Multivariate/complexes.ml, Multivariate/canal.ml, Multivariate/transcendentals.ml, Multivariate/realanalysis.ml, Multivariate/moretop.ml, Multivariate/cauchy.ml, Multivariate/complex_ring.ml, Multivariate/complex_field.ml, ANT/complex_embeddings.ml, ANT/power_basis.ml, ANT/infinite_places.ml, ANT/linear_forms.ml, ANT/classgroup_group.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/quadratic.ml, ANT/minkowski_theory.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.UnitTheorem fills them).

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
import HolLibrary.Products
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolANT.Algmisc
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolANT.IdealArith
import HolLibrary.Matroids
import HolLibrary.FieldTheory
import HolANT.Integral
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolLibrary.Isum
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.Classgroup
import HolANT.Discriminant
import HolLibrary.RingGroups
import HolANT.FingenGroup
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.NfValuation
import HolANT.PrimeSplit
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
import HolANT.PowerBasis
import HolANT.InfinitePlaces
import HolANT.LinearForms
import HolANT.ClassgroupGroup
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.Quadratic
import HolANT.MinkowskiTheory

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Algmisc
open HolANT.IdealArith
open HolANT.Integral
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.Classgroup
open HolANT.Discriminant
open HolANT.FingenGroup
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.NfValuation
open HolANT.PrimeSplit
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.Integrality
open HolANT.ComplexEmbeddings
open HolANT.PowerBasis
open HolANT.InfinitePlaces
open HolANT.LinearForms
open HolANT.ClassgroupGroup
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.Quadratic
open HolANT.MinkowskiTheory

namespace HolANT.UnitTheorem

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ABELIAN_GROUP_DISCRETE_DEPENDENT ABELIAN_GROUP_SUM_INV ABELIAN_UNIT_GROUP
   ARITH_EQ CARD_CLAUSES CARD_DELETE CARD_EQ_0 COMPLEX_EMBEDDINGS_NONEMPTY
   COMPLEX_EMBEDDINGS_NORM_MUL COMPLEX_EMBEDDINGS_NORM_POS COMPLEX_NORM_MUL
   COMPLEX_RING_CLAUSES COND_ID CONJ_ASSOC CONTRAPOS_THM DIVIDES_REFL EQ_TRANS
   EXTENSION EXTENSIONAL FIELD_IMP_INTEGRAL_DOMAIN FIELD_NONTRIVIAL
   FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS FINITE_COMPLEX_EMBEDDINGS
   FINITE_DELETE FINITE_DIFF FINITE_IMAGE_INJ_EQ FINITE_INFINITE_PLACES
   FINITE_RESTRICT FINITE_SUBSET FORALL_IN_IMAGE FUN_EQ_THM GROUP_INV_ID
   GROUP_NPOW GROUP_POW GROUP_POW_EQ_ID GROUP_REAL_MULTIPLICATIVE_ID_INV_POW
   GROUP_REAL_MULTIPLICATIVE_SUM GROUP_SUM_CLAUSES_EXISTS GROUP_SUM_IMAGE
   GROUP_SUM_SING GROUP_SUM_SUPERSET GROUP_ZPOW GROUP_ZPOW_0 GROUP_ZPOW_NEG
   HAS_SIZE HAS_SIZE_0 HAS_SIZE_IMAGE_INJ IDEALS_GENERATED_SING_EQ
   IDEAL_NORM_CARRIER IMAGE_EQ_EMPTY IMP_CONJ INFINITE
   INTEGRAL_DOMAIN_ASSOCIATES INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING
   INTEGRAL_DOMAIN_RING_OF_INTEGERS INTEGRAL_DOMAIN_ROOTS_OF_UNITY_CYCLIC
   INT_LE_ANTISYM INT_LT_IMP_LE INT_LT_IMP_NE INT_NOT_LT INT_OF_NUM_EQ
   INT_OF_NUM_OF_INT IN_DELETE IN_DIFF IN_ELIM_THM IN_IDEAL_GENERATED_SELF
   IN_IMAGE IN_SING IN_UNIV ITER ITERATE_CASES LE_1 LE_ANTISYM LT_CASES
   MEMBER_NOT_EMPTY MONOIDAL_REAL_MUL MONO_AND MONO_EXISTS MONO_FORALL
   NORM_POS_LE NOT_EXISTS_THM NOT_FORALL_THM NOT_IMP NOT_IN_EMPTY : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (NPRODUCT_DELETE NPRODUCT_POS_LT NUMBER_FIELD_DISCRIMINANT_NONZERO
   NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM NUMBER_FIELD_IDEAL_MINKOWSKI
   NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_ROOTS_OF_UNITY_FINITE NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED
   NUM_OF_INT_OF_NUM PRODUCT_CONST PRODUCT_DELETE PRODUCT_EQ PRODUCT_EQ_0
   PRODUCT_LE PRODUCT_LE_1 PRODUCT_LT_1 PRODUCT_MUL PRODUCT_ONE PRODUCT_POS_LE
   PRODUCT_POS_LT REAL_ABS_NZ REAL_ARCH_SIMPLE REAL_DIV_RMUL REAL_HALF
   REAL_INV_LE_1 REAL_LE_DIV REAL_LE_INV_EQ REAL_LE_LMUL REAL_LE_MUL2
   REAL_LE_REFL REAL_LE_RMUL REAL_LE_TRANS REAL_LTE_TRANS REAL_LT_DIV
   REAL_LT_IMP_LE REAL_LT_IMP_NZ REAL_LT_LMUL_EQ REAL_MUL_AC REAL_MUL_RID
   REAL_MUL_RINV REAL_NOT_LE REAL_OF_INT_CLAUSES REAL_OF_NUM_EQ REAL_OF_NUM_LE
   REAL_POS REAL_POW_1 REAL_POW_1_LT REAL_POW_LE_1 REAL_POW_MONO REAL_POW_ROOT
   RIGHT_FORALL_IMP_THM RIGHT_IMP_EXISTS_THM RING_1 RING_HOMOMORPHISM_MUL
   RING_IDEAL_CARRIER RING_IDEAL_IDEAL_GENERATED RING_MUL_RID RING_OF_INTEGERS
   RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE RING_OF_INTEGERS_SUBSET
   RING_OF_INTEGERS_UNIT_NORM_PRODUCT RING_POW_MUL RING_POW_ONE RING_UNIT_0
   RING_UNIT_IN_CARRIER ROOT_POS_LT SING_SUBSET SKOLEM_THM SQRT_POS_LT SUBSET
   SUB_REFL TRANSITIVE_STEPWISE_LT UNIT_GROUP UNIT_GROUP_POW complex_embeddings
   group_pow group_zpow infinite_places lemma num_INFINITE o_DEF product : thm)
  deriving Inhabited

/-- What unit_theorem.ml uses from Session besides theorems. -/
structure UnitTheoremDeps where
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
/- unit_theorem.ml phrases from line 89 to 741                            -/
/- ---------------------------------------------------------------------- -/

structure UnitTheorem01 where
  -- @@FIELDS
  NUMBER_FIELD_UNIT_DOMINANT_PLACE : thm
  NUMBER_FIELD_UNITS_INDEPENDENT : thm
  NUMBER_FIELD_UNITS_DEPENDENT : thm
  NUMBER_FIELD_ROOTS_OF_UNITY_CYCLIC : thm
  NUMBER_FIELD_FUNDAMENTAL_UNITS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupUnitTheorem01 [HolBase] (D : UnitTheoremDeps) :
    ExceptT String IO UnitTheorem01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_INT_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC,
        INDUCT_TAC, INT_ARITH, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, SET_RULE,
        SET_TAC, TAUT, .. } := D
  let { ABELIAN_GROUP_DISCRETE_DEPENDENT, ABELIAN_GROUP_SUM_INV, ABELIAN_UNIT_GROUP,
        ARITH_EQ, CARD_DELETE, CARD_EQ_0, COMPLEX_EMBEDDINGS_NONEMPTY,
        COMPLEX_EMBEDDINGS_NORM_MUL, COMPLEX_EMBEDDINGS_NORM_POS, COMPLEX_NORM_MUL,
        COMPLEX_RING_CLAUSES, COND_ID, CONJ_ASSOC, CONTRAPOS_THM, DIVIDES_REFL,
        EXTENSION, EXTENSIONAL, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_NONTRIVIAL,
        FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS, FINITE_COMPLEX_EMBEDDINGS,
        FINITE_DELETE, FINITE_DIFF, FINITE_IMAGE_INJ_EQ, FINITE_INFINITE_PLACES,
        FINITE_RESTRICT, FINITE_SUBSET, FORALL_IN_IMAGE, FUN_EQ_THM, GROUP_INV_ID,
        GROUP_POW, GROUP_POW_EQ_ID, GROUP_REAL_MULTIPLICATIVE_ID_INV_POW,
        GROUP_REAL_MULTIPLICATIVE_SUM, GROUP_SUM_IMAGE, GROUP_ZPOW, GROUP_ZPOW_NEG,
        HAS_SIZE, HAS_SIZE_IMAGE_INJ, IDEALS_GENERATED_SING_EQ, IDEAL_NORM_CARRIER,
        IMP_CONJ, INFINITE, INTEGRAL_DOMAIN_ASSOCIATES,
        INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING, INTEGRAL_DOMAIN_RING_OF_INTEGERS,
        INTEGRAL_DOMAIN_ROOTS_OF_UNITY_CYCLIC, INT_LE_ANTISYM, INT_LT_IMP_LE,
        INT_LT_IMP_NE, INT_NOT_LT, INT_OF_NUM_EQ, INT_OF_NUM_OF_INT, IN_DELETE,
        IN_DIFF, IN_ELIM_THM, IN_IDEAL_GENERATED_SELF, IN_IMAGE, IN_SING, IN_UNIV,
        ITER, ITERATE_CASES, LE_1, LE_ANTISYM, LT_CASES, MEMBER_NOT_EMPTY,
        MONOIDAL_REAL_MUL, MONO_AND, MONO_EXISTS, MONO_FORALL, NORM_POS_LE,
        NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, .. } := D.core1
  let { NPRODUCT_DELETE, NPRODUCT_POS_LT, NUMBER_FIELD_DISCRIMINANT_NONZERO,
        NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM, NUMBER_FIELD_IDEAL_MINKOWSKI,
        NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_ROOTS_OF_UNITY_FINITE, NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED,
        NUM_OF_INT_OF_NUM, PRODUCT_CONST, PRODUCT_DELETE, PRODUCT_EQ, PRODUCT_EQ_0,
        PRODUCT_LE, PRODUCT_LE_1, PRODUCT_LT_1, PRODUCT_MUL, PRODUCT_ONE,
        PRODUCT_POS_LE, PRODUCT_POS_LT, REAL_ABS_NZ, REAL_ARCH_SIMPLE, REAL_DIV_RMUL,
        REAL_HALF, REAL_INV_LE_1, REAL_LE_DIV, REAL_LE_INV_EQ, REAL_LE_LMUL,
        REAL_LE_MUL2, REAL_LE_REFL, REAL_LE_RMUL, REAL_LE_TRANS, REAL_LTE_TRANS,
        REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_LMUL_EQ, REAL_MUL_AC,
        REAL_MUL_RID, REAL_MUL_RINV, REAL_NOT_LE, REAL_OF_INT_CLAUSES, REAL_OF_NUM_EQ,
        REAL_OF_NUM_LE, REAL_POS, REAL_POW_1, REAL_POW_1_LT, REAL_POW_LE_1,
        REAL_POW_MONO, REAL_POW_ROOT, RIGHT_FORALL_IMP_THM, RIGHT_IMP_EXISTS_THM,
        RING_1, RING_HOMOMORPHISM_MUL, RING_IDEAL_CARRIER, RING_IDEAL_IDEAL_GENERATED,
        RING_OF_INTEGERS, RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE,
        RING_OF_INTEGERS_SUBSET, RING_OF_INTEGERS_UNIT_NORM_PRODUCT, RING_POW_MUL,
        RING_POW_ONE, RING_UNIT_0, RING_UNIT_IN_CARRIER, ROOT_POS_LT, SKOLEM_THM,
        SQRT_POS_LT, SUBSET, TRANSITIVE_STEPWISE_LT, UNIT_GROUP, UNIT_GROUP_POW,
        complex_embeddings, group_pow, group_zpow, infinite_places, num_INFINITE,
        o_DEF, product, .. } := D.core2
  -- @@SCOPE END

  let NUMBER_FIELD_UNIT_DOMINANT_PLACE ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"h:A->complex"
    let q2 ← q r"h:A->complex"
    let q3 ← q r"b:A"
    let q4 ← q r"g:A->complex"
    let q5 ← q r"h:A->complex"
    let q6 ← q r"(h:A->complex) IN s <=> g IN s"
    let q7 ← q r"h:A->complex"
    let q8 ← q r"g:A->complex"
    let q9 ← q r"\h:A->complex. if h IN s then root (CARD(s:(A->complex)->bool)) (D / p)
                     else norm(h(a:A)) / &2"
    let q10 ← q r"ring_carrier(ring_of_integers k):A->bool"
    let q11 ← q r"k:A ring"
    let v12 ← ISPECL [q11, q10, q9] NUMBER_FIELD_IDEAL_MINKOWSKI
    let q13 ← q r"!s t:(A->complex)->bool.
                    {x | x IN t /\ ~(x IN s)} = t DIFF s"
    let r14 ← SET_RULE q13
    let q15 ← q r"!s t:(A->complex)->bool.
                     s SUBSET t ==> {x | x IN t /\ x IN s} = s"
    let r16 ← SET_RULE q15
    let v17 ← GSYM product
    let v18 ← MATCH_MP ITERATE_CASES MONOIDAL_REAL_MUL
    let q19 ← q r"product (complex_embeddings k)
        (\h:A->complex. if h IN s then root (CARD s) (D / p)
                        else norm(h(a:A)) / &2) = D"
    let v20 ← GSYM REAL_ABS_NZ
    let q21 ← q r"&0:real < D /\ &0:real < p"
    let q22 ← q r"p = product (complex_embeddings k DIFF s)
                            (\h:A->complex. norm(h(a:A)) / &2)"
    let q23 ← q r"D = sqrt(abs(real_of_int(number_field_discriminant(k:A ring))))"
    let q24 ← q r"!h:A->complex. h IN complex_embeddings k ==> &0 < norm(h a)"
    let q25 ← q r"FINITE(complex_embeddings(k:A ring)) /\
                  FINITE(s:(A->complex)->bool) /\ (a:A) IN ring_carrier k"
    let q26 ← q r"a:A"
    let p27 ← prove r"!k s.
        number_field k /\ s SUBSET complex_embeddings k /\ ~(s = {}) /\
        (!g h. g IN s /\ h IN complex_embeddings k /\
               (!x. x IN ring_carrier k ==> norm(h x) = norm(g x))
               ==> h IN s)
        ==> !a:A. a IN ring_carrier(ring_of_integers k) /\ ~(a = ring_0 k)
                  ==> ?b. (b IN ring_carrier(ring_of_integers k) /\
                           ~(b = ring_0 k)) /\
                          (!h. h IN complex_embeddings k DIFF s
                               ==> norm(h b) <= norm(h a) / &2) /\
                          product (complex_embeddings k) (\h. norm(h b)) <=
                          sqrt(abs(real_of_int(number_field_discriminant k)))" (REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC q26 THEN STRIP_TAC THEN SUBGOAL_THEN q25 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [FINITE_COMPLEX_EMBEDDINGS, FINITE_SUBSET, RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN q24 ASSUME_TAC THENL [ASM_SIMP_TAC [COMPLEX_EMBEDDINGS_NORM_POS, NUMBER_FIELD_IMP_FIELD], ALL_TAC] THEN ABBREV_TAC q23 THEN ABBREV_TAC q22 THEN SUBGOAL_THEN q21 STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["D", "p"] THEN CONJ_TAC THENL [ASM_SIMP_TAC [SQRT_POS_LT, v20, REAL_OF_INT_CLAUSES, NUMBER_FIELD_DISCRIMINANT_NONZERO], MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_SIMP_TAC [FINITE_DIFF, IN_DIFF, REAL_HALF]], ALL_TAC] THEN SUBGOAL_THEN q19 ASSUME_TAC THENL [ASM_SIMP_TAC [product, v18] THEN REWRITE_TAC [v17] THEN ASM_SIMP_TAC [r16] THEN REWRITE_TAC [r14] THEN ASM_SIMP_TAC [PRODUCT_CONST, REAL_POW_ROOT, CARD_EQ_0, REAL_LE_DIV, REAL_LT_IMP_LE, REAL_DIV_RMUL, REAL_LT_IMP_NZ], ALL_TAC] THEN MP_TAC v12 THEN ASM_REWRITE_TAC [RING_IDEAL_CARRIER, IDEAL_NORM_CARRIER, REAL_MUL_RID, REAL_LE_REFL] THEN ANTS_TAC THENL [REPEAT CONJ_TAC THENL [ASM SET_TAC [], GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [ROOT_POS_LT, REAL_LT_DIV, REAL_HALF], MAP_EVERY X_GEN_TAC [q8, q7] THEN STRIP_TAC THEN SUBGOAL_THEN q6 SUBST1_TAC THENL [EQ_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL [EXISTS_TAC q5, EXISTS_TAC q4] THEN ASM_SIMP_TAC [], ASM_SIMP_TAC []]], MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q3 THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [X_GEN_TAC q2 THEN REWRITE_TAC [IN_DIFF] THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC q1)) THEN ASM_REWRITE_TAC [], FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) THEN MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC [NORM_POS_LE]]])
    let lemma := p27
    let v28 ← GSYM REAL_MUL_RID
    let q32 ← q r"n:num"
    let q33 ← q r"m:num"
    let q34 ← q r"h:A->complex"
    let q35 ← q r"(a:num->A) m IN ring_carrier k /\ u IN ring_carrier k"
    let q36 ← q r"h:A->complex"
    let q37 ← q r"u:A"
    let q38 ← q r"(a:num->A) m"
    let q39 ← q r"(a:num->A) n"
    let q40 ← q r"ring_of_integers k:A ring"
    let v41 ← ISPECL [q40, q39, q38] IDEALS_GENERATED_SING_EQ
    let v42 ← GSYM REAL_OF_NUM_LE
    let q43 ← q r"(a:num->A) m"
    let q44 ← q r"m:num"
    let v45 ← REWRITE_RULE [IMP_CONJ] FINITE_SUBSET
    let v46 ← GSYM INFINITE
    let q47 ← q r"~r /\ q /\ (~p ==> s) ==> (p ==> (q <=> r)) ==> s"
    let r48 ← TAUT q47
    let q49 ← q r"(:num)"
    let q50 ← q r"\m. ideal_generated (ring_of_integers k) {(a:num->A) m}"
    let v51 ← ISPECL [q50, q49] FINITE_IMAGE_INJ_EQ
    let q52 ← q r"c:num"
    let q53 ← q r"sqrt(abs(real_of_int(number_field_discriminant(k:A ring))))"
    let v54 ← SPEC q53 REAL_ARCH_SIMPLE
    let q55 ← q r"c:num"
    let q56 ← q r"?m n. m < n /\
            ideal_generated (ring_of_integers k) {(a:num->A) n} =
            ideal_generated (ring_of_integers k) {a m}"
    let v57 ← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET
    let q58 ← q r"&0 < y /\ x <= y / &2 ==> x < y"
    let r59 ← REAL_ARITH q58
    let q60 ← q r"m:num"
    let q61 ← q r"h:A->complex"
    let q62 ← q r"p /\ (p ==> q) ==> p /\ q"
    let r63 ← TAUT q62
    let q64 ← q r"\m. ITER m (f:A->A) (f(ring_1 k))"
    let q65 ← q r"ring_of_integers k:A ring"
    let v66 ← ISPEC q65 RING_1
    let q67 ← q r"ring_1 k IN ring_carrier(ring_of_integers k) /\
                    ~(ring_1 k:A = ring_0 k)"
    let q68 ← q r"f:A->A"
    let v69 ← GSYM MEMBER_NOT_EMPTY
    let q70 ← q r"{h | h IN complex_embeddings k /\
              !x. x IN ring_carrier k ==> norm(h x) = norm((g:A->complex) x)}"
    let q71 ← q r"k:A ring"
    let v72 ← ISPECL [q71, q70] lemma
    let q73 ← q r"?a:num->A.
        (!m. (a m IN ring_carrier(ring_of_integers k) /\ ~(a m = ring_0 k)) /\
             product (complex_embeddings k) (\h. norm(h(a m))) <=
             sqrt(abs(real_of_int(number_field_discriminant k)))) /\
        (!h. h IN complex_embeddings k /\
             ~(!x. x IN ring_carrier k ==> norm(h x) = norm((g:A->complex) x))
             ==> !m n. m < n ==> norm(h(a n)) < norm(h(a m)))"
    prove
      r"!k (g:A->complex).
          number_field k /\ g IN complex_embeddings k
          ==> ?u. ring_unit (ring_of_integers k) u /\
                  !h. h IN complex_embeddings k /\
                      ~(!x. x IN ring_carrier k ==> norm(h x) = norm(g x))
                      ==> norm(h u) < &1"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN q73 STRIP_ASSUME_TAC THENL [MP_TAC v72 THEN ANTS_TAC THENL [REWRITE_TAC [SUBSET, IN_ELIM_THM, v69] THEN ASM_MESON_TAC [], REWRITE_TAC [IN_DIFF, IN_ELIM_THM]] THEN DISCH_THEN ((X_CHOOSE_TAC q68) o ((REWRITE_RULE [SKOLEM_THM]) o (GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]))) THEN SUBGOAL_THEN q67 STRIP_ASSUME_TAC THENL [MP_TAC v66 THEN ASM_SIMP_TAC [RING_OF_INTEGERS, FIELD_NONTRIVIAL], ALL_TAC] THEN EXISTS_TAC q64 THEN BETA_TAC THEN MATCH_MP_TAC r63 THEN CONJ_TAC THENL [INDUCT_TAC THEN ASM_SIMP_TAC [ITER], DISCH_TAC THEN X_GEN_TAC q61 THEN STRIP_TAC THEN MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN CONJ_TAC THENL [REAL_ARITH_TAC, X_GEN_TAC q60] THEN REWRITE_TAC [ITER] THEN MATCH_MP_TAC r59 THEN ASM_SIMP_TAC [COMPLEX_EMBEDDINGS_NORM_POS, v57]], ALL_TAC] THEN SUBGOAL_THEN q56 STRIP_ASSUME_TAC THENL [X_CHOOSE_TAC q55 v54 THEN FIRST_ASSUM (ASSUME_TAC o ((SPEC q52) o (MATCH_MP NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM))) THEN MP_TAC v51 THEN MATCH_MP_TAC r48 THEN REWRITE_TAC [v46, num_INFINITE] THEN CONJ_TAC THENL [FIRST_X_ASSUM (MATCH_MP_TAC o (MATCH_MP v45)) THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_UNIV, IN_ELIM_THM] THEN X_GEN_TAC q44 THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN CONJ_TAC THENL [REWRITE_TAC [EXTENSION, IN_SING] THEN DISCH_THEN (MP_TAC o (SPEC q43)) THEN ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF], REWRITE_TAC [v42] THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS] THEN ASM_MESON_TAC [REAL_LE_TRANS]], REWRITE_TAC [IN_UNIV, NOT_FORALL_THM, NOT_IMP] THEN MESON_TAC [LT_CASES]], ALL_TAC] THEN MP_TAC v41 THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_ASSOCIATES, INTEGRAL_DOMAIN_RING_OF_INTEGERS] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q37 THEN REWRITE_TAC [RING_OF_INTEGERS] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC q36 THEN STRIP_TAC THEN SUBGOAL_THEN q35 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_UNIT_IN_CARRIER, RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC q34)) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (SPECL [q33, q32])) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun z29 => (do let z30 ← (do let z31 ← (pure z29); pure (concl z31)); pure (is_eq z30)))))) THEN ASM_SIMP_TAC [COMPLEX_EMBEDDINGS_NORM_MUL] THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [v28] THEN ASM_SIMP_TAC [REAL_LT_LMUL_EQ, COMPLEX_EMBEDDINGS_NORM_POS])

  let NUMBER_FIELD_UNITS_INDEPENDENT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"\v:A->real. --((n:(A->real)->int) v)"
    let q2 ← q r"&0:int <= x <=> --x <= &0"
    let r3 ← INT_ARITH q2
    let v4 ← GSYM INT_LE_ANTISYM
    let q5 ← q r"v:A->real"
    let q6 ← q r"n:(A->real)->int"
    let q7 ← q r"v:A->real"
    let q8 ← q r"w:A->real"
    let q9 ← q r"x:real < &1 ==> ~(&1 = x)"
    let r10 ← REAL_ARITH q9
    let q11 ← q r"t:(A->real)->bool"
    let q12 ← q r"\v:A->real. group_zpow G ((u:(A->real)->A) v) (n v)"
    let q13 ← q r"beta:A->real"
    let q14 ← q r"G:A group"
    let v15 ← ISPECL [q14, q13, q12, q11] GROUP_REAL_MULTIPLICATIVE_SUM
    let q16 ← q r"(n:(A->real)->int) v = &0"
    let v17 ← GSYM INT_OF_NUM_EQ
    let q18 ← q r"x:real < &1 ==> x <= &1 /\ x < &1"
    let r19 ← REAL_ARITH q18
    let q20 ← q r"&0:int < n(v:A->real)"
    let q21 ← q r"v:A->real"
    let q22 ← q r"!v. v IN t
            ==> (beta:A->real)(group_zpow G ((u:(A->real)->A) v) (n v)) <= &1 /\
                (&0 < n v ==> beta(group_zpow G (u v) (n v)) < &1)"
    let q23 ← q r"&0 < (n:(A->real)->int)((f:K->A->real) i)"
    let q24 ← q r"i:K"
    let q25 ← q r"a:real * b <= &1 * b ==> &1 = a * b ==> &1 <= b"
    let r26 ← REAL_ARITH q25
    let v27 ← GSYM product
    let v28 ← MATCH_MP ITERATE_CASES MONOIDAL_REAL_MUL
    let q29 ← q r"\i. (f:K->A->real) i ((u:(A->real)->A) v)"
    let q30 ← q r"\i. (f:K->A->real) i ((u:(A->real)->A) v)"
    let q31 ← q r"\i. (f:K->A->real) i IN t /\ &0 < (n:(A->real)->int)(f i)"
    let q32 ← q r"s:K->bool"
    let v33 ← ISPECL [q32, q31, q30, q29] v28
    let q34 ← q r"!x. x IN group_carrier G
              ==> product s (\i. (f:K->A->real) i x) = &1"
    let v35 ← ASSUME q34
    let q36 ← q r"(u:(A->real)->A) v"
    let v37 ← SPEC q36 v35
    let q38 ← q r"!v. v IN t /\ ~(&0 < (n:(A->real)->int) v)
            ==> &1 <= (beta:A->real)((u:(A->real)->A) v)"
    let q42 ← q r"i:K"
    let q43 ← q r"j:K"
    let q44 ← q r"!v. v IN t /\ &0 < (n:(A->real)->int) v
            ==> (beta:A->real)((u:(A->real)->A) v) < &1"
    let q45 ← q r"beta:A->real"
    let q46 ← q r"G:A group"
    let v47 ← ISPECL [q46, q45] GROUP_REAL_MULTIPLICATIVE_ID_INV_POW
    let q48 ← q r"FINITE(s:K->bool)"
    let v49 ← ASSUME q48
    let v50 ← GSYM PRODUCT_MUL
    let q51 ← q r"(!x. x IN group_carrier G ==> &0 < (beta:A->real) x) /\
        (!x y. x IN group_carrier G /\ y IN group_carrier G
               ==> beta(group_mul G x y) = beta x * beta y)"
    let q52 ← q r"beta = \x:A. product {i:K | i IN s /\
                           ~(f i IN t /\ &0 < (n:(A->real)->int)(f i))}
                           (\i. f i x)"
    let v53 ← GSYM INT_NOT_LT
    let q54 ← q r"w:A->real"
    let q55 ← q r"n:(A->real)->int"
    let q56 ← q r"!n. group_sum G t (\v. group_zpow G ((u:(A->real)->A) v) (n v)) =
          group_id G
          ==> !v. v IN t ==> n v <= &0"
    let p57 ← prove r"!G (f:K->A->real) s t (u:(A->real)->A).
        abelian_group G /\ FINITE s /\ FINITE t /\
        (!i x. i IN s /\ x IN group_carrier G ==> &0 < f i x) /\
        (!i x y. i IN s /\ x IN group_carrier G /\ y IN group_carrier G
                 ==> f i (group_mul G x y) = f i x * f i y) /\
        (!x. x IN group_carrier G ==> product s (\i. f i x) = &1) /\
        (?j. j IN s /\ ~(f j IN t)) /\
        (!v. v IN t ==> u v IN group_carrier G) /\
        (!i v. i IN s /\ v IN t /\ ~(f i = v) ==> f i (u v) < &1)
        ==> !n. group_sum G t (\v. group_zpow G (u v) (n v)) = group_id G
                ==> !v. v IN t ==> n v = &0" (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN q56 ASSUME_TAC THENL [X_GEN_TAC q55 THEN DISCH_TAC THEN X_GEN_TAC q54 THEN REWRITE_TAC [v53] THEN REPEAT STRIP_TAC THEN ABBREV_TAC q52 THEN SUBGOAL_THEN q51 STRIP_ASSUME_TAC THENL [EXPAND_TAC "beta" THEN SIMP_TAC [v50, FINITE_RESTRICT, v49] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL [MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_SIMP_TAC [FINITE_RESTRICT, IN_ELIM_THM], MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM]], ALL_TAC] THEN MP_TAC v47 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN q44 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN EXPAND_TAC "beta" THEN MATCH_MP_TAC PRODUCT_LT_1 THEN EXISTS_TAC q43 THEN ASM_SIMP_TAC [FINITE_RESTRICT, IN_ELIM_THM] THEN CONJ_TAC THENL [X_GEN_TAC q42 THEN STRIP_TAC THEN ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LT_IMP_LE, ALL_TAC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun z39 => (do let z40 ← (do let z41 ← (pure z39); pure (concl z41)); pure (is_neg z40))))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q38 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN EXPAND_TAC "beta" THEN MP_TAC v37 THEN ANTS_TAC THENL [ASM_SIMP_TAC [], DISCH_TAC] THEN MP_TAC v33 THEN ASM_REWRITE_TAC [COND_ID, v27] THEN MATCH_MP_TAC r26 THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [MATCH_MP_TAC PRODUCT_LE_1, MATCH_MP_TAC PRODUCT_POS_LE] THEN ASM_SIMP_TAC [FINITE_RESTRICT, IN_ELIM_THM, REAL_LT_IMP_LE] THEN X_GEN_TAC q24 THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN UNDISCH_TAC q23 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q22 ASSUME_TAC THENL [X_GEN_TAC q21 THEN DISCH_TAC THEN REWRITE_TAC [group_zpow] THEN ASM_CASES_TAC q20 THEN ASM_SIMP_TAC [INT_LT_IMP_LE, GROUP_POW] THENL [MATCH_MP_TAC r19 THEN MATCH_MP_TAC REAL_POW_1_LT THEN ASM_SIMP_TAC [REAL_LT_IMP_LE, v17, INT_OF_NUM_OF_INT, INT_LT_IMP_LE, INT_LT_IMP_NE], COND_CASES_TAC THENL [SUBGOAL_THEN q16 SUBST1_TAC THENL [ASM_INT_ARITH_TAC, ASM_REWRITE_TAC [NUM_OF_INT_OF_NUM, group_pow]] THEN REAL_ARITH_TAC, ASM_SIMP_TAC [GROUP_POW] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_SIMP_TAC []]], ALL_TAC] THEN MP_TAC v15 THEN ASM_SIMP_TAC [GROUP_ZPOW] THEN MATCH_MP_TAC r10 THEN MATCH_MP_TAC PRODUCT_LT_1 THEN EXISTS_TAC q8 THEN ASM_SIMP_TAC [] THEN X_GEN_TAC q7 THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [GROUP_ZPOW], ALL_TAC] THEN X_GEN_TAC q6 THEN DISCH_TAC THEN X_GEN_TAC q5 THEN DISCH_TAC THEN REWRITE_TAC [v4] THEN CONJ_TAC THENL [ASM_MESON_TAC [], ONCE_REWRITE_TAC [r3] THEN FIRST_X_ASSUM (MP_TAC o (SPEC q1)) THEN ASM_SIMP_TAC [GROUP_ZPOW_NEG, ABELIAN_GROUP_SUM_INV, GROUP_ZPOW, FINITE_RESTRICT, GROUP_INV_ID]])
    let lemma := p57
    let q58 ← q r"\v. (n:A->int)((u:(A->real)->A) v)"
    let q59 ← q r"n:A->int"
    let q60 ← q r"IMAGE (u:(A->real)->A)
            (infinite_places k DELETE (\x. norm((g:A->complex) x)))"
    let q61 ← q r"g:A->complex"
    let q62 ← q r"x:real < &1 ==> x = &1 ==> F"
    let r63 ← REAL_ARITH q62
    let q64 ← q r"(u:(A->real)->A) w"
    let q65 ← q r"k:A ring"
    let v66 ← ISPECL [q65, q64] RING_OF_INTEGERS_UNIT_NORM_PRODUCT
    let q67 ← q r"product (complex_embeddings k)
          (\h. norm((h:A->complex)((u:(A->real)->A) w))) = &1"
    let q68 ← q r"~(v:A->real = w)"
    let q69 ← q r"h:A->complex"
    let q70 ← q r"!h. h IN complex_embeddings k
            ==> norm((h:A->complex)((u:(A->real)->A) w)) < &1"
    let q71 ← q r"(~p ==> F) ==> p"
    let r72 ← TAUT q71
    let q73 ← q r"!v w. v IN infinite_places k DELETE (\x. norm((g:A->complex) x)) /\
            w IN infinite_places k DELETE (\x. norm(g x)) /\
            (u:(A->real)->A) v = u w ==> v = w"
    let q74 ← q r"g:A->complex"
    let q75 ← q r"x:A"
    let q76 ← q r"k:A ring"
    let v77 ← ISPECL [q76, q75] RING_OF_INTEGERS_UNIT_NORM_PRODUCT
    let q78 ← q r"x:A"
    let q79 ← q r"u:(A->real)->A"
    let q80 ← q r"infinite_places k DELETE (\x:A. norm((g:A->complex) x))"
    let q81 ← q r"complex_embeddings(k:A ring)"
    let q82 ← q r"\h:A->complex x:A. norm(h x)"
    let q83 ← q r"unit_group(ring_of_integers k):A group"
    let v84 ← ISPECL [q83, q82, q81, q80, q79] lemma
    let q85 ← q r"!n. group_sum (unit_group(ring_of_integers k))
            (infinite_places k DELETE (\x. norm((g:A->complex) x)))
            (\v. group_zpow (unit_group(ring_of_integers k))
                            ((u:(A->real)->A) v) (n v)) = ring_1 k
          ==> !v. v IN infinite_places k DELETE (\x. norm(g x)) ==> n v = &0"
    let q86 ← q r"infinite_places k DELETE (\x:A. norm((g:A->complex) x)) HAS_SIZE
      CARD(infinite_places k) - 1"
    let q87 ← q r"g:A->complex"
    let q88 ← q r"FINITE(complex_embeddings(k:A ring)) /\ FINITE(infinite_places k) /\
      (\x:A. norm((g:A->complex) x)) IN infinite_places k"
    let q89 ← q r"g:A->complex"
    let v90 ← GSYM MEMBER_NOT_EMPTY
    let v91 ← CONJUNCT1 RING_OF_INTEGERS
    let v92 ← GSYM v91
    let q93 ← q r"ring_unit (ring_of_integers k) (x:A)"
    let q94 ← q r"x:A"
    let q95 ← q r"!x. ring_unit (ring_of_integers k) x
          ==> (x:A) IN ring_carrier k /\ ~(x = ring_0 k)"
    let q96 ← q r"u:(A->real)->A"
    let q97 ← q r"(x:A) IN ring_carrier k"
    let q98 ← q r"x:A"
    let q99 ← q r"~((\x:A. norm((h:A->complex) x)) = (\x. norm((g:A->complex) x)))"
    let q100 ← q r"(q ==> p) ==> (p ==> r) ==> (q ==> r)"
    let r101 ← TAUT q100
    let q102 ← q r"h:A->complex"
    let q103 ← q r"u:A"
    let q104 ← q r"g:A->complex"
    let q105 ← q r"k:A ring"
    let v106 ← ISPECL [q105, q104] NUMBER_FIELD_UNIT_DOMINANT_PLACE
    let q107 ← q r"g:A->complex"
    let q108 ← q r"!v. v IN infinite_places k
          ==> ?u. ring_unit (ring_of_integers k) u /\
                  !h. h IN complex_embeddings k /\ ~((\x. norm(h x)) = v)
                      ==> norm((h:A->complex) u) < &1"
    prove
      r"!k:A ring.
          number_field k
          ==> ?t. t HAS_SIZE (CARD(infinite_places k) - 1) /\
                  (!u. u IN t ==> ring_unit (ring_of_integers k) u) /\
                  !n. group_sum (unit_group(ring_of_integers k)) t
                        (\u. group_zpow (unit_group(ring_of_integers k)) u
                                        (n u)) =
                      ring_1 k
                      ==> !u. u IN t ==> n u = &0"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN q108 MP_TAC THENL [REWRITE_TAC [infinite_places, FORALL_IN_IMAGE] THEN X_GEN_TAC q107 THEN DISCH_TAC THEN MP_TAC v106 THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q103 THEN MATCH_MP_TAC MONO_AND THEN REWRITE_TAC [] THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC q102 THEN MATCH_MP_TAC r101 THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC q99 THEN REWRITE_TAC [CONTRAPOS_THM, FUN_EQ_THM] THEN DISCH_TAC THEN X_GEN_TAC q98 THEN ASM_CASES_TAC q97 THEN ASM_SIMP_TAC [] THEN RULE_ASSUM_TAC (REWRITE_RULE [complex_embeddings, EXTENSIONAL, IN_ELIM_THM]) THEN ASM_SIMP_TAC [], DISCH_THEN ((X_CHOOSE_TAC q96) o ((REWRITE_RULE [SKOLEM_THM]) o (GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM])))] THEN SUBGOAL_THEN q95 ASSUME_TAC THENL [X_GEN_TAC q94 THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_UNIT_IN_CARRIER)) THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], DISCH_TAC] THEN UNDISCH_TAC q93 THEN ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [v92] THEN ASM_SIMP_TAC [RING_UNIT_0, INTEGRAL_DOMAIN_RING_OF_INTEGERS, INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY)) THEN REWRITE_TAC [v90] THEN DISCH_THEN (X_CHOOSE_TAC q89) THEN SUBGOAL_THEN q88 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [FINITE_COMPLEX_EMBEDDINGS, FINITE_INFINITE_PLACES] THEN REWRITE_TAC [infinite_places, IN_IMAGE] THEN EXISTS_TAC q87 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q86 ASSUME_TAC THENL [ASM_SIMP_TAC [HAS_SIZE, FINITE_DELETE, CARD_DELETE], ALL_TAC] THEN SUBGOAL_THEN q85 ASSUME_TAC THENL [MP_TAC v84 THEN REWRITE_TAC [UNIT_GROUP, IN_ELIM_THM, RING_OF_INTEGERS, ABELIAN_UNIT_GROUP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [FINITE_DELETE, COMPLEX_EMBEDDINGS_NORM_POS, COMPLEX_EMBEDDINGS_NORM_MUL, IN_DELETE] THEN CONJ_TAC THENL [X_GEN_TAC q78 THEN DISCH_TAC THEN MP_TAC v77 THEN ASM_SIMP_TAC [], EXISTS_TAC q74 THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN q73 (fun th => tactic_of do pure (MP_TAC (← MATCH_MP HAS_SIZE_IMAGE_INJ (← CONJ th (← ASSUME (← q r"infinite_places k DELETE (\x:A. norm((g:A->complex) x))
                   HAS_SIZE CARD(infinite_places k) - 1")))) THEN MP_TAC (← MATCH_MP GROUP_SUM_IMAGE (← CONJ (← ISPEC (← q r"ring_of_integers k:A ring") ABELIAN_UNIT_GROUP) th)))) THENL [REWRITE_TAC [IN_DELETE] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC r72 THEN DISCH_TAC THEN SUBGOAL_THEN q70 ASSUME_TAC THENL [X_GEN_TAC q69 THEN DISCH_TAC THEN FIRST_X_ASSUM (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"h:A->complex") (← CONJUNCT2 (← MATCH_MP th (← ASSUME (← q r"(v:A->real) IN infinite_places k"))))) THEN MP_TAC (← SPEC (← q r"h:A->complex") (← CONJUNCT2 (← MATCH_MP th (← ASSUME (← q r"(w:A->real) IN infinite_places k"))))))) THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC q68 THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN q67 MP_TAC THENL [MP_TAC v66 THEN ASM_SIMP_TAC [], ALL_TAC] THEN MATCH_MP_TAC r63 THEN MATCH_MP_TAC PRODUCT_LT_1 THEN EXISTS_TAC q61 THEN ASM_SIMP_TAC [NORM_POS_LE, REAL_LT_IMP_LE], ALL_TAC] THEN DISCH_TAC THEN DISCH_TAC THEN EXISTS_TAC q60 THEN ASM_SIMP_TAC [FORALL_IN_IMAGE, IN_DELETE, o_DEF] THEN X_GEN_TAC q59 THEN FIRST_X_ASSUM (MP_TAC o (SPEC q58)) THEN REWRITE_TAC [IN_DELETE])

  let NUMBER_FIELD_UNITS_DEPENDENT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"a * c * p:real = c * (a * p)"
    let v2 ← GSYM REAL_MUL_RID
    let q3 ← q r"a * c * p:real"
    let p4 ← prove r"!a c p. &0 <= a:real /\ a * p = &1 /\ &1 <= c * p ==> a <= c" (REPEAT STRIP_TAC THEN TRANS_TAC REAL_LE_TRANS q3 THEN CONJ_TAC THENL [GEN_REWRITE_TAC LAND_CONV [v2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [], SUBGOAL_THEN q1 SUBST1_TAC THENL [REWRITE_TAC [REAL_MUL_AC], ASM_REWRITE_TAC [REAL_MUL_RID, REAL_LE_REFL]]])
    let lemma := p4
    let q5 ← q r"product (complex_embeddings k DELETE g) (\h:A->complex. &1) <=
      product (complex_embeddings k DELETE g) (\h. B * norm(h(x:A)))"
    let q6 ← q r"product (complex_embeddings k DELETE g)
                        (\h:A->complex. norm(h(x:A)))"
    let q7 ← q r"g:A->complex"
    let q8 ← q r"complex_embeddings(k:A ring)"
    let q9 ← q r"\h:A->complex. norm(h(x:A))"
    let v10 ← ISPECL [q9, q8, q7] PRODUCT_DELETE
    let q11 ← q r"x:A"
    let q12 ← q r"k:A ring"
    let v13 ← ISPECL [q12, q11] RING_OF_INTEGERS_UNIT_NORM_PRODUCT
    let p14 ← prove r"!k (g:A->complex) x B.
        number_field k /\ ring_unit (ring_of_integers k) x /\
        g IN complex_embeddings k /\
        (!h. h IN complex_embeddings k /\ ~(h = g) ==> &1 <= B * norm(h x))
        ==> norm(g x) <= B pow (CARD(complex_embeddings k) - 1)" (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_COMPLEX_EMBEDDINGS)) THEN MP_TAC v13 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC v10 THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MATCH_MP_TAC lemma THEN EXISTS_TAC q6 THEN ASM_REWRITE_TAC [NORM_POS_LE] THEN SUBGOAL_THEN q5 MP_TAC THENL [MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC [FINITE_DELETE, IN_DELETE, REAL_POS], ASM_SIMP_TAC [PRODUCT_ONE, PRODUCT_MUL, FINITE_DELETE, PRODUCT_CONST, CARD_DELETE]])
    let bound := p14
    let q15 ← q r"b * inv b:real"
    let q16 ← q r"norm((h:A->complex) x)"
    let q17 ← q r"&0:real < b"
    let q18 ← q r"h:A->complex"
    let q19 ← q r"&1:real * &1"
    let q20 ← q r"norm((h:A->complex) x) = norm((g:A->complex) x)"
    let q21 ← q r"(\x:A. norm((h:A->complex) x)) = (\x. norm((g0:A->complex) x))"
    let q22 ← q r"h:A->complex"
    let q23 ← q r"&1:real <= max (&1) b"
    let r24 ← REAL_ARITH q23
    let q25 ← q r"max (&1:real) b pow (CARD(complex_embeddings(k:A ring)) - 1)"
    let q26 ← q r"&1:real <= max (&1) b"
    let r27 ← REAL_ARITH q26
    let q28 ← q r"&1:real"
    let q29 ← q r"norm((g:A->complex) x) <= &1"
    let q30 ← q r"g:A->complex"
    let q31 ← q r"&1:real <= max (&1) b"
    let r32 ← REAL_ARITH q31
    let q33 ← q r"max (&1:real) b pow 1"
    let q34 ← q r"(\x:A. norm((g:A->complex) x)) = (\x. norm((g0:A->complex) x))"
    let q35 ← q r"1 <= CARD(complex_embeddings(k:A ring))"
    let q36 ← q r"g:A->complex"
    let q37 ← q r"x:A"
    let q38 ← q r"{x | x IN ring_carrier(ring_of_integers k) /\
           !g. g IN complex_embeddings k
               ==> norm((g:A->complex) x) <=
                   max (&1) b pow CARD(complex_embeddings k)}"
    let q39 ← q r"b:real"
    let v40 ← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET
    let q41 ← q r"y:A"
    let q42 ← q r"x:A"
    let q43 ← q r"g:A->complex"
    let q44 ← q r"complex_ring"
    let q45 ← q r"k:A ring"
    let v46 ← ISPECL [q45, q44, q43] RING_HOMOMORPHISM_MUL
    let q47 ← q r"y:A"
    let q48 ← q r"x:A"
    let q49 ← q r"g:A->complex"
    let q50 ← q r"~(p = 0) /\ p <= t ==> p - 1 < t"
    let r51 ← ARITH_RULE q50
    let q52 ← q r"d /\ a /\ b /\ c ==> a /\ b /\ c /\ d"
    let r53 ← TAUT q52
    let q54 ← q r"t:A->bool"
    let q55 ← q r"\(v:A->real) (x:A). v x"
    let q56 ← q r"infinite_places k DELETE (\x:A. norm((g0:A->complex) x))"
    let q57 ← q r"unit_group(ring_of_integers k):A group"
    let v58 ← ISPECL [q57, q56, q55, q54] ABELIAN_GROUP_DISCRETE_DEPENDENT
    let q59 ← q r"(\x:A. norm((g0:A->complex) x)) IN infinite_places k"
    let q60 ← q r"(g:A->complex) x"
    let v61 ← ISPEC q60 NORM_POS_LE
    let q62 ← q r"g:A->complex"
    let q63 ← q r"complex_embeddings(k:A ring)"
    let q64 ← q r"\g:A->complex. norm(g(x:A))"
    let v65 ← ISPECL [q64, q63] PRODUCT_EQ_0
    let q66 ← q r"x:A"
    let q67 ← q r"k:A ring"
    let v68 ← ISPECL [q67, q66] RING_OF_INTEGERS_UNIT_NORM_PRODUCT
    let q69 ← q r"!g x. g IN complex_embeddings k /\ ring_unit (ring_of_integers k) x
            ==> &0 < norm((g:A->complex) x)"
    let q70 ← q r"g0:A->complex"
    let v71 ← GSYM MEMBER_NOT_EMPTY
    prove
      r"!k t:A->bool.
          number_field k /\ FINITE t /\
          (!u. u IN t ==> ring_unit (ring_of_integers k) u) /\
          CARD(infinite_places k) <= CARD t
          ==> ?n. (?u. u IN t /\ ~(n u = &0)) /\
                  group_sum (unit_group(ring_of_integers k)) t
                    (\u. group_zpow (unit_group(ring_of_integers k)) u (n u)) =
                  ring_1 k"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_COMPLEX_EMBEDDINGS)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY)) THEN REWRITE_TAC [v71] THEN DISCH_THEN (X_CHOOSE_TAC q70) THEN SUBGOAL_THEN q69 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC v68 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC v65 THEN ASM_REWRITE_TAC [REAL_OF_NUM_EQ, ARITH_EQ, NOT_EXISTS_THM] THEN DISCH_THEN (MP_TAC o (SPEC q62)) THEN ASM_REWRITE_TAC [] THEN MP_TAC v61 THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN q59 ASSUME_TAC THENL [REWRITE_TAC [infinite_places, IN_IMAGE] THEN ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC v58 THEN REWRITE_TAC [UNIT_GROUP, RING_OF_INTEGERS, IN_ELIM_THM, SUBSET, ABELIAN_UNIT_GROUP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [FINITE_DELETE, FINITE_INFINITE_PLACES, CARD_DELETE] THEN MATCH_MP_TAC r53 THEN CONJ_TAC THENL [MATCH_MP_TAC r51 THEN ASM_SIMP_TAC [CARD_EQ_0, FINITE_INFINITE_PLACES] THEN ASM_MESON_TAC [NOT_IN_EMPTY], ALL_TAC] THEN REWRITE_TAC [infinite_places, IN_DELETE, IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [], REWRITE_TAC [complex_embeddings, IN_ELIM_THM] THEN X_GEN_TAC q49 THEN STRIP_TAC THEN DISCH_TAC THEN X_GEN_TAC q48 THEN DISCH_TAC THEN X_GEN_TAC q47 THEN DISCH_TAC THEN MP_TAC v46 THEN ASM_REWRITE_TAC [COMPLEX_RING_CLAUSES] THEN DISCH_THEN (MP_TAC o (SPECL [q42, q41])) THEN ANTS_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC v40 THEN ASM_SIMP_TAC [RING_UNIT_IN_CARRIER], SIMP_TAC [COMPLEX_NORM_MUL]], ALL_TAC] THEN X_GEN_TAC q39 THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC q38 THEN ASM_SIMP_TAC [RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC q37 THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_UNIT_IN_CARRIER] THEN X_GEN_TAC q36 THEN DISCH_TAC THEN SUBGOAL_THEN q35 ASSUME_TAC THENL [ASM_SIMP_TAC [LE_1, CARD_EQ_0, COMPLEX_EMBEDDINGS_NONEMPTY], ALL_TAC] THEN ASM_CASES_TAC q34 THENL [ALL_TAC, TRANS_TAC REAL_LE_TRANS q33 THEN ASM_SIMP_TAC [REAL_POW_MONO, r32] THEN REWRITE_TAC [REAL_POW_1] THEN FIRST_X_ASSUM (MP_TAC o (SPEC q30)) THEN ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC] THEN ASM_CASES_TAC q29 THENL [TRANS_TAC REAL_LE_TRANS q28 THEN ASM_SIMP_TAC [REAL_POW_LE_1, r27], RULE_ASSUM_TAC (REWRITE_RULE [REAL_NOT_LE])] THEN TRANS_TAC REAL_LE_TRANS q25 THEN CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC [r24] THEN ARITH_TAC] THEN MATCH_MP_TAC bound THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC q22 THEN STRIP_TAC THEN ASM_CASES_TAC q21 THENL [SUBGOAL_THEN q20 SUBST1_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN TRANS_TAC REAL_LE_TRANS q19 THEN CONJ_TAC THENL [REAL_ARITH_TAC, MATCH_MP_TAC REAL_LE_MUL2] THEN ASM_REAL_ARITH_TAC, FIRST_X_ASSUM (MP_TAC o (SPEC q18)) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN q17 ASSUME_TAC THENL [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC q16 THEN ASM_SIMP_TAC [], ALL_TAC] THEN TRANS_TAC REAL_LE_TRANS q15 THEN CONJ_TAC THENL [ASM_SIMP_TAC [REAL_MUL_RINV, REAL_LT_IMP_NZ, REAL_LE_REFL], MATCH_MP_TAC REAL_LE_MUL2] THEN ASM_SIMP_TAC [REAL_LE_INV_EQ, REAL_LT_IMP_LE] THEN REAL_ARITH_TAC])

  let NUMBER_FIELD_ROOTS_OF_UNITY_CYCLIC ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"0 < n <=> 1 <= n")
    let r2 ← ARITH_RULE (← q r"1 <= n <=> 0 < n")
    prove
      r"!k:A ring.
          number_field k
          ==> ?z. z IN ring_carrier k /\
                  (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                  !x. x IN ring_carrier k /\
                      (?m. 1 <= m /\ ring_pow k x m = ring_1 k)
                      ==> ?j. x = ring_pow k z j"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP NUMBER_FIELD_ROOTS_OF_UNITY_FINITE)) THEN ABBREV_TAC (← q r"w = {x:A | x IN ring_carrier k /\
                           ?m. 1 <= m /\ ring_pow k x m = ring_1 k}") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"?d. !x:A. x IN w ==> 1 <= d x /\ ring_pow k x (d x) = ring_1 k") (X_CHOOSE_TAC (← q r"d:A->num")) THENL [REWRITE_TAC [(← GSYM SKOLEM_THM), (← GSYM RIGHT_IMP_EXISTS_THM)] THEN EXPAND_TAC "w" THEN REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"1 <= nproduct w (d:A->num)") ASSUME_TAC THENL [REWRITE_TAC [r2] THEN MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_SIMP_TAC [r1], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x:A. x IN w ==> ring_pow k x (nproduct w d) = ring_1 k") ASSUME_TAC THENL [X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"d:A->num"), (← q r"w:A->bool"), (← q r"x:A")] NPRODUCT_DELETE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [UNDISCH_TAC (← q r"(x:A) IN w") THEN EXPAND_TAC "w" THEN SIMP_TAC [IN_ELIM_THM], ASM_SIMP_TAC [RING_POW_MUL, RING_POW_ONE]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"nproduct w (d:A->num)")] INTEGRAL_DOMAIN_ROOTS_OF_UNITY_CYCLIC) THEN ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD, FIELD_IMP_INTEGRAL_DOMAIN] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"z:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [EXISTS_TAC (← q r"nproduct w (d:A->num)") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"x:A"))) THEN SUBGOAL_THEN (← q r"(x:A) IN w") (fun th => ASM_SIMP_TAC [th]) THENL [EXPAND_TAC "w" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [], MESON_TAC []])

  let NUMBER_FIELD_FUNDAMENTAL_UNITS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"~(p <= t) ==> t <= p - 1")
    prove
      r"!k:A ring.
        number_field k
        ==> ?t. t HAS_SIZE (CARD(infinite_places k) - 1) /\
                (!u. u IN t ==> ring_unit (ring_of_integers k) u) /\
                (!n. group_sum (unit_group(ring_of_integers k)) t
                       (\u. group_zpow (unit_group(ring_of_integers k)) u
                                       (n u)) =
                     ring_1 k
                     ==> !u. u IN t ==> n u = &0) /\
                !u. ring_unit (ring_of_integers k) u
                    ==> ?z n. z IN ring_carrier k /\
                              (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                              u = ring_mul k z
                                   (group_sum (unit_group(ring_of_integers k)) t
                                     (\x. group_zpow
                                           (unit_group(ring_of_integers k)) x
                                           (n x)))"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"unit_group(ring_of_integers k):A group") FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS) THEN ASM_SIMP_TAC [ABELIAN_UNIT_GROUP, NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED] THEN REWRITE_TAC [UNIT_GROUP, RING_OF_INTEGERS, SUBSET, IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:A->bool") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rep") (LABEL_TAC "rank"))))) THEN REWRITE_TAC [HAS_SIZE, (← GSYM CONJ_ASSOC)] THEN REPEAT CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, REWRITE_TAC [(← GSYM LE_ANTISYM)] THEN CONJ_TAC THENL [MATCH_MP_TAC r1 THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"t:A->bool")] NUMBER_FIELD_UNITS_DEPENDENT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ASM_MESON_TAC []], MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_UNITS_INDEPENDENT) THEN ASM_REWRITE_TAC [HAS_SIZE] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"s:A->bool") (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) STRIP_ASSUME_TAC)) THEN USE_THEN "rank" MATCH_MP_TAC THEN ASM_REWRITE_TAC []], FIRST_ASSUM ACCEPT_TAC, FIRST_ASSUM ACCEPT_TAC, X_GEN_TAC (← q r"u:A") THEN DISCH_TAC THEN USE_THEN "rep" (MP_TAC o (SPEC (← q r"u:A"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"z:A") THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"n:A->int") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET) THEN ASM_SIMP_TAC [RING_UNIT_IN_CARRIER], EXISTS_TAC (← q r"group_element_order (unit_group(ring_of_integers k)) (z:A)") THEN ASM_SIMP_TAC [LE_1] THEN MP_TAC (← ISPECL [(← q r"unit_group(ring_of_integers k):A group"), (← q r"z:A"), (← q r"group_element_order (unit_group(ring_of_integers k)) (z:A)")] GROUP_POW_EQ_ID) THEN ASM_REWRITE_TAC [UNIT_GROUP, UNIT_GROUP_POW, RING_OF_INTEGERS, IN_ELIM_THM, DIVIDES_REFL]]])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_UNIT_DOMINANT_PLACE, NUMBER_FIELD_UNITS_INDEPENDENT,
           NUMBER_FIELD_UNITS_DEPENDENT, NUMBER_FIELD_ROOTS_OF_UNITY_CYCLIC,
           NUMBER_FIELD_FUNDAMENTAL_UNITS }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- unit_theorem.ml phrases from line 805 to 805                           -/
/- ---------------------------------------------------------------------- -/

structure UnitTheorem02 where
  -- @@FIELDS
  NUMBER_FIELD_UNITS_ROOTS_OF_UNITY : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupUnitTheorem02 [HolBase] (D : UnitTheoremDeps) (BUnitTheorem01 : UnitTheorem01) :
    ExceptT String IO UnitTheorem02 := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, .. } := D
  let { ARITH_EQ, CARD_CLAUSES, CARD_EQ_0, COMPLEX_EMBEDDINGS_NONEMPTY, COND_ID,
        EQ_TRANS, FINITE_INFINITE_PLACES, GROUP_NPOW, GROUP_SUM_CLAUSES_EXISTS,
        GROUP_SUM_SING, GROUP_SUM_SUPERSET, GROUP_ZPOW_0, HAS_SIZE, HAS_SIZE_0,
        IMAGE_EQ_EMPTY, INT_OF_NUM_EQ, IN_SING, MEMBER_NOT_EMPTY, .. } := D.core1
  let { RING_MUL_RID, RING_OF_INTEGERS, SING_SUBSET, SUB_REFL, UNIT_GROUP,
        UNIT_GROUP_POW, infinite_places, .. } := D.core2
  let { NUMBER_FIELD_FUNDAMENTAL_UNITS, .. } := BUnitTheorem01
  -- @@SCOPE END

  let NUMBER_FIELD_UNITS_ROOTS_OF_UNITY ← prove
    r"!k:A ring.
        number_field k
        ==> ((!u. ring_unit (ring_of_integers k) u
                  ==> ?m. 1 <= m /\ ring_pow k u m = ring_1 k) <=>
             CARD(infinite_places k) = 1)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP NUMBER_FIELD_FUNDAMENTAL_UNITS)) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:A->bool") (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 (LABEL_TAC "units") (CONJUNCTS_THEN2 (LABEL_TAC "indep") (LABEL_TAC "rep"))))) THEN SUBGOAL_THEN (← q r"~(infinite_places(k:A ring) = {})") MP_TAC THENL [ASM_SIMP_TAC [infinite_places, IMAGE_EQ_EMPTY, COMPLEX_EMBEDDINGS_NONEMPTY], ASM_SIMP_TAC [(← GSYM CARD_EQ_0), FINITE_INFINITE_PLACES]] THEN ASM_CASES_TAC (← q r"CARD(infinite_places(k:A ring)) = 1") THEN FIRST_ASSUM (fun th => REWRITE_TAC [th, SUB_REFL, HAS_SIZE_0, ARITH_EQ]) THENL [DISCH_THEN SUBST_ALL_TAC THEN X_GEN_TAC (← q r"u:A") THEN DISCH_TAC THEN REMOVE_THEN "rep" (MP_TAC o (SPEC (← q r"u:A"))) THEN ASM_REWRITE_TAC [(← CONJUNCT1 (← SPEC_ALL GROUP_SUM_CLAUSES_EXISTS)), UNIT_GROUP, RING_OF_INTEGERS] THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_MUL_RID] THEN ASM_MESON_TAC [], REWRITE_TAC [HAS_SIZE] THEN DISCH_TAC THEN STRIP_TAC THEN DISCH_THEN (LABEL_TAC "ru")] THEN SUBGOAL_THEN (← q r"?v:A. v IN t") STRIP_ASSUME_TAC THENL [REWRITE_TAC [MEMBER_NOT_EMPTY] THEN DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [CARD_CLAUSES]) THEN ASM_ARITH_TAC, ALL_TAC] THEN USE_THEN "units" (MP_TAC o (SPEC (← q r"v:A"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, DISCH_TAC] THEN USE_THEN "ru" (MP_TAC o (SPEC (← q r"v:A"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:num") STRIP_ASSUME_TAC) THEN USE_THEN "indep" (MP_TAC o (SPEC (← q r"\x:A. if x = v then &m else &0:int"))) THEN ANTS_TAC THENL [BETA_TAC THEN TRANS_TAC EQ_TRANS (← q r"group_sum (unit_group(ring_of_integers k)) {v:A}
       (\x. group_zpow (unit_group(ring_of_integers k)) x
              (if x = v then &m else &0))") THEN CONJ_TAC THENL [MATCH_MP_TAC GROUP_SUM_SUPERSET THEN ASM_SIMP_TAC [SING_SUBSET, IN_SING, GROUP_ZPOW_0], ASM_REWRITE_TAC [GROUP_SUM_SING, GROUP_NPOW, UNIT_GROUP_POW, UNIT_GROUP, RING_OF_INTEGERS, COND_ID]], DISCH_THEN (MP_TAC o (SPEC (← q r"v:A"))) THEN ASM_REWRITE_TAC [INT_OF_NUM_EQ] THEN ASM_ARITH_TAC])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_UNITS_ROOTS_OF_UNITY }
  -- @@RETURN END

end HolANT.UnitTheorem
