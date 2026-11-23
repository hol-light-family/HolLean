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
  literals right to left.  The `do` macro of HolCore/OcamlOrder.lean
  (HolLight.Syntax) binds each statement's `(← ...)` actions in that order,
  so quotations and rules (MESON, ARITH_RULE, ...) run as in HOL Light;
  where a rule is bound by a `let` before the proof, it is bound in OCaml's
  order.
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
    let lemma := (← prove r"!k s.
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
                          sqrt(abs(real_of_int(number_field_discriminant k)))" (REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC (← q r"a:A") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"FINITE(complex_embeddings(k:A ring)) /\
                  FINITE(s:(A->complex)->bool) /\ (a:A) IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [FINITE_COMPLEX_EMBEDDINGS, FINITE_SUBSET, RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!h:A->complex. h IN complex_embeddings k ==> &0 < norm(h a)") ASSUME_TAC THENL [ASM_SIMP_TAC [COMPLEX_EMBEDDINGS_NORM_POS, NUMBER_FIELD_IMP_FIELD], ALL_TAC] THEN ABBREV_TAC (← q r"D = sqrt(abs(real_of_int(number_field_discriminant(k:A ring))))") THEN ABBREV_TAC (← q r"p = product (complex_embeddings k DIFF s)
                            (\h:A->complex. norm(h(a:A)) / &2)") THEN SUBGOAL_THEN (← q r"&0:real < D /\ &0:real < p") STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["D", "p"] THEN CONJ_TAC THENL [ASM_SIMP_TAC [SQRT_POS_LT, (← GSYM REAL_ABS_NZ), REAL_OF_INT_CLAUSES, NUMBER_FIELD_DISCRIMINANT_NONZERO], MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_SIMP_TAC [FINITE_DIFF, IN_DIFF, REAL_HALF]], ALL_TAC] THEN SUBGOAL_THEN (← q r"product (complex_embeddings k)
        (\h:A->complex. if h IN s then root (CARD s) (D / p)
                        else norm(h(a:A)) / &2) = D") ASSUME_TAC THENL [ASM_SIMP_TAC [product, (← MATCH_MP ITERATE_CASES MONOIDAL_REAL_MUL)] THEN REWRITE_TAC [(← GSYM product)] THEN ASM_SIMP_TAC [(← SET_RULE (← q r"!s t:(A->complex)->bool.
                     s SUBSET t ==> {x | x IN t /\ x IN s} = s"))] THEN REWRITE_TAC [(← SET_RULE (← q r"!s t:(A->complex)->bool.
                    {x | x IN t /\ ~(x IN s)} = t DIFF s"))] THEN ASM_SIMP_TAC [PRODUCT_CONST, REAL_POW_ROOT, CARD_EQ_0, REAL_LE_DIV, REAL_LT_IMP_LE, REAL_DIV_RMUL, REAL_LT_IMP_NZ], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_carrier(ring_of_integers k):A->bool"), (← q r"\h:A->complex. if h IN s then root (CARD(s:(A->complex)->bool)) (D / p)
                     else norm(h(a:A)) / &2")] NUMBER_FIELD_IDEAL_MINKOWSKI) THEN ASM_REWRITE_TAC [RING_IDEAL_CARRIER, IDEAL_NORM_CARRIER, REAL_MUL_RID, REAL_LE_REFL] THEN ANTS_TAC THENL [REPEAT CONJ_TAC THENL [ASM SET_TAC [], GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [ROOT_POS_LT, REAL_LT_DIV, REAL_HALF], MAP_EVERY X_GEN_TAC [(← q r"g:A->complex"), (← q r"h:A->complex")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(h:A->complex) IN s <=> g IN s") SUBST1_TAC THENL [EQ_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL [EXISTS_TAC (← q r"h:A->complex"), EXISTS_TAC (← q r"g:A->complex")] THEN ASM_SIMP_TAC [], ASM_SIMP_TAC []]], MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"b:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"h:A->complex") THEN REWRITE_TAC [IN_DIFF] THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"h:A->complex"))) THEN ASM_REWRITE_TAC [], FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) THEN MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC [NORM_POS_LE]]]))
    prove
      r"!k (g:A->complex).
          number_field k /\ g IN complex_embeddings k
          ==> ?u. ring_unit (ring_of_integers k) u /\
                  !h. h IN complex_embeddings k /\
                      ~(!x. x IN ring_carrier k ==> norm(h x) = norm(g x))
                      ==> norm(h u) < &1"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"?a:num->A.
        (!m. (a m IN ring_carrier(ring_of_integers k) /\ ~(a m = ring_0 k)) /\
             product (complex_embeddings k) (\h. norm(h(a m))) <=
             sqrt(abs(real_of_int(number_field_discriminant k)))) /\
        (!h. h IN complex_embeddings k /\
             ~(!x. x IN ring_carrier k ==> norm(h x) = norm((g:A->complex) x))
             ==> !m n. m < n ==> norm(h(a n)) < norm(h(a m)))") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{h | h IN complex_embeddings k /\
              !x. x IN ring_carrier k ==> norm(h x) = norm((g:A->complex) x)}")] lemma) THEN ANTS_TAC THENL [REWRITE_TAC [SUBSET, IN_ELIM_THM, (← GSYM MEMBER_NOT_EMPTY)] THEN ASM_MESON_TAC [], REWRITE_TAC [IN_DIFF, IN_ELIM_THM]] THEN DISCH_THEN ((X_CHOOSE_TAC (← q r"f:A->A")) o ((REWRITE_RULE [SKOLEM_THM]) o (GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]))) THEN SUBGOAL_THEN (← q r"ring_1 k IN ring_carrier(ring_of_integers k) /\
                    ~(ring_1 k:A = ring_0 k)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_1) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, FIELD_NONTRIVIAL], ALL_TAC] THEN EXISTS_TAC (← q r"\m. ITER m (f:A->A) (f(ring_1 k))") THEN BETA_TAC THEN MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL [INDUCT_TAC THEN ASM_SIMP_TAC [ITER], DISCH_TAC THEN X_GEN_TAC (← q r"h:A->complex") THEN STRIP_TAC THEN MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN CONJ_TAC THENL [REAL_ARITH_TAC, X_GEN_TAC (← q r"m:num")] THEN REWRITE_TAC [ITER] THEN MATCH_MP_TAC (← REAL_ARITH (← q r"&0 < y /\ x <= y / &2 ==> x < y")) THEN ASM_SIMP_TAC [COMPLEX_EMBEDDINGS_NORM_POS, (← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET)]], ALL_TAC] THEN SUBGOAL_THEN (← q r"?m n. m < n /\
            ideal_generated (ring_of_integers k) {(a:num->A) n} =
            ideal_generated (ring_of_integers k) {a m}") STRIP_ASSUME_TAC THENL [X_CHOOSE_TAC (← q r"c:num") (← SPEC (← q r"sqrt(abs(real_of_int(number_field_discriminant(k:A ring))))") REAL_ARCH_SIMPLE) THEN FIRST_ASSUM (ASSUME_TAC o ((SPEC (← q r"c:num")) o (MATCH_MP NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM))) THEN MP_TAC (← ISPECL [(← q r"\m. ideal_generated (ring_of_integers k) {(a:num->A) m}"), (← q r"(:num)")] FINITE_IMAGE_INJ_EQ) THEN MATCH_MP_TAC (← TAUT (← q r"~r /\ q /\ (~p ==> s) ==> (p ==> (q <=> r)) ==> s")) THEN REWRITE_TAC [(← GSYM INFINITE), num_INFINITE] THEN CONJ_TAC THENL [FIRST_X_ASSUM (MATCH_MP_TAC o (MATCH_MP (← REWRITE_RULE [IMP_CONJ] FINITE_SUBSET))) THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_UNIV, IN_ELIM_THM] THEN X_GEN_TAC (← q r"m:num") THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN CONJ_TAC THENL [REWRITE_TAC [EXTENSION, IN_SING] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"(a:num->A) m"))) THEN ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF], REWRITE_TAC [(← GSYM REAL_OF_NUM_LE)] THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS] THEN ASM_MESON_TAC [REAL_LE_TRANS]], REWRITE_TAC [IN_UNIV, NOT_FORALL_THM, NOT_IMP] THEN MESON_TAC [LT_CASES]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"(a:num->A) n"), (← q r"(a:num->A) m")] IDEALS_GENERATED_SING_EQ) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_ASSOCIATES, INTEGRAL_DOMAIN_RING_OF_INTEGERS] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"u:A") THEN REWRITE_TAC [RING_OF_INTEGERS] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"h:A->complex") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:num->A) m IN ring_carrier k /\ u IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_UNIT_IN_CARRIER, RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"h:A->complex"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (SPECL [(← q r"m:num"), (← q r"n:num")])) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun z29 => (do let z30 ← (do let z31 ← (pure z29); pure (concl z31)); pure (is_eq z30)))))) THEN ASM_SIMP_TAC [COMPLEX_EMBEDDINGS_NORM_MUL] THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← GSYM REAL_MUL_RID)] THEN ASM_SIMP_TAC [REAL_LT_LMUL_EQ, COMPLEX_EMBEDDINGS_NORM_POS])

  let NUMBER_FIELD_UNITS_INDEPENDENT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let lemma := (← prove r"!G (f:K->A->real) s t (u:(A->real)->A).
        abelian_group G /\ FINITE s /\ FINITE t /\
        (!i x. i IN s /\ x IN group_carrier G ==> &0 < f i x) /\
        (!i x y. i IN s /\ x IN group_carrier G /\ y IN group_carrier G
                 ==> f i (group_mul G x y) = f i x * f i y) /\
        (!x. x IN group_carrier G ==> product s (\i. f i x) = &1) /\
        (?j. j IN s /\ ~(f j IN t)) /\
        (!v. v IN t ==> u v IN group_carrier G) /\
        (!i v. i IN s /\ v IN t /\ ~(f i = v) ==> f i (u v) < &1)
        ==> !n. group_sum G t (\v. group_zpow G (u v) (n v)) = group_id G
                ==> !v. v IN t ==> n v = &0" (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!n. group_sum G t (\v. group_zpow G ((u:(A->real)->A) v) (n v)) =
          group_id G
          ==> !v. v IN t ==> n v <= &0") ASSUME_TAC THENL [X_GEN_TAC (← q r"n:(A->real)->int") THEN DISCH_TAC THEN X_GEN_TAC (← q r"w:A->real") THEN REWRITE_TAC [(← GSYM INT_NOT_LT)] THEN REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"beta = \x:A. product {i:K | i IN s /\
                           ~(f i IN t /\ &0 < (n:(A->real)->int)(f i))}
                           (\i. f i x)") THEN SUBGOAL_THEN (← q r"(!x. x IN group_carrier G ==> &0 < (beta:A->real) x) /\
        (!x y. x IN group_carrier G /\ y IN group_carrier G
               ==> beta(group_mul G x y) = beta x * beta y)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "beta" THEN SIMP_TAC [(← GSYM PRODUCT_MUL), FINITE_RESTRICT, (← ASSUME (← q r"FINITE(s:K->bool)"))] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL [MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_SIMP_TAC [FINITE_RESTRICT, IN_ELIM_THM], MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"G:A group"), (← q r"beta:A->real")] GROUP_REAL_MULTIPLICATIVE_ID_INV_POW) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!v. v IN t /\ &0 < (n:(A->real)->int) v
            ==> (beta:A->real)((u:(A->real)->A) v) < &1") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN EXPAND_TAC "beta" THEN MATCH_MP_TAC PRODUCT_LT_1 THEN EXISTS_TAC (← q r"j:K") THEN ASM_SIMP_TAC [FINITE_RESTRICT, IN_ELIM_THM] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"i:K") THEN STRIP_TAC THEN ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LT_IMP_LE, ALL_TAC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun z39 => (do let z40 ← (do let z41 ← (pure z39); pure (concl z41)); pure (is_neg z40))))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!v. v IN t /\ ~(&0 < (n:(A->real)->int) v)
            ==> &1 <= (beta:A->real)((u:(A->real)->A) v)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN EXPAND_TAC "beta" THEN MP_TAC (← SPEC (← q r"(u:(A->real)->A) v") (← ASSUME (← q r"!x. x IN group_carrier G
              ==> product s (\i. (f:K->A->real) i x) = &1"))) THEN ANTS_TAC THENL [ASM_SIMP_TAC [], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"s:K->bool"), (← q r"\i. (f:K->A->real) i IN t /\ &0 < (n:(A->real)->int)(f i)"), (← q r"\i. (f:K->A->real) i ((u:(A->real)->A) v)"), (← q r"\i. (f:K->A->real) i ((u:(A->real)->A) v)")] (← MATCH_MP ITERATE_CASES MONOIDAL_REAL_MUL)) THEN ASM_REWRITE_TAC [COND_ID, (← GSYM product)] THEN MATCH_MP_TAC (← REAL_ARITH (← q r"a:real * b <= &1 * b ==> &1 = a * b ==> &1 <= b")) THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [MATCH_MP_TAC PRODUCT_LE_1, MATCH_MP_TAC PRODUCT_POS_LE] THEN ASM_SIMP_TAC [FINITE_RESTRICT, IN_ELIM_THM, REAL_LT_IMP_LE] THEN X_GEN_TAC (← q r"i:K") THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"&0 < (n:(A->real)->int)((f:K->A->real) i)") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!v. v IN t
            ==> (beta:A->real)(group_zpow G ((u:(A->real)->A) v) (n v)) <= &1 /\
                (&0 < n v ==> beta(group_zpow G (u v) (n v)) < &1)") ASSUME_TAC THENL [X_GEN_TAC (← q r"v:A->real") THEN DISCH_TAC THEN REWRITE_TAC [group_zpow] THEN ASM_CASES_TAC (← q r"&0:int < n(v:A->real)") THEN ASM_SIMP_TAC [INT_LT_IMP_LE, GROUP_POW] THENL [MATCH_MP_TAC (← REAL_ARITH (← q r"x:real < &1 ==> x <= &1 /\ x < &1")) THEN MATCH_MP_TAC REAL_POW_1_LT THEN ASM_SIMP_TAC [REAL_LT_IMP_LE, (← GSYM INT_OF_NUM_EQ), INT_OF_NUM_OF_INT, INT_LT_IMP_LE, INT_LT_IMP_NE], COND_CASES_TAC THENL [SUBGOAL_THEN (← q r"(n:(A->real)->int) v = &0") SUBST1_TAC THENL [ASM_INT_ARITH_TAC, ASM_REWRITE_TAC [NUM_OF_INT_OF_NUM, group_pow]] THEN REAL_ARITH_TAC, ASM_SIMP_TAC [GROUP_POW] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_SIMP_TAC []]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"G:A group"), (← q r"beta:A->real"), (← q r"\v:A->real. group_zpow G ((u:(A->real)->A) v) (n v)"), (← q r"t:(A->real)->bool")] GROUP_REAL_MULTIPLICATIVE_SUM) THEN ASM_SIMP_TAC [GROUP_ZPOW] THEN MATCH_MP_TAC (← REAL_ARITH (← q r"x:real < &1 ==> ~(&1 = x)")) THEN MATCH_MP_TAC PRODUCT_LT_1 THEN EXISTS_TAC (← q r"w:A->real") THEN ASM_SIMP_TAC [] THEN X_GEN_TAC (← q r"v:A->real") THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [GROUP_ZPOW], ALL_TAC] THEN X_GEN_TAC (← q r"n:(A->real)->int") THEN DISCH_TAC THEN X_GEN_TAC (← q r"v:A->real") THEN DISCH_TAC THEN REWRITE_TAC [(← GSYM INT_LE_ANTISYM)] THEN CONJ_TAC THENL [ASM_MESON_TAC [], ONCE_REWRITE_TAC [(← INT_ARITH (← q r"&0:int <= x <=> --x <= &0"))] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"\v:A->real. --((n:(A->real)->int) v)"))) THEN ASM_SIMP_TAC [GROUP_ZPOW_NEG, ABELIAN_GROUP_SUM_INV, GROUP_ZPOW, FINITE_RESTRICT, GROUP_INV_ID]]))
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
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"!v. v IN infinite_places k
          ==> ?u. ring_unit (ring_of_integers k) u /\
                  !h. h IN complex_embeddings k /\ ~((\x. norm(h x)) = v)
                      ==> norm((h:A->complex) u) < &1") MP_TAC THENL [REWRITE_TAC [infinite_places, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"g:A->complex") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"g:A->complex")] NUMBER_FIELD_UNIT_DOMINANT_PLACE) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"u:A") THEN MATCH_MP_TAC MONO_AND THEN REWRITE_TAC [] THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"h:A->complex") THEN MATCH_MP_TAC (← TAUT (← q r"(q ==> p) ==> (p ==> r) ==> (q ==> r)")) THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"~((\x:A. norm((h:A->complex) x)) = (\x. norm((g:A->complex) x)))") THEN REWRITE_TAC [CONTRAPOS_THM, FUN_EQ_THM] THEN DISCH_TAC THEN X_GEN_TAC (← q r"x:A") THEN ASM_CASES_TAC (← q r"(x:A) IN ring_carrier k") THEN ASM_SIMP_TAC [] THEN RULE_ASSUM_TAC (REWRITE_RULE [complex_embeddings, EXTENSIONAL, IN_ELIM_THM]) THEN ASM_SIMP_TAC [], DISCH_THEN ((X_CHOOSE_TAC (← q r"u:(A->real)->A")) o ((REWRITE_RULE [SKOLEM_THM]) o (GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM])))] THEN SUBGOAL_THEN (← q r"!x. ring_unit (ring_of_integers k) x
          ==> (x:A) IN ring_carrier k /\ ~(x = ring_0 k)") ASSUME_TAC THENL [X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_UNIT_IN_CARRIER)) THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], DISCH_TAC] THEN UNDISCH_TAC (← q r"ring_unit (ring_of_integers k) (x:A)") THEN ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [(← GSYM (← CONJUNCT1 RING_OF_INTEGERS))] THEN ASM_SIMP_TAC [RING_UNIT_0, INTEGRAL_DOMAIN_RING_OF_INTEGERS, INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY)) THEN REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY)] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"g:A->complex")) THEN SUBGOAL_THEN (← q r"FINITE(complex_embeddings(k:A ring)) /\ FINITE(infinite_places k) /\
      (\x:A. norm((g:A->complex) x)) IN infinite_places k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [FINITE_COMPLEX_EMBEDDINGS, FINITE_INFINITE_PLACES] THEN REWRITE_TAC [infinite_places, IN_IMAGE] THEN EXISTS_TAC (← q r"g:A->complex") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"infinite_places k DELETE (\x:A. norm((g:A->complex) x)) HAS_SIZE
      CARD(infinite_places k) - 1") ASSUME_TAC THENL [ASM_SIMP_TAC [HAS_SIZE, FINITE_DELETE, CARD_DELETE], ALL_TAC] THEN SUBGOAL_THEN (← q r"!n. group_sum (unit_group(ring_of_integers k))
            (infinite_places k DELETE (\x. norm((g:A->complex) x)))
            (\v. group_zpow (unit_group(ring_of_integers k))
                            ((u:(A->real)->A) v) (n v)) = ring_1 k
          ==> !v. v IN infinite_places k DELETE (\x. norm(g x)) ==> n v = &0") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"unit_group(ring_of_integers k):A group"), (← q r"\h:A->complex x:A. norm(h x)"), (← q r"complex_embeddings(k:A ring)"), (← q r"infinite_places k DELETE (\x:A. norm((g:A->complex) x))"), (← q r"u:(A->real)->A")] lemma) THEN REWRITE_TAC [UNIT_GROUP, IN_ELIM_THM, RING_OF_INTEGERS, ABELIAN_UNIT_GROUP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [FINITE_DELETE, COMPLEX_EMBEDDINGS_NORM_POS, COMPLEX_EMBEDDINGS_NORM_MUL, IN_DELETE] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] RING_OF_INTEGERS_UNIT_NORM_PRODUCT) THEN ASM_SIMP_TAC [], EXISTS_TAC (← q r"g:A->complex") THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"!v w. v IN infinite_places k DELETE (\x. norm((g:A->complex) x)) /\
            w IN infinite_places k DELETE (\x. norm(g x)) /\
            (u:(A->real)->A) v = u w ==> v = w") (fun th => tactic_of do pure (MP_TAC (← MATCH_MP HAS_SIZE_IMAGE_INJ (← CONJ th (← ASSUME (← q r"infinite_places k DELETE (\x:A. norm((g:A->complex) x))
                   HAS_SIZE CARD(infinite_places k) - 1")))) THEN MP_TAC (← MATCH_MP GROUP_SUM_IMAGE (← CONJ (← ISPEC (← q r"ring_of_integers k:A ring") ABELIAN_UNIT_GROUP) th)))) THENL [REWRITE_TAC [IN_DELETE] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC (← TAUT (← q r"(~p ==> F) ==> p")) THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"!h. h IN complex_embeddings k
            ==> norm((h:A->complex)((u:(A->real)->A) w)) < &1") ASSUME_TAC THENL [X_GEN_TAC (← q r"h:A->complex") THEN DISCH_TAC THEN FIRST_X_ASSUM (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"h:A->complex") (← CONJUNCT2 (← MATCH_MP th (← ASSUME (← q r"(v:A->real) IN infinite_places k"))))) THEN MP_TAC (← SPEC (← q r"h:A->complex") (← CONJUNCT2 (← MATCH_MP th (← ASSUME (← q r"(w:A->real) IN infinite_places k"))))))) THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"~(v:A->real = w)") THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"product (complex_embeddings k)
          (\h. norm((h:A->complex)((u:(A->real)->A) w))) = &1") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"(u:(A->real)->A) w")] RING_OF_INTEGERS_UNIT_NORM_PRODUCT) THEN ASM_SIMP_TAC [], ALL_TAC] THEN MATCH_MP_TAC (← REAL_ARITH (← q r"x:real < &1 ==> x = &1 ==> F")) THEN MATCH_MP_TAC PRODUCT_LT_1 THEN EXISTS_TAC (← q r"g:A->complex") THEN ASM_SIMP_TAC [NORM_POS_LE, REAL_LT_IMP_LE], ALL_TAC] THEN DISCH_TAC THEN DISCH_TAC THEN EXISTS_TAC (← q r"IMAGE (u:(A->real)->A)
            (infinite_places k DELETE (\x. norm((g:A->complex) x)))") THEN ASM_SIMP_TAC [FORALL_IN_IMAGE, IN_DELETE, o_DEF] THEN X_GEN_TAC (← q r"n:A->int") THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"\v. (n:A->int)((u:(A->real)->A) v)"))) THEN REWRITE_TAC [IN_DELETE])

  let NUMBER_FIELD_UNITS_DEPENDENT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let lemma := (← prove r"!a c p. &0 <= a:real /\ a * p = &1 /\ &1 <= c * p ==> a <= c" (REPEAT STRIP_TAC THEN TRANS_TAC REAL_LE_TRANS (← q r"a * c * p:real") THEN CONJ_TAC THENL [GEN_REWRITE_TAC LAND_CONV [(← GSYM REAL_MUL_RID)] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [], SUBGOAL_THEN (← q r"a * c * p:real = c * (a * p)") SUBST1_TAC THENL [REWRITE_TAC [REAL_MUL_AC], ASM_REWRITE_TAC [REAL_MUL_RID, REAL_LE_REFL]]]))
    let bound := (← prove r"!k (g:A->complex) x B.
        number_field k /\ ring_unit (ring_of_integers k) x /\
        g IN complex_embeddings k /\
        (!h. h IN complex_embeddings k /\ ~(h = g) ==> &1 <= B * norm(h x))
        ==> norm(g x) <= B pow (CARD(complex_embeddings k) - 1)" (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_COMPLEX_EMBEDDINGS)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] RING_OF_INTEGERS_UNIT_NORM_PRODUCT) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"\h:A->complex. norm(h(x:A))"), (← q r"complex_embeddings(k:A ring)"), (← q r"g:A->complex")] PRODUCT_DELETE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MATCH_MP_TAC lemma THEN EXISTS_TAC (← q r"product (complex_embeddings k DELETE g)
                        (\h:A->complex. norm(h(x:A)))") THEN ASM_REWRITE_TAC [NORM_POS_LE] THEN SUBGOAL_THEN (← q r"product (complex_embeddings k DELETE g) (\h:A->complex. &1) <=
      product (complex_embeddings k DELETE g) (\h. B * norm(h(x:A)))") MP_TAC THENL [MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC [FINITE_DELETE, IN_DELETE, REAL_POS], ASM_SIMP_TAC [PRODUCT_ONE, PRODUCT_MUL, FINITE_DELETE, PRODUCT_CONST, CARD_DELETE]]))
    prove
      r"!k t:A->bool.
          number_field k /\ FINITE t /\
          (!u. u IN t ==> ring_unit (ring_of_integers k) u) /\
          CARD(infinite_places k) <= CARD t
          ==> ?n. (?u. u IN t /\ ~(n u = &0)) /\
                  group_sum (unit_group(ring_of_integers k)) t
                    (\u. group_zpow (unit_group(ring_of_integers k)) u (n u)) =
                  ring_1 k"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_COMPLEX_EMBEDDINGS)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY)) THEN REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY)] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"g0:A->complex")) THEN SUBGOAL_THEN (← q r"!g x. g IN complex_embeddings k /\ ring_unit (ring_of_integers k) x
            ==> &0 < norm((g:A->complex) x)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] RING_OF_INTEGERS_UNIT_NORM_PRODUCT) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"\g:A->complex. norm(g(x:A))"), (← q r"complex_embeddings(k:A ring)")] PRODUCT_EQ_0) THEN ASM_REWRITE_TAC [REAL_OF_NUM_EQ, ARITH_EQ, NOT_EXISTS_THM] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"g:A->complex"))) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPEC (← q r"(g:A->complex) x") NORM_POS_LE) THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"(\x:A. norm((g0:A->complex) x)) IN infinite_places k") ASSUME_TAC THENL [REWRITE_TAC [infinite_places, IN_IMAGE] THEN ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"unit_group(ring_of_integers k):A group"), (← q r"infinite_places k DELETE (\x:A. norm((g0:A->complex) x))"), (← q r"\(v:A->real) (x:A). v x"), (← q r"t:A->bool")] ABELIAN_GROUP_DISCRETE_DEPENDENT) THEN REWRITE_TAC [UNIT_GROUP, RING_OF_INTEGERS, IN_ELIM_THM, SUBSET, ABELIAN_UNIT_GROUP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [FINITE_DELETE, FINITE_INFINITE_PLACES, CARD_DELETE] THEN MATCH_MP_TAC (← TAUT (← q r"d /\ a /\ b /\ c ==> a /\ b /\ c /\ d")) THEN CONJ_TAC THENL [MATCH_MP_TAC (← ARITH_RULE (← q r"~(p = 0) /\ p <= t ==> p - 1 < t")) THEN ASM_SIMP_TAC [CARD_EQ_0, FINITE_INFINITE_PLACES] THEN ASM_MESON_TAC [NOT_IN_EMPTY], ALL_TAC] THEN REWRITE_TAC [infinite_places, IN_DELETE, IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [], REWRITE_TAC [complex_embeddings, IN_ELIM_THM] THEN X_GEN_TAC (← q r"g:A->complex") THEN STRIP_TAC THEN DISCH_TAC THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"g:A->complex")] RING_HOMOMORPHISM_MUL) THEN ASM_REWRITE_TAC [COMPLEX_RING_CLAUSES] THEN DISCH_THEN (MP_TAC o (SPECL [(← q r"x:A"), (← q r"y:A")])) THEN ANTS_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET) THEN ASM_SIMP_TAC [RING_UNIT_IN_CARRIER], SIMP_TAC [COMPLEX_NORM_MUL]], ALL_TAC] THEN X_GEN_TAC (← q r"b:real") THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{x | x IN ring_carrier(ring_of_integers k) /\
           !g. g IN complex_embeddings k
               ==> norm((g:A->complex) x) <=
                   max (&1) b pow CARD(complex_embeddings k)}") THEN ASM_SIMP_TAC [RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_UNIT_IN_CARRIER] THEN X_GEN_TAC (← q r"g:A->complex") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"1 <= CARD(complex_embeddings(k:A ring))") ASSUME_TAC THENL [ASM_SIMP_TAC [LE_1, CARD_EQ_0, COMPLEX_EMBEDDINGS_NONEMPTY], ALL_TAC] THEN ASM_CASES_TAC (← q r"(\x:A. norm((g:A->complex) x)) = (\x. norm((g0:A->complex) x))") THENL [ALL_TAC, TRANS_TAC REAL_LE_TRANS (← q r"max (&1:real) b pow 1") THEN ASM_SIMP_TAC [REAL_POW_MONO, (← REAL_ARITH (← q r"&1:real <= max (&1) b"))] THEN REWRITE_TAC [REAL_POW_1] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"g:A->complex"))) THEN ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC] THEN ASM_CASES_TAC (← q r"norm((g:A->complex) x) <= &1") THENL [TRANS_TAC REAL_LE_TRANS (← q r"&1:real") THEN ASM_SIMP_TAC [REAL_POW_LE_1, (← REAL_ARITH (← q r"&1:real <= max (&1) b"))], RULE_ASSUM_TAC (REWRITE_RULE [REAL_NOT_LE])] THEN TRANS_TAC REAL_LE_TRANS (← q r"max (&1:real) b pow (CARD(complex_embeddings(k:A ring)) - 1)") THEN CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC [(← REAL_ARITH (← q r"&1:real <= max (&1) b"))] THEN ARITH_TAC] THEN MATCH_MP_TAC bound THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"h:A->complex") THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"(\x:A. norm((h:A->complex) x)) = (\x. norm((g0:A->complex) x))") THENL [SUBGOAL_THEN (← q r"norm((h:A->complex) x) = norm((g:A->complex) x)") SUBST1_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN TRANS_TAC REAL_LE_TRANS (← q r"&1:real * &1") THEN CONJ_TAC THENL [REAL_ARITH_TAC, MATCH_MP_TAC REAL_LE_MUL2] THEN ASM_REAL_ARITH_TAC, FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"h:A->complex"))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"&0:real < b") ASSUME_TAC THENL [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q r"norm((h:A->complex) x)") THEN ASM_SIMP_TAC [], ALL_TAC] THEN TRANS_TAC REAL_LE_TRANS (← q r"b * inv b:real") THEN CONJ_TAC THENL [ASM_SIMP_TAC [REAL_MUL_RINV, REAL_LT_IMP_NZ, REAL_LE_REFL], MATCH_MP_TAC REAL_LE_MUL2] THEN ASM_SIMP_TAC [REAL_LE_INV_EQ, REAL_LT_IMP_LE] THEN REAL_ARITH_TAC])

  let NUMBER_FIELD_ROOTS_OF_UNITY_CYCLIC ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    prove
      r"!k:A ring.
          number_field k
          ==> ?z. z IN ring_carrier k /\
                  (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                  !x. x IN ring_carrier k /\
                      (?m. 1 <= m /\ ring_pow k x m = ring_1 k)
                      ==> ?j. x = ring_pow k z j"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP NUMBER_FIELD_ROOTS_OF_UNITY_FINITE)) THEN ABBREV_TAC (← q r"w = {x:A | x IN ring_carrier k /\
                           ?m. 1 <= m /\ ring_pow k x m = ring_1 k}") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"?d. !x:A. x IN w ==> 1 <= d x /\ ring_pow k x (d x) = ring_1 k") (X_CHOOSE_TAC (← q r"d:A->num")) THENL [REWRITE_TAC [(← GSYM SKOLEM_THM), (← GSYM RIGHT_IMP_EXISTS_THM)] THEN EXPAND_TAC "w" THEN REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"1 <= nproduct w (d:A->num)") ASSUME_TAC THENL [REWRITE_TAC [(← ARITH_RULE (← q r"1 <= n <=> 0 < n"))] THEN MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_SIMP_TAC [(← ARITH_RULE (← q r"0 < n <=> 1 <= n"))], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x:A. x IN w ==> ring_pow k x (nproduct w d) = ring_1 k") ASSUME_TAC THENL [X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"d:A->num"), (← q r"w:A->bool"), (← q r"x:A")] NPRODUCT_DELETE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [UNDISCH_TAC (← q r"(x:A) IN w") THEN EXPAND_TAC "w" THEN SIMP_TAC [IN_ELIM_THM], ASM_SIMP_TAC [RING_POW_MUL, RING_POW_ONE]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"nproduct w (d:A->num)")] INTEGRAL_DOMAIN_ROOTS_OF_UNITY_CYCLIC) THEN ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD, FIELD_IMP_INTEGRAL_DOMAIN] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"z:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [EXISTS_TAC (← q r"nproduct w (d:A->num)") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"x:A"))) THEN SUBGOAL_THEN (← q r"(x:A) IN w") (fun th => ASM_SIMP_TAC [th]) THENL [EXPAND_TAC "w" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [], MESON_TAC []])

  let NUMBER_FIELD_FUNDAMENTAL_UNITS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
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
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"unit_group(ring_of_integers k):A group") FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS) THEN ASM_SIMP_TAC [ABELIAN_UNIT_GROUP, NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED] THEN REWRITE_TAC [UNIT_GROUP, RING_OF_INTEGERS, SUBSET, IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:A->bool") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rep") (LABEL_TAC "rank"))))) THEN REWRITE_TAC [HAS_SIZE, (← GSYM CONJ_ASSOC)] THEN REPEAT CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, REWRITE_TAC [(← GSYM LE_ANTISYM)] THEN CONJ_TAC THENL [MATCH_MP_TAC (← ARITH_RULE (← q r"~(p <= t) ==> t <= p - 1")) THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"t:A->bool")] NUMBER_FIELD_UNITS_DEPENDENT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ASM_MESON_TAC []], MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_UNITS_INDEPENDENT) THEN ASM_REWRITE_TAC [HAS_SIZE] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"s:A->bool") (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) STRIP_ASSUME_TAC)) THEN USE_THEN "rank" MATCH_MP_TAC THEN ASM_REWRITE_TAC []], FIRST_ASSUM ACCEPT_TAC, FIRST_ASSUM ACCEPT_TAC, X_GEN_TAC (← q r"u:A") THEN DISCH_TAC THEN USE_THEN "rep" (MP_TAC o (SPEC (← q r"u:A"))) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"z:A") THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"n:A->int") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET) THEN ASM_SIMP_TAC [RING_UNIT_IN_CARRIER], EXISTS_TAC (← q r"group_element_order (unit_group(ring_of_integers k)) (z:A)") THEN ASM_SIMP_TAC [LE_1] THEN MP_TAC (← ISPECL [(← q r"unit_group(ring_of_integers k):A group"), (← q r"z:A"), (← q r"group_element_order (unit_group(ring_of_integers k)) (z:A)")] GROUP_POW_EQ_ID) THEN ASM_REWRITE_TAC [UNIT_GROUP, UNIT_GROUP_POW, RING_OF_INTEGERS, IN_ELIM_THM, DIVIDES_REFL]]])

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
