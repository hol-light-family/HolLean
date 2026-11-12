/- ========================================================================= -/
/- ANT: The Dedekind zeta function of a number field k for Re s > 1 ...    -/
/- ========================================================================= -/
/- File: HolANT/DedekindZeta.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/dedekind_zeta.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antdedekindzetadiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, Library/frag.ml, Library/grouptheory.ml, Library/floor.ml, Multivariate/misc.ml, Multivariate/metric.ml, Multivariate/homology.ml, Multivariate/vectors.ml, Multivariate/determinants.ml, Multivariate/topology.ml, Multivariate/convex.ml, Multivariate/paths.ml, Multivariate/polytope.ml, Multivariate/degree.ml, Multivariate/derivatives.ml, Multivariate/integration.ml, Multivariate/measure.ml, Multivariate/complex_algebra.ml, Multivariate/complexes.ml, Multivariate/canal.ml, Multivariate/transcendentals.ml, Multivariate/realanalysis.ml, ANT/algmisc.ml, ANT/ideal_arith.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, Library/isum.ml, ANT/zlattice.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/classgroup.ml, ANT/prime_split.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/nf_valuation.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/integrality.ml, Library/ring_groups.ml, ANT/fingen_group.ml, Multivariate/moretop.ml, Multivariate/cauchy.ml, Multivariate/complex_ring.ml, Multivariate/complex_field.ml, ANT/complex_embeddings.ml, ANT/power_basis.ml, ANT/infinite_places.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.DedekindZeta fills them).

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
import HolLibrary.Products
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.Floor
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
import HolANT.Algmisc
import HolANT.IdealArith
import HolANT.Integral
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolLibrary.Isum
import HolANT.Zlattice
import HolANT.Numfield
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.Discriminant
import HolANT.Classgroup
import HolANT.PrimeSplit
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.NfValuation
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.Integrality
import HolLibrary.RingGroups
import HolANT.FingenGroup
import HolMultiLib.MoreTop
import HolMultiLib.Cauchy
import HolMultiLib.ComplexRing
import HolMultiLib.ComplexField
import HolANT.ComplexEmbeddings
import HolANT.PowerBasis
import HolANT.InfinitePlaces

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
open HolANT.Discriminant
open HolANT.Classgroup
open HolANT.PrimeSplit
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.NfValuation
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.Integrality
open HolANT.FingenGroup
open HolANT.ComplexEmbeddings
open HolANT.PowerBasis
open HolANT.InfinitePlaces

namespace HolANT.DedekindZeta

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD_CLAUSES ADD_SUB ALWAYS_EVENTUALLY ARITH CARD_CLAUSES CARD_CROSS CARD_EQ_0
   CARD_IMAGE_INJ CARD_SUBSET CARD_UNION_EQ COMPLEX_CMUL
   COMPLEX_EMBEDDINGS_HAS_SIZE COMPLEX_MUL_LID COMPLEX_NORM_0 COMPLEX_NORM_CX
   COMPLEX_NORM_DIV COMPLEX_NORM_INV COMPLEX_NORM_MUL COMPLEX_POW_INV
   COMPLEX_RING_CLAUSES COMPLEX_RING_OF_INT COMPLEX_RING_OF_NUM COMPLEX_RING_SUM
   COMPLEX_SUB_RDISTRIB CONJ_ASSOC CONVERGENT_REAL_BOUNDED_MONOTONE
   CPOW_NPRODUCT CPOW_NUM_EXP CPRODUCT_EQ CPRODUCT_INV CPRODUCT_VSUM_POW CX_DIV
   CX_INV CX_PRODUCT CX_RPOW CX_SUB DEDEKIND_IDEAL_EQ_VALUATION
   DEDEKIND_IDEAL_NORM_PRIME_POWERS DEDEKIND_IDEAL_PRODUCT_PRIME_POWERS
   DEDEKIND_IDEAL_PROD_CANCEL DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES
   DEDEKIND_IDEAL_SUBSET_POW_VALUATION DEDEKIND_RING_OF_INTEGERS DE_MORGAN_THM
   DIVIDES_LE_IMP DIVISION DIV_MUL_LE EQ_IMP EQ_IMP_LE EQ_TRANS ETA_AX
   EVENTUALLY_SEQUENTIALLY EVENTUALLY_TRUE EVENTUALLY_WITHINREAL
   EVENTUALLY_WITHIN_IMP EXP_1 EXP_2 EXP_MONO_LE EXP_ONE EXTENSION
   FIELD_NONTRIVIAL FINITE_COMPLEX_EMBEDDINGS FINITE_CROSS FINITE_FUNSPACE
   FINITE_IMAGE FINITE_INTER FINITE_NUMSEG FINITE_NUMSEG_LT FINITE_RESTRICT
   FINITE_SUBSET FINITE_UNION FORALL_AND_THM FORALL_IN_IMAGE FORALL_PAIR_THM
   FREE_BASIS_IDEAL_BOX_PRINCIPLE FREE_BASIS_INTEGER_RING_LINCOMB
   FREE_BASIS_IN_CARRIER FREE_BASIS_NORM_BOUND FROM_0 FROM_INTER_NUMSEG
   FUN_EQ_THM GE HAS_SIZE HAS_SIZE_CARD HAS_SIZE_FUNSPACE HAS_SIZE_INT_ABS_LE
   HAS_SIZE_NUMSEG HAS_SIZE_NUMSEG_LT IDEAL_GENERATED_EQ_0
   IDEAL_GENERATED_MINIMAL IDEAL_NORM_CARRIER IDEAL_NORM_GT_1
   IDEAL_NORM_IDEAL_POW IDEAL_NORM_POS IDEAL_NORM_SUBSET_DIVIDES IDEAL_PROD_COMM
   IDEAL_PROD_EQ_ZERO IMP_CONJ IMP_IMP INFINITE INTEGER_RING
   INTEGRAL_DOMAIN_RING_OF_INTEGERS INTER_SUBSET INTER_UNIV INT_ABS_POS
   INT_LE_LMUL INT_LE_LMUL_EQ INT_LE_MUL INT_LE_REFL INT_LE_TRANS INT_MUL_AC
   INT_OF_NUM_LE INT_OF_NUM_LT INT_OF_NUM_MUL INT_OF_NUM_OF_INT INT_OF_NUM_POW
   INT_POS INT_POW_LE INT_POW_MUL IN_CROSS IN_ELIM_THM IN_FROM
   IN_IDEAL_GENERATED_SELF IN_IDEAL_GENERATED_SING_EQ IN_IMAGE IN_INTER
   IN_NUMSEG IN_SING IN_UNIV LE LEFT_ADD_DISTRIB : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (LEFT_IMP_EXISTS_THM LE_0 LE_1 LE_EXP LE_MULT2 LE_MULT_LCANCEL LE_MULT_RCANCEL
   LE_REFL LE_SQUARE_REFL LE_TRANS LIM_CONST LIM_CPRODUCT LIM_NORM_UBOUND
   LIM_SEQUENTIALLY LIM_SUB LOG_DIV LOG_EXP LOG_INV LOG_MONO_LE_IMP
   LOG_MONO_LT_IMP LOG_POS_LT LTE_TRANS LT_IMP_LE LT_NZ LT_POW2_REFL
   MEMBER_NOT_EMPTY MONO_EXISTS MULT_AC MULT_ASSOC MULT_CLAUSES MULT_EXP
   MULT_SYM NORM_CPOW NORM_POS_LE NOT_LT NUMBER_FIELD_DEGREE_POS
   NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM
   NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM NUMBER_FIELD_IDEAL_NORM_MUL_Q
   NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS
   NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_NORM_INTEGRAL_BASIS NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q
   NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2
   NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q NUM_ROOT_FLOOR PAIR_EQ PRIME_GE_2
   PRIME_IMP_PROPER_IDEAL PRIME_IMP_RING_IDEAL PRODUCT_CONST PRODUCT_LE
   PROPER_IDEAL_ALT REALLIM_ADD REALLIM_COMPLEX REALLIM_CONST REALLIM_LBOUND
   REALLIM_LE REALLIM_LMUL REALLIM_REAL_CONTINUOUS_FUNCTION REALLIM_SEQUENTIALLY
   REALLIM_SUB REALLIM_TRANSFORM_EVENTUALLY REALLIM_UBOUND REALLIM_UNIQUE
   REALLIM_WITHINREAL REAL_ABS_DIV REAL_ABS_LE REAL_ABS_MUL REAL_ABS_NUM
   REAL_ABS_POS REAL_ABS_RPOW REAL_ADD_LDISTRIB REAL_ADD_LID REAL_ADD_RDISTRIB
   REAL_ADD_RID REAL_ARCH_SIMPLE REAL_BOUNDED_POS REAL_CONTINUOUS_AT_EXP REAL_CX
   REAL_EQ_IMP_LE REAL_EXP_LE_INV_1_SUB REAL_EXP_MONO_LE REAL_EXP_POS_LE
   REAL_EXP_POS_LT REAL_EXP_SUM REAL_INFSUM_ADD REAL_INFSUM_SUB
   REAL_INFSUM_UNIQUE REAL_INFSUM_ZETA_BOUNDS REAL_INV_0 REAL_INV_1
   REAL_INV_1_LT REAL_INV_1_SUB_LE_EXP REAL_INV_LE_1 REAL_INV_LT_1
   REAL_LET_TRANS REAL_LE_ADD2 REAL_LE_ADDR REAL_LE_DIV REAL_LE_INV2
   REAL_LE_INV_EQ REAL_LE_LDIV_EQ REAL_LE_LMUL REAL_LE_LMUL_EQ REAL_LE_MUL
   REAL_LE_REFL REAL_LE_RMUL REAL_LE_TRANS REAL_LT_01 REAL_LT_DIV REAL_LT_IMP_LE
   REAL_LT_INV_EQ REAL_LT_LDIV_EQ REAL_LT_MIN REAL_LT_RDIV_EQ REAL_LT_TRANS
   REAL_MUL_ASSOC REAL_MUL_LID REAL_MUL_LZERO REAL_MUL_RID REAL_MUL_RZERO
   REAL_MUL_SYM REAL_OF_INT_CLAUSES REAL_OF_NUM_ADD REAL_OF_NUM_LE
   REAL_OF_NUM_LT REAL_OF_NUM_MUL REAL_OF_NUM_POW : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms3 where
  (REAL_PARTIAL_SUMS_LE_INFSUM REAL_POS REAL_POW_1 REAL_POW_2 REAL_POW_INV
   REAL_POW_LE REAL_POW_LE2 REAL_POW_LT REAL_SERIES_FINITE_SUPPORT
   REAL_SERIES_FROM REAL_SERIES_POS REAL_SUB_LE REAL_SUB_RDISTRIB REAL_SUB_REFL
   REAL_SUB_RZERO REAL_SUMMABLE REAL_SUMMABLE_COMPARISON
   REAL_SUMMABLE_FROM_ELSEWHERE_EQ REAL_SUMMABLE_SUB REAL_SUMMABLE_ZETA
   REAL_SUMS_COMPLEX REAL_SUMS_INFSUM REAL_SUMS_OFFSET RE_CX RIGHT_ADD_DISTRIB
   RIGHT_IMP_EXISTS_THM RING_0 RING_1 RING_ADD RING_ADD_LCANCEL
   RING_HOMOMORPHISM_0 RING_HOMOMORPHISM_ADD
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT RING_HOMOMORPHISM_MUL
   RING_HOMOMORPHISM_RING_OF_INT RING_HOMOMORPHISM_RING_OF_NUM
   RING_HOMOMORPHISM_SUM RING_IDEAL_CARRIER RING_IDEAL_IDEAL_GENERATED
   RING_IDEAL_IDEAL_POW RING_IDEAL_IMP_SUBSET
   RING_MONOMORPHISM_INTEGER_RING_OF_INT RING_MUL RING_OF_INT RING_OF_INTEGERS
   RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE RING_OF_INTEGERS_FINITE_QUOTIENT
   RING_OF_INTEGERS_FREE RING_OF_INTEGERS_FREE_BASIS_FIELD
   RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q RING_OF_INTEGERS_PRIME_IDEAL_ABOVE
   RING_OF_INTEGERS_SUBSET RING_OF_INT_IN_RING_OF_INTEGERS RING_OF_NUM RING_SUM
   RING_SUM_EQ RING_SUM_RING_OF_INTEGERS RPOW_ADD RPOW_LE2 RPOW_LE_1 RPOW_LT_1
   RPOW_MONO_LE RPOW_ONE RPOW_POS_LE RPOW_POS_LT RPOW_POW RPOW_ZERO
   SERIES_UNIQUE SKOLEM_THM SUBSET SUBSET_ANTISYM SUBSET_DIFF SUBSET_REFL SUB_0
   SUB_REFL SUMMABLE_COMPARISON SUMS_EQ SUMS_GP SUMS_INFSUM SUM_ABS_BOUND
   SUM_ADD SUM_ADD_NUMSEG SUM_ADD_SPLIT SUM_CLAUSES_NUMSEG SUM_CLAUSES_RIGHT
   SUM_CONST SUM_CONST_NUMSEG SUM_DIFFS SUM_EQ SUM_EQ_0_NUMSEG SUM_EQ_NUMSEG
   SUM_GROUP SUM_LE SUM_LE_NUMSEG SUM_LMUL SUM_NEG SUM_PARTIAL_PRE
   SUM_POS_LE_NUMSEG SUM_SUBSET_SIMPLE SUM_SUB_NUMSEG SUM_UNION
   TRIVIAL_LIMIT_ATREAL_RIGHT TRIVIAL_LIMIT_SEQUENTIALLY UNION_COMM
   UPPER_BOUND_FINITE_SET UPPER_BOUND_FINITE_SET_INT UPPER_BOUND_FINITE_SET_REAL
   VSUM_CONST VSUM_EQ VSUM_GROUP VSUM_IMAGE VSUM_NORM VSUM_SUB complex_div
   complex_embeddings complex_pow dist free_basis ideal_norm int_le number_field
   o_DEF o_THM prime_ideal proper_ideal real_abs real_div real_summable
   ring_divides ring_monomorphism sums : thm)
  deriving Inhabited

/-- What dedekind_zeta.ml uses from Session besides theorems. -/
structure DedekindZetaDeps where
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
  NORM_ARITH : term → ExceptT String IO thm
  SELECT_CONV : ioconv
  COMPLEX_RING : term → ExceptT String IO thm
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3

/-- RingTheory's `wPart` (copied verbatim).  `W(MP_TAC o PART_MATCH f th o g
    o snd)`: match `th`'s part `f` against the part `g` of the goal, and
    MP_TAC the instance. -/
def wPart [HolBase] (g : term → Except String term) (f : term → Except String term)
    (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (g gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)



/- ---------------------------------------------------------------------- -/
/- dedekind_zeta.ml phrases from line 140 to 490                          -/
/- ---------------------------------------------------------------------- -/

structure DedekindZeta01 where
  -- @@FIELDS
  DIRICHLET_SERIES_LINEAR_PARTIAL_SUMS : thm
  NUMBER_FIELD_IDEAL_BOX_COFACTOR : thm
  NUMBER_FIELD_IDEAL_COUNT_UPPER : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekindZeta01 [HolBase] (D : DedekindZetaDeps) :
    ExceptT String IO DedekindZeta01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_INT_ARITH_TAC, ASM_MESON_TAC,
        ASM_REAL_ARITH_TAC, INT_ARITH, INT_ARITH_TAC, MESON_TAC, REAL_ARITH,
        REAL_ARITH_TAC, SET_RULE, SET_TAC, TAUT, .. } := D
  let { ADD_CLAUSES, ADD_SUB, ARITH, CARD_CLAUSES, CARD_CROSS, CARD_EQ_0,
        CARD_IMAGE_INJ, CARD_SUBSET, CONVERGENT_REAL_BOUNDED_MONOTONE,
        DEDEKIND_IDEAL_PROD_CANCEL, DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES,
        DEDEKIND_RING_OF_INTEGERS, EQ_IMP_LE, ETA_AX, EVENTUALLY_SEQUENTIALLY,
        EVENTUALLY_TRUE, EXP_MONO_LE, EXP_ONE, FINITE_CROSS, FINITE_NUMSEG_LT,
        FORALL_IN_IMAGE, FORALL_PAIR_THM, FREE_BASIS_IDEAL_BOX_PRINCIPLE,
        FREE_BASIS_NORM_BOUND, FROM_INTER_NUMSEG, HAS_SIZE, HAS_SIZE_FUNSPACE,
        HAS_SIZE_NUMSEG, HAS_SIZE_NUMSEG_LT, IDEAL_GENERATED_EQ_0,
        IDEAL_GENERATED_MINIMAL, IDEAL_PROD_COMM, IDEAL_PROD_EQ_ZERO, INTEGER_RING,
        INTEGRAL_DOMAIN_RING_OF_INTEGERS, INT_ABS_POS, INT_LE_LMUL, INT_LE_LMUL_EQ,
        INT_LE_MUL, INT_LE_REFL, INT_LE_TRANS, INT_MUL_AC, INT_OF_NUM_LE,
        INT_OF_NUM_LT, INT_OF_NUM_MUL, INT_OF_NUM_OF_INT, INT_OF_NUM_POW, INT_POS,
        INT_POW_LE, INT_POW_MUL, IN_CROSS, IN_ELIM_THM, IN_NUMSEG, IN_UNIV, LE, .. } := D.core1
  let { LE_0, LE_MULT2, LE_MULT_LCANCEL, LE_REFL, LE_TRANS, LT_NZ, MEMBER_NOT_EMPTY,
        MONO_EXISTS, MULT_EXP, NOT_LT, NUMBER_FIELD_DEGREE_POS,
        NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM, NUMBER_FIELD_IDEAL_NORM_MUL_Q,
        NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_NORM_INTEGRAL_BASIS, NUM_ROOT_FLOOR, PAIR_EQ, REALLIM_CONST,
        REALLIM_LE, REALLIM_LMUL, REALLIM_SUB, REAL_ABS_LE, REAL_ABS_MUL, REAL_ABS_POS,
        REAL_ADD_LDISTRIB, REAL_BOUNDED_POS, REAL_INFSUM_UNIQUE,
        REAL_INFSUM_ZETA_BOUNDS, REAL_INV_1, REAL_INV_LE_1, REAL_LE_ADD2, REAL_LE_ADDR,
        REAL_LE_INV2, REAL_LE_INV_EQ, REAL_LE_LMUL, REAL_LE_MUL, REAL_LE_REFL,
        REAL_LE_RMUL, REAL_LE_TRANS, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_RID,
        REAL_MUL_RZERO, REAL_OF_NUM_LE, REAL_OF_NUM_LT, .. } := D.core2
  let { REAL_PARTIAL_SUMS_LE_INFSUM, REAL_POS, REAL_SERIES_FROM, REAL_SUB_LE,
        REAL_SUB_RZERO, REAL_SUMMABLE_ZETA, REAL_SUMS_INFSUM, RIGHT_IMP_EXISTS_THM,
        RING_0, RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IMP_SUBSET, RING_MONOMORPHISM_INTEGER_RING_OF_INT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS_FREE,
        RING_OF_INTEGERS_FREE_BASIS_FIELD, RING_SUM, RING_SUM_EQ, RPOW_LE2, RPOW_ONE,
        RPOW_POS_LE, RPOW_POS_LT, SKOLEM_THM, SUBSET, SUB_0, SUB_REFL, SUM_ADD_NUMSEG,
        SUM_CLAUSES_NUMSEG, SUM_CLAUSES_RIGHT, SUM_CONST_NUMSEG, SUM_DIFFS,
        SUM_EQ_NUMSEG, SUM_LE_NUMSEG, SUM_LMUL, SUM_NEG, SUM_PARTIAL_PRE,
        SUM_POS_LE_NUMSEG, TRIVIAL_LIMIT_SEQUENTIALLY, UPPER_BOUND_FINITE_SET_INT,
        free_basis, ideal_norm, number_field, real_div, real_summable,
        ring_monomorphism, .. } := D.core3
  -- @@SCOPE END

  let DIRICHLET_SERIES_LINEAR_PARTIAL_SUMS ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let v1 ← GSYM SUM_NEG
    let q2 ← q r"1 <= k ==> 0 < k"
    let r3 ← ARITH_RULE q2
    let q4 ← q r"k:num"
    let q5 ← q r"x:real = x' /\ y:real = --y' ==> x = z - y ==> x' = z + y'"
    let r6 ← REAL_ARITH q5
    let q7 ← q r"M:num"
    let q8 ← q r"1"
    let q9 ← q r"\k. sum(1..k) (a:num->real)"
    let q10 ← q r"f:num->real"
    let v11 ← ISPECL [q10, q9, q8, q7] SUM_PARTIAL_PRE
    let p12 ← prove r"!(a:num->real) (f:num->real) M.
          1 <= M
          ==> sum(1..M) (\m. a m * f m) =
              f(M + 1) * sum(1..M) a +
              sum(1..M) (\k. sum(1..k) a * (f k - f(k + 1)))" (REPEAT STRIP_TAC THEN MP_TAC v11 THEN ASM_REWRITE_TAC [SUB_REFL] THEN REWRITE_TAC [SUM_CLAUSES_NUMSEG, ARITH, REAL_MUL_RZERO, REAL_SUB_RZERO] THEN MATCH_MP_TAC r6 THEN CONJ_TAC THENL [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC q4 THEN STRIP_TAC THEN REWRITE_TAC [] THEN ASM_SIMP_TAC [SUM_CLAUSES_RIGHT, r3] THEN REAL_ARITH_TAC, REWRITE_TAC [v1] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN REWRITE_TAC [] THEN REAL_ARITH_TAC])
    let abel_lemma := p12
    let q13 ← q r"abs x = x:real"
    let q14 ← q r"abs(C * x:real)"
    let q15 ← q r"abs C * x:real"
    let p16 ← prove r"!C x Z. &0 <= x /\ x <= Z ==> C * x <= abs C * (Z:real)" (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC q15 THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC q14 THEN REWRITE_TAC [REAL_ABS_LE, REAL_ABS_MUL] THEN SUBGOAL_THEN q13 SUBST1_TAC THENL [ASM_REAL_ARITH_TAC, REWRITE_TAC [REAL_LE_REFL]], MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [REAL_ABS_POS]])
    let abs_lemma := p16
    let q17 ← q r"\M. C * sum(1..M) (f:num->real)"
    let q18 ← q r"\M. sum(1..M) (\m. (a:num->real) m * f m)"
    let q19 ← q r"sequentially"
    let v20 ← ISPEC q19 REALLIM_LE
    let q21 ← q r"M:num"
    let q22 ← q r"N0 + 1"
    let q23 ← q r"\M. sum(1..M) (\m. (a:num->real) m * f m)"
    let q24 ← q r"\M. c * sum(1..M) (f:num->real) - c * &N0"
    let q25 ← q r"sequentially"
    let v26 ← ISPEC q25 REALLIM_LE
    let q27 ← q r"((\m. (a:num->real) m * f m) real_sums l) (from 1)"
    let q28 ← q r"l:real"
    let q29 ← q r"1 <= SUC M"
    let r30 ← ARITH_RULE q29
    let q31 ← q r"M:num"
    let q32 ← q r"Z:real"
    let q33 ← q r"sum(1..M) (f:num->real)"
    let q34 ← q r"C:real"
    let v35 ← SPECL [q34, q33, q32] abs_lemma
    let q41 ← q r"M:num"
    let q47 ← q r"M:num"
    let q48 ← q r"&0 <= sum(1..M) (\m. (a:num->real) m * f m) /\
                    &0 <= sum(1..M) (f:num->real)"
    let q49 ← q r"M:num"
    let q50 ← q r"inv(s - &1)"
    let q51 ← q r"&0 <= x:real ==> &0 < x + &1"
    let r52 ← REAL_ARITH q51
    let q53 ← q r"abs C * Z + &1:real"
    let q54 ← q r"\M. sum(1..M) (\m. (a:num->real) m * f m)"
    let v55 ← ISPEC q54 CONVERGENT_REAL_BOUNDED_MONOTONE
    let q56 ← q r"M:num"
    let q57 ← q r"from 1"
    let q58 ← q r"f:num->real"
    let v59 ← ISPECL [q58, q57, q56] REAL_PARTIAL_SUMS_LE_INFSUM
    let q60 ← q r"M:num"
    let q61 ← q r"!M. sum(1..M) (f:num->real) <= Z"
    let v65 ← GSYM REAL_SUMS_INFSUM
    let q66 ← q r"c * n * (&1 - f) <= c * n <=> &0 <= c * n * f:real"
    let r67 ← REAL_ARITH q66
    let q68 ← q r"y <= e ==> x + y <= x + e:real"
    let r69 ← REAL_ARITH q68
    let q70 ← q r"~(N0 <= k:num)"
    let q71 ← q r"x <= z /\ &0 <= y ==> x <= y + z:real"
    let r72 ← REAL_ARITH q71
    let q73 ← q r"x <= y /\ &0 <= z ==> x <= y + z:real"
    let r74 ← REAL_ARITH q73
    let q75 ← q r"N0 <= k:num"
    let q76 ← q r"&0 <= (f:num->real) k - f(k + 1)"
    let q77 ← q r"k:num"
    let q78 ← q r"sum(1..M) (\k. sum(1..k) a * (f k - f(k + 1)) +
                              c * &N0 * (f k - (f:num->real)(k + 1)))"
    let v79 ← GSYM SUM_LMUL
    let q80 ← q r"c * x * y:real = x * c * y"
    let r81 ← REAL_ARITH q80
    let q82 ← q r"x <= x' /\ y <= y' + e ==> (x + y) - e <= x' + y':real"
    let r83 ← REAL_ARITH q82
    let q93 ← q r"M:num"
    let q94 ← q r"M:num"
    let q95 ← q r"f:num->real"
    let q96 ← q r"a:num->real"
    let v97 ← ISPECL [q96, q95, q94] abel_lemma
    let q98 ← q r"!M. 1 <= M /\ N0 <= M
        ==> c * sum(1..M) f - c * &N0 <= sum(1..M) (\m. (a:num->real) m * f m)"
    let q99 ← q r"k:num"
    let v100 ← GSYM SUM_LMUL
    let q101 ← q r"C * x * y:real = x * C * y"
    let r102 ← REAL_ARITH q101
    let q103 ← q r"~(M = 0) ==> 1 <= M"
    let r104 ← ARITH_RULE q103
    let q110 ← q r"M:num"
    let q111 ← q r"~(M = 0) ==> 1 <= M"
    let r112 ← ARITH_RULE q111
    let q113 ← q r"M:num"
    let q114 ← q r"f:num->real"
    let q115 ← q r"a:num->real"
    let v116 ← ISPECL [q115, q114, q113] abel_lemma
    let q117 ← q r"M = 0"
    let q118 ← q r"M:num"
    let q119 ← q r"!M. sum(1..M) (\m. (a:num->real) m * f m) <= C * sum(1..M) f"
    let q120 ← q r"M:num"
    let q121 ← q r"f:num->real"
    let q122 ← q r"\m:num. &1:real"
    let v123 ← ISPECL [q122, q121, q120] abel_lemma
    let q124 ← q r"!M. 1 <= M
        ==> sum(1..M) (f:num->real) =
            f(M + 1) * &M + sum(1..M) (\k. &k * (f k - f(k + 1)))"
    let q125 ← q r"(\m. (a:num->real) m * inv(&m rpow s)) = (\m. a m * f m)"
    let q126 ← q r"&1 rpow s = &1 /\ &1 rpow s <= x ==> &1 <= x"
    let r127 ← REAL_ARITH q126
    let q128 ← q r"m:num"
    let q129 ← q r"(!m. &0 <= (f:num->real) m) /\ (!m. 1 <= m ==> f(m + 1) <= f m) /\
    (!m. 1 <= m ==> f m <= &1) /\ f 1 = &1"
    let q130 ← q r"f = \m. inv(&m rpow s)"
    let q131 ← q r"Z = real_infsum (from 1) (\m. inv(&m rpow s))"
    let q132 ← q r"s:real"
    let q133 ← q r"1"
    let v134 ← SPECL [q133, q132] REAL_SUMMABLE_ZETA
    let q135 ← q r"s:real"
    let v136 ← SPEC q135 REAL_INFSUM_ZETA_BOUNDS
    prove
      r"!(a:num->real) C c N0 s.
          (!m. &0 <= a m) /\ &0 <= c /\
          (!N. sum(1..N) a <= C * &N) /\
          (!N. N0 <= N ==> c * &N <= sum(1..N) a) /\
          &1 < s
          ==> real_summable (from 1) (\m. a m / &m rpow s) /\
              c * real_infsum (from 1) (\m. inv(&m rpow s)) - c * &N0 <=
              real_infsum (from 1) (\m. a m / &m rpow s) /\
              real_infsum (from 1) (\m. a m / &m rpow s) <=
              C * real_infsum (from 1) (\m. inv(&m rpow s))"
      (REWRITE_TAC [real_div] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC v136 THEN MP_TAC v134 THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC q131 THEN REPEAT (DISCH_THEN STRIP_ASSUME_TAC) THEN ABBREV_TAC q130 THEN SUBGOAL_THEN q129 STRIP_ASSUME_TAC THENL [EXPAND_TAC "f" THEN SIMP_TAC [REAL_LE_INV_EQ, RPOW_POS_LE, REAL_POS, RPOW_ONE, REAL_INV_1] THEN CONJ_TAC THEN X_GEN_TAC q128 THEN DISCH_TAC THENL [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL [MATCH_MP_TAC RPOW_POS_LT THEN REWRITE_TAC [REAL_OF_NUM_LT] THEN ASM_ARITH_TAC, MATCH_MP_TAC RPOW_LE2 THEN REWRITE_TAC [REAL_POS, REAL_OF_NUM_LE] THEN CONJ_TAC THENL [ARITH_TAC, ASM_REAL_ARITH_TAC]], MATCH_MP_TAC REAL_INV_LE_1 THEN MATCH_MP_TAC r127 THEN CONJ_TAC THENL [REWRITE_TAC [RPOW_ONE], MATCH_MP_TAC RPOW_LE2] THEN REWRITE_TAC [REAL_POS, REAL_OF_NUM_LE] THEN CONJ_TAC THENL [ASM_ARITH_TAC, ASM_REAL_ARITH_TAC]], ALL_TAC] THEN SUBGOAL_THEN q125 SUBST1_TAC THENL [EXPAND_TAC "f" THEN REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q124 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC v123 THEN ASM_REWRITE_TAC [REAL_MUL_LID, SUM_CONST_NUMSEG, ADD_SUB, REAL_MUL_RID] THEN REWRITE_TAC [ETA_AX], ALL_TAC] THEN SUBGOAL_THEN q119 ASSUME_TAC THENL [X_GEN_TAC q118 THEN ASM_CASES_TAC q117 THENL [ASM_REWRITE_TAC [SUM_CLAUSES_NUMSEG, ARITH, REAL_MUL_RZERO, REAL_LE_REFL], ALL_TAC] THEN MP_TAC v116 THEN ASM_SIMP_TAC [r112] THEN DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q110) o (checkM (fun th => (do if ← (do let z105 ← (do let z106 ← (pure th); pure (concl z106)); pure (is_forall z105)) then (do let z107 ← (do pure (Prod.snd (← (do let z108 ← (do let z109 ← (pure th); pure (concl z109)); liftExcept (dest_forall z108))))); pure (is_imp z107)) else pure false))))) THEN ASM_SIMP_TAC [r104] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL [ONCE_REWRITE_TAC [r102] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [], REWRITE_TAC [v100] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC q99 THEN STRIP_TAC THEN REWRITE_TAC [REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC [REAL_SUB_LE]], ALL_TAC] THEN SUBGOAL_THEN q98 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC v97 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q93) o (checkM (fun th => (do if ← (do if ← (do let z84 ← (do let z85 ← (pure th); pure (concl z85)); pure (is_forall z84)) then (do let z86 ← (do pure (Prod.snd (← (do let z87 ← (do let z88 ← (pure th); pure (concl z88)); liftExcept (dest_forall z87))))); pure (is_imp z86)) else pure false) then (do let z89 ← (do let z90 ← (do pure (Prod.snd (← (do let z91 ← (do let z92 ← (pure th); pure (concl z92)); liftExcept (dest_forall z91))))); liftExcept (rand z90)); pure (is_eq z89)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC r83 THEN CONJ_TAC THENL [ONCE_REWRITE_TAC [r81] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC [], ALL_TAC] THEN REWRITE_TAC [v79] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC q78 THEN CONJ_TAC THENL [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC q77 THEN STRIP_TAC THEN REWRITE_TAC [] THEN SUBGOAL_THEN q76 ASSUME_TAC THENL [ASM_SIMP_TAC [REAL_SUB_LE], ALL_TAC] THEN ASM_CASES_TAC q75 THENL [MATCH_MP_TAC r74 THEN CONJ_TAC THENL [REWRITE_TAC [REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC [], MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC [REAL_LE_MUL, REAL_POS]], MATCH_MP_TAC r72 THEN CONJ_TAC THENL [REWRITE_TAC [REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [REAL_OF_NUM_LE] THEN UNDISCH_TAC q70 THEN ARITH_TAC, MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC []]], REWRITE_TAC [SUM_ADD_NUMSEG] THEN MATCH_MP_TAC r69 THEN REWRITE_TAC [SUM_LMUL] THEN ASM_SIMP_TAC [SUM_DIFFS] THEN REWRITE_TAC [r67] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC [REAL_LE_MUL, REAL_POS]], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o ((GEN_REWRITE_RULE id [v65]) o (checkM (fun th => (do let z64 ← (q r"real_summable (from 1) (f:num->real)"); let z63 ← (do let z62 ← (pure th); pure (concl z62)); pure (z63 == z64)))))) THEN ASM_REWRITE_TAC [REAL_SERIES_FROM] THEN DISCH_TAC THEN SUBGOAL_THEN q61 ASSUME_TAC THENL [X_GEN_TAC q60 THEN MP_TAC v59 THEN ASM_REWRITE_TAC [FROM_INTER_NUMSEG], ALL_TAC] THEN MP_TAC v55 THEN ANTS_TAC THENL [REWRITE_TAC [] THEN CONJ_TAC THENL [REWRITE_TAC [REAL_BOUNDED_POS, FORALL_IN_IMAGE, IN_UNIV] THEN EXISTS_TAC q53 THEN CONJ_TAC THENL [MATCH_MP_TAC r52 THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [REAL_ABS_POS] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC q50 THEN ASM_REWRITE_TAC [REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN X_GEN_TAC q49 THEN SUBGOAL_THEN q48 STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_SIMP_TAC [REAL_LE_MUL], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q47) o (checkM (fun th => (do if ← (do let z43 ← (do let z44 ← (pure th); pure (concl z44)); let z42 ← (q r"C:real"); pure (free_in z42 z43)) then (do let z45 ← (do let z46 ← (pure th); pure (concl z46)); pure (is_forall z45)) else pure false))))) THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q41) o (checkM (fun th => (do if ← (do let z37 ← (do let z38 ← (pure th); pure (concl z38)); let z36 ← (q r"Z:real"); pure (free_in z36 z37)) then (do let z39 ← (do let z40 ← (pure th); pure (concl z40)); pure (is_forall z39)) else pure false))))) THEN MP_TAC v35 THEN ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC, DISJ1_TAC THEN X_GEN_TAC q31 THEN REWRITE_TAC [SUM_CLAUSES_NUMSEG, r30] THEN ASM_SIMP_TAC [REAL_LE_ADDR, REAL_LE_MUL]], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_TAC q28) THEN SUBGOAL_THEN q27 ASSUME_TAC THENL [ASM_REWRITE_TAC [REAL_SERIES_FROM], ALL_TAC] THEN CONJ_TAC THENL [ASM_MESON_TAC [real_summable], ALL_TAC] THEN FIRST_ASSUM (SUBST1_TAC o (MATCH_MP REAL_INFSUM_UNIQUE)) THEN CONJ_TAC THENL [MATCH_MP_TAC v26 THEN EXISTS_TAC q24 THEN EXISTS_TAC q23 THEN ASM_REWRITE_TAC [TRIVIAL_LIMIT_SEQUENTIALLY, EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL [MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC [REALLIM_CONST] THEN MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC [], EXISTS_TAC q22 THEN X_GEN_TAC q21 THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC], MATCH_MP_TAC v20 THEN EXISTS_TAC q18 THEN EXISTS_TAC q17 THEN ASM_REWRITE_TAC [TRIVIAL_LIMIT_SEQUENTIALLY, EVENTUALLY_TRUE] THEN MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC []])

  let NUMBER_FIELD_IDEAL_BOX_COFACTOR ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r4 ← INT_ARITH (← q r"x <= y ==> y <= z ==> x:int <= z")
    let r11 ← TAUT (← q r"p /\ (q ==> r) ==> (p <=> q) ==> r")
    prove
      r"!k:A ring n w B j.
          number_field k /\
          free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
          (!i l m. i < n /\ l < n /\ m < n
                   ==> abs(mul_matrix (integer_ring,ring_of_integers k)
                             (ring_of_int k) n w (w i) m l)
                       <= B) /\
          ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
          ==> ?c t j'. t EXP n <= ideal_norm (ring_of_integers k) j /\
                       (!m. m < n ==> abs(c m) <= &t) /\
                       ring_ideal (ring_of_integers k) j' /\
                       ~(j' = {ring_0 k}) /\
                       &(ideal_norm (ring_of_integers k) j') <=
                       &(FACT n) * (&n * B) pow n /\
                       ideal_prod (ring_of_integers k) j j' =
                       ideal_generated (ring_of_integers k)
                        {ring_sum (ring_of_integers k) {m | m < n}
                          (\m. ring_mul k (ring_of_int k (c m)) (w m))}"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_char(k:A ring) = 0") ASSUME_TAC THENL [ASM_MESON_TAC [number_field], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(integer_ring,ring_of_integers k) (ring_of_int k:int->A)") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_DEGREE_POS) THEN ASM_SIMP_TAC [] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 <= (B:int)") ASSUME_TAC THENL [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC (← q r"abs(mul_matrix (integer_ring,ring_of_integers k)
                        (ring_of_int k) n w ((w:num->A) 0) 0 0)") THEN REWRITE_TAC [INT_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"FINITE(ring_carrier(quotient_ring (ring_of_integers k) (j:A->bool)))") ASSUME_TAC THENL [MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"n:num"), (← q r"ideal_norm (ring_of_integers k) (j:A->bool)")] NUM_ROOT_FLOOR) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:num") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"j:A->bool"), (← q r"t:num")] FREE_BASIS_IDEAL_BOX_PRINCIPLE) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->int") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"m0:num")) ASSUME_TAC))) THEN MAP_EVERY EXISTS_TAC [(← q r"c:num->int"), (← q r"t:num")] THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"a = ring_sum (ring_of_integers k) {m | m < n}
        (\m. ring_mul k (ring_of_int k ((c:num->int) m)) ((w:num->A) m))") THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [EXPAND_TAC "a" THEN REWRITE_TAC [RING_SUM], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(a:A = ring_0 k)") ASSUME_TAC THENL [DISCH_TAC THEN FIRST_ASSUM (fun z12 => tactic_of do pure (MP_TAC (← SPEC (← q r"c:num->int") (← (do let z13 ← (do pure (CONJUNCTS (← GEN_REWRITE_RULE id [free_basis] z12))); liftExcept (last z13)))))) THEN ASM_REWRITE_TAC [INTEGER_RING, IN_UNIV, RING_OF_INTEGERS] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers k:A ring)") ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_generated (ring_of_integers k) {a:A}"), (← q r"j:A->bool")] DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN MATCH_MP_TAC r11 THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM SET_TAC [], ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"j':A->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"~(j':A->bool = {ring_0 k})") ASSUME_TAC THENL [DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool"), (← q r"j':A->bool")] IDEAL_PROD_EQ_ZERO) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_RING_OF_INTEGERS, NUMBER_FIELD_IMP_FIELD, RING_OF_INTEGERS, IDEAL_GENERATED_EQ_0] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"a:A")] IDEAL_GENERATED_EQ_0) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ASM_REWRITE_TAC []] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"j:A->bool"), (← q r"j':A->bool")] NUMBER_FIELD_IDEAL_NORM_MUL_Q) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A")] NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"z:int") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"a:A")] NUMBER_FIELD_NORM_INTEGRAL_BASIS) THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MP_TAC o (CONJUNCT2 o ((REWRITE_RULE [ring_monomorphism]) o (GEN_REWRITE_RULE id [(← GSYM RING_MONOMORPHISM_INTEGER_RING_OF_INT)])))) THEN REWRITE_TAC [INTEGER_RING, IN_UNIV] THEN DISCH_THEN (fun th => DISCH_THEN (SUBST_ALL_TAC o (MATCH_MP th))) THEN SUBGOAL_THEN (← q r"~(ideal_norm (ring_of_integers k) (j:A->bool) = 0)") ASSUME_TAC THENL [ASM_SIMP_TAC [ideal_norm, CARD_EQ_0, (← GSYM MEMBER_NOT_EMPTY)] THEN MESON_TAC [RING_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"B:int"), (← q r"c:num->int"), (← q r"t:num")] FREE_BASIS_NORM_BOUND) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"&(ideal_norm (ring_of_integers k) (j':A->bool)):int"), (← q r"(&(FACT n) * (&n * B) pow n):int"), (← q r"&(ideal_norm (ring_of_integers k) (j:A->bool)):int")] INT_LE_LMUL_EQ) THEN ASM_REWRITE_TAC [INT_OF_NUM_LT, LT_NZ] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [INT_OF_NUM_MUL] THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); pure (is_eq z5)) then (do let z10 ← (q r"&(ideal_norm (ring_of_integers k) j *        ideal_norm (ring_of_integers k) (j':A->bool)):int"); let z9 ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); liftExcept (lhand z7)); pure (z9 == z10)) else pure false)))) THEN FIRST_X_ASSUM (MATCH_MP_TAC o ((MATCH_MP r4) o (checkM (fun th => (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); let z1 ← (q r"t:num"); pure (free_in z1 z2)))))) THEN SUBGOAL_THEN (← q r"&(FACT n) * ((&n * B) * &t) pow n =
      (&(FACT n) * (&n * B) pow n) * &(t EXP n):int") SUBST1_TAC THENL [REWRITE_TAC [INT_POW_MUL, (← GSYM INT_OF_NUM_POW)] THEN INT_ARITH_TAC, ALL_TAC] THEN MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC (← q r"(&(FACT n) * (&n * B) pow n) *
                &(ideal_norm (ring_of_integers k) (j:A->bool)):int") THEN CONJ_TAC THENL [MATCH_MP_TAC INT_LE_LMUL THEN ASM_SIMP_TAC [INT_POW_LE, INT_LE_MUL, INT_POS, INT_OF_NUM_LE], REWRITE_TAC [INT_MUL_AC, INT_LE_REFL]])

  let NUMBER_FIELD_IDEAL_COUNT_UPPER ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"(a * b) * c:num = (a * c) * b")
    let r18 ← ARITH_RULE (← q r"tm < 1 <=> tm = 0")
    let r19 ← SET_RULE (← q r"{x:A->bool | P x} = {} <=> !x. ~P x")
    prove
      r"!k:A ring.
          number_field k
          ==> ?C. !N. CARD {j | ring_ideal (ring_of_integers k) j /\
                                ~(j = {ring_0 k}) /\
                                ideal_norm (ring_of_integers k) j <= N}
                      <= C * N"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"w:num->A")) o (MATCH_MP RING_OF_INTEGERS_FREE)) THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)") THEN MP_TAC (← ISPECL [(← q r"\p. abs(mul_matrix (integer_ring,ring_of_integers k)
                 (ring_of_int k) n w ((w:num->A)(FST p)) (SND(SND p))
                 (FST(SND p)))"), (← q r"{i:num | i < n} CROSS ({l:num | l < n} CROSS {m:num | m < n})")] UPPER_BOUND_FINITE_SET_INT) THEN SIMP_TAC [FINITE_CROSS, FINITE_NUMSEG_LT] THEN REWRITE_TAC [FORALL_PAIR_THM, IN_CROSS, IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"B:int")) THEN SUBGOAL_THEN (← q r"1 <= n") ASSUME_TAC THENL [EXPAND_TAC "n" THEN ASM_SIMP_TAC [NUMBER_FIELD_DEGREE_POS], ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 <= (B:int)") ASSUME_TAC THENL [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC (← q r"abs(mul_matrix (integer_ring,ring_of_integers k)
                        (ring_of_int k) n w ((w:num->A) 0) 0 0)") THEN REWRITE_TAC [INT_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN ABBREV_TAC (← q r"M0 = num_of_int(&(FACT n) * (&n * B) pow n)") THEN SUBGOAL_THEN (← q r"(&M0:int) = &(FACT n) * (&n * B) pow n") ASSUME_TAC THENL [EXPAND_TAC "M0" THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_SIMP_TAC [INT_LE_MUL, INT_POW_LE, INT_POS], ALL_TAC] THEN ABBREV_TAC (← q r"Sm = {j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
                ideal_norm (ring_of_integers k) (j:A->bool) <= M0}") THEN SUBGOAL_THEN (← q r"FINITE(Sm:(A->bool)->bool)") ASSUME_TAC THENL [EXPAND_TAC "Sm" THEN ASM_SIMP_TAC [NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM], ALL_TAC] THEN EXISTS_TAC (← q r"3 EXP n * CARD(Sm:(A->bool)->bool)") THEN X_GEN_TAC (← q r"N:num") THEN ABBREV_TAC (← q r"S = {j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
               ideal_norm (ring_of_integers k) (j:A->bool) <= N}") THEN SUBGOAL_THEN (← q r"FINITE(S:(A->bool)->bool)") ASSUME_TAC THENL [EXPAND_TAC "S" THEN ASM_SIMP_TAC [NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM], ALL_TAC] THEN ASM_CASES_TAC (← q r"N = 0") THENL [SUBGOAL_THEN (← q r"S:(A->bool)->bool = {}") SUBST1_TAC THENL [ALL_TAC, REWRITE_TAC [CARD_CLAUSES, LE_0]] THEN EXPAND_TAC "S" THEN REWRITE_TAC [r19] THEN X_GEN_TAC (← q r"j:A->bool") THEN ASM_REWRITE_TAC [LE] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"j:A->bool")] RING_OF_INTEGERS_FINITE_QUOTIENT) THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"ideal_norm (ring_of_integers k) (j:A->bool) = 0") THEN REWRITE_TAC [ideal_norm] THEN REPEAT DISCH_TAC THEN UNDISCH_TAC (← q r"CARD(ring_carrier(quotient_ring (ring_of_integers k)
                    (j:A->bool))) = 0") THEN ASM_SIMP_TAC [CARD_EQ_0, (← GSYM MEMBER_NOT_EMPTY)] THEN MESON_TAC [RING_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"n:num"), (← q r"N:num")] NUM_ROOT_FLOOR) THEN ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"tm:num") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"1 <= tm") ASSUME_TAC THENL [REWRITE_TAC [(← GSYM NOT_LT), r18] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"N < (tm + 1) EXP n") THEN ASM_REWRITE_TAC [ADD_CLAUSES, EXP_ONE] THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"!j. j IN S
          ==> ?c j'. (!m. m < n ==> abs(c m) <= &tm) /\ j' IN Sm /\
                     ideal_prod (ring_of_integers k) j j' =
                     ideal_generated (ring_of_integers k)
                      {ring_sum (ring_of_integers k) {m | m < n}
                        (\m. ring_mul k (ring_of_int k (c m)) ((w:num->A) m))}") MP_TAC THENL [X_GEN_TAC (← q r"j:A->bool") THEN EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"B:int"), (← q r"j:A->bool")] NUMBER_FIELD_IDEAL_BOX_COFACTOR) THEN ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->int") (X_CHOOSE_THEN (← q r"t:num") (X_CHOOSE_THEN (← q r"j':A->bool") STRIP_ASSUME_TAC))) THEN MAP_EVERY EXISTS_TAC [(← q r"c:num->int"), (← q r"j':A->bool")] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC (← q r"&t:int") THEN ASM_SIMP_TAC [INT_OF_NUM_LE] THEN REWRITE_TAC [(← GSYM NOT_LT)] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(tm + 1) EXP n <= t EXP n") MP_TAC THENL [REWRITE_TAC [EXP_MONO_LE] THEN ASM_ARITH_TAC, ASM_ARITH_TAC], EXPAND_TAC "Sm" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [(← GSYM INT_OF_NUM_LE)]], ALL_TAC] THEN REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"cf:(A->bool)->num->int") (X_CHOOSE_TAC (← q r"jf:(A->bool)->(A->bool)"))) THEN ABBREV_TAC (← q r"Bx = {f:num->num | (!m. m IN {m | m < n} ==> f m IN 0..2 * tm) /\
                         (!m. ~(m IN {m | m < n}) ==> f m = 0)}") THEN SUBGOAL_THEN (← q r"(Bx:(num->num)->bool) HAS_SIZE (2 * tm + 1) EXP n") ASSUME_TAC THENL [EXPAND_TAC "Bx" THEN MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN REWRITE_TAC [HAS_SIZE_NUMSEG_LT] THEN MP_TAC (← SPECL [(← q r"0"), (← q r"2 * tm")] HAS_SIZE_NUMSEG) THEN REWRITE_TAC [SUB_0], ALL_TAC] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"CARD((Bx:(num->num)->bool) CROSS (Sm:(A->bool)->bool))") THEN CONJ_TAC THENL [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"CARD(IMAGE (\j:A->bool. (\m. if m < n
                       then num_of_int((cf:(A->bool)->num->int) j m + &tm)
                       else 0),
                      (jf:(A->bool)->(A->bool)) j) S)") THEN CONJ_TAC THENL [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC [PAIR_EQ] THEN MAP_EVERY X_GEN_TAC [(← q r"j1:A->bool"), (← q r"j2:A->bool")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!m. m < n ==> (cf:(A->bool)->num->int) j1 m = cf j2 m") ASSUME_TAC THENL [X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((← do let c := (← q r"m:num"); pure (fun th => AP_THM th c)) o (checkM (fun th => (do if ← (do let z13 ← (do let z14 ← (pure th); pure (concl z14)); pure (is_eq z13)) then (do let z15 ← (do let z16 ← (do let z17 ← (pure th); pure (concl z17)); liftExcept (lhand z16)); pure (is_abs z15)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"int_of_num"))) THEN FIRST_X_ASSUM (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"j1:A->bool") th) THEN MP_TAC (← SPEC (← q r"j2:A->bool") th))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"m:num")) o CONJUNCT1)) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"m:num")) o CONJUNCT1)) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPEC (← q r"(cf:(A->bool)->num->int) j1 m + &tm") INT_OF_NUM_OF_INT) THEN MP_TAC (← ISPEC (← q r"(cf:(A->bool)->num->int) j2 m + &tm") INT_OF_NUM_OF_INT) THEN REPEAT (ANTS_TAC THENL [ASM_INT_ARITH_TAC, DISCH_THEN SUBST1_TAC]) THEN INT_ARITH_TAC, ALL_TAC] THEN FIRST_X_ASSUM (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"j1:A->bool") th) THEN MP_TAC (← SPEC (← q r"j2:A->bool") th))) THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"(jf:(A->bool)->(A->bool)) j2")] DEDEKIND_IDEAL_PROD_CANCEL) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN UNDISCH_TAC (← q r"(jf:(A->bool)->(A->bool)) j2 IN Sm") THEN EXPAND_TAC "Sm" THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS] THEN UNDISCH_TAC (← q r"(j1:A->bool) IN S") THEN UNDISCH_TAC (← q r"(j2:A->bool) IN S") THEN EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"(jf:(A->bool)->(A->bool)) j2"), (← q r"j1:A->bool")] IDEAL_PROD_COMM) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"(jf:(A->bool)->(A->bool)) j2"), (← q r"j2:A->bool")] IDEAL_PROD_COMM) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC [] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM], MATCH_MP_TAC CARD_SUBSET THEN ASM_SIMP_TAC [FINITE_CROSS, HAS_SIZE] THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_CROSS] THEN X_GEN_TAC (← q r"j:A->bool") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"j:A->bool")) o (checkM (fun th => (do if ← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); pure (is_forall z8)) then (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); let z10 ← (q r"jf:(A->bool)->(A->bool)"); pure (free_in z10 z11)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "Bx" THEN REWRITE_TAC [IN_ELIM_THM, IN_NUMSEG, LE_0] THEN SIMP_TAC [] THEN X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"m:num"))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN REWRITE_TAC [(← GSYM INT_OF_NUM_LE)] THEN MP_TAC (← ISPEC (← q r"(cf:(A->bool)->num->int) j m + &tm") INT_OF_NUM_OF_INT) THEN ANTS_TAC THENL [ASM_INT_ARITH_TAC, DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [(← GSYM INT_OF_NUM_MUL)] THEN ASM_INT_ARITH_TAC, ASM_MESON_TAC [FINITE_CROSS, HAS_SIZE]]], ALL_TAC] THEN FIRST_X_ASSUM (STRIP_ASSUME_TAC o ((GEN_REWRITE_RULE id [HAS_SIZE]) o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_comb z2)) then (do let z7 ← (q r"(2 * tm + 1) EXP n"); let z6 ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (rand z4)); pure (z6 == z7)) else pure false))))) THEN ASM_SIMP_TAC [CARD_CROSS] THEN ONCE_REWRITE_TAC [r1] THEN MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC [LE_REFL] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"(3 * tm) EXP n") THEN CONJ_TAC THENL [REWRITE_TAC [EXP_MONO_LE] THEN ASM_ARITH_TAC, REWRITE_TAC [MULT_EXP] THEN ASM_SIMP_TAC [LE_MULT_LCANCEL]])

  -- @@RETURN BEGIN
  return { DIRICHLET_SERIES_LINEAR_PARTIAL_SUMS, NUMBER_FIELD_IDEAL_BOX_COFACTOR,
           NUMBER_FIELD_IDEAL_COUNT_UPPER }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- dedekind_zeta.ml phrases from line 694 to 1379                         -/
/- ---------------------------------------------------------------------- -/

structure DedekindZeta02 where
  -- @@FIELDS
  NUMBER_FIELD_PRINCIPAL_IDEAL_FAMILY : thm
  NUMBER_FIELD_IDEAL_COUNT_LOWER : thm
  NUMBER_FIELD_IDEAL_COUNT_BOUNDS : thm
  SUM_GROUP_CARD : thm
  VSUM_GROUP_CARD : thm
  NUMBER_FIELD_IDEAL_SUM_BY_NORM : thm
  dedekind_zeta : thm
  NUMBER_FIELD_IDEAL_COUNT_SUM : thm
  NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE : thm
  DEDEKIND_ZETA_CONVERGES : thm
  DEDEKIND_ZETA_REAL : thm
  DEDEKIND_ZETA_REAL_INFSUM : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekindZeta02 [HolBase] (D : DedekindZetaDeps) (BDedekindZeta01 : DedekindZeta01) :
    ExceptT String IO DedekindZeta02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC,
        COMPLEX_RING, NORM_ARITH, REAL_ARITH, REAL_ARITH_TAC, SELECT_CONV, SET_TAC,
        TAUT, new_definition, .. } := D
  let { CARD_CLAUSES, CARD_CROSS, CARD_EQ_0, CARD_IMAGE_INJ, CARD_SUBSET, COMPLEX_CMUL,
        COMPLEX_EMBEDDINGS_HAS_SIZE, COMPLEX_NORM_0, COMPLEX_NORM_CX, COMPLEX_NORM_DIV,
        COMPLEX_NORM_MUL, COMPLEX_RING_CLAUSES, COMPLEX_RING_OF_INT,
        COMPLEX_RING_OF_NUM, COMPLEX_RING_SUM, CONJ_ASSOC, CX_DIV, CX_RPOW, DIVISION,
        DIV_MUL_LE, EQ_IMP_LE, EQ_TRANS, EXP_MONO_LE, EXTENSION, FIELD_NONTRIVIAL,
        FINITE_COMPLEX_EMBEDDINGS, FINITE_CROSS, FINITE_NUMSEG_LT, FINITE_RESTRICT,
        FINITE_SUBSET, FORALL_IN_IMAGE, FREE_BASIS_INTEGER_RING_LINCOMB,
        FREE_BASIS_IN_CARRIER, FUN_EQ_THM, GE, HAS_SIZE, HAS_SIZE_CARD,
        HAS_SIZE_FUNSPACE, HAS_SIZE_INT_ABS_LE, HAS_SIZE_NUMSEG_LT,
        IDEAL_GENERATED_EQ_0, IDEAL_NORM_CARRIER, IDEAL_NORM_POS, INT_OF_NUM_LE,
        IN_CROSS, IN_ELIM_THM, IN_FROM, IN_IDEAL_GENERATED_SELF,
        IN_IDEAL_GENERATED_SING_EQ, IN_NUMSEG, IN_SING, LEFT_ADD_DISTRIB, .. } := D.core1
  let { LE_0, LE_1, LE_MULT2, LE_MULT_LCANCEL, LE_MULT_RCANCEL, LE_REFL, LE_TRANS,
        LT_IMP_LE, MEMBER_NOT_EMPTY, MULT_AC, MULT_ASSOC, MULT_CLAUSES, MULT_EXP,
        MULT_SYM, NORM_CPOW, NORM_POS_LE, NOT_LT, NUMBER_FIELD_DEGREE_POS,
        NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM,
        NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS, NUMBER_FIELD_IMP_FIELD,
        NUM_ROOT_FLOOR, PAIR_EQ, PRODUCT_CONST, PRODUCT_LE, REAL_ABS_NUM,
        REAL_ARCH_SIMPLE, REAL_CX, REAL_INFSUM_UNIQUE, REAL_LE_LMUL, REAL_LE_LMUL_EQ,
        REAL_LE_REFL, REAL_LE_RMUL, REAL_LE_TRANS, REAL_MUL_LZERO, REAL_MUL_RID,
        REAL_OF_INT_CLAUSES, REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_OF_NUM_MUL,
        REAL_OF_NUM_POW, .. } := D.core2
  let { REAL_POS, REAL_POW_LE2, REAL_SUMMABLE, REAL_SUMS_COMPLEX, REAL_SUMS_INFSUM,
        RE_CX, RIGHT_ADD_DISTRIB, RIGHT_IMP_EXISTS_THM, RING_1, RING_ADD,
        RING_ADD_LCANCEL, RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_ADD,
        RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_RING_OF_INT,
        RING_HOMOMORPHISM_RING_OF_NUM, RING_HOMOMORPHISM_SUM, RING_IDEAL_CARRIER,
        RING_IDEAL_IDEAL_GENERATED, RING_MUL, RING_OF_INT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE, RING_OF_INTEGERS_FINITE_QUOTIENT,
        RING_OF_INTEGERS_FREE, RING_OF_INTEGERS_FREE_BASIS_FIELD,
        RING_OF_INTEGERS_SUBSET, RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_NUM,
        RING_SUM_RING_OF_INTEGERS, SERIES_UNIQUE, SKOLEM_THM, SUBSET,
        SUMMABLE_COMPARISON, SUMS_EQ, SUMS_INFSUM, SUM_CONST, SUM_EQ, SUM_EQ_NUMSEG,
        SUM_GROUP, SUM_LE, SUM_LMUL, SUM_POS_LE_NUMSEG, UPPER_BOUND_FINITE_SET_REAL,
        VSUM_CONST, VSUM_EQ, VSUM_GROUP, VSUM_NORM, complex_embeddings, int_le, o_THM,
        ring_divides, .. } := D.core3
  let { DIRICHLET_SERIES_LINEAR_PARTIAL_SUMS, NUMBER_FIELD_IDEAL_COUNT_UPPER, .. } := BDedekindZeta01
  -- @@SCOPE END

  let NUMBER_FIELD_PRINCIPAL_IDEAL_FAMILY ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r39 ← REAL_ARITH (← q r"&1 <= mm ==> &0 < mm / &2")
    let r77 ← REAL_ARITH (← q r"y <= z ==> x <= y ==> x <= z:real")
    let r78 ← COMPLEX_RING (← q r"(a + b) - a:complex = b")
    prove
      r"!k:A ring n w Bn m.
          number_field k /\
          free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
          (!g. g IN complex_embeddings k
               ==> sum {i | i < n} (\i. norm(g(w i))) <= &Bn) /\
          1 <= m
          ==> (2 * (m DIV (2 * Bn)) + 1) EXP n <=
              CARD {x | x IN ring_carrier(ring_of_integers k) /\
                        !g. g IN complex_embeddings k ==> norm(g x) <= &3} *
              CARD {j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
                        ideal_norm (ring_of_integers k) j <= (2 * m) EXP n}"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o (SYM o CONJUNCT1)) THEN MP_TAC (← ISPEC (← q r"k:A ring") COMPLEX_EMBEDDINGS_HAS_SIZE) THEN ASM_REWRITE_TAC [HAS_SIZE] THEN STRIP_TAC THEN ABBREV_TAC (← q r"t = m DIV (2 * Bn)") THEN SUBGOAL_THEN (← q r"2 * t * Bn <= m") ASSUME_TAC THENL [EXPAND_TAC "t" THEN MP_TAC (← SPECL [(← q r"m:num"), (← q r"2 * Bn")] DIV_MUL_LE) THEN REWRITE_TAC [MULT_AC], ALL_TAC] THEN ABBREV_TAC (← q r"U = {x | x IN ring_carrier(ring_of_integers k) /\
               !g. g IN complex_embeddings k ==> norm((g:A->complex) x)
                 <= &3}") THEN ABBREV_TAC (← q r"S = {j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
               ideal_norm (ring_of_integers k) (j:A->bool) <= (2 * m) EXP n}") THEN SUBGOAL_THEN (← q r"FINITE(U:A->bool) /\ FINITE(S:(A->bool)->bool)") STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["U", "S"] THEN ASM_SIMP_TAC [RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE, NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i < n ==> (w:num->A) i IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [FIRST_ASSUM (ACCEPT_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)), ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_carrier(ring_of_integers k) SUBSET ring_carrier(k:A ring)") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBSET], ALL_TAC] THEN ABBREV_TAC (← q r"psi = \z:num->int. ring_sum (ring_of_integers k) {i | i < n}
              (\i. ring_mul k (ring_of_int k (z i)) ((w:num->A) i))") THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"psi:(num->int)->A")] FREE_BASIS_INTEGER_RING_LINCOMB) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN EXPAND_TAC "psi" THEN REWRITE_TAC [], STRIP_TAC] THEN SUBGOAL_THEN (← q r"!(z:num->int) g. g IN complex_embeddings k
            ==> (g:A->complex)(psi z) =
                vsum {i:num | i < n} (\i. Cx(real_of_int(z i)) * g(w i))") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o ((REWRITE_RULE [complex_embeddings, IN_ELIM_THM]) o (checkM (fun th => (do let z84 ← (q r"(g:A->complex) IN complex_embeddings k"); let z83 ← (do let z82 ← (pure th); pure (concl z82)); pure (z83 == z84))))))) THEN DISCH_TAC THEN EXPAND_TAC "psi" THEN REWRITE_TAC [] THEN wPart (rand o lhand) (lhand o rand) RING_SUM_RING_OF_INTEGERS THEN ANTS_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_int k ((z:num->int) i):A"), (← q r"(w:num->A) i")] RING_MUL) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, RING_OF_INT_IN_RING_OF_INTEGERS], DISCH_THEN SUBST1_TAC] THEN SUBGOAL_THEN (← q r"!i. i < n ==> ring_mul k (ring_of_int k ((z:num->int) i))
                                   ((w:num->A) i) IN ring_carrier k /\
                        (w:num->A) i IN ring_carrier k") ASSUME_TAC THENL [REPEAT STRIP_TAC THENL [MATCH_MP_TAC RING_MUL THEN REWRITE_TAC [RING_OF_INT], ALL_TAC] THEN ASM SET_TAC [], ALL_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (wPart lhand (lhand o rand) (← MATCH_MP RING_HOMOMORPHISM_SUM th))) THEN ANTS_TAC THENL [REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN SIMP_TAC [COMPLEX_RING_SUM, FINITE_NUMSEG_LT] THEN MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC [IN_ELIM_THM, o_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (wPart lhand (lhand o rand) (← MATCH_MP RING_HOMOMORPHISM_MUL th))) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_OF_INT], DISCH_THEN SUBST1_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th)])) THEN REWRITE_TAC [COMPLEX_RING_OF_INT, COMPLEX_RING_CLAUSES], ALL_TAC] THEN ABBREV_TAC (← q r"Bx = {z:num->int |
            (!i. i IN {i:num | i < n} ==> z i IN {x:int | abs x <= &t}) /\
                         (!i. ~(i IN {i:num | i < n}) ==> z i = &0)}") THEN SUBGOAL_THEN (← q r"(Bx:(num->int)->bool) HAS_SIZE (2 * t + 1) EXP n") ASSUME_TAC THENL [EXPAND_TAC "Bx" THEN MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN REWRITE_TAC [HAS_SIZE_NUMSEG_LT, HAS_SIZE_INT_ABS_LE], ALL_TAC] THEN ABBREV_TAC (← q r"elt = \z:num->int. ring_add k (ring_of_num k m) (psi z:A)") THEN SUBGOAL_THEN (← q r"!z. (elt:(num->int)->A) z IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [GEN_TAC THEN EXPAND_TAC "elt" THEN REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_num k m:A"), (← q r"psi(z:num->int):A")] RING_ADD) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"m:num")] RING_OF_NUM) THEN REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"!z g. z IN Bx /\ g IN complex_embeddings k
            ==> norm((g:A->complex)((elt:(num->int)->A) z) - Cx(&m)) <= &m / &2") ASSUME_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"z:num->int"), (← q r"g:A->complex")] THEN STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o ((REWRITE_RULE [complex_embeddings, IN_ELIM_THM]) o (checkM (fun th => (do let z81 ← (q r"(g:A->complex) IN complex_embeddings k"); let z80 ← (do let z79 ← (pure th); pure (concl z79)); pure (z80 == z81))))))) THEN DISCH_TAC THEN EXPAND_TAC "elt" THEN REWRITE_TAC [] THEN FIRST_ASSUM (fun th => tactic_of do pure (wPart (lhand o rand o lhand) (lhand o rand) (← MATCH_MP RING_HOMOMORPHISM_ADD th))) THEN ANTS_TAC THENL [REWRITE_TAC [RING_OF_NUM] THEN ASM SET_TAC [], DISCH_THEN SUBST1_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th)])) THEN ASM_SIMP_TAC [COMPLEX_RING_OF_NUM, COMPLEX_RING_CLAUSES] THEN REWRITE_TAC [COMPLEX_RING_OF_NUM, COMPLEX_RING_CLAUSES, r78] THEN wPart lhand (lhand o rand) VSUM_NORM THEN REWRITE_TAC [FINITE_NUMSEG_LT] THEN MATCH_MP_TAC r77 THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"sum {i:num | i < n} (\i. &t * norm((g:A->complex)(w i)))") THEN CONJ_TAC THENL [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN REWRITE_TAC [COMPLEX_NORM_MUL, COMPLEX_NORM_CX] THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [NORM_POS_LE] THEN UNDISCH_TAC (← q r"(z:num->int) IN Bx") THEN EXPAND_TAC "Bx" THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"i:num")) o CONJUNCT1)) THEN ASM_REWRITE_TAC [(← GSYM REAL_OF_INT_CLAUSES), (← GSYM INT_OF_NUM_LE)] THEN REWRITE_TAC [REAL_OF_INT_CLAUSES, (← GSYM int_le)], REWRITE_TAC [SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"(&t * &Bn):real") THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_POS] THEN ASM_SIMP_TAC [], UNDISCH_TAC (← q r"2 * t * Bn <= m") THEN REWRITE_TAC [(← GSYM REAL_OF_NUM_LE), (← GSYM REAL_OF_NUM_MUL)] THEN REAL_ARITH_TAC]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!z g. z IN Bx /\ g IN complex_embeddings k
            ==> &m / &2 <= norm((g:A->complex)((elt:(num->int)->A) z)) /\
                norm(g(elt z)) <= &3 * &m / &2") ASSUME_TAC THENL [REPEAT GEN_TAC THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← MATCH_MP (← ASSUME (← q r"!z g. z IN Bx /\ g IN complex_embeddings k
                ==> norm((g:A->complex)((elt:(num->int)->A) z) - Cx(&m)) <=
                    &m / &2")) th))) THEN MP_TAC (← SPEC (← q r"&m:real") COMPLEX_NORM_CX) THEN REWRITE_TAC [REAL_ABS_NUM] THEN CONV_TAC NORM_ARITH, ALL_TAC] THEN SUBGOAL_THEN (← q r"~(complex_embeddings(k:A ring) = {})") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"CARD(complex_embeddings(k:A ring)) = n") THEN ASM_REWRITE_TAC [CARD_CLAUSES] THEN MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_DEGREE_POS) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"!z. z IN Bx ==> ~((elt:(num->int)->A) z = ring_0 k)") ASSUME_TAC THENL [X_GEN_TAC (← q r"z:num->int") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((GEN_REWRITE_RULE id [(← GSYM MEMBER_NOT_EMPTY)]) o (checkM (fun th => (do let z76 ← (q r"~(complex_embeddings(k:A ring) = {})"); let z75 ← (do let z74 ← (pure th); pure (concl z74)); pure (z75 == z76)))))) THEN DISCH_THEN (X_CHOOSE_TAC (← q r"g:A->complex")) THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o ((REWRITE_RULE [complex_embeddings, IN_ELIM_THM]) o (checkM (fun th => (do let z73 ← (q r"(g:A->complex) IN complex_embeddings k"); let z72 ← (do let z71 ← (pure th); pure (concl z71)); pure (z72 == z73))))))) THEN DISCH_THEN (MP_TAC o (MATCH_MP RING_HOMOMORPHISM_0)) THEN REWRITE_TAC [COMPLEX_RING_CLAUSES] THEN DISCH_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPECL [(← q r"z:num->int"), (← q r"g:A->complex")]) o (checkM (fun th => (do let z69 ← (do let z70 ← (pure th); pure (concl z70)); let z68 ← (q r"&3 * &m / &2"); pure (free_in z68 z69)))))) THEN ASM_REWRITE_TAC [COMPLEX_NORM_0] THEN UNDISCH_TAC (← q r"1 <= m") THEN REWRITE_TAC [(← GSYM REAL_OF_NUM_LE)] THEN REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"!z. z IN Bx
          ==> ideal_generated (ring_of_integers k) {(elt:(num->int)->A) z} IN S") ASSUME_TAC THENL [X_GEN_TAC (← q r"z:num->int") THEN DISCH_TAC THEN EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM, RING_IDEAL_IDEAL_GENERATED] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"(elt:(num->int)->A) z")] IDEAL_GENERATED_EQ_0) THEN ASM_SIMP_TAC [RING_OF_INTEGERS], ALL_TAC] THEN REWRITE_TAC [(← GSYM REAL_OF_NUM_LE)] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"(elt:(num->int)->A) z")] NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS) THEN ASM_SIMP_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"product (complex_embeddings(k:A ring)) (\g. &3 * &m / &2)") THEN CONJ_TAC THENL [MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC [NORM_POS_LE], ASM_SIMP_TAC [PRODUCT_CONST, (← GSYM REAL_OF_NUM_POW)] THEN MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC [(← GSYM REAL_OF_NUM_MUL)] THEN REAL_ARITH_TAC], ALL_TAC] THEN SUBGOAL_THEN (← q r"!z z'. z IN Bx /\ z' IN Bx /\ (elt:(num->int)->A) z = elt z' ==> z = z'") ASSUME_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"z:num->int"), (← q r"z':num->int")] THEN EXPAND_TAC "elt" THEN REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(psi:(num->int)->A) z = psi z'") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_of_num k m:A"), (← q r"(psi:(num->int)->A) z"), (← q r"(psi:(num->int)->A) z'")] RING_ADD_LCANCEL) THEN ASM_REWRITE_TAC [RING_OF_NUM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC [], ASM_REWRITE_TAC [] THEN DISCH_TAC] THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:num") THEN ASM_CASES_TAC (← q r"i:num < n") THEN ASM_SIMP_TAC [] THEN UNDISCH_TAC (← q r"(z:num->int) IN Bx") THEN UNDISCH_TAC (← q r"(z':num->int) IN Bx") THEN EXPAND_TAC "Bx" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"rep = \J. @z. z IN Bx /\
                   ideal_generated (ring_of_integers k)
                     {(elt:(num->int)->A) z} = J") THEN SUBGOAL_THEN (← q r"!z. z IN Bx
          ==> (rep:(A->bool)->num->int)
                (ideal_generated (ring_of_integers k) {(elt:(num->int)->A) z})
              IN Bx /\
              ideal_generated (ring_of_integers k)
               {elt(rep(ideal_generated (ring_of_integers k) {elt z}))} =
              ideal_generated (ring_of_integers k) {elt z}") ASSUME_TAC THENL [X_GEN_TAC (← q r"z:num->int") THEN DISCH_TAC THEN EXPAND_TAC "rep" THEN CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN CONV_TAC SELECT_CONV THEN EXISTS_TAC (← q r"z:num->int") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!z. z IN Bx
          ==> ?x. x IN U /\
                  (elt:(num->int)->A) z =
                  ring_mul k (elt((rep:(A->bool)->num->int)
                     (ideal_generated (ring_of_integers k) {elt z}))) x") MP_TAC THENL [X_GEN_TAC (← q r"z:num->int") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"z:num->int")) o (checkM (fun th => (do if ← (do let z64 ← (do let z65 ← (pure th); pure (concl z65)); let z63 ← (q r"rep:(A->bool)->num->int"); pure (free_in z63 z64)) then (do let z66 ← (do let z67 ← (pure th); pure (concl z67)); pure (is_forall z66)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"z0 = (rep:(A->bool)->num->int)
                   (ideal_generated (ring_of_integers k)
                    {(elt:(num->int)->A) z})") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_divides (ring_of_integers k) ((elt:(num->int)->A) z0) (elt z)") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"(elt:(num->int)->A) z0"), (← q r"(elt:(num->int)->A) z")] IN_IDEAL_GENERATED_SING_EQ) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF], ALL_TAC] THEN REWRITE_TAC [ring_divides, RING_OF_INTEGERS] THEN DISCH_THEN (fun z61 => tactic_of do pure (X_CHOOSE_THEN (← q r"x:A") STRIP_ASSUME_TAC (← (do let z62 ← (pure (CONJUNCTS z61)); liftExcept (last z62))))) THEN EXISTS_TAC (← q r"x:A") THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "U" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"g:A->complex") THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o ((REWRITE_RULE [complex_embeddings, IN_ELIM_THM]) o (checkM (fun th => (do let z60 ← (q r"(g:A->complex) IN complex_embeddings k"); let z59 ← (do let z58 ← (pure th); pure (concl z58)); pure (z59 == z60))))))) THEN DISCH_THEN (MP_TAC o (MATCH_MP RING_HOMOMORPHISM_MUL)) THEN DISCH_THEN (MP_TAC o (SPECL [(← q r"(elt:(num->int)->A) z0"), (← q r"x:A")])) THEN ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN REWRITE_TAC [COMPLEX_RING_CLAUSES] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z52 ← (do let z53 ← (pure th); pure (concl z53)); pure (is_eq z52)) then (do let z57 ← (q r"(elt:(num->int)->A) z"); let z56 ← (do let z54 ← (do let z55 ← (pure th); pure (concl z55)); liftExcept (lhand z54)); pure (z56 == z57)) else pure false))))) THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o ((← do let c := (← CONJ (← ASSUME (← q r"(z:num->int) IN Bx")) (← ASSUME (← q r"(g:A->complex) IN complex_embeddings k"))); pure (fun th => MP th c)) o ((SPECL [(← q r"z:num->int"), (← q r"g:A->complex")]) o (checkM (fun th => (do let z50 ← (do let z51 ← (pure th); pure (concl z51)); let z49 ← (q r"&3 * &m / &2"); pure (free_in z49 z50))))))) THEN FIRST_ASSUM (MP_TAC o ((← do let c := (← CONJ (← ASSUME (← q r"(z0:num->int) IN Bx")) (← ASSUME (← q r"(g:A->complex) IN complex_embeddings k"))); pure (fun th => MP th c)) o ((SPECL [(← q r"z0:num->int"), (← q r"g:A->complex")]) o (checkM (fun th => (do let z47 ← (do let z48 ← (pure th); pure (concl z48)); let z46 ← (q r"&3 * &m / &2"); pure (free_in z46 z47))))))) THEN FIRST_ASSUM (fun th => tactic_of do pure ((← do if ← (do if ← (do let z40 ← (do let z41 ← (pure th); pure (concl z41)); pure (is_eq z40)) then (do let z45 ← (q r"(g:A->complex)((elt:(num->int)->A) z)"); let z44 ← (do let z42 ← (do let z43 ← (pure th); pure (concl z43)); liftExcept (lhand z42)); pure (z44 == z45)) else pure false) then pure (ONCE_REWRITE_TAC [th]) else pure NO_TAC))) THEN REWRITE_TAC [COMPLEX_NORM_MUL] THEN UNDISCH_TAC (← q r"1 <= (m:num)") THEN REWRITE_TAC [(← GSYM REAL_OF_NUM_LE)] THEN MP_TAC (← ISPEC (← q r"(g:A->complex) x") NORM_POS_LE) THEN SPEC_TAC ((← q r"norm((g:A->complex)((elt:(num->int)->A) z0))"), (← q r"a:real")) THEN SPEC_TAC ((← q r"norm((g:A->complex) x)"), (← q r"y:real")) THEN SPEC_TAC ((← q r"&m:real"), (← q r"mm:real")) THEN REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"mm / &2 * y <= a * y") MP_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC [], DISCH_TAC] THEN SUBGOAL_THEN (← q r"mm / &2 * y <= mm / &2 * &3") MP_TAC THENL [ASM_REAL_ARITH_TAC, ASM_SIMP_TAC [REAL_LE_LMUL_EQ, r39]], ALL_TAC] THEN REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"quo:(num->int)->A")) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o ((GEN_REWRITE_RULE id [HAS_SIZE]) o (checkM (fun th => (do if ← (do let z33 ← (do let z34 ← (pure th); pure (concl z34)); pure (is_comb z33)) then (do let z38 ← (q r"(2 * t + 1) EXP n"); let z37 ← (do let z35 ← (do let z36 ← (pure th); pure (concl z36)); liftExcept (rand z35)); pure (z37 == z38)) else pure false)))))) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o ((MATCH_MP HAS_SIZE_CARD) o (checkM (fun th => (do if ← (do let z27 ← (do let z28 ← (pure th); pure (concl z28)); pure (is_comb z27)) then (do let z32 ← (q r"(2 * t + 1) EXP n"); let z31 ← (do let z29 ← (do let z30 ← (pure th); pure (concl z30)); liftExcept (rand z29)); pure (z31 == z32)) else pure false)))))) THEN ONCE_REWRITE_TAC [MULT_SYM] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"CARD((S:(A->bool)->bool) CROSS (U:A->bool))") THEN CONJ_TAC THENL [ALL_TAC, ASM_SIMP_TAC [CARD_CROSS, LE_REFL]] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"CARD(IMAGE (\z. ideal_generated (ring_of_integers k)
                       {(elt:(num->int)->A) z},
                      (quo:(num->int)->A) z) Bx)") THEN CONJ_TAC THENL [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [(← q r"z:num->int"), (← q r"z':num->int")] THEN REWRITE_TAC [PAIR_EQ] THEN STRIP_TAC THEN FIRST_ASSUM (MATCH_MP_TAC o (checkM (fun th => (do if ← (do let z19 ← (do let z20 ← (pure th); pure (concl z20)); pure (is_forall z19)) then (do let b ← (do pure (Prod.snd (← (do let z21 ← (do let z22 ← (pure th); pure (concl z22)); pure (strip_forall z21))))); (do if ← (do let z23 ← (pure b); pure (is_imp z23)) then (do let z26 ← (q r"z:num->int = z'"); let z25 ← (do let z24 ← (pure b); liftExcept (rand z24)); pure (z25 == z26)) else pure false)) else pure false)))) THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM ((fun th => tactic_of do pure ((← do let th1 ← (do pure (← CONJUNCT2 (← MP (← SPEC (← q r"z:num->int") th) (← ASSUME (← q r"(z:num->int) IN Bx"))))); pure (← do let th2 ← (do pure (← CONJUNCT2 (← MP (← SPEC (← q r"z':num->int") th) (← ASSUME (← q r"(z':num->int) IN Bx"))))); pure (GEN_REWRITE_TAC BINOP_CONV [th1, th2]))))) o (checkM (fun th => (do if ← (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); let z14 ← (q r"quo:(num->int)->A"); pure (free_in z14 z15)) then (do let z17 ← (do let z18 ← (pure th); pure (concl z18)); pure (is_forall z17)) else pure false)))) THEN ASM_REWRITE_TAC [], MATCH_MP_TAC CARD_SUBSET THEN ASM_SIMP_TAC [FINITE_CROSS] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_CROSS] THEN X_GEN_TAC (← q r"z:num->int") THEN DISCH_TAC THEN CONJ_TAC THENL [FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun th => (do if ← (do if ← (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); pure (is_forall z6)) then (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); let z8 ← (q r"S:(A->bool)->bool"); pure (free_in z8 z9)) else pure false) then (do pure !(← (do let z12 ← (do let z13 ← (pure th); pure (concl z13)); let z11 ← (q r"quo:(num->int)->A"); pure (free_in z11 z12)))) else pure false)))) THEN ASM_REWRITE_TAC [], FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"z:num->int")) o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); let z1 ← (q r"quo:(num->int)->A"); pure (free_in z1 z2)) then (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); pure (is_forall z4)) else pure false))))) THEN ASM_SIMP_TAC []]])

  let NUMBER_FIELD_IDEAL_COUNT_LOWER ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r6 ← ARITH_RULE (← q r"a:num <= b ==> b <= c ==> a <= c")
    prove
      r"!k:A ring.
          number_field k
          ==> ?c N0. !N. N0 <= N
                         ==> N <= c * CARD
                                  {j | ring_ideal (ring_of_integers k) j /\
                                       ~(j = {ring_0 k}) /\
                                       ideal_norm (ring_of_integers k) j <= N}"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"w:num->A")) o (MATCH_MP RING_OF_INTEGERS_FREE)) THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)") THEN MP_TAC (← ISPECL [(← q r"\g:A->complex. sum {i:num | i < n} (\i. norm(g((w:num->A) i)))"), (← q r"complex_embeddings(k:A ring)")] UPPER_BOUND_FINITE_SET_REAL) THEN ASM_SIMP_TAC [FINITE_COMPLEX_EMBEDDINGS] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"B:real")) THEN MP_TAC (← SPEC (← q r"B:real") REAL_ARCH_SIMPLE) THEN DISCH_THEN (X_CHOOSE_TAC (← q r"B0:num")) THEN SUBGOAL_THEN (← q r"!g. g IN complex_embeddings k
          ==> sum {i:num | i < n} (\i. norm((g:A->complex)(w i))) <= &(B0 + 1)") ASSUME_TAC THENL [X_GEN_TAC (← q r"g:A->complex") THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"B:real") THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&B0:real") THEN ASM_REWRITE_TAC [REAL_OF_NUM_LE] THEN ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"B0 + 1")] NUMBER_FIELD_PRINCIPAL_IDEAL_FAMILY) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"Bn = B0 + 1") THEN ABBREV_TAC (← q r"W = CARD {x | x IN ring_carrier(ring_of_integers k) /\
                    !g. g IN complex_embeddings k
                        ==> norm((g:A->complex) x) <= &3}") THEN DISCH_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"(4 * Bn) EXP n * W"), (← q r"2 EXP n")] THEN X_GEN_TAC (← q r"N:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_DEGREE_POS) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"n:num"), (← q r"N:num")] NUM_ROOT_FLOOR) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"tm:num") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"2 <= tm") ASSUME_TAC THENL [REWRITE_TAC [(← GSYM NOT_LT)] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(tm + 1) EXP n <= 2 EXP n") MP_TAC THENL [REWRITE_TAC [EXP_MONO_LE] THEN ASM_ARITH_TAC, ASM_ARITH_TAC], ALL_TAC] THEN ABBREV_TAC (← q r"m = tm DIV 2") THEN SUBGOAL_THEN (← q r"1 <= m /\ 2 * m <= tm /\ tm <= 2 * m + 1") STRIP_ASSUME_TAC THENL [EXPAND_TAC "m" THEN MP_TAC (← SPECL [(← q r"tm:num"), (← q r"2")] DIVISION) THEN ASM_ARITH_TAC, ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"m:num")) o (checkM (fun th => (do if ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); pure (is_forall z7)) then (do let z10 ← (do let z11 ← (pure th); pure (concl z11)); let z9 ← (q r"W:num"); pure (free_in z9 z10)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"t = m DIV (2 * Bn)") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"m < (t + 1) * (2 * Bn)") ASSUME_TAC THENL [EXPAND_TAC "t" THEN MP_TAC (← SPECL [(← q r"m:num"), (← q r"2 * Bn")] DIVISION) THEN ANTS_TAC THENL [EXPAND_TAC "Bn" THEN ARITH_TAC, ALL_TAC] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"tm + 1 <= (4 * Bn) * (2 * t + 1)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"m < (t + 1) * (2 * Bn)") THEN REWRITE_TAC [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES] THEN ASM_ARITH_TAC, ALL_TAC] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"(tm + 1) EXP n") THEN CONJ_TAC THENL [ASM_SIMP_TAC [LT_IMP_LE], ALL_TAC] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"((4 * Bn) * (2 * t + 1)) EXP n") THEN CONJ_TAC THENL [ASM_REWRITE_TAC [EXP_MONO_LE], ALL_TAC] THEN REWRITE_TAC [MULT_EXP, (← GSYM MULT_ASSOC)] THEN MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC [LE_REFL] THEN MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC [LE_REFL] THEN FIRST_X_ASSUM (MATCH_MP_TAC o ((MATCH_MP r6) o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); let z1 ← (q r"W:num"); pure (free_in z1 z2)) then (do pure !(← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); pure (is_eq z4)))) else pure false))))) THEN MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC [LE_REFL] THEN MATCH_MP_TAC CARD_SUBSET THEN ASM_SIMP_TAC [NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"j:A->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN TRANS_TAC LE_TRANS (← q r"(2 * m) EXP n") THEN ASM_REWRITE_TAC [] THEN TRANS_TAC LE_TRANS (← q r"tm EXP n") THEN ASM_REWRITE_TAC [EXP_MONO_LE])

  let NUMBER_FIELD_IDEAL_COUNT_BOUNDS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")
    prove
      r"!k:A ring.
          number_field k
          ==> ?c C. !N. N <= c * CARD {j | ring_ideal (ring_of_integers k) j /\
                                           ~(j = {ring_0 k}) /\
                                           ideal_norm (ring_of_integers k) j
                                           <= N} /\
                        CARD {j | ring_ideal (ring_of_integers k) j /\
                                  ~(j = {ring_0 k}) /\
                                  ideal_norm (ring_of_integers k) j <= N}
                        <= C * N"
      (GEN_TAC THEN DISCH_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_IDEAL_COUNT_UPPER) THEN MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_IDEAL_COUNT_LOWER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num") (X_CHOOSE_TAC (← q r"N0:num"))) THEN DISCH_THEN (X_CHOOSE_TAC (← q r"C:num")) THEN MAP_EVERY EXISTS_TAC [(← q r"c + N0:num"), (← q r"C:num")] THEN X_GEN_TAC (← q r"N:num") THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"X = CARD {j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
                    ideal_norm (ring_of_integers k) (j:A->bool) <= N}") THEN ASM_CASES_TAC (← q r"N0:num <= N") THENL [FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"N:num")) o (checkM (fun th => (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); let z2 ← (q r"N0:num"); pure (free_in z2 z3)))))) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN ARITH_TAC, ALL_TAC] THEN ASM_CASES_TAC (← q r"N = 0") THEN ASM_REWRITE_TAC [LE_0] THEN SUBGOAL_THEN (← q r"1 <= X") MP_TAC THENL [EXPAND_TAC "X" THEN REWRITE_TAC [r1] THEN ASM_SIMP_TAC [CARD_EQ_0, NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN EXISTS_TAC (← q r"ring_carrier(ring_of_integers k:A ring)") THEN REWRITE_TAC [RING_IDEAL_CARRIER, IDEAL_NORM_CARRIER] THEN CONJ_TAC THENL [ALL_TAC, ASM_ARITH_TAC] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"\s. (ring_1 k:A) IN s"))) THEN REWRITE_TAC [IN_SING] THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_1) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN ASM_MESON_TAC [NUMBER_FIELD_IMP_FIELD, FIELD_NONTRIVIAL], DISCH_TAC] THEN TRANS_TAC LE_TRANS (← q r"N0 * X:num") THEN CONJ_TAC THENL [TRANS_TAC LE_TRANS (← q r"N0 * 1:num") THEN ASM_SIMP_TAC [LE_MULT_LCANCEL] THEN ASM_ARITH_TAC, REWRITE_TAC [LE_MULT_RCANCEL] THEN ARITH_TAC])

  let SUM_GROUP_CARD ← prove
    r"!(f:A->B) (g:B->real) s t.
        FINITE s /\ IMAGE f s SUBSET t
        ==> sum s (\x. g(f x)) =
            sum t (\y. &(CARD {x | x IN s /\ f x = y}) * g y)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"f:A->B"), (← q r"\x:A. (g:B->real)(f x)"), (← q r"s:A->bool"), (← q r"t:B->bool")] SUM_GROUP) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN REWRITE_TAC [] THEN TRANS_TAC EQ_TRANS (← q r"sum {x | x IN s /\ (f:A->B) x = y} (\x. (g:B->real) y)") THEN CONJ_TAC THENL [MATCH_MP_TAC SUM_EQ THEN SIMP_TAC [IN_ELIM_THM], ASM_SIMP_TAC [SUM_CONST, FINITE_RESTRICT]])

  let VSUM_GROUP_CARD ← prove
    r"!(f:A->B) (g:B->complex) s t.
        FINITE s /\ IMAGE f s SUBSET t
        ==> vsum s (\x. g(f x)) =
            vsum t (\y. Cx(&(CARD {x | x IN s /\ f x = y})) * g y)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"f:A->B"), (← q r"\x:A. (g:B->complex)(f x)"), (← q r"s:A->bool"), (← q r"t:B->bool")] VSUM_GROUP) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN REWRITE_TAC [] THEN TRANS_TAC EQ_TRANS (← q r"vsum {x | x IN s /\ (f:A->B) x = y} (\x. (g:B->complex) y)") THEN CONJ_TAC THENL [MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC [IN_ELIM_THM], ASM_SIMP_TAC [VSUM_CONST, FINITE_RESTRICT, COMPLEX_CMUL]])

  let NUMBER_FIELD_IDEAL_SUM_BY_NORM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k:A ring S (g:num->real) M.
          number_field k /\
          (!j. j IN S
               ==> ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}))
          ==> FINITE {j | j IN S /\ ideal_norm (ring_of_integers k) j <= M} /\
              sum {j | j IN S /\ ideal_norm (ring_of_integers k) j <= M}
                  (\j. g(ideal_norm (ring_of_integers k) j)) =
              sum(1..M) (\m. &(CARD {j | j IN S /\
                                         ideal_norm (ring_of_integers k) j =
                                         m}) * g m)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
                       ideal_norm (ring_of_integers k) (j:A->bool) <= M}") THEN ASM_SIMP_TAC [NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"ideal_norm (ring_of_integers k):(A->bool)->num"), (← q r"g:num->real"), (← q r"{j | j IN S /\ ideal_norm (ring_of_integers k) (j:A->bool)
                                   <= M}"), (← q r"1..M")] SUM_GROUP_CARD) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, IN_NUMSEG] THEN X_GEN_TAC (← q r"j:A->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IDEAL_NORM_POS THEN MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC (← q r"m:num") THEN STRIP_TAC THEN REWRITE_TAC [] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN ASM_MESON_TAC [LE_REFL])

  let dedekind_zeta ← new_definition
    r"dedekind_zeta (k:A ring) s =
        infsum (from 1)
         (\m. Cx(&(CARD {j | ring_ideal (ring_of_integers k) j /\
                             ~(j = {ring_0 k}) /\
                             ideal_norm (ring_of_integers k) j = m})) /
              Cx(&m) cpow s)"

  let NUMBER_FIELD_IDEAL_COUNT_SUM ← prove
    r"!k:A ring N.
        number_field k
        ==> sum(1..N) (\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                                      ~(j = {ring_0 k}) /\
                                      ideal_norm (ring_of_integers k) j =
                                      m})) =
            &(CARD {j | ring_ideal (ring_of_integers k) j /\
                        ~(j = {ring_0 k}) /\
                        ideal_norm (ring_of_integers k) j <= N})"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{j | ring_ideal (ring_of_integers k) j /\
                       ~(j = {ring_0(k:A ring)})}"), (← q r"\m:num. &1:real"), (← q r"N:num")] NUMBER_FIELD_IDEAL_SUM_BY_NORM) THEN ASM_SIMP_TAC [IN_ELIM_THM, REAL_MUL_RID, (← GSYM CONJ_ASSOC)] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN ASM_SIMP_TAC [SUM_CONST, REAL_MUL_RID])

  let NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE ← prove
    r"!k:A ring s.
        number_field k /\ &1 < s
        ==> real_summable (from 1)
             (\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                              ~(j = {ring_0 k}) /\
                              ideal_norm (ring_of_integers k) j = m}) /
                  &m rpow s)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_IDEAL_COUNT_UPPER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"C:num")) THEN MP_TAC (← ISPECL [(← q r"\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                    ~(j = {ring_0 k}) /\
                    ideal_norm (ring_of_integers k) (j:A->bool) = m}):real"), (← q r"&C:real"), (← q r"&0:real"), (← q r"0"), (← q r"s:real")] DIRICHLET_SERIES_LINEAR_PARTIAL_SUMS) THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_COUNT_SUM, REAL_POS, REAL_LE_REFL, REAL_MUL_LZERO, REAL_OF_NUM_MUL, REAL_OF_NUM_LE] THEN ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC [REAL_POS])

  let DEDEKIND_ZETA_CONVERGES ← prove
    r"!k:A ring s.
        number_field k /\ &1 < Re s
        ==> ((\m. Cx(&(CARD {j | ring_ideal (ring_of_integers k) j /\
                                 ~(j = {ring_0 k}) /\
                                 ideal_norm (ring_of_integers k) j = m})) /
                  Cx(&m) cpow s)
             sums dedekind_zeta k s) (from 1)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [dedekind_zeta, SUMS_INFSUM] THEN MATCH_MP_TAC SUMMABLE_COMPARISON THEN EXISTS_TAC (← q r"\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                    ~(j = {ring_0 k}) /\
                    ideal_norm (ring_of_integers k) (j:A->bool) = m}) /
        &m rpow (Re s)") THEN CONJ_TAC THENL [REWRITE_TAC [(← GSYM REAL_SUMMABLE)] THEN MATCH_MP_TAC NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE THEN ASM_REWRITE_TAC [], EXISTS_TAC (← q r"1") THEN X_GEN_TAC (← q r"m:num") THEN REWRITE_TAC [IN_FROM, GE] THEN STRIP_TAC THEN REWRITE_TAC [COMPLEX_NORM_DIV, COMPLEX_NORM_CX, REAL_ABS_NUM] THEN ASM_SIMP_TAC [NORM_CPOW, REAL_CX, RE_CX, REAL_OF_NUM_LT, LE_1] THEN REWRITE_TAC [COMPLEX_NORM_CX, REAL_ABS_NUM, REAL_LE_REFL]])

  let DEDEKIND_ZETA_REAL ← prove
    r"!k:A ring s.
        number_field k /\ &1 < s
        ==> ((\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                              ~(j = {ring_0 k}) /\
                              ideal_norm (ring_of_integers k) j = m}) /
                  &m rpow s)
             real_sums Re(dedekind_zeta k (Cx s))) (from 1) /\
            dedekind_zeta k (Cx s) = Cx(Re(dedekind_zeta k (Cx s)))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:real")] NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (GEN_REWRITE_RULE id [(← GSYM REAL_SUMS_INFSUM)])) THEN ABBREV_TAC (← q r"z = real_infsum (from 1)
         (\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                          ~(j = {ring_0 k}) /\
                          ideal_norm (ring_of_integers k) (j:A->bool) = m}) /
              &m rpow s)") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"dedekind_zeta (k:A ring) (Cx s) = Cx z") ASSUME_TAC THENL [MATCH_MP_TAC SERIES_UNIQUE THEN MAP_EVERY EXISTS_TAC [(← q r"\m. Cx(&(CARD {j | ring_ideal (ring_of_integers k) j /\
                          ~(j = {ring_0 k}) /\
                          ideal_norm (ring_of_integers k) (j:A->bool) = m})) /
           Cx(&m) cpow (Cx s)"), (← q r"from 1")] THEN ASM_SIMP_TAC [DEDEKIND_ZETA_CONVERGES, RE_CX] THEN MATCH_MP_TAC SUMS_EQ THEN EXISTS_TAC (← q r"Cx o (\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                            ~(j = {ring_0 k}) /\
                            ideal_norm (ring_of_integers k) (j:A->bool) =
                            m}) / &m rpow s)") THEN ASM_REWRITE_TAC [(← GSYM REAL_SUMS_COMPLEX)] THEN REWRITE_TAC [IN_FROM, o_THM] THEN X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN ASM_SIMP_TAC [CX_DIV, CX_RPOW, REAL_OF_NUM_LT, LE_1], ASM_REWRITE_TAC [RE_CX]])

  let DEDEKIND_ZETA_REAL_INFSUM ← prove
    r"!k:A ring s.
        number_field k /\ &1 < s
        ==> real_infsum (from 1)
             (\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                              ~(j = {ring_0 k}) /\
                              ideal_norm (ring_of_integers k) j = m}) /
                  &m rpow s) =
            Re(dedekind_zeta k (Cx s))"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN ASM_SIMP_TAC [DEDEKIND_ZETA_REAL])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_PRINCIPAL_IDEAL_FAMILY, NUMBER_FIELD_IDEAL_COUNT_LOWER,
           NUMBER_FIELD_IDEAL_COUNT_BOUNDS, SUM_GROUP_CARD, VSUM_GROUP_CARD,
           NUMBER_FIELD_IDEAL_SUM_BY_NORM, dedekind_zeta, NUMBER_FIELD_IDEAL_COUNT_SUM,
           NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE, DEDEKIND_ZETA_CONVERGES,
           DEDEKIND_ZETA_REAL, DEDEKIND_ZETA_REAL_INFSUM }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- dedekind_zeta.ml phrases from line 1391 to 1909                        -/
/- ---------------------------------------------------------------------- -/

structure DedekindZeta03 where
  -- @@FIELDS
  DEDEKIND_ZETA_POLE_BOUNDS : thm
  DEDEKIND_FINITE_EULER_PRODUCT : thm
  NUMBER_FIELD_IDEAL_PRIME_POWER_PRODUCT : thm
  DEDEKIND_ZETA_EULER_PRODUCT_BOUND : thm
  DEDEKIND_ZETA_EULER_PRODUCT : thm
  DEDEKIND_ZETA_EULER_PRODUCT_REAL : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekindZeta03 [HolBase] (D : DedekindZetaDeps) (BDedekindZeta01 : DedekindZeta01) (BDedekindZeta02 : DedekindZeta02) :
    ExceptT String IO DedekindZeta03 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC,
        MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, TAUT, .. } := D
  let { ADD_SUB, CARD_SUBSET, COMPLEX_MUL_LID, COMPLEX_NORM_CX, COMPLEX_NORM_INV,
        COMPLEX_NORM_MUL, COMPLEX_POW_INV, COMPLEX_SUB_RDISTRIB, CPOW_NPRODUCT,
        CPOW_NUM_EXP, CPRODUCT_EQ, CPRODUCT_INV, CPRODUCT_VSUM_POW, CX_INV, CX_PRODUCT,
        CX_RPOW, CX_SUB, DEDEKIND_IDEAL_EQ_VALUATION, DEDEKIND_IDEAL_NORM_PRIME_POWERS,
        DEDEKIND_IDEAL_PRODUCT_PRIME_POWERS, DEDEKIND_IDEAL_SUBSET_POW_VALUATION,
        DEDEKIND_RING_OF_INTEGERS, DIVIDES_LE_IMP, EVENTUALLY_SEQUENTIALLY,
        EXP_MONO_LE, FINITE_FUNSPACE, FINITE_IMAGE, FINITE_NUMSEG, FINITE_SUBSET,
        FORALL_AND_THM, FORALL_IN_IMAGE, FROM_0, FROM_INTER_NUMSEG, FUN_EQ_THM,
        IDEAL_NORM_GT_1, IDEAL_NORM_IDEAL_POW, IDEAL_NORM_POS,
        IDEAL_NORM_SUBSET_DIVIDES, INTER_UNIV, IN_ELIM_THM, IN_IMAGE, IN_NUMSEG, .. } := D.core1
  let { LEFT_IMP_EXISTS_THM, LE_0, LE_1, LE_EXP, LE_REFL, LE_TRANS, LIM_CONST,
        LIM_CPRODUCT, LIM_NORM_UBOUND, LIM_SEQUENTIALLY, LIM_SUB, LTE_TRANS, LT_IMP_LE,
        LT_NZ, LT_POW2_REFL, MULT_CLAUSES, MULT_SYM, NORM_CPOW,
        NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM,
        NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM,
        NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2, PRIME_IMP_PROPER_IDEAL,
        PRIME_IMP_RING_IDEAL, PROPER_IDEAL_ALT, REALLIM_COMPLEX, REALLIM_SEQUENTIALLY,
        REAL_ABS_NUM, REAL_ADD_LID, REAL_CX, REAL_EQ_IMP_LE, REAL_INFSUM_UNIQUE,
        REAL_INFSUM_ZETA_BOUNDS, REAL_INV_LT_1, REAL_LET_TRANS, REAL_LE_DIV,
        REAL_LE_INV_EQ, REAL_LE_LDIV_EQ, REAL_LE_LMUL, REAL_LE_RMUL, REAL_LE_TRANS,
        REAL_LT_INV_EQ, REAL_MUL_ASSOC, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_MUL_SYM,
        REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_OF_NUM_MUL, .. } := D.core2
  let { REAL_PARTIAL_SUMS_LE_INFSUM, REAL_POS, REAL_SERIES_FROM, REAL_SUB_REFL,
        REAL_SUB_RZERO, REAL_SUMMABLE_FROM_ELSEWHERE_EQ, REAL_SUMS_INFSUM,
        REAL_SUMS_OFFSET, RE_CX, RING_IDEAL_IDEAL_POW, RING_OF_INTEGERS,
        RING_OF_INTEGERS_FINITE_QUOTIENT, RPOW_LT_1, RPOW_POS_LE, SUBSET,
        SUBSET_ANTISYM, SUMS_GP, SUM_ADD_SPLIT, SUM_EQ_0_NUMSEG, SUM_EQ_NUMSEG,
        SUM_LE_NUMSEG, TRIVIAL_LIMIT_SEQUENTIALLY, UPPER_BOUND_FINITE_SET, VSUM_EQ,
        VSUM_IMAGE, VSUM_NORM, VSUM_SUB, complex_div, complex_pow, dist, o_DEF, o_THM,
        prime_ideal, proper_ideal, real_div, sums, .. } := D.core3
  let { DIRICHLET_SERIES_LINEAR_PARTIAL_SUMS, .. } := BDedekindZeta01
  let { DEDEKIND_ZETA_CONVERGES, DEDEKIND_ZETA_REAL, DEDEKIND_ZETA_REAL_INFSUM,
        NUMBER_FIELD_IDEAL_COUNT_BOUNDS, NUMBER_FIELD_IDEAL_COUNT_SUM,
        NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE, VSUM_GROUP_CARD, .. } := BDedekindZeta02
  -- @@SCOPE END

  let DEDEKIND_ZETA_POLE_BOUNDS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"&2 * c = c * &2:real")
    prove
      r"!k:A ring.
          number_field k
          ==> ?c C. &0 < c /\
                    !s. &1 < s /\ s <= &2
                        ==> c / (s - &1) <= Re(dedekind_zeta k (Cx s)) /\
                            Re(dedekind_zeta k (Cx s)) <= C / (s - &1)"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_IDEAL_COUNT_BOUNDS) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM, FORALL_AND_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"c0:num"), (← q r"C0:num")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(c0 = 0)") ASSUME_TAC THENL [DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"1")) o (checkM (fun th => (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); let z2 ← (q r"c0:num"); pure (free_in z2 z3)))))) THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN ARITH_TAC, ALL_TAC] THEN MAP_EVERY EXISTS_TAC [(← q r"inv(&c0):real"), (← q r"&2 * &C0:real")] THEN ASM_SIMP_TAC [REAL_LT_INV_EQ, REAL_OF_NUM_LT, LT_NZ] THEN X_GEN_TAC (← q r"s:real") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                      ~(j = {ring_0 k}) /\
                      ideal_norm (ring_of_integers k) (j:A->bool) = m}):real"), (← q r"&C0:real"), (← q r"inv(&c0):real"), (← q r"0"), (← q r"s:real")] DIRICHLET_SERIES_LINEAR_PARTIAL_SUMS) THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_COUNT_SUM, DEDEKIND_ZETA_REAL_INFSUM] THEN ANTS_TAC THENL [ASM_REWRITE_TAC [REAL_POS, REAL_LE_INV_EQ, REAL_OF_NUM_MUL, REAL_OF_NUM_LE, LE_0] THEN X_GEN_TAC (← q r"N:num") THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [(← GSYM real_div)] THEN ASM_SIMP_TAC [REAL_LE_LDIV_EQ, REAL_OF_NUM_LT, LT_NZ] THEN REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_LE] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← SPEC (← q r"s:real") REAL_INFSUM_ZETA_BOUNDS) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"Z = real_infsum (from 1) (\m. inv(&m rpow s))") THEN REWRITE_TAC [REAL_MUL_RZERO, REAL_SUB_RZERO] THEN STRIP_TAC THEN STRIP_TAC THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"inv(&c0) * Z:real") THEN ASM_REWRITE_TAC [real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [REAL_LE_INV_EQ, REAL_POS], MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&C0 * Z:real") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&C0 * s / (s - &1)") THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [REAL_POS], REWRITE_TAC [real_div, REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC] THEN ONCE_REWRITE_TAC [r1] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [REAL_POS]]])

  let DEDEKIND_FINITE_EULER_PRODUCT ← prove
    r"!r t E s.
        dedekind_domain r /\ FINITE t /\
        (!P. P IN t ==> prime_ideal r P /\ ~(P = {ring_0 r}) /\
                        FINITE(ring_carrier(quotient_ring r P)))
        ==> cproduct t (\P. vsum(0..E)
                              (\i. inv(Cx(&(ideal_norm r P)) cpow s) pow i)) =
            vsum (IMAGE (\e. ideal_product r t (\P. ideal_pow r P (e P)))
                        {e | (!P. P IN t ==> e P <= E) /\
                             (!P. ~(P IN t) ==> e P = 0)})
                 (\j:A->bool. inv(Cx(&(ideal_norm r j)) cpow s))"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [CPRODUCT_VSUM_POW] THEN wPart rand (lhand o rand) VSUM_IMAGE THEN ANTS_TAC THENL [CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{e:(A->bool)->num | (!P. P IN t ==> e P IN 0..E) /\
                                      (!P. ~(P IN t) ==> e P = 0)}") THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_FUNSPACE THEN ASM_REWRITE_TAC [FINITE_NUMSEG], REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_NUMSEG, LE_0] THEN MESON_TAC []], ALL_TAC] THEN REWRITE_TAC [IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"e:(A->bool)->num"), (← q r"f:(A->bool)->num")] THEN STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"P:A->bool") THEN ASM_CASES_TAC (← q r"(P:A->bool) IN t") THEN ASM_SIMP_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"t:(A->bool)->bool"), (← q r"e:(A->bool)->num")] DEDEKIND_IDEAL_PRODUCT_PRIME_POWERS) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"t:(A->bool)->bool"), (← q r"f:(A->bool)->num")] DEDEKIND_IDEAL_PRODUCT_PRIME_POWERS) THEN ASM_SIMP_TAC [] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN DISCH_THEN (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ASM_SIMP_TAC [] THEN ARITH_TAC, DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC (← q r"e:(A->bool)->num") THEN REWRITE_TAC [IN_ELIM_THM, o_THM] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"t:(A->bool)->bool"), (← q r"e:(A->bool)->num")] DEDEKIND_IDEAL_NORM_PRIME_POWERS) THEN ASM_SIMP_TAC [] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN ASM_SIMP_TAC [CPOW_NPRODUCT, CPOW_NUM_EXP, (← GSYM CPRODUCT_INV)] THEN MATCH_MP_TAC CPRODUCT_EQ THEN REWRITE_TAC [COMPLEX_POW_INV])

  let NUMBER_FIELD_IDEAL_PRIME_POWER_PRODUCT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"a EXP 1 <= b ==> a <= b")
    let r2 ← ARITH_RULE (← q r"2 <= n <=> 1 < n")
    let r3 ← ARITH_RULE (← q r"~(1 <= 0)")
    prove
      r"!k:A ring n E j.
          number_field k /\ n <= E /\
          ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
          ideal_norm (ring_of_integers k) j <= n
          ==> ?e. (!P. P IN {P | prime_ideal (ring_of_integers k) P /\
                                 ~(P = {ring_0 k}) /\
                                 ideal_norm (ring_of_integers k) P <= n}
                       ==> e P <= E) /\
                  (!P. ~(P IN {P | prime_ideal (ring_of_integers k) P /\
                                   ~(P = {ring_0 k}) /\
                                   ideal_norm (ring_of_integers k) P <= n})
                       ==> e P = 0) /\
                  j = ideal_product (ring_of_integers k)
                        {P | prime_ideal (ring_of_integers k) P /\
                             ~(P = {ring_0 k}) /\
                             ideal_norm (ring_of_integers k) P <= n}
                        (\P. ideal_pow (ring_of_integers k) P (e P))"
      (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"t = {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
               ideal_norm (ring_of_integers k) (P:A->bool) <= n}") THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers k:A ring)") ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"FINITE(t:(A->bool)->bool)") ASSUME_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
                       ideal_norm (ring_of_integers k) (j:A->bool) <= n}") THEN ASM_SIMP_TAC [NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN EXPAND_TAC "t" THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN MESON_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"FINITE(ring_carrier(quotient_ring (ring_of_integers k) (j:A->bool)))") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_OF_INTEGERS_FINITE_QUOTIENT], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ideal_norm (ring_of_integers k) (j:A->bool) = 0)") ASSUME_TAC THENL [ASM_MESON_TAC [IDEAL_NORM_POS, r3], ALL_TAC] THEN SUBGOAL_THEN (← q r"!P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
          ~(ideal_valuation (ring_of_integers k) P j = 0)
          ==> (P:A->bool) IN t /\
              ideal_valuation (ring_of_integers k) P j <= E") ASSUME_TAC THENL [GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"v = ideal_valuation (ring_of_integers k) P (j:A->bool)") THEN SUBGOAL_THEN (← q r"FINITE(ring_carrier(quotient_ring (ring_of_integers k) (P:A->bool))) /\
        2 <= ideal_norm (ring_of_integers k) P") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_OF_INTEGERS_FINITE_QUOTIENT, PRIME_IMP_RING_IDEAL] THEN REWRITE_TAC [r2] THEN MATCH_MP_TAC IDEAL_NORM_GT_1 THEN ASM_SIMP_TAC [RING_OF_INTEGERS_FINITE_QUOTIENT, PRIME_IMP_RING_IDEAL] THEN ASM_MESON_TAC [PRIME_IMP_PROPER_IDEAL, PROPER_IDEAL_ALT, prime_ideal, proper_ideal], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_norm (ring_of_integers k) P EXP v <=
        ideal_norm (ring_of_integers k) (j:A->bool)") ASSUME_TAC THENL [MATCH_MP_TAC DIVIDES_LE_IMP THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"v:num")] IDEAL_NORM_IDEAL_POW) THEN ANTS_TAC THENL [ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS], ALL_TAC] THEN DISCH_THEN (SUBST1_TAC o (SYM o CONJUNCT2)) THEN MATCH_MP_TAC IDEAL_NORM_SUBSET_DIVIDES THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"j:A->bool"), (← q r"v:num")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_REWRITE_TAC [LE_REFL, RING_OF_INTEGERS], ALL_TAC] THEN CONJ_TAC THENL [EXPAND_TAC "t" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN TRANS_TAC LE_TRANS (← q r"ideal_norm (ring_of_integers k) (j:A->bool)") THEN ASM_REWRITE_TAC [] THEN TRANS_TAC LE_TRANS (← q r"ideal_norm (ring_of_integers k) (P:A->bool) EXP v") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r1 THEN REWRITE_TAC [LE_EXP] THEN ASM_ARITH_TAC, MATCH_MP_TAC LT_IMP_LE THEN TRANS_TAC LTE_TRANS (← q r"2 EXP v") THEN REWRITE_TAC [LT_POW2_REFL] THEN TRANS_TAC LE_TRANS (← q r"ideal_norm (ring_of_integers k) (P:A->bool) EXP v") THEN ASM_SIMP_TAC [EXP_MONO_LE] THEN ASM_ARITH_TAC], ALL_TAC] THEN EXISTS_TAC (← q r"\P. if P IN t then ideal_valuation (ring_of_integers k) P (j:A->bool)
          else 0") THEN REWRITE_TAC [] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"P:A->bool") THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"ideal_valuation (ring_of_integers k) P (j:A->bool) = 0") THEN ASM_REWRITE_TAC [LE_0] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"(P:A->bool) IN t") THEN EXPAND_TAC "t" THEN SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN CONJ_TAC THENL [SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"t:(A->bool)->bool"), (← q r"\P. if P IN t then ideal_valuation (ring_of_integers k) P (j:A->bool)
            else 0")] DEDEKIND_IDEAL_PRODUCT_PRIME_POWERS) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN EXPAND_TAC "t" THEN SIMP_TAC [IN_ELIM_THM, RING_OF_INTEGERS], REWRITE_TAC [RING_OF_INTEGERS] THEN STRIP_TAC] THEN wPart Except.ok (lhand o rand) (← ISPEC (← q r"ring_of_integers k:A ring") DEDEKIND_IDEAL_EQ_VALUATION) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN X_GEN_TAC (← q r"Q:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [])

  let DEDEKIND_ZETA_EULER_PRODUCT_BOUND ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"(x:real) - y <= x <=> &0 <= y")
    let r2 ← ARITH_RULE (← q r"1 <= n + 1")
    let r3 ← REAL_ARITH (← q r"x <= y ==> abs(x - y) = y - x:real")
    let r4 ← REAL_ARITH (← q r"y <= z ==> x <= y ==> x <= z:real")
    let r5 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    let r6 ← ARITH_RULE (← q r"2 <= n ==> 0 < n")
    let r7 ← ARITH_RULE (← q r"2 <= n <=> 1 < n")
    let r8 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k:A ring s n.
          number_field k /\ &1 < Re s
          ==> norm(cproduct {P | prime_ideal (ring_of_integers k) P /\
                                 ~(P = {ring_0 k}) /\
                                 ideal_norm (ring_of_integers k) P <= n}
                            (\P. inv(Cx(&1) -
                                     inv(Cx(&(ideal_norm (ring_of_integers k) P))
                                         cpow s))) -
                   dedekind_zeta k s)
              <= real_infsum (from (n + 1))
                   (\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                                    ~(j = {ring_0 k}) /\
                                    ideal_norm (ring_of_integers k) j = m}) /
                        &m rpow Re s)"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers k:A ring)") ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], ALL_TAC] THEN ABBREV_TAC (← q r"t = {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
               ideal_norm (ring_of_integers k) (P:A->bool) <= n}") THEN ABBREV_TAC (← q r"g = \m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                          ~(j = {ring_0 k}) /\
                          ideal_norm (ring_of_integers k) (j:A->bool) = m}) /
              &m rpow Re s") THEN ABBREV_TAC (← q r"a = \m. CARD {j | ring_ideal (ring_of_integers k) j /\
                        ~(j = {ring_0 k}) /\
                        ideal_norm (ring_of_integers k) (j:A->bool) = m}") THEN SUBGOAL_THEN (← q r"FINITE(t:(A->bool)->bool) /\
      !P. P IN t
          ==> prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
              FINITE(ring_carrier(quotient_ring (ring_of_integers k) P)) /\
              2 <= ideal_norm (ring_of_integers k) P") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
               ideal_norm (ring_of_integers k) (j:A->bool) <= n}") THEN ASM_SIMP_TAC [NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN EXPAND_TAC "t" THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN MESON_TAC [PRIME_IMP_RING_IDEAL], EXPAND_TAC "t" THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r8 THEN CONJ_TAC THENL [ASM_SIMP_TAC [RING_OF_INTEGERS_FINITE_QUOTIENT, PRIME_IMP_RING_IDEAL], DISCH_TAC THEN REWRITE_TAC [r7] THEN MATCH_MP_TAC IDEAL_NORM_GT_1 THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN ASM_MESON_TAC [PRIME_IMP_PROPER_IDEAL, PROPER_IDEAL_ALT, prime_ideal, proper_ideal]]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!P. P IN t
          ==> norm(inv(Cx(&(ideal_norm (ring_of_integers k) (P:A->bool)))
                       cpow s)) < &1") ASSUME_TAC THENL [X_GEN_TAC (← q r"P:A->bool") THEN DISCH_TAC THEN REWRITE_TAC [COMPLEX_NORM_INV] THEN MATCH_MP_TAC REAL_INV_LT_1 THEN SUBGOAL_THEN (← q r"2 <= ideal_norm (ring_of_integers k) (P:A->bool)") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [NORM_CPOW, REAL_CX, RE_CX, REAL_OF_NUM_LT, r6] THEN REWRITE_TAC [COMPLEX_NORM_CX, REAL_ABS_NUM] THEN MATCH_MP_TAC RPOW_LT_1 THEN REWRITE_TAC [REAL_OF_NUM_LT] THEN CONJ_TAC THENL [ASM_ARITH_TAC, ASM_REAL_ARITH_TAC], ALL_TAC] THEN SUBGOAL_THEN (← q r"real_summable (from 1) g /\ !m. &0 <= (g:num->real) m") STRIP_ASSUME_TAC THENL [EXPAND_TAC "g" THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE] THEN GEN_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN SIMP_TAC [REAL_POS, RPOW_POS_LE], ALL_TAC] THEN SUBGOAL_THEN (← q r"!E. n <= E
          ==> norm(cproduct t (\P. vsum(0..E)
                     (\i. inv(Cx(&(ideal_norm (ring_of_integers k)
                                     (P:A->bool))) cpow s) pow i)) -
                   dedekind_zeta k s)
              <= real_infsum (from (n + 1)) g") ASSUME_TAC THENL [X_GEN_TAC (← q r"E:num") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"t:(A->bool)->bool"), (← q r"E:num"), (← q r"s:complex")] DEDEKIND_FINITE_EULER_PRODUCT) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_OF_INTEGERS], DISCH_THEN SUBST1_TAC] THEN ABBREV_TAC (← q r"EF = {e | (!P. P IN t ==> e P <= E) /\
                 (!P:A->bool. ~(P IN t) ==> e P = 0)}") THEN ABBREV_TAC (← q r"IM = IMAGE (\e. ideal_product (ring_of_integers k) t
                         (\P:A->bool. ideal_pow (ring_of_integers k) P (e P)))
                   EF") THEN SUBGOAL_THEN (← q r"FINITE(EF:((A->bool)->num)->bool)") ASSUME_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{e:(A->bool)->num | (!P. P IN t ==> e P IN 0..E) /\
                                        (!P. ~(P IN t) ==> e P = 0)}") THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_FUNSPACE THEN ASM_REWRITE_TAC [FINITE_NUMSEG], EXPAND_TAC "EF" THEN REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_NUMSEG, LE_0] THEN MESON_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"FINITE(IM:(A->bool)->bool) /\
        !j. j IN IM
            ==> ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
                FINITE(ring_carrier(quotient_ring (ring_of_integers k) j)) /\
                1 <= ideal_norm (ring_of_integers k) j") STRIP_ASSUME_TAC THENL [EXPAND_TAC "IM" THEN ASM_SIMP_TAC [FINITE_IMAGE, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"e:(A->bool)->num") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"t:(A->bool)->bool"), (← q r"e:(A->bool)->num")] DEDEKIND_IDEAL_PRODUCT_PRIME_POWERS) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_OF_INTEGERS], REWRITE_TAC [RING_OF_INTEGERS] THEN STRIP_TAC] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r5 THEN CONJ_TAC THENL [ASM_SIMP_TAC [RING_OF_INTEGERS_FINITE_QUOTIENT], REWRITE_TAC [IDEAL_NORM_POS]], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o ((ISPEC (← q r"ideal_norm (ring_of_integers k):(A->bool)->num")) o (MATCH_MP UPPER_BOUND_FINITE_SET))) THEN DISCH_THEN (X_CHOOSE_TAC (← q r"M:num")) THEN ABBREV_TAC (← q r"b = \m. CARD {j | j IN IM /\
                          ideal_norm (ring_of_integers k) (j:A->bool) = m}") THEN SUBGOAL_THEN (← q r"!m. (b:num->num) m <= (a:num->num) m") ASSUME_TAC THENL [X_GEN_TAC (← q r"m:num") THEN MAP_EVERY EXPAND_TAC ["a", "b"] THEN REWRITE_TAC [] THEN MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [], MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
                 ideal_norm (ring_of_integers k) (j:A->bool) <= m}") THEN ASM_SIMP_TAC [NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN MESON_TAC [LE_REFL]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!m. m <= n ==> (b:num->num) m = (a:num->num) m") ASSUME_TAC THENL [X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["a", "b"] THEN REWRITE_TAC [] THEN AP_TERM_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [], REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"j:A->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"E:num"), (← q r"j:A->bool")] NUMBER_FIELD_IDEAL_PRIME_POWER_PRODUCT) THEN ANTS_TAC THENL [ASM_MESON_TAC [], ASM_REWRITE_TAC []] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:(A->bool)->num") STRIP_ASSUME_TAC) THEN EXPAND_TAC "IM" THEN REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"e:(A->bool)->num") THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "EF" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC []], ALL_TAC] THEN MATCH_MP_TAC (← ISPEC (← q r"sequentially") LIM_NORM_UBOUND) THEN EXISTS_TAC (← q r"\N. vsum (IM:(A->bool)->bool)
              (\j. inv(Cx(&(ideal_norm (ring_of_integers k) j)) cpow s)) -
            vsum(1..N) (\m. Cx(&((a:num->num) m)) / Cx(&m) cpow s)") THEN REWRITE_TAC [TRIVIAL_LIMIT_SEQUENTIALLY, EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL [MATCH_MP_TAC LIM_SUB THEN REWRITE_TAC [LIM_CONST] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:complex")] DEDEKIND_ZETA_CONVERGES) THEN ASM_REWRITE_TAC [sums, FROM_INTER_NUMSEG] THEN EXPAND_TAC "a" THEN REWRITE_TAC [], ALL_TAC] THEN EXISTS_TAC (← q r"M + n:num") THEN X_GEN_TAC (← q r"N:num") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ideal_norm (ring_of_integers k):(A->bool)->num"), (← q r"\m. inv(Cx(&m) cpow s)"), (← q r"IM:(A->bool)->bool"), (← q r"1..N")] VSUM_GROUP_CARD) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_NUMSEG] THEN X_GEN_TAC (← q r"j:A->bool") THEN DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN TRANS_TAC LE_TRANS (← q r"M:num") THEN CONJ_TAC THENL [ASM_MESON_TAC [], ASM_ARITH_TAC], REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC [(← GSYM VSUM_SUB), FINITE_NUMSEG] THEN wPart lhand (lhand o rand) VSUM_NORM THEN REWRITE_TAC [FINITE_NUMSEG] THEN MATCH_MP_TAC r4 THEN SUBGOAL_THEN (← q r"!m. 1 <= m
            ==> norm(Cx(&(CARD {j | j IN IM /\
                                    ideal_norm (ring_of_integers k)
                                      (j:A->bool) = m})) *
                     inv(Cx(&m) cpow s) -
                     Cx(&((a:num->num) m)) / Cx(&m) cpow s) =
                (&(a m) - &((b:num->num) m)) / &m rpow Re s") ASSUME_TAC THENL [X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"CARD {j | j IN IM /\ ideal_norm (ring_of_integers k) (j:A->bool) = m} =
          (b:num->num) m") SUBST1_TAC THENL [EXPAND_TAC "b" THEN REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [complex_div, (← GSYM COMPLEX_SUB_RDISTRIB), (← GSYM CX_SUB)] THEN REWRITE_TAC [COMPLEX_NORM_MUL, COMPLEX_NORM_CX, COMPLEX_NORM_INV] THEN ASM_SIMP_TAC [NORM_CPOW, REAL_CX, RE_CX, REAL_OF_NUM_LT, LE_1] THEN REWRITE_TAC [COMPLEX_NORM_CX, REAL_ABS_NUM, real_div] THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC r3 THEN ASM_REWRITE_TAC [REAL_OF_NUM_LE], ALL_TAC] THEN TRANS_TAC REAL_LE_TRANS (← q r"sum(1..N) (\m. (&((a:num->num) m) - &((b:num->num) m)) /
                       &m rpow Re s)") THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"N:num = n + (N - n)") SUBST1_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN SIMP_TAC [SUM_ADD_SPLIT, r2] THEN SUBGOAL_THEN (← q r"sum(1..n) (\m. (&((a:num->num) m) - &((b:num->num) m)) /
                       &m rpow Re s) = &0") SUBST1_TAC THENL [MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN ASM_SIMP_TAC [REAL_SUB_REFL, real_div, REAL_MUL_LZERO], REWRITE_TAC [REAL_ADD_LID]] THEN TRANS_TAC REAL_LE_TRANS (← q r"sum(n + 1..n + (N - n)) (g:num->real)") THEN CONJ_TAC THENL [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC (← q r"m:num") THEN STRIP_TAC THEN EXPAND_TAC "g" THEN REWRITE_TAC [real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC [REAL_LE_INV_EQ, RPOW_POS_LE, REAL_POS] THEN EXPAND_TAC "a" THEN REWRITE_TAC [] THEN REWRITE_TAC [r1, REAL_POS], MP_TAC (← ISPECL [(← q r"g:num->real"), (← q r"from (n + 1)"), (← q r"n + (N - n):num")] REAL_PARTIAL_SUMS_LE_INFSUM) THEN REWRITE_TAC [FROM_INTER_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [REAL_SUMMABLE_FROM_ELSEWHERE_EQ]], ALL_TAC] THEN MATCH_MP_TAC (← ISPEC (← q r"sequentially") LIM_NORM_UBOUND) THEN EXISTS_TAC (← q r"\E. cproduct t (\P. vsum(0..E)
            (\i. inv(Cx(&(ideal_norm (ring_of_integers k) (P:A->bool)))
                     cpow s) pow i)) - dedekind_zeta k s") THEN REWRITE_TAC [TRIVIAL_LIMIT_SEQUENTIALLY, EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL [ALL_TAC, EXISTS_TAC (← q r"n:num") THEN ASM_SIMP_TAC []] THEN MATCH_MP_TAC LIM_SUB THEN REWRITE_TAC [LIM_CONST] THEN MATCH_MP_TAC LIM_CPRODUCT THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"P:A->bool") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"0")) o (MATCH_MP SUMS_GP))) THEN REWRITE_TAC [sums, FROM_0, INTER_UNIV, complex_pow] THEN REWRITE_TAC [complex_div, COMPLEX_MUL_LID])

  let DEDEKIND_ZETA_EULER_PRODUCT ← prove
    r"!k:A ring s.
        number_field k /\ &1 < Re s
        ==> ((\n. cproduct {P | prime_ideal (ring_of_integers k) P /\
                               ~(P = {ring_0 k}) /\
                               ideal_norm (ring_of_integers k) P <= n}
                          (\P. inv(Cx(&1) -
                                   inv(Cx(&(ideal_norm (ring_of_integers k) P))
                                       cpow s))))
             --> dedekind_zeta k s) sequentially"
    (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"g = \m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                        ~(j = {ring_0 k}) /\
                        ideal_norm (ring_of_integers k) (j:A->bool) = m}) /
            &m rpow Re s") THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"Re s")] NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (GEN_REWRITE_RULE id [(← GSYM REAL_SUMS_INFSUM)])) THEN ABBREV_TAC (← q r"l = real_infsum (from 1) (g:num->real)") THEN DISCH_TAC THEN REWRITE_TAC [LIM_SEQUENTIALLY, dist] THEN X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [REAL_SERIES_FROM])) THEN REWRITE_TAC [REALLIM_SEQUENTIALLY] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"e:real"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"N:num")) THEN EXISTS_TAC (← q r"N + 1") THEN X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q r"real_infsum (from (n + 1)) (g:num->real)") THEN CONJ_TAC THENL [EXPAND_TAC "g" THEN ASM_SIMP_TAC [DEDEKIND_ZETA_EULER_PRODUCT_BOUND], ALL_TAC] THEN SUBGOAL_THEN (← q r"real_infsum (from (n + 1)) g = l - sum(1..n) (g:num->real)") SUBST1_TAC THENL [MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN MP_TAC (← ISPECL [(← q r"g:num->real"), (← q r"l:real"), (← q r"1"), (← q r"n + 1")] REAL_SUMS_OFFSET) THEN ASM_REWRITE_TAC [ADD_SUB] THEN ANTS_TAC THENL [ASM_ARITH_TAC, SIMP_TAC []], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"n:num"))) THEN ANTS_TAC THENL [ASM_ARITH_TAC, REAL_ARITH_TAC])

  let DEDEKIND_ZETA_EULER_PRODUCT_REAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"2 <= n ==> 0 < n")
    prove
      r"!k:A ring s.
          number_field k /\ &1 < s
          ==> ((\n. product {P | prime_ideal (ring_of_integers k) P /\
                                ~(P = {ring_0 k}) /\
                                ideal_norm (ring_of_integers k) P <= n}
                           (\P. inv(&1 -
                                    inv(&(ideal_norm (ring_of_integers k) P)
                                        rpow s))))
               ---> Re(dedekind_zeta k (Cx s))) sequentially"
      (REPEAT STRIP_TAC THEN REWRITE_TAC [REALLIM_COMPLEX] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:real")] DEDEKIND_ZETA_REAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o (SYM o CONJUNCT2)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"Cx s")] DEDEKIND_ZETA_EULER_PRODUCT) THEN ASM_REWRITE_TAC [RE_CX] THEN SUBGOAL_THEN (← q r"!n. cproduct {P | prime_ideal (ring_of_integers k) P /\
                        ~(P = {ring_0 k}) /\
                        ideal_norm (ring_of_integers k) P <= n}
                   (\P. inv(Cx(&1) -
                            inv(Cx(&(ideal_norm (ring_of_integers k) P))
                                cpow Cx s))) =
          Cx(product {P | prime_ideal (ring_of_integers k) P /\
                          ~(P = {ring_0 k}) /\
                          ideal_norm (ring_of_integers k) (P:A->bool) <= n}
                     (\P. inv(&1 -
                              inv(&(ideal_norm (ring_of_integers k) P)
                                  rpow s))))") (fun th => REWRITE_TAC [th, o_DEF]) THEN X_GEN_TAC (← q r"n:num") THEN ASM_SIMP_TAC [CX_PRODUCT, NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM] THEN MATCH_MP_TAC CPRODUCT_EQ THEN X_GEN_TAC (← q r"P:A->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool")] NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_SIMP_TAC [CX_INV, CX_SUB, CX_RPOW, REAL_OF_NUM_LT, r1])

  -- @@RETURN BEGIN
  return { DEDEKIND_ZETA_POLE_BOUNDS, DEDEKIND_FINITE_EULER_PRODUCT,
           NUMBER_FIELD_IDEAL_PRIME_POWER_PRODUCT, DEDEKIND_ZETA_EULER_PRODUCT_BOUND,
           DEDEKIND_ZETA_EULER_PRODUCT, DEDEKIND_ZETA_EULER_PRODUCT_REAL }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- dedekind_zeta.ml phrases from line 1948 to 2650                        -/
/- ---------------------------------------------------------------------- -/

structure DedekindZeta04 where
  -- @@FIELDS
  DEDEKIND_ZETA_LOG_PRIME_IDEALS : thm
  NUMBER_FIELD_NONPRIME_NORM_SUM_LE : thm
  DEDEKIND_ZETA_LOG_POLE : thm
  NUMBER_FIELD_PRIME_IDEALS_LOG : thm
  NUMBER_FIELD_DEGREE_ONE_PRIMES_LOG : thm
  has_dirichlet_density : thm
  HAS_DIRICHLET_DENSITY_LOG : thm
  HAS_DIRICHLET_DENSITY_UNIQUE : thm
  HAS_DIRICHLET_DENSITY_FINITE : thm
  HAS_DIRICHLET_DENSITY_INFINITE : thm
  NUMBER_FIELD_PRIME_IDEALS_DENSITY : thm
  NUMBER_FIELD_DEGREE_ONE_PRIMES_DENSITY : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekindZeta04 [HolBase] (D : DedekindZetaDeps) (BDedekindZeta02 : DedekindZeta02) (BDedekindZeta03 : DedekindZeta03) :
    ExceptT String IO DedekindZeta04 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON, MESON_TAC,
        REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD, REAL_RAT_REDUCE_CONV, SET_RULE,
        SET_TAC, new_definition, .. } := D
  let { ALWAYS_EVENTUALLY, ARITH, CARD_CLAUSES, CARD_SUBSET, CONJ_ASSOC, DE_MORGAN_THM,
        EVENTUALLY_TRUE, EXP_1, EXP_2, FINITE_IMAGE, FINITE_INTER, FINITE_RESTRICT,
        FINITE_SUBSET, FORALL_IN_IMAGE, FROM_INTER_NUMSEG, INFINITE, INTER_SUBSET,
        IN_ELIM_THM, IN_FROM, IN_INTER, IN_NUMSEG, .. } := D.core1
  let { LE_0, LE_EXP, LE_REFL, LE_SQUARE_REFL, LE_TRANS, LOG_DIV, LOG_EXP, LOG_INV,
        LOG_MONO_LE_IMP, LOG_MONO_LT_IMP, NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM,
        NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM,
        NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q, NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE,
        NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2, NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q,
        PRIME_GE_2, PRIME_IMP_RING_IDEAL, PRODUCT_LE, REALLIM_LE,
        REALLIM_REAL_CONTINUOUS_FUNCTION, REALLIM_UBOUND, REALLIM_UNIQUE,
        REALLIM_WITHINREAL, REAL_ABS_DIV, REAL_ABS_NUM, REAL_ADD_RID,
        REAL_CONTINUOUS_AT_EXP, REAL_EQ_IMP_LE, REAL_EXP_LE_INV_1_SUB,
        REAL_EXP_MONO_LE, REAL_EXP_POS_LE, REAL_EXP_POS_LT, REAL_EXP_SUM,
        REAL_INFSUM_SUB, REAL_INFSUM_UNIQUE, REAL_INFSUM_ZETA_BOUNDS, REAL_INV_0,
        REAL_INV_1_SUB_LE_EXP, REAL_LE_ADD2, REAL_LE_DIV, REAL_LE_INV2, REAL_LE_INV_EQ,
        REAL_LE_LDIV_EQ, REAL_LE_LMUL, REAL_LE_MUL, REAL_LE_RMUL, REAL_LE_TRANS,
        REAL_LT_01, REAL_LT_DIV, REAL_LT_INV_EQ, REAL_LT_LDIV_EQ, REAL_LT_MIN,
        REAL_LT_RDIV_EQ, REAL_LT_TRANS, REAL_MUL_LID, REAL_MUL_LZERO, REAL_MUL_RID,
        REAL_MUL_RZERO, REAL_MUL_SYM, REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_OF_NUM_POW, .. } := D.core2
  let { REAL_PARTIAL_SUMS_LE_INFSUM, REAL_POS, REAL_POW_1, REAL_POW_2, REAL_POW_INV,
        REAL_POW_LE, REAL_POW_LT, REAL_SERIES_FINITE_SUPPORT, REAL_SERIES_FROM,
        REAL_SERIES_POS, REAL_SUB_LE, REAL_SUMMABLE_COMPARISON, REAL_SUMMABLE_SUB,
        REAL_SUMMABLE_ZETA, REAL_SUMS_INFSUM, RIGHT_IMP_EXISTS_THM,
        RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q, RING_OF_INTEGERS_PRIME_IDEAL_ABOVE,
        RPOW_ADD, RPOW_LE_1, RPOW_MONO_LE, RPOW_POS_LE, RPOW_POS_LT, RPOW_POW,
        RPOW_ZERO, SKOLEM_THM, SUBSET, SUM_ABS_BOUND, SUM_ADD, SUM_CONST, SUM_EQ,
        SUM_GROUP, SUM_LE, SUM_LE_NUMSEG, SUM_LMUL, SUM_SUBSET_SIMPLE, SUM_SUB_NUMSEG,
        SUM_UNION, TRIVIAL_LIMIT_ATREAL_RIGHT, TRIVIAL_LIMIT_SEQUENTIALLY, real_abs,
        real_div, .. } := D.core3
  let { DEDEKIND_ZETA_REAL_INFSUM, NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE,
        NUMBER_FIELD_IDEAL_SUM_BY_NORM, .. } := BDedekindZeta02
  let { DEDEKIND_ZETA_EULER_PRODUCT_REAL, DEDEKIND_ZETA_POLE_BOUNDS, .. } := BDedekindZeta03
  -- @@SCOPE END

  let DEDEKIND_ZETA_LOG_PRIME_IDEALS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"inv(&2) < &1")
    let r7 ← REAL_ARITH (← q r"inv(&2) < &1")
    let r26 ← REAL_ARITH (← q r"&2 <= (q:real) ==> &0 < q")
    prove
      r"!k:A ring s.
          number_field k /\ &1 < s
          ==> real_summable (from 1)
               (\m. &(CARD {P | prime_ideal (ring_of_integers k) P /\
                                ~(P = {ring_0 k}) /\
                                ideal_norm (ring_of_integers k) P = m}) /
                    &m rpow s) /\
              &0 < Re(dedekind_zeta k (Cx s)) /\
              real_infsum (from 1)
               (\m. &(CARD {P | prime_ideal (ring_of_integers k) P /\
                                ~(P = {ring_0 k}) /\
                                ideal_norm (ring_of_integers k) P = m}) /
                    &m rpow s) <= log(Re(dedekind_zeta k (Cx s))) /\
              log(Re(dedekind_zeta k (Cx s))) <=
              real_infsum (from 1)
               (\m. &(CARD {P | prime_ideal (ring_of_integers k) P /\
                                ~(P = {ring_0 k}) /\
                                ideal_norm (ring_of_integers k) P = m}) /
                    &m rpow s) + &2 * Re(dedekind_zeta k (Cx(&2)))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"f = \m. &(CARD {P | prime_ideal (ring_of_integers k) P /\
                          ~(P = {ring_0 k}) /\
                          ideal_norm (ring_of_integers k) (P:A->bool) = m}) /
              &m rpow s") THEN ABBREV_TAC (← q r"Z = Re(dedekind_zeta (k:A ring) (Cx s))") THEN ABBREV_TAC (← q r"Z2 = Re(dedekind_zeta (k:A ring) (Cx(&2)))") THEN SUBGOAL_THEN (← q r"!m. &0 <= (f:num->real) m /\
          f m <= &(CARD {j | ring_ideal (ring_of_integers k) j /\
                             ~(j = {ring_0 k}) /\
                             ideal_norm (ring_of_integers k) (j:A->bool) = m}) /
                 &m rpow s") ASSUME_TAC THENL [X_GEN_TAC (← q r"m:num") THEN EXPAND_TAC "f" THEN REWRITE_TAC [] THEN SIMP_TAC [REAL_LE_DIV, REAL_POS, RPOW_POS_LE] THEN REWRITE_TAC [real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC [REAL_LE_INV_EQ, RPOW_POS_LE, REAL_POS, REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN MESON_TAC [PRIME_IMP_RING_IDEAL], MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
               ideal_norm (ring_of_integers k) (j:A->bool) <= m}") THEN ASM_SIMP_TAC [NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN MESON_TAC [LE_REFL]], ALL_TAC] THEN SUBGOAL_THEN (← q r"real_summable (from 1) (f:num->real)") ASSUME_TAC THENL [MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN EXISTS_TAC (← q r"\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                        ~(j = {ring_0 k}) /\
                        ideal_norm (ring_of_integers k) (j:A->bool) = m}) /
            &m rpow s") THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE] THEN EXISTS_TAC (← q r"0") THEN ASM_SIMP_TAC [real_abs], ASM_REWRITE_TAC []] THEN ABBREV_TAC (← q r"PS = real_infsum (from 1) (f:num->real)") THEN ABBREV_TAC (← q r"TP = \n. {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
                   ideal_norm (ring_of_integers k) (P:A->bool) <= n}") THEN SUBGOAL_THEN (← q r"!n. FINITE((TP:num->(A->bool)->bool) n) /\
          !P. P IN TP n
              ==> &0 < inv(&(ideal_norm (ring_of_integers k) P) rpow s) /\
                  inv(&(ideal_norm (ring_of_integers k) P) rpow s) <= inv(&2) /\
                  inv(&(ideal_norm (ring_of_integers k) P) rpow s) pow 2 <=
                  inv(&(ideal_norm (ring_of_integers k) P) rpow &2)") ASSUME_TAC THENL [X_GEN_TAC (← q r"n:num") THEN EXPAND_TAC "TP" THEN ASM_SIMP_TAC [NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM] THEN X_GEN_TAC (← q r"P:A->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool")] NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ABBREV_TAC (← q r"q = &(ideal_norm (ring_of_integers k) (P:A->bool)):real") THEN SUBGOAL_THEN (← q r"&2 <= (q:real)") ASSUME_TAC THENL [EXPAND_TAC "q" THEN ASM_REWRITE_TAC [REAL_OF_NUM_LE], ALL_TAC] THEN SUBGOAL_THEN (← q r"&2 <= q rpow s") ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"q rpow &1") THEN CONJ_TAC THENL [ASM_REWRITE_TAC [RPOW_POW, REAL_POW_1], MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REAL_ARITH_TAC], ALL_TAC] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC, MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC, REWRITE_TAC [(← GSYM REAL_POW_INV)] THEN REWRITE_TAC [REAL_POW_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL [MATCH_MP_TAC RPOW_POS_LT THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"(q rpow s) pow 2 = q rpow (s + s)") SUBST1_TAC THENL [ASM_SIMP_TAC [RPOW_ADD, REAL_POW_2, r26], MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REAL_ARITH_TAC]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!n. sum ((TP:num->(A->bool)->bool) n)
              (\P. inv(&(ideal_norm (ring_of_integers k) P) rpow s)) =
          sum(1..n) f") ASSUME_TAC THENL [X_GEN_TAC (← q r"n:num") THEN EXPAND_TAC "TP" THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0(k:A ring)})}"), (← q r"\m. inv(&m rpow s)"), (← q r"n:num")] NUMBER_FIELD_IDEAL_SUM_BY_NORM) THEN ANTS_TAC THENL [ASM_SIMP_TAC [IN_ELIM_THM, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN REWRITE_TAC [IN_ELIM_THM, (← GSYM CONJ_ASSOC)] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT2) THEN EXPAND_TAC "f" THEN REWRITE_TAC [real_div], ALL_TAC] THEN SUBGOAL_THEN (← q r"!n. sum ((TP:num->(A->bool)->bool) n)
              (\P. inv(&(ideal_norm (ring_of_integers k) P) rpow s) pow 2) <= Z2") ASSUME_TAC THENL [X_GEN_TAC (← q r"n:num") THEN TRANS_TAC REAL_LE_TRANS (← q r"sum ((TP:num->(A->bool)->bool) n)
            (\P. inv(&(ideal_norm (ring_of_integers k) P) rpow &2))") THEN CONJ_TAC THENL [MATCH_MP_TAC SUM_LE THEN ASM_MESON_TAC [], ALL_TAC] THEN TRANS_TAC REAL_LE_TRANS (← q r"sum {j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
                 ideal_norm (ring_of_integers k) (j:A->bool) <= n}
            (\j. inv(&(ideal_norm (ring_of_integers k) j) rpow &2))") THEN CONJ_TAC THENL [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_SIMP_TAC [NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN SIMP_TAC [REAL_LE_INV_EQ, RPOW_POS_LE, REAL_POS] THEN EXPAND_TAC "TP" THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN MESON_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0(k:A ring)})}"), (← q r"\m. inv(&m rpow &2)"), (← q r"n:num")] NUMBER_FIELD_IDEAL_SUM_BY_NORM) THEN ANTS_TAC THENL [ASM_SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN REWRITE_TAC [IN_ELIM_THM, (← GSYM CONJ_ASSOC)] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT2) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"(&2:real)")] DEDEKIND_ZETA_REAL_INFSUM) THEN ASM_REWRITE_TAC [REAL_OF_NUM_LT, ARITH] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [(← GSYM real_div)] THEN MP_TAC (← ISPECL [(← q r"\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\
                         ~(j = {ring_0 k}) /\
                         ideal_norm (ring_of_integers k) (j:A->bool) = m}) /
             &m rpow &2"), (← q r"from 1"), (← q r"n:num")] REAL_PARTIAL_SUMS_LE_INFSUM) THEN REWRITE_TAC [FROM_INTER_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE, REAL_OF_NUM_LT, ARITH] THEN SIMP_TAC [REAL_LE_DIV, REAL_POS, RPOW_POS_LE], ALL_TAC] THEN SUBGOAL_THEN (← q r"!n. exp(sum(1..n) f) <=
          product ((TP:num->(A->bool)->bool) n)
            (\P. inv(&1 - inv(&(ideal_norm (ring_of_integers k) P) rpow s))) /\
          product ((TP:num->(A->bool)->bool) n)
            (\P. inv(&1 - inv(&(ideal_norm (ring_of_integers k) P) rpow s))) <=
          exp(PS + &2 * Z2)") ASSUME_TAC THENL [X_GEN_TAC (← q r"n:num") THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((SPEC (← q r"n:num")) o (checkM (fun th => (do if ← (do let z21 ← (do let z22 ← (pure th); pure (concl z22)); pure (is_forall z21)) then (do let z23 ← (do pure (Prod.snd (← (do let z24 ← (do let z25 ← (pure th); pure (concl z25)); liftExcept (dest_forall z24))))); pure (is_conj z23)) else pure false))))) THEN CONJ_TAC THENL [FIRST_ASSUM ((fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← SPEC (← q r"n:num") th))])) o (checkM (fun th => (do if ← (do if ← (do let z13 ← (do let z14 ← (pure th); pure (concl z14)); pure (is_forall z13)) then (do let z15 ← (do pure (Prod.snd (← (do let z16 ← (do let z17 ← (pure th); pure (concl z17)); liftExcept (dest_forall z16))))); pure (is_eq z15)) else pure false) then (do let z19 ← (do let z20 ← (pure th); pure (concl z20)); let z18 ← (q r"f:num->real"); pure (free_in z18 z19)) else pure false)))) THEN ASM_SIMP_TAC [REAL_EXP_SUM] THEN MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC [REAL_EXP_POS_LE] THEN X_GEN_TAC (← q r"P:A->bool") THEN DISCH_TAC THEN MATCH_MP_TAC REAL_EXP_LE_INV_1_SUB THEN FIRST_ASSUM (MP_TAC o ((SPEC (← q r"P:A->bool")) o (checkM (fun th => (do if ← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); pure (is_forall z8)) then (do let z10 ← (do pure (Prod.snd (← (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); liftExcept (dest_forall z11))))); pure (is_imp z10)) else pure false))))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC r7 THEN REAL_ARITH_TAC, ALL_TAC] THEN TRANS_TAC REAL_LE_TRANS (← q r"exp(sum ((TP:num->(A->bool)->bool) n)
              (\P. inv(&(ideal_norm (ring_of_integers k) P) rpow s) +
                   &2 * inv(&(ideal_norm (ring_of_integers k) P) rpow s)
                        pow 2))") THEN CONJ_TAC THENL [ASM_SIMP_TAC [REAL_EXP_SUM] THEN MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"P:A->bool") THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o ((SPEC (← q r"P:A->bool")) o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_forall z2)) then (do let z4 ← (do pure (Prod.snd (← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); liftExcept (dest_forall z5))))); pure (is_imp z4)) else pure false))))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN STRIP_TAC THEN CONJ_TAC THENL [REWRITE_TAC [REAL_LE_INV_EQ] THEN MP_TAC r1 THEN ASM_REAL_ARITH_TAC, MATCH_MP_TAC REAL_INV_1_SUB_LE_EXP THEN ASM_REAL_ARITH_TAC], ALL_TAC] THEN REWRITE_TAC [REAL_EXP_MONO_LE] THEN ASM_SIMP_TAC [SUM_ADD, SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL [EXPAND_TAC "PS" THEN MP_TAC (← ISPECL [(← q r"f:num->real"), (← q r"from 1"), (← q r"n:num")] REAL_PARTIAL_SUMS_LE_INFSUM) THEN ASM_REWRITE_TAC [FROM_INTER_NUMSEG], MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [REAL_POS]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:real")] DEDEKIND_ZETA_EULER_PRODUCT_REAL) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"!n. {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
               ideal_norm (ring_of_integers k) (P:A->bool) <= n} = TP n") (fun th => REWRITE_TAC [th]) THENL [EXPAND_TAC "TP" THEN REWRITE_TAC [], ALL_TAC] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"exp PS <= Z /\ Z <= exp(PS + &2 * Z2)") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [MATCH_MP_TAC (← ISPEC (← q r"sequentially") REALLIM_LE) THEN EXISTS_TAC (← q r"\n. exp(sum(1..n) (f:num->real))") THEN EXISTS_TAC (← q r"\n. product ((TP:num->(A->bool)->bool) n)
                (\P. inv(&1 - inv(&(ideal_norm (ring_of_integers k) P)
                                 rpow s)))") THEN ASM_REWRITE_TAC [TRIVIAL_LIMIT_SEQUENTIALLY, EVENTUALLY_TRUE] THEN MATCH_MP_TAC REALLIM_REAL_CONTINUOUS_FUNCTION THEN REWRITE_TAC [REAL_CONTINUOUS_AT_EXP] THEN REWRITE_TAC [(← GSYM REAL_SERIES_FROM)] THEN EXPAND_TAC "PS" THEN ASM_REWRITE_TAC [REAL_SUMS_INFSUM], MATCH_MP_TAC (← ISPEC (← q r"sequentially") REALLIM_UBOUND) THEN EXISTS_TAC (← q r"\n. product ((TP:num->(A->bool)->bool) n)
                (\P. inv(&1 - inv(&(ideal_norm (ring_of_integers k) P)
                                 rpow s)))") THEN ASM_REWRITE_TAC [TRIVIAL_LIMIT_SEQUENTIALLY, EVENTUALLY_TRUE]], ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 < (Z:real)") ASSUME_TAC THENL [MP_TAC (← SPEC (← q r"PS:real") REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC, ASM_REWRITE_TAC []] THEN CONJ_TAC THENL [GEN_REWRITE_TAC LAND_CONV [(← GSYM LOG_EXP)] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC [REAL_EXP_POS_LT], GEN_REWRITE_TAC RAND_CONV [(← GSYM LOG_EXP)] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC []])

  let NUMBER_FIELD_NONPRIME_NORM_SUM_LE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r4 ← SET_RULE (← q r"{x:A->bool | x IN s /\ P x} = {} <=> !x. x IN s ==> ~P x")
    let r14 ← ARITH_RULE (← q r"2 <= f <=> 1 <= f /\ ~(f = 1)")
    prove
      r"!k:A ring s N.
          number_field k /\ &1 <= s
          ==> sum {q | prime_ideal (ring_of_integers k) q /\ ~(q = {ring_0 k}) /\
                       ~prime(ideal_norm (ring_of_integers k) q) /\
                       ideal_norm (ring_of_integers k) q <= N}
                  (\q. inv(&(ideal_norm (ring_of_integers k) q) rpow s))
              <= &2 * &(extension_degree (subfield_generated k {ring_0 k},k) I)"
      (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)") THEN ABBREV_TAC (← q r"Cc = {q | prime_ideal (ring_of_integers k) q /\ ~(q = {ring_0 k}) /\
                ~prime(ideal_norm (ring_of_integers k) q) /\
                ideal_norm (ring_of_integers k) (q:A->bool) <= N}") THEN SUBGOAL_THEN (← q r"FINITE(Cc:(A->bool)->bool)") ASSUME_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
             ideal_norm (ring_of_integers k) (j:A->bool) <= N}") THEN ASM_SIMP_TAC [NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN EXPAND_TAC "Cc" THEN SIMP_TAC [SUBSET, IN_ELIM_THM, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"?pb. !q:A->bool. q IN Cc ==> prime(pb q) /\ ring_of_num k (pb q) IN q") (X_CHOOSE_TAC (← q r"pb:(A->bool)->num")) THENL [REWRITE_TAC [(← GSYM RIGHT_IMP_EXISTS_THM), (← GSYM SKOLEM_THM)] THEN X_GEN_TAC (← q r"q:A->bool") THEN EXPAND_TAC "Cc" THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"q:A->bool")] RING_OF_INTEGERS_PRIME_IDEAL_ABOVE) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!q:A->bool. q IN Cc
          ==> inv(&(ideal_norm (ring_of_integers k) q) rpow s) <=
              inv(&(pb q) pow 2) /\
              1 <= pb q /\ pb q <= N") ASSUME_TAC THENL [X_GEN_TAC (← q r"q:A->bool") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (← do let c := (← ASSUME (← q r"(q:A->bool) IN Cc")); pure (fun th => MATCH_MP th c))) THEN STRIP_TAC THEN UNDISCH_TAC (← q r"(q:A->bool) IN Cc") THEN EXPAND_TAC "Cc" THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"q:A->bool"), (← q r"pb(q:A->bool):num")] RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"q:A->bool"), (← q r"pb(q:A->bool):num")] NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"f = residue_degree (integer_ring,ring_of_integers k)
                        (ring_of_int k) (q:A->bool)") THEN STRIP_TAC THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"2 <= f") ASSUME_TAC THENL [REWRITE_TAC [r14] THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~prime(ideal_norm (ring_of_integers k) (q:A->bool))") THEN ASM_REWRITE_TAC [EXP_1], ALL_TAC] THEN SUBGOAL_THEN (← q r"2 <= pb(q:A->bool)") ASSUME_TAC THENL [ASM_MESON_TAC [PRIME_GE_2], ALL_TAC] THEN SUBGOAL_THEN (← q r"pb(q:A->bool) EXP 2 <= ideal_norm (ring_of_integers k) q") ASSUME_TAC THENL [ASM_REWRITE_TAC [LE_EXP] THEN COND_CASES_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"pb(q:A->bool) <= pb q EXP 2") ASSUME_TAC THENL [REWRITE_TAC [EXP_2, LE_SQUARE_REFL], ALL_TAC] THEN FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun th => (do if ← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); pure (is_eq z8)) then (do let z13 ← (q r"ideal_norm (ring_of_integers k) (q:A->bool)"); let z12 ← (do let z10 ← (do let z11 ← (pure th); pure (concl z11)); liftExcept (lhs z10)); pure (z12 == z13)) else pure false)))) THEN REPEAT CONJ_TAC THENL [ALL_TAC, ASM_ARITH_TAC, ASM_ARITH_TAC] THEN MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC [REAL_OF_NUM_LT] THEN ASM_ARITH_TAC, ALL_TAC] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&(ideal_norm (ring_of_integers k) (q:A->bool)):real") THEN CONJ_TAC THENL [ASM_REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_LE], MP_TAC (← SPECL [(← q r"&1:real"), (← q r"s:real"), (← q r"&(ideal_norm (ring_of_integers k) (q:A->bool)):real")] RPOW_MONO_LE) THEN REWRITE_TAC [RPOW_POW, REAL_POW_1] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [REAL_OF_NUM_LE] THEN ASM_ARITH_TAC], ALL_TAC] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"sum Cc (\q:A->bool. inv(&(pb q) pow 2))") THEN CONJ_TAC THENL [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"pb:(A->bool)->num"), (← q r"\q:A->bool. inv(&(pb q) pow 2)"), (← q r"Cc:(A->bool)->bool"), (← q r"1..N")] SUM_GROUP) THEN ANTS_TAC THENL [ASM_SIMP_TAC [SUBSET, FORALL_IN_IMAGE, IN_NUMSEG], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"sum(1..N) (\p. &n * inv(&p pow 2))") THEN CONJ_TAC THENL [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC (← q r"p:num") THEN STRIP_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"sum {q | q IN Cc /\ pb q = p} (\q:A->bool. inv(&p pow 2))") THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN ASM_SIMP_TAC [SUM_CONST, FINITE_RESTRICT] THEN MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC [REAL_LE_INV_EQ, REAL_POW_LE, REAL_POS, REAL_OF_NUM_LE] THEN ASM_CASES_TAC (← q r"prime p") THENL [EXPAND_TAC "n" THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"CARD {P | prime_ideal (ring_of_integers k) P /\
                              ring_of_num k p IN (P:A->bool)}") THEN ASM_SIMP_TAC [NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q] THEN MATCH_MP_TAC CARD_SUBSET THEN ASM_SIMP_TAC [NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"q:A->bool") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"q:A->bool")) o (checkM (fun th => (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); let z5 ← (q r"ring_of_num (k:A ring)"); pure (free_in z5 z6)))))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"(q:A->bool) IN Cc") THEN EXPAND_TAC "Cc" THEN SIMP_TAC [IN_ELIM_THM], SUBGOAL_THEN (← q r"{q | q IN Cc /\ (pb:(A->bool)->num) q = p} = {}:(A->bool)->bool") SUBST1_TAC THENL [REWRITE_TAC [r4] THEN ASM_MESON_TAC [], REWRITE_TAC [CARD_CLAUSES, LE_0]]], ALL_TAC] THEN REWRITE_TAC [SUM_LMUL] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_POS] THEN MP_TAC (← SPEC (← q r"&2:real") REAL_INFSUM_ZETA_BOUNDS) THEN MP_TAC (← SPECL [(← q r"1"), (← q r"&2:real")] REAL_SUMMABLE_ZETA) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [RPOW_POW] THEN REPEAT DISCH_TAC THEN FIRST_X_ASSUM (STRIP_ASSUME_TAC o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_conj z2))))) THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"real_infsum (from 1) (\m. inv(&m pow 2))") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"\m. inv(&m pow 2)"), (← q r"from 1"), (← q r"N:num")] REAL_PARTIAL_SUMS_LE_INFSUM) THEN ASM_REWRITE_TAC [FROM_INTER_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC [REAL_LE_INV_EQ, REAL_POW_LE, REAL_POS])

  let DEDEKIND_ZETA_LOG_POLE ← prove
    r"!k:A ring.
        number_field k
        ==> ?C. !s. &1 < s /\ s <= &2
                    ==> &0 < Re(dedekind_zeta k (Cx s)) /\
                        abs(log(Re(dedekind_zeta k (Cx s))) + log(s - &1))
                        <= C"
    (GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP DEDEKIND_ZETA_POLE_BOUNDS)) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:real") (X_CHOOSE_THEN (← q r"C:real") STRIP_ASSUME_TAC)) THEN EXISTS_TAC (← q r"abs(log c) + abs(log C)") THEN X_GEN_TAC (← q r"s:real") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"s:real"))) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"Z = Re(dedekind_zeta (k:A ring) (Cx s))") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"&0 < (s:real) - &1") ASSUME_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 < c / (s - &1)") ASSUME_TAC THENL [ASM_SIMP_TAC [REAL_LT_DIV], ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 < (Z:real) /\ &0 < (C:real)") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 < C / (s - &1)") MP_TAC THENL [ASM_REAL_ARITH_TAC, ASM_SIMP_TAC [REAL_LT_RDIV_EQ, REAL_MUL_LZERO]], ASM_REWRITE_TAC []] THEN MP_TAC (← ISPECL [(← q r"c / (s - &1)"), (← q r"Z:real")] LOG_MONO_LE_IMP) THEN MP_TAC (← ISPECL [(← q r"Z:real"), (← q r"C / (s - &1)")] LOG_MONO_LE_IMP) THEN ASM_SIMP_TAC [LOG_DIV] THEN REAL_ARITH_TAC)

  let NUMBER_FIELD_PRIME_IDEALS_LOG ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"&0 < z2
    ==> (&0 < (z:real) /\ abs((lz:real) + l) <= C)
        ==> (&0 < z /\ x <= lz /\ lz <= x + &2 * z2)
            ==> abs(x + l) <= C + &2 * z2")
    prove
      r"!k:A ring.
          number_field k
          ==> ?C. !s. &1 < s /\ s <= &2
                      ==> real_summable (from 1)
                           (\m. &(CARD {P | prime_ideal (ring_of_integers k) P /\
                                            ~(P = {ring_0 k}) /\
                                            ideal_norm (ring_of_integers k) P =
                                            m}) /
                                &m rpow s) /\
                          abs(real_infsum (from 1)
                               (\m. &(CARD {P | prime_ideal
                                                 (ring_of_integers k) P /\
                                                ~(P = {ring_0 k}) /\
                                                ideal_norm
                                                 (ring_of_integers k) P = m}) /
                                    &m rpow s) +
                              log(s - &1)) <= C"
      (GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"C:real")) o (MATCH_MP DEDEKIND_ZETA_LOG_POLE)) THEN SUBGOAL_THEN (← q r"&0 < Re(dedekind_zeta (k:A ring) (Cx(&2)))") ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (SPEC (← q r"(&2:real)"))) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC [], ALL_TAC] THEN EXISTS_TAC (← q r"C + &2 * Re(dedekind_zeta (k:A ring) (Cx(&2)))") THEN X_GEN_TAC (← q r"s:real") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:real")] DEDEKIND_ZETA_LOG_PRIME_IDEALS) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (CONJUNCTS_THEN2 (fun th => REWRITE_TAC [th]) MP_TAC) THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"s:real"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_DEGREE_ONE_PRIMES_LOG ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"N:num"
    let v2 ← GSYM REAL_SERIES_FROM
    let q3 ← q r"\N. sum(1..N) (\m. (pf:num->real) m - df m)"
    let q4 ← q r"sequentially"
    let v5 ← ISPEC q4 REALLIM_UBOUND
    let q6 ← q r"from 1"
    let q7 ← q r"\m. (pf:num->real) m - df m"
    let v8 ← GSYM REAL_SUMS_INFSUM
    let q9 ← q r"real_summable (from 1) (\m. (pf:num->real) m - df m)"
    let q10 ← q r"&0 <= real_infsum (from 1) (\m. (pf:num->real) m - df m) /\
    real_infsum (from 1) (\m. (pf:num->real) m - df m) <= &2 * &n"
    let q11 ← q r"0"
    let q12 ← q r"pf:num->real"
    let q13 ← q r"real_summable (from 1) (df:num->real)"
    let q14 ← q r"{P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
           ideal_norm (ring_of_integers k) (P:A->bool) <= m}"
    let q15 ← q r"m:num"
    let q16 ← q r"!m. &0 <= (df:num->real) m /\ df m <= pf m"
    let q17 ← q r"k:A ring"
    let v18 ← ISPEC q17 NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE
    let q19 ← q r"{P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
             ideal_norm (ring_of_integers k) (P:A->bool) <= N}"
    let q20 ← q r"FINITE s /\ FINITE t /\ DISJOINT s t /\ u = s UNION t
      ==> sum u f = sum s f + sum t (f:(A->bool)->real)"
    let r21 ← MESON [SUM_UNION] q20
    let q22 ← q r"x:real = y + z ==> x - y = z"
    let r23 ← REAL_ARITH q22
    let v24 ← GSYM CONJ_ASSOC
    let q25 ← q r"N:num"
    let q26 ← q r"\m. inv(&m rpow s)"
    let q27 ← q r"{P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0(k:A ring)}) /\
             residue_degree (integer_ring,ring_of_integers k)
               (ring_of_int k) P = 1}"
    let q28 ← q r"k:A ring"
    let v29 ← ISPECL [q28, q27, q26, q25] NUMBER_FIELD_IDEAL_SUM_BY_NORM
    let q30 ← q r"N:num"
    let q31 ← q r"\m. inv(&m rpow s)"
    let q32 ← q r"{P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0(k:A ring)})}"
    let q33 ← q r"k:A ring"
    let v34 ← ISPECL [q33, q32, q31, q30] NUMBER_FIELD_IDEAL_SUM_BY_NORM
    let q35 ← q r"N:num"
    let q36 ← q r"!N. sum(1..N) (\m. (pf:num->real) m - df m) =
        sum {q | prime_ideal (ring_of_integers k) q /\ ~(q = {ring_0 k}) /\
                 ~prime(ideal_norm (ring_of_integers k) q) /\
                 ideal_norm (ring_of_integers k) (q:A->bool) <= N}
            (\q. inv(&(ideal_norm (ring_of_integers k) q) rpow s))"
    let q37 ← q r"df = \m. &(CARD {P | prime_ideal (ring_of_integers k) P /\
                         ~(P = {ring_0 k}) /\
                         residue_degree (integer_ring,ring_of_integers k)
                           (ring_of_int k) P = 1 /\
                         ideal_norm (ring_of_integers k) (P:A->bool) = m}) /
             &m rpow s"
    let q38 ← q r"pf = \m. &(CARD {P | prime_ideal (ring_of_integers k) P /\
                         ~(P = {ring_0 k}) /\
                         ideal_norm (ring_of_integers k) (P:A->bool) = m}) /
             &m rpow s"
    let q39 ← q r"s:real"
    let q40 ← q r"s:real"
    let q41 ← q r"(C:real) + &2 * &n"
    let q42 ← q r"n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)"
    let q43 ← q r"C:real"
    prove
      r"!k:A ring.
          number_field k
          ==> ?C. !s. &1 < s /\ s <= &2
                      ==> real_summable (from 1)
                           (\m. &(CARD {P | prime_ideal (ring_of_integers k) P /\
                                            ~(P = {ring_0 k}) /\
                                            residue_degree
                                             (integer_ring,ring_of_integers k)
                                             (ring_of_int k) P = 1 /\
                                            ideal_norm (ring_of_integers k) P =
                                            m}) /
                                &m rpow s) /\
                          abs(real_infsum (from 1)
                               (\m. &(CARD {P | prime_ideal
                                                 (ring_of_integers k) P /\
                                                ~(P = {ring_0 k}) /\
                                                residue_degree
                                                 (integer_ring,
                                                  ring_of_integers k)
                                                 (ring_of_int k) P = 1 /\
                                                ideal_norm
                                                 (ring_of_integers k) P = m}) /
                                    &m rpow s) +
                              log(s - &1)) <= C"
      (GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC q43) o (MATCH_MP NUMBER_FIELD_PRIME_IDEALS_LOG)) THEN ABBREV_TAC q42 THEN EXISTS_TAC q41 THEN X_GEN_TAC q40 THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC q39)) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC q38 THEN ABBREV_TAC q37 THEN STRIP_TAC THEN SUBGOAL_THEN q36 ASSUME_TAC THENL [X_GEN_TAC q35 THEN REWRITE_TAC [SUM_SUB_NUMSEG] THEN MAP_EVERY EXPAND_TAC ["pf", "df"] THEN REWRITE_TAC [real_div] THEN MP_TAC v34 THEN MP_TAC v29 THEN ASM_SIMP_TAC [IN_ELIM_THM, PRIME_IMP_RING_IDEAL] THEN REWRITE_TAC [v24] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN MATCH_MP_TAC r23 THEN MATCH_MP_TAC r21 THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC q19 THEN ASM_SIMP_TAC [NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM] THEN SET_TAC [], ALL_TAC] THEN MP_TAC v18 THEN ASM_REWRITE_TAC [] THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q16 ASSUME_TAC THENL [X_GEN_TAC q15 THEN MAP_EVERY EXPAND_TAC ["pf", "df"] THEN REWRITE_TAC [real_div] THEN SIMP_TAC [REAL_LE_MUL, REAL_POS, REAL_LE_INV_EQ, RPOW_POS_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC [REAL_LE_INV_EQ, RPOW_POS_LE, REAL_POS, REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC q14 THEN ASM_SIMP_TAC [NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM] THEN SIMP_TAC [SUBSET, IN_ELIM_THM, LE_REFL], ALL_TAC] THEN SUBGOAL_THEN q13 ASSUME_TAC THENL [MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN EXISTS_TAC q12 THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC q11 THEN ASM_SIMP_TAC [real_abs], ASM_REWRITE_TAC []] THEN SUBGOAL_THEN q10 MP_TAC THENL [SUBGOAL_THEN q9 MP_TAC THENL [ASM_SIMP_TAC [REAL_SUMMABLE_SUB], ALL_TAC] THEN DISCH_THEN (MP_TAC o (GEN_REWRITE_RULE id [v8])) THEN DISCH_TAC THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_SERIES_POS THEN EXISTS_TAC q7 THEN EXISTS_TAC q6 THEN ASM_REWRITE_TAC [REAL_SUB_LE], MATCH_MP_TAC v5 THEN EXISTS_TAC q3 THEN ASM_REWRITE_TAC [v2, TRIVIAL_LIMIT_SEQUENTIALLY] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC q1 THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "n" THEN MATCH_MP_TAC NUMBER_FIELD_NONPRIME_NORM_SUM_LE THEN ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC], ASM_SIMP_TAC [REAL_INFSUM_SUB] THEN ASM_REAL_ARITH_TAC])

  let has_dirichlet_density ← new_definition
    r"has_dirichlet_density (k:A ring) S d <=>
        ((\s. real_infsum (from 1)
                (\m. &(CARD {P | P IN S /\
                                 ideal_norm (ring_of_integers k) P = m}) /
                     &m rpow s) /
              log(inv(s - &1)))
         ---> d) (atreal (&1) within {s | &1 < s})"

  let HAS_DIRICHLET_DENSITY_LOG ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"&0 < (x:real) ==> abs x = x")
    prove
      r"!k:A ring S d C.
          (!s. &1 < s /\ s <= &2
               ==> abs(real_infsum (from 1)
                        (\m. &(CARD {P | P IN S /\
                                         ideal_norm (ring_of_integers k) P =
                                         m}) /
                             &m rpow s) + d * log(s - &1)) <= C)
          ==> has_dirichlet_density k S d"
      (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [has_dirichlet_density, REALLIM_WITHINREAL, IN_ELIM_THM] THEN X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN EXISTS_TAC (← q r"min (&1) (exp(--((abs C + &1) / e)))") THEN REWRITE_TAC [REAL_LT_MIN, REAL_EXP_POS_LT, REAL_LT_01] THEN X_GEN_TAC (← q r"s:real") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"s:real"))) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN ABBREV_TAC (← q r"ds = real_infsum (from 1)
            (\m. &(CARD {P | P IN S /\
                             ideal_norm (ring_of_integers k) (P:A->bool) = m}) /
                 &m rpow s)") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"&0 < s - &1 /\ s - &1 < exp(--((abs C + &1) / e))") STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"log(s - &1) < --((abs C + &1) / e)") ASSUME_TAC THENL [GEN_REWRITE_TAC RAND_CONV [(← GSYM LOG_EXP)] THEN MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [LOG_INV] THEN SUBGOAL_THEN (← q r"abs C + &1 < e * --log(s - &1)") ASSUME_TAC THENL [ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN ASM_SIMP_TAC [(← GSYM REAL_LT_LDIV_EQ)] THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"&0 < --log(s - &1)") ASSUME_TAC THENL [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (← q r"(abs C + &1) / e") THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC, ASM_REAL_ARITH_TAC], ALL_TAC] THEN SUBGOAL_THEN (← q r"ds / --log(s - &1) - d = (ds + d * log(s - &1)) / --log(s - &1)") SUBST1_TAC THENL [UNDISCH_TAC (← q r"&0 < --log(s - &1)") THEN CONV_TAC REAL_FIELD, ALL_TAC] THEN ASM_SIMP_TAC [REAL_ABS_DIV, r1, REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC)

  let HAS_DIRICHLET_DENSITY_UNIQUE ← prove
    r"!k:A ring S d d'.
        has_dirichlet_density k S d /\ has_dirichlet_density k S d'
        ==> d = d'"
    (REWRITE_TAC [has_dirichlet_density] THEN MESON_TAC [REALLIM_UNIQUE, (← SPEC (← q r"&1:real") TRIVIAL_LIMIT_ATREAL_RIGHT)])

  let HAS_DIRICHLET_DENSITY_FINITE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"&1 <= x:real ==> &0 < x")
    let r2 ← REAL_ARITH (← q r"&1 <= x ==> abs x = x:real")
    prove
      r"!k:A ring S. FINITE S ==> has_dirichlet_density k S (&0)"
      (REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DIRICHLET_DENSITY_LOG THEN ABBREV_TAC (← q r"NS = IMAGE (ideal_norm (ring_of_integers k)) (S:(A->bool)->bool)") THEN EXISTS_TAC (← q r"(&(CARD(NS:num->bool)) * &(CARD(S:(A->bool)->bool))):real") THEN X_GEN_TAC (← q r"s:real") THEN STRIP_TAC THEN REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_RID] THEN SUBGOAL_THEN (← q r"FINITE(NS:num->bool)") ASSUME_TAC THENL [EXPAND_TAC "NS" THEN ASM_SIMP_TAC [FINITE_IMAGE], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"\m. &(CARD {P | P IN (S:(A->bool)->bool) /\
                       ideal_norm (ring_of_integers k) P = m}) /
           &m rpow s"), (← q r"NS:num->bool"), (← q r"from 1")] REAL_SERIES_FINITE_SUPPORT) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_INTER] THEN X_GEN_TAC (← q r"m:num") THEN REWRITE_TAC [IN_INTER, IN_FROM, DE_MORGAN_THM] THEN STRIP_TAC THENL [SUBGOAL_THEN (← q r"{P | P IN S /\ ideal_norm (ring_of_integers k) P = m} =
          {}:(A->bool)->bool") (fun th => REWRITE_TAC [th, CARD_CLAUSES, real_div, REAL_MUL_LZERO]) THEN UNDISCH_TAC (← q r"~((m:num) IN NS)") THEN EXPAND_TAC "NS" THEN SET_TAC [], SUBGOAL_THEN (← q r"m = 0") SUBST1_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [RPOW_ZERO] THEN COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC, REWRITE_TAC [real_div, REAL_INV_0, REAL_MUL_RZERO]]], ALL_TAC] THEN DISCH_THEN (SUBST1_TAC o (MATCH_MP REAL_INFSUM_UNIQUE)) THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"(&(CARD(NS INTER from 1)) * &(CARD(S:(A->bool)->bool))):real") THEN CONJ_TAC THENL [MATCH_MP_TAC SUM_ABS_BOUND THEN ASM_SIMP_TAC [FINITE_INTER] THEN X_GEN_TAC (← q r"m:num") THEN REWRITE_TAC [IN_INTER, IN_FROM] THEN STRIP_TAC THEN REWRITE_TAC [REAL_ABS_DIV, REAL_ABS_NUM] THEN SUBGOAL_THEN (← q r"&1 <= &m rpow s") ASSUME_TAC THENL [MATCH_MP_TAC RPOW_LE_1 THEN ASM_REWRITE_TAC [REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN ASM_SIMP_TAC [r2, REAL_LE_LDIV_EQ, r1] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"(&(CARD(S:(A->bool)->bool))):real") THEN CONJ_TAC THENL [REWRITE_TAC [REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC [] THEN SET_TAC [], GEN_REWRITE_TAC LAND_CONV [(← GSYM REAL_MUL_RID)] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [REAL_POS]], MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [REAL_POS, REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC [INTER_SUBSET]])

  let HAS_DIRICHLET_DENSITY_INFINITE ← prove
    r"!k:A ring S d.
        has_dirichlet_density k S d /\ ~(d = &0) ==> INFINITE S"
    (REWRITE_TAC [INFINITE] THEN MESON_TAC [HAS_DIRICHLET_DENSITY_FINITE, HAS_DIRICHLET_DENSITY_UNIQUE])

  let NUMBER_FIELD_PRIME_IDEALS_DENSITY ← prove
    r"!k:A ring.
        number_field k
        ==> has_dirichlet_density k
             {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})}
             (&1)"
    (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DIRICHLET_DENSITY_LOG THEN FIRST_ASSUM (MP_TAC o (MATCH_MP NUMBER_FIELD_PRIME_IDEALS_LOG)) THEN REWRITE_TAC [IN_ELIM_THM, (← GSYM CONJ_ASSOC), REAL_MUL_LID] THEN MESON_TAC [])

  let NUMBER_FIELD_DEGREE_ONE_PRIMES_DENSITY ← prove
    r"!k:A ring.
        number_field k
        ==> has_dirichlet_density k
             {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
                  residue_degree (integer_ring,ring_of_integers k)
                    (ring_of_int k) P = 1}
             (&1)"
    (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DIRICHLET_DENSITY_LOG THEN FIRST_ASSUM (MP_TAC o (MATCH_MP NUMBER_FIELD_DEGREE_ONE_PRIMES_LOG)) THEN REWRITE_TAC [IN_ELIM_THM, (← GSYM CONJ_ASSOC), REAL_MUL_LID] THEN MESON_TAC [])

  -- @@RETURN BEGIN
  return { DEDEKIND_ZETA_LOG_PRIME_IDEALS, NUMBER_FIELD_NONPRIME_NORM_SUM_LE,
           DEDEKIND_ZETA_LOG_POLE, NUMBER_FIELD_PRIME_IDEALS_LOG,
           NUMBER_FIELD_DEGREE_ONE_PRIMES_LOG, has_dirichlet_density,
           HAS_DIRICHLET_DENSITY_LOG, HAS_DIRICHLET_DENSITY_UNIQUE,
           HAS_DIRICHLET_DENSITY_FINITE, HAS_DIRICHLET_DENSITY_INFINITE,
           NUMBER_FIELD_PRIME_IDEALS_DENSITY, NUMBER_FIELD_DEGREE_ONE_PRIMES_DENSITY }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- dedekind_zeta.ml phrases from line 2668 to 2884                        -/
/- ---------------------------------------------------------------------- -/

structure DedekindZeta05 where
  -- @@FIELDS
  NUMBER_FIELD_PRIME_IDEAL_DIRICHLET_SUMMABLE : thm
  HAS_DIRICHLET_DENSITY_DISJOINT_UNION : thm
  HAS_DIRICHLET_DENSITY_DIFF_SUBSET : thm
  HAS_DIRICHLET_DENSITY_COMPLEMENT : thm
  HAS_DIRICHLET_DENSITY_BOUNDS : thm
  HAS_DIRICHLET_DENSITY_SUBSET : thm
  HAS_DIRICHLET_DENSITY_FINITE_SYMDIFF : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekindZeta05 [HolBase] (D : DedekindZetaDeps) (BDedekindZeta02 : DedekindZeta02) (BDedekindZeta04 : DedekindZeta04) :
    ExceptT String IO DedekindZeta05 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC,
        SET_TAC, .. } := D
  let { ALWAYS_EVENTUALLY, CARD_SUBSET, CARD_UNION_EQ, EQ_IMP, EVENTUALLY_WITHINREAL,
        EVENTUALLY_WITHIN_IMP, FINITE_SUBSET, FINITE_UNION, FUN_EQ_THM, IMP_CONJ,
        IMP_IMP, IN_ELIM_THM, .. } := D.core1
  let { LE_REFL, LOG_POS_LT, NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM,
        PRIME_IMP_RING_IDEAL, REALLIM_ADD, REALLIM_LBOUND, REALLIM_SUB,
        REALLIM_TRANSFORM_EVENTUALLY, REAL_ABS_DIV, REAL_ABS_NUM, REAL_ABS_RPOW,
        REAL_ADD_RDISTRIB, REAL_ADD_RID, REAL_INFSUM_ADD, REAL_INV_1_LT, REAL_LE_DIV,
        REAL_LE_INV_EQ, REAL_LE_RMUL, REAL_LT_01, REAL_LT_IMP_LE, REAL_OF_NUM_ADD,
        REAL_OF_NUM_LE, .. } := D.core2
  let { REAL_POS, REAL_SERIES_POS, REAL_SUB_RDISTRIB, REAL_SUB_RZERO,
        REAL_SUMMABLE_COMPARISON, REAL_SUMS_INFSUM, RPOW_POS_LE, SUBSET, SUBSET_DIFF,
        SUBSET_REFL, TRIVIAL_LIMIT_ATREAL_RIGHT, UNION_COMM, real_div, .. } := D.core3
  let { NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE, .. } := BDedekindZeta02
  let { HAS_DIRICHLET_DENSITY_FINITE, NUMBER_FIELD_PRIME_IDEALS_DENSITY,
        has_dirichlet_density, .. } := BDedekindZeta04
  -- @@SCOPE END

  let NUMBER_FIELD_PRIME_IDEAL_DIRICHLET_SUMMABLE ← prove
    r"!k:A ring S.
        number_field k /\
        S SUBSET {P | prime_ideal (ring_of_integers k) P /\
                      ~(P = {ring_0 k})}
        ==> (!m. FINITE {P | P IN S /\
                             ideal_norm (ring_of_integers k) P = m}) /\
            (!s. &1 < s
                 ==> real_summable (from 1)
                      (\m. &(CARD {P | P IN S /\
                                       ideal_norm (ring_of_integers k) P =
                                       m}) /
                           &m rpow s))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!m. {P | P IN S /\ ideal_norm (ring_of_integers k) P = m} SUBSET
        {j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
             ideal_norm (ring_of_integers k) (j:A->bool) = m} /\
        FINITE {j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
                    ideal_norm (ring_of_integers k) (j:A->bool) = m}") ASSUME_TAC THENL [X_GEN_TAC (← q r"m:num") THEN CONJ_TAC THENL [UNDISCH_TAC (← q r"S SUBSET {P | prime_ideal (ring_of_integers k) P /\
                      ~(P = {ring_0(k:A ring)})}") THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN MESON_TAC [PRIME_IMP_RING_IDEAL], MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
             ideal_norm (ring_of_integers k) (j:A->bool) <= m}") THEN ASM_SIMP_TAC [NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN SIMP_TAC [SUBSET, IN_ELIM_THM, LE_REFL]], ALL_TAC] THEN CONJ_TAC THENL [ASM_MESON_TAC [FINITE_SUBSET], ALL_TAC] THEN X_GEN_TAC (← q r"s:real") THEN DISCH_TAC THEN MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN EXISTS_TAC (← q r"\m. &(CARD {j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
                    ideal_norm (ring_of_integers k) (j:A->bool) = m}) /
        &m rpow s") THEN ASM_SIMP_TAC [NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE] THEN EXISTS_TAC (← q r"0") THEN X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN REWRITE_TAC [REAL_ABS_DIV, REAL_ABS_NUM, REAL_ABS_RPOW] THEN REWRITE_TAC [real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC [REAL_LE_INV_EQ, RPOW_POS_LE, REAL_POS, REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC [])

  let HAS_DIRICHLET_DENSITY_DISJOINT_UNION ← prove
    r"!k:A ring S1 S2 d1 d2.
        number_field k /\
        S1 SUBSET {P | prime_ideal (ring_of_integers k) P /\
                       ~(P = {ring_0 k})} /\
        S2 SUBSET {P | prime_ideal (ring_of_integers k) P /\
                       ~(P = {ring_0 k})} /\
        has_dirichlet_density k S1 d1 /\ has_dirichlet_density k S2 d2 /\
        DISJOINT S1 S2
        ==> has_dirichlet_density k (S1 UNION S2) (d1 + d2)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"S2:(A->bool)->bool")] NUMBER_FIELD_PRIME_IDEAL_DIRICHLET_SUMMABLE) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"S1:(A->bool)->bool")] NUMBER_FIELD_PRIME_IDEAL_DIRICHLET_SUMMABLE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN STRIP_TAC THEN UNDISCH_TAC (← q r"has_dirichlet_density (k:A ring) S2 d2") THEN UNDISCH_TAC (← q r"has_dirichlet_density (k:A ring) S1 d1") THEN REWRITE_TAC [has_dirichlet_density, IMP_IMP] THEN DISCH_THEN (MP_TAC o (MATCH_MP REALLIM_ADD)) THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] REALLIM_TRANSFORM_EVENTUALLY) THEN REWRITE_TAC [EVENTUALLY_WITHIN_IMP] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC (← q r"s:real") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC [real_div, (← GSYM REAL_ADD_RDISTRIB)] THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [(← GSYM real_div)] THEN MP_TAC (← ISPECL [(← q r"\m. &(CARD {P | P IN S1 /\
                     ideal_norm (ring_of_integers k) (P:A->bool) = m}) /
         &m rpow s"), (← q r"\m. &(CARD {P | P IN S2 /\
                     ideal_norm (ring_of_integers k) (P:A->bool) = m}) /
         &m rpow s"), (← q r"from 1")] REAL_INFSUM_ADD) THEN ASM_SIMP_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"m:num") THEN REWRITE_TAC [real_div, (← GSYM REAL_ADD_RDISTRIB), REAL_OF_NUM_ADD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC CARD_UNION_EQ THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{P | P IN S1 /\ ideal_norm (ring_of_integers k) P = m} UNION
      {P | P IN S2 /\ ideal_norm (ring_of_integers k) (P:A->bool) = m}") THEN ASM_REWRITE_TAC [FINITE_UNION] THEN SET_TAC [], UNDISCH_TAC (← q r"DISJOINT (S1:(A->bool)->bool) S2") THEN SET_TAC [], SET_TAC []])

  let HAS_DIRICHLET_DENSITY_DIFF_SUBSET ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"x:real = y + z ==> x - y = z")
    prove
      r"!k:A ring S1 S2 d1 d2.
          number_field k /\
          S1 SUBSET {P | prime_ideal (ring_of_integers k) P /\
                         ~(P = {ring_0 k})} /\
          has_dirichlet_density k S1 d1 /\ has_dirichlet_density k S2 d2 /\
          S2 SUBSET S1
          ==> has_dirichlet_density k (S1 DIFF S2) (d1 - d2)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"S1 DIFF S2:(A->bool)->bool")] NUMBER_FIELD_PRIME_IDEAL_DIRICHLET_SUMMABLE) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"S2:(A->bool)->bool")] NUMBER_FIELD_PRIME_IDEAL_DIRICHLET_SUMMABLE) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"S1:(A->bool)->bool")] NUMBER_FIELD_PRIME_IDEAL_DIRICHLET_SUMMABLE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ANTS_TAC THENL [ASM SET_TAC [], STRIP_TAC] THEN ANTS_TAC THENL [ASM SET_TAC [], STRIP_TAC] THEN UNDISCH_TAC (← q r"has_dirichlet_density (k:A ring) S2 d2") THEN UNDISCH_TAC (← q r"has_dirichlet_density (k:A ring) S1 d1") THEN REWRITE_TAC [has_dirichlet_density, IMP_IMP] THEN DISCH_THEN (MP_TAC o (MATCH_MP REALLIM_SUB)) THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] REALLIM_TRANSFORM_EVENTUALLY) THEN REWRITE_TAC [EVENTUALLY_WITHIN_IMP] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC (← q r"s:real") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC [real_div, (← GSYM REAL_SUB_RDISTRIB)] THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [(← GSYM real_div)] THEN MATCH_MP_TAC r1 THEN MP_TAC (← ISPECL [(← q r"\m. &(CARD {P | P IN S2 /\
                       ideal_norm (ring_of_integers k) (P:A->bool) = m}) /
           &m rpow s"), (← q r"\m. &(CARD {P | P IN S1 DIFF S2 /\
                       ideal_norm (ring_of_integers k) (P:A->bool) = m}) /
           &m rpow s"), (← q r"from 1")] REAL_INFSUM_ADD) THEN ASM_SIMP_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"m:num") THEN REWRITE_TAC [real_div, (← GSYM REAL_ADD_RDISTRIB), REAL_OF_NUM_ADD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC [])

  let HAS_DIRICHLET_DENSITY_COMPLEMENT ← prove
    r"!k:A ring S d.
        number_field k /\
        S SUBSET {P | prime_ideal (ring_of_integers k) P /\
                      ~(P = {ring_0 k})} /\
        has_dirichlet_density k S d
        ==> has_dirichlet_density k
             ({P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})}
              DIFF S)
             (&1 - d)"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DIRICHLET_DENSITY_DIFF_SUBSET THEN ASM_SIMP_TAC [SUBSET_REFL, NUMBER_FIELD_PRIME_IDEALS_DENSITY])

  let HAS_DIRICHLET_DENSITY_BOUNDS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"&0 <= &1 - d ==> (d:real) <= &1")
    prove
      r"!k:A ring S d.
          number_field k /\
          S SUBSET {P | prime_ideal (ring_of_integers k) P /\
                        ~(P = {ring_0 k})} /\
          has_dirichlet_density k S d
          ==> &0 <= d /\ d <= &1"
      (SUBGOAL_THEN (← q r"!k:A ring S d.
          number_field k /\
          S SUBSET {P | prime_ideal (ring_of_integers k) P /\
                        ~(P = {ring_0 k})} /\
          has_dirichlet_density k S d
          ==> &0 <= d") ASSUME_TAC THENL [REPEAT GEN_TAC THEN REWRITE_TAC [has_dirichlet_density] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"S:(A->bool)->bool")] NUMBER_FIELD_PRIME_IDEAL_DIRICHLET_SUMMABLE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC (← ISPEC (← q r"atreal (&1) within {s | &1 < s}") REALLIM_LBOUND) THEN EXISTS_TAC (← q r"\s. real_infsum (from 1)
              (\m. &(CARD {P | P IN S /\
                               ideal_norm (ring_of_integers k) (P:A->bool) =
                               m}) /
                   &m rpow s) /
            log(inv(s - &1))") THEN ASM_REWRITE_TAC [TRIVIAL_LIMIT_ATREAL_RIGHT] THEN REWRITE_TAC [EVENTUALLY_WITHINREAL, IN_ELIM_THM] THEN EXISTS_TAC (← q r"&1:real") THEN REWRITE_TAC [REAL_LT_01] THEN X_GEN_TAC (← q r"s:real") THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_SERIES_POS THEN MAP_EVERY EXISTS_TAC [(← q r"\m. &(CARD {P | P IN S /\
                           ideal_norm (ring_of_integers k) (P:A->bool) = m}) /
               &m rpow s"), (← q r"from 1")] THEN ASM_SIMP_TAC [REAL_SUMS_INFSUM, REAL_LE_DIV, REAL_POS, RPOW_POS_LE], MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC LOG_POS_LT THEN MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REAL_ARITH_TAC], REPEAT STRIP_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN MATCH_MP_TAC r1 THEN FIRST_X_ASSUM (MATCH_MP_TAC o (SPECL [(← q r"k:A ring"), (← q r"{P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})} DIFF
         (S:(A->bool)->bool)")])) THEN ASM_SIMP_TAC [HAS_DIRICHLET_DENSITY_COMPLEMENT, SUBSET_DIFF]])

  let HAS_DIRICHLET_DENSITY_SUBSET ← prove
    r"!k:A ring S1 S2 d1 d2.
        number_field k /\
        S2 SUBSET {P | prime_ideal (ring_of_integers k) P /\
                       ~(P = {ring_0 k})} /\
        has_dirichlet_density k S1 d1 /\ has_dirichlet_density k S2 d2 /\
        S1 SUBSET S2
        ==> d1 <= d2"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"S2:(A->bool)->bool"), (← q r"S1:(A->bool)->bool"), (← q r"d2:real"), (← q r"d1:real")] HAS_DIRICHLET_DENSITY_DIFF_SUBSET) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"S2 DIFF S1:(A->bool)->bool"), (← q r"d2 - d1:real")] HAS_DIRICHLET_DENSITY_BOUNDS) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM SET_TAC [], REAL_ARITH_TAC])

  let HAS_DIRICHLET_DENSITY_FINITE_SYMDIFF ← prove
    r"!k:A ring S1 S2 d.
        number_field k /\
        S1 SUBSET {P | prime_ideal (ring_of_integers k) P /\
                       ~(P = {ring_0 k})} /\
        S2 SUBSET {P | prime_ideal (ring_of_integers k) P /\
                       ~(P = {ring_0 k})} /\
        FINITE((S1 DIFF S2) UNION (S2 DIFF S1))
        ==> (has_dirichlet_density k S1 d <=> has_dirichlet_density k S2 d)"
    (SUBGOAL_THEN (← q r"!k:A ring S1 S2 d.
        number_field k /\
        S1 SUBSET {P | prime_ideal (ring_of_integers k) P /\
                       ~(P = {ring_0 k})} /\
        S2 SUBSET {P | prime_ideal (ring_of_integers k) P /\
                       ~(P = {ring_0 k})} /\
        FINITE((S1 DIFF S2) UNION (S2 DIFF S1)) /\
        has_dirichlet_density k S1 d
        ==> has_dirichlet_density k S2 d") (fun th => MESON_TAC [th, UNION_COMM]) THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"has_dirichlet_density (k:A ring)
     ((S1 DIFF (S1 DIFF S2)) UNION (S2 DIFF S1)) ((d - &0) + &0)") MP_TAC THENL [MATCH_MP_TAC HAS_DIRICHLET_DENSITY_DISJOINT_UNION THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [ASM SET_TAC [], ASM SET_TAC [], MATCH_MP_TAC HAS_DIRICHLET_DENSITY_DIFF_SUBSET THEN ASM_REWRITE_TAC [SUBSET_DIFF] THEN MATCH_MP_TAC HAS_DIRICHLET_DENSITY_FINITE THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"(S1 DIFF S2) UNION (S2 DIFF S1):(A->bool)->bool") THEN ASM_REWRITE_TAC [] THEN SET_TAC [], MATCH_MP_TAC HAS_DIRICHLET_DENSITY_FINITE THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"(S1 DIFF S2) UNION (S2 DIFF S1):(A->bool)->bool") THEN ASM_REWRITE_TAC [] THEN SET_TAC [], SET_TAC []], REWRITE_TAC [REAL_SUB_RZERO, REAL_ADD_RID] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC []])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_PRIME_IDEAL_DIRICHLET_SUMMABLE,
           HAS_DIRICHLET_DENSITY_DISJOINT_UNION, HAS_DIRICHLET_DENSITY_DIFF_SUBSET,
           HAS_DIRICHLET_DENSITY_COMPLEMENT, HAS_DIRICHLET_DENSITY_BOUNDS,
           HAS_DIRICHLET_DENSITY_SUBSET, HAS_DIRICHLET_DENSITY_FINITE_SYMDIFF }
  -- @@RETURN END

end HolANT.DedekindZeta
