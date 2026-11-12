/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/dedekind_zeta.ml                              . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/DedekindZeta.lean

  The session half of the dedekind_zeta.ml translation: it supplies HolANT.DedekindZeta's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/dedekind_zeta.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.DedekindZeta
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Matroids
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionLibrary.FieldTheory
import SessionLibrary.Products
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.Floor
import SessionMultiLib.Misc
import SessionMultiLib.Metric
import SessionMultiLib.Homology
import SessionMultiLib.Vectors
import SessionMultiLib.Determinants
import SessionMultiLib.Topology
import SessionMultiLib.Convex
import SessionMultiLib.Paths
import SessionMultiLib.Polytope
import SessionMultiLib.Degree
import SessionMultiLib.Derivatives
import SessionMultiLib.Integration
import SessionMultiLib.Measure
import SessionMultiLib.ComplexAlgebra
import SessionMultiLib.Complexes
import SessionMultiLib.Canal
import SessionMultiLib.Transcendentals
import SessionMultiLib.RealAnalysis
import SessionANT.Algmisc
import SessionANT.IdealArith
import SessionANT.Integral
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionANT.Numfield
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionANT.Classgroup
import SessionANT.PrimeSplit
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.NfValuation
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.Integrality
import SessionLibrary.RingGroups
import SessionANT.FingenGroup
import SessionMultiLib.MoreTop
import SessionMultiLib.Cauchy
import SessionMultiLib.ComplexRing
import SessionMultiLib.ComplexField
import SessionANT.ComplexEmbeddings
import SessionANT.PowerBasis
import SessionANT.InfinitePlaces

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.DedekindZeta

/-- The core theorems dedekind_zeta.ml uses. -/
def core1 : HolANT.DedekindZeta.CoreThms1 where
  ADD_CLAUSES := Session.ADD_CLAUSES
  ADD_SUB := Session.ADD_SUB
  ALWAYS_EVENTUALLY := SessionMultiLib.Metric.«ALWAYS_EVENTUALLY»
  ARITH := Session.ARITH
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_CROSS := Session.CARD_CROSS
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_SUBSET := Session.CARD_SUBSET
  CARD_UNION_EQ := Session.CARD_UNION_EQ
  COMPLEX_CMUL := SessionMultiLib.ComplexAlgebra.«COMPLEX_CMUL»
  COMPLEX_EMBEDDINGS_HAS_SIZE := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_HAS_SIZE»
  COMPLEX_MUL_LID := SessionMultiLib.ComplexAlgebra.«COMPLEX_MUL_LID»
  COMPLEX_NORM_0 := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_0»
  COMPLEX_NORM_CX := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_CX»
  COMPLEX_NORM_DIV := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_DIV»
  COMPLEX_NORM_INV := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_INV»
  COMPLEX_NORM_MUL := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_MUL»
  COMPLEX_POW_INV := SessionMultiLib.ComplexAlgebra.«COMPLEX_POW_INV»
  COMPLEX_RING_CLAUSES := SessionMultiLib.ComplexRing.«COMPLEX_RING_CLAUSES»
  COMPLEX_RING_OF_INT := SessionMultiLib.ComplexRing.«COMPLEX_RING_OF_INT»
  COMPLEX_RING_OF_NUM := SessionMultiLib.ComplexRing.«COMPLEX_RING_OF_NUM»
  COMPLEX_RING_SUM := SessionMultiLib.ComplexRing.«COMPLEX_RING_SUM»
  COMPLEX_SUB_RDISTRIB := SessionMultiLib.ComplexAlgebra.«COMPLEX_SUB_RDISTRIB»
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONVERGENT_REAL_BOUNDED_MONOTONE := SessionMultiLib.RealAnalysis.«CONVERGENT_REAL_BOUNDED_MONOTONE»
  CPOW_NPRODUCT := SessionMultiLib.Transcendentals.«CPOW_NPRODUCT»
  CPOW_NUM_EXP := SessionMultiLib.Transcendentals.«CPOW_NUM_EXP»
  CPRODUCT_EQ := SessionMultiLib.ComplexAlgebra.«CPRODUCT_EQ»
  CPRODUCT_INV := SessionMultiLib.ComplexAlgebra.«CPRODUCT_INV»
  CPRODUCT_VSUM_POW := SessionMultiLib.Transcendentals.«CPRODUCT_VSUM_POW»
  CX_DIV := SessionMultiLib.ComplexAlgebra.«CX_DIV»
  CX_INV := SessionMultiLib.ComplexAlgebra.«CX_INV»
  CX_PRODUCT := SessionMultiLib.ComplexAlgebra.«CX_PRODUCT»
  CX_RPOW := SessionMultiLib.Transcendentals.«CX_RPOW»
  CX_SUB := SessionMultiLib.ComplexAlgebra.«CX_SUB»
  DEDEKIND_IDEAL_EQ_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_EQ_VALUATION»
  DEDEKIND_IDEAL_NORM_PRIME_POWERS := SessionANT.IdealNorm.«DEDEKIND_IDEAL_NORM_PRIME_POWERS»
  DEDEKIND_IDEAL_PRODUCT_PRIME_POWERS := SessionANT.Dedekind.«DEDEKIND_IDEAL_PRODUCT_PRIME_POWERS»
  DEDEKIND_IDEAL_PROD_CANCEL := SessionANT.Dedekind.«DEDEKIND_IDEAL_PROD_CANCEL»
  DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES»
  DEDEKIND_IDEAL_SUBSET_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_POW_VALUATION»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIVIDES_LE_IMP := Session.DIVIDES_LE_IMP
  DIVISION := Session.DIVISION
  DIV_MUL_LE := Session.DIV_MUL_LE
  EQ_IMP := Session.EQ_IMP
  EQ_IMP_LE := Session.EQ_IMP_LE
  EQ_TRANS := Session.EQ_TRANS
  ETA_AX := Session.ETA_AX
  EVENTUALLY_SEQUENTIALLY := SessionMultiLib.Metric.«EVENTUALLY_SEQUENTIALLY»
  EVENTUALLY_TRUE := SessionMultiLib.Metric.«EVENTUALLY_TRUE»
  EVENTUALLY_WITHINREAL := SessionMultiLib.RealAnalysis.«EVENTUALLY_WITHINREAL»
  EVENTUALLY_WITHIN_IMP := SessionMultiLib.Metric.«EVENTUALLY_WITHIN_IMP»
  EXP_1 := Session.EXP_1
  EXP_2 := Session.EXP_2
  EXP_MONO_LE := Session.EXP_MONO_LE
  EXP_ONE := Session.EXP_ONE
  EXTENSION := Session.EXTENSION
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FINITE_COMPLEX_EMBEDDINGS := SessionANT.ComplexEmbeddings.«FINITE_COMPLEX_EMBEDDINGS»
  FINITE_CROSS := Session.FINITE_CROSS
  FINITE_FUNSPACE := Session.FINITE_FUNSPACE
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INTER := Session.FINITE_INTER
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNION := Session.FINITE_UNION
  FORALL_AND_THM := Session.FORALL_AND_THM
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FREE_BASIS_IDEAL_BOX_PRINCIPLE := SessionANT.Classgroup.«FREE_BASIS_IDEAL_BOX_PRINCIPLE»
  FREE_BASIS_INTEGER_RING_LINCOMB := SessionANT.Discriminant.«FREE_BASIS_INTEGER_RING_LINCOMB»
  FREE_BASIS_IN_CARRIER := SessionLibrary.RingDet.«FREE_BASIS_IN_CARRIER»
  FREE_BASIS_NORM_BOUND := SessionANT.Classgroup.«FREE_BASIS_NORM_BOUND»
  FROM_0 := SessionMultiLib.Misc.«FROM_0»
  FROM_INTER_NUMSEG := SessionMultiLib.Misc.«FROM_INTER_NUMSEG»
  FUN_EQ_THM := Session.FUN_EQ_THM
  GE := Session.GE
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_CARD := Session.HAS_SIZE_CARD
  HAS_SIZE_FUNSPACE := Session.HAS_SIZE_FUNSPACE
  HAS_SIZE_INT_ABS_LE := SessionLibrary.Isum.«HAS_SIZE_INT_ABS_LE»
  HAS_SIZE_NUMSEG := Session.HAS_SIZE_NUMSEG
  HAS_SIZE_NUMSEG_LT := Session.HAS_SIZE_NUMSEG_LT
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_NORM_CARRIER := SessionANT.IdealNorm.«IDEAL_NORM_CARRIER»
  IDEAL_NORM_GT_1 := SessionANT.IdealNorm.«IDEAL_NORM_GT_1»
  IDEAL_NORM_IDEAL_POW := SessionANT.IdealNorm.«IDEAL_NORM_IDEAL_POW»
  IDEAL_NORM_POS := SessionANT.IdealNorm.«IDEAL_NORM_POS»
  IDEAL_NORM_SUBSET_DIVIDES := SessionANT.IdealNorm.«IDEAL_NORM_SUBSET_DIVIDES»
  IDEAL_PROD_COMM := SessionANT.IdealArith.«IDEAL_PROD_COMM»
  IDEAL_PROD_EQ_ZERO := SessionANT.IdealArith.«IDEAL_PROD_EQ_ZERO»
  IMP_CONJ := Session.IMP_CONJ
  IMP_IMP := Session.IMP_IMP
  INFINITE := Session.INFINITE
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGRAL_DOMAIN_RING_OF_INTEGERS := SessionANT.Numfield.«INTEGRAL_DOMAIN_RING_OF_INTEGERS»
  INTER_SUBSET := Session.INTER_SUBSET
  INTER_UNIV := Session.INTER_UNIV
  INT_ABS_POS := Session.INT_ABS_POS
  INT_LE_LMUL := Session.INT_LE_LMUL
  INT_LE_LMUL_EQ := Session.INT_LE_LMUL_EQ
  INT_LE_MUL := Session.INT_LE_MUL
  INT_LE_REFL := Session.INT_LE_REFL
  INT_LE_TRANS := Session.INT_LE_TRANS
  INT_MUL_AC := Session.INT_MUL_AC
  INT_OF_NUM_LE := Session.INT_OF_NUM_LE
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_OF_NUM_POW := Session.INT_OF_NUM_POW
  INT_POS := Session.INT_POS
  INT_POW_LE := Session.INT_POW_LE
  INT_POW_MUL := Session.INT_POW_MUL
  IN_CROSS := Session.IN_CROSS
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_FROM := SessionMultiLib.Misc.«IN_FROM»
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_IDEAL_GENERATED_SING_EQ := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SING_EQ»
  IN_IMAGE := Session.IN_IMAGE
  IN_INTER := Session.IN_INTER
  IN_NUMSEG := Session.IN_NUMSEG
  IN_SING := Session.IN_SING
  IN_UNIV := Session.IN_UNIV
  LE := Session.LE
  LEFT_ADD_DISTRIB := Session.LEFT_ADD_DISTRIB
/-- The core theorems dedekind_zeta.ml uses. -/
def core2 : HolANT.DedekindZeta.CoreThms2 where
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_0 := Session.LE_0
  LE_1 := Session.LE_1
  LE_EXP := Session.LE_EXP
  LE_MULT2 := Session.LE_MULT2
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  LE_MULT_RCANCEL := Session.LE_MULT_RCANCEL
  LE_REFL := Session.LE_REFL
  LE_SQUARE_REFL := Session.LE_SQUARE_REFL
  LE_TRANS := Session.LE_TRANS
  LIM_CONST := SessionMultiLib.Topology.«LIM_CONST»
  LIM_CPRODUCT := SessionMultiLib.Transcendentals.«LIM_CPRODUCT»
  LIM_NORM_UBOUND := SessionMultiLib.Topology.«LIM_NORM_UBOUND»
  LIM_SEQUENTIALLY := SessionMultiLib.Topology.«LIM_SEQUENTIALLY»
  LIM_SUB := SessionMultiLib.Topology.«LIM_SUB»
  LOG_DIV := SessionMultiLib.Transcendentals.«LOG_DIV»
  LOG_EXP := SessionMultiLib.Transcendentals.«LOG_EXP»
  LOG_INV := SessionMultiLib.Transcendentals.«LOG_INV»
  LOG_MONO_LE_IMP := SessionMultiLib.Transcendentals.«LOG_MONO_LE_IMP»
  LOG_MONO_LT_IMP := SessionMultiLib.Transcendentals.«LOG_MONO_LT_IMP»
  LOG_POS_LT := SessionMultiLib.Transcendentals.«LOG_POS_LT»
  LTE_TRANS := Session.LTE_TRANS
  LT_IMP_LE := Session.LT_IMP_LE
  LT_NZ := Session.LT_NZ
  LT_POW2_REFL := Session.LT_POW2_REFL
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_AC := Session.MULT_AC
  MULT_ASSOC := Session.MULT_ASSOC
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EXP := Session.MULT_EXP
  MULT_SYM := Session.MULT_SYM
  NORM_CPOW := SessionMultiLib.Transcendentals.«NORM_CPOW»
  NORM_POS_LE := SessionMultiLib.Vectors.«NORM_POS_LE»
  NOT_LT := Session.NOT_LT
  NUMBER_FIELD_DEGREE_POS := SessionANT.Numfield.«NUMBER_FIELD_DEGREE_POS»
  NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM := SessionANT.Classgroup.«NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM»
  NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM := SessionANT.Classgroup.«NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM»
  NUMBER_FIELD_IDEAL_NORM_MUL_Q := SessionANT.NormIndex.«NUMBER_FIELD_IDEAL_NORM_MUL_Q»
  NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS := SessionANT.InfinitePlaces.«NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS»
  NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q := SessionANT.NormIndex.«NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_NORM_INTEGRAL_BASIS := SessionANT.NormIndex.«NUMBER_FIELD_NORM_INTEGRAL_BASIS»
  NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q := SessionANT.PrimeSplit.«NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q»
  NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE := SessionANT.PrimeSplit.«NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE»
  NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2 := SessionANT.Classgroup.«NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2»
  NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q := SessionANT.PrimeSplit.«NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q»
  NUM_ROOT_FLOOR := SessionANT.Algmisc.«NUM_ROOT_FLOOR»
  PAIR_EQ := Session.PAIR_EQ
  PRIME_GE_2 := SessionLibrary.Prime.«PRIME_GE_2»
  PRIME_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_PROPER_IDEAL»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRODUCT_CONST := SessionLibrary.Products.«PRODUCT_CONST»
  PRODUCT_LE := SessionLibrary.Products.«PRODUCT_LE»
  PROPER_IDEAL_ALT := SessionLibrary.RingTheory.«PROPER_IDEAL_ALT»
  REALLIM_ADD := SessionMultiLib.RealAnalysis.«REALLIM_ADD»
  REALLIM_COMPLEX := SessionMultiLib.RealAnalysis.«REALLIM_COMPLEX»
  REALLIM_CONST := SessionMultiLib.RealAnalysis.«REALLIM_CONST»
  REALLIM_LBOUND := SessionMultiLib.RealAnalysis.«REALLIM_LBOUND»
  REALLIM_LE := SessionMultiLib.RealAnalysis.«REALLIM_LE»
  REALLIM_LMUL := SessionMultiLib.RealAnalysis.«REALLIM_LMUL»
  REALLIM_REAL_CONTINUOUS_FUNCTION := SessionMultiLib.RealAnalysis.«REALLIM_REAL_CONTINUOUS_FUNCTION»
  REALLIM_SEQUENTIALLY := SessionMultiLib.RealAnalysis.«REALLIM_SEQUENTIALLY»
  REALLIM_SUB := SessionMultiLib.RealAnalysis.«REALLIM_SUB»
  REALLIM_TRANSFORM_EVENTUALLY := SessionMultiLib.RealAnalysis.«REALLIM_TRANSFORM_EVENTUALLY»
  REALLIM_UBOUND := SessionMultiLib.RealAnalysis.«REALLIM_UBOUND»
  REALLIM_UNIQUE := SessionMultiLib.RealAnalysis.«REALLIM_UNIQUE»
  REALLIM_WITHINREAL := SessionMultiLib.RealAnalysis.«REALLIM_WITHINREAL»
  REAL_ABS_DIV := Session.REAL_ABS_DIV
  REAL_ABS_LE := Session.REAL_ABS_LE
  REAL_ABS_MUL := Session.REAL_ABS_MUL
  REAL_ABS_NUM := Session.REAL_ABS_NUM
  REAL_ABS_POS := Session.REAL_ABS_POS
  REAL_ABS_RPOW := SessionMultiLib.Transcendentals.«REAL_ABS_RPOW»
  REAL_ADD_LDISTRIB := Session.REAL_ADD_LDISTRIB
  REAL_ADD_LID := Session.REAL_ADD_LID
  REAL_ADD_RDISTRIB := Session.REAL_ADD_RDISTRIB
  REAL_ADD_RID := Session.REAL_ADD_RID
  REAL_ARCH_SIMPLE := Session.REAL_ARCH_SIMPLE
  REAL_BOUNDED_POS := SessionMultiLib.Metric.«REAL_BOUNDED_POS»
  REAL_CONTINUOUS_AT_EXP := SessionMultiLib.RealAnalysis.«REAL_CONTINUOUS_AT_EXP»
  REAL_CX := SessionMultiLib.ComplexAlgebra.«REAL_CX»
  REAL_EQ_IMP_LE := Session.REAL_EQ_IMP_LE
  REAL_EXP_LE_INV_1_SUB := SessionMultiLib.Transcendentals.«REAL_EXP_LE_INV_1_SUB»
  REAL_EXP_MONO_LE := SessionMultiLib.Transcendentals.«REAL_EXP_MONO_LE»
  REAL_EXP_POS_LE := SessionMultiLib.Transcendentals.«REAL_EXP_POS_LE»
  REAL_EXP_POS_LT := SessionMultiLib.Transcendentals.«REAL_EXP_POS_LT»
  REAL_EXP_SUM := SessionMultiLib.Transcendentals.«REAL_EXP_SUM»
  REAL_INFSUM_ADD := SessionMultiLib.RealAnalysis.«REAL_INFSUM_ADD»
  REAL_INFSUM_SUB := SessionMultiLib.RealAnalysis.«REAL_INFSUM_SUB»
  REAL_INFSUM_UNIQUE := SessionMultiLib.RealAnalysis.«REAL_INFSUM_UNIQUE»
  REAL_INFSUM_ZETA_BOUNDS := SessionMultiLib.RealAnalysis.«REAL_INFSUM_ZETA_BOUNDS»
  REAL_INV_0 := Session.REAL_INV_0
  REAL_INV_1 := Session.REAL_INV_1
  REAL_INV_1_LT := Session.REAL_INV_1_LT
  REAL_INV_1_SUB_LE_EXP := SessionMultiLib.Transcendentals.«REAL_INV_1_SUB_LE_EXP»
  REAL_INV_LE_1 := Session.REAL_INV_LE_1
  REAL_INV_LT_1 := Session.REAL_INV_LT_1
  REAL_LET_TRANS := Session.REAL_LET_TRANS
  REAL_LE_ADD2 := Session.REAL_LE_ADD2
  REAL_LE_ADDR := Session.REAL_LE_ADDR
  REAL_LE_DIV := Session.REAL_LE_DIV
  REAL_LE_INV2 := Session.REAL_LE_INV2
  REAL_LE_INV_EQ := Session.REAL_LE_INV_EQ
  REAL_LE_LDIV_EQ := Session.REAL_LE_LDIV_EQ
  REAL_LE_LMUL := Session.REAL_LE_LMUL
  REAL_LE_LMUL_EQ := Session.REAL_LE_LMUL_EQ
  REAL_LE_MUL := Session.REAL_LE_MUL
  REAL_LE_REFL := Session.REAL_LE_REFL
  REAL_LE_RMUL := Session.REAL_LE_RMUL
  REAL_LE_TRANS := Session.REAL_LE_TRANS
  REAL_LT_01 := Session.REAL_LT_01
  REAL_LT_DIV := Session.REAL_LT_DIV
  REAL_LT_IMP_LE := Session.REAL_LT_IMP_LE
  REAL_LT_INV_EQ := Session.REAL_LT_INV_EQ
  REAL_LT_LDIV_EQ := Session.REAL_LT_LDIV_EQ
  REAL_LT_MIN := Session.REAL_LT_MIN
  REAL_LT_RDIV_EQ := Session.REAL_LT_RDIV_EQ
  REAL_LT_TRANS := Session.REAL_LT_TRANS
  REAL_MUL_ASSOC := Session.REAL_MUL_ASSOC
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_LZERO := Session.REAL_MUL_LZERO
  REAL_MUL_RID := Session.REAL_MUL_RID
  REAL_MUL_RZERO := Session.REAL_MUL_RZERO
  REAL_MUL_SYM := Session.REAL_MUL_SYM
  REAL_OF_INT_CLAUSES := Session.REAL_OF_INT_CLAUSES
  REAL_OF_NUM_ADD := Session.REAL_OF_NUM_ADD
  REAL_OF_NUM_LE := Session.REAL_OF_NUM_LE
  REAL_OF_NUM_LT := Session.REAL_OF_NUM_LT
  REAL_OF_NUM_MUL := Session.REAL_OF_NUM_MUL
  REAL_OF_NUM_POW := Session.REAL_OF_NUM_POW
/-- The core theorems dedekind_zeta.ml uses. -/
def core3 : HolANT.DedekindZeta.CoreThms3 where
  REAL_PARTIAL_SUMS_LE_INFSUM := SessionMultiLib.RealAnalysis.«REAL_PARTIAL_SUMS_LE_INFSUM»
  REAL_POS := Session.REAL_POS
  REAL_POW_1 := Session.REAL_POW_1
  REAL_POW_2 := Session.REAL_POW_2
  REAL_POW_INV := Session.REAL_POW_INV
  REAL_POW_LE := Session.REAL_POW_LE
  REAL_POW_LE2 := Session.REAL_POW_LE2
  REAL_POW_LT := Session.REAL_POW_LT
  REAL_SERIES_FINITE_SUPPORT := SessionMultiLib.RealAnalysis.«REAL_SERIES_FINITE_SUPPORT»
  REAL_SERIES_FROM := SessionMultiLib.RealAnalysis.«REAL_SERIES_FROM»
  REAL_SERIES_POS := SessionMultiLib.RealAnalysis.«REAL_SERIES_POS»
  REAL_SUB_LE := Session.REAL_SUB_LE
  REAL_SUB_RDISTRIB := Session.REAL_SUB_RDISTRIB
  REAL_SUB_REFL := Session.REAL_SUB_REFL
  REAL_SUB_RZERO := Session.REAL_SUB_RZERO
  REAL_SUMMABLE := SessionMultiLib.RealAnalysis.«REAL_SUMMABLE»
  REAL_SUMMABLE_COMPARISON := SessionMultiLib.RealAnalysis.«REAL_SUMMABLE_COMPARISON»
  REAL_SUMMABLE_FROM_ELSEWHERE_EQ := SessionMultiLib.RealAnalysis.«REAL_SUMMABLE_FROM_ELSEWHERE_EQ»
  REAL_SUMMABLE_SUB := SessionMultiLib.RealAnalysis.«REAL_SUMMABLE_SUB»
  REAL_SUMMABLE_ZETA := SessionMultiLib.RealAnalysis.«REAL_SUMMABLE_ZETA»
  REAL_SUMS_COMPLEX := SessionMultiLib.RealAnalysis.«REAL_SUMS_COMPLEX»
  REAL_SUMS_INFSUM := SessionMultiLib.RealAnalysis.«REAL_SUMS_INFSUM»
  REAL_SUMS_OFFSET := SessionMultiLib.RealAnalysis.«REAL_SUMS_OFFSET»
  RE_CX := SessionMultiLib.ComplexAlgebra.«RE_CX»
  RIGHT_ADD_DISTRIB := Session.RIGHT_ADD_DISTRIB
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_LCANCEL := SessionLibrary.RingTheory.«RING_ADD_LCANCEL»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_RING_OF_NUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_NUM»
  RING_HOMOMORPHISM_SUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM»
  RING_IDEAL_CARRIER := SessionLibrary.RingTheory.«RING_IDEAL_CARRIER»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_MONOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INTEGER_RING_OF_INT»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE := SessionANT.ComplexEmbeddings.«RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_FREE := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE»
  RING_OF_INTEGERS_FREE_BASIS_FIELD := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE_BASIS_FIELD»
  RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q := SessionANT.PrimeSplit.«RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q»
  RING_OF_INTEGERS_PRIME_IDEAL_ABOVE := SessionANT.PrimeSplit.«RING_OF_INTEGERS_PRIME_IDEAL_ABOVE»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_IN_RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INT_IN_RING_OF_INTEGERS»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_SUM_RING_OF_INTEGERS»
  RPOW_ADD := SessionMultiLib.Transcendentals.«RPOW_ADD»
  RPOW_LE2 := SessionMultiLib.Transcendentals.«RPOW_LE2»
  RPOW_LE_1 := SessionMultiLib.Transcendentals.«RPOW_LE_1»
  RPOW_LT_1 := SessionMultiLib.Transcendentals.«RPOW_LT_1»
  RPOW_MONO_LE := SessionMultiLib.Transcendentals.«RPOW_MONO_LE»
  RPOW_ONE := SessionMultiLib.Transcendentals.«RPOW_ONE»
  RPOW_POS_LE := SessionMultiLib.Transcendentals.«RPOW_POS_LE»
  RPOW_POS_LT := SessionMultiLib.Transcendentals.«RPOW_POS_LT»
  RPOW_POW := SessionMultiLib.Transcendentals.«RPOW_POW»
  RPOW_ZERO := SessionMultiLib.Transcendentals.«RPOW_ZERO»
  SERIES_UNIQUE := SessionMultiLib.Topology.«SERIES_UNIQUE»
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_DIFF := Session.SUBSET_DIFF
  SUBSET_REFL := Session.SUBSET_REFL
  SUB_0 := Session.SUB_0
  SUB_REFL := Session.SUB_REFL
  SUMMABLE_COMPARISON := SessionMultiLib.Topology.«SUMMABLE_COMPARISON»
  SUMS_EQ := SessionMultiLib.Topology.«SUMS_EQ»
  SUMS_GP := SessionMultiLib.Canal.«SUMS_GP»
  SUMS_INFSUM := SessionMultiLib.Topology.«SUMS_INFSUM»
  SUM_ABS_BOUND := Session.SUM_ABS_BOUND
  SUM_ADD := Session.SUM_ADD
  SUM_ADD_NUMSEG := Session.SUM_ADD_NUMSEG
  SUM_ADD_SPLIT := Session.SUM_ADD_SPLIT
  SUM_CLAUSES_NUMSEG := Session.SUM_CLAUSES_NUMSEG
  SUM_CLAUSES_RIGHT := Session.SUM_CLAUSES_RIGHT
  SUM_CONST := Session.SUM_CONST
  SUM_CONST_NUMSEG := Session.SUM_CONST_NUMSEG
  SUM_DIFFS := Session.SUM_DIFFS
  SUM_EQ := Session.SUM_EQ
  SUM_EQ_0_NUMSEG := Session.SUM_EQ_0_NUMSEG
  SUM_EQ_NUMSEG := Session.SUM_EQ_NUMSEG
  SUM_GROUP := Session.SUM_GROUP
  SUM_LE := Session.SUM_LE
  SUM_LE_NUMSEG := Session.SUM_LE_NUMSEG
  SUM_LMUL := Session.SUM_LMUL
  SUM_NEG := Session.SUM_NEG
  SUM_PARTIAL_PRE := Session.SUM_PARTIAL_PRE
  SUM_POS_LE_NUMSEG := Session.SUM_POS_LE_NUMSEG
  SUM_SUBSET_SIMPLE := Session.SUM_SUBSET_SIMPLE
  SUM_SUB_NUMSEG := Session.SUM_SUB_NUMSEG
  SUM_UNION := Session.SUM_UNION
  TRIVIAL_LIMIT_ATREAL_RIGHT := SessionMultiLib.RealAnalysis.«TRIVIAL_LIMIT_ATREAL_RIGHT»
  TRIVIAL_LIMIT_SEQUENTIALLY := SessionMultiLib.Metric.«TRIVIAL_LIMIT_SEQUENTIALLY»
  UNION_COMM := Session.UNION_COMM
  UPPER_BOUND_FINITE_SET := SessionMultiLib.Misc.«UPPER_BOUND_FINITE_SET»
  UPPER_BOUND_FINITE_SET_INT := SessionANT.Algmisc.«UPPER_BOUND_FINITE_SET_INT»
  UPPER_BOUND_FINITE_SET_REAL := SessionMultiLib.Misc.«UPPER_BOUND_FINITE_SET_REAL»
  VSUM_CONST := SessionMultiLib.Vectors.«VSUM_CONST»
  VSUM_EQ := SessionMultiLib.Vectors.«VSUM_EQ»
  VSUM_GROUP := SessionMultiLib.Vectors.«VSUM_GROUP»
  VSUM_IMAGE := SessionMultiLib.Vectors.«VSUM_IMAGE»
  VSUM_NORM := SessionMultiLib.Vectors.«VSUM_NORM»
  VSUM_SUB := SessionMultiLib.Vectors.«VSUM_SUB»
  complex_div := SessionMultiLib.ComplexAlgebra.«complex_div»
  complex_embeddings := SessionANT.ComplexEmbeddings.«complex_embeddings»
  complex_pow := SessionMultiLib.ComplexAlgebra.«complex_pow»
  dist := SessionMultiLib.Vectors.«dist»
  free_basis := SessionLibrary.RingDet.«free_basis»
  ideal_norm := SessionANT.IdealNorm.«ideal_norm»
  int_le := Session.int_le
  number_field := SessionANT.Numfield.«number_field»
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM
  prime_ideal := SessionLibrary.RingTheory.«prime_ideal»
  proper_ideal := SessionLibrary.RingTheory.«proper_ideal»
  real_abs := Session.real_abs
  real_div := Session.real_div
  real_summable := SessionMultiLib.RealAnalysis.«real_summable»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  sums := SessionMultiLib.Topology.«sums»

/-- What dedekind_zeta.ml uses from Session. -/
def deps : HolANT.DedekindZeta.DedekindZetaDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  new_recursive_definition ax s := do
    ExceptT.mk (Session.new_recursive_definition ax (← HolLight.q s))
  LIST_INDUCT_TAC := Session.LIST_INDUCT_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  METIS_TAC := Session.METIS_TAC
  ASM_METIS_TAC := Session.ASM_METIS_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  TAUT t := ExceptT.mk (Session.TAUT t)
  ITAUT t := ExceptT.mk (Session.ITAUT t)
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH t)
  REAL_FIELD t := ExceptT.mk (Session.REAL_FIELD t)
  REAL_ARITH_TAC := Session.REAL_ARITH_TAC
  ASM_REAL_ARITH_TAC := Session.ASM_REAL_ARITH_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  INT_ARITH t := ExceptT.mk (Session.INT_ARITH t)
  INT_ARITH_TAC := Session.INT_ARITH_TAC
  ASM_INT_ARITH_TAC := Session.ASM_INT_ARITH_TAC
  INTEGER_RULE t := ExceptT.mk (Session.INTEGER_RULE t)
  INTEGER_TAC := Session.INTEGER_TAC
  NUMBER_RULE := Session.NUMBER_RULE
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  INT_REDUCE_CONV := Session.INT_REDUCE_CONV
  INT_RED_CONV := Session.INT_RED_CONV
  INT_REM_DOWN_CONV := Session.INT_REM_DOWN_CONV
  HAS_SIZE_CONV := Session.HAS_SIZE_CONV
  let_CONV := Session.let_CONV
  num_CONV := Session.num_CONV
  mk_numeral := Session.mk_numeral
  PRIME_CONV t := ExceptT.mk (SessionLibrary.Pocklington.PRIME_CONV t)
  PRIME_RULE := SessionLibrary.Pocklington.PRIME_RULE
  RING_RULE t := ExceptT.mk (SessionLibrary.RingTheory.RING_RULE t)
  INTEGRAL_DOMAIN_RULE t := ExceptT.mk (SessionLibrary.RingTheory.INTEGRAL_DOMAIN_RULE t)
  FIELD_TAC := SessionLibrary.RingTheory.FIELD_TAC
  RING_CARRIER_TAC := SessionLibrary.RingTheory.RING_CARRIER_TAC
  RING_TAC := SessionLibrary.RingTheory.RING_TAC
  RING_PULL_DIV_TAC := SessionLibrary.RingTheory.RING_PULL_DIV_TAC
  LET_TAC := Session.LET_TAC
  GROUP_RULE t := ExceptT.mk (SessionLibrary.GroupTheory.GROUP_RULE t)
  basic_ss := Session.basic_ss
  INTEGER_MOD_RING_RED_CONV := SessionLibrary.RingTheory.INTEGER_MOD_RING_RED_CONV
  NUM_SUB_CONV := Session.NUM_SUB_CONV
  REAL_RAT_REDUCE_CONV := Session.REAL_RAT_REDUCE_CONV
  NUM_EQ_CONV := Session.NUM_EQ_CONV
  NUM_DIV_CONV := Session.NUM_DIV_CONV
  EXP_MOD_CONV := Session.EXP_MOD_CONV
  EXPAND_CASES_CONV := Session.EXPAND_CASES_CONV
  DIVIDES_CONV := SessionLibrary.Prime.DIVIDES_CONV
  COPRIME_CONV := SessionLibrary.Prime.COPRIME_CONV
  NORM_ARITH t := ExceptT.mk (SessionMultiLib.Vectors.NORM_ARITH t)
  SELECT_CONV t := pure (Session.SELECT_CONV t)
  COMPLEX_RING t := ExceptT.mk (SessionMultiLib.ComplexAlgebra.COMPLEX_RING t)
  core1 := core1
  core2 := core2
  core3 := core3

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in dedekind_zeta.ml order. -/
initialize BDedekindZeta01 : HolANT.DedekindZeta.DedekindZeta01 ←
  ioB "setupDedekindZeta01" (HolANT.DedekindZeta.setupDedekindZeta01 deps).run
initialize BDedekindZeta02 : HolANT.DedekindZeta.DedekindZeta02 ←
  ioB "setupDedekindZeta02" (HolANT.DedekindZeta.setupDedekindZeta02 deps BDedekindZeta01).run
initialize BDedekindZeta03 : HolANT.DedekindZeta.DedekindZeta03 ←
  ioB "setupDedekindZeta03" (HolANT.DedekindZeta.setupDedekindZeta03 deps BDedekindZeta01 BDedekindZeta02).run
initialize BDedekindZeta04 : HolANT.DedekindZeta.DedekindZeta04 ←
  ioB "setupDedekindZeta04" (HolANT.DedekindZeta.setupDedekindZeta04 deps BDedekindZeta02 BDedekindZeta03).run
initialize BDedekindZeta05 : HolANT.DedekindZeta.DedekindZeta05 ←
  ioB "setupDedekindZeta05" (HolANT.DedekindZeta.setupDedekindZeta05 deps BDedekindZeta02 BDedekindZeta04).run

-- DedekindZeta01
def DIRICHLET_SERIES_LINEAR_PARTIAL_SUMS : thm := BDedekindZeta01.DIRICHLET_SERIES_LINEAR_PARTIAL_SUMS
def NUMBER_FIELD_IDEAL_BOX_COFACTOR : thm := BDedekindZeta01.NUMBER_FIELD_IDEAL_BOX_COFACTOR
def NUMBER_FIELD_IDEAL_COUNT_UPPER : thm := BDedekindZeta01.NUMBER_FIELD_IDEAL_COUNT_UPPER

-- DedekindZeta02
def NUMBER_FIELD_PRINCIPAL_IDEAL_FAMILY : thm := BDedekindZeta02.NUMBER_FIELD_PRINCIPAL_IDEAL_FAMILY
def NUMBER_FIELD_IDEAL_COUNT_LOWER : thm := BDedekindZeta02.NUMBER_FIELD_IDEAL_COUNT_LOWER
def NUMBER_FIELD_IDEAL_COUNT_BOUNDS : thm := BDedekindZeta02.NUMBER_FIELD_IDEAL_COUNT_BOUNDS
def SUM_GROUP_CARD : thm := BDedekindZeta02.SUM_GROUP_CARD
def VSUM_GROUP_CARD : thm := BDedekindZeta02.VSUM_GROUP_CARD
def NUMBER_FIELD_IDEAL_SUM_BY_NORM : thm := BDedekindZeta02.NUMBER_FIELD_IDEAL_SUM_BY_NORM
def dedekind_zeta : thm := BDedekindZeta02.dedekind_zeta
def NUMBER_FIELD_IDEAL_COUNT_SUM : thm := BDedekindZeta02.NUMBER_FIELD_IDEAL_COUNT_SUM
def NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE : thm := BDedekindZeta02.NUMBER_FIELD_IDEAL_DIRICHLET_SUMMABLE
def DEDEKIND_ZETA_CONVERGES : thm := BDedekindZeta02.DEDEKIND_ZETA_CONVERGES
def DEDEKIND_ZETA_REAL : thm := BDedekindZeta02.DEDEKIND_ZETA_REAL
def DEDEKIND_ZETA_REAL_INFSUM : thm := BDedekindZeta02.DEDEKIND_ZETA_REAL_INFSUM

-- DedekindZeta03
def DEDEKIND_ZETA_POLE_BOUNDS : thm := BDedekindZeta03.DEDEKIND_ZETA_POLE_BOUNDS
def DEDEKIND_FINITE_EULER_PRODUCT : thm := BDedekindZeta03.DEDEKIND_FINITE_EULER_PRODUCT
def NUMBER_FIELD_IDEAL_PRIME_POWER_PRODUCT : thm := BDedekindZeta03.NUMBER_FIELD_IDEAL_PRIME_POWER_PRODUCT
def DEDEKIND_ZETA_EULER_PRODUCT_BOUND : thm := BDedekindZeta03.DEDEKIND_ZETA_EULER_PRODUCT_BOUND
def DEDEKIND_ZETA_EULER_PRODUCT : thm := BDedekindZeta03.DEDEKIND_ZETA_EULER_PRODUCT
def DEDEKIND_ZETA_EULER_PRODUCT_REAL : thm := BDedekindZeta03.DEDEKIND_ZETA_EULER_PRODUCT_REAL

-- DedekindZeta04
def DEDEKIND_ZETA_LOG_PRIME_IDEALS : thm := BDedekindZeta04.DEDEKIND_ZETA_LOG_PRIME_IDEALS
def NUMBER_FIELD_NONPRIME_NORM_SUM_LE : thm := BDedekindZeta04.NUMBER_FIELD_NONPRIME_NORM_SUM_LE
def DEDEKIND_ZETA_LOG_POLE : thm := BDedekindZeta04.DEDEKIND_ZETA_LOG_POLE
def NUMBER_FIELD_PRIME_IDEALS_LOG : thm := BDedekindZeta04.NUMBER_FIELD_PRIME_IDEALS_LOG
def NUMBER_FIELD_DEGREE_ONE_PRIMES_LOG : thm := BDedekindZeta04.NUMBER_FIELD_DEGREE_ONE_PRIMES_LOG
def has_dirichlet_density : thm := BDedekindZeta04.has_dirichlet_density
def HAS_DIRICHLET_DENSITY_LOG : thm := BDedekindZeta04.HAS_DIRICHLET_DENSITY_LOG
def HAS_DIRICHLET_DENSITY_UNIQUE : thm := BDedekindZeta04.HAS_DIRICHLET_DENSITY_UNIQUE
def HAS_DIRICHLET_DENSITY_FINITE : thm := BDedekindZeta04.HAS_DIRICHLET_DENSITY_FINITE
def HAS_DIRICHLET_DENSITY_INFINITE : thm := BDedekindZeta04.HAS_DIRICHLET_DENSITY_INFINITE
def NUMBER_FIELD_PRIME_IDEALS_DENSITY : thm := BDedekindZeta04.NUMBER_FIELD_PRIME_IDEALS_DENSITY
def NUMBER_FIELD_DEGREE_ONE_PRIMES_DENSITY : thm := BDedekindZeta04.NUMBER_FIELD_DEGREE_ONE_PRIMES_DENSITY

-- DedekindZeta05
def NUMBER_FIELD_PRIME_IDEAL_DIRICHLET_SUMMABLE : thm := BDedekindZeta05.NUMBER_FIELD_PRIME_IDEAL_DIRICHLET_SUMMABLE
def HAS_DIRICHLET_DENSITY_DISJOINT_UNION : thm := BDedekindZeta05.HAS_DIRICHLET_DENSITY_DISJOINT_UNION
def HAS_DIRICHLET_DENSITY_DIFF_SUBSET : thm := BDedekindZeta05.HAS_DIRICHLET_DENSITY_DIFF_SUBSET
def HAS_DIRICHLET_DENSITY_COMPLEMENT : thm := BDedekindZeta05.HAS_DIRICHLET_DENSITY_COMPLEMENT
def HAS_DIRICHLET_DENSITY_BOUNDS : thm := BDedekindZeta05.HAS_DIRICHLET_DENSITY_BOUNDS
def HAS_DIRICHLET_DENSITY_SUBSET : thm := BDedekindZeta05.HAS_DIRICHLET_DENSITY_SUBSET
def HAS_DIRICHLET_DENSITY_FINITE_SYMDIFF : thm := BDedekindZeta05.HAS_DIRICHLET_DENSITY_FINITE_SYMDIFF

/-- `needs "ANT/dedekind_zeta.ml"`: already done by importing this module. -/
def ensureDedekindZeta : IO Unit := pure ()

end SessionANT.DedekindZeta
