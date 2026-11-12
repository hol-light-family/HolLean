/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/sunit_rank.ml                                 . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/SunitRank.lean

  The session half of the sunit_rank.ml translation: it supplies HolANT.SunitRank's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/sunit_rank.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.SunitRank
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionLibrary.Matroids
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionLibrary.FieldTheory
import SessionANT.Integral
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.RingOfIntegers
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.NfValuation
import SessionANT.ClassgroupGroup
import SessionLibrary.RingGroups
import SessionANT.FingenGroup
import SessionANT.PrimeSplit
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.Integrality
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
import SessionMultiLib.MoreTop
import SessionMultiLib.Cauchy
import SessionMultiLib.ComplexRing
import SessionMultiLib.ComplexField
import SessionANT.ComplexEmbeddings
import SessionANT.FractionalIdeals
import SessionANT.DedekindCriteria
import SessionANT.SIntegers
import SessionANT.Sunits
import SessionANT.PowerBasis
import SessionANT.InfinitePlaces
import SessionANT.LinearForms
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.Quadratic
import SessionANT.MinkowskiTheory
import SessionANT.UnitTheorem
import SessionANT.ValuationRing
import SessionANT.DedekindAbsolute
import SessionANT.ProductFormula
import SessionANT.Regulator

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.SunitRank

/-- The core theorems sunit_rank.ml uses. -/
def core1 : HolANT.SunitRank.CoreThms1 where
  ABELIAN_GROUP_DISCRETE_DEPENDENT := SessionANT.FingenGroup.«ABELIAN_GROUP_DISCRETE_DEPENDENT»
  ABELIAN_S_UNIT_GROUP := SessionANT.Sunits.«ABELIAN_S_UNIT_GROUP»
  ABELIAN_UNIT_GROUP := SessionLibrary.RingGroups.«ABELIAN_UNIT_GROUP»
  CARD_DELETE := Session.CARD_DELETE
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_IMAGE_LE := Session.CARD_IMAGE_LE
  CARD_SUBSET := Session.CARD_SUBSET
  CARD_UNION := Session.CARD_UNION
  CARD_UNION_LE := Session.CARD_UNION_LE
  COMPLEX_EMBEDDINGS_NONEMPTY := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_NONEMPTY»
  COMPLEX_EMBEDDINGS_NORM_MUL := SessionANT.InfinitePlaces.«COMPLEX_EMBEDDINGS_NORM_MUL»
  COMPLEX_NORM_CX := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_CX»
  COMPLEX_RING_OF_NUM := SessionMultiLib.ComplexRing.«COMPLEX_RING_OF_NUM»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DISJOINT := Session.DISJOINT
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  EQ_SYM_EQ := Session.EQ_SYM_EQ
  EQ_TRANS := Session.EQ_TRANS
  EXP_EQ_0 := Session.EXP_EQ_0
  EXTENSION := Session.EXTENSION
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_MUL_LINV := SessionLibrary.RingTheory.«FIELD_MUL_LINV»
  FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS := SessionANT.FingenGroup.«FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS»
  FINITELY_GENERATED_S_UNIT_GROUP := SessionANT.Sunits.«FINITELY_GENERATED_S_UNIT_GROUP»
  FINITE_COMPLEX_EMBEDDINGS := SessionANT.ComplexEmbeddings.«FINITE_COMPLEX_EMBEDDINGS»
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INFINITE_PLACES := SessionANT.InfinitePlaces.«FINITE_INFINITE_PLACES»
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNION := Session.FINITE_UNION
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FUN_EQ_THM := Session.FUN_EQ_THM
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  GROUP_HOMOMORPHISM := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM»
  GROUP_HOMOMORPHISM_ZPOW := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM_ZPOW»
  GROUP_POW_EQ_ID := SessionLibrary.GroupTheory.«GROUP_POW_EQ_ID»
  GROUP_REAL_MULTIPLICATIVE_LOG_SUM_ZPOW := SessionANT.Regulator.«GROUP_REAL_MULTIPLICATIVE_LOG_SUM_ZPOW»
  GROUP_SUM_EQ := SessionLibrary.GroupTheory.«GROUP_SUM_EQ»
  GROUP_SUM_HOMOMORPHIC_IMAGE := SessionLibrary.GroupTheory.«GROUP_SUM_HOMOMORPHIC_IMAGE»
  GROUP_SUM_SUPERSET := SessionLibrary.GroupTheory.«GROUP_SUM_SUPERSET»
  GROUP_ZPOW := SessionLibrary.GroupTheory.«GROUP_ZPOW»
  GROUP_ZPOW_0 := SessionLibrary.GroupTheory.«GROUP_ZPOW_0»
  HAS_SIZE := Session.HAS_SIZE
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_NORM_GT_1 := SessionANT.IdealNorm.«IDEAL_NORM_GT_1»
  IDEAL_NORM_IN_IDEAL := SessionANT.IdealNorm.«IDEAL_NORM_IN_IDEAL»
  IDEAL_NORM_POS := SessionANT.IdealNorm.«IDEAL_NORM_POS»
  IDEAL_POW_EQ_ZERO := SessionANT.IdealArith.«IDEAL_POW_EQ_ZERO»
  IDEAL_VALUATION_IDEAL_POW := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_POW»
  IDEAL_VALUATION_PRIME := SessionANT.Dedekind.«IDEAL_VALUATION_PRIME»
  IMAGE_EQ_EMPTY := Session.IMAGE_EQ_EMPTY
  IMAGE_I := Session.IMAGE_I
  INFINITE_PLACES_MUL := SessionANT.InfinitePlaces.«INFINITE_PLACES_MUL»
  INFINITE_PLACES_POS := SessionANT.InfinitePlaces.«INFINITE_PLACES_POS»
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_RING_OF_INTEGERS := SessionANT.Numfield.«INTEGRAL_DOMAIN_RING_OF_INTEGERS»
  INT_ABS_NEG := Session.INT_ABS_NEG
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_IMAGE := Session.INT_IMAGE
  INT_LE_LMUL := Session.INT_LE_LMUL
  INT_LE_REFL := Session.INT_LE_REFL
  INT_MUL_RID := Session.INT_MUL_RID
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_POS := Session.INT_POS
  IN_DELETE := Session.IN_DELETE
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INTER := Session.IN_INTER
  IN_RING_IDEAL_RMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_RMUL»
  IN_UNION := Session.IN_UNION
  I_THM := Session.I_THM
  LET_TRANS := Session.LET_TRANS
  LE_ANTISYM := Session.LE_ANTISYM
  LOG_1 := SessionMultiLib.Transcendentals.«LOG_1»
  LOG_POS_LT := SessionMultiLib.Transcendentals.«LOG_POS_LT»
  LOG_ZPOW := SessionMultiLib.Transcendentals.«LOG_ZPOW»
  LT_NZ := Session.LT_NZ
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONO_EXISTS := Session.MONO_EXISTS
  NORM_POS_LE := SessionMultiLib.Vectors.«NORM_POS_LE»
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LE := Session.NOT_LE
  NOT_LT := Session.NOT_LT
  NPRODUCT_DELETE := SessionLibrary.Products.«NPRODUCT_DELETE»
  NPRODUCT_POS_LT := SessionLibrary.Products.«NPRODUCT_POS_LT»
  NUMBER_FIELD_CLASS_NUMBER_POS := SessionANT.Classgroup.«NUMBER_FIELD_CLASS_NUMBER_POS»
/-- The core theorems sunit_rank.ml uses. -/
def core2 : HolANT.SunitRank.CoreThms2 where
  NUMBER_FIELD_FUNDAMENTAL_UNITS := SessionANT.UnitTheorem.«NUMBER_FIELD_FUNDAMENTAL_UNITS»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2 := SessionANT.Classgroup.«NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2»
  NUMBER_FIELD_PRINCIPAL_IDEAL_POW_CLASS_NUMBER := SessionANT.ClassgroupGroup.«NUMBER_FIELD_PRINCIPAL_IDEAL_POW_CLASS_NUMBER»
  NUMBER_FIELD_PRODUCT_FORMULA := SessionANT.ProductFormula.«NUMBER_FIELD_PRODUCT_FORMULA»
  NUMBER_FIELD_RING_OF_NUM_EQ_0 := SessionANT.Numfield.«NUMBER_FIELD_RING_OF_NUM_EQ_0»
  NUMBER_FIELD_VALUATION_1 := SessionANT.NfValuation.«NUMBER_FIELD_VALUATION_1»
  NUMBER_FIELD_VALUATION_INTEGRAL := SessionANT.NfValuation.«NUMBER_FIELD_VALUATION_INTEGRAL»
  NUMBER_FIELD_VALUATION_MUL := SessionANT.NfValuation.«NUMBER_FIELD_VALUATION_MUL»
  NUMBER_FIELD_VALUATION_POW := SessionANT.NfValuation.«NUMBER_FIELD_VALUATION_POW»
  NUMBER_FIELD_VALUATION_PRIME_IDEAL := SessionANT.NfValuation.«NUMBER_FIELD_VALUATION_PRIME_IDEAL»
  NUMBER_FIELD_VALUATION_RING_OF_INTEGERS := SessionANT.NfValuation.«NUMBER_FIELD_VALUATION_RING_OF_INTEGERS»
  NUMBER_FIELD_VALUATION_UNIT := SessionANT.NfValuation.«NUMBER_FIELD_VALUATION_UNIT»
  PRIME_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_PROPER_IDEAL»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRODUCT_CONST := SessionLibrary.Products.«PRODUCT_CONST»
  PRODUCT_FACTOR_BOUND := SessionLibrary.Products.«PRODUCT_FACTOR_BOUND»
  PRODUCT_INV := SessionLibrary.Products.«PRODUCT_INV»
  PRODUCT_LE := SessionLibrary.Products.«PRODUCT_LE»
  PRODUCT_POS_LT := SessionLibrary.Products.«PRODUCT_POS_LT»
  PRODUCT_SUPERSET := SessionLibrary.Products.«PRODUCT_SUPERSET»
  PSUBSET := Session.PSUBSET
  REAL_ABS_NUM := Session.REAL_ABS_NUM
  REAL_ARCH_POW2 := Session.REAL_ARCH_POW2
  REAL_ENTIRE := Session.REAL_ENTIRE
  REAL_INV_1 := Session.REAL_INV_1
  REAL_LE_LMUL := Session.REAL_LE_LMUL
  REAL_LE_MUL2 := Session.REAL_LE_MUL2
  REAL_LE_REFL := Session.REAL_LE_REFL
  REAL_LE_TRANS := Session.REAL_LE_TRANS
  REAL_LTE_TRANS := Session.REAL_LTE_TRANS
  REAL_LT_IMP_LE := Session.REAL_LT_IMP_LE
  REAL_LT_IMP_NZ := Session.REAL_LT_IMP_NZ
  REAL_LT_INV2 := Session.REAL_LT_INV2
  REAL_LT_INV_EQ := Session.REAL_LT_INV_EQ
  REAL_MUL_ASSOC := Session.REAL_MUL_ASSOC
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_RID := Session.REAL_MUL_RID
  REAL_MUL_RINV := Session.REAL_MUL_RINV
  REAL_NOT_LE := Session.REAL_NOT_LE
  REAL_NOT_LT := Session.REAL_NOT_LT
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_OF_NUM_LE := Session.REAL_OF_NUM_LE
  REAL_OF_NUM_LT := Session.REAL_OF_NUM_LT
  REAL_POS := Session.REAL_POS
  REAL_POW_1 := Session.REAL_POW_1
  REAL_POW_ADD := Session.REAL_POW_ADD
  REAL_POW_LE2 := Session.REAL_POW_LE2
  REAL_POW_LT := Session.REAL_POW_LT
  REAL_POW_MONO := Session.REAL_POW_MONO
  REAL_ZPOW_0 := Session.REAL_ZPOW_0
  REAL_ZPOW_ADD := Session.REAL_ZPOW_ADD
  REAL_ZPOW_LT := Session.REAL_ZPOW_LT
  REAL_ZPOW_NEG := Session.REAL_ZPOW_NEG
  REAL_ZPOW_NUM := Session.REAL_ZPOW_NUM
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_HOMOMORPHISM_RING_OF_NUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_NUM»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE := SessionANT.ComplexEmbeddings.«RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INTEGERS_UNIT_NONZERO := SessionANT.Numfield.«RING_OF_INTEGERS_UNIT_NONZERO»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_EXP := SessionLibrary.RingTheory.«RING_OF_NUM_EXP»
  RING_OF_NUM_MUL := SessionLibrary.RingTheory.«RING_OF_NUM_MUL»
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  SUBSET_UNION := Session.SUBSET_UNION
  SUM_DELTA := Session.SUM_DELTA
  SUM_EQ := Session.SUM_EQ
  S_UNIT_GROUP := SessionANT.Sunits.«S_UNIT_GROUP»
  S_UNIT_GROUP_EMPTY := SessionANT.Sunits.«S_UNIT_GROUP_EMPTY»
  S_UNIT_GROUP_MONO := SessionANT.Sunits.«S_UNIT_GROUP_MONO»
  S_UNIT_GROUP_POW := SessionANT.Sunits.«S_UNIT_GROUP_POW»
  UNION_SUBSET := Session.UNION_SUBSET
  UNIT_GROUP := SessionLibrary.RingGroups.«UNIT_GROUP»
  complex_embeddings := SessionANT.ComplexEmbeddings.«complex_embeddings»
  infinite_places := SessionANT.InfinitePlaces.«infinite_places»
  int_eq := Session.int_eq
  int_of_num_th := Session.int_of_num_th
  lemma := SessionMultiLib.Integration.«lemma»
  o_DEF := Session.o_DEF
  principal_ideal := SessionLibrary.RingTheory.«principal_ideal»
  proper_ideal := SessionLibrary.RingTheory.«proper_ideal»

/-- What sunit_rank.ml uses from Session. -/
def deps : HolANT.SunitRank.SunitRankDeps where
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
  core1 := core1
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in sunit_rank.ml order. -/
initialize BSunitRank01 : HolANT.SunitRank.SunitRank01 ←
  ioB "setupSunitRank01" (HolANT.SunitRank.setupSunitRank01 deps).run
initialize BSunitRank02 : HolANT.SunitRank.SunitRank02 ←
  ioB "setupSunitRank02" (HolANT.SunitRank.setupSunitRank02 deps BSunitRank01).run

-- SunitRank01
def GROUP_HOMOMORPHISM_UNIT_GROUP_S_UNIT_GROUP : thm := BSunitRank01.GROUP_HOMOMORPHISM_UNIT_GROUP_S_UNIT_GROUP
def S_UNIT_GROUP_INFINITE_PLACES : thm := BSunitRank01.S_UNIT_GROUP_INFINITE_PLACES
def S_UNIT_GROUP_PRIME_SIZE : thm := BSunitRank01.S_UNIT_GROUP_PRIME_SIZE
def NUMBER_FIELD_VALUATION_DENOMINATOR : thm := BSunitRank01.NUMBER_FIELD_VALUATION_DENOMINATOR
def S_UNIT_GROUP_PRODUCT_FORMULA : thm := BSunitRank01.S_UNIT_GROUP_PRODUCT_FORMULA
def S_UNIT_GROUP_BOUNDED_EMBEDDINGS : thm := BSunitRank01.S_UNIT_GROUP_BOUNDED_EMBEDDINGS
def S_UNIT_GROUP_BOUNDED_FINITE : thm := BSunitRank01.S_UNIT_GROUP_BOUNDED_FINITE
def S_UNIT_GROUP_DEPENDENT : thm := BSunitRank01.S_UNIT_GROUP_DEPENDENT
def NUMBER_FIELD_PRIME_POW_GENERATOR : thm := BSunitRank01.NUMBER_FIELD_PRIME_POW_GENERATOR

-- SunitRank02
def S_UNIT_GROUP_INDEPENDENT : thm := BSunitRank02.S_UNIT_GROUP_INDEPENDENT
def S_UNIT_GROUP_FUNDAMENTAL : thm := BSunitRank02.S_UNIT_GROUP_FUNDAMENTAL

/-- `needs "ANT/sunit_rank.ml"`: already done by importing this module. -/
def ensureSunitRank : IO Unit := pure ()

end SessionANT.SunitRank
