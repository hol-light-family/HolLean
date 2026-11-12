/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/unit_theorem.ml                               . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/UnitTheorem.lean

  The session half of the unit_theorem.ml translation: it supplies HolANT.UnitTheorem's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/unit_theorem.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.UnitTheorem
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Products
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionANT.Algmisc
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionANT.IdealArith
import SessionLibrary.Matroids
import SessionLibrary.FieldTheory
import SessionANT.Integral
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.Discriminant
import SessionLibrary.RingGroups
import SessionANT.FingenGroup
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.NfValuation
import SessionANT.PrimeSplit
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
import SessionANT.PowerBasis
import SessionANT.InfinitePlaces
import SessionANT.LinearForms
import SessionANT.ClassgroupGroup
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.Quadratic
import SessionANT.MinkowskiTheory

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.UnitTheorem

/-- The core theorems unit_theorem.ml uses. -/
def core1 : HolANT.UnitTheorem.CoreThms1 where
  ABELIAN_GROUP_DISCRETE_DEPENDENT := SessionANT.FingenGroup.«ABELIAN_GROUP_DISCRETE_DEPENDENT»
  ABELIAN_GROUP_SUM_INV := SessionLibrary.GroupTheory.«ABELIAN_GROUP_SUM_INV»
  ABELIAN_UNIT_GROUP := SessionLibrary.RingGroups.«ABELIAN_UNIT_GROUP»
  ARITH_EQ := Session.ARITH_EQ
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_DELETE := Session.CARD_DELETE
  CARD_EQ_0 := Session.CARD_EQ_0
  COMPLEX_EMBEDDINGS_NONEMPTY := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_NONEMPTY»
  COMPLEX_EMBEDDINGS_NORM_MUL := SessionANT.InfinitePlaces.«COMPLEX_EMBEDDINGS_NORM_MUL»
  COMPLEX_EMBEDDINGS_NORM_POS := SessionANT.InfinitePlaces.«COMPLEX_EMBEDDINGS_NORM_POS»
  COMPLEX_NORM_MUL := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_MUL»
  COMPLEX_RING_CLAUSES := SessionMultiLib.ComplexRing.«COMPLEX_RING_CLAUSES»
  COND_ID := Session.COND_ID
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  EQ_TRANS := Session.EQ_TRANS
  EXTENSION := Session.EXTENSION
  EXTENSIONAL := Session.EXTENSIONAL
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS := SessionANT.FingenGroup.«FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS»
  FINITE_COMPLEX_EMBEDDINGS := SessionANT.ComplexEmbeddings.«FINITE_COMPLEX_EMBEDDINGS»
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_DIFF := Session.FINITE_DIFF
  FINITE_IMAGE_INJ_EQ := Session.FINITE_IMAGE_INJ_EQ
  FINITE_INFINITE_PLACES := SessionANT.InfinitePlaces.«FINITE_INFINITE_PLACES»
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FUN_EQ_THM := Session.FUN_EQ_THM
  GROUP_INV_ID := SessionLibrary.GroupTheory.«GROUP_INV_ID»
  GROUP_NPOW := SessionLibrary.GroupTheory.«GROUP_NPOW»
  GROUP_POW := SessionLibrary.GroupTheory.«GROUP_POW»
  GROUP_POW_EQ_ID := SessionLibrary.GroupTheory.«GROUP_POW_EQ_ID»
  GROUP_REAL_MULTIPLICATIVE_ID_INV_POW := SessionLibrary.RingGroups.«GROUP_REAL_MULTIPLICATIVE_ID_INV_POW»
  GROUP_REAL_MULTIPLICATIVE_SUM := SessionLibrary.RingGroups.«GROUP_REAL_MULTIPLICATIVE_SUM»
  GROUP_SUM_CLAUSES_EXISTS := SessionLibrary.GroupTheory.«GROUP_SUM_CLAUSES_EXISTS»
  GROUP_SUM_IMAGE := SessionLibrary.GroupTheory.«GROUP_SUM_IMAGE»
  GROUP_SUM_SING := SessionLibrary.GroupTheory.«GROUP_SUM_SING»
  GROUP_SUM_SUPERSET := SessionLibrary.GroupTheory.«GROUP_SUM_SUPERSET»
  GROUP_ZPOW := SessionLibrary.GroupTheory.«GROUP_ZPOW»
  GROUP_ZPOW_0 := SessionLibrary.GroupTheory.«GROUP_ZPOW_0»
  GROUP_ZPOW_NEG := SessionLibrary.GroupTheory.«GROUP_ZPOW_NEG»
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_0 := Session.HAS_SIZE_0
  HAS_SIZE_IMAGE_INJ := Session.HAS_SIZE_IMAGE_INJ
  IDEALS_GENERATED_SING_EQ := SessionLibrary.RingTheory.«IDEALS_GENERATED_SING_EQ»
  IDEAL_NORM_CARRIER := SessionANT.IdealNorm.«IDEAL_NORM_CARRIER»
  IMAGE_EQ_EMPTY := Session.IMAGE_EQ_EMPTY
  IMP_CONJ := Session.IMP_CONJ
  INFINITE := Session.INFINITE
  INTEGRAL_DOMAIN_ASSOCIATES := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_ASSOCIATES»
  INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING»
  INTEGRAL_DOMAIN_RING_OF_INTEGERS := SessionANT.Numfield.«INTEGRAL_DOMAIN_RING_OF_INTEGERS»
  INTEGRAL_DOMAIN_ROOTS_OF_UNITY_CYCLIC := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_ROOTS_OF_UNITY_CYCLIC»
  INT_LE_ANTISYM := Session.INT_LE_ANTISYM
  INT_LT_IMP_LE := Session.INT_LT_IMP_LE
  INT_LT_IMP_NE := Session.INT_LT_IMP_NE
  INT_NOT_LT := Session.INT_NOT_LT
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  IN_DELETE := Session.IN_DELETE
  IN_DIFF := Session.IN_DIFF
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_IMAGE := Session.IN_IMAGE
  IN_SING := Session.IN_SING
  IN_UNIV := Session.IN_UNIV
  ITER := SessionLibrary.Iter.«ITER»
  ITERATE_CASES := Session.ITERATE_CASES
  LE_1 := Session.LE_1
  LE_ANTISYM := Session.LE_ANTISYM
  LT_CASES := Session.LT_CASES
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONOIDAL_REAL_MUL := Session.MONOIDAL_REAL_MUL
  MONO_AND := Session.MONO_AND
  MONO_EXISTS := Session.MONO_EXISTS
  MONO_FORALL := Session.MONO_FORALL
  NORM_POS_LE := SessionMultiLib.Vectors.«NORM_POS_LE»
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
/-- The core theorems unit_theorem.ml uses. -/
def core2 : HolANT.UnitTheorem.CoreThms2 where
  NPRODUCT_DELETE := SessionLibrary.Products.«NPRODUCT_DELETE»
  NPRODUCT_POS_LT := SessionLibrary.Products.«NPRODUCT_POS_LT»
  NUMBER_FIELD_DISCRIMINANT_NONZERO := SessionANT.Discriminant.«NUMBER_FIELD_DISCRIMINANT_NONZERO»
  NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM := SessionANT.Classgroup.«NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM»
  NUMBER_FIELD_IDEAL_MINKOWSKI := SessionANT.MinkowskiTheory.«NUMBER_FIELD_IDEAL_MINKOWSKI»
  NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS := SessionANT.InfinitePlaces.«NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_ROOTS_OF_UNITY_FINITE := SessionANT.ComplexEmbeddings.«NUMBER_FIELD_ROOTS_OF_UNITY_FINITE»
  NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED := SessionANT.ComplexEmbeddings.«NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED»
  NUM_OF_INT_OF_NUM := Session.NUM_OF_INT_OF_NUM
  PRODUCT_CONST := SessionLibrary.Products.«PRODUCT_CONST»
  PRODUCT_DELETE := SessionLibrary.Products.«PRODUCT_DELETE»
  PRODUCT_EQ := SessionLibrary.Products.«PRODUCT_EQ»
  PRODUCT_EQ_0 := SessionLibrary.Products.«PRODUCT_EQ_0»
  PRODUCT_LE := SessionLibrary.Products.«PRODUCT_LE»
  PRODUCT_LE_1 := SessionLibrary.Products.«PRODUCT_LE_1»
  PRODUCT_LT_1 := SessionLibrary.Products.«PRODUCT_LT_1»
  PRODUCT_MUL := SessionLibrary.Products.«PRODUCT_MUL»
  PRODUCT_ONE := SessionLibrary.Products.«PRODUCT_ONE»
  PRODUCT_POS_LE := SessionLibrary.Products.«PRODUCT_POS_LE»
  PRODUCT_POS_LT := SessionLibrary.Products.«PRODUCT_POS_LT»
  REAL_ABS_NZ := Session.REAL_ABS_NZ
  REAL_ARCH_SIMPLE := Session.REAL_ARCH_SIMPLE
  REAL_DIV_RMUL := Session.REAL_DIV_RMUL
  REAL_HALF := SessionMultiLib.Misc.«REAL_HALF»
  REAL_INV_LE_1 := Session.REAL_INV_LE_1
  REAL_LE_DIV := Session.REAL_LE_DIV
  REAL_LE_INV_EQ := Session.REAL_LE_INV_EQ
  REAL_LE_LMUL := Session.REAL_LE_LMUL
  REAL_LE_MUL2 := Session.REAL_LE_MUL2
  REAL_LE_REFL := Session.REAL_LE_REFL
  REAL_LE_RMUL := Session.REAL_LE_RMUL
  REAL_LE_TRANS := Session.REAL_LE_TRANS
  REAL_LTE_TRANS := Session.REAL_LTE_TRANS
  REAL_LT_DIV := Session.REAL_LT_DIV
  REAL_LT_IMP_LE := Session.REAL_LT_IMP_LE
  REAL_LT_IMP_NZ := Session.REAL_LT_IMP_NZ
  REAL_LT_LMUL_EQ := Session.REAL_LT_LMUL_EQ
  REAL_MUL_AC := Session.REAL_MUL_AC
  REAL_MUL_RID := Session.REAL_MUL_RID
  REAL_MUL_RINV := Session.REAL_MUL_RINV
  REAL_NOT_LE := Session.REAL_NOT_LE
  REAL_OF_INT_CLAUSES := Session.REAL_OF_INT_CLAUSES
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_OF_NUM_LE := Session.REAL_OF_NUM_LE
  REAL_POS := Session.REAL_POS
  REAL_POW_1 := Session.REAL_POW_1
  REAL_POW_1_LT := Session.REAL_POW_1_LT
  REAL_POW_LE_1 := Session.REAL_POW_LE_1
  REAL_POW_MONO := Session.REAL_POW_MONO
  REAL_POW_ROOT := SessionMultiLib.Transcendentals.«REAL_POW_ROOT»
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_IDEAL_CARRIER := SessionLibrary.RingTheory.«RING_IDEAL_CARRIER»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE := SessionANT.ComplexEmbeddings.«RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INTEGERS_UNIT_NORM_PRODUCT := SessionANT.InfinitePlaces.«RING_OF_INTEGERS_UNIT_NORM_PRODUCT»
  RING_POW_MUL := SessionLibrary.RingTheory.«RING_POW_MUL»
  RING_POW_ONE := SessionLibrary.RingTheory.«RING_POW_ONE»
  RING_UNIT_0 := SessionLibrary.RingTheory.«RING_UNIT_0»
  RING_UNIT_IN_CARRIER := SessionLibrary.RingTheory.«RING_UNIT_IN_CARRIER»
  ROOT_POS_LT := SessionMultiLib.Transcendentals.«ROOT_POS_LT»
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SQRT_POS_LT := Session.SQRT_POS_LT
  SUBSET := Session.SUBSET
  SUB_REFL := Session.SUB_REFL
  TRANSITIVE_STEPWISE_LT := Session.TRANSITIVE_STEPWISE_LT
  UNIT_GROUP := SessionLibrary.RingGroups.«UNIT_GROUP»
  UNIT_GROUP_POW := SessionLibrary.RingGroups.«UNIT_GROUP_POW»
  complex_embeddings := SessionANT.ComplexEmbeddings.«complex_embeddings»
  group_pow := SessionLibrary.GroupTheory.«group_pow»
  group_zpow := SessionLibrary.GroupTheory.«group_zpow»
  infinite_places := SessionANT.InfinitePlaces.«infinite_places»
  lemma := SessionMultiLib.Integration.«lemma»
  num_INFINITE := Session.num_INFINITE
  o_DEF := Session.o_DEF
  product := Session.product

/-- What unit_theorem.ml uses from Session. -/
def deps : HolANT.UnitTheorem.UnitTheoremDeps where
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

/- The bundles, in unit_theorem.ml order. -/
initialize BUnitTheorem01 : HolANT.UnitTheorem.UnitTheorem01 ←
  ioB "setupUnitTheorem01" (HolANT.UnitTheorem.setupUnitTheorem01 deps).run
initialize BUnitTheorem02 : HolANT.UnitTheorem.UnitTheorem02 ←
  ioB "setupUnitTheorem02" (HolANT.UnitTheorem.setupUnitTheorem02 deps BUnitTheorem01).run

-- UnitTheorem01
def NUMBER_FIELD_UNIT_DOMINANT_PLACE : thm := BUnitTheorem01.NUMBER_FIELD_UNIT_DOMINANT_PLACE
def NUMBER_FIELD_UNITS_INDEPENDENT : thm := BUnitTheorem01.NUMBER_FIELD_UNITS_INDEPENDENT
def NUMBER_FIELD_UNITS_DEPENDENT : thm := BUnitTheorem01.NUMBER_FIELD_UNITS_DEPENDENT
def NUMBER_FIELD_ROOTS_OF_UNITY_CYCLIC : thm := BUnitTheorem01.NUMBER_FIELD_ROOTS_OF_UNITY_CYCLIC
def NUMBER_FIELD_FUNDAMENTAL_UNITS : thm := BUnitTheorem01.NUMBER_FIELD_FUNDAMENTAL_UNITS

-- UnitTheorem02
def NUMBER_FIELD_UNITS_ROOTS_OF_UNITY : thm := BUnitTheorem02.NUMBER_FIELD_UNITS_ROOTS_OF_UNITY

/-- `needs "ANT/unit_theorem.ml"`: already done by importing this module. -/
def ensureUnitTheorem : IO Unit := pure ()

end SessionANT.UnitTheorem
