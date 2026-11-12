/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/regulator.ml                                  . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/Regulator.lean

  The session half of the regulator.ml translation: it supplies HolANT.Regulator's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/regulator.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.Regulator
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.Permutations
import SessionLibrary.Products
import SessionLibrary.RingDet
import SessionLibrary.Matroids
import SessionLibrary.FieldTheory
import SessionLibrary.Isum
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionLibrary.RingGroups
import SessionANT.FingenGroup
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.NfValuation
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
import SessionANT.PowerBasis
import SessionANT.InfinitePlaces
import SessionANT.LinearForms
import SessionANT.ClassgroupGroup
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.Quadratic
import SessionANT.MinkowskiTheory
import SessionANT.UnitTheorem

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.Regulator

/-- The core theorems regulator.ml uses. -/
def core1 : HolANT.Regulator.CoreThms1 where
  ABELIAN_UNIT_GROUP := SessionLibrary.RingGroups.«ABELIAN_UNIT_GROUP»
  CARD_DELETE := Session.CARD_DELETE
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_EQ_BIJECTION := Session.CARD_EQ_BIJECTION
  CARD_IMAGE_LE := Session.CARD_IMAGE_LE
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  CARD_SUBSET := Session.CARD_SUBSET
  COMPLEX_EMBEDDINGS_NONEMPTY := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_NONEMPTY»
  COMPLEX_EMBEDDINGS_NORM_EQ := SessionANT.InfinitePlaces.«COMPLEX_EMBEDDINGS_NORM_EQ»
  COMPLEX_EMBEDDINGS_NORM_FUN_EQ := SessionANT.InfinitePlaces.«COMPLEX_EMBEDDINGS_NORM_FUN_EQ»
  COMPLEX_EMBEDDINGS_NORM_POS := SessionANT.InfinitePlaces.«COMPLEX_EMBEDDINGS_NORM_POS»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSION := Session.EXTENSION
  FIELD_REAL_RING := SessionLibrary.RingTheory.«FIELD_REAL_RING»
  FIELD_UNIT := SessionLibrary.RingTheory.«FIELD_UNIT»
  FINITE_COMPLEX_EMBEDDINGS := SessionANT.ComplexEmbeddings.«FINITE_COMPLEX_EMBEDDINGS»
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_DIFF := Session.FINITE_DIFF
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INFINITE_PLACES := SessionANT.InfinitePlaces.«FINITE_INFINITE_PLACES»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  GROUP_REAL_MULTIPLICATIVE_ID_INV_POW := SessionLibrary.RingGroups.«GROUP_REAL_MULTIPLICATIVE_ID_INV_POW»
  GROUP_REAL_MULTIPLICATIVE_SUM := SessionLibrary.RingGroups.«GROUP_REAL_MULTIPLICATIVE_SUM»
  GROUP_REAL_MULTIPLICATIVE_ZPOW := SessionLibrary.RingGroups.«GROUP_REAL_MULTIPLICATIVE_ZPOW»
  GROUP_SUM := SessionLibrary.GroupTheory.«GROUP_SUM»
  GROUP_SUM_IMAGE := SessionLibrary.GroupTheory.«GROUP_SUM_IMAGE»
  GROUP_ZPOW := SessionLibrary.GroupTheory.«GROUP_ZPOW»
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_INDEX := Session.HAS_SIZE_INDEX
  IMAGE_EQ_EMPTY := Session.IMAGE_EQ_EMPTY
  IMP_CONJ := Session.IMP_CONJ
  INFINITE_PLACES_DEGREE := SessionANT.InfinitePlaces.«INFINITE_PLACES_DEGREE»
  INFINITE_PLACES_MUL := SessionANT.InfinitePlaces.«INFINITE_PLACES_MUL»
  INFINITE_PLACES_POS := SessionANT.InfinitePlaces.«INFINITE_PLACES_POS»
  INFINITE_PLACES_ROOT_OF_UNITY := SessionANT.InfinitePlaces.«INFINITE_PLACES_ROOT_OF_UNITY»
  INFINITE_PLACES_SUM := SessionANT.InfinitePlaces.«INFINITE_PLACES_SUM»
  INFINITE_PLACES_UNIT_GROUP := SessionANT.InfinitePlaces.«INFINITE_PLACES_UNIT_GROUP»
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGRAL_DOMAIN_REAL_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_REAL_RING»
  INT_MUL_EQ_1 := Session.INT_MUL_EQ_1
  IN_DELETE := Session.IN_DELETE
  IN_DIFF := Session.IN_DIFF
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_UNIV := Session.IN_UNIV
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LOG_1 := SessionMultiLib.Transcendentals.«LOG_1»
  LOG_INJ := SessionMultiLib.Transcendentals.«LOG_INJ»
  LOG_MONO_LT_IMP := SessionMultiLib.Transcendentals.«LOG_MONO_LT_IMP»
  LOG_PRODUCT := SessionMultiLib.Transcendentals.«LOG_PRODUCT»
  LOG_ZPOW := SessionMultiLib.Transcendentals.«LOG_ZPOW»
  LT := Session.LT
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONO_EXISTS := Session.MONO_EXISTS
  NUMBER_FIELD_FUNDAMENTAL_UNITS := SessionANT.UnitTheorem.«NUMBER_FIELD_FUNDAMENTAL_UNITS»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_UNIT_DOMINANT_PLACE := SessionANT.UnitTheorem.«NUMBER_FIELD_UNIT_DOMINANT_PLACE»
  REAL_ABS_NEG := Session.REAL_ABS_NEG
  REAL_ABS_NZ := Session.REAL_ABS_NZ
  REAL_ENTIRE := Session.REAL_ENTIRE
  REAL_EQ_MUL_LCANCEL := Session.REAL_EQ_MUL_LCANCEL
  REAL_LT_01 := Session.REAL_LT_01
  REAL_LT_MUL := Session.REAL_LT_MUL
  REAL_MUL_ASSOC := Session.REAL_MUL_ASSOC
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_RID := Session.REAL_MUL_RID
  REAL_MUL_RNEG := Session.REAL_MUL_RNEG
  REAL_NEG_EQ := Session.REAL_NEG_EQ
  REAL_NEG_NEG := Session.REAL_NEG_NEG
  REAL_OF_NUM_LT := Session.REAL_OF_NUM_LT
  REAL_RING_CLAUSES := SessionLibrary.RingTheory.«REAL_RING_CLAUSES»
  REAL_RING_OF_INT := SessionLibrary.RingTheory.«REAL_RING_OF_INT»
  REAL_RING_SUM := SessionLibrary.RingTheory.«REAL_RING_SUM»
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RING_DET_DEPENDENT_COLUMNS := SessionLibrary.RingDet.«RING_DET_DEPENDENT_COLUMNS»
  RING_DET_EMPTY := SessionLibrary.RingDet.«RING_DET_EMPTY»
  RING_DET_EQ := SessionLibrary.RingDet.«RING_DET_EQ»
  RING_DET_HOMOMORPHISM := SessionLibrary.RingDet.«RING_DET_HOMOMORPHISM»
  RING_DET_MUL := SessionLibrary.RingDet.«RING_DET_MUL»
  RING_DET_REAL_DIAGONALLY_DOMINANT := SessionLibrary.RingDet.«RING_DET_REAL_DIAGONALLY_DOMINANT»
  RING_DET_REINDEX := SessionLibrary.RingDet.«RING_DET_REINDEX»
  RING_DET_ROWS_OMIT := SessionLibrary.RingDet.«RING_DET_ROWS_OMIT»
  RING_DET_ROWS_SAME_IMAGE := SessionLibrary.RingDet.«RING_DET_ROWS_SAME_IMAGE»
  RING_DET_ROW_NEG_SUM := SessionLibrary.RingDet.«RING_DET_ROW_NEG_SUM»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_MATRIX_SOLVE := SessionLibrary.RingDet.«RING_MATRIX_SOLVE»
  RING_OF_INTEGERS_ROOT_OF_UNITY := SessionANT.ComplexEmbeddings.«RING_OF_INTEGERS_ROOT_OF_UNITY»
  RING_OF_INTEGERS_UNIT_NONZERO := SessionANT.Numfield.«RING_OF_INTEGERS_UNIT_NONZERO»
  RING_OF_INTEGERS_UNIT_NORM_PRODUCT := SessionANT.InfinitePlaces.«RING_OF_INTEGERS_UNIT_NORM_PRODUCT»
  RING_UNIT_IN_CARRIER := SessionLibrary.RingTheory.«RING_UNIT_IN_CARRIER»
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  SUB_REFL := Session.SUB_REFL
  SUM_CLAUSES := Session.SUM_CLAUSES
  SUM_DELETE := Session.SUM_DELETE
  SUM_DIFF := Session.SUM_DIFF
  SUM_EQ := Session.SUM_EQ
  SUM_IMAGE := Session.SUM_IMAGE
  SUM_LMUL := Session.SUM_LMUL
  SUM_NEG := Session.SUM_NEG
  SUM_POS_LE := Session.SUM_POS_LE
  SUM_SWAP := Session.SUM_SWAP
  UNIT_GROUP := SessionLibrary.RingGroups.«UNIT_GROUP»
  infinite_places := SessionANT.InfinitePlaces.«infinite_places»
  int_eq := Session.int_eq
  int_mul_th := Session.int_mul_th
  int_neg_th := Session.int_neg_th
  int_of_num_th := Session.int_of_num_th
  o_DEF := Session.o_DEF

/-- What regulator.ml uses from Session. -/
def deps : HolANT.Regulator.RegulatorDeps where
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

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in regulator.ml order. -/
initialize BRegulator01 : HolANT.Regulator.Regulator01 ←
  ioB "setupRegulator01" (HolANT.Regulator.setupRegulator01 deps).run
initialize BRegulator02 : HolANT.Regulator.Regulator02 ←
  ioB "setupRegulator02" (HolANT.Regulator.setupRegulator02 deps BRegulator01).run

-- Regulator01
def REAL_MATRIX_SOLVE : thm := BRegulator01.REAL_MATRIX_SOLVE
def RING_DET_REAL_OF_INT : thm := BRegulator01.RING_DET_REAL_OF_INT
def RING_DET_REAL_ROW_NEG_SUM : thm := BRegulator01.RING_DET_REAL_ROW_NEG_SUM
def RING_DET_REAL_ROWS_SAME_IMAGE : thm := BRegulator01.RING_DET_REAL_ROWS_SAME_IMAGE
def RING_DET_REAL_ROWS_OMIT : thm := BRegulator01.RING_DET_REAL_ROWS_OMIT
def GROUP_REAL_MULTIPLICATIVE_LOG_SUM_ZPOW : thm := BRegulator01.GROUP_REAL_MULTIPLICATIVE_LOG_SUM_ZPOW
def NUMBER_FIELD_LOG_UNIT_SUM : thm := BRegulator01.NUMBER_FIELD_LOG_UNIT_SUM
def NUMBER_FIELD_LOG_UNIT_EQ_0 : thm := BRegulator01.NUMBER_FIELD_LOG_UNIT_EQ_0
def NUMBER_FIELD_LOG_UNIT_COMBINATION : thm := BRegulator01.NUMBER_FIELD_LOG_UNIT_COMBINATION
def NUMBER_FIELD_UNIT_DOMINANT_INFINITE_PLACE : thm := BRegulator01.NUMBER_FIELD_UNIT_DOMINANT_INFINITE_PLACE
def NUMBER_FIELD_LOG_MATRIX_CHANGE : thm := BRegulator01.NUMBER_FIELD_LOG_MATRIX_CHANGE
def NUMBER_FIELD_LOG_MATRIX_NONZERO : thm := BRegulator01.NUMBER_FIELD_LOG_MATRIX_NONZERO
def NUMBER_FIELD_LOG_MATRIX_SYSTEM : thm := BRegulator01.NUMBER_FIELD_LOG_MATRIX_SYSTEM
def NUMBER_FIELD_LOG_MATRIX_INVARIANT : thm := BRegulator01.NUMBER_FIELD_LOG_MATRIX_INVARIANT

-- Regulator02
def NUMBER_FIELD_LOG_UNITS_LATTICE : thm := BRegulator02.NUMBER_FIELD_LOG_UNITS_LATTICE
def INFINITE_PLACES_LOCAL_DEGREES : thm := BRegulator02.INFINITE_PLACES_LOCAL_DEGREES
def number_field_regulator : thm := BRegulator02.number_field_regulator
def NUMBER_FIELD_REGULATOR_SYSTEM_EXISTS : thm := BRegulator02.NUMBER_FIELD_REGULATOR_SYSTEM_EXISTS
def NUMBER_FIELD_REGULATOR : thm := BRegulator02.NUMBER_FIELD_REGULATOR
def NUMBER_FIELD_REGULATOR_POS : thm := BRegulator02.NUMBER_FIELD_REGULATOR_POS
def NUMBER_FIELD_REGULATOR_RANK_0 : thm := BRegulator02.NUMBER_FIELD_REGULATOR_RANK_0

/-- `needs "ANT/regulator.ml"`: already done by importing this module. -/
def ensureRegulator : IO Unit := pure ()

end SessionANT.Regulator
