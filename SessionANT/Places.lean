/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/places.ml                                     . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/Places.lean

  The session half of the places.ml translation: it supplies HolANT.Places's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/places.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.Places
import SessionLibrary.Products
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
import SessionLibrary.Isum
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.NfValuation
import SessionANT.PrimeSplit
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionANT.Integrality
import SessionLibrary.RingGroups
import SessionANT.FingenGroup
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
import SessionANT.ValuationRing
import SessionANT.DedekindAbsolute
import SessionANT.ProductFormula
import SessionANT.AbsoluteValues

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.Places

/-- The core theorems places.ml uses. -/
def core1 : HolANT.Places.CoreThms1 where
  ABSOLUTE_VALUE_0 := SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_0»
  ABSOLUTE_VALUE_1 := SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_1»
  ABSOLUTE_VALUE_DIV := SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_DIV»
  ABSOLUTE_VALUE_MUL := SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_MUL»
  ABSOLUTE_VALUE_NEG := SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_NEG»
  ABSOLUTE_VALUE_POS := SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_POS»
  ABSOLUTE_VALUE_RING_OF_NUM_LE := SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_RING_OF_NUM_LE»
  ABSOLUTE_VALUE_TRIANGLE := SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_TRIANGLE»
  ADD1 := Session.ADD1
  ADD_CLAUSES := Session.ADD_CLAUSES
  COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE := SessionANT.ProductFormula.«COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE»
  COMPLEX_EMBEDDINGS_HAS_SIZE := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_HAS_SIZE»
  COMPLEX_EMBEDDINGS_MONOMORPHISM := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_MONOMORPHISM»
  COMPLEX_NORM_CX := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_CX»
  COMPLEX_RING_CLAUSES := SessionMultiLib.ComplexRing.«COMPLEX_RING_CLAUSES»
  COMPLEX_RING_OF_INT := SessionMultiLib.ComplexRing.«COMPLEX_RING_OF_INT»
  CONJ_ASSOC := Session.CONJ_ASSOC
  CX_DIV := SessionMultiLib.ComplexAlgebra.«CX_DIV»
  CX_INJ := SessionMultiLib.ComplexAlgebra.«CX_INJ»
  DEDEKIND_NONARCHIMEDEAN_ABSOLUTE_VALUE := SessionANT.AbsoluteValues.«DEDEKIND_NONARCHIMEDEAN_ABSOLUTE_VALUE»
  DIVIDES_PRIME_PRIME := SessionLibrary.Prime.«DIVIDES_PRIME_PRIME»
  DIVISION := Session.DIVISION
  EQ_IMP := Session.EQ_IMP
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_INT_CASES := Session.EXISTS_INT_CASES
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXP := Session.EXP
  EXP_1 := Session.EXP_1
  EXP_ADD := Session.EXP_ADD
  EXP_EQ_0 := Session.EXP_EQ_0
  EXP_LOG := SessionMultiLib.Transcendentals.«EXP_LOG»
  EXP_LT_0 := Session.EXP_LT_0
  EXP_MONO_LE := Session.EXP_MONO_LE
  EXTENSION := Session.EXTENSION
  FIELD_HOMOMORPHISM_DIV := SessionLibrary.RingTheory.«FIELD_HOMOMORPHISM_DIV»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FIELD_REAL_RING := SessionLibrary.RingTheory.«FIELD_REAL_RING»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_IMAGE_INJ_EQ := Session.FINITE_IMAGE_INJ_EQ
  FORALL_INT_CASES := Session.FORALL_INT_CASES
  HAS_SIZE := Session.HAS_SIZE
  IDEAL_GENERATED_INC_GEN := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC_GEN»
  IDEAL_NORM_GT_1 := SessionANT.IdealNorm.«IDEAL_NORM_GT_1»
  INTEGER_CLOSED := SessionLibrary.Floor.«INTEGER_CLOSED»
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_SING := Session.IN_SING
  I_THM := Session.I_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_1 := Session.LE_1
  LE_EXP := Session.LE_EXP
  LE_TRANS := Session.LE_TRANS
  LOG_MONO_LE := SessionMultiLib.Transcendentals.«LOG_MONO_LE»
  LOG_MONO_LE_IMP := SessionMultiLib.Transcendentals.«LOG_MONO_LE_IMP»
  LOG_POS_LT := SessionMultiLib.Transcendentals.«LOG_POS_LT»
  LOG_POW := SessionMultiLib.Transcendentals.«LOG_POW»
  LOG_RPOW := SessionMultiLib.Transcendentals.«LOG_RPOW»
  LTE_TRANS := Session.LTE_TRANS
  LT_IMP_LE := Session.LT_IMP_LE
  LT_POW2_REFL := Session.LT_POW2_REFL
  MONO_EXISTS := Session.MONO_EXISTS
  MONO_IMP := Session.MONO_IMP
  NONARCHIMEDEAN_ABSOLUTE_VALUE_BOUNDED := SessionANT.DedekindAbsolute.«NONARCHIMEDEAN_ABSOLUTE_VALUE_BOUNDED»
  NONARCHIMEDEAN_ABSOLUTE_VALUE_INTEGRAL := SessionANT.DedekindAbsolute.«NONARCHIMEDEAN_ABSOLUTE_VALUE_INTEGRAL»
  NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INT := SessionANT.DedekindAbsolute.«NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INT»
  NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE := SessionANT.DedekindAbsolute.«NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE»
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS := SessionANT.InfinitePlaces.«NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_PRIME_SUBFIELD := SessionANT.Numfield.«NUMBER_FIELD_PRIME_SUBFIELD»
  NUMBER_FIELD_PRODUCT_FORMULA := SessionANT.ProductFormula.«NUMBER_FIELD_PRODUCT_FORMULA»
  NUMBER_FIELD_RATIONAL_FIELD := SessionANT.Numfield.«NUMBER_FIELD_RATIONAL_FIELD»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_PROPER_IDEAL»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRIME_SUBFIELD_CHAR_0 := SessionANT.Numfield.«PRIME_SUBFIELD_CHAR_0»
  PRIME_SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_SUBFIELD_GENERATED»
  PRODUCT_CONST := SessionLibrary.Products.«PRODUCT_CONST»
  PRODUCT_EQ := SessionLibrary.Products.«PRODUCT_EQ»
  PRODUCT_IMAGE := SessionLibrary.Products.«PRODUCT_IMAGE»
  PROPER_IDEAL_ALT := SessionLibrary.RingTheory.«PROPER_IDEAL_ALT»
  RDIV_LT_EQ := Session.RDIV_LT_EQ
/-- The core theorems places.ml uses. -/
def core2 : HolANT.Places.CoreThms2 where
  REAL_ABS_DIV := Session.REAL_ABS_DIV
  REAL_ABS_NEG := Session.REAL_ABS_NEG
  REAL_ABS_NUM := Session.REAL_ABS_NUM
  REAL_DIV_RMUL := Session.REAL_DIV_RMUL
  REAL_LE_ANTISYM := Session.REAL_LE_ANTISYM
  REAL_LE_LDIV_EQ := Session.REAL_LE_LDIV_EQ
  REAL_LE_LMUL := Session.REAL_LE_LMUL
  REAL_LE_MUL2 := Session.REAL_LE_MUL2
  REAL_LE_RADD := Session.REAL_LE_RADD
  REAL_LE_RDIV_EQ := Session.REAL_LE_RDIV_EQ
  REAL_LE_REFL := Session.REAL_LE_REFL
  REAL_LE_TRANS := Session.REAL_LE_TRANS
  REAL_LT_DIV := Session.REAL_LT_DIV
  REAL_LT_IMP_LE := Session.REAL_LT_IMP_LE
  REAL_LT_IMP_NZ := Session.REAL_LT_IMP_NZ
  REAL_LT_RDIV_EQ := Session.REAL_LT_RDIV_EQ
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_RID := Session.REAL_MUL_RID
  REAL_NOT_LE := Session.REAL_NOT_LE
  REAL_NOT_LT := Session.REAL_NOT_LT
  REAL_OF_NUM_ADD := Session.REAL_OF_NUM_ADD
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_OF_NUM_LE := Session.REAL_OF_NUM_LE
  REAL_OF_NUM_LT := Session.REAL_OF_NUM_LT
  REAL_OF_NUM_POW := Session.REAL_OF_NUM_POW
  REAL_OF_NUM_SUC := Session.REAL_OF_NUM_SUC
  REAL_POS := Session.REAL_POS
  REAL_POW_1 := Session.REAL_POW_1
  REAL_POW_DIV := Session.REAL_POW_DIV
  REAL_POW_EVENTUALLY_GT_LINEAR := SessionANT.DedekindAbsolute.«REAL_POW_EVENTUALLY_GT_LINEAR»
  REAL_POW_LE := Session.REAL_POW_LE
  REAL_POW_LE_1 := Session.REAL_POW_LE_1
  REAL_POW_LT := Session.REAL_POW_LT
  REAL_RING_CHAR := SessionLibrary.RingTheory.«REAL_RING_CHAR»
  REAL_RING_CLAUSES := SessionLibrary.RingTheory.«REAL_RING_CLAUSES»
  REAL_RING_DIV := SessionLibrary.RingTheory.«REAL_RING_DIV»
  REAL_RING_OF_INT := SessionLibrary.RingTheory.«REAL_RING_OF_INT»
  REAL_RING_OF_NUM := SessionLibrary.RingTheory.«REAL_RING_OF_NUM»
  REAL_ZPOW_RPOW := SessionMultiLib.Transcendentals.«REAL_ZPOW_RPOW»
  RINGS_EQ := SessionLibrary.RingTheory.«RINGS_EQ»
  RING_CHAR_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_CHAR_SUBFIELD_GENERATED»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_CARRIER := SessionANT.Numfield.«RING_OF_INTEGERS_CARRIER»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_FRACTION_FIELD := SessionANT.NfValuation.«RING_OF_INTEGERS_FRACTION_FIELD»
  RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL := SessionANT.RelativeSplit.«RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL»
  RING_OF_INTEGERS_RATIONAL_FIELD := SessionANT.RelativeSplit.«RING_OF_INTEGERS_RATIONAL_FIELD»
  RING_OF_INT_CASES := SessionLibrary.RingTheory.«RING_OF_INT_CASES»
  RING_OF_INT_IN_PRIME_IDEAL := SessionANT.PrimeSplit.«RING_OF_INT_IN_PRIME_IDEAL»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_INT_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_SUBFIELD_GENERATED»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_1 := SessionLibrary.RingTheory.«RING_OF_NUM_1»
  RING_OF_NUM_ADD := SessionLibrary.RingTheory.«RING_OF_NUM_ADD»
  RING_OF_NUM_MUL := SessionLibrary.RingTheory.«RING_OF_NUM_MUL»
  RING_OF_NUM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_NUM_SUBFIELD_GENERATED»
  RPOW_DIV := SessionMultiLib.Transcendentals.«RPOW_DIV»
  RPOW_LE_1 := SessionMultiLib.Transcendentals.«RPOW_LE_1»
  RPOW_LT_1 := SessionMultiLib.Transcendentals.«RPOW_LT_1»
  RPOW_MONO_LE := SessionMultiLib.Transcendentals.«RPOW_MONO_LE»
  RPOW_MONO_LE_EQ := SessionMultiLib.Transcendentals.«RPOW_MONO_LE_EQ»
  RPOW_ONE := SessionMultiLib.Transcendentals.«RPOW_ONE»
  RPOW_POS_LT := SessionMultiLib.Transcendentals.«RPOW_POS_LT»
  RPOW_POW := SessionMultiLib.Transcendentals.«RPOW_POW»
  RPOW_RPOW := SessionMultiLib.Transcendentals.«RPOW_RPOW»
  RPOW_ZERO := SessionMultiLib.Transcendentals.«RPOW_ZERO»
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  int_eq := Session.int_eq
  int_neg_th := Session.int_neg_th
  int_of_num_th := Session.int_of_num_th
  num_WOP := Session.num_WOP
  num_divides := Session.num_divides
  o_DEF := Session.o_DEF
  real_pow := Session.real_pow
  ring_of_num := SessionLibrary.RingTheory.«ring_of_num»
  rpow := SessionMultiLib.Transcendentals.«rpow»

/-- What places.ml uses from Session. -/
def deps : HolANT.Places.PlacesDeps where
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
  COMPLEX_FIELD t := ExceptT.mk (SessionMultiLib.ComplexAlgebra.COMPLEX_FIELD t)
  core1 := core1
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in places.ml order. -/
initialize BPlaces01 : HolANT.Places.Places01 ←
  ioB "setupPlaces01" (HolANT.Places.setupPlaces01 deps).run
initialize BPlaces02 : HolANT.Places.Places02 ←
  ioB "setupPlaces02" (HolANT.Places.setupPlaces02 deps BPlaces01).run

-- Places01
def NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INTEGERS : thm := BPlaces01.NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INTEGERS
def NUMBER_FIELD_NONARCHIMEDEAN_ABSOLUTE_VALUE : thm := BPlaces01.NUMBER_FIELD_NONARCHIMEDEAN_ABSOLUTE_VALUE
def NUMBER_FIELD_NONARCHIMEDEAN_ABSOLUTE_VALUE_EQUIVALENT : thm := BPlaces01.NUMBER_FIELD_NONARCHIMEDEAN_ABSOLUTE_VALUE_EQUIVALENT
def COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE_ARCHIMEDEAN : thm := BPlaces01.COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE_ARCHIMEDEAN
def OSTROWSKI_DIGITS_LEMMA : thm := BPlaces01.OSTROWSKI_DIGITS_LEMMA
def OSTROWSKI_BOUND_LEMMA : thm := BPlaces01.OSTROWSKI_BOUND_LEMMA
def OSTROWSKI_NUM_LEMMA : thm := BPlaces01.OSTROWSKI_NUM_LEMMA
def PRIME_SUBFIELD_IDEAL_GENERATED_PRIME_EQ : thm := BPlaces01.PRIME_SUBFIELD_IDEAL_GENERATED_PRIME_EQ
def OSTROWSKI_PRIME_SUBFIELD : thm := BPlaces01.OSTROWSKI_PRIME_SUBFIELD
def OSTROWSKI : thm := BPlaces01.OSTROWSKI
def OSTROWSKI_RATIONAL : thm := BPlaces01.OSTROWSKI_RATIONAL
def RATIONAL_FIELD_COMPLEX_EMBEDDINGS : thm := BPlaces01.RATIONAL_FIELD_COMPLEX_EMBEDDINGS

-- Places02
def RATIONAL_PRODUCT_FORMULA : thm := BPlaces02.RATIONAL_PRODUCT_FORMULA

/-- `needs "ANT/places.ml"`: already done by importing this module. -/
def ensurePlaces : IO Unit := pure ()

end SessionANT.Places
