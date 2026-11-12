/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/quadratic_units.ml                            . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/QuadraticUnits.lean

  The session half of the quadratic_units.ml translation: it supplies HolANT.QuadraticUnits's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/quadratic_units.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.QuadraticUnits
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.Matroids
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionLibrary.FieldTheory
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.Integral
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionLibrary.RingGroups
import SessionANT.FingenGroup
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionANT.Quadratic
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
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
import SessionANT.MinkowskiTheory
import SessionANT.UnitTheorem
import SessionANT.Regulator
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionLibrary.FiniteFields
import SessionLibrary.Integer
import SessionLibrary.Multiplicative
import SessionLibrary.Primitive
import SessionANT.CyclotomicPoly
import SessionANT.RelativeDegree
import SessionANT.DedekindKummer
import SessionANT.CyclotomicField
import SessionANT.RootsOfUnity

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.QuadraticUnits

/-- The core theorems quadratic_units.ml uses. -/
def core1 : HolANT.QuadraticUnits.CoreThms1 where
  ARITH_EQ := Session.ARITH_EQ
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_INFINITE_PLACES := SessionANT.InfinitePlaces.«CARD_INFINITE_PLACES»
  CARD_INFINITE_PLACES_EQ_1 := SessionANT.InfinitePlaces.«CARD_INFINITE_PLACES_EQ_1»
  CARD_INFINITE_PLACE_EMBEDDINGS := SessionANT.InfinitePlaces.«CARD_INFINITE_PLACE_EMBEDDINGS»
  CARD_SING := Session.CARD_SING
  CARD_SUBSET_EQ := Session.CARD_SUBSET_EQ
  COMPLEX_EMBEDDINGS_HAS_SIZE := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_HAS_SIZE»
  COMPLEX_EMBEDDINGS_NONEMPTY := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_NONEMPTY»
  COMPLEX_EMBEDDINGS_PRIME_SUBFIELD_REAL := SessionANT.InfinitePlaces.«COMPLEX_EMBEDDINGS_PRIME_SUBFIELD_REAL»
  COMPLEX_EMBEDDINGS_ROOT_OF_UNITY := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_ROOT_OF_UNITY»
  COMPLEX_EQ := SessionMultiLib.ComplexAlgebra.«COMPLEX_EQ»
  COMPLEX_NORM_CX := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_CX»
  COMPLEX_NORM_MUL := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_MUL»
  COMPLEX_POW_2 := SessionMultiLib.ComplexAlgebra.«COMPLEX_POW_2»
  COMPLEX_RING_CLAUSES := SessionMultiLib.ComplexRing.«COMPLEX_RING_CLAUSES»
  COMPLEX_RING_OF_INT := SessionMultiLib.ComplexRing.«COMPLEX_RING_OF_INT»
  COMPLEX_RING_OF_NUM := SessionMultiLib.ComplexRing.«COMPLEX_RING_OF_NUM»
  COMPLEX_RING_POW := SessionMultiLib.ComplexRing.«COMPLEX_RING_POW»
  COMPLEX_SQNORM := SessionMultiLib.ComplexAlgebra.«COMPLEX_SQNORM»
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  CX_INJ := SessionMultiLib.ComplexAlgebra.«CX_INJ»
  CX_POW := SessionMultiLib.ComplexAlgebra.«CX_POW»
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  EXISTS_PAIR_THM := Session.EXISTS_PAIR_THM
  EXTENSION := Session.EXTENSION
  EXTENSIONAL := Session.EXTENSIONAL
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_MUL_RINV := SessionLibrary.RingTheory.«FIELD_MUL_RINV»
  FIELD_POW_EQ_0 := SessionLibrary.RingTheory.«FIELD_POW_EQ_0»
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  FST := Session.FST
  FUN_EQ_THM := Session.FUN_EQ_THM
  GROUP_REAL_MULTIPLICATIVE_ZPOW := SessionLibrary.RingGroups.«GROUP_REAL_MULTIPLICATIVE_ZPOW»
  GROUP_SUM_SING := SessionLibrary.GroupTheory.«GROUP_SUM_SING»
  GROUP_ZPOW := SessionLibrary.GroupTheory.«GROUP_ZPOW»
  GROUP_ZPOW_1 := SessionLibrary.GroupTheory.«GROUP_ZPOW_1»
  GROUP_ZPOW_2 := SessionLibrary.GroupTheory.«GROUP_ZPOW_2»
  GROUP_ZPOW_INV := SessionLibrary.GroupTheory.«GROUP_ZPOW_INV»
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_IMAGE_INJ := Session.HAS_SIZE_IMAGE_INJ
  IDEAL_GENERATED_INC := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC»
  IDEAL_GENERATED_SING_ALT := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING_ALT»
  IM := SessionMultiLib.ComplexAlgebra.«IM»
  IMP_CONJ := Session.IMP_CONJ
  IM_ADD := SessionMultiLib.ComplexAlgebra.«IM_ADD»
  IM_CX := SessionMultiLib.ComplexAlgebra.«IM_CX»
  INFINITE := Session.INFINITE
  INFINITE_IMAGE := Session.INFINITE_IMAGE
  INFINITE_SUPERSET := Session.INFINITE_SUPERSET
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_ELEMENT_QUADRATIC := SessionANT.Quadratic.«INTEGRAL_ELEMENT_QUADRATIC»
  INT_ABS_POS := Session.INT_ABS_POS
  INT_ENTIRE := Session.INT_ENTIRE
  INT_LE_LMUL := Session.INT_LE_LMUL
  INT_LE_MUL := Session.INT_LE_MUL
  INT_LE_MUL2 := Session.INT_LE_MUL2
  INT_LE_SQUARE_ABS := Session.INT_LE_SQUARE_ABS
  INT_LT_IMP_LE := Session.INT_LT_IMP_LE
  INT_LT_MUL := Session.INT_LT_MUL
  INT_LT_REFL := Session.INT_LT_REFL
  INT_LT_RMUL_EQ := Session.INT_LT_RMUL_EQ
  INT_MUL_LID := Session.INT_MUL_LID
  INT_MUL_LZERO := Session.INT_MUL_LZERO
  INT_MUL_RZERO := Session.INT_MUL_RZERO
  INT_NEG_NEG := Session.INT_NEG_NEG
  INT_NORM_FORM_4_IMAGINARY := SessionANT.Quadratic.«INT_NORM_FORM_4_IMAGINARY»
  INT_OF_NUM_ADD := Session.INT_OF_NUM_ADD
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_OF_NUM_POW := Session.INT_OF_NUM_POW
  INT_POW2_ABS := Session.INT_POW2_ABS
  INT_POW_LT := Session.INT_POW_LT
  INT_SQUAREFREE_DECOMPOSITION := SessionLibrary.Pocklington.«INT_SQUAREFREE_DECOMPOSITION»
  INT_SUB_RZERO := Session.INT_SUB_RZERO
  IN_ELIM_PAIR_THM := Session.IN_ELIM_PAIR_THM
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_SING := Session.IN_SING
  IN_UNIV := Session.IN_UNIV
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_1 := Session.LE_1
  LE_REFL := Session.LE_REFL
  LOG_POS_LT := SessionMultiLib.Transcendentals.«LOG_POS_LT»
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NUMBER_FIELD_FUNDAMENTAL_UNITS := SessionANT.UnitTheorem.«NUMBER_FIELD_FUNDAMENTAL_UNITS»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_REAL_ROOTS_OF_UNITY := SessionANT.RootsOfUnity.«NUMBER_FIELD_REAL_ROOTS_OF_UNITY»
  NUMBER_FIELD_REGULATOR := SessionANT.Regulator.«NUMBER_FIELD_REGULATOR»
  NUMBER_FIELD_RING_OF_NUM_EQ_0 := SessionANT.Numfield.«NUMBER_FIELD_RING_OF_NUM_EQ_0»
  NUMBER_FIELD_UNITS_EQ_ROOTS_OF_UNITY := SessionANT.RootsOfUnity.«NUMBER_FIELD_UNITS_EQ_ROOTS_OF_UNITY»
  NUMBER_FIELD_UNITS_ROOTS_OF_UNITY := SessionANT.UnitTheorem.«NUMBER_FIELD_UNITS_ROOTS_OF_UNITY»
  NUM_OF_INT_OF_NUM := Session.NUM_OF_INT_OF_NUM
  PAIR := Session.PAIR
  PAIR_EQ := Session.PAIR_EQ
  PRODUCT_CLAUSES := Session.PRODUCT_CLAUSES
  QUADRATIC_FIELD_COORDINATES := SessionANT.Quadratic.«QUADRATIC_FIELD_COORDINATES»
  QUADRATIC_FIELD_EXISTS := SessionANT.Quadratic.«QUADRATIC_FIELD_EXISTS»
  QUADRATIC_FIELD_INTEGRAL_COORDINATES := SessionANT.Quadratic.«QUADRATIC_FIELD_INTEGRAL_COORDINATES»
  QUADRATIC_FIELD_INT_COORDINATES_EQ := SessionANT.Quadratic.«QUADRATIC_FIELD_INT_COORDINATES_EQ»
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
/-- The core theorems quadratic_units.ml uses. -/
def core2 : HolANT.QuadraticUnits.CoreThms2 where
  RE := SessionMultiLib.ComplexAlgebra.«RE»
  REAL_ABS_MUL := Session.REAL_ABS_MUL
  REAL_ABS_NZ := Session.REAL_ABS_NZ
  REAL_ABS_REFL := Session.REAL_ABS_REFL
  REAL_ADD := SessionMultiLib.ComplexAlgebra.«REAL_ADD»
  REAL_ADD_RID := Session.REAL_ADD_RID
  REAL_EMBEDDINGS_MONOMORPHISM := SessionANT.InfinitePlaces.«REAL_EMBEDDINGS_MONOMORPHISM»
  REAL_ENTIRE := Session.REAL_ENTIRE
  REAL_EXISTS := SessionMultiLib.ComplexAlgebra.«REAL_EXISTS»
  REAL_FIELD_CLAUSES := SessionLibrary.RingTheory.«REAL_FIELD_CLAUSES»
  REAL_INV_1_LT := Session.REAL_INV_1_LT
  REAL_INV_NEG := Session.REAL_INV_NEG
  REAL_LE_POW_2 := Session.REAL_LE_POW_2
  REAL_LE_SQUARE := Session.REAL_LE_SQUARE
  REAL_LT_IMP_LE := Session.REAL_LT_IMP_LE
  REAL_MUL := SessionMultiLib.ComplexAlgebra.«REAL_MUL»
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_LZERO := Session.REAL_MUL_LZERO
  REAL_MUL_RID := Session.REAL_MUL_RID
  REAL_MUL_RINV_UNIQ := Session.REAL_MUL_RINV_UNIQ
  REAL_NORM := SessionMultiLib.ComplexAlgebra.«REAL_NORM»
  REAL_OF_INT_CLAUSES := Session.REAL_OF_INT_CLAUSES
  REAL_POW_LT_1 := Session.REAL_POW_LT_1
  REAL_RING_CLAUSES := SessionLibrary.RingTheory.«REAL_RING_CLAUSES»
  REAL_RING_OF_INT := SessionLibrary.RingTheory.«REAL_RING_OF_INT»
  REAL_SUB_RZERO := Session.REAL_SUB_RZERO
  REAL_ZPOW_0 := Session.REAL_ZPOW_0
  REAL_ZPOW_1 := Session.REAL_ZPOW_1
  REAL_ZPOW_LT := Session.REAL_ZPOW_LT
  REAL_ZPOW_MONO := Session.REAL_ZPOW_MONO
  REAL_ZPOW_MONO_LT := Session.REAL_ZPOW_MONO_LT
  RE_ADD := SessionMultiLib.ComplexAlgebra.«RE_ADD»
  RE_CX := SessionMultiLib.ComplexAlgebra.«RE_CX»
  RE_NEG := SessionMultiLib.ComplexAlgebra.«RE_NEG»
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RNEG := SessionLibrary.RingTheory.«RING_ADD_RNEG»
  RING_CARRIER_SUBFIELD_GENERATED_SUBSET := SessionLibrary.FieldTheory.«RING_CARRIER_SUBFIELD_GENERATED_SUBSET»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_DET_SING := SessionLibrary.RingDet.«RING_DET_SING»
  RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_RING_OF_NUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_NUM»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LNEG := SessionLibrary.RingTheory.«RING_MUL_LNEG»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RINV := SessionLibrary.RingTheory.«RING_MUL_RINV»
  RING_MUL_RNEG := SessionLibrary.RingTheory.«RING_MUL_RNEG»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_NEG_NEG := SessionLibrary.RingTheory.«RING_NEG_NEG»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_CARRIER := SessionANT.Numfield.«RING_OF_INTEGERS_CARRIER»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INTEGERS_UNIT_NONZERO := SessionANT.Numfield.«RING_OF_INTEGERS_UNIT_NONZERO»
  RING_OF_INTEGERS_UNIT_NORM_PRODUCT := SessionANT.InfinitePlaces.«RING_OF_INTEGERS_UNIT_NORM_PRODUCT»
  RING_OF_INT_0 := SessionLibrary.RingTheory.«RING_OF_INT_0»
  RING_OF_INT_1 := SessionLibrary.RingTheory.«RING_OF_INT_1»
  RING_OF_INT_ADD := SessionLibrary.RingTheory.«RING_OF_INT_ADD»
  RING_OF_INT_EQ_0_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0_CHAR_0»
  RING_OF_INT_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_IN_SUBFIELD_GENERATED»
  RING_OF_INT_MUL := SessionLibrary.RingTheory.«RING_OF_INT_MUL»
  RING_OF_INT_NEG := SessionLibrary.RingTheory.«RING_OF_INT_NEG»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_INT_POW := SessionLibrary.RingTheory.«RING_OF_INT_POW»
  RING_OF_INT_SUB := SessionLibrary.RingTheory.«RING_OF_INT_SUB»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_1 := SessionLibrary.RingTheory.«RING_OF_NUM_1»
  RING_OF_NUM_ADD := SessionLibrary.RingTheory.«RING_OF_NUM_ADD»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_1 := SessionLibrary.RingTheory.«RING_POW_1»
  RING_POW_2 := SessionLibrary.RingTheory.«RING_POW_2»
  RING_POW_ADD := SessionLibrary.RingTheory.«RING_POW_ADD»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_UNIT_1 := SessionLibrary.RingTheory.«RING_UNIT_1»
  RING_UNIT_INV := SessionLibrary.RingTheory.«RING_UNIT_INV»
  RING_UNIT_IN_CARRIER := SessionLibrary.RingTheory.«RING_UNIT_IN_CARRIER»
  RING_UNIT_NEG := SessionLibrary.RingTheory.«RING_UNIT_NEG»
  RING_UNIT_POW := SessionLibrary.RingTheory.«RING_UNIT_POW»
  SING_SUBSET := Session.SING_SUBSET
  SND := Session.SND
  SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD := SessionANT.Quadratic.«SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD»
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBSET := Session.SUBSET
  TRANSITIVE_STEPWISE_LT := Session.TRANSITIVE_STEPWISE_LT
  UNIT_GROUP := SessionLibrary.RingGroups.«UNIT_GROUP»
  UNIT_GROUP_ZPOW_RING_NEG := SessionLibrary.RingGroups.«UNIT_GROUP_ZPOW_RING_NEG»
  WLOG_LT := Session.WLOG_LT
  complex_embeddings := SessionANT.ComplexEmbeddings.«complex_embeddings»
  complex_mul := SessionMultiLib.ComplexAlgebra.«complex_mul»
  infinite_places := SessionANT.InfinitePlaces.«infinite_places»
  int_abs_th := Session.int_abs_th
  int_mul_th := Session.int_mul_th
  int_of_num_th := Session.int_of_num_th
  int_pow_th := Session.int_pow_th
  int_sub_th := Session.int_sub_th
  num_INFINITE := Session.num_INFINITE
  num_RECURSION := Session.num_RECURSION
  number_field := SessionANT.Numfield.«number_field»
  real := SessionMultiLib.ComplexAlgebra.«real»
  real_embeddings := SessionANT.InfinitePlaces.«real_embeddings»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  ring_unit := SessionLibrary.RingTheory.«ring_unit»
  squarefree := SessionLibrary.Pocklington.«squarefree»

/-- What quadratic_units.ml uses from Session. -/
def deps : HolANT.QuadraticUnits.QuadraticUnitsDeps where
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
  GEN_BETA_CONV := Session.GEN_BETA_CONV
  REAL_RING t := ExceptT.mk (Session.REAL_RING t)
  COMPLEX_RING t := ExceptT.mk (SessionMultiLib.ComplexAlgebra.COMPLEX_RING t)
  core1 := core1
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in quadratic_units.ml order. -/
initialize BQuadraticUnits01 : HolANT.QuadraticUnits.QuadraticUnits01 ←
  ioB "setupQuadraticUnits01" (HolANT.QuadraticUnits.setupQuadraticUnits01 deps).run
initialize BQuadraticUnits02 : HolANT.QuadraticUnits.QuadraticUnits02 ←
  ioB "setupQuadraticUnits02" (HolANT.QuadraticUnits.setupQuadraticUnits02 deps BQuadraticUnits01).run
initialize BQuadraticUnits03 : HolANT.QuadraticUnits.QuadraticUnits03 ←
  ioB "setupQuadraticUnits03" (HolANT.QuadraticUnits.setupQuadraticUnits03 deps BQuadraticUnits01 BQuadraticUnits02).run

-- QuadraticUnits01
def NUMBER_FIELD_FUNDAMENTAL_UNIT_REAL : thm := BQuadraticUnits01.NUMBER_FIELD_FUNDAMENTAL_UNIT_REAL
def NUMBER_FIELD_REGULATOR_FUNDAMENTAL_UNIT_REAL : thm := BQuadraticUnits01.NUMBER_FIELD_REGULATOR_FUNDAMENTAL_UNIT_REAL
def QUADRATIC_FIELD_REAL_EMBEDDINGS : thm := BQuadraticUnits01.QUADRATIC_FIELD_REAL_EMBEDDINGS
def QUADRATIC_FIELD_CONJUGATE_EMBEDDING : thm := BQuadraticUnits01.QUADRATIC_FIELD_CONJUGATE_EMBEDDING
def QUADRATIC_FIELD_INFINITE_PLACES : thm := BQuadraticUnits01.QUADRATIC_FIELD_INFINITE_PLACES
def QUADRATIC_FIELD_UNITS_IMAGINARY_ROOTS_OF_UNITY : thm := BQuadraticUnits01.QUADRATIC_FIELD_UNITS_IMAGINARY_ROOTS_OF_UNITY

-- QuadraticUnits02
def QUADRATIC_FIELD_UNIT_IMAGINARY : thm := BQuadraticUnits02.QUADRATIC_FIELD_UNIT_IMAGINARY
def QUADRATIC_FIELD_UNITS_IMAGINARY : thm := BQuadraticUnits02.QUADRATIC_FIELD_UNITS_IMAGINARY
def QUADRATIC_FIELD_UNITS_IMAGINARY_CARD : thm := BQuadraticUnits02.QUADRATIC_FIELD_UNITS_IMAGINARY_CARD
def QUADRATIC_FIELD_UNITS_IMAGINARY_GENERIC : thm := BQuadraticUnits02.QUADRATIC_FIELD_UNITS_IMAGINARY_GENERIC
def QUADRATIC_FIELD_FUNDAMENTAL_UNIT : thm := BQuadraticUnits02.QUADRATIC_FIELD_FUNDAMENTAL_UNIT
def QUADRATIC_FIELD_PELL_UNIT : thm := BQuadraticUnits02.QUADRATIC_FIELD_PELL_UNIT
def QUADRATIC_FIELD_UNIT_POW_IN_ORDER : thm := BQuadraticUnits02.QUADRATIC_FIELD_UNIT_POW_IN_ORDER

-- QuadraticUnits03
def QUADRATIC_FIELD_PELL_SOLUTION : thm := BQuadraticUnits03.QUADRATIC_FIELD_PELL_SOLUTION
def PELL_SOLUTION_IMP_INFINITE : thm := BQuadraticUnits03.PELL_SOLUTION_IMP_INFINITE
def PELL_EQUATION_INFINITE : thm := BQuadraticUnits03.PELL_EQUATION_INFINITE
def PELL_EQUATION_INFINITE_NUM : thm := BQuadraticUnits03.PELL_EQUATION_INFINITE_NUM

/-- `needs "ANT/quadratic_units.ml"`: already done by importing this module. -/
def ensureQuadraticUnits : IO Unit := pure ()

end SessionANT.QuadraticUnits
