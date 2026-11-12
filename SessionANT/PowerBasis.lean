/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/power_basis.ml                                . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/PowerBasis.lean

  The session half of the power_basis.ml translation: it supplies HolANT.PowerBasis's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/power_basis.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.PowerBasis
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
import SessionANT.Algmisc
import SessionLibrary.Isum
import SessionANT.Integral
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.PowerBasis

/-- The core theorems power_basis.ml uses. -/
def core1 : HolANT.PowerBasis.CoreThms1 where
  ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH := SessionLibrary.FieldTheory.«ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH»
  ALGEBRA_NORM_FREE_BASIS := SessionLibrary.RingDet.«ALGEBRA_NORM_FREE_BASIS»
  ALGEBRA_TRACE_FREE_BASIS := SessionLibrary.RingDet.«ALGEBRA_TRACE_FREE_BASIS»
  ALGEBRA_TRACE_NORM_EQ_IMAGE := SessionLibrary.RingDet.«ALGEBRA_TRACE_NORM_EQ_IMAGE»
  ALGEBRA_TRACE_NORM_INTERMEDIATE := SessionLibrary.FieldTheory.«ALGEBRA_TRACE_NORM_INTERMEDIATE»
  ALGEBRA_TRACE_NORM_IN_CARRIER := SessionLibrary.RingDet.«ALGEBRA_TRACE_NORM_IN_CARRIER»
  AND_FORALL_THM := Session.AND_FORALL_THM
  BASIS_COORDINATES := SessionLibrary.RingDet.«BASIS_COORDINATES»
  BASIS_COORDINATES_UNIQUE := SessionLibrary.RingDet.«BASIS_COORDINATES_UNIQUE»
  CARD_IMAGE_EQ_INJ := Session.CARD_IMAGE_EQ_INJ
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  COEFF_COMPOSE := SessionLibrary.RingTheory.«COEFF_COMPOSE»
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSION := Session.EXTENSION
  EXTENSIONAL_EQ := Session.EXTENSIONAL_EQ
  FIELD_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED»
  FIELD_EXTENSION_TRANS := SessionLibrary.FieldTheory.«FIELD_EXTENSION_TRANS»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_RING_HOMOMORPHISM_MONOMORPHISM := SessionLibrary.RingTheory.«FIELD_RING_HOMOMORPHISM_MONOMORPHISM»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FIELD_UNIT := SessionLibrary.RingTheory.«FIELD_UNIT»
  FINITE_EXTENSION_RING_MATROID := SessionLibrary.FieldTheory.«FINITE_EXTENSION_RING_MATROID»
  FINITE_IMP_ALGEBRAIC_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_ALGEBRAIC_EXTENSION»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FREE_BASIS_FIELD := SessionLibrary.FieldTheory.«FREE_BASIS_FIELD»
  FREE_BASIS_IN_CARRIER := SessionLibrary.RingDet.«FREE_BASIS_IN_CARRIER»
  FUN_EQ_THM := Session.FUN_EQ_THM
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_INDEX := Session.HAS_SIZE_INDEX
  HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS := SessionLibrary.FieldTheory.«HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS»
  IMAGE_I := Session.IMAGE_I
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_SING := Session.IN_SING
  IN_SUBFIELD_0 := SessionLibrary.FieldTheory.«IN_SUBFIELD_0»
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LE_REFL := Session.LE_REFL
  LT := Session.LT
  MATROID_BASIS_LARGE_INDEPENDENT := SessionLibrary.Matroids.«MATROID_BASIS_LARGE_INDEPENDENT»
  MINIMAL_POLYNOMIAL_IN_CARRIER := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_IN_CARRIER»
  MINIMAL_POLYNOMIAL_MONIC := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_MONIC»
  MINIMAL_POLYNOMIAL_POWERS_HAS_SIZE := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_POWERS_HAS_SIZE»
  MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE»
  MOD_LT_EQ := Session.MOD_LT_EQ
  MONIC_POLY_EQ_ROOTS_PRODUCT := SessionLibrary.RingTheory.«MONIC_POLY_EQ_ROOTS_PRODUCT»
  MULT_CLAUSES := Session.MULT_CLAUSES
  MUL_MATRIX_EXPAND := SessionLibrary.RingDet.«MUL_MATRIX_EXPAND»
  MUL_MATRIX_IN_CARRIER := SessionLibrary.RingDet.«MUL_MATRIX_IN_CARRIER»
  NUMBER_FIELD_ALGEBRAIC := SessionANT.Numfield.«NUMBER_FIELD_ALGEBRAIC»
  NUMBER_FIELD_FREE_BASIS := SessionANT.Numfield.«NUMBER_FIELD_FREE_BASIS»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  POLY_DEG_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_DEG_MONOMORPHIC_IMAGE»
  POLY_DERIV_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_DERIV_HOMOMORPHIC_IMAGE»
  POLY_DERIV_IN_CARRIER := SessionLibrary.RingTheory.«POLY_DERIV_IN_CARRIER»
  POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS := SessionLibrary.RingDet.«POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS»
  POLY_EXTEND := SessionLibrary.RingTheory.«POLY_EXTEND»
  POLY_EXTEND_EVALUATE := SessionLibrary.RingTheory.«POLY_EXTEND_EVALUATE»
  POLY_EXTEND_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_EXTEND_HOMOMORPHIC_IMAGE»
  PRIME_SUBFIELD_HOMOMORPHISM_EXISTS := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_HOMOMORPHISM_EXISTS»
  PRIME_SUBFIELD_MONOMORPHIC_IMAGE := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_MONOMORPHIC_IMAGE»
  PRIME_SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_SUBFIELD_GENERATED»
  RDIV_LT_EQ := Session.RDIV_LT_EQ
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_CARRIER_SUBFIELD_GENERATED_SUBSET := SessionLibrary.FieldTheory.«RING_CARRIER_SUBFIELD_GENERATED_SUBSET»
  RING_CHAR_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_CHAR_MONOMORPHIC_IMAGE»
  RING_CHAR_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_CHAR_SUBFIELD_GENERATED»
  RING_DET := SessionLibrary.RingDet.«RING_DET»
  RING_DET_EQ := SessionLibrary.RingDet.«RING_DET_EQ»
  RING_DET_HOMOMORPHISM := SessionLibrary.RingDet.«RING_DET_HOMOMORPHISM»
  RING_DET_INDEPENDENT_ROWS := SessionLibrary.RingDet.«RING_DET_INDEPENDENT_ROWS»
  RING_DET_MUL := SessionLibrary.RingDet.«RING_DET_MUL»
  RING_DET_TRANSP := SessionLibrary.RingDet.«RING_DET_TRANSP»
  RING_DET_VANDERMONDE := SessionLibrary.RingDet.«RING_DET_VANDERMONDE»
  RING_HOMOMORPHISMS_EQ_FROM_RING_SPAN := SessionLibrary.FieldTheory.«RING_HOMOMORPHISMS_EQ_FROM_RING_SPAN»
  RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED»
  RING_HOMOMORPHISMS_INDEPENDENT := SessionLibrary.FieldTheory.«RING_HOMOMORPHISMS_INDEPENDENT»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_FROM_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_FROM_SUBRING_GENERATED»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_NEG := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_NEG»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_RING_OF_NUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_NUM»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_HOMOMORPHISM_SUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM»
  RING_HOMOMORPHISM_SUM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM_MUL»
  RING_INDEPENDENT_MINIMAL_POLYNOMIAL_POWERS := SessionLibrary.FieldTheory.«RING_INDEPENDENT_MINIMAL_POLYNOMIAL_POWERS»
  RING_MATROID_BASIS := SessionLibrary.FieldTheory.«RING_MATROID_BASIS»
  RING_MATROID_INDEPENDENT := SessionLibrary.FieldTheory.«RING_MATROID_INDEPENDENT»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_NUM_SUBFIELD_GENERATED»
  RING_POLYNOMIAL := SessionLibrary.RingTheory.«RING_POLYNOMIAL»
  RING_POLYNOMIAL_COMPOSE := SessionLibrary.RingTheory.«RING_POLYNOMIAL_COMPOSE»
  RING_POLYNOMIAL_IMP_POWERSERIES := SessionLibrary.RingTheory.«RING_POLYNOMIAL_IMP_POWERSERIES»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_2 := SessionLibrary.RingTheory.«RING_POW_2»
  RING_POW_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_POW_SUBFIELD_GENERATED»
  RING_PRODUCT_DIFFERENCES_SQUARE := SessionLibrary.RingDet.«RING_PRODUCT_DIFFERENCES_SQUARE»
  RING_PRODUCT_EQ := SessionLibrary.RingTheory.«RING_PRODUCT_EQ»
  RING_PRODUCT_IMAGE := SessionLibrary.RingTheory.«RING_PRODUCT_IMAGE»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_EQ_0 := SessionLibrary.RingTheory.«RING_SUM_EQ_0»
  RING_SUM_IMAGE := SessionLibrary.RingTheory.«RING_SUM_IMAGE»
  RING_SUM_MUL_MOD_DIV := SessionLibrary.RingTheory.«RING_SUM_MUL_MOD_DIV»
  RING_SUM_MUL_SWAP := SessionLibrary.RingDet.«RING_SUM_MUL_SWAP»
  RING_TRACE_DET_SIMILAR_DIAGONAL := SessionLibrary.RingDet.«RING_TRACE_DET_SIMILAR_DIAGONAL»
  SEPARABLE_EXTENSION_CHAR0 := SessionLibrary.FieldTheory.«SEPARABLE_EXTENSION_CHAR0»
  SIMPLE_IMAGE_GEN := Session.SIMPLE_IMAGE_GEN
  SING_SUBSET := Session.SING_SUBSET
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_MINIMAL := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_MINIMAL»
  SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_SUBFIELD_GENERATED»
  SUBRING_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBRING_GENERATED_BY_SUBFIELD_GENERATED»
  SUBSET := Session.SUBSET
  algebraic_extension := SessionLibrary.FieldTheory.«algebraic_extension»
  algebraically_closed_field := SessionLibrary.FieldTheory.«algebraically_closed_field»
  basis_discriminant := SessionLibrary.RingDet.«basis_discriminant»
  extension_degree := SessionLibrary.FieldTheory.«extension_degree»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  monic := SessionLibrary.RingTheory.«monic»
  mul_matrix := SessionLibrary.RingDet.«mul_matrix»
  number_field := SessionANT.Numfield.«number_field»
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM
  poly_eval := SessionLibrary.RingTheory.«poly_eval»
  ring_basis := SessionLibrary.FieldTheory.«ring_basis»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_homomorphism_extensions := SessionLibrary.FieldTheory.«ring_homomorphism_extensions»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  ring_polynomial := SessionLibrary.RingTheory.«ring_polynomial»
  ring_powerseries := SessionLibrary.RingTheory.«ring_powerseries»
  ring_spanning := SessionLibrary.FieldTheory.«ring_spanning»

/-- What power_basis.ml uses from Session. -/
def deps : HolANT.PowerBasis.PowerBasisDeps where
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

/- The bundles, in power_basis.ml order. -/
initialize BPowerBasis01 : HolANT.PowerBasis.PowerBasis01 ←
  ioB "setupPowerBasis01" (HolANT.PowerBasis.setupPowerBasis01 deps).run
initialize BPowerBasis02 : HolANT.PowerBasis.PowerBasis02 ←
  ioB "setupPowerBasis02" (HolANT.PowerBasis.setupPowerBasis02 deps).run

-- PowerBasis01
def NUMBER_FIELD_TRACE_HOMOMORPHISMS : thm := BPowerBasis01.NUMBER_FIELD_TRACE_HOMOMORPHISMS
def NUMBER_FIELD_NORM_HOMOMORPHISMS : thm := BPowerBasis01.NUMBER_FIELD_NORM_HOMOMORPHISMS
def NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS : thm := BPowerBasis01.NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS
def NUMBER_FIELD_HOMOMORPHISMS_HAS_SIZE : thm := BPowerBasis01.NUMBER_FIELD_HOMOMORPHISMS_HAS_SIZE
def NUMBER_FIELD_FREE_BASIS_POWERS : thm := BPowerBasis01.NUMBER_FIELD_FREE_BASIS_POWERS
def NUMBER_FIELD_DISCRIMINANT_POWER_BASIS : thm := BPowerBasis01.NUMBER_FIELD_DISCRIMINANT_POWER_BASIS

-- PowerBasis02
def NUMBER_FIELD_TRACE_TOWER : thm := BPowerBasis02.NUMBER_FIELD_TRACE_TOWER
def NUMBER_FIELD_NORM_TOWER : thm := BPowerBasis02.NUMBER_FIELD_NORM_TOWER
def ALGEBRA_TRACE_PRODUCT_BASIS : thm := BPowerBasis02.ALGEBRA_TRACE_PRODUCT_BASIS

/-- `needs "ANT/power_basis.ml"`: already done by importing this module. -/
def ensurePowerBasis : IO Unit := pure ()

end SessionANT.PowerBasis
