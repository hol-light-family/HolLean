/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/cyclotomic_field.ml                           . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/CyclotomicField.lean

  The session half of the cyclotomic_field.ml translation: it supplies HolANT.CyclotomicField's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/cyclotomic_field.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.CyclotomicField
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
import SessionANT.Integral
import SessionLibrary.Isum
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.PrimeSplit
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.RelativeDegree
import SessionANT.NfValuation
import SessionANT.Integrality
import SessionANT.DedekindKummer
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionLibrary.Integer
import SessionLibrary.Multiplicative
import SessionLibrary.Primitive
import SessionANT.CyclotomicPoly
import SessionANT.PowerBasis

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.CyclotomicField

/-- The core theorems cyclotomic_field.ml uses. -/
def core1 : HolANT.CyclotomicField.CoreThms1 where
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_SUBSET := Session.CARD_SUBSET
  COEFF_IN_CARRIER := SessionLibrary.RingTheory.«COEFF_IN_CARRIER»
  COEFF_POLY_LMUL := SessionLibrary.RingTheory.«COEFF_POLY_LMUL»
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  COPRIME_0 := SessionLibrary.Prime.«COPRIME_0»
  COPRIME_LMUL := SessionLibrary.Prime.«COPRIME_LMUL»
  CYCLOTOMIC_POLY_DEG := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_DEG»
  CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE»
  CYCLOTOMIC_POLY_IN_CARRIER := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_IN_CARRIER»
  CYCLOTOMIC_POLY_MONIC := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_MONIC»
  CYCLOTOMIC_POLY_ROOT := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_ROOT»
  CYCLOTOMIC_POLY_ROOT_EQ := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_ROOT_EQ»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  EQ_IMP_LE := Session.EQ_IMP_LE
  EXTENSION_DEGREE_SIMPLE := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_SIMPLE»
  FIELD_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FIELD_POLY_DEG_EQ_0 := SessionLibrary.RingTheory.«FIELD_POLY_DEG_EQ_0»
  FIELD_REAL_RING := SessionLibrary.RingTheory.«FIELD_REAL_RING»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_FIELD_EXTENSION»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_SIMPLE_ALGEBRAIC_EXTENSION := SessionLibrary.FieldTheory.«FINITE_SIMPLE_ALGEBRAIC_EXTENSION»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FUN_EQ_THM := Session.FUN_EQ_THM
  IMP_CONJ := Session.IMP_CONJ
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_RING_POLYNOMIAL_CARRIER_COMPOSE := SessionLibrary.RingTheory.«IN_RING_POLYNOMIAL_CARRIER_COMPOSE»
  I_O_ID := Session.I_O_ID
  KRONECKER_SIMPLE_FIELD_EXTENSION := SessionLibrary.FieldTheory.«KRONECKER_SIMPLE_FIELD_EXTENSION»
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_0 := Session.LE_0
  LE_TRANS := Session.LE_TRANS
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MINIMAL_POLYNOMIAL_DEG_LE := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_DEG_LE»
  MINIMAL_POLYNOMIAL_DIVIDES := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_DIVIDES»
  MINIMAL_POLYNOMIAL_MONIC := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_MONIC»
  MONIC_DIVIDES_EQ := SessionLibrary.RingTheory.«MONIC_DIVIDES_EQ»
  MONIC_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«MONIC_HOMOMORPHIC_IMAGE»
  MONIC_IMP_NONZERO := SessionLibrary.RingTheory.«MONIC_IMP_NONZERO»
  MONO_OR := Session.MONO_OR
  MULT_SYM := Session.MULT_SYM
  NOT_LT := Session.NOT_LT
  NUMBER_FIELD_ALGEBRAIC := SessionANT.Numfield.«NUMBER_FIELD_ALGEBRAIC»
  NUMBER_FIELD_FREE_BASIS_POWERS := SessionANT.PowerBasis.«NUMBER_FIELD_FREE_BASIS_POWERS»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q := SessionANT.PrimeSplit.«NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q»
  NUMBER_FIELD_PRIME_SUBFIELD := SessionANT.Numfield.«NUMBER_FIELD_PRIME_SUBFIELD»
  PHI_0 := SessionLibrary.Pocklington.«PHI_0»
  PHI_ALT := SessionLibrary.Pocklington.«PHI_ALT»
  PHI_EQ_0 := SessionLibrary.Pocklington.«PHI_EQ_0»
  POLY_COMPOSE_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_MUL»
  POLY_CONST_1 := SessionLibrary.RingTheory.«POLY_CONST_1»
  POLY_DEG_0 := SessionLibrary.RingTheory.«POLY_DEG_0»
  POLY_DEG_EQ_0 := SessionLibrary.RingTheory.«POLY_DEG_EQ_0»
  POLY_DEG_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_DEG_MONOMORPHIC_IMAGE»
  POLY_DEG_MUL := SessionLibrary.RingTheory.«POLY_DEG_MUL»
  POLY_DEG_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«POLY_DEG_SUBFIELD_GENERATED»
  POLY_DEG_UNIT := SessionLibrary.RingTheory.«POLY_DEG_UNIT»
  POLY_DERIV_1 := SessionLibrary.RingTheory.«POLY_DERIV_1»
  POLY_DERIV_SUB := SessionLibrary.RingTheory.«POLY_DERIV_SUB»
  POLY_DERIV_VAR_POW := SessionLibrary.RingTheory.«POLY_DERIV_VAR_POW»
  POLY_DIVIDES_X_MINUS_ROOT := SessionLibrary.RingTheory.«POLY_DIVIDES_X_MINUS_ROOT»
  POLY_DIV_REM := SessionLibrary.RingTheory.«POLY_DIV_REM»
  POLY_EQ_0_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_EQ_0_MONOMORPHIC_IMAGE»
  POLY_EVAL := SessionLibrary.RingTheory.«POLY_EVAL»
  POLY_EVAL_0 := SessionLibrary.RingTheory.«POLY_EVAL_0»
  POLY_EVAL_1 := SessionLibrary.RingTheory.«POLY_EVAL_1»
  POLY_EVAL_CONST := SessionLibrary.RingTheory.«POLY_EVAL_CONST»
  POLY_EVAL_MUL := SessionLibrary.RingTheory.«POLY_EVAL_MUL»
  POLY_EVAL_POW := SessionLibrary.RingTheory.«POLY_EVAL_POW»
  POLY_EVAL_SUB := SessionLibrary.RingTheory.«POLY_EVAL_SUB»
  POLY_EVAL_VAR := SessionLibrary.RingTheory.«POLY_EVAL_VAR»
  POLY_EXTEND := SessionLibrary.RingTheory.«POLY_EXTEND»
  POLY_EXTEND_CONST := SessionLibrary.RingTheory.«POLY_EXTEND_CONST»
  POLY_EXTEND_EVALUATE := SessionLibrary.RingTheory.«POLY_EXTEND_EVALUATE»
  POLY_EXTEND_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_EXTEND_HOMOMORPHIC_IMAGE»
  POLY_EXTEND_RING_OF_INTEGERS := SessionANT.DedekindKummer.«POLY_EXTEND_RING_OF_INTEGERS»
  POLY_EXTEND_SUB := SessionLibrary.RingTheory.«POLY_EXTEND_SUB»
  POLY_EXTEND_VARPOW := SessionLibrary.RingTheory.«POLY_EXTEND_VARPOW»
  POLY_MUL_0 := SessionLibrary.RingTheory.«POLY_MUL_0»
  POLY_MUL_SYM := SessionLibrary.RingTheory.«POLY_MUL_SYM»
  POLY_RING_CLAUSES := SessionLibrary.RingTheory.«POLY_RING_CLAUSES»
  POLY_ROOT_BOUND := SessionLibrary.RingTheory.«POLY_ROOT_BOUND»
  POLY_VAR_POW_SUB_1_HOMOMORPHIC_IMAGE := SessionANT.CyclotomicPoly.«POLY_VAR_POW_SUB_1_HOMOMORPHIC_IMAGE»
  PRIME_COPRIME_EQ := SessionLibrary.Prime.«PRIME_COPRIME_EQ»
  PRIME_FACTOR_INDUCT := SessionLibrary.Prime.«PRIME_FACTOR_INDUCT»
/-- The core theorems cyclotomic_field.ml uses. -/
def core2 : HolANT.CyclotomicField.CoreThms2 where
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRIME_SUBFIELD_MONOMORPHIC_IMAGE := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_MONOMORPHIC_IMAGE»
  PRIME_SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_SUBFIELD_GENERATED»
  PRIME_SUBFIELD_TOWER_LAW := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_TOWER_LAW»
  REAL_RING_CHAR := SessionLibrary.RingTheory.«REAL_RING_CHAR»
  REPEATED_ROOT_POLY_DERIV_ZERO := SessionLibrary.RingTheory.«REPEATED_ROOT_POLY_DERIV_ZERO»
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_CHAR_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_CHAR_SUBFIELD_GENERATED»
  RING_DIVIDES_IN_CARRIER := SessionLibrary.RingTheory.«RING_DIVIDES_IN_CARRIER»
  RING_DIVIDES_MUL2 := SessionLibrary.RingTheory.«RING_DIVIDES_MUL2»
  RING_ENDOMORPHISM_FROBENIUS := SessionLibrary.RingTheory.«RING_ENDOMORPHISM_FROBENIUS»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_INTO_SUBRING := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTO_SUBRING»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_POLY_EXTEND := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_EXTEND»
  RING_HOMOMORPHISM_POLY_RINGS := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_RINGS»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_MONOMORPHISM_I := SessionLibrary.RingTheory.«RING_MONOMORPHISM_I»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INTEGER_RING_OF_INT»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_CARRIER := SessionANT.Numfield.«RING_OF_INTEGERS_CARRIER»
  RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL := SessionANT.DedekindKummer.«RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL»
  RING_OF_INT_1 := SessionLibrary.RingTheory.«RING_OF_INT_1»
  RING_OF_INT_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_SUBFIELD_GENERATED»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_0 := SessionLibrary.RingTheory.«RING_OF_NUM_0»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_OF_NUM_IN_PRIME_IDEAL := SessionANT.PrimeSplit.«RING_OF_NUM_IN_PRIME_IDEAL»
  RING_ORDER_EQ_1 := SessionLibrary.RingTheory.«RING_ORDER_EQ_1»
  RING_POLYNOMIAL := SessionLibrary.RingTheory.«RING_POLYNOMIAL»
  RING_POLYNOMIAL_0 := SessionLibrary.RingTheory.«RING_POLYNOMIAL_0»
  RING_POLYNOMIAL_1 := SessionLibrary.RingTheory.«RING_POLYNOMIAL_1»
  RING_POLYNOMIAL_CONST := SessionLibrary.RingTheory.«RING_POLYNOMIAL_CONST»
  RING_POLYNOMIAL_IMP_POWERSERIES := SessionLibrary.RingTheory.«RING_POLYNOMIAL_IMP_POWERSERIES»
  RING_POLYNOMIAL_MUL := SessionLibrary.RingTheory.«RING_POLYNOMIAL_MUL»
  RING_POLYNOMIAL_POW := SessionLibrary.RingTheory.«RING_POLYNOMIAL_POW»
  RING_POLYNOMIAL_SUB := SessionLibrary.RingTheory.«RING_POLYNOMIAL_SUB»
  RING_POLYNOMIAL_VAR := SessionLibrary.RingTheory.«RING_POLYNOMIAL_VAR»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POWERSERIES_1 := SessionLibrary.RingTheory.«RING_POWERSERIES_1»
  RING_POWERSERIES_POW := SessionLibrary.RingTheory.«RING_POWERSERIES_POW»
  RING_POWERSERIES_VAR := SessionLibrary.RingTheory.«RING_POWERSERIES_VAR»
  RING_POW_1 := SessionLibrary.RingTheory.«RING_POW_1»
  RING_POW_2 := SessionLibrary.RingTheory.«RING_POW_2»
  RING_POW_EQ_LT_EQ := SessionLibrary.RingTheory.«RING_POW_EQ_LT_EQ»
  RING_POW_ONE := SessionLibrary.RingTheory.«RING_POW_ONE»
  RING_POW_POW := SessionLibrary.RingTheory.«RING_POW_POW»
  RING_POW_RING_ORDER := SessionLibrary.RingTheory.«RING_POW_RING_ORDER»
  RING_POW_ZERO := SessionLibrary.RingTheory.«RING_POW_ZERO»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_SUB_RZERO := SessionLibrary.RingTheory.«RING_SUB_RZERO»
  RING_UNIT_1 := SessionLibrary.RingTheory.«RING_UNIT_1»
  RING_UNIT_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_UNIT_HOMOMORPHIC_IMAGE»
  RING_UNIT_POLY_CONST := SessionLibrary.RingTheory.«RING_UNIT_POLY_CONST»
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_SING_ALGEBRAIC := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_SING_ALGEBRAIC»
  SUBRING_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBRING_GENERATED_BY_SUBFIELD_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_REFL := Session.SUBSET_REFL
  SUC_SUB1 := Session.SUC_SUB1
  TRIVIAL_RING_10 := SessionLibrary.RingTheory.«TRIVIAL_RING_10»
  algebraic_over := SessionLibrary.FieldTheory.«algebraic_over»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  integral_element := SessionANT.Integral.«integral_element»
  monic := SessionLibrary.RingTheory.«monic»
  num_CASES := Session.num_CASES
  number_field := SessionANT.Numfield.«number_field»
  o_THM := Session.o_THM
  poly_0 := SessionLibrary.RingTheory.«poly_0»
  poly_const := SessionLibrary.RingTheory.«poly_const»
  poly_eval := SessionLibrary.RingTheory.«poly_eval»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_endomorphism := SessionLibrary.RingTheory.«ring_endomorphism»
  ring_irreducible := SessionLibrary.RingTheory.«ring_irreducible»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_unit := SessionLibrary.RingTheory.«ring_unit»

/-- What cyclotomic_field.ml uses from Session. -/
def deps : HolANT.CyclotomicField.CyclotomicFieldDeps where
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

/- The bundles, in cyclotomic_field.ml order. -/
initialize BCyclotomicField01 : HolANT.CyclotomicField.CyclotomicField01 ←
  ioB "setupCyclotomicField01" (HolANT.CyclotomicField.setupCyclotomicField01 deps).run
initialize BCyclotomicField02 : HolANT.CyclotomicField.CyclotomicField02 ←
  ioB "setupCyclotomicField02" (HolANT.CyclotomicField.setupCyclotomicField02 deps BCyclotomicField01).run

-- CyclotomicField01
def NUMBER_FIELD_FINITE_EXTENSION : thm := BCyclotomicField01.NUMBER_FIELD_FINITE_EXTENSION
def POLY_EXTEND_INTEGER_RING_HOMOMORPHIC_IMAGE : thm := BCyclotomicField01.POLY_EXTEND_INTEGER_RING_HOMOMORPHIC_IMAGE
def POLY_EXTEND_INTEGER_RING_VAR_POW_SUB_1 : thm := BCyclotomicField01.POLY_EXTEND_INTEGER_RING_VAR_POW_SUB_1
def RING_UNIT_POLY_DIVIDES_MONIC : thm := BCyclotomicField01.RING_UNIT_POLY_DIVIDES_MONIC
def POLY_VAR_POW_SUB_1_COMMON_ROOT : thm := BCyclotomicField01.POLY_VAR_POW_SUB_1_COMMON_ROOT
def POLY_VAR_POW_SUB_1_FROBENIUS_ROOT : thm := BCyclotomicField01.POLY_VAR_POW_SUB_1_FROBENIUS_ROOT
def NUMBER_FIELD_VAR_POW_SUB_1_FROBENIUS_ROOT : thm := BCyclotomicField01.NUMBER_FIELD_VAR_POW_SUB_1_FROBENIUS_ROOT
def NUMBER_FIELD_VAR_POW_SUB_1_DIVISOR_ROOT_POW : thm := BCyclotomicField01.NUMBER_FIELD_VAR_POW_SUB_1_DIVISOR_ROOT_POW
def NUMBER_FIELD_VAR_POW_SUB_1_DIVISOR_DEG : thm := BCyclotomicField01.NUMBER_FIELD_VAR_POW_SUB_1_DIVISOR_DEG
def NUMBER_FIELD_INTEGER_MINIMAL_POLYNOMIAL_DIVIDES : thm := BCyclotomicField01.NUMBER_FIELD_INTEGER_MINIMAL_POLYNOMIAL_DIVIDES
def CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL : thm := BCyclotomicField01.CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL
def PHI_LE_POLY_DEG_PRIMITIVE_ROOT : thm := BCyclotomicField01.PHI_LE_POLY_DEG_PRIMITIVE_ROOT
def PHI_LE_POLY_DEG_CYCLOTOMIC_DIVISOR_ROOT : thm := BCyclotomicField01.PHI_LE_POLY_DEG_CYCLOTOMIC_DIVISOR_ROOT
def PHI_LE_POLY_DEG_CYCLOTOMIC_DIVISOR : thm := BCyclotomicField01.PHI_LE_POLY_DEG_CYCLOTOMIC_DIVISOR
def CYCLOTOMIC_POLY_IRREDUCIBLE_PRIME_SUBFIELD : thm := BCyclotomicField01.CYCLOTOMIC_POLY_IRREDUCIBLE_PRIME_SUBFIELD

-- CyclotomicField02
def CYCLOTOMIC_POLY_IRREDUCIBLE : thm := BCyclotomicField02.CYCLOTOMIC_POLY_IRREDUCIBLE
def CYCLOTOMIC_FIELD_DEGREE : thm := BCyclotomicField02.CYCLOTOMIC_FIELD_DEGREE
def CYCLOTOMIC_FIELD_FREE_BASIS : thm := BCyclotomicField02.CYCLOTOMIC_FIELD_FREE_BASIS

/-- `needs "ANT/cyclotomic_field.ml"`: already done by importing this module. -/
def ensureCyclotomicField : IO Unit := pure ()

end SessionANT.CyclotomicField
