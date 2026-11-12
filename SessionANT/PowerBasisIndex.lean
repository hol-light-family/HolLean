/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/power_basis_index.ml                          . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/PowerBasisIndex.lean

  The session half of the power_basis_index.ml translation: it supplies HolANT.PowerBasisIndex's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/power_basis_index.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.PowerBasisIndex
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
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.NfValuation
import SessionANT.PrimeSplit
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.Integrality
import SessionANT.RelativeDegree
import SessionANT.DedekindKummer
import SessionANT.PowerBasis

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.PowerBasisIndex

/-- The core theorems power_basis_index.ml uses. -/
def core1 : HolANT.PowerBasisIndex.CoreThms1 where
  ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH := SessionLibrary.FieldTheory.«ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH»
  ALGEBRA_TRACE_NORM_IN_CARRIER := SessionLibrary.RingDet.«ALGEBRA_TRACE_NORM_IN_CARRIER»
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  COEFF_ABOVE_DEG := SessionLibrary.RingTheory.«COEFF_ABOVE_DEG»
  COEFF_COMPOSE := SessionLibrary.RingTheory.«COEFF_COMPOSE»
  COEFF_IN_CARRIER_ALT := SessionLibrary.RingTheory.«COEFF_IN_CARRIER_ALT»
  COEFF_POLY_DERIV := SessionLibrary.RingTheory.«COEFF_POLY_DERIV»
  COEFF_POLY_MUL_X_MINUS := SessionLibrary.RingTheory.«COEFF_POLY_MUL_X_MINUS»
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSION := Session.EXTENSION
  EXTENSIONAL_EQ := Session.EXTENSIONAL_EQ
  EXTENSION_DEGREE_SIMPLE := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_SIMPLE»
  FIELD_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED»
  FIELD_HOMOMORPHISM_INV := SessionLibrary.RingTheory.«FIELD_HOMOMORPHISM_INV»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_MUL_LINV := SessionLibrary.RingTheory.«FIELD_MUL_LINV»
  FIELD_RING_HOMOMORPHISM_MONOMORPHISM := SessionLibrary.RingTheory.«FIELD_RING_HOMOMORPHISM_MONOMORPHISM»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FREE_BASIS_FIELD := SessionLibrary.FieldTheory.«FREE_BASIS_FIELD»
  FREE_BASIS_IN_CARRIER := SessionLibrary.RingDet.«FREE_BASIS_IN_CARRIER»
  FUN_EQ_THM := Session.FUN_EQ_THM
  HAS_SIZE_0 := Session.HAS_SIZE_0
  HAS_SIZE_CLAUSES := Session.HAS_SIZE_CLAUSES
  HAS_SIZE_INDEX := Session.HAS_SIZE_INDEX
  IMAGE_I := Session.IMAGE_I
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGRAL_DOMAIN_MUL_LCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_LCANCEL»
  INTEGRAL_DOMAIN_POLY_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_POLY_RING»
  INTEGRAL_DOMAIN_PRODUCT_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_PRODUCT_EQ_0»
  INT_ABS_MUL := Session.INT_ABS_MUL
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_ABS_POS := Session.INT_ABS_POS
  INT_ABS_POW := Session.INT_ABS_POW
  INT_MUL_LID := Session.INT_MUL_LID
  INT_OF_NUM_POW := Session.INT_OF_NUM_POW
  INT_POS := Session.INT_POS
  INT_POW_ONE := Session.INT_POW_ONE
  IN_DELETE := Session.IN_DELETE
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_SING := Session.IN_SING
  IN_SUBFIELD_0 := SessionLibrary.FieldTheory.«IN_SUBFIELD_0»
  IN_SUBFIELD_INV := SessionLibrary.FieldTheory.«IN_SUBFIELD_INV»
  IN_SUBFIELD_MUL := SessionLibrary.FieldTheory.«IN_SUBFIELD_MUL»
  IN_SUBRING_1 := SessionLibrary.RingTheory.«IN_SUBRING_1»
  IN_SUBRING_ADD := SessionLibrary.RingTheory.«IN_SUBRING_ADD»
  IN_SUBRING_INT := SessionLibrary.RingTheory.«IN_SUBRING_INT»
  IN_SUBRING_MUL := SessionLibrary.RingTheory.«IN_SUBRING_MUL»
  IN_SUBRING_NUM := SessionLibrary.RingTheory.«IN_SUBRING_NUM»
  IN_SUBRING_POW := SessionLibrary.RingTheory.«IN_SUBRING_POW»
  IN_SUBRING_SUM := SessionLibrary.RingTheory.«IN_SUBRING_SUM»
  IN_UNIV := Session.IN_UNIV
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LE_REFL := Session.LE_REFL
  MINIMAL_POLYNOMIAL_DIVIDES := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_DIVIDES»
  MINIMAL_POLYNOMIAL_IN_CARRIER := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_IN_CARRIER»
  MINIMAL_POLYNOMIAL_MONIC := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_MONIC»
  MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE»
  MONIC_DIVIDES_EQ := SessionLibrary.RingTheory.«MONIC_DIVIDES_EQ»
  MONIC_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«MONIC_HOMOMORPHIC_IMAGE»
  MONIC_IMP_NONZERO := SessionLibrary.RingTheory.«MONIC_IMP_NONZERO»
  MONIC_POLY_0 := SessionLibrary.RingTheory.«MONIC_POLY_0»
  MONIC_POLY_EQ_ROOTS_PRODUCT := SessionLibrary.RingTheory.«MONIC_POLY_EQ_ROOTS_PRODUCT»
  MONIC_X_MINUS_A := SessionLibrary.RingTheory.«MONIC_X_MINUS_A»
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NUMBER_FIELD_ALGEBRAIC := SessionANT.Numfield.«NUMBER_FIELD_ALGEBRAIC»
  NUMBER_FIELD_DEGREE_POS := SessionANT.Numfield.«NUMBER_FIELD_DEGREE_POS»
  NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS := SessionANT.PowerBasis.«NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS»
  NUMBER_FIELD_DISCRIMINANT_INDEX := SessionANT.Discriminant.«NUMBER_FIELD_DISCRIMINANT_INDEX»
  NUMBER_FIELD_FREE_BASIS_POWERS := SessionANT.PowerBasis.«NUMBER_FIELD_FREE_BASIS_POWERS»
  NUMBER_FIELD_HOMOMORPHISMS_HAS_SIZE := SessionANT.PowerBasis.«NUMBER_FIELD_HOMOMORPHISMS_HAS_SIZE»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_INTEGRAL_MULTIPLE := SessionANT.Numfield.«NUMBER_FIELD_INTEGRAL_MULTIPLE»
  NUMBER_FIELD_TRACE_FORM_INJECTIVE := SessionANT.Numfield.«NUMBER_FIELD_TRACE_FORM_INJECTIVE»
  NUMBER_FIELD_TRACE_HOMOMORPHISMS := SessionANT.PowerBasis.«NUMBER_FIELD_TRACE_HOMOMORPHISMS»
  NUMBER_FIELD_TRACE_IN_RING_OF_INTEGERS := SessionANT.Numfield.«NUMBER_FIELD_TRACE_IN_RING_OF_INTEGERS»
  NUMBER_FIELD_TRACE_MUL_LINCOMB := SessionANT.Numfield.«NUMBER_FIELD_TRACE_MUL_LINCOMB»
  NUM_OF_INT_MUL := Session.NUM_OF_INT_MUL
  NUM_OF_INT_OF_NUM := Session.NUM_OF_INT_OF_NUM
  ONE := Session.ONE
  POLY_COMPOSE_HOMOMORPHISM_CONST := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_CONST»
  POLY_COMPOSE_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_MUL»
  POLY_COMPOSE_HOMOMORPHISM_SUB := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_SUB»
  POLY_COMPOSE_HOMOMORPHISM_VAR := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_VAR»
  POLY_CONST_1 := SessionLibrary.RingTheory.«POLY_CONST_1»
  POLY_DEG_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_DEG_MONOMORPHIC_IMAGE»
  POLY_DEG_MUL_X_MINUS_A := SessionLibrary.RingTheory.«POLY_DEG_MUL_X_MINUS_A»
  POLY_DERIV_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_DERIV_HOMOMORPHIC_IMAGE»
  POLY_DERIV_IN_CARRIER := SessionLibrary.RingTheory.«POLY_DERIV_IN_CARRIER»
  POLY_DISCRIMINANT_HOMOMORPHISM := SessionLibrary.RingDet.«POLY_DISCRIMINANT_HOMOMORPHISM»
  POLY_DISCRIMINANT_IN_CARRIER := SessionLibrary.RingDet.«POLY_DISCRIMINANT_IN_CARRIER»
  POLY_DISCRIMINANT_VANDERMONDE := SessionLibrary.RingDet.«POLY_DISCRIMINANT_VANDERMONDE»
  POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS := SessionLibrary.RingDet.«POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS»
  POLY_EXTEND := SessionLibrary.RingTheory.«POLY_EXTEND»
  POLY_EXTEND_EVALUATE := SessionLibrary.RingTheory.«POLY_EXTEND_EVALUATE»
  POLY_EXTEND_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_EXTEND_HOMOMORPHIC_IMAGE»
  POLY_EXTEND_UNIVARIATE := SessionLibrary.RingTheory.«POLY_EXTEND_UNIVARIATE»
  POLY_MUL_0 := SessionLibrary.RingTheory.«POLY_MUL_0»
  POLY_RING := SessionLibrary.RingTheory.«POLY_RING»
/-- The core theorems power_basis_index.ml uses. -/
def core2 : HolANT.PowerBasisIndex.CoreThms2 where
  POLY_RING_CLAUSES := SessionLibrary.RingTheory.«POLY_RING_CLAUSES»
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_CARRIER_SUBFIELD_GENERATED_SUBSET := SessionLibrary.FieldTheory.«RING_CARRIER_SUBFIELD_GENERATED_SUBSET»
  RING_CHAR_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_CHAR_MONOMORPHIC_IMAGE»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_DET := SessionLibrary.RingDet.«RING_DET»
  RING_DET_EQ := SessionLibrary.RingDet.«RING_DET_EQ»
  RING_HOMOMORPHISMS_EQ_FROM_RING_SPAN := SessionLibrary.FieldTheory.«RING_HOMOMORPHISMS_EQ_FROM_RING_SPAN»
  RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_FROM_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_FROM_SUBRING_GENERATED»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_INT_LINCOMB := SessionANT.Numfield.«RING_INT_LINCOMB»
  RING_INT_LINCOMB_LINCOMB := SessionANT.Numfield.«RING_INT_LINCOMB_LINCOMB»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_INT_LINCOMB := SessionANT.Numfield.«RING_MUL_INT_LINCOMB»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_CARRIER := SessionANT.Numfield.«RING_OF_INTEGERS_CARRIER»
  RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL := SessionANT.DedekindKummer.«RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL»
  RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q := SessionANT.Integrality.«RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_0 := SessionLibrary.RingTheory.«RING_OF_INT_0»
  RING_OF_INT_1 := SessionLibrary.RingTheory.«RING_OF_INT_1»
  RING_OF_INT_EQ_0_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0_CHAR_0»
  RING_OF_INT_EQ_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_CHAR_0»
  RING_OF_INT_IN_RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INT_IN_RING_OF_INTEGERS»
  RING_OF_INT_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_IN_SUBFIELD_GENERATED»
  RING_OF_INT_ISUM := SessionLibrary.RingTheory.«RING_OF_INT_ISUM»
  RING_OF_INT_MUL := SessionLibrary.RingTheory.«RING_OF_INT_MUL»
  RING_OF_INT_NEG := SessionLibrary.RingTheory.«RING_OF_INT_NEG»
  RING_OF_INT_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_SUBFIELD_GENERATED»
  RING_OF_NUM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_NUM_SUBFIELD_GENERATED»
  RING_POLYNOMIAL := SessionLibrary.RingTheory.«RING_POLYNOMIAL»
  RING_POLYNOMIAL_COMPOSE := SessionLibrary.RingTheory.«RING_POLYNOMIAL_COMPOSE»
  RING_POLYNOMIAL_CONST := SessionLibrary.RingTheory.«RING_POLYNOMIAL_CONST»
  RING_POLYNOMIAL_IMP_POWERSERIES := SessionLibrary.RingTheory.«RING_POLYNOMIAL_IMP_POWERSERIES»
  RING_POLYNOMIAL_SUB := SessionLibrary.RingTheory.«RING_POLYNOMIAL_SUB»
  RING_POLYNOMIAL_VAR := SessionLibrary.RingTheory.«RING_POLYNOMIAL_VAR»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POWERSERIES_CONST := SessionLibrary.RingTheory.«RING_POWERSERIES_CONST»
  RING_POWERSERIES_VAR := SessionLibrary.RingTheory.«RING_POWERSERIES_VAR»
  RING_POW_ONE := SessionLibrary.RingTheory.«RING_POW_ONE»
  RING_PRODUCT := SessionLibrary.RingTheory.«RING_PRODUCT»
  RING_PRODUCT_DELETE := SessionLibrary.RingDet.«RING_PRODUCT_DELETE»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_RZERO := SessionLibrary.RingTheory.«RING_SUB_RZERO»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_DELTA := SessionLibrary.RingTheory.«RING_SUM_DELTA»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_IMAGE := SessionLibrary.RingTheory.«RING_SUM_IMAGE»
  RING_SUM_LAGRANGE_COEFF := SessionLibrary.RingTheory.«RING_SUM_LAGRANGE_COEFF»
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBFIELDS_GENERATED_EQ := SessionLibrary.FieldTheory.«SUBFIELDS_GENERATED_EQ»
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_EQ := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_EQ»
  SUBFIELD_GENERATED_INSERT := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_INSERT»
  SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC»
  SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_SUBFIELD_GENERATED»
  SUBRING_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBRING_GENERATED_BY_SUBFIELD_GENERATED»
  SUBRING_GENERATED_INC := SessionLibrary.RingTheory.«SUBRING_GENERATED_INC»
  SUBRING_GENERATED_INDEX_COPRIME := SessionANT.DedekindKummer.«SUBRING_GENERATED_INDEX_COPRIME»
  SUBRING_GENERATED_INT_LINCOMB := SessionANT.DedekindKummer.«SUBRING_GENERATED_INT_LINCOMB»
  SUBRING_GENERATED_MINIMAL := SessionLibrary.RingTheory.«SUBRING_GENERATED_MINIMAL»
  SUBRING_SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_SUBRING_GENERATED»
  SUBRING_SUBSET_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBRING_SUBSET_SUBFIELD_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_ANTISYM_EQ := Session.SUBSET_ANTISYM_EQ
  SUB_0 := Session.SUB_0
  UNWIND_THM2 := Session.UNWIND_THM2
  algebraic_extension := SessionLibrary.FieldTheory.«algebraic_extension»
  basis_discriminant := SessionLibrary.RingDet.«basis_discriminant»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  integral_element := SessionANT.Integral.«integral_element»
  monic := SessionLibrary.RingTheory.«monic»
  num_divides := Session.num_divides
  number_field := SessionANT.Numfield.«number_field»
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM
  poly_eval := SessionLibrary.RingTheory.«poly_eval»
  ring_basis := SessionLibrary.FieldTheory.«ring_basis»
  ring_div := SessionLibrary.RingTheory.«ring_div»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  ring_polynomial := SessionLibrary.RingTheory.«ring_polynomial»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_powerseries := SessionLibrary.RingTheory.«ring_powerseries»
  ring_spanning := SessionLibrary.FieldTheory.«ring_spanning»
  squarefree := SessionLibrary.Pocklington.«squarefree»
  subring_of := SessionLibrary.RingTheory.«subring_of»

/-- What power_basis_index.ml uses from Session. -/
def deps : HolANT.PowerBasisIndex.PowerBasisIndexDeps where
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
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in power_basis_index.ml order. -/
initialize BPowerBasisIndex01 : HolANT.PowerBasisIndex.PowerBasisIndex01 ←
  ioB "setupPowerBasisIndex01" (HolANT.PowerBasisIndex.setupPowerBasisIndex01 deps).run
initialize BPowerBasisIndex02 : HolANT.PowerBasisIndex.PowerBasisIndex02 ←
  ioB "setupPowerBasisIndex02" (HolANT.PowerBasisIndex.setupPowerBasisIndex02 deps BPowerBasisIndex01).run

-- PowerBasisIndex01
def NUMBER_FIELD_POWER_BASIS_HOMOMORPHISMS : thm := BPowerBasisIndex01.NUMBER_FIELD_POWER_BASIS_HOMOMORPHISMS
def NUMBER_FIELD_POWER_BASIS_POLY_DISCRIMINANT : thm := BPowerBasisIndex01.NUMBER_FIELD_POWER_BASIS_POLY_DISCRIMINANT
def NUMBER_FIELD_GENERATOR_MINIMAL_POLYNOMIAL_DEGREE : thm := BPowerBasisIndex01.NUMBER_FIELD_GENERATOR_MINIMAL_POLYNOMIAL_DEGREE
def NUMBER_FIELD_POLY_DISCRIMINANT_INDEX : thm := BPowerBasisIndex01.NUMBER_FIELD_POLY_DISCRIMINANT_INDEX
def NUMBER_FIELD_POLY_DISCRIMINANT_INDEX_INTEGER : thm := BPowerBasisIndex01.NUMBER_FIELD_POLY_DISCRIMINANT_INDEX_INTEGER
def NUMBER_FIELD_POLY_DISCRIMINANT_SQUAREFREE : thm := BPowerBasisIndex01.NUMBER_FIELD_POLY_DISCRIMINANT_SQUAREFREE
def NUMBER_FIELD_POLY_DISCRIMINANT_INDEX_COPRIME : thm := BPowerBasisIndex01.NUMBER_FIELD_POLY_DISCRIMINANT_INDEX_COPRIME

-- PowerBasisIndex02
def NUMBER_FIELD_POWER_BASIS_DUAL : thm := BPowerBasisIndex02.NUMBER_FIELD_POWER_BASIS_DUAL
def NUMBER_FIELD_TRACE_DUAL_LATTICE : thm := BPowerBasisIndex02.NUMBER_FIELD_TRACE_DUAL_LATTICE
def SUBRING_GENERATED_HORNER_SPAN : thm := BPowerBasisIndex02.SUBRING_GENERATED_HORNER_SPAN
def NUMBER_FIELD_MINIMAL_POLYNOMIAL_DERIV_SUBRING : thm := BPowerBasisIndex02.NUMBER_FIELD_MINIMAL_POLYNOMIAL_DERIV_SUBRING
def NUMBER_FIELD_SUBRING_GENERATED_EQ_RING_OF_INTEGERS : thm := BPowerBasisIndex02.NUMBER_FIELD_SUBRING_GENERATED_EQ_RING_OF_INTEGERS

/-- `needs "ANT/power_basis_index.ml"`: already done by importing this module. -/
def ensurePowerBasisIndex : IO Unit := pure ()

end SessionANT.PowerBasisIndex
