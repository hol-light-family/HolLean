/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/quadratic.ml                                  . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/Quadratic.lean

  The session half of the quadratic.ml translation: it supplies HolANT.Quadratic's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/quadratic.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.Quadratic
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
import SessionANT.NormIndex
import SessionANT.Discriminant

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.Quadratic

/-- The core theorems quadratic.ml uses. -/
def core1 : HolANT.Quadratic.CoreThms1 where
  ALGEBRAIC_OVER_IMAGE := SessionLibrary.FieldTheory.«ALGEBRAIC_OVER_IMAGE»
  ALGEBRAIC_OVER_POW_EQ := SessionLibrary.FieldTheory.«ALGEBRAIC_OVER_POW_EQ»
  ALGEBRA_TRACE_ADD := SessionLibrary.RingDet.«ALGEBRA_TRACE_ADD»
  ALGEBRA_TRACE_FREE_BASIS := SessionLibrary.RingDet.«ALGEBRA_TRACE_FREE_BASIS»
  ALGEBRA_TRACE_NORM_BASE_FREE_BASIS := SessionLibrary.RingDet.«ALGEBRA_TRACE_NORM_BASE_FREE_BASIS»
  ALGEBRA_TRACE_NORM_IN_CARRIER := SessionLibrary.RingDet.«ALGEBRA_TRACE_NORM_IN_CARRIER»
  ALGEBRA_TRACE_SCALAR := SessionLibrary.RingDet.«ALGEBRA_TRACE_SCALAR»
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  BASIS_COORDINATES_BASIS := SessionLibrary.RingDet.«BASIS_COORDINATES_BASIS»
  BASIS_COORDINATES_LMUL := SessionLibrary.RingDet.«BASIS_COORDINATES_LMUL»
  BASIS_DISCRIMINANT_CHANGE_OF_BASIS := SessionLibrary.RingDet.«BASIS_DISCRIMINANT_CHANGE_OF_BASIS»
  COEFF_POLY_CONST := SessionLibrary.RingTheory.«COEFF_POLY_CONST»
  COEFF_POLY_SUB := SessionLibrary.RingTheory.«COEFF_POLY_SUB»
  COEFF_POLY_VARPOW := SessionLibrary.RingTheory.«COEFF_POLY_VARPOW»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  EQ_SYM_EQ := Session.EQ_SYM_EQ
  EXISTS_OR_THM := Session.EXISTS_OR_THM
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSION := Session.EXTENSION
  EXTENSION_DEGREE_EQ_TOWER := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_EQ_TOWER»
  FIELD_EXTENSION_IMP_HOMOMORPHISM := SessionLibrary.FieldTheory.«FIELD_EXTENSION_IMP_HOMOMORPHISM»
  FIELD_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_MUL_LINV := SessionLibrary.RingTheory.«FIELD_MUL_LINV»
  FIELD_MUL_RINV := SessionLibrary.RingTheory.«FIELD_MUL_RINV»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FIELD_REAL_RING := SessionLibrary.RingTheory.«FIELD_REAL_RING»
  FIELD_RING_HOMOMORPHISM_MONOMORPHISM := SessionLibrary.RingTheory.«FIELD_RING_HOMOMORPHISM_MONOMORPHISM»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_FIELD_EXTENSION»
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FORALL_LT_2 := SessionANT.Algmisc.«FORALL_LT_2»
  FREE_BASIS_FIELD := SessionLibrary.FieldTheory.«FREE_BASIS_FIELD»
  FREE_BASIS_INTEGER_RING_SUBRING_GENERATED := SessionANT.RingOfIntegers.«FREE_BASIS_INTEGER_RING_SUBRING_GENERATED»
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  IMAGE_EQ := Session.IMAGE_EQ
  IMAGE_I := Session.IMAGE_I
  IMP_CONJ := Session.IMP_CONJ
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_MUL_LCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_LCANCEL»
  INTEGRAL_DOMAIN_POW_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_POW_EQ_0»
  INTEGRAL_DOMAIN_SQUARE_EQ := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_SQUARE_EQ»
  INTEGRAL_ELEMENT_FROM_RELATION := SessionANT.Integral.«INTEGRAL_ELEMENT_FROM_RELATION»
  INTEGRAL_ELEMENT_PRIME_SUBFIELD := SessionANT.Integral.«INTEGRAL_ELEMENT_PRIME_SUBFIELD»
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_ABS_POS := Session.INT_ABS_POS
  INT_ABS_POW := Session.INT_ABS_POW
  INT_DIVIDES_NUM_OF_INT_ABS := SessionANT.Algmisc.«INT_DIVIDES_NUM_OF_INT_ABS»
  INT_DIVISION := Session.INT_DIVISION
  INT_ENTIRE := Session.INT_ENTIRE
  INT_EQ_MUL_LCANCEL := Session.INT_EQ_MUL_LCANCEL
  INT_LE_POW_2 := Session.INT_LE_POW_2
  INT_LE_RMUL := Session.INT_LE_RMUL
  INT_MUL_LID := Session.INT_MUL_LID
  INT_NOT_LT := Session.INT_NOT_LT
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_POW2_ABS := Session.INT_POW2_ABS
  INT_POW_LE2 := Session.INT_POW_LE2
  INT_POW_ONE := Session.INT_POW_ONE
  INT_REM_EQ := Session.INT_REM_EQ
  INT_REM_EQ_0 := Session.INT_REM_EQ_0
  INT_SQUAREFREE_DECOMPOSITION := SessionLibrary.Pocklington.«INT_SQUAREFREE_DECOMPOSITION»
  INT_SQUAREFREE_DIVPOW := SessionLibrary.Pocklington.«INT_SQUAREFREE_DIVPOW»
  INT_SQUAREFREE_MUL_SQUARE := SessionLibrary.Pocklington.«INT_SQUAREFREE_MUL_SQUARE»
  INT_SUB_0 := Session.INT_SUB_0
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_INTER := Session.IN_INTER
  IN_SING := Session.IN_SING
  IN_SUBRING_MUL := SessionLibrary.RingTheory.«IN_SUBRING_MUL»
  IN_SUBRING_POW := SessionLibrary.RingTheory.«IN_SUBRING_POW»
  IN_SUBRING_SUB := SessionLibrary.RingTheory.«IN_SUBRING_SUB»
  IN_UNION := Session.IN_UNION
  IN_UNIV := Session.IN_UNIV
  IRREDUCIBLE_IMP_POLY_DEG_NZ := SessionLibrary.RingTheory.«IRREDUCIBLE_IMP_POLY_DEG_NZ»
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  KRONECKER_SIMPLE_FIELD_EXTENSION := SessionLibrary.FieldTheory.«KRONECKER_SIMPLE_FIELD_EXTENSION»
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  MINIMAL_POLYNOMIAL_DEG_EQ_1 := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_DEG_EQ_1»
  MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE»
  MINIMAL_POLYNOMIAL_IRREDUCIBLE := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_IRREDUCIBLE»
  MINIMAL_POLYNOMIAL_UNIQUE := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_UNIQUE»
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NUMBER_FIELD_ALGEBRAIC := SessionANT.Numfield.«NUMBER_FIELD_ALGEBRAIC»
  NUMBER_FIELD_ALT := SessionANT.Numfield.«NUMBER_FIELD_ALT»
  NUMBER_FIELD_DEGREE_EQ_1 := SessionANT.Numfield.«NUMBER_FIELD_DEGREE_EQ_1»
  NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD := SessionANT.Discriminant.«NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD»
  NUMBER_FIELD_FREE_BASIS_DEGREE := SessionANT.Numfield.«NUMBER_FIELD_FREE_BASIS_DEGREE»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_TRACE_INTEGRAL_Q := SessionANT.Numfield.«NUMBER_FIELD_TRACE_INTEGRAL_Q»
  NUM_OF_INT_ABS_POW := SessionANT.Algmisc.«NUM_OF_INT_ABS_POW»
  NUM_OF_INT_OF_NUM := Session.NUM_OF_INT_OF_NUM
  POLY_DEG_2_IRREDUCIBLE := SessionLibrary.RingTheory.«POLY_DEG_2_IRREDUCIBLE»
  POLY_EVAL_VAR_POW_SUB_CONST := SessionLibrary.RingTheory.«POLY_EVAL_VAR_POW_SUB_CONST»
  POLY_EXTEND_CONST := SessionLibrary.RingTheory.«POLY_EXTEND_CONST»
  POLY_EXTEND_EVALUATE := SessionLibrary.RingTheory.«POLY_EXTEND_EVALUATE»
  POLY_EXTEND_SUB := SessionLibrary.RingTheory.«POLY_EXTEND_SUB»
  POLY_EXTEND_VARPOW := SessionLibrary.RingTheory.«POLY_EXTEND_VARPOW»
  POLY_RING_CLAUSES := SessionLibrary.RingTheory.«POLY_RING_CLAUSES»
  POLY_VAR_POW_SUB_CONST := SessionLibrary.RingTheory.«POLY_VAR_POW_SUB_CONST»
  PRIME_SUBFIELD_COMMON_DENOMINATOR := SessionANT.Numfield.«PRIME_SUBFIELD_COMMON_DENOMINATOR»
/-- The core theorems quadratic.ml uses. -/
def core2 : HolANT.Quadratic.CoreThms2 where
  PRIME_SUBFIELD_HOMOMORPHISM_EXISTS := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_HOMOMORPHISM_EXISTS»
  PRIME_SUBFIELD_MONOMORPHIC_IMAGE := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_MONOMORPHIC_IMAGE»
  PRIME_SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_SUBFIELD_GENERATED»
  REAL_RING_CHAR := SessionLibrary.RingTheory.«REAL_RING_CHAR»
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_OR_DISTRIB := Session.RIGHT_OR_DISTRIB
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_0_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_0_IN_SUBFIELD_GENERATED»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_1_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_1_IN_SUBFIELD_GENERATED»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_EQ_0 := SessionLibrary.RingTheory.«RING_ADD_EQ_0»
  RING_ADD_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_ADD_IN_SUBFIELD_GENERATED»
  RING_ADD_IN_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_ADD_IN_SUBRING_GENERATED»
  RING_ADD_LDISTRIB := SessionLibrary.RingTheory.«RING_ADD_LDISTRIB»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RNEG := SessionLibrary.RingTheory.«RING_ADD_RNEG»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_ADD_SYM := SessionLibrary.RingTheory.«RING_ADD_SYM»
  RING_CARRIER_SUBFIELD_GENERATED_SUBSET := SessionLibrary.FieldTheory.«RING_CARRIER_SUBFIELD_GENERATED_SUBSET»
  RING_CHAR_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_CHAR_MONOMORPHIC_IMAGE»
  RING_CHAR_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_CHAR_SUBFIELD_GENERATED»
  RING_DET_DIAGONAL := SessionLibrary.RingDet.«RING_DET_DIAGONAL»
  RING_DET_LOWERTRIANGULAR := SessionLibrary.RingDet.«RING_DET_LOWERTRIANGULAR»
  RING_DIV := SessionLibrary.RingTheory.«RING_DIV»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_I := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_I»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_INV_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_INV_IN_SUBFIELD_GENERATED»
  RING_ISOMORPHISM_MONOMORPHISM_ALT := SessionLibrary.RingTheory.«RING_ISOMORPHISM_MONOMORPHISM_ALT»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_MUL_IN_SUBFIELD_GENERATED»
  RING_MUL_IN_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_MUL_IN_SUBRING_GENERATED»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_NEG_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_NEG_IN_SUBFIELD_GENERATED»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_CARRIER := SessionANT.Numfield.«RING_OF_INTEGERS_CARRIER»
  RING_OF_INTEGERS_PRIME_SUBFIELD := SessionANT.Numfield.«RING_OF_INTEGERS_PRIME_SUBFIELD»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_0 := SessionLibrary.RingTheory.«RING_OF_INT_0»
  RING_OF_INT_1 := SessionLibrary.RingTheory.«RING_OF_INT_1»
  RING_OF_INT_ADD := SessionLibrary.RingTheory.«RING_OF_INT_ADD»
  RING_OF_INT_EQ_0_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0_CHAR_0»
  RING_OF_INT_EQ_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_CHAR_0»
  RING_OF_INT_IN_RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INT_IN_RING_OF_INTEGERS»
  RING_OF_INT_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_IN_SUBFIELD_GENERATED»
  RING_OF_INT_MUL := SessionLibrary.RingTheory.«RING_OF_INT_MUL»
  RING_OF_INT_NEG := SessionLibrary.RingTheory.«RING_OF_INT_NEG»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_INT_POW := SessionLibrary.RingTheory.«RING_OF_INT_POW»
  RING_OF_INT_SUB := SessionLibrary.RingTheory.«RING_OF_INT_SUB»
  RING_OF_INT_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_SUBFIELD_GENERATED»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_OF_NUM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_NUM_SUBFIELD_GENERATED»
  RING_POLYNOMIAL_CONST := SessionLibrary.RingTheory.«RING_POLYNOMIAL_CONST»
  RING_POLYNOMIAL_POW := SessionLibrary.RingTheory.«RING_POLYNOMIAL_POW»
  RING_POLYNOMIAL_VAR := SessionLibrary.RingTheory.«RING_POLYNOMIAL_VAR»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_0 := SessionLibrary.RingTheory.«RING_POW_0»
  RING_POW_1 := SessionLibrary.RingTheory.«RING_POW_1»
  RING_POW_2 := SessionLibrary.RingTheory.«RING_POW_2»
  RING_POW_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_POW_IN_SUBFIELD_GENERATED»
  RING_POW_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_POW_SUBFIELD_GENERATED»
  RING_PRODUCT_LT_2 := SessionLibrary.RingTheory.«RING_PRODUCT_LT_2»
  RING_SIMPLE_ALGEBRAIC_EXTENSION_BASIS := SessionLibrary.FieldTheory.«RING_SIMPLE_ALGEBRAIC_EXTENSION_BASIS»
  RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN := SessionLibrary.FieldTheory.«RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN»
  RING_SPAN_SING := SessionLibrary.FieldTheory.«RING_SPAN_SING»
  RING_SPAN_UNION := SessionLibrary.FieldTheory.«RING_SPAN_UNION»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_SUB_RZERO := SessionLibrary.RingTheory.«RING_SUB_RZERO»
  RING_SUM_LT_2 := SessionLibrary.RingTheory.«RING_SUM_LT_2»
  SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM_ROOT := SessionLibrary.FieldTheory.«SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM_ROOT»
  SIMPLE_IMAGE_GEN := Session.SIMPLE_IMAGE_GEN
  SQUAREFREE_0 := SessionLibrary.Pocklington.«SQUAREFREE_0»
  SQUAREFREE_EXP := SessionLibrary.Pocklington.«SQUAREFREE_EXP»
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_EQ := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_EQ»
  SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC»
  SUBRING_GENERATED_INC_GEN := SessionLibrary.RingTheory.«SUBRING_GENERATED_INC_GEN»
  SUBRING_GENERATED_SUPERSET := SessionLibrary.RingTheory.«SUBRING_GENERATED_SUPERSET»
  SUBSET := Session.SUBSET
  UNWIND_THM2 := Session.UNWIND_THM2
  basis_discriminant := SessionLibrary.RingDet.«basis_discriminant»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  free_basis := SessionLibrary.RingDet.«free_basis»
  int_congruent := Session.int_congruent
  int_divides := Session.int_divides
  isomorphic_ring := SessionLibrary.RingTheory.«isomorphic_ring»
  monic := SessionLibrary.RingTheory.«monic»
  mul_matrix := SessionLibrary.RingDet.«mul_matrix»
  number_field := SessionANT.Numfield.«number_field»
  poly_eval := SessionLibrary.RingTheory.«poly_eval»
  ring_div := SessionLibrary.RingTheory.«ring_div»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  ring_sub := SessionLibrary.RingTheory.«ring_sub»
  squarefree := SessionLibrary.Pocklington.«squarefree»

/-- What quadratic.ml uses from Session. -/
def deps : HolANT.Quadratic.QuadraticDeps where
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

/- The bundles, in quadratic.ml order. -/
initialize BQuadratic01 : HolANT.Quadratic.Quadratic01 ←
  ioB "setupQuadratic01" (HolANT.Quadratic.setupQuadratic01 deps).run
initialize BQuadratic02 : HolANT.Quadratic.Quadratic02 ←
  ioB "setupQuadratic02" (HolANT.Quadratic.setupQuadratic02 deps BQuadratic01).run
initialize BQuadratic03 : HolANT.Quadratic.Quadratic03 ←
  ioB "setupQuadratic03" (HolANT.Quadratic.setupQuadratic03 deps BQuadratic01 BQuadratic02).run

-- Quadratic01
def INT_SQUARE_SUB_MUL_SQUARE_MOD_4 : thm := BQuadratic01.INT_SQUARE_SUB_MUL_SQUARE_MOD_4
def INT_NORM_FORM_4_IMAGINARY : thm := BQuadratic01.INT_NORM_FORM_4_IMAGINARY
def IN_SUBFIELD_GENERATED_MUL_CANCEL : thm := BQuadratic01.IN_SUBFIELD_GENERATED_MUL_CANCEL
def SUBFIELD_GENERATED_ADD_MUL_EQ_0 : thm := BQuadratic01.SUBFIELD_GENERATED_ADD_MUL_EQ_0
def SUBFIELD_GENERATED_HALF_SUCC : thm := BQuadratic01.SUBFIELD_GENERATED_HALF_SUCC
def FREE_BASIS_SUBFIELD_GENERATED_2 : thm := BQuadratic01.FREE_BASIS_SUBFIELD_GENERATED_2
def INTEGRAL_ELEMENT_QUADRATIC : thm := BQuadratic01.INTEGRAL_ELEMENT_QUADRATIC
def PRIME_SUBFIELD_SQRT_INTEGER : thm := BQuadratic01.PRIME_SUBFIELD_SQRT_INTEGER
def PRIME_SUBFIELD_SQUAREFREE_MUL_SQUARE : thm := BQuadratic01.PRIME_SUBFIELD_SQUAREFREE_MUL_SQUARE
def SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD : thm := BQuadratic01.SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD
def QUADRATIC_FIELD_FREE_BASIS : thm := BQuadratic01.QUADRATIC_FIELD_FREE_BASIS
def QUADRATIC_FIELD_COORDINATES : thm := BQuadratic01.QUADRATIC_FIELD_COORDINATES
def QUADRATIC_FIELD_INT_COORDINATES_EQ : thm := BQuadratic01.QUADRATIC_FIELD_INT_COORDINATES_EQ
def QUADRATIC_FIELD_INTEGER_SQUARE : thm := BQuadratic01.QUADRATIC_FIELD_INTEGER_SQUARE
def QUADRATIC_FIELD_SQRT_EXISTS : thm := BQuadratic01.QUADRATIC_FIELD_SQRT_EXISTS
def QUADRATIC_FIELD_SQRT_UNIQUE : thm := BQuadratic01.QUADRATIC_FIELD_SQRT_UNIQUE
def QUADRATIC_FIELD_SQRT : thm := BQuadratic01.QUADRATIC_FIELD_SQRT
def FIELD_EXTENSION_SQRT : thm := BQuadratic01.FIELD_EXTENSION_SQRT

-- Quadratic02
def QUADRATIC_FIELD_EXISTS : thm := BQuadratic02.QUADRATIC_FIELD_EXISTS
def QUADRATIC_EXTEND_HOMOMORPHISM : thm := BQuadratic02.QUADRATIC_EXTEND_HOMOMORPHISM
def QUADRATIC_FIELD_UNIQUE_EXPLICIT : thm := BQuadratic02.QUADRATIC_FIELD_UNIQUE_EXPLICIT
def QUADRATIC_FIELD_UNIQUE : thm := BQuadratic02.QUADRATIC_FIELD_UNIQUE
def QUADRATIC_FIELD_TRACE : thm := BQuadratic02.QUADRATIC_FIELD_TRACE
def QUADRATIC_FIELD_INTEGRAL_COORDINATES : thm := BQuadratic02.QUADRATIC_FIELD_INTEGRAL_COORDINATES
def QUADRATIC_FIELD_INTEGRAL_FREE_BASIS : thm := BQuadratic02.QUADRATIC_FIELD_INTEGRAL_FREE_BASIS
def QUADRATIC_FIELD_INTEGRAL_BASIS_SQRT : thm := BQuadratic02.QUADRATIC_FIELD_INTEGRAL_BASIS_SQRT
def QUADRATIC_FIELD_INTEGRAL_BASIS_HALF : thm := BQuadratic02.QUADRATIC_FIELD_INTEGRAL_BASIS_HALF
def QUADRATIC_FIELD_INTEGRAL_BASIS : thm := BQuadratic02.QUADRATIC_FIELD_INTEGRAL_BASIS
def QUADRATIC_FIELD_BASIS_DISCRIMINANT : thm := BQuadratic02.QUADRATIC_FIELD_BASIS_DISCRIMINANT

-- Quadratic03
def QUADRATIC_FIELD_BASIS_DISCRIMINANT_HALF : thm := BQuadratic03.QUADRATIC_FIELD_BASIS_DISCRIMINANT_HALF
def QUADRATIC_FIELD_DISCRIMINANT : thm := BQuadratic03.QUADRATIC_FIELD_DISCRIMINANT

/-- `needs "ANT/quadratic.ml"`: already done by importing this module. -/
def ensureQuadratic : IO Unit := pure ()

end SessionANT.Quadratic
