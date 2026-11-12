/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/linear_forms.ml                               . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/LinearForms.lean

  The session half of the linear_forms.ml translation: it supplies HolANT.LinearForms's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/linear_forms.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.LinearForms
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Permutations
import SessionLibrary.Isum
import SessionLibrary.Products
import SessionLibrary.Floor
import SessionANT.Algmisc
import SessionLibrary.RingDet
import SessionANT.Zlattice

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.LinearForms

/-- The core theorems linear_forms.ml uses. -/
def core1 : HolANT.LinearForms.CoreThms1 where
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_PERMUTATIONS := SessionLibrary.Permutations.«CARD_PERMUTATIONS»
  CARD_SUBSET := Session.CARD_SUBSET
  EQ_SYM_EQ := Session.EQ_SYM_EQ
  EQ_TRANS := Session.EQ_TRANS
  EXTENSION := Session.EXTENSION
  FINITE_FUNSPACE := Session.FINITE_FUNSPACE
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_INT_SEG := Session.FINITE_INT_SEG
  FINITE_PERMUTATIONS := SessionLibrary.Permutations.«FINITE_PERMUTATIONS»
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET := Session.FINITE_SUBSET
  FLOOR := SessionLibrary.Floor.«FLOOR»
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FUN_EQ_THM := Session.FUN_EQ_THM
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_FUNSPACE := Session.HAS_SIZE_FUNSPACE
  HAS_SIZE_IMAGE_INJ := Session.HAS_SIZE_IMAGE_INJ
  HAS_SIZE_INT_SEG_LT := SessionANT.Algmisc.«HAS_SIZE_INT_SEG_LT»
  IMP_CONJ := Session.IMP_CONJ
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGRAL_DOMAIN_REAL_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_REAL_RING»
  INT_ABS_BOUNDS := Session.INT_ABS_BOUNDS
  INT_ABS_POS := Session.INT_ABS_POS
  INT_COSETS_MATRIX_IMAGE := SessionANT.Zlattice.«INT_COSETS_MATRIX_IMAGE»
  INT_ENTIRE := Session.INT_ENTIRE
  INT_LATTICE_0 := SessionANT.Zlattice.«INT_LATTICE_0»
  INT_LATTICE_INT_MATRIX_IMAGE := SessionANT.Zlattice.«INT_LATTICE_INT_MATRIX_IMAGE»
  INT_MATRIX_IMAGE_IN := SessionANT.Zlattice.«INT_MATRIX_IMAGE_IN»
  INT_MUL_RZERO := Session.INT_MUL_RZERO
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_SUB_0 := Session.INT_SUB_0
  INT_SUB_REFL := Session.INT_SUB_REFL
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_INSERT := Session.IN_INSERT
  IN_SING := Session.IN_SING
  IN_UNIV := Session.IN_UNIV
  ISUM_EQ := SessionLibrary.Isum.«ISUM_EQ»
  ISUM_EQ_0 := SessionLibrary.Isum.«ISUM_EQ_0»
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_1 := Session.LE_1
  LE_REFL := Session.LE_REFL
  LT_IMP_LE := Session.LT_IMP_LE
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_LE := Session.NOT_LE
  PERMUTES_IN_IMAGE := SessionLibrary.Permutations.«PERMUTES_IN_IMAGE»
  PRODUCT_ABS := SessionLibrary.Products.«PRODUCT_ABS»
  PRODUCT_CLAUSES := Session.PRODUCT_CLAUSES
  PRODUCT_CONST := SessionLibrary.Products.«PRODUCT_CONST»
  PRODUCT_INV := SessionLibrary.Products.«PRODUCT_INV»
  PRODUCT_LE := SessionLibrary.Products.«PRODUCT_LE»
  PRODUCT_MUL := SessionLibrary.Products.«PRODUCT_MUL»
  PRODUCT_POS_LT := SessionLibrary.Products.«PRODUCT_POS_LT»
  REAL_ABS_INV := Session.REAL_ABS_INV
  REAL_ABS_MUL := Session.REAL_ABS_MUL
  REAL_ABS_NUM := Session.REAL_ABS_NUM
  REAL_ABS_NZ := Session.REAL_ABS_NZ
  REAL_ABS_POS := Session.REAL_ABS_POS
  REAL_ADD_RDISTRIB := Session.REAL_ADD_RDISTRIB
  REAL_ADD_RID := Session.REAL_ADD_RID
  REAL_ARCH := Session.REAL_ARCH
  REAL_ARCH_INV := Session.REAL_ARCH_INV
  REAL_ARCH_SIMPLE := Session.REAL_ARCH_SIMPLE
  REAL_DIV_LMUL := Session.REAL_DIV_LMUL
  REAL_ENTIRE := Session.REAL_ENTIRE
  REAL_EQ_IMP_LE := Session.REAL_EQ_IMP_LE
  REAL_FIELD_CLAUSES := SessionLibrary.RingTheory.«REAL_FIELD_CLAUSES»
  REAL_INV_EQ_0 := Session.REAL_INV_EQ_0
  REAL_INV_LE_1 := Session.REAL_INV_LE_1
  REAL_LET_TRANS := Session.REAL_LET_TRANS
  REAL_LE_INV2 := Session.REAL_LE_INV2
  REAL_LE_LADD := Session.REAL_LE_LADD
  REAL_LE_LMUL := Session.REAL_LE_LMUL
  REAL_LE_LMUL_EQ := Session.REAL_LE_LMUL_EQ
  REAL_LE_MUL := Session.REAL_LE_MUL
  REAL_LE_MUL2 := Session.REAL_LE_MUL2
  REAL_LE_REFL := Session.REAL_LE_REFL
  REAL_LE_RMUL := Session.REAL_LE_RMUL
  REAL_LE_SQUARE_ABS := Session.REAL_LE_SQUARE_ABS
/-- The core theorems linear_forms.ml uses. -/
def core2 : HolANT.LinearForms.CoreThms2 where
  REAL_LE_TRANS := Session.REAL_LE_TRANS
  REAL_LT_ADDR := Session.REAL_LT_ADDR
  REAL_LT_DIV := Session.REAL_LT_DIV
  REAL_LT_IMP_LE := Session.REAL_LT_IMP_LE
  REAL_LT_IMP_NZ := Session.REAL_LT_IMP_NZ
  REAL_LT_INV_EQ := Session.REAL_LT_INV_EQ
  REAL_LT_LDIV_EQ := Session.REAL_LT_LDIV_EQ
  REAL_LT_LMUL := Session.REAL_LT_LMUL
  REAL_LT_LMUL_EQ := Session.REAL_LT_LMUL_EQ
  REAL_LT_MIN := Session.REAL_LT_MIN
  REAL_LT_MUL := Session.REAL_LT_MUL
  REAL_LT_RDIV_EQ := Session.REAL_LT_RDIV_EQ
  REAL_LT_RMUL := Session.REAL_LT_RMUL
  REAL_MIN_MIN := Session.REAL_MIN_MIN
  REAL_MUL_ASSOC := Session.REAL_MUL_ASSOC
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_LZERO := Session.REAL_MUL_LZERO
  REAL_MUL_RID := Session.REAL_MUL_RID
  REAL_MUL_RZERO := Session.REAL_MUL_RZERO
  REAL_MUL_SYM := Session.REAL_MUL_SYM
  REAL_NOT_LE := Session.REAL_NOT_LE
  REAL_NOT_LT := Session.REAL_NOT_LT
  REAL_OF_INT_OF_REAL := SessionLibrary.Floor.«REAL_OF_INT_OF_REAL»
  REAL_OF_NUM_ADD := Session.REAL_OF_NUM_ADD
  REAL_OF_NUM_LE := Session.REAL_OF_NUM_LE
  REAL_OF_NUM_LT := Session.REAL_OF_NUM_LT
  REAL_OF_NUM_POW := Session.REAL_OF_NUM_POW
  REAL_OF_NUM_SUB := Session.REAL_OF_NUM_SUB
  REAL_POS := Session.REAL_POS
  REAL_POW_EQ_0 := Session.REAL_POW_EQ_0
  REAL_POW_LE := Session.REAL_POW_LE
  REAL_POW_LT := Session.REAL_POW_LT
  REAL_POW_LT_1 := Session.REAL_POW_LT_1
  REAL_POW_MUL := Session.REAL_POW_MUL
  REAL_RING_CLAUSES := SessionLibrary.RingTheory.«REAL_RING_CLAUSES»
  REAL_RING_OF_INT := SessionLibrary.RingTheory.«REAL_RING_OF_INT»
  REAL_RING_PRODUCT := SessionLibrary.RingTheory.«REAL_RING_PRODUCT»
  REAL_RING_SUM := SessionLibrary.RingTheory.«REAL_RING_SUM»
  REAL_SUB_LDISTRIB := Session.REAL_SUB_LDISTRIB
  REAL_SUB_LT := Session.REAL_SUB_LT
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RING_DET_ADJUGATE_COLUMNS := SessionLibrary.RingDet.«RING_DET_ADJUGATE_COLUMNS»
  RING_DET_BLOCK_TRIANGULAR := SessionLibrary.RingDet.«RING_DET_BLOCK_TRIANGULAR»
  RING_DET_CMUL := SessionLibrary.RingDet.«RING_DET_CMUL»
  RING_DET_DEPENDENT_COLUMNS := SessionLibrary.RingDet.«RING_DET_DEPENDENT_COLUMNS»
  RING_DET_EMPTY := SessionLibrary.RingDet.«RING_DET_EMPTY»
  RING_DET_EQ := SessionLibrary.RingDet.«RING_DET_EQ»
  RING_DET_HOMOMORPHISM := SessionLibrary.RingDet.«RING_DET_HOMOMORPHISM»
  RING_DET_I := SessionLibrary.RingDet.«RING_DET_I»
  RING_DET_MUL := SessionLibrary.RingDet.«RING_DET_MUL»
  RING_DET_ROWS_MUL := SessionLibrary.RingDet.«RING_DET_ROWS_MUL»
  RING_DET_SING := SessionLibrary.RingDet.«RING_DET_SING»
  RING_DET_TRANSP := SessionLibrary.RingDet.«RING_DET_TRANSP»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  SUC_SUB1 := Session.SUC_SUB1
  SUM_ABS_BOUND := Session.SUM_ABS_BOUND
  SUM_ABS_LE := Session.SUM_ABS_LE
  SUM_ADD := Session.SUM_ADD
  SUM_BOUND := Session.SUM_BOUND
  SUM_CLAUSES := Session.SUM_CLAUSES
  SUM_CONST := Session.SUM_CONST
  SUM_DELTA := Session.SUM_DELTA
  SUM_EQ := Session.SUM_EQ
  SUM_EQ_0 := Session.SUM_EQ_0
  SUM_LE := Session.SUM_LE
  SUM_LMUL := Session.SUM_LMUL
  SUM_POS_BOUND := Session.SUM_POS_BOUND
  SUM_POS_LE := Session.SUM_POS_LE
  SUM_RMUL := Session.SUM_RMUL
  SUM_SUB := Session.SUM_SUB
  SUM_SWAP := Session.SUM_SWAP
  int_abs_th := Session.int_abs_th
  int_cosets := SessionANT.Zlattice.«int_cosets»
  int_divides := Session.int_divides
  int_eq := Session.int_eq
  int_isum := SessionLibrary.Isum.«int_isum»
  int_le := Session.int_le
  int_lt := Session.int_lt
  int_mul_th := Session.int_mul_th
  int_of_num_th := Session.int_of_num_th
  num_FINITE := Session.num_FINITE
  real_div := Session.real_div
  real_pow := Session.real_pow
  ring_det := SessionLibrary.RingDet.«ring_det»
  ring_sign := SessionLibrary.RingDet.«ring_sign»

/-- What linear_forms.ml uses from Session. -/
def deps : HolANT.LinearForms.LinearFormsDeps where
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
  REAL_RING t := ExceptT.mk (Session.REAL_RING t)
  core1 := core1
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in linear_forms.ml order. -/
initialize BLinearForms01 : HolANT.LinearForms.LinearForms01 ←
  ioB "setupLinearForms01" (HolANT.LinearForms.setupLinearForms01 deps).run
initialize BLinearForms02 : HolANT.LinearForms.LinearForms02 ←
  ioB "setupLinearForms02" (HolANT.LinearForms.setupLinearForms02 deps BLinearForms01).run

-- LinearForms01
def PRODUCT_SUB_BOUND : thm := BLinearForms01.PRODUCT_SUB_BOUND
def REAL_DET_SUB_BOUND : thm := BLinearForms01.REAL_DET_SUB_BOUND
def REAL_MATRIX_LEFT_INVERSE : thm := BLinearForms01.REAL_MATRIX_LEFT_INVERSE
def INT_MATRIX_PIGEONHOLE : thm := BLinearForms01.INT_MATRIX_PIGEONHOLE
def REAL_DET_ROUNDING : thm := BLinearForms01.REAL_DET_ROUNDING
def MINKOWSKI_LINEAR_FORMS_STRICT : thm := BLinearForms01.MINKOWSKI_LINEAR_FORMS_STRICT
def MINKOWSKI_LINEAR_FORMS : thm := BLinearForms01.MINKOWSKI_LINEAR_FORMS
def QUADRATIC_FORM_COMPLETE_SQUARE : thm := BLinearForms01.QUADRATIC_FORM_COMPLETE_SQUARE

-- LinearForms02
def REAL_DET_SCHUR_COMPLEMENT : thm := BLinearForms02.REAL_DET_SCHUR_COMPLEMENT
def QUADRATIC_FORM_BASIS_VECTOR : thm := BLinearForms02.QUADRATIC_FORM_BASIS_VECTOR
def QUADRATIC_FORM_SCHUR_POSITIVE : thm := BLinearForms02.QUADRATIC_FORM_SCHUR_POSITIVE
def QUADRATIC_FORM_POS_LE : thm := BLinearForms02.QUADRATIC_FORM_POS_LE
def QUADRATIC_FORM_MINIMAL_PRIMITIVE : thm := BLinearForms02.QUADRATIC_FORM_MINIMAL_PRIMITIVE
def QUADRATIC_FORM_CHANGE_BASIS : thm := BLinearForms02.QUADRATIC_FORM_CHANGE_BASIS
def REAL_DET_CONGRUENT_MATRIX : thm := BLinearForms02.REAL_DET_CONGRUENT_MATRIX
def QUADRATIC_FORM_CONGRUENT_POSITIVE : thm := BLinearForms02.QUADRATIC_FORM_CONGRUENT_POSITIVE

/-- `needs "ANT/linear_forms.ml"`: already done by importing this module. -/
def ensureLinearForms : IO Unit := pure ()

end SessionANT.LinearForms
