/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/zlattice.ml                                   . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/Zlattice.lean

  The session half of the zlattice.ml translation: it supplies HolANT.Zlattice's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/zlattice.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.Zlattice
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
import SessionANT.Algmisc
import SessionLibrary.RingDet

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.Zlattice

/-- The core theorems zlattice.ml uses. -/
def core1 : HolANT.Zlattice.CoreThms1 where
  CARD_IMAGE_LE := Session.CARD_IMAGE_LE
  CARD_PERMUTATIONS := SessionLibrary.Permutations.«CARD_PERMUTATIONS»
  CARD_SING := Session.CARD_SING
  COND_ID := Session.COND_ID
  COND_RAND := Session.COND_RAND
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  EQ_IMP := Session.EQ_IMP
  EQ_TRANS := Session.EQ_TRANS
  ETA_AX := Session.ETA_AX
  EXISTS_IN_IMAGE := Session.EXISTS_IN_IMAGE
  EXISTS_PAIR_THM := Session.EXISTS_PAIR_THM
  EXTENSION := Session.EXTENSION
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_PERMUTATIONS := SessionLibrary.Permutations.«FINITE_PERMUTATIONS»
  FINITE_SING := Session.FINITE_SING
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FUN_EQ_THM := Session.FUN_EQ_THM
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_FUNSPACE := Session.HAS_SIZE_FUNSPACE
  HAS_SIZE_IMAGE_INJ := Session.HAS_SIZE_IMAGE_INJ
  HAS_SIZE_INT_SEG_LT := SessionANT.Algmisc.«HAS_SIZE_INT_SEG_LT»
  HAS_SIZE_NUMSEG_LT := Session.HAS_SIZE_NUMSEG_LT
  HAS_SIZE_PRODUCT := Session.HAS_SIZE_PRODUCT
  IMP_CONJ := Session.IMP_CONJ
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGER_RING_POW := SessionLibrary.RingTheory.«INTEGER_RING_POW»
  INTEGER_RING_PRODUCT := SessionLibrary.RingTheory.«INTEGER_RING_PRODUCT»
  INTEGER_RING_SUM := SessionLibrary.RingTheory.«INTEGER_RING_SUM»
  INTEGRAL_DOMAIN_INTEGER_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_INTEGER_RING»
  INT_ABS_MUL := Session.INT_ABS_MUL
  INT_ABS_NEG := Session.INT_ABS_NEG
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_ABS_POS := Session.INT_ABS_POS
  INT_ABS_ZERO := Session.INT_ABS_ZERO
  INT_ADD_RDISTRIB := Session.INT_ADD_RDISTRIB
  INT_ADD_RID := Session.INT_ADD_RID
  INT_DIVIDES_LE := Session.INT_DIVIDES_LE
  INT_DIVISION := Session.INT_DIVISION
  INT_ENTIRE := Session.INT_ENTIRE
  INT_EQ_IMP_LE := Session.INT_EQ_IMP_LE
  INT_IMAGE := Session.INT_IMAGE
  INT_LET_TRANS := Session.INT_LET_TRANS
  INT_LT_IMP_LE := Session.INT_LT_IMP_LE
  INT_MUL_AC := Session.INT_MUL_AC
  INT_MUL_ASSOC := Session.INT_MUL_ASSOC
  INT_MUL_EQ_1 := Session.INT_MUL_EQ_1
  INT_MUL_LID := Session.INT_MUL_LID
  INT_MUL_LNEG := Session.INT_MUL_LNEG
  INT_MUL_LZERO := Session.INT_MUL_LZERO
  INT_MUL_RID := Session.INT_MUL_RID
  INT_MUL_RZERO := Session.INT_MUL_RZERO
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_OF_NUM_SUC := Session.INT_OF_NUM_SUC
  INT_POW_EQ_0 := Session.INT_POW_EQ_0
  INT_REM_EQ_0 := Session.INT_REM_EQ_0
  INT_SUB_0 := Session.INT_SUB_0
  INT_SUB_LDISTRIB := Session.INT_SUB_LDISTRIB
  INT_SUB_LZERO := Session.INT_SUB_LZERO
  INT_SUB_REFL := Session.INT_SUB_REFL
  INT_SUB_RNEG := Session.INT_SUB_RNEG
  INT_SUB_RZERO := Session.INT_SUB_RZERO
  IN_ELIM_PAIR_THM := Session.IN_ELIM_PAIR_THM
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_SING := Session.IN_SING
  IN_UNIV := Session.IN_UNIV
  IPRODUCT_ABS_BOUND := SessionLibrary.Products.«IPRODUCT_ABS_BOUND»
  IPRODUCT_DELTA := SessionLibrary.Products.«IPRODUCT_DELTA»
  ISUM_0 := SessionLibrary.Isum.«ISUM_0»
  ISUM_ABS_BOUND := SessionLibrary.Isum.«ISUM_ABS_BOUND»
  ISUM_CLAUSES := Session.ISUM_CLAUSES
  ISUM_DELTA := SessionLibrary.Isum.«ISUM_DELTA»
  ISUM_DELTA_GEN := SessionLibrary.Isum.«ISUM_DELTA_GEN»
  ISUM_EQ := SessionLibrary.Isum.«ISUM_EQ»
  ISUM_LMUL := SessionLibrary.Isum.«ISUM_LMUL»
  ISUM_POS_LE := SessionLibrary.Isum.«ISUM_POS_LE»
  ISUM_RMUL := SessionLibrary.Isum.«ISUM_RMUL»
  ISUM_SUB := SessionLibrary.Isum.«ISUM_SUB»
  ISUM_SWAP := SessionLibrary.Isum.«ISUM_SWAP»
  I_THM := Session.I_THM
  LEFT_AND_EXISTS_THM := Session.LEFT_AND_EXISTS_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_TRANS := Session.LE_TRANS
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NUM_OF_INT_MUL := Session.NUM_OF_INT_MUL
  NUM_OF_INT_OF_NUM := Session.NUM_OF_INT_OF_NUM
  PAIR_EQ := Session.PAIR_EQ
  PERMUTES_IN_IMAGE := SessionLibrary.Permutations.«PERMUTES_IN_IMAGE»
  RIGHT_AND_EXISTS_THM := Session.RIGHT_AND_EXISTS_THM
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RING_DET_CMUL := SessionLibrary.RingDet.«RING_DET_CMUL»
  RING_DET_DEPENDENT_COLUMNS := SessionLibrary.RingDet.«RING_DET_DEPENDENT_COLUMNS»
  RING_DET_DIAGONAL := SessionLibrary.RingDet.«RING_DET_DIAGONAL»
  RING_DET_EMPTY := SessionLibrary.RingDet.«RING_DET_EMPTY»
  RING_DET_EQ := SessionLibrary.RingDet.«RING_DET_EQ»
  RING_DET_I := SessionLibrary.RingDet.«RING_DET_I»
  RING_DET_LAPLACE_INSERT := SessionLibrary.RingDet.«RING_DET_LAPLACE_INSERT»
  RING_DET_MUL := SessionLibrary.RingDet.«RING_DET_MUL»
  RING_DET_ROW_OPERATION := SessionLibrary.RingDet.«RING_DET_ROW_OPERATION»
  RING_DET_SWAP_ROWS := SessionLibrary.RingDet.«RING_DET_SWAP_ROWS»
  RING_SIGN_I := SessionLibrary.RingDet.«RING_SIGN_I»
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  SWAP_REFL := SessionLibrary.Permutations.«SWAP_REFL»
  int_divides := Session.int_divides
  num_WOP := Session.num_WOP
  ring_det := SessionLibrary.RingDet.«ring_det»
  ring_sign := SessionLibrary.RingDet.«ring_sign»
  swap := SessionLibrary.Permutations.«swap»

/-- What zlattice.ml uses from Session. -/
def deps : HolANT.Zlattice.ZlatticeDeps where
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
  WF_INDUCT_TAC := Session.WF_INDUCT_TAC
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in zlattice.ml order. -/
initialize BZlattice01 : HolANT.Zlattice.Zlattice01 ←
  ioB "setupZlattice01" (HolANT.Zlattice.setupZlattice01 deps).run
initialize BZlattice02 : HolANT.Zlattice.Zlattice02 ←
  ioB "setupZlattice02" (HolANT.Zlattice.setupZlattice02 deps BZlattice01).run

-- Zlattice01
def int_lattice : thm := BZlattice01.int_lattice
def int_matrix_image : thm := BZlattice01.int_matrix_image
def int_cosets : thm := BZlattice01.int_cosets
def INT_LATTICE_0 : thm := BZlattice01.INT_LATTICE_0
def INT_LATTICE_SUB : thm := BZlattice01.INT_LATTICE_SUB
def INT_LATTICE_SUPPORT : thm := BZlattice01.INT_LATTICE_SUPPORT
def INT_LATTICE_NEG : thm := BZlattice01.INT_LATTICE_NEG
def INT_LATTICE_ADD : thm := BZlattice01.INT_LATTICE_ADD
def INT_LATTICE_CMUL : thm := BZlattice01.INT_LATTICE_CMUL
def INT_LATTICE_CLOSED : thm := BZlattice01.INT_LATTICE_CLOSED
def INT_LATTICE_ISUM : thm := BZlattice01.INT_LATTICE_ISUM
def INT_MATRIX_IMAGE_IN : thm := BZlattice01.INT_MATRIX_IMAGE_IN
def INT_LATTICE_INT_MATRIX_IMAGE : thm := BZlattice01.INT_LATTICE_INT_MATRIX_IMAGE
def INT_MATRIX_IMAGE_COLUMN : thm := BZlattice01.INT_MATRIX_IMAGE_COLUMN
def INT_MATRIX_IMAGE_SUBSET : thm := BZlattice01.INT_MATRIX_IMAGE_SUBSET
def INT_MATRIX_IMAGE_FACTOR : thm := BZlattice01.INT_MATRIX_IMAGE_FACTOR
def INT_DET_MUL : thm := BZlattice01.INT_DET_MUL
def INT_DET_INSERT_ROW : thm := BZlattice01.INT_DET_INSERT_ROW
def INT_MATRIX_MUL_ASSOC : thm := BZlattice01.INT_MATRIX_MUL_ASSOC
def INT_MATRIX_IMAGE_INJECTIVE : thm := BZlattice01.INT_MATRIX_IMAGE_INJECTIVE
def INT_LATTICE_FULL_RANK : thm := BZlattice01.INT_LATTICE_FULL_RANK
def INT_MATRIX_IMAGE_EQ_DET : thm := BZlattice01.INT_MATRIX_IMAGE_EQ_DET
def INT_PRIMITIVE_UNIMODULAR_COLUMN : thm := BZlattice01.INT_PRIMITIVE_UNIMODULAR_COLUMN
def INT_DET_BOUND : thm := BZlattice01.INT_DET_BOUND
def INT_LATTICE_CONG_SYM : thm := BZlattice01.INT_LATTICE_CONG_SYM
def INT_LATTICE_CONG_TRANS : thm := BZlattice01.INT_LATTICE_CONG_TRANS
def INT_LATTICE_COSET_EQ : thm := BZlattice01.INT_LATTICE_COSET_EQ
def INT_COSETS_COVER : thm := BZlattice01.INT_COSETS_COVER
def INT_COSETS_TRANSVERSAL : thm := BZlattice01.INT_COSETS_TRANSVERSAL
def INT_COSETS_FINITE : thm := BZlattice01.INT_COSETS_FINITE
def INT_LATTICE_COORDINATE_GENERATOR : thm := BZlattice01.INT_LATTICE_COORDINATE_GENERATOR
def INT_LATTICE_SPLIT : thm := BZlattice01.INT_LATTICE_SPLIT
def INT_MATRIX_IMAGE_INSERT : thm := BZlattice01.INT_MATRIX_IMAGE_INSERT

-- Zlattice02
def INT_LATTICE_INSERT_IMAGE : thm := BZlattice02.INT_LATTICE_INSERT_IMAGE
def INT_LATTICE_MATRIX_IMAGE : thm := BZlattice02.INT_LATTICE_MATRIX_IMAGE
def INT_LATTICE_TRANSVERSAL_INSERT : thm := BZlattice02.INT_LATTICE_TRANSVERSAL_INSERT
def INT_MATRIX_IMAGE_TRANSVERSAL : thm := BZlattice02.INT_MATRIX_IMAGE_TRANSVERSAL
def INT_COSETS_MATRIX_IMAGE : thm := BZlattice02.INT_COSETS_MATRIX_IMAGE

/-- `needs "ANT/zlattice.ml"`: already done by importing this module. -/
def ensureZlattice : IO Unit := pure ()

end SessionANT.Zlattice
