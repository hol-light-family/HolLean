/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/hermite_inequality.ml                         . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/HermiteInequality.lean

  The session half of the hermite_inequality.ml translation: it supplies HolANT.HermiteInequality's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/hermite_inequality.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.HermiteInequality
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Isum
import SessionLibrary.Floor
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.Zlattice
import SessionANT.LinearForms

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.HermiteInequality

/-- The core theorems hermite_inequality.ml uses. -/
def core1 : HolANT.HermiteInequality.CoreThms1 where
  ADD1 := Session.ADD1
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_EQ_0 := Session.CARD_EQ_0
  EXISTS_IN_IMAGE := Session.EXISTS_IN_IMAGE
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_INT_SEG := Session.FINITE_INT_SEG
  FINITE_PRODUCT_DEPENDENT := Session.FINITE_PRODUCT_DEPENDENT
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FUN_EQ_THM := Session.FUN_EQ_THM
  IMAGE_EQ_EMPTY := Session.IMAGE_EQ_EMPTY
  IMP_CONJ := Session.IMP_CONJ
  INF_FINITE_LEMMA := Session.INF_FINITE_LEMMA
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGER_RING_SUM := SessionLibrary.RingTheory.«INTEGER_RING_SUM»
  INTEGER_ROUND := SessionLibrary.Floor.«INTEGER_ROUND»
  INTEGRAL_DOMAIN_INTEGER_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_INTEGER_RING»
  INT_ABS_BOUNDS := Session.INT_ABS_BOUNDS
  INT_POW2_ABS := Session.INT_POW2_ABS
  INT_POW_ONE := Session.INT_POW_ONE
  INT_PRIMITIVE_UNIMODULAR_COLUMN := SessionANT.Zlattice.«INT_PRIMITIVE_UNIMODULAR_COLUMN»
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_INSERT := Session.IN_INSERT
  IN_SING := Session.IN_SING
  IN_UNIV := Session.IN_UNIV
  LE_EXISTS := Session.LE_EXISTS
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_INSERT_EMPTY := Session.NOT_INSERT_EMPTY
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  QUADRATIC_FORM_BASIS_VECTOR := SessionANT.LinearForms.«QUADRATIC_FORM_BASIS_VECTOR»
  QUADRATIC_FORM_CHANGE_BASIS := SessionANT.LinearForms.«QUADRATIC_FORM_CHANGE_BASIS»
  QUADRATIC_FORM_COMPLETE_SQUARE := SessionANT.LinearForms.«QUADRATIC_FORM_COMPLETE_SQUARE»
  QUADRATIC_FORM_CONGRUENT_POSITIVE := SessionANT.LinearForms.«QUADRATIC_FORM_CONGRUENT_POSITIVE»
  QUADRATIC_FORM_MINIMAL_PRIMITIVE := SessionANT.LinearForms.«QUADRATIC_FORM_MINIMAL_PRIMITIVE»
  QUADRATIC_FORM_POS_LE := SessionANT.LinearForms.«QUADRATIC_FORM_POS_LE»
  QUADRATIC_FORM_SCHUR_POSITIVE := SessionANT.LinearForms.«QUADRATIC_FORM_SCHUR_POSITIVE»
  REAL_ARCH_SIMPLE := Session.REAL_ARCH_SIMPLE
  REAL_DET_CONGRUENT_MATRIX := SessionANT.LinearForms.«REAL_DET_CONGRUENT_MATRIX»
  REAL_DET_SCHUR_COMPLEMENT := SessionANT.LinearForms.«REAL_DET_SCHUR_COMPLEMENT»
  REAL_EQ_IMP_LE := Session.REAL_EQ_IMP_LE
  REAL_LE_LMUL := Session.REAL_LE_LMUL
  REAL_LE_MAX := Session.REAL_LE_MAX
  REAL_LE_MUL := Session.REAL_LE_MUL
  REAL_LE_MUL2 := Session.REAL_LE_MUL2
  REAL_LE_POW_2 := Session.REAL_LE_POW_2
  REAL_LE_RDIV_EQ := Session.REAL_LE_RDIV_EQ
  REAL_LE_REFL := Session.REAL_LE_REFL
  REAL_LE_RMUL := Session.REAL_LE_RMUL
  REAL_LE_SQUARE_ABS := Session.REAL_LE_SQUARE_ABS
  REAL_LE_TOTAL := Session.REAL_LE_TOTAL
  REAL_LE_TRANS := Session.REAL_LE_TRANS
  REAL_LT_01 := Session.REAL_LT_01
  REAL_LT_IMP_LE := Session.REAL_LT_IMP_LE
  REAL_LT_IMP_NZ := Session.REAL_LT_IMP_NZ
  REAL_LT_MUL := Session.REAL_LT_MUL
  REAL_MUL_ASSOC := Session.REAL_MUL_ASSOC
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_RID := Session.REAL_MUL_RID
  REAL_OF_INT_OF_REAL := SessionLibrary.Floor.«REAL_OF_INT_OF_REAL»
  REAL_POW2_ABS := Session.REAL_POW2_ABS
  REAL_POW_2 := Session.REAL_POW_2
  REAL_POW_ADD := Session.REAL_POW_ADD
  REAL_POW_LE2 := Session.REAL_POW_LE2
  REAL_POW_LT := Session.REAL_POW_LT
  REAL_POW_MUL := Session.REAL_POW_MUL
  REAL_POW_ONE := Session.REAL_POW_ONE
  REAL_RING_CLAUSES := SessionLibrary.RingTheory.«REAL_RING_CLAUSES»
  REAL_RING_OF_INT := SessionLibrary.RingTheory.«REAL_RING_OF_INT»
  RING_DET_DEPENDENT_COLUMNS := SessionLibrary.RingDet.«RING_DET_DEPENDENT_COLUMNS»
  RING_DET_EMPTY := SessionLibrary.RingDet.«RING_DET_EMPTY»
  RING_DET_HOMOMORPHISM := SessionLibrary.RingDet.«RING_DET_HOMOMORPHISM»
  RING_DET_SING := SessionLibrary.RingDet.«RING_DET_SING»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  SUBSET := Session.SUBSET
  SUC_SUB1 := Session.SUC_SUB1
  SUM_EQ := Session.SUM_EQ
  int_abs_th := Session.int_abs_th
  int_eq := Session.int_eq
  int_isum := SessionLibrary.Isum.«int_isum»
  int_le := Session.int_le
  int_mul_th := Session.int_mul_th
  int_of_num_th := Session.int_of_num_th
  int_pow_th := Session.int_pow_th
  real_div := Session.real_div
  real_pow := Session.real_pow

/-- What hermite_inequality.ml uses from Session. -/
def deps : HolANT.HermiteInequality.HermiteInequalityDeps where
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
  NUM_RING := Session.NUM_RING
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in hermite_inequality.ml order. -/
initialize BHermiteInequality : HolANT.HermiteInequality.HermiteInequality ←
  ioB "setupHermiteInequality" (HolANT.HermiteInequality.setupHermiteInequality deps).run

-- HermiteInequality
def QUADRATIC_FORM_DET_POS : thm := BHermiteInequality.QUADRATIC_FORM_DET_POS
def QUADRATIC_FORM_FINITE_INTEGER_POINTS : thm := BHermiteInequality.QUADRATIC_FORM_FINITE_INTEGER_POINTS
def QUADRATIC_FORM_MINIMAL_VECTOR : thm := BHermiteInequality.QUADRATIC_FORM_MINIMAL_VECTOR
def HERMITE_INEQUALITY : thm := BHermiteInequality.HERMITE_INEQUALITY

/-- `needs "ANT/hermite_inequality.ml"`: already done by importing this module. -/
def ensureHermiteInequality : IO Unit := pure ()

end SessionANT.HermiteInequality
