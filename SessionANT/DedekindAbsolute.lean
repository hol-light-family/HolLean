/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/dedekind_absolute.ml                          . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/DedekindAbsolute.lean

  The session half of the dedekind_absolute.ml translation: it supplies HolANT.DedekindAbsolute's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/dedekind_absolute.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.DedekindAbsolute
import SessionLibrary.Products
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionANT.Algmisc
import SessionLibrary.Matroids
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionLibrary.FieldTheory
import SessionANT.Integral
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.IdealNorm
import SessionANT.ValuationRing

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.DedekindAbsolute

/-- The core theorems dedekind_absolute.ml uses. -/
def core1 : HolANT.DedekindAbsolute.CoreThms1 where
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_SUBSET := Session.CARD_SUBSET
  CARRIER_SUBRING_GENERATED_SUBRING := SessionLibrary.RingTheory.«CARRIER_SUBRING_GENERATED_SUBRING»
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DEDEKIND_IDEAL_FACTORIZATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_FACTORIZATION»
  DEDEKIND_VALUATION_ADD := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_ADD»
  DEDEKIND_VALUATION_IMAGE := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_IMAGE»
  DEDEKIND_VALUATION_MUL := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_MUL»
  DEDEKIND_VALUATION_PRIME_IDEAL := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_PRIME_IDEAL»
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  EQ_IMP := Session.EQ_IMP
  EXTENSION := Session.EXTENSION
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_MUL_RINV := SessionLibrary.RingTheory.«FIELD_MUL_RINV»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_INTEGRAL_DOMAIN_POW_CARD := SessionLibrary.FieldTheory.«FINITE_INTEGRAL_DOMAIN_POW_CARD»
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FORALL_INT_CASES := Session.FORALL_INT_CASES
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FUN_EQ_THM := Session.FUN_EQ_THM
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_GENERATED_INC_GEN := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC_GEN»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_NORM_FACTORIZATION := SessionANT.IdealNorm.«IDEAL_NORM_FACTORIZATION»
  IDEAL_NORM_GT_1 := SessionANT.IdealNorm.«IDEAL_NORM_GT_1»
  IDEAL_NORM_IDEAL_POW := SessionANT.IdealNorm.«IDEAL_NORM_IDEAL_POW»
  IMP_CONJ := Session.IMP_CONJ
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_NONTRIVIAL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_NONTRIVIAL»
  INTEGRAL_ELEMENT_OVER_SUBRING := SessionANT.Integral.«INTEGRAL_ELEMENT_OVER_SUBRING»
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_DIVISION := Session.INT_DIVISION
  INT_LE_NEG2 := Session.INT_LE_NEG2
  INT_MIN_LE := Session.INT_MIN_LE
  INT_NEG_ADD := Session.INT_NEG_ADD
  INT_NOT_LE := Session.INT_NOT_LE
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_SING := Session.IN_SING
  LE_REFL := Session.LE_REFL
  LE_TRANS := Session.LE_TRANS
  LT_IMP_LE := Session.LT_IMP_LE
  MONO_EXISTS := Session.MONO_EXISTS
  MONO_OR := Session.MONO_OR
  MULT_SYM := Session.MULT_SYM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  PRIME_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_PROPER_IDEAL»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRODUCT_EQ := SessionLibrary.Products.«PRODUCT_EQ»
  PROPER_IDEAL_ALT := SessionLibrary.RingTheory.«PROPER_IDEAL_ALT»
  REAL_ABS_POS := Session.REAL_ABS_POS
  REAL_ARCH := Session.REAL_ARCH
  REAL_ENTIRE := Session.REAL_ENTIRE
  REAL_INV_0 := Session.REAL_INV_0
  REAL_INV_1 := Session.REAL_INV_1
  REAL_INV_1_LT := Session.REAL_INV_1_LT
  REAL_INV_LT_1 := Session.REAL_INV_LT_1
  REAL_LE_ADD2 := Session.REAL_LE_ADD2
  REAL_LE_ANTISYM := Session.REAL_LE_ANTISYM
  REAL_LE_LADD := Session.REAL_LE_LADD
  REAL_LE_LDIV_EQ := Session.REAL_LE_LDIV_EQ
  REAL_LE_MAX := Session.REAL_LE_MAX
  REAL_LE_MUL := Session.REAL_LE_MUL
  REAL_LE_MUL2 := Session.REAL_LE_MUL2
  REAL_LE_REFL := Session.REAL_LE_REFL
  REAL_LE_RMUL := Session.REAL_LE_RMUL
  REAL_LE_TRANS := Session.REAL_LE_TRANS
  REAL_LTE_TRANS := Session.REAL_LTE_TRANS
  REAL_LT_01 := Session.REAL_LT_01
  REAL_LT_IMP_LE := Session.REAL_LT_IMP_LE
  REAL_LT_LE := Session.REAL_LT_LE
  REAL_LT_LMUL := Session.REAL_LT_LMUL
  REAL_LT_RDIV_EQ := Session.REAL_LT_RDIV_EQ
/-- The core theorems dedekind_absolute.ml uses. -/
def core2 : HolANT.DedekindAbsolute.CoreThms2 where
  REAL_MAX_LE := Session.REAL_MAX_LE
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_LINV := Session.REAL_MUL_LINV
  REAL_MUL_LZERO := Session.REAL_MUL_LZERO
  REAL_MUL_RZERO := Session.REAL_MUL_RZERO
  REAL_NOT_LE := Session.REAL_NOT_LE
  REAL_NOT_LT := Session.REAL_NOT_LT
  REAL_OF_NUM_ADD := Session.REAL_OF_NUM_ADD
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_OF_NUM_LE := Session.REAL_OF_NUM_LE
  REAL_OF_NUM_LT := Session.REAL_OF_NUM_LT
  REAL_OF_NUM_NPRODUCT := SessionLibrary.Products.«REAL_OF_NUM_NPRODUCT»
  REAL_OF_NUM_POW := Session.REAL_OF_NUM_POW
  REAL_OF_NUM_SUC := Session.REAL_OF_NUM_SUC
  REAL_POS := Session.REAL_POS
  REAL_POW_2 := Session.REAL_POW_2
  REAL_POW_ADD := Session.REAL_POW_ADD
  REAL_POW_DIV := Session.REAL_POW_DIV
  REAL_POW_EQ_0 := Session.REAL_POW_EQ_0
  REAL_POW_EQ_1_IMP := Session.REAL_POW_EQ_1_IMP
  REAL_POW_LBOUND := Session.REAL_POW_LBOUND
  REAL_POW_LE := Session.REAL_POW_LE
  REAL_POW_LE2 := Session.REAL_POW_LE2
  REAL_POW_LT := Session.REAL_POW_LT
  REAL_POW_POW := Session.REAL_POW_POW
  REAL_SUB_LT := Session.REAL_SUB_LT
  REAL_ZPOW_0 := Session.REAL_ZPOW_0
  REAL_ZPOW_ADD := Session.REAL_ZPOW_ADD
  REAL_ZPOW_EQ_0 := Session.REAL_ZPOW_EQ_0
  REAL_ZPOW_LE := Session.REAL_ZPOW_LE
  REAL_ZPOW_MONO := Session.REAL_ZPOW_MONO
  REAL_ZPOW_MONO_LT := Session.REAL_ZPOW_MONO_LT
  REAL_ZPOW_NUM := Session.REAL_ZPOW_NUM
  REAL_ZPOW_POW := Session.REAL_ZPOW_POW
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_BINOMIAL_THEOREM := SessionLibrary.RingTheory.«RING_BINOMIAL_THEOREM»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_INV_0 := SessionLibrary.RingTheory.«RING_INV_0»
  RING_MONOMORPHISM_EQ_0 := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EQ_0»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LNEG := SessionLibrary.RingTheory.«RING_MUL_LNEG»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RNEG := SessionLibrary.RingTheory.«RING_MUL_RNEG»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_NEG_NEG := SessionLibrary.RingTheory.«RING_NEG_NEG»
  RING_NEG_SUB := SessionLibrary.RingTheory.«RING_NEG_SUB»
  RING_OF_INT_CASES := SessionLibrary.RingTheory.«RING_OF_INT_CASES»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_INT_REM := SessionLibrary.RingTheory.«RING_OF_INT_REM»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_CLAUSES := SessionLibrary.RingTheory.«RING_SUM_CLAUSES»
  SING_SUBSET := Session.SING_SUBSET
  SQRT_1 := Session.SQRT_1
  SQRT_MONO_LT := Session.SQRT_MONO_LT
  SQRT_POW_2 := Session.SQRT_POW_2
  SUBSET := Session.SUBSET
  SUB_0 := Session.SUB_0
  SUM_CLAUSES := Session.SUM_CLAUSES
  SUM_CONST_NUMSEG := Session.SUM_CONST_NUMSEG
  SUM_LE_NUMSEG := Session.SUM_LE_NUMSEG
  VALUATION_SUBRING_INTEGRAL_ELEMENT := SessionANT.ValuationRing.«VALUATION_SUBRING_INTEGRAL_ELEMENT»
  VALUATION_SUBRING_MAXIMAL_IDEAL := SessionANT.ValuationRing.«VALUATION_SUBRING_MAXIMAL_IDEAL»
  field_of_fractions := SessionLibrary.RingTheory.«field_of_fractions»
  real_div := Session.real_div
  real_pow := Session.real_pow
  ring_div := SessionLibrary.RingTheory.«ring_div»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_of_num := SessionLibrary.RingTheory.«ring_of_num»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_sub := SessionLibrary.RingTheory.«ring_sub»
  subring_of := SessionLibrary.RingTheory.«subring_of»
  valuation_subring := SessionANT.ValuationRing.«valuation_subring»

/-- What dedekind_absolute.ml uses from Session. -/
def deps : HolANT.DedekindAbsolute.DedekindAbsoluteDeps where
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

/- The bundles, in dedekind_absolute.ml order. -/
initialize BDedekindAbsolute : HolANT.DedekindAbsolute.DedekindAbsolute ←
  ioB "setupDedekindAbsolute" (HolANT.DedekindAbsolute.setupDedekindAbsolute deps).run

-- DedekindAbsolute
def absolute_value : thm := BDedekindAbsolute.absolute_value
def nonarchimedean_absolute_value : thm := BDedekindAbsolute.nonarchimedean_absolute_value
def NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE : thm := BDedekindAbsolute.NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE
def NONARCHIMEDEAN_ABSOLUTE_VALUE : thm := BDedekindAbsolute.NONARCHIMEDEAN_ABSOLUTE_VALUE
def ABSOLUTE_VALUE_POS : thm := BDedekindAbsolute.ABSOLUTE_VALUE_POS
def ABSOLUTE_VALUE_EQ_0 : thm := BDedekindAbsolute.ABSOLUTE_VALUE_EQ_0
def ABSOLUTE_VALUE_POS_LT : thm := BDedekindAbsolute.ABSOLUTE_VALUE_POS_LT
def ABSOLUTE_VALUE_0 : thm := BDedekindAbsolute.ABSOLUTE_VALUE_0
def ABSOLUTE_VALUE_MUL : thm := BDedekindAbsolute.ABSOLUTE_VALUE_MUL
def ABSOLUTE_VALUE_TRIANGLE : thm := BDedekindAbsolute.ABSOLUTE_VALUE_TRIANGLE
def ABSOLUTE_VALUE_1 : thm := BDedekindAbsolute.ABSOLUTE_VALUE_1
def ABSOLUTE_VALUE_NEG : thm := BDedekindAbsolute.ABSOLUTE_VALUE_NEG
def ABSOLUTE_VALUE_SUB : thm := BDedekindAbsolute.ABSOLUTE_VALUE_SUB
def ABSOLUTE_VALUE_SUB_LE : thm := BDedekindAbsolute.ABSOLUTE_VALUE_SUB_LE
def ABSOLUTE_VALUE_ABS_SUB_LE : thm := BDedekindAbsolute.ABSOLUTE_VALUE_ABS_SUB_LE
def ABSOLUTE_VALUE_POW : thm := BDedekindAbsolute.ABSOLUTE_VALUE_POW
def ABSOLUTE_VALUE_INV : thm := BDedekindAbsolute.ABSOLUTE_VALUE_INV
def ABSOLUTE_VALUE_DIV : thm := BDedekindAbsolute.ABSOLUTE_VALUE_DIV
def ABSOLUTE_VALUE_RING_SUM : thm := BDedekindAbsolute.ABSOLUTE_VALUE_RING_SUM
def ABSOLUTE_VALUE_RING_OF_NUM_LE : thm := BDedekindAbsolute.ABSOLUTE_VALUE_RING_OF_NUM_LE
def ABSOLUTE_VALUE_EQ : thm := BDedekindAbsolute.ABSOLUTE_VALUE_EQ
def ABSOLUTE_VALUE_NONTRIVIAL : thm := BDedekindAbsolute.ABSOLUTE_VALUE_NONTRIVIAL
def NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_NUM : thm := BDedekindAbsolute.NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_NUM
def NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INT : thm := BDedekindAbsolute.NONARCHIMEDEAN_ABSOLUTE_VALUE_RING_OF_INT
def REAL_POW_EVENTUALLY_GT_LINEAR : thm := BDedekindAbsolute.REAL_POW_EVENTUALLY_GT_LINEAR
def NONARCHIMEDEAN_ABSOLUTE_VALUE_BOUNDED : thm := BDedekindAbsolute.NONARCHIMEDEAN_ABSOLUTE_VALUE_BOUNDED
def NONARCHIMEDEAN_ABSOLUTE_VALUE_CHAR : thm := BDedekindAbsolute.NONARCHIMEDEAN_ABSOLUTE_VALUE_CHAR
def ABSOLUTE_VALUE_FINITE : thm := BDedekindAbsolute.ABSOLUTE_VALUE_FINITE
def NONARCHIMEDEAN_ABSOLUTE_VALUE_VALUATION_SUBRING : thm := BDedekindAbsolute.NONARCHIMEDEAN_ABSOLUTE_VALUE_VALUATION_SUBRING
def NONARCHIMEDEAN_ABSOLUTE_VALUE_INTEGRAL : thm := BDedekindAbsolute.NONARCHIMEDEAN_ABSOLUTE_VALUE_INTEGRAL
def DEDEKIND_VALUATION_ABSOLUTE_VALUE : thm := BDedekindAbsolute.DEDEKIND_VALUATION_ABSOLUTE_VALUE
def DEDEKIND_VALUATION_IDEAL_NORM : thm := BDedekindAbsolute.DEDEKIND_VALUATION_IDEAL_NORM
def DEDEKIND_VALUATION_NORMALIZED_ABSOLUTE_VALUE : thm := BDedekindAbsolute.DEDEKIND_VALUATION_NORMALIZED_ABSOLUTE_VALUE

/-- `needs "ANT/dedekind_absolute.ml"`: already done by importing this module. -/
def ensureDedekindAbsolute : IO Unit := pure ()

end SessionANT.DedekindAbsolute
