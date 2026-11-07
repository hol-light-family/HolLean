/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/integer.ml.                           -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Integer.lean

  The session half of the integer.ml translation: it supplies
  HolLibrary.Integer's dependencies from Session and exports every name
  under its HOL Light name.  Importing this module is
  `needs "Library/integer.ml"` (integer.ml has no `needs`): the bundles are
  built by `initialize` when the module is loaded, in file order.
-/

import Session
import HolLibrary.Integer

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Integer

/-- The core theorems integer.ml uses. -/
def core1 : HolLibrary.Integer.CoreThms1 where
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DISJ_ACI := Session.DISJ_ACI
  EQ_ADD_RCANCEL_0 := Session.EQ_ADD_RCANCEL_0
  EXISTS_OR_THM := Session.EXISTS_OR_THM
  FACT := Session.FACT
  FACT_NZ := Session.FACT_NZ
  FINITE_IMAGE_INJ := Session.FINITE_IMAGE_INJ
  INFINITE := Session.INFINITE
  INT_ABS := Session.INT_ABS
  INT_ABS_ABS := Session.INT_ABS_ABS
  INT_ABS_MUL := Session.INT_ABS_MUL
  INT_ABS_MUL_1 := Session.INT_ABS_MUL_1
  INT_ABS_NEG := Session.INT_ABS_NEG
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_ABS_POS := Session.INT_ABS_POS
  INT_ABS_POW := Session.INT_ABS_POW
  INT_ABS_ZERO := Session.INT_ABS_ZERO
  INT_CONG_DIV2 := Session.INT_CONG_DIV2
  INT_CONG_RREM := Session.INT_CONG_RREM
  INT_DIVIDES_ABS := Session.INT_DIVIDES_ABS
  INT_DIVIDES_LABS := Session.INT_DIVIDES_LABS
  INT_DIVIDES_LCM_GCD := Session.INT_DIVIDES_LCM_GCD
  INT_DIVIDES_RABS := Session.INT_DIVIDES_RABS
  INT_DIV_1 := Session.INT_DIV_1
  INT_DIV_MUL := Session.INT_DIV_MUL
  INT_ENTIRE := Session.INT_ENTIRE
  INT_EQ_MUL_LCANCEL := Session.INT_EQ_MUL_LCANCEL
  INT_EXISTS_POS := Session.INT_EXISTS_POS
  INT_GT := Session.INT_GT
  INT_IMAGE := Session.INT_IMAGE
  INT_LCM_DIVIDES := Session.INT_LCM_DIVIDES
  INT_LCM_POS := Session.INT_LCM_POS
  INT_LE_LMUL := Session.INT_LE_LMUL
  INT_LE_MUL := Session.INT_LE_MUL
  INT_LT_LE := Session.INT_LT_LE
  INT_LT_MUL := Session.INT_LT_MUL
  INT_MUL_AC := Session.INT_MUL_AC
  INT_MUL_LCM_GCD := Session.INT_MUL_LCM_GCD
  INT_MUL_LID := Session.INT_MUL_LID
  INT_MUL_LNEG := Session.INT_MUL_LNEG
  INT_MUL_LZERO := Session.INT_MUL_LZERO
  INT_MUL_RID := Session.INT_MUL_RID
  INT_MUL_RNEG := Session.INT_MUL_RNEG
  INT_MUL_RZERO := Session.INT_MUL_RZERO
  INT_MUL_SYM := Session.INT_MUL_SYM
  INT_NEG_EQ_0 := Session.INT_NEG_EQ_0
  INT_NEG_NEG := Session.INT_NEG_NEG
  INT_NOT_LE := Session.INT_NOT_LE
  INT_OF_NUM_ADD := Session.INT_OF_NUM_ADD
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  INT_OF_NUM_SUC := Session.INT_OF_NUM_SUC
  INT_POS := Session.INT_POS
  INT_POW := Session.INT_POW
  INT_POW_ADD := Session.INT_POW_ADD
  INT_POW_EQ_0 := Session.INT_POW_EQ_0
  INT_POW_MONO_LT := Session.INT_POW_MONO_LT
  INT_POW_MUL := Session.INT_POW_MUL
  INT_POW_NEG := Session.INT_POW_NEG
  INT_POW_ONE := Session.INT_POW_ONE
  INT_POW_ZERO := Session.INT_POW_ZERO
  INT_SUB_0 := Session.INT_SUB_0
  IN_ELIM_THM := Session.IN_ELIM_THM
  LEFT_EXISTS_AND_THM := Session.LEFT_EXISTS_AND_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_EXISTS := Session.LE_EXISTS
  MONO_AND := Session.MONO_AND
/-- The core theorems integer.ml uses. -/
def core2 : HolLibrary.Integer.CoreThms2 where
  MONO_EXISTS := Session.MONO_EXISTS
  MONO_FORALL := Session.MONO_FORALL
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_LE := Session.NOT_LE
  NOT_ODD := Session.NOT_ODD
  NOT_SUC := Session.NOT_SUC
  OR_EXISTS_THM := Session.OR_EXISTS_THM
  RIGHT_EXISTS_AND_THM := Session.RIGHT_EXISTS_AND_THM
  RIGHT_OR_DISTRIB := Session.RIGHT_OR_DISTRIB
  SWAP_FORALL_THM := Session.SWAP_FORALL_THM
  UNWIND_THM2 := Session.UNWIND_THM2
  WF_INT_MEASURE := Session.WF_INT_MEASURE
  int_congruent := Session.int_congruent
  int_divides := Session.int_divides
  int_gcd := Session.int_gcd
  int_lcm := Session.int_lcm
  num_FINITE := Session.num_FINITE
/-- The core theorems integer.ml uses. -/
def core3 : HolLibrary.Integer.CoreThms3 where
/-- The core theorems integer.ml uses. -/
def core4 : HolLibrary.Integer.CoreThms4 where

/-- What integer.ml uses from Session. -/
def deps : HolLibrary.Integer.IntegerDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  prioritize_int := do
    match ← HolCore.Kernel.mk_type "int" [] with
    | .ok ty => Session.prioritize_overload ty
    | .error e => throw (IO.userError e)
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  INT_ARITH t := ExceptT.mk (Session.INT_ARITH t)
  INT_ARITH_TAC := Session.INT_ARITH_TAC
  ASM_INT_ARITH_TAC := Session.ASM_INT_ARITH_TAC
  INTEGER_RULE t := ExceptT.mk (Session.INTEGER_RULE t)
  INTEGER_TAC := Session.INTEGER_TAC
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  INT_RING t := ExceptT.mk (Session.INT_RING t)
  INT_REDUCE_CONV := Session.INT_REDUCE_CONV
  METIS_TAC := Session.METIS_TAC
  core1 := core1
  core2 := core2
  core3 := core3
  core4 := core4

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in integer.ml order. -/
initialize BDivides : HolLibrary.Integer.Divides ←
  ioB "setupDivides" (HolLibrary.Integer.setupDivides deps).run
initialize BGcd : HolLibrary.Integer.Gcd ←
  ioB "setupGcd" (HolLibrary.Integer.setupGcd deps BDivides).run
initialize BLcm : HolLibrary.Integer.Lcm ←
  ioB "setupLcm" (HolLibrary.Integer.setupLcm deps BDivides BGcd).run
initialize BCoprime : HolLibrary.Integer.Coprime ←
  ioB "setupCoprime" (HolLibrary.Integer.setupCoprime deps BDivides BGcd BLcm).run
initialize BCong : HolLibrary.Integer.Cong ←
  ioB "setupCong" (HolLibrary.Integer.setupCong deps BDivides BGcd BCoprime).run
initialize BCrt : HolLibrary.Integer.Crt ←
  ioB "setupCrt" (HolLibrary.Integer.setupCrt deps).run
initialize BIntPrime : HolLibrary.Integer.IntPrime ←
  ioB "setupIntPrime" (HolLibrary.Integer.setupIntPrime deps BDivides BCrt).run
initialize BIntPrime2 : HolLibrary.Integer.IntPrime2 ←
  ioB "setupIntPrime2"
    (HolLibrary.Integer.setupIntPrime2 deps BDivides BGcd BCoprime BCrt BIntPrime).run

-- Divides
def INT_DIVIDES_REFL : thm := BDivides.INT_DIVIDES_REFL
def INT_DIVIDES_TRANS : thm := BDivides.INT_DIVIDES_TRANS
def INT_DIVIDES_ADD : thm := BDivides.INT_DIVIDES_ADD
def INT_DIVIDES_SUB : thm := BDivides.INT_DIVIDES_SUB
def INT_DIVIDES_0 : thm := BDivides.INT_DIVIDES_0
def INT_DIVIDES_ZERO : thm := BDivides.INT_DIVIDES_ZERO
def INT_DIVIDES_LNEG : thm := BDivides.INT_DIVIDES_LNEG
def INT_DIVIDES_RNEG : thm := BDivides.INT_DIVIDES_RNEG
def INT_DIVIDES_RMUL : thm := BDivides.INT_DIVIDES_RMUL
def INT_DIVIDES_LMUL : thm := BDivides.INT_DIVIDES_LMUL
def INT_DIVIDES_1 : thm := BDivides.INT_DIVIDES_1
def INT_DIVIDES_ADD_REVR : thm := BDivides.INT_DIVIDES_ADD_REVR
def INT_DIVIDES_ADD_REVL : thm := BDivides.INT_DIVIDES_ADD_REVL
def INT_DIVIDES_MUL_L : thm := BDivides.INT_DIVIDES_MUL_L
def INT_DIVIDES_MUL_R : thm := BDivides.INT_DIVIDES_MUL_R
def INT_DIVIDES_LMUL2 : thm := BDivides.INT_DIVIDES_LMUL2
def INT_DIVIDES_RMUL2 : thm := BDivides.INT_DIVIDES_RMUL2
def INT_DIVIDES_CMUL2 : thm := BDivides.INT_DIVIDES_CMUL2
def INT_DIVIDES_LMUL2_EQ : thm := BDivides.INT_DIVIDES_LMUL2_EQ
def INT_DIVIDES_RMUL2_EQ : thm := BDivides.INT_DIVIDES_RMUL2_EQ
def INT_DIVIDES_MUL2 : thm := BDivides.INT_DIVIDES_MUL2
def INT_DIVIDES_POW : thm := BDivides.INT_DIVIDES_POW
def INT_DIVIDES_POW2 : thm := BDivides.INT_DIVIDES_POW2
def INT_DIVIDES_RPOW : thm := BDivides.INT_DIVIDES_RPOW
def INT_DIVIDES_RPOW_SUC : thm := BDivides.INT_DIVIDES_RPOW_SUC
def INT_DIVIDES_POW_LE_IMP : thm := BDivides.INT_DIVIDES_POW_LE_IMP
def INT_DIVIDES_ANTISYM_DIVISORS : thm := BDivides.INT_DIVIDES_ANTISYM_DIVISORS
def INT_DIVIDES_ANTISYM_MULTIPLES : thm := BDivides.INT_DIVIDES_ANTISYM_MULTIPLES
def INT_DIVIDES_ONE_POS : thm := BDivides.INT_DIVIDES_ONE_POS
def INT_DIVIDES_ONE_ABS : thm := BDivides.INT_DIVIDES_ONE_ABS
def INT_DIVIDES_ONE : thm := BDivides.INT_DIVIDES_ONE
def INT_DIVIDES_ANTISYM_ASSOCIATED : thm := BDivides.INT_DIVIDES_ANTISYM_ASSOCIATED
def INT_DIVIDES_ANTISYM : thm := BDivides.INT_DIVIDES_ANTISYM
def INT_DIVIDES_ANTISYM_ABS : thm := BDivides.INT_DIVIDES_ANTISYM_ABS
def INT_DIVIDES_ANTISYM_POS : thm := BDivides.INT_DIVIDES_ANTISYM_POS

-- Gcd
def INT_GCD_POS : thm := BGcd.INT_GCD_POS
def INT_ABS_GCD : thm := BGcd.INT_ABS_GCD
def INT_GCD_DIVIDES : thm := BGcd.INT_GCD_DIVIDES
def INT_COPRIME_GCD : thm := BGcd.INT_COPRIME_GCD
def INT_GCD_BEZOUT : thm := BGcd.INT_GCD_BEZOUT
def INT_DIVIDES_GCD : thm := BGcd.INT_DIVIDES_GCD
def INT_GCD : thm := BGcd.INT_GCD
def INT_GCD_UNIQUE : thm := BGcd.INT_GCD_UNIQUE
def INT_GCD_UNIQUE_ABS : thm := BGcd.INT_GCD_UNIQUE_ABS
def INT_GCD_REFL : thm := BGcd.INT_GCD_REFL
def INT_GCD_SYM : thm := BGcd.INT_GCD_SYM
def INT_GCD_ASSOC : thm := BGcd.INT_GCD_ASSOC
def INT_GCD_1 : thm := BGcd.INT_GCD_1
def INT_GCD_0 : thm := BGcd.INT_GCD_0
def INT_GCD_EQ_0 : thm := BGcd.INT_GCD_EQ_0
def INT_GCD_ABS : thm := BGcd.INT_GCD_ABS
def INT_GCD_ADD : thm := BGcd.INT_GCD_ADD
def INT_GCD_SUB : thm := BGcd.INT_GCD_SUB
def INT_DIVIDES_GCD_LEFT : thm := BGcd.INT_DIVIDES_GCD_LEFT
def INT_DIVIDES_GCD_RIGHT : thm := BGcd.INT_DIVIDES_GCD_RIGHT
def INT_GCD_EQ : thm := BGcd.INT_GCD_EQ
def INT_GCD_LNEG : thm := BGcd.INT_GCD_LNEG
def INT_GCD_RNEG : thm := BGcd.INT_GCD_RNEG
def INT_GCD_NEG : thm := BGcd.INT_GCD_NEG
def INT_GCD_LABS : thm := BGcd.INT_GCD_LABS
def INT_GCD_RABS : thm := BGcd.INT_GCD_RABS
def INT_GCD_LMUL : thm := BGcd.INT_GCD_LMUL
def INT_GCD_RMUL : thm := BGcd.INT_GCD_RMUL
def INT_GCD_COPRIME_LMUL : thm := BGcd.INT_GCD_COPRIME_LMUL
def INT_GCD_COPRIME_RMUL : thm := BGcd.INT_GCD_COPRIME_RMUL
def INT_GCD_COPRIME_DIVIDES_LMUL : thm := BGcd.INT_GCD_COPRIME_DIVIDES_LMUL
def INT_GCD_COPRIME_DIVIDES_RMUL : thm := BGcd.INT_GCD_COPRIME_DIVIDES_RMUL
def INT_GCD_COPRIME_EXISTS : thm := BGcd.INT_GCD_COPRIME_EXISTS

-- Lcm
def INT_ABS_LCM : thm := BLcm.INT_ABS_LCM
def INT_LCM_EQ_0 : thm := BLcm.INT_LCM_EQ_0
def INT_DIVIDES_LCM : thm := BLcm.INT_DIVIDES_LCM
def INT_LCM_0 : thm := BLcm.INT_LCM_0
def INT_LCM_1 : thm := BLcm.INT_LCM_1
def INT_LCM_UNIQUE_ABS : thm := BLcm.INT_LCM_UNIQUE_ABS
def INT_LCM_UNIQUE : thm := BLcm.INT_LCM_UNIQUE
def INT_LCM_EQ : thm := BLcm.INT_LCM_EQ
def INT_LCM_REFL : thm := BLcm.INT_LCM_REFL
def INT_LCM_SYM : thm := BLcm.INT_LCM_SYM
def INT_LCM_ASSOC : thm := BLcm.INT_LCM_ASSOC
def INT_LCM_LNEG : thm := BLcm.INT_LCM_LNEG
def INT_LCM_RNEG : thm := BLcm.INT_LCM_RNEG
def INT_LCM_NEG : thm := BLcm.INT_LCM_NEG
def INT_LCM_LABS : thm := BLcm.INT_LCM_LABS
def INT_LCM_RABS : thm := BLcm.INT_LCM_RABS
def INT_LCM_ABS : thm := BLcm.INT_LCM_ABS
def INT_LCM_LMUL : thm := BLcm.INT_LCM_LMUL
def INT_LCM_RMUL : thm := BLcm.INT_LCM_RMUL

-- Coprime
def INT_COPRIME : thm := BCoprime.INT_COPRIME
def INT_COPRIME_ALT : thm := BCoprime.INT_COPRIME_ALT
def INT_COPRIME_SYM : thm := BCoprime.INT_COPRIME_SYM
def INT_COPRIME_DIVPROD : thm := BCoprime.INT_COPRIME_DIVPROD
def INT_COPRIME_1 : thm := BCoprime.INT_COPRIME_1
def INT_GCD_COPRIME : thm := BCoprime.INT_GCD_COPRIME
def INT_COPRIME_0 : thm := BCoprime.INT_COPRIME_0
def INT_COPRIME_MUL : thm := BCoprime.INT_COPRIME_MUL
def INT_COPRIME_LMUL2 : thm := BCoprime.INT_COPRIME_LMUL2
def INT_COPRIME_RMUL2 : thm := BCoprime.INT_COPRIME_RMUL2
def INT_COPRIME_LMUL : thm := BCoprime.INT_COPRIME_LMUL
def INT_COPRIME_RMUL : thm := BCoprime.INT_COPRIME_RMUL
def INT_COPRIME_REFL : thm := BCoprime.INT_COPRIME_REFL
def INT_COPRIME_PLUS1 : thm := BCoprime.INT_COPRIME_PLUS1
def INT_COPRIME_MINUS1 : thm := BCoprime.INT_COPRIME_MINUS1
def INT_COPRIME_RPOW : thm := BCoprime.INT_COPRIME_RPOW
def INT_COPRIME_LPOW : thm := BCoprime.INT_COPRIME_LPOW
def INT_COPRIME_POW2 : thm := BCoprime.INT_COPRIME_POW2
def INT_COPRIME_POW : thm := BCoprime.INT_COPRIME_POW
def INT_COPRIME_POW_IMP : thm := BCoprime.INT_COPRIME_POW_IMP
def INT_GCD_POW : thm := BCoprime.INT_GCD_POW
def INT_LCM_POW : thm := BCoprime.INT_LCM_POW
def INT_DIVISION_DECOMP : thm := BCoprime.INT_DIVISION_DECOMP
def INT_DIVIDES_MUL : thm := BCoprime.INT_DIVIDES_MUL
def INT_CHINESE_REMAINDER : thm := BCoprime.INT_CHINESE_REMAINDER
def INT_CHINESE_REMAINDER_USUAL : thm := BCoprime.INT_CHINESE_REMAINDER_USUAL
def INT_COPRIME_DIVISORS : thm := BCoprime.INT_COPRIME_DIVISORS
def INT_COPRIME_LNEG : thm := BCoprime.INT_COPRIME_LNEG
def INT_COPRIME_RNEG : thm := BCoprime.INT_COPRIME_RNEG
def INT_COPRIME_NEG : thm := BCoprime.INT_COPRIME_NEG
def INT_COPRIME_LABS : thm := BCoprime.INT_COPRIME_LABS
def INT_COPRIME_RABS : thm := BCoprime.INT_COPRIME_RABS
def INT_COPRIME_ABS : thm := BCoprime.INT_COPRIME_ABS

-- Cong
def INT_CONG_MOD_0 : thm := BCong.INT_CONG_MOD_0
def INT_CONG_MOD_1 : thm := BCong.INT_CONG_MOD_1
def INT_CONG : thm := BCong.INT_CONG
def INT_CONG_MOD_ABS : thm := BCong.INT_CONG_MOD_ABS
def INT_CONG_MUL_LCANCEL : thm := BCong.INT_CONG_MUL_LCANCEL
def INT_CONG_MUL_RCANCEL : thm := BCong.INT_CONG_MUL_RCANCEL
def INT_CONG_MULT_LCANCEL_ALL : thm := BCong.INT_CONG_MULT_LCANCEL_ALL
def INT_CONG_LMUL : thm := BCong.INT_CONG_LMUL
def INT_CONG_RMUL : thm := BCong.INT_CONG_RMUL
def INT_CONG_REFL : thm := BCong.INT_CONG_REFL
def INT_EQ_IMP_CONG : thm := BCong.INT_EQ_IMP_CONG
def INT_CONG_SYM : thm := BCong.INT_CONG_SYM
def INT_CONG_TRANS : thm := BCong.INT_CONG_TRANS
def INT_CONG_ADD : thm := BCong.INT_CONG_ADD
def INT_CONG_SUB : thm := BCong.INT_CONG_SUB
def INT_CONG_MUL : thm := BCong.INT_CONG_MUL
def INT_CONG_POW : thm := BCong.INT_CONG_POW
def INT_CONG_MUL_1 : thm := BCong.INT_CONG_MUL_1
def INT_CONG_POW_1 : thm := BCong.INT_CONG_POW_1
def INT_CONG_MUL_LCANCEL_EQ : thm := BCong.INT_CONG_MUL_LCANCEL_EQ
def INT_CONG_MUL_RCANCEL_EQ : thm := BCong.INT_CONG_MUL_RCANCEL_EQ
def INT_CONG_ADD_LCANCEL_EQ : thm := BCong.INT_CONG_ADD_LCANCEL_EQ
def INT_CONG_ADD_RCANCEL_EQ : thm := BCong.INT_CONG_ADD_RCANCEL_EQ
def INT_CONG_ADD_RCANCEL : thm := BCong.INT_CONG_ADD_RCANCEL
def INT_CONG_ADD_LCANCEL : thm := BCong.INT_CONG_ADD_LCANCEL
def INT_CONG_ADD_LCANCEL_EQ_0 : thm := BCong.INT_CONG_ADD_LCANCEL_EQ_0
def INT_CONG_ADD_RCANCEL_EQ_0 : thm := BCong.INT_CONG_ADD_RCANCEL_EQ_0
def INT_CONG_INT_DIVIDES_MODULUS : thm := BCong.INT_CONG_INT_DIVIDES_MODULUS
def INT_CONG_0_DIVIDES : thm := BCong.INT_CONG_0_DIVIDES
def INT_CONG_1_DIVIDES : thm := BCong.INT_CONG_1_DIVIDES
def INT_CONG_DIVIDES : thm := BCong.INT_CONG_DIVIDES
def INT_CONG_COPRIME : thm := BCong.INT_CONG_COPRIME
def INT_COPRIME_RREM : thm := BCong.INT_COPRIME_RREM
def INT_COPRIME_LREM : thm := BCong.INT_COPRIME_LREM
def INT_CONG_GCD_RIGHT : thm := BCong.INT_CONG_GCD_RIGHT
def INT_CONG_GCD_LEFT : thm := BCong.INT_CONG_GCD_LEFT
def INT_CONG_TO_1 : thm := BCong.INT_CONG_TO_1
def INT_CONG_SOLVE : thm := BCong.INT_CONG_SOLVE
def INT_CONG_SOLVE_EQ : thm := BCong.INT_CONG_SOLVE_EQ
def INT_CONG_SOLVE_UNIQUE : thm := BCong.INT_CONG_SOLVE_UNIQUE
def INT_CONG_CHINESE : thm := BCong.INT_CONG_CHINESE
def INT_CHINESE_REMAINDER_COPRIME : thm := BCong.INT_CHINESE_REMAINDER_COPRIME
def INT_CHINESE_REMAINDER_COPRIME_UNIQUE : thm := BCong.INT_CHINESE_REMAINDER_COPRIME_UNIQUE
def SOLVABLE_GCD : thm := BCong.SOLVABLE_GCD
def INT_LINEAR_CONG_POS : thm := BCong.INT_LINEAR_CONG_POS
def INT_CONG_SOLVE_POS : thm := BCong.INT_CONG_SOLVE_POS
def INT_CONG_IMP_EQ : thm := BCong.INT_CONG_IMP_EQ
def INT_CONG_DIV : thm := BCong.INT_CONG_DIV
def INT_CONG_DIV_COPRIME : thm := BCong.INT_CONG_DIV_COPRIME

-- Crt
def INT_CRT_STRONG : thm := BCrt.INT_CRT_STRONG
def INT_CRT_STRONG_IFF : thm := BCrt.INT_CRT_STRONG_IFF
def EVEN_SQUARE_MOD4 : thm := BCrt.EVEN_SQUARE_MOD4
def ODD_SQUARE_MOD4 : thm := BCrt.ODD_SQUARE_MOD4
def INT_DIVIDES_LE : thm := BCrt.INT_DIVIDES_LE
def INT_DIVIDES_POW_LE : thm := BCrt.INT_DIVIDES_POW_LE

-- IntPrime
def int_prime : thm := BIntPrime.int_prime
def INT_PRIME_NEG : thm := BIntPrime.INT_PRIME_NEG
def INT_PRIME_ABS : thm := BIntPrime.INT_PRIME_ABS
def INT_PRIME_GE_2 : thm := BIntPrime.INT_PRIME_GE_2
def INT_PRIME_0 : thm := BIntPrime.INT_PRIME_0
def INT_PRIME_1 : thm := BIntPrime.INT_PRIME_1
def INT_PRIME_2 : thm := BIntPrime.INT_PRIME_2
def INT_PRIME_FACTOR : thm := BIntPrime.INT_PRIME_FACTOR
def INT_PRIME_FACTOR_LT : thm := BIntPrime.INT_PRIME_FACTOR_LT
def INT_PRIME_FACTOR_INDUCT : thm := BIntPrime.INT_PRIME_FACTOR_INDUCT

-- IntPrime2
def INT_DIVIDES_FACT : thm := BIntPrime2.INT_DIVIDES_FACT
def INT_EUCLID_BOUND : thm := BIntPrime2.INT_EUCLID_BOUND
def INT_EUCLID : thm := BIntPrime2.INT_EUCLID
def INT_PRIMES_INFINITE : thm := BIntPrime2.INT_PRIMES_INFINITE
def INT_COPRIME_PRIME : thm := BIntPrime2.INT_COPRIME_PRIME
def INT_COPRIME_PRIME_EQ : thm := BIntPrime2.INT_COPRIME_PRIME_EQ
def INT_PRIME_COPRIME : thm := BIntPrime2.INT_PRIME_COPRIME
def INT_PRIME_COPRIME_EQ : thm := BIntPrime2.INT_PRIME_COPRIME_EQ
def INT_COPRIME_PRIMEPOW : thm := BIntPrime2.INT_COPRIME_PRIMEPOW
def INT_COPRIME_BEZOUT : thm := BIntPrime2.INT_COPRIME_BEZOUT
def INT_COPRIME_BEZOUT_ALT : thm := BIntPrime2.INT_COPRIME_BEZOUT_ALT
def INT_BEZOUT_PRIME : thm := BIntPrime2.INT_BEZOUT_PRIME
def INT_PRIME_DIVPROD : thm := BIntPrime2.INT_PRIME_DIVPROD
def INT_PRIME_DIVPROD_EQ : thm := BIntPrime2.INT_PRIME_DIVPROD_EQ
def INT_PRIME_DIVPOW : thm := BIntPrime2.INT_PRIME_DIVPOW
def INT_PRIME_DIVPOW_N : thm := BIntPrime2.INT_PRIME_DIVPOW_N
def INT_COPRIME_SOS : thm := BIntPrime2.INT_COPRIME_SOS
def INT_PRIME_IMP_NZ : thm := BIntPrime2.INT_PRIME_IMP_NZ
def INT_DISTINCT_PRIME_COPRIME : thm := BIntPrime2.INT_DISTINCT_PRIME_COPRIME
def INT_PRIME_COPRIME_LT : thm := BIntPrime2.INT_PRIME_COPRIME_LT
def INT_DIVIDES_PRIME_PRIME : thm := BIntPrime2.INT_DIVIDES_PRIME_PRIME
def INT_COPRIME_POW_DIVPROD : thm := BIntPrime2.INT_COPRIME_POW_DIVPROD
def INT_PRIME_COPRIME_CASES : thm := BIntPrime2.INT_PRIME_COPRIME_CASES
def INT_PRIME_DIVPROD_POW : thm := BIntPrime2.INT_PRIME_DIVPROD_POW
def INT_DIVIDES_POW2_REV : thm := BIntPrime2.INT_DIVIDES_POW2_REV
def INT_DIVIDES_POW2_EQ : thm := BIntPrime2.INT_DIVIDES_POW2_EQ
def INT_POW_MUL_EXISTS : thm := BIntPrime2.INT_POW_MUL_EXISTS
def INT_COPRIME_POW_ABS : thm := BIntPrime2.INT_COPRIME_POW_ABS
def INT_COPRIME_POW_ODD : thm := BIntPrime2.INT_COPRIME_POW_ODD
def INT_DIVIDES_PRIME_POW_LE : thm := BIntPrime2.INT_DIVIDES_PRIME_POW_LE
def INT_EQ_PRIME_POW_ABS : thm := BIntPrime2.INT_EQ_PRIME_POW_ABS
def INT_EQ_PRIME_POW_POS : thm := BIntPrime2.INT_EQ_PRIME_POW_POS
def INT_DIVIDES_FACT_PRIME : thm := BIntPrime2.INT_DIVIDES_FACT_PRIME
/-- `needs "Library/integer.ml"`: already done by importing this module. -/
def ensureInteger : IO Unit := pure ()

end SessionLibrary.Integer
