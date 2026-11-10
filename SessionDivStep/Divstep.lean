/- ---------------------------------------------------------------------- -/
/- Session wiring for Divstep/divstep.ml                                    . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionDivStep/Divstep.lean

  The session half of the divstep.ml translation: it supplies HolDivStep.Divstep's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Divstep/divstep.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolDivStep.Divstep
import SessionLibrary.Iter
import SessionLibrary.Integer

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionDivStep.Divstep

/-- The core theorems divstep.ml uses. -/
def core1 : HolDivStep.Divstep.CoreThms1 where
  ADD_SYM := Session.ADD_SYM
  ARITH_EQ := Session.ARITH_EQ
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  IMP_CONJ := Session.IMP_CONJ
  INT_ADD_LID := Session.INT_ADD_LID
  INT_ADD_REM := Session.INT_ADD_REM
  INT_DIVISION_SIMP := Session.INT_DIVISION_SIMP
  INT_DIV_LT_EQ := Session.INT_DIV_LT_EQ
  INT_DIV_ZERO := Session.INT_DIV_ZERO
  INT_GCD_EQ := SessionLibrary.Integer.«INT_GCD_EQ»
  INT_LE_DIV_EQ := Session.INT_LE_DIV_EQ
  INT_LT_DIV_EQ := Session.INT_LT_DIV_EQ
  INT_MUL_DIV_EQ := Session.INT_MUL_DIV_EQ
  INT_MUL_LID := Session.INT_MUL_LID
  INT_MUL_LZERO := Session.INT_MUL_LZERO
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_REM_2_CASES := Session.INT_REM_2_CASES
  INT_REM_EQ_0 := Session.INT_REM_EQ_0
  INT_REM_LNEG := Session.INT_REM_LNEG
  INT_REM_ZERO := Session.INT_REM_ZERO
  INT_SUB_REM := Session.INT_SUB_REM
  ITER_ADD := SessionLibrary.Iter.«ITER_ADD»
  ITER_ALT := SessionLibrary.Iter.«ITER_ALT»
  LEFT_AND_EXISTS_THM := Session.LEFT_AND_EXISTS_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_EXISTS := Session.LE_EXISTS
  LE_REFL := Session.LE_REFL
  PAIR := Session.PAIR
  PAIR_EQ := Session.PAIR_EQ
  o_THM := Session.o_THM

/-- What divstep.ml uses from Session. -/
def deps : HolDivStep.Divstep.DivstepDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
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
  LET_TAC := Session.LET_TAC
  basic_ss := Session.basic_ss
  NUM_SUB_CONV := Session.NUM_SUB_CONV
  REAL_RAT_REDUCE_CONV := Session.REAL_RAT_REDUCE_CONV
  NUM_EQ_CONV := Session.NUM_EQ_CONV
  NUM_DIV_CONV := Session.NUM_DIV_CONV
  EXP_MOD_CONV := Session.EXP_MOD_CONV
  EXPAND_CASES_CONV := Session.EXPAND_CASES_CONV
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in divstep.ml order. -/
initialize BDivstepThms : HolDivStep.Divstep.DivstepThms ←
  ioB "setupDivstepThms" (HolDivStep.Divstep.setupDivstepThms deps).run

-- DivstepThms
def divstep : thm := BDivstepThms.divstep
def divstep1 : thm := BDivstepThms.divstep1
def divstep2 : thm := BDivstepThms.divstep2
def DIVSTEP1_DIVSTEP2 : thm := BDivstepThms.DIVSTEP1_DIVSTEP2
def DIVSTEP_STAYS_ODD : thm := BDivstepThms.DIVSTEP_STAYS_ODD
def DIVSTEP_STAYS_ZERO : thm := BDivstepThms.DIVSTEP_STAYS_ZERO
def DIVSTEP_MAINTAINS_GCD : thm := BDivstepThms.DIVSTEP_MAINTAINS_GCD
def DIVSTEP_RANGE_2SCOMPLEMENT : thm := BDivstepThms.DIVSTEP_RANGE_2SCOMPLEMENT
def DIVSTEP_RANGE_SIGNMAGNITUDE : thm := BDivstepThms.DIVSTEP_RANGE_SIGNMAGNITUDE
def ITER_DIVSTEP_ODD : thm := BDivstepThms.ITER_DIVSTEP_ODD
def ITER_DIVSTEP_ZERO : thm := BDivstepThms.ITER_DIVSTEP_ZERO
def ITER_DIVSTEP_GCD : thm := BDivstepThms.ITER_DIVSTEP_GCD
def ITER_DIVSTEP_BOUND_ALT : thm := BDivstepThms.ITER_DIVSTEP_BOUND_ALT

/-- `needs "Divstep/divstep.ml"`: already done by importing this module. -/
def ensureDivstep : IO Unit := pure ()

end SessionDivStep.Divstep
