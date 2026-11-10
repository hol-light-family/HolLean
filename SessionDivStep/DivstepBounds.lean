/- ---------------------------------------------------------------------- -/
/- Session wiring for Divstep/divstep_bounds.ml                             . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionDivStep/DivstepBounds.lean

  The session half of the divstep_bounds.ml translation: it supplies HolDivStep.DivstepBounds's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Divstep/divstep_bounds.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolDivStep.DivstepBounds
import SessionLibrary.Iter
import SessionLibrary.Integer
import SessionLibrary.Floor
import SessionDivStep.Divstep
import SessionDivStep.IDivstep
import SessionDivStep.HullLight

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionDivStep.DivstepBounds

/-- The core theorems divstep_bounds.ml uses. -/
def core1 : HolDivStep.DivstepBounds.CoreThms1 where
  ADD1 := Session.ADD1
  COND_SWAP := Session.COND_SWAP
  CONJ_ASSOC := Session.CONJ_ASSOC
  DIVSTEP_FG_GCD := SessionDivStep.IDivstep.«DIVSTEP_FG_GCD»
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  IMP_IMP := Session.IMP_IMP
  INTEGER_CLOSED := SessionLibrary.Floor.«INTEGER_CLOSED»
  INTEGER_REAL_OF_INT := Session.INTEGER_REAL_OF_INT
  INT_2_DIVIDES_ADD := Session.INT_2_DIVIDES_ADD
  INT_2_DIVIDES_SUB := Session.INT_2_DIVIDES_SUB
  INT_ADD_RID := Session.INT_ADD_RID
  INT_GCD_0 := SessionLibrary.Integer.«INT_GCD_0»
  INT_MUL_DIV_EQ := Session.INT_MUL_DIV_EQ
  INT_MUL_LID := Session.INT_MUL_LID
  INT_MUL_LZERO := Session.INT_MUL_LZERO
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_REM_2_CASES := Session.INT_REM_2_CASES
  INT_REM_2_DIVIDES := Session.INT_REM_2_DIVIDES
  ITER := SessionLibrary.Iter.«ITER»
  ITER_DIVSTEP_BOUND_ALT := SessionDivStep.Divstep.«ITER_DIVSTEP_BOUND_ALT»
  ITER_DIVSTEP_INTEGER := SessionDivStep.IDivstep.«ITER_DIVSTEP_INTEGER»
  ITER_DIVSTEP_ODD := SessionDivStep.Divstep.«ITER_DIVSTEP_ODD»
  PAIR := Session.PAIR
  REAL_LT_INTEGERS := SessionLibrary.Floor.«REAL_LT_INTEGERS»
  REAL_OF_INT_CLAUSES := Session.REAL_OF_INT_CLAUSES
  REAL_OF_INT_OF_REAL := SessionLibrary.Floor.«REAL_OF_INT_OF_REAL»
  REAL_SUB_0 := Session.REAL_SUB_0
  REAL_SUB_REFL := Session.REAL_SUB_REFL
  divstep := SessionDivStep.Divstep.«divstep»
  divsteps_s := SessionDivStep.HullLight.«divsteps_s»
  endtoend_bits_simple := SessionDivStep.HullLight.«endtoend_bits_simple»
  int_eq := Session.int_eq
  int_of_num_th := Session.int_of_num_th

/-- What divstep_bounds.ml uses from Session. -/
def deps : HolDivStep.DivstepBounds.DivstepBoundsDeps where
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

/- The bundles, in divstep_bounds.ml order. -/
initialize BDivstepBoundsThms : HolDivStep.DivstepBounds.DivstepBoundsThms ←
  ioB "setupDivstepBoundsThms" (HolDivStep.DivstepBounds.setupDivstepBoundsThms deps).run

-- DivstepBoundsThms
def INTEGER_DIVSTEP_DELTA : thm := BDivstepBoundsThms.INTEGER_DIVSTEP_DELTA
def ITER_DIVSTEP_ODD_ALT : thm := BDivstepBoundsThms.ITER_DIVSTEP_ODD_ALT
def DIVSTEP_ENDTOEND_BITS_SIMPLE : thm := BDivstepBoundsThms.DIVSTEP_ENDTOEND_BITS_SIMPLE
def IDIVSTEP_ENDTOEND_BITS_SIMPLE : thm := BDivstepBoundsThms.IDIVSTEP_ENDTOEND_BITS_SIMPLE

/-- `needs "Divstep/divstep_bounds.ml"`: already done by importing this module. -/
def ensureDivstepBounds : IO Unit := pure ()

end SessionDivStep.DivstepBounds
