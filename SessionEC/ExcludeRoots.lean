/- ---------------------------------------------------------------------- -/
/- Session wiring for EC/excluderoots.ml                               . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionEC/ExcludeRoots.lean

  The session half of the excluderoots.ml translation: it supplies HolEC.ExcludeRoots's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "EC/excluderoots.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolEC.ExcludeRoots
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionEC.ExcludeRoots

/-- The core theorems excluderoots.ml uses. -/
def core1 : HolEC.ExcludeRoots.CoreThms1 where
  CONG := Session.CONG
  COPRIME_SYM := SessionLibrary.Prime.«COPRIME_SYM»
  DIVIDES_LE := Session.DIVIDES_LE
  EXP := Session.EXP
  FERMAT_LITTLE_PRIME := SessionLibrary.Pocklington.«FERMAT_LITTLE_PRIME»
  IMP_CONJ := Session.IMP_CONJ
  INT_CONG_RREM := Session.INT_CONG_RREM
  INT_FORALL_POS := Session.INT_FORALL_POS
  INT_LT_REM_EQ := Session.INT_LT_REM_EQ
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_OF_NUM_POW := Session.INT_OF_NUM_POW
  INT_OF_NUM_REM := Session.INT_OF_NUM_REM
  INT_POW_ADD := Session.INT_POW_ADD
  INT_POW_REM := Session.INT_POW_REM
  INT_REM_EQ := Session.INT_REM_EQ
  INT_REM_MOD_SELF := Session.INT_REM_MOD_SELF
  INT_REM_POS_EQ := Session.INT_REM_POS_EQ
  LE_1 := Session.LE_1
  MOD_LT := Session.MOD_LT
  MULT_2 := Session.MULT_2
  PRIME_COPRIME_EQ := SessionLibrary.Prime.«PRIME_COPRIME_EQ»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  num_coprime := Session.num_coprime

/-- What excluderoots.ml uses from Session. -/
def deps : HolEC.ExcludeRoots.ExcludeRootsDeps where
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
  LET_TAC := Session.LET_TAC
  basic_ss := Session.basic_ss
  mk_intconst := Session.mk_intconst
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in excluderoots.ml order. -/
initialize BExcludeRootsRules : HolEC.ExcludeRoots.ExcludeRootsRules ←
  ioB "setupExcludeRootsRules" (HolEC.ExcludeRoots.setupExcludeRootsRules deps).run

-- ExcludeRootsRules
def EXCLUDE_MODULAR_CUBIC_ROOTS : term → thm → ExceptT String IO thm := BExcludeRootsRules.EXCLUDE_MODULAR_CUBIC_ROOTS
def EXCLUDE_MODULAR_CUBIC_ROOTS_TAC : thm → List thm → ExceptT String IO HolCore.Tactics.tactic := BExcludeRootsRules.EXCLUDE_MODULAR_CUBIC_ROOTS_TAC

/-- `needs "EC/excluderoots.ml"`: already done by importing this module. -/
def ensureExcludeRoots : IO Unit := pure ()

end SessionEC.ExcludeRoots
