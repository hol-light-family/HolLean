/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/algmisc.ml                                    . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/Algmisc.lean

  The session half of the algmisc.ml translation: it supplies HolANT.Algmisc's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/algmisc.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.Algmisc
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Products

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.Algmisc

/-- The core theorems algmisc.ml uses. -/
def core1 : HolANT.Algmisc.CoreThms1 where
  EXP_1 := Session.EXP_1
  EXP_ZERO := Session.EXP_ZERO
  EXTENSION := Session.EXTENSION
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  HAS_SIZE_IMAGE_INJ := Session.HAS_SIZE_IMAGE_INJ
  HAS_SIZE_NUMSEG_LT := Session.HAS_SIZE_NUMSEG_LT
  INT_ABS_POS := Session.INT_ABS_POS
  INT_DIVIDES_ABS := Session.INT_DIVIDES_ABS
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_OF_NUM_POW := Session.INT_OF_NUM_POW
  INT_POS := Session.INT_POS
  INT_POW_LE := Session.INT_POW_LE
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  LE_0 := Session.LE_0
  LE_EXP := Session.LE_EXP
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  num_MAX := Session.num_MAX
  num_divides := Session.num_divides

/-- What algmisc.ml uses from Session. -/
def deps : HolANT.Algmisc.AlgmiscDeps where
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

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in algmisc.ml order. -/
initialize BAlgmisc : HolANT.Algmisc.Algmisc ←
  ioB "setupAlgmisc" (HolANT.Algmisc.setupAlgmisc deps).run

-- Algmisc
def UPPER_BOUND_FINITE_SET_INT : thm := BAlgmisc.UPPER_BOUND_FINITE_SET_INT
def HAS_SIZE_INT_SEG_LT : thm := BAlgmisc.HAS_SIZE_INT_SEG_LT
def NUM_ROOT_FLOOR : thm := BAlgmisc.NUM_ROOT_FLOOR
def INT_DIVIDES_NUM_OF_INT_ABS : thm := BAlgmisc.INT_DIVIDES_NUM_OF_INT_ABS
def NUM_OF_INT_ABS_POW : thm := BAlgmisc.NUM_OF_INT_ABS_POW
def FORALL_LT_2 : thm := BAlgmisc.FORALL_LT_2

/-- `needs "ANT/algmisc.ml"`: already done by importing this module. -/
def ensureAlgmisc : IO Unit := pure ()

end SessionANT.Algmisc
