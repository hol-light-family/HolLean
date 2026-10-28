/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/iter.ml.                                    -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Iter.lean

  The session half of the iter.ml translation: it supplies
  HolLibrary.Iter's dependencies from Session and exports every name under
  its HOL Light name.  Importing this module is `needs "Library/iter.ml"`:
  the bundle is built by `initialize` when the module is loaded.
-/

import Session
import HolLibrary.Iter

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Iter

/-- The core theorems iter.ml uses. -/
def core1 : HolLibrary.Iter.CoreThms1 where
  ADD := Session.ADD
  ADD_AC := Session.ADD_AC
  ADD_SYM := Session.ADD_SYM
  CARD_IMAGE_EQ_INJ := Session.CARD_IMAGE_EQ_INJ
  CARD_NUMSEG := Session.CARD_NUMSEG
  CARD_SUBSET := Session.CARD_SUBSET
  DIVIDES_LE := Session.DIVIDES_LE
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FUN_EQ_THM := Session.FUN_EQ_THM
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  IN_NUMSEG := Session.IN_NUMSEG
  I_THM := Session.I_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_1 := Session.LE_1
  LE_REFL := Session.LE_REFL
  MONO_EXISTS := Session.MONO_EXISTS
  MULT := Session.MULT
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_LT := Session.NOT_LT
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  SUB_0 := Session.SUB_0
  SUB_REFL := Session.SUB_REFL
  WLOG_LT := Session.WLOG_LT
  num_WF := Session.num_WF
  num_WOP := Session.num_WOP
  o_THM := Session.o_THM

/-- What iter.ml uses from Session. -/
def deps : HolLibrary.Iter.IterDeps where
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  num_CONV := Session.num_CONV
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  ASM_SIMP_TAC := Session.ASM_SIMP_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  NUMBER_RULE t := ExceptT.mk (Session.NUMBER_RULE t)
  SET_TAC := Session.SET_TAC
  core1 := core1

/-- iter.ml, run when this module is loaded. -/
initialize BIter : HolLibrary.Iter.Iter ← do
  match ← (HolLibrary.Iter.setupIter deps).run with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"setupIter failed: {e}")

-- Iter
def ITER : thm := BIter.ITER
def ITER_POINTLESS : thm := BIter.ITER_POINTLESS
def ITER_ALT : thm := BIter.ITER_ALT
def ITER_ALT_POINTLESS : thm := BIter.ITER_ALT_POINTLESS
def ITER_1 : thm := BIter.ITER_1
def ITER_ADD : thm := BIter.ITER_ADD
def ITER_ADD_POINTLESS : thm := BIter.ITER_ADD_POINTLESS
def ITER_MUL : thm := BIter.ITER_MUL
def ITER_FIXPOINT : thm := BIter.ITER_FIXPOINT
def ORDER_EXISTENCE_GEN : thm := BIter.ORDER_EXISTENCE_GEN
def ORDER_EXISTENCE_ITER : thm := BIter.ORDER_EXISTENCE_ITER
def ORDER_EXISTENCE_CARD : thm := BIter.ORDER_EXISTENCE_CARD
def ORDER_EXISTENCE_FINITE : thm := BIter.ORDER_EXISTENCE_FINITE

/-- `needs "Library/iter.ml"`: already done by importing this module. -/
def ensureIter : IO Unit := pure ()

end SessionLibrary.Iter
