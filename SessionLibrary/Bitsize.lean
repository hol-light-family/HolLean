/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/bitsize.ml.                                 -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Bitsize.lean

  The session half of the bitsize.ml translation: it supplies
  HolLibrary.Bitsize's dependencies from Session and exports every name
  under its HOL Light name.  Importing this module is
  `needs "Library/bitsize.ml"`: the bundle is built by `initialize` when the
  module is loaded.
-/

import Session
import HolLibrary.Bitsize

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Bitsize

/-- The core theorems bitsize.ml uses. -/
def core1 : HolLibrary.Bitsize.CoreThms1 where
  ADD_EQ_0 := Session.ADD_EQ_0
  ADD_SUB := Session.ADD_SUB
  ADD_SYM := Session.ADD_SYM
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  DISJ_SYM := Session.DISJ_SYM
  EQ_IMP_LE := Session.EQ_IMP_LE
  EXP := Session.EXP
  EXP_ADD := Session.EXP_ADD
  EXP_EQ_0 := Session.EXP_EQ_0
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  LET_TRANS := Session.LET_TRANS
  LE_0 := Session.LE_0
  LE_ANTISYM := Session.LE_ANTISYM
  LE_EXP := Session.LE_EXP
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  LE_RDIV_EQ := Session.LE_RDIV_EQ
  LE_REFL := Session.LE_REFL
  LE_TRANS := Session.LE_TRANS
  LT := Session.LT
  LTE_TRANS := Session.LTE_TRANS
  LT_ANTISYM := Session.LT_ANTISYM
  LT_CASES := Session.LT_CASES
  LT_EXP := Session.LT_EXP
  LT_MULT2 := Session.LT_MULT2
  LT_MULT_LCANCEL := Session.LT_MULT_LCANCEL
  LT_POW2_REFL := Session.LT_POW2_REFL
  LT_TRANS := Session.LT_TRANS
  MINIMAL_LE := Session.MINIMAL_LE
  MINIMAL_UNIQUE := Session.MINIMAL_UNIQUE
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_SYM := Session.MULT_SYM
  NOT_LE := Session.NOT_LE
  NOT_LT := Session.NOT_LT
  RDIV_LT_EQ := Session.RDIV_LT_EQ

/-- What bitsize.ml uses from Session. -/
def deps : HolLibrary.Bitsize.BitsizeDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  SIMP_TAC := Session.SIMP_TAC
  mk_small_numeral := Session.mk_small_numeral
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  core1 := core1

/-- bitsize.ml, run when this module is loaded. -/
initialize BBitsize : HolLibrary.Bitsize.Bitsize ← do
  match ← (HolLibrary.Bitsize.setupBitsize deps).run with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"setupBitsize failed: {e}")

-- Bitsize
def bitsize : thm := BBitsize.bitsize
def BITSIZE_0 : thm := BBitsize.BITSIZE_0
def BITSIZE_POW2 : thm := BBitsize.BITSIZE_POW2
def BITSIZE_1 : thm := BBitsize.BITSIZE_1
def BITSIZE_2 : thm := BBitsize.BITSIZE_2
def BITSIZE_LE : thm := BBitsize.BITSIZE_LE
def BITSIZE : thm := BBitsize.BITSIZE
def BITSIZE_UNIQUE : thm := BBitsize.BITSIZE_UNIQUE
def BITSIZE_UNIQUE_ALT : thm := BBitsize.BITSIZE_UNIQUE_ALT
def BITSIZE_EQ_0 : thm := BBitsize.BITSIZE_EQ_0
def BITSIZE_MONO : thm := BBitsize.BITSIZE_MONO
def BITSIZE_MAX : thm := BBitsize.BITSIZE_MAX
def BITSIZE_MIN : thm := BBitsize.BITSIZE_MIN
def BITSIZE_MULT_LE : thm := BBitsize.BITSIZE_MULT_LE
def BITSIZE_REV_EQ : thm := BBitsize.BITSIZE_REV_EQ
def BITSIZE_REV : thm := BBitsize.BITSIZE_REV
def BITSIZE_REV_EQ_ALT : thm := BBitsize.BITSIZE_REV_EQ_ALT
def BITSIZE_REV_ALT : thm := BBitsize.BITSIZE_REV_ALT
def LE_BITSIZE : thm := BBitsize.LE_BITSIZE
def LE_BITSIZE_ALT : thm := BBitsize.LE_BITSIZE_ALT
def BITSIZE_UNIQUE_EQ : thm := BBitsize.BITSIZE_UNIQUE_EQ
def BITSIZE_MULT : thm := BBitsize.BITSIZE_MULT
def BITSIZE_MULT_ADD : thm := BBitsize.BITSIZE_MULT_ADD
def BITSIZE_DIV : thm := BBitsize.BITSIZE_DIV
def BITSIZE_CONV : term → IO (Except String thm) := fun t => (BBitsize.BITSIZE_CONV t).run

/-- `needs "Library/bitsize.ml"`: already done by importing this module. -/
def ensureBitsize : IO Unit := pure ()

end SessionLibrary.Bitsize
