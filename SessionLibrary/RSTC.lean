/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/rstc.ml.                                    -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/RSTC.lean

  The session half of the rstc.ml translation: it supplies HolLibrary.RSTC's
  dependencies from Session and exports every name under its HOL Light name.
  Importing this module is `needs "Library/rstc.ml"`: each bundle is built
  by `initialize` when the module is loaded, in file order, after the whole
  of Session (so rstc.ml's `prioritize_num` applies only after hol_lib.ml,
  as in HOL Light).
-/

import Session
import HolLibrary.RSTC

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.RSTC

/-- The core theorems rstc.ml uses. -/
def core1 : HolLibrary.RSTC.CoreThms1 where
  ADD_CLAUSES := Session.«ADD_CLAUSES»
  ARITH := Session.«ARITH»
  DISJ_ACI := Session.«DISJ_ACI»
  DISJ_SYM := Session.«DISJ_SYM»
  EQ_SYM_EQ := Session.«EQ_SYM_EQ»
  FUN_EQ_THM := Session.«FUN_EQ_THM»
  IMP_IMP := Session.«IMP_IMP»
  LEFT_EXISTS_AND_THM := Session.«LEFT_EXISTS_AND_THM»
  LEFT_IMP_EXISTS_THM := Session.«LEFT_IMP_EXISTS_THM»
  LE_0 := Session.«LE_0»
  LE_LT := Session.«LE_LT»
  LE_REFL := Session.«LE_REFL»
  LE_SUC_LT := Session.«LE_SUC_LT»
  LT := Session.«LT»
  NOT_SUC := Session.«NOT_SUC»
  SWAP_EXISTS_THM := Session.«SWAP_EXISTS_THM»
  SWAP_FORALL_THM := Session.«SWAP_FORALL_THM»
  UNWIND_THM1 := Session.«UNWIND_THM1»
  WF := Session.«WF»
  WF_SUBSET := Session.«WF_SUBSET»
  num_RECURSION := Session.«num_RECURSION»

/-- What rstc.ml uses from Session. -/
def deps : HolLibrary.RSTC.RSTCDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  new_inductive_definition s := do
    ExceptT.mk (Session.new_inductive_definition (← HolLight.q s))
  new_recursive_definition ax s := do
    ExceptT.mk (Session.new_recursive_definition ax (← HolLight.q s))
  prioritize_num := do
    match ← HolCore.Kernel.mk_type "num" [] with
    | .ok ty => Session.prioritize_overload ty
    | .error e => throw (IO.userError e)
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  MESON_TAC := Session.MESON_TAC
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in rstc.ml order. -/
initialize BClosures : HolLibrary.RSTC.Closures ←
  ioB "setupClosures" (HolLibrary.RSTC.setupClosures deps).run
initialize BCommute : HolLibrary.RSTC.Commute ←
  ioB "setupCommute" (HolLibrary.RSTC.setupCommute deps BClosures).run
initialize BRscRtc : HolLibrary.RSTC.RscRtc ←
  ioB "setupRscRtc" (HolLibrary.RSTC.setupRscRtc deps BClosures BCommute).run
initialize BStcRstc : HolLibrary.RSTC.StcRstc ←
  ioB "setupStcRstc" (HolLibrary.RSTC.setupStcRstc deps BClosures BCommute).run
initialize BRelpow : HolLibrary.RSTC.Relpow ←
  ioB "setupRelpow" (HolLibrary.RSTC.setupRelpow deps BClosures BCommute BRscRtc BStcRstc).run

-- Closures
def RULE_INDUCT_TAC := BClosures.RULE_INDUCT_TAC
def SYM_ALT : thm := BClosures.SYM_ALT
def TRANS_ALT : thm := BClosures.TRANS_ALT
def RC_RULES : thm := BClosures.RC_RULES
def RC_INDUCT : thm := BClosures.RC_INDUCT
def RC_CASES : thm := BClosures.RC_CASES
def RC_INC : thm := BClosures.RC_INC
def RC_REFL : thm := BClosures.RC_REFL
def RC_EXPLICIT : thm := BClosures.RC_EXPLICIT
def RC_MONO : thm := BClosures.RC_MONO
def RC_CLOSED : thm := BClosures.RC_CLOSED
def RC_IDEMP : thm := BClosures.RC_IDEMP
def RC_SYM : thm := BClosures.RC_SYM
def RC_TRANS : thm := BClosures.RC_TRANS
def SC_RULES : thm := BClosures.SC_RULES
def SC_INDUCT : thm := BClosures.SC_INDUCT
def SC_CASES : thm := BClosures.SC_CASES
def SC_INC : thm := BClosures.SC_INC
def SC_SYM : thm := BClosures.SC_SYM
def SC_EXPLICIT : thm := BClosures.SC_EXPLICIT
def SC_MONO : thm := BClosures.SC_MONO
def SC_CLOSED : thm := BClosures.SC_CLOSED
def SC_IDEMP : thm := BClosures.SC_IDEMP
def SC_REFL : thm := BClosures.SC_REFL
def TC_RULES : thm := BClosures.TC_RULES
def TC_INDUCT : thm := BClosures.TC_INDUCT
def TC_CASES : thm := BClosures.TC_CASES
def TC_INC : thm := BClosures.TC_INC
def TC_TRANS : thm := BClosures.TC_TRANS
def TC_MONO : thm := BClosures.TC_MONO
def TC_CLOSED : thm := BClosures.TC_CLOSED
def TC_IDEMP : thm := BClosures.TC_IDEMP
def TC_REFL : thm := BClosures.TC_REFL
def TC_SYM : thm := BClosures.TC_SYM

-- Commute
def RC_SC : thm := BCommute.RC_SC
def SC_RC : thm := BCommute.SC_RC
def RC_TC : thm := BCommute.RC_TC
def TC_RC : thm := BCommute.TC_RC
def TC_SC : thm := BCommute.TC_SC
def SC_TC : thm := BCommute.SC_TC
def TC_TRANS_L : thm := BCommute.TC_TRANS_L
def TC_TRANS_R : thm := BCommute.TC_TRANS_R
def TC_CASES_L : thm := BCommute.TC_CASES_L
def TC_CASES_R : thm := BCommute.TC_CASES_R
def TC_INDUCT_L : thm := BCommute.TC_INDUCT_L
def TC_INDUCT_R : thm := BCommute.TC_INDUCT_R
def WF_TC : thm := BCommute.WF_TC

-- RscRtc
def RSC : thm := BRscRtc.RSC
def RSC_INC : thm := BRscRtc.RSC_INC
def RSC_REFL : thm := BRscRtc.RSC_REFL
def RSC_SYM : thm := BRscRtc.RSC_SYM
def RSC_CASES : thm := BRscRtc.RSC_CASES
def RSC_INDUCT : thm := BRscRtc.RSC_INDUCT
def RSC_MONO : thm := BRscRtc.RSC_MONO
def RSC_CLOSED : thm := BRscRtc.RSC_CLOSED
def RSC_IDEMP : thm := BRscRtc.RSC_IDEMP
def RTC : thm := BRscRtc.RTC
def RTC_INC : thm := BRscRtc.RTC_INC
def RTC_REFL : thm := BRscRtc.RTC_REFL
def RTC_TRANS : thm := BRscRtc.RTC_TRANS
def RTC_RULES : thm := BRscRtc.RTC_RULES
def RTC_TRANS_L : thm := BRscRtc.RTC_TRANS_L
def RTC_TRANS_R : thm := BRscRtc.RTC_TRANS_R
def RTC_CASES : thm := BRscRtc.RTC_CASES
def RTC_CASES_L : thm := BRscRtc.RTC_CASES_L
def RTC_CASES_R : thm := BRscRtc.RTC_CASES_R
def RTC_INDUCT : thm := BRscRtc.RTC_INDUCT
def RTC_INDUCT_L : thm := BRscRtc.RTC_INDUCT_L
def RTC_INDUCT_R : thm := BRscRtc.RTC_INDUCT_R
def RTC_MONO : thm := BRscRtc.RTC_MONO
def RTC_CLOSED : thm := BRscRtc.RTC_CLOSED
def RTC_IDEMP : thm := BRscRtc.RTC_IDEMP
def RTC_SYM : thm := BRscRtc.RTC_SYM
def RTC_STUTTER : thm := BRscRtc.RTC_STUTTER
def TC_RTC_CASES_L : thm := BRscRtc.TC_RTC_CASES_L
def TC_RTC_CASES_R : thm := BRscRtc.TC_RTC_CASES_R
def TC_TC_RTC_CASES : thm := BRscRtc.TC_TC_RTC_CASES
def TC_RTC_TC_CASES : thm := BRscRtc.TC_RTC_TC_CASES
def RTC_NE_IMP_TC : thm := BRscRtc.RTC_NE_IMP_TC

-- StcRstc
def STC : thm := BStcRstc.STC
def STC_INC : thm := BStcRstc.STC_INC
def STC_SYM : thm := BStcRstc.STC_SYM
def STC_TRANS : thm := BStcRstc.STC_TRANS
def STC_TRANS_L : thm := BStcRstc.STC_TRANS_L
def STC_TRANS_R : thm := BStcRstc.STC_TRANS_R
def STC_CASES : thm := BStcRstc.STC_CASES
def STC_CASES_L : thm := BStcRstc.STC_CASES_L
def STC_CASES_R : thm := BStcRstc.STC_CASES_R
def STC_INDUCT : thm := BStcRstc.STC_INDUCT
def STC_MONO : thm := BStcRstc.STC_MONO
def STC_CLOSED : thm := BStcRstc.STC_CLOSED
def STC_IDEMP : thm := BStcRstc.STC_IDEMP
def STC_REFL : thm := BStcRstc.STC_REFL
def RSTC : thm := BStcRstc.RSTC
def RSTC_INC : thm := BStcRstc.RSTC_INC
def RSTC_REFL : thm := BStcRstc.RSTC_REFL
def RSTC_SYM : thm := BStcRstc.RSTC_SYM
def RSTC_TRANS : thm := BStcRstc.RSTC_TRANS
def RSTC_RULES : thm := BStcRstc.RSTC_RULES
def RSTC_TRANS_L : thm := BStcRstc.RSTC_TRANS_L
def RSTC_TRANS_R : thm := BStcRstc.RSTC_TRANS_R
def RSTC_CASES : thm := BStcRstc.RSTC_CASES
def RSTC_CASES_L : thm := BStcRstc.RSTC_CASES_L
def RSTC_CASES_R : thm := BStcRstc.RSTC_CASES_R
def RSTC_INDUCT : thm := BStcRstc.RSTC_INDUCT
def RSTC_MONO : thm := BStcRstc.RSTC_MONO
def RSTC_CLOSED : thm := BStcRstc.RSTC_CLOSED
def RSTC_IDEMP : thm := BStcRstc.RSTC_IDEMP

-- Relpow
def RSC_INC_RC : thm := BRelpow.RSC_INC_RC
def RSC_INC_SC : thm := BRelpow.RSC_INC_SC
def RTC_INC_RC : thm := BRelpow.RTC_INC_RC
def RTC_INC_TC : thm := BRelpow.RTC_INC_TC
def STC_INC_SC : thm := BRelpow.STC_INC_SC
def STC_INC_TC : thm := BRelpow.STC_INC_TC
def RSTC_INC_RC : thm := BRelpow.RSTC_INC_RC
def RSTC_INC_SC : thm := BRelpow.RSTC_INC_SC
def RSTC_INC_TC : thm := BRelpow.RSTC_INC_TC
def RSTC_INC_RSC : thm := BRelpow.RSTC_INC_RSC
def RSTC_INC_RTC : thm := BRelpow.RSTC_INC_RTC
def RSTC_INC_STC : thm := BRelpow.RSTC_INC_STC
def INV : thm := BRelpow.INV
def RC_INV : thm := BRelpow.RC_INV
def SC_INV : thm := BRelpow.SC_INV
def SC_INV_STRONG : thm := BRelpow.SC_INV_STRONG
def TC_INV : thm := BRelpow.TC_INV
def RSC_INV : thm := BRelpow.RSC_INV
def RTC_INV : thm := BRelpow.RTC_INV
def STC_INV : thm := BRelpow.STC_INV
def RSTC_INV : thm := BRelpow.RSTC_INV
def RELPOW : thm := BRelpow.RELPOW
def RELPOW_R : thm := BRelpow.RELPOW_R
def RELPOW_M : thm := BRelpow.RELPOW_M
def RTC_RELPOW : thm := BRelpow.RTC_RELPOW
def TC_RELPOW : thm := BRelpow.TC_RELPOW
def RELPOW_SEQUENCE : thm := BRelpow.RELPOW_SEQUENCE





/-- `needs "Library/rstc.ml"`: already done by importing this module. -/
def ensureRSTC : IO Unit := pure ()

end SessionLibrary.RSTC
