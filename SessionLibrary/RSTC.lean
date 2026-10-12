/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/rstc.ml.                                    -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/RSTC.lean

  The `unsafe` half of the rstc.ml translation: it supplies HolLibrary.RSTC's
  dependencies from Session, builds each bundle once, in file order, and
  exports every name under its HOL Light name.  `ensureRSTC` is `needs
  "Library/rstc.ml"`.

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/RSTC.lean by tools/rstcdiff/gen_session.py (bookkeeping only:
  field-by-field copies and accessors).
-/

import Session
import HolLibrary.RSTC

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.RSTC

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems rstc.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.RSTC.CoreThms1 where
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
  num_RECURSION := Session.«num_RECURSION»-- @@CORE END

/-- What rstc.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.RSTC.RSTCDeps where
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
  core1 := core1 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`): HOL Light has loaded all of hol_lib.ml before
    `needs "Library/rstc.ml"`, and rstc.ml's `prioritize_num` must not apply
    to core layers that Session would otherwise build later, on first use. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.RSTC: {name}"

/- The bundles, in rstc.ml order.  Each forces the one before it, so that
   any bundle builds every earlier one first, as HOL Light's load does. -/

-- @@BUNDLES BEGIN
initialize theClosures : IO.Ref (Option HolLibrary.RSTC.Closures) ← IO.mkRef none
unsafe def BClosures : HolLibrary.RSTC.Closures :=
  cached theClosures "setupClosures" fun _ => do
    (HolLibrary.RSTC.setupClosures (deps ())).run

initialize theCommute : IO.Ref (Option HolLibrary.RSTC.Commute) ← IO.mkRef none
unsafe def BCommute : HolLibrary.RSTC.Commute :=
  cached theCommute "setupCommute" fun _ => do
    let _ ← IO.mkRef BClosures.RULE_INDUCT_TAC
    (HolLibrary.RSTC.setupCommute (deps ()) BClosures).run

initialize theRscRtc : IO.Ref (Option HolLibrary.RSTC.RscRtc) ← IO.mkRef none
unsafe def BRscRtc : HolLibrary.RSTC.RscRtc :=
  cached theRscRtc "setupRscRtc" fun _ => do
    let _ ← IO.mkRef BCommute.RC_SC
    (HolLibrary.RSTC.setupRscRtc (deps ()) BClosures BCommute).run

initialize theStcRstc : IO.Ref (Option HolLibrary.RSTC.StcRstc) ← IO.mkRef none
unsafe def BStcRstc : HolLibrary.RSTC.StcRstc :=
  cached theStcRstc "setupStcRstc" fun _ => do
    let _ ← IO.mkRef BRscRtc.RSC
    (HolLibrary.RSTC.setupStcRstc (deps ()) BClosures BCommute).run

initialize theRelpow : IO.Ref (Option HolLibrary.RSTC.Relpow) ← IO.mkRef none
unsafe def BRelpow : HolLibrary.RSTC.Relpow :=
  cached theRelpow "setupRelpow" fun _ => do
    let _ ← IO.mkRef BStcRstc.STC
    (HolLibrary.RSTC.setupRelpow (deps ()) BClosures BCommute BRscRtc BStcRstc).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Closures
unsafe def RULE_INDUCT_TAC := BClosures.RULE_INDUCT_TAC
unsafe def SYM_ALT : thm := BClosures.SYM_ALT
unsafe def TRANS_ALT : thm := BClosures.TRANS_ALT
unsafe def RC_RULES : thm := BClosures.RC_RULES
unsafe def RC_INDUCT : thm := BClosures.RC_INDUCT
unsafe def RC_CASES : thm := BClosures.RC_CASES
unsafe def RC_INC : thm := BClosures.RC_INC
unsafe def RC_REFL : thm := BClosures.RC_REFL
unsafe def RC_EXPLICIT : thm := BClosures.RC_EXPLICIT
unsafe def RC_MONO : thm := BClosures.RC_MONO
unsafe def RC_CLOSED : thm := BClosures.RC_CLOSED
unsafe def RC_IDEMP : thm := BClosures.RC_IDEMP
unsafe def RC_SYM : thm := BClosures.RC_SYM
unsafe def RC_TRANS : thm := BClosures.RC_TRANS
unsafe def SC_RULES : thm := BClosures.SC_RULES
unsafe def SC_INDUCT : thm := BClosures.SC_INDUCT
unsafe def SC_CASES : thm := BClosures.SC_CASES
unsafe def SC_INC : thm := BClosures.SC_INC
unsafe def SC_SYM : thm := BClosures.SC_SYM
unsafe def SC_EXPLICIT : thm := BClosures.SC_EXPLICIT
unsafe def SC_MONO : thm := BClosures.SC_MONO
unsafe def SC_CLOSED : thm := BClosures.SC_CLOSED
unsafe def SC_IDEMP : thm := BClosures.SC_IDEMP
unsafe def SC_REFL : thm := BClosures.SC_REFL
unsafe def TC_RULES : thm := BClosures.TC_RULES
unsafe def TC_INDUCT : thm := BClosures.TC_INDUCT
unsafe def TC_CASES : thm := BClosures.TC_CASES
unsafe def TC_INC : thm := BClosures.TC_INC
unsafe def TC_TRANS : thm := BClosures.TC_TRANS
unsafe def TC_MONO : thm := BClosures.TC_MONO
unsafe def TC_CLOSED : thm := BClosures.TC_CLOSED
unsafe def TC_IDEMP : thm := BClosures.TC_IDEMP
unsafe def TC_REFL : thm := BClosures.TC_REFL
unsafe def TC_SYM : thm := BClosures.TC_SYM

-- Commute
unsafe def RC_SC : thm := BCommute.RC_SC
unsafe def SC_RC : thm := BCommute.SC_RC
unsafe def RC_TC : thm := BCommute.RC_TC
unsafe def TC_RC : thm := BCommute.TC_RC
unsafe def TC_SC : thm := BCommute.TC_SC
unsafe def SC_TC : thm := BCommute.SC_TC
unsafe def TC_TRANS_L : thm := BCommute.TC_TRANS_L
unsafe def TC_TRANS_R : thm := BCommute.TC_TRANS_R
unsafe def TC_CASES_L : thm := BCommute.TC_CASES_L
unsafe def TC_CASES_R : thm := BCommute.TC_CASES_R
unsafe def TC_INDUCT_L : thm := BCommute.TC_INDUCT_L
unsafe def TC_INDUCT_R : thm := BCommute.TC_INDUCT_R
unsafe def WF_TC : thm := BCommute.WF_TC

-- RscRtc
unsafe def RSC : thm := BRscRtc.RSC
unsafe def RSC_INC : thm := BRscRtc.RSC_INC
unsafe def RSC_REFL : thm := BRscRtc.RSC_REFL
unsafe def RSC_SYM : thm := BRscRtc.RSC_SYM
unsafe def RSC_CASES : thm := BRscRtc.RSC_CASES
unsafe def RSC_INDUCT : thm := BRscRtc.RSC_INDUCT
unsafe def RSC_MONO : thm := BRscRtc.RSC_MONO
unsafe def RSC_CLOSED : thm := BRscRtc.RSC_CLOSED
unsafe def RSC_IDEMP : thm := BRscRtc.RSC_IDEMP
unsafe def RTC : thm := BRscRtc.RTC
unsafe def RTC_INC : thm := BRscRtc.RTC_INC
unsafe def RTC_REFL : thm := BRscRtc.RTC_REFL
unsafe def RTC_TRANS : thm := BRscRtc.RTC_TRANS
unsafe def RTC_RULES : thm := BRscRtc.RTC_RULES
unsafe def RTC_TRANS_L : thm := BRscRtc.RTC_TRANS_L
unsafe def RTC_TRANS_R : thm := BRscRtc.RTC_TRANS_R
unsafe def RTC_CASES : thm := BRscRtc.RTC_CASES
unsafe def RTC_CASES_L : thm := BRscRtc.RTC_CASES_L
unsafe def RTC_CASES_R : thm := BRscRtc.RTC_CASES_R
unsafe def RTC_INDUCT : thm := BRscRtc.RTC_INDUCT
unsafe def RTC_INDUCT_L : thm := BRscRtc.RTC_INDUCT_L
unsafe def RTC_INDUCT_R : thm := BRscRtc.RTC_INDUCT_R
unsafe def RTC_MONO : thm := BRscRtc.RTC_MONO
unsafe def RTC_CLOSED : thm := BRscRtc.RTC_CLOSED
unsafe def RTC_IDEMP : thm := BRscRtc.RTC_IDEMP
unsafe def RTC_SYM : thm := BRscRtc.RTC_SYM
unsafe def RTC_STUTTER : thm := BRscRtc.RTC_STUTTER
unsafe def TC_RTC_CASES_L : thm := BRscRtc.TC_RTC_CASES_L
unsafe def TC_RTC_CASES_R : thm := BRscRtc.TC_RTC_CASES_R
unsafe def TC_TC_RTC_CASES : thm := BRscRtc.TC_TC_RTC_CASES
unsafe def TC_RTC_TC_CASES : thm := BRscRtc.TC_RTC_TC_CASES
unsafe def RTC_NE_IMP_TC : thm := BRscRtc.RTC_NE_IMP_TC

-- StcRstc
unsafe def STC : thm := BStcRstc.STC
unsafe def STC_INC : thm := BStcRstc.STC_INC
unsafe def STC_SYM : thm := BStcRstc.STC_SYM
unsafe def STC_TRANS : thm := BStcRstc.STC_TRANS
unsafe def STC_TRANS_L : thm := BStcRstc.STC_TRANS_L
unsafe def STC_TRANS_R : thm := BStcRstc.STC_TRANS_R
unsafe def STC_CASES : thm := BStcRstc.STC_CASES
unsafe def STC_CASES_L : thm := BStcRstc.STC_CASES_L
unsafe def STC_CASES_R : thm := BStcRstc.STC_CASES_R
unsafe def STC_INDUCT : thm := BStcRstc.STC_INDUCT
unsafe def STC_MONO : thm := BStcRstc.STC_MONO
unsafe def STC_CLOSED : thm := BStcRstc.STC_CLOSED
unsafe def STC_IDEMP : thm := BStcRstc.STC_IDEMP
unsafe def STC_REFL : thm := BStcRstc.STC_REFL
unsafe def RSTC : thm := BStcRstc.RSTC
unsafe def RSTC_INC : thm := BStcRstc.RSTC_INC
unsafe def RSTC_REFL : thm := BStcRstc.RSTC_REFL
unsafe def RSTC_SYM : thm := BStcRstc.RSTC_SYM
unsafe def RSTC_TRANS : thm := BStcRstc.RSTC_TRANS
unsafe def RSTC_RULES : thm := BStcRstc.RSTC_RULES
unsafe def RSTC_TRANS_L : thm := BStcRstc.RSTC_TRANS_L
unsafe def RSTC_TRANS_R : thm := BStcRstc.RSTC_TRANS_R
unsafe def RSTC_CASES : thm := BStcRstc.RSTC_CASES
unsafe def RSTC_CASES_L : thm := BStcRstc.RSTC_CASES_L
unsafe def RSTC_CASES_R : thm := BStcRstc.RSTC_CASES_R
unsafe def RSTC_INDUCT : thm := BStcRstc.RSTC_INDUCT
unsafe def RSTC_MONO : thm := BStcRstc.RSTC_MONO
unsafe def RSTC_CLOSED : thm := BStcRstc.RSTC_CLOSED
unsafe def RSTC_IDEMP : thm := BStcRstc.RSTC_IDEMP

-- Relpow
unsafe def RSC_INC_RC : thm := BRelpow.RSC_INC_RC
unsafe def RSC_INC_SC : thm := BRelpow.RSC_INC_SC
unsafe def RTC_INC_RC : thm := BRelpow.RTC_INC_RC
unsafe def RTC_INC_TC : thm := BRelpow.RTC_INC_TC
unsafe def STC_INC_SC : thm := BRelpow.STC_INC_SC
unsafe def STC_INC_TC : thm := BRelpow.STC_INC_TC
unsafe def RSTC_INC_RC : thm := BRelpow.RSTC_INC_RC
unsafe def RSTC_INC_SC : thm := BRelpow.RSTC_INC_SC
unsafe def RSTC_INC_TC : thm := BRelpow.RSTC_INC_TC
unsafe def RSTC_INC_RSC : thm := BRelpow.RSTC_INC_RSC
unsafe def RSTC_INC_RTC : thm := BRelpow.RSTC_INC_RTC
unsafe def RSTC_INC_STC : thm := BRelpow.RSTC_INC_STC
unsafe def INV : thm := BRelpow.INV
unsafe def RC_INV : thm := BRelpow.RC_INV
unsafe def SC_INV : thm := BRelpow.SC_INV
unsafe def SC_INV_STRONG : thm := BRelpow.SC_INV_STRONG
unsafe def TC_INV : thm := BRelpow.TC_INV
unsafe def RSC_INV : thm := BRelpow.RSC_INV
unsafe def RTC_INV : thm := BRelpow.RTC_INV
unsafe def STC_INV : thm := BRelpow.STC_INV
unsafe def RSTC_INV : thm := BRelpow.RSTC_INV
unsafe def RELPOW : thm := BRelpow.RELPOW
unsafe def RELPOW_R : thm := BRelpow.RELPOW_R
unsafe def RELPOW_M : thm := BRelpow.RELPOW_M
unsafe def RTC_RELPOW : thm := BRelpow.RTC_RELPOW
unsafe def TC_RELPOW : thm := BRelpow.TC_RELPOW
unsafe def RELPOW_SEQUENCE : thm := BRelpow.RELPOW_SEQUENCE





-- @@EXPORTS END

/-- `needs "Library/rstc.ml"`: build every bundle, in file order. -/
unsafe def ensureRSTC : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BClosures.SYM_ALT
  let _ ← IO.mkRef BCommute.RC_SC
  let _ ← IO.mkRef BRscRtc.RSC
  let _ ← IO.mkRef BStcRstc.STC
  let _ ← IO.mkRef BRelpow.RSC_INC_RC  -- @@ENSURE END
  pure ()

end SessionLibrary.RSTC
