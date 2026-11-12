/- ---------------------------------------------------------------------- -/
/- Session wiring for Rqe/matinsert.ml                                  . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionRQE/Matinsert.lean

  The session half of the matinsert.ml translation: it supplies HolRQE.Matinsert's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Rqe/matinsert.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolRQE.Matinsert
import SessionLibrary.Analysis
import SessionLibrary.Poly
import SessionRQE.RqeLib
import SessionRQE.RqeTacticsExt
import SessionRQE.Util
import SessionRQE.Rewrites
import SessionRQE.Basic
import SessionRQE.RqeNum
import SessionRQE.RqeReal
import SessionRQE.ListRewrites
import SessionRQE.RqeList
import SessionRQE.Timers
import SessionRQE.NumCalcSimp
import SessionRQE.Asym
import SessionRQE.Rol
import SessionRQE.PolyExt
import SessionRQE.Simplify
import SessionRQE.LiftQelim
import SessionRQE.Defs
import SessionRQE.TestformThms
import SessionRQE.CondenseThms
import SessionRQE.InferisignThms
import SessionRQE.MatinsertThms
import SessionRQE.SignsThms
import SessionRQE.InferpsignThms
import SessionRQE.DedmatrixThms
import SessionRQE.PdividesThms
import SessionRQE.MainThms
import SessionRQE.WorkThms
import SessionRQE.Testform
import SessionRQE.Condense
import SessionRQE.Inferisign

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionRQE.Matinsert

/-- The core theorems matinsert.ml uses. -/
def core1 : HolRQE.Matinsert.CoreThms1 where
  ALL2 := Session.listDefs.ALL2
  LENGTH := Session.listDefs.LENGTH
  PARTITION_LINE_LENGTH := SessionRQE.WorkThms.«PARTITION_LINE_LENGTH»
  TRUTH := Session.TRUTH
  all2_thm := SessionRQE.Defs.«all2_thm»
  interpsign := SessionRQE.Defs.«interpsign»
  matinsert_lem0 := SessionRQE.MatinsertThms.«matinsert_lem0»

/-- What matinsert.ml uses from Session. -/
def deps : HolRQE.Matinsert.MatinsertDeps where
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
  LET_TAC := Session.LET_TAC
  basic_ss := Session.basic_ss
  NUM_SUB_CONV := Session.NUM_SUB_CONV
  REAL_RAT_REDUCE_CONV := Session.REAL_RAT_REDUCE_CONV
  NUM_EQ_CONV := Session.NUM_EQ_CONV
  NUM_DIV_CONV := Session.NUM_DIV_CONV
  EXP_MOD_CONV := Session.EXP_MOD_CONV
  EXPAND_CASES_CONV := Session.EXPAND_CASES_CONV
  mk_small_numeral := Session.mk_small_numeral
  t_tm := SessionRQE.LiftQelim.t_tm
  nle := SessionRQE.RqeNum.nle
  matinsert_timer := SessionRQE.Timers.matinsert_timer
  ARITH_SIMP_CONV := SessionRQE.NumCalcSimp.ARITH_SIMP_CONV
  dest_interpsign := SessionRQE.Defs.dest_interpsign
  interpsigns_thms2 := SessionRQE.Defs.interpsigns_thms2
  mk_interpsigns := SessionRQE.Defs.mk_interpsigns
  PARTITION_LINE_CONV := SessionRQE.Defs.PARTITION_LINE_CONV
  interpmat_thms := SessionRQE.Defs.interpmat_thms
  mk_interpmat_thm := SessionRQE.Defs.mk_interpmat_thm
  mk_all2_interpsigns := SessionRQE.Defs.mk_all2_interpsigns
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in matinsert.ml order. -/
initialize BMatinsertFns : HolRQE.Matinsert.MatinsertFns ←
  ioB "setupMatinsertFns" (HolRQE.Matinsert.setupMatinsertFns deps).run

-- MatinsertFns
def ROWINSERT : Int → thm → thm → ExceptT String IO thm := BMatinsertFns.ROWINSERT
def MATINSERT : List term → Int → thm → HolRQE.Matinsert.MatCont → HolRQE.Matinsert.MatCont := BMatinsertFns.MATINSERT
def mk_suc : Int → Except String term := BMatinsertFns.mk_suc
def MK_SUC : Int → ExceptT String IO thm := BMatinsertFns.MK_SUC
def PL_LENGTH : term → ExceptT String IO thm := BMatinsertFns.PL_LENGTH
def MK_LT : Int × Int → ExceptT String IO thm := BMatinsertFns.MK_LT

/-- `needs "Rqe/matinsert.ml"`: already done by importing this module. -/
def ensureMatinsert : IO Unit := pure ()

end SessionRQE.Matinsert
