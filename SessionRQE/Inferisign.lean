/- ---------------------------------------------------------------------- -/
/- Session wiring for Rqe/inferisign.ml                                 . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionRQE/Inferisign.lean

  The session half of the inferisign.ml translation: it supplies HolRQE.Inferisign's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Rqe/inferisign.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolRQE.Inferisign
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionRQE.Inferisign

/-- The core theorems inferisign.ml uses. -/
def core1 : HolRQE.Inferisign.CoreThms1 where
  APPEND := Session.listDefs.APPEND
  INFERISIGN_NEG_NEG_NEG := SessionRQE.WorkThms.«INFERISIGN_NEG_NEG_NEG»
  INFERISIGN_NEG_NEG_POS := SessionRQE.WorkThms.«INFERISIGN_NEG_NEG_POS»
  INFERISIGN_NEG_POS_NEG := SessionRQE.WorkThms.«INFERISIGN_NEG_POS_NEG»
  INFERISIGN_NEG_POS_POS := SessionRQE.WorkThms.«INFERISIGN_NEG_POS_POS»
  INFERISIGN_NEG_ZERO_NEG := SessionRQE.WorkThms.«INFERISIGN_NEG_ZERO_NEG»
  INFERISIGN_NEG_ZERO_POS := SessionRQE.WorkThms.«INFERISIGN_NEG_ZERO_POS»
  INFERISIGN_POS_NEG_NEG := SessionRQE.WorkThms.«INFERISIGN_POS_NEG_NEG»
  INFERISIGN_POS_NEG_POS := SessionRQE.WorkThms.«INFERISIGN_POS_NEG_POS»
  INFERISIGN_POS_POS_NEG := SessionRQE.WorkThms.«INFERISIGN_POS_POS_NEG»
  INFERISIGN_POS_POS_POS := SessionRQE.WorkThms.«INFERISIGN_POS_POS_POS»
  INFERISIGN_POS_ZERO_NEG := SessionRQE.WorkThms.«INFERISIGN_POS_ZERO_NEG»
  INFERISIGN_POS_ZERO_POS := SessionRQE.WorkThms.«INFERISIGN_POS_ZERO_POS»
  INFERISIGN_ZERO_NEG_NEG := SessionRQE.WorkThms.«INFERISIGN_ZERO_NEG_NEG»
  INFERISIGN_ZERO_NEG_POS := SessionRQE.WorkThms.«INFERISIGN_ZERO_NEG_POS»
  INFERISIGN_ZERO_POS_NEG := SessionRQE.WorkThms.«INFERISIGN_ZERO_POS_NEG»
  INFERISIGN_ZERO_POS_POS := SessionRQE.WorkThms.«INFERISIGN_ZERO_POS_POS»
  INFERISIGN_ZERO_ZERO_NEG := SessionRQE.WorkThms.«INFERISIGN_ZERO_ZERO_NEG»
  INFERISIGN_ZERO_ZERO_POS := SessionRQE.WorkThms.«INFERISIGN_ZERO_ZERO_POS»
  LENGTH := Session.listDefs.LENGTH
  TRUTH := Session.TRUTH
  one := Session.one

/-- What inferisign.ml uses from Session. -/
def deps : HolRQE.Inferisign.InferisignDeps where
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
  real_ty := SessionRQE.RqeReal.real_ty
  inferisign_timer := SessionRQE.Timers.inferisign_timer
  POLY_ENLIST_CONV := SessionRQE.PolyExt.POLY_ENLIST_CONV
  dest_interpmat := SessionRQE.Defs.dest_interpmat
  new_var := SessionRQE.Defs.new_var
  tmat := SessionRQE.Testform.tmat
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in inferisign.ml order. -/
initialize BInferisignFns : HolRQE.Inferisign.InferisignFns ←
  ioB "setupInferisignFns" (HolRQE.Inferisign.setupInferisignFns deps).run

-- InferisignFns
def Isign_arg : Option (IO.Ref (thm × List (term × thm))) := BInferisignFns.Isign_arg
def get_mp : term → term → term → ExceptT String IO thm := BInferisignFns.get_mp
def tvars : Option (IO.Ref (List term)) := BInferisignFns.tvars
def tdiff : Option (IO.Ref thm) := BInferisignFns.tdiff
def tmat : Option (IO.Ref thm) := BInferisignFns.tmat
def tex : Option (IO.Ref (List (term × thm))) := BInferisignFns.tex
def INFERISIGN : List term → thm → thm → List (term × thm) → ExceptT String IO (thm × List (term × thm)) := BInferisignFns.INFERISIGN

/-- `needs "Rqe/inferisign.ml"`: already done by importing this module. -/
def ensureInferisign : IO Unit := pure ()

end SessionRQE.Inferisign
