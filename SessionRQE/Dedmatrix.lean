/- ---------------------------------------------------------------------- -/
/- Session wiring for Rqe/dedmatrix.ml                                  . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionRQE/Dedmatrix.lean

  The session half of the dedmatrix.ml translation: it supplies HolRQE.Dedmatrix's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Rqe/dedmatrix.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolRQE.Dedmatrix
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
import SessionRQE.Matinsert
import SessionRQE.Signs
import SessionRQE.Inferpsign

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionRQE.Dedmatrix

/-- The core theorems dedmatrix.ml uses. -/
def core1 : HolRQE.Dedmatrix.CoreThms1 where
  APPEND := Session.listDefs.APPEND
  HD := Session.listDefs.HD
  INFIN_NEG_NEG := SessionRQE.WorkThms.«INFIN_NEG_NEG»
  INFIN_NEG_POS := SessionRQE.WorkThms.«INFIN_NEG_POS»
  INFIN_NIL_NEG := SessionRQE.WorkThms.«INFIN_NIL_NEG»
  INFIN_NIL_POS := SessionRQE.WorkThms.«INFIN_NIL_POS»
  INFIN_POS_NEG := SessionRQE.WorkThms.«INFIN_POS_NEG»
  INFIN_POS_POS := SessionRQE.WorkThms.«INFIN_POS_POS»
  INFIN_SING_NEG_NEG := SessionRQE.WorkThms.«INFIN_SING_NEG_NEG»
  INFIN_SING_NEG_POS := SessionRQE.WorkThms.«INFIN_SING_NEG_POS»
  INFIN_SING_POS_NEG := SessionRQE.WorkThms.«INFIN_SING_POS_NEG»
  INFIN_SING_POS_POS := SessionRQE.WorkThms.«INFIN_SING_POS_POS»
  INTERPMAT_TRIO := SessionRQE.WorkThms.«INTERPMAT_TRIO»
  INTERPMAT_TRIO_TL := SessionRQE.WorkThms.«INTERPMAT_TRIO_TL»
  MAP := Session.listDefs.MAP
  NORMAL_PDIFF := SessionRQE.Asym.«NORMAL_PDIFF»
  REMOVE_COL1 := SessionRQE.WorkThms.«REMOVE_COL1»
  TL := Session.listDefs.TL
  TRUTH := Session.TRUTH

/-- What dedmatrix.ml uses from Session. -/
def deps : HolRQE.Dedmatrix.DedmatrixDeps where
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
  remove_column1_timer := SessionRQE.Timers.remove_column1_timer
  add_infinities_timer := SessionRQE.Timers.add_infinities_timer
  remove_infinities_timer := SessionRQE.Timers.remove_infinities_timer
  print_timers := SessionRQE.Timers.print_timers
  POLY_ENLIST_CONV := SessionRQE.PolyExt.POLY_ENLIST_CONV
  dest_interpmat := SessionRQE.Defs.dest_interpmat
  new_var := SessionRQE.Defs.new_var
  tmat := SessionRQE.Inferisign.tmat
  CONDENSE := SessionRQE.Condense.CONDENSE
  tvars := SessionRQE.Inferisign.tvars
  tdiff := SessionRQE.Inferisign.tdiff
  tex := SessionRQE.Inferisign.tex
  INFERISIGN := SessionRQE.Inferisign.INFERISIGN
  INFERPSIGN := SessionRQE.Inferpsign.INFERPSIGN
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in dedmatrix.ml order. -/
initialize BDedmatrixFns : HolRQE.Dedmatrix.DedmatrixFns ←
  ioB "setupDedmatrixFns" (HolRQE.Dedmatrix.setupDedmatrixFns deps).run

-- DedmatrixFns
def prove_nonconstant : thm → thm → ExceptT String IO thm := BDedmatrixFns.prove_nonconstant
def REMOVE_COLUMN1 : thm → ExceptT String IO thm := BDedmatrixFns.REMOVE_COLUMN1
def APPENDIZE : term → Int → ExceptT String IO thm := BDedmatrixFns.APPENDIZE
def REMOVE_INFINITIES : thm → ExceptT String IO thm := BDedmatrixFns.REMOVE_INFINITIES
def get_dirs : term → term → ExceptT String IO thm := BDedmatrixFns.get_dirs
def get_sing_dirs : term → term → ExceptT String IO thm := BDedmatrixFns.get_sing_dirs
def aitvars : Option (IO.Ref (List term)) := BDedmatrixFns.aitvars
def aitdiff : Option (IO.Ref thm) := BDedmatrixFns.aitdiff
def aitnorm : Option (IO.Ref thm) := BDedmatrixFns.aitnorm
def aitmat : Option (IO.Ref thm) := BDedmatrixFns.aitmat
def ADD_INFINITIES : List term → thm → thm → thm → ExceptT String IO (thm × (term × thm) × (term × thm)) := BDedmatrixFns.ADD_INFINITIES
def tvars : Option (IO.Ref (List term)) := BDedmatrixFns.tvars
def tsgns : Option (IO.Ref (List thm)) := BDedmatrixFns.tsgns
def tdivs : Option (IO.Ref (List thm)) := BDedmatrixFns.tdivs
def tdiff : Option (IO.Ref thm) := BDedmatrixFns.tdiff
def tnorm : Option (IO.Ref thm) := BDedmatrixFns.tnorm
def tcont : Option (IO.Ref HolRQE.Dedmatrix.DedCont) := BDedmatrixFns.tcont
def tmat : Option (IO.Ref thm) := BDedmatrixFns.tmat
def tex : Option (IO.Ref (List (term × thm))) := BDedmatrixFns.tex
def DEDMATRIX : List term → List thm → List thm → thm → thm → HolRQE.Dedmatrix.DedCont → thm → List (term × thm) → ExceptT String IO thm := BDedmatrixFns.DEDMATRIX

/-- `needs "Rqe/dedmatrix.ml"`: already done by importing this module. -/
def ensureDedmatrix : IO Unit := pure ()

end SessionRQE.Dedmatrix
