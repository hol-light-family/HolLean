/- ---------------------------------------------------------------------- -/
/- Session wiring for Rqe/inferpsign.ml                                 . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionRQE/Inferpsign.lean

  The session half of the inferpsign.ml translation: it supplies HolRQE.Inferpsign's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Rqe/inferpsign.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolRQE.Inferpsign
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionRQE.Inferpsign

/-- The core theorems inferpsign.ml uses. -/
def core1 : HolRQE.Inferpsign.CoreThms1 where
  ALL2 := Session.listDefs.ALL2
  APPEND := Session.listDefs.APPEND
  BUTLAST := Session.listDefs.BUTLAST
  EVEN := Session.EVEN
  EVEN_DIV_LEM := SessionRQE.InferpsignThms.«EVEN_DIV_LEM»
  GT_DIV_LEM := SessionRQE.InferpsignThms.«GT_DIV_LEM»
  HD := Session.listDefs.HD
  INFERPSIGN_MATINSERT_THM := SessionRQE.WorkThms.«INFERPSIGN_MATINSERT_THM»
  INFERPSIGN_NEG_EVEN := SessionRQE.WorkThms.«INFERPSIGN_NEG_EVEN»
  INFERPSIGN_NEG_ODD_POS := SessionRQE.WorkThms.«INFERPSIGN_NEG_ODD_POS»
  INFERPSIGN_POS_EVEN := SessionRQE.WorkThms.«INFERPSIGN_POS_EVEN»
  INFERPSIGN_POS_ODD_POS := SessionRQE.WorkThms.«INFERPSIGN_POS_ODD_POS»
  INFERPSIGN_ZERO_EVEN := SessionRQE.WorkThms.«INFERPSIGN_ZERO_EVEN»
  INFERPSIGN_ZERO_ODD_POS := SessionRQE.WorkThms.«INFERPSIGN_ZERO_ODD_POS»
  LENGTH := Session.listDefs.LENGTH
  MAP := Session.listDefs.MAP
  MAP2 := Session.listDefs.MAP2
  NOT_CONS_NIL := Session.listThms1.NOT_CONS_NIL
  NOT_EVEN := Session.NOT_EVEN
  NOT_ODD := Session.NOT_ODD
  ODD := Session.ODD
  REMOVE_LAST := SessionRQE.WorkThms.«REMOVE_LAST»
  REPLICATE := Session.listDefs.REPLICATE
  TL := Session.listDefs.TL
  TRUTH := Session.TRUTH
  interpsigns := SessionRQE.Defs.«interpsigns»
  ips_gt_nz_thm := SessionRQE.InferpsignThms.«ips_gt_nz_thm»
  ips_lt_nz_thm := SessionRQE.InferpsignThms.«ips_lt_nz_thm»
  one := Session.one
  pow := SessionLibrary.Analysis.«pow»
  t1 := SessionRQE.Rol.«t1»
  unknown_thm := SessionRQE.InferpsignThms.«unknown_thm»

/-- What inferpsign.ml uses from Session. -/
def deps : HolRQE.Inferpsign.InferpsignDeps where
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
  nm := SessionRQE.RqeNum.nm
  np := SessionRQE.RqeNum.np
  even_tm := SessionRQE.RqeNum.even_tm
  odd_tm := SessionRQE.RqeNum.odd_tm
  PARITY_CONV := SessionRQE.RqeNum.PARITY_CONV
  rneq := SessionRQE.RqeReal.rneq
  rlt := SessionRQE.RqeReal.rlt
  rgt := SessionRQE.RqeReal.rgt
  rm := SessionRQE.RqeReal.rm
  dest_mult := SessionRQE.RqeReal.dest_mult
  dest_pow := SessionRQE.RqeReal.dest_pow
  dest_plus := SessionRQE.RqeReal.dest_plus
  HD_CONV := SessionRQE.RqeList.HD_CONV
  inferpsign_timer := SessionRQE.Timers.inferpsign_timer
  ARITH_SIMP_CONV := SessionRQE.NumCalcSimp.ARITH_SIMP_CONV
  sneg_tm := SessionRQE.Defs.sneg_tm
  spos_tm := SessionRQE.Defs.spos_tm
  szero_tm := SessionRQE.Defs.szero_tm
  dest_interpsign := SessionRQE.Defs.dest_interpsign
  interpsigns_thms2 := SessionRQE.Defs.interpsigns_thms2
  dest_interpsigns := SessionRQE.Defs.dest_interpsigns
  mk_interpsigns := SessionRQE.Defs.mk_interpsigns
  PARTITION_LINE_CONV := SessionRQE.Defs.PARTITION_LINE_CONV
  dest_interpmat := SessionRQE.Defs.dest_interpmat
  interpmat_thms := SessionRQE.Defs.interpmat_thms
  mk_interpmat_thm := SessionRQE.Defs.mk_interpmat_thm
  mk_all2_interpsigns := SessionRQE.Defs.mk_all2_interpsigns
  MK_SUC := SessionRQE.Matinsert.MK_SUC
  FINDSIGN := SessionRQE.Signs.FINDSIGN
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in inferpsign.ml order. -/
initialize BInferpsignFns : HolRQE.Inferpsign.InferpsignFns ←
  ioB "setupInferpsignFns" (HolRQE.Inferpsign.setupInferpsignFns deps).run

-- InferpsignFns
def isign_eq_zero : thm → Except String Bool := BInferpsignFns.isign_eq_zero
def isign_lt_zero : thm → Except String Bool := BInferpsignFns.isign_lt_zero
def isign_gt_zero : thm → Except String Bool := BInferpsignFns.isign_gt_zero
def inferpsign_row : List term → List thm → thm → thm → List thm → ExceptT String IO thm := BInferpsignFns.inferpsign_row
def split_interpsigns : thm → ExceptT String IO (thm × thm) := BInferpsignFns.split_interpsigns
def INFERPSIGN : List term → List thm → thm → List thm → ExceptT String IO thm := BInferpsignFns.INFERPSIGN
def MK_REP : term → ExceptT String IO thm := BInferpsignFns.MK_REP
def INSERT_UNKNOWN_COL : thm → term → ExceptT String IO thm := BInferpsignFns.INSERT_UNKNOWN_COL
def REMOVE_QS : thm → ExceptT String IO thm := BInferpsignFns.REMOVE_QS
def SPLIT_LIST : Nat → term → hol_type → ExceptT String IO thm := BInferpsignFns.SPLIT_LIST
def prove_nonzero : thm → ExceptT String IO thm := BInferpsignFns.prove_nonzero
def INFERPT : List term → List thm → thm → List thm → Int → ExceptT String IO thm := BInferpsignFns.INFERPT
def INFERPTS : List term → List thm → thm → List thm → ExceptT String IO thm := BInferpsignFns.INFERPTS
def itvars : Option (IO.Ref (List term)) := BInferpsignFns.itvars
def itsgns : Option (IO.Ref (List thm)) := BInferpsignFns.itsgns
def itmat : Option (IO.Ref thm) := BInferpsignFns.itmat
def itdivs : Option (IO.Ref (List thm)) := BInferpsignFns.itdivs
def INFERPSIGN2 : List term → List thm → thm → List thm → ExceptT String IO thm := BInferpsignFns.INFERPSIGN2

/-- `needs "Rqe/inferpsign.ml"`: already done by importing this module. -/
def ensureInferpsign : IO Unit := pure ()

end SessionRQE.Inferpsign
