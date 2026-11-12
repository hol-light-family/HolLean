/- ---------------------------------------------------------------------- -/
/- Session wiring for Rqe/pdivides.ml                                   . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionRQE/Pdivides.lean

  The session half of the pdivides.ml translation: it supplies HolRQE.Pdivides's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Rqe/pdivides.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolRQE.Pdivides
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
import SessionRQE.Dedmatrix

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionRQE.Pdivides

/-- The core theorems pdivides.ml uses. -/
def core1 : HolRQE.Pdivides.CoreThms1 where
  mul_odd_lem := SessionRQE.PdividesThms.«mul_odd_lem»
  neg_odd_lem := SessionRQE.PdividesThms.«neg_odd_lem»

/-- What pdivides.ml uses from Session. -/
def deps : HolRQE.Pdivides.PdividesDeps where
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
  PARITY_CONV := SessionRQE.RqeNum.PARITY_CONV
  req := SessionRQE.RqeReal.req
  rneq := SessionRQE.RqeReal.rneq
  rlt := SessionRQE.RqeReal.rlt
  rgt := SessionRQE.RqeReal.rgt
  dest_mult := SessionRQE.RqeReal.dest_mult
  dest_pow := SessionRQE.RqeReal.dest_pow
  dest_plus := SessionRQE.RqeReal.dest_plus
  pdivides_timer := SessionRQE.Timers.pdivides_timer
  POLY_NEG_CONV := SessionRQE.PolyExt.POLY_NEG_CONV
  POLY_MUL_CONV := SessionRQE.PolyExt.POLY_MUL_CONV
  POLYNATE_CONV := SessionRQE.PolyExt.POLYNATE_CONV
  head := SessionRQE.PolyExt.head
  PDIVIDE := SessionRQE.PolyExt.PDIVIDE
  FINDSIGN := SessionRQE.Signs.FINDSIGN
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in pdivides.ml order. -/
initialize BPdividesFns : HolRQE.Pdivides.PdividesFns ←
  ioB "setupPdividesFns" (HolRQE.Pdivides.setupPdividesFns deps).run

-- PdividesFns
def PDIVIDES : List term → List thm → term → term → ExceptT String IO (term × thm) := BPdividesFns.PDIVIDES

/-- `needs "Rqe/pdivides.ml"`: already done by importing this module. -/
def ensurePdivides : IO Unit := pure ()

end SessionRQE.Pdivides
