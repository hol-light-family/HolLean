/- ---------------------------------------------------------------------- -/
/- Session wiring for Rqe/signs.ml                                      . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionRQE/Signs.lean

  The session half of the signs.ml translation: it supplies HolRQE.Signs's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Rqe/signs.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolRQE.Signs
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionRQE.Signs

/-- The core theorems signs.ml uses. -/
def core1 : HolRQE.Signs.CoreThms1 where
  PULL_CASES_THM := SessionRQE.SignsThms.«PULL_CASES_THM»
  PULL_CASES_THM_NZ := SessionRQE.SignsThms.«PULL_CASES_THM_NZ»
  REAL_MUL_ASSOC := Session.REAL_MUL_ASSOC
  REAL_MUL_LID := Session.REAL_MUL_LID
  pth_0g := SessionRQE.SignsThms.«pth_0g»
  pth_0l := SessionRQE.SignsThms.«pth_0l»
  pth_gg := SessionRQE.SignsThms.«pth_gg»
  pth_gl := SessionRQE.SignsThms.«pth_gl»
  pth_lg := SessionRQE.SignsThms.«pth_lg»
  pth_ll := SessionRQE.SignsThms.«pth_ll»
  pth_nzg := SessionRQE.SignsThms.«pth_nzg»
  pth_nzl := SessionRQE.SignsThms.«pth_nzl»
  signs_lem0002 := SessionRQE.SignsThms.«signs_lem0002»
  signs_lem0003 := SessionRQE.SignsThms.«signs_lem0003»
  signs_lem002 := SessionRQE.SignsThms.«signs_lem002»
  signs_lem003 := SessionRQE.SignsThms.«signs_lem003»
  signs_lem01 := SessionRQE.SignsThms.«signs_lem01»
  signs_lem02 := SessionRQE.SignsThms.«signs_lem02»
  signs_lem03 := SessionRQE.SignsThms.«signs_lem03»
  signs_lem04 := SessionRQE.SignsThms.«signs_lem04»
  signs_lem05 := SessionRQE.SignsThms.«signs_lem05»
  signs_lem06 := SessionRQE.SignsThms.«signs_lem06»
  signs_lem07 := SessionRQE.SignsThms.«signs_lem07»
  signs_lem08 := SessionRQE.SignsThms.«signs_lem08»

/-- What signs.ml uses from Session. -/
def deps : HolRQE.Signs.SignsDeps where
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
  term_of_rat x := HolMath.CalcInt.term_of_rat Session.RSyn x
  MATCH_EQ_MP := SessionRQE.RqeTacticsExt.MATCH_EQ_MP
  dest_beq := SessionRQE.Basic.dest_beq
  mk_neq := SessionRQE.Basic.mk_neq
  req := SessionRQE.RqeReal.req
  rneq := SessionRQE.RqeReal.rneq
  rlt := SessionRQE.RqeReal.rlt
  rgt := SessionRQE.RqeReal.rgt
  rm := SessionRQE.RqeReal.rm
  rzero := SessionRQE.RqeReal.rzero
  MONIC_CONV := SessionRQE.PolyExt.MONIC_CONV
  SIGN_CONST := SessionRQE.PolyExt.SIGN_CONST
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in signs.ml order. -/
initialize BSignsFns : HolRQE.Signs.SignsFns ←
  ioB "setupSignsFns" (HolRQE.Signs.setupSignsFns deps).run

-- SignsFns
def FINDSIGN : List term → List thm → term → ExceptT String IO thm := BSignsFns.FINDSIGN
def ASSERTSIGN : List term → List thm → thm → ExceptT String IO (List thm) := BSignsFns.ASSERTSIGN
def SPLIT_ZERO : List term → List thm → term → HolRQE.Signs.SignCont → HolRQE.Signs.SignCont → List (term × thm) → ExceptT String IO thm := BSignsFns.SPLIT_ZERO
def SPLIT_SIGN : List term → List thm → term → HolRQE.Signs.SignCont → HolRQE.Signs.SignCont → List (term × thm) → ExceptT String IO thm := BSignsFns.SPLIT_SIGN

/-- `needs "Rqe/signs.ml"`: already done by importing this module. -/
def ensureSigns : IO Unit := pure ()

end SessionRQE.Signs
