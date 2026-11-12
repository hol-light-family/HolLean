/- ---------------------------------------------------------------------- -/
/- Session wiring for Rqe/util.ml                                       . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionRQE/Util.lean

  The session half of the util.ml translation: it supplies HolRQE.Util's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Rqe/util.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolRQE.Util
import SessionLibrary.Analysis
import SessionLibrary.Poly
import SessionRQE.RqeLib
import SessionRQE.RqeTacticsExt

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionRQE.Util

/-- The core theorems util.ml uses. -/
def core1 : HolRQE.Util.CoreThms1 where

/-- What util.ml uses from Session. -/
def deps : HolRQE.Util.UtilDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
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
  current_goalstack := Session.currentGoalstack
  g := Session.g
  p _ := Session.p
  top_goal _ := Session.top_goal
  labels_flag := SessionRQE.RqeTacticsExt.labels_flag
  prove_by_refinement := SessionRQE.RqeTacticsExt.prove_by_refinement
  exclude_list := SessionRQE.RqeTacticsExt.exclude_list
  get_var_list := SessionRQE.RqeTacticsExt.get_var_list
  auto_type := SessionRQE.RqeTacticsExt.auto_type
  auto_type_list := SessionRQE.RqeTacticsExt.auto_type_list
  auto_type_goal := SessionRQE.RqeTacticsExt.auto_type_goal
  TYPE_TAC := SessionRQE.RqeTacticsExt.TYPE_TAC
  TYPE_TACL := SessionRQE.RqeTacticsExt.TYPE_TACL
  CLAIM := SessionRQE.RqeTacticsExt.CLAIM
  MATCH_EQ_MP := SessionRQE.RqeTacticsExt.MATCH_EQ_MP
  DISJ_LCASE := SessionRQE.RqeTacticsExt.DISJ_LCASE
  DISJ_RCASE := SessionRQE.RqeTacticsExt.DISJ_RCASE
  CASES_ON := SessionRQE.RqeTacticsExt.CASES_ON
  EXISTS_TAC := SessionRQE.RqeTacticsExt.EXISTS_TAC
  MATCH_EQ_MPL := SessionRQE.RqeTacticsExt.MATCH_EQ_MPL
  CCONTR_TAC := SessionRQE.RqeTacticsExt.CCONTR_TAC
  pgoal := SessionRQE.RqeTacticsExt.pgoal
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in util.ml order. -/
initialize BUtilFns : HolRQE.Util.UtilFns ←
  ioB "setupUtilFns" (HolRQE.Util.setupUtilFns deps).run

-- UtilFns
def suppress : Option (IO.Ref (List String)) := BUtilFns.suppress
def get_type_list : term → IO (List (String × hol_type)) := BUtilFns.get_type_list
def set_types : term → IO (List (String × hol_type)) := BUtilFns.set_types
def print_term_types : term → IO Unit := BUtilFns.print_term_types
def print_thm_types : thm → IO Unit := BUtilFns.print_thm_types
def goal_types : Unit → IO Unit := BUtilFns.goal_types
def assum : Int → ExceptT String IO term := BUtilFns.assum
def assum_types : Int → ExceptT String IO Unit := BUtilFns.assum_types
def get_type : String → thm → ExceptT String IO hol_type := BUtilFns.get_type
def proof_stack : Option (IO.Ref (List HolCore.Tactics.goalstack)) := BUtilFns.proof_stack
def push_proof : term → IO HolCore.Tactics.goalstack := BUtilFns.push_proof
def pop_proof : Unit → ExceptT String IO HolCore.Tactics.goalstack := BUtilFns.pop_proof

/-- `needs "Rqe/util.ml"`: already done by importing this module. -/
def ensureUtil : IO Unit := pure ()

end SessionRQE.Util
