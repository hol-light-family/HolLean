/- ---------------------------------------------------------------------- -/
/- Session wiring for Rqe/rqe_tactics_ext.ml                            . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionRQE/RqeTacticsExt.lean

  The session half of the rqe_tactics_ext.ml translation: it supplies HolRQE.RqeTacticsExt's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Rqe/rqe_tactics_ext.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolRQE.RqeTacticsExt
import SessionLibrary.Analysis
import SessionLibrary.Poly
import SessionRQE.RqeLib

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionRQE.RqeTacticsExt

/-- The core theorems rqe_tactics_ext.ml uses. -/
def core1 : HolRQE.RqeTacticsExt.CoreThms1 where
  EXCLUDED_MIDDLE := Session.EXCLUDED_MIDDLE
  num_CASES := Session.num_CASES

/-- What rqe_tactics_ext.ml uses from Session. -/
def deps : HolRQE.RqeTacticsExt.RqeTacticsExtDeps where
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
  refine := Session.refine
  current_goalstack := Session.currentGoalstack
  FALSITY_DEF := Session.FALSITY_DEF
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in rqe_tactics_ext.ml order. -/
initialize BRqeTacticsExtTactics : HolRQE.RqeTacticsExt.RqeTacticsExtTactics ←
  ioB "setupRqeTacticsExtTactics" (HolRQE.RqeTacticsExt.setupRqeTacticsExtTactics deps).run

-- RqeTacticsExtTactics
def labels_flag : Option (IO.Ref Bool) := BRqeTacticsExtTactics.labels_flag
def e : HolCore.Tactics.tactic → IO HolCore.Tactics.goalstack := BRqeTacticsExtTactics.e
def prove_by_refinement : term × List HolCore.Tactics.tactic → ExceptT String IO thm := BRqeTacticsExtTactics.prove_by_refinement
def exclude_list : Option (IO.Ref (List String)) := BRqeTacticsExtTactics.exclude_list
def get_var_list : term → IO (List (String × hol_type)) := BRqeTacticsExtTactics.get_var_list
def auto_type : term → term → IO term := BRqeTacticsExtTactics.auto_type
def auto_type_list : term → List term → IO term := BRqeTacticsExtTactics.auto_type_list
def auto_type_goal : term → HolCore.Tactics.goal → IO term := BRqeTacticsExtTactics.auto_type_goal
def TYPE_TAC : (term → HolCore.Tactics.tactic) → term → HolCore.Tactics.tactic := BRqeTacticsExtTactics.TYPE_TAC
def TYPE_TACL : (List term → HolCore.Tactics.tactic) → List term → HolCore.Tactics.tactic := BRqeTacticsExtTactics.TYPE_TACL
def CLAIM : term → HolCore.Tactics.tactic := BRqeTacticsExtTactics.CLAIM
def lem : thm := BRqeTacticsExtTactics.lem
def MATCH_EQ_MP : thm → thm → ExceptT String IO thm := BRqeTacticsExtTactics.MATCH_EQ_MP
def DISJ_LCASE : HolCore.Tactics.tactic := BRqeTacticsExtTactics.DISJ_LCASE
def DISJ_RCASE : HolCore.Tactics.tactic := BRqeTacticsExtTactics.DISJ_RCASE
def CASES_ON : term → HolCore.Tactics.tactic := BRqeTacticsExtTactics.CASES_ON
def EXISTS_TAC : term → HolCore.Tactics.tactic := BRqeTacticsExtTactics.EXISTS_TAC
def MATCH_EQ_MPL : List thm → ExceptT String IO thm := BRqeTacticsExtTactics.MATCH_EQ_MPL
def CCONTR_TAC : HolCore.Tactics.tactic := BRqeTacticsExtTactics.CCONTR_TAC
def pgoal : Unit → IO HolCore.Tactics.goalstack := BRqeTacticsExtTactics.pgoal

/-- `needs "Rqe/rqe_tactics_ext.ml"`: already done by importing this module. -/
def ensureRqeTacticsExt : IO Unit := pure ()

end SessionRQE.RqeTacticsExt
