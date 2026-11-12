/- ---------------------------------------------------------------------- -/
/- Session wiring for Rqe/rewrites.ml                                   . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionRQE/Rewrites.lean

  The session half of the rewrites.ml translation: it supplies HolRQE.Rewrites's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Rqe/rewrites.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolRQE.Rewrites
import SessionLibrary.Analysis
import SessionLibrary.Poly
import SessionRQE.RqeLib
import SessionRQE.RqeTacticsExt
import SessionRQE.Util

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionRQE.Rewrites

/-- The core theorems rewrites.ml uses. -/
def core1 : HolRQE.Rewrites.CoreThms1 where
  GE := Session.GE
  GT := Session.GT
  LET_TRANS := Session.LET_TRANS
  LE_TRANS := Session.LE_TRANS
  LTE_TRANS := Session.LTE_TRANS
  LT_TRANS := Session.LT_TRANS
  PRE := Session.PRE
  REAL_ADD_ASSOC := Session.REAL_ADD_ASSOC
  REAL_ADD_LDISTRIB := Session.REAL_ADD_LDISTRIB
  REAL_ADD_LID := Session.REAL_ADD_LID
  REAL_ADD_RDISTRIB := Session.REAL_ADD_RDISTRIB
  REAL_ADD_RID := Session.REAL_ADD_RID
  REAL_ADD_SYM := Session.REAL_ADD_SYM
  REAL_INV_INV := Session.REAL_INV_INV
  REAL_INV_MUL := Session.REAL_INV_MUL
  REAL_LET_TRANS := Session.REAL_LET_TRANS
  REAL_LE_LT := SessionLibrary.Analysis.«REAL_LE_LT»
  REAL_LE_MUL := SessionLibrary.Analysis.«REAL_LE_MUL»
  REAL_LE_REFL := SessionLibrary.Analysis.«REAL_LE_REFL»
  REAL_LE_TRANS := SessionLibrary.Analysis.«REAL_LE_TRANS»
  REAL_LTE_TRANS := SessionLibrary.Analysis.«REAL_LTE_TRANS»
  REAL_LT_INV := Session.REAL_LT_INV
  REAL_LT_LE := SessionLibrary.Analysis.«REAL_LT_LE»
  REAL_LT_REFL := Session.REAL_LT_REFL
  REAL_LT_TRANS := Session.REAL_LT_TRANS
  REAL_MAX_MAX := Session.REAL_MAX_MAX
  REAL_MUL_ASSOC := Session.REAL_MUL_ASSOC
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_LZERO := SessionLibrary.Analysis.«REAL_MUL_LZERO»
  REAL_MUL_RID := SessionLibrary.Analysis.«REAL_MUL_RID»
  REAL_MUL_RZERO := SessionLibrary.Analysis.«REAL_MUL_RZERO»
  REAL_MUL_SYM := Session.REAL_MUL_SYM
  REAL_NEG_0 := SessionLibrary.Analysis.«REAL_NEG_0»
  REAL_NEG_MUL2 := SessionLibrary.Analysis.«REAL_NEG_MUL2»
  REAL_NEG_NEG := SessionLibrary.Analysis.«REAL_NEG_NEG»
  REAL_NOT_LE := SessionLibrary.Analysis.«REAL_NOT_LE»
  REAL_NOT_LT := SessionLibrary.Analysis.«REAL_NOT_LT»
  REAL_OF_NUM_LT := Session.REAL_OF_NUM_LT
  REAL_POW_1 := Session.REAL_POW_1
  REAL_POW_ONE := Session.REAL_POW_ONE
  real_div := Session.real_div
  real_ge := Session.real_ge
  real_gt := Session.real_gt
  real_pow := Session.real_pow

/-- What rewrites.ml uses from Session. -/
def deps : HolRQE.Rewrites.RewritesDeps where
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
  suppress := SessionRQE.Util.suppress
  get_type_list := SessionRQE.Util.get_type_list
  set_types := SessionRQE.Util.set_types
  print_term_types := SessionRQE.Util.print_term_types
  print_thm_types := SessionRQE.Util.print_thm_types
  goal_types := SessionRQE.Util.goal_types
  assum := SessionRQE.Util.assum
  assum_types := SessionRQE.Util.assum_types
  get_type := SessionRQE.Util.get_type
  proof_stack := SessionRQE.Util.proof_stack
  push_proof := SessionRQE.Util.push_proof
  pop_proof := SessionRQE.Util.pop_proof
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in rewrites.ml order. -/
initialize BRewritesFns : HolRQE.Rewrites.RewritesFns ←
  ioB "setupRewritesFns" (HolRQE.Rewrites.setupRewritesFns deps).run

-- RewritesFns
def NUM_REWRITES : Option (IO.Ref (List thm)) := BRewritesFns.NUM_REWRITES
def NUM_SIMP_TAC : HolCore.Tactics.tactic := BRewritesFns.NUM_SIMP_TAC
def extend_num_rewrites : List thm → IO Unit := BRewritesFns.extend_num_rewrites
def REAL_REWRITES : Option (IO.Ref (List thm)) := BRewritesFns.REAL_REWRITES
def REAL_ELIM : Option (IO.Ref (List thm)) := BRewritesFns.REAL_ELIM
def REAL_SIMP_TAC : HolCore.Tactics.tactic := BRewritesFns.REAL_SIMP_TAC
def REAL_SOLVE_TAC : HolCore.Tactics.tactic := BRewritesFns.REAL_SOLVE_TAC
def extend_real_rewrites : List thm → IO Unit := BRewritesFns.extend_real_rewrites
def BASIC_REWRITES : Option (IO.Ref (List thm)) := BRewritesFns.BASIC_REWRITES

/-- `needs "Rqe/rewrites.ml"`: already done by importing this module. -/
def ensureRewrites : IO Unit := pure ()

end SessionRQE.Rewrites
