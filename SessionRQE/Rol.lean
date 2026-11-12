/- ---------------------------------------------------------------------- -/
/- Session wiring for Rqe/rol.ml                                        . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionRQE/Rol.lean

  The session half of the rol.ml translation: it supplies HolRQE.Rol's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Rqe/rol.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolRQE.Rol
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionRQE.Rol

/-- The core theorems rol.ml uses. -/
def core1 : HolRQE.Rol.CoreThms1 where
  AND_IMP_THM := SessionRQE.Basic.«AND_IMP_THM»
  APPEND := Session.listDefs.APPEND
  COND_CLAUSES := Session.COND_CLAUSES
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  EL := Session.listDefs.EL
  HD := Session.listDefs.HD
  HD_APPEND := SessionRQE.RqeList.«HD_APPEND»
  LAST := Session.listDefs.LAST
  LAST_CONS := SessionRQE.RqeList.«LAST_CONS»
  LAST_CONS_CONS := SessionRQE.RqeList.«LAST_CONS_CONS»
  LAST_SING := SessionRQE.RqeList.«LAST_SING»
  NOT_CONS_NIL := Session.listThms1.NOT_CONS_NIL
  NOT_NIL := SessionRQE.ListRewrites.«NOT_NIL»
  REAL_DENSE := SessionRQE.RqeReal.«REAL_DENSE»
  REAL_GT_EXISTS := SessionRQE.RqeReal.«REAL_GT_EXISTS»
  REAL_LT_EXISTS := SessionRQE.RqeReal.«REAL_LT_EXISTS»
  REAL_LT_TRANS := Session.REAL_LT_TRANS
  TL := Session.listDefs.TL
  list_RECURSION := Session.list_RECURSION
  real_ge := Session.real_ge
  real_gt := Session.real_gt

/-- What rol.ml uses from Session. -/
def deps : HolRQE.Rol.RolDeps where
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
  NUM_REWRITES := SessionRQE.Rewrites.NUM_REWRITES
  NUM_SIMP_TAC := SessionRQE.Rewrites.NUM_SIMP_TAC
  extend_num_rewrites := SessionRQE.Rewrites.extend_num_rewrites
  REAL_REWRITES := SessionRQE.Rewrites.REAL_REWRITES
  REAL_ELIM := SessionRQE.Rewrites.REAL_ELIM
  REAL_SIMP_TAC := SessionRQE.Rewrites.REAL_SIMP_TAC
  REAL_SOLVE_TAC := SessionRQE.Rewrites.REAL_SOLVE_TAC
  extend_real_rewrites := SessionRQE.Rewrites.extend_real_rewrites
  BASIC_REWRITES := SessionRQE.Rewrites.BASIC_REWRITES
  dest_beq := SessionRQE.Basic.dest_beq
  t_tm := SessionRQE.Basic.t_tm
  f_tm := SessionRQE.Basic.f_tm
  nqt := SessionRQE.Basic.nqt
  mk_neq := SessionRQE.Basic.mk_neq
  neq := SessionRQE.RqeNum.neq
  nlt := SessionRQE.RqeNum.nlt
  ngt := SessionRQE.RqeNum.ngt
  nle := SessionRQE.RqeNum.nle
  nge := SessionRQE.RqeNum.nge
  nm := SessionRQE.RqeNum.nm
  np := SessionRQE.RqeNum.np
  nzero := SessionRQE.RqeNum.nzero
  even_tm := SessionRQE.RqeNum.even_tm
  odd_tm := SessionRQE.RqeNum.odd_tm
  PARITY_CONV := SessionRQE.RqeNum.PARITY_CONV
  real_ty := SessionRQE.RqeReal.real_ty
  rx := SessionRQE.RqeReal.rx
  ry := SessionRQE.RqeReal.ry
  rz := SessionRQE.RqeReal.rz
  req := SessionRQE.RqeReal.req
  rneq := SessionRQE.RqeReal.rneq
  rlt := SessionRQE.RqeReal.rlt
  rgt := SessionRQE.RqeReal.rgt
  rle := SessionRQE.RqeReal.rle
  rge := SessionRQE.RqeReal.rge
  rm := SessionRQE.RqeReal.rm
  rs := SessionRQE.RqeReal.rs
  rn := SessionRQE.RqeReal.rn
  rd := SessionRQE.RqeReal.rd
  rp := SessionRQE.RqeReal.rp
  rzero := SessionRQE.RqeReal.rzero
  rone := SessionRQE.RqeReal.rone
  rlast := SessionRQE.RqeReal.rlast
  rappend := SessionRQE.RqeReal.rappend
  mk_rlist := SessionRQE.RqeReal.mk_rlist
  diffl_tm := SessionRQE.RqeReal.diffl_tm
  dest_diffl := SessionRQE.RqeReal.dest_diffl
  dest_mult := SessionRQE.RqeReal.dest_mult
  mk_mult := SessionRQE.RqeReal.mk_mult
  pow_tm := SessionRQE.RqeReal.pow_tm
  dest_pow := SessionRQE.RqeReal.dest_pow
  mk_plus := SessionRQE.RqeReal.mk_plus
  mk_negative := SessionRQE.RqeReal.mk_negative
  dest_plus := SessionRQE.RqeReal.dest_plus
  LIST_REWRITES := SessionRQE.ListRewrites.LIST_REWRITES
  LIST_SIMP_TAC := SessionRQE.ListRewrites.LIST_SIMP_TAC
  extend_list_rewrites := SessionRQE.ListRewrites.extend_list_rewrites
  aacons_tm := SessionRQE.RqeList.aacons_tm
  HD_CONV := SessionRQE.RqeList.HD_CONV
  TL_CONV := SessionRQE.RqeList.TL_CONV
  EL_CONV := SessionRQE.RqeList.EL_CONV
  testform_timer := SessionRQE.Timers.testform_timer
  combine_testforms_timer := SessionRQE.Timers.combine_testforms_timer
  condense_timer := SessionRQE.Timers.condense_timer
  inferisign_timer := SessionRQE.Timers.inferisign_timer
  matinsert_timer := SessionRQE.Timers.matinsert_timer
  inferpsign_timer := SessionRQE.Timers.inferpsign_timer
  remove_column1_timer := SessionRQE.Timers.remove_column1_timer
  add_infinities_timer := SessionRQE.Timers.add_infinities_timer
  remove_infinities_timer := SessionRQE.Timers.remove_infinities_timer
  pdivides_timer := SessionRQE.Timers.pdivides_timer
  duplicate_columns_timer := SessionRQE.Timers.duplicate_columns_timer
  unmonicize_mat_timer := SessionRQE.Timers.unmonicize_mat_timer
  swap_head_col_timer := SessionRQE.Timers.swap_head_col_timer
  replace_pol_timer := SessionRQE.Timers.replace_pol_timer
  unfactor_mat_timer := SessionRQE.Timers.unfactor_mat_timer
  reset_timers := SessionRQE.Timers.reset_timers
  print_timers := SessionRQE.Timers.print_timers
  arith_ss := SessionRQE.NumCalcSimp.arith_ss
  ARITH_SIMP_CONV := SessionRQE.NumCalcSimp.ARITH_SIMP_CONV
  arith_net := SessionRQE.NumCalcSimp.arith_net
  ARITH_REWRITE_CONV := SessionRQE.NumCalcSimp.ARITH_REWRITE_CONV
  ARITH_SIMP_TAC := SessionRQE.NumCalcSimp.ARITH_SIMP_TAC
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in rol.ml order. -/
initialize BRolFns : HolRQE.Rol.RolFns ←
  ioB "setupRolFns" (HolRQE.Rol.setupRolFns deps).run

-- RolFns
def real_ordered_list : thm := BRolFns.real_ordered_list
def ROL_EMPTY : thm := BRolFns.ROL_EMPTY
def ROL_SING : thm := BRolFns.ROL_SING
def ROL_TAIL : thm := BRolFns.ROL_TAIL
def EL_CONS : thm := BRolFns.EL_CONS
def NOT_ROL : thm := BRolFns.NOT_ROL
def ROL_CONS : thm := BRolFns.ROL_CONS
def ROL_CONS_CONS : thm := BRolFns.ROL_CONS_CONS
def ROL_APPEND : thm := BRolFns.ROL_APPEND
def ROL_CONS_CONS_LT : thm := BRolFns.ROL_CONS_CONS_LT
def ROL_INSERT_THM : thm := BRolFns.ROL_INSERT_THM
def ROL_INSERT_FRONT_THM : thm := BRolFns.ROL_INSERT_FRONT_THM
def ROL_CONS_CONS_DELETE : thm := BRolFns.ROL_CONS_CONS_DELETE
def LAST_CONS_LT : thm := BRolFns.LAST_CONS_LT
def ROL_INSERT_BACK_THM : thm := BRolFns.ROL_INSERT_BACK_THM
def CHOP_REAL_LIST : Int → term → ExceptT String IO thm := BRolFns.CHOP_REAL_LIST
def ROL_CHOP_LT : Int → thm → ExceptT String IO thm := BRolFns.ROL_CHOP_LT
def t1 : thm := BRolFns.t1
def ROL_CHOP_LIST : Int → thm → ExceptT String IO (thm × thm × thm) := BRolFns.ROL_CHOP_LIST
def lem1 : thm := BRolFns.lem1
def ROL_INSERT_MIDDLE : thm → thm → ExceptT String IO thm := BRolFns.ROL_INSERT_MIDDLE
def ROL_INSERT_FRONT : thm → thm → ExceptT String IO thm := BRolFns.ROL_INSERT_FRONT
def ROL_INSERT_BACK : thm → thm → ExceptT String IO thm := BRolFns.ROL_INSERT_BACK
def ROL_INSERT : thm → thm → ExceptT String IO thm := BRolFns.ROL_INSERT
def rol_thms : thm → ExceptT String IO (List thm) := BRolFns.rol_thms
def lem : thm := BRolFns.lem
def lem0 : thm := BRolFns.lem0
def rol_nonempty_thms : thm → ExceptT String IO (List thm) := BRolFns.rol_nonempty_thms
def lem2 : thm := BRolFns.lem2
def mk_rol : List thm → ExceptT String IO thm := BRolFns.mk_rol
def real_nil : term := BRolFns.real_nil
def ROL_NIL : thm := BRolFns.ROL_NIL
def ROL_REMOVE : term → thm → ExceptT String IO thm := BRolFns.ROL_REMOVE
def ROL_COVERS : thm → ExceptT String IO thm := BRolFns.ROL_COVERS

/-- `needs "Rqe/rol.ml"`: already done by importing this module. -/
def ensureRol : IO Unit := pure ()

end SessionRQE.Rol
