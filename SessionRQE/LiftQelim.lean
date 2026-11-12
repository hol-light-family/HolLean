/- ---------------------------------------------------------------------- -/
/- Session wiring for Rqe/lift_qelim.ml                                 . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionRQE/LiftQelim.lean

  The session half of the lift_qelim.ml translation: it supplies HolRQE.LiftQelim's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Rqe/lift_qelim.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolRQE.LiftQelim
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionRQE.LiftQelim

/-- The core theorems lift_qelim.ml uses. -/
def core1 : HolRQE.LiftQelim.CoreThms1 where
  CONJ_ASSOC := Session.CONJ_ASSOC
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  EXISTS_SIMP := Session.EXISTS_SIMP
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  OR_EXISTS_THM := Session.OR_EXISTS_THM
  RIGHT_EXISTS_AND_THM := Session.RIGHT_EXISTS_AND_THM
  t1 := SessionRQE.Rol.«t1»

/-- What lift_qelim.ml uses from Session. -/
def deps : HolRQE.LiftQelim.LiftQelimDeps where
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
  CHOP_REAL_LIST := SessionRQE.Rol.CHOP_REAL_LIST
  ROL_CHOP_LT := SessionRQE.Rol.ROL_CHOP_LT
  ROL_CHOP_LIST := SessionRQE.Rol.ROL_CHOP_LIST
  ROL_INSERT_MIDDLE := SessionRQE.Rol.ROL_INSERT_MIDDLE
  ROL_INSERT_FRONT := SessionRQE.Rol.ROL_INSERT_FRONT
  ROL_INSERT_BACK := SessionRQE.Rol.ROL_INSERT_BACK
  ROL_INSERT := SessionRQE.Rol.ROL_INSERT
  rol_thms := SessionRQE.Rol.rol_thms
  rol_nonempty_thms := SessionRQE.Rol.rol_nonempty_thms
  mk_rol := SessionRQE.Rol.mk_rol
  real_nil := SessionRQE.Rol.real_nil
  ROL_REMOVE := SessionRQE.Rol.ROL_REMOVE
  ROL_COVERS := SessionRQE.Rol.ROL_COVERS
  poly_tm := SessionRQE.PolyExt.poly_tm
  dest_poly := SessionRQE.PolyExt.dest_poly
  is_poly := SessionRQE.PolyExt.is_poly
  polyvar := SessionRQE.PolyExt.polyvar
  is_constant := SessionRQE.PolyExt.is_constant
  POLY_ENLIST_CONV := SessionRQE.PolyExt.POLY_ENLIST_CONV
  POLY_DELIST_CONV := SessionRQE.PolyExt.POLY_DELIST_CONV
  CANON_POLY_DIFF_CONV := SessionRQE.PolyExt.CANON_POLY_DIFF_CONV
  POLY_ADD_CONV := SessionRQE.PolyExt.POLY_ADD_CONV
  POLY_NEG_CONV := SessionRQE.PolyExt.POLY_NEG_CONV
  POLY_SUB_CONV := SessionRQE.PolyExt.POLY_SUB_CONV
  POLY_MUL_CONV := SessionRQE.PolyExt.POLY_MUL_CONV
  POLY_POW_CONV := SessionRQE.PolyExt.POLY_POW_CONV
  POLYNATE_CONV := SessionRQE.PolyExt.POLYNATE_CONV
  poly_add_ := SessionRQE.PolyExt.poly_add_
  poly_sub_ := SessionRQE.PolyExt.poly_sub_
  poly_mul_ := SessionRQE.PolyExt.poly_mul_
  poly_neg_ := SessionRQE.PolyExt.poly_neg_
  poly_pow_ := SessionRQE.PolyExt.poly_pow_
  degree_ := SessionRQE.PolyExt.degree_
  coefficients := SessionRQE.PolyExt.coefficients
  head := SessionRQE.PolyExt.head
  behead := SessionRQE.PolyExt.behead
  BEHEAD3 := SessionRQE.PolyExt.BEHEAD3
  BEHEAD := SessionRQE.PolyExt.BEHEAD
  is_const_poly := SessionRQE.PolyExt.is_const_poly
  MONIC_CONV := SessionRQE.PolyExt.MONIC_CONV
  PDIVIDE := SessionRQE.PolyExt.PDIVIDE
  SIGN_CONST := SessionRQE.PolyExt.SIGN_CONST
  POLY_DERIV_CONV := SessionRQE.PolyExt.POLY_DERIV_CONV
  POLYATOM_CONV := SessionRQE.PolyExt.POLYATOM_CONV
  weakfactor := SessionRQE.PolyExt.weakfactor
  poly_var := SessionRQE.PolyExt.poly_var
  SIMP_POW_CONV := SessionRQE.PolyExt.SIMP_POW_CONV
  WEAKFACTOR_CONV := SessionRQE.PolyExt.WEAKFACTOR_CONV
  PSIMPLIFY1_CONV := SessionRQE.Simplify.PSIMPLIFY1_CONV
  SIMPLIFY1_CONV := SessionRQE.Simplify.SIMPLIFY1_CONV
  SIMPLIFY_CONV := SessionRQE.Simplify.SIMPLIFY_CONV
  REAL_LEAF_CONV := SessionRQE.Simplify.REAL_LEAF_CONV
  EVALC_CONV := SessionRQE.Simplify.EVALC_CONV
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in lift_qelim.ml order. -/
initialize BLiftQelimFns : HolRQE.LiftQelim.LiftQelimFns ←
  ioB "setupLiftQelimFns" (HolRQE.LiftQelim.setupLiftQelimFns deps).run

-- LiftQelimFns
def ACI_CONJ : term → term → ExceptT String IO thm := BLiftQelimFns.ACI_CONJ
def QE_SIMPLIFY_CONV : HolCore.Equal.ioconv := BLiftQelimFns.QE_SIMPLIFY_CONV
def OR_ASSOC : thm := BLiftQelimFns.OR_ASSOC
def forall_thm : thm := BLiftQelimFns.forall_thm
def or_exists_conv : HolCore.Equal.ioconv := BLiftQelimFns.or_exists_conv
def triv_exists_conv : HolCore.Equal.ioconv := BLiftQelimFns.triv_exists_conv
def push_exists_conv : HolCore.Equal.ioconv := BLiftQelimFns.push_exists_conv
def not_tm : term := BLiftQelimFns.not_tm
def or_tm : term := BLiftQelimFns.or_tm
def t_tm : term := BLiftQelimFns.t_tm
def f_tm : term := BLiftQelimFns.f_tm
def LIFT_QELIM_CONV : (List term → HolCore.Equal.ioconv) → HolCore.Equal.ioconv → (List term → HolCore.Equal.ioconv) → HolCore.Equal.ioconv := BLiftQelimFns.LIFT_QELIM_CONV

/-- `needs "Rqe/lift_qelim.ml"`: already done by importing this module. -/
def ensureLiftQelim : IO Unit := pure ()

end SessionRQE.LiftQelim
