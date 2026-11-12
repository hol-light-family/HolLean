/- ---------------------------------------------------------------------- -/
/- Session wiring for Rqe/pdivides_thms.ml                              . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionRQE/PdividesThms.lean

  The session half of the pdivides_thms.ml translation: it supplies HolRQE.PdividesThms's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Rqe/pdivides_thms.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolRQE.PdividesThms
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionRQE.PdividesThms

/-- The core theorems pdivides_thms.ml uses. -/
def core1 : HolRQE.PdividesThms.CoreThms1 where
  NOT_ODD := Session.NOT_ODD
  ODD := Session.ODD
  REAL_POW_NEG := Session.REAL_POW_NEG
  num_CASES := Session.num_CASES
  real_pow := Session.real_pow

/-- What pdivides_thms.ml uses from Session. -/
def deps : HolRQE.PdividesThms.PdividesThmsDeps where
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
  t_tm := SessionRQE.LiftQelim.t_tm
  f_tm := SessionRQE.LiftQelim.f_tm
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
  ACI_CONJ := SessionRQE.LiftQelim.ACI_CONJ
  QE_SIMPLIFY_CONV := SessionRQE.LiftQelim.QE_SIMPLIFY_CONV
  or_exists_conv := SessionRQE.LiftQelim.or_exists_conv
  triv_exists_conv := SessionRQE.LiftQelim.triv_exists_conv
  push_exists_conv := SessionRQE.LiftQelim.push_exists_conv
  not_tm := SessionRQE.LiftQelim.not_tm
  or_tm := SessionRQE.LiftQelim.or_tm
  LIFT_QELIM_CONV := SessionRQE.LiftQelim.LIFT_QELIM_CONV
  sunk_tm := SessionRQE.Defs.sunk_tm
  snonz_tm := SessionRQE.Defs.snonz_tm
  sneg_tm := SessionRQE.Defs.sneg_tm
  spos_tm := SessionRQE.Defs.spos_tm
  szero_tm := SessionRQE.Defs.szero_tm
  interpsign_tm := SessionRQE.Defs.interpsign_tm
  dest_interpsign := SessionRQE.Defs.dest_interpsign
  interpsigns_thms := SessionRQE.Defs.interpsigns_thms
  interpsigns_thms2 := SessionRQE.Defs.interpsigns_thms2
  interpsigns_tm := SessionRQE.Defs.interpsigns_tm
  dest_interpsigns := SessionRQE.Defs.dest_interpsigns
  mk_interpsigns := SessionRQE.Defs.mk_interpsigns
  make_partition_list := SessionRQE.Defs.make_partition_list
  part_line_tm := SessionRQE.Defs.part_line_tm
  real_bool_ty := SessionRQE.Defs.real_bool_ty
  PARTITION_LINE_CONV := SessionRQE.Defs.PARTITION_LINE_CONV
  interpmat_tm := SessionRQE.Defs.interpmat_tm
  dest_interpmat := SessionRQE.Defs.dest_interpmat
  interpmat_thms := SessionRQE.Defs.interpmat_thms
  mk_interpmat_thm := SessionRQE.Defs.mk_interpmat_thm
  mk_all2_interpsigns := SessionRQE.Defs.mk_all2_interpsigns
  dest_all2 := SessionRQE.Defs.dest_all2
  is_interval := SessionRQE.Defs.is_interval
  is_point := SessionRQE.Defs.is_point
  new_var := SessionRQE.Defs.new_var
  reset_vars := SessionRQE.Defs.reset_vars
  sz_z_thm := SessionRQE.SignsThms.sz_z_thm
  sz_nz_thm := SessionRQE.SignsThms.sz_nz_thm
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in pdivides_thms.ml order. -/
initialize BPdividesThmsThms : HolRQE.PdividesThms.PdividesThmsThms ←
  ioB "setupPdividesThmsThms" (HolRQE.PdividesThms.setupPdividesThmsThms deps).run

-- PdividesThmsThms
def neg_odd_lem : thm := BPdividesThmsThms.neg_odd_lem
def mul_odd_lem : thm := BPdividesThmsThms.mul_odd_lem

/-- `needs "Rqe/pdivides_thms.ml"`: already done by importing this module. -/
def ensurePdividesThms : IO Unit := pure ()

end SessionRQE.PdividesThms
