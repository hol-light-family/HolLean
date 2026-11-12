/- ---------------------------------------------------------------------- -/
/- Session wiring for Rqe/work_thms.ml                                  . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionRQE/WorkThms.lean

  The session half of the work_thms.ml translation: it supplies HolRQE.WorkThms's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Rqe/work_thms.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolRQE.WorkThms
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionRQE.WorkThms

/-- The core theorems work_thms.ml uses. -/
def core1 : HolRQE.WorkThms.CoreThms1 where
  ALL := Session.listDefs.ALL
  ALL2 := Session.listDefs.ALL2
  APPEND := Session.listDefs.APPEND
  APPEND_EQ_NIL := Session.listThms2.APPEND_EQ_NIL
  APPEND_NIL := Session.listThms1.APPEND_NIL
  BUTLAST := Session.listDefs.BUTLAST
  CONS_11 := Session.listThms1.CONS_11
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIVISION := Session.DIVISION
  EL := Session.listDefs.EL
  EVEN_MOD := Session.EVEN_MOD
  EVEN_ODD_POW := SessionRQE.RqeReal.«EVEN_ODD_POW»
  FUN_EQ_THM := Session.FUN_EQ_THM
  GT := Session.GT
  HD := Session.listDefs.HD
  IMP_AND_THM := SessionRQE.Basic.«IMP_AND_THM»
  IN := Session.IN
  INTERPSIGNS_SUBSET := SessionRQE.DedmatrixThms.«INTERPSIGNS_SUBSET»
  INTERPSIGN_SUBSET := SessionRQE.DedmatrixThms.«INTERPSIGN_SUBSET»
  LAST := Session.listDefs.LAST
  LENGTH := Session.listDefs.LENGTH
  LENGTH_0 := SessionRQE.RqeList.«LENGTH_0»
  LENGTH_1 := SessionRQE.RqeList.«LENGTH_1»
  LENGTH_APPEND := Session.listThms1.LENGTH_APPEND
  LENGTH_EQ_NIL := Session.listThms1.LENGTH_EQ_NIL
  LENGTH_MAP := Session.listThms1.LENGTH_MAP
  LENGTH_MAP2 := Session.listThms2.LENGTH_MAP2
  LENGTH_PAIR := SessionRQE.RqeList.«LENGTH_PAIR»
  LENGTH_REPLICATE := Session.listThms1.LENGTH_REPLICATE
  LENGTH_SING := SessionRQE.RqeList.«LENGTH_SING»
  LET_TRANS := Session.LET_TRANS
  LE_SUC := Session.LE_SUC
  LTE_TRANS := Session.LTE_TRANS
  LT_0 := Session.LT_0
  LT_IMP_LE := Session.LT_IMP_LE
  LT_SUC := Session.LT_SUC
  LT_TRANS := Session.LT_TRANS
  MAP := Session.listDefs.MAP
  MAP2 := Session.listDefs.MAP2
  MEM := Session.listDefs.MEM
  NOT_CONS_NIL := Session.listThms1.NOT_CONS_NIL
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_LE := Session.NOT_LE
  NOT_NIL := SessionRQE.ListRewrites.«NOT_NIL»
  NOT_ODD := Session.NOT_ODD
  NOT_SUC := Session.NOT_SUC
  ODD := Session.ODD
  ONE := Session.ONE
  POLY_DIFF_DOWN_LEFT5 := SessionRQE.Asym.«POLY_DIFF_DOWN_LEFT5»
  POLY_DIFF_DOWN_RIGHT3 := SessionRQE.Asym.«POLY_DIFF_DOWN_RIGHT3»
  POLY_DIFF_UP_LEFT5 := SessionRQE.Asym.«POLY_DIFF_UP_LEFT5»
  POLY_DIFF_UP_RIGHT3 := SessionRQE.Asym.«POLY_DIFF_UP_RIGHT3»
  PRE := Session.PRE
  REAL_ADD_LID := Session.REAL_ADD_LID
  REAL_ENTIRE := Session.REAL_ENTIRE
  REAL_EQ_IMP_LE := Session.REAL_EQ_IMP_LE
  REAL_LT_IMP_LE := SessionLibrary.Analysis.«REAL_LT_IMP_LE»
  REAL_LT_IMP_NZ := SessionLibrary.Analysis.«REAL_LT_IMP_NZ»
  REAL_LT_TRANS := Session.REAL_LT_TRANS
  REAL_MUL_GT := SessionRQE.RqeReal.«REAL_MUL_GT»
  REAL_MUL_LT := SessionRQE.RqeReal.«REAL_MUL_LT»
  REAL_MUL_RZERO := SessionLibrary.Analysis.«REAL_MUL_RZERO»
  REAL_POW_LT := Session.REAL_POW_LT
  REPLICATE := Session.listDefs.REPLICATE
  ROL_APPEND := SessionRQE.Rol.«ROL_APPEND»
  ROL_CONS_CONS := SessionRQE.Rol.«ROL_CONS_CONS»
  ROL_CONS_CONS_DELETE := SessionRQE.Rol.«ROL_CONS_CONS_DELETE»
  ROL_INSERT_BACK_THM := SessionRQE.Rol.«ROL_INSERT_BACK_THM»
  ROL_NIL := SessionRQE.Rol.«ROL_NIL»
  ROL_SING := SessionRQE.Rol.«ROL_SING»
  ROL_TAIL := SessionRQE.Rol.«ROL_TAIL»
  SIGN_CASES := SessionRQE.Defs.«SIGN_CASES»
  SUBSET := Session.SUBSET
  SUC_INJ := Session.SUC_INJ
  TL := Session.listDefs.TL
  eq_eq_false_thm := SessionRQE.InferisignThms.«eq_eq_false_thm»
  interpmat := SessionRQE.Defs.«interpmat»
  interpsign := SessionRQE.Defs.«interpsign»
  interpsigns := SessionRQE.Defs.«interpsigns»
  list_CASES := Session.listThms1.list_CASES
  list_RECURSION := Session.list_RECURSION
  neg_neg_neq_thm := SessionRQE.InferisignThms.«neg_neg_neq_thm»
  neg_pos_neq_thm := SessionRQE.InferisignThms.«neg_pos_neq_thm»
  neg_zero_neg_thm := SessionRQE.InferisignThms.«neg_zero_neg_thm»
  num_CASES := Session.num_CASES
  num_RECURSION := Session.num_RECURSION
  partition_line := SessionRQE.Defs.«partition_line»
  pos_neg_neq_thm := SessionRQE.InferisignThms.«pos_neg_neq_thm»
  pos_pos_neq_thm := SessionRQE.InferisignThms.«pos_pos_neq_thm»
  pos_zero_pos_thm := SessionRQE.InferisignThms.«pos_zero_pos_thm»
  real_gt := Session.real_gt
  real_ordered_list := SessionRQE.Rol.«real_ordered_list»
  zero_neg_neg_thm := SessionRQE.InferisignThms.«zero_neg_neg_thm»
  zero_pos_pos_thm := SessionRQE.InferisignThms.«zero_pos_pos_thm»

/-- What work_thms.ml uses from Session. -/
def deps : HolRQE.WorkThms.WorkThmsDeps where
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
  mk_small_numeral := Session.mk_small_numeral
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
  empty_sgns := SessionRQE.MainThms.empty_sgns
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in work_thms.ml order. -/
initialize BWorkThms01 : HolRQE.WorkThms.WorkThms01 ←
  ioB "setupWorkThms01" (HolRQE.WorkThms.setupWorkThms01 deps).run
initialize BWorkThms02 : HolRQE.WorkThms.WorkThms02 ←
  ioB "setupWorkThms02" (HolRQE.WorkThms.setupWorkThms02 deps BWorkThms01).run
initialize BWorkThms03 : HolRQE.WorkThms.WorkThms03 ←
  ioB "setupWorkThms03" (HolRQE.WorkThms.setupWorkThms03 deps BWorkThms01 BWorkThms02).run
initialize BWorkThms04 : HolRQE.WorkThms.WorkThms04 ←
  ioB "setupWorkThms04" (HolRQE.WorkThms.setupWorkThms04 deps BWorkThms01 BWorkThms02).run
initialize BWorkThms05 : HolRQE.WorkThms.WorkThms05 ←
  ioB "setupWorkThms05" (HolRQE.WorkThms.setupWorkThms05 deps BWorkThms01).run
initialize BWorkThms06 : HolRQE.WorkThms.WorkThms06 ←
  ioB "setupWorkThms06" (HolRQE.WorkThms.setupWorkThms06 deps BWorkThms01 BWorkThms02 BWorkThms05).run
initialize BWorkThms07 : HolRQE.WorkThms.WorkThms07 ←
  ioB "setupWorkThms07" (HolRQE.WorkThms.setupWorkThms07 deps BWorkThms01 BWorkThms06).run
initialize BWorkThms08 : HolRQE.WorkThms.WorkThms08 ←
  ioB "setupWorkThms08" (HolRQE.WorkThms.setupWorkThms08 deps BWorkThms01 BWorkThms02).run
initialize BWorkThms09 : HolRQE.WorkThms.WorkThms09 ←
  ioB "setupWorkThms09" (HolRQE.WorkThms.setupWorkThms09 deps BWorkThms01 BWorkThms08).run
initialize BWorkThms10 : HolRQE.WorkThms.WorkThms10 ←
  ioB "setupWorkThms10" (HolRQE.WorkThms.setupWorkThms10 deps BWorkThms01 BWorkThms08).run

-- WorkThms01
def INTERPSIGNS_CONJ : thm := BWorkThms01.INTERPSIGNS_CONJ
def INTERPMAT_TRIO : thm := BWorkThms01.INTERPMAT_TRIO
def PARTITION_LINE_NOT_NIL : thm := BWorkThms01.PARTITION_LINE_NOT_NIL
def ALL2_LENGTH : thm := BWorkThms01.ALL2_LENGTH
def LENGTH_TL : thm := BWorkThms01.LENGTH_TL
def PARTITION_LINE_LENGTH : thm := BWorkThms01.PARTITION_LINE_LENGTH
def PARTITION_LINE_LENGTH_TL : thm := BWorkThms01.PARTITION_LINE_LENGTH_TL
def PL_ALL2_LENGTH : thm := BWorkThms01.PL_ALL2_LENGTH
def INTERPMAT_LENGTH : thm := BWorkThms01.INTERPMAT_LENGTH
def ALL2_HD : thm := BWorkThms01.ALL2_HD
def ALL2_TL : thm := BWorkThms01.ALL2_TL
def ALL2_APPEND_LENGTH : thm := BWorkThms01.ALL2_APPEND_LENGTH
def ALL2_APPEND : thm := BWorkThms01.ALL2_APPEND
def ALL2_SPLIT : thm := BWorkThms01.ALL2_SPLIT
def BUTLAST_THM : thm := BWorkThms01.BUTLAST_THM
def HD_BUTLAST : thm := BWorkThms01.HD_BUTLAST
def SUBLIST : thm := BWorkThms01.SUBLIST
def SUBLIST_NIL : thm := BWorkThms01.SUBLIST_NIL
def SUBLIST_CONS : thm := BWorkThms01.SUBLIST_CONS
def SUBLIST_TL : thm := BWorkThms01.SUBLIST_TL
def SUBLIST_CONS2 : thm := BWorkThms01.SUBLIST_CONS2
def SUBLIST_ID : thm := BWorkThms01.SUBLIST_ID
def SUBLIST_CONS_CONS : thm := BWorkThms01.SUBLIST_CONS_CONS
def SUBLIST_NEQ : thm := BWorkThms01.SUBLIST_NEQ
def SUBLIST_TRANS : thm := BWorkThms01.SUBLIST_TRANS
def ROL_MEM : thm := BWorkThms01.ROL_MEM
def SUBLIST_MEM : thm := BWorkThms01.SUBLIST_MEM
def ROL_SUBLIST_LT : thm := BWorkThms01.ROL_SUBLIST_LT
def SUBLIST_DELETE : thm := BWorkThms01.SUBLIST_DELETE
def SUBLIST_MATCH : thm := BWorkThms01.SUBLIST_MATCH
def ROL_SUBLIST : thm := BWorkThms01.ROL_SUBLIST
def SUBLIST_BUTLAST : thm := BWorkThms01.SUBLIST_BUTLAST
def SUBLIST_APPEND_HD : thm := BWorkThms01.SUBLIST_APPEND_HD
def SUBLIST_ID_CONS : thm := BWorkThms01.SUBLIST_ID_CONS
def SUBLIST_ID_APPEND : thm := BWorkThms01.SUBLIST_ID_APPEND
def SUBLIST_APPEND_TL : thm := BWorkThms01.SUBLIST_APPEND_TL
def SUBLIST_TRANS2 : thm := BWorkThms01.SUBLIST_TRANS2
def APPEND_CONS : thm := BWorkThms01.APPEND_CONS
def SUBLIST_APPEND : thm := BWorkThms01.SUBLIST_APPEND
def SUBLIST_APPEND2 : thm := BWorkThms01.SUBLIST_APPEND2
def ROL_APPEND2 : thm := BWorkThms01.ROL_APPEND2
def PL_LEM : thm := BWorkThms01.PL_LEM
def HD_APPEND2 : thm := BWorkThms01.HD_APPEND2
def BUTLAST_TL : thm := BWorkThms01.BUTLAST_TL
def APPEND_TL : thm := BWorkThms01.APPEND_TL
def APPEND_HD : thm := BWorkThms01.APPEND_HD
def PL_LEM2 : thm := BWorkThms01.PL_LEM2
def BUTLAST_APPEND : thm := BWorkThms01.BUTLAST_APPEND
def LENGTH_TL1 : thm := BWorkThms01.LENGTH_TL1
def PL_BUTLAST : thm := BWorkThms01.PL_BUTLAST
def PARTITION_LINE_APPEND : thm := BWorkThms01.PARTITION_LINE_APPEND
def HD_TL : thm := BWorkThms01.HD_TL
def HD_LEM : thm := BWorkThms01.HD_LEM
def LENGTH_N : Int → hol_type → ExceptT String IO thm := BWorkThms01.LENGTH_N
def BUTLAST_LENGTH : thm := BWorkThms01.BUTLAST_LENGTH

-- WorkThms02
def ALL2_LEM : thm := BWorkThms02.ALL2_LEM
def INTERPMAT_TRIO_TL : thm := BWorkThms02.INTERPMAT_TRIO_TL
def LAST_APPEND : thm := BWorkThms02.LAST_APPEND
def APPEND_APPEND : thm := BWorkThms02.APPEND_APPEND
def ALL2_LEM2 : thm := BWorkThms02.ALL2_LEM2
def INTERPMAT_TRIO_INNER : thm := BWorkThms02.INTERPMAT_TRIO_INNER
def INTERPMAT_SING : thm := BWorkThms02.INTERPMAT_SING
def INFERISIGN_POS_POS_POS : thm := BWorkThms02.INFERISIGN_POS_POS_POS
def INFERISIGN_POS_POS_NEG : thm := BWorkThms02.INFERISIGN_POS_POS_NEG
def INFERISIGN_NEG_NEG_POS : thm := BWorkThms02.INFERISIGN_NEG_NEG_POS
def INFERISIGN_NEG_NEG_NEG : thm := BWorkThms02.INFERISIGN_NEG_NEG_NEG
def ALL2_INTERPSIGN_SUBSET : thm := BWorkThms02.ALL2_INTERPSIGN_SUBSET
def HD_APPEND1 : thm := BWorkThms02.HD_APPEND1
def ROL_APPEND_INSERT : thm := BWorkThms02.ROL_APPEND_INSERT

-- WorkThms03
def INFERISIGN_POS_NEG_POS : thm := BWorkThms03.INFERISIGN_POS_NEG_POS
def INFERISIGN_POS_NEG_NEG : thm := BWorkThms03.INFERISIGN_POS_NEG_NEG
def INFERISIGN_NEG_POS_NEG : thm := BWorkThms03.INFERISIGN_NEG_POS_NEG

-- WorkThms04
def INFERISIGN_NEG_POS_POS : thm := BWorkThms04.INFERISIGN_NEG_POS_POS
def INFERISIGN_ZERO_POS_POS : thm := BWorkThms04.INFERISIGN_ZERO_POS_POS
def INFERISIGN_ZERO_POS_NEG : thm := BWorkThms04.INFERISIGN_ZERO_POS_NEG
def INFERISIGN_POS_ZERO_POS : thm := BWorkThms04.INFERISIGN_POS_ZERO_POS
def INFERISIGN_POS_ZERO_NEG : thm := BWorkThms04.INFERISIGN_POS_ZERO_NEG

-- WorkThms05
def INFERISIGN_ZERO_NEG_POS : thm := BWorkThms05.INFERISIGN_ZERO_NEG_POS
def INFERISIGN_ZERO_NEG_NEG : thm := BWorkThms05.INFERISIGN_ZERO_NEG_NEG
def INFERISIGN_NEG_ZERO_NEG : thm := BWorkThms05.INFERISIGN_NEG_ZERO_NEG
def INFERISIGN_NEG_ZERO_POS : thm := BWorkThms05.INFERISIGN_NEG_ZERO_POS
def INFERISIGN_ZERO_ZERO_POS : thm := BWorkThms05.INFERISIGN_ZERO_ZERO_POS
def INFERISIGN_ZERO_ZERO_NEG : thm := BWorkThms05.INFERISIGN_ZERO_ZERO_NEG
def BUTLAST_ID : thm := BWorkThms05.BUTLAST_ID
def BUTLAST_NIL : thm := BWorkThms05.BUTLAST_NIL

-- WorkThms06
def INFIN_HD_POS_LEM : thm := BWorkThms06.INFIN_HD_POS_LEM
def INFIN_TL_POS_LEM : thm := BWorkThms06.INFIN_TL_POS_LEM
def INFIN_HD_NEG_LEM : thm := BWorkThms06.INFIN_HD_NEG_LEM
def INFIN_TL_NEG_LEM : thm := BWorkThms06.INFIN_TL_NEG_LEM
def INFIN_POS_POS : thm := BWorkThms06.INFIN_POS_POS
def INFIN_POS_NEG : thm := BWorkThms06.INFIN_POS_NEG
def INFIN_NEG_POS : thm := BWorkThms06.INFIN_NEG_POS
def INFIN_NEG_NEG : thm := BWorkThms06.INFIN_NEG_NEG
def INFIN_NIL_POS : thm := BWorkThms06.INFIN_NIL_POS
def INFIN_NIL_NEG : thm := BWorkThms06.INFIN_NIL_NEG
def INFIN_SING_POS_POS : thm := BWorkThms06.INFIN_SING_POS_POS
def INFIN_SING_POS_NEG : thm := BWorkThms06.INFIN_SING_POS_NEG
def INFIN_SING_NEG_POS : thm := BWorkThms06.INFIN_SING_NEG_POS
def INFIN_SING_NEG_NEG : thm := BWorkThms06.INFIN_SING_NEG_NEG
def EL_SUC : thm := BWorkThms06.EL_SUC
def EL_PRE : thm := BWorkThms06.EL_PRE
def ALL2_EL_LT_LEM : thm := BWorkThms06.ALL2_EL_LT_LEM
def ALL2_EL_LT : thm := BWorkThms06.ALL2_EL_LT

-- WorkThms07
def ALL2_EL_LEM : thm := BWorkThms07.ALL2_EL_LEM
def ALL2_EL : thm := BWorkThms07.ALL2_EL
def EL_MAP : thm := BWorkThms07.EL_MAP
def REMOVE_HD_COL : thm := BWorkThms07.REMOVE_HD_COL
def REMOVE_COL1 : thm := BWorkThms07.REMOVE_COL1
def ALL_EL : thm := BWorkThms07.ALL_EL
def INTERPMAT_POL_LENGTH_LEM : thm := BWorkThms07.INTERPMAT_POL_LENGTH_LEM
def INTERPMAT_POL_LENGTH : thm := BWorkThms07.INTERPMAT_POL_LENGTH
def ALL2_BUTLAST : thm := BWorkThms07.ALL2_BUTLAST
def REMOVE_LAST : thm := BWorkThms07.REMOVE_LAST
def INSERTAT : thm := BWorkThms07.INSERTAT
def MAP2_EL_LEM : thm := BWorkThms07.MAP2_EL_LEM
def MAP2_EL : thm := BWorkThms07.MAP2_EL
def INSERTAT_LENGTH : thm := BWorkThms07.INSERTAT_LENGTH
def NUM_CASES_TAC : term → HolCore.Tactics.tactic := BWorkThms07.NUM_CASES_TAC
def INSERTAT_TL : thm := BWorkThms07.INSERTAT_TL
def INSERTAT_EL : thm := BWorkThms07.INSERTAT_EL
def MATINSERT_THM : thm := BWorkThms07.MATINSERT_THM
def INTERP_CONST_POS : thm := BWorkThms07.INTERP_CONST_POS
def INTERP_CONST_NEG : thm := BWorkThms07.INTERP_CONST_NEG
def INTERP_CONST_ZERO : thm := BWorkThms07.INTERP_CONST_ZERO
def EL_REPLICATE : thm := BWorkThms07.EL_REPLICATE
def ALL2_UNKNOWN : thm := BWorkThms07.ALL2_UNKNOWN
def MATINSERT_THM2 : thm := BWorkThms07.MATINSERT_THM2
def FUN_EQ_TAC : HolCore.Tactics.tactic := BWorkThms07.FUN_EQ_TAC
def INSERTAT_0 : thm := BWorkThms07.INSERTAT_0
def INFERPSIGN_MATINSERT_THM : thm := BWorkThms07.INFERPSIGN_MATINSERT_THM
def INFERPSIGN_POS : thm := BWorkThms07.INFERPSIGN_POS

-- WorkThms08
def INFERPSIGN_NEG : thm := BWorkThms08.INFERPSIGN_NEG
def INFERPSIGN_POS_EVEN_LEM : thm := BWorkThms08.INFERPSIGN_POS_EVEN_LEM
def SPLIT_LIST_THM : thm := BWorkThms08.SPLIT_LIST_THM
def EXISTS_TACL : List term → HolCore.Tactics.tactic := BWorkThms08.EXISTS_TACL
def DIV_EVEN : thm := BWorkThms08.DIV_EVEN
def PRE_LEM : thm := BWorkThms08.PRE_LEM
def EVEN_PRE : thm := BWorkThms08.EVEN_PRE
def ODD_PRE : thm := BWorkThms08.ODD_PRE
def INFERPSIGN_POS_EVEN : thm := BWorkThms08.INFERPSIGN_POS_EVEN
def INFERPSIGN_NEG_EVEN_LEM : thm := BWorkThms08.INFERPSIGN_NEG_EVEN_LEM
def INFERPSIGN_NEG_EVEN : thm := BWorkThms08.INFERPSIGN_NEG_EVEN

-- WorkThms09
def INFERPSIGN_ZERO_EVEN_LEM : thm := BWorkThms09.INFERPSIGN_ZERO_EVEN_LEM
def INFERPSIGN_ZERO_EVEN : thm := BWorkThms09.INFERPSIGN_ZERO_EVEN
def INFERPSIGN_POS_ODD_POS_LEM : thm := BWorkThms09.INFERPSIGN_POS_ODD_POS_LEM
def INFERPSIGN_POS_ODD_POS : thm := BWorkThms09.INFERPSIGN_POS_ODD_POS
def INFERPSIGN_NEG_ODD_POS_LEM : thm := BWorkThms09.INFERPSIGN_NEG_ODD_POS_LEM
def INFERPSIGN_NEG_ODD_POS : thm := BWorkThms09.INFERPSIGN_NEG_ODD_POS

-- WorkThms10
def INFERPSIGN_ZERO_ODD_POS_LEM : thm := BWorkThms10.INFERPSIGN_ZERO_ODD_POS_LEM
def INFERPSIGN_ZERO_ODD_POS : thm := BWorkThms10.INFERPSIGN_ZERO_ODD_POS

/-- `needs "Rqe/work_thms.ml"`: already done by importing this module. -/
def ensureWorkThms : IO Unit := pure ()

end SessionRQE.WorkThms
