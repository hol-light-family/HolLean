/- ---------------------------------------------------------------------- -/
/- Session wiring for Rqe/poly_ext.ml                                   . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionRQE/PolyExt.lean

  The session half of the poly_ext.ml translation: it supplies HolRQE.PolyExt's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Rqe/poly_ext.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolRQE.PolyExt
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionRQE.PolyExt

/-- The core theorems poly_ext.ml uses. -/
def core1 : HolRQE.PolyExt.CoreThms1 where
  DIFF_ADD := SessionLibrary.Analysis.«DIFF_ADD»
  DIFF_CMUL := SessionLibrary.Analysis.«DIFF_CMUL»
  DIFF_CONST := SessionLibrary.Analysis.«DIFF_CONST»
  DIFF_POW := SessionLibrary.Analysis.«DIFF_POW»
  HD := Session.listDefs.HD
  NOT_CONS_NIL := Session.listThms1.NOT_CONS_NIL
  POW_1 := SessionLibrary.Analysis.«POW_1»
  REAL_ADD_LID := Session.REAL_ADD_LID
  REAL_LDISTRIB := SessionLibrary.Analysis.«REAL_LDISTRIB»
  REAL_MUL_ASSOC := Session.REAL_MUL_ASSOC
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_RZERO := SessionLibrary.Analysis.«REAL_MUL_RZERO»
  REAL_MUL_SYM := Session.REAL_MUL_SYM
  SUC_SUB1 := SessionLibrary.Analysis.«SUC_SUB1»
  SWAP_FORALL_THM := Session.SWAP_FORALL_THM
  TL := Session.listDefs.TL
  lem := SessionRQE.Rol.«lem»
  poly := SessionLibrary.Poly.«poly»
  poly_diff := SessionLibrary.Poly.«poly_diff»
  poly_diff_aux := SessionLibrary.Poly.«poly_diff_aux»
  pow := SessionLibrary.Analysis.«pow»
  real_div := Session.real_div
  real_ge := Session.real_ge
  real_gt := Session.real_gt
  real_pow := Session.real_pow
  real_sub := Session.real_sub

/-- What poly_ext.ml uses from Session. -/
def deps : HolRQE.PolyExt.PolyExtDeps where
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
  REAL_RAT_NEG_CONV := Session.REAL_RAT_NEG_CONV
  REAL_RAT_GT_CONV := Session.REAL_RAT_GT_CONV
  REAL_RAT_LT_CONV := Session.REAL_RAT_LT_CONV
  REAL_RAT_MUL_CONV := Session.REAL_RAT_MUL_CONV
  REAL_RAT_EQ_CONV := Session.REAL_RAT_EQ_CONV
  ETA_CONV t := pure (Session.ETA_CONV t)
  mk_small_numeral := Session.mk_small_numeral
  term_of_rat x := HolMath.CalcInt.term_of_rat Session.RSyn x
  NUM_SUC_CONV := Session.NUM_SUC_CONV
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
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in poly_ext.ml order. -/
initialize BPolyExtFns : HolRQE.PolyExt.PolyExtFns ←
  ioB "setupPolyExtFns" (HolRQE.PolyExt.setupPolyExtFns deps).run

-- PolyExtFns
def poly_tm : term := BPolyExtFns.poly_tm
def dest_poly : term → Except String (term × term) := BPolyExtFns.dest_poly
def is_poly : term → ExceptT String IO Bool := BPolyExtFns.is_poly
def polyvar : term → Except String term := BPolyExtFns.polyvar
def is_constant : List term → term → Except String Bool := BPolyExtFns.is_constant
def POLY : thm := BPolyExtFns.POLY
def POLY_ENLIST_CONV : List term → ExceptT String IO HolCore.Equal.ioconv := BPolyExtFns.POLY_ENLIST_CONV
def POLY_DELIST_CONV : HolCore.Equal.ioconv := BPolyExtFns.POLY_DELIST_CONV
def POLY_DIFF_CLAUSES : thm := BPolyExtFns.POLY_DIFF_CLAUSES
def POLY_DIFF_LEMMA : thm := BPolyExtFns.POLY_DIFF_LEMMA
def POLY_DIFF : thm := BPolyExtFns.POLY_DIFF
def CANON_POLY_DIFF_CONV : HolCore.Equal.ioconv := BPolyExtFns.CANON_POLY_DIFF_CONV
def POLY_ADD_CONV : List term → HolCore.Equal.ioconv := BPolyExtFns.POLY_ADD_CONV
def POLY_NEG_CONV : HolCore.Equal.ioconv := BPolyExtFns.POLY_NEG_CONV
def POLY_SUB_CONV : List term → HolCore.Equal.ioconv := BPolyExtFns.POLY_SUB_CONV
def POLY_MUL_CONV : List term → HolCore.Equal.ioconv := BPolyExtFns.POLY_MUL_CONV
def POLY_POW_CONV : List term → HolCore.Equal.ioconv := BPolyExtFns.POLY_POW_CONV
def POLYNATE_CONV : List term → HolCore.Equal.ioconv := BPolyExtFns.POLYNATE_CONV
def poly_add_ : List term → term → term → ExceptT String IO term := BPolyExtFns.poly_add_
def poly_sub_ : List term → term → term → ExceptT String IO term := BPolyExtFns.poly_sub_
def poly_mul_ : List term → term → term → ExceptT String IO term := BPolyExtFns.poly_mul_
def poly_neg_ : term → ExceptT String IO term := BPolyExtFns.poly_neg_
def poly_pow_ : List term → term → Int → ExceptT String IO term := BPolyExtFns.poly_pow_
def degree_ : List term → term → Except String Int := BPolyExtFns.degree_
def coefficients : List term → term → Except String (List term) := BPolyExtFns.coefficients
def head : List term → term → Except String term := BPolyExtFns.head
def behead : List term → term → Except String term := BPolyExtFns.behead
def BEHEAD3 : List term → thm → term → ExceptT String IO thm := BPolyExtFns.BEHEAD3
def BEHEAD : List term → thm → term → ExceptT String IO thm := BPolyExtFns.BEHEAD
def is_const_poly : List term → term → Except String Bool := BPolyExtFns.is_const_poly
def MONIC_CONV : List term → HolCore.Equal.ioconv := BPolyExtFns.MONIC_CONV
def PDIVIDE : List term → term → term → ExceptT String IO thm := BPolyExtFns.PDIVIDE
def SIGN_CONST : term → ExceptT String IO thm := BPolyExtFns.SIGN_CONST
def POLY_DERIV_CONV : List term → term → ExceptT String IO thm := BPolyExtFns.POLY_DERIV_CONV
def lt_lem : thm := BPolyExtFns.lt_lem
def le_lem : thm := BPolyExtFns.le_lem
def eq_lem : thm := BPolyExtFns.eq_lem
def POLYATOM_CONV : List term → term → ExceptT String IO thm := BPolyExtFns.POLYATOM_CONV
def weakfactor : term → term → Int × term := BPolyExtFns.weakfactor
def poly_var : term → Except String term := BPolyExtFns.poly_var
def POW_PROD_SUM : thm := BPolyExtFns.POW_PROD_SUM
def lem1 : thm := BPolyExtFns.lem1
def lem2 : thm := BPolyExtFns.lem2
def lem3 : thm := BPolyExtFns.lem3
def SIMP_POW_CONV : term → ExceptT String IO thm := BPolyExtFns.SIMP_POW_CONV
def WEAKFACTOR_CONV : term → term → ExceptT String IO thm := BPolyExtFns.WEAKFACTOR_CONV

/-- `needs "Rqe/poly_ext.ml"`: already done by importing this module. -/
def ensurePolyExt : IO Unit := pure ()

end SessionRQE.PolyExt
