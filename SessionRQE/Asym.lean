/- ---------------------------------------------------------------------- -/
/- Session wiring for Rqe/asym.ml                                       . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionRQE/Asym.lean

  The session half of the asym.ml translation: it supplies HolRQE.Asym's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Rqe/asym.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolRQE.Asym
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionRQE.Asym

/-- The core theorems asym.ml uses. -/
def core1 : HolRQE.Asym.CoreThms1 where
  ABS_0 := SessionLibrary.Analysis.«ABS_0»
  ABS_DIV := SessionLibrary.Analysis.«ABS_DIV»
  ABS_LE := SessionLibrary.Analysis.«ABS_LE»
  ABS_POS := SessionLibrary.Analysis.«ABS_POS»
  ADD1 := Session.ADD1
  ADD_SYM := Session.ADD_SYM
  AND_IMP_THM := SessionRQE.Basic.«AND_IMP_THM»
  CONS_11 := Session.listThms1.CONS_11
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIV_ID := SessionRQE.RqeReal.«DIV_ID»
  ETA_AX := Session.ETA_AX
  EVEN := Session.EVEN
  EVEN_OR_ODD := Session.EVEN_OR_ODD
  FUN_EQ_THM := Session.FUN_EQ_THM
  GE := Session.GE
  GT := Session.GT
  LAST := Session.listDefs.LAST
  LAST_CONS := SessionRQE.RqeList.«LAST_CONS»
  LAST_SING := SessionRQE.RqeList.«LAST_SING»
  LAST_TL := SessionRQE.RqeList.«LAST_TL»
  LENGTH := Session.listDefs.LENGTH
  LENGTH_0 := SessionRQE.RqeList.«LENGTH_0»
  LENGTH_1 := SessionRQE.RqeList.«LENGTH_1»
  LENGTH_EQ_NIL := Session.listThms1.LENGTH_EQ_NIL
  LENGTH_NZ := SessionRQE.RqeList.«LENGTH_NZ»
  LENGTH_PAIR := SessionRQE.RqeList.«LENGTH_PAIR»
  LENGTH_SING := SessionRQE.RqeList.«LENGTH_SING»
  LENGTH_TL := SessionRQE.RqeList.«LENGTH_TL»
  LE_REFL := Session.LE_REFL
  LT := Session.LT
  LT_REFL := Session.LT_REFL
  NEG_ABS := SessionRQE.RqeReal.«NEG_ABS»
  NOT_CONS_NIL := Session.listThms1.NOT_CONS_NIL
  NOT_EVEN := Session.NOT_EVEN
  NOT_LE := Session.NOT_LE
  NOT_ODD := Session.NOT_ODD
  NOT_SUC := Session.NOT_SUC
  ODD := Session.ODD
  ONE := Session.ONE
  POLY_MVT := SessionLibrary.Poly.«POLY_MVT»
  POLY_NEG := SessionLibrary.Poly.«POLY_NEG»
  POW_NZ := SessionLibrary.Analysis.«POW_NZ»
  PRE := Session.PRE
  REAL_10 := SessionLibrary.Analysis.«REAL_10»
  REAL_ABS_DIV := Session.REAL_ABS_DIV
  REAL_ABS_NEG := Session.REAL_ABS_NEG
  REAL_ABS_NUM := Session.REAL_ABS_NUM
  REAL_ABS_NZ := Session.REAL_ABS_NZ
  REAL_ABS_REFL := Session.REAL_ABS_REFL
  REAL_ADD_LID := Session.REAL_ADD_LID
  REAL_ADD_RID := Session.REAL_ADD_RID
  REAL_ADD_RINV := Session.REAL_ADD_RINV
  REAL_ARCH_SIMPLE := SessionLibrary.Analysis.«REAL_ARCH_SIMPLE»
  REAL_ARCH_SIMPLE_LT := SessionRQE.RqeReal.«REAL_ARCH_SIMPLE_LT»
  REAL_DIV_ADD_DISTRIB := SessionRQE.RqeReal.«REAL_DIV_ADD_DISTRIB»
  REAL_DIV_DENOM_LT := SessionRQE.RqeReal.«REAL_DIV_DENOM_LT»
  REAL_DIV_DISTRIB_2 := SessionRQE.RqeReal.«REAL_DIV_DISTRIB_2»
  REAL_DIV_DISTRIB_L := SessionRQE.RqeReal.«REAL_DIV_DISTRIB_L»
  REAL_DIV_DISTRIB_R := SessionRQE.RqeReal.«REAL_DIV_DISTRIB_R»
  REAL_DIV_LZERO := SessionLibrary.Analysis.«REAL_DIV_LZERO»
  REAL_DIV_REFL := Session.REAL_DIV_REFL
  REAL_ENTIRE := Session.REAL_ENTIRE
  REAL_EQ_MUL_LCANCEL := Session.REAL_EQ_MUL_LCANCEL
  REAL_INJ := SessionLibrary.Analysis.«REAL_INJ»
  REAL_INV_NEG := Session.REAL_INV_NEG
  REAL_INV_NZ := SessionLibrary.Analysis.«REAL_INV_NZ»
  REAL_INV_POS := SessionLibrary.Analysis.«REAL_INV_POS»
  REAL_LE := SessionLibrary.Analysis.«REAL_LE»
  REAL_LET_TRANS := Session.REAL_LET_TRANS
  REAL_LE_DIV := Session.REAL_LE_DIV
  REAL_LE_LCANCEL_IMP := Session.REAL_LE_LCANCEL_IMP
  REAL_LE_LDIV_EQ := Session.REAL_LE_LDIV_EQ
  REAL_LE_LMUL := Session.REAL_LE_LMUL
  REAL_LE_LT := SessionLibrary.Analysis.«REAL_LE_LT»
  REAL_LE_MUL := SessionLibrary.Analysis.«REAL_LE_MUL»
  REAL_LE_MUL2 := Session.REAL_LE_MUL2
  REAL_LE_NEG2 := SessionLibrary.Analysis.«REAL_LE_NEG2»
  REAL_LE_RCANCEL_IMP := Session.REAL_LE_RCANCEL_IMP
  REAL_LE_REFL := SessionLibrary.Analysis.«REAL_LE_REFL»
  REAL_LE_TRANS := SessionLibrary.Analysis.«REAL_LE_TRANS»
  REAL_LT := SessionLibrary.Analysis.«REAL_LT»
  REAL_LTE_TRANS := SessionLibrary.Analysis.«REAL_LTE_TRANS»
  REAL_LT_IMP_NZ := SessionLibrary.Analysis.«REAL_LT_IMP_NZ»
  REAL_LT_INV := Session.REAL_LT_INV
  REAL_LT_INV_EQ := Session.REAL_LT_INV_EQ
  REAL_LT_LCANCEL_IMP := Session.REAL_LT_LCANCEL_IMP
  REAL_LT_LDIV_EQ := Session.REAL_LT_LDIV_EQ
  REAL_LT_LE := SessionLibrary.Analysis.«REAL_LT_LE»
  REAL_LT_LMUL := Session.REAL_LT_LMUL
  REAL_LT_MUL := Session.REAL_LT_MUL
  REAL_LT_MUL2 := Session.REAL_LT_MUL2
  REAL_LT_NZ := SessionLibrary.Analysis.«REAL_LT_NZ»
  REAL_LT_RCANCEL_IMP := Session.REAL_LT_RCANCEL_IMP
  REAL_LT_RDIV_0 := SessionLibrary.Analysis.«REAL_LT_RDIV_0»
  REAL_LT_TOTAL := Session.REAL_LT_TOTAL
  REAL_LT_TRANS := Session.REAL_LT_TRANS
  REAL_MAX_MAX := Session.REAL_MAX_MAX
  REAL_MUL_ASSOC := Session.REAL_MUL_ASSOC
  REAL_MUL_GT := SessionRQE.RqeReal.«REAL_MUL_GT»
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_LINV := Session.REAL_MUL_LINV
  REAL_MUL_LT := SessionRQE.RqeReal.«REAL_MUL_LT»
  REAL_MUL_LZERO := SessionLibrary.Analysis.«REAL_MUL_LZERO»
  REAL_MUL_RID := SessionLibrary.Analysis.«REAL_MUL_RID»
  REAL_MUL_RINV := SessionLibrary.Analysis.«REAL_MUL_RINV»
  REAL_MUL_RZERO := SessionLibrary.Analysis.«REAL_MUL_RZERO»
  REAL_MUL_SYM := Session.REAL_MUL_SYM
  REAL_NEG_0 := SessionLibrary.Analysis.«REAL_NEG_0»
  REAL_NEG_DIV := SessionRQE.RqeReal.«REAL_NEG_DIV»
  REAL_NEG_MUL2 := SessionLibrary.Analysis.«REAL_NEG_MUL2»
  REAL_NOT_LE := SessionLibrary.Analysis.«REAL_NOT_LE»
  REAL_NOT_LT := SessionLibrary.Analysis.«REAL_NOT_LT»
  REAL_NUM_LE_0 := SessionRQE.RqeReal.«REAL_NUM_LE_0»
  REAL_OF_NUM_ADD := Session.REAL_OF_NUM_ADD
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_OF_NUM_LE := Session.REAL_OF_NUM_LE
  REAL_OF_NUM_LT := Session.REAL_OF_NUM_LT
  REAL_POW_1 := Session.REAL_POW_1
  REAL_POW_LE := Session.REAL_POW_LE
  REAL_POW_MONO := Session.REAL_POW_MONO
  REAL_POW_NEG := Session.REAL_POW_NEG
  REAL_POW_NZ := Session.REAL_POW_NZ
  SEQ := SessionLibrary.Analysis.«SEQ»
  SEQ_ADD := SessionLibrary.Analysis.«SEQ_ADD»
  SEQ_CONST := SessionLibrary.Analysis.«SEQ_CONST»
  SEQ_MUL := SessionLibrary.Analysis.«SEQ_MUL»
  TL := Session.listDefs.TL
  TL_NIL := SessionRQE.RqeList.«TL_NIL»
  degree := SessionLibrary.Poly.«degree»
  list_CASES := Session.listThms1.list_CASES
  list_RECURSION := Session.list_RECURSION
  mono := SessionLibrary.Analysis.«mono»
  nmax := SessionRQE.RqeNum.«nmax»
  normalize := SessionLibrary.Poly.«normalize»
  poly := SessionLibrary.Poly.«poly»
  poly_cmul := SessionLibrary.Poly.«poly_cmul»
  poly_diff := SessionLibrary.Poly.«poly_diff»
  poly_diff_aux := SessionLibrary.Poly.«poly_diff_aux»
  poly_neg := SessionLibrary.Poly.«poly_neg»
  pow := SessionLibrary.Analysis.«pow»
  real_div := Session.real_div
  real_ge := Session.real_ge
  real_gt := Session.real_gt
  real_max := Session.real_max
  real_pow := Session.real_pow
  real_sub := Session.real_sub

/-- What asym.ml uses from Session. -/
def deps : HolRQE.Asym.AsymDeps where
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
  override_interface s t := ExceptT.mk (Session.override_interface s t)
  prioritize_real := Session.prioritize_real
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

/- The bundles, in asym.ml order. -/
initialize BAsymSeq : HolRQE.Asym.AsymSeq ←
  ioB "setupAsymSeq" (HolRQE.Asym.setupAsymSeq deps).run
initialize BAsymPoly : HolRQE.Asym.AsymPoly ←
  ioB "setupAsymPoly" (HolRQE.Asym.setupAsymPoly deps BAsymSeq).run
initialize BAsymUnb : HolRQE.Asym.AsymUnb ←
  ioB "setupAsymUnb" (HolRQE.Asym.setupAsymUnb deps BAsymSeq BAsymPoly).run
initialize BAsymPneg : HolRQE.Asym.AsymPneg ←
  ioB "setupAsymPneg" (HolRQE.Asym.setupAsymPneg deps BAsymPoly BAsymUnb).run
initialize BAsymLeft : HolRQE.Asym.AsymLeft ←
  ioB "setupAsymLeft" (HolRQE.Asym.setupAsymLeft deps BAsymSeq BAsymPoly BAsymUnb BAsymPneg).run

-- AsymSeq
def LIM_INV_1N : thm := BAsymSeq.LIM_INV_1N
def LIM_INV_CONST : thm := BAsymSeq.LIM_INV_CONST
def LIM_INV_1NP : thm := BAsymSeq.LIM_INV_1NP
def LIM_INV_CON : thm := BAsymSeq.LIM_INV_CON
def LIM_NN : thm := BAsymSeq.LIM_NN
def LIM_NNC : thm := BAsymSeq.LIM_NNC
def LIM_MONO : thm := BAsymSeq.LIM_MONO
def LIM_POLY_LT : thm := BAsymSeq.LIM_POLY_LT
def LIM_POLY : thm := BAsymSeq.LIM_POLY
def mono_inc : thm := BAsymSeq.mono_inc
def mono_dec : thm := BAsymSeq.mono_dec
def mono_inc_dec : thm := BAsymSeq.mono_inc_dec
def mono_inc_pow : thm := BAsymSeq.mono_inc_pow
def mono_inc_pow_const : thm := BAsymSeq.mono_inc_pow_const
def mono_unbounded_above : thm := BAsymSeq.mono_unbounded_above
def mono_unbounded_below : thm := BAsymSeq.mono_unbounded_below
def mono_unbounded_above_pos : thm := BAsymSeq.mono_unbounded_above_pos
def mono_unbounded_below_neg : thm := BAsymSeq.mono_unbounded_below_neg
def mua_quotient_limit : thm := BAsymSeq.mua_quotient_limit
def mua_neg : thm := BAsymSeq.mua_neg
def mua_neg2 : thm := BAsymSeq.mua_neg2
def mua_quotient_limit_neg : thm := BAsymSeq.mua_quotient_limit_neg

-- AsymPoly
def normal : thm := BAsymPoly.normal
def nonconstant : thm := BAsymPoly.nonconstant
def NORMALIZE_SING : thm := BAsymPoly.NORMALIZE_SING
def NORMALIZE_PAIR : thm := BAsymPoly.NORMALIZE_PAIR
def POLY_NORMALIZE : thm := BAsymPoly.POLY_NORMALIZE
def NORMAL_CONS : thm := BAsymPoly.NORMAL_CONS
def NORMAL_TAIL : thm := BAsymPoly.NORMAL_TAIL
def NORMAL_LAST_NONZERO : thm := BAsymPoly.NORMAL_LAST_NONZERO
def NORMAL_LENGTH : thm := BAsymPoly.NORMAL_LENGTH
def NORMAL_LAST_LENGTH : thm := BAsymPoly.NORMAL_LAST_LENGTH
def NORMAL_ID : thm := BAsymPoly.NORMAL_ID
def LIM_POLY2 : thm := BAsymPoly.LIM_POLY2
def POW_UNB : thm := BAsymPoly.POW_UNB
def POW_UNB_CON : thm := BAsymPoly.POW_UNB_CON
def POW_UNBB_CON : thm := BAsymPoly.POW_UNBB_CON
def POLY_SING : thm := BAsymPoly.POLY_SING
def POLY_LAST_GT : thm := BAsymPoly.POLY_LAST_GT
def POLY_LAST_LT : thm := BAsymPoly.POLY_LAST_LT
def NORMALIZE_LENGTH_MONO : thm := BAsymPoly.NORMALIZE_LENGTH_MONO
def DEGREE_SING : thm := BAsymPoly.DEGREE_SING
def DEGREE_CONS : thm := BAsymPoly.DEGREE_CONS
def PDA_LENGTH : thm := BAsymPoly.PDA_LENGTH
def POLY_DIFF_LENGTH : thm := BAsymPoly.POLY_DIFF_LENGTH
def POLY_DIFF_SING : thm := BAsymPoly.POLY_DIFF_SING
def NONCONSTANT_LENGTH : thm := BAsymPoly.NONCONSTANT_LENGTH
def NONCONSTANT_DIFF_NIL : thm := BAsymPoly.NONCONSTANT_DIFF_NIL
def NONCONSTANT_DEGREE : thm := BAsymPoly.NONCONSTANT_DEGREE
def POLY_DIFF_LAST_LEM : thm := BAsymPoly.POLY_DIFF_LAST_LEM
def NONCONSTANT_DIFF_0 : thm := BAsymPoly.NONCONSTANT_DIFF_0
def POLY_DIFF_LAST_LT : thm := BAsymPoly.POLY_DIFF_LAST_LT
def POLY_DIFF_LAST_GT : thm := BAsymPoly.POLY_DIFF_LAST_GT
def NONCONSTANT_DIFF_NORMAL : thm := BAsymPoly.NONCONSTANT_DIFF_NORMAL
def PDIFF_POS_LAST : thm := BAsymPoly.PDIFF_POS_LAST
def LAST_UNB : thm := BAsymPoly.LAST_UNB

-- AsymUnb
def POLY_DIFF_UP_RIGHT : thm := BAsymUnb.POLY_DIFF_UP_RIGHT
def PDIFF_NEG_LAST : thm := BAsymUnb.PDIFF_NEG_LAST
def LAST_UNB_NEG : thm := BAsymUnb.LAST_UNB_NEG
def POLY_DIFF_DOWN_RIGHT : thm := BAsymUnb.POLY_DIFF_DOWN_RIGHT
def UNB_LEFT_EVEN : thm := BAsymUnb.UNB_LEFT_EVEN
def UNB_LEFT_ODD : thm := BAsymUnb.UNB_LEFT_ODD
def EVEN_CONS : thm := BAsymUnb.EVEN_CONS
def ODD_CONS : thm := BAsymUnb.ODD_CONS
def MUA_DIV_CONST : thm := BAsymUnb.MUA_DIV_CONST
def SEQ_0_NEG : thm := BAsymUnb.SEQ_0_NEG
def lem : thm := BAsymUnb.lem
def MUB_DIV_CONST : thm := BAsymUnb.MUB_DIV_CONST
def mono_unbounded : thm := BAsymUnb.mono_unbounded
def MU_DIV_CONST : thm := BAsymUnb.MU_DIV_CONST
def MUA_MUA : thm := BAsymUnb.MUA_MUA
def MUA_MUB : thm := BAsymUnb.MUA_MUB
def MUB_MUA : thm := BAsymUnb.MUB_MUA
def MUB_MUB : thm := BAsymUnb.MUB_MUB
def MU_PROD : thm := BAsymUnb.MU_PROD
def mub_quotient_limit : thm := BAsymUnb.mub_quotient_limit
def POLY_UB : thm := BAsymUnb.POLY_UB
def pneg_aux : thm := BAsymUnb.pneg_aux
def pneg : thm := BAsymUnb.pneg
def POLY_PNEG_AUX_SUC : thm := BAsymUnb.POLY_PNEG_AUX_SUC
def POLY_NEG_NEG : thm := BAsymUnb.POLY_NEG_NEG
def POLY_PNEG_NEG : thm := BAsymUnb.POLY_PNEG_NEG
def POLY_PNEG_AUX : thm := BAsymUnb.POLY_PNEG_AUX
def POLY_PNEG : thm := BAsymUnb.POLY_PNEG
def DEGREE_0 : thm := BAsymUnb.DEGREE_0
def EVEN_ODD : thm := BAsymUnb.EVEN_ODD
def ODD_EVEN : thm := BAsymUnb.ODD_EVEN

-- AsymPneg
def PNEG_CONS : thm := BAsymPneg.PNEG_CONS
def PNEG_NIL : thm := BAsymPneg.PNEG_NIL
def PNEG_AUX_NIL : thm := BAsymPneg.PNEG_AUX_NIL
def POLY_CMUL_NIL : thm := BAsymPneg.POLY_CMUL_NIL
def POLY_NEG_NIL : thm := BAsymPneg.POLY_NEG_NIL
def NEG_LAST : thm := BAsymPneg.NEG_LAST
def POLY_PNEG_LAST : thm := BAsymPneg.POLY_PNEG_LAST
def PNEG_AUX_LENGTH : thm := BAsymPneg.PNEG_AUX_LENGTH
def PNEG_LENGTH : thm := BAsymPneg.PNEG_LENGTH
def LAST_PNEG_AUX_0 : thm := BAsymPneg.LAST_PNEG_AUX_0
def LAST_PNEG_0 : thm := BAsymPneg.LAST_PNEG_0
def PNEG_LAST : thm := BAsymPneg.PNEG_LAST
def NORMAL_PNEG : thm := BAsymPneg.NORMAL_PNEG
def PNEG_AUX_NORMALIZE_LENGTH : thm := BAsymPneg.PNEG_AUX_NORMALIZE_LENGTH
def PNEG_NORMALIZE_LENGTH : thm := BAsymPneg.PNEG_NORMALIZE_LENGTH
def DEGREE_PNEG : thm := BAsymPneg.DEGREE_PNEG
def PNEG_SING : thm := BAsymPneg.PNEG_SING
def PNEG_NONCONSTANT : thm := BAsymPneg.PNEG_NONCONSTANT
def LAST_UNBB_EVEN_NEG : thm := BAsymPneg.LAST_UNBB_EVEN_NEG
def POLY_PNEG_LAST2 : thm := BAsymPneg.POLY_PNEG_LAST2
def LAST_UNB_ODD_NEG : thm := BAsymPneg.LAST_UNB_ODD_NEG
def LAST_UNB_EVEN_POS : thm := BAsymPneg.LAST_UNB_EVEN_POS
def LAST_UNB_ODD_POS : thm := BAsymPneg.LAST_UNB_ODD_POS
def POLY_DIFF_AUX_NORMAL : thm := BAsymPneg.POLY_DIFF_AUX_NORMAL
def POLY_DIFF_NORMAL : thm := BAsymPneg.POLY_DIFF_NORMAL
def POLY_DIFF_AUX_NORMAL2 : thm := BAsymPneg.POLY_DIFF_AUX_NORMAL2
def POLY_DIFF_AUX_DEGREE : thm := BAsymPneg.POLY_DIFF_AUX_DEGREE
def poly_diff_aux_odd : thm := BAsymPneg.poly_diff_aux_odd

-- AsymLeft
def poly_diff_parity : thm := BAsymLeft.poly_diff_parity
def poly_diff_parity2 : thm := BAsymLeft.poly_diff_parity2
def normal_nonconstant : thm := BAsymLeft.normal_nonconstant
def nmax_le : thm := BAsymLeft.nmax_le
def POLY_DIFF_UP_LEFT : thm := BAsymLeft.POLY_DIFF_UP_LEFT
def POLY_DIFF_DOWN_LEFT : thm := BAsymLeft.POLY_DIFF_DOWN_LEFT
def POLY_DIFF_DOWN_LEFT2 : thm := BAsymLeft.POLY_DIFF_DOWN_LEFT2
def POLY_DIFF_UP_LEFT2 : thm := BAsymLeft.POLY_DIFF_UP_LEFT2
def POLY_DIFF_DOWN_LEFT3 : thm := BAsymLeft.POLY_DIFF_DOWN_LEFT3
def POLY_DIFF_UP_LEFT3 : thm := BAsymLeft.POLY_DIFF_UP_LEFT3
def POLY_DIFF_DOWN_LEFT4 : thm := BAsymLeft.POLY_DIFF_DOWN_LEFT4
def POLY_DIFF_UP_LEFT4 : thm := BAsymLeft.POLY_DIFF_UP_LEFT4
def POLY_DIFF_DOWN_LEFT5 : thm := BAsymLeft.POLY_DIFF_DOWN_LEFT5
def POLY_DIFF_UP_LEFT5 : thm := BAsymLeft.POLY_DIFF_UP_LEFT5
def NORMAL_PDIFF_LEM : thm := BAsymLeft.NORMAL_PDIFF_LEM
def NORMAL_PDIFF : thm := BAsymLeft.NORMAL_PDIFF
def POLY_DIFF_UP_RIGHT2 : thm := BAsymLeft.POLY_DIFF_UP_RIGHT2
def POLY_DIFF_DOWN_RIGHT2 : thm := BAsymLeft.POLY_DIFF_DOWN_RIGHT2
def POLY_DIFF_UP_RIGHT3 : thm := BAsymLeft.POLY_DIFF_UP_RIGHT3
def POLY_DIFF_DOWN_RIGHT3 : thm := BAsymLeft.POLY_DIFF_DOWN_RIGHT3

/-- `needs "Rqe/asym.ml"`: already done by importing this module. -/
def ensureAsym : IO Unit := pure ()

end SessionRQE.Asym
