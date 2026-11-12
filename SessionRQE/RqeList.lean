/- ---------------------------------------------------------------------- -/
/- Session wiring for Rqe/rqe_list.ml                                   . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionRQE/RqeList.lean

  The session half of the rqe_list.ml translation: it supplies HolRQE.RqeList's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Rqe/rqe_list.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolRQE.RqeList
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionRQE.RqeList

/-- The core theorems rqe_list.ml uses. -/
def core1 : HolRQE.RqeList.CoreThms1 where
  APPEND := Session.listDefs.APPEND
  COND_CLAUSES := Session.COND_CLAUSES
  HD := Session.listDefs.HD
  LAST := Session.listDefs.LAST
  LENGTH := Session.listDefs.LENGTH
  LET_DEF := Session.LET_DEF
  LET_END_DEF := Session.LET_END_DEF
  LT_REFL := Session.LT_REFL
  MEM := Session.listDefs.MEM
  NOT_CONS_NIL := Session.listThms1.NOT_CONS_NIL
  NOT_NIL := SessionRQE.ListRewrites.«NOT_NIL»
  ONE := Session.ONE
  TL := Session.listDefs.TL
  list_CASES := Session.listThms1.list_CASES
  list_RECURSION := Session.list_RECURSION
  num_RECURSION := Session.num_RECURSION

/-- What rqe_list.ml uses from Session. -/
def deps : HolRQE.RqeList.RqeListDeps where
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
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in rqe_list.ml order. -/
initialize BRqeListThms : HolRQE.RqeList.RqeListThms ←
  ioB "setupRqeListThms" (HolRQE.RqeList.setupRqeListThms deps).run

-- RqeListThms
def aacons_tm : term := BRqeListThms.aacons_tm
def HD_CONV : HolCore.Equal.ioconv → HolCore.Equal.ioconv := BRqeListThms.HD_CONV
def TL_CONV : HolCore.Equal.ioconv → HolCore.Equal.ioconv := BRqeListThms.TL_CONV
def EL_CONV : HolCore.Equal.ioconv → Int → HolCore.Equal.ioconv := BRqeListThms.EL_CONV
def NOT_CONS : thm := BRqeListThms.NOT_CONS
def REMOVE : thm := BRqeListThms.REMOVE
def CHOP_LIST : thm := BRqeListThms.CHOP_LIST
def REM_NIL : thm := BRqeListThms.REM_NIL
def REM_FALSE : thm := BRqeListThms.REM_FALSE
def MEM_REMOVE : thm := BRqeListThms.MEM_REMOVE
def REM_NEQ : thm := BRqeListThms.REM_NEQ
def LAST_SING : thm := BRqeListThms.LAST_SING
def LAST_CONS : thm := BRqeListThms.LAST_CONS
def LAST_CONS_CONS : thm := BRqeListThms.LAST_CONS_CONS
def HD_APPEND : thm := BRqeListThms.HD_APPEND
def LENGTH_0 : thm := BRqeListThms.LENGTH_0
def LENGTH_1 : thm := BRqeListThms.LENGTH_1
def LIST_TRI : thm := BRqeListThms.LIST_TRI
def LENGTH_PAIR : thm := BRqeListThms.LENGTH_PAIR
def LENGTH_SING : thm := BRqeListThms.LENGTH_SING
def TL_NIL : thm := BRqeListThms.TL_NIL
def LAST_TL : thm := BRqeListThms.LAST_TL
def LENGTH_TL : thm := BRqeListThms.LENGTH_TL
def LENGTH_NZ : thm := BRqeListThms.LENGTH_NZ

/-- `needs "Rqe/rqe_list.ml"`: already done by importing this module. -/
def ensureRqeList : IO Unit := pure ()

end SessionRQE.RqeList
