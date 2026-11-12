/- ---------------------------------------------------------------------- -/
/- Session wiring for Rqe/rqe_real.ml                                   . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionRQE/RqeReal.lean

  The session half of the rqe_real.ml translation: it supplies HolRQE.RqeReal's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Rqe/rqe_real.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolRQE.RqeReal
import SessionLibrary.Analysis
import SessionLibrary.Poly
import SessionRQE.RqeLib
import SessionRQE.RqeTacticsExt
import SessionRQE.Util
import SessionRQE.Rewrites
import SessionRQE.Basic
import SessionRQE.RqeNum

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionRQE.RqeReal

/-- The core theorems rqe_real.ml uses. -/
def core1 : HolRQE.RqeReal.CoreThms1 where
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  EVEN := Session.EVEN
  EVEN_AND_ODD := Session.EVEN_AND_ODD
  EVEN_OR_ODD := Session.EVEN_OR_ODD
  NEQ := SessionRQE.Basic.«NEQ»
  NOT_EVEN := Session.NOT_EVEN
  NOT_ODD := Session.NOT_ODD
  ODD := Session.ODD
  POW_0 := SessionLibrary.Analysis.«POW_0»
  REAL := SessionLibrary.Analysis.«REAL»
  REAL_ADD_ASSOC := Session.REAL_ADD_ASSOC
  REAL_ADD_LDISTRIB := Session.REAL_ADD_LDISTRIB
  REAL_ADD_LID := Session.REAL_ADD_LID
  REAL_ADD_RDISTRIB := Session.REAL_ADD_RDISTRIB
  REAL_ADD_RID := Session.REAL_ADD_RID
  REAL_ADD_RINV := Session.REAL_ADD_RINV
  REAL_ADD_SYM := Session.REAL_ADD_SYM
  REAL_ARCH_SIMPLE := SessionLibrary.Analysis.«REAL_ARCH_SIMPLE»
  REAL_DOWN := Session.REAL_DOWN
  REAL_INV_MUL := Session.REAL_INV_MUL
  REAL_INV_NEG := Session.REAL_INV_NEG
  REAL_LET_ADD2 := Session.REAL_LET_ADD2
  REAL_LE_ADD2 := Session.REAL_LE_ADD2
  REAL_LE_INV2 := Session.REAL_LE_INV2
  REAL_LE_LCANCEL_IMP := Session.REAL_LE_LCANCEL_IMP
  REAL_LE_LMUL := Session.REAL_LE_LMUL
  REAL_LE_MUL := SessionLibrary.Analysis.«REAL_LE_MUL»
  REAL_LE_MUL2 := Session.REAL_LE_MUL2
  REAL_LE_REFL := SessionLibrary.Analysis.«REAL_LE_REFL»
  REAL_LE_TRANS := SessionLibrary.Analysis.«REAL_LE_TRANS»
  REAL_LT := SessionLibrary.Analysis.«REAL_LT»
  REAL_LT_IMP_NZ := SessionLibrary.Analysis.«REAL_LT_IMP_NZ»
  REAL_LT_INV := Session.REAL_LT_INV
  REAL_LT_INV2 := Session.REAL_LT_INV2
  REAL_LT_LCANCEL_IMP := Session.REAL_LT_LCANCEL_IMP
  REAL_LT_LE := SessionLibrary.Analysis.«REAL_LT_LE»
  REAL_LT_MUL := Session.REAL_LT_MUL
  REAL_LT_MUL2 := Session.REAL_LT_MUL2
  REAL_LT_RADD := SessionLibrary.Analysis.«REAL_LT_RADD»
  REAL_LT_SUB_LADD := SessionLibrary.Analysis.«REAL_LT_SUB_LADD»
  REAL_MUL_ASSOC := Session.REAL_MUL_ASSOC
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_LINV := Session.REAL_MUL_LINV
  REAL_MUL_LZERO := SessionLibrary.Analysis.«REAL_MUL_LZERO»
  REAL_MUL_RID := SessionLibrary.Analysis.«REAL_MUL_RID»
  REAL_MUL_RNEG := Session.REAL_MUL_RNEG
  REAL_MUL_SYM := Session.REAL_MUL_SYM
  REAL_NOT_LT := SessionLibrary.Analysis.«REAL_NOT_LT»
  REAL_POW_LE := Session.REAL_POW_LE
  REAL_POW_LT := Session.REAL_POW_LT
  real_div := Session.real_div
  real_gt := Session.real_gt
  real_pow := Session.real_pow
  real_sub := Session.real_sub

/-- What rqe_real.ml uses from Session. -/
def deps : HolRQE.RqeReal.RqeRealDeps where
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
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in rqe_real.ml order. -/
initialize BRqeRealThms : HolRQE.RqeReal.RqeRealThms ←
  ioB "setupRqeRealThms" (HolRQE.RqeReal.setupRqeRealThms deps).run

-- RqeRealThms
def real_ty : hol_type := BRqeRealThms.real_ty
def rx : term := BRqeRealThms.rx
def ry : term := BRqeRealThms.ry
def rz : term := BRqeRealThms.rz
def req : term := BRqeRealThms.req
def rneq : term := BRqeRealThms.rneq
def rlt : term := BRqeRealThms.rlt
def rgt : term := BRqeRealThms.rgt
def rle : term := BRqeRealThms.rle
def rge : term := BRqeRealThms.rge
def rm : term := BRqeRealThms.rm
def rs : term := BRqeRealThms.rs
def rn : term := BRqeRealThms.rn
def rd : term := BRqeRealThms.rd
def rp : term := BRqeRealThms.rp
def rzero : term := BRqeRealThms.rzero
def rone : term := BRqeRealThms.rone
def rlast : term := BRqeRealThms.rlast
def rappend : term := BRqeRealThms.rappend
def mk_rlist : List term → IO (Except String term) := BRqeRealThms.mk_rlist
def diffl_tm : term := BRqeRealThms.diffl_tm
def dest_diffl : term → Except String (term × term) := BRqeRealThms.dest_diffl
def dest_mult : term → Except String (term × term) := BRqeRealThms.dest_mult
def mk_mult : term → Except String (term → Except String term) := BRqeRealThms.mk_mult
def pow_tm : term := BRqeRealThms.pow_tm
def dest_pow : term → Except String (term × term) := BRqeRealThms.dest_pow
def mk_plus : term → Except String (term → Except String term) := BRqeRealThms.mk_plus
def mk_negative : term → Except String term := BRqeRealThms.mk_negative
def dest_plus : term → Except String (term × term) := BRqeRealThms.dest_plus
def REAL_DENSE : thm := BRqeRealThms.REAL_DENSE
def REAL_LT_EXISTS : thm := BRqeRealThms.REAL_LT_EXISTS
def REAL_GT_EXISTS : thm := BRqeRealThms.REAL_GT_EXISTS
def REAL_DIV_DISTRIB_L : thm := BRqeRealThms.REAL_DIV_DISTRIB_L
def REAL_DIV_DISTRIB_R : thm := BRqeRealThms.REAL_DIV_DISTRIB_R
def REAL_DIV_DISTRIB_2 : thm := BRqeRealThms.REAL_DIV_DISTRIB_2
def REAL_DIV_ADD_DISTRIB : thm := BRqeRealThms.REAL_DIV_ADD_DISTRIB
def DIV_ID : thm := BRqeRealThms.DIV_ID
def POS_POW : thm := BRqeRealThms.POS_POW
def POS_NAT_POW : thm := BRqeRealThms.POS_NAT_POW
def REAL_NUM_LE_0 : thm := BRqeRealThms.REAL_NUM_LE_0
def REAL_ARCH_SIMPLE_LT : thm := BRqeRealThms.REAL_ARCH_SIMPLE_LT
def BINOMIAL_LEMMA_LT : thm := BRqeRealThms.BINOMIAL_LEMMA_LT
def BINOMIAL_LEMMA : thm := BRqeRealThms.BINOMIAL_LEMMA
def NEG_ABS : thm := BRqeRealThms.NEG_ABS
def REAL_MUL_LT : thm := BRqeRealThms.REAL_MUL_LT
def REAL_MUL_GT : thm := BRqeRealThms.REAL_MUL_GT
def REAL_DIV_INV : thm := BRqeRealThms.REAL_DIV_INV
def REAL_DIV_DENOM_LT : thm := BRqeRealThms.REAL_DIV_DENOM_LT
def REAL_DIV_DENOM_LE : thm := BRqeRealThms.REAL_DIV_DENOM_LE
def REAL_NEG_DIV : thm := BRqeRealThms.REAL_NEG_DIV
def REAL_GT_IMP_NZ : thm := BRqeRealThms.REAL_GT_IMP_NZ
def REAL_NEG_NZ : thm := BRqeRealThms.REAL_NEG_NZ
def PARITY_POW_LT : thm := BRqeRealThms.PARITY_POW_LT
def EVEN_ODD_POW : thm := BRqeRealThms.EVEN_ODD_POW

/-- `needs "Rqe/rqe_real.ml"`: already done by importing this module. -/
def ensureRqeReal : IO Unit := pure ()

end SessionRQE.RqeReal
