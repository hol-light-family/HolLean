/- ---------------------------------------------------------------------- -/
/- Session wiring for Rqe/rqe_main.ml                                   . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionRQE/RqeMain.lean

  The session half of the rqe_main.ml translation: it supplies HolRQE.RqeMain's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Rqe/rqe_main.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolRQE.RqeMain
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
import SessionRQE.WorkThms
import SessionRQE.Testform
import SessionRQE.Condense
import SessionRQE.Inferisign
import SessionRQE.Matinsert
import SessionRQE.Signs
import SessionRQE.Inferpsign
import SessionRQE.Dedmatrix
import SessionRQE.Pdivides

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionRQE.RqeMain

/-- The core theorems rqe_main.ml uses. -/
def core1 : HolRQE.RqeMain.CoreThms1 where
  ALL2 := Session.listDefs.ALL2
  LAST := Session.listDefs.LAST
  LENGTH := Session.listDefs.LENGTH
  NEQ := SessionRQE.Basic.«NEQ»
  NORMAL_ID := SessionRQE.Asym.«NORMAL_ID»
  NOT_CONS_NIL := Session.listThms1.NOT_CONS_NIL
  TRUTH := Session.TRUTH
  empty_mat := SessionRQE.MainThms.«empty_mat»
  factor_neg_even_neg := SessionRQE.MainThms.«factor_neg_even_neg»
  factor_neg_even_pos := SessionRQE.MainThms.«factor_neg_even_pos»
  factor_neg_even_zero := SessionRQE.MainThms.«factor_neg_even_zero»
  factor_neg_odd_neg := SessionRQE.MainThms.«factor_neg_odd_neg»
  factor_neg_odd_pos := SessionRQE.MainThms.«factor_neg_odd_pos»
  factor_neg_odd_zero := SessionRQE.MainThms.«factor_neg_odd_zero»
  factor_pos_neg := SessionRQE.MainThms.«factor_pos_neg»
  factor_pos_pos := SessionRQE.MainThms.«factor_pos_pos»
  factor_pos_zero := SessionRQE.MainThms.«factor_pos_zero»
  factor_zero_neg := SessionRQE.MainThms.«factor_zero_neg»
  factor_zero_pos := SessionRQE.MainThms.«factor_zero_pos»
  factor_zero_zero := SessionRQE.MainThms.«factor_zero_zero»
  gtneg := SessionRQE.MainThms.«gtneg»
  gtpos := SessionRQE.MainThms.«gtpos»
  gtzero := SessionRQE.MainThms.«gtzero»
  ltneg := SessionRQE.MainThms.«ltneg»
  ltpos := SessionRQE.MainThms.«ltpos»
  ltzero := SessionRQE.MainThms.«ltzero»
  main_lem000 := SessionRQE.MainThms.«main_lem000»
  main_lem001 := SessionRQE.MainThms.«main_lem001»
  main_lem002 := SessionRQE.MainThms.«main_lem002»

/-- What rqe_main.ml uses from Session. -/
def deps : HolRQE.RqeMain.RqeMainDeps where
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
  MATCH_EQ_MP := SessionRQE.RqeTacticsExt.MATCH_EQ_MP
  t_tm := SessionRQE.LiftQelim.t_tm
  f_tm := SessionRQE.LiftQelim.f_tm
  nzero := SessionRQE.RqeNum.nzero
  even_tm := SessionRQE.RqeNum.even_tm
  odd_tm := SessionRQE.RqeNum.odd_tm
  PARITY_CONV := SessionRQE.RqeNum.PARITY_CONV
  req := SessionRQE.RqeReal.req
  rneq := SessionRQE.RqeReal.rneq
  rlt := SessionRQE.RqeReal.rlt
  rgt := SessionRQE.RqeReal.rgt
  rle := SessionRQE.RqeReal.rle
  rge := SessionRQE.RqeReal.rge
  rzero := SessionRQE.RqeReal.rzero
  dest_mult := SessionRQE.RqeReal.dest_mult
  EL_CONV := SessionRQE.RqeList.EL_CONV
  duplicate_columns_timer := SessionRQE.Timers.duplicate_columns_timer
  unmonicize_mat_timer := SessionRQE.Timers.unmonicize_mat_timer
  swap_head_col_timer := SessionRQE.Timers.swap_head_col_timer
  replace_pol_timer := SessionRQE.Timers.replace_pol_timer
  unfactor_mat_timer := SessionRQE.Timers.unfactor_mat_timer
  poly_tm := SessionRQE.PolyExt.poly_tm
  dest_poly := SessionRQE.PolyExt.dest_poly
  is_constant := SessionRQE.PolyExt.is_constant
  POLY_ENLIST_CONV := SessionRQE.PolyExt.POLY_ENLIST_CONV
  POLY_DELIST_CONV := SessionRQE.PolyExt.POLY_DELIST_CONV
  CANON_POLY_DIFF_CONV := SessionRQE.PolyExt.CANON_POLY_DIFF_CONV
  POLYNATE_CONV := SessionRQE.PolyExt.POLYNATE_CONV
  degree_ := SessionRQE.PolyExt.degree_
  head := SessionRQE.PolyExt.head
  behead := SessionRQE.PolyExt.behead
  BEHEAD := SessionRQE.PolyExt.BEHEAD
  MONIC_CONV := SessionRQE.PolyExt.MONIC_CONV
  SIGN_CONST := SessionRQE.PolyExt.SIGN_CONST
  POLYATOM_CONV := SessionRQE.PolyExt.POLYATOM_CONV
  weakfactor := SessionRQE.PolyExt.weakfactor
  poly_var := SessionRQE.PolyExt.poly_var
  WEAKFACTOR_CONV := SessionRQE.PolyExt.WEAKFACTOR_CONV
  SIMPLIFY_CONV := SessionRQE.Simplify.SIMPLIFY_CONV
  EVALC_CONV := SessionRQE.Simplify.EVALC_CONV
  LIFT_QELIM_CONV := SessionRQE.LiftQelim.LIFT_QELIM_CONV
  sneg_tm := SessionRQE.Defs.sneg_tm
  spos_tm := SessionRQE.Defs.spos_tm
  szero_tm := SessionRQE.Defs.szero_tm
  dest_interpsign := SessionRQE.Defs.dest_interpsign
  interpsigns_thms2 := SessionRQE.Defs.interpsigns_thms2
  mk_interpsigns := SessionRQE.Defs.mk_interpsigns
  PARTITION_LINE_CONV := SessionRQE.Defs.PARTITION_LINE_CONV
  dest_interpmat := SessionRQE.Defs.dest_interpmat
  interpmat_thms := SessionRQE.Defs.interpmat_thms
  mk_interpmat_thm := SessionRQE.Defs.mk_interpmat_thm
  mk_all2_interpsigns := SessionRQE.Defs.mk_all2_interpsigns
  dest_all2 := SessionRQE.Defs.dest_all2
  empty_sgns := SessionRQE.MainThms.empty_sgns
  COMBINE_TESTFORMS := SessionRQE.Testform.COMBINE_TESTFORMS
  Isign_arg := SessionRQE.Inferisign.Isign_arg
  MATINSERT := SessionRQE.Matinsert.MATINSERT
  FINDSIGN := SessionRQE.Signs.FINDSIGN
  SPLIT_ZERO := SessionRQE.Signs.SPLIT_ZERO
  SPLIT_SIGN := SessionRQE.Signs.SPLIT_SIGN
  DEDMATRIX := SessionRQE.Dedmatrix.DEDMATRIX
  PDIVIDES := SessionRQE.Pdivides.PDIVIDES
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in rqe_main.ml order. -/
initialize BRqeMainFns : HolRQE.RqeMain.RqeMainFns ←
  ioB "setupRqeMainFns" (HolRQE.RqeMain.setupRqeMainFns deps).run

-- RqeMainFns
def TRAPOUT : HolRQE.Matinsert.MatCont → thm → List (term × thm) → term → ExceptT String IO thm := BRqeMainFns.TRAPOUT
def remove_column : Int → thm → ExceptT String IO thm := BRqeMainFns.remove_column
def REMOVE_COLUMN : Int → thm → ExceptT String IO thm := BRqeMainFns.REMOVE_COLUMN
def SETIFY_CONV : thm → ExceptT String IO thm := BRqeMainFns.SETIFY_CONV
def duplicate_columns : List Int → thm → ExceptT String IO thm := BRqeMainFns.duplicate_columns
def DUPLICATE_COLUMNS : thm → List Int → ExceptT String IO thm := BRqeMainFns.DUPLICATE_COLUMNS
def UNMONICIZE_ISIGN : List term → thm → thm → ExceptT String IO thm := BRqeMainFns.UNMONICIZE_ISIGN
def UNMONICIZE_ISIGNS : List term → List thm → thm → ExceptT String IO thm := BRqeMainFns.UNMONICIZE_ISIGNS
def UNMONICIZE_MAT : List term → List thm → thm → ExceptT String IO thm := BRqeMainFns.UNMONICIZE_MAT
def SWAP_HEAD_COL_ROW : Int → thm → ExceptT String IO thm := BRqeMainFns.SWAP_HEAD_COL_ROW
def SWAP_HEAD_COL : Int → thm → ExceptT String IO thm := BRqeMainFns.SWAP_HEAD_COL
def LENGTH_CONV : term → ExceptT String IO thm := BRqeMainFns.LENGTH_CONV
def LAST_NZ_CONV : thm → term → ExceptT String IO thm := BRqeMainFns.LAST_NZ_CONV
def NEQ_RULE : thm → ExceptT String IO thm := BRqeMainFns.NEQ_RULE
def NORMAL_LIST_CONV : thm → term → ExceptT String IO thm := BRqeMainFns.NORMAL_LIST_CONV
def pdiff_tm : term := BRqeMainFns.pdiff_tm
def GEN_POLY_DIFF_CONV : List term → term → ExceptT String IO thm := BRqeMainFns.GEN_POLY_DIFF_CONV
def rppeq : Option (IO.Ref thm) := BRqeMainFns.rppeq
def rpmat : Option (IO.Ref thm) := BRqeMainFns.rpmat
def REPLACE_POL : thm → thm → ExceptT String IO thm := BRqeMainFns.REPLACE_POL
def UNFACTOR_ISIGN : List term → thm → term → thm → ExceptT String IO thm := BRqeMainFns.UNFACTOR_ISIGN
def UNFACTOR_ISIGNS : List term → List term → thm → ExceptT String IO thm := BRqeMainFns.UNFACTOR_ISIGNS
def UNFACTOR_MAT : List term → List term → thm → ExceptT String IO thm := BRqeMainFns.UNFACTOR_MAT
def matrix_count : Option (IO.Ref Int) := BRqeMainFns.matrix_count
def splitzero_count : Option (IO.Ref Int) := BRqeMainFns.splitzero_count
def splitsigns_count : Option (IO.Ref Int) := BRqeMainFns.splitsigns_count
def monicize_count : Option (IO.Ref Int) := BRqeMainFns.monicize_count
def reset_counts : Unit → IO Unit := BRqeMainFns.reset_counts
def print_counts : Unit → IO (Int × Int × Int × Int) := BRqeMainFns.print_counts
def MATRIX : HolRQE.RqeMain.MatrixFn := BRqeMainFns.MATRIX
def SPLITZERO : HolRQE.RqeMain.SplitFn := BRqeMainFns.SPLITZERO
def SPLITSIGNS : HolRQE.RqeMain.SplitFn := BRqeMainFns.SPLITSIGNS
def MONICIZE : HolRQE.RqeMain.MatrixFn := BRqeMainFns.MONICIZE
def polynomials : term → Except String (List term) := BRqeMainFns.polynomials
def BASIC_REAL_QELIM_CONV : List term → HolCore.Equal.ioconv := BRqeMainFns.BASIC_REAL_QELIM_CONV
def REAL_QELIM_CONV : HolCore.Equal.ioconv := BRqeMainFns.REAL_QELIM_CONV

/-- `needs "Rqe/rqe_main.ml"`: already done by importing this module. -/
def ensureRqeMain : IO Unit := pure ()

end SessionRQE.RqeMain
