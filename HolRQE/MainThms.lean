/- ========================================================================= -/
/- Rqe: theorems for the main decision procedure (monic signs, factors).   -/
/- ========================================================================= -/
/- File: HolRQE/MainThms.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/main_thms.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml, Rqe/num_calc_simp.ml, Rqe/asym.ml, Rqe/rol.ml, Rqe/poly_ext.ml, Rqe/simplify.ml, Rqe/lift_qelim.ml, Rqe/defs.ml, Rqe/testform_thms.ml, Rqe/condense_thms.ml, Rqe/inferisign_thms.ml, Rqe/matinsert_thms.ml, Rqe/signs_thms.ml, Rqe/inferpsign_thms.ml, Rqe/dedmatrix_thms.ml, Rqe/pdivides_thms.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.MainThms fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, INT_ARITH, TAUT, SET_RULE, ...) they are
  bound first, in OCaml's order.
-/

import HolLibrary.Analysis
import HolLibrary.Poly
import HolRQE.RqeLib
import HolRQE.RqeTacticsExt
import HolRQE.Util
import HolRQE.Rewrites
import HolRQE.Basic
import HolRQE.RqeNum
import HolRQE.RqeReal
import HolRQE.ListRewrites
import HolRQE.RqeList
import HolRQE.Timers
import HolRQE.NumCalcSimp
import HolRQE.Asym
import HolRQE.Rol
import HolRQE.PolyExt
import HolRQE.Simplify
import HolRQE.LiftQelim
import HolRQE.Defs
import HolRQE.TestformThms
import HolRQE.CondenseThms
import HolRQE.InferisignThms
import HolRQE.MatinsertThms
import HolRQE.SignsThms
import HolRQE.InferpsignThms
import HolRQE.DedmatrixThms
import HolRQE.PdividesThms

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolRQE.RqeLib
open HolRQE.RqeTacticsExt
open HolRQE.Util
open HolRQE.Rewrites
open HolRQE.Basic
open HolRQE.RqeNum
open HolRQE.RqeReal
open HolRQE.ListRewrites
open HolRQE.RqeList
open HolRQE.Timers
open HolRQE.NumCalcSimp
open HolRQE.Asym
open HolRQE.Rol
open HolRQE.PolyExt
open HolRQE.Simplify
open HolRQE.LiftQelim
open HolRQE.Defs
open HolRQE.TestformThms
open HolRQE.CondenseThms
open HolRQE.InferisignThms
open HolRQE.MatinsertThms
open HolRQE.SignsThms
open HolRQE.InferpsignThms
open HolRQE.DedmatrixThms
open HolRQE.PdividesThms

namespace HolRQE.MainThms

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALL2 LENGTH NEQ PARITY_POW_LT POW_0 REAL_ADD_LID REAL_ENTIRE REAL_MUL_GT
   REAL_MUL_LT REAL_MUL_RID REAL_POW_LT ROL_EMPTY interpmat interpsign
   interpsigns num_CASES partition_line real_gt : thm)
  deriving Inhabited

/-- What main_thms.ml uses from Session besides theorems. -/
structure MainThmsDeps where
  new_definition : String → ExceptT String IO thm
  define : String → ExceptT String IO thm
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  new_recursive_definition : thm → String → ExceptT String IO thm
  LIST_INDUCT_TAC : tactic
  ASM_ARITH_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  METIS_TAC : List thm → tactic
  ASM_METIS_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  TAUT : term → ExceptT String IO thm
  ITAUT : term → ExceptT String IO thm
  REAL_ARITH : term → ExceptT String IO thm
  REAL_FIELD : term → ExceptT String IO thm
  REAL_ARITH_TAC : tactic
  ASM_REAL_ARITH_TAC : tactic
  INDUCT_TAC : tactic
  INT_ARITH : term → ExceptT String IO thm
  INT_ARITH_TAC : tactic
  ASM_INT_ARITH_TAC : tactic
  INTEGER_RULE : term → ExceptT String IO thm  -- ints.ml's INTEGER_RULE
  INTEGER_TAC : tactic
  NUMBER_RULE : ioconv  -- ints.ml's NUMBER_RULE
  NUM_REDUCE_CONV : ioconv
  INT_REDUCE_CONV : ioconv
  INT_RED_CONV : ioconv
  INT_REM_DOWN_CONV : ioconv
  HAS_SIZE_CONV : ioconv  -- card.ml's HAS_SIZE_CONV
  let_CONV : ioconv
  num_CONV : ioconv
  mk_numeral : Rat → Except String term
  LET_TAC : tactic
  basic_ss : List thm → IO (Except String HolCore.Simp.simpset)
  NUM_SUB_CONV : ioconv
  REAL_RAT_REDUCE_CONV : ioconv
  NUM_EQ_CONV : ioconv
  NUM_DIV_CONV : ioconv
  EXP_MOD_CONV : ioconv
  EXPAND_CASES_CONV : ioconv
  labels_flag : Option (IO.Ref Bool)
  prove_by_refinement : term × List tactic → ExceptT String IO thm
  exclude_list : Option (IO.Ref (List String))
  get_var_list : term → IO (List (String × hol_type))
  auto_type : term → term → IO term
  auto_type_list : term → List term → IO term
  auto_type_goal : term → HolCore.Tactics.goal → IO term
  TYPE_TAC : (term → tactic) → term → tactic
  TYPE_TACL : (List term → tactic) → List term → tactic
  CLAIM : term → tactic
  MATCH_EQ_MP : thm → thm → ExceptT String IO thm
  DISJ_LCASE : tactic
  DISJ_RCASE : tactic
  CASES_ON : term → tactic
  EXISTS_TAC : term → tactic
  MATCH_EQ_MPL : List thm → ExceptT String IO thm
  CCONTR_TAC : tactic
  pgoal : Unit → IO HolCore.Tactics.goalstack
  suppress : Option (IO.Ref (List String))
  get_type_list : term → IO (List (String × hol_type))
  set_types : term → IO (List (String × hol_type))
  print_term_types : term → IO Unit
  print_thm_types : thm → IO Unit
  goal_types : Unit → IO Unit
  assum : Int → ExceptT String IO term
  assum_types : Int → ExceptT String IO Unit
  get_type : String → thm → ExceptT String IO hol_type
  proof_stack : Option (IO.Ref (List HolCore.Tactics.goalstack))
  push_proof : term → IO HolCore.Tactics.goalstack
  pop_proof : Unit → ExceptT String IO HolCore.Tactics.goalstack
  NUM_REWRITES : Option (IO.Ref (List thm))
  NUM_SIMP_TAC : tactic
  extend_num_rewrites : List thm → IO Unit
  REAL_REWRITES : Option (IO.Ref (List thm))
  REAL_ELIM : Option (IO.Ref (List thm))
  REAL_SIMP_TAC : tactic
  REAL_SOLVE_TAC : tactic
  extend_real_rewrites : List thm → IO Unit
  BASIC_REWRITES : Option (IO.Ref (List thm))
  dest_beq : term → Except String (term × term)
  t_tm : term
  f_tm : term
  nqt : term
  mk_neq : term × term → Except String term
  neq : term
  nlt : term
  ngt : term
  nle : term
  nge : term
  nm : term
  np : term
  nzero : term
  even_tm : term
  odd_tm : term
  PARITY_CONV : term → ExceptT String IO thm
  real_ty : hol_type
  rx : term
  ry : term
  rz : term
  req : term
  rneq : term
  rlt : term
  rgt : term
  rle : term
  rge : term
  rm : term
  rs : term
  rn : term
  rd : term
  rp : term
  rzero : term
  rone : term
  rlast : term
  rappend : term
  mk_rlist : List term → IO (Except String term)
  diffl_tm : term
  dest_diffl : term → Except String (term × term)
  dest_mult : term → Except String (term × term)
  mk_mult : term → Except String (term → Except String term)
  pow_tm : term
  dest_pow : term → Except String (term × term)
  mk_plus : term → Except String (term → Except String term)
  mk_negative : term → Except String term
  dest_plus : term → Except String (term × term)
  LIST_REWRITES : Option (IO.Ref (List thm))
  LIST_SIMP_TAC : tactic
  extend_list_rewrites : List thm → IO Unit
  aacons_tm : term
  HD_CONV : ioconv → ioconv
  TL_CONV : ioconv → ioconv
  EL_CONV : ioconv → Int → ioconv
  testform_timer : Option (IO.Ref Float)
  combine_testforms_timer : Option (IO.Ref Float)
  condense_timer : Option (IO.Ref Float)
  inferisign_timer : Option (IO.Ref Float)
  matinsert_timer : Option (IO.Ref Float)
  inferpsign_timer : Option (IO.Ref Float)
  remove_column1_timer : Option (IO.Ref Float)
  add_infinities_timer : Option (IO.Ref Float)
  remove_infinities_timer : Option (IO.Ref Float)
  pdivides_timer : Option (IO.Ref Float)
  duplicate_columns_timer : Option (IO.Ref Float)
  unmonicize_mat_timer : Option (IO.Ref Float)
  swap_head_col_timer : Option (IO.Ref Float)
  replace_pol_timer : Option (IO.Ref Float)
  unfactor_mat_timer : Option (IO.Ref Float)
  reset_timers : Unit → IO Unit
  print_timers : Unit → IO Unit
  arith_ss : List thm → ExceptT String IO HolCore.Simp.simpset
  ARITH_SIMP_CONV : List thm → ioconv
  arith_net : Unit → ExceptT String IO (HolCore.Nets.net HolCore.Simp.gconv)
  ARITH_REWRITE_CONV : List thm → ioconv
  ARITH_SIMP_TAC : List thm → tactic
  CHOP_REAL_LIST : Int → term → ExceptT String IO thm
  ROL_CHOP_LT : Int → thm → ExceptT String IO thm
  ROL_CHOP_LIST : Int → thm → ExceptT String IO (thm × thm × thm)
  ROL_INSERT_MIDDLE : thm → thm → ExceptT String IO thm
  ROL_INSERT_FRONT : thm → thm → ExceptT String IO thm
  ROL_INSERT_BACK : thm → thm → ExceptT String IO thm
  ROL_INSERT : thm → thm → ExceptT String IO thm
  rol_thms : thm → ExceptT String IO (List thm)
  rol_nonempty_thms : thm → ExceptT String IO (List thm)
  mk_rol : List thm → ExceptT String IO thm
  real_nil : term
  ROL_REMOVE : term → thm → ExceptT String IO thm
  ROL_COVERS : thm → ExceptT String IO thm
  poly_tm : term
  dest_poly : term → Except String (term × term)
  is_poly : term → ExceptT String IO Bool
  polyvar : term → Except String term
  is_constant : List term → term → Except String Bool
  POLY_ENLIST_CONV : List term → ExceptT String IO ioconv
  POLY_DELIST_CONV : ioconv
  CANON_POLY_DIFF_CONV : ioconv
  POLY_ADD_CONV : List term → ioconv
  POLY_NEG_CONV : ioconv
  POLY_SUB_CONV : List term → ioconv
  POLY_MUL_CONV : List term → ioconv
  POLY_POW_CONV : List term → ioconv
  POLYNATE_CONV : List term → ioconv
  poly_add_ : List term → term → term → ExceptT String IO term
  poly_sub_ : List term → term → term → ExceptT String IO term
  poly_mul_ : List term → term → term → ExceptT String IO term
  poly_neg_ : term → ExceptT String IO term
  poly_pow_ : List term → term → Int → ExceptT String IO term
  degree_ : List term → term → Except String Int
  coefficients : List term → term → Except String (List term)
  head : List term → term → Except String term
  behead : List term → term → Except String term
  BEHEAD3 : List term → thm → term → ExceptT String IO thm
  BEHEAD : List term → thm → term → ExceptT String IO thm
  is_const_poly : List term → term → Except String Bool
  MONIC_CONV : List term → ioconv
  PDIVIDE : List term → term → term → ExceptT String IO thm
  SIGN_CONST : term → ExceptT String IO thm
  POLY_DERIV_CONV : List term → term → ExceptT String IO thm
  POLYATOM_CONV : List term → term → ExceptT String IO thm
  weakfactor : term → term → Int × term
  poly_var : term → Except String term
  SIMP_POW_CONV : term → ExceptT String IO thm
  WEAKFACTOR_CONV : term → term → ExceptT String IO thm
  PSIMPLIFY1_CONV : ioconv
  SIMPLIFY1_CONV : ioconv
  SIMPLIFY_CONV : ioconv
  REAL_LEAF_CONV : ioconv
  EVALC_CONV : ioconv
  ACI_CONJ : term → term → ExceptT String IO thm
  QE_SIMPLIFY_CONV : ioconv
  or_exists_conv : ioconv
  triv_exists_conv : ioconv
  push_exists_conv : ioconv
  not_tm : term
  or_tm : term
  LIFT_QELIM_CONV : (List term → ioconv) → ioconv → (List term → ioconv) → ioconv
  sunk_tm : term
  snonz_tm : term
  sneg_tm : term
  spos_tm : term
  szero_tm : term
  interpsign_tm : term
  dest_interpsign : thm → Except String (term × term × term)
  interpsigns_thms : thm → ExceptT String IO (List thm)
  interpsigns_thms2 : thm → ExceptT String IO (List thm)
  interpsigns_tm : term
  dest_interpsigns : thm → Except String (term × term × term)
  mk_interpsigns : List thm → ExceptT String IO thm
  make_partition_list : List term → ExceptT String IO (List term)
  part_line_tm : term
  real_bool_ty : hol_type
  PARTITION_LINE_CONV : term → ExceptT String IO thm
  interpmat_tm : term
  dest_interpmat : term → Except String (term × term × term)
  interpmat_thms : thm → ExceptT String IO (thm × thm)
  mk_interpmat_thm : thm → thm → ExceptT String IO thm
  mk_all2_interpsigns : thm → List thm → ExceptT String IO thm
  dest_all2 : term → Except String (term × term × term)
  is_interval : term → Bool
  is_point : term → Bool
  new_var : (hol_type → IO term)
  reset_vars : (Unit → IO Unit)
  sz_z_thm : Option (IO.Ref thm)
  sz_nz_thm : Option (IO.Ref thm)
  core1 : CoreThms1

/-- RingTheory's `wPart` (copied verbatim).  `W(MP_TAC o PART_MATCH f th o g
    o snd)`: match `th`'s part `f` against the part `g` of the goal, and
    MP_TAC the instance. -/
def wPart [HolBase] (g : term → Except String term) (f : term → Except String term)
    (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (g gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)

/-- tactics.ml's NO_TAC. -/
def NO_TAC : tactic := HolCore.Tactics.NO_TAC



/- ---------------------------------------------------------------------- -/
/-  main_thms.ml 1-247.  The theorem phrases are converted by              -/
/-  gxwork/rq/ml2lean.py (disclosed; comments in their proofs are not      -/
/-  carried over); `empty_sgns` and the destructuring of monic_isign_lem   -/
/-  are by hand.                                                           -/
/- ---------------------------------------------------------------------- -/

structure MainThmsThms where
  -- @@FIELDS
  empty_mat : thm
  empty_sgns : List thm
  monic_isign_lem : thm
  gtpos : thm
  ltpos : thm
  gtneg : thm
  ltneg : thm
  gtzero : thm
  ltzero : thm
  main_lem000 : thm
  main_lem001 : thm
  main_lem002 : thm
  factor_pos_pos : thm
  factor_pos_neg : thm
  factor_pos_zero : thm
  factor_zero_pos : thm
  factor_zero_neg : thm
  factor_zero_zero : thm
  factor_neg_even_pos : thm
  factor_neg_even_neg : thm
  factor_neg_even_zero : thm
  factor_neg_odd_pos : thm
  factor_neg_odd_neg : thm
  factor_neg_odd_zero : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMainThmsThms [HolBase] (D : MainThmsDeps) :
    ExceptT String IO MainThmsThms := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, LIST_INDUCT_TAC, MESON_TAC,
        REAL_ARITH_TAC, prove_by_refinement, rx, .. } := D
  let { ALL2, LENGTH, NEQ, PARITY_POW_LT, POW_0, REAL_ADD_LID, REAL_ENTIRE,
        REAL_MUL_GT, REAL_MUL_LT, REAL_MUL_RID, REAL_POW_LT, ROL_EMPTY, interpmat,
        interpsign, interpsigns, num_CASES, partition_line, real_gt, .. } := D.core1
  -- @@SCOPE END

  let empty_mat ← prove_by_refinement (
    (← q r"interpmat [] [] [[]]"),
  [
    REWRITE_TAC [interpmat, ROL_EMPTY, interpsigns, ALL2, partition_line]
  ])

  let empty_sgns : List thm ← do
    pure [← ARITH_RULE (← q r"&1 > &0")]

  let monic_isign_lem ← prove
    r"(!s c mp p. (!x. c * p x = mp x) ==> c > &0 ==> interpsign s mp Pos ==> interpsign s p Pos) /\
   (!s c mp p. (!x. c * p x = mp x) ==> c < &0 ==> interpsign s mp Pos ==> interpsign s p Neg) /\
   (!s c mp p. (!x. c * p x = mp x) ==> c > &0 ==> interpsign s mp Neg ==> interpsign s p Neg) /\
   (!s c mp p. (!x. c * p x = mp x) ==> c < &0 ==> interpsign s mp Neg ==> interpsign s p Pos) /\
   (!s c mp p. (!x. c * p x = mp x) ==> c > &0 ==> interpsign s mp Zero ==> interpsign s p Zero) /\
   (!s c mp p. (!x. c * p x = mp x) ==> c < &0 ==> interpsign s mp Zero ==> interpsign s p Zero)"
    (REWRITE_TAC [interpsign] THEN REPEAT STRIP_TAC THEN POP_ASSUM (fun x => tactic_of do pure (POP_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))) THEN POP_ASSUM MP_TAC THEN POP_ASSUM (ASSUME_TAC o (GSYM o (ISPEC (← q r"x:real")))) THEN ASM_REWRITE_TAC [REAL_MUL_LT, REAL_MUL_GT, real_gt, REAL_ENTIRE] THEN REAL_ARITH_TAC)

  -- `let gtpos::ltpos::gtneg::ltneg::gtzero::ltzero::[] = CONJUNCTS ..`
  let (gtpos, ltpos, gtneg, ltneg, gtzero, ltzero) ←
    match CONJUNCTS monic_isign_lem with
    | [a, b, c, d, e, f] => pure (a, b, c, d, e, f)
    | _ => throw "Match_failure"

  let main_lem000 ← prove_by_refinement (
    (← q r"!l n. (LENGTH l = SUC n) ==> 0 < LENGTH l"),
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [LENGTH],
    ARITH_TAC,
    ARITH_TAC
  ])

  let main_lem001 ← prove_by_refinement (
    (← q r"x <> &0 ==> (LAST l = x) ==> LAST l <> &0"),
  [
    MESON_TAC []
  ])

  let main_lem002 ← prove_by_refinement (
    (← q r"(x <> y ==> x <> y) /\
   (x < y ==> x <> y) /\
   (x > y ==> x <> y) /\
   (~(x >= y) ==> x <> y) /\
   (~(x <= y) ==> x <> y) /\
   (~(x = y) ==> x <> y)"),
  [
    REWRITE_TAC [NEQ] THEN REAL_ARITH_TAC
  ])

  let factor_pos_pos ← prove_by_refinement (
    (← q r"interpsign s (\x. &0 + x * &1) Pos ==> interpsign s p Pos ==>
   (!x. x pow k * p x = q x) ==> interpsign s q Pos"),
  [
    REWRITE_TAC [interpsign, REAL_ADD_LID, REAL_MUL_RID],
    REPEAT STRIP_TAC,
    POP_ASSUM (fun x => RULE_ASSUM_TAC (fun y => tryCatch (MATCH_MP y x) (fun _ => (pure y)))),
    POP_ASSUM (ASSUME_TAC o ((ISPEC rx) o GSYM)),
    ASM_REWRITE_TAC [],
    REWRITE_TAC [REAL_MUL_GT, real_gt],
    DISJ2_TAC,
    ASM_MESON_TAC [REAL_POW_LT, real_gt]
  ])

  let factor_pos_neg ← prove_by_refinement (
    (← q r"interpsign s (\x. &0 + x * &1) Pos ==> interpsign s p Neg ==>
   (!x. x pow k * p x = q x) ==> interpsign s q Neg"),
  [
    REWRITE_TAC [interpsign, REAL_ADD_LID, REAL_MUL_RID],
    REPEAT STRIP_TAC,
    POP_ASSUM (fun x => RULE_ASSUM_TAC (fun y => tryCatch (MATCH_MP y x) (fun _ => (pure y)))),
    POP_ASSUM (ASSUME_TAC o ((ISPEC rx) o GSYM)),
    ASM_REWRITE_TAC [],
    REWRITE_TAC [REAL_MUL_LT, real_gt],
    DISJ2_TAC,
    ASM_MESON_TAC [REAL_POW_LT, real_gt]
  ])

  let factor_pos_zero ← prove_by_refinement (
    (← q r"interpsign s (\x. &0 + x * &1) Pos ==> interpsign s p Zero ==>
   (!x. x pow k * p x = q x) ==> interpsign s q Zero"),
  [
    REWRITE_TAC [interpsign, REAL_ADD_LID, REAL_MUL_RID],
    REPEAT STRIP_TAC,
    POP_ASSUM (fun x => RULE_ASSUM_TAC (fun y => tryCatch (MATCH_MP y x) (fun _ => (pure y)))),
    POP_ASSUM (ASSUME_TAC o ((ISPEC rx) o GSYM)),
    ASM_REWRITE_TAC [],
    REWRITE_TAC [REAL_MUL_LT, REAL_ENTIRE, real_gt]
  ])

  let factor_zero_pos ← prove_by_refinement (
    (← q r"interpsign s (\x. &0 + x * &1) Zero ==> interpsign s p Pos ==> ~(k = 0) ==>
   (!x. x pow k * p x = q x) ==> interpsign s q Zero"),
  [
    REWRITE_TAC [interpsign, REAL_ADD_LID, REAL_MUL_RID],
    REPEAT STRIP_TAC,
    POP_ASSUM (fun x => RULE_ASSUM_TAC (fun y => tryCatch (MATCH_MP y x) (fun _ => (pure y)))),
    POP_ASSUM (ASSUME_TAC o ((ISPEC rx) o GSYM)),
    ASM_REWRITE_TAC [],
    REWRITE_TAC [REAL_MUL_GT, REAL_MUL_LT, REAL_ENTIRE],
    DISJ1_TAC,
    ASM_MESON_TAC [POW_0, num_CASES]
  ])

  let factor_zero_neg ← prove_by_refinement (
    (← q r"interpsign s (\x. &0 + x * &1) Zero ==> interpsign s p Neg ==> ~(k = 0) ==>
   (!x. x pow k * p x = q x) ==> interpsign s q Zero"),
  [
    REWRITE_TAC [interpsign, REAL_ADD_LID, REAL_MUL_RID],
    REPEAT STRIP_TAC,
    POP_ASSUM (fun x => RULE_ASSUM_TAC (fun y => tryCatch (MATCH_MP y x) (fun _ => (pure y)))),
    POP_ASSUM (ASSUME_TAC o ((ISPEC rx) o GSYM)),
    ASM_REWRITE_TAC [],
    REWRITE_TAC [REAL_MUL_GT, REAL_MUL_LT, REAL_ENTIRE],
    DISJ1_TAC,
    ASM_MESON_TAC [POW_0, num_CASES]
  ])

  let factor_zero_zero ← prove_by_refinement (
    (← q r"interpsign s (\x. &0 + x * &1) Zero ==> interpsign s p Zero ==> ~(k = 0) ==>
   (!x. x pow k * p x = q x) ==> interpsign s q Zero"),
  [
    REWRITE_TAC [interpsign, REAL_ADD_LID, REAL_MUL_RID],
    REPEAT STRIP_TAC,
    POP_ASSUM (fun x => RULE_ASSUM_TAC (fun y => tryCatch (MATCH_MP y x) (fun _ => (pure y)))),
    POP_ASSUM (ASSUME_TAC o ((ISPEC rx) o GSYM)),
    ASM_REWRITE_TAC [],
    REAL_ARITH_TAC
  ])

  let factor_neg_even_pos ← prove_by_refinement (
    (← q r"interpsign s (\x. &0 + x * &1) Neg ==> interpsign s p Pos ==> EVEN k ==> ~(k = 0) ==>
   (!x. x pow k * p x = q x) ==> interpsign s q Pos"),
  [
    REWRITE_TAC [interpsign, REAL_ADD_LID, REAL_MUL_RID],
    REPEAT STRIP_TAC,
    POP_ASSUM (fun x => RULE_ASSUM_TAC (fun y => tryCatch (MATCH_MP y x) (fun _ => (pure y)))),
    POP_ASSUM (ASSUME_TAC o ((ISPEC rx) o GSYM)),
    ASM_REWRITE_TAC [],
    REWRITE_TAC [REAL_MUL_GT, REAL_MUL_LT, real_gt],
    DISJ2_TAC,
    ASM_MESON_TAC [REAL_POW_LT, real_gt, PARITY_POW_LT]
  ])

  let factor_neg_even_neg ← prove_by_refinement (
    (← q r"interpsign s (\x. &0 + x * &1) Neg ==> interpsign s p Neg ==> EVEN k ==> ~(k = 0) ==>
   (!x. x pow k * p x = q x) ==> interpsign s q Neg"),
  [
    REWRITE_TAC [interpsign, REAL_ADD_LID, REAL_MUL_RID],
    REPEAT STRIP_TAC,
    POP_ASSUM (fun x => RULE_ASSUM_TAC (fun y => tryCatch (MATCH_MP y x) (fun _ => (pure y)))),
    POP_ASSUM (ASSUME_TAC o ((ISPEC rx) o GSYM)),
    ASM_REWRITE_TAC [],
    REWRITE_TAC [REAL_MUL_GT, REAL_MUL_LT, real_gt],
    DISJ2_TAC,
    ASM_MESON_TAC [REAL_POW_LT, real_gt, PARITY_POW_LT]
  ])

  let factor_neg_even_zero ← prove_by_refinement (
    (← q r"interpsign s (\x. &0 + x * &1) Neg ==> interpsign s p Zero ==> EVEN k ==> ~(k = 0) ==>
   (!x. x pow k * p x = q x) ==> interpsign s q Zero"),
  [
    REWRITE_TAC [interpsign, REAL_ADD_LID, REAL_MUL_RID],
    REPEAT STRIP_TAC,
    POP_ASSUM (fun x => RULE_ASSUM_TAC (fun y => tryCatch (MATCH_MP y x) (fun _ => (pure y)))),
    POP_ASSUM (ASSUME_TAC o ((ISPEC rx) o GSYM)),
    ASM_REWRITE_TAC [],
    REWRITE_TAC [REAL_MUL_GT, REAL_MUL_LT, real_gt, REAL_ENTIRE]
  ])

  let factor_neg_odd_pos ← prove_by_refinement (
    (← q r"interpsign s (\x. &0 + x * &1) Neg ==> interpsign s p Pos ==> ODD k ==> ~(k = 0) ==>
   (!x. x pow k * p x = q x) ==> interpsign s q Neg"),
  [
    REWRITE_TAC [interpsign, REAL_ADD_LID, REAL_MUL_RID],
    REPEAT STRIP_TAC,
    POP_ASSUM (fun x => RULE_ASSUM_TAC (fun y => tryCatch (MATCH_MP y x) (fun _ => (pure y)))),
    POP_ASSUM (ASSUME_TAC o ((ISPEC rx) o GSYM)),
    ASM_REWRITE_TAC [],
    REWRITE_TAC [REAL_MUL_GT, REAL_MUL_LT, real_gt, REAL_ENTIRE],
    DISJ1_TAC,
    ASM_MESON_TAC [REAL_POW_LT, real_gt, PARITY_POW_LT]
  ])

  let factor_neg_odd_neg ← prove_by_refinement (
    (← q r"interpsign s (\x. &0 + x * &1) Neg ==> interpsign s p Neg ==> ODD k ==> ~(k = 0) ==>
   (!x. x pow k * p x = q x) ==> interpsign s q Pos"),
  [
    REWRITE_TAC [interpsign, REAL_ADD_LID, REAL_MUL_RID],
    REPEAT STRIP_TAC,
    POP_ASSUM (fun x => RULE_ASSUM_TAC (fun y => tryCatch (MATCH_MP y x) (fun _ => (pure y)))),
    POP_ASSUM (ASSUME_TAC o ((ISPEC rx) o GSYM)),
    ASM_REWRITE_TAC [],
    REWRITE_TAC [REAL_MUL_GT, REAL_MUL_LT, real_gt, REAL_ENTIRE],
    DISJ1_TAC,
    ASM_MESON_TAC [REAL_POW_LT, real_gt, PARITY_POW_LT]
  ])

  let factor_neg_odd_zero ← prove_by_refinement (
    (← q r"interpsign s (\x. &0 + x * &1) Neg ==> interpsign s p Zero ==> ODD k ==> ~(k = 0) ==>
   (!x. x pow k * p x = q x) ==> interpsign s q Zero"),
  [
    REWRITE_TAC [interpsign, REAL_ADD_LID, REAL_MUL_RID],
    REPEAT STRIP_TAC,
    POP_ASSUM (fun x => RULE_ASSUM_TAC (fun y => tryCatch (MATCH_MP y x) (fun _ => (pure y)))),
    POP_ASSUM (ASSUME_TAC o ((ISPEC rx) o GSYM)),
    ASM_REWRITE_TAC [],
    REWRITE_TAC [REAL_MUL_GT, REAL_MUL_LT, real_gt, REAL_ENTIRE]
  ])

  -- @@RETURN BEGIN
  return { empty_mat, empty_sgns, monic_isign_lem, gtpos, ltpos, gtneg, ltneg, gtzero,
           ltzero, main_lem000, main_lem001, main_lem002, factor_pos_pos, factor_pos_neg,
           factor_pos_zero, factor_zero_pos, factor_zero_neg, factor_zero_zero,
           factor_neg_even_pos, factor_neg_even_neg, factor_neg_even_zero,
           factor_neg_odd_pos, factor_neg_odd_neg, factor_neg_odd_zero }
  -- @@RETURN END

end HolRQE.MainThms
