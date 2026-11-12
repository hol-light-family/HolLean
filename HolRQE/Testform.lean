/- ========================================================================= -/
/- Rqe: evaluating a formula on the rows of a sign matrix.                 -/
/- ========================================================================= -/
/- File: HolRQE/Testform.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/testform.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml, Rqe/num_calc_simp.ml, Rqe/asym.ml, Rqe/rol.ml, Rqe/poly_ext.ml, Rqe/simplify.ml, Rqe/lift_qelim.ml, Rqe/defs.ml, Rqe/testform_thms.ml, Rqe/condense_thms.ml, Rqe/inferisign_thms.ml, Rqe/matinsert_thms.ml, Rqe/signs_thms.ml, Rqe/inferpsign_thms.ml, Rqe/dedmatrix_thms.ml, Rqe/pdivides_thms.ml, Rqe/main_thms.ml, Rqe/work_thms.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.Testform fills them).

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
import HolRQE.MainThms
import HolRQE.WorkThms

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
open HolRQE.MainThms
open HolRQE.WorkThms

namespace HolRQE.Testform

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALL2 FORALL_NOT_THM NOT_EXISTS_CONJ_THM TRUTH all2_thm and_thm_nn and_thm_np
   and_thm_pn and_thm_pp eq_ge_thm eq_gt_thm eq_le_thm eq_lt_thm f_thm gen_thm
   gt_eq_thm gt_ge_thm gt_le_thm gt_lt_thm iff_thm_nn iff_thm_np iff_thm_pn
   iff_thm_pp imp_thm_n imp_thm_pn imp_thm_pp lem1 lem2 lt_eq_thm lt_ge_thm
   lt_gt_thm lt_le_thm neg_thm_n neg_thm_p or_thm_nn or_thm_p or_thm_q t1 t_thm
   testform_itlem : thm)
  deriving Inhabited

/-- What testform.ml uses from Session besides theorems. -/
structure TestformDeps where
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
  empty_sgns : List thm
  LENGTH_N : Int → hol_type → ExceptT String IO thm
  NUM_CASES_TAC : term → tactic
  FUN_EQ_TAC : tactic
  EXISTS_TACL : List term → tactic
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

/-- HOL Light's `map2` (lib.ml) with a fallible function: left to right,
    failing with "map2: length mismatch" where the lists' lengths part. -/
def map2M {α β γ : Type} (f : α → β → ExceptT String IO γ) :
    List α → List β → ExceptT String IO (List γ)
  | [], [] => pure []
  | h1 :: t1, h2 :: t2 => do
    let h ← f h1 h2
    return h :: (← map2M f t1 t2)
  | _, _ => throw "map2: length mismatch"

/-- What TESTFORM closes over: the theorems of testform_thms.ml, rqe_real.ml's
    relations, lift_qelim.ml's `t_tm`/`f_tm` and defs.ml's functions. -/
structure TestformEnv where
  t_tm : term
  f_tm : term
  req : term
  rlt : term
  rgt : term
  rle : term
  rge : term
  dest_interpsigns : thm → Except String (term × term × term)
  interpsigns_thms : thm → ExceptT String IO (List thm)
  t_thm : thm
  f_thm : thm
  neg_thm_p : thm
  neg_thm_n : thm
  and_thm_nn : thm
  and_thm_np : thm
  and_thm_pn : thm
  and_thm_pp : thm
  or_thm_nn : thm
  or_thm_p : thm
  or_thm_q : thm
  imp_thm_n : thm
  imp_thm_pn : thm
  imp_thm_pp : thm
  iff_thm_nn : thm
  iff_thm_np : thm
  iff_thm_pn : thm
  iff_thm_pp : thm
  lt_eq_thm : thm
  gt_eq_thm : thm
  eq_lt_thm : thm
  gt_lt_thm : thm
  eq_gt_thm : thm
  lt_gt_thm : thm
  lt_le_thm : thm
  eq_le_thm : thm
  gt_le_thm : thm
  lt_ge_thm : thm
  eq_ge_thm : thm
  gt_ge_thm : thm

/-- testform.ml's `let rec TESTFORM var interpsigns_thm set_thm fm`. -/
partial def TESTFORM.go [HolBase] (E : TestformEnv) (var : term) (interpsigns_thm set_thm : thm)
    (fm : term) : ExceptT String IO thm := do
  let rec_ := TESTFORM.go E var interpsigns_thm set_thm
  let { t_tm, f_tm, req, rlt, rgt, rle, rge, dest_interpsigns, interpsigns_thms, .. } := E
  let (polys, set, signs) ← liftExcept (dest_interpsigns interpsigns_thm)
  let polys' ← liftExcept (dest_list polys)
  let signs' ← liftExcept (dest_list signs)
  -- the four-way and three-way cases of the connectives: `MATCH_MPL [BETA_RULE
  -- (ISPECL [a';b';set] th); ..]`
  let inst2 (th : thm) (a' b' : term) : ExceptT String IO thm := do
    BETA_RULE (← ISPECL [a', b', set] th)
  if fm == t_tm then BETA_RULE (← ISPECL [set] E.t_thm)
  else if fm == f_tm then BETA_RULE (← ISPECL [set] E.f_thm)
  else if is_neg fm then
    let lam ← liftExcept (mk_abs var (← liftExcept (dest_neg fm)))
    let thm ← rec_ (← liftExcept (dest_neg fm))
    if is_pos (concl thm) then
      MATCH_MP (← BETA_RULE (← ISPECL [lam, set] E.neg_thm_p)) thm
    else if is_neg (concl thm) then
      MATCH_MP (← BETA_RULE (← ISPECL [lam, set] E.neg_thm_n)) thm
    else throw "error"
  else if is_conj fm then
    let (a, b) ← liftExcept (dest_conj fm)
    -- `let a',b' = mk_abs (var,a),mk_abs (var,b)`, right to left
    let b' ← liftExcept (mk_abs var b)
    let a' ← liftExcept (mk_abs var a)
    let thma ← rec_ a
    let thmb ← rec_ b
    if is_neg (concl thma) && is_neg (concl thmb) then
      MATCH_MPL [← inst2 E.and_thm_nn a' b', set_thm, thma, thmb]
    else if is_neg (concl thma) && is_pos (concl thmb) then
      MATCH_MPL [← inst2 E.and_thm_np a' b', set_thm, thma, thmb]
    else if is_pos (concl thma) && is_neg (concl thmb) then
      MATCH_MPL [← inst2 E.and_thm_pn a' b', set_thm, thma, thmb]
    else if is_pos (concl thma) && is_pos (concl thmb) then
      MATCH_MPL [← inst2 E.and_thm_pp a' b', set_thm, thma, thmb]
    else throw "error"
  else if is_disj fm then
    let (a, b) ← liftExcept (dest_disj fm)
    let b' ← liftExcept (mk_abs var b)
    let a' ← liftExcept (mk_abs var a)
    let thma ← rec_ a
    let thmb ← rec_ b
    if is_neg (concl thma) && is_neg (concl thmb) then
      MATCH_MPL [← inst2 E.or_thm_nn a' b', set_thm, thma, thmb]
    else if is_pos (concl thma) then
      MATCH_MPL [← inst2 E.or_thm_p a' b', set_thm, thma]
    else if is_pos (concl thmb) then
      MATCH_MPL [← inst2 E.or_thm_q a' b', set_thm, thmb]
    else throw "error"
  else if is_imp fm then
    let (a, b) ← liftExcept (dest_imp fm)
    let b' ← liftExcept (mk_abs var b)
    let a' ← liftExcept (mk_abs var a)
    let thma ← rec_ a
    let thmb ← rec_ b
    if is_neg (concl thma) then
      MATCH_MPL [← inst2 E.imp_thm_n a' b', set_thm, thma]
    else if is_pos (concl thma) && is_neg (concl thmb) then
      MATCH_MPL [← inst2 E.imp_thm_pn a' b', set_thm, thma, thmb]
    else if is_pos (concl thma) && is_pos (concl thmb) then
      MATCH_MPL [← inst2 E.imp_thm_pp a' b', set_thm, thmb]
    else throw "error"
  else if HolCore.Bool.is_iff fm then
    let (a, b) ← liftExcept (dest_eq fm)
    let b' ← liftExcept (mk_abs var b)
    let a' ← liftExcept (mk_abs var a)
    let thma ← rec_ a
    let thmb ← rec_ b
    if is_neg (concl thma) && is_neg (concl thmb) then
      MATCH_MPL [← inst2 E.iff_thm_nn a' b', set_thm, thma, thmb]
    else if is_neg (concl thma) && is_pos (concl thmb) then
      MATCH_MPL [← inst2 E.iff_thm_np a' b', set_thm, thma, thmb]
    else if is_pos (concl thma) && is_neg (concl thmb) then
      MATCH_MPL [← inst2 E.iff_thm_pn a' b', set_thm, thma, thmb]
    else if is_pos (concl thma) && is_pos (concl thmb) then
      MATCH_MPL [← inst2 E.iff_thm_pp a' b', set_thm, thma, thmb]
    else throw "error"
  else /- an atom -/
    let (op, p, _) ← liftExcept (get_binop fm)
    let lam ← liftExcept (mk_abs var p)
    let ind ← match index lam polys' with
      | .ok i => pure (i : Int)
      | .error "index" => throw "TESTFORM: Poly not present in list"
      | .error e => throw e
    let inst1 (th : thm) : ExceptT String IO thm := do BETA_RULE (← ISPECL [lam, set] th)
    let _sign ← liftExcept (ith ind signs')
    let thm ← liftExcept (ith ind (← interpsigns_thms interpsigns_thm))
    let (thm_op, _thm_p, _) ← liftExcept (get_binop
      (← liftExcept (dest_imp (← liftExcept (dest_forall (concl thm))).2)).2)
    if op == req then
      if thm_op == req then pure thm
      else if thm_op == rlt then
        MATCH_MPL [← inst1 E.lt_eq_thm, thm]
      else if thm_op == rgt then
        MATCH_MPL [← inst1 E.gt_eq_thm, thm]
      else throw "error"
    else if op == rlt then
      if thm_op == rlt then pure thm
      else if thm_op == req then
        MATCH_MPL [← inst1 E.eq_lt_thm, thm]
      else if thm_op == rgt then
        MATCH_MPL [← inst1 E.gt_lt_thm, thm]
      else throw "error"
    else if op == rgt then
      if thm_op == rgt then pure thm
      else if thm_op == req then
        MATCH_MPL [← inst1 E.eq_gt_thm, thm]
      else if thm_op == rlt then
        MATCH_MPL [← inst1 E.lt_gt_thm, thm]
      else throw "error"
    else if op == rle then
      if thm_op == rlt then
        MATCH_MPL [← inst1 E.lt_le_thm, thm]
      else if thm_op == req then
        MATCH_MPL [← inst1 E.eq_le_thm, thm]
      else if thm_op == rgt then
        MATCH_MPL [← inst1 E.gt_le_thm, thm]
      else throw "error"
    else if op == rge then
      if thm_op == rlt then
        MATCH_MPL [← inst1 E.lt_ge_thm, thm]
      else if thm_op == req then
        MATCH_MPL [← inst1 E.eq_ge_thm, thm]
      else if thm_op == rgt then
        MATCH_MPL [← inst1 E.gt_ge_thm, thm]
      else throw "error"
    else throw "error"



/- ====================================================================== -/
/-  TESTFORM (testform.ml 1-218; the examples are in a comment there)     -/
/- ====================================================================== -/

structure TestformFns where
  -- @@FIELDS
  TESTFORM : term → thm → thm → term → ExceptT String IO thm
  tvar : Option (IO.Ref term)
  tmat : Option (IO.Ref thm)
  tfm : Option (IO.Ref term)
  COMBINE_TESTFORMS : term → thm → term → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupTestformFns [HolBase] (D : TestformDeps) :
    ExceptT String IO TestformFns := do
  -- @@SCOPE BEGIN
  let { MATCH_EQ_MP, PARTITION_LINE_CONV, ROL_COVERS, TAUT, combine_testforms_timer,
        dest_interpsigns, f_tm, interpmat_thms, interpsigns_thms, new_var, real_ty,
        req, rge, rgt, rle, rlt, rol_nonempty_thms, t_tm, testform_timer, .. } := D
  let { ALL2, FORALL_NOT_THM, NOT_EXISTS_CONJ_THM, TRUTH, and_thm_nn, and_thm_np,
        and_thm_pn, and_thm_pp, eq_ge_thm, eq_gt_thm, eq_le_thm, eq_lt_thm, f_thm,
        gt_eq_thm, gt_ge_thm, gt_le_thm, gt_lt_thm, iff_thm_nn, iff_thm_np, iff_thm_pn,
        iff_thm_pp, imp_thm_n, imp_thm_pn, imp_thm_pp, lt_eq_thm, lt_ge_thm, lt_gt_thm,
        lt_le_thm, neg_thm_n, neg_thm_p, or_thm_nn, or_thm_p, or_thm_q, t_thm,
        testform_itlem, .. } := D.core1
  -- @@SCOPE END

  -- `let rec TESTFORM ..` (its recursion is TESTFORM.go), rebound below by
  -- the timed TESTFORM
  let TESTFORM : term → thm → thm → term → ExceptT String IO thm ← pure (TESTFORM.go
    { t_tm, f_tm, req, rlt, rgt, rle, rge, dest_interpsigns, interpsigns_thms,
      t_thm, f_thm, neg_thm_p, neg_thm_n, and_thm_nn, and_thm_np, and_thm_pn, and_thm_pp,
      or_thm_nn, or_thm_p, or_thm_q, imp_thm_n, imp_thm_pn, imp_thm_pp,
      iff_thm_nn, iff_thm_np, iff_thm_pn, iff_thm_pp,
      lt_eq_thm, gt_eq_thm, eq_lt_thm, gt_lt_thm, eq_gt_thm, lt_gt_thm,
      lt_le_thm, eq_le_thm, gt_le_thm, lt_ge_thm, eq_ge_thm, gt_ge_thm })

  let TESTFORM : term → thm → thm → term → ExceptT String IO thm ← pure
    (fun var interpsigns_thm set_thm fm => do
      let start_time ← sys_time
      let res ← TESTFORM var interpsigns_thm set_thm fm
      plus_dot_eq' testform_timer ((← sys_time) - start_time)
      pure res)


  -- `let tvar,tmat,tfm = ref `T`,ref TRUTH,ref `T``: the tuple right to left;
  -- exported as `some ref` (see HolRQE/Rewrites.lean)
  let loc_tfm : IO.Ref term ← IO.mkRef (← q r"T")
  let loc_tmat : IO.Ref thm ← IO.mkRef TRUTH
  let loc_tvar : IO.Ref term ← IO.mkRef (← q r"T")
  let tvar : Option (IO.Ref term) ← pure (some loc_tvar)
  let tmat : Option (IO.Ref thm) ← pure (some loc_tmat)
  let tfm : Option (IO.Ref term) ← pure (some loc_tfm)
  /-
  let var,mat_thm,fm = !tvar,!tmat,!tfm
  -/

  let COMBINE_TESTFORMS : term → thm → term → ExceptT String IO thm ← do
    let lem1 ← TAUT (← q r"(T ==> a) <=> a")
    let lem2 ← TAUT (← q r"(T /\ x) <=> x")
    let _imat_tm ← q r"interpmat"
    pure (fun var mat_thm fm => do
      loc_tvar.set var
      loc_tmat.set mat_thm
      loc_tfm.set fm
      /- if not (fst (strip_comb (concl mat_thm)) = imat_tm) then failwith "not a mat thm" else -/
      let alpha : ioconv := fun t => pure (HolCore.Equal.ALPHA_CONV var t)
      let mat_thm' ← (CONV_RULE (RATOR_CONV (RAND_CONV (HolMath.Lists.LIST_CONV_IO alpha)))) mat_thm
      let (rol_thm, all2_thm) ← interpmat_thms mat_thm'
      let ord_thms ← rol_nonempty_thms rol_thm
      let part_thm ← PARTITION_LINE_CONV (← liftExcept (dest_comb (concl rol_thm))).2
      let isigns_thms := CONJUNCTS (← REWRITE_RULE [ALL2, part_thm] all2_thm)
      let ex_thms ← map2M (fun x y => TESTFORM var x y fm) isigns_thms ord_thms
      if ex_thms.any (fun x => is_forall (concl x)) then
        let witness_thm ← liftExcept (HolCore.Lib.find (fun x => is_forall (concl x)) ex_thms)
        let i ← match ex_thms.findIdx? (· == witness_thm) with
          | some i => pure (i : Int)
          | none => throw "COMBINE_TESTFORMS: witness not present"
        let ord_thm ← liftExcept (ith i ord_thms)
        let (_x, bod) ← liftExcept (dest_exists (concl ord_thm))
        if bod == t_tm then
          let thm1 ← ISPEC var witness_thm
          let thm2 ← PURE_REWRITE_RULE [lem1] thm1
          let exists_thm ← EXISTS (← liftExcept (HolCore.Bool.mk_exists var (concl thm2)), var) thm2
          EQT_INTRO exists_thm
        else
          let nv ← new_var real_ty
          let ord_thm' ← CONV_RULE (RAND_CONV (fun t => pure (HolCore.Equal.ALPHA_CONV nv t))) ord_thm
          let (y, bod) ← liftExcept (dest_exists (concl ord_thm'))
          let ass_thm ← liftExcept (HolCore.Kernel.ASSUME bod)
          let thm ← MATCH_MP witness_thm ass_thm
          let exists_thm ← EXISTS (← liftExcept (HolCore.Bool.mk_exists y (concl thm)), y) thm
          let ret ← CHOOSE (nv, ord_thm) exists_thm
          EQT_INTRO ret
      else
        if ord_thms.length = 1 &&
            (← liftExcept (dest_exists (concl (← liftExcept (hd ord_thms))))).2 == t_tm then
          PURE_REWRITE_RULE [lem2] (← EQF_INTRO (← liftExcept (hd ex_thms))) else
        let ex_thms' ← ex_thms.mapM (MATCH_MP NOT_EXISTS_CONJ_THM)
        let len := ex_thms'.length
        let (first, t1, t2) ← do
          if len < 2 then throw "chop_list"
          match ← liftExcept (chop_list (len - 2) ex_thms') with
          | (first, [t1, t2]) => pure (first, t1, t2)
          | _ => throw "Match_failure"
        let base ← MATCH_MPL [testform_itlem, t1, t2]
        let ex_thm ← first.foldrM (fun x y => MATCH_MPL [testform_itlem, x, y]) base
        let cover_thm ← ROL_COVERS rol_thm
        let pre_thm ← MATCH_MP ex_thm (← ISPEC var cover_thm)
        let gen_thm ← GEN var pre_thm
        let ret ← MATCH_EQ_MP FORALL_NOT_THM gen_thm
        EQF_INTRO ret)

  let COMBINE_TESTFORMS : term → thm → term → ExceptT String IO thm ← pure
    (fun var mat_thm fm => do
      let start_time ← sys_time
      let res ← COMBINE_TESTFORMS var mat_thm fm
      plus_dot_eq' combine_testforms_timer ((← sys_time) - start_time)
      pure res)

  /- {{{ Examples -/
  /- (in testform.ml) -/
  /- }}} -/

  -- @@RETURN BEGIN
  return { TESTFORM, tvar, tmat, tfm, COMBINE_TESTFORMS }
  -- @@RETURN END

end HolRQE.Testform
