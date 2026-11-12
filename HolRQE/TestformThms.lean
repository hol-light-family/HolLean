/- ========================================================================= -/
/- Rqe: theorems for evaluating a formula on a sign matrix row.            -/
/- ========================================================================= -/
/- File: HolRQE/TestformThms.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/testform_thms.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml, Rqe/num_calc_simp.ml, Rqe/asym.ml, Rqe/rol.ml, Rqe/poly_ext.ml, Rqe/simplify.ml, Rqe/lift_qelim.ml, Rqe/defs.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.TestformThms fills them).

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

namespace HolRQE.TestformThms

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (REAL_LT_LE REAL_LT_REFL REAL_LT_TRANS real_ge real_gt real_le : thm)
  deriving Inhabited

/-- What testform_thms.ml uses from Session besides theorems. -/
structure TestformThmsDeps where
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



/- ------------------------------------------------------------------------- -/
/- Evaluate a quantifier-free formula given a sign matrix row for its polys. -/
/- (testform_thms.ml 1-196; the OCaml model `testform` and its notes are in  -/
/- a comment there.)                                                         -/
/- ------------------------------------------------------------------------- -/

structure TestformThms where
  -- @@FIELDS
  t_thm : thm
  f_thm : thm
  neg_thm_p : thm
  neg_thm_n : thm
  and_thm_pp : thm
  and_thm_pn : thm
  and_thm_np : thm
  and_thm_nn : thm
  or_thm_p : thm
  or_thm_q : thm
  or_thm_nn : thm
  imp_thm_pp : thm
  imp_thm_pn : thm
  imp_thm_n : thm
  iff_thm_pp : thm
  iff_thm_pn : thm
  iff_thm_np : thm
  iff_thm_nn : thm
  eq_lt_thm : thm
  gt_lt_thm : thm
  lt_eq_thm : thm
  gt_eq_thm : thm
  eq_gt_thm : thm
  lt_gt_thm : thm
  lt_le_thm : thm
  eq_le_thm : thm
  gt_le_thm : thm
  lt_ge_thm : thm
  eq_ge_thm : thm
  gt_ge_thm : thm
  NOT_EXISTS_CONJ_THM : thm
  testform_itlem : thm
  deriving Inhabited

@[nospecialize]
def setupTestformThms [HolBase] (D : TestformThmsDeps) :
    ExceptT String IO TestformThms := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, prove_by_refinement, .. } := D
  let { REAL_LT_LE, REAL_LT_REFL, REAL_LT_TRANS, real_ge, real_gt, real_le, .. } := D.core1
  -- @@SCOPE END

  /- ====================================================================== -/
  /-  Theorems                                                              -/
  /- ====================================================================== -/

  /- --------------------------------  T   -------------------------------- -/

  let t_thm ← prove r"!set:real->bool. (!x. set x ==> T)" (MESON_TAC [])

  /- --------------------------------  F  --------------------------------- -/

  let f_thm ← prove r"!set:real->bool. ~(?x. set x /\ F)" (MESON_TAC [])

  /- --------------------------------  ~  --------------------------------- -/

  let neg_thm_p ← prove
    r"!P set. (!x. set x ==> P x) ==> (~ ?x. set x /\ ~ P x)" (MESON_TAC [])

  let neg_thm_n ← prove
    r"!P set. (~ ?x. set x /\ P x) ==> (!x. set x ==> ~ P x)" (MESON_TAC [])

  /- --------------------------------  /\  -------------------------------- -/

  let and_thm_pp ← prove
    r"!P Q set. (?x. set x) ==> (!x. set x ==> P x) ==> (!x. set x ==> Q x) ==>
          (!x. set x ==> (P x /\ Q x))" (MESON_TAC [])

  let and_thm_pn ← prove
    r"!P Q set. (?x. set x) ==> (!x. set x ==> P x) ==>
       (~ ?x. set x /\ Q x) ==> (~ ?x. set x /\ P x /\ Q x)" (MESON_TAC [])

  let and_thm_np ← prove
    r"!P Q set. (?x. set x) ==> (~ ?x. set x /\ P x) ==>
            (!x. set x ==> Q x) ==> (~ ?x. set x /\ P x /\ Q x)" (MESON_TAC [])

  let and_thm_nn ← prove
    r"!P Q set. (?x. set x) ==> (~ ?x. set x /\ P x) ==>
      (~ ?x. set x /\ Q x) ==> (~ ?x. set x /\ P x /\ Q x)" (MESON_TAC [])

  /- --------------------------------  \/  -------------------------------- -/

  let or_thm_p ← prove
    r"!P Q set. (?x. set x) ==> (!x. set x ==> P x) ==> (!x. set x ==> (P x \/ Q x))"
    (MESON_TAC [])

  let or_thm_q ← prove
    r"!P Q set. (?x. set x) ==> (!x. set x ==> Q x) ==> (!x. set x ==> (P x \/ Q x))"
    (MESON_TAC [])

  let or_thm_nn ←
    prove r"!P Q set. (?x. set x) ==> (~ ?x. set x /\ P x) ==>
            (~ ?x. set x /\ Q x) ==> (~ ?x. set x /\ (P x \/ Q x))" (MESON_TAC [])

  /- -------------------------------  ==>  -------------------------------- -/

  let imp_thm_pp ←
    prove r"!P Q set. (?x. set x) ==> (!x. set x ==> Q x) ==>
          (!x. set x ==> (P x ==> Q x))" (MESON_TAC [])

  let imp_thm_pn ←
    prove r"!P Q set. (?x. set x) ==> (!x. set x ==> P x) ==>
          (~ ?x. set x /\ Q x) ==> (~ ?x. set x /\ (P x ==> Q x))" (MESON_TAC [])

  let imp_thm_n ←
    prove r"!P Q set. (?x. set x) ==> (~ ?x. set x /\ P x) ==>
       (!x. set x ==> (P x ==> Q x))" (MESON_TAC [])

  /- --------------------------------  =  --------------------------------- -/

  let iff_thm_pp ← prove
    r"!P Q set. (?x. set x) ==> (!x. set x ==> P x) ==> (!x. set x ==> Q x) ==>
          (!x. set x ==> (P x <=> Q x))" (MESON_TAC [])

  let iff_thm_pn ← prove
    r"!P Q set. (?x. set x) ==> (!x. set x ==> P x) ==>
       (~ ?x. set x /\ Q x) ==> (~ ?x. set x /\ (P x <=> Q x))" (MESON_TAC [])

  let iff_thm_np ← prove
    r"!P Q set. (?x. set x) ==> (~ ?x. set x /\ P x) ==>
            (!x. set x ==> Q x) ==> (~ ?x. set x /\ (P x <=> Q x))" (MESON_TAC [])

  let iff_thm_nn ← prove
    r"!P Q set. (?x. set x) ==> (~ ?x. set x /\ P x) ==>
      (~ ?x. set x /\ Q x) ==> (!x. set x ==> (P x <=> Q x))" (MESON_TAC [])

  /- ---------------------------------------------------------------------- -/
  /-  Atoms                                                                 -/
  /- ---------------------------------------------------------------------- -/

  /- ---------------------------  ?x. p x < &0  --------------------------- -/

  let eq_lt_thm ← prove
    r"!P set. (!x. set x ==> (P x = &0)) ==> ~ ?x. set x /\ P x < &0"
    (MESON_TAC [REAL_LT_LE])

  let gt_lt_thm ← prove
    r"!P set. (!x. set x ==> (P x > &0)) ==> ~ ?x. set x /\ P x < &0"
    (MESON_TAC [real_gt, REAL_LT_REFL, REAL_LT_TRANS])

  /- ---------------------------  ?x. p x = &0  --------------------------- -/

  let lt_eq_thm ← prove
    r"!P set. (!x. set x ==> (P x < &0)) ==> ~ ?x. set x /\ (P x = &0)"
    (MESON_TAC [REAL_LT_LE])

  let gt_eq_thm ← prove
    r"!P set. (!x. set x ==> (P x > &0)) ==> ~ ?x. set x /\ (P x = &0)"
    (MESON_TAC [real_gt, REAL_LT_LE])

  /- ---------------------------  ?x. p x > &0  --------------------------- -/

  let eq_gt_thm ← prove
    r"!P set. (!x. set x ==> (P x = &0)) ==> ~ ?x. set x /\ (P x > &0)"
    (MESON_TAC [real_gt, REAL_LT_LE])

  let lt_gt_thm ← prove
    r"!P set. (!x. set x ==> (P x < &0)) ==> ~ ?x. set x /\ (P x > &0)"
    (MESON_TAC [real_gt, REAL_LT_LE, REAL_LT_TRANS])

  /- --------------------------  ?x. p x <= &0  --------------------------- -/

  let lt_le_thm ← prove
    r"!P set. (!x. set x ==> (P x < &0)) ==> !x. set x ==> (P x <= &0)"
    (MESON_TAC [real_gt, REAL_LT_LE, REAL_LT_TRANS])

  let eq_le_thm ← prove
    r"!P set. (!x. set x ==> (P x = &0)) ==> (!x. set x ==> (P x <= &0))"
    (MESON_TAC [real_gt, REAL_LT_LE, REAL_LT_TRANS, real_le])

  let gt_le_thm ← prove
    r"!P set. (!x. set x ==> (P x > &0)) ==> ~ ?x. set x /\ (P x <= &0)"
    (MESON_TAC [real_gt, REAL_LT_LE, REAL_LT_TRANS, real_le])

  /- --------------------------  ?x. p x >= &0  --------------------------- -/

  let lt_ge_thm ← prove
    r"!P set. (!x. set x ==> (P x < &0)) ==> ~ ?x. set x /\ (P x >= &0)"
    (MESON_TAC [real_gt, REAL_LT_LE, REAL_LT_TRANS, real_ge])

  let eq_ge_thm ← prove
    r"!P set. (!x. set x ==> (P x = &0)) ==> (!x. set x ==> (P x >= &0))"
    (MESON_TAC [real_gt, REAL_LT_LE, REAL_LT_TRANS, real_ge, real_le])

  let gt_ge_thm ← prove
    r"!P set. (!x. set x ==> (P x > &0)) ==> (!x. set x ==> (P x >= &0))"
    (MESON_TAC [real_gt, REAL_LT_LE, REAL_LT_TRANS, real_ge, real_le])

  /- let lookup_sign isigns_thm fm =  -/
  /-   let asms,_ = dest_thm isigns_thm in -/
  /-   let    -/


  let NOT_EXISTS_CONJ_THM ← prove_by_refinement (
    (← q r"~(?x. P x /\ Q x) ==> (!x. P x ==> ~Q x)"),
  /- {{{ Proof -/
  [
    MESON_TAC []
  ])
  /- }}} -/

  let testform_itlem ← prove_by_refinement (
    (← q r"(!x. P x ==> ~Q x) ==> (!x. P2 x ==> ~Q x) ==> (!x. P x \/ P2 x ==> ~ Q x)"),
  /- {{{ Proof -/
  [MESON_TAC []])
  /- }}} -/

  -- @@RETURN BEGIN
  return { t_thm, f_thm, neg_thm_p, neg_thm_n, and_thm_pp, and_thm_pn, and_thm_np,
           and_thm_nn, or_thm_p, or_thm_q, or_thm_nn, imp_thm_pp, imp_thm_pn, imp_thm_n,
           iff_thm_pp, iff_thm_pn, iff_thm_np, iff_thm_nn, eq_lt_thm, gt_lt_thm,
           lt_eq_thm, gt_eq_thm, eq_gt_thm, lt_gt_thm, lt_le_thm, eq_le_thm, gt_le_thm,
           lt_ge_thm, eq_ge_thm, gt_ge_thm, NOT_EXISTS_CONJ_THM, testform_itlem }
  -- @@RETURN END

end HolRQE.TestformThms
