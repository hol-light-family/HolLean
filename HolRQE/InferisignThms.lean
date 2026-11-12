/- ========================================================================= -/
/- Rqe: theorems for inferring the signs of a polynomial on intervals.     -/
/- ========================================================================= -/
/- File: HolRQE/InferisignThms.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/inferisign_thms.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml, Rqe/num_calc_simp.ml, Rqe/asym.ml, Rqe/rol.ml, Rqe/poly_ext.ml, Rqe/simplify.ml, Rqe/lift_qelim.ml, Rqe/defs.ml, Rqe/testform_thms.ml, Rqe/condense_thms.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.InferisignThms fills them).

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

namespace HolRQE.InferisignThms

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (POLY_IVT_NEG POLY_IVT_POS POLY_MVT REAL_ENTIRE REAL_LT_ANTISYM REAL_LT_IMP_NZ
   REAL_LT_NZ REAL_LT_TRANS REAL_MUL_GT REAL_MUL_LT real_gt real_sub : thm)
  deriving Inhabited

/-- What inferisign_thms.ml uses from Session besides theorems. -/
structure InferisignThmsDeps where
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



/- ---------------------------------------------------------------------- -/
/- inferisign_thms.ml lines 1-2000, converted by gxwork/rq/ml2lean.py     -/
/- (disclosed); comments in the proofs are not carried over.              -/
/- ---------------------------------------------------------------------- -/

structure InferisignThmsThms where
  -- @@FIELDS
  inferisign_lem00 : thm
  neg_neg_neq_thm : thm
  neg_neg_neq_thm2 : thm
  pos_pos_neq_thm : thm
  pos_pos_neq_thm2 : thm
  pos_neg_neq_thm : thm
  pos_neg_neq_thm2 : thm
  neg_pos_neq_thm : thm
  neg_pos_neq_thm2 : thm
  lt_nz_thm : thm
  gt_nz_thm : thm
  eq_eq_false_thm : thm
  neg_zero_neg_thm : thm
  pos_zero_pos_thm : thm
  zero_neg_neg_thm : thm
  zero_pos_pos_thm : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupInferisignThmsThms [HolBase] (D : InferisignThmsDeps) :
    ExceptT String IO InferisignThmsThms := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, CLAIM, EXISTS_TAC, MESON_TAC, REAL_ARITH,
        REAL_ARITH_TAC, REAL_SIMP_TAC, prove_by_refinement, .. } := D
  let { POLY_IVT_NEG, POLY_IVT_POS, POLY_MVT, REAL_ENTIRE, REAL_LT_ANTISYM,
        REAL_LT_IMP_NZ, REAL_LT_NZ, REAL_LT_TRANS, REAL_MUL_GT, REAL_MUL_LT, real_gt,
        real_sub, .. } := D.core1
  -- @@SCOPE END

  let inferisign_lem00 ← prove_by_refinement (
    (← q r"x1 < x3 ==> x3 < x2 ==> (!x. x1 < x /\ x < x2 ==> P x) ==>
    (!x. x1 < x /\ x < x3 ==> P x) /\
    (!x. (x = x3) ==> P x) /\
    (!x. x3 < x /\ x < x2 ==> P x)"),
  [
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_REWRITE_TAC [],
    MATCH_MP_TAC REAL_LT_TRANS,
    EXISTS_TAC (← q r"x3"),
    ASM_REWRITE_TAC [],
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_REWRITE_TAC [],
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_REWRITE_TAC [],
    MATCH_MP_TAC REAL_LT_TRANS,
    EXISTS_TAC (← q r"x3"),
    ASM_REWRITE_TAC []
  ])

  let neg_neg_neq_thm ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"x < y <=> ~(y <= x)")
    prove_by_refinement (
      (← q r"!x y p. x < y /\ poly p x < &0 /\ poly p y < &0 /\
              (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
              (!z. x < z /\ z < y ==> poly p z < &0)"),
    [
      REPEAT STRIP_TAC,
      REWRITE_TAC [r1],
      STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"x:real"), (← q r"z:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      CLAIM (← q r"&0 < poly p z - poly p x"),
      LABEL_ALL_TAC,
      USE_THEN "Z-3" MP_TAC,
      USE_THEN "Z-8" MP_TAC,
      REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"&0 < (z - x) * poly (poly_diff p) x'"),
      REPEAT_N 2 (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC,
      ASM_REWRITE_TAC [REAL_MUL_GT],
      REPEAT STRIP_TAC,
      CLAIM (← q r"&0 < z - x"),
      LABEL_ALL_TAC,
      USE_THEN "Z-8" MP_TAC THEN REAL_ARITH_TAC,
      LABEL_ALL_TAC,
      USE_THEN "Z-1" MP_TAC THEN REAL_ARITH_TAC,
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"z:real"), (← q r"y:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      CLAIM (← q r"poly p y - poly p z < &0"),
      LABEL_ALL_TAC,
      USE_THEN "Z-13" MP_TAC,
      USE_THEN "Z-9" MP_TAC,
      REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"&0 < y - z"),
      LABEL_ALL_TAC,
      USE_THEN "Z-11" MP_TAC THEN REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"(y - z) * poly (poly_diff p) x'' < &0"),
      POP_ASSUM IGNORE,
      POP_ASSUM MP_TAC,
      POP_ASSUM MP_TAC,
      REAL_ARITH_TAC,
      ASM_REWRITE_TAC [REAL_MUL_LT],
      REPEAT STRIP_TAC,
      REPEAT_N 3 (POP_ASSUM MP_TAC),
      REAL_ARITH_TAC,
      CLAIM (← q r"x' < x''"),
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"z"),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"poly_diff p"), (← q r"x':real"), (← q r"x'':real")] (← REWRITE_RULE [real_gt] POLY_IVT_NEG)),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      CLAIM (← q r"x < x''' /\  x''' < y"),
      STRIP_TAC,
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"x'"),
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"x''"),
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC []
    ])

  let neg_neg_neq_thm2 ← prove_by_refinement (
    (← q r"!x y p. x < y ==> poly p x < &0 ==> poly p y < &0 ==>
            (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
            (!z. x < z /\ z < y ==> poly p z < &0)"),
  [
    REPEAT_N 7 STRIP_TAC,
    MATCH_MP_TAC neg_neg_neq_thm,
    ASM_MESON_TAC []
  ])

  let pos_pos_neq_thm ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"x < y <=> ~(y <= x)")
    prove_by_refinement (
      (← q r"!x y p. x < y /\ &0 < poly p x /\ &0 < poly p y /\
              (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
              (!z. x < z /\ z < y ==> &0 < poly p z)"),
    [
      REPEAT STRIP_TAC,
      REWRITE_TAC [r1],
      STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"x:real"), (← q r"z:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      CLAIM (← q r"poly p z - poly p x < &0"),
      LABEL_ALL_TAC,
      USE_THEN "Z-3" MP_TAC,
      USE_THEN "Z-8" MP_TAC,
      REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"(z - x) * poly (poly_diff p) x' < &0"),
      REPEAT_N 2 (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC,
      ASM_REWRITE_TAC [REAL_MUL_LT],
      REPEAT STRIP_TAC,
      CLAIM (← q r"&0 < z - x"),
      LABEL_ALL_TAC,
      USE_THEN "Z-8" MP_TAC THEN REAL_ARITH_TAC,
      LABEL_ALL_TAC,
      USE_THEN "Z-1" MP_TAC THEN REAL_ARITH_TAC,
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"z:real"), (← q r"y:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      CLAIM (← q r"&0 < poly p y - poly p z"),
      LABEL_ALL_TAC,
      USE_THEN "Z-13" MP_TAC,
      USE_THEN "Z-9" MP_TAC,
      REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"&0 < y - z"),
      LABEL_ALL_TAC,
      USE_THEN "Z-11" MP_TAC THEN REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"&0 < (y - z) * poly (poly_diff p) x''"),
      POP_ASSUM IGNORE,
      POP_ASSUM MP_TAC,
      POP_ASSUM MP_TAC,
      REAL_ARITH_TAC,
      ASM_REWRITE_TAC [REAL_MUL_GT],
      REPEAT STRIP_TAC,
      REPEAT_N 3 (POP_ASSUM MP_TAC),
      REAL_ARITH_TAC,
      CLAIM (← q r"x' < x''"),
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"z"),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"poly_diff p"), (← q r"x':real"), (← q r"x'':real")] (← REWRITE_RULE [real_gt] POLY_IVT_POS)),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      CLAIM (← q r"x < x''' /\  x''' < y"),
      STRIP_TAC,
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"x'"),
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"x''"),
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC []
    ])

  let pos_pos_neq_thm2 ← prove_by_refinement (
    (← q r"!x y p. x < y ==> poly p x > &0 ==> poly p y > &0 ==>
            (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
            (!z. x < z /\ z < y ==> poly p z > &0)"),
  [
    REWRITE_TAC [real_gt],
    REPEAT_N 7 STRIP_TAC,
    MATCH_MP_TAC pos_pos_neq_thm,
    ASM_MESON_TAC []
  ])

  let pos_neg_neq_thm ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"(x:real = y) <=> (y = x)")
    let r2 ← ARITH_RULE (← q r"x < y <=> ~(y < x \/ (x = y))")
    let r3 ← REAL_ARITH (← q r"(x:real = y) <=> (y = x)")
    let r4 ← ARITH_RULE (← q r"x < y <=> ~(y < x \/ (x = y))")
    prove_by_refinement (
      (← q r"!x y p. x < y /\ &0 < poly p x /\ poly p y < &0 /\
              (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
              ?X. x < X /\ X < y /\ (poly p X = &0) /\
                (!z. x < z /\ z < X ==> &0 < poly p z) /\
                (!z. X < z /\ z < y ==> poly p z < &0)"),
    [
      REPEAT STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"x:real"), (← q r"y:real")] POLY_IVT_NEG),
      REWRITE_TAC [real_gt],
      ASM_REWRITE_TAC [],
      DISCH_THEN (X_CHOOSE_TAC (← q r"X:real")),
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      EXISTS_TAC (← q r"X"),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      REPEAT STRIP_TAC,
      ONCE_REWRITE_TAC [r4],
      STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"x:real"), (← q r"z:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      DISCH_THEN (X_CHOOSE_TAC (← q r"N:real")),
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      CLAIM (← q r"poly p z - poly p x < &0"),
      LABEL_ALL_TAC,
      USE_THEN "Z-3" MP_TAC,
      USE_THEN "Z-11" MP_TAC,
      REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"(z - x) * poly (poly_diff p) N < &0"),
      REPEAT_N 2 (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC,
      ASM_REWRITE_TAC [REAL_MUL_LT],
      REPEAT STRIP_TAC,
      CLAIM (← q r"&0 < z - x"),
      LABEL_ALL_TAC,
      USE_THEN "Z-8" MP_TAC THEN REAL_ARITH_TAC,
      LABEL_ALL_TAC,
      USE_THEN "Z-1" MP_TAC THEN REAL_ARITH_TAC,
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"z:real"), (← q r"X:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      DISCH_THEN (X_CHOOSE_TAC (← q r"M:real")),
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      CLAIM (← q r"&0 < &0 - poly p z"),
      LABEL_ALL_TAC,
      USE_THEN "Z-9" MP_TAC,
      REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"&0 < X - z"),
      LABEL_ALL_TAC,
      USE_THEN "Z-11" MP_TAC THEN REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"&0 < (X - z) * poly (poly_diff p) M"),
      POP_ASSUM IGNORE,
      POP_ASSUM MP_TAC,
      POP_ASSUM MP_TAC,
      REAL_ARITH_TAC,
      REWRITE_TAC [REAL_MUL_GT],
      REPEAT STRIP_TAC,
      POP_ASSUM IGNORE,
      POP_ASSUM MP_TAC,
      POP_ASSUM MP_TAC,
      REAL_ARITH_TAC,
      CLAIM (← q r"N < M"),
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"z"),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"poly_diff p"), (← q r"N:real"), (← q r"M:real")] (← REWRITE_RULE [real_gt] POLY_IVT_POS)),
      ASM_REWRITE_TAC [],
      DISCH_THEN (X_CHOOSE_TAC (← q r"K:real")),
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      CLAIM (← q r"x < K /\  K < y"),
      STRIP_TAC,
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"N"),
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"M"),
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"X"),
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [],
      POP_ASSUM (ASSUME_TAC o GSYM),
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"z:real"), (← q r"X:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      REAL_SIMP_TAC,
      ONCE_REWRITE_TAC [r3],
      ASM_REWRITE_TAC [REAL_ENTIRE],
      DISCH_THEN (X_CHOOSE_TAC (← q r"M:real")),
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      LABEL_ALL_TAC,
      POP_ASSUM MP_TAC,
      USE_THEN "Z-4" MP_TAC THEN REAL_ARITH_TAC,
      CLAIM (← q r"x < M /\  M < y"),
      STRIP_TAC,
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"z"),
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"X"),
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [],
      REPEAT STRIP_TAC,
      ONCE_REWRITE_TAC [r2],
      STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"X:real"), (← q r"z:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      DISCH_THEN (X_CHOOSE_TAC (← q r"N:real")),
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      POP_ASSUM MP_TAC,
      REAL_SIMP_TAC,
      STRIP_TAC,
      CLAIM (← q r"&0 < (z - X) * poly (poly_diff p) N"),
      LABEL_ALL_TAC,
      USE_THEN "Z-3" MP_TAC,
      POP_ASSUM MP_TAC THEN REAL_ARITH_TAC,
      ASM_REWRITE_TAC [REAL_MUL_GT],
      REPEAT STRIP_TAC,
      CLAIM (← q r"&0 < z - X"),
      LABEL_ALL_TAC,
      USE_THEN "Z-7" MP_TAC THEN REAL_ARITH_TAC,
      LABEL_ALL_TAC,
      USE_THEN "Z-1" MP_TAC THEN REAL_ARITH_TAC,
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"z:real"), (← q r"y:real")] POLY_MVT),
      LABEL_ALL_TAC,
      USE_THEN "Z-6" (REWRITE_TAC o (list : thm → List thm)),
      DISCH_THEN (X_CHOOSE_TAC (← q r"M:real")),
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      CLAIM (← q r"poly p y - poly p z < &0"),
      LABEL_ALL_TAC,
      USE_THEN "Z-12" MP_TAC,
      USE_THEN "Z-5" MP_TAC,
      REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"&0 < y - z"),
      LABEL_ALL_TAC,
      USE_THEN "Z-6" MP_TAC THEN REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"(y - z) * poly (poly_diff p) M < &0"),
      POP_ASSUM IGNORE,
      POP_ASSUM MP_TAC,
      POP_ASSUM MP_TAC,
      REAL_ARITH_TAC,
      REWRITE_TAC [REAL_MUL_LT],
      REPEAT STRIP_TAC,
      POP_ASSUM IGNORE,
      POP_ASSUM MP_TAC,
      POP_ASSUM MP_TAC,
      REAL_ARITH_TAC,
      CLAIM (← q r"N < M"),
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"z"),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"poly_diff p"), (← q r"N:real"), (← q r"M:real")] (← REWRITE_RULE [real_gt] POLY_IVT_NEG)),
      ASM_REWRITE_TAC [],
      DISCH_THEN (X_CHOOSE_TAC (← q r"K:real")),
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      CLAIM (← q r"x < K /\  K < y"),
      STRIP_TAC,
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"N"),
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"X"),
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"M"),
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [],
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"X:real"), (← q r"z:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      REAL_SIMP_TAC,
      ONCE_REWRITE_TAC [r1],
      ASM_REWRITE_TAC [REAL_ENTIRE],
      DISCH_THEN (X_CHOOSE_TAC (← q r"M:real")),
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      LABEL_ALL_TAC,
      POP_ASSUM MP_TAC,
      USE_THEN "Z-5" MP_TAC THEN REAL_ARITH_TAC,
      CLAIM (← q r"x < M /\  M < y"),
      STRIP_TAC,
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"X"),
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"z"),
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC []
    ])

  let pos_neg_neq_thm2 ← prove_by_refinement (
    (← q r"!x y p. x < y ==> poly p x > &0 ==> poly p y < &0 ==>
            (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
            ?X. x < X /\ X < y /\
              (!z. (z = X) ==> (poly p z = &0)) /\
              (!z. x < z /\ z < X ==> poly p z > &0) /\
              (!z. X < z /\ z < y ==> poly p z < &0)"),
  [
    REWRITE_TAC [real_gt],
    REPEAT STRIP_TAC,
    MP_TAC (← ISPECL [(← q r"x:real"), (← q r"y:real"), (← q r"p:real list")] pos_neg_neq_thm),
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    EXISTS_TAC (← q r"X"),
    ASM_MESON_TAC []
  ])

  let neg_pos_neq_thm ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"(x:real = y) <=> (y = x)")
    let r2 ← ARITH_RULE (← q r"x < y <=> ~(y < x \/ (x = y))")
    let r3 ← REAL_ARITH (← q r"(x:real = y) <=> (y = x)")
    let r4 ← ARITH_RULE (← q r"x < y <=> ~(y < x \/ (x = y))")
    prove_by_refinement (
      (← q r"!x y p. x < y /\ poly p x < &0 /\ &0 < poly p y /\
              (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
              ?X. x < X /\ X < y /\ (poly p X = &0) /\
                (!z. x < z /\ z < X ==> poly p z < &0) /\
                (!z. X < z /\ z < y ==> &0 < poly p z)"),
    [
      REPEAT STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"x:real"), (← q r"y:real")] POLY_IVT_POS),
      REWRITE_TAC [real_gt],
      ASM_REWRITE_TAC [],
      DISCH_THEN (X_CHOOSE_TAC (← q r"X:real")),
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      EXISTS_TAC (← q r"X"),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      REPEAT STRIP_TAC,
      ONCE_REWRITE_TAC [r4],
      STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"x:real"), (← q r"z:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      DISCH_THEN (X_CHOOSE_TAC (← q r"N:real")),
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      CLAIM (← q r"&0 < poly p z - poly p x"),
      LABEL_ALL_TAC,
      USE_THEN "Z-3" MP_TAC,
      USE_THEN "Z-11" MP_TAC,
      REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"&0 < (z - x) * poly (poly_diff p) N"),
      REPEAT_N 2 (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC,
      ASM_REWRITE_TAC [REAL_MUL_GT],
      REPEAT STRIP_TAC,
      CLAIM (← q r"&0 < z - x"),
      LABEL_ALL_TAC,
      USE_THEN "Z-8" MP_TAC THEN REAL_ARITH_TAC,
      LABEL_ALL_TAC,
      USE_THEN "Z-1" MP_TAC THEN REAL_ARITH_TAC,
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"z:real"), (← q r"X:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      DISCH_THEN (X_CHOOSE_TAC (← q r"M:real")),
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      CLAIM (← q r"&0 - poly p z < &0"),
      LABEL_ALL_TAC,
      USE_THEN "Z-9" MP_TAC,
      REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"&0 < X - z"),
      LABEL_ALL_TAC,
      USE_THEN "Z-11" MP_TAC THEN REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"(X - z) * poly (poly_diff p) M < &0"),
      POP_ASSUM IGNORE,
      POP_ASSUM MP_TAC,
      POP_ASSUM MP_TAC,
      REAL_ARITH_TAC,
      REWRITE_TAC [REAL_MUL_LT],
      REPEAT STRIP_TAC,
      POP_ASSUM IGNORE,
      POP_ASSUM MP_TAC,
      POP_ASSUM MP_TAC,
      REAL_ARITH_TAC,
      CLAIM (← q r"N < M"),
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"z"),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"poly_diff p"), (← q r"N:real"), (← q r"M:real")] (← REWRITE_RULE [real_gt] POLY_IVT_NEG)),
      ASM_REWRITE_TAC [],
      DISCH_THEN (X_CHOOSE_TAC (← q r"K:real")),
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      CLAIM (← q r"x < K /\  K < y"),
      STRIP_TAC,
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"N"),
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"M"),
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"X"),
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [],
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"z:real"), (← q r"X:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      REAL_SIMP_TAC,
      ONCE_REWRITE_TAC [r3],
      ASM_REWRITE_TAC [REAL_ENTIRE],
      DISCH_THEN (X_CHOOSE_TAC (← q r"M:real")),
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      LABEL_ALL_TAC,
      POP_ASSUM MP_TAC,
      USE_THEN "Z-4" MP_TAC THEN REAL_ARITH_TAC,
      CLAIM (← q r"x < M /\  M < y"),
      STRIP_TAC,
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"z"),
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"X"),
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [],
      REPEAT STRIP_TAC,
      ONCE_REWRITE_TAC [r2],
      STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"X:real"), (← q r"z:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      DISCH_THEN (X_CHOOSE_TAC (← q r"N:real")),
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      POP_ASSUM MP_TAC,
      REAL_SIMP_TAC,
      STRIP_TAC,
      CLAIM (← q r"(z - X) * poly (poly_diff p) N < &0"),
      LABEL_ALL_TAC,
      USE_THEN "Z-3" MP_TAC,
      POP_ASSUM MP_TAC THEN REAL_ARITH_TAC,
      ASM_REWRITE_TAC [REAL_MUL_LT],
      REPEAT STRIP_TAC,
      CLAIM (← q r"&0 < z - X"),
      LABEL_ALL_TAC,
      USE_THEN "Z-7" MP_TAC THEN REAL_ARITH_TAC,
      LABEL_ALL_TAC,
      USE_THEN "Z-1" MP_TAC THEN REAL_ARITH_TAC,
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"z:real"), (← q r"y:real")] POLY_MVT),
      LABEL_ALL_TAC,
      USE_THEN "Z-6" (REWRITE_TAC o (list : thm → List thm)),
      DISCH_THEN (X_CHOOSE_TAC (← q r"M:real")),
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      CLAIM (← q r"&0 < poly p y - poly p z"),
      LABEL_ALL_TAC,
      USE_THEN "Z-12" MP_TAC,
      USE_THEN "Z-5" MP_TAC,
      REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"&0 < y - z"),
      LABEL_ALL_TAC,
      USE_THEN "Z-6" MP_TAC THEN REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"&0 < (y - z) * poly (poly_diff p) M"),
      POP_ASSUM IGNORE,
      POP_ASSUM MP_TAC,
      POP_ASSUM MP_TAC,
      REAL_ARITH_TAC,
      REWRITE_TAC [REAL_MUL_GT],
      REPEAT STRIP_TAC,
      POP_ASSUM IGNORE,
      POP_ASSUM MP_TAC,
      POP_ASSUM MP_TAC,
      REAL_ARITH_TAC,
      CLAIM (← q r"N < M"),
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"z"),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"poly_diff p"), (← q r"N:real"), (← q r"M:real")] (← REWRITE_RULE [real_gt] POLY_IVT_POS)),
      ASM_REWRITE_TAC [],
      DISCH_THEN (X_CHOOSE_TAC (← q r"K:real")),
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      CLAIM (← q r"x < K /\  K < y"),
      STRIP_TAC,
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"N"),
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"X"),
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"M"),
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [],
      POP_ASSUM (ASSUME_TAC o GSYM),
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"X:real"), (← q r"z:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      REAL_SIMP_TAC,
      ONCE_REWRITE_TAC [r1],
      ASM_REWRITE_TAC [REAL_ENTIRE],
      DISCH_THEN (X_CHOOSE_TAC (← q r"M:real")),
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      LABEL_ALL_TAC,
      POP_ASSUM MP_TAC,
      USE_THEN "Z-5" MP_TAC THEN REAL_ARITH_TAC,
      CLAIM (← q r"x < M /\  M < y"),
      STRIP_TAC,
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"X"),
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"z"),
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC []
    ])

  let neg_pos_neq_thm2 ← prove_by_refinement (
    (← q r"!x y p. x < y ==> poly p x < &0 ==> poly p y > &0 ==>
            (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
            ?X. x < X /\ X < y /\
              (!z. (z = X) ==> (poly p z = &0)) /\
              (!z. x < z /\ z < X ==> poly p z < &0) /\
              (!z. X < z /\ z < y ==> poly p z > &0)"),
  [
    REWRITE_TAC [real_gt],
    REPEAT STRIP_TAC,
    MP_TAC (← ISPECL [(← q r"x:real"), (← q r"y:real"), (← q r"p:real list")] neg_pos_neq_thm),
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    EXISTS_TAC (← q r"X"),
    ASM_MESON_TAC []
  ])

  let lt_nz_thm ← prove_by_refinement (
    (← q r"(!x. x1 < x /\ x < x2 ==> poly p x < &0) ==> (!x. x1 < x /\ x < x2 ==> ~(poly p x = &0))"),
  [
    MESON_TAC [REAL_LT_NZ]
  ])

  let gt_nz_thm ← prove_by_refinement (
    (← q r"(!x. x1 < x /\ x < x2 ==> poly p x > &0) ==> (!x. x1 < x /\ x < x2 ==> ~(poly p x = &0))"),
  [
    MESON_TAC [REAL_LT_NZ, real_gt]
  ])

  let eq_eq_false_thm ← prove_by_refinement (
    (← q r"!x y p. x < y ==> (poly p x = &0) ==> (poly p y = &0) ==>
       (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==> F"),
  [
    REPEAT_N 3 STRIP_TAC,
    DISCH_THEN (fun x => tactic_of do pure (MP_TAC (← MATCH_MP (← ISPEC (← q r"p:real list") POLY_MVT) x) THEN ASSUME_TAC x)),
    REPEAT STRIP_TAC,
    LABEL_ALL_TAC,
    CLAIM (← q r"poly p y - poly p x = &0"),
    REWRITE_TAC [real_sub],
    ASM_REWRITE_TAC [],
    REAL_ARITH_TAC,
    DISCH_THEN (REWRITE_ASSUMS o (list : thm → List thm)),
    CLAIM (← q r"&0 < y - x"),
    USE_THEN "Z-6" MP_TAC THEN REAL_ARITH_TAC,
    POP_ASSUM (MP_TAC o (ISPEC (← q r"x':real"))),
    RULE_ASSUM_TAC GSYM,
    POP_ASSUM IGNORE THEN POP_ASSUM IGNORE,
    ASM_REWRITE_TAC [],
    STRIP_TAC,
    STRIP_TAC,
    ASM_MESON_TAC [REAL_ENTIRE, REAL_LT_IMP_NZ]
  ])

  let neg_zero_neg_thm ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"x <= y <=> (x < y \/ (x = y))")
    let r2 ← ARITH_RULE (← q r"x < y <=> ~(y <= x)")
    prove_by_refinement (
      (← q r"!x y p. x < y ==> poly p x < &0 ==> (poly p y = &0) ==>
       (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
       (!z. x < z /\ z < y ==> poly p z < &0)"),
    [
      REPEAT STRIP_TAC,
      REWRITE_TAC [r2],
      REWRITE_TAC [r1],
      STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"x:real"), (← q r"z:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      CLAIM (← q r"poly p z - poly p x > &0"),
      LABEL_ALL_TAC,
      USE_THEN "Z-3" MP_TAC,
      USE_THEN "Z-8" MP_TAC,
      REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"(z - x) * poly (poly_diff p) x' > &0"),
      REPEAT_N 2 (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC,
      REWRITE_TAC [real_gt],
      ASM_REWRITE_TAC [REAL_MUL_GT],
      REPEAT STRIP_TAC,
      CLAIM (← q r"&0 < z - x"),
      LABEL_ALL_TAC,
      USE_THEN "Z-8" MP_TAC THEN REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"(z - x) * poly (poly_diff p) x' < &0"),
      REWRITE_TAC [REAL_MUL_LT],
      DISJ2_TAC,
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [REAL_LT_ANTISYM],
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"z:real"), (← q r"y:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      CLAIM (← q r"&0 - poly p z < &0"),
      LABEL_ALL_TAC,
      USE_THEN "Z-9" MP_TAC,
      REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"&0 < y - z"),
      LABEL_ALL_TAC,
      USE_THEN "Z-11" MP_TAC THEN REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"(y - z) * poly (poly_diff p) x'' < &0"),
      POP_ASSUM IGNORE,
      POP_ASSUM MP_TAC,
      POP_ASSUM MP_TAC,
      REAL_ARITH_TAC,
      ASM_REWRITE_TAC [REAL_MUL_LT],
      REPEAT STRIP_TAC,
      REPEAT_N 3 (POP_ASSUM MP_TAC),
      REAL_ARITH_TAC,
      CLAIM (← q r"x' < x''"),
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"z"),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"poly_diff p"), (← q r"x':real"), (← q r"x'':real")] (← REWRITE_RULE [real_gt] POLY_IVT_NEG)),
      REWRITE_ASSUMS [real_gt],
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      CLAIM (← q r"x < x''' /\  x''' < y"),
      STRIP_TAC,
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"x'"),
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"x''"),
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [],
      MP_TAC (← ISPECL [(← q r"z:real"), (← q r"y:real"), (← q r"p:real list")] eq_eq_false_thm),
      POP_ASSUM (ASSUME_TAC o GSYM),
      ASM_REWRITE_TAC [],
      REPEAT_N 2 STRIP_TAC,
      FIRST_ASSUM MATCH_MP_TAC,
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"z"),
      ASM_REWRITE_TAC []
    ])

  let pos_zero_pos_thm ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"x >= y <=> (x > y \/ (x = y))")
    let r2 ← ARITH_RULE (← q r"x > y <=> ~(y >= x)")
    prove_by_refinement (
      (← q r"!x y p. x < y ==> poly p x > &0 ==> (poly p y = &0) ==>
       (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
       (!z. x < z /\ z < y ==> poly p z > &0)"),
    [
      REPEAT STRIP_TAC,
      REWRITE_TAC [r2],
      REWRITE_TAC [r1],
      STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"x:real"), (← q r"z:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      CLAIM (← q r"poly p z - poly p x < &0"),
      LABEL_ALL_TAC,
      USE_THEN "Z-3" MP_TAC,
      USE_THEN "Z-8" MP_TAC,
      REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"(z - x) * poly (poly_diff p) x' < &0"),
      REPEAT_N 2 (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC,
      REWRITE_TAC [real_gt],
      ASM_REWRITE_TAC [REAL_MUL_LT],
      REPEAT STRIP_TAC,
      CLAIM (← q r"&0 < z - x"),
      LABEL_ALL_TAC,
      USE_THEN "Z-8" MP_TAC THEN REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"&0 < (z - x) * poly (poly_diff p) x'"),
      REWRITE_TAC [REAL_MUL_GT],
      DISJ2_TAC,
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [REAL_LT_ANTISYM],
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"z:real"), (← q r"y:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      CLAIM (← q r"&0 - poly p z > &0"),
      LABEL_ALL_TAC,
      USE_THEN "Z-9" MP_TAC,
      REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"&0 < y - z"),
      LABEL_ALL_TAC,
      USE_THEN "Z-11" MP_TAC THEN REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"(y - z) * poly (poly_diff p) x'' > &0"),
      POP_ASSUM IGNORE,
      POP_ASSUM MP_TAC,
      POP_ASSUM MP_TAC,
      REAL_ARITH_TAC,
      ASM_REWRITE_TAC [REAL_MUL_GT, REAL_MUL_LT, real_gt],
      REPEAT STRIP_TAC,
      REPEAT_N 3 (POP_ASSUM MP_TAC),
      REAL_ARITH_TAC,
      CLAIM (← q r"x' < x''"),
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"z"),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"poly_diff p"), (← q r"x':real"), (← q r"x'':real")] (← REWRITE_RULE [real_gt] POLY_IVT_POS)),
      REWRITE_ASSUMS [real_gt],
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      CLAIM (← q r"x < x''' /\  x''' < y"),
      STRIP_TAC,
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"x'"),
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"x''"),
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [],
      MP_TAC (← ISPECL [(← q r"z:real"), (← q r"y:real"), (← q r"p:real list")] eq_eq_false_thm),
      POP_ASSUM (ASSUME_TAC o GSYM),
      ASM_REWRITE_TAC [],
      REPEAT_N 2 STRIP_TAC,
      FIRST_ASSUM MATCH_MP_TAC,
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"z"),
      ASM_REWRITE_TAC []
    ])

  let zero_neg_neg_thm ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"x <= y <=> (x < y \/ (x = y))")
    let r2 ← ARITH_RULE (← q r"x < y <=> ~(y <= x)")
    prove_by_refinement (
      (← q r"!x y p. x < y ==> (poly p x = &0) ==> (poly p y < &0) ==>
       (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
       (!z. x < z /\ z < y ==> poly p z < &0)"),
    [
      REPEAT STRIP_TAC,
      REWRITE_TAC [r2],
      REWRITE_TAC [r1],
      STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"x:real"), (← q r"z:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      CLAIM (← q r"poly p z - &0 > &0"),
      LABEL_ALL_TAC,
      USE_THEN "Z-3" MP_TAC,
      USE_THEN "Z-8" MP_TAC,
      REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"(z - x) * poly (poly_diff p) x' > &0"),
      REPEAT_N 2 (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC,
      REWRITE_TAC [real_gt],
      ASM_REWRITE_TAC [REAL_MUL_LT, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      CLAIM (← q r"&0 < z - x"),
      LABEL_ALL_TAC,
      USE_THEN "Z-8" MP_TAC THEN REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"&0 > (z - x) * poly (poly_diff p) x'"),
      REWRITE_TAC [REAL_MUL_GT, real_gt, REAL_MUL_LT],
      DISJ2_TAC,
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [REAL_LT_ANTISYM],
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"z:real"), (← q r"y:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      CLAIM (← q r"poly p y - poly p z < &0"),
      LABEL_ALL_TAC,
      USE_THEN "Z-13" MP_TAC,
      USE_THEN "Z-9" MP_TAC,
      REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"&0 < y - z"),
      LABEL_ALL_TAC,
      USE_THEN "Z-11" MP_TAC THEN REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"(y - z) * poly (poly_diff p) x'' < &0"),
      POP_ASSUM IGNORE,
      POP_ASSUM MP_TAC,
      POP_ASSUM MP_TAC,
      REAL_ARITH_TAC,
      ASM_REWRITE_TAC [REAL_MUL_GT, REAL_MUL_LT, real_gt],
      REPEAT STRIP_TAC,
      REPEAT_N 3 (POP_ASSUM MP_TAC),
      REAL_ARITH_TAC,
      CLAIM (← q r"x' < x''"),
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"z"),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"poly_diff p"), (← q r"x':real"), (← q r"x'':real")] (← REWRITE_RULE [real_gt] POLY_IVT_NEG)),
      REWRITE_ASSUMS [real_gt],
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      CLAIM (← q r"x < x''' /\  x''' < y"),
      STRIP_TAC,
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"x'"),
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"x''"),
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [],
      MP_TAC (← ISPECL [(← q r"x:real"), (← q r"z:real"), (← q r"p:real list")] eq_eq_false_thm),
      POP_ASSUM (ASSUME_TAC o GSYM),
      ASM_REWRITE_TAC [],
      REPEAT_N 2 STRIP_TAC,
      FIRST_ASSUM MATCH_MP_TAC,
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"z"),
      ASM_REWRITE_TAC []
    ])

  let zero_pos_pos_thm ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"x >= y <=> (x > y \/ (x = y))")
    let r2 ← ARITH_RULE (← q r"x > y <=> ~(y >= x)")
    prove_by_refinement (
      (← q r"!x y p. x < y ==> (poly p x = &0) ==> (poly p y > &0) ==>
       (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
       (!z. x < z /\ z < y ==> poly p z > &0)"),
    [
      REPEAT STRIP_TAC,
      REWRITE_TAC [r2],
      REWRITE_TAC [r1],
      STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"z:real"), (← q r"y:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      CLAIM (← q r"poly p y - poly p z > &0"),
      LABEL_ALL_TAC,
      USE_THEN "Z-7" MP_TAC,
      USE_THEN "Z-3" MP_TAC,
      REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"(y - z) * poly (poly_diff p) x' > &0"),
      REPEAT_N 2 (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC,
      REWRITE_TAC [real_gt],
      ASM_REWRITE_TAC [REAL_MUL_LT, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      LABEL_ALL_TAC,
      USE_THEN "Z-1" MP_TAC,
      USE_THEN "Z-7" MP_TAC,
      REAL_ARITH_TAC,
      MP_TAC (← ISPECL [(← q r"p:real list"), (← q r"x:real"), (← q r"z:real")] POLY_MVT),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      CLAIM (← q r"poly p z - &0 < &0"),
      LABEL_ALL_TAC,
      USE_THEN "Z-9" MP_TAC,
      REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"&0 < z - x"),
      LABEL_ALL_TAC,
      USE_THEN "Z-12" MP_TAC THEN REAL_ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"(z - x) * poly (poly_diff p) x'' < &0"),
      POP_ASSUM IGNORE,
      POP_ASSUM MP_TAC,
      POP_ASSUM MP_TAC,
      REAL_ARITH_TAC,
      ASM_REWRITE_TAC [REAL_MUL_GT, REAL_MUL_LT, real_gt],
      REPEAT STRIP_TAC,
      REPEAT_N 3 (POP_ASSUM MP_TAC),
      REAL_ARITH_TAC,
      CLAIM (← q r"x'' < x'"),
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"z"),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"poly_diff p"), (← q r"x'':real"), (← q r"x':real")] (← REWRITE_RULE [real_gt] POLY_IVT_POS)),
      REWRITE_ASSUMS [real_gt],
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      CLAIM (← q r"x < x''' /\  x''' < y"),
      STRIP_TAC,
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"x''"),
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"x'"),
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [],
      MP_TAC (← ISPECL [(← q r"x:real"), (← q r"z:real"), (← q r"p:real list")] eq_eq_false_thm),
      POP_ASSUM (ASSUME_TAC o GSYM),
      ASM_REWRITE_TAC [],
      REPEAT_N 2 STRIP_TAC,
      FIRST_ASSUM MATCH_MP_TAC,
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC REAL_LT_TRANS,
      EXISTS_TAC (← q r"z"),
      ASM_REWRITE_TAC []
    ])

  -- @@RETURN BEGIN
  return { inferisign_lem00, neg_neg_neq_thm, neg_neg_neq_thm2, pos_pos_neq_thm,
           pos_pos_neq_thm2, pos_neg_neq_thm, pos_neg_neq_thm2, neg_pos_neq_thm,
           neg_pos_neq_thm2, lt_nz_thm, gt_nz_thm, eq_eq_false_thm, neg_zero_neg_thm,
           pos_zero_pos_thm, zero_neg_neg_thm, zero_pos_pos_thm }
  -- @@RETURN END

end HolRQE.InferisignThms
