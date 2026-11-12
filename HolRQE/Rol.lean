/- ========================================================================= -/
/- Rqe: real ordered lists and the rules that insert into and remove from  -/
/- ========================================================================= -/
/- File: HolRQE/Rol.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/rol.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml, Rqe/num_calc_simp.ml, Rqe/asym.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.Rol fills them).

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

namespace HolRQE.Rol

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (AND_IMP_THM APPEND COND_CLAUSES DE_MORGAN_THM EL HD HD_APPEND LAST LAST_CONS
   LAST_CONS_CONS LAST_SING NOT_CONS_NIL NOT_NIL REAL_DENSE REAL_GT_EXISTS
   REAL_LT_EXISTS REAL_LT_TRANS TL list_RECURSION real_ge real_gt : thm)
  deriving Inhabited

/-- What rol.ml uses from Session besides theorems. -/
structure RolDeps where
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

def interleave {α : Type} : List α → List α → List α
  | [], l2 => l2
  | h :: t, l2 =>
    match l2 with
    | [] => h :: t
    | h1 :: t1 => h :: h1 :: interleave t t1

/-- ROL_REMOVE's local `insert`, given its `connect_thm` (and rqe_real.ml's
    `rlt`). -/
def ROL_REMOVE.insert (rlt : term) (connect_thm xz_thm : thm) :
    List thm → Except String (List thm)
  | [] => .ok [connect_thm]
  | h :: t => do
    let (l, _r) ← dest_binop rlt (concl h)
    let (_l1, r1) ← dest_binop rlt (concl xz_thm)
    if r1 == l then pure (xz_thm :: h :: t)
    else pure (h :: (← ROL_REMOVE.insert rlt connect_thm xz_thm t))



/- ---------------------------------------------------------------------- -/
/-  Real Ordered Lists (rol.ml 1-606)                                     -/
/- ---------------------------------------------------------------------- -/

structure RolFns where
  -- @@FIELDS
  real_ordered_list : thm
  ROL_EMPTY : thm
  ROL_SING : thm
  ROL_TAIL : thm
  EL_CONS : thm
  NOT_ROL : thm
  ROL_CONS : thm
  ROL_CONS_CONS : thm
  ROL_APPEND : thm
  ROL_CONS_CONS_LT : thm
  ROL_INSERT_THM : thm
  ROL_INSERT_FRONT_THM : thm
  ROL_CONS_CONS_DELETE : thm
  LAST_CONS_LT : thm
  ROL_INSERT_BACK_THM : thm
  CHOP_REAL_LIST : Int → term → ExceptT String IO thm
  ROL_CHOP_LT : Int → thm → ExceptT String IO thm
  t1 : thm
  ROL_CHOP_LIST : Int → thm → ExceptT String IO (thm × thm × thm)
  lem1 : thm
  ROL_INSERT_MIDDLE : thm → thm → ExceptT String IO thm
  ROL_INSERT_FRONT : thm → thm → ExceptT String IO thm
  ROL_INSERT_BACK : thm → thm → ExceptT String IO thm
  ROL_INSERT : thm → thm → ExceptT String IO thm
  rol_thms : thm → ExceptT String IO (List thm)
  lem : thm
  lem0 : thm
  rol_nonempty_thms : thm → ExceptT String IO (List thm)
  lem2 : thm
  mk_rol : List thm → ExceptT String IO thm
  real_nil : term
  ROL_NIL : thm
  ROL_REMOVE : term → thm → ExceptT String IO thm
  ROL_COVERS : thm → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupRolFns [HolBase] (D : RolDeps) :
    ExceptT String IO RolFns := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, CASES_ON, CLAIM, EXISTS_TAC, LIST_INDUCT_TAC, MESON_TAC,
        REAL_ARITH_TAC, TAUT, mk_rlist, new_recursive_definition, prove_by_refinement,
        rappend, real_ty, rlast, rlt, .. } := D
  let { AND_IMP_THM, APPEND, COND_CLAUSES, DE_MORGAN_THM, EL, HD, HD_APPEND, LAST,
        LAST_CONS, LAST_CONS_CONS, LAST_SING, NOT_CONS_NIL, NOT_NIL, REAL_DENSE,
        REAL_GT_EXISTS, REAL_LT_EXISTS, REAL_LT_TRANS, TL, list_RECURSION, real_ge,
        real_gt, .. } := D.core1
  -- @@SCOPE END

  let real_ordered_list ← new_recursive_definition list_RECURSION
    r"(real_ordered_list [] <=> T) /\
     (real_ordered_list (CONS h t) <=>
        real_ordered_list t /\
        ((t = []) \/ (h < HD t)))"

  let ROL_EMPTY ← EQT_ELIM (← CONJUNCT1 real_ordered_list)

  let ROL_SING ← prove_by_refinement (
    (← q r"!x. real_ordered_list [x]"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [real_ordered_list]
  ])
  /- }}} -/

  let ROL_TAIL ← prove
    r"!l. ~(l = []) /\ real_ordered_list l ==> real_ordered_list (TL l)"
  /- {{{ Proof -/
    (LIST_INDUCT_TAC THEN
    MESON_TAC [real_ordered_list, TL])
  /- }}} -/

  let EL_CONS ← prove_by_refinement (
    (← q r"!l h n. EL n t = EL (SUC n) (CONS h t)"),
  /- {{{ Proof -/
  [
    MESON_TAC [TL, EL]
  ])
  /- }}} -/

  let NOT_ROL ← prove_by_refinement (
    (← q r"!l. ~(real_ordered_list l) ==> ?n. EL n l >= EL (SUC n) l"),
  /- {{{ Proof -/

  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [real_ordered_list],
    REWRITE_TAC [real_ordered_list, DE_MORGAN_THM],
    STRIP_TAC,
    POP_ASSUM (fun x => POP_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x)))),
    STRIP_TAC,
    EXISTS_TAC (← q r"SUC n"),
    ASM_MESON_TAC [EL_CONS],
    EXISTS_TAC (← q r"0"),
    REWRITE_TAC [EL, HD, TL, real_ge],
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC
  ])

  /- }}} -/

  let ROL_CONS ← prove_by_refinement (
    (← q r"!h t. real_ordered_list (CONS h t) ==> real_ordered_list t"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [real_ordered_list],
    REPEAT STRIP_TAC
  ])
  /- }}} -/

  let ROL_CONS_CONS ← prove_by_refinement (
    (← q r"!h t. real_ordered_list (CONS h1 (CONS h2 t)) <=>
       real_ordered_list (CONS h2 t) /\ h1 < h2"),
  /- {{{ Proof -/

  [
    REPEAT GEN_TAC,
    EQ_TAC,
    REWRITE_TAC [real_ordered_list],
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [NOT_CONS_NIL, HD],
    ASM_MESON_TAC [NOT_CONS_NIL],
    ASM_MESON_TAC [HD],
    ASM_MESON_TAC [NOT_CONS_NIL],
    ASM_MESON_TAC [HD],
    REWRITE_TAC [real_ordered_list],
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [NOT_CONS_NIL, HD]
  ])

  /- }}} -/

  let ROL_APPEND ← prove_by_refinement (
    (← q r"!l1 l2. real_ordered_list (APPEND l1 l2) ==>
      real_ordered_list l1 /\ real_ordered_list l2"),
  /- {{{ Proof -/

  [
    LIST_INDUCT_TAC,
    MESON_TAC [APPEND, real_ordered_list],
    GEN_TAC,
    REWRITE_TAC [APPEND],
    STRIP_TAC,
    CLAIM (← q r"real_ordered_list (APPEND t l2)"),
    ASM_MESON_TAC [ROL_CONS],
    STRIP_TAC,
    CLAIM (← q r"real_ordered_list t /\ real_ordered_list l2"),
    ASM_MESON_TAC [],
    STRIP_TAC,
    ASM_REWRITE_TAC [],
    CASES_ON (← q r"t = []"),
    ASM_MESON_TAC [real_ordered_list],
    POP_ASSUM MP_TAC,
    REWRITE_TAC [NOT_NIL],
    STRIP_TAC,
    ASM_REWRITE_TAC [ROL_CONS_CONS],
    CONJ_TAC,
    ASM_MESON_TAC [],
    LABEL_ALL_TAC,
    USE_THEN "Z-4" MP_TAC,
    POP_ASSUM SUBST1_TAC,
    REWRITE_TAC [APPEND],
    ASM_MESON_TAC [ROL_CONS_CONS]
  ])

  /- }}} -/

  let ROL_CONS_CONS_LT ← prove_by_refinement (
    (← q r"!h1 h2 t. real_ordered_list (CONS h1 (CONS h2 t)) ==> h1 < h2"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [real_ordered_list],
    REPEAT STRIP_TAC THEN
    ASM_MESON_TAC [NOT_CONS_NIL, HD]
  ])
  /- }}} -/

  let ROL_INSERT_THM ← do
    let t1 ← TAUT (← q r"(p ==> q ==> r) <=> (p /\ q ==> r)")
    prove_by_refinement (
    (← q r"!x l1 l2.
      real_ordered_list l1 /\ real_ordered_list l2 /\
      ~(l1 = []) /\ ~(l2 = []) /\ LAST l1 < x /\ x < HD l2 ==>
        real_ordered_list (APPEND l1 (CONS x l2))"),
  /- {{{ Proof -/

  [
    GEN_TAC,
    LIST_INDUCT_TAC,
    REWRITE_TAC [APPEND],
    CASES_ON (← q r"t = []"),
    ASM_REWRITE_TAC [APPEND, LAST_SING, NOT_CONS_NIL],
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [ROL_CONS_CONS, real_ordered_list],
    POP_ASSUM MP_TAC,
    REWRITE_TAC [NOT_NIL],
    STRIP_TAC,
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    CLAIM (← q r"real_ordered_list (APPEND t (CONS x l2))"),
    REWRITE_ASSUMS [t1],
    FIRST_ASSUM MATCH_MP_TAC,
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [ROL_CONS],
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    ASM_MESON_TAC [NOT_CONS_NIL],
    ASM_MESON_TAC [NOT_CONS_NIL],
    ASM_MESON_TAC [LAST_CONS, NOT_CONS_NIL],
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    ASM_REWRITE_TAC [],
    LABEL_ALL_TAC,
    USE_THEN "Z-3" (SUBST1_TAC o GSYM),
    REWRITE_TAC [APPEND],
    STRIP_TAC,
    REWRITE_TAC [ROL_CONS_CONS],
    STRIP_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    ASM_MESON_TAC [ROL_CONS_CONS]
  ])

  /- }}} -/

  let ROL_INSERT_FRONT_THM ← prove_by_refinement (
    (← q r"!x l. real_ordered_list l /\ ~(l = []) /\ x < HD l ==>
      real_ordered_list (CONS x l)"),
  /- {{{ Proof -/

  [
    REWRITE_TAC [NOT_NIL, AND_IMP_THM],
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [],
    ASM_MESON_TAC [ROL_CONS_CONS, HD]
  ])

  /- }}} -/

  let ROL_CONS_CONS_DELETE ← prove_by_refinement (
    (← q r"!h1 h2 t. real_ordered_list (CONS h1 (CONS h2 t)) ==>
       real_ordered_list (CONS h1 t)"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [real_ordered_list],
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
    ASM_MESON_TAC [NOT_CONS_NIL],
    REWRITE_ASSUMS [HD],
    ASM_MESON_TAC [REAL_LT_TRANS]
  ])
  /- }}} -/

  let LAST_CONS_LT ← prove_by_refinement (
    (← q r"!x t h. real_ordered_list (CONS h t) /\ LAST (CONS h t) < x ==> h < x"),
  /- {{{ Proof -/

  [
    GEN_TAC,
    LIST_INDUCT_TAC,
    REWRITE_TAC [LAST],
    REPEAT STRIP_TAC,
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    CONJ_TAC,
    ASM_MESON_TAC [ROL_CONS_CONS_DELETE],
    CASES_ON (← q r"t = []"),
    ASM_REWRITE_TAC [LAST],
    ASM_MESON_TAC [LAST, ROL_CONS_CONS, REAL_LT_TRANS],
    ASM_MESON_TAC [LAST_CONS, ROL_CONS_CONS_DELETE, LAST_CONS_CONS]
  ])

  /- }}} -/

  let ROL_INSERT_BACK_THM ← prove_by_refinement (
    (← q r"!x l. real_ordered_list l /\ ~(l = []) /\ LAST l < x ==>
      real_ordered_list (APPEND l [x])"),
  /- {{{ Proof -/

  [
    STRIP_TAC,
    LIST_INDUCT_TAC,
    REWRITE_TAC [APPEND, ROL_SING],
    LABEL_ALL_TAC,
    STRIP_TAC,
    CASES_ON (← q r"t = []"),
    ASM_REWRITE_TAC [APPEND, ROL_CONS_CONS, ROL_SING],
    ASM_MESON_TAC [LAST, COND_CLAUSES],
    PROVE_ASSUM_ANTECEDENT_TAC 0,
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [ROL_CONS],
    ASM_MESON_TAC [],
    ASM_MESON_TAC [LAST_CONS],
    REWRITE_TAC [APPEND],
    REWRITE_TAC [real_ordered_list],
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    DISJ2_TAC,
    REWRITE_ASSUMS [NOT_NIL],
    LABEL_ALL_TAC,
    USE_IASSUM 2 MP_TAC,
    STRIP_TAC,
    ASM_REWRITE_TAC [HD_APPEND],
    ASM_MESON_TAC [ROL_CONS_CONS]
  ])

  /- }}} -/

  /-
    CHOP_REAL_LIST 1 `[&1; &2; &3]` --> |- [&1; &2; &3] = APPEND [&1; &2] [&3]
    let n,l = 1,`[&1; &2; &3]`
  -/
  let CHOP_REAL_LIST : Int → term → ExceptT String IO thm ← pure (fun n l => do
    let l' ← liftExcept (dest_list l)
    let (l1', l2') ← liftExcept (chop_list n.toNat l')
    -- the pair right to left
    let l2 ← ExceptT.mk (HolMath.Lists.mk_list l2' real_ty)
    let l1 ← ExceptT.mk (HolMath.Lists.mk_list l1' real_ty)
    let tm ← liftExcept (do (← mk_binop rappend l1) l2)
    GSYM (← ExceptT.mk (REWRITE_CONV [APPEND] tm)))


  /-
    ROL_CHOP_LT 2
    let n = 1
  -/
  let ROL_CHOP_LT : Int → thm → ExceptT String IO thm ← pure (fun n thm => do
    -- `funpow (n - 1) (MATCH_MP ROL_CONS) thm`
    let thm' ← (List.range (n - 1).toNat).foldlM (fun th _ => MATCH_MP ROL_CONS th) thm
    CONJUNCT2 (← PURE_REWRITE_RULE [ROL_CONS_CONS] thm'))

  let t1 ← prove_by_refinement (
    (← q r"real_ordered_list [&1; &2; &3; &4]"),
  [
    REWRITE_TAC [HD, real_ordered_list],
    REAL_ARITH_TAC
  ])

  /-
  ROL_CHOP_LIST 2 |- real_ordered_list [&1; &2; &3; &4] -->
                     |- real_ordered_list [&1; &2; &3],
                     |- real_ordered_list [&4],
                     |- &3 < &4
  let thm = ASSUME `real_ordered_list [&1; &2; &3; &4]`
  let n = 2
  ROL_CHOP_LIST 2 thm
  -/
  let ROL_CHOP_LIST : Int → thm → ExceptT String IO (thm × thm × thm) ← pure (fun n thm => do
    let (_, l) ← liftExcept (dest_comb (concl thm))
    let lthm ← CHOP_REAL_LIST n l
    let thm' ← REWRITE_RULE [lthm] thm
    let thm'' ← MATCH_MP ROL_APPEND thm'
    let (lthm, rthm) ← match CONJUNCTS thm'' with
      | [lthm, rthm] => pure (lthm, rthm)
      | _ => throw "Match_failure"
    let lt_thm ← ROL_CHOP_LT n thm
    pure (lthm, rthm, lt_thm))

  /-
  rol_insert (|- x1 < x4 /\ x4 < x2)
             (|- real_ordered_list [x1; x2; x3]) -->
    (|- real_ordered_list [x1; x4; x2; x3]);

  rol_insert (|- &2 < &5 /\ &5 < &6) (|- real_ordered_list [&1; &2; &6]) -->
    (|- real_ordered_list [&1; &2; &5; &6]);

  rol_insert (|- x4 < x1)
             (|- real_ordered_list [x1; x2; x3]) -->
    (|- real_ordered_list [x4; x1; x2; x3]);

  rol_insert (|- x1 < x4)
             (|- real_ordered_list [x1; x2; x3]) -->
    (|- real_ordered_list [x1; x2; x3; x4]);
  -/

  -- rol.ml binds `lem1` three times (this one, then 466 and 502); each
  -- rule below uses the one in scope where it is defined, as in OCaml
  let lem1 ← prove
    r"!e x l. e < x /\ (LAST l = e) ==> LAST l < x"
    (MESON_TAC [])

  let ROL_INSERT_MIDDLE : thm → thm → ExceptT String IO thm ← pure (fun place_thm rol_thm => do
    let (pl1, pl2) ← match CONJUNCTS place_thm with
      | [pl1, pl2] => pure (pl1, pl2)
      | _ => throw "Match_failure"
    let list := (← liftExcept (dest_comb (concl rol_thm))).2
    let (_new_x, slot) ← do
      let (ltl, ltr) ← liftExcept (dest_conj (concl place_thm))
      let (x1, x4) ← liftExcept (dest_binop rlt ltl)
      let (_, _x2) ← liftExcept (dest_binop rlt ltr)
      let n := ((← liftExcept (index x1 (← liftExcept (dest_list list)))) : Int) + 1
      pure (x4, n)
    let (lthm, rthm, _lt_thm) ← ROL_CHOP_LIST slot rol_thm
    let llist := (← liftExcept (dest_comb (concl lthm))).2
    let hllist ← liftExcept (hd (← liftExcept (dest_list llist)))
    let tllist ← ExceptT.mk (mk_rlist (← liftExcept (tl (← liftExcept (dest_list llist)))))
    let rlist := (← liftExcept (dest_comb (concl rthm))).2
    let hrlist ← liftExcept (hd (← liftExcept (dest_list rlist)))
    let trlist ← ExceptT.mk (mk_rlist (← liftExcept (tl (← liftExcept (dest_list rlist)))))
    let gthm ← REWRITE_RULE [AND_IMP_THM] ROL_INSERT_THM
    let a1 := lthm
    let a2 := rthm
    let a3 ← ISPECL [hllist, tllist] NOT_CONS_NIL
    let a4 ← ISPECL [hrlist, trlist] NOT_CONS_NIL
    let (l, r) ← liftExcept (dest_binop rlt (concl pl1))
    let a5_aux ← do
      -- `prove(mk_eq (mk_comb(rlast,llist),l), REWRITE_TAC[..])`, right to left
      let tac := REWRITE_TAC [LAST, COND_CLAUSES, NOT_CONS_NIL]
      let mkEq ← ExceptT.mk _root_.mk_eq
      let tm ← liftExcept (mkEq (← liftExcept (mk_comb rlast llist), l))
      ExceptT.mk (HolCore.Tactics.prove HolBase.B tm tac)
    let a5 ← MATCH_MPL [← ISPECL [l, r, llist] (← REWRITE_RULE [AND_IMP_THM] lem1), pl1, a5_aux]
    let a6_aux ← ISPECL [trlist, hrlist] (← GEN_ALL HD)
    let a6 ← CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [← GSYM a6_aux])) pl2
    let thm ← MATCH_MPL [gthm, a1, a2, a3, a4, a5, a6]
    REWRITE_RULE [APPEND] thm)

  /-
  ROL_INSERT_MIDDLE (ASSUME `x1 < x4 /\ x4 < x2`)
                        (ASSUME `real_ordered_list [x1; x2; x3]`);;

  ROL_INSERT_MIDDLE (ASSUME `x1 < x6 /\ x6 < x2`)
                        (ASSUME `real_ordered_list [x1; x2; x3; x4; x5]`);;

  ROL_INSERT_MIDDLE (ASSUME `x2 < x6 /\ x6 < x3`)
                        (ASSUME `real_ordered_list [x1; x2; x3; x4; x5]`);;

  ROL_INSERT_MIDDLE (ASSUME `x4 < x6 /\ x6 < x5`)
                        (ASSUME `real_ordered_list [x1; x2; x3; x4; x5]`);;

  ROL_INSERT_MIDDLE (ASSUME `x2 < x4 /\ x4 < x3`)
                        (ASSUME `real_ordered_list [x1; x2; x3]`);;

  -/


  let ROL_INSERT_FRONT : thm → thm → ExceptT String IO thm ← pure (fun place_thm rol_thm => do
    let (_, rlist) ← liftExcept (dest_comb (concl rol_thm))
    -- the pair right to left
    let t ← ExceptT.mk (mk_rlist (← liftExcept (tl (← liftExcept (dest_list rlist)))))
    let h ← liftExcept (hd (← liftExcept (dest_list rlist)))
    let imp_thm ← ISPECL [h, t] (← GSYM ROL_CONS_CONS)
    let imp_thm' ← REWRITE_RULE [AND_IMP_THM] (← EQ_IMP_RULE imp_thm).1
    MATCH_MPL [imp_thm', rol_thm, place_thm])

  /-
  ROL_INSERT_FRONT (ASSUME `x4 < x1`)
                       (ASSUME `real_ordered_list [x1; x2; x3]`);;
  ROL_INSERT_FRONT (ASSUME `x4 < x1`)
                       (ASSUME `real_ordered_list [x1]`);;
  -/

  let ROL_INSERT_BACK : thm → thm → ExceptT String IO thm ← pure (fun place_thm rol_thm => do
    let (_, rlist) ← liftExcept (dest_comb (concl rol_thm))
    let rlist' ← liftExcept (dest_list rlist)
    -- the pair right to left
    let t ← ExceptT.mk (mk_rlist (← liftExcept (tl rlist')))
    let h ← liftExcept (hd rlist')
    let lst ← liftExcept (last rlist')
    let (_b, x) ← liftExcept (dest_binop rlt (concl place_thm))
    let imp_thm ← REWRITE_RULE [AND_IMP_THM]
                    (← ISPECL [x, rlist] ROL_INSERT_BACK_THM)
    let a1 := rol_thm
    let a2 ← ISPECL [h, t] NOT_CONS_NIL
    let a3_aux ← do
      let tac := REWRITE_TAC [LAST, COND_CLAUSES, NOT_CONS_NIL]
      let mkEq ← ExceptT.mk _root_.mk_eq
      let tm ← liftExcept (mkEq (← liftExcept (mk_comb rlast rlist), lst))
      ExceptT.mk (HolCore.Tactics.prove HolBase.B tm tac)
    let a3 ← MATCH_MPL [← ISPECL [lst, x, rlist]
                          (← REWRITE_RULE [AND_IMP_THM] lem1), place_thm, a3_aux]
    REWRITE_RULE [APPEND] (← MATCH_MPL [imp_thm, a1, a2, a3]))

  /-
  ROL_INSERT_BACK (ASSUME `x3 < x4`)
                  (ASSUME `real_ordered_list [x1; x2; x3]`);;
  -/

  let ROL_INSERT : thm → thm → ExceptT String IO thm ← pure (fun place_thm rol_thm => do
    let place_thm' ← REWRITE_RULE [real_gt] place_thm
    if is_conj (concl place_thm') then ROL_INSERT_MIDDLE place_thm' rol_thm
    else
      let (_, rlist) ← liftExcept (dest_comb (concl rol_thm))
      let rlist' ← liftExcept (dest_list rlist)
      let h ← liftExcept (hd rlist')
      let (_l, r) ← liftExcept (dest_binop rlt (concl place_thm'))
      if r == h then ROL_INSERT_FRONT place_thm' rol_thm
      else ROL_INSERT_BACK place_thm' rol_thm)

  /-
  let k00 = ROL_INSERT (ASSUME `x1 < x4 /\ x4 < x2`)
             (ASSUME `real_ordered_list [x1; x2; x3]`);;

  rol_thms k00

  PARTITION_LINE_CONV `[x1; x4; x2; x3:real]`

  ROL_INSERT (ASSUME `x4 < x1`)
             (ASSUME `real_ordered_list [x1]`);;

  ROL_INSERT (ASSUME `x3 < x4`)
             (ASSUME `real_ordered_list [x1; x2; x3]`);;

  -/


  /-
    rol_thms |- real_ordered_list [x;y;z]

    --->

    |- x < y; |- y < z

  -/
  let rol_thms : thm → ExceptT String IO (List thm) ← pure (fun rol_thm => do
    let thm ← REWRITE_RULE [real_ordered_list, NOT_CONS_NIL, HD] rol_thm
    pure (HolLight.rev (CONJUNCTS thm)))
  /-
  let rol_thm = ASSUME `real_ordered_list [x;y;z]`
  rol_thms rol_thm
  -/

  -- rol.ml binds `lem` twice (here and 580), `lem0` twice (here and 496)
  -- and `lem2` twice (510 and 586)
  let lem ← prove r"!x. ?y. y = x" (MESON_TAC [])

  let lem0 ← prove r"?x:real. T" (MESON_TAC [])

  let lem1 ← prove_by_refinement (
    (← q r"!x. (?y. y < x) /\ (?y. y = x) /\ (?y. x < y)"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    EXISTS_TAC (← q r"x - &1"),
    REAL_ARITH_TAC,
    MESON_TAC [],
    EXISTS_TAC (← q r"x + &1"),
    REAL_ARITH_TAC
  ])
  /- }}} -/

  let rol_nonempty_thms : thm → ExceptT String IO (List thm) ← pure (fun rol_thm => do
    let pts ← liftExcept (dest_list (← liftExcept (dest_comb (concl rol_thm))).2)
    if pts.length = 0 then pure [lem0] else
    if pts.length = 1 then pure (CONJUNCTS (← ISPEC (← liftExcept (hd pts)) lem1)) else
    let rthms ← rol_thms rol_thm
    let pt_thms ← pts.mapM (fun t => ISPEC t lem)
    let left_thm ← ISPEC (← liftExcept (hd pts)) REAL_GT_EXISTS
    let right_thm ← ISPEC (← liftExcept (last pts)) REAL_LT_EXISTS
    let int_thms ← rthms.mapM (MATCH_MP REAL_DENSE)
    let thms := interleave pt_thms int_thms
    pure (left_thm :: thms ++ [right_thm]))


  /-
    rol_nonempty_thms (ASSUME `real_ordered_list [y]`)
  -/

  let lem0 ← prove_by_refinement (
    (← q r"real_ordered_list []"),
  /- {{{ Proof -/
  [REWRITE_TAC [real_ordered_list]])
  /- }}} -/

  let lem1 ← prove_by_refinement (
    (← q r"!x y. x < y ==> real_ordered_list [x; y]"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [real_ordered_list, NOT_CONS_NIL, HD]
  ])
  /- }}} -/

  let lem2 ← prove_by_refinement (
    (← q r"!x y. x < y ==> real_ordered_list (CONS y t) ==>
       real_ordered_list (CONS x (CONS y t))"),
  /- {{{ Proof -/
  [
    ASM_MESON_TAC [real_ordered_list, NOT_CONS_NIL, HD, TL]
  ])
  /- }}} -/

  let mk_rol : List thm → ExceptT String IO thm ← pure (fun ord_thms => do
    match ord_thms with
    | [] => pure lem0
    | [x] => MATCH_MP lem1 x
    | _h1 :: _h2 :: _rest =>
      -- itlist: the last of `butlast ord_thms` first
      (← liftExcept (butlast ord_thms)).foldrM (fun x y => MATCH_MPL [lem2, x, y])
        (← MATCH_MP lem1 (← liftExcept (last ord_thms))))

  /-
  let k0 = rol_thms (ASSUME `real_ordered_list [x1; x2; x3; x4; x5]`)
  mk_rol k0
  -/

  let real_nil : term ← q r"[]:real list"
  let ROL_NIL ← prove
    r"real_ordered_list ([]:real list)"
     (REWRITE_TAC [real_ordered_list])

  let ROL_REMOVE : term → thm → ExceptT String IO thm ← pure (fun x rol_thm => do
    let list ← liftExcept (dest_list (← liftExcept (dest_comb (concl rol_thm))).2)
    if list.length = 0 then throw "ROL_REMOVE: 0"
    else if list.length = 1 then
      if x == (← liftExcept (hd list)) then pure ROL_NIL
      else throw "ROL_REMOVE: Not an elem"
    else if list.length = 2 then
      let (l, r) ← match list with
        | [l, r] => pure (l, r)
        | _ => throw "Match_failure"
      if l == x then ISPEC r ROL_SING
      else if r == x then ISPEC l ROL_SING
      else throw "ROL_REMOVE: Not an elem"
    else
    let ord_thms ← rol_thms rol_thm
    let partition_fun (thm : thm) : Except String Bool := do
      let (l, r) ← dest_binop rlt (concl thm)
      pure (!(x == l) && !(x == r))
    -- `partition partition_fun ord_thms`, whose failure is the rule's
    let flags ← liftExcept (ord_thms.mapM partition_fun)
    let ord_thms' := ((ord_thms.zip flags).filter (·.2)).map (·.1)
    let elim_thms := ((ord_thms.zip flags).filter (!·.2)).map (·.1)
    if elim_thms.length = 1 then mk_rol ord_thms' else
    let (xy_thm, yz_thm) ← match elim_thms with
      | [xy_thm, yz_thm] => pure (xy_thm, yz_thm)
      | _ => throw "Match_failure"
    let connect_thm ← MATCH_MP REAL_LT_TRANS (← CONJ xy_thm yz_thm)
    let ord_thms'' ← liftExcept (ROL_REMOVE.insert rlt connect_thm connect_thm ord_thms')
    mk_rol ord_thms'')


  /-
  ROL_REMOVE `x1:real` (ASSUME `real_ordered_list [x1]`)
  ROL_REMOVE `x1:real` (ASSUME `real_ordered_list [x1; x3]`)
  ROL_REMOVE `x3:real` (ASSUME `real_ordered_list [x1; x3]`)
  ROL_REMOVE `x3:real` (ASSUME `real_ordered_list [x1; x2; x3; x4; x5]`)
  ROL_REMOVE `x1:real` (ASSUME `real_ordered_list [x1; x2; x3; x4; x5]`)
  ROL_REMOVE `x5:real` (ASSUME `real_ordered_list [x1; x2; x3; x4; x5]`)

  ROL_REMOVE `-- &1` (ASSUME `real_ordered_list [-- &1; &0; &1]`)
  let rol_thm =  (ASSUME `real_ordered_list [-- &1; &0; &1]`)
  let x = `&0`
  -/

  let lem ← prove
    r"!y x. x < y \/ (x = y) \/ y < x"
  /- {{{ Proof -/
    REAL_ARITH_TAC
  /- }}} -/

  let lem2 ← prove
    r"!x y z. y < z ==> (y < x <=> (y < x /\ x < z) \/ (x = z) \/ z < x)"
  /- {{{ Proof -/
    REAL_ARITH_TAC
  /- }}} -/


  let ROL_COVERS : thm → ExceptT String IO thm ← pure (fun rol_thm => do
    let pts ← liftExcept (dest_list (← liftExcept (dest_comb (concl rol_thm))).2)
    if pts.length = 1 then ISPEC (← liftExcept (hd pts)) lem else
    let thms ← rol_thms rol_thm
    -- `let thms' = map (MATCH_MP lem2) thms`: unused, but its failure is the
    -- rule's
    discard <| thms.mapM (MATCH_MP lem2)
    let base ← ISPEC (← liftExcept (hd pts)) lem
    (HolLight.rev thms).foldrM (fun x y => do ONCE_REWRITE_RULE [← MATCH_MP lem2 x] y) base)

  /-
  ROL_COVERS (ASSUME `real_ordered_list [x; y; z]`)
  ROL_COVERS (ASSUME `real_ordered_list [x; y]`)
  ROL_COVERS (ASSUME `real_ordered_list [x]`)

  -/

  -- @@RETURN BEGIN
  return { real_ordered_list, ROL_EMPTY, ROL_SING, ROL_TAIL, EL_CONS, NOT_ROL, ROL_CONS,
           ROL_CONS_CONS, ROL_APPEND, ROL_CONS_CONS_LT, ROL_INSERT_THM,
           ROL_INSERT_FRONT_THM, ROL_CONS_CONS_DELETE, LAST_CONS_LT, ROL_INSERT_BACK_THM,
           CHOP_REAL_LIST, ROL_CHOP_LT, t1, ROL_CHOP_LIST, lem1, ROL_INSERT_MIDDLE,
           ROL_INSERT_FRONT, ROL_INSERT_BACK, ROL_INSERT, rol_thms, lem, lem0,
           rol_nonempty_thms, lem2, mk_rol, real_nil, ROL_NIL, ROL_REMOVE, ROL_COVERS }
  -- @@RETURN END

end HolRQE.Rol
