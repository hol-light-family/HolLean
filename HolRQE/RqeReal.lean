/- ========================================================================= -/
/- Rqe: real operators and basic real lemmas.                              -/
/- ========================================================================= -/
/- File: HolRQE/RqeReal.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/rqe_real.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.RqeReal fills them).

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

namespace HolRQE.RqeReal

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (DE_MORGAN_THM EVEN EVEN_AND_ODD EVEN_OR_ODD NEQ NOT_EVEN NOT_ODD ODD POW_0
   REAL REAL_ADD_ASSOC REAL_ADD_LDISTRIB REAL_ADD_LID REAL_ADD_RDISTRIB
   REAL_ADD_RID REAL_ADD_RINV REAL_ADD_SYM REAL_ARCH_SIMPLE REAL_DOWN
   REAL_INV_MUL REAL_INV_NEG REAL_LET_ADD2 REAL_LE_ADD2 REAL_LE_INV2
   REAL_LE_LCANCEL_IMP REAL_LE_LMUL REAL_LE_MUL REAL_LE_MUL2 REAL_LE_REFL
   REAL_LE_TRANS REAL_LT REAL_LT_IMP_NZ REAL_LT_INV REAL_LT_INV2
   REAL_LT_LCANCEL_IMP REAL_LT_LE REAL_LT_MUL REAL_LT_MUL2 REAL_LT_RADD
   REAL_LT_SUB_LADD REAL_MUL_ASSOC REAL_MUL_LID REAL_MUL_LINV REAL_MUL_LZERO
   REAL_MUL_RID REAL_MUL_RNEG REAL_MUL_SYM REAL_NOT_LT REAL_POW_LE REAL_POW_LT
   real_div real_gt real_pow real_sub : thm)
  deriving Inhabited

/-- What rqe_real.ml uses from Session besides theorems. -/
structure RqeRealDeps where
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
/-  Reals (rqe_real.ml 1-475)                                             -/
/- ---------------------------------------------------------------------- -/

structure RqeRealThms where
  -- @@FIELDS
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
  REAL_DENSE : thm
  REAL_LT_EXISTS : thm
  REAL_GT_EXISTS : thm
  REAL_DIV_DISTRIB_L : thm
  REAL_DIV_DISTRIB_R : thm
  REAL_DIV_DISTRIB_2 : thm
  REAL_DIV_ADD_DISTRIB : thm
  DIV_ID : thm
  POS_POW : thm
  POS_NAT_POW : thm
  REAL_NUM_LE_0 : thm
  REAL_ARCH_SIMPLE_LT : thm
  BINOMIAL_LEMMA_LT : thm
  BINOMIAL_LEMMA : thm
  NEG_ABS : thm
  REAL_MUL_LT : thm
  REAL_MUL_GT : thm
  REAL_DIV_INV : thm
  REAL_DIV_DENOM_LT : thm
  REAL_DIV_DENOM_LE : thm
  REAL_NEG_DIV : thm
  REAL_GT_IMP_NZ : thm
  REAL_NEG_NZ : thm
  PARITY_POW_LT : thm
  EVEN_ODD_POW : thm
  deriving Inhabited

@[nospecialize]
def setupRqeRealThms [HolBase] (D : RqeRealDeps) :
    ExceptT String IO RqeRealThms := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, CASES_ON, CCONTR_TAC, CLAIM, EXISTS_TAC,
        INDUCT_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_REWRITES,
        REAL_SIMP_TAC, REAL_SOLVE_TAC, prove_by_refinement, .. } := D
  let { DE_MORGAN_THM, EVEN, EVEN_AND_ODD, EVEN_OR_ODD, NEQ, NOT_EVEN, NOT_ODD, ODD,
        POW_0, REAL, REAL_ADD_ASSOC, REAL_ADD_LDISTRIB, REAL_ADD_LID,
        REAL_ADD_RDISTRIB, REAL_ADD_RID, REAL_ADD_RINV, REAL_ADD_SYM, REAL_ARCH_SIMPLE,
        REAL_DOWN, REAL_INV_MUL, REAL_INV_NEG, REAL_LET_ADD2, REAL_LE_ADD2,
        REAL_LE_INV2, REAL_LE_LCANCEL_IMP, REAL_LE_LMUL, REAL_LE_MUL, REAL_LE_MUL2,
        REAL_LE_REFL, REAL_LE_TRANS, REAL_LT, REAL_LT_IMP_NZ, REAL_LT_INV,
        REAL_LT_INV2, REAL_LT_LCANCEL_IMP, REAL_LT_LE, REAL_LT_MUL, REAL_LT_MUL2,
        REAL_LT_RADD, REAL_LT_SUB_LADD, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LINV,
        REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RNEG, REAL_MUL_SYM, REAL_NOT_LT,
        REAL_POW_LE, REAL_POW_LT, real_div, real_gt, real_pow, real_sub, .. } := D.core1
  -- @@SCOPE END

  let real_ty : hol_type ← qty "real"
  let rx : term ← q r"x:real"
  let ry : term ← q r"y:real"
  let rz : term ← q r"z:real"
  -- `rzero`, rebound (the same way) below
  discard <| q r"&0"
  let req : term ← q r"(=):real->real->bool"
  let rneq : term ← q r"(<>):real->real->bool"
  let rlt : term ← q r"(<):real->real->bool"
  let rgt : term ← q r"(>):real->real->bool"
  let rle : term ← q r"(<=):real->real->bool"
  let rge : term ← q r"(>=):real->real->bool"
  let rm : term ← q r"( * ):real->real->real"
  let rs : term ← q r"(-):real->real->real"
  let rn : term ← q r"(--):real->real"
  let rd : term ← q r"(/):real->real->real"
  let rp : term ← q r"(+):real->real->real"
  let rzero : term ← q r"&0"
  let rone : term ← q r"&1"
  let rlast : term ← q r"LAST:(real) list -> real"
  let rappend : term ← q r"APPEND:(real) list -> real list -> real list"
  let mk_rlist : List term → IO (Except String term) ← pure (fun l => HolMath.Lists.mk_list l real_ty)

  let diffl_tm : term ← q r"(diffl)"
  let dest_diffl : term → Except String (term × term) ← pure (fun tm =>
    match (do
        let (l, _var) ← dest_comb tm
        let (dp, p') ← dest_comb l
        let (d, p) ← dest_comb dp
        if !(d == diffl_tm) then .error "dest_diffl: not a diffl" else
        let (_, bod) ← dest_abs p
        pure (bod, p') : Except String (term × term)) with
    | .ok v => .ok v
    | .error _ => .error "dest_diffl")

  -- `let dest_mult = try dest_binop rm with _ -> ..`: the `try` covers only
  -- the partial application, which cannot fail, so dest_mult is dest_binop rm
  -- (and likewise dest_pow and dest_plus)
  let dest_mult : term → Except String (term × term) ← pure (dest_binop rm)

  let mk_mult : term → Except String (term → Except String term) ← pure (mk_binop rm)

  let pow_tm : term ← q r"(pow)"
  let dest_pow : term → Except String (term × term) ← pure (dest_binop pow_tm)

  let mk_plus : term → Except String (term → Except String term) ← pure (mk_binop rp)
  let mk_negative : term → Except String term ← pure (curry (fun (a, b) => mk_comb a b) rn)

  let dest_plus : term → Except String (term × term) ← pure (dest_binop rp)

  let REAL_DENSE ← prove
   r"!x y. x < y ==> ?z. x < z /\ z < y"
  /- {{{ Proof -/
    (REPEAT STRIP_TAC THEN
    CLAIM (← q r"&0 < y - x") THENL
    [REWRITE_TAC [REAL_LT_SUB_LADD, REAL_ADD_LID] THEN
       POP_ASSUM MATCH_ACCEPT_TAC,
     DISCH_THEN (ASSUME_TAC o (MATCH_MP REAL_DOWN)) THEN
       POP_ASSUM MP_TAC THEN STRIP_TAC THEN
       EXISTS_TAC (← q r"e + x") THEN
       STRIP_TAC THENL
       [ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
        CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [← GSYM REAL_ADD_RID])) THEN
        MATCH_MP_TAC REAL_LET_ADD2 THEN
        STRIP_TAC THENL
        [MATCH_ACCEPT_TAC REAL_LE_REFL,
         FIRST_ASSUM MATCH_ACCEPT_TAC],
        MATCH_EQ_MP_TAC ((← GEN (← q r"y:real") (← GEN (← q r"z:real")
          (← ISPECL [← q r"y:real", ← q r"z:real", ← q r"-- x"] REAL_LT_RADD)))) THEN
        REWRITE_TAC [← GSYM REAL_ADD_ASSOC, REAL_ADD_RINV, REAL_ADD_RID] THEN
        REWRITE_TAC [← GSYM real_sub] THEN
        FIRST_ASSUM MATCH_ACCEPT_TAC]])
  /- }}} -/

  let REAL_LT_EXISTS ← prove
   r"!x. ?y. x < y"
  /- {{{ Proof -/
    (GEN_TAC THEN
    EXISTS_TAC (← q r"x + &1") THEN
    REAL_ARITH_TAC)
  /- }}} -/

  let REAL_GT_EXISTS ← prove
   r"!x. ?y. y < x"
  /- {{{ Proof -/
    (GEN_TAC THEN
    EXISTS_TAC (← q r"x - &1") THEN
    REAL_ARITH_TAC)
  /- }}} -/

  let REAL_DIV_DISTRIB_L ← prove_by_refinement (
    (← q r"!x y z. x / (y * z) = (x / y) * (&1 / z)"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [real_div, REAL_INV_MUL],
    REAL_ARITH_TAC
  ])
  /- }}} -/

  let REAL_DIV_DISTRIB_R ← prove_by_refinement (
    (← q r"!x y z. x / (y * z) = (&1 / y) * (x / z)"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [real_div, REAL_INV_MUL],
    REAL_ARITH_TAC
  ])
  /- }}} -/

  let REAL_DIV_DISTRIB_2 ← prove_by_refinement (
    (← q r"!x y z. (x * w) / (y * z) = (x / y) * (w / z)"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [real_div, REAL_INV_MUL],
    REAL_ARITH_TAC
  ])
  /- }}} -/

  let REAL_DIV_ADD_DISTRIB ← prove_by_refinement (
    (← q r"!x y z. (x + y) / z = (x / z) + (y / z)"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [real_div, REAL_INV_MUL],
    REAL_ARITH_TAC
  ])
  /- }}} -/

  let DIV_ID ← prove_by_refinement (
   (← q r"!x. ~(x = &0) ==> (x / x = &1)"),
  /- {{{ Proof -/

  [
    REPEAT STRIP_TAC,
    REWRITE_TAC [real_div],
    ASM_MESON_TAC [REAL_MUL_LINV, REAL_MUL_SYM]
  ])

  /- }}} -/

  let POS_POW ← prove_by_refinement (
   (← q r"!c x. &0 < c /\ &0 < x ==> &0 < c * x pow k"),
  /- {{{ Proof -/

  [
    MESON_TAC [REAL_POW_LT, REAL_LT_MUL]
  ])

  /- }}} -/

  let POS_NAT_POW ← prove_by_refinement (
   (← q r"!c n. 0 < n /\ &0 < c ==> &0 < c * &n pow k"),
  /- {{{ Proof -/

  [
    MESON_TAC [REAL_POW_LT, REAL_LT_MUL, REAL_LT]
  ])

  /- }}} -/

  let REAL_NUM_LE_0 ← prove_by_refinement (
    (← q r"!n. &0 <= (&n)"),
  /- {{{ Proof -/
  [
    INDUCT_TAC,
    REAL_ARITH_TAC,
    REWRITE_TAC [REAL],
    REAL_ARITH_TAC
  ])
  /- }}} -/

  let REAL_ARCH_SIMPLE_LT ← prove_by_refinement (
    (← q r"!x. ?n. x < &n"),
  /- {{{ Proof -/
  [
    STRIP_TAC,
    CHOOSE_THEN ASSUME_TAC (← ISPEC (← q r"x:real") REAL_ARCH_SIMPLE),
    EXISTS_TAC (← q r"SUC n"),
    REWRITE_TAC [REAL],
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC
  ])
  /- }}} -/

  let BINOMIAL_LEMMA_LT ← do
    -- the REAL_ARITHs of the tactic list, right to left
    let r3 ← REAL_ARITH (← q r"x < y ==> x <= y")
    let r2 ← REAL_ARITH (← q r"&0 <= y ==> x <= y + x")
    let r1 ← REAL_ARITH (← q r"&0 <= y ==> x <= x + y")
    prove_by_refinement (
     (← q r"!x y. &0 < x /\ &0 < y
             ==> !n. 0 < n ==> x pow n + y pow n <= (x + y) pow n"),
  /- {{{ Proof -/

  [
    REPEAT GEN_TAC,
    STRIP_TAC,
    INDUCT_TAC,
    ARITH_TAC,
    REWRITE_TAC [real_pow],
    STRIP_TAC,
    CASES_ON (← q r"n = 0"),
    ASM_REWRITE_TAC [real_pow, REAL_MUL_RID, REAL_LE_REFL],
    CLAIM (← q r"0 < n"),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    DISCH_THEN (fun x => FIRST_ASSUM (fun y => tactic_of do pure (ASSUME_TAC (← MATCH_MP y x)))),
    MATCH_MP_TAC REAL_LE_TRANS,
    EXISTS_TAC (← q r"(x + y) * (x pow n + y pow n)"),
    STRIP_TAC,
    REWRITE_TAC [REAL_ADD_RDISTRIB],
    MATCH_MP_TAC REAL_LE_ADD2,
    CONJ_TAC,
    MATCH_MP_TAC REAL_LE_LMUL,
    STRIP_TAC,
    FIRST_ASSUM (fun x => MP_TAC x THEN ARITH_TAC),
    MATCH_MP_TAC r1,
    MATCH_MP_TAC REAL_POW_LE,
    FIRST_ASSUM (fun x => MP_TAC x THEN ARITH_TAC),
    REWRITE_TAC [REAL_ADD_LDISTRIB],
    MATCH_MP_TAC r2,
    MATCH_MP_TAC REAL_LE_MUL,
    CONJ_TAC,
    FIRST_ASSUM (fun x => MP_TAC x THEN REAL_ARITH_TAC),
    MATCH_MP_TAC r3,
    MATCH_MP_TAC REAL_POW_LT,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    MATCH_MP_TAC REAL_LE_LMUL,
    CONJ_TAC,
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC
  ])

  /- }}} -/

  let BINOMIAL_LEMMA ← prove_by_refinement (
     (← q r"!x y. &0 <= x /\ &0 <= y
             ==> !n. 0 < n ==> x pow n + y pow n <= (x + y) pow n"),
  /- {{{ Proof -/

  [
    REPEAT GEN_TAC,
    STRIP_TAC,
    CASES_ON (← q r"(x = &0) \/ (y = &0)"),
    POP_ASSUM DISJ_CASES_TAC,
    ASM_REWRITE_TAC [real_pow, REAL_ADD_LID, POW_0],
    REPEAT STRIP_TAC,
    CLAIM (← q r"n = SUC (PRE n)"),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    ONCE_ASM_REWRITE_TAC [],
    ASM_REWRITE_TAC [POW_0, REAL_ADD_LID, real_pow, REAL_LE_REFL],
    REPEAT STRIP_TAC,
    CLAIM (← q r"n = SUC (PRE n)"),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    ONCE_ASM_REWRITE_TAC [],
    ASM_REWRITE_TAC [POW_0, REAL_ADD_LID, REAL_ADD_RID, real_pow, REAL_LE_REFL],
    POP_ASSUM MP_TAC THEN REWRITE_TAC [DE_MORGAN_THM] THEN STRIP_TAC,
    MATCH_MP_TAC BINOMIAL_LEMMA_LT,
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC
  ])

  /- }}} -/

  let NEG_ABS ← prove_by_refinement (
    (← q r"!x. -- (abs x) <= &0"),
  /- {{{ Proof -/
  [
    REAL_ARITH_TAC
  ])
  /- }}} -/

  let REAL_MUL_LT ← do
    -- the REAL_ARITHs of the tactic list, right to left
    let r2 ← REAL_ARITH (← q r"x * --y = --(x * y)")
    let r1 ← REAL_ARITH (← q r"--y * x = --(y * x)")
    prove_by_refinement (
      (← q r"!x y. x * y < &0 <=> (x < &0 /\ &0 < y) \/ (&0 < x /\ y < &0)"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    EQ_TAC,
    REPEAT STRIP_TAC,
    CCONTR_TAC,
    REWRITE_ASSUMS ([REAL_NOT_LT, DE_MORGAN_THM] ++ (← deref REAL_REWRITES)),
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    CLAIM (← q r"x = &0"),
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    DISCH_THEN (REWRITE_ASSUMS o (list : thm → List thm)),
    REWRITE_ASSUMS (← deref REAL_REWRITES),
    ASM_MESON_TAC (← deref REAL_REWRITES),
    CLAIM (← q r"&0 * &0 <= x * y"),
    MATCH_MP_TAC REAL_LE_MUL2,
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    REAL_SIMP_TAC,
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    CLAIM (← q r"&0 * &0 <= --x * --y"),
    MATCH_MP_TAC REAL_LE_MUL2,
    REAL_SIMP_TAC,
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    REAL_SIMP_TAC,
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    CLAIM (← q r"y = &0"),
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    DISCH_THEN (REWRITE_ASSUMS o (list : thm → List thm)),
    REWRITE_ASSUMS (← deref REAL_REWRITES),
    ASM_REWRITE_TAC [],
    EVERY_ASSUM MP_TAC THEN ARITH_TAC,
    /- save -/
    REPEAT STRIP_TAC,
    CLAIM (← q r"&0 < --x"),
    EVERY_ASSUM MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"&0 * &0 < --x * y"),
    MATCH_MP_TAC REAL_LT_MUL2,
    REAL_SIMP_TAC,
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    REAL_SIMP_TAC,
    REWRITE_TAC [r1],
    REAL_ARITH_TAC,
    CLAIM (← q r"&0 < --y"),
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"&0 * &0 < x * --y"),
    MATCH_MP_TAC REAL_LT_MUL2,
    REAL_SIMP_TAC,
    ASM_REWRITE_TAC [],
    REAL_SIMP_TAC,
    REWRITE_TAC [r2],
    REAL_ARITH_TAC
  ])
  /- }}} -/

  let REAL_MUL_GT ← do
    -- the rules of the tactic list, right to left
    let a5 ← ARITH_RULE (← q r"&0 = &0 * &0")
    let a4 ← ARITH_RULE (← q r"&0 = &0 * &0")
    let a3 ← ARITH_RULE (← q r"x * y = --x * --y")
    let r2 ← REAL_ARITH (← q r"-- &0 = &0")
    let a1 ← ARITH_RULE (← q r"x < y <=> -- y < -- x")
    prove_by_refinement (
      (← q r"!x y. &0 < x * y <=> (x < &0 /\ y < &0) \/ (&0 < x /\ &0 < y)"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    EQ_TAC,
    REPEAT STRIP_TAC,
    ONCE_REWRITE_ASSUMS [a1],
    REWRITE_ASSUMS [← GSYM REAL_MUL_RNEG],
    REWRITE_ASSUMS [r2, REAL_MUL_LT],
    POP_ASSUM MP_TAC THEN REPEAT STRIP_TAC,
    DISJ1_TAC,
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    REPEAT STRIP_TAC,
    ONCE_REWRITE_TAC [a3],
    ONCE_REWRITE_TAC [a4],
    MATCH_MP_TAC REAL_LT_MUL2,
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    ONCE_REWRITE_TAC [a5],
    MATCH_MP_TAC REAL_LT_MUL2,
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC
  ])
  /- }}} -/

  let REAL_DIV_INV ← prove_by_refinement (
    (← q r"!y z. &0 < y /\ y < z ==> &1 / z < &1 / y"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    REWRITE_TAC [real_div],
    REAL_SIMP_TAC,
    MATCH_MP_TAC REAL_LT_INV2,
    ASM_MESON_TAC []
  ])
  /- }}} -/

  let REAL_DIV_DENOM_LT ← prove_by_refinement (
    (← q r"!x y z. &0 < x /\ &0 < y /\ y < z ==> x / z < x / y"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP,
    EXISTS_TAC (← q r"inv x"),
    REPEAT STRIP_TAC,
    REAL_SOLVE_TAC,
    REWRITE_TAC [real_div],
    ASM_SIMP_TAC [REAL_LT_IMP_NZ, REAL_MUL_ASSOC, REAL_MUL_LINV],
    REAL_SIMP_TAC,
    MATCH_MP_TAC (← REWRITE_RULE [REAL_MUL_LID, real_div] REAL_DIV_INV),
    ASM_MESON_TAC []
  ])
  /- }}} -/

  let REAL_DIV_DENOM_LE ← prove_by_refinement (
    (← q r"!x y z. &0 <= x /\ &0 < y /\ y <= z ==> x / z <= x / y"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    CASES_ON (← q r"x = &0"),
    ASM_REWRITE_TAC [],
    REWRITE_TAC [real_div, REAL_MUL_LZERO, REAL_LE_REFL],
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP,
    EXISTS_TAC (← q r"inv x"),
    REPEAT STRIP_TAC,
    MATCH_MP_TAC REAL_LT_INV,
    ASM_MESON_TAC [REAL_LT_LE],
    REWRITE_TAC [real_div],
    ASM_SIMP_TAC [REAL_LT_IMP_NZ, REAL_MUL_ASSOC, REAL_MUL_LINV],
    REAL_SIMP_TAC,
    MATCH_MP_TAC REAL_LE_INV2,
    ASM_REWRITE_TAC []
  ])
  /- }}} -/

  let REAL_NEG_DIV ← prove_by_refinement (
    (← q r"!x y. -- x / -- y = x / y"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [real_div],
    REWRITE_TAC [REAL_INV_NEG],
    REAL_ARITH_TAC
  ])
  /- }}} -/

  let REAL_GT_IMP_NZ ← prove
    r"!x. x < &0 ==> ~(x = &0)"
  /- {{{ Proof -/
   REAL_ARITH_TAC
  /- }}} -/

  let REAL_NEG_NZ ← prove
    r"!x. x < &0 ==> ~(x = &0)"
  /- {{{ Proof -/
    REAL_ARITH_TAC
  /- }}} -/

  let PARITY_POW_LT ← prove_by_refinement (
    (← q r"!a n. a < &0 ==> (EVEN n ==> a pow n > &0) /\ (ODD n ==> a pow n < &0)"),
  /- {{{ Proof -/

  [
    STRIP_TAC,
    INDUCT_TAC,
    REWRITE_TAC [EVEN, ODD, real_pow],
    REAL_ARITH_TAC,
    DISCH_THEN (fun x => REWRITE_ASSUMS [x] THEN ASSUME_TAC x),
    REWRITE_TAC [EVEN, ODD, real_pow, NOT_EVEN, NOT_ODD],
    DISJ_CASES_TAC (← ISPEC (← q r"n:num") EVEN_OR_ODD),
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [real_gt, REAL_MUL_GT],
    ASM_MESON_TAC [EVEN_AND_ODD],
    ASM_REWRITE_TAC [real_gt, REAL_MUL_LT],
    ASM_MESON_TAC [real_gt],
    ASM_REWRITE_TAC [],
    ASM_REWRITE_TAC [real_gt, REAL_MUL_LT, REAL_MUL_GT],
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [],
    ASM_MESON_TAC [EVEN_AND_ODD]
  ])

  /- }}} -/

  let EVEN_ODD_POW ← prove_by_refinement (
    (← q r"!a n.  a <> &0 ==>
            (EVEN n ==> a pow n > &0) /\
            (ODD n ==> a < &0 ==> a pow n < &0) /\
            (ODD n ==> a > &0 ==> a pow n > &0)"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [NEQ],
    REPEAT_N 2 STRIP_TAC,
    CLAIM (← q r"a < &0 \/ a > &0 \/ (a = &0)"),
    REAL_ARITH_TAC,
    ASM_REWRITE_TAC [],
    STRIP_TAC,
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [PARITY_POW_LT],
    ASM_MESON_TAC [PARITY_POW_LT],
    ASM_MESON_TAC [REAL_POW_LT, real_gt],
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [REAL_POW_LT, real_gt],
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    ASM_MESON_TAC [REAL_POW_LT, real_gt],
    ASM_REWRITE_TAC []
  ])
  /- }}} -/

  -- @@RETURN BEGIN
  return { real_ty, rx, ry, rz, req, rneq, rlt, rgt, rle, rge, rm, rs, rn, rd, rp, rzero,
           rone, rlast, rappend, mk_rlist, diffl_tm, dest_diffl, dest_mult, mk_mult,
           pow_tm, dest_pow, mk_plus, mk_negative, dest_plus, REAL_DENSE, REAL_LT_EXISTS,
           REAL_GT_EXISTS, REAL_DIV_DISTRIB_L, REAL_DIV_DISTRIB_R, REAL_DIV_DISTRIB_2,
           REAL_DIV_ADD_DISTRIB, DIV_ID, POS_POW, POS_NAT_POW, REAL_NUM_LE_0,
           REAL_ARCH_SIMPLE_LT, BINOMIAL_LEMMA_LT, BINOMIAL_LEMMA, NEG_ABS, REAL_MUL_LT,
           REAL_MUL_GT, REAL_DIV_INV, REAL_DIV_DENOM_LT, REAL_DIV_DENOM_LE, REAL_NEG_DIV,
           REAL_GT_IMP_NZ, REAL_NEG_NZ, PARITY_POW_LT, EVEN_ODD_POW }
  -- @@RETURN END

end HolRQE.RqeReal
