/- ========================================================================= -/
/- Rqe: asymptotics of sequences and polynomials, normal polynomials.      -/
/- ========================================================================= -/
/- File: HolRQE/Asym.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/asym.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml, Rqe/num_calc_simp.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.Asym fills them).

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

namespace HolRQE.Asym

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ABS_0 ABS_DIV ABS_LE ABS_POS ADD1 ADD_SYM AND_IMP_THM CONS_11 DE_MORGAN_THM
   DIV_ID ETA_AX EVEN EVEN_OR_ODD FUN_EQ_THM GE GT LAST LAST_CONS LAST_SING
   LAST_TL LENGTH LENGTH_0 LENGTH_1 LENGTH_EQ_NIL LENGTH_NZ LENGTH_PAIR
   LENGTH_SING LENGTH_TL LE_REFL LT LT_REFL NEG_ABS NOT_CONS_NIL NOT_EVEN NOT_LE
   NOT_ODD NOT_SUC ODD ONE POLY_MVT POLY_NEG POW_NZ PRE REAL_10 REAL_ABS_DIV
   REAL_ABS_NEG REAL_ABS_NUM REAL_ABS_NZ REAL_ABS_REFL REAL_ADD_LID REAL_ADD_RID
   REAL_ADD_RINV REAL_ARCH_SIMPLE REAL_ARCH_SIMPLE_LT REAL_DIV_ADD_DISTRIB
   REAL_DIV_DENOM_LT REAL_DIV_DISTRIB_2 REAL_DIV_DISTRIB_L REAL_DIV_DISTRIB_R
   REAL_DIV_LZERO REAL_DIV_REFL REAL_ENTIRE REAL_EQ_MUL_LCANCEL REAL_INJ
   REAL_INV_NEG REAL_INV_NZ REAL_INV_POS REAL_LE REAL_LET_TRANS REAL_LE_DIV
   REAL_LE_LCANCEL_IMP REAL_LE_LDIV_EQ REAL_LE_LMUL REAL_LE_LT REAL_LE_MUL
   REAL_LE_MUL2 REAL_LE_NEG2 REAL_LE_RCANCEL_IMP REAL_LE_REFL REAL_LE_TRANS
   REAL_LT REAL_LTE_TRANS REAL_LT_IMP_NZ REAL_LT_INV REAL_LT_INV_EQ
   REAL_LT_LCANCEL_IMP REAL_LT_LDIV_EQ REAL_LT_LE REAL_LT_LMUL REAL_LT_MUL
   REAL_LT_MUL2 REAL_LT_NZ REAL_LT_RCANCEL_IMP REAL_LT_RDIV_0 REAL_LT_TOTAL
   REAL_LT_TRANS REAL_MAX_MAX REAL_MUL_ASSOC REAL_MUL_GT REAL_MUL_LID
   REAL_MUL_LINV REAL_MUL_LT REAL_MUL_LZERO REAL_MUL_RID REAL_MUL_RINV
   REAL_MUL_RZERO REAL_MUL_SYM REAL_NEG_0 REAL_NEG_DIV REAL_NEG_MUL2 REAL_NOT_LE
   REAL_NOT_LT REAL_NUM_LE_0 REAL_OF_NUM_ADD REAL_OF_NUM_EQ REAL_OF_NUM_LE
   REAL_OF_NUM_LT REAL_POW_1 REAL_POW_LE REAL_POW_MONO REAL_POW_NEG REAL_POW_NZ
   SEQ SEQ_ADD SEQ_CONST SEQ_MUL TL TL_NIL degree list_CASES list_RECURSION mono
   nmax normalize poly poly_cmul poly_diff poly_diff_aux poly_neg pow real_div
   real_ge real_gt real_max real_pow real_sub : thm)
  deriving Inhabited

/-- What asym.ml uses from Session besides theorems. -/
structure AsymDeps where
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
  override_interface : String → term → ExceptT String IO Unit
  prioritize_real : IO Unit
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



/- ---------------------------------------------------------------------- -/
/-  The `-->` interface, prioritize_real, properties of num sequences and  -/
/-  unbounded sequences (asym.ml 1-505)                                    -/
/- ---------------------------------------------------------------------- -/

structure AsymSeq where
  -- @@FIELDS
  LIM_INV_1N : thm
  LIM_INV_CONST : thm
  LIM_INV_1NP : thm
  LIM_INV_CON : thm
  LIM_NN : thm
  LIM_NNC : thm
  LIM_MONO : thm
  LIM_POLY_LT : thm
  LIM_POLY : thm
  mono_inc : thm
  mono_dec : thm
  mono_inc_dec : thm
  mono_inc_pow : thm
  mono_inc_pow_const : thm
  mono_unbounded_above : thm
  mono_unbounded_below : thm
  mono_unbounded_above_pos : thm
  mono_unbounded_below_neg : thm
  mua_quotient_limit : thm
  mua_neg : thm
  mua_neg2 : thm
  mua_quotient_limit_neg : thm
  deriving Inhabited

@[nospecialize]
def setupAsymSeq [HolBase] (D : AsymDeps) :
    ExceptT String IO AsymSeq := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, CASES_ON, CLAIM, EXISTS_TAC, INDUCT_TAC,
        LIST_INDUCT_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_REWRITES,
        new_definition, override_interface, prioritize_real, prove_by_refinement, .. } := D
  let { ABS_0, ABS_DIV, ABS_LE, ABS_POS, AND_IMP_THM, DIV_ID, GE, GT, LAST, LENGTH,
        LENGTH_0, LT, NEG_ABS, PRE, REAL_10, REAL_ABS_NUM, REAL_ADD_RID, REAL_ADD_RINV,
        REAL_ARCH_SIMPLE, REAL_DIV_ADD_DISTRIB, REAL_DIV_DISTRIB_2, REAL_DIV_DISTRIB_L,
        REAL_DIV_DISTRIB_R, REAL_DIV_LZERO, REAL_DIV_REFL, REAL_INV_NEG, REAL_LE,
        REAL_LET_TRANS, REAL_LE_DIV, REAL_LE_LDIV_EQ, REAL_LE_LMUL, REAL_LE_MUL,
        REAL_LE_MUL2, REAL_LE_RCANCEL_IMP, REAL_LE_REFL, REAL_LE_TRANS, REAL_LTE_TRANS,
        REAL_LT_IMP_NZ, REAL_LT_INV, REAL_LT_INV_EQ, REAL_LT_LCANCEL_IMP,
        REAL_LT_LDIV_EQ, REAL_LT_LE, REAL_LT_LMUL, REAL_LT_NZ, REAL_LT_RCANCEL_IMP,
        REAL_LT_RDIV_0, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_RID, REAL_MUL_RINV,
        REAL_MUL_RZERO, REAL_MUL_SYM, REAL_NEG_0, REAL_NEG_MUL2, REAL_NOT_LE,
        REAL_NUM_LE_0, REAL_POW_1, REAL_POW_LE, SEQ, SEQ_ADD, SEQ_CONST, SEQ_MUL, mono,
        nmax, poly, real_div, real_ge, real_gt, real_pow, real_sub, .. } := D.core1
  -- @@SCOPE END

  override_interface "-->" (← q r"(tends_num_real)")
  prioritize_real

  /- ---------------------------------------------------------------------- -/
  /-  properites of num sequences                                           -/
  /- ---------------------------------------------------------------------- -/

  let LIM_INV_1N ← do
    -- the REAL_ARITHs of the tactic list, right to left
    let r2 ← REAL_ARITH (← q r"&1 < &2")
    let r1 ← REAL_ARITH (← q r"&0 < &2")
    prove_by_refinement (
    (← q r"(\n. &1 / &n) --> &0"),
  /- {{{ Proof -/

  [
    REWRITE_TAC [SEQ, real_sub, REAL_ADD_RID, REAL_NEG_0, real_gt, real_ge, GT, GE],
    REPEAT STRIP_TAC,
    MP_TAC (← ISPEC (← q r"&2 / e") REAL_ARCH_SIMPLE),
    STRIP_TAC,
    EXISTS_TAC (← q r"n"),
    REPEAT STRIP_TAC,
    CLAIM (← q r"&0 < &2 / e"),
    ASM_MESON_TAC [REAL_LT_RDIV_0, r1],
    STRIP_TAC,
    CLAIM (← q r"&0 < &n"),
    ASM_MESON_TAC [REAL_LTE_TRANS, REAL_LE],
    STRIP_TAC,
    CLAIM (← q r"&0 < &n'"),
    ASM_MESON_TAC [REAL_LTE_TRANS, REAL_LE],
    STRIP_TAC,
    CLAIM (← q r"~(&n' = &0)"),
    ASM_MESON_TAC [REAL_LT_IMP_NZ],
    STRIP_TAC,
    ASM_SIMP_TAC [ABS_DIV],
    REWRITE_TAC [REAL_ABS_NUM],
    ASM_SIMP_TAC [REAL_LT_LDIV_EQ],
    CLAIM (← q r"&2 <= e * &n"),
    ASM_MESON_TAC [REAL_LE_LDIV_EQ, REAL_MUL_SYM],
    STRIP_TAC,
    CLAIM (← q r"e * &n <= e * &n'"),
    MATCH_MP_TAC REAL_LE_LMUL,
    ASM_MESON_TAC [REAL_LT_LE, REAL_LE],
    STRIP_TAC,
    ASM_MESON_TAC [REAL_LTE_TRANS, REAL_LE_TRANS, r2]
  ])

  /- }}} -/

  let LIM_INV_CONST ← do
    let r2 ← REAL_ARITH (← q r"&0 = c * &0")
    let r1 ← REAL_ARITH (← q r"c / &n = c * &1 / &n")
    prove_by_refinement (
    (← q r"!c. (\n. c / &n) --> &0"),
  /- {{{ Proof -/

  [
    ONCE_REWRITE_TAC [r1],
    STRIP_TAC,
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [r2])),
    MATCH_MP_TAC SEQ_MUL,
    CONJ_TAC THENL [MATCH_ACCEPT_TAC SEQ_CONST, MATCH_ACCEPT_TAC LIM_INV_1N]
  ])

  /- }}} -/

  let LIM_INV_1NP ← do
    let r2 ← REAL_ARITH (← q r"&0 = &0 * &0")
    let a1 ← ARITH_RULE (← q r"~(0 < 0)")
    prove_by_refinement (
    (← q r"!c k. 0 < k ==> (\n. c / &n pow k) --> &0"),
  /- {{{ Proof -/
  [
    STRIP_TAC,
    INDUCT_TAC,
    REWRITE_TAC [a1],
    REWRITE_TAC [real_pow, REAL_DIV_DISTRIB_R],
    STRIP_TAC,
    CASES_ON (← q r"k = 0"),
    ASM_REWRITE_TAC [real_pow, ← GSYM REAL_DIV_DISTRIB_R, REAL_MUL_RID],
    MATCH_ACCEPT_TAC LIM_INV_CONST,
    CLAIM (← q r"(\n. c / &n pow k) --> &0"),
    FIRST_ASSUM MATCH_MP_TAC,
    EVERY_ASSUM MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    ONCE_REWRITE_TAC [r2],
    MATCH_MP_TAC SEQ_MUL,
    CONJ_TAC THENL [MATCH_ACCEPT_TAC LIM_INV_1N, FIRST_ASSUM MATCH_ACCEPT_TAC]
  ])
  /- }}} -/

  let LIM_INV_CON ← do
    let r1 ← REAL_ARITH (← q r"&0 = (&1 / d) * &0")
    prove_by_refinement (
    (← q r"!c d k. 0 < k ==> (\n. c / (d * &n pow k)) --> &0"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [REAL_DIV_DISTRIB_R],
    REPEAT STRIP_TAC,
    ONCE_REWRITE_TAC [r1],
    MATCH_MP_TAC SEQ_MUL,
    CONJ_TAC,
    MATCH_ACCEPT_TAC SEQ_CONST,
    POP_ASSUM MP_TAC THEN MATCH_ACCEPT_TAC LIM_INV_1NP
  ])
  /- }}} -/

  let LIM_NN ← do
    let r1 ← REAL_ARITH (← q r"&0 < &1")
    prove_by_refinement (
    (← q r"(\n. &n / &n) --> &1"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [SEQ],
    REPEAT STRIP_TAC,
    EXISTS_TAC (← q r"1"),
    REWRITE_TAC [GT, GE],
    REPEAT STRIP_TAC,
    CLAIM (← q r"~(&n = &0)"),
    MATCH_MP_TAC REAL_LT_IMP_NZ,
    ASM_MESON_TAC [REAL_LE, r1, REAL_LTE_TRANS],
    STRIP_TAC,
    ASM_SIMP_TAC [REAL_DIV_REFL, real_sub, REAL_ADD_RINV, ABS_0]
  ])
  /- }}} -/

  let LIM_NNC ← do
    let r1 ← REAL_ARITH (← q r"&1 = &1 * &1")
    prove_by_refinement (
    (← q r"~(k = &0) ==> (\n. (k * &n) / (k * &n)) --> &1"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [REAL_DIV_DISTRIB_2],
    ONCE_REWRITE_TAC [r1],
    STRIP_TAC,
    MATCH_MP_TAC SEQ_MUL,
    CONJ_TAC,
    ASM_SIMP_TAC [real_div, REAL_MUL_RINV],
    MATCH_ACCEPT_TAC SEQ_CONST,
    MATCH_ACCEPT_TAC LIM_NN
  ])
  /- }}} -/

  let LIM_MONO ← do
    let r2 ← REAL_ARITH (← q r"&0 = &1 * &0")
    let a1 ← ARITH_RULE (← q r"a * b * c = b * a * c")
    prove_by_refinement (
    (← q r"!c d a b. ~(d = &0) /\ a < b ==> (\n. (c * &n pow a) / (d * &n pow b)) --> &0"),
  /- {{{ Proof -/
  [
    STRIP_TAC THEN STRIP_TAC,
    INDUCT_TAC,
    REPEAT STRIP_TAC,
    REWRITE_TAC [real_pow, REAL_MUL_RID],
    POP_ASSUM MP_TAC THEN MATCH_ACCEPT_TAC LIM_INV_CON,
    REPEAT STRIP_TAC,
    REWRITE_TAC [real_pow],
    CLAIM (← q r"(b = SUC(PRE b))"),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    ONCE_ASM_REWRITE_TAC [],
    REWRITE_TAC [real_pow],
    ONCE_REWRITE_TAC [a1],
    ONCE_REWRITE_TAC [REAL_DIV_DISTRIB_2],
    ONCE_REWRITE_TAC [r2],
    MATCH_MP_TAC SEQ_MUL,
    CONJ_TAC,
    MATCH_ACCEPT_TAC LIM_NN,
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_REWRITE_TAC [],
    LABEL_ALL_TAC,
    USE_THEN "Z-1" MP_TAC,
    ARITH_TAC
  ])
  /- }}} -/

  let LIM_POLY_LT ← do
    -- the rules of the tactic list, right to left
    let r3 ← REAL_ARITH (← q r"&0 = &1 * &0")
    let a2 ← ARITH_RULE (← q r"n pow k = &1 * n pow k")
    let r1 ← REAL_ARITH (← q r"&0 = &0 + &0")
    prove_by_refinement (
    (← q r"!p k. LENGTH p <= k ==> (\n. poly p (&n) / &n pow k) --> &0"),
  /- {{{ Proof -/

  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [poly, LENGTH],
    REPEAT STRIP_TAC,
    REWRITE_TAC [REAL_DIV_LZERO, SEQ_CONST],
    REWRITE_TAC [poly, LENGTH],
    REPEAT STRIP_TAC,
    CLAIM (← q r"~(k = 0)"),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    LABEL_ALL_TAC,
    CLAIM (← q r"LENGTH t <= PRE k"),
    USE_THEN "Z-1" MP_TAC THEN ARITH_TAC,
    DISCH_THEN (fun x => FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x)))),
    STRIP_TAC,
    REWRITE_TAC [REAL_DIV_ADD_DISTRIB],
    ONCE_REWRITE_TAC [r1],
    MATCH_MP_TAC SEQ_ADD,
    CONJ_TAC,
    ONCE_REWRITE_TAC [a2],
    MATCH_MP_TAC LIM_INV_CON,
    USE_THEN "Z-0" MP_TAC THEN ARITH_TAC,
    CLAIM (← q r"k = SUC (PRE k)"),
    USE_THEN "Z-0" MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    ONCE_ASM_REWRITE_TAC [],
    REWRITE_TAC [real_pow],
    REWRITE_TAC [REAL_DIV_DISTRIB_2],
    ONCE_REWRITE_TAC [r3],
    MATCH_MP_TAC SEQ_MUL,
    CONJ_TAC,
    MATCH_ACCEPT_TAC LIM_NN,
    FIRST_ASSUM MATCH_MP_TAC,
    USE_THEN "Z-1" MP_TAC THEN ARITH_TAC
  ])

  /- }}} -/

  let LIM_POLY ← do
    -- the rules of the tactic list, right to left
    let r4 ← REAL_ARITH (← q r"&1 = &1 * &1")
    let a3 ← ARITH_RULE (← q r"a * b * c = b * a * c")
    let r2 ← REAL_ARITH (← q r"&1 = &0 + &1")
    let r1 ← REAL_ARITH (← q r"&1 = &1 * &1")
    prove_by_refinement (
    (← q r"!p. (0 < LENGTH p /\ ~(LAST p = &0)) ==>
       (\n. poly p (&n) / (LAST p * &n pow PRE (LENGTH p))) --> &1"),
  /- {{{ Proof -/

  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [LENGTH, LT],
    ASM_REWRITE_TAC [LENGTH, poly],
    REPEAT STRIP_TAC,
    CASES_ON (← q r"t = []"),
    ASM_REWRITE_TAC [PRE, real_pow, REAL_POW_1, LAST, poly, REAL_MUL_RZERO, REAL_ADD_RID, LENGTH, REAL_DIV_DISTRIB_L],
    CLAIM (← q r"~(h = &0)"),
    ASM_MESON_TAC [LAST],
    STRIP_TAC,
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [r1])),
    MATCH_MP_TAC SEQ_MUL,
    CONJ_TAC,
    ASM_SIMP_TAC [DIV_ID],
    MATCH_ACCEPT_TAC SEQ_CONST,
    ASM_SIMP_TAC [DIV_ID, REAL_10],
    MATCH_ACCEPT_TAC SEQ_CONST,
    CLAIM (← q r"LAST (CONS h t) = LAST t"),
    ASM_REWRITE_TAC [LAST],
    STRIP_TAC,
    ASM_REWRITE_TAC [LAST, PRE],
    REWRITE_TAC [REAL_DIV_ADD_DISTRIB],
    ONCE_REWRITE_TAC [r2],
    MATCH_MP_TAC SEQ_ADD,
    CLAIM (← q r"~(LENGTH t = 0)"),
    ASM_MESON_TAC [LENGTH_0],
    STRIP_TAC,
    CONJ_TAC,
    MATCH_MP_TAC LIM_INV_CON,
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    CLAIM (← q r"(LENGTH t = SUC (PRE (LENGTH t)))"),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    ONCE_ASM_REWRITE_TAC [],
    REWRITE_TAC [real_pow],
    ONCE_REWRITE_TAC [a3],
    REWRITE_TAC [REAL_DIV_DISTRIB_2],
    ONCE_REWRITE_TAC [r4],
    MATCH_MP_TAC SEQ_MUL,
    CONJ_TAC,
    MATCH_ACCEPT_TAC LIM_NN,
    FIRST_ASSUM MATCH_MP_TAC,
    CONJ_TAC,
    LABEL_ALL_TAC,
    USE_THEN "Z-1" MP_TAC THEN ARITH_TAC,
    ASM_MESON_TAC []
  ])

  /- }}} -/

  let mono_inc ← new_definition (
    r"mono_inc (f:num -> real) = !(m:num) n. m <= n ==> f m <= f n")

  let mono_dec ← new_definition (
    r"mono_dec (f:num -> real) = !(m:num) n. m <= n ==> f n <= f m")

  let mono_inc_dec ← prove_by_refinement (
    (← q r"!f. mono f <=> mono_inc f \/ mono_dec f"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [mono_inc, mono_dec, mono, real_ge]
  ])
  /- }}} -/

  let mono_inc_pow ← prove_by_refinement (
   (← q r"!k. mono_inc (\n. &n pow k)"),
  /- {{{ Proof -/

  [
    REWRITE_TAC [mono_inc],
    INDUCT_TAC THEN REWRITE_TAC [real_pow, REAL_LE_REFL],
    GEN_TAC THEN GEN_TAC,
    DISCH_THEN (fun x => (RULE_ASSUM_TAC (fun y => MATCH_MP y x)) THEN ASSUME_TAC x),
    MATCH_MP_TAC REAL_LE_MUL2,
    REPEAT STRIP_TAC,
    MATCH_ACCEPT_TAC REAL_NUM_LE_0,
    ASM_REWRITE_TAC [REAL_LE],
    MATCH_MP_TAC REAL_POW_LE,
    MATCH_ACCEPT_TAC REAL_NUM_LE_0,
    FIRST_ASSUM MATCH_ACCEPT_TAC
  ])

  /- }}} -/

  let mono_inc_pow_const ← prove_by_refinement (
   (← q r"!k c. &0 < c ==> mono_inc (\n. c * &n pow k)"),
  /- {{{ Proof -/

  [
    REWRITE_TAC [mono_inc],
    REPEAT STRIP_TAC,
    MATCH_MP_TAC REAL_LE_MUL2,
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [REAL_LT_LE],
    REAL_ARITH_TAC,
    MATCH_MP_TAC REAL_POW_LE,
    MATCH_ACCEPT_TAC REAL_NUM_LE_0,
    ASM_MESON_TAC [mono_inc_pow, mono_inc]
  ])

  /- }}} -/

  /- ---------------------------------------------------------------------- -/
  /-  Unbounded sequences                                                   -/
  /- ---------------------------------------------------------------------- -/

  let mono_unbounded_above ← new_definition (
   r"mono_unbounded_above (f:num -> real) = !c. ?N. !n. N <= n ==> c < f n")

  let mono_unbounded_below ← new_definition (
   r"mono_unbounded_below (f:num -> real) = !c. ?N. !n. N <= n ==> f n < c")

  let mono_unbounded_above_pos ← prove_by_refinement (
   (← q r"mono_unbounded_above (f:num -> real) = !c. &0 <= c ==> ?N. !n. N <= n ==> c < f n"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [mono_unbounded_above],
    EQ_TAC THENL [ASM_MESON_TAC [], ALL_TAC],
    REPEAT STRIP_TAC,
    POP_ASSUM (ASSUME_TAC o ISPEC (← q r"abs c")),
    POP_ASSUM (MP_TAC o (← do
      let c ← ISPEC (← q r"c:real") ABS_POS
      pure (fun th => MATCH_MP th c))),
    STRIP_TAC,
    EXISTS_TAC (← q r"N"),
    GEN_TAC,
    DISCH_THEN (fun x => POP_ASSUM (fun y => tactic_of do pure (ASSUME_TAC (← MATCH_MP y x)))),
    ASM_MESON_TAC [ABS_LE, REAL_LET_TRANS]
  ])
  /- }}} -/

  let mono_unbounded_below_neg ← prove_by_refinement (
   (← q r"mono_unbounded_below (f:num -> real) = !c. c <= &0 ==> ?N. !n. N <= n ==> f n < c"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [mono_unbounded_below],
    EQ_TAC THENL [ASM_MESON_TAC [], ALL_TAC],
    REPEAT STRIP_TAC,
    POP_ASSUM (ASSUME_TAC o ISPEC (← q r"-- (abs c)")),
    POP_ASSUM (MP_TAC o (← do
      let c ← ISPEC (← q r"c:real") NEG_ABS
      pure (fun th => MATCH_MP th c))),
    STRIP_TAC,
    EXISTS_TAC (← q r"N"),
    GEN_TAC,
    DISCH_THEN (fun x => POP_ASSUM (fun y => tactic_of do pure (ASSUME_TAC (← MATCH_MP y x)))),
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC
  ])
  /- }}} -/

  let mua_quotient_limit ← do
    -- OCaml builds the tactic list right to left, so the elements after
    -- the nested `prove` (with their ARITH_RULEs and quotations, which warn
    -- "inventing type variables") come before its MESON, and the elements
    -- before it after
    let a4 ← ARITH_RULE (← q r"(a * b) * c = b * (a * c)")
    let a3 ← ARITH_RULE (← q r"a * (b * c) * d = c * b * (d * a)")
    let a2 ← ARITH_RULE (← q r"inv(&2) * &2 = &1")
    let tl : List tactic := [
    REPEAT STRIP_TAC,
    USE_THEN "Z-1" MP_TAC THEN REAL_ARITH_TAC,
    FIRST_ASSUM (fun x => tactic_of do
      pure (ASSUME_TAC (← MATCH_MP (← REWRITE_RULE [AND_IMP_THM] REAL_LT_LMUL) x))),
    LABEL_ALL_TAC,
    POP_ASSUM (fun y => USE_THEN "Z-6" (fun x => tactic_of do pure (ASSUME_TAC (← MATCH_MP y x)))),
    CLAIM (← q r"k * &2 * d * inv k = (k * inv k) * &2 * d"),
    REAL_ARITH_TAC,
    CLAIM (← q r"k * inv k = &1"),
    ASM_MESON_TAC [REAL_MUL_RINV, REAL_LT_NZ],
    STRIP_TAC,
    ASM_REWRITE_TAC [REAL_MUL_LID],
    ASM_MESON_TAC [],
    /-  -/
    MATCH_MP_TAC REAL_LE_RCANCEL_IMP,
    EXISTS_TAC (← q r"inv (g n)"),
    REWRITE_TAC [← GSYM REAL_MUL_ASSOC],
    CLAIM (← q r"&0 < inv (g n)"),
    CLAIM (← q r"&0 < inv k"),
    MATCH_MP_TAC REAL_LT_INV THEN FIRST_ASSUM MATCH_ACCEPT_TAC,
    STRIP_TAC,
    CLAIM (← q r"&0 < g n"),
    ASM_MESON_TAC (← deref REAL_REWRITES),
    STRIP_TAC,
    ASM_MESON_TAC [REAL_LT_INV],
    STRIP_TAC,
    ASM_REWRITE_TAC [],
    CLAIM (← q r"g n * inv (g n) = &1"),
    ASM_MESON_TAC [REAL_MUL_RINV, REAL_LT_NZ, REAL_LT_INV_EQ],
    DISCH_THEN SUBST1_TAC,
    REWRITE_TAC [REAL_MUL_RID],
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    /-  -/
    RULE_ASSUM_TAC (REWRITE_RULE [REAL_NOT_LE]),
    CLAIM (← q r"f n * inv (g n) - k < &0"),
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"abs (f n * inv (g n) - k) = k - (f n * inv (g n))"),
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    DISCH_THEN (fun x => RULE_ASSUM_TAC (REWRITE_RULE (list x))),
    CLAIM (← q r"k * inv(&2) < f n * inv (g n)"),
    LABEL_ALL_TAC,
    USE_THEN "Z-5" MP_TAC THEN REAL_ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"k * g n < &2 * f n"),
    CLAIM (← q r"&0 < g n"),
    LABEL_ALL_TAC,
    MATCH_MP_TAC REAL_LET_TRANS,
    EXISTS_TAC (← q r"&2 * d * inv k"),
    CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC,
    STRIP_TAC,
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP,
    EXISTS_TAC (← q r"inv(&2)"),
    CONJ_TAC THENL [REAL_ARITH_TAC, ALL_TAC],
    REWRITE_TAC [a2, REAL_MUL_LID, REAL_MUL_ASSOC],
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP,
    EXISTS_TAC (← q r"inv(g n)"),
    CONJ_TAC,
    ASM_MESON_TAC [REAL_LT_INV],
    ONCE_REWRITE_TAC [a3],
    CLAIM (← q r"g n * inv (g n) = &1"),
    POP_ASSUM MP_TAC THEN ASM_MESON_TAC [REAL_MUL_RINV, REAL_LT_IMP_NZ],
    DISCH_THEN SUBST1_TAC,
    ASM_MESON_TAC [REAL_MUL_RID, REAL_MUL_SYM],
    STRIP_TAC,
    CLAIM (← q r"&2 * d < k * g n"),
    MATCH_MP_TAC REAL_LT_RCANCEL_IMP,
    EXISTS_TAC (← q r"inv k"),
    STRIP_TAC,
    ASM_MESON_TAC [REAL_LT_INV],
    MATCH_MP_TAC REAL_LTE_TRANS,
    EXISTS_TAC (← q r"g n"),
    CONJ_TAC,
    REWRITE_TAC [← GSYM REAL_MUL_ASSOC],
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    LABEL_ALL_TAC,
    ONCE_REWRITE_TAC [a4],
    CLAIM (← q r"k * inv k = &1"),
    ASM_MESON_TAC [REAL_MUL_RINV, REAL_LT_IMP_NZ],
    DISCH_THEN SUBST1_TAC,
    REAL_ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"&2 * d < &2 * f n"),
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    REAL_ARITH_TAC
    ]
    let p1 ← prove r"d <= &2 * d /\ &2 * d < k * (g n) /\ k * (g n) <= f n ==> d < f n"
      (MESON_TAC (← deref REAL_REWRITES))
    let hd : List tactic := [
    REWRITE_TAC [SEQ, mono_unbounded_above_pos, AND_IMP_THM],
    REPEAT GEN_TAC,
    STRIP_TAC,
    CLAIM (← q r"&0 < k / &2"),
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    DISCH_THEN (fun x => DISCH_THEN (fun y => tactic_of do
      pure (ASSUME_TAC (← MATCH_MP (← ISPEC (← q r"k / &2") y) x)))),
    POP_ASSUM (X_CHOOSE_TAC (← q r"M:num")),
    STRIP_TAC,
    X_GEN_TAC (← q r"d:real"),
    STRIP_TAC,
    CLAIM (← q r"&0 <= &2 * d / k"),
    MATCH_MP_TAC REAL_LE_MUL,
    CONJ_TAC THENL [REAL_ARITH_TAC, ALL_TAC],
    MATCH_MP_TAC REAL_LE_DIV,
    CONJ_TAC THENL [FIRST_ASSUM MATCH_ACCEPT_TAC, ASM_MESON_TAC [REAL_LT_LE]],
    STRIP_TAC,
    LABEL_ALL_TAC,
    MOVE_TO_FRONT "Z-2",
    POP_ASSUM (fun x => USE_THEN "Z-0" (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y)))),
    DISCH_THEN (X_CHOOSE_TAC (← q r"K:num")),
    EXISTS_TAC (← q r"nmax M K"),
    REPEAT STRIP_TAC,
    CLAIM (← q r"M <= n /\ K <= (n:num)"),
    POP_ASSUM MP_TAC THEN REWRITE_TAC [nmax] THEN COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    RULE_ASSUM_TAC (REWRITE_RULE [GE]),
    FIRST_X_ASSUM (fun x => FIRST_X_ASSUM (fun y => tactic_of do pure (ASSUME_TAC (← MATCH_MP y x)))),
    FIRST_X_ASSUM (fun x => FIRST_X_ASSUM (fun y => tactic_of do pure (ASSUME_TAC (← MATCH_MP y x)))),
    RULE_ASSUM_TAC (REWRITE_RULE [real_div]),
    CASES_ON (← q r"k <= f n * inv (g n)"),
    MATCH_MP_TAC p1
    ]
    prove_by_refinement (
   (← q r"!k f g. &0 < k /\ (\n. f n / g n) --> k /\ mono_unbounded_above g
      ==> mono_unbounded_above f"),
    hd ++ tl)

  let mua_neg ← do
    -- the REAL_ARITHs of the theorem list, right to left
    let r2 ← REAL_ARITH (← q r"-- (-- x) = x")
    let r1 ← REAL_ARITH (← q r"x < y ==> --y < -- x")
    prove_by_refinement (
   (← q r"!f. mono_unbounded_above f = mono_unbounded_below (\n. -- (f n))"),
  /- {{{ Proof -/

  [
    MESON_TAC [mono_unbounded_above, mono_unbounded_below, r1, r2]
  ])

  /- }}} -/

  let mua_neg2 ← do
    let r2 ← REAL_ARITH (← q r"-- (-- x) = x")
    let r1 ← REAL_ARITH (← q r"x < y ==> --y < -- x")
    prove_by_refinement (
   (← q r"!f. mono_unbounded_below f = mono_unbounded_above (\n. -- (f n))"),
  /- {{{ Proof -/
  [
    MESON_TAC [mono_unbounded_above, mono_unbounded_below, r1, r2]
  ])
  /- }}} -/

  let mua_quotient_limit_neg ← prove_by_refinement (
   (← q r"!k f g. &0 < k /\ (\n. f n / g n) --> k /\ mono_unbounded_below g
      ==> mono_unbounded_below f"),
  /- {{{ Proof -/

  [
    REWRITE_TAC [mua_neg2],
    REPEAT STRIP_TAC,
    MATCH_MP_TAC (mua_quotient_limit),
    EXISTS_TAC (← q r"k"),
    EXISTS_TAC (← q r"\n. -- g n"),
    ASM_REWRITE_TAC [],
    POP_ASSUM (fun _x => ALL_TAC),
    POP_ASSUM MP_TAC,
    REWRITE_TAC [SEQ],
    DISCH_THEN (fun x => REPEAT STRIP_TAC THEN MP_TAC x),
    DISCH_THEN (MP_TAC o ISPEC (← q r"e:real")),
    ANTS_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    STRIP_TAC,
    EXISTS_TAC (← q r"N"),
    REPEAT STRIP_TAC,
    REWRITE_TAC [real_div, REAL_NEG_MUL2, REAL_INV_NEG],
    ASM_MESON_TAC [real_div]
  ])

  /- }}} -/

  -- @@RETURN BEGIN
  return { LIM_INV_1N, LIM_INV_CONST, LIM_INV_1NP, LIM_INV_CON, LIM_NN, LIM_NNC,
           LIM_MONO, LIM_POLY_LT, LIM_POLY, mono_inc, mono_dec, mono_inc_dec,
           mono_inc_pow, mono_inc_pow_const, mono_unbounded_above, mono_unbounded_below,
           mono_unbounded_above_pos, mono_unbounded_below_neg, mua_quotient_limit,
           mua_neg, mua_neg2, mua_quotient_limit_neg }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/-  Polynomial properties and the derivative (asym.ml 506-1171)            -/
/- ---------------------------------------------------------------------- -/

structure AsymPoly where
  -- @@FIELDS
  normal : thm
  nonconstant : thm
  NORMALIZE_SING : thm
  NORMALIZE_PAIR : thm
  POLY_NORMALIZE : thm
  NORMAL_CONS : thm
  NORMAL_TAIL : thm
  NORMAL_LAST_NONZERO : thm
  NORMAL_LENGTH : thm
  NORMAL_LAST_LENGTH : thm
  NORMAL_ID : thm
  LIM_POLY2 : thm
  POW_UNB : thm
  POW_UNB_CON : thm
  POW_UNBB_CON : thm
  POLY_SING : thm
  POLY_LAST_GT : thm
  POLY_LAST_LT : thm
  NORMALIZE_LENGTH_MONO : thm
  DEGREE_SING : thm
  DEGREE_CONS : thm
  PDA_LENGTH : thm
  POLY_DIFF_LENGTH : thm
  POLY_DIFF_SING : thm
  lem : thm
  NONCONSTANT_LENGTH : thm
  NONCONSTANT_DIFF_NIL : thm
  NONCONSTANT_DEGREE : thm
  POLY_DIFF_LAST_LEM : thm
  NONCONSTANT_DIFF_0 : thm
  POLY_DIFF_LAST_LT : thm
  POLY_DIFF_LAST_GT : thm
  NONCONSTANT_DIFF_NORMAL : thm
  PDIFF_POS_LAST : thm
  LAST_UNB : thm
  deriving Inhabited

@[nospecialize]
def setupAsymPoly [HolBase] (D : AsymDeps) (BAsymSeq : AsymSeq) :
    ExceptT String IO AsymPoly := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, CASES_ON, CLAIM, EXISTS_TAC,
        LIST_INDUCT_TAC, LIST_REWRITES, LIST_SIMP_TAC, MATCH_EQ_MP, MESON_TAC,
        REAL_ARITH, REAL_ARITH_TAC, REAL_REWRITES, REAL_SIMP_TAC, new_definition,
        prove_by_refinement, .. } := D
  let { AND_IMP_THM, CONS_11, FUN_EQ_THM, LAST, LAST_CONS, LAST_SING, LAST_TL, LENGTH,
        LENGTH_0, LENGTH_1, LENGTH_EQ_NIL, LENGTH_PAIR, LENGTH_TL, LE_REFL, LT_REFL,
        NOT_CONS_NIL, NOT_LE, PRE, REAL_ADD_LID, REAL_ARCH_SIMPLE, REAL_ARCH_SIMPLE_LT,
        REAL_ENTIRE, REAL_EQ_MUL_LCANCEL, REAL_LE, REAL_LET_TRANS, REAL_LE_LT,
        REAL_LE_TRANS, REAL_LT, REAL_LTE_TRANS, REAL_LT_INV, REAL_LT_LCANCEL_IMP,
        REAL_LT_LE, REAL_LT_MUL2, REAL_LT_TOTAL, REAL_MAX_MAX, REAL_MUL_ASSOC,
        REAL_MUL_GT, REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_LT, REAL_MUL_RZERO,
        REAL_OF_NUM_ADD, REAL_OF_NUM_EQ, REAL_OF_NUM_LT, REAL_POW_MONO, TL, TL_NIL,
        degree, list_CASES, nmax, normalize, poly, poly_diff, poly_diff_aux, .. } := D.core1
  let { LIM_POLY, mono_unbounded_above, mono_unbounded_below, mua_neg2,
        mua_quotient_limit, mua_quotient_limit_neg, .. } := BAsymSeq
  -- @@SCOPE END

  let normal ← new_definition (
   r"normal p <=> ((normalize p = p) /\ ~(p = []))")

  let nonconstant ← new_definition (
   r"nonconstant p <=> normal p /\ (!x. ~(p = [x]))")

  let NORMALIZE_SING ← prove_by_refinement (
    (← q r"!x. (normalize [x] = [x]) <=> ~(x = &0)"),
  /- {{{ Proof -/
  [
    MESON_TAC [NOT_CONS_NIL, normalize]
  ])
  /- }}} -/

  let NORMALIZE_PAIR ← prove_by_refinement (
    (← q r"!x y. ~(y = &0) <=> (normalize [x; y] = [x; y])"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [normalize, NOT_CONS_NIL],
    REPEAT GEN_TAC,
    COND_CASES_TAC,
    CLAIM (← q r"y = &0"),
    ASM_MESON_TAC (← deref LIST_REWRITES),
    DISCH_THEN SUBST1_TAC,
    ASM_MESON_TAC (← deref LIST_REWRITES),
    ASM_MESON_TAC (← deref LIST_REWRITES)
  ])
  /- }}} -/

  let POLY_NORMALIZE ← prove
   r"!p. poly (normalize p) = poly p"
  /- {{{ Proof -/
    (LIST_INDUCT_TAC THEN REWRITE_TAC [normalize, poly] THEN
    ASM_CASES_TAC (← q r"h = &0") THEN ASM_REWRITE_TAC [] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [poly, FUN_EQ_THM] THEN
    UNDISCH_TAC (← q r"poly (normalize t) = poly t") THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [poly] THEN
    REWRITE_TAC [REAL_MUL_RZERO, REAL_ADD_LID])
  /- }}} -/

  let NORMAL_CONS ← prove_by_refinement (
   (← q r"!h t. normal t ==> normal (CONS h t)"),
   /- {{{ Proof -/
  [
    REWRITE_TAC [normal, normalize],
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [],
    ASM_MESON_TAC [NOT_CONS_NIL]
  ])
  /- }}} -/

  let NORMAL_TAIL ← prove_by_refinement (
   (← q r"!h t. ~(t = []) /\ normal (CONS h t) ==> normal t"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [normal, normalize],
    REPEAT STRIP_TAC  THENL [ALL_TAC, ASM_MESON_TAC []],
    CASES_ON (← q r"normalize t = []"),
    ASM_MESON_TAC [NOT_CONS_NIL, CONS_11],
    ASM_MESON_TAC [NOT_CONS_NIL, CONS_11]
  ])
  /- }}} -/

  let NORMAL_LAST_NONZERO ← prove_by_refinement (
   (← q r"!p. normal p ==> ~(LAST p = &0)"),
  /- {{{ Proof -/

  [
    LIST_INDUCT_TAC,
    ASM_MESON_TAC [normal],
    CASES_ON (← q r"t = []"),
    ASM_REWRITE_TAC [normal, normalize, NOT_CONS_NIL, LAST],
    MESON_TAC [NOT_CONS_NIL],
    ASM_SIMP_TAC [← GSYM LAST_CONS],
    ASM_REWRITE_TAC [LAST, NOT_CONS_NIL],
    STRIP_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    MATCH_MP_TAC NORMAL_TAIL,
    ASM_MESON_TAC []
  ])

  /- }}} -/

  let NORMAL_LENGTH ← do
    let a1 ← ARITH_RULE (← q r"~(n = 0) <=> 0 < n")
    prove_by_refinement (
    (← q r"!p. normal p ==> 0 < LENGTH p"),
  /- {{{ Proof -/

  [
    MESON_TAC [normal, LENGTH_0, a1]
  ])

  /- }}} -/

  let NORMAL_LAST_LENGTH ← do
    let a1 ← ARITH_RULE (← q r"~(n = 0) <=> 0 < n")
    prove_by_refinement (
    (← q r"!p. 0 < LENGTH p /\ ~(LAST p = &0) ==> normal p"),
  /- {{{ Proof -/

  [
    LIST_INDUCT_TAC,
    MESON_TAC [LENGTH, LT_REFL],
    STRIP_TAC,
    CASES_ON (← q r"t = []"),
    ASM_REWRITE_TAC [normal, NORMALIZE_SING, NOT_CONS_NIL],
    ASM_MESON_TAC [LAST],
    MATCH_MP_TAC NORMAL_CONS,
    FIRST_ASSUM MATCH_MP_TAC,
    STRIP_TAC,
    ASM_MESON_TAC [LENGTH_0, a1],
    ASM_MESON_TAC [LAST_CONS]
  ])

  /- }}} -/

  let NORMAL_ID ← prove_by_refinement (
   (← q r"!p. normal p <=> 0 < LENGTH p /\ ~(LAST p = &0)"),
  /- {{{ Proof -/
  [
    MESON_TAC [NORMAL_LAST_LENGTH, NORMAL_LENGTH, NORMAL_LAST_NONZERO]
  ])
  /- }}} -/

  let LIM_POLY2 ← prove_by_refinement (
    (← q r"!p. normal p ==> (\n. poly p (&n) / (LAST p * &n pow (degree p))) --> &1"),
  /- {{{ Proof -/

  [
    REPEAT STRIP_TAC,
    REWRITE_TAC [degree],
    CLAIM (← q r"normalize p = p"),
    ASM_MESON_TAC [normal],
    DISCH_THEN SUBST1_TAC,
    MATCH_MP_TAC LIM_POLY,
    ASM_MESON_TAC [NORMAL_ID]
  ])

  /- }}} -/

  let POW_UNB ← do
    let r1 ← REAL_ARITH (← q r"x = x pow 1")
    prove_by_refinement (
    (← q r"!k. 0 < k ==> mono_unbounded_above (\n. (&n) pow k)"),
  /- {{{ Proof -/

  [
    REWRITE_TAC [mono_unbounded_above],
    REPEAT STRIP_TAC,
    MP_TAC (← ISPEC (← q r"max (&1) c") REAL_ARCH_SIMPLE_LT),
    STRIP_TAC,
    EXISTS_TAC (← q r"n"),
    REPEAT STRIP_TAC,
    MATCH_MP_TAC REAL_LTE_TRANS,
    EXISTS_TAC (← q r"&n"),
    CONJ_TAC,
    MATCH_MP_TAC REAL_LET_TRANS,
    EXISTS_TAC (← q r"max (&1) c"),
    ASM_MESON_TAC [REAL_MAX_MAX],
    MATCH_MP_TAC REAL_LE_TRANS,
    EXISTS_TAC (← q r"&n'"),
    STRIP_TAC,
    ASM_MESON_TAC [REAL_LE],
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [r1])),
    MATCH_MP_TAC REAL_POW_MONO,
    STRIP_TAC,
    MATCH_MP_TAC REAL_LE_TRANS,
    EXISTS_TAC (← q r"max (&1) c"),
    CONJ_TAC THENL [ASM_MESON_TAC [REAL_MAX_MAX], ALL_TAC],
    MATCH_MP_TAC REAL_LE_TRANS,
    EXISTS_TAC (← q r"&n"),
    ASM_MESON_TAC ((← deref REAL_REWRITES) ++ [REAL_LE, REAL_LT_LE]),
    EVERY_ASSUM MP_TAC THEN ARITH_TAC
  ])

  /- }}} -/

  let POW_UNB_CON ← prove_by_refinement (
    (← q r"!k a. 0 < k /\ &0 < a ==> mono_unbounded_above (\n. a * (&n) pow k)"),
  /- {{{ Proof -/

  [
    REWRITE_TAC [mono_unbounded_above, AND_IMP_THM],
    REPEAT STRIP_TAC,
    LABEL_ALL_TAC,
    MOVE_TO_FRONT "Z-1",
    POP_ASSUM (fun x => tactic_of do pure (MP_TAC (← MATCH_MP POW_UNB x))),
    REWRITE_TAC [mono_unbounded_above],
    DISCH_THEN (MP_TAC o ISPEC (← q r"inv a * c")),
    STRIP_TAC,
    EXISTS_TAC (← q r"N"),
    STRIP_TAC,
    DISCH_THEN (fun x => POP_ASSUM (fun y => tactic_of do pure (ASSUME_TAC (← MATCH_MP y x)))),
    CLAIM (← q r"inv a * a = &1"),
    MATCH_MP_TAC REAL_MUL_LINV,
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    STRIP_TAC,
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP,
    EXISTS_TAC (← q r"inv a"),
    CONJ_TAC,
    ASM_MESON_TAC [REAL_LT_INV],
    ASM_REWRITE_TAC [REAL_MUL_ASSOC, REAL_MUL_LID]
  ])

  /- }}} -/

  let POW_UNBB_CON ← do
    let a1 ← ARITH_RULE (← q r"--(x * y) = -- x * y")
    prove_by_refinement (
    (← q r"!k a. 0 < k /\ a < &0 ==> mono_unbounded_below (\n. a * (&n) pow k)"),
  /- {{{ Proof -/

  [
    REWRITE_TAC [mua_neg2, a1],
    REPEAT STRIP_TAC,
    MATCH_MP_TAC POW_UNB_CON,
    STRIP_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC
  ])

  /- }}} -/

  let POLY_SING ← prove_by_refinement (
    (← q r"!x y. poly [x] y = x"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [poly],
    REAL_ARITH_TAC
  ])
  /- }}} -/

  let POLY_LAST_GT ← do
    let a1 ← ARITH_RULE (← q r"~(x < y /\ y < x)")
    prove_by_refinement (
    (← q r"!p. normal p /\ (?X. !x. X < x ==> &0 < poly p x) ==> &0 < LAST p"),
  /- {{{ Proof -/

  [
    GEN_TAC,
    CASES_ON (← q r"LENGTH p = 1"),
    RULE_ASSUM_TAC (REWRITE_RULE [LENGTH_1]),
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    ASM_REWRITE_TAC [LAST_SING, POLY_SING],
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    EXISTS_TAC (← q r"X + &1"),
    REAL_ARITH_TAC,
    /-  -/
    REWRITE_TAC [AND_IMP_THM],
    DISCH_THEN (fun x => tactic_of do pure (MP_TAC (← MATCH_MP LIM_POLY2 x) THEN ASSUME_TAC x)),
    REPEAT STRIP_TAC,
    DISJ_CASES_TAC (← ISPECL [← q r"&0", ← q r"LAST (p:real list)"] REAL_LT_TOTAL),
    ASM_MESON_TAC [NORMAL_ID],
    POP_ASSUM DISJ_CASES_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    /- save -/
    CLAIM (← q r"mono_unbounded_below (\n. LAST p * &n pow degree p)"),
    MATCH_MP_TAC POW_UNBB_CON,
    REWRITE_TAC [degree],
    CONJ_TAC THENL [ALL_TAC, FIRST_ASSUM MATCH_ACCEPT_TAC],
    CLAIM (← q r"normalize p = p"),
    ASM_MESON_TAC [normal],
    DISCH_THEN SUBST1_TAC,
    CLAIM (← q r"~(LENGTH p = 0)"),
    ASM_MESON_TAC [normal, LENGTH_EQ_NIL],
    LABEL_ALL_TAC,
    USE_THEN "Z-4" MP_TAC,
    ARITH_TAC,
    /- save -/
    STRIP_TAC,
    CLAIM (← q r"mono_unbounded_below (\n. poly p (&n))"),
    MATCH_MP_TAC mua_quotient_limit_neg,
    BETA_TAC,
    EXISTS_TAC (← q r"&1"),
    EXISTS_TAC (← q r"(\n. LAST p * &n pow degree p)"),
    REPEAT STRIP_TAC,
    REAL_ARITH_TAC,
    BETA_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    REWRITE_TAC [mono_unbounded_below],
    DISCH_THEN (MP_TAC o ISPEC (← q r"&0")),
    STRIP_TAC,
    LABEL_ALL_TAC,
    USE_THEN "Z-3" MP_TAC,
    POP_ASSUM MP_TAC,
    POP_ASSUM_LIST (fun _x => ALL_TAC),
    MP_TAC (← ISPEC (← q r"X:real") REAL_ARCH_SIMPLE),
    STRIP_TAC,
    DISCH_THEN (ASSUME_TAC o ISPEC (← q r"1 + nmax N n")),
    DISCH_THEN (ASSUME_TAC o ISPEC (← q r"&1 + &(nmax N n)")),
    POP_ASSUM MP_TAC THEN ANTS_TAC,
    REWRITE_TAC [nmax],
    COND_CASES_TAC,
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    RULE_ASSUM_TAC (REWRITE_RULE [NOT_LE, ← GSYM REAL_LT]),
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    POP_ASSUM MP_TAC THEN ANTS_TAC,
    REWRITE_TAC [nmax],
    ARITH_TAC,
    ASM_MESON_TAC [a1, ← GSYM REAL_OF_NUM_ADD]
  ])

  /- }}} -/

  let POLY_LAST_LT ← do
    let a1 ← ARITH_RULE (← q r"~(x < y /\ y < x)")
    prove_by_refinement (
    (← q r"!p. normal p /\ (?X. !x. X < x ==> poly p x < &0) ==> LAST p < &0"),
  /- {{{ Proof -/

  [
    GEN_TAC,
    CASES_ON (← q r"LENGTH p = 1"),
    RULE_ASSUM_TAC (REWRITE_RULE [LENGTH_1]),
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    ASM_REWRITE_TAC [LAST_SING, POLY_SING],
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    EXISTS_TAC (← q r"X + &1"),
    REAL_ARITH_TAC,
    /-  -/
    REWRITE_TAC [AND_IMP_THM],
    DISCH_THEN (fun x => tactic_of do pure (MP_TAC (← MATCH_MP LIM_POLY2 x) THEN ASSUME_TAC x)),
    REPEAT STRIP_TAC,
    DISJ_CASES_TAC (← ISPECL [← q r"&0", ← q r"LAST (p:real list)"] REAL_LT_TOTAL),
    ASM_MESON_TAC [NORMAL_ID],
    POP_ASSUM DISJ_CASES_TAC THENL [ALL_TAC, FIRST_ASSUM MATCH_ACCEPT_TAC],
    /- save -/
    CLAIM (← q r"mono_unbounded_above (\n. LAST p * &n pow degree p)"),
    MATCH_MP_TAC POW_UNB_CON,
    REWRITE_TAC [degree],
    CONJ_TAC THENL [ALL_TAC, FIRST_ASSUM MATCH_ACCEPT_TAC],
    CLAIM (← q r"normalize p = p"),
    ASM_MESON_TAC [normal],
    DISCH_THEN SUBST1_TAC,
    CLAIM (← q r"~(LENGTH p = 0)"),
    ASM_MESON_TAC [normal, LENGTH_EQ_NIL],
    LABEL_ALL_TAC,
    USE_THEN "Z-4" MP_TAC,
    ARITH_TAC,
    /- save -/
    STRIP_TAC,
    CLAIM (← q r"mono_unbounded_above (\n. poly p (&n))"),
    MATCH_MP_TAC mua_quotient_limit,
    BETA_TAC,
    EXISTS_TAC (← q r"&1"),
    EXISTS_TAC (← q r"(\n. LAST p * &n pow degree p)"),
    REPEAT STRIP_TAC,
    REAL_ARITH_TAC,
    BETA_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    REWRITE_TAC [mono_unbounded_above],
    DISCH_THEN (MP_TAC o ISPEC (← q r"&0")),
    STRIP_TAC,
    LABEL_ALL_TAC,
    USE_THEN "Z-3" MP_TAC,
    POP_ASSUM MP_TAC,
    POP_ASSUM_LIST (fun _x => ALL_TAC),
    MP_TAC (← ISPEC (← q r"X:real") REAL_ARCH_SIMPLE),
    STRIP_TAC,
    DISCH_THEN (ASSUME_TAC o ISPEC (← q r"1 + nmax N n")),
    DISCH_THEN (ASSUME_TAC o ISPEC (← q r"&1 + &(nmax N n)")),
    POP_ASSUM MP_TAC THEN ANTS_TAC,
    REWRITE_TAC [nmax],
    COND_CASES_TAC,
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    RULE_ASSUM_TAC (REWRITE_RULE [NOT_LE, ← GSYM REAL_LT]),
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    POP_ASSUM MP_TAC THEN ANTS_TAC,
    REWRITE_TAC [nmax],
    ARITH_TAC,
    ASM_MESON_TAC [a1, ← GSYM REAL_OF_NUM_ADD]
  ])

  /- }}} -/

  let NORMALIZE_LENGTH_MONO ← prove_by_refinement (
    (← q r"!l. LENGTH (normalize l) <= LENGTH l"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    MESON_TAC [normalize, LE_REFL],
    REWRITE_TAC [LENGTH, normalize],
    REPEAT COND_CASES_TAC THEN REWRITE_TAC [LENGTH] THEN EVERY_ASSUM MP_TAC THEN ARITH_TAC
  ])
  /- }}} -/

  let DEGREE_SING ← prove_by_refinement (
    (← q r"!x. (degree [x] = 0)"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [degree],
    STRIP_TAC,
    CASES_ON (← q r"x = &0"),
    ASM_REWRITE_TAC [normalize, LENGTH],
    ARITH_TAC,
    CLAIM (← q r"normalize [x] = [x]"),
    ASM_MESON_TAC [NORMALIZE_SING],
    DISCH_THEN SUBST1_TAC,
    REWRITE_TAC [LENGTH],
    ARITH_TAC
  ])
  /- }}} -/

  let DEGREE_CONS ← prove_by_refinement (
    (← q r"!h t. normal t ==> (degree (CONS h t) = 1 + degree t)"),
  /- {{{ Proof -/

  [
    REPEAT STRIP_TAC,
    CLAIM (← q r"normal (CONS h t)"),
    ASM_MESON_TAC [NORMAL_CONS],
    REWRITE_TAC [normal, degree],
    STRIP_TAC,
    ASM_REWRITE_TAC [],
    RULE_ASSUM_TAC (REWRITE_RULE [normal]),
    CLAIM (← q r"~(LENGTH t = 0)"),
    ASM_MESON_TAC [LENGTH_0],
    STRIP_TAC,
    ASM_REWRITE_TAC [LENGTH],
    POP_ASSUM MP_TAC THEN ARITH_TAC
  ])

  /- }}} -/

  /- ---------------------------------------------------------------------- -/
  /-  Now the derivative                                                    -/
  /- ---------------------------------------------------------------------- -/

  let PDA_LENGTH ← prove_by_refinement (
   (← q r"!p n. ~(p = []) ==> (LENGTH(poly_diff_aux n p) = LENGTH p)"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [],
    GEN_TAC THEN DISCH_THEN IGNORE,
    REWRITE_TAC [LENGTH, poly_diff_aux],
    CASES_ON (← q r"t = []"),
    ASM_REWRITE_TAC [LENGTH, poly_diff_aux],
    ASM_MESON_TAC []
  ])
  /- }}} -/

  let POLY_DIFF_LENGTH ← prove_by_refinement (
   (← q r"!p. LENGTH (poly_diff p) = PRE (LENGTH p)"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [poly_diff, LENGTH, PRE],
    CASES_ON (← q r"t = []"),
    ASM_REWRITE_TAC [LENGTH, PRE],
    REWRITE_TAC [poly_diff, NOT_CONS_NIL, TL, PRE, poly_diff_aux, LENGTH],
    REWRITE_TAC [poly_diff, TL, LENGTH, PRE, NOT_CONS_NIL],
    MATCH_MP_TAC PDA_LENGTH,
    FIRST_ASSUM MATCH_ACCEPT_TAC
  ])
  /- }}} -/

  let POLY_DIFF_SING ← do
    -- the ARITH_RULEs of the tactic list, right to left
    let a2 ← ARITH_RULE (← q r"SUC 0 = 1")
    let a1 ← ARITH_RULE (← q r"!n. (n = 0) \/ (n = 1) \/ (n = 2) \/ 2 < n")
    prove_by_refinement (
   (← q r"!p h. (poly_diff p = [h]) <=> ?x. p = [x; h]"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    DISJ_CASES_TAC (← ISPEC (← q r"LENGTH (p:real list)") a1),
    ASM_MESON_TAC [poly_diff, LENGTH_0, NOT_CONS_NIL],
    POP_ASSUM DISJ_CASES_TAC,
    RULE_ASSUM_TAC (REWRITE_RULE [LENGTH_1]),
    POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM SUBST1_TAC,
    REWRITE_TAC [poly_diff, NOT_CONS_NIL, TL, poly_diff_aux],
    ASM_MESON_TAC (← deref LIST_REWRITES),
    POP_ASSUM DISJ_CASES_TAC,
    RULE_ASSUM_TAC (MATCH_EQ_MP LENGTH_PAIR),
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    ASM_REWRITE_TAC [poly_diff, NOT_CONS_NIL, TL, poly_diff_aux, REAL_MUL_LID],
    ASM_MESON_TAC [CONS_11],
    EQ_TAC,
    STRIP_TAC,
    POP_ASSUM (ASSUME_TAC o (AP_TERM (← q r"LENGTH:((real) list) -> num"))),
    RULE_ASSUM_TAC (REWRITE_RULE [LENGTH]),
    CLAIM (← q r"PRE (LENGTH p) = 1"),
    ASM_MESON_TAC [POLY_DIFF_LENGTH, a2],
    STRIP_TAC,
    CLAIM (← q r"LENGTH p = 2"),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    ASM_MESON_TAC [LT_REFL],
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [],
    REWRITE_TAC [poly_diff, NOT_CONS_NIL, TL, poly_diff_aux, REAL_MUL_LID]
  ])
  /- }}} -/

  -- asym.ml's `lem`, which rebinds rqe_tactics_ext.ml's
  let lem ← prove_by_refinement (
    (← q r"!p n. ~(p = []) ==> (LAST (poly_diff_aux n p) = LAST p * &(PRE(LENGTH p) + n))"),
  /- {{{ Proof -/

  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [],
    REPEAT STRIP_TAC,
    POP_ASSUM IGNORE,
    REWRITE_TAC [LENGTH, poly_diff_aux],
    CASES_ON (← q r"t = []"),
    ASM_REWRITE_TAC [poly_diff_aux, LAST, LENGTH, ← GSYM REAL_OF_NUM_ADD],
    CLAIM (← q r"((SUC 0) - 1) + n = n"),
    ARITH_TAC,
    DISCH_THEN SUBST1_TAC,
    REWRITE_TAC [PRE],
    REAL_ARITH_TAC,
    POP_ASSUM (fun x => FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))) THEN ASSUME_TAC x),
    STRIP_TAC,
    ASM_REWRITE_TAC [],
    LIST_SIMP_TAC,
    ASM_REWRITE_TAC [],
    COND_CASES_TAC,
    REWRITE_TAC [PRE],
    ASM_MESON_TAC [PDA_LENGTH, LENGTH, LENGTH_0],
    REWRITE_TAC [PRE],
    MATCH_EQ_MP_TAC (← GSYM REAL_EQ_MUL_LCANCEL),
    DISJ2_TAC,
    AP_TERM_TAC,
    CLAIM (← q r"~(LENGTH t = 0)"),
    ASM_MESON_TAC [LENGTH_0],
    ARITH_TAC
  ])

  /- }}} -/

  let NONCONSTANT_LENGTH ← do
    let a1 ← ARITH_RULE (← q r"(x = 0) \/ (x = 1) \/ 1 < x")
    prove_by_refinement (
    (← q r"!p. nonconstant p ==> 1 < LENGTH p"),
  /- {{{ Proof -/

  [
    REWRITE_TAC [nonconstant, normal],
    ASM_MESON_TAC [LENGTH_0, LENGTH_1, a1]
  ])

  /- }}} -/

  let NONCONSTANT_DIFF_NIL ← prove_by_refinement (
    (← q r"!p. nonconstant p ==> ~(poly_diff p = [])"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    CLAIM (← q r"1 < LENGTH p"),
    ASM_MESON_TAC [NONCONSTANT_LENGTH],
    STRIP_TAC,
    CLAIM (← q r"0 < LENGTH (poly_diff p)"),
    REWRITE_TAC [POLY_DIFF_LENGTH],
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    ASM_REWRITE_TAC [LENGTH],
    ARITH_TAC
  ])
  /- }}} -/

  let NONCONSTANT_DEGREE ← prove_by_refinement (
    (← q r"!p. nonconstant p ==> 0 < degree p"),
  /- {{{ Proof -/
  [
    GEN_TAC,
    DISCH_THEN (fun x => ASSUME_TAC x THEN MP_TAC x),
    REWRITE_TAC [nonconstant, degree],
    REPEAT STRIP_TAC,
    CLAIM (← q r"normalize p = p"),
    ASM_MESON_TAC [normal],
    STRIP_TAC,
    ASM_REWRITE_TAC [],
    CLAIM (← q r"1 < LENGTH p"),
    ASM_MESON_TAC [NONCONSTANT_LENGTH],
    ARITH_TAC
  ])
  /- }}} -/

  let POLY_DIFF_LAST_LEM ← prove_by_refinement (
    (← q r"!p. nonconstant p ==> (LAST (poly_diff p) = LAST p * &(degree p))"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [nonconstant, poly_diff],
    REPEAT STRIP_TAC,
    COND_CASES_TAC,
    ASM_MESON_TAC [normal],
    CLAIM (← q r"~(TL p = [])"),
    ASM_MESON_TAC [TL, NOT_CONS_NIL, list_CASES, TL_NIL],
    DISCH_THEN (fun x => tactic_of do pure (MP_TAC (← MATCH_MP lem x) THEN ASSUME_TAC x)),
    DISCH_THEN (ASSUME_TAC o ISPEC (← q r"1")),
    ASM_REWRITE_TAC [],
    CLAIM (← q r"LAST (TL p) = LAST p"),
    ASM_MESON_TAC [LAST_TL],
    DISCH_THEN SUBST1_TAC,
    REWRITE_TAC [degree],
    CLAIM (← q r"normalize p = p"),
    ASM_MESON_TAC [normal],
    DISCH_THEN SUBST1_TAC,
    MATCH_EQ_MP_TAC (← GSYM REAL_EQ_MUL_LCANCEL),
    DISJ2_TAC,
    AP_TERM_TAC,
    ASM_SIMP_TAC [LENGTH_TL],
    CLAIM (← q r"~(LENGTH p = 0)"),
    ASM_MESON_TAC [LENGTH_0],
    CLAIM (← q r"~(LENGTH p = 1)"),
    ASM_MESON_TAC [LENGTH_1],
    ARITH_TAC
  ])
  /- }}} -/

  let NONCONSTANT_DIFF_0 ← prove_by_refinement (
    (← q r"!p. nonconstant p ==> ~(poly_diff p = [&0])"),
  /- {{{ Proof -/

  [
    STRIP_TAC,
    DISCH_THEN (fun x => MP_TAC x THEN ASSUME_TAC x),
    REWRITE_TAC [nonconstant],
    REPEAT STRIP_TAC,
    CLAIM (← q r"~(p = [])"),
    ASM_MESON_TAC [normal],
    DISCH_THEN (fun x => RULE_ASSUM_TAC (REWRITE_RULE [x]) THEN ASSUME_TAC x),
    CLAIM (← q r"~(LAST p = &0)"),
    MATCH_MP_TAC NORMAL_LAST_NONZERO,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    STRIP_TAC,
    CLAIM (← q r"LAST p * &(degree p) = &0"),
    ASM_SIMP_TAC [← GSYM POLY_DIFF_LAST_LEM],
    REWRITE_TAC [LAST],
    STRIP_TAC,
    CLAIM (← q r"(LAST p = &0) \/ (&(degree p) = &0)"),
    ASM_MESON_TAC [REAL_ENTIRE],
    STRIP_TAC,
    ASM_MESON_TAC [],
    CLAIM (← q r"?h t. p = CONS h t"),
    ASM_MESON_TAC [list_CASES],
    STRIP_TAC,
    CLAIM (← q r"normal t"),
    ASM_MESON_TAC [NORMAL_TAIL],
    STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP (← ISPECL [← q r"h:real", ← q r"t:real list"] DEGREE_CONS))),
    STRIP_TAC,
    CLAIM (← q r"degree p = 0"),
    ASM_MESON_TAC [REAL_OF_NUM_EQ],
    ASM_REWRITE_TAC [],
    ARITH_TAC
  ])

  /- }}} -/

  let POLY_DIFF_LAST_LT ← prove_by_refinement (
   (← q r"!p. nonconstant p ==> (LAST (poly_diff p) < &0 <=> LAST p < &0)"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    ASM_SIMP_TAC [POLY_DIFF_LAST_LEM],
    CLAIM (← q r"&0 <= &(degree p)"),
    REAL_ARITH_TAC,
    STRIP_TAC,
    EQ_TAC,
    ASM_MESON_TAC ([REAL_MUL_LT] ++ (← deref REAL_REWRITES)),
    STRIP_TAC,
    CLAIM (← q r"0 < degree p"),
    ASM_MESON_TAC [NONCONSTANT_DEGREE],
    STRIP_TAC,
    CLAIM (← q r"&0 < &(degree p)"),
    REAL_SIMP_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    STRIP_TAC,
    MATCH_EQ_MP_TAC (← GSYM REAL_MUL_LT),
    ASM_REWRITE_TAC []
  ])
  /- }}} -/

  let POLY_DIFF_LAST_GT ← do
    let a1 ← ARITH_RULE (← q r"&0 = &0 * &0")
    prove_by_refinement (
   (← q r"!p. nonconstant p ==> (&0 < LAST (poly_diff p) <=> &0 < LAST p)"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    ASM_SIMP_TAC [POLY_DIFF_LAST_LEM],
    CLAIM (← q r"&0 < &(degree p)"),
    ASM_MESON_TAC [NONCONSTANT_DEGREE, REAL_OF_NUM_LT],
    STRIP_TAC,
    EQ_TAC,
    REWRITE_TAC [REAL_MUL_GT],
    STRIP_TAC,
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    STRIP_TAC,
    ONCE_REWRITE_TAC [a1],
    MATCH_MP_TAC REAL_LT_MUL2,
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC
  ])
  /- }}} -/

  let NONCONSTANT_DIFF_NORMAL ← prove_by_refinement (
    (← q r"!p. nonconstant p ==> normal (poly_diff p)"),
  /- {{{ Proof -/
  [
    GEN_TAC,
    DISCH_THEN (fun x =>  ASSUME_TAC x THEN MP_TAC x),
    REWRITE_TAC [nonconstant],
    REPEAT STRIP_TAC,
    MATCH_MP_TAC NORMAL_LAST_LENGTH,
    STRIP_TAC,
    CLAIM (← q r"1 < LENGTH p"),
    ASM_MESON_TAC [NONCONSTANT_LENGTH],
    STRIP_TAC,
    CLAIM (← q r"LENGTH (poly_diff p) = PRE (LENGTH p)"),
    ASM_MESON_TAC [POLY_DIFF_LENGTH],
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    CASES_ON (← q r"LAST p < &0"),
    CLAIM (← q r"LAST (poly_diff p) < &0"),
    ASM_MESON_TAC [POLY_DIFF_LAST_LT],
    ASM_REWRITE_TAC [],
    REAL_ARITH_TAC,
    REWRITE_ASSUMS (← deref REAL_REWRITES),
    REWRITE_ASSUMS [REAL_LE_LT],
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    CLAIM (← q r"&0 < LAST (poly_diff p)"),
    ASM_MESON_TAC [POLY_DIFF_LAST_GT],
    ASM_REWRITE_TAC [],
    REAL_ARITH_TAC,
    ASM_MESON_TAC [NORMAL_ID]
  ])
  /- }}} -/

  let PDIFF_POS_LAST ← prove_by_refinement (
    (← q r"!p. nonconstant p /\ (?X. !x. X < x ==> &0 < poly (poly_diff p) x) ==> &0 < LAST p"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    CLAIM (← q r"&0 < LAST (poly_diff p)"),
    MATCH_MP_TAC POLY_LAST_GT,
    ASM_SIMP_TAC [NONCONSTANT_DIFF_NORMAL],
    ASM_MESON_TAC [],
    STRIP_TAC,
    ASM_SIMP_TAC [← GSYM POLY_DIFF_LAST_GT]
  ])
  /- }}} -/

  let LAST_UNB ← prove_by_refinement (
   (← q r"!p. nonconstant p /\ &0 < LAST p ==> mono_unbounded_above (\n. poly p (&n))"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    MATCH_MP_TAC mua_quotient_limit,
    EXISTS_TAC (← q r"&1"),
    EXISTS_TAC (← q r"(\n. (LAST p) * (&n) pow (degree p))"),
    BETA_TAC,
    STRIP_TAC,
    REAL_ARITH_TAC,
    STRIP_TAC,
    MATCH_MP_TAC LIM_POLY2,
    ASM_MESON_TAC [nonconstant],
    MATCH_MP_TAC POW_UNB_CON,
    ASM_REWRITE_TAC [],
    ASM_MESON_TAC [NONCONSTANT_DEGREE]
  ])
  /- }}} -/

  -- @@RETURN BEGIN
  return { normal, nonconstant, NORMALIZE_SING, NORMALIZE_PAIR, POLY_NORMALIZE,
           NORMAL_CONS, NORMAL_TAIL, NORMAL_LAST_NONZERO, NORMAL_LENGTH,
           NORMAL_LAST_LENGTH, NORMAL_ID, LIM_POLY2, POW_UNB, POW_UNB_CON, POW_UNBB_CON,
           POLY_SING, POLY_LAST_GT, POLY_LAST_LT, NORMALIZE_LENGTH_MONO, DEGREE_SING,
           DEGREE_CONS, PDA_LENGTH, POLY_DIFF_LENGTH, POLY_DIFF_SING, lem,
           NONCONSTANT_LENGTH, NONCONSTANT_DIFF_NIL, NONCONSTANT_DEGREE,
           POLY_DIFF_LAST_LEM, NONCONSTANT_DIFF_0, POLY_DIFF_LAST_LT, POLY_DIFF_LAST_GT,
           NONCONSTANT_DIFF_NORMAL, PDIFF_POS_LAST, LAST_UNB }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/-  The positive and negative theorems, products of unbounded sequences,  -/
/-  and a polynomial applied to a negative argument (asym.ml 1172-1925)    -/
/- ---------------------------------------------------------------------- -/

structure AsymUnb where
  -- @@FIELDS
  POLY_DIFF_UP_RIGHT : thm
  PDIFF_NEG_LAST : thm
  LAST_UNB_NEG : thm
  POLY_DIFF_DOWN_RIGHT : thm
  UNB_LEFT_EVEN : thm
  UNB_LEFT_ODD : thm
  EVEN_CONS : thm
  ODD_CONS : thm
  MUA_DIV_CONST : thm
  SEQ_0_NEG : thm
  lem : thm
  MUB_DIV_CONST : thm
  mono_unbounded : thm
  MU_DIV_CONST : thm
  MUA_MUA : thm
  MUA_MUB : thm
  MUB_MUA : thm
  MUB_MUB : thm
  MU_PROD : thm
  mub_quotient_limit : thm
  POLY_UB : thm
  pneg_aux : thm
  pneg : thm
  POLY_PNEG_AUX_SUC : thm
  POLY_NEG_NEG : thm
  POLY_PNEG_NEG : thm
  POLY_PNEG_AUX : thm
  POLY_PNEG : thm
  DEGREE_0 : thm
  EVEN_ODD : thm
  ODD_EVEN : thm
  deriving Inhabited

@[nospecialize]
def setupAsymUnb [HolBase] (D : AsymDeps) (BAsymSeq : AsymSeq) (BAsymPoly : AsymPoly) :
    ExceptT String IO AsymUnb := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, CASES_ON, CCONTR_TAC, CLAIM, EXISTS_TAC,
        LIST_INDUCT_TAC, MESON_TAC, NUM_REWRITES, REAL_ARITH, REAL_ARITH_TAC,
        REAL_REWRITES, REAL_SIMP_TAC, REAL_SOLVE_TAC, new_definition,
        new_recursive_definition, prove_by_refinement, .. } := D
  let { ABS_0, ETA_AX, EVEN, LENGTH, LENGTH_SING, NOT_EVEN, NOT_ODD, ODD, ONE,
        POLY_MVT, POLY_NEG, REAL_ABS_DIV, REAL_ABS_NEG, REAL_ABS_NZ, REAL_ABS_REFL,
        REAL_ARCH_SIMPLE_LT, REAL_DIV_DENOM_LT, REAL_INV_NEG, REAL_INV_NZ,
        REAL_INV_POS, REAL_LET_TRANS, REAL_LE_LCANCEL_IMP, REAL_LE_LT, REAL_LE_MUL2,
        REAL_LE_RCANCEL_IMP, REAL_LTE_TRANS, REAL_LT_LE, REAL_LT_MUL, REAL_LT_MUL2,
        REAL_LT_TRANS, REAL_MAX_MAX, REAL_MUL_ASSOC, REAL_MUL_LINV, REAL_MUL_LT,
        REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RINV, REAL_MUL_SYM, REAL_NEG_DIV,
        REAL_NOT_LT, REAL_OF_NUM_LT, REAL_POW_NEG, SEQ, degree, list_RECURSION, nmax,
        normalize, poly, poly_cmul, poly_neg, pow, real_div, real_max, .. } := D.core1
  let { mono_unbounded_above, mono_unbounded_above_pos, mono_unbounded_below, mua_neg,
        mua_neg2, mua_quotient_limit, mua_quotient_limit_neg, .. } := BAsymSeq
  let { LAST_UNB, LIM_POLY2, NONCONSTANT_DEGREE, NONCONSTANT_DIFF_NORMAL,
        NORMAL_LAST_NONZERO, PDIFF_POS_LAST, POLY_DIFF_LAST_LT, POLY_LAST_LT, POW_UNB,
        POW_UNBB_CON, POW_UNB_CON, nonconstant, .. } := BAsymPoly
  -- @@SCOPE END

  /- ---------------------------------------------------------------------- -/
  /-  Finally, the positive theorems                                        -/
  /- ---------------------------------------------------------------------- -/


  let POLY_DIFF_UP_RIGHT ← do
    -- the rules of the tactic list, right to left
    let a2 ← ARITH_RULE (← q r"&0 = &0 * &0")
    let r1 ← REAL_ARITH (← q r"x <= &0 /\ &0 < y ==> x - y <= &0")
    prove_by_refinement (
   (← q r"nonconstant p /\ (?X. !x. X < x ==> &0 < poly (poly_diff p) x) ==>
     (?Y. !y. Y < y ==> &0 < poly p y)"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    CLAIM (← q r"mono_unbounded_above (\n. poly p (&n))"),
    MATCH_MP_TAC LAST_UNB,
    ASM_MESON_TAC [PDIFF_POS_LAST],
    REWRITE_TAC [mono_unbounded_above],
    DISCH_THEN (MP_TAC o (ISPEC (← q r"&0"))),
    STRIP_TAC,
    CLAIM (← q r"?K. max X (&N) < &K"),
    ASM_MESON_TAC [REAL_ARCH_SIMPLE_LT],
    STRIP_TAC,
    EXISTS_TAC (← q r"&K"),
    REPEAT STRIP_TAC,
    CCONTR_TAC,
    REWRITE_ASSUMS [REAL_NOT_LT],
    CLAIM (← q r"&N < y /\ X < y"),
    ASM_MESON_TAC ([REAL_MAX_MAX] ++ (← deref REAL_REWRITES)),
    REPEAT STRIP_TAC,
    MP_TAC (← ISPECL [← q r"p:real list", ← q r"&K", ← q r"y:real"] POLY_MVT),
    ANTS_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    STRIP_TAC,
    CLAIM (← q r"poly p y - poly p (&K) <= &0"),
    MATCH_MP_TAC r1,
    ASM_REWRITE_TAC [],
    FIRST_ASSUM MATCH_MP_TAC,
    CLAIM (← q r"&N < &K"),
    ASM_MESON_TAC [REAL_MAX_MAX, REAL_LET_TRANS],
    STRIP_TAC,
    CLAIM (← q r"N:num < K"),
    ASM_MESON_TAC [REAL_OF_NUM_LT],
    ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"&0 < y - &K"),
    LABEL_ALL_TAC,
    USE_THEN "Z-7" MP_TAC,
    REAL_ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"&0 < poly (poly_diff p) x"),
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [REAL_MAX_MAX, REAL_LET_TRANS, REAL_LT_TRANS],
    STRIP_TAC,
    CLAIM (← q r"&0 < (y - &K) * poly (poly_diff p) x"),
    ONCE_REWRITE_TAC [a2],
    MATCH_MP_TAC REAL_LT_MUL2 THEN REPEAT STRIP_TAC THEN TRY REAL_ARITH_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC,
    STRIP_TAC,
    REAL_SOLVE_TAC
  ])
  /- }}} -/

  let PDIFF_NEG_LAST ← prove_by_refinement (
    (← q r"!p. nonconstant p /\ (?X. !x. X < x ==> poly (poly_diff p) x < &0) ==> LAST p < &0"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    CLAIM (← q r"LAST (poly_diff p) < &0"),
    MATCH_MP_TAC POLY_LAST_LT,
    ASM_SIMP_TAC [NONCONSTANT_DIFF_NORMAL],
    ASM_MESON_TAC [],
    STRIP_TAC,
    ASM_SIMP_TAC [← GSYM POLY_DIFF_LAST_LT]
  ])
  /- }}} -/

  let LAST_UNB_NEG ← prove_by_refinement (
   (← q r"!p. nonconstant p /\ LAST p < &0 ==> mono_unbounded_below (\n. poly p (&n))"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    MATCH_MP_TAC mua_quotient_limit_neg,
    EXISTS_TAC (← q r"&1"),
    EXISTS_TAC (← q r"(\n. (LAST p) * (&n) pow (degree p))"),
    BETA_TAC,
    STRIP_TAC,
    REAL_ARITH_TAC,
    STRIP_TAC,
    MATCH_MP_TAC LIM_POLY2,
    ASM_MESON_TAC [nonconstant],
    MATCH_MP_TAC POW_UNBB_CON,
    ASM_REWRITE_TAC [],
    ASM_MESON_TAC [NONCONSTANT_DEGREE]
  ])
  /- }}} -/

  let POLY_DIFF_DOWN_RIGHT ← do
    let r1 ← REAL_ARITH (← q r"&0 <= x /\ y < &0 ==> &0 <= x - y")
    prove_by_refinement (
   (← q r"nonconstant p /\ (?X. !x. X < x ==> poly (poly_diff p) x < &0) ==>
     (?Y. !y. Y < y ==> poly p y < &0)"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    CLAIM (← q r"mono_unbounded_below (\n. poly p (&n))"),
    MATCH_MP_TAC LAST_UNB_NEG,
    ASM_MESON_TAC [PDIFF_NEG_LAST],
    REWRITE_TAC [mono_unbounded_below],
    DISCH_THEN (MP_TAC o (ISPEC (← q r"&0"))),
    STRIP_TAC,
    CLAIM (← q r"?K. max X (&N) < &K"),
    ASM_MESON_TAC [REAL_ARCH_SIMPLE_LT],
    STRIP_TAC,
    EXISTS_TAC (← q r"&K"),
    REPEAT STRIP_TAC,
    CCONTR_TAC,
    REWRITE_ASSUMS [REAL_NOT_LT],
    CLAIM (← q r"&N < y /\ X < y"),
    ASM_MESON_TAC ([REAL_MAX_MAX] ++ (← deref REAL_REWRITES)),
    REPEAT STRIP_TAC,
    MP_TAC (← ISPECL [← q r"p:real list", ← q r"&K", ← q r"y:real"] POLY_MVT),
    ANTS_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    STRIP_TAC,
    CLAIM (← q r"&0 <= poly p y - poly p (&K)"),
    MATCH_MP_TAC r1,
    ASM_REWRITE_TAC [],
    FIRST_ASSUM MATCH_MP_TAC,
    CLAIM (← q r"&N < &K"),
    ASM_MESON_TAC ((← deref REAL_REWRITES) ++ (← deref NUM_REWRITES)),
    STRIP_TAC,
    CLAIM (← q r"N:num < K"),
    ASM_MESON_TAC [REAL_OF_NUM_LT],
    ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"&0 < y - &K"),
    LABEL_ALL_TAC,
    USE_THEN "Z-7" MP_TAC,
    REAL_ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"poly (poly_diff p) x < &0"),
    FIRST_ASSUM MATCH_MP_TAC,
    REAL_SOLVE_TAC,
    STRIP_TAC,
    CLAIM (← q r"(y - &K) * poly (poly_diff p) x < &0"),
    ASM_MESON_TAC [REAL_MUL_LT],
    REPEAT STRIP_TAC,
    REAL_SOLVE_TAC
  ])
  /- }}} -/

  /- ---------------------------------------------------------------------- -/
  /-  Now the negative ones                                                 -/
  /- ---------------------------------------------------------------------- -/

  let UNB_LEFT_EVEN ← prove_by_refinement (
   (← q r"!k. 0 < k /\ EVEN k ==> mono_unbounded_above (\n. (-- &n) pow k)"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [REAL_POW_NEG],
    MATCH_MP_TAC POW_UNB,
    FIRST_ASSUM MATCH_ACCEPT_TAC
  ])
  /- }}} -/

  let UNB_LEFT_ODD ← prove_by_refinement (
   (← q r"!k. 0 < k /\ ODD k ==> mono_unbounded_below (\n. (-- &n) pow k)"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    REWRITE_ASSUMS [← GSYM NOT_EVEN],
    ASM_REWRITE_TAC [REAL_POW_NEG],
    MATCH_EQ_MP_TAC mua_neg,
    MATCH_MP_TAC POW_UNB,
    FIRST_ASSUM MATCH_ACCEPT_TAC
  ])
  /- }}} -/

  let EVEN_CONS ← prove_by_refinement (
    (← q r"!t h. ODD (LENGTH (CONS h t)) = EVEN (LENGTH t)"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC THEN
    ASM_MESON_TAC [LENGTH_SING, LENGTH, EVEN, ODD, ONE]
  ])
  /- }}} -/

  let ODD_CONS ← prove_by_refinement (
    (← q r"!t h. EVEN (LENGTH (CONS h t)) = ODD (LENGTH t)"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC THEN
    ASM_MESON_TAC [LENGTH_SING, LENGTH, EVEN, ODD, ONE]
  ])
  /- }}} -/

  let MUA_DIV_CONST ← do
    let a1 ← ARITH_RULE (← q r"b + a - b = a")
    prove_by_refinement (
    (← q r"!a b p. mono_unbounded_above (\n. p n) ==> (\n. a / (b + p n)) --> &0"),
  /- {{{ Proof -/

  [
    REWRITE_TAC [mono_unbounded_above, SEQ],
    REPEAT STRIP_TAC,
    REAL_SIMP_TAC,
    CASES_ON (← q r"a = &0"),
    ASM_REWRITE_TAC [real_div, REAL_MUL_LZERO, ABS_0],
    ABBREV_TAC (← q r"k = (max (&1) (abs a / e - b))"),
    FIRST_ASSUM (MP_TAC o (ISPEC (← q r"k:real"))),
    STRIP_TAC,
    EXISTS_TAC (← q r"N"),
    REPEAT STRIP_TAC,
    REWRITE_ASSUMS ((← deref REAL_REWRITES) ++ (← deref NUM_REWRITES)),
    POP_ASSUM (fun x => POP_ASSUM (fun y => tactic_of do pure (ASSUME_TAC (← MATCH_MP y x)))),
    REWRITE_TAC [REAL_ABS_DIV],
    MATCH_MP_TAC REAL_LTE_TRANS,
    EXISTS_TAC (← q r"abs a / (b + k)"),
    STRIP_TAC,
    MATCH_MP_TAC REAL_DIV_DENOM_LT,
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [REAL_ABS_NZ],
    LABEL_ALL_TAC,
    CLAIM (← q r"(abs a / e - b) <= k"),
    ASM_MESON_TAC [REAL_MAX_MAX],
    STRIP_TAC,
    CLAIM (← q r"&0 < abs a / e"),
    REWRITE_TAC [real_div],
    MATCH_MP_TAC REAL_LT_MUL,
    ASM_MESON_TAC [REAL_INV_POS, REAL_ABS_NZ],
    STRIP_TAC,
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    CLAIM (← q r"-- b < p n"),
    MATCH_MP_TAC REAL_LET_TRANS,
    EXISTS_TAC (← q r"k"),
    ASM_REWRITE_TAC [],
    CLAIM (← q r"(abs a / e - b) <= k"),
    ASM_MESON_TAC [REAL_MAX_MAX],
    STRIP_TAC,
    CLAIM (← q r"&0 < abs a / e"),
    REWRITE_TAC [real_div],
    MATCH_MP_TAC REAL_LT_MUL,
    ASM_MESON_TAC [REAL_INV_POS, REAL_ABS_NZ],
    STRIP_TAC,
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"abs (b + p n) = b + p n"),
    MATCH_EQ_MP_TAC REAL_ABS_REFL,
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    DISCH_THEN SUBST1_TAC,
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    CLAIM (← q r"(abs a / e - b) <= k"),
    ASM_MESON_TAC [REAL_MAX_MAX],
    STRIP_TAC,
    CLAIM (← q r"&0 < abs a / e"),
    REWRITE_TAC [real_div],
    MATCH_MP_TAC REAL_LT_MUL,
    ASM_MESON_TAC [REAL_INV_POS, REAL_ABS_NZ],
    STRIP_TAC,
    LABEL_ALL_TAC,
    CLAIM (← q r"abs a / e <= b + k"),
    USE_THEN "Z-1" MP_TAC THEN REAL_ARITH_TAC,
    STRIP_TAC,
    CASES_ON (← q r"&1 <= abs a / e - b"),
    CLAIM (← q r"k = abs a / e - b"),
    USE_THEN "Z-3" (SUBST1_TAC o GSYM),
    ASM_REWRITE_TAC [real_max],
    ASM_MESON_TAC [real_max],
    DISCH_THEN SUBST1_TAC,
    REWRITE_TAC [a1],
    REWRITE_TAC [real_div],
    REAL_SIMP_TAC,
    REWRITE_TAC [REAL_MUL_ASSOC],
    CLAIM (← q r"~(abs a = &0)"),
    ASM_MESON_TAC [REAL_ABS_NZ, REAL_LT_LE],
    STRIP_TAC,
    ASM_SIMP_TAC [REAL_MUL_RINV],
    REAL_SIMP_TAC,
    /- save -/
    REWRITE_ASSUMS (← deref REAL_REWRITES),
    CLAIM (← q r"k = &1"),
    ASM_MESON_TAC ([real_max] ++ (← deref REAL_REWRITES)),
    STRIP_TAC,
    CLAIM (← q r"&0 < b + k"),
    MATCH_MP_TAC REAL_LTE_TRANS,
    EXISTS_TAC (← q r"abs a / e"),
    ASM_MESON_TAC [],
    STRIP_TAC,
    MATCH_MP_TAC REAL_LE_RCANCEL_IMP,
    EXISTS_TAC (← q r"b + k"),
    ASM_REWRITE_TAC [],
    REWRITE_TAC [real_div],
    REWRITE_TAC [← GSYM REAL_MUL_ASSOC],
    CLAIM (← q r"inv (b + &1) * (b + &1) = &1"),
    LABEL_ALL_TAC,
    POP_ASSUM MP_TAC,
    ASM_REWRITE_TAC [],
    STRIP_TAC,
    ASM_MESON_TAC [REAL_MUL_LINV, REAL_LT_LE],
    DISCH_THEN SUBST1_TAC,
    REWRITE_TAC [REAL_MUL_RID],
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP,
    EXISTS_TAC (← q r"inv e"),
    REPEAT STRIP_TAC,
    USE_THEN "Z-5" MP_TAC,
    MESON_TAC [REAL_INV_POS, REAL_LT_LE],
    REWRITE_TAC [REAL_MUL_ASSOC],
    CLAIM (← q r"~(e = &0)"),
    ASM_MESON_TAC [REAL_INV_NZ, REAL_LT_LE],
    STRIP_TAC,
    ASM_SIMP_TAC [REAL_MUL_LINV],
    REAL_SIMP_TAC,
    ASM_MESON_TAC [real_div, REAL_MUL_SYM]
  ])

  /- }}} -/

  let SEQ_0_NEG ← prove_by_refinement (
    (← q r"!p. (\n. p n) --> &0 <=> (\n. -- p n) --> &0"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [SEQ],
    GEN_TAC THEN EQ_TAC,
    REPEAT STRIP_TAC,
    LABEL_ALL_TAC,
    USE_THEN "Z-0" (fun x => FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x)))),
    STRIP_TAC,
    EXISTS_TAC (← q r"N"),
    REPEAT STRIP_TAC,
    POP_ASSUM  (fun x => FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x)))),
    REAL_SIMP_TAC,
    STRIP_TAC,
    ASM_MESON_TAC [REAL_ABS_NEG],
    REPEAT STRIP_TAC,
    LABEL_ALL_TAC,
    USE_THEN "Z-0" (fun x => FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x)))),
    STRIP_TAC,
    EXISTS_TAC (← q r"N"),
    REPEAT STRIP_TAC,
    POP_ASSUM  (fun x => FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x)))),
    REAL_SIMP_TAC,
    STRIP_TAC,
    ASM_MESON_TAC [REAL_ABS_NEG]
  ])
  /- }}} -/

  -- asym.ml's second `lem`, which rebinds the first
  let lem ← do
    -- the ARITH_RULEs of the tactic list, right to left
    let a2 ← ARITH_RULE (← q r"-- y + -- z = --(y + z)")
    let a1 ← ARITH_RULE (← q r"--(x * y) = x * -- y")
    prove_by_refinement (
    (← q r"!x y z. --(x / (y + z)) = x / (-- y + -- z)"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    REWRITE_TAC [real_div],
    REWRITE_TAC [a1],
    REWRITE_TAC [a2],
    REWRITE_TAC [REAL_INV_NEG]
  ])
  /- }}} -/

  let MUB_DIV_CONST ← prove_by_refinement (
    (← q r"!a b p. mono_unbounded_below (\n. p n) ==> (\n. a / (b + p n)) --> &0"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [mua_neg2],
    REPEAT STRIP_TAC,
    ONCE_REWRITE_TAC [SEQ_0_NEG],
    REWRITE_TAC [lem],
    MATCH_MP_TAC MUA_DIV_CONST,
    FIRST_ASSUM MATCH_ACCEPT_TAC
  ])
  /- }}} -/

  let mono_unbounded ← new_definition (
    r"mono_unbounded p <=> mono_unbounded_above p \/ mono_unbounded_below p")

  let MU_DIV_CONST ← prove_by_refinement (
    (← q r"!a b p. mono_unbounded p ==> (\n. a / (b + p n)) --> &0"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [mono_unbounded],
    REPEAT STRIP_TAC,
    MATCH_MP_TAC MUA_DIV_CONST,
    REWRITE_TAC [ETA_AX],
    POP_ASSUM MATCH_ACCEPT_TAC,
    MATCH_MP_TAC MUB_DIV_CONST,
    REWRITE_TAC [ETA_AX],
    POP_ASSUM MATCH_ACCEPT_TAC
  ])
  /- }}} -/

  let MUA_MUA ← prove_by_refinement (
    (← q r"!p q. mono_unbounded_above (\n. p n) /\ mono_unbounded_above (\n. q n) ==>
             mono_unbounded_above (\n. p n * q n)"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [mono_unbounded_above_pos],
    REPEAT STRIP_TAC,
    CLAIM (← q r"&0 <= max c (&1)"),
    REWRITE_TAC [real_max],
    COND_CASES_TAC,
    REAL_ARITH_TAC,
    ASM_REWRITE_TAC [],
    DISCH_THEN (fun y => POP_ASSUM (fun x => RULE_ASSUM_TAC (fun th => MATCH_MP th y) THEN ASSUME_TAC x)),
    EVERY_ASSUM MP_TAC THEN REPEAT STRIP_TAC,
    EXISTS_TAC (← q r"nmax N N'"),
    REPEAT STRIP_TAC,
    MATCH_MP_TAC REAL_LET_TRANS,
    EXISTS_TAC (← q r"max c (&1)"),
    ASM_REWRITE_TAC [REAL_MAX_MAX],
    MATCH_MP_TAC REAL_LET_TRANS,
    EXISTS_TAC (← q r"max c (&1) * max c (&1)"),
    REPEAT STRIP_TAC,
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [← GSYM REAL_MUL_RID])),
    MATCH_MP_TAC REAL_LE_MUL2,
    REPEAT STRIP_TAC,
    REAL_SOLVE_TAC,
    REAL_SIMP_TAC,
    REAL_ARITH_TAC,
    REAL_SOLVE_TAC,
    MATCH_MP_TAC REAL_LT_MUL2,
    REPEAT STRIP_TAC,
    REAL_SOLVE_TAC,
    CLAIM (← q r"N <= n /\ N' <= (n:num)"),
    POP_ASSUM MP_TAC,
    REWRITE_TAC [nmax],
    COND_CASES_TAC,
    REPEAT STRIP_TAC,
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC,
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    REAL_SOLVE_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    POP_ASSUM MP_TAC THEN REWRITE_TAC [nmax] THEN ARITH_TAC
  ])
  /- }}} -/

  let MUA_MUB ← do
    let a1 ← ARITH_RULE (← q r"--(x * y) = x * -- y")
    prove_by_refinement (
    (← q r"!p q. mono_unbounded_above (\n. p n) /\ mono_unbounded_below (\n. q n) ==>
             mono_unbounded_below (\n. p n * q n)"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [mua_neg2],
    REWRITE_TAC [a1],
    REPEAT STRIP_TAC,
    MATCH_MP_TAC MUA_MUA,
    ASM_REWRITE_TAC []
  ])
  /- }}} -/

  let MUB_MUA ← do
    let a1 ← ARITH_RULE (← q r"--(x * y) = -- x * y")
    prove_by_refinement (
    (← q r"!p q. mono_unbounded_below (\n. p n) /\ mono_unbounded_above (\n. q n) ==>
             mono_unbounded_below (\n. p n * q n)"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [mua_neg2],
    REWRITE_TAC [a1],
    REPEAT STRIP_TAC,
    MATCH_MP_TAC MUA_MUA,
    ASM_REWRITE_TAC []
  ])
  /- }}} -/

  let MUB_MUB ← do
    let a1 ← ARITH_RULE (← q r"(x * y) = -- x * -- y")
    prove_by_refinement (
    (← q r"!p q. mono_unbounded_below (\n. p n) /\ mono_unbounded_below (\n. q n) ==>
             mono_unbounded_above (\n. p n * q n)"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [mua_neg2],
    ONCE_REWRITE_TAC [a1],
    REPEAT STRIP_TAC,
    MATCH_MP_TAC MUA_MUA,
    ASM_REWRITE_TAC []
  ])
  /- }}} -/

  let MU_PROD ← prove_by_refinement (
    (← q r"!p q. mono_unbounded (\n. p n) /\ mono_unbounded (\n. q n) ==> mono_unbounded (\n. p n * q n)"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [mono_unbounded],
    ASM_MESON_TAC [MUA_MUA, MUA_MUB, MUB_MUA, MUB_MUB]
  ])
  /- }}} -/

  let mub_quotient_limit ← prove_by_refinement (
   (← q r"!k f g. &0 < k /\ (\n. f n / g n) --> k /\ mono_unbounded_below g
      ==> mono_unbounded_below f"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [mua_neg2],
    REPEAT STRIP_TAC,
    MATCH_MP_TAC mua_quotient_limit,
    EXISTS_TAC (← q r"k"),
    EXISTS_TAC (← q r"\n. -- g n"),
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    BETA_TAC,
    REWRITE_TAC [REAL_NEG_DIV],
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC
  ])
  /- }}} -/

  let POLY_UB ← prove_by_refinement (
    (← q r"!p. nonconstant p ==> mono_unbounded (\n. poly p (&n))"),
  /- {{{ Proof -/

  [
    GEN_TAC,
    DISCH_THEN (fun x => ASSUME_TAC x THEN MP_TAC x),
    REWRITE_TAC [nonconstant],
    REPEAT STRIP_TAC,
    FIRST_ASSUM (fun x => tactic_of do pure (ASSUME_TAC (← MATCH_MP LIM_POLY2 x))),
    CASES_ON (← q r"LAST p < &0"),
    REWRITE_TAC [mono_unbounded],
    DISJ2_TAC,
    MATCH_MP_TAC mub_quotient_limit,
    EXISTS_TAC (← q r"&1"),
    EXISTS_TAC (← q r"(\n. LAST p * &n pow degree p)"),
    REPEAT STRIP_TAC,
    REAL_ARITH_TAC,
    BETA_TAC,
    MATCH_MP_TAC LIM_POLY2,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    MATCH_MP_TAC POW_UNBB_CON,
    ASM_REWRITE_TAC [],
    MATCH_MP_TAC NONCONSTANT_DEGREE,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    REWRITE_ASSUMS (← deref REAL_REWRITES),
    REWRITE_ASSUMS [REAL_LE_LT],
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    /- save -/
    REWRITE_TAC [mono_unbounded],
    DISJ1_TAC,
    MATCH_MP_TAC mua_quotient_limit,
    EXISTS_TAC (← q r"&1"),
    EXISTS_TAC (← q r"(\n. LAST p * &n pow degree p)"),
    REPEAT STRIP_TAC,
    REAL_ARITH_TAC,
    BETA_TAC,
    MATCH_MP_TAC LIM_POLY2,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    MATCH_MP_TAC POW_UNB_CON,
    ASM_REWRITE_TAC [],
    MATCH_MP_TAC NONCONSTANT_DEGREE,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    ASM_MESON_TAC [NORMAL_LAST_NONZERO]
  ])

  /- }}} -/

  /- ---------------------------------------------------------------------- -/
  /-  A polynomial applied to a negative argument                           -/
  /- ---------------------------------------------------------------------- -/

  let pneg_aux ← new_recursive_definition list_RECURSION
   r"(pneg_aux n [] = []) /\
    (pneg_aux n (CONS h t) = CONS (--(&1) pow n * h) (pneg_aux (SUC n) t))"

  let pneg ← new_recursive_definition list_RECURSION
   r"(pneg [] = []) /\
    (pneg (CONS h t) = pneg_aux 0 (CONS h t))"

  let POLY_PNEG_AUX_SUC ← prove_by_refinement (
    (← q r"!t n. pneg_aux (SUC (SUC n)) t = pneg_aux n t"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    STRIP_TAC,
    REWRITE_TAC [pneg_aux],
    REWRITE_TAC [pneg_aux, pow],
    REAL_SIMP_TAC,
    STRIP_TAC,
    AP_TERM_TAC,
    ASM_MESON_TAC []
  ])
  /- }}} -/

  let POLY_NEG_NEG ← prove_by_refinement (
   (← q r"!p. poly_neg (poly_neg p) = p"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [poly_neg, poly_cmul],
    REWRITE_TAC [poly_neg, poly_cmul],
    REAL_SIMP_TAC,
    AP_TERM_TAC,
    ASM_MESON_TAC [poly_neg, poly_cmul]
  ])
  /- }}} -/

  let POLY_PNEG_NEG ← prove_by_refinement (
   (← q r"!p n. poly_neg (pneg_aux (SUC n) p) = pneg_aux n p"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    ASM_REWRITE_TAC [pneg_aux, poly_neg, poly_cmul],
    REWRITE_TAC [pneg_aux],
    REPEAT STRIP_TAC,
    REWRITE_TAC [POLY_PNEG_AUX_SUC],
    REWRITE_TAC [poly_neg, poly_cmul],
    REAL_SIMP_TAC,
    AP_TERM_TAC,
    REWRITE_TAC [← GSYM poly_neg],
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [← GSYM POLY_NEG_NEG])),
    POP_ASSUM (fun x => ONCE_REWRITE_TAC (list x)),
    REWRITE_TAC []
  ])
  /- }}} -/

  let POLY_PNEG_AUX ← prove_by_refinement (
   (← q r"!k p n. EVEN n ==> (poly p (-- k) = poly (pneg_aux n p) k)"),
  /- {{{ Proof -/
  [
    STRIP_TAC,
    LIST_INDUCT_TAC,
    REPEAT STRIP_TAC,
    REWRITE_TAC [pneg_aux, poly],
    REPEAT STRIP_TAC,
    POP_ASSUM (fun x => RULE_ASSUM_TAC (fun y => MATCH_MP y x) THEN ASSUME_TAC x),
    REWRITE_TAC [poly, pneg_aux],
    REAL_SIMP_TAC,
    ASM_REWRITE_TAC [],
    REAL_SIMP_TAC,
    CLAIM (← q r"-- &1 pow n = &1"),
    REWRITE_TAC [REAL_POW_NEG],
    ASM_REWRITE_TAC [],
    REAL_SIMP_TAC,
    DISCH_THEN SUBST1_TAC,
    REAL_SIMP_TAC,
    AP_TERM_TAC,
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [← GSYM POLY_PNEG_NEG])),
    REWRITE_TAC [POLY_NEG],
    REAL_SIMP_TAC
  ])
  /- }}} -/

  let POLY_PNEG ← prove_by_refinement (
   (← q r"!p x. poly p (-- x) = poly (pneg p) x"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [pneg, poly],
    REWRITE_TAC [pneg, poly],
    REPEAT STRIP_TAC,
    CLAIM (← q r"poly (pneg_aux 0 (CONS h t)) x = poly (CONS h t) (--x)"),
    ASM_MESON_TAC [POLY_PNEG_AUX, EVEN],
    DISCH_THEN SUBST1_TAC,
    REWRITE_TAC [poly]
  ])
  /- }}} -/

  let DEGREE_0 ← prove_by_refinement (
   (← q r"degree [] = 0 "),
  /- {{{ Proof -/
  [
    REWRITE_TAC [degree],
    REWRITE_TAC [normalize, LENGTH],
    ARITH_TAC
  ])
  /- }}} -/

  let EVEN_ODD ← prove_by_refinement (
   (← q r"!x. EVEN (SUC x) = ODD x"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [EVEN, NOT_EVEN]
  ])
  /- }}} -/

  let ODD_EVEN ← prove_by_refinement (
   (← q r"!x. ODD (SUC x) = EVEN x"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [ODD, NOT_ODD]
  ])
  /- }}} -/

  -- @@RETURN BEGIN
  return { POLY_DIFF_UP_RIGHT, PDIFF_NEG_LAST, LAST_UNB_NEG, POLY_DIFF_DOWN_RIGHT,
           UNB_LEFT_EVEN, UNB_LEFT_ODD, EVEN_CONS, ODD_CONS, MUA_DIV_CONST, SEQ_0_NEG,
           lem, MUB_DIV_CONST, mono_unbounded, MU_DIV_CONST, MUA_MUA, MUA_MUB, MUB_MUA,
           MUB_MUB, MU_PROD, mub_quotient_limit, POLY_UB, pneg_aux, pneg,
           POLY_PNEG_AUX_SUC, POLY_NEG_NEG, POLY_PNEG_NEG, POLY_PNEG_AUX, POLY_PNEG,
           DEGREE_0, EVEN_ODD, ODD_EVEN }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/-  pneg, its lengths, degrees and last coefficients, and the parity of   -/
/-  the degree of a derivative (asym.ml 1926-2528)                         -/
/- ---------------------------------------------------------------------- -/

structure AsymPneg where
  -- @@FIELDS
  PNEG_CONS : thm
  PNEG_NIL : thm
  PNEG_AUX_NIL : thm
  POLY_CMUL_NIL : thm
  POLY_NEG_NIL : thm
  NEG_LAST : thm
  POLY_PNEG_LAST : thm
  PNEG_AUX_LENGTH : thm
  PNEG_LENGTH : thm
  LAST_PNEG_AUX_0 : thm
  LAST_PNEG_0 : thm
  PNEG_LAST : thm
  NORMAL_PNEG : thm
  PNEG_AUX_NORMALIZE_LENGTH : thm
  PNEG_NORMALIZE_LENGTH : thm
  DEGREE_PNEG : thm
  PNEG_SING : thm
  PNEG_NONCONSTANT : thm
  LAST_UNBB_EVEN_NEG : thm
  POLY_PNEG_LAST2 : thm
  LAST_UNB_ODD_NEG : thm
  LAST_UNB_EVEN_POS : thm
  LAST_UNB_ODD_POS : thm
  POLY_DIFF_AUX_NORMAL : thm
  POLY_DIFF_NORMAL : thm
  POLY_DIFF_AUX_NORMAL2 : thm
  POLY_DIFF_AUX_DEGREE : thm
  poly_diff_aux_odd : thm
  deriving Inhabited

@[nospecialize]
def setupAsymPneg [HolBase] (D : AsymDeps) (BAsymPoly : AsymPoly) (BAsymUnb : AsymUnb) :
    ExceptT String IO AsymPneg := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, CASES_ON, CLAIM, EXISTS_TAC,
        LIST_INDUCT_TAC, LIST_REWRITES, LIST_SIMP_TAC, MESON_TAC, REAL_ARITH_TAC,
        REAL_REWRITES, REAL_SIMP_TAC, prove_by_refinement, .. } := D
  let { ADD1, ADD_SYM, DE_MORGAN_THM, EVEN, EVEN_OR_ODD, LAST, LAST_CONS, LENGTH,
        LENGTH_0, LENGTH_NZ, LENGTH_PAIR, NOT_CONS_NIL, NOT_EVEN, NOT_SUC, ODD, POW_NZ,
        REAL_ENTIRE, REAL_INJ, REAL_POW_NZ, TL, degree, list_CASES, normalize,
        poly_cmul, poly_diff, poly_diff_aux, poly_neg, .. } := D.core1
  let { DEGREE_CONS, DEGREE_SING, LAST_UNB, NORMALIZE_SING, NORMAL_CONS, NORMAL_ID,
        NORMAL_TAIL, nonconstant, normal, .. } := BAsymPoly
  let { EVEN_ODD, LAST_UNB_NEG, ODD_EVEN, POLY_PNEG, POLY_PNEG_AUX_SUC, POLY_PNEG_NEG,
        pneg, pneg_aux, .. } := BAsymUnb
  -- @@SCOPE END

  let PNEG_CONS ← prove_by_refinement (
   (← q r"!p. pneg (CONS h t) = CONS h (neg (pneg t))"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [pneg, pneg_aux],
    REAL_SIMP_TAC,
    ONCE_REWRITE_TAC [← GSYM POLY_PNEG_NEG],
    REWRITE_TAC [POLY_PNEG_AUX_SUC],
    CASES_ON (← q r"t = []"),
    ASM_REWRITE_TAC [pneg, pneg_aux],
    REWRITE_ASSUMS (← deref LIST_REWRITES),
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    ASM_REWRITE_TAC [],
    REWRITE_TAC [← GSYM pneg]
  ])
  /- }}} -/

  let PNEG_NIL ← prove_by_refinement (
   (← q r"!p. (pneg p = []) <=> (p = [])"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC THEN
    MESON_TAC [pneg, NOT_CONS_NIL, pneg_aux]
  ])
  /- }}} -/

  let PNEG_AUX_NIL ← prove_by_refinement (
   (← q r"!p n. (pneg_aux n p = []) <=> (p = [])"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC THEN
    MESON_TAC [pneg, NOT_CONS_NIL, pneg_aux]
  ])
  /- }}} -/

  let POLY_CMUL_NIL ← prove_by_refinement (
   (← q r"!p. (c ## p = []) <=> (p = [])"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC THEN
    MESON_TAC [poly_cmul, NOT_CONS_NIL, pneg_aux]
  ])
  /- }}} -/

  let POLY_NEG_NIL ← prove_by_refinement (
   (← q r"!p. (poly_neg p = []) <=> (p = [])"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC THEN
    MESON_TAC [poly_neg, poly_cmul, NOT_CONS_NIL]
  ])
  /- }}} -/

  let NEG_LAST ← prove_by_refinement (
   (← q r"!p. ~(p = []) ==> (LAST (neg p) = -- LAST p)"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [],
    DISCH_THEN IGNORE,
    CASES_ON (← q r"t = []"),
    ASM_REWRITE_TAC [poly_neg, poly_cmul, LAST],
    REAL_ARITH_TAC,
    POP_ASSUM (fun x => REWRITE_ASSUMS [x] THEN ASSUME_TAC x),
    ASM_SIMP_TAC [LAST_CONS, poly_neg, poly_cmul],
    CLAIM (← q r"~(-- &1 ## t = [])"),
    ASM_MESON_TAC [POLY_CMUL_NIL],
    STRIP_TAC,
    ASM_SIMP_TAC [LAST_CONS],
    ASM_MESON_TAC [poly_neg]
  ])
  /- }}} -/

  let POLY_PNEG_LAST ← prove_by_refinement (
   (← q r"!p. normal p ==>
        (EVEN (degree p) ==> (LAST p = LAST (pneg p))) /\
        (ODD (degree p) ==> (LAST p = -- LAST (pneg p)))"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [normal],
    STRIP_TAC,
    CASES_ON (← q r"t = []"),
    ASM_REWRITE_TAC [LAST, pneg, pneg_aux],
    REAL_SIMP_TAC,
    ASM_MESON_TAC [DEGREE_SING, EVEN, NOT_EVEN],
    CLAIM (← q r"normal t"),
    MATCH_MP_TAC NORMAL_TAIL,
    ASM_MESON_TAC [],
    DISCH_THEN (fun x => RULE_ASSUM_TAC (REWRITE_RULE [x]) THEN ASSUME_TAC x),
    STRIP_TAC,
    STRIP_TAC,
    CLAIM (← q r"ODD (degree t)"),
    MATCH_EQ_MP_TAC EVEN_ODD,
    ASM_MESON_TAC [DEGREE_CONS, ADD1, ADD_SYM],
    DISCH_THEN (fun x => RULE_ASSUM_TAC (REWRITE_RULE [x]) THEN ASSUME_TAC x),
    ASM_SIMP_TAC [LAST_CONS],
    REWRITE_TAC [PNEG_CONS],
    CLAIM (← q r"~(neg (pneg t) = [])"),
    ASM_MESON_TAC [POLY_NEG_NIL, PNEG_NIL],
    STRIP_TAC,
    ASM_SIMP_TAC [LAST_CONS],
    ASM_MESON_TAC [NEG_LAST, PNEG_NIL],
    CLAIM (← q r"normal t"),
    MATCH_MP_TAC NORMAL_TAIL,
    ASM_MESON_TAC [],
    REPEAT STRIP_TAC,
    CLAIM (← q r"EVEN (degree t)"),
    MATCH_EQ_MP_TAC ODD_EVEN,
    ASM_MESON_TAC [DEGREE_CONS, ADD1, ADD_SYM],
    DISCH_THEN (fun x => RULE_ASSUM_TAC (REWRITE_RULE [x]) THEN ASSUME_TAC x),
    ASM_SIMP_TAC [LAST_CONS],
    REWRITE_TAC [PNEG_CONS],
    CLAIM (← q r"~(neg (pneg t) = [])"),
    ASM_MESON_TAC [POLY_NEG_NIL, PNEG_NIL],
    STRIP_TAC,
    ASM_SIMP_TAC [LAST_CONS],
    ASM_SIMP_TAC [NEG_LAST, PNEG_NIL],
    REAL_SIMP_TAC
  ])
  /- }}} -/

  let PNEG_AUX_LENGTH ← prove_by_refinement (
   (← q r"!p n. LENGTH (pneg_aux n p) = LENGTH p"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [LENGTH, pneg, pneg_aux],
    REWRITE_TAC [LENGTH, pneg, pneg_aux],
    ASM_MESON_TAC []
  ])
  /- }}} -/

  let PNEG_LENGTH ← prove_by_refinement (
   (← q r"!p. LENGTH (pneg p) = LENGTH p"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [LENGTH, pneg, pneg_aux],
    REWRITE_TAC [LENGTH, pneg, pneg_aux],
    ASM_MESON_TAC [PNEG_AUX_LENGTH]
  ])
  /- }}} -/

  let LAST_PNEG_AUX_0 ← do
    let a1 ← ARITH_RULE (← q r"~(-- &1 = &0)")
    prove_by_refinement (
   (← q r"!p n. ~(p = []) ==> ((LAST p = &0) <=> (LAST (pneg_aux n p) = &0))"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [],
    STRIP_TAC,
    DISCH_THEN IGNORE,
    CASES_ON (← q r"t = []"),
    ASM_REWRITE_TAC [LAST, pneg, pneg_aux],
    REAL_SIMP_TAC,
    ASM_SIMP_TAC [LAST_CONS, pneg, pneg_aux],
    REAL_SIMP_TAC,
    EQ_TAC,
    DISCH_THEN SUBST1_TAC,
    REAL_SIMP_TAC,
    STRIP_TAC,
    MP_TAC (← ISPECL [← q r"-- &1", ← q r"n:num"] POW_NZ),
    REAL_SIMP_TAC,
    REWRITE_TAC [a1],
    STRIP_TAC,
    ASM_MESON_TAC [REAL_ENTIRE],
    ASM_SIMP_TAC [LAST_CONS],
    REWRITE_TAC [pneg_aux],
    CLAIM (← q r"~(pneg_aux (SUC n) t = [])"),
    ASM_MESON_TAC [PNEG_AUX_NIL],
    STRIP_TAC,
    ASM_SIMP_TAC [LAST_CONS],
    ASM_MESON_TAC []
  ])
  /- }}} -/

  let LAST_PNEG_0 ← prove_by_refinement (
   (← q r"!p n. ~(p = []) ==> ((LAST p = &0) = (LAST (pneg p) = &0))"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC THEN MESON_TAC [LAST_PNEG_AUX_0, pneg]
  ])
  /- }}} -/

  let PNEG_LAST ← prove_by_refinement (
    (← q r"!p. ~(p = []) ==> (LAST (pneg p) = LAST p) \/ (LAST (pneg p) = -- LAST p)"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    CASES_ON (← q r"normal p"),
    MP_TAC (← ISPEC (← q r"p:real list") POLY_PNEG_LAST),
    ASM_REWRITE_TAC [],
    STRIP_TAC,
    DISJ_CASES_TAC (← ISPEC (← q r"degree p") EVEN_OR_ODD),
    ASM_MESON_TAC [],
    ASM_MESON_TAC (← deref REAL_REWRITES),
    REWRITE_ASSUMS [NORMAL_ID, DE_MORGAN_THM],
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    CLAIM (← q r"LENGTH p = 0"),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    ASM_MESON_TAC [LENGTH_0],
    ASM_REWRITE_TAC [],
    DISJ1_TAC,
    ASM_MESON_TAC [LAST_PNEG_0]
  ])
  /- }}} -/

  let NORMAL_PNEG ← prove_by_refinement (
   (← q r"!p. normal p = normal (pneg p)"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [NORMAL_ID],
    REPEAT STRIP_TAC,
    EQ_TAC,
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [PNEG_LENGTH],
    MP_TAC (← ISPEC (← q r"p:real list") PNEG_LAST),
    CLAIM (← q r"~(p = [])"),
    ASM_MESON_TAC [LENGTH_NZ],
    STRIP_TAC,
    ASM_REWRITE_TAC [],
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    /- save -/
    REPEAT STRIP_TAC,
    ONCE_REWRITE_TAC [← GSYM PNEG_LENGTH],
    ASM_REWRITE_TAC [],
    MP_TAC (← ISPEC (← q r"p:real list") PNEG_LAST),
    CLAIM (← q r"~(p = [])"),
    ASM_MESON_TAC [LENGTH_NZ, PNEG_LENGTH],
    STRIP_TAC,
    ASM_REWRITE_TAC [],
    EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC
  ])
  /- }}} -/

  let PNEG_AUX_NORMALIZE_LENGTH ← prove_by_refinement (
   (← q r"!p n. LENGTH (normalize (pneg_aux n p)) = LENGTH (normalize p)"),
  /- {{{ Proof -/

  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [normalize, LENGTH, pneg_aux],
    REWRITE_TAC [normalize, LENGTH, pneg, pneg_aux],
    STRIP_TAC,
    REPEAT COND_CASES_TAC THEN TRY (ASM_SIMP_TAC (← deref LIST_REWRITES)),
    LABEL_ALL_TAC,
    KEEP ["Z-2", "Z-0"],
    CLAIM (← q r"~(-- &1 pow n = &0)"),
    MATCH_MP_TAC REAL_POW_NZ,
    REAL_ARITH_TAC,
    STRIP_TAC,
    ASM_MESON_TAC [REAL_ENTIRE],
    ASM_MESON_TAC [LENGTH_0],
    CLAIM (← q r"~(-- &1 pow n = &0)"),
    MATCH_MP_TAC REAL_POW_NZ,
    REAL_ARITH_TAC,
    STRIP_TAC,
    ASM_MESON_TAC [REAL_ENTIRE],
    ASM_MESON_TAC [LENGTH_0],
    ASM_MESON_TAC [LENGTH_0]
  ])

  /- }}} -/

  -- asym.ml proves PNEG_NORMALIZE_LENGTH twice, the same way; the second
  -- (below) rebinds this one
  let PNEG_NORMALIZE_LENGTH ← prove_by_refinement (
   (← q r"!p n. LENGTH (normalize (pneg p)) = LENGTH (normalize p)"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [pneg],
    ASM_MESON_TAC [PNEG_AUX_NORMALIZE_LENGTH, pneg, pneg_aux]
  ])
  /- }}} -/

  let DEGREE_PNEG ← prove_by_refinement (
   (← q r"!p. degree (pneg p) = degree p"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [degree],
    ASM_MESON_TAC [PNEG_NORMALIZE_LENGTH]
  ])
  /- }}} -/

  let PNEG_SING ← prove_by_refinement (
   (← q r"!p. (pneg p = [x]) <=> (p = [x])"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [pneg, pneg_aux],
    EQ_TAC,
    REPEAT STRIP_TAC,
    LIST_SIMP_TAC,
    STRIP_TAC,
    REWRITE_ASSUMS [pneg, pneg_aux],
    POP_ASSUM MP_TAC,
    REAL_SIMP_TAC,
    LIST_SIMP_TAC,
    MESON_TAC [],
    POP_ASSUM MP_TAC,
    REWRITE_TAC [pneg, pneg_aux],
    LIST_SIMP_TAC,
    ASM_MESON_TAC [PNEG_AUX_NIL],
    REWRITE_TAC [pneg, pneg_aux],
    REAL_SIMP_TAC,
    LIST_SIMP_TAC,
    STRIP_TAC,
    ASM_MESON_TAC [pneg_aux]
  ])
  /- }}} -/

  let PNEG_NONCONSTANT ← prove_by_refinement (
   (← q r"!p. nonconstant (pneg p) = nonconstant p"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [nonconstant],
    STRIP_TAC THEN EQ_TAC,
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [NORMAL_PNEG],
    POP_ASSUM (fun x => REWRITE_ASSUMS (list x)),
    REWRITE_ASSUMS [pneg, pneg_aux],
    POP_ASSUM MP_TAC,
    REAL_SIMP_TAC,
    MESON_TAC [],
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [NORMAL_PNEG],
    ASM_MESON_TAC [PNEG_SING]
  ])
  /- }}} -/

  let LAST_UNBB_EVEN_NEG ← prove_by_refinement (
   (← q r"!p. nonconstant p /\ EVEN (degree p) /\ LAST p < &0 ==>
         mono_unbounded_below (\n. poly p (-- &n))"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    REWRITE_TAC [POLY_PNEG],
    MATCH_MP_TAC LAST_UNB_NEG,
    ASM_REWRITE_TAC [PNEG_NONCONSTANT],
    ASM_MESON_TAC [POLY_PNEG_LAST, nonconstant]
  ])
  /- }}} -/

  let POLY_PNEG_LAST2 ← do
    let a1 ← ARITH_RULE (← q r"(--x = y) <=> (x = -- y)")
    prove_by_refinement (
    (← q r"!p. normal p
           ==> (EVEN (degree p) ==> (LAST (pneg p) = LAST p)) /\
               (ODD (degree p) ==> (LAST (pneg p) = -- LAST p))"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [POLY_PNEG_LAST],
    ASM_MESON_TAC ([POLY_PNEG_LAST, a1])
  ])
  /- }}} -/

  let LAST_UNB_ODD_NEG ← prove_by_refinement (
   (← q r"!p. nonconstant p /\ ODD (degree p) /\ LAST p < &0 ==>
         mono_unbounded_above (\n. poly p (-- &n))"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    REWRITE_TAC [POLY_PNEG],
    MATCH_MP_TAC LAST_UNB,
    ASM_REWRITE_TAC [PNEG_NONCONSTANT],
    CLAIM (← q r"LAST (pneg p) = -- LAST p"),
    ASM_MESON_TAC [POLY_PNEG_LAST2, nonconstant],
    DISCH_THEN SUBST1_TAC,
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC
  ])
  /- }}} -/

  let LAST_UNB_EVEN_POS ← prove_by_refinement (
   (← q r"!p. nonconstant p /\ EVEN (degree p) /\ &0 < LAST p ==>
         mono_unbounded_above (\n. poly p (-- &n))"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    REWRITE_TAC [POLY_PNEG],
    MATCH_MP_TAC LAST_UNB,
    ASM_REWRITE_TAC [PNEG_NONCONSTANT],
    ASM_MESON_TAC [POLY_PNEG_LAST2, nonconstant]
  ])
  /- }}} -/

  let LAST_UNB_ODD_POS ← prove_by_refinement (
   (← q r"!p. nonconstant p /\ ODD (degree p) /\ &0 < LAST p ==>
         mono_unbounded_below (\n. poly p (-- &n))"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    REWRITE_TAC [POLY_PNEG],
    MATCH_MP_TAC LAST_UNB_NEG,
    ASM_REWRITE_TAC [PNEG_NONCONSTANT],
    CLAIM (← q r"LAST (pneg p) = -- LAST p"),
    ASM_MESON_TAC [POLY_PNEG_LAST2, nonconstant],
    DISCH_THEN SUBST1_TAC,
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC
  ])
  /- }}} -/

  let PNEG_NORMALIZE_LENGTH ← prove_by_refinement (
   (← q r"!p n. LENGTH (normalize (pneg p)) = LENGTH (normalize p)"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [pneg],
    ASM_MESON_TAC [PNEG_AUX_NORMALIZE_LENGTH, pneg, pneg_aux]
  ])
  /- }}} -/

  let POLY_DIFF_AUX_NORMAL ← do
    -- the ARITH_RULEs of the tactic list, right to left
    let a2 ← ARITH_RULE (← q r"~(SUC n = 0)")
    let a1 ← ARITH_RULE (← q r"~(SUC x = 0)")
    prove_by_refinement (
   (← q r"!p n. ~(n = 0) ==> (normal p = normal (poly_diff_aux n p))"),
  /- {{{ Proof -/

  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [normal, poly_diff_aux],
    REPEAT STRIP_TAC,
    REWRITE_TAC [poly_diff_aux],
    CASES_ON (← q r"t = []"),
    ASM_REWRITE_TAC [poly_diff_aux],
    REWRITE_TAC [normal],
    EQ_TAC,
    REPEAT STRIP_TAC,
    REWRITE_TAC [normalize],
    COND_CASES_TAC,
    CLAIM (← q r"~(h = &0)"),
    ASM_MESON_TAC [normal, normalize],
    STRIP_TAC,
    ASM_MESON_TAC [REAL_ENTIRE, REAL_INJ],
    ASM_REWRITE_TAC [],
    ASM_MESON_TAC [NOT_CONS_NIL],
    STRIP_TAC,
    ASM_REWRITE_TAC [NOT_CONS_NIL],
    REWRITE_TAC [NORMALIZE_SING],
    CLAIM (← q r"~(&n * h = &0)"),
    ASM_MESON_TAC [normalize],
    ASM_MESON_TAC [REAL_ENTIRE, REAL_INJ, normalize],
    EQ_TAC,
    REPEAT STRIP_TAC,
    CLAIM (← q r"normal t"),
    ASM_MESON_TAC [NORMAL_TAIL],
    STRIP_TAC,
    MATCH_MP_TAC NORMAL_CONS,
    ASM_MESON_TAC [a1],
    STRIP_TAC,
    MATCH_MP_TAC NORMAL_CONS,
    MP_TAC a2,
    DISCH_THEN (fun x => FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x)))),
    STRIP_TAC,
    ASM_REWRITE_TAC [],
    MATCH_MP_TAC NORMAL_TAIL,
    EXISTS_TAC (← q r"&n * h"),
    ASM_REWRITE_TAC [],
    ASM_MESON_TAC [poly_diff_aux, NOT_CONS_NIL, list_CASES]
  ])

  /- }}} -/

  let POLY_DIFF_NORMAL ← do
    -- the ARITH_RULEs of the tactic list, right to left
    let a2 ← ARITH_RULE (← q r"~(1 = 0)")
    let a1 ← ARITH_RULE (← q r"~(1 = 0)")
    prove_by_refinement (
   (← q r"!p. nonconstant p ==> normal (poly_diff p)"),
  /- {{{ Proof -/

  [
    LIST_INDUCT_TAC,
    ASM_MESON_TAC [normal, poly_diff, poly_diff_aux, POLY_DIFF_AUX_NORMAL, a1, nonconstant],
    REWRITE_TAC [poly_diff, NOT_CONS_NIL, TL],
    REWRITE_TAC [nonconstant],
    STRIP_TAC,
    CLAIM (← q r"normal t"),
    MATCH_MP_TAC NORMAL_TAIL,
    EXISTS_TAC (← q r"h:real"),
    ASM_MESON_TAC [normal],
    STRIP_TAC,
    ASM_MESON_TAC [normal, poly_diff, poly_diff_aux, POLY_DIFF_AUX_NORMAL, a2]
  ])

  /- }}} -/

  let POLY_DIFF_AUX_NORMAL2 ← prove_by_refinement (
   (← q r"!p n. ~(n = 0) ==> (normal (poly_diff_aux n p) <=> normal p)"),
  /- {{{ Proof -/
  [MESON_TAC [POLY_DIFF_AUX_NORMAL]])
  /- }}} -/

  let POLY_DIFF_AUX_DEGREE ← prove_by_refinement (
   (← q r"!p m n. ~(n = 0) /\ ~(m = 0) /\ normal p ==>
      (degree (poly_diff_aux n p) = degree (poly_diff_aux m p))"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [poly_diff_aux],
    REPEAT STRIP_TAC,
    REWRITE_TAC [poly_diff_aux],
    CASES_ON (← q r"t = []"),
    ASM_REWRITE_TAC [poly_diff_aux, DEGREE_SING],
    CLAIM (← q r"normal (poly_diff_aux (SUC n) t)"),
    ASM_SIMP_TAC [POLY_DIFF_AUX_NORMAL2, NOT_SUC],
    MATCH_MP_TAC NORMAL_TAIL,
    ASM_REWRITE_TAC [],
    EXISTS_TAC (← q r"h:real"),
    ASM_REWRITE_TAC [],
    STRIP_TAC,
    CLAIM (← q r"normal (poly_diff_aux (SUC m) t)"),
    ASM_SIMP_TAC [POLY_DIFF_AUX_NORMAL2, NOT_SUC],
    MATCH_MP_TAC NORMAL_TAIL,
    ASM_REWRITE_TAC [],
    EXISTS_TAC (← q r"h:real"),
    ASM_REWRITE_TAC [],
    STRIP_TAC,
    ASM_SIMP_TAC [DEGREE_CONS],
    AP_TERM_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    STRIP_TAC,
    ARITH_TAC,
    STRIP_TAC,
    ARITH_TAC,
    MATCH_MP_TAC NORMAL_TAIL,
    ASM_MESON_TAC []
  ])
  /- }}} -/

  let poly_diff_aux_odd ← do
    let a1 ← ARITH_RULE (← q r"~(SUC n = 0)")
    prove_by_refinement (
   (← q r"!p n. nonconstant p ==>
    (EVEN (degree p) = EVEN (degree (poly_diff_aux n p))) /\
    (ODD (degree p) = ODD (degree (poly_diff_aux n p)))"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [normal, nonconstant],
    STRIP_TAC,
    DISCH_THEN (fun x => ASSUME_TAC x THEN MP_TAC x),
    REWRITE_TAC [nonconstant],
    STRIP_TAC,
    CASES_ON (← q r"t = []"),
    ASM_MESON_TAC [nonconstant, normal],
    REWRITE_TAC [poly_diff_aux],
    CLAIM (← q r"normal t"),
    ASM_MESON_TAC [NORMAL_TAIL],
    STRIP_TAC,
    CLAIM (← q r"normal (poly_diff_aux (SUC n) t)"),
    ASM_MESON_TAC [nonconstant, normal, POLY_DIFF_AUX_NORMAL, NOT_SUC],
    STRIP_TAC,
    CASES_ON (← q r"?x. t = [x]"),
    POP_ASSUM MP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [],
    CLAIM (← q r"~(x = &0)"),
    ASM_MESON_TAC [normal, normalize],
    STRIP_TAC,
    CLAIM (← q r"degree [h; x] = 1"),
    CLAIM (← q r"normalize [h; x] = [h; x]"),
    ASM_MESON_TAC [normal],
    DISCH_THEN SUBST1_TAC,
    CLAIM (← q r"LENGTH [h; x] = 2"),
    ASM_MESON_TAC [LENGTH_PAIR],
    STRIP_TAC,
    REWRITE_TAC [degree],
    CLAIM (← q r"normal [h; x]"),
    ASM_MESON_TAC [normal, normalize],
    DISCH_THEN (fun x => ASSUME_TAC x THEN MP_TAC x),
    REWRITE_TAC [normal],
    STRIP_TAC,
    ASM_REWRITE_TAC [],
    ARITH_TAC,
    STRIP_TAC,
    ASM_REWRITE_TAC [poly_diff_aux],
    CLAIM (← q r"~(&(SUC n) * x = &0)"),
    ASM_MESON_TAC [normal, normalize, REAL_ENTIRE, a1, REAL_INJ],
    STRIP_TAC,
    CLAIM (← q r"degree [&n * h; &(SUC n) * x] = 1"),
    REWRITE_TAC [degree],
    ASM_REWRITE_TAC [normalize, NOT_CONS_NIL, LENGTH],
    ARITH_TAC,
    STRIP_TAC,
    ASM_REWRITE_TAC [],
    ASM_SIMP_TAC [DEGREE_CONS],
    CLAIM (← q r"nonconstant t"),
    ASM_MESON_TAC [nonconstant],
    STRIP_TAC,
    ONCE_REWRITE_TAC [ADD_SYM],
    REWRITE_TAC [← GSYM ADD1],
    ASM_SIMP_TAC [EVEN, ODD],
    ASM_MESON_TAC [POLY_DIFF_AUX_DEGREE]
  ])
  /- }}} -/

  -- @@RETURN BEGIN
  return { PNEG_CONS, PNEG_NIL, PNEG_AUX_NIL, POLY_CMUL_NIL, POLY_NEG_NIL, NEG_LAST,
           POLY_PNEG_LAST, PNEG_AUX_LENGTH, PNEG_LENGTH, LAST_PNEG_AUX_0, LAST_PNEG_0,
           PNEG_LAST, NORMAL_PNEG, PNEG_AUX_NORMALIZE_LENGTH, PNEG_NORMALIZE_LENGTH,
           DEGREE_PNEG, PNEG_SING, PNEG_NONCONSTANT, LAST_UNBB_EVEN_NEG, POLY_PNEG_LAST2,
           LAST_UNB_ODD_NEG, LAST_UNB_EVEN_POS, LAST_UNB_ODD_POS, POLY_DIFF_AUX_NORMAL,
           POLY_DIFF_NORMAL, POLY_DIFF_AUX_NORMAL2, POLY_DIFF_AUX_DEGREE,
           poly_diff_aux_odd }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/-  The parity of the degree of a derivative, and the theorems on the     -/
/-  left and right (asym.ml 2530-3227)                                     -/
/- ---------------------------------------------------------------------- -/

structure AsymLeft where
  -- @@FIELDS
  poly_diff_parity : thm
  poly_diff_parity2 : thm
  normal_nonconstant : thm
  nmax_le : thm
  POLY_DIFF_UP_LEFT : thm
  POLY_DIFF_DOWN_LEFT : thm
  POLY_DIFF_DOWN_LEFT2 : thm
  POLY_DIFF_UP_LEFT2 : thm
  POLY_DIFF_DOWN_LEFT3 : thm
  POLY_DIFF_UP_LEFT3 : thm
  POLY_DIFF_DOWN_LEFT4 : thm
  POLY_DIFF_UP_LEFT4 : thm
  POLY_DIFF_DOWN_LEFT5 : thm
  POLY_DIFF_UP_LEFT5 : thm
  NORMAL_PDIFF_LEM : thm
  NORMAL_PDIFF : thm
  POLY_DIFF_UP_RIGHT2 : thm
  POLY_DIFF_DOWN_RIGHT2 : thm
  POLY_DIFF_UP_RIGHT3 : thm
  POLY_DIFF_DOWN_RIGHT3 : thm
  deriving Inhabited

@[nospecialize]
def setupAsymLeft [HolBase] (D : AsymDeps) (BAsymSeq : AsymSeq) (BAsymPoly : AsymPoly) (BAsymUnb : AsymUnb) (BAsymPneg : AsymPneg) :
    ExceptT String IO AsymLeft := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, CASES_ON, CLAIM, EXISTS_TAC,
        LIST_INDUCT_TAC, LIST_REWRITES, LIST_SIMP_TAC, MESON_TAC, REAL_ARITH,
        REAL_ARITH_TAC, REAL_SIMP_TAC, prove_by_refinement, .. } := D
  let { ADD1, ADD_SYM, EVEN, EVEN_OR_ODD, LAST, LENGTH, LENGTH_0, LENGTH_1, LENGTH_NZ,
        LT_REFL, NOT_CONS_NIL, NOT_EVEN, NOT_ODD, NOT_SUC, ODD, ONE, POLY_MVT,
        REAL_ARCH_SIMPLE, REAL_ENTIRE, REAL_LET_TRANS, REAL_LE_NEG2, REAL_LE_TRANS,
        REAL_LTE_TRANS, REAL_MUL_GT, REAL_MUL_LT, REAL_OF_NUM_LE, TL, degree,
        list_CASES, nmax, normalize, poly, poly_diff, poly_diff_aux, real_ge, real_gt, .. } := D.core1
  let { mono_unbounded_above, mono_unbounded_below, mua_quotient_limit,
        mua_quotient_limit_neg, .. } := BAsymSeq
  let { DEGREE_CONS, DEGREE_SING, LIM_POLY2, NONCONSTANT_DIFF_NORMAL, NORMAL_CONS,
        NORMAL_ID, NORMAL_TAIL, POLY_DIFF_LAST_GT, POLY_DIFF_LAST_LT, POW_UNBB_CON,
        POW_UNB_CON, nonconstant, normal, .. } := BAsymPoly
  let { POLY_DIFF_DOWN_RIGHT, POLY_DIFF_UP_RIGHT, POLY_PNEG, .. } := BAsymUnb
  let { DEGREE_PNEG, LAST_UNBB_EVEN_NEG, LAST_UNB_EVEN_POS, LAST_UNB_ODD_NEG,
        LAST_UNB_ODD_POS, NORMAL_PNEG, POLY_DIFF_AUX_DEGREE, POLY_DIFF_AUX_NORMAL,
        POLY_DIFF_AUX_NORMAL2, POLY_DIFF_NORMAL, POLY_PNEG_LAST, .. } := BAsymPneg
  -- @@SCOPE END

  let poly_diff_parity ← do
    -- the ARITH_RULEs of the tactic list, right to left
    let a2 ← ARITH_RULE (← q r"1 + x = SUC x")
    let a1 ← ARITH_RULE (← q r"~(&1 = &0)")
    prove_by_refinement (
   (← q r"!p n. nonconstant p ==>
    (EVEN (degree p) = ODD (degree (poly_diff p))) /\
    (ODD (degree p) = EVEN (degree (poly_diff p)))"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [nonconstant, normal],
    STRIP_TAC,
    DISCH_ASS,
    REWRITE_TAC [nonconstant],
    STRIP_TAC,
    REWRITE_TAC [poly_diff],
    LIST_SIMP_TAC,
    CLAIM (← q r"~(1 = 0)"),
    ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"normal t"),
    MATCH_MP_TAC NORMAL_TAIL,
    ASM_MESON_TAC [nonconstant, normal],
    STRIP_TAC,
    ASM_SIMP_TAC [DEGREE_CONS],
    CASES_ON (← q r"?x. t = [x]"),
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    CLAIM (← q r"~(x = &0)"),
    ASM_MESON_TAC [normal, normalize],
    STRIP_TAC,
    ASM_REWRITE_TAC [poly_diff_aux, DEGREE_SING, degree, normalize, LENGTH, NOT_CONS_NIL],
    CLAIM (← q r"~(&1 * x = &0)"),
    ASM_MESON_TAC [REAL_ENTIRE, a1],
    STRIP_TAC,
    ASM_REWRITE_TAC [LENGTH],
    REWRITE_TAC [a2],
    ASM_MESON_TAC [EVEN, ODD, NOT_EVEN, NOT_ODD],
    CLAIM (← q r"nonconstant t"),
    ASM_MESON_TAC [nonconstant],
    DISCH_ASS,
    DISCH_THEN (fun x => REWRITE_ASSUMS [x] THEN ASSUME_TAC x),
    ONCE_REWRITE_TAC [ADD_SYM],
    REWRITE_TAC [← GSYM ADD1, EVEN, ODD],
    CLAIM (← q r"?h' t'. t = CONS h' t'"),
    ASM_MESON_TAC [nonconstant, normal, list_CASES],
    STRIP_TAC,
    POP_ASSUM (fun x => REWRITE_ASSUMS [x] THEN REWRITE_TAC [x] THEN ASSUME_TAC x),
    REWRITE_ASSUMS [poly_diff, NOT_CONS_NIL, TL],
    REWRITE_TAC [poly_diff_aux],
    CLAIM (← q r"normal t'"),
    ASM_MESON_TAC [nonconstant, NORMAL_TAIL, normal],
    STRIP_TAC,
    CLAIM (← q r"normal (poly_diff_aux (SUC 1) t')"),
    ASM_MESON_TAC [POLY_DIFF_AUX_NORMAL2, NOT_SUC],
    STRIP_TAC,
    ASM_SIMP_TAC [DEGREE_CONS],
    ONCE_REWRITE_TAC [ADD_SYM],
    REWRITE_TAC [← GSYM ADD1, EVEN, ODD],
    CLAIM (← q r"normal (poly_diff_aux 1 t')"),
    ASM_MESON_TAC [POLY_DIFF_AUX_NORMAL2, ONE, NOT_SUC],
    STRIP_TAC,
    ASM_MESON_TAC [POLY_DIFF_AUX_DEGREE, ONE, NOT_SUC]
  ])
  /- }}} -/

  let poly_diff_parity2 ← prove_by_refinement (
   (← q r"!p n. nonconstant p ==>
    (ODD (degree (poly_diff p)) = EVEN (degree p)) /\
    (EVEN (degree (poly_diff p)) = ODD (degree p))"),
  /- {{{ Proof -/
  [MESON_TAC [poly_diff_parity]])
  /- }}} -/

  let normal_nonconstant ← prove_by_refinement (
   (← q r"!p. normal p /\ 0 < degree p ==> nonconstant p"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [nonconstant],
    ASM_MESON_TAC [DEGREE_SING, LT_REFL]
  ])
  /- }}} -/

  let nmax_le ← prove_by_refinement (
   (← q r"!n m. n <= nmax n m /\ m <= nmax n m"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [nmax],
    REPEAT STRIP_TAC,
    COND_CASES_TAC,
    ARITH_TAC,
    ARITH_TAC
  ])
  /- }}} -/

  let POLY_DIFF_UP_LEFT ← do
    -- the rules of the tactic list, right to left
    let t5 ← ARITH_RULE (← q r"x < y <=> ~(y <= x)")
    let t4 ← ARITH_RULE (← q r"~(x < &0 /\ &0 < x)")
    let t3 ← ARITH_RULE (← q r"x < y <=> ~(y < x) /\ ~(y = x)")
    let t2 ← ARITH_RULE (← q r"~(x < &0 /\ &0 < x)")
    let t1 ← REAL_ARITH (← q r"x < y <=> ~(x = y) /\ ~(y < x)")
    prove_by_refinement (
   (← q r"!p. nonconstant p /\ (?X. !x. x < X ==> poly (poly_diff p) x < &0) ==>
     (?Y. !y. y < Y ==> &0 < poly p y)"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    CLAIM (← q r"mono_unbounded_above (\n. poly p (-- &n))"),
    REWRITE_TAC [POLY_PNEG],
    DISJ_CASES_TAC (← ISPEC (← q r"degree p") EVEN_OR_ODD),
    MATCH_MP_TAC mua_quotient_limit,
    EXISTS_TAC (← q r"&1"),
    EXISTS_TAC (← q r"(\n. LAST (pneg p) * &n pow degree (pneg p))"),
    REPEAT STRIP_TAC,
    REAL_ARITH_TAC,
    BETA_TAC,
    MATCH_MP_TAC LIM_POLY2,
    MATCH_EQ_MP_TAC NORMAL_PNEG,
    ASM_MESON_TAC [nonconstant],
    MATCH_MP_TAC POW_UNB_CON,
    STRIP_TAC,
    REWRITE_TAC [DEGREE_PNEG],
    REWRITE_TAC [degree],
    CLAIM (← q r"normalize p = p"),
    ASM_MESON_TAC [nonconstant, normal],
    DISCH_THEN SUBST1_TAC,
    CLAIM (← q r"~(LENGTH p = 0)"),
    ASM_MESON_TAC [nonconstant, normal, LENGTH_NZ, LENGTH_0, degree],
    STRIP_TAC,
    CLAIM (← q r"~(LENGTH p = 1)"),
    ASM_MESON_TAC [nonconstant, normal, LENGTH_NZ, LENGTH_1, degree],
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    /- save -/
    CLAIM (← q r"LAST (pneg p) = LAST p"),
    ASM_MESON_TAC [← GSYM POLY_PNEG_LAST, nonconstant],
    DISCH_THEN SUBST1_TAC,
    ONCE_REWRITE_TAC [t1],
    STRIP_TAC,
    ASM_MESON_TAC [NORMAL_ID, nonconstant],
    STRIP_TAC,
    CLAIM (← q r"ODD (degree (poly_diff p))"),
    ASM_SIMP_TAC [poly_diff_parity2],
    STRIP_TAC,
    CLAIM (← q r"nonconstant (poly_diff p)"),
    MATCH_MP_TAC normal_nonconstant,
    STRIP_TAC,
    MATCH_MP_TAC NONCONSTANT_DIFF_NORMAL,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"mono_unbounded_above (\n. poly (poly_diff p) (-- &n))"),
    MATCH_MP_TAC LAST_UNB_ODD_NEG,
    ASM_REWRITE_TAC [],
    ASM_MESON_TAC [POLY_DIFF_LAST_LT],
    REWRITE_TAC [mono_unbounded_above],
    DISCH_THEN (MP_TAC o ISPEC (← q r"&0")),
    STRIP_TAC,
    /- save -/
    MP_TAC (← ISPEC (← q r"-- (X - &1)") REAL_ARCH_SIMPLE),
    DISCH_THEN (X_CHOOSE_TAC (← q r"M:num")),
    CLAIM (← q r"-- &M <= X - &1"),
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    STRIP_TAC,
    LABEL_ALL_TAC,
    USE_THEN "Z-2" (MP_TAC o ISPEC (← q r"nmax M N")),
    STRIP_TAC,
    CLAIM (← q r"N <= nmax M N"),
    REWRITE_TAC [nmax_le],
    DISCH_THEN (fun x => REWRITE_ASSUMS (list x)),
    CLAIM (← q r"-- &(nmax M N) < X"),
    MATCH_MP_TAC REAL_LET_TRANS,
    EXISTS_TAC (← q r"-- &M"),
    STRIP_TAC,
    REWRITE_TAC [nmax],
    REWRITE_TAC [REAL_LE_NEG2, REAL_OF_NUM_LE] THEN ARITH_TAC,
    USE_THEN "Z-0" MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    ASM_MESON_TAC [t2],
    /- save -/
    REWRITE_TAC [← GSYM POLY_PNEG],
    MATCH_MP_TAC LAST_UNB_ODD_NEG,
    ASM_REWRITE_TAC [],
    ASM_SIMP_TAC [← GSYM POLY_DIFF_LAST_LT],
    CASES_ON (← q r"?x. poly_diff p = [x]"),
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    ASM_REWRITE_TAC [LAST],
    LABEL_ALL_TAC,
    USE_THEN "Z-2" MP_TAC,
    POP_ASSUM (fun x => REWRITE_TAC [x] THEN ASSUME_TAC x),
    REWRITE_TAC [poly],
    REAL_SIMP_TAC,
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    EXISTS_TAC (← q r"X - &1"),
    REAL_ARITH_TAC,
    CLAIM (← q r"nonconstant (poly_diff p)"),
    REWRITE_TAC [nonconstant],
    STRIP_TAC,
    MATCH_MP_TAC POLY_DIFF_NORMAL,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    ASM_MESON_TAC [],
    STRIP_TAC,
    CLAIM (← q r"EVEN (degree (poly_diff p))"),
    ASM_MESON_TAC [poly_diff_parity],
    STRIP_TAC,
    ONCE_REWRITE_TAC [t3],
    REPEAT STRIP_TAC,
    CLAIM (← q r"mono_unbounded_above (\n. poly (poly_diff p) (-- (&n)))"),
    MATCH_MP_TAC LAST_UNB_EVEN_POS,
    ASM_REWRITE_TAC [],
    REWRITE_TAC [mono_unbounded_above],
    DISCH_THEN (MP_TAC o ISPEC (← q r"&0")),
    STRIP_TAC,
    /- save -/
    MP_TAC (← ISPEC (← q r"-- (X - &1)") REAL_ARCH_SIMPLE),
    DISCH_THEN (X_CHOOSE_TAC (← q r"M:num")),
    CLAIM (← q r"-- &M <= X - &1"),
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    STRIP_TAC,
    LABEL_ALL_TAC,
    USE_THEN "Z-2" (MP_TAC o ISPEC (← q r"nmax M N")),
    STRIP_TAC,
    CLAIM (← q r"N <= nmax M N"),
    REWRITE_TAC [nmax_le],
    DISCH_THEN (fun x => REWRITE_ASSUMS (list x)),
    CLAIM (← q r"-- &(nmax M N) < X"),
    MATCH_MP_TAC REAL_LET_TRANS,
    EXISTS_TAC (← q r"-- &M"),
    STRIP_TAC,
    REWRITE_TAC [nmax],
    REWRITE_TAC [REAL_LE_NEG2, REAL_OF_NUM_LE] THEN ARITH_TAC,
    USE_THEN "Z-0" MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    ASM_MESON_TAC [t4],
    ASM_MESON_TAC [nonconstant, NORMAL_ID],
    /- save xxx -/
    REWRITE_TAC [mono_unbounded_above],
    DISCH_THEN (MP_TAC o ISPEC (← q r"&0")),
    STRIP_TAC,
    MP_TAC (← ISPEC (← q r"-- (X - &1)") REAL_ARCH_SIMPLE),
    DISCH_THEN (X_CHOOSE_TAC (← q r"M:num")),
    ABBREV_TAC (← q r"k = nmax N M"),
    EXISTS_TAC (← q r"-- &k"),
    REPEAT STRIP_TAC,
    REWRITE_TAC [t5],
    STRIP_TAC,
    MP_TAC (← ISPECL [← q r"p:real list", ← q r"y:real", ← q r"-- &k"] POLY_MVT),
    ASM_REWRITE_TAC [],
    STRIP_TAC,
    LABEL_ALL_TAC,
    CLAIM (← q r"&0 < (-- &k) - y"),
    USE_THEN "Z-4" MP_TAC THEN REAL_ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"poly (poly_diff p) x < &0"),
    FIRST_ASSUM MATCH_MP_TAC,
    MATCH_MP_TAC REAL_LTE_TRANS,
    EXISTS_TAC (← q r"-- &k"),
    ASM_REWRITE_TAC [],
    MATCH_MP_TAC REAL_LE_TRANS,
    EXISTS_TAC (← q r"-- &M"),
    STRIP_TAC,
    USE_THEN "Z-5" (SUBST1_TAC o GSYM),
    REWRITE_TAC [nmax],
    REWRITE_TAC [REAL_LE_NEG2, REAL_OF_NUM_LE] THEN ARITH_TAC,
    USE_THEN "Z-6" MP_TAC THEN REAL_ARITH_TAC,
    STRIP_TAC,
    /- save -/
    CLAIM (← q r"N <= k:num"),
    USE_THEN "Z-5" (SUBST1_TAC o GSYM),
    REWRITE_TAC [nmax] THEN ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"&0 < poly p (-- &k)"),
    ASM_MESON_TAC [],
    STRIP_TAC,
    CLAIM (← q r"&0 < poly p (-- &k) - poly p y"),
    LABEL_ALL_TAC,
    USE_ASSUM_LIST ["Z-10", "Z-3"] MP_TAC THEN REAL_ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"(-- &k - y) * poly (poly_diff p) x < &0"),
    REWRITE_TAC [REAL_MUL_LT],
    ASM_REWRITE_TAC [],
    POP_ASSUM MP_TAC,
    USE_THEN "Z-0" MP_TAC,
    REAL_ARITH_TAC
  ])
  /- }}} -/

  let POLY_DIFF_DOWN_LEFT ← do
    -- the rules of the tactic list, right to left
    let t5 ← ARITH_RULE (← q r"x < y <=> ~(y <= x)")
    let t4 ← ARITH_RULE (← q r"~(x < &0 /\ &0 < x)")
    let t3 ← ARITH_RULE (← q r"x < y <=> ~(y < x) /\ ~(y = x)")
    let t2 ← ARITH_RULE (← q r"~(x < &0 /\ &0 < x)")
    let t1 ← REAL_ARITH (← q r"x < y <=> ~(x = y) /\ ~(y < x)")
    prove_by_refinement (
   (← q r"!p. nonconstant p /\ (?X. !x. x < X ==> &0 < poly (poly_diff p) x) ==>
     (?Y. !y. y < Y ==> poly p y < &0)"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    CLAIM (← q r"mono_unbounded_below (\n. poly p (-- &n))"),
    REWRITE_TAC [POLY_PNEG],
    DISJ_CASES_TAC (← ISPEC (← q r"degree p") EVEN_OR_ODD),
    MATCH_MP_TAC mua_quotient_limit_neg,
    EXISTS_TAC (← q r"&1"),
    EXISTS_TAC (← q r"(\n. LAST (pneg p) * &n pow degree (pneg p))"),
    REPEAT STRIP_TAC,
    REAL_ARITH_TAC,
    BETA_TAC,
    MATCH_MP_TAC LIM_POLY2,
    MATCH_EQ_MP_TAC NORMAL_PNEG,
    ASM_MESON_TAC [nonconstant],
    MATCH_MP_TAC POW_UNBB_CON,
    STRIP_TAC,
    REWRITE_TAC [DEGREE_PNEG],
    REWRITE_TAC [degree],
    CLAIM (← q r"normalize p = p"),
    ASM_MESON_TAC [nonconstant, normal],
    DISCH_THEN SUBST1_TAC,
    CLAIM (← q r"~(LENGTH p = 0)"),
    ASM_MESON_TAC [nonconstant, normal, LENGTH_NZ, LENGTH_0, degree],
    STRIP_TAC,
    CLAIM (← q r"~(LENGTH p = 1)"),
    ASM_MESON_TAC [nonconstant, normal, LENGTH_NZ, LENGTH_1, degree],
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    /- save -/
    CLAIM (← q r"LAST (pneg p) = LAST p"),
    ASM_MESON_TAC [← GSYM POLY_PNEG_LAST, nonconstant],
    DISCH_THEN SUBST1_TAC,
    ONCE_REWRITE_TAC [t1],
    STRIP_TAC,
    ASM_MESON_TAC [NORMAL_ID, nonconstant],
    STRIP_TAC,
    CLAIM (← q r"ODD (degree (poly_diff p))"),
    ASM_SIMP_TAC [poly_diff_parity2],
    STRIP_TAC,
    CLAIM (← q r"nonconstant (poly_diff p)"),
    MATCH_MP_TAC normal_nonconstant,
    STRIP_TAC,
    MATCH_MP_TAC NONCONSTANT_DIFF_NORMAL,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"mono_unbounded_below (\n. poly (poly_diff p) (-- &n))"),
    MATCH_MP_TAC LAST_UNB_ODD_POS,
    ASM_REWRITE_TAC [],
    ASM_MESON_TAC [POLY_DIFF_LAST_GT],
    REWRITE_TAC [mono_unbounded_below],
    DISCH_THEN (MP_TAC o ISPEC (← q r"&0")),
    STRIP_TAC,
    /- save -/
    MP_TAC (← ISPEC (← q r"-- (X - &1)") REAL_ARCH_SIMPLE),
    DISCH_THEN (X_CHOOSE_TAC (← q r"M:num")),
    CLAIM (← q r"-- &M <= X - &1"),
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    STRIP_TAC,
    LABEL_ALL_TAC,
    USE_THEN "Z-2" (MP_TAC o ISPEC (← q r"nmax M N")),
    STRIP_TAC,
    CLAIM (← q r"N <= nmax M N"),
    REWRITE_TAC [nmax_le],
    DISCH_THEN (fun x => REWRITE_ASSUMS (list x)),
    CLAIM (← q r"-- &(nmax M N) < X"),
    MATCH_MP_TAC REAL_LET_TRANS,
    EXISTS_TAC (← q r"-- &M"),
    STRIP_TAC,
    REWRITE_TAC [nmax],
    REWRITE_TAC [REAL_LE_NEG2, REAL_OF_NUM_LE] THEN ARITH_TAC,
    USE_THEN "Z-0" MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    ASM_MESON_TAC [t2],
    /- save -/
    REWRITE_TAC [← GSYM POLY_PNEG],
    MATCH_MP_TAC LAST_UNB_ODD_POS,
    ASM_REWRITE_TAC [],
    ASM_SIMP_TAC [← GSYM POLY_DIFF_LAST_GT],
    CASES_ON (← q r"?x. poly_diff p = [x]"),
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    ASM_REWRITE_TAC [LAST],
    LABEL_ALL_TAC,
    USE_THEN "Z-2" MP_TAC,
    POP_ASSUM (fun x => REWRITE_TAC [x] THEN ASSUME_TAC x),
    REWRITE_TAC [poly],
    REAL_SIMP_TAC,
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    EXISTS_TAC (← q r"X - &1"),
    REAL_ARITH_TAC,
    CLAIM (← q r"nonconstant (poly_diff p)"),
    REWRITE_TAC [nonconstant],
    STRIP_TAC,
    MATCH_MP_TAC POLY_DIFF_NORMAL,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    ASM_MESON_TAC [],
    STRIP_TAC,
    CLAIM (← q r"EVEN (degree (poly_diff p))"),
    ASM_MESON_TAC [poly_diff_parity],
    STRIP_TAC,
    ONCE_REWRITE_TAC [t3],
    REPEAT STRIP_TAC,
    CLAIM (← q r"mono_unbounded_below (\n. poly (poly_diff p) (-- (&n)))"),
    MATCH_MP_TAC LAST_UNBB_EVEN_NEG,
    ASM_REWRITE_TAC [],
    REWRITE_TAC [mono_unbounded_below],
    DISCH_THEN (MP_TAC o ISPEC (← q r"&0")),
    STRIP_TAC,
    /- save -/
    MP_TAC (← ISPEC (← q r"-- (X - &1)") REAL_ARCH_SIMPLE),
    DISCH_THEN (X_CHOOSE_TAC (← q r"M:num")),
    CLAIM (← q r"-- &M <= X - &1"),
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC,
    STRIP_TAC,
    LABEL_ALL_TAC,
    USE_THEN "Z-2" (MP_TAC o ISPEC (← q r"nmax M N")),
    STRIP_TAC,
    CLAIM (← q r"N <= nmax M N"),
    REWRITE_TAC [nmax_le],
    DISCH_THEN (fun x => REWRITE_ASSUMS (list x)),
    CLAIM (← q r"-- &(nmax M N) < X"),
    MATCH_MP_TAC REAL_LET_TRANS,
    EXISTS_TAC (← q r"-- &M"),
    STRIP_TAC,
    REWRITE_TAC [nmax],
    REWRITE_TAC [REAL_LE_NEG2, REAL_OF_NUM_LE] THEN ARITH_TAC,
    USE_THEN "Z-0" MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    ASM_MESON_TAC [t4],
    ASM_MESON_TAC [nonconstant, NORMAL_ID],
    /- save -/
    REWRITE_TAC [mono_unbounded_below],
    DISCH_THEN (MP_TAC o ISPEC (← q r"&0")),
    STRIP_TAC,
    MP_TAC (← ISPEC (← q r"-- (X - &1)") REAL_ARCH_SIMPLE),
    DISCH_THEN (X_CHOOSE_TAC (← q r"M:num")),
    ABBREV_TAC (← q r"k = nmax N M"),
    EXISTS_TAC (← q r"-- &k"),
    REPEAT STRIP_TAC,
    REWRITE_TAC [t5],
    STRIP_TAC,
    MP_TAC (← ISPECL [← q r"p:real list", ← q r"y:real", ← q r"-- &k"] POLY_MVT),
    ASM_REWRITE_TAC [],
    STRIP_TAC,
    LABEL_ALL_TAC,
    CLAIM (← q r"&0 < (-- &k) - y"),
    USE_THEN "Z-4" MP_TAC THEN REAL_ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"&0 < poly (poly_diff p) x"),
    FIRST_ASSUM MATCH_MP_TAC,
    MATCH_MP_TAC REAL_LTE_TRANS,
    EXISTS_TAC (← q r"-- &k"),
    ASM_REWRITE_TAC [],
    MATCH_MP_TAC REAL_LE_TRANS,
    EXISTS_TAC (← q r"-- &M"),
    STRIP_TAC,
    USE_THEN "Z-5" (SUBST1_TAC o GSYM),
    REWRITE_TAC [nmax],
    REWRITE_TAC [REAL_LE_NEG2, REAL_OF_NUM_LE] THEN ARITH_TAC,
    USE_THEN "Z-6" MP_TAC THEN REAL_ARITH_TAC,
    STRIP_TAC,
    /- save -/
    CLAIM (← q r"N <= k:num"),
    USE_THEN "Z-5" (SUBST1_TAC o GSYM),
    REWRITE_TAC [nmax] THEN ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"poly p (-- &k) < &0"),
    ASM_MESON_TAC [],
    STRIP_TAC,
    CLAIM (← q r"poly p (-- &k) - poly p y < &0"),
    LABEL_ALL_TAC,
    USE_ASSUM_LIST ["Z-10", "Z-3"] MP_TAC THEN REAL_ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"&0 < (-- &k - y) * poly (poly_diff p) x"),
    REWRITE_TAC [REAL_MUL_GT],
    ASM_REWRITE_TAC [],
    POP_ASSUM MP_TAC,
    USE_THEN "Z-0" MP_TAC,
    REAL_ARITH_TAC
  ])
  /- }}} -/

  let POLY_DIFF_DOWN_LEFT2 ← prove_by_refinement (
   (← q r"!p X. nonconstant p /\ (!x. x < X ==> &0 < poly (poly_diff p) x) ==>
     (?Y. Y < X /\ (!y. y < Y ==> poly p y < &0))"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    MP_TAC (← ISPEC (← q r"p:real list") POLY_DIFF_DOWN_LEFT),
    ASM_REWRITE_TAC [],
    ANTS_TAC,
    ASM_MESON_TAC [],
    STRIP_TAC,
    EXISTS_TAC (← q r"min X Y - &1"),
    REPEAT STRIP_TAC,
    REAL_ARITH_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC
  ])
  /- }}} -/

  let POLY_DIFF_UP_LEFT2 ← prove_by_refinement (
   (← q r"!p X. nonconstant p /\ (!x. x < X ==> poly (poly_diff p) x < &0) ==>
     (?Y. Y < X /\ (!y. y < Y ==> &0 < poly p y))"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    MP_TAC (← ISPEC (← q r"p:real list") POLY_DIFF_UP_LEFT),
    ASM_REWRITE_TAC [],
    ANTS_TAC,
    ASM_MESON_TAC [],
    STRIP_TAC,
    EXISTS_TAC (← q r"min X Y - &1"),
    REPEAT STRIP_TAC,
    REAL_ARITH_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC
  ])
  /- }}} -/

  let POLY_DIFF_DOWN_LEFT3 ← prove_by_refinement (
   (← q r"!p p' X. nonconstant p ==> (poly_diff p = p') ==>
     (!x. x < X ==> &0 < poly p' x) ==>
       (?Y. Y < X /\ (!y. y < Y ==> poly p y < &0))"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    MP_TAC (← ISPEC (← q r"p:real list") POLY_DIFF_DOWN_LEFT),
    ASM_REWRITE_TAC [],
    ANTS_TAC,
    ASM_MESON_TAC [],
    STRIP_TAC,
    EXISTS_TAC (← q r"min X Y - &1"),
    REPEAT STRIP_TAC,
    REAL_ARITH_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC
  ])
  /- }}} -/

  let POLY_DIFF_UP_LEFT3 ← prove_by_refinement (
   (← q r"!p p' X. nonconstant p ==> (poly_diff p = p') ==>
     (!x. x < X ==> poly p' x < &0) ==>
       (?Y. Y < X /\ (!y. y < Y ==> &0 < poly p y))"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    MP_TAC (← ISPEC (← q r"p:real list") POLY_DIFF_UP_LEFT),
    ASM_REWRITE_TAC [],
    ANTS_TAC,
    ASM_MESON_TAC [],
    STRIP_TAC,
    EXISTS_TAC (← q r"min X Y - &1"),
    REPEAT STRIP_TAC,
    REAL_ARITH_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC
  ])
  /- }}} -/

  let POLY_DIFF_DOWN_LEFT4 ← prove_by_refinement (
   (← q r"!p p' X. nonconstant p ==> (poly_diff p = p') ==>
     (!x. x < X ==> &0 < poly p' x) ==>
       (?Y. Y < X /\ (!y. y <= Y ==> poly p y < &0))"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    MP_TAC (← ISPECL [← q r"p:real list", ← q r"p':real list", ← q r"X:real"] POLY_DIFF_DOWN_LEFT3),
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    EXISTS_TAC (← q r"Y - &1"),
    STRIP_TAC,
    POP_ASSUM IGNORE,
    POP_ASSUM MP_TAC,
    REAL_ARITH_TAC,
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC
  ])
  /- }}} -/

  let POLY_DIFF_UP_LEFT4 ← prove_by_refinement (
   (← q r"!p p' X. nonconstant p ==> (poly_diff p = p') ==>
     (!x. x < X ==> poly p' x < &0) ==>
       (?Y. Y < X /\ (!y. y <= Y ==> &0 < poly p y))"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    MP_TAC (← ISPECL [← q r"p:real list", ← q r"p':real list", ← q r"X:real"] POLY_DIFF_UP_LEFT3),
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    EXISTS_TAC (← q r"Y - &1"),
    STRIP_TAC,
    POP_ASSUM IGNORE,
    POP_ASSUM MP_TAC,
    REAL_ARITH_TAC,
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC
  ])
  /- }}} -/

  let POLY_DIFF_DOWN_LEFT5 ← prove_by_refinement (
   (← q r"!p p' X. nonconstant p ==> (poly_diff p = p') ==>
     (!x. x < X ==> poly p' x > &0) ==>
       (?Y. Y < X /\ (!y. y <= Y ==> poly p y < &0))"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [real_gt],
    ASM_MESON_TAC [POLY_DIFF_DOWN_LEFT4]
  ])
  /- }}} -/

  let POLY_DIFF_UP_LEFT5 ← prove_by_refinement (
   (← q r"!p p' X. nonconstant p ==> (poly_diff p = p') ==>
     (!x. x < X ==> poly p' x < &0) ==>
       (?Y. Y < X /\ (!y. y <= Y ==> poly p y > &0))"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [real_gt],
    MESON_TAC [POLY_DIFF_UP_LEFT4]
  ])
  /- }}} -/

  let NORMAL_PDIFF_LEM ← do
    let a1 ← ARITH_RULE (← q r"~(1 = 0)")
    prove_by_refinement (
   (← q r"!p. normal (poly_diff p) ==> nonconstant p"),
  /- {{{ Proof -/
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [normal, poly_diff, poly_diff_aux],
    REWRITE_TAC [nonconstant],
    REWRITE_TAC [poly_diff, poly_diff_aux, NOT_CONS_NIL, TL],
    REPEAT STRIP_TAC,
    MATCH_MP_TAC NORMAL_CONS,
    ASM_MESON_TAC [POLY_DIFF_AUX_NORMAL, a1],
    CLAIM (← q r"t = []"),
    ASM_MESON_TAC (← deref LIST_REWRITES),
    DISCH_THEN (fun x => REWRITE_ASSUMS (list x)),
    ASM_MESON_TAC [normal, poly_diff_aux]
  ])
  /- }}} -/

  let NORMAL_PDIFF ← prove_by_refinement (
   (← q r"!p. nonconstant p = normal (poly_diff p)"),
  /- {{{ Proof -/
  [
    MESON_TAC [NORMAL_PDIFF_LEM, POLY_DIFF_NORMAL]
  ])
  /- }}} -/

  let POLY_DIFF_UP_RIGHT2 ← prove_by_refinement (
   (← q r"!p p' X. nonconstant p ==> (poly_diff p = p') ==>
       (!x. X < x ==> &0 < poly p' x) ==>
       (?Y. X < Y /\ (!y. Y <= y ==> &0 < poly p y))"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    MP_TAC (← ISPECL [← q r"p:real list"] (← GEN_ALL POLY_DIFF_UP_RIGHT)),
    ASM_REWRITE_TAC [],
    ANTS_TAC,
    ASM_MESON_TAC [],
    REPEAT STRIP_TAC,
    EXISTS_TAC (← q r"(max X Y) + &1"),
    STRIP_TAC,
    REAL_ARITH_TAC,
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC
  ])
  /- }}} -/

  let POLY_DIFF_DOWN_RIGHT2 ← prove_by_refinement (
   (← q r"!p p' X. nonconstant p ==> (poly_diff p = p') ==>
       (!x. X < x ==> poly p' x < &0) ==>
       (?Y. X < Y /\ (!y. Y <= y ==> poly p y < &0))"),
  /- {{{ Proof -/
  [
    REPEAT STRIP_TAC,
    MP_TAC (← ISPECL [← q r"p:real list"] (← GEN_ALL POLY_DIFF_DOWN_RIGHT)),
    ASM_REWRITE_TAC [],
    ANTS_TAC,
    ASM_MESON_TAC [],
    REPEAT STRIP_TAC,
    EXISTS_TAC (← q r"(max X Y) + &1"),
    STRIP_TAC,
    REAL_ARITH_TAC,
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC
  ])
  /- }}} -/

  let POLY_DIFF_UP_RIGHT3 ← prove_by_refinement (
   (← q r"!p p' X. nonconstant p ==> (poly_diff p = p') ==>
       (!x. X < x ==> poly p' x > &0) ==>
       (?Y. X < Y /\ (!y. Y <= y ==> poly p y > &0))"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [real_gt, real_ge],
    MESON_TAC [POLY_DIFF_UP_RIGHT2]
  ])
  /- }}} -/

  let POLY_DIFF_DOWN_RIGHT3 ← prove_by_refinement (
   (← q r"!p p' X. nonconstant p ==> (poly_diff p = p') ==>
       (!x. X < x ==> poly p' x < &0) ==>
       (?Y. X < Y /\ (!y. Y <= y ==> poly p y < &0))"),
  /- {{{ Proof -/
  [
    REWRITE_TAC [real_gt, real_ge],
    MESON_TAC [POLY_DIFF_DOWN_RIGHT2]
  ])
  /- }}} -/

  -- @@RETURN BEGIN
  return { poly_diff_parity, poly_diff_parity2, normal_nonconstant, nmax_le,
           POLY_DIFF_UP_LEFT, POLY_DIFF_DOWN_LEFT, POLY_DIFF_DOWN_LEFT2,
           POLY_DIFF_UP_LEFT2, POLY_DIFF_DOWN_LEFT3, POLY_DIFF_UP_LEFT3,
           POLY_DIFF_DOWN_LEFT4, POLY_DIFF_UP_LEFT4, POLY_DIFF_DOWN_LEFT5,
           POLY_DIFF_UP_LEFT5, NORMAL_PDIFF_LEM, NORMAL_PDIFF, POLY_DIFF_UP_RIGHT2,
           POLY_DIFF_DOWN_RIGHT2, POLY_DIFF_UP_RIGHT3, POLY_DIFF_DOWN_RIGHT3 }
  -- @@RETURN END

end HolRQE.Asym
