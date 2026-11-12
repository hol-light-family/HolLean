/- ========================================================================= -/
/- Rqe: basic arithmetic of the naturals in the simplifier.                -/
/- ========================================================================= -/
/- File: HolRQE/NumCalcSimp.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/num_calc_simp.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.NumCalcSimp fills them).

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

namespace HolRQE.NumCalcSimp

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  deriving Inhabited

/-- What num_calc_simp.ml uses from Session besides theorems. -/
structure NumCalcSimpDeps where
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
  NUM_SUC_CONV : ioconv
  NUM_PRE_CONV : ioconv
  NUM_FACT_CONV : ioconv
  NUM_REL_CONV : ioconv
  NUM_EVEN_CONV : ioconv
  NUM_ODD_CONV : ioconv
  NUM_ADD_CONV : ioconv
  NUM_MULT_CONV : ioconv
  NUM_EXP_CONV : ioconv
  NUM_MOD_CONV : ioconv
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
/-  Put basic arithmetic of the naturals into the simplifier, based on     -/
/-  NUM_RED_CONV in num_calc (num_calc_simp.ml 1-50)                       -/
/- ---------------------------------------------------------------------- -/

structure NumCalcSimpFns where
  -- @@FIELDS
  arith_ss : List thm → ExceptT String IO HolCore.Simp.simpset
  ARITH_SIMP_CONV : List thm → ioconv
  arith_net : Unit → ExceptT String IO (HolCore.Nets.net HolCore.Simp.gconv)
  ARITH_REWRITE_CONV : List thm → ioconv
  ARITH_SIMP_TAC : List thm → tactic
  deriving Inhabited

@[nospecialize]
def setupNumCalcSimpFns [HolBase] (D : NumCalcSimpDeps) :
    ExceptT String IO NumCalcSimpFns := do
  -- @@SCOPE BEGIN
  let { NUM_ADD_CONV, NUM_DIV_CONV, NUM_EVEN_CONV, NUM_EXP_CONV, NUM_FACT_CONV,
        NUM_MOD_CONV, NUM_MULT_CONV, NUM_ODD_CONV, NUM_PRE_CONV, NUM_REL_CONV,
        NUM_SUB_CONV, NUM_SUC_CONV, basic_ss, .. } := D
  -- @@SCOPE END

  -- `arith_ss thml` and `arith_net()` parse their key terms on each call, as
  -- OCaml does (the list literal is in the function body)
  let arith_ss : List thm → ExceptT String IO HolCore.Simp.simpset ← pure (fun thml => do
    let ss0 ← ExceptT.mk (basic_ss thml)
    let l : List (term × ioconv) := [
      (← q r"SUC(NUMERAL n)", NUM_SUC_CONV),
      (← q r"PRE(NUMERAL n)", NUM_PRE_CONV),
      (← q r"FACT(NUMERAL n)", NUM_FACT_CONV),
      (← q r"NUMERAL m < NUMERAL n", NUM_REL_CONV),
      (← q r"NUMERAL m <= NUMERAL n", NUM_REL_CONV),
      (← q r"NUMERAL m > NUMERAL n", NUM_REL_CONV),
      (← q r"NUMERAL m >= NUMERAL n", NUM_REL_CONV),
      (← q r"NUMERAL m = NUMERAL n", NUM_REL_CONV),
      (← q r"EVEN(NUMERAL n)", NUM_EVEN_CONV),
      (← q r"ODD(NUMERAL n)", NUM_ODD_CONV),
      (← q r"NUMERAL m + NUMERAL n", NUM_ADD_CONV),
      (← q r"NUMERAL m - NUMERAL n", NUM_SUB_CONV),
      (← q r"NUMERAL m * NUMERAL n", NUM_MULT_CONV),
      (← q r"(NUMERAL m) EXP (NUMERAL n)", NUM_EXP_CONV),
      (← q r"(NUMERAL m) DIV (NUMERAL n)", NUM_DIV_CONV),
      (← q r"(NUMERAL m) MOD (NUMERAL n)", NUM_MOD_CONV)]
    -- itlist: the last pair is added first
    l.foldrM (fun (x, y) ss => ExceptT.mk (HolCore.Simp.ss_of_conv x y ss)) ss0)

  let ARITH_SIMP_CONV : List thm → ioconv ← pure (fun thl => fun tm => ExceptT.run do
    let c ← ExceptT.mk (HolCore.Simp.SIMPLIFY_CONV HolBase.B (← arith_ss []) thl)
    ExceptT.mk (c tm))

  let arith_net : Unit → ExceptT String IO (HolCore.Nets.net HolCore.Simp.gconv) ← pure (fun () => do
    let n0 ← HolCore.Simp.basic_net
    let l : List (term × ioconv) := [
      (← q r"SUC(NUMERAL n)", NUM_SUC_CONV),
      (← q r"PRE(NUMERAL n)", NUM_PRE_CONV),
      (← q r"FACT(NUMERAL n)", NUM_FACT_CONV),
      (← q r"NUMERAL m < NUMERAL n", NUM_REL_CONV),
      (← q r"NUMERAL m <= NUMERAL n", NUM_REL_CONV),
      (← q r"NUMERAL m > NUMERAL n", NUM_REL_CONV),
      (← q r"NUMERAL m >= NUMERAL n", NUM_REL_CONV),
      (← q r"NUMERAL m = NUMERAL n", NUM_REL_CONV),
      (← q r"EVEN(NUMERAL n)", NUM_EVEN_CONV),
      (← q r"ODD(NUMERAL n)", NUM_ODD_CONV),
      (← q r"NUMERAL m + NUMERAL n", NUM_ADD_CONV),
      (← q r"NUMERAL m - NUMERAL n", NUM_SUB_CONV),
      (← q r"NUMERAL m * NUMERAL n", NUM_MULT_CONV),
      (← q r"(NUMERAL m) EXP (NUMERAL n)", NUM_EXP_CONV),
      (← q r"(NUMERAL m) DIV (NUMERAL n)", NUM_DIV_CONV),
      (← q r"(NUMERAL m) MOD (NUMERAL n)", NUM_MOD_CONV)]
    l.foldrM (fun (x, y) nt => ExceptT.mk (HolCore.Simp.net_of_conv x y nt)) n0)

  let ARITH_REWRITE_CONV : List thm → ioconv ← pure (fun thl => fun tm => ExceptT.run do
    let c ← ExceptT.mk (HolCore.Simp.GENERAL_REWRITE_CONV HolBase.B true TOP_DEPTH_CONV
      (← arith_net ()) thl)
    ExceptT.mk (c tm))

  let ARITH_SIMP_TAC : List thm → tactic ← pure (fun thl => CONV_TAC (ARITH_SIMP_CONV thl))

  -- @@RETURN BEGIN
  return { arith_ss, ARITH_SIMP_CONV, arith_net, ARITH_REWRITE_CONV, ARITH_SIMP_TAC }
  -- @@RETURN END

end HolRQE.NumCalcSimp
