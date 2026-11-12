/- ========================================================================= -/
/- Rqe: list rewrites.                                                     -/
/- ========================================================================= -/
/- File: HolRQE/ListRewrites.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/list_rewrites.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.ListRewrites fills them).

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

namespace HolRQE.ListRewrites

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CONS_11 HD LAST LENGTH NOT_CONS_NIL TL list_CASES : thm)
  deriving Inhabited

/-- What list_rewrites.ml uses from Session besides theorems. -/
structure ListRewritesDeps where
  new_definition : String → ExceptT String IO thm
  define : String → ExceptT String IO thm
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
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
/-  List (list_rewrites.ml 1-36)                                          -/
/- ---------------------------------------------------------------------- -/

structure ListRewritesFns where
  -- @@FIELDS
  NOT_NIL : thm
  LIST_REWRITES : Option (IO.Ref (List thm))
  LIST_SIMP_TAC : tactic
  extend_list_rewrites : List thm → IO Unit
  deriving Inhabited

@[nospecialize]
def setupListRewritesFns [HolBase] (D : ListRewritesDeps) :
    ExceptT String IO ListRewritesFns := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, BASIC_REWRITES, MESON_TAC, prove_by_refinement, .. } := D
  let { CONS_11, HD, LAST, LENGTH, NOT_CONS_NIL, TL, list_CASES, .. } := D.core1
  -- @@SCOPE END

  let NOT_NIL ← prove_by_refinement (
   (← q r"!l. ~(l = []) <=> ?(h:A) t. l = CONS h t"),
  /- {{{ Proof -/

  [
    STRIP_TAC THEN EQ_TAC,
    MESON_TAC [list_CASES],
    STRIP_TAC,
    ASM_MESON_TAC [NOT_CONS_NIL]
  ])

  /- }}} -/

  -- the ref is created once, when this (cached) setup runs at load, and
  -- exported as `some ref` (see HolRQE/Rewrites.lean)
  let loc_LIST_REWRITES : IO.Ref (List thm) ← IO.mkRef [
      NOT_CONS_NIL,
      HD,
      TL,
      CONS_11,
      LENGTH,
      LAST,
      list_CASES,
      NOT_NIL
    ]
  let LIST_REWRITES : Option (IO.Ref (List thm)) ← pure (some loc_LIST_REWRITES)

  let LIST_SIMP_TAC : tactic ← do pure (REWRITE_TAC (
    (← loc_LIST_REWRITES.get)
  ))

  let extend_list_rewrites : List thm → IO Unit ← pure (fun l => do
    loc_LIST_REWRITES.set ((← loc_LIST_REWRITES.get) ++ l))

  -- `BASIC_REWRITES := !LIST_REWRITES @ !BASIC_REWRITES` (rewrites.ml's ref)
  match BASIC_REWRITES with
  | some r => r.set ((← loc_LIST_REWRITES.get) ++ (← r.get))
  | none => throw "BASIC_REWRITES"

  -- @@RETURN BEGIN
  return { NOT_NIL, LIST_REWRITES, LIST_SIMP_TAC, extend_list_rewrites }
  -- @@RETURN END

end HolRQE.ListRewrites
