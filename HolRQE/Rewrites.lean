/- ========================================================================= -/
/- Rqe: extensible lists of num and real rewrites.                         -/
/- ========================================================================= -/
/- File: HolRQE/Rewrites.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/rewrites.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.Rewrites fills them).

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

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolRQE.RqeLib
open HolRQE.RqeTacticsExt
open HolRQE.Util

namespace HolRQE.Rewrites

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (GE GT LET_TRANS LE_TRANS LTE_TRANS LT_TRANS PRE REAL_ADD_ASSOC
   REAL_ADD_LDISTRIB REAL_ADD_LID REAL_ADD_RDISTRIB REAL_ADD_RID REAL_ADD_SYM
   REAL_INV_INV REAL_INV_MUL REAL_LET_TRANS REAL_LE_LT REAL_LE_MUL REAL_LE_REFL
   REAL_LE_TRANS REAL_LTE_TRANS REAL_LT_INV REAL_LT_LE REAL_LT_REFL
   REAL_LT_TRANS REAL_MAX_MAX REAL_MUL_ASSOC REAL_MUL_LID REAL_MUL_LZERO
   REAL_MUL_RID REAL_MUL_RZERO REAL_MUL_SYM REAL_NEG_0 REAL_NEG_MUL2
   REAL_NEG_NEG REAL_NOT_LE REAL_NOT_LT REAL_OF_NUM_LT REAL_POW_1 REAL_POW_ONE
   real_div real_ge real_gt real_pow : thm)
  deriving Inhabited

/-- What rewrites.ml uses from Session besides theorems. -/
structure RewritesDeps where
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

/-- OCaml's `!r` on a bundle's exported ref (an `Option`, as a structure with
    an `IO.Ref` field cannot derive `Inhabited` computably; it is `some` once
    the bundle is built). -/
def deref {α : Type} (r : Option (IO.Ref α)) : ExceptT String IO α :=
  match r with
  | some r => r.get
  | none => throw "deref: bundle not built"



/- ---------------------------------------------------------------------- -/
/-  Num and Real rewrites (rewrites.ml 1-90)                              -/
/- ---------------------------------------------------------------------- -/

structure RewritesFns where
  -- @@FIELDS
  NUM_REWRITES : Option (IO.Ref (List thm))
  NUM_SIMP_TAC : tactic
  extend_num_rewrites : List thm → IO Unit
  REAL_REWRITES : Option (IO.Ref (List thm))
  REAL_ELIM : Option (IO.Ref (List thm))
  REAL_SIMP_TAC : tactic
  REAL_SOLVE_TAC : tactic
  extend_real_rewrites : List thm → IO Unit
  BASIC_REWRITES : Option (IO.Ref (List thm))
  deriving Inhabited

@[nospecialize]
def setupRewritesFns [HolBase] (D : RewritesDeps) :
    ExceptT String IO RewritesFns := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, REAL_ARITH, .. } := D
  let { GE, GT, LET_TRANS, LE_TRANS, LTE_TRANS, LT_TRANS, PRE, REAL_ADD_ASSOC,
        REAL_ADD_LDISTRIB, REAL_ADD_LID, REAL_ADD_RDISTRIB, REAL_ADD_RID, REAL_ADD_SYM,
        REAL_INV_INV, REAL_INV_MUL, REAL_LET_TRANS, REAL_LE_LT, REAL_LE_MUL,
        REAL_LE_REFL, REAL_LE_TRANS, REAL_LTE_TRANS, REAL_LT_INV, REAL_LT_LE,
        REAL_LT_REFL, REAL_LT_TRANS, REAL_MAX_MAX, REAL_MUL_ASSOC, REAL_MUL_LID,
        REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RZERO, REAL_MUL_SYM, REAL_NEG_0,
        REAL_NEG_MUL2, REAL_NEG_NEG, REAL_NOT_LE, REAL_NOT_LT, REAL_OF_NUM_LT,
        REAL_POW_1, REAL_POW_ONE, real_div, real_ge, real_gt, real_pow, .. } := D.core1
  -- @@SCOPE END

  -- The refs are created once, when this (cached) setup runs at load, and
  -- exported as `some ref` (a structure with an `IO.Ref` field cannot
  -- derive `Inhabited` computably).  OCaml evaluates the list literals
  -- right to left, so their ARITH_RULEs are bound last first.

  -- Num
  let loc_NUM_REWRITES : IO.Ref (List thm) ← do
    let a4 ← ARITH_RULE (← q r"x * 1 = x")
    let a3 ← ARITH_RULE (← q r"1 * x = x")
    let a2 ← ARITH_RULE (← q r"0 + x = x")
    let a1 ← ARITH_RULE (← q r"x + 0 = x")
    IO.mkRef [
      LT_TRANS,
      LET_TRANS,
      LTE_TRANS,
      LE_TRANS,
      GT,
      GE,
      PRE,
      a1,
      a2,
      a3,
      a4
    ]
  let NUM_REWRITES : Option (IO.Ref (List thm)) ← pure (some loc_NUM_REWRITES)

  let NUM_SIMP_TAC : tactic ← do pure (REWRITE_TAC (← loc_NUM_REWRITES.get))

  let extend_num_rewrites : List thm → IO Unit ← pure (fun l => do
    loc_NUM_REWRITES.set ((← loc_NUM_REWRITES.get) ++ l))

  -- Real
  let loc_REAL_REWRITES : IO.Ref (List thm) ← do
    let a5 ← ARITH_RULE (← q r"x - x = &0")
    let a4 ← ARITH_RULE (← q r"-- (-- x * y) = x * y")
    let a3 ← ARITH_RULE (← q r"-- &1 * -- &1 = &1")
    let a2 ← ARITH_RULE (← q r"-- &1 * x = -- x")
    let r1 ← REAL_ARITH (← q r"x - &0 = x")
    IO.mkRef [
      REAL_MUL_LID,
      REAL_MUL_RID,
      REAL_MUL_RZERO,
      REAL_MUL_LZERO,
      REAL_LT_TRANS,
      REAL_LET_TRANS,
      REAL_LTE_TRANS,
      REAL_LE_TRANS,
      REAL_LE_MUL,
      REAL_NOT_LT,
      REAL_LT_REFL,
      REAL_LE_REFL,
      REAL_ADD_RID,
      REAL_ADD_LID,
      REAL_ADD_LDISTRIB,
      REAL_ADD_RDISTRIB,
      REAL_NEG_0,
      REAL_NEG_MUL2,
      REAL_OF_NUM_LT,
      REAL_MAX_MAX,
      real_pow,
      r1,
      REAL_NOT_LT,
      REAL_NOT_LE,
      REAL_INV_INV,
      REAL_INV_MUL,
      real_gt,
      real_ge,
      REAL_POW_1,
      a2,
      a3,
      a4,
      a5,
      REAL_POW_ONE,
      REAL_NEG_NEG
    ]
  let REAL_REWRITES : Option (IO.Ref (List thm)) ← pure (some loc_REAL_REWRITES)

  let loc_REAL_ELIM : IO.Ref (List thm) ← IO.mkRef [
      REAL_LT_INV,
      REAL_ADD_SYM,
      REAL_ADD_ASSOC,
      REAL_MUL_SYM,
      REAL_MUL_ASSOC,
      REAL_LT_LE,
      REAL_LE_LT,
      real_div
    ]
  let REAL_ELIM : Option (IO.Ref (List thm)) ← pure (some loc_REAL_ELIM)

  let REAL_SIMP_TAC : tactic ← do pure (REWRITE_TAC (
    (← loc_REAL_REWRITES.get)
  ))

  let REAL_SOLVE_TAC : tactic ← do
    pure (ASM_MESON_TAC ((← loc_REAL_REWRITES.get) ++ (← loc_REAL_ELIM.get)))

  let extend_real_rewrites : List thm → IO Unit ← pure (fun l => do
    loc_REAL_REWRITES.set ((← loc_REAL_REWRITES.get) ++ l))

  let loc_BASIC_REWRITES : IO.Ref (List thm) ← do
    IO.mkRef ((← loc_REAL_REWRITES.get) ++ (← loc_NUM_REWRITES.get))
  let BASIC_REWRITES : Option (IO.Ref (List thm)) ← pure (some loc_BASIC_REWRITES)

  -- @@RETURN BEGIN
  return { NUM_REWRITES, NUM_SIMP_TAC, extend_num_rewrites, REAL_REWRITES, REAL_ELIM,
           REAL_SIMP_TAC, REAL_SOLVE_TAC, extend_real_rewrites, BASIC_REWRITES }
  -- @@RETURN END

end HolRQE.Rewrites
