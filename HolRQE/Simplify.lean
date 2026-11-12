/- ========================================================================= -/
/- Rqe: propositional simplification and evaluation of rational atoms.     -/
/- ========================================================================= -/
/- File: HolRQE/Simplify.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/simplify.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml, Rqe/num_calc_simp.ml, Rqe/asym.ml, Rqe/rol.ml, Rqe/poly_ext.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.Simplify fills them).

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

namespace HolRQE.Simplify

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  deriving Inhabited

/-- What simplify.ml uses from Session besides theorems. -/
structure SimplifyDeps where
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
  REAL_RAT_LT_CONV : ioconv
  REAL_RAT_GT_CONV : ioconv
  REAL_RAT_GE_CONV : ioconv
  REAL_RAT_LE_CONV : ioconv
  REAL_RAT_EQ_CONV : ioconv
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

/-- simplify.ml's `SIMPLIFY_CONV` (a `let rec` over an inner `let`), given
    the terms that `let` binds and SIMPLIFY1_CONV. -/
partial def SIMPLIFY_CONV.go [HolBase] (not_tm ex_tm : term) (SIMPLIFY1_CONV : ioconv) : ioconv :=
  fun fm => ExceptT.run do
  let rec_ := SIMPLIFY_CONV.go not_tm ex_tm SIMPLIFY1_CONV
  if is_neg fm then
    let thm1 ← ExceptT.mk (rec_ (← liftExcept (dest_neg fm)))
    let thm2 ← AP_TERM not_tm thm1
    let (_l, r) ← liftExcept (dest_eq (concl thm2))
    let thm3 ← ExceptT.mk (SIMPLIFY1_CONV r)
    TRANS thm2 thm3
  else if is_conj fm || is_disj fm || is_imp fm || HolCore.Bool.is_iff fm then
    let (op, l, r) ← liftExcept (get_binop fm)
    let l_thm ← ExceptT.mk (rec_ l)
    let r_thm ← ExceptT.mk (rec_ r)
    let a_thm ← (curry MK_COMB) (← AP_TERM op l_thm) r_thm
    let (_al, ar) ← liftExcept (dest_eq (concl a_thm))
    let thm ← ExceptT.mk (SIMPLIFY1_CONV ar)
    TRANS a_thm thm
  else if is_forall fm || is_exists fm then
    let (x, bod) ← liftExcept (dest_quant fm)
    let bod_thm ← ExceptT.mk (rec_ bod)
    let lam_thm ← liftExcept (HolCore.Kernel.ABS x bod_thm)
    let q_thm ← AP_TERM ex_tm lam_thm
    let (_l, r) ← liftExcept (dest_eq (concl q_thm))
    let thm ← ExceptT.mk (SIMPLIFY1_CONV r)
    TRANS q_thm thm
  else pure (REFL fm)



/- ---------------------------------------------------------------------- -/
/-  Simplification (simplify.ml 1-189; the commented-out OCaml versions    -/
/-  of the functions are in simplify.ml)                                   -/
/- ---------------------------------------------------------------------- -/

structure SimplifyFns where
  -- @@FIELDS
  PSIMPLIFY1_CONV : ioconv
  SIMPLIFY1_CONV : ioconv
  SIMPLIFY_CONV : ioconv
  REAL_LEAF_CONV : ioconv
  EVALC_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupSimplifyFns [HolBase] (D : SimplifyDeps) :
    ExceptT String IO SimplifyFns := do
  -- @@SCOPE BEGIN
  let { REAL_RAT_EQ_CONV, REAL_RAT_GE_CONV, REAL_RAT_GT_CONV, REAL_RAT_LE_CONV,
        REAL_RAT_LT_CONV, dest_beq, req, rge, rgt, rle, rlt, .. } := D
  -- @@SCOPE END

  -- the `try .. with _ -> REFL fm` catches every failure of its body
  let PSIMPLIFY1_CONV : ioconv ← do
    let nt ← q r"~T"
    let t ← q r"T"
    let f ← q r"F"
    let nf ← q r"~F"
    pure (fun fm => do
      let r ← (ExceptT.run (do
        let fm' ←
          if fm == nt then pure f
          else if fm == nf then pure t
          else if is_conj fm then do
            let (l, r) ← liftExcept (dest_conj fm)
            if l == f || r == f then pure f
            else if l == t then pure r
            else if r == t then pure l
            else pure fm
          else if is_disj fm then do
            let (l, r) ← liftExcept (dest_disj fm)
            if l == t || r == t then pure t
            else if l == f then pure r
            else if r == f then pure l
            else pure fm
          else if is_imp fm then do
            let (l, r) ← liftExcept (dest_imp fm)
            if l == f then pure t
            else if r == t then pure t
            else if l == t then pure r
            else if r == f then liftExcept (HolCore.Bool.mk_neg l)
            else pure fm
          else if HolCore.Bool.is_iff fm then do
            let (l, r) ← liftExcept (dest_beq fm)
            if l == f then liftExcept (HolCore.Bool.mk_neg r)
            else if l == t then pure r
            else if r == t then pure l
            else if r == f then liftExcept (HolCore.Bool.mk_neg l)
              else pure fm
          else throw "PSIMPLIFY: 0"
        let mkEq ← ExceptT.mk _root_.mk_eq
        let fm'' ← liftExcept (mkEq (fm, fm'))
        ExceptT.mk (HolCore.Tactics.prove HolBase.B fm'' (REWRITE_TAC [])) : ExceptT String IO thm))
      match r with
      | .ok th => pure (.ok th)
      | .error _ => pure (.ok (REFL fm)))

  /-
  let fm = `T /\ T`
  PSIMPLIFY1_CONV `T /\ A`
  -/

  let SIMPLIFY1_CONV : ioconv ← pure (fun fm => ExceptT.run do
    if is_forall fm || is_exists fm then
      let (x, p) ← liftExcept (dest_forall fm)
      if mem x (frees p) then pure (REFL fm)
      else do
        let mkEq ← ExceptT.mk _root_.mk_eq
        ExceptT.mk (HolCore.Tactics.prove HolBase.B (← liftExcept (mkEq (fm, p))) (REWRITE_TAC []))
    else ExceptT.mk (PSIMPLIFY1_CONV fm))

  let SIMPLIFY_CONV : ioconv ← do
    let not_tm ← q r"(~)"
    let ex_tm ← q r"(?)"
    pure (SIMPLIFY_CONV.go not_tm ex_tm SIMPLIFY1_CONV)



  /-

  SIMPLIFY_CONV `T /\ T \/ F`

  (the commented-out OCaml evalc is in simplify.ml)
  -/

  let REAL_LEAF_CONV : ioconv ← pure (fun fm => ExceptT.run do
    let (op, _l, _r) ← liftExcept (get_binop fm)
    if op == rlt then
      ExceptT.mk (REAL_RAT_LT_CONV fm)
    else if op == rgt then
      ExceptT.mk (REAL_RAT_GT_CONV fm)
    else if op == rle then
      ExceptT.mk (REAL_RAT_LE_CONV fm)
    else if op == rge then
      ExceptT.mk (REAL_RAT_GE_CONV fm)
    else if op == req then
      ExceptT.mk (REAL_RAT_EQ_CONV fm)
    else throw "REAL_LEAF_CONV")

  let EVALC_CONV : ioconv ← pure (DEPTH_CONV REAL_LEAF_CONV)


  /-
  EVALC_CONV `x < &0 /\ &1 < &2`
  (EVALC_CONV THENC SIMPLIFY_CONV) `..` (the example is in simplify.ml)
  -/

  -- @@RETURN BEGIN
  return { PSIMPLIFY1_CONV, SIMPLIFY1_CONV, SIMPLIFY_CONV, REAL_LEAF_CONV, EVALC_CONV }
  -- @@RETURN END

end HolRQE.Simplify
