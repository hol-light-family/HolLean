/- ========================================================================= -/
/- Rqe: lifting a basic quantifier elimination to full first-order formula -/
/- ========================================================================= -/
/- File: HolRQE/LiftQelim.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/lift_qelim.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml, Rqe/num_calc_simp.ml, Rqe/asym.ml, Rqe/rol.ml, Rqe/poly_ext.ml, Rqe/simplify.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.LiftQelim fills them).

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

namespace HolRQE.LiftQelim

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CONJ_ASSOC DE_MORGAN_THM EXISTS_SIMP EXISTS_UNIQUE_THM NOT_EXISTS_THM
   NOT_FORALL_THM NOT_IMP OR_EXISTS_THM RIGHT_EXISTS_AND_THM t1 : thm)
  deriving Inhabited

/-- What lift_qelim.ml uses from Session besides theorems. -/
structure LiftQelimDeps where
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

/-- ACI_CONJ's local `build`. -/
partial def ACI_CONJ.build [HolBase] (ths : List thm) (tm : term) : ExceptT String IO thm := do
  if is_conj tm then
    let (l, r) ← liftExcept (dest_conj tm)
    -- `CONJ (build ths l) (build ths r)`, right to left
    let r' ← ACI_CONJ.build ths r
    let l' ← ACI_CONJ.build ths l
    CONJ l' r'
  else liftExcept (HolCore.Lib.find (fun th => concl th == tm) ths)

/-- What LIFT_QELIM_CONV's local functions close over: lift_qelim.ml's
    top-level `OR_ASSOC`, `forall_thm`, the conversions and terms bound with
    it, ACI_CONJ and QE_SIMPLIFY_CONV. -/
structure LiftQelimEnv where
  OR_ASSOC : thm
  forall_thm : thm
  or_exists_conv : ioconv
  triv_exists_conv : ioconv
  push_exists_conv : ioconv
  not_tm : term
  or_tm : term
  t_tm : term
  f_tm : term
  ACI_CONJ : term → term → ExceptT String IO thm
  QE_SIMPLIFY_CONV : ioconv

/-- LIFT_QELIM_CONV, with its local `let rec qelift_conv .. and qelim ..`. -/
partial def LIFT_QELIM_CONV.go [HolBase] (E : LiftQelimEnv)
    (afn_conv : List term → ioconv) (nfn_conv : ioconv) (qfn_conv : List term → ioconv) :
    ioconv :=
  fun fm => ((fun t => (qelift_conv (frees fm) t).run) THENC E.QE_SIMPLIFY_CONV) fm
where
  qelift_conv (vars : List term) (fm : term) : ExceptT String IO thm := do
    let { OR_ASSOC, forall_thm, or_exists_conv, not_tm, or_tm, t_tm, f_tm, .. } := E
    if fm == t_tm || fm == f_tm then pure (REFL fm)
    else if is_neg fm then
      let thm1 ← qelift_conv vars (← liftExcept (dest_neg fm))
      MK_COMB (REFL not_tm, thm1)
    else if is_conj fm || is_disj fm || is_imp fm || HolCore.Bool.is_iff fm then
      let (op, p, q) ← liftExcept (get_binop fm)
      let thm1 ← qelift_conv vars p
      let thm2 ← qelift_conv vars q
      MK_COMB (← MK_COMB ((REFL op), thm1), thm2)
    else if is_forall fm then
      let (x, p) ← liftExcept (dest_forall fm)
      let nex_thm ← BETA_RULE (← ISPEC (← liftExcept (mk_abs x p)) forall_thm)
      let alpha : ioconv := fun t => pure (HolCore.Equal.ALPHA_CONV x t)
      let nex_thm' ← CONV_RULE (LAND_CONV (RAND_CONV alpha)) nex_thm
      let nex_thm'' ← CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV alpha))) nex_thm'
      let elim_thm ← qelift_conv vars
        (← liftExcept (HolCore.Bool.mk_exists x (← liftExcept (HolCore.Bool.mk_neg p))))
      TRANS nex_thm'' (← MK_COMB (REFL not_tm, elim_thm))
    else if is_exists fm then
      let (x, p) ← liftExcept (dest_exists fm)
      let thm1 ← qelift_conv (x :: vars) p
      let thm1a ← MK_EXISTS x thm1
      let thm1b ← PURE_REWRITE_RULE [OR_ASSOC] thm1a
      let thm2 ← ExceptT.mk (nfn_conv (← liftExcept (rhs (concl thm1))))
      let thm2a ← MK_EXISTS x thm2
      let thm2b ← PURE_REWRITE_RULE [OR_ASSOC] thm2a
      let djs := disjuncts (← liftExcept (rhs (concl thm2)))
      let djthms ← djs.mapM (qelim x vars)
      let thm3 ← HolLight.end_itlist
        (fun thm1 thm2 => do MK_COMB (← MK_COMB (REFL or_tm, thm1), thm2)) djthms
      let split_ex_thm ← GSYM (← ExceptT.mk (or_exists_conv (← liftExcept (lhs (concl thm3)))))
      let thm3a ← TRANS split_ex_thm thm3
      TRANS (← TRANS thm1b thm2b) thm3a
    else
      ExceptT.mk (afn_conv vars fm)
  qelim (x : term) (vars : List term) (p : term) : ExceptT String IO thm := do
    let { triv_exists_conv, push_exists_conv, ACI_CONJ, .. } := E
    let cjs := conjuncts p
    let (ycjs, ncjs) := partition (fun c => mem x (frees c)) cjs
    if ycjs == [] then ExceptT.mk (triv_exists_conv (← liftExcept (HolCore.Bool.mk_exists x p)))
    else if ncjs == [] then ExceptT.mk (qfn_conv vars (← liftExcept (HolCore.Bool.mk_exists x p))) else
    let th1 ← ACI_CONJ p (← liftExcept (HolCore.Bool.mk_conj
      (← liftExcept (HolCore.Bool.list_mk_conj ncjs)) (← liftExcept (HolCore.Bool.list_mk_conj ycjs))))
    let th2 ← CONV_RULE (RAND_CONV push_exists_conv) (← MK_EXISTS x th1)
    let (t1, t2) ← liftExcept (dest_comb (← liftExcept (rand (concl th2))))
    TRANS th2 (← AP_TERM t1 (← ExceptT.mk (qfn_conv vars t2)))



/- ---------------------------------------------------------------------- -/
/-  Lifting quantifier elimination (lift_qelim.ml 1-129)                   -/
/- ---------------------------------------------------------------------- -/

structure LiftQelimFns where
  -- @@FIELDS
  ACI_CONJ : term → term → ExceptT String IO thm
  QE_SIMPLIFY_CONV : ioconv
  OR_ASSOC : thm
  forall_thm : thm
  or_exists_conv : ioconv
  triv_exists_conv : ioconv
  push_exists_conv : ioconv
  not_tm : term
  or_tm : term
  t_tm : term
  f_tm : term
  LIFT_QELIM_CONV : (List term → ioconv) → ioconv → (List term → ioconv) → ioconv
  deriving Inhabited

@[nospecialize]
def setupLiftQelimFns [HolBase] (D : LiftQelimDeps) :
    ExceptT String IO LiftQelimFns := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, TAUT, .. } := D
  let { CONJ_ASSOC, DE_MORGAN_THM, EXISTS_SIMP, EXISTS_UNIQUE_THM, NOT_EXISTS_THM,
        NOT_FORALL_THM, NOT_IMP, OR_EXISTS_THM, RIGHT_EXISTS_AND_THM, .. } := D.core1
  -- @@SCOPE END

  let ACI_CONJ : term → term → ExceptT String IO thm ← pure (fun p p' => do
    -- `let cjs = .. and cjs' = ..`
    let cjs := CONJUNCTS (← liftExcept (HolCore.Kernel.ASSUME p))
    let cjs' := CONJUNCTS (← liftExcept (HolCore.Kernel.ASSUME p'))
    let th ← ACI_CONJ.build cjs p'
    let th' ← ACI_CONJ.build cjs' p
    IMP_ANTISYM_RULE (← DISCH_ALL th) (← DISCH_ALL th'))

  let QE_SIMPLIFY_CONV : ioconv ← do
    let NOT_EXISTS_UNIQUE_THM ← prove
     r"~(?!x. P x) <=> (!x. ~P x) \/ ?x x'. P x /\ P x' /\ ~(x = x')"
      (REWRITE_TAC [EXISTS_UNIQUE_THM, DE_MORGAN_THM, NOT_EXISTS_THM] THEN
      REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, CONJ_ASSOC])
    let tauts ← do
      -- the TAUTs of the list, right to left
      let t12 ← TAUT (← q r"~(p /\ q \/ ~p /\ r) <=> p /\ ~q \/ ~p /\ ~r")
      let t11 ← TAUT (← q r"(p <=> q) <=> (p /\ q) \/ (~p /\ ~q)")
      let t10 ← TAUT (← q r"~(p <=> q) <=> (p /\ ~q) \/ (~p /\ q)")
      let t5 ← TAUT (← q r"p ==> q <=> ~p \/ q")
      let t4 ← TAUT (← q r"~(p ==> q) <=> p /\ ~q")
      let t3 ← TAUT (← q r"~(p \/ q) <=> ~p /\ ~q")
      let t2 ← TAUT (← q r"~(p /\ q) <=> ~p \/ ~q")
      let t1 ← TAUT (← q r"~(~p) <=> p")
      pure [
       t1,
       t2,
       t3,
       t4,
       t5,
       NOT_FORALL_THM,
       NOT_EXISTS_THM,
       EXISTS_UNIQUE_THM,
       NOT_EXISTS_UNIQUE_THM,
       t10,
       t11,
       t12]
    GEN_REWRITE_CONV_NET TOP_SWEEP_CONV tauts

  let OR_ASSOC ← TAUT (← q r"(a \/ b) \/ c <=> a \/ b \/ c")
  -- `let forall_thm = .. and or_exists_conv = .. and .. and f_tm = ..`
  let forall_thm ← prove r"!P. (!x. P x) <=> ~ (?x. ~ P x)" (MESON_TAC [])
  let or_exists_conv : ioconv ← pure (PURE_REWRITE_CONV [OR_EXISTS_THM])
  let triv_exists_conv : ioconv ← pure (REWR_CONV EXISTS_SIMP)
  let push_exists_conv : ioconv ← pure (REWR_CONV RIGHT_EXISTS_AND_THM)
  let not_tm : term ← q r"(~)"
  let or_tm : term ← q r"(\/)"
  let t_tm : term ← q r"T"
  let f_tm : term ← q r"F"

  let LIFT_QELIM_CONV : (List term → ioconv) → ioconv → (List term → ioconv) → ioconv ←
    pure (LIFT_QELIM_CONV.go
      { OR_ASSOC, forall_thm, or_exists_conv, triv_exists_conv, push_exists_conv,
        not_tm, or_tm, t_tm, f_tm, ACI_CONJ, QE_SIMPLIFY_CONV })



  /-
  (the commented-out experiments and QELIM_DLO_CONV are in lift_qelim.ml)
  -/

  -- @@RETURN BEGIN
  return { ACI_CONJ, QE_SIMPLIFY_CONV, OR_ASSOC, forall_thm, or_exists_conv,
           triv_exists_conv, push_exists_conv, not_tm, or_tm, t_tm, f_tm,
           LIFT_QELIM_CONV }
  -- @@RETURN END

end HolRQE.LiftQelim
