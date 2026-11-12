/- ========================================================================= -/
/- Rqe: signs, their interpretation, partitions of the line and sign matri -/
/- ========================================================================= -/
/- File: HolRQE/Defs.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/defs.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml, Rqe/num_calc_simp.ml, Rqe/asym.ml, Rqe/rol.ml, Rqe/poly_ext.ml, Rqe/simplify.ml, Rqe/lift_qelim.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.Defs fills them).

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

namespace HolRQE.Defs

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALL2 AND_IMP_THM APPEND COND_CLAUSES HD NOT_CONS_NIL TL list_RECURSION t1 : thm)
  deriving Inhabited

/-- What defs.ml uses from Session besides theorems. -/
structure DefsDeps where
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
  define_type : String → ExceptT String IO (thm × thm)
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

/-- make_partition_list's local `make_partition_list`, given the terms its
    `let .. and .. in` binds. -/
partial def make_partition_list.go (lxt htm h1tm h2tm x_lt_h x_eq_h h_lt_x x_lt_h1 x_eq_h1 x_h1_h2 : term) :
    List term → ExceptT String IO (List term)
  | [] => pure [lxt]
  | [h] => do
    let s ← ExceptT.mk (subst [(h, htm)])
    [x_lt_h, x_eq_h, h_lt_x].mapM (fun t => ExceptT.mk (s t))
  | h1 :: h2 :: t => do
    -- `map (subst ..) [..] @ tl (make_partition_list (h2::t))`, right to left
    let rest ← make_partition_list.go lxt htm h1tm h2tm x_lt_h x_eq_h h_lt_x x_lt_h1 x_eq_h1 x_h1_h2
      (h2 :: t)
    let tl' ← liftExcept (tl rest)
    let s ← ExceptT.mk (subst [(h1, h1tm), (h2, h2tm)])
    let l ← [x_lt_h1, x_eq_h1, x_h1_h2].mapM (fun t => ExceptT.mk (s t))
    pure (l ++ tl')



/- ====================================================================== -/
/-  Signs (defs.ml 1-314)                                                 -/
/- ====================================================================== -/

structure DefsFns where
  -- @@FIELDS
  sign_INDUCT : thm
  sign_RECURSION : thm
  SIGN_CASES : thm
  sunk_tm : term
  snonz_tm : term
  sneg_tm : term
  spos_tm : term
  szero_tm : term
  interpsign : thm
  interpsign_tm : term
  dest_interpsign : thm → Except String (term × term × term)
  interpsigns : thm
  t0 : thm
  interpsigns_thms : thm → ExceptT String IO (List thm)
  interpsigns_thms2 : thm → ExceptT String IO (List thm)
  interpsigns_tm : term
  dest_interpsigns : thm → Except String (term × term × term)
  interp_sing : thm
  interp_doub : thm
  mk_interpsigns : List thm → ExceptT String IO thm
  partition_line : thm
  make_partition_list : List term → ExceptT String IO (List term)
  part_line_tm : term
  real_bool_ty : hol_type
  PARTITION_LINE_CONV : term → ExceptT String IO thm
  interpmat : thm
  interpmat_tm : term
  dest_interpmat : term → Except String (term × term × term)
  interpmat_thms : thm → ExceptT String IO (thm × thm)
  mk_interpmat_thm : thm → thm → ExceptT String IO thm
  all2_thm0 : thm
  all2_thm : thm
  mk_all2_interpsigns : thm → List thm → ExceptT String IO thm
  dest_all2 : term → Except String (term × term × term)
  is_interval : term → Bool
  is_point : term → Bool
  new_var : (hol_type → IO term)
  reset_vars : (Unit → IO Unit)
  deriving Inhabited

@[nospecialize]
def setupDefsFns [HolBase] (D : DefsDeps) :
    ExceptT String IO DefsFns := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, TAUT, define_type, new_definition, new_recursive_definition,
        prove_by_refinement, rlt, .. } := D
  let { ALL2, AND_IMP_THM, APPEND, COND_CLAUSES, HD, NOT_CONS_NIL, TL, list_RECURSION, .. } := D.core1
  -- @@SCOPE END

  /- ---------------------------------------------------------------------- -/
  /-  Datatype                                                              -/
  /- ---------------------------------------------------------------------- -/

  let (sign_INDUCT, sign_RECURSION) ← define_type
    "sign = Zero | Pos | Neg | Nonzero | Unknown"

  let SIGN_CASES ← prove_by_refinement (
    (← q r"!s. (s = Pos) \/ (s = Neg) \/ (s = Zero) \/ (s = Nonzero) \/ (s = Unknown)"),
  /- {{{ Proof -/
  [
    MATCH_MP_TAC sign_INDUCT,
    REWRITE_TAC []
  ])
  /- }}} -/

  -- the tuple right to left
  let sunk_tm : term ← q r"Unknown"
  let snonz_tm : term ← q r"Nonzero"
  let sneg_tm : term ← q r"Neg"
  let spos_tm : term ← q r"Pos"
  let szero_tm : term ← q r"Zero"

  /- ------------------------------------------------------------------------- -/
  /- Intepretation of signs.                                                   -/
  /- ------------------------------------------------------------------------- -/

  /- An interpretation of the sign of a polynomial over a set. -/
  let interpsign ← new_recursive_definition sign_RECURSION
    r"(interpsign set ply Zero = (!x:real. set x ==> (ply x = &0))) /\
     (interpsign set ply Pos  = (!x. set x ==> (ply x > &0))) /\
     (interpsign set ply Neg  = (!x. set x ==> (ply x < &0))) /\
     (interpsign set ply Nonzero  = (!x. set x ==> (ply x <> &0))) /\
     (interpsign set ply Unknown = (!x. set x ==> (ply x = ply x)))"


  let interpsign_tm : term ← q r"interpsign"
  let dest_interpsign : thm → Except String (term × term × term) ← pure (fun interpthm => do
    let (int, args) ← HolCore.IndDefs.strip_ncomb 3 (concl interpthm)
    let (set, poly0, sign) ← match args with
      | [set, poly0, sign] => pure (set, poly0, sign)
      | _ => throw "Match_failure"
    if !(int == interpsign_tm) then
      throw "not an interpsign"
    else
      pure (set, poly0, sign))

  /-
  (an example is in defs.ml)
  -/

  /- A version for one set but multiple polynomials -/
  let interpsigns ← new_definition
    r"interpsigns polyl set signl = ALL2 (interpsign set) polyl signl"

  let t0 ← TAUT (← q r"a /\ T <=> a")
  let interpsigns_thms : thm → ExceptT String IO (List thm) ← pure (fun interpthm => do
    let ret ← (CONJUNCTS (← PURE_REWRITE_RULE [interpsign, interpsigns, ALL2, t0] interpthm)).mapM
      BETA_RULE
    pure ret)

  /- keep interpsign -/
  let interpsigns_thms2 : thm → ExceptT String IO (List thm) ← pure (fun interpthm => do
    pure (CONJUNCTS (← PURE_REWRITE_RULE [interpsigns, ALL2, t0] interpthm)))

  let interpsigns_tm : term ← q r"interpsigns"
  let dest_interpsigns : thm → Except String (term × term × term) ← pure (fun interpthm => do
    let (int, args) ← HolCore.IndDefs.strip_ncomb 3 (concl interpthm)
    let (polys, set, signs) ← match args with
      | [polys, set, signs] => pure (polys, set, signs)
      | _ => throw "Match_failure"
    if !(int == interpsigns_tm) then
      throw "not an interpsigns"
    else
      pure (polys, set, signs))


  let interp_sing ← prove
    r"interpsign set p s = interpsigns [p] set [s]"
    (REWRITE_TAC [interpsigns, ALL2])

  let interp_doub ← prove
    r"interpsigns [p1] set [s1] ==> interpsigns pl set sl ==>
       interpsigns (CONS p1 pl) set (CONS s1 sl)"
    (ASM_MESON_TAC [interpsigns, ALL2])

  let mk_interpsigns : List thm → ExceptT String IO thm ← pure (fun thms => do
    let thms' ← thms.mapM (PURE_REWRITE_RULE [interp_sing])
    HolLight.end_itlist (fun t1 t2 => MATCH_MPL [interp_doub, t1, t2]) thms')


  /-
  (examples are in defs.ml)
  -/

  /- ---------------------------------------------------------------------- -/
  /-  Partition line                                                        -/
  /- ---------------------------------------------------------------------- -/


  let partition_line ← new_recursive_definition list_RECURSION
    r"(partition_line [] = [(\x. T)]) /\
     (partition_line (CONS h t) =
        if t = [] then [(\x. x < h); (\x. x = h); (\x. h < x)] else
          APPEND [(\x. x < h); (\x. x = h); (\x. h < x /\ x < HD t)]
                  (TL (partition_line t)))"

  /-
  (examples are in defs.ml)
  -/


  let make_partition_list : List term → ExceptT String IO (List term) ← do
    let lxt ← q r"\x:real. T"
    let htm ← q r"h:real"
    let h1tm ← q r"h1:real"
    let h2tm ← q r"h2:real"
    let x_lt_h ← q r"(\x. x < h)"
    let x_eq_h ← q r"(\x:real. x = h)"
    let h_lt_x ← q r"(\x. h < x)"
    let x_lt_h1 ← q r"(\x. x < h1)"
    let x_eq_h1 ← q r"(\x:real. x = h1)"
    let x_h1_h2 ← q r"(\x. h1 < x /\ x < h2)"
    pure (make_partition_list.go lxt htm h1tm h2tm x_lt_h x_eq_h h_lt_x x_lt_h1 x_eq_h1 x_h1_h2)


  /-
  make_partition_list [`&1`;`&2`]
  -/

  /- partition a line based on a list of points
     this is just a compact representation of a list of terms
  -/
  let part_line_tm : term ← q r"partition_line"
  let real_bool_ty : hol_type ← qty "real->bool"
  let PARTITION_LINE_CONV : term → ExceptT String IO thm ← pure (fun pts => do
    let ptm ← liftExcept (mk_comb part_line_tm pts)
    let ltm ← ExceptT.mk (HolMath.Lists.mk_list (← make_partition_list (← liftExcept (dest_list pts)))
      real_bool_ty)
    let mkEq ← ExceptT.mk _root_.mk_eq
    let tm ← liftExcept (mkEq (ptm, ltm))
    ExceptT.mk (HolCore.Tactics.prove HolBase.B tm
      (REWRITE_TAC [partition_line, APPEND, COND_CLAUSES, NOT_CONS_NIL, TL, HD])))

  /-
  PARTITION_LINE_CONV `[]:real list`
  PARTITION_LINE_CONV `[&1; &2]`
  PARTITION_LINE_CONV `[&2; &1]`
  PARTITION_LINE_CONV `[a:real; b]`
  -/


  /- an interpretation of a sign matrix
     arguments are a list of points, a list of polynomials, and a sign matrix
     the points form an ordered list (smallest first),
     each zero of each polynomial must appear among the list of points
     and finally, the sign matrix corresponds to the correct sign for the polynomial
     in the region represented by the set.
  -/
  let interpmat ← new_definition
    r"interpmat ptl polyl signll <=>
      real_ordered_list ptl /\
      ALL2 (interpsigns polyl) (partition_line ptl) signll"

  let interpmat_tm : term ← q r"interpmat"
  let dest_interpmat : term → Except String (term × term × term) ← do
    let imat_tm := interpmat_tm
    pure (fun tm => do
      let (sc, args) := strip_comb tm
      if !(sc == imat_tm) then throw "dest_interpmat: not an interpmat term" else
      let (ptl, polyl, signll) ← match args with
        | [ptl, polyl, signll] => pure (ptl, polyl, signll)
        | _ => throw "Match_failure"
      pure (ptl, polyl, signll))

  let interpmat_thms : thm → ExceptT String IO (thm × thm) ← pure (fun thm => do
    match CONJUNCTS (← PURE_REWRITE_RULE [interpmat] thm) with
    | [rol_thm, interpsigns_thm] => pure (rol_thm, interpsigns_thm)
    | _ => throw "Match_failure")

  let mk_interpmat_thm : thm → thm → ExceptT String IO thm ← pure (fun rol_thm =>
      fun all_thm => do
        let ret ← REWRITE_RULE [← GSYM interpmat] (← CONJ rol_thm all_thm)
        let (l, _) := strip_comb (concl ret)
        if !(l == interpmat_tm) then throw "mk_interpmat" else pure ret)

  /-
  let rol_thm = rol_thm'''
  let all_thm = all_thm''
  -/

  /- {{{ Doc -/

  /-
  mk_all2_interpsigns: (the documentation is in defs.ml)
  -/

  /- }}} -/

  let all2_thm0 ← GEN_ALL (← EQT_ELIM (← liftExcept (hd (CONJUNCTS ALL2))))
  let all2_thm ← GEN_ALL (← REWRITE_RULE [AND_IMP_THM]
    (← EQ_IMP_RULE (← GSYM (← liftExcept (last (CONJUNCTS ALL2))))).1)

  let mk_all2_interpsigns : thm → List thm → ExceptT String IO thm ← pure (fun part_thm is_thms => do
    let is_tm := (← liftExcept (dest_comb (← liftExcept (dest_comb (concl (← liftExcept (hd is_thms))))).1)).1
    let all2_thm0' ← ISPEC is_tm all2_thm0 /- it`s having trouble matching -/
    let ret ← is_thms.foldrM (fun x y => MATCH_MPL [all2_thm, x, y]) all2_thm0'
    REWRITE_RULE [← GSYM part_thm] ret)

  let dest_all2 : term → Except String (term × term × term) ← pure (fun tm => do
    let (a2, l) := strip_comb tm
    if (← dest_const a2).1 == "ALL2" then
      match l with
      | [a1, a2, a3] => pure (a1, a2, a3)
      | _ => throw "Match_failure"
    else
      throw "dest_all2: not an ALL2")

  /- ---------------------------------------------------------------------- -/
  /-  Sets                                                                  -/
  /- ---------------------------------------------------------------------- -/

  let is_interval : term → Bool ← pure (fun set =>
    match (do
      let (_x, bod) ← dest_abs set
      if is_conj bod then
        let (l, r) ← dest_conj bod
        pure (can (dest_binop rlt) l && can (dest_binop rlt) r)
      else pure (can (dest_binop rlt) bod) : Except String Bool) with
    | .ok v => v
    | .error _ => false)

  /-
  is_interval `\x. &4 < x /\ x < &5`;;
  is_interval `\x. x = &4`;;
  -/

  let is_point : term → Bool ← pure (fun set =>
    match (do
      let (_x, bod) ← dest_abs set
      if is_eq bod then pure true else pure false : Except String Bool) with
    | .ok v => v
    | .error _ => false)

  /-
  is_point `\x. x = &5`
  is_point `\x. x = y:real`
  -/

  /- ---------------------------------------------------------------------- -/
  /-  We generate new var names                                             -/
  /- ---------------------------------------------------------------------- -/

  let (new_var, reset_vars) : (hol_type → IO term) × (Unit → IO Unit) ← do
    let id ← IO.mkRef (0 : Int)
    let pre := "x_"
    let new_var (ty : hol_type) : IO term := do
      id.set ((← id.get) + 1)
      return mk_var (pre ++ toString (← id.get)) ty
    let reset_vars (_ : Unit) : IO Unit :=
      id.set 0
    pure (new_var, reset_vars)

  -- @@RETURN BEGIN
  return { sign_INDUCT, sign_RECURSION, SIGN_CASES, sunk_tm, snonz_tm, sneg_tm, spos_tm,
           szero_tm, interpsign, interpsign_tm, dest_interpsign, interpsigns, t0,
           interpsigns_thms, interpsigns_thms2, interpsigns_tm, dest_interpsigns,
           interp_sing, interp_doub, mk_interpsigns, partition_line, make_partition_list,
           part_line_tm, real_bool_ty, PARTITION_LINE_CONV, interpmat, interpmat_tm,
           dest_interpmat, interpmat_thms, mk_interpmat_thm, all2_thm0, all2_thm,
           mk_all2_interpsigns, dest_all2, is_interval, is_point, new_var, reset_vars }
  -- @@RETURN END

end HolRQE.Defs
