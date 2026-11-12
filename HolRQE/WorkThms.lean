/- ========================================================================= -/
/- Rqe: the working theorems of the decision procedure.                    -/
/- ========================================================================= -/
/- File: HolRQE/WorkThms.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/work_thms.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml, Rqe/num_calc_simp.ml, Rqe/asym.ml, Rqe/rol.ml, Rqe/poly_ext.ml, Rqe/simplify.ml, Rqe/lift_qelim.ml, Rqe/defs.ml, Rqe/testform_thms.ml, Rqe/condense_thms.ml, Rqe/inferisign_thms.ml, Rqe/matinsert_thms.ml, Rqe/signs_thms.ml, Rqe/inferpsign_thms.ml, Rqe/dedmatrix_thms.ml, Rqe/pdivides_thms.ml, Rqe/main_thms.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.WorkThms fills them).

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
import HolRQE.InferisignThms
import HolRQE.MatinsertThms
import HolRQE.SignsThms
import HolRQE.InferpsignThms
import HolRQE.DedmatrixThms
import HolRQE.PdividesThms
import HolRQE.MainThms

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
open HolRQE.InferisignThms
open HolRQE.MatinsertThms
open HolRQE.SignsThms
open HolRQE.InferpsignThms
open HolRQE.DedmatrixThms
open HolRQE.PdividesThms
open HolRQE.MainThms

namespace HolRQE.WorkThms

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALL ALL2 APPEND APPEND_EQ_NIL APPEND_NIL BUTLAST CONS_11 DE_MORGAN_THM
   DIVISION EL EVEN_MOD EVEN_ODD_POW FUN_EQ_THM GT HD IMP_AND_THM IN
   INTERPSIGNS_SUBSET INTERPSIGN_SUBSET LAST LENGTH LENGTH_0 LENGTH_1
   LENGTH_APPEND LENGTH_EQ_NIL LENGTH_MAP LENGTH_MAP2 LENGTH_PAIR
   LENGTH_REPLICATE LENGTH_SING LET_TRANS LE_SUC LTE_TRANS LT_0 LT_IMP_LE LT_SUC
   LT_TRANS MAP MAP2 MEM NOT_CONS_NIL NOT_EXISTS_THM NOT_LE NOT_NIL NOT_ODD
   NOT_SUC ODD ONE POLY_DIFF_DOWN_LEFT5 POLY_DIFF_DOWN_RIGHT3 POLY_DIFF_UP_LEFT5
   POLY_DIFF_UP_RIGHT3 PRE REAL_ADD_LID REAL_ENTIRE REAL_EQ_IMP_LE
   REAL_LT_IMP_LE REAL_LT_IMP_NZ REAL_LT_TRANS REAL_MUL_GT REAL_MUL_LT
   REAL_MUL_RZERO REAL_POW_LT REPLICATE ROL_APPEND ROL_CONS_CONS
   ROL_CONS_CONS_DELETE ROL_INSERT_BACK_THM ROL_NIL ROL_SING ROL_TAIL SIGN_CASES
   SUBSET SUC_INJ TL eq_eq_false_thm interpmat interpsign interpsigns list_CASES
   list_RECURSION neg_neg_neq_thm neg_pos_neq_thm neg_zero_neg_thm num_CASES
   num_RECURSION partition_line pos_neg_neq_thm pos_pos_neq_thm pos_zero_pos_thm
   real_gt real_ordered_list zero_neg_neg_thm zero_pos_pos_thm : thm)
  deriving Inhabited

/-- What work_thms.ml uses from Session besides theorems. -/
structure WorkThmsDeps where
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
  mk_small_numeral : Int → Except String term
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
  sz_z_thm : Option (IO.Ref thm)
  sz_nz_thm : Option (IO.Ref thm)
  empty_sgns : List thm
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

/- work_thms.ml's OCaml functions, by hand (the theorem phrases are
   converted by gxwork/rq/ml2lean.py; see the bundles).  The plain ones are
   top-level definitions; the ones over theorems or session functions are
   bundle fields, built from the helpers here. -/

section
variable [HolBase]

/-- `let rec DISJ_TAC thm = DISJ_CASES_TAC thm THENL[ALL_TAC;TRY (POP_ASSUM DISJ_TAC)]` -/
partial def DISJ_TAC (th : thm) : tactic := fun g =>
  (DISJ_CASES_TAC th THENL [ALL_TAC, TRY (POP_ASSUM DISJ_TAC)]) g

/-- LENGTH_N's recursion, given the theorems and session rules it uses.
    OCaml's `let ... in` before the `match` runs on each call. -/
partial def LENGTH_N.go (TAUT : term → ExceptT String IO thm) (ARITH_TAC : tactic)
    (mk_small_numeral : Int → Except String term)
    (LENGTH LENGTH_SING LENGTH_0 LENGTH_TL HD_TL HD_LEM PRE : thm)
    (n : Int) (ty : hol_type) : ExceptT String IO thm := do
  let zero ← q r"0"
  let neg ← q r"(~)"
  let imp_thm ← TAUT (← q r"(a ==> b) ==> (b ==> a) ==> (a <=> b)")
  match n with
  | 0 => CONJUNCT1 LENGTH
  | 1 => pure LENGTH_SING
  | n =>
      let len_tm ← ExceptT.mk (mk_const "LENGTH" [(ty, aty)])
      let tl_tm ← ExceptT.mk (mk_const "TL" [(ty, aty)])
      let hd_tm ← ExceptT.mk (mk_const "HD" [(ty, aty)])
      let t := mk_var "t" (← ExceptT.mk (mk_type "list" [ty]))
      let n_tm ← liftExcept (mk_small_numeral n)
      let pren_tm ← liftExcept (mk_small_numeral (n - 1))
      let mkEq ← ExceptT.mk _root_.mk_eq
      let len_thm ← liftExcept (HolCore.Kernel.ASSUME (← liftExcept (mkEq (← liftExcept (mk_comb len_tm t), n_tm))))
      let pre_thm ← LENGTH_N.go TAUT ARITH_TAC mk_small_numeral LENGTH LENGTH_SING LENGTH_0 LENGTH_TL
        HD_TL HD_LEM PRE (n - 1) ty
      let n_nz ← ExceptT.mk (HolCore.Tactics.prove HolBase.B
        (← liftExcept (HolCore.Bool.mk_neg (← liftExcept (mkEq (n_tm, zero))))) ARITH_TAC)
      let not_nil_thm ← EQ_MP (← REWRITE_RULE [len_thm] (← AP_TERM neg (← ISPEC t LENGTH_0))) n_nz
      let n_suc ← ExceptT.mk (HolCore.Tactics.prove HolBase.B
        (← liftExcept (mkEq (n_tm, ← liftExcept (mk_comb (← q r"SUC") pren_tm)))) ARITH_TAC)
      let len_tl ← REWRITE_RULE [n_suc, PRE, ← ISPEC (← liftExcept (mk_comb tl_tm t)) pre_thm, len_thm]
        (← MATCH_MP LENGTH_TL not_nil_thm)
      let cons_thm ← MATCH_MP (← ISPEC t HD_TL) not_nil_thm
      let hd_thm ← ONCE_REWRITE_RULE [HD_LEM] len_tl
      let thm ← REWRITE_RULE [← GSYM cons_thm] hd_thm
      let x0 := mk_var ("x" ++ toString n) ty
      let hdt ← liftExcept (mk_comb hd_tm t)
      let s ← ExceptT.mk (subst [(x0, hdt)])
      -- `EXISTS (mk_exists(..), mk_comb(hd_tm,t)) thm`: the pair right to left
      let w ← liftExcept (mk_comb hd_tm t)
      let ex_thm ← EXISTS
        (← liftExcept (HolCore.Bool.mk_exists x0 (← ExceptT.mk (s (concl thm)))), w) thm
      let left ← DISCH (concl len_thm) ex_thm
      let right ← ExceptT.mk (HolCore.Tactics.prove HolBase.B
        (← liftExcept (HolCore.Bool.mk_imp (concl ex_thm) (concl len_thm)))
        (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [LENGTH] THEN ARITH_TAC))
      GEN_ALL (← MATCH_MPL [imp_thm, left, right])

def RESTRIP_TAC : tactic := REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC

def USE_X_ASSUM (lab : String) (ttac : thm_tactic) : tactic :=
    USE_THEN lab (fun th => UNDISCH_THEN (concl th) ttac)

def QUANT_CONV (conv : ioconv) : ioconv := RAND_CONV (ABS_CONV conv)

partial def PATH_CONV2 (s : List String) (cnv : ioconv) : ioconv := fun tm =>
  match s with
  | [] => cnv tm
  | "l" :: t => RATOR_CONV (PATH_CONV2 t cnv) tm
  | "r" :: t => RAND_CONV (PATH_CONV2 t cnv) tm
  | "q" :: t => QUANT_CONV (PATH_CONV2 t cnv) tm
  | "a" :: t => ABS_CONV (PATH_CONV2 t cnv) tm
  | _ => pure (.error "PATH_CONV2: unknown direction")

/-- EXISTS_TACL's recursion, given rqe_tactics_ext.ml's TYPE_TAC and
    EXISTS_TAC. -/
partial def EXISTS_TACL.go (TYPE_TAC : (term → tactic) → term → tactic)
    (EXISTS_TAC : term → tactic) : List term → tactic
  | [] => ALL_TAC
  | h :: t => TYPE_TAC EXISTS_TAC h THEN EXISTS_TACL.go TYPE_TAC EXISTS_TAC t

end



/- ---------------------------------------------------------------------- -/
/- work_thms.ml phrases from line 1 to 973; the theorems                  -/
/- converted by gxwork/rq/ml2lean.py (disclosed; comments in the          -/
/- proofs are not carried over), the functions by hand.                   -/
/- ---------------------------------------------------------------------- -/

structure WorkThms01 where
  -- @@FIELDS
  INTERPSIGNS_CONJ : thm
  INTERPMAT_TRIO : thm
  PARTITION_LINE_NOT_NIL : thm
  ALL2_LENGTH : thm
  LENGTH_TL : thm
  PARTITION_LINE_LENGTH : thm
  PARTITION_LINE_LENGTH_TL : thm
  PL_ALL2_LENGTH : thm
  INTERPMAT_LENGTH : thm
  ALL2_HD : thm
  ALL2_TL : thm
  ALL2_APPEND_LENGTH : thm
  ALL2_APPEND : thm
  ALL2_SPLIT : thm
  BUTLAST_THM : thm
  HD_BUTLAST : thm
  SUBLIST : thm
  SUBLIST_NIL : thm
  SUBLIST_CONS : thm
  SUBLIST_TL : thm
  SUBLIST_CONS2 : thm
  SUBLIST_ID : thm
  SUBLIST_CONS_CONS : thm
  SUBLIST_NEQ : thm
  SUBLIST_TRANS : thm
  ROL_MEM : thm
  SUBLIST_MEM : thm
  ROL_SUBLIST_LT : thm
  SUBLIST_DELETE : thm
  SUBLIST_MATCH : thm
  ROL_SUBLIST : thm
  SUBLIST_BUTLAST : thm
  SUBLIST_APPEND_HD : thm
  SUBLIST_ID_CONS : thm
  SUBLIST_ID_APPEND : thm
  SUBLIST_APPEND_TL : thm
  SUBLIST_TRANS2 : thm
  APPEND_CONS : thm
  SUBLIST_APPEND : thm
  SUBLIST_APPEND2 : thm
  ROL_APPEND2 : thm
  PL_LEM : thm
  HD_APPEND2 : thm
  BUTLAST_TL : thm
  APPEND_TL : thm
  APPEND_HD : thm
  PL_LEM2 : thm
  BUTLAST_APPEND : thm
  LENGTH_TL1 : thm
  PL_BUTLAST : thm
  PARTITION_LINE_APPEND : thm
  HD_TL : thm
  HD_LEM : thm
  LENGTH_N : Int → hol_type → ExceptT String IO thm
  BUTLAST_LENGTH : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupWorkThms01 [HolBase] (D : WorkThmsDeps) :
    ExceptT String IO WorkThms01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_SIMP_TAC, ARITH_TAC, ASM_MESON_TAC, CASES_ON, CLAIM,
        EXISTS_TAC, LIST_INDUCT_TAC, MESON_TAC, REAL_ARITH_TAC, TAUT, mk_small_numeral,
        new_recursive_definition, prove_by_refinement, .. } := D
  let { ALL2, APPEND, APPEND_EQ_NIL, APPEND_NIL, BUTLAST, CONS_11, HD, IMP_AND_THM, IN,
        INTERPSIGNS_SUBSET, LAST, LENGTH, LENGTH_0, LENGTH_APPEND, LENGTH_EQ_NIL,
        LENGTH_SING, MEM, NOT_CONS_NIL, NOT_NIL, ONE, PRE, ROL_APPEND, ROL_CONS_CONS,
        ROL_CONS_CONS_DELETE, ROL_NIL, ROL_SING, ROL_TAIL, SIGN_CASES, SUBSET, SUC_INJ,
        TL, interpmat, interpsign, interpsigns, list_CASES, list_RECURSION,
        partition_line, real_ordered_list, .. } := D.core1
  -- @@SCOPE END

  -- DISJ_TAC (work_thms.ml 1) is a top-level definition (by hand, above)

  let INTERPSIGNS_CONJ ← prove_by_refinement (
    (← q r"!P Q eqs l.
    interpsigns eqs (\x. P x) l /\
    interpsigns eqs (\x. Q x) l ==>
    interpsigns eqs (\x. P x \/ Q x) l"),
  [
    STRIP_TAC THEN STRIP_TAC,
    REPEAT LIST_INDUCT_TAC THEN REWRITE_TAC [interpsigns, ALL2, interpsign],
    REPEAT (POP_ASSUM MP_TAC),
    DISJ_TAC (← ISPEC (← q r"h':sign") SIGN_CASES) THEN ASM_REWRITE_TAC [interpsign, interpsigns] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC []
  ])

  let INTERPMAT_TRIO ← prove_by_refinement (
    (← q r"!eqs x y l r t.
    interpmat (CONS x (CONS y t)) eqs (CONS l (CONS l (CONS l r))) ==>
    interpmat (CONS y t) eqs (CONS l r)"),
  [
    REWRITE_TAC [interpmat, partition_line, NOT_CONS_NIL, ALL2, HD, TL, APPEND],
    REPEAT_N 6 STRIP_TAC,
    DISJ_CASES_TAC (← ISPEC (← q r"t:real list") list_CASES),
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    MATCH_ACCEPT_TAC ROL_SING,
    REWRITE_TAC [ALL2],
    REWRITE_ASSUMS [TL],
    STRIP_TAC,
    MATCH_MP_TAC INTERPSIGNS_SUBSET,
    EXISTS_TAC (← q r"\z. z < x \/ (z = x) \/ (x < z /\ z < y)"),
    STRIP_TAC,
    MATCH_MP_TAC INTERPSIGNS_CONJ,
    ASM_REWRITE_TAC [],
    MATCH_MP_TAC INTERPSIGNS_CONJ,
    ASM_REWRITE_TAC [],
    REWRITE_TAC [SUBSET, IN],
    REAL_ARITH_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    ASM_REWRITE_TAC [NOT_CONS_NIL, TL],
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [ROL_TAIL, TL, NOT_CONS_NIL],
    REWRITE_TAC [ALL2],
    ASM_REWRITE_TAC [],
    MATCH_MP_TAC INTERPSIGNS_SUBSET,
    EXISTS_TAC (← q r"\z. z < x \/ (z = x) \/ (x < z /\ z < y)"),
    STRIP_TAC,
    MATCH_MP_TAC INTERPSIGNS_CONJ,
    ASM_REWRITE_TAC [],
    MATCH_MP_TAC INTERPSIGNS_CONJ,
    ASM_REWRITE_TAC [],
    REWRITE_TAC [SUBSET, IN],
    REAL_ARITH_TAC
  ])

  let PARTITION_LINE_NOT_NIL ← prove_by_refinement (
    (← q r"!l. ~(partition_line l = [])"),
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [partition_line, NOT_CONS_NIL],
    REWRITE_TAC [partition_line],
    COND_CASES_TAC,
    REWRITE_TAC [NOT_CONS_NIL],
    ASM_MESON_TAC [APPEND_EQ_NIL, NOT_CONS_NIL]
  ])

  let ALL2_LENGTH ← prove_by_refinement (
    (← q r"!P l1 l2. ALL2 P l1 l2 ==> (LENGTH l1 = LENGTH l2)"),
  [
    STRIP_TAC,
    REPEAT LIST_INDUCT_TAC THEN REWRITE_TAC [ALL2, LENGTH],
    ASM_MESON_TAC []
  ])

  let LENGTH_TL ← prove_by_refinement (
    (← q r"!l:A list. ~(l = []) ==> (LENGTH (TL l) = PRE (LENGTH l))"),
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [],
    REWRITE_TAC [NOT_CONS_NIL, TL, LENGTH],
    ARITH_TAC
  ])

  let PARTITION_LINE_LENGTH ← prove_by_refinement (
    (← q r"!l. LENGTH (partition_line l) = 2 * LENGTH l + 1"),
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [partition_line, LENGTH],
    ARITH_TAC,
    REWRITE_TAC [partition_line, LENGTH],
    COND_CASES_TAC,
    ASM_REWRITE_TAC [LENGTH],
    ARITH_TAC,
    REWRITE_TAC [APPEND, LENGTH],
    ASM_SIMP_TAC [PARTITION_LINE_NOT_NIL, LENGTH_TL],
    ARITH_TAC
  ])

  let PARTITION_LINE_LENGTH_TL ← prove_by_refinement (
    (← q r"!l. LENGTH (TL (partition_line l)) = 2 * LENGTH l"),
  [
    STRIP_TAC,
    REWRITE_TAC [(← MATCH_MP LENGTH_TL (← ISPEC (← q r"l:real list") PARTITION_LINE_NOT_NIL))],
    REWRITE_TAC [PARTITION_LINE_LENGTH],
    ARITH_TAC
  ])

  let PL_ALL2_LENGTH ← prove_by_refinement (
    (← q r"!eqs pts sgns. ALL2 (interpsigns eqs) (partition_line pts) sgns ==>
     (LENGTH sgns = 2 * LENGTH pts + 1)"),
  [
    REPEAT_N 3 STRIP_TAC,
    DISJ_CASES_TAC (← ISPEC (← q r"pts:real list") list_CASES),
    ASM_REWRITE_TAC [interpmat, LENGTH, ROL_NIL, partition_line],
    ARITH_SIMP_TAC [],
    DISJ_CASES_TAC (← ISPEC (← q r"sgns:(sign list) list") list_CASES),
    ASM_REWRITE_TAC [ALL2],
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    ASM_REWRITE_TAC [],
    ASM_REWRITE_TAC [ALL2],
    DISJ_CASES_TAC (← ISPEC (← q r"t:(sign list) list") list_CASES),
    ASM_REWRITE_TAC [ALL2, LENGTH, ONE],
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    ASM_REWRITE_TAC [],
    ASM_REWRITE_TAC [ALL2],
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    ASM_REWRITE_TAC [interpmat, partition_line],
    COND_CASES_TAC,
    ASM_REWRITE_TAC [ROL_SING, LENGTH, (← GSYM ONE)],
    ARITH_SIMP_TAC [],
    STRIP_TAC,
    CLAIM (← q r"LENGTH [\x. x < h; \x. x = h; \x. h < x] = LENGTH sgns"),
    ASM_MESON_TAC [ALL2_LENGTH],
    REWRITE_TAC [LENGTH],
    ARITH_TAC,
    REWRITE_ASSUMS [NOT_NIL],
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    REWRITE_TAC [LENGTH],
    STRIP_TAC,
    CLAIM (← q r"LENGTH sgns = LENGTH (APPEND [\x. x < h; \x. x = h; \x. h < x /\ x < HD t] (TL (partition_line t)))"),
    ASM_MESON_TAC [ALL2_LENGTH],
    DISCH_THEN SUBST1_TAC,
    REWRITE_TAC [LENGTH_APPEND],
    REWRITE_TAC [PARTITION_LINE_LENGTH_TL],
    REWRITE_TAC [LENGTH],
    ARITH_TAC
  ])

  let INTERPMAT_LENGTH ← prove_by_refinement (
    (← q r"!eqs pts sgns. interpmat pts eqs sgns ==>
    (LENGTH sgns = 2 * LENGTH pts + 1)"),
  [
    REPEAT_N 3 STRIP_TAC,
    DISJ_CASES_TAC (← ISPEC (← q r"pts:real list") list_CASES),
    ASM_REWRITE_TAC [interpmat, LENGTH, ROL_NIL, partition_line],
    ARITH_SIMP_TAC [],
    DISJ_CASES_TAC (← ISPEC (← q r"sgns:(sign list) list") list_CASES),
    ASM_REWRITE_TAC [ALL2],
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    ASM_REWRITE_TAC [],
    ASM_REWRITE_TAC [ALL2],
    DISJ_CASES_TAC (← ISPEC (← q r"t:(sign list) list") list_CASES),
    ASM_REWRITE_TAC [ALL2, LENGTH, ONE],
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    ASM_REWRITE_TAC [],
    ASM_REWRITE_TAC [ALL2],
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    ASM_REWRITE_TAC [interpmat, partition_line],
    COND_CASES_TAC,
    ASM_REWRITE_TAC [ROL_SING, LENGTH, (← GSYM ONE)],
    ARITH_SIMP_TAC [],
    STRIP_TAC,
    CLAIM (← q r"LENGTH [\x. x < h; \x. x = h; \x. h < x] = LENGTH sgns"),
    ASM_MESON_TAC [ALL2_LENGTH],
    REWRITE_TAC [LENGTH],
    ARITH_TAC,
    REWRITE_ASSUMS [NOT_NIL],
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    REWRITE_TAC [LENGTH],
    STRIP_TAC,
    CLAIM (← q r"LENGTH sgns = LENGTH (APPEND [\x. x < h; \x. x = h; \x. h < x /\ x < HD t] (TL (partition_line t)))"),
    ASM_MESON_TAC [ALL2_LENGTH],
    DISCH_THEN SUBST1_TAC,
    REWRITE_TAC [LENGTH_APPEND],
    REWRITE_TAC [PARTITION_LINE_LENGTH_TL],
    REWRITE_TAC [LENGTH],
    ARITH_TAC
  ])

  let ALL2_HD ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let p1 ← prove r"(x = y) <=> (y = x)" (MESON_TAC [])
    let q2 ← q r"!b d a c. (LENGTH a = LENGTH c) ==>
    ALL2 P (APPEND a b) (APPEND c d) ==> ALL2 P a c"
    prove_by_refinement (
      q2,
    [
      REPEAT_N 2 STRIP_TAC,
      LIST_INDUCT_TAC,
      ONCE_REWRITE_TAC [p1],
      REWRITE_TAC [LENGTH, LENGTH_EQ_NIL],
      MESON_TAC [ALL2],
      REWRITE_TAC [LENGTH, APPEND],
      LIST_INDUCT_TAC,
      REWRITE_TAC [LENGTH],
      ARITH_TAC,
      REWRITE_TAC [LENGTH, APPEND, ALL2, SUC_INJ],
      ASM_MESON_TAC []
    ])

  let ALL2_TL ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let p1 ← prove r"(x = y) <=> (y = x)" (MESON_TAC [])
    let q2 ← q r"!b d a c. (LENGTH a = LENGTH c) ==>
    ALL2 P (APPEND a b) (APPEND c d) ==> ALL2 P b d"
    prove_by_refinement (
      q2,
    [
      REPEAT_N 2 STRIP_TAC,
      LIST_INDUCT_TAC,
      ONCE_REWRITE_TAC [p1],
      REWRITE_TAC [LENGTH, LENGTH_EQ_NIL],
      MESON_TAC [APPEND],
      REWRITE_TAC [LENGTH, APPEND],
      LIST_INDUCT_TAC,
      REWRITE_TAC [LENGTH],
      ARITH_TAC,
      REWRITE_TAC [ALL2, APPEND, LENGTH, SUC_INJ],
      ASM_MESON_TAC []
    ])

  let ALL2_APPEND_LENGTH ← prove_by_refinement (
    (← q r"!P a c b d. (LENGTH a = LENGTH c) ==>
    ALL2 P (APPEND a b) (APPEND c d) ==> ALL2 P a c /\ ALL2 P b d"),
  [
    ASM_MESON_TAC [ALL2_HD, ALL2_TL]
  ])

  let ALL2_APPEND ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"~(0 = SUC x)")
    prove_by_refinement (
      (← q r"!a c b d. ALL2 P a c /\ ALL2 P b d ==>
        ALL2 P (APPEND a b) (APPEND c d)"),
    [
      REPEAT LIST_INDUCT_TAC THEN REWRITE_ALL [APPEND, ALL2, LENGTH, r1, APPEND_NIL],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      FIRST_ASSUM MATCH_MP_TAC,
      ASM_REWRITE_TAC [],
      ASM_REWRITE_TAC [ALL2]
    ])

  let ALL2_SPLIT ← prove_by_refinement (
    (← q r"!a c b d. (LENGTH a = LENGTH c) ==>
    (ALL2 P (APPEND a b) (APPEND c d) <=> ALL2 P a c /\ ALL2 P b d)"),
  [
    ASM_MESON_TAC [ALL2_APPEND, ALL2_APPEND_LENGTH]
  ])

  let BUTLAST_THM ← prove_by_refinement (
    (← q r"(BUTLAST [] = []) /\
   (BUTLAST [x] = []) /\
   (BUTLAST (CONS h1 (CONS h2 t)) = CONS h1 (BUTLAST (CONS h2 t)))"),
  [
    ASM_MESON_TAC [BUTLAST, NOT_CONS_NIL]
  ])

  let HD_BUTLAST ← prove_by_refinement (
    (← q r"!l. ~(l = []) ==> (!x. ~(l = [x])) ==> (HD (BUTLAST l) = HD l)"),
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [],
    REWRITE_TAC [NOT_CONS_NIL, HD, BUTLAST],
    COND_CASES_TAC,
    ASM_REWRITE_TAC [],
    ASM_MESON_TAC [],
    REPEAT STRIP_TAC,
    REWRITE_TAC [HD]
  ])

  let SUBLIST ← new_recursive_definition list_RECURSION
    r"(SUBLIST l [] <=> (l = [])) /\
   (SUBLIST l (CONS h t) <=> (l = []) \/
    SUBLIST l t \/
    ((HD l = h) /\ SUBLIST (TL l) t))"

  let SUBLIST_NIL ← prove_by_refinement (
    (← q r"!l. SUBLIST [] l"),
  [
    LIST_INDUCT_TAC THEN ASM_MESON_TAC [SUBLIST]
  ])

  let SUBLIST_CONS ← prove_by_refinement (
    (← q r"!l1 l2 h. SUBLIST l1 l2 ==> SUBLIST l1 (CONS h l2)"),
  [
    REPEAT LIST_INDUCT_TAC THEN ASM_MESON_TAC [SUBLIST]
  ])

  let SUBLIST_TL ← prove_by_refinement (
    (← q r"!l1 l2. SUBLIST l1 l2 ==> ~(l1 = []) ==> SUBLIST (TL l1) l2"),
  [
    REPEAT LIST_INDUCT_TAC THEN ASM_MESON_TAC [SUBLIST]
  ])

  let SUBLIST_CONS2 ← prove_by_refinement (
    (← q r"!h t l. SUBLIST (CONS h t) l ==> SUBLIST t l"),
  [
    STRIP_TAC,
    REPEAT LIST_INDUCT_TAC THEN ASM_MESON_TAC [SUBLIST, NOT_CONS_NIL, HD, TL]
  ])

  let SUBLIST_ID ← prove_by_refinement (
    (← q r"!l. SUBLIST l l"),
  [
    LIST_INDUCT_TAC THEN ASM_MESON_TAC [SUBLIST, SUBLIST_NIL, NOT_CONS_NIL, HD, TL]
  ])

  let SUBLIST_CONS_CONS ← prove_by_refinement (
    (← q r"!h t1 t2. SUBLIST (CONS h t1) (CONS h t2) = SUBLIST t1 t2"),
  [
    STRIP_TAC,
    REPEAT LIST_INDUCT_TAC,
    ASM_MESON_TAC [SUBLIST, SUBLIST_NIL, SUBLIST_ID],
    ASM_MESON_TAC [SUBLIST, SUBLIST_NIL, SUBLIST_ID],
    REWRITE_TAC [SUBLIST, SUBLIST_NIL, SUBLIST_ID, NOT_CONS_NIL, HD, TL],
    REWRITE_TAC [SUBLIST, SUBLIST_NIL, SUBLIST_ID, NOT_CONS_NIL, HD, TL, SUBLIST_CONS2, SUBLIST_CONS],
    ASM_MESON_TAC [SUBLIST, SUBLIST_NIL, SUBLIST_ID, NOT_CONS_NIL, HD, TL]
  ])

  let SUBLIST_NEQ ← prove_by_refinement (
    (← q r"!h1 h2 t1 t2. SUBLIST (CONS h1 t1) (CONS h2 t2) ==> ~(h1 = h2) ==>
     SUBLIST (CONS h1 t1) t2"),
  [
    ASM_MESON_TAC [SUBLIST, NOT_CONS_NIL, HD, TL]
  ])

  let SUBLIST_TRANS ← prove_by_refinement (
    (← q r"!l1 l2 l3. SUBLIST l1 l2 ==> SUBLIST l2 l3 ==> SUBLIST l1 l3"),
  [
    REPEAT LIST_INDUCT_TAC,
    ASM_MESON_TAC [SUBLIST],
    ASM_MESON_TAC [SUBLIST],
    ASM_MESON_TAC [SUBLIST],
    ASM_MESON_TAC [SUBLIST],
    ASM_MESON_TAC [SUBLIST],
    ASM_MESON_TAC [SUBLIST],
    ASM_MESON_TAC [SUBLIST],
    REPEAT STRIP_TAC,
    REWRITE_TAC [SUBLIST, NOT_CONS_NIL, HD, TL],
    CASES_ON (← q r"h = h''"),
    DISJ2_TAC,
    ASM_REWRITE_TAC [],
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    CASES_ON (← q r"h' = h''"),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    ASM_MESON_TAC [SUBLIST_CONS_CONS],
    REWRITE_ASSUMS [IMP_AND_THM],
    FIRST_ASSUM MATCH_MP_TAC,
    EVERY_ASSUM (fun x => tactic_of (tryCatch (do pure (MP_TAC (← MATCH_MP SUBLIST_CONS2 x))) (fun _ => do pure (ALL_TAC)))),
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [SUBLIST, NOT_CONS_NIL, HD, TL, SUBLIST_CONS, SUBLIST_CONS2],
    DISJ1_TAC,
    CASES_ON (← q r"h' = h''"),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ASSUMS [SUBLIST_CONS_CONS],
    CLAIM (← q r"SUBLIST (CONS h t) t'"),
    ASM_MESON_TAC [SUBLIST_NEQ],
    STRIP_TAC,
    ASM_MESON_TAC [],
    CASES_ON (← q r"h = h'"),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ASSUMS [SUBLIST_CONS_CONS],
    ASM_MESON_TAC [SUBLIST_NEQ],
    CLAIM (← q r"SUBLIST (CONS h t) t'"),
    ASM_MESON_TAC [SUBLIST_NEQ],
    STRIP_TAC,
    CLAIM (← q r"SUBLIST (CONS h' t') t''"),
    ASM_MESON_TAC [SUBLIST_NEQ],
    STRIP_TAC,
    CLAIM (← q r"SUBLIST t' t''"),
    ASM_MESON_TAC [SUBLIST_CONS2],
    STRIP_TAC,
    ASM_MESON_TAC []
  ])

  let ROL_MEM ← prove_by_refinement (
    (← q r"!h t. real_ordered_list (CONS h t) ==> !x. MEM x t ==> h < x"),
  [
    STRIP_TAC,
    LIST_INDUCT_TAC,
    REWRITE_TAC [MEM],
    REPEAT STRIP_TAC,
    CASES_ON (← q r"x = h'"),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    ASM_MESON_TAC [ROL_CONS_CONS],
    CLAIM (← q r"real_ordered_list (CONS h t)"),
    ASM_MESON_TAC [ROL_CONS_CONS_DELETE],
    DISCH_THEN (REWRITE_ASSUMS o (list : thm → List thm)),
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [MEM]
  ])

  let SUBLIST_MEM ← prove_by_refinement (
    (← q r"!x l1 l2. SUBLIST l1 l2 ==> MEM x l1 ==> MEM x l2"),
  [
    STRIP_TAC,
    REPEAT LIST_INDUCT_TAC,
    REWRITE_TAC [MEM],
    REWRITE_TAC [MEM],
    REWRITE_TAC [SUBLIST, NOT_CONS_NIL],
    REPEAT STRIP_TAC,
    CASES_ON (← q r"h = h'"),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ASSUMS [SUBLIST_CONS_CONS],
    CASES_ON (← q r"x = h'"),
    ASM_MESON_TAC [MEM],
    REWRITE_ASSUMS [IMP_AND_THM],
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [MEM, SUBLIST_CONS],
    CASES_ON (← q r"x = h'"),
    ASM_MESON_TAC [MEM],
    ASM_MESON_TAC [SUBLIST_NEQ, SUBLIST, MEM]
  ])

  let ROL_SUBLIST_LT ← prove_by_refinement (
    (← q r"!h t1 t2. real_ordered_list (CONS h t2) ==>
      SUBLIST (CONS h t1) (CONS h t2) ==> !x. MEM x t1 ==> h < x"),
  [
    STRIP_TAC,
    REPEAT LIST_INDUCT_TAC,
    REWRITE_TAC [MEM],
    REWRITE_TAC [MEM],
    ASM_MESON_TAC [SUBLIST, NOT_CONS_NIL, HD, TL],
    REPEAT STRIP_TAC,
    REWRITE_ASSUMS [SUBLIST_CONS_CONS],
    CLAIM (← q r"MEM x (CONS h'' t')"),
    ASM_MESON_TAC [SUBLIST_MEM],
    STRIP_TAC,
    ASM_MESON_TAC [ROL_MEM]
  ])

  let SUBLIST_DELETE ← prove_by_refinement (
    (← q r"!h1 h2 t l. SUBLIST (CONS h1 (CONS h2 t)) l ==>
    SUBLIST (CONS h1 t) l"),
  [
    STRIP_TAC THEN STRIP_TAC,
    REPEAT LIST_INDUCT_TAC,
    REWRITE_TAC [SUBLIST, NOT_CONS_NIL],
    CASES_ON (← q r"h1 = h"),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_TAC [SUBLIST, NOT_CONS_NIL, HD, TL, SUBLIST_NIL],
    STRIP_TAC,
    CLAIM (← q r"SUBLIST [h1; h2] t"),
    ASM_MESON_TAC [SUBLIST_NEQ],
    DISCH_THEN (REWRITE_ASSUMS o (list : thm → List thm)),
    ASM_MESON_TAC [SUBLIST_CONS],
    REWRITE_TAC [SUBLIST, NOT_CONS_NIL],
    CASES_ON (← q r"h1 = h'"),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_TAC [SUBLIST_CONS_CONS],
    MESON_TAC [SUBLIST_CONS2],
    STRIP_TAC,
    CLAIM (← q r"SUBLIST (CONS h1 (CONS h2 (CONS h t))) t'"),
    ASM_MESON_TAC [SUBLIST_NEQ],
    DISCH_THEN (REWRITE_ASSUMS o (list : thm → List thm)),
    ASM_MESON_TAC [SUBLIST_CONS]
  ])

  let SUBLIST_MATCH ← prove_by_refinement (
    (← q r"!h t l. SUBLIST (CONS h t) l ==>
     ?(l1:A list) l2. (l = APPEND l1 (CONS h l2)) /\ SUBLIST t l2"),
  [
    STRIP_TAC,
    REPEAT LIST_INDUCT_TAC,
    REWRITE_TAC [SUBLIST, NOT_CONS_NIL],
    CASES_ON (← q r"h = h'"),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    STRIP_TAC,
    EXISTS_TAC (← q r"[]"),
    REWRITE_TAC [APPEND, SUBLIST_NIL],
    ASM_MESON_TAC [],
    REWRITE_TAC [SUBLIST_NIL],
    STRIP_TAC,
    CLAIM (← q r"SUBLIST [h] t"),
    ASM_MESON_TAC [SUBLIST_NEQ],
    DISCH_THEN (REWRITE_ASSUMS o (list : thm → List thm)),
    REPEAT (POP_ASSUM MP_TAC),
    REPEAT STRIP_TAC,
    EXISTS_TAC (← q r"CONS h' l1"),
    EXISTS_TAC (← q r"l2"),
    REWRITE_TAC [APPEND],
    AP_TERM_TAC,
    ASM_MESON_TAC [],
    REWRITE_TAC [SUBLIST, NOT_CONS_NIL],
    CASES_ON (← q r"h = h''"),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    STRIP_TAC,
    REWRITE_ASSUMS [SUBLIST_CONS_CONS],
    EXISTS_TAC (← q r"[]:A list"),
    EXISTS_TAC (← q r"t'"),
    ASM_MESON_TAC [APPEND],
    STRIP_TAC,
    CLAIM (← q r"SUBLIST (CONS h (CONS h' t)) t'"),
    ASM_MESON_TAC [SUBLIST_NEQ],
    DISCH_THEN (REWRITE_ASSUMS o (list : thm → List thm)),
    REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [],
    EXISTS_TAC (← q r"CONS h'' l1"),
    EXISTS_TAC (← q r"l2"),
    ASM_REWRITE_TAC [APPEND]
  ])

  let ROL_SUBLIST ← prove_by_refinement (
    (← q r"!l1 l2.  real_ordered_list l2 ==> SUBLIST l1 l2 ==> real_ordered_list l1"),
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [ROL_NIL],
    REWRITE_TAC [real_ordered_list],
    REPEAT STRIP_TAC,
    REWRITE_ASSUMS [IMP_AND_THM],
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [SUBLIST_CONS2],
    CASES_ON (← q r"t = []"),
    ASM_REWRITE_TAC [],
    ASM_REWRITE_TAC [],
    REWRITE_ASSUMS [NOT_NIL],
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_TAC [HD],
    DISJ_CASES_TAC (← ISPEC (← q r"l2:real list") list_CASES),
    ASM_MESON_TAC [SUBLIST, NOT_CONS_NIL],
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    CASES_ON (← q r"h = h''"),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    ASM_MESON_TAC [ROL_SUBLIST_LT, MEM],
    FIRST_ASSUM (fun x => tactic_of do pure (MP_TAC (← MATCH_MP SUBLIST_MATCH x))),
    STRIP_TAC,
    CLAIM (← q r"real_ordered_list (CONS h l2')"),
    ASM_MESON_TAC [ROL_APPEND],
    STRIP_TAC,
    CLAIM (← q r"MEM h' l2'"),
    ASM_MESON_TAC [SUBLIST_MEM, MEM],
    STRIP_TAC,
    ASM_MESON_TAC [ROL_MEM]
  ])

  let SUBLIST_BUTLAST ← prove_by_refinement (
    (← q r"!l. SUBLIST (BUTLAST l) l"),
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [BUTLAST, SUBLIST_NIL],
    REWRITE_TAC [BUTLAST, SUBLIST_NIL, SUBLIST],
    REPEAT COND_CASES_TAC,
    REWRITE_TAC [SUBLIST_NIL],
    ASM_REWRITE_TAC [HD, TL, NOT_CONS_NIL]
  ])

  let SUBLIST_APPEND_HD ← prove_by_refinement (
    (← q r"!l2 l3 l1. SUBLIST (APPEND l1 l2) (APPEND l1 l3) = SUBLIST l2 l3"),
  [
    REPEAT_N 2 STRIP_TAC,
    LIST_INDUCT_TAC,
    REWRITE_TAC [APPEND],
    ASM_REWRITE_TAC [APPEND, SUBLIST_CONS_CONS]
  ])

  let SUBLIST_ID_CONS ← prove_by_refinement (
    (← q r"!h l. ~(SUBLIST (CONS h l) l)"),
  [
    STRIP_TAC,
    LIST_INDUCT_TAC,
    REWRITE_TAC [SUBLIST, NOT_CONS_NIL],
    ASM_REWRITE_TAC [SUBLIST, NOT_CONS_NIL, HD, TL],
    ASM_MESON_TAC [SUBLIST_DELETE]
  ])

  let SUBLIST_ID_APPEND ← prove_by_refinement (
    (← q r"!m l. ~(l = []) ==> ~(SUBLIST (APPEND l m) m)"),
  [
    STRIP_TAC,
    LIST_INDUCT_TAC,
    REWRITE_TAC [],
    REWRITE_TAC [APPEND],
    DISCH_THEN (fun _x => ALL_TAC),
    CASES_ON (← q r"t = []"),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_TAC [APPEND, SUBLIST_ID_CONS],
    POP_ASSUM (fun x => REWRITE_ASSUMS [x] THEN ASSUME_TAC x),
    ASM_MESON_TAC [SUBLIST_CONS2]
  ])

  let SUBLIST_APPEND_TL ← prove_by_refinement (
    (← q r"!l3 l1 l2. SUBLIST (APPEND l1 l3) (APPEND l2 l3) = SUBLIST l1 l2"),
  [
    STRIP_TAC,
    REPEAT LIST_INDUCT_TAC,
    REWRITE_TAC [APPEND, APPEND_NIL, SUBLIST, SUBLIST_ID],
    REWRITE_ALL [SUBLIST_NIL, APPEND, APPEND_NIL, SUBLIST, SUBLIST_ID],
    ASM_REWRITE_TAC [],
    REWRITE_ALL [SUBLIST_NIL, SUBLIST, SUBLIST_ID, NOT_CONS_NIL],
    ASM_MESON_TAC [SUBLIST_ID_APPEND, APPEND, NOT_CONS_NIL],
    REWRITE_TAC [APPEND],
    CASES_ON (← q r"h = h'"),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    EQ_TAC,
    REWRITE_TAC [SUBLIST, APPEND, HD, TL, NOT_CONS_NIL],
    STRIP_TAC,
    ASM_MESON_TAC [APPEND],
    ASM_MESON_TAC [APPEND],
    REWRITE_TAC [SUBLIST_CONS_CONS],
    ASM_MESON_TAC [],
    EQ_TAC,
    STRIP_TAC,
    MATCH_MP_TAC SUBLIST_CONS,
    CLAIM (← q r"SUBLIST (CONS h (APPEND t l3)) (APPEND t' l3)"),
    ASM_MESON_TAC [SUBLIST_NEQ],
    STRIP_TAC,
    ASM_MESON_TAC [APPEND],
    ASM_REWRITE_TAC [NOT_CONS_NIL, SUBLIST, HD, TL],
    STRIP_TAC,
    ASM_MESON_TAC [APPEND]
  ])

  let SUBLIST_TRANS2 ← REWRITE_RULE [IMP_AND_THM] SUBLIST_TRANS

  let APPEND_CONS ← prove_by_refinement (
    (← q r"!h l1 l2. APPEND l1 (CONS h l2) = APPEND (APPEND l1 [h]) l2"),
  [
    STRIP_TAC,
    REPEAT LIST_INDUCT_TAC THEN REWRITE_TAC [APPEND_NIL, APPEND],
    ASM_MESON_TAC []
  ])

  let SUBLIST_APPEND ← prove_by_refinement (
    (← q r"!l1 l2 m1 m2. SUBLIST l1 l2 ==> SUBLIST m1 m2 ==>
    SUBLIST (APPEND l1 m1) (APPEND l2 m2)"),
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [SUBLIST_NIL, APPEND],
    LIST_INDUCT_TAC,
    REWRITE_TAC [APPEND],
    REPEAT STRIP_TAC,
    POP_ASSUM (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (ASSUME_TAC (← MATCH_MP y x) THEN ASSUME_TAC x)))),
    REWRITE_TAC [APPEND],
    ASM_MESON_TAC [SUBLIST_CONS],
    LIST_INDUCT_TAC,
    MESON_TAC [SUBLIST, NOT_CONS_NIL],
    CASES_ON (← q r"h = h'"),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_TAC [SUBLIST_CONS_CONS],
    REWRITE_TAC [SUBLIST_CONS_CONS, APPEND],
    ASM_MESON_TAC [],
    REPEAT STRIP_TAC,
    CLAIM (← q r"SUBLIST (CONS h t) t'"),
    ASM_MESON_TAC [SUBLIST_NEQ],
    DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    POP_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    ASM_MESON_TAC [APPEND, SUBLIST_CONS]
  ])

  let SUBLIST_APPEND2 ← REWRITE_RULE [IMP_AND_THM] SUBLIST_APPEND

  let ROL_APPEND2 ← prove_by_refinement (
    (← q r"!l2 l1. real_ordered_list (APPEND l1 l2) ==>
           real_ordered_list (APPEND l1 (BUTLAST l2))"),
  [
    REPEAT STRIP_TAC,
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ROL_SUBLIST),
    EXISTS_TAC (← q r"APPEND l1 l2"),
    ASM_REWRITE_TAC [SUBLIST_APPEND_HD, SUBLIST_BUTLAST]
  ])

  let PL_LEM ← prove_by_refinement (
    (← q r"!l. ~(l = []) ==> ~(TL (partition_line l) = [])"),
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [],
    STRIP_TAC,
    REWRITE_TAC [partition_line],
    ASM_MESON_TAC [NOT_CONS_NIL, APPEND, TL]
  ])

  let HD_APPEND2 ← prove_by_refinement (
    (← q r"!l m. ~(l = []) ==> (HD (APPEND l m) = HD l)"),
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [],
    REPEAT STRIP_TAC,
    REWRITE_TAC [APPEND, HD]
  ])

  let BUTLAST_TL ← prove_by_refinement (
    (← q r"!l. LENGTH l > 1 ==> (BUTLAST (TL l) = TL (BUTLAST l))"),
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [LENGTH] THEN ARITH_TAC,
    REWRITE_TAC [LENGTH],
    STRIP_TAC,
    REWRITE_TAC [TL, BUTLAST],
    COND_CASES_TAC,
    REWRITE_ASSUMS [(← GSYM LENGTH_0)],
    REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC,
    REWRITE_ASSUMS [NOT_NIL],
    POP_ASSUM MP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [],
    REWRITE_TAC [TL, BUTLAST]
  ])

  let APPEND_TL ← prove_by_refinement (
    (← q r"!m l. ~(l = []) ==> (APPEND (TL l) m = TL (APPEND l m))"),
  [
    STRIP_TAC,
    LIST_INDUCT_TAC,
    REWRITE_TAC [],
    REWRITE_TAC [APPEND, TL]
  ])

  let APPEND_HD ← prove_by_refinement (
    (← q r"!m l. ~(l = []) ==> (HD (APPEND l m) = HD l)"),
  [
    STRIP_TAC,
    LIST_INDUCT_TAC,
    REWRITE_TAC [],
    STRIP_TAC,
    REWRITE_TAC [APPEND, HD]
  ])

  let PL_LEM2 ← prove_by_refinement (
    (← q r"!l. ~(l = []) ==> LENGTH (partition_line l) > 1"),
  [
    LIST_INDUCT_TAC THEN REWRITE_TAC [],
    REWRITE_TAC [partition_line],
    STRIP_TAC,
    COND_CASES_TAC,
    REWRITE_TAC [LENGTH] THEN ARITH_TAC,
    REWRITE_TAC [APPEND, LENGTH] THEN ARITH_TAC
  ])

  let BUTLAST_APPEND ← prove_by_refinement (
    (← q r"!l m. ~(m = []) ==>
     (BUTLAST (APPEND l m) = APPEND l (BUTLAST m))"),
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [APPEND],
    REPEAT STRIP_TAC,
    REWRITE_TAC [APPEND, BUTLAST],
    ASM_MESON_TAC [APPEND_EQ_NIL]
  ])

  let LENGTH_TL1 ← prove_by_refinement (
    (← q r"!l. LENGTH l > 1 ==> ~(TL l = [])"),
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [LENGTH] THEN ARITH_TAC,
    REWRITE_TAC [LENGTH, TL],
    REPEAT STRIP_TAC,
    POP_ASSUM (REWRITE_ASSUMS o (list : thm → List thm)),
    REWRITE_ASSUMS [LENGTH],
    POP_ASSUM MP_TAC THEN ARITH_TAC
  ])

  let PL_BUTLAST ← prove_by_refinement (
    (← q r"!l. ~(l = []) ==> ~(BUTLAST (partition_line l) = [])"),
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [],
    REWRITE_TAC [partition_line],
    COND_CASES_TAC,
    REWRITE_TAC [APPEND, NOT_CONS_NIL, BUTLAST],
    REWRITE_TAC [APPEND, NOT_CONS_NIL, BUTLAST]
  ])

  let PARTITION_LINE_APPEND ← prove_by_refinement (
    (← q r"!h t l. ~(l = []) ==>
    (partition_line (APPEND l (CONS h t)) =
      APPEND (BUTLAST (partition_line l))
        (CONS (\x. LAST l < x /\ x < h)
          (TL (partition_line (CONS h t)))))"),
  [
    STRIP_TAC THEN STRIP_TAC,
    LIST_INDUCT_TAC,
    REWRITE_TAC [],
    DISCH_THEN (fun _x => ALL_TAC),
    CASES_ON (← q r"t' = []"),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_TAC [HD, APPEND, partition_line, BUTLAST, LAST, TL, NOT_CONS_NIL],
    POP_ASSUM (fun x => REWRITE_ASSUMS [x] THEN ASSUME_TAC x),
    REWRITE_TAC [APPEND],
    CONV_TAC (LAND_CONV (REWRITE_CONV [partition_line])),
    COND_CASES_TAC,
    ASM_MESON_TAC [NOT_CONS_NIL, APPEND_EQ_NIL],
    POP_ASSUM (fun _x => ALL_TAC),
    ASM_REWRITE_TAC [],
    ASM_REWRITE_TAC [LAST],
    ASM_SIMP_TAC [APPEND_HD],
    CONV_TAC (RAND_CONV (LAND_CONV (RAND_CONV (REWRITE_CONV [partition_line])))),
    ASM_REWRITE_TAC [],
    REWRITE_TAC [APPEND, BUTLAST, NOT_CONS_NIL],
    REPEAT AP_TERM_TAC,
    COND_CASES_TAC,
    ASM_MESON_TAC [PL_LEM2, LENGTH_TL1],
    REWRITE_TAC [APPEND],
    AP_TERM_TAC,
    MP_TAC (← ISPEC (← q r"t':real list") PL_LEM2),
    ASM_REWRITE_TAC [],
    STRIP_TAC,
    ASM_SIMP_TAC [BUTLAST_TL],
    MP_TAC (← ISPEC (← q r"t':real list") PL_BUTLAST),
    ASM_REWRITE_TAC [],
    STRIP_TAC,
    ASM_SIMP_TAC [APPEND_TL]
  ])

  let HD_TL ← prove_by_refinement (
    (← q r"!l. ~(l = []) ==> (l = CONS (HD l) (TL l))"),
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [],
    REWRITE_TAC [HD, TL]
  ])

  let HD_LEM ← prove_by_refinement (
    (← q r"!l1 l2. (TL l1 = l2) <=> (CONS (HD l1) (TL l1) = CONS (HD l1) l2)"),
  [
    MESON_TAC [CONS_11]
  ])

  -- `let rec LENGTH_N n ty = ..` (by hand; its recursion is LENGTH_N.go)
  let LENGTH_N : Int → hol_type → ExceptT String IO thm ← pure
    (LENGTH_N.go TAUT ARITH_TAC mk_small_numeral LENGTH LENGTH_SING LENGTH_0 LENGTH_TL HD_TL
      HD_LEM PRE)

  let BUTLAST_LENGTH ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"~(n = 0) ==> (SUC(PRE n) = PRE(SUC n))")
    prove_by_refinement (
      (← q r"!l. ~(l = []) ==> (LENGTH (BUTLAST l) = PRE (LENGTH l))"),
    [
      LIST_INDUCT_TAC THEN REWRITE_TAC [],
      REWRITE_TAC [BUTLAST, LENGTH],
      COND_CASES_TAC,
      ASM_REWRITE_TAC [NOT_CONS_NIL, LENGTH],
      ARITH_TAC,
      ASM_REWRITE_TAC [NOT_CONS_NIL, LENGTH],
      ASM_SIMP_TAC [],
      MATCH_MP_TAC r1,
      ASM_MESON_TAC [LENGTH_0]
    ])

  -- @@RETURN BEGIN
  return { INTERPSIGNS_CONJ, INTERPMAT_TRIO, PARTITION_LINE_NOT_NIL, ALL2_LENGTH,
           LENGTH_TL, PARTITION_LINE_LENGTH, PARTITION_LINE_LENGTH_TL, PL_ALL2_LENGTH,
           INTERPMAT_LENGTH, ALL2_HD, ALL2_TL, ALL2_APPEND_LENGTH, ALL2_APPEND,
           ALL2_SPLIT, BUTLAST_THM, HD_BUTLAST, SUBLIST, SUBLIST_NIL, SUBLIST_CONS,
           SUBLIST_TL, SUBLIST_CONS2, SUBLIST_ID, SUBLIST_CONS_CONS, SUBLIST_NEQ,
           SUBLIST_TRANS, ROL_MEM, SUBLIST_MEM, ROL_SUBLIST_LT, SUBLIST_DELETE,
           SUBLIST_MATCH, ROL_SUBLIST, SUBLIST_BUTLAST, SUBLIST_APPEND_HD,
           SUBLIST_ID_CONS, SUBLIST_ID_APPEND, SUBLIST_APPEND_TL, SUBLIST_TRANS2,
           APPEND_CONS, SUBLIST_APPEND, SUBLIST_APPEND2, ROL_APPEND2, PL_LEM, HD_APPEND2,
           BUTLAST_TL, APPEND_TL, APPEND_HD, PL_LEM2, BUTLAST_APPEND, LENGTH_TL1,
           PL_BUTLAST, PARTITION_LINE_APPEND, HD_TL, HD_LEM, LENGTH_N, BUTLAST_LENGTH }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- work_thms.ml phrases from line 989 to 1877; the theorems               -/
/- converted by gxwork/rq/ml2lean.py (disclosed; comments in the          -/
/- proofs are not carried over), the functions by hand.                   -/
/- ---------------------------------------------------------------------- -/

structure WorkThms02 where
  -- @@FIELDS
  ALL2_LEM : thm
  INTERPMAT_TRIO_TL : thm
  LAST_APPEND : thm
  APPEND_APPEND : thm
  ALL2_LEM2 : thm
  INTERPMAT_TRIO_INNER : thm
  INTERPMAT_SING : thm
  INFERISIGN_POS_POS_POS : thm
  INFERISIGN_POS_POS_NEG : thm
  INFERISIGN_NEG_NEG_POS : thm
  INFERISIGN_NEG_NEG_NEG : thm
  ALL2_INTERPSIGN_SUBSET : thm
  HD_APPEND1 : thm
  ROL_APPEND_INSERT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupWorkThms02 [HolBase] (D : WorkThmsDeps) (BWorkThms01 : WorkThms01) :
    ExceptT String IO WorkThms02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_SIMP_TAC, ARITH_TAC, ASM_MESON_TAC, CASES_ON, CLAIM,
        EXISTS_TAC, LIST_INDUCT_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC,
        prove_by_refinement, .. } := D
  let { ALL2, APPEND, APPEND_EQ_NIL, BUTLAST, HD, IMP_AND_THM, IN, INTERPSIGNS_SUBSET,
        INTERPSIGN_SUBSET, LAST, LENGTH, LENGTH_0, LENGTH_1, LENGTH_APPEND,
        LENGTH_PAIR, NOT_CONS_NIL, NOT_NIL, ROL_APPEND, ROL_NIL, ROL_SING, SUBSET, TL,
        interpmat, interpsign, interpsigns, list_CASES, neg_neg_neq_thm,
        partition_line, pos_pos_neq_thm, real_gt, real_ordered_list, .. } := D.core1
  let { ALL2_APPEND, ALL2_APPEND_LENGTH, ALL2_LENGTH, ALL2_SPLIT, APPEND_CONS,
        BUTLAST_LENGTH, INTERPSIGNS_CONJ, LENGTH_TL, LENGTH_TL1, PARTITION_LINE_APPEND,
        PARTITION_LINE_LENGTH, PARTITION_LINE_NOT_NIL, PL_LEM2, ROL_SUBLIST,
        SUBLIST_APPEND_HD, SUBLIST_CONS, SUBLIST_CONS_CONS, SUBLIST_ID, SUBLIST_NIL, .. } := BWorkThms01
  -- @@SCOPE END

  let ALL2_LEM ← prove_by_refinement (
    (← q r"!a b x y s eqs pts sgns.
   ALL2 (interpsigns eqs) (partition_line
    (APPEND pts [x; y])) (APPEND sgns [a; b; s; s; s]) ==>
   ALL2 (interpsigns eqs) (partition_line
    (APPEND pts [x])) (APPEND sgns [a; b; s])"),
  [
    REPEAT STRIP_TAC,
    DISJ_CASES_TAC (← ISPEC (← q r"pts:real list") list_CASES),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [APPEND, partition_line, NOT_CONS_NIL, HD, TL],
    CLAIM (← q r"sgns = []"),
    CLAIM (← q r"LENGTH [\x'. x' < x; \x'. x' = x; \x'. x < x' /\ x' < y; \x. x = y; \x. y < x] = LENGTH (APPEND sgns [a; b; s; s; s])"),
    ASM_MESON_TAC [ALL2_LENGTH],
    REWRITE_TAC [LENGTH, LENGTH_APPEND, (← GSYM LENGTH_0)],
    ARITH_TAC,
    DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [APPEND, ALL2],
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    ASM_REWRITE_TAC [],
    MATCH_MP_TAC INTERPSIGNS_SUBSET,
    EXISTS_TAC (← q r"\z. x < z /\ z < y \/ (z = y) \/ y < z"),
    STRIP_TAC,
    MATCH_MP_TAC INTERPSIGNS_CONJ,
    ASM_REWRITE_TAC [],
    MATCH_MP_TAC INTERPSIGNS_CONJ,
    ASM_REWRITE_TAC [],
    REWRITE_TAC [SUBSET, IN],
    REAL_ARITH_TAC,
    POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    POP_ASSUM MP_TAC,
    ASM_SIMP_TAC [PARTITION_LINE_APPEND, NOT_CONS_NIL],
    STRIP_TAC,
    CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line (CONS (h:real) t))) (CONS (\x'. LAST (CONS h t) < x' /\ x' < x) (TL (partition_line [x; y])))) = LENGTH (APPEND sgns [(a:sign list); b; s; s; s])"),
    ASM_MESON_TAC [ALL2_LENGTH],
    CLAIM (← q r"~(partition_line [x; y] = [])"),
    REWRITE_TAC [APPEND, NOT_CONS_NIL, partition_line],
    REWRITE_TAC [TL, APPEND, NOT_CONS_NIL, LENGTH_APPEND, PARTITION_LINE_LENGTH, LENGTH, LENGTH_TL],
    STRIP_TAC,
    ASM_SIMP_TAC [LENGTH_TL],
    REWRITE_TAC [partition_line, NOT_CONS_NIL],
    COND_CASES_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_TAC [HD, LENGTH, APPEND, TL, BUTLAST, NOT_CONS_NIL],
    ARITH_SIMP_TAC [],
    STRIP_TAC,
    CLAIM (← q r"LENGTH sgns = 2"),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    REWRITE_TAC [LENGTH_PAIR],
    STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [partition_line, BUTLAST, LAST, ALL2, TL, APPEND, NOT_CONS_NIL, LENGTH_APPEND, PARTITION_LINE_LENGTH, LENGTH, LENGTH_TL],
    ASM_REWRITE_TAC [],
    POP_ASSUM (fun _x => ALL_TAC),
    POP_ASSUM (fun _x => ALL_TAC),
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    MATCH_MP_TAC INTERPSIGNS_SUBSET,
    REWRITE_ASSUMS [HD],
    EXISTS_TAC (← q r"\z. x < z /\ z < y \/ (z = y) \/ y < z"),
    STRIP_TAC,
    MATCH_MP_TAC INTERPSIGNS_CONJ,
    ASM_REWRITE_TAC [],
    MATCH_MP_TAC INTERPSIGNS_CONJ,
    ASM_REWRITE_TAC [],
    REWRITE_TAC [SUBSET, IN],
    REAL_ARITH_TAC,
    REWRITE_ALL [HD, partition_line, BUTLAST, LAST, ALL2, TL, APPEND, NOT_CONS_NIL, LENGTH_APPEND, PARTITION_LINE_LENGTH, LENGTH, LENGTH_TL],
    POP_ASSUM (fun x => REWRITE_ASSUMS [x] THEN ASSUME_TAC x),
    COND_CASES_TAC,
    ASM_MESON_TAC [PL_LEM2, LENGTH_TL1],
    ARITH_SIMP_TAC [LENGTH],
    ASM_SIMP_TAC [PARTITION_LINE_LENGTH],
    ASM_SIMP_TAC [BUTLAST_LENGTH],
    CLAIM (← q r"~(partition_line t =  [])"),
    REWRITE_ASSUMS [NOT_NIL],
    POP_ASSUM (fun _x => ALL_TAC),
    POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_TAC [partition_line, NOT_CONS_NIL, list_CASES, APPEND],
    COND_CASES_TAC,
    MESON_TAC [NOT_CONS_NIL],
    MESON_TAC [NOT_CONS_NIL],
    STRIP_TAC,
    ASM_SIMP_TAC [LENGTH_TL],
    STRIP_TAC,
    MP_TAC (← ISPEC (← q r"t:real list") PARTITION_LINE_LENGTH),
    STRIP_TAC,
    CLAIM (← q r"~(LENGTH (partition_line t) = 0)"),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP PL_LEM2)),
    STRIP_TAC,
    CLAIM (← q r"~(PRE (LENGTH (partition_line t)) = 0)"),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    CLAIM (← q r"SUC(LENGTH (partition_line t)) = LENGTH sgns"),
    REPEAT_N 5 (POP_ASSUM MP_TAC) THEN ARITH_TAC,
    DISCH_THEN (ASSUME_TAC o GSYM),
    POP_ASSUM (fun x => REWRITE_ASSUMS [x] THEN ASSUME_TAC x),
    REWRITE_TAC [(← GSYM APPEND)],
    CLAIM (← q r"(ALL2 (interpsigns eqs) (BUTLAST
        (CONS (\x. x < h)
        (CONS (\x. x = h)
        (CONS (\x. h < x /\ x < HD t) (TL (partition_line t))))))
        sgns) /\ (ALL2 (interpsigns eqs) [\x'. LAST t < x' /\ x' < x; \x'. x' = x; \x'. x < x' /\
                                                      x' < y;
       \x. x = y; \x. y < x] [a; b; s; s; s])"),
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_APPEND_LENGTH),
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [BUTLAST, NOT_CONS_NIL, LENGTH],
    ASM_SIMP_TAC [BUTLAST_LENGTH, LENGTH_TL],
    CLAIM (← q r"~(LENGTH t = 0)"),
    ASM_MESON_TAC [LENGTH_0],
    ARITH_TAC,
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    MATCH_MP_TAC ALL2_APPEND,
    STRIP_TAC,
    REWRITE_ASSUMS [BUTLAST, NOT_CONS_NIL],
    ASM_MESON_TAC [],
    REWRITE_ALL [BUTLAST, LAST, ALL2, TL, APPEND, NOT_CONS_NIL, LENGTH_APPEND, PARTITION_LINE_LENGTH, LENGTH, LENGTH_TL],
    ASM_REWRITE_TAC [],
    MATCH_MP_TAC INTERPSIGNS_SUBSET,
    EXISTS_TAC (← q r"\z. x < z /\ z < y \/ (z = y) \/ y < z"),
    STRIP_TAC,
    MATCH_MP_TAC INTERPSIGNS_CONJ,
    ASM_REWRITE_TAC [],
    MATCH_MP_TAC INTERPSIGNS_CONJ,
    ASM_REWRITE_TAC [],
    REWRITE_TAC [SUBSET, IN],
    REAL_ARITH_TAC
  ])

  let INTERPMAT_TRIO_TL ← prove_by_refinement (
    (← q r"!a b x y s eqs pts sgns.
     interpmat (APPEND pts [x; y]) eqs
        (APPEND sgns [a; b; s; s; s]) ==>
     interpmat (APPEND pts [x]) eqs (APPEND sgns [a; b; s])"),
  [
    REWRITE_TAC [interpmat],
    REPEAT STRIP_TAC,
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ROL_SUBLIST),
    EXISTS_TAC (← q r"APPEND pts [x; y]"),
    ASM_REWRITE_TAC [SUBLIST_APPEND_HD, SUBLIST_CONS_CONS, SUBLIST_NIL],
    MATCH_MP_TAC ALL2_LEM,
    ASM_MESON_TAC []
  ])

  let LAST_APPEND ← prove_by_refinement (
    (← q r"!l1 l2. ~(l2 = []) ==> (LAST (APPEND l1 l2) = LAST l2)"),
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [APPEND],
    REWRITE_TAC [APPEND, LAST],
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [APPEND_EQ_NIL],
    ASM_MESON_TAC []
  ])

  let APPEND_APPEND ← prove_by_refinement (
    (← q r"!l1 l2 l3. APPEND (APPEND l1 l2) l3 = APPEND l1 (APPEND l2 l3)"),
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [APPEND],
    REWRITE_TAC [APPEND],
    ASM_MESON_TAC []
  ])

  let ALL2_LEM2 ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"2 * 0 = 0")
    prove_by_refinement (
      (← q r"!a b x y s eqs pts sgns qts rgns.
     ALL2 (interpsigns eqs) (partition_line
      (APPEND pts (CONS x (CONS y qts))))
      (APPEND sgns (CONS a (CONS b
        (CONS s (CONS s (CONS s rgns)))))) ==>
     (LENGTH sgns = 2 * LENGTH pts) ==>
     ALL2 (interpsigns eqs) (partition_line
      (APPEND pts (CONS x qts)))
      (APPEND sgns (CONS a (CONS b (CONS s rgns))))"),
    [
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (partition_line
      (APPEND pts (CONS x (CONS y qts)))) =
      LENGTH (APPEND sgns (CONS (a:sign list) (CONS b
        (CONS s (CONS s (CONS s rgns))))))"),
      ASM_MESON_TAC [ALL2_LENGTH],
      ASM_REWRITE_TAC [PARTITION_LINE_LENGTH, LENGTH, APPEND, LENGTH_APPEND],
      STRIP_TAC,
      CLAIM (← q r"LENGTH rgns = 2 * LENGTH qts"),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      POP_ASSUM (fun _x => ALL_TAC),
      STRIP_TAC,
      CASES_ON (← q r"pts = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      CLAIM (← q r"sgns = []"),
      ASM_MESON_TAC [r1, LENGTH_0, LENGTH],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [partition_line, NOT_CONS_NIL, HD, TL, APPEND],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [ALL2, partition_line, NOT_CONS_NIL, HD, TL, APPEND],
      REPEAT_N 3 STRIP_TAC,
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC INTERPSIGNS_SUBSET,
      EXISTS_TAC (← q r"\(z:real). x < z /\ z < y \/ (z = y) \/ y < z"),
      STRIP_TAC,
      MATCH_MP_TAC INTERPSIGNS_CONJ,
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC INTERPSIGNS_CONJ,
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REAL_ARITH_TAC,
      ASM_REWRITE_TAC [],
      REWRITE_TAC [ALL2, partition_line, NOT_CONS_NIL, HD, TL, APPEND],
      REPEAT_N 3 STRIP_TAC,
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC INTERPSIGNS_SUBSET,
      EXISTS_TAC (← q r"\(z:real). x < z /\ z < y \/ (z = y) \/ y < z /\ z < HD qts"),
      STRIP_TAC,
      MATCH_MP_TAC INTERPSIGNS_CONJ,
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC INTERPSIGNS_CONJ,
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REAL_ARITH_TAC,
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND],
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      CLAIM (← q r"LENGTH (BUTLAST (partition_line pts)) = LENGTH sgns"),
      ASM_REWRITE_TAC [],
      ASSUME_TAC (← ISPEC (← q r"pts:real list") PARTITION_LINE_NOT_NIL),
      ASM_SIMP_TAC [BUTLAST_LENGTH],
      REWRITE_TAC [PARTITION_LINE_LENGTH],
      ARITH_TAC,
      STRIP_TAC,
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [ALL2_SPLIT],
      REWRITE_ALL [partition_line, NOT_CONS_NIL, HD, TL],
      COND_CASES_TAC,
      REWRITE_TAC [ALL2, TL, HD, APPEND],
      REPEAT_N 4 STRIP_TAC,
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC INTERPSIGNS_SUBSET,
      EXISTS_TAC (← q r"\(z:real). x < z /\ z < y \/ (z = y) \/ y < z"),
      STRIP_TAC,
      MATCH_MP_TAC INTERPSIGNS_CONJ,
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC INTERPSIGNS_CONJ,
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REAL_ARITH_TAC,
      REWRITE_TAC [APPEND, TL, HD, ALL2],
      REPEAT_N 4 STRIP_TAC,
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC INTERPSIGNS_SUBSET,
      EXISTS_TAC (← q r"\(z:real). x < z /\ z < y \/ (z = y) \/ y < z /\ z < HD qts"),
      STRIP_TAC,
      MATCH_MP_TAC INTERPSIGNS_CONJ,
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC INTERPSIGNS_CONJ,
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REAL_ARITH_TAC
    ])

  let INTERPMAT_TRIO_INNER ← prove_by_refinement (
    (← q r"!a b x y s eqs qts rgns pts sgns.
     interpmat (APPEND pts (CONS x (CONS y qts))) eqs
        (APPEND sgns (CONS a (CONS b
          (CONS s (CONS s (CONS s rgns)))))) ==>
        (LENGTH sgns = 2 * LENGTH pts) ==>
       interpmat (APPEND pts (CONS x qts)) eqs
        (APPEND sgns (CONS a (CONS b (CONS s rgns))))"),
  [
    REWRITE_TAC [interpmat],
    REPEAT STRIP_TAC,
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ROL_SUBLIST),
    EXISTS_TAC (← q r"(APPEND pts (CONS x (CONS y qts)))"),
    ASM_REWRITE_TAC [SUBLIST_APPEND_HD, SUBLIST_CONS_CONS, SUBLIST_NIL],
    MESON_TAC [SUBLIST_CONS, SUBLIST_ID],
    ASM_MESON_TAC [ALL2_LEM2]
  ])

  let INTERPMAT_SING ← prove_by_refinement (
    (← q r"!x l.  interpmat [x] eqs [l; l; l] ==> interpmat [] eqs [l]"),
  [
    REWRITE_TAC [interpmat],
    REWRITE_TAC [ROL_SING, partition_line, ROL_NIL, ALL2],
    REPEAT STRIP_TAC,
    MATCH_MP_TAC INTERPSIGNS_SUBSET,
    EXISTS_TAC (← q r"\(z:real). x < z \/ (z = x) \/ z < x"),
    STRIP_TAC,
    MATCH_MP_TAC INTERPSIGNS_CONJ,
    ASM_REWRITE_TAC [],
    MATCH_MP_TAC INTERPSIGNS_CONJ,
    ASM_REWRITE_TAC [],
    REWRITE_TAC [SUBSET, IN],
    REAL_ARITH_TAC
  ])

  let INFERISIGN_POS_POS_POS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r3 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    let r5 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    prove_by_refinement (
      (← q r"!y z p pts qts eqs sgns rgns r1 r2 r3.
       interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Pos r1)
             (CONS (CONS Unknown (CONS Pos r2))
              (CONS (CONS Pos r3) rgns)))) ==>
       (LENGTH sgns = 2 * LENGTH pts + 1) ==>
      interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Pos r1)
             (CONS (CONS Pos (CONS Pos r2))
              (CONS (CONS Pos r3) rgns))))"),
    [
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"~(sgns = [])"),
      REWRITE_TAC [(← GSYM LENGTH_0)],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = LENGTH (APPEND sgns (CONS (CONS Pos r1) (CONS (CONS Unknown (CONS Pos r2)) (CONS (CONS Pos r3) rgns))))"),
      ASM_MESON_TAC [ALL2_LENGTH],
      STRIP_TAC,
      CASES_ON (← q r"pts = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      CLAIM (← q r"LENGTH sgns = 1"),
      POP_ASSUM (fun _x => ALL_TAC),
      REWRITE_ALL [LENGTH],
      ASM_REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [LENGTH_1],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [partition_line, TL, HD, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, APPEND, ALL2, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] pos_pos_neq_thm),
      REWRITE_ALL [real_ordered_list, NOT_CONS_NIL, HD, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt, ALL2, interpsigns, interpsign],
      ASM_MESON_TAC [],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [r5],
      REWRITE_TAC [LENGTH, APPEND, TL, HD, ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] pos_pos_neq_thm),
      REWRITE_ALL [interpsign, real_ordered_list, NOT_CONS_NIL, HD, ALL2],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt],
      ASM_MESON_TAC [],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [r4],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND, partition_line, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, HD, APPEND, ALL2],
      CLAIM (← q r"APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]"),
      MESON_TAC [APPEND, APPEND_CONS],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] pos_pos_neq_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list [y; z]"),
      ASM_MESON_TAC [ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [r3],
      REWRITE_TAC [APPEND, TL, HD, ALL2],
      REPEAT STRIP_TAC,
      CLAIM (← q r"!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j"),
      MESON_TAC [APPEND, APPEND_CONS],
      DISCH_THEN (fun x => ONCE_REWRITE_TAC [x] THEN ONCE_REWRITE_ASSUMS [x]),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [LENGTH_APPEND, BUTLAST_LENGTH, LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      REWRITE_ALL [TL, APPEND, HD],
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] pos_pos_neq_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list (CONS y (CONS z qts))"),
      ASM_MESON_TAC [ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [r2],
      ASM_MESON_TAC [r1]
    ])

  let INFERISIGN_POS_POS_NEG ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r3 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r5 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    prove_by_refinement (
      (← q r"!y z p pts qts eqs sgns rgns r1 r2 r3.
       interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Pos r1)
             (CONS (CONS Unknown (CONS Neg r2))
              (CONS (CONS Pos r3) rgns)))) ==>
       (LENGTH sgns = 2 * LENGTH pts + 1) ==>
      interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Pos r1)
             (CONS (CONS Pos (CONS Neg r2))
              (CONS (CONS Pos r3) rgns))))"),
    [
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"~(sgns = [])"),
      REWRITE_TAC [(← GSYM LENGTH_0)],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = LENGTH (APPEND sgns (CONS (CONS Pos r1) (CONS (CONS Unknown (CONS Neg r2)) (CONS (CONS Pos r3) rgns))))"),
      ASM_MESON_TAC [ALL2_LENGTH],
      STRIP_TAC,
      CASES_ON (← q r"pts = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      CLAIM (← q r"LENGTH sgns = 1"),
      POP_ASSUM (fun _x => ALL_TAC),
      REWRITE_ALL [LENGTH],
      ASM_REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [LENGTH_1],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [partition_line, TL, HD, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, APPEND, ALL2, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] pos_pos_neq_thm),
      REWRITE_ALL [real_ordered_list, NOT_CONS_NIL, HD, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt, ALL2, interpsigns, interpsign],
      ASM_MESON_TAC [],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [r5],
      REWRITE_TAC [LENGTH, APPEND, TL, HD, ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] pos_pos_neq_thm),
      REWRITE_ALL [interpsign, real_ordered_list, NOT_CONS_NIL, HD, ALL2],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt],
      ASM_MESON_TAC [],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [r4],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND, partition_line, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, HD, APPEND, ALL2],
      CLAIM (← q r"APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]"),
      MESON_TAC [APPEND, APPEND_CONS],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] pos_pos_neq_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list [y; z]"),
      ASM_MESON_TAC [ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [r3],
      REWRITE_TAC [APPEND, TL, HD, ALL2],
      REPEAT STRIP_TAC,
      CLAIM (← q r"!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j"),
      MESON_TAC [APPEND, APPEND_CONS],
      DISCH_THEN (fun x => ONCE_REWRITE_TAC [x] THEN ONCE_REWRITE_ASSUMS [x]),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [LENGTH_APPEND, BUTLAST_LENGTH, LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      REWRITE_ALL [TL, APPEND, HD],
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] pos_pos_neq_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list (CONS y (CONS z qts))"),
      ASM_MESON_TAC [ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [r2],
      ASM_MESON_TAC [r1]
    ])

  let INFERISIGN_NEG_NEG_POS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r3 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    let r5 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    prove_by_refinement (
      (← q r"!y z p pts qts eqs sgns rgns r1 r2 r3.
       interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Neg r1)
             (CONS (CONS Unknown (CONS Pos r2))
              (CONS (CONS Neg r3) rgns)))) ==>
       (LENGTH sgns = 2 * LENGTH pts + 1) ==>
      interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Neg r1)
             (CONS (CONS Neg (CONS Pos r2))
              (CONS (CONS Neg r3) rgns))))"),
    [
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"~(sgns = [])"),
      REWRITE_TAC [(← GSYM LENGTH_0)],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = LENGTH (APPEND sgns (CONS (CONS Neg r1) (CONS (CONS Unknown (CONS Pos r2)) (CONS (CONS Neg r3) rgns))))"),
      ASM_MESON_TAC [ALL2_LENGTH],
      STRIP_TAC,
      CASES_ON (← q r"pts = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      CLAIM (← q r"LENGTH sgns = 1"),
      POP_ASSUM (fun _x => ALL_TAC),
      REWRITE_ALL [LENGTH],
      ASM_REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [LENGTH_1],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [partition_line, TL, HD, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, APPEND, ALL2, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] neg_neg_neq_thm),
      REWRITE_ALL [real_ordered_list, NOT_CONS_NIL, HD, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt, ALL2, interpsigns, interpsign],
      ASM_MESON_TAC [],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [r5],
      REWRITE_TAC [LENGTH, APPEND, TL, HD, ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] neg_neg_neq_thm),
      REWRITE_ALL [interpsign, real_ordered_list, NOT_CONS_NIL, HD, ALL2],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt],
      ASM_MESON_TAC [],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [r4],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND, partition_line, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, HD, APPEND, ALL2],
      CLAIM (← q r"APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]"),
      MESON_TAC [APPEND, APPEND_CONS],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] neg_neg_neq_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list [y; z]"),
      ASM_MESON_TAC [ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [r3],
      REWRITE_TAC [APPEND, TL, HD, ALL2],
      REPEAT STRIP_TAC,
      CLAIM (← q r"!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j"),
      MESON_TAC [APPEND, APPEND_CONS],
      DISCH_THEN (fun x => ONCE_REWRITE_TAC [x] THEN ONCE_REWRITE_ASSUMS [x]),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [LENGTH_APPEND, BUTLAST_LENGTH, LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      REWRITE_ALL [TL, APPEND, HD],
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] neg_neg_neq_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list (CONS y (CONS z qts))"),
      ASM_MESON_TAC [ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [r2],
      ASM_MESON_TAC [r1]
    ])

  let INFERISIGN_NEG_NEG_NEG ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r3 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    let r5 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    prove_by_refinement (
      (← q r"!y z p pts qts eqs sgns rgns r1 r2 r3.
       interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Neg r1)
             (CONS (CONS Unknown (CONS Neg r2))
              (CONS (CONS Neg r3) rgns)))) ==>
       (LENGTH sgns = 2 * LENGTH pts + 1) ==>
      interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Neg r1)
             (CONS (CONS Neg (CONS Neg r2))
              (CONS (CONS Neg r3) rgns))))"),
    [
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"~(sgns = [])"),
      REWRITE_TAC [(← GSYM LENGTH_0)],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = LENGTH (APPEND sgns (CONS (CONS Neg r1) (CONS (CONS Unknown (CONS Neg r2)) (CONS (CONS Neg r3) rgns))))"),
      ASM_MESON_TAC [real_gt, ALL2_LENGTH],
      STRIP_TAC,
      CASES_ON (← q r"pts = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      CLAIM (← q r"LENGTH sgns = 1"),
      POP_ASSUM (fun _x => ALL_TAC),
      REWRITE_ALL [LENGTH],
      ASM_REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [LENGTH_1],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [partition_line, TL, HD, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, APPEND, ALL2, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] neg_neg_neq_thm),
      REWRITE_ALL [real_ordered_list, NOT_CONS_NIL, HD, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt, ALL2, interpsigns, interpsign],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r5],
      REWRITE_TAC [LENGTH, APPEND, TL, HD, ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] neg_neg_neq_thm),
      REWRITE_ALL [interpsign, real_ordered_list, NOT_CONS_NIL, HD, ALL2],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r4],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND, partition_line, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, HD, APPEND, ALL2],
      CLAIM (← q r"APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] neg_neg_neq_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list [y; z]"),
      ASM_MESON_TAC [real_gt, ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r3],
      REWRITE_TAC [APPEND, TL, HD, ALL2],
      REPEAT STRIP_TAC,
      CLAIM (← q r"!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (fun x => ONCE_REWRITE_TAC [x] THEN ONCE_REWRITE_ASSUMS [x]),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [LENGTH_APPEND, BUTLAST_LENGTH, LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      REWRITE_ALL [TL, APPEND, HD],
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] neg_neg_neq_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list (CONS y (CONS z qts))"),
      ASM_MESON_TAC [real_gt, ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r2],
      ASM_MESON_TAC [real_gt, r1]
    ])

  let ALL2_INTERPSIGN_SUBSET ← prove_by_refinement (
    (← q r"!P Q l1 l2. ALL2 (interpsign P) l1 l2 ==> Q SUBSET P ==>
   ALL2 (interpsign Q) l1 l2"),
  [
    STRIP_TAC THEN STRIP_TAC THEN REPEAT LIST_INDUCT_TAC THEN REWRITE_TAC [ALL2],
    ASM_MESON_TAC [INTERPSIGN_SUBSET]
  ])

  let HD_APPEND1 ← prove_by_refinement (
    (← q r"!h i l1 l2.
  HD (APPEND l1 (CONS h l2)) = HD (APPEND l1 (CONS h (CONS i l2)))"),
  [
    STRIP_TAC THEN STRIP_TAC,
    LIST_INDUCT_TAC,
    ASM_REWRITE_TAC [HD, APPEND],
    ASM_REWRITE_TAC [HD, APPEND]
  ])

  let ROL_APPEND_INSERT ← prove_by_refinement (
    (← q r"!h j l1 l2.
    real_ordered_list (APPEND l1 (CONS h (CONS i l2))) ==>
    h < j ==> j < i ==>
      real_ordered_list (APPEND l1 (CONS h (CONS j (CONS i l2))))"),
  [
    STRIP_TAC THEN STRIP_TAC,
    LIST_INDUCT_TAC,
    REWRITE_TAC [APPEND, real_ordered_list, HD, TL, NOT_CONS_NIL],
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
    REWRITE_TAC [APPEND, real_ordered_list],
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [],
    ASM_MESON_TAC [APPEND_EQ_NIL, NOT_CONS_NIL],
    ASM_MESON_TAC [],
    DISJ2_TAC,
    ASM_MESON_TAC [HD_APPEND1]
  ])

  -- @@RETURN BEGIN
  return { ALL2_LEM, INTERPMAT_TRIO_TL, LAST_APPEND, APPEND_APPEND, ALL2_LEM2,
           INTERPMAT_TRIO_INNER, INTERPMAT_SING, INFERISIGN_POS_POS_POS,
           INFERISIGN_POS_POS_NEG, INFERISIGN_NEG_NEG_POS, INFERISIGN_NEG_NEG_NEG,
           ALL2_INTERPSIGN_SUBSET, HD_APPEND1, ROL_APPEND_INSERT }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- work_thms.ml phrases from line 1899 to 2449; the theorems              -/
/- converted by gxwork/rq/ml2lean.py (disclosed; comments in the          -/
/- proofs are not carried over), the functions by hand.                   -/
/- ---------------------------------------------------------------------- -/

structure WorkThms03 where
  -- @@FIELDS
  INFERISIGN_POS_NEG_POS : thm
  INFERISIGN_POS_NEG_NEG : thm
  INFERISIGN_NEG_POS_NEG : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupWorkThms03 [HolBase] (D : WorkThmsDeps) (BWorkThms01 : WorkThms01) (BWorkThms02 : WorkThms02) :
    ExceptT String IO WorkThms03 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, CASES_ON, CLAIM, EXISTS_TAC, MESON_TAC, REAL_ARITH,
        prove_by_refinement, .. } := D
  let { ALL2, APPEND, HD, IMP_AND_THM, IN, LENGTH, LENGTH_0, LENGTH_1, LENGTH_APPEND,
        NOT_CONS_NIL, REAL_LT_TRANS, ROL_APPEND, SUBSET, TL, interpmat, interpsign,
        interpsigns, neg_pos_neq_thm, partition_line, pos_neg_neq_thm, real_gt,
        real_ordered_list, .. } := D.core1
  let { ALL2_APPEND, ALL2_APPEND_LENGTH, ALL2_LENGTH, APPEND_CONS, BUTLAST_LENGTH,
        PARTITION_LINE_APPEND, PARTITION_LINE_LENGTH, PARTITION_LINE_NOT_NIL, .. } := BWorkThms01
  let { ALL2_INTERPSIGN_SUBSET, ROL_APPEND_INSERT, .. } := BWorkThms02
  -- @@SCOPE END

  let INFERISIGN_POS_NEG_POS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"y < x ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r3 ← REAL_ARITH (← q r"y < x ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r5 ← REAL_ARITH (← q r"y < x ==> ~(x = y)")
    let r6 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r7 ← REAL_ARITH (← q r"y < x ==> ~(x = y)")
    let r8 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    prove_by_refinement (
      (← q r"!y z p pts qts eqs sgns rgns r1 r2 r3.
       interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Pos r1)
             (CONS (CONS Unknown (CONS Pos r2))
              (CONS (CONS Neg r3) rgns)))) ==>
       (LENGTH sgns = 2 * LENGTH pts + 1) ==>
      ?w. interpmat (APPEND pts (CONS y (CONS w (CONS z qts))))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Pos r1)
            (CONS (CONS Pos (CONS Pos r2))
            (CONS (CONS Zero (CONS Pos r2))
            (CONS (CONS Neg (CONS Pos r2))
            (CONS (CONS Neg r3) rgns))))))"),
    [
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      CLAIM (← q r"~(sgns = [])"),
      REWRITE_TAC [(← GSYM LENGTH_0)],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = LENGTH (APPEND sgns (CONS (CONS Pos r1) (CONS (CONS Unknown (CONS Pos r2)) (CONS (CONS Neg r3) rgns))))"),
      ASM_MESON_TAC [ALL2_LENGTH],
      STRIP_TAC,
      CASES_ON (← q r"pts = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      CLAIM (← q r"LENGTH sgns = 1"),
      POP_ASSUM (fun _x => ALL_TAC),
      REWRITE_ALL [LENGTH],
      ASM_REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [LENGTH_1],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [partition_line, TL, HD, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, APPEND, ALL2, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MP_TAC (← ISPECL [(← q r"y:real"), (← q r"z:real"), (← q r"p:real list")] pos_neg_neq_thm),
      REWRITE_ALL [real_ordered_list, HD, NOT_CONS_NIL],
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [interpsigns, ALL2, interpsign, real_gt],
      ASM_MESON_TAC [interpsigns, ALL2, interpsign, real_gt],
      ASM_MESON_TAC [interpsigns, ALL2, interpsign, real_gt, r8, r7],
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      EXISTS_TAC (← q r"X"),
      REWRITE_ALL [interpsign, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      FIRST_ASSUM MATCH_MP_TAC,
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [REAL_LT_TRANS],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [REAL_LT_TRANS],
      ASM_MESON_TAC [REAL_LT_TRANS],
      ASM_MESON_TAC [REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [REAL_LT_TRANS],
      ASM_MESON_TAC [REAL_LT_TRANS],
      ASM_MESON_TAC [REAL_LT_TRANS],
      ASM_MESON_TAC [REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [REAL_LT_TRANS],
      ASM_MESON_TAC [REAL_LT_TRANS],
      REWRITE_TAC [TL, APPEND, ALL2, real_gt, interpsigns, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MP_TAC (← ISPECL [(← q r"y:real"), (← q r"z:real"), (← q r"p:real list")] pos_neg_neq_thm),
      REWRITE_ALL [real_ordered_list, HD, NOT_CONS_NIL],
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [interpsigns, ALL2, interpsign, real_gt],
      ASM_MESON_TAC [interpsigns, ALL2, interpsign, real_gt],
      ASM_MESON_TAC [interpsigns, ALL2, interpsign, real_gt, r6, r5],
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      EXISTS_TAC (← q r"X"),
      REWRITE_ALL [interpsign, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      FIRST_ASSUM MATCH_MP_TAC,
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [REAL_LT_TRANS],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      ASM_MESON_TAC [REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [REAL_LT_TRANS],
      ASM_MESON_TAC [REAL_LT_TRANS],
      ASM_MESON_TAC [REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [REAL_LT_TRANS],
      ASM_MESON_TAC [REAL_LT_TRANS],
      ASM_MESON_TAC [REAL_LT_TRANS],
      ASM_MESON_TAC [REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [REAL_LT_TRANS],
      ASM_MESON_TAC [REAL_LT_TRANS],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND],
      CLAIM (← q r"!rts. APPEND (BUTLAST (partition_line pts))
         (CONS (\x. LAST pts < x /\ x < y) rts) =
       APPEND (APPEND (BUTLAST (partition_line pts))
          [\x. LAST pts < x /\ x < y]) rts"),
      MESON_TAC [APPEND, APPEND_CONS],
      DISCH_THEN (ONCE_REWRITE_TAC o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      CLAIM (← q r"real_ordered_list (CONS y (CONS z qts))"),
      ASM_MESON_TAC [real_gt, ROL_APPEND],
      REWRITE_TAC [real_ordered_list, NOT_CONS_NIL, HD],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_ALL [ALL2, partition_line, HD, TL, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, TL, HD, interpsigns, interpsign, ALL2],
      REPEAT STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"y:real"), (← q r"z:real"), (← q r"p:real list")] pos_neg_neq_thm),
      REPEAT STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, r4, r3],
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      EXISTS_TAC (← q r"X"),
      REWRITE_ALL [interpsign, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [interpsigns, interpsign],
      FIRST_ASSUM (MP_TAC o (MATCH_MP ROL_APPEND)),
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [ROL_APPEND_INSERT],
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns, interpsign],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      REWRITE_ALL [APPEND, TL, HD, interpsigns, interpsign, ALL2],
      REPEAT STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"y:real"), (← q r"z:real"), (← q r"p:real list")] pos_neg_neq_thm),
      REPEAT STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, r2, r1],
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      EXISTS_TAC (← q r"X"),
      REWRITE_ALL [interpsign, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [interpsigns, interpsign],
      FIRST_ASSUM (MP_TAC o (MATCH_MP ROL_APPEND)),
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [ROL_APPEND_INSERT],
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns, interpsign],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS]
    ])

  let INFERISIGN_POS_NEG_NEG ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"y < x ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r3 ← REAL_ARITH (← q r"y < x ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r5 ← REAL_ARITH (← q r"y < x ==> ~(x = y)")
    let r6 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r7 ← REAL_ARITH (← q r"y < x ==> ~(x = y)")
    let r8 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    prove_by_refinement (
      (← q r"!y z p pts qts eqs sgns rgns r1 r2 r3.
       interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Pos r1)
             (CONS (CONS Unknown (CONS Neg r2))
              (CONS (CONS Neg r3) rgns)))) ==>
       (LENGTH sgns = 2 * LENGTH pts + 1) ==>
      ?w. interpmat (APPEND pts (CONS y (CONS w (CONS z qts))))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Pos r1)
            (CONS (CONS Pos (CONS Neg r2))
            (CONS (CONS Zero (CONS Neg r2))
            (CONS (CONS Neg (CONS Neg r2))
            (CONS (CONS Neg r3) rgns))))))"),
    [
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      CLAIM (← q r"~(sgns = [])"),
      REWRITE_TAC [(← GSYM LENGTH_0)],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = LENGTH (APPEND sgns (CONS (CONS Pos r1) (CONS (CONS Unknown (CONS Neg r2)) (CONS (CONS Neg r3) rgns))))"),
      ASM_MESON_TAC [real_gt, ALL2_LENGTH],
      STRIP_TAC,
      CASES_ON (← q r"pts = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      CLAIM (← q r"LENGTH sgns = 1"),
      POP_ASSUM (fun _x => ALL_TAC),
      REWRITE_ALL [LENGTH],
      ASM_REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [LENGTH_1],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [partition_line, TL, HD, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, APPEND, ALL2, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MP_TAC (← ISPECL [(← q r"y:real"), (← q r"z:real"), (← q r"p:real list")] pos_neg_neq_thm),
      REWRITE_ALL [real_ordered_list, HD, NOT_CONS_NIL],
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, interpsigns, ALL2, interpsign, real_gt],
      ASM_MESON_TAC [real_gt, interpsigns, ALL2, interpsign, real_gt],
      ASM_MESON_TAC [real_gt, interpsigns, ALL2, interpsign, real_gt, r8, r7],
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      EXISTS_TAC (← q r"X"),
      REWRITE_ALL [interpsign, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      FIRST_ASSUM MATCH_MP_TAC,
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      REWRITE_TAC [TL, APPEND, ALL2, real_gt, interpsigns, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MP_TAC (← ISPECL [(← q r"y:real"), (← q r"z:real"), (← q r"p:real list")] pos_neg_neq_thm),
      REWRITE_ALL [real_ordered_list, HD, NOT_CONS_NIL],
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, interpsigns, ALL2, interpsign, real_gt],
      ASM_MESON_TAC [real_gt, interpsigns, ALL2, interpsign, real_gt],
      ASM_MESON_TAC [real_gt, interpsigns, ALL2, interpsign, real_gt, r6, r5],
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      EXISTS_TAC (← q r"X"),
      REWRITE_ALL [interpsign, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      FIRST_ASSUM MATCH_MP_TAC,
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND],
      CLAIM (← q r"!rts. APPEND (BUTLAST (partition_line pts))
         (CONS (\x. LAST pts < x /\ x < y) rts) =
       APPEND (APPEND (BUTLAST (partition_line pts))
          [\x. LAST pts < x /\ x < y]) rts"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (ONCE_REWRITE_TAC o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      CLAIM (← q r"real_ordered_list (CONS y (CONS z qts))"),
      ASM_MESON_TAC [real_gt, real_gt, ROL_APPEND],
      REWRITE_TAC [real_ordered_list, NOT_CONS_NIL, HD],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_ALL [ALL2, partition_line, HD, TL, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, TL, HD, interpsigns, interpsign, ALL2],
      REPEAT STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"y:real"), (← q r"z:real"), (← q r"p:real list")] pos_neg_neq_thm),
      REPEAT STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, real_gt, r4, r3],
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      EXISTS_TAC (← q r"X"),
      REWRITE_ALL [interpsign, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [interpsigns, interpsign],
      FIRST_ASSUM (MP_TAC o (MATCH_MP ROL_APPEND)),
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, ROL_APPEND_INSERT],
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns, interpsign],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      REWRITE_ALL [APPEND, TL, HD, interpsigns, interpsign, ALL2],
      REPEAT STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"y:real"), (← q r"z:real"), (← q r"p:real list")] pos_neg_neq_thm),
      REPEAT STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, real_gt, r2, r1],
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      EXISTS_TAC (← q r"X"),
      REWRITE_ALL [interpsign, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [interpsigns, interpsign],
      FIRST_ASSUM (MP_TAC o (MATCH_MP ROL_APPEND)),
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, ROL_APPEND_INSERT],
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns, interpsign],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS]
    ])

  let INFERISIGN_NEG_POS_NEG ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"y < x ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r3 ← REAL_ARITH (← q r"y < x ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r5 ← REAL_ARITH (← q r"y < x ==> ~(x = y)")
    let r6 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r7 ← REAL_ARITH (← q r"y < x ==> ~(x = y)")
    let r8 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    prove_by_refinement (
      (← q r"!y z p pts qts eqs sgns rgns r1 r2 r3.
       interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Neg r1)
             (CONS (CONS Unknown (CONS Neg r2))
              (CONS (CONS Pos r3) rgns)))) ==>
       (LENGTH sgns = 2 * LENGTH pts + 1) ==>
      ?w. interpmat (APPEND pts (CONS y (CONS w (CONS z qts))))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Neg r1)
            (CONS (CONS Neg (CONS Neg r2))
            (CONS (CONS Zero (CONS Neg r2))
            (CONS (CONS Pos (CONS Neg r2))
            (CONS (CONS Pos r3) rgns))))))"),
    [
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      CLAIM (← q r"~(sgns = [])"),
      REWRITE_TAC [(← GSYM LENGTH_0)],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) =
           LENGTH (APPEND sgns (CONS (CONS Neg r1)
            (CONS (CONS Unknown (CONS Neg r2))
            (CONS (CONS Pos r3) rgns))))"),
      ASM_MESON_TAC [real_gt, ALL2_LENGTH],
      STRIP_TAC,
      CASES_ON (← q r"pts = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      CLAIM (← q r"LENGTH sgns = 1"),
      POP_ASSUM (fun _x => ALL_TAC),
      REWRITE_ALL [LENGTH],
      ASM_REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [LENGTH_1],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [partition_line, TL, HD, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, APPEND, ALL2, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MP_TAC (← ISPECL [(← q r"y:real"), (← q r"z:real"), (← q r"p:real list")] neg_pos_neq_thm),
      REWRITE_ALL [real_ordered_list, HD, NOT_CONS_NIL],
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, interpsigns, ALL2, interpsign, real_gt],
      ASM_MESON_TAC [real_gt, interpsigns, ALL2, interpsign, real_gt],
      ASM_MESON_TAC [real_gt, interpsigns, ALL2, interpsign, real_gt, r8, r7],
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      EXISTS_TAC (← q r"X"),
      REWRITE_ALL [interpsign, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      FIRST_ASSUM MATCH_MP_TAC,
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      REWRITE_TAC [TL, APPEND, ALL2, real_gt, interpsigns, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MP_TAC (← ISPECL [(← q r"y:real"), (← q r"z:real"), (← q r"p:real list")] neg_pos_neq_thm),
      REWRITE_ALL [real_ordered_list, HD, NOT_CONS_NIL],
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, interpsigns, ALL2, interpsign, real_gt],
      ASM_MESON_TAC [real_gt, interpsigns, ALL2, interpsign, real_gt],
      ASM_MESON_TAC [real_gt, interpsigns, ALL2, interpsign, real_gt, r6, r5],
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      EXISTS_TAC (← q r"X"),
      REWRITE_ALL [interpsign, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      FIRST_ASSUM MATCH_MP_TAC,
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND],
      CLAIM (← q r"!rts. APPEND (BUTLAST (partition_line pts))
         (CONS (\x. LAST pts < x /\ x < y) rts) =
       APPEND (APPEND (BUTLAST (partition_line pts))
          [\x. LAST pts < x /\ x < y]) rts"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (ONCE_REWRITE_TAC o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      CLAIM (← q r"real_ordered_list (CONS y (CONS z qts))"),
      ASM_MESON_TAC [real_gt, real_gt, ROL_APPEND],
      REWRITE_TAC [real_ordered_list, NOT_CONS_NIL, HD],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_ALL [ALL2, partition_line, HD, TL, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, TL, HD, interpsigns, interpsign, ALL2],
      REPEAT STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"y:real"), (← q r"z:real"), (← q r"p:real list")] neg_pos_neq_thm),
      REPEAT STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, real_gt, r4, r3],
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      EXISTS_TAC (← q r"X"),
      REWRITE_ALL [interpsign, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [interpsigns, interpsign],
      FIRST_ASSUM (MP_TAC o (MATCH_MP ROL_APPEND)),
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, ROL_APPEND_INSERT],
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns, interpsign],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      REWRITE_ALL [APPEND, TL, HD, interpsigns, interpsign, ALL2],
      REPEAT STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"y:real"), (← q r"z:real"), (← q r"p:real list")] neg_pos_neq_thm),
      REPEAT STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, real_gt, r2, r1],
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      EXISTS_TAC (← q r"X"),
      REWRITE_ALL [interpsign, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [interpsigns, interpsign],
      FIRST_ASSUM (MP_TAC o (MATCH_MP ROL_APPEND)),
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, ROL_APPEND_INSERT],
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns, interpsign],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS]
    ])

  -- @@RETURN BEGIN
  return { INFERISIGN_POS_NEG_POS, INFERISIGN_POS_NEG_NEG, INFERISIGN_NEG_POS_NEG }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- work_thms.ml phrases from line 2726 to 3408; the theorems              -/
/- converted by gxwork/rq/ml2lean.py (disclosed; comments in the          -/
/- proofs are not carried over), the functions by hand.                   -/
/- ---------------------------------------------------------------------- -/

structure WorkThms04 where
  -- @@FIELDS
  INFERISIGN_NEG_POS_POS : thm
  INFERISIGN_ZERO_POS_POS : thm
  INFERISIGN_ZERO_POS_NEG : thm
  INFERISIGN_POS_ZERO_POS : thm
  INFERISIGN_POS_ZERO_NEG : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupWorkThms04 [HolBase] (D : WorkThmsDeps) (BWorkThms01 : WorkThms01) (BWorkThms02 : WorkThms02) :
    ExceptT String IO WorkThms04 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, CASES_ON, CLAIM, EXISTS_TAC, MESON_TAC, REAL_ARITH,
        prove_by_refinement, .. } := D
  let { ALL2, APPEND, HD, IMP_AND_THM, IN, LENGTH, LENGTH_0, LENGTH_1, LENGTH_APPEND,
        NOT_CONS_NIL, REAL_LT_TRANS, ROL_APPEND, SUBSET, TL, interpmat, interpsign,
        interpsigns, neg_pos_neq_thm, partition_line, pos_zero_pos_thm, real_gt,
        real_ordered_list, zero_pos_pos_thm, .. } := D.core1
  let { ALL2_APPEND, ALL2_APPEND_LENGTH, ALL2_LENGTH, APPEND_CONS, BUTLAST_LENGTH,
        PARTITION_LINE_APPEND, PARTITION_LINE_LENGTH, PARTITION_LINE_NOT_NIL, .. } := BWorkThms01
  let { ALL2_INTERPSIGN_SUBSET, ROL_APPEND_INSERT, .. } := BWorkThms02
  -- @@SCOPE END

  let INFERISIGN_NEG_POS_POS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"y < x ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r3 ← REAL_ARITH (← q r"y < x ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r5 ← REAL_ARITH (← q r"y < x ==> ~(x = y)")
    let r6 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r7 ← REAL_ARITH (← q r"y < x ==> ~(x = y)")
    let r8 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    prove_by_refinement (
      (← q r"!y z p pts qts eqs sgns rgns r1 r2 r3.
       interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Neg r1)
             (CONS (CONS Unknown (CONS Pos r2))
              (CONS (CONS Pos r3) rgns)))) ==>
       (LENGTH sgns = 2 * LENGTH pts + 1) ==>
      ?w. interpmat (APPEND pts (CONS y (CONS w (CONS z qts))))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Neg r1)
            (CONS (CONS Neg (CONS Pos r2))
            (CONS (CONS Zero (CONS Pos r2))
            (CONS (CONS Pos (CONS Pos r2))
            (CONS (CONS Pos r3) rgns))))))"),
    [
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      CLAIM (← q r"~(sgns = [])"),
      REWRITE_TAC [(← GSYM LENGTH_0)],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) =
           LENGTH (APPEND sgns (CONS (CONS Neg r1)
            (CONS (CONS Unknown (CONS Pos r2))
            (CONS (CONS Pos r3) rgns))))"),
      ASM_MESON_TAC [real_gt, ALL2_LENGTH],
      STRIP_TAC,
      CASES_ON (← q r"pts = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      CLAIM (← q r"LENGTH sgns = 1"),
      POP_ASSUM (fun _x => ALL_TAC),
      REWRITE_ALL [LENGTH],
      ASM_REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [LENGTH_1],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [partition_line, TL, HD, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, APPEND, ALL2, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MP_TAC (← ISPECL [(← q r"y:real"), (← q r"z:real"), (← q r"p:real list")] neg_pos_neq_thm),
      REWRITE_ALL [real_ordered_list, HD, NOT_CONS_NIL],
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, interpsigns, ALL2, interpsign, real_gt],
      ASM_MESON_TAC [real_gt, interpsigns, ALL2, interpsign, real_gt],
      ASM_MESON_TAC [real_gt, interpsigns, ALL2, interpsign, real_gt, r8, r7],
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      EXISTS_TAC (← q r"X"),
      REWRITE_ALL [interpsign, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      FIRST_ASSUM MATCH_MP_TAC,
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      REWRITE_TAC [TL, APPEND, ALL2, real_gt, interpsigns, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MP_TAC (← ISPECL [(← q r"y:real"), (← q r"z:real"), (← q r"p:real list")] neg_pos_neq_thm),
      REWRITE_ALL [real_ordered_list, HD, NOT_CONS_NIL],
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, interpsigns, ALL2, interpsign, real_gt],
      ASM_MESON_TAC [real_gt, interpsigns, ALL2, interpsign, real_gt],
      ASM_MESON_TAC [real_gt, interpsigns, ALL2, interpsign, real_gt, r6, r5],
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      EXISTS_TAC (← q r"X"),
      REWRITE_ALL [interpsign, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      FIRST_ASSUM MATCH_MP_TAC,
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [SUBSET, IN],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, REAL_LT_TRANS],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND],
      CLAIM (← q r"!rts. APPEND (BUTLAST (partition_line pts))
         (CONS (\x. LAST pts < x /\ x < y) rts) =
       APPEND (APPEND (BUTLAST (partition_line pts))
          [\x. LAST pts < x /\ x < y]) rts"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (ONCE_REWRITE_TAC o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      CLAIM (← q r"real_ordered_list (CONS y (CONS z qts))"),
      ASM_MESON_TAC [real_gt, real_gt, ROL_APPEND],
      REWRITE_TAC [real_ordered_list, NOT_CONS_NIL, HD],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_ALL [ALL2, partition_line, HD, TL, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, TL, HD, interpsigns, interpsign, ALL2],
      REPEAT STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"y:real"), (← q r"z:real"), (← q r"p:real list")] neg_pos_neq_thm),
      REPEAT STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, real_gt, r4, r3],
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      EXISTS_TAC (← q r"X"),
      REWRITE_ALL [interpsign, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [interpsigns, interpsign],
      FIRST_ASSUM (MP_TAC o (MATCH_MP ROL_APPEND)),
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, ROL_APPEND_INSERT],
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns, interpsign],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      REWRITE_ALL [APPEND, TL, HD, interpsigns, interpsign, ALL2],
      REPEAT STRIP_TAC,
      MP_TAC (← ISPECL [(← q r"y:real"), (← q r"z:real"), (← q r"p:real list")] neg_pos_neq_thm),
      REPEAT STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, real_gt, r2, r1],
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      EXISTS_TAC (← q r"X"),
      REWRITE_ALL [interpsign, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [interpsigns, interpsign],
      FIRST_ASSUM (MP_TAC o (MATCH_MP ROL_APPEND)),
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [real_gt, ROL_APPEND_INSERT],
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns, interpsign],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
      EXISTS_TAC (← q r"\x. y < x /\ x < z"),
      REWRITE_TAC [SUBSET, IN],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS],
      ASM_MESON_TAC [real_gt, real_gt, REAL_LT_TRANS]
    ])

  let INFERISIGN_ZERO_POS_POS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r3 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    let r5 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    prove_by_refinement (
      (← q r"!y z p pts qts eqs sgns rgns r1 r2 r3.
       interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Zero r1)
             (CONS (CONS Unknown (CONS Pos r2))
              (CONS (CONS Pos r3) rgns)))) ==>
       (LENGTH sgns = 2 * LENGTH pts + 1) ==>
      interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Zero r1)
             (CONS (CONS Pos (CONS Pos r2))
              (CONS (CONS Pos r3) rgns))))"),
    [
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"~(sgns = [])"),
      REWRITE_TAC [(← GSYM LENGTH_0)],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = LENGTH (APPEND sgns (CONS (CONS Zero r1) (CONS (CONS Unknown (CONS Pos r2)) (CONS (CONS Pos r3) rgns))))"),
      ASM_MESON_TAC [real_gt, ALL2_LENGTH],
      STRIP_TAC,
      CASES_ON (← q r"pts = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      CLAIM (← q r"LENGTH sgns = 1"),
      POP_ASSUM (fun _x => ALL_TAC),
      REWRITE_ALL [LENGTH],
      ASM_REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [LENGTH_1],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [partition_line, TL, HD, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, APPEND, ALL2, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] zero_pos_pos_thm),
      REWRITE_ALL [real_ordered_list, NOT_CONS_NIL, HD, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt, ALL2, interpsigns, interpsign],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r5],
      REWRITE_TAC [LENGTH, APPEND, TL, HD, ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] zero_pos_pos_thm),
      REWRITE_ALL [interpsign, real_ordered_list, NOT_CONS_NIL, HD, ALL2],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r4],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND, partition_line, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, HD, APPEND, ALL2],
      CLAIM (← q r"APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] zero_pos_pos_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list [y; z]"),
      ASM_MESON_TAC [real_gt, ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r3],
      REWRITE_TAC [APPEND, TL, HD, ALL2],
      REPEAT STRIP_TAC,
      CLAIM (← q r"!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (fun x => ONCE_REWRITE_TAC [x] THEN ONCE_REWRITE_ASSUMS [x]),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [LENGTH_APPEND, BUTLAST_LENGTH, LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      REWRITE_ALL [TL, APPEND, HD],
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] zero_pos_pos_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list (CONS y (CONS z qts))"),
      ASM_MESON_TAC [real_gt, ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r2],
      ASM_MESON_TAC [real_gt, r1]
    ])

  let INFERISIGN_ZERO_POS_NEG ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r3 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    let r5 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    prove_by_refinement (
      (← q r"!y z p pts qts eqs sgns rgns r1 r2 r3.
       interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Zero r1)
             (CONS (CONS Unknown (CONS Neg r2))
              (CONS (CONS Pos r3) rgns)))) ==>
       (LENGTH sgns = 2 * LENGTH pts + 1) ==>
      interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Zero r1)
             (CONS (CONS Pos (CONS Neg r2))
              (CONS (CONS Pos r3) rgns))))"),
    [
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"~(sgns = [])"),
      REWRITE_TAC [(← GSYM LENGTH_0)],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = LENGTH (APPEND sgns (CONS (CONS Zero r1) (CONS (CONS Unknown (CONS Neg r2)) (CONS (CONS Pos r3) rgns))))"),
      ASM_MESON_TAC [real_gt, ALL2_LENGTH],
      STRIP_TAC,
      CASES_ON (← q r"pts = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      CLAIM (← q r"LENGTH sgns = 1"),
      POP_ASSUM (fun _x => ALL_TAC),
      REWRITE_ALL [LENGTH],
      ASM_REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [LENGTH_1],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [partition_line, TL, HD, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, APPEND, ALL2, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] zero_pos_pos_thm),
      REWRITE_ALL [real_ordered_list, NOT_CONS_NIL, HD, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt, ALL2, interpsigns, interpsign],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r5],
      REWRITE_TAC [LENGTH, APPEND, TL, HD, ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] zero_pos_pos_thm),
      REWRITE_ALL [interpsign, real_ordered_list, NOT_CONS_NIL, HD, ALL2],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r4],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND, partition_line, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, HD, APPEND, ALL2],
      CLAIM (← q r"APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] zero_pos_pos_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list [y; z]"),
      ASM_MESON_TAC [real_gt, ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r3],
      REWRITE_TAC [APPEND, TL, HD, ALL2],
      REPEAT STRIP_TAC,
      CLAIM (← q r"!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (fun x => ONCE_REWRITE_TAC [x] THEN ONCE_REWRITE_ASSUMS [x]),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [LENGTH_APPEND, BUTLAST_LENGTH, LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      REWRITE_ALL [TL, APPEND, HD],
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] zero_pos_pos_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list (CONS y (CONS z qts))"),
      ASM_MESON_TAC [real_gt, ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r2],
      ASM_MESON_TAC [real_gt, r1]
    ])

  let INFERISIGN_POS_ZERO_POS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r3 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    let r5 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    prove_by_refinement (
      (← q r"!y z p pts qts eqs sgns rgns r1 r2 r3.
       interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Pos r1)
             (CONS (CONS Unknown (CONS Pos r2))
              (CONS (CONS Zero r3) rgns)))) ==>
       (LENGTH sgns = 2 * LENGTH pts + 1) ==>
      interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Pos r1)
             (CONS (CONS Pos (CONS Pos r2))
              (CONS (CONS Zero r3) rgns))))"),
    [
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"~(sgns = [])"),
      REWRITE_TAC [(← GSYM LENGTH_0)],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = LENGTH (APPEND sgns (CONS (CONS Pos r1) (CONS (CONS Unknown (CONS Pos r2)) (CONS (CONS Zero r3) rgns))))"),
      ASM_MESON_TAC [real_gt, ALL2_LENGTH],
      STRIP_TAC,
      CASES_ON (← q r"pts = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      CLAIM (← q r"LENGTH sgns = 1"),
      POP_ASSUM (fun _x => ALL_TAC),
      REWRITE_ALL [LENGTH],
      ASM_REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [LENGTH_1],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [partition_line, TL, HD, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, APPEND, ALL2, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] pos_zero_pos_thm),
      REWRITE_ALL [real_ordered_list, NOT_CONS_NIL, HD, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt, ALL2, interpsigns, interpsign],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r5],
      REWRITE_TAC [LENGTH, APPEND, TL, HD, ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] pos_zero_pos_thm),
      REWRITE_ALL [interpsign, real_ordered_list, NOT_CONS_NIL, HD, ALL2],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r4],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND, partition_line, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, HD, APPEND, ALL2],
      CLAIM (← q r"APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] pos_zero_pos_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list [y; z]"),
      ASM_MESON_TAC [real_gt, ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r3],
      REWRITE_TAC [APPEND, TL, HD, ALL2],
      REPEAT STRIP_TAC,
      CLAIM (← q r"!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (fun x => ONCE_REWRITE_TAC [x] THEN ONCE_REWRITE_ASSUMS [x]),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [LENGTH_APPEND, BUTLAST_LENGTH, LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      REWRITE_ALL [TL, APPEND, HD],
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] pos_zero_pos_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list (CONS y (CONS z qts))"),
      ASM_MESON_TAC [real_gt, ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r2],
      ASM_MESON_TAC [real_gt, r1]
    ])

  let INFERISIGN_POS_ZERO_NEG ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r3 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    let r5 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    prove_by_refinement (
      (← q r"!y z p pts qts eqs sgns rgns r1 r2 r3.
       interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Pos r1)
             (CONS (CONS Unknown (CONS Neg r2))
              (CONS (CONS Zero r3) rgns)))) ==>
       (LENGTH sgns = 2 * LENGTH pts + 1) ==>
      interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Pos r1)
             (CONS (CONS Pos (CONS Neg r2))
              (CONS (CONS Zero r3) rgns))))"),
    [
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"~(sgns = [])"),
      REWRITE_TAC [(← GSYM LENGTH_0)],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = LENGTH (APPEND sgns (CONS (CONS Pos r1) (CONS (CONS Unknown (CONS Neg r2)) (CONS (CONS Zero r3) rgns))))"),
      ASM_MESON_TAC [real_gt, ALL2_LENGTH],
      STRIP_TAC,
      CASES_ON (← q r"pts = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      CLAIM (← q r"LENGTH sgns = 1"),
      POP_ASSUM (fun _x => ALL_TAC),
      REWRITE_ALL [LENGTH],
      ASM_REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [LENGTH_1],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [partition_line, TL, HD, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, APPEND, ALL2, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] pos_zero_pos_thm),
      REWRITE_ALL [real_ordered_list, NOT_CONS_NIL, HD, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt, ALL2, interpsigns, interpsign],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r5],
      REWRITE_TAC [LENGTH, APPEND, TL, HD, ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] pos_zero_pos_thm),
      REWRITE_ALL [interpsign, real_ordered_list, NOT_CONS_NIL, HD, ALL2],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r4],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND, partition_line, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, HD, APPEND, ALL2],
      CLAIM (← q r"APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] pos_zero_pos_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list [y; z]"),
      ASM_MESON_TAC [real_gt, ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r3],
      REWRITE_TAC [APPEND, TL, HD, ALL2],
      REPEAT STRIP_TAC,
      CLAIM (← q r"!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (fun x => ONCE_REWRITE_TAC [x] THEN ONCE_REWRITE_ASSUMS [x]),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [LENGTH_APPEND, BUTLAST_LENGTH, LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      REWRITE_ALL [TL, APPEND, HD],
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] pos_zero_pos_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list (CONS y (CONS z qts))"),
      ASM_MESON_TAC [real_gt, ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r2],
      ASM_MESON_TAC [real_gt, r1]
    ])

  -- @@RETURN BEGIN
  return { INFERISIGN_NEG_POS_POS, INFERISIGN_ZERO_POS_POS, INFERISIGN_ZERO_POS_NEG,
           INFERISIGN_POS_ZERO_POS, INFERISIGN_POS_ZERO_NEG }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- work_thms.ml phrases from line 3542 to 4383; the theorems              -/
/- converted by gxwork/rq/ml2lean.py (disclosed; comments in the          -/
/- proofs are not carried over), the functions by hand.                   -/
/- ---------------------------------------------------------------------- -/

structure WorkThms05 where
  -- @@FIELDS
  INFERISIGN_ZERO_NEG_POS : thm
  INFERISIGN_ZERO_NEG_NEG : thm
  INFERISIGN_NEG_ZERO_NEG : thm
  INFERISIGN_NEG_ZERO_POS : thm
  INFERISIGN_ZERO_ZERO_POS : thm
  INFERISIGN_ZERO_ZERO_NEG : thm
  BUTLAST_ID : thm
  BUTLAST_NIL : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupWorkThms05 [HolBase] (D : WorkThmsDeps) (BWorkThms01 : WorkThms01) :
    ExceptT String IO WorkThms05 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, CASES_ON, CLAIM, EXISTS_TAC, LIST_INDUCT_TAC,
        MESON_TAC, REAL_ARITH, prove_by_refinement, .. } := D
  let { ALL2, APPEND, BUTLAST, CONS_11, HD, IMP_AND_THM, LAST, LENGTH, LENGTH_0,
        LENGTH_1, LENGTH_APPEND, NOT_CONS_NIL, ROL_APPEND, TL, eq_eq_false_thm,
        interpmat, interpsign, interpsigns, neg_zero_neg_thm, partition_line, real_gt,
        real_ordered_list, zero_neg_neg_thm, .. } := D.core1
  let { ALL2_APPEND, ALL2_APPEND_LENGTH, ALL2_LENGTH, APPEND_CONS, BUTLAST_LENGTH,
        PARTITION_LINE_APPEND, PARTITION_LINE_LENGTH, PARTITION_LINE_NOT_NIL, .. } := BWorkThms01
  -- @@SCOPE END

  let INFERISIGN_ZERO_NEG_POS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r3 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    let r5 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    prove_by_refinement (
      (← q r"!y z p pts qts eqs sgns rgns r1 r2 r3.
       interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Zero r1)
             (CONS (CONS Unknown (CONS Pos r2))
              (CONS (CONS Neg r3) rgns)))) ==>
       (LENGTH sgns = 2 * LENGTH pts + 1) ==>
      interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Zero r1)
             (CONS (CONS Neg (CONS Pos r2))
              (CONS (CONS Neg r3) rgns))))"),
    [
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"~(sgns = [])"),
      REWRITE_TAC [(← GSYM LENGTH_0)],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) =
     LENGTH (APPEND sgns (CONS (CONS Zero r1)
     (CONS (CONS Unknown (CONS Pos r2)) (CONS (CONS Neg r3) rgns))))"),
      ASM_MESON_TAC [real_gt, ALL2_LENGTH],
      STRIP_TAC,
      CASES_ON (← q r"pts = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      CLAIM (← q r"LENGTH sgns = 1"),
      POP_ASSUM (fun _x => ALL_TAC),
      REWRITE_ALL [LENGTH],
      ASM_REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [LENGTH_1],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [partition_line, TL, HD, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, APPEND, ALL2, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] zero_neg_neg_thm),
      REWRITE_ALL [real_ordered_list, NOT_CONS_NIL, HD, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt, ALL2, interpsigns, interpsign],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r5],
      REWRITE_TAC [LENGTH, APPEND, TL, HD, ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] zero_neg_neg_thm),
      REWRITE_ALL [interpsign, real_ordered_list, NOT_CONS_NIL, HD, ALL2],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r4],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND, partition_line, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, HD, APPEND, ALL2],
      CLAIM (← q r"APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] zero_neg_neg_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list [y; z]"),
      ASM_MESON_TAC [real_gt, ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r3],
      REWRITE_TAC [APPEND, TL, HD, ALL2],
      REPEAT STRIP_TAC,
      CLAIM (← q r"!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (fun x => ONCE_REWRITE_TAC [x] THEN ONCE_REWRITE_ASSUMS [x]),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [LENGTH_APPEND, BUTLAST_LENGTH, LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      REWRITE_ALL [TL, APPEND, HD],
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] zero_neg_neg_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list (CONS y (CONS z qts))"),
      ASM_MESON_TAC [real_gt, ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r2],
      ASM_MESON_TAC [real_gt, r1]
    ])

  let INFERISIGN_ZERO_NEG_NEG ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r3 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    let r5 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    prove_by_refinement (
      (← q r"!y z p pts qts eqs sgns rgns r1 r2 r3.
       interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Zero r1)
             (CONS (CONS Unknown (CONS Neg r2))
              (CONS (CONS Neg r3) rgns)))) ==>
       (LENGTH sgns = 2 * LENGTH pts + 1) ==>
      interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Zero r1)
             (CONS (CONS Neg (CONS Neg r2))
              (CONS (CONS Neg r3) rgns))))"),
    [
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"~(sgns = [])"),
      REWRITE_TAC [(← GSYM LENGTH_0)],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) =
     LENGTH (APPEND sgns (CONS (CONS Zero r1)
     (CONS (CONS Unknown (CONS Neg r2)) (CONS (CONS Neg r3) rgns))))"),
      ASM_MESON_TAC [real_gt, ALL2_LENGTH],
      STRIP_TAC,
      CASES_ON (← q r"pts = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      CLAIM (← q r"LENGTH sgns = 1"),
      POP_ASSUM (fun _x => ALL_TAC),
      REWRITE_ALL [LENGTH],
      ASM_REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [LENGTH_1],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [partition_line, TL, HD, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, APPEND, ALL2, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] zero_neg_neg_thm),
      REWRITE_ALL [real_ordered_list, NOT_CONS_NIL, HD, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt, ALL2, interpsigns, interpsign],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r5],
      REWRITE_TAC [LENGTH, APPEND, TL, HD, ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] zero_neg_neg_thm),
      REWRITE_ALL [interpsign, real_ordered_list, NOT_CONS_NIL, HD, ALL2],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r4],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND, partition_line, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, HD, APPEND, ALL2],
      CLAIM (← q r"APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] zero_neg_neg_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list [y; z]"),
      ASM_MESON_TAC [real_gt, ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r3],
      REWRITE_TAC [APPEND, TL, HD, ALL2],
      REPEAT STRIP_TAC,
      CLAIM (← q r"!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (fun x => ONCE_REWRITE_TAC [x] THEN ONCE_REWRITE_ASSUMS [x]),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [LENGTH_APPEND, BUTLAST_LENGTH, LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      REWRITE_ALL [TL, APPEND, HD],
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] zero_neg_neg_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list (CONS y (CONS z qts))"),
      ASM_MESON_TAC [real_gt, ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r2],
      ASM_MESON_TAC [real_gt, r1]
    ])

  let INFERISIGN_NEG_ZERO_NEG ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r3 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    let r5 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    prove_by_refinement (
      (← q r"!y z p pts qts eqs sgns rgns r1 r2 r3.
       interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Neg r1)
             (CONS (CONS Unknown (CONS Neg r2))
              (CONS (CONS Zero r3) rgns)))) ==>
       (LENGTH sgns = 2 * LENGTH pts + 1) ==>
      interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Neg r1)
             (CONS (CONS Neg (CONS Neg r2))
              (CONS (CONS Zero r3) rgns))))"),
    [
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"~(sgns = [])"),
      REWRITE_TAC [(← GSYM LENGTH_0)],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) =
     LENGTH (APPEND sgns (CONS (CONS Neg r1)
     (CONS (CONS Unknown (CONS Neg r2)) (CONS (CONS Zero r3) rgns))))"),
      ASM_MESON_TAC [real_gt, ALL2_LENGTH],
      STRIP_TAC,
      CASES_ON (← q r"pts = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      CLAIM (← q r"LENGTH sgns = 1"),
      POP_ASSUM (fun _x => ALL_TAC),
      REWRITE_ALL [LENGTH],
      ASM_REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [LENGTH_1],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [partition_line, TL, HD, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, APPEND, ALL2, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] neg_zero_neg_thm),
      REWRITE_ALL [real_ordered_list, NOT_CONS_NIL, HD, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt, ALL2, interpsigns, interpsign],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r5],
      REWRITE_TAC [LENGTH, APPEND, TL, HD, ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] neg_zero_neg_thm),
      REWRITE_ALL [interpsign, real_ordered_list, NOT_CONS_NIL, HD, ALL2],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r4],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND, partition_line, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, HD, APPEND, ALL2],
      CLAIM (← q r"APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] neg_zero_neg_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list [y; z]"),
      ASM_MESON_TAC [real_gt, ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r3],
      REWRITE_TAC [APPEND, TL, HD, ALL2],
      REPEAT STRIP_TAC,
      CLAIM (← q r"!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (fun x => ONCE_REWRITE_TAC [x] THEN ONCE_REWRITE_ASSUMS [x]),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [LENGTH_APPEND, BUTLAST_LENGTH, LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      REWRITE_ALL [TL, APPEND, HD],
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] neg_zero_neg_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list (CONS y (CONS z qts))"),
      ASM_MESON_TAC [real_gt, ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r2],
      ASM_MESON_TAC [real_gt, r1]
    ])

  let INFERISIGN_NEG_ZERO_POS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r3 ← REAL_ARITH (← q r"x < y ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    let r5 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    prove_by_refinement (
      (← q r"!y z p pts qts eqs sgns rgns r1 r2 r3.
       interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Neg r1)
             (CONS (CONS Unknown (CONS Pos r2))
              (CONS (CONS Zero r3) rgns)))) ==>
       (LENGTH sgns = 2 * LENGTH pts + 1) ==>
      interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Neg r1)
             (CONS (CONS Neg (CONS Pos r2))
              (CONS (CONS Zero r3) rgns))))"),
    [
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"~(sgns = [])"),
      REWRITE_TAC [(← GSYM LENGTH_0)],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) =
     LENGTH (APPEND sgns (CONS (CONS Neg r1)
     (CONS (CONS Unknown (CONS Pos r2)) (CONS (CONS Zero r3) rgns))))"),
      ASM_MESON_TAC [real_gt, ALL2_LENGTH],
      STRIP_TAC,
      CASES_ON (← q r"pts = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      CLAIM (← q r"LENGTH sgns = 1"),
      POP_ASSUM (fun _x => ALL_TAC),
      REWRITE_ALL [LENGTH],
      ASM_REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [LENGTH_1],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [partition_line, TL, HD, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, APPEND, ALL2, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] neg_zero_neg_thm),
      REWRITE_ALL [real_ordered_list, NOT_CONS_NIL, HD, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt, ALL2, interpsigns, interpsign],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r5],
      REWRITE_TAC [LENGTH, APPEND, TL, HD, ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] neg_zero_neg_thm),
      REWRITE_ALL [interpsign, real_ordered_list, NOT_CONS_NIL, HD, ALL2],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [real_gt],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r4],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND, partition_line, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, HD, APPEND, ALL2],
      CLAIM (← q r"APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] neg_zero_neg_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list [y; z]"),
      ASM_MESON_TAC [real_gt, ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r3],
      REWRITE_TAC [APPEND, TL, HD, ALL2],
      REPEAT STRIP_TAC,
      CLAIM (← q r"!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (fun x => ONCE_REWRITE_TAC [x] THEN ONCE_REWRITE_ASSUMS [x]),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [LENGTH_APPEND, BUTLAST_LENGTH, LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      REWRITE_ALL [TL, APPEND, HD],
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← REWRITE_RULE [real_gt, IMP_AND_THM] neg_zero_neg_thm),
      REWRITE_ALL [interpsign, real_ordered_list, ROL_APPEND, NOT_CONS_NIL, HD, ALL2, real_ordered_list, APPEND],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list (CONS y (CONS z qts))"),
      ASM_MESON_TAC [real_gt, ROL_APPEND],
      REWRITE_ALL [NOT_CONS_NIL, real_gt, real_ordered_list, HD],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r2],
      ASM_MESON_TAC [real_gt, r1]
    ])

  let INFERISIGN_ZERO_ZERO_POS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    let r3 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    prove_by_refinement (
      (← q r"!y z p pts qts eqs sgns rgns r1 r2 r3.
       interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Zero r1)
             (CONS (CONS Unknown (CONS Pos r2))
              (CONS (CONS Zero r3) rgns)))) ==>
       (LENGTH sgns = 2 * LENGTH pts + 1) ==> F"),
    [
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"~((sgns:(sign list) list) = [])"),
      REWRITE_TAC [(← GSYM LENGTH_0)],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) =
     LENGTH (APPEND sgns (CONS (CONS Zero r1)
     (CONS (CONS Unknown (CONS Pos r2)) (CONS (CONS Zero r3) rgns))))"),
      ASM_MESON_TAC [real_gt, ALL2_LENGTH],
      STRIP_TAC,
      CASES_ON (← q r"pts = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      CLAIM (← q r"LENGTH (sgns:(sign list) list) = 1"),
      POP_ASSUM (fun _x => ALL_TAC),
      REWRITE_ALL [LENGTH],
      ASM_REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [LENGTH_1],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [partition_line, TL, HD, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, APPEND, ALL2, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MATCH_MP_TAC (← PURE_REWRITE_RULE [real_gt, IMP_AND_THM] eq_eq_false_thm),
      EXISTS_TAC (← q r"y"),
      EXISTS_TAC (← q r"z"),
      EXISTS_TAC (← q r"p"),
      REWRITE_ALL [real_ordered_list, NOT_CONS_NIL, HD, interpsign],
      REWRITE_ALL [real_gt, ALL2, interpsigns, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r4],
      REWRITE_TAC [LENGTH, APPEND, TL, HD, ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign, real_gt],
      MATCH_MP_TAC (← PURE_REWRITE_RULE [real_gt, IMP_AND_THM] eq_eq_false_thm),
      EXISTS_TAC (← q r"y"),
      EXISTS_TAC (← q r"z"),
      EXISTS_TAC (← q r"p"),
      REWRITE_ALL [real_ordered_list, NOT_CONS_NIL, HD, interpsign],
      REWRITE_ALL [real_gt, ALL2, interpsigns, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r3],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND, partition_line, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, HD, APPEND, ALL2],
      CLAIM (← q r"APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH (sgns:(sign list) list)"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC (← PURE_REWRITE_RULE [real_gt, IMP_AND_THM] eq_eq_false_thm),
      EXISTS_TAC (← q r"y"),
      EXISTS_TAC (← q r"z"),
      EXISTS_TAC (← q r"p"),
      REWRITE_ALL [real_ordered_list, NOT_CONS_NIL, HD, interpsign],
      REWRITE_ALL [real_gt, ALL2, interpsigns, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list [y; z]"),
      ASM_MESON_TAC [ROL_APPEND],
      REWRITE_TAC [HD, NOT_CONS_NIL, real_ordered_list],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r2],
      REWRITE_TAC [APPEND, TL, HD, ALL2],
      REPEAT STRIP_TAC,
      CLAIM (← q r"!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j"),
      MESON_TAC [APPEND, APPEND_CONS],
      DISCH_THEN (fun x => ONCE_REWRITE_TAC [x] THEN ONCE_REWRITE_ASSUMS [x]),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH (sgns:(sign list)list)"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [LENGTH_APPEND, BUTLAST_LENGTH, LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      REWRITE_ALL [TL, APPEND, HD],
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← PURE_REWRITE_RULE [real_gt, IMP_AND_THM] eq_eq_false_thm),
      EXISTS_TAC (← q r"y"),
      EXISTS_TAC (← q r"z"),
      EXISTS_TAC (← q r"p"),
      REWRITE_ALL [real_ordered_list, NOT_CONS_NIL, HD, interpsign],
      REWRITE_ALL [real_gt, ALL2, interpsigns, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list (CONS y(CONS  z qts))"),
      ASM_MESON_TAC [ROL_APPEND],
      REWRITE_TAC [HD, NOT_CONS_NIL, real_ordered_list],
      STRIP_TAC,
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r1]
    ])

  let INFERISIGN_ZERO_ZERO_NEG ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    let r3 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"x > y ==> ~(x = y)")
    prove_by_refinement (
      (← q r"!y z p pts qts eqs sgns rgns r1 r2 r3.
       interpmat (APPEND pts (CONS y (CONS z qts)))
        (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs))
          (APPEND sgns
            (CONS (CONS Zero r1)
             (CONS (CONS Unknown (CONS Neg r2))
              (CONS (CONS Zero r3) rgns)))) ==>
       (LENGTH sgns = 2 * LENGTH pts + 1) ==> F"),
    [
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"~((sgns:(sign list) list) = [])"),
      REWRITE_TAC [(← GSYM LENGTH_0)],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) =
     LENGTH (APPEND sgns (CONS (CONS Zero r1)
     (CONS (CONS Unknown (CONS Neg r2)) (CONS (CONS Zero r3) rgns))))"),
      ASM_MESON_TAC [real_gt, ALL2_LENGTH],
      STRIP_TAC,
      CASES_ON (← q r"pts = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      CLAIM (← q r"LENGTH (sgns:(sign list) list) = 1"),
      POP_ASSUM (fun _x => ALL_TAC),
      REWRITE_ALL [LENGTH],
      ASM_REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [LENGTH_1],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND],
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [partition_line, TL, HD, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, APPEND, ALL2, real_gt],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, ALL2],
      ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign],
      REWRITE_ALL [real_gt],
      MATCH_MP_TAC (← PURE_REWRITE_RULE [real_gt, IMP_AND_THM] eq_eq_false_thm),
      EXISTS_TAC (← q r"y"),
      EXISTS_TAC (← q r"z"),
      EXISTS_TAC (← q r"p"),
      REWRITE_ALL [real_ordered_list, NOT_CONS_NIL, HD, interpsign],
      REWRITE_ALL [real_gt, ALL2, interpsigns, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r4],
      REWRITE_TAC [LENGTH, APPEND, TL, HD, ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [interpsign, real_gt],
      MATCH_MP_TAC (← PURE_REWRITE_RULE [real_gt, IMP_AND_THM] eq_eq_false_thm),
      EXISTS_TAC (← q r"y"),
      EXISTS_TAC (← q r"z"),
      EXISTS_TAC (← q r"p"),
      REWRITE_ALL [real_ordered_list, NOT_CONS_NIL, HD, interpsign],
      REWRITE_ALL [real_gt, ALL2, interpsigns, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r3],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND, partition_line, NOT_CONS_NIL],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [TL, HD, APPEND, ALL2],
      CLAIM (← q r"APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]"),
      MESON_TAC [real_gt, APPEND, APPEND_CONS],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH (sgns:(sign list) list)"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC (← PURE_REWRITE_RULE [real_gt, IMP_AND_THM] eq_eq_false_thm),
      EXISTS_TAC (← q r"y"),
      EXISTS_TAC (← q r"z"),
      EXISTS_TAC (← q r"p"),
      REWRITE_ALL [real_ordered_list, NOT_CONS_NIL, HD, interpsign],
      REWRITE_ALL [real_gt, ALL2, interpsigns, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list [y; z]"),
      ASM_MESON_TAC [ROL_APPEND],
      REWRITE_TAC [HD, NOT_CONS_NIL, real_ordered_list],
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r2],
      REWRITE_TAC [APPEND, TL, HD, ALL2],
      REPEAT STRIP_TAC,
      CLAIM (← q r"!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j"),
      MESON_TAC [APPEND, APPEND_CONS],
      DISCH_THEN (fun x => ONCE_REWRITE_TAC [x] THEN ONCE_REWRITE_ASSUMS [x]),
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH (sgns:(sign list)list)"),
      REWRITE_TAC [LENGTH_APPEND, LENGTH],
      ASM_SIMP_TAC [LENGTH_APPEND, BUTLAST_LENGTH, LENGTH, PARTITION_LINE_NOT_NIL, PARTITION_LINE_LENGTH],
      ARITH_TAC,
      REWRITE_ALL [TL, APPEND, HD],
      DISCH_THEN (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
      REPEAT STRIP_TAC,
      REPEAT STRIP_TAC,
      REWRITE_ALL [ALL2, interpsigns],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsign, real_gt],
      MATCH_MP_TAC (← PURE_REWRITE_RULE [real_gt, IMP_AND_THM] eq_eq_false_thm),
      EXISTS_TAC (← q r"y"),
      EXISTS_TAC (← q r"z"),
      EXISTS_TAC (← q r"p"),
      REWRITE_ALL [real_ordered_list, NOT_CONS_NIL, HD, interpsign],
      REWRITE_ALL [real_gt, ALL2, interpsigns, interpsign],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      CLAIM (← q r"real_ordered_list (CONS y(CONS  z qts))"),
      ASM_MESON_TAC [ROL_APPEND],
      REWRITE_TAC [HD, NOT_CONS_NIL, real_ordered_list],
      STRIP_TAC,
      ASM_MESON_TAC [real_gt],
      ASM_MESON_TAC [real_gt, real_gt],
      ASM_MESON_TAC [real_gt, r1]
    ])

  let BUTLAST_ID ← prove_by_refinement (
    (← q r"!l. ~(l = []) ==> (APPEND (BUTLAST l) [LAST l] = l)"),
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [],
    DISCH_THEN (fun _x => ALL_TAC),
    REWRITE_TAC [BUTLAST, APPEND, LAST],
    COND_CASES_TAC,
    ASM_REWRITE_TAC [BUTLAST, APPEND, LAST],
    ASM_REWRITE_TAC [APPEND],
    ASM_MESON_TAC []
  ])

  let BUTLAST_ID ← prove_by_refinement (
    (← q r"!l. ~(l = []) ==> (l = APPEND (BUTLAST l) [LAST l])"),
  [
    MESON_TAC [BUTLAST_ID]
  ])

  let BUTLAST_NIL ← prove_by_refinement (
    (← q r"!l. (BUTLAST l = []) <=> (l = []) \/ (?x. l = [x])"),
  [
    LIST_INDUCT_TAC,
    REWRITE_TAC [BUTLAST],
    REWRITE_TAC [BUTLAST, NOT_CONS_NIL],
    COND_CASES_TAC,
    ASM_REWRITE_TAC [],
    MESON_TAC [],
    ASM_REWRITE_TAC [],
    POP_ASSUM (fun x => REWRITE_ALL [x] THEN ASSUME_TAC x),
    REWRITE_TAC [NOT_CONS_NIL],
    STRIP_TAC,
    ASM_MESON_TAC [NOT_CONS_NIL, CONS_11]
  ])

  -- @@RETURN BEGIN
  return { INFERISIGN_ZERO_NEG_POS, INFERISIGN_ZERO_NEG_NEG, INFERISIGN_NEG_ZERO_NEG,
           INFERISIGN_NEG_ZERO_POS, INFERISIGN_ZERO_ZERO_POS, INFERISIGN_ZERO_ZERO_NEG,
           BUTLAST_ID, BUTLAST_NIL }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- work_thms.ml phrases from line 4401 to 5293; the theorems              -/
/- converted by gxwork/rq/ml2lean.py (disclosed; comments in the          -/
/- proofs are not carried over), the functions by hand.                   -/
/- ---------------------------------------------------------------------- -/

structure WorkThms06 where
  -- @@FIELDS
  INFIN_HD_POS_LEM : thm
  INFIN_TL_POS_LEM : thm
  INFIN_HD_NEG_LEM : thm
  INFIN_TL_NEG_LEM : thm
  INFIN_POS_POS : thm
  INFIN_POS_NEG : thm
  INFIN_NEG_POS : thm
  INFIN_NEG_NEG : thm
  INFIN_NIL_POS : thm
  INFIN_NIL_NEG : thm
  INFIN_SING_POS_POS : thm
  INFIN_SING_POS_NEG : thm
  INFIN_SING_NEG_POS : thm
  INFIN_SING_NEG_NEG : thm
  EL_SUC : thm
  EL_PRE : thm
  ALL2_EL_LT_LEM : thm
  ALL2_EL_LT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupWorkThms06 [HolBase] (D : WorkThmsDeps) (BWorkThms01 : WorkThms01) (BWorkThms02 : WorkThms02) (BWorkThms05 : WorkThms05) :
    ExceptT String IO WorkThms06 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, CASES_ON, CLAIM, EXISTS_TAC, INDUCT_TAC, MESON_TAC,
        prove_by_refinement, .. } := D
  let { ALL2, APPEND, BUTLAST, EL, HD, IMP_AND_THM, IN, LAST, LENGTH, LENGTH_0,
        LENGTH_APPEND, LT_SUC, NOT_CONS_NIL, NOT_NIL, POLY_DIFF_DOWN_LEFT5,
        POLY_DIFF_DOWN_RIGHT3, POLY_DIFF_UP_LEFT5, POLY_DIFF_UP_RIGHT3, PRE,
        REAL_EQ_IMP_LE, REAL_LT_IMP_LE, REAL_LT_TRANS, ROL_CONS_CONS,
        ROL_INSERT_BACK_THM, ROL_NIL, ROL_SING, SUBSET, SUC_INJ, TL, interpmat,
        interpsign, interpsigns, list_CASES, num_CASES, partition_line, real_gt,
        real_ordered_list, .. } := D.core1
  let { ALL2_APPEND, ALL2_APPEND_LENGTH, ALL2_LENGTH, BUTLAST_APPEND, BUTLAST_LENGTH,
        PARTITION_LINE_APPEND, PARTITION_LINE_LENGTH, PARTITION_LINE_NOT_NIL, .. } := BWorkThms01
  let { ALL2_INTERPSIGN_SUBSET, APPEND_APPEND, LAST_APPEND, .. } := BWorkThms02
  let { BUTLAST_ID, BUTLAST_NIL, .. } := BWorkThms05
  -- @@SCOPE END

  let INFIN_HD_POS_LEM ← prove_by_refinement (
    (← q r"!pts p ps r1 sgns.
  interpmat pts
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
    (CONS (CONS Unknown (CONS Pos r1)) sgns)  ==>
   nonconstant p ==>
  ?xminf.
   interpmat (CONS xminf pts)
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
      (CONS (CONS Neg (CONS Pos r1))
      (CONS (CONS Neg (CONS Pos r1))
      (CONS (CONS Unknown (CONS Pos r1)) sgns)))"),
  [
    REWRITE_TAC [interpmat, partition_line],
    REPEAT STRIP_TAC,
    DISJ_CASES_TAC (← ISPEC (← q r"pts:real list") list_CASES),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP (← ISPECL [(← q r"p:real list"), (← q r"poly_diff p"), (← q r"&0")] POLY_DIFF_DOWN_LEFT5))),
    ASM_REWRITE_TAC [real_gt],
    STRIP_TAC,
    EXISTS_TAC (← q r"Y"),
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [real_gt, REAL_LT_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. T"),
    ASM_MESON_TAC [SUBSET, IN],
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. T"),
    ASM_MESON_TAC [SUBSET, IN],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. T"),
    ASM_MESON_TAC [SUBSET, IN],
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [NOT_CONS_NIL, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
    COND_CASES_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [NOT_CONS_NIL, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP (← ISPECL [(← q r"p:real list"), (← q r"poly_diff p"), (← q r"h:real")] POLY_DIFF_DOWN_LEFT5))),
    ASM_REWRITE_TAC [real_gt],
    STRIP_TAC,
    EXISTS_TAC (← q r"Y"),
    ASM_REWRITE_TAC [real_ordered_list, HD, NOT_CONS_NIL],
    REWRITE_ALL [APPEND, TL, NOT_CONS_NIL, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. x < h"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. x < h"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. x < h"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    POP_ASSUM (fun x => REWRITE_ALL [x] THEN ASSUME_TAC x),
    REWRITE_ALL [APPEND, NOT_CONS_NIL, HD, TL, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP (← ISPECL [(← q r"p:real list"), (← q r"poly_diff p"), (← q r"h:real")] POLY_DIFF_DOWN_LEFT5))),
    ASM_REWRITE_TAC [real_gt],
    STRIP_TAC,
    EXISTS_TAC (← q r"Y"),
    ASM_REWRITE_TAC [real_ordered_list, HD, NOT_CONS_NIL],
    REWRITE_ALL [APPEND, TL, NOT_CONS_NIL, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. x < h"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. x < h"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. x < h"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE]
  ])

  let INFIN_TL_POS_LEM ← prove_by_refinement (
    (← q r"!pts p ps r1 sgns r2.
  interpmat pts
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
    (APPEND sgns [a; b; CONS Unknown (CONS Pos r2)]) ==>
   nonconstant p ==>
  ?xinf.
   interpmat (APPEND pts [xinf])
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
    (APPEND sgns
     [a; b; CONS Unknown (CONS Pos r2);
      CONS Pos (CONS Pos r2);
      CONS Pos (CONS Pos r2)])"),
  [
    REWRITE_TAC [interpmat, partition_line],
    REPEAT STRIP_TAC,
    CLAIM (← q r"LENGTH (partition_line pts) = LENGTH (APPEND sgns [a; b; CONS Unknown (CONS Pos r2)])"),
    ASM_MESON_TAC [ALL2_LENGTH],
    STRIP_TAC,
    CLAIM (← q r"LENGTH sgns = LENGTH (partition_line pts) - 3"),
    REWRITE_ALL [PARTITION_LINE_LENGTH],
    ASM_REWRITE_TAC [LENGTH_APPEND, LENGTH],
    ARITH_TAC,
    STRIP_TAC,
    CASES_ON (← q r"pts = []"),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [LENGTH, LENGTH_APPEND, APPEND, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN FALSE_ANTECEDENT_TAC,
    ARITH_TAC,
    ASM_SIMP_TAC [PARTITION_LINE_APPEND],
    CLAIM (← q r"pts = APPEND (BUTLAST pts) [LAST (pts:real list)]"),
    MATCH_MP_TAC BUTLAST_ID,
    ASM_MESON_TAC [],
    STRIP_TAC,
    CLAIM (← q r"ALL2
       (interpsigns
       (CONS (\x. poly p x)
       (CONS (\x. poly (poly_diff p) x) ps)))
       (partition_line (APPEND (BUTLAST pts) [LAST pts]))
       (APPEND sgns [a; b; CONS Unknown (CONS Pos r2)])"),
    ASM_MESON_TAC [],
    CASES_ON (← q r"BUTLAST (pts:real list) = []"),
    CLAIM (← q r"?w. pts = [w:real]"),
    ASM_MESON_TAC [BUTLAST_NIL],
    STRIP_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [LAST, LENGTH, LENGTH_APPEND, APPEND, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    CLAIM (← q r"sgns = []"),
    REPEAT_N 3 (POP_ASSUM (fun _x => ALL_TAC)),
    REWRITE_TAC [(← GSYM LENGTH_0)],
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [LAST, LENGTH, LENGTH_APPEND, APPEND, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP (← ISPECL [(← q r"p:real list"), (← q r"poly_diff p"), (← q r"w:real")] POLY_DIFF_UP_RIGHT3))),
    ASM_REWRITE_TAC [real_gt],
    STRIP_TAC,
    EXISTS_TAC (← q r"Y"),
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [ROL_CONS_CONS, ROL_SING],
    REWRITE_ALL [BUTLAST, TL, NOT_CONS_NIL, LAST, LENGTH, LENGTH_APPEND, APPEND, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [REAL_EQ_IMP_LE, REAL_LT_TRANS],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. w < x"),
    ASM_MESON_TAC [SUBSET, IN],
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [REAL_EQ_IMP_LE],
    ASM_MESON_TAC [REAL_LT_TRANS],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. w < x"),
    ASM_MESON_TAC [SUBSET, IN],
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [REAL_LT_IMP_LE],
    ASM_MESON_TAC [REAL_LT_IMP_LE, REAL_LT_TRANS],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. w < x"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS],
    CLAIM (← q r"LENGTH (BUTLAST (partition_line (BUTLAST pts))) = LENGTH sgns"),
    ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL],
    REWRITE_ALL [PARTITION_LINE_LENGTH, LENGTH_APPEND, LENGTH],
    MP_TAC (← ISPEC (← q r"pts:real list") BUTLAST_LENGTH),
    STRIP_TAC,
    LABEL_ALL_TAC,
    PROVE_ASSUM_ANTECEDENT_TAC 0,
    ASM_MESON_TAC [],
    POP_ASSUM SUBST1_TAC,
    REPEAT_N 4 (POP_ASSUM (fun _x => ALL_TAC)),
    POP_ASSUM SUBST1_TAC,
    ARITH_TAC,
    STRIP_TAC,
    ASM_SIMP_TAC [PARTITION_LINE_APPEND],
    STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
    REWRITE_ALL [BUTLAST, TL, NOT_CONS_NIL, LAST, LENGTH, LENGTH_APPEND, APPEND, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    REPEAT STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP (← ISPECL [(← q r"p:real list"), (← q r"poly_diff p"), (← q r"LAST pts:real")] POLY_DIFF_UP_RIGHT3))),
    ASM_REWRITE_TAC [real_gt],
    STRIP_TAC,
    EXISTS_TAC (← q r"Y"),
    REPEAT STRIP_TAC,
    MATCH_MP_TAC ROL_INSERT_BACK_THM,
    ASM_REWRITE_TAC [],
    ONCE_ASM_REWRITE_TAC [],
    ASM_SIMP_TAC [PARTITION_LINE_APPEND],
    REWRITE_TAC [partition_line, TL],
    SIMP_TAC [NOT_CONS_NIL, LAST_APPEND],
    REWRITE_TAC [LAST],
    SIMP_TAC [BUTLAST_APPEND, NOT_CONS_NIL],
    REWRITE_TAC [BUTLAST, NOT_CONS_NIL],
    REWRITE_TAC [APPEND_APPEND],
    MATCH_MP_TAC ALL2_APPEND,
    ASM_REWRITE_TAC [],
    REWRITE_ALL [ALL2, BUTLAST, TL, NOT_CONS_NIL, LAST, LENGTH, LENGTH_APPEND, APPEND, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
    ASM_MESON_TAC [real_gt, REAL_LT_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. LAST pts < x"),
    ASM_MESON_TAC [SUBSET, IN],
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [REAL_EQ_IMP_LE],
    ASM_MESON_TAC [REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. LAST pts < x"),
    ASM_MESON_TAC [SUBSET, IN],
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [REAL_EQ_IMP_LE, REAL_LT_IMP_LE],
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [REAL_EQ_IMP_LE, REAL_LT_IMP_LE, REAL_LT_TRANS],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. LAST pts < x"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS]
  ])

  let INFIN_HD_NEG_LEM ← prove_by_refinement (
    (← q r"!pts p ps r1 sgns.
  interpmat pts
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
    (CONS (CONS Unknown (CONS Neg r1)) sgns)  ==>
   nonconstant p ==>
  ?xminf.
   interpmat (CONS xminf pts)
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
      (CONS (CONS Pos (CONS Neg r1))
      (CONS (CONS Pos (CONS Neg r1))
      (CONS (CONS Unknown (CONS Neg r1)) sgns)))"),
  [
    REWRITE_TAC [interpmat, partition_line],
    REPEAT STRIP_TAC,
    DISJ_CASES_TAC (← ISPEC (← q r"pts:real list") list_CASES),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP (← ISPECL [(← q r"p:real list"), (← q r"poly_diff p"), (← q r"&0")] POLY_DIFF_UP_LEFT5))),
    ASM_REWRITE_TAC [real_gt],
    STRIP_TAC,
    EXISTS_TAC (← q r"Y"),
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [real_gt, REAL_LT_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. T"),
    ASM_MESON_TAC [SUBSET, IN],
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. T"),
    ASM_MESON_TAC [SUBSET, IN],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. T"),
    ASM_MESON_TAC [SUBSET, IN],
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [NOT_CONS_NIL, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
    COND_CASES_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [NOT_CONS_NIL, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP (← ISPECL [(← q r"p:real list"), (← q r"poly_diff p"), (← q r"h:real")] POLY_DIFF_UP_LEFT5))),
    ASM_REWRITE_TAC [real_gt],
    STRIP_TAC,
    EXISTS_TAC (← q r"Y"),
    ASM_REWRITE_TAC [real_ordered_list, HD, NOT_CONS_NIL],
    REWRITE_ALL [APPEND, TL, NOT_CONS_NIL, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. x < h"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. x < h"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. x < h"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    POP_ASSUM (fun x => REWRITE_ALL [x] THEN ASSUME_TAC x),
    REWRITE_ALL [APPEND, NOT_CONS_NIL, HD, TL, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP (← ISPECL [(← q r"p:real list"), (← q r"poly_diff p"), (← q r"h:real")] POLY_DIFF_UP_LEFT5))),
    ASM_REWRITE_TAC [real_gt],
    STRIP_TAC,
    EXISTS_TAC (← q r"Y"),
    ASM_REWRITE_TAC [real_ordered_list, HD, NOT_CONS_NIL],
    REWRITE_ALL [APPEND, TL, NOT_CONS_NIL, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. x < h"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. x < h"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. x < h"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE]
  ])

  let INFIN_TL_NEG_LEM ← prove_by_refinement (
    (← q r"!pts p ps r1 sgns r2.
  interpmat pts
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
    (APPEND sgns [a; b; CONS Unknown (CONS Neg r2)]) ==>
   nonconstant p ==>
  ?xinf.
   interpmat (APPEND pts [xinf])
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
    (APPEND sgns
     [a; b; CONS Unknown (CONS Neg r2);
      CONS Neg (CONS Neg r2);
      CONS Neg (CONS Neg r2)])"),
  [
    REWRITE_TAC [interpmat, partition_line],
    REPEAT STRIP_TAC,
    CLAIM (← q r"LENGTH (partition_line pts) = LENGTH (APPEND sgns [a; b; CONS Unknown (CONS Neg r2)])"),
    ASM_MESON_TAC [ALL2_LENGTH],
    STRIP_TAC,
    CLAIM (← q r"LENGTH sgns = LENGTH (partition_line pts) - 3"),
    REWRITE_ALL [PARTITION_LINE_LENGTH],
    ASM_REWRITE_TAC [LENGTH_APPEND, LENGTH],
    ARITH_TAC,
    STRIP_TAC,
    CASES_ON (← q r"pts = []"),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [LENGTH, LENGTH_APPEND, APPEND, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN FALSE_ANTECEDENT_TAC,
    ARITH_TAC,
    ASM_SIMP_TAC [PARTITION_LINE_APPEND],
    CLAIM (← q r"pts = APPEND (BUTLAST pts) [LAST (pts:real list)]"),
    MATCH_MP_TAC BUTLAST_ID,
    ASM_MESON_TAC [],
    STRIP_TAC,
    CLAIM (← q r"ALL2
       (interpsigns
       (CONS (\x. poly p x)
       (CONS (\x. poly (poly_diff p) x) ps)))
       (partition_line (APPEND (BUTLAST pts) [LAST pts]))
       (APPEND sgns [a; b; CONS Unknown (CONS Neg r2)])"),
    ASM_MESON_TAC [],
    CASES_ON (← q r"BUTLAST (pts:real list) = []"),
    CLAIM (← q r"?w. pts = [w:real]"),
    ASM_MESON_TAC [BUTLAST_NIL],
    STRIP_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [LAST, LENGTH, LENGTH_APPEND, APPEND, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    CLAIM (← q r"sgns = []"),
    REPEAT_N 3 (POP_ASSUM (fun _x => ALL_TAC)),
    REWRITE_TAC [(← GSYM LENGTH_0)],
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [LAST, LENGTH, LENGTH_APPEND, APPEND, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP (← ISPECL [(← q r"p:real list"), (← q r"poly_diff p"), (← q r"w:real")] POLY_DIFF_DOWN_RIGHT3))),
    ASM_REWRITE_TAC [real_gt],
    STRIP_TAC,
    EXISTS_TAC (← q r"Y"),
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [ROL_CONS_CONS, ROL_SING],
    REWRITE_ALL [BUTLAST, TL, NOT_CONS_NIL, LAST, LENGTH, LENGTH_APPEND, APPEND, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [REAL_EQ_IMP_LE, REAL_LT_TRANS],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. w < x"),
    ASM_MESON_TAC [SUBSET, IN],
    ASM_MESON_TAC [REAL_EQ_IMP_LE, REAL_LT_TRANS],
    ASM_MESON_TAC [REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. w < x"),
    ASM_MESON_TAC [SUBSET, IN],
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [REAL_LT_IMP_LE],
    ASM_MESON_TAC [REAL_LT_IMP_LE, REAL_LT_TRANS],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. w < x"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS],
    CLAIM (← q r"LENGTH (BUTLAST (partition_line (BUTLAST pts))) = LENGTH sgns"),
    ASM_SIMP_TAC [BUTLAST_LENGTH, PARTITION_LINE_NOT_NIL],
    REWRITE_ALL [PARTITION_LINE_LENGTH, LENGTH_APPEND, LENGTH],
    MP_TAC (← ISPEC (← q r"pts:real list") BUTLAST_LENGTH),
    STRIP_TAC,
    LABEL_ALL_TAC,
    PROVE_ASSUM_ANTECEDENT_TAC 0,
    ASM_MESON_TAC [],
    POP_ASSUM SUBST1_TAC,
    REPEAT_N 4 (POP_ASSUM (fun _x => ALL_TAC)),
    POP_ASSUM SUBST1_TAC,
    ARITH_TAC,
    STRIP_TAC,
    ASM_SIMP_TAC [PARTITION_LINE_APPEND],
    STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP x y))))),
    REWRITE_ALL [BUTLAST, TL, NOT_CONS_NIL, LAST, LENGTH, LENGTH_APPEND, APPEND, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    REPEAT STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP (← ISPECL [(← q r"p:real list"), (← q r"poly_diff p"), (← q r"LAST pts:real")] POLY_DIFF_DOWN_RIGHT3))),
    ASM_REWRITE_TAC [real_gt],
    STRIP_TAC,
    EXISTS_TAC (← q r"Y"),
    REPEAT STRIP_TAC,
    MATCH_MP_TAC ROL_INSERT_BACK_THM,
    ASM_REWRITE_TAC [],
    ONCE_ASM_REWRITE_TAC [],
    ASM_SIMP_TAC [PARTITION_LINE_APPEND],
    REWRITE_TAC [partition_line, TL],
    SIMP_TAC [NOT_CONS_NIL, LAST_APPEND],
    REWRITE_TAC [LAST],
    SIMP_TAC [BUTLAST_APPEND, NOT_CONS_NIL],
    REWRITE_TAC [BUTLAST, NOT_CONS_NIL],
    REWRITE_TAC [APPEND_APPEND],
    MATCH_MP_TAC ALL2_APPEND,
    ASM_REWRITE_TAC [],
    REWRITE_ALL [ALL2, BUTLAST, TL, NOT_CONS_NIL, LAST, LENGTH, LENGTH_APPEND, APPEND, partition_line, ALL2, interpsigns, interpsign, real_gt, ROL_SING],
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
    ASM_MESON_TAC [real_gt, REAL_LT_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. LAST pts < x"),
    ASM_MESON_TAC [SUBSET, IN],
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [REAL_EQ_IMP_LE],
    ASM_MESON_TAC [REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. LAST pts < x"),
    ASM_MESON_TAC [SUBSET, IN],
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [REAL_EQ_IMP_LE, REAL_LT_IMP_LE],
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_MESON_TAC [REAL_EQ_IMP_LE, REAL_LT_IMP_LE, REAL_LT_TRANS],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. LAST pts < x"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS]
  ])

  let INFIN_POS_POS ← prove_by_refinement (
    (← q r"!pts p ps r1 sgns r2.
  interpmat pts
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
    (APPEND (CONS (CONS Unknown (CONS Pos r1)) sgns)
     [a; b; CONS Unknown (CONS Pos r2)]) ==>
   nonconstant p ==>
  ?xminf xinf.
   interpmat (APPEND (CONS xminf pts) [xinf])
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
    (APPEND
      (CONS (CONS Neg (CONS Pos r1))
      (CONS (CONS Neg (CONS Pos r1))
      (CONS (CONS Unknown (CONS Pos r1)) sgns)))
     [a; b; CONS Unknown (CONS Pos r2);
      CONS Pos (CONS Pos r2);
      CONS Pos (CONS Pos r2)])"),
  [
    REPEAT STRIP_TAC,
    REWRITE_ASSUMS [APPEND],
    FIRST_ASSUM (MP_TAC o (MATCH_MP INFIN_HD_POS_LEM)),
    ASM_REWRITE_TAC [],
    STRIP_TAC,
    EXISTS_TAC (← q r"xminf"),
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] INFIN_TL_POS_LEM),
    ASM_REWRITE_TAC [APPEND]
  ])

  let INFIN_POS_NEG ← prove_by_refinement (
    (← q r"!pts p ps r1 sgns r2.
  interpmat pts
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
    (APPEND (CONS (CONS Unknown (CONS Pos r1)) sgns)
     [a; b; CONS Unknown (CONS Neg r2)]) ==>
   nonconstant p ==>
  ?xminf xinf.
   interpmat (APPEND (CONS xminf pts) [xinf])
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
    (APPEND
      (CONS (CONS Neg (CONS Pos r1))
      (CONS (CONS Neg (CONS Pos r1))
      (CONS (CONS Unknown (CONS Pos r1)) sgns)))
     [a; b; CONS Unknown (CONS Neg r2);
      CONS Neg (CONS Neg r2);
      CONS Neg (CONS Neg r2)])"),
  [
    REPEAT STRIP_TAC,
    REWRITE_ASSUMS [APPEND],
    FIRST_ASSUM (MP_TAC o (MATCH_MP INFIN_HD_POS_LEM)),
    ASM_REWRITE_TAC [],
    STRIP_TAC,
    EXISTS_TAC (← q r"xminf"),
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] INFIN_TL_NEG_LEM),
    ASM_REWRITE_TAC [APPEND]
  ])

  let INFIN_NEG_POS ← prove_by_refinement (
    (← q r"!pts p ps r1 sgns r2.
  interpmat pts
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
    (APPEND (CONS (CONS Unknown (CONS Neg r1)) sgns)
     [a; b; CONS Unknown (CONS Pos r2)]) ==>
   nonconstant p ==>
  ?xminf xinf.
   interpmat (APPEND (CONS xminf pts) [xinf])
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
    (APPEND
      (CONS (CONS Pos (CONS Neg r1))
      (CONS (CONS Pos (CONS Neg r1))
      (CONS (CONS Unknown (CONS Neg r1)) sgns)))
     [a; b; CONS Unknown (CONS Pos r2);
      CONS Pos (CONS Pos r2);
      CONS Pos (CONS Pos r2)])"),
  [
    REPEAT STRIP_TAC,
    REWRITE_ASSUMS [APPEND],
    FIRST_ASSUM (MP_TAC o (MATCH_MP INFIN_HD_NEG_LEM)),
    ASM_REWRITE_TAC [],
    STRIP_TAC,
    EXISTS_TAC (← q r"xminf"),
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] INFIN_TL_POS_LEM),
    ASM_REWRITE_TAC [APPEND]
  ])

  let INFIN_NEG_NEG ← prove_by_refinement (
    (← q r"!pts p ps r1 sgns r2.
  interpmat pts
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
    (APPEND (CONS (CONS Unknown (CONS Neg r1)) sgns)
     [a; b; CONS Unknown (CONS Neg r2)]) ==>
   nonconstant p ==>
  ?xminf xinf.
   interpmat (APPEND (CONS xminf pts) [xinf])
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
    (APPEND
      (CONS (CONS Pos (CONS Neg r1))
      (CONS (CONS Pos (CONS Neg r1))
      (CONS (CONS Unknown (CONS Neg r1)) sgns)))
     [a; b; CONS Unknown (CONS Neg r2);
      CONS Neg (CONS Neg r2);
      CONS Neg (CONS Neg r2)])"),
  [
    REPEAT STRIP_TAC,
    REWRITE_ASSUMS [APPEND],
    FIRST_ASSUM (MP_TAC o (MATCH_MP INFIN_HD_NEG_LEM)),
    ASM_REWRITE_TAC [],
    STRIP_TAC,
    EXISTS_TAC (← q r"xminf"),
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] INFIN_TL_NEG_LEM),
    ASM_REWRITE_TAC [APPEND]
  ])

  let INFIN_NIL_POS ← prove_by_refinement (
    (← q r"!p ps r1.
  interpmat []
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
    [CONS Unknown (CONS Pos r1)]  ==>
   nonconstant p ==>
  ?xminf xinf.
   interpmat [xminf; xinf]
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
      [CONS Neg (CONS Pos r1);
       CONS Neg (CONS Pos r1);
       CONS Unknown (CONS Pos r1);
       CONS Pos (CONS Pos r1);
       CONS Pos (CONS Pos r1)]"),
  [
    REWRITE_TAC [real_gt, interpmat, partition_line, ROL_NIL, ALL2, interpsigns, interpsign],
    REPEAT STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP (← ISPECL [(← q r"p:real list"), (← q r"poly_diff p"), (← q r"&0")] POLY_DIFF_UP_RIGHT3))),
    ASM_REWRITE_TAC [real_gt],
    STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP (← ISPECL [(← q r"p:real list"), (← q r"poly_diff p"), (← q r"&0")] POLY_DIFF_DOWN_LEFT5))),
    ASM_REWRITE_TAC [real_gt],
    STRIP_TAC,
    EXISTS_TAC (← q r"Y'"),
    EXISTS_TAC (← q r"Y"),
    ASM_REWRITE_TAC [real_gt, NOT_CONS_NIL, HD, TL, APPEND, ALL2, interpsigns, interpsign],
    REWRITE_TAC [ROL_CONS_CONS, ROL_SING],
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    ASM_MESON_TAC [REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. T"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS],
    ASM_MESON_TAC [REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. T"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. T"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS],
    ASM_MESON_TAC [REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. T"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS],
    ASM_MESON_TAC [REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. T"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS]
  ])

  let INFIN_NIL_NEG ← prove_by_refinement (
    (← q r"!p ps r1.
  interpmat []
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
    [CONS Unknown (CONS Neg r1)]  ==>
   nonconstant p ==>
  ?xminf xinf.
   interpmat [xminf; xinf]
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
      [CONS Pos (CONS Neg r1);
       CONS Pos (CONS Neg r1);
       CONS Unknown (CONS Neg r1);
       CONS Neg (CONS Neg r1);
       CONS Neg (CONS Neg r1)]"),
  [
    REWRITE_TAC [real_gt, interpmat, partition_line, ROL_NIL, ALL2, interpsigns, interpsign],
    REPEAT STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP (← ISPECL [(← q r"p:real list"), (← q r"poly_diff p"), (← q r"&0")] POLY_DIFF_DOWN_RIGHT3))),
    ASM_REWRITE_TAC [real_gt],
    STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP (← ISPECL [(← q r"p:real list"), (← q r"poly_diff p"), (← q r"&0")] POLY_DIFF_UP_LEFT5))),
    ASM_REWRITE_TAC [real_gt],
    STRIP_TAC,
    EXISTS_TAC (← q r"Y'"),
    EXISTS_TAC (← q r"Y"),
    ASM_REWRITE_TAC [real_gt, NOT_CONS_NIL, HD, TL, APPEND, ALL2, interpsigns, interpsign],
    REWRITE_TAC [ROL_CONS_CONS, ROL_SING],
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    ASM_MESON_TAC [REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. T"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS],
    ASM_MESON_TAC [REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. T"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. T"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS],
    ASM_MESON_TAC [REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. T"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS],
    ASM_MESON_TAC [REAL_LT_TRANS, REAL_LT_IMP_LE, REAL_EQ_IMP_LE],
    MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] ALL2_INTERPSIGN_SUBSET),
    EXISTS_TAC (← q r"\x. T"),
    ASM_MESON_TAC [SUBSET, IN, REAL_LT_TRANS]
  ])

  let INFIN_SING_POS_POS ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"xinf"
    let p2 ← prove r"(?y x. P x y) ==> (?x y. P x y)" (MESON_TAC [])
    let p3 ← prove r"[x; y; z] = APPEND [] [x; y; z]" (REWRITE_TAC [APPEND])
    let q4 ← q r"!p ps r1 x s2 r2 r3.
  interpmat [x]
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
    [CONS Unknown (CONS Pos r1);CONS s2 r2;CONS Unknown (CONS Pos r3)]  ==>
   nonconstant p ==>
  ?xminf xinf.
   interpmat [xminf; x; xinf]
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
      [CONS Neg (CONS Pos r1);
       CONS Neg (CONS Pos r1);
       CONS Unknown (CONS Pos r1);
       CONS s2 r2;
       CONS Unknown (CONS Pos r3);
       CONS Pos (CONS Pos r3);
       CONS Pos (CONS Pos r3)]"
    prove_by_refinement (
      q4,
    [
      REPEAT STRIP_TAC,
      ONCE_REWRITE_ASSUMS [p3],
      FIRST_ASSUM (MP_TAC o (MATCH_MP INFIN_TL_POS_LEM)),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      MATCH_MP_TAC p2,
      EXISTS_TAC q1,
      REWRITE_ALL [APPEND],
      FIRST_ASSUM (MP_TAC o (MATCH_MP INFIN_HD_POS_LEM)),
      ASM_REWRITE_TAC []
    ])

  let INFIN_SING_POS_NEG ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"xinf"
    let p2 ← prove r"(?y x. P x y) ==> (?x y. P x y)" (MESON_TAC [])
    let p3 ← prove r"[x; y; z] = APPEND [] [x; y; z]" (REWRITE_TAC [APPEND])
    let q4 ← q r"!p ps r1 x s2 r2 r3.
  interpmat [x]
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
    [CONS Unknown (CONS Pos r1);CONS s2 r2;CONS Unknown (CONS Neg r3)]  ==>
   nonconstant p ==>
  ?xminf xinf.
   interpmat [xminf; x; xinf]
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
      [CONS Neg (CONS Pos r1);
       CONS Neg (CONS Pos r1);
       CONS Unknown (CONS Pos r1);
       CONS s2 r2;
       CONS Unknown (CONS Neg r3);
       CONS Neg (CONS Neg r3);
       CONS Neg (CONS Neg r3)]"
    prove_by_refinement (
      q4,
    [
      REPEAT STRIP_TAC,
      ONCE_REWRITE_ASSUMS [p3],
      FIRST_ASSUM (MP_TAC o (MATCH_MP INFIN_TL_NEG_LEM)),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      MATCH_MP_TAC p2,
      EXISTS_TAC q1,
      REWRITE_ALL [APPEND],
      FIRST_ASSUM (MP_TAC o (MATCH_MP INFIN_HD_POS_LEM)),
      ASM_REWRITE_TAC []
    ])

  let INFIN_SING_NEG_POS ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"xinf"
    let p2 ← prove r"(?y x. P x y) ==> (?x y. P x y)" (MESON_TAC [])
    let p3 ← prove r"[x; y; z] = APPEND [] [x; y; z]" (REWRITE_TAC [APPEND])
    let q4 ← q r"!p ps r1 x s2 r2 r3.
  interpmat [x]
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
    [CONS Unknown (CONS Neg r1);CONS s2 r2;CONS Unknown (CONS Pos r3)]  ==>
   nonconstant p ==>
  ?xminf xinf.
   interpmat [xminf; x; xinf]
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
      [CONS Pos (CONS Neg r1);
       CONS Pos (CONS Neg r1);
       CONS Unknown (CONS Neg r1);
       CONS s2 r2;
       CONS Unknown (CONS Pos r3);
       CONS Pos (CONS Pos r3);
       CONS Pos (CONS Pos r3)]"
    prove_by_refinement (
      q4,
    [
      REPEAT STRIP_TAC,
      ONCE_REWRITE_ASSUMS [p3],
      FIRST_ASSUM (MP_TAC o (MATCH_MP INFIN_TL_POS_LEM)),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      MATCH_MP_TAC p2,
      EXISTS_TAC q1,
      REWRITE_ALL [APPEND],
      FIRST_ASSUM (MP_TAC o (MATCH_MP INFIN_HD_NEG_LEM)),
      ASM_REWRITE_TAC []
    ])

  let INFIN_SING_NEG_NEG ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"xinf"
    let p2 ← prove r"(?y x. P x y) ==> (?x y. P x y)" (MESON_TAC [])
    let p3 ← prove r"[x; y; z] = APPEND [] [x; y; z]" (REWRITE_TAC [APPEND])
    let q4 ← q r"!p ps r1 x s2 r2 r3.
  interpmat [x]
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
    [CONS Unknown (CONS Neg r1);CONS s2 r2;CONS Unknown (CONS Neg r3)]  ==>
   nonconstant p ==>
  ?xminf xinf.
   interpmat [xminf; x; xinf]
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps))
      [CONS Pos (CONS Neg r1);
       CONS Pos (CONS Neg r1);
       CONS Unknown (CONS Neg r1);
       CONS s2 r2;
       CONS Unknown (CONS Neg r3);
       CONS Neg (CONS Neg r3);
       CONS Neg (CONS Neg r3)]"
    prove_by_refinement (
      q4,
    [
      REPEAT STRIP_TAC,
      ONCE_REWRITE_ASSUMS [p3],
      FIRST_ASSUM (MP_TAC o (MATCH_MP INFIN_TL_NEG_LEM)),
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      MATCH_MP_TAC p2,
      EXISTS_TAC q1,
      REWRITE_ALL [APPEND],
      FIRST_ASSUM (MP_TAC o (MATCH_MP INFIN_HD_NEG_LEM)),
      ASM_REWRITE_TAC []
    ])

  let EL_SUC ← prove_by_refinement (
    (← q r"!i h t. EL (SUC i) (CONS h t) = EL i t"),
  [
    REWRITE_TAC [EL, TL]
  ])

  let EL_PRE ← prove_by_refinement (
    (← q r"!i h t. ~(i = 0) ==> (EL i (CONS h t) = EL (PRE i) t)"),
  [
    INDUCT_TAC,
    REWRITE_TAC [],
    REPEAT STRIP_TAC,
    REWRITE_TAC [EL, TL, PRE]
  ])

  let ALL2_EL_LT_LEM ← prove_by_refinement (
    (← q r"!k P l1 l2 n.
    (k = LENGTH l1) /\ ALL2 P l1 l2 /\ n < k ==>
       P (EL n l1) (EL n l2)"),
  [
    INDUCT_TAC,
    REPEAT STRIP_TAC,
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    REPEAT STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_LENGTH)),
    STRIP_TAC,
    CLAIM (← q r"~(l1 = [])"),
    REWRITE_TAC [(← GSYM LENGTH_0)],
    REPEAT_N 3 (POP_ASSUM (fun _x => ALL_TAC)),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    REWRITE_TAC [NOT_NIL],
    STRIP_TAC,
    CLAIM (← q r"~(l2 = [])"),
    REWRITE_TAC [(← GSYM LENGTH_0)],
    POP_ASSUM (fun _x => ALL_TAC),
    POP_ASSUM (SUBST1_TAC o GSYM),
    REPEAT_N 2 (POP_ASSUM (fun _x => ALL_TAC)),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    REWRITE_TAC [NOT_NIL],
    STRIP_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ASSUMS [LENGTH, SUC_INJ, ALL2],
    REPEAT_N 3 (POP_ASSUM MP_TAC),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REPEAT STRIP_TAC,
    DISJ_CASES_TAC (← ISPEC (← q r"n:num") num_CASES),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    ASM_REWRITE_TAC [EL, HD],
    POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_TAC [EL, TL],
    REWRITE_ASSUMS [LENGTH, SUC_INJ, ALL2, LT_SUC],
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_REWRITE_TAC []
  ])

  let ALL2_EL_LT ← prove_by_refinement (
    (← q r"!P l1 l2 n. ALL2 P l1 l2 /\ n < LENGTH l1 ==> P (EL n l1) (EL n l2)"),
  [
    MESON_TAC [ALL2_EL_LT_LEM]
  ])

  -- @@RETURN BEGIN
  return { INFIN_HD_POS_LEM, INFIN_TL_POS_LEM, INFIN_HD_NEG_LEM, INFIN_TL_NEG_LEM,
           INFIN_POS_POS, INFIN_POS_NEG, INFIN_NEG_POS, INFIN_NEG_NEG, INFIN_NIL_POS,
           INFIN_NIL_NEG, INFIN_SING_POS_POS, INFIN_SING_POS_NEG, INFIN_SING_NEG_POS,
           INFIN_SING_NEG_NEG, EL_SUC, EL_PRE, ALL2_EL_LT_LEM, ALL2_EL_LT }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- work_thms.ml phrases from line 5301 to 5990; the theorems              -/
/- converted by gxwork/rq/ml2lean.py (disclosed; comments in the          -/
/- proofs are not carried over), the functions by hand.                   -/
/- ---------------------------------------------------------------------- -/

structure WorkThms07 where
  -- @@FIELDS
  ALL2_EL_LEM : thm
  ALL2_EL : thm
  EL_MAP : thm
  REMOVE_HD_COL : thm
  REMOVE_COL1 : thm
  ALL_EL : thm
  INTERPMAT_POL_LENGTH_LEM : thm
  INTERPMAT_POL_LENGTH : thm
  ALL2_BUTLAST : thm
  REMOVE_LAST : thm
  INSERTAT : thm
  MAP2_EL_LEM : thm
  MAP2_EL : thm
  INSERTAT_LENGTH : thm
  NUM_CASES_TAC : term → tactic
  INSERTAT_TL : thm
  INSERTAT_EL : thm
  MATINSERT_THM : thm
  INTERP_CONST_POS : thm
  INTERP_CONST_NEG : thm
  INTERP_CONST_ZERO : thm
  EL_REPLICATE : thm
  ALL2_UNKNOWN : thm
  MATINSERT_THM2 : thm
  FUN_EQ_TAC : tactic
  INSERTAT_0 : thm
  INFERPSIGN_MATINSERT_THM : thm
  INFERPSIGN_POS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupWorkThms07 [HolBase] (D : WorkThmsDeps) (BWorkThms01 : WorkThms01) (BWorkThms06 : WorkThms06) :
    ExceptT String IO WorkThms07 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, CASES_ON, CLAIM, DISJ_LCASE, EXISTS_TAC,
        INDUCT_TAC, LIST_INDUCT_TAC, MESON_TAC, TYPE_TAC, TYPE_TACL,
        new_recursive_definition, prove_by_refinement, .. } := D
  let { ALL, ALL2, APPEND, BUTLAST, DE_MORGAN_THM, EL, FUN_EQ_THM, GT, HD, LENGTH,
        LENGTH_0, LENGTH_1, LENGTH_APPEND, LENGTH_MAP, LENGTH_MAP2, LENGTH_REPLICATE,
        LET_TRANS, LE_SUC, LTE_TRANS, LT_0, LT_IMP_LE, LT_SUC, LT_TRANS, MAP, MAP2,
        NOT_CONS_NIL, NOT_EXISTS_THM, NOT_LE, NOT_NIL, NOT_SUC, PRE, REAL_ADD_LID,
        REAL_MUL_RZERO, REPLICATE, SUC_INJ, TL, interpmat, interpsign, interpsigns,
        num_CASES, num_RECURSION, partition_line, real_gt, .. } := D.core1
  let { ALL2_APPEND, ALL2_APPEND_LENGTH, ALL2_LENGTH, APPEND_CONS, BUTLAST_LENGTH,
        HD_TL, LENGTH_TL, PARTITION_LINE_APPEND, PARTITION_LINE_LENGTH,
        PARTITION_LINE_NOT_NIL, .. } := BWorkThms01
  let { ALL2_EL_LT, EL_PRE, EL_SUC, .. } := BWorkThms06
  -- @@SCOPE END

  let ALL2_EL_LEM ← prove_by_refinement (
    (← q r"!k P (l1:A list) (l2:B list).  (k = LENGTH l1) /\ (k = LENGTH l2) /\
    ~(?i. i < LENGTH l1 /\ ~(P (EL i l1) (EL i l2))) ==> ALL2 P l1 l2"),
  [
    INDUCT_TAC,
    REPEAT STRIP_TAC,
    EVERY_ASSUM (MP_TAC o GSYM),
    ASM_MESON_TAC [LENGTH_0, ALL2],
    REPEAT STRIP_TAC,
    CLAIM (← q r"~(l1 = [])"),
    REWRITE_TAC [(← GSYM LENGTH_0)],
    REPEAT_N 2 (POP_ASSUM (fun _x => ALL_TAC)),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    REWRITE_TAC [NOT_NIL],
    STRIP_TAC,
    CLAIM (← q r"~(l2 = [])"),
    REWRITE_TAC [(← GSYM LENGTH_0)],
    REPEAT_N 2 (POP_ASSUM (fun _x => ALL_TAC)),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    REWRITE_TAC [NOT_NIL],
    STRIP_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [LENGTH, SUC_INJ, ALL2],
    STRIP_TAC,
    ASM_MESON_TAC [LT_0, EL, HD],
    FIRST_ASSUM MATCH_MP_TAC,
    ASM_REWRITE_TAC [],
    STRIP_TAC,
    ASM_MESON_TAC [],
    REPEAT STRIP_TAC,
    CLAIM (← q r"SUC i < SUC (LENGTH t)"),
    POP_ASSUM (fun _x => ALL_TAC),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    REPEAT_N 3 (POP_ASSUM MP_TAC),
    REWRITE_ASSUMS [NOT_EXISTS_THM],
    POP_ASSUM (ASSUME_TAC o (ISPEC (← q r"SUC i"))),
    REWRITE_ALL [LT_SUC],
    REWRITE_ALL [EL, TL],
    ASM_MESON_TAC []
  ])

  let ALL2_EL ← prove_by_refinement (
    (← q r"!P (l1:A list) (l2:B list). ALL2 P l1 l2 <=> (LENGTH l1 = LENGTH l2) /\
    ~(?i. i < LENGTH l1 /\ ~(P (EL i l1) (EL i l2)))"),
  [
    REPEAT STRIP_TAC,
    EQ_TAC,
    REPEAT STRIP_TAC,
    MATCH_MP_TAC ALL2_LENGTH,
    ASM_MESON_TAC [],
    ASM_MESON_TAC [ALL2_EL_LT],
    ASM_MESON_TAC [ALL2_EL_LEM]
  ])

  let EL_MAP ← prove_by_refinement (
    (← q r"!f l n. n < LENGTH l ==> (EL n (MAP f l) = f (EL n l))"),
  [
    STRIP_TAC,
    LIST_INDUCT_TAC,
    REWRITE_TAC [LENGTH],
    ARITH_TAC,
    REWRITE_TAC [MAP, LENGTH],
    INDUCT_TAC,
    REWRITE_TAC [MAP, LENGTH, EL, HD],
    REWRITE_ALL [LT_SUC, TL, MAP, LENGTH, EL, HD],
    ASM_REWRITE_TAC []
  ])

  let REMOVE_HD_COL ← prove_by_refinement (
    (← q r"!p ps sgns pts.
    interpmat pts (CONS p ps) sgns ==> interpmat pts ps (MAP TL sgns)"),
  [
    REWRITE_TAC [interpmat, ALL2_EL],
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [],
    REWRITE_ALL [ALL2_EL],
    ASM_MESON_TAC [LENGTH_MAP],
    REWRITE_ASSUMS [NOT_EXISTS_THM],
    REPEAT_N 2 (POP_ASSUM MP_TAC),
    POP_ASSUM (MP_TAC o (ISPEC (← q r"i:num"))),
    REWRITE_TAC [DE_MORGAN_THM],
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [],
    REWRITE_ALL [interpsigns],
    CLAIM (← q r"i < LENGTH sgns"),
    ASM_MESON_TAC [],
    STRIP_TAC,
    ASM_SIMP_TAC [EL_MAP],
    REWRITE_ALL [interpsigns],
    CLAIM (← q r"~(EL i sgns = [])"),
    REWRITE_TAC [(← GSYM LENGTH_0)],
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_LENGTH)),
    REWRITE_TAC [LENGTH],
    ARITH_TAC,
    DISCH_THEN (MP_TAC o (MATCH_MP HD_TL)),
    DISCH_THEN (fun x => REPEAT (POP_ASSUM MP_TAC) THEN SUBST1_TAC x),
    REWRITE_TAC [ALL2, TL],
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC
  ])

  let REMOVE_COL1 ← prove_by_refinement (
    (← q r"!sgns pts p1 p2 ps.
   interpmat pts (CONS p1 (CONS p2 ps)) sgns ==>
   interpmat pts (CONS p1 ps) (MAP (\x. CONS (HD x) (TL (TL x))) sgns)"),
  [
    REWRITE_TAC [interpmat, ALL2_EL],
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [],
    ASM_MESON_TAC [LENGTH_MAP],
    REWRITE_ASSUMS [NOT_EXISTS_THM],
    REPEAT_N 2 (POP_ASSUM MP_TAC),
    POP_ASSUM (MP_TAC o (ISPEC (← q r"i:num"))),
    REWRITE_TAC [DE_MORGAN_THM],
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [],
    REWRITE_ALL [interpsigns],
    CLAIM (← q r"i < LENGTH sgns"),
    ASM_MESON_TAC [],
    STRIP_TAC,
    ASM_SIMP_TAC [EL_MAP],
    REWRITE_ALL [interpsigns],
    CLAIM (← q r"~(EL i sgns = [])"),
    REWRITE_TAC [(← GSYM LENGTH_0)],
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_LENGTH)),
    REWRITE_TAC [LENGTH],
    ARITH_TAC,
    DISCH_THEN (MP_TAC o (MATCH_MP HD_TL)),
    DISCH_THEN (fun x => REPEAT (POP_ASSUM MP_TAC) THEN SUBST1_TAC x),
    REWRITE_TAC [ALL2, TL],
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [HD],
    CLAIM (← q r"~(TL (EL i sgns) = [])"),
    REWRITE_TAC [(← GSYM LENGTH_0)],
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_LENGTH)),
    REWRITE_TAC [LENGTH],
    ARITH_TAC,
    DISCH_THEN (MP_TAC o (MATCH_MP HD_TL)),
    DISCH_THEN (fun x => REPEAT (POP_ASSUM MP_TAC) THEN SUBST1_TAC x),
    REWRITE_TAC [ALL2, TL],
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [HD]
  ])

  let ALL_EL ← prove_by_refinement (
    (← q r"!P l. ALL P l <=> !n. n < LENGTH l ==> P (EL n l)"),
  [
    STRIP_TAC,
    LIST_INDUCT_TAC,
    REWRITE_TAC [ALL, LENGTH],
    ARITH_TAC,
    ASM_REWRITE_TAC [ALL],
    POP_ASSUM (fun _x => ALL_TAC),
    EQ_TAC,
    REPEAT STRIP_TAC,
    CASES_ON (← q r"n = 0"),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    ASM_REWRITE_TAC [EL, HD],
    REWRITE_ASSUMS [LENGTH],
    CLAIM (← q r"PRE n < LENGTH t"),
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC,
    DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (MP_TAC o (← do let c := x; pure (fun th => MATCH_MP th c))))),
    ASM_MESON_TAC [EL_PRE],
    REPEAT STRIP_TAC,
    REWRITE_ASSUMS [LENGTH],
    FIRST_ASSUM (MP_TAC o (ISPEC (← q r"0"))),
    REWRITE_TAC [EL, HD],
    MESON_TAC [LT_0],
    REWRITE_ASSUMS [LENGTH],
    CLAIM (← q r"SUC n < SUC (LENGTH t)"),
    ASM_MESON_TAC [LT_SUC],
    DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (MP_TAC o (← do let c := x; pure (fun th => MATCH_MP th c))))),
    REWRITE_TAC [EL_SUC]
  ])

  let INTERPMAT_POL_LENGTH_LEM ← prove_by_refinement (
    (← q r"!k pols l1 l2. ALL2 (interpsigns pols) l1 l2 /\ (k = LENGTH l2) ==>
    ALL (\x. LENGTH x = LENGTH pols) l2"),
  [
    INDUCT_TAC,
    REPEAT STRIP_TAC,
    CLAIM (← q r"l2 = []"),
    ASM_MESON_TAC [NOT_CONS_NIL, LENGTH_0, ALL2_LENGTH],
    DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_TAC [ALL],
    REPEAT STRIP_TAC,
    CLAIM (← q r"~(l2 = [])"),
    ASM_MESON_TAC [NOT_CONS_NIL, LENGTH_0, ALL2_LENGTH, NOT_SUC],
    REWRITE_TAC [NOT_NIL],
    STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    CLAIM (← q r"~(l1 = [])"),
    ASM_MESON_TAC [NOT_CONS_NIL, LENGTH_0, ALL2_LENGTH, NOT_SUC],
    REWRITE_TAC [NOT_NIL],
    STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [ALL2, ALL, interpsigns],
    STRIP_TAC,
    ASM_MESON_TAC [ALL2_LENGTH],
    FIRST_ASSUM MATCH_MP_TAC,
    EXISTS_TAC (← q r"t'"),
    ASM_REWRITE_TAC [],
    REWRITE_ALL [LENGTH],
    POP_ASSUM MP_TAC THEN ARITH_TAC
  ])

  let INTERPMAT_POL_LENGTH ← prove_by_refinement (
    (← q r"!pts pols sgns. interpmat pts pols sgns ==>
    ALL (\x. LENGTH x = LENGTH pols) sgns"),
  [
    REWRITE_TAC [interpmat],
    MESON_TAC [INTERPMAT_POL_LENGTH_LEM]
  ])

  -- RESTRIP_TAC (work_thms.ml 5537) is a top-level definition (by hand, above)

  let ALL2_BUTLAST ← prove_by_refinement (
    (← q r"!P l1 l2. ALL2 P l1 l2 ==> ALL2 P (BUTLAST l1) (BUTLAST l2)"),
  [
    STRIP_TAC,
    REPEAT LIST_INDUCT_TAC,
    REWRITE_TAC [ALL2, BUTLAST],
    REWRITE_TAC [ALL2, BUTLAST],
    REWRITE_TAC [ALL2, BUTLAST],
    POP_ASSUM (fun _x => ALL_TAC),
    REWRITE_TAC [ALL2, BUTLAST],
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC [NOT_CONS_NIL, ALL2],
    REWRITE_ASSUMS [NOT_NIL],
    POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_TAC [ALL2],
    REWRITE_ASSUMS [NOT_NIL],
    RESTRIP_TAC,
    ASM_MESON_TAC [ALL2],
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [],
    FIRST_ASSUM MATCH_MP_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC
  ])

  let REMOVE_LAST ← prove_by_refinement (
    (← q r"!pts pols sgns .
     interpmat pts pols sgns ==>
     interpmat pts (BUTLAST pols) (MAP BUTLAST sgns)"),
  [
    REWRITE_TAC [interpmat, ALL2_EL],
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [],
    ASM_MESON_TAC [LENGTH_MAP],
    REWRITE_ASSUMS [NOT_EXISTS_THM],
    REPEAT_N 2 (POP_ASSUM MP_TAC),
    POP_ASSUM (MP_TAC o (ISPEC (← q r"i:num"))),
    REWRITE_TAC [DE_MORGAN_THM],
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [],
    REWRITE_ALL [interpsigns],
    CLAIM (← q r"i < LENGTH sgns"),
    ASM_MESON_TAC [],
    STRIP_TAC,
    ASM_SIMP_TAC [EL_MAP],
    ASM_MESON_TAC [ALL2_BUTLAST]
  ])

  let INSERTAT ← new_recursive_definition num_RECURSION
    r"(INSERTAT 0 x l = CONS x l) /\
   (INSERTAT (SUC n) x l = CONS (HD l) (INSERTAT n x (TL l)))"

  let MAP2_EL_LEM ← prove_by_refinement (
    (← q r"!f k l1 l2 i. (LENGTH l1 = LENGTH l2) ==> i < LENGTH l1 ==>
    (k = LENGTH l1) ==>
     (EL i (MAP2 f l1 l2) = f (EL i l1) (EL i l2))"),
  [
    STRIP_TAC,
    INDUCT_TAC,
    REPEAT STRIP_TAC,
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC,
    REPEAT STRIP_TAC,
    CLAIM (← q r"~(l1 = [])"),
    ASM_MESON_TAC [LENGTH_0, NOT_SUC],
    CLAIM (← q r"~(l2 = [])"),
    ASM_MESON_TAC [LENGTH_0, NOT_SUC],
    REWRITE_TAC [NOT_NIL],
    REPEAT STRIP_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_TAC [MAP2],
    REWRITE_ALL [LENGTH, SUC_INJ],
    DISJ_CASES_TAC (← ISPEC (← q r"i:num") num_CASES),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_TAC [EL, HD],
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_TAC [EL, TL],
    REWRITE_ASSUMS [LT_SUC],
    ASM_MESON_TAC []
  ])

  let MAP2_EL ← prove_by_refinement (
    (← q r"!f i l1 l2. (LENGTH l1 = LENGTH l2) ==> i < LENGTH l1 ==>
     (EL i (MAP2 f l1 l2) = f (EL i l1) (EL i l2))"),
  [
    MESON_TAC [MAP2_EL_LEM]
  ])

  let INSERTAT_LENGTH ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"~(SUC n <= 0)")
    prove_by_refinement (
      (← q r"!x n l. n <= LENGTH l ==> (LENGTH (INSERTAT n x l) = SUC (LENGTH l))"),
    [
      STRIP_TAC,
      INDUCT_TAC,
      REWRITE_TAC [INSERTAT, LENGTH],
      REWRITE_TAC [INSERTAT, LENGTH],
      REPEAT STRIP_TAC,
      AP_TERM_TAC,
      CLAIM (← q r"~(l = [])"),
      ASM_MESON_TAC [LENGTH_0, NOT_LE, r1],
      REWRITE_TAC [NOT_NIL],
      STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [LENGTH, TL, LE_SUC],
      ASM_MESON_TAC []
    ])

  -- (by hand)
  let NUM_CASES_TAC : term → tactic ← pure
    (TYPE_TAC (fun x => tactic_of do pure (DISJ_CASES_TAC (← ISPEC x num_CASES))))

  let INSERTAT_TL ← prove_by_refinement (
    (← q r"!x n l. n < LENGTH l ==> (INSERTAT n x (TL l) = TL (INSERTAT (SUC n) x l))"),
  [
    STRIP_TAC,
    INDUCT_TAC,
    REPEAT STRIP_TAC,
    REWRITE_TAC [INSERTAT, TL],
    REPEAT STRIP_TAC,
    CLAIM (← q r"n < LENGTH l \/ (n = LENGTH l)"),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    REWRITE_TAC [INSERTAT, HD, TL],
    REWRITE_TAC [INSERTAT, HD, TL]
  ])

  let INSERTAT_EL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"x < y ==> ~(y = 0)")
    let r2 ← ARITH_RULE (← q r"~(SUC n <= 0)")
    prove_by_refinement (
      (← q r"!n (x:A) i l. n <= LENGTH l ==> i <= LENGTH l ==>
     ((i < n ==> (EL i (INSERTAT n x l) = EL i l)) /\
     ((i = n) ==> (EL i (INSERTAT n x l) = x)) /\
     (i > n ==> (EL i (INSERTAT n x l) = EL (PRE i) l)))"),
    [
      INDUCT_TAC,
      REPEAT STRIP_TAC,
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      ASM_REWRITE_TAC [INSERTAT, EL, HD],
      ASM_REWRITE_TAC [INSERTAT, EL, HD],
      DISJ_CASES_TAC (← ISPEC (← q r"i:num") num_CASES),
      EVERY_ASSUM MP_TAC THEN ARITH_TAC,
      POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [EL, TL, PRE],
      REPEAT_N 5 STRIP_TAC,
      CLAIM (← q r"~(l = [])"),
      ASM_MESON_TAC [LENGTH_0, NOT_LE, r2],
      STRIP_TAC,
      CLAIM (← q r"n <= LENGTH (TL l)"),
      ASM_SIMP_TAC [LENGTH_TL],
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      REPEAT STRIP_TAC,
      REWRITE_TAC [INSERTAT],
      NUM_CASES_TAC (← q r"i"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [EL, HD],
      POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [EL, TL],
      CLAIM (← q r"n' <= LENGTH (TL l)"),
      REWRITE_ASSUMS [LT_SUC],
      ASM_MESON_TAC [LTE_TRANS, LT_TRANS, LET_TRANS, LT_IMP_LE],
      STRIP_TAC,
      REWRITE_ASSUMS [LT_SUC],
      ASM_MESON_TAC [],
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [EL, INSERTAT, TL],
      ASM_MESON_TAC [],
      REWRITE_TAC [INSERTAT],
      NUM_CASES_TAC (← q r"i"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [EL, HD, PRE],
      POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [EL, TL, PRE],
      CLAIM (← q r"n' <= LENGTH (TL l)"),
      ASM_SIMP_TAC [LENGTH_TL],
      REPEAT_N 3 (POP_ASSUM (fun _x => ALL_TAC)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      REWRITE_ASSUMS [GT, LT_SUC],
      FIRST_X_ASSUM (MP_TAC o (ISPECL [(← q r"x:A"), (← q r"n':num"), (← q r"TL l:A list")])),
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      NUM_CASES_TAC (← q r"n'"),
      ASM_MESON_TAC [r1],
      POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_TAC [PRE, EL]
    ])

  -- USE_X_ASSUM (work_thms.ml 5747) is a top-level definition (by hand, above)

  let MATINSERT_THM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"x <= y /\ z < x ==> z < (y:num)")
    let r2 ← ARITH_RULE (← q r"i' < n \/ (i' = n) \/ i' > (n:num)")
    prove_by_refinement (
      (← q r"!pts p pols n psgns sgns.
       interpmat pts pols sgns ==>
       ALL2 (\x y. interpsign x p y) (partition_line pts) psgns ==>
       n <= LENGTH pols ==>
        interpmat pts (INSERTAT n p pols) (MAP2 (INSERTAT n) psgns sgns)"),
    [
      REWRITE_TAC [interpmat, ALL2_EL, NOT_EXISTS_THM, DE_MORGAN_THM],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      ASM_REWRITE_TAC [],
      CLAIM (← q r"LENGTH (psgns:sign list) = LENGTH sgns"),
      ASM_MESON_TAC [LENGTH_MAP2],
      ASM_MESON_TAC [LENGTH_MAP2],
      DISJ_LCASE,
      REWRITE_ASSUMS [],
      REWRITE_ALL [interpsigns],
      CLAIM (← q r"LENGTH psgns = LENGTH sgns"),
      ASM_MESON_TAC [],
      STRIP_TAC,
      CLAIM (← q r"i < LENGTH psgns"),
      ASM_MESON_TAC [],
      STRIP_TAC,
      ASM_SIMP_TAC [MAP2_EL],
      REWRITE_TAC [ALL2_EL],
      REWRITE_TAC [NOT_EXISTS_THM, DE_MORGAN_THM],
      REPEAT STRIP_TAC,
      ASM_SIMP_TAC [INSERTAT_LENGTH],
      CLAIM (← q r"LENGTH (EL i (sgns:(sign list) list)) = LENGTH pols"),
      ASM_MESON_TAC [ALL2_LENGTH],
      STRIP_TAC,
      ASM_SIMP_TAC [INSERTAT_LENGTH],
      DISJ_LCASE,
      REWRITE_ASSUMS [],
      MP_TAC r2,
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (EL i sgns) = LENGTH pols"),
      ASM_MESON_TAC [ALL2_LENGTH],
      STRIP_TAC,
      CLAIM (← q r"n <= LENGTH (EL i sgns)"),
      ASM_MESON_TAC [],
      STRIP_TAC,
      CLAIM (← q r"i' <= LENGTH (EL i sgns)"),
      ASM_MESON_TAC [LTE_TRANS, LET_TRANS, LT_TRANS, LT_IMP_LE],
      STRIP_TAC,
      ASM_SIMP_TAC [INSERTAT_EL],
      CLAIM (← q r"i' <= LENGTH pols"),
      ASM_MESON_TAC [LTE_TRANS, LET_TRANS, LT_TRANS, LT_IMP_LE],
      STRIP_TAC,
      ASM_SIMP_TAC [INSERTAT_EL],
      REPEAT_N 12 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"i:num"))),
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [],
      LABEL_ALL_TAC,
      USE_THEN "Z-12" MP_TAC,
      REWRITE_TAC [ALL2_EL],
      REWRITE_TAC [NOT_EXISTS_THM, DE_MORGAN_THM],
      STRIP_TAC,
      POP_ASSUM (MP_TAC o (ISPEC (← q r"i':num"))),
      POP_ASSUM (fun _x => ALL_TAC),
      ASM_REWRITE_TAC [],
      POP_ASSUM (fun _x => ALL_TAC),
      STRIP_TAC,
      ASM_MESON_TAC [r1],
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      CLAIM (← q r"LENGTH (EL i sgns) = LENGTH pols"),
      ASM_MESON_TAC [ALL2_LENGTH],
      STRIP_TAC,
      CLAIM (← q r"n <= LENGTH (EL i sgns)"),
      ASM_MESON_TAC [],
      STRIP_TAC,
      ASM_SIMP_TAC [INSERTAT_EL],
      ASM_MESON_TAC [ALL2_EL],
      CLAIM (← q r"LENGTH (EL i sgns) = LENGTH pols"),
      ASM_MESON_TAC [ALL2_LENGTH],
      STRIP_TAC,
      CLAIM (← q r"n <= LENGTH (EL i sgns)"),
      ASM_MESON_TAC [],
      STRIP_TAC,
      CLAIM (← q r"i' <= LENGTH (EL i sgns)"),
      ASM_REWRITE_TAC [],
      LABEL_ALL_TAC,
      USE_THEN "Z-7" (MP_TAC o (MATCH_MP INSERTAT_LENGTH)),
      TYPE_TAC (fun x => DISCH_THEN (MP_TAC o (ISPEC x))) (← q r"p"),
      USE_THEN "Z-3" MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      CLAIM (← q r"i' <= LENGTH pols"),
      ASM_MESON_TAC [],
      STRIP_TAC,
      ASM_SIMP_TAC [INSERTAT_EL],
      LABEL_ALL_TAC,
      USE_X_ASSUM "Z-12" (MP_TAC o (ISPEC (← q r"i:num"))),
      ASM_REWRITE_TAC [],
      REWRITE_TAC [ALL2_EL],
      ASM_REWRITE_TAC [NOT_EXISTS_THM, DE_MORGAN_THM],
      DISCH_THEN (MP_TAC o (ISPEC (← q r"PRE i':num"))),
      STRIP_TAC,
      CLAIM (← q r"~(i' = 0)"),
      USE_THEN "Z-4" MP_TAC THEN ARITH_TAC,
      POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC
    ])

  let INTERP_CONST_POS ← prove_by_refinement (
    (← q r"!c l. c > &0 ==>
    ALL2 (\x y. interpsign x (\x. c) y) l (REPLICATE (LENGTH l) Pos)"),
  [
    REWRITE_TAC [real_gt],
    STRIP_TAC,
    LIST_INDUCT_TAC,
    REWRITE_TAC [REPLICATE, LENGTH, ALL2],
    DISCH_THEN (fun x => REWRITE_ASSUMS [x] THEN ASSUME_TAC x),
    REWRITE_TAC [REPLICATE, LENGTH, ALL2, interpsign, real_gt],
    ASM_MESON_TAC [REPLICATE, LENGTH, ALL2, interpsign, real_gt]
  ])

  let INTERP_CONST_NEG ← prove_by_refinement (
    (← q r"!c l. c < &0 ==>
    ALL2 (\x y. interpsign x (\x. c) y) l (REPLICATE (LENGTH l) Neg)"),
  [
    STRIP_TAC,
    LIST_INDUCT_TAC,
    REWRITE_TAC [REPLICATE, LENGTH, ALL2],
    DISCH_THEN (fun x => REWRITE_ASSUMS [x] THEN ASSUME_TAC x),
    REWRITE_TAC [REPLICATE, LENGTH, ALL2, interpsign, real_gt],
    ASM_MESON_TAC []
  ])

  let INTERP_CONST_ZERO ← prove_by_refinement (
    (← q r"!c l. (c = &0) ==>
    ALL2 (\x y. interpsign x (\x. c) y) l (REPLICATE (LENGTH l) Zero)"),
  [
    STRIP_TAC,
    LIST_INDUCT_TAC,
    REWRITE_TAC [REPLICATE, LENGTH, ALL2],
    DISCH_THEN (fun x => REWRITE_ASSUMS [x] THEN ASSUME_TAC x),
    REWRITE_TAC [REPLICATE, LENGTH, ALL2, interpsign, real_gt],
    ASM_REWRITE_TAC []
  ])

  -- QUANT_CONV (work_thms.ml 5905) is a top-level definition (by hand, above)

  -- PATH_CONV2 (work_thms.ml 5907) is a top-level definition (by hand, above)

  let EL_REPLICATE ← prove_by_refinement (
    (← q r"!n x i. i < n ==> (EL i (REPLICATE n x) = x)"),
  [
    INDUCT_TAC,
    ARITH_TAC,
    REPEAT STRIP_TAC,
    REWRITE_TAC [REPLICATE],
    NUM_CASES_TAC (← q r"i"),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_TAC [EL, HD],
    POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_TAC [EL, TL],
    ASM_MESON_TAC [LT_SUC]
  ])

  let ALL2_UNKNOWN ← prove_by_refinement (
    (← q r"!p pts. ALL2 (\x y. interpsign x p y) (partition_line pts)
    (REPLICATE (LENGTH (partition_line pts)) Unknown)"),
  [
    REWRITE_TAC [ALL2_EL],
    REWRITE_TAC [NOT_EXISTS_THM, DE_MORGAN_THM],
    REPEAT STRIP_TAC,
    ASM_MESON_TAC [LENGTH_REPLICATE],
    DISJ_LCASE,
    REWRITE_ASSUMS [],
    ASM_SIMP_TAC [EL_REPLICATE],
    REWRITE_TAC [interpsign]
  ])

  let MATINSERT_THM2 ← prove_by_refinement (
    (← q r"!pts p pols n psgns sgns.
    ALL2 (\x y. interpsign x p y) (partition_line pts) psgns ==>
    n <= LENGTH pols ==>
    interpmat pts pols sgns ==>
     interpmat pts (INSERTAT n p pols) (MAP2 (INSERTAT n) psgns sgns)"),
  [
    MESON_TAC [MATINSERT_THM]
  ])

  -- (by hand)
  let FUN_EQ_TAC : tactic ← do pure (MATCH_EQ_MP_TAC (← GSYM FUN_EQ_THM))

  let INSERTAT_0 ← prove_by_refinement (
    (← q r"INSERTAT 0 = CONS"),
  [
    FUN_EQ_TAC,
    STRIP_TAC,
    FUN_EQ_TAC,
    REWRITE_TAC [INSERTAT]
  ])

  let INFERPSIGN_MATINSERT_THM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"0 <= x")
    prove_by_refinement (
      (← q r"!pts p pols sgns.
      interpmat pts pols sgns ==>
       interpmat pts (CONS p pols)
        (MAP2 CONS
          (REPLICATE (2 * LENGTH pts + 1) Unknown) sgns)"),
    [
      REPEAT STRIP_TAC,
      TYPE_TACL (fun l => tactic_of do pure (MP_TAC (← ISPECL l MATINSERT_THM))) [(← q r"pts"), (← q r"p"), (← q r"pols"), (← q r"0"), (← q r"REPLICATE (LENGTH (partition_line pts)) Unknown"), (← q r"sgns")],
      ASM_REWRITE_TAC [ALL2_UNKNOWN, r1, INSERTAT, PARTITION_LINE_LENGTH],
      MESON_TAC [INSERTAT_0]
    ])

  let INFERPSIGN_POS ← prove_by_refinement (
    (← q r"!p ps q qs r rs s x pts1 pts2  s1 s2 s3 rest sgns.
  interpmat (APPEND pts1 (CONS x pts2))
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns
      (CONS (APPEND (CONS Unknown s1)
        (APPEND (CONS Zero s2) (CONS Pos s3))) rest)) ==>
  (LENGTH ps = LENGTH s1) ==>
  (LENGTH qs = LENGTH s2) ==>
  ODD (LENGTH sgns) ==>
  (LENGTH sgns = 2 * LENGTH pts1 + 1) ==>
  (!x. p x = s x * q x + r x) ==>
  interpmat (APPEND pts1 (CONS x pts2))
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns
      (CONS (APPEND (CONS Pos s1)
        (APPEND (CONS Zero s2) (CONS Pos s3))) rest))"),
  [
    REWRITE_TAC [interpmat],
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    CASES_ON (← q r"pts1 = []"),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [APPEND, partition_line],
    COND_CASES_TAC,
    CLAIM (← q r"?k. sgns = [k]"),
    MATCH_EQ_MP_TAC (← GSYM LENGTH_1),
    REWRITE_ALL [LENGTH],
    POP_ASSUM (fun _x => ALL_TAC),
    POP_ASSUM (fun _x => ALL_TAC),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [APPEND, partition_line, ALL2],
    REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [],
    REWRITE_ALL [interpsigns, interpsign, ALL2],
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    REPEAT_N 5 (POP_ASSUM MP_TAC),
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    REWRITE_TAC [ALL2, interpsign],
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [],
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    REWRITE_TAC [ALL2, interpsign],
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [],
    CLAIM (← q r"q x = &0"),
    ASM_MESON_TAC [],
    DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
    POP_ASSUM (fun _x => ALL_TAC),
    REWRITE_TAC [REAL_MUL_RZERO, REAL_ADD_LID],
    FIRST_ASSUM MATCH_MP_TAC,
    REWRITE_TAC [],
    ASM_REWRITE_TAC [],
    CLAIM (← q r"?k. sgns = [k]"),
    MATCH_EQ_MP_TAC (← GSYM LENGTH_1),
    REWRITE_ALL [LENGTH],
    POP_ASSUM (fun _x => ALL_TAC),
    POP_ASSUM (fun _x => ALL_TAC),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    POP_ASSUM (fun x => REWRITE_ASSUMS [x] THEN ASSUME_TAC x),
    REWRITE_ALL [APPEND, partition_line, ALL2],
    REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [],
    REWRITE_ALL [interpsigns, interpsign, ALL2],
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    REPEAT_N 6 (POP_ASSUM MP_TAC),
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    REWRITE_TAC [ALL2, interpsign],
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [],
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    REWRITE_TAC [ALL2, interpsign],
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [],
    CLAIM (← q r"q x = &0"),
    ASM_MESON_TAC [],
    DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
    POP_ASSUM (fun _x => ALL_TAC),
    REWRITE_TAC [REAL_MUL_RZERO, REAL_ADD_LID],
    FIRST_ASSUM MATCH_MP_TAC,
    REWRITE_TAC [],
    ASM_REWRITE_TAC [],
    POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
    ASM_SIMP_TAC [PARTITION_LINE_APPEND],
    REPEAT STRIP_TAC,
    CLAIM (← q r"(APPEND (BUTLAST (partition_line pts1))
     (CONS (\x'. LAST pts1 < x' /\ x' < x)
     (TL (partition_line (CONS x pts2))))) =
     (APPEND
      (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x])
     (TL (partition_line (CONS x pts2))))"),
    ASM_MESON_TAC [APPEND_CONS],
    DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
    REPEAT (POP_ASSUM MP_TAC),
    REWRITE_ALL [partition_line],
    COND_CASES_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REPEAT STRIP_TAC,
    REWRITE_ALL [TL],
    CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns"),
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_LENGTH)),
    ASM_SIMP_TAC [LENGTH_APPEND, PARTITION_LINE_NOT_NIL, BUTLAST_LENGTH, PARTITION_LINE_LENGTH, LENGTH],
    ARITH_TAC,
    STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    REPEAT STRIP_TAC,
    MATCH_MP_TAC ALL2_APPEND,
    ASM_REWRITE_TAC [],
    REPEAT_N 6 (POP_ASSUM MP_TAC),
    POP_ASSUM (fun x => POP_ASSUM (fun y => REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y)),
    REWRITE_ALL [ALL2, interpsigns, APPEND, interpsign],
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    RESTRIP_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    REWRITE_TAC [ALL2, interpsign],
    REPEAT STRIP_TAC,
    REWRITE_ALL [interpsigns, ALL2, interpsign],
    REPEAT_N 4 (POP_ASSUM MP_TAC),
    POP_ASSUM (fun x => REPEAT STRIP_TAC THEN ASSUME_TAC x),
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    REWRITE_TAC [ALL2, interpsign],
    REPEAT STRIP_TAC,
    REWRITE_ALL [interpsigns, ALL2, interpsign],
    ASM_REWRITE_TAC [],
    CLAIM (← q r"q x = &0"),
    ASM_MESON_TAC [],
    DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
    POP_ASSUM (fun _x => ALL_TAC),
    REWRITE_TAC [REAL_MUL_RZERO, REAL_ADD_LID],
    FIRST_ASSUM MATCH_MP_TAC,
    REWRITE_TAC [],
    REPEAT STRIP_TAC,
    CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns"),
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_LENGTH)),
    ASM_SIMP_TAC [LENGTH_APPEND, PARTITION_LINE_NOT_NIL, BUTLAST_LENGTH, PARTITION_LINE_LENGTH, LENGTH],
    ARITH_TAC,
    STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    REPEAT STRIP_TAC,
    MATCH_MP_TAC ALL2_APPEND,
    ASM_REWRITE_TAC [],
    REWRITE_ALL [TL, ALL2, interpsign, interpsigns, APPEND],
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    REPEAT_N 7 (POP_ASSUM MP_TAC),
    POP_ASSUM (fun x => POP_ASSUM (fun y => REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y)),
    REWRITE_ALL [ALL2, interpsigns, APPEND, interpsign],
    ASM_REWRITE_TAC [],
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    REWRITE_TAC [ALL2, interpsign],
    REPEAT STRIP_TAC,
    REWRITE_ALL [interpsigns, ALL2, interpsign],
    REPEAT_N 4 (POP_ASSUM MP_TAC),
    POP_ASSUM (fun x => REPEAT STRIP_TAC THEN ASSUME_TAC x),
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    REWRITE_TAC [ALL2, interpsign],
    REPEAT STRIP_TAC,
    REWRITE_ALL [interpsigns, ALL2, interpsign],
    ASM_REWRITE_TAC [],
    CLAIM (← q r"q x = &0"),
    ASM_MESON_TAC [],
    DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
    POP_ASSUM (fun _x => ALL_TAC),
    REWRITE_TAC [REAL_MUL_RZERO, REAL_ADD_LID],
    FIRST_ASSUM MATCH_MP_TAC,
    REWRITE_TAC []
  ])

  -- @@RETURN BEGIN
  return { ALL2_EL_LEM, ALL2_EL, EL_MAP, REMOVE_HD_COL, REMOVE_COL1, ALL_EL,
           INTERPMAT_POL_LENGTH_LEM, INTERPMAT_POL_LENGTH, ALL2_BUTLAST, REMOVE_LAST,
           INSERTAT, MAP2_EL_LEM, MAP2_EL, INSERTAT_LENGTH, NUM_CASES_TAC, INSERTAT_TL,
           INSERTAT_EL, MATINSERT_THM, INTERP_CONST_POS, INTERP_CONST_NEG,
           INTERP_CONST_ZERO, EL_REPLICATE, ALL2_UNKNOWN, MATINSERT_THM2, FUN_EQ_TAC,
           INSERTAT_0, INFERPSIGN_MATINSERT_THM, INFERPSIGN_POS }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- work_thms.ml phrases from line 6189 to 7000; the theorems              -/
/- converted by gxwork/rq/ml2lean.py (disclosed; comments in the          -/
/- proofs are not carried over), the functions by hand.                   -/
/- ---------------------------------------------------------------------- -/

structure WorkThms08 where
  -- @@FIELDS
  INFERPSIGN_NEG : thm
  INFERPSIGN_POS_EVEN_LEM : thm
  SPLIT_LIST_THM : thm
  EXISTS_TACL : List term → tactic
  DIV_EVEN : thm
  PRE_LEM : thm
  EVEN_PRE : thm
  ODD_PRE : thm
  INFERPSIGN_POS_EVEN : thm
  INFERPSIGN_NEG_EVEN_LEM : thm
  INFERPSIGN_NEG_EVEN : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupWorkThms08 [HolBase] (D : WorkThmsDeps) (BWorkThms01 : WorkThms01) (BWorkThms02 : WorkThms02) :
    ExceptT String IO WorkThms08 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_SIMP_TAC, ARITH_TAC, ASM_MESON_TAC, CASES_ON, CLAIM,
        EXISTS_TAC, INDUCT_TAC, REAL_ARITH, TYPE_TAC, TYPE_TACL, prove_by_refinement, .. } := D
  let { ALL2, APPEND, APPEND_NIL, DIVISION, EVEN_MOD, EVEN_ODD_POW, HD, IMP_AND_THM,
        LENGTH, LENGTH_0, LENGTH_1, LENGTH_APPEND, NOT_NIL, NOT_ODD, ODD, PRE,
        REAL_ADD_LID, REAL_MUL_GT, REAL_MUL_LT, REAL_MUL_RZERO, TL, interpmat,
        interpsign, interpsigns, partition_line, real_gt, .. } := D.core1
  let { ALL2_APPEND, ALL2_APPEND_LENGTH, ALL2_LENGTH, APPEND_CONS, BUTLAST_LENGTH,
        PARTITION_LINE_APPEND, PARTITION_LINE_LENGTH, PARTITION_LINE_NOT_NIL, .. } := BWorkThms01
  let { APPEND_APPEND, .. } := BWorkThms02
  -- @@SCOPE END

  let INFERPSIGN_NEG ← prove_by_refinement (
    (← q r"!p ps q qs r rs s x pts1 pts2  s1 s2 s3 rest sgns.
  interpmat (APPEND pts1 (CONS x pts2))
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns
      (CONS (APPEND (CONS Unknown s1)
        (APPEND (CONS Zero s2) (CONS Neg s3))) rest)) ==>
  (LENGTH ps = LENGTH s1) ==>
  (LENGTH qs = LENGTH s2) ==>
  ODD (LENGTH sgns) ==>
  (LENGTH sgns = 2 * LENGTH pts1 + 1) ==>
  (!x. p x = s x * q x + r x) ==>
  interpmat (APPEND pts1 (CONS x pts2))
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns
      (CONS (APPEND (CONS Neg s1)
        (APPEND (CONS Zero s2) (CONS Neg s3))) rest))"),
  [
    REWRITE_TAC [interpmat],
    REPEAT STRIP_TAC,
    FIRST_ASSUM MATCH_ACCEPT_TAC,
    CASES_ON (← q r"pts1 = []"),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [APPEND, partition_line],
    COND_CASES_TAC,
    CLAIM (← q r"?k. sgns = [k]"),
    MATCH_EQ_MP_TAC (← GSYM LENGTH_1),
    REWRITE_ALL [LENGTH],
    POP_ASSUM (fun _x => ALL_TAC),
    POP_ASSUM (fun _x => ALL_TAC),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REWRITE_ALL [APPEND, partition_line, ALL2],
    REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [],
    REWRITE_ALL [interpsigns, interpsign, ALL2],
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    REPEAT_N 5 (POP_ASSUM MP_TAC),
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    REWRITE_TAC [ALL2, interpsign],
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [],
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    REWRITE_TAC [ALL2, interpsign],
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [],
    CLAIM (← q r"q x = &0"),
    ASM_MESON_TAC [],
    DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
    POP_ASSUM (fun _x => ALL_TAC),
    REWRITE_TAC [REAL_MUL_RZERO, REAL_ADD_LID],
    FIRST_ASSUM MATCH_MP_TAC,
    REWRITE_TAC [],
    ASM_REWRITE_TAC [],
    CLAIM (← q r"?k. sgns = [k]"),
    MATCH_EQ_MP_TAC (← GSYM LENGTH_1),
    REWRITE_ALL [LENGTH],
    POP_ASSUM (fun _x => ALL_TAC),
    POP_ASSUM (fun _x => ALL_TAC),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    STRIP_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    POP_ASSUM (fun x => REWRITE_ASSUMS [x] THEN ASSUME_TAC x),
    REWRITE_ALL [APPEND, partition_line, ALL2],
    REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [],
    REWRITE_ALL [interpsigns, interpsign, ALL2],
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    REPEAT_N 6 (POP_ASSUM MP_TAC),
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    REWRITE_TAC [ALL2, interpsign],
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [],
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    REWRITE_TAC [ALL2, interpsign],
    REPEAT STRIP_TAC,
    ASM_REWRITE_TAC [],
    CLAIM (← q r"q x = &0"),
    ASM_MESON_TAC [],
    DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
    POP_ASSUM (fun _x => ALL_TAC),
    REWRITE_TAC [REAL_MUL_RZERO, REAL_ADD_LID],
    FIRST_ASSUM MATCH_MP_TAC,
    REWRITE_TAC [],
    ASM_REWRITE_TAC [],
    POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
    ASM_SIMP_TAC [PARTITION_LINE_APPEND],
    REPEAT STRIP_TAC,
    CLAIM (← q r"(APPEND (BUTLAST (partition_line pts1))
     (CONS (\x'. LAST pts1 < x' /\ x' < x)
     (TL (partition_line (CONS x pts2))))) =
     (APPEND
      (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x])
     (TL (partition_line (CONS x pts2))))"),
    ASM_MESON_TAC [APPEND_CONS],
    DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
    REPEAT (POP_ASSUM MP_TAC),
    REWRITE_ALL [partition_line],
    COND_CASES_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    REPEAT STRIP_TAC,
    REWRITE_ALL [TL],
    CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns"),
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_LENGTH)),
    ASM_SIMP_TAC [LENGTH_APPEND, PARTITION_LINE_NOT_NIL, BUTLAST_LENGTH, PARTITION_LINE_LENGTH, LENGTH],
    ARITH_TAC,
    STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    REPEAT STRIP_TAC,
    MATCH_MP_TAC ALL2_APPEND,
    ASM_REWRITE_TAC [],
    REPEAT_N 6 (POP_ASSUM MP_TAC),
    POP_ASSUM (fun x => POP_ASSUM (fun y => REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y)),
    REWRITE_ALL [ALL2, interpsigns, APPEND, interpsign],
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    RESTRIP_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    REWRITE_TAC [ALL2, interpsign],
    REPEAT STRIP_TAC,
    REWRITE_ALL [interpsigns, ALL2, interpsign],
    REPEAT_N 4 (POP_ASSUM MP_TAC),
    POP_ASSUM (fun x => REPEAT STRIP_TAC THEN ASSUME_TAC x),
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    REWRITE_TAC [ALL2, interpsign],
    REPEAT STRIP_TAC,
    REWRITE_ALL [interpsigns, ALL2, interpsign],
    ASM_REWRITE_TAC [],
    CLAIM (← q r"q x = &0"),
    ASM_MESON_TAC [],
    DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
    POP_ASSUM (fun _x => ALL_TAC),
    REWRITE_TAC [REAL_MUL_RZERO, REAL_ADD_LID],
    FIRST_ASSUM MATCH_MP_TAC,
    REWRITE_TAC [],
    REPEAT STRIP_TAC,
    CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns"),
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_LENGTH)),
    ASM_SIMP_TAC [LENGTH_APPEND, PARTITION_LINE_NOT_NIL, BUTLAST_LENGTH, PARTITION_LINE_LENGTH, LENGTH],
    ARITH_TAC,
    STRIP_TAC,
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    REPEAT STRIP_TAC,
    MATCH_MP_TAC ALL2_APPEND,
    ASM_REWRITE_TAC [],
    REWRITE_ALL [TL, ALL2, interpsign, interpsigns, APPEND],
    ASM_REWRITE_TAC [],
    REPEAT STRIP_TAC,
    REPEAT_N 7 (POP_ASSUM MP_TAC),
    POP_ASSUM (fun x => POP_ASSUM (fun y => REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y)),
    REWRITE_ALL [ALL2, interpsigns, APPEND, interpsign],
    ASM_REWRITE_TAC [],
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    REWRITE_TAC [ALL2, interpsign],
    REPEAT STRIP_TAC,
    REWRITE_ALL [interpsigns, ALL2, interpsign],
    REPEAT_N 4 (POP_ASSUM MP_TAC),
    POP_ASSUM (fun x => REPEAT STRIP_TAC THEN ASSUME_TAC x),
    FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
    FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    REWRITE_TAC [ALL2, interpsign],
    REPEAT STRIP_TAC,
    REWRITE_ALL [interpsigns, ALL2, interpsign],
    ASM_REWRITE_TAC [],
    CLAIM (← q r"q x = &0"),
    ASM_MESON_TAC [],
    DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
    POP_ASSUM (fun _x => ALL_TAC),
    REWRITE_TAC [REAL_MUL_RZERO, REAL_ADD_LID],
    FIRST_ASSUM MATCH_MP_TAC,
    REWRITE_TAC []
  ])

  let INFERPSIGN_POS_EVEN_LEM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    let r2 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    let r3 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    let r4 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    prove_by_refinement (
      (← q r"!a n p ps q qs r rs s x pts1 pts2  s1 s2 s3 rest sgns.
    interpmat (APPEND pts1 (CONS x pts2))
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Unknown s1)
          (APPEND (CONS Zero s2) (CONS Pos s3))) rest)) ==>
    (LENGTH ps = LENGTH s1) ==>
    (LENGTH qs = LENGTH s2) ==>
    ODD (LENGTH sgns) ==>
    (LENGTH sgns = 2 * LENGTH pts1 + 1) ==>
    (!x. a pow n * p x = s x * q x + r x) ==>
    (a <> &0) ==>
    EVEN n ==>
    interpmat (APPEND pts1 (CONS x pts2))
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Pos s1)
          (APPEND (CONS Zero s2) (CONS Pos s3))) rest))"),
    [
      REPEAT STRIP_TAC,
      CLAIM (← q r"a pow n > &0"),
      ASM_MESON_TAC [EVEN_ODD_POW],
      STRIP_TAC,
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      FIRST_ASSUM MATCH_ACCEPT_TAC,
      CASES_ON (← q r"pts1 = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, partition_line],
      COND_CASES_TAC,
      CLAIM (← q r"?k. sgns = [k]"),
      MATCH_EQ_MP_TAC (← GSYM LENGTH_1),
      REWRITE_ALL [LENGTH],
      REPEAT_N 5 (POP_ASSUM (fun _x => ALL_TAC)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, partition_line, ALL2],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, interpsign, ALL2],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      REPEAT_N 8 (POP_ASSUM MP_TAC),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x > &0"),
      ASM_MESON_TAC [],
      REPEAT_N 6 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 7 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r4],
      ASM_REWRITE_TAC [],
      POP_ASSUM (fun x => REWRITE_ASSUMS [x] THEN ASSUME_TAC x),
      CLAIM (← q r"?k. sgns = [k]"),
      MATCH_EQ_MP_TAC (← GSYM LENGTH_1),
      REWRITE_ALL [LENGTH],
      REPEAT_N 5 (POP_ASSUM (fun _x => ALL_TAC)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, partition_line, ALL2],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, interpsign, ALL2],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      REPEAT_N 9 (POP_ASSUM MP_TAC),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x > &0"),
      ASM_MESON_TAC [],
      REPEAT_N 8 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 9 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r3],
      ASM_REWRITE_TAC [],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND],
      REPEAT STRIP_TAC,
      CLAIM (← q r"(APPEND (BUTLAST (partition_line pts1))
       (CONS (\x'. LAST pts1 < x' /\ x' < x)
       (TL (partition_line (CONS x pts2))))) =
       (APPEND
        (APPEND (BUTLAST (partition_line pts1))
        [\x'. LAST pts1 < x' /\ x' < x])
       (TL (partition_line (CONS x pts2))))"),
      ASM_MESON_TAC [APPEND_CONS],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_ALL [partition_line],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      REWRITE_ALL [TL],
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts1))
        [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns"),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_LENGTH)),
      ASM_SIMP_TAC [LENGTH_APPEND, PARTITION_LINE_NOT_NIL, BUTLAST_LENGTH, PARTITION_LINE_LENGTH, LENGTH],
      ARITH_TAC,
      STRIP_TAC,
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REPEAT_N 9 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => POP_ASSUM (fun y => REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y)),
      REWRITE_ALL [ALL2, interpsigns, APPEND, interpsign],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      RESTRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      REPEAT_N 4 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => REPEAT STRIP_TAC THEN ASSUME_TAC x),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      ASM_REWRITE_TAC [],
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x > &0"),
      ASM_MESON_TAC [],
      REPEAT_N 15 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 16 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r2],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts1))
        [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns"),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_LENGTH)),
      ASM_SIMP_TAC [LENGTH_APPEND, PARTITION_LINE_NOT_NIL, BUTLAST_LENGTH, PARTITION_LINE_LENGTH, LENGTH],
      ARITH_TAC,
      STRIP_TAC,
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [TL, ALL2, interpsign, interpsigns, APPEND],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      REPEAT_N 10 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => POP_ASSUM (fun y => REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y)),
      REWRITE_ALL [ALL2, interpsigns, APPEND, interpsign],
      ASM_REWRITE_TAC [],
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      REPEAT_N 4 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => REPEAT STRIP_TAC THEN ASSUME_TAC x),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      ASM_REWRITE_TAC [],
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x > &0"),
      ASM_MESON_TAC [],
      REPEAT_N 16 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 17 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r1]
    ])

  let SPLIT_LIST_THM ← prove_by_refinement (
    (← q r"!n (l:A list). n < LENGTH l ==>
    ?l1 l2. (l = APPEND l1 l2) /\ (LENGTH l1 = n)"),
  [
    INDUCT_TAC,
    REPEAT STRIP_TAC,
    EXISTS_TAC (← q r"[]:A list"),
    EXISTS_TAC (← q r"l"),
    REWRITE_TAC [APPEND, LENGTH],
    REPEAT STRIP_TAC,
    CLAIM (← q r"n < LENGTH l"),
    POP_ASSUM MP_TAC THEN ARITH_TAC,
    DISCH_THEN (fun x => tactic_of do pure (FIRST_ASSUM (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
    STRIP_TAC,
    EXISTS_TAC (← q r"APPEND l1 [HD l2]"),
    EXISTS_TAC (← q r"TL (l2:A list)"),
    CLAIM (← q r"~((l2:A list) = [])"),
    REWRITE_TAC [(← GSYM LENGTH_0)],
    STRIP_TAC,
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC,
    POP_ASSUM (MP_TAC o (AP_TERM (← q r"LENGTH:A list -> num"))),
    REWRITE_TAC [LENGTH_APPEND],
    REPEAT STRIP_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC,
    REWRITE_TAC [NOT_NIL],
    STRIP_TAC,
    POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
    ASM_REWRITE_TAC [TL, HD, LENGTH_APPEND, LENGTH],
    STRIP_TAC,
    REWRITE_TAC [APPEND_APPEND, APPEND],
    ARITH_TAC
  ])

  -- `let rec EXISTS_TACL = (fun l -> ..)` (by hand; EXISTS_TACL.go)
  let EXISTS_TACL : List term → tactic ← pure (EXISTS_TACL.go TYPE_TAC EXISTS_TAC)

  let DIV_EVEN ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"x * y = y * x:num")
    let r2 ← ARITH_RULE (← q r"x + 0 = x")
    prove_by_refinement (
      (← q r"!x. EVEN x ==> (2 * x DIV 2 = x)"),
    [
      REPEAT STRIP_TAC,
      TYPE_TACL (fun l => tactic_of do pure (MP_TAC (← ISPECL l DIVISION))) [(← q r"x"), (← q r"2")],
      ARITH_SIMP_TAC [],
      REWRITE_ASSUMS [EVEN_MOD],
      ASM_REWRITE_TAC [],
      ARITH_SIMP_TAC [],
      STRIP_TAC,
      REWRITE_ASSUMS [r2],
      ONCE_REWRITE_ASSUMS [r1],
      ASM_MESON_TAC []
    ])

  let PRE_LEM ← prove_by_refinement (
    (← q r"!n. (ODD n ==> EVEN (PRE n)) /\
       (~(n = 0) ==> (EVEN n ==> ODD (PRE n)))"),
  [
    INDUCT_TAC,
    ARITH_TAC,
    POP_ASSUM MP_TAC THEN STRIP_TAC,
    REPEAT STRIP_TAC,
    REWRITE_TAC [PRE],
    ASM_MESON_TAC [ODD, NOT_ODD],
    ASM_MESON_TAC [ODD, PRE, NOT_ODD]
  ])

  let EVEN_PRE ← GEN_ALL (← CONJUNCT1 (← SPEC_ALL PRE_LEM))

  let ODD_PRE ← GEN_ALL (← CONJUNCT2 (← SPEC_ALL PRE_LEM))

  let INFERPSIGN_POS_EVEN ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"x - 1 = PRE x")
    prove_by_refinement (
      (← q r"!a n p ps q qs pts r rs s s1 s2 s3 rest sgns.
    interpmat pts
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Unknown s1)
          (APPEND (CONS Zero s2) (CONS Pos s3))) rest)) ==>
    (LENGTH ps = LENGTH s1) ==>
    (LENGTH qs = LENGTH s2) ==>
    ODD (LENGTH sgns) ==>
    (!x. a pow n * p x = s x * q x + r x) ==>
    (a <> &0) ==>
    EVEN n ==>
    interpmat pts
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Pos s1)
          (APPEND (CONS Zero s2) (CONS Pos s3))) rest))"),
    [
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND sgns (CONS
      (APPEND (CONS Unknown s1)
        (APPEND (CONS Zero s2) (CONS Pos s3))) rest)) =
          LENGTH (partition_line pts)"),
      REWRITE_ALL [interpmat],
      ASM_MESON_TAC [ALL2_LENGTH],
      REWRITE_TAC [LENGTH_APPEND, PARTITION_LINE_LENGTH, LENGTH],
      STRIP_TAC,
      TYPE_TACL (fun l => tactic_of do pure (MP_TAC (← ISPECL l SPLIT_LIST_THM))) [(← q r"(LENGTH sgns - 1) DIV 2"), (← q r"pts")],
      STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM MP_TAC,
      POP_ASSUM MP_TAC,
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM MP_TAC,
      ARITH_TAC,
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"~(l2 = [])"),
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC,
      REWRITE_ALL [APPEND_NIL],
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM (fun _x => ALL_TAC),
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC,
      POP_ASSUM MP_TAC,
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [NOT_NIL],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] INFERPSIGN_POS_EVEN_LEM),
      ASM_REWRITE_TAC [],
      EXISTS_TACL [(← q r"a"), (← q r"n"), (← q r"s")],
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      ASM_MESON_TAC [],
      LABEL_ALL_TAC,
      CLAIM (← q r"EVEN (LENGTH sgns - 1)"),
      ASM_MESON_TAC [EVEN_PRE, r1],
      STRIP_TAC,
      ASM_SIMP_TAC [DIV_EVEN],
      USE_THEN "Z-5" MP_TAC THEN ARITH_TAC
    ])

  let INFERPSIGN_NEG_EVEN_LEM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    let r2 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    let r3 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    let r4 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    prove_by_refinement (
      (← q r"!a n p ps q qs r rs s x pts1 pts2  s1 s2 s3 rest sgns.
    interpmat (APPEND pts1 (CONS x pts2))
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Unknown s1)
          (APPEND (CONS Zero s2) (CONS Neg s3))) rest)) ==>
    (LENGTH ps = LENGTH s1) ==>
    (LENGTH qs = LENGTH s2) ==>
    ODD (LENGTH sgns) ==>
    (LENGTH sgns = 2 * LENGTH pts1 + 1) ==>
    (!x. a pow n * p x = s x * q x + r x) ==>
    (a <> &0) ==>
    EVEN n ==>
    interpmat (APPEND pts1 (CONS x pts2))
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Neg s1)
          (APPEND (CONS Zero s2) (CONS Neg s3))) rest))"),
    [
      REPEAT STRIP_TAC,
      CLAIM (← q r"a pow n > &0"),
      ASM_MESON_TAC [EVEN_ODD_POW],
      STRIP_TAC,
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      FIRST_ASSUM MATCH_ACCEPT_TAC,
      CASES_ON (← q r"pts1 = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, partition_line],
      COND_CASES_TAC,
      CLAIM (← q r"?k. sgns = [k]"),
      MATCH_EQ_MP_TAC (← GSYM LENGTH_1),
      REWRITE_ALL [LENGTH],
      REPEAT_N 5 (POP_ASSUM (fun _x => ALL_TAC)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, partition_line, ALL2],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, interpsign, ALL2],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      REPEAT_N 8 (POP_ASSUM MP_TAC),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x < &0"),
      ASM_MESON_TAC [],
      REPEAT_N 6 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 7 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r4, REAL_MUL_LT],
      ASM_REWRITE_TAC [],
      POP_ASSUM (fun x => REWRITE_ASSUMS [x] THEN ASSUME_TAC x),
      CLAIM (← q r"?k. sgns = [k]"),
      MATCH_EQ_MP_TAC (← GSYM LENGTH_1),
      REWRITE_ALL [LENGTH],
      REPEAT_N 5 (POP_ASSUM (fun _x => ALL_TAC)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, partition_line, ALL2],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, interpsign, ALL2],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      REPEAT_N 9 (POP_ASSUM MP_TAC),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x < &0"),
      ASM_MESON_TAC [],
      REPEAT_N 8 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 9 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r3, REAL_MUL_LT],
      ASM_REWRITE_TAC [],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND],
      REPEAT STRIP_TAC,
      CLAIM (← q r"(APPEND (BUTLAST (partition_line pts1))
       (CONS (\x'. LAST pts1 < x' /\ x' < x)
       (TL (partition_line (CONS x pts2))))) =
       (APPEND
        (APPEND (BUTLAST (partition_line pts1))
        [\x'. LAST pts1 < x' /\ x' < x])
       (TL (partition_line (CONS x pts2))))"),
      ASM_MESON_TAC [APPEND_CONS],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_ALL [partition_line],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      REWRITE_ALL [TL],
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts1))
        [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns"),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_LENGTH)),
      ASM_SIMP_TAC [LENGTH_APPEND, PARTITION_LINE_NOT_NIL, BUTLAST_LENGTH, PARTITION_LINE_LENGTH, LENGTH],
      ARITH_TAC,
      STRIP_TAC,
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REPEAT_N 9 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => POP_ASSUM (fun y => REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y)),
      REWRITE_ALL [ALL2, interpsigns, APPEND, interpsign],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      RESTRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      REPEAT_N 4 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => REPEAT STRIP_TAC THEN ASSUME_TAC x),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      ASM_REWRITE_TAC [],
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x < &0"),
      ASM_MESON_TAC [],
      REPEAT_N 15 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 16 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r2, REAL_MUL_LT],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts1))
        [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns"),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_LENGTH)),
      ASM_SIMP_TAC [LENGTH_APPEND, PARTITION_LINE_NOT_NIL, BUTLAST_LENGTH, PARTITION_LINE_LENGTH, LENGTH],
      ARITH_TAC,
      STRIP_TAC,
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [TL, ALL2, interpsign, interpsigns, APPEND],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      REPEAT_N 10 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => POP_ASSUM (fun y => REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y)),
      REWRITE_ALL [ALL2, interpsigns, APPEND, interpsign],
      ASM_REWRITE_TAC [],
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      REPEAT_N 4 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => REPEAT STRIP_TAC THEN ASSUME_TAC x),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      ASM_REWRITE_TAC [],
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x < &0"),
      ASM_MESON_TAC [],
      REPEAT_N 16 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 17 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r1, REAL_MUL_LT]
    ])

  let INFERPSIGN_NEG_EVEN ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"x - 1 = PRE x")
    prove_by_refinement (
      (← q r"!a n p ps q qs pts r rs s s1 s2 s3 rest sgns.
    interpmat pts
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Unknown s1)
          (APPEND (CONS Zero s2) (CONS Neg s3))) rest)) ==>
    (LENGTH ps = LENGTH s1) ==>
    (LENGTH qs = LENGTH s2) ==>
    ODD (LENGTH sgns) ==>
    (!x. a pow n * p x = s x * q x + r x) ==>
    (a <> &0) ==>
    EVEN n ==>
    interpmat pts
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Neg s1)
          (APPEND (CONS Zero s2) (CONS Neg s3))) rest))"),
    [
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND sgns (CONS
      (APPEND (CONS Unknown s1)
        (APPEND (CONS Zero s2) (CONS Neg s3))) rest)) =
          LENGTH (partition_line pts)"),
      REWRITE_ALL [interpmat],
      ASM_MESON_TAC [ALL2_LENGTH],
      REWRITE_TAC [LENGTH_APPEND, PARTITION_LINE_LENGTH, LENGTH],
      STRIP_TAC,
      TYPE_TACL (fun l => tactic_of do pure (MP_TAC (← ISPECL l SPLIT_LIST_THM))) [(← q r"(LENGTH sgns - 1) DIV 2"), (← q r"pts")],
      STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM MP_TAC,
      POP_ASSUM MP_TAC,
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM MP_TAC,
      ARITH_TAC,
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"~(l2 = [])"),
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC,
      REWRITE_ALL [APPEND_NIL],
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM (fun _x => ALL_TAC),
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC,
      POP_ASSUM MP_TAC,
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [NOT_NIL],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] INFERPSIGN_NEG_EVEN_LEM),
      ASM_REWRITE_TAC [],
      EXISTS_TACL [(← q r"a"), (← q r"n"), (← q r"s")],
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      ASM_MESON_TAC [],
      LABEL_ALL_TAC,
      CLAIM (← q r"EVEN (LENGTH sgns - 1)"),
      ASM_MESON_TAC [EVEN_PRE, r1],
      STRIP_TAC,
      ASM_SIMP_TAC [DIV_EVEN],
      USE_THEN "Z-5" MP_TAC THEN ARITH_TAC
    ])

  -- @@RETURN BEGIN
  return { INFERPSIGN_NEG, INFERPSIGN_POS_EVEN_LEM, SPLIT_LIST_THM, EXISTS_TACL,
           DIV_EVEN, PRE_LEM, EVEN_PRE, ODD_PRE, INFERPSIGN_POS_EVEN,
           INFERPSIGN_NEG_EVEN_LEM, INFERPSIGN_NEG_EVEN }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- work_thms.ml phrases from line 7074 to 7910; the theorems              -/
/- converted by gxwork/rq/ml2lean.py (disclosed; comments in the          -/
/- proofs are not carried over), the functions by hand.                   -/
/- ---------------------------------------------------------------------- -/

structure WorkThms09 where
  -- @@FIELDS
  INFERPSIGN_ZERO_EVEN_LEM : thm
  INFERPSIGN_ZERO_EVEN : thm
  INFERPSIGN_POS_ODD_POS_LEM : thm
  INFERPSIGN_POS_ODD_POS : thm
  INFERPSIGN_NEG_ODD_POS_LEM : thm
  INFERPSIGN_NEG_ODD_POS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupWorkThms09 [HolBase] (D : WorkThmsDeps) (BWorkThms01 : WorkThms01) (BWorkThms08 : WorkThms08) :
    ExceptT String IO WorkThms09 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, CASES_ON, CLAIM, REAL_ARITH, TYPE_TACL,
        prove_by_refinement, .. } := D
  let { ALL2, APPEND, APPEND_NIL, EVEN_ODD_POW, IMP_AND_THM, LENGTH, LENGTH_1,
        LENGTH_APPEND, NOT_NIL, REAL_ADD_LID, REAL_ENTIRE, REAL_MUL_GT, REAL_MUL_LT,
        REAL_MUL_RZERO, REAL_POW_LT, TL, interpmat, interpsign, interpsigns,
        partition_line, real_gt, .. } := D.core1
  let { ALL2_APPEND, ALL2_APPEND_LENGTH, ALL2_LENGTH, APPEND_CONS, BUTLAST_LENGTH,
        PARTITION_LINE_APPEND, PARTITION_LINE_LENGTH, PARTITION_LINE_NOT_NIL, .. } := BWorkThms01
  let { DIV_EVEN, EVEN_PRE, EXISTS_TACL, SPLIT_LIST_THM, .. } := BWorkThms08
  -- @@SCOPE END

  let INFERPSIGN_ZERO_EVEN_LEM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"x < y ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    let r3 ← ARITH_RULE (← q r"x < y ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    let r5 ← ARITH_RULE (← q r"x < y ==> ~(x = y)")
    let r6 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    let r7 ← ARITH_RULE (← q r"x < y ==> ~(x = y)")
    let r8 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    prove_by_refinement (
      (← q r"!a n p ps q qs r rs s x pts1 pts2  s1 s2 s3 rest sgns.
    interpmat (APPEND pts1 (CONS x pts2))
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Unknown s1)
          (APPEND (CONS Zero s2) (CONS Zero s3))) rest)) ==>
    (LENGTH ps = LENGTH s1) ==>
    (LENGTH qs = LENGTH s2) ==>
    ODD (LENGTH sgns) ==>
    (LENGTH sgns = 2 * LENGTH pts1 + 1) ==>
    (!x. a pow n * p x = s x * q x + r x) ==>
    (a <> &0) ==>
    EVEN n ==>
    interpmat (APPEND pts1 (CONS x pts2))
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Zero s1)
          (APPEND (CONS Zero s2) (CONS Zero s3))) rest))"),
    [
      REPEAT STRIP_TAC,
      CLAIM (← q r"a pow n > &0"),
      ASM_MESON_TAC [EVEN_ODD_POW],
      STRIP_TAC,
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      FIRST_ASSUM MATCH_ACCEPT_TAC,
      CASES_ON (← q r"pts1 = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, partition_line],
      COND_CASES_TAC,
      CLAIM (← q r"?k. sgns = [k]"),
      MATCH_EQ_MP_TAC (← GSYM LENGTH_1),
      REWRITE_ALL [LENGTH],
      REPEAT_N 5 (POP_ASSUM (fun _x => ALL_TAC)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, partition_line, ALL2],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, interpsign, ALL2],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      REPEAT_N 8 (POP_ASSUM MP_TAC),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x = &0"),
      ASM_MESON_TAC [],
      REPEAT_N 6 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 7 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r8, REAL_MUL_LT, REAL_ENTIRE, r7],
      ASM_REWRITE_TAC [],
      POP_ASSUM (fun x => REWRITE_ASSUMS [x] THEN ASSUME_TAC x),
      CLAIM (← q r"?k. sgns = [k]"),
      MATCH_EQ_MP_TAC (← GSYM LENGTH_1),
      REWRITE_ALL [LENGTH],
      REPEAT_N 5 (POP_ASSUM (fun _x => ALL_TAC)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, partition_line, ALL2],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, interpsign, ALL2],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      REPEAT_N 9 (POP_ASSUM MP_TAC),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x = &0"),
      ASM_MESON_TAC [],
      REPEAT_N 8 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 9 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r6, REAL_MUL_LT, REAL_ENTIRE, r5],
      ASM_REWRITE_TAC [],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND],
      REPEAT STRIP_TAC,
      CLAIM (← q r"(APPEND (BUTLAST (partition_line pts1))
       (CONS (\x'. LAST pts1 < x' /\ x' < x)
       (TL (partition_line (CONS x pts2))))) =
       (APPEND
        (APPEND (BUTLAST (partition_line pts1))
        [\x'. LAST pts1 < x' /\ x' < x])
       (TL (partition_line (CONS x pts2))))"),
      ASM_MESON_TAC [APPEND_CONS],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_ALL [partition_line],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      REWRITE_ALL [TL],
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts1))
        [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns"),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_LENGTH)),
      ASM_SIMP_TAC [LENGTH_APPEND, PARTITION_LINE_NOT_NIL, BUTLAST_LENGTH, PARTITION_LINE_LENGTH, LENGTH],
      ARITH_TAC,
      STRIP_TAC,
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REPEAT_N 9 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => POP_ASSUM (fun y => REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y)),
      REWRITE_ALL [ALL2, interpsigns, APPEND, interpsign],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      RESTRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      REPEAT_N 4 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => REPEAT STRIP_TAC THEN ASSUME_TAC x),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      ASM_REWRITE_TAC [],
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x = &0"),
      ASM_MESON_TAC [],
      REPEAT_N 15 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 16 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r4, REAL_MUL_LT, REAL_ENTIRE, r3],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts1))
        [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns"),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_LENGTH)),
      ASM_SIMP_TAC [LENGTH_APPEND, PARTITION_LINE_NOT_NIL, BUTLAST_LENGTH, PARTITION_LINE_LENGTH, LENGTH],
      ARITH_TAC,
      STRIP_TAC,
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [TL, ALL2, interpsign, interpsigns, APPEND],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      REPEAT_N 10 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => POP_ASSUM (fun y => REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y)),
      REWRITE_ALL [ALL2, interpsigns, APPEND, interpsign],
      ASM_REWRITE_TAC [],
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      REPEAT_N 4 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => REPEAT STRIP_TAC THEN ASSUME_TAC x),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      ASM_REWRITE_TAC [],
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x = &0"),
      ASM_MESON_TAC [],
      REPEAT_N 16 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 17 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r2, REAL_MUL_LT, REAL_ENTIRE, r1]
    ])

  let INFERPSIGN_ZERO_EVEN ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"x - 1 = PRE x")
    prove_by_refinement (
      (← q r"!a n p ps q qs pts r rs s s1 s2 s3 rest sgns.
    interpmat pts
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Unknown s1)
          (APPEND (CONS Zero s2) (CONS Zero s3))) rest)) ==>
    (LENGTH ps = LENGTH s1) ==>
    (LENGTH qs = LENGTH s2) ==>
    ODD (LENGTH sgns) ==>
    (!x. a pow n * p x = s x * q x + r x) ==>
    (a <> &0) ==>
    EVEN n ==>
    interpmat pts
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Zero s1)
          (APPEND (CONS Zero s2) (CONS Zero s3))) rest))"),
    [
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND sgns (CONS
      (APPEND (CONS Unknown s1)
        (APPEND (CONS Zero s2) (CONS Zero s3))) rest)) =
          LENGTH (partition_line pts)"),
      REWRITE_ALL [interpmat],
      ASM_MESON_TAC [ALL2_LENGTH],
      REWRITE_TAC [LENGTH_APPEND, PARTITION_LINE_LENGTH, LENGTH],
      STRIP_TAC,
      TYPE_TACL (fun l => tactic_of do pure (MP_TAC (← ISPECL l SPLIT_LIST_THM))) [(← q r"(LENGTH sgns - 1) DIV 2"), (← q r"pts")],
      STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM MP_TAC,
      POP_ASSUM MP_TAC,
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM MP_TAC,
      ARITH_TAC,
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"~(l2 = [])"),
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC,
      REWRITE_ALL [APPEND_NIL],
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM (fun _x => ALL_TAC),
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC,
      POP_ASSUM MP_TAC,
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [NOT_NIL],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] INFERPSIGN_ZERO_EVEN_LEM),
      ASM_REWRITE_TAC [],
      EXISTS_TACL [(← q r"a"), (← q r"n"), (← q r"s")],
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      ASM_MESON_TAC [],
      LABEL_ALL_TAC,
      CLAIM (← q r"EVEN (LENGTH sgns - 1)"),
      ASM_MESON_TAC [EVEN_PRE, r1],
      STRIP_TAC,
      ASM_SIMP_TAC [DIV_EVEN],
      USE_THEN "Z-5" MP_TAC THEN ARITH_TAC
    ])

  let INFERPSIGN_POS_ODD_POS_LEM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"x < y ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    let r3 ← ARITH_RULE (← q r"x < y ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    let r5 ← ARITH_RULE (← q r"x < y ==> ~(x = y)")
    let r6 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    let r7 ← ARITH_RULE (← q r"x < y ==> ~(x = y)")
    let r8 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    prove_by_refinement (
      (← q r"!a n p ps q qs r rs s x pts1 pts2  s1 s2 s3 rest sgns.
    interpmat (APPEND pts1 (CONS x pts2))
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Unknown s1)
          (APPEND (CONS Zero s2) (CONS Pos s3))) rest)) ==>
    (LENGTH ps = LENGTH s1) ==>
    (LENGTH qs = LENGTH s2) ==>
    ODD (LENGTH sgns) ==>
    (LENGTH sgns = 2 * LENGTH pts1 + 1) ==>
    (!x. a pow n * p x = s x * q x + r x) ==>
    (a > &0) ==>
    interpmat (APPEND pts1 (CONS x pts2))
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Pos s1)
          (APPEND (CONS Zero s2) (CONS Pos s3))) rest))"),
    [
      REPEAT STRIP_TAC,
      CLAIM (← q r"a pow n > &0"),
      ASM_MESON_TAC [REAL_POW_LT, real_gt],
      STRIP_TAC,
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      FIRST_ASSUM MATCH_ACCEPT_TAC,
      CASES_ON (← q r"pts1 = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, partition_line],
      COND_CASES_TAC,
      CLAIM (← q r"?k. sgns = [k]"),
      MATCH_EQ_MP_TAC (← GSYM LENGTH_1),
      REWRITE_ALL [LENGTH],
      REPEAT_N 4 (POP_ASSUM (fun _x => ALL_TAC)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, partition_line, ALL2],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, interpsign, ALL2],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      REPEAT_N 7 (POP_ASSUM MP_TAC),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x > &0"),
      ASM_MESON_TAC [],
      REPEAT_N 5 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 6 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r8, REAL_MUL_LT, REAL_ENTIRE, r7],
      ASM_REWRITE_TAC [],
      POP_ASSUM (fun x => REWRITE_ASSUMS [x] THEN ASSUME_TAC x),
      CLAIM (← q r"?k. sgns = [k]"),
      MATCH_EQ_MP_TAC (← GSYM LENGTH_1),
      REWRITE_ALL [LENGTH],
      REPEAT_N 4 (POP_ASSUM (fun _x => ALL_TAC)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, partition_line, ALL2],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, interpsign, ALL2],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      REPEAT_N 8 (POP_ASSUM MP_TAC),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x > &0"),
      ASM_MESON_TAC [],
      REPEAT_N 7 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 8 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r6, REAL_MUL_LT, REAL_ENTIRE, r5],
      ASM_REWRITE_TAC [],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND],
      REPEAT STRIP_TAC,
      CLAIM (← q r"(APPEND (BUTLAST (partition_line pts1))
       (CONS (\x'. LAST pts1 < x' /\ x' < x)
       (TL (partition_line (CONS x pts2))))) =
       (APPEND
        (APPEND (BUTLAST (partition_line pts1))
        [\x'. LAST pts1 < x' /\ x' < x])
       (TL (partition_line (CONS x pts2))))"),
      ASM_MESON_TAC [APPEND_CONS],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_ALL [partition_line],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      REWRITE_ALL [TL],
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts1))
        [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns"),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_LENGTH)),
      ASM_SIMP_TAC [LENGTH_APPEND, PARTITION_LINE_NOT_NIL, BUTLAST_LENGTH, PARTITION_LINE_LENGTH, LENGTH],
      ARITH_TAC,
      STRIP_TAC,
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REPEAT_N 8 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => POP_ASSUM (fun y => REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y)),
      REWRITE_ALL [ALL2, interpsigns, APPEND, interpsign],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      RESTRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      REPEAT_N 4 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => REPEAT STRIP_TAC THEN ASSUME_TAC x),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      ASM_REWRITE_TAC [],
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x > &0"),
      ASM_MESON_TAC [],
      REPEAT_N 14 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 16 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r4, REAL_MUL_LT, REAL_ENTIRE, r3, REAL_MUL_GT],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts1))
        [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns"),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_LENGTH)),
      ASM_SIMP_TAC [LENGTH_APPEND, PARTITION_LINE_NOT_NIL, BUTLAST_LENGTH, PARTITION_LINE_LENGTH, LENGTH],
      ARITH_TAC,
      STRIP_TAC,
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [TL, ALL2, interpsign, interpsigns, APPEND],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      REPEAT_N 9 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => POP_ASSUM (fun y => REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y)),
      REWRITE_ALL [ALL2, interpsigns, APPEND, interpsign],
      ASM_REWRITE_TAC [],
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      REPEAT_N 4 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => REPEAT STRIP_TAC THEN ASSUME_TAC x),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      ASM_REWRITE_TAC [],
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x > &0"),
      ASM_MESON_TAC [],
      REPEAT_N 15 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 16 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r2, REAL_MUL_LT, REAL_ENTIRE, r1]
    ])

  let INFERPSIGN_POS_ODD_POS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"x - 1 = PRE x")
    prove_by_refinement (
      (← q r"!a n p ps q qs pts r rs s s1 s2 s3 rest sgns.
    interpmat pts
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Unknown s1)
          (APPEND (CONS Zero s2) (CONS Pos s3))) rest)) ==>
    (LENGTH ps = LENGTH s1) ==>
    (LENGTH qs = LENGTH s2) ==>
    ODD (LENGTH sgns) ==>
    (!x. a pow n * p x = s x * q x + r x) ==>
    (a > &0) ==>
    interpmat pts
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Pos s1)
          (APPEND (CONS Zero s2) (CONS Pos s3))) rest))"),
    [
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND sgns (CONS
      (APPEND (CONS Unknown s1)
        (APPEND (CONS Zero s2) (CONS Pos s3))) rest)) =
          LENGTH (partition_line pts)"),
      REWRITE_ALL [interpmat],
      ASM_MESON_TAC [ALL2_LENGTH],
      REWRITE_TAC [LENGTH_APPEND, PARTITION_LINE_LENGTH, LENGTH],
      STRIP_TAC,
      TYPE_TACL (fun l => tactic_of do pure (MP_TAC (← ISPECL l SPLIT_LIST_THM))) [(← q r"(LENGTH sgns - 1) DIV 2"), (← q r"pts")],
      STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM MP_TAC,
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM MP_TAC,
      ARITH_TAC,
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"~(l2 = [])"),
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC,
      REWRITE_ALL [APPEND_NIL],
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM (fun _x => ALL_TAC),
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC,
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [NOT_NIL],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] INFERPSIGN_POS_ODD_POS_LEM),
      ASM_REWRITE_TAC [],
      EXISTS_TACL [(← q r"a"), (← q r"n"), (← q r"s")],
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      ASM_MESON_TAC [],
      LABEL_ALL_TAC,
      CLAIM (← q r"EVEN (LENGTH sgns - 1)"),
      ASM_MESON_TAC [EVEN_PRE, r1],
      STRIP_TAC,
      ASM_SIMP_TAC [DIV_EVEN],
      USE_THEN "Z-4" MP_TAC THEN ARITH_TAC
    ])

  let INFERPSIGN_NEG_ODD_POS_LEM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"x < y ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    let r3 ← ARITH_RULE (← q r"x < y ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    let r5 ← ARITH_RULE (← q r"x < y ==> ~(x = y)")
    let r6 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    let r7 ← ARITH_RULE (← q r"x < y ==> ~(x = y)")
    let r8 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    prove_by_refinement (
      (← q r"!a n p ps q qs r rs s x pts1 pts2  s1 s2 s3 rest sgns.
    interpmat (APPEND pts1 (CONS x pts2))
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Unknown s1)
          (APPEND (CONS Zero s2) (CONS Neg s3))) rest)) ==>
    (LENGTH ps = LENGTH s1) ==>
    (LENGTH qs = LENGTH s2) ==>
    ODD (LENGTH sgns) ==>
    (LENGTH sgns = 2 * LENGTH pts1 + 1) ==>
    (!x. a pow n * p x = s x * q x + r x) ==>
    (a > &0) ==>
    interpmat (APPEND pts1 (CONS x pts2))
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Neg s1)
          (APPEND (CONS Zero s2) (CONS Neg s3))) rest))"),
    [
      REPEAT STRIP_TAC,
      CLAIM (← q r"a pow n > &0"),
      ASM_MESON_TAC [REAL_POW_LT, real_gt],
      STRIP_TAC,
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      FIRST_ASSUM MATCH_ACCEPT_TAC,
      CASES_ON (← q r"pts1 = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, partition_line],
      COND_CASES_TAC,
      CLAIM (← q r"?k. sgns = [k]"),
      MATCH_EQ_MP_TAC (← GSYM LENGTH_1),
      REWRITE_ALL [LENGTH],
      REPEAT_N 4 (POP_ASSUM (fun _x => ALL_TAC)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, partition_line, ALL2],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, interpsign, ALL2],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      REPEAT_N 7 (POP_ASSUM MP_TAC),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x < &0"),
      ASM_MESON_TAC [real_gt],
      REPEAT_N 5 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 6 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r8, REAL_MUL_LT, REAL_ENTIRE, r7],
      ASM_REWRITE_TAC [],
      POP_ASSUM (fun x => REWRITE_ASSUMS [x] THEN ASSUME_TAC x),
      CLAIM (← q r"?k. sgns = [k]"),
      MATCH_EQ_MP_TAC (← GSYM LENGTH_1),
      REWRITE_ALL [LENGTH],
      REPEAT_N 4 (POP_ASSUM (fun _x => ALL_TAC)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, partition_line, ALL2],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, interpsign, ALL2],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      REPEAT_N 8 (POP_ASSUM MP_TAC),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x < &0"),
      ASM_MESON_TAC [],
      REPEAT_N 7 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 8 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r6, REAL_MUL_LT, REAL_ENTIRE, r5],
      ASM_REWRITE_TAC [],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND],
      REPEAT STRIP_TAC,
      CLAIM (← q r"(APPEND (BUTLAST (partition_line pts1))
       (CONS (\x'. LAST pts1 < x' /\ x' < x)
       (TL (partition_line (CONS x pts2))))) =
       (APPEND
        (APPEND (BUTLAST (partition_line pts1))
        [\x'. LAST pts1 < x' /\ x' < x])
       (TL (partition_line (CONS x pts2))))"),
      ASM_MESON_TAC [APPEND_CONS],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_ALL [partition_line],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      REWRITE_ALL [TL],
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts1))
        [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns"),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_LENGTH)),
      ASM_SIMP_TAC [LENGTH_APPEND, PARTITION_LINE_NOT_NIL, BUTLAST_LENGTH, PARTITION_LINE_LENGTH, LENGTH],
      ARITH_TAC,
      STRIP_TAC,
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REPEAT_N 8 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => POP_ASSUM (fun y => REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y)),
      REWRITE_ALL [ALL2, interpsigns, APPEND, interpsign],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      RESTRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      REPEAT_N 4 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => REPEAT STRIP_TAC THEN ASSUME_TAC x),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      ASM_REWRITE_TAC [],
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x < &0"),
      ASM_MESON_TAC [],
      REPEAT_N 14 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 16 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r4, REAL_MUL_LT, REAL_ENTIRE, r3, REAL_MUL_GT],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts1))
        [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns"),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_LENGTH)),
      ASM_SIMP_TAC [LENGTH_APPEND, PARTITION_LINE_NOT_NIL, BUTLAST_LENGTH, PARTITION_LINE_LENGTH, LENGTH],
      ARITH_TAC,
      STRIP_TAC,
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [TL, ALL2, interpsign, interpsigns, APPEND],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      REPEAT_N 9 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => POP_ASSUM (fun y => REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y)),
      REWRITE_ALL [ALL2, interpsigns, APPEND, interpsign],
      ASM_REWRITE_TAC [],
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      REPEAT_N 4 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => REPEAT STRIP_TAC THEN ASSUME_TAC x),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      ASM_REWRITE_TAC [],
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x < &0"),
      ASM_MESON_TAC [],
      REPEAT_N 15 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 16 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r2, REAL_MUL_LT, REAL_ENTIRE, r1]
    ])

  let INFERPSIGN_NEG_ODD_POS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"x - 1 = PRE x")
    prove_by_refinement (
      (← q r"!a n p ps q qs pts r rs s s1 s2 s3 rest sgns.
    interpmat pts
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Unknown s1)
          (APPEND (CONS Zero s2) (CONS Neg s3))) rest)) ==>
    (LENGTH ps = LENGTH s1) ==>
    (LENGTH qs = LENGTH s2) ==>
    ODD (LENGTH sgns) ==>
    (!x. a pow n * p x = s x * q x + r x) ==>
    (a > &0) ==>
    interpmat pts
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Neg s1)
          (APPEND (CONS Zero s2) (CONS Neg s3))) rest))"),
    [
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND sgns (CONS
      (APPEND (CONS Unknown s1)
        (APPEND (CONS Zero s2) (CONS Neg s3))) rest)) =
          LENGTH (partition_line pts)"),
      REWRITE_ALL [interpmat],
      ASM_MESON_TAC [ALL2_LENGTH],
      REWRITE_TAC [LENGTH_APPEND, PARTITION_LINE_LENGTH, LENGTH],
      STRIP_TAC,
      TYPE_TACL (fun l => tactic_of do pure (MP_TAC (← ISPECL l SPLIT_LIST_THM))) [(← q r"(LENGTH sgns - 1) DIV 2"), (← q r"pts")],
      STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM MP_TAC,
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM MP_TAC,
      ARITH_TAC,
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"~(l2 = [])"),
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC,
      REWRITE_ALL [APPEND_NIL],
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM (fun _x => ALL_TAC),
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC,
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [NOT_NIL],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] INFERPSIGN_NEG_ODD_POS_LEM),
      ASM_REWRITE_TAC [],
      EXISTS_TACL [(← q r"a"), (← q r"n"), (← q r"s")],
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      ASM_MESON_TAC [],
      LABEL_ALL_TAC,
      CLAIM (← q r"EVEN (LENGTH sgns - 1)"),
      ASM_MESON_TAC [EVEN_PRE, r1],
      STRIP_TAC,
      ASM_SIMP_TAC [DIV_EVEN],
      USE_THEN "Z-4" MP_TAC THEN ARITH_TAC
    ])

  -- @@RETURN BEGIN
  return { INFERPSIGN_ZERO_EVEN_LEM, INFERPSIGN_ZERO_EVEN, INFERPSIGN_POS_ODD_POS_LEM,
           INFERPSIGN_POS_ODD_POS, INFERPSIGN_NEG_ODD_POS_LEM, INFERPSIGN_NEG_ODD_POS }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- work_thms.ml phrases from line 7981 to 8211; the theorems              -/
/- converted by gxwork/rq/ml2lean.py (disclosed; comments in the          -/
/- proofs are not carried over), the functions by hand.                   -/
/- ---------------------------------------------------------------------- -/

structure WorkThms10 where
  -- @@FIELDS
  INFERPSIGN_ZERO_ODD_POS_LEM : thm
  INFERPSIGN_ZERO_ODD_POS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupWorkThms10 [HolBase] (D : WorkThmsDeps) (BWorkThms01 : WorkThms01) (BWorkThms08 : WorkThms08) :
    ExceptT String IO WorkThms10 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, CASES_ON, CLAIM, REAL_ARITH, TYPE_TACL,
        prove_by_refinement, .. } := D
  let { ALL2, APPEND, APPEND_NIL, IMP_AND_THM, LENGTH, LENGTH_1, LENGTH_APPEND,
        NOT_NIL, REAL_ADD_LID, REAL_ENTIRE, REAL_LT_IMP_NZ, REAL_MUL_GT, REAL_MUL_LT,
        REAL_MUL_RZERO, REAL_POW_LT, TL, interpmat, interpsign, interpsigns,
        partition_line, real_gt, .. } := D.core1
  let { ALL2_APPEND, ALL2_APPEND_LENGTH, ALL2_LENGTH, APPEND_CONS, BUTLAST_LENGTH,
        PARTITION_LINE_APPEND, PARTITION_LINE_LENGTH, PARTITION_LINE_NOT_NIL, .. } := BWorkThms01
  let { DIV_EVEN, EVEN_PRE, EXISTS_TACL, SPLIT_LIST_THM, .. } := BWorkThms08
  -- @@SCOPE END

  let INFERPSIGN_ZERO_ODD_POS_LEM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"x < y ==> ~(x = y)")
    let r2 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    let r3 ← ARITH_RULE (← q r"x < y ==> ~(x = y)")
    let r4 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    let r5 ← ARITH_RULE (← q r"x < y ==> ~(x = y)")
    let r6 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    let r7 ← ARITH_RULE (← q r"x < y ==> ~(x = y)")
    let r8 ← REAL_ARITH (← q r"~(x < y /\ y < x)")
    prove_by_refinement (
      (← q r"!a n p ps q qs r rs s x pts1 pts2  s1 s2 s3 rest sgns.
    interpmat (APPEND pts1 (CONS x pts2))
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Unknown s1)
          (APPEND (CONS Zero s2) (CONS Zero s3))) rest)) ==>
    (LENGTH ps = LENGTH s1) ==>
    (LENGTH qs = LENGTH s2) ==>
    ODD (LENGTH sgns) ==>
    (LENGTH sgns = 2 * LENGTH pts1 + 1) ==>
    (!x. a pow n * p x = s x * q x + r x) ==>
    (a > &0) ==>
    interpmat (APPEND pts1 (CONS x pts2))
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Zero s1)
          (APPEND (CONS Zero s2) (CONS Zero s3))) rest))"),
    [
      REPEAT STRIP_TAC,
      CLAIM (← q r"a pow n > &0"),
      ASM_MESON_TAC [REAL_POW_LT, real_gt],
      STRIP_TAC,
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_TAC [interpmat],
      REPEAT STRIP_TAC,
      FIRST_ASSUM MATCH_ACCEPT_TAC,
      CASES_ON (← q r"pts1 = []"),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, partition_line],
      COND_CASES_TAC,
      CLAIM (← q r"?k. sgns = [k]"),
      MATCH_EQ_MP_TAC (← GSYM LENGTH_1),
      REWRITE_ALL [LENGTH],
      REPEAT_N 4 (POP_ASSUM (fun _x => ALL_TAC)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, partition_line, ALL2],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, interpsign, ALL2],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      REPEAT_N 7 (POP_ASSUM MP_TAC),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x = &0"),
      ASM_MESON_TAC [real_gt],
      REPEAT_N 5 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 6 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r8, REAL_MUL_LT, REAL_ENTIRE, r7],
      ASM_REWRITE_TAC [],
      POP_ASSUM (fun x => REWRITE_ASSUMS [x] THEN ASSUME_TAC x),
      CLAIM (← q r"?k. sgns = [k]"),
      MATCH_EQ_MP_TAC (← GSYM LENGTH_1),
      REWRITE_ALL [LENGTH],
      REPEAT_N 4 (POP_ASSUM (fun _x => ALL_TAC)),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [APPEND, partition_line, ALL2],
      REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [interpsigns, interpsign, ALL2],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      REPEAT_N 8 (POP_ASSUM MP_TAC),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x = &0"),
      ASM_MESON_TAC [],
      REPEAT_N 7 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 8 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r6, REAL_MUL_LT, REAL_ENTIRE, r5],
      ASM_REWRITE_TAC [],
      POP_ASSUM (fun x => REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x),
      ASM_SIMP_TAC [PARTITION_LINE_APPEND],
      REPEAT STRIP_TAC,
      CLAIM (← q r"(APPEND (BUTLAST (partition_line pts1))
       (CONS (\x'. LAST pts1 < x' /\ x' < x)
       (TL (partition_line (CONS x pts2))))) =
       (APPEND
        (APPEND (BUTLAST (partition_line pts1))
        [\x'. LAST pts1 < x' /\ x' < x])
       (TL (partition_line (CONS x pts2))))"),
      ASM_MESON_TAC [APPEND_CONS],
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      REPEAT (POP_ASSUM MP_TAC),
      REWRITE_ALL [partition_line],
      COND_CASES_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REPEAT STRIP_TAC,
      REWRITE_ALL [TL],
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts1))
        [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns"),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_LENGTH)),
      ASM_SIMP_TAC [LENGTH_APPEND, PARTITION_LINE_NOT_NIL, BUTLAST_LENGTH, PARTITION_LINE_LENGTH, LENGTH],
      ARITH_TAC,
      STRIP_TAC,
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REPEAT_N 8 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => POP_ASSUM (fun y => REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y)),
      REWRITE_ALL [ALL2, interpsigns, APPEND, interpsign],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      RESTRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      REPEAT_N 4 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => REPEAT STRIP_TAC THEN ASSUME_TAC x),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      ASM_REWRITE_TAC [],
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x = &0"),
      ASM_MESON_TAC [],
      REPEAT_N 14 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 16 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r4, REAL_MUL_LT, REAL_ENTIRE, r3, REAL_MUL_GT, REAL_LT_IMP_NZ],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND (BUTLAST (partition_line pts1))
        [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns"),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_LENGTH)),
      ASM_SIMP_TAC [LENGTH_APPEND, PARTITION_LINE_NOT_NIL, BUTLAST_LENGTH, PARTITION_LINE_LENGTH, LENGTH],
      ARITH_TAC,
      STRIP_TAC,
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REPEAT STRIP_TAC,
      MATCH_MP_TAC ALL2_APPEND,
      ASM_REWRITE_TAC [],
      REWRITE_ALL [TL, ALL2, interpsign, interpsigns, APPEND],
      ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC,
      REPEAT_N 9 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => POP_ASSUM (fun y => REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y)),
      REWRITE_ALL [ALL2, interpsigns, APPEND, interpsign],
      ASM_REWRITE_TAC [],
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      REPEAT_N 4 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun x => REPEAT STRIP_TAC THEN ASSUME_TAC x),
      FIRST_ASSUM (MP_TAC o (MATCH_MP ALL2_APPEND_LENGTH)),
      FIRST_ASSUM (fun x => tactic_of do pure (DISCH_THEN (fun y => tactic_of do pure (MP_TAC (← MATCH_MP y x))))),
      REWRITE_TAC [ALL2, interpsign],
      REPEAT STRIP_TAC,
      REWRITE_ALL [interpsigns, ALL2, interpsign],
      ASM_REWRITE_TAC [],
      CLAIM (← q r"q x = &0"),
      ASM_MESON_TAC [],
      CLAIM (← q r"r x = &0"),
      ASM_MESON_TAC [],
      REPEAT_N 15 (POP_ASSUM MP_TAC),
      POP_ASSUM (MP_TAC o (ISPEC (← q r"x:real"))),
      REPEAT STRIP_TAC,
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      REWRITE_ALL [REAL_MUL_RZERO, REAL_ADD_LID],
      REPEAT_N 16 (POP_ASSUM MP_TAC),
      POP_ASSUM (fun th => tactic_of do pure (REWRITE_ALL [← GSYM th])),
      REWRITE_TAC [real_gt, REAL_MUL_GT],
      REPEAT STRIP_TAC,
      ASM_MESON_TAC [r2, REAL_MUL_LT, REAL_ENTIRE, r1, REAL_MUL_GT, REAL_LT_IMP_NZ]
    ])

  let INFERPSIGN_ZERO_ODD_POS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"x - 1 = PRE x")
    prove_by_refinement (
      (← q r"!a n p ps q qs pts r rs s s1 s2 s3 rest sgns.
    interpmat pts
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Unknown s1)
          (APPEND (CONS Zero s2) (CONS Zero s3))) rest)) ==>
    (LENGTH ps = LENGTH s1) ==>
    (LENGTH qs = LENGTH s2) ==>
    ODD (LENGTH sgns) ==>
    (!x. a pow n * p x = s x * q x + r x) ==>
    (a > &0) ==>
    interpmat pts
      (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
      (APPEND sgns
        (CONS (APPEND (CONS Zero s1)
          (APPEND (CONS Zero s2) (CONS Zero s3))) rest))"),
    [
      REPEAT STRIP_TAC,
      CLAIM (← q r"LENGTH (APPEND sgns (CONS
      (APPEND (CONS Unknown s1)
        (APPEND (CONS Zero s2) (CONS Zero s3))) rest)) =
          LENGTH (partition_line pts)"),
      REWRITE_ALL [interpmat],
      ASM_MESON_TAC [ALL2_LENGTH],
      REWRITE_TAC [LENGTH_APPEND, PARTITION_LINE_LENGTH, LENGTH],
      STRIP_TAC,
      TYPE_TACL (fun l => tactic_of do pure (MP_TAC (← ISPECL l SPLIT_LIST_THM))) [(← q r"(LENGTH sgns - 1) DIV 2"), (← q r"pts")],
      STRIP_TAC,
      LABEL_ALL_TAC,
      PROVE_ASSUM_ANTECEDENT_TAC 0,
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM MP_TAC,
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM MP_TAC,
      ARITH_TAC,
      POP_ASSUM MP_TAC THEN STRIP_TAC,
      ASM_REWRITE_TAC [],
      CLAIM (← q r"~(l2 = [])"),
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC,
      REWRITE_ALL [APPEND_NIL],
      POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM (fun _x => ALL_TAC),
      DISCH_THEN (REWRITE_ALL o (list : thm → List thm)),
      POP_ASSUM MP_TAC,
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM (fun _x => ALL_TAC),
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      REWRITE_TAC [NOT_NIL],
      STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o (list : thm → List thm)),
      MATCH_MP_TAC (← REWRITE_RULE [IMP_AND_THM] INFERPSIGN_ZERO_ODD_POS_LEM),
      ASM_REWRITE_TAC [],
      EXISTS_TACL [(← q r"a"), (← q r"n"), (← q r"s")],
      ASM_REWRITE_TAC [],
      STRIP_TAC,
      ASM_MESON_TAC [],
      LABEL_ALL_TAC,
      CLAIM (← q r"EVEN (LENGTH sgns - 1)"),
      ASM_MESON_TAC [EVEN_PRE, r1],
      STRIP_TAC,
      ASM_SIMP_TAC [DIV_EVEN],
      USE_THEN "Z-4" MP_TAC THEN ARITH_TAC
    ])

  -- @@RETURN BEGIN
  return { INFERPSIGN_ZERO_ODD_POS_LEM, INFERPSIGN_ZERO_ODD_POS }
  -- @@RETURN END

end HolRQE.WorkThms
