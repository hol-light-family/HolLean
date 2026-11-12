/- ========================================================================= -/
/- Rqe: the main quantifier elimination procedure, REAL_QELIM_CONV.        -/
/- ========================================================================= -/
/- File: HolRQE/RqeMain.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/rqe_main.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml, Rqe/num_calc_simp.ml, Rqe/asym.ml, Rqe/rol.ml, Rqe/poly_ext.ml, Rqe/simplify.ml, Rqe/lift_qelim.ml, Rqe/defs.ml, Rqe/testform_thms.ml, Rqe/condense_thms.ml, Rqe/inferisign_thms.ml, Rqe/matinsert_thms.ml, Rqe/signs_thms.ml, Rqe/inferpsign_thms.ml, Rqe/dedmatrix_thms.ml, Rqe/pdivides_thms.ml, Rqe/main_thms.ml, Rqe/work_thms.ml, Rqe/testform.ml, Rqe/condense.ml, Rqe/inferisign.ml, Rqe/matinsert.ml, Rqe/signs.ml, Rqe/inferpsign.ml, Rqe/dedmatrix.ml, Rqe/pdivides.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.RqeMain fills them).

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
import HolRQE.WorkThms
import HolRQE.Testform
import HolRQE.Condense
import HolRQE.Inferisign
import HolRQE.Matinsert
import HolRQE.Signs
import HolRQE.Inferpsign
import HolRQE.Dedmatrix
import HolRQE.Pdivides

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
open HolRQE.WorkThms
open HolRQE.Testform
open HolRQE.Condense
open HolRQE.Inferisign
open HolRQE.Matinsert
open HolRQE.Signs
open HolRQE.Inferpsign
open HolRQE.Dedmatrix
open HolRQE.Pdivides

namespace HolRQE.RqeMain

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALL2 LAST LENGTH NEQ NORMAL_ID NOT_CONS_NIL TRUTH empty_mat
   factor_neg_even_neg factor_neg_even_pos factor_neg_even_zero
   factor_neg_odd_neg factor_neg_odd_pos factor_neg_odd_zero factor_pos_neg
   factor_pos_pos factor_pos_zero factor_zero_neg factor_zero_pos
   factor_zero_zero gtneg gtpos gtzero ltneg ltpos ltzero main_lem000
   main_lem001 main_lem002 : thm)
  deriving Inhabited

/-- What rqe_main.ml uses from Session besides theorems. -/
structure RqeMainDeps where
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
  MATCH_EQ_MP : thm → thm → ExceptT String IO thm
  t_tm : term
  f_tm : term
  nzero : term
  even_tm : term
  odd_tm : term
  PARITY_CONV : term → ExceptT String IO thm
  req : term
  rneq : term
  rlt : term
  rgt : term
  rle : term
  rge : term
  rzero : term
  dest_mult : term → Except String (term × term)
  EL_CONV : ioconv → Int → ioconv
  duplicate_columns_timer : Option (IO.Ref Float)
  unmonicize_mat_timer : Option (IO.Ref Float)
  swap_head_col_timer : Option (IO.Ref Float)
  replace_pol_timer : Option (IO.Ref Float)
  unfactor_mat_timer : Option (IO.Ref Float)
  poly_tm : term
  dest_poly : term → Except String (term × term)
  is_constant : List term → term → Except String Bool
  POLY_ENLIST_CONV : List term → ExceptT String IO ioconv
  POLY_DELIST_CONV : ioconv
  CANON_POLY_DIFF_CONV : ioconv
  POLYNATE_CONV : List term → ioconv
  degree_ : List term → term → Except String Int
  head : List term → term → Except String term
  behead : List term → term → Except String term
  BEHEAD : List term → thm → term → ExceptT String IO thm
  MONIC_CONV : List term → ioconv
  SIGN_CONST : term → ExceptT String IO thm
  POLYATOM_CONV : List term → term → ExceptT String IO thm
  weakfactor : term → term → Int × term
  poly_var : term → Except String term
  WEAKFACTOR_CONV : term → term → ExceptT String IO thm
  SIMPLIFY_CONV : ioconv
  EVALC_CONV : ioconv
  LIFT_QELIM_CONV : (List term → ioconv) → ioconv → (List term → ioconv) → ioconv
  sneg_tm : term
  spos_tm : term
  szero_tm : term
  dest_interpsign : thm → Except String (term × term × term)
  interpsigns_thms2 : thm → ExceptT String IO (List thm)
  mk_interpsigns : List thm → ExceptT String IO thm
  PARTITION_LINE_CONV : term → ExceptT String IO thm
  dest_interpmat : term → Except String (term × term × term)
  interpmat_thms : thm → ExceptT String IO (thm × thm)
  mk_interpmat_thm : thm → thm → ExceptT String IO thm
  mk_all2_interpsigns : thm → List thm → ExceptT String IO thm
  dest_all2 : term → Except String (term × term × term)
  empty_sgns : List thm
  COMBINE_TESTFORMS : term → thm → term → ExceptT String IO thm
  Isign_arg : Option (IO.Ref (thm × List (term × thm)))
  MATINSERT : List term → Int → thm → MatCont → MatCont
  FINDSIGN : List term → List thm → term → ExceptT String IO thm
  SPLIT_ZERO : List term → List thm → term → SignCont → SignCont → List (term × thm) → ExceptT String IO thm
  SPLIT_SIGN : List term → List thm → term → SignCont → SignCont → List (term × thm) → ExceptT String IO thm
  DEDMATRIX : List term → List thm → List thm → thm → thm → DedCont → thm → List (term × thm) → ExceptT String IO thm
  PDIVIDES : List term → List thm → term → term → ExceptT String IO (term × thm)
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

/-- lib.ml's `partition` with a predicate that can fail (`itlist`, so the
    last element is tested first). -/
def partitionE {α : Type} (p : α → Except String Bool) : List α → Except String (List α × List α)
  | [] => pure ([], [])
  | h :: t => do
    let (yes, no) ← partitionE p t
    if ← p h then pure (h :: yes, no) else pure (yes, h :: no)

/-- lib.ml's `sort` (quicksort) with an ordering that can fail; OCaml
    evaluates `(sort cmp l) @ (piv::(sort cmp r))` right to left. -/
partial def sortE {α : Type} (cmp : α → α → Except String Bool) : List α → Except String (List α)
  | [] => pure []
  | piv :: rest => do
    let (r, l) ← partitionE (cmp piv) rest
    let sr ← sortE cmp r
    let sl ← sortE cmp l
    pure (sl ++ piv :: sr)

/-- lib.ml's `map2` for a rule that can fail (left to right). -/
def map2M {α β γ : Type} (f : α → β → ExceptT String IO γ) :
    List α → List β → ExceptT String IO (List γ)
  | [], [] => pure []
  | h1 :: t1, h2 :: t2 => do
    let h ← f h1 h2
    return h :: (← map2M f t1 t2)
  | _, _ => throw "map2: length mismatch"

/-- rqe_main.ml's `get_repeats`. -/
def get_repeats {α : Type} [BEq α] (l : List α) : List Int :=
  let rec go : List α → List α → Int → List Int
    | [], _, _ => []
    | h :: t, seen, ind =>
      if mem h seen then ind :: go t seen (ind + 1)
      else go t (h :: seen) (ind + 1)
  go l [] 0

/-- rqe_main.ml's `subtract_index`. -/
def subtract_index (l : List Int) : List Int :=
  let rec go : List Int → Int → List Int
    | [], _ => []
    | h :: t, ind => (h - ind) :: go t (ind + 1)
  go l 0

/-- rqe_main.ml's `let rec first f l`: `if can f h then f h else ..`, so `f`
    runs twice on the element that succeeds. -/
partial def first_can {α β : Type} (f : α → ExceptT String IO β) : List α → ExceptT String IO β
  | [] => throw "first"
  | h :: t => do
    let ok ← tryCatch (do let _ ← f h; pure true) (fun _ => pure false)
    if ok then f h else first_can f t

/-- rqe_main.ml's `message_time s f x = report s; time f x`. -/
def message_time {α β : Type} (s : String) (f : α → ExceptT String IO β) (x : α) :
    ExceptT String IO β := do
  report s
  ExceptT.mk (time (fun y => (f y).run) x)

/-- The inner `let rec polynomials` of rqe_main.ml's `polynomials`; OCaml
    evaluates `polynomials l @ polynomials r` right to left. -/
partial def polynomials.go (t_tm f_tm : term) (rels : List term) (tm : term) :
    Except String (List term) :=
  if tm == t_tm || tm == f_tm then pure []
  else if is_conj tm || is_disj tm || is_imp tm || HolCore.Bool.is_iff tm then do
    let (_, l, r) ← get_binop tm
    let pr ← polynomials.go t_tm f_tm rels r
    let pl ← polynomials.go t_tm f_tm rels l
    pure (pl ++ pr)
  else if is_neg tm then do polynomials.go t_tm f_tm rels (← dest_neg tm)
  else if rels.any (fun r => canE (dest_binop r) tm) then do
    let (_, l, _) ← get_binop tm
    pure [l]
  else .error "not a fol atom"

/-- The types of MATRIX and MONICIZE (`vars pols cont sgns ex_thms fm`) and of
    SPLITZERO and SPLITSIGNS (`vars dun pols cont sgns ex_thms fm`); a
    continuation is a MatCont, as MATINSERT's. -/
abbrev MatrixFn := List term → List term → MatCont → List thm → List (term × thm) → term → ExceptT String IO thm
abbrev SplitFn := List term → List term → List term → MatCont → List thm → List (term × thm) → term → ExceptT String IO thm

/-- `deriving Inhabited` does not find a default for a function of seven
    arguments, so give one. -/
instance : Inhabited SplitFn := ⟨fun _ _ _ _ _ _ _ => throw "SPLITZERO: bundle not built"⟩



/- ---------------------------------------------------------------------- -/
/-  The main procedure (rqe_main.ml 1-671; its examples are in comments) -/
/- ---------------------------------------------------------------------- -/

structure RqeMainFns where
  -- @@FIELDS
  TRAPOUT : MatCont → thm → List (term × thm) → term → ExceptT String IO thm
  remove_column : Int → thm → ExceptT String IO thm
  REMOVE_COLUMN : Int → thm → ExceptT String IO thm
  SETIFY_CONV : thm → ExceptT String IO thm
  duplicate_columns : List Int → thm → ExceptT String IO thm
  DUPLICATE_COLUMNS : thm → List Int → ExceptT String IO thm
  UNMONICIZE_ISIGN : List term → thm → thm → ExceptT String IO thm
  UNMONICIZE_ISIGNS : List term → List thm → thm → ExceptT String IO thm
  UNMONICIZE_MAT : List term → List thm → thm → ExceptT String IO thm
  SWAP_HEAD_COL_ROW : Int → thm → ExceptT String IO thm
  SWAP_HEAD_COL : Int → thm → ExceptT String IO thm
  LENGTH_CONV : term → ExceptT String IO thm
  LAST_NZ_CONV : thm → term → ExceptT String IO thm
  NEQ_RULE : thm → ExceptT String IO thm
  NORMAL_LIST_CONV : thm → term → ExceptT String IO thm
  pdiff_tm : term
  GEN_POLY_DIFF_CONV : List term → term → ExceptT String IO thm
  rppeq : Option (IO.Ref thm)
  rpmat : Option (IO.Ref thm)
  REPLACE_POL : thm → thm → ExceptT String IO thm
  UNFACTOR_ISIGN : List term → thm → term → thm → ExceptT String IO thm
  UNFACTOR_ISIGNS : List term → List term → thm → ExceptT String IO thm
  UNFACTOR_MAT : List term → List term → thm → ExceptT String IO thm
  matrix_count : Option (IO.Ref Int)
  splitzero_count : Option (IO.Ref Int)
  splitsigns_count : Option (IO.Ref Int)
  monicize_count : Option (IO.Ref Int)
  reset_counts : Unit → IO Unit
  print_counts : Unit → IO (Int × Int × Int × Int)
  MATRIX : MatrixFn
  SPLITZERO : SplitFn
  SPLITSIGNS : SplitFn
  MONICIZE : MatrixFn
  polynomials : term → Except String (List term)
  BASIC_REAL_QELIM_CONV : List term → ioconv
  REAL_QELIM_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupRqeMainFns [HolBase] (D : RqeMainDeps) :
    ExceptT String IO RqeMainFns := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, BEHEAD, CANON_POLY_DIFF_CONV, COMBINE_TESTFORMS, DEDMATRIX, EL_CONV,
        EVALC_CONV, FINDSIGN, Isign_arg, LIFT_QELIM_CONV, MATCH_EQ_MP, MATINSERT,
        MONIC_CONV, PARITY_CONV, PARTITION_LINE_CONV, PDIVIDES, POLYATOM_CONV,
        POLYNATE_CONV, POLY_DELIST_CONV, POLY_ENLIST_CONV, SIGN_CONST, SIMPLIFY_CONV,
        SPLIT_SIGN, SPLIT_ZERO, WEAKFACTOR_CONV, behead, degree_, dest_all2,
        dest_interpmat, dest_interpsign, dest_mult, dest_poly, duplicate_columns_timer,
        empty_sgns, even_tm, f_tm, head, interpmat_thms, interpsigns_thms2,
        is_constant, mk_all2_interpsigns, mk_interpmat_thm, mk_interpsigns,
        mk_small_numeral, nzero, odd_tm, poly_tm, poly_var, replace_pol_timer, req,
        rge, rgt, rle, rlt, rneq, rzero, sneg_tm, spos_tm, swap_head_col_timer,
        szero_tm, t_tm, unfactor_mat_timer, unmonicize_mat_timer, weakfactor, .. } := D
  let { ALL2, LAST, LENGTH, NEQ, NORMAL_ID, NOT_CONS_NIL, TRUTH, empty_mat,
        factor_neg_even_neg, factor_neg_even_pos, factor_neg_even_zero,
        factor_neg_odd_neg, factor_neg_odd_pos, factor_neg_odd_zero, factor_pos_neg,
        factor_pos_pos, factor_pos_zero, factor_zero_neg, factor_zero_pos,
        factor_zero_zero, gtneg, gtpos, gtzero, ltneg, ltpos, ltzero, main_lem000,
        main_lem001, main_lem002, .. } := D.core1
  -- @@SCOPE END

  -- `try cont mat_thm ex_thms with Isign (false_thm,ex_thms) -> ..`: only
  -- Isign (the failure "Isign", its argument in Isign_arg) is caught
  let TRAPOUT : MatCont → thm → List (term × thm) → term → ExceptT String IO thm ← pure (fun cont mat_thm ex_thms fm =>
    tryCatch (do (← cont mat_thm) ex_thms) (fun x => do
      if x != Isign_tag then throw x
      let (false_thm, ex_thms) ← deref Isign_arg
      let mkEq ← ExceptT.mk _root_.mk_eq
      let ftm ← liftExcept (mkEq (fm, f_tm))
      let fthm ← CONTR ftm false_thm
      let ex_thms' ← liftExcept (sortE (fun x y => xterm_lt y.1 x.1) ex_thms)
      let fthm' ← ex_thms'.foldlM (fun acc e => CHOOSE e acc) fthm
      pure fthm'))

  /- (`subtract_index (get_repeats [1; 2; 1; 2 ; 3])` is in a comment) -/

  let remove_column : Int → thm → ExceptT String IO thm ← pure (fun n isigns_thm => do
    let thms ← interpsigns_thms2 isigns_thm
    let (l, r) ← liftExcept (chop_listI n thms)
    let thms' := l ++ (← liftExcept (tl r))
    mk_interpsigns thms')

  let REMOVE_COLUMN : Int → thm → ExceptT String IO thm ← pure (fun n mat_thm => do
    let (rol_thm, all_thm) ← interpmat_thms mat_thm
    let (_ints, part, _signs) ← liftExcept (dest_all2 (concl all_thm))
    let part_thm ← PARTITION_LINE_CONV (← liftExcept (dest_comb part)).2
    let isigns_thms := CONJUNCTS (← REWRITE_RULE [ALL2, part_thm] all_thm)
    let isigns_thms' ← isigns_thms.mapM (remove_column n)
    let all_thm' ← mk_all2_interpsigns part_thm isigns_thms'
    let all_thm'' ← REWRITE_RULE [← GSYM part_thm] all_thm'
    let mat_thm' ← mk_interpmat_thm rol_thm all_thm''
    pure mat_thm')

  let SETIFY_CONV : thm → ExceptT String IO thm ← pure (fun mat_thm => do
    let (_, pols, _) ← liftExcept (dest_interpmat (concl mat_thm))
    let pols' ← liftExcept (dest_list pols)
    let sols := setify (← liftExcept (dest_list pols))
    let indices ← pols'.mapM (fun p => match index p sols with
      | .ok n => pure (n : Int)
      | .error _ => throw "SETIFY: no index")
    let subtract_cols := subtract_index (get_repeats indices)
    -- `rev_itlist REMOVE_COLUMN subtract_cols mat_thm`
    subtract_cols.foldlM (fun acc n => REMOVE_COLUMN n acc) mat_thm)

  /- (a SETIFY_CONV example and the commented-out duplicate_column and
     DUPLICATE_COLUMN are in rqe_main.ml) -/

  let duplicate_columns : List Int → thm → ExceptT String IO thm ← pure (fun new_cols isigns_thm => do
    let thms ← interpsigns_thms2 isigns_thm
    let thms' ← liftExcept (new_cols.mapM (fun i =>
      if i < 0 then .error "el" else el i.toNat thms))
    mk_interpsigns thms')

  -- rebound below by the timed DUPLICATE_COLUMNS
  let DUPLICATE_COLUMNS : thm → List Int → ExceptT String IO thm ← pure (fun mat_thm ls => do
    if ls.isEmpty then
      if mat_thm == empty_mat then return empty_mat else throw "empty duplication list" else
    let (rol_thm, all_thm) ← interpmat_thms mat_thm
    let (_ints, part, _signs) ← liftExcept (dest_all2 (concl all_thm))
    let part_thm ← PARTITION_LINE_CONV (← liftExcept (dest_comb part)).2
    let isigns_thms := CONJUNCTS (← REWRITE_RULE [ALL2, part_thm] all_thm)
    let isigns_thms' ← isigns_thms.mapM (duplicate_columns ls)
    let all_thm' ← mk_all2_interpsigns part_thm isigns_thms'
    let all_thm'' ← REWRITE_RULE [← GSYM part_thm] all_thm'
    let mat_thm' ← mk_interpmat_thm rol_thm all_thm''
    pure mat_thm')

  let DUPLICATE_COLUMNS : thm → List Int → ExceptT String IO thm ← pure (fun mat_thm ls => do
    let start_time ← sys_time
    let res ← DUPLICATE_COLUMNS mat_thm ls
    plus_dot_eq' duplicate_columns_timer ((← sys_time) - start_time)
    pure res)

  let UNMONICIZE_ISIGN : List term → thm → thm → ExceptT String IO thm ← pure (fun vars monic_thm isign_thm => do
    let (_, _, sign) ← liftExcept (dest_interpsign isign_thm)
    let const ← liftExcept (do return (← dest_mult (← lhs (concl monic_thm))).1)
    let const_thm ← SIGN_CONST const
    let (op, _, _) ← liftExcept (get_binop (concl const_thm))
    let mp_thm ←
      if op == rgt then
        if sign == spos_tm then pure gtpos
        else if sign == sneg_tm then pure gtneg
        else if sign == szero_tm then pure gtzero
        else throw "bad sign"
      else if op == rlt then
        if sign == spos_tm then pure ltpos
        else if sign == sneg_tm then pure ltneg
        else if sign == szero_tm then pure ltzero
        else throw "bad sign"
      else (throw "bad op")
    let monic_thm' ← GEN (← liftExcept (hd vars)) monic_thm
    MATCH_MPL [mp_thm, monic_thm', const_thm, isign_thm])

  let UNMONICIZE_ISIGNS : List term → List thm → thm → ExceptT String IO thm ← pure (fun vars monic_thms isigns_thm => do
    let isign_thms ← interpsigns_thms2 isigns_thm
    let isign_thms' ← map2M (UNMONICIZE_ISIGN vars) monic_thms isign_thms
    mk_interpsigns isign_thms')

  -- rebound below by the timed UNMONICIZE_MAT
  let UNMONICIZE_MAT : List term → List thm → thm → ExceptT String IO thm ← pure (fun vars monic_thms mat_thm => do
    if monic_thms.isEmpty then return mat_thm else
    let (rol_thm, all_thm) ← interpmat_thms mat_thm
    let (_ints, part, _signs) ← liftExcept (dest_all2 (concl all_thm))
    let part_thm ← PARTITION_LINE_CONV (← liftExcept (dest_comb part)).2
    let _consts ← liftExcept (monic_thms.mapM (fun th => do return (← dest_mult (← lhs (concl th))).1))
    let isigns_thms := CONJUNCTS (← REWRITE_RULE [ALL2, part_thm] all_thm)
    let isigns_thms' ← isigns_thms.mapM (UNMONICIZE_ISIGNS vars monic_thms)
    let all_thm' ← mk_all2_interpsigns part_thm isigns_thms'
    let all_thm'' ← REWRITE_RULE [← GSYM part_thm] all_thm'
    let mat_thm' ← mk_interpmat_thm rol_thm all_thm''
    pure mat_thm')

  let UNMONICIZE_MAT : List term → List thm → thm → ExceptT String IO thm ← pure (fun vars monic_thms mat_thm => do
    let start_time ← sys_time
    let res ← UNMONICIZE_MAT vars monic_thms mat_thm
    plus_dot_eq' unmonicize_mat_timer ((← sys_time) - start_time)
    pure res)

  /- (examples are in a comment in rqe_main.ml) -/

  let SWAP_HEAD_COL_ROW : Int → thm → ExceptT String IO thm ← pure (fun i isigns_thm => do
    let s_thms ← interpsigns_thms2 isigns_thm
    -- `insertat i (hd s_thms) (tl s_thms)`, right to left
    let t ← liftExcept (tl s_thms)
    let h ← liftExcept (hd s_thms)
    let s_thms' ← liftExcept (insertat i h t)
    mk_interpsigns s_thms')

  -- rebound below by the timed SWAP_HEAD_COL
  let SWAP_HEAD_COL : Int → thm → ExceptT String IO thm ← pure (fun i mat_thm => do
    let (rol_thm, all_thm) ← interpmat_thms mat_thm
    let (_ints, part, _signs) ← liftExcept (dest_all2 (concl all_thm))
    let part_thm ← PARTITION_LINE_CONV (← liftExcept (dest_comb part)).2
    let isigns_thms := CONJUNCTS (← REWRITE_RULE [ALL2, part_thm] all_thm)
    let isigns_thms' ← isigns_thms.mapM (SWAP_HEAD_COL_ROW i)
    let all_thm' ← mk_all2_interpsigns part_thm isigns_thms'
    mk_interpmat_thm rol_thm all_thm')

  let SWAP_HEAD_COL : Int → thm → ExceptT String IO thm ← pure (fun i mat_thm => do
    let start_time ← sys_time
    let res ← SWAP_HEAD_COL i mat_thm
    plus_dot_eq' swap_head_col_timer ((← sys_time) - start_time)
    pure res)

  -- `try .. with _ -> failwith "LENGTH_CONV"`
  let LENGTH_CONV : term → ExceptT String IO thm ← do
    let alength_tm ← q r"LENGTH:(A list) -> num"
    pure (fun tm => tryCatch (do
      let ty := type_of tm
      let (lty, cty) ← match ← liftExcept (dest_type ty) with
        | (lty, [cty]) => pure (lty, cty)
        | _ => throw "Match_failure"
      if lty != "list" then throw "LENGTH_CONV: not a list" else
      let ltm ← liftExcept (mk_comb (inst [(cty, aty)] alength_tm) tm)
      let lthm ← ExceptT.mk (REWRITE_CONV [LENGTH] ltm)
      MATCH_MP main_lem000 lthm)
      (fun _ => throw "LENGTH_CONV"))

  let LAST_NZ_CONV : thm → term → ExceptT String IO thm ← do
    let alast_tm ← q r"LAST:(A list) -> A"
    pure (fun nz_thm tm => tryCatch (do
      let ty := type_of tm
      let (lty, cty) ← match ← liftExcept (dest_type ty) with
        | (lty, [cty]) => pure (lty, cty)
        | _ => throw "Match_failure"
      if lty != "list" then throw "LAST_NZ_CONV: not a list" else
      let ltm ← liftExcept (mk_comb (inst [(cty, aty)] alast_tm) tm)
      let lthm ← ExceptT.mk (REWRITE_CONV [LAST, NOT_CONS_NIL] ltm)
      MATCH_MPL [main_lem001, nz_thm, lthm])
      (fun _ => throw "LAST_NZ_CONV"))

  let NEQ_RULE : thm → ExceptT String IO thm ← pure (fun thm => do
    let thms := CONJUNCTS main_lem002
    first_can (fun th => MATCH_MP th thm) thms)

  /- (`NEQ_CONV (ARITH_RULE ..)` is in a comment) -/

  let NORMAL_LIST_CONV : thm → term → ExceptT String IO thm ← pure (fun nz_thm tm => do
    let nz_thm' ← NEQ_RULE nz_thm
    let len_thm ← LENGTH_CONV tm
    let last_thm ← LAST_NZ_CONV nz_thm' tm
    let cthm ← CONJ len_thm last_thm
    MATCH_EQ_MP (← GSYM (← REWRITE_RULE [← GSYM NEQ] NORMAL_ID)) cthm)

  /- (an example is in a comment in rqe_main.ml) -/
  let pdiff_tm : term ← q r"poly_diff"
  let GEN_POLY_DIFF_CONV : List term → term → ExceptT String IO thm ← pure (fun vars tm => do
    let thm1 ← ExceptT.mk ((← POLY_ENLIST_CONV vars) tm)
    let (l, _x) ← liftExcept (do dest_poly (← rhs (concl thm1)))
    let thm2 ← ExceptT.mk (CANON_POLY_DIFF_CONV (← liftExcept (mk_comb pdiff_tm l)))
    let thm3 ← CONV_RULE (RAND_CONV (HolMath.Lists.LIST_CONV_IO (POLYNATE_CONV vars))) thm2
    pure thm3)

  /- if \x. p = \x. q, where \x. p is the leading polynomial
     replace p by q in mat_thm, -/

  /- (`let peq,mat_thm = !rppeq,!rpmat` is in a comment) -/
  let loc_rppeq : IO.Ref thm ← IO.mkRef TRUTH
  let loc_rpmat : IO.Ref thm ← IO.mkRef TRUTH
  let rppeq : Option (IO.Ref thm) ← pure (some loc_rppeq)
  let rpmat : Option (IO.Ref thm) ← pure (some loc_rpmat)
  -- rebound below by the timed REPLACE_POL
  let REPLACE_POL : thm → thm → ExceptT String IO thm ← do
    let imat_tm ← q r"interpmat"
    pure (fun peq mat_thm => do
      loc_rppeq.set peq
      loc_rpmat.set mat_thm
      let (pts, pols, sgnll) ← liftExcept (dest_interpmat (concl mat_thm))
      let rep_p ← liftExcept (lhs (concl peq))
      let i ← match (do index rep_p (← dest_list pols) : Except String Nat) with
        | .ok n => pure n
        | .error _ => throw "REPLACE_POL: index"
      let thm1 ← ExceptT.mk (EL_CONV (fun x => (do ExceptT.mk ((← GEN_REWRITE_CONV_NET id [peq]) x)).run) i pols)
      -- `end_itlist (C (curry MK_COMB)) (rev [REFL imat_tm;REFL pts;thm1;REFL sgnll])`
      HolLight.end_itlist (fun x y => MK_COMB (y, x))
        (HolLight.rev [REFL imat_tm, REFL pts, thm1, REFL sgnll]))

  let REPLACE_POL : thm → thm → ExceptT String IO thm ← pure (fun peq mat_thm => do
    let start_time ← sys_time
    let res ← REPLACE_POL peq mat_thm
    plus_dot_eq' replace_pol_timer ((← sys_time) - start_time)
    pure res)

  /- (examples are in a comment in rqe_main.ml) -/

  /- ---------------------------------------------------------------------- -/
  /-  Factoring                                                             -/
  /- ---------------------------------------------------------------------- -/

  let UNFACTOR_ISIGN : List term → thm → term → thm → ExceptT String IO thm ← pure (fun vars xsign_thm pol isign_thm => do
    let x ← liftExcept (hd vars)
    let (k, _pol') := weakfactor x pol
    if k = 0 then return isign_thm else
    let fact_thm ← GEN x (← GSYM (← WEAKFACTOR_CONV x pol))
    let par_thm ← PARITY_CONV (← liftExcept (mk_small_numeral k))
    let (_, _, xsign) ← liftExcept (dest_interpsign xsign_thm)
    let (_, _, psign) ← liftExcept (dest_interpsign isign_thm)
    let (parity, _) ← liftExcept (dest_comb (concl par_thm))
    let k_thm : Unit → ExceptT String IO thm := fun _ => do
      let mkEq ← ExceptT.mk _root_.mk_eq
      ExceptT.mk (HolCore.Tactics.prove HolBase.B
        (← liftExcept (HolCore.Bool.mk_neg (← liftExcept (mkEq ((← liftExcept (mk_small_numeral k)), nzero)))))
        ARITH_TAC)
    if xsign == spos_tm then
      let mp_thm ←
        if psign == spos_tm then pure factor_pos_pos
        else if psign == sneg_tm then pure factor_pos_neg
        else if psign == szero_tm then pure factor_pos_zero
        else throw "bad sign"
      let ret ← BETA_RULE (← MATCH_MPL [mp_thm, xsign_thm, isign_thm])
      MATCH_MP ret fact_thm
    else if xsign == szero_tm then
      let k_thm ← k_thm ()
      let mp_thm ←
        if psign == spos_tm then pure factor_zero_pos
        else if psign == sneg_tm then pure factor_zero_neg
        else if psign == szero_tm then pure factor_zero_zero
        else throw "bad sign"
      let ret ← BETA_RULE (← MATCH_MPL [mp_thm, xsign_thm, isign_thm, k_thm])
      MATCH_MP ret fact_thm
    else if xsign == sneg_tm && parity == even_tm then
      let k_thm ← k_thm ()
      let mp_thm ←
        if psign == spos_tm then pure factor_neg_even_pos
        else if psign == sneg_tm then pure factor_neg_even_neg
        else if psign == szero_tm then pure factor_neg_even_zero
        else throw "bad sign"
      let ret ← BETA_RULE (← MATCH_MPL [mp_thm, xsign_thm, isign_thm, par_thm, k_thm])
      MATCH_MP ret fact_thm
    else if xsign == sneg_tm && parity == odd_tm then
      let k_thm ← k_thm ()
      let mp_thm ←
        if psign == spos_tm then pure factor_neg_odd_pos
        else if psign == sneg_tm then pure factor_neg_odd_neg
        else if psign == szero_tm then pure factor_neg_odd_zero
        else throw "bad sign"
      let ret ← BETA_RULE (← MATCH_MPL [mp_thm, xsign_thm, isign_thm, par_thm, k_thm])
      MATCH_MP ret fact_thm
    else throw "bad something...")

  /- (examples are in a comment in rqe_main.ml) -/

  let UNFACTOR_ISIGNS : List term → List term → thm → ExceptT String IO thm ← pure (fun vars pols isigns_thm => do
    let isign_thms ← interpsigns_thms2 isigns_thm
    -- `map2 (UNFACTOR_ISIGN vars (hd isign_thms)) pols (tl isign_thms)`, right to left
    let t ← liftExcept (tl isign_thms)
    let h ← liftExcept (hd isign_thms)
    let isign_thms' ← map2M (UNFACTOR_ISIGN vars h) pols t
    mk_interpsigns isign_thms')

  -- rebound below by the timed UNFACTOR_MAT
  let UNFACTOR_MAT : List term → List term → thm → ExceptT String IO thm ← pure (fun vars pols mat_thm => do
    let (rol_thm, all_thm) ← interpmat_thms mat_thm
    let (_ints, part, _signs) ← liftExcept (dest_all2 (concl all_thm))
    let part_thm ← PARTITION_LINE_CONV (← liftExcept (dest_comb part)).2
    let isigns_thms := CONJUNCTS (← REWRITE_RULE [ALL2, part_thm] all_thm)
    let isigns_thms' ← isigns_thms.mapM (UNFACTOR_ISIGNS vars pols)
    let all_thm' ← mk_all2_interpsigns part_thm isigns_thms'
    let all_thm'' ← REWRITE_RULE [← GSYM part_thm] all_thm'
    let mat_thm' ← mk_interpmat_thm rol_thm all_thm''
    pure mat_thm')

  let UNFACTOR_MAT : List term → List term → thm → ExceptT String IO thm ← pure (fun vars pols mat_thm => do
    let start_time ← sys_time
    let res ← UNFACTOR_MAT vars pols mat_thm
    plus_dot_eq' unfactor_mat_timer ((← sys_time) - start_time)
    pure res)

  /- (examples are in a comment in rqe_main.ml; message_time is above) -/

  /- ---------------------------------------------------------------------- -/
  /-  Matrix                                                                -/
  /- ---------------------------------------------------------------------- -/

  let loc_matrix_count : IO.Ref Int ← IO.mkRef 0
  let loc_splitzero_count : IO.Ref Int ← IO.mkRef 0
  let loc_splitsigns_count : IO.Ref Int ← IO.mkRef 0
  let loc_monicize_count : IO.Ref Int ← IO.mkRef 0
  let matrix_count : Option (IO.Ref Int) ← pure (some loc_matrix_count)
  let splitzero_count : Option (IO.Ref Int) ← pure (some loc_splitzero_count)
  let splitsigns_count : Option (IO.Ref Int) ← pure (some loc_splitsigns_count)
  let monicize_count : Option (IO.Ref Int) ← pure (some loc_monicize_count)
  let reset_counts : Unit → IO Unit ← pure (fun _ => do
    loc_matrix_count.set 0; loc_splitzero_count.set 0; loc_splitsigns_count.set 0
    loc_monicize_count.set 0)
  let print_counts : Unit → IO (Int × Int × Int × Int) ← pure (fun _ => do
    -- a tuple, right to left
    let m ← loc_monicize_count.get
    let ss ← loc_splitsigns_count.get
    let sz ← loc_splitzero_count.get
    let mc ← loc_matrix_count.get
    pure (mc, sz, ss, m))

  /- (`let vars,dun,pols,cont,sgns,ex_thms,fm = !szvars,..` is in a comment) -/

  -- `let rec MATRIX .. and SPLITZERO .. and SPLITSIGNS .. and MONICIZE ..`:
  -- the four call each other through these refs, set below
  let loc_rMATRIX : IO.Ref MatrixFn ← IO.mkRef (fun _ _ _ _ _ _ => throw "MATRIX")
  let loc_rSPLITZERO : IO.Ref SplitFn ← IO.mkRef (fun _ _ _ _ _ _ _ => throw "SPLITZERO")
  let loc_rSPLITSIGNS : IO.Ref SplitFn ← IO.mkRef (fun _ _ _ _ _ _ _ => throw "SPLITSIGNS")
  let loc_rMONICIZE : IO.Ref MatrixFn ← IO.mkRef (fun _ _ _ _ _ _ => throw "MONICIZE")

  let MATRIX : MatrixFn ← pure (fun vars pols cont sgns ex_thms fm => do
    loc_matrix_count.modify (· + 1)
    if pols.isEmpty then TRAPOUT cont empty_mat [] fm else
    if ← liftExcept (pols.anyM (is_constant vars)) then
      let p ← liftExcept (findM (is_constant vars) pols)
      let i ← match index p pols with
        | .ok n => pure n
        | .error _ => throw "MATRIX: no such pol"
      let (pols1, pols2) ← liftExcept (chop_list i pols)
      let pols' := pols1 ++ (← liftExcept (tl pols2))
      let cont' := MATINSERT vars i (← FINDSIGN vars sgns p) cont
      (← loc_rMATRIX.get) vars pols' cont' sgns ex_thms fm
    else
      let hv ← liftExcept (hd vars)
      let kqs := pols.map (weakfactor hv)
      if ← liftExcept (kqs.anyM (fun (k, q) => do
          if k != 0 then return !(← is_constant vars q) else return false)) then
        let pols' := (← liftExcept (poly_var hv)) :: kqs.map (·.2)
        let _ks := kqs.map (·.1)
        let cont' : MatCont := fun mat_thm => pure (fun ex_thms => do
          (← cont (← UNFACTOR_MAT vars pols mat_thm)) ex_thms)
        (← loc_rMATRIX.get) vars pols' cont' sgns ex_thms fm
      else
      let d ← liftExcept (pols.foldrM (fun p acc => do return max (← degree_ vars p) acc) (-1))
      let p ← liftExcept (findM (fun p => do return (← degree_ vars p) == d) pols)
      let pl_thm ← ExceptT.mk ((← POLY_ENLIST_CONV vars) p)
      let pl ← liftExcept (rhs (concl pl_thm))
      let (_l, _x) ← liftExcept (dest_poly pl)
      let pdiff_thm ← GEN_POLY_DIFF_CONV vars p
      let p'l ← liftExcept (rhs (concl pdiff_thm))
      let p' ← liftExcept (do mk_comb (← mk_comb poly_tm p'l) hv)
      let p'thm ← ExceptT.mk ((POLY_DELIST_CONV THENC (POLYNATE_CONV vars)) p')
      let p'c ← liftExcept (rhs (concl p'thm))
      let hdp' ← liftExcept (do last (← dest_list p'l))
      let sign_thm ← FINDSIGN vars sgns hdp'
      let normal_thm ← NORMAL_LIST_CONV sign_thm p'l
      let i ← match index p pols with
        | .ok n => pure n
        | .error _ => throw "MATRIX: no such pol1"
      let qs ← liftExcept (do
        let (p1, p2) ← chop_list i pols
        return p'c :: p1 ++ (← tl p2))
      let (gs, div_thms) := unzip (← qs.mapM (PDIVIDES vars sgns p))
      -- `let cont' mat_thm = cont (SWAP_HEAD_COL i mat_thm)` (one argument)
      let cont' : MatCont := fun mat_thm => do cont (← SWAP_HEAD_COL i mat_thm)
      let dedcont : MatCont := fun mat_thm => pure (fun ex_thms =>
        DEDMATRIX vars sgns div_thms pdiff_thm normal_thm
          (fun m ex => do (← cont' m) ex) mat_thm ex_thms)
      (← loc_rSPLITZERO.get) vars qs gs dedcont sgns ex_thms fm)

  let SPLITZERO : SplitFn ← pure (fun vars dun pols cont sgns ex_thms fm => do
    loc_splitzero_count.modify (· + 1)
    match pols with
    | [] => (← loc_rSPLITSIGNS.get) vars [] dun cont sgns ex_thms fm
    | p :: ops =>
      if p == rzero then
        let cont' : MatCont := fun mat_thm => pure (fun ex_thms => do
          (← MATINSERT vars dun.length (REFL rzero) cont mat_thm) ex_thms)
        (← loc_rSPLITZERO.get) vars dun ops cont' sgns ex_thms fm
      else
        let hp ← liftExcept (behead vars p)
        let h ← liftExcept (head vars p)
        let nzcont : SignCont := fun sgns ex_thms => do
          (← loc_rSPLITZERO.get) vars (dun ++ [p]) ops cont sgns ex_thms fm
        let zcont : SignCont := fun sgns ex_thms => do
          let zthm ← FINDSIGN vars sgns h
          let b_thm ← GSYM (← BEHEAD vars zthm p)
          let lam_thm ← liftExcept (HolCore.Kernel.ABS (← liftExcept (hd vars)) b_thm)
          let cont' : MatCont := fun mat_thm => pure (fun ex_thms => do
            let mat_thm' ← REPLACE_POL lam_thm mat_thm
            let mat_thm'' ← MATCH_EQ_MP mat_thm' mat_thm
            (← cont mat_thm'') ex_thms)
          (← loc_rSPLITZERO.get) vars dun (hp :: ops) cont' sgns ex_thms fm
        SPLIT_ZERO (← liftExcept (tl vars)) sgns (← liftExcept (head vars p)) zcont nzcont ex_thms)

  let SPLITSIGNS : SplitFn ← pure (fun vars dun pols cont sgns ex_thms fm => do
    loc_splitsigns_count.modify (· + 1)
    match pols with
    | [] => (← loc_rMONICIZE.get) vars dun cont sgns ex_thms fm
    /- `[] -> MATRIX vars dun cont sgns ex_thms fm` is in a comment -/
    | p :: ops =>
      let cont' : SignCont := fun sgns ex_thms => do
        (← loc_rSPLITSIGNS.get) vars (dun ++ [p]) ops cont sgns ex_thms fm
      SPLIT_SIGN (← liftExcept (tl vars)) sgns (← liftExcept (head vars p)) cont' cont' ex_thms)

  let MONICIZE : MatrixFn ← pure (fun vars pols cont sgns ex_thms fm => do
    loc_monicize_count.modify (· + 1)
    let monic_thms ← pols.mapM (fun p => ExceptT.mk (MONIC_CONV vars p))
    let monic_pols ← liftExcept (monic_thms.mapM (fun th => rhs (concl th)))
    let sols := setify monic_pols
    let indices ← monic_pols.mapM (fun p => match index p sols with
      | .ok n => pure (n : Int)
      | .error _ => throw "MONICIZE: no such pol")
    let transform : thm → ExceptT String IO thm := fun mat_thm => do
      let mat_thm' ← DUPLICATE_COLUMNS mat_thm indices
      /- `mat_thm'` is in a comment -/
      UNMONICIZE_MAT vars monic_thms mat_thm'
    let cont' : MatCont := fun mat_thm => pure (fun ex_thms => do
      (← cont (← transform mat_thm)) ex_thms)
    (← loc_rMATRIX.get) vars sols cont' sgns ex_thms fm)

  loc_rMATRIX.set MATRIX
  loc_rSPLITZERO.set SPLITZERO
  loc_rSPLITSIGNS.set SPLITSIGNS
  loc_rMONICIZE.set MONICIZE

  /- (examples are in a comment in rqe_main.ml) -/

  /- ---------------------------------------------------------------------- -/
  /-  Set up RQE                                                            -/
  /- ---------------------------------------------------------------------- -/

  let polynomials : term → Except String (List term) ← pure (fun tm => do
    return setify (← polynomials.go t_tm f_tm [rlt, rgt, rle, rge, req, rneq] tm))

  /- (an example is in a comment in rqe_main.ml) -/

  let BASIC_REAL_QELIM_CONV : List term → ioconv ← pure (fun vars fm => ExceptT.run do
    let (x, bod) ← liftExcept (dest_exists fm)
    let pols ← liftExcept (polynomials bod)
    let cont : MatCont := fun mat_thm => pure (fun ex_thms => do
      let ex_thms' ← liftExcept (sortE (fun x y => xterm_lt y.1 x.1) ex_thms)
      let comb_thm ← COMBINE_TESTFORMS x mat_thm bod
      let comb_thm' ← ex_thms'.foldlM (fun acc e => CHOOSE e acc) comb_thm
      pure comb_thm')
    let ret_thm ← SPLITZERO (x :: vars) [] pols cont empty_sgns [] fm
    PURE_REWRITE_RULE [NEQ] ret_thm)

  let REAL_QELIM_CONV : ioconv ← pure (fun fm => ExceptT.run do
    reset_counts ()
    ExceptT.mk (((LIFT_QELIM_CONV (fun vs t => (POLYATOM_CONV vs t).run)
      (EVALC_CONV THENC SIMPLIFY_CONV) BASIC_REAL_QELIM_CONV) THENC EVALC_CONV THENC
      SIMPLIFY_CONV) fm))

  /- ---------------------------------------------------------------------- -/
  /-  timers                                                                -/
  /- ---------------------------------------------------------------------- -/

  -- @@RETURN BEGIN
  return { TRAPOUT, remove_column, REMOVE_COLUMN, SETIFY_CONV, duplicate_columns,
           DUPLICATE_COLUMNS, UNMONICIZE_ISIGN, UNMONICIZE_ISIGNS, UNMONICIZE_MAT,
           SWAP_HEAD_COL_ROW, SWAP_HEAD_COL, LENGTH_CONV, LAST_NZ_CONV, NEQ_RULE,
           NORMAL_LIST_CONV, pdiff_tm, GEN_POLY_DIFF_CONV, rppeq, rpmat, REPLACE_POL,
           UNFACTOR_ISIGN, UNFACTOR_ISIGNS, UNFACTOR_MAT, matrix_count, splitzero_count,
           splitsigns_count, monicize_count, reset_counts, print_counts, MATRIX,
           SPLITZERO, SPLITSIGNS, MONICIZE, polynomials, BASIC_REAL_QELIM_CONV,
           REAL_QELIM_CONV }
  -- @@RETURN END

end HolRQE.RqeMain
