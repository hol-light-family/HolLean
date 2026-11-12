/- ========================================================================= -/
/- Rqe: inserting a row of constant signs into a sign matrix.              -/
/- ========================================================================= -/
/- File: HolRQE/Matinsert.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/matinsert.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml, Rqe/num_calc_simp.ml, Rqe/asym.ml, Rqe/rol.ml, Rqe/poly_ext.ml, Rqe/simplify.ml, Rqe/lift_qelim.ml, Rqe/defs.ml, Rqe/testform_thms.ml, Rqe/condense_thms.ml, Rqe/inferisign_thms.ml, Rqe/matinsert_thms.ml, Rqe/signs_thms.ml, Rqe/inferpsign_thms.ml, Rqe/dedmatrix_thms.ml, Rqe/pdivides_thms.ml, Rqe/main_thms.ml, Rqe/work_thms.ml, Rqe/testform.ml, Rqe/condense.ml, Rqe/inferisign.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.Matinsert fills them).

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

namespace HolRQE.Matinsert

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALL2 LENGTH PARTITION_LINE_LENGTH TRUTH all2_thm interpsign matinsert_lem0 : thm)
  deriving Inhabited

/-- What matinsert.ml uses from Session besides theorems. -/
structure MatinsertDeps where
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
  t_tm : term
  nle : term
  matinsert_timer : Option (IO.Ref Float)
  ARITH_SIMP_CONV : List thm → ioconv
  dest_interpsign : thm → Except String (term × term × term)
  interpsigns_thms2 : thm → ExceptT String IO (List thm)
  mk_interpsigns : List thm → ExceptT String IO thm
  PARTITION_LINE_CONV : term → ExceptT String IO thm
  interpmat_thms : thm → ExceptT String IO (thm × thm)
  mk_interpmat_thm : thm → thm → ExceptT String IO thm
  mk_all2_interpsigns : thm → List thm → ExceptT String IO thm
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

/-- The continuations of the decision procedure (`cont` in matinsert.ml and
    rqe_main.ml): applied to a matrix theorem, then to the list of
    existential witnesses.  OCaml applies them one argument at a time, and
    the first application may already do work (and fail), so it is a
    computation here. -/
abbrev MatCont := thm → ExceptT String IO (List (term × thm) → ExceptT String IO thm)

/-- mk_suc's recursion, given its `zero` and `suc`. -/
partial def mk_suc.go (zero suc : term) (n : Int) : Except String term :=
  if n = 0 then .ok zero else do mk_comb suc (← mk_suc.go zero suc (n - 1))



/- ---------------------------------------------------------------------- -/
/-  MATINSERT (matinsert.ml 1-125)                                        -/
/- ---------------------------------------------------------------------- -/

structure MatinsertFns where
  -- @@FIELDS
  ROWINSERT : Int → thm → thm → ExceptT String IO thm
  MATINSERT : List term → Int → thm → MatCont → MatCont
  mk_suc : Int → Except String term
  MK_SUC : Int → ExceptT String IO thm
  PL_LENGTH : term → ExceptT String IO thm
  MK_LT : Int × Int → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupMatinsertFns [HolBase] (D : MatinsertDeps) :
    ExceptT String IO MatinsertFns := do
  -- @@SCOPE BEGIN
  let { ARITH_SIMP_CONV, ARITH_TAC, PARTITION_LINE_CONV, dest_interpsign,
        interpmat_thms, interpsigns_thms2, matinsert_timer, mk_all2_interpsigns,
        mk_interpmat_thm, mk_interpsigns, mk_small_numeral, nle, t_tm, .. } := D
  let { ALL2, LENGTH, PARTITION_LINE_LENGTH, TRUTH, interpsign, matinsert_lem0, .. } := D.core1
  -- @@SCOPE END

  let ROWINSERT : Int → thm → thm → ExceptT String IO thm ← do
    let lxt ← q r"\x:real. T"
    pure (fun i const_thm interpsigns_thm => do
      let isigns_thms ← interpsigns_thms2 interpsigns_thm
      let isigns_thm ← liftExcept (hd isigns_thms)
      let (set, _, _) ←
        if concl isigns_thm == t_tm then pure (lxt, t_tm, t_tm) else
          liftExcept (dest_interpsign (← liftExcept (hd isigns_thms)))
      let const_thm' ← MATCH_MP (← ISPEC set matinsert_lem0) const_thm
      let const_thm'' ← PURE_REWRITE_RULE [← GSYM interpsign] const_thm'
      let isigns_thms' ← liftExcept (insertat i const_thm'' isigns_thms)
      let isigns_thms'' ← if isigns_thm == TRUTH then liftExcept (butlast isigns_thms') else pure isigns_thms'
      mk_interpsigns isigns_thms'')

  -- rebound below by the timed MATINSERT
  let MATINSERT : List term → Int → thm → MatCont → MatCont ← pure (fun vars i const_thm cont mat_thm => do
    let const_thm' ← GEN (← liftExcept (hd vars)) const_thm
    let (rol_thm, all2_thm) ← interpmat_thms mat_thm
    let part_thm ← PARTITION_LINE_CONV (← liftExcept (dest_comb (concl rol_thm))).2
    let isigns_thms := CONJUNCTS (← REWRITE_RULE [ALL2, part_thm] all2_thm)
    let isigns_thms' ← isigns_thms.mapM (ROWINSERT i const_thm')
    let all2_thm' ← mk_all2_interpsigns part_thm isigns_thms'
    let mat_thm' ← mk_interpmat_thm rol_thm all2_thm'
    cont mat_thm')

  /- (examples are in matinsert.ml) -/

  let mk_suc : Int → Except String term ← do
    let zero ← q r"0"
    let suc ← q r"SUC"
    pure (mk_suc.go zero suc)

  -- `let rec MK_SUC = let f n = .. in .. (a table of 0..100, built now) ..
  -- in fun n -> try Hashtbl.find suc_tbl n with _ -> f n`
  let MK_SUC : Int → ExceptT String IO thm ← do
    let f (n : Int) : ExceptT String IO thm := do
      let mkEq ← ExceptT.mk _root_.mk_eq
      -- `mk_eq(mk_small_numeral n, mk_suc n)`, right to left
      let s ← liftExcept (mk_suc n)
      let m ← liftExcept (mk_small_numeral n)
      ExceptT.mk (HolCore.Tactics.prove HolBase.B (← liftExcept (mkEq (m, s))) ARITH_TAC)
    let size : Int := 100
    let range := List.map Int.ofNat (List.range (size.toNat + 1))
    let ths ← range.mapM f
    let suc_tbl := range.zip ths
    pure (fun n => match suc_tbl.lookup n with
      | some th => pure th
      | none => f n)

  let PL_LENGTH : term → ExceptT String IO thm ← do
    let pl_tm ← q r"partition_line"
    let len_tm ← q r"LENGTH:(real -> bool) list -> num"
    pure (fun pts => do
      let lpts ← liftExcept (do mk_comb len_tm (← mk_comb pl_tm pts))
      let lthm ← ExceptT.mk (ARITH_SIMP_CONV [PARTITION_LINE_LENGTH, LENGTH] lpts)
      let pts' := (← liftExcept (dest_eq (concl lthm))).2
      let n ← liftExcept (HolMath.Nums.dest_small_numeral pts')
      let suc_thm ← MK_SUC n
      TRANS lthm suc_thm)

  let MK_LT : Int × Int → ExceptT String IO thm ← do
    let f (p : Int × Int) : ExceptT String IO thm := do
      let (n1, n2) := p
      -- `mk_binop nle (mk_suc n1) (mk_suc n2)`, right to left
      let s2 ← liftExcept (mk_suc n2)
      let s1 ← liftExcept (mk_suc n1)
      ExceptT.mk (HolCore.Tactics.prove HolBase.B
        (← liftExcept (do (← mk_binop nle s1) s2)) ARITH_TAC)
    let size1 : Int := 20
    let size2 : Int := 20
    let range1 := List.map Int.ofNat (List.range (size1.toNat + 1))
    let range2 := List.map Int.ofNat (List.range (size2.toNat + 1))
    let range := filter (fun (x, y) => x ≤ y) (allpairs (fun x y => (x, y)) range1 range2)
    let ths ← range.mapM f
    let suc_tbl := range.zip ths
    pure (fun p => match suc_tbl.lookup p with
      | some th => pure th
      | none => f p)

  let MATINSERT : List term → Int → thm → MatCont → MatCont ← pure (fun vars i const_thm cont mat_thm => do
    let start_time ← sys_time
    let res ← MATINSERT vars i const_thm cont mat_thm
    plus_dot_eq' matinsert_timer ((← sys_time) - start_time)
    pure res)

  -- @@RETURN BEGIN
  return { ROWINSERT, MATINSERT, mk_suc, MK_SUC, PL_LENGTH, MK_LT }
  -- @@RETURN END

end HolRQE.Matinsert
