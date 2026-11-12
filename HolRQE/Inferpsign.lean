/- ========================================================================= -/
/- Rqe: inferring the signs of a polynomial at points from the remainders  -/
/- ========================================================================= -/
/- File: HolRQE/Inferpsign.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/inferpsign.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml, Rqe/num_calc_simp.ml, Rqe/asym.ml, Rqe/rol.ml, Rqe/poly_ext.ml, Rqe/simplify.ml, Rqe/lift_qelim.ml, Rqe/defs.ml, Rqe/testform_thms.ml, Rqe/condense_thms.ml, Rqe/inferisign_thms.ml, Rqe/matinsert_thms.ml, Rqe/signs_thms.ml, Rqe/inferpsign_thms.ml, Rqe/dedmatrix_thms.ml, Rqe/pdivides_thms.ml, Rqe/main_thms.ml, Rqe/work_thms.ml, Rqe/testform.ml, Rqe/condense.ml, Rqe/inferisign.ml, Rqe/matinsert.ml, Rqe/signs.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.Inferpsign fills them).

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

namespace HolRQE.Inferpsign

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALL2 APPEND BUTLAST EVEN EVEN_DIV_LEM GT_DIV_LEM HD INFERPSIGN_MATINSERT_THM
   INFERPSIGN_NEG_EVEN INFERPSIGN_NEG_ODD_POS INFERPSIGN_POS_EVEN
   INFERPSIGN_POS_ODD_POS INFERPSIGN_ZERO_EVEN INFERPSIGN_ZERO_ODD_POS LENGTH
   MAP MAP2 NOT_CONS_NIL NOT_EVEN NOT_ODD ODD REMOVE_LAST REPLICATE TL TRUTH
   interpsigns ips_gt_nz_thm ips_lt_nz_thm one pow t1 unknown_thm : thm)
  deriving Inhabited

/-- What inferpsign.ml uses from Session besides theorems. -/
structure InferpsignDeps where
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
  nm : term
  np : term
  even_tm : term
  odd_tm : term
  PARITY_CONV : term → ExceptT String IO thm
  rneq : term
  rlt : term
  rgt : term
  rm : term
  dest_mult : term → Except String (term × term)
  dest_pow : term → Except String (term × term)
  dest_plus : term → Except String (term × term)
  HD_CONV : ioconv → ioconv
  inferpsign_timer : Option (IO.Ref Float)
  ARITH_SIMP_CONV : List thm → ioconv
  sneg_tm : term
  spos_tm : term
  szero_tm : term
  dest_interpsign : thm → Except String (term × term × term)
  interpsigns_thms2 : thm → ExceptT String IO (List thm)
  dest_interpsigns : thm → Except String (term × term × term)
  mk_interpsigns : List thm → ExceptT String IO thm
  PARTITION_LINE_CONV : term → ExceptT String IO thm
  dest_interpmat : term → Except String (term × term × term)
  interpmat_thms : thm → ExceptT String IO (thm × thm)
  mk_interpmat_thm : thm → thm → ExceptT String IO thm
  mk_all2_interpsigns : thm → List thm → ExceptT String IO thm
  MK_SUC : Int → ExceptT String IO thm
  FINDSIGN : List term → List thm → term → ExceptT String IO thm
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

/-- rqe_lib.ml's `get_index` with a predicate that can fail (as in OCaml,
    the predicate's failure passes through); "get_index" when nothing
    satisfies it. -/
def get_indexM {α : Type} (p : α → Except String Bool) (l : List α) : Except String Int :=
  let rec go : List α → Int → Except String Int
    | [], _ => .error "get_index"
    | h :: t, n => do if ← p h then pure n else go t (n + 1)
  go l 0

/-- OCaml's `can f x`. -/
def canE {α β : Type} (f : α → Except String β) (x : α) : Bool :=
  match f x with | .ok _ => true | .error _ => false

/-- lib.ml's `funpow n f x` for a rule that can fail. -/
def funpowM {α : Type} : Nat → (α → ExceptT String IO α) → α → ExceptT String IO α
  | 0, _, x => pure x
  | n + 1, f, x => do funpowM n f (← f x)



/- ---------------------------------------------------------------------- -/
/-  INFERPSIGN (inferpsign.ml 1-310; its examples are in a comment there) -/
/- ---------------------------------------------------------------------- -/

structure InferpsignFns where
  -- @@FIELDS
  isign_eq_zero : thm → Except String Bool
  isign_lt_zero : thm → Except String Bool
  isign_gt_zero : thm → Except String Bool
  inferpsign_row : List term → List thm → thm → thm → List thm → ExceptT String IO thm
  split_interpsigns : thm → ExceptT String IO (thm × thm)
  INFERPSIGN : List term → List thm → thm → List thm → ExceptT String IO thm
  MK_REP : term → ExceptT String IO thm
  INSERT_UNKNOWN_COL : thm → term → ExceptT String IO thm
  REMOVE_QS : thm → ExceptT String IO thm
  SPLIT_LIST : Nat → term → hol_type → ExceptT String IO thm
  prove_nonzero : thm → ExceptT String IO thm
  INFERPT : List term → List thm → thm → List thm → Int → ExceptT String IO thm
  INFERPTS : List term → List thm → thm → List thm → ExceptT String IO thm
  itvars : Option (IO.Ref (List term))
  itsgns : Option (IO.Ref (List thm))
  itmat : Option (IO.Ref thm)
  itdivs : Option (IO.Ref (List thm))
  INFERPSIGN2 : List term → List thm → thm → List thm → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupInferpsignFns [HolBase] (D : InferpsignDeps) :
    ExceptT String IO InferpsignFns := do
  -- @@SCOPE BEGIN
  let { ARITH_SIMP_CONV, FINDSIGN, HD_CONV, MK_SUC, PARITY_CONV, PARTITION_LINE_CONV,
        dest_interpmat, dest_interpsign, dest_interpsigns, dest_mult, dest_plus,
        dest_pow, even_tm, inferpsign_timer, interpmat_thms, interpsigns_thms2,
        mk_all2_interpsigns, mk_interpmat_thm, mk_interpsigns, nm, np, rgt, rlt, rm,
        rneq, sneg_tm, spos_tm, szero_tm, .. } := D
  let { ALL2, APPEND, BUTLAST, EVEN, EVEN_DIV_LEM, GT_DIV_LEM, HD,
        INFERPSIGN_MATINSERT_THM, INFERPSIGN_NEG_EVEN, INFERPSIGN_NEG_ODD_POS,
        INFERPSIGN_POS_EVEN, INFERPSIGN_POS_ODD_POS, INFERPSIGN_ZERO_EVEN,
        INFERPSIGN_ZERO_ODD_POS, LENGTH, MAP, MAP2, NOT_CONS_NIL, NOT_EVEN, NOT_ODD,
        ODD, REMOVE_LAST, REPLICATE, TL, TRUTH, interpsigns, ips_gt_nz_thm,
        ips_lt_nz_thm, unknown_thm, .. } := D.core1
  -- @@SCOPE END

  let isign_eq_zero : thm → Except String Bool ← pure (fun thm => do
    let (_, _, sign) ← dest_interpsign thm
    pure (sign == szero_tm))

  let isign_lt_zero : thm → Except String Bool ← pure (fun thm => do
    let (_, _, sign) ← dest_interpsign thm
    pure (sign == sneg_tm))

  let isign_gt_zero : thm → Except String Bool ← pure (fun thm => do
    let (_, _, sign) ← dest_interpsign thm
    pure (sign == spos_tm))

  /- (`let p_thm,q_thm = ith 1 split_thms` is in a comment) -/
  let inferpsign_row : List term → List thm → thm → thm → List thm → ExceptT String IO thm ← pure (fun vars sgns p_thm q_thm div_thms => do
    let pthms ← (← interpsigns_thms2 p_thm).mapM (fun th => do BETA_RULE (← PURE_REWRITE_RULE [interpsigns] th))
    let qthms ← (← interpsigns_thms2 q_thm).mapM (fun th => do BETA_RULE (← PURE_REWRITE_RULE [interpsigns] th))
    let (_, set, _) ← liftExcept (dest_interpsigns p_thm)
    if canE (get_indexM isign_eq_zero) pthms then /- there's a zero -/
      let ind ← liftExcept (get_indexM isign_eq_zero pthms)
      let pthm ← liftExcept (ith ind pthms)
      let qthm ← liftExcept (ith ind qthms)
      let div_thm ← liftExcept (ith ind div_thms)
      let div_thm' ← GEN (← liftExcept (hd vars)) div_thm
      let (aks, pqr) ← liftExcept (dest_eq (concl div_thm))
      let (ak, _s) ← liftExcept (dest_mult aks)
      let (a, k) ← liftExcept (dest_pow ak)
      let (pq, _r) ← liftExcept (dest_plus pqr)
      let (_p, _q) ← liftExcept (dest_mult pq)
      let parity_thm ← PARITY_CONV k
      let evenp := (← liftExcept (dest_comb (concl parity_thm))).1 == even_tm
      let sign_thm ← FINDSIGN vars sgns a
      let (op, _, _) ← liftExcept (get_binop (concl sign_thm))
      if evenp then
        let nz_thm ←
          if op == rlt then MATCH_MP ips_lt_nz_thm sign_thm
          else if op == rgt then MATCH_MP ips_gt_nz_thm sign_thm
          else if op == rneq then pure sign_thm
          else throw "inferpsign: 0"
        let imp_thms :=
          CONJUNCTS (← ISPEC set (← MATCH_MPL [EVEN_DIV_LEM, div_thm', nz_thm, parity_thm]))
        let (_, _, qsign) ← liftExcept (dest_interpsign qthm)
        let mp_thm ←
          if qsign == sneg_tm then liftExcept (ith 0 imp_thms)
          else if qsign == spos_tm then liftExcept (ith 1 imp_thms)
          else if qsign == szero_tm then liftExcept (ith 2 imp_thms)
          else throw "inferpsign: 1"
        let final_thm ← MATCH_MPL [mp_thm, pthm, qthm]
        mk_interpsigns (final_thm :: pthms)
      else /- k is odd -/
        if op == rgt then /- a > &0 -/
          let imp_thms :=
            CONJUNCTS (← ISPEC set (← MATCH_MPL [GT_DIV_LEM, div_thm', sign_thm]))
          let (_, _, qsign) ← liftExcept (dest_interpsign qthm)
          let mp_thm ←
            if qsign == sneg_tm then liftExcept (ith 0 imp_thms)
            else if qsign == spos_tm then liftExcept (ith 1 imp_thms)
            else if qsign == szero_tm then liftExcept (ith 2 imp_thms)
            else throw "inferpsign: 1"
          let final_thm ← MATCH_MPL [mp_thm, pthm, qthm]
          mk_interpsigns (final_thm :: pthms)
        else
          throw "inferpsign: shouldn`t reach this point with an odd power and negative sign!  See PDIVIDES and return the correct div_thm"
    else /- no zero -/
      let p := (← liftExcept (dest_mult (← liftExcept (lhs (concl (← liftExcept (hd div_thms))))))).2
      let p1 ← liftExcept (mk_abs (← liftExcept (hd vars)) p)
      let pthm ← ISPECL [set, p1] unknown_thm
      mk_interpsigns (pthm :: pthms))

  /- (the doc comment for split_interpsigns is in inferpsign.ml) -/
  let split_interpsigns : thm → ExceptT String IO (thm × thm) ← pure (fun thm => do
    let thms ← interpsigns_thms2 thm
    let n := thms.length / 2
    let (l, r) ← liftExcept (chop_list n thms)
    -- the pair's components, right to left
    let r' ← mk_interpsigns r
    let l' ← mk_interpsigns l
    pure (l', r'))

  -- rebound below by the timed INFERPSIGN
  let INFERPSIGN : List term → List thm → thm → List thm → ExceptT String IO thm ← pure (fun vars sgns mat_thm div_thms => do
    let (_pts, pols, _signs) ← liftExcept (dest_interpmat (concl mat_thm))
    let _n := (← liftExcept (dest_list pols)).length / 2
    let (rol_thm, sgn_thm) ← interpmat_thms mat_thm
    let part_thm ← PARTITION_LINE_CONV (← liftExcept (dest_comb (concl rol_thm))).2
    let conj_thms := CONJUNCTS (← REWRITE_RULE [ALL2, part_thm] sgn_thm)
    let split_thms ← conj_thms.mapM split_interpsigns
    let conj_thms' ← split_thms.mapM (fun (x, y) => inferpsign_row vars sgns x y div_thms)
    let all_thm ← mk_all2_interpsigns part_thm conj_thms'
    let mat_thm' ← mk_interpmat_thm rol_thm all_thm
    pure mat_thm')

  /- ---------------------------------------------------------------------- -/
  /-  Opt                                                                   -/
  /- ---------------------------------------------------------------------- -/

  let MK_REP : term → ExceptT String IO thm ← do
    let rep_tm ← q r"REPLICATE:num -> sign -> sign list"
    let len_tm ← q r"LENGTH:real list -> num"
    let one ← q r"1"
    let two ← q r"2"
    let unknown ← q r"Unknown"
    pure (fun pts => do
      let num ← liftExcept (do
        (← mk_binop np (← (← mk_binop nm two) (← mk_comb len_tm pts))) one)
      let len := (← liftExcept (dest_list pts)).length
      let num2 ← MK_SUC (2 * len + 1)
      let lthm ← ExceptT.mk (ARITH_SIMP_CONV [LENGTH] num)
      let lthm2 ← TRANS lthm num2
      let lthm3 ← AP_THM (← AP_TERM rep_tm lthm2) unknown
      REWRITE_RULE [REPLICATE] lthm3)

  let INSERT_UNKNOWN_COL : thm → term → ExceptT String IO thm ← pure (fun mat_thm p => do
    let (pts, _, _) ← liftExcept (dest_interpmat (concl mat_thm))
    let rep_thm ← MK_REP pts
    let mat_thm' ← MATCH_MP INFERPSIGN_MATINSERT_THM mat_thm
    let mat_thm'' ← PURE_REWRITE_RULE [MAP2, rep_thm] mat_thm'
    ISPEC p mat_thm'')

  let REMOVE_QS : thm → ExceptT String IO thm ← pure (fun mat_thm => do
    let (_, pols, _) ← liftExcept (dest_interpmat (concl mat_thm))
    let len := (← liftExcept (dest_list pols)).length
    if !(len % 2 == 1) then throw "odd pols?" else
    let mat_thm' ← funpowM (len / 2) (MATCH_MP REMOVE_LAST) mat_thm
    REWRITE_RULE [MAP, BUTLAST, NOT_CONS_NIL, TL, HD] mat_thm')

  let SPLIT_LIST : Nat → term → hol_type → ExceptT String IO thm ← pure (fun n l ty => do
    let l' ← liftExcept (dest_list l)
    let (l1', l2') ← liftExcept (chop_list n l')
    -- `(mk_list(l1',ty),mk_list(l2',ty))`, right to left
    let l2 ← ExceptT.mk (HolMath.Lists.mk_list l2' ty)
    let l1 ← ExceptT.mk (HolMath.Lists.mk_list l1' ty)
    let app_tm ← ExceptT.mk (mk_const "APPEND" [(ty, aty)])
    let l3 ← liftExcept (do mk_comb (← mk_comb app_tm l1) l2)
    SYM (← ExceptT.mk (REWRITE_CONV [APPEND] l3)))

  /- (`let thm = asign` is in a comment) -/

  let prove_nonzero : thm → ExceptT String IO thm ← pure (fun thm => do
    let (op, _, _) ← liftExcept (get_binop (concl thm))
    if op == rgt then MATCH_MP ips_gt_nz_thm thm
    else if op == rlt then MATCH_MP ips_lt_nz_thm thm
    else if op == rneq then pure thm
    else throw "prove_nonzero: bad op")

  /- (`let mat_thm = mat_thm'` and `let ind = 7` are in a comment) -/

  let INFERPT : List term → List thm → thm → List thm → Int → ExceptT String IO thm ← do
    let _unknown ← q r"Unknown"
    let zero ← q r"Zero"
    let pos ← q r"Pos"
    let neg ← q r"Neg"
    let pow ← q r"(pow)"
    let even_tm ← q r"(EVEN)"
    let odd_tm ← q r"(ODD)"
    let rr_ty ← qty "real -> real"
    let sl_ty ← qty "sign list"
    let s_ty ← qty "sign"
    let _imat ← q r"interpmat"
    let rr_length ← ExceptT.mk (mk_const "LENGTH" [(rr_ty, aty)])
    let s_length ← ExceptT.mk (mk_const "LENGTH" [(s_ty, aty)])
    let sl_length ← ExceptT.mk (mk_const "LENGTH" [(sl_ty, aty)])
    let imat ← q r"interpmat"
    pure (fun vars sgns mat_thm div_thms ind => do
      let (pts, pols, signs) ← liftExcept (dest_interpmat (concl mat_thm))
      let pols' ← liftExcept (dest_list pols)
      let signsl ← liftExcept (dest_list signs)
      let signs' ← liftExcept (signsl.mapM dest_list)
      let pols_len := (← liftExcept (hd signs')).length
      let pols_len2 := pols_len / 2
      let pt_sgnl ← liftExcept (ith ind signsl)
      let pt_sgns ← liftExcept (ith ind signs')
      let zind ← liftExcept (index zero pt_sgns)
      if zind > pols_len2 then return mat_thm else /- return if not a zero of a p, only a q -/
      let psgn ← liftExcept (ith (pols_len2 + zind) pt_sgns)
      let div_thm ← liftExcept (ith ((zind : Int) - 1) div_thms)
      let (a, n) ← liftExcept (do
        dest_binop pow (← dest_binop rm (← lhs (concl div_thm))).1)
      let asign ← FINDSIGN vars sgns a
      let (_op, _, _) ← liftExcept (get_binop (concl asign))
      let par_thm ← PARITY_CONV n
      let par := (← liftExcept (dest_comb (concl par_thm))).1
      let mp_thm ←
        /- note: by def of PDIVIDES, we can`t have
           negative sign and odd power at this point -/
        /- n is even -/
        if par == even_tm then
          if psgn == pos then pure INFERPSIGN_POS_EVEN
          else if psgn == neg then pure INFERPSIGN_NEG_EVEN
          else if psgn == zero then pure INFERPSIGN_ZERO_EVEN
          else throw "INFERPT: bad sign"
        else /- n is odd -/
          if psgn == pos then pure INFERPSIGN_POS_ODD_POS
          else if psgn == neg then pure INFERPSIGN_NEG_ODD_POS
          else if psgn == zero then pure INFERPSIGN_ZERO_ODD_POS
          else throw "INFERPT: bad sign"
      /- pols -/
      let split_pols1 ← SPLIT_LIST zind pols rr_ty
      let (_, l2) ← liftExcept (chop_list zind pols')
      let split_pols2 ← SPLIT_LIST pols_len2 (← ExceptT.mk (HolMath.Lists.mk_list l2 rr_ty)) rr_ty
      let (s1, t1) ← liftExcept (do dest_comb (← rhs (concl split_pols1)))
      let split_pols_thm ← TRANS split_pols1 (← AP_TERM s1 split_pols2)
      /- pt_sgns -/
      let split_sgns1 ← SPLIT_LIST zind pt_sgnl s_ty
      let (_, l3) ← liftExcept (chop_list zind pt_sgns)
      let split_sgns2 ← SPLIT_LIST pols_len2 (← ExceptT.mk (HolMath.Lists.mk_list l3 s_ty)) s_ty
      let (s2, t2) ← liftExcept (do dest_comb (← rhs (concl split_sgns1)))
      let split_pt_sgns_thm ← TRANS split_sgns1 (← AP_TERM s2 split_sgns2)
      /- sgns -/
      let split_signs ← SPLIT_LIST ind.toNat signs sl_ty
      let (r1, r3) ← liftExcept (do dest_comb (← rhs (concl split_signs)))
      let tl_thm ← ExceptT.mk (HD_CONV (ONCE_REWRITE_CONV [split_pt_sgns_thm]) r3)
      let (r4, _) ← liftExcept (do dest_comb (← rhs (concl split_signs)))
      let split_sgns_thm ← TRANS split_signs (← AP_TERM r4 tl_thm)
      /- imat -/
      let mat1 ← liftExcept (mk_comb imat pts)
      let mat_thm1 ← AP_TERM mat1 split_pols_thm
      let mat_thm2 ← MK_COMB (mat_thm1, split_sgns_thm)
      let mat_thm3 ← EQ_MP mat_thm2 mat_thm
      /- length thms -/
      /- LENGTH ps = LENGTH s1 -/
      let ps ← ExceptT.mk (HolMath.Lists.mk_list
        (← liftExcept (do tl (← dest_list (← dest_comb s1).2))) rr_ty)
      let ps_len ← ExceptT.mk (REWRITE_CONV [LENGTH] (← liftExcept (mk_comb rr_length ps)))
      let ss ← ExceptT.mk (HolMath.Lists.mk_list
        (← liftExcept (do tl (← dest_list (← dest_comb s2).2))) s_ty)
      let ss_len ← ExceptT.mk (REWRITE_CONV [LENGTH] (← liftExcept (mk_comb s_length ss)))
      let ps_s1_thm ← TRANS ps_len (← SYM ss_len)
      /- LENGTH qs = LENGTH s2 -/
      let k1 ← liftExcept (do tl (← chop_list pols_len2 (← dest_list t1)).1)
      let qs ← ExceptT.mk (HolMath.Lists.mk_list k1 rr_ty)
      let qs_len ← ExceptT.mk (REWRITE_CONV [LENGTH] (← liftExcept (mk_comb rr_length qs)))
      let k2 ← liftExcept (do tl (← chop_list pols_len2 (← dest_list t2)).1)
      let s2s ← ExceptT.mk (HolMath.Lists.mk_list k2 s_ty)
      let s2s_len ← ExceptT.mk (REWRITE_CONV [LENGTH] (← liftExcept (mk_comb s_length s2s)))
      let qs_s2_thm ← TRANS qs_len (← SYM s2s_len)
      /- ODD (LENGTH sgns) -/
      let (_, hdsgns) ← liftExcept (dest_comb r1)
      let odd_thm ← EQT_ELIM (← ExceptT.mk (REWRITE_CONV [LENGTH, ODD, EVEN, NOT_ODD, NOT_EVEN]
        (← liftExcept (do mk_comb odd_tm (← mk_comb sl_length hdsgns)))))
      /- a <> 0 -/
      let a_thm ←
        if par == even_tm then prove_nonzero asign
        else pure asign
      let div_thm' ← GEN (← liftExcept (hd vars)) div_thm
      /- main -/
      let thm1 ← BETA_RULE (← MATCH_MPL [mp_thm, mat_thm3, ps_s1_thm, qs_s2_thm, odd_thm])
      let thm2 ←
        if par == even_tm then MATCH_MPL [thm1, div_thm', a_thm, par_thm]
        else MATCH_MPL [thm1, div_thm', a_thm]
      REWRITE_RULE [APPEND] thm2)

  /- (`let mat_thm = mat_thm'` is in a comment) -/
  let INFERPTS : List term → List thm → thm → List thm → ExceptT String IO thm ← pure (fun vars sgns mat_thm div_thms => do
    let (pts, _, _) ← liftExcept (dest_interpmat (concl mat_thm))
    let len := 2 * ((← liftExcept (dest_list pts)).length : Int)
    let ods := (upto 1 len).filter odd
    -- `itlist`: the last element first
    ods.foldrM (fun i matthm => INFERPT vars sgns matthm div_thms i) mat_thm)

  let loc_itvars : IO.Ref (List term) ← IO.mkRef []
  let loc_itsgns : IO.Ref (List thm) ← IO.mkRef []
  let loc_itmat : IO.Ref thm ← IO.mkRef TRUTH
  let loc_itdivs : IO.Ref (List thm) ← IO.mkRef []
  let itvars : Option (IO.Ref (List term)) ← pure (some loc_itvars)
  let itsgns : Option (IO.Ref (List thm)) ← pure (some loc_itsgns)
  let itmat : Option (IO.Ref thm) ← pure (some loc_itmat)
  let itdivs : Option (IO.Ref (List thm)) ← pure (some loc_itdivs)
  /- (`let vars,sgns,mat_thm,div_thms = !itvars,..` is in a comment) -/

  let INFERPSIGN2 : List term → List thm → thm → List thm → ExceptT String IO thm ← pure (fun vars sgns mat_thm div_thms => do
    loc_itvars.set vars
    loc_itsgns.set sgns
    loc_itmat.set mat_thm
    loc_itdivs.set div_thms
    let (_, bod) ← liftExcept (do dest_binop rm (← lhs (concl (← hd div_thms))))
    let p ← liftExcept (do mk_abs (← hd vars) bod)
    let mat_thm' ← INSERT_UNKNOWN_COL mat_thm p
    let mat_thm'' ← INFERPTS vars sgns mat_thm' div_thms
    REMOVE_QS mat_thm'')

  /- ---------------------------------------------------------------------- -/
  /-  Timing                                                                -/
  /- ---------------------------------------------------------------------- -/

  let INFERPSIGN : List term → List thm → thm → List thm → ExceptT String IO thm ← pure (fun vars sgns mat_thm div_thms => do
    let start_time ← sys_time
    let res ← INFERPSIGN vars sgns mat_thm div_thms
    plus_dot_eq' inferpsign_timer ((← sys_time) - start_time)
    pure res)

  /- (the examples are in a comment in inferpsign.ml) -/

  -- @@RETURN BEGIN
  return { isign_eq_zero, isign_lt_zero, isign_gt_zero, inferpsign_row,
           split_interpsigns, INFERPSIGN, MK_REP, INSERT_UNKNOWN_COL, REMOVE_QS,
           SPLIT_LIST, prove_nonzero, INFERPT, INFERPTS, itvars, itsgns, itmat, itdivs,
           INFERPSIGN2 }
  -- @@RETURN END

end HolRQE.Inferpsign
