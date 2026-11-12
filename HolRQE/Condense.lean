/- ========================================================================= -/
/- Rqe: condensing a sign matrix by removing points with no relevant zeros -/
/- ========================================================================= -/
/- File: HolRQE/Condense.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/condense.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml, Rqe/num_calc_simp.ml, Rqe/asym.ml, Rqe/rol.ml, Rqe/poly_ext.ml, Rqe/simplify.ml, Rqe/lift_qelim.ml, Rqe/defs.ml, Rqe/testform_thms.ml, Rqe/condense_thms.ml, Rqe/inferisign_thms.ml, Rqe/matinsert_thms.ml, Rqe/signs_thms.ml, Rqe/inferpsign_thms.ml, Rqe/dedmatrix_thms.ml, Rqe/pdivides_thms.ml, Rqe/main_thms.ml, Rqe/work_thms.ml, Rqe/testform.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.Condense fills them).

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

namespace HolRQE.Condense

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (APPEND INTERPMAT_SING INTERPMAT_TRIO INTERPMAT_TRIO_INNER LENGTH TRUTH : thm)
  deriving Inhabited

/-- What condense.ml uses from Session besides theorems. -/
structure CondenseDeps where
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
  real_ty : hol_type
  condense_timer : Option (IO.Ref Float)
  dest_interpmat : term → Except String (term × term × term)
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

/-- condense.ml's `triple_index`: where three equal rows start. -/
partial def triple_index {α : Type} [BEq α] : List α → Except String Int
  | [] => .error "triple_index"
  | [_x] => .error "triple_index"
  | [_x, _y] => .error "triple_index"
  | x :: y :: z :: rest =>
    if x == y && y == z then .ok 0 else do return 1 + (← triple_index (y :: z :: rest))

/-- What CONDENSE closes over. -/
structure CondenseEnv where
  real_app : term
  sign_app : term
  real_len : term
  sign_len : term
  num_mul : term
  real_ty : hol_type
  two : term
  sl_ty : hol_type
  loc_tmp : IO.Ref thm
  dest_interpmat : term → Except String (term × term × term)
  INTERPMAT_SING : thm
  INTERPMAT_TRIO : thm
  INTERPMAT_TRIO_INNER : thm
  APPEND : thm
  LENGTH : thm
  ARITH_TAC : tactic

/-- condense.ml's `let rec CONDENSE = let .. in fun mat_thm -> try .. with
    Failure "triple_index" -> mat_thm | Failure x -> failwith ("CONDENSE: " ^ x)`.
    The handler covers the recursive calls too, as in OCaml. -/
partial def CONDENSE.go [HolBase] (E : CondenseEnv) (mat_thm : thm) : ExceptT String IO thm :=
  tryCatch (do
    let { real_app, sign_app, real_len, sign_len, num_mul, real_ty, two, sl_ty, loc_tmp,
          dest_interpmat, INTERPMAT_SING, INTERPMAT_TRIO, INTERPMAT_TRIO_INNER, APPEND,
          LENGTH, ARITH_TAC } := E
    loc_tmp.set mat_thm
    let (pts, _, sgns) ← liftExcept (dest_interpmat (concl mat_thm))
    let sgnl ← liftExcept (dest_list sgns)
    let ptl ← liftExcept (dest_list pts)
    let i ← liftExcept (triple_index sgnl)
    if !(i % 2 = 0) then throw "misshifted matrix" else
    if i = 0 then
      if ptl.length = 1 then MATCH_MP INTERPMAT_SING mat_thm
      else CONDENSE.go E (← MATCH_MP INTERPMAT_TRIO mat_thm) else
    let (l, r) ← liftExcept (chop_list (i - 2).toNat sgnl)
    -- `let sgn1,sgn2 = mk_list(l,..),mk_list(r,..)`, right to left
    let sgn2 ← ExceptT.mk (HolMath.Lists.mk_list r sl_ty)
    let sgn1 ← ExceptT.mk (HolMath.Lists.mk_list l sl_ty)
    let sgns' ← liftExcept (do mk_comb (← mk_comb sign_app sgn1) sgn2)
    let mkEq ← ExceptT.mk _root_.mk_eq
    let sgn_thm ← ExceptT.mk (HolCore.Tactics.prove HolBase.B
      (← liftExcept (mkEq (sgns, sgns'))) (REWRITE_TAC [APPEND]))
    let (l', r') ← liftExcept (chop_list (i / 2 - 1).toNat ptl)
    let pt2 ← ExceptT.mk (HolMath.Lists.mk_list r' real_ty)
    let pt1 ← ExceptT.mk (HolMath.Lists.mk_list l' real_ty)
    let pts' ← liftExcept (do mk_comb (← mk_comb real_app pt1) pt2)
    let pt_thm ← ExceptT.mk (HolCore.Tactics.prove HolBase.B
      (← liftExcept (mkEq (pts, pts'))) (REWRITE_TAC [APPEND]))
    let mat_thm' ← ONCE_REWRITE_RULE [sgn_thm, pt_thm] mat_thm
    let len_thm ← ExceptT.mk (HolCore.Tactics.prove HolBase.B
      (← liftExcept (mkEq (← liftExcept (mk_comb sign_len sgn1),
        ← liftExcept (do (← mk_binop num_mul two) (← mk_comb real_len pt1)))))
      (REWRITE_TAC [LENGTH] THEN ARITH_TAC))
    CONDENSE.go E (← REWRITE_RULE [APPEND]
       (← MATCH_MP (← MATCH_MP INTERPMAT_TRIO_INNER mat_thm') len_thm)))
  (fun x =>
    if x == "triple_index" then pure mat_thm
    else throw ("CONDENSE: " ++ x))



/- ====================================================================== -/
/-  CONDENSE (condense.ml 1-667; the commented-out OCaml, its examples     -/
/-  and docs are in condense.ml)                                           -/
/- ====================================================================== -/

structure CondenseFns where
  -- @@FIELDS
  tmp : Option (IO.Ref thm)
  CONDENSE : thm → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupCondenseFns [HolBase] (D : CondenseDeps) :
    ExceptT String IO CondenseFns := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, condense_timer, dest_interpmat, .. } := D
  let { APPEND, INTERPMAT_SING, INTERPMAT_TRIO, INTERPMAT_TRIO_INNER, LENGTH, TRUTH, .. } := D.core1
  -- @@SCOPE END

  -- `let tmp = ref TRUTH`, exported as `some ref` (see HolRQE/Rewrites.lean)
  let loc_tmp : IO.Ref thm ← IO.mkRef TRUTH
  let tmp : Option (IO.Ref thm) ← pure (some loc_tmp)

  -- `let rec CONDENSE = let real_app = .. in fun mat_thm -> ..` (CONDENSE.go),
  -- rebound below by the timed CONDENSE
  let CONDENSE : thm → ExceptT String IO thm ← do
    let real_app ← q r"APPEND:real list -> real list -> real list"
    let sign_app ← q r"APPEND:(sign list) list -> (sign list) list -> (sign list) list"
    let real_len ← q r"LENGTH:real list -> num"
    let sign_len ← q r"LENGTH:(sign list) list -> num"
    let num_mul ← q r"( * ):num -> num -> num"
    let real_ty ← qty "real"
    let two ← q r"2"
    let sl_ty ← qty "sign list"
    pure (CONDENSE.go (CondenseEnv.mk real_app sign_app real_len sign_len num_mul real_ty two sl_ty
      loc_tmp dest_interpmat INTERPMAT_SING INTERPMAT_TRIO INTERPMAT_TRIO_INNER
      APPEND LENGTH ARITH_TAC))

  let CONDENSE : thm → ExceptT String IO thm ← pure (fun mat_thm => do
    let start_time ← sys_time
    let res ← CONDENSE mat_thm
    plus_dot_eq' condense_timer ((← sys_time) - start_time)
    pure res)

  -- @@RETURN BEGIN
  return { tmp, CONDENSE }
  -- @@RETURN END

end HolRQE.Condense
