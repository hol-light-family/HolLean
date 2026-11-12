/- ========================================================================= -/
/- Rqe: inferring the signs of a polynomial on intervals from its derivati -/
/- ========================================================================= -/
/- File: HolRQE/Inferisign.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/inferisign.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml, Rqe/num_calc_simp.ml, Rqe/asym.ml, Rqe/rol.ml, Rqe/poly_ext.ml, Rqe/simplify.ml, Rqe/lift_qelim.ml, Rqe/defs.ml, Rqe/testform_thms.ml, Rqe/condense_thms.ml, Rqe/inferisign_thms.ml, Rqe/matinsert_thms.ml, Rqe/signs_thms.ml, Rqe/inferpsign_thms.ml, Rqe/dedmatrix_thms.ml, Rqe/pdivides_thms.ml, Rqe/main_thms.ml, Rqe/work_thms.ml, Rqe/testform.ml, Rqe/condense.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.Inferisign fills them).

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

namespace HolRQE.Inferisign

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (APPEND INFERISIGN_NEG_NEG_NEG INFERISIGN_NEG_NEG_POS INFERISIGN_NEG_POS_NEG
   INFERISIGN_NEG_POS_POS INFERISIGN_NEG_ZERO_NEG INFERISIGN_NEG_ZERO_POS
   INFERISIGN_POS_NEG_NEG INFERISIGN_POS_NEG_POS INFERISIGN_POS_POS_NEG
   INFERISIGN_POS_POS_POS INFERISIGN_POS_ZERO_NEG INFERISIGN_POS_ZERO_POS
   INFERISIGN_ZERO_NEG_NEG INFERISIGN_ZERO_NEG_POS INFERISIGN_ZERO_POS_NEG
   INFERISIGN_ZERO_POS_POS INFERISIGN_ZERO_ZERO_NEG INFERISIGN_ZERO_ZERO_POS
   LENGTH TRUTH one : thm)
  deriving Inhabited

/-- What inferisign.ml uses from Session besides theorems. -/
structure InferisignDeps where
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
  inferisign_timer : Option (IO.Ref Float)
  POLY_ENLIST_CONV : List term → ExceptT String IO ioconv
  dest_interpmat : term → Except String (term × term × term)
  new_var : (hol_type → IO term)
  tmat : Option (IO.Ref thm)
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

/- inferisign.ml's `exception Isign of (thm * ((term * thm) list))`.  Lean's
   failures are strings, so raising Isign stores its argument in the bundle's
   ref `Isign_arg` and fails with the string "Isign"; a handler for OCaml's
   `Failure _` passes "Isign" on, and one for `Isign (..)` reads the ref. -/

/-- The failure string that stands for OCaml's `Isign` exception. -/
def Isign_tag : String := "Isign"

/-- What INFERISIGN closes over. -/
structure InferisignEnv where
  real_app : term
  sign_app : term
  real_len : term
  sign_len : term
  unknown : term
  pos : term
  zero : term
  neg : term
  num_mul : term
  num_add : term
  real_ty : hol_type
  one : term
  two : term
  f : term
  imat : term
  sl_ty : hol_type
  tvars : IO.Ref (List term)
  tdiff : IO.Ref thm
  tmat : IO.Ref thm
  tex : IO.Ref (List (term × thm))
  isign_arg : IO.Ref (thm × List (term × thm))
  dest_interpmat : term → Except String (term × term × term)
  POLY_ENLIST_CONV : List term → ExceptT String IO ioconv
  get_mp : term → term → term → ExceptT String IO thm
  new_var : hol_type → IO term
  APPEND : thm
  LENGTH : thm
  ARITH_TAC : tactic

/-- inferisign.ml's `let rec INFERISIGN = let .. in fun vars diff_thm mat_thm
    ex_thms -> try .. with Failure "get_index" -> mat_thm,ex_thms | Failure x
    -> failwith ("INFERISIGN: " ^ x)`; the handler covers the recursive calls
    and passes Isign on. -/
partial def INFERISIGN.go [HolBase] (E : InferisignEnv) (vars : List term) (diff_thm mat_thm : thm)
    (ex_thms : List (term × thm)) : ExceptT String IO (thm × List (term × thm)) :=
  tryCatch (do
    let { real_app, sign_app, real_len, sign_len, unknown, num_mul, num_add, real_ty, one, two,
          f, imat, sl_ty, tvars, tdiff, tmat, tex, isign_arg, dest_interpmat, POLY_ENLIST_CONV,
          get_mp, new_var, APPEND, LENGTH, ARITH_TAC, .. } := E
    tvars.set vars
    tdiff.set diff_thm
    tmat.set mat_thm
    tex.set ex_thms
    let (pts, ps, sgns) ← liftExcept (dest_interpmat (concl mat_thm))
    let pts' ← liftExcept (dest_list pts)
    if pts' == [] then return (mat_thm, ex_thms) else
    let sgns' ← liftExcept (dest_list sgns)
    let sgnl ← liftExcept (sgns'.mapM dest_list)
    let i ← liftExcept (get_index (fun x => match x with | h :: _ => h == unknown | [] => false) sgnl)
    -- (`hd x = unknown` fails on an empty row; the rows are never empty)
    if i % 2 = 1 then throw "bad shifted matrix" else
    let (p, p') ← match ← liftExcept (dest_list ps) with
      | p :: p' :: _ => pure (p, p')
      | _ => throw "Match_failure"
    let hv ← liftExcept (hd vars)
    let p_thm ← liftExcept (HolCore.Kernel.ABS hv
      (← ExceptT.mk ((← POLY_ENLIST_CONV vars) (← liftExcept (dest_abs p)).2)))
    let p'_thm ← ONCE_REWRITE_RULE [← GSYM diff_thm] (← liftExcept (HolCore.Kernel.ABS hv
      (← ExceptT.mk ((← POLY_ENLIST_CONV vars) (← liftExcept (dest_abs p')).2))))
    let (pts1, qts1) ← liftExcept (chop_list (i / 2 - 1).toNat pts')
    let ps_thm ← ExceptT.mk (REWRITE_CONV [p_thm, p'_thm] ps)
    let pts2 ← ExceptT.mk (HolMath.Lists.mk_list pts1 real_ty)
    let qts2 ← ExceptT.mk (HolMath.Lists.mk_list qts1 real_ty)
    let pts3 ← liftExcept (do mk_comb (← mk_comb real_app pts2) qts2)
    let mkEq ← ExceptT.mk _root_.mk_eq
    let pts_thm ← ExceptT.mk (HolCore.Tactics.prove HolBase.B
      (← liftExcept (mkEq (pts, pts3))) (REWRITE_TAC [APPEND]))
    let (sgns1, rgns1) ← liftExcept (chop_list (i - 1).toNat sgns')
    let sgns2 ← ExceptT.mk (HolMath.Lists.mk_list sgns1 sl_ty)
    let rgns2 ← ExceptT.mk (HolMath.Lists.mk_list rgns1 sl_ty)
    let sgns3 ← liftExcept (do mk_comb (← mk_comb sign_app sgns2) rgns2)
    let sgns_thm ← ExceptT.mk (HolCore.Tactics.prove HolBase.B
      (← liftExcept (mkEq (sgns, sgns3))) (REWRITE_TAC [APPEND]))
    let len1 ← liftExcept (mk_comb sign_len sgns2)
    let len2 ← liftExcept (do (← mk_binop num_add
      (← (← mk_binop num_mul two) (← mk_comb real_len pts2))) one)
    let len_thm ← ExceptT.mk (HolCore.Tactics.prove HolBase.B
      (← liftExcept (mkEq (len1, len2))) (REWRITE_TAC [LENGTH] THEN ARITH_TAC))
    let mat_thm1 ← MK_COMB (← MK_COMB ((← AP_TERM imat pts_thm), ps_thm), sgns_thm)
    let mat_thm2 ← EQ_MP mat_thm1 mat_thm
    let upper_sign ← liftExcept (hd (← liftExcept (ith (i - 1) sgnl)))
    let lower_sign ← liftExcept (hd (← liftExcept (ith (i + 1) sgnl)))
    let deriv_sign ← liftExcept (hd (← liftExcept (tl (← liftExcept (ith i sgnl)))))
    let mp_thm ← get_mp upper_sign lower_sign deriv_sign
    let mat_thm3 ← MATCH_MP (← MATCH_MP mp_thm mat_thm2) len_thm
    let mat_thm4 ← REWRITE_RULE [← GSYM p_thm, ← GSYM p'_thm, APPEND] mat_thm3
    let c := concl mat_thm4
    if c == f then
      isign_arg.set (mat_thm4, ex_thms)
      throw Isign_tag
    if !(is_exists c) then
      INFERISIGN.go E vars diff_thm mat_thm4 ex_thms else
    let (x, bod) ← liftExcept (dest_exists c)
    let x' ← new_var real_ty
    let s ← ExceptT.mk (subst [(x', x)])
    let assume_thm ← liftExcept (HolCore.Kernel.ASSUME (← ExceptT.mk (s bod)))
    INFERISIGN.go E vars diff_thm assume_thm ((x', mat_thm4) :: ex_thms))
  (fun x =>
    if x == Isign_tag then throw x
    else if x == "get_index" then pure (mat_thm, ex_thms)
    else throw ("INFERISIGN: " ++ x))



/- ====================================================================== -/
/-  INFERISIGN (inferisign.ml 1-241; its examples are in a comment there) -/
/- ====================================================================== -/

structure InferisignFns where
  -- @@FIELDS
  Isign_arg : Option (IO.Ref (thm × List (term × thm)))
  get_mp : term → term → term → ExceptT String IO thm
  tvars : Option (IO.Ref (List term))
  tdiff : Option (IO.Ref thm)
  tmat : Option (IO.Ref thm)
  tex : Option (IO.Ref (List (term × thm)))
  INFERISIGN : List term → thm → thm → List (term × thm) → ExceptT String IO (thm × List (term × thm))
  deriving Inhabited

@[nospecialize]
def setupInferisignFns [HolBase] (D : InferisignDeps) :
    ExceptT String IO InferisignFns := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, POLY_ENLIST_CONV, dest_interpmat, inferisign_timer, new_var, .. } := D
  let { APPEND, INFERISIGN_NEG_NEG_NEG, INFERISIGN_NEG_NEG_POS, INFERISIGN_NEG_POS_NEG,
        INFERISIGN_NEG_POS_POS, INFERISIGN_NEG_ZERO_NEG, INFERISIGN_NEG_ZERO_POS,
        INFERISIGN_POS_NEG_NEG, INFERISIGN_POS_NEG_POS, INFERISIGN_POS_POS_NEG,
        INFERISIGN_POS_POS_POS, INFERISIGN_POS_ZERO_NEG, INFERISIGN_POS_ZERO_POS,
        INFERISIGN_ZERO_NEG_NEG, INFERISIGN_ZERO_NEG_POS, INFERISIGN_ZERO_POS_NEG,
        INFERISIGN_ZERO_POS_POS, INFERISIGN_ZERO_ZERO_NEG, INFERISIGN_ZERO_ZERO_POS,
        LENGTH, TRUTH, .. } := D.core1
  -- @@SCOPE END

  -- `exception Isign of (thm * ((term * thm) list))`: its argument, when
  -- raised (see Isign_tag above); exported as `some ref`
  let loc_Isign_arg : IO.Ref (thm × List (term × thm)) ← IO.mkRef (TRUTH, [])
  let Isign_arg : Option (IO.Ref (thm × List (term × thm))) ← pure (some loc_Isign_arg)

  let get_mp : term → term → term → ExceptT String IO thm ← do
    let _unknown ← q r"Unknown"
    let pos ← q r"Pos"
    let zero ← q r"Zero"
    let neg ← q r"Neg"
    pure (fun upper_sign lower_sign deriv_sign =>
      if upper_sign == pos &&
         lower_sign == pos &&
         deriv_sign == pos then pure INFERISIGN_POS_POS_POS
      else if upper_sign == pos &&
         lower_sign == pos &&
         deriv_sign == neg then pure INFERISIGN_POS_POS_NEG

      else if upper_sign == pos &&
         lower_sign == neg &&
         deriv_sign == pos then pure INFERISIGN_POS_NEG_POS
      else if upper_sign == pos &&
         lower_sign == neg &&
         deriv_sign == neg then pure INFERISIGN_POS_NEG_NEG

      else if upper_sign == pos &&
         lower_sign == zero &&
         deriv_sign == pos then pure INFERISIGN_POS_ZERO_POS
      else if upper_sign == pos &&
         lower_sign == zero &&
         deriv_sign == neg then pure INFERISIGN_POS_ZERO_NEG

      else if upper_sign == neg &&
         lower_sign == pos &&
         deriv_sign == pos then pure INFERISIGN_NEG_POS_POS
      else if upper_sign == neg &&
         lower_sign == pos &&
         deriv_sign == neg then pure INFERISIGN_NEG_POS_NEG

      else if upper_sign == neg &&
         lower_sign == neg &&
         deriv_sign == pos then pure INFERISIGN_NEG_NEG_POS
      else if upper_sign == neg &&
         lower_sign == neg &&
         deriv_sign == neg then pure INFERISIGN_NEG_NEG_NEG

      else if upper_sign == neg &&
         lower_sign == zero &&
         deriv_sign == pos then pure INFERISIGN_NEG_ZERO_POS
      else if upper_sign == neg &&
         lower_sign == zero &&
         deriv_sign == neg then pure INFERISIGN_NEG_ZERO_NEG

      else if upper_sign == zero &&
         lower_sign == pos &&
         deriv_sign == pos then pure INFERISIGN_ZERO_POS_POS
      else if upper_sign == zero &&
         lower_sign == pos &&
         deriv_sign == neg then pure INFERISIGN_ZERO_POS_NEG

      else if upper_sign == zero &&
         lower_sign == neg &&
         deriv_sign == pos then pure INFERISIGN_ZERO_NEG_POS
      else if upper_sign == zero &&
         lower_sign == neg &&
         deriv_sign == neg then pure INFERISIGN_ZERO_NEG_NEG

      else if upper_sign == zero &&
         lower_sign == zero &&
         deriv_sign == pos then pure INFERISIGN_ZERO_ZERO_POS
      else if upper_sign == zero &&
         lower_sign == zero &&
         deriv_sign == neg then pure INFERISIGN_ZERO_ZERO_NEG
      else throw "bad signs in thm")

  -- `let tvars,tdiff,tmat,tex = ref [],ref TRUTH,ref TRUTH,ref []`: the tuple
  -- right to left; exported as `some ref`
  let loc_tex : IO.Ref (List (term × thm)) ← IO.mkRef []
  let loc_tmat : IO.Ref thm ← IO.mkRef TRUTH
  let loc_tdiff : IO.Ref thm ← IO.mkRef TRUTH
  let loc_tvars : IO.Ref (List term) ← IO.mkRef []
  let tvars : Option (IO.Ref (List term)) ← pure (some loc_tvars)
  let tdiff : Option (IO.Ref thm) ← pure (some loc_tdiff)
  let tmat : Option (IO.Ref thm) ← pure (some loc_tmat)
  let tex : Option (IO.Ref (List (term × thm))) ← pure (some loc_tex)

  -- `let rec INFERISIGN = let real_app = .. in fun vars diff_thm mat_thm
  -- ex_thms -> ..` (INFERISIGN.go), rebound below by the timed INFERISIGN
  let INFERISIGN : List term → thm → thm → List (term × thm) → ExceptT String IO (thm × List (term × thm)) ← do
    let real_app ← q r"APPEND:real list -> real list -> real list"
    let sign_app ← q r"APPEND:(sign list) list -> (sign list) list -> (sign list) list"
    let real_len ← q r"LENGTH:real list -> num"
    let sign_len ← q r"LENGTH:(sign list) list -> num"
    let unknown ← q r"Unknown"
    let pos ← q r"Pos"
    let zero ← q r"Zero"
    let neg ← q r"Neg"
    let num_mul ← q r"( * ):num -> num -> num"
    let num_add ← q r"( + ):num -> num -> num"
    let real_ty ← qty "real"
    let one ← q r"1"
    let two ← q r"2"
    let f ← q r"F"
    let imat ← q r"interpmat"
    let sl_ty ← qty "sign list"
    pure (INFERISIGN.go (InferisignEnv.mk real_app sign_app real_len sign_len unknown pos zero neg
      num_mul num_add real_ty one two f imat sl_ty loc_tvars loc_tdiff loc_tmat loc_tex
      loc_Isign_arg dest_interpmat POLY_ENLIST_CONV get_mp new_var APPEND LENGTH ARITH_TAC))

  let INFERISIGN : List term → thm → thm → List (term × thm) → ExceptT String IO (thm × List (term × thm)) ← pure (fun vars diff_thm mat_thm ex_thms => do
    let start_time ← sys_time
    let res ← INFERISIGN vars diff_thm mat_thm ex_thms
    plus_dot_eq' inferisign_timer ((← sys_time) - start_time)
    pure res)

  -- @@RETURN BEGIN
  return { Isign_arg, get_mp, tvars, tdiff, tmat, tex, INFERISIGN }
  -- @@RETURN END

end HolRQE.Inferisign
