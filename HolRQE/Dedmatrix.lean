/- ========================================================================= -/
/- Rqe: deducing the sign matrix of p from that of its derivative and rema -/
/- ========================================================================= -/
/- File: HolRQE/Dedmatrix.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/dedmatrix.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml, Rqe/num_calc_simp.ml, Rqe/asym.ml, Rqe/rol.ml, Rqe/poly_ext.ml, Rqe/simplify.ml, Rqe/lift_qelim.ml, Rqe/defs.ml, Rqe/testform_thms.ml, Rqe/condense_thms.ml, Rqe/inferisign_thms.ml, Rqe/matinsert_thms.ml, Rqe/signs_thms.ml, Rqe/inferpsign_thms.ml, Rqe/dedmatrix_thms.ml, Rqe/pdivides_thms.ml, Rqe/main_thms.ml, Rqe/work_thms.ml, Rqe/testform.ml, Rqe/condense.ml, Rqe/inferisign.ml, Rqe/matinsert.ml, Rqe/signs.ml, Rqe/inferpsign.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.Dedmatrix fills them).

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

namespace HolRQE.Dedmatrix

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (APPEND HD INFIN_NEG_NEG INFIN_NEG_POS INFIN_NIL_NEG INFIN_NIL_POS
   INFIN_POS_NEG INFIN_POS_POS INFIN_SING_NEG_NEG INFIN_SING_NEG_POS
   INFIN_SING_POS_NEG INFIN_SING_POS_POS INTERPMAT_TRIO INTERPMAT_TRIO_TL MAP
   NORMAL_PDIFF REMOVE_COL1 TL TRUTH : thm)
  deriving Inhabited

/-- What dedmatrix.ml uses from Session besides theorems. -/
structure DedmatrixDeps where
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
  remove_column1_timer : Option (IO.Ref Float)
  add_infinities_timer : Option (IO.Ref Float)
  remove_infinities_timer : Option (IO.Ref Float)
  print_timers : Unit → IO Unit
  POLY_ENLIST_CONV : List term → ExceptT String IO ioconv
  dest_interpmat : term → Except String (term × term × term)
  new_var : (hol_type → IO term)
  tmat : Option (IO.Ref thm)
  CONDENSE : thm → ExceptT String IO thm
  tvars : Option (IO.Ref (List term))
  tdiff : Option (IO.Ref thm)
  tex : Option (IO.Ref (List (term × thm)))
  INFERISIGN : List term → thm → thm → List (term × thm) → ExceptT String IO (thm × List (term × thm))
  INFERPSIGN : List term → List thm → thm → List thm → ExceptT String IO thm
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

/-- lib.ml's `chop_list` on an OCaml int: a negative count recurses until
    `tl` fails, which is reported as "chop_list". -/
def chop_listI {α : Type} (n : Int) (l : List α) : Except String (List α × List α) :=
  if n < 0 then .error "chop_list" else chop_list n.toNat l

/-- DEDMATRIX's continuation: given the deduced matrix and the existential
    witnesses. -/
abbrev DedCont := thm → List (term × thm) → ExceptT String IO thm

/-- `deriving Inhabited` does not find a default for a function of eight
    arguments (DEDMATRIX's type), so give one. -/
instance : Inhabited (List term → List thm → List thm → thm → thm → DedCont → thm →
    List (term × thm) → ExceptT String IO thm) :=
  ⟨fun _ _ _ _ _ _ _ _ => throw "DEDMATRIX: bundle not built"⟩



/- ---------------------------------------------------------------------- -/
/-  DEDMATRIX (dedmatrix.ml 1-238; its examples are in a comment there)   -/
/- ---------------------------------------------------------------------- -/

structure DedmatrixFns where
  -- @@FIELDS
  prove_nonconstant : thm → thm → ExceptT String IO thm
  REMOVE_COLUMN1 : thm → ExceptT String IO thm
  APPENDIZE : term → Int → ExceptT String IO thm
  REMOVE_INFINITIES : thm → ExceptT String IO thm
  get_dirs : term → term → ExceptT String IO thm
  get_sing_dirs : term → term → ExceptT String IO thm
  aitvars : Option (IO.Ref (List term))
  aitdiff : Option (IO.Ref thm)
  aitnorm : Option (IO.Ref thm)
  aitmat : Option (IO.Ref thm)
  ADD_INFINITIES : List term → thm → thm → thm → ExceptT String IO (thm × (term × thm) × (term × thm))
  tvars : Option (IO.Ref (List term))
  tsgns : Option (IO.Ref (List thm))
  tdivs : Option (IO.Ref (List thm))
  tdiff : Option (IO.Ref thm)
  tnorm : Option (IO.Ref thm)
  tcont : Option (IO.Ref DedCont)
  tmat : Option (IO.Ref thm)
  tex : Option (IO.Ref (List (term × thm)))
  DEDMATRIX : List term → List thm → List thm → thm → thm → DedCont → thm → List (term × thm) → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupDedmatrixFns [HolBase] (D : DedmatrixDeps) :
    ExceptT String IO DedmatrixFns := do
  -- @@SCOPE BEGIN
  let { CONDENSE, INFERISIGN, INFERPSIGN, POLY_ENLIST_CONV, add_infinities_timer,
        dest_interpmat, new_var, remove_column1_timer, remove_infinities_timer, .. } := D
  let { APPEND, HD, INFIN_NEG_NEG, INFIN_NEG_POS, INFIN_NIL_NEG, INFIN_NIL_POS,
        INFIN_POS_NEG, INFIN_POS_POS, INFIN_SING_NEG_NEG, INFIN_SING_NEG_POS,
        INFIN_SING_POS_NEG, INFIN_SING_POS_POS, INTERPMAT_TRIO, INTERPMAT_TRIO_TL, MAP,
        NORMAL_PDIFF, REMOVE_COL1, TL, TRUTH, .. } := D.core1
  -- @@SCOPE END

  let prove_nonconstant : thm → thm → ExceptT String IO thm ← do
    let nonconstant_tm ← q r"nonconstant"
    pure (fun pdiff_thm normal_thm => do
      let thm ← ONCE_REWRITE_RULE [← GSYM pdiff_thm] normal_thm
      let ret ← REWRITE_RULE [← GSYM NORMAL_PDIFF] thm
      let (f, _) := strip_comb (concl ret)
      if !(f == nonconstant_tm) then throw "prove_nonconstant" else pure ret)

  -- rebound below by the timed REMOVE_COLUMN1
  let REMOVE_COLUMN1 : thm → ExceptT String IO thm ← pure (fun mat_thm => do
    let mat_thm1 ← MATCH_MP REMOVE_COL1 mat_thm
    REWRITE_RULE [MAP, HD, TL] mat_thm1)

  let APPENDIZE : term → Int → ExceptT String IO thm ← pure (fun l n => do
    let lty := type_of l
    let ty ← liftExcept (do hd (← dest_type lty).2)
    let app_tm ← ExceptT.mk (mk_const "APPEND" [(ty, aty)])
    let (l1, l2) ← liftExcept (do chop_listI n (← dest_list l))
    -- `mk_comb(mk_comb(app_tm,mk_list(l1,ty)),mk_list(l2,ty))`, right to left
    let l2' ← ExceptT.mk (HolMath.Lists.mk_list l2 ty)
    let l1' ← ExceptT.mk (HolMath.Lists.mk_list l1 ty)
    let app ← liftExcept (do mk_comb (← mk_comb app_tm l1') l2')
    GSYM (← ExceptT.mk (REWRITE_CONV [APPEND] app)))

  -- rebound below by the timed REMOVE_INFINITIES
  let REMOVE_INFINITIES : thm → ExceptT String IO thm ← pure (fun thm => do
    let thm' ← MATCH_MP INTERPMAT_TRIO thm
    let (pts, _, _sgns) ← liftExcept (dest_interpmat (concl thm'))
    let p_thm ← APPENDIZE pts ((← liftExcept (dest_list pts)).length - 2 : Int)
    let (_pts', _, sgns) ← liftExcept (dest_interpmat (concl thm'))
    let s_thm ← APPENDIZE sgns ((← liftExcept (dest_list sgns)).length - 5 : Int)
    let thm'' ← MATCH_MP INTERPMAT_TRIO_TL (← ONCE_REWRITE_RULE [p_thm, s_thm] thm')
    REWRITE_RULE [APPEND] thm'')

  let get_dirs : term → term → ExceptT String IO thm ← do
    let pos ← q r"Pos"
    let neg ← q r"Neg"
    pure (fun lb_deriv ub_deriv =>
      if lb_deriv == pos && ub_deriv == pos then pure INFIN_POS_POS
      else if lb_deriv == pos && ub_deriv == neg then pure INFIN_POS_NEG
      else if lb_deriv == neg && ub_deriv == pos then pure INFIN_NEG_POS
      else if lb_deriv == neg && ub_deriv == neg then pure INFIN_NEG_NEG
      else throw "get_dirs: bad signs")

  let get_sing_dirs : term → term → ExceptT String IO thm ← do
    let pos ← q r"Pos"
    let neg ← q r"Neg"
    pure (fun lb_deriv ub_deriv =>
      if lb_deriv == pos && ub_deriv == pos then pure INFIN_SING_POS_POS
      else if lb_deriv == pos && ub_deriv == neg then pure INFIN_SING_POS_NEG
      else if lb_deriv == neg && ub_deriv == pos then pure INFIN_SING_NEG_POS
      else if lb_deriv == neg && ub_deriv == neg then pure INFIN_SING_NEG_NEG
      else throw "get_dirs: bad signs")

  let loc_aitvars : IO.Ref (List term) ← IO.mkRef []
  let loc_aitdiff : IO.Ref thm ← IO.mkRef TRUTH
  let loc_aitnorm : IO.Ref thm ← IO.mkRef TRUTH
  let loc_aitmat : IO.Ref thm ← IO.mkRef TRUTH
  let aitvars : Option (IO.Ref (List term)) ← pure (some loc_aitvars)
  let aitdiff : Option (IO.Ref thm) ← pure (some loc_aitdiff)
  let aitnorm : Option (IO.Ref thm) ← pure (some loc_aitnorm)
  let aitmat : Option (IO.Ref thm) ← pure (some loc_aitmat)
  /- (`let vars,diff_thm,normal_thm,mat_thm = ..` are in a comment) -/

  -- rebound below by the timed ADD_INFINITIES
  let ADD_INFINITIES : List term → thm → thm → thm → ExceptT String IO (thm × (term × thm) × (term × thm)) ← do
    let _real_app ← q r"APPEND:real list -> real list -> real list"
    let sign_app ← q r"APPEND:(sign list) list -> (sign list) list -> (sign list) list"
    let imat ← q r"interpmat"
    let pos ← q r"Pos"
    let neg ← q r"Neg"
    let sl_ty ← qty "sign list"
    let real_ty ← qty "real"
    pure (fun vars diff_thm normal_thm mat_thm => do
      loc_aitvars.set vars
      loc_aitdiff.set diff_thm
      loc_aitnorm.set normal_thm
      loc_aitmat.set mat_thm
      let nc_thm ← prove_nonconstant diff_thm normal_thm
      let (pts, pols, sgns) ← liftExcept (dest_interpmat (concl mat_thm))
      let polsl ← liftExcept (dest_list pols)
      let (p, p') ← match polsl with
        | p :: p' :: _ => pure (p, p')
        | _ => throw "Match_failure"
      let hv ← liftExcept (hd vars)
      let p_thm ← liftExcept (HolCore.Kernel.ABS hv
        (← ExceptT.mk ((← POLY_ENLIST_CONV vars) (← liftExcept (dest_abs p)).2)))
      let p'_thm ← ONCE_REWRITE_RULE [← GSYM diff_thm] (← liftExcept (HolCore.Kernel.ABS hv
        (← ExceptT.mk ((← POLY_ENLIST_CONV vars) (← liftExcept (dest_abs p')).2))))
      let pols_thm ← ExceptT.mk (REWRITE_CONV [p_thm, p'_thm] pols)
      let sgnsl ← liftExcept (dest_list sgns)
      let sgns_len := sgnsl.length
      let thm1 ←
        if sgns_len = 1 then do
          let sgn ← liftExcept (do hd (← tl (← dest_list (← hd sgnsl))))
          let mp_thm ←
            if sgn == pos then pure INFIN_NIL_POS
            else if sgn == neg then pure INFIN_NIL_NEG
            else throw "bad sign in mat"
          let mat_thm1 ← MK_COMB ((← MK_COMB ((← AP_TERM imat (REFL pts)), pols_thm)), REFL sgns)
          let mat_thm2 ← EQ_MP mat_thm1 mat_thm
          MATCH_MP (← MATCH_MP mp_thm mat_thm2) nc_thm
        else if sgns_len = 3 then do
          let lb_deriv ← liftExcept (do hd (← tl (← dest_list (← hd sgnsl))))
          let ub_deriv ← liftExcept (do hd (← tl (← dest_list (← last sgnsl))))
          let mp_thm ← get_sing_dirs lb_deriv ub_deriv
          let mat_thm1 ← MK_COMB ((← MK_COMB ((← AP_TERM imat (REFL pts)), pols_thm)), REFL sgns)
          let mat_thm2 ← EQ_MP mat_thm1 mat_thm
          MATCH_MP (← MATCH_MP mp_thm mat_thm2) nc_thm
        else do
          let (s1, s2) ← liftExcept (chop_listI ((sgns_len : Int) - 3) sgnsl)
          let s3 ← ExceptT.mk (HolMath.Lists.mk_list s1 sl_ty)
          let s2' ← ExceptT.mk (HolMath.Lists.mk_list s2 sl_ty)
          let s4 ← liftExcept (do mk_comb (← mk_comb sign_app s3) s2')
          let mkEq ← ExceptT.mk _root_.mk_eq
          let sgns_thm ← ExceptT.mk (HolCore.Tactics.prove HolBase.B
            (← liftExcept (mkEq (sgns, s4))) (REWRITE_TAC [APPEND]))
          let mat_thm1 ← MK_COMB ((← MK_COMB ((← AP_TERM imat (REFL pts)), pols_thm)), sgns_thm)
          let mat_thm2 ← EQ_MP mat_thm1 mat_thm
          let lb_deriv ← liftExcept (do hd (← tl (← dest_list (← hd sgnsl))))
          let ub_deriv ← liftExcept (do hd (← tl (← dest_list (← last sgnsl))))
          let mp_thm ← get_dirs lb_deriv ub_deriv
          MATCH_MP (← MATCH_MP mp_thm mat_thm2) nc_thm
      let thm2 ← REWRITE_RULE [APPEND, ← GSYM pols_thm] thm1
      let c := concl thm2
      let (x, bod) ← liftExcept (dest_exists c)
      let x' ← new_var real_ty
      let s1 ← ExceptT.mk (subst [(x', x)])
      let bod1 ← ExceptT.mk (s1 bod)
      let assume_thm1 ← liftExcept (HolCore.Kernel.ASSUME bod1)
      let (x2, bod2) ← liftExcept (dest_exists bod1)
      let x'' ← new_var real_ty
      let s2 ← ExceptT.mk (subst [(x'', x2)])
      let assume_thm2 ← liftExcept (HolCore.Kernel.ASSUME (← ExceptT.mk (s2 bod2)))
      pure (assume_thm2, (x', thm2), (x'', assume_thm1)))

  /- (`print_timers()` etc. are in a comment) -/

  let loc_tvars : IO.Ref (List term) ← IO.mkRef []
  let loc_tsgns : IO.Ref (List thm) ← IO.mkRef []
  let loc_tdivs : IO.Ref (List thm) ← IO.mkRef []
  let loc_tdiff : IO.Ref thm ← IO.mkRef TRUTH
  let loc_tnorm : IO.Ref thm ← IO.mkRef TRUTH
  let loc_tcont : IO.Ref DedCont ← IO.mkRef (fun x _y => pure x)
  let loc_tmat : IO.Ref thm ← IO.mkRef TRUTH
  let loc_tex : IO.Ref (List (term × thm)) ← IO.mkRef []
  let tvars : Option (IO.Ref (List term)) ← pure (some loc_tvars)
  let tsgns : Option (IO.Ref (List thm)) ← pure (some loc_tsgns)
  let tdivs : Option (IO.Ref (List thm)) ← pure (some loc_tdivs)
  let tdiff : Option (IO.Ref thm) ← pure (some loc_tdiff)
  let tnorm : Option (IO.Ref thm) ← pure (some loc_tnorm)
  let tcont : Option (IO.Ref DedCont) ← pure (some loc_tcont)
  let tmat : Option (IO.Ref thm) ← pure (some loc_tmat)
  let tex : Option (IO.Ref (List (term × thm))) ← pure (some loc_tex)
  /- (`let vars,sgns,.. = !tvars,..` and a DEDMATRIX call are in a comment) -/

  -- the handler covers the continuation too, and passes Isign on
  let DEDMATRIX : List term → List thm → List thm → thm → thm → DedCont → thm → List (term × thm) → ExceptT String IO thm ← pure (fun vars sgns div_thms pdiff_thm normal_thm cont mat_thm ex_thms =>
    tryCatch (do
      loc_tvars.set vars
      loc_tsgns.set sgns
      loc_tdivs.set div_thms
      loc_tdiff.set pdiff_thm
      loc_tnorm.set normal_thm
      loc_tmat.set mat_thm
      loc_tex.set ex_thms
      loc_tcont.set cont
      let _start_time ← sys_time
      let (_pts, _pols, _signll) ← liftExcept (dest_interpmat (concl mat_thm))
      let mat_thm' ← INFERPSIGN vars sgns mat_thm div_thms
      let mat_thm'' ← CONDENSE mat_thm'
      let (mat_thm''', (v1, exthm1), (v2, exthm2)) ← ADD_INFINITIES vars pdiff_thm normal_thm mat_thm''
      let (mat_thm4, new_ex_pairs) ← INFERISIGN vars pdiff_thm mat_thm''' ((v1, exthm1) :: (v2, exthm2) :: ex_thms)
      let mat_thm5 ← REMOVE_INFINITIES mat_thm4
      let mat_thm6 ← REMOVE_COLUMN1 mat_thm5
      let mat_thm7 ← CONDENSE mat_thm6
      /- hack for changing renamed vars -/
      let hv ← liftExcept (hd vars)
      let alpha : ioconv := fun t => pure (HolCore.Equal.ALPHA_CONV hv t)
      let mat_thm8 ← CONV_RULE (RATOR_CONV (RAND_CONV (HolMath.Lists.LIST_CONV_IO alpha))) mat_thm7
      let ex_pairs := [(v1, exthm1), (v2, exthm2)] ++ new_ex_pairs
      let cont' : DedCont := fun mat_thm ex_thms => cont mat_thm (ex_thms ++ ex_pairs)
      cont' mat_thm8 ex_thms)
    (fun x => if x == Isign_tag then throw x else throw ("DEDMATRIX: " ++ x)))

  /- (the examples are in a comment in dedmatrix.ml) -/

  /- ---------------------------------------------------------------------- -/
  /-  Timing                                                                -/
  /- ---------------------------------------------------------------------- -/

  let REMOVE_COLUMN1 : thm → ExceptT String IO thm ← pure (fun mat_thm => do
    let start_time ← sys_time
    let res ← REMOVE_COLUMN1 mat_thm
    plus_dot_eq' remove_column1_timer ((← sys_time) - start_time)
    pure res)

  let ADD_INFINITIES : List term → thm → thm → thm → ExceptT String IO (thm × (term × thm) × (term × thm)) ← pure (fun vars pdiff_thm normal_thm mat_thm => do
    let start_time ← sys_time
    let res ← ADD_INFINITIES vars pdiff_thm normal_thm mat_thm
    plus_dot_eq' add_infinities_timer ((← sys_time) - start_time)
    pure res)

  let REMOVE_INFINITIES : thm → ExceptT String IO thm ← pure (fun thm => do
    let start_time ← sys_time
    let res ← REMOVE_INFINITIES thm
    plus_dot_eq' remove_infinities_timer ((← sys_time) - start_time)
    pure res)

  -- @@RETURN BEGIN
  return { prove_nonconstant, REMOVE_COLUMN1, APPENDIZE, REMOVE_INFINITIES, get_dirs,
           get_sing_dirs, aitvars, aitdiff, aitnorm, aitmat, ADD_INFINITIES, tvars,
           tsgns, tdivs, tdiff, tnorm, tcont, tmat, tex, DEDMATRIX }
  -- @@RETURN END

end HolRQE.Dedmatrix
