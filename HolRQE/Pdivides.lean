/- ========================================================================= -/
/- Rqe: pseudo-division with a remainder of the right sign (PDIVIDES).     -/
/- ========================================================================= -/
/- File: HolRQE/Pdivides.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/pdivides.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml, Rqe/num_calc_simp.ml, Rqe/asym.ml, Rqe/rol.ml, Rqe/poly_ext.ml, Rqe/simplify.ml, Rqe/lift_qelim.ml, Rqe/defs.ml, Rqe/testform_thms.ml, Rqe/condense_thms.ml, Rqe/inferisign_thms.ml, Rqe/matinsert_thms.ml, Rqe/signs_thms.ml, Rqe/inferpsign_thms.ml, Rqe/dedmatrix_thms.ml, Rqe/pdivides_thms.ml, Rqe/main_thms.ml, Rqe/work_thms.ml, Rqe/testform.ml, Rqe/condense.ml, Rqe/inferisign.ml, Rqe/matinsert.ml, Rqe/signs.ml, Rqe/inferpsign.ml, Rqe/dedmatrix.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.Pdivides fills them).

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

namespace HolRQE.Pdivides

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (mul_odd_lem neg_odd_lem : thm)
  deriving Inhabited

/-- What pdivides.ml uses from Session besides theorems. -/
structure PdividesDeps where
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
  PARITY_CONV : term → ExceptT String IO thm
  req : term
  rneq : term
  rlt : term
  rgt : term
  dest_mult : term → Except String (term × term)
  dest_pow : term → Except String (term × term)
  dest_plus : term → Except String (term × term)
  pdivides_timer : Option (IO.Ref Float)
  POLY_NEG_CONV : ioconv
  POLY_MUL_CONV : List term → ioconv
  POLYNATE_CONV : List term → ioconv
  head : List term → term → Except String term
  PDIVIDE : List term → term → term → ExceptT String IO thm
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



/- ---------------------------------------------------------------------- -/
/-  PDIVIDES (pdivides.ml 1-90; its examples are in a comment there)      -/
/- ---------------------------------------------------------------------- -/

structure PdividesFns where
  -- @@FIELDS
  PDIVIDES : List term → List thm → term → term → ExceptT String IO (term × thm)
  deriving Inhabited

@[nospecialize]
def setupPdividesFns [HolBase] (D : PdividesDeps) :
    ExceptT String IO PdividesFns := do
  -- @@SCOPE BEGIN
  let { FINDSIGN, PARITY_CONV, PDIVIDE, POLYNATE_CONV, POLY_MUL_CONV, POLY_NEG_CONV,
        dest_mult, dest_plus, dest_pow, head, pdivides_timer, req, rgt, rlt, rneq, .. } := D
  let { mul_odd_lem, neg_odd_lem, .. } := D.core1
  -- @@SCOPE END

  -- rebound below by the timed PDIVIDES
  let PDIVIDES : List term → List thm → term → term → ExceptT String IO (term × thm) ← pure (fun vars sgns p q => do
    let s_thm ← FINDSIGN vars sgns (← liftExcept (head vars q))
    let (op, _l1, _r1) ← liftExcept (get_binop (concl s_thm))
    if op == req then throw "PDIVIDES : head coefficient is zero" else
    let div_thm ← PDIVIDE vars p q
    let (asx, pqr) ← liftExcept (dest_eq (concl div_thm))
    let (pq, r) ← liftExcept (dest_plus pqr)
    let (_p', _q') ← liftExcept (dest_mult pq)
    let (ak, _s) ← liftExcept (dest_mult asx)
    let (_a, k) ← liftExcept (dest_pow ak)
    let k' ← liftExcept (HolMath.Nums.dest_small_numeral k)
    if op == rgt || even k' then
      pure (r, div_thm)
    else if odd k' && op == rlt then
      let par_thm ← PARITY_CONV k
      let mp_thm ← MATCH_MPL [neg_odd_lem, div_thm, par_thm]
      let mp_thm1 ← (CONV_RULE (LAND_CONV (LAND_CONV (LAND_CONV POLY_NEG_CONV)))) mp_thm
      let mp_thm2 ← (CONV_RULE (RAND_CONV (LAND_CONV (LAND_CONV (POLY_NEG_CONV))))) mp_thm1
      let mp_thm3 ← (CONV_RULE (RAND_CONV (RAND_CONV POLY_NEG_CONV))) mp_thm2
      let ret ← liftExcept (do return (← dest_plus (← rhs (concl mp_thm3))).2)
      pure (ret, mp_thm3)
    else if odd k' && op == rneq then
      let par_thm ← PARITY_CONV k
      let mp_thm ← MATCH_MPL [mul_odd_lem, div_thm, par_thm]
      let mp_thm1 ← (CONV_RULE (LAND_CONV (LAND_CONV (LAND_CONV (POLYNATE_CONV vars))))) mp_thm
      let mp_thm2 ← (CONV_RULE (RAND_CONV (LAND_CONV (POLYNATE_CONV vars)))) mp_thm1
      let mp_thm3 ← (CONV_RULE (RAND_CONV (RAND_CONV (POLY_MUL_CONV vars)))) mp_thm2
      let ret ← liftExcept (do return (← dest_plus (← rhs (concl mp_thm3))).2)
      pure (ret, mp_thm3)
    else throw "PDIVIDES: 1")

  /- ---------------------------------------------------------------------- -/
  /-  Timing                                                                -/
  /- ---------------------------------------------------------------------- -/

  let PDIVIDES : List term → List thm → term → term → ExceptT String IO (term × thm) ← pure (fun vars sgns mat_thm div_thms => do
    let start_time ← sys_time
    let res ← PDIVIDES vars sgns mat_thm div_thms
    plus_dot_eq' pdivides_timer ((← sys_time) - start_time)
    pure res)

  /- (the examples are in a comment in pdivides.ml) -/

  -- @@RETURN BEGIN
  return { PDIVIDES }
  -- @@RETURN END

end HolRQE.Pdivides
