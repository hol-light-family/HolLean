/- ========================================================================= -/
/- Rqe: finding, asserting and splitting on the signs of polynomials.      -/
/- ========================================================================= -/
/- File: HolRQE/Signs.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/signs.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml, Rqe/num_calc_simp.ml, Rqe/asym.ml, Rqe/rol.ml, Rqe/poly_ext.ml, Rqe/simplify.ml, Rqe/lift_qelim.ml, Rqe/defs.ml, Rqe/testform_thms.ml, Rqe/condense_thms.ml, Rqe/inferisign_thms.ml, Rqe/matinsert_thms.ml, Rqe/signs_thms.ml, Rqe/inferpsign_thms.ml, Rqe/dedmatrix_thms.ml, Rqe/pdivides_thms.ml, Rqe/main_thms.ml, Rqe/work_thms.ml, Rqe/testform.ml, Rqe/condense.ml, Rqe/inferisign.ml, Rqe/matinsert.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.Signs fills them).

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

namespace HolRQE.Signs

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (PULL_CASES_THM PULL_CASES_THM_NZ REAL_MUL_ASSOC REAL_MUL_LID pth_0g pth_0l
   pth_gg pth_gl pth_lg pth_ll pth_nzg pth_nzl signs_lem0002 signs_lem0003
   signs_lem002 signs_lem003 signs_lem01 signs_lem02 signs_lem03 signs_lem04
   signs_lem05 signs_lem06 signs_lem07 signs_lem08 : thm)
  deriving Inhabited

/-- What signs.ml uses from Session besides theorems. -/
structure SignsDeps where
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
  term_of_rat : Rat → Except String term
  MATCH_EQ_MP : thm → thm → ExceptT String IO thm
  dest_beq : term → Except String (term × term)
  mk_neq : term × term → Except String term
  req : term
  rneq : term
  rlt : term
  rgt : term
  rm : term
  rzero : term
  MONIC_CONV : List term → ioconv
  SIGN_CONST : term → ExceptT String IO thm
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

/-- HOL Light's `find` with a predicate that can fail (the failure is the
    caller's, as in OCaml); "find" when nothing satisfies it. -/
def findM {α : Type} (p : α → Except String Bool) : List α → Except String α
  | [] => .error "find"
  | h :: t => do if ← p h then pure h else findM p t

/-- The continuations of SPLIT_ZERO and SPLIT_SIGN: given the sign
    assumptions and the existential witnesses. -/
abbrev SignCont := List thm → List (term × thm) → ExceptT String IO thm

def xterm_lt (t1 t2 : term) : Except String Bool :=
  match (do
      let (n1, _) ← dest_var t1
      let (n2, _) ← dest_var t2
      -- `String.sub n 2 (String.length n - 2)` fails on a name shorter than 2
      if n1.length < 2 || n2.length < 2 then throw "Invalid_argument" else
      let i1 := String.ofList (n1.toList.drop 2)
      let i2 := String.ofList (n2.toList.drop 2)
      let x1 ← match i1.toInt? with | some v => pure v | none => throw "int_of_string"
      let x2 ← match i2.toInt? with | some v => pure v | none => throw "int_of_string"
      pure (x1 < x2) : Except String Bool) with
  | .ok b => .ok b
  | .error _ => .error "xterm_lt: not an xvar?"



/- ---------------------------------------------------------------------- -/
/-  Signs (signs.ml 1-352; xterm_lt is above; the examples are in comments -/
/-  in signs.ml)                                                           -/
/- ---------------------------------------------------------------------- -/

structure SignsFns where
  -- @@FIELDS
  FINDSIGN : List term → List thm → term → ExceptT String IO thm
  ASSERTSIGN : List term → List thm → thm → ExceptT String IO (List thm)
  SPLIT_ZERO : List term → List thm → term → SignCont → SignCont → List (term × thm) → ExceptT String IO thm
  SPLIT_SIGN : List term → List thm → term → SignCont → SignCont → List (term × thm) → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupSignsFns [HolBase] (D : SignsDeps) :
    ExceptT String IO SignsFns := do
  -- @@SCOPE BEGIN
  let { MATCH_EQ_MP, MONIC_CONV, REAL_RAT_REDUCE_CONV, SIGN_CONST, dest_beq, mk_neq,
        req, rgt, rlt, rm, rneq, rzero, term_of_rat, .. } := D
  let { PULL_CASES_THM, PULL_CASES_THM_NZ, REAL_MUL_ASSOC, REAL_MUL_LID, pth_0g,
        pth_0l, pth_gg, pth_gl, pth_lg, pth_ll, pth_nzg, pth_nzl, signs_lem0002,
        signs_lem0003, signs_lem002, signs_lem003, signs_lem01, signs_lem02,
        signs_lem03, signs_lem04, signs_lem05, signs_lem06, signs_lem07, signs_lem08, .. } := D.core1
  -- @@SCOPE END

  -- `let p_tm = .. and c_tm = .. and fth = prove(..) in let rec FINDSIGN ..`
  -- (not recursive); every failure is "FINDSIGN"
  let FINDSIGN : List term → List thm → term → ExceptT String IO thm ← do
    let p_tm ← q r"p:real"
    let c_tm ← q r"c:real"
    let fth ← prove
     r"r (a * b * p) (&0) ==> (a * b = &1) ==> r p (&0)"
      (DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC [REAL_MUL_ASSOC, REAL_MUL_LID])
    pure (fun vars sgns p => tryCatch (tryCatch (SIGN_CONST p) (fun x => do
      if x == Isign_tag then throw x
      let mth ← ExceptT.mk (MONIC_CONV vars p)
      let p' ← liftExcept (rand (concl mth))
      let pth ← liftExcept (findM (fun th => do return (← lhand (concl th)) == p') sgns)
      let c ← liftExcept (do lhand (← lhand (concl mth)))
      let r ← liftExcept (HolMath.CalcInt.rat_of_term c)
      -- `num 1 // ..`: OCaml's Num division by zero raises Division_by_zero
      if r == 0 then throw "Division_by_zero"
      let c' ← liftExcept (term_of_rat (1 / r))
      let sth ← SIGN_CONST c'
      let rel_c ← liftExcept (do rator (← rator (concl sth)))
      let rel_p ← liftExcept (do rator (← rator (concl pth)))
      let th1 ←
        if rel_p == req then pure (if rel_c == rgt then pth_0g else pth_0l)
        else if rel_p == rgt then pure (if rel_c == rgt then pth_gg else pth_gl)
        else if rel_p == rlt then pure (if rel_c == rgt then pth_lg else pth_ll)
        else if rel_p == rneq then pure (if rel_c == rgt then pth_nzg else pth_nzl)
        else throw "FINDSIGN"
      let th2 ← MP (← MP (← INST [(p', p_tm), (c', c_tm)] th1) pth) sth
      let symm ← SYM mth
      let th3 ← EQ_MP (← ExceptT.mk (LAND_CONV (RAND_CONV (fun _ => pure (.ok symm))) (concl th2))) th2
      let th4 ← MATCH_MP fth th3
      MP th4 (← EQT_ELIM (← ExceptT.mk (REAL_RAT_REDUCE_CONV (← liftExcept (lhand (concl th4))))))))
      (fun x => if x == Isign_tag then throw x else throw "FINDSIGN"))

  /- (examples are in signs.ml) -/

  let ASSERTSIGN : List term → List thm → thm → ExceptT String IO (List thm) ← pure (fun vars sgns sgn_thm => do
    let (op, l, _r) ← liftExcept (get_binop (concl sgn_thm))
    let p_thm ← ExceptT.mk (MONIC_CONV vars l)
    let (_, pl, pr) ← liftExcept (get_binop (concl p_thm))
    let (c, _) ← liftExcept (dest_binop rm pl)
    let c_thm ← SIGN_CONST c
    let (c_op, _, _) ← liftExcept (get_binop (concl c_thm))
    let sgn_thm' ←
      if c_op == rlt && op == rlt then
        MATCH_MPL [signs_lem01, c_thm, sgn_thm, p_thm]
      else if c_op == rgt && op == rlt then
        MATCH_MPL [signs_lem02, c_thm, sgn_thm, p_thm]
      else if c_op == rlt && op == rgt then
        MATCH_MPL [signs_lem03, c_thm, sgn_thm, p_thm]
      else if c_op == rgt && op == rgt then
        MATCH_MPL [signs_lem04, c_thm, sgn_thm, p_thm]
      else if c_op == rlt && op == req then
        MATCH_MPL [signs_lem05, c_thm, sgn_thm, p_thm]
      else if c_op == rgt && op == req then
        MATCH_MPL [signs_lem06, c_thm, sgn_thm, p_thm]
      else if c_op == rlt && op == rneq then
        MATCH_MPL [signs_lem07, c_thm, sgn_thm, p_thm]
      else if c_op == rgt && op == rneq then
        MATCH_MPL [signs_lem08, c_thm, sgn_thm, p_thm]
      else throw "ASSERTSIGN : 0"
    tryCatch (do
      let sgn_thm'' ← liftExcept (findM (fun th => do return (← lhand (concl th)) == pr) sgns)
      let (op1, _l1, _r1) ← liftExcept (get_binop (concl sgn_thm'))
      let (op2, _l2, _r2) ← liftExcept (get_binop (concl sgn_thm''))
      if (concl sgn_thm') == (concl sgn_thm'') then pure sgns
      else if op2 == rneq && (op1 == rlt || op1 == rgt) then
        pure (sgn_thm' :: (← liftExcept (remove (· == sgn_thm'') sgns)).2)
      else throw "ASSERTSIGN : 1")
      (fun x => if x == "find" then pure (sgn_thm' :: sgns) else throw x))

  /- (examples are in signs.ml) -/

  -- the `try .. with Failure "FINDSIGN"` covers the continuation too
  let SPLIT_ZERO : List term → List thm → term → SignCont → SignCont → List (term × thm) → ExceptT String IO thm ← pure (fun vars sgns p cont_z cont_n ex_thms =>
    tryCatch (do
      let sgn_thm ← FINDSIGN vars sgns p
      let (op, _l, _r) ← liftExcept (get_binop (concl sgn_thm))
      (if op == req then cont_z else cont_n) sgns ex_thms)
    (fun x => do
      if x != "FINDSIGN" then throw x
      let mkEq ← ExceptT.mk _root_.mk_eq
      let eq_tm ← liftExcept (mkEq (p, rzero))
      let neq_tm ← liftExcept (mk_neq (p, rzero))
      let or_thm ← ISPEC p signs_lem002

      let z_thm ← cont_z (← ASSERTSIGN vars sgns (← liftExcept (HolCore.Kernel.ASSUME eq_tm))) ex_thms
      let z_thm' ← DISCH eq_tm z_thm

      let nz_thm ← cont_n (← ASSERTSIGN vars sgns (← liftExcept (HolCore.Kernel.ASSUME neq_tm))) ex_thms
      let nz_thm' ← DISCH neq_tm nz_thm

      let ret ← MATCH_MPL [signs_lem003, or_thm, z_thm', nz_thm']

      let (ldj, rdj) ← liftExcept (dest_disj (concl ret))
      let (lcj, rcj) ← liftExcept (dest_conj ldj)
      let (a, _) ← liftExcept (dest_binop req lcj)
      let (p, p1) ← liftExcept (dest_beq rcj)
      let (_, rcj) ← liftExcept (dest_conj rdj)
      let p2 ← liftExcept (rhs rcj)
      let pull_thm ← ISPECL [a, p, p1, p2] PULL_CASES_THM
      let ret' ← MATCH_EQ_MP pull_thm ret
      pure ret'))

  /- (examples and the commented-out SPLIT_ZERO tests are in signs.ml) -/

  let SPLIT_SIGN : List term → List thm → term → SignCont → SignCont → List (term × thm) → ExceptT String IO thm ← pure (fun vars sgns p cont_p cont_n ex_thms => do
    let sgn_thm ← tryCatch (FINDSIGN vars sgns p) (fun x =>
                  if x == "FINDSIGN" then
                    throw "SPLIT_SIGN: no sign -- should have sign assumption by now"
                  else throw x)
    let gt_tm ← liftExcept (do (← mk_binop rgt p) rzero)
    let lt_tm ← liftExcept (do (← mk_binop rlt p) rzero)
    let (op, _, _) ← liftExcept (get_binop (concl sgn_thm))
    if op == rgt then cont_p sgns ex_thms
    else if op == rlt then cont_n sgns ex_thms
    else if op == req then throw "SPLIT_SIGN: lead coef is 0"
    else if op == rneq then
      let or_thm ← MATCH_MP signs_lem0002 sgn_thm

      let lt_sgns ← ASSERTSIGN vars sgns (← liftExcept (HolCore.Kernel.ASSUME lt_tm))
      let lt_thm ← cont_n lt_sgns ex_thms
      let lt_thm' ← DISCH lt_tm lt_thm

      let gt_sgns ← ASSERTSIGN vars sgns (← liftExcept (HolCore.Kernel.ASSUME gt_tm))
      let gt_thm ← cont_p gt_sgns ex_thms
      let gt_thm' ← DISCH gt_tm gt_thm

      let ret ← MATCH_MPL [signs_lem0003, or_thm, gt_thm', lt_thm']

      let (ldj, rdj) ← liftExcept (dest_disj (concl ret))
      let (lcj, rcj) ← liftExcept (dest_conj ldj)
      let (a, _) ← liftExcept (dest_binop rgt lcj)
      let (p, p1) ← liftExcept (dest_beq rcj)
      let (_, rcj) ← liftExcept (dest_conj rdj)
      let p2 ← liftExcept (rhs rcj)
      let pull_thm ← ISPECL [a, p, p1, p2] PULL_CASES_THM_NZ
      let ret' ← MATCH_EQ_MP (← MATCH_MP pull_thm sgn_thm) ret
      pure ret'
    else throw "SPLIT_SIGN: unknown op")

  /- (examples are in signs.ml) -/

  -- @@RETURN BEGIN
  return { FINDSIGN, ASSERTSIGN, SPLIT_ZERO, SPLIT_SIGN }
  -- @@RETURN END

end HolRQE.Signs
