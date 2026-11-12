/- ========================================================================= -/
/- Rqe: the examples, each REAL_QELIM_CONV call timed.                     -/
/- ========================================================================= -/
/- File: HolRQE/Examples.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/examples.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml, Rqe/timers.ml, Rqe/num_calc_simp.ml, Rqe/asym.ml, Rqe/rol.ml, Rqe/poly_ext.ml, Rqe/simplify.ml, Rqe/lift_qelim.ml, Rqe/defs.ml, Rqe/testform_thms.ml, Rqe/condense_thms.ml, Rqe/inferisign_thms.ml, Rqe/matinsert_thms.ml, Rqe/signs_thms.ml, Rqe/inferpsign_thms.ml, Rqe/dedmatrix_thms.ml, Rqe/pdivides_thms.ml, Rqe/main_thms.ml, Rqe/work_thms.ml, Rqe/testform.ml, Rqe/condense.ml, Rqe/inferisign.ml, Rqe/matinsert.ml, Rqe/signs.ml, Rqe/inferpsign.ml, Rqe/dedmatrix.ml, Rqe/pdivides.ml, Rqe/rqe_main.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.Examples fills them).

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
import HolRQE.RqeMain

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
open HolRQE.RqeMain

namespace HolRQE.Examples

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  deriving Inhabited

/-- What examples.ml uses from Session besides theorems. -/
structure ExamplesDeps where
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
  polynomials : term → Except String (List term)
  REAL_QELIM_CONV : ioconv
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

/-- lib.ml's `time f x` for a conversion: reports "CPU time (user): t", or
    on failure prints "Failed after (user) CPU time of t: " and fails the same
    way (HolCore.Lib.time, with the failure an `Except`). -/
def timeE {α β : Type} (f : α → IO (Except String β)) (x : α) : ExceptT String IO β := do
  if !(← HolCore.Lib.report_timing.get) then ExceptT.mk (f x) else
  let start_time ← IO.monoNanosNow
  let r : Except String β ← f x
  match r with
  | Except.ok result =>
    report s!"CPU time (user): {(← IO.monoNanosNow) - start_time}ns"
    pure result
  | Except.error e =>
    IO.print s!"Failed after (user) CPU time of {(← IO.monoNanosNow) - start_time}ns: "
    throw e



/- ---------------------------------------------------------------------- -/
/-  The examples (examples.ml 1-1429): each REAL_QELIM_CONV call, timed,  -/
/-  as loading examples.ml runs them (make.ml leaves it out)              -/
/- ---------------------------------------------------------------------- -/

structure ExamplesFns where
  -- @@FIELDS
  th : thm
  deriving Inhabited

@[nospecialize]
def setupExamplesFns [HolBase] (D : ExamplesDeps) :
    ExceptT String IO ExamplesFns := do
  -- @@SCOPE BEGIN
  let { REAL_QELIM_CONV, .. } := D
  -- @@SCOPE END
  /- ---------------------------------------------------------------------- -/
  /- Paper -/
  /- ---------------------------------------------------------------------- -/
  /- ----------------------------  Chebychev  ----------------------------- -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x. --(&1) <= x /\ x <= &1 ==>
    -- (&1) <= &2 * x pow 2 - &1 /\ &2 * x pow 2 - &1 <= &1")
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x. --(&1) <= x /\ x <= &1 ==>
    -- (&1) <= &4 * x pow 3 - &3 * x /\ &4 * x pow 3 - &3 * x <= &1")
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"&1 < &2 /\ (!x. &1 < x ==> &1 < x pow 2) /\
 (!x y. &1 < x /\ &1 < y ==> &1 < x * (&1 + &2 * y))")
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"&0 <= b /\ &0 <= c /\ &0 < a * c ==> ?u. &0 < u /\ u * (u * c - a * c) -
   (u * a * c - (a pow 2 * c + b)) < a pow 2 * c + b")
  /- (notes are in a comment in examples.ml) -/
  /- ------------------------------------------------------------------------- -/
  /- Examples. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 4 + x pow 2 + &1 = &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 3 - x pow 2 + x - &1 = &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x y. (x pow 3 - x pow 2 + x - &1 = &0) /\
              (y pow 3 - y pow 2 + y - &1 = &0) /\ ~(x = y)")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!a f k. (!e. k < e ==> f < a * e) ==> f <= a * k")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. a * x pow 2 + b * x + c = &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!a b c. (?x. a * x pow 2 + b * x + c = &0) <=>
                 b pow 2 >= &4 * a * c")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!a b c. (?x. a * x pow 2 + b * x + c = &0) <=>
                 (a = &0) /\ (~(b = &0) \/ (c = &0)) \/
                 ~(a = &0) /\ b pow 2 >= &4 * a * c")
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. &0 <= x /\ x <= &1 /\ (r pow 2 * x pow 2 - r * (&1 + r) * x + (&1 + r) = &0)
   /\ ~(&2 * r * x = &1 + r)")
  /- (notes are in a comment in examples.ml) -/
  /- ------------------------------------------------------------------------- -/
  /- Termination ordering for group theory completion. -/
  /- ------------------------------------------------------------------------- -/
  /- ------------------------------------------------------------------------- -/
  /- Left this out -/
  /- ------------------------------------------------------------------------- -/
  /- ------------------------------------------------------------------------- -/
  /- This one works better using DNF. -/
  /- ------------------------------------------------------------------------- -/
  /- ------------------------------------------------------------------------- -/
  /- And this -/
  /- ------------------------------------------------------------------------- -/
  /- ------------------------------------------------------------------------- -/
  /- Linear examples. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x - &1 > &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. &3 - x > &0 /\ x - &1 > &0")
  /- (notes are in a comment in examples.ml) -/
  /- ------------------------------------------------------------------------- -/
  /- Quadratics. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 2 = &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 2 + &1 = &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 2 - &1 = &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 2 - &2 * x + &1 = &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 2 - &3 * x + &1 = &0")
  /- (notes are in a comment in examples.ml) -/
  /- ------------------------------------------------------------------------- -/
  /- Cubics. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 3 - &1 > &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 3 - &3 * x pow 2 + &3 * x - &1 > &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 3 - &4 * x pow 2 + &5 * x - &2 > &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 3 - &6 * x pow 2 + &11 * x - &6 = &0")
  /- (notes are in a comment in examples.ml) -/
  /- ------------------------------------------------------------------------- -/
  /- Quartics. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 4 - &1 > &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 4 + &1 > &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 4 = &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 4 - x pow 3 = &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 4 - x pow 2 = &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 4 - &2 * x pow 2 + &2 = &0")
  /- (notes are in a comment in examples.ml) -/
  /- ------------------------------------------------------------------------- -/
  /- Quintics. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 5 - &15 * x pow 4 + &85 * x pow 3 - &225 * x pow 2 + &274 * x - &120 = &0")
  /- (notes are in a comment in examples.ml) -/
  /- ------------------------------------------------------------------------- -/
  /- Sextics(?) -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x.
 x pow 6 - &21 * x pow 5 + &175 * x pow 4 - &735 * x pow 3 + &1624 * x pow 2 - &1764 * x + &720 = &0")
  -- a bare quotation (OCaml prints it)
  discard <| q r"?x. x pow 5 - &15 * x pow 4 + &85 * x pow 3 - &225 * x pow 2 + &274 * x - &120 = &0"
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  /- NOT YET -/
  /- (notes are in a comment in examples.ml) -/
  /- ------------------------------------------------------------------------- -/
  /- Multiple polynomials. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 2 + &2 > &0 /\ (x pow 3 - &11 = &0) /\ x + &131 >= &0")
  /- (notes are in a comment in examples.ml) -/
  /- ------------------------------------------------------------------------- -/
  /- With more variables. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. a * x pow 2 + b * x + c = &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. a * x pow 3 + b * x pow 2 + c * x + d = &0")
  /- (notes are in a comment in examples.ml) -/
  /- ------------------------------------------------------------------------- -/
  /- Constraint solving. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x1 x2. x1 pow 2 + x2 pow 2 - u1 <= &0 /\ x1 pow 2 - u2 > &0")
  /- (notes are in a comment in examples.ml) -/
  /- ------------------------------------------------------------------------- -/
  /- Huet & Oppen (interpretation of group theory). -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x y. x > &0 /\ y > &0 ==> x * (&1 + &2 * y) > &0")
  /- (notes are in a comment in examples.ml) -/
  /- ------------------------------------------------------------------------- -/
  /- Other examples. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 2 - x + &1 = &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 2 - &3 * x + &1 = &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x > &6 /\ (x pow 2 - &3 * x + &1 = &0)")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. &7 * x pow 2 - &5 * x + &3 > &0 /\
                            (x pow 2 - &3 * x + &1 = &0)")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. (&11 * x pow 3 - &7 * x pow 2 - &2 * x + &1 = &0) /\
                            &7 * x pow 2 - &5 * x + &3 > &0 /\
                            (x pow 2 - &8 * x + &1 = &0)")
  /- (notes are in a comment in examples.ml) -/
  /- ------------------------------------------------------------------------- -/
  /- Quadratic inequality from Liska and Steinberg -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x. -- &1 <= x /\ x <= &1 ==>
      C * (x - &1) * (&4 * x * a * C - x * C - &4 * a * C + C - &2) >= &0")
  /- (notes are in a comment in examples.ml) -/
  /- ------------------------------------------------------------------------- -/
  /- Metal-milling example from Loos and Weispfenning -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x y. &0 < x /\
                y < &0 /\
                (x * r - x * t + t = q * x - s * x + s) /\
                (x * b - x * d + d = a * y - c * y + c)")
  /- ------------------------------------------------------------------------- -/
  /- Linear example from Collins and Johnson -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?r. &0 < r /\
      r < &1 /\
      &0 < (&1 - &3 * r) * (a pow 2 + b pow 2) + &2 * a * r /\
      (&2 - &3 * r) * (a pow 2 + b pow 2) + &4 * a * r - &2 * a - r < &0")
  /- ------------------------------------------------------------------------- -/
  /- Dave Griffioen #4 -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x y. (&1 - t) * x <= (&1 + t) * y /\ (&1 - t) * y <= (&1 + t) * x
         ==> &0 <= y")
  /- (notes are in a comment in examples.ml) -/
  /- ------------------------------------------------------------------------- -/
  /- Some examples from "Real Quantifier Elimination in practice". -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x2. x1 pow 2 + x2 pow 2 <= u1 /\ x1 pow 2 > u2")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x1 x2. x1 pow 2 + x2 pow 2 <= u1 /\ x1 pow 2 > u2")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x1 x2. x1 + x2 <= &2 /\ x1 <= &1 /\ x1 >= &0 /\ x2 >= &0
           ==> &3 * (x1 + &3 * x2 pow 2 + &2) <= &8 * (&2 * x1 + x2 + &1)")
  /- (notes are in a comment in examples.ml) -/
  /- ------------------------------------------------------------------------- -/
  /- From Collins & Johnson's "Sign variation..." article. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?r. &0 < r /\ r < &1 /\
                (&1 - &3 * r) * (a pow 2 + b pow 2) + &2 * a * r > &0 /\
                (&2 - &3 * r) * (a pow 2 + b pow 2) + &4 * a * r - &2 * a - r < &0")
  /- (notes are in a comment in examples.ml) -/
  /- ------------------------------------------------------------------------- -/
  /- From "Parallel implementation of CAD" article. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. !y. x pow 2 + y pow 2 > &1 /\ x * y >= &1")
  /- (notes are in a comment in examples.ml) -/
  /- ------------------------------------------------------------------------- -/
  /- Other misc examples. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x y. (x pow 2 + y pow 2 = &1) ==> &2 * x * y <= &1")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x y. (x pow 2 + y pow 2 = &1) ==> &2 * x * y < &1")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x y. x * y > &0 <=> x > &0 /\ y > &0 \/ x < &0 /\ y < &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x y. x > y /\ x pow 2 < y pow 2")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x y. x < y ==> ?z. x < z /\ z < y")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x. &0 < x <=> ?y. x * y pow 2 = &1")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x. &0 <= x <=> ?y. x * y pow 2 = &1")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x. &0 <= x <=> ?y. x = y pow 2")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x y. &0 < x /\ x < y ==> ?z. x < z pow 2 /\ z pow 2 < y")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x y. x < y ==> ?z. x < z pow 2 /\ z pow 2 < y")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x y. (x pow 2 + y pow 2 = &0) ==> (x = &0) /\ (y = &0)")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x y z. (x pow 2 + y pow 2 + z pow 2 = &0) ==> (x = &0) /\ (y = &0) /\ (z = &0)")
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!w x y z. (w pow 2 + x pow 2 + y pow 2 + z pow 2 = &0)
                      ==> (w = &0) /\ (x = &0) /\ (y = &0) /\ (z = &0)")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!a. (a pow 2 = &2) ==> !x. ~(x pow 2 + a*x + &1 = &0)")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!a. (a pow 2 = &2) ==> !x. ~(x pow 2 - a*x + &1 = &0)")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x y. (x pow 2 = &2) /\ (y pow 2 = &3) ==> ((x * y) pow 2 = &6)")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x. ?y. x pow 2 = y pow 3")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x. ?y. x pow 3 = y pow 2")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!a b c.
        (a * x pow 2 + b * x + c = &0) /\
        (a * y pow 2 + b * y + c = &0) /\
        ~(x = y)
        ==> (a * (x + y) + b = &0)")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!y_1 y_2 y_3 y_4.
     (y_1 = &2 * y_3) /\
     (y_2 = &2 * y_4) /\
     (y_1 * y_3 = y_2 * y_4)
     ==> (y_1 pow 2 = y_2 pow 2)")
  /- (notes are in a comment in examples.ml) -/
  /- ------------------------------------------------------------------------- -/
  /- Counting roots. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 3 - x pow 2 + x - &1 = &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x y. (x pow 3 - x pow 2 + x - &1 = &0) /\ (y pow 3 - y pow 2 + y - &1 = &0) /\ ~(x = y)")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x. x pow 4 + x pow 2 - &2 = &0")
  /- (notes are in a comment in examples.ml) -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x y. x pow 4 + x pow 2 - &2 = &0 /\ y pow 4 + y pow 2 - &2 = &0 /\ ~(x = y)")
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x y. (x pow 3 + x pow 2 - x - &1 = &0) /\ (y pow 3 + y pow 2 - y - &1 = &0) /\ ~(x = y)")
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?x y z. (x pow 3 + x pow 2 - x - &1 = &0) /\
                    (y pow 3 + y pow 2 - y - &1 = &0) /\
                    (z pow 3 + z pow 2 - z - &1 = &0) /\ ~(x = y) /\ ~(x = z)")
  /- ------------------------------------------------------------------------- -/
  /- Existence of tangents, so to speak. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x y. ?s c. (s pow 2 + c pow 2 = &1) /\ s * x + c * y = &0")
  /- ------------------------------------------------------------------------- -/
  /- Another useful thing (componentwise ==> normwise accuracy etc.) -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x y. (x + y) pow 2 <= &2 * (x pow 2 + y pow 2)")
  /- ------------------------------------------------------------------------- -/
  /- Some related quantifier elimination problems. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x y. (x + y) pow 2 <= c * (x pow 2 + y pow 2)")
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!c. (!x y. (x + y) pow 2 <= c * (x pow 2 + y pow 2)) <=> &2 <= c")
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!a b. a * b * c <= a pow 2 + b pow 2")
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!c. (!a b. a * b * c <= a pow 2 + b pow 2) <=> c pow 2 <= &4")
  /- ------------------------------------------------------------------------- -/
  /- Tedious lemmas I once proved manually in HOL. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!a b c. &0 < a /\ &0 < b /\ &0 < c
                 ==> &0 < a * b /\ &0 < a * c /\ &0 < b * c")
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!a b c. a * b > &0 ==> (c * a < &0 <=> c * b < &0)")
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!a b c. a * b > &0 ==> (a * c < &0 <=> b * c < &0)")
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!a b. a < &0 ==> (a * b > &0 <=> b < &0)")
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!a b c. a * b < &0 /\ ~(c = &0) ==> (c * a < &0 <=> ~(c * b < &0))")
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!a b. a * b < &0 <=> a > &0 /\ b < &0 \/ a < &0 /\ b > &0")
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!a b. a * b <= &0 <=> a >= &0 /\ b <= &0 \/ a <= &0 /\ b >= &0")
  /- ------------------------------------------------------------------------- -/
  /- Vaguely connected with reductions for Robinson arithmetic. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!a b. ~(a <= b) <=> !d. d <= b ==> d < a")
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!a b. ~(a <= b) <=> !d. d <= b ==> ~(d = a)")
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!a b. ~(a < b) <=> !d. d < b ==> d < a")
  /- ------------------------------------------------------------------------- -/
  /- Another nice problem. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x y. (x pow 2 + y pow 2 = &1) ==> (x + y) pow 2 <= &2")
  /- ------------------------------------------------------------------------- -/
  /- Some variants / intermediate steps in Cauchy-Schwartz inequality. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x y. &2 * x * y <= x pow 2 + y pow 2")
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!a b c d. &2 * a * b * c * d <= a pow 2 * b pow 2 + c pow 2 * d pow 2")
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x1 x2 y1 y2.
      (x1 * y1 + x2 * y2) pow 2 <= (x1 pow 2 + x2 pow 2) * (y1 pow 2 + y2 pow 2)")
  /- ------------------------------------------------------------------------- -/
  /- The determinant example works OK here too. -/
  /- ------------------------------------------------------------------------- -/
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"?w x y z. (a * w + b * y = &1) /\
                   (a * x + b * z = &0) /\
                   (c * w + d * y = &0) /\
                   (c * x + d * z = &1)")
  /- ---------------------------------    --------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!a b c d.
        (?w x y z. (a * w + b * y = &1) /\
                         (a * x + b * z = &0) /\
                         (c * w + d * y = &0) /\
                         (c * x + d * z = &1))
        <=> ~(a * d = b * c)")
  /- ------------------------------------------------------------------------- -/
  /- From applying SOLOVAY_VECTOR_TAC. -/
  /- ------------------------------------------------------------------------- -/
  let th ← prove
    r"&0 <= c' /\ &0 <= c /\ &0 < h * c'
   ==> (?u. &0 < u /\
            (!v. &0 < v /\ v <= u
                 ==> v * (v * (h * h * c' + c) - h * c') - (v * h * c' - c') <
                     c'))"
    (W (fun (_asl, w) => MAP_EVERY (fun v => SPEC_TAC (v, v)) (frees w)) THEN
     CONV_TAC REAL_QELIM_CONV)
  /- ------------------------------------------------------------------------- -/
  /- Two notions of parallelism. -/
  /- ------------------------------------------------------------------------- -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x1 x2 y1 y2. (?c. (x2 = c * x1) /\ (y2 = c * y1)) <=>
                 (x1 = &0 /\ y1 = &0 ==> x2 = &0 /\ y2 = &0) /\
                 x1 * y2 = x2 * y1")
  /- ------------------------------------------------------------------------- -/
  /- From Behzad Akbarpour (takes about 300 seconds). -/
  /- ------------------------------------------------------------------------- -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x. &0 <= x /\ x <= &1
       ==> &0 < &1 - x + x pow 2 / &2 - x pow 3 / &6 /\
           &1 <= (&1 + x + x pow 2) *
           (&1 - x + x pow 2 / &2 - x pow 3 / &6)")
  /- ------------------------------------------------------------------------- -/
  /- A natural simplification of "limit of a product" result. -/
  /- Takes about 450 seconds. -/
  /- ------------------------------------------------------------------------- -/
  /- (notes are in a comment in examples.ml) -/
  discard <| timeE REAL_QELIM_CONV (← q r"!x y e. &0 < e ==> ?d. &0 < d /\ (x + d) * (y + d) - x * y < e /\
                                   x * y - (x + d) * (y + d) < e")

  -- @@RETURN BEGIN
  return { th }
  -- @@RETURN END

end HolRQE.Examples
