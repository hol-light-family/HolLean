/- ========================================================================= -/
/- Rqe: general list, reference, timing and term utilities.                -/
/- ========================================================================= -/
/- File: HolRQE/RqeLib.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/rqe_lib.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.RqeLib fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, INT_ARITH, TAUT, SET_RULE, ...) they are
  bound first, in OCaml's order.
-/

import HolLibrary.Analysis
import HolLibrary.Poly

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolRQE.RqeLib

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  deriving Inhabited

/-- What rqe_lib.ml uses from Session besides theorems. -/
structure RqeLibDeps where
  new_definition : String → ExceptT String IO thm
  define : String → ExceptT String IO thm
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
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

/- rqe_lib.ml has no theorems: it is general OCaml utilities, translated as
   top-level functions (they use no session state).  OCaml's failures are
   `Except String` with the same messages. -/

/- ---------------------------------------------------------------------- -/
/-  Refs                                                                  -/
/- ---------------------------------------------------------------------- -/

/-- rqe_lib.ml's `(+=)`: `a := !a + b`. -/
def plus_eq (a : IO.Ref Int) (b : Int) : IO Unit := a.modify (· + b)

/-- rqe_lib.ml's `(+.=)`: `a := !a +. b`. -/
def plus_dot_eq (a : IO.Ref Float) (b : Float) : IO Unit := a.modify (· + b)

/- ---------------------------------------------------------------------- -/
/-  Timing                                                                -/
/- ---------------------------------------------------------------------- -/

/-- OCaml's `Sys.time()`: seconds as a float (Lean has no CPU-time clock;
    this is the monotonic clock, as HolCore.Lib.time uses). -/
def sys_time : IO Float := do
  return (← IO.monoNanosNow).toFloat / 1.0e9

/-- `ptime f x`: the result and the time taken; on failure it prints
    "Failed after (user) CPU time of t: " and fails the same way. -/
def ptime {α β : Type} (f : α → ExceptT String IO β) (x : α) : ExceptT String IO (β × Float) := do
  let start_time ← sys_time
  try
    let result ← f x
    let finish_time ← sys_time
    let total_time := finish_time - start_time
    pure (result, total_time)
  catch e =>
    let finish_time ← sys_time
    let total_time := finish_time - start_time
    IO.print ("Failed after (user) CPU time of " ++ (toString total_time ++ ": "))
    throw e

/- ---------------------------------------------------------------------- -/
/-  Lists                                                                 -/
/- ---------------------------------------------------------------------- -/

def mappair {α β γ δ : Type} (f : α → γ) (g : β → δ) (l : List (α × β)) : List (γ × δ) :=
  let (a, b) := unzip l
  let la := a.map f
  let lb := b.map g
  List.zip la lb

partial def insertat {α : Type} (i : Int) (x : α) (l : List α) : Except String (List α) :=
  if i = 0 then .ok (x :: l) else
  match l with
  | [] => .error "insertat: list too short for position to exist"
  | h :: t => do return h :: (← insertat (i - 1) x t)

def allcombs {α β : Type} (f : α → α → β) : List α → List β
  | [] => []
  | h :: t => t.map (f h) ++ allcombs f t

def assoc_list {α β : Type} [BEq α] : List α → List (α × β) → Except String (List β)
  | [], _ => .ok []
  | h :: t, assl => do return (← assoc h assl) :: (← assoc_list t assl)

def add_to_list {α : Type} (l1 : IO.Ref (List α)) (l2 : List α) : IO Unit :=
  l1.modify (· ++ l2)

def list {α : Type} (x : α) : List α := [x]

partial def ith {α : Type} [Inhabited α] (i : Int) (l : List α) : Except String α :=
  if i = 0 then hd l else do ith (i - 1) (← tl l)

def rev_ith {α : Type} [Inhabited α] (i : Int) (l : List α) : Except String α :=
  ith (l.length - i - 1) l

def get_index {α : Type} (p : α → Bool) (l : List α) : Except String Int :=
  let rec go : List α → Int → Except String Int
    | [], _ => .error "get_index"
    | h :: t, n => if p h then .ok n else go t (n + 1)
  go l 0

def bindex {α : Type} (p : α → Bool) (l : List α) : Except String Int :=
  let rec go : List α → Int → Except String Int
    | [], _ => .error "bindex: not found"
    | h :: t, i => if p h then .ok i else go t (i + 1)
  go l 0

def cons {α : Type} (x : α) (y : List α) : List α := x :: y

/-- The first `swap_lists` (`let rec swap_lists l store`), which the second
    one, below, rebinds in OCaml. -/
def swap_lists_store {α : Type} : List (List α) → List (List α) → Except String (List (List α))
  | [], store => .ok store
  | h :: t, store => do
    let store' ← map2 cons h store
    swap_lists_store t store'

def swap_lists {α : Type} (l : List (List α)) : Except String (List (List α)) := do
  let n := (← hd l).length
  let l' ← swap_lists_store l (replicate [] n)
  return l'.map List.reverse

def fst3 {α β γ : Type} : α × β × γ → α | (a, _, _) => a
def snd3 {α β γ : Type} : α × β × γ → β | (_, a, _) => a
def thd3 {α β γ : Type} : α × β × γ → γ | (_, _, a) => a

def odd (n : Int) : Bool := n % 2 == 1
def even (n : Int) : Bool := n % 2 == 0

/- ---------------------------------------------------------------------- -/
/-  Terms                                                                 -/
/- ---------------------------------------------------------------------- -/

def dest_var_or_const (t : term) : Except String (String × hol_type) :=
  match t with
  | .Var s ty => .ok (s, ty)
  | .Const s ty => .ok (s, ty)
  | _ => .error "not a var or const"

/-- `term_match` runs in IO here, so this does too.  OCaml's `&&` evaluates
    the match only when the names agree. -/
def can_match (t1 t2 : term) : IO Bool := do
  match dest_var_or_const t1, dest_var_or_const t2 with
  | .ok (n1, _), .ok (n2, _) =>
    if n1 == n2 then return (← term_match [] t1 t2) matches .ok _ else return false
  | _, _ => return false

def dest_quant (tm : term) : Except String (term × term) :=
  if is_forall tm then dest_forall tm
  else if is_exists tm then dest_exists tm
  else .error "dest_quant: not a quantified term"

def get_binop (tm : term) : Except String (term × term × term) :=
  match (do
      let (f, r) ← dest_comb tm
      let (xop, l) ← dest_comb f
      pure (xop, l, r) : Except String (term × term × term)) with
  | .ok v => .ok v
  | .error _ => .error "get_binop"



end HolRQE.RqeLib
