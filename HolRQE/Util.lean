/- ========================================================================= -/
/- Rqe: interactive utilities (types of terms, a proof stack, printing).   -/
/- ========================================================================= -/
/- File: HolRQE/Util.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/util.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.Util fills them).

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

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolRQE.RqeLib
open HolRQE.RqeTacticsExt

namespace HolRQE.Util

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  deriving Inhabited

/-- What util.ml uses from Session besides theorems. -/
structure UtilDeps where
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
  current_goalstack : IO.Ref HolCore.Tactics.goalstack  -- tactics.ml's current_goalstack
  g : term → IO HolCore.Tactics.goalstack  -- tactics.ml's g
  p : Unit → IO HolCore.Tactics.goalstack  -- tactics.ml's p
  top_goal : Unit → IO (List term × term)  -- tactics.ml's top_goal
  labels_flag : Option (IO.Ref Bool)  -- rqe_tactics_ext.ml's labels_flag
  prove_by_refinement : term × List tactic → ExceptT String IO thm  -- rqe_tactics_ext.ml's prove_by_refinement
  exclude_list : Option (IO.Ref (List String))  -- rqe_tactics_ext.ml's exclude_list
  get_var_list : term → IO (List (String × hol_type))  -- rqe_tactics_ext.ml's get_var_list
  auto_type : term → term → IO term  -- rqe_tactics_ext.ml's auto_type
  auto_type_list : term → List term → IO term  -- rqe_tactics_ext.ml's auto_type_list
  auto_type_goal : term → HolCore.Tactics.goal → IO term  -- rqe_tactics_ext.ml's auto_type_goal
  TYPE_TAC : (term → tactic) → term → tactic  -- rqe_tactics_ext.ml's TYPE_TAC
  TYPE_TACL : (List term → tactic) → List term → tactic  -- rqe_tactics_ext.ml's TYPE_TACL
  CLAIM : term → tactic  -- rqe_tactics_ext.ml's CLAIM
  MATCH_EQ_MP : thm → thm → ExceptT String IO thm  -- rqe_tactics_ext.ml's MATCH_EQ_MP
  DISJ_LCASE : tactic  -- rqe_tactics_ext.ml's DISJ_LCASE
  DISJ_RCASE : tactic  -- rqe_tactics_ext.ml's DISJ_RCASE
  CASES_ON : term → tactic  -- rqe_tactics_ext.ml's CASES_ON
  EXISTS_TAC : term → tactic  -- rqe_tactics_ext.ml's EXISTS_TAC
  MATCH_EQ_MPL : List thm → ExceptT String IO thm  -- rqe_tactics_ext.ml's MATCH_EQ_MPL
  CCONTR_TAC : tactic  -- rqe_tactics_ext.ml's CCONTR_TAC
  pgoal : Unit → IO HolCore.Tactics.goalstack  -- rqe_tactics_ext.ml's pgoal
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

/- util.ml is interactive utilities, used by nothing at load.  Its plain
   functions are top-level definitions here, as in HolRQE/RqeLib.lean; the
   ones over its refs or the current goalstack are the bundle below.
   HOL Light's `open_hbox()`/`close_box()` only box the formatter's output;
   Lean's printers print directly, so they are left out. -/

/-- OCaml's polymorphic compare on `(string * hol_type)` pairs: first the
    name, then the type. -/
local instance : Ord (String × hol_type) := lexOrd

def string_of_char (c : Char) : String := String.singleton c

/-- `gensort = sort (<)`, with OCaml's polymorphic `<` as the derived `Ord`. -/
def gensort {α : Type} [Ord α] : List α → List α := sort (fun a b => compare a b == .lt)

/-- get_type_list's recursion, given `!suppress`. -/
def get_type_list.go (suppress : List String) : term → List (String × hol_type)
  | .Var s t => if mem s suppress then [] else [(s, t)]
  | .Const s t => if mem s suppress then [] else [(s, t)]
  | .Comb t1 t2 => get_type_list.go suppress t1 ++ get_type_list.go suppress t2
  | .Abs t1 t2 => get_type_list.go suppress t1 ++ get_type_list.go suppress t2

def my_print_type (st : String × hol_type) : IO Unit := do
  let (s, t) := st
  IO.print ("(\"" ++ s ++ "\", ")
  HolCore.Printer.print_qtype t
  IO.print ")\n"

def my_print_typel : List (String × hol_type) → IO Unit
  | [] => pure ()
  | h :: t => do my_print_type h; my_print_typel t

def print_thm_no_hyps (th : thm) : IO Unit := do
  let (asl, tm) := dest_thm th
  if !(asl == []) then IO.print "..." else pure ()
  IO.print "|- "
  HolCore.Printer.print_term tm

def print_trace_thm (hyps : Bool) (msg : String) (th : thm) : IO Unit := do
  let (_asl, _tm) := dest_thm th
  IO.print "------------------------\n "
  IO.print (msg ++ "\n")
  if hyps then HolCore.Printer.print_thm th else print_thm_no_hyps th
  IO.print "\n========================\n "



/- ---------------------------------------------------------------------- -/
/-  Types and the proof stack (util.ml 15-65: the bindings over the refs  -/
/-  `suppress` and `proof_stack` and the current goalstack).               -/
/- ---------------------------------------------------------------------- -/

structure UtilFns where
  -- @@FIELDS
  suppress : Option (IO.Ref (List String))
  get_type_list : term → IO (List (String × hol_type))
  set_types : term → IO (List (String × hol_type))
  print_term_types : term → IO Unit
  print_thm_types : thm → IO Unit
  goal_types : Unit → IO Unit
  assum : Int → ExceptT String IO term
  assum_types : Int → ExceptT String IO Unit
  get_type : String → thm → ExceptT String IO hol_type
  proof_stack : Option (IO.Ref (List HolCore.Tactics.goalstack))
  push_proof : term → IO HolCore.Tactics.goalstack
  pop_proof : Unit → ExceptT String IO HolCore.Tactics.goalstack
  deriving Inhabited

@[nospecialize]
def setupUtilFns [HolBase] (D : UtilDeps) :
    ExceptT String IO UtilFns := do
  -- @@SCOPE BEGIN
  let { g, p, top_goal, .. } := D
  -- @@SCOPE END

  -- `let suppress = ref ([]:string list)`, then `suppress := [..]`: created
  -- once, when this (cached) setup runs at load.  Exported as `some ref`, as
  -- a structure with an `IO.Ref` field cannot derive `Inhabited` computably.
  let loc_suppress : IO.Ref (List String) ← IO.mkRef []
  let suppress : Option (IO.Ref (List String)) ← pure (some loc_suppress)
  loc_suppress.set ["==>", "?", "!", "/\\", "\\/", ",", "~", "APPEND", "CONS", "HD", "LAST",
    "NIL", "=", "real_lt", "real_gt", "real_le", "real_ge", "BIT0", "BIT1", "NUMERAL",
    "real_of_num", "_0", "_1", "real_div", "real_mul", "real_pow", "COND"]

  let get_type_list : term → IO (List (String × hol_type)) ← pure (fun tm => do
    return get_type_list.go (← loc_suppress.get) tm)

  let set_types : term → IO (List (String × hol_type)) ← pure (fun tm => do
    return gensort (setify (← get_type_list tm)))

  let print_term_types : term → IO Unit ← pure (fun tm => do
    my_print_typel (← set_types tm))
  let print_thm_types : thm → IO Unit ← pure (fun tm => print_term_types (concl tm))
  let goal_types : Unit → IO Unit ← pure (fun () => do
    print_term_types (← top_goal ()).2)

  let assum : Int → ExceptT String IO term ← pure (fun i => do
    liftExcept (rev_ith i (← top_goal ()).1))
  let assum_types : Int → ExceptT String IO Unit ← pure (fun i => do
    print_term_types (← liftExcept (rev_ith i (← top_goal ()).1)))

  let get_type : String → thm → ExceptT String IO hol_type ← pure (fun s th => do
    liftExcept (assoc s (← get_type_list (concl th))))

  -- Proof stack.  `exception Empty_stack` is the failure "Empty_stack".
  let loc_proof_stack : IO.Ref (List HolCore.Tactics.goalstack) ← IO.mkRef []
  let proof_stack : Option (IO.Ref (List HolCore.Tactics.goalstack)) ← pure (some loc_proof_stack)
  let push_proof : term → IO HolCore.Tactics.goalstack ← pure (fun t => do
    loc_proof_stack.set ([← D.current_goalstack.get] ++ (← loc_proof_stack.get))
    g t)

  let pop_proof : Unit → ExceptT String IO HolCore.Tactics.goalstack ← pure (fun () => do
    match ← loc_proof_stack.get with
    | [] => throw "Empty_stack"
    | h :: t =>
      D.current_goalstack.set h
      loc_proof_stack.set t
      p ())

  -- @@RETURN BEGIN
  return { suppress, get_type_list, set_types, print_term_types, print_thm_types,
           goal_types, assum, assum_types, get_type, proof_stack, push_proof, pop_proof }
  -- @@RETURN END

end HolRQE.Util
