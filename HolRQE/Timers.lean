/- ========================================================================= -/
/- Rqe: timers for the stages of the decision procedure.                   -/
/- ========================================================================= -/
/- File: HolRQE/Timers.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Rqe/timers.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/analysis.ml, Library/poly.ml, Rqe/rqe_lib.ml, Rqe/rqe_tactics_ext.ml, Rqe/util.ml, Rqe/rewrites.ml, Rqe/basic.ml, Rqe/rqe_num.ml, Rqe/rqe_real.ml, Rqe/list_rewrites.ml, Rqe/rqe_list.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionRQE.Timers fills them).

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

namespace HolRQE.Timers

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  deriving Inhabited

/-- What timers.ml uses from Session besides theorems. -/
structure TimersDeps where
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
  labels_flag : Option (IO.Ref Bool)
  prove_by_refinement : term × List tactic → ExceptT String IO thm
  exclude_list : Option (IO.Ref (List String))
  get_var_list : term → IO (List (String × hol_type))
  auto_type : term → term → IO term
  auto_type_list : term → List term → IO term
  auto_type_goal : term → HolCore.Tactics.goal → IO term
  TYPE_TAC : (term → tactic) → term → tactic
  TYPE_TACL : (List term → tactic) → List term → tactic
  CLAIM : term → tactic
  MATCH_EQ_MP : thm → thm → ExceptT String IO thm
  DISJ_LCASE : tactic
  DISJ_RCASE : tactic
  CASES_ON : term → tactic
  EXISTS_TAC : term → tactic
  MATCH_EQ_MPL : List thm → ExceptT String IO thm
  CCONTR_TAC : tactic
  pgoal : Unit → IO HolCore.Tactics.goalstack
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
  NUM_REWRITES : Option (IO.Ref (List thm))
  NUM_SIMP_TAC : tactic
  extend_num_rewrites : List thm → IO Unit
  REAL_REWRITES : Option (IO.Ref (List thm))
  REAL_ELIM : Option (IO.Ref (List thm))
  REAL_SIMP_TAC : tactic
  REAL_SOLVE_TAC : tactic
  extend_real_rewrites : List thm → IO Unit
  BASIC_REWRITES : Option (IO.Ref (List thm))
  dest_beq : term → Except String (term × term)
  t_tm : term
  f_tm : term
  nqt : term
  mk_neq : term × term → Except String term
  neq : term
  nlt : term
  ngt : term
  nle : term
  nge : term
  nm : term
  np : term
  nzero : term
  even_tm : term
  odd_tm : term
  PARITY_CONV : term → ExceptT String IO thm
  real_ty : hol_type
  rx : term
  ry : term
  rz : term
  req : term
  rneq : term
  rlt : term
  rgt : term
  rle : term
  rge : term
  rm : term
  rs : term
  rn : term
  rd : term
  rp : term
  rzero : term
  rone : term
  rlast : term
  rappend : term
  mk_rlist : List term → IO (Except String term)
  diffl_tm : term
  dest_diffl : term → Except String (term × term)
  dest_mult : term → Except String (term × term)
  mk_mult : term → Except String (term → Except String term)
  pow_tm : term
  dest_pow : term → Except String (term × term)
  mk_plus : term → Except String (term → Except String term)
  mk_negative : term → Except String term
  dest_plus : term → Except String (term × term)
  LIST_REWRITES : Option (IO.Ref (List thm))
  LIST_SIMP_TAC : tactic
  extend_list_rewrites : List thm → IO Unit
  aacons_tm : term
  HD_CONV : ioconv → ioconv
  TL_CONV : ioconv → ioconv
  EL_CONV : ioconv → Int → ioconv
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

/-- OCaml's `string_of_float` (as `print_float` prints): `"%.12g"`, with a
    trailing "." when the result looks like an integer.  Lean has no `%g`,
    so this rounds to 12 significant digits itself (exact for the values the
    timers hold, sums of CPU times). -/
def string_of_float (f : Float) : String :=
  if f.isNaN then "nan" else
  if f.isInf then (if f > 0 then "inf" else "-inf") else
  if f == 0 then (if 1 / f < 0 then "-0." else "0.") else
  let sign := if f < 0 then "-" else ""
  let a := f.abs
  let e0 : Int := (Float.floor (Float.log10 a)).toInt64.toInt
  let scale (k : Int) : Float := if k ≥ 0 then Float.pow 10 (Float.ofInt k)
    else 1 / Float.pow 10 (Float.ofInt (-k))
  let m0 := Float.round (a / scale (e0 - 11))
  let (m, e) := if m0 ≥ 1.0e12 then (Float.round (m0 / 10), e0 + 1)
    else if m0 < 1.0e11 then (Float.round (a / scale (e0 - 12)), e0 - 1) else (m0, e0)
  -- the 12 significant digits, trailing zeros dropped (as a list of chars)
  let ds0 := (toString m.toUInt64).toList.reverse.dropWhile (· == '0') |>.reverse
  let ds := if ds0.isEmpty then ['0'] else ds0
  let str (l : List Char) : String := String.ofList l
  let body :=
    if e < -4 || e ≥ 12 then
      let mant := if ds.length == 1 then str ds else str (ds.take 1) ++ "." ++ str (ds.drop 1)
      let ex := if e < 0 then "-" ++ (if -e < 10 then "0" else "") ++ toString (-e)
        else "+" ++ (if e < 10 then "0" else "") ++ toString e
      mant ++ "e" ++ ex
    else if e < 0 then
      "0." ++ str (List.replicate (-e - 1).toNat '0') ++ str ds
    else
      let n := e.toNat + 1
      if ds.length ≤ n then str ds ++ str (List.replicate (n - ds.length) '0')
      else str (ds.take n) ++ "." ++ str (ds.drop n)
  let s := sign ++ body
  if s.any (fun c => c == '.' || c == 'e' || c == 'n' || c == 'i') then s else s ++ "."

def print_float (f : Float) : IO Unit := IO.print (string_of_float f)

/-- `timer +.= x` on an exported (Option) timer ref. -/
def plus_dot_eq' (r : Option (IO.Ref Float)) (b : Float) : IO Unit :=
  match r with
  | some r => plus_dot_eq r b
  | none => pure ()



/- ---------------------------------------------------------------------- -/
/-  Timers (timers.ml 1-118)                                              -/
/- ---------------------------------------------------------------------- -/

structure TimersFns where
  -- @@FIELDS
  testform_timer : Option (IO.Ref Float)
  combine_testforms_timer : Option (IO.Ref Float)
  condense_timer : Option (IO.Ref Float)
  inferisign_timer : Option (IO.Ref Float)
  matinsert_timer : Option (IO.Ref Float)
  inferpsign_timer : Option (IO.Ref Float)
  remove_column1_timer : Option (IO.Ref Float)
  add_infinities_timer : Option (IO.Ref Float)
  remove_infinities_timer : Option (IO.Ref Float)
  pdivides_timer : Option (IO.Ref Float)
  duplicate_columns_timer : Option (IO.Ref Float)
  unmonicize_mat_timer : Option (IO.Ref Float)
  swap_head_col_timer : Option (IO.Ref Float)
  replace_pol_timer : Option (IO.Ref Float)
  unfactor_mat_timer : Option (IO.Ref Float)
  reset_timers : Unit → IO Unit
  print_timers : Unit → IO Unit
  deriving Inhabited

@[nospecialize]
def setupTimersFns [HolBase] (D : TimersDeps) :
    ExceptT String IO TimersFns := do
  -- @@SCOPE BEGIN
  let _ := D
  -- @@SCOPE END

  -- the refs are created once, when this (cached) setup runs at load, and
  -- exported as `some ref` (see HolRQE/Rewrites.lean)
  let loc_testform_timer : IO.Ref Float ← IO.mkRef 0.0
  let testform_timer : Option (IO.Ref Float) ← pure (some loc_testform_timer)
  let loc_combine_testforms_timer : IO.Ref Float ← IO.mkRef 0.0
  let combine_testforms_timer : Option (IO.Ref Float) ← pure (some loc_combine_testforms_timer)
  let loc_condense_timer : IO.Ref Float ← IO.mkRef 0.0
  let condense_timer : Option (IO.Ref Float) ← pure (some loc_condense_timer)
  let loc_inferisign_timer : IO.Ref Float ← IO.mkRef 0.0
  let inferisign_timer : Option (IO.Ref Float) ← pure (some loc_inferisign_timer)
  let loc_matinsert_timer : IO.Ref Float ← IO.mkRef 0.0
  let matinsert_timer : Option (IO.Ref Float) ← pure (some loc_matinsert_timer)
  let loc_inferpsign_timer : IO.Ref Float ← IO.mkRef 0.0
  let inferpsign_timer : Option (IO.Ref Float) ← pure (some loc_inferpsign_timer)
  let loc_remove_column1_timer : IO.Ref Float ← IO.mkRef 0.0
  let remove_column1_timer : Option (IO.Ref Float) ← pure (some loc_remove_column1_timer)
  let loc_add_infinities_timer : IO.Ref Float ← IO.mkRef 0.0
  let add_infinities_timer : Option (IO.Ref Float) ← pure (some loc_add_infinities_timer)
  let loc_remove_infinities_timer : IO.Ref Float ← IO.mkRef 0.0
  let remove_infinities_timer : Option (IO.Ref Float) ← pure (some loc_remove_infinities_timer)
  let loc_pdivides_timer : IO.Ref Float ← IO.mkRef 0.0
  let pdivides_timer : Option (IO.Ref Float) ← pure (some loc_pdivides_timer)
  let loc_duplicate_columns_timer : IO.Ref Float ← IO.mkRef 0.0
  let duplicate_columns_timer : Option (IO.Ref Float) ← pure (some loc_duplicate_columns_timer)
  let loc_unmonicize_mat_timer : IO.Ref Float ← IO.mkRef 0.0
  let unmonicize_mat_timer : Option (IO.Ref Float) ← pure (some loc_unmonicize_mat_timer)
  let loc_swap_head_col_timer : IO.Ref Float ← IO.mkRef 0.0
  let swap_head_col_timer : Option (IO.Ref Float) ← pure (some loc_swap_head_col_timer)
  let loc_replace_pol_timer : IO.Ref Float ← IO.mkRef 0.0
  let replace_pol_timer : Option (IO.Ref Float) ← pure (some loc_replace_pol_timer)
  let loc_unfactor_mat_timer : IO.Ref Float ← IO.mkRef 0.0
  let unfactor_mat_timer : Option (IO.Ref Float) ← pure (some loc_unfactor_mat_timer)

  let reset_timers : Unit → IO Unit ← pure (fun () => do
    loc_testform_timer.set 0.0
    loc_combine_testforms_timer.set 0.0
    loc_condense_timer.set 0.0
    loc_inferisign_timer.set 0.0
    loc_matinsert_timer.set 0.0
    loc_inferpsign_timer.set 0.0
    loc_remove_column1_timer.set 0.0
    loc_add_infinities_timer.set 0.0
    loc_remove_infinities_timer.set 0.0
    loc_pdivides_timer.set 0.0
    loc_duplicate_columns_timer.set 0.0
    loc_unmonicize_mat_timer.set 0.0
    loc_swap_head_col_timer.set 0.0
    loc_replace_pol_timer.set 0.0
    loc_unfactor_mat_timer.set 0.0
    pure ())

  let print_timers : Unit → IO Unit ← pure (fun () => do
    IO.print "\n----------TIMERS---------\n\n"

    IO.print "TESTFORM: "
    print_float (← loc_testform_timer.get)
    IO.print "\n"

    IO.print "COMBINE_TESTFORMS: "
    print_float (← loc_combine_testforms_timer.get)
    IO.print "\n"

    IO.print "CONDENSE: "
    print_float (← loc_condense_timer.get)
    IO.print "\n"

    IO.print "INFERISIGN: "
    print_float (← loc_inferisign_timer.get)
    IO.print "\n"

    IO.print "MATINSERT: "
    print_float (← loc_matinsert_timer.get)
    IO.print "\n"

    IO.print "INFERPSIGN: "
    print_float (← loc_inferpsign_timer.get)
    IO.print "\n"

    IO.print "REMOVE_COLUMN1: "
    print_float (← loc_remove_column1_timer.get)
    IO.print "\n"

    IO.print "ADD_INFINITIES: "
    print_float (← loc_add_infinities_timer.get)
    IO.print "\n"

    IO.print "REMOVE_INFINITIES: "
    print_float (← loc_remove_infinities_timer.get)
    IO.print "\n"

    IO.print "PDIVIDES: "
    print_float (← loc_pdivides_timer.get)
    IO.print "\n"

    IO.print "DUPLICATE_COLUMNS: "
    print_float (← loc_duplicate_columns_timer.get)
    IO.print "\n"

    IO.print "UNMONICIZE_MAT: "
    print_float (← loc_unmonicize_mat_timer.get)
    IO.print "\n"

    IO.print "SWAP_HEAD_COL: "
    print_float (← loc_swap_head_col_timer.get)
    IO.print "\n"

    IO.print "REPLACE_POL: "
    print_float (← loc_replace_pol_timer.get)
    IO.print "\n"

    IO.print "UNFACTOR_MAT: "
    print_float (← loc_unfactor_mat_timer.get)
    IO.print "\n"

    IO.print "\n-------------------------\n")

  -- @@RETURN BEGIN
  return { testform_timer, combine_testforms_timer, condense_timer, inferisign_timer,
           matinsert_timer, inferpsign_timer, remove_column1_timer, add_infinities_timer,
           remove_infinities_timer, pdivides_timer, duplicate_columns_timer,
           unmonicize_mat_timer, swap_head_col_timer, replace_pol_timer,
           unfactor_mat_timer, reset_timers, print_timers }
  -- @@RETURN END

end HolRQE.Timers
