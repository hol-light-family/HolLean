/- File: SessionCore/IndDefs.lean
ind_defs.ml: its load-time auxiliaries (`indAux`: EXISTS_EQUATION's proforma,
IMP_REFL by ITAUT, and `T`), built by `initialize` when this module is
imported (hol_lib.ml 67, between theorems.ml and class.ml), and the
inductive-definition package over the monotonicity store.
-/
import SessionCore.Theorems
import HolCore.IndDefs

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Theorems HolCore.Classic
open HolCore.Trivia HolCore.Printer

namespace Session

private def ioOk {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")

/-- ind_defs.ml's load-time auxiliaries (hol_lib.ml 67, between theorems.ml
    and class.ml): `EXISTS_EQUATION`'s proforma, `IMP_REFL` (by ITAUT) and
    `T`. -/
initialize indAux : thm × thm × term ← do
  let pth ← ioOk "EXISTS_EQUATION_pth" (HolCore.IndDefs.EXISTS_EQUATION_pth B).run
  let p ← ioOk "parse !p. p ==> p" (HolCore.Parser.parse_term "!p. p ==> p")
  let impRefl ← ioOk "IMP_REFL" (HolCore.Itab.ITAUT B p)
  let tTm ← ioOk "parse T" (HolCore.Parser.parse_term "T")
  pure (pth, impRefl, tTm)

initialize theInductiveDefinitions : IO.Ref (List (thm × thm × thm)) ← IO.mkRef []

def get_monotonicity_theorems : IO (List thm) := theMonotonicityTheorems.get

def prove_inductive_relations_exist (tm : term) : IO (Except String thm) := do
  IndDefs.prove_inductive_relations_exist B indAux.1 T.REFL_CLAUSE T.CONJ_ACI indAux.2.2
    (← get_monotonicity_theorems) indAux.2.1 tm

/-- `monotonicity_theorems := l`. -/
def set_monotonicity_theorems (l : List thm) : IO Unit := theMonotonicityTheorems.set l

/-- `EXISTS_EQUATION tm th`. -/
def EXISTS_EQUATION (tm : term) (th : thm) : Except String thm :=
  IndDefs.EXISTS_EQUATION B indAux.1 tm th

/-- `derive_nonschematic_inductive_relations tm`. -/
def derive_nonschematic_inductive_relations (tm : term) : IO (Except String thm) :=
  IndDefs.derive_nonschematic_inductive_relations B T.REFL_CLAUSE T.CONJ_ACI indAux.2.2 tm

/-- Monotonicity tactic, using the current `theMonotonicityTheorems` (re-read on
    every invocation, as OCaml's `fun gl -> ... !monotonicity_theorems ...`). -/
def MONO_TAC : tactic := fun g => do
  IndDefs.MONO_TAC B (← get_monotonicity_theorems) indAux.2.1 g

/-- Prove/discharge the monotonicity hypotheses of `th`. -/
def prove_monotonicity_hyps (th : thm) : IO (Except String thm) := do
  IndDefs.prove_monotonicity_hyps B (← get_monotonicity_theorems) indAux.2.1 th

/-- Derive strong induction from a rule/induction pair. -/
def derive_strong_induction (rth ith : thm) : IO (Except String thm) := do
  IndDefs.derive_strong_induction B T.MONO_AND (← get_monotonicity_theorems) indAux.2.1 rth ith

def new_inductive_definition (tm : term) : IO (Except String (thm × thm × thm)) := do
  let existing ← theInductiveDefinitions.get
  match ← IndDefs.new_inductive_definition_core B indAux.1 T.REFL_CLAUSE T.CONJ_ACI indAux.2.2
            (← get_monotonicity_theorems) indAux.2.1 existing tm with
  | .error e => return .error e
  | .ok (trip, newEntry) =>
    match newEntry with
    | some entry => do theInductiveDefinitions.set (entry :: existing); return .ok trip
    | none => return .ok trip

end Session
