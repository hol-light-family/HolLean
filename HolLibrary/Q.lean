/- ========================================================================= -/
/- A library whose purpose is to remove type annotations from tactics when   -/
/- types can be found from the context.                                      -/
/- Similar to the Q module of HOL4 (<http://hol.sourceforge.net/             -/
/-   kananaskis-8-helpdocs/help/src-sml/htmlsigs/Q.html>).                   -/
/-                                                                           -/
/-            (c) Copyright, Vincent Aravantinos 2012-2013,                  -/
/-                           Hardware Verification Group,                    -/
/-                           Concordia University                            -/
/-                                                                           -/
/-                Contact:   <vincent@encs.concordia.ca>                     -/
/-                                                                           -/
/-            Distributed under the same license as HOL Light.               -/
/- ========================================================================= -/
/- File: HolLibrary/Q.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/q.ml`, by hand, in file order.
  q.ml proves no theorems: it is the OCaml module `Pa`, whose functions are
  HOL Light's tactics and rules with a string in place of each term.  The
  string is parsed and typechecked against the free variables of the goal
  (or theorem), so their types need not be written.  OCaml's `Pa.X` is
  `HolLibrary.Q.Pa.X` here, and `SessionLibrary.Q.Pa.X` at the top level.

  From q.ml: all the functions have the same signature as their standard
  HOL Light counterpart, except that `term` is replaced by `string`.
  REAL_ARITH, ARITH_RULE and the other decision procedures are wrapped with
  `call_with_interface`, which parses the string with the matching type
  prioritized (`prioritize_real` and so on) and then restores the interface.
  Those six depend on Session, so they are a bundle (`Rules`) built by
  `setupRules` from `QDeps`; the tactic wrappers use only the core tactics
  and are plain functions.

  Example (q.ml): the goal `!x:real. P x ==> ?y. P y` can be reduced by
  `REPEAT STRIP_TAC THEN EXISTS_TAC (← q "x:real")` or, equivalently, by
  `REPEAT STRIP_TAC THEN Pa.EXISTS_TAC "x"`.

  q.ml ends with a comment showing how to add COMPLEX_FIELD and
  SIMPLE_COMPLEX_ARITH once complex theories are loaded; it is not code.
-/

import HolMath

open HolCore HolCore.Lib HolCore.Basics HolCore.Preterm
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv)
open HolCore.Tactics (tactic thm_tactic goal goalstate)
open HolLight HolLight.Syntax

namespace HolLibrary.Q.Pa

/-- `parse_preterm = fst o parse_preterm o lex o explode`: lex and parse a
    preterm, ignoring any input left over (as q.ml does). -/
def parse_preterm (s : String) : ExceptT String IO preterm := do
  let c ← HolCore.Parser.mkCtx
  match HolCore.Parser.lex c (explode s) with
  | .error e => throw (HolCore.Parser.perrMsg e)
  | .ok toks =>
    match ← HolCore.Parser.parse_preterm c toks with
    | .error e => throw (HolCore.Parser.perrMsg e)
    | .ok (ptm, _) => pure ptm

/-- `CONTEXT_common f hs c x`: call `f` with the names and types of the free
    variables of `c` and `hs`. -/
def CONTEXT_common {α β : Type} (f : List (String × pretype) → α → β)
    (hs : List term) (c : term) (x : α) : β :=
  let vs := freesl (c :: hs)
  f (vs.map (fun x => (HolCore.Printer.name_of x, pretype_of_type (type_of x)))) x

/-- `CONTEXT_TAC ttac`: `ttac` given the free variables of the goal and its
    assumptions. -/
def CONTEXT_TAC (ttac : List (String × pretype) → tactic) : tactic := fun g =>
  let (asms, c) := g
  CONTEXT_common ttac (asms.map (concl ∘ Prod.snd)) c g

/-- `CONTEXT_RULE r th`: `r` given the free variables of `th`. -/
def CONTEXT_RULE {β : Type} (r : List (String × pretype) → thm → β) (th : thm) : β :=
  CONTEXT_common r (hyp th) (concl th) th

/-- `PARSES_IN_CONTEXT ttac ss`: parse each string in the goal's context. -/
def PARSES_IN_CONTEXT (ttac : List term → tactic) (ss : List String) : tactic :=
  CONTEXT_TAC (fun env => fun g => ExceptT.run do
    let tms ← ss.mapM (fun s => do term_of_preterm (← retypecheck env (← parse_preterm s)))
    ExceptT.mk (ttac tms g))

/-- `PARSE_IN_CONTEXT tac s`. -/
def PARSE_IN_CONTEXT (tac : term → tactic) (s : String) : tactic :=
  PARSES_IN_CONTEXT (fun l => match l with
    | [t] => tac t
    | _ => fun _ => pure (.error "Match_failure")) [s]

/-- `type_of_forall = type_of o fst o dest_forall`. -/
def type_of_forall (tm : term) : Except String hol_type := do
  return type_of (← dest_forall tm).1

/-- `force_type ?(env=[]) s ty`: parse `s` as a term of type `ty`. -/
def force_type (env : List (String × pretype) := []) (s : String) (ty : hol_type) :
    ExceptT String IO term := do
  let pty := pretype_of_type ty
  term_of_preterm (← retypecheck env (.Typing (← parse_preterm s) pty))

/-- `BOOL_CONTEXT_TAC ttac s`: parse `s` as a boolean term in the goal's
    context. -/
def BOOL_CONTEXT_TAC (ttac : term → tactic) (s : String) : tactic :=
  CONTEXT_TAC (fun env => fun g => ExceptT.run do
    ExceptT.mk (ttac (← force_type env s bool_ty) g))

section Tactics
variable [HolBase]

def SUBGOAL_THEN (s : String) (ttac : thm_tactic) : tactic :=
  BOOL_CONTEXT_TAC (fun t => HolLight.SUBGOAL_THEN t ttac) s
def SUBGOAL_TAC (l s : String) (tacs : List tactic) : tactic :=
  BOOL_CONTEXT_TAC (fun t => HolCore.Tactics.SUBGOAL_TAC HolBase.B l t tacs) s
def ABBREV_TAC : String → tactic := BOOL_CONTEXT_TAC HolLight.ABBREV_TAC

def ASM_CASES_TAC : String → tactic := BOOL_CONTEXT_TAC HolLight.ASM_CASES_TAC
def BOOL_CASES_TAC : String → tactic := BOOL_CONTEXT_TAC HolLight.BOOL_CASES_TAC

def EXISTS_TAC (s : String) : tactic := fun g =>
  let (_, c) := g
  CONTEXT_TAC (fun env => fun g => ExceptT.run do
    let ty := type_of (← liftExcept (dest_exists c)).1
    ExceptT.mk (HolLight.EXISTS_TAC (← force_type env s ty) g)) g

def SPEC_TAC (p : String × String) : tactic :=
  let (u, x) := p
  PARSE_IN_CONTEXT (fun u' => fun g => ExceptT.run do
    ExceptT.mk (HolLight.SPEC_TAC (u', ← force_type [] x (type_of u')) g)) u

def SPEC (s : String) (th : thm) : ExceptT String IO thm :=
  CONTEXT_RULE (fun env th => do
    HolLight.SPEC (← force_type env s (← liftExcept (type_of_forall (concl th)))) th) th

/-- `SPECL tms th = try rev_itlist SPEC tms th with Failure _ -> failwith
    "SPECL"` (`Pa.SPEC`, applied to the first string first). -/
def SPECL (tms : List String) (th : thm) : ExceptT String IO thm :=
  tryCatch (tms.foldlM (fun th s => SPEC s th) th) (fun _ => throw "SPECL")

/-- `GEN s th`: generalize over the free variable of `th` named `s`, or
    over `s` parsed as a term if there is none. -/
def GEN (s : String) (th : thm) : ExceptT String IO thm := do
  let v ← match find (fun x => s == HolCore.Printer.name_of x) (frees (concl th)) with
    | .ok v => pure v
    | .error _ => ExceptT.mk (HolCore.Parser.parse_term s)
  HolLight.GEN v th

/-- `GENL = itlist GEN` (`Pa.GEN`). -/
def GENL (ss : List String) (th : thm) : ExceptT String IO thm :=
  ss.foldrM (fun s th => GEN s th) th

def X_GEN_TAC (s : String) : tactic := fun g =>
  let (_, c) := g
  ExceptT.run do
    let t ← force_type [] s (← liftExcept (type_of_forall c))
    ExceptT.mk (HolLight.X_GEN_TAC t g)

end Tactics

/-- `call_with_interface p f s`: parse `s` and apply `f` with the interface
    set by `p`, then restore the interface.  As in OCaml, a failure of the
    parse or of `f` leaves the interface as `p` set it. -/
def call_with_interface {β : Type} (p : IO Unit) (f : term → ExceptT String IO β)
    (s : String) : ExceptT String IO β := do
  let i ← HolCore.Printer.the_interface.get
  p
  let res ← f (← ExceptT.mk (HolCore.Parser.parse_term s))
  HolCore.Printer.the_interface.set i
  pure res

end HolLibrary.Q.Pa

namespace HolLibrary.Q

/-- What q.ml uses from Session: the interface priorities and the decision
    procedures it wraps. -/
structure QDeps where
  prioritize_real : IO Unit
  prioritize_num : IO Unit
  prioritize_int : IO Unit
  REAL_ARITH : term → ExceptT String IO thm
  REAL_FIELD : term → ExceptT String IO thm
  REAL_RING : term → ExceptT String IO thm
  ARITH_RULE : term → ExceptT String IO thm
  NUM_RING : term → ExceptT String IO thm
  INT_ARITH : term → ExceptT String IO thm

/-- The decision procedures with a string argument (q.ml's last lines). -/
structure Rules where
  REAL_ARITH : String → ExceptT String IO thm
  REAL_FIELD : String → ExceptT String IO thm
  REAL_RING : String → ExceptT String IO thm
  ARITH_RULE : String → ExceptT String IO thm
  NUM_RING : String → ExceptT String IO thm
  INT_ARITH : String → ExceptT String IO thm

instance : Inhabited Rules :=
  ⟨⟨fun _ => throw "", fun _ => throw "", fun _ => throw "", fun _ => throw "",
    fun _ => throw "", fun _ => throw ""⟩⟩

open Pa in
/-- `let [REAL_ARITH;REAL_FIELD;REAL_RING] = map (call_with_interface
    prioritize_real) [...]`, likewise for ARITH_RULE and NUM_RING with
    `prioritize_num` and INT_ARITH with `prioritize_int`. -/
@[nospecialize]
def setupRules (D : QDeps) : ExceptT String IO Rules := do
  let (REAL_ARITH, REAL_FIELD, REAL_RING) :=
    (call_with_interface D.prioritize_real D.REAL_ARITH,
     call_with_interface D.prioritize_real D.REAL_FIELD,
     call_with_interface D.prioritize_real D.REAL_RING)
  let (ARITH_RULE, NUM_RING) :=
    (call_with_interface D.prioritize_num D.ARITH_RULE,
     call_with_interface D.prioritize_num D.NUM_RING)
  let INT_ARITH := call_with_interface D.prioritize_int D.INT_ARITH
  return { REAL_ARITH, REAL_FIELD, REAL_RING, ARITH_RULE, NUM_RING, INT_ARITH }

end HolLibrary.Q
