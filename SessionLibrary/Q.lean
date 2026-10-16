/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/q.ml.                                       -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Q.lean

  The `unsafe` half of the q.ml translation: it supplies HolLibrary.Q's
  dependencies from Session, builds the `Rules` bundle once, and exports the
  module `Pa` as `SessionLibrary.Q.Pa`, under its HOL Light names
  (`Pa.EXISTS_TAC "x"`, `Pa.SPECL ["m"; "n"] th`, `Pa.REAL_ARITH "..."`).
  `ensureQ` is `needs "Library/q.ml"` (q.ml has no `needs`).
-/

import Session
import HolLibrary.Q

open HolCore HolCore.Kernel
open HolCore.Tactics (tactic thm_tactic)

namespace SessionLibrary.Q

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

/-- `prioritize_num`, `prioritize_int`: make the type the default for
    overloaded symbols (as SessionLibrary.Integer). -/
private unsafe def prioritizeType (name : String) : IO Unit := do
  match ← HolCore.Kernel.mk_type name [] with
  | .ok ty => Session.prioritize_overload ty
  | .error e => throw (IO.userError e)

/-- What q.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Q.QDeps where
  prioritize_real := Session.prioritize_real
  prioritize_num := prioritizeType "num"
  prioritize_int := prioritizeType "int"
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH3 t)
  REAL_FIELD t := ExceptT.mk (Session.REAL_FIELD t)
  REAL_RING t := ExceptT.mk (Session.REAL_RING t)
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  NUM_RING t := ExceptT.mk (Session.NUM_RING t)
  INT_ARITH t := ExceptT.mk (Session.INT_ARITH t)

initialize theRules : IO.Ref (Option HolLibrary.Q.Rules) ← IO.mkRef none

/-- The `Rules` bundle, built once, after the whole core library. -/
unsafe def BRules : HolLibrary.Q.Rules :=
  match unsafeIO (do
    match ← theRules.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      match ← (HolLibrary.Q.setupRules (deps ())).run with
      | .ok d => do theRules.set (some d); pure d
      | .error e => panic! s!"setupRules failed: {e}") with
  | .ok d => d | _ => panic! "SessionLibrary.Q: setupRules"

/-- `needs "Library/q.ml"`. -/
unsafe def ensureQ : IO Unit := do
  let _ ← IO.mkRef BRules
  pure ()

end SessionLibrary.Q

/- The module `Pa`, at the top level. -/
namespace SessionLibrary.Q.Pa
open SessionLibrary.Q (BRules)

unsafe def CONTEXT_TAC := @HolLibrary.Q.Pa.CONTEXT_TAC
unsafe def PARSE_IN_CONTEXT := @HolLibrary.Q.Pa.PARSE_IN_CONTEXT
unsafe def PARSES_IN_CONTEXT := @HolLibrary.Q.Pa.PARSES_IN_CONTEXT
unsafe def EXISTS_TAC (s : String) : tactic := HolLibrary.Q.Pa.EXISTS_TAC s
unsafe def SUBGOAL_THEN (s : String) (ttac : thm_tactic) : tactic :=
  HolLibrary.Q.Pa.SUBGOAL_THEN s ttac
unsafe def SUBGOAL_TAC (l s : String) (tacs : List tactic) : tactic :=
  HolLibrary.Q.Pa.SUBGOAL_TAC l s tacs
unsafe def ASM_CASES_TAC (s : String) : tactic := HolLibrary.Q.Pa.ASM_CASES_TAC s
unsafe def BOOL_CASES_TAC (s : String) : tactic := HolLibrary.Q.Pa.BOOL_CASES_TAC s
unsafe def SPEC_TAC (p : String × String) : tactic := HolLibrary.Q.Pa.SPEC_TAC p
unsafe def SPEC (s : String) (th : thm) : IO (Except String thm) := (HolLibrary.Q.Pa.SPEC s th).run
unsafe def SPECL (ss : List String) (th : thm) : IO (Except String thm) :=
  (HolLibrary.Q.Pa.SPECL ss th).run
unsafe def GEN (s : String) (th : thm) : IO (Except String thm) := (HolLibrary.Q.Pa.GEN s th).run
unsafe def GENL (ss : List String) (th : thm) : IO (Except String thm) :=
  (HolLibrary.Q.Pa.GENL ss th).run
unsafe def X_GEN_TAC (s : String) : tactic := HolLibrary.Q.Pa.X_GEN_TAC s
unsafe def REAL_ARITH (s : String) : IO (Except String thm) := (BRules.REAL_ARITH s).run
unsafe def REAL_FIELD (s : String) : IO (Except String thm) := (BRules.REAL_FIELD s).run
unsafe def REAL_RING (s : String) : IO (Except String thm) := (BRules.REAL_RING s).run
unsafe def ARITH_RULE (s : String) : IO (Except String thm) := (BRules.ARITH_RULE s).run
unsafe def NUM_RING (s : String) : IO (Except String thm) := (BRules.NUM_RING s).run
unsafe def INT_ARITH (s : String) : IO (Except String thm) := (BRules.INT_ARITH s).run
unsafe def ABBREV_TAC (s : String) : tactic := HolLibrary.Q.Pa.ABBREV_TAC s
unsafe def call_with_interface := @HolLibrary.Q.Pa.call_with_interface

end SessionLibrary.Q.Pa
