/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/q.ml.                                       -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Q.lean

  The session half of the q.ml translation: it supplies HolLibrary.Q's
  dependencies from Session, builds the `Rules` bundle, and exports the
  module `Pa` as `SessionLibrary.Q.Pa`, under its HOL Light names
  (`Pa.EXISTS_TAC "x"`, `Pa.SPECL ["m"; "n"] th`, `Pa.REAL_ARITH "..."`).
  Importing this module is `needs "Library/q.ml"` (q.ml has no `needs`).
-/

import Session
import HolLibrary.Q

open HolCore HolCore.Kernel
open HolCore.Tactics (tactic thm_tactic)

namespace SessionLibrary.Q

/-- `prioritize_num`, `prioritize_int`: make the type the default for
    overloaded symbols (as SessionLibrary.Integer). -/
private def prioritizeType (name : String) : IO Unit := do
  match ← HolCore.Kernel.mk_type name [] with
  | .ok ty => Session.prioritize_overload ty
  | .error e => throw (IO.userError e)

/-- What q.ml uses from Session. -/
def deps : HolLibrary.Q.QDeps where
  prioritize_real := Session.prioritize_real
  prioritize_num := prioritizeType "num"
  prioritize_int := prioritizeType "int"
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH3 t)
  REAL_FIELD t := ExceptT.mk (Session.REAL_FIELD t)
  REAL_RING t := ExceptT.mk (Session.REAL_RING t)
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  NUM_RING t := ExceptT.mk (Session.NUM_RING t)
  INT_ARITH t := ExceptT.mk (Session.INT_ARITH t)

/-- The `Rules` bundle (q.ml), built when this module is loaded. -/
initialize BRules : HolLibrary.Q.Rules ← do
  match ← (HolLibrary.Q.setupRules deps).run with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"setupRules failed: {e}")

/-- `needs "Library/q.ml"`: already done by importing this module. -/
def ensureQ : IO Unit := pure ()

end SessionLibrary.Q

/- The module `Pa`, at the top level. -/
namespace SessionLibrary.Q.Pa
open SessionLibrary.Q (BRules)

def CONTEXT_TAC := @HolLibrary.Q.Pa.CONTEXT_TAC
def PARSE_IN_CONTEXT := @HolLibrary.Q.Pa.PARSE_IN_CONTEXT
def PARSES_IN_CONTEXT := @HolLibrary.Q.Pa.PARSES_IN_CONTEXT
def EXISTS_TAC (s : String) : tactic := HolLibrary.Q.Pa.EXISTS_TAC s
def SUBGOAL_THEN (s : String) (ttac : thm_tactic) : tactic :=
  HolLibrary.Q.Pa.SUBGOAL_THEN s ttac
def SUBGOAL_TAC (l s : String) (tacs : List tactic) : tactic :=
  HolLibrary.Q.Pa.SUBGOAL_TAC l s tacs
def ASM_CASES_TAC (s : String) : tactic := HolLibrary.Q.Pa.ASM_CASES_TAC s
def BOOL_CASES_TAC (s : String) : tactic := HolLibrary.Q.Pa.BOOL_CASES_TAC s
def SPEC_TAC (p : String × String) : tactic := HolLibrary.Q.Pa.SPEC_TAC p
def SPEC (s : String) (th : thm) : IO (Except String thm) := (HolLibrary.Q.Pa.SPEC s th).run
def SPECL (ss : List String) (th : thm) : IO (Except String thm) :=
  (HolLibrary.Q.Pa.SPECL ss th).run
def GEN (s : String) (th : thm) : IO (Except String thm) := (HolLibrary.Q.Pa.GEN s th).run
def GENL (ss : List String) (th : thm) : IO (Except String thm) :=
  (HolLibrary.Q.Pa.GENL ss th).run
def X_GEN_TAC (s : String) : tactic := HolLibrary.Q.Pa.X_GEN_TAC s
def REAL_ARITH (s : String) : IO (Except String thm) := (BRules.REAL_ARITH s).run
def REAL_FIELD (s : String) : IO (Except String thm) := (BRules.REAL_FIELD s).run
def REAL_RING (s : String) : IO (Except String thm) := (BRules.REAL_RING s).run
def ARITH_RULE (s : String) : IO (Except String thm) := (BRules.ARITH_RULE s).run
def NUM_RING (s : String) : IO (Except String thm) := (BRules.NUM_RING s).run
def INT_ARITH (s : String) : IO (Except String thm) := (BRules.INT_ARITH s).run
def ABBREV_TAC (s : String) : tactic := HolLibrary.Q.Pa.ABBREV_TAC s
def call_with_interface := @HolLibrary.Q.Pa.call_with_interface

end SessionLibrary.Q.Pa
