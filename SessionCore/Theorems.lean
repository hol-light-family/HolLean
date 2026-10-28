/- File: SessionCore/Theorems.lean
theorems.ml: the standard logical theorems (`theoremsLayer`, the bundle
`T`), built quietly by `initialize` when this module is imported, the
theorems.ml tactic DSL, and the theorems as top-level names.  Also the
monotonicity and inductive-type stores, which theorems.ml's successors fill.
-/
import SessionCore.Simp
import HolCore.Theorems

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Theorems HolCore.Classic
open HolCore.Trivia HolCore.Printer

namespace Session

private def ioOk {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")

/- theorems.ml and class.ml (quietly, as Session.lean does). -/
initialize theMonotonicityTheorems : IO.Ref (List thm) ← IO.mkRef []
initialize theInductiveTypeStore : IO.Ref (List (String × (Int × thm × thm))) ← IO.mkRef []

/-- theorems.ml, run quietly (as the old Session did). -/
private def bootTheorems : IO TheoremThms := do
  let verb ← HolCore.Lib.verbose.get
  let tiw ← HolCore.Preterm.type_invention_warning.get
  HolCore.Lib.verbose.set false
  HolCore.Preterm.type_invention_warning.set false
  let t ← ioOk "setupTheorems" (setupTheorems B).run
  HolCore.Lib.verbose.set verb
  HolCore.Preterm.type_invention_warning.set tiw
  pure t

initialize theoremsLayer : TheoremThms ← bootTheorems

def T : TheoremThms := theoremsLayer

/- theorems.ml: the standard logical theorems (Session 636-707). -/
def EQ_REFL := T.EQ_REFL
def REFL_CLAUSE := T.REFL_CLAUSE
/-- `AC acsuite` (theorems.ml): prove an equation between terms equal up to
    the associativity and commutativity given by `acsuite`. -/
def AC (acsuite : thm) (tm : term) : IO (Except String thm) :=
  Theorems.AC B T.REFL_CLAUSE acsuite tm
def EQ_SYM := T.EQ_SYM
def EQ_SYM_EQ := T.EQ_SYM_EQ
def BETA_THM := T.BETA_THM
def ABS_SIMP := T.ABS_SIMP
def DISJ_ASSOC := T.DISJ_ASSOC
def DISJ_SYM := T.DISJ_SYM
def DISJ_ACI := T.DISJ_ACI
def RIGHT_OR_DISTRIB := T.RIGHT_OR_DISTRIB
def FORALL_SIMP := T.FORALL_SIMP
def EXISTS_SIMP := T.EXISTS_SIMP
def EQ_IMP := T.EQ_IMP
def EQ_CLAUSES := T.EQ_CLAUSES
def NOT_CLAUSES_WEAK := T.NOT_CLAUSES_WEAK
def AND_CLAUSES := T.AND_CLAUSES
def OR_CLAUSES := T.OR_CLAUSES
def IMP_CLAUSES := T.IMP_CLAUSES
def EXISTS_UNIQUE_THM := T.EXISTS_UNIQUE_THM
def EXISTS_UNIQUE_REFL := T.EXISTS_UNIQUE_REFL
def FORALL_UNWIND_THM2 := T.FORALL_UNWIND_THM2
def FORALL_UNWIND_THM1 := T.FORALL_UNWIND_THM1
def SWAP_EXISTS_THM := T.SWAP_EXISTS_THM
def FORALL_AND_THM := T.FORALL_AND_THM
def LEFT_AND_FORALL_THM := T.LEFT_AND_FORALL_THM
def RIGHT_AND_FORALL_THM := T.RIGHT_AND_FORALL_THM
def EXISTS_OR_THM := T.EXISTS_OR_THM
def OR_EXISTS_THM := T.OR_EXISTS_THM
def LEFT_OR_EXISTS_THM := T.LEFT_OR_EXISTS_THM
def RIGHT_OR_EXISTS_THM := T.RIGHT_OR_EXISTS_THM
def LEFT_EXISTS_AND_THM := T.LEFT_EXISTS_AND_THM
def RIGHT_EXISTS_AND_THM := T.RIGHT_EXISTS_AND_THM
def TRIV_EXISTS_AND_THM := T.TRIV_EXISTS_AND_THM
def LEFT_AND_EXISTS_THM := T.LEFT_AND_EXISTS_THM
def RIGHT_AND_EXISTS_THM := T.RIGHT_AND_EXISTS_THM
def TRIV_AND_EXISTS_THM := T.TRIV_AND_EXISTS_THM
def TRIV_FORALL_OR_THM := T.TRIV_FORALL_OR_THM
def TRIV_OR_FORALL_THM := T.TRIV_OR_FORALL_THM
def TRIV_FORALL_IMP_THM := T.TRIV_FORALL_IMP_THM
def TRIV_EXISTS_IMP_THM := T.TRIV_EXISTS_IMP_THM
def MONO_AND := T.MONO_AND
def MONO_OR := T.MONO_OR
def MONO_IMP := T.MONO_IMP
def MONO_NOT := T.MONO_NOT
def WLOG_RELATION := T.WLOG_RELATION
def EXISTS_UNIQUE_ALT := T.EXISTS_UNIQUE_ALT
def EXISTS_UNIQUE := T.EXISTS_UNIQUE

/- The theorems.ml tactic DSL (pure). -/
def DSL : DSLThms :=
  setupTacticDSL B T.SWAP_FORALL_THM T.AND_FORALL_THM T.RIGHT_IMP_FORALL_THM

def DESTRUCT_TAC := DSL.DESTRUCT_TAC
def FIX_TAC      := DSL.FIX_TAC
def INTRO_TAC    := DSL.INTRO_TAC
def HYP_TAC      := DSL.HYP_TAC
def CLAIM_TAC    := DSL.CLAIM_TAC

end Session
