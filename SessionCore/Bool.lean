/- File: SessionCore/Bool.lean
bool.ml: the boolean constants and their theorems and rules, built by
`initialize` when this module is imported (`boolLayer`, the bundle `B`),
and bool.ml's names (`CONJ`, `SPEC`, `DISCH`, ...) as top-level names.
-/
import SessionCore.Base
import HolCore.Bool

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Theorems HolCore.Classic
open HolCore.Trivia HolCore.Printer

namespace Session


deriving instance Inhabited for HolCore.Bool.BoolThms

private def parseLoadQuotes (qs : List String) : IO Unit := do
  for s in qs do
    match ← HolCore.Parser.parse_term s with
    | .ok _ => pure ()
    | .error e => throw (IO.userError s!"load quotation {s}: {e}")

private def ioOk {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")

private def bootBool : IO (BoolThms × thm) := do
  let b ← ioOk "setupBool" setupBool.run
  ioOk "set_verbose_symbols" HolCore.Bool.set_verbose_symbols
  parseLoadQuotes ["(/\\)", "(\\/)"]
  let fal ← ioOk "_FALSITY_" (do
    Drule.new_definition b (← ioOk "_FALSITY_ parse" (HolCore.Parser.parse_term "_FALSITY_ = F")))
  parseLoadQuotes ["_FALSITY_", "_FALSITY_", "T", "F", "p /\\ (q ==> r)", "p ==> q", "T"]
  pure (b, fal)

/-- bool.ml, run when this module is loaded. -/
initialize boolLayer : BoolThms × thm ← bootBool

def B : BoolThms := boolLayer.1
def FALSITY_DEF : thm := boolLayer.2

/- Expose the `BoolThms` rules/theorems as top-level names, so tests can write
   `CONJ`, `SPEC`, `DISCH`, … (HOL Light style) instead of `B.CONJ`. -/
def T_DEF := B.T_DEF
def TRUTH := B.TRUTH
def EQT_ELIM := B.EQT_ELIM
def EQT_INTRO := B.EQT_INTRO
def AND_DEF := B.AND_DEF
def CONJ := B.CONJ
def CONJUNCT1 := B.CONJUNCT1
def CONJUNCT2 := B.CONJUNCT2
def CONJ_PAIR := B.CONJ_PAIR
def CONJUNCTS := B.CONJUNCTS
def IMP_DEF := B.IMP_DEF
def MP := B.MP
def DISCH := B.DISCH
def DISCH_ALL := B.DISCH_ALL
def UNDISCH := B.UNDISCH
def UNDISCH_ALL := B.UNDISCH_ALL
def IMP_ANTISYM_RULE := B.IMP_ANTISYM_RULE
def ADD_ASSUM := B.ADD_ASSUM
def EQ_IMP_RULE := B.EQ_IMP_RULE
def IMP_TRANS := B.IMP_TRANS
def FORALL_DEF := B.FORALL_DEF
def SPEC := B.SPEC
def SPECL := B.SPECL
def SPEC_VAR := B.SPEC_VAR
def SPEC_ALL := B.SPEC_ALL
def GEN := B.GEN
def GENL := B.GENL
def GEN_ALL := B.GEN_ALL
def ISPEC := B.ISPEC
def ISPECL := B.ISPECL
def EXISTS_DEF := B.EXISTS_DEF
def EXISTS := B.EXISTS
def SIMPLE_EXISTS := B.SIMPLE_EXISTS
def CHOOSE := B.CHOOSE
def SIMPLE_CHOOSE := B.SIMPLE_CHOOSE
def OR_DEF := B.OR_DEF
def DISJ1 := B.DISJ1
def DISJ2 := B.DISJ2
def DISJ_CASES := B.DISJ_CASES
def SIMPLE_DISJ_CASES := B.SIMPLE_DISJ_CASES
def F_DEF := B.F_DEF
def NOT_DEF := B.NOT_DEF
def NOT_ELIM := B.NOT_ELIM
def NOT_INTRO := B.NOT_INTRO
def EQF_INTRO := B.EQF_INTRO
def EQF_ELIM := B.EQF_ELIM
def CONTR := B.CONTR
def EXISTS_UNIQUE_DEF := B.EXISTS_UNIQUE_DEF
def EXISTENCE := B.EXISTENCE


end Session
