/- File: SessionCore/Trivia.lean
trivia.ml, built by `initialize` when this module is imported, in file
order: the `o` infix and the definitions of `o` and `I` (`triviaDefLayer`),
then the type `1` and the file's theorems (`triviaBoot`), and its theorems
as top-level names.
-/
import SessionCore.Classic
import HolCore.Trivia

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Theorems HolCore.Classic
open HolCore.Trivia HolCore.Printer

namespace Session

private def ioOk {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")

/- trivia.ml: the type `1`. -/
def new_type_definition (tyname absname repname : String) (th : thm) :
    IO (Except String thm) := ExceptT.run do
  let conv : ioconv := Simp.thencIO (Simp.ratorConvIO (Simp.REWR_CONV B C.EXISTS_THM))
                        (fun t => pure (BETA_CONV t))
  let th0 ← ExceptT.mk (Simp.convRuleIO conv th)
  let (th1, th2) ← ExceptT.mk (Kernel.new_basic_type_definition tyname absname repname th0)
  liftExcept (do
    let g1 ← B.GEN_ALL th1
    let th2' ← CONV_RULE (LAND_CONV (TRY_CONV BETA_CONV)) th2
    let g2 ← B.GEN_ALL th2'
    B.CONJ g1 g2)

/-- trivia.ml 16-22: the `o` infix and the definitions of `o` and `I`. -/
private def bootTriviaDefs : IO (thm × thm) := do
  HolCore.Printer.parse_as_infix ("o", (26, "right"))
  let odef ← ioOk "o_DEF" (do Drule.new_definition B (← ioOk "o_DEF parse" (HolCore.Parser.parse_term "(o) (f:B->C) g = \\x:A. f(g(x))")))
  let idef ← ioOk "I_DEF" (do Drule.new_definition B (← ioOk "I_DEF parse" (HolCore.Parser.parse_term "I = \\x:A. x")))
  pure (odef, idef)

initialize triviaDefLayer : thm × thm ← bootTriviaDefs

def o_DEF : thm := triviaDefLayer.1
def I_DEF : thm := triviaDefLayer.2

private def bootTrivia : IO (TriviaThms × thm × thm) := do
  let goal ← ioOk "goal" (HolCore.Parser.parse_term "?b:bool. b")
  let tW ← ioOk "T" (HolCore.Parser.parse_term "T")
  let existsOneRep ← ioOk "EXISTS_ONE_REP" (Tactics.prove B goal
    (Tactics.THEN B (Tactics.EXISTS_TAC B tW)
      (Tactics.THEN B (Tactics.BETA_TAC B) (Tactics.ACCEPT_TAC B B.TRUTH))))
  let oneTydef ← ioOk "one_tydef" (new_type_definition "1" "one_ABS" "one_REP" existsOneRep)
  let oneDef ← ioOk "one_DEF" (do Drule.new_definition B (← ioOk "one parse" (HolCore.Parser.parse_term "one = @x:1. T")))
  let tv ← ioOk "setupTrivia" (setupTrivia B T C o_DEF I_DEF existsOneRep oneTydef oneDef).run
  theInductiveTypeStore.modify (("1", (1, tv.one_INDUCT, tv.one_RECURSION)) :: ·)
  pure (tv, oneTydef, oneDef)

initialize triviaBoot : TriviaThms × thm × thm ← bootTrivia

def triviaLayer : TriviaThms := triviaBoot.1
def one_tydef : thm := triviaBoot.2.1
def one_DEF : thm := triviaBoot.2.2

/- trivia.ml (Session 1138-1153). -/
def o_ASSOC := triviaLayer.o_ASSOC
def I_THM := triviaLayer.I_THM
def I_O_ID := triviaLayer.I_O_ID
def EXISTS_ONE_REP := triviaLayer.EXISTS_ONE_REP
def one := triviaLayer.one
def one_axiom := triviaLayer.one_axiom
def one_INDUCT := triviaLayer.one_INDUCT
def one_RECURSION := triviaLayer.one_RECURSION
def one_Axiom := triviaLayer.one_Axiom
def FORALL_ONE_THM := triviaLayer.FORALL_ONE_THM
def EXISTS_ONE_THM := triviaLayer.EXISTS_ONE_THM
def ETA_ONE := triviaLayer.ETA_ONE

end Session
