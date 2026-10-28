/- File: SessionCore/Canon.lean
canon.ml: the canonical-form conversions (`canonLayer`, the bundle `Cn`),
built by `initialize` when this module is imported, as top-level names.
-/
import SessionCore.Trivia
import HolCore.Canon

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Theorems HolCore.Classic
open HolCore.Trivia HolCore.Printer

namespace Session

private def ioOk {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")

initialize canonLayer : Canon.CanonThms ← do
  let propsimps ← Simp.basic_net
  ioOk "setupCanon" (Canon.setupCanon B T C ETA_AX SELECT_AX triviaLayer.I_THM propsimps).run


def Cn : Canon.CanonThms := canonLayer

/- canon.ml conversions (Session 1166-1192). -/
def PRESIMP_CONV : term → IO (Except String thm) := Canon.PRESIMP_CONV B T C
def SKOLEM_CONV : term → IO (Except String thm) := Canon.SKOLEM_CONV B T C
def PRENEX_CONV : term → IO (Except String thm) := Canon.PRENEX_CONV B T C
def CONJ_CANON_CONV : term → IO (Except String thm) := Canon.CONJ_CANON_CONV B
def DISJ_CANON_CONV : term → IO (Except String thm) := Canon.disjCanonConv B Cn
def NNF_CONV : term → IO (Except String thm) := Canon.NNF_CONV B Cn.nnf
def NNFC_CONV : term → IO (Except String thm) := Canon.NNFC_CONV B Cn.nnf
def WEAK_DNF_CONV : term → IO (Except String thm) := Canon.weakDnfConv B Cn
def DNF_CONV : term → IO (Except String thm) := Canon.dnfConv B Cn
def WEAK_CNF_CONV : term → IO (Except String thm) := Canon.weakCnfConv B Cn
def CNF_CONV : term → IO (Except String thm) := Canon.cnfConv B Cn
def SELECT_ELIM_TAC : tactic := Canon.SELECT_ELIM_TAC B Cn.selLam
def LAMBDA_ELIM_CONV : term → IO (Except String thm) := Canon.LAMBDA_ELIM_CONV B Cn.selLam
def CONDS_ELIM_CONV : term → IO (Except String thm) := Canon.CONDS_ELIM_CONV B Cn.conds
def CONDS_CELIM_CONV : term → IO (Except String thm) := Canon.CONDS_CELIM_CONV B Cn.conds
def ASSOC_CONV (th : thm) : Except String (term → IO (Except String thm)) :=
  Canon.ASSOC_CONV B th
def PROP_ATOM_CONV : (term → IO (Except String thm)) → term → IO (Except String thm) :=
  Canon.PROP_ATOM_CONV
def ASM_FOL_TAC : tactic := Canon.ASM_FOL_TAC B Cn.fol

end Session
