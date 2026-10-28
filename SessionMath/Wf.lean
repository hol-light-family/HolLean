/- File: SessionMath/Wf.lean
wf.ml: wellfounded relations (`Wf`), built by `initialize` when this module
is imported, with WF_INDUCT_TAC's proformas and its `qqconv` (boxed in
`WfQqconvBox`: an `initialize` must not have a function type).
-/
import SessionMath.Arith
import HolMath.Wf

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic

namespace Session

private def ioOk' {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")


/- ---------------------------------------------------------------------- -/
/- wf.ml : theory of wellfounded relations.                               -/
/- ---------------------------------------------------------------------- -/

initialize Wf : HolMath.Wf.WfThms ← do
  -- wf.ml declares `<<` (and later `<<<`) before its terms are parsed.
  HolMath.Wf.setupWfInfixes
  ioOk' "setupWf" (HolMath.Wf.setupWf new_definition arith2 arith3 arith4 arith9 Nm Pr ETA_AX
    MESON_TAC ASM_MESON_TAC
    prove_recursive_functions_exist prove_inductive_relations_exist
    SELECT_CONV).run

def WF                   : thm := Wf.WF
def WF_EQ                : thm := Wf.WF_EQ
def WF_IND               : thm := Wf.WF_IND
def WF_DCHAIN            : thm := Wf.WF_DCHAIN
def WF_DCHAIN_TRANSITIVE : thm := Wf.WF_DCHAIN_TRANSITIVE
def WF_UREC              : thm := Wf.WF_UREC
def WF_UREC_WF           : thm := Wf.WF_UREC_WF
def WF_REC_INVARIANT     : thm := Wf.WF_REC_INVARIANT
def WF_REC               : thm := Wf.WF_REC
def WF_REC_WF            : thm := Wf.WF_REC_WF
def WF_EREC              : thm := Wf.WF_EREC
def WF_REC_EXISTS        : thm := Wf.WF_REC_EXISTS
def WF_SUBSET            : thm := Wf.WF_SUBSET
def WF_RESTRICT          : thm := Wf.WF_RESTRICT
def WF_MEASURE_GEN       : thm := Wf.WF_MEASURE_GEN
def WF_LEX_DEPENDENT     : thm := Wf.WF_LEX_DEPENDENT
def WF_LEX               : thm := Wf.WF_LEX
def WF_POINTWISE         : thm := Wf.WF_POINTWISE
def WF_num               : thm := Wf.WF_num
def WF_REC_num           : thm := Wf.WF_REC_num
def MEASURE              : thm := Wf.MEASURE
def WF_MEASURE           : thm := Wf.WF_MEASURE
def MEASURE_LE           : thm := Wf.MEASURE_LE
def WF_ANTISYM           : thm := Wf.WF_ANTISYM
def WF_REFL              : thm := Wf.WF_REFL
def WF_FALSE             : thm := Wf.WF_FALSE
def MINIMAL_BAD_SEQUENCE : thm := Wf.MINIMAL_BAD_SEQUENCE
def WF_REC_TAIL          : thm := Wf.WF_REC_TAIL
def WF_REC_TAIL_GENERAL  : thm := Wf.WF_REC_TAIL_GENERAL

/-- `WF_INDUCT_TAC`'s two `MESON`-proved proformas, built by
    `setupWfInductPths` in a clean parser context. -/
initialize WfInductPths : thm × thm ←
  ioOk' "setupWfInductPths" (HolMath.Wf.setupWfInductPths MESON_TAC).run

/- WF_INDUCT_TAC's `qqconv = GEN_REWRITE_CONV I [pth]`, with its net built
   once, as wf.ml builds it. -/
/-- A function-valued `initialize` constant is unusable from importing
    modules (Lean 4.35: calling it segfaults natively, "unreachable code" when
    interpreted; https://github.com/leanprover/lean4/issues/15768), so the
    conversion is kept in a one-field structure. -/
structure WfQqconvBox where
  conv : ioconv
  deriving Inhabited

initialize wfQqconvBox : WfQqconvBox ← do
  return ⟨← ioOk' "WF_INDUCT_TAC qqconv" (Simp.GEN_REWRITE_CONV B id [WfInductPths.1])⟩

def WfQqconv : ioconv := wfQqconvBox.conv

/-- `WF_INDUCT_TAC` (wf.ml): wellfounded induction on a free measured term.
    The two `MESON`-proved proformas come from `setupWfInductPths`; `num_WF`
    from arith.ml. -/
def WF_INDUCT_TAC (tm : term) : tactic :=
  HolMath.Wf.WF_INDUCT_TAC WfQqconv WfInductPths.2 arith4.num_WF tm

/- ---------------------------------------------------------------------- -/

end Session
