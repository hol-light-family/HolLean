/- File: SessionCore/Itab.lean
itab.ml: the intuitionistic tableau prover (`ITAUT`, `ITAUT_TAC`).
-/
import SessionCore.Tactics
import HolCore.Itab

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Theorems HolCore.Classic
open HolCore.Trivia HolCore.Printer

namespace Session

/- Itab: intuitionistic tableau prover. -/
def UNIFY_REFL_TAC := Itab.UNIFY_REFL_TAC B
def ITAUT_TAC := Itab.ITAUT_TAC_MAIN B
def ITAUT := Itab.ITAUT B
export Itab (UNIFY_ACCEPT_TAC)


end Session
