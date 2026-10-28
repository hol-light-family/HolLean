/- File: SessionCore/Meson.lean
meson.ml: the MESON prover (`mesonLayer` and its stores), built by
`initialize` when this module is imported, and `MESON`, `MESON_TAC`,
`ASM_MESON_TAC` and `GEN_MESON_TAC` over them.
-/
import SessionCore.Canon
import HolCore.Meson

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Theorems HolCore.Classic
open HolCore.Trivia HolCore.Printer

namespace Session

private def ioOk {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")

initialize mesonLayer : Meson.MesonThms ← ioOk "setupMeson" (Meson.setupMeson B T C).run

initialize mesonInferences : IO.Ref Int ← IO.mkRef 0
initialize mesonContraposCache : Meson.ContraposCache ← IO.mkRef []
initialize mesonVstore : IO.Ref (List (term × Int)) ← IO.mkRef []
initialize mesonGstore : IO.Ref (List (term × Int)) ← IO.mkRef []
initialize mesonVcounter : IO.Ref Int ← IO.mkRef 0
initialize mesonCstore : IO.Ref (List (term × Int)) ← IO.mkRef []
initialize mesonCcounter : IO.Ref Int ← IO.mkRef 2

def MesonS : Meson.FolStores :=
  { vstore := mesonVstore, gstore := mesonGstore, vcounter := mesonVcounter,
    cstore := mesonCstore, ccounter := mesonCcounter }

def Mn : Meson.MesonThms := mesonLayer

def MesonD : Meson.MesonTacDeps :=
  { presimp    := Canon.PRESIMP_CONV B T C
    nnf        := Canon.NNF_CONV B Cn.nnf
    skolem     := Canon.SKOLEM_CONV B T C
    prenex     := Canon.PRENEX_CONV B T C
    condsCelim := Canon.CONDS_CELIM_CONV B Cn.conds
    weakCnf    := Canon.weakCnfConv B Cn
    quantBool  := Meson.QUANT_BOOL_CONV B T C
    lambdaElim := Canon.LAMBDA_ELIM_CONV B Cn.selLam
    assocDisj  := (match Canon.ASSOC_CONV B T.DISJ_ASSOC with
                   | .ok c => c | .error _ => fun _ => pure (.error "ASSOC_CONV DISJ_ASSOC"))
    selectElim := Canon.SELECT_ELIM_TAC B Cn.selLam
    asmFol     := Canon.ASM_FOL_TAC B Cn.fol
    refuteThen := fun ttac => Classic.REFUTE_THEN B (Simp.REWR_CONV B C.refuteThenPth) C.refuteF ttac }

def MESON_TAC (ths : List thm) : tactic := fun g => do
  Meson.MESON_TAC B MesonD (← Meson.readConfig) MesonS mesonInferences
    Mn.pths Mn.eqAx Mn.brand mesonContraposCache ths g
def MESON (ths : List thm) (tm : term) : IO (Except String thm) := do
  Meson.MESON B MesonD (← Meson.readConfig) MesonS mesonInferences
    Mn.pths Mn.eqAx Mn.brand mesonContraposCache ths tm

/-- `GEN_MESON_TAC min max step ths`. -/
def GEN_MESON_TAC (min max step : Int) (ths : List thm) : tactic := fun g => do
  Meson.GEN_MESON_TAC B MesonD (← Meson.readConfig) MesonS mesonInferences
    Mn.pths Mn.eqAx Mn.brand mesonContraposCache min max step ths g

/-- meson.ml's settable parameters (`meson_depth := true`, ...). -/
abbrev meson_depth := Meson.meson_depth
abbrev meson_prefine := Meson.meson_prefine
abbrev meson_dcutin := Meson.meson_dcutin
abbrev meson_skew := Meson.meson_skew
abbrev meson_brand := Meson.meson_brand
abbrev meson_split_limit := Meson.meson_split_limit
abbrev meson_chatty := Meson.meson_chatty

def ASM_MESON_TAC (ths : List thm) : tactic := fun g => do
  Meson.ASM_MESON_TAC B MesonD (← Meson.readConfig) MesonS mesonInferences
    Mn.pths Mn.eqAx Mn.brand mesonContraposCache ths g

end Session
