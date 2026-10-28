/- File: SessionCore/FirstOrder.lean
firstorder.ml: the first-order shadow-term facilities, with their own
term/code stores (`foVstore`, ...), created by `initialize` when this module
is imported.
-/
import SessionCore.Meson
import HolCore.FirstOrder

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Theorems HolCore.Classic
open HolCore.Trivia HolCore.Printer

namespace Session


/-- `parse_term`, panicking with context on failure (for the load-time
    quotations below). -/
private def ptm (s : String) : IO term := do
  match ← HolCore.Parser.parse_term s with
  | .ok t => pure t
  | .error e => throw (IO.userError s!"parse {s}: {e}")


initialize foVstore : IO.Ref (List (term × Int)) ← IO.mkRef []
initialize foGstore : IO.Ref (List (term × Int)) ← IO.mkRef []
initialize foVcounter : IO.Ref Int ← IO.mkRef 0
initialize foCstore : IO.Ref (List (term × Int)) ← IO.mkRef []
initialize foCcounter : IO.Ref Int ← IO.mkRef 2

/-- FirstOrder's own term↔code stores (separate from MESON's). -/
def FoS : Meson.FolStores :=
  { vstore := foVstore, gstore := foGstore, vcounter := foVcounter,
    cstore := foCstore, ccounter := foCcounter }

def fo_reset_vars : IO Unit := FirstOrder.Mapping.reset_vars FoS
def fo_reset_consts : IO (Except String Unit) := FirstOrder.Mapping.reset_consts FoS
def fo_fol_of_term (env consts : List term) (tm : term) :
    IO (Except String Meson.fol_term) := FirstOrder.Mapping.fol_of_term FoS env consts tm
def fo_fol_of_form (env consts : List term) (tm : term) :
    IO (Except String Meson.fol_form) := FirstOrder.Mapping.fol_of_form FoS env consts tm
def fo_hol_of_term (ty : hol_type) (tm : Meson.fol_term) : IO (Except String term) :=
  FirstOrder.Mapping.hol_of_term FoS ty tm
def fo_fol_of_hol_clauses (thms : List thm) : IO (Except String Meson.ancestors) :=
  FirstOrder.Mapping.fol_of_hol_clauses FoS thms

end Session
