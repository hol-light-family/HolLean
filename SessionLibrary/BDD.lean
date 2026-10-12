/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/bdd.ml.                                     -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/BDD.lean

  The `unsafe` half of the bdd.ml translation: it builds bdd.ml's
  load-time proformas once (`ensureBDD` is `needs "Library/bdd.ml"`) and
  exports bdd.ml's functions under their own names.
-/

import Session
import HolLibrary.BDD

open HolCore HolCore.Kernel
open Session

namespace SessionLibrary.BDD

open HolLibrary.BDD (Tables Bdd VTable UTable CTable BDDThms)

/-- The core bundles, for HolLibrary's rules. -/
unsafe instance : HolLight.HolBase := ⟨sessionB, sessionC, sessionT⟩

initialize theBDDThms : IO.Ref (Option BDDThms) ← IO.mkRef none

/-- bdd.ml's load (it has no `needs` of its own). -/
unsafe def getBDDThms : IO BDDThms := do
  match ← theBDDThms.get with
  | some k => pure k
  | none => do
    Session.ensureDefine
    match ← (HolLibrary.BDD.setupBDD (fun ths t => ExceptT.mk (Session.MESON ths t))).run with
    | .ok k => do theBDDThms.set (some k); pure k
    | .error e => panic! s!"setupBDD failed: {e}"

/-- `needs "Library/bdd.ml"`. -/
unsafe def ensureBDD : IO Unit := do
  let _ ← getBDDThms
  pure ()

private unsafe def run {α : Type} (f : BDDThms → ExceptT String IO α) : IO (Except String α) := do
  (f (← getBDDThms)).run

def BDD_1 : Int := HolLibrary.BDD.BDD_1
def BDD_0 : Int := HolLibrary.BDD.BDD_0
def mk_vtable (n : Int) : IO (Except String VTable) := (HolLibrary.BDD.mk_vtable n).run
unsafe def mk_utable : IO UTable := HolLibrary.BDD.mk_utable
def mk_ctable : IO CTable := HolLibrary.BDD.mk_ctable
def num_of_var (vt : VTable) (v : term) : IO (Except String Int) :=
  (HolLibrary.BDD.num_of_var vt v).run
def var_of_num (varray : IO.Ref (Array term)) (n : Int) : IO (Except String term) :=
  (HolLibrary.BDD.var_of_num varray n).run
def bdd_expand (uarray : IO.Ref (HolCore.Lib.Func Int ((Int × Int × Int) × thm))) (b : Int) :
    IO (Except String (Int × Int × Int)) := (HolLibrary.BDD.bdd_expand uarray b).run
unsafe def btm_of_int (uarray : IO.Ref (HolCore.Lib.Func Int ((Int × Int × Int) × thm)))
    (n : Int) : IO (Except String term) := run (HolLibrary.BDD.btm_of_int · uarray n)
unsafe def lookup_triple (varray : IO.Ref (Array term)) (ut : UTable) (tr : Int × Int × Int) :
    IO (Except String Int) := run (HolLibrary.BDD.lookup_triple · varray ut tr)
unsafe def BDD_EXPAND (uarray : IO.Ref (HolCore.Lib.Func Int ((Int × Int × Int) × thm)))
    (b : Int) : IO (Except String thm) := run (HolLibrary.BDD.BDD_EXPAND · uarray b)
unsafe def BDD_LOOKUP (varray : IO.Ref (Array term)) (ut : UTable) (vlr : Int × Int × Int) :
    IO (Except String (thm × Int × Int)) := run (HolLibrary.BDD.BDD_LOOKUP · varray ut vlr)
unsafe def bdd_and (tt : IO.Ref (Array term) × UTable × CTable) (lr : Int × Int) :
    IO (Except String (Int × Int)) := run (HolLibrary.BDD.bdd_and · tt lr)
unsafe def BDD_TRUE : IO Bdd := do return (← getBDDThms).BDD_TRUE
unsafe def BDD_FALSE : IO Bdd := do return (← getBDDThms).BDD_FALSE
unsafe def BDD_VAR (tt : Tables) (tm : term) : IO (Except String Bdd) :=
  run (HolLibrary.BDD.BDD_VAR · tt tm)
unsafe def BDD_NEG (tt : Tables) (b : Bdd) : IO (Except String Bdd) :=
  run (HolLibrary.BDD.BDD_NEG · tt b)
unsafe def BDD_AND (tt : Tables) (bs : Bdd × Bdd) : IO (Except String Bdd) :=
  run (HolLibrary.BDD.BDD_AND · tt bs)
unsafe def BDD_OR (tt : Tables) (bs : Bdd × Bdd) : IO (Except String Bdd) :=
  run (HolLibrary.BDD.BDD_OR · tt bs)
unsafe def BDD_IMP (tt : Tables) (bs : Bdd × Bdd) : IO (Except String Bdd) :=
  run (HolLibrary.BDD.BDD_IMP · tt bs)
unsafe def BDD_IFF (tt : Tables) (bs : Bdd × Bdd) : IO (Except String Bdd) :=
  run (HolLibrary.BDD.BDD_IFF · tt bs)
unsafe def BDD_OF_TERM (defs : HolCore.Lib.Func term Bdd) (tt : Tables) (tm : term) :
    IO (Except String Bdd) := run (HolLibrary.BDD.BDD_OF_TERM · defs tt tm)
unsafe def BDD_EXISTS (tt : Tables) (x : term) :
    IO (Except String (Bdd → IO (Except String Bdd))) := do
  match ← run (HolLibrary.BDD.BDD_EXISTS · tt x) with
  | .ok f => return .ok (fun b => (f b).run)
  | .error e => return .error e
def bdd_stats (nd : Int) (vt : VTable) (ct : CTable) (ut : UTable) : IO Unit :=
  HolLibrary.BDD.bdd_stats nd vt ct ut
/-- `BDD_TAUT tm` (bdd.ml 394). -/
unsafe def BDD_TAUT (tm : term) : IO (Except String thm) := run (HolLibrary.BDD.BDD_TAUT · tm)
/-- `BDD_DEFTAUT ivars tm` (bdd.ml 406). -/
unsafe def BDD_DEFTAUT (ivars : List term) (tm : term) : IO (Except String thm) :=
  run (HolLibrary.BDD.BDD_DEFTAUT · ivars tm)

end SessionLibrary.BDD
