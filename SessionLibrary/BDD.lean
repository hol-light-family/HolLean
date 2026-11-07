/- File: SessionLibrary/BDD.lean
The session half of the bdd.ml translation: it supplies HolLibrary.BDD's
dependencies from Session and exports every bdd.ml function under its own
name.  Importing this module is `needs "Library/bdd.ml"`: the load-time
proformas (`BBDDThms`) are built by `initialize` when the module is loaded.
bdd.ml's `needs "Library/define.ml"` is satisfied by importing Session.
-/

import Session
import HolLibrary.BDD

open HolCore HolCore.Kernel

namespace SessionLibrary.BDD

open HolLibrary.BDD (Tables Bdd VTable UTable CTable BDDThms)

/-- bdd.ml's load (it has no `needs` of its own; define.ml has already loaded
    with the Session import).  Built once, eagerly.  A failed setup throws, as
    Session panics. -/
initialize BBDDThms : BDDThms ← do
  if !(← Session.bundlesWanted) then return default
  Session.ensureDefine
  match ← Session.quietly (HolLibrary.BDD.setupBDD (fun ths t => ExceptT.mk (Session.MESON ths t))).run with
  | .ok k => pure k
  | .error e => throw (IO.userError s!"setupBDD failed: {e}")

/-- `getBDDThms`: the bundle (eager, so a plain accessor). -/
def getBDDThms : IO BDDThms := pure BBDDThms

/-- A no-op: importing this module has loaded bdd.ml.  Kept for callers of
    the old `ensureBDD`. -/
def ensureBDD : IO Unit := pure ()

private def run {α : Type} (f : BDDThms → ExceptT String IO α) : IO (Except String α) := do
  (f BBDDThms).run

def BDD_1 : Int := HolLibrary.BDD.BDD_1
def BDD_0 : Int := HolLibrary.BDD.BDD_0
def mk_vtable (n : Int) : IO (Except String VTable) := (HolLibrary.BDD.mk_vtable n).run
def mk_utable : IO UTable := HolLibrary.BDD.mk_utable
def mk_ctable : IO CTable := HolLibrary.BDD.mk_ctable
def num_of_var (vt : VTable) (v : term) : IO (Except String Int) :=
  (HolLibrary.BDD.num_of_var vt v).run
def var_of_num (varray : IO.Ref (Array term)) (n : Int) : IO (Except String term) :=
  (HolLibrary.BDD.var_of_num varray n).run
def bdd_expand (uarray : IO.Ref (HolCore.Lib.Func Int ((Int × Int × Int) × thm))) (b : Int) :
    IO (Except String (Int × Int × Int)) := (HolLibrary.BDD.bdd_expand uarray b).run
def btm_of_int (uarray : IO.Ref (HolCore.Lib.Func Int ((Int × Int × Int) × thm)))
    (n : Int) : IO (Except String term) := run (HolLibrary.BDD.btm_of_int · uarray n)
def lookup_triple (varray : IO.Ref (Array term)) (ut : UTable) (tr : Int × Int × Int) :
    IO (Except String Int) := run (HolLibrary.BDD.lookup_triple · varray ut tr)
def BDD_EXPAND (uarray : IO.Ref (HolCore.Lib.Func Int ((Int × Int × Int) × thm)))
    (b : Int) : IO (Except String thm) := run (HolLibrary.BDD.BDD_EXPAND · uarray b)
def BDD_LOOKUP (varray : IO.Ref (Array term)) (ut : UTable) (vlr : Int × Int × Int) :
    IO (Except String (thm × Int × Int)) := run (HolLibrary.BDD.BDD_LOOKUP · varray ut vlr)
def bdd_and (tt : IO.Ref (Array term) × UTable × CTable) (lr : Int × Int) :
    IO (Except String (Int × Int)) := run (HolLibrary.BDD.bdd_and · tt lr)
def BDD_TRUE : IO Bdd := do return BBDDThms.BDD_TRUE
def BDD_FALSE : IO Bdd := do return BBDDThms.BDD_FALSE
def BDD_VAR (tt : Tables) (tm : term) : IO (Except String Bdd) :=
  run (HolLibrary.BDD.BDD_VAR · tt tm)
def BDD_NEG (tt : Tables) (b : Bdd) : IO (Except String Bdd) :=
  run (HolLibrary.BDD.BDD_NEG · tt b)
def BDD_AND (tt : Tables) (bs : Bdd × Bdd) : IO (Except String Bdd) :=
  run (HolLibrary.BDD.BDD_AND · tt bs)
def BDD_OR (tt : Tables) (bs : Bdd × Bdd) : IO (Except String Bdd) :=
  run (HolLibrary.BDD.BDD_OR · tt bs)
def BDD_IMP (tt : Tables) (bs : Bdd × Bdd) : IO (Except String Bdd) :=
  run (HolLibrary.BDD.BDD_IMP · tt bs)
def BDD_IFF (tt : Tables) (bs : Bdd × Bdd) : IO (Except String Bdd) :=
  run (HolLibrary.BDD.BDD_IFF · tt bs)
def BDD_OF_TERM (defs : HolCore.Lib.Func term Bdd) (tt : Tables) (tm : term) :
    IO (Except String Bdd) := run (HolLibrary.BDD.BDD_OF_TERM · defs tt tm)
def BDD_EXISTS (tt : Tables) (x : term) :
    IO (Except String (Bdd → IO (Except String Bdd))) := do
  match ← run (HolLibrary.BDD.BDD_EXISTS · tt x) with
  | .ok f => return .ok (fun b => (f b).run)
  | .error e => return .error e
def bdd_stats (nd : Int) (vt : VTable) (ct : CTable) (ut : UTable) : IO Unit :=
  HolLibrary.BDD.bdd_stats nd vt ct ut
/-- `BDD_TAUT tm` (bdd.ml 394). -/
def BDD_TAUT (tm : term) : IO (Except String thm) := run (HolLibrary.BDD.BDD_TAUT · tm)
/-- `BDD_DEFTAUT ivars tm` (bdd.ml 406). -/
def BDD_DEFTAUT (ivars : List term) (tm : term) : IO (Except String thm) :=
  run (HolLibrary.BDD.BDD_DEFTAUT · ivars tm)

end SessionLibrary.BDD
