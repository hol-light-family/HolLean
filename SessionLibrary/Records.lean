/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/records.ml.                                 -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Records.lean

  The session half of the records.ml translation: it holds
  `the_record_types` (records.ml 31), supplies HolLibrary.Records'
  dependencies from Session and SessionLibrary.Components, and exports
  records.ml's functions under their own names.  Importing this module is
  `needs "Library/records.ml"`; its `needs "Library/components.ml"`
  (records.ml 7) is the import of SessionLibrary.Components.
-/

import Session
import HolLibrary.Records
import SessionLibrary.Components

open HolCore HolCore.Kernel
open Session SessionLibrary.Components

namespace SessionLibrary.Records

/-- `the_record_types` (records.ml 31-32). -/
initialize the_record_types : IO.Ref HolLibrary.Records.RecordTypes ← IO.mkRef []

/-- What records.ml uses from Session and components.ml. -/
def deps : HolLibrary.Records.RecordsDeps where
  define_type_raw d := HolMath.IndTypes.define_type_raw3 Session.raw3Ctx d
  prove_recursive_functions_exist ax t :=
    ExceptT.mk (Session.prove_recursive_functions_exist ax t)
  new_specification ns th := ExceptT.mk (Session.new_specification ns th)
  MESON_TAC := MESON_TAC
  the_record_types := the_record_types
  add_component_read_write_thms := add_component_read_write_thms
  add_valid_component_thms := add_valid_component_thms
  add_weakly_valid_component_thms := add_weakly_valid_component_thms
  add_strongly_valid_component_thms := add_strongly_valid_component_thms
  add_extensionally_valid_component_thms := add_extensionally_valid_component_thms
  add_component_orthogonality_thms := add_component_orthogonality_thms
  C := components

/-- `define_record_type`, as built by records.ml's load.  A function, so it
    is kept in a one-field structure: an `initialize` of function type is
    never run in compiled code (see `WfQqconvBox`, SessionMath/Wf.lean). -/
structure DefineRecordTypeBox where
  run : String → ExceptT String IO (thm × thm × thm)

instance : Inhabited DefineRecordTypeBox := ⟨⟨fun _ => throw "define_record_type"⟩⟩

/-- records.ml's load: `tweak` (records.ml 35-37), run when this module is
    loaded. -/
initialize defineRecordTypeBox : DefineRecordTypeBox ← do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly (HolLibrary.Records.setupRecords deps).run with
  | .ok f => pure ⟨f⟩
  | .error e => throw (IO.userError s!"setupRecords failed: {e}")

/-- `needs "Library/records.ml"`: already done by importing this module. -/
def ensureRecords : IO Unit := pure ()

/-- `parse_record_specification s` (records.ml 9). -/
def parse_record_specification (s : String) :
    IO (Except String (String × List (String × hol_type))) :=
  (HolLibrary.Records.parse_record_specification s).run

/-- `define_record_type s` (records.ml 34). -/
def define_record_type (s : String) : IO (Except String (thm × thm × thm)) :=
  (defineRecordTypeBox.run s).run

/-- `get_record_components cth` (records.ml 80). -/
def get_record_components (cth : thm) : Except String (List term) :=
  HolLibrary.Records.get_record_components cth

/-- `record_read_write_thms (ith,cth)` (records.ml 90). -/
def record_read_write_thms (p : thm × thm) : IO (Except String (List thm)) :=
  (HolLibrary.Records.record_read_write_thms p.1 p.2).run

/-- `record_strongly_valid_component_thms (ith,cth)` (records.ml 103). -/
def record_strongly_valid_component_thms (p : thm × thm) :
    IO (Except String (List thm)) :=
  (HolLibrary.Records.record_strongly_valid_component_thms components p.1 p.2).run

/-- `record_valid_component_thms (ith,cth)` (records.ml 112). -/
def record_valid_component_thms (p : thm × thm) : IO (Except String (List thm)) :=
  (HolLibrary.Records.record_valid_component_thms components p.1 p.2).run

/-- `record_extensionally_valid_component_thms (ith,cth)` (records.ml 116). -/
def record_extensionally_valid_component_thms (p : thm × thm) :
    IO (Except String (List thm)) :=
  (HolLibrary.Records.record_extensionally_valid_component_thms components p.1 p.2).run

/-- `record_weakly_valid_component_thms (ith,cth)` (records.ml 120). -/
def record_weakly_valid_component_thms (p : thm × thm) :
    IO (Except String (List thm)) :=
  (HolLibrary.Records.record_weakly_valid_component_thms components p.1 p.2).run

/-- `record_orthogonality_thms (ith,cth)` (records.ml 128). -/
def record_orthogonality_thms (p : thm × thm) : IO (Except String (List thm)) :=
  (HolLibrary.Records.record_orthogonality_thms components p.1 p.2).run

/-- `define_auto_record_type def` (records.ml 144). -/
def define_auto_record_type (s : String) : IO (Except String (thm × thm × thm)) :=
  (HolLibrary.Records.define_auto_record_type deps defineRecordTypeBox.run s).run

end SessionLibrary.Records
