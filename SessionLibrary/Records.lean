/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/records.ml.                                 -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Records.lean

  The `unsafe` half of the records.ml translation: it holds
  `the_record_types` (records.ml 31), supplies HolLibrary.Records'
  dependencies from Session and SessionLibrary.Components, and exports
  records.ml's functions under their own names.  `ensureRecords` is
  `needs "Library/records.ml"`, which first does `needs
  "Library/components.ml"` (records.ml 7).
-/

import Session
import HolLibrary.Records
import SessionLibrary.Components

open HolCore HolCore.Kernel
open Session SessionLibrary.Components

namespace SessionLibrary.Records

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨sessionB, sessionC, sessionT⟩

/-- `the_record_types` (records.ml 31-32). -/
initialize the_record_types : IO.Ref HolLibrary.Records.RecordTypes ← IO.mkRef []

/-- What records.ml uses from Session and components.ml. -/
unsafe def deps (_ : Unit) : HolLibrary.Records.RecordsDeps where
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

initialize theDefineRecordType :
    IO.Ref (Option (String → ExceptT String IO (thm × thm × thm))) ← IO.mkRef none

/-- records.ml's load: `needs "Library/components.ml"`, then `tweak`
    (records.ml 35-37), once.  (An explicit IO step: a cached value of
    function type would be evaluated afresh at each call, not at `needs`.) -/
unsafe def getDefineRecordType : IO (String → ExceptT String IO (thm × thm × thm)) := do
  match ← theDefineRecordType.get with
  | some f => pure f
  | none => do
    ensureComponents
    match ← (HolLibrary.Records.setupRecords (deps ())).run with
    | .ok f => do theDefineRecordType.set (some f); pure f
    | .error e => panic! s!"setupRecords failed: {e}"

/-- `needs "Library/records.ml"`. -/
unsafe def ensureRecords : IO Unit := do
  let _ ← getDefineRecordType
  pure ()

/-- `parse_record_specification s` (records.ml 9). -/
def parse_record_specification (s : String) :
    IO (Except String (String × List (String × hol_type))) :=
  (HolLibrary.Records.parse_record_specification s).run

/-- `define_record_type s` (records.ml 34). -/
unsafe def define_record_type (s : String) : IO (Except String (thm × thm × thm)) := do
  ((← getDefineRecordType) s).run

/-- `get_record_components cth` (records.ml 80). -/
def get_record_components (cth : thm) : Except String (List term) :=
  HolLibrary.Records.get_record_components cth

/-- `record_read_write_thms (ith,cth)` (records.ml 90). -/
unsafe def record_read_write_thms (p : thm × thm) : IO (Except String (List thm)) :=
  (HolLibrary.Records.record_read_write_thms p.1 p.2).run

/-- `record_strongly_valid_component_thms (ith,cth)` (records.ml 103). -/
unsafe def record_strongly_valid_component_thms (p : thm × thm) :
    IO (Except String (List thm)) :=
  (HolLibrary.Records.record_strongly_valid_component_thms components p.1 p.2).run

/-- `record_valid_component_thms (ith,cth)` (records.ml 112). -/
unsafe def record_valid_component_thms (p : thm × thm) : IO (Except String (List thm)) :=
  (HolLibrary.Records.record_valid_component_thms components p.1 p.2).run

/-- `record_extensionally_valid_component_thms (ith,cth)` (records.ml 116). -/
unsafe def record_extensionally_valid_component_thms (p : thm × thm) :
    IO (Except String (List thm)) :=
  (HolLibrary.Records.record_extensionally_valid_component_thms components p.1 p.2).run

/-- `record_weakly_valid_component_thms (ith,cth)` (records.ml 120). -/
unsafe def record_weakly_valid_component_thms (p : thm × thm) :
    IO (Except String (List thm)) :=
  (HolLibrary.Records.record_weakly_valid_component_thms components p.1 p.2).run

/-- `record_orthogonality_thms (ith,cth)` (records.ml 128). -/
unsafe def record_orthogonality_thms (p : thm × thm) : IO (Except String (List thm)) :=
  (HolLibrary.Records.record_orthogonality_thms components p.1 p.2).run

/-- `define_auto_record_type def` (records.ml 144). -/
unsafe def define_auto_record_type (s : String) : IO (Except String (thm × thm × thm)) := do
  let drt ← getDefineRecordType
  (HolLibrary.Records.define_auto_record_type (deps ()) drt s).run

end SessionLibrary.Records
