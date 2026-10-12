/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/components.ml.                              -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Components.lean

  The `unsafe` half of the components.ml translation (as
  SessionLibrary/Floor.lean is for floor.ml): it holds the theorem lists of
  components.ml 17-50, supplies HolLibrary.Components' dependencies from
  Session, builds the bundle on first use, and exports every theorem by
  name.  `ensureComponents` is `needs "Library/components.ml"`.
-/

import Session
import HolLibrary.Components

open HolCore HolCore.Kernel
open Session

namespace SessionLibrary.Components

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨sessionB, sessionC, sessionT⟩

/- ------------------------------------------------------------------------- -/
/- Storing useful per-case theorems not true of a general component.         -/
/- (components.ml 17-50)                                                     -/
/- ------------------------------------------------------------------------- -/

initialize component_read_write_thms : IO.Ref (List thm) ← IO.mkRef []

def add_component_read_write_thms (l : List thm) : IO Unit := do
  component_read_write_thms.set (HolCore.Lib.union l (← component_read_write_thms.get))

initialize component_alias_thms : IO.Ref (List thm) ← IO.mkRef []

initialize valid_component_thms : IO.Ref (List thm) ← IO.mkRef []

def add_valid_component_thms (l : List thm) : IO Unit := do
  valid_component_thms.set (HolCore.Lib.union l (← valid_component_thms.get))

initialize strongly_valid_component_thms : IO.Ref (List thm) ← IO.mkRef []

def add_strongly_valid_component_thms (l : List thm) : IO Unit := do
  strongly_valid_component_thms.set
    (HolCore.Lib.union l (← strongly_valid_component_thms.get))

initialize weakly_valid_component_thms : IO.Ref (List thm) ← IO.mkRef []

def add_weakly_valid_component_thms (l : List thm) : IO Unit := do
  weakly_valid_component_thms.set
    (HolCore.Lib.union l (← weakly_valid_component_thms.get))

initialize extensionally_valid_component_thms : IO.Ref (List thm) ← IO.mkRef []

def add_extensionally_valid_component_thms (l : List thm) : IO Unit := do
  extensionally_valid_component_thms.set
    (HolCore.Lib.union l (← extensionally_valid_component_thms.get))

initialize component_orthogonality_thms : IO.Ref (List thm) ← IO.mkRef []

def add_component_orthogonality_thms (l : List thm) : IO Unit := do
  component_orthogonality_thms.set
    (HolCore.Lib.union l (← component_orthogonality_thms.get))

/- ------------------------------------------------------------------------- -/
/- The bundle.                                                               -/
/- ------------------------------------------------------------------------- -/

/-- What components.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Components.ComponentsDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  new_type_definition ty names th :=
    ExceptT.mk (Session.new_type_definition ty names.1 names.2 th)
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  parse_as_infix := Session.parse_as_infix
  add_component_read_write_thms := add_component_read_write_thms
  add_valid_component_thms := add_valid_component_thms
  add_weakly_valid_component_thms := add_weakly_valid_component_thms
  add_strongly_valid_component_thms := add_strongly_valid_component_thms
  add_extensionally_valid_component_thms := add_extensionally_valid_component_thms
  MESON_TAC := MESON_TAC
  FUN_EQ_THM := Session.FUN_EQ_THM
  I_DEF := Session.I_DEF
  I_THM := Session.I_THM
  PAIR := Session.PAIR
  PAIR_EQ := Session.PAIR_EQ
  o_DEF := Session.o_DEF

initialize theComponents : IO.Ref (Option HolLibrary.Components.Components) ← IO.mkRef none

/-- components.ml runs after the whole of hol.ml (it has no `needs` and no
    `prioritize_...` call of its own), so the library is loaded first. -/
private unsafe def BComponents : HolLibrary.Components.Components :=
  match unsafeIO (do
    match ← theComponents.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      match ← (HolLibrary.Components.setupComponents (deps ())).run with
      | .ok d => do theComponents.set (some d); pure d
      | .error e => panic! s!"setupComponents failed: {e}") with
  | .ok d => d | _ => panic! "SessionLibrary.Components: setupComponents"

/-- The whole components.ml bundle, for records.ml. -/
unsafe def components : HolLibrary.Components.Components := BComponents

/- The theorems, by name. -/
unsafe def component_tybij              : thm := BComponents.component_tybij
unsafe def COMPONENT_INJ                : thm := BComponents.COMPONENT_INJ
unsafe def FORALL_COMPONENT             : thm := BComponents.FORALL_COMPONENT
unsafe def EXISTS_COMPONENT             : thm := BComponents.EXISTS_COMPONENT
unsafe def read_def                     : thm := BComponents.read_def
unsafe def write_def                    : thm := BComponents.write_def
unsafe def read                         : thm := BComponents.read
unsafe def write                        : thm := BComponents.write
unsafe def COMPONENT_EQ                 : thm := BComponents.COMPONENT_EQ
unsafe def entirety                     : thm := BComponents.entirety
unsafe def READ_ENTIRETY                : thm := BComponents.READ_ENTIRETY
unsafe def WRITE_ENTIRETY               : thm := BComponents.WRITE_ENTIRETY
unsafe def READ_WRITE_ENTIRETY          : thm := BComponents.READ_WRITE_ENTIRETY
unsafe def component_compose            : thm := BComponents.component_compose
unsafe def COMPONENT_COMPOSE_ASSOC      : thm := BComponents.COMPONENT_COMPOSE_ASSOC
unsafe def READ_COMPONENT_COMPOSE       : thm := BComponents.READ_COMPONENT_COMPOSE
unsafe def WRITE_COMPONENT_COMPOSE      : thm := BComponents.WRITE_COMPONENT_COMPOSE
unsafe def COMPOSE_ENTIRETY             : thm := BComponents.COMPOSE_ENTIRETY
unsafe def READ_WRITE_COMPONENT_COMPOSE : thm := BComponents.READ_WRITE_COMPONENT_COMPOSE
unsafe def read_over_write              : thm := BComponents.read_over_write
unsafe def write_over_write             : thm := BComponents.write_over_write
unsafe def write_over_read              : thm := BComponents.write_over_read
unsafe def weak_read_over_write         : thm := BComponents.weak_read_over_write
unsafe def valid_component              : thm := BComponents.valid_component
unsafe def VALID_COMPONENT_COMPOSE      : thm := BComponents.VALID_COMPONENT_COMPOSE
unsafe def VALID_COMPONENT_ENTIRETY     : thm := BComponents.VALID_COMPONENT_ENTIRETY
unsafe def weakly_valid_component       : thm := BComponents.weakly_valid_component
unsafe def VALID_IMP_WEAKLY_VALID_COMPONENT : thm := BComponents.VALID_IMP_WEAKLY_VALID_COMPONENT
unsafe def WEAKLY_VALID_COMPONENT_ENTIRETY : thm := BComponents.WEAKLY_VALID_COMPONENT_ENTIRETY
unsafe def strongly_valid_component     : thm := BComponents.strongly_valid_component
unsafe def STRONGLY_VALID_IMP_VALID_COMPONENT : thm := BComponents.STRONGLY_VALID_IMP_VALID_COMPONENT
unsafe def STRONGLY_VALID_COMPONENT_COMPOSE : thm := BComponents.STRONGLY_VALID_COMPONENT_COMPOSE
unsafe def STRONGLY_VALID_COMPONENT_ENTIRETY : thm := BComponents.STRONGLY_VALID_COMPONENT_ENTIRETY
unsafe def extensionally_valid_component : thm := BComponents.extensionally_valid_component
unsafe def STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT : thm := BComponents.STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT
unsafe def EXTENSIONALLY_VALID_COMPONENT_ENTIRETY : thm := BComponents.EXTENSIONALLY_VALID_COMPONENT_ENTIRETY
unsafe def orthogonal_components        : thm := BComponents.orthogonal_components
unsafe def ORTHOGONAL_COMPONENTS_SYM    : thm := BComponents.ORTHOGONAL_COMPONENTS_SYM

/-- `needs "Library/components.ml"`. -/
unsafe def ensureComponents : IO Unit := do
  let _ ← IO.mkRef (concl BComponents.component_tybij)
  pure ()

end SessionLibrary.Components
