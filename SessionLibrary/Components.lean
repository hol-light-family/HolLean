/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/components.ml.                              -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Components.lean

  The session half of the components.ml translation: it holds the theorem
  lists of components.ml 17-50, supplies HolLibrary.Components' dependencies
  from Session, and exports every theorem by name.  Importing this module is
  `needs "Library/components.ml"`: the bundle is built by `initialize` when
  the module is loaded, after the whole of Session (components.ml has no
  `needs` and no `prioritize_...` call of its own).
-/

import Session
import HolLibrary.Components

open HolCore HolCore.Kernel
open Session

namespace SessionLibrary.Components

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
def deps : HolLibrary.Components.ComponentsDeps where
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

/-- components.ml, run when this module is loaded. -/
initialize BComponents : HolLibrary.Components.Components ← do
  match ← (HolLibrary.Components.setupComponents deps).run with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"setupComponents failed: {e}")

/-- The whole components.ml bundle, for records.ml. -/
def components : HolLibrary.Components.Components := BComponents

/- The theorems, by name. -/
def component_tybij              : thm := BComponents.component_tybij
def COMPONENT_INJ                : thm := BComponents.COMPONENT_INJ
def FORALL_COMPONENT             : thm := BComponents.FORALL_COMPONENT
def EXISTS_COMPONENT             : thm := BComponents.EXISTS_COMPONENT
def read_def                     : thm := BComponents.read_def
def write_def                    : thm := BComponents.write_def
def read                         : thm := BComponents.read
def write                        : thm := BComponents.write
def COMPONENT_EQ                 : thm := BComponents.COMPONENT_EQ
def entirety                     : thm := BComponents.entirety
def READ_ENTIRETY                : thm := BComponents.READ_ENTIRETY
def WRITE_ENTIRETY               : thm := BComponents.WRITE_ENTIRETY
def READ_WRITE_ENTIRETY          : thm := BComponents.READ_WRITE_ENTIRETY
def component_compose            : thm := BComponents.component_compose
def COMPONENT_COMPOSE_ASSOC      : thm := BComponents.COMPONENT_COMPOSE_ASSOC
def READ_COMPONENT_COMPOSE       : thm := BComponents.READ_COMPONENT_COMPOSE
def WRITE_COMPONENT_COMPOSE      : thm := BComponents.WRITE_COMPONENT_COMPOSE
def COMPOSE_ENTIRETY             : thm := BComponents.COMPOSE_ENTIRETY
def READ_WRITE_COMPONENT_COMPOSE : thm := BComponents.READ_WRITE_COMPONENT_COMPOSE
def read_over_write              : thm := BComponents.read_over_write
def write_over_write             : thm := BComponents.write_over_write
def write_over_read              : thm := BComponents.write_over_read
def weak_read_over_write         : thm := BComponents.weak_read_over_write
def valid_component              : thm := BComponents.valid_component
def VALID_COMPONENT_COMPOSE      : thm := BComponents.VALID_COMPONENT_COMPOSE
def VALID_COMPONENT_ENTIRETY     : thm := BComponents.VALID_COMPONENT_ENTIRETY
def weakly_valid_component       : thm := BComponents.weakly_valid_component
def VALID_IMP_WEAKLY_VALID_COMPONENT : thm := BComponents.VALID_IMP_WEAKLY_VALID_COMPONENT
def WEAKLY_VALID_COMPONENT_ENTIRETY : thm := BComponents.WEAKLY_VALID_COMPONENT_ENTIRETY
def strongly_valid_component     : thm := BComponents.strongly_valid_component
def STRONGLY_VALID_IMP_VALID_COMPONENT : thm := BComponents.STRONGLY_VALID_IMP_VALID_COMPONENT
def STRONGLY_VALID_COMPONENT_COMPOSE : thm := BComponents.STRONGLY_VALID_COMPONENT_COMPOSE
def STRONGLY_VALID_COMPONENT_ENTIRETY : thm := BComponents.STRONGLY_VALID_COMPONENT_ENTIRETY
def extensionally_valid_component : thm := BComponents.extensionally_valid_component
def STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT : thm := BComponents.STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT
def EXTENSIONALLY_VALID_COMPONENT_ENTIRETY : thm := BComponents.EXTENSIONALLY_VALID_COMPONENT_ENTIRETY
def orthogonal_components        : thm := BComponents.orthogonal_components
def ORTHOGONAL_COMPONENTS_SYM    : thm := BComponents.ORTHOGONAL_COMPONENTS_SYM

/-- `needs "Library/components.ml"`: already done by importing this module. -/
def ensureComponents : IO Unit := pure ()

end SessionLibrary.Components
