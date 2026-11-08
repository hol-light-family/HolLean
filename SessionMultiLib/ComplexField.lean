/- ---------------------------------------------------------------------- -/
/- Session wiring for Multivariate/complex_field.ml.                      -/
/- ---------------------------------------------------------------------- -/
/- File: SessionMultiLib/ComplexField.lean

  The session half of the complex_field.ml translation.  Importing this
  module is `needs "Multivariate/complex_field.ml"`: its own `needs` are the
  imports of SessionLibrary.FieldTheory, SessionMultiLib.Cauchy and
  SessionMultiLib.ComplexRing (in that order), and the bundle is built by
  `initialize` when the module is loaded.
-/

import SessionLibrary.FieldTheory
import SessionMultiLib.Cauchy
import SessionMultiLib.ComplexRing
import HolMultiLib.ComplexField

open HolCore HolCore.Kernel

namespace SessionMultiLib.ComplexField

/-- The theorems complex_field.ml uses from the core library,
    Library/ringtheory.ml, Library/fieldtheory.ml and Multivariate/cauchy.ml. -/
def cf : HolMultiLib.ComplexField.CfThms where
  IN_NUMSEG := Session.IN_NUMSEG
  IN_UNIV := Session.IN_UNIV
  LE_1 := Session.LE_1
  LE_REFL := Session.LE_REFL
  POLY_DEG_0 := SessionLibrary.RingTheory.POLY_DEG_0
  POLY_TOP_EQ_0 := SessionLibrary.RingTheory.POLY_TOP_EQ_0
  RING_POLYNOMIAL := SessionLibrary.RingTheory.RING_POLYNOMIAL
  algebraically_closed_field := SessionLibrary.FieldTheory.algebraically_closed_field
  FTA := SessionMultiLib.Cauchy.FTA

def deps : HolMultiLib.ComplexField.ComplexFieldDeps where
  crd := SessionMultiLib.ComplexRing.deps
  cf := cf

private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

initialize BCF : HolMultiLib.ComplexField.CF ←
  ioB "setupCF" (HolMultiLib.ComplexField.setupCF deps SessionMultiLib.ComplexRing.BCR).run

-- CF (complex_field.ml 7-21)
def ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING : thm := BCF.ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING

/-- `needs "Multivariate/complex_field.ml"`: importing this module has built
    the bundle; a no-op kept for symmetry with the other wiring files. -/
def ensureComplexField : IO Unit := pure ()

end SessionMultiLib.ComplexField
