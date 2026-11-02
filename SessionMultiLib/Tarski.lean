/- ---------------------------------------------------------------------- -/
/- Session wiring for Multivariate/tarski.ml.                             -/
/- ---------------------------------------------------------------------- -/
/- File: SessionMultiLib/Tarski.lean

  The session half of the tarski.ml translation: it passes convex.ml's
  deps and the extra theorems to HolMultiLib.Tarski, and exports every
  theorem by name.  Importing this module is `needs "Multivariate/tarski.ml"`:
  its own `needs` is the import of SessionMultiLib.Convex, and the bundle is
  built by `initialize` when the module is loaded.
-/

import SessionMultiLib.Convex
import HolMultiLib.Tarski

open HolCore HolCore.Kernel

namespace SessionMultiLib.Tarski

open Session SessionMultiLib.Vectors SessionMultiLib.Convex in
/-- The theorems tarski.ml uses that convex.ml's deps do not carry. -/
def thms : HolMultiLib.Tarski.TarskiThms :=
  { REAL_EQ_MUL_LCANCEL, REAL_EQ_MUL_RCANCEL, BETWEEN_EXISTS_EXTENSION, BETWEEN_REFL_EQ,
    BETWEEN_TRANSLATION, FORALL_2, between, BETWEEN_LINEAR_IMAGE_EQ,
    RIGID_TRANSFORMATION_BETWEEN_3 }

private def ioB {α : Type} (name : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

initialize BTAR : HolMultiLib.Tarski.TAR ←
  ioB "setupTAR" (HolMultiLib.Tarski.setupTAR SessionMultiLib.Convex.deps thms).run

-- TAR (tarski.ml 12-262)
def TARSKI_AXIOM_1_EUCLIDEAN : thm := BTAR.TARSKI_AXIOM_1_EUCLIDEAN
def TARSKI_AXIOM_2_EUCLIDEAN : thm := BTAR.TARSKI_AXIOM_2_EUCLIDEAN
def TARSKI_AXIOM_3_EUCLIDEAN : thm := BTAR.TARSKI_AXIOM_3_EUCLIDEAN
def TARSKI_AXIOM_4_EUCLIDEAN : thm := BTAR.TARSKI_AXIOM_4_EUCLIDEAN
def TARSKI_AXIOM_5_EUCLIDEAN : thm := BTAR.TARSKI_AXIOM_5_EUCLIDEAN
def TARSKI_AXIOM_6_EUCLIDEAN : thm := BTAR.TARSKI_AXIOM_6_EUCLIDEAN
def TARSKI_AXIOM_7_EUCLIDEAN : thm := BTAR.TARSKI_AXIOM_7_EUCLIDEAN
def TARSKI_AXIOM_8_EUCLIDEAN : thm := BTAR.TARSKI_AXIOM_8_EUCLIDEAN
def TARSKI_AXIOM_9_EUCLIDEAN : thm := BTAR.TARSKI_AXIOM_9_EUCLIDEAN
def TARSKI_AXIOM_10_EUCLIDEAN : thm := BTAR.TARSKI_AXIOM_10_EUCLIDEAN
def TARSKI_AXIOM_11_EUCLIDEAN : thm := BTAR.TARSKI_AXIOM_11_EUCLIDEAN

/-- `needs "Multivariate/tarski.ml"`: importing this module has built the
    bundle; this is a no-op kept for symmetry with the other wiring files. -/
def ensureTarski : IO Unit := pure ()

end SessionMultiLib.Tarski
