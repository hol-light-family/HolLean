/- ---------------------------------------------------------------------- -/
/- Session wiring for Multivariate/complexes.ml.                          -/
/- ---------------------------------------------------------------------- -/
/- File: SessionMultiLib/Complexes.lean

  The session half of the complexes.ml translation: it passes
  HolMultiLib.Complexes the deps and bundles of complex_algebra.ml
  (SessionMultiLib.ComplexAlgebra) and exports every theorem by name.
  Importing this module is `needs "Multivariate/complexes.ml"`: its own
  `needs` are the imports of SessionMultiLib.Convex and
  SessionMultiLib.ComplexAlgebra (in that order), and each bundle is built
  by `initialize` when the module is loaded, in file order.  The theorems of
  complex_algebra.ml are exported by SessionMultiLib.ComplexAlgebra.
-/

import SessionMultiLib.Convex
import SessionMultiLib.ComplexAlgebra
import HolMultiLib.Complexes

open HolCore HolCore.Kernel

namespace SessionMultiLib.Complexes

open SessionMultiLib.ComplexAlgebra (deps BCXA BCXB BCXC BCXD BCXE BCXF BCXG BCXH BCXI BCXJ BCXK)

private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in complexes.ml order. -/

initialize BCXL : HolMultiLib.Complexes.CXL ←
  ioB "setupCXL" (HolMultiLib.Complexes.setupCXL deps BCXA BCXC BCXF BCXG BCXH).run

-- CXL (complexes.ml 18-91)
def ORTHOGONAL_TRANSFORMATION_CNJ : thm := BCXL.ORTHOGONAL_TRANSFORMATION_CNJ
def ORTHOGONAL_TRANSFORMATION_COMPLEX_MUL : thm := BCXL.ORTHOGONAL_TRANSFORMATION_COMPLEX_MUL
def COMPLEX_ORTHOGONAL_ROTATION : thm := BCXL.COMPLEX_ORTHOGONAL_ROTATION
def COMPLEX_ORTHOGONAL_ROTOINVERSION : thm := BCXL.COMPLEX_ORTHOGONAL_ROTOINVERSION
def COMPLEX_ORTHOGONAL_TRANSFORMATION : thm := BCXL.COMPLEX_ORTHOGONAL_TRANSFORMATION

initialize BCXM : HolMultiLib.Complexes.CXM ←
  ioB "setupCXM" (HolMultiLib.Complexes.setupCXM deps BCXA BCXC BCXI).run

-- CXM (complexes.ml 93-164)
def REAL_SEGMENT : thm := BCXM.REAL_SEGMENT
def IN_SEGMENT_CX : thm := BCXM.IN_SEGMENT_CX
def IN_SEGMENT_CX_GEN : thm := BCXM.IN_SEGMENT_CX_GEN
def RE_POS_SEGMENT : thm := BCXM.RE_POS_SEGMENT
def CONVEX_REAL : thm := BCXM.CONVEX_REAL
def INTERIOR_REAL : thm := BCXM.INTERIOR_REAL

initialize BCXN : HolMultiLib.Complexes.CXN ←
  ioB "setupCXN" (HolMultiLib.Complexes.setupCXN deps BCXB BCXF BCXJ).run

-- CXN (complexes.ml 166-204)
def COMPLEX_POLYFUN_EXTREMAL : thm := BCXN.COMPLEX_POLYFUN_EXTREMAL

/-- `needs "Multivariate/complexes.ml"`: importing this module has built
    every bundle; this is a no-op kept for symmetry with the other wiring files. -/
def ensureComplexes : IO Unit := pure ()

end SessionMultiLib.Complexes
