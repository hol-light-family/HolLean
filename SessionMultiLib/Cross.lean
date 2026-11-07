/- ---------------------------------------------------------------------- -/
/- Session wiring for Multivariate/cross.ml.                              -/
/- ---------------------------------------------------------------------- -/
/- File: SessionMultiLib/Cross.lean

  The session half of the cross.ml translation: it supplies
  HolMultiLib.Cross's dependencies from Session and SessionMultiLib, and
  exports every theorem and procedure by name.  Importing this module is
  `needs "Multivariate/cross.ml"`: its own `needs` is the import of
  SessionMultiLib.Topology, and the bundle is built by `initialize` when the
  module is loaded.
-/

import SessionMultiLib.Topology
import HolMultiLib.Cross

open HolCore HolCore.Kernel

namespace SessionMultiLib.Cross

open Session SessionMultiLib.Vectors SessionMultiLib.Determinants
  SessionMultiLib.Topology in
/-- The theorems cross.ml uses. -/
def thms : HolMultiLib.Cross.CrossThms :=
  { ARITH, CART_EQ, CONJ_ASSOC, DIMINDEX_3, EQ_SYM_EQ, LAMBDA_BETA, MONO_FORALL, REAL_ENTIRE,
    REAL_EQ_SQUARE_ABS, REAL_LE_MUL, REAL_MUL_LZERO, REAL_POW_MUL, REAL_SUB_0, REAL_SUB_RZERO,
    o_DEF, real_abs,
    DOT_EQ_0, DOT_LZERO, DOT_RZERO, FORALL_3, LIFT_CMUL, LIFT_SUB, MATRIX_VECTOR_MUL_ASSOC,
    MATRIX_VECTOR_MUL_LID, MATRIX_VECTOR_MUL_RMUL, MATRIX_WORKS, NORM_CAUCHY_SCHWARZ_EQUAL,
    NORM_EQ_0, NORM_POS_LE, NORM_POW_2, ORTHOGONAL_REFL, SUM_3, VECTOR_3, VECTOR_MUL_COMPONENT,
    VECTOR_MUL_LID, VECTOR_MUL_LNEG, VECTOR_SUB_EQ, basis, bilinear, dot, linear,
    matrix_vector_mul, orthogonal, transp, vec, vector_add, vector_mul, vector_neg, vector_sub,
    DET_3, ORTHOGONAL_TRANSFORMATION, ORTHOGONAL_TRANSFORMATION_LINEAR,
    ORTHOGONAL_TRANSFORMATION_MATRIX, orthogonal_matrix, rotation_matrix, rotoinversion_matrix,
    CONTINUOUS_COMPONENTWISE_LIFT, CONTINUOUS_LIFT_COMPONENT_COMPOSE, CONTINUOUS_MUL,
    CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN, CONTINUOUS_SUB }

def deps : HolMultiLib.Cross.CrossDeps where
  new_definition s := do
    let t ← ExceptT.mk (HolCore.Parser.parse_term s)
    ExceptT.mk (Session.new_definition t)
  parse_as_infix := Session.parse_as_infix
  prioritize_vector := SessionMultiLib.Vectors.prioritize_vector
  add_linear_invariants := SessionMultiLib.Vectors.add_linear_invariants
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  MESON_TAC := Session.MESON_TAC
  REAL_ARITH_TAC := Session.REAL_ARITH_TAC2
  REAL_RING t := ExceptT.mk (Session.REAL_RING t)
  thms := thms

private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

initialize BCRS : HolMultiLib.Cross.CRS ←
  ioB "setupCRS" (HolMultiLib.Cross.setupCRS deps).run

-- CRS (cross.ml 7-279)
def cross : thm := BCRS.cross
/-- `VEC3_TAC` (cross.ml 25). -/
def VEC3_TAC : HolCore.Tactics.tactic := fun g => BCRS.VEC3_TAC g
/-- `VEC3_RULE tm` (cross.ml 31). -/
def VEC3_RULE : term → IO (Except String thm) := fun t => (BCRS.VEC3_RULE t).run
def ORTHOGONAL_CROSS : thm := BCRS.ORTHOGONAL_CROSS
def CROSS_LZERO : thm := BCRS.CROSS_LZERO
def CROSS_RZERO : thm := BCRS.CROSS_RZERO
def CROSS_SKEW : thm := BCRS.CROSS_SKEW
def CROSS_REFL : thm := BCRS.CROSS_REFL
def CROSS_LADD : thm := BCRS.CROSS_LADD
def CROSS_RADD : thm := BCRS.CROSS_RADD
def CROSS_LMUL : thm := BCRS.CROSS_LMUL
def CROSS_RMUL : thm := BCRS.CROSS_RMUL
def CROSS_LNEG : thm := BCRS.CROSS_LNEG
def CROSS_RNEG : thm := BCRS.CROSS_RNEG
def CROSS_LSUB : thm := BCRS.CROSS_LSUB
def CROSS_RSUB : thm := BCRS.CROSS_RSUB
def CROSS_JACOBI : thm := BCRS.CROSS_JACOBI
def CROSS_LAGRANGE : thm := BCRS.CROSS_LAGRANGE
def CROSS_TRIPLE : thm := BCRS.CROSS_TRIPLE
def DOT_CROSS_SELF : thm := BCRS.DOT_CROSS_SELF
def CROSS_COMPONENTS : thm := BCRS.CROSS_COMPONENTS
def CROSS_BASIS : thm := BCRS.CROSS_BASIS
def CROSS_BASIS_NONZERO : thm := BCRS.CROSS_BASIS_NONZERO
def CROSS_DOT_CANCEL : thm := BCRS.CROSS_DOT_CANCEL
def NORM_CROSS_DOT : thm := BCRS.NORM_CROSS_DOT
def DOT_CROSS_DET : thm := BCRS.DOT_CROSS_DET
def CROSS_CROSS_DET : thm := BCRS.CROSS_CROSS_DET
def DOT_CROSS : thm := BCRS.DOT_CROSS
def NORM_CROSS : thm := BCRS.NORM_CROSS
def CROSS_EQ_0 : thm := BCRS.CROSS_EQ_0
def CROSS_0 : thm := BCRS.CROSS_0
def CROSS_EQ_SELF : thm := BCRS.CROSS_EQ_SELF
def NORM_AND_CROSS_EQ_0 : thm := BCRS.NORM_AND_CROSS_EQ_0
def BILINEAR_CROSS : thm := BCRS.BILINEAR_CROSS
def CROSS_MATRIX_MUL : thm := BCRS.CROSS_MATRIX_MUL
def CROSS_ORTHOGONAL_MATRIX : thm := BCRS.CROSS_ORTHOGONAL_MATRIX
def CROSS_ROTATION_MATRIX : thm := BCRS.CROSS_ROTATION_MATRIX
def CROSS_ROTOINVERSION_MATRIX : thm := BCRS.CROSS_ROTOINVERSION_MATRIX
def CROSS_ORTHOGONAL_TRANSFORMATION : thm := BCRS.CROSS_ORTHOGONAL_TRANSFORMATION
def CROSS_LINEAR_IMAGE : thm := BCRS.CROSS_LINEAR_IMAGE
def CONTINUOUS_CROSS : thm := BCRS.CONTINUOUS_CROSS
def CONTINUOUS_ON_CROSS : thm := BCRS.CONTINUOUS_ON_CROSS
def CROSS_LINEAR_IMAGE_WEAK : thm := BCRS.CROSS_LINEAR_IMAGE_WEAK

/-- `needs "Multivariate/cross.ml"`: importing this module has built the
    bundle; this is a no-op kept for symmetry with the other wiring files. -/
def ensureCross : IO Unit := pure ()

end SessionMultiLib.Cross
