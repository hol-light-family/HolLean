/- ---------------------------------------------------------------------- -/
/- Session wiring for Multivariate/wlog.ml.                               -/
/- ---------------------------------------------------------------------- -/
/- File: SessionMultiLib/Wlog.lean

  The session half of the wlog.ml translation: it passes convex.ml's deps,
  four determinants.ml/vectors.ml procedures and the extra theorems to
  HolMultiLib.Wlog, and exports every theorem, rule and tactic by name.
  Importing this module is `needs "Multivariate/wlog.ml"`: its own `needs`
  (determinants.ml and convex.ml) is the import of SessionMultiLib.Convex,
  and the bundle is built by `initialize` when the module is loaded.
-/

import SessionMultiLib.Convex
import HolMultiLib.Wlog

open HolCore HolCore.Kernel

namespace SessionMultiLib.Wlog

open Session SessionMultiLib.Vectors SessionMultiLib.Determinants SessionMultiLib.Convex in
/-- The theorems wlog.ml uses that convex.ml's deps do not carry. -/
def thms : HolMultiLib.Wlog.WlogThms :=
  { AFFINE_HULL_INSERT_SPAN, AFFINE_HULL_LINEAR_IMAGE, COLLINEAR_LINEAR_IMAGE_EQ,
    ORTHOGONAL_TRANSFORMATION_INVERSE, ORTHOGONAL_TRANSFORMATION_SURJECTIVE, ROTATION_EXISTS,
    ROTATION_LOWDIM_HORIZONTAL, LTE_ANTISYM, COLLINEAR_3, DIM_INJECTIVE_LINEAR_IMAGE, DOT_3,
    INDEPENDENT_BOUND_GENERAL, QUANTIFY_SURJECTION_THM, SPAN_BREAKDOWN_EQ, SPAN_LINEAR_IMAGE }

def deps : HolMultiLib.Wlog.WlogDeps where
  cvx := SessionMultiLib.Convex.deps
  EXPAND_QUANTS_CONV := SessionMultiLib.Vectors.EXPAND_QUANTS_CONV
  EXISTS_GENVAR_RULE := SessionMultiLib.Determinants.EXISTS_GENVAR_RULE
  TRANSLATION_INVARIANTS := SessionMultiLib.Determinants.TRANSLATION_INVARIANTS
  LINEAR_INVARIANTS := SessionMultiLib.Determinants.LINEAR_INVARIANTS
  thms := thms

private def ioB {α : Type} (name : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

initialize BWLG : HolMultiLib.Wlog.WLG ←
  ioB "setupWLG" (HolMultiLib.Wlog.setupWLG deps).run

-- WLG (wlog.ml 8-389)
def plane : thm := BWLG.plane
def PLANE_TRANSLATION_EQ : thm := BWLG.PLANE_TRANSLATION_EQ
def PLANE_TRANSLATION : thm := BWLG.PLANE_TRANSLATION
def PLANE_LINEAR_IMAGE_EQ : thm := BWLG.PLANE_LINEAR_IMAGE_EQ
def PLANE_LINEAR_IMAGE : thm := BWLG.PLANE_LINEAR_IMAGE
def ROTATION_PLANE_HORIZONTAL : thm := BWLG.ROTATION_PLANE_HORIZONTAL
def ROTATION_HORIZONTAL_PLANE : thm := BWLG.ROTATION_HORIZONTAL_PLANE
/-- `GEOM_HORIZONTAL_PLANE_RULE tm` (wlog.ml 160). -/
def GEOM_HORIZONTAL_PLANE_RULE (tm : term) : ExceptT String IO thm :=
  BWLG.GEOM_HORIZONTAL_PLANE_RULE tm
/-- `GEOM_HORIZONTAL_PLANE_TAC p` (wlog.ml 220). -/
def GEOM_HORIZONTAL_PLANE_TAC (p : term) : HolCore.Tactics.tactic := fun g =>
  BWLG.GEOM_HORIZONTAL_PLANE_TAC p g
def pad2d3d : thm := BWLG.pad2d3d
def FORALL_PAD2D3D_THM : thm := BWLG.FORALL_PAD2D3D_THM
def QUANTIFY_PAD2D3D_THM : thm := BWLG.QUANTIFY_PAD2D3D_THM
def LINEAR_PAD2D3D : thm := BWLG.LINEAR_PAD2D3D
def INJECTIVE_PAD2D3D : thm := BWLG.INJECTIVE_PAD2D3D
def NORM_PAD2D3D : thm := BWLG.NORM_PAD2D3D
/-- `PAD2D3D_QUANTIFY_CONV` (wlog.ml 284). -/
def PAD2D3D_QUANTIFY_CONV : term → IO (Except String thm) := fun t =>
  BWLG.PAD2D3D_QUANTIFY_CONV t
/-- `PAD2D3D_TAC` (wlog.ml 297). -/
def PAD2D3D_TAC : HolCore.Tactics.tactic := fun g => BWLG.PAD2D3D_TAC g
def ROTATION_HORIZONTAL_LINE : thm := BWLG.ROTATION_HORIZONTAL_LINE
/-- `GEOM_HORIZONTAL_LINE_RULE tm` (wlog.ml 330). -/
def GEOM_HORIZONTAL_LINE_RULE (tm : term) : ExceptT String IO thm :=
  BWLG.GEOM_HORIZONTAL_LINE_RULE tm
/-- `GEOM_HORIZONTAL_LINE_TAC l` (wlog.ml 381). -/
def GEOM_HORIZONTAL_LINE_TAC (l : term) : HolCore.Tactics.tactic := fun g =>
  BWLG.GEOM_HORIZONTAL_LINE_TAC l g

/-- `needs "Multivariate/wlog.ml"`: importing this module has built the
    bundle; this is a no-op kept for symmetry with the other wiring files. -/
def ensureWlog : IO Unit := pure ()

end SessionMultiLib.Wlog
