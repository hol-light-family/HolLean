/- ---------------------------------------------------------------------- -/
/- Session wiring for Multivariate/wlog_examples.ml.                      -/
/- ---------------------------------------------------------------------- -/
/- File: SessionMultiLib/WlogExamples.lean

  The session half of the wlog_examples.ml translation: it passes convex.ml's
  deps, wlog.ml's bundle and the extra theorems to HolMultiLib.WlogExamples,
  and exports every theorem by name.  Importing this module is
  `needs "Multivariate/wlog_examples.ml"`: its own `needs` is the import of
  SessionMultiLib.Wlog, and each bundle is built by `initialize` when the
  module is loaded, in file order.
-/

import SessionMultiLib.Wlog
import HolMultiLib.WlogExamples

open HolCore HolCore.Kernel

namespace SessionMultiLib.WlogExamples

open Session SessionMultiLib.Vectors SessionMultiLib.Convex in
/-- The theorems wlog_examples.ml uses that convex.ml's deps do not carry. -/
def thms : HolMultiLib.WlogExamples.WexThms :=
  { AFFINE_AFFINE_HULL, AFFINE_DEPENDENT_IMP_COLLINEAR_3, AFFINE_HULL_2, AFFINE_HULL_EQ_SPAN,
    AFFINE_HULL_FINITE, AFFINE_HULL_FINITE_STEP, AFFINE_HULL_FINITE_STEP_GEN,
    COLLINEAR_AFFINE_HULL, CONVEX_HULL_2_ALT, COPLANAR_3, DEPENDENT_AFFINE_DEPENDENT_CASES,
    DEPENDENT_IMP_AFFINE_DEPENDENT, affine, coplanar, GT, ITERATE_EXPAND_CASES, REAL_ADD_RINV,
    REAL_LE_SQUARE, EXISTS_VECTOR_2, FORALL_2, NORM_GT_SQUARE, ORTHOGONAL_LINEAR_IMAGE_EQ,
    SPAN_SPAN, SUBSPACE_SPECIAL_HYPERPLANE, VECTOR_2 }

private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

initialize BWXA : HolMultiLib.WlogExamples.WXA ←
  ioB "setupWXA" (HolMultiLib.WlogExamples.setupWXA SessionMultiLib.Convex.deps
    SessionMultiLib.Wlog.BWLG thms).run

-- WXA (wlog_examples.ml 7-252)
/-- The second `lemma` (wlog_examples.ml 147). -/
def lemma : thm := BWXA.lemma
def TRUONG_1 : thm := BWXA.TRUONG_1
def opposite : thm := BWXA.opposite
def OPPOSITE_TRANSLATION_EQ : thm := BWXA.OPPOSITE_TRANSLATION_EQ
def OPPOSITE_LINEAR_IMAGE_EQ : thm := BWXA.OPPOSITE_LINEAR_IMAGE_EQ
def AFFINE_PLANE : thm := BWXA.AFFINE_PLANE
def TRUONG_OPPOSITE_LEMMA : thm := BWXA.TRUONG_OPPOSITE_LEMMA
def TRUONG_OPPOSITE_THM : thm := BWXA.TRUONG_OPPOSITE_THM

initialize BWXB : HolMultiLib.WlogExamples.WXB ←
  ioB "setupWXB" (HolMultiLib.WlogExamples.setupWXB SessionMultiLib.Convex.deps
    SessionMultiLib.Wlog.BWLG thms).run

-- WXB (wlog_examples.ml 253-744)
def lin_combo : thm := BWXB.lin_combo
def affsign : thm := BWXB.affsign
def sgn_gt : thm := BWXB.sgn_gt
def sgn_ge : thm := BWXB.sgn_ge
def sgn_lt : thm := BWXB.sgn_lt
def sgn_le : thm := BWXB.sgn_le
def aff_gt_def : thm := BWXB.aff_gt_def
def aff_ge_def : thm := BWXB.aff_ge_def
def aff_lt_def : thm := BWXB.aff_lt_def
def aff_le_def : thm := BWXB.aff_le_def
/-- The second `AFFSIGN` (wlog_examples.ml 506). -/
def AFFSIGN : thm := BWXB.AFFSIGN
def AFFSIGN_ALT : thm := BWXB.AFFSIGN_ALT
/-- The second `IN_AFFSIGN` (wlog_examples.ml 513). -/
def IN_AFFSIGN : thm := BWXB.IN_AFFSIGN
def AFFSIGN_INJECTIVE_LINEAR_IMAGE : thm := BWXB.AFFSIGN_INJECTIVE_LINEAR_IMAGE
def AFF_GE_INJECTIVE_LINEAR_IMAGE : thm := BWXB.AFF_GE_INJECTIVE_LINEAR_IMAGE
def AFF_GT_INJECTIVE_LINEAR_IMAGE : thm := BWXB.AFF_GT_INJECTIVE_LINEAR_IMAGE
def AFF_LE_INJECTIVE_LINEAR_IMAGE : thm := BWXB.AFF_LE_INJECTIVE_LINEAR_IMAGE
def AFF_LT_INJECTIVE_LINEAR_IMAGE : thm := BWXB.AFF_LT_INJECTIVE_LINEAR_IMAGE
def IN_AFFSIGN_TRANSLATION : thm := BWXB.IN_AFFSIGN_TRANSLATION
def AFFSIGN_TRANSLATION : thm := BWXB.AFFSIGN_TRANSLATION
def AFF_GE_TRANSLATION : thm := BWXB.AFF_GE_TRANSLATION
def AFF_GT_TRANSLATION : thm := BWXB.AFF_GT_TRANSLATION
def AFF_LE_TRANSLATION : thm := BWXB.AFF_LE_TRANSLATION
def AFF_LT_TRANSLATION : thm := BWXB.AFF_LT_TRANSLATION
def NOT_COPLANAR_NOT_COLLINEAR : thm := BWXB.NOT_COPLANAR_NOT_COLLINEAR
def LEMMA : thm := BWXB.LEMMA
def THEOREM : thm := BWXB.THEOREM

/-- `needs "Multivariate/wlog_examples.ml"`: importing this module has built
    every bundle; this is a no-op kept for symmetry with the other wiring files. -/
def ensureWlogExamples : IO Unit := pure ()

end SessionMultiLib.WlogExamples
