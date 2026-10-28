/- File: HolTest/WlogTest.lean
Runtime test suite: Multivariate/wlog.ml
(HolMultiLib/Wlog.lean, wired by SessionMultiLib/Wlog.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/wlog.ml"`, then `string_of_thm`).  The whole file
is also compared with HOL Light by tools/wlogdiff: all 14 theorems
structurally and by their printed forms.

The theorem checks cover the plane invariance theorems, the rotations to a
horizontal plane or line, and the pad2d3d embedding.

Loading wlog.ml (`ensureWlog`) builds every bundle in file order; a
proof that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Wlog

open HolCore.Kernel SessionMultiLib.Wlog
open HolTest.CommonTest HolLight.Syntax

#eval ensureWlog

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- Theorem statements (wlog.ml), as HOL Light prints them.              -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "wlog.ml PLANE_TRANSLATION_EQ" PLANE_TRANSLATION_EQ
  "|- forall a s. plane (IMAGE (\\x. a + x) s) <=> plane s"
#eval thmCheck "wlog.ml PLANE_TRANSLATION" PLANE_TRANSLATION
  "|- forall a s. plane s ==> plane (IMAGE (\\x. a + x) s)"
#eval thmCheck "wlog.ml PLANE_LINEAR_IMAGE_EQ" PLANE_LINEAR_IMAGE_EQ
  "|- forall f p. linear f /\\ (forall x y. f x = f y ==> x = y) ==> (plane (IMAGE f p) <=> plane p)"
#eval thmCheck "wlog.ml PLANE_LINEAR_IMAGE" PLANE_LINEAR_IMAGE
  "|- forall f p. linear f /\\ plane p /\\ (forall x y. f x = f y ==> x = y) ==> plane (IMAGE f p)"
#eval thmCheck "wlog.ml ROTATION_PLANE_HORIZONTAL" ROTATION_PLANE_HORIZONTAL
  "|- forall s. plane s ==> (exists a f. orthogonal_transformation f /\\ det (matrix f) = &1 /\\ IMAGE f (IMAGE (\\x. a + x) s) = {z | z$3 = &0})"
#eval thmCheck "wlog.ml ROTATION_HORIZONTAL_PLANE" ROTATION_HORIZONTAL_PLANE
  "|- forall p. plane p ==> (exists a f. orthogonal_transformation f /\\ det (matrix f) = &1 /\\ IMAGE (\\x. a + x) (IMAGE f {z | z$3 = &0}) = p)"
#eval thmCheck "wlog.ml pad2d3d" pad2d3d
  "|- forall x. pad2d3d x = (lambda i. if i < 3 then x$i else &0)"
#eval thmCheck "wlog.ml FORALL_PAD2D3D_THM" FORALL_PAD2D3D_THM
  "|- forall P. (forall y. y$3 = &0 ==> P y) <=> (forall x. P (pad2d3d x))"
#eval thmCheck "wlog.ml QUANTIFY_PAD2D3D_THM" QUANTIFY_PAD2D3D_THM
  "|- (forall P. (forall y. y$3 = &0 ==> P y) <=> (forall x. P (pad2d3d x))) /\\ (forall P. (exists y. y$3 = &0 /\\ P y) <=> (exists x. P (pad2d3d x)))"
#eval thmCheck "wlog.ml LINEAR_PAD2D3D" LINEAR_PAD2D3D "|- linear pad2d3d"
#eval thmCheck "wlog.ml INJECTIVE_PAD2D3D" INJECTIVE_PAD2D3D
  "|- forall x y. pad2d3d x = pad2d3d y ==> x = y"
#eval thmCheck "wlog.ml NORM_PAD2D3D" NORM_PAD2D3D "|- forall x. norm (pad2d3d x) = norm x"
#eval thmCheck "wlog.ml ROTATION_HORIZONTAL_LINE" ROTATION_HORIZONTAL_LINE
  "|- forall a. exists b f. orthogonal_transformation f /\\ det (matrix f) = &1 /\\ f b = a /\\ (forall k. 1 < k /\\ k <= dimindex (:N) ==> b$k = &0)"
