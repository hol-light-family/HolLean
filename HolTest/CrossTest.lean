/- File: HolTest/CrossTest.lean
Runtime test suite: Multivariate/cross.ml
(HolMultiLib/Cross.lean, wired by SessionMultiLib/Cross.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/cross.ml"`, then `string_of_thm`).  The whole file
is also compared with HOL Light by tools/crossdiff: all 41 theorems
structurally and by their printed forms.

The theorem checks cover the definition, the algebraic laws, the Lagrange and
triple-product identities, the determinant forms, the matrix and orthogonal
transformation results and continuity.  The procedure check runs VEC3_RULE
on a term whose result HOL Light printed.

Loading cross.ml (`ensureCross`) builds every bundle in file order; a
proof that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Cross

open HolCore.Kernel SessionMultiLib.Cross
open HolTest.CommonTest HolLight.Syntax

#eval ensureCross

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/-- Run a rule or conversion on a parsed term and check the printed theorem. -/
private unsafe def procCheck (lbl : String) (f : term → IO (Except String thm)) (s : String)
    (expected : String) : IO Unit := do
  match ← HolCore.Parser.parse_term s with
  | .error e => IO.println s!"{lbl} -> MISMATCH parse: {e}"
  | .ok tm =>
    match ← f tm with
    | .error e => IO.println s!"{lbl} -> MISMATCH failed: {e}"
    | .ok th => thmCheck lbl th expected

/- ---------------------------------------------------------------------- -/
/- Theorem statements (cross.ml), as HOL Light prints them.             -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "cross.ml cross" cross
  "|- forall a b. a cross b = vector [a$2 * b$3 - a$3 * b$2; a$3 * b$1 - a$1 * b$3; a$1 * b$2 - a$2 * b$1]"
#eval thmCheck "cross.ml CROSS_LZERO" CROSS_LZERO "|- forall x. vec 0 cross x = vec 0"
#eval thmCheck "cross.ml CROSS_SKEW" CROSS_SKEW "|- forall x y. x cross y = --(y cross x)"
#eval thmCheck "cross.ml CROSS_LMUL" CROSS_LMUL "|- forall c x y. c % x cross y = c % (x cross y)"
#eval thmCheck "cross.ml CROSS_JACOBI" CROSS_JACOBI
  "|- forall x y z. x cross y cross z + y cross z cross x + z cross x cross y = vec 0"
#eval thmCheck "cross.ml CROSS_LAGRANGE" CROSS_LAGRANGE
  "|- forall x y z. x cross y cross z = (x dot z) % y - (x dot y) % z"
#eval thmCheck "cross.ml CROSS_TRIPLE" CROSS_TRIPLE
  "|- forall x y z. (x cross y) dot z = (y cross z) dot x"
#eval thmCheck "cross.ml NORM_CROSS_DOT" NORM_CROSS_DOT
  "|- forall x y. norm (x cross y) pow 2 + (x dot y) pow 2 = (norm x * norm y) pow 2"
#eval thmCheck "cross.ml DOT_CROSS_DET" DOT_CROSS_DET
  "|- forall x y z. x dot (y cross z) = det (vector [x; y; z])"
#eval thmCheck "cross.ml CROSS_EQ_0" CROSS_EQ_0
  "|- forall x y. x cross y = vec 0 <=> collinear {vec 0, x, y}"
#eval thmCheck "cross.ml CROSS_0" CROSS_0
  "|- (forall x. vec 0 cross x = vec 0) /\\ (forall x. x cross vec 0 = vec 0)"
#eval thmCheck "cross.ml NORM_AND_CROSS_EQ_0" NORM_AND_CROSS_EQ_0
  "|- forall x y. x dot y = &0 /\\ x cross y = vec 0 <=> x = vec 0 \\/ y = vec 0"
#eval thmCheck "cross.ml BILINEAR_CROSS" BILINEAR_CROSS "|- bilinear (cross)"
#eval thmCheck "cross.ml CROSS_MATRIX_MUL" CROSS_MATRIX_MUL
  "|- forall A x y. transp A ** ((A ** x) cross (A ** y)) = det A % (x cross y)"
#eval thmCheck "cross.ml CROSS_ROTATION_MATRIX" CROSS_ROTATION_MATRIX
  "|- forall A x y. rotation_matrix A ==> (A ** x) cross (A ** y) = A ** (x cross y)"
#eval thmCheck "cross.ml CROSS_LINEAR_IMAGE" CROSS_LINEAR_IMAGE
  "|- forall f x y. linear f /\\ (forall x. norm (f x) = norm x) /\\ det (matrix f) = &1 ==> f x cross f y = f (x cross y)"
#eval thmCheck "cross.ml CONTINUOUS_CROSS" CONTINUOUS_CROSS
  "|- forall net f g. f continuous net /\\ g continuous net ==> (\\x. f x cross g x) continuous net"
#eval thmCheck "cross.ml CONTINUOUS_ON_CROSS" CONTINUOUS_ON_CROSS
  "|- forall f g s. f continuous_on s /\\ g continuous_on s ==> (\\x. f x cross g x) continuous_on s"

/- ---------------------------------------------------------------------- -/
/- The procedure, on a term HOL Light ran it on.                          -/
/- ---------------------------------------------------------------------- -/
#eval procCheck "cross.ml VEC3_RULE" VEC3_RULE
  "!x y:real^3. x cross y = --(y cross x)"
  "|- forall x y. x cross y = --(y cross x)"
