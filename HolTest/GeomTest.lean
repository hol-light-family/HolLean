/- File: HolTest/GeomTest.lean
Runtime test suite: Multivariate/geom.ml
(HolMultiLib/Geom.lean, wired by SessionMultiLib/Geom.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/geom.ml"`, then `string_of_thm`).  The whole file is also
compared with HOL Light by tools/geomdiff: all exported theorems structurally
and by their printed forms.  The 20 theorems here are spread evenly over the
file; theorems that print with `?nnn` invented type variables are left out.

Loading geom.ml (`ensureGeom`) builds every bundle in file order; a proof
that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Geom

open HolCore.Kernel Session SessionMultiLib.Geom
open HolTest.CommonTest HolLight.Syntax

#eval ensureGeom

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

#eval thmCheck "geom.ml PYTHAGORAS" PYTHAGORAS
  "|- forall A B C.        orthogonal (A - B) (C - B)        ==> norm (C - A) pow 2 = norm (B - A) pow 2 + norm (C - B) pow 2"
#eval thmCheck "geom.ml VECTOR_ANGLE_RMUL" VECTOR_ANGLE_RMUL
  "|- forall a x y.        vector_angle x (a % y) =        (if a = &0         then pi / &2         else if &0 <= a then vector_angle x y else pi - vector_angle x y)"
#eval thmCheck "geom.ml VECTOR_ANGLE" VECTOR_ANGLE
  "|- forall x y. x dot y = norm x * norm y * cos (vector_angle x y)"
#eval thmCheck "geom.ml VECTOR_ANGLE_EQ_0" VECTOR_ANGLE_EQ_0
  "|- forall x y.        vector_angle x y = &0 <=>        ~(x = vec 0) /\\ ~(y = vec 0) /\\ norm x % y = norm y % x"
#eval thmCheck "geom.ml VECTOR_ANGLE_EQ_PI_DIST" VECTOR_ANGLE_EQ_PI_DIST
  "|- forall x y.        vector_angle x y = pi <=>        ~(x = vec 0) /\\ ~(y = vec 0) /\\ norm (x - y) = norm x + norm y"
#eval thmCheck "geom.ml CONTINUOUS_AT_CX_VECTOR_ANGLE" CONTINUOUS_AT_CX_VECTOR_ANGLE
  "|- forall c x. ~(x = vec 0) ==> Cx o vector_angle c continuous at x"
#eval thmCheck "geom.ml REAL_CONTINUOUS_WITHIN_VECTOR_ANGLE" REAL_CONTINUOUS_WITHIN_VECTOR_ANGLE
  "|- forall c s x.        ~(x = vec 0) ==> vector_angle c real_continuous at x within s"
#eval thmCheck "geom.ml VECTOR_ANGLE_EQ_PI_RIGHT" VECTOR_ANGLE_EQ_PI_RIGHT
  "|- forall x y z.        vector_angle x y = pi ==> vector_angle x z = pi - vector_angle y z"
#eval thmCheck "geom.ml SIN_VECTOR_ANGLE" SIN_VECTOR_ANGLE
  "|- forall x y.        sin (vector_angle x y) =        (if x = vec 0 \\/ y = vec 0         then &1         else sqrt (&1 - ((x dot y) / (norm x * norm y)) pow 2))"
#eval thmCheck "geom.ml VECTOR_ANGLE_1" VECTOR_ANGLE_1
  "|- forall x. vector_angle x (Cx (&1)) = acs (Re x / norm x)"
#eval thmCheck "geom.ml VECTOR_ANGLE_PRESERVING_EQ_SIMILARITY" VECTOR_ANGLE_PRESERVING_EQ_SIMILARITY
  "|- forall f.        linear f /\\ (forall x y. vector_angle (f x) (f y) = vector_angle x y) <=>        (exists c g.             ~(c = &0) /\\ orthogonal_transformation g /\\ f = (\\z. c % g z))"
#eval thmCheck "geom.ml COS_ADJACENT_HYPOTENUSE" COS_ADJACENT_HYPOTENUSE
  "|- forall A B C.        orthogonal (A - B) (C - B)        ==> dist (A,C) * cos (angle (B,A,C)) = dist (A,B)"
#eval thmCheck "geom.ml SIN_OPPOSITE_OVER_HYPOTENUSE" SIN_OPPOSITE_OVER_HYPOTENUSE
  "|- forall A B C.        orthogonal (A - B) (C - B) /\\ ~(A = C)        ==> sin (angle (B,A,C)) = dist (C,B) / dist (A,C)"
#eval thmCheck "geom.ml LAW_OF_COSINES" LAW_OF_COSINES
  "|- forall A B C.        dist (B,C) pow 2 =        (dist (A,B) pow 2 + dist (A,C) pow 2) -        &2 * dist (A,B) * dist (A,C) * cos (angle (B,A,C))"
#eval thmCheck "geom.ml COS_MINUS1_LEMMA" COS_MINUS1_LEMMA
  "|- forall x. cos x = -- &1 /\\ &0 <= x /\\ x < &3 * pi ==> x = pi"
#eval thmCheck "geom.ml ANGLE_EQ_0_DIST" ANGLE_EQ_0_DIST
  "|- forall A B C.        angle (A,B,C) = &0 <=>        ~(A = B) /\\        ~(C = B) /\\        (dist (A,B) = dist (A,C) + dist (C,B) \\/         dist (B,C) = dist (A,C) + dist (A,B))"
#eval thmCheck "geom.ml CONGRUENT_TRIANGLES_SAS" CONGRUENT_TRIANGLES_SAS
  "|- forall A B C A' B' C'.        dist (A,B) = dist (A',B') /\\        angle (A,B,C) = angle (A',B',C') /\\        dist (B,C) = dist (B',C')        ==> dist (A,C) = dist (A',C')"
#eval thmCheck "geom.ml CONGRUENT_TRIANGLES_SSS_FULL" CONGRUENT_TRIANGLES_SSS_FULL
  "|- forall A B C A' B' C'.        dist (A,B) = dist (A',B') /\\        dist (B,C) = dist (B',C') /\\        dist (C,A) = dist (C',A')        ==> dist (A,B) = dist (A',B') /\\            dist (B,C) = dist (B',C') /\\            dist (C,A) = dist (C',A') /\\            angle (A,B,C) = angle (A',B',C') /\\            angle (B,C,A) = angle (B',C',A') /\\            angle (C,A,B) = angle (C',A',B')"
#eval thmCheck "geom.ml CONGRUENT_TRIANGLES_ASA_FULL" CONGRUENT_TRIANGLES_ASA_FULL
  "|- forall A B C A' B' C'.        angle (A,B,C) = angle (A',B',C') /\\        dist (A,B) = dist (A',B') /\\        angle (B,A,C) = angle (B',A',C') /\\        ~collinear {A, B, C}        ==> dist (A,B) = dist (A',B') /\\            dist (B,C) = dist (B',C') /\\            dist (C,A) = dist (C',A') /\\            angle (A,B,C) = angle (A',B',C') /\\            angle (B,C,A) = angle (B',C',A') /\\            angle (C,A,B) = angle (C',A',B')"
#eval thmCheck "geom.ml SETDIST_POINT_LINE" SETDIST_POINT_LINE
  "|- forall x y z.        setdist ({x},affine hull {y, z}) = dist (x,y) * sin (angle (x,y,z))"
