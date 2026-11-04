/- File: HolTest/FlyspeckTest.lean
Runtime test suite: Multivariate/flyspeck.ml
(HolMultiLib/Flyspeck.lean, wired by SessionMultiLib/Flyspeck.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/flyspeck.ml"`, then `string_of_thm`).  The whole file is also
compared with HOL Light by tools/flyspeckdiff: all exported theorems structurally
and by their printed forms.  The 20 theorems here are spread evenly over the
file; theorems that print with `?nnn` invented type variables are left out.

Loading flyspeck.ml (`ensureFlyspeck`) builds every bundle in file order; a proof
that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Flyspeck

open HolCore.Kernel Session SessionMultiLib.Flyspeck
open HolTest.CommonTest HolLight.Syntax

#eval ensureFlyspeck

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

#eval thmCheck "flyspeck.ml NORM_CROSS_SIN" NORM_CROSS_SIN
  "|- forall x y. norm (x cross y) = norm x * norm y * sin (vector_angle x y)"
#eval thmCheck "flyspeck.ml SLICE_123" SLICE_123
  "|- forall s. slice 3 t s = {y | vector [y$1; y$2; t] IN s}"
#eval thmCheck "flyspeck.ml ROTATION_PLANE_HORIZONTAL" ROTATION_PLANE_HORIZONTAL
  "|- forall s.        plane s        ==> (exists a f.                 orthogonal_transformation f /\\                 det (matrix f) = &1 /\\                 IMAGE f (IMAGE (\\x. a + x) s) = {z | z$3 = &0})"
#eval thmCheck "flyspeck.ml AFF_LT_INJECTIVE_LINEAR_IMAGE" AFF_LT_INJECTIVE_LINEAR_IMAGE
  "|- forall f s t.        linear f /\\ (forall x y. f x = f y ==> x = y)        ==> aff_lt (IMAGE f s) (IMAGE f t) = IMAGE f (aff_lt s t)"
#eval thmCheck "flyspeck.ml AFFINE_HULL_SUBSET_AFFSIGN" AFFINE_HULL_SUBSET_AFFSIGN
  "|- forall sgn s t.        sgn (&0) /\\ DISJOINT s t ==> affine hull s SUBSET affsign sgn s t"
#eval thmCheck "flyspeck.ml AFF_GE_0_CONVEX_CONE_NEGATIONS" AFF_GE_0_CONVEX_CONE_NEGATIONS
  "|- forall s t.        FINITE s /\\ FINITE t /\\ vec 0 IN s DIFF t        ==> aff_ge s t =            convex_cone hull (s UNION t UNION IMAGE (--) (s DIFF t))"
#eval thmCheck "flyspeck.ml CONVEX_HULL_CONV0_DECOMP" CONVEX_HULL_CONV0_DECOMP
  "|- forall s.        FINITE s        ==> convex hull s =            conv0 s UNION UNIONS {convex hull (s DELETE a) | a | a IN s}"
#eval thmCheck "flyspeck.ml ORTHONORMAL_IMP_SPANNING" ORTHONORMAL_IMP_SPANNING
  "|- forall e1 e2 e3. orthonormal e1 e2 e3 ==> span {e1, e2, e3} = (:real^3)"
#eval thmCheck "flyspeck.ml AZIM_SPECIAL_SCALE" AZIM_SPECIAL_SCALE
  "|- forall a v w1 w2.        &0 < a ==> azim (vec 0) (a % v) w1 w2 = azim (vec 0) v w1 w2"
#eval thmCheck "flyspeck.ml AZIM_EQ_0_GE" AZIM_EQ_0_GE
  "|- forall v0 v1 w x.        ~collinear {v0, v1, w} /\\ ~collinear {v0, v1, x}        ==> (azim v0 v1 w x = &0 <=> w IN aff_ge {v0, v1} {x})"
#eval thmCheck "flyspeck.ml COLLINEAR_WITHIN_AFF_GE_COLLINEAR" COLLINEAR_WITHIN_AFF_GE_COLLINEAR
  "|- forall a u v w.        v IN aff_ge {a} {u, w} /\\ collinear {a, u, w} ==> collinear {a, v, w}"
#eval thmCheck "flyspeck.ml AZIM_DIHV_SAME" AZIM_DIHV_SAME
  "|- forall v w v1 v2.        ~collinear {v, w, v1} /\\ ~collinear {v, w, v2} /\\ azim v w v1 v2 < pi        ==> azim v w v1 v2 = dihV v w v1 v2"
#eval thmCheck "flyspeck.ml AZIM_ARCV" AZIM_ARCV
  "|- forall e u v w.        orthogonal (e - u) (v - u) /\\        orthogonal (e - u) (w - u) /\\        ~collinear {u, e, v} /\\        ~collinear {u, e, w} /\\        azim u e v w <= pi        ==> azim u e v w = arcV u v w"
#eval thmCheck "flyspeck.ml REAL_CONTINUOUS_ATREAL_AZIM_COMPOSE" REAL_CONTINUOUS_ATREAL_AZIM_COMPOSE
  "|- forall f g h k x.        ~collinear {f x, g x, h x} /\\        ~collinear {f x, g x, k x} /\\        ~(k x IN aff_ge {f x, g x} {h x}) /\\        f continuous atreal x /\\        g continuous atreal x /\\        h continuous atreal x /\\        k continuous atreal x        ==> (\\x. azim (f x) (g x) (h x) (k x)) real_continuous atreal x"
#eval thmCheck "flyspeck.ml WEDGE_LUNE" WEDGE_LUNE
  "|- forall v0 v1 w1 w2.        ~coplanar {v0, v1, w1, w2} /\\ azim v0 v1 w1 w2 < pi        ==> wedge v0 v1 w1 w2 = aff_gt {v0, v1} {w1, w2}"
#eval thmCheck "flyspeck.ml AREA_BALL" AREA_BALL
  "|- forall z r. &0 <= r ==> measure (ball (z,r)) = pi * r pow 2"
#eval thmCheck "flyspeck.ml MEASURABLE_ELLIPSOID" MEASURABLE_ELLIPSOID
  "|- forall t r. measurable (ellipsoid t r)"
#eval thmCheck "flyspeck.ml MEASURABLE_CLOSED_SECTOR_LE" MEASURABLE_CLOSED_SECTOR_LE
  "|- forall r t. measurable {z | norm z <= r /\\ Arg z <= t}"
#eval thmCheck "flyspeck.ml HAS_MEASURE_LUNE_SIMPLE" HAS_MEASURE_LUNE_SIMPLE
  "|- forall z w r w1 w2.        &0 <= r /\\ ~coplanar {z, w, w1, w2}        ==> ball (z,r) INTER aff_gt {z, w} {w1, w2} has_measure            dihV z w w1 w2 * &2 * r pow 3 / &3"
#eval thmCheck "flyspeck.ml VOLUME_CONIC_CAP_WEDGE_WEAK" VOLUME_CONIC_CAP_WEDGE_WEAK
  "|- forall v0 v1 w1 w2 r a.        &0 < a /\\ ~collinear {v0, v1, w1} /\\ ~collinear {v0, v1, w2}        ==> bounded (conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) /\\            measurable (conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) /\\            vol (conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) =            (if &1 <= a \\/ r < &0             then &0             else azim v0 v1 w1 w2 / &3 * (&1 - a) * r pow 3)"
