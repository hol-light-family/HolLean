/- File: HolTest/PolytopeTest.lean
Runtime test suite: Multivariate/polytope.ml
(HolMultiLib/Polytope.lean, wired by SessionMultiLib/Polytope.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/polytope.ml"`, then `string_of_thm`).  The whole file
is also compared with HOL Light by tools/ptdiff: all 362 exported theorems
structurally and by their printed forms.

The theorems chosen here are spread over the file: faces and the
Krein-Milman-Minkowski theorem, polytopes and polyhedra, cones and Farkas's
lemma, ridges and lower bounds on faces, simplices and triangles, and
triangulations and subdivisions of cell complexes.

Loading polytope.ml (`ensurePolytope`) builds every bundle in file order; a
proof that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Polytope

open HolCore.Kernel Session SessionMultiLib.Polytope
open HolTest.CommonTest HolLight.Syntax

#eval ensurePolytope

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- Faces, exposed faces and extreme points.                               -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "polytope.ml FACE_OF_DISJOINT_RELATIVE_INTERIOR" FACE_OF_DISJOINT_RELATIVE_INTERIOR
  "|- forall f s. f face_of s /\\ ~(f = s) ==> f INTER relative_interior s = {}"
#eval thmCheck "polytope.ml KREIN_MILMAN_MINKOWSKI" KREIN_MILMAN_MINKOWSKI
  "|- forall s.
          convex s /\\ compact s ==> s = convex hull {x | x extreme_point_of s}"
#eval thmCheck "polytope.ml EXPOSED_FACE_OF_POLYHEDRON" EXPOSED_FACE_OF_POLYHEDRON
  "|- forall s f. polyhedron s ==> (f exposed_face_of s <=> f face_of s)"
#eval thmCheck "polytope.ml FACE_OF_POLYHEDRON_POLYHEDRON" FACE_OF_POLYHEDRON_POLYHEDRON
  "|- forall s c. polyhedron s /\\ c face_of s ==> polyhedron c"

/- ---------------------------------------------------------------------- -/
/- Polytopes and polyhedra.                                               -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "polytope.ml POLYTOPE_EQ_BOUNDED_POLYHEDRON" POLYTOPE_EQ_BOUNDED_POLYHEDRON
  "|- forall s. polytope s <=> polyhedron s /\\ bounded s"
#eval thmCheck "polytope.ml FINITE_POLYHEDRON_FACES" FINITE_POLYHEDRON_FACES
  "|- forall s. polyhedron s ==> FINITE {f | f face_of s}"
#eval thmCheck "polytope.ml FACET_OF_POLYHEDRON" FACET_OF_POLYHEDRON
  "|- forall s c.
          polyhedron s /\\ c facet_of s
          ==> (exists a b.
                   ~(a = vec 0) /\\
                   s SUBSET {x | a dot x <= b} /\\
                   c = s INTER {x | a dot x = b})"

/- ---------------------------------------------------------------------- -/
/- Cones, Farkas's lemma and separation.                                  -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "polytope.ml POLYHEDRAL_CONVEX_CONE" POLYHEDRAL_CONVEX_CONE
  "|- forall s.
          polyhedron s /\\ convex_cone s <=>
          (exists k. FINITE k /\\ s = convex_cone hull k)"
#eval thmCheck "polytope.ml FARKAS_LEMMA" FARKAS_LEMMA
  "|- forall A b.
          (exists x.
               A ** x = b /\\
               (forall i. 1 <= i /\\ i <= dimindex (:N) ==> &0 <= x$i)) <=>
          ~(exists y.
                b dot y < &0 /\\
                (forall i.
                     1 <= i /\\ i <= dimindex (:N) ==> &0 <= (transp A ** y)$i))"
#eval thmCheck "polytope.ml SEPARATING_HYPERPLANE_POLYHEDRA" SEPARATING_HYPERPLANE_POLYHEDRA
  "|- forall s t.
          polyhedron s /\\ polyhedron t /\\ ~(s = {}) /\\ ~(t = {}) /\\ DISJOINT s t
          ==> (exists a b.
                   ~(a = vec 0) /\\
                   (forall x. x IN s ==> a dot x < b) /\\
                   (forall x. x IN t ==> a dot x > b))"

/- ---------------------------------------------------------------------- -/
/- Ridges, lower bounds, simplices and triangles.                         -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "polytope.ml POLYHEDRON_RIDGE_TWO_FACETS" POLYHEDRON_RIDGE_TWO_FACETS
  "|- forall p r.
          polyhedron p /\\ r face_of p /\\ ~(r = {}) /\\ aff_dim r = aff_dim p - &2
          ==> (exists f1 f2.
                   f1 face_of p /\\
                   aff_dim f1 = aff_dim p - &1 /\\
                   f2 face_of p /\\
                   aff_dim f2 = aff_dim p - &1 /\\
                   ~(f1 = f2) /\\
                   r SUBSET f1 /\\
                   r SUBSET f2 /\\
                   f1 INTER f2 = r /\\
                   (forall f.
                        f face_of p /\\ aff_dim f = aff_dim p - &1 /\\ r SUBSET f
                        ==> f = f1 \\/ f = f2))"
#eval thmCheck "polytope.ml POLYTOPE_FACET_LOWER_BOUND" POLYTOPE_FACET_LOWER_BOUND
  "|- forall p.
          polytope p /\\ ~(aff_dim p = &0)
          ==> aff_dim p + &1 <= &(CARD {f | f facet_of p})"
#eval thmCheck "polytope.ml SIMPLEX_ALT" SIMPLEX_ALT
  "|- forall s i.
          i simplex s <=>
          convex s /\\
          compact s /\\
          FINITE {v | v extreme_point_of s} /\\
          &(CARD {v | v extreme_point_of s}) = i + &1 /\\
          ~affine_dependent {v | v extreme_point_of s}"
#eval thmCheck "polytope.ml HAS_SIZE_FACES_OF_SIMPLEX" HAS_SIZE_FACES_OF_SIMPLEX
  "|- forall n s.
          n simplex s ==> {f | f face_of s} HAS_SIZE 2 EXP num_of_int (n + &1)"
#eval thmCheck "polytope.ml FRONTIER_OF_TRIANGLE" FRONTIER_OF_TRIANGLE
  "|- forall a b c.
          frontier (convex hull {a, b, c}) =
          segment [a,b] UNION segment [b,c] UNION segment [c,a]"

/- ---------------------------------------------------------------------- -/
/- Triangulations and subdivisions of cell complexes.                     -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "polytope.ml triangulation" triangulation
  "|- forall tr.
          triangulation tr <=>
          FINITE tr /\\
          (forall t. t IN tr ==> (exists n. n simplex t)) /\\
          (forall t t'.
               t IN tr /\\ t' IN tr
               ==> t INTER t' face_of t /\\ t INTER t' face_of t')"
#eval thmCheck "polytope.ml TRIANGULATION_SUBSET" TRIANGULATION_SUBSET
  "|- forall tr tr'. triangulation tr /\\ tr' SUBSET tr ==> triangulation tr'"
#eval thmCheck "polytope.ml CELL_COMPLEX_SUBDIVISION_EXISTS" CELL_COMPLEX_SUBDIVISION_EXISTS
  "|- forall m d e.
          &0 < e /\\
          FINITE m /\\
          (forall c. c IN m ==> polytope c) /\\
          (forall c. c IN m ==> aff_dim c <= d) /\\
          (forall c1 c2.
               c1 IN m /\\ c2 IN m
               ==> c1 INTER c2 face_of c1 /\\ c1 INTER c2 face_of c2)
          ==> (exists m'.
                   (forall c. c IN m' ==> diameter c < e) /\\
                   UNIONS m' = UNIONS m /\\
                   FINITE m' /\\
                   (forall c. c IN m' ==> (exists d. d IN m /\\ c SUBSET d)) /\\
                   (forall c x.
                        c IN m /\\ x IN c
                        ==> (exists d. d IN m' /\\ x IN d /\\ d SUBSET c)) /\\
                   (forall c. c IN m' ==> polytope c) /\\
                   (forall c. c IN m' ==> aff_dim c <= d) /\\
                   (forall c1 c2.
                        c1 IN m' /\\ c2 IN m'
                        ==> c1 INTER c2 face_of c1 /\\ c1 INTER c2 face_of c2))"
#eval thmCheck "polytope.ml SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX" SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX
  "|- forall m.
          FINITE m /\\
          (forall c. c IN m ==> polytope c) /\\
          (forall c1 c2.
               c1 IN m /\\ c2 IN m
               ==> c1 INTER c2 face_of c1 /\\ c1 INTER c2 face_of c2)
          ==> (exists t.
                   simplicial_complex t /\\
                   UNIONS t = UNIONS m /\\
                   (forall c.
                        c IN m
                        ==> (exists f. FINITE f /\\ f SUBSET t /\\ c = UNIONS f)) /\\
                   (forall k. k IN t ==> (exists c. c IN m /\\ k SUBSET c)))"
#eval thmCheck "polytope.ml FINE_TRIANGULAR_SUBDIVISION_OF_CELL_COMPLEX" FINE_TRIANGULAR_SUBDIVISION_OF_CELL_COMPLEX
  "|- forall m d e.
          &0 < e /\\
          FINITE m /\\
          (forall c. c IN m ==> polytope c) /\\
          (forall c. c IN m ==> aff_dim c = d) /\\
          (forall c1 c2.
               c1 IN m /\\ c2 IN m
               ==> c1 INTER c2 face_of c1 /\\ c1 INTER c2 face_of c2)
          ==> (exists t.
                   triangulation t /\\
                   (forall k. k IN t ==> diameter k < e) /\\
                   (forall k. k IN t ==> aff_dim k = d) /\\
                   UNIONS t = UNIONS m /\\
                   (forall c.
                        c IN m
                        ==> (exists f. FINITE f /\\ f SUBSET t /\\ c = UNIONS f)) /\\
                   (forall k. k IN t ==> (exists c. c IN m /\\ k SUBSET c)))"
