/- File: HolTest/PathsTest.lean
Runtime test suite: Multivariate/paths.ml
(HolMultiLib/Paths.lean, wired by SessionMultiLib/Paths.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/paths.ml"`, then `string_of_thm`).  The whole file is
also compared with HOL Light by tools/pathsdiff: all 1,071 exported theorems
structurally and by their printed forms.

The theorems chosen here are spread over the file: paths and arcs, path
connectedness, inside and outside, homotopy and simple connectedness,
contractibility, punctured spheres, dimension, covering spaces, invariance of
domain and dimension, and the Jordan curve theorem.

Loading paths.ml (`ensurePaths`) builds every bundle in file order; a proof
that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Paths

open HolCore.Kernel Session SessionMultiLib.Paths
open HolTest.CommonTest HolLight.Syntax

#eval ensurePaths

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- Paths, arcs and path connectedness.                                    -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "paths.ml PATH_JOIN" PATH_JOIN
  "|- forall g1 g2.
          pathfinish g1 = pathstart g2
          ==> (path (g1 ++ g2) <=> path g1 /\\ path g2)"
#eval thmCheck "paths.ml SIMPLE_PATH_JOIN_LOOP" SIMPLE_PATH_JOIN_LOOP
  "|- forall g1 g2.
          arc g1 /\\
          arc g2 /\\
          pathfinish g1 = pathstart g2 /\\
          pathfinish g2 = pathstart g1 /\\
          path_image g1 INTER path_image g2 SUBSET {pathstart g1, pathstart g2}
          ==> simple_path (g1 ++ g2)"
#eval thmCheck "paths.ml ARC_JOIN" ARC_JOIN
  "|- forall g1 g2.
          arc g1 /\\
          arc g2 /\\
          pathfinish g1 = pathstart g2 /\\
          path_image g1 INTER path_image g2 SUBSET {pathstart g2}
          ==> arc (g1 ++ g2)"
#eval thmCheck "paths.ml PATH_CONNECTED_IMP_CONNECTED" PATH_CONNECTED_IMP_CONNECTED
  "|- forall s. path_connected s ==> connected s"
#eval thmCheck "paths.ml CONVEX_IMP_PATH_CONNECTED" CONVEX_IMP_PATH_CONNECTED
  "|- forall s. convex s ==> path_connected s"
#eval thmCheck "paths.ml PATH_CONNECTED_PUNCTURED_UNIVERSE" PATH_CONNECTED_PUNCTURED_UNIVERSE
  "|- forall a. 2 <= dimindex (:N) ==> path_connected ((:real^N) DIFF {a})"
#eval thmCheck "paths.ml PATH_COMPONENT_EQ_CONNECTED_COMPONENT" PATH_COMPONENT_EQ_CONNECTED_COMPONENT
  "|- forall s x.
          locally path_connected s
          ==> path_component s x = connected_component s x"
#eval thmCheck "paths.ml LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED" LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED
  "|- forall s. locally path_connected s ==> locally connected s"

/- ---------------------------------------------------------------------- -/
/- Inside and outside of a set.                                           -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "paths.ml CONNECTED_COMPLEMENT_BOUNDED_CONVEX" CONNECTED_COMPLEMENT_BOUNDED_CONVEX
  "|- forall s.
          2 <= dimindex (:N) /\\ bounded s /\\ convex s
          ==> connected ((:real^N) DIFF s)"
#eval thmCheck "paths.ml OUTSIDE_BOUNDED_NONEMPTY" OUTSIDE_BOUNDED_NONEMPTY
  "|- forall s. bounded s ==> ~(outside s = {})"
#eval thmCheck "paths.ml INSIDE_OUTSIDE_UNIQUE" INSIDE_OUTSIDE_UNIQUE
  "|- forall s t u.
          connected t /\\
          bounded t /\\
          connected u /\\
          ~bounded u /\\
          ~connected ((:real^N) DIFF s) /\\
          t UNION u = (:real^N) DIFF s
          ==> inside s = t /\\ outside s = u"

/- ---------------------------------------------------------------------- -/
/- Homotopy, simple connectedness and contractibility.                    -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "paths.ml HOMOTOPIC_PATHS_JOIN" HOMOTOPIC_PATHS_JOIN
  "|- forall s p q p' q'.
          homotopic_paths s p p' /\\
          homotopic_paths s q q' /\\
          pathfinish p = pathstart q
          ==> homotopic_paths s (p ++ q) (p' ++ q')"
#eval thmCheck "paths.ml HOMOTOPIC_LOOPS_IMP_PATH_COMPONENT_VALUE" HOMOTOPIC_LOOPS_IMP_PATH_COMPONENT_VALUE
  "|- forall s p q t.
          homotopic_loops s p q /\\ t IN interval [vec 0,vec 1]
          ==> path_component s (p t) (q t)"
#eval thmCheck "paths.ml PATH_CONNECTED_EQ_HOMOTOPIC_POINTS" PATH_CONNECTED_EQ_HOMOTOPIC_POINTS
  "|- forall s.
          path_connected s <=>
          (forall a b.
               a IN s /\\ b IN s
               ==> homotopic_loops s (linepath (a,a)) (linepath (b,b)))"
#eval thmCheck "paths.ml SIMPLY_CONNECTED_EQ_CONTRACTIBLE_PATH" SIMPLY_CONNECTED_EQ_CONTRACTIBLE_PATH
  "|- forall s.
          simply_connected s <=>
          path_connected s /\\
          (forall p.
               path p /\\ path_image p SUBSET s /\\ pathfinish p = pathstart p
               ==> homotopic_paths s p (linepath (pathstart p,pathstart p)))"
#eval thmCheck "paths.ml SIMPLY_CONNECTED_IMP_CONNECTED" SIMPLY_CONNECTED_IMP_CONNECTED
  "|- forall s. simply_connected s ==> connected s"
#eval thmCheck "paths.ml HOMOTOPY_EQUIVALENT_SYM" HOMOTOPY_EQUIVALENT_SYM
  "|- forall s t. s homotopy_equivalent t <=> t homotopy_equivalent s"
#eval thmCheck "paths.ml HOMOTOPY_EQUIVALENT_CONNECTEDNESS" HOMOTOPY_EQUIVALENT_CONNECTEDNESS
  "|- forall s t. s homotopy_equivalent t ==> (connected s <=> connected t)"
#eval thmCheck "paths.ml CONTRACTIBLE_IMP_SIMPLY_CONNECTED" CONTRACTIBLE_IMP_SIMPLY_CONNECTED
  "|- forall s. contractible s ==> simply_connected s"

/- ---------------------------------------------------------------------- -/
/- Punctured spheres; dimension.                                          -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "paths.ml HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE" HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE
  "|- forall a r b t.
          &0 < r /\\
          b IN sphere (a,r) /\\
          affine t /\\
          aff_dim t + &1 = &(dimindex (:N))
          ==> sphere (a,r) DELETE b homeomorphic t"
#eval thmCheck "paths.ml CONTRACTIBLE_PUNCTURED_SPHERE" CONTRACTIBLE_PUNCTURED_SPHERE
  "|- forall a r b.
          &0 < r /\\ b IN sphere (a,r) ==> contractible (sphere (a,r) DELETE b)"
#eval thmCheck "paths.ml CARD_EQ_COMPONENTS_IN_COMPACTIFICATION" CARD_EQ_COMPONENTS_IN_COMPACTIFICATION
  "|- forall f g a r s z.
          homeomorphism (sphere (a,r) DELETE z,(:real^M)) (f,g) /\\
          s SUBSET sphere (a,r) /\\
          z IN sphere (a,r) /\\
          ~(z IN closure s)
          ==> components (sphere (a,r) DIFF s) =_c
              {1} +_c
              {c | c IN components ((:real^M) DIFF IMAGE f s) /\\ bounded c}"
#eval thmCheck "paths.ml DIMENSION_LE_EQ" DIMENSION_LE_EQ
  "|- forall s n.
          dimension s <= n <=>
          -- &1 <= n /\\
          (forall v a.
               open v /\\ a IN v /\\ a IN s
               ==> (exists u.
                        a IN u /\\
                        u SUBSET v /\\
                        open u /\\
                        dimension (s INTER frontier u) <= n - &1))"
#eval thmCheck "paths.ml DIMENSION_LE_DIMINDEX" DIMENSION_LE_DIMINDEX
  "|- forall s. dimension s <= &(dimindex (:N))"
#eval thmCheck "paths.ml DIMENSION_LE_UNION" DIMENSION_LE_UNION
  "|- forall s t n.
          fsigma s /\\ fsigma t /\\ dimension s <= n /\\ dimension t <= n
          ==> dimension (s UNION t) <= n"
#eval thmCheck "paths.ml TINY_INDUCTIVE_DIMENSION" TINY_INDUCTIVE_DIMENSION
  "|- forall s n.
          locally compact s
          ==> (dimension s <= n <=>
               (if s = {}
                then -- &1 <= n
                else &0 <= n /\\
                     (forall x y.
                          x IN s /\\ y IN s /\\ ~(x = y)
                          ==> (exists b.
                                   closed_in (subtopology euclidean s) b /\\
                                   dimension b <= n - &1 /\\
                                   (exists u v.
                                        open_in (subtopology euclidean s) u /\\
                                        open_in (subtopology euclidean s) v /\\
                                        DISJOINT u v /\\
                                        u UNION v = s DIFF b /\\
                                        x IN u /\\
                                        y IN v)))))"

/- ---------------------------------------------------------------------- -/
/- Covering spaces and lifting.                                           -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "paths.ml COVERING_SPACE_LIFT_UNIQUE" COVERING_SPACE_LIFT_UNIQUE
  "|- forall p f g1 g2 c s t a x.
          covering_space (c,p) s /\\
          f continuous_on t /\\
          IMAGE f t SUBSET s /\\
          g1 continuous_on t /\\
          IMAGE g1 t SUBSET c /\\
          (forall x. x IN t ==> f x = p (g1 x)) /\\
          g2 continuous_on t /\\
          IMAGE g2 t SUBSET c /\\
          (forall x. x IN t ==> f x = p (g2 x)) /\\
          connected t /\\
          a IN t /\\
          g1 a = g2 a /\\
          x IN t
          ==> g1 x = g2 x"
#eval thmCheck "paths.ml COVERING_SPACE_LIFT_HOMOTOPY" COVERING_SPACE_LIFT_HOMOTOPY
  "|- forall p c s h f u.
          covering_space (c,p) s /\\
          h continuous_on interval [vec 0,vec 1] PCROSS u /\\
          IMAGE h (interval [vec 0,vec 1] PCROSS u) SUBSET s /\\
          (forall y. y IN u ==> h (pastecart (vec 0) y) = p (f y)) /\\
          f continuous_on u /\\
          IMAGE f u SUBSET c
          ==> (exists k.
                   k continuous_on interval [vec 0,vec 1] PCROSS u /\\
                   IMAGE k (interval [vec 0,vec 1] PCROSS u) SUBSET c /\\
                   (forall y. y IN u ==> k (pastecart (vec 0) y) = f y) /\\
                   (forall z.
                        z IN interval [vec 0,vec 1] PCROSS u ==> h z = p (k z)))"
#eval thmCheck "paths.ml COVERING_SPACE_MONODROMY" COVERING_SPACE_MONODROMY
  "|- forall p c s g1 g2 h1 h2.
          covering_space (c,p) s /\\
          path g1 /\\
          path_image g1 SUBSET s /\\
          path g2 /\\
          path_image g2 SUBSET s /\\
          homotopic_paths s g1 g2 /\\
          path h1 /\\
          path_image h1 SUBSET c /\\
          (forall t. t IN interval [vec 0,vec 1] ==> p (h1 t) = g1 t) /\\
          path h2 /\\
          path_image h2 SUBSET c /\\
          (forall t. t IN interval [vec 0,vec 1] ==> p (h2 t) = g2 t) /\\
          pathstart h1 = pathstart h2
          ==> pathfinish h1 = pathfinish h2"
#eval thmCheck "paths.ml COVERING_SPACE_LIFT" COVERING_SPACE_LIFT
  "|- forall p c s f u.
          covering_space (c,p) s /\\
          simply_connected u /\\
          locally path_connected u /\\
          f continuous_on u /\\
          IMAGE f u SUBSET s
          ==> (exists g.
                   g continuous_on u /\\
                   IMAGE g u SUBSET c /\\
                   (forall y. y IN u ==> p (g y) = f y))"
#eval thmCheck "paths.ml UNIVERSAL_COVERING_SPACE" UNIVERSAL_COVERING_SPACE
  "|- forall c p c' p' s.
          covering_space (c,p) s /\\
          covering_space (c',p') s /\\
          locally path_connected c /\\
          simply_connected c /\\
          connected c'
          ==> (exists q.
                   covering_space (c,q) c' /\\
                   (forall x. x IN c ==> p' (q x) = p x))"
#eval thmCheck "paths.ml PROPER_LOCAL_HOMEOMORPHISM_IMP_COVERING_MAP" PROPER_LOCAL_HOMEOMORPHISM_IMP_COVERING_MAP
  "|- forall p c s.
          IMAGE p c = s /\\
          (forall k.
               k SUBSET s /\\ compact k ==> compact {x | x IN c /\\ p x IN k}) /\\
          (forall x.
               x IN c
               ==> (exists t u q.
                        x IN t /\\
                        open_in (subtopology euclidean c) t /\\
                        open_in (subtopology euclidean s) u /\\
                        homeomorphism (t,u) (p,q)))
          ==> covering_space (c,p) s"
#eval thmCheck "paths.ml CARD_EQ_FUNDAMENTAL_GROUP_COVERING_SPACE" CARD_EQ_FUNDAMENTAL_GROUP_COVERING_SPACE
  "|- forall p c s a.
          covering_space (c,p) s /\\ path_connected c /\\ a IN c
          ==> fundamental_group (s,p a) =_c
              fundamental_group (c,a) *_c {a' | a' IN c /\\ p a' = p a}"

/- ---------------------------------------------------------------------- -/
/- Invariance of domain and dimension.                                    -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "paths.ml INVARIANCE_OF_DOMAIN" INVARIANCE_OF_DOMAIN
  "|- forall f s.
          f continuous_on s /\\
          open s /\\
          (forall x y. x IN s /\\ y IN s /\\ f x = f y ==> x = y)
          ==> open (IMAGE f s)"
#eval thmCheck "paths.ml INVARIANCE_OF_DIMENSION" INVARIANCE_OF_DIMENSION
  "|- forall f s.
          f continuous_on s /\\
          open s /\\
          ~(s = {}) /\\
          (forall x y. x IN s /\\ y IN s /\\ f x = f y ==> x = y)
          ==> dimindex (:M) <= dimindex (:N)"
#eval thmCheck "paths.ml HOMEOMORPHIC_INTERVALS_EQ" HOMEOMORPHIC_INTERVALS_EQ
  "|- (forall a b c d.
           interval [a,b] homeomorphic interval [c,d] <=>
           aff_dim (interval [a,b]) = aff_dim (interval [c,d])) /\\
      (forall a b c d.
           interval [a,b] homeomorphic interval (c,d) <=>
           interval [a,b] = {} /\\ interval (c,d) = {}) /\\
      (forall a b c d.
           interval (a,b) homeomorphic interval [c,d] <=>
           interval (a,b) = {} /\\ interval [c,d] = {}) /\\
      (forall a b c d.
           interval (a,b) homeomorphic interval (c,d) <=>
           interval (a,b) = {} /\\ interval (c,d) = {} \\/
           ~(interval (a,b) = {}) /\\
           ~(interval (c,d) = {}) /\\
           dimindex (:M) = dimindex (:N))"
#eval thmCheck "paths.ml HOMEOMORPHIC_BALLS_EQ" HOMEOMORPHIC_BALLS_EQ
  "|- forall a b r s.
          ball (a,r) homeomorphic ball (b,s) <=>
          r <= &0 /\\ s <= &0 \\/
          &0 < r /\\ &0 < s /\\ dimindex (:M) = dimindex (:N)"
#eval thmCheck "paths.ml NO_EMBEDDING_SPHERE_LOWDIM" NO_EMBEDDING_SPHERE_LOWDIM
  "|- forall f a r.
          &0 < r /\\
          f continuous_on sphere (a,r) /\\
          (forall x y.
               x IN sphere (a,r) /\\ y IN sphere (a,r) /\\ f x = f y ==> x = y)
          ==> dimindex (:M) <= dimindex (:N)"

/- ---------------------------------------------------------------------- -/
/- The Jordan curve theorem and separation.                               -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "paths.ml JORDAN_CURVE_THEOREM" JORDAN_CURVE_THEOREM
  "|- forall c.
          simple_path c /\\ pathfinish c = pathstart c
          ==> (exists ins out.
                   ~(ins = {}) /\\
                   open ins /\\
                   connected ins /\\
                   ~(out = {}) /\\
                   open out /\\
                   connected out /\\
                   bounded ins /\\
                   ~bounded out /\\
                   ins INTER out = {} /\\
                   ins UNION out = (:real^2) DIFF path_image c /\\
                   frontier ins = path_image c /\\
                   frontier out = path_image c)"
#eval thmCheck "paths.ml JORDAN_BROUWER_SEPARATION" JORDAN_BROUWER_SEPARATION
  "|- forall s a r.
          &0 < r /\\ s homeomorphic sphere (a,r)
          ==> ~connected ((:real^N) DIFF s)"
#eval thmCheck "paths.ml HOMEOMORPHIC_SEPARATION" HOMEOMORPHIC_SEPARATION
  "|- forall s t.
          bounded s /\\ bounded t /\\ s homeomorphic t
          ==> (connected ((:real^N) DIFF s) <=> connected ((:real^N) DIFF t))"
#eval thmCheck "paths.ml HAS_SIZE_EQ_COMPONENTS_COMPLEMENTS" HAS_SIZE_EQ_COMPONENTS_COMPLEMENTS
  "|- forall s t n.
          (closed s /\\ closed t \\/ bounded s /\\ bounded t) /\\ s homeomorphic t
          ==> (components ((:real^N) DIFF s) HAS_SIZE n <=>
               components ((:real^N) DIFF t) HAS_SIZE n)"
