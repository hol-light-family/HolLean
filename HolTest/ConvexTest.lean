/- File: HolTest/ConvexTest.lean
Runtime test suite: Multivariate/convex.ml
(HolMultiLib/Convex.lean, wired by SessionMultiLib/Convex.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/convex.ml"`, then `string_of_thm`).  The whole file is
also compared with HOL Light by tools/cxdiff: all 933 theorems structurally
and by their printed forms.

The theorems chosen here are spread over the file: affine and convex hulls,
Caratheodory, Radon and Helly, affine dimension, relative interiors and
frontiers, homeomorphisms of convex sets, the graph embedding in R^3,
barycentres, simplices, and continuity of convex functions.

Loading convex.ml (`ensureConvex`) builds every bundle in file order; a proof
that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Convex

open HolCore.Kernel Session SessionMultiLib.Convex
open HolTest.CommonTest HolLight.Syntax

#eval ensureConvex

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- Affine, conic and convex hulls; Caratheodory, Radon, Helly.            -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "convex.ml DIM_EQ_HYPERPLANE" DIM_EQ_HYPERPLANE
  "|- forall s. dim s = dimindex (:N) - 1 <=>
      (exists a. ~(a = vec 0) /\\ span s = {x | a dot x = &0})"
#eval thmCheck "convex.ml AFFINE_HULL_AFFINITY" AFFINE_HULL_AFFINITY
  "|- forall s a c. affine hull IMAGE (\\x. c % x + a) s = IMAGE (\\x. c % x + a) (affine hull s)"
#eval thmCheck "convex.ml AFFINE_EQ_SUBSPACE" AFFINE_EQ_SUBSPACE
  "|- forall s. vec 0 IN s ==> (affine s <=> subspace s)"
#eval thmCheck "convex.ml AFFINE_DEPENDENT_EXPLICIT" AFFINE_DEPENDENT_EXPLICIT
  "|- forall p. affine_dependent p <=>
      (exists s u. FINITE s /\\ s SUBSET p /\\ sum s u = &0 /\\
                   (exists v. v IN s /\\ ~(u v = &0)) /\\ vsum s (\\v. u v % v) = vec 0)"
#eval thmCheck "convex.ml CONIC_HULL_SUBSET_SPAN" CONIC_HULL_SUBSET_SPAN
  "|- forall s. conic hull s SUBSET span s"
#eval thmCheck "convex.ml CONVEX_PCROSS_EQ" CONVEX_PCROSS_EQ
  "|- forall s t. convex (s PCROSS t) <=> s = {} \\/ t = {} \\/ convex s /\\ convex t"
#eval thmCheck "convex.ml CONVEX_CBALL" CONVEX_CBALL
  "|- forall x e. convex (cball (x,e))"
#eval thmCheck "convex.ml CONVEX_HULL_EXPLICIT" CONVEX_HULL_EXPLICIT
  "|- forall p. convex hull p =
      {y | exists s u. FINITE s /\\ s SUBSET p /\\ (forall x. x IN s ==> &0 <= u x) /\\
                       sum s u = &1 /\\ vsum s (\\v. u v % v) = y}"
#eval thmCheck "convex.ml CARATHEODORY" CARATHEODORY
  "|- forall p. convex hull p =
      {x | exists s. FINITE s /\\ s SUBSET p /\\ CARD s <= dimindex (:N) + 1 /\\
                     x IN convex hull s}"
#eval thmCheck "convex.ml RADON" RADON
  "|- forall c. affine_dependent c ==>
      (exists m p. m SUBSET c /\\ p SUBSET c /\\ DISJOINT m p /\\
                   ~DISJOINT (convex hull m) (convex hull p))"
#eval thmCheck "convex.ml HELLY" HELLY
  "|- forall f. FINITE f /\\ CARD f >= dimindex (:N) + 1 /\\ (forall s. s IN f ==> convex s) /\\
      (forall t. t SUBSET f /\\ CARD t = dimindex (:N) + 1 ==> ~(INTERS t = {}))
      ==> ~(INTERS f = {})"
#eval thmCheck "convex.ml CLOSED_POLAR_DUAL" CLOSED_POLAR_DUAL
  "|- forall s. closed (polar_dual s)"

/- ---------------------------------------------------------------------- -/
/- Connectedness, intervals and segments.                                 -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "convex.ml CONVEX_CONNECTED" CONVEX_CONNECTED
  "|- forall s. convex s ==> connected s"
#eval thmCheck "convex.ml CARD_LE_COMPONENTS_FRONTIER" CARD_LE_COMPONENTS_FRONTIER
  "|- forall s. compact s ==> components s <=_c components (frontier s)"
#eval thmCheck "convex.ml CONVEX_INTERVAL" CONVEX_INTERVAL
  "|- forall a b. convex (interval [a,b]) /\\ convex (interval (a,b))"
#eval thmCheck "convex.ml CONVEX_EQ_CONNECTED_LINE_INTERSECTION"
  CONVEX_EQ_CONNECTED_LINE_INTERSECTION
  "|- forall s. convex s <=> (forall a b. connected (s INTER affine hull {a, b}))"
#eval thmCheck "convex.ml COLLINEAR_3_AFFINE_HULL" COLLINEAR_3_AFFINE_HULL
  "|- forall a b c. ~(a = b) ==> (collinear {a, b, c} <=> c IN affine hull {a, b})"

/- ---------------------------------------------------------------------- -/
/- Affine dimension.                                                      -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "convex.ml AFF_DIM_SING" AFF_DIM_SING
  "|- forall a. aff_dim {a} = &0"
#eval thmCheck "convex.ml AFF_DIM_2" AFF_DIM_2
  "|- forall a b. aff_dim {a, b} = (if a = b then &0 else &1)"
#eval thmCheck "convex.ml AFF_DIM_UNIV" AFF_DIM_UNIV
  "|- aff_dim (:real^N) = &(dimindex (:N))"
#eval thmCheck "convex.ml COLLINEAR_AFF_DIM" COLLINEAR_AFF_DIM
  "|- forall s. collinear s <=> aff_dim s <= &1"
#eval thmCheck "convex.ml DIM_OPEN" DIM_OPEN
  "|- forall s. open s /\\ ~(s = {}) ==> dim s = dimindex (:N)"
#eval thmCheck "convex.ml AFF_DIM_PCROSS" AFF_DIM_PCROSS
  "|- forall s t. ~(s = {}) /\\ ~(t = {}) ==> aff_dim (s PCROSS t) = aff_dim s + aff_dim t"
#eval thmCheck "convex.ml AFF_DIM_BALL" AFF_DIM_BALL
  "|- forall a r. aff_dim (ball (a,r)) = (if &0 < r then &(dimindex (:N)) else -- &1)"

/- ---------------------------------------------------------------------- -/
/- Relative interiors and frontiers; homeomorphisms.                      -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "convex.ml DIAMETER_RELATIVE_FRONTIER" DIAMETER_RELATIVE_FRONTIER
  "|- forall s. bounded s /\\ ~(exists a. s = {a})
      ==> diameter (relative_frontier s) = diameter s"
#eval thmCheck "convex.ml HOMEOMORPHIC_CONVEX_COMPACT_SETS" HOMEOMORPHIC_CONVEX_COMPACT_SETS
  "|- forall s t. convex s /\\ compact s /\\ convex t /\\ compact t /\\ aff_dim s = aff_dim t
      ==> s homeomorphic t"
#eval thmCheck "convex.ml HOMEOMORPHIC_CLOSED_INTERVALS" HOMEOMORPHIC_CLOSED_INTERVALS
  "|- forall a b c d. ~(interval (a,b) = {}) /\\ ~(interval (c,d) = {})
      ==> interval [a,b] homeomorphic interval [c,d]"
#eval thmCheck "convex.ml HOMEOMORPHIC_CONVEX_OPEN_SETS" HOMEOMORPHIC_CONVEX_OPEN_SETS
  "|- forall s t. convex s /\\ open s /\\ convex t /\\ open t /\\ (s = {} <=> t = {})
      ==> s homeomorphic t"
#eval thmCheck "convex.ml LIPSCHITZ_CONVEX_SPHERICAL_PROJECTION"
  LIPSCHITZ_CONVEX_SPHERICAL_PROJECTION
  "|- forall s. convex s /\\ vec 0 IN relative_interior s
      ==> (exists B. forall x y. x IN relative_frontier s /\\ y IN relative_frontier s
               ==> dist (inv (norm x) % x,inv (norm y) % y) <= B * dist (x,y))"
#eval thmCheck "convex.ml GRAPH_EMBEDS_IN_R3" GRAPH_EMBEDS_IN_R3
  "|- forall s. s <=_c (:real)
      ==> (exists v. (forall a b. a IN s /\\ b IN s ==> (v a = v b <=> a = b)) /\\
            (forall a b c d. ~({v a, v b} = {v c, v d})
               ==> segment [v a,v b] INTER segment [v c,v d] SUBSET
                   {v a, v b} INTER {v c, v d}))"
#eval thmCheck "convex.ml SUPPORTING_HYPERPLANE_FRONTIER" SUPPORTING_HYPERPLANE_FRONTIER
  "|- forall s x. convex s /\\ x IN frontier s
      ==> (exists a. ~(a = vec 0) /\\ (forall y. y IN closure s ==> a dot x <= a dot y))"
#eval thmCheck "convex.ml UNBOUNDED_CONVEX_CLOSED_CONTAINS_RAY"
  UNBOUNDED_CONVEX_CLOSED_CONTAINS_RAY
  "|- forall s a. convex s /\\ ~bounded s /\\ closed s /\\ a IN s
      ==> (exists l. ~(l = vec 0) /\\ (forall t. &0 <= t ==> a + t % l IN s))"

/- ---------------------------------------------------------------------- -/
/- Explicit formulas, barycentres and simplices.                          -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "convex.ml RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT"
  RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT
  "|- forall s. ~affine_dependent s
      ==> relative_interior (convex hull s) =
          {y | exists u. (forall x. x IN s ==> &0 < u x) /\\ sum s u = &1 /\\
                         vsum s (\\x. u x % x) = y}"
#eval thmCheck "convex.ml DISJOINT_RELATIVE_INTERIOR_CONVEX_HULL"
  DISJOINT_RELATIVE_INTERIOR_CONVEX_HULL
  "|- forall s. ~affine_dependent s /\\ ~(exists a. s = {a})
      ==> relative_interior (convex hull s) INTER s = {}"
#eval thmCheck "convex.ml INTERIOR_CONVEX_HULL_3" INTERIOR_CONVEX_HULL_3
  "|- forall a b c. ~collinear {a, b, c}
      ==> interior (convex hull {a, b, c}) =
          {v | exists x y z. &0 < x /\\ x < &1 /\\ &0 < y /\\ y < &1 /\\ &0 < z /\\ z < &1 /\\
                             x + y + z = &1 /\\ x % a + y % b + z % c = v}"
#eval thmCheck "convex.ml BARYCENTRE_2" BARYCENTRE_2
  "|- forall a b. barycentre {a, b} = midpoint (a,b)"
#eval thmCheck "convex.ml STD_SIMPLEX" STD_SIMPLEX
  "|- convex hull (vec 0 INSERT {basis i | 1 <= i /\\ i <= dimindex (:N)}) =
      {x | (forall i. 1 <= i /\\ i <= dimindex (:N) ==> &0 <= x$i) /\\
           sum (1..dimindex (:N)) (\\i. x$i) <= &1}"

/- ---------------------------------------------------------------------- -/
/- Continuity of convex functions.                                        -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "convex.ml CONTINUOUS_MIDPOINT_CONVEX" CONTINUOUS_MIDPOINT_CONVEX
  "|- forall f s. lift o f continuous_on s /\\ convex s /\\
      (forall x y. x IN s /\\ y IN s ==> f (midpoint (x,y)) <= (f x + f y) / &2)
      ==> f convex_on s"
#eval thmCheck "convex.ml CONVEX_ON_CONTINUOUS" CONVEX_ON_CONTINUOUS
  "|- forall f s. open s /\\ f convex_on s ==> lift o f continuous_on s"
#eval thmCheck "convex.ml CONVEX_IMP_LIPSCHITZ" CONVEX_IMP_LIPSCHITZ
  "|- forall f s t. f convex_on t /\\ compact s /\\ s SUBSET relative_interior t
      ==> (exists B. &0 < B /\\
             (forall x y. x IN s /\\ y IN s ==> abs (f x - f y) <= B * norm (x - y)))"
