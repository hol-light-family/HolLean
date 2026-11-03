/- File: HolTest/MoreTopTest.lean
Runtime test suite: Multivariate/moretop.ml
(HolMultiLib/MoreTop.lean, wired by SessionMultiLib/MoreTop.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/moretop.ml"`, then `string_of_thm`).  The whole file is also
compared with HOL Light by tools/moretopdiff: all exported theorems structurally
and by their printed forms.  The 20 theorems here are spread evenly over the
file; theorems that print with `?nnn` invented type variables are left out.

Loading moretop.ml (`ensureMoreTop`) builds every bundle in file order; a proof
that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.MoreTop

open HolCore.Kernel Session SessionMultiLib.MoreTop
open HolTest.CommonTest HolLight.Syntax

#eval ensureMoreTop

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

#eval thmCheck "moretop.ml INJECTIVE_EQ_1D_OPEN_MAP_UNIV" INJECTIVE_EQ_1D_OPEN_MAP_UNIV
  "|- forall f s.        f continuous_on s /\\ is_interval s        ==> ((forall x y. x IN s /\\ y IN s /\\ f x = f y ==> x = y) <=>             (forall t. open t /\\ t SUBSET s ==> open (IMAGE f t)))"
#eval thmCheck "moretop.ml SIMPLY_CONNECTED_PUNCTURED_CONVEX" SIMPLY_CONNECTED_PUNCTURED_CONVEX
  "|- forall s a. convex s /\\ &3 <= aff_dim s ==> simply_connected (s DELETE a)"
#eval thmCheck "moretop.ml BORSUK_ULAM_NOT_NULLHOMOTOPIC" BORSUK_ULAM_NOT_NULLHOMOTOPIC
  "|- forall f a.        f continuous_on sphere (vec 0,&1) /\\        IMAGE f (sphere (vec 0,&1)) SUBSET sphere (vec 0,&1) /\\        (forall x. x IN sphere (vec 0,&1) ==> f (--x) = --f x)        ==> ~homotopic_with (\\x. true)             (subtopology euclidean (sphere (vec 0,&1)),              subtopology euclidean (sphere (vec 0,&1)))             f             (\\x. a)"
#eval thmCheck "moretop.ml BORSUK_ULAM_ANTIPODAL" BORSUK_ULAM_ANTIPODAL
  "|- forall f s.        aff_dim s < &(dimindex (:M)) /\\        f continuous_on sphere (vec 0,&1) /\\        IMAGE f (sphere (vec 0,&1)) SUBSET s        ==> (exists x. x IN sphere (vec 0,&1) /\\ f (--x) = f x)"
#eval thmCheck "moretop.ml EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_SIMPLE" EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_SIMPLE
  "|- forall f s t u.        compact s /\\        convex u /\\        bounded u /\\        aff_dim t <= aff_dim u /\\        s SUBSET t /\\        f continuous_on s /\\        IMAGE f s SUBSET relative_frontier u        ==> (exists k g.                 FINITE k /\\                 k SUBSET t /\\                 DISJOINT k s /\\                 g continuous_on t DIFF k /\\                 IMAGE g (t DIFF k) SUBSET relative_frontier u /\\                 (forall x. x IN s ==> g x = f x))"
#eval thmCheck "moretop.ml EXTEND_MAP_SPHERE_TO_SPHERE_COFINITE_GEN" EXTEND_MAP_SPHERE_TO_SPHERE_COFINITE_GEN
  "|- forall f s t u p.        convex t /\\        bounded t /\\        convex u /\\        bounded u /\\        aff_dim t <= aff_dim u + &1 /\\        closed s /\\        s SUBSET relative_frontier t /\\        f continuous_on s /\\        IMAGE f s SUBSET relative_frontier u /\\        (forall c.             c IN components (relative_frontier t DIFF s)             ==> ~(c INTER p = {}))        ==> (exists k g.                 FINITE k /\\                 k SUBSET p /\\                 k SUBSET relative_frontier t /\\                 DISJOINT k s /\\                 g continuous_on relative_frontier t DIFF k /\\                 IMAGE g (relative_frontier t DIFF k) SUBSET                 relative_frontier u /\\                 (forall x. x IN s ==> g x = f x))"
#eval thmCheck "moretop.ml HOMOTOPIC_BORSUK_MAPS_IN_BOUNDED_COMPONENT" HOMOTOPIC_BORSUK_MAPS_IN_BOUNDED_COMPONENT
  "|- forall s a b.        compact s /\\        ~(a IN s) /\\        ~(b IN s) /\\        bounded (connected_component ((:real^N) DIFF s) a) /\\        homotopic_with (\\x. true)        (subtopology euclidean s,subtopology euclidean (sphere (vec 0,&1)))        (\\x. inv (norm (x - a)) % (x - a))        (\\x. inv (norm (x - b)) % (x - b))        ==> connected_component ((:real^N) DIFF s) a b"
#eval thmCheck "moretop.ml HOMOTOPY_EQUIVALENT_SEPARATION_SPHERE" HOMOTOPY_EQUIVALENT_SEPARATION_SPHERE
  "|- forall s t a r.        s SUBSET sphere (a,r) /\\        t SUBSET sphere (a,r) /\\        compact s /\\        compact t /\\        s homotopy_equivalent t        ==> (connected (sphere (a,r) DIFF s) <=>             connected (sphere (a,r) DIFF t))"
#eval thmCheck "moretop.ml SIMPLY_CONNECTED_PUNCTURED_UNIVERSE_EQ" SIMPLY_CONNECTED_PUNCTURED_UNIVERSE_EQ
  "|- forall a. simply_connected ((:real^N) DELETE a) <=> 3 <= dimindex (:N)"
#eval thmCheck "moretop.ml HOMOTOPIC_CIRCLEMAPS_DIV_1" HOMOTOPIC_CIRCLEMAPS_DIV_1
  "|- forall f g s.        homotopic_with (\\x. true)        (subtopology euclidean s,subtopology euclidean (sphere (vec 0,&1)))        f        g <=>        f continuous_on s /\\        IMAGE f s SUBSET sphere (vec 0,&1) /\\        g continuous_on s /\\        IMAGE g s SUBSET sphere (vec 0,&1) /\\        homotopic_with (\\x. true)        (subtopology euclidean s,subtopology euclidean (sphere (vec 0,&1)))        (\\x. f x / g x)        (\\x. Cx (&1))"
#eval thmCheck "moretop.ml CONTRACTIBLE_IMP_HOLOMORPHIC_LOG" CONTRACTIBLE_IMP_HOLOMORPHIC_LOG
  "|- forall s.        contractible s        ==> (forall f.                 f holomorphic_on s /\\ (forall z. z IN s ==> ~(f z = Cx (&0)))                 ==> (exists g.                          g holomorphic_on s /\\                          (forall z. z IN s ==> f z = cexp (g z))))"
#eval thmCheck "moretop.ml BORSUKIAN_RETRACTION_GEN" BORSUKIAN_RETRACTION_GEN
  "|- forall s t h k.        h continuous_on s /\\        IMAGE h s = t /\\        k continuous_on t /\\        IMAGE k t SUBSET s /\\        (forall y. y IN t ==> h (k y) = y) /\\        borsukian s        ==> borsukian t"
#eval thmCheck "moretop.ml HOMOTOPY_EQUIVALENT_BORSUKIANNESS" HOMOTOPY_EQUIVALENT_BORSUKIANNESS
  "|- forall s t. s homotopy_equivalent t ==> (borsukian s <=> borsukian t)"
#eval thmCheck "moretop.ml CONTRACTIBLE_IMP_BORSUKIAN" CONTRACTIBLE_IMP_BORSUKIAN
  "|- forall s. contractible s ==> borsukian s"
#eval thmCheck "moretop.ml BORSUKIAN_1_GEN" BORSUKIAN_1_GEN
  "|- forall s.        dimindex (:N) = 1 \\/ (exists r. s homeomorphic r) ==> borsukian s"
#eval thmCheck "moretop.ml BORSUKIAN_COMPONENTWISE" BORSUKIAN_COMPONENTWISE
  "|- forall s.        (locally connected s \\/ compact s) /\\        (forall c. c IN components s ==> borsukian c)        ==> borsukian s"
#eval thmCheck "moretop.ml HOMEOMORPHISM_UNICOHERENCE" HOMEOMORPHISM_UNICOHERENCE
  "|- forall f g s t k.        homeomorphism (s,t) (f,g) /\\ k SUBSET s        ==> (unicoherent (IMAGE f k) <=> unicoherent k)"
#eval thmCheck "moretop.ml CONNECTED_FRONTIER_COMPONENT_COMPLEMENT" CONNECTED_FRONTIER_COMPONENT_COMPLEMENT
  "|- forall s c.        connected s /\\ c IN components ((:real^N) DIFF s)        ==> connected (frontier c)"
#eval thmCheck "moretop.ml SEPARATION_BY_COMPONENT_OPEN" SEPARATION_BY_COMPONENT_OPEN
  "|- forall s.        open s /\\ ~connected ((:real^N) DIFF s)        ==> (exists c. c IN components s /\\ ~connected ((:real^N) DIFF c))"
#eval thmCheck "moretop.ml INESSENTIAL_SPHEREMAP_2" INESSENTIAL_SPHEREMAP_2
  "|- forall f a r b s.        2 < dimindex (:M) /\\        dimindex (:N) = 2 /\\        f continuous_on sphere (a,r) /\\        IMAGE f (sphere (a,r)) SUBSET sphere (b,s)        ==> (exists c.                 homotopic_with (\\z. true)                 (subtopology euclidean (sphere (a,r)),                  subtopology euclidean (sphere (b,s)))                 f                 (\\x. c))"
