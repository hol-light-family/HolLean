/- File: HolTest/TopologyTest.lean
Runtime test suite: Multivariate/topology.ml (HolMultiLib/Topology.lean, wired
by SessionMultiLib/Topology.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/topology.ml"`, then `string_of_thm`).  The whole file is
also compared with HOL Light by tools/topdiff: all 2,494 theorems
structurally and by their printed forms.

The theorems chosen here print without invented type variables, so their
printed forms do not depend on type-variable numbering.  They are spread over
the whole file, from the Euclidean metric at the start to partitions of unity
at the end.

Loading topology.ml (`ensureTopology`) builds every bundle in file order; a
proof that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Topology

open HolCore.Kernel Session SessionMultiLib.Topology
open HolTest.CommonTest HolLight.Syntax

#eval ensureTopology

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- Theorem statements (topology.ml), as HOL Light prints them.             -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "topology.ml euclidean_metric" euclidean_metric
  "|- euclidean_metric = metric ((:real^N),dist)"
#eval thmCheck "topology.ml OPEN_IN_REFL" OPEN_IN_REFL
  "|- forall s. open_in (subtopology euclidean s) s"
#eval thmCheck "topology.ml TOPSPACE_EUCLIDEAN" TOPSPACE_EUCLIDEAN
  "|- topspace euclidean = (:real^N)"
#eval thmCheck "topology.ml CLOSED_POSITIVE_ORTHANT" CLOSED_POSITIVE_ORTHANT
  "|- closed {x | forall i. 1 <= i /\\ i <= dimindex (:N) ==> &0 <= x$i}"
#eval thmCheck "topology.ml CLOSED_SING" CLOSED_SING
  "|- forall a. closed {a}"
#eval thmCheck "topology.ml FRONTIER_FRONTIER_FRONTIER" FRONTIER_FRONTIER_FRONTIER
  "|- forall s. frontier (frontier (frontier s)) = frontier (frontier s)"
#eval thmCheck "topology.ml LIM_NULL_SUB" LIM_NULL_SUB
  "|- forall net f g. (f --> vec 0) net /\\ (g --> vec 0) net ==> ((\\x. f x - g x) --> vec 0) net"
#eval thmCheck "topology.ml BOUNDED_INTERIOR" BOUNDED_INTERIOR
  "|- forall s. bounded s ==> bounded (interior s)"
#eval thmCheck "topology.ml BOLZANO_WEIERSTRASS_IMP_BOUNDED" BOLZANO_WEIERSTRASS_IMP_BOUNDED
  "|- forall s. (forall t. INFINITE t /\\ t SUBSET s ==> (exists x. x limit_point_of t)) ==> bounded s"
#eval thmCheck "topology.ml CONTINUOUS_TRANSFORM_WITHIN_OPEN" CONTINUOUS_TRANSFORM_WITHIN_OPEN
  "|- forall f g s a. open s /\\ a IN s /\\ (forall x. x IN s ==> f x = g x) /\\ f continuous at a ==> g continuous at a"
#eval thmCheck "topology.ml CLOSED_MAP_CLOSURES" CLOSED_MAP_CLOSURES
  "|- forall f. (forall s. closed s ==> closed (IMAGE f s)) <=> (forall s. closure (IMAGE f s) SUBSET IMAGE f (closure s))"
#eval thmCheck "topology.ml BOUNDED_HALFSPACE_LE" BOUNDED_HALFSPACE_LE
  "|- forall a b. bounded {x | a dot x <= b} <=> a = vec 0 /\\ b < &0"
#eval thmCheck "topology.ml CONNECTED_UNIV" CONNECTED_UNIV
  "|- connected (:real^N)"
#eval thmCheck "topology.ml CONNECTED_COMPONENT_SYM" CONNECTED_COMPONENT_SYM
  "|- forall s x y. connected_component s x y ==> connected_component s y x"
#eval thmCheck "topology.ml COMPACT_INTERVAL" COMPACT_INTERVAL
  "|- forall a b. compact (interval [a,b])"
#eval thmCheck "topology.ml CLOSED_NEGATIONS" CLOSED_NEGATIONS
  "|- forall s. closed s ==> closed (IMAGE (--) s)"
#eval thmCheck "topology.ml HOMEOMORPHIC_REFL" HOMEOMORPHIC_REFL
  "|- forall s. s homeomorphic s"
#eval thmCheck "topology.ml INVOLUTION_IMP_HOMEOMORPHISM" INVOLUTION_IMP_HOMEOMORPHISM
  "|- forall f s. f continuous_on s /\\ IMAGE f s SUBSET s /\\ (forall x. x IN s ==> f (f x) = x) ==> homeomorphism (s,s) (f,f)"
#eval thmCheck "topology.ml CARD_EQ_EUCLIDEAN" CARD_EQ_EUCLIDEAN
  "|- (:real^N) =_c (:real)"
#eval thmCheck "topology.ml CARD_EQ_CONNECTED" CARD_EQ_CONNECTED
  "|- forall s a b. connected s /\\ a IN s /\\ b IN s /\\ ~(a = b) ==> s =_c (:real)"
#eval thmCheck "topology.ml SERIES_DROP_POS" SERIES_DROP_POS
  "|- forall f s a. (f sums a) s /\\ (forall x. x IN s ==> &0 <= drop (f x)) ==> &0 <= drop a"
#eval thmCheck "topology.ml UNIFORMLY_CONTINUOUS_ON_LIFT_SETDIST"
  UNIFORMLY_CONTINUOUS_ON_LIFT_SETDIST
  "|- forall s t. (\\y. lift (setdist ({y},s))) uniformly_continuous_on t"
#eval thmCheck "topology.ml LOCALLY_COMPACT_CLOSURE_DIFF" LOCALLY_COMPACT_CLOSURE_DIFF
  "|- forall s. locally compact s <=> closed (closure s DIFF s)"
#eval thmCheck "topology.ml GDELTA_UNIV" GDELTA_UNIV
  "|- gdelta (:real^N)"
#eval thmCheck "topology.ml BOREL_UNIV" BOREL_UNIV
  "|- borel (:real^N)"
#eval thmCheck "topology.ml CARD_EQ_GDELTA_SETS" CARD_EQ_GDELTA_SETS
  "|- {s | gdelta s} =_c (:real)"
#eval thmCheck "topology.ml BAIRE_CONST" BAIRE_CONST
  "|- forall s n a. baire n s (\\x. a)"
#eval thmCheck "topology.ml BAIRE_MUL" BAIRE_MUL
  "|- forall f g s n. baire n s (\\x. lift (f x)) /\\ baire n s g ==> baire n s (\\x. f x % g x)"
#eval thmCheck "topology.ml BAIRE_IMP_BOREL_MEASURABLE" BAIRE_IMP_BOREL_MEASURABLE
  "|- forall f s n. baire n s f ==> f borel_measurable_on s"
#eval thmCheck "topology.ml BOREL_MEASURABLE_CONST" BOREL_MEASURABLE_CONST
  "|- forall s c. (\\x. c) borel_measurable_on s"
#eval thmCheck "topology.ml BOREL_MEASURABLE_INDICATOR" BOREL_MEASURABLE_INDICATOR
  "|- forall s. indicator s borel_measurable_on (:real^N) <=> borel s"
#eval thmCheck "topology.ml ANALYTIC_EMPTY" ANALYTIC_EMPTY
  "|- analytic {}"
#eval thmCheck "topology.ml ANALYTIC_UNIV" ANALYTIC_UNIV
  "|- analytic (:real^N)"
#eval thmCheck "topology.ml HOMEOMORPHIC_ANALYTICITY" HOMEOMORPHIC_ANALYTICITY
  "|- forall s t. s homeomorphic t ==> (analytic s <=> analytic t)"
#eval thmCheck "topology.ml CARD_EQ_ANALYTIC_SETS" CARD_EQ_ANALYTIC_SETS
  "|- {s | analytic s} =_c (:real)"
#eval thmCheck "topology.ml CARD_EQ_BOREL_SETS" CARD_EQ_BOREL_SETS
  "|- {s | borel s} =_c (:real)"
#eval thmCheck "topology.ml BOREL_PREIMAGE_FINITE" BOREL_PREIMAGE_FINITE
  "|- forall f s. f continuous_on s /\\ fsigma s ==> borel {y | FINITE {x | x IN s /\\ f x = y}}"
#eval thmCheck "topology.ml BOREL_PREIMAGE_INFINITE" BOREL_PREIMAGE_INFINITE
  "|- forall f s. f continuous_on s /\\ fsigma s ==> borel {y | INFINITE {x | x IN s /\\ f x = y}}"
#eval thmCheck "topology.ml DENSE_GDELTA_IMP_LARGE" DENSE_GDELTA_IMP_LARGE
  "|- forall s. gdelta s /\\ (:real^N) SUBSET closure s ==> s =_c (:real)"
#eval thmCheck "topology.ml NOT_GDELTA_DENSE_COUNTABLE" NOT_GDELTA_DENSE_COUNTABLE
  "|- forall s. COUNTABLE s /\\ closure s = (:real^N) ==> ~gdelta s"
#eval thmCheck "topology.ml PARACOMPACT_SPACE_EUCLIDEAN" PARACOMPACT_SPACE_EUCLIDEAN
  "|- paracompact_space euclidean"
