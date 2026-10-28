/- File: HolTest/MetricTest.lean
Runtime test suite: Multivariate/metric.ml (HolMultiLib/Metric.lean, wired by
SessionMultiLib/Metric.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/metric.ml"`, then `string_of_thm`).  The whole file is
also compared with HOL Light by tools/metricdiff: all 2,600 theorems and
definitions structurally and by their printed forms.

The theorems chosen here print without invented type variables, so their
printed forms do not depend on type-variable numbering.  They are spread over
the whole file, from the topology basics at the start to the Kuratowski
theorems at the end.

Loading metric.ml (`ensureMetric`) builds every bundle in file order; a proof
that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Metric

open HolCore.Kernel Session SessionMultiLib.Metric
open HolTest.CommonTest HolLight.Syntax

#eval ensureMetric

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/-- Run a derived rule; compare the theorem, or `FAIL msg`. -/
private unsafe def ruleCheck (lbl : String) (r : ExceptT String IO thm) (expected : String) :
    IO Unit := do
  let got ← match ← r.run with
    | Except.ok th => pure (squash (← HolCore.Printer.string_of_thm th))
    | Except.error e => pure s!"FAIL {e}"
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

private def tm (s : String) : ExceptT String IO term := ExceptT.mk (HolCore.Parser.parse_term s)

/- ---------------------------------------------------------------------- -/
/- Theorem statements (metric.ml), as HOL Light prints them.               -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "metric.ml topology_tybij_th" topology_tybij_th
  "|- exists t. istopology t"
#eval thmCheck "metric.ml TOPSPACE_SUBTOPOLOGY_IS_SUBSET" TOPSPACE_SUBTOPOLOGY_IS_SUBSET
  "|- forall top s. topspace (subtopology top s) SUBSET s"
#eval thmCheck "metric.ml DERIVED_SET_OF_MONO" DERIVED_SET_OF_MONO
  "|- forall top s t. s SUBSET t ==> top derived_set_of s SUBSET top derived_set_of t"
#eval thmCheck "metric.ml CLOSURE_OF_EQ_UNIV" CLOSURE_OF_EQ_UNIV
  "|- forall top s. top closure_of s = topspace top <=> top interior_of (topspace top DIFF s) = {}"
#eval thmCheck "metric.ml OPEN_MAP_EQ" OPEN_MAP_EQ
  "|- forall top top' f g. (forall x. x IN topspace top ==> f x = g x) /\\ open_map (top,top') f ==> open_map (top,top') g"
#eval thmCheck "metric.ml SUBTOPOLOGY_CROSS" SUBTOPOLOGY_CROSS
  "|- forall top1 top2 s t. subtopology (prod_topology top1 top2) (s CROSS t) = prod_topology (subtopology top1 s) (subtopology top2 t)"
#eval thmCheck "metric.ml HOMEOMORPHIC_MAP_ID" HOMEOMORPHIC_MAP_ID
  "|- forall top top'. homeomorphic_map (top,top') (\\x. x) <=> top' = top"
#eval thmCheck "metric.ml embedding_map" embedding_map
  "|- forall top' top f. embedding_map (top,top') f <=> homeomorphic_map (top,subtopology top' (IMAGE f (topspace top))) f"
#eval thmCheck "metric.ml RETRACT_OF_SPACE_TOPSPACE" RETRACT_OF_SPACE_TOPSPACE
  "|- forall top. topspace top retract_of_space top"
#eval thmCheck "metric.ml COMPACT_IN_CROSS" COMPACT_IN_CROSS
  "|- forall top1 top2 s t. compact_in (prod_topology top1 top2) (s CROSS t) <=> s = {} \\/ t = {} \\/ compact_in top1 s /\\ compact_in top2 t"
#eval thmCheck "metric.ml HOMEOMORPHIC_KC_SPACE" HOMEOMORPHIC_KC_SPACE
  "|- forall top top'. top homeomorphic_space top' ==> (kc_space top <=> kc_space top')"
#eval thmCheck "metric.ml NETLIMITS_WITHIN" NETLIMITS_WITHIN
  "|- forall n s. netlimits (n within s) = netlimits n"
#eval thmCheck "metric.ml OPEN_IMP_GDELTA_IN" OPEN_IMP_GDELTA_IN
  "|- forall top s. open_in top s ==> gdelta_in top s"
#eval thmCheck "metric.ml MBALL_EQ_EMPTY" MBALL_EQ_EMPTY
  "|- forall m x r. mball m (x,r) = {} <=> ~(x IN mspace m) \\/ r <= &0"
#eval thmCheck "metric.ml MDIST_TRIANGLE" MDIST_TRIANGLE
  "|- forall m x y z. x IN mspace m /\\ y IN mspace m /\\ z IN mspace m ==> mdist m (x,z) <= mdist m (x,y) + mdist m (y,z)"
#eval thmCheck "metric.ml METRIZABLE_IMP_FIRST_COUNTABLE" METRIZABLE_IMP_FIRST_COUNTABLE
  "|- forall top. metrizable_space top ==> first_countable top"
#eval thmCheck "metric.ml CONNECTED_SPACE_SEPARATED_BETWEEN" CONNECTED_SPACE_SEPARATED_BETWEEN
  "|- forall top. connected_space top <=> (forall s t. separated_between top s t ==> s = {} \\/ t = {})"
#eval thmCheck "metric.ml LOCALLY_COMPACT_SPACE_DISCRETE_TOPOLOGY"
  LOCALLY_COMPACT_SPACE_DISCRETE_TOPOLOGY
  "|- forall u. locally_compact_space (discrete_topology u)"
#eval thmCheck "metric.ml KC_SPACE_EUCLIDEANREAL" KC_SPACE_EUCLIDEANREAL
  "|- kc_space euclideanreal"
#eval thmCheck "metric.ml REAL_COMPACT_CONTAINS_SUP" REAL_COMPACT_CONTAINS_SUP
  "|- forall s. real_compact s /\\ ~(s = {}) ==> sup s IN s"
#eval thmCheck "metric.ml TOTALLY_BOUNDED_IN_SING" TOTALLY_BOUNDED_IN_SING
  "|- forall m x. totally_bounded_in m {x} <=> x IN mspace m"
#eval thmCheck "metric.ml tendsto_real_def" tendsto_real_def
  "|- forall f l net. (f ---> l) net <=> limit euclideanreal f l net"
#eval thmCheck "metric.ml PATH_START_IN_TOPSPACE" PATH_START_IN_TOPSPACE
  "|- forall top g. path_in top g ==> g (&0) IN topspace top"
#eval thmCheck "metric.ml COMPLETELY_REGULAR_IMP_REGULAR_SPACE"
  COMPLETELY_REGULAR_IMP_REGULAR_SPACE
  "|- forall top. completely_regular_space top ==> regular_space top"
#eval thmCheck "metric.ml CONTRACTIBLE_IMP_PATH_CONNECTED_SPACE"
  CONTRACTIBLE_IMP_PATH_CONNECTED_SPACE
  "|- forall top. contractible_space top ==> path_connected_space top"
#eval thmCheck "metric.ml UNIFORMLY_CONTINUOUS_MAP_CONST" UNIFORMLY_CONTINUOUS_MAP_CONST
  "|- forall m1 m2 c. uniformly_continuous_map (m1,m2) (\\x. c) <=> mspace m1 = {} \\/ c IN mspace m2"
#eval thmCheck "metric.ml FCCOVERABLE_SPACE_IMP_LOCALLY_CONNECTED_SPACE"
  FCCOVERABLE_SPACE_IMP_LOCALLY_CONNECTED_SPACE
  "|- forall m. fccoverable_space m ==> locally_connected_space (mtopology m)"
#eval thmCheck "metric.ml SUBTOPOLOGY_NSPHERE_EQUATOR" SUBTOPOLOGY_NSPHERE_EQUATOR
  "|- forall n. subtopology (nsphere (n + 1)) {x | x (n + 2) = &0} = nsphere n"
#eval thmCheck "metric.ml REGULAR_LINDELOF_IMP_PARACOMPACT_SPACE"
  REGULAR_LINDELOF_IMP_PARACOMPACT_SPACE
  "|- forall top. regular_space top /\\ lindelof_space top ==> paracompact_space top"
#eval thmCheck "metric.ml PARACOMPACT_SPACE_DISCRETE_TOPOLOGY"
  PARACOMPACT_SPACE_DISCRETE_TOPOLOGY
  "|- forall u. paracompact_space (discrete_topology u)"
#eval thmCheck "metric.ml DIMENSION_LE_EQ_EMPTY" DIMENSION_LE_EQ_EMPTY
  "|- forall top. top dimension_le -- &1 <=> topspace top = {}"
#eval thmCheck "metric.ml cantor_set" cantor_set
  "|- cantor_set = IMAGE cantor_map (:num->bool)"
#eval thmCheck "metric.ml TOPSPACE_CANTOR_SPACE" TOPSPACE_CANTOR_SPACE
  "|- topspace cantor_space = (:num->bool)"
#eval thmCheck "metric.ml ZERO_DIMENSIONAL_CANTOR_SPACE" ZERO_DIMENSIONAL_CANTOR_SPACE
  "|- cantor_space dimension_le &0"
#eval thmCheck "metric.ml SUM_TWOTHIRDS" SUM_TWOTHIRDS
  "|- forall n. sum (0..n) (\\k. &2 / &3 pow (k + 1)) = &1 - (&1 / &3) pow (n + 1)"
#eval thmCheck "metric.ml CANTOR_MAP_POS" CANTOR_MAP_POS
  "|- forall a. &0 <= cantor_map a"
#eval thmCheck "metric.ml CANTOR_MAP_INJECTIVE" CANTOR_MAP_INJECTIVE
  "|- forall a b. cantor_map a = cantor_map b <=> a = b"
#eval thmCheck "metric.ml HAHN_MAZURKIEWICZ" HAHN_MAZURKIEWICZ
  "|- forall top. hausdorff_space top ==> ((exists f. continuous_map (subtopology euclideanreal (real_interval [&0,&1]),top) f /\\ IMAGE f (real_interval [&0,&1]) = topspace top) <=> compact_space top /\\ connected_space top /\\ locally_connected_space top /\\ metrizable_space top /\\ ~(topspace top = {}))"
#eval thmCheck "metric.ml MCOMPLETE_CONNECTED_LOCALLY_CONNECTED_IMP_PATH_CONNECTED"
  MCOMPLETE_CONNECTED_LOCALLY_CONNECTED_IMP_PATH_CONNECTED
  "|- forall m. mcomplete m /\\ connected_space (mtopology m) /\\ locally_connected_space (mtopology m) ==> path_connected_space (mtopology m)"
#eval thmCheck "metric.ml SEPARATION_BY_CLOSED_INTERMEDIATES_GEN"
  SEPARATION_BY_CLOSED_INTERMEDIATES_GEN
  "|- forall top s. hereditarily normal_space top /\\ ~connected_in top (topspace top DIFF s) ==> (exists c. closed_in top c /\\ c SUBSET s /\\ (forall d. closed_in top d /\\ c SUBSET d /\\ d SUBSET s ==> ~connected_in top (topspace top DIFF d)))"

/- ---------------------------------------------------------------------- -/
/- METRIC_ARITH (metric.ml 12333-12631) proves its goal as stated.         -/
/- ---------------------------------------------------------------------- -/
#eval ruleCheck "metric.ml METRIC_ARITH triangle"
  (do METRIC_ARITH (← tm "!m x y z:A. x IN mspace m /\\ y IN mspace m /\\ z IN mspace m ==> mdist m (x,z) <= mdist m (x,y) + mdist m (y,z)"))
  "|- forall m x y z. x IN mspace m /\\ y IN mspace m /\\ z IN mspace m ==> mdist m (x,z) <= mdist m (x,y) + mdist m (y,z)"
