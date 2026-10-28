/- File: HolTest/SpecialTopologiesTest.lean
Runtime test suite: Multivariate/specialtopologies.ml
(HolMultiLib/SpecialTopologies.lean, wired by
SessionMultiLib/SpecialTopologies.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/specialtopologies.ml"`, then `string_of_thm`).  The
whole file is also compared with HOL Light by tools/stdiff: all 48 theorems
structurally and by their printed forms.

The theorems chosen here cover the three topologies the file defines: the
indiscrete, cofinite and cocountable topologies.

Loading specialtopologies.ml (`ensureSpecialTopologies`) builds every bundle in
file order; a proof that failed would stop the load, which the `make verify`
gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.SpecialTopologies

open HolCore.Kernel Session SessionMultiLib.SpecialTopologies
open HolTest.CommonTest HolLight.Syntax

#eval ensureSpecialTopologies

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- Theorem statements (specialtopologies.ml), as HOL Light prints them.    -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "specialtopologies.ml indiscrete_topology" indiscrete_topology
  "|- forall u. indiscrete_topology u = topology {{}, u}"
#eval thmCheck "specialtopologies.ml OPEN_IN_INDISCRETE_TOPOLOGY" OPEN_IN_INDISCRETE_TOPOLOGY
  "|- forall u s. open_in (indiscrete_topology u) s <=> s = {} \\/ s = u"
#eval thmCheck "specialtopologies.ml SUBTOPOLOGY_INDISCRETE_TOPOLOGY"
  SUBTOPOLOGY_INDISCRETE_TOPOLOGY
  "|- forall u s. subtopology (indiscrete_topology u) s = indiscrete_topology (u INTER s)"
#eval thmCheck "specialtopologies.ml COMPACT_IN_INDISCRETE_TOPOLOGY"
  COMPACT_IN_INDISCRETE_TOPOLOGY
  "|- forall u s. compact_in (indiscrete_topology u) s <=> s SUBSET u"
#eval thmCheck "specialtopologies.ml T0_SPACE_INDISCRETE_TOPOLOGY" T0_SPACE_INDISCRETE_TOPOLOGY
  "|- forall u. t0_space (indiscrete_topology u) <=> (exists a. u SUBSET {a})"
#eval thmCheck "specialtopologies.ml NORMAL_SPACE_INDISCRETE_TOPOLOGY"
  NORMAL_SPACE_INDISCRETE_TOPOLOGY
  "|- forall u. normal_space (indiscrete_topology u)"
#eval thmCheck "specialtopologies.ml DERIVED_SET_OF_INDISCRETE_TOPOLOGY"
  DERIVED_SET_OF_INDISCRETE_TOPOLOGY
  "|- forall u s. indiscrete_topology u derived_set_of s =
      (if exists a. u INTER s SUBSET {a} then if DISJOINT u s then {} else u DIFF s else u)"
#eval thmCheck "specialtopologies.ml PERFECT_SET_INDISCRETE_TOPOLOGY"
  PERFECT_SET_INDISCRETE_TOPOLOGY
  "|- forall u s. indiscrete_topology u derived_set_of s = s <=>
      s = {} \\/ s = u /\\ ~(exists a. u SUBSET {a})"
#eval thmCheck "specialtopologies.ml CONTINUOUS_MAP_FROM_INDISCRETE_TOPOLOGY"
  CONTINUOUS_MAP_FROM_INDISCRETE_TOPOLOGY
  "|- forall top u f. t1_space top ==> (continuous_map (indiscrete_topology u,top) f <=>
      u = {} \\/ (exists a. a IN topspace top /\\ (forall x. x IN u ==> f x = a)))"
#eval thmCheck "specialtopologies.ml PATH_CONNECTED_SPACE_INDISCRETE_TOPOLOGY"
  PATH_CONNECTED_SPACE_INDISCRETE_TOPOLOGY
  "|- forall u. path_connected_space (indiscrete_topology u)"
#eval thmCheck "specialtopologies.ml NEIGHBOURHOOD_BASE_OF_INDISCRETE_TOPOLOGY"
  NEIGHBOURHOOD_BASE_OF_INDISCRETE_TOPOLOGY
  "|- forall P u. neighbourhood_base_of P (indiscrete_topology u) <=> u = {} \\/ P u"
#eval thmCheck "specialtopologies.ml cofinite_topology" cofinite_topology
  "|- forall u. cofinite_topology u = topology ({} INSERT {s | s SUBSET u /\\ FINITE (u DIFF s)})"
#eval thmCheck "specialtopologies.ml CLOSED_IN_COFINITE_TOPOLOGY" CLOSED_IN_COFINITE_TOPOLOGY
  "|- forall u s. closed_in (cofinite_topology u) s <=> s = u \\/ s SUBSET u /\\ FINITE s"
#eval thmCheck "specialtopologies.ml T1_SPACE_COFINITE_TOPOLOGY_MINIMAL"
  T1_SPACE_COFINITE_TOPOLOGY_MINIMAL
  "|- forall top s. t1_space top /\\ closed_in (cofinite_topology (topspace top)) s
      ==> closed_in top s"
#eval thmCheck "specialtopologies.ml CONNECTED_SPACE_COFINITE_TOPOLOGY"
  CONNECTED_SPACE_COFINITE_TOPOLOGY
  "|- forall u. connected_space (cofinite_topology u) <=> (exists a. u SUBSET {a}) \\/ INFINITE u"
#eval thmCheck "specialtopologies.ml COMPACT_IN_COFINITE_TOPOLOGY" COMPACT_IN_COFINITE_TOPOLOGY
  "|- forall u s. compact_in (cofinite_topology u) s <=> s SUBSET u"
#eval thmCheck "specialtopologies.ml HAUSDORFF_SPACE_COFINITE_TOPOLOGY"
  HAUSDORFF_SPACE_COFINITE_TOPOLOGY
  "|- forall u. hausdorff_space (cofinite_topology u) <=> FINITE u"
#eval thmCheck "specialtopologies.ml OPEN_IN_COCOUNTABLE_TOPOLOGY" OPEN_IN_COCOUNTABLE_TOPOLOGY
  "|- forall u s. open_in (cocountable_topology u) s <=>
      s = {} \\/ s SUBSET u /\\ COUNTABLE (u DIFF s)"
#eval thmCheck "specialtopologies.ml COCOUNTABLE_EQ_DISCRETE_TOPOLOGY"
  COCOUNTABLE_EQ_DISCRETE_TOPOLOGY
  "|- forall u. COUNTABLE u ==> cocountable_topology u = discrete_topology u"
#eval thmCheck "specialtopologies.ml CONNECTED_IN_COCOUNTABLE_TOPOLOGY"
  CONNECTED_IN_COCOUNTABLE_TOPOLOGY
  "|- forall u s. ~COUNTABLE s /\\ s SUBSET u ==> connected_in (cocountable_topology u) s"
#eval thmCheck "specialtopologies.ml COMPACT_IN_COCOUNTABLE_TOPOLOGY"
  COMPACT_IN_COCOUNTABLE_TOPOLOGY
  "|- forall u s. compact_in (cocountable_topology u) s <=> s SUBSET u /\\ FINITE s"
#eval thmCheck "specialtopologies.ml COMPACT_SPACE_COCOUNTABLE_TOPOLOGY"
  COMPACT_SPACE_COCOUNTABLE_TOPOLOGY
  "|- forall u. compact_space (cocountable_topology u) <=> FINITE u"
#eval thmCheck "specialtopologies.ml HAUSDORFF_SPACE_SUBTOPOLOGY_COCOUNTABLE_TOPOLOGY"
  HAUSDORFF_SPACE_SUBTOPOLOGY_COCOUNTABLE_TOPOLOGY
  "|- forall u s. hausdorff_space (subtopology (cocountable_topology u) s) <=>
      COUNTABLE (u INTER s)"
#eval thmCheck "specialtopologies.ml KC_SPACE_COCOUNTABLE_TOPOLOGY"
  KC_SPACE_COCOUNTABLE_TOPOLOGY
  "|- forall u. kc_space (cocountable_topology u)"
