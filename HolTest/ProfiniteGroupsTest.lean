/- File: HolTest/ProfiniteGroupsTest.lean
Runtime test suite: Multivariate/profinite_groups.ml
(HolMultiLib/ProfiniteGroups.lean, wired by SessionMultiLib/ProfiniteGroups.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/profinite_groups.ml"`, then `string_of_thm`).  The whole file is also
compared with HOL Light by tools/pgdiff: all exported theorems structurally
and by their printed forms.  The 20 theorems here are spread evenly over the
file; theorems that print with `?nnn` invented type variables are left out.

Loading profinite_groups.ml (`ensureProfiniteGroups`) builds every bundle in file order; a proof
that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.ProfiniteGroups

open HolCore.Kernel Session SessionMultiLib.ProfiniteGroups
open HolTest.CommonTest HolLight.Syntax

#eval ensureProfiniteGroups

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

#eval thmCheck "profinite_groups.ml CONTINUOUS_MAP_GROUP_MUL" CONTINUOUS_MAP_GROUP_MUL
  "|- forall G top top' f g.        topological_group G top /\\        continuous_map (top',top) f /\\        continuous_map (top',top) g        ==> continuous_map (top',top) (\\x. group_mul G (f x) (g x))"
#eval thmCheck "profinite_groups.ml OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES" OPEN_IN_TOPOLOGICAL_GROUP_TRANSLATES
  "|- forall G top a u.        topological_group G top /\\ a IN group_carrier G /\\ open_in top u        ==> open_in top (left_coset G a u) /\\            open_in top (right_coset G u a) /\\            open_in top (IMAGE (group_inv G) u)"
#eval thmCheck "profinite_groups.ml OPEN_IN_CLOSED_SUBGROUP_FINITE_INDEX" OPEN_IN_CLOSED_SUBGROUP_FINITE_INDEX
  "|- forall G top h.        topological_group G top /\\        h subgroup_of G /\\        closed_in top h /\\        FINITE (group_cosets G h)        ==> open_in top h"
#eval thmCheck "profinite_groups.ml NORMAL_SUBGROUP_OF_CLOSURE_OF" NORMAL_SUBGROUP_OF_CLOSURE_OF
  "|- forall G top h.        topological_group G top /\\ h normal_subgroup_of G        ==> top closure_of h normal_subgroup_of G"
#eval thmCheck "profinite_groups.ml TOPOLOGICAL_GROUP_HOMEOMORPHIC_ISOMORPHISM" TOPOLOGICAL_GROUP_HOMEOMORPHIC_ISOMORPHISM
  "|- forall G H top top' f.        topological_group H top' /\\        topspace top = group_carrier G /\\        group_isomorphism (G,H) f /\\        homeomorphic_map (top,top') f        ==> topological_group G top"
#eval thmCheck "profinite_groups.ml CLOSED_IN_GROUP_KERNEL" CLOSED_IN_GROUP_KERNEL
  "|- forall G H top top' f.        topological_group G top /\\        topological_group H top' /\\        hausdorff_space top' /\\        group_homomorphism (G,H) f /\\        continuous_map (top,top') f        ==> closed_in top (group_kernel (G,H) f)"
#eval thmCheck "profinite_groups.ml OPEN_MAP_RIGHT_COSET" OPEN_MAP_RIGHT_COSET
  "|- forall G top n.        topological_group G top /\\ n normal_subgroup_of G        ==> open_map (top,quotient_topology (top,right_coset G n))            (right_coset G n)"
#eval thmCheck "profinite_groups.ml OPEN_NORMAL_SUBGROUP_QUOTIENT_IMAGE" OPEN_NORMAL_SUBGROUP_QUOTIENT_IMAGE
  "|- forall G top N U.        topological_group G top /\\        N normal_subgroup_of G /\\        U normal_subgroup_of G /\\        open_in top U /\\        N SUBSET U        ==> IMAGE (right_coset G N) U normal_subgroup_of quotient_group G N /\\            open_in (quotient_topology (top,right_coset G N))            (IMAGE (right_coset G N) U) /\\            quotient_group G U isomorphic_group            quotient_group (quotient_group G N) (IMAGE (right_coset G N) U)"
#eval thmCheck "profinite_groups.ml TOPOLOGICAL_GROUP_PRODUCT_GROUP" TOPOLOGICAL_GROUP_PRODUCT_GROUP
  "|- forall k G top.        (forall i. i IN k ==> topological_group (G i) (top i))        ==> topological_group (product_group k G) (product_topology k top)"
#eval thmCheck "profinite_groups.ml PROFINITE_GROUP_COSET_NEIGHBOURHOOD" PROFINITE_GROUP_COSET_NEIGHBOURHOOD
  "|- forall G top w x.        profinite_group G top /\\ open_in top w /\\ x IN w        ==> (exists u.                 u normal_subgroup_of G /\\                 open_in top u /\\                 right_coset G u x SUBSET w)"
#eval thmCheck "profinite_groups.ml OPEN_IN_COMPACT_TOPOLOGICAL_GROUP_SUBGROUP" OPEN_IN_COMPACT_TOPOLOGICAL_GROUP_SUBGROUP
  "|- forall G top h.        topological_group G top /\\ compact_space top /\\ h subgroup_of G        ==> (open_in top h <=> closed_in top h /\\ FINITE (group_cosets G h))"
#eval thmCheck "profinite_groups.ml PROFINITE_GROUP_HOMEOMORPHIC_ISOMORPHISM" PROFINITE_GROUP_HOMEOMORPHIC_ISOMORPHISM
  "|- forall G H top top' f.        profinite_group H top' /\\        topspace top = group_carrier G /\\        group_isomorphism (G,H) f /\\        homeomorphic_map (top,top') f        ==> profinite_group G top"
#eval thmCheck "profinite_groups.ml PROFINITE_GROUP_QUOTIENT_GROUP" PROFINITE_GROUP_QUOTIENT_GROUP
  "|- forall G top n.        profinite_group G top /\\ n normal_subgroup_of G /\\ closed_in top n        ==> profinite_group (quotient_group G n)            (quotient_topology (top,right_coset G n))"
#eval thmCheck "profinite_groups.ml PROFINITE_GROUP_OPEN_SUBGROUPS" PROFINITE_GROUP_OPEN_SUBGROUPS
  "|- forall G top.        profinite_group G top <=>        topological_group G top /\\        compact_space top /\\        hausdorff_space top /\\        (forall w.             open_in top w /\\ group_id G IN w             ==> (exists h. h subgroup_of G /\\ open_in top h /\\ h SUBSET w))"
#eval thmCheck "profinite_groups.ml PROFINITE_GROUP_CLOSED_SUBGROUP_INTERS" PROFINITE_GROUP_CLOSED_SUBGROUP_INTERS
  "|- forall G top h.        profinite_group G top /\\ h subgroup_of G /\\ closed_in top h        ==> INTERS {u | u subgroup_of G /\\ open_in top u /\\ h SUBSET u} = h"
#eval thmCheck "profinite_groups.ml PROFINITE_GROUP_INVERSE_LIMIT" PROFINITE_GROUP_INVERSE_LIMIT
  "|- forall k le G f top.        (forall i. i IN k ==> profinite_group (G i) (top i)) /\\        (forall i j.             i IN k /\\ j IN k /\\ le i j             ==> group_homomorphism (G j,G i) (f i j) /\\                 continuous_map (top j,top i) (f i j))        ==> profinite_group (inverse_limit_group k le G f)            (subtopology (product_topology k top)            (group_carrier (inverse_limit_group k le G f)))"
#eval thmCheck "profinite_groups.ml TOPOLOGICAL_GROUP_POINTWISE_TOPOLOGY" TOPOLOGICAL_GROUP_POINTWISE_TOPOLOGY
  "|- forall X G.        G subgroup_of symmetric_group X        ==> topological_group (subgroup_generated (symmetric_group X) G)            (pointwise_topology G)"
#eval thmCheck "profinite_groups.ml CLOSED_IN_POINTWISE_STABILIZER" CLOSED_IN_POINTWISE_STABILIZER
  "|- forall G k.        closed_in (pointwise_topology G)        {g | g IN G /\\ (forall x. x IN k ==> g x = x)}"
#eval thmCheck "profinite_groups.ml OPEN_IN_POINTWISE_TOPOLOGY_SUBGROUP" OPEN_IN_POINTWISE_TOPOLOGY_SUBGROUP
  "|- forall X G h.        G subgroup_of symmetric_group X /\\        h subgroup_of subgroup_generated (symmetric_group X) G        ==> (open_in (pointwise_topology G) h <=>             (exists k.                  FINITE k /\\                  k SUBSET X /\\                  {g | g IN G /\\ (forall x. x IN k ==> g x = x)} SUBSET h))"
#eval thmCheck "profinite_groups.ml PROFINITE_GROUP_POINTWISE_TOPOLOGY" PROFINITE_GROUP_POINTWISE_TOPOLOGY
  "|- forall X G.        G subgroup_of symmetric_group X /\\        (forall x. x IN X ==> FINITE {g x | g IN G}) /\\        closed_in (product_topology (:A) (\\x. discrete_topology (:A))) G        ==> profinite_group (subgroup_generated (symmetric_group X) G)            (pointwise_topology G)"
