/- File: HolTest/InfiniteGaloisTest.lean
Runtime test suite: Multivariate/infinite_galois.ml
(HolMultiLib/InfiniteGalois.lean, wired by SessionMultiLib/InfiniteGalois.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/infinite_galois.ml"`, then `string_of_thm`).  The whole file is also
compared with HOL Light by tools/igdiff: all exported theorems structurally
and by their printed forms.  The 20 theorems here are spread evenly over the
file; theorems that print with `?nnn` invented type variables are left out.

Loading infinite_galois.ml (`ensureInfiniteGalois`) builds every bundle in file order; a proof
that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.InfiniteGalois

open HolCore.Kernel Session SessionMultiLib.InfiniteGalois
open HolTest.CommonTest HolLight.Syntax

#eval ensureInfiniteGalois

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

#eval thmCheck "infinite_galois.ml TOPOLOGICAL_GROUP_GALOIS_GROUP" TOPOLOGICAL_GROUP_GALOIS_GROUP
  "|- forall h k l.        topological_group (galois_group (k,l) h)        (pointwise_topology (group_carrier (galois_group (k,l) h)))"
#eval thmCheck "infinite_galois.ml PROFINITE_GROUP_GALOIS_GROUP" PROFINITE_GROUP_GALOIS_GROUP
  "|- forall h k l.        algebraic_extension (k,l) h        ==> profinite_group (galois_group (k,l) h)            (pointwise_topology (group_carrier (galois_group (k,l) h)))"
#eval thmCheck "infinite_galois.ml OPEN_IN_GALOIS_GROUP_SUBGROUP" OPEN_IN_GALOIS_GROUP_SUBGROUP
  "|- forall h k l H.        H subgroup_of galois_group (k,l) h        ==> (open_in             (pointwise_topology (group_carrier (galois_group (k,l) h)))             H <=>             (exists s.                  FINITE s /\\                  s SUBSET ring_carrier l /\\                  {f | f IN group_carrier (galois_group (k,l) h) /\\                       (forall x. x IN s ==> f x = x)} SUBSET                  H))"
#eval thmCheck "infinite_galois.ml CLOSED_IN_GALOIS_GROUP_INTERMEDIATE" CLOSED_IN_GALOIS_GROUP_INTERMEDIATE
  "|- forall h k l s.        s subfield_of l /\\ IMAGE h (ring_carrier k) SUBSET s        ==> closed_in            (pointwise_topology (group_carrier (galois_group (k,l) h)))            (group_carrier (galois_group (subfield_generated l s,l) I))"
#eval thmCheck "infinite_galois.ml POINTWISE_TOPOLOGY_GALOIS_GROUP_FINITE" POINTWISE_TOPOLOGY_GALOIS_GROUP_FINITE
  "|- forall h k l.        finite_extension (k,l) h        ==> pointwise_topology (group_carrier (galois_group (k,l) h)) =            discrete_topology (group_carrier (galois_group (k,l) h))"
#eval thmCheck "infinite_galois.ml GALOIS_GROUP_NEIGHBOURHOOD_BASE" GALOIS_GROUP_NEIGHBOURHOOD_BASE
  "|- forall h k l w.        galois_extension (k,l) h /\\        open_in (pointwise_topology (group_carrier (galois_group (k,l) h))) w /\\        I IN w        ==> (exists e.                 e IN finite_galois_subfields (k,l) h /\\                 group_carrier (galois_group (subfield_generated l e,l) I) SUBSET                 w)"
#eval thmCheck "infinite_galois.ml CLOSURE_OF_GALOIS_GROUP_SUBGROUP_GALOIS" CLOSURE_OF_GALOIS_GROUP_SUBGROUP_GALOIS
  "|- forall h k l H.        galois_extension (k,l) h /\\ H subgroup_of galois_group (k,l) h        ==> pointwise_topology (group_carrier (galois_group (k,l) h)) closure_of            H =            group_carrier            (galois_group (subfield_generated l (fixed_field l H),l) I)"
#eval thmCheck "infinite_galois.ml CLOSURE_OF_GALOIS_GROUP_SUBGROUP" CLOSURE_OF_GALOIS_GROUP_SUBGROUP
  "|- forall h k l H.        algebraic_extension (k,l) h /\\ H subgroup_of galois_group (k,l) h        ==> pointwise_topology (group_carrier (galois_group (k,l) h)) closure_of            H =            group_carrier            (galois_group (subfield_generated l (fixed_field l H),l) I)"
#eval thmCheck "infinite_galois.ml CLOSED_IN_GALOIS_GROUP_SUBGROUP" CLOSED_IN_GALOIS_GROUP_SUBGROUP
  "|- forall h k l H.        algebraic_extension (k,l) h /\\ H subgroup_of galois_group (k,l) h        ==> (closed_in             (pointwise_topology (group_carrier (galois_group (k,l) h)))             H <=>             group_carrier             (galois_group (subfield_generated l (fixed_field l H),l) I) =             H)"
#eval thmCheck "infinite_galois.ml INFINITE_GALOIS_CORRESPONDENCE" INFINITE_GALOIS_CORRESPONDENCE
  "|- forall h k l.        galois_extension (k,l) h        ==> (forall H.                 H subgroup_of galois_group (k,l) h /\\                 closed_in                 (pointwise_topology (group_carrier (galois_group (k,l) h)))                 H                 ==> fixed_field l H subfield_of l /\\                     IMAGE h (ring_carrier k) SUBSET fixed_field l H /\\                     group_carrier                     (galois_group (subfield_generated l (fixed_field l H),l)                     I) =                     H) /\\            (forall s.                 s subfield_of l /\\ IMAGE h (ring_carrier k) SUBSET s                 ==> group_carrier (galois_group (subfield_generated l s,l) I) subgroup_of                     galois_group (k,l) h /\\                     closed_in                     (pointwise_topology                     (group_carrier (galois_group (k,l) h)))                     (group_carrier                     (galois_group (subfield_generated l s,l) I)) /\\                     fixed_field l                     (group_carrier                     (galois_group (subfield_generated l s,l) I)) =                     s)"
#eval thmCheck "infinite_galois.ml OPEN_IN_GALOIS_GROUP_INTERMEDIATE" OPEN_IN_GALOIS_GROUP_INTERMEDIATE
  "|- forall h k l s.        galois_extension (k,l) h /\\        s subfield_of l /\\        IMAGE h (ring_carrier k) SUBSET s        ==> (open_in             (pointwise_topology (group_carrier (galois_group (k,l) h)))             (group_carrier (galois_group (subfield_generated l s,l) I)) <=>             finite_extension (k,subfield_generated l s) h)"
#eval thmCheck "infinite_galois.ml INFINITE_GALOIS_CORRESPONDENCE_NORMAL" INFINITE_GALOIS_CORRESPONDENCE_NORMAL
  "|- forall h k l H.        galois_extension (k,l) h /\\        H subgroup_of galois_group (k,l) h /\\        closed_in (pointwise_topology (group_carrier (galois_group (k,l) h)))        H        ==> (H normal_subgroup_of galois_group (k,l) h <=>             galois_extension (k,subfield_generated l (fixed_field l H)) h)"
#eval thmCheck "infinite_galois.ml GALOIS_GROUP_INTER_CLOSURE" GALOIS_GROUP_INTER_CLOSURE
  "|- forall h k l s t.        galois_extension (k,l) h /\\        s subfield_of l /\\        t subfield_of l /\\        IMAGE h (ring_carrier k) SUBSET s /\\        IMAGE h (ring_carrier k) SUBSET t        ==> group_carrier            (galois_group (subfield_generated l (s INTER t),l) I) =            pointwise_topology (group_carrier (galois_group (k,l) h)) closure_of            group_carrier            (subgroup_generated (galois_group (k,l) h)            (group_carrier (galois_group (subfield_generated l s,l) I) UNION             group_carrier (galois_group (subfield_generated l t,l) I)))"
#eval thmCheck "infinite_galois.ml FIXED_FIELD_INTER_CLOSED" FIXED_FIELD_INTER_CLOSED
  "|- forall h k l G H.        galois_extension (k,l) h /\\        G subgroup_of galois_group (k,l) h /\\        closed_in (pointwise_topology (group_carrier (galois_group (k,l) h)))        G /\\        H subgroup_of galois_group (k,l) h /\\        closed_in (pointwise_topology (group_carrier (galois_group (k,l) h)))        H        ==> fixed_field l (G INTER H) =            ring_carrier            (subfield_generated l (fixed_field l G UNION fixed_field l H))"
#eval thmCheck "infinite_galois.ml GALOIS_GROUP_RESTRICTION_QUOTIENT_MAP" GALOIS_GROUP_RESTRICTION_QUOTIENT_MAP
  "|- forall h k l s.        normal_extension (k,l) h /\\        s subfield_of l /\\        normal_extension (k,subfield_generated l s) h        ==> open_map            (pointwise_topology (group_carrier (galois_group (k,l) h)),             pointwise_topology             (group_carrier (galois_group (k,subfield_generated l s) h)))            (\\f x. if x IN s then f x else x) /\\            quotient_map            (pointwise_topology (group_carrier (galois_group (k,l) h)),             pointwise_topology             (group_carrier (galois_group (k,subfield_generated l s) h)))            (\\f x. if x IN s then f x else x)"
#eval thmCheck "infinite_galois.ml CONTINUOUS_MAP_GALOIS_GROUP_RESTRICTION_FINITE" CONTINUOUS_MAP_GALOIS_GROUP_RESTRICTION_FINITE
  "|- forall h k l e.        field_extension (k,l) h /\\ e IN finite_galois_subfields (k,l) h        ==> continuous_map            (pointwise_topology (group_carrier (galois_group (k,l) h)),             discrete_topology             (group_carrier (galois_group (k,subfield_generated l e) h)))            (\\f x. if x IN e then f x else x)"
#eval thmCheck "infinite_galois.ml GALOIS_GROUP_RESTRICTION_FINITE_GALOIS" GALOIS_GROUP_RESTRICTION_FINITE_GALOIS
  "|- forall h k l e.        galois_extension (k,l) h /\\ e IN finite_galois_subfields (k,l) h        ==> group_epimorphism            (galois_group (k,l) h,galois_group (k,subfield_generated l e) h)            (\\f x. if x IN e then f x else x) /\\            continuous_map            (pointwise_topology (group_carrier (galois_group (k,l) h)),             discrete_topology             (group_carrier (galois_group (k,subfield_generated l e) h)))            (\\f x. if x IN e then f x else x) /\\            group_kernel            (galois_group (k,l) h,galois_group (k,subfield_generated l e) h)            (\\f x. if x IN e then f x else x) =            group_carrier (galois_group (subfield_generated l e,l) I) /\\            group_carrier (galois_group (subfield_generated l e,l) I) normal_subgroup_of            galois_group (k,l) h /\\            open_in            (pointwise_topology (group_carrier (galois_group (k,l) h)))            (group_carrier (galois_group (subfield_generated l e,l) I))"
#eval thmCheck "infinite_galois.ml INFINITE_GALOIS_CORRESPONDENCE_INDEX" INFINITE_GALOIS_CORRESPONDENCE_INDEX
  "|- forall h k l s.        galois_extension (k,l) h /\\        s subfield_of l /\\        IMAGE h (ring_carrier k) SUBSET s /\\        finite_extension (k,subfield_generated l s) h        ==> CARD            (group_cosets (galois_group (k,l) h)            (group_carrier (galois_group (subfield_generated l s,l) I))) =            extension_degree (k,subfield_generated l s) h"
#eval thmCheck "infinite_galois.ml GALOIS_GROUP_COMPATIBLE_RESTRICTIONS" GALOIS_GROUP_COMPATIBLE_RESTRICTIONS
  "|- forall h k l S.        normal_extension (k,l) h /\\        (forall e.             e IN finite_galois_subfields (k,l) h             ==> ~(S e = {}) /\\                 S e SUBSET                 group_carrier (galois_group (k,subfield_generated l e) h)) /\\        (forall e e'.             e IN finite_galois_subfields (k,l) h /\\             e' IN finite_galois_subfields (k,l) h /\\             e SUBSET e'             ==> IMAGE (\\f x. if x IN e then f x else x) (S e') SUBSET S e)        ==> (exists f.                 f IN group_carrier (galois_group (k,l) h) /\\                 (forall e.                      e IN finite_galois_subfields (k,l) h                      ==> (\\x. if x IN e then f x else x) IN S e))"
#eval thmCheck "infinite_galois.ml GALOIS_GROUP_INVERSE_LIMIT" GALOIS_GROUP_INVERSE_LIMIT
  "|- forall h k l.        galois_extension (k,l) h        ==> group_isomorphism            (galois_group (k,l) h,             inverse_limit_group (finite_galois_subfields (k,l) h) (SUBSET)             (\\e. galois_group (k,subfield_generated l e) h)             (\\e e' f x. if x IN e then f x else x))            (\\f.                 RESTRICTION (finite_galois_subfields (k,l) h)                 (\\e x. if x IN e then f x else x)) /\\            homeomorphic_map            (pointwise_topology (group_carrier (galois_group (k,l) h)),             subtopology             (product_topology (finite_galois_subfields (k,l) h)             (\\e.                  discrete_topology                  (group_carrier (galois_group (k,subfield_generated l e) h))))             (group_carrier             (inverse_limit_group (finite_galois_subfields (k,l) h) (SUBSET)              (\\e. galois_group (k,subfield_generated l e) h)             (\\e e' f x. if x IN e then f x else x))))            (\\f.                 RESTRICTION (finite_galois_subfields (k,l) h)                 (\\e x. if x IN e then f x else x))"
