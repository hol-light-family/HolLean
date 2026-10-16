/- File: HolTest/SymmetricGroupTest.lean
Runtime test suite: Library/symmetric_group.ml (HolLibrary/SymmetricGroup.lean, wired by
SessionLibrary/SymmetricGroup.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/symmetric_group.ml"`, then `string_of_thm`, newlines joined).
tools/symmetric_groupdiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.SymmetricGroup.ensureSymmetricGroup

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def check (lbl : String) (r : IO (Except String thm)) (expected : String) :
    IO Unit := do
  let got ← match ← r with
    | .ok th => pure (squash (← HolCore.Printer.string_of_thm th))
    | .error e => pure s!"FAIL {e}"
  if got == squash expected || got == expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

private unsafe def thm' (lbl : String) (th : thm) (expected : String) : IO Unit :=
  check lbl (pure (.ok th)) expected

namespace T
open Session SessionLibrary.SymmetricGroup HolLight.Syntax

#eval thm' "symmetric_group" symmetric_group
  "|- forall s. symmetric_group s = group ({p | p permutes s},I,inverse,(o))"
#eval thm' "FINITE_SYMMETRIC_GROUP" FINITE_SYMMETRIC_GROUP
  "|- forall s. FINITE s ==> FINITE (group_carrier (symmetric_group s))"
#eval thm' "SYMMETRIC_GROUP_MUL" SYMMETRIC_GROUP_MUL
  "|- forall s p q. group_mul (symmetric_group s) p q = p o q"
#eval thm' "SYMMETRIC_GROUP_ID" SYMMETRIC_GROUP_ID
  "|- forall s. group_id (symmetric_group s) = I"
#eval thm' "THREE_CYCLE_IN_SYMMETRIC" THREE_CYCLE_IN_SYMMETRIC
  "|- forall s a b c.        a IN s /\\ b IN s /\\ c IN s /\\ ~(a = b) /\\ ~(b = c) /\\ ~(a = c)        ==> three_cycle a b c IN group_carrier (symmetric_group s)"
#eval thm' "CAYLEY_THEOREM" CAYLEY_THEOREM
  "|- forall G.        exists h.            h subgroup_of symmetric_group (group_carrier G) /\\            subgroup_generated (symmetric_group (group_carrier G)) h isomorphic_group            G"
#eval thm' "CHAIN_STEP_THREE_CYCLES_GEN" CHAIN_STEP_THREE_CYCLES_GEN
  "|- forall s H n.        5 <= CARD s /\\        FINITE s /\\        n normal_subgroup_of H /\\        abelian_group (quotient_group H n) /\\        group_mul H = (o) /\\        group_inv H = inverse /\\        (forall a b c.             a IN s /\\ b IN s /\\ c IN s /\\ ~(a = b) /\\ ~(b = c) /\\ ~(a = c)             ==> three_cycle a b c IN group_carrier H)        ==> (forall a b c.                 a IN s /\\                 b IN s /\\                 c IN s /\\                 ~(a = b) /\\                 ~(b = c) /\\                 ~(a = c)                 ==> three_cycle a b c IN n)"
#eval thm' "POINT_TRANSPOSITIONS_GENERATE_ALL" POINT_TRANSPOSITIONS_GENERATE_ALL
  "|- forall s a h.        a IN s /\\        h subgroup_of symmetric_group s /\\        (forall x. x IN s /\\ ~(x = a) ==> swap (a,x) IN h)        ==> (forall x y. x IN s /\\ y IN s /\\ ~(x = y) ==> swap (x,y) IN h)"
#eval thm' "SUBGROUP_RESTRICT_PERMUTES" SUBGROUP_RESTRICT_PERMUTES
  "|- forall s t h.        t SUBSET s /\\ h subgroup_of symmetric_group s        ==> h INTER group_carrier (symmetric_group t) subgroup_of            symmetric_group t"
#eval thm' "SYMMETRIC_GROUP_POW" SYMMETRIC_GROUP_POW
  "|- forall s t sigma n.        group_pow (symmetric_group s) sigma n =        group_pow (symmetric_group t) sigma n"
#eval thm' "PRIME_ORDER_PERM_NO_FIXPOINT" PRIME_ORDER_PERM_NO_FIXPOINT
  "|- forall s sigma a.        FINITE s /\\        prime (CARD s) /\\        sigma permutes s /\\        group_element_order (symmetric_group s) sigma = CARD s /\\        a IN s        ==> ~(sigma a = a)"
#eval thm' "PRIME_ORDER_PERM_ORBIT" PRIME_ORDER_PERM_ORBIT
  "|- forall s sigma a x.        FINITE s /\\        prime (CARD s) /\\        sigma permutes s /\\        group_element_order (symmetric_group s) sigma = CARD s /\\        a IN s /\\        x IN s        ==> (exists k.                 k < CARD s /\\ group_pow (symmetric_group s) sigma k a = x)"
#eval thm' "TRANSPOSITION_PCYCLE_GENERATES" TRANSPOSITION_PCYCLE_GENERATES
  "|- forall s sigma a b h.        FINITE s /\\        prime (CARD s) /\\        h subgroup_of symmetric_group s /\\        sigma IN h /\\        group_element_order (symmetric_group s) sigma = CARD s /\\        swap (a,b) IN h /\\        a IN s /\\        b IN s /\\        ~(a = b)        ==> group_carrier (symmetric_group s) SUBSET h"
#eval thm' "TRANSITIVE_TRANSPOSITION_GENERATES_SYMMETRIC" TRANSITIVE_TRANSPOSITION_GENERATES_SYMMETRIC
  "|- forall s a b h.        FINITE s /\\        prime (CARD s) /\\        h subgroup_of symmetric_group s /\\        (forall x y.             x IN s /\\ y IN s ==> (exists sigma. sigma IN h /\\ sigma x = y)) /\\        swap (a,b) IN h /\\        a IN s /\\        b IN s /\\        ~(a = b)        ==> group_carrier (symmetric_group s) SUBSET h"

end T
