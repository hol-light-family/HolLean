/- File: HolTest/ModmulGroupTest.lean
Runtime test suite: Library/modmul_group.ml (HolLibrary/ModmulGroup.lean, wired by
SessionLibrary/ModmulGroup.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/modmul_group.ml"`, then `string_of_thm`, newlines joined).
tools/modmul_groupdiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.ModmulGroup.ensureModmulGroup

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
open Session SessionLibrary.ModmulGroup HolLight.Syntax

#eval thm' "MULT_EQ_2" MULT_EQ_2
  "|- forall m n. m * n = 2 <=> m = 1 /\\ n = 2 \\/ m = 2 /\\ n = 1"
#eval thm' "modmul_group" modmul_group
  "|- forall n.        modmul_group n =        (if n <= 1         then singleton_group 1         else group              ({m | m < n /\\ coprime (m,n)},               1,               inverse_mod n,               (\\a b. (a * b) MOD n)))"
#eval thm' "MODMUL_GROUP" MODMUL_GROUP
  "|- (forall n.         group_carrier (modmul_group n) =         (if n <= 1 then {1} else {m | m < n /\\ coprime (m,n)})) /\\    (forall n. group_id (modmul_group n) = 1) /\\    (forall n. group_inv (modmul_group n) = inverse_mod n) /\\    (forall n.         group_mul (modmul_group n) =         (if n <= 1 then \\a b. 1 else \\a b. (a * b) MOD n))"
#eval thm' "FINITE_MODMUL_GROUP" FINITE_MODMUL_GROUP
  "|- forall n. FINITE (group_carrier (modmul_group n))"
#eval thm' "ORDER_MODMUL_GROUP" ORDER_MODMUL_GROUP
  "|- forall n.        CARD (group_carrier (modmul_group n)) = (if n = 0 then 1 else phi n)"
#eval thm' "HAS_SIZE_MODMUL_GROUP" HAS_SIZE_MODMUL_GROUP
  "|- forall n. ~(n = 0) ==> group_carrier (modmul_group n) HAS_SIZE phi n"
#eval thm' "ABELIAN_MODMUL_GROUP" ABELIAN_MODMUL_GROUP
  "|- forall n. abelian_group (modmul_group n)"
#eval thm' "TRIVIAL_MODMUL_GROUP" TRIVIAL_MODMUL_GROUP
  "|- forall n. trivial_group (modmul_group n) <=> n <= 2"
#eval thm' "GROUP_HOMOMORPHISM_PROD_MODMUL_GROUP" GROUP_HOMOMORPHISM_PROD_MODMUL_GROUP
  "|- forall m n.        2 <= m /\\ 2 <= n        ==> group_homomorphism            (modmul_group (m * n),             prod_group (modmul_group m) (modmul_group n))            (\\a. a MOD m,a MOD n)"
#eval thm' "GROUP_ISOMORPHISM_PROD_MODMUL_GROUP" GROUP_ISOMORPHISM_PROD_MODMUL_GROUP
  "|- forall m n.        2 <= m /\\ 2 <= n /\\ coprime (m,n)        ==> group_isomorphism            (modmul_group (m * n),             prod_group (modmul_group m) (modmul_group n))            (\\a. a MOD m,a MOD n)"
#eval thm' "ISOMORPHIC_GROUP_MODMUL_GROUP" ISOMORPHIC_GROUP_MODMUL_GROUP
  "|- forall m n.        coprime (m,n)        ==> prod_group (modmul_group m) (modmul_group n) isomorphic_group            modmul_group (m * n)"
#eval thm' "GROUP_POW_MODMUL_GROUP" GROUP_POW_MODMUL_GROUP
  "|- forall n a k.        group_pow (modmul_group n) a k = (if n <= 1 then 1 else a EXP k MOD n)"
#eval thm' "GROUP_ELEMENT_ORDER_MODMUL_GROUP" GROUP_ELEMENT_ORDER_MODMUL_GROUP
  "|- forall n a.        a IN group_carrier (modmul_group n)        ==> group_element_order (modmul_group n) a = order n a"
#eval thm' "CYCLIC_MODMUL_GROUP" CYCLIC_MODMUL_GROUP
  "|- forall n.        cyclic_group (modmul_group n) <=>        n = 0 \\/        n = 1 \\/        n = 2 \\/        n = 4 \\/        (exists p k. prime p /\\ 3 <= p /\\ (n = p EXP k \\/ n = 2 * p EXP k))"

end T
