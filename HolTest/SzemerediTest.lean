/- File: HolTest/SzemerediTest.lean
Runtime test suite: Library/szemeredi.ml (HolLibrary/Szemeredi.lean, wired by
SessionLibrary/Szemeredi.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/szemeredi.ml"`, then `string_of_thm`, newlines joined).
tools/szemeredidiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary.Szemeredi

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Szemeredi.ensureSzemeredi

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
open Session SessionLibrary.Szemeredi HolLight.Syntax

#eval thm' "fmean" fmean
  "|- forall g X. fmean X g = sum X g / &(CARD X)"
#eval thm' "IN_HJ_CUBE" IN_HJ_CUBE
  "|- forall k n x.        x IN hj_cube k n <=>        (forall i. i < n ==> x i < k) /\\ (forall i. n <= i ==> x i = 0)"
#eval thm' "HJ_CONCAT_SPLIT" HJ_CONCAT_SPLIT
  "|- forall l w. hj_concat l (hj_take l w) (hj_drop l w) = w"
#eval thm' "HJ_SUBST_INJ" HJ_SUBST_INJ
  "|- forall k k' m n z a b.        hj_subspace k m n z /\\        a IN hj_cube k' m /\\        b IN hj_cube k' m /\\        hj_subst k z a = hj_subst k z b        ==> a = b"
#eval thm' "HJ_LINE_SUBST" HJ_LINE_SUBST
  "|- forall k m n z u.        1 <= k /\\ hj_subspace k m n z /\\ hj_line k m u        ==> hj_line k n (hj_subst k z u)"
#eval thm' "HJ_DENSITY_POS" HJ_DENSITY_POS
  "|- forall k n A. &0 <= hj_density k n A"
#eval thm' "HJT_MONO_N" HJT_MONO_N
  "|- forall t r N N'.        1 <= t /\\ hales_jewett_template t r N /\\ N <= N'        ==> hales_jewett_template t r N'"
#eval thm' "HJT_PROD_LIFT_SUBST_LE" HJT_PROD_LIFT_SUBST_LE
  "|- forall t M l Ns p a.        hjt_line t M l /\\ a <= t        ==> hjt_subst (t + 1) (Ns + M) (hjt_prod Ns p (hjt_lift t M l)) a =            hjt_prod Ns (hjt_subst (t + 1) Ns p a) (hjt_subst t M l a)"
#eval thm' "HJ_SUBST_TAKE" HJ_SUBST_TAKE
  "|- forall k m n z a.        1 <= k /\\ hj_subspace k m n z        ==> hj_subst k z (hj_take m a) = hj_subst k z a"
#eval thm' "HJ_SUBSPACE_1_UNIT" HJ_SUBSPACE_1_UNIT
  "|- hj_subspace 1 1 1 (\\i. if i = 0 then 1 else 0)"
#eval thm' "HJ_LINE_POINT_K" HJ_LINE_POINT_K
  "|- forall k n x. hj_line k n x ==> hj_line_point k x k = x"
#eval thm' "MULTIDIM_DENSITY_HALES_JEWETT" MULTIDIM_DENSITY_HALES_JEWETT
  "|- forall k.        1 <= k /\\ density_hales_jewett k        ==> (forall m delta.                 &0 < delta                 ==> (exists N.                          forall n A.                              N <= n /\\ delta <= hj_density k n A                              ==> (exists z.                                       hj_subspace k m n z /\\                                       (forall a.                                            a IN hj_cube k m                                            ==> hj_subst k z a IN A))))"
#eval thm' "HJ_SUBSPACE_MONO_LENGTH" HJ_SUBSPACE_MONO_LENGTH
  "|- forall k m n n' z.        1 <= k /\\ n <= n' /\\ hj_subspace k m n z ==> hj_subspace k m n' z"
#eval thm' "HJ_INSENSITIVE_REPLACE" HJ_INSENSITIVE_REPLACE
  "|- forall q n i j A. hj_insensitive q n i j {x | hj_replace j i x IN A}"
#eval thm' "DKT_PARTITION_INCREMENT" DKT_PARTITION_INCREMENT
  "|- forall k q n C A rho eta.        1 <= k /\\        &0 < eta /\\        &0 <= rho /\\        (rho + &6 * eta) *        hj_density q n        {x | x IN hj_cube q n /\\ (exists i. i < k /\\ ~(x IN C i))} <=        hj_density q n {x | x IN A /\\ (exists i. i < k /\\ ~(x IN C i))}        ==> (exists i0.                 i0 < k /\\                 &3 *                 eta / &k *                 hj_density q n                 {x | x IN hj_cube q n /\\ (exists i. i < k /\\ ~(x IN C i))} <=                 hj_density q n                 {x | x IN hj_cube q n /\\                      ~(x IN C i0) /\\                      (forall j. j < i0 ==> x IN C j)} /\\                 (rho + &3 * eta) *                 hj_density q n                 {x | x IN hj_cube q n /\\                      ~(x IN C i0) /\\                      (forall j. j < i0 ==> x IN C j)} <=                 hj_density q n                 {x | x IN A /\\                      ~(x IN C i0) /\\                      (forall j. j < i0 ==> x IN C j)})"
#eval thm' "HJ_DENSITY_TILING_UNION_RESTRICT" HJ_DENSITY_TILING_UNION_RESTRICT
  "|- forall q m n Fs E P.        1 <= q /\\ hj_tiling q m n Fs E        ==> hj_density q n {x | x IN hj_tiling_union q m Fs /\\ P x} =            sum Fs (\\z. hj_density q m {a | P (hj_subst q z a)}) *            &(q EXP m) / &(q EXP n)"
#eval thm' "SUM_HJ_INSERT" SUM_HJ_INSERT
  "|- forall q p M1 r f.        sum (hj_cube q (p + M1 + r)) f =        sum (hj_cube q (p + r))        (\\w. sum (hj_cube q M1) (\\z. f (hj_insert p M1 w z)))"
#eval thm' "HJ_DENSITY_SUBADD" HJ_DENSITY_SUBADD
  "|- forall q n A B C.        (forall x. x IN hj_cube q n /\\ x IN A ==> x IN B \\/ x IN C)        ==> hj_density q n A <= hj_density q n B + hj_density q n C"
#eval thm' "HJ_LINE_WILDCARDS" HJ_LINE_WILDCARDS
  "|- forall k n l.        hj_line k n l        ==> 0 < CARD {r | r < n /\\ l r = k} /\\            CARD {r | r < n /\\ l r = k} <= n"
#eval thm' "SZEMEREDI_UP_PROGRESSION" SZEMEREDI_UP_PROGRESSION
  "|- forall k N W b X a d ok Q.        2 <= k /\\        1 <= W /\\        (forall y. ok y ==> 2 * y < N /\\ Q (W * y + b) /\\ W * y + b <= X) /\\        a < N /\\        0 < d /\\        d < N /\\        (forall j. j < k ==> ok ((a + j * d) MOD N)) /\\        a < (a + d) MOD N        ==> 0 < W * ((a + d) MOD N - a) /\\            (W * a + b) + (k - 1) * W * ((a + d) MOD N - a) <= X /\\            (forall j.                 j < k ==> Q ((W * a + b) + j * W * ((a + d) MOD N - a)))"

end T
