/- File: HolTest/DivStepTest.lean
Runtime test suite: Divstep/divstep.ml, Divstep/idivstep.ml, Divstep/hull_light.ml, Divstep/divstep_bounds.ml
(HolDivStep/, wired by SessionDivStep/).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Divstep/<file>.ml"`, then `string_of_thm`, newlines joined).
tools/ds<file>diff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here.  The files are
in one test module so that each SessionDivStep module replays once. -/

import HolTest.CommonTest
-- DivstepBounds first: its imports load the files in make.ml's order, so
-- hull_light.ml loads after floor.ml's prioritize_real (loading it after
-- divstep.ml alone, under integer priority, fails, as in HOL Light).
import SessionDivStep.DivstepBounds
import SessionDivStep.Divstep
import SessionDivStep.IDivstep
import SessionDivStep.HullLight

open HolCore.Kernel HolTest.CommonTest

#eval SessionDivStep.Divstep.ensureDivstep
#eval SessionDivStep.IDivstep.ensureIDivstep
#eval SessionDivStep.HullLight.ensureHullLight
#eval SessionDivStep.DivstepBounds.ensureDivstepBounds

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

-- Divstep
#eval thm' "Divstep.divstep" SessionDivStep.Divstep.«divstep»
  "|- forall d g f.        divstep (d,f,g) =        (if d > &0 /\\ g rem &2 = &1         then &1 - d,g,(g - f) div &2         else &1 + d,f,(g + g rem &2 * f) div &2)"
#eval thm' "Divstep.divstep1" SessionDivStep.Divstep.«divstep1»
  "|- forall d f g.        divstep1 (d,f,g) =        (if d > &0 /\\ g rem &2 = &1 then --d,g,--f else d,f,g)"
#eval thm' "Divstep.divstep2" SessionDivStep.Divstep.«divstep2»
  "|- forall d g f. divstep2 (d,f,g) = &1 + d,f,(g + g rem &2 * f) div &2"
#eval thm' "Divstep.DIVSTEP1_DIVSTEP2" SessionDivStep.Divstep.«DIVSTEP1_DIVSTEP2»
  "|- forall d f g.        f rem &2 = &1 ==> (divstep2 o divstep1) (d,f,g) = divstep (d,f,g)"
#eval thm' "Divstep.DIVSTEP_STAYS_ODD" SessionDivStep.Divstep.«DIVSTEP_STAYS_ODD»
  "|- forall d f g d' f' g'.        f rem &2 = &1 /\\ divstep (d,f,g) = d',f',g' ==> f' rem &2 = &1"
#eval thm' "Divstep.DIVSTEP_STAYS_ZERO" SessionDivStep.Divstep.«DIVSTEP_STAYS_ZERO»
  "|- forall d f g d' f' g'. g = &0 /\\ divstep (d,f,g) = d',f',g' ==> g' = &0"
#eval thm' "Divstep.DIVSTEP_MAINTAINS_GCD" SessionDivStep.Divstep.«DIVSTEP_MAINTAINS_GCD»
  "|- forall d f g d' f' g'.        f rem &2 = &1 /\\ divstep (d,f,g) = d',f',g'        ==> gcd (f',g') = gcd (f,g)"
#eval thm' "Divstep.DIVSTEP_RANGE_2SCOMPLEMENT" SessionDivStep.Divstep.«DIVSTEP_RANGE_2SCOMPLEMENT»
  "|- forall B d f g d' f' g'.        divstep (d,f,g) = d',f',g' /\\ --B <= f /\\ f < B /\\ --B <= g /\\ g < B        ==> --B <= f' /\\ f' < B /\\ --B <= g' /\\ g' < B"
#eval thm' "Divstep.DIVSTEP_RANGE_SIGNMAGNITUDE" SessionDivStep.Divstep.«DIVSTEP_RANGE_SIGNMAGNITUDE»
  "|- forall B d f g d' f' g'.        divstep (d,f,g) = d',f',g' /\\ --B < f /\\ f < B /\\ --B < g /\\ g < B        ==> --B < f' /\\ f' < B /\\ --B < g' /\\ g' < B"
#eval thm' "Divstep.ITER_DIVSTEP_ODD" SessionDivStep.Divstep.«ITER_DIVSTEP_ODD»
  "|- forall n d f g d' f' g'.        f rem &2 = &1 /\\ ITER n divstep (d,f,g) = d',f',g' ==> f' rem &2 = &1"
#eval thm' "Divstep.ITER_DIVSTEP_ZERO" SessionDivStep.Divstep.«ITER_DIVSTEP_ZERO»
  "|- forall n d f g d' f' g'.        g = &0 /\\ ITER n divstep (d,f,g) = d',f',g' ==> g' = &0"
#eval thm' "Divstep.ITER_DIVSTEP_GCD" SessionDivStep.Divstep.«ITER_DIVSTEP_GCD»
  "|- forall n d f g d' f' g'.        f rem &2 = &1 /\\ ITER n divstep (d,f,g) = d',f',g'        ==> gcd (f',g') = gcd (f,g)"

-- IDivstep
#eval thm' "IDivstep.FORALL_2" SessionDivStep.IDivstep.«FORALL_2»
  "|- forall P. (forall i. 1 <= i /\\ i <= 2 ==> P i) <=> P 1 /\\ P 2"
#eval thm' "IDivstep.imat_mul" SessionDivStep.IDivstep.«imat_mul»
  "|- imat_mul m n = (lambda i j. isum (1..2) (\\k. m$i$k * n$k$j))"
#eval thm' "IDivstep.IMAT_MUL_ASSOC" SessionDivStep.IDivstep.«IMAT_MUL_ASSOC»
  "|- forall m1 m2 m3.        imat_mul m1 (imat_mul m2 m3) = imat_mul (imat_mul m1 m2) m3"
#eval thm' "IDivstep.divstep_d" SessionDivStep.IDivstep.«divstep_d»
  "|- divstep_d n t = FST (ITER n idivstep t)"
#eval thm' "IDivstep.DIVSTEP_F" SessionDivStep.IDivstep.«DIVSTEP_F»
  "|- divstep_f 0 (d,f,g) = f /\\    divstep_f (SUC n) t =    (if divstep_d n t >= &0 /\\ divstep_g n t rem &2 = &1     then divstep_g n t     else divstep_f n t)"
#eval thm' "IDivstep.DIVSTEP_D_BOUND" SessionDivStep.IDivstep.«DIVSTEP_D_BOUND»
  "|- forall n d f g. abs (abs (divstep_d n (d,f,g)) - abs d) <= &2 * &n"
#eval thm' "IDivstep.DIVSTEP_G_BOUNDS" SessionDivStep.IDivstep.«DIVSTEP_G_BOUNDS»
  "|- forall B n d f g.        --B <= f /\\ f < B /\\ --B <= g /\\ g < B        ==> --B <= divstep_g n (d,f,g) /\\ divstep_g n (d,f,g) < B"
#eval thm' "IDivstep.divstep_mat" SessionDivStep.IDivstep.«divstep_mat»
  "|- divstep_mat 0 t = imat_I /\\    divstep_mat (SUC n) t =    imat_mul    (if divstep_d n t >= &0 /\\ divstep_g n t rem &2 = &1     then vector [vector [&0; &2]; vector [-- &1; &1]]     else vector [vector [&2; &0]; vector [divstep_g n t rem &2; &1]])    (divstep_mat n t)"
#eval thm' "IDivstep.DIVSTEP_MAT_DIAGONAL" SessionDivStep.IDivstep.«DIVSTEP_MAT_DIAGONAL»
  "|- forall d f n.        divstep_mat n (d,f,&0)$1$2 = &0 /\\ divstep_mat n (d,f,&0)$2$1 = &0"
#eval thm' "IDivstep.DIVSTEP_D_CONGRUENCE" SessionDivStep.IDivstep.«DIVSTEP_D_CONGRUENCE»
  "|- forall d f g f' g' n.        (f == f') (mod (&2 pow n)) /\\ (g == g') (mod (&2 pow n))        ==> divstep_d n (d,f,g) = divstep_d n (d,f',g')"
#eval thm' "IDivstep.DIVSTEP_MAT_MOD" SessionDivStep.IDivstep.«DIVSTEP_MAT_MOD»
  "|- forall m n d f g.        m <= n        ==> divstep_mat m (d,f rem &2 pow n,g rem &2 pow n) =            divstep_mat m (d,f,g)"
#eval thm' "IDivstep.DIVSTEP_G_NEG" SessionDivStep.IDivstep.«DIVSTEP_G_NEG»
  "|- forall n d f g.        f rem &2 = &1 ==> divstep_g n (d,--f,--g) = --divstep_g n (d,f,g)"

-- HullLight
#eval thm' "HullLight.int_neg_as_minusnum1" SessionDivStep.HullLight.«int_neg_as_minusnum1»
  "|- forall i. i < &0 ==> (exists m. i = -- &(m + 1))"
#eval thm' "HullLight.generic_1_Ppos" SessionDivStep.HullLight.«generic_1_Ppos»
  "|- forall D a b c d e f M00 M01 M10 M11 M P Q x y.        &0 < D        ==> &0 <= M        ==> &0 < P        ==> &0 < Q        ==> M * a * D = Q * (d * M00 + e * M10)        ==> M * b * D = Q * (d * M01 + e * M11)        ==> M * c + P = Q * f        ==> a * x + b * y <= c        ==> d * (M00 * x + M01 * y) / D + e * (M10 * x + M11 * y) / D <= f"
#eval thm' "HullLight.REAL_LE_RDIV" SessionDivStep.HullLight.«REAL_LE_RDIV»
  "|- forall x y z. &0 < x /\\ y * x <= z ==> y <= z / x"
#eval thm' "HullLight.init2stable_simple" SessionDivStep.HullLight.«init2stable_simple»
  "|- forall x y.        divsteps_hinit_0_1 x y        ==> divsteps_H1 (&2753 / &4096 * x) (&2753 / &4096 * y)"
#eval thm' "HullLight.theorem3" SessionDivStep.HullLight.«theorem3»
  "|- forall x y.        divsteps_H1 x y        ==> divsteps_H1 ((&0 * x + &1 * y) / divsteps_s pow 1)            ((-- &1 / &2 * x + &1 / &2 * y) / divsteps_s pow 1)"
#eval thm' "HullLight.theorem_3scale" SessionDivStep.HullLight.«theorem_3scale»
  "|- forall x y.        divsteps_H1 x y        ==> divsteps_H1            ((&33 / &64 * x + -- &33 / &512 * y) / divsteps_s pow 2)            ((&0 * x + &33 / &64 * y) / divsteps_s pow 2)"
#eval thm' "HullLight.h1_shrink32" SessionDivStep.HullLight.«h1_shrink32»
  "|- forall x y.        divsteps_H1 x y ==> divsteps_H1 (&32 / &33 * x) (&32 / &33 * y)"
#eval thm' "HullLight.h1_16_lemma1neg" SessionDivStep.HullLight.«h1_16_lemma1neg»
  "|- forall m x y.        2 <= m        ==> (&1 - (&1 / &2 - &2 / &2 pow m)) * (&1 / &2 * x + -- &1 / &16 * y) +            (&1 / &2 - &2 / &2 pow m) * (&1 / &2 * x + &1 / &16 * y) =            &1 / &2 * x - &1 / &2 pow (m + 2) * y /\\            &0 <= &1 / &2 - &2 / &2 pow m /\\            &1 / &2 - &2 / &2 pow m <= &1"
#eval thm' "HullLight.divsteps_W" SessionDivStep.HullLight.«divsteps_W»
  "|- forall i x y.        divsteps_W i x y <=>        (if i = -- &1         then divsteps_H0 x y         else if i = -- &2              then divsteps_H1 ((x - &2 * y) * divsteps_s zpow (&1 - i))                   (x * divsteps_s zpow (&1 - i) / &2 zpow i)              else if i < -- &2                   then divsteps_H1                        (&32 / &33 * (x - &2 * y) * divsteps_s zpow (&1 - i))                        (&32 / &33 * x * divsteps_s zpow (&1 - i) / &2 zpow i)                   else if i > &2                        then divsteps_H1 (&32 / &33 * x * divsteps_s zpow i)                             (&32 / &33 * y * (&2 * divsteps_s) zpow i)                        else divsteps_H1 (x * divsteps_s zpow i)                             (y * (&2 * divsteps_s) zpow i))"
#eval thm' "HullLight.theoremouter_simple" SessionDivStep.HullLight.«theoremouter_simple»
  "|- forall x y. divsteps_H1 x y ==> divsteps_Houter x y"
#eval thm' "HullLight.iteration_sizebound_simple" SessionDivStep.HullLight.«iteration_sizebound_simple»
  "|- (forall x y. divsteps_H1 x y ==> divsteps_Houter x y)    ==> (forall x y.             divsteps_H0 x y             ==> divsteps_H1 ((&1 * x + &0 * y) / divsteps_s pow 1)                 ((&0 * x + &1 / &2 * y) / divsteps_s pow 1))    ==> (forall x y.             divsteps_H0 x y             ==> divsteps_H1 ((&1 * x + &0 * y) / divsteps_s pow 1)                 ((&1 / &2 * x + &1 / &2 * y) / divsteps_s pow 1))    ==> (forall x y.             divsteps_H1 x y             ==> divsteps_H1 ((&0 * x + &1 * y) / divsteps_s pow 1)                 ((-- &1 / &2 * x + &1 / &2 * y) / divsteps_s pow 1))    ==> (forall x y.             divsteps_H1 x y             ==> divsteps_H0 ((&0 * x + &1 / &2 * y) / divsteps_s pow 2)                 ((-- &1 / &2 * x + &1 / &4 * y) / divsteps_s pow 2))    ==> (forall x y.             divsteps_H1 x y             ==> divsteps_H0 ((&0 * x + &1 / &4 * y) / divsteps_s pow 4)                 ((-- &1 / &4 * x + &1 / &16 * y) / divsteps_s pow 4))    ==> (forall x y.             divsteps_H1 x y             ==> divsteps_H0 ((&0 * x + &1 / &4 * y) / divsteps_s pow 4)                 ((-- &1 / &4 * x + &3 / &16 * y) / divsteps_s pow 4))    ==> (forall x y.             divsteps_H1 x y             ==> divsteps_H1                 ((&33 / &64 * x + &33 / &512 * y) / divsteps_s pow 2)                 ((&0 * x + &33 / &64 * y) / divsteps_s pow 2))    ==> (forall x y.             divsteps_H1 x y             ==> divsteps_H1                 ((&33 / &64 * x + -- &33 / &512 * y) / divsteps_s pow 2)                 ((&0 * x + &33 / &64 * y) / divsteps_s pow 2))    ==> (forall i f g u.             i 0 = &0             ==> (forall n.                      i (n + 1) = &1 + i n /\\                      f (n + 1) = f n /\\                      g (n + 1) = g n / &2 \\/                      (if i n < &0                       then i (n + 1) = &1 + i n /\\                            f (n + 1) = f n /\\                            g (n + 1) = (g n + f n) / &2                       else i (n + 1) = --i n /\\                            f (n + 1) = g n /\\                            g (n + 1) = (g n - f n) / &2))             ==> &0 < u             ==> divsteps_H1 (f 0 / u) (g 0 / u)             ==> (forall n. integer (f n))             ==> (forall n. integer (g n))             ==> (forall m.                      (forall n. n <= m ==> ~(g n = &0))                      ==> &3047 / &2048 < u * divsteps_s pow m))"
#eval thm' "HullLight.endtoend_bits_simple" SessionDivStep.HullLight.«endtoend_bits_simple»
  "|- forall i f g b m.        i 0 = &0        ==> &0 <= g 0        ==> g 0 <= f 0        ==> f 0 <= &2 pow b        ==> (forall n.                 i (n + 1) = &1 + i n /\\                 f (n + 1) = f n /\\                 g (n + 1) = g n / &2 \\/                 (if i n < &0                  then i (n + 1) = &1 + i n /\\                       f (n + 1) = f n /\\                       g (n + 1) = (g n + f n) / &2                  else i (n + 1) = --i n /\\                       f (n + 1) = g n /\\                       g (n + 1) = (g n - f n) / &2))        ==> (forall n. integer (f n))        ==> (forall n. integer (g n))        ==> 9437 * b + 1 <= 4096 * m        ==> (exists n. n <= m /\\ g n = &0)"

-- DivstepBounds
#eval thm' "DivstepBounds.INTEGER_DIVSTEP_DELTA" SessionDivStep.DivstepBounds.«INTEGER_DIVSTEP_DELTA»
  "|- forall f g n. integer (FST (ITER n divstep (&1 / &2,f,g)) - &1 / &2)"
#eval thm' "DivstepBounds.ITER_DIVSTEP_ODD_ALT" SessionDivStep.DivstepBounds.«ITER_DIVSTEP_ODD_ALT»
  "|- forall f g n.        f rem &2 = &1 ==> FST (SND (ITER n divstep (&1 / &2,f,g))) rem &2 = &1"
#eval thm' "DivstepBounds.DIVSTEP_ENDTOEND_BITS_SIMPLE" SessionDivStep.DivstepBounds.«DIVSTEP_ENDTOEND_BITS_SIMPLE»
  "|- forall f g b n.        &0 <= g /\\        g <= f /\\        f <= &2 pow b /\\        f rem &2 = &1 /\\        9437 * b + 1 <= 4096 * n        ==> SND (SND (ITER n divstep (&1 / &2,f,g))) = &0"
#eval thm' "DivstepBounds.IDIVSTEP_ENDTOEND_BITS_SIMPLE" SessionDivStep.DivstepBounds.«IDIVSTEP_ENDTOEND_BITS_SIMPLE»
  "|- forall f g b n.        &0 <= g /\\        g <= f /\\        f <= &2 pow b /\\        f rem &2 = &1 /\\        9437 * b + 1 <= 4096 * n        ==> divstep_g n (&1,f,g) = &0 /\\            abs (divstep_f n (&1,f,g)) = gcd (f,g)"

end T
