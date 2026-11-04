/- File: HolTest/GammaTest.lean
Runtime test suite: Multivariate/gamma.ml
(HolMultiLib/Gamma.lean, wired by SessionMultiLib/Gamma.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/gamma.ml"`, then `string_of_thm`).  The whole file is also
compared with HOL Light by tools/gammadiff: all exported theorems structurally
and by their printed forms.  The 20 theorems here are spread evenly over the
file; theorems that print with `?nnn` invented type variables are left out.

Loading gamma.ml (`ensureGamma`) builds every bundle in file order; a proof
that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Gamma

open HolCore.Kernel Session SessionMultiLib.Gamma
open HolTest.CommonTest HolLight.Syntax

#eval ensureGamma

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

#eval thmCheck "gamma.ml EULER_MASCHERONI" EULER_MASCHERONI
  "|- ((\\n. sum (1..n) (\\k. inv (&k)) - log (&n)) ---> euler_mascheroni)    sequentially"
#eval thmCheck "gamma.ml COMPLEX_DIFFERENTIABLE_AT_LGAMMA" COMPLEX_DIFFERENTIABLE_AT_LGAMMA
  "|- forall z. (Im z = &0 ==> &0 < Re z) ==> lgamma complex_differentiable at z"
#eval thmCheck "gamma.ml CGAMMA_EQ_0" CGAMMA_EQ_0
  "|- forall z. cgamma z = Cx (&0) <=> (exists n. z + Cx (&n) = Cx (&0))"
#eval thmCheck "gamma.ml CGAMMA_FACT" CGAMMA_FACT
  "|- forall n. cgamma (Cx (&(n + 1))) = Cx (&(FACT n))"
#eval thmCheck "gamma.ml HOLOMORPHIC_ON_CGAMMA" HOLOMORPHIC_ON_CGAMMA
  "|- forall s.        s SUBSET {z | forall n. ~(z + Cx (&n) = Cx (&0))}        ==> cgamma holomorphic_on s"
#eval thmCheck "gamma.ml CGAMMA_SIMPLE_POLES" CGAMMA_SIMPLE_POLES
  "|- forall n.        ((\\z. (z + Cx (&n)) * cgamma z) --> --Cx (&1) pow n / Cx (&(FACT n)))        (at (--Cx (&n)))"
#eval thmCheck "gamma.ml CGAMMA_REFLECTION" CGAMMA_REFLECTION
  "|- forall z. cgamma z * cgamma (Cx (&1) - z) = Cx pi / csin (Cx pi * z)"
#eval thmCheck "gamma.ml COMPLEX_DIFFERENTIABLE_AT_RECIP_CGAMMA" COMPLEX_DIFFERENTIABLE_AT_RECIP_CGAMMA
  "|- forall z. inv o cgamma complex_differentiable at z"
#eval thmCheck "gamma.ml CONTINUOUS_WITHIN_RECIP_CGAMMA" CONTINUOUS_WITHIN_RECIP_CGAMMA
  "|- forall z s. inv o cgamma continuous at z within s"
#eval thmCheck "gamma.ml GAMMA_EQ_0" GAMMA_EQ_0
  "|- forall x. gamma x = &0 <=> (exists n. x + &n = &0)"
#eval thmCheck "gamma.ml REAL_CONTINUOUS_ATREAL_GAMMA" REAL_CONTINUOUS_ATREAL_GAMMA
  "|- forall x. (forall n. ~(x + &n = &0)) ==> gamma real_continuous atreal x"
#eval thmCheck "gamma.ml REAL_DIFFERENTIABLE_WITHIN_RECIP_GAMMA" REAL_DIFFERENTIABLE_WITHIN_RECIP_GAMMA
  "|- forall x s. inv o gamma real_differentiable atreal x within s"
#eval thmCheck "gamma.ml GAMMA_RECURRENCE_ALT" GAMMA_RECURRENCE_ALT
  "|- forall x. gamma x = gamma (x + &1) / x"
#eval thmCheck "gamma.ml GAMMA_POLES" GAMMA_POLES
  "|- forall n. gamma (-- &n) = &0"
#eval thmCheck "gamma.ml GAMMA_LEGENDRE_ALT" GAMMA_LEGENDRE_ALT
  "|- forall x.        gamma x * gamma (x + &1 / &2) =        &2 rpow (&1 - &2 * x) * gamma (&1 / &2) * gamma (&2 * x)"
#eval thmCheck "gamma.ml REAL_LOG_CONVEX_GAMMA" REAL_LOG_CONVEX_GAMMA
  "|- forall s. (forall x. x IN s ==> &0 < x) ==> gamma real_log_convex_on s"
#eval thmCheck "gamma.ml EULER_INTEGRABLE" EULER_INTEGRABLE
  "|- forall z.        &0 < Re z        ==> (\\t. Cx (drop t) cpow (z - Cx (&1)) / cexp (Cx (drop t))) integrable_on            {t | &0 <= drop t}"
#eval thmCheck "gamma.ml EULER_ORIGINAL_REAL_INTEGRABLE" EULER_ORIGINAL_REAL_INTEGRABLE
  "|- forall x.        &0 < x        ==> (\\t. --log t rpow (x - &1)) real_integrable_on            real_interval [&0,&1]"
#eval thmCheck "gamma.ml EULER_ORIGINAL_REAL_INTEGRAL" EULER_ORIGINAL_REAL_INTEGRAL
  "|- forall x.        &0 < x        ==> real_integral (real_interval [&0,&1]) (\\t. --log t rpow (x - &1)) =            gamma x"
#eval thmCheck "gamma.ml CSIN_PRODUCT" CSIN_PRODUCT
  "|- forall z.        ((\\n. z * cproduct (1..n) (\\m. Cx (&1) - (z / Cx (pi * &m)) pow 2)) -->         csin z)        sequentially"
