/- File: HolTest/RealAnalysisTest.lean
Runtime test suite: Multivariate/realanalysis.ml
(HolMultiLib/RealAnalysis.lean, wired by SessionMultiLib/RealAnalysis.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/realanalysis.ml"`, then `string_of_thm`).  The whole file is also
compared with HOL Light by tools/realanalysisdiff: all exported theorems structurally
and by their printed forms.  The 20 theorems here are spread evenly over the
file; theorems that print with `?nnn` invented type variables are left out.

Loading realanalysis.ml (`ensureRealAnalysis`) builds every bundle in file order; a proof
that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.RealAnalysis

open HolCore.Kernel Session SessionMultiLib.RealAnalysis
open HolTest.CommonTest HolLight.Syntax

#eval ensureRealAnalysis

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

#eval thmCheck "realanalysis.ml REAL_OPEN" REAL_OPEN
  "|- forall s. real_open s <=> open (IMAGE lift s)"
#eval thmCheck "realanalysis.ml REAL_SERIES_GOESTOZERO" REAL_SERIES_GOESTOZERO
  "|- forall s x.        real_summable s x        ==> (forall e.                 &0 < e                 ==> eventually (\\n. n IN s ==> abs (x n) < e) sequentially)"
#eval thmCheck "realanalysis.ml REAL_SERIES_COMPARISON_UNIFORM" REAL_SERIES_COMPARISON_UNIFORM
  "|- forall f g P s.        (exists l. (g real_sums l) s) /\\        (exists N. forall n x. N <= n /\\ n IN s /\\ P x ==> abs (f x n) <= g n)        ==> (exists l.                 forall e.                     &0 < e                     ==> (exists N.                              forall n x.                                  N <= n /\\ P x                                  ==> abs (sum (s INTER (0..n)) (f x) - l x) <                                      e))"
#eval thmCheck "realanalysis.ml CONTINUOUS_CX_ATREAL" CONTINUOUS_CX_ATREAL
  "|- forall x. Cx continuous atreal x"
#eval thmCheck "realanalysis.ml HAS_REAL_DERIVATIVE_ATREAL" HAS_REAL_DERIVATIVE_ATREAL
  "|- (f has_real_derivative f') (atreal a) <=>    ((\\x. (f x - f a) / (x - a)) ---> f') (atreal a)"
#eval thmCheck "realanalysis.ml HAS_REAL_DERIVATIVE_ZERO_UNIQUE" HAS_REAL_DERIVATIVE_ZERO_UNIQUE
  "|- forall f s c a.        is_realinterval s /\\        a IN s /\\        f a = c /\\        (forall x. x IN s ==> (f has_real_derivative &0) (atreal x within s))        ==> (forall x. x IN s ==> f x = c)"
#eval thmCheck "realanalysis.ml REAL_CONTINUOUS_AT_EXP" REAL_CONTINUOUS_AT_EXP
  "|- forall x. exp real_continuous atreal x"
#eval thmCheck "realanalysis.ml REAL_CONTINUOUS_WITHIN_ACS_STRONG" REAL_CONTINUOUS_WITHIN_ACS_STRONG
  "|- forall x. acs real_continuous atreal x within {t | abs t <= &1}"
#eval thmCheck "realanalysis.ml HAS_LIMSUP_SEQUENTIALLY_IMP_REALLIM_SUP" HAS_LIMSUP_SEQUENTIALLY_IMP_REALLIM_SUP
  "|- forall f l.        (f has_limsup l) sequentially        ==> ((\\n. sup {f m | m >= n}) ---> l) sequentially"
#eval thmCheck "realanalysis.ml IS_REALINTERVAL_CONTAINS_SEGMENT_EQ" IS_REALINTERVAL_CONTAINS_SEGMENT_EQ
  "|- forall s.        is_realinterval s <=>        (forall a b. real_segment [a,b] SUBSET s <=> a IN s /\\ b IN s)"
#eval thmCheck "realanalysis.ml REAL_EXP_LIMIT_RPOW_LT" REAL_EXP_LIMIT_RPOW_LT
  "|- forall x r s.        &0 < r /\\ r < s /\\ ~(x = &0) /\\ x < r        ==> (&1 - x / r) rpow r < (&1 - x / s) rpow s"
#eval thmCheck "realanalysis.ml REAL_INTEGRABLE_RMUL_EQ" REAL_INTEGRABLE_RMUL_EQ
  "|- forall f s c.        (\\x. f x * c) real_integrable_on s <=>        c = &0 \\/ f real_integrable_on s"
#eval thmCheck "realanalysis.ml REAL_INTEGRABLE_SPIKE_INTERIOR" REAL_INTEGRABLE_SPIKE_INTERIOR
  "|- forall f g a b.        (forall x. x IN real_interval (a,b) ==> g x = f x)        ==> f real_integrable_on real_interval [a,b]        ==> g real_integrable_on real_interval [a,b]"
#eval thmCheck "realanalysis.ml REAL_INDEFINITE_INTEGRAL_CONTINUOUS" REAL_INDEFINITE_INTEGRAL_CONTINUOUS
  "|- forall f a b c d e.        f real_integrable_on real_interval [a,b] /\\        c IN real_interval [a,b] /\\        d IN real_interval [a,b] /\\        &0 < e        ==> (exists k.                 &0 < k /\\                 (forall c' d'.                      c' IN real_interval [a,b] /\\                      d' IN real_interval [a,b] /\\                      abs (c' - c) <= k /\\                      abs (d' - d) <= k                      ==> abs                          (real_integral (real_interval [c',d']) f -                           real_integral (real_interval [c,d]) f) <                          e))"
#eval thmCheck "realanalysis.ml REAL_MEASURE_SUBSET" REAL_MEASURE_SUBSET
  "|- forall s t.        real_measurable s /\\ real_measurable t /\\ s SUBSET t        ==> real_measure s <= real_measure t"
#eval thmCheck "realanalysis.ml REAL_MEASURABLE_NESTED_UNIONS" REAL_MEASURABLE_NESTED_UNIONS
  "|- forall s B.        (forall n. real_measurable (s n)) /\\        (forall n. real_measure (s n) <= B) /\\        (forall n. s n SUBSET s (SUC n))        ==> real_measurable (UNIONS {s n | n IN (:num)})"
#eval thmCheck "realanalysis.ml REAL_CONTINUOUS_ON_COMPOSE_FRAC" REAL_CONTINUOUS_ON_COMPOSE_FRAC
  "|- forall f.        f real_continuous_on real_interval [&0,&1] /\\ f (&1) = f (&0)        ==> f o frac real_continuous_on (:real)"
#eval thmCheck "realanalysis.ml BERNOULLI_NUMBER_ALT" BERNOULLI_NUMBER_ALT
  "|- forall n.        sum (0..n) (\\k. &(binom (n + 1,k)) * bernoulli k (&0)) =        (if n = 0 then &1 else &0)"
#eval thmCheck "realanalysis.ml REAL_COMPLEX_MEASURABLE_ON" REAL_COMPLEX_MEASURABLE_ON
  "|- forall f s.        f real_measurable_on s <=> Cx o f o drop measurable_on IMAGE lift s"
#eval thmCheck "realanalysis.ml HAS_BOUNDED_REAL_VARIATION_ON_EQ" HAS_BOUNDED_REAL_VARIATION_ON_EQ
  "|- forall f g s.        (forall x. x IN s ==> f x = g x) /\\ f has_bounded_real_variation_on s        ==> g has_bounded_real_variation_on s"
