/- File: HolTest/IntegrationTest.lean
Runtime test suite: Multivariate/integration.ml
(HolMultiLib/Integration.lean, wired by SessionMultiLib/Integration.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/integration.ml"`, then `string_of_thm`).  The whole file
is also compared with HOL Light by tools/indiff: all 919 exported theorems
structurally and by their printed forms.

The theorems chosen here are spread over the file: uniqueness and linearity
of the integral, the Cauchy criterion and uniform limits, Henstock's lemma,
the monotone and dominated convergence theorems and Fatou's lemma, the
fundamental theorem of calculus and integration by parts, the second mean
value theorem, bounded variation (its definition, the Darboux decomposition
and Helly's selection theorem), one-sided derivatives of convex functions,
absolute continuity, path length, and the Picard-Lindelof theorem.

Loading integration.ml (`ensureIntegration`) builds every bundle in file order;
a proof that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Integration

open HolCore.Kernel Session SessionMultiLib.Integration
open HolTest.CommonTest HolLight.Syntax

#eval ensureIntegration

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- The integral: uniqueness, linearity, Cauchy criterion, uniform limits. -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "integration.ml HAS_INTEGRAL_UNIQUE" HAS_INTEGRAL_UNIQUE
  "|- forall f i k1 k2.
       (f has_integral k1) i /\\ (f has_integral k2) i ==> k1 = k2"
#eval thmCheck "integration.ml INTEGRAL_NEG" INTEGRAL_NEG
  "|- forall f s. f integrable_on s ==> integral s (\\x. --f x) = --integral s f"
#eval thmCheck "integration.ml INTEGRABLE_CAUCHY" INTEGRABLE_CAUCHY
  "|- forall f a b.
       f integrable_on interval [a,b] <=>
       (forall e.
            &0 < e
            ==> (exists d.
                     gauge d /\\
                     (forall p1 p2.
                          p1 tagged_division_of interval [a,b] /\\
                          d fine p1 /\\
                          p2 tagged_division_of interval [a,b] /\\
                          d fine p2
                          ==> norm
                              (vsum p1 (\\(x,k). content k % f x) -
                               vsum p2 (\\(x,k). content k % f x)) <
                              e)))"
#eval thmCheck "integration.ml INTEGRABLE_UNIFORM_LIMIT" INTEGRABLE_UNIFORM_LIMIT
  "|- forall f a b.
       (forall e.
            &0 < e
            ==> (exists g.
                     (forall x.
                          x IN interval [a,b] ==> norm (f x - g x) <= e) /\\
                     g integrable_on interval [a,b]))
       ==> f integrable_on interval [a,b]"
#eval thmCheck "integration.ml INTEGRAL_SPIKE" INTEGRAL_SPIKE
  "|- forall f g s t.
       negligible s /\\ (forall x. x IN t DIFF s ==> g x = f x)
       ==> integral t f = integral t g"
#eval thmCheck "integration.ml HENSTOCK_LEMMA" HENSTOCK_LEMMA
  "|- forall f a b.
       f integrable_on interval [a,b]
       ==> (forall e.
                &0 < e
                ==> (exists d.
                         gauge d /\\
                         (forall p.
                              p tagged_partial_division_of interval [a,b] /\\
                              d fine p
                              ==> sum p
                                  (\\(x,k).
                                       norm (content k % f x - integral k f)) <
                                  e)))"

/- ---------------------------------------------------------------------- -/
/- Convergence theorems.                                                  -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "integration.ml MONOTONE_CONVERGENCE_INCREASING" MONOTONE_CONVERGENCE_INCREASING
  "|- forall f g s.
       (forall k. f k integrable_on s) /\\
       (forall k x. x IN s ==> drop (f k x) <= drop (f (SUC k) x)) /\\
       (forall x. x IN s ==> ((\\k. f k x) --> g x) sequentially) /\\
       bounded {integral s (f k) | k IN (:num)}
       ==> g integrable_on s /\\
           ((\\k. integral s (f k)) --> integral s g) sequentially"
#eval thmCheck "integration.ml DOMINATED_CONVERGENCE" DOMINATED_CONVERGENCE
  "|- forall f g h s.
       (forall k. f k integrable_on s) /\\
       h integrable_on s /\\
       (forall k x. x IN s ==> norm (f k x) <= drop (h x)) /\\
       (forall x. x IN s ==> ((\\k. f k x) --> g x) sequentially)
       ==> g integrable_on s /\\
           ((\\k. integral s (f k)) --> integral s g) sequentially"
#eval thmCheck "integration.ml FATOU" FATOU
  "|- forall f g s t B.
       negligible t /\\
       (forall n. f n integrable_on s) /\\
       (forall n x. x IN s DIFF t ==> &0 <= drop (f n x)) /\\
       (forall x. x IN s DIFF t ==> ((\\n. f n x) --> g x) sequentially) /\\
       (forall n. drop (integral s (f n)) <= B)
       ==> g integrable_on s /\\
           &0 <= drop (integral s g) /\\
           drop (integral s g) <= B"

/- ---------------------------------------------------------------------- -/
/- Fundamental theorem of calculus, integration by parts, mean values.    -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "integration.ml FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG" FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG
  "|- forall f f' s a b.
       COUNTABLE s /\\
       drop a <= drop b /\\
       f continuous_on interval [a,b] /\\
       (forall x.
            x IN interval [a,b] DIFF s
            ==> (f has_vector_derivative f' x) (at x within interval [a,b]))
       ==> (f' has_integral f b - f a) (interval [a,b])"
#eval thmCheck "integration.ml FUNDAMENTAL_THEOREM_OF_CALCULUS" FUNDAMENTAL_THEOREM_OF_CALCULUS
  "|- forall f f' a b.
       drop a <= drop b /\\
       (forall x.
            x IN interval [a,b]
            ==> (f has_vector_derivative f' x) (at x within interval [a,b]))
       ==> (f' has_integral f b - f a) (interval [a,b])"
#eval thmCheck "integration.ml INTEGRATION_BY_PARTS" INTEGRATION_BY_PARTS
  "|- forall bop f g f' g' a b c y.
       bilinear bop /\\
       drop a <= drop b /\\
       COUNTABLE c /\\
       (\\x. bop (f x) (g x)) continuous_on interval [a,b] /\\
       (forall x.
            x IN interval (a,b) DIFF c
            ==> (f has_vector_derivative f' x) (at x) /\\
                (g has_vector_derivative g' x) (at x)) /\\
       ((\\x. bop (f x) (g' x)) has_integral
        bop (f b) (g b) - bop (f a) (g a) - y)
       (interval [a,b])
       ==> ((\\x. bop (f' x) (g x)) has_integral y) (interval [a,b])"
#eval thmCheck "integration.ml SECOND_MEAN_VALUE_THEOREM" SECOND_MEAN_VALUE_THEOREM
  "|- forall f g a b.
       ~(interval [a,b] = {}) /\\
       f integrable_on interval [a,b] /\\
       (forall x y.
            x IN interval [a,b] /\\ y IN interval [a,b] /\\ drop x <= drop y
            ==> g x <= g y)
       ==> (exists c.
                c IN interval [a,b] /\\
                integral (interval [a,b]) (\\x. g x % f x) =
                g a % integral (interval [a,c]) f +
                g b % integral (interval [c,b]) f)"

/- ---------------------------------------------------------------------- -/
/- Bounded variation.                                                     -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "integration.ml has_bounded_variation_on" has_bounded_variation_on
  "|- forall f s.
       f has_bounded_variation_on s <=>
       (\\k. f (interval_upperbound k) - f (interval_lowerbound k)) has_bounded_setvariation_on
       s"
#eval thmCheck "integration.ml HAS_BOUNDED_VARIATION_DARBOUX" HAS_BOUNDED_VARIATION_DARBOUX
  "|- forall f a b.
       f has_bounded_variation_on interval [a,b] <=>
       (exists g h.
            (forall x y.
                 x IN interval [a,b] /\\
                 y IN interval [a,b] /\\
                 drop x <= drop y
                 ==> drop (g x) <= drop (g y)) /\\
            (forall x y.
                 x IN interval [a,b] /\\
                 y IN interval [a,b] /\\
                 drop x <= drop y
                 ==> drop (h x) <= drop (h y)) /\\
            (forall x. f x = g x - h x))"
#eval thmCheck "integration.ml HELLY_SELECTION_THEOREM" HELLY_SELECTION_THEOREM
  "|- forall f s c d.
       is_interval s /\\
       (forall n. f n has_bounded_variation_on s) /\\
       (forall n. vector_variation s (f n) <= c) /\\
       (forall n x. x IN s ==> norm (f n x) <= d)
       ==> (exists r g.
                (forall m n. m < n ==> r m < r n) /\\
                (forall x. x IN s ==> ((\\n. f (r n) x) --> g x) sequentially) /\\
                g has_bounded_variation_on s /\\
                vector_variation s g <= c)"

/- ---------------------------------------------------------------------- -/
/- Convex functions, absolute continuity, path length, Picard-Lindelof.   -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "integration.ml CONVEX_ON_DIRECTIONAL_DERIVATIVES" CONVEX_ON_DIRECTIONAL_DERIVATIVES
  "|- forall f s a.
       f convex_on s /\\ a IN interior s
       ==> (exists l r.
                (lift o f has_vector_derivative l)
                (at a within {x | drop x <= drop a}) /\\
                (lift o f has_vector_derivative r)
                (at a within {x | drop a <= drop x}) /\\
                drop l <= drop r)"
#eval thmCheck "integration.ml ABSOLUTELY_CONTINUOUS_ON_IMP_HAS_BOUNDED_VARIATION_ON" ABSOLUTELY_CONTINUOUS_ON_IMP_HAS_BOUNDED_VARIATION_ON
  "|- forall f s.
       f absolutely_continuous_on s /\\ bounded s
       ==> f has_bounded_variation_on s"
#eval thmCheck "integration.ml PATH_LENGTH_JOIN" PATH_LENGTH_JOIN
  "|- forall g1 g2.
       rectifiable_path g1 /\\
       rectifiable_path g2 /\\
       pathfinish g1 = pathstart g2
       ==> path_length (g1 ++ g2) = path_length g1 + path_length g2"
#eval thmCheck "integration.ml PICARD_LINDELOF_RIGHT" PICARD_LINDELOF_RIGHT
  "|- forall s f t0 u0 r0 r1 B c.
       open s /\\
       f continuous_on s /\\
       &0 < r0 /\\
       &0 < r1 /\\
       B * r0 < r1 /\\
       c * r0 < &1 /\\
       interval [t0,t0 + lift r0] PCROSS cball (u0,r1) SUBSET s /\\
       (forall x. x IN s ==> norm (f x) <= B) /\\
       (forall t v w.
            t IN interval [t0,t0 + lift r0] /\\
            v IN cball (u0,r1) /\\
            w IN cball (u0,r1)
            ==> norm (f (pastecart t v) - f (pastecart t w)) <=
                c * norm (v - w))
       ==> (exists u.
                u t0 = u0 /\\
                (forall t.
                     t IN interval [t0,t0 + lift r0]
                     ==> (u has_vector_derivative f (pastecart t (u t)))
                         (at t within interval [t0,t0 + lift r0])) /\\
                (forall v.
                     (forall t.
                          t IN interval [t0,t0 + lift r0]
                          ==> pastecart t (v t) IN s) /\\
                     v t0 = u0 /\\
                     (forall t.
                          t IN interval [t0,t0 + lift r0]
                          ==> (v has_vector_derivative f (pastecart t (v t)))
                              (at t within interval [t0,t0 + lift r0]))
                     ==> (forall t.
                              t IN interval [t0,t0 + lift r0] ==> v t = u t)))"
