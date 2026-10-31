/- File: HolTest/DerivativesTest.lean
Runtime test suite: Multivariate/derivatives.ml
(HolMultiLib/Derivatives.lean, wired by SessionMultiLib/Derivatives.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/derivatives.ml"`, then `string_of_thm`).  The whole file
is also compared with HOL Light by tools/dvdiff: all 209 exported theorems
structurally and by their printed forms.

The theorems chosen here are spread over the file: the chain rule and
uniqueness of derivatives, Rolle's theorem and the mean value theorems,
inverse functions and Sussmann's open mapping theorem, uniformly convergent
sequences of derivatives, the strong inverse function theorem and the sign
invariance of the Jacobian, vector derivatives and Kachurovskii's theorem.

Loading derivatives.ml (`ensureDerivatives`) builds every bundle in file order; a
proof that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Derivatives

open HolCore.Kernel Session SessionMultiLib.Derivatives
open HolTest.CommonTest HolLight.Syntax

#eval ensureDerivatives

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- Derivatives, the chain rule and uniqueness.                            -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "derivatives.ml DIFF_CHAIN_AT" DIFF_CHAIN_AT
  "|- forall f g f' g' x.
          (f has_derivative f') (at x) /\\ (g has_derivative g') (at (f x))
          ==> (g o f has_derivative g' o f') (at x)"
#eval thmCheck "derivatives.ml DIFF_CHAIN_WITHIN" DIFF_CHAIN_WITHIN
  "|- forall f g f' g' x s.
          (f has_derivative f') (at x within s) /\\
          (g has_derivative g') (at (f x) within IMAGE f s)
          ==> (g o f has_derivative g' o f') (at x within s)"
#eval thmCheck "derivatives.ml FRECHET_DERIVATIVE_UNIQUE_AT" FRECHET_DERIVATIVE_UNIQUE_AT
  "|- forall f f' f'' x.
          (f has_derivative f') (at x) /\\ (f has_derivative f'') (at x)
          ==> f' = f''"
#eval thmCheck "derivatives.ml HAS_DERIVATIVE_BILINEAR_AT" HAS_DERIVATIVE_BILINEAR_AT
  "|- forall h f g f' g' x.
          (f has_derivative f') (at x) /\\
          (g has_derivative g') (at x) /\\
          bilinear h
          ==> ((\\x. h (f x) (g x)) has_derivative
               (\\d. h (f x) (g' d) + h (f' d) (g x)))
              (at x)"
#eval thmCheck "derivatives.ml HAS_DERIVATIVE_SQNORM_AT" HAS_DERIVATIVE_SQNORM_AT
  "|- forall a.
          ((\\x. lift (norm x pow 2)) has_derivative (\\x. &2 % lift (a dot x)))
          (at a)"

/- ---------------------------------------------------------------------- -/
/- Rolle, mean value theorems and bounds.                                 -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "derivatives.ml DIFFERENTIAL_ZERO_MAXMIN" DIFFERENTIAL_ZERO_MAXMIN
  "|- forall f f' x s.
          x IN s /\\
          open s /\\
          (f has_derivative f') (at x) /\\
          ((forall y. y IN s ==> drop (f y) <= drop (f x)) \\/
           (forall y. y IN s ==> drop (f x) <= drop (f y)))
          ==> f' = (\\v. vec 0)"
#eval thmCheck "derivatives.ml ROLLE" ROLLE
  "|- forall f f' a b.
          drop a < drop b /\\
          f a = f b /\\
          f continuous_on interval [a,b] /\\
          (forall x. x IN interval (a,b) ==> (f has_derivative f' x) (at x))
          ==> (exists x. x IN interval (a,b) /\\ f' x = (\\v. vec 0))"
#eval thmCheck "derivatives.ml MVT" MVT
  "|- forall f f' a b.
          drop a < drop b /\\
          f continuous_on interval [a,b] /\\
          (forall x. x IN interval (a,b) ==> (f has_derivative f' x) (at x))
          ==> (exists x. x IN interval (a,b) /\\ f b - f a = f' x (b - a))"
#eval thmCheck "derivatives.ml MVT_GENERAL" MVT_GENERAL
  "|- forall f f' a b.
          drop a < drop b /\\
          f continuous_on interval [a,b] /\\
          (forall x. x IN interval (a,b) ==> (f has_derivative f' x) (at x))
          ==> (exists x.
                   x IN interval (a,b) /\\
                   norm (f b - f a) <= norm (f' x (b - a)))"
#eval thmCheck "derivatives.ml DIFFERENTIABLE_BOUND" DIFFERENTIABLE_BOUND
  "|- forall f f' s B.
          convex s /\\
          (forall x. x IN s ==> (f has_derivative f' x) (at x within s)) /\\
          (forall x. x IN s ==> onorm (f' x) <= B)
          ==> (forall x y.
                   x IN s /\\ y IN s ==> norm (f x - f y) <= B * norm (x - y))"
#eval thmCheck "derivatives.ml HAS_DERIVATIVE_ZERO_CONNECTED_CONSTANT" HAS_DERIVATIVE_ZERO_CONNECTED_CONSTANT
  "|- forall f s.
          open s /\\
          connected s /\\
          (forall x. x IN s ==> (f has_derivative (\\h. vec 0)) (at x))
          ==> (exists c. forall x. x IN s ==> f x = c)"

/- ---------------------------------------------------------------------- -/
/- Inverse functions, open mappings and sequences of derivatives.         -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "derivatives.ml SUSSMANN_OPEN_MAPPING" SUSSMANN_OPEN_MAPPING
  "|- forall f f' g' s x.
          open s /\\
          f continuous_on s /\\
          x IN s /\\
          (f has_derivative f') (at x) /\\
          linear g' /\\
          f' o g' = I
          ==> (forall t.
                   t SUBSET s /\\ x IN interior t ==> f x IN interior (IMAGE f t))"
#eval thmCheck "derivatives.ml HAS_DERIVATIVE_INVERSE_STRONG" HAS_DERIVATIVE_INVERSE_STRONG
  "|- forall f g f' g' s x.
          open s /\\
          x IN s /\\
          f continuous_on s /\\
          (forall x. x IN s ==> g (f x) = x) /\\
          (f has_derivative f') (at x) /\\
          f' o g' = I
          ==> (g has_derivative g') (at (f x))"
#eval thmCheck "derivatives.ml HAS_DERIVATIVE_SEQUENCE" HAS_DERIVATIVE_SEQUENCE
  "|- forall s f f' g'.
          convex s /\\
          (forall n x. x IN s ==> (f n has_derivative f' n x) (at x within s)) /\\
          (forall e.
               &0 < e
               ==> (exists N.
                        forall n x h.
                            n >= N /\\ x IN s
                            ==> norm (f' n x h - g' x h) <= e * norm h)) /\\
          (exists x l. x IN s /\\ ((\\n. f n x) --> l) sequentially)
          ==> (exists g.
                   forall x.
                       x IN s
                       ==> ((\\n. f n x) --> g x) sequentially /\\
                           (g has_derivative g' x) (at x within s))"
#eval thmCheck "derivatives.ml GATEAUX_DERIVATIVE" GATEAUX_DERIVATIVE
  "|- forall f f' x y.
          (f has_derivative f') (at x)
          ==> ((\\t. inv (drop t) % (f (x + drop t % y) - f x)) --> f' y)
              (at (vec 0))"

/- ---------------------------------------------------------------------- -/
/- The inverse function theorem and the sign of the Jacobian.             -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "derivatives.ml INVERSE_FUNCTION_THEOREM" INVERSE_FUNCTION_THEOREM
  "|- forall f f' a s.
          open s /\\
          a IN s /\\
          (forall x.
               x IN s
               ==> (f has_derivative f' x) (at x) /\\ ~(det (matrix (f' x)) = &0))
          ==> (exists t u g g'.
                   open t /\\
                   a IN t /\\
                   t SUBSET s /\\
                   open u /\\
                   f a IN u /\\
                   homeomorphism (t,u) (f,g) /\\
                   (forall x.
                        x IN t
                        ==> (f has_derivative f' x) (at x) /\\
                            f' x o g' (f x) = I /\\
                            g' (f x) o f' x = I) /\\
                   (forall y.
                        y IN u
                        ==> (g has_derivative g' y) (at y) /\\
                            f' (g y) o g' y = I /\\
                            g' y o f' (g y) = I))"
#eval thmCheck "derivatives.ml JACOBIAN_SIGN_INVARIANCE" JACOBIAN_SIGN_INVARIANCE
  "|- forall f f' s.
          open s /\\
          connected s /\\
          (forall x.
               x IN s
               ==> (f has_derivative f' x) (at x) /\\ ~(det (matrix (f' x)) = &0))
          ==> (forall x. x IN s ==> &0 < det (matrix (f' x))) \\/
              (forall x. x IN s ==> det (matrix (f' x)) < &0)"
#eval thmCheck "derivatives.ml INVERSE_FUNCTION_THEOREM_GLOBAL" INVERSE_FUNCTION_THEOREM_GLOBAL
  "|- forall f f' s t.
          open s /\\
          connected s /\\
          simply_connected t /\\
          (s = {} ==> t = {}) /\\
          (forall c.
               closed_in (subtopology euclidean s) c
               ==> closed_in (subtopology euclidean t) (IMAGE f c)) /\\
          (forall x.
               x IN s
               ==> (f has_derivative f' x) (at x) /\\ ~(det (matrix (f' x)) = &0))
          ==> (exists g g'.
                   homeomorphism (s,t) (f,g) /\\
                   (forall y.
                        y IN t
                        ==> (g has_derivative g' y) (at y) /\\
                            f' (g y) o g' y = I /\\
                            g' y o f' (g y) = I) /\\
                   (forall x.
                        x IN s ==> f' x o g' (f x) = I /\\ g' (f x) o f' x = I))"

/- ---------------------------------------------------------------------- -/
/- Vector derivatives and Kachurovskii's theorem.                         -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "derivatives.ml VECTOR_DERIVATIVE_WORKS" VECTOR_DERIVATIVE_WORKS
  "|- forall net f.
          f differentiable net <=>
          (f has_vector_derivative vector_derivative f net) net"
#eval thmCheck "derivatives.ml CONVEX_ON_DERIVATIVES" CONVEX_ON_DERIVATIVES
  "|- forall f f' s.
          convex s /\\
          (forall x.
               x IN s ==> (lift o f has_derivative lift o f' x) (at x within s))
          ==> (f convex_on s <=>
               (forall x y. x IN s /\\ y IN s ==> f' x (y - x) <= f' y (y - x)))"
