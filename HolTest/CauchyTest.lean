/- File: HolTest/CauchyTest.lean
Runtime test suite: Multivariate/cauchy.ml
(HolMultiLib/Cauchy.lean, wired by SessionMultiLib/Cauchy.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/cauchy.ml"`, then `string_of_thm`).  The whole file is also
compared with HOL Light by tools/cauchydiff: all exported theorems structurally
and by their printed forms.  The 20 theorems here are spread evenly over the
file; theorems that print with `?nnn` invented type variables are left out.

Loading cauchy.ml (`ensureCauchy`) builds every bundle in file order; a proof
that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Cauchy

open HolCore.Kernel Session SessionMultiLib.Cauchy
open HolTest.CommonTest HolLight.Syntax

#eval ensureCauchy

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

#eval thmCheck "cauchy.ml DIFFERENTIABLE_ON_IMP_PIECEWISE_DIFFERENTIABLE" DIFFERENTIABLE_ON_IMP_PIECEWISE_DIFFERENTIABLE
  "|- forall f a b.        f differentiable_on interval [a,b]        ==> f piecewise_differentiable_on interval [a,b]"
#eval thmCheck "cauchy.ml HAS_PATH_INTEGRAL_UNIQUE" HAS_PATH_INTEGRAL_UNIQUE
  "|- forall f i j g.        (f has_path_integral i) g /\\ (f has_path_integral j) g ==> i = j"
#eval thmCheck "cauchy.ml VALID_PATH_LINEPATH" VALID_PATH_LINEPATH
  "|- forall a b. valid_path (linepath (a,b))"
#eval thmCheck "cauchy.ml PATH_INTEGRABLE_CONTINUOUS_LINEPATH" PATH_INTEGRABLE_CONTINUOUS_LINEPATH
  "|- forall f a b.        f continuous_on segment [a,b] ==> f path_integrable_on linepath (a,b)"
#eval thmCheck "cauchy.ml PATH_INTEGRAL_0" PATH_INTEGRAL_0
  "|- forall g. path_integral g (\\x. Cx (&0)) = Cx (&0)"
#eval thmCheck "cauchy.ml CAUCHY_THEOREM_FLAT_LEMMA" CAUCHY_THEOREM_FLAT_LEMMA
  "|- forall f a b c k.        f continuous_on convex hull {a, b, c} /\\        c - a = k % (b - a) /\\        &0 <= k        ==> path_integral (linepath (a,b)) f +            path_integral (linepath (b,c)) f +            path_integral (linepath (c,a)) f =            Cx (&0)"
#eval thmCheck "cauchy.ml VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION" VALID_PATH_VECTOR_POLYNOMIAL_FUNCTION
  "|- forall p. vector_polynomial_function p ==> valid_path p"
#eval thmCheck "cauchy.ml COMPLEX_INTEGER" COMPLEX_INTEGER
  "|- complex_integer z <=> (exists n. integer n /\\ z = Cx n)"
#eval thmCheck "cauchy.ml WINDING_NUMBER_LT_HALF_LINEPATH" WINDING_NUMBER_LT_HALF_LINEPATH
  "|- forall a b z.        ~(z IN segment [a,b])        ==> abs (Re (winding_number (linepath (a,b),z))) < &1 / &2"
#eval thmCheck "cauchy.ml SIMPLY_CONNECTED_IMP_WINDING_NUMBER_ZERO" SIMPLY_CONNECTED_IMP_WINDING_NUMBER_ZERO
  "|- forall s g z.        simply_connected s /\\        path g /\\        path_image g SUBSET s /\\        pathfinish g = pathstart g /\\        ~(z IN s)        ==> winding_number (g,z) = Cx (&0)"
#eval thmCheck "cauchy.ml PATH_CIRCLEPATH" PATH_CIRCLEPATH
  "|- forall z r. path (circlepath (z,r))"
#eval thmCheck "cauchy.ml CAUCHY_NEXT_DERIVATIVE_CIRCLEPATH" CAUCHY_NEXT_DERIVATIVE_CIRCLEPATH
  "|- forall f g z r k.        ~(k = 0) /\\        f continuous_on path_image (circlepath (z,r)) /\\        (forall w.             w IN ball (z,r)             ==> ((\\u. f u / (u - w) pow k) has_path_integral g w)                 (circlepath (z,r)))        ==> (forall w.                 w IN ball (z,r)                 ==> (\\u. f u / (u - w) pow (k + 1)) path_integrable_on                     circlepath (z,r) /\\                     (g has_complex_derivative                      Cx (&k) *                      path_integral (circlepath (z,r))                      (\\u. f u / (u - w) pow (k + 1)))                     (at w))"
#eval thmCheck "cauchy.ml HIGHER_COMPLEX_DERIVATIVE_ADD_AT" HIGHER_COMPLEX_DERIVATIVE_ADD_AT
  "|- forall f g n z.        f analytic_on {z} /\\ g analytic_on {z}        ==> higher_complex_derivative n (\\w. f w + g w) z =            higher_complex_derivative n f z + higher_complex_derivative n g z"
#eval thmCheck "cauchy.ml HOLOMORPHIC_IFF_POWER_SERIES" HOLOMORPHIC_IFF_POWER_SERIES
  "|- forall f z r.        f holomorphic_on ball (z,r) <=>        (forall w.             w IN ball (z,r)             ==> ((\\n.                       higher_complex_derivative n f z / Cx (&(FACT n)) *                       (w - z) pow n) sums                  f w)                 (from 0))"
#eval thmCheck "cauchy.ml POLE_LEMMA_OPEN" POLE_LEMMA_OPEN
  "|- forall f s a.        open s /\\ f holomorphic_on s        ==> (\\z.                 if z = a                 then complex_derivative f a                 else (f z - f a) / (z - a)) holomorphic_on            s"
#eval thmCheck "cauchy.ml CAUCHY_HIGHER_COMPLEX_DERIVATIVE_BOUND" CAUCHY_HIGHER_COMPLEX_DERIVATIVE_BOUND
  "|- forall f z y r B0 n.        &0 < r /\\        0 < n /\\        f holomorphic_on ball (z,r) /\\        f continuous_on cball (z,r) /\\        (forall w. w IN ball (z,r) ==> f w IN ball (y,B0))        ==> norm (higher_complex_derivative n f z) <= &(FACT n) * B0 / r pow n"
#eval thmCheck "cauchy.ml HADAMARD_THREE_LINE_RE" HADAMARD_THREE_LINE_RE
  "|- forall f a b.        f holomorphic_on {z | a < Re z /\\ Re z < b} /\\        f continuous_on {z | a <= Re z /\\ Re z <= b} /\\        bounded (IMAGE f {z | a <= Re z /\\ Re z <= b})        ==> (\\y. sup {norm (f z) | Re z = y}) real_log_convex_on            real_interval [a,b]"
#eval thmCheck "cauchy.ml SCHWARZ_REFLECTION" SCHWARZ_REFLECTION
  "|- forall f s.        open s /\\        (forall z. z IN s ==> cnj z IN s) /\\        f holomorphic_on {z | z IN s /\\ &0 < Im z} /\\        f continuous_on {z | z IN s /\\ &0 <= Im z} /\\        (forall z. z IN s /\\ real z ==> real (f z))        ==> (\\z. if &0 <= Im z then f z else cnj (f (cnj z))) holomorphic_on s"
#eval thmCheck "cauchy.ml MONTEL_OMITTING" MONTEL_OMITTING
  "|- forall f p s a b.        open s /\\        connected s /\\        ~(a = b) /\\        (forall h.             h IN p             ==> h holomorphic_on s /\\                 (forall z. z IN s ==> ~(h z = a) /\\ ~(h z = b))) /\\        (forall n. f n IN p)        ==> (exists r.                 (forall m n. m < n ==> r m < r n) /\\                 ((forall x.                       x IN s                       ==> ((\\n. inv (f (r n) x)) --> Cx (&0)) sequentially) /\\                  (forall k c.                       compact k /\\ k SUBSET s                       ==> (exists N.                                forall n x.                                    n >= N /\\ x IN k ==> c < norm (f (r n) x))) \\/                  (exists g.                       g holomorphic_on s /\\                       (forall x.                            x IN s ==> ((\\n. f (r n) x) --> g x) sequentially) /\\                       (forall k e.                            compact k /\\ k SUBSET s /\\ &0 < e                            ==> (exists N.                                     forall n x.                                         n >= N /\\ x IN k                                         ==> norm (f (r n) x - g x) < e)))))"
#eval thmCheck "cauchy.ml BORSUKIAN_SEPARATION_OPEN_CLOSED" BORSUKIAN_SEPARATION_OPEN_CLOSED
  "|- forall s.        (open s \\/ closed s) /\\ bounded s        ==> (borsukian s <=> connected ((:real^2) DIFF s))"
