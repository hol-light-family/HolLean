/- File: HolTest/CanalTest.lean
Runtime test suite: Multivariate/canal.ml
(HolMultiLib/Canal.lean, wired by SessionMultiLib/Canal.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/canal.ml"`, then `string_of_thm`).  The whole file is also
compared with HOL Light by tools/canaldiff: all exported theorems structurally
and by their printed forms.  The 20 theorems here are spread evenly over the
file; theorems that print with `?nnn` invented type variables are left out.

Loading canal.ml (`ensureCanal`) builds every bundle in file order; a proof
that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Canal

open HolCore.Kernel Session SessionMultiLib.Canal
open HolTest.CommonTest HolLight.Syntax

#eval ensureCanal

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

#eval thmCheck "canal.ml CLOSED_HALFSPACE_RE_GE" CLOSED_HALFSPACE_RE_GE
  "|- forall b. closed {z | Re z >= b}"
#eval thmCheck "canal.ml CONVEX_HALFSPACE_IM_GE" CONVEX_HALFSPACE_IM_GE
  "|- forall b. convex {z | Im z >= b}"
#eval thmCheck "canal.ml CLOSED_REAL" CLOSED_REAL
  "|- closed real"
#eval thmCheck "canal.ml LIM_RE_LBOUND" LIM_RE_LBOUND
  "|- forall net f l b.        ~trivial_limit net /\\        (f --> l) net /\\        eventually (\\x. b <= Re (f x)) net        ==> b <= Re l"
#eval thmCheck "canal.ml CONTINUOUS_CPRODUCT" CONTINUOUS_CPRODUCT
  "|- forall net f k.        FINITE k /\\ (forall i. i IN k ==> f i continuous net)        ==> (\\z. cproduct k (\\i. f i z)) continuous net"
#eval thmCheck "canal.ml CONTINUOUS_ON_CX_RE" CONTINUOUS_ON_CX_RE
  "|- forall s. Cx o Re continuous_on s"
#eval thmCheck "canal.ml HOLOMORPHIC_ON_IMP_CONTINUOUS_ON" HOLOMORPHIC_ON_IMP_CONTINUOUS_ON
  "|- forall f s. f holomorphic_on s ==> f continuous_on s"
#eval thmCheck "canal.ml COMPLEX_DIFF_CHAIN_AT" COMPLEX_DIFF_CHAIN_AT
  "|- forall f g f' g' x.        (f has_complex_derivative f') (at x) /\\        (g has_complex_derivative g') (at (f x))        ==> (g o f has_complex_derivative g' * f') (at x)"
#eval thmCheck "canal.ml HAS_COMPLEX_DERIVATIVE_CDIV_AT" HAS_COMPLEX_DERIVATIVE_CDIV_AT
  "|- forall f f' c x.        (f has_complex_derivative f') (at x)        ==> ((\\x. f x / c) has_complex_derivative f' / c) (at x)"
#eval thmCheck "canal.ml COMPLEX_DIFFERENTIABLE_LINEAR" COMPLEX_DIFFERENTIABLE_LINEAR
  "|- (\\z. c * z) complex_differentiable p"
#eval thmCheck "canal.ml COMPLEX_DIFFERENTIABLE_INV_AT" COMPLEX_DIFFERENTIABLE_INV_AT
  "|- forall f z.        f complex_differentiable at z /\\ ~(f z = Cx (&0))        ==> (\\z. inv (f z)) complex_differentiable at z"
#eval thmCheck "canal.ml HOLOMORPHIC_ON_ADD" HOLOMORPHIC_ON_ADD
  "|- forall f g s.        f holomorphic_on s /\\ g holomorphic_on s        ==> (\\z. f z + g z) holomorphic_on s"
#eval thmCheck "canal.ml COMPLEX_DERIVATIVE_CONST" COMPLEX_DERIVATIVE_CONST
  "|- forall c. complex_derivative (\\w. c) = (\\z. Cx (&0))"
#eval thmCheck "canal.ml ANALYTIC_ON_IMP_DIFFERENTIABLE_AT" ANALYTIC_ON_IMP_DIFFERENTIABLE_AT
  "|- forall f s x. f analytic_on s /\\ x IN s ==> f complex_differentiable at x"
#eval thmCheck "canal.ml ANALYTIC_ON_DIV" ANALYTIC_ON_DIV
  "|- forall f g s.        f analytic_on s /\\        g analytic_on s /\\        (forall z. z IN s ==> ~(g z = Cx (&0)))        ==> (\\z. f z / g z) analytic_on s"
#eval thmCheck "canal.ml COMPLEX_DERIVATIVE_RMUL_AT" COMPLEX_DERIVATIVE_RMUL_AT
  "|- forall f c z.        f analytic_on {z}        ==> complex_derivative (\\w. f w * c) z = complex_derivative f z * c"
#eval thmCheck "canal.ml COMPLEX_TAYLOR" COMPLEX_TAYLOR
  "|- forall f n s B.        convex s /\\        (forall i x.             x IN s /\\ i <= n             ==> (f i has_complex_derivative f (i + 1) x) (at x within s)) /\\        (forall x. x IN s ==> norm (f (n + 1) x) <= B)        ==> (forall w z.                 w IN s /\\ z IN s                 ==> norm                     (f 0 z -                      vsum (0..n) (\\i. f i w * (z - w) pow i / Cx (&(FACT i)))) <=                     B * norm (z - w) pow (n + 1) / &(FACT n))"
#eval thmCheck "canal.ml SERIES_COMPARISON_UNIFORM_COMPLEX" SERIES_COMPARISON_UNIFORM_COMPLEX
  "|- forall f g P s.        summable s g /\\        (forall n. n IN s ==> real (g n) /\\ &0 <= Re (g n)) /\\        (exists N.             forall n x.                 N <= n /\\ n IN s /\\ P x ==> norm (f x n) <= norm (g n))        ==> (exists l.                 forall e.                     &0 < e                     ==> (exists N.                              forall n x.                                  N <= n /\\ P x                                  ==> dist (vsum (s INTER (0..n)) (f x),l x) <                                      e))"
#eval thmCheck "canal.ml REAL_COMPLEX_INTEGRAL" REAL_COMPLEX_INTEGRAL
  "|- forall f s.        f integrable_on s /\\ (forall x. x IN s ==> real (f x))        ==> real (integral s f)"
#eval thmCheck "canal.ml LIM_AT_INFINITY_COMPLEX_0" LIM_AT_INFINITY_COMPLEX_0
  "|- forall f l. (f --> l) at_infinity <=> (f o inv --> l) (at (Cx (&0)))"
