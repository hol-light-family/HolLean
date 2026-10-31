/- File: HolTest/DegreeTest.lean
Runtime test suite: Multivariate/degree.ml
(HolMultiLib/Degree.lean, wired by SessionMultiLib/Degree.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/degree.ml"`, then `string_of_thm`).  The whole file
is also compared with HOL Light by tools/dgdiff: all 388 exported theorems
structurally and by their printed forms.

The theorems chosen here are spread over the file: no retraction of a ball
onto its sphere, the Brouwer fixed point theorem and the hairy ball theorem,
dimension, ARs, ANRs and ENRs, the Borsuk homotopy extension theorem,
deformation retracts, the Bohl, Schauder and Perron-Frobenius theorems, the
Fashoda meet theorem, arc complements and accessibility of ANR complement
components.

Loading degree.ml (`ensureDegree`) builds every bundle in file order; a
proof that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Degree

open HolCore.Kernel Session SessionMultiLib.Degree
open HolTest.CommonTest HolLight.Syntax

#eval ensureDegree

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- No retraction, the Brouwer fixed point and hairy ball theorems.        -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "degree.ml NO_RETRACTION_CBALL" NO_RETRACTION_CBALL
  "|- forall a e. &0 < e ==> ~(sphere (a,e) retract_of cball (a,e))"
#eval thmCheck "degree.ml BROUWER_BALL" BROUWER_BALL
  "|- forall f a e.
          &0 < e /\\
          f continuous_on cball (a,e) /\\
          IMAGE f (cball (a,e)) SUBSET cball (a,e)
          ==> (exists x. x IN cball (a,e) /\\ f x = x)"
#eval thmCheck "degree.ml BROUWER" BROUWER
  "|- forall f s.
          compact s /\\
          convex s /\\
          ~(s = {}) /\\
          f continuous_on s /\\
          IMAGE f s SUBSET s
          ==> (exists x. x IN s /\\ f x = x)"
#eval thmCheck "degree.ml HAIRY_BALL_THEOREM" HAIRY_BALL_THEOREM
  "|- forall r.
          (exists f.
               f continuous_on sphere (vec 0,r) /\\
               IMAGE f (sphere (vec 0,r)) SUBSET sphere (vec 0,r) /\\
               (forall x.
                    x IN sphere (vec 0,r)
                    ==> ~(f x = vec 0) /\\ orthogonal x (f x))) <=>
          r < &0 \\/ &0 < r /\\ EVEN (dimindex (:N))"

/- ---------------------------------------------------------------------- -/
/- Dimension and absolute (neighbourhood) retracts.                       -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "degree.ml DIMENSION_EQ_AFF_DIM" DIMENSION_EQ_AFF_DIM
  "|- forall s. convex s ==> dimension s = aff_dim s"
#eval thmCheck "degree.ml ANR_COMPONENTWISE" ANR_COMPONENTWISE
  "|- forall s.
          ANR s <=>
          COUNTABLE (components s) /\\
          (forall c.
               c IN components s
               ==> open_in (subtopology euclidean s) c /\\ ANR c)"
#eval thmCheck "degree.ml ENR_SPHERE" ENR_SPHERE
  "|- forall a r. ENR (sphere (a,r))"
#eval thmCheck "degree.ml ANR_SPHERE" ANR_SPHERE
  "|- forall a r. ANR (sphere (a,r))"
#eval thmCheck "degree.ml AR_ARC_IMAGE" AR_ARC_IMAGE
  "|- forall g. arc g ==> AR (path_image g)"
#eval thmCheck "degree.ml ABSOLUTE_RETRACT_CONVEX_CLOSED" ABSOLUTE_RETRACT_CONVEX_CLOSED
  "|- forall s t.
          convex s /\\ closed s /\\ ~(s = {}) /\\ s SUBSET t ==> s retract_of t"

/- ---------------------------------------------------------------------- -/
/- Borsuk homotopy extension and deformation retracts.                    -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "degree.ml BORSUK_HOMOTOPY_EXTENSION" BORSUK_HOMOTOPY_EXTENSION
  "|- forall f g s t u.
          closed_in (subtopology euclidean t) s /\\
          (ANR s /\\ ANR t \\/ ANR u) /\\
          f continuous_on t /\\
          IMAGE f t SUBSET u /\\
          homotopic_with (\\x. true)
          (subtopology euclidean s,subtopology euclidean u)
          f
          g
          ==> (exists g'.
                   g' continuous_on t /\\
                   IMAGE g' t SUBSET u /\\
                   (forall x. x IN s ==> g' x = g x))"
#eval thmCheck "degree.ml NULLHOMOTOPIC_INTO_SPHERE_EXTENSION" NULLHOMOTOPIC_INTO_SPHERE_EXTENSION
  "|- forall f s a r.
          closed s /\\
          f continuous_on s /\\
          ~(s = {}) /\\
          IMAGE f s SUBSET sphere (a,r)
          ==> ((exists c.
                    homotopic_with (\\x. true)
                    (subtopology euclidean s,
                     subtopology euclidean (sphere (a,r)))
                    f
                    (\\x. c)) <=>
               (exists g.
                    g continuous_on (:real^M) /\\
                    IMAGE g (:real^M) SUBSET sphere (a,r) /\\
                    (forall x. x IN s ==> g x = f x)))"
#eval thmCheck "degree.ml HOMOTOPY_EQUIVALENT_PUNCTURED_UNIV_SPHERE" HOMOTOPY_EQUIVALENT_PUNCTURED_UNIV_SPHERE
  "|- forall c a r.
          &0 < r ==> (:real^N) DELETE c homotopy_equivalent sphere (a,r)"

/- ---------------------------------------------------------------------- -/
/- Fixed point theorems: Bohl, Schauder, Perron-Frobenius.                -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "degree.ml BOHL" BOHL
  "|- forall f s a.
          f continuous_on s /\\ convex s /\\ compact s /\\ a IN interior s
          ==> (exists x. x IN s /\\ f x = x) \\/
              (exists x. x IN frontier s /\\ x IN segment (a,f x))"
#eval thmCheck "degree.ml BROUWER_AR" BROUWER_AR
  "|- forall f s.
          compact s /\\ AR s /\\ f continuous_on s /\\ IMAGE f s SUBSET s
          ==> (exists x. x IN s /\\ f x = x)"
#eval thmCheck "degree.ml SCHAUDER" SCHAUDER
  "|- forall f s t.
          convex s /\\
          ~(s = {}) /\\
          t SUBSET s /\\
          compact t /\\
          f continuous_on s /\\
          IMAGE f s SUBSET t
          ==> (exists x. x IN s /\\ f x = x)"
#eval thmCheck "degree.ml PERRON_FROBENIUS" PERRON_FROBENIUS
  "|- forall A.
          (forall i j.
               1 <= i /\\ i <= dimindex (:N) /\\ 1 <= j /\\ j <= dimindex (:N)
               ==> &0 <= A$i$j)
          ==> (exists v c. norm v = &1 /\\ &0 <= c /\\ A ** v = c % v)"

/- ---------------------------------------------------------------------- -/
/- Fashoda, arc complements and accessibility of ANR complement components. -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "degree.ml FASHODA" FASHODA
  "|- forall f g a b.
          path f /\\
          path g /\\
          path_image f SUBSET interval [a,b] /\\
          path_image g SUBSET interval [a,b] /\\
          pathstart f$1 = a$1 /\\
          pathfinish f$1 = b$1 /\\
          pathstart g$2 = a$2 /\\
          pathfinish g$2 = b$2
          ==> (exists z. z IN path_image f /\\ z IN path_image g)"
#eval thmCheck "degree.ml CONNECTED_ARC_COMPLEMENT" CONNECTED_ARC_COMPLEMENT
  "|- forall p.
          2 <= dimindex (:N) /\\ arc p
          ==> connected ((:real^N) DIFF path_image p)"
#eval thmCheck "degree.ml ACCESSIBLE_FRONTIER_ANR_COMPLEMENT_COMPONENT" ACCESSIBLE_FRONTIER_ANR_COMPLEMENT_COMPONENT
  "|- forall s c x y.
          compact s /\\
          ANR s /\\
          c IN components ((:real^N) DIFF s) /\\
          x IN c /\\
          y IN frontier c
          ==> (exists g.
                   arc g /\\
                   pathstart g = x /\\
                   pathfinish g = y /\\
                   (forall t.
                        t IN interval [vec 0,vec 1] DELETE vec 1 ==> g t IN c))"
