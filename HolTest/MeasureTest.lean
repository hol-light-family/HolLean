/- File: HolTest/MeasureTest.lean
Runtime test suite: Multivariate/measure.ml
(HolMultiLib/Measure.lean, wired by SessionMultiLib/Measure.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/measure.ml"`, then `string_of_thm`).  The whole file
is also compared with HOL Light by tools/msdiff: all 765 exported theorems
structurally and by their printed forms.

The theorems chosen here are spread over the file: additivity, translation
and scaling of measure, countable unions, convex sets, linear images,
Steinhaus's theorem, sums and limits of measurable functions, negligible
images under differentiable maps, the Vitali covering lemma, Luzin's theorem,
the change of variables formula, the Lebesgue differentiation theorem, the
Banach-Zarecki theorem, Fubini-Tonelli, and the theorems of Rademacher and
Stepanov.

Loading measure.ml (`ensureMeasure`) builds every bundle in file order;
a proof that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Measure

open HolCore.Kernel Session SessionMultiLib.Measure
open HolTest.CommonTest HolLight.Syntax

#eval ensureMeasure

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ----------------------------------------------------------------------- -/
/- Measure: unions, translation, scaling, countable unions, convex sets.   -/
/- ----------------------------------------------------------------------- -/
#eval thmCheck "measure.ml MEASURE_UNION" MEASURE_UNION
  "|- forall s t.
       measurable s /\\ measurable t
       ==> measure (s UNION t) = measure s + measure t - measure (s INTER t)"
#eval thmCheck "measure.ml MEASURE_TRANSLATION" MEASURE_TRANSLATION
  "|- forall a s. measure (IMAGE (\\x. a + x) s) = measure s"
#eval thmCheck "measure.ml MEASURE_SCALING" MEASURE_SCALING
  "|- forall s c.
       measurable s
       ==> measure (IMAGE (\\x. c % x) s) =
           abs c pow dimindex (:N) * measure s"
#eval thmCheck "measure.ml MEASURE_COUNTABLE_UNIONS_LE" MEASURE_COUNTABLE_UNIONS_LE
  "|- forall d B.
       (forall n. measurable (d n)) /\\
       (forall n. sum (0..n) (\\k. measure (d k)) <= B)
       ==> measurable (UNIONS {d n | n IN (:num)}) /\\
           measure (UNIONS {d n | n IN (:num)}) <= B"
#eval thmCheck "measure.ml MEASURABLE_CONVEX" MEASURABLE_CONVEX
  "|- forall s. convex s /\\ bounded s ==> measurable s"

/- ------------------------------------------------- -/
/- Linear images, Steinhaus, measurable functions.   -/
/- ------------------------------------------------- -/
#eval thmCheck "measure.ml NEGLIGIBLE_LINEAR_SINGULAR_IMAGE" NEGLIGIBLE_LINEAR_SINGULAR_IMAGE
  "|- forall f s.
       linear f /\\ ~(forall x y. f x = f y ==> x = y)
       ==> negligible (IMAGE f s)"
#eval thmCheck "measure.ml MEASURE_LINEAR_IMAGE" MEASURE_LINEAR_IMAGE
  "|- forall f s.
       linear f /\\ measurable s
       ==> measure (IMAGE f s) = abs (det (matrix f)) * measure s"
#eval thmCheck "measure.ml STEINHAUS" STEINHAUS
  "|- forall s.
       measurable s /\\ &0 < measure s
       ==> (exists d.
                &0 < d /\\ ball (vec 0,d) SUBSET {x - y | x IN s /\\ y IN s})"
#eval thmCheck "measure.ml MEASURABLE_ON_ADD" MEASURABLE_ON_ADD
  "|- forall f g s.
       f measurable_on s /\\ g measurable_on s
       ==> (\\x. f x + g x) measurable_on s"
#eval thmCheck "measure.ml MEASURABLE_ON_LIMIT" MEASURABLE_ON_LIMIT
  "|- forall f g s k.
       (forall n. f n measurable_on s) /\\
       negligible k /\\
       (forall x. x IN s DIFF k ==> ((\\n. f n x) --> g x) sequentially)
       ==> g measurable_on s"

/- --------------------------------------------------------------- -/
/- Differentiable images, Lebesgue measurability, Vitali, Luzin.   -/
/- --------------------------------------------------------------- -/
#eval thmCheck "measure.ml NEGLIGIBLE_DIFFERENTIABLE_IMAGE_NEGLIGIBLE" NEGLIGIBLE_DIFFERENTIABLE_IMAGE_NEGLIGIBLE
  "|- forall f s.
       dimindex (:M) <= dimindex (:N) /\\
       negligible s /\\
       f differentiable_on s
       ==> negligible (IMAGE f s)"
#eval thmCheck "measure.ml LEBESGUE_MEASURABLE_COUNTABLE_UNIONS" LEBESGUE_MEASURABLE_COUNTABLE_UNIONS
  "|- forall f.
       COUNTABLE f /\\ (forall s. s IN f ==> lebesgue_measurable s)
       ==> lebesgue_measurable (UNIONS f)"
#eval thmCheck "measure.ml VITALI_COVERING_LEMMA_CBALLS" VITALI_COVERING_LEMMA_CBALLS
  "|- forall s a r k B.
       s SUBSET UNIONS (IMAGE (\\i. cball (a i,r i)) k) /\\
       (forall i. i IN k ==> &0 < r i /\\ r i <= B)
       ==> (exists c.
                COUNTABLE c /\\
                c SUBSET k /\\
                pairwise (\\i j. DISJOINT (cball (a i,r i)) (cball (a j,r j)))
                c /\\
                s SUBSET UNIONS (IMAGE (\\i. cball (a i,&5 * r i)) c))"
#eval thmCheck "measure.ml LUZIN" LUZIN
  "|- forall f s e.
       measurable s /\\ f measurable_on s /\\ &0 < e
       ==> (exists k.
                compact k /\\
                k SUBSET s /\\
                measure (s DIFF k) < e /\\
                f continuous_on k)"

/- ------------------------------------------------------------------------ -/
/- Change of variables, Lebesgue differentiation, Banach-Zarecki, Fubini.   -/
/- ------------------------------------------------------------------------ -/
#eval thmCheck "measure.ml HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES" HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES
  "|- forall f g g' s b.
       lebesgue_measurable s /\\
       (forall x. x IN s ==> (g has_derivative g' x) (at x within s)) /\\
       (forall x y. x IN s /\\ y IN s /\\ g x = g y ==> x = y)
       ==> ((\\x. abs (det (matrix (g' x))) % f (g x)) absolutely_integrable_on
            s /\\
            integral s (\\x. abs (det (matrix (g' x))) % f (g x)) = b <=>
            f absolutely_integrable_on IMAGE g s /\\
            integral (IMAGE g s) f = b)"
#eval thmCheck "measure.ml LEBESGUE_DIFFERENTIATION_THEOREM" LEBESGUE_DIFFERENTIATION_THEOREM
  "|- forall f s.
       is_interval s /\\ f has_bounded_variation_on s
       ==> negligible {x | x IN s /\\ ~(f differentiable at x)}"
#eval thmCheck "measure.ml BANACH_ZARECKI" BANACH_ZARECKI
  "|- forall f a b.
       f absolutely_continuous_on interval [a,b] <=>
       f continuous_on interval [a,b] /\\
       f has_bounded_variation_on interval [a,b] /\\
       (forall t.
            t SUBSET interval [a,b] /\\ negligible t
            ==> negligible (IMAGE f t))"
#eval thmCheck "measure.ml FUBINI_TONELLI" FUBINI_TONELLI
  "|- forall f.
       f measurable_on (:real^(M,N)finite_sum)
       ==> (f absolutely_integrable_on (:real^(M,N)finite_sum) <=>
            negligible
            {x | ~((\\y. f (pastecart x y)) absolutely_integrable_on
                   (:real^N))} /\\
            (\\x. integral (:real^N) (\\y. lift (norm (f (pastecart x y))))) integrable_on
            (:real^M))"

/- --------------------------------------- -/
/- Rademacher's and Stepanov's theorems.   -/
/- --------------------------------------- -/
#eval thmCheck "measure.ml RADEMACHER" RADEMACHER
  "|- forall f s.
       (exists B.
            forall x y.
                x IN s /\\ y IN s ==> norm (f x - f y) <= B * norm (x - y))
       ==> negligible {x | x IN s /\\ ~(f differentiable at x within s)}"
#eval thmCheck "measure.ml STEPANOV_UNIV" STEPANOV_UNIV
  "|- forall f.
       negligible
       {x | (exists B.
                 eventually (\\y. norm (f x - f y) / norm (x - y) <= B) (at x)) /\\
            ~(f differentiable at x)}"
