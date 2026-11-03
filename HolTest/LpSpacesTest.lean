/- File: HolTest/LpSpacesTest.lean
Runtime test suite: Multivariate/lpspaces.ml
(HolMultiLib/LpSpaces.lean, wired by SessionMultiLib/LpSpaces.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/lpspaces.ml"`, then `string_of_thm`).  The whole file is also
compared with HOL Light by tools/lpdiff: all exported theorems structurally
and by their printed forms.  The 20 theorems here are spread evenly over the
file; theorems that print with `?nnn` invented type variables are left out.

Loading lpspaces.ml (`ensureLpSpaces`) builds every bundle in file order; a proof
that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.LpSpaces

open HolCore.Kernel Session SessionMultiLib.LpSpaces
open HolTest.CommonTest HolLight.Syntax

#eval ensureLpSpaces

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

#eval thmCheck "lpspaces.ml LSPACE_ALT" LSPACE_ALT
  "|- lspace s p =    {f | f measurable_on s /\\         (\\x. lift (norm (f x) rpow p)) absolutely_integrable_on s}"
#eval thmCheck "lpspaces.ml LSPACE_CMUL" LSPACE_CMUL
  "|- forall s p c f. f IN lspace s p ==> (\\x. c % f x) IN lspace s p"
#eval thmCheck "lpspaces.ml LSPACE_ADD" LSPACE_ADD
  "|- forall s p f g.        &0 <= p /\\ f IN lspace s p /\\ g IN lspace s p        ==> (\\x. f x + g x) IN lspace s p"
#eval thmCheck "lpspaces.ml LSPACE_BOUNDED_MEASURABLE" LSPACE_BOUNDED_MEASURABLE
  "|- forall s p f g.        &0 < p /\\        f measurable_on s /\\        g IN lspace s p /\\        (forall x. x IN s ==> norm (f x) <= norm (g x))        ==> f IN lspace s p"
#eval thmCheck "lpspaces.ml LSPACE_INTEGRABLE_PRODUCT" LSPACE_INTEGRABLE_PRODUCT
  "|- forall s p q f g.        &0 < p /\\        &0 < q /\\        inv p + inv q = &1 /\\        f IN lspace s p /\\        g IN lspace s q        ==> (\\x. lift (norm (f x) * norm (g x))) integrable_on s"
#eval thmCheck "lpspaces.ml LSPACE_INCLUSION" LSPACE_INCLUSION
  "|- forall s p q.        measurable s /\\ &0 < p /\\ p <= q ==> lspace s q SUBSET lspace s p"
#eval thmCheck "lpspaces.ml LNORM_CONST" LNORM_CONST
  "|- forall s p c.        measurable s /\\ &0 < p        ==> lnorm s p (\\x. c) = measure s rpow inv p * norm c"
#eval thmCheck "lpspaces.ml LNORM_NEG" LNORM_NEG
  "|- forall s p f. lnorm s p (\\x. --f x) = lnorm s p f"
#eval thmCheck "lpspaces.ml HOELDER_INEQUALITY" HOELDER_INEQUALITY
  "|- forall s p q f g.        &0 < p /\\        &0 < q /\\        inv p + inv q = &1 /\\        f IN lspace s p /\\        g IN lspace s q        ==> drop (integral s (\\x. lift (norm (f x) * norm (g x)))) <=            lnorm s p f * lnorm s q g"
#eval thmCheck "lpspaces.ml LNORM_TRIANGLE" LNORM_TRIANGLE
  "|- forall s p f g.        f IN lspace s p /\\ g IN lspace s p /\\ &1 <= p        ==> lnorm s p (\\x. f x + g x) <= lnorm s p f + lnorm s p g"
#eval thmCheck "lpspaces.ml LPRODUCT_SYM" LPRODUCT_SYM
  "|- forall s f g.        (\\x. f x * cnj (g x)) integrable_on s        ==> lproduct s f g = cnj (lproduct s g f)"
#eval thmCheck "lpspaces.ml CX_DROP_INTEGRAL" CX_DROP_INTEGRAL
  "|- forall s gg.        gg integrable_on s        ==> integral s (\\x. Cx (drop (gg x))) = Cx (drop (integral s gg))"
#eval thmCheck "lpspaces.ml LPRODUCT_SELF_LNORM" LPRODUCT_SELF_LNORM
  "|- forall s f.        f IN lspace s (&2) ==> lproduct s f f = Cx (lnorm s (&2) f pow 2)"
#eval thmCheck "lpspaces.ml LPRODUCT_RSUM" LPRODUCT_RSUM
  "|- forall s f g k.        FINITE k /\\        (forall i. i IN k ==> (\\x. f x * cnj (g i x)) integrable_on s)        ==> lproduct s f (\\x. vsum k (\\i. g i x)) =            vsum k (\\i. lproduct s f (g i))"
#eval thmCheck "lpspaces.ml LPRODUCT_LSUM" LPRODUCT_LSUM
  "|- forall s g h k.        FINITE k /\\        (forall i. i IN k ==> (\\x. g i x * cnj (h x)) integrable_on s)        ==> lproduct s (\\x. vsum k (\\i. g i x)) h =            vsum k (\\i. lproduct s (g i) h)"
#eval thmCheck "lpspaces.ml L2_CNJ_PRODUCT_INTEGRABLE" L2_CNJ_PRODUCT_INTEGRABLE
  "|- forall s f g.        f IN lspace s (&2) /\\ g IN lspace s (&2)        ==> (\\x. f x * cnj (g x)) integrable_on s"
#eval thmCheck "lpspaces.ml LPRODUCT_LSUB" LPRODUCT_LSUB
  "|- forall a b c s.        a IN lspace s (&2) /\\ b IN lspace s (&2) /\\ c IN lspace s (&2)        ==> lproduct s a c - lproduct s b c = lproduct s (\\x. a x - b x) c"
#eval thmCheck "lpspaces.ml LPRODUCT_L2LIM_RSLOT" LPRODUCT_L2LIM_RSLOT
  "|- forall mn m d s.        (forall n. mn n IN lspace s (&2)) /\\        m IN lspace s (&2) /\\        d IN lspace s (&2) /\\        (forall e.             &0 < e             ==> (exists M.                      forall n. n >= M ==> lnorm s (&2) (\\x. mn n x - m x) < e))        ==> ((\\n. lproduct s d (mn n)) --> lproduct s d m) sequentially"
#eval thmCheck "lpspaces.ml RIESZ_FISCHER" RIESZ_FISCHER
  "|- forall f p s.        &1 <= p /\\        (forall n. f n IN lspace s p) /\\        (forall e.             &0 < e             ==> (exists N.                      forall m n.                          m >= N /\\ n >= N                          ==> lnorm s p (\\x. f m x - f n x) < e))        ==> (exists g.                 g IN lspace s p /\\                 (forall e.                      &0 < e                      ==> (exists N.                               forall n.                                   n >= N ==> lnorm s p (\\x. f n x - g x) < e)))"
#eval thmCheck "lpspaces.ml LSPACE_APPROXIMATE_BOUNDED" LSPACE_APPROXIMATE_BOUNDED
  "|- forall f s p e.        &0 < p /\\ measurable s /\\ f IN lspace s p /\\ &0 < e        ==> (exists g.                 g IN lspace s p /\\                 bounded (IMAGE g s) /\\                 lnorm s p (\\x. f x - g x) < e)"
