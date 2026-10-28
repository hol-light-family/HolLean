/- File: HolTest/WlogExamplesTest.lean
Runtime test suite: Multivariate/wlog_examples.ml
(HolMultiLib/WlogExamples.lean, wired by SessionMultiLib/WlogExamples.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/wlog_examples.ml"`, then `string_of_thm`).  The whole file
is also compared with HOL Light by tools/wlogexdiff: all 35 theorems
structurally and by their printed forms.

The theorem checks cover the last binding of `lemma`, the definitions of
`opposite`, `lin_combo` and the sign predicates, and the invariance of the
aff_* sets under translation and injective linear maps.

Loading wlog_examples.ml (`ensureWlogExamples`) builds every bundle in file order; a
proof that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.WlogExamples

open HolCore.Kernel SessionMultiLib.WlogExamples
open HolTest.CommonTest HolLight.Syntax

#eval ensureWlogExamples

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- Theorem statements (wlog_examples.ml), as HOL Light prints them.     -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "wlog_examples.ml lemma" lemma
  "|- forall a b. a$2 <= &0 /\\ &0 <= b$2 ==> (exists x. x IN convex hull {a, b} /\\ x$2 = &0)"
#eval thmCheck "wlog_examples.ml opposite" opposite
  "|- forall p a b. opposite a b p <=> &1 / &2 % (a + b) IN p /\\ (forall x y. {x, y} SUBSET p ==> (x - y) dot (a - b) = &0)"
#eval thmCheck "wlog_examples.ml lin_combo" lin_combo
  "|- forall V f. lin_combo V f = vsum V (\\v. f v % v)"
#eval thmCheck "wlog_examples.ml sgn_gt" sgn_gt "|- sgn_gt = (\\t. &0 < t)"
#eval thmCheck "wlog_examples.ml sgn_ge" sgn_ge "|- sgn_ge = (\\t. &0 <= t)"
#eval thmCheck "wlog_examples.ml sgn_lt" sgn_lt "|- sgn_lt = (\\t. t < &0)"
#eval thmCheck "wlog_examples.ml sgn_le" sgn_le "|- sgn_le = (\\t. t <= &0)"
#eval thmCheck "wlog_examples.ml AFF_GE_INJECTIVE_LINEAR_IMAGE" AFF_GE_INJECTIVE_LINEAR_IMAGE
  "|- forall f s t. linear f /\\ (forall x y. f x = f y ==> x = y) ==> aff_ge (IMAGE f s) (IMAGE f t) = IMAGE f (aff_ge s t)"
#eval thmCheck "wlog_examples.ml AFF_LT_INJECTIVE_LINEAR_IMAGE" AFF_LT_INJECTIVE_LINEAR_IMAGE
  "|- forall f s t. linear f /\\ (forall x y. f x = f y ==> x = y) ==> aff_lt (IMAGE f s) (IMAGE f t) = IMAGE f (aff_lt s t)"
#eval thmCheck "wlog_examples.ml IN_AFFSIGN_TRANSLATION" IN_AFFSIGN_TRANSLATION
  "|- forall sgn s t a v. affsign sgn s t v ==> affsign sgn (IMAGE (\\x. a + x) s) (IMAGE (\\x. a + x) t) (a + v)"
#eval thmCheck "wlog_examples.ml AFFSIGN_TRANSLATION" AFFSIGN_TRANSLATION
  "|- forall a sgn s t. affsign sgn (IMAGE (\\x. a + x) s) (IMAGE (\\x. a + x) t) = IMAGE (\\x. a + x) (affsign sgn s t)"
#eval thmCheck "wlog_examples.ml AFF_GE_TRANSLATION" AFF_GE_TRANSLATION
  "|- forall a s t. aff_ge (IMAGE (\\x. a + x) s) (IMAGE (\\x. a + x) t) = IMAGE (\\x. a + x) (aff_ge s t)"
#eval thmCheck "wlog_examples.ml AFF_LT_TRANSLATION" AFF_LT_TRANSLATION
  "|- forall a s t. aff_lt (IMAGE (\\x. a + x) s) (IMAGE (\\x. a + x) t) = IMAGE (\\x. a + x) (aff_lt s t)"
#eval thmCheck "wlog_examples.ml NOT_COPLANAR_NOT_COLLINEAR" NOT_COPLANAR_NOT_COLLINEAR
  "|- forall v1 v2 v3 w. ~coplanar {v1, v2, v3, w} ==> ~collinear {v1, v2, v3}"
