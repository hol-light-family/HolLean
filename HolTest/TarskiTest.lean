/- File: HolTest/TarskiTest.lean
Runtime test suite: Multivariate/tarski.ml
(HolMultiLib/Tarski.lean, wired by SessionMultiLib/Tarski.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/tarski.ml"`, then `string_of_thm`).  The whole file
is also compared with HOL Light by tools/tarskidiff: all 11 theorems
structurally and by their printed forms.

The theorem checks cover the eight of the eleven Euclidean Tarski axioms
whose printed forms contain no invented type variables.

Loading tarski.ml (`ensureTarski`) builds every bundle in file order; a
proof that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Tarski

open HolCore.Kernel SessionMultiLib.Tarski
open HolTest.CommonTest HolLight.Syntax

#eval ensureTarski

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- Theorem statements (tarski.ml), as HOL Light prints them.            -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "tarski.ml TARSKI_AXIOM_1_EUCLIDEAN" TARSKI_AXIOM_1_EUCLIDEAN
  "|- forall a b. dist (a,b) = dist (b,a)"
#eval thmCheck "tarski.ml TARSKI_AXIOM_4_EUCLIDEAN" TARSKI_AXIOM_4_EUCLIDEAN
  "|- forall a q b c. exists x. between a (q,x) /\\ dist (a,x) = dist (b,c)"
#eval thmCheck "tarski.ml TARSKI_AXIOM_5_EUCLIDEAN" TARSKI_AXIOM_5_EUCLIDEAN
  "|- forall a b c x a' b' c' x'. ~(a = b) /\\ dist (a,b) = dist (a',b') /\\ dist (a,c) = dist (a',c') /\\ dist (b,c) = dist (b',c') /\\ between b (a,x) /\\ between b' (a',x') /\\ dist (b,x) = dist (b',x') ==> dist (c,x) = dist (c',x')"
#eval thmCheck "tarski.ml TARSKI_AXIOM_7_EUCLIDEAN" TARSKI_AXIOM_7_EUCLIDEAN
  "|- forall a b c p q. between p (a,c) /\\ between q (b,c) ==> (exists x. between x (p,b) /\\ between x (q,a))"
#eval thmCheck "tarski.ml TARSKI_AXIOM_8_EUCLIDEAN" TARSKI_AXIOM_8_EUCLIDEAN
  "|- exists a b c. ~between b (a,c) /\\ ~between c (b,a) /\\ ~between a (c,b)"
#eval thmCheck "tarski.ml TARSKI_AXIOM_9_EUCLIDEAN" TARSKI_AXIOM_9_EUCLIDEAN
  "|- forall p q a b c. ~(p = q) /\\ dist (a,p) = dist (a,q) /\\ dist (b,p) = dist (b,q) /\\ dist (c,p) = dist (c,q) ==> between b (a,c) \\/ between c (b,a) \\/ between a (c,b)"
#eval thmCheck "tarski.ml TARSKI_AXIOM_10_EUCLIDEAN" TARSKI_AXIOM_10_EUCLIDEAN
  "|- forall a b c d t. between d (a,t) /\\ between d (b,c) /\\ ~(a = d) ==> (exists x y. between b (a,x) /\\ between c (a,y) /\\ between t (x,y))"
#eval thmCheck "tarski.ml TARSKI_AXIOM_11_EUCLIDEAN" TARSKI_AXIOM_11_EUCLIDEAN
  "|- forall X Y. (exists a. forall x y. x IN X /\\ y IN Y ==> between x (a,y)) ==> (exists b. forall x y. x IN X /\\ y IN Y ==> between b (x,y))"
