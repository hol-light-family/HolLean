/- File: HolTest/IterTest.lean
Runtime test suite: Library/iter.ml (HolLibrary/Iter.lean, wired by
SessionLibrary/Iter.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/iter.ml"`, `set_margin 1000`, then `string_of_thm`).  The
theorems whose printed form contains `?NNN` invented type variables (ITER,
ITER_POINTLESS, ITER_ALT, ITER_1, ...) are tested through conversions on
concrete inputs instead, so no invented type variable appears. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Iter.ensureIter

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def check (lbl : String) (r : IO (Except String thm)) (expected : String) :
    IO Unit := do
  let got ← match ← r with
    | .ok th => pure (squash (← HolCore.Printer.string_of_thm th))
    | .error e => pure s!"FAIL {e}"
  if got == squash expected || got == expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

private unsafe def thm' (lbl : String) (th : thm) (expected : String) : IO Unit :=
  check lbl (pure (.ok th)) expected

namespace I
open Session SessionLibrary.Iter HolLight.Syntax

-- The four "order existence" theorems print with no invented type variables.
#eval thm' "ORDER_EXISTENCE_GEN" ORDER_EXISTENCE_GEN
  "|- forall P f. P (f 0) /\\ (forall m n. P (f m) /\\ ~(m = 0) ==> (P (f (m + n)) <=> P (f n))) ==> (exists d. forall n. P (f n) <=> d divides n)"
#eval thm' "ORDER_EXISTENCE_ITER" ORDER_EXISTENCE_ITER
  "|- forall R f z. R z z /\\ (forall x y. R x y ==> R y x) /\\ (forall x y z. R x y /\\ R y z ==> R x z) /\\ (forall x y. R x y ==> R (f x) (f y)) ==> (exists d. forall n. R (ITER n f z) z <=> d divides n)"
#eval thm' "ORDER_EXISTENCE_CARD" ORDER_EXISTENCE_CARD
  "|- forall R f z k. FINITE {R (ITER n f z) | n IN (:num)} /\\ CARD {R (ITER n f z) | n IN (:num)} <= k /\\ R z z /\\ (forall x y. R x y ==> R y x) /\\ (forall x y z. R x y /\\ R y z ==> R x z) /\\ (forall x y. R (f x) (f y) <=> R x y) ==> (exists d. 0 < d /\\ d <= k /\\ (forall n. R (ITER n f z) z <=> d divides n))"
#eval thm' "ORDER_EXISTENCE_FINITE" ORDER_EXISTENCE_FINITE
  "|- forall R f z. FINITE {R (ITER n f z) | n IN (:num)} /\\ R z z /\\ (forall x y. R x y ==> R y x) /\\ (forall x y z. R x y /\\ R y z ==> R x z) /\\ (forall x y. R (f x) (f y) <=> R x y) ==> (exists d. 0 < d /\\ (forall n. R (ITER n f z) z <=> d divides n))"

-- The recursive definition ITER, used as a rewrite on a concrete iteration,
-- reduces `ITER 2 (\n. n + 1) 0` to `2` (num_CONV unfolds 2 and 1, ITER steps,
-- NUM_REDUCE_CONV adds).  No invented type variable appears.
#eval check "ITER eval 2"
  (do
    match ← HolCore.Parser.parse_term r"ITER 2 (\n. n + 1) 0" with
    | .ok t =>
      (do
        let c1 ← ExceptT.mk (Session.num_CONV (← HolLight.q "2"))
        let c2 ← ExceptT.mk (Session.num_CONV (← HolLight.q "1"))
        ExceptT.mk ((REWRITE_CONV [c1, c2, ITER] THENC Session.NUM_REDUCE_CONV) t)).run
    | .error e => pure (.error e))
  "|- ITER 2 (\\n. n + 1) 0 = 2"

-- ITER_1 as a rewrite: `ITER 1 f x = f x`.
#eval check "ITER_1 use"
  (do
    match ← HolCore.Parser.parse_term r"ITER 1 (f:A->A) x" with
    | .ok t => (REWRITE_CONV [ITER_1] t)
    | .error e => pure (.error e))
  "|- ITER 1 f x = f x"

-- A failure: num_CONV rejects 0 (NUMERAL n with n = 0 is not SUC of anything).
#eval (do
  match ← HolCore.Parser.parse_term r"0" with
  | .ok t =>
    match ← Session.num_CONV t with
    | .ok _ => IO.println "num_CONV 0 -> MISMATCH unexpectedly OK"
    | .error _ => IO.println "num_CONV 0 -> OK (rejected)"
  | .error e => IO.println s!"num_CONV 0 -> MISMATCH parse ERR {e}")

end I
