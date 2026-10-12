/- File: HolTest/IsumTest.lean
Runtime test suite: Library/isum.ml (HolLibrary/Isum.lean, wired by
SessionLibrary/Isum.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/isum.ml"`, `set_margin 1000`, then `string_of_thm`).

The suite exercises:
  * a selection of the lifted ISUM theorems and the manually proved ones;
  * `EXPAND_ISUM_CONV` on an empty, a singleton and a split range;
  * the rule `INT_OF_REAL_THM` ITSELF, applied to two real sum theorems that
    isum.ml does NOT lift (`SUM_CLAUSES`, `SUM_ADD_GEN`), to test the rule as
    an independent object (brief: "test the rule itself ... besides the
    theorems"). -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Isum.ensureIsum

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
open Session SessionLibrary.Isum HolLight.Syntax

-- A selection of the lifted theorems.
#eval thm' "int_isum" int_isum
  "|- forall f s. real_of_int (isum s f) = sum s (\\x. real_of_int (f x))"
#eval thm' "ISUM_0" ISUM_0
  "|- forall s. isum s (\\n. &0) = &0"
#eval thm' "ISUM_ADD" ISUM_ADD
  "|- forall f g s. FINITE s ==> isum s (\\x. f x + g x) = isum s f + isum s g"
#eval thm' "ISUM_CONST" ISUM_CONST
  "|- forall c s. FINITE s ==> isum s (\\n. c) = &(CARD s) * c"
#eval thm' "ISUM_SING_NUMSEG" ISUM_SING_NUMSEG
  "|- forall f n. isum (n..n) f = f n"
#eval thm' "ISUM_CLAUSES_NUMSEG" ISUM_CLAUSES_NUMSEG
  "|- (forall m. isum (m..0) f = (if m = 0 then f 0 else &0)) /\\ (forall m n. isum (m..SUC n) f = (if m <= SUC n then isum (m..n) f + f (SUC n) else isum (m..n) f))"
#eval thm' "CARD_EQ_ISUM" CARD_EQ_ISUM
  "|- forall s. FINITE s ==> &(CARD s) = isum s (\\x. &1)"
#eval thm' "INT_SUB_POW" INT_SUB_POW
  "|- forall x y n. 1 <= n ==> x pow n - y pow n = (x - y) * isum (0..n - 1) (\\i. x pow i * y pow (n - 1 - i))"
#eval thm' "REAL_OF_NUM_ISUM" REAL_OF_NUM_ISUM
  "|- forall f s. FINITE s ==> &(nsum s f) = isum s (\\x. &(f x))"

-- The manually proved theorems.
#eval thm' "ISUM_ISUM_PRODUCT" ISUM_ISUM_PRODUCT
  "|- forall s t x. FINITE s /\\ (forall i. i IN s ==> FINITE (t i)) ==> isum s (\\i. isum (t i) (x i)) = isum {i,j | i IN s /\\ j IN t i} (\\(i,j). x i j)"
#eval thm' "ADMISSIBLE_ISUM" ADMISSIBLE_ISUM
  "|- forall (<<) p s h a b. admissible (<<) (\\f (k,x). a x <= k /\\ k <= b x /\\ p f x) (\\(k,x). s x) (\\f (k,x). h f x k) ==> admissible (<<) p s (\\f x. isum (a x..b x) (h f x))"
#eval thm' "INT_SUB_POW_L1" INT_SUB_POW_L1
  "|- forall x n. 1 <= n ==> &1 - x pow n = (&1 - x) * isum (0..n - 1) (\\i. x pow i)"
#eval thm' "ISUM_CLOSED" ISUM_CLOSED
  "|- forall P f s. P (&0) /\\ (forall x y. P x /\\ P y ==> P (x + y)) /\\ (forall a. a IN s ==> P (f a)) ==> P (isum s f)"

-- EXPAND_ISUM_CONV on an empty, a singleton and a split range.
#eval check "EXPAND empty"
  (do match ← HolCore.Parser.parse_term r"isum(5..3) (\i. &i:int)" with
      | .ok t => EXPAND_ISUM_CONV t
      | .error e => pure (.error e))
  "|- isum (5..3) (\\i. &i) = &0"
#eval check "EXPAND single"
  (do match ← HolCore.Parser.parse_term r"isum(2..2) (\i. &i:int)" with
      | .ok t => EXPAND_ISUM_CONV t
      | .error e => pure (.error e))
  "|- isum (2..2) (\\i. &i) = &2"
#eval check "EXPAND split"
  (do match ← HolCore.Parser.parse_term r"isum(1..3) (\i. &i:int)" with
      | .ok t => EXPAND_ISUM_CONV t
      | .error e => pure (.error e))
  "|- isum (1..3) (\\i. &i) = &1 + &2 + &3"

-- The rule INT_OF_REAL_THM itself, on two real theorems isum.ml does NOT lift.
#eval check "rule SUM_CLAUSES" (SessionLibrary.Isum.INT_OF_REAL_THM SUM_CLAUSES)
  "|- (forall f. isum {} f = &0) /\\ (forall x f s. FINITE s ==> isum (x INSERT s) f = (if x IN s then isum s f else f x + isum s f))"
#eval check "rule SUM_ADD_GEN" (SessionLibrary.Isum.INT_OF_REAL_THM SUM_ADD_GEN)
  "|- forall f g s. FINITE {x | x IN s /\\ ~(f x = &0)} /\\ FINITE {x | x IN s /\\ ~(g x = &0)} ==> isum s (\\x. f x + g x) = isum s f + isum s g"

end I
