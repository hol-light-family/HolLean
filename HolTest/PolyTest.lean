/- File: HolTest/PolyTest.lean
Runtime test suite: Library/poly.ml (HolLibrary/Poly.lean, wired by
SessionLibrary/Poly.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/poly.ml"`, then `string_of_thm`, newlines joined).
tools/polydiff/check.sh compares every theorem structurally and as
printed, and the constants and definitions after loading.  Theorems that
print with `?NNN` invented type variables are omitted here. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Poly.ensurePoly

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

namespace T
open Session SessionLibrary.Poly HolLight.Syntax

#eval thm' "poly" poly
  "|- poly [] x = &0 /\\ poly (CONS h t) x = h + x * poly t x"
#eval thm' "LENGTH_POLY_DIFF" LENGTH_POLY_DIFF
  "|- forall l. LENGTH (poly_diff l) = PRE (LENGTH l)"
#eval thm' "POLY_DIFF_LEMMA" POLY_DIFF_LEMMA
  "|- forall l n x.        ((\\x. x pow SUC n * poly l x) diffl         x pow n * poly (poly_diff_aux (SUC n) l) x)        x"
#eval thm' "POLY_DIFF_AUX_ADD" POLY_DIFF_AUX_ADD
  "|- forall p1 p2 n.        poly (poly_diff_aux n (p1 ++ p2)) =        poly (poly_diff_aux n p1 ++ poly_diff_aux n p2)"
#eval thm' "POLY_LINEAR_REM" POLY_LINEAR_REM
  "|- forall t h. exists q r. CONS h t = [r] ++ [--a; &1] ** q"
#eval thm' "POLY_EXP_EQ_0" POLY_EXP_EQ_0
  "|- forall p n. poly (poly_exp p n) = poly [] <=> poly p = poly [] /\\ ~(n = 0)"
#eval thm' "POLY_DIVIDES_REFL" POLY_DIVIDES_REFL
  "|- forall p. poly_divides p p"
#eval thm' "ORDER" ORDER
  "|- forall p a n.        poly_divides (poly_exp [--a; &1] n) p /\\        ~poly_divides (poly_exp [--a; &1] (SUC n)) p <=>        n = order a p /\\ ~(poly p = poly [])"
#eval thm' "RSQUAREFREE_ROOTS" RSQUAREFREE_ROOTS
  "|- forall p.        rsquarefree p <=>        (forall a. ~(poly p a = &0 /\\ poly (poly_diff p) a = &0))"
#eval thm' "NOT_POLY_EXP_NIL" NOT_POLY_EXP_NIL
  "|- forall n p. ~(p = []) ==> ~(poly_exp p n = [])"
#eval thm' "HD_POLY_ADD" HD_POLY_ADD
  "|- forall p1 p2. ~(p1 = []) /\\ ~(p2 = []) ==> HD (p1 ++ p2) = HD p1 + HD p2"
#eval thm' "POLY_CMUL_POLY_DIFF" POLY_CMUL_POLY_DIFF
  "|- forall p c. poly_diff (c ## p) = c ## poly_diff p"
#eval thm' "ITERATE_RADD_POLYADD" ITERATE_RADD_POLYADD
  "|- forall n x f.        iterate (+) (0..n) (\\i. poly (f i) x) = poly (iterate (++) (0..n) f) x"

-- The conversions on sample inputs (expected values printed by HOL Light;
-- a failure is expected as `FAIL <message>`).
#eval check "POLY_DIFF_CONV poly_diff [&1; &2; &3]" (do
    match ← HolCore.Parser.parse_term "poly_diff [&1; &2; &3]" with
    | .ok tm => POLY_DIFF_CONV tm
    | .error e => pure (.error e))
  "|- poly_diff [&1; &2; &3] = [&2; &6]"
#eval check "POLY_DIFF_CONV poly_diff [&1 / &2; &0; -- &3; &4]" (do
    match ← HolCore.Parser.parse_term "poly_diff [&1 / &2; &0; -- &3; &4]" with
    | .ok tm => POLY_DIFF_CONV tm
    | .error e => pure (.error e))
  "|- poly_diff [&1 / &2; &0; -- &3; &4] = [&0; -- &6; &12]"
#eval check "POLY_CMUL_CONV &2 ## [&1; &3 / &4]" (do
    match ← HolCore.Parser.parse_term "&2 ## [&1; &3 / &4]" with
    | .ok tm => POLY_CMUL_CONV tm
    | .error e => pure (.error e))
  "|- &2 ## [&1; &3 / &4] = [&2; &3 / &2]"
#eval check "POLY_ADD_CONV [&1; &2] ++ [&3]" (do
    match ← HolCore.Parser.parse_term "[&1; &2] ++ [&3]" with
    | .ok tm => POLY_ADD_CONV tm
    | .error e => pure (.error e))
  "|- [&1; &2] ++ [&3] = [&4; &2]"
#eval check "POLY_ADD_CONV [&1] ++ [&3; -- &1 / &2; &5]" (do
    match ← HolCore.Parser.parse_term "[&1] ++ [&3; -- &1 / &2; &5]" with
    | .ok tm => POLY_ADD_CONV tm
    | .error e => pure (.error e))
  "|- [&1] ++ [&3; -- &1 / &2; &5] = [&4; -- &1 / &2; &5]"
#eval check "POLY_MUL_CONV [&1; &1] ** [&1; -- &1]" (do
    match ← HolCore.Parser.parse_term "[&1; &1] ** [&1; -- &1]" with
    | .ok tm => POLY_MUL_CONV tm
    | .error e => pure (.error e))
  "|- [&1; &1] ** [&1; -- &1] = [&1; &0; -- &1]"
#eval check "POLY_MUL_CONV [&2; &0; &1] ** [&1 / &3; &4]" (do
    match ← HolCore.Parser.parse_term "[&2; &0; &1] ** [&1 / &3; &4]" with
    | .ok tm => POLY_MUL_CONV tm
    | .error e => pure (.error e))
  "|- [&2; &0; &1] ** [&1 / &3; &4] = [&2 / &3; &8; &1 / &3; &4]"
#eval check "POLY_NORMALIZE_CONV normalize [&1; &0; &0]" (do
    match ← HolCore.Parser.parse_term "normalize [&1; &0; &0]" with
    | .ok tm => POLY_NORMALIZE_CONV tm
    | .error e => pure (.error e))
  "|- normalize [&1; &0; &0] = [&1]"
#eval check "POLY_NORMALIZE_CONV normalize [&0; &2; &0]" (do
    match ← HolCore.Parser.parse_term "normalize [&0; &2; &0]" with
    | .ok tm => POLY_NORMALIZE_CONV tm
    | .error e => pure (.error e))
  "|- normalize [&0; &2; &0] = [&0; &2]"
#eval check "POLY_DIFF_CONV poly_diff []" (do
    match ← HolCore.Parser.parse_term "poly_diff []" with
    | .ok tm => POLY_DIFF_CONV tm
    | .error e => pure (.error e))
  "|- poly_diff [] = []"

end T
