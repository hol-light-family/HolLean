/- File: HolTest/ProductsTest.lean
Runtime test suite: Library/products.ml (HolLibrary/Products.lean, wired by
SessionLibrary/Products.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Library/products.ml"`, `set_margin 1000`, then `string_of_thm`).
tools/productsdiff/check.sh compares far more structurally: all 147
theorems, the constants and definitions and all 126 load messages.  The
congruences products.ml adds with `extend_basic_congs` are not in those
dumps, so the `cong` checks below test them through SIMP_TAC. -/

import HolTest.CommonTest
import SessionLibrary

open HolCore.Kernel HolTest.CommonTest

#eval SessionLibrary.Products.ensureProducts

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

namespace P
open Session SessionLibrary.Products HolLight.Syntax

#eval thm' "NPRODUCT_CLAUSES_NUMSEG" NPRODUCT_CLAUSES_NUMSEG
  "|- (forall m. nproduct (m..0) f = (if m = 0 then f 0 else 1)) /\\ (forall m n. nproduct (m..SUC n) f = (if m <= SUC n then nproduct (m..n) f * f (SUC n) else nproduct (m..n) f))"
#eval thm' "NPRODUCT_FACT" NPRODUCT_FACT
  "|- forall n. nproduct (1..n) (\\m. m) = FACT n"
#eval thm' "CONG_NPRODUCT" CONG_NPRODUCT
  "|- forall n f g s. FINITE s /\\ (forall x. x IN s ==> (f x == g x) (mod n)) ==> (nproduct s f == nproduct s g) (mod n)"
#eval thm' "HAS_SIZE_CART" HAS_SIZE_CART
  "|- forall P m. (forall i. 1 <= i /\\ i <= dimindex (:N) ==> {x | P i x} HAS_SIZE m i) ==> {v | forall i. 1 <= i /\\ i <= dimindex (:N) ==> P i (v$i)} HAS_SIZE nproduct (1..dimindex (:N)) m"
#eval thm' "CARD_CART" CARD_CART
  "|- forall P. (forall i. 1 <= i /\\ i <= dimindex (:N) ==> FINITE {x | P i x}) ==> CARD {v | forall i. 1 <= i /\\ i <= dimindex (:N) ==> P i (v$i)} = nproduct (1..dimindex (:N)) (\\i. CARD {x | P i x})"
#eval thm' "IPRODUCT_NEG" IPRODUCT_NEG
  "|- forall f s. FINITE s ==> iproduct s (\\i. --f i) = -- &1 pow CARD s * iproduct s f"
#eval thm' "INT_OF_NUM_NPRODUCT" INT_OF_NUM_NPRODUCT
  "|- forall f s. FINITE s ==> &(nproduct s f) = iproduct s (\\x. &(f x))"
#eval thm' "REAL_OF_NUM_NPRODUCT" REAL_OF_NUM_NPRODUCT
  "|- forall f s. FINITE s ==> &(nproduct s f) = product s (\\x. &(f x))"
#eval thm' "POLYNOMIAL_FUNCTION_PRODUCT" POLYNOMIAL_FUNCTION_PRODUCT
  "|- forall s p. FINITE s /\\ (forall i. i IN s ==> polynomial_function (\\x. p x i)) ==> polynomial_function (\\x. product s (p x))"

-- The congruences from `extend_basic_congs`: SIMP_TAC [] uses the context
-- `1 <= i /\ i <= n` inside `nproduct (1..n)` and `product (1..n)`.
#eval check "cong nproduct"
  (HolLight.prove r"!f n. nproduct(1..n) (\i. if 1 <= i then f i else 1) = nproduct(1..n) f"
     (SIMP_TAC [])).run
  "|- forall f n. nproduct (1..n) (\\i. if 1 <= i then f i else 1) = nproduct (1..n) f"
#eval check "cong product"
  (HolLight.prove r"!f n. product(1..n) (\i. if i <= n then f i else &0) = product(1..n) f"
     (SIMP_TAC [])).run
  "|- forall f n. product (1..n) (\\i. if i <= n then f i else &0) = product (1..n) f"
#eval check "NPRODUCT_CONST_NUMSEG_1 use"
  (do
    match ← HolCore.Parser.parse_term r"nproduct(1..5) (\x. 2)" with
    | .ok t => (REWRITE_CONV [NPRODUCT_CONST_NUMSEG_1] t)
    | .error e => pure (.error e))
  "|- nproduct (1..5) (\\x. 2) = 2 EXP 5"

end P
