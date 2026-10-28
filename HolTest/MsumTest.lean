/- File: HolTest/MsumTest.lean
Runtime test suite: Multivariate/msum.ml (HolMultiLib/MSum.lean, wired by
SessionMultiLib/MSum.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/msum.ml"`, then `string_of_thm`).  The whole file is
also compared with HOL Light by tools/msumdiff: all 85 theorems and
definitions structurally.

Loading msum.ml (`ensureMsum`) builds every bundle in file order; a proof
that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.MSum

open HolCore.Kernel Session SessionMultiLib.MSum HolTest.CommonTest HolLight.Syntax

#eval ensureMsum

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- Theorem statements (msum.ml), as HOL Light prints them.  The first one  -/
/- also checks the `norm` overload for matrix_norm (msum.ml 16).            -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "msum.ml matrix_norm" matrix_norm
  "|- forall m. norm m = norm (vectorize m)"
#eval thmCheck "msum.ml msum" msum
  "|- forall s f. msum s f = (lambda i j. sum s (\\x. f x$i$j))"
#eval thmCheck "msum.ml NEUTRAL_MATRIX_ADD" NEUTRAL_MATRIX_ADD
  "|- neutral (+) = mat 0"
#eval thmCheck "msum.ml MSUM_COMPONENT" MSUM_COMPONENT
  "|- forall s f i j. msum s f$i$j = sum s (\\x. f x$i$j)"
#eval thmCheck "msum.ml MSUM_CLAUSES" MSUM_CLAUSES
  "|- (forall f. msum {} f = mat 0) /\\ (forall x f s. FINITE s ==> msum (x INSERT s) f = (if x IN s then msum s f else f x + msum s f))"
#eval thmCheck "msum.ml MSUM_NORM" MSUM_NORM
  "|- forall s f. FINITE s ==> norm (msum s f) <= sum s (\\x. norm (f x))"
#eval thmCheck "msum.ml MSUM_2" MSUM_2
  "|- forall t. msum (1..2) t = t 1 + t 2"
#eval thmCheck "msum.ml MSUM_SWAP_NUMSEG" MSUM_SWAP_NUMSEG
  "|- forall a b c d f. msum (a..b) (\\i. msum (c..d) (f i)) = msum (c..d) (\\j. msum (a..b) (\\i. f i j))"
#eval thmCheck "msum.ml MSUM_REFLECT" MSUM_REFLECT
  "|- forall x m n. msum (m..n) x = (if n < m then mat 0 else msum (0..n - m) (\\i. x (n - i)))"
#eval thmCheck "msum.ml MSUM_PARTIAL_SUC" MSUM_PARTIAL_SUC
  "|- forall f g m n. msum (m..n) (\\k. f k %% (g (k + 1) - g k)) = (if m <= n then f (n + 1) %% g (n + 1) - f m %% g m - msum (m..n) (\\k. (f (k + 1) - f k) %% g (k + 1)) else mat 0)"
