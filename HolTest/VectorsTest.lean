/- File: HolTest/VectorsTest.lean
Runtime test suite: Multivariate/vectors.ml (HolMultiLib/Vectors.lean, wired by
SessionMultiLib/Vectors.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/vectors.ml"`, then `string_of_thm`).  The whole file is
also compared with HOL Light by tools/vecdiff: all 1198 theorems and
definitions structurally, NORM_ARITH on seven goals, EXPAND_VSUM_CONV on
three sums, a SIMP_CONV that uses the vsum congruences, and the contents of
invariant_under_linear, invariant_under_translation and scaling_theorems.

The theorems chosen here print without invented type variables, so their
printed forms do not depend on type-variable numbering.

Loading vectors.ml (`ensureVectors`) builds every bundle in file order; a
proof that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Vectors

open HolCore.Kernel Session SessionMultiLib.Vectors HolTest.CommonTest HolLight.Syntax

#eval ensureVectors

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/-- Apply a conversion to a parsed term; compare the theorem, or `FAIL msg`. -/
private unsafe def convCheck (lbl : String) (c : HolCore.Equal.ioconv) (s expected : String) :
    IO Unit := do
  let got ← match ← HolCore.Parser.parse_term s with
    | Except.error e => pure s!"FAIL parse: {e}"
    | Except.ok tm => do
      match ← c tm with
      | Except.ok th => pure (squash (← HolCore.Printer.string_of_thm th))
      | Except.error e => pure s!"FAIL {e}"
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/-- Run a derived rule; compare the theorem, or `FAIL msg`. -/
private unsafe def ruleCheck (lbl : String) (r : ExceptT String IO thm) (expected : String) :
    IO Unit := do
  let got ← match ← r.run with
    | Except.ok th => pure (squash (← HolCore.Printer.string_of_thm th))
    | Except.error e => pure s!"FAIL {e}"
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- Theorem statements (vectors.ml), as HOL Light prints them.             -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "vectors.ml BASIS_EXPANSION" BASIS_EXPANSION
  "|- forall x. vsum (1..dimindex (:N)) (\\i. x$i % basis i) = x"
#eval thmCheck "vectors.ml MATRIX_MUL_ASSOC" MATRIX_MUL_ASSOC
  "|- forall A B C. A ** B ** C = (A ** B) ** C"
#eval thmCheck "vectors.ml DIM_UNIV" DIM_UNIV
  "|- dim (:real^N) = dimindex (:N)"
#eval thmCheck "vectors.ml RANK_TRANSP" RANK_TRANSP
  "|- forall A. rank (transp A) = rank A"
#eval thmCheck "vectors.ml MATRIX_INV_INV" MATRIX_INV_INV
  "|- forall A. matrix_inv (matrix_inv A) = A"
#eval thmCheck "vectors.ml COLLINEAR_3_EXPAND" COLLINEAR_3_EXPAND
  "|- forall a b c. collinear {a, b, c} <=> a = c \\/ (exists u. b = u % a + (&1 - u) % c)"
#eval thmCheck "vectors.ml IN_INTERVAL" IN_INTERVAL
  "|- (forall x. x IN interval (a,b) <=> (forall i. 1 <= i /\\ i <= dimindex (:N) ==> a$i < x$i /\\ x$i < b$i)) /\\ (forall x. x IN interval [a,b] <=> (forall i. 1 <= i /\\ i <= dimindex (:N) ==> a$i <= x$i /\\ x$i <= b$i))"
#eval thmCheck "vectors.ml EUCLIDEAN_MATROID_DIM" EUCLIDEAN_MATROID_DIM
  "|- matroid_dim euclidean_matroid = dim"
#eval thmCheck "vectors.ml dim" dim
  "|- forall v. dim v = (@n. exists b. b SUBSET v /\\ independent b /\\ v SUBSET span b /\\ b HAS_SIZE n)"
#eval thmCheck "vectors.ml BESSEL_INEQUALITY" BESSEL_INEQUALITY
  "|- forall s x. pairwise orthogonal s /\\ (forall x. x IN s ==> norm x = &1) ==> sum s (\\e. (e dot x) pow 2) <= norm x pow 2"
#eval thmCheck "vectors.ml RANK_SYLVESTER" RANK_SYLVESTER
  "|- forall A B. rank A + rank B <= rank (A ** B) + dimindex (:N)"

/- ---------------------------------------------------------------------- -/
/- Decision procedures and conversions, as HOL Light prints their results. -/
/- ---------------------------------------------------------------------- -/
#eval convCheck "vectors.ml VECTOR_ARITH" VECTOR_ARITH
  "!x y:real^N. (x + y) - y = x"
  "|- forall x y. (x + y) - y = x"
#eval convCheck "vectors.ml NORM_ARITH" NORM_ARITH
  "!x y:real^N. norm(x) <= norm(x - y) + norm(y)"
  "|- forall x y. norm x <= norm (x - y) + norm y"
#eval convCheck "vectors.ml MATRIX_ARITH" MATRIX_ARITH
  "!A B:real^N^N. A + B = B + A"
  "|- forall A B. A + B = B + A"
#eval convCheck "vectors.ml EXPAND_VSUM_CONV" EXPAND_VSUM_CONV
  "vsum(1..2) (\\i. &i % (x:real^2))"
  "|- vsum (1..2) (\\i. &i % x) = &1 % x + &2 % x"

/- ---------------------------------------------------------------------- -/
/- The invariance machinery (vectors.ml 10301-10797).                      -/
/- ---------------------------------------------------------------------- -/
#eval ruleCheck "vectors.ml SCALING_INVARIANT" (SCALING_INVARIANT SUBSPACE_LINEAR_IMAGE_EQ)
  "|- forall c. &0 < c ==> (forall s. subspace (IMAGE (\\x. c % x) s) <=> subspace s)"
#eval ruleCheck "vectors.ml EXPAND_QUANTS_CONV" (do
    let sth ← ExceptT.mk (Session.MESON [VECTOR_NEG_NEG]
      (← ExceptT.mk (HolCore.Parser.parse_term "!y:real^N. ?x. --x = y")))
    let qth ← ExceptT.mk (Session.MATCH_MP QUANTIFY_SURJECTION_THM sth)
    let c ← EXPAND_QUANTS_CONV qth
    ExceptT.mk (c (← ExceptT.mk (HolCore.Parser.parse_term "!x:real^N. ?y. x = y"))))
  "|- (forall x. exists y. x = y) <=> (forall x. exists y. --x = --y)"
#eval do
  let n1 := (← invariant_under_linear.get).length
  let n2 := (← invariant_under_translation.get).length
  let n3 := (← scaling_theorems.get).length
  if (n1, n2, n3) == (63, 56, 80) then IO.println "vectors.ml invariance list lengths -> OK"
  else IO.println s!"vectors.ml invariance list lengths -> MISMATCH got={n1} {n2} {n3}"
