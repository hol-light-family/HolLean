/- File: HolTest/DeterminantsTest.lean
Runtime test suite: Multivariate/determinants.ml (HolMultiLib/Determinants.lean,
wired by SessionMultiLib/Determinants.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/determinants.ml"`, then `string_of_thm`, or `length` for
the counts).  The whole file is also compared with HOL Light by
tools/detdiff: all 319 theorems and definitions structurally, and the
contents of invariant_under_linear, invariant_under_translation and
scaling_theorems after loading determinants.ml.

The theorems and goals chosen here print without invented type variables,
so their printed forms do not depend on type-variable numbering.

Loading determinants.ml (`ensureDeterminants`) builds every bundle in file
order; a proof that failed would stop the load, which the `make verify` gates
catch. -/

import HolTest.CommonTest
import SessionMultiLib.Determinants

open HolCore.Kernel Session SessionMultiLib.Vectors SessionMultiLib.Determinants
open HolTest.CommonTest HolLight.Syntax

#eval ensureDeterminants

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
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

/-- Compare a count computed by a rule with HOL Light's. -/
private def countCheck (lbl : String) (r : ExceptT String IO Nat) (expected : Nat) :
    IO Unit := do
  match ← r.run with
  | Except.ok n =>
    if n == expected then IO.println s!"{lbl} -> OK"
    else IO.println s!"{lbl} -> MISMATCH got={n}"
  | Except.error e => IO.println s!"{lbl} -> MISMATCH FAIL {e}"

private def tm (s : String) : ExceptT String IO term := ExceptT.mk (HolCore.Parser.parse_term s)

/- ---------------------------------------------------------------------- -/
/- Theorem statements (determinants.ml), as HOL Light prints them.         -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "determinants.ml det" det
  "|- forall A. det A = sum {p | p permutes 1..dimindex (:N)} (\\p. sign p * product (1..dimindex (:N)) (\\i. A$i$p i))"
#eval thmCheck "determinants.ml trace" trace
  "|- forall A. trace A = sum (1..dimindex (:N)) (\\i. A$i$i)"
#eval thmCheck "determinants.ml DET_2" DET_2
  "|- forall A. det A = A$1$1 * A$2$2 - A$1$2 * A$2$1"
#eval thmCheck "determinants.ml cofactor" cofactor
  "|- forall A. cofactor A = (lambda i j. det (lambda k l. if k = i /\\ l = j then &1 else if k = i \\/ l = j then &0 else A$k$l))"
#eval thmCheck "determinants.ml CRAMER" CRAMER
  "|- forall A x b. ~(det A = &0) ==> (A ** x = b <=> x = (lambda k. det (lambda i j. if j = k then b$i else A$i$j) / det A))"
#eval thmCheck "determinants.ml DET_COFACTOR_EXPANSION" DET_COFACTOR_EXPANSION
  "|- forall A i. 1 <= i /\\ i <= dimindex (:N) ==> det A = sum (1..dimindex (:N)) (\\j. A$i$j * cofactor A$i$j)"
#eval thmCheck "determinants.ml HADAMARD_INEQUALITY_ROW" HADAMARD_INEQUALITY_ROW
  "|- forall A. abs (det A) <= product (1..dimindex (:N)) (\\i. norm (row i A))"
#eval thmCheck "determinants.ml reflect_along" reflect_along
  "|- forall x v. reflect_along v x = x - (&2 * (x dot v) / (v dot v)) % v"
#eval thmCheck "determinants.ml ROTATION_EXISTS" ROTATION_EXISTS
  "|- forall a b. 2 <= dimindex (:N) /\\ norm a = norm b ==> (exists f. orthogonal_transformation f /\\ det (matrix f) = &1 /\\ f a = b)"

/- determinants.ml 3059 binds a (term, tactic) pair; check the term. -/
#eval show IO Unit from do
  let got := squash (← HolCore.Printer.string_of_term ORTHOGONAL_TRANSFORMATION_ADJOINT_EQ.1)
  let exp := squash "forall f. linear f ==> (orthogonal_transformation (adjoint f) <=> orthogonal_transformation f)"
  if got == exp then IO.println "determinants.ml ORTHOGONAL_TRANSFORMATION_ADJOINT_EQ -> OK"
  else IO.println s!"determinants.ml ORTHOGONAL_TRANSFORMATION_ADJOINT_EQ -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- The GEOM conversions, rules and tactics (determinants.ml 4411-4956).     -/
/- ---------------------------------------------------------------------- -/
#eval ruleCheck "determinants.ml GEOM_ORIGIN_CONV"
  (do ExceptT.mk (GEOM_ORIGIN_CONV [] (← tm "!a:real^N b. dist(a,b) = norm(b - a)")))
  "|- (forall a b. dist (a,b) = norm (b - a)) <=> (forall b. dist (vec 0,b) = norm (b - vec 0))"
#eval ruleCheck "determinants.ml GEOM_TRANSLATE_CONV"
  (do ExceptT.mk (GEOM_TRANSLATE_CONV [] (← tm "a:real^N") (← tm "!x:real^N. norm(x) = &1")))
  "|- (forall x. norm x = &1) <=> (forall x. norm (a + x) = &1)"
#eval ruleCheck "determinants.ml GEOM_BASIS_MULTIPLE_RULE"
  (do GEOM_BASIS_MULTIPLE_RULE 1 (← tm "!x:real^N. norm x = &1"))
  "|- (forall x. &0 <= x ==> norm (x % basis 1) = &1) ==> (forall x. norm x = &1)"
#eval ruleCheck "determinants.ml GEOM_NORMALIZE_RULE"
  (do GEOM_NORMALIZE_RULE [] (← tm "!b:real^N c. orthogonal b c <=> orthogonal c b"))
  "|- (forall c. orthogonal (vec 0) c <=> orthogonal c (vec 0)) /\\ (forall b. norm b = &1 ==> (forall c. orthogonal b c <=> orthogonal c b)) ==> (forall b c. orthogonal b c <=> orthogonal c b)"
#eval ruleCheck "determinants.ml GEOM_EQUAL_DIMENSION_RULE"
  (do GEOM_EQUAL_DIMENSION_RULE (← HolLight.ASSUME (← tm "dimindex(:M) = dimindex(:N)"))
        (← HolLight.ISPEC (← tm "x:real^N") NORM_POS_LE))
  "dimindex (:M) = dimindex (:N) |- &0 <= norm x"
#eval ruleCheck "determinants.ml GEOM_DROP_DIMENSION_RULE"
  (do GEOM_DROP_DIMENSION_RULE
        (← HolLight.prove "dimindex(:2) <= dimindex(:3)"
             (REWRITE_TAC [DIMINDEX_2, DIMINDEX_3] THEN ARITH_TAC))
        (← HolLight.ISPEC (← tm "x:real^3") NORM_POS_LE))
  "|- forall x. &0 <= norm x"
#eval ruleCheck "determinants.ml GEOM_ORIGIN_TAC"
  (HolLight.prove "!a b:real^N. dist(a,b) = dist(b,a)"
    (HolLight.tactic_of (do pure (GEOM_ORIGIN_TAC (← tm "a:real^N"))) THEN
     REWRITE_TAC [DIST_SYM]))
  "|- forall a b. dist (a,b) = dist (b,a)"
#eval ruleCheck "determinants.ml GEOM_TRANSLATE_TAC"
  (HolLight.prove "!a:real^N x. norm(a + x) = norm(a + x)"
    (GEOM_TRANSLATE_TAC [] THEN REWRITE_TAC []))
  "|- forall a x. norm (a + x) = norm (a + x)"
#eval ruleCheck "determinants.ml GEOM_BASIS_MULTIPLE_TAC"
  (HolLight.prove "!x:real^N. &0 <= norm x"
    (HolLight.tactic_of (do pure (GEOM_BASIS_MULTIPLE_TAC 1 (← tm "x:real^N"))) THEN
     REWRITE_TAC [NORM_POS_LE]))
  "|- forall x. &0 <= norm x"
#eval ruleCheck "determinants.ml GEOM_NORMALIZE_TAC"
  (HolLight.prove "!b:real^N c. orthogonal b c <=> orthogonal c b"
    (HolLight.tactic_of (do pure (GEOM_NORMALIZE_TAC (← tm "b:real^N"))) THEN
     REWRITE_TAC [ORTHOGONAL_SYM]))
  "|- forall b c. orthogonal b c <=> orthogonal c b"
#eval ruleCheck "determinants.ml GEOM_TRANSFORM_TAC"
  (HolLight.prove "!f:real^M->real^N x y. linear f /\\ (!x. norm(f x) = norm x) ==> (orthogonal (f x) (f y) <=> orthogonal x y)"
    (GEOM_TRANSFORM_TAC []))
  "|- forall f x y. linear f /\\ (forall x. norm (f x) = norm x) ==> (orthogonal (f x) (f y) <=> orthogonal x y)"

/- EXISTS_GENVAR_RULE renames to a genvar, whose number differs; check the
   hypothesis count, as HOL Light reports it. -/
#eval countCheck "determinants.ml EXISTS_GENVAR_RULE"
  (do pure (hyp (← EXISTS_GENVAR_RULE (← HolLight.ASSUME (← tm "?n:num. n = 1")))).length) 1

#eval countCheck "determinants.ml SCALING_THEOREMS"
  (do pure (HolLight.CONJUNCTS (← SCALING_THEOREMS (← tm "x:real^N"))).length) 81
#eval countCheck "determinants.ml TRANSLATION_INVARIANTS"
  (do pure (HolLight.CONJUNCTS (← TRANSLATION_INVARIANTS (← tm "a:real^N"))).length) 57
#eval countCheck "determinants.ml LINEAR_INVARIANTS"
  (do
    let a ← HolLight.ASSUME (← tm "linear(f:real^N->real^N) /\\ (!x. norm(f x) = norm x)")
    pure (HolLight.CONJUNCTS (← LINEAR_INVARIANTS (← tm "f:real^N->real^N")
      (HolLight.CONJUNCTS a))).length) 65

#eval do
  let n1 := (← invariant_under_linear.get).length
  let n2 := (← invariant_under_translation.get).length
  let n3 := (← scaling_theorems.get).length
  if (n1, n2, n3) == (65, 57, 81) then IO.println "determinants.ml invariance list lengths -> OK"
  else IO.println s!"determinants.ml invariance list lengths -> MISMATCH got={n1} {n2} {n3}"
