/- File: HolTest/MiscTest.lean
Runtime test suite: Multivariate/misc.ml (HolMultiLib/Misc.lean, wired by
SessionMultiLib/Misc.lean).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

FAITHFULNESS BASIS.  Every expected value below was printed by real HOL Light
(`needs "Multivariate/misc.ml"`, then `string_of_thm`).  The whole file is
also compared with HOL Light by tools/miscdiff: all 190 theorems and
definitions structurally, and HORNER_SUM_CONV on two sums.

Loading misc.ml (`ensureMisc`) builds every bundle in file order; a proof
that failed would stop the load, which the `make verify` gates catch. -/

import HolTest.CommonTest
import SessionMultiLib.Misc

open HolCore.Kernel Session SessionMultiLib.Misc HolTest.CommonTest HolLight.Syntax

#eval ensureMisc

/-- Strip spaces and newlines, so line breaking does not matter. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/-- Apply HORNER_SUM_CONV; compare the theorem, or `FAIL msg`. -/
private unsafe def convCheck (lbl : String) (s expected : String) : IO Unit := do
  let got ← match ← HolCore.Parser.parse_term s with
    | Except.error e => pure s!"FAIL parse: {e}"
    | Except.ok tm => do
      match ← HORNER_SUM_CONV tm with
      | Except.ok th => pure (squash (← HolCore.Printer.string_of_thm th))
      | Except.error e => pure s!"FAIL {e}"
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/-- Prove a goal with a tactic; compare the theorem, or `FAIL msg`. -/
private unsafe def tacCheck (lbl : String) (s : String) (tac : HolCore.Tactics.tactic)
    (expected : String) : IO Unit := do
  let got ← match ← HolCore.Parser.parse_term s with
    | Except.error e => pure s!"FAIL parse: {e}"
    | Except.ok tm => do
      match ← Session.prove tm tac with
      | Except.ok th => pure (squash (← HolCore.Printer.string_of_thm th))
      | Except.error e => pure s!"FAIL {e}"
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- Theorem statements (misc.ml), as HOL Light prints them.                -/
/- ---------------------------------------------------------------------- -/
#eval thmCheck "misc.ml REAL_HALF" REAL_HALF
  "|- (forall e. &0 < e / &2 <=> &0 < e) /\\ (forall e. e / &2 + e / &2 = e) /\\ (forall e. &2 * e / &2 = e)"
#eval thmCheck "misc.ml real_interval" real_interval
  "|- real_interval (a,b) = {x | a < x /\\ x < b} /\\ real_interval [a,b] = {x | a <= x /\\ x <= b}"
#eval thmCheck "misc.ml IN_REAL_INTERVAL" IN_REAL_INTERVAL
  "|- forall a b x. (x IN real_interval [a,b] <=> a <= x /\\ x <= b) /\\ (x IN real_interval (a,b) <=> a < x /\\ x < b)"
#eval thmCheck "misc.ml vectorize" vectorize
  "|- vectorize = (\\x. lambda i. x$(1 + (i - 1) DIV dimindex (:N))$(1 + (i - 1) MOD dimindex (:N)))"
#eval thmCheck "misc.ml IN_FROM" IN_FROM
  "|- forall m n. m IN from n <=> n <= m"
#eval thmCheck "misc.ml SUM_GP" SUM_GP
  "|- forall x m n. sum (m..n) (\\i. x pow i) = (if n < m then &0 else if x = &1 then &((n + 1) - m) else (x pow m - x pow SUC n) / (&1 - x))"
#eval thmCheck "misc.ml COUNTABLE_RATIONAL" COUNTABLE_RATIONAL
  "|- COUNTABLE rational"
#eval thmCheck "misc.ml IRRATIONAL_BETWEEN" IRRATIONAL_BETWEEN
  "|- forall a b. a < b ==> (exists q. ~rational q /\\ a < q /\\ q < b)"
#eval thmCheck "misc.ml GENERAL_REDUCTION_THEOREM_2" GENERAL_REDUCTION_THEOREM_2
  "|- forall P. P {} /\\ (forall s t. P s /\\ P t ==> P (s UNION t)) /\\ (forall s t. P s /\\ P t ==> P (s DIFF t)) ==> (forall s t. (COUNTABLE UNION_OF P) s /\\ (COUNTABLE UNION_OF P) t ==> (exists s' t'. (COUNTABLE UNION_OF P) s' /\\ (COUNTABLE UNION_OF P) t' /\\ s' SUBSET s /\\ t' SUBSET t /\\ DISJOINT s' t' /\\ s' UNION t' = s UNION t))"
#eval thmCheck "misc.ml RECURSION_ON_DYADIC_FRACTIONS" RECURSION_ON_DYADIC_FRACTIONS
  "|- forall R a b. (forall x y z. R x y /\\ R y z ==> R x z) /\\ R a b /\\ (forall x y. R x y ==> (exists z. R x z /\\ R z y)) ==> (exists f. f (&0) = a /\\ f (&1) = b /\\ (forall x y. x IN {&k / &2 pow n | k <= 2 EXP n} /\\ y IN {&k / &2 pow n | k <= 2 EXP n} /\\ x < y ==> R (f x) (f y)))"
#eval thmCheck "misc.ml SUSLIN_SUSLIN" SUSLIN_SUSLIN
  "|- forall u. suslin (suslin u) = suslin u"
#eval thmCheck "misc.ml CARD_SUSLIN_EQ" CARD_SUSLIN_EQ
  "|- forall C. C =_c (:real) ==> suslin C =_c (:real)"

/- ---------------------------------------------------------------------- -/
/- HORNER_SUM_CONV (misc.ml 898), as HOL Light prints its results.        -/
/- ---------------------------------------------------------------------- -/
#eval convCheck "misc.ml HORNER_SUM_CONV 0..2" "sum(0..2) (\\k. &k * x pow k)"
  "|- sum (0..2) (\\k. &k * x pow k) = &0 + x * (&1 + x * &2)"
#eval convCheck "misc.ml HORNER_SUM_CONV 0..3" "sum(0..3) (\\i. (&i + &1) / &2 * y pow i)"
  "|- sum (0..3) (\\i. (&i + &1) / &2 * y pow i) = &1 / &2 + y * (&1 + y * (&3 / &2 + y * &2))"

/- ---------------------------------------------------------------------- -/
/- ASSERT_TAC and EQ_TRANS_TAC (misc.ml 16-20).                           -/
/- ---------------------------------------------------------------------- -/
#eval do
  tacCheck "misc.ml ASSERT_TAC" "!x:real. &0 < x ==> &0 < x + &1"
    (REPEAT STRIP_TAC THEN ASSERT_TAC (← IO.ofExcept (← HolCore.Parser.parse_term "&0 < &1"))
      THENL [REAL_ARITH_TAC2, ASM_REAL_ARITH_TAC])
    "|- forall x. &0 < x ==> &0 < x + &1"
#eval do
  tacCheck "misc.ml EQ_TRANS_TAC" "!a b:num. a + b = b + a"
    (REPEAT GEN_TAC THEN EQ_TRANS_TAC (← IO.ofExcept (← HolCore.Parser.parse_term "b + a:num"))
      THEN ARITH_TAC)
    "|- forall a b. a + b = b + a"
