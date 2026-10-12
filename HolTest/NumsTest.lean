/- File: HolTest/NumsTest.lean
Runtime test suite: nums.ml - the axiom of infinity and the natural numbers
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Tests: nums.ml - the axiom of infinity and the natural numbers.        -/
/- ---------------------------------------------------------------------- -/


/- ---------------------------------------------------------------------- -/
/- nums.ml : the axiom of infinity and the natural numbers.               -/
/- Forcing any Nums theorem forces `Session.Nm`, which runs the whole     -/
/- nums.ml script: the type `ind`, INFINITY_AX, the inductive carving of  -/
/- `num` out of `ind`, and the induction/recursion/cases theorems.        -/
/- Gated by TestFlags.runNums.                                            -/
/- ---------------------------------------------------------------------- -/

-- Each theorem this layer establishes, printed as `|- ...`.
#eval ONE_ONE
#eval ONTO
#eval INFINITY_AX
#eval IND_SUC_0_EXISTS
#eval IND_SUC_INJ
#eval IND_SUC_0
#eval NUM_REP_RULES
#eval num_tydef.1
#eval num_tydef.2
#eval ZERO_DEF
#eval SUC_DEF
#eval NOT_SUC
#eval SUC_INJ
#eval num_INDUCTION
#eval num_Axiom
#eval NUMERAL
#eval num_RECURSION
#eval num_CASES
#eval BIT0_DEF
#eval BIT1_DEF

-- Numeral syntax operations, including the 2^24 chunk boundary of mk_numeral.
#eval (do
  for n in [0, 1, 2, 3, 10, 255, 1000, 16777215, 16777216, 16777217,
            123456789012345] do
    match Session.mk_numeral (Rat.ofInt n) with
    | .error e => IO.println s!"mk_numeral {n} ERR: {e}"
    | .ok t =>
      IO.println s!"mk_numeral {n} -> {← HolCore.Printer.string_of_term t}  \
round-trip={Session.dest_small_numeral t}  is_numeral={Session.is_numeral t}")

#eval (do
  match Session.mk_numeral (-5) with
  | .error e => IO.println s!"mk_numeral negative correctly rejected: {e}"
  | .ok _ => IO.println "NEGATIVE ACCEPTED - BUG")

#eval (do
  match Session.mk_small_numeral 42 with
  | .error e => IO.println s!"mk_small_numeral ERR: {e}"
  | .ok t => IO.println s!"mk_small_numeral 42 -> {← HolCore.Printer.string_of_term t}")
-- is_numeral must reject a non-numeral.

#eval (do
  IO.println s!"is_numeral (SUC 0) = {Session.is_numeral ([[ SUC 0 ]])}")


-- INDUCT_TAC, num_CASES and the recursion theorem in actual proofs.
#eval (do
  match ← Session.prove ([[ !n. ~(SUC n = 0) ]])
            (THEN Session.INDUCT_TAC (Session.REWRITE_TAC [Session.NOT_SUC])) with
  | .ok th => IO.println s!"INDUCT_TAC proof -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"INDUCT_TAC proof (msg): {e}")
-- num_CASES used to case-split.

#eval (do
  match ← Session.prove ([[ !m. m = 0 \/ (?n. m = SUC n) ]])
            (Session.MESON_TAC [Session.num_CASES]) with
  | .ok th => IO.println s!"num_CASES use -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"num_CASES use (msg): {e}")
-- num is registered in the inductive type store with arity 2.

#eval (do
  for (n, (a, _, _)) in ← Session.get_inductive_type_store do
    if n == "num" then IO.println s!"inductive_type_store has num, arity {a}")


-- new_specification: a derived principle of definition based on existence.
#eval (do
  match ← Session.prove ([[ ?x. x = 0 ]]) (Session.MESON_TAC []) with
  | .error e => IO.println s!"new_specification setup (msg): {e}"
  | .ok exth => do
    (do match ← Session.new_specification ["MYZERO"] exth with
        | .ok sth => IO.println s!"new_specification -> {← HolCore.Printer.string_of_thm sth}"
        | .error e => IO.println s!"new_specification ERR: {e}")
    -- A repeat is a benign respecification and reuses the stored theorem.
    (do match ← Session.new_specification ["MYZERO"] exth with
        | .ok sth => IO.println s!"benign respecification -> {← HolCore.Printer.string_of_thm sth}"
        | .error e => IO.println s!"respecification ERR: {e}")
    -- Error paths, with OCaml's exact messages.
    (do match ← Session.new_specification [] exth with
        | .error e => IO.println s!"no names rejected: {e}"
        | .ok _ => IO.println "EMPTY NAMES ACCEPTED - BUG")
    (do match ← Session.new_specification ["A", "B"] exth with
        | .error e => IO.println s!"too many names rejected: {e}"
        | .ok _ => IO.println "TOO MANY NAMES ACCEPTED - BUG"))

-- The remaining new_specification paths.  The two error tests above BOTH hit the
-- `Unsuitable number of constant names` guard (2 names vs 1 existential), so the
-- other three failure messages, and `check_distinct` itself, need a theorem with
-- TWO existentials to be reachable at all.
#eval (do
  match ← Session.prove ([[ ?x y. x = 0 /\ y = 0 ]]) (Session.MESON_TAC []) with
  | .error e => IO.println s!"2-existential setup (msg): {e}"
  | .ok th2 => do
    -- `specifies` recursing over more than one name.
    (do match ← Session.new_specification ["MYA", "MYB"] th2 with
        | .ok s => IO.println s!"multi-name specification -> {← HolCore.Printer.string_of_thm s}"
        | .error e => IO.println s!"multi-name specification ERR: {e}")
    -- Now the length guard passes, so `check_distinct` actually runs.
    (do match ← Session.new_specification ["A", "A"] th2 with
        | .error e => IO.println s!"duplicate names rejected: {e}"
        | .ok _ => IO.println "DUPLICATE NAMES ACCEPTED - BUG"))
-- A theorem carrying an assumption.

#eval (do
  match ASSUME ([[ ?x. x = 0 ]]) with
  | .error e => IO.println s!"ASSUME ERR: {e}"
  | .ok ath =>
    match ← Session.new_specification ["Z"] ath with
    | .error e => IO.println s!"assumptions rejected: {e}"
    | .ok _ => IO.println "ASSUMPTIONS ACCEPTED - BUG")
-- No assumptions, but a free variable in the conclusion.

#eval (do
  match ← Session.new_specification ["Z"] (REFL ([[ y:num ]])) with
  | .error e => IO.println s!"free variables rejected: {e}"
  | .ok _ => IO.println "FREE VARS ACCEPTED - BUG")
-- dest_small_numeral must fail on a non-numeral.

#eval (do
  IO.println s!"dest_small_numeral (SUC 0) = {Session.dest_small_numeral ([[ SUC 0 ]])}")


-- Induction and recursion actually driving proofs (not just printed).
#eval (do
  match ← Session.prove ([[ !n. ~(n = SUC n) ]])
            (THEN Session.INDUCT_TAC
              (Session.ASM_MESON_TAC [Session.NOT_SUC, Session.SUC_INJ])) with
  | .ok th => IO.println s!"induction using the hypothesis -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"induction using the hypothesis (msg): {e}")
-- num_RECURSION instantiated to yield an actual recursive function.

#eval (do
  match Session.ISPECL [([[ 0 ]]), ([[ \m n:num. SUC m ]])] Session.num_RECURSION with
  | .ok th => IO.println s!"num_RECURSION instance -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"num_RECURSION instance ERR: {e}")
-- num_CASES driving a case split.

#eval (do
  match ← Session.prove ([[ !m. ~(m = 0) ==> (?n. m = SUC n) ]])
            (Session.MESON_TAC [Session.num_CASES]) with
  | .ok th => IO.println s!"num_CASES case split -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"num_CASES case split (msg): {e}")

/- ---------------------------------------------------------------------- -/
/- Every remaining theorem this layer establishes, printed as `|- ...`.   -/
/- Forcing any one of them runs the whole layer, so these also serve as   -/
/- a check that no proof in it regressed.                                 -/
/- ---------------------------------------------------------------------- -/

-- Remaining statements from the remaining nums.ml theorems (one `#eval` each, so a
-- failure points at the individual theorem).
#eval IND_SUC_SPEC
#eval NUM_REP_INDUCT
#eval NUM_REP_CASES
