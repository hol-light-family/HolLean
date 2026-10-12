/- File: HolTest/ItabTest.lean
Runtime test suite: itab.ml - the intuitionistic tableau prover ITAUT.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

FAITHFULNESS BASIS.  ITAUT is HOL Light's INTUITIONISTIC prover, "complete for
the propositional fragment" (itab.ml header).  The positive goals below are
taken VERBATIM from the theorems.ml bootstrap, where HOL Light itself proves
each of them with `ITAUT_TAC` - so they are guaranteed intuitionistically
provable and are the authoritative oracle.  See HolCore/Theorems.lean (the
Lean port of theorems.ml) at the lines cited per test.  A handful of standard
Pelletier / propositional benchmarks are added, with the intuitionistic-vs-
classical distinction made explicit.

WHY NO ITAUT NON-THEOREM ASSERTIONS.  itab.ml's driver `ITAUT_ITERDEEP_TAC`
increases the depth limit WITHOUT BOUND: `(ITAUT_TAC [] n THEN NO_TAC) ORELSE
ITAUT_ITERDEEP_TAC (n + 1)` (itab.ml, Lean HolCore/Itab.lean:150).  On a
non-theorem it never succeeds and recurses forever, so calling `ITAUT` on a
classically-valid-but-not-intuitionistic goal (LEM, Peirce, ...) would HANG the
compile - there is no exposed bounded entry point (the inner `ITAUT_TAC mvs n`
is `private`).  An `evalNonThm`-style assertion is therefore INFEASIBLE here and
would be unsafe.  Instead the distinction is pinned POSITIVELY and terminatingly:
  * the classical tautology is proved with the CLASSICAL prover `TAUT`
    (Session.TAUT, terminating) - showing it IS valid classically; and
  * its Glivenko double-negation `~~(...)`, which IS intuitionistically valid,
    is proved with `ITAUT` - showing ITAUT handles the intuitionistic core but
    (by Glivenko) needs the double negation, i.e. it is genuinely constructive.
-/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Self-checking helpers.                                                 -/
/- ---------------------------------------------------------------------- -/

/-- Squash whitespace so a printed theorem compares as a single line. -/
private def itabSquash (s : String) : String :=
  (s.replace "\n" "").replace " " ""

/-- Prove `goalStr` with a prover `p` and assert the resulting theorem is
    exactly `|- <goalStr>` (no extra hypotheses, no leftover subgoals).  The
    expected string is the goal itself re-printed, so we are not guessing the
    printer's exact spacing - we assert "the prover proved precisely the stated
    goal and nothing weaker".  Prints a line containing `-> OK` on success. -/
private unsafe def proveExactly (lbl goalStr : String)
    (p : term → IO (Except String thm)) : IO Unit := do
  match ← HolCore.Parser.parse_term goalStr with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok g =>
    match ← p g with
    | .error e => IO.println s!"{lbl} -> FAILED (prover error): {e}"
    | .ok th =>
      let got := itabSquash (← HolCore.Printer.string_of_thm th)
      let want := itabSquash ("|- " ++ (← HolCore.Printer.string_of_term g))
      if got == want then IO.println s!"{lbl} -> OK"
      else IO.println s!"{lbl} -> FAILED got={got} want={want}"

/-- `ITAUT` specialisation of `proveExactly`. -/
private unsafe def itaut (lbl goalStr : String) : IO Unit :=
  proveExactly lbl goalStr Session.ITAUT

/-- Classical `TAUT` specialisation (terminating; used only for the
    intuitionistic-vs-classical contrast). -/
private unsafe def taut (lbl goalStr : String) : IO Unit :=
  proveExactly lbl goalStr Session.TAUT

/- ---------------------------------------------------------------------- -/
/- Propositional core - all intuitionistically valid (Theorems.lean).     -/
/- Each `goalStr` is the exact statement theorems.ml proves with ITAUT_TAC.-/
/- ---------------------------------------------------------------------- -/

-- Trivial identity / weakening - the base reversible-rule paths (DISCH,CONJ).
#eval itaut "p ==> p" "p ==> p"
#eval itaut "p /\\ q ==> p" "p /\\ q ==> p"
#eval itaut "p /\\ q ==> q /\\ p" "p /\\ q ==> q /\\ p"
#eval itaut "p ==> q ==> p" "p ==> q ==> p"

-- CONJ_SYM (Theorems.lean:156): !t1 t2. t1 /\ t2 <=> t2 /\ t1  (GEN + EQ_TAC).
#eval itaut "CONJ_SYM" "!t1 t2. t1 /\\ t2 <=> t2 /\\ t1"
-- DISJ_SYM (Theorems.lean:159): disjunction commutes (DISJ_CASES left path).
#eval itaut "DISJ_SYM" "!t1 t2. t1 \\/ t2 <=> t2 \\/ t1"
-- IMP_CONJ / currying (Theorems.lean:160): p /\ q ==> r <=> p ==> q ==> r.
#eval itaut "IMP_CONJ (curry)" "p /\\ q ==> r <=> p ==> q ==> r"
-- LEFT_OR_DISTRIB (Theorems.lean:163): distributivity, intuitionistically fine.
#eval itaut "LEFT_OR_DISTRIB" "!p q r. p /\\ (q \\/ r) <=> p /\\ q \\/ p /\\ r"
-- congruence lemma theorems.ml feeds to extend_basic_congs (Theorems.lean:181):
-- (p <=> p') ==> (p' ==> (q <=> q')) ==> (p ==> q <=> p' ==> q').  Deeply nested
-- implications; a good stress of the DISCH/EQ reversible chain.
#eval itaut "cong lemma"
  "(p <=> p') ==> (p' ==> (q <=> q')) ==> (p ==> q <=> p' ==> q')"

/- ---------------------------------------------------------------------- -/
/- First-order goals that force the DEEPEST ORELSE branches of ITAUT_TAC   -/
/- (itab.ml).  These are the branches an off-by-one in the depth argument  -/
/- would hide.  Every goal here is one theorems.ml proves with ITAUT_TAC,  -/
/- so it is a guaranteed (terminating) success.                            -/
/- ---------------------------------------------------------------------- -/

-- item 6 (allTac): a UNIVERSAL assumption must be META_SPEC'd with a fresh
-- metavariable, recursing at depth (n - 2).  FORALL_SIMP exercises exactly the
-- universal-assumption path.  (Theorems.lean:166)
#eval itaut "FORALL_SIMP (allTac)" "!t. (!x:A. t) = t"

-- item 9 (step7): an EXISTENTIAL GOAL must be closed via X_META_EXISTS_TAC and
-- a metavariable, recursing at (n - 2).  EXISTS_SIMP hits the existential-goal
-- path.  (Theorems.lean:167)
#eval itaut "EXISTS_SIMP (step7)" "!t. (?x:A. t) = t"

-- SWAP_EXISTS_THM (Theorems.lean:196): (?x y. P x y) <=> (?y x. P x y).  The
-- task called this out explicitly: it needs step7 (existential goal) AND the
-- universal-assumption/meta machinery to line up the swapped witnesses; an
-- off-by-one in the (n - 2) depth would fail it.
#eval itaut "SWAP_EXISTS_THM" "!P:A->B->bool. (?x y. P x y) <=> (?y x. P x y)"

-- LEFT_IMP_EXISTS_THM (Theorems.lean:216): ((?x. P x) ==> Q) <=> (!x. P x ==> Q).
-- Also called out by the task.  Combines the existential-antecedent handling
-- with the universal RHS - the meta/existential ORELSE branches together.
#eval itaut "LEFT_IMP_EXISTS_THM" "!P Q. ((?x:A. P x) ==> Q) <=> (!x. P x ==> Q)"

-- FORALL_AND_THM (Theorems.lean:200): (!x. P x /\ Q x) <=> (!x. P x) /\ (!x. Q x).
-- Universal-over-conjunction: reversible CONJ_TAC + universal-assumption path.
#eval itaut "FORALL_AND_THM"
  "!P Q. (!x:A. P x /\\ Q x) <=> (!x. P x) /\\ (!x. Q x)"

-- EXISTS_OR_THM (Theorems.lean:205): (?x. P x \/ Q x) <=> (?x. P x) \/ (?x. Q x).
-- Existential-over-disjunction: exercises step7 in BOTH directions plus the
-- DISJ1/DISJ2 branches (items 7/8).
#eval itaut "EXISTS_OR_THM"
  "!P Q. (?x:A. P x \\/ Q x) <=> (?x. P x) \\/ (?x. Q x)"

-- RIGHT_IMP_FORALL_THM (Theorems.lean:214): (P ==> !x. Q x) <=> (!x. P ==> Q x).
-- Universal under an implication - reversible GEN/DISCH interleaving.
#eval itaut "RIGHT_IMP_FORALL_THM"
  "!P Q. (P ==> !x:A. Q x) <=> (!x. P ==> Q x)"

/- ---------------------------------------------------------------------- -/
/- The intuitionistic-vs-classical distinction, pinned WITHOUT hanging.    -/
/- For each classical tautology: (a) TAUT proves it (classical, valid);    -/
/- (b) ITAUT proves its Glivenko double-negation `~~(...)` (which IS        -/
/- intuitionistically valid).  We do NOT run ITAUT on the bare classical    -/
/- tautology - that would loop forever (see file header).                  -/
/- ---------------------------------------------------------------------- -/

-- Law of excluded middle.  Classically valid; intuitionistically NOT, but its
-- double negation is (Glivenko) - the canonical small example.
#eval taut  "LEM classical (TAUT)"      "p \\/ ~p"
#eval itaut "~~LEM intuitionistic (ITAUT)" "~ ~(p \\/ ~p)"

-- Double-negation elimination and Peirce's law are classical-only.  We show
-- they ARE classically valid via TAUT (terminating).  We deliberately do NOT
-- run ITAUT on them, nor on their Glivenko double-negations: `~~LEM` above
-- already witnesses the intuitionistic core, and the double-negations of these
-- deeper formulas would drive ITAUT's UNBOUNDED iterative deepening into a slow
-- (though terminating) search with no extra pinning value (see file header).
#eval taut  "DNE classical (TAUT)"    "~ ~p ==> p"
#eval taut  "Peirce classical (TAUT)" "((p ==> q) ==> p) ==> p"

-- One direction of De Morgan that is constructively FINE (the easy direction),
-- shown positively with ITAUT: ~p \/ ~q ==> ~(p /\ q).
#eval itaut "De Morgan (easy dir, intuit.)" "~p \\/ ~q ==> ~(p /\\ q)"

-- And the contrapositive, which is intuitionistically valid:
-- (p ==> q) ==> (~q ==> ~p).
#eval itaut "contrapositive (intuit.)" "(p ==> q) ==> (~q ==> ~p)"
