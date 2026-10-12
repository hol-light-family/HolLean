/- File: HolTest/TriviaTest.lean
Runtime test suite: trivia.ml - the combinators and the one-element type
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Tests: trivia.ml - the combinators and the one-element type.           -/
/- ---------------------------------------------------------------------- -/

-- trivia.ml: combinators
#eval o_THM    -- |- !f g x. (f o g) x = f (g x)
#eval o_ASSOC  -- |- !f g h. f o (g o h) = (f o g) o h
#eval I_THM    -- |- !x. I x = x
#eval I_O_ID   -- |- !f. I o f = f /\ f o I = f
-- trivia.ml: the one-element type 1
#eval EXISTS_ONE_REP  -- |- ?b. b
#eval one             -- |- !v. v = one
#eval one_axiom       -- |- !f g. f = g
#eval one_INDUCT      -- |- !P. P one ==> !x. P x
#eval one_RECURSION   -- |- !e. ?fn. fn one = e
#eval one_Axiom       -- |- !e. ?!fn. fn one = e
#eval FORALL_ONE_THM  -- |- (!x. P x) <=> P one
#eval EXISTS_ONE_THM  -- |- (?x. P x) <=> P one

/- ---------------------------------------------------------------------- -/
/- Every remaining theorem this layer establishes, printed as `|- ...`.   -/
/- Forcing any one of them runs the whole layer, so these also serve as   -/
/- a check that no proof in it regressed.                                 -/
/- ---------------------------------------------------------------------- -/

-- Remaining statements from the one-element type definitions (one `#eval` each, so a
-- failure points at the individual theorem).
#eval one_tydef
#eval one_DEF
