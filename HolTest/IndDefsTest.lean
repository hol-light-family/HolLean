/- File: HolTest/IndDefsTest.lean
Runtime test suite: ind_defs.ml - new_inductive_definition
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Tests: ind_defs.ml - new_inductive_definition.                         -/
/- ---------------------------------------------------------------------- -/


-- ind_defs.ml: new_inductive_definition (transitive closure)
-- Define TC (transitive closure of a schematic relation R) inductively:
--   (!x y. R x y ==> TC R x y) /\
--   (!x y z. TC R x y /\ TC R y z ==> TC R x z)
-- Returns the (rule, induction, cases) triple.
#eval (do
  match ← new_inductive_definition
      ([[ (!x y. (R:A->A->bool) x y ==> TC R x y) /\
          (!x y z. TC R x y /\ TC R y z ==> TC R x z) ]]) with
  | .error e => IO.println s!"ERROR: {e}"
  | .ok (rule, induct, cases) => do
      IO.println s!"RULE:    {← HolCore.Printer.string_of_thm rule}"
      IO.println s!"INDUCT:  {← HolCore.Printer.string_of_thm induct}"
      IO.println s!"CASES:   {← HolCore.Printer.string_of_thm cases}" : IO Unit)
