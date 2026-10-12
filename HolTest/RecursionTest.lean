/- File: HolTest/RecursionTest.lean
Runtime test suite: recursion.ml - definition by primitive recursion
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Tests: recursion.ml - definition by primitive recursion.               -/
/- ---------------------------------------------------------------------- -/


/- ---------------------------------------------------------------------- -/
/- recursion.ml : definition by primitive recursion.                      -/
/- NOTE: the term must be parsed with `parse_term` at the point of use,   -/
/- not via a hoisted `[[ ]]` quotation.  Before a function is defined its -/
/- name parses as a VARIABLE; afterwards as a CONSTANT.  OCaml re-parses  -/
/- each quotation at its point in the script, so reusing a pre-definition -/
/- term would not exercise the benign-redefinition path.                  -/
/- ---------------------------------------------------------------------- -/

-- Each test module is compiled in its OWN process, so the lazily-bootstrapped
-- session state starts empty here.  Printing `num_RECURSION` is a real test AND
-- forces the nums.ml layer, which declares the type `num`; without it the
-- `parse_term` calls below fail with "mk_type: type num has not been defined".
#eval num_RECURSION

#eval (do
  -- The canonical use: define PRE by primitive recursion over num.
  match ← HolCore.Parser.parse_term "(PRE 0 = 0) /\\ (!n. PRE (SUC n) = n)" with
  | .error e => IO.println s!"PRE parse ERR: {e}"
  | .ok tm => do
    match ← Session.new_recursive_definition Session.num_RECURSION tm with
    | .error e => IO.println s!"new_recursive_definition PRE ERR: {e}"
    | .ok th => do
      IO.println s!"PRE by recursion -> {← HolCore.Printer.string_of_thm th}"
      -- Re-parse so PRE is now a constant, then redefine: must take the
      -- benign-redefinition path and reuse the stored theorem.
      match ← HolCore.Parser.parse_term "(PRE 0 = 0) /\\ (!n. PRE (SUC n) = n)" with
      | .error e => IO.println s!"PRE re-parse ERR: {e}"
      | .ok tm2 =>
        match ← Session.new_recursive_definition Session.num_RECURSION tm2 with
        | .ok th2 => IO.println s!"PRE benign redefinition -> {← HolCore.Printer.string_of_thm th2}"
        | .error e => IO.println s!"PRE redefinition ERR: {e}")

-- A two-argument function, which exercises `canonize` (the recursion argument
-- must come first) and `reshuffle` (arguments reordered so variables come last).
#eval (do
  match ← HolCore.Parser.parse_term
            "(!m. ADDX 0 m = m) /\\ (!n m. ADDX (SUC n) m = SUC (ADDX n m))" with
  | .error e => IO.println s!"ADDX parse ERR: {e}"
  | .ok tm =>
    match ← Session.new_recursive_definition Session.num_RECURSION tm with
    | .ok th => IO.println s!"ADDX (2 args) -> {← HolCore.Printer.string_of_thm th}"
    | .error e => IO.println s!"ADDX ERR: {e}")
-- The recursion argument NOT first: this is the case `reshuffle` exists for.

#eval (do
  match ← HolCore.Parser.parse_term
            "(!m. ADDY m 0 = m) /\\ (!m n. ADDY m (SUC n) = SUC (ADDY m n))" with
  | .error e => IO.println s!"ADDY parse ERR: {e}"
  | .ok tm =>
    match ← Session.new_recursive_definition Session.num_RECURSION tm with
    | .ok th => IO.println s!"ADDY (arg not first) -> {← HolCore.Printer.string_of_thm th}"
    | .error e => IO.println s!"ADDY ERR: {e}")


-- The three existence layers directly, and the derived function computing.
#eval (do
  match ← HolCore.Parser.parse_term "(fn 0 = 0) /\\ (!n. fn (SUC n) = SUC (fn n))" with
  | .error e => IO.println s!"exists parse ERR: {e}"
  | .ok tm => do
    (do match ← Session.prove_recursive_functions_exist Session.num_RECURSION tm with
        | .ok th => IO.println s!"prove_recursive_functions_exist -> {← HolCore.Printer.string_of_thm th}"
        | .error e => IO.println s!"prove_recursive_functions_exist ERR: {e}")
    (do match ← Session.prove_canon_recursive_functions_exist Session.num_RECURSION tm with
        | .ok th => IO.println s!"prove_canon_recursive_functions_exist -> {← HolCore.Printer.string_of_thm th}"
        | .error e => IO.println s!"prove_canon ERR: {e}"))
-- The defined function must actually compute: define PRE3, then use its own
-- defining theorem to reduce `PRE3 (SUC (SUC 0))`.

#eval (do
  match ← HolCore.Parser.parse_term "(PRE3 0 = 0) /\\ (!n. PRE3 (SUC n) = n)" with
  | .error e => IO.println s!"PRE3 parse ERR: {e}"
  | .ok tm =>
    match ← Session.new_recursive_definition Session.num_RECURSION tm with
    | .error e => IO.println s!"PRE3 ERR: {e}"
    | .ok dth => do
      match ← HolCore.Parser.parse_term "PRE3 (SUC (SUC 0)) = SUC 0" with
      | .error e => IO.println s!"PRE3 goal parse ERR: {e}"
      | .ok goal =>
        match ← Session.prove goal (Session.REWRITE_TAC [dth]) with
        | .ok th => IO.println s!"PRE3 computes -> {← HolCore.Printer.string_of_thm th}"
        | .error e => IO.println s!"PRE3 computes (msg): {e}")


-- Paths the tests above do not reach.
#eval (do
  match ← HolCore.Parser.parse_term "(fnr 0 = 0) /\\ (!n. fnr (SUC n) = SUC (fnr n))" with
  | .error e => IO.println s!"raw parse ERR: {e}"
  | .ok tm =>
    match ← Session.prove_raw_recursive_functions_exist Session.num_RECURSION tm with
    | .ok th => IO.println s!"prove_raw direct -> {← HolCore.Printer.string_of_thm th}"
    | .error e => IO.println s!"prove_raw direct ERR: {e}")
-- A clause left UNQUANTIFIED.  This is what the `fvs` machinery is for:
-- `fvs = map (fun t -> subtract (frees t) ufns) rawcls` is non-empty here, so
-- the clause is generalized to `!n. ...` before proving existence and the
-- result is SPEC'd back down by `map2 SPECL fvs (CONJUNCTS dth)`.  Every other
-- test has all clauses pre-quantified, leaving `fvs` empty and that path dead.

#eval (do
  match ← HolCore.Parser.parse_term "(FQ 0 = 0) /\\ (FQ (SUC n) = SUC (FQ n))" with
  | .error e => IO.println s!"unquantified parse ERR: {e}"
  | .ok tm =>
    match ← Session.new_recursive_definition Session.num_RECURSION tm with
    | .ok th => IO.println s!"unquantified clause -> {← HolCore.Printer.string_of_thm th}"
    | .error e => IO.println s!"unquantified clause ERR: {e}")
-- Defining TWO functions at once must FAIL against num_RECURSION, which has a
-- single existential; a two-function definition needs a recursion theorem with
-- two.  (OCaml fails here too: `list_mk_exists(urfns,tm)` cannot match
-- `list_mk_exists(exvs,...)` when the binder counts differ.)

#eval (do
  match ← HolCore.Parser.parse_term
            "(P1 0 = 0) /\\ (!n. P1 (SUC n) = n) /\\ (Q1 0 = 0) /\\ (!n. Q1 (SUC n) = SUC n)" with
  | .error e => IO.println s!"two-fn parse ERR: {e}"
  | .ok tm =>
    match ← Session.new_recursive_definition Session.num_RECURSION tm with
    | .error e => IO.println s!"two functions correctly rejected: {e}"
    | .ok _ => IO.println "TWO FUNCTIONS ACCEPTED - unexpected")


