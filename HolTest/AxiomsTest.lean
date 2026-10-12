/- File: HolTest/AxiomsTest.lean
The NEGATIVE control for `check_axioms` (hol_lib.ml 105-114): a leaked axiom must
be REJECTED.  The positive assertions live in `DefineTest`, which already forces
the full bootstrap; this module deliberately does NOT, because `mk_thm`
permanently dirties `the_axioms` for the process and because the rejection path
needs no upper layers.
Lean4 translation by Chris Walton 2026 -/

import Session
import HolTest.CommonTest

open HolCore.Kernel

/-
  `mk_thm` is `new_axiom` underneath (drule.ml 24-26), so it is exactly how an
  axiom leaks into `the_axioms` - which is what `check_axioms` exists to catch.
  Assert that it IS caught, and with OCaml's message shape.
-/

#eval (do
  -- Baseline: clean before the leak.
  match ← Session.check_axioms with
  | .error e => IO.println s!"check_axioms baseline -> MISMATCH already dirty: {e}"
  | .ok _ =>
    match ← HolCore.Parser.parse_term "T \\/ ~T" with
    | .error e => IO.println s!"check_axioms negative control -> parse ERR {e}"
    | .ok tm =>
      match ← Session.mk_thm [] tm with
      | .error e => IO.println s!"check_axioms negative control -> mk_thm ERR {e}"
      | .ok _ =>
        match ← Session.check_axioms with
        | .ok _ => IO.println "check_axioms -> MISMATCH accepted a leaked axiom"
        | .error e =>
          if (e.splitOn "check_axioms: ").length >= 2 then
            IO.println "check_axioms REJECTS a leaked mk_thm axiom -> OK (correctly rejected)"
          else IO.println s!"check_axioms -> MISMATCH wrong message: {e}")
