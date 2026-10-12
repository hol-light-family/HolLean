/- File: HolTest/QuotTest.lean
Runtime test suite: quot.ml - quotient types and theorem lifting
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Tests: quot.ml - quotient types and theorem lifting.                   -/
/- ---------------------------------------------------------------------- -/


-- ========================================================================
-- quot.ml : quotient types + lifting of first-order theorems
--   Uses equality `(=):A->A->bool` as the equivalence relation.  We prove its
--   reflexivity / symmetry / transitivity (by MESON), build the quotient type,
--   lift the `I` combinator two ways — via a relation-valued well-definedness
--   theorem (ETA_CONV branch) and an equality-valued one (SELECT_LEMMA / `@`
--   branch) — and lift a theorem through the quotient.  Gated by TestFlags.runQuot.
-- ========================================================================
#eval (do
  -- equivalence relation = equality on A
  let eqv := ([[ (\(x:A) (y:A). x = y) ]] : term)
  match ← define_quotient_type "qA" ("mk_qA", "dest_qA") eqv with
  | .error e => IO.println s!"QUOT define ERR: {e}"
  | .ok (tybij1, tybij2) =>
    IO.println s!"QUOT tybij1 -> {← HolCore.Printer.string_of_thm tybij1}"
    IO.println s!"QUOT tybij2 -> {← HolCore.Printer.string_of_thm tybij2}"
    -- reflexivity / symmetry / transitivity of the relation `(\x y. x = y)`
    match ← MESON [] ([[ !x:A. (\(x:A) (y:A). x = y) x x ]]),
          ← MESON [] ([[ !x y:A. (\(x:A) (y:A). x = y) x y <=> (\(x:A) (y:A). x = y) y x ]]),
          ← MESON [] ([[ !x y z:A. (\(x:A) (y:A). x = y) x y /\ (\(x:A) (y:A). x = y) y z
                                    ==> (\(x:A) (y:A). x = y) x z ]]) with
    | .ok refl_th, .ok sym_th, .ok trans_th =>
      -- well-definedness (congruence) of the identity combinator I:A->A
      match ← MESON [I_THM] ([[ !x x':A. (\(x:A) (y:A). x = y) x x'
                                    ==> (\(x:A) (y:A). x = y) ((I:A->A) x) (I x') ]]) with
      | .error e => IO.println s!"QUOT wdef ERR: {e}"
      | .ok wth =>
        match ← lift_function tybij2 (refl_th, trans_th) "I_qA" wth with
        | .error e => IO.println s!"QUOT lift_function ERR: {e}"
        | .ok (defn, cons) =>
          IO.println s!"QUOT lift_function def -> {← HolCore.Printer.string_of_thm defn}"
          IO.println s!"QUOT lift_function cons -> {← HolCore.Printer.string_of_thm cons}"
          -- lift a source theorem through the quotient
          match ← MESON [I_THM] ([[ !x:A. (\(x:A) (y:A). x = y) ((I:A->A) x) (I x) ]]) with
          | .error e => IO.println s!"QUOT src-thm ERR: {e}"
          | .ok srcth =>
            match ← lift_theorem (tybij1, tybij2) (refl_th, sym_th, trans_th) [cons] srcth with
            | .ok lifted => IO.println s!"QUOT lift_theorem -> {← HolCore.Printer.string_of_thm lifted}"
            | .error e => IO.println s!"QUOT lift_theorem ERR: {e}"
          -- lift_function, `is_eq con` branch: well-definedness whose conclusion
          -- is an EQUALITY (not the relation) exercises list_mk_icomb "@" +
          -- REWR_CONV SELECT_LEMMA rather than the ETA_CONV branch.
          match ← MESON [I_THM] ([[ !x x':A. (\(x:A) (y:A). x = y) x x'
                                        ==> (I:A->A) x = I x' ]]) with
          | .error e => IO.println s!"QUOT wdef-eq ERR: {e}"
          | .ok wthEq =>
            match ← lift_function tybij2 (refl_th, trans_th) "Ieq_qA" wthEq with
            | .ok (deq, ceq) =>
              IO.println s!"QUOT lift_function(eq) def -> {← HolCore.Printer.string_of_thm deq}"
              IO.println s!"QUOT lift_function(eq) cons -> {← HolCore.Printer.string_of_thm ceq}"
            | .error e => IO.println s!"QUOT lift_function(eq) ERR: {e}"
    | _, _, _ => IO.println "QUOT refl/sym/trans ERR")
