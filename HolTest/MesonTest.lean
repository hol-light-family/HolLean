/- File: HolTest/MesonTest.lean
Runtime test suite: meson.ml - first-order goals via MESON
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Tests: meson.ml - first-order goals via MESON.                         -/
/- ---------------------------------------------------------------------- -/


-- == meson.ml — real first-order goals via MESON ==
#eval evalMeson (MESON [] ([[ (p:bool) \/ ~p ]]))                                       -- excluded-middle
#eval evalMeson (MESON [] ([[ (?x:A. !y:A. (R:A->A->bool) x y) ==> (!y:A. ?x:A. R x y) ]])) -- ex-forall=>forall-ex
#eval evalMeson (MESON [] ([[ (!x:A. (P:A->bool) x /\ (Q:A->bool) x) ==> P a ]]))        -- conj-inst
-- broader MESON battery (distinct code paths)
-- deeper propositional (chained implications / modus ponens chain)
#eval evalMeson (MESON [] ([[ ((p:bool) ==> q) ==> (q ==> r) ==> (r ==> s) ==> p ==> s ]])) -- imp-chain
-- disjunction / case analysis
#eval evalMeson (MESON [] ([[ ((p:bool) \/ q) /\ (p ==> r) /\ (q ==> r) ==> r ]]))       -- case-split
-- equality transitivity (exercises transitivity equality axiom)
#eval evalMeson (MESON [] ([[ (a:A) = b /\ (b:A) = c ==> (a:A) = c ]]))                  -- eq-trans
-- function congruence (needs congruence axiom for f)
#eval evalMeson (MESON [] ([[ (x:A) = y ==> (f:A->B) x = f y ]]))                        -- fun-cong
-- predicate congruence via equality
#eval evalMeson (MESON [] ([[ (x:A) = y /\ (P:A->bool) x ==> P y ]]))                    -- pred-cong
-- exists in conclusion (witness)
#eval evalMeson (MESON [] ([[ (P:A->bool) a ==> (?x:A. P x) ]]))                         -- exists-intro
-- nested function terms / 2-place relation transitivity as a lemma (POLY_ASSUME path)
#eval evalMeson (MESON [] ([[ (!x y z:A. (R:A->A->bool) x y /\ R y z ==> R x z) /\
                             (!x y:A. R x y ==> R y x) /\ (R:A->A->bool) a b ==> R a a ]])) -- rel-lemma
-- combined quantifiers + implication (Andrews-style)
#eval evalMeson (MESON [] ([[ (?x:A. !y:A. (P:A->bool) x <=> P y) ==>
                             ((?x:A. P x) <=> (!y:A. P y)) ]]))               -- andrews
-- deeper-search goals (stress iterative deepening / caching / backtracking)
-- Pelletier 18 (note: avoid `F`/`T` — reserved as falsity/truth constants)
#eval evalMeson (MESON [] ([[ ?y:A. !x:A. (G:A->bool) y ==> (G:A->bool) x ]]))           -- P18
-- Pelletier 19
#eval evalMeson (MESON [] ([[ ?x:A. !y z:A. ((P:A->bool) y ==> (Q:A->bool) z) ==> (P x ==> Q x) ]])) -- P19
-- transitivity chain needing several resolution steps
#eval evalMeson (MESON [] ([[ (!x y:A. (R:A->A->bool) x y ==> R y x) /\
                             (!x y z:A. R x y /\ R y z ==> R x z) /\
                             (!x:A. ?y:A. R x y) ==> (!x:A. R x x) ]]))        -- refl-from
-- equality + function: f(f(f a)) = a, f(f a) = a  ==>  f a = a  (congruence + eq chain)
#eval evalMeson (MESON [] ([[ (f:A->A) ((f:A->A) ((f:A->A) a)) = a /\ (f:A->A) ((f:A->A) a) = a
                             ==> (f:A->A) a = a ]]))                          -- eq-fun-chain
-- Pelletier 24-ish (disjunction + negation, several clauses)
#eval evalMeson (MESON [] ([[ ~(?x:A. (S:A->bool) x /\ (Q:A->bool) x) /\
                             (!x:A. (P:A->bool) x ==> Q x \/ (R:A->bool) x) /\
                             ~(?x:A. P x) ==> (!x:A. P x ==> R x) ]]))         -- P24ish
-- goal needing backtracking: two ways to derive, one dead-ends
#eval evalMeson (MESON [] ([[ (!x:A. (P:A->bool) x ==> (Q:A->bool) x) /\
                             (!x:A. Q x ==> (R:A->bool) x) /\ P a ==> R a ]])) -- PQR
-- entry-point / soundness paths
-- MESON with a supplied lemma (exercises POLY_ASSUME_TAC / polymorph)
#eval evalWithLemmas MESON [([[ !x:A. (x:A) = x ]])] ([[ (a:A) = a ]]) -- with-lemma
-- MESON_TAC / ASM_MESON_TAC as goal tactics
#eval evalMeson (prove ([[ (p:bool) \/ ~p ]]) (MESON_TAC []))                            -- MESON_TAC
#eval evalMeson (prove ([[ ((!x:A. (P:A->bool) x ==> (Q:A->bool) x)) ==> P a ==> Q a ]])
           (THEN DISCH_TAC (THEN DISCH_TAC (ASM_MESON_TAC []))))              -- ASM_MESON_TAC
-- Non-theorems must fail cleanly (soundness + termination)
#eval evalNonThm (MESON [] ([[ (p:bool) ]]))                          -- non-thm (bare p)
#eval evalNonThm (MESON [] ([[ (?x:A. (P:A->bool) x) ==> (!x:A. (P:A->bool) x) ]])) -- non-thm (ex=>all)

-- == firstorder.ml — FOL shadow-term translation (Mapping) ==
-- Round-trip a variable-free HOL term through fol_of_term / hol_of_term.
#eval (do
  fo_reset_vars
  match ← fo_reset_consts with
  | .error e => IO.println s!"fo_reset_consts ERR: {e}"
  | .ok _ =>
    let tm := ([[ (P:A->A->bool) (c:A) (d:A) ]])
    match ← fo_fol_of_term [] [] tm with
    | .error e => IO.println s!"fol_of_term ERR: {e}"
    | .ok fol =>
      match ← fo_hol_of_term bool_ty fol with
      | .error e => IO.println s!"hol_of_term ERR: {e}"
      | .ok tm' => IO.println s!"FO round-trip: {← HolCore.Printer.string_of_term tm'} (orig {← HolCore.Printer.string_of_term tm})")
-- fol_of_form on a quantified formula (shape check via Repr).
#eval (do
  fo_reset_vars
  match ← fo_reset_consts with
  | .error _ => IO.println "reset ERR"
  | .ok _ =>
    match ← fo_fol_of_form [] [] ([[ !x:A. (P:A->bool) x \/ (Q:A->bool) x ]]) with
    | .error e => IO.println s!"fol_of_form ERR: {e}"
    | .ok f => IO.println s!"FO fol_of_form ok: {repr f}")
-- fol_of_hol_clauses on a couple of clauses (partition/sort into rule lists).
#eval (do
  fo_reset_vars
  match ← fo_reset_consts with
  | .error _ => IO.println "reset ERR"
  | .ok _ =>
    match (ASSUME ([[ (P:A->bool) a ]])), (ASSUME ([[ ~((P:A->bool) a) \/ (Q:A->bool) a ]])) with
    | .ok c1, .ok c2 =>
        match ← fo_fol_of_hol_clauses [c1, c2] with
        | .error e => IO.println s!"fol_of_hol_clauses ERR: {e}"
        | .ok rules => IO.println s!"FO fol_of_hol_clauses ok: {rules.length} predicate groups"
    | _, _ => IO.println "ASSUME failed")
