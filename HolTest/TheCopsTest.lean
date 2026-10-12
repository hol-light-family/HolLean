/- File: HolTest/TheCopsTest.lean
Runtime test suite: thecops.ml - the leanCoP and nanoCoP connection provers
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Tests: thecops.ml - the leanCoP and nanoCoP connection provers.        -/
/- ---------------------------------------------------------------------- -/


-- ========================================================================
-- thecops.ml : leanCoP + nanoCoP connection provers (proof-reconstructing)
-- NOTE: connection provers do NOT terminate on non-theorems (iterative
-- deepening never bottoms out), so — as in the OCaml — every test goal is a
-- genuine theorem.  Reconstruction yields `|- <goal>`.
--
-- These sections are gated by `TestFlags.runLeancop` / `TestFlags.runNanocop`
-- (see the top of this file) since the searches are slow.
-- ========================================================================

-- leanCoP
#eval evalLeancop (LEANCOP [] ([[ (p:bool) \/ ~p ]]))                                    -- excluded-middle
#eval evalLeancop (LEANCOP [] ([[ ((p:bool) ==> q) ==> (q ==> r) ==> p ==> r ]]))        -- imp-chain
#eval evalLeancop (LEANCOP [] ([[ ((p:bool) \/ q) /\ (p ==> r) /\ (q ==> r) ==> r ]]))   -- case-split
#eval evalLeancop (LEANCOP [] ([[ (!x:A. (P:A->bool) x ==> (Q:A->bool) x) /\
                     (!x:A. Q x ==> (R:A->bool) x) /\ P a ==> R a ]]))       -- barbara
#eval evalLeancop (LEANCOP [] ([[ (?x:A. !y:A. (R:A->A->bool) x y) ==> (!y:A. ?x:A. R x y) ]])) -- ex-forall
#eval evalLeancop (LEANCOP [] ([[ (a:A) = b /\ (b:A) = c ==> (a:A) = c ]]))              -- eq-trans
#eval evalLeancop (LEANCOP [] ([[ (p:bool) /\ (p ==> q) ==> q ]]))                       -- modus ponens
#eval evalLeancop (LEANCOP [] ([[ ((p:bool) ==> q) /\ ~q ==> ~p ]]))                     -- modus tollens
#eval evalLeancop (LEANCOP [] ([[ (x:A) = y ==> (f:A->B) x = f y ]]))                    -- fun-cong
#eval evalLeancop (LEANCOP [] ([[ (x:A) = y /\ (P:A->bool) x ==> P y ]]))                -- pred-cong
#eval evalLeancop (LEANCOP [] ([[ (a:A) = b ==> (b:A) = a ]]))                           -- eq-sym
#eval evalLeancop (LEANCOP [] ([[ (P:A->bool) a ==> (?x:A. P x) ]]))                     -- exists-intro
#eval evalLeancop (LEANCOP [] ([[ (!x y z:A. (R:A->A->bool) x y /\ R y z ==> R x z) /\
                     (R:A->A->bool) a b /\ R b c ==> R a c ]]))              -- trans3
#eval evalLeancop (LEANCOP [] ([[ ~((p:bool) /\ q) <=> ~p \/ ~q ]]))                     -- de-morgan
-- with a supplied lemma (POLY_ASSUME path)
#eval evalWithLemmas LEANCOP [([[ !x:A. (x:A) = x ]])] ([[ (a:A) = a ]]) -- with-lemma
#eval evalLeancop (prove ([[ (p:bool) \/ ~p ]]) (LEANCOP_TAC []))                       -- LEANCOP_TAC

-- nanoCoP
-- NOTE on function congruence: a goal like `x = y ==> f x = f y` where `f` is a
-- free *variable* is genuinely higher-order for a first-order prover — the OCaml
-- `create_eq_axs` builds `!g1 g2. ~(g1=g2) \/ f g1 = f g2` and `GEN_ALL` then
-- generalises the free `f`, yielding a higher-order `!f. ...` that `fol_of_thm`
-- rejects with "fol_of_term: higher order" (verified faithful to HOL Light).
-- With a constant function symbol the axiom keeps `f` fixed and works; here we
-- exercise nanoCoP's non-clausal matrix with a nested-structure goal instead.
#eval evalNanocop (NANOCOP [] ([[ (p:bool) \/ ~p ]]))                                    -- excluded-middle
#eval evalNanocop (NANOCOP [] ([[ ((p:bool) \/ q) /\ (p ==> r) /\ (q ==> r) ==> r ]]))   -- case-split
#eval evalNanocop (NANOCOP [] ([[ (!x:A. (P:A->bool) x ==> (Q:A->bool) x) /\
                     (!x:A. Q x ==> (R:A->bool) x) /\ P a ==> R a ]]))       -- barbara
#eval evalNanocop (NANOCOP [] ([[ (?x:A. !y:A. (R:A->A->bool) x y) ==> (!y:A. ?x:A. R x y) ]])) -- ex-forall
#eval evalNanocop (NANOCOP [] ([[ (p:bool) /\ (p ==> q) ==> q ]]))                       -- modus ponens
#eval evalNanocop (NANOCOP [] ([[ (p:bool) /\ (q \/ r) ==> (p /\ q) \/ (p /\ r) ]]))     -- distrib (non-clausal matrix)
#eval evalNanocop (NANOCOP [] ([[ (a:A) = b /\ (b:A) = c ==> (a:A) = c ]]))              -- eq-trans
#eval evalNanocop (NANOCOP [] ([[ (P:A->bool) a ==> (?x:A. P x) ]]))                     -- exists-intro
#eval evalNanocop (NANOCOP [] ([[ (!x:A. (P:A->bool) x ==> (Q:A->bool) x) /\
                     (!x:A. Q x ==> (R:A->bool) x) /\ (!x:A. R x ==> (S:A->bool) x) /\
                     P a ==> S a ]]))                                        -- chain3
#eval evalNanocop (prove ([[ (p:bool) \/ ~p ]]) (NANOCOP_TAC []))                       -- NANOCOP_TAC
