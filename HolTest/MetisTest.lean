/- File: HolTest/MetisTest.lean
Runtime test suite: metis.ml - METIS automation with proof reconstruction
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Tests: metis.ml - METIS automation with proof reconstruction.          -/
/- ---------------------------------------------------------------------- -/


-- ========================================================================
-- metis.ml : METIS first-order automation with proof reconstruction
-- Comprehensive test battery. Reserved-constant caveats: `F`/`T` are falsity/
-- truth constants — never use as predicate/variable names (use G/H/... instead).
-- Every `.ok` prints the reconstructed `|- ...` theorem; every intended
-- non-theorem must print "correctly failed". `UNSOUND!!` never appears.
-- ========================================================================

#eval evalMetis (METIS [] ([[ (p:bool) \/ ~p ]]))                                       -- excluded-middle
-- modus ponens
#eval evalMetis (METIS [] ([[ (p:bool) /\ (p ==> q) ==> q ]]))                          -- modus-ponens
-- modus tollens
#eval evalMetis (METIS [] ([[ ((p:bool) ==> q) /\ ~q ==> ~p ]]))                        -- modus-tollens
-- implication chain (hypothetical syllogism, several resolution steps)
#eval evalMetis (METIS [] ([[ ((p:bool) ==> q) ==> (q ==> r) ==> (r ==> s) ==> p ==> s ]])) -- imp-chain
-- case analysis over a disjunction
#eval evalMetis (METIS [] ([[ ((p:bool) \/ q) /\ (p ==> r) /\ (q ==> r) ==> r ]]))       -- case-split
-- De Morgan
#eval evalMetis (METIS [] ([[ ~((p:bool) /\ q) <=> ~p \/ ~q ]]))                         -- de-morgan
-- distributivity
#eval evalMetis (METIS [] ([[ (p:bool) /\ (q \/ r) <=> (p /\ q) \/ (p /\ r) ]]))         -- distrib
-- biconditional / Peirce's law
#eval evalMetis (METIS [] ([[ (((p:bool) ==> q) ==> p) ==> p ]]))                        -- peirce
-- iff is symmetric+transitive (contradiction search)
#eval evalMetis (METIS [] ([[ ((p:bool) <=> q) /\ (q <=> r) ==> (p <=> r) ]]))           -- iff-trans

-- 2. Quantifier reasoning
-- universal instantiation
#eval evalMetis (METIS [] ([[ (!x:A. (P:A->bool) x /\ (Q:A->bool) x) ==> P a ]]))        -- forall-inst
-- existential introduction (witness)
#eval evalMetis (METIS [] ([[ (P:A->bool) a ==> (?x:A. P x) ]]))                         -- exists-intro
-- quantifier swap (exists-forall implies forall-exists)
#eval evalMetis (METIS [] ([[ (?x:A. !y:A. (R:A->A->bool) x y) ==> (!y:A. ?x:A. R x y) ]])) -- ex-forall=>forall-ex
-- syllogism (Barbara): all P are Q, all Q are R, P a  ==>  R a
#eval evalMetis (METIS [] ([[ (!x:A. (P:A->bool) x ==> (Q:A->bool) x) /\
                               (!x:A. Q x ==> (R:A->bool) x) /\ P a ==> R a ]])) -- barbara
-- ∀ distributes over ∧
#eval evalMetis (METIS [] ([[ (!x:A. (P:A->bool) x /\ (Q:A->bool) x) <=>
                               (!x:A. P x) /\ (!x:A. Q x) ]]))                -- forall-conj
-- ∃ distributes over ∨
#eval evalMetis (METIS [] ([[ (?x:A. (P:A->bool) x \/ (Q:A->bool) x) <=>
                               (?x:A. P x) \/ (?x:A. Q x) ]]))                -- exists-disj
-- pushing negation through a quantifier
#eval evalMetis (METIS [] ([[ ~(!x:A. (P:A->bool) x) <=> (?x:A. ~P x) ]]))               -- not-forall
-- Andrews' challenge
#eval evalMetis (METIS [] ([[ (?x:A. !y:A. (P:A->bool) x <=> P y) ==>
                               ((?x:A. P x) <=> (!y:A. P y)) ]]))             -- andrews

-- 3. Equality & paramodulation (Metis's forte)
-- reflexivity
#eval evalMetis (METIS [] ([[ (a:A) = a ]]))                                            -- refl
-- symmetry
#eval evalMetis (METIS [] ([[ (a:A) = b ==> (b:A) = a ]]))                              -- sym
-- transitivity
#eval evalMetis (METIS [] ([[ (a:A) = b /\ (b:A) = c ==> (a:A) = c ]]))                 -- eq-trans
-- function congruence
#eval evalMetis (METIS [] ([[ (x:A) = y ==> (f:A->B) x = f y ]]))                       -- fun-cong
-- 2-arg function congruence
#eval evalMetis (METIS [] ([[ (x:A) = u /\ (y:A) = v ==> (g:A->A->B) x y = g u v ]]))    -- fun2-cong
-- predicate congruence (substitution of equals)
#eval evalMetis (METIS [] ([[ (x:A) = y /\ (P:A->bool) x ==> P y ]]))                    -- pred-cong
-- paramodulation chain: f(f(f a))=a, f(f a)=a  ==>  f a = a
#eval evalMetis (METIS [] ([[ (f:A->A) ((f:A->A) ((f:A->A) a)) = a /\ (f:A->A) ((f:A->A) a) = a
                               ==> (f:A->A) a = a ]]))                        -- eq-fun-chain
-- rewriting under a predicate through several equalities
#eval evalMetis (METIS [] ([[ (a:A) = b /\ (b:A) = c /\ (P:A->bool) a ==> P c ]]))       -- rewrite-chain
-- congruence with nested terms
#eval evalMetis (METIS [] ([[ (x:A) = y ==> (f:A->A) ((f:A->A) x) = (f:A->A) ((f:A->A) y) ]])) -- nested-cong

-- 4. Combined relations / group-flavoured problems
-- reflexivity from symmetry+transitivity+seriality
#eval evalMetis (METIS [] ([[ (!x y:A. (R:A->A->bool) x y ==> R y x) /\
                               (!x y z:A. R x y /\ R y z ==> R x z) /\
                               (!x:A. ?y:A. R x y) ==> (!x:A. R x x) ]]))     -- refl-from
-- left inverse + associativity ⇒ right inverse-ish (equational)
#eval evalMetis (METIS [] ([[ (!x:A. (m:A->A->A) e x = x) /\
                               (!x y z:A. m (m x y) z = m x (m y z)) /\
                               (!x:A. m ((i:A->A) x) x = e) ==>
                               (!x:A. m ((i:A->A) x) x = e) ]]))              -- group-lemma

-- 5. With supplied lemmas (POLY_ASSUME_TAC path)
#eval evalWithLemmas METIS [([[ !x:A. (x:A) = x ]])] ([[ (a:A) = a ]]) -- with-refl-lemma
#eval evalWithLemmas METIS [([[ !x y:A. (x:A) = y ==> (y:A) = x ]])] ([[ (a:A) = b ==> (b:A) = a ]]) -- with-sym-lemma

-- 6. Pelletier problems (deeper search / factoring / paramodulation)
-- P18: ?y. !x. G y ==> G x
#eval evalMetis (METIS [] ([[ ?y:A. !x:A. (G:A->bool) y ==> (G:A->bool) x ]]))           -- P18
-- P19
#eval evalMetis (METIS [] ([[ ?x:A. !y z:A. ((P:A->bool) y ==> (Q:A->bool) z) ==> (P x ==> Q x) ]])) -- P19
-- P24-style: several clauses, negation, disjunction
#eval evalMetis (METIS [] ([[ ~(?x:A. (S:A->bool) x /\ (Q:A->bool) x) /\
                               (!x:A. (P:A->bool) x ==> Q x \/ (R:A->bool) x) /\
                               ~(?x:A. P x) ==> (!x:A. P x ==> R x) ]]))       -- P24ish
-- P39: ~ ?x. !y. F y x <=> ~ F y y   (no set of all non-self-membered)
#eval evalMetis (METIS [] ([[ ~(?x:A. !y:A. (Fr:A->A->bool) y x <=> ~Fr y y) ]]))         -- P39
-- P35 (drinker-like existence)
#eval evalMetis (METIS [] ([[ ?x y:A. (P:A->A->bool) x y ==> (!x y:A. P x y) ]]))         -- P35

-- 7. Tactic entry points
#eval evalMetis (prove ([[ (p:bool) \/ ~p ]]) (METIS_TAC []))                            -- METIS_TAC
-- ASM_METIS_TAC uses the assumptions: discharge, then prove from them
#eval evalMetis (prove ([[ ((!x:A. (P:A->bool) x ==> (Q:A->bool) x)) ==> P a ==> Q a ]])
           (THEN DISCH_TAC (THEN DISCH_TAC (ASM_METIS_TAC []))))              -- ASM_METIS_TAC
-- METIS_TAC on an equational goal
#eval evalMetis (prove ([[ (a:A) = b /\ (b:A) = c ==> (a:A) = c ]]) (METIS_TAC []))       -- METIS_TAC eq

-- 8. Soundness: non-theorems MUST be rejected
#eval evalNonThm (METIS [] ([[ (p:bool) ]]))                          -- non-thm (bare p)
#eval evalNonThm (METIS [] ([[ (?x:A. (P:A->bool) x) ==> (!x:A. (P:A->bool) x) ]])) -- non-thm (ex=>all)
#eval evalNonThm (METIS [] ([[ (!x:A. ?y:A. (R:A->A->bool) x y) ==> (?y:A. !x:A. R x y) ]])) -- non-thm (all-ex=>ex-all)
#eval evalNonThm (METIS [] ([[ ((p:bool) ==> q) ==> (q ==> p) ]]))    -- non-thm (converse)


-- 9. Previously-untested code paths
-- (a) Case-splitting BEFORE Metis proper: split_limit > 0 exercises Meson.SPLIT_TAC
--     inside FOL_PREPARE_TAC (the default limit 0 makes it a no-op).
#eval evalMetis (METIS_SPLIT 2 [] ([[ ((p:bool) \/ q) /\ (p ==> r) /\ (q ==> r) ==> r ]])) -- split=2 case
#eval evalMetis (METIS_SPLIT 4 [] ([[ (a:A) = b /\ (b:A) = c ==> (a:A) = c ]]))          -- split=4 eq
#eval evalMetis (prove ([[ ((p:bool) <=> q) /\ (q <=> r) ==> (p <=> r) ]])
           (GEN_METIS_TAC_SPLIT 3 []))                                        -- GEN_METIS_TAC split=3 iff

-- (b) Deeper search: many resolution/paramodulation steps, forcing the Waiting
--     clause-weighting (random-finite-Model check) + subsumption to matter.
-- Pelletier 25
#eval evalMetis (METIS [] ([[ (?x:A. (P:A->bool) x) /\
                               (!x:A. (Fr:A->bool) x ==> ~(G:A->bool) x /\ (R:A->bool) x) /\
                               (!x:A. P x ==> G x /\ Fr x) /\
                               ((!x:A. P x ==> Q x) \/ (?x:A. P x /\ (H:A->bool) x))
                               ==> (?x:A. Q x /\ P x) ]]))                     -- P25
-- Pelletier 26
#eval evalMetis (METIS [] ([[ ((?x:A. (P:A->bool) x) <=> (?x:A. (Q:A->bool) x)) /\
                               (!x y:A. P x /\ Q y ==> ((R:A->bool) x <=> (S:A->bool) y))
                               ==> ((!x:A. P x ==> R x) <=> (!x:A. Q x ==> S x)) ]])) -- P26
-- transitivity closure forcing several paramodulation/resolution rounds
#eval evalMetis (METIS [] ([[ (!x y z:A. (R:A->A->bool) x y /\ R y z ==> R x z) /\
                               (R:A->A->bool) a b /\ R b c /\ R c d ==> R a d ]])) -- trans4

-- (c) Paramodulation INTO an equation (deduceParamodulationInto): an equation's
--     subterm is rewritten by another equation.
#eval evalMetis (METIS [] ([[ (a:A) = b /\ (f:A->A) a = c ==> (f:A->A) b = c ]]))         -- para-into
#eval evalMetis (METIS [] ([[ (a:A) = b /\ (g:A->A->A) a a = (g:A->A->A) b b ==>
                               (g:A->A->A) a a = (g:A->A->A) b b ]]))          -- para-into2

-- (d) Factoring: a clause with two unifiable literals must be factored to close.
#eval evalMetis (METIS [] ([[ (!x y:A. (P:A->bool) x \/ P y) ==> (?z:A. P z) ]]))         -- factor

-- (e) Multiple supplied lemmas used together (POLY_ASSUME over several thms).
#eval evalWithLemmas METIS
        [([[ !x:A. (x:A) = x ]]), ([[ !x y:A. (x:A) = y ==> (y:A) = x ]])]
        ([[ (a:A) = b ==> (b:A) = a /\ (a:A) = a ]])                          -- multi-lemma

-- (f) Determinism: the same goal proved twice must give the identical theorem
--     (RNG is reseeded to mkStdGen 0 on each call — reconstruction is stable).
#eval evalDeterministic (METIS [] ([[ (?x:A. !y:A. (R:A->A->bool) x y) ==> (!y:A. ?x:A. R x y) ]])) -- determinism

-- (g) Larger equational goal: predicate holds after a 3-step rewrite through
--     distinct equations (exercises Units store + repeated paramodulation).
#eval evalMetis (METIS [] ([[ (a:A) = b /\ (b:A) = c /\ (c:A) = d /\ (P:A->bool) a ==> P d ]])) -- rewrite3

-- 10. Harder problems (stress search / subsumption / weighting / paramod)
-- Pelletier 43: equality-defined predicate (Q x y <=> !z. F z x <=> F z y) is
--   symmetric.  Heavy on paramodulation + iff handling.
#eval evalMetis (METIS [] ([[ (!x y:A. (Q:A->A->bool) x y <=>
                                 (!z:A. (Fr:A->A->bool) z x <=> Fr z y))
                               ==> (!x y:A. Q x y <=> Q y x) ]]))              -- P43

-- Pelletier 44
#eval evalMetis (METIS [] ([[ (!x:A. (P:A->bool) x ==>
                                 (?y:A. (G:A->bool) y /\ (H:A->A->bool) x y) /\
                                 (?y:A. G y /\ ~H x y)) /\
                               (?x:A. (J:A->bool) x /\ (!y:A. G y ==> H x y))
                               ==> (?x:A. J x /\ ~P x) ]]))                    -- P44

-- Pelletier 45
#eval evalMetis (METIS [] ([[ (!x:A. (P:A->bool) x /\
                                 (!y:A. (G:A->bool) y /\ (H:A->A->bool) x y ==> (J:A->A->bool) x y)
                                 ==> (!y:A. G y /\ H x y ==> (R:A->bool) y)) /\
                               ~(?y:A. (L:A->bool) y /\ R y) /\
                               (?x:A. P x /\ (!y:A. H x y ==> L y) /\
                                 (!y:A. G y /\ H x y ==> J x y))
                               ==> (?x:A. P x /\ ~(?y:A. G y /\ H x y)) ]]))    -- P45

-- Group theory: from the left axioms, x * inv x = id (right inverse).
-- One of the classic paramodulation/equational stress tests.
#eval evalMetis (METIS [] ([[ (!x:A. (m:A->A->A) e x = x) /\
                               (!x:A. m ((i:A->A) x) x = e) /\
                               (!x y z:A. m (m x y) z = m x (m y z))
                               ==> (!x:A. m x ((i:A->A) x) = e) ]]))           -- group-right-inv

-- Group theory: x * id = x (right identity) from the left axioms.
#eval evalMetis (METIS [] ([[ (!x:A. (m:A->A->A) e x = x) /\
                               (!x:A. m ((i:A->A) x) x = e) /\
                               (!x y z:A. m (m x y) z = m x (m y z))
                               ==> (!x:A. m x e = x) ]]))                      -- group-right-id

-- Equation orientation / KBO: if f is an involution and commutes-ish.
#eval evalMetis (METIS [] ([[ (!x:A. (f:A->A) ((f:A->A) x) = x) /\
                               (!x:A. (f:A->A) ((g:A->A) x) = (g:A->A) ((f:A->A) x))
                               ==> (!x:A. (f:A->A) ((g:A->A) ((f:A->A) x)) = (g:A->A) x) ]])) -- involution

-- Deep relational: transitive + symmetric + total-reachability closure.
#eval evalMetis (METIS [] ([[ (!x y:A. (R:A->A->bool) x y ==> R y x) /\
                               (!x y z:A. R x y /\ R y z ==> R x z) /\
                               (R:A->A->bool) a b /\ R c b /\ R c d ==> R a d ]])) -- rel-closure

-- Combined equality + relation congruence (substitute equal into a relation
-- through a function symbol; several paramodulation steps).
#eval evalMetis (METIS [] ([[ (a:A) = b /\ (!x:A. (P:A->bool) ((f:A->A) x)) ==> P ((f:A->A) b) ]])) -- eq+cong

-- A goal that benefits from subsumption: redundant hypotheses.
#eval evalMetis (METIS [] ([[ (!x:A. (P:A->bool) x ==> (Q:A->bool) x) /\
                               (!x:A. P x ==> Q x) /\ (!x:A. Q x ==> (R:A->bool) x) /\ P a
                               ==> R a ]]))                                    -- subsume

-- Harder non-theorem (must still be rejected): near-miss of a valid schema.
#eval evalNonThm (METIS [] ([[ (!x:A. (P:A->bool) x ==> (Q:A->bool) x) /\ Q a ==> P a ]])) -- non-thm (affirm-consequent)

/- ---------------------------------------------------------------------- -/
/- Metis's ordered-set fold and leftist heap, against OCaml's semantics.   -/
/- ---------------------------------------------------------------------- -/

-- `Mset.foldr f a s = Se.fold (fun x acc -> f (x,acc)) s a` (metis.ml 1893), and
-- OCaml's `Set.fold` applies `f` to the SMALLEST element FIRST.  Consing each
-- element onto the accumulator therefore yields DESCENDING order.  The port's
-- `List.foldr` applied `f` to the LARGEST first, giving ascending order and
-- reversing every non-commutative set fold in Metis.
#eval (do
  let s := [3, 1, 2].foldl HolCore.Metis.Prover.Intset.add HolCore.Metis.Prover.Intset.empty
  let r := HolCore.Metis.Prover.Intset.foldl (fun (x, acc) => x :: acc) ([] : List Int) s
  if r == [3, 2, 1] then IO.println "Metis set fold visits smallest first (metis.ml 1893) -> OK"
  else IO.println s!"Metis set fold order -> MISMATCH got {r}, OCaml [3; 2; 1]")

-- Leftist heap (metis.ml 1950-1970): OCaml's `merge` passes the ORIGINAL node
-- through (`as h1`), so every node satisfies `rank = rank right + 1` and
-- `rank left >= rank right`.  The port rebuilt the passed-through node with rank
-- 0, breaking the invariant (and so the tie-break order among equal-priority
-- clauses).  Check the invariant over every node after sixteen insertions.
open HolCore.Metis.Prover.Heap in
#eval (do
  let h := (List.range 16).foldl (fun h i => add h (Int.ofNat ((i * 7) % 16)))
             (newHeap (fun (a b : Int) => if a < b then -1 else if a == b then 0 else 1))
  let rec ok : Node Int → Bool
    | .Em => true
    | .Tr r _ a b => r == rank b + 1 && rank a ≥ rank b && ok a && ok b
  if ok h.root then IO.println "Metis leftist heap invariant after 16 inserts -> OK"
  else IO.println "Metis leftist heap -> MISMATCH rank invariant broken")
