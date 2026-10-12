/- File: HolTest/CoreTest.lean
Runtime test suite: the core layers - parsing/printing, the kernel, basics,
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

*** THIS FILE IS DELIBERATELY INSPECTION-STYLE. *** Its `#eval`s PRINT values
with the expected result in a trailing comment; they do NOT self-check, so it
contributes ZERO to the `-> OK` assertion total and that is expected, not a gap.
Its job is to be a readable CROSS-LAYER smoke test of the parse -> kernel ->
print pipeline: a crash or a glaringly wrong value shows up here first, in one
place, spanning modules that no single per-module test file owns.

PER-MODULE, SELF-CHECKING tests live in their own files and are the place to add
new coverage:
  HolTest/FusionTest.lean  the kernel: every primitive rule, its failure text,
                           and the soundness side conditions
  HolTest/DruleTest.lean   matching and unification, incl. the higher-order
                           `PART_MATCH` regression probe
  HolTest/NetsTest.lean    term nets: enter / lookup / merge_nets
  HolTest/ItabTest.lean    ITAUT, with Pelletier-style propositions
  HolTest/PretermTest.lean preterm elaboration and type inference -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Tests: the core layers - parsing/printing, the kernel, basics,         -/
/- bool, equal, drule, tactics, simp and itab.                            -/
/- ---------------------------------------------------------------------- -/

-- parsing / printing (via [[ ]] quotation)
#eval [[ \x. x ]]                    -- \(x:?0). x   (invented type var)
#eval [[ p /\ q ]]                   -- p /\ q
#eval [[ !x. x ]]                    -- !x. x
#eval [[ ?x. x ]]                    -- ?x. x
#eval [[ p ==> q ==> r ]]            -- p ==> q ==> r
#eval [[ p /\ q \/ r ]]              -- p /\ q \/ r
#eval [[ if p then q else p ]]       -- if p then q else p
#eval [[ :bool->bool ]]              -- bool->bool

-- propositional rules
#eval ASSUME p                                             -- p |- p
#eval CONJ (ASSUME p) (ASSUME q)                         -- p, q |- p /\ q
#eval CONJUNCT1 (CONJ (ASSUME p) (ASSUME q))           -- p, q |- p
#eval CONJUNCT2 (CONJ (ASSUME p) (ASSUME q))           -- p, q |- q
#eval DISCH p (ASSUME q)                                 -- q |- p ==> q
#eval MP (ASSUME [[ p ==> q ]]) (ASSUME p) -- p, p ==> q |- q
#eval ADD_ASSUM q (ASSUME p)                             -- p, q |- p
#eval IMP_ANTISYM_RULE (DISCH p (ASSUME q)) (DISCH q (ASSUME p))  -- p, q |- p <=> q
#eval IMP_TRANS (DISCH p (ASSUME q)) (DISCH q (ASSUME p))         -- p, q |- p ==> p
#eval DISCH_ALL (CONJ (ASSUME p) (ASSUME q))           -- |- q ==> p ==> p /\ q

-- disjunction
#eval DISJ1 (ASSUME p) q                                 -- p |- p \/ q
#eval DISJ2 p (ASSUME q)                                 -- q |- p \/ q
#eval DISJ_CASES (DISJ1 (ASSUME p) p) (ASSUME p) (ASSUME p)  -- p |- p

-- quantifiers
#eval GEN x (REFL x)                                     -- |- !x. x <=> x
#eval SPEC p (GEN x (REFL x))                          -- |- p <=> p
#eval SPEC_ALL (GEN x (REFL x))                        -- |- x <=> x
#eval GEN_ALL (GEN x (REFL x))                         -- |- !x. x <=> x
#eval SPEC tT (ASSUME [[ !x. x ==> x ]])                 -- !x. x ==> x |- T ==> T
#eval ISPEC tT (ASSUME [[ !x. x ==> x ]])                -- !x. x ==> x |- T ==> T
#eval SPECL [tT, fF] (ASSUME [[ !x y. x ==> y ]]) -- !x y. x ==> y |- T ==> F
#eval ISPECL [tT, fF] (ASSUME [[ !x y. x ==> y ]]) -- !x y. x ==> y |- T ==> F

-- existentials
#eval SIMPLE_EXISTS x (ASSUME [[ (x:bool) = x ]])        -- x<=>x |- ?x. x<=>x
#eval EXISTS (([[ ?x. (x:bool) = x ]]), tT) (REFL tT)   -- |- ?x. x<=>x
#eval CHOOSE (x, ASSUME ([[ ?x. (x:bool) = x ]])) (ADD_ASSUM ([[ (x:bool) = x ]]) TRUTH)  -- ?x. x<=>x |- T

-- truth / negation / falsity
#eval EQT_INTRO (ASSUME p)                               -- p |- p <=> T
#eval EQT_ELIM (EQT_INTRO (ASSUME p))                  -- p |- p
#eval NOT_ELIM (ASSUME [[ ~p ]])                  -- ~p |- p ==> F
#eval NOT_INTRO (ASSUME [[ p ==> F ]])            -- p ==> F |- ~p
#eval CONTR p (ASSUME fF)                                -- F |- p

-- conversions
#eval BETA_CONV ([[ (\x:bool. x) T ]])                     -- |- (\x. x) T <=> T
#eval CONV_RULE (ONCE_DEPTH_CONV BETA_CONV) (REFL ([[ (\x:bool. x) T ]]))  -- |- T <=> T
#eval BETA_RULE (REFL ([[ (\x:bool. x) T ]]))              -- |- T <=> T
#eval GSYM (REFL p)                                        -- |- p <=> p
#eval SUBS [(EQT_INTRO (ASSUME p) : thm)] (ASSUME p)       -- p |- T  (rewrite p := T)

-- syntax helpers
#eval mk_conj p q                                          -- p /\ q
#eval list_mk_conj [p, q, p]                               -- p /\ q /\ p
#eval mk_forall x p                                        -- !x. p
#eval atoms ([[ p /\ q ==> p ]])                           -- [p, q]

-- Drule

-- Congruence rules (standalone). (Boolean `=` prints as `<=>`.)
#eval MK_CONJ (REFL p) (REFL q)                            -- |- p /\ q <=> p /\ q
#eval MK_DISJ (REFL p) (REFL q)                            -- |- p \/ q <=> p \/ q

-- INSTANTIATE: the empty instantiation is a no-op on `|- p = p`.
#eval INSTANTIATE ([], [], []) (REFL p)                    -- |- p <=> p

-- Drule's matching and unification machinery moved to HolTest/DruleTest.lean,
-- where each case is a SELF-CHECKING assertion rather than a value dump:
--   term_match, PART_MATCH, GEN_PART_MATCH, MATCH_MP, instantiate, INSTANTIATE,
--   INSTANTIATE_ALL, type_unify, term_unify, term_type_unify, mk_thm, BETAS_CONV,
--   deep_alpha, MK_CONJ/MK_DISJ/MK_FORALL/MK_EXISTS, HIGHER_REWRITE_CONV.
-- That file also carries the higher-order `PART_MATCH` regression probe.

-- MK_FORALL / MK_EXISTS: congruence under a binder.
#eval MK_FORALL x (REFL x)                                 -- |- (!x. x) <=> (!x. x)
#eval MK_EXISTS x (REFL x)                                 -- |- (?x. x) <=> (?x. x)

-- BETAS_CONV: multiple beta-reduction of an application.
#eval BETAS_CONV ([[ (\x:bool. x) T ]])                    -- |- (\x. x) T <=> T

-- MP_CONV: eliminate a `T` antecedent using ALL_CONV (proves `T <=> T`).
#eval MP_CONV ALL_CONV (ASSUME [[ T ==> q ]])       -- T ==> q |- q

-- Tactics (prove)
-- Prove `p ==> p`: discharge, then close with the assumption.
#eval prove ([[ p ==> p ]])
        (THEN DISCH_TAC (FIRST_ASSUM ACCEPT_TAC))          -- |- p ==> p

-- Prove `p ==> p \/ q`: discharge, choose left disjunct, use assumption.
#eval prove ([[ p ==> p \/ q ]])
        (THEN DISCH_TAC (THEN DISJ1_TAC (FIRST_ASSUM ACCEPT_TAC)))  -- |- p ==> p \/ q

-- Prove `p /\ q ==> p`: discharge, then accept the first conjunct.
#eval prove ([[ p /\ q ==> p ]])
        (THEN DISCH_TAC (POP_ASSUM (fun th => ACCEPT_TAC (CONJUNCT1 th))))  -- |- p /\ q ==> p

-- Prove `p ==> q ==> p /\ q`: two discharges, split, close both by assumption.
#eval prove ([[ p ==> q ==> p /\ q ]])
        (THEN (REPEAT DISCH_TAC)
              (THEN CONJ_TAC (FIRST_ASSUM ACCEPT_TAC)))    -- |- p ==> q ==> p /\ q

-- Interactive: g / e / top_thm on `p ==> p`.
#eval do
  let _ ← g ([[ p ==> p ]])
  let _ ← e DISCH_TAC
  let _ ← e (FIRST_ASSUM ACCEPT_TAC)
  match ← top_thm with
  | th => pure th                                          -- |- p ==> p

-- Tactics (more)
-- EQ_TAC: prove `p <=> p` by proving both implications (THEN closes both).
#eval prove ([[ p <=> p ]])
        (THEN EQ_TAC (THEN DISCH_TAC (FIRST_ASSUM ACCEPT_TAC)))     -- |- p <=> p

-- GEN_TAC + REFL_TAC: prove `!x. x = x`.
#eval prove ([[ !x:bool. x = x ]])
        (THEN (GEN_TAC) (REFL_TAC))                                 -- |- !x. x = x

-- EXISTS_TAC: prove `?x. x = T` with witness T.
#eval prove ([[ ?x:bool. x = T ]])
        (THEN (EXISTS_TAC ([[ T ]])) (REFL_TAC))                    -- |- ?x. x = T

-- STRIP_TAC: strip `p /\ q ==> q /\ p`, then split and close by assumption.
#eval prove ([[ p /\ q ==> q /\ p ]])
        (THEN STRIP_TAC (THEN CONJ_TAC (FIRST_ASSUM ACCEPT_TAC)))   -- |- p /\ q ==> q /\ p

-- MP_TAC: prove `p ==> (p ==> q) ==> q` using MATCH_MP_TAC on the assumption.
#eval prove ([[ p ==> (p ==> q) ==> q ]])
        (THEN DISCH_TAC (THEN DISCH_TAC
          (THEN (FIRST_X_ASSUM MATCH_MP_TAC)
                (FIRST_ASSUM ACCEPT_TAC))))                         -- |- p ==> (p ==> q) ==> q

-- MP_TAC proper: goal `q`, feed assumption `q` back in via MP_TAC then discharge.
--   prove `q ==> q`: MP_TAC on the discharged hypothesis, then discharge again.
#eval prove ([[ q ==> q ]])
        (THEN DISCH_TAC
          (THEN (FIRST_ASSUM MP_TAC) (THEN DISCH_TAC (FIRST_ASSUM ACCEPT_TAC))))
                                                                    -- |- q ==> q

-- ORELSE / TRY: a failing tactic recovered by ALL_TAC/second branch.
#eval prove ([[ p ==> p ]])
        (THEN (ORELSE NO_TAC DISCH_TAC) (FIRST_ASSUM ACCEPT_TAC))   -- |- p ==> p

-- REPEAT + CONJ over 3 conjuncts, all closed by the stripped assumptions.
#eval prove ([[ p /\ q /\ p ==> p /\ q /\ p ]])
        (THEN STRIP_TAC (THEN (REPEAT CONJ_TAC) (FIRST_ASSUM ACCEPT_TAC)))
                                                                    -- |- p /\ q /\ p ==> p /\ q /\ p

-- CHEAT_TAC: prove an arbitrary goal via a fresh axiom (UNSOUND demo).
#eval prove ([[ p /\ q ]]) CHEAT_TAC                         -- |- p /\ q  (via axiom)

-- Tactics (coverage: previously untested)
-- DISJ_CASES_THEN2: prove `p \/ p ==> p` by casing and accepting each branch.
#eval prove ([[ p \/ p ==> p ]])
        (DISCH_THEN (DISJ_CASES_THEN2 ACCEPT_TAC ACCEPT_TAC))       -- |- p \/ p ==> p

-- DISJ_CASES_TAC: prove `p \/ q ==> q \/ p` (commute) via explicit case-split.
#eval prove ([[ p \/ q ==> q \/ p ]])
        (THEN DISCH_TAC (THEN (FIRST_X_ASSUM DISJ_CASES_TAC)
          (ORELSE (THEN DISJ2_TAC (FIRST_ASSUM ACCEPT_TAC))
                  (THEN DISJ1_TAC (FIRST_ASSUM ACCEPT_TAC)))))      -- |- p \/ q ==> q \/ p

-- SUBGOAL_THEN: prove `p ==> p`, routing through an intermediate lemma `p`.
#eval prove ([[ p ==> p ]])
        (THEN DISCH_TAC
          (THEN (SUBGOAL_THEN ([[ p:bool ]]) ACCEPT_TAC)
                (FIRST_ASSUM ACCEPT_TAC)))                          -- |- p ==> p

-- UNDISCH_TAC: discharge then re-undischarge the same assumption.
#eval prove ([[ p ==> p ]])
        (THEN DISCH_TAC (THEN (UNDISCH_TAC ([[ p:bool ]]))
          (THEN DISCH_TAC (FIRST_ASSUM ACCEPT_TAC))))               -- |- p ==> p

-- SPEC_TAC: generalize `T` back to a variable, then prove `!x. x = x`.
#eval prove ([[ T = T ]])
        (THEN (SPEC_TAC (([[ T ]]), ([[ x:bool ]])))
          (THEN (GEN_TAC) (REFL_TAC)))                              -- |- T = T

-- BETA_TAC: beta-reduce the goal, then close by reflexivity.
#eval prove ([[ (\x:bool. x) T = T ]])
        (THEN (BETA_TAC) (REFL_TAC))                                -- |- (\x. x) T = T

-- AP_TERM_TAC: reduce `f a = f b` to `a = b`, closed by reflexivity here.
#eval prove ([[ (\y:bool. y) T = (\y:bool. y) T ]])
        (REFL_TAC)                                                  -- |- (\y. y) T = (\y. y) T

-- CONTR_TAC: from a `F` assumption, close any goal.
#eval prove ([[ F ==> p ]])
        (THEN DISCH_TAC (FIRST_ASSUM CONTR_TAC))                    -- |- F ==> p

-- Itab (ITAUT intuitionistic prover)
-- Prove propositional tautologies automatically via ITAUT (iterative deepening
-- intuitionistic search; may print "Searching with limit N" as it deepens).
#eval ITAUT ([[ p ==> p ]])                          -- |- p ==> p
#eval ITAUT ([[ p /\ q ==> p ]])                     -- |- p /\ q ==> p
#eval ITAUT ([[ p ==> q ==> p ]])                    -- |- p ==> q ==> p
#eval ITAUT ([[ p /\ q ==> q /\ p ]])                -- |- p /\ q ==> q /\ p

-- Simp (rewriting / simplification)
-- REWR_CONV: rewrite p to q using the assumption p = q (REWR_CONV is an ioconv).
#eval REWR_CONV (ASSUME [[ (p:bool) = q ]]) p                      -- p <=> q |- p <=> q

-- REWRITE_CONV applies the conversion in one step (HOL Light style).
#eval REWRITE_CONV [ASSUME ([[ (p:bool) = q ]])] ([[ p /\ p ]])
                                                                   -- p<=>q |- p /\ p <=> q /\ q

-- REWRITE_RULE: rewrite the theorem `p /\ p` with `p = q` (returns IO (Except thm)).
#eval REWRITE_RULE [ASSUME ([[ (p:bool) = q ]])] (ASSUME ([[ p /\ p ]]))
                                                                   -- p<=>q, p/\p |- q /\ q

-- SIMP_CONV: simplify `p /\ p` with `p = q` in one step.
#eval SIMP_CONV [ASSUME ([[ (p:bool) = q ]])] ([[ p /\ p ]])
                                                                   -- p<=>q |- p /\ p <=> q /\ q

-- Simp (more coverage)
-- Chained rewriting to a fixpoint: p=q and q=r rewrite p all the way to r.
#eval REWRITE_CONV [ASSUME ([[ (p:bool) = q ]]), ASSUME ([[ (q:bool) = r ]])] p
                                                                   -- p<=>q, q<=>r |- p <=> r

-- Rewriting under a binder (congruence descent into the ! body).
#eval REWRITE_CONV [ASSUME ([[ (p:bool) = q ]])] ([[ !x:bool. p ]])
                                                                   -- p<=>q |- (!x. p) <=> (!x. q)

-- ONCE_REWRITE_CONV: rewrite once at each descended position.
#eval ONCE_REWRITE_CONV [ASSUME ([[ (p:bool) = q ]])] ([[ p /\ p ]])
                                                                   -- p<=>q |- p /\ p <=> q /\ q

-- PURE_REWRITE_RULE: rewrite the theorem `p` with `p = q`, giving `q`.
#eval PURE_REWRITE_RULE [ASSUME ([[ (p:bool) = q ]])] (ASSUME p)  -- p<=>q, p |- q

-- SIMP_RULE: simplify the theorem `p /\ p` with `p = q`.
#eval SIMP_RULE [ASSUME ([[ (p:bool) = q ]])] (ASSUME ([[ p /\ p ]]))
                                                                   -- p<=>q, p/\p |- q /\ q

-- new_definition
-- new_definition: define a fresh nullary constant TT := T (declares a constant).
#eval new_definition ([[ TT = T ]])                                -- |- TT <=> T
