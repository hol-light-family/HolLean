/- File: HolTest/TheoremsTest.lean
Runtime test suite: theorems.ml (the standard logical library) and its
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Tests: theorems.ml (the standard logical library) and its              -/
/- tactic DSL (FIX_TAC/INTRO_TAC/DESTRUCT_TAC/CLAIM_TAC).                 -/
/- ---------------------------------------------------------------------- -/


-- Theorems (theorems.ml standard library)
-- Forcing any theorem runs setupTheorems once (proving all ~65 + populating
-- basic rewrites). This is SLOW (many ITAUT iterative-deepening searches run
-- sequentially) and prints many "Searching with limit N" lines — let it finish.
-- Regression: rewriting under a binder whose bound var collides with a free var
-- in the rewrite RHS must alpha-rename to avoid capture (was a no-op bug).
#eval REWRITE_CONV [ASSUME ([[ !y:A. (P:A->bool) y <=> (x:A = y) ]])] ([[ ?x:A. (P:A->bool) x ]])
-- expected: |- (?x. P x) <=> (?x'. x = x')   [alpha-renamed]
#eval EQ_REFL                                                      -- |- !x. x = x
#eval EQ_SYM_EQ                                                    -- |- !x y. x = y <=> y = x
#eval CONJ_SYM                                                     -- |- !t1 t2. t1 /\ t2 <=> t2 /\ t1
#eval CONJ_ASSOC                                                   -- |- ...
#eval IMP_IMP                                                      -- |- (GSYM IMP_CONJ)
#eval FORALL_AND_THM                                               -- |- ... (ITAUT)
#eval MONO_FORALL                                                  -- |- (prove script)
#eval UNWIND_THM1                                                  -- |- ... (intricate script)
#eval UNWIND_THM2                                                  -- |- ... (uses UNWIND_THM1)
#eval FORALL_UNWIND_THM2                                           -- |- ... (B.SPEC continuation)
#eval EXISTS_UNIQUE_REFL                                           -- |- ... (THENL script)
#eval WLOG_RELATION                                                -- |- ... (MONO_FORALL + ASM_SIMP)
#eval EXISTS_UNIQUE_ALT                                            -- |- ... (EQ_TAC/CHOOSE script)
#eval EXISTS_UNIQUE                                                -- |- ... (uses EXISTS_UNIQUE_ALT)
#eval REWRITE_CONV [] ([[ T /\ (p:bool) ]])                        -- |- T /\ p <=> p (basic net)

-- theorems.ml Part B: tactic DSL (FIX_TAC/INTRO_TAC/DESTRUCT_TAC/CLAIM_TAC)
-- FIX_TAC "x y": specialise the two leading universals, then reflexivity.
#eval prove ([[ !x y:A. (x:A) = x ]]) (THEN (FIX_TAC "x y") REFL_TAC)
                                                                   -- |- !x y. x = x
-- INTRO_TAC "!x y": same, introduce-pattern form.
#eval prove ([[ !x y:A. (x:A) = x ]]) (THEN (INTRO_TAC "!x y") REFL_TAC)
                                                                   -- |- !x y. x = x
-- INTRO_TAC "p q": DISCH the antecedent and split/label its conjuncts, then
-- ASM_REWRITE closes q /\ p.
#eval prove ([[ (p:bool) /\ q ==> q /\ p ]])
        (THEN (INTRO_TAC "p q") (ASM_REWRITE_TAC []))              -- |- p /\ q ==> q /\ p
-- DESTRUCT_TAC "p q" via DISCH_THEN: destructure the antecedent conjunction,
-- labelling the parts, then ASM_REWRITE.
#eval prove ([[ (p:bool) /\ q ==> q ]])
        (THEN (DISCH_THEN (DESTRUCT_TAC "p q")) (ASM_REWRITE_TAC []))
                                                                   -- |- p /\ q ==> q
-- CLAIM_TAC "c": on `p ==> p`, DISCH p, claim `p` (label c), discharge both
-- subgoals with the assumption.
#eval prove ([[ (p:bool) ==> p ]])
        (THEN (DISCH_TAC)
          (THENL (CLAIM_TAC "c" ([[ p:bool ]])) [ASM_REWRITE_TAC [], ASM_REWRITE_TAC []]))
                                                                   -- |- p ==> p
-- HYP_TAC "h: p q": label the antecedent `p /\ q` as h, then destructure that
-- hypothesis (removing h) into labels p,q via the identity rule; ASM_REWRITE.
#eval prove ([[ (p:bool) /\ q ==> q ]])
        (THEN (DISCH_THEN (LABEL_TAC "h"))
          (THEN (HYP_TAC "h: p q" (fun th => Except.ok th)) (ASM_REWRITE_TAC [])))
                                                                   -- |- p /\ q ==> q

-- HYP_TAC with NO destructuring action is `REMOVE_THEN lbl (LABEL_TAC lbl o rule)`
-- (theorems.ml 528), so a FAILING `rule` must fail the tactic.  The port used to
-- fall back to the unchanged theorem, re-label it, and succeed.
#eval (do
  match ← prove ([[ (p:bool) ==> p ]])
            (THEN (DISCH_THEN (LABEL_TAC "h"))
              (THEN (HYP_TAC "h" (fun _ => Except.error "rule-boom")) (ASM_REWRITE_TAC []))) with
  | .ok th => IO.println s!"HYP_TAC failing rule -> MISMATCH succeeded: {← HolCore.Printer.string_of_thm th}"
  | .error e =>
    if (e.splitOn "rule-boom").length ≥ 2 then
      IO.println "HYP_TAC propagates a failing rule (theorems.ml 528) -> OK (correctly rejected)"
    else IO.println s!"HYP_TAC failing rule -> MISMATCH failed for another reason: {e}")
