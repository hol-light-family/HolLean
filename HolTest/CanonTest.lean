/- File: HolTest/CanonTest.lean
Runtime test suite: canon.ml - the normalisation conversions and tactics
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Tests: canon.ml - the normalisation conversions and tactics.           -/
/- ---------------------------------------------------------------------- -/

#eval ETA_ONE         -- |- !f. (\x. f one) = f
-- canon.ml conversions (Stages 1-4)
#eval NNF_CONV ([[ ~((p:bool) /\ q) ]])                 -- |- ~(p /\ q) <=> ~p \/ ~q
#eval NNF_CONV ([[ ~(!x:A. (P:A->bool) x) ]])           -- |- ~(!x. P x) <=> (?x. ~P x)
#eval NNFC_CONV ([[ (p:bool) <=> q ]])                  -- |- (p<=>q) <=> (p\/~q)/\(~p\/q)
#eval PRESIMP_CONV ([[ T /\ (p:bool) \/ F ]])           -- |- ... <=> p
#eval PRENEX_CONV ([[ (!x:A. (P:A->bool) x) /\ (!x. (Q:A->bool) x) ]])  -- |- ... <=> !x. P x /\ Q x
#eval CONJ_CANON_CONV ([[ ((p:bool) /\ q) /\ p ]])      -- |- (p/\q)/\p <=> p/\q
-- canon.ml conversions (Stages 5-7)
#eval DISJ_CANON_CONV ([[ ((p:bool) \/ q) \/ p ]])      -- |- (p\/q)\/p <=> p\/q
#eval DNF_CONV ([[ (p:bool) /\ (q \/ r) ]])             -- |- p/\(q\/r) <=> p/\q \/ p/\r
#eval CNF_CONV ([[ (p:bool) \/ (q /\ r) ]])             -- |- p\/(q/\r) <=> (p\/q)/\(p\/r)
#eval WEAK_DNF_CONV ([[ (p:bool) /\ (q \/ r) ]])        -- |- p/\(q\/r) <=> p/\q \/ p/\r
#eval LAMBDA_ELIM_CONV ([[ (\x:A. (P:A->bool) x) = P ]])  -- eliminate the lambda
#eval CONDS_ELIM_CONV ([[ (if (b:bool) then (x:bool) else y) ]])   -- eliminate the conditional
#eval PROP_ATOM_CONV (fun t => NNF_CONV t) ([[ (!x:A. (P:A->bool) x) /\ ~(q:bool) ]])
#eval PROP_ATOM_CONV (fun t => NNF_CONV t) ([[ ~((p:bool) /\ q) /\ (r:bool) ]])  -- NNF pushed into atoms
-- canon.ml: previously-untested paths
#eval SKOLEM_CONV ([[ !x:A. ?y:B. (R:A->B->bool) x y ]])       -- skolemize ?y under !x
#eval WEAK_CNF_CONV ([[ (p:bool) \/ (q /\ r) ]])               -- |- p\/(q/\r) <=> (p\/q)/\(p\/r)
#eval CONDS_CELIM_CONV ([[ (if (b:bool) then (x:bool) else y) ]])  -- conjunctive split
#eval NNFC_CONV ([[ ~(!x:A. (P:A->bool) x) ]])                 -- NNFC on a quantifier
#eval NNF_CONV ([[ ?!x:A. (P:A->bool) x ]])                    -- exercise the ?! branch
#eval NNF_CONV ([[ ~(?!x:A. (P:A->bool) x) ]])                 -- exercise the ?! negative branch
#eval LAMBDA_ELIM_CONV ([[ (P:(A->B)->bool) (\x:A. (f:A->B) x) ]])  -- real lambda elimination
#eval LAMBDA_ELIM_CONV ([[ (P:(A->bool)->bool) (\x:A. (Q:A->bool) x /\ (r:bool)) ]])  -- lambda w/ body
-- ASSOC_CONV needs an associativity theorem; use \/-assoc (DISJ_ASSOC).
#eval (match ASSOC_CONV DISJ_ASSOC with
       | .error e => pure (.error e : Except String thm)
       | .ok c => c ([[ ((p:bool) \/ q) \/ r ]]))
-- canon.ml tactics
-- SELECT_ELIM_TAC: goal mentioning a select-term, then prove by existence.
#eval prove ([[ (?y:A. y = a) ==> (?) (\y:A. y = a) ]])
        (THEN DISCH_TAC (THEN SELECT_ELIM_TAC (FIRST_ASSUM ACCEPT_TAC)))
-- ASM_FOL_TAC: runs the assumption FOL-normalisation, then closes by assumption.
#eval prove ([[ (P:A->bool) a ==> P a ]])
        (THEN DISCH_TAC (THEN ASM_FOL_TAC (FIRST_ASSUM ACCEPT_TAC)))


-- == Foundational rewriting/matching branch-coverage (Simp/Drule) ==
-- mk_rewrites must SPLIT a conjunctive theorem into its component rewrites.
#eval (do match ← mk_rewrites true AND_CLAUSES [] with
          | .error e => IO.println s!"ERR: {e}"
          | .ok ths => IO.println s!"mk_rewrites AND_CLAUSES -> {ths.length} rules")  -- expect several
#eval (do match ← mk_rewrites true CONJ_ACI [] with
          | .error e => IO.println s!"ERR: {e}"
          | .ok ths => IO.println s!"mk_rewrites CONJ_ACI -> {ths.length} rules")     -- 5 permutative
-- ORDERED_REWR_CONV (permutative): REWRITE_CONV[CONJ_SYM] must terminate + orient.
#eval REWRITE_CONV [CONJ_SYM] ([[ (q:bool) /\ p ]])          -- ordered: canonical orientation
-- ONCE_REWRITE_CONV with a permutative rule applies exactly once (no loop).
#eval ONCE_REWRITE_CONV [CONJ_SYM] ([[ (q:bool) /\ p ]])
-- REWRITE_CONV with CONJ_ACI (5 permutative rules) on a nested conjunction.
#eval REWRITE_CONV [CONJ_ACI] ([[ ((p:bool) /\ q) /\ r ]])
-- HIGHER_REWRITE_CONV (via COND_ELIM_CONV): the real designed input shape
-- P(if c then x else y).  (SWAP_FORALL_THM is NOT a valid HIGHER_REWRITE input.)
#eval COND_ELIM_CONV ([[ (P:A->bool) (if (c:bool) then x else y) ]])
-- Higher-order MATCH_MP: MONO_AND is (a==>b)/\(c==>d) ==> (a/\c ==> b/\d).
#eval (do match (ASSUME ([[ ((p1:bool) ==> q1) /\ (p2 ==> q2) ]])) with
          | .error e => IO.println s!"ASSUME ERR: {e}"
          | .ok h =>
            match ← MATCH_MP MONO_AND h with
            | .error e => IO.println s!"MATCH_MP ERR: {e}"
            | .ok th => IO.println s!"MATCH_MP MONO_AND -> {← HolCore.Printer.string_of_thm th}")
