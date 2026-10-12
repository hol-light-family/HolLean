/- File: HolTest/ImpConvTest.lean
Runtime test suite: impconv.ml - implicational rewriting
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Tests: impconv.ml - implicational rewriting.                           -/
/- ---------------------------------------------------------------------- -/


-- ========================================================================
-- impconv.ml : implicational rewriting (IMP_REWRITE_TAC, HINT_EXISTS_TAC, …)
-- Gated by TestFlags.runImpConv.  Forcing the tactics also forces the ~37
-- ImpConvDeps + ImpConvVars to be proved/parsed (a panic would surface here).
-- ========================================================================
open Session (IMP_REWRITE_TAC SEQ_IMP_REWRITE_TAC HINT_EXISTS_TAC CASE_REWRITE_TAC TARGET_REWRITE_TAC) in
#eval (do
  -- Helper: run a tactic on the closed goal `([], tm)` and print resulting subgoals.
  let runShow (label : String) (tm : term) (tac : HolCore.Tactics.tactic) : IO Unit := do
    match ← tac ([], tm) with
    | .error e => IO.println s!"{label} ERR: {e}"
    | .ok gstate =>
      let subs : List HolCore.Tactics.goal := gstate.2.1
      if subs.isEmpty then IO.println s!"{label} -> (no subgoals)"
      else
        let parts ← subs.mapM (fun (gl : HolCore.Tactics.goal) => do
          let asms := gl.1
          let gtm := gl.2
          let gstr ← HolCore.Printer.string_of_term gtm
          let ah ← asms.mapM (fun (a : String × thm) => HolCore.Printer.string_of_term (concl a.2))
          pure (if ah.isEmpty then gstr else s!"[{String.intercalate ", " ah}] |- {gstr}"))
        IO.println s!"{label} -> {String.intercalate "  ||  " parts}"
  -- IMP_REWRITE_TAC
  -- (1) empty list closes a reflexive implication.
  (do match ← prove ([[ (p:bool) ==> p ]]) (IMP_REWRITE_TAC []) with
      | .ok th => IO.println s!"IMP_REWRITE_TAC[] -> {← HolCore.Printer.string_of_thm th}"
      | .error e => IO.println s!"IMP_REWRITE_TAC[] ERR: {e}")
  -- (2) unconditional equational rewrite EQ_SYM_EQ closes `a=b ==> b=a`.
  (do match ← prove ([[ ((a:A) = b) ==> ((b:A) = a) ]]) (IMP_REWRITE_TAC [Session.EQ_SYM_EQ]) with
      | .ok th => IO.println s!"IMP_REWRITE_TAC eq -> {← HolCore.Printer.string_of_thm th}"
      | .error e => IO.println s!"IMP_REWRITE_TAC eq ERR: {e}")
  -- (3) SUBTERM equational rewrite with a real non-symmetric equation.
  --     AND_CLAUSES has clause `t /\ T <=> t`; rewriting `f c /\ T`->`f c` in
  --     `(f c /\ T) <=> f c` yields `f c <=> f c` = T, closing the goal.
  --     Also exercises theorem-conjunction preprocessing (AND_CLAUSES is a big /\).
  (do match ← prove ([[ ((f:A->bool) c /\ T) <=> f c ]]) (IMP_REWRITE_TAC [Session.AND_CLAUSES]) with
      | .ok th => IO.println s!"IMP_REWRITE_TAC subterm-eq -> {← HolCore.Printer.string_of_thm th}"
      | .error e => IO.println s!"IMP_REWRITE_TAC subterm-eq ERR: {e}")
  -- (3b) same rewrite applied DEEP inside an implication: `p ==> (f c /\ T)` -> `p ==> f c`.
  (do runShow "IMP_REWRITE_TAC deep-subterm" ([[ p ==> ((f:A->bool) c /\ T) ]])
        (IMP_REWRITE_TAC [Session.AND_CLAUSES]))
  -- (4) conditional biconditional rewrite closes `c=a ==> (f c <=> f a)`.
  (do match ← MESON [] ([[ !x:A. (x = a) ==> ((f:A->bool) x <=> f a) ]]) with
      | .error e => IO.println s!"IMP_REWRITE cond lemma ERR: {e}"
      | .ok cond => do
        (do match ← prove ([[ ((c:A) = a) ==> ((f:A->bool) c <=> f a) ]]) (IMP_REWRITE_TAC [cond]) with
            | .ok th => IO.println s!"IMP_REWRITE_TAC cond -> {← HolCore.Printer.string_of_thm th}"
            | .error e => IO.println s!"IMP_REWRITE_TAC cond ERR: {e}")
        (do match ← prove ([[ ((c:A) = a) ==> ((f:A->bool) c <=> f a) ]]) (SEQ_IMP_REWRITE_TAC [cond]) with
            | .ok th => IO.println s!"SEQ_IMP_REWRITE_TAC -> {← HolCore.Printer.string_of_thm th}"
            | .error e => IO.println s!"SEQ_IMP_REWRITE_TAC ERR: {e}")
        -- ASM variant.
        (do match ← prove ([[ ((c:A) = a) ==> ((f:A->bool) c <=> f a) ]])
                      (Session.ASM_IMP_REWRITE_TAC [cond]) with
            | .ok th => IO.println s!"ASM_IMP_REWRITE_TAC -> {← HolCore.Printer.string_of_thm th}"
            | .error e => IO.println s!"ASM_IMP_REWRITE_TAC ERR: {e}"))
  -- (5) Conditional rewrite that ADDS then discharges a precondition end-to-end:
  --     goal `c = a ==> (f c <=> f a)` closed by cond `!x. (x=a) ==> (f x <=> f a)` (see #4).
  --     Here we confirm IMP_REWRITE leaves a residual precondition when it cannot discharge it:
  --     goal `f c <=> f a` (no `c=a` available) -> `c = a ==> T`-style residual `c = a`.
  (do match ← MESON [] ([[ !x:A. (x = a) ==> ((f:A->bool) x <=> f a) ]]) with
      | .error e => IO.println s!"IMP_REWRITE residual lemma ERR: {e}"
      | .ok th => runShow "IMP_REWRITE_TAC residual-precond" ([[ (f:A->bool) c <=> f a ]]) (IMP_REWRITE_TAC [th]))
  -- (6) THEOREM-CONJUNCTION input: a single theorem that is a conjunction of two
  --     rewrites should be preprocessed into two (exercises `preprocess`/IMPLY_AND/CONJUNCTS).
  (do match ← MESON [] ([[ (!x:A. (x=a) ==> ((f:A->bool) x <=> f a)) /\ (!y:A. (y=b) ==> ((h:A->bool) y <=> h b)) ]]) with
      | .error e => IO.println s!"IMP_REWRITE conj-thm lemma ERR: {e}"
      | .ok th =>
        match ← prove ([[ ((c:A)=a) ==> ((f:A->bool) c <=> f a) ]]) (IMP_REWRITE_TAC [th]) with
        | .ok r => IO.println s!"IMP_REWRITE_TAC conj-thm -> {← HolCore.Printer.string_of_thm r}"
        | .error e => IO.println s!"IMP_REWRITE_TAC conj-thm ERR: {e}")
  -- (7) FAILURE behavior: IMP_REWRITE with a non-applicable rewrite fails (Unchanged).
  --     AND_CLAUSES has no applicable subterm in `p ==> q`.
  (do match ← prove ([[ (p:bool) ==> q ]]) (IMP_REWRITE_TAC [Session.AND_CLAUSES]) with
      | .ok th => IO.println s!"IMP_REWRITE_TAC no-op UNEXPECTEDLY closed -> {← HolCore.Printer.string_of_thm th}"
      | .error e => IO.println s!"IMP_REWRITE_TAC no-op fails as expected: {e}")
  -- CASE_REWRITE_TAC
  -- Documented shape: atom A with subterm matching l -> (P' ==> A') /\ (~P' ==> A).
  -- cond `!x.(x=a)==>(f x<=>f a)` registers atom `f x<=>f a`; goal `(f c<=>f a)/\q`
  -- contains that atom, so CASE_REWRITE splits it on `c=a`.
  (do match ← MESON [] ([[ !x:A. (x = a) ==> ((f:A->bool) x <=> f a) ]]) with
      | .error e => IO.println s!"CASE_REWRITE lemma ERR: {e}"
      | .ok cond => runShow "CASE_REWRITE_TAC" ([[ ((f:A->bool) c <=> f a) /\ q ]]) (CASE_REWRITE_TAC cond))
  -- HINT_EXISTS_TAC
  -- (a) single-conjunct existential.
  (do match ← prove ([[ (P:A->bool) a ==> (?x:A. P x) ]]) (THEN DISCH_TAC HINT_EXISTS_TAC) with
      | .ok th => IO.println s!"HINT_EXISTS_TAC 1 -> {← HolCore.Printer.string_of_thm th}"
      | .error e => IO.println s!"HINT_EXISTS_TAC 1 ERR: {e}")
  -- (b) DOCUMENTED example (pure-logic analog): P a /\ Q b /\ R c ==> ?x y. P x /\ R y /\ S x y
  --     Applied DIRECTLY (no DISCH): TOP_DEPTH descends the `==>` via IMP_CTXIMPCONV, which
  --     strip_conj's the antecedent into context [P a, Q b, R c]; then x:=a, y:=c leaving `S a c`.
  (do let goal := [[ (P:A->bool) a /\ (Q:A->bool) b /\ (R:A->bool) c
                     ==> (?x y:A. P x /\ R y /\ (S:A->A->bool) x y) ]]
      runShow "HINT_EXISTS_TAC documented" goal HINT_EXISTS_TAC)
  -- (c) partial hint: body `P x /\ Q x`, only P a in context -> instantiate x:=a.
  (do let goal := [[ (P:A->bool) a ==> (?x:A. P x /\ (Q:A->bool) x) ]]
      runShow "HINT_EXISTS_TAC 2conj" goal HINT_EXISTS_TAC)
  -- (d) FAILURE: no hint available -> fails.
  (do match ← prove ([[ (P:A->bool) a ==> (?x:A. (Q:A->bool) x) ]]) (THEN DISCH_TAC HINT_EXISTS_TAC) with
      | .ok th => IO.println s!"HINT_EXISTS_TAC no-hint UNEXPECTEDLY -> {← HolCore.Printer.string_of_thm th}"
      | .error e => IO.println s!"HINT_EXISTS_TAC no-hint fails as expected: {e}")
  -- TARGET_REWRITE_TAC
  -- Rewrite toward a target: support EQ_SYM_EQ, target `b=a`; goal `a=b` -> reach `b=a`.
  (do runShow "TARGET_REWRITE_TAC" ([[ (a:A) = b ]])
        (TARGET_REWRITE_TAC [Session.EQ_SYM_EQ] (ASSUME ([[ (b:A) = a ]]))))
  -- REWRITE UNDER A BINDER (exercises acSubQConv Abs / ABS_CONV path)
  -- AND_CLAUSES rewrites `f x /\ T`->`f x` under the `!x` binder: `!x. f x /\ T` -> `!x. f x`.
  (do runShow "IMP_REWRITE_TAC under-binder" ([[ !x:A. (f:A->bool) x /\ T ]])
        (IMP_REWRITE_TAC [Session.AND_CLAUSES]))
  -- Rewrite under an existential binder too: `?x. f x /\ T` -> `?x. f x`.
  (do runShow "IMP_REWRITE_TAC under-exists" ([[ ?x:A. (f:A->bool) x /\ T ]])
        (IMP_REWRITE_TAC [Session.AND_CLAUSES]))
  -- ROUND-4 ADDITIONAL TESTS
  -- (8) CONTRAVARIANT position: rewrite in the ANTECEDENT of an implication.
  --     `(f c /\ T) ==> q`: AND_CLAUSES rewrites `f c /\ T`->`f c` in the antecedent
  --     (Contra variance), giving `f c ==> q`. Exercises MKIMPL/Contra builders.
  (do runShow "IMP_REWRITE_TAC contravariant" ([[ ((f:A->bool) c /\ T) ==> q ]])
        (IMP_REWRITE_TAC [Session.AND_CLAUSES]))
  -- (9) rewrite inside a DISJUNCTION: `(f c /\ T) \/ q` -> `f c \/ q`.
  (do runShow "IMP_REWRITE_TAC disj" ([[ ((f:A->bool) c /\ T) \/ q ]])
        (IMP_REWRITE_TAC [Session.AND_CLAUSES]))
  -- (10) rewrite inside a NEGATION: `~(f c /\ T)` -> `~(f c)`.
  (do runShow "IMP_REWRITE_TAC neg" ([[ ~((f:A->bool) c /\ T) ]])
        (IMP_REWRITE_TAC [Session.AND_CLAUSES]))
  -- (11) MULTIPLE simultaneous rewrites: AND_CLAUSES + OR_CLAUSES together on
  --      `(f c /\ T) \/ F` -> `f c` (both clause-sets apply).
  (do runShow "IMP_REWRITE_TAC multi" ([[ ((f:A->bool) c /\ T) \/ F ]])
        (IMP_REWRITE_TAC [Session.AND_CLAUSES, Session.OR_CLAUSES]))
  -- (12) NESTED binders: rewrite deep under two quantifiers.
  --      `!x. ?y. (f x /\ T)` -> `!x. ?y. f x`.
  (do runShow "IMP_REWRITE_TAC nested-binders" ([[ !x:A. ?y:A. ((f:A->bool) x /\ T) ]])
        (IMP_REWRITE_TAC [Session.AND_CLAUSES]))
  -- (13) IDEMPOTENT re-run: applying the same closed rewrite twice still closes.
  (do match ← prove ([[ ((f:A->bool) c /\ T) <=> f c ]])
                (THEN (IMP_REWRITE_TAC [Session.AND_CLAUSES])
                      (IMP_REWRITE_TAC [Session.AND_CLAUSES])) with
      | .ok th => IO.println s!"IMP_REWRITE_TAC then-again -> {← HolCore.Printer.string_of_thm th}"
      | .error e => IO.println s!"IMP_REWRITE_TAC then-again (2nd may be Unchanged): {e}")
  -- (14) SEQ_IMP_REWRITE_TAC with multiple theorems applied to full closure.
  (do match ← prove ([[ (((f:A->bool) c /\ T) /\ T) <=> f c ]])
                (SEQ_IMP_REWRITE_TAC [Session.AND_CLAUSES]) with
      | .ok th => IO.println s!"SEQ_IMP_REWRITE_TAC iterate -> {← HolCore.Printer.string_of_thm th}"
      | .error e => IO.println s!"SEQ_IMP_REWRITE_TAC iterate ERR: {e}")
  -- (15) CASE_REWRITE deep inside an implication conclusion.
  (do match ← MESON [] ([[ !x:A. (x = a) ==> ((f:A->bool) x <=> f a) ]]) with
      | .error e => IO.println s!"CASE_REWRITE deep lemma ERR: {e}"
      | .ok cond => runShow "CASE_REWRITE_TAC deep" ([[ p ==> ((f:A->bool) c <=> f a) ]]) (CASE_REWRITE_TAC cond))
  -- (16) HINT_EXISTS three-variable / reordered conjuncts:
  --      `Q b /\ P a /\ R c ==> ?x y. R y /\ P x` -> witnesses x:=a, y:=c.
  (do runShow "HINT_EXISTS_TAC reordered"
        ([[ (Q:A->bool) b /\ (P:A->bool) a /\ (R:A->bool) c ==> (?x y:A. R y /\ P x) ]])
        HINT_EXISTS_TAC)
  -- (17) SANITY: a fully-closing IMP_REWRITE chain (like the .hlp REAL example structure):
  --      rewrite `f c /\ T` to `f c` in `((f c /\ T) <=> f c)` then it's reflexive -> closed.
  (do match ← prove ([[ ((f:A->bool) c /\ T) /\ ((g:A->bool) d \/ F) <=> f c /\ g d ]])
                (IMP_REWRITE_TAC [Session.AND_CLAUSES, Session.OR_CLAUSES]) with
      | .ok th => IO.println s!"IMP_REWRITE_TAC full-close -> {← HolCore.Printer.string_of_thm th}"
      | .error e => IO.println s!"IMP_REWRITE_TAC full-close ERR: {e}"))




/- ---------------------------------------------------------------------- -/
/- `Unchanged` propagation (impconv.ml 64, 841-847, 1049, 1094-1098, 1374). -/
/- ---------------------------------------------------------------------- -/
/- `!x y. g x y = g y y` rewrites `g a a` to ITSELF, so REWR_IMPCONV_OF_CONV
   raises `Unchanged` (1374).  The connective and depth combinators catch only
   `Failure _`, so it escapes all of them and `fail_if_unchanged` makes
   IMP_REWRITE_TAC fail - even when another conjunct could be rewritten.  (A
   symmetric equation such as ADD_SYM never reaches that point: pat_cnv_of_thm
   turns it into an EQT_INTRO rewrite, 1228.) -/
#eval (do
  let gxy := ASSUME ([[ !x y. (g:A->A->bool) x y = g y y ]])
  let run (lbl : String) (w : term) (want : Option String) : IO Unit := do
    match ← (IMP_REWRITE_TAC [gxy, AND_CLAUSES] ([], w) : IO (Except String HolCore.Tactics.goalstate)),
          want with
    | .error e, none =>
      IO.println (if e == "Unchanged" then s!"{lbl} -> OK (correctly rejected)"
                  else s!"{lbl} -> MISMATCH message {e}")
    | .ok (_, [gl], _), some s =>
      let got ← HolCore.Printer.string_of_term gl.2
      IO.println (if got == s then s!"{lbl} -> OK" else s!"{lbl} -> MISMATCH got {got}")
    | .ok (_, gls, _), _ => IO.println s!"{lbl} -> MISMATCH succeeded with {gls.length} goals"
    | .error e, some _ => IO.println s!"{lbl} -> MISMATCH failed: {e}"
  run "Unchanged: g a a fails" ([[ (g:A->A->bool) a a ]]) none
  run "Unchanged: g a a /\\ (f c /\\ T) fails, not just the f c rewrite" ([[ (g:A->A->bool) a a /\ ((f:A->bool) c /\ T) ]]) none
  run "Unchanged: (f c /\\ T) /\\ g a a fails" ([[ ((f:A->bool) c /\ T) /\ (g:A->A->bool) a a ]]) none
  run "Unchanged: g a a ==> (f c /\\ T) fails" ([[ (g:A->A->bool) a a ==> ((f:A->bool) c /\ T) ]]) none
  run "Unchanged: g a b is a real rewrite" ([[ (g:A->A->bool) a b ]]) (some "g b b")
  : IO Unit)
