/- File: HolTest/ComputeTest.lean
Runtime test suite: compute.ml - call-by-value reduction (HOL4's computeLib)
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Tests: compute.ml - call-by-value reduction (HOL4's computeLib).       -/
/- ---------------------------------------------------------------------- -/


-- ========================================================================
-- compute.ml : call-by-value reduction (HOL4's computeLib).
-- These tests deliberately cover EVERY branch of the reduction machine
-- (`cbv_wk`, `cbv_up`, `strong`, `strong_up`), not one happy path:
--   · cbv_wk App/Clos      — an applied abstraction or constant
--   · cbv_wk beta          — `(\x. ...) arg` with an arg on the stack
--   · cbv_wk Const         — a constant matching a rewrite rule
--   · cbv_up Zrator/Zrand  — rebuilding an application after each operand
--   · cbv_up is_skip       — COND, whose branches must NOT be evaluated
--   · strong Abs           — reduction under a lambda
--   · strong Const/skip    — partition_skip over a skipped constant
--   · strong_up Neutr      — a free variable applied to reduced arguments
--   · reduce_cst Conv      — a conversion action (let_CONV in basic_compset)
-- Gated by TestFlags.runCompute.
-- ========================================================================
#eval (do
  let cs ← Session.the_compset
  let items ← Session.listItems cs
  IO.println s!"the_compset constants -> {items.length}")
-- EVAL_CONV on the boolean operators (cbv_wk Const + reduce_cst Rewrite).

#eval EVAL_CONV ([[ T /\ F ]])
#eval EVAL_CONV ([[ F /\ T ]])
#eval EVAL_CONV ([[ T /\ T ]])
#eval EVAL_CONV ([[ T \/ F ]])
#eval EVAL_CONV ([[ F \/ F ]])
#eval EVAL_CONV ([[ ~T ]])
#eval EVAL_CONV ([[ ~F ]])
#eval EVAL_CONV ([[ T ==> F ]])
#eval EVAL_CONV ([[ F ==> T ]])
#eval EVAL_CONV ([[ (T <=> F) ]])
-- Nested, so cbv_up must rebuild through several Zrand frames.

#eval (do
  match ← Session.EVAL_CONV ([[ (T /\ T) /\ (F \/ T) ]]) with
  | .ok th => IO.println s!"EVAL_CONV nested -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"EVAL_CONV nested ERR: {e}")


-- Beta redexes, reduction under abstractions, and neutral (free) variables.
#eval (do
  match ← Session.EVAL_CONV ([[ (\x. x /\ T) T ]]) with
  | .ok th => IO.println s!"EVAL_CONV beta -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"EVAL_CONV beta ERR: {e}")

#eval (do
  match ← Session.EVAL_CONV ([[ (\x y. x \/ y) F T ]]) with
  | .ok th => IO.println s!"EVAL_CONV beta2 -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"EVAL_CONV beta2 ERR: {e}")
-- strong's Abs case + strong_up's Zabs case: reduce under a lambda.

#eval (do
  match ← Session.EVAL_CONV ([[ \x. T /\ x ]]) with
  | .ok th => IO.println s!"EVAL_CONV under-lambda -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"EVAL_CONV under-lambda ERR: {e}")

#eval (do
  match ← Session.EVAL_CONV ([[ \x y. (x /\ T) \/ (F /\ y) ]]) with
  | .ok th => IO.println s!"EVAL_CONV under-lambda2 -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"EVAL_CONV under-lambda2 ERR: {e}")
-- Neutr: a free variable applied to arguments that ARE reduced
-- (strong's Neutr case, strong_up's Zrand-Neutr and Zrator cases).

#eval (do
  match ← Session.EVAL_CONV ([[ (f:bool->bool) (T /\ T) ]]) with
  | .ok th => IO.println s!"EVAL_CONV neutral -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"EVAL_CONV neutral ERR: {e}")

#eval (do
  match ← Session.EVAL_CONV ([[ (g:bool->bool->bool) (F \/ T) (~F) ]]) with
  | .ok th => IO.println s!"EVAL_CONV neutral2 -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"EVAL_CONV neutral2 ERR: {e}")
-- A neutral head under a lambda: both machines' recursive paths at once.

#eval (do
  match ← Session.EVAL_CONV ([[ \x. (h:bool->bool) (x /\ T) ]]) with
  | .ok th => IO.println s!"EVAL_CONV neutral-lambda -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"EVAL_CONV neutral-lambda ERR: {e}")


-- Conditionals (the `set_skip` path), `let`, and WEAK_CBV_CONV.
#eval (do
  match ← Session.EVAL_CONV ([[ if T then (a:A) else b ]]) with
  | .ok th => IO.println s!"EVAL_CONV cond-T -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"EVAL_CONV cond-T ERR: {e}")

#eval (do
  match ← Session.EVAL_CONV ([[ if F then (a:A) else b ]]) with
  | .ok th => IO.println s!"EVAL_CONV cond-F -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"EVAL_CONV cond-F ERR: {e}")

#eval (do
  match ← Session.EVAL_CONV ([[ if (T /\ F) then (a:A) else b ]]) with
  | .ok th => IO.println s!"EVAL_CONV cond-guard -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"EVAL_CONV cond-guard ERR: {e}")
-- COND_ID: both branches the same.

#eval (do
  match ← Session.EVAL_CONV ([[ if (p:bool) then (a:A) else a ]]) with
  | .ok th => IO.println s!"EVAL_CONV cond-id -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"EVAL_CONV cond-id ERR: {e}")
-- `let` via the strictified LET_DEF in bool_compset.

#eval (do
  match ← Session.EVAL_CONV ([[ let x = T in x /\ F ]]) with
  | .ok th => IO.println s!"EVAL_CONV let -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"EVAL_CONV let ERR: {e}")
-- WEAK_CBV_CONV: no reduction under abstractions (exercises stack_out).

#eval (do
  let cs ← Session.the_compset
  match ← Session.WEAK_CBV_CONV cs ([[ (\x. x /\ T) T ]]) with
  | .ok th => IO.println s!"WEAK_CBV_CONV -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"WEAK_CBV_CONV ERR: {e}")

#eval (do
  let cs ← Session.the_compset
  match ← Session.WEAK_CBV_CONV cs ([[ \x. T /\ x ]]) with
  | .ok th => IO.println s!"WEAK_CBV_CONV lambda -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"WEAK_CBV_CONV lambda ERR: {e}")


-- lazyfy_thm / strictify_thm, user rewrites, stoppers, and compset surgery.
#eval (do
  match ← Session.lazyfy_thm Session.AND_CLAUSES with
  | .ok th => IO.println s!"lazyfy_thm AND_CLAUSES -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"lazyfy_thm ERR: {e}")

#eval (do
  match Session.strictify_thm Session.LET_DEF with
  | .ok th => IO.println s!"strictify_thm LET_DEF -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"strictify_thm ERR: {e}")
-- A user rule added to a fresh compset, then used by CBV_CONV.  This is the
-- normal way `add_funs` is used: define a constant, feed in its equation.

#eval (do
  match ← Session.new_definition ([[ NANDC x y <=> ~(x /\ y) ]]) with
  | .error e => IO.println s!"user rule setup ERR: {e}"
  | .ok kth => do
    IO.println s!"NANDC def -> {← HolCore.Printer.string_of_thm kth}"
    match ← Session.new_compset [kth] with
    | .error e => IO.println s!"new_compset ERR: {e}"
    | .ok cs => do
      -- The rule fires, but ~ and /\ are NOT in this compset, so the rhs
      -- stays as-is: exactly the expected behaviour of a bare compset.
      (do match ← Session.CBV_CONV cs ([[ NANDC T F ]]) with
          | .ok th => IO.println s!"CBV_CONV user-rule -> {← HolCore.Printer.string_of_thm th}"
          | .error e => IO.println s!"CBV_CONV user-rule ERR: {e}")
      -- Add the boolean rules too, so the rhs reduces all the way.
      (do match ← Session.add_thms [Session.NOT_CLAUSES, Session.AND_CLAUSES] cs with
          | .error e => IO.println s!"add_thms ERR: {e}"
          | .ok _ =>
            match ← Session.CBV_CONV cs ([[ NANDC T F ]]) with
            | .ok th => IO.println s!"CBV_CONV user-rule+bool -> {← HolCore.Printer.string_of_thm th}"
            | .error e => IO.println s!"CBV_CONV user-rule+bool ERR: {e}")
      -- add_funs: the same rule in the GLOBAL compset, used by EVAL_CONV.
      (do match ← Session.add_funs [kth] with
          | .error e => IO.println s!"add_funs ERR: {e}"
          | .ok _ =>
            match ← Session.EVAL_CONV ([[ NANDC T (F \/ T) ]]) with
            | .ok th => IO.println s!"EVAL_CONV after add_funs -> {← HolCore.Printer.string_of_thm th}"
            | .error e => IO.println s!"EVAL_CONV after add_funs ERR: {e}")
      -- del_funs: remove it again; the constant must stop reducing.
      (do match ← Session.del_funs [kth] with
          | .error e => IO.println s!"del_funs ERR: {e}"
          | .ok _ =>
            match ← Session.EVAL_CONV ([[ NANDC T F ]]) with
            | .ok th => IO.println s!"EVAL_CONV after del_funs -> {← HolCore.Printer.string_of_thm th}"
            | .error e => IO.println s!"EVAL_CONV after del_funs ERR: {e}")
      -- scrub_thms on the local compset: the rule must no longer fire.
      (do match ← Session.scrub_thms [kth] cs with
          | .error e => IO.println s!"scrub_thms ERR: {e}"
          | .ok _ =>
            match ← Session.CBV_CONV cs ([[ NANDC T F ]]) with
            | .ok th => IO.println s!"CBV_CONV after scrub -> {← HolCore.Printer.string_of_thm th}"
            | .error e => IO.println s!"CBV_CONV after scrub ERR: {e}"))
-- RESTR_EVAL_CONV: stop at `\/`, so the disjunction survives unreduced
-- while the conjunction around it is still evaluated.

#eval (do
  match ← Session.RESTR_EVAL_CONV [([[ (\/) ]])] ([[ (T /\ T) /\ (F \/ T) ]]) with
  | .ok th => IO.println s!"RESTR_EVAL_CONV stop-or -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"RESTR_EVAL_CONV stop-or ERR: {e}")
-- The flag must be restored: a plain EVAL_CONV afterwards reduces fully.

#eval (do
  match ← Session.EVAL_CONV ([[ (T /\ T) /\ (F \/ T) ]]) with
  | .ok th => IO.println s!"EVAL_CONV after RESTR -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"EVAL_CONV after RESTR ERR: {e}")
-- EVAL_RULE / EVAL_TAC / the RESTR_EVAL wrappers.

#eval (do
  match ← Session.EVAL_RULE (REFL ([[ (T /\ T) \/ F ]])) with
  | .ok th => IO.println s!"EVAL_RULE -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"EVAL_RULE ERR: {e}")

#eval (do
  match ← Session.prove ([[ (T /\ T) \/ F ]]) Session.EVAL_TAC with
  | .ok th => IO.println s!"EVAL_TAC -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"EVAL_TAC ERR: {e}")

#eval (do
  match ← Session.RESTR_EVAL_RULE [([[ (\/) ]])] (REFL ([[ T /\ (F \/ T) ]])) with
  | .ok th => IO.println s!"RESTR_EVAL_RULE -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"RESTR_EVAL_RULE ERR: {e}")

#eval (do
  match ← Session.prove ([[ (T /\ T) \/ F ]]) (Session.RESTR_EVAL_TAC [([[ (~) ]])]) with
  | .ok th => IO.println s!"RESTR_EVAL_TAC -> {← HolCore.Printer.string_of_thm th}"
  | .error e => IO.println s!"RESTR_EVAL_TAC ERR: {e}")
-- del_consts on the global compset, then restore it (so this test leaves
-- `the_compset` as it found it and later tests are unaffected).

#eval (do
  match ← Session.del_consts [([[ (==>) ]])] with
  | .error e => IO.println s!"del_consts ERR: {e}"
  | .ok _ => do
    (do match ← Session.EVAL_CONV ([[ T ==> F ]]) with
        | .ok th => IO.println s!"EVAL_CONV after del_consts -> {← HolCore.Printer.string_of_thm th}"
        | .error e => IO.println s!"EVAL_CONV after del_consts ERR: {e}")
    match ← Session.lazyfy_thm Session.IMP_CLAUSES with
    | .error e => IO.println s!"restore lazyfy ERR: {e}"
    | .ok l =>
      match ← Session.add_funs [l] with
      | .error e => IO.println s!"restore add_funs ERR: {e}"
      | .ok _ =>
        match ← Session.EVAL_CONV ([[ T ==> F ]]) with
        | .ok th => IO.println s!"EVAL_CONV restored -> {← HolCore.Printer.string_of_thm th}"
        | .error e => IO.println s!"EVAL_CONV restored ERR: {e}")


-- basic_compset: the lambda-lhs filter, the registered conversions, let_CONV.
#eval (do
  let rws ← HolCore.Simp.basic_rewrites
  match (do
    let a ← Session.SPEC_ALL Session.SELECT_REFL
    let b ← Session.SPEC_ALL Session.FORALL_SIMP
    let c ← Session.SPEC_ALL Session.EXISTS_SIMP
    pure [a, b, c] : Except String (List thm)) with
  | .error e => IO.println s!"filter check ERR: {e}"
  | .ok bad =>
    let kept := rws.filter (fun th => !(HolCore.Lib.mem th bad))
    IO.println s!"basic_rewrites {rws.length}, kept {kept.length}, removed {rws.length - kept.length}")
-- basic_compset attaches let_CONV to LET as a Conv action, which exercises
-- reduce_cst's Conv branch (a different code path from a Rewrite action).
--
-- NOTE: the constant COUNT below is STATE-DEPENDENT, not a fixed expectation.
-- `basic_compset` is built from `basic_rewrites()`/`basic_convs()`, which every
-- layer extends as it is forced, so the number grows with how much of the
-- session has been initialised: 9 here, but 13 in the old monolithic Test.lean
-- because its pair.ml section had already run by that point (verified by
-- forcing `PAIR_EQ` first, which raises the count to 13).  Forcing the pair
-- layer explicitly makes this test order-independent.
#eval (do
  IO.println s!"(force pair: {← HolCore.Printer.string_of_thm Session.PAIR_EQ})"
  match ← Session.basic_compset with
  | .error e => IO.println s!"basic_compset ERR: {e}"
  | .ok cs => do
    (do let items ← Session.listItems cs
        IO.println s!"basic_compset constants -> {items.length}")
    (do match ← Session.CBV_CONV cs ([[ let x = T in x /\ F ]]) with
        | .ok th => IO.println s!"basic CBV let -> {← HolCore.Printer.string_of_thm th}"
        | .error e => IO.println s!"basic CBV let ERR: {e}")
    (do match ← Session.CBV_CONV cs ([[ let (x,y) = (T,F) in x \/ y ]]) with
        | .ok th => IO.println s!"basic CBV paired-let -> {← HolCore.Printer.string_of_thm th}"
        | .error e => IO.println s!"basic CBV paired-let ERR: {e}")
    (do match ← Session.CBV_CONV cs ([[ (\x. x /\ T) (F \/ T) ]]) with
        | .ok th => IO.println s!"basic CBV beta -> {← HolCore.Printer.string_of_thm th}"
        | .error e => IO.println s!"basic CBV beta ERR: {e}")
    -- set_skip with Some 1, then scrub_const, on this local compset.
    (do match ← Session.set_skip cs ([[ COND: bool -> A -> A -> A ]]) (some 1) with
        | .ok _ => IO.println "set_skip COND (Some 1) -> ok"
        | .error e => IO.println s!"set_skip ERR: {e}")
    (do match ← Session.scrub_const cs ([[ (/\) ]]) with
        | .ok _ => IO.println "scrub_const /\\ -> ok"
        | .error e => IO.println s!"scrub_const ERR: {e}")
    (do match ← Session.CBV_CONV cs ([[ T /\ F ]]) with
        | .ok th => IO.println s!"basic CBV after scrub-and -> {← HolCore.Printer.string_of_thm th}"
        | .error e => IO.println s!"basic CBV after scrub-and ERR: {e}"))

