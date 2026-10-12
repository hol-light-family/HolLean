/- File: HolTest/UnitBasicTest.lean
Runtime test suite: HOL Light's own UnitTests/basic_tests.ml, translated
assertion by assertion, in file order.  Each OCaml `assert` becomes one
`-> OK` / `-> MISMATCH` line; a toplevel command that must merely succeed
(`define`, `prove`, `top_thm`, ...) becomes an assertion that it succeeds.
Every assertion passes in real HOL Light (run against /tmp/hol4).

Not translated: the "pa_j preprocessor" block (basic_tests.ml 199-208), which
tests OCaml's camlp5 lexer (`unset_jrh_lexer`, an OCaml `function` over
`Unix.sockaddr`), not HOL Light.
Part of the Lean4 translation of HOL Light by Chris Walton 2026. -/

import HolTest.CommonTest

open HolCore.Kernel HolTest.CommonTest

namespace HolTest.UnitBasicTest
open Session HolLight.Syntax
open HolCore.Equal (lhs rhs)

private def ok (lbl : String) (b : Bool) : IO Unit :=
  IO.println (if b then s!"{lbl} -> OK" else s!"{lbl} -> MISMATCH")

private def pt (s : String) : IO term := do
  match ← HolCore.Parser.parse_term s with
  | .ok t => pure t
  | .error e => throw (IO.userError s!"parse `{s}`: {e}")

/-- Run an assertion; an exception is a MISMATCH. -/
private def run (lbl : String) (act : IO Bool) : IO Unit := do
  try ok lbl (← act) catch e => IO.println s!"{lbl} -> MISMATCH {e}"

/-- `rhs (concl (conv tm)) = expected`. -/
private def rhsIs (conv : term → IO (Except String thm)) (tm want : String) : IO Bool := do
  match ← conv (← pt tm) with
  | .ok th => pure ((← IO.ofExcept (rhs (concl th))) == (← pt want))
  | .error e => throw (IO.userError e)

/-- `assert_conv conv tm tm'` (basic_tests.ml 5-7). -/
private def assertConv (conv : term → IO (Except String thm)) (tm want : String) : IO Bool := do
  let t ← pt tm; let t' ← pt want
  match ← conv t with
  | .ok th =>
    let etm := concl th
    pure (hyp th == [] && is_eq etm &&
          (lhs etm |>.toOption) == some t && (rhs etm |>.toOption) == some t')
  | .error e => throw (IO.userError e)

/-- A command that must succeed. -/
private def succeeds (act : IO (Except String α)) : IO Bool := do
  match ← act with
  | .ok _ => pure true
  | .error e => throw (IO.userError e)

-- Verbose descriptive names for quantifiers/logical consts (13-17).
#eval (do
  for (a, b) in [("T", "true"), ("F", "false"), ("!(x:A). P x", "forall (x:A). P x"),
                 ("?(x:A). P x", "exists (x:A). P x"),
                 ("?!(x:A). P x", "existsunique (x:A). P x")] do
    run s!"`{a}` = `{b}`" (do pure ((← pt a) == (← pt b)))
  : IO Unit)

-- COMPUTE_CONVs (23-33).
#eval (do
  ensureHolPrefixThroughInt
  run "NUM_COMPUTE_CONV if x" (rhsIs NUM_COMPUTE_CONV
    "if x then 1 + 2 else 3 + 4" "if x then 1 + 2 else 3 + 4")
  run "NUM_COMPUTE_CONV if true" (rhsIs NUM_COMPUTE_CONV
    "if true then 1 + 2 else 3 + 4" "3")
  run "NUM_COMPUTE_CONV lambda" (rhsIs NUM_COMPUTE_CONV
    "\\x. x + (1 + 2)" "\\x. x + (1 + 2)")
  run "NUM_COMPUTE_CONV beta" (rhsIs NUM_COMPUTE_CONV
    "(\\x. x + (1 + 2)) (3 + 4)" "10")
  run "NUM_COMPUTE_CONV unknown_fn" (rhsIs NUM_COMPUTE_CONV
    "(unknown_fn:num->num) (1+2)" "(unknown_fn:num->num) 3")
  : IO Unit)

-- List-specific evaluation conversions (39-46).
#eval (do
  ensureHolPrefixThroughInt
  run "LIST_OF_SEQ_CONV" (assertConv LIST_OF_SEQ_CONV
    "list_of_seq (\\i. f(i + 17):B) 3" "[f (0 + 17):B; f (1 + 17); f (2 + 17)]")
  run "EL_CONV" (assertConv EL_CONV "EL 1 [0;1;2;3;4]" "1")
  run "LENGTH_CONV" (assertConv LENGTH_CONV "LENGTH[1;2;3;4;5]" "5")
  run "REVERSE_CONV" (assertConv REVERSE_CONV "REVERSE[a:X;b;c;d]" "[d:X;c;b;a]")
  : IO Unit)

-- basic_compset (52-83).
#eval (do
  ensureHolPrefixThroughInt
  match ← basic_compset with
  | .error e => IO.println s!"basic_compset -> MISMATCH {e}"
  | .ok cs =>
    let cv := CBV_CONV cs
    let wcv := WEAK_CBV_CONV cs
    run "WEAK_CBV_CONV gabs" (rhsIs wcv
      "(\\((x,y),(z,w)). x + y + z + w) ((1,2),(3,4))" "1 + 2 + 3 + 4")
    run "CBV_CONV gabs" (rhsIs cv
      "(\\((x,y),(z,w)). x + y + z + w) ((1,2),(3,4))" "1 + 2 + 3 + 4")
    run "WEAK_CBV_CONV body not reduced" (rhsIs wcv
      "(\\((x,y),(z,w)):(num#num)#(num#num). true /\\ true)"
      "(\\((x,y),(z,w)):(num#num)#(num#num). true /\\ true)")
    run "CBV_CONV body reduced" (rhsIs cv
      "(\\((x,y),(z,w)):(num#num)#(num#num). true /\\ true)"
      "(\\((x,y),(z,w)):(num#num)#(num#num). true)")
    run "WEAK_CBV_CONV match" (rhsIs wcv
      "match [1;2;3;4;5] with [] -> [] | CONS x (CONS y z) -> z" "[3; 4; 5]")
    run "CBV_CONV match" (rhsIs cv
      "match [1;2;3;4;5] with [] -> [] | CONS x (CONS y z) -> z" "[3; 4; 5]")
    run "WEAK_CBV_CONV let" (rhsIs wcv "let x = 1 in x + 2" "1 + 2")
    run "CBV_CONV let" (rhsIs cv "let x = 1 in x + 2" "1 + 2")
  : IO Unit)

-- Benign redefinition with a polymorphic type (90-93), and of an inductive
-- definition (100-107): each command run twice, both must succeed.
#eval (do
  ensureDefine
  let d := "(h_benign:A list -> num) [] = 0 /\\ h_benign (CONS _ t) = 1 + h_benign t"
  run "define h_benign" (do succeeds (define (← pt d)))
  run "define h_benign again (benign)" (do succeeds (define (← pt d)))
  let i := "(forall s. steps (step:S->S->bool) 0 (s:S) (s:S)) /\\ " ++
           "(forall s s'' n. (exists s'. step s s' /\\ steps step n s' s'') " ++
           "==> steps step (n+1) s s'')"
  run "new_inductive_definition steps" (do succeeds (new_inductive_definition (← pt i)))
  run "new_inductive_definition steps again (benign)"
    (do succeeds (new_inductive_definition (← pt i)))
  : IO Unit)

/-- A goalstack command that must succeed. -/
private def step (act : IO α) : IO Bool := do let _ ← act; pure true

-- The `er` command of the subgoal package (115-176): each case's proof in
-- THEN form, then in g-e(er) form ending in top_thm.
#eval (do
  ensureHolPrefixThroughInt
  -- case 1: er rotates 1 subgoal
  run "er case 1 (prove)" (succeeds (HolLight.prove r"x + 1 = 1 + x /\ 1 + 1 = 2"
    (CONJ_TAC THENL [ALL_TAC, ARITH_TAC] THEN REWRITE_TAC [ADD_SYM])).run)
  run "er case 1 (g/e/er)" (do
    let _ ← g (← pt "x + 1 = 1 + x /\\ 1 + 1 = 2")
    let _ ← e CONJ_TAC
    let _ ← er ALL_TAC
    let _ ← e ARITH_TAC
    let _ ← e (REWRITE_TAC [ADD_SYM])
    step top_thm)
  -- case 2: er rotates 2 subgoals
  let c2 := "(x + 1 = 1 + x /\\ (x + y) + z = x + (y + z)) /\\ 1 + 1 = 2"
  run "er case 2 (prove)" (succeeds
    (HolLight.prove r"(x + 1 = 1 + x /\ (x + y) + z = x + (y + z)) /\ 1 + 1 = 2"
      (CONJ_TAC THENL [CONJ_TAC, ARITH_TAC] THEN REWRITE_TAC [ADD_AC])).run)
  run "er case 2 (g/e/er)" (do
    let _ ← g (← pt c2)
    let _ ← e CONJ_TAC
    let _ ← er CONJ_TAC
    let _ ← e ARITH_TAC
    let _ ← e (REWRITE_TAC [ADD_AC])
    let _ ← e (REWRITE_TAC [ADD_AC])
    step top_thm)
  -- case 2': as case 2, with a b() after the er
  run "er case 2' (prove)" (succeeds
    (HolLight.prove r"(x + 1 = 1 + x /\ (x + y) + z = x + (y + z)) /\ 1 + 1 = 2"
      (CONJ_TAC THENL [CONJ_TAC, ARITH_TAC] THEN REWRITE_TAC [ADD_AC])).run)
  run "er case 2' (g/e/er/b)" (do
    let _ ← g (← pt c2)
    let _ ← e CONJ_TAC
    let _ ← er CONJ_TAC
    let _ ← b
    let _ ← er CONJ_TAC
    let _ ← e ARITH_TAC
    let _ ← e (REWRITE_TAC [ADD_AC])
    let _ ← e (REWRITE_TAC [ADD_AC])
    step top_thm)
  -- case 3: er rotates no subgoal (ARITH_TAC discharges it)
  run "er case 3 (prove)" (succeeds (HolLight.prove r"x + 1 = 1 + x /\ 1 + 1 = 2"
    (CONJ_TAC THENL [ARITH_TAC, ARITH_TAC])).run)
  run "er case 3 (g/e/er)" (do
    let _ ← g (← pt "x + 1 = 1 + x /\\ 1 + 1 = 2")
    let _ ← e CONJ_TAC
    let _ ← er ARITH_TAC
    let _ ← e ARITH_TAC
    step top_thm)
  : IO Unit)

-- Functions in lib (183-186).
#eval (do
  ok "find_index ((=) 10) [0;10;20] = Some 1"
    (HolCore.Lib.find_index (· == 10) [0, 10, 20] == some 1)
  ok "find_index ((=) 99) [0;10;20] = None"
    (HolCore.Lib.find_index (· == 99) [0, 10, 20] == none)
  ok "index 10 [0;10;20] = 1"
    (match HolCore.Lib.index 10 [0, 10, 20] with | .ok n => n == 1 | .error _ => false)
  ok "not (can (index 99) [0;10;20])"
    (match HolCore.Lib.index 99 [0, 10, 20] with | .ok _ => false | .error _ => true)
  : IO Unit)

-- bignum (194-207): `num n` is the Rat `n`, `//` is division.
#eval (do
  ok "power_num (num 0) (num 0) = num 1" (HolCore.Lib.power_num 0 0 == 1)
  ok "pow (num 0) 0 = num 1" (HolCore.Lib.pow 0 0 == 1)
  ok "power_num (num 2) (num 3) = num 8" (HolCore.Lib.power_num 2 3 == 8)
  ok "power_num (1/2) (num 3) = 1/8" (HolCore.Lib.power_num (1/2) 3 == 1/8)
  ok "power_num (1/2) (num 4) = 1/16" (HolCore.Lib.power_num (1/2) 4 == 1/16)
  ok "power_num (1/2) (num (-3)) = num 8" (HolCore.Lib.power_num (1/2) (-3) == 8)
  ok "power_num (1/2) (num (-4)) = num 16" (HolCore.Lib.power_num (1/2) (-4) == 16)
  ok "power_num (1/2) (num 0) = num 1" (HolCore.Lib.power_num (1/2) 0 == 1)
  ok "pow (num 2) 3 = num 8" (HolCore.Lib.pow 2 3 == 8)
  ok "pow (1/2) 3 = 1/8" (HolCore.Lib.pow (1/2) 3 == 1/8)
  ok "pow (1/2) 4 = 1/16" (HolCore.Lib.pow (1/2) 4 == 1/16)
  ok "pow (1/2) (-3) = num 8" (HolCore.Lib.pow (1/2) (-3) == 8)
  ok "pow (1/2) (-4) = num 16" (HolCore.Lib.pow (1/2) (-4) == 16)
  ok "pow (1/2) 0 = num 1" (HolCore.Lib.pow (1/2) 0 == 1)
  : IO Unit)

-- UNIFY_REFL_TAC (213-217).
#eval (do
  ensureHolPrefixThroughInt
  run "UNIFY_REFL_TAC_TEST" (succeeds
    (HolLight.prove r"?x. 1 = x" (META_EXISTS_TAC THEN UNIFY_REFL_TAC)).run)
  run "UNIFY_REFL_TAC_TEST2" (succeeds
    (HolLight.prove r"?f. y + z = f y z" (META_EXISTS_TAC THEN UNIFY_REFL_TAC)).run)
  run "UNIFY_REFL_TAC_TEST3" (succeeds
    (HolLight.prove r"?f. y + 1 = f y 0" (META_EXISTS_TAC THEN UNIFY_REFL_TAC)).run)
  : IO Unit)

-- check_axioms (229-233): after `new_axiom`, check_axioms must fail.  Last,
-- because the new axiom stays in `the_axioms` for the rest of the process.
#eval (do
  ensureHolPrefixThroughInt
  run "new_axiom `k = 1`" (do succeeds (HolCore.Kernel.new_axiom (← pt "k = 1")))
  run "check_axioms raises Failure" (do
    match ← check_axioms with
    | .ok _ => pure false
    | .error _ => pure true)
  : IO Unit)

end HolTest.UnitBasicTest
