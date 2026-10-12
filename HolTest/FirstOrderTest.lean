/- File: HolTest/FirstOrderTest.lean
Runtime test suite: firstorder.ml - first-order shadow-term facilities used by
the connection provers (meson/metis and the CoPs).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

FAITHFULNESS BASIS.  Two layers are exercised.
  (1) `Utils.List` - small pure list combinators.  Their expected outputs are
      read straight off the OCaml definitions in
        hol-light/firstorder.ml   (module Utils.List)
      and the doc comments in HolCore/FirstOrder.lean, e.g. `nth_rest i l`
      returns "the i-th element ... as well as the elements before and after
      (in order)".
  (2) `Mapping` - the HOL-term <-> first-order shadow-syntax translation
      (`fol_of_term`/`fol_of_form`/`hol_of_term`).  These pin the CONSTANT and
      VARIABLE numbering scheme (from meson.ml's stores: `reset_consts` seeds
      `F` at code 1 with the counter at 2, and `fol_of_var` allocates 0,1,2,...)
      and check that a constant-headed term ROUND-TRIPS HOL -> FOL -> HOL.

NUMBERING NOTE.  `Session.FoS` is a set of persistent `initialize` refs, so
every numbering assertion first calls `fo_reset_vars`/`fo_reset_consts`, making
the allocated codes deterministic regardless of what ran before.

VARIABLE ROUND-TRIP CAVEAT.  `hol_of_term` maps a shadow variable `Fvar n` to a
FRESH genvar (FirstOrder's `hol_of_var` always allocates into `gstore`; it does
NOT recover the original HOL variable name).  So only CONSTANT-headed terms can
round-trip to a syntactically identical HOL term; the round-trip test below uses
`T /\ F` for exactly that reason. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

open HolCore.Meson (fol_term fol_form)
open HolCore.FirstOrder.Utils.List

/- ---------------------------------------------------------------------- -/
/- (1) Utils.List pure combinators.  Expected values from firstorder.ml.   -/
/- ---------------------------------------------------------------------- -/

/-- Compare an `Except`-valued result against an expected `.ok` payload. -/
private def okCheck [BEq α] [Repr α] (lbl : String)
    (got : Except String α) (expected : α) : IO Unit := do
  match got with
  | .ok v => if v == expected then IO.println s!"{lbl} -> OK"
             else IO.println s!"{lbl} -> MISMATCH got={repr v} expected={repr expected}"
  | .error e => IO.println s!"{lbl} -> MISMATCH unexpected error {e}"

/-- Assert an `Except`-valued result is `.error` with a message containing
    `needle` (the `failwith` text matters). -/
private def errCheck (lbl : String) (got : Except String α) (needle : String) : IO Unit := do
  match got with
  | .error e => if needle.isEmpty || (e.splitOn needle).length > 1 then
                  IO.println s!"{lbl} -> OK (correctly rejected: {e})"
                else IO.println s!"{lbl} -> MISMATCH wrong error text {e} (want {needle})"
  | .ok _ => IO.println s!"{lbl} -> MISMATCH wrongly succeeded"

/-- Plain equality check for non-`Except` values. -/
private def eqCheck [BEq α] [Repr α] (lbl : String) (got expected : α) : IO Unit := do
  if got == expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={repr got} expected={repr expected}"

-- `nth_rest 1 [10,20,30]`: the element 20, with [10] before (in order) and
-- [30] after.  (firstorder.ml: `nth_rest i l` -> x, (List.rev acc, xs).)
#eval okCheck "nth_rest 1 [10,20,30]"
  (nth_rest 1 [10, 20, 30]) (20, ([10], [30]))
-- Out of range must fail with exactly "nth_rest".
#eval errCheck "nth_rest 5 [1,2] fails"
  (nth_rest 5 [1, 2]) "nth_rest"

-- `insert_at 1 99 [1,2,3]` = [1,99,2,3].
#eval okCheck "insert_at 1 99 [1,2,3]"
  (insert_at 1 99 [1, 2, 3]) [1, 99, 2, 3]
-- `insert_at 0 99 [1,2]` prepends.
#eval okCheck "insert_at 0 99 [1,2]"
  (insert_at 0 99 [1, 2]) [99, 1, 2]
-- Past the end fails with "insert_at".
#eval errCheck "insert_at 5 9 [1] fails"
  (insert_at 5 9 [1]) "insert_at"

-- `take_drop 2 [1,2,3,4]` = ([1,2],[3,4]).
#eval okCheck "take_drop 2 [1,2,3,4]"
  (take_drop 2 [1, 2, 3, 4]) ([1, 2], [3, 4])
-- Too short fails with "take_drop".
#eval errCheck "take_drop 5 [1,2] fails"
  (take_drop 5 [1, 2]) "take_drop"
-- `take 2 [1,2,3]` = fst (take_drop ...).
#eval okCheck "take 2 [1,2,3]" (take 2 [1, 2, 3]) [1, 2]

-- `list_rest [1,2,3]`: each element paired with (reversed-before, after).
-- firstorder.ml: go [] l with acc built by (x::acc), so the "before" list is
-- in REVERSE order (that is the source's behaviour, unlike nth_rest).
#eval eqCheck "list_rest [1,2,3]"
  (list_rest [1, 2, 3])
  [(1, ([], [2, 3])), (2, ([1], [3])), (3, ([2, 1], []))]

-- `findi p l`: first (index, element) with p.  Index is 0-based.
#eval okCheck "findi (=20) [10,20,30]"
  (findi (fun _ x => x == 20) [10, 20, 30]) (1, 20)
#eval errCheck "findi (none) [1,2] fails"
  (findi (fun _ _ => false) [1, 2]) "findi"

-- `fold_right1 (+) [1,2,3] = 1+(2+3) = 6`; empty fails with "fold_right1".
#eval okCheck "fold_right1 (+) [1,2,3]"
  (fold_right1 (· + ·) [1, 2, 3]) 6
#eval errCheck "fold_right1 [] fails"
  (fold_right1 (· + ·) ([] : List Nat)) "fold_right1"

-- `exists_unique p l`: true iff EXACTLY one element satisfies p.
#eval eqCheck "exists_unique (=2) [1,2,3] = true"
  (exists_unique (fun x => x == 2) [1, 2, 3]) true
#eval eqCheck "exists_unique (>0) [1,2] = false (two match)"
  (exists_unique (fun x => x > 0) [1, 2]) false
#eval eqCheck "exists_unique (=9) [1,2] = false (none match)"
  (exists_unique (fun x => x == 9) [1, 2]) false

-- `union2 [1,2] [2,3]`: 1 not in y -> keep; 2 in y -> drop.  Result [1,2,3].
-- (firstorder.ml union2: [] -> y | h::t -> if mem h y then union1 t y
--  else union2 t (h::y).)
#eval eqCheck "union2 [1,2] [2,3]"
  (union2 [1, 2] [2, 3]) [1, 2, 3]

-- `concat_map f l = concat (map f l)`.
#eval eqCheck "concat_map (fun n => [n,n]) [1,2]"
  (concat_map (fun n => [n, n]) [1, 2]) [1, 1, 2, 2]

/- ---------------------------------------------------------------------- -/
/- (2) Mapping: HOL term -> first-order shadow syntax.                     -/
/- ---------------------------------------------------------------------- -/

/-- Compare a `fol_term` result (after resets) against an expected shadow term. -/
private def folTermCheck (lbl : String)
    (act : IO (Except String fol_term)) (expected : fol_term) : IO Unit := do
  match ← act with
  | .ok v => if v == expected then IO.println s!"{lbl} -> OK"
             else IO.println s!"{lbl} -> MISMATCH got={repr v} expected={repr expected}"
  | .error e => IO.println s!"{lbl} -> MISMATCH unexpected error {e}"

/-- Compare a `fol_form` result (after resets) against an expected shadow form. -/
private def folFormCheck (lbl : String)
    (act : IO (Except String fol_form)) (expected : fol_form) : IO Unit := do
  match ← act with
  | .ok v => if v == expected then IO.println s!"{lbl} -> OK"
             else IO.println s!"{lbl} -> MISMATCH got={repr v} expected={repr expected}"
  | .error e => IO.println s!"{lbl} -> MISMATCH unexpected error {e}"

-- `fol_of_term [] [] (T /\ F)`.  Fresh stores: `reset_consts` puts F at code 1,
-- counter 2.  `fol_of_term` codes the HEAD first, so `/\` -> 2, then arg `T`
-- -> 3, then arg `F` is already 1.  Hence `Fnapp 2 [Fnapp 3 [], Fnapp 1 []]`.
#eval (do
  fo_reset_vars
  let _ ← fo_reset_consts
  folTermCheck "fol_of_term (T /\\ F) constant numbering"
    (fo_fol_of_term [] [] [[ T /\ F ]])
    (.Fnapp 2 [.Fnapp 3 [], .Fnapp 1 []]))

-- Variables: `fol_of_term [] [] (p /\ p)` codes `/\` -> 2 and the (single,
-- reused) variable `p` -> Fvar 0 BOTH times (the vstore assoc keeps it stable).
#eval (do
  fo_reset_vars
  let _ ← fo_reset_consts
  folTermCheck "fol_of_term (p /\\ p) reuses one var code"
    (fo_fol_of_term [] [] [[ (p:bool) /\ p ]])
    (.Fnapp 2 [.Fvar 0, .Fvar 0]))

-- Two DISTINCT variables get DISTINCT, increasing codes: p -> 0, q -> 1.
#eval (do
  fo_reset_vars
  let _ ← fo_reset_consts
  folTermCheck "fol_of_term (p /\\ q) numbers vars 0,1"
    (fo_fol_of_term [] [] [[ (p:bool) /\ q ]])
    (.Fnapp 2 [.Fvar 0, .Fvar 1]))

-- `fol_of_form [] [] (!x:bool. x = x)`.  The bound var is coded FIRST (fv -> 0),
-- then the body's equality atom codes `=` -> 2, with both args the bound var 0.
-- Result: Forallq 0 (Atom (2, [Fvar 0, Fvar 0])).
#eval (do
  fo_reset_vars
  let _ ← fo_reset_consts
  folFormCheck "fol_of_form (!x. x = x) structure + numbering"
    (fo_fol_of_form [] [] [[ !x:bool. x = x ]])
    (.Forallq 0 (.Atom (2, [.Fvar 0, .Fvar 0]))))

-- Higher-order formula: in `!x:bool. x` the body's head is the bound `x`, so
-- translating the body fails ("fol_of_atom: higher order", firstorder.ml 174).
-- The `try` in fol_of_form (185) covers that call, so the quantifier case
-- fails as a whole and the formula is translated as one literal: `(!)` applied
-- to `\x. x`.  Real HOL Light gives `Atom (2, [_])`, one argument.
#eval (do
  fo_reset_vars
  let _ ← fo_reset_consts
  match ← fo_fol_of_form [] [] [[ !x:bool. x ]] with
  | .ok (.Atom (_, [_])) => IO.println "fol_of_form (!x. x) falls back to a literal (as HOL Light) -> OK"
  | .ok v => IO.println s!"fol_of_form (!x. x) -> MISMATCH {repr v}"
  | .error e => IO.println s!"fol_of_form (!x. x) -> MISMATCH failed: {e}")

-- ROUND TRIP for a constant-headed term: HOL `T /\ F` -> shadow -> HOL, and the
-- reconstructed term must PRINT identically.  (Variables cannot round-trip; see
-- the header caveat, hence a purely constant term is used.)
#eval (do
  fo_reset_vars
  let _ ← fo_reset_consts
  let tm : term := [[ T /\ F ]]
  match ← fo_fol_of_term [] [] tm with
  | .error e => IO.println s!"round-trip fol_of_term ERR: {e}"
  | .ok ft =>
    match ← fo_hol_of_term (type_of tm) ft with
    | .error e => IO.println s!"round-trip hol_of_term ERR: {e}"
    | .ok back => do
        let s ← HolCore.Printer.string_of_term back
        if s == "true /\\ false" then IO.println "round-trip T /\\ F -> OK"
        else IO.println s!"round-trip T /\\ F -> MISMATCH got={s} expected=true /\\ false")
