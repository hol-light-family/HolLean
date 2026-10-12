/- File: HolTest/TacticsTest.lean
Runtime test suite: the tactic engine (tactics.ml).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

FAITHFULNESS BASIS.  This module is the tactic ENGINE, and `THEN`/`THENL`
misattachment is this project's most frequent historical defect class.  The
headline tests below therefore pin the SEMANTICS of `THENL`'s branch/subgoal
correspondence with a DISCRIMINATING PAIR that no wrong wiring can satisfy: a
right-length branch list must succeed, a wrong-length one must FAIL on arity,
and reordering the branches so a branch lands on the WRONG subgoal must FAIL.

Expectations come from:
  hol-light/Help/THENL.hlp   FAILURE: the resulting tactic fails "if the goal
                             list is not empty and its length is not the same as
                             that of the tactic list" - the arity gate pinned
                             below, and the branch/subgoal correspondence.
  hol-light/Help/THEN.hlp    "applies t2 to ALL the subgoals generated" - the
                             trailing-tactic-hits-every-survivor property.
  hol-light/Help/VALID.hlp   VALID must reject a tactic whose justification does
                             not reconstruct the original goal.
  hol-light/Help/CHANGED_TAC.hlp  fails "if the basic tactic ... has no effect".
  tactics.ml itself for the derived combinator and assumption-tactic behaviour.

All goals are BOOLEAN and use only `p`, `q` (`:bool`, from CommonTest) and the
propositional connectives, so NO arithmetic layer needs forcing.  Results are
checked by asserting the CONCLUSION of the proved theorem (a degenerate default
theorem prints as `|-  = ` and so cannot masquerade as a pass), or, for expected
failures, by asserting the tactic errored. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

namespace HolTest.TacticsTest

/- ---------------------------------------------------------------------- -/
/- Reporting helpers.                                                     -/
/-                                                                        -/
/- A passing assertion prints a line containing `-> OK`.  Because the      -/
/- headline `THENL` expectations are taken VERBATIM from THENL.hlp's       -/
/- FAILURE clause (arity / branch correspondence), a genuine defect there  -/
/- trips the `MISMATCH` build-gate.  Softer, derived expectations print     -/
/- `DIFFERS`.  An expected failure prints `-> OK (correctly rejected)`.     -/
/- ---------------------------------------------------------------------- -/

/-- A tactic proof must SUCCEED and its conclusion must equal `exp`.  Used for
    derived expectations, so a wrong conclusion is a soft `DIFFERS`. -/
private unsafe def proves (lbl : String) (act : IO (Except String thm))
    (exp : term) : IO Unit := do
  match ← act with
  | .ok th   => if concl th == exp then IO.println s!"{lbl} -> OK"
                else IO.println s!"{lbl} -> DIFFERS concl={reprStr (concl th)}"
  | .error e => IO.println s!"{lbl} -> DIFFERS unexpected error: {e}"

/-- A tactic proof must SUCCEED with conclusion `exp`; a failure is a hard
    build-gate `MISMATCH` (used where THENL.hlp says the shape must succeed). -/
private unsafe def provesGated (lbl : String) (act : IO (Except String thm))
    (exp : term) : IO Unit := do
  match ← act with
  | .ok th   => if concl th == exp then IO.println s!"{lbl} -> OK"
                else IO.println s!"{lbl} -> MISMATCH concl={reprStr (concl th)}"
  | .error e => IO.println s!"{lbl} -> MISMATCH unexpected error: {e}"

/-- A tactic proof must FAIL (build gate: THENL.hlp's arity/correspondence
    clause).  Prints `-> OK (correctly rejected)`, or `MISMATCH` if it somehow
    succeeded. -/
private unsafe def provesRejected (lbl : String) (act : IO (Except String thm)) :
    IO Unit := do
  match ← act with
  | .ok th   => IO.println s!"{lbl} -> MISMATCH unexpectedly proved {reprStr (concl th)}"
  | .error _ => IO.println s!"{lbl} -> OK (correctly rejected)"

/-- A tactic proof must FAIL with EXACTLY `expMsg`. -/
private unsafe def provesRejectedMsg (lbl : String) (act : IO (Except String thm))
    (expMsg : String) : IO Unit := do
  match ← act with
  | .ok th   => IO.println s!"{lbl} -> MISMATCH unexpectedly proved {reprStr (concl th)}"
  | .error e => if e == expMsg then IO.println s!"{lbl} -> OK (correctly rejected)"
                else IO.println s!"{lbl} -> DIFFERS msg=\"{e}\" expected=\"{expMsg}\""

/-- A raw tactic application (on a goal) must SUCCEED. -/
private def tacOk (lbl : String)
    (act : IO (Except String HolCore.Tactics.goalstate)) : IO Unit := do
  match ← act with
  | .ok _    => IO.println s!"{lbl} -> OK"
  | .error e => IO.println s!"{lbl} -> DIFFERS unexpected error: {e}"

/-- A raw tactic application must FAIL with EXACTLY `expMsg` (build gate). -/
private unsafe def tacRejectedMsg (lbl : String)
    (act : IO (Except String HolCore.Tactics.goalstate)) (expMsg : String) : IO Unit := do
  match ← act with
  | .ok _    => IO.println s!"{lbl} -> MISMATCH unexpectedly succeeded"
  | .error e => if e == expMsg then IO.println s!"{lbl} -> OK (correctly rejected)"
                else IO.println s!"{lbl} -> MISMATCH msg=\"{e}\" expected=\"{expMsg}\""

/- ---------------------------------------------------------------------- -/
/- Fixed goals and closing tactics, all boolean.                          -/
/- ---------------------------------------------------------------------- -/

-- Goal that splits into TWO subgoals via CONJ_TAC after a DISCH_TAC:
-- `p /\ q ==> p /\ q`.  After DISCH_TAC the assumption is `p /\ q`; CONJ_TAC
-- then yields subgoal `p` (first) and subgoal `q` (second), each carrying that
-- assumption.
private unsafe def goalPQ : term := ([[ p /\ q ==> p /\ q ]])

-- Closers keyed to a SPECIFIC subgoal, so a branch on the wrong subgoal fails.
-- `closeP` closes ONLY `p` (takes the first conjunct of the assumption);
-- `closeQ` closes ONLY `q` (the second conjunct); `closeEither` closes whichever
-- of `p`/`q` is the goal (used as a trailing tactic applied to every survivor).
private unsafe def closeP : HolCore.Tactics.tactic :=
  FIRST_ASSUM (fun th => ACCEPT_TAC (CONJUNCT1 th))
private unsafe def closeQ : HolCore.Tactics.tactic :=
  FIRST_ASSUM (fun th => ACCEPT_TAC (CONJUNCT2 th))
private unsafe def closeEither : HolCore.Tactics.tactic := ORELSE closeP closeQ

/- ====================================================================== -/
/- 1.  THEN / THENL SEMANTICS  - THE HEADLINE.                            -/
/- ====================================================================== -/

-- THENL with the RIGHT length (2 branches for 2 subgoals) SUCCEEDS, and the
-- branches land on the right subgoals (closeP on `p`, closeQ on `q`).
#eval provesGated "THENL right length [closeP, closeQ]"
  (prove goalPQ (THEN DISCH_TAC (THENL CONJ_TAC [closeP, closeQ])))
  ([[ p /\ q ==> p /\ q ]])

-- BRANCH/SUBGOAL CORRESPONDENCE (THENL.hlp): swapping the branches so closeQ
-- lands on subgoal `p` and closeP on subgoal `q` must FAIL - closeP cannot close
-- `q` (CONJUNCT1 gives `p`, not `q`) and vice-versa.  This is the misattachment
-- the historical defect class produces; a wrong engine that ignored order would
-- wrongly pass.
#eval provesRejected "THENL swapped branches [closeQ, closeP] fails"
  (prove goalPQ (THEN DISCH_TAC (THENL CONJ_TAC [closeQ, closeP])))

-- WRONG LENGTH (too FEW): 1 branch for 2 subgoals must FAIL on arity
-- (THENL.hlp: "length is not the same as that of the tactic list").
#eval provesRejected "THENL too few branches [closeP] fails on arity"
  (prove goalPQ (THEN DISCH_TAC (THENL CONJ_TAC [closeP])))

-- WRONG LENGTH (too MANY): 3 branches for 2 subgoals must FAIL on arity.
#eval provesRejected "THENL too many branches [closeP,closeQ,closeQ] fails on arity"
  (prove goalPQ (THEN DISCH_TAC (THENL CONJ_TAC [closeP, closeQ, closeQ])))

-- TRAILING TACTIC HITS EVERY SURVIVOR (THEN.hlp: "applies t2 to ALL the
-- subgoals generated").  Leave BOTH subgoals open with ALL_TAC branches, then a
-- single trailing `closeEither` must close BOTH.
#eval provesGated "THEN (THENL CONJ_TAC [ALL_TAC,ALL_TAC]) closeEither"
  (prove goalPQ (THEN DISCH_TAC
      (THEN (THENL CONJ_TAC [ALL_TAC, ALL_TAC]) closeEither)))
  ([[ p /\ q ==> p /\ q ]])

-- ... whereas folding that trailing tactic INTO the branch list as a THIRD
-- branch must FAIL on arity (2 subgoals, 3 branches) - the exact confusion the
-- defect class embodies.  Discriminating partner of the test above.
#eval provesRejected "THENL CONJ_TAC [ALL_TAC,ALL_TAC,closeEither] fails on arity"
  (prove goalPQ (THEN DISCH_TAC
      (THENL CONJ_TAC [ALL_TAC, ALL_TAC, closeEither])))

-- THEN applies the same tactic to every subgoal (THEN.hlp example shape
-- `EQ_TAC THEN t`): here CONJ_TAC yields 2 subgoals and the single trailing
-- `closeEither` closes both, with NO branch list at all.
#eval provesGated "THEN CONJ_TAC closeEither (same tac to all subgoals)"
  (prove goalPQ (THEN DISCH_TAC (THEN CONJ_TAC closeEither)))
  ([[ p /\ q ==> p /\ q ]])

/- ====================================================================== -/
/- 2.  VALID  - the validity checker (tactics.ml `VALID`).               -/
/- ====================================================================== -/

-- A genuinely valid tactic passes VALID unchanged: VALID CONJ_TAC on `p /\ q`
-- must SUCCEED (return a goalstate), because CONJ_TAC's justification (CONJ)
-- reconstructs `p /\ q` from the two subgoals.
#eval tacOk "VALID passes a valid CONJ_TAC"
  (VALID CONJ_TAC ([], [[ p /\ q ]]))

-- A tactic that LIES - claims to have solved goal `p` but whose justification
-- yields `|- q = q` (concl `q = q`, not `p`) - must be caught.  The raw tactic
-- SUCCEEDS on its own (so the discrimination is real, not vacuous), but wrapping
-- it in VALID rejects it with the exact message "VALID: Invalid tactic".
private unsafe def bogusTac : HolCore.Tactics.tactic :=
  fun _ => return .ok (HolCore.Tactics.null_meta, [], fun _ _ => return (.ok (REFL q)))

-- The bogus tactic itself succeeds (proving the check below is discriminating).
#eval tacOk "bogus tactic itself succeeds (control)"
  (bogusTac ([], p))

-- VALID catches it, with the literal kernel-style message.
#eval tacRejectedMsg "VALID rejects a lying tactic"
  (VALID bogusTac ([], p)) "VALID: Invalid tactic"

/- ====================================================================== -/
/- 3.  Combinators: TRY REPEAT EVERY FIRST ORELSE CHANGED_TAC            -/
/-     REPLICATE_TAC MAP_EVERY.                                           -/
/- ====================================================================== -/

-- TRY t = t on success, ALL_TAC on failure (tactics.ml: ORELSE tac ALL_TAC).
-- TRY NO_TAC therefore behaves as ALL_TAC (does not abort the proof).
#eval proves "TRY NO_TAC acts as ALL_TAC"
  (prove ([[ p ==> p ]]) (THEN (TRY NO_TAC) (THEN DISCH_TAC (FIRST_ASSUM ACCEPT_TAC))))
  ([[ p ==> p ]])

-- REPEAT applies a tactic until it fails: REPEAT DISCH_TAC discharges BOTH
-- antecedents of `p ==> q ==> p`.
#eval proves "REPEAT DISCH_TAC discharges both antecedents"
  (prove ([[ p ==> q ==> p ]]) (THEN (REPEAT DISCH_TAC) (FIRST_ASSUM ACCEPT_TAC)))
  ([[ p ==> q ==> p ]])

-- EVERY runs a list of tactics in sequence (left-first fold onto ALL_TAC).
#eval proves "EVERY [DISCH_TAC, FIRST_ASSUM ACCEPT_TAC]"
  (prove ([[ p ==> p ]]) (EVERY [DISCH_TAC, FIRST_ASSUM ACCEPT_TAC]))
  ([[ p ==> p ]])

-- FIRST tries each tactic until one succeeds: NO_TAC fails, DISCH_TAC runs.
#eval proves "FIRST [NO_TAC, DISCH_TAC]"
  (prove ([[ p ==> p ]]) (THEN (FIRST [NO_TAC, DISCH_TAC]) (FIRST_ASSUM ACCEPT_TAC)))
  ([[ p ==> p ]])

-- ORELSE: first tactic fails, second runs.
#eval proves "ORELSE NO_TAC DISCH_TAC"
  (prove ([[ p ==> p ]]) (THEN (ORELSE NO_TAC DISCH_TAC) (FIRST_ASSUM ACCEPT_TAC)))
  ([[ p ==> p ]])

-- CHANGED_TAC: DISCH_TAC changes the goal, so CHANGED_TAC DISCH_TAC succeeds.
#eval proves "CHANGED_TAC DISCH_TAC (has effect) succeeds"
  (prove ([[ p ==> p ]]) (THEN (CHANGED_TAC DISCH_TAC) (FIRST_ASSUM ACCEPT_TAC)))
  ([[ p ==> p ]])

-- CHANGED_TAC ALL_TAC has NO effect, so it must FAIL with "CHANGED_TAC"
-- (CHANGED_TAC.hlp: fails "if the basic tactic ... has no effect").
#eval provesRejectedMsg "CHANGED_TAC ALL_TAC (no effect) fails"
  (prove ([[ p ==> p ]]) (THEN (CHANGED_TAC ALL_TAC) (THEN DISCH_TAC (FIRST_ASSUM ACCEPT_TAC))))
  "CHANGED_TAC"

-- REPLICATE_TAC n t applies t exactly n times: REPLICATE_TAC 2 DISCH_TAC
-- discharges the two antecedents of `p ==> q ==> p`.
#eval proves "REPLICATE_TAC 2 DISCH_TAC"
  (prove ([[ p ==> q ==> p ]]) (THEN (REPLICATE_TAC 2 DISCH_TAC) (FIRST_ASSUM ACCEPT_TAC)))
  ([[ p ==> q ==> p ]])

-- MAP_EVERY tacf lst = EVERY (map tacf lst): applying DISCH_TAC once per list
-- element (twice here) discharges both antecedents.
#eval proves "MAP_EVERY (fun _ => DISCH_TAC) [1,2]"
  (prove ([[ p ==> q ==> p ]])
    (THEN (MAP_EVERY (fun (_ : Nat) => DISCH_TAC) [1, 2]) (FIRST_ASSUM ACCEPT_TAC)))
  ([[ p ==> q ==> p ]])

/- ====================================================================== -/
/- 4.  Assumption tactics: ASSUME_TAC POP_ASSUM FIRST_ASSUM              -/
/-     RULE_ASSUM_TAC LABEL_TAC/USE_THEN/REMOVE_THEN and ASM.            -/
/- ====================================================================== -/

-- POP_ASSUM applies its continuation to the MOST RECENT assumption, removing it.
-- Here it takes CONJUNCT1 of the discharged `p /\ q` to close goal `p`.
#eval proves "POP_ASSUM (CONJUNCT1) proves p /\\ q ==> p"
  (prove ([[ p /\ q ==> p ]]) (THEN DISCH_TAC (POP_ASSUM (fun th => ACCEPT_TAC (CONJUNCT1 th)))))
  ([[ p /\ q ==> p ]])

-- FIRST_ASSUM tries its continuation on each assumption until one works.
#eval proves "FIRST_ASSUM ACCEPT_TAC proves p ==> p"
  (prove ([[ p ==> p ]]) (THEN DISCH_TAC (FIRST_ASSUM ACCEPT_TAC)))
  ([[ p ==> p ]])

-- ASSUME_TAC adds a theorem to the assumptions (ASSUME_TAC = LABEL_TAC "").
-- Discharge `p`, re-add `p /\ q`'s... here simply: prove `p ==> p` by ASSUME_TAC
-- of the popped hypothesis then close.
#eval proves "ASSUME_TAC re-adds a hypothesis"
  (prove ([[ p ==> p ]]) (THEN DISCH_TAC (POP_ASSUM (fun th =>
      THEN (ASSUME_TAC th) (FIRST_ASSUM ACCEPT_TAC)))))
  ([[ p ==> p ]])

-- RULE_ASSUM_TAC applies a rule to EVERY assumption.  Discharge `p /\ q`, map
-- CONJUNCT2 over the assumptions (turning `p /\ q` into `q`), then close `q`.
#eval proves "RULE_ASSUM_TAC CONJUNCT2 rewrites the assumption to q"
  (prove ([[ p /\ q ==> q ]]) (THEN DISCH_TAC
      (THEN (RULE_ASSUM_TAC (fun th => return (CONJUNCT2 th))) (FIRST_ASSUM ACCEPT_TAC))))
  ([[ p /\ q ==> q ]])

-- LABEL_TAC gives an assumption a name; USE_THEN retrieves it BY THAT NAME and
-- (unlike REMOVE_THEN) keeps it in place.
#eval proves "LABEL_TAC \"h\" + USE_THEN \"h\" ACCEPT_TAC"
  (prove ([[ p ==> p ]]) (THEN (DISCH_THEN (LABEL_TAC "h")) (USE_THEN "h" ACCEPT_TAC)))
  ([[ p ==> p ]])

-- REMOVE_THEN retrieves the labelled assumption and REMOVES it.
#eval proves "LABEL_TAC \"h\" + REMOVE_THEN \"h\" ACCEPT_TAC"
  (prove ([[ p ==> p ]]) (THEN (DISCH_THEN (LABEL_TAC "h")) (REMOVE_THEN "h" ACCEPT_TAC)))
  ([[ p ==> p ]])

-- USE_THEN on a MISSING label must fail with the exact message
-- "USE_TAC: didn't find assumption <s>" (tactics.ml).
#eval provesRejectedMsg "USE_THEN missing label fails"
  (prove ([[ p ==> p ]]) (THEN DISCH_TAC (USE_THEN "nope" ACCEPT_TAC)))
  "USE_TAC: didn't find assumption nope"

-- ASM prepends ALL current assumptions to the theorem list handed to its inner
-- list-tactic (tactics.ml:318, the `let (ASM : ...)` form).  Here the inner
-- tactic tries to ACCEPT one of the supplied theorems; with `[]` extra, the sole
-- supplied theorem is the discharged assumption `p`, which closes goal `p`.
#eval proves "ASM prepends assumptions to the theorem list"
  (prove ([[ p ==> p ]]) (THEN DISCH_TAC (ASM (fun ths => FIRST (ths.map ACCEPT_TAC)) [])))
  ([[ p ==> p ]])

/- ====================================================================== -/
/- 5.  TAC_PROOF and prove.                                              -/
/- ====================================================================== -/

-- TAC_PROOF runs a tactic against a full goal (assumptions allowed) and returns
-- the theorem.  Prove `p ==> p` with an EMPTY assumption list.
#eval proves "TAC_PROOF ([], p ==> p)"
  (TAC_PROOF ([], [[ p ==> p ]]) (THEN DISCH_TAC (FIRST_ASSUM ACCEPT_TAC)))
  ([[ p ==> p ]])

-- TAC_PROOF with an ASSUMPTION in the goal: `[p] ?- p` closed by the assumption.
-- This distinguishes TAC_PROOF (assumptions permitted) from `prove` (which
-- rejects leftover assumptions).  The resulting theorem has `p` as a hypothesis.
#eval (do
  match ← TAC_PROOF ([("", (ASSUME p : Except String thm).toOption.get!)], p)
                    (FIRST_ASSUM ACCEPT_TAC) with
  | .ok th => if concl th == CommonTest.p && hyp th == [CommonTest.p] then
                IO.println "TAC_PROOF with assumption (p ?- p) -> OK"
              else IO.println s!"TAC_PROOF with assumption -> DIFFERS concl={reprStr (concl th)} hyp={reprStr (hyp th)}"
  | .error e => IO.println s!"TAC_PROOF with assumption -> DIFFERS error: {e}")

-- `prove` proves a small goal and returns an ASSUMPTION-FREE theorem.
#eval (do
  match ← prove ([[ p ==> p ]]) (THEN DISCH_TAC (FIRST_ASSUM ACCEPT_TAC)) with
  | .ok th => if concl th == ([[ p ==> p ]] : term) && hyp th == [] then
                IO.println "prove p ==> p (no leftover hyps) -> OK"
              else IO.println s!"prove p ==> p -> DIFFERS concl={reprStr (concl th)} hyp={reprStr (hyp th)}"
  | .error e => IO.println s!"prove p ==> p -> DIFFERS error: {e}")

-- `prove` REJECTS a goal that the tactic does not actually close: ALL_TAC leaves
-- the goal `p` open, so `prove` must fail with "TAC_PROOF: Unsolved goals"
-- rather than fabricate a theorem.  (A free variable `p` is unprovable.)
#eval provesRejectedMsg "prove rejects an unsolved (false) goal"
  (prove p ALL_TAC) "TAC_PROOF: Unsolved goals"

end HolTest.TacticsTest


/- ---------------------------------------------------------------------- -/
/- X_GEN_TAC's type-mismatch DIAGNOSTIC (tactics.ml 474-478).              -/
/- ---------------------------------------------------------------------- -/
/-
  `tactic_type_compatibility_check` reports BOTH types:
      failwith(pfx ^ ": expected type :" ^ string_of_type et ^
               " but got :" ^ string_of_type gt)
  Ours had collapsed this to a bare "type mismatch", losing exactly the
  information the user needs.  Pinned here because a shortened diagnostic is
  invisible to any test that only checks success/failure.
-/

#eval (do
  (do
    -- goal `!x:bool. x`, specialised with a variable of the WRONG type.
    match ← HolCore.Parser.parse_term "!x:bool. x" with
    | .error e => IO.println s!"X_GEN_TAC diagnostic -> parse ERR {e}"
    | .ok w =>
      let wrong : term := HolCore.Kernel.mk_var "y" HolCore.Kernel.aty
      match ← Session.X_GEN_TAC wrong ([], w) with
      | .ok _ => IO.println "X_GEN_TAC diagnostic -> DIFFERS unexpectedly succeeded"
      | .error e =>
        -- must name BOTH types, not just say "type mismatch"
        if e.startsWith "X_GEN_TAC: expected type :" && (e.splitOn " but got :").length == 2 then
          IO.println s!"X_GEN_TAC names both types -> OK ({e})"
        else
          IO.println s!"X_GEN_TAC diagnostic -> MISMATCH got \"{e}\""))
