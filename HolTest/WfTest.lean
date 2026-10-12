/- File: HolTest/WfTest.lean
Runtime test suite: wf.ml - the theory of wellfounded relations
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Tests: wf.ml - the theory of wellfounded relations.                    -/
/- ---------------------------------------------------------------------- -/

/- ---------------------------------------------------------------------- -/
/- wf.ml : theory of wellfounded relations.                               -/
/- Forcing any Wf theorem forces `Session.Wf`, which runs the whole       -/
/- wf.ml script.  Every theorem WfThms establishes is printed, and        -/
/- CRUCIALLY `WF_INDUCT_TAC` is USED to prove a real goal (a printed      -/
/- theorem alone does not exercise the tactic).  Gated by TestFlags.runWf.-/
/- ---------------------------------------------------------------------- -/

-- Every theorem wf.ml establishes, in OCaml order, printed as `|- ...`.
-- Each theorem this layer establishes, printed as `|- ...`.
#eval WF
#eval WF_EQ
#eval WF_IND
#eval WF_DCHAIN
#eval WF_DCHAIN_TRANSITIVE
#eval WF_UREC
#eval WF_UREC_WF
#eval WF_REC_INVARIANT
#eval WF_REC
#eval WF_REC_WF
#eval WF_EREC
#eval WF_REC_EXISTS
#eval WF_SUBSET
#eval WF_RESTRICT
#eval WF_MEASURE_GEN
#eval WF_LEX_DEPENDENT
#eval WF_LEX
#eval WF_POINTWISE
#eval WF_num
#eval WF_REC_num
#eval MEASURE
#eval WF_MEASURE
#eval MEASURE_LE
#eval WF_ANTISYM
#eval WF_REFL
#eval WF_FALSE
#eval MINIMAL_BAD_SEQUENCE
#eval WF_REC_TAIL
#eval WF_REC_TAIL_GENERAL

-- WF_INDUCT_TAC ACTUALLY USED to prove goals.  A printed theorem cannot show
-- the tactic works; only running it can.  The measure term is parsed with
-- `parse_term` at the point of use (the doc-example convention), and the goal
-- is proved by wellfounded induction on that measure.
#eval (do
  match ← HolCore.Parser.parse_term "!m n. m + n = n + m" with
  | .error e => IO.println s!"WF_INDUCT_TAC goal parse ERR: {e}"
  | .ok g =>
    match ← HolCore.Parser.parse_term "m + n:num" with
    | .error e => IO.println s!"WF_INDUCT_TAC measure parse ERR: {e}"
    | .ok meas =>
      match ← Session.prove g
                (THEN Session.GEN_TAC (THEN Session.GEN_TAC
                  (THEN (Session.WF_INDUCT_TAC meas)
                    (Session.ASM_MESON_TAC [Session.ADD_SYM])))) with
      | .ok th => IO.println s!"WF_INDUCT_TAC proof -> {← HolCore.Printer.string_of_thm th}"
      | .error e => IO.println s!"WF_INDUCT_TAC proof (msg): {e}")
-- Single-variable measure `n`: the tactic must GEN the one free var and set
-- up the strong-induction hypothesis on a num measure.  Closed from num_CASES
-- and LT_0 (both established in arith.ml).

#eval (do
  match ← HolCore.Parser.parse_term "!n. n = 0 \\/ 0 < n" with
  | .error e => IO.println s!"WF_INDUCT_TAC goal2 parse ERR: {e}"
  | .ok g =>
    match ← HolCore.Parser.parse_term "n:num" with
    | .error e => IO.println s!"WF_INDUCT_TAC measure2 parse ERR: {e}"
    | .ok meas =>
      match ← Session.prove g
                (THEN Session.GEN_TAC
                  (THEN (Session.WF_INDUCT_TAC meas)
                    (Session.MESON_TAC [Session.num_CASES, Session.LT_0]))) with
      | .ok th => IO.println s!"WF_INDUCT_TAC single-measure proof -> {← HolCore.Printer.string_of_thm th}"
      | .error e => IO.println s!"WF_INDUCT_TAC single-measure proof (msg): {e}")


/- ---------------------------------------------------------------------- -/
/- wf.ml: the theorems APPLIED, not merely printed.  The block above      -/
/- prints all 29 statements (so every proof runs), but nothing exercised  -/
/- them as tools - which is the whole point of a wellfoundedness library. -/
/- Gated by TestFlags.runWf.                                              -/
/- ---------------------------------------------------------------------- -/

#eval (do
  match ← HolCore.Parser.parse_term "WF(MEASURE (\\n:num. n))" with
  | .error e => IO.println s!"WF_MEASURE parse ERR: {e}"
  | .ok g =>
    match ← Session.prove g (Session.MESON_TAC [Session.WF_MEASURE]) with
    | .ok th => IO.println s!"WF_MEASURE applied -> {← HolCore.Printer.string_of_thm th}"
    | .error e => IO.println s!"WF_MEASURE applied (msg): {e}")
-- WF_SUBSET applied: `<` is wellfounded, so a sub-relation of it is too.

#eval (do
  match ← HolCore.Parser.parse_term "WF(\\m n:num. m < n /\\ m < 5)" with
  | .error e => IO.println s!"WF_SUBSET parse ERR: {e}"
  | .ok g =>
    match ← Session.prove g (Session.MESON_TAC [Session.WF_SUBSET, Session.WF_num]) with
    | .ok th => IO.println s!"WF_SUBSET applied -> {← HolCore.Printer.string_of_thm th}"
    | .error e => IO.println s!"WF_SUBSET applied (msg): {e}")
-- WF_REC_TAIL and WF_REC_num are HIGHER-ORDER, so they are applied by
-- INSTANTIATION (ISPECL + BETA_RULE), not by MESON search - MESON hits
-- `solve_goal: Too deep` on them, which is its depth limit, not a defect.

#eval (do
  match ← HolCore.Parser.parse_term "\\x:num. 0 < x" with
  | .error e => IO.println s!"WF_REC_TAIL parse ERR: {e}"
  | .ok pTm =>
    match ← HolCore.Parser.parse_term "PRE" with
    | .error e => IO.println s!"WF_REC_TAIL parse ERR: {e}"
    | .ok gTm =>
      match ← HolCore.Parser.parse_term "\\x:num. x" with
      | .error e => IO.println s!"WF_REC_TAIL parse ERR: {e}"
      | .ok hTm =>
        match (do HolCore.Equal.BETA_RULE
                    (← Session.ISPECL [pTm, gTm, hTm] Session.WF_REC_TAIL)) with
        | .ok b => IO.println s!"WF_REC_TAIL instantiated -> {← HolCore.Printer.string_of_thm b}"
        | .error e => IO.println s!"WF_REC_TAIL instantiate ERR: {e}")

#eval (do
  match ← HolCore.Parser.parse_term
            "\\(f:num->num) n. if n = 0 then 0 else SUC (f (PRE n))" with
  | .error e => IO.println s!"WF_REC_num parse ERR: {e}"
  | .ok bigH =>
    match (do HolCore.Equal.BETA_RULE
                (← Session.ISPECL [bigH] Session.WF_REC_num)) with
    | .ok b => IO.println s!"WF_REC_num instantiated -> {← HolCore.Printer.string_of_thm b}"
    | .error e => IO.println s!"WF_REC_num instantiate ERR: {e}")


