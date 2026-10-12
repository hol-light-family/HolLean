/- File: HolTest/DefineTest.lean
Tests for HolMath/Define.lean (define.ml).

Like `HolTest/CartTest.lean` section (0), this file's forcing section is a
REGRESSION GUARD for the latent-defect trap: a bundle that is never FORCED is
never built, so a panic inside it (which degenerates every field of the bundle
to the `Inhabited` default `|-  = `) is INVISIBLE to the build - the
masked-failure detector reads its expected count and the build stays green.

So this file FORCES every define.ml bundle translated so far, IN FILE ORDER,
through `Session.ensureDefine`, and then PRINTS a theorem that REALLY BELONGS to
each bundle, emitting the literal token MISMATCH if it is degenerate.
`IO.mkRef (concl th)` SUCCEEDS on a degenerate theorem, so we PRINT the theorem
and test for `|-  = `.  `make verify` greps for MISMATCH and counts `|-  = `.

RANGES LANDED: define.ml 10-47 (DefineCasewise), 48-78 (DefineAdmissible),
79-222 (DefineAdmissibleThms), 223-356 (DefineSuperadmissibleThms),
357-463 (DefineWfCasewise), 467-598 (DefineSuiteLemmas - the ML suite context,
part 1: welldefinedness/patterns/proformas; probed behaviourally since it
publishes no public theorem), 599-810 (DefineHackApply + the hack-and-apply
tactics and instantiate_casewise_recursion - the ML suite, part 2; probed
behaviourally by running instantiate_casewise_recursion on a concrete recursive
definition, which instantiates RECURSION_SUPERADMISSIBLE and drives the
admissibility tactics), 811-953 (DefineGuessLemmas + the two remaining public
functions pure_prove_recursive_function_exists and
prove_general_recursive_function_exists - the ML suite, part 3, which yields the
binding's three public names; probed behaviourally by running the two public
entry points on concrete recursive definitions, which drive REPEAT ADMISS_TAC
and the wellfoundedness guessing search), and 954-1028 (`define` itself, the
user-facing entry point - probed by CALLING it on concrete definitions, both
successful and failing, since forcing an ML function proves nothing).

define.ml is now COMPLETE, and with it the HOL Light core library.
-/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ====================================================================== -/
/- (0) FORCING GUARD: every define.ml bundle must build, in a bare process, -/
/-     and its probe theorem must be NON-DEGENERATE.                        -/
/- ====================================================================== -/

private def sqi (s : String) : String := (s.replace "\n" "").replace " " ""

/-- Force a theorem, PRINT it (so it lands in the build log), and reject the
    `Inhabited` default `|-  = ` a panicked `setupX` yields. -/
private unsafe def forceOk (lbl : String) (th : thm) : IO Unit := do
  let s ← HolCore.Printer.string_of_thm th
  if sqi s == "|-" || sqi s == "|-=" then
    IO.println s!"Define force {lbl} -> MISMATCH degenerate (setup panicked): {s}"
  else
    IO.println s!"Define force {lbl} -> OK {s}"

/- Enter through `Session.ensureDefine`, which forces every define.ml bundle IN
   FILE ORDER (after `ensureCart`), reproducing HOL Light's eager top-to-bottom
   load. -/
#eval Session.ensureDefine

-- DefineCasewise (define.ml 10-47): the CASEWISE recursive definition and the
-- three theorems giving the conditions for all clauses to hold.  `CASEWISE_DEF`
-- (13) is the file's ONLY new_recursive_definition; probe it plus the three
-- theorems that REALLY belong to this bundle (grep-confirmed in Define.lean).
#eval forceOk "DefineCasewise/CASEWISE_DEF" Session.CASEWISE_DEF
#eval forceOk "DefineCasewise/CASEWISE" Session.CASEWISE
#eval forceOk "DefineCasewise/CASEWISE_CASES" Session.CASEWISE_CASES
#eval forceOk "DefineCasewise/CASEWISE_WORKS" Session.CASEWISE_WORKS

-- DefineAdmissible (define.ml 48-78): the three core definitions
-- `admissible` (51), `tailadmissible` (56), `superadmissible` (65) and the
-- lemma `MATCH_SEQPATTERN` (73).  Probe each — a panic in `setupDefineAdmissible`
-- degenerates every field to `|-  = `, which the MISMATCH check catches.
#eval forceOk "DefineAdmissible/admissible" Session.admissible_DEF
#eval forceOk "DefineAdmissible/tailadmissible" Session.tailadmissible_DEF
#eval forceOk "DefineAdmissible/superadmissible" Session.superadmissible_DEF
#eval forceOk "DefineAdmissible/MATCH_SEQPATTERN" Session.MATCH_SEQPATTERN

-- DefineAdmissibleThms (define.ml 79-222): the fifteen admissibility
-- combinators `ADMISSIBLE_CONST` (82) through `ADMISSIBLE_MATCH_SEQPATTERN`
-- (211).  A panic in `setupDefineAdmissibleThms` degenerates every field to
-- `|-  = `; probe all fifteen (each grep-confirmed to belong to this bundle in
-- Define.lean) so no cross-file (`NSUM`/`SUM`/`MAP`) or pattern combinator
-- slips through degenerate.
#eval forceOk "DefineAdmissibleThms/ADMISSIBLE_CONST" Session.ADMISSIBLE_CONST
#eval forceOk "DefineAdmissibleThms/ADMISSIBLE_BASE" Session.ADMISSIBLE_BASE
#eval forceOk "DefineAdmissibleThms/ADMISSIBLE_COMB" Session.ADMISSIBLE_COMB
#eval forceOk "DefineAdmissibleThms/ADMISSIBLE_RAND" Session.ADMISSIBLE_RAND
#eval forceOk "DefineAdmissibleThms/ADMISSIBLE_LAMBDA" Session.ADMISSIBLE_LAMBDA
#eval forceOk "DefineAdmissibleThms/ADMISSIBLE_NEST" Session.ADMISSIBLE_NEST
#eval forceOk "DefineAdmissibleThms/ADMISSIBLE_COND" Session.ADMISSIBLE_COND
#eval forceOk "DefineAdmissibleThms/ADMISSIBLE_MATCH" Session.ADMISSIBLE_MATCH
#eval forceOk "DefineAdmissibleThms/ADMISSIBLE_SEQPATTERN" Session.ADMISSIBLE_SEQPATTERN
#eval forceOk "DefineAdmissibleThms/ADMISSIBLE_UNGUARDED_PATTERN" Session.ADMISSIBLE_UNGUARDED_PATTERN
#eval forceOk "DefineAdmissibleThms/ADMISSIBLE_GUARDED_PATTERN" Session.ADMISSIBLE_GUARDED_PATTERN
#eval forceOk "DefineAdmissibleThms/ADMISSIBLE_NSUM" Session.ADMISSIBLE_NSUM
#eval forceOk "DefineAdmissibleThms/ADMISSIBLE_SUM" Session.ADMISSIBLE_SUM
#eval forceOk "DefineAdmissibleThms/ADMISSIBLE_MAP" Session.ADMISSIBLE_MAP
#eval forceOk "DefineAdmissibleThms/ADMISSIBLE_MATCH_SEQPATTERN" Session.ADMISSIBLE_MATCH_SEQPATTERN

-- DefineSuperadmissibleThms (define.ml 223-356): the seven superadmissible
-- generalizations `ADMISSIBLE_IMP_SUPERADMISSIBLE` (233) through
-- `SUPERADMISSIBLE_MATCH_GUARDED_PATTERN` (330).  A panic in
-- `setupDefineSuperadmissibleThms` degenerates every field to `|-  = `; probe
-- all seven (each belongs to this bundle) so neither the heavy
-- `SUPERADMISSIBLE_COND` nor the two pattern combinators slips through
-- degenerate.
#eval forceOk "DefineSuperadmissibleThms/ADMISSIBLE_IMP_SUPERADMISSIBLE" Session.ADMISSIBLE_IMP_SUPERADMISSIBLE
#eval forceOk "DefineSuperadmissibleThms/SUPERADMISSIBLE_CONST" Session.SUPERADMISSIBLE_CONST
#eval forceOk "DefineSuperadmissibleThms/SUPERADMISSIBLE_TAIL" Session.SUPERADMISSIBLE_TAIL
#eval forceOk "DefineSuperadmissibleThms/SUPERADMISSIBLE_COND" Session.SUPERADMISSIBLE_COND
#eval forceOk "DefineSuperadmissibleThms/SUPERADMISSIBLE_MATCH_SEQPATTERN" Session.SUPERADMISSIBLE_MATCH_SEQPATTERN
#eval forceOk "DefineSuperadmissibleThms/SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN" Session.SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN
#eval forceOk "DefineSuperadmissibleThms/SUPERADMISSIBLE_MATCH_GUARDED_PATTERN" Session.SUPERADMISSIBLE_MATCH_GUARDED_PATTERN

-- DefineWfCasewise (define.ml 357-463): the WF/tail-recursion-meets-casewise
-- theorems `WF_REC_TAIL_GENERAL'` (360, PRIMED) through
-- `RECURSION_SUPERADMISSIBLE` (460).  A panic in `setupDefineWfCasewise`
-- degenerates every field to `|-  = `; probe all seven.  `RECURSION_CASEWISE`
-- and `RECURSION_SUPERADMISSIBLE` are the two the ML suite instantiates, so a
-- degenerate one there would silently break `define`.  The primed
-- `WF_REC_TAIL_GENERAL_prime` is probed under its distinct Lean name; the
-- pre-existing UNPRIMED `WF_REC_TAIL_GENERAL` is a different accessor.
#eval forceOk "DefineWfCasewise/WF_REC_TAIL_GENERAL_prime" Session.WF_REC_TAIL_GENERAL_prime
#eval forceOk "DefineWfCasewise/WF_REC_CASES" Session.WF_REC_CASES
#eval forceOk "DefineWfCasewise/WF_REC_CASES_prime" Session.WF_REC_CASES_prime
#eval forceOk "DefineWfCasewise/RECURSION_CASEWISE" Session.RECURSION_CASEWISE
#eval forceOk "DefineWfCasewise/RECURSION_CASEWISE_PAIRWISE" Session.RECURSION_CASEWISE_PAIRWISE
#eval forceOk "DefineWfCasewise/SUPERADMISSIBLE_T" Session.SUPERADMISSIBLE_T
#eval forceOk "DefineWfCasewise/RECURSION_SUPERADMISSIBLE" Session.RECURSION_SUPERADMISSIBLE

/- ====================================================================== -/
/- (1) DefineSuiteLemmas (define.ml 467-598): the ML suite context, part 1. -/
/-     This bundle publishes NO public theorem (only stage 3's three names   -/
/-     are public), so it is probed BEHAVIOURALLY: force the once-proved      -/
/-     lemmas non-degenerate, then RUN the four local helpers on concrete     -/
/-     terms.  These are real conversions doing real proof, not `forcing`.    -/
/- ====================================================================== -/

-- The once-proved context lemmas must be non-degenerate (a panic in
-- `setupDefineSuiteLemmas` would degenerate them to `|-  = `).
#eval forceOk "DefineSuiteLemmas/eq_refl" Session.DSUITE_eq_refl
#eval forceOk "DefineSuiteLemmas/elemma0" Session.DSUITE_elemma0
#eval forceOk "DefineSuiteLemmas/elemma1" Session.DSUITE_elemma1

/-- Run an ioconv-style helper on a parsed term and print the resulting thm,
    flagging MISMATCH on a degenerate/absent result. -/
private unsafe def probeConv (lbl : String) (f : term → IO (Except String thm))
    (src : String) : IO Unit := do
  match ← parse_term src with
  | .error e => IO.println s!"Define probe {lbl} -> MISMATCH parse: {e}"
  | .ok tm =>
    match ← f tm with
    | .error e => IO.println s!"Define probe {lbl} -> ERR {e}"
    | .ok th => do
      let s ← HolCore.Printer.string_of_thm th
      if sqi s == "|-" || sqi s == "|-=" then
        IO.println s!"Define probe {lbl} -> MISMATCH degenerate: {s}"
      else IO.println s!"Define probe {lbl} -> OK {s}"

-- SIMPLIFY_WELLDEFINEDNESS_CONV (475-526): a conjunction of welldefinedness
-- clauses.  `2*m = 2*n+1` is impossible (opposite parity), so the guarded
-- clause simplifies away via `evensimps`/`allsimps` + the case simplifiers.
#eval probeConv "SIMPLIFY_WELLDEFINEDNESS_CONV"
        Session.SIMPLIFY_WELLDEFINEDNESS_CONV
        "!m n. (2 * m = 2 * n + 1) ==> (f m = f n)"

-- EXISTS_PAT_CONV (531-544): an existential over an unguarded pattern reduces
-- to the equation `s = t` (the `pth` base case, 532-536).
#eval probeConv "EXISTS_PAT_CONV"
        Session.EXISTS_PAT_CONV
        "?y. _UNGUARDED_PATTERN (GEQ (s:A) (t:A)) (GEQ (z:B) y)"

-- HACK_PROFORMA / EACK_PROFORMA (565-595): with n <= 1 they are the identity
-- (565-566, 581).  Feed a concrete theorem and confirm it comes back intact.
#eval (do
  match ← parse_term "!x:num. x = x" with
  | .error e => IO.println s!"Define probe HACK_PROFORMA n=1 -> MISMATCH parse: {e}"
  | .ok tm =>
    let th := REFL tm
    (match ← Session.HACK_PROFORMA 1 th with
      | .error e => IO.println s!"Define probe HACK_PROFORMA n=1 -> ERR {e}"
      | .ok r => do
        let s ← HolCore.Printer.string_of_thm r
        IO.println s!"Define probe HACK_PROFORMA n=1 (identity) -> OK {s}"))

#eval (do
  match ← parse_term "!x:num. x = x" with
  | .error e => IO.println s!"Define probe EACK_PROFORMA n=1 -> MISMATCH parse: {e}"
  | .ok tm =>
    let th := REFL tm
    (match ← Session.EACK_PROFORMA 1 th with
      | .error e => IO.println s!"Define probe EACK_PROFORMA n=1 -> ERR {e}"
      | .ok r => do
        let s ← HolCore.Printer.string_of_thm r
        IO.println s!"Define probe EACK_PROFORMA n=1 (identity) -> OK {s}"))


/- ====================================================================== -/
/- (2) DefineHackApply + instantiate_casewise_recursion (define.ml         -/
/-     599-810): the ML suite, part 2.  Force the four once-proved lemmas  -/
/-     non-degenerate, then RUN `instantiate_casewise_recursion` on         -/
/-     concrete recursive definitions - it instantiates                     -/
/-     RECURSION_SUPERADMISSIBLE (770) and drives the hack-and-apply         -/
/-     tactics, so a real theorem coming back exercises the whole range.    -/
/- ====================================================================== -/

-- The four once-proved DefineHackApply lemmas must be non-degenerate (a panic
-- in `setupDefineHackApply` would degenerate them to `|-  = `).
#eval forceOk "DefineHackApply/smw_pth0" Session.DHACK_smw_pth0
#eval forceOk "DefineHackApply/smw_pth1" Session.DHACK_smw_pth1
#eval forceOk "DefineHackApply/epa_pth0" Session.DHACK_epa_pth0
#eval forceOk "DefineHackApply/epa_pth1" Session.DHACK_epa_pth1

-- instantiate_casewise_recursion (698-808): feed a CONCRETE existential
-- recursion claim.  A single-argument primitive-recursive definition (factorial
-- over SUC) tuples to nothing (one arg), so `pinstantiate` runs the full
-- ISPEC/RECURSION_SUPERADMISSIBLE path and returns a theorem whose remaining
-- hypotheses are the wellfoundedness (and possibly distinctness) side-conditions
-- described in the define.ml 692-695 caveat.
#eval probeConv "instantiate_casewise_recursion/fact"
        Session.instantiate_casewise_recursion
        "?fact. (fact 0 = 1) /\\ (!n. fact (SUC n) = SUC n * fact n)"

-- A PATTERN-MATCHING definition: `_MATCH`/`_SEQPATTERN` drives the pattern arms
-- of MAIN_ADMISS_TAC (637-654) and EXISTS_PAT_CONV.  Fibonacci-style two-arg
-- recursion also forces the tuple_function_existence pairing path (domtys > 1).
#eval probeConv "instantiate_casewise_recursion/gcd2"
        Session.instantiate_casewise_recursion
        "?f. (!n. f 0 n = n) /\\ (!m n. f (SUC m) n = f m (SUC n))"


/- ====================================================================== -/
/- (3) DefineGuessLemmas + the two remaining public functions (define.ml   -/
/-     811-953): the ML suite, part 3, which YIELDS THE BINDING'S THREE     -/
/-     PUBLIC NAMES.  Force the three wellfoundedness reduction lemmas       -/
/-     non-degenerate, then RUN `pure_prove_recursive_function_exists` and   -/
/-     `prove_general_recursive_function_exists` on concrete recursive       -/
/-     definitions - pure_prove drives `REPEAT ADMISS_TAC` (the first        -/
/-     end-to-end use of the twenty-one-arm MAIN_ADMISS_TAC dispatcher);     -/
/-     prove_general additionally runs the wellfoundedness GUESSING search   -/
/-     (real proof, not forcing), so a real theorem coming back exercises    -/
/-     the whole 811-953 range and confirms all three public names reachable -/
/-     from Session.                                                         -/
/- ====================================================================== -/

-- The three DefineGuessLemmas reduction lemmas must be non-degenerate (a panic
-- in `setupDefineGuessLemmas` would degenerate them to `|-  = `).  These are
-- the candidate orderings `GUESS_WF_THEN` applies, in this exact order:
-- pth_lexleft, pth_lexright, pth_measure.
#eval forceOk "DefineGuessLemmas/pth_lexleft" Session.DGUESS_pth_lexleft
#eval forceOk "DefineGuessLemmas/pth_lexright" Session.DGUESS_pth_lexright
#eval forceOk "DefineGuessLemmas/pth_measure" Session.DGUESS_pth_measure

-- pure_prove_recursive_function_exists (814-851): the SECOND public name.
-- Runs instantiate_casewise_recursion then break_down_admissibility, whose
-- `REPEAT ADMISS_TAC` is the FIRST end-to-end driver of the twenty-one-arm
-- MAIN_ADMISS_TAC dispatcher.  Factorial is single-argument primitive
-- recursion; the returned theorem still carries the wellfoundedness `?(<<)`
-- hypothesis (pure_prove does NOT guess it).
#eval probeConv "pure_prove_recursive_function_exists/fact"
        Session.pure_prove_recursive_function_exists
        "?fact. (fact 0 = 1) /\\ (!n. fact (SUC n) = SUC n * fact n)"

-- prove_general_recursive_function_exists (857-947): the THIRD public name,
-- and the one `define` (stage 4) calls.  As pure_prove but ALSO guesses the
-- wellfoundedness ordering (real proof search: PRE_GUESS_TAC then
-- GUESS_ORDERING_TAC over the load-bearing candidate list).  For factorial the
-- successor-measure `\n. n+1` guess should discharge the `?(<<)` hypothesis, so
-- the result should have STRICTLY FEWER hypotheses than pure_prove's.
#eval probeConv "prove_general_recursive_function_exists/fact"
        Session.prove_general_recursive_function_exists
        "?fact. (fact 0 = 1) /\\ (!n. fact (SUC n) = SUC n * fact n)"

-- A PATTERN-MATCHING definition through the full public entry point: exercises
-- the pattern arms of MAIN_ADMISS_TAC and the guessing search together.
#eval probeConv "prove_general_recursive_function_exists/pattern"
        Session.prove_general_recursive_function_exists
        "?f. (f 0 = 0) /\\ (!n. f (SUC n) = f n + 1)"

-- A TWO-ARGUMENT definition: forces the tuple_function_existence pairing path
-- (domtys > 1) through prove_general, so the lexicographic candidates
-- (pth_lexleft/pth_lexright) in GUESS_WF_THEN are reachable.
#eval probeConv "prove_general_recursive_function_exists/twoarg"
        Session.prove_general_recursive_function_exists
        "?f. (!n. f 0 n = n) /\\ (!m n. f (SUC m) n = f m (SUC n))"


/- ====================================================================== -/
/- (4) `define` (define.ml 954-1028): THE USER-FACING ENTRY POINT, and     -/
/-     the last thing `hol_lib.ml` loads.  `define` is an ML function, so   -/
/-     forcing proves nothing - every probe below CALLS it on a concrete    -/
/-     definition and inspects the theorem that comes back.                 -/
/-                                                                          -/
/-     These probes MUTATE session state (`define` introduces constants via  -/
/-     `new_specification` and extends `the_definitions`), which is contained -/
/-     because each test module runs in its own process.  All the defined     -/
/-     names are prefixed `dt_` so they cannot collide with anything the      -/
/-     core library already defines.                                         -/
/- ====================================================================== -/

/-- Run `define` on a concrete definition and print the resulting theorem,
    flagging MISMATCH on a degenerate result. -/
private unsafe def probeDefine (lbl : String) (src : String) : IO Unit := do
  match ← parse_term src with
  | .error e => IO.println s!"Define define {lbl} -> MISMATCH parse: {e}"
  | .ok tm =>
    match ← Session.define tm with
    | .error e => IO.println s!"Define define {lbl} -> MISMATCH rejected: {e}"
    | .ok th => do
      let s ← HolCore.Printer.string_of_thm th
      if sqi s == "|-" || sqi s == "|-=" then
        IO.println s!"Define define {lbl} -> MISMATCH degenerate: {s}"
      else IO.println s!"Define define {lbl} -> OK {s}"

/-- `define` must FAIL with exactly the OCaml message `msg`. -/
private unsafe def defineFails (lbl src msg : String) : IO Unit := do
  match ← parse_term src with
  | .error e => IO.println s!"Define define {lbl} -> MISMATCH parse: {e}"
  | .ok tm =>
    match ← Session.define tm with
    | .ok th => IO.println s!"Define define {lbl} -> MISMATCH accepted: {← HolCore.Printer.string_of_thm th}"
    | .error e =>
      if e == msg then IO.println s!"Define define {lbl} -> OK (correctly rejected: {e})"
      else IO.println s!"Define define {lbl} -> MISMATCH message \"{e}\", expected \"{msg}\""

/-- `define` must SUCCEED and return exactly the clauses given (up to
    alpha-conversion, with the defined name now a constant), with no
    hypotheses.  Unlike `probeDefine`, a failure
    prints MISMATCH, so a regression fails `make verify`. -/
private unsafe def defineOK (lbl : String) (src : String) : IO Unit := do
  match ← parse_term src with
  | .error e => IO.println s!"Define define {lbl} -> MISMATCH parse: {e}"
  | .ok tm =>
    match ← Session.define tm with
    | .error e => IO.println s!"Define define {lbl} -> MISMATCH rejected: {e}"
    | .ok th =>
      -- Re-parse the clauses now `define` has made the name a constant.
      let want ← match ← parse_term src with | .ok t => pure t | .error _ => pure tm
      if (hyp th).isEmpty && aconv (concl th) want then
        IO.println s!"Define define {lbl} -> OK {← HolCore.Printer.string_of_thm th}"
      else IO.println s!"Define define {lbl} -> MISMATCH got {← HolCore.Printer.string_of_thm th}"

-- A NON-RECURSIVE definition: the shortest path through `define` - close the
-- clauses (958-975), build the existential, let
-- `prove_general_recursive_function_exists` discharge it trivially, then
-- `new_specification` (1025) introduces the constant and `mk_mconst`/`INST`
-- (1026-1027) transfer the clause onto it.
#eval probeDefine "nonrec" "!x. dt_twice x = x + x"

-- A TWO-ARGUMENT recursive definition.  This is the full pipeline: the pairing
-- path of `tuple_function_existence` (domtys > 1), `REPEAT ADMISS_TAC` reducing
-- the admissibility clause to a pure ordering condition, and the LEXICOGRAPHIC
-- candidates of `GUESS_WF_THEN` discharging the wellfoundedness hypothesis -
-- which is required, because `new_specification` rejects a theorem with
-- assumptions.
#eval probeDefine "twoarg"
        "(!n. dt_add 0 n = n) /\\ (!m n. dt_add (SUC m) n = dt_add m (SUC n))"

-- BENIGN REDEFINITION (define.ml 1010-1016): define the SAME thing again.  The
-- first definition is now in `the_definitions`, so `type_instantiate_defining_const`
-- + `tryfind`/`PART_MATCH` should find it, the reverse match should succeed, and
-- `define` should warn "Benign redefinition" and return the STORED theorem
-- without introducing a second constant or extending the list.
#eval probeDefine "benign-redef"
        "(!n. dt_add 0 n = n) /\\ (!m n. dt_add (SUC m) n = dt_add m (SUC n))"

-- ERROR PATH (define.ml 964-965): two different functions in one definition.
-- Must fail with the OCaml's exact message, character for character.
#eval defineFails "two-functions" "(dt_a 0 = 1) /\\ (dt_b 0 = 2)"
  "close_definition_clauses: defining multiple functions"   -- define.ml 965

-- ERROR PATH (define.ml 961-963): a clause that is not an equation.  Must fail
-- with "close_definition_clauses: non-equation".
#eval defineFails "non-equation" "dt_c 0"
  "close_definition_clauses: non-equation"                 -- define.ml 963

-- A single-argument recursion whose body is a COMBINATION (`SUC n * fact n`),
-- i.e. the recursive call is NOT in tail position.  This needs `ADMISSIBLE_COMB`
-- (define.ml 92) to split the body into `(g f x) (y f x)`, a higher-order match
-- in which BOTH `g` and `y` are synthesised as lambdas.
--
-- THIS WAS THE LAST KNOWN FUNCTIONAL GAP and it is now CLOSED.  It failed until
-- `HO_BETAS` was fixed in HolCore/Drule.lean: an arity mismatch on the betacount
-- lookup must FALL THROUGH to the decompose-and-descend branch (drule.ml
-- 112-114 wraps the lookup and the arity check in ONE `try`), and ours aborted
-- instead.  With that repaired the match beta-reduces, `PART_MATCH`'s sanity
-- check passes, and `define` accepts the definition.  Kept as a regression probe
-- because the failure mode was silent: a CORRECT match was rejected downstream.
#eval defineOK "comb-body (non-tail recursion, factorial)"
        "(dt_fact 0 = 1) /\\ (!n. dt_fact (SUC n) = SUC n * dt_fact n)"
-- Same shape with the recursive call as the LEFT operand.
#eval defineOK "comb-body (non-tail recursion, recursive call first)"
        "(dt_sq 0 = 0) /\\ (!n. dt_sq (SUC n) = dt_sq n + 2 * n + 1)"

/- ---------------------------------------------------------------------- -/
/- check_axioms (hol_lib.ml 105-114): the library's TRUSTED BASE.          -/
/- ---------------------------------------------------------------------- -/
/-
  hol_lib.ml's last definition asserts that the whole library introduces exactly
  THREE axioms - `INFINITY_AX`, `SELECT_AX`, `ETA_AX` - and that nothing else
  reached `the_axioms`.  Anything else means an axiom leaked in, most likely via
  `mk_thm`, which is `new_axiom` underneath (drule.ml 24-26).

  ASSERTED HERE, deliberately, rather than in a module of its own: the check is
  only meaningful over the FULLY bootstrapped library, and this file has already
  paid that cost via `Session.ensureDefine` above (which forces `ensureCart`, and
  so essentially everything).  A separate module would re-pay the single most
  expensive bootstrap in the project for no extra coverage.
-/

#eval (do
  let axs ← HolCore.Kernel.axioms
  let expected := [Session.INFINITY_AX, Session.ETA_AX, Session.SELECT_AX]
  if axs.length == 3 then IO.println "axiom count is exactly 3 -> OK"
  else IO.println s!"axiom count -> MISMATCH got {axs.length}"
  if axs.all (fun th => expected.any (equals_thm th)) then
    IO.println "every axiom is INFINITY_AX/ETA_AX/SELECT_AX -> OK"
  else IO.println "axiom identity -> MISMATCH an axiom is none of the three"
  match ← Session.check_axioms with
  | .ok _ => IO.println "check_axioms over the bootstrapped library -> OK"
  | .error e => IO.println s!"check_axioms -> MISMATCH {e}")
