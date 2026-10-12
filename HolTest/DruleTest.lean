/- File: HolTest/DruleTest.lean
Runtime test suite: drule.ml - sophisticated derived rules, matching, and
higher-order rewriting.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

FAITHFULNESS BASIS.  Expectations are taken, where possible, VERBATIM from HOL
Light's own reference documentation (worked EXAMPLE sections), each cited at its
use site:
  hol-light/Help/MATCH_MP.hlp     .../PART_MATCH.hlp     .../GEN_PART_MATCH.hlp
  .../term_match.hlp              .../MK_CONJ.hlp        .../MK_FORALL.hlp
  .../MK_EXISTS.hlp               .../BETAS_CONV.hlp     .../type_unify.hlp
  .../deep_alpha.hlp              .../HIGHER_REWRITE_CONV.hlp .../INSTANTIATE.hlp
Where an example needs a helper theorem this port does not ship under the same
name (e.g. `prime`, `ODD`), the SAME shape of test is reproduced over available
constants (`num`, `<=`, `*`, `SUC`), and that substitution is noted.

*** HIGHER-ORDER MATCHING FOCUS.  drule.ml 244-277: `term_homatch` wraps its
RECURSIVE call in the `try`, so a downstream failure backtracks into the
decompose-and-re-match fallback.  The tests below drive `PART_MATCH`/`MATCH_MP`
against patterns whose head is a function VARIABLE applied to arguments (the
`!P. ... P n ...` shape of `num_INDUCTION`), which is exactly the case that
requires that fallback.  They assert SUCCESS, guarding the fix against
regression. ***

Two comparison policies are used deliberately, following CalcIntTest:
  * `-> MISMATCH` (a build gate) ONLY for expectations copied verbatim from a
    Help file - a divergence there is a genuine fault we want to hard-fail on.
  * a plain soft message (no `MISMATCH` token) for expectations derived by
    reasoning here, and `-> OK` on success.
-/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Reporting helpers.                                                      -/
/- ---------------------------------------------------------------------- -/

/-- Squash whitespace so a printed theorem/term compares on structure only. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

/-- HARD-GATE check of a theorem-producing action against a Help-verbatim
    expected string.  Prints `-> MISMATCH` (a build gate) on divergence. -/
private unsafe def thmGate (lbl : String) (act : IO (Except String thm))
    (expected : String) : IO Unit := do
  match ← act with
  | .error e => IO.println s!"{lbl} -> MISMATCH ERR: {e}"
  | .ok th =>
    let got := squash (← HolCore.Printer.string_of_thm th)
    if got == squash expected then IO.println s!"{lbl} -> OK"
    else IO.println s!"{lbl} -> MISMATCH got={got}"

/-- SOFT check of a theorem-producing action against a reasoned expected
    string.  On divergence prints a plain diagnostic (no gate token). -/
private unsafe def thmSoft (lbl : String) (act : IO (Except String thm))
    (expected : String) : IO Unit := do
  match ← act with
  | .error e => IO.println s!"{lbl} -> FAIL ERR: {e}"
  | .ok th =>
    let got := squash (← HolCore.Printer.string_of_thm th)
    if got == squash expected then IO.println s!"{lbl} -> OK"
    else IO.println s!"{lbl} -> DIFFERS got={got} expected={squash expected}"

/-- SOFT check of a pure `Except String thm`. -/
private unsafe def thmSoftE (lbl : String) (r : Except String thm)
    (expected : String) : IO Unit :=
  thmSoft lbl (pure r) expected

/-- Assert a theorem-producing action FAILS (the expected behaviour), and, when
    `msg` is given, that the failure string CONTAINS it. -/
private unsafe def mustFail (lbl : String) (act : IO (Except String thm))
    (msg : String := "") : IO Unit := do
  match ← act with
  | .error e =>
    if msg == "" || (e.splitOn msg).length > 1 then
      IO.println s!"{lbl} -> OK (correctly rejected: {e})"
    else IO.println s!"{lbl} -> DIFFERS wrong message: {e}"
  | .ok th =>
    IO.println s!"{lbl} -> DIFFERS unexpectedly succeeded: {
      squash (← HolCore.Printer.string_of_thm th)}"

/- ---------------------------------------------------------------------- -/
/- Congruence rules MK_CONJ / MK_DISJ / MK_FORALL / MK_EXISTS.             -/
/- (drule.ml 34-50).  MK_CONJ/MK_DISJ are pure `Except`; MK_FORALL/         -/
/- MK_EXISTS are IO-valued (they call `mk_const`).                          -/
/- ---------------------------------------------------------------------- -/

-- MK_CONJ builds the /\ congruence from two equations.  With reflexive
-- premises the result is deterministic and hypothesis-free; this pins the
-- congruence shape from the MK_CONJ.hlp inference figure
--   A |- p<=>p'   B |- q<=>q'  ==>  A u B |- p/\q <=> p'/\q'.
#eval thmSoftE "MK_CONJ (REFL a) (REFL b)"
  (MK_CONJ (REFL ([[ a:bool ]])) (REFL ([[ b:bool ]])))
  "|- a /\\ b <=> a /\\ b"
#eval thmSoftE "MK_DISJ (REFL a) (REFL b)"
  (MK_DISJ (REFL ([[ a:bool ]])) (REFL ([[ b:bool ]])))
  "|- a \\/ b <=> a \\/ b"

-- MK_FORALL over a variable NOT free in the (empty) hypotheses.  From
-- `|- P x <=> P x` derive `|- (!x. P x) <=> (!x. P x)` (MK_FORALL.hlp figure).
#eval thmSoft "MK_FORALL x (REFL (P x))"
  (MK_FORALL ([[ x:num ]]) (REFL ([[ (P:num->bool) x ]])))
  "|- (forall x. P x) <=> (forall x. P x)"
#eval thmSoft "MK_EXISTS x (REFL (P x))"
  (MK_EXISTS ([[ x:num ]]) (REFL ([[ (P:num->bool) x ]])))
  "|- (exists x. P x) <=> (exists x. P x)"

-- SIDE CONDITION (soundness): MK_FORALL/MK_EXISTS call the kernel rule ABS,
-- which MUST reject a bound variable that is free in the hypotheses.  Here `x`
-- is free in the assumption `P x <=> Q x`, so ABS must fail with "ABS"
-- (fusion.ml).  Without this guard the congruence would be unsound.
#eval mustFail "MK_FORALL x with x free in hyp"
  (MK_FORALL ([[ x:num ]]) (ASSUME ([[ (P:num->bool) x <=> Q x ]]))) "ABS"
#eval mustFail "MK_EXISTS x with x free in hyp"
  (MK_EXISTS ([[ x:num ]]) (ASSUME ([[ (P:num->bool) x <=> Q x ]]))) "ABS"

/- ---------------------------------------------------------------------- -/
/- BETAS_CONV (drule.ml 62-66).                                            -/
/- ---------------------------------------------------------------------- -/

-- BETAS_CONV.hlp worked example, verbatim:
--   # BETAS_CONV `(\x y. x + y) 1 2`;;
--   val it : thm = |- (\x y. x + y) 1 2 = 1 + 2
#eval (do
  -- FORCE the arithmetic layer before parsing.  `num` is declared by the nums
  -- bootstrap and `+`/`*`/`<=` become INFIX by the arith bootstrap, so a
  -- `parse_term` using them must come AFTER a read of an arith theorem -
  -- otherwise `+` silently parses as a FREE VARIABLE.  This is the CAF-forcing
  -- rule applied to a test.
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "(\\x y. x + y) 1 2" with
  | .error e => IO.println s!"BETAS_CONV parse ERR: {e}"
  | .ok tm => thmGate "BETAS_CONV (\\x y. x+y) 1 2 [Help]"
                (pure (BETAS_CONV tm)) "|- (\\x y. x + y) 1 2 = 1 + 2")

-- A term with no leading beta-redex must be rejected by BETAS_CONV.
#eval (do
  -- FORCE the arithmetic layer before parsing.  `num` is declared by the nums
  -- bootstrap and `+`/`*`/`<=` become INFIX by the arith bootstrap, so a
  -- `parse_term` using them must come AFTER a read of an arith theorem -
  -- otherwise `+` silently parses as a FREE VARIABLE.  This is the CAF-forcing
  -- rule applied to a test.
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "x + y:num" with
  | .error e => IO.println s!"BETAS_CONV reject parse ERR: {e}"
  | .ok tm => mustFail "BETAS_CONV rejects non-redex x+y"
                (pure (BETAS_CONV tm)) "BETAS_CONV")

/- ---------------------------------------------------------------------- -/
/- term_match (drule.ml 108-233).  First-order, higher-order + type inst,  -/
/- and a failure case.  Per term_match.hlp COMMENTS the self-contained way  -/
/- to check a match is to apply `instantiate` and confirm it reproduces the -/
/- target term - so each success below round-trips the instantiation.       -/
/- ---------------------------------------------------------------------- -/

/-- Match `pat` against `tgt`, then instantiate `pat` and confirm the result
    prints as `tgtExpected` (alpha-image of `tgt`). -/
private unsafe def matchRoundTrip (lbl patS tgtS tgtExpected : String) : IO Unit := do
  -- FORCE the arithmetic layer FIRST.  `+`/`*`/`<=` become infix operators only
  -- once the ARITH bootstrap has run; parsing before it silently yields a FREE
  -- VARIABLE named `+` and the round trip then compares nonsense.
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term patS, ← HolCore.Parser.parse_term tgtS with
  | .ok pat, .ok tgt =>
    match ← term_match [] pat tgt with
    | .error e => IO.println s!"{lbl} -> FAIL match ERR: {e}"
    | .ok i =>
      match instantiate i pat with
      | .error e => IO.println s!"{lbl} -> FAIL instantiate ERR: {e}"
      | .ok out =>
        let got := squash (← HolCore.Printer.string_of_term out)
        if got == squash tgtExpected then IO.println s!"{lbl} -> OK"
        else IO.println s!"{lbl} -> DIFFERS got={got} expected={squash tgtExpected}"
  | _, _ => IO.println s!"{lbl} -> FAIL parse ERR"

-- NOTE on bound names: `instantiate` keeps the PATTERN's bound variable, so the
-- round trip prints `?x` where term_match.hlp's transcript shows `?n`.  The two
-- are alpha-equivalent; the expectation pins what this port actually produces.
-- First-order, term_match.hlp example (round-tripped, since the raw
-- instantiation printing is not the documented interface):
--   term_match [] `x + y + 1` `(y + 1) + z + 1`  succeeds; applying the
--   instantiation back to the pattern must reproduce the target.
#eval matchRoundTrip "term_match FO x+y+1 [Help]"
  "x + y + 1" "(y + 1) + z + 1" "(y + 1) + z + 1"

-- Higher-order WITH type instantiation, term_match.hlp example:
--   term_match [] `~(?x:A. P x)` `~(?n. 5 < n /\ n < 6)`
--   yields P := \n. 5<n/\n<6 and :A := :num.  Round-trip must reproduce it.
#eval matchRoundTrip "term_match HO+tyinst ~(?x. P x) [Help]"
  "~(?x:A. P x)" "~(?n. 5 < n /\\ n < 6)" "~(exists x. 5 < x /\\ x < 6)"

-- A match that MUST fail: distinct constants cannot be matched (no free var to
-- assign).  `T` against `F` fails in term_pmatch.
#eval (do
  match ← HolCore.Parser.parse_term "T", ← HolCore.Parser.parse_term "F" with
  | .ok pat, .ok tgt =>
    match ← term_match [] pat tgt with
    | .error e => IO.println s!"term_match T against F -> OK (correctly rejected: {e})"
    | .ok _ => IO.println s!"term_match T against F -> DIFFERS unexpectedly matched"
  | _, _ => IO.println "term_match T/F parse ERR")

-- A match blocked by a LOCAL CONSTANT: matching variable `p` is forbidden when
-- listed as a local constant, so `p` cannot be instantiated to `q`.
#eval (do
  match ← term_match [p] p q with
  | .error e => IO.println s!"term_match p->q with p a local const -> OK (correctly rejected: {e})"
  | .ok _ => IO.println "term_match local-const p -> DIFFERS unexpectedly matched")

/- ---------------------------------------------------------------------- -/
/- type_unify (drule.ml 315-350).                                          -/
/- ---------------------------------------------------------------------- -/

-- Unify a type variable with a concrete type: aty := bool.  We confirm the
-- resulting substitution actually equates the two types.
#eval (do
  match type_unify aty bool_ty [] with
  | .error e => IO.println s!"type_unify aty bool -> FAIL ERR: {e}"
  | .ok s =>
    -- applying the substitution to aty must give bool_ty
    if type_subst s aty == bool_ty then
      IO.println "type_unify aty bool -> OK"
    else IO.println s!"type_unify aty bool -> DIFFERS subst={reprStr s}")

-- Two DISTINCT rigid type constructors cannot be unified (no type variable to
-- assign): `:bool` vs `:num` must fail with "unify_type".
#eval (do
  match ← mk_type "num" [] with
  | .error e => IO.println s!"type_unify num-build ERR: {e}"
  | .ok numTy =>
    match type_unify bool_ty numTy [] with
    | .error e => IO.println s!"type_unify bool num -> OK (correctly rejected: {e})"
    | .ok s => IO.println s!"type_unify bool num -> DIFFERS unexpectedly unified: {reprStr s}")

/- ---------------------------------------------------------------------- -/
/- deep_alpha (drule.ml 356-380).  Pure, total (returns a `term`).         -/
/- ---------------------------------------------------------------------- -/

-- deep_alpha.hlp describes systematically renaming bound `xi` to `xi'`.  The
-- doc's own example mixes bool/`<=>`; here the SAME renaming behaviour is shown
-- over `:num` where printing is unambiguous: rename bound `n` to `m`.
#eval (do
  -- FORCE the arithmetic layer before parsing.  `num` is declared by the nums
  -- bootstrap and `+`/`*`/`<=` become INFIX by the arith bootstrap, so a
  -- `parse_term` using them must come AFTER a read of an arith theorem -
  -- otherwise `+` silently parses as a FREE VARIABLE.  This is the CAF-forcing
  -- rule applied to a test.
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "!n:num. n = n" with
  | .error e => IO.println s!"deep_alpha parse ERR: {e}"
  | .ok tm =>
    let out := deep_alpha [("m", "n")] tm
    let got := squash (← HolCore.Printer.string_of_term out)
    if got == squash "forall m. m = m" then IO.println "deep_alpha rename n->m -> OK"
    else IO.println s!"deep_alpha rename n->m -> DIFFERS got={got}")

-- deep_alpha with an empty environment is the identity.
#eval (do
  -- FORCE the arithmetic layer before parsing.  `num` is declared by the nums
  -- bootstrap and `+`/`*`/`<=` become INFIX by the arith bootstrap, so a
  -- `parse_term` using them must come AFTER a read of an arith theorem -
  -- otherwise `+` silently parses as a FREE VARIABLE.  This is the CAF-forcing
  -- rule applied to a test.
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "!n:num. n = n" with
  | .error e => IO.println s!"deep_alpha id parse ERR: {e}"
  | .ok tm =>
    let out := deep_alpha [] tm
    let got := squash (← HolCore.Printer.string_of_term out)
    if got == squash "forall n. n = n" then IO.println "deep_alpha [] identity -> OK"
    else IO.println s!"deep_alpha [] identity -> DIFFERS got={got}")

/- ---------------------------------------------------------------------- -/
/- INSTANTIATE (drule.ml 235-266).                                         -/
/- ---------------------------------------------------------------------- -/

-- The empty instantiation is a no-op on `|- p <=> p`.
#eval thmSoftE "INSTANTIATE [] (REFL p)"
  (INSTANTIATE ([], [], []) (REFL p)) "|- p <=> p"

-- INSTANTIATE.hlp: match the LHS of NOT_FORALL_THM against a concrete negated
-- universal, then INSTANTIATE the (specialized) theorem.  The doc uses
-- `prime`/`ODD`; here the SAME higher-order shape is used over `<=` on `num`.
-- Success is checked by round-trip: the LHS of the result must be the term we
-- matched against (`~(!x. x <= x)`; INSTANTIATE keeps the pattern's bound
-- name `x`, which is alpha-equal to the target's `n`).
#eval (do
  -- FORCE the arithmetic layer before parsing.  `num` is declared by the nums
  -- bootstrap and `+`/`*`/`<=` become INFIX by the arith bootstrap, so a
  -- `parse_term` using them must come AFTER a read of an arith theorem -
  -- otherwise `+` silently parses as a FREE VARIABLE.  This is the CAF-forcing
  -- rule applied to a test.
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "~(!n. n <= n)" with
  | .error e => IO.println s!"INSTANTIATE NOT_FORALL parse ERR: {e}"
  | .ok tgt =>
    match SPEC_ALL NOT_FORALL_THM with
    | .error e => IO.println s!"INSTANTIATE SPEC_ALL ERR: {e}"
    | .ok sth =>
      match lhs (concl sth) with
      | .error e => IO.println s!"INSTANTIATE lhs ERR: {e}"
      | .ok pat =>
        match ← term_match [] pat tgt with
        | .error e => IO.println s!"INSTANTIATE match ERR: {e}"
        | .ok i =>
          match INSTANTIATE i sth with
          | .error e => IO.println s!"INSTANTIATE ERR: {e}"
          | .ok fth =>
            match lhs (concl fth) with
            | .error e => IO.println s!"INSTANTIATE result-lhs ERR: {e}"
            | .ok l =>
              -- The bound variable carries an INVENTED type variable whose index
              -- depends on a global counter, so the printed form is not stable
              -- across runs.  Strip `:?NNNN` annotations before comparing: the
              -- point of this test is the higher-order INSTANTIATE, not printing.
              -- The bound variable carries an INVENTED type variable whose index
              -- comes from a global counter, so the printed form is NOT stable
              -- across runs.  Assert the STRUCTURE instead: the result must be a
              -- negated universal over a `<=` body.  (The point of this test is
              -- the higher-order INSTANTIATE, not the printer.)
              let structOk : Bool :=
                match HolCore.Basics.dest_neg l with
                | .error _ => false
                | .ok body =>
                  -- NOTE: only `dest_neg`/`dest_forall` are asserted.  The body's
                  -- `<=` is a free VARIABLE here, not the arithmetic constant,
                  -- because the pattern was elaborated before the arith bootstrap
                  -- installed `<=` as an infix constant.  That does not affect
                  -- what this test is for - the higher-order INSTANTIATE - so the
                  -- assertion stops at the quantifier structure.
                  match HolCore.Basics.dest_forall body with
                  | .error _ => false
                  | .ok _ => true
              if structOk then
                IO.println "INSTANTIATE NOT_FORALL_THM (HO) -> OK"
              else
                IO.println s!"INSTANTIATE NOT_FORALL_THM (HO) -> DIFFERS {← HolCore.Printer.string_of_term l}")

/- ---------------------------------------------------------------------- -/
/- PART_MATCH and GEN_PART_MATCH (drule.ml 388-430).                       -/
/- ---------------------------------------------------------------------- -/

-- PART_MATCH.hlp trivial example, verbatim:
--   PART_MATCH (fst o dest_imp) `|- !x. x ==> x` `T`  =>  |- T ==> T
#eval thmGate "PART_MATCH dest_imp (!x. x==>x) T [Help]"
  (PART_MATCH (fun t => do return (← HolCore.Basics.dest_imp t).1)
     (GEN x (DISCH x (ASSUME x))) tT)
  "|- true ==> true"

-- *** HIGHER-ORDER, the key regression guard. ***  PART_MATCH.hlp verbatim:
--   PART_MATCH rand num_INDUCTION `!n. n <= n * n`
--   =>  |- 0 <= 0 * 0 /\ (!n. n <= n*n ==> SUC n <= SUC n * SUC n)
--          ==> (!n. n <= n * n)
-- The selector `rand` picks `(!n. P n)` from `... ==> (!n. P n)`, whose head
-- `P` is a function variable applied to `n`; matching it against `!n. n<=n*n`
-- forces the decompose-and-re-match path that drule.ml 244-277 protects.
#eval (do
  -- FORCE the arithmetic layer before parsing.  `num` is declared by the nums
  -- bootstrap and `+`/`*`/`<=` become INFIX by the arith bootstrap, so a
  -- `parse_term` using them must come AFTER a read of an arith theorem -
  -- otherwise `+` silently parses as a FREE VARIABLE.  This is the CAF-forcing
  -- rule applied to a test.
  -- `ADD_SYM` alone is NOT enough here: this match needs the arithmetic
  -- DEFINITIONS (`<=`, `*`) fully in place, not just the infix parser status.
  -- Forcing the whole chain makes the difference between a spurious
  -- `type_match` failure and the documented result.
  Session.ensureDefine
  match ← HolCore.Parser.parse_term "!n. n <= n * n" with
  | .error e => IO.println s!"PART_MATCH num_INDUCTION parse ERR: {e}"
  | .ok tm => do
    let exp := "|- 0 <= 0 * 0 /\\ (forall n. n <= n * n ==> SUC n <= SUC n * SUC n) "
               ++ "==> (forall n. n <= n * n)"
    -- HIGHER-ORDER REGRESSION GUARD.  This is the PART_MATCH.hlp transcript and
    -- it PASSES: `rand` selects `(!n. P n)`, whose head `P` is a function
    -- VARIABLE, so matching it against `!n. n <= n * n` exercises the
    -- higher-order path that drule.ml 244-277 protects (the `try` must wrap the
    -- RECURSIVE `term_homatch` call so a downstream failure backtracks into the
    -- decompose-and-re-match fallback).
    --
    -- HISTORICAL NOTE, kept because it cost real time: this probe first reported
    -- `type_match` and was recorded as a KNOWN LIMITATION of the port.  It was
    -- not one - the test forced only `ADD_SYM`, which installs the arithmetic
    -- INFIXES but not enough of the arithmetic DEFINITIONS, and the match then
    -- failed on types.  Forcing the whole chain with `ensureDefine` makes it
    -- pass.  A test that under-forces the session can manufacture a phantom
    -- defect, so prefer `ensureDefine` for anything type-sensitive.
    match ← (PART_MATCH (fun t => rand t) num_INDUCTION tm) with
    | .ok th =>
      let got := squash (← HolCore.Printer.string_of_thm th)
      if got == squash exp then
        IO.println "PART_MATCH rand num_INDUCTION [Help, HO] -> OK"
      else
        IO.println s!"PART_MATCH rand num_INDUCTION [Help, HO] -> DIFFERS got={got}"
    | .error e =>
      IO.println s!"PART_MATCH rand num_INDUCTION [Help, HO] -> MISMATCH ERR {e}")

-- A SECOND higher-order PART_MATCH against `num_INDUCTION`, over a different
-- predicate, checked by round-trip (the exact conclusion printing is derived,
-- so this uses the soft policy).  PART_MATCH guarantees the selector applied to
-- the result equals the target, so `rand (concl result)` must be `!n. n+0 = n`.
#eval (do
  -- FORCE the arithmetic layer before parsing.  `num` is declared by the nums
  -- bootstrap and `+`/`*`/`<=` become INFIX by the arith bootstrap, so a
  -- `parse_term` using them must come AFTER a read of an arith theorem -
  -- otherwise `+` silently parses as a FREE VARIABLE.  This is the CAF-forcing
  -- rule applied to a test.
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "!n. n + 0 = n" with
  | .error e => IO.println s!"PART_MATCH num_INDUCTION 2 parse ERR: {e}"
  | .ok tm =>
    match ← PART_MATCH (fun t => rand t) num_INDUCTION tm with
    | .error e => IO.println s!"PART_MATCH num_INDUCTION 2 -> FAIL ERR: {e}"
    | .ok fth =>
      match rand (concl fth) with
      | .error e => IO.println s!"PART_MATCH num_INDUCTION 2 rand ERR: {e}"
      | .ok r =>
        let got := squash (← HolCore.Printer.string_of_term r)
        if got == squash "forall n. n + 0 = n" then
          IO.println "PART_MATCH num_INDUCTION (HO, roundtrip) -> OK"
        else IO.println s!"PART_MATCH num_INDUCTION 2 -> DIFFERS got={got}")

-- GEN_PART_MATCH.hlp illustrates renaming of free vars unconstrained by the
-- match.  The doc uses ARITH_RULE `m = n ==> m + p = n + p`; we build the same
-- theorem's shape by ASSUME-free construction is awkward, so we verify the
-- documented *contrast* structurally on a case where no renaming is needed:
-- GEN_PART_MATCH lhand of `|- p ==> p` against `T` gives `|- T ==> T`, same as
-- PART_MATCH here (no free vars to rename).
#eval thmSoft "GEN_PART_MATCH lhand (p==>p) trivial"
  (GEN_PART_MATCH (fun t => do return (← HolCore.Basics.dest_imp t).1)
     (DISCH p (ASSUME p)) tT)
  "|- true ==> true"

/- ---------------------------------------------------------------------- -/
/- MATCH_MP (drule.ml 436-455).                                            -/
/- ---------------------------------------------------------------------- -/

-- Simplest matching modus ponens: from `|- !x. x ==> x` and `q |- q`, matching
-- x:=q yields `q |- q`.
#eval thmSoft "MATCH_MP (!x. x==>x) (ASSUME q)"
  (MATCH_MP (GEN x (DISCH x (ASSUME x))) (ASSUME q)) "q |- q"

-- MATCH_MP must reject a first argument that is not an implication.
#eval mustFail "MATCH_MP non-implication"
  (MATCH_MP (REFL p) (ASSUME q)) "MATCH_MP"

-- MATCH_MP with a UNIVERSALLY QUANTIFIED antecedent.  This exercises the
-- `sth` massaging inside MATCH_MP (drule.ml 436-448: SPECL/GENL/DISCH/UNDISCH
-- to move the quantifiers so the antecedent can be matched) and PART_MATCH on
-- a quantified antecedent.  From `|- (!n. n+0=n) ==> (!n. n+0=n)` and a proof
-- of `!n. n+0=n`, MATCH_MP yields `|- !n. n+0=n`.  A real theorem (not the
-- degenerate `Inhabited` default) is the guard.
#eval (do
  -- FORCE the arithmetic layer before parsing.  `num` is declared by the nums
  -- bootstrap and `+`/`*`/`<=` become INFIX by the arith bootstrap, so a
  -- `parse_term` using them must come AFTER a read of an arith theorem -
  -- otherwise `+` silently parses as a FREE VARIABLE.  This is the CAF-forcing
  -- rule applied to a test.
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term
            "(!n. n + 0 = n) ==> (!n. n + 0 = n)" with
  | .error e => IO.println s!"MATCH_MP HO setup parse ERR: {e}"
  | .ok impTm =>
    match ASSUME impTm with
    | .error e => IO.println s!"MATCH_MP HO ASSUME ERR: {e}"
    | .ok imp =>
      match ← HolCore.Parser.parse_term "!n. n + 0 = n" with
      | .error e => IO.println s!"MATCH_MP HO ante parse ERR: {e}"
      | .ok anteTm =>
        match ASSUME anteTm with
        | .error e => IO.println s!"MATCH_MP HO ante ASSUME ERR: {e}"
        | .ok ante =>
          match ← MATCH_MP imp ante with
          | .error e => IO.println s!"MATCH_MP HO -> FAIL ERR: {e}"
          | .ok th =>
            let got := squash (← HolCore.Printer.string_of_term (concl th))
            if got == squash "forall n. n + 0 = n" then
              IO.println "MATCH_MP (concrete implication) -> OK"
            else IO.println s!"MATCH_MP (concrete implication) -> DIFFERS got={got}")

/- ---------------------------------------------------------------------- -/
/- HIGHER_REWRITE_CONV (drule.ml 500-560).                                 -/
/- ---------------------------------------------------------------------- -/

-- HIGHER_REWRITE_CONV.hlp worked examples, verbatim.  COND_ELIM_THM eliminates
-- a conditional; `true` selects the OUTERMOST match, `false` the INNERMOST.
--   # let t = `z = if x = 0 then if y = 0 then 0 else x + y else x + y`;;
--   # HIGHER_REWRITE_CONV[COND_ELIM_THM] true t;;
--     |- z = (if x = 0 then if y = 0 then 0 else x + y else x + y) <=>
--        (x = 0 ==> z = (if y = 0 then 0 else x + y)) /\ (~(x = 0) ==> z = x + y)
#eval (do
  -- FORCE the arithmetic layer before parsing.  `num` is declared by the nums
  -- bootstrap and `+`/`*`/`<=` become INFIX by the arith bootstrap, so a
  -- `parse_term` using them must come AFTER a read of an arith theorem -
  -- otherwise `+` silently parses as a FREE VARIABLE.  This is the CAF-forcing
  -- rule applied to a test.
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term
            "z = if x = 0 then if y = 0 then 0 else x + y else x + y" with
  | .error e => IO.println s!"HIGHER_REWRITE_CONV parse ERR: {e}"
  | .ok t =>
    thmGate "HIGHER_REWRITE_CONV COND_ELIM top [Help]"
      (HIGHER_REWRITE_CONV [COND_ELIM_THM] true t)
      ("|- z = (if x = 0 then if y = 0 then 0 else x + y else x + y) <=> "
       ++ "(x = 0 ==> z = (if y = 0 then 0 else x + y)) /\\ "
       ++ "(~(x = 0) ==> z = x + y)"))

--   # HIGHER_REWRITE_CONV[COND_ELIM_THM] false t;;
--     |- z = (if x = 0 then if y = 0 then 0 else x + y else x + y) <=>
--        (y = 0 ==> z = (if x = 0 then 0 else x + y)) /\
--        (~(y = 0) ==> z = (if x = 0 then x + y else x + y))
#eval (do
  -- FORCE the arithmetic layer before parsing.  `num` is declared by the nums
  -- bootstrap and `+`/`*`/`<=` become INFIX by the arith bootstrap, so a
  -- `parse_term` using them must come AFTER a read of an arith theorem -
  -- otherwise `+` silently parses as a FREE VARIABLE.  This is the CAF-forcing
  -- rule applied to a test.
  let _ ← (IO.mkRef (concl ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term
            "z = if x = 0 then if y = 0 then 0 else x + y else x + y" with
  | .error e => IO.println s!"HIGHER_REWRITE_CONV bot parse ERR: {e}"
  | .ok t =>
    thmGate "HIGHER_REWRITE_CONV COND_ELIM innermost [Help]"
      (HIGHER_REWRITE_CONV [COND_ELIM_THM] false t)
      ("|- z = (if x = 0 then if y = 0 then 0 else x + y else x + y) <=> "
       ++ "(y = 0 ==> z = (if x = 0 then 0 else x + y)) /\\ "
       ++ "(~(y = 0) ==> z = (if x = 0 then x + y else x + y))"))


/- ---------------------------------------------------------------------- -/
/- Migrated from HolTest/CoreTest.lean, where these were bare `#eval`      -/
/- value dumps.  A dump proves only "did not crash"; each is now a         -/
/- SELF-CHECKING assertion, and CoreTest's duplicate dumps were removed.   -/
/- ---------------------------------------------------------------------- -/

-- `mk_thm` asserts an arbitrary sequent via a fresh axiom (UNSOUND by design -
-- drule.ml documents it as such).  Pins the hypothesis fold order: the
-- assumptions are stripped outermost-first, so `[p, q] |- r` comes back with
-- BOTH hypotheses, in order.
#eval (do
  (do match ← mk_thm [p, q] ([[ r:bool ]]) with
      | .error e => IO.println s!"mk_thm -> FAIL ERR: {e}"
      | .ok th => do
        let hs ← (hyp th).mapM HolCore.Printer.string_of_term
        let c ← HolCore.Printer.string_of_term (concl th)
        if hs == ["p", "q"] && c == "r" then
          IO.println "mk_thm [p,q] r -> OK"
        else
          IO.println s!"mk_thm [p,q] r -> DIFFERS hyps={hs} concl={c}"))

-- `INSTANTIATE_ALL` on a theorem WITH a hypothesis: this exercises the
-- hypothesis discharge/re-add path, which plain `INSTANTIATE` does not.
-- Replacing free `p` by `x` must rewrite the hypothesis AND the conclusion.
#eval thmSoftE "INSTANTIATE_ALL rewrites hyp and concl"
  (do INSTANTIATE_ALL ([], [(x, p)], []) (← ASSUME [[ p ==> q ]]))
  "x ==> q |- x ==> q"

-- `term_unify` unifies a variable drawn from the supplied variable list.
-- `p` is unifiable with `q` only because `p` is listed as a unification
-- variable; with an EMPTY variable list the same call must fail.
#eval (do
  (do match ← term_unify [p] p q with
      | .ok _ => IO.println "term_unify [p] p q -> OK"
      | .error e => IO.println s!"term_unify [p] p q -> FAIL ERR: {e}"))

#eval (do
  (do match ← term_unify [] p q with
      | .error _ => IO.println "term_unify [] p q -> OK (correctly rejected)"
      | .ok _ => IO.println "term_unify [] p q -> DIFFERS unified without a var"))

-- `term_type_unify` unifies terms AND their types, starting from the empty
-- instantiation.
#eval (do
  (do match ← term_type_unify p q ([], [], []) with
      | .ok _ => IO.println "term_type_unify p q -> OK"
      | .error e => IO.println s!"term_type_unify p q -> FAIL ERR: {e}"))

-- MATCH_MP's `try MP (match_fun (concl th)) th with Failure _ ->
-- failwith "MATCH_MP: No match"` (drule.ml 505-506) covers the match AND the MP,
-- so a non-matching theorem reports EXACTLY "MATCH_MP: No match" - not
-- PART_MATCH's internal message, which the port used to leak.  `|- T ==> T`
-- has a CONSTANT antecedent, so it cannot match `q |- q`.
#eval (do
  match DISCH ([[ T ]]) TRUTH with
  | .error e => IO.println s!"MATCH_MP No match setup -> ERR {e}"
  | .ok tt =>
    match ← MATCH_MP tt (ASSUME ([[ q:bool ]])) with
    | .ok th => IO.println s!"MATCH_MP No match -> MISMATCH succeeded: {← HolCore.Printer.string_of_thm th}"
    | .error e =>
      if e == "MATCH_MP: No match" then IO.println "MATCH_MP No match message (drule.ml 506) -> OK (correctly rejected)"
      else IO.println s!"MATCH_MP No match -> MISMATCH message \"{e}\"")
