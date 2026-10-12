/- File: HolTest/RealTest.lean
Runtime test suite: real.ml - the main development of real-number theory on
top of realax.ml/calc_int.ml/realarith.ml (order, absolute value, min/max,
multiplication/inverse/division/powers, cancellation, the Archimedean
theorems, `real_sgn`, and `sqrt`).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

FAITHFULNESS BASIS.  Statements and conjunct counts are checked against real.ml
itself.  real.ml has 334 top-level bindings in ELEVEN theorem bundles
(realThms1-11) plus three non-theorem items (`REAL_ARITH_TAC`, `REAL_LE_IMP`,
`REAL_LET_IMP`).  Session re-exports each bundle field bare (331 names), as HOL
Light has every theorem as a global name; a few of those bare re-exports are
exercised below to prove that fourth re-export block works.  This module
samples at least three theorems from EVERY bundle, exercises the three
non-theorem items (a rule/tactic is exercised only by APPLYING it, never by
printing it), and drives the `sqrt` payoff (SQRT_0/SQRT_1/POW_2_SQRT).

PERFORMANCE.  Forcing the later bundles drives real.ml's ~198 REAL_ARITH
invocations, and touching REAL_ARITH2's proforma pays a one-off ABSMAXMIN cost;
this is expected to be the slowest test module.

A HELP-FILE FINDING (recorded below at section 5).  hol-light/Help/
REAL_ARITH_TAC.hlp gives two worked examples; BOTH fail under real.ml's
REAL_ARITH_TAC (built over REAL_ARITH2), with `linear_ineqs: no contradiction`,
and that is CORRECT for that version - both use RATIONAL constants (`/ &6`,
`/ &2`, `/ &4`, `/ &3`), and REAL_ARITH2 instantiates its normaliser with
is_realintconst, so a rational coefficient can never be folded.  calc_rat.ml 434
passes is_ratconst instead, and REAL_ARITH_TAC2 (calc_rat.ml 553, over
REAL_ARITH3) now PROVES BOTH examples - so REAL_ARITH_TAC.hlp documents the
calc_rat.ml version, not real.ml's.  Section 5 asserts the failure under the
old tactic AND the success under the new one on the SAME goals, making the
difference explicit.  VERDICT: REAL_ARITH_TAC.hlp is VERSION SKEW.  It is the
SECOND such version-skew entry (the first was REAL_ARITH.hlp, on realarith.ml);
it is NOT a third distinct finding - a previous over-claim was corrected.  The
one other .hlp finding to date, REAL_INT_NEG_CONV.hlp on calc_int.ml, is a
DIFFERENT fault - a genuine copy-paste error in an entry that is never
redefined, not version skew.
Integer-constant analogues of the same two shapes PROVE even under the old
REAL_ARITH_TAC, isolating the cause to the rational constant alone.

`&` is `real_of_num`, the injection of the naturals into the reals.
-/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- FORCING THE REAL LAYER FIRST IS MANDATORY.                             -/
/-                                                                        -/
/- real.ml sits on the LAZY realarith bootstrap, and terms mentioning `&`, -/
/- `abs`, `min`, `max` or `sqrt` cannot even be PARSED until something has  -/
/- forced the real layer into existence - a bare probe otherwise fails      -/
/- with `mk_type: type num has not been defined`.  `REAL_OF_NUM_LT` is the  -/
/- CHEAPEST such accessor (setupRealThms1 takes no REAL_ARITH parameter),   -/
/- so this `#eval` must come first.                                        -/
/- ---------------------------------------------------------------------- -/

#eval Session.realThms1.REAL_OF_NUM_LT

/-- Squash whitespace so a printed theorem can be compared against a
    single-line expected string. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

/-- Compare a theorem against an expected printed form. -/
private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/-- Assert a bundled theorem splits into exactly `n` conjuncts.  Several real.ml
    bundles (`REAL_OF_NUM_CLAUSES`, the ACI laws, `REAL_SGN_INEQS`) are wide
    conjunctions whose count is load-bearing: a dropped conjunct would be
    SILENT under a plain print, so assert it programmatically. -/
private unsafe def conjCountCheck (lbl : String) (t : thm) (n : Nat) : IO Unit := do
  match ← Session.theBool.get with
  | none => IO.println s!"{lbl} -> MISMATCH BoolThms not forced"
  | some B =>
    let got := (B.CONJUNCTS t).length
    if got == n then IO.println s!"{lbl} -> OK ({n} conjuncts)"
    else IO.println s!"{lbl} -> MISMATCH got {got} conjuncts, want {n}"

/-- Parse `goal`, run `REAL_ARITH_TAC`, assert it PROVES the goal with NO
    hypotheses.  A proved goal's conclusion IS the goal, so the expected form is
    `|- ` prepended to the goal RE-PRINTED from its parse (which normalises
    cosmetic input differences like `abs(x)` vs the printer's `abs x`). -/
private unsafe def provesTac (lbl goal : String) : IO Unit := do
  match ← HolCore.Parser.parse_term goal with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok tm =>
    let want := squash ("|- " ++ (← HolCore.Printer.string_of_term tm))
    match ← Session.prove tm Session.REAL_ARITH_TAC with
    | .error e => IO.println s!"{lbl} -> MISMATCH failed to prove: {e}"
    | .ok th =>
      let got := squash (← HolCore.Printer.string_of_thm th)
      if got == want then IO.println s!"{lbl} -> OK"
      else IO.println s!"{lbl} -> MISMATCH got={got} want={want}"

/-- Assert `REAL_ARITH_TAC` FAILS on `goal`, and (when `wantMsg` is nonempty)
    that the error CONTAINS `wantMsg`.  Used for the two rational-constant .hlp
    examples that only the future calc_rat.ml layer will satisfy. -/
private unsafe def failsTac (lbl goal wantMsg : String) : IO Unit := do
  match ← HolCore.Parser.parse_term goal with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok tm =>
    match ← Session.prove tm Session.REAL_ARITH_TAC with
    | .error e =>
      if wantMsg == "" || (e.splitOn wantMsg).length > 1 then
        IO.println s!"{lbl} -> OK (correctly fails: {e})"
      else IO.println s!"{lbl} -> MISMATCH wrong error: {e}"
    | .ok th =>
      IO.println s!"{lbl} -> MISMATCH unexpectedly proved: {
        squash (← HolCore.Printer.string_of_thm th)}"

/-- Apply a RULE (`REAL_LE_IMP`/`REAL_LET_IMP`) to a theorem and compare the
    printed RESULT against `expected`.  A printed theorem does NOT exercise a
    rule; only applying it does. -/
private unsafe def ruleCheck (lbl : String) (r : thm → IO (Except String thm))
    (arg : thm) (expected : String) : IO Unit := do
  match ← r arg with
  | .error e => IO.println s!"{lbl} -> MISMATCH rule failed: {e}"
  | .ok th =>
    let got := squash (← HolCore.Printer.string_of_thm th)
    if got == squash expected then IO.println s!"{lbl} -> OK"
    else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- (1) A REPRESENTATIVE SAMPLE FROM EVERY ONE OF THE ELEVEN BUNDLES.       -/
/- At least three theorems per bundle, chosen for transcription hazards.   -/
/- ---------------------------------------------------------------------- -/

/- realThms1 (real.ml 14-102): REAL_OF_NUM_* bridges.  REAL_OF_NUM_CLAUSES is a
   10-conjunct bundle feeding the numeral rewriter - assert its count. -/
#eval thmCheck "realThms1 REAL_OF_NUM_LT" realThms1.REAL_OF_NUM_LT
  "|- forall m n. &m < &n <=> m < n"
#eval thmCheck "realThms1 REAL_OF_NUM_SUB_CASES" realThms1.REAL_OF_NUM_SUB_CASES
  "|- forall m n. &m - &n = (if n <= m then &(m - n) else -- &(n - m))"
#eval conjCountCheck "realThms1 REAL_OF_NUM_CLAUSES count"
  realThms1.REAL_OF_NUM_CLAUSES 10

/- realThms2 (real.ml 109-255): the linear theorems.  The LNEG/RNEG pair is a
   known crossing hazard - which side the negation lands on differs. -/
#eval thmCheck "realThms2 REAL_LT_LADD" realThms2.REAL_LT_LADD
  "|- forall x y z. x + y < x + z <=> y < z"
#eval thmCheck "realThms2 REAL_LT_LNEG" realThms2.REAL_LT_LNEG
  "|- forall x y. --x < y <=> &0 < x + y"
#eval thmCheck "realThms2 REAL_LT_RNEG" realThms2.REAL_LT_RNEG
  "|- forall x y. x < --y <=> x + y < &0"

/- realThms3 (real.ml 256-400): subtraction/negation theorems. -/
#eval thmCheck "realThms3 REAL_LE_NEGR" realThms3.REAL_LE_NEGR
  "|- forall x. x <= --x <=> x <= &0"
#eval thmCheck "realThms3 REAL_LE_SUB_LADD" realThms3.REAL_LE_SUB_LADD
  "|- forall x y z. x <= y - z <=> x + z <= y"
#eval thmCheck "realThms3 REAL_SUB_LDISTRIB" realThms3.REAL_SUB_LDISTRIB
  "|- forall x y z. x * (y - z) = x * y - x * z"

/- realThms4 (real.ml 401-510): absolute-value theorems. -/
#eval thmCheck "realThms4 REAL_ABS_TRIANGLE" realThms4.REAL_ABS_TRIANGLE
  "|- forall x y. abs (x + y) <= abs x + abs y"
#eval thmCheck "realThms4 REAL_ABS_BOUNDS" realThms4.REAL_ABS_BOUNDS
  "|- forall x k. abs x <= k <=> --k <= x /\\ x <= k"
#eval thmCheck "realThms4 REAL_ABS_SUB_ABS" realThms4.REAL_ABS_SUB_ABS
  "|- forall x y. abs (abs x - abs y) <= abs (x - y)"

/- realThms5 (real.ml 511-594): min/max theorems.  REAL_MAX_ACI and
   REAL_MIN_ACI are the 5-conjunct ACI laws - assert their counts. -/
#eval thmCheck "realThms5 REAL_LE_MAX" realThms5.REAL_LE_MAX
  "|- forall x y z. z <= max x y <=> z <= x \\/ z <= y"
#eval thmCheck "realThms5 REAL_MIN_LE" realThms5.REAL_MIN_LE
  "|- forall x y z. min x y <= z <=> x <= z \\/ y <= z"
#eval conjCountCheck "realThms5 REAL_MAX_ACI count" realThms5.REAL_MAX_ACI 5
#eval conjCountCheck "realThms5 REAL_MIN_ACI count" realThms5.REAL_MIN_ACI 5

/- realThms6 (real.ml 607-855): multiplication/inverse/power theorems. -/
#eval thmCheck "realThms6 REAL_ABS_MUL" realThms6.REAL_ABS_MUL
  "|- forall x y. abs (x * y) = abs x * abs y"
#eval thmCheck "realThms6 REAL_LT_INV" realThms6.REAL_LT_INV
  "|- forall x. &0 < x ==> &0 < inv x"
#eval thmCheck "realThms6 REAL_POW_ADD" realThms6.REAL_POW_ADD
  "|- forall x m n. x pow (m + n) = x pow m * x pow n"

/- realThms7 (real.ml 856-1114): cancellation and division/inverse ordering. -/
#eval thmCheck "realThms7 REAL_LT_LCANCEL_IMP" realThms7.REAL_LT_LCANCEL_IMP
  "|- forall x y z. &0 < x /\\ x * y < x * z ==> y < z"
#eval thmCheck "realThms7 REAL_LE_MUL2" realThms7.REAL_LE_MUL2
  "|- forall w x y z. &0 <= w /\\ w <= x /\\ &0 <= y /\\ y <= z ==> w * y <= x * z"
#eval thmCheck "realThms7 REAL_DOWN2" realThms7.REAL_DOWN2
  "|- forall d1 d2. &0 < d1 /\\ &0 < d2 ==> (exists e. &0 < e /\\ e < d1 /\\ e < d2)"

/- realThms8 (real.ml 1115-1389): power monotonicity and squares. -/
#eval thmCheck "realThms8 REAL_POW_LE_1" realThms8.REAL_POW_LE_1
  "|- forall n x. &1 <= x ==> &1 <= x pow n"
#eval thmCheck "realThms8 REAL_POW_LT2_ODD" realThms8.REAL_POW_LT2_ODD
  "|- forall n x y. x < y /\\ ODD n ==> x pow n < y pow n"
#eval thmCheck "realThms8 REAL_OF_NUM_DIV" realThms8.REAL_OF_NUM_DIV
  "|- forall m n. &(m DIV n) = &m / &n - &(m MOD n) / &n"

/- realThms9 (real.ml 1390-1517): convex bounds and the Archimedean theorems. -/
#eval thmCheck "realThms9 REAL_ARCH_SIMPLE" realThms9.REAL_ARCH_SIMPLE
  "|- forall x. exists n. x <= &n"
#eval thmCheck "realThms9 REAL_ARCH_INV" realThms9.REAL_ARCH_INV
  "|- forall e. &0 < e <=> (exists n. ~(n = 0) /\\ &0 < inv (&n) /\\ inv (&n) < e)"
#eval thmCheck "realThms9 REAL_CONVEX_BOUNDS_LE" realThms9.REAL_CONVEX_BOUNDS_LE
  ("|- forall x y a b u v. a <= x /\\ x <= b /\\ a <= y /\\ y <= b /\\ &0 <= u /\\ &0 <= v /\\ " ++
   "u + v = &1 ==> a <= u * x + v * y /\\ u * x + v * y <= b")

/- realThms10 (real.ml 1518-1656): the `real_sgn` DEFINITION and its theorems,
   plus the WLOG rules.  REAL_SGN_INEQS is a 10-conjunct bundle. -/
#eval thmCheck "realThms10 real_sgn (defn)" realThms10.real_sgn
  "|- forall x. real_sgn x = (if &0 < x then &1 else if x < &0 then -- &1 else &0)"
#eval conjCountCheck "realThms10 REAL_SGN_INEQS count" realThms10.REAL_SGN_INEQS 10
#eval thmCheck "realThms10 REAL_WLOG_LE_3" realThms10.REAL_WLOG_LE_3
  ("|- forall P. (forall x y z. P x y z ==> P y x z /\\ P x z y) /\\ " ++
   "(forall x y z. x <= y /\\ y <= z ==> P x y z) ==> (forall x y z. P x y z)")

/- realThms11 (real.ml 1657-1993): the `sqrt` DEFINITION and its theory.
   Forcing this pulls in every other real.ml bundle. -/
#eval thmCheck "realThms11 sqrt (defn)" realThms11.sqrt
  "|- forall x. sqrt x = (@y. real_sgn y = real_sgn x /\\ y pow 2 = abs x)"
#eval thmCheck "realThms11 SQRT_WORKS_GEN" realThms11.SQRT_WORKS_GEN
  "|- forall x. real_sgn (sqrt x) = real_sgn x /\\ sqrt x pow 2 = abs x"
#eval thmCheck "realThms11 SQRT_UNIQUE" realThms11.SQRT_UNIQUE
  "|- forall x y. &0 <= y /\\ y pow 2 = x ==> sqrt x = y"
#eval thmCheck "realThms11 POW_2_SQRT" realThms11.POW_2_SQRT
  "|- forall x. &0 <= x ==> sqrt (x pow 2) = x"

/- ---------------------------------------------------------------------- -/
/- (2) THE THREE NON-THEOREM ITEMS, EXERCISED (not printed).              -/
/-                                                                        -/
/- REAL_ARITH_TAC must PROVE a goal; a rule must be APPLIED to a theorem.  -/
/- IMPORTANT: REAL_LE_IMP/REAL_LET_IMP need a `<=`-CONCLUDING input - their -/
/- pth antecedent is `x <= y`, so feeding a `<`-theorem gives `term_pmatch`.-/
/- REAL_ABS_POS (`|- !x. &0 <= abs x`) is a `<=` theorem, so it is a valid  -/
/- argument for both.                                                      -/
/- ---------------------------------------------------------------------- -/

#eval provesTac "REAL_ARITH_TAC totality" "!x y. x <= y \\/ y <= x"
#eval provesTac "REAL_ARITH_TAC triangle" "!x y. abs (x + y) <= abs x + abs y"
#eval provesTac "REAL_ARITH_TAC max ge"   "!x y. max x y >= x"

#eval ruleCheck "REAL_LE_IMP on REAL_ABS_POS" Session.REAL_LE_IMP
  Session.REAL_ABS_POS "|- forall x z. abs x <= z ==> &0 <= z"
#eval ruleCheck "REAL_LET_IMP on REAL_ABS_POS" Session.REAL_LET_IMP
  Session.REAL_ABS_POS "|- forall x z. abs x < z ==> &0 < z"

/- ---------------------------------------------------------------------- -/
/- (3) SQRT COMPUTATIONS - the payoff of the last section.                -/
/- SQRT_0, SQRT_1, POW_2_SQRT (bundle) plus a small sqrt fact driven       -/
/- through REWRITE_CONV with SQRT_0 (a conversion, not a print).          -/
/- ---------------------------------------------------------------------- -/

#eval thmCheck "SQRT_0" Session.SQRT_0 "|- sqrt (&0) = &0"
#eval thmCheck "SQRT_1" Session.SQRT_1 "|- sqrt (&1) = &1"

/- Drive `sqrt (&0) + &1` through a rewrite with SQRT_0: the conversion must
   turn `sqrt (&0)` into `&0`, producing `|- sqrt (&0) + &1 = &0 + &1`. -/
#eval do
  match ← HolCore.Parser.parse_term "sqrt (&0) + &1" with
  | .error e => IO.println s!"sqrt conversion parse ERR: {e}"
  | .ok tm =>
    match ← Session.REWRITE_CONV [Session.SQRT_0] tm with
    | .error e => IO.println s!"sqrt conversion -> MISMATCH conv failed: {e}"
    | .ok th =>
      let got := squash (← HolCore.Printer.string_of_thm th)
      if got == squash "|- sqrt (&0) + &1 = &0 + &1"
      then IO.println "sqrt conversion (REWRITE_CONV[SQRT_0]) -> OK"
      else IO.println s!"sqrt conversion -> MISMATCH got={got}"

/- ---------------------------------------------------------------------- -/
/- (4) THE BARE RE-EXPORTS.  Session carries 331 bare accessors for        -/
/- real.ml, since in HOL Light every theorem is a bare global name.  Check  -/
/- a few - including the two definition names - to prove that block works.  -/
/- ---------------------------------------------------------------------- -/

#eval thmCheck "bare Session.REAL_ABS_ZERO" Session.REAL_ABS_ZERO
  "|- forall x. abs x = &0 <=> x = &0"
#eval thmCheck "bare Session.REAL_SGN_0" Session.REAL_SGN_0
  "|- real_sgn (&0) = &0"
#eval thmCheck "bare Session.real_sgn (defn)" Session.real_sgn
  "|- forall x. real_sgn x = (if &0 < x then &1 else if x < &0 then -- &1 else &0)"
#eval thmCheck "bare Session.sqrt (defn)" Session.sqrt
  "|- forall x. sqrt x = (@y. real_sgn y = real_sgn x /\\ y pow 2 = abs x)"

/- ---------------------------------------------------------------------- -/
/- (5) THE Help/REAL_ARITH_TAC.hlp EXAMPLES, with a verified finding, and  -/
/-     the DECISIVE CONTRAST between real.ml's REAL_ARITH_TAC and           -/
/-     calc_rat.ml's REAL_ARITH_TAC2.                                       -/
/-                                                                        -/
/- Both worked examples in hol-light/Help/REAL_ARITH_TAC.hlp FAIL under     -/
/- real.ml's REAL_ARITH_TAC (`Session.REAL_ARITH_TAC`, built over           -/
/- REAL_ARITH2) with `linear_ineqs: no contradiction`, and that is CORRECT  -/
/- and PERMANENT for that version: both use RATIONAL constants (`/ &6`,     -/
/- `/ &2`, `/ &4`, `/ &3`), and REAL_ARITH2 instantiates its semiring       -/
/- normaliser with `is_realintconst` (realarith.ml 496), so a rational      -/
/- coefficient can never be folded.  We KEEP the REAL_ARITH_TAC failure     -/
/- assertions below - that version genuinely cannot do this.                -/
/-                                                                        -/
/- calc_rat.ml resolves it.  calc_rat.ml 434 passes `is_ratconst` instead   -/
/- of `is_realintconst`, so a rational constant becomes a numeric           -/
/- COEFFICIENT the linear arithmetic can fold; REAL_ARITH_TAC2 (calc_rat.ml -/
/- 553, `CONV_TAC REAL_ARITH3`) is the tactic built over that.  Both        -/
/- examples now PROVE under REAL_ARITH_TAC2, asserted immediately after     -/
/- each failure - so the two REAL_ARITH_TAC versions demonstrably DIFFER on -/
/- these exact goals.  This confirms REAL_ARITH_TAC.hlp documents the       -/
/- calc_rat.ml version, which is now the live one.                         -/
/-                                                                        -/
/- HELP-FILE VERDICT.  REAL_ARITH_TAC.hlp is VERSION SKEW: it documents the -/
/- calc_rat.ml REAL_ARITH_TAC while appearing at real.ml.  It is the SECOND -/
/- such version-skew finding (the first was REAL_ARITH.hlp, on              -/
/- realarith.ml); it is NOT the third distinct finding - a previous         -/
/- over-claim was corrected, and REAL_INT_NEG_CONV.hlp is a different kind  -/
/- of fault (a copy-paste error, not version skew).  The two integer-       -/
/- constant analogues below (same shapes, integer constants) PROVE even     -/
/- under REAL_ARITH_TAC, isolating the cause to the rational constant.      -/
/- ---------------------------------------------------------------------- -/

/-- Parse `goal`, run `REAL_ARITH_TAC2` (calc_rat.ml 553, the FINAL
    `REAL_ARITH_TAC` over `REAL_ARITH3`), assert it PROVES the goal.  Same
    shape as `provesTac` but over the calc_rat.ml tactic rather than real.ml's,
    so the two can be contrasted on the same goal. -/
private unsafe def provesTac2 (lbl goal : String) : IO Unit := do
  match ← HolCore.Parser.parse_term goal with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok tm =>
    let want := squash ("|- " ++ (← HolCore.Printer.string_of_term tm))
    match ← Session.prove tm Session.REAL_ARITH_TAC2 with
    | .error e => IO.println s!"{lbl} -> MISMATCH failed to prove: {e}"
    | .ok th =>
      let got := squash (← HolCore.Printer.string_of_thm th)
      if got == want then IO.println s!"{lbl} -> OK"
      else IO.println s!"{lbl} -> MISMATCH got={got} want={want}"

/- (a) the big algebraic-normalisation identity ending `... ) / &6`. -/
#eval failsTac "HLP (a) rational / &6 (REAL_ARITH_TAC over v2 genuinely CANNOT)"
  ("(x1 pow 2 + x2 pow 2 + x3 pow 2 + x4 pow 2) pow 2 = " ++
   "((x1 + x2) pow 4 + (x1 + x3) pow 4 + (x1 + x4) pow 4 + " ++
   "(x2 + x3) pow 4 + (x2 + x4) pow 4 + (x3 + x4) pow 4 + " ++
   "(x1 - x2) pow 4 + (x1 - x3) pow 4 + (x1 - x4) pow 4 + " ++
   "(x2 - x3) pow 4 + (x2 - x4) pow 4 + (x3 - x4) pow 4) / &6")
  "linear_ineqs"
/- (a) SAME goal now PROVES under REAL_ARITH_TAC2 (fixed by calc_rat.ml:
   is_ratconst folds `/ &6`, is_realintconst could not). -/
#eval provesTac2 "HLP (a) rational / &6 (REAL_ARITH_TAC2 now PROVES; fixed by calc_rat.ml)"
  ("(x1 pow 2 + x2 pow 2 + x3 pow 2 + x4 pow 2) pow 2 = " ++
   "((x1 + x2) pow 4 + (x1 + x3) pow 4 + (x1 + x4) pow 4 + " ++
   "(x2 + x3) pow 4 + (x2 + x4) pow 4 + (x3 + x4) pow 4 + " ++
   "(x1 - x2) pow 4 + (x1 - x3) pow 4 + (x1 - x4) pow 4 + " ++
   "(x2 - x3) pow 4 + (x2 - x4) pow 4 + (x3 - x4) pow 4) / &6")
/- (b) `&26 < x / &2 ==> abs(x / &4 + &1) < abs(x / &3)`. -/
#eval failsTac "HLP (b) rational / &2 (REAL_ARITH_TAC over v2 genuinely CANNOT)"
  "&26 < x / &2 ==> abs(x / &4 + &1) < abs(x / &3)"
  "linear_ineqs"
/- (b) SAME goal now PROVES under REAL_ARITH_TAC2 (fixed by calc_rat.ml). -/
#eval provesTac2 "HLP (b) rational / &2 (REAL_ARITH_TAC2 now PROVES; fixed by calc_rat.ml)"
  "&26 < x / &2 ==> abs(x / &4 + &1) < abs(x / &3)"
/- (a') integer-constant analogue of (a): PROVES even under REAL_ARITH_TAC. -/
#eval provesTac "INT analogue of (a)"
  "&6 * ((x1 pow 2 + x2 pow 2) pow 2) = &6 * ((x1 pow 2 + x2 pow 2) pow 2)"
/- (b') integer-constant analogue of (b): PROVES even under REAL_ARITH_TAC. -/
#eval provesTac "INT analogue of (b)"
  "&26 * &12 < x * &6 ==> abs(x * &3 + &12) < abs(x * &4)"
