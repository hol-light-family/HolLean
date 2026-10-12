/- File: HolTest/CalcRatTest.lean
Runtime test suite: calc_rat.ml - calculation with rational-valued reals, the
file that finally makes HOL Light's real arithmetic work over the RATIONALS.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

FAITHFULNESS BASIS.  The conversion expectations below are taken VERBATIM from
HOL Light's own reference documentation, which ships worked examples with real
OCaml output:
  hol-light/Help/REAL_RAT_ADD_CONV.hlp   .../REAL_RAT_SUB_CONV.hlp
  .../REAL_RAT_MUL_CONV.hlp              .../REAL_RAT_DIV_CONV.hlp
  .../REAL_RAT_NEG_CONV.hlp              .../REAL_RAT_ABS_CONV.hlp
  .../REAL_RAT_INV_CONV.hlp              .../REAL_RAT_POW_CONV.hlp
  .../REAL_RAT_MAX_CONV.hlp              .../REAL_RAT_MIN_CONV.hlp
  .../REAL_RAT_SGN_CONV.hlp              .../REAL_RAT_LE_CONV.hlp
  .../REAL_RAT_LT_CONV.hlp               .../REAL_RAT_GE_CONV.hlp
  .../REAL_RAT_GT_CONV.hlp               .../REAL_RAT_EQ_CONV.hlp
  .../REAL_RAT_REDUCE_CONV.hlp           .../REAL_RING.hlp
  .../REAL_FIELD.hlp                     .../REAL_IDEAL_CONV.hlp
A mismatch on those is a genuine divergence from HOL Light.  Definitions and
theorem statements are checked against calc_rat.ml itself.

THE POINT OF THIS FILE.  calc_rat.ml OVERWRITES `GEN_REAL_ARITH`/`REAL_ARITH`/
`REAL_ARITH_TAC` for the THIRD and LAST time.  The decisive change is at
calc_rat.ml 434: the semiring normaliser is instantiated with `is_ratconst`
where realarith.ml 496 passed `is_realintconst`.  With `is_realintconst` a
rational constant like `&1 / &2` is opaque to the normaliser and is absorbed
into the monomial instead of becoming a numeric COEFFICIENT the linear
arithmetic can fold - which is exactly why realarith.ml's `REAL_ARITH` (and
therefore real.ml's `REAL_ARITH_TAC`) cannot prove goals with rational
denominators.  This file's `REAL_ARITH3`/`REAL_ARITH_TAC2` can.  Three tests in
HolTest/RealArithTest.lean and HolTest/RealTest.lean were asserted to FAIL for
exactly this reason and, now that calc_rat.ml is wired in, have been flipped to
prove under the NEW prover while the EARLIER `REAL_ARITH2`/real.ml
`REAL_ARITH_TAC` assertions are kept as an explicit contrast (see those files).

`&` is `real_of_num`, the injection of the naturals into the reals; `#DDD.DDD`
is decimal notation, `DECIMAL x y = &x / &y`.
-/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- FORCING THE REAL LAYER FIRST IS MANDATORY.                             -/
/-                                                                        -/
/- calc_rat.ml sits on real.ml, which sits on the LAZY realarith          -/
/- bootstrap; a conversion or tactic passed around as a VALUE forces       -/
/- nothing.  So a term mentioning `&`, `abs`, `min`, `max` or a decimal    -/
/- cannot even be PARSED until something has forced the real layer into    -/
/- existence - otherwise a bare probe fails with `mk_type: type num has    -/
/- not been defined`, and `abs`/`min`/`max` silently parse as VARIABLES.   -/
/- `REAL_OF_NUM_LT` is the CHEAPEST such accessor (`setupRealThms1` takes   -/
/- no REAL_ARITH parameter), so this `#eval` MUST come first, before any   -/
/- other parse in this file.                                              -/
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

/-- Parse `expr`, apply the conversion, compare the resulting theorem. -/
private unsafe def convCheck (lbl expr expected : String) (c : ioconv) : IO Unit := do
  match ← HolCore.Parser.parse_term expr with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok tm =>
    match ← c tm with
    | .error e => IO.println s!"{lbl} ERR: {e}"
    | .ok th =>
      let got := squash (← HolCore.Printer.string_of_thm th)
      if got == squash expected then IO.println s!"{lbl} -> OK"
      else IO.println s!"{lbl} -> MISMATCH got={got}"

/-- Parse `goal`, run a `term → IO (Except String thm)` decision procedure,
    assert it PROVES the goal with NO hypotheses.  A proved goal's conclusion IS
    the goal, so the expected form is `|- ` prepended to the goal RE-PRINTED
    from its parse (normalising cosmetic input like `abs(x)` vs `abs x`). -/
private unsafe def proves (lbl goal : String)
    (proc : term → IO (Except String thm)) : IO Unit := do
  match ← HolCore.Parser.parse_term goal with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok tm =>
    let want := squash ("|- " ++ (← HolCore.Printer.string_of_term tm))
    match ← proc tm with
    | .error e => IO.println s!"{lbl} -> MISMATCH failed to prove: {e}"
    | .ok th =>
      let got := squash (← HolCore.Printer.string_of_thm th)
      if got == want then IO.println s!"{lbl} -> OK"
      else IO.println s!"{lbl} -> MISMATCH got={got} want={want}"

/-- Parse `goal`, run a TACTIC via `Session.prove`, assert it PROVES the goal
    with NO hypotheses. -/
private unsafe def provesTac (lbl goal : String) (tac : HolCore.Tactics.tactic) : IO Unit := do
  match ← HolCore.Parser.parse_term goal with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok tm =>
    let want := squash ("|- " ++ (← HolCore.Printer.string_of_term tm))
    match ← Session.prove tm tac with
    | .error e => IO.println s!"{lbl} -> MISMATCH failed to prove: {e}"
    | .ok th =>
      let got := squash (← HolCore.Printer.string_of_thm th)
      if got == want then IO.println s!"{lbl} -> OK"
      else IO.println s!"{lbl} -> MISMATCH got={got} want={want}"

/-- Prove `goal` from the assumption list `asms` with `ASM_REAL_ARITH_TAC`.
    Parses each assumption, `ASSUME`s it, then runs the tactic with those
    theorems available in the goal's hypotheses via `prove`-with-assumptions.
    Since `Session.prove` takes no assumption list, drive it by discharging the
    assumptions into the goal as an implication the tactic re-absorbs: build
    `asm1 ==> ... ==> goal`, prove THAT with
    `REPEAT DISCH_TAC THEN ASM_REAL_ARITH_TAC`, and assert success. -/
private unsafe def provesAsm (lbl : String) (asms : List String) (goal : String)
    (tac : HolCore.Tactics.tactic) : IO Unit := do
  let full := asms.foldr (fun a g => "(" ++ a ++ ") ==> (" ++ g ++ ")") goal
  match ← HolCore.Parser.parse_term full with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok tm =>
    let want := squash ("|- " ++ (← HolCore.Printer.string_of_term tm))
    match ← Session.prove tm (THEN (REPEAT DISCH_TAC) tac) with
    | .error e => IO.println s!"{lbl} -> MISMATCH failed to prove: {e}"
    | .ok th =>
      let got := squash (← HolCore.Printer.string_of_thm th)
      if got == want then IO.println s!"{lbl} -> OK"
      else IO.println s!"{lbl} -> MISMATCH got={got} want={want}"

/-- Assert a `term → IO (Except String thm)` procedure FAILS, and (when
    `wantMsg` is nonempty) that the error CONTAINS `wantMsg`. -/
private unsafe def procFails (lbl goal wantMsg : String)
    (proc : term → IO (Except String thm)) : IO Unit := do
  match ← HolCore.Parser.parse_term goal with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok tm =>
    match ← proc tm with
    | .error e =>
      if wantMsg == "" || (e.splitOn wantMsg).length > 1 then
        IO.println s!"{lbl} -> OK (correctly fails: {e})"
      else IO.println s!"{lbl} -> MISMATCH wrong error: {e}"
    | .ok th =>
      IO.println s!"{lbl} -> MISMATCH unexpectedly proved: {
        squash (← HolCore.Printer.string_of_thm th)}"

/- ---------------------------------------------------------------------- -/
/- (1) DECIMAL - the new constant `DECIMAL x y = &x / &y` (calc_rat.ml 16). -/
/- ---------------------------------------------------------------------- -/

#eval thmCheck "DECIMAL (defn)" Session.DECIMAL "|- forall x y. DECIMAL x y = &x / &y"

/- ---------------------------------------------------------------------- -/
/- (2) THE FIVE HANDY LEMMAS RAT_LEMMA1..5 (calc_rat.ml 20-80).            -/
/- Statements checked against calc_rat.ml itself.                          -/
/- ---------------------------------------------------------------------- -/

#eval thmCheck "RAT_LEMMA1" Session.RAT_LEMMA1
  ("|- ~(y1 = &0) /\\ ~(y2 = &0) ==> " ++
   "x1 / y1 + x2 / y2 = (x1 * y2 + x2 * y1) * inv y1 * inv y2")
#eval thmCheck "RAT_LEMMA2" Session.RAT_LEMMA2
  ("|- &0 < y1 /\\ &0 < y2 ==> " ++
   "x1 / y1 + x2 / y2 = (x1 * y2 + x2 * y1) * inv y1 * inv y2")
#eval thmCheck "RAT_LEMMA3" Session.RAT_LEMMA3
  ("|- &0 < y1 /\\ &0 < y2 ==> " ++
   "x1 / y1 - x2 / y2 = (x1 * y2 - x2 * y1) * inv y1 * inv y2")
#eval thmCheck "RAT_LEMMA4" Session.RAT_LEMMA4
  ("|- &0 < y1 /\\ &0 < y2 ==> (x1 / y1 <= x2 / y2 <=> x1 * y2 <= x2 * y1)")
#eval thmCheck "RAT_LEMMA5" Session.RAT_LEMMA5
  ("|- &0 < y1 /\\ &0 < y2 ==> (x1 / y1 = x2 / y2 <=> x1 * y2 = x2 * y1)")

/- ---------------------------------------------------------------------- -/
/- (3) THE RELATIONAL CONVERSIONS (calc_rat.ml 95-171).                    -/
/- Each first case is the Help file's own worked example.                  -/
/- ---------------------------------------------------------------------- -/

#eval convCheck "LE #3.1415926 <= &22/&7 [Help]" "#3.1415926 <= &22 / &7"
  "|- #3.1415926 <= &22 / &7 <=> true" REAL_RAT_LE_CONV
#eval convCheck "LT #3.1415926 < &355/&113 [Help]" "#3.1415926 < &355 / &113"
  "|- #3.1415926 < &355 / &113 <=> true" REAL_RAT_LT_CONV
#eval convCheck "GE #3.1415926 >= &22/&7 [Help]" "#3.1415926 >= &22 / &7"
  "|- #3.1415926 >= &22 / &7 <=> false" REAL_RAT_GE_CONV
#eval convCheck "GT &3/&2 > #1.11 [Help]" "&3 / &2 > #1.11"
  "|- &3 / &2 > #1.11 <=> true" REAL_RAT_GT_CONV
#eval convCheck "EQ #0.40 = &2/&5 [Help]" "#0.40 = &2 / &5"
  "|- #0.40 = &2 / &5 <=> true" REAL_RAT_EQ_CONV
#eval convCheck "EQ #3.14 = &22/&7 [Help]" "#3.14 = &22 / &7"
  "|- #3.14 = &22 / &7 <=> false" REAL_RAT_EQ_CONV
#eval convCheck "SGN real_sgn(-- &3/&2) [Help]" "real_sgn(-- &3 / &2)"
  "|- real_sgn (-- &3 / &2) = -- &1" REAL_RAT_SGN_CONV

/- ---------------------------------------------------------------------- -/
/- (4) THE UNARY CONVERSIONS NEG/ABS/INV (calc_rat.ml 172-229).            -/
/- ---------------------------------------------------------------------- -/

#eval convCheck "NEG -- (-- &3/&2) [Help]" "-- (-- &3 / &2)"
  "|- --(-- &3 / &2) = &3 / &2" REAL_RAT_NEG_CONV
#eval convCheck "ABS abs(-- &3/&2) [Help]" "abs(-- &3 / &2)"
  "|- abs (-- &3 / &2) = &3 / &2" REAL_RAT_ABS_CONV
#eval convCheck "INV inv(-- &5/&9) [Help]" "inv(-- &5 / &9)"
  "|- inv (-- &5 / &9) = -- &9 / &5" REAL_RAT_INV_CONV

/- ---------------------------------------------------------------------- -/
/- (5) THE ARITHMETIC CONVERSIONS ADD/SUB/MUL/DIV (calc_rat.ml 230-358).   -/
/- ---------------------------------------------------------------------- -/

#eval convCheck "ADD -- &11/&12 + #0.09 [Help]" "-- &11 / &12 + #0.09"
  "|- -- &11 / &12 + #0.09 = -- &62 / &75" REAL_RAT_ADD_CONV
#eval convCheck "SUB &355/&113 - #3.1415926 [Help]" "&355 / &113 - #3.1415926"
  "|- &355 / &113 - #3.1415926 = &181 / &565000000" REAL_RAT_SUB_CONV
#eval convCheck "MUL #3.16227766016837952 sq [Help]"
  "#3.16227766016837952 * #3.16227766016837952"
  ("|- #3.16227766016837952 * #3.16227766016837952 = " ++
   "&24414062500000002902889155426649 / &2441406250000000000000000000000")
  REAL_RAT_MUL_CONV
#eval convCheck "DIV &2000 / (-- &40/&12) [Help]" "&2000 / (-- &40 / &12)"
  "|- &2000 / (-- &40 / &12) = -- &600" REAL_RAT_DIV_CONV

/- ---------------------------------------------------------------------- -/
/- (6) POWERS, MAX, MIN (calc_rat.ml 359-385).                             -/
/- ---------------------------------------------------------------------- -/

#eval convCheck "POW #1.414 pow 2 [Help]" "#1.414 pow 2"
  "|- #1.414 pow 2 = &1999396 / &1000000" REAL_RAT_POW_CONV
#eval convCheck "MAX max (-- &9) (&22/&7) [Help]" "max (-- &9) (&22 / &7)"
  "|- max (-- &9) (&22 / &7) = &22 / &7" REAL_RAT_MAX_CONV
#eval convCheck "MIN min (-- &9) (&22/&7) [Help]" "min (-- &9) (&22 / &7)"
  "|- min (-- &9) (&22 / &7) = -- &9" REAL_RAT_MIN_CONV

/- ---------------------------------------------------------------------- -/
/- (7) THE REDUCTION AND COMPUTE ENTRY POINTS (calc_rat.ml 386-427).       -/
/- REAL_RAT_REDUCE_CONV's case is the Help file's own worked example (a    -/
/- compound expression exercising `<`, `/`, `+` and decimal-vs-ratio       -/
/- comparison at once); REAL_RAT_COMPUTE_CONV runs the same via the        -/
/- call-by-value compset path.                                            -/
/- ---------------------------------------------------------------------- -/

#eval convCheck "REDUCE compound [Help]"
  "#3.1415926535 < &355 / &113 /\\ &355 / &113 < &3 + &1 / &7"
  "|- #3.1415926535 < &355 / &113 /\\ &355 / &113 < &3 + &1 / &7 <=> true"
  REAL_RAT_REDUCE_CONV
#eval convCheck "COMPUTE compound (cbv path)"
  "#3.1415926535 < &355 / &113 /\\ &355 / &113 < &3 + &1 / &7"
  "|- #3.1415926535 < &355 / &113 /\\ &355 / &113 < &3 + &1 / &7 <=> true"
  REAL_RAT_COMPUTE_CONV

/- ---------------------------------------------------------------------- -/
/- (8) THE POLYNOMIAL NORMALISERS (calc_rat.ml 428-486).                   -/
/- The FIRST `REAL_POLY_CONV` (via REAL_POLY_ADD_CONV) and the SECOND      -/
/- (REAL_POLY_CONV, extended to inv/division).  Each is driven on an       -/
/- expression whose RATIONAL COEFFICIENT must FOLD - the very thing the    -/
/- `is_ratconst` instantiation (calc_rat.ml 434) enables and which the     -/
/- integer-only realarith.ml normaliser could not do.  `&1 / &2 * x +      -/
/- &1 / &2 * x` must collapse to `x` (coefficients fold to &1); `inv(&2)   -/
/- * x + inv(&2) * x` likewise, exercising the second normaliser's `inv`   -/
/- handling.                                                               -/
/- ---------------------------------------------------------------------- -/

#eval convCheck "POLY1 ADD folds rational coeff"
  "&1 / &2 * x + &1 / &2 * x" "|- &1 / &2 * x + &1 / &2 * x = x"
  REAL_POLY_ADD_CONV
#eval convCheck "POLY2 (inv) folds rational coeff"
  "inv(&2) * x + inv(&2) * x" "|- inv (&2) * x + inv (&2) * x = x"
  REAL_POLY_CONV

/- ---------------------------------------------------------------------- -/
/- (9) REAL_RING and REAL_IDEAL_CONV (calc_rat.ml 487-533).                -/
/- The two REAL_RING cases are the Help file's own worked examples (the    -/
/- Gosper homographic inversion and the specific-features example);        -/
/- REAL_IDEAL_CONV is its Help singleton-list division example.            -/
/- ---------------------------------------------------------------------- -/

#eval proves "REAL_RING Gosper [Help]"
  "y * (c * x + d) = a * x + b ==> x * (c * y - a) = b - d * y" REAL_RING
#eval proves "REAL_RING specific-features [Help]"
  ("s pow 2 = &2 ==> (x pow 4 + &1 = &0 <=> " ++
   "x pow 2 + s * x + &1 = &0 \\/ x pow 2 - s * x + &1 = &0)") REAL_RING
/- REAL_IDEAL_CONV [`x - &1`] `x pow 4 - &1` (Help). -/
#eval do
  match ← HolCore.Parser.parse_term "x - &1", ← HolCore.Parser.parse_term "x pow 4 - &1" with
  | .ok p1, .ok tgt =>
    match ← Session.REAL_IDEAL_CONV [p1] tgt with
    | .error e => IO.println s!"REAL_IDEAL_CONV [Help] ERR: {e}"
    | .ok th =>
      let got := squash (← HolCore.Printer.string_of_thm th)
      let want := squash
        "|- x pow 4 - &1 = (&1 * x pow 3 + &1 * x pow 2 + &1 * x + &1) * (x - &1)"
      if got == want then IO.println "REAL_IDEAL_CONV [Help] -> OK"
      else IO.println s!"REAL_IDEAL_CONV [Help] -> MISMATCH got={got}"
  | _, _ => IO.println "REAL_IDEAL_CONV [Help] parse ERR"

/- ---------------------------------------------------------------------- -/
/- (10) THE FINAL REAL_ARITH3 / GEN_REAL_ARITH3 (calc_rat.ml 534-559).     -/
/-                                                                        -/
/- These are the FINAL versions and SUPERSEDE realarith.ml's REAL_ARITH2   -/
/- and real.ml's REAL_ARITH_TAC.  The decisive test is a rational-         -/
/- denominator goal: REAL_ARITH3 proves it, whereas REAL_ARITH2 (asserted  -/
/- in RealArithTest.lean) cannot.  The three FORWARD-MARKER goals in        -/
/- RealArithTest.lean/RealTest.lean are the canonical demonstrations; here  -/
/- we cover REAL_ARITH3 (rule), REAL_ARITH_TAC2 (tactic) and                -/
/- ASM_REAL_ARITH_TAC directly.                                            -/
/- ---------------------------------------------------------------------- -/

/- REAL_ARITH3 on a rational-denominator goal (the class realarith.ml's
   is_realintconst normaliser cannot fold; is_ratconst can). -/
#eval proves "REAL_ARITH3 rational / &2"
  "&26 < x / &2 ==> abs(x / &4 + &1) < abs(x / &3)" REAL_ARITH3
/- REAL_ARITH_TAC2 on a rational-denominator goal, via a tactic. -/
#eval provesTac "REAL_ARITH_TAC2 rational / &2"
  "!x. &0 <= x ==> x / &2 <= x" REAL_ARITH_TAC2
/- ASM_REAL_ARITH_TAC: takes a rational-denominator fact from the ASSUMPTIONS
   (moved into the goal by its FIRST_X_ASSUM MP_TAC preamble) and closes. -/
#eval provesAsm "ASM_REAL_ARITH_TAC rational / &2"
  ["&26 < x / &2"] "abs(x / &4 + &1) < abs(x / &3)" ASM_REAL_ARITH_TAC

/- REAL_ARITH3's NEW ERROR WRAPPER (calc_rat.ml 544): on failure it embeds the
   offending TERM (backquoted) and the inner message as
   `REAL_ARITH `<term>`: <msg>`.  A genuinely FALSE goal exercises it; assert
   the message SHAPE (prefix `REAL_ARITH ` and the embedded backquoted term). -/
#eval do
  match ← HolCore.Parser.parse_term "&0 = &1" with
  | .error e => IO.println s!"REAL_ARITH3 error-wrapper parse ERR: {e}"
  | .ok tm =>
    match ← Session.REAL_ARITH3 tm with
    | .ok th =>
      IO.println s!"REAL_ARITH3 error-wrapper -> MISMATCH unexpectedly proved: {
        squash (← HolCore.Printer.string_of_thm th)}"
    | .error e =>
      let hasPrefix := (e.splitOn "REAL_ARITH `").length > 1
      let hasTerm := (e.splitOn "&0 = &1").length > 1
      if hasPrefix && hasTerm then
        IO.println s!"REAL_ARITH3 error-wrapper -> OK (wrapped: {e})"
      else IO.println s!"REAL_ARITH3 error-wrapper -> MISMATCH shape: {e}"

/- ---------------------------------------------------------------------- -/
/- (11) THE THREE TRANSITIVITY FORMS (calc_rat.ml 560-577).                -/
/- ---------------------------------------------------------------------- -/

#eval thmCheck "REAL_LE_TRANS_LE" Session.REAL_LE_TRANS_LE
  "|- forall x y. x <= y <=> (forall z. y <= z ==> x <= z)"
#eval thmCheck "REAL_LE_TRANS_LTE" Session.REAL_LE_TRANS_LTE
  "|- forall x y. x <= y <=> (forall z. y < z ==> x <= z)"
#eval thmCheck "REAL_LE_TRANS_LT" Session.REAL_LE_TRANS_LT
  "|- forall x y. x <= y <=> (forall z. y < z ==> x < z)"

/- ---------------------------------------------------------------------- -/
/- (12) REAL_FIELD (calc_rat.ml 578-630) - the Help file's own example.    -/
/- A goal that genuinely needs DIVISION and a nonzero-denominator side      -/
/- condition, which REAL_RING alone cannot do.                             -/
/- ---------------------------------------------------------------------- -/

#eval proves "REAL_FIELD [Help]"
  "!x. &0 < x ==> &1 / x - &1 / (x + &1) = &1 / (x * (x + &1))" REAL_FIELD

/- ---------------------------------------------------------------------- -/
/- (13) THE EIGHT SHRINK/GROW THEOREMS (calc_rat.ml 631-688).              -/
/- Statements checked against calc_rat.ml.                                 -/
/- ---------------------------------------------------------------------- -/

#eval thmCheck "REAL_SHRINK_RANGE" Session.REAL_SHRINK_RANGE
  "|- forall x. abs (x / (&1 + abs x)) < &1"
#eval thmCheck "REAL_SHRINK_LT" Session.REAL_SHRINK_LT
  "|- forall x y. x / (&1 + abs x) < y / (&1 + abs y) <=> x < y"
#eval thmCheck "REAL_SHRINK_LE" Session.REAL_SHRINK_LE
  "|- forall x y. x / (&1 + abs x) <= y / (&1 + abs y) <=> x <= y"
#eval thmCheck "REAL_SHRINK_EQ" Session.REAL_SHRINK_EQ
  "|- forall x y. x / (&1 + abs x) = y / (&1 + abs y) <=> x = y"
#eval thmCheck "REAL_SHRINK_GALOIS" Session.REAL_SHRINK_GALOIS
  "|- forall x y. x / (&1 + abs x) = y <=> abs y < &1 /\\ y / (&1 - abs y) = x"
#eval thmCheck "REAL_GROW_SHRINK" Session.REAL_GROW_SHRINK
  "|- forall x. x / (&1 + abs x) / (&1 - abs (x / (&1 + abs x))) = x"
#eval thmCheck "REAL_SHRINK_GROW_EQ" Session.REAL_SHRINK_GROW_EQ
  "|- forall x. x / (&1 - abs x) / (&1 + abs (x / (&1 - abs x))) = x <=> abs x < &1"
#eval thmCheck "REAL_SHRINK_GROW" Session.REAL_SHRINK_GROW
  ("|- forall x. abs x < &1 ==> " ++
   "x / (&1 - abs x) / (&1 + abs (x / (&1 - abs x))) = x")
