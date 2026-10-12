/- File: HolTest/IntTest.lean
Runtime test suite: int.ml - the integers, embedded in the reals.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

WHAT THIS FILE VERIFIES, ABOVE ALL.  int.ml is loaded (hol_lib.ml 98) with
`prioritize_int()` (int.ml 70) in force for its whole 2700-line body, and closes
with `prioritize_num()` (int.ml 2765) - the VERY LAST effect - to RESTORE `num`
as the default for overloaded symbols.  The two assertions this file exists for:

  1. THE PARSER PRIORITY REVERTS TO `num`.  After the int layer has fully run
     (including `prioritize_num`), a SCHEMATIC arithmetic term with no type
     annotation - `x + y = y + x` - must parse at type `:num`, NOT `:int`,
     exactly as HOL Light leaves the parser after loading int.ml.  A closed
     numeral term like `1 + 2` is NOT sufficient to detect this (its numerals
     pin the type), so the probe is deliberately schematic.  Miss or misplace
     `prioritize_num` and this comes out `:int` - defect class #5, the same
     failure that once panicked the bootstrap (`setupWf failed: tryfind`).

  2. `INT_ARITH2` SUPERSEDES `INT_ARITH1`.  int.ml 2190's banner is "Enhanced
     integer procedures eliminating div and rem (replacing first one)".  The
     enhanced `INT_ARITH2` (= the unnumbered `INT_ARITH`) gains an
     `INT_DIVREM_ELIM_CONV` link that the bootstrapping `INT_ARITH1` lacks, so a
     goal mentioning `rem` is DECIDED by `INT_ARITH2` and FAILS under
     `INT_ARITH1` (which leaves `rem` as an opaque atom).  This is the project's
     self-documenting-contrast convention (cf. REAL_ARITH2 vs REAL_ARITH3 in
     CalcRatTest.lean, and INTEGER_RULE1 vs INTEGER_RULE2 in section 3 below).

The remaining sections sample the 276 lifted theorems (section 4), the int type
and operation bridge theorems, the numeral conversions, INT_POLY_CONV, INT_RING,
INT_RED_CONV/INT_COMPUTE_CONV, the rem conversions, ARITH_RULE/ASM_ARITH_TAC,
NUMBER_TAC, gcd/lcm/Bezout, prime, real_zpow and num_of_int (section 5), and
verify the worked examples of the shipping .hlp entries at runtime (section 6).

`&` is `int_of_num`/`real_of_num` (the injection of the naturals); `rem`/`div`
are the Euclidean remainder/quotient on `:int`.
-/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- FORCING THE REAL + CALC_RAT LAYERS FIRST IS MANDATORY.                  -/
/-                                                                        -/
/- hol_lib.ml loads real.ml (96) and calc_rat.ml (97) BEFORE int.ml (98),  -/
/- so every real proof is elaborated while `num` is still the default and  -/
/- BEFORE int.ml's `prioritize_int` (int.ml 70) takes effect.  Our layers  -/
/- are LAZY, so if the int force below were the FIRST demand for a real     -/
/- bundle (e.g. `setupIntArith2` needs `REAL_ARITH3`, `setupRealZpow` needs -/
/- the real-power lemmas), that real proof would run under `int` priority   -/
/- and its `real` proforma would parse wrong - measured: `setupRealThms5`   -/
/- panics `linear_ineqs: no contradiction`.  So force the whole real chain  -/
/- here, in hol_lib.ml order, BEFORE anything int.  `realThms11` (sqrt)      -/
/- transitively pulls in every real.ml bundle; `REAL_ARITH3` pulls the      -/
/- calc_rat prover chain.  Only then is it safe to force the int layer.     -/
/- ---------------------------------------------------------------------- -/

/- Force the `num` polynomial/ring/integral decision procedures FIRST, in
   hol_lib.ml order (grobner.ml 91 is BEFORE realax.ml 93).  Their one-time
   setup proofs search over the currently-registered overloads; forcing them
   before the real layer registers the `real` overloads keeps that search small
   (forcing them AFTER blows up as `NUM_INTEGRAL: solve_goal: Too deep`). -/
#eval do
  -- arith.ml first, or `a + b` does not parse and nothing is forced.
  let _ ← (IO.mkRef (HolCore.Kernel.concl Session.ADD_SYM) : IO (IO.Ref HolCore.Kernel.term))
  match ← HolCore.Parser.parse_term "(a + b) * c = a * c + b * c" with
  | .ok tm => let _ ← Session.NUM_RING tm; IO.println "NUM_RING forced"
  | .error e => IO.println s!"NUM_RING force -> MISMATCH parse ERR: {e}"

#eval Session.realThms1.REAL_OF_NUM_LT
#eval Session.realThms5.REAL_LE_MAX
#eval Session.realThms9.REAL_ARCH_SIMPLE
#eval Session.realThms11.SQRT_0
#eval do
  match ← HolCore.Parser.parse_term "&0 <= &0" with
  | .ok tm => let _ ← Session.REAL_ARITH3 tm; IO.println "real+calc_rat forced"
  | .error e => IO.println s!"real force parse ERR: {e}"

/- ---------------------------------------------------------------------- -/
/- FORCING THE INT LAYER (INCLUDING prioritize_num) FIRST IS MANDATORY.    -/
/-                                                                        -/
/- With the real layer already built (above), reading `ensurePrioritizeNum`-/
/- now drives ONLY the int chain in int.ml's own order: it forces the       -/
/- whole int layer under `prioritize_int` (int.ml 70), then runs            -/
/- `prioritize_num()` (int.ml 2765) LAST, so afterwards the parser default  -/
/- is `num`, matching a fully loaded int.ml.  This `#eval` MUST come before -/
/- every schematic parse below.                                            -/
/- ---------------------------------------------------------------------- -/

#eval Session.ensurePrioritizeNum

/-- Squash whitespace so a printed theorem can be compared against a
    single-line expected string. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

/-- Compare a theorem against an expected printed form. -/
private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  IO.println s!"[start] {lbl}"
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/-- Parse a term and compare BOTH its printed form and its type.  Used for the
    parser-priority check, where the TYPE is the whole point. -/
private unsafe def parseCheck (lbl expr expTm expTy : String) : IO Unit := do
  IO.println s!"[start] {lbl}"
  match ← HolCore.Parser.parse_term expr with
  | .error e => IO.println s!"{lbl} -> PARSE FAILED: {e}"
  | .ok tm =>
    let gotTm := squash (← HolCore.Printer.string_of_term tm)
    let gotTy := squash (← HolCore.Printer.string_of_type (type_of tm))
    if gotTm == squash expTm && gotTy == squash expTy then
      IO.println s!"{lbl} -> OK (type {gotTy})"
    else IO.println s!"{lbl} -> MISMATCH got={gotTm} : {gotTy}"

/-- Parse `goal`, run a `term → IO (Except String thm)` decision procedure,
    assert it PROVES the goal with NO hypotheses. -/
private unsafe def proves (lbl goal : String)
    (proc : term → IO (Except String thm)) : IO Unit := do
  IO.println s!"[start] {lbl}"
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

/-- Parse `goal`, run a TACTIC via `Session.prove`, assert it PROVES the goal. -/
private unsafe def provesTac (lbl goal : String) (tac : HolCore.Tactics.tactic) : IO Unit := do
  IO.println s!"[start] {lbl}"
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

/-- Prove `goal` from assumptions `asms` via a tactic that absorbs a leading
    implication (`REPEAT DISCH_TAC THEN tac`).  Builds `asm1 ==> ... ==> goal`,
    proves it, and asserts success. -/
private unsafe def provesAsm (lbl : String) (asms : List String) (goal : String)
    (tac : HolCore.Tactics.tactic) : IO Unit := do
  IO.println s!"[start] {lbl}"
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

/-- Assert a `term → IO (Except String thm)` procedure FAILS on `goal`.  Used
    for the INT_ARITH1-cannot-do-div/rem and INTEGER_RULE1-cannot-do-gcd halves
    of the supersession contrasts. -/
private unsafe def procFails (lbl goal : String)
    (proc : term → IO (Except String thm)) : IO Unit := do
  IO.println s!"[start] {lbl}"
  match ← HolCore.Parser.parse_term goal with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok tm =>
    match ← proc tm with
    | .error e => IO.println s!"{lbl} -> OK (correctly fails: {e})"
    | .ok th =>
      IO.println s!"{lbl} -> MISMATCH unexpectedly proved: {
        squash (← HolCore.Printer.string_of_thm th)}"

/-- Parse `expr`, apply a conversion, compare the resulting theorem. -/
private unsafe def convCheck (lbl expr expected : String) (c : ioconv) : IO Unit := do
  IO.println s!"[start] {lbl}"
  match ← HolCore.Parser.parse_term expr with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok tm =>
    match ← c tm with
    | .error e => IO.println s!"{lbl} ERR: {e}"
    | .ok th =>
      let got := squash (← HolCore.Printer.string_of_thm th)
      if got == squash expected then IO.println s!"{lbl} -> OK"
      else IO.println s!"{lbl} -> MISMATCH got={got}"

/- ====================================================================== -/
/- (1) THE HEADLINE ASSERTION: PARSER PRIORITY REVERTS TO `num`.           -/
/- ====================================================================== -/

/- A SCHEMATIC term (no annotation) must parse at `:num`, not `:int`, after
   `prioritize_num` has run.  `x`/`y` are free variables; the overloaded `+`
   and `=` resolve to their `num` instances because `num` is again the default.
   If `prioritize_num` were missing or misplaced, `int` priority (int.ml 70)
   would still be in force and these would come out `:int` (`x`,`y` : int). -/
#eval parseCheck "schematic `x + y = y + x` is num" "x + y = y + x"
  "x + y = y + x" "bool"
#eval parseCheck "schematic addend `x + y` is num" "x + y" "x + y" "num"
#eval parseCheck "schematic bound var `\\x. x + 1` is num"
  "\\x. x + 1" "\\x. x + 1" "num->num"

/- CONTRAST: an EXPLICITLY int-annotated term still parses at `:int` - the int
   overloads remain REGISTERED (int.ml never removed them); `prioritize_num`
   only changes the DEFAULT for un-annotated schematic terms. -/
#eval parseCheck "annotated `x + y:int` stays int" "x + y:int" "x + y" "int"

/- ====================================================================== -/
/- (2) THE OTHER HEADLINE ASSERTION: INT_ARITH2 SUPERSEDES INT_ARITH1.     -/
/- The distinguishing goal (Int.lean's own suggested contrast): a `rem`    -/
/- goal.  INT_ARITH2 (= the unnumbered INT_ARITH) clears the `rem` via     -/
/- INT_DIVREM_ELIM_CONV and PROVES it; INT_ARITH1 has no div/rem           -/
/- elimination and FAILS.                                                  -/
/- ====================================================================== -/

#eval proves "INT_ARITH2 proves rem goal"
  "!m:int. m rem &2 = &0 \\/ m rem &2 = &1" Session.INT_ARITH2
#eval procFails "INT_ARITH1 fails the same rem goal"
  "!m:int. m rem &2 = &0 \\/ m rem &2 = &1" Session.INT_ARITH1
/- The unnumbered `INT_ARITH` is the enhanced version (int.ml 2190 "replacing
   first one"), so it too proves the rem goal - confirming the alias points at
   v2, not v1. -/
#eval proves "INT_ARITH (unnumbered) = v2, proves rem goal"
  "!m:int. m rem &2 = &0 \\/ m rem &2 = &1" Session.INT_ARITH

/- ====================================================================== -/
/- (3) THE INTEGER_RULE1 vs INTEGER_RULE2 CONTRAST (already established).   -/
/- int.ml defines INTEGER_TAC/RULE twice: v1 (int.ml 1224-1327) handles     -/
/- divides/coprime/congruence but NOT gcd/lcm; v2 (int.ml 2045/2064)        -/
/- REPLACES it, adding gcd/lcm elimination.  So `gcd(a,b) divides a` is     -/
/- decided by INTEGER_RULE2 and FAILS under INTEGER_RULE1 (which cannot     -/
/- unfold `gcd`).  Assert BOTH outcomes on the SAME goal.                   -/
/- ====================================================================== -/

#eval proves "INTEGER_RULE2 proves gcd divides"
  "!a b:int. gcd(a,b) divides a" Session.INTEGER_RULE2
#eval procFails "INTEGER_RULE1 fails the same gcd goal"
  "!a b:int. gcd(a,b) divides a" Session.INTEGER_RULE1
/- The unnumbered INTEGER_RULE aliases v2, so it proves it too. -/
#eval proves "INTEGER_RULE (unnumbered) = v2, proves gcd divides"
  "!a b:int. gcd(a,b) divides a" Session.INTEGER_RULE

/- ====================================================================== -/
/- (4) A REPRESENTATIVE SAMPLE OF THE 276 LIFTED THEOREMS (int.ml 325-618). -/
/- The failure mode: a lift that silently stayed about `real` - it would    -/
/- typecheck and print plausibly.  So assert the ACTUAL integer statements   -/
/- (each `&` here is `int_of_num`, each variable `:int`), spanning the whole -/
/- range and deliberately including abs/max/min/pow, a conditional and a     -/
/- conjunction.  (IntLeakCheck.lean separately walks all 276 ASTs for        -/
/- residual `real_` constants; this file asserts the printed statements.)    -/
/- ====================================================================== -/

/- abs family (int.ml 325-350). -/
#eval thmCheck "INT_ABS_NUM" Session.INT_ABS_NUM "|- forall n. abs (&n) = &n"
#eval thmCheck "INT_ABS_NEG" Session.INT_ABS_NEG "|- forall x. abs (--x) = abs x"
#eval thmCheck "INT_ABS_MUL" Session.INT_ABS_MUL
  "|- forall x y. abs (x * y) = abs x * abs y"
#eval thmCheck "INT_ABS_TRIANGLE" Session.INT_ABS_TRIANGLE
  "|- forall x y. abs (x + y) <= abs x + abs y"
/- abs with a conjunction (INT_ABS_BOUNDS). -/
#eval thmCheck "INT_ABS_BOUNDS" Session.INT_ABS_BOUNDS
  "|- forall x k. abs x <= k <=> --k <= x /\\ x <= k"
/- add/entire/diffsq. -/
#eval thmCheck "INT_ADD_SYM" Session.INT_ADD_SYM "|- forall x y. x + y = y + x"
#eval thmCheck "INT_ENTIRE" Session.INT_ENTIRE
  "|- forall x y. x * y = &0 <=> x = &0 \\/ y = &0"
#eval thmCheck "INT_DIFFSQ" Session.INT_DIFFSQ
  "|- forall x y. (x + y) * (x - y) = x * x - y * y"
/- le/lt family, including the pow-square and cancellation shapes. -/
#eval thmCheck "INT_LE_SQUARE" Session.INT_LE_SQUARE "|- forall x. &0 <= x * x"
#eval thmCheck "INT_LE_MUL2" Session.INT_LE_MUL2
  "|- forall w x y z. &0 <= w /\\ w <= x /\\ &0 <= y /\\ y <= z ==> w * y <= x * z"
#eval thmCheck "INT_LT_LADD" Session.INT_LT_LADD "|- forall x y z. x + y < x + z <=> y < z"
/- max/min family - the shapes most at risk of a silent real leak. -/
#eval thmCheck "INT_LE_MAX" Session.INT_LE_MAX
  "|- forall x y z. z <= max x y <=> z <= x \\/ z <= y"
#eval thmCheck "INT_MIN_LE" Session.INT_MIN_LE
  "|- forall x y z. min x y <= z <=> x <= z \\/ y <= z"
#eval thmCheck "INT_MAX_SYM" Session.INT_MAX_SYM "|- forall x y. max x y = max y x"
/- neg/mul. -/
#eval thmCheck "INT_NEG_NEG" Session.INT_NEG_NEG "|- forall x. ----x = x"
#eval thmCheck "INT_MUL_SYM" Session.INT_MUL_SYM "|- forall x y. x * y = y * x"
/- of_num bridges (a conditional lives in INT_OF_NUM_SUB_CASES). -/
#eval thmCheck "INT_OF_NUM_ADD" Session.INT_OF_NUM_ADD
  "|- forall m n. &m + &n = &(m + n)"
#eval thmCheck "INT_OF_NUM_SUB_CASES" Session.INT_OF_NUM_SUB_CASES
  "|- forall m n. &m - &n = (if n <= m then &(m - n) else --&(n - m))"
/- pow family (pow appears literally). -/
#eval thmCheck "INT_POW_ADD" Session.INT_POW_ADD
  "|- forall x m n. x pow (m + n) = x pow m * x pow n"
#eval thmCheck "INT_POW_2" Session.INT_POW_2 "|- forall x. x pow 2 = x * x"
#eval thmCheck "INT_POW_MUL" Session.INT_POW_MUL
  "|- forall x y n. (x * y) pow n = x pow n * y pow n"
/- sgn family (a nested conditional). -/
#eval thmCheck "INT_SGN" Session.INT_SGN
  "|- forall x. int_sgn x = (if &0 < x then &1 else if x < &0 then --&1 else &0)"
/- sub family, spanning the end of the lifted range (int.ml ~590-618). -/
#eval thmCheck "INT_SUB_REFL" Session.INT_SUB_REFL "|- forall x. x - x = &0"
#eval thmCheck "INT_SUB_TRIANGLE" Session.INT_SUB_TRIANGLE
  "|- forall a b c. a - b + b - c = a - c"

/- ====================================================================== -/
/- (5) DEFINITIONS, OPERATIONS, CONVERSIONS AND PROCEDURES (int.ml body).   -/
/- ====================================================================== -/

/- (5a) int_tybij and the int type (int.ml 76). -/
#eval thmCheck "int_tybij" Session.int_tybij
  ("|- (forall a. int_of_real (real_of_int a) = a) /\\ " ++
   "(forall r. integer r <=> real_of_int (int_of_real r) = r)")
#eval thmCheck "integer (defn)" Session.integer
  "|- forall x. integer x <=> (exists n. abs x = &n)"

/- (5b) The fourteen operations' `int_<op>_th` bridge theorems (int.ml 76-257).
   Each states that `real_of_int` distributes over the int operation - the very
   equations INT_OF_REAL_THM rewrites under.  Sample five, incl. neg/add/mul. -/
#eval thmCheck "int_add_th" Session.int_add_th
  "|- forall x y. real_of_int (x + y) = real_of_int x + real_of_int y"
#eval thmCheck "int_mul_th" Session.int_mul_th
  "|- forall x y. real_of_int (x * y) = real_of_int x * real_of_int y"
#eval thmCheck "int_neg_th" Session.int_neg_th
  "|- forall x. real_of_int (--x) = --real_of_int x"
#eval thmCheck "int_of_num_th" Session.int_of_num_th
  "|- forall n. real_of_int (&n) = &n"
#eval thmCheck "int_abs_th" Session.int_abs_th
  "|- forall x. real_of_int (abs x) = abs (real_of_int x)"

/- (5c) The nine INT_*_CONV arithmetic conversions + five relational ones,
   plus INT_NEG_CONV, on integer numerals (int.ml 871-1084). -/
#eval convCheck "INT_ADD_CONV &2 + &3" "&2 + &3" "|- &2 + &3 = &5" INT_ADD_CONV
#eval convCheck "INT_MUL_CONV &3 * &4" "&3 * &4" "|- &3 * &4 = &12" INT_MUL_CONV
#eval convCheck "INT_SUB_CONV &7 - &10" "&7 - &10" "|- &7 - &10 = --&3" INT_SUB_CONV
#eval convCheck "INT_NEG_CONV --(&5)" "--(&5)" "|- --&5 = --&5" INT_NEG_CONV
#eval convCheck "INT_POW_CONV &2 pow 5" "&2 pow 5" "|- &2 pow 5 = &32" INT_POW_CONV
#eval convCheck "INT_ABS_CONV abs(--(&6))" "abs(--(&6))" "|- abs (--&6) = &6" INT_ABS_CONV
#eval convCheck "INT_MAX_CONV max (&3) (&8)" "max (&3) (&8)" "|- max (&3) (&8) = &8" INT_MAX_CONV
#eval convCheck "INT_MIN_CONV min (&3) (&8)" "min (&3) (&8)" "|- min (&3) (&8) = &3" INT_MIN_CONV
#eval convCheck "INT_LE_CONV &3 <= &5" "&3 <= &5" "|- &3 <= &5 <=> true" INT_LE_CONV
#eval convCheck "INT_LT_CONV &5 < &3" "&5 < &3" "|- &5 < &3 <=> false" INT_LT_CONV
#eval convCheck "INT_EQ_CONV &4 = &4" "&4 = &4" "|- &4 = &4 <=> true" INT_EQ_CONV
#eval convCheck "INT_GT_CONV &5 > &3" "&5 > &3" "|- &5 > &3 <=> true" INT_GT_CONV
#eval convCheck "INT_GE_CONV &3 >= &5" "&3 >= &5" "|- &3 >= &5 <=> false" INT_GE_CONV
#eval convCheck "INT_SGN_CONV int_sgn(--(&4))" "int_sgn(--(&4))"
  "|- int_sgn (--&4) = --&1" INT_SGN_CONV

/- (5d) INT_RED_CONV / INT_REDUCE_CONV / INT_COMPUTE_CONV (int.ml 1821-1835).
   `INT_RED_CONV` is a SINGLE reduction step - `REWRITES_CONV` over the
   sixteen-entry net - so it folds `&2 + &3` but FAILS on a compound whose
   arguments are not yet numerals, exactly as the OCaml does.
   `INT_REDUCE_CONV` is `DEPTH_CONV INT_RED_CONV` and folds the compound.
   NOTE THE `:int` ANNOTATIONS BELOW ARE LOAD-BEARING.  int.ml 2765 calls
   `prioritize_num`, so by the end of the file a schematic `&`-numeral term
   parses as `num` - see (1) above - and an INTEGER reducer then correctly
   declines to touch it.  An earlier draft of this test omitted the annotation
   and mistook that for a defect in the reducers; they are in fact correct. -/
#eval convCheck "INT_RED_CONV single step &2 + &3"
  "(&2 + &3):int" "|- &2 + &3 = &5" INT_RED_CONV
#eval procFails "INT_RED_CONV is one step only, so a compound FAILS"
  "((&2 + &3) * &4):int" INT_RED_CONV
#eval convCheck "INT_REDUCE_CONV compound folds"
  "((&2 + &3) * &4 - &5):int" "|- (&2 + &3) * &4 - &5 = &15"
  INT_REDUCE_CONV
#eval convCheck "INT_COMPUTE_CONV compound folds"
  "((&2 + &3) * &4 - &5):int" "|- (&2 + &3) * &4 - &5 = &15"
  INT_COMPUTE_CONV

/- (5e) INT_POLY_CONV: normalise a polynomial (int.ml 1090). -/
#eval convCheck "INT_POLY_CONV (x + y) pow 2" "(x + y:int) pow 2"
  "|- (x + y) pow 2 = x pow 2 + &2 * x * y + y pow 2" INT_POLY_CONV

/- (5f) INT_RING (int.ml 1122) - Brahmagupta's identity (from INT_RING.hlp,
   verified at runtime in section 6; here a smaller ring identity). -/
#eval proves "INT_RING difference of squares"
  "!x y:int. (x + y) * (x - y) = x pow 2 - y pow 2" Session.INT_RING

/- (5g) INT_REM_DOWN_CONV and INT_POW_REM_CONV (int.ml 1880-1928).
   INT_REM_DOWN_CONV COMBINES the nested `rem`s down to a single outer `rem`
   (here `(&7 + &9) rem &12`); it does not itself evaluate the resulting sum.
   INT_POW_REM_CONV reduces `(a pow k) rem n` to a numeral. -/
#eval convCheck "INT_REM_DOWN_CONV nested rem"
  "(&7 rem &12 + &9 rem &12) rem &12"
  "|- (&7 rem &12 + &9 rem &12) rem &12 = (&7 + &9) rem &12"
  INT_REM_DOWN_CONV
#eval convCheck "INT_POW_REM_CONV (a pow k) rem n"
  "(&3 pow 4) rem &5" "|- &3 pow 4 rem &5 = &1" INT_POW_REM_CONV

/- (5h) ARITH_RULE / ARITH_TAC / ASM_ARITH_TAC (int.ml 2153, banner "Linear
   decision procedure for the naturals at last!").  Includes a TRUNCATED-
   natural-subtraction goal (SUC c - SUC(..) <= c) from ARITH_RULE.hlp. -/
#eval proves "ARITH_RULE linear num" "!x y:num. x = 1 ==> y <= 1 \\/ x < y"
  Session.ARITH_RULE
#eval proves "ARITH_RULE truncated subtraction"
  "2 * a * b EXP 2 <= b * a * b ==> (SUC c - SUC(a * b * b) <= c)"
  Session.ARITH_RULE
#eval provesTac "ARITH_TAC via tactic" "!m n:num. m + n = n + m" Session.ARITH_TAC
#eval provesAsm "ASM_ARITH_TAC uses assumption" ["x + 1 <= y"] "x < y:num"
  Session.ASM_ARITH_TAC

/- (5i) NUMBER_TAC / NUMBER_RULE (int.ml 2503) - a divisibility fact. -/
#eval proves "NUMBER_RULE divides-refl" "!n:num. n divides n" Session.NUMBER_RULE
#eval provesTac "NUMBER_TAC coprime moduli"
  ("!m n x y:num. (x == y) (mod m) /\\ (x == y) (mod n) /\\ coprime(m,n) " ++
   "==> (x == y) (mod (m * n))") Session.NUMBER_TAC

/- (5j) gcd/lcm/Bezout (int.ml 1929-2067).  `int_gcd` (via new_specification)
   is characterised by nonnegativity, divisibility of both args, and a Bezout
   witness; `INT_LCM` gives lcm's dual divisibility characterisation. -/
#eval thmCheck "int_gcd (spec)" Session.int_gcd
  ("|- forall a b. &0 <= gcd (a,b) /\\ gcd (a,b) divides a /\\ gcd (a,b) divides b /\\ " ++
   "(exists x y. gcd (a,b) = a * x + b * y)")
#eval thmCheck "INT_LCM (characterisation)" Session.INT_LCM
  ("|- forall m n. m divides lcm (m,n) /\\ n divides lcm (m,n) /\\ " ++
   "(forall d. m divides d /\\ n divides d ==> lcm (m,n) divides d)")
/- Bezout: gcd is an integer combination - the defining existence. -/
#eval proves "gcd Bezout via INTEGER_RULE"
  "!a b:int. ?x y. gcd(a,b) = a * x + b * y" Session.INTEGER_RULE

/- (5k) prime (int.ml 2571). -/
#eval thmCheck "prime (defn)" Session.prime
  "|- forall p. prime p <=> ~(p = 1) /\\ (forall x. x divides p ==> x = 1 \\/ x = p)"

/- (5l) real_zpow (int.ml 2633) - the definition and the &n bridge. -/
#eval thmCheck "real_zpow (defn)" Session.real_zpow
  ("|- forall z i. z zpow i = " ++
   "(if &0 <= i then z pow num_of_int i else inv (z pow num_of_int (--i)))")
#eval thmCheck "REAL_ZPOW_NUM" Session.REAL_ZPOW_NUM "|- forall x n. x zpow &n = x pow n"

/- (5m) num_of_int (int.ml 2070). -/
#eval thmCheck "num_of_int (defn)" Session.num_of_int
  "|- forall x. num_of_int x = (@n. &n = x)"
#eval thmCheck "NUM_OF_INT_OF_NUM" Session.NUM_OF_INT_OF_NUM
  "|- forall n. num_of_int (&n) = n"

/- (5n) INT_REM_REM_POW_MIN (int.ml 2358): its proof's last step is the
   ENHANCED ASM_INT_ARITH_TAC2 - a correct statement is evidence IMn used v2. -/
#eval thmCheck "INT_REM_REM_POW_MIN" Session.INT_REM_REM_POW_MIN
  "|- forall x p m n. x rem p pow m rem p pow n = x rem p pow MIN m n"

/- ====================================================================== -/
/- (6) HELP-FILE EXAMPLES VERIFIED AT RUNTIME (hol-light/Help/*.hlp).       -/
/- Every worked example below is transcribed VERBATIM from the shipping     -/
/- .hlp entry and asserted to hold under the live procedure.  A mismatch    -/
/- would mean either the translation or the documentation is wrong; the     -/
/- verdict is reported in the summary.                                      -/
/- ====================================================================== -/

/- ARITH_RULE.hlp - all three worked examples. -/
#eval proves "ARITH_RULE.hlp ex1" "x = 1 ==> y <= 1 \\/ x < y" Session.ARITH_RULE
#eval proves "ARITH_RULE.hlp ex2" "x <= 127 ==> ((86 * x) DIV 256 = x DIV 3)"
  Session.ARITH_RULE
#eval proves "ARITH_RULE.hlp ex3"
  "2 * a * b EXP 2 <= b * a * b ==> (SUC c - SUC(a * b * b) <= c)"
  Session.ARITH_RULE

/- INT_ARITH.hlp - both worked examples. -/
#eval proves "INT_ARITH.hlp ex1" "!x y:int. x <= y + &1 ==> x + &2 < y + &4"
  Session.INT_ARITH
#eval proves "INT_ARITH.hlp ex2"
  "(x + y:int) pow 2 = x pow 2 + &2 * x * y + y pow 2" Session.INT_ARITH

/- INT_RING.hlp - Brahmagupta's identity (the degenerate-case example) and the
   negative control `x pow 2 = &2 ==> F`, which the doc states INT_RING CANNOT
   prove (not valid in all integral domains). -/
#eval proves "INT_RING.hlp Brahmagupta"
  ("(a pow 2 + b pow 2) * (c pow 2 + d pow 2) = " ++
   "(a * c - b * d) pow 2 + (a * d + b * c) pow 2") Session.INT_RING
#eval procFails "INT_RING.hlp x pow 2 = &2 ==> F (doc says CANNOT)"
  "x pow 2 = &2 ==> F" Session.INT_RING

/- INTEGER_RULE.hlp - two of its worked examples. -/
#eval proves "INTEGER_RULE.hlp congruence-divides"
  "!x y n:int. (x == y) (mod n) ==> (n divides x <=> n divides y)"
  Session.INTEGER_RULE
#eval proves "INTEGER_RULE.hlp d divides gcd"
  "!a b d:int. d divides gcd(a,b) <=> d divides a /\\ d divides b"
  Session.INTEGER_RULE

/- INTEGER_TAC.hlp - the resultant-divisibility example. -/
#eval provesTac "INTEGER_TAC.hlp resultant"
  ("!c2 c1 c0 n x:int. (c0 * x == c1) (mod n) /\\ (c1 * x == c2) (mod n) " ++
   "==> n divides (c1 * c1 - c0 * c2)") Session.INTEGER_TAC

/- INT_ARITH_TAC.hlp - both worked examples (algebraic + linear inequality). -/
#eval provesTac "INT_ARITH_TAC.hlp linear-abs"
  "!x y:int. abs(x + y) < abs(x) + abs(y) + &1" Session.INT_ARITH_TAC

/- ASM_INT_ARITH_TAC.hlp - the doc shows INT_ARITH_TAC FAILING on the stripped
   goal and ASM_INT_ARITH_TAC SUCCEEDING using the assumptions.  Assert both. -/
#eval provesAsm "ASM_INT_ARITH_TAC.hlp uses asms"
  ["x <= y", "&2 * y <= &2 * x + &1"] "x = y:int" Session.ASM_INT_ARITH_TAC
#eval proves "ASM_INT_ARITH_TAC.hlp whole goal via INT_ARITH"
  "!x y:int. x <= y /\\ &2 * y <= &2 * x + &1 ==> x = y" Session.INT_ARITH

/- NUMBER_RULE.hlp - the gcd/coprime worked example. -/
#eval proves "NUMBER_RULE.hlp gcd-coprime"
  ("!a b a' b'. ~(gcd(a,b) = 0) /\\ a = a' * gcd(a,b) /\\ b = b' * gcd(a,b) " ++
   "==> coprime(a',b')") Session.NUMBER_RULE

/- NUMBER_TAC.hlp - the coprime-moduli example (already exercised in 5i via the
   same goal; here through the documented tactic path for the .hlp record). -/
#eval provesTac "NUMBER_TAC.hlp coprime-moduli"
  ("!m n x y:num. (x == y) (mod m) /\\ (x == y) (mod n) /\\ coprime(m,n) " ++
   "==> (x == y) (mod (m * n))") Session.NUMBER_TAC

/- ---------------------------------------------------------------------- -/
/- A FIFTH HOL Light Help-file fault, found while auditing int.ml.        -/
/- ---------------------------------------------------------------------- -/

/- `Help/INT_REDUCE_CONV.hlp` is a CLONE of `Help/REAL_RAT_REDUCE_CONV.hlp`
   with incomplete adaptation - the same fault mode as
   `Help/REAL_INT_NEG_CONV.hlp` (which copied `REAL_RAT_NEG_CONV.hlp`'s example
   verbatim, leaving a rational argument on an integer-only conversion).
   Three defects, all in the prose; the worked EXAMPLE is correct and is
   asserted below.

   (a) Its DESCRIBE is near-verbatim from the rational entry and carries over
       the operator list UNCHANGED, so it claims `INT_REDUCE_CONV` evaluates
       the unary `inv` and the binary `/`.  THE INTEGERS HAVE NEITHER.  int.ml
       61-70's interface map registers no `inv` and no `/`, and neither is
       among `int_red_conv_list`'s sixteen entries (int.ml 1804-1819).  They are
       not merely absent but UNWRITABLE at `:int` - both are real-only, so
       `inv(&4):int` and `(&6 / &3):int` fail to TYPECHECK, with
       "inv cannot have type real->real and real->int simultaneously" and the
       corresponding message for `/`.
   (b) That same DESCRIBE OMITS five operators the net does handle: `div`,
       `rem`, `int_sgn`, `max` and `min`.
   (c) Its COMMENTS section is self-referential - "The corresponding
       {INT_REDUCE_CONV} works for the type of integers" appears in
       INT_REDUCE_CONV's OWN entry - and then states that
       `REAL_RAT_REDUCE_CONV` "works similarly over {:int}", when that
       conversion works over `:real`.

   A LESSER, SEPARATE incompleteness: `Help/INT_RED_CONV.hlp`'s DESCRIBE lists
   eleven term forms but the net has sixteen entries, omitting `int_sgn`, `div`,
   `rem`, `max` and `min`.  That is an omission rather than a false statement,
   so it is not counted among the faults. -/
#eval convCheck "INT_REDUCE_CONV.hlp worked example (the hlp's one correct part)"
  "if &5 pow 4 < &4 pow 5 then (&2 pow 3 - &1) pow 2 + &1 else &99"
  ("|- (if &5 pow 4 < &4 pow 5 then (&2 pow 3 - &1) pow 2 + &1 else &99) " ++
   "= &50") INT_REDUCE_CONV

/- ====================================================================== -/
/- (7) THE 276-LIFT REAL-LEAK SWEEP.                                       -/
/-                                                                         -/
/- Merged in from what was a separate HolTest/IntLeakCheck.lean.  It was    -/
/- the ONLY module in HolTest/ not named `<Source>Test`, and that is        -/
/- exactly why it sat ORPHANED - nothing imported it, so its check never    -/
/- ran, and the "one Test module per source file" sweep could not see it    -/
/- was missing.  Folding it in removes that failure mode outright.          -/
/-                                                                         -/
/- It walks the raw AST of all 276 lifted `INT_*` statements and asserts    -/
/- no constant name contains `real_`.  That is THE correctness property     -/
/- for int.ml's lifted half: a lift that failed to rewrite would stay       -/
/- about `real` yet typecheck and print plausibly, so only a mechanical     -/
/- sweep catches it.  It also flags DEGENERATE conclusions, which would     -/
/- otherwise false-pass, and validates its own detector first.              -/
/- ====================================================================== -/
namespace HolTest.IntLeakCheck

/-- Collect every `Const` name occurring in a term (raw AST walk). -/
partial def constNames : term → List String
  | .Var _ _      => []
  | .Const c _    => [c]
  | .Comb f x     => constNames f ++ constNames x
  | .Abs v b      => constNames v ++ constNames b

/-- The `real_`-leaking constant names in a theorem's conclusion. -/
def realLeaks (th : thm) : List String :=
  (constNames (concl th)).filter (fun c => (c.splitOn "real_").length > 1)

/-- A conclusion is DEGENERATE (a masked failure: panicked setup -> Inhabited
    default, printing `|-  = `) when its only constant is `=` (the two operands
    are the empty-named `Var ""`). -/
def isDegenerate (th : thm) : Bool :=
  let cs := constNames (concl th)
  cs.isEmpty || cs.all (fun c => c == "=")

/- ---------------------------------------------------------------------- -/
/- WARM-UP: force the real bundles RT1..RT11.  The four this file needs    -/
/- that the module header has not already forced are RT2, RT3, RT4, RT6,    -/
/- RT7, RT8 and RT10; re-forcing a memoised CAF is a no-op, so the full     -/
/- list is kept for self-documentation.  NOTE the ordering remark below is  -/
/- inherited from when this was a standalone module: the header's force     -/
/- block above already takes RT5 before RT2-RT4 and passes, so the stated   -/
/- RT1..RT4-before-RT5 constraint is NOT binding in this configuration.     -/
/- (original note follows)                                                  -/
/- WARM-UP: force the real bundles RT1..RT11 FIRST, with the correct       -/
/- `IO.mkRef (concl ...)` idiom (a bare `let _ := caf` does NOT force a     -/
/- Lean CAF - defect class #3, the very trap this file guards).  They MUST  -/
/- be forced before the int lifts pull them in, because the int lifts run   -/
/- through `prioritize_int` (which makes `:int` the schematic default) and  -/
/- REAL_ARITH2 must prove the real min/max theorems while `:real` is still  -/
/- the default.  RT1..RT4 must precede RT5 (measured).                      -/
/- ---------------------------------------------------------------------- -/
#eval show IO Unit from do
  let _ ← IO.mkRef (concl realThms1.REAL_OF_NUM_LT)
  let _ ← IO.mkRef (concl realThms2.REAL_LT_LADD)
  let _ ← IO.mkRef (concl realThms3.REAL_LE_NEGR)
  let _ ← IO.mkRef (concl realThms4.REAL_ABS_TRIANGLE)
  let _ ← IO.mkRef (concl realThms5.REAL_MAX_MIN)
  let _ ← IO.mkRef (concl realThms6.REAL_ABS_MUL)
  let _ ← IO.mkRef (concl realThms7.REAL_LT_LCANCEL_IMP)
  let _ ← IO.mkRef (concl realThms8.REAL_POW_LE_1)
  let _ ← IO.mkRef (concl realThms9.REAL_ARCH)
  let _ ← IO.mkRef (concl realThms10.real_sgn)
  let _ ← IO.mkRef (concl realThms11.sqrt)
  IO.println "[warm-up] forced RealThms1..11 (non-degenerate real sources)"

/-- The 276 lifted theorems, paired with their names. -/
unsafe def lifts : List (String × thm) :=
  [
    ("INT_ABS_0", Session.INT_ABS_0),
    ("INT_ABS_1", Session.INT_ABS_1),
    ("INT_ABS_ABS", Session.INT_ABS_ABS),
    ("INT_ABS_BETWEEN", Session.INT_ABS_BETWEEN),
    ("INT_ABS_BETWEEN1", Session.INT_ABS_BETWEEN1),
    ("INT_ABS_BETWEEN2", Session.INT_ABS_BETWEEN2),
    ("INT_ABS_BOUND", Session.INT_ABS_BOUND),
    ("INT_ABS_BOUNDS", Session.INT_ABS_BOUNDS),
    ("INT_ABS_CASES", Session.INT_ABS_CASES),
    ("INT_ABS_CIRCLE", Session.INT_ABS_CIRCLE),
    ("INT_ABS_LE", Session.INT_ABS_LE),
    ("INT_ABS_MUL", Session.INT_ABS_MUL),
    ("INT_ABS_NEG", Session.INT_ABS_NEG),
    ("INT_ABS_NUM", Session.INT_ABS_NUM),
    ("INT_ABS_NZ", Session.INT_ABS_NZ),
    ("INT_ABS_POS", Session.INT_ABS_POS),
    ("INT_ABS_POW", Session.INT_ABS_POW),
    ("INT_ABS_REFL", Session.INT_ABS_REFL),
    ("INT_ABS_SGN", Session.INT_ABS_SGN),
    ("INT_ABS_SIGN", Session.INT_ABS_SIGN),
    ("INT_ABS_SIGN2", Session.INT_ABS_SIGN2),
    ("INT_ABS_STILLNZ", Session.INT_ABS_STILLNZ),
    ("INT_ABS_SUB", Session.INT_ABS_SUB),
    ("INT_ABS_SUB_ABS", Session.INT_ABS_SUB_ABS),
    ("INT_ABS_TRIANGLE", Session.INT_ABS_TRIANGLE),
    ("INT_ABS_ZERO", Session.INT_ABS_ZERO),
    ("INT_ADD2_SUB2", Session.INT_ADD2_SUB2),
    ("INT_ADD_AC", Session.INT_ADD_AC),
    ("INT_ADD_ASSOC", Session.INT_ADD_ASSOC),
    ("INT_ADD_LDISTRIB", Session.INT_ADD_LDISTRIB),
    ("INT_ADD_LID", Session.INT_ADD_LID),
    ("INT_ADD_LINV", Session.INT_ADD_LINV),
    ("INT_ADD_RDISTRIB", Session.INT_ADD_RDISTRIB),
    ("INT_ADD_RID", Session.INT_ADD_RID),
    ("INT_ADD_RINV", Session.INT_ADD_RINV),
    ("INT_ADD_SUB", Session.INT_ADD_SUB),
    ("INT_ADD_SUB2", Session.INT_ADD_SUB2),
    ("INT_ADD_SYM", Session.INT_ADD_SYM),
    ("INT_BOUNDS_LE", Session.INT_BOUNDS_LE),
    ("INT_BOUNDS_LT", Session.INT_BOUNDS_LT),
    ("INT_DIFFSQ", Session.INT_DIFFSQ),
    ("INT_ENTIRE", Session.INT_ENTIRE),
    ("INT_EQ_ADD_LCANCEL", Session.INT_EQ_ADD_LCANCEL),
    ("INT_EQ_ADD_LCANCEL_0", Session.INT_EQ_ADD_LCANCEL_0),
    ("INT_EQ_ADD_RCANCEL", Session.INT_EQ_ADD_RCANCEL),
    ("INT_EQ_ADD_RCANCEL_0", Session.INT_EQ_ADD_RCANCEL_0),
    ("INT_EQ_IMP_LE", Session.INT_EQ_IMP_LE),
    ("INT_EQ_LCANCEL_IMP", Session.INT_EQ_LCANCEL_IMP),
    ("INT_EQ_MUL_LCANCEL", Session.INT_EQ_MUL_LCANCEL),
    ("INT_EQ_MUL_RCANCEL", Session.INT_EQ_MUL_RCANCEL),
    ("INT_EQ_NEG2", Session.INT_EQ_NEG2),
    ("INT_EQ_RCANCEL_IMP", Session.INT_EQ_RCANCEL_IMP),
    ("INT_EQ_SGN_ABS", Session.INT_EQ_SGN_ABS),
    ("INT_EQ_SQUARE_ABS", Session.INT_EQ_SQUARE_ABS),
    ("INT_EQ_SUB_LADD", Session.INT_EQ_SUB_LADD),
    ("INT_EQ_SUB_RADD", Session.INT_EQ_SUB_RADD),
    ("INT_EVENPOW_ABS", Session.INT_EVENPOW_ABS),
    ("INT_LET_ADD", Session.INT_LET_ADD),
    ("INT_LET_ADD2", Session.INT_LET_ADD2),
    ("INT_LET_ANTISYM", Session.INT_LET_ANTISYM),
    ("INT_LET_TOTAL", Session.INT_LET_TOTAL),
    ("INT_LET_TRANS", Session.INT_LET_TRANS),
    ("INT_LE_01", Session.INT_LE_01),
    ("INT_LE_ADD", Session.INT_LE_ADD),
    ("INT_LE_ADD2", Session.INT_LE_ADD2),
    ("INT_LE_ADDL", Session.INT_LE_ADDL),
    ("INT_LE_ADDR", Session.INT_LE_ADDR),
    ("INT_LE_ANTISYM", Session.INT_LE_ANTISYM),
    ("INT_LE_DOUBLE", Session.INT_LE_DOUBLE),
    ("INT_LE_LADD", Session.INT_LE_LADD),
    ("INT_LE_LADD_IMP", Session.INT_LE_LADD_IMP),
    ("INT_LE_LCANCEL_IMP", Session.INT_LE_LCANCEL_IMP),
    ("INT_LE_LMUL", Session.INT_LE_LMUL),
    ("INT_LE_LMUL_EQ", Session.INT_LE_LMUL_EQ),
    ("INT_LE_LNEG", Session.INT_LE_LNEG),
    ("INT_LE_LT", Session.INT_LE_LT),
    ("INT_LE_MAX", Session.INT_LE_MAX),
    ("INT_LE_MIN", Session.INT_LE_MIN),
    ("INT_LE_MUL", Session.INT_LE_MUL),
    ("INT_LE_MUL2", Session.INT_LE_MUL2),
    ("INT_LE_MUL_EQ", Session.INT_LE_MUL_EQ),
    ("INT_LE_NEG2", Session.INT_LE_NEG2),
    ("INT_LE_NEGL", Session.INT_LE_NEGL),
    ("INT_LE_NEGR", Session.INT_LE_NEGR),
    ("INT_LE_NEGTOTAL", Session.INT_LE_NEGTOTAL),
    ("INT_LE_POW2", Session.INT_LE_POW2),
    ("INT_LE_POW_2", Session.INT_LE_POW_2),
    ("INT_LE_RADD", Session.INT_LE_RADD),
    ("INT_LE_RCANCEL_IMP", Session.INT_LE_RCANCEL_IMP),
    ("INT_LE_REFL", Session.INT_LE_REFL),
    ("INT_LE_RMUL", Session.INT_LE_RMUL),
    ("INT_LE_RMUL_EQ", Session.INT_LE_RMUL_EQ),
    ("INT_LE_RNEG", Session.INT_LE_RNEG),
    ("INT_LE_SQUARE", Session.INT_LE_SQUARE),
    ("INT_LE_SQUARE_ABS", Session.INT_LE_SQUARE_ABS),
    ("INT_LE_SUB_LADD", Session.INT_LE_SUB_LADD),
    ("INT_LE_SUB_RADD", Session.INT_LE_SUB_RADD),
    ("INT_LE_TOTAL", Session.INT_LE_TOTAL),
    ("INT_LE_TRANS", Session.INT_LE_TRANS),
    ("INT_LNEG_UNIQ", Session.INT_LNEG_UNIQ),
    ("INT_LTE_ADD", Session.INT_LTE_ADD),
    ("INT_LTE_ADD2", Session.INT_LTE_ADD2),
    ("INT_LTE_ANTISYM", Session.INT_LTE_ANTISYM),
    ("INT_LTE_TOTAL", Session.INT_LTE_TOTAL),
    ("INT_LTE_TRANS", Session.INT_LTE_TRANS),
    ("INT_LT_01", Session.INT_LT_01),
    ("INT_LT_ADD", Session.INT_LT_ADD),
    ("INT_LT_ADD1", Session.INT_LT_ADD1),
    ("INT_LT_ADD2", Session.INT_LT_ADD2),
    ("INT_LT_ADDL", Session.INT_LT_ADDL),
    ("INT_LT_ADDNEG", Session.INT_LT_ADDNEG),
    ("INT_LT_ADDNEG2", Session.INT_LT_ADDNEG2),
    ("INT_LT_ADDR", Session.INT_LT_ADDR),
    ("INT_LT_ADD_SUB", Session.INT_LT_ADD_SUB),
    ("INT_LT_ANTISYM", Session.INT_LT_ANTISYM),
    ("INT_LT_GT", Session.INT_LT_GT),
    ("INT_LT_IMP_LE", Session.INT_LT_IMP_LE),
    ("INT_LT_IMP_NE", Session.INT_LT_IMP_NE),
    ("INT_LT_LADD", Session.INT_LT_LADD),
    ("INT_LT_LADD_IMP", Session.INT_LT_LADD_IMP),
    ("INT_LT_LCANCEL_IMP", Session.INT_LT_LCANCEL_IMP),
    ("INT_LT_LE", Session.INT_LT_LE),
    ("INT_LT_LMUL", Session.INT_LT_LMUL),
    ("INT_LT_LMUL_EQ", Session.INT_LT_LMUL_EQ),
    ("INT_LT_LNEG", Session.INT_LT_LNEG),
    ("INT_LT_MAX", Session.INT_LT_MAX),
    ("INT_LT_MIN", Session.INT_LT_MIN),
    ("INT_LT_MUL", Session.INT_LT_MUL),
    ("INT_LT_MUL2", Session.INT_LT_MUL2),
    ("INT_LT_MUL_EQ", Session.INT_LT_MUL_EQ),
    ("INT_LT_NEG2", Session.INT_LT_NEG2),
    ("INT_LT_NEGTOTAL", Session.INT_LT_NEGTOTAL),
    ("INT_LT_POW2", Session.INT_LT_POW2),
    ("INT_LT_POW_2", Session.INT_LT_POW_2),
    ("INT_LT_RADD", Session.INT_LT_RADD),
    ("INT_LT_RCANCEL_IMP", Session.INT_LT_RCANCEL_IMP),
    ("INT_LT_REFL", Session.INT_LT_REFL),
    ("INT_LT_RMUL", Session.INT_LT_RMUL),
    ("INT_LT_RMUL_EQ", Session.INT_LT_RMUL_EQ),
    ("INT_LT_RNEG", Session.INT_LT_RNEG),
    ("INT_LT_SQUARE", Session.INT_LT_SQUARE),
    ("INT_LT_SQUARE_ABS", Session.INT_LT_SQUARE_ABS),
    ("INT_LT_SUB_LADD", Session.INT_LT_SUB_LADD),
    ("INT_LT_SUB_RADD", Session.INT_LT_SUB_RADD),
    ("INT_LT_TOTAL", Session.INT_LT_TOTAL),
    ("INT_LT_TRANS", Session.INT_LT_TRANS),
    ("INT_MAX_ACI", Session.INT_MAX_ACI),
    ("INT_MAX_ASSOC", Session.INT_MAX_ASSOC),
    ("INT_MAX_LE", Session.INT_MAX_LE),
    ("INT_MAX_LT", Session.INT_MAX_LT),
    ("INT_MAX_MAX", Session.INT_MAX_MAX),
    ("INT_MAX_MIN", Session.INT_MAX_MIN),
    ("INT_MAX_SYM", Session.INT_MAX_SYM),
    ("INT_MIN_ACI", Session.INT_MIN_ACI),
    ("INT_MIN_ASSOC", Session.INT_MIN_ASSOC),
    ("INT_MIN_LE", Session.INT_MIN_LE),
    ("INT_MIN_LT", Session.INT_MIN_LT),
    ("INT_MIN_MAX", Session.INT_MIN_MAX),
    ("INT_MIN_MIN", Session.INT_MIN_MIN),
    ("INT_MIN_SYM", Session.INT_MIN_SYM),
    ("INT_MUL_2", Session.INT_MUL_2),
    ("INT_MUL_AC", Session.INT_MUL_AC),
    ("INT_MUL_ASSOC", Session.INT_MUL_ASSOC),
    ("INT_MUL_LID", Session.INT_MUL_LID),
    ("INT_MUL_LNEG", Session.INT_MUL_LNEG),
    ("INT_MUL_LZERO", Session.INT_MUL_LZERO),
    ("INT_MUL_POS_LE", Session.INT_MUL_POS_LE),
    ("INT_MUL_POS_LT", Session.INT_MUL_POS_LT),
    ("INT_MUL_RID", Session.INT_MUL_RID),
    ("INT_MUL_RNEG", Session.INT_MUL_RNEG),
    ("INT_MUL_RZERO", Session.INT_MUL_RZERO),
    ("INT_MUL_SYM", Session.INT_MUL_SYM),
    ("INT_NEG_0", Session.INT_NEG_0),
    ("INT_NEG_ADD", Session.INT_NEG_ADD),
    ("INT_NEG_EQ", Session.INT_NEG_EQ),
    ("INT_NEG_EQ_0", Session.INT_NEG_EQ_0),
    ("INT_NEG_GE0", Session.INT_NEG_GE0),
    ("INT_NEG_GT0", Session.INT_NEG_GT0),
    ("INT_NEG_LE0", Session.INT_NEG_LE0),
    ("INT_NEG_LMUL", Session.INT_NEG_LMUL),
    ("INT_NEG_LT0", Session.INT_NEG_LT0),
    ("INT_NEG_MINUS1", Session.INT_NEG_MINUS1),
    ("INT_NEG_MUL2", Session.INT_NEG_MUL2),
    ("INT_NEG_NEG", Session.INT_NEG_NEG),
    ("INT_NEG_RMUL", Session.INT_NEG_RMUL),
    ("INT_NEG_SUB", Session.INT_NEG_SUB),
    ("INT_NOT_EQ", Session.INT_NOT_EQ),
    ("INT_NOT_LE", Session.INT_NOT_LE),
    ("INT_NOT_LT", Session.INT_NOT_LT),
    ("INT_OF_NUM_ADD", Session.INT_OF_NUM_ADD),
    ("INT_OF_NUM_CLAUSES", Session.INT_OF_NUM_CLAUSES),
    ("INT_OF_NUM_EQ", Session.INT_OF_NUM_EQ),
    ("INT_OF_NUM_GE", Session.INT_OF_NUM_GE),
    ("INT_OF_NUM_GT", Session.INT_OF_NUM_GT),
    ("INT_OF_NUM_LE", Session.INT_OF_NUM_LE),
    ("INT_OF_NUM_LT", Session.INT_OF_NUM_LT),
    ("INT_OF_NUM_MAX", Session.INT_OF_NUM_MAX),
    ("INT_OF_NUM_MIN", Session.INT_OF_NUM_MIN),
    ("INT_OF_NUM_MOD", Session.INT_OF_NUM_MOD),
    ("INT_OF_NUM_MUL", Session.INT_OF_NUM_MUL),
    ("INT_OF_NUM_POW", Session.INT_OF_NUM_POW),
    ("INT_OF_NUM_SUB", Session.INT_OF_NUM_SUB),
    ("INT_OF_NUM_SUB_CASES", Session.INT_OF_NUM_SUB_CASES),
    ("INT_OF_NUM_SUC", Session.INT_OF_NUM_SUC),
    ("INT_POS", Session.INT_POS),
    ("INT_POS_EQ_SQUARE", Session.INT_POS_EQ_SQUARE),
    ("INT_POS_NZ", Session.INT_POS_NZ),
    ("INT_POW2_ABS", Session.INT_POW2_ABS),
    ("INT_POW_1", Session.INT_POW_1),
    ("INT_POW_1_LE", Session.INT_POW_1_LE),
    ("INT_POW_1_LT", Session.INT_POW_1_LT),
    ("INT_POW_2", Session.INT_POW_2),
    ("INT_POW_ADD", Session.INT_POW_ADD),
    ("INT_POW_EQ", Session.INT_POW_EQ),
    ("INT_POW_EQ_0", Session.INT_POW_EQ_0),
    ("INT_POW_EQ_1", Session.INT_POW_EQ_1),
    ("INT_POW_EQ_1_IMP", Session.INT_POW_EQ_1_IMP),
    ("INT_POW_EQ_ABS", Session.INT_POW_EQ_ABS),
    ("INT_POW_EQ_EQ", Session.INT_POW_EQ_EQ),
    ("INT_POW_EQ_ODD", Session.INT_POW_EQ_ODD),
    ("INT_POW_EQ_ODD_EQ", Session.INT_POW_EQ_ODD_EQ),
    ("INT_POW_LBOUND", Session.INT_POW_LBOUND),
    ("INT_POW_LE", Session.INT_POW_LE),
    ("INT_POW_LE2", Session.INT_POW_LE2),
    ("INT_POW_LE2_ODD", Session.INT_POW_LE2_ODD),
    ("INT_POW_LE2_ODD_EQ", Session.INT_POW_LE2_ODD_EQ),
    ("INT_POW_LE2_REV", Session.INT_POW_LE2_REV),
    ("INT_POW_LE_1", Session.INT_POW_LE_1),
    ("INT_POW_LT", Session.INT_POW_LT),
    ("INT_POW_LT2", Session.INT_POW_LT2),
    ("INT_POW_LT2_ODD", Session.INT_POW_LT2_ODD),
    ("INT_POW_LT2_ODD_EQ", Session.INT_POW_LT2_ODD_EQ),
    ("INT_POW_LT2_REV", Session.INT_POW_LT2_REV),
    ("INT_POW_LT_1", Session.INT_POW_LT_1),
    ("INT_POW_MONO", Session.INT_POW_MONO),
    ("INT_POW_MONO_LT", Session.INT_POW_MONO_LT),
    ("INT_POW_MUL", Session.INT_POW_MUL),
    ("INT_POW_NEG", Session.INT_POW_NEG),
    ("INT_POW_NZ", Session.INT_POW_NZ),
    ("INT_POW_ONE", Session.INT_POW_ONE),
    ("INT_POW_POW", Session.INT_POW_POW),
    ("INT_POW_ZERO", Session.INT_POW_ZERO),
    ("INT_RNEG_UNIQ", Session.INT_RNEG_UNIQ),
    ("INT_SGN", Session.INT_SGN),
    ("INT_SGNS_EQ", Session.INT_SGNS_EQ),
    ("INT_SGNS_EQ_ALT", Session.INT_SGNS_EQ_ALT),
    ("INT_SGN_0", Session.INT_SGN_0),
    ("INT_SGN_ABS", Session.INT_SGN_ABS),
    ("INT_SGN_ABS_ALT", Session.INT_SGN_ABS_ALT),
    ("INT_SGN_CASES", Session.INT_SGN_CASES),
    ("INT_SGN_EQ", Session.INT_SGN_EQ),
    ("INT_SGN_EQ_INEQ", Session.INT_SGN_EQ_INEQ),
    ("INT_SGN_INEQS", Session.INT_SGN_INEQS),
    ("INT_SGN_INT_SGN", Session.INT_SGN_INT_SGN),
    ("INT_SGN_MUL", Session.INT_SGN_MUL),
    ("INT_SGN_NEG", Session.INT_SGN_NEG),
    ("INT_SGN_POW", Session.INT_SGN_POW),
    ("INT_SGN_POW_2", Session.INT_SGN_POW_2),
    ("INT_SOS_EQ_0", Session.INT_SOS_EQ_0),
    ("INT_SUB_0", Session.INT_SUB_0),
    ("INT_SUB_ABS", Session.INT_SUB_ABS),
    ("INT_SUB_ADD", Session.INT_SUB_ADD),
    ("INT_SUB_ADD2", Session.INT_SUB_ADD2),
    ("INT_SUB_LDISTRIB", Session.INT_SUB_LDISTRIB),
    ("INT_SUB_LE", Session.INT_SUB_LE),
    ("INT_SUB_LNEG", Session.INT_SUB_LNEG),
    ("INT_SUB_LT", Session.INT_SUB_LT),
    ("INT_SUB_LZERO", Session.INT_SUB_LZERO),
    ("INT_SUB_NEG2", Session.INT_SUB_NEG2),
    ("INT_SUB_RDISTRIB", Session.INT_SUB_RDISTRIB),
    ("INT_SUB_REFL", Session.INT_SUB_REFL),
    ("INT_SUB_RNEG", Session.INT_SUB_RNEG),
    ("INT_SUB_RZERO", Session.INT_SUB_RZERO),
    ("INT_SUB_SUB", Session.INT_SUB_SUB),
    ("INT_SUB_SUB2", Session.INT_SUB_SUB2),
    ("INT_SUB_TRIANGLE", Session.INT_SUB_TRIANGLE)
  ]

/- ---------------------------------------------------------------------- -/
/- STEP 1: VALIDATE THE DETECTOR.  `REAL_ADD_SYM` genuinely mentions the  -/
/- real constant `real_add`, so the detector MUST report a non-empty leak -/
/- list for it; and a real lift like `INT_ADD_SYM` MUST report empty.     -/
/- ---------------------------------------------------------------------- -/
#eval show IO Unit from do
  let realLeakSample := realLeaks Session.REAL_ADD_SYM
  let intSample := realLeaks Session.INT_ADD_SYM
  IO.println s!"[detector-validation] REAL_ADD_SYM leaks (want NON-empty): {realLeakSample}"
  IO.println s!"[detector-validation] INT_ADD_SYM leaks (want empty):     {intSample}"
  if realLeakSample.isEmpty then
    IO.eprintln "DETECTOR BROKEN: failed to flag REAL_ADD_SYM's real_add"
  else if !intSample.isEmpty then
    IO.eprintln s!"DETECTOR SUSPECT: flagged a clean int lift: {intSample}"
  else
    IO.println "[detector-validation] OK: flags a real term, passes a clean int lift"

/- ---------------------------------------------------------------------- -/
/- STEP 2: RUN THE CHECK over all 276 lifts.  Report total and leak count.-/
/- ---------------------------------------------------------------------- -/

/-- THE ONE EXPECTED `real_` RESIDUE, and why it is FAITHFUL rather than a bug.

    `INT_POS_EQ_SQUARE` (int.ml 531) lifts `REAL_POS_EQ_SQUARE` (real.ml
    1825-1826), whose statement is `!x. &0 <= x <=> ?y. y pow 2 = x`.  The
    lifted form is `!x:int. &0 <= x <=> (?y. y pow 2 = real_of_int x)`.
    `INT_OF_REAL_THM` retypes only the variables in `newavs` and `avs` - that
    is, those free in the conclusion or universally quantified at the top - and
    `y` here is EXISTENTIALLY BOUND, so the rule cannot reach it.  Upstream HOL
    Light produces the identical residue, so reproducing it is correct.

    Listing it explicitly means PASS asserts something stronger than "no leaks":
    it asserts EXACTLY this residue and no other.  A new leak, or the
    DISAPPEARANCE of this one, both trip the check.  Same discipline as the
    Makefile's EXPECTED_MASKED. -/
def expectedResidues : List String := ["INT_POS_EQ_SQUARE"]

#eval show IO Unit from do
  let mut unexpected : List String := []
  let mut expectedSeen : List String := []
  let mut degen : List String := []
  for (nm, th) in lifts do
    let cs := constNames (concl th)
    let ls := realLeaks th
    -- A masked failure (panicked setupX -> Inhabited default) prints as
    -- `|-  = ` and carries ONLY the `=` constant, so it would FALSELY pass the
    -- real_-leak test.  Flag any such degenerate lift.
    if isDegenerate th then
      degen := degen ++ [nm ++ s!" (consts={cs})"]
    if !ls.isEmpty then
      if expectedResidues.contains nm then expectedSeen := expectedSeen ++ [nm]
      else unexpected := unexpected ++ [s!"{nm}: {ls}"]
  let missing := expectedResidues.filter (fun n => !(expectedSeen.contains n))
  IO.println s!"[276-lift-check] total lifts walked:        {lifts.length}"
  IO.println s!"[276-lift-check] expected residues seen:    {expectedSeen}"
  IO.println s!"[276-lift-check] UNEXPECTED real_ leaks:    {unexpected.length}"
  IO.println s!"[276-lift-check] degenerate (masked) lifts: {degen.length}"
  -- Emit the literal token MISMATCH on any failure: that is what `make verify`
  -- greps for, so without it a regression here would be INVISIBLE to the
  -- acceptance gates and this whole file would be decoration.
  if lifts.length != 276 then
    IO.println s!"[276-lift-check] MISMATCH wrong lift count {lifts.length}, want 276"
  if !unexpected.isEmpty then
    IO.println s!"[276-lift-check] MISMATCH unexpected real_ leak(s): {unexpected}"
  if !degen.isEmpty then
    IO.println s!"[276-lift-check] MISMATCH degenerate lift(s): {degen}"
  if !missing.isEmpty then
    IO.println s!"[276-lift-check] MISMATCH expected residue vanished: {missing}"
  if unexpected.isEmpty && degen.isEmpty && missing.isEmpty
       && lifts.length == 276 then
    IO.println "[276-lift-check] RESULT: OK - 276 lifts, exactly the one faithful INT_POS_EQ_SQUARE residue, none degenerate"

end HolTest.IntLeakCheck

