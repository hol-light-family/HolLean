/- File: HolTest/CalcNumTest.lean
Runtime test suite: calc_num.ml - calculation with natural numbers
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set. -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- Tests: calc_num.ml - calculation with natural numbers.                 -/
/- ---------------------------------------------------------------------- -/

/- ---------------------------------------------------------------------- -/
/- calc_num.ml : the `ARITH_*` trivial-arithmetic rewrite collection.     -/
/- Forcing any `ARITH_*` theorem forces the whole `setupArithRewrites`    -/
/- run, so every rewrite proof executes.  `#eval Session.DIVISION` forces -/
/- the DIV/MOD constants (arith.ml part 7) so the payoff terms below      -/
/- parse them as CONSTANTS, not variables (a not-yet-declared constant    -/
/- parses as a variable, which would silently break the conversion).      -/
/- ---------------------------------------------------------------------- -/

-- Every `ARITH_*` theorem, printed as `|- ...`.
#eval ARITH_ZERO
#eval BIT0_0
#eval BIT1_0
#eval ARITH_SUC
#eval ARITH_PRE
#eval ARITH_ADD
#eval ARITH_MULT
#eval ARITH_EXP
#eval ARITH_EVEN
#eval ARITH_ODD
#eval ARITH_LE
#eval ARITH_LT
#eval ARITH_GE
#eval ARITH_GT
#eval ARITH_EQ
#eval ARITH_SUB
#eval ARITH
#eval EXP_2_NE_0

-- Force the DIV/MOD constants (arith.ml part 7) before any term mentioning
-- them is parsed below.
#eval DIVISION

/- ---------------------------------------------------------------------- -/
/- calc_num.ml : the exported numeral conversions applied to concrete     -/
/- numerals.  Each expected value is in a trailing `--` comment.  Terms    -/
/- are parsed with `parse_term` at point of use because they mention       -/
/- constants (DIV, MOD, FACT, MAX, MIN, ...) that a hoisted `[[ ]]`         -/
/- quotation would parse as variables.                                     -/
/- ---------------------------------------------------------------------- -/

-- NUM_SUC_CONV: SUC 41 = 42.
#eval (do
  match ← HolCore.Parser.parse_term "SUC 41" with
  | .error e => IO.println s!"NUM_SUC_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_SUC_CONV tm with
    | .ok th => IO.println s!"NUM_SUC_CONV -> {← HolCore.Printer.string_of_thm th}"  -- 42
    | .error e => IO.println s!"NUM_SUC_CONV ERR: {e}")

-- NUM_ADD_CONV: 123 + 877 = 1000.
#eval (do
  match ← HolCore.Parser.parse_term "123 + 877" with
  | .error e => IO.println s!"NUM_ADD_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_ADD_CONV tm with
    | .ok th => IO.println s!"NUM_ADD_CONV -> {← HolCore.Printer.string_of_thm th}"  -- 1000
    | .error e => IO.println s!"NUM_ADD_CONV ERR: {e}")

-- NUM_MULT_CONV: 12345 * 6789 = 83810205.
#eval (do
  match ← HolCore.Parser.parse_term "12345 * 6789" with
  | .error e => IO.println s!"NUM_MULT_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_MULT_CONV tm with
    | .ok th => IO.println s!"NUM_MULT_CONV -> {← HolCore.Printer.string_of_thm th}"  -- 83810205
    | .error e => IO.println s!"NUM_MULT_CONV ERR: {e}")

-- NUM_EXP_CONV: 2 EXP 10 = 1024.
#eval (do
  match ← HolCore.Parser.parse_term "2 EXP 10" with
  | .error e => IO.println s!"NUM_EXP_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_EXP_CONV tm with
    | .ok th => IO.println s!"NUM_EXP_CONV -> {← HolCore.Printer.string_of_thm th}"  -- 1024
    | .error e => IO.println s!"NUM_EXP_CONV ERR: {e}")

-- NUM_LT_CONV: 3 < 5 <=> T.
#eval (do
  match ← HolCore.Parser.parse_term "3 < 5" with
  | .error e => IO.println s!"NUM_LT_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_LT_CONV tm with
    | .ok th => IO.println s!"NUM_LT_CONV -> {← HolCore.Printer.string_of_thm th}"  -- T
    | .error e => IO.println s!"NUM_LT_CONV ERR: {e}")

-- NUM_LE_CONV: 5 <= 5 <=> T.
#eval (do
  match ← HolCore.Parser.parse_term "5 <= 5" with
  | .error e => IO.println s!"NUM_LE_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_LE_CONV tm with
    | .ok th => IO.println s!"NUM_LE_CONV -> {← HolCore.Printer.string_of_thm th}"  -- T
    | .error e => IO.println s!"NUM_LE_CONV ERR: {e}")

-- NUM_EQ_CONV: 4 = 5 <=> F.
#eval (do
  match ← HolCore.Parser.parse_term "4 = 5" with
  | .error e => IO.println s!"NUM_EQ_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_EQ_CONV tm with
    | .ok th => IO.println s!"NUM_EQ_CONV -> {← HolCore.Printer.string_of_thm th}"  -- F
    | .error e => IO.println s!"NUM_EQ_CONV ERR: {e}")

-- NUM_GT_CONV: 5 > 3 <=> T.
#eval (do
  match ← HolCore.Parser.parse_term "5 > 3" with
  | .error e => IO.println s!"NUM_GT_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_GT_CONV tm with
    | .ok th => IO.println s!"NUM_GT_CONV -> {← HolCore.Printer.string_of_thm th}"  -- T
    | .error e => IO.println s!"NUM_GT_CONV ERR: {e}")

-- NUM_GE_CONV: 5 >= 3 <=> T.
#eval (do
  match ← HolCore.Parser.parse_term "5 >= 3" with
  | .error e => IO.println s!"NUM_GE_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_GE_CONV tm with
    | .ok th => IO.println s!"NUM_GE_CONV -> {← HolCore.Printer.string_of_thm th}"  -- T
    | .error e => IO.println s!"NUM_GE_CONV ERR: {e}")

-- NUM_PRE_CONV: PRE 7 = 6.
#eval (do
  match ← HolCore.Parser.parse_term "PRE 7" with
  | .error e => IO.println s!"NUM_PRE_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_PRE_CONV tm with
    | .ok th => IO.println s!"NUM_PRE_CONV -> {← HolCore.Printer.string_of_thm th}"  -- 6
    | .error e => IO.println s!"NUM_PRE_CONV ERR: {e}")

-- NUM_SUB_CONV: 100 - 58 = 42.
#eval (do
  match ← HolCore.Parser.parse_term "100 - 58" with
  | .error e => IO.println s!"NUM_SUB_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_SUB_CONV tm with
    | .ok th => IO.println s!"NUM_SUB_CONV -> {← HolCore.Printer.string_of_thm th}"  -- 42
    | .error e => IO.println s!"NUM_SUB_CONV ERR: {e}")

-- NUM_DIV_CONV: 7 DIV 2 = 3.
#eval (do
  match ← HolCore.Parser.parse_term "7 DIV 2" with
  | .error e => IO.println s!"NUM_DIV_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_DIV_CONV tm with
    | .ok th => IO.println s!"NUM_DIV_CONV -> {← HolCore.Printer.string_of_thm th}"  -- 3
    | .error e => IO.println s!"NUM_DIV_CONV ERR: {e}")

-- NUM_MOD_CONV: 7 MOD 2 = 1.
#eval (do
  match ← HolCore.Parser.parse_term "7 MOD 2" with
  | .error e => IO.println s!"NUM_MOD_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_MOD_CONV tm with
    | .ok th => IO.println s!"NUM_MOD_CONV -> {← HolCore.Printer.string_of_thm th}"  -- 1
    | .error e => IO.println s!"NUM_MOD_CONV ERR: {e}")

-- NUM_FACT_CONV: FACT 5 = 120.
#eval (do
  match ← HolCore.Parser.parse_term "FACT 5" with
  | .error e => IO.println s!"NUM_FACT_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_FACT_CONV tm with
    | .ok th => IO.println s!"NUM_FACT_CONV -> {← HolCore.Printer.string_of_thm th}"  -- 120
    | .error e => IO.println s!"NUM_FACT_CONV ERR: {e}")

-- NUM_MAX_CONV: MAX 3 5 = 5.
#eval (do
  match ← HolCore.Parser.parse_term "MAX 3 5" with
  | .error e => IO.println s!"NUM_MAX_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_MAX_CONV tm with
    | .ok th => IO.println s!"NUM_MAX_CONV -> {← HolCore.Printer.string_of_thm th}"  -- 5
    | .error e => IO.println s!"NUM_MAX_CONV ERR: {e}")

-- NUM_MIN_CONV: MIN 3 5 = 3.
#eval (do
  match ← HolCore.Parser.parse_term "MIN 3 5" with
  | .error e => IO.println s!"NUM_MIN_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_MIN_CONV tm with
    | .ok th => IO.println s!"NUM_MIN_CONV -> {← HolCore.Printer.string_of_thm th}"  -- 3
    | .error e => IO.println s!"NUM_MIN_CONV ERR: {e}")

-- NUM_EVEN_CONV: EVEN 10 <=> T.
#eval (do
  let conv := Session.NUM_EVEN_CONV
  do
    match ← HolCore.Parser.parse_term "EVEN 10" with
    | .error e => IO.println s!"NUM_EVEN_CONV parse ERR: {e}"
    | .ok tm =>
      match ← conv tm with
      | .ok th => IO.println s!"NUM_EVEN_CONV -> {← HolCore.Printer.string_of_thm th}"  -- T
      | .error e => IO.println s!"NUM_EVEN_CONV ERR: {e}")

-- NUM_ODD_CONV: ODD 7 <=> T.
#eval (do
  let conv := Session.NUM_ODD_CONV
  do
    match ← HolCore.Parser.parse_term "ODD 7" with
    | .error e => IO.println s!"NUM_ODD_CONV parse ERR: {e}"
    | .ok tm =>
      match ← conv tm with
      | .ok th => IO.println s!"NUM_ODD_CONV -> {← HolCore.Printer.string_of_thm th}"  -- T
      | .error e => IO.println s!"NUM_ODD_CONV ERR: {e}")

-- num_CONV: 7 = SUC 6.
#eval (do
  match ← HolCore.Parser.parse_term "7" with
  | .error e => IO.println s!"num_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.num_CONV tm with
    | .ok th => IO.println s!"num_CONV -> {← HolCore.Printer.string_of_thm th}"  -- 7 = SUC 6
    | .error e => IO.println s!"num_CONV ERR: {e}")

-- NUM_REL_CONV: 12 >= 4 <=> T (the relational net conversion).
#eval (do
  match ← Session.NUM_REL_CONV with
  | .error e => IO.println s!"NUM_REL_CONV build ERR: {e}"
  | .ok conv =>
    match ← HolCore.Parser.parse_term "12 >= 4" with
    | .error e => IO.println s!"NUM_REL_CONV parse ERR: {e}"
    | .ok tm =>
      match ← conv tm with
      | .ok th => IO.println s!"NUM_REL_CONV -> {← HolCore.Printer.string_of_thm th}"  -- T
      | .error e => IO.println s!"NUM_REL_CONV ERR: {e}")

-- NUM_RED_CONV: a single reduction step, 12 + 30 = 42.
#eval (do
  match ← HolCore.Parser.parse_term "12 + 30" with
  | .error e => IO.println s!"NUM_RED_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_RED_CONV tm with
    | .ok th => IO.println s!"NUM_RED_CONV -> {← HolCore.Printer.string_of_thm th}"  -- 42
    | .error e => IO.println s!"NUM_RED_CONV ERR: {e}")

-- NUM_COMPUTE_CONV: call-by-value evaluation, 6 * 7 = 42.
#eval (do
  match ← HolCore.Parser.parse_term "6 * 7" with
  | .error e => IO.println s!"NUM_COMPUTE_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_COMPUTE_CONV tm with
    | .ok th => IO.println s!"NUM_COMPUTE_CONV -> {← HolCore.Printer.string_of_thm th}"  -- 42
    | .error e => IO.println s!"NUM_COMPUTE_CONV ERR: {e}")

-- EXP_MOD_CONV: (7 EXP 13) MOD 11 = 2 (kept reduced modulo 11).
#eval (do
  match ← HolCore.Parser.parse_term "(7 EXP 13) MOD 11" with
  | .error e => IO.println s!"EXP_MOD_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.EXP_MOD_CONV tm with
    | .ok th => IO.println s!"EXP_MOD_CONV -> {← HolCore.Printer.string_of_thm th}"  -- 2
    | .error e => IO.println s!"EXP_MOD_CONV ERR: {e}")

-- EXPAND_CASES_CONV: expand `!n. n < 3 ==> n < 5` into the three cases.
#eval (do
  match ← HolCore.Parser.parse_term "!n. n < 3 ==> n < 5" with
  | .error e => IO.println s!"EXPAND_CASES_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.EXPAND_CASES_CONV tm with
    | .ok th => IO.println s!"EXPAND_CASES_CONV -> {← HolCore.Printer.string_of_thm th}"
    | .error e => IO.println s!"EXPAND_CASES_CONV ERR: {e}")

/- ---------------------------------------------------------------------- -/
/- THE PAYOFF: NUM_REDUCE_CONV on a COMPOUND expression, impossible in     -/
/- every earlier layer, reduced to a single numeral.                       -/
/- ---------------------------------------------------------------------- -/

-- NUM_REDUCE_CONV: (2 + 3) * (10 - 4) = 30 (a compound expression reduced
-- to a single numeral by DEPTH_CONV NUM_RED_CONV).
#eval (do
  match ← HolCore.Parser.parse_term "(2 + 3) * (10 - 4)" with
  | .error e => IO.println s!"NUM_REDUCE_CONV parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_REDUCE_CONV tm with
    | .ok th => IO.println s!"NUM_REDUCE_CONV -> {← HolCore.Printer.string_of_thm th}"  -- 30
    | .error e => IO.println s!"NUM_REDUCE_CONV ERR: {e}")

-- NUM_REDUCE_CONV on a deeper mix of every operator: reduces to one numeral.
#eval (do
  match ← HolCore.Parser.parse_term
            "(7 DIV 2 + 7 MOD 2) * FACT 4 + 2 EXP 5 - MAX 3 (MIN 8 5)" with
  | .error e => IO.println s!"NUM_REDUCE_CONV deep parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_REDUCE_CONV tm with
    | .ok th => IO.println s!"NUM_REDUCE_CONV deep -> {← HolCore.Printer.string_of_thm th}"
    | .error e => IO.println s!"NUM_REDUCE_CONV deep ERR: {e}")

-- NUM_REDUCE_TAC: prove a compound arithmetic goal outright.
#eval (do
  match ← HolCore.Parser.parse_term "(2 + 3) * (10 - 4) = 30" with
  | .error e => IO.println s!"NUM_REDUCE_TAC parse ERR: {e}"
  | .ok g =>
    match ← Session.prove g Session.NUM_REDUCE_TAC with
    | .ok th => IO.println s!"NUM_REDUCE_TAC -> {← HolCore.Printer.string_of_thm th}"
    | .error e => IO.println s!"NUM_REDUCE_TAC ERR: {e}")

/- ---------------------------------------------------------------------- -/
/- NUM_MULT_CONV size sweep: regression guard for the branch-selection     -/
/- logic in NUM_MUL_RULE / NUM_SQUARE_RULE.  Small operands take the       -/
/- schoolbook path; larger dense operands cross the `w+z` thresholds into  -/
/- divide-and-conquer (pth_rec) and Toom-3 (pth_toom3).  A `RAND_CONV`     -/
/- nesting bug in the pth_rec unshift step made every large-operand        -/
/- multiply fail with `NUM_UNSHIFT_CONV: malformed numeral`; that bug went -/
/- uncaught because every earlier test was small enough to stay schoolbook.-/
/- Each case checks the product digit-for-digit against Python ground      -/
/- truth (in the trailing comment).  One case per regime, plus a large     -/
/- Toom-3 squaring.                                                        -/
/- ---------------------------------------------------------------------- -/

-- Helper: multiply `a * b`, assert the product equals `expected`.
private unsafe def numMultCheck (lbl a b expected : String) : IO Unit := do
  match ← HolCore.Parser.parse_term (a ++ " * " ++ b) with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok tm =>
    match ← Session.NUM_MULT_CONV tm with
    | .error e => IO.println s!"{lbl} ERR: {e}"
    | .ok th =>
      match HolCore.Equal.rhs (concl th) with
      | .error e => IO.println s!"{lbl} rhs ERR: {e}"
      | .ok r =>
        let s := (← HolCore.Printer.string_of_term r).replace " " ""
        if s == expected then IO.println s!"{lbl} -> OK"
        else IO.println s!"{lbl} -> MISMATCH got={s}"

-- SCHOOLBOOK regime (k,l <= 50): dense 40-bit operands, (2^40-1)*(2^40-3).
#eval numMultCheck "SWEEP schoolbook (2^40-1)*(2^40-3)"
  "1099511627775" "1099511627773"
  "1208925819610231128195075"  -- 1208925819610231128195075

-- DIVIDE-AND-CONQUER regime (pth_rec, w+z < 800): dense 160-bit operands,
-- (2^160-1)*(2^160-3).  This is the smallest case in the reproduction that
-- used to fail.
#eval numMultCheck "SWEEP rec (2^160-1)*(2^160-3)"
  "1461501637330902918203684832716283019655932542975"
  "1461501637330902918203684832716283019655932542973"
  "2135987035920910082395021706169552114602704522350806763397717996149404986449775417944338356764675"  -- 2135987035920910082395021706169552114602704522350806763397717996149404986449775417944338356764675

-- DIVIDE-AND-CONQUER regime, decimal: (10^120+7)*(10^120+13).
#eval numMultCheck "SWEEP rec (10^120+7)*(10^120+13)"
  "1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007"
  "1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000013"
  "1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000091"  -- 1000...(120)...007 * 1000...(120)...013

-- TOOM-3 regime (pth_toom3, w+z >= 800) via a large SQUARING: (10^250+9)^2.
-- The operand is 831 bits, so NUM_SQUARE_RULE dispatches to the Toom-3 path,
-- whose recursive sub-squares in turn exercise the divide-and-conquer path.
#eval numMultCheck "SWEEP toom3 (10^250+9)^2"
  "10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009"
  "10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009"
  "100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000081"  -- (10^250+9)^2


/- ---------------------------------------------------------------------- -/
/- Size/shape sweep for the REMAINING numeral conversions.  Motivation:   -/
/- the multiplication bug (a `RAND_CONV` nested one level too deep in the  -/
/- divide-and-conquer branch) was invisible to every small-operand test   -/
/- and only surfaced on large DENSE operands.  These bit-level algorithms  -/
/- all have size-dependent branches, so each conversion below is exercised -/
/- across regimes - tiny (0,1,2), medium (~60 bit), large (~200 bit), very -/
/- large (~800 bit) - and across bit patterns - dense (2^k-1), sparse      -/
/- (2^k+1), decimal (10^d+c) - plus the carry / clamp / identity edge      -/
/- cases from HOL Light's truncated-subtraction and DIV/MOD semantics.     -/
/- Every result is checked digit-for-digit against Python ground truth (in -/
/- the trailing comment).  Each check self-reports `-> OK` / `-> MISMATCH`.-/
/- ---------------------------------------------------------------------- -/

-- Helper: apply a direct `term -> thm` conversion to the parsed `expr`,
-- assert the equation's rhs prints (spaces stripped) as `expected`.
private unsafe def numConvCheck (lbl expr expected : String)
    (conv : term → IO (Except String thm)) : IO Unit := do
  match ← HolCore.Parser.parse_term expr with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok tm =>
    match ← conv tm with
    | .error e => IO.println s!"{lbl} ERR: {e}"
    | .ok th =>
      match HolCore.Equal.rhs (concl th) with
      | .error e => IO.println s!"{lbl} rhs ERR: {e}"
      | .ok r =>
        let s := ((← HolCore.Printer.string_of_term r).replace "\n" "").replace " " ""
        if s == expected then IO.println s!"{lbl} -> OK"
        else IO.println s!"{lbl} -> MISMATCH got={s}"

-- Helper: same, for an already-built `ioconv` (NUM_GT/GE/MAX/MIN/EXPAND).
private unsafe def numIoConvCheck (lbl expr expected : String)
    (conv : HolCore.Equal.ioconv) : IO Unit := do
  match ← HolCore.Parser.parse_term expr with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok tm =>
    match ← conv tm with
    | .error e => IO.println s!"{lbl} ERR: {e}"
    | .ok th =>
      match HolCore.Equal.rhs (concl th) with
      | .error e => IO.println s!"{lbl} rhs ERR: {e}"
      | .ok r =>
        let s := ((← HolCore.Printer.string_of_term r).replace "\n" "").replace " " ""
        if s == expected then IO.println s!"{lbl} -> OK"
        else IO.println s!"{lbl} -> MISMATCH got={s}"

-- Helper: same, for a conversion built inside `IO (Except String ioconv)`
-- (NUM_EVEN/NUM_ODD/NUM_REL).
private unsafe def numBuiltConvCheck (lbl expr expected : String)
    (mk : IO (Except String HolCore.Equal.ioconv)) : IO Unit := do
  match ← mk with
  | .error e => IO.println s!"{lbl} build ERR: {e}"
  | .ok conv => numConvCheck lbl expr expected conv

/- ---------------------------------------------------------------------- -/
/- NUM_ADD_CONV: carry propagation and dense/decimal large operands.      -/
/- ---------------------------------------------------------------------- -/
#eval numConvCheck "ADD carry (2^200-1)+1"
  "1606938044258990275541962092341162602522202993782792835301375 + 1"
  "1606938044258990275541962092341162602522202993782792835301376"  -- (2^200-1)+1 all-ones carry -> 2^200
  Session.NUM_ADD_CONV

#eval numConvCheck "ADD dense 200-bit"
  "1606938044258990275541962092341162602522202993782792835301375 + 1606938044258990275541962092341162602522202993782792835301373"
  "3213876088517980551083924184682325205044405987565585670602748"  -- dense 200-bit
  Session.NUM_ADD_CONV

#eval numConvCheck "ADD decimal 10^120"
  "1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007 + 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000013"
  "2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020"  -- decimal (10^120+7)+(10^120+13)
  Session.NUM_ADD_CONV

#eval numConvCheck "ADD dense 800-bit"
  "6668014432879854274079851790721257797144758322315908160396257811764037237817632071521432200871554290742929910593433240445888801654119365080363356052330830046095157579514014558463078285911814024728965016135886601981690748037476461291163877375 + 6668014432879854274079851790721257797144758322315908160396257811764037237817632071521432200871554290742929910593433240445888801654119365080363356052330830046095157579514014558463078285911814024728965016135886601981690748037476461291163877373"
  "13336028865759708548159703581442515594289516644631816320792515623528074475635264143042864401743108581485859821186866480891777603308238730160726712104661660092190315159028029116926156571823628049457930032271773203963381496074952922582327754748"  -- very large dense ~800-bit
  Session.NUM_ADD_CONV

/- ---------------------------------------------------------------------- -/
/- NUM_SUC_CONV: successor across the all-ones carry boundary.            -/
/- ---------------------------------------------------------------------- -/
#eval numConvCheck "SUC 0"
  "SUC 0"
  "1"  -- SUC 0 = 1
  Session.NUM_SUC_CONV

#eval numConvCheck "SUC (2^200-1)"
  "SUC 1606938044258990275541962092341162602522202993782792835301375"
  "1606938044258990275541962092341162602522202993782792835301376"  -- SUC (2^200-1) full carry
  Session.NUM_SUC_CONV

/- ---------------------------------------------------------------------- -/
/- NUM_PRE_CONV: predecessor of 0, 1 and a large power of two.            -/
/- ---------------------------------------------------------------------- -/
#eval numConvCheck "PRE 0"
  "PRE 0"
  "0"  -- PRE 0 = 0 (clamped)
  Session.NUM_PRE_CONV

#eval numConvCheck "PRE 1"
  "PRE 1"
  "0"  -- PRE 1 = 0
  Session.NUM_PRE_CONV

#eval numConvCheck "PRE 2^200"
  "PRE 1606938044258990275541962092341162602522202993782792835301376"
  "1606938044258990275541962092341162602522202993782792835301375"  -- PRE 2^200 borrow chain
  Session.NUM_PRE_CONV

/- ---------------------------------------------------------------------- -/
/- NUM_SUB_CONV: truncated subtraction - clamp to 0, equal, large.        -/
/- ---------------------------------------------------------------------- -/
#eval numConvCheck "SUB clamp 58-100"
  "58 - 100"
  "0"  -- negative result clamps to 0
  Session.NUM_SUB_CONV

#eval numConvCheck "SUB equal 2^200"
  "1606938044258990275541962092341162602522202993782792835301376 - 1606938044258990275541962092341162602522202993782792835301376"
  "0"  -- equal operands -> 0
  Session.NUM_SUB_CONV

#eval numConvCheck "SUB 2^200-2^100"
  "1606938044258990275541962092341162602522202993782792835301376 - 1267650600228229401496703205376"
  "1606938044258990275541962092339894951921974764381296132096000"  -- large 2^200-2^100
  Session.NUM_SUB_CONV

/- ---------------------------------------------------------------------- -/
/- NUM_MULT_CONV: SPARSE large operands (bug did NOT repro on sparse).    -/
/- ---------------------------------------------------------------------- -/
#eval numConvCheck "MULT sparse 200x100"
  "1606938044258990275541962092341162602522202993782792835301377 * 1267650600228229401496703205377"
  "2037035976334486086268445688410985099095727383941478212728482879607503730986520995721904129"  -- sparse (2^200+1)*(2^100+1)
  Session.NUM_MULT_CONV

#eval numConvCheck "MULT dense 800-bit"
  "6668014432879854274079851790721257797144758322315908160396257811764037237817632071521432200871554290742929910593433240445888801654119365080363356052330830046095157579514014558463078285911814024728965016135886601981690748037476461291163877375 * 6668014432879854274079851790721257797144758322315908160396257811764037237817632071521432200871554290742929910593433240445888801654119365080363356052330830046095157579514014558463078285911814024728965016135886601981690748037476461291163877373"
  "44462416477094044620016814065517364315819234512137839319418223093753683069769152238984782576173969417485953521141049383745107056455283979316385016701612810119562585078620415976730705698345087039035930761275083827265405596065418173652685035762226056260107625232927443151144845973043454122614146937307065782634312580731387025281133665455931729234278241454532759506741013632725214419216390496495244580629329982333583609469622864769217676228651864703241838632775978807390315461709135875"  -- very large dense ~800-bit (Toom-3)
  Session.NUM_MULT_CONV

/- ---------------------------------------------------------------------- -/
/- NUM_EXP_CONV: exponent 0 and 1, large base^2, and 3^500.               -/
/- ---------------------------------------------------------------------- -/
#eval numConvCheck "EXP base^0"
  "12345 EXP 0"
  "1"  -- anything^0 = 1
  Session.NUM_EXP_CONV

#eval numConvCheck "EXP base^1"
  "987654321 EXP 1"
  "987654321"  -- anything^1 = itself
  Session.NUM_EXP_CONV

#eval numConvCheck "EXP largebase^2"
  "1606938044258990275541962092341162602522202993782792835301375 EXP 2"
  "2582249878086908589655919172003011874329705792829223512830656142664559104036290110705460670954932787029915606387076890625"  -- large base squared (2^200-1)^2
  Session.NUM_EXP_CONV

#eval numConvCheck "EXP 3^500"
  "3 EXP 500"
  "36360291795869936842385267079543319118023385026001623040346035832580600191583895484198508262979388783308179702534403855752855931517013066142992430916562025780021771247847643450125342836565813209972590371590152578728008385990139795377610001"  -- 3^500 ~792-bit result
  Session.NUM_EXP_CONV

/- ---------------------------------------------------------------------- -/
/- NUM_DIV_CONV: divide by 1, divisor > dividend, large dense.            -/
/- ---------------------------------------------------------------------- -/
#eval numConvCheck "DIV by 1"
  "1606938044258990275541962092341162602522202993782792835301376 DIV 1"
  "1606938044258990275541962092341162602522202993782792835301376"  -- DIV by 1 = itself
  Session.NUM_DIV_CONV

#eval numConvCheck "DIV bigger divisor"
  "5 DIV 1606938044258990275541962092341162602522202993782792835301376"
  "0"  -- divisor > dividend -> 0
  Session.NUM_DIV_CONV

#eval numConvCheck "DIV dense 200/60"
  "1606938044258990275541962092341162602522202993782792835301375 DIV 1152921504606846975"
  "1393796574908163947554908211655151769878528"  -- large dense (2^200-1) DIV (2^60-1)
  Session.NUM_DIV_CONV

/- ---------------------------------------------------------------------- -/
/- NUM_MOD_CONV: mod by 1, and large dense modulus.                       -/
/- ---------------------------------------------------------------------- -/
#eval numConvCheck "MOD by 1"
  "1606938044258990275541962092341162602522202993782792835301376 MOD 1"
  "0"  -- MOD 1 = 0
  Session.NUM_MOD_CONV

#eval numConvCheck "MOD dense 200/60"
  "1606938044258990275541962092341162602522202993782792835301375 MOD 1152921504606846975"
  "1048575"  -- large dense (2^200-1) MOD (2^60-1)
  Session.NUM_MOD_CONV

/- ---------------------------------------------------------------------- -/
/- NUM_LT/LE/EQ/GT/GE_CONV: relations on large near-equal operands.       -/
/- ---------------------------------------------------------------------- -/
#eval numConvCheck "LT large"
  "1606938044258990275541962092341162602522202993782792835301375 < 1606938044258990275541962092341162602522202993782792835301376"
  "true"  -- (2^200-1) < 2^200
  Session.NUM_LT_CONV

#eval numConvCheck "LE large eq"
  "1606938044258990275541962092341162602522202993782792835301376 <= 1606938044258990275541962092341162602522202993782792835301376"
  "true"  -- equal <= true
  Session.NUM_LE_CONV

#eval numConvCheck "EQ large neq"
  "1606938044258990275541962092341162602522202993782792835301375 = 1606938044258990275541962092341162602522202993782792835301376"
  "false"  -- differ by 1 -> false
  Session.NUM_EQ_CONV

#eval numConvCheck "EQ large eq"
  "1606938044258990275541962092341162602522202993782792835301376 = 1606938044258990275541962092341162602522202993782792835301376"
  "true"  -- equal -> true
  Session.NUM_EQ_CONV

#eval numIoConvCheck "GT large"
  "1606938044258990275541962092341162602522202993782792835301376 > 1606938044258990275541962092341162602522202993782792835301375"
  "true"  -- 2^200 > (2^200-1)
  Session.NUM_GT_CONV

#eval numIoConvCheck "GE large eq"
  "1606938044258990275541962092341162602522202993782792835301376 >= 1606938044258990275541962092341162602522202993782792835301376"
  "true"  -- equal >= true
  Session.NUM_GE_CONV

/- ---------------------------------------------------------------------- -/
/- NUM_MAX_CONV / NUM_MIN_CONV: selection among large operands.           -/
/- ---------------------------------------------------------------------- -/
#eval numIoConvCheck "MAX large"
  "MAX 1606938044258990275541962092341162602522202993782792835301375 1606938044258990275541962092341162602522202993782792835301376"
  "1606938044258990275541962092341162602522202993782792835301376"  -- MAX picks larger
  Session.NUM_MAX_CONV

#eval numIoConvCheck "MIN large"
  "MIN 1606938044258990275541962092341162602522202993782792835301375 1606938044258990275541962092341162602522202993782792835301376"
  "1606938044258990275541962092341162602522202993782792835301375"  -- MIN picks smaller
  Session.NUM_MIN_CONV

/- ---------------------------------------------------------------------- -/
/- NUM_EVEN_CONV / NUM_ODD_CONV: parity of large even / odd numerals.     -/
/- ---------------------------------------------------------------------- -/
#eval numBuiltConvCheck "EVEN large"
  "EVEN 1606938044258990275541962092341162602522202993782792835301376"
  "true"  -- 2^200 is even
  (pure (.ok Session.NUM_EVEN_CONV))

#eval numBuiltConvCheck "ODD large"
  "ODD 1606938044258990275541962092341162602522202993782792835301375"
  "true"  -- 2^200-1 is odd
  (pure (.ok Session.NUM_ODD_CONV))

/- ---------------------------------------------------------------------- -/
/- NUM_REL_CONV: the relational net conversion on a large operand.        -/
/- ---------------------------------------------------------------------- -/
#eval numBuiltConvCheck "REL large ge"
  "1606938044258990275541962092341162602522202993782792835301376 >= 4"
  "true"  -- large >= 4
  Session.NUM_REL_CONV

/- ---------------------------------------------------------------------- -/
/- NUM_FACT_CONV: factorial of 0 and larger arguments (20, 30, 50).       -/
/- ---------------------------------------------------------------------- -/
#eval numConvCheck "FACT 0"
  "FACT 0"
  "1"  -- 0! = 1
  Session.NUM_FACT_CONV

#eval numConvCheck "FACT 20"
  "FACT 20"
  "2432902008176640000"  -- 20!
  Session.NUM_FACT_CONV

#eval numConvCheck "FACT 30"
  "FACT 30"
  "265252859812191058636308480000000"  -- 30!
  Session.NUM_FACT_CONV

#eval numConvCheck "FACT 50"
  "FACT 50"
  "30414093201713378043612608166064768844377641568960512000000000000"  -- 50! ~215-bit
  Session.NUM_FACT_CONV

/- ---------------------------------------------------------------------- -/
/- num_CONV: `n = SUC (n-1)` on a large numeral.                          -/
/- ---------------------------------------------------------------------- -/
#eval numConvCheck "num_CONV 2^200"
  "1606938044258990275541962092341162602522202993782792835301376"
  "SUC1606938044258990275541962092341162602522202993782792835301375"  -- 2^200 = SUC (2^200-1)
  Session.num_CONV

/- ---------------------------------------------------------------------- -/
/- NUM_RED_CONV: single reduction step on a large all-ones + 1 add.       -/
/- ---------------------------------------------------------------------- -/
#eval numConvCheck "RED add carry"
  "1606938044258990275541962092341162602522202993782792835301375 + 1"
  "1606938044258990275541962092341162602522202993782792835301376"  -- one-step add with full carry
  Session.NUM_RED_CONV

/- ---------------------------------------------------------------------- -/
/- NUM_REDUCE_CONV: compound expression over a large all-ones operand.    -/
/- ---------------------------------------------------------------------- -/
#eval numConvCheck "REDUCE compound large"
  "(1606938044258990275541962092341162602522202993782792835301375 + 1) * 2"
  "3213876088517980551083924184682325205044405987565585670602752"  -- ((2^200-1)+1)*2 = 2^201
  Session.NUM_REDUCE_CONV

/- ---------------------------------------------------------------------- -/
/- EXP_MOD_CONV: modular exponentiation with reduced intermediates.       -/
/- ---------------------------------------------------------------------- -/
#eval numConvCheck "EXPMOD 7^101 mod p"
  "(7 EXP 101) MOD 1000000007"
  "625507266"  -- 7^101 mod 1e9+7
  Session.EXP_MOD_CONV

/- ---------------------------------------------------------------------- -/
/- EXPAND_CASES_CONV: expand `!n. n < k ==> P n` with a larger bound.     -/
/- ---------------------------------------------------------------------- -/
#eval numIoConvCheck "EXPAND bound 8"
  "!n. n < 8 ==> n < 100"
  "0<100/\\1<100/\\2<100/\\3<100/\\4<100/\\5<100/\\6<100/\\7<100"  -- eight conjuncts
  Session.EXPAND_CASES_CONV
