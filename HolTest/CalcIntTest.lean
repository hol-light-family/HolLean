/- File: HolTest/CalcIntTest.lean
Runtime test suite: calc_int.ml - calculation with integer-valued reals.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

FAITHFULNESS BASIS.  The conversion expectations below are taken VERBATIM from
HOL Light's own reference documentation, which ships worked examples with real
OCaml output:
  hol-light/Help/REAL_INT_LE_CONV.hlp   .../REAL_INT_LT_CONV.hlp
  .../REAL_INT_GE_CONV.hlp              .../REAL_INT_GT_CONV.hlp
  .../REAL_INT_EQ_CONV.hlp              .../REAL_INT_MUL_CONV.hlp
  .../REAL_INT_ADD_CONV.hlp             .../REAL_INT_SUB_CONV.hlp
  .../REAL_INT_POW_CONV.hlp             .../REAL_INT_ABS_CONV.hlp
  .../REAL_INT_NEG_CONV.hlp             .../REAL_INT_REDUCE_CONV.hlp
A mismatch on those is a genuine divergence from HOL Light, not a disagreement
with this translator's guesses.  ONE exception, documented in full at its use
site: REAL_INT_NEG_CONV.hlp's example is a copy-paste from its rational sibling
REAL_RAT_NEG_CONV.hlp and is wrong for this conversion, so the CORRECTED example
`-- (-- &3)` is used instead.  Definitions and theorem statements are checked
against calc_int.ml itself.

`&` is `real_of_num`, the injection of the naturals into the reals; HOL Light
has no separate real-literal syntax, so an integer-valued real is written `&n`
or `--(&n)`.  That is exactly the class this file's conversions operate on.
-/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- FORCING THE LAYER FIRST IS MANDATORY.                                  -/
/-                                                                        -/
/- The calc_int bootstrap is LAZY, and a conversion passed around as a     -/
/- VALUE forces nothing.  So a term mentioning `&` cannot even be PARSED   -/
/- until something has forced the real layer into existence - measured, a  -/
/- bare probe fails with `mk_type: type num has not been defined`.         -/
/- Reading any calc_int accessor drives the whole chain (calc_int on top   -/
/- of realax.ml's ten stages), so this `#eval` must come first.            -/
/-                                                                        -/
/- NOTE there is deliberately NO `ARITH_*` preamble and NO pre-calling of  -/
/- the `NUM_*_CONV` family here.  An earlier draft of this work concluded   -/
/- such ceremony was required; it was not - it was masking two real        -/
/- Session bugs (calc_num's proformas not forcing the DIV/MOD constant     -/
/- declaration, and being constructible after realax.ml had changed the    -/
/- default type of schematic terms).  Both are fixed, so the conversions   -/
/- now work unaided, as they do in OCaml.  If ceremony ever appears to be  -/
/- needed again, that is a load-order regression, not a test problem.      -/
/- ---------------------------------------------------------------------- -/

#eval Session.calcIntThms.REAL_ADD_AC

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

/-- Check a rational round-trips: `term_of_rat` then `rat_of_term`. -/
private unsafe def ratRoundTrip (lbl : String) (x : Rat) (expTm : String) : IO Unit := do
  match Session.term_of_rat x with
  | .error e => IO.println s!"{lbl} term_of_rat ERR: {e}"
  | .ok tm =>
    let got := squash (← HolCore.Printer.string_of_term tm)
    -- `Except String Rat` has no `BEq`, so match rather than compare.
    let backOk : Bool := match Session.rat_of_term tm with
                         | .ok v => v == x
                         | .error _ => false
    if got != squash expTm then IO.println s!"{lbl} -> MISMATCH term={got}"
    else if !backOk then IO.println s!"{lbl} -> MISMATCH round-trip failed"
    else IO.println s!"{lbl} -> OK"

/-- Assert a term is NOT accepted as an integer/rational constant. -/
private unsafe def rejectCheck (lbl expr : String) (f : term → Bool) : IO Unit := do
  match ← HolCore.Parser.parse_term expr with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok tm =>
    if f tm then IO.println s!"{lbl} -> MISMATCH wrongly accepted"
    else IO.println s!"{lbl} -> OK (correctly rejected)"

/- ---------------------------------------------------------------------- -/
/- Syntax operations on integer constants of type ":real".                -/
/- (calc_int.ml 16-60)                                                    -/
/- ---------------------------------------------------------------------- -/

#eval ratRoundTrip "term_of_rat 3" 3 "&3"
#eval ratRoundTrip "term_of_rat -3" (-3) "-- &3"
#eval ratRoundTrip "term_of_rat 0" 0 "&0"
#eval ratRoundTrip "term_of_rat 1/2" (1/2 : Rat) "&1 / &2"
#eval ratRoundTrip "term_of_rat -3/4" (-3/4 : Rat) "-- &3 / &4"
/- Denominator 1 must emit NO division - just the integer constant. -/
#eval ratRoundTrip "term_of_rat 7/1" (7/1 : Rat) "&7"

/- `--(&0)` is NOT a permitted integer constant: `&0` is the canonical form for
   zero, and the OCaml guards the negated case with a non-zero test. -/
#eval rejectCheck "reject --(&0)" "--(&0)" Session.is_realintconst
/- A rational constant must be in LOWEST TERMS with denominator > 1. -/
#eval rejectCheck "reject &2 / &4 (not lowest terms)" "&2 / &4" Session.is_ratconst
#eval rejectCheck "reject &3 / &1 (denominator 1)" "&3 / &1" Session.is_ratconst

/- ---------------------------------------------------------------------- -/
/- The elementary real theorems (calc_int.ml 66-171), checked against the  -/
/- OCaml source.                                                          -/
/- ---------------------------------------------------------------------- -/

#eval thmCheck "REAL_ADD_AC" calcIntThms.REAL_ADD_AC
  "|- m + n = n + m /\\ (m + n) + p = m + n + p /\\ m + n + p = n + m + p"
#eval thmCheck "REAL_ADD_RINV" calcIntThms.REAL_ADD_RINV "|- forall x. x + --x = &0"
#eval thmCheck "REAL_EQ_ADD_LCANCEL" calcIntThms.REAL_EQ_ADD_LCANCEL
  "|- forall x y z. x + y = x + z <=> y = z"
#eval thmCheck "REAL_EQ_ADD_RCANCEL" calcIntThms.REAL_EQ_ADD_RCANCEL
  "|- forall x y z. x + z = y + z <=> x = y"
#eval thmCheck "REAL_MUL_RZERO" calcIntThms.REAL_MUL_RZERO "|- forall x. x * &0 = &0"
#eval thmCheck "REAL_MUL_LZERO" calcIntThms.REAL_MUL_LZERO "|- forall x. &0 * x = &0"
#eval thmCheck "REAL_NEG_NEG" calcIntThms.REAL_NEG_NEG "|- forall x. -- --x = x"
#eval thmCheck "REAL_MUL_RNEG" calcIntThms.REAL_MUL_RNEG "|- forall x y. x * --y = --(x * y)"
#eval thmCheck "REAL_MUL_LNEG" calcIntThms.REAL_MUL_LNEG "|- forall x y. --x * y = --(x * y)"
#eval thmCheck "REAL_NEG_ADD" calcIntThms.REAL_NEG_ADD "|- forall x y. --(x + y) = --x + --y"
#eval thmCheck "REAL_ADD_RID" calcIntThms.REAL_ADD_RID "|- forall x. x + &0 = x"
#eval thmCheck "REAL_NEG_0" calcIntThms.REAL_NEG_0 "|- -- &0 = &0"
#eval thmCheck "REAL_LE_LNEG" calcIntThms.REAL_LE_LNEG
  "|- forall x y. --x <= y <=> &0 <= x + y"
#eval thmCheck "REAL_LE_NEG2" calcIntThms.REAL_LE_NEG2 "|- forall x y. --x <= --y <=> y <= x"
#eval thmCheck "REAL_LE_RNEG" calcIntThms.REAL_LE_RNEG
  "|- forall x y. x <= --y <=> x + y <= &0"
#eval thmCheck "REAL_OF_NUM_POW" calcIntThms.REAL_OF_NUM_POW
  "|- forall x n. &x pow n = &(x EXP n)"
#eval thmCheck "REAL_POW_NEG" calcIntThms.REAL_POW_NEG
  "|- forall x n. --x pow n = (if EVEN n then x pow n else --(x pow n))"
#eval thmCheck "REAL_ABS_NUM" calcIntThms.REAL_ABS_NUM "|- forall n. abs (&n) = &n"
#eval thmCheck "REAL_ABS_NEG" calcIntThms.REAL_ABS_NEG "|- forall x. abs (--x) = abs x"

/- ---------------------------------------------------------------------- -/
/- The five comparison conversions (calc_int.ml 177-246).                  -/
/- The first case of each group is the Help file's own worked example.      -/
/- ---------------------------------------------------------------------- -/

#eval convCheck "LE &11 <= &77 [Help]" "&11 <= &77" "|- &11 <= &77 <=> true" REAL_INT_LE_CONV
#eval convCheck "LT -- &18 < &64 [Help]" "-- &18 < &64" "|- -- &18 < &64 <=> true"
  REAL_INT_LT_CONV
#eval convCheck "GE &7 >= &6 [Help]" "&7 >= &6" "|- &7 >= &6 <=> true" REAL_INT_GE_CONV
#eval convCheck "GT &1 > &2 [Help]" "&1 > &2" "|- &1 > &2 <=> false" REAL_INT_GT_CONV
#eval convCheck "EQ &1 = &2 [Help]" "&1 = &2" "|- &1 = &2 <=> false" REAL_INT_EQ_CONV
#eval convCheck "EQ -- &1 = -- &1 [Help]" "-- &1 = -- &1" "|- -- &1 = -- &1 <=> true"
  REAL_INT_EQ_CONV

/- All four sign combinations for LE, plus the both-zero case.  The last two
   exercise the alternatives whose right-hand sides are `(m = 0) /\ (n = 0)`. -/
#eval convCheck "LE &3 <= &2" "&3 <= &2" "|- &3 <= &2 <=> false" REAL_INT_LE_CONV
#eval convCheck "LE --(&2) <= &3" "--(&2) <= &3" "|- -- &2 <= &3 <=> true" REAL_INT_LE_CONV
#eval convCheck "LE --(&2) <= --(&3)" "--(&2) <= --(&3)" "|- -- &2 <= -- &3 <=> false"
  REAL_INT_LE_CONV
#eval convCheck "LE &2 <= --(&3)" "&2 <= --(&3)" "|- &2 <= -- &3 <=> false" REAL_INT_LE_CONV
#eval convCheck "LE &0 <= --(&0) (both zero)" "&0 <= --(&0)" "|- &0 <= -- &0 <=> true"
  REAL_INT_LE_CONV
#eval convCheck "EQ --(&0) = &0 (both zero)" "--(&0) = &0" "|- -- &0 = &0 <=> true"
  REAL_INT_EQ_CONV

/- ---------------------------------------------------------------------- -/
/- The six arithmetic conversions (calc_int.ml 248-374).                   -/
/- ---------------------------------------------------------------------- -/

#eval convCheck "NEG -- &0" "--(&0)" "|- -- &0 = &0" REAL_INT_NEG_CONV

/- ---------------------------------------------------------------------- -/
/- THE Help EXAMPLE FOR THIS CONVERSION IS WRONG IN THE HOL LIGHT DOCS,    -/
/- SO THE CORRECTED FORM IS USED BELOW.                                    -/
/-                                                                        -/
/- Help/REAL_INT_NEG_CONV.hlp prints                                       -/
/-     # REAL_INT_NEG_CONV `-- (-- &3 / &2)`;;                             -/
/-     val it : thm = |- --(-- &3 / &2) = &3 / &2                          -/
/- but that argument is a RATIONAL, and this conversion only handles        -/
/- integer literals.  calc_int.ml 248 defines it as `GEN_REWRITE_CONV I     -/
/- [pth]` with                                                             -/
/-     pth = (--(&0) = &0) /\ (--(--(&x)) = &x)                             -/
/- whose second pattern requires the inner `--`'s argument to be a numeral  -/
/- literal `&x`.  In the doc's example that argument is a division (head    -/
/- `real_div`), so neither pattern matches and the conversion must fail.    -/
/-                                                                        -/
/- THREE pieces of evidence that the DOC is at fault, not the code:         -/
/-  1. the .hlp's own prose contradicts its example - it says "Conversion   -/
/-     to negate an INTEGER literal ... may be of the form `&n` or `-- &n`";-/
/-  2. `REAL_RAT_NEG_CONV.hlp` carries the BYTE-IDENTICAL example, so it    -/
/-     was copy-pasted from the rational sibling (which does handle it;     -/
/-     `REAL_RAT_NEG_CONV` arrives later, in real.ml);                      -/
/-  3. `REAL_INT_NEG_CONV` occurs in calc_int.ml ALONE and is never         -/
/-     redefined, so no later version rescues the documented behaviour.     -/
/-                                                                        -/
/- The corrected example, used as the Help case below, is                   -/
/-     # REAL_INT_NEG_CONV `-- (-- &3)`;;                                   -/
/-     val it : thm = |- -- -- &3 = &3                                      -/
/-                                                                        -/
/- The doc's rational term is ALSO kept, as a guard asserting that it        -/
/- FAILS - so if this conversion ever starts accepting rationals we find    -/
/- out rather than drifting silently from calc_int.ml.                      -/
/-                                                                        -/
/- Worth noting generally: the Help files are this project's best oracle    -/
/- and have caught three real translation errors, but they are not          -/
/- infallible and deserve the same scrutiny as everything else.             -/
/- ---------------------------------------------------------------------- -/

#eval convCheck "NEG -- (-- &3) [Help, corrected]" "-- (-- &3)"
  "|- -- -- &3 = &3" REAL_INT_NEG_CONV

/-- Assert a conversion FAILS on a term (the expected behaviour here). -/
private unsafe def convFails (lbl expr : String) (c : ioconv) : IO Unit := do
  match ← HolCore.Parser.parse_term expr with
  | .error e => IO.println s!"{lbl} parse ERR: {e}"
  | .ok tm =>
    match ← c tm with
    | .error _ => IO.println s!"{lbl} -> OK (correctly fails)"
    | .ok th =>
      IO.println s!"{lbl} -> MISMATCH unexpectedly succeeded: {
        squash (← HolCore.Printer.string_of_thm th)}"

#eval convFails "NEG rejects rational -- (-- &3 / &2)" "-- (-- &3 / &2)"
  REAL_INT_NEG_CONV

#eval convCheck "MUL &6 * -- &9 [Help]" "&6 * --(&9)" "|- &6 * -- &9 = -- &54"
  REAL_INT_MUL_CONV
#eval convCheck "SUB &33 - &77 [Help]" "&33 - &77" "|- &33 - &77 = -- &44"
  REAL_INT_SUB_CONV
#eval convCheck "ABS abs(-- &42) [Help]" "abs(--(&42))" "|- abs (-- &42) = &42"
  REAL_INT_ABS_CONV

/- `REAL_INT_ADD_CONV` is a HAND-WRITTEN conversion with SIX leaf paths, one per
   sign/magnitude combination.  Each leaf uses a different accessor chain into
   its instantiated theorem and a different `TRANS` argument order, so a fault
   in one leaf leaves the other five working.  Every leaf is exercised here. -/
#eval convCheck "ADD -- &17 + &25 [Help]" "--(&17) + &25" "|- -- &17 + &25 = &8"
  REAL_INT_ADD_CONV
#eval convCheck "ADD &3 + &4 (leaf 6)" "&3 + &4" "|- &3 + &4 = &7" REAL_INT_ADD_CONV
#eval convCheck "ADD --&3 + --&4 (leaf 1)" "--(&3) + --(&4)" "|- -- &3 + -- &4 = -- &7"
  REAL_INT_ADD_CONV
#eval convCheck "ADD --&3 + &7 (leaf 2)" "--(&3) + &7" "|- -- &3 + &7 = &4"
  REAL_INT_ADD_CONV
#eval convCheck "ADD --&7 + &3 (leaf 3)" "--(&7) + &3" "|- -- &7 + &3 = -- &4"
  REAL_INT_ADD_CONV
#eval convCheck "ADD &7 + --&3 (leaf 4)" "&7 + --(&3)" "|- &7 + -- &3 = &4"
  REAL_INT_ADD_CONV
#eval convCheck "ADD &3 + --&7 (leaf 5)" "&3 + --(&7)" "|- &3 + -- &7 = -- &4"
  REAL_INT_ADD_CONV
#eval convCheck "ADD --&3 + &3 (cancel)" "--(&3) + &3" "|- -- &3 + &3 = &0"
  REAL_INT_ADD_CONV
#eval convCheck "ADD &3 + --&3 (cancel)" "&3 + --(&3)" "|- &3 + -- &3 = &0"
  REAL_INT_ADD_CONV

/- POW branches on `EVEN n`: an even exponent gives a positive result, an odd
   one a negative.  The Help example also stress-tests a large exponent. -/
#eval convCheck "POW &2 pow 3" "&2 pow 3" "|- &2 pow 3 = &8" REAL_INT_POW_CONV
#eval convCheck "POW --&2 pow 2 (EVEN)" "--(&2) pow 2" "|- -- &2 pow 2 = &4"
  REAL_INT_POW_CONV
#eval convCheck "POW --&2 pow 3 (ODD)" "--(&2) pow 3" "|- -- &2 pow 3 = -- &8"
  REAL_INT_POW_CONV
#eval convCheck "POW -- &2 pow 77 [Help]" "--(&2) pow 77"
  "|- -- &2 pow 77 = -- &151115727451828646838272" REAL_INT_POW_CONV

/- ---------------------------------------------------------------------- -/
/- The reduction net and computeLib integration (calc_int.ml 376-407).     -/
/- ---------------------------------------------------------------------- -/

/- RED_CONV performs ONE top-level step. -/
#eval convCheck "RED &3 + &4" "&3 + &4" "|- &3 + &4 = &7" REAL_INT_RED_CONV
#eval convCheck "RED &3 * &4" "&3 * &4" "|- &3 * &4 = &12" REAL_INT_RED_CONV

/- REDUCE_CONV is `DEPTH_CONV RED_CONV`, so it evaluates nested expressions
   bottom-up.  The last case is the Help file's own example and is the strongest
   test in this file: it exercises POW, LT, SUB, POW again and ADD, and requires
   the literal to propagate through the conditional.
   (5^4 = 625 < 1024 = 4^5, so the branch taken is (2^3-1)^2+1 = 49+1 = 50.) -/
#eval convCheck "REDUCE (&3 + &4) * --(&2)" "(&3 + &4) * --(&2)"
  "|- (&3 + &4) * -- &2 = -- &14" REAL_INT_REDUCE_CONV
#eval convCheck "REDUCE abs(&2 - &7) + &1" "abs(&2 - &7) + &1"
  "|- abs (&2 - &7) + &1 = &6" REAL_INT_REDUCE_CONV
#eval convCheck "REDUCE &2 pow 3 <= &10" "&2 pow 3 <= &10"
  "|- &2 pow 3 <= &10 <=> true" REAL_INT_REDUCE_CONV
#eval convCheck "REDUCE (&5 - &2) * (&4 + --(&1))" "(&5 - &2) * (&4 + --(&1))"
  "|- (&5 - &2) * (&4 + -- &1) = &9" REAL_INT_REDUCE_CONV
#eval convCheck "REDUCE conditional [Help]"
  "if &5 pow 4 < &4 pow 5 then (&2 pow 3 - &1) pow 2 + &1 else &99"
  "|- (if &5 pow 4 < &4 pow 5 then (&2 pow 3 - &1) pow 2 + &1 else &99) = &50"
  REAL_INT_REDUCE_CONV

/- COMPUTE_CONV goes through the `compset` / call-by-value path instead. -/
#eval convCheck "COMPUTE &3 + &4" "&3 + &4" "|- &3 + &4 = &7" REAL_INT_COMPUTE_CONV
#eval convCheck "COMPUTE (&3 + &4) * &2" "(&3 + &4) * &2"
  "|- (&3 + &4) * &2 = &14" REAL_INT_COMPUTE_CONV
