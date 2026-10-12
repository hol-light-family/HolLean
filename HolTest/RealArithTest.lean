/- File: HolTest/RealArithTest.lean
Runtime test suite: realarith.ml - the universal linear real decision
procedure (GEN_REAL_ARITH / REAL_ARITH, bootstrapping version).
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Tests are compile-time `#eval`s, so building this module runs them.  To disable
a group of tests, exclude its file from the build - there is no flag to set.

FAITHFULNESS BASIS.  Theorem statements and conjunct counts are checked against
realarith.ml itself (the twenty-nine driving lemmas 16-160, the two `GEN_REAL_
ARITH1` proforma bundles 185-256, the alien lemmas 477-479, and the second-
framework proformas 518-641).  The decision-procedure goals proved below, and
the two worked examples, are taken from hol-light/Help/REAL_ARITH.hlp.

TWO VERSIONS.  realarith.ml defines `REAL_ARITH` TWICE.  `REAL_ARITH1`
(realarith.ml 494) is the bootstrapping instance - trivial abs-elimination
(both `absconv` slots `NO_CONV`) preceded by a crude `deabs_conv =
REWRITE_CONV[real_abs; real_max; real_min]`.  Its ONLY job is to prove version
2's 42-clause ABSMAXMIN proforma.  `REAL_ARITH2` (realarith.ml 651) is the
instance the rest of HOL Light sees at this point, with abs/max/min eliminated
intelligently by the two hardwired conversions.  NOTE that v1 is NOT incapable
on abs/max/min goals: its `deabs_conv` turns those constants into conditionals
which `GEN_REAL_ARITH1`'s init_conv then removes, so v1 PROVES them too - the
difference is that v2's elimination is more intelligent, not that v1 fails.
Neither is the FINAL `REAL_ARITH`: calc_rat.ml (hol_lib.ml 97) overwrites it a
THIRD time to add rational-constant support (its `REAL_ARITH3`).  calc_rat.ml is
now wired in, so this file marks (below, section 5) exactly which Help example
`REAL_ARITH2` CANNOT satisfy while `REAL_ARITH3` CAN, asserting both outcomes on
the SAME goal to make the difference explicit.

`&` is `real_of_num`, the injection of the naturals into the reals.
-/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- FORCING THE LAYER FIRST IS MANDATORY.                                  -/
/-                                                                        -/
/- The realarith bootstrap is LAZY, and a procedure passed around as a     -/
/- VALUE forces nothing.  So a term mentioning `&`, `abs`, `min` or `max`  -/
/- cannot even be PARSED until something has forced the real layer into    -/
/- existence - measured, a bare probe fails with `mk_type: type num has    -/
/- not been defined`.  Reading any realarith accessor drives the whole     -/
/- chain (realarith on top of calc_int on top of realax.ml), so this       -/
/- `#eval` must come first.  `realArithLemmas` is the cheapest such        -/
/- accessor (it forces none of the ~8.8s ABSMAXMIN proof).                 -/
/- ---------------------------------------------------------------------- -/

#eval Session.realArithLemmas.REAL_LTE_TOTAL

/-- Squash whitespace so a printed theorem can be compared against a
    single-line expected string. -/
private def squash (s : String) : String := (s.replace "\n" "").replace " " ""

/-- Compare a theorem against an expected printed form. -/
private unsafe def thmCheck (lbl : String) (t : thm) (expected : String) : IO Unit := do
  let got := squash (← HolCore.Printer.string_of_thm t)
  if got == squash expected then IO.println s!"{lbl} -> OK"
  else IO.println s!"{lbl} -> MISMATCH got={got}"

/-- Assert a bundled theorem splits into exactly `n` conjuncts.  The conjunct
    ORDER of `REAL_POLY_CLAUSES` (10) and `REAL_POLY_NEG_CLAUSES` (2) is
    load-bearing: both `REAL_ARITH` definitions feed them to
    `SEMIRING_NORMALIZERS_CONV`, so a dropped conjunct would be SILENT. -/
private unsafe def conjCountCheck (lbl : String) (t : thm) (n : Nat) : IO Unit := do
  match ← Session.theBool.get with
  | none => IO.println s!"{lbl} -> MISMATCH BoolThms not forced"
  | some B =>
    let got := (B.CONJUNCTS t).length
    if got == n then IO.println s!"{lbl} -> OK ({n} conjuncts)"
    else IO.println s!"{lbl} -> MISMATCH got {got} conjuncts, want {n}"

/-- Parse `goal`, run a decision procedure, assert it PROVES the goal with NO
    hypotheses.  A proved goal's conclusion IS the goal, so the expected form is
    `|- ` prepended to the goal RE-PRINTED from its parse (which normalises
    cosmetic input differences like `abs(x)` vs the printer's `abs x`). -/
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

/-- Assert a decision procedure FAILS on `goal` (the expected behaviour for a
    rational-constant goal under the integer-only bootstrapping versions).
    Optionally require the error message to CONTAIN `wantMsg`. -/
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
/- (1) THE TWENTY-NINE DRIVING LEMMAS (realarith.ml 16-160).               -/
/- Consequences of the realax.ml axioms that only exist to make the        -/
/- decision procedure go through.  Every statement checked against source. -/
/- ---------------------------------------------------------------------- -/

#eval thmCheck "REAL_LTE_TOTAL" realArithLemmas.REAL_LTE_TOTAL
  "|- forall x y. x < y \\/ y <= x"
#eval thmCheck "REAL_LET_TOTAL" realArithLemmas.REAL_LET_TOTAL
  "|- forall x y. x <= y \\/ y < x"
#eval thmCheck "REAL_LT_IMP_LE" realArithLemmas.REAL_LT_IMP_LE
  "|- forall x y. x < y ==> x <= y"
#eval thmCheck "REAL_LTE_TRANS" realArithLemmas.REAL_LTE_TRANS
  "|- forall x y z. x < y /\\ y <= z ==> x < z"
#eval thmCheck "REAL_LET_TRANS" realArithLemmas.REAL_LET_TRANS
  "|- forall x y z. x <= y /\\ y < z ==> x < z"
#eval thmCheck "REAL_LT_TRANS" realArithLemmas.REAL_LT_TRANS
  "|- forall x y z. x < y /\\ y < z ==> x < z"
#eval thmCheck "REAL_LE_ADD" realArithLemmas.REAL_LE_ADD
  "|- forall x y. &0 <= x /\\ &0 <= y ==> &0 <= x + y"
#eval thmCheck "REAL_LTE_ANTISYM" realArithLemmas.REAL_LTE_ANTISYM
  "|- forall x y. ~(x < y /\\ y <= x)"
#eval thmCheck "REAL_SUB_LE" realArithLemmas.REAL_SUB_LE
  "|- forall x y. &0 <= x - y <=> y <= x"
#eval thmCheck "REAL_NEG_SUB" realArithLemmas.REAL_NEG_SUB
  "|- forall x y. --(x - y) = y - x"
#eval thmCheck "REAL_LE_LT" realArithLemmas.REAL_LE_LT
  "|- forall x y. x <= y <=> x < y \\/ x = y"
#eval thmCheck "REAL_SUB_LT" realArithLemmas.REAL_SUB_LT
  "|- forall x y. &0 < x - y <=> y < x"
#eval thmCheck "REAL_NOT_LT" realArithLemmas.REAL_NOT_LT
  "|- forall x y. ~(x < y) <=> y <= x"
#eval thmCheck "REAL_SUB_0" realArithLemmas.REAL_SUB_0
  "|- forall x y. x - y = &0 <=> x = y"
#eval thmCheck "REAL_LT_LE" realArithLemmas.REAL_LT_LE
  "|- forall x y. x < y <=> x <= y /\\ ~(x = y)"
#eval thmCheck "REAL_LT_REFL" realArithLemmas.REAL_LT_REFL
  "|- forall x. ~(x < x)"
#eval thmCheck "REAL_LTE_ADD" realArithLemmas.REAL_LTE_ADD
  "|- forall x y. &0 < x /\\ &0 <= y ==> &0 < x + y"
#eval thmCheck "REAL_LET_ADD" realArithLemmas.REAL_LET_ADD
  "|- forall x y. &0 <= x /\\ &0 < y ==> &0 < x + y"
#eval thmCheck "REAL_LT_ADD" realArithLemmas.REAL_LT_ADD
  "|- forall x y. &0 < x /\\ &0 < y ==> &0 < x + y"
#eval thmCheck "REAL_ENTIRE" realArithLemmas.REAL_ENTIRE
  "|- forall x y. x * y = &0 <=> x = &0 \\/ y = &0"
#eval thmCheck "REAL_LE_NEGTOTAL" realArithLemmas.REAL_LE_NEGTOTAL
  "|- forall x. &0 <= x \\/ &0 <= --x"
#eval thmCheck "REAL_LE_SQUARE" realArithLemmas.REAL_LE_SQUARE
  "|- forall x. &0 <= x * x"
#eval thmCheck "REAL_MUL_RID" realArithLemmas.REAL_MUL_RID
  "|- forall x. x * &1 = x"
#eval thmCheck "REAL_POW_2" realArithLemmas.REAL_POW_2
  "|- forall x. x pow 2 = x * x"
#eval thmCheck "REAL_POS" realArithLemmas.REAL_POS
  "|- forall n. &0 <= &n"
#eval thmCheck "REAL_LT_NZ" realArithLemmas.REAL_LT_NZ
  "|- forall n. ~(&n = &0) <=> &0 < &n"
#eval thmCheck "REAL_POS_LT" realArithLemmas.REAL_POS_LT
  "|- forall n. &0 < &(SUC n)"

/- The two clause bundles fed to SEMIRING_NORMALIZERS_CONV.  Assert their
   CONJUNCT COUNTS programmatically - a dropped conjunct is otherwise silent.
   (realarith.ml 125: REAL_POLY_CLAUSES = 10; 140: REAL_POLY_NEG_CLAUSES = 2.) -/
#eval conjCountCheck "REAL_POLY_CLAUSES count"
  realArithLemmas.REAL_POLY_CLAUSES 10
#eval conjCountCheck "REAL_POLY_NEG_CLAUSES count"
  realArithLemmas.REAL_POLY_NEG_CLAUSES 2

/- ---------------------------------------------------------------------- -/
/- (2) THE PROFORMAS of the two frameworks.                                -/
/- GEN_REAL_ARITH1 (realarith.ml 185-256), the alien lemmas (477-479), and  -/
/- GEN_REAL_ARITH2's abs/max/min proformas (518-641).                      -/
/- ---------------------------------------------------------------------- -/

/- genRealArith1Ctx.pth (realarith.ml 186-207): the TEN-conjunct comparison
   rewrite.  Count is load-bearing (it drives the sign-case split), so assert
   it programmatically. -/
#eval conjCountCheck "genRealArith1Ctx.pth count" genRealArith1Ctx.pth 10
/- pth_final = TAUT `(~p ==> F) ==> p` (realarith.ml 208). -/
#eval thmCheck "genRealArith1Ctx.pth_final" genRealArith1Ctx.pth_final
  "|- (~p ==> false) ==> p"
/- pth_add (realarith.ml 209-222): NINE conjuncts, addition sign rules. -/
#eval conjCountCheck "genRealArith1Ctx.pth_add count" genRealArith1Ctx.pth_add 9
/- pth_mul (realarith.ml 223-236): NINE conjuncts, multiplication sign rules. -/
#eval conjCountCheck "genRealArith1Ctx.pth_mul count" genRealArith1Ctx.pth_mul 9
/- pth_emul (realarith.ml 237-239) and pth_square (240-242): single facts. -/
#eval thmCheck "genRealArith1Ctx.pth_emul" genRealArith1Ctx.pth_emul
  "|- y = &0 ==> (forall x. x * y = &0)"
#eval thmCheck "genRealArith1Ctx.pth_square" genRealArith1Ctx.pth_square
  "|- forall x. x * x >= &0"

/- linearProverAliens (realarith.ml 477-479): the two alien point lemmas the
   linear prover appends.  `pth` is `&n >= &0`; `pth_suc` is `&(SUC n) > &0`. -/
#eval thmCheck "linearProverAliens.pth" linearProverAliens.pth
  "|- &n >= &0"
#eval thmCheck "linearProverAliens.pth_suc" linearProverAliens.pth_suc
  "|- &(SUC n) > &0"

/- genRealArith2Ctx abs/max/min proformas (realarith.ml, PART 2).  Forcing
   this record runs the ~8.8s ABSMAXMIN proof ONCE (memoised).  pth_max and
   pth_min differ ONLY in which of `P x`/`P y` sits in which disjunct, so both
   are asserted EXPLICITLY. -/
#eval thmCheck "genRealArith2Ctx.pth_abs" genRealArith2Ctx.pth_abs
  "|- P (abs x) <=> x >= &0 /\\ P x \\/ &0 > x /\\ P (--x)"
#eval thmCheck "genRealArith2Ctx.pth_max" genRealArith2Ctx.pth_max
  "|- P (max x y) <=> y >= x /\\ P y \\/ x > y /\\ P x"
#eval thmCheck "genRealArith2Ctx.pth_min" genRealArith2Ctx.pth_min
  "|- P (min x y) <=> y >= x /\\ P x \\/ x > y /\\ P y"

/- ---------------------------------------------------------------------- -/
/- (3) THE `positivstellensatz` CERTIFICATE DATATYPE (realarith.ml 166-177).-/
/- Build values exercising all TEN constructors and check they construct    -/
/- and print (it derives `Repr`).  The three Axiom_* take Int indices, the   -/
/- three Rational_* take Rat, Square takes a term, and Eqmul/Sum/Product     -/
/- are the recursive constructors.                                          -/
/- ---------------------------------------------------------------------- -/

private def certCheck (lbl : String) (c : positivstellensatz) : IO Unit :=
  IO.println s!"{lbl} -> OK ({reprStr c})"

open HolMath.RealArith.positivstellensatz in
#eval certCheck "Axiom_eq 0" (Axiom_eq 0)
open HolMath.RealArith.positivstellensatz in
#eval certCheck "Axiom_le 1" (Axiom_le 1)
open HolMath.RealArith.positivstellensatz in
#eval certCheck "Axiom_lt 2" (Axiom_lt 2)
open HolMath.RealArith.positivstellensatz in
#eval certCheck "Rational_eq 3/2" (Rational_eq (3/2 : Rat))
open HolMath.RealArith.positivstellensatz in
#eval certCheck "Rational_le 5" (Rational_le (5 : Rat))
open HolMath.RealArith.positivstellensatz in
#eval certCheck "Rational_lt -1/4" (Rational_lt (-1/4 : Rat))
open HolMath.RealArith.positivstellensatz in
#eval do
  match ← HolCore.Parser.parse_term "x:real" with
  | .error e => IO.println s!"Square/Eqmul/Sum/Product parse ERR: {e}"
  | .ok xt =>
    let sq := Square xt
    certCheck "Square x" sq
    certCheck "Eqmul x (Axiom_le 0)" (Eqmul xt (Axiom_le 0))
    certCheck "Sum (Axiom_le 0) (Axiom_lt 1)" (Sum (Axiom_le 0) (Axiom_lt 1))
    certCheck "Product (Square x) (Rational_le 2)"
      (Product sq (Rational_le (2 : Rat)))

/- ---------------------------------------------------------------------- -/
/- (4) THE TWO DECISION PROCEDURES.                                        -/
/-                                                                        -/
/- REAL_ARITH1 (realarith.ml 494) is the bootstrapping instance;           -/
/- REAL_ARITH2 (651) is the intelligent one.  All outcomes below were       -/
/- measured; the module asserts exactly them.                              -/
/- ---------------------------------------------------------------------- -/

/- REAL_ARITH1 - pure linear/algebraic goals. -/
#eval proves "v1 x<y ==> x<=y" "!x y. x < y ==> x <= y" REAL_ARITH1
#eval proves "v1 transitivity" "!x y z. x <= y /\\ y <= z ==> x <= z" REAL_ARITH1
#eval proves "v1 x + &0 = x" "!x. x + &0 = x" REAL_ARITH1
#eval proves "v1 &2 * x = x + x" "!x. &2 * x = x + x" REAL_ARITH1
#eval proves "v1 totality" "!x y. x <= y \\/ y <= x" REAL_ARITH1
/- abs under v1: NOT a failure - deabs_conv rewrites abs to a conditional
   which init_conv then eliminates, so v1 PROVES it. -/
#eval proves "v1 abs x >= &0" "!x. abs x >= &0" REAL_ARITH1

/- THE THREE ALIEN GOALS.  These exercise REAL_LINEAR_PROVER appending its
   alien lemmas (`&n >= &0`, `&(SUC n) > &0`) to the `le`/`lt` lists, so that
   the certificate's Axiom_le/Axiom_lt indices count into the EXTENDED lists.
   The two-alien goal `&0 <= &m + &n` is the strongest: it forces TWO aliens
   into the extended lists at once.  A regression here would mean the
   translator is being handed a PRE-APPLIED triple rather than applying it to
   its own alien-extended triple (realarith.ml 488) - hence these are kept as
   dedicated markers. -/
#eval proves "v1 alien &0 <= &n" "!n. &0 <= &n" REAL_ARITH1
#eval proves "v1 alien &n + &1 > &0" "!n. &n + &1 > &0" REAL_ARITH1
#eval proves "v1 alien &0 <= &m + &n (two aliens)" "!m n. &0 <= &m + &n" REAL_ARITH1

/- REAL_ARITH2 - the intelligent abs/max/min instance.  Both versions succeed
   on abs/max/min goals; v2's elimination is simply more intelligent than v1's
   deabs_conv-then-CONDS_ELIM route. -/
#eval proves "v2 max x y >= x" "!x y. max x y >= x" REAL_ARITH2
#eval proves "v2 min x y <= x" "!x y. min x y <= x" REAL_ARITH2
#eval proves "v2 abs x >= x" "!x. abs x >= x" REAL_ARITH2
#eval proves "v2 triangle" "!x y. abs (x + y) <= abs x + abs y" REAL_ARITH2
#eval proves "v2 transitivity" "!x y z. x <= y /\\ y <= z ==> x <= z" REAL_ARITH2

/- ---------------------------------------------------------------------- -/
/- (5) THE Help/REAL_ARITH.hlp EXAMPLES, with a verified finding recorded.  -/
/-                                                                        -/
/- (a) proves under REAL_ARITH2: algebraic normalization reduces it to a    -/
/-     linear problem in the monomial `x pow 4`.                            -/
/- (b) The DECISIVE CONTRAST between REAL_ARITH2 and calc_rat.ml's           -/
/-     REAL_ARITH3.  Under REAL_ARITH2 it FAILS with `linear_ineqs: no       -/
/-     contradiction`, and that is CORRECT and PERMANENT for v2: `/ &2` is a  -/
/-     RATIONAL constant, and realarith.ml instantiates its semiring          -/
/-     normaliser with `is_realintconst` (realarith.ml 496), so `min e d /    -/
/-     &2` is opaque - the `/ &2` coefficient can never be folded.  We KEEP   -/
/-     the v2 failure assertion below: v2 genuinely cannot do this.  calc_    -/
/-     rat.ml 434 passes `is_ratconst` instead, which is precisely the fix,   -/
/-     so this file's sibling REAL_ARITH3 (calc_rat.ml 544) now PROVES the    -/
/-     SAME goal - asserted immediately after.  The two versions therefore    -/
/-     demonstrably DIFFER on this exact goal.  (VERSION-SKEW NOTE:           -/
/-     REAL_ARITH.hlp documents the calc_rat.ml REAL_ARITH while appearing    -/
/-     at realarith.ml; this was the FIRST of the .hlp version-skew findings, -/
/-     REAL_ARITH_TAC.hlp being the second.)                                 -/
/- (c) The integer-constant analogue of (b) (`min e d` and `&2 * (d + e)`     -/
/-     instead of `min e d / &2` and `d + e`) DOES prove under REAL_ARITH2,   -/
/-     isolating the cause to the rational constant alone.                    -/
/- ---------------------------------------------------------------------- -/

#eval proves "Help (a) x pow 4"
  "(&1 + x) * (&1 - x) * (&1 + x pow 2) < &1 ==> &0 < x pow 4" REAL_ARITH2
/- v2 CANNOT (and never will): is_realintconst makes `/ &2` unfoldable. -/
#eval procFails "Help (b) rational / &2 (REAL_ARITH2 genuinely CANNOT)"
  "abs(x) < min e d / &2 /\\ abs(y) < min e d / &2 ==> abs(x + y) < d + e"
  "linear_ineqs" REAL_ARITH2
/- calc_rat.ml's REAL_ARITH3 CAN: is_ratconst (calc_rat.ml 434) folds `/ &2`.
   Same goal, opposite outcome - this is the whole point of calc_rat.ml. -/
#eval proves "Help (b) rational / &2 (REAL_ARITH3 now PROVES; fixed by calc_rat.ml)"
  "abs(x) < min e d / &2 /\\ abs(y) < min e d / &2 ==> abs(x + y) < d + e"
  Session.REAL_ARITH3
#eval proves "Help (c) integer analogue of (b)"
  "abs(x) < min e d /\\ abs(y) < min e d ==> abs(x + y) < &2 * (d + e)" REAL_ARITH2
