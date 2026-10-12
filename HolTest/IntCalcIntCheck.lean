/- File: HolTest/IntCalcIntCheck.lean
Self-checking tests for int.ml and calc_int.ml: theorem statements checked
against the OCaml source, and documented examples from hol-light/Help.
Lean4 translation by Chris Walton 2026 -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/-- Parse `goal` (after the int layer is loaded) and run a prover on it. -/
private unsafe def onGoal (prover : term → IO (Except String thm)) (goal : String) :
    IO (Except String thm) := do
  match ← HolCore.Parser.parse_term goal with
  | .error e => return .error s!"parse: {e}"
  | .ok t => prover t

/- ---------------------------------------------------------------------- -/
/- LAYER FORCING (mandatory).  hol_lib.ml loads real.ml (96) and           -/
/- calc_rat.ml (97) BEFORE int.ml (98), so force the num ring, then the    -/
/- whole real+calc_rat chain, and only then the int layer.  The final      -/
/- `ensurePrioritizeNum` drives int.ml in its own order (int.ml 70         -/
/- prioritize_int ... int.ml 2765 prioritize_num), leaving `num` default.  -/
/- Every `div`/`rem`/`zpow`/int-infix parse below depends on this having    -/
/- run first, exactly as IntTest.lean does.                                -/
/- ---------------------------------------------------------------------- -/

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

#eval Session.ensurePrioritizeNum

/- ---------------------------------------------------------------------- -/
/- Local helpers for the pure (non-thm) syntax functions and conversions.  -/
/- The thm-level tests use the CommonTest helpers stmtOK/ruleOK/failsOK.    -/
/- ---------------------------------------------------------------------- -/

/-- A `term → Bool` predicate must ACCEPT `expr`. -/
private unsafe def accepts (lbl expr : String) (f : term → Bool) : IO Unit := do
  match ← HolCore.Parser.parse_term expr with
  | .error e => IO.println s!"{lbl} -> MISMATCH parse ERR {e}"
  | .ok tm =>
    if f tm then IO.println s!"{lbl} -> OK"
    else IO.println s!"{lbl} -> MISMATCH wrongly rejected"

/-- A `term → Bool` predicate must REJECT `expr`. -/
private unsafe def rejects (lbl expr : String) (f : term → Bool) : IO Unit := do
  match ← HolCore.Parser.parse_term expr with
  | .error e => IO.println s!"{lbl} -> MISMATCH parse ERR {e}"
  | .ok tm =>
    if f tm then IO.println s!"{lbl} -> MISMATCH wrongly accepted"
    else IO.println s!"{lbl} -> OK"

/-- A `term → Except String Rat` destructor must yield `exp`. -/
private unsafe def destEq (lbl expr : String) (f : term → Except String Rat)
    (exp : Rat) : IO Unit := do
  match ← HolCore.Parser.parse_term expr with
  | .error e => IO.println s!"{lbl} -> MISMATCH parse ERR {e}"
  | .ok tm =>
    match f tm with
    | .ok v => if v == exp then IO.println s!"{lbl} -> OK"
               else IO.println s!"{lbl} -> MISMATCH got {v} want {exp}"
    | .error e => IO.println s!"{lbl} -> MISMATCH errored {e}"

/-- A `term → Except String Rat` destructor must FAIL on `expr`. -/
private unsafe def destFails (lbl expr : String) (f : term → Except String Rat) :
    IO Unit := do
  match ← HolCore.Parser.parse_term expr with
  | .error e => IO.println s!"{lbl} -> MISMATCH parse ERR {e}"
  | .ok tm =>
    match f tm with
    | .error _ => IO.println s!"{lbl} -> OK (correctly rejected)"
    | .ok v => IO.println s!"{lbl} -> MISMATCH wrongly gave {v}"

/-- `mk_intconst n` must build a term equal (aconv) to `expected` at type int. -/
private unsafe def mkIntEq (lbl : String) (n : Rat) (expected : String) : IO Unit := do
  match Session.mk_intconst n with
  | .error e => IO.println s!"{lbl} -> MISMATCH errored {e}"
  | .ok tm =>
    match ← HolCore.Parser.parse_term expected with
    | .error e => IO.println s!"{lbl} -> MISMATCH expected parse ERR {e}"
    | .ok want =>
      if aconv tm want then IO.println s!"{lbl} -> OK"
      else IO.println s!"{lbl} -> MISMATCH got {← HolCore.Printer.string_of_term tm}"

/-- Apply an `ioconv` to the parsed term `input`; delegate to ruleOK. -/
private unsafe def convOK (lbl input expected : String) (cv : ioconv) : IO Unit := do
  match ← HolCore.Parser.parse_term input with
  | .error e => IO.println s!"{lbl} -> MISMATCH input parse ERR {e}"
  | .ok tm => ruleOK lbl (cv tm) expected

/- ====================================================================== -/
/- (1) int.ml THEOREM STATEMENTS (stmtOK vs verbatim OCaml `prove`).       -/
/-     Spread early / middle / late; several with THENL-heavy proofs.      -/
/- ====================================================================== -/

-- early (int.ml 217): INT_IMAGE, THENL [DISJ1_TAC; DISJ2_TAC].
#eval stmtOK "INT_IMAGE (int.ml 217)" Session.INT_IMAGE
  "!x. (?n. x = &n) \\/ (?n. x = --(&n))"
-- int.ml 227/232: cases lemmas (MESON[INT_IMAGE]).
#eval stmtOK "FORALL_INT_CASES (int.ml 227)" Session.FORALL_INT_CASES
  "!P:int->bool. (!x. P x) <=> (!n. P(&n)) /\\ (!n. P(-- &n))"
#eval stmtOK "EXISTS_INT_CASES (int.ml 232)" Session.EXISTS_INT_CASES
  "!P:int->bool. (?x. P x) <=> (?n. P(&n)) \\/ (?n. P(-- &n))"
-- int.ml 235: INT_LT_DISCRETE (the discreteness lemma; multi-step proof).
#eval stmtOK "INT_LT_DISCRETE (int.ml 235)" Session.INT_LT_DISCRETE
  "!x y. x < y <=> (x + &1) <= y"
-- int.ml 337/350: INT_OF_REAL_THM lifts (simple statements, complex origin).
#eval stmtOK "INT_ABS_MUL (int.ml 337)" Session.INT_ABS_MUL
  "!x y. abs(x * y) = abs x * abs y"
#eval stmtOK "INT_ABS_TRIANGLE (int.ml 350)" Session.INT_ABS_TRIANGLE
  "!x y. abs(x + y) <= abs x + abs y"
-- int.ml 425/530: more lifts.
#eval stmtOK "INT_LNEG_UNIQ (int.ml 425)" Session.INT_LNEG_UNIQ
  "!x y. (x + y = &0) <=> (x = --y)"
#eval stmtOK "INT_POS (int.ml 530)" Session.INT_POS
  "!n. &0 <= &n"
-- middle (int.ml 732): INT_LE_DISCRETE (proved by INT_ARITH).
#eval stmtOK "INT_LE_DISCRETE (int.ml 732)" Session.INT_LE_DISCRETE
  "!x y:int. x <= y <=> x < y + &1"
-- int.ml 773: INT_ARCH (big SUBGOAL_THEN/THENL proof).
#eval stmtOK "INT_ARCH (int.ml 773)" Session.INT_ARCH
  "!x d. ~(d = &0) ==> ?c. x < c * d"
-- int.ml 822: INT_DIVISION (MESON[INT_DIVISION_0]).
#eval stmtOK "INT_DIVISION (int.ml 822)" Session.INT_DIVISION
  ("!m n. ~(n = &0) ==> m = m div n * n + m rem n /\\ " ++
   "&0 <= m rem n /\\ m rem n < abs n")
-- int.ml 827: INT_DIVISION_SIMP (CONV_TAC INT_ARITH tail).
#eval stmtOK "INT_DIVISION_SIMP (int.ml 827)" Session.INT_DIVISION_SIMP
  "!m n. m div n * n + m rem n = m"
-- int.ml 854: INT_LT_REM (MESON with an inline INT_ARITH lemma).
#eval stmtOK "INT_LT_REM (int.ml 854)" Session.INT_LT_REM
  "!x n. &0 < n ==> x rem n < n"
-- int.ml 1484: INT_OF_NUM_REM (second conjunct of a CONJ_PAIR prove).
#eval stmtOK "INT_OF_NUM_REM (int.ml 1484)" Session.INT_OF_NUM_REM
  "!m n. &m rem &n = &(m MOD n)"
-- int.ml 1635: INT_REM_UNIQUE (long EQ_TAC THENL proof).
#eval stmtOK "INT_REM_UNIQUE (int.ml 1635)" Session.INT_REM_UNIQUE
  ("!m n p. m rem n = p <=> " ++
   "(n = &0 /\\ m = p \\/ &0 <= p /\\ p < abs n) /\\ (m == p) (mod n)")
-- int.ml 1715: INT_REM_2_CASES (GEN_TAC ... INT_ARITH_TAC).
#eval stmtOK "INT_REM_2_CASES (int.ml 1715)" Session.INT_REM_2_CASES
  "!n. n rem &2 = &0 \\/ n rem &2 = &1"
-- late (int.ml 2083): NUM_OF_INT (num_of_int bridge).
#eval stmtOK "NUM_OF_INT (int.ml 2083)" Session.NUM_OF_INT
  "!x. &0 <= x <=> (&(num_of_int x) = x)"
-- late (int.ml 2666/2704): real_zpow theorems (ASM_CASES/ASM_SIMP proofs).
#eval stmtOK "REAL_ZPOW_NEG (int.ml 2666)" Session.REAL_ZPOW_NEG
  "!x n. x zpow (--n) = inv(x zpow n)"
#eval stmtOK "REAL_ZPOW_MUL (int.ml 2704)" Session.REAL_ZPOW_MUL
  "!(x:real) (y:real) n. (x * y) zpow n = x zpow n * y zpow n"

/- ====================================================================== -/
/- (2) INTEGER-CONSTANT SYNTAX: is_/dest_/mk_intconst  (int.ml 268-281).   -/
/-     Expected values are VERBATIM from the shipping .hlp files.          -/
/- ====================================================================== -/

-- is_intconst.hlp: `-- &3 :int` -> true ; `-- &0 :int` -> false.
#eval accepts "is_intconst -- &3 (is_intconst.hlp)" "-- &3 :int" Session.is_intconst
#eval rejects "is_intconst -- &0 (is_intconst.hlp)" "-- &0 :int" Session.is_intconst
#eval accepts "is_intconst &7 :int" "&7 :int" Session.is_intconst
-- dest_intconst.hlp: `-- &11 :int` -> -11.
#eval destEq "dest_intconst -- &11 (dest_intconst.hlp)" "-- &11 :int"
  Session.dest_intconst (-11)
#eval destEq "dest_intconst &5 :int" "&5 :int" Session.dest_intconst 5
-- dest_intconst fails on the non-canonical `-- &0`.
#eval destFails "dest_intconst -- &0 (non-canonical)" "-- &0 :int" Session.dest_intconst
-- mk_intconst.hlp: mk_intconst (-101) -> `-- &101` : int.
#eval mkIntEq "mk_intconst -101 (mk_intconst.hlp)" (-101) "-- &101 :int"
#eval mkIntEq "mk_intconst 42" 42 "&42 :int"
#eval mkIntEq "mk_intconst 0" 0 "&0 :int"

/- ====================================================================== -/
/- (3) REAL INTEGER / RATIONAL SYNTAX (calc_int.ml).                       -/
/-     is_realintconst / dest_realintconst / rat_of_term accept + reject.  -/
/- ====================================================================== -/

-- is_realintconst.hlp: `-- &3 :real` -> true ; `&1 :int` -> false (wrong type).
#eval accepts "is_realintconst -- &3 :real (is_realintconst.hlp)" "-- &3 :real"
  Session.is_realintconst
#eval rejects "is_realintconst &1 :int (is_realintconst.hlp)" "&1 :int"
  Session.is_realintconst
#eval accepts "is_realintconst &5 :real" "&5 :real" Session.is_realintconst
#eval accepts "is_realintconst &0 :real" "&0 :real" Session.is_realintconst
-- `-- &0` is not canonical (neg zero) -> rejected.
#eval rejects "is_realintconst -- &0 :real (non-canonical)" "-- &0 :real"
  Session.is_realintconst
-- dest_realintconst.hlp: `-- &27 :real` -> -27.
#eval destEq "dest_realintconst -- &27 (dest_realintconst.hlp)" "-- &27 :real"
  Session.dest_realintconst (-27)
#eval destEq "dest_realintconst &42 :real" "&42 :real" Session.dest_realintconst 42
-- dest_realintconst FAILS on a proper ratio (not an integer literal).
#eval destFails "dest_realintconst &1 / &2 (not an int const)" "&1 / &2"
  Session.dest_realintconst
#eval destFails "dest_realintconst -- &0 :real (non-canonical)" "-- &0 :real"
  Session.dest_realintconst

-- is_ratconst: a canonical ratio and an integer are accepted; non-lowest-terms
-- and denominator-1 forms are rejected.
#eval accepts "is_ratconst &1 / &2" "&1 / &2" Session.is_ratconst
#eval accepts "is_ratconst -- &3 / &4" "-- &3 / &4" Session.is_ratconst
#eval accepts "is_ratconst &5 (int is a ratconst)" "&5 :real" Session.is_ratconst
#eval rejects "is_ratconst &2 / &4 (not lowest terms)" "&2 / &4" Session.is_ratconst
#eval rejects "is_ratconst &3 / &1 (denominator 1)" "&3 / &1" Session.is_ratconst

-- rat_of_term.hlp: `-- &22 / &7` -> -22/7 ; plus round-trip on integers.
#eval destEq "rat_of_term -- &22 / &7 (rat_of_term.hlp)" "-- &22 / &7"
  Session.rat_of_term ((-22 : Rat) / 7)
#eval destEq "rat_of_term &1 / &2" "&1 / &2" Session.rat_of_term ((1 : Rat) / 2)
#eval destEq "rat_of_term &7 (integer)" "&7 :real" Session.rat_of_term 7
-- rat_of_term FAILS on non-canonical rationals.
#eval destFails "rat_of_term &2 / &4 (not lowest terms)" "&2 / &4" Session.rat_of_term
#eval destFails "rat_of_term &3 / &1 (denominator 1)" "&3 / &1" Session.rat_of_term

/- ====================================================================== -/
/- (4) EUCLIDEAN div/rem SIGN CASES (INT_DIV_CONV / INT_REM_CONV).         -/
/-     HOL Light int division is Euclidean: 0 <= (m rem n) < abs n, and    -/
/-     m = (m div n)*n + m rem n  (INT_DIVISION, int.ml 822).  Values are   -/
/-     computed by hand from that spec.                                    -/
/-                                                                         -/
/-   -7 = (-4)*2 + 1   -> -7 div  2 = -4, -7 rem  2 = 1                     -/
/-    7 = (-3)*-2 + 1  ->  7 div -2 = -3,  7 rem -2 = 1                     -/
/-   -7 = 4*-2 + 1     -> -7 div -2 = 4,  -7 rem -2 = 1                     -/
/-    7 = 3*2 + 1      ->  7 div  2 = 3,   7 rem  2 = 1                     -/
/- ====================================================================== -/

#eval convOK "INT_DIV_CONV -7 div 2 (=-4)"
  "(-- &7) div &2" "(-- &7) div &2 = -- &4" Session.INT_DIV_CONV
#eval convOK "INT_REM_CONV -7 rem 2 (=1)"
  "(-- &7) rem &2" "(-- &7) rem &2 = &1" Session.INT_REM_CONV
#eval convOK "INT_DIV_CONV 7 div -2 (=-3)"
  "&7 div (-- &2)" "&7 div (-- &2) = -- &3" Session.INT_DIV_CONV
#eval convOK "INT_REM_CONV 7 rem -2 (=1)"
  "&7 rem (-- &2)" "&7 rem (-- &2) = &1" Session.INT_REM_CONV
#eval convOK "INT_DIV_CONV -7 div -2 (=4)"
  "(-- &7) div (-- &2)" "(-- &7) div (-- &2) = &4" Session.INT_DIV_CONV
#eval convOK "INT_REM_CONV -7 rem -2 (=1)"
  "(-- &7) rem (-- &2)" "(-- &7) rem (-- &2) = &1" Session.INT_REM_CONV
#eval convOK "INT_DIV_CONV 7 div 2 (=3)"
  "&7 div &2" "&7 div &2 = &3" Session.INT_DIV_CONV
#eval convOK "INT_REM_CONV 7 rem 2 (=1)"
  "&7 rem &2" "&7 rem &2 = &1" Session.INT_REM_CONV
-- exact division: remainder 0.
#eval convOK "INT_DIV_CONV 6 div 3 (=2)"
  "&6 div &3" "&6 div &3 = &2" Session.INT_DIV_CONV
#eval convOK "INT_REM_CONV -6 rem 3 (=0)"
  "(-- &6) rem &3" "(-- &6) rem &3 = &0" Session.INT_REM_CONV

/- ====================================================================== -/
/- (5) DECISION PROCEDURES: INT_ARITH and INTEGER_RULE.                    -/
/-     Provable goals -> ruleOK with the goal itself; false -> failsOK.    -/
/- ====================================================================== -/

-- INT_ARITH.hlp worked examples (verbatim goals).
#eval ruleOK "INT_ARITH.hlp linear ineq"
  (onGoal Session.INT_ARITH "!x y:int. x <= y + &1 ==> x + &2 < y + &4")
  "!x y:int. x <= y + &1 ==> x + &2 < y + &4"
#eval ruleOK "INT_ARITH.hlp square expansion"
  (onGoal Session.INT_ARITH "(x + y:int) pow 2 = x pow 2 + &2 * x * y + y pow 2")
  "(x + y:int) pow 2 = x pow 2 + &2 * x * y + y pow 2"
-- INT_ARITH discreteness: TRUE over the integers (false over the reals) - the
-- raison d'etre of a dedicated integer procedure.
#eval ruleOK "INT_ARITH discreteness abs<1 ==> eq"
  (onGoal Session.INT_ARITH "!x y:int. abs(x - y) < &1 ==> x = y")
  "!x y:int. abs(x - y) < &1 ==> x = y"
#eval ruleOK "INT_ARITH negation totality"
  (onGoal Session.INT_ARITH "!n:int. &0 <= n \\/ &0 <= --n")
  "!n:int. &0 <= n \\/ &0 <= --n"
-- INT_ARITH must REJECT a false linear goal.
#eval failsOK "INT_ARITH false: n < n"
  (onGoal Session.INT_ARITH "!n:int. n < n")
#eval failsOK "INT_ARITH false: 0 = 1"
  (onGoal Session.INT_ARITH "(&0:int) = &1")

-- INTEGER_RULE.hlp worked examples (verbatim goals).
#eval ruleOK "INTEGER_RULE.hlp congruence/divides"
  (onGoal Session.INTEGER_RULE "!x y n:int. (x == y) (mod n) ==> (n divides x <=> n divides y)")
  "!x y n:int. (x == y) (mod n) ==> (n divides x <=> n divides y)"
#eval ruleOK "INTEGER_RULE.hlp gcd divides"
  (onGoal Session.INTEGER_RULE "!a b d:int. d divides gcd(a,b) <=> d divides a /\\ d divides b")
  "!a b d:int. d divides gcd(a,b) <=> d divides a /\\ d divides b"
#eval ruleOK "INTEGER_RULE.hlp coprime product"
  (onGoal Session.INTEGER_RULE "!x y. coprime(x * y,x pow 2 + y pow 2) <=> coprime(x,y)")
  "!x y. coprime(x * y,x pow 2 + y pow 2) <=> coprime(x,y)"
#eval ruleOK "INTEGER_RULE.hlp linear congruence exists"
  (onGoal Session.INTEGER_RULE "!a b n:int. coprime(a,n) ==> ?x. (a * x == b) (mod n)")
  "!a b n:int. coprime(a,n) ==> ?x. (a * x == b) (mod n)"
-- INTEGER_RULE must REJECT a plainly false divisibility goal.
#eval failsOK "INTEGER_RULE false: 2 divides 3"
  (onGoal Session.INTEGER_RULE "(&2:int) divides &3")
