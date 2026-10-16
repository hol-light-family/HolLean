/- File: HolTutorial/RecursiveDefinitions.lean
Translation of HOL Light's Tutorial/Recursive_definitions.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/

import HolTutorial.Common

open HolCore.Kernel Session HolLight.Syntax HolTutorial

namespace HolTutorial.RecursiveDefinitions

/- Helpers: the session's IO-valued rules lifted into `ExceptT String IO`, so
   tactic scripts can use them as `(← ar ...)` inside a `prove` the way the
   OCaml inlines `ARITH_RULE`, `NUM_RING`, etc.  `prove` here is the session's
   `prove`, lifted the same way. -/
private unsafe def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private unsafe def rwc (ths : List thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (REWRITE_CONV ths tm)
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

#eval phrase 1
unsafe def fib : thm := keep "fib" fun _ => define
 [[fib n = if n = 0 \/ n = 1 then 1 else fib(n - 1) + fib(n - 2)]]
#eval fib

#eval phrase 2
unsafe def fib2 : thm := keep "fib2" fun _ => define
 [[(fib2 0 = 1) /\
  (fib2 1 = 1) /\
  (fib2 (n + 2) = fib2(n) + fib2(n + 1))]]
#eval fib2

#eval phrase 3
unsafe def halve : thm := keep "halve" fun _ => define [[halve (2 * n) = n]]
#eval halve

#eval phrase 4
unsafe def unknown : thm := keep "unknown" fun _ => define [[unknown n = unknown(n + 1)]]
#eval unknown

#eval phrase 5
#eval define
 [[!n. collatz(n) = if n <= 1 then n
                   else if EVEN(n) then collatz(n DIV 2)
                   else collatz(3 * n + 1)]]

#eval phrase 6
unsafe def fusc_def : thm := keep "fusc_def" fun _ => define
 [[(fusc (2 * n) = if n = 0 then 0 else fusc(n)) /\
  (fusc (2 * n + 1) = if n = 0 then 1 else fusc(n) + fusc(n + 1))]]
#eval fusc_def

#eval phrase 7
unsafe def fusc : thm := keep "fusc" fun _ => (do
  prove ([[fusc 0 = 0 /\
   fusc 1 = 1 /\
   fusc (2 * n) = fusc(n) /\
   fusc (2 * n + 1) = fusc(n) + fusc(n + 1)]])
   (REWRITE_TAC [fusc_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (← HolLight.INST [([[0]], [[n:num]])] fusc_def) THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval fusc

#eval phrase 8
unsafe def binom : thm := keep "binom" fun _ => define
 [[(!n. binom(n,0) = 1) /\
  (!k. binom(0,SUC(k)) = 0) /\
  (!n k. binom(SUC(n),SUC(k)) = binom(n,SUC(k)) + binom(n,k))]]
#eval binom

#eval phrase 9
unsafe def BINOM_LT : thm := keep "BINOM_LT" fun _ => (do
  prove ([[!n k. n < k ==> (binom(n,k) = 0)]])
   (INDUCT_TAC THEN INDUCT_TAC THEN REWRITE_TAC [binom, ARITH, LT_SUC, LT] THEN
    ASM_SIMP_TAC [(← ar [[n < k ==> n < SUC(k)]]), ARITH])
  : ExceptT String IO thm).run
#eval BINOM_LT

#eval phrase 10
unsafe def BINOM_REFL : thm := keep "BINOM_REFL" fun _ => (do
  prove ([[!n. binom(n,n) = 1]])
   (INDUCT_TAC THEN ASM_SIMP_TAC [binom, BINOM_LT, LT, ARITH])
  : ExceptT String IO thm).run
#eval BINOM_REFL

#eval phrase 11
unsafe def BINOM_FACT : thm := keep "BINOM_FACT" fun _ => (do
  prove ([[!n k. FACT n * FACT k * binom(n+k,k) = FACT(n + k)]])
   (INDUCT_TAC THEN REWRITE_TAC [FACT, ADD_CLAUSES, MULT_CLAUSES, BINOM_REFL] THEN
    INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, FACT, MULT_CLAUSES, binom] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC (← HolLight.q r"SUC k")) THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC [ADD_CLAUSES, FACT, binom] THEN CONV_TAC NUM_RING)
  : ExceptT String IO thm).run
#eval BINOM_FACT

#eval phrase 12
unsafe def BINOMIAL_THEOREM : thm := keep "BINOMIAL_THEOREM" fun _ => (do
  prove ([[!n. (x + y) EXP n = nsum(0..n) (\k. binom(n,k) * x EXP k * y EXP (n - k))]])
   (INDUCT_TAC THEN ASM_REWRITE_TAC [EXP] THEN
    REWRITE_TAC [NSUM_SING_NUMSEG, binom, SUB_REFL, EXP, MULT_CLAUSES] THEN
    SIMP_TAC [NSUM_CLAUSES_LEFT, ADD1, (← ar [[0 <= n + 1]]), NSUM_OFFSET] THEN
    ASM_REWRITE_TAC [EXP, binom, (← HolLight.GSYM ADD1), (← HolLight.GSYM NSUM_LMUL)] THEN
    REWRITE_TAC [RIGHT_ADD_DISTRIB, NSUM_ADD_NUMSEG, MULT_CLAUSES, SUB_0] THEN
    MATCH_MP_TAC (← ar [[a = e /\ b = c + d ==> a + b = c + d + e]]) THEN
    CONJ_TAC THENL [REWRITE_TAC [MULT_AC, SUB_SUC], REWRITE_TAC [(← HolLight.GSYM EXP)]] THEN
    SIMP_TAC [ADD1, (← HolLight.SYM (← rwc [NSUM_OFFSET] [[nsum(m+1..n+1) (\i. f i)]]))] THEN
    REWRITE_TAC [NSUM_CLAUSES_NUMSEG, (← HolLight.GSYM ADD1), LE_SUC, LE_0] THEN
    SIMP_TAC [NSUM_CLAUSES_LEFT, LE_0] THEN
    SIMP_TAC [BINOM_LT, LT, MULT_CLAUSES, ADD_CLAUSES, SUB_0, EXP, binom] THEN
    SIMP_TAC [ARITH, (← ar [[k <= n ==> SUC n - k = SUC(n - k)]]), EXP] THEN
    REWRITE_TAC [MULT_AC])
  : ExceptT String IO thm).run
#eval BINOMIAL_THEOREM

end HolTutorial.RecursiveDefinitions
