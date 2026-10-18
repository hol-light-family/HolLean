/- File: HolExamples/GcdRecurrence.lean
Translation of HOL Light's Examples/gcdrecurrence.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionLibrary.Prime SessionLibrary.Integer SessionLibrary.GroupTheory
namespace HolExamples.GcdRecurrence

/- Helpers: the session's rules lifted into `ExceptT String IO`, so the tactic
   scripts read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private unsafe def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def ec {α : Type} (x : Except String α) : ExceptT String IO α := ExceptT.mk (pure x)

-- ========================================================================= --
-- Some divisibility properties of certain linear integer recurrences.       --
-- ========================================================================= --

#eval phrase 1
-- needs "Library/prime.ml";;
#eval SessionLibrary.Prime.ensurePrime

#eval phrase 2
-- needs "Library/integer.ml";;
#eval SessionLibrary.Integer.ensureInteger

#eval phrase 3
-- prioritize_int();;
#eval Session.prioritize_int

-- ------------------------------------------------------------------------- --
-- A customized induction principle.                                         --
-- ------------------------------------------------------------------------- --

#eval phrase 4
unsafe def INDUCT_SPECIAL : thm := keep "INDUCT_SPECIAL" fun _ => (do
  prove ([[!P. (!n. P 0 n) /\
       (!m n. P m n <=> P n m) /\
       (!m n. P m n ==> P n (m + n))
       ==> !m n. P m n]])
   (GEN_TAC THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN WF_INDUCT_TAC [[m + n:num]] THEN
    ASM_CASES_TAC [[m = 0]] THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    ASM_CASES_TAC [[n = 0]] THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    DISJ_CASES_THEN MP_TAC (← ar [[m <= n:num \/ n <= m]]) THEN
    REWRITE_TAC [LE_EXISTS] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[p:num]]) SUBST_ALL_TAC) THENL
     [ALL_TAC, HolLight.ASM (GEN_REWRITE_TAC HolCore.Lib.I) []] THEN
    MATCH_MP_TAC (← HolLight.ASSUME [[!m n:num. P m n ==> P n (m + n)]]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC)
  : ExceptT String IO thm).run
#eval INDUCT_SPECIAL

-- ------------------------------------------------------------------------- --
-- The main results; to literally apply integer gcd we need nonnegativity.   --
-- ------------------------------------------------------------------------- --

#eval phrase 5
unsafe def INT_DIVISORS_RECURRENCE : thm := keep "INT_DIVISORS_RECURRENCE" fun _ => (do
  prove ([[!G a b. G(0) = &0 /\ G(1) = &1 /\
           coprime(a,b) /\ (!n. G(n + 2) = a * G(n + 1) + b * G(n))
           ==> !d m n. d divides (G m) /\ d divides (G n) <=>
                       d divides G(gcd(m,n))]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[!n. coprime(G(n + 1),b)]]) ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM_REWRITE_TAC [ARITH, (← ar [[SUC n + 1 = n + 2]])] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN NUMBER_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!n. coprime(G(n + 1),G n)]]) ASSUME_TAC THENL
     [INDUCT_TAC THENL [ASM_REWRITE_TAC [ARITH] THEN NUMBER_TAC, ALL_TAC] THEN
      REPEAT (FIRST_X_ASSUM (ASSUME_TAC o HolLight.SPEC [[n:num]])) THEN
      ASM_REWRITE_TAC [ADD1, (← ar [[(n + 1) + 1 = n + 2]])] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN INTEGER_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!m p. G(m + 1 + p) = G(m + 1) * G(p + 1) + b * G(m) * G(p)]])
    ASSUME_TAC THENL
     [INDUCT_TAC THENL
       [ASM_REWRITE_TAC [ADD_CLAUSES, ADD_AC] THEN INTEGER_TAC, ALL_TAC] THEN
      ASM_REWRITE_TAC [(← ar [[SUC m + 1 + p = (m + p) + 2]])] THEN
      ASM_REWRITE_TAC [(← ar [[SUC m + 1 = m + 2]])] THEN
      ASM_REWRITE_TAC [(← ar [[(m + p) + 1 = m + 1 + p]])] THEN
      INDUCT_TAC THEN ASM_REWRITE_TAC [ARITH, ADD_CLAUSES] THEN
      ASM_REWRITE_TAC [(← ar [[SUC(m + p) = m + 1 + p]])] THEN
      ASM_REWRITE_TAC [(← ar [[SUC(m + 1) = m + 2]]), ARITH] THEN
      REWRITE_TAC [ADD1] THEN ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!m p:num. gcd(G(m + p),G m) = gcd(G m,G p)]]) ASSUME_TAC THENL
     [INDUCT_TAC THEN
      REWRITE_TAC [ADD_CLAUSES, (← ec (EQT_INTRO (← ExceptT.mk (HolLight.SPEC_ALL INT_GCD_SYM))))] THEN
      ASM_REWRITE_TAC [ADD1, (← ar [[(m + p) + 1 = m + 1 + p]])] THEN
      GEN_TAC THEN SIMP_TAC [INT_GCD_POS, (← ExceptT.mk (HolLight.GSYM INT_DIVIDES_ANTISYM_POS))] THEN
      MP_TAC (← ExceptT.mk (HolLight.SPEC ([[m:num]]) (← HolLight.ASSUME [[!n. coprime(G(n + 1),b)]]))) THEN
      MP_TAC (← ExceptT.mk (HolLight.SPEC ([[m:num]]) (← HolLight.ASSUME [[!n. coprime(G(n + 1),G n)]]))) THEN
      INTEGER_TAC,
      ALL_TAC] THEN
    GEN_TAC THEN MATCH_MP_TAC INDUCT_SPECIAL THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC [GCD_0, INT_DIVIDES_0], MESON_TAC [GCD_SYM], ALL_TAC] THEN
    ASM_MESON_TAC [GCD_ADD, INT_DIVIDES_GCD, INT_GCD_SYM, ADD_SYM, GCD_SYM])
  : ExceptT String IO thm).run
#eval INT_DIVISORS_RECURRENCE

#eval phrase 6
unsafe def INT_GCD_RECURRENCE : thm := keep "INT_GCD_RECURRENCE" fun _ => (do
  prove ([[!G a b. G(0) = &0 /\ G(1) = &1 /\
           coprime(a,b) /\ (!n. G(n + 2) = a * G(n + 1) + b * G(n)) /\
           (!n. &0 <= G n)
           ==> !m n. gcd(G m,G n) = G(gcd(m,n))]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM INT_DIVIDES_ANTISYM_POS)), INT_GCD_POS] THEN
    REWRITE_TAC [INT_DIVIDES_ANTISYM_DIVISORS, INT_DIVIDES_GCD] THEN
    ASM_MESON_TAC [INT_DIVISORS_RECURRENCE])
  : ExceptT String IO thm).run
#eval INT_GCD_RECURRENCE

-- ------------------------------------------------------------------------- --
-- Natural number variants of the same results.                              --
-- ------------------------------------------------------------------------- --

#eval phrase 7
unsafe def GCD_RECURRENCE : thm := keep "GCD_RECURRENCE" fun _ => (do
  prove ([[!G a b. G(0) = 0 /\ G(1) = 1 /\
           coprime(a,b) /\ (!n. G(n + 2) = a * G(n + 1) + b * G(n))
           ==> !m n. gcd(G m,G n) = G(gcd(m,n))]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ExceptT.mk (HolLight.SPECL [ [[& o (G:num->num)]], [[&a:int]], [[&b:int]] ]
          INT_GCD_RECURRENCE)) THEN
    ASM_REWRITE_TAC [o_THM, (← ExceptT.mk (HolLight.GSYM INT_OF_NUM_ADD)), (← ExceptT.mk (HolLight.GSYM INT_OF_NUM_MUL))] THEN
    ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM num_coprime)), INT_POS, (← ExceptT.mk (HolLight.GSYM NUM_GCD)), INT_OF_NUM_EQ])
  : ExceptT String IO thm).run
#eval GCD_RECURRENCE

#eval phrase 8
unsafe def DIVISORS_RECURRENCE : thm := keep "DIVISORS_RECURRENCE" fun _ => (do
  prove ([[!G a b. G(0) = 0 /\ G(1) = 1 /\
           coprime(a,b) /\ (!n. G(n + 2) = a * G(n + 1) + b * G(n))
           ==> !d m n. d divides (G m) /\ d divides (G n) <=>
                       d divides G(gcd(m,n))]])
   (REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM DIVIDES_GCD))] THEN MESON_TAC [DIVISORS_EQ, GCD_RECURRENCE])
  : ExceptT String IO thm).run
#eval DIVISORS_RECURRENCE

-- ------------------------------------------------------------------------- --
-- Application 1: Mersenne numbers.                                          --
-- ------------------------------------------------------------------------- --

#eval phrase 9
unsafe def GCD_MERSENNE : thm := keep "GCD_MERSENNE" fun _ => (do
  prove ([[!m n. gcd(2 EXP m - 1,2 EXP n - 1) = 2 EXP (gcd(m,n)) - 1]])
   (SIMP_TAC [(← ExceptT.mk (HolLight.GSYM INT_OF_NUM_EQ)), NUM_GCD, (← ExceptT.mk (HolLight.GSYM INT_OF_NUM_SUB)),
             (← ExceptT.mk (HolLight.GSYM INT_OF_NUM_POW)), EXP_LT_0, ARITH,
             (← ar [[1 <= n <=> 0 < n]])] THEN
    MATCH_MP_TAC INT_GCD_RECURRENCE THEN
    MAP_EVERY EXISTS_TAC [ [[&3]], [[(-- &2)]] ] THEN
    REWRITE_TAC [INT_POW_ADD, INT_LE_SUB_LADD] THEN
    CONV_TAC INT_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM (← ExceptT.mk (INT_REDUCE_CONV [[&2 * &2 - &1]]))))] THEN
      SPEC_TAC ([[&2]], [[t:int]]) THEN INTEGER_TAC,
      INT_ARITH_TAC,
      GEN_TAC THEN MATCH_MP_TAC INT_POW_LE_1 THEN INT_ARITH_TAC])
  : ExceptT String IO thm).run
#eval GCD_MERSENNE

#eval phrase 10
unsafe def DIVIDES_MERSENNE : thm := keep "DIVIDES_MERSENNE" fun _ => (do
  prove ([[!m n. (2 EXP m - 1) divides (2 EXP n - 1) <=> m divides n]])
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [DIVIDES_GCD_LEFT, GCD_MERSENNE] THEN
    SIMP_TAC [EXP_EQ_0, EQ_EXP, ARITH_EQ, (← ar
     [[~(x = 0) /\ ~(y = 0) ==> (x - 1 = y - 1 <=> x = y)]])])
  : ExceptT String IO thm).run
#eval DIVIDES_MERSENNE

-- ------------------------------------------------------------------------- --
-- Application 2: the Fibonacci series.                                      --
-- ------------------------------------------------------------------------- --

#eval phrase 11
unsafe def fib : thm := keep "fib" fun _ => (do
  ExceptT.mk (define
   [[fib 0 = 0 /\ fib 1 = 1 /\ !n. fib(n + 2) = fib(n + 1) + fib(n)]])
  : ExceptT String IO thm).run
#eval fib

#eval phrase 12
unsafe def GCD_FIB : thm := keep "GCD_FIB" fun _ => (do
  prove ([[!m n. gcd(fib m,fib n) = fib(gcd(m,n))]])
   (MATCH_MP_TAC GCD_RECURRENCE THEN
    REPEAT (EXISTS_TAC [[1]]) THEN REWRITE_TAC [fib, COPRIME_1] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval GCD_FIB

#eval phrase 13
unsafe def FIB_EQ_0 : thm := keep "FIB_EQ_0" fun _ => (do
  prove ([[!n. fib n = 0 <=> n = 0]])
   (MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC [fib] THEN
    MATCH_MP_TAC num_INDUCTION THEN
    REWRITE_TAC [fib, (← ar [[SUC(SUC n) = n + 2]]), ADD_EQ_0] THEN
    SIMP_TAC [ADD1, ADD_EQ_0, ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [fib, ARITH_EQ])
  : ExceptT String IO thm).run
#eval FIB_EQ_0

#eval phrase 14
unsafe def FIB_INCREASES_LE : thm := keep "FIB_INCREASES_LE" fun _ => (do
  prove ([[!m n. m <= n ==> fib m <= fib n]])
   (MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
    REWRITE_TAC [LE_REFL, LE_TRANS] THEN
    MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC [fib, ARITH] THEN
    REWRITE_TAC [ADD1, fib, (← ar [[(n + 1) + 1 = n + 2]])] THEN
    ARITH_TAC)
  : ExceptT String IO thm).run
#eval FIB_INCREASES_LE

#eval phrase 15
unsafe def FIB_INCREASES_LT : thm := keep "FIB_INCREASES_LT" fun _ => (do
  prove ([[!m n. 2 <= m /\ m < n ==> fib m < fib n]])
   (INDUCT_TAC THEN REWRITE_TAC [ARITH] THEN
    REPEAT STRIP_TAC THEN TRANS_TAC LTE_TRANS [[fib(m + 2)]] THEN
    ASM_SIMP_TAC [FIB_INCREASES_LE, (← ar [[m + 2 <= n <=> SUC m < n]])] THEN
    REWRITE_TAC [fib, ADD1, (← ar [[m < m + n <=> ~(n = 0)]]), FIB_EQ_0] THEN
    ASM_ARITH_TAC)
  : ExceptT String IO thm).run
#eval FIB_INCREASES_LT

#eval phrase 16
unsafe def FIB_EQ_1 : thm := keep "FIB_EQ_1" fun _ => (do
  prove ([[!n. fib n = 1 <=> n = 1 \/ n = 2]])
   (MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC [fib, ARITH] THEN
    MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC [fib, ARITH] THEN
    REWRITE_TAC [fib, (← ar [[SUC(SUC n) = n + 2]])] THEN
    REWRITE_TAC [FIB_EQ_0, ADD_EQ_0, ARITH, (← ar
     [[m + n = 1 <=> m = 0 /\ n = 1 \/ m = 1 /\ n = 0]])] THEN
    ARITH_TAC)
  : ExceptT String IO thm).run
#eval FIB_EQ_1

#eval phrase 17
unsafe def DIVIDES_FIB : thm := keep "DIVIDES_FIB" fun _ => (do
  prove ([[!m n. (fib m) divides (fib n) <=> m divides n \/ n = 0 \/ m = 2]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [DIVIDES_GCD_LEFT, GCD_FIB] THEN
    MP_TAC (← ExceptT.mk (HolLight.SPECL [ [[gcd(m:num,n)]], [[m:num]] ] DIVIDES_LE)) THEN REWRITE_TAC [GCD] THEN
    ASM_CASES_TAC [[m = 0]] THEN ASM_REWRITE_TAC [GCD_0, fib, FIB_EQ_0, ARITH] THEN
    ASM_CASES_TAC [[n = 0]] THEN ASM_REWRITE_TAC [GCD_0] THEN
    ASM_CASES_TAC [[gcd(m:num,n) = m]] THEN ASM_REWRITE_TAC [LE_LT] THEN
    ASM_CASES_TAC [[gcd(m:num,n) = 0]] THENL
     [ASM_MESON_TAC [GCD_ZERO], ALL_TAC] THEN
    ASM_CASES_TAC [[m:num = n]] THEN ASM_REWRITE_TAC [GCD_REFL, LT_REFL] THEN
    ASM_CASES_TAC [[2 <= gcd(m,n)]] THENL
     [MP_TAC (← ExceptT.mk (HolLight.SPECL [ [[gcd(m:num,n)]], [[m:num]] ] FIB_INCREASES_LT)) THEN
      ASM_ARITH_TAC,
      ASM_CASES_TAC [[gcd(m,n) = 1]] THENL [ASM_REWRITE_TAC [], ASM_ARITH_TAC] THEN
      DISCH_TAC THEN CONV_TAC (HolLight.LAND_CONV HolLight.SYM_CONV) THEN
      REWRITE_TAC [FIB_EQ_1, fib] THEN ASM_ARITH_TAC])
  : ExceptT String IO thm).run
#eval DIVIDES_FIB

-- ------------------------------------------------------------------------- --
-- Application 3: solutions of the Pell equation x^2 = (a^2 - 1) y^2 + 1.    --
-- All solutions are of the form (pellx a n,pelly a n); see Examples/pell.ml --
-- ------------------------------------------------------------------------- --

#eval phrase 18
unsafe def pellx : thm := keep "pellx" fun _ => (do
  ExceptT.mk (define
   [[(!a. pellx a 0 = 1) /\
   (!a. pellx a 1 = a) /\
   (!a n. pellx a (n + 2) = 2 * a * pellx a (n + 1) - pellx a n)]])
  : ExceptT String IO thm).run
#eval pellx

#eval phrase 19
unsafe def pelly : thm := keep "pelly" fun _ => (do
  ExceptT.mk (define
   [[(!a. pelly a 0 = 0) /\
   (!a. pelly a 1 = 1) /\
   (!a n. pelly a (n + 2) = 2 * a * pelly a (n + 1) - pelly a (n))]])
  : ExceptT String IO thm).run
#eval pelly

#eval phrase 20
unsafe def PELLY_INCREASES : thm := keep "PELLY_INCREASES" fun _ => (do
  prove ([[!a n. ~(a = 0) ==> pelly a n <= pelly a (n + 1)]])
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    INDUCT_TAC THEN
    ASM_SIMP_TAC [pelly, ARITH, LE_1, ADD1, (← ar [[(n + 1) + 1 = n + 2]])] THEN
    TRANS_TAC LE_TRANS [[2 * pelly a (n + 1) - pelly a n]] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    MATCH_MP_TAC (← ar [[a:num <= b ==> a - c <= b - c]]) THEN
    REWRITE_TAC [MULT_ASSOC, LE_MULT_RCANCEL] THEN ASM_ARITH_TAC)
  : ExceptT String IO thm).run
#eval PELLY_INCREASES

#eval phrase 21
unsafe def GCD_PELLY : thm := keep "GCD_PELLY" fun _ => (do
  prove ([[!a m n. ~(a = 0) ==> gcd(pelly a m,pelly a n) = pelly a (gcd(m,n))]])
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM INT_OF_NUM_EQ)), NUM_GCD] THEN
    MATCH_MP_TAC INT_GCD_RECURRENCE THEN
    MAP_EVERY EXISTS_TAC [ [[&2 * &a:int]], [[(-- &1:int)]] ] THEN
    REWRITE_TAC [pelly, INT_POS, INT_COPRIME_NEG, INT_COPRIME_1] THEN
    GEN_TAC THEN REWRITE_TAC [INT_OF_NUM_MUL, MULT_ASSOC] THEN
    REWRITE_TAC [(← ExceptT.mk (INT_ARITH [[a + -- &1 * b:int = a - b]]))] THEN
    MATCH_MP_TAC (← ExceptT.mk (HolLight.GSYM INT_OF_NUM_SUB)) THEN
    TRANS_TAC LE_TRANS [[1 * pelly a (n + 1)]] THEN
    REWRITE_TAC [LE_MULT_RCANCEL] THEN
    ASM_SIMP_TAC [MULT_CLAUSES, PELLY_INCREASES] THEN ASM_ARITH_TAC)
  : ExceptT String IO thm).run
#eval GCD_PELLY

end HolExamples.GcdRecurrence
