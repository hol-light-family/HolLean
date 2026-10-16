/- File: HolTutorial/NumberTheory.lean
Translation of HOL Light's Tutorial/Number_theory.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/

import HolTutorial.Common

open HolCore.Kernel Session HolLight.Syntax HolTutorial
open SessionLibrary.Prime SessionLibrary.Pocklington SessionLibrary.Binomial

namespace HolTutorial.NumberTheory

/- Helpers: the session's `prove` lifted into `ExceptT String IO`, so tactic
   scripts read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

#eval phrase 1
-- needs "Library/prime.ml";;
#eval SessionLibrary.Prime.ensurePrime

#eval phrase 2
-- needs "Library/pocklington.ml";;
#eval SessionLibrary.Pocklington.ensurePocklington

#eval phrase 3
-- needs "Library/binomial.ml";;
#eval SessionLibrary.Binomial.ensureBinomial

#eval phrase 4
-- prioritize_num();;
#eval Session.prioritize_num

#eval phrase 5
/- let FERMAT_PRIME_CONV n = ... ;;   (OCaml prints `val FERMAT_PRIME_CONV :
   int -> thm = <fun>`) -/
unsafe def FERMAT_PRIME_CONV (n : Int) : IO (Except String thm) := (do
  let m ← ExceptT.mk (pure (mk_small_numeral n))
  let base : term := [[prime(2 EXP (2 EXP x) + 1)]]
  let substFn ← ExceptT.mk (HolCore.Basics.subst [(m, [[x:num]])])
  let tm ← ExceptT.mk (substFn base)
  ExceptT.mk ((HolLight.RAND_CONV NUM_REDUCE_CONV THENC PRIME_CONV) tm)
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 6
#eval FERMAT_PRIME_CONV 0

#eval phrase 7
#eval FERMAT_PRIME_CONV 1

#eval phrase 8
#eval FERMAT_PRIME_CONV 2

#eval phrase 9
#eval FERMAT_PRIME_CONV 3

#eval phrase 10
#eval FERMAT_PRIME_CONV 4

#eval phrase 11
#eval FERMAT_PRIME_CONV 5

#eval phrase 12
#eval FERMAT_PRIME_CONV 6

#eval phrase 13
#eval FERMAT_PRIME_CONV 7

#eval phrase 14
#eval FERMAT_PRIME_CONV 8

#eval phrase 15
unsafe def CONG_TRIVIAL : thm := keep "CONG_TRIVIAL" fun _ => (do
  prove ([[!x y. n divides x /\ n divides y ==> (x == y) (mod n)]])
   (MESON_TAC [CONG_0, CONG_SYM, CONG_TRANS])
  : ExceptT String IO thm).run
#eval CONG_TRIVIAL

#eval phrase 16
/- let LITTLE_CHECK_CONV tm = ... ;;   (prints `<fun>`) -/
unsafe def LITTLE_CHECK_CONV (tm : term) : IO (Except String thm) := (do
  let th ← ExceptT.mk ((HolLight.RATOR_CONV (HolLight.LAND_CONV NUM_EXP_CONV) THENC CONG_CONV) tm)
  Session.EQT_ELIM th
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 17
#eval LITTLE_CHECK_CONV [[(9 EXP 8 == 9) (mod 3)]]

#eval phrase 18
#eval LITTLE_CHECK_CONV [[(9 EXP 3 == 9) (mod 3)]]

#eval phrase 19
#eval LITTLE_CHECK_CONV [[(10 EXP 7 == 10) (mod 7)]]

#eval phrase 20
#eval LITTLE_CHECK_CONV [[(2 EXP 7 == 2) (mod 7)]]

#eval phrase 21
#eval LITTLE_CHECK_CONV [[(777 EXP 13 == 777) (mod 13)]]

#eval phrase 22
unsafe def DIVIDES_FACT_PRIME : thm := keep "DIVIDES_FACT_PRIME" fun _ => (do
  prove ([[!p. prime p ==> !n. p divides (FACT n) <=> p <= n]])
   (GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC [FACT, LE] THENL
     [ASM_MESON_TAC [DIVIDES_ONE, PRIME_0, PRIME_1],
      ASM_MESON_TAC [PRIME_DIVPROD_EQ, DIVIDES_LE, NOT_SUC, DIVIDES_REFL,
                     (← ExceptT.mk (ARITH_RULE [[~(p <= n) /\ p <= SUC n ==> p = SUC n]]))]])
  : ExceptT String IO thm).run
#eval DIVIDES_FACT_PRIME

#eval phrase 23
unsafe def DIVIDES_BINOM_PRIME : thm := keep "DIVIDES_BINOM_PRIME" fun _ => (do
  prove ([[!n p. prime p /\ 0 < n /\ n < p ==> p divides binom(p,n)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ExceptT.mk (HolLight.AP_TERM ([[(divides) p]])
             (← ExceptT.mk (HolLight.SPECL [ [[p - n]], [[n:num]] ] BINOM_FACT)))) THEN
    ASM_SIMP_TAC [DIVIDES_FACT_PRIME, PRIME_DIVPROD_EQ, SUB_ADD, LT_IMP_LE] THEN
    ASM_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM NOT_LT)), LT_REFL] THEN
    ASM_SIMP_TAC [(← ExceptT.mk (ARITH_RULE [[0 < n /\ n < p ==> p - n < p]]))])
  : ExceptT String IO thm).run
#eval DIVIDES_BINOM_PRIME

#eval phrase 24
unsafe def DIVIDES_NSUM : thm := keep "DIVIDES_NSUM" fun _ => (do
  prove ([[!m n. (!i. m <= i /\ i <= n ==> p divides f(i)) ==> p divides nsum(m..n) f]])
   (GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [NSUM_CLAUSES_NUMSEG] THEN
    ASM_MESON_TAC [LE, LE_TRANS, DIVIDES_0, DIVIDES_ADD, LE_REFL])
  : ExceptT String IO thm).run
#eval DIVIDES_NSUM

#eval phrase 25
unsafe def FLT_LEMMA : thm := keep "FLT_LEMMA" fun _ => (do
  prove ([[!p a b. prime p ==> ((a + b) EXP p == a EXP p + b EXP p) (mod p)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [BINOMIAL_THEOREM] THEN
    SUBGOAL_THEN ([[1 <= p /\ 0 < p]]) STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP PRIME_IMP_NZ) THEN ARITH_TAC, ALL_TAC] THEN
    ASM_SIMP_TAC [NSUM_CLAUSES_LEFT, LE_0, ARITH, NSUM_CLAUSES_RIGHT] THEN
    REWRITE_TAC [SUB_0, SUB_REFL, EXP, binom, BINOM_REFL, MULT_CLAUSES] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [(← ExceptT.mk (ARITH_RULE [[a + b = (b + 0) + a]]))] THEN
    REPEAT (MATCH_MP_TAC CONG_ADD THEN REWRITE_TAC [CONG_REFL]) THEN
    REWRITE_TAC [CONG_0] THEN MATCH_MP_TAC DIVIDES_NSUM THEN
    ASM_MESON_TAC [DIVIDES_RMUL, DIVIDES_BINOM_PRIME,
      (← ExceptT.mk (ARITH_RULE
        [[0 < p /\ 1 <= i /\ i <= p - 1 ==> 0 < i /\ i < p]]))])
  : ExceptT String IO thm).run
#eval FLT_LEMMA

#eval phrase 26
unsafe def FERMAT_LITTLE : thm := keep "FERMAT_LITTLE" fun _ => (do
  prove ([[!p a. prime p ==> (a EXP p == a) (mod p)]])
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    INDUCT_TAC THENL
     [ASM_MESON_TAC [EXP_EQ_0, CONG_REFL, PRIME_0],
      ASM_MESON_TAC [ADD1, FLT_LEMMA, EXP_ONE, CONG_ADD, CONG_TRANS, CONG_REFL]])
  : ExceptT String IO thm).run
#eval FERMAT_LITTLE

#eval phrase 27
unsafe def FERMAT_LITTLE_COPRIME : thm := keep "FERMAT_LITTLE_COPRIME" fun _ => (do
  prove ([[!p a. prime p /\ coprime(a,p) ==> (a EXP (p - 1) == 1) (mod p)]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_MULT_LCANCEL THEN
    EXISTS_TAC [[a:num]] THEN ASM_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM (← ExceptT.mk (HolLight.CONJUNCT2 EXP))))] THEN
    ASM_SIMP_TAC [PRIME_IMP_NZ, (← ExceptT.mk (ARITH_RULE [[~(p = 0) ==> SUC(p - 1) = p]]))] THEN
    ASM_SIMP_TAC [FERMAT_LITTLE, MULT_CLAUSES])
  : ExceptT String IO thm).run
#eval FERMAT_LITTLE_COPRIME

#eval phrase 28
unsafe def FERMAT_LITTLE_VARIANT : thm := keep "FERMAT_LITTLE_VARIANT" fun _ => (do
  prove ([[!p a. prime p ==> (a EXP (1 + m * (p - 1)) == a) (mod p)]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (DISJ_CASES_TAC o HolLight.SPEC [[a:num]] o HolLight.MATCH_MP PRIME_COPRIME_STRONG)
    THENL [ASM_MESON_TAC [CONG_TRIVIAL, ADD_AC, ADD1, DIVIDES_REXP_SUC],
           ALL_TAC] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [(← ExceptT.mk (ARITH_RULE [[a = a * 1]]))] THEN
    REWRITE_TAC [EXP_ADD, EXP_1] THEN MATCH_MP_TAC CONG_MULT THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM EXP_EXP)), CONG_REFL] THEN
    ASM_MESON_TAC [COPRIME_SYM, COPRIME_EXP, PHI_PRIME, FERMAT_LITTLE_COPRIME])
  : ExceptT String IO thm).run
#eval FERMAT_LITTLE_VARIANT

#eval phrase 29
unsafe def RSA : thm := keep "RSA" fun _ => (do
  prove ([[prime p /\ prime q /\ ~(p = q) /\
   (d * e == 1) (mod ((p - 1) * (q - 1))) /\
   plaintext < p * q /\ (ciphertext = (plaintext EXP e) MOD (p * q))
   ==> (plaintext = (ciphertext EXP d) MOD (p * q))]])
   (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [MOD_EXP_MOD, MULT_EQ_0, PRIME_IMP_NZ, EXP_EXP] THEN
    SUBGOAL_THEN ([[(plaintext == plaintext EXP (e * d)) (mod (p * q))]]) MP_TAC THENL
     [ALL_TAC, ASM_SIMP_TAC [CONG, MULT_EQ_0, PRIME_IMP_NZ, MOD_LT]] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [MULT_SYM] THEN
    FIRST_X_ASSUM (DISJ_CASES_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [CONG_TO_1]) THENL
     [ASM_MESON_TAC [MULT_EQ_1, (← ExceptT.mk (ARITH_RULE [[p - 1 = 1 <=> p = 2]]))], ALL_TAC] THEN
    MATCH_MP_TAC CONG_CHINESE THEN ASM_SIMP_TAC [DISTINCT_PRIME_COPRIME] THEN
    ASM_MESON_TAC [FERMAT_LITTLE_VARIANT, MULT_AC, CONG_SYM])
  : ExceptT String IO thm).run
#eval RSA

end HolTutorial.NumberTheory
