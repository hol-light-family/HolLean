/- File: Hol100/Wilson.lean
Translation of HOL Light's 100/wilson.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Pocklington
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionLibrary.Prime SessionLibrary.Pocklington
namespace Hol100.Wilson

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)

/- ========================================================================= -/
/- Wilson's theorem.                                                         -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/prime.ml";;
#eval SessionLibrary.Prime.ensurePrime

#eval phrase 2
-- needs "Library/pocklington.ml";;
#eval SessionLibrary.Pocklington.ensurePocklington

#eval phrase 3
#eval Session.prioritize_num

/- ------------------------------------------------------------------------- -/
/- Factorial in terms of products.                                           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def FACT_NPRODUCT : thm := keep "FACT_NPRODUCT" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[1 <= SUC n]])
  prove ([[!n. FACT(n) = nproduct(1..n) (\i. i)]])
   (INDUCT_TAC THEN
    REWRITE_TAC [FACT, NUMSEG_CLAUSES, ARITH, NPRODUCT_CLAUSES] THEN
    ASM_SIMP_TAC [h1, NPRODUCT_CLAUSES, FINITE_NUMSEG] THEN
    REWRITE_TAC [IN_NUMSEG] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval FACT_NPRODUCT

#eval phrase 5
def FACT_NPRODUCT_ALT : thm := keep "FACT_NPRODUCT_ALT" fun _ => (do
  let n1 ← ExceptT.mk (num_CONV (← ExceptT.mk [[1]]))
  let h1 ← ar (← ExceptT.mk [[n = 0 \/ 1 <= n]])
  prove ([[!n. FACT(n) = nproduct(2..n) (\i. i)]])
   (GEN_TAC THEN REWRITE_TAC [FACT_NPRODUCT] THEN
    DISJ_CASES_TAC h1 THEN
    ASM_REWRITE_TAC [n1, NUMSEG_CLAUSES] THEN
    REWRITE_TAC [ARITH, NPRODUCT_CLAUSES, FACT] THEN
    ASM_SIMP_TAC [(← HolLight.GSYM NUMSEG_LREC)] THEN
    SIMP_TAC [NPRODUCT_CLAUSES, FINITE_NUMSEG, IN_NUMSEG, MULT_CLAUSES] THEN
    ARITH_TAC)
  : ExceptT String IO thm).run
#eval FACT_NPRODUCT_ALT

/- ------------------------------------------------------------------------- -/
/- General "pairing up" theorem for products.                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 6
def NPRODUCT_PAIRUP_INDUCT : thm := keep "NPRODUCT_PAIRUP_INDUCT" fun _ => (do
  let r11 ← HolLight.SYM (← ExceptT.mk (NUM_REDUCE_CONV (← ExceptT.mk [[1 * 1]])))
  let a5 ← HolLight.ASSUME ([[FINITE(s:A->bool)]])
  let a4 ← HolLight.ASSUME ([[(b:A) IN s]])
  let a3 ← HolLight.ASSUME ([[(x:A) IN s]])
  let a2 ← HolLight.ASSUME ([[FINITE(s:A->bool)]])
  let a1 ← HolLight.ASSUME ([[(a:A) IN s]])
  let h1 ← ar (← ExceptT.mk [[~(n = 0) ==> n - 2 < n]])
  prove ([[!f r n s. FINITE s /\ CARD s = n /\
             (!x:A. x IN s ==> ?!y. y IN s /\ ~(y = x) /\
                                    (f(x) * f(y) == 1) (mod r))
             ==> (nproduct s f == 1) (mod r)]])
   (GEN_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC num_WF THEN X_GEN_TAC ([[n:num]]) THEN DISCH_TAC THEN
    X_GEN_TAC ([[s:A->bool]]) THEN ASM_CASES_TAC ([[s:A->bool = {}]]) THEN
    ASM_REWRITE_TAC [NPRODUCT_CLAUSES, CONG_REFL] THEN STRIP_TAC THEN
    ASM_CASES_TAC ([[n = 0]]) THENL [ASM_MESON_TAC [CARD_EQ_0], ALL_TAC] THEN
    FIRST_X_ASSUM (X_CHOOSE_TAC ([[a:A]]) o
      HolLight.GEN_REWRITE_RULE HolCore.Lib.I [(← HolLight.GSYM MEMBER_NOT_EMPTY)]) THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPEC ([[n - 2]])) THEN
    ASM_SIMP_TAC [h1] THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPEC ([[a:A]])) THEN REWRITE_TAC [a1] THEN
    REWRITE_TAC [EXISTS_UNIQUE] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[b:A]]) STRIP_ASSUME_TAC) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[(s DELETE a) DELETE (b:A)]])) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC [FINITE_DELETE] THEN
      SIMP_TAC [FINITE_DELETE, a2, CARD_DELETE] THEN
      ASM_REWRITE_TAC [IN_DELETE] THEN CONJ_TAC THENL [ARITH_TAC, ALL_TAC] THEN
      X_GEN_TAC ([[x:A]]) THEN STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o fun th => HolLight.MATCH_MP th a3) THEN
      REWRITE_TAC [EXISTS_UNIQUE] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC ([[y:A]]) THEN STRIP_TAC THEN CONJ_TAC THENL
       [ALL_TAC, ASM_MESON_TAC []] THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
       [ASM_MESON_TAC [MULT_SYM], ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o fun th => HolLight.MATCH_MP th a4) THEN
      REWRITE_TAC [EXISTS_UNIQUE_THM] THEN
      DISCH_THEN (MP_TAC o HolLight.SPECL [([[a:A]]), ([[x:A]])] o HolLight.CONJUNCT2) THEN
      ASM_MESON_TAC [MULT_SYM],
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN ([[s = (a:A) INSERT (b INSERT (s DELETE a DELETE b))]])
    SUBST1_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
    SIMP_TAC [NPRODUCT_CLAUSES, FINITE_INSERT, FINITE_DELETE, a5] THEN
    ASM_REWRITE_TAC [IN_INSERT, IN_DELETE, MULT_CLAUSES] THEN
    REWRITE_TAC [MULT_ASSOC] THEN
    ONCE_REWRITE_TAC [r11] THEN
    MATCH_MP_TAC CONG_MULT THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval NPRODUCT_PAIRUP_INDUCT

#eval phrase 7
def NPRODUCT_PAIRUP : thm := keep "NPRODUCT_PAIRUP" fun _ => (do
  prove ([[!f r s. FINITE s /\
           (!x:A. x IN s ==> ?!y. y IN s /\ ~(y = x) /\
                                  (f(x) * f(y) == 1) (mod r))
           ==> (nproduct s f == 1) (mod r)]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC NPRODUCT_PAIRUP_INDUCT THEN
    EXISTS_TAC ([[CARD(s:A->bool)]]) THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval NPRODUCT_PAIRUP

/- ------------------------------------------------------------------------- -/
/- Hence Wilson's theorem.                                                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 8
def WILSON : thm := keep "WILSON" fun _ => (do
  let h8 ← ar (← ExceptT.mk [[(x + 1) * 1 <= (x + 1) * x
      ==> 1 + (x + 1) * x - (x + 1) * 1 = x * x]])
  let gs1 ← HolLight.GSYM (← HolLight.SPEC ([[1]]) CONG_ADD_LCANCEL_EQ)
  let ap ← HolLight.ASSUME ([[prime p]])
  let h6 ← ar (← ExceptT.mk [[x = x * 1]])
  let gsa ← HolLight.GSYM SUB_ADD
  let h5 ← ar (← ExceptT.mk [[y < p /\ ~(y = p - 1) ==> y <= p - 2]])
  let h4 ← ar (← ExceptT.mk [[~(p = 0) /\ ~(p = 1) ==> 1 < p]])
  let h3 ← ar (← ExceptT.mk [[x <= p - 2 /\ ~(p = 0) ==> x < p]])
  let h2 ← ar (← ExceptT.mk [[2 <= y <=> 0 < y /\ ~(y = 1)]])
  let h1 ← ar (← ExceptT.mk [[x = 1 * x]])
  prove ([[!p. prime(p) ==> (FACT(p - 1) == p - 1) (mod p)]])
   (GEN_TAC THEN DISCH_TAC THEN
    ASM_CASES_TAC ([[p = 0]]) THENL [ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN
    ASM_CASES_TAC ([[p = 1]]) THENL [ASM_MESON_TAC [PRIME_1], ALL_TAC] THEN
    ASM_CASES_TAC ([[p = 2]]) THENL
     [ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC [CONG_REFL],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[FACT(p - 1) = FACT(p - 2) * (p - 1)]]) SUBST1_TAC THENL
     [SUBGOAL_THEN ([[p - 1 = SUC(p - 2)]])
       (fun th => REWRITE_TAC [th, FACT, MULT_AC]) THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [h1] THEN
    MATCH_MP_TAC CONG_MULT THEN REWRITE_TAC [CONG_REFL] THEN
    REWRITE_TAC [FACT_NPRODUCT_ALT] THEN MATCH_MP_TAC NPRODUCT_PAIRUP THEN
    REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
    X_GEN_TAC ([[x:num]]) THEN STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [([[p:num]]), ([[x:num]])] CONG_UNIQUE_INVERSE_PRIME) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [ASM_ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [EXISTS_UNIQUE_THM] THEN MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [MATCH_MP_TAC MONO_EXISTS,
      REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
      DISCH_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC] THEN
    X_GEN_TAC ([[y:num]]) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
     [ASM_CASES_TAC ([[y = 1]]) THEN
      ASM_REWRITE_TAC [h2] THEN
      UNDISCH_TAC ([[(x * y == 1) (mod p)]]) THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN
      ASM_SIMP_TAC [CONG, MOD_LT, h3, h4] THEN
      UNDISCH_TAC ([[2 <= x]]) THEN ARITH_TAC,
      MATCH_MP_TAC h5 THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
      UNDISCH_TAC ([[(x * y == 1) (mod p)]]) THEN ASM_REWRITE_TAC [] THEN
      DISCH_TAC THEN SUBGOAL_THEN ([[(x + 1 == 0) (mod p)]]) MP_TAC THENL
       [ALL_TAC,
        REWRITE_TAC [CONG_0] THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP DIVIDES_LE) THEN
        MAP_EVERY UNDISCH_TAC [([[2 <= x]]), ([[x <= p - 2]])] THEN ARITH_TAC] THEN
      MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC ([[x * p:num]]) THEN CONJ_TAC THENL
       [ALL_TAC, REWRITE_TAC [CONG_0] THEN MESON_TAC [divides, MULT_SYM]] THEN
      SUBGOAL_THEN ([[x * p = x + x * (p - 1)]]) SUBST1_TAC THENL
       [REWRITE_TAC [LEFT_SUB_DISTRIB, MULT_CLAUSES] THEN
        ONCE_REWRITE_TAC [ADD_SYM] THEN MATCH_MP_TAC gsa THEN
        GEN_REWRITE_TAC HolLight.LAND_CONV [h6] THEN
        ASM_REWRITE_TAC [LE_MULT_LCANCEL] THEN
        UNDISCH_TAC ([[~(p = 0)]]) THEN ARITH_TAC,
        ALL_TAC] THEN
      ONCE_REWRITE_TAC [CONG_SYM] THEN MATCH_MP_TAC CONG_ADD THEN
      ASM_REWRITE_TAC [CONG_REFL],
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN ([[((x + 1) * (x - 1) == 0) (mod p)]]) MP_TAC THENL
       [ALL_TAC,
        REWRITE_TAC [CONG_0] THEN
        DISCH_THEN (MP_TAC o HolLight.CONJ ap) THEN
        DISCH_THEN (MP_TAC o HolLight.MATCH_MP PRIME_DIVPROD) THEN
        DISCH_THEN (DISJ_CASES_THEN (MP_TAC o HolLight.MATCH_MP DIVIDES_LE)) THEN
        MAP_EVERY UNDISCH_TAC
          [([[2 <= x]]), ([[x <= p - 2]]), ([[~(p = 1)]]), ([[~(p = 0)]])] THEN
        ARITH_TAC] THEN
      ONCE_REWRITE_TAC [gs1] THEN
      SUBGOAL_THEN ([[1 + (x + 1) * (x - 1) = x * x]])
       (fun th => ASM_REWRITE_TAC [th, ARITH]) THEN
      REWRITE_TAC [LEFT_SUB_DISTRIB] THEN
      MATCH_MP_TAC h8 THEN
      REWRITE_TAC [LE_MULT_LCANCEL] THEN UNDISCH_TAC ([[2 <= x]]) THEN ARITH_TAC])
  : ExceptT String IO thm).run
#eval WILSON

/- ------------------------------------------------------------------------- -/
/- And in fact we have a converse.                                           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 9
def WILSON_EQ : thm := keep "WILSON_EQ" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[~(n = 0) ==> n - 1 + 1 = n]])
  let h1 ← ar (← ExceptT.mk [[x < y ==> x <= y - 1]])
  prove ([[!p. ~(p = 1) ==> (prime p <=> (FACT(p - 1) == p - 1) (mod p))]])
   (X_GEN_TAC ([[n:num]]) THEN DISCH_TAC THEN EQ_TAC THEN SIMP_TAC [WILSON] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP PRIME_FACTOR) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[p:num]]) STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP DIVIDES_LE) THEN
    ASM_CASES_TAC ([[n = 0]]) THEN ASM_REWRITE_TAC [] THENL
     [ASM_REWRITE_TAC [CONG_MOD_0] THEN CONV_TAC NUM_REDUCE_CONV, ALL_TAC] THEN
    REWRITE_TAC [LE_LT] THEN ASM_CASES_TAC ([[n:num = p]]) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP h1) THEN
    ASM_SIMP_TAC [(← HolLight.GSYM DIVIDES_FACT_PRIME)] THEN
    DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
    SUBGOAL_THEN ([[p divides FACT(n - 1) <=> p divides (n - 1)]]) SUBST1_TAC THENL
     [MATCH_MP_TAC CONG_DIVIDES THEN
      MATCH_MP_TAC CONG_DIVIDES_MODULUS THEN EXISTS_TAC ([[n:num]]) THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    DISCH_TAC THEN SUBGOAL_THEN ([[p divides 1]]) MP_TAC THENL
     [MATCH_MP_TAC DIVIDES_ADD_REVR THEN EXISTS_TAC ([[n - 1]]) THEN
      ASM_SIMP_TAC [h2],
      REWRITE_TAC [DIVIDES_ONE] THEN ASM_MESON_TAC [PRIME_1]])
  : ExceptT String IO thm).run
#eval WILSON_EQ

end Hol100.Wilson
