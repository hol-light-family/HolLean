/- File: Hol100/Perfect.lean
Translation of HOL Light's 100/perfect.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Prime
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Prime
namespace Hol100.Perfect

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- Perfect number theorems.                                                  -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/prime.ml";;
#eval SessionLibrary.Prime.ensurePrime

#eval phrase 2
#eval Session.prioritize_num

/- ------------------------------------------------------------------------- -/
/- The sum-of-divisors function.                                             -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def sigma : thm := keep "sigma" fun _ => new_definition
 [[sigma(n) = if n = 0 then 0 else nsum {d | d divides n} (\i. i)]]
#eval sigma

/- ------------------------------------------------------------------------- -/
/- Definition of perfection.                                                 -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def perfect : thm := keep "perfect" fun _ => new_definition
 [[perfect n <=> ~(n = 0) /\ sigma(n) = 2 * n]]
#eval perfect

/- ------------------------------------------------------------------------- -/
/- Various number-theoretic lemmas.                                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
def ODD_POW2_MINUS1 : thm := keep "ODD_POW2_MINUS1" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[k = k - 1 + 1 <=> ~(k = 0)]])
  prove ([[!k. ~(k = 0) ==> ODD(2 EXP k - 1)]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[EVEN(2 EXP k) <=> EVEN((2 EXP k - 1) + 1)]]) MP_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC [h1] THEN
      REWRITE_TAC [EXP_EQ_0, ARITH],
      ASM_REWRITE_TAC [(← HolLight.GSYM NOT_EVEN), EVEN_ADD, EVEN_EXP, ARITH]])
  : ExceptT String IO thm).run
#eval ODD_POW2_MINUS1

#eval phrase 6
def EVEN_ODD_DECOMP : thm := keep "EVEN_ODD_DECOMP" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[m < 2 * m <=> ~(m = 0)]])
  prove ([[!n. ~(n = 0) ==> ?r s. ODD s /\ n = 2 EXP r * s]])
   (MATCH_MP_TAC num_WF THEN X_GEN_TAC ([[n:num]]) THEN
    MP_TAC (← HolLight.SPEC ([[n:num]]) EVEN_OR_ODD) THEN
    REWRITE_TAC [EVEN_EXISTS, ODD_EXISTS] THEN
    DISCH_THEN (DISJ_CASES_THEN (X_CHOOSE_THEN ([[m:num]]) SUBST_ALL_TAC)) THENL
     [DISCH_THEN (MP_TAC o HolLight.SPEC ([[m:num]])) THEN
      REWRITE_TAC [MULT_EQ_0, ARITH, h1] THEN
      ASM_CASES_TAC ([[m = 0]]) THEN ASM_REWRITE_TAC [] THEN
      ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC ([[s:num]]) THEN DISCH_THEN (X_CHOOSE_TAC ([[r:num]])) THEN
      EXISTS_TAC ([[SUC r]]) THEN ASM_REWRITE_TAC [EXP, (← HolLight.GSYM MULT_ASSOC)],
      REPEAT (DISCH_THEN ((fun _ => ALL_TAC))) THEN EXISTS_TAC ([[0]]) THEN
      REWRITE_TAC [EXP, MULT_CLAUSES] THEN MESON_TAC []])
  : ExceptT String IO thm).run
#eval EVEN_ODD_DECOMP

#eval phrase 7
def FINITE_DIVISORS : thm := keep "FINITE_DIVISORS" fun _ => (do
  prove ([[!n. ~(n = 0) ==> FINITE {d | d divides n}]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC ([[{d | d <= n}]]) THEN REWRITE_TAC [FINITE_NUMSEG_LE] THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [DIVIDES_LE])
  : ExceptT String IO thm).run
#eval FINITE_DIVISORS

#eval phrase 8
def MULT_EQ_COPRIME : thm := keep "MULT_EQ_COPRIME" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[(a * x * u = x * a * v) <=> (a * x) * u = (a * x) * v]])
  prove ([[!a b x y. a * b = x * y /\ coprime(a,x)
             ==> ?d. y = a * d /\ b = x * d]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [([[a:num]]), ([[x:num]]), ([[y:num]])] COPRIME_DIVPROD) THEN
    MP_TAC (← HolLight.SPECL [([[x:num]]), ([[a:num]]), ([[b:num]])] COPRIME_DIVPROD) THEN
    REPEAT (ANTS_TAC THENL
     [ASM_MESON_TAC [DIVIDES_REFL, DIVIDES_RMUL, COPRIME_SYM],
      REWRITE_TAC [divides] THEN STRIP_TAC]) THEN
    UNDISCH_TAC ([[a * b = x * y]]) THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [h1] THEN
    REWRITE_TAC [EQ_MULT_LCANCEL, MULT_EQ_0] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval MULT_EQ_COPRIME

#eval phrase 9
def COPRIME_ODD_POW2 : thm := keep "COPRIME_ODD_POW2" fun _ => (do
  prove ([[!k n. ODD(n) ==> coprime(2 EXP k,n)]])
   (SIMP_TAC [coprime, PRIME_2, DIVIDES_PRIMEPOW] THEN REWRITE_TAC [divides] THEN
    REPEAT STRIP_TAC THEN UNDISCH_TAC ([[ODD n]]) THEN ASM_REWRITE_TAC [] THEN
    SIMP_TAC [ODD_MULT, ODD_EXP, ARITH])
  : ExceptT String IO thm).run
#eval COPRIME_ODD_POW2

#eval phrase 10
def MULT_NSUM : thm := keep "MULT_NSUM" fun _ => (do
  prove ([[!s t. FINITE s /\ FINITE t
         ==> nsum s f * nsum t g =
             nsum {(x:A,y:B) | x IN s /\ y IN t} (\(x,y). f(x) * g(y))]])
   (SIMP_TAC [(← HolLight.GSYM NSUM_NSUM_PRODUCT), NSUM_LMUL, NSUM_RMUL])
  : ExceptT String IO thm).run
#eval MULT_NSUM

/- ------------------------------------------------------------------------- -/
/- Some elementary properties of the sigma function.                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 11
def SIGMA_0 : thm := keep "SIGMA_0" fun _ => (do
  prove ([[sigma 0 = 0]])
   (REWRITE_TAC [sigma])
  : ExceptT String IO thm).run
#eval SIGMA_0

#eval phrase 12
def SIGMA_1 : thm := keep "SIGMA_1" fun _ => (do
  let h1 ← sr (← ExceptT.mk [[{d | d = 1} = {1}]])
  prove ([[sigma(1) = 1]])
   (REWRITE_TAC [sigma, DIVIDES_ONE, h1] THEN
    REWRITE_TAC [ARITH, NSUM_SING])
  : ExceptT String IO thm).run
#eval SIGMA_1

#eval phrase 13
def SIGMA_LBOUND : thm := keep "SIGMA_LBOUND" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[1 < n ==> ~(n = 0)]])
  prove ([[!n. 1 < n ==> n + 1 <= sigma(n)]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP h1) THEN
    ASM_REWRITE_TAC [sigma] THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC ([[nsum {1,n} (\i. i)]]) THEN CONJ_TAC THENL
     [SIMP_TAC [NSUM_CLAUSES, FINITE_RULES, IN_SING, NOT_IN_EMPTY] THEN
      ASM_ARITH_TAC,
      MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN ASM_SIMP_TAC [FINITE_DIVISORS] THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM, NOT_IN_EMPTY, IN_INSERT] THEN
      MESON_TAC [DIVIDES_1, DIVIDES_REFL]])
  : ExceptT String IO thm).run
#eval SIGMA_LBOUND

#eval phrase 14
def SIGMA_MULT : thm := keep "SIGMA_MULT" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[x = a * b <=> a * b = 1 * x]])
  let h1 ← ar (← ExceptT.mk [[1 < n ==> ~(n = 0)]])
  prove ([[!a b. 1 < a /\ 1 < b ==> 1 + b + a * b <= sigma(a * b)]])
   (REPEAT STRIP_TAC THEN
    EVERY_ASSUM (ASSUME_TAC o HolLight.MATCH_MP h1) THEN
    ASM_REWRITE_TAC [sigma] THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC ([[nsum {1,b,a*b} (\i. i)]]) THEN CONJ_TAC THENL
     [SIMP_TAC [NSUM_CLAUSES, FINITE_RULES, IN_INSERT, NOT_IN_EMPTY] THEN
      ONCE_REWRITE_TAC [h2] THEN
      ASM_REWRITE_TAC [EQ_MULT_RCANCEL] THEN
      REWRITE_TAC [MULT_CLAUSES, MULT_EQ_1] THEN
      ASM_ARITH_TAC,
      ASM_REWRITE_TAC [MULT_EQ_0] THEN
      MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN
      ASM_SIMP_TAC [FINITE_DIVISORS, MULT_EQ_0] THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM, NOT_IN_EMPTY, IN_INSERT] THEN
      MESON_TAC [DIVIDES_1, DIVIDES_REFL, DIVIDES_LMUL]])
  : ExceptT String IO thm).run
#eval SIGMA_MULT

#eval phrase 15
def SIGMA_PRIME : thm := keep "SIGMA_PRIME" fun _ => (do
  prove ([[!p. prime(p) ==> sigma(p) = p + 1]])
   (GEN_TAC THEN
    ASM_CASES_TAC ([[p = 0]]) THEN ASM_REWRITE_TAC [PRIME_0, SIGMA_0, ARITH] THEN
    ASM_CASES_TAC ([[p = 1]]) THEN ASM_REWRITE_TAC [PRIME_1, SIGMA_1, ARITH] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC [sigma] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC ([[nsum {1,p} (\i. i)]]) THEN
    CONJ_TAC THENL
     [AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY] THEN
      ASM_MESON_TAC [prime, DIVIDES_1, DIVIDES_REFL],
      ASM_SIMP_TAC [NSUM_CLAUSES, IN_SING, FINITE_RULES, NOT_IN_EMPTY] THEN
      ARITH_TAC])
  : ExceptT String IO thm).run
#eval SIGMA_PRIME

#eval phrase 16
def SIGMA_PRIME_EQ : thm := keep "SIGMA_PRIME_EQ" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[a = a * b <=> a * b = a * 1]])
  prove ([[!p. prime(p) <=> sigma(p) = p + 1]])
   (GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [SIGMA_PRIME] THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM CONTRAPOS_THM)] THEN
    REWRITE_TAC [prime, DE_MORGAN_THM] THEN
    ASM_CASES_TAC ([[p = 1]]) THEN ASM_REWRITE_TAC [SIGMA_1, ARITH] THEN
    REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, divides, DE_MORGAN_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[a:num]]) (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[b:num]]) SUBST_ALL_TAC) THEN
    MP_TAC (← HolLight.SPECL [([[a:num]]), ([[b:num]])] SIGMA_MULT) THEN
    ASM_CASES_TAC ([[a = 0]]) THEN ASM_REWRITE_TAC [MULT_CLAUSES, SIGMA_0, ARITH] THEN
    ASM_CASES_TAC ([[b = 0]]) THEN ASM_REWRITE_TAC [MULT_CLAUSES, SIGMA_0, ARITH] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [MULT_EQ_1] THEN
    ONCE_REWRITE_TAC [h1] THEN
    REWRITE_TAC [EQ_MULT_LCANCEL] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval SIGMA_PRIME_EQ

#eval phrase 17
def SIGMA_POW2 : thm := keep "SIGMA_POW2" fun _ => (do
  let h5 ← ar (← ExceptT.mk [[~(SUC k <= k)]])
  let h4 ← sr (← ExceptT.mk [[{2 EXP i | i <= k} = IMAGE (\i. 2 EXP i) {i | i <= k}]])
  let h3 ← sr (← ExceptT.mk [[{2 EXP i | i = SUC k \/ i <= k} =
    (2 EXP (SUC k)) INSERT {2 EXP i | i <= k}]])
  let h2 ← sr (← ExceptT.mk [[{2 EXP i | i = 0} = {2 EXP 0}]])
  let h1 ← ar (← ExceptT.mk [[x + 1 = y ==> x = y - 1]])
  prove ([[!k. sigma(2 EXP k) = 2 EXP (k + 1) - 1]])
   (GEN_TAC THEN REWRITE_TAC [sigma, EXP_EQ_0, ARITH] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[nsum {2 EXP i | i <= k} (\i. i)]]) THEN CONJ_TAC THENL
     [AP_THM_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC [DIVIDES_PRIMEPOW, PRIME_2, EXTENSION, IN_ELIM_THM],
      ALL_TAC] THEN
    MATCH_MP_TAC h1 THEN
    SPEC_TAC (([[k:num]]), ([[k:num]])) THEN INDUCT_TAC THEN REWRITE_TAC [LE] THENL
     [REWRITE_TAC [h2] THEN
      REWRITE_TAC [ARITH, NSUM_SING],
      ALL_TAC] THEN
    REWRITE_TAC [h3] THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [h4] THEN
    SIMP_TAC [NSUM_CLAUSES, FINITE_IMAGE, FINITE_NUMSEG_LE] THEN
    REWRITE_TAC [IN_IMAGE, (← HolLight.GSYM LE_ANTISYM), LE_EXP, ARITH] THEN
    REWRITE_TAC [LE_ANTISYM, IN_ELIM_THM, UNWIND_THM1] THEN
    REWRITE_TAC [h5] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC [(← HolLight.GSYM ADD_ASSOC)] THEN
    REWRITE_TAC [EXP, EXP_ADD, ARITH] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval SIGMA_POW2

/- ------------------------------------------------------------------------- -/
/- Multiplicativity of sigma, the most interesting property.                 -/
/- ------------------------------------------------------------------------- -/

#eval phrase 18
def SIGMA_MULTIPLICATIVE : thm := keep "SIGMA_MULTIPLICATIVE" fun _ => (do
  let h1 ← tt (← ExceptT.mk [[(a /\ b) /\ c <=> c /\ a /\ b]])
  prove ([[!a b. coprime(a,b) ==> sigma(a * b) = sigma(a) * sigma(b)]])
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC ([[a = 0]]) THEN ASM_REWRITE_TAC [SIGMA_0, MULT_CLAUSES] THEN
    ASM_CASES_TAC ([[b = 0]]) THEN ASM_REWRITE_TAC [SIGMA_0, MULT_CLAUSES] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC [sigma, MULT_EQ_0] THEN
    ASM_SIMP_TAC [FINITE_DIVISORS, MULT_NSUM] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[nsum (IMAGE (\(x,y). x * y)
         {x,y | x divides a /\ y divides b}) (\i. i)]]) THEN
    CONJ_TAC THENL
     [AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM, EXISTS_PAIR_THM] THEN
      REWRITE_TAC [PAIR_EQ] THEN
      ONCE_REWRITE_TAC [h1] THEN
      REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC), RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
      X_GEN_TAC ([[n:num]]) THEN EQ_TAC THEN REWRITE_TAC [DIVISION_DECOMP] THEN
      REWRITE_TAC [divides] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      MESON_TAC [MULT_AC],
      ALL_TAC] THEN
    HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) NSUM_IMAGE (← ec (HolCore.Equal.lhand w))))) THEN
    REWRITE_TAC [o_DEF, ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [([[w:num]]), ([[x:num]]), ([[y:num]]), ([[z:num]])] THEN
    REWRITE_TAC [PAIR_EQ] THEN STRIP_TAC THEN
    REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o HolLight.SYM o
      check (HolCore.Kernel.is_var o HolCore.Kernel.rand o concl))) THEN
    REWRITE_TAC [(← HolLight.GSYM DIVIDES_ANTISYM)] THEN
    ASM_MESON_TAC [COPRIME_DIVISORS, COPRIME_SYM, COPRIME_DIVPROD,
                  DIVIDES_RMUL, DIVIDES_REFL, MULT_SYM])
  : ExceptT String IO thm).run
#eval SIGMA_MULTIPLICATIVE

/- ------------------------------------------------------------------------- -/
/- Hence the main theorems.                                                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 19
def PERFECT_EUCLID : thm := keep "PERFECT_EUCLID" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[~(k = 0) ==> k - 1 + 1 = k]])
  prove ([[!k. prime(2 EXP k - 1) ==> perfect(2 EXP (k - 1) * (2 EXP k - 1))]])
   (GEN_TAC THEN ASM_CASES_TAC ([[k = 0]]) THEN ASM_REWRITE_TAC [ARITH, PRIME_0] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN ([[coprime(2 EXP (k - 1),2 EXP k - 1)]]) ASSUME_TAC THENL
     [MATCH_MP_TAC COPRIME_ODD_POW2 THEN ASM_SIMP_TAC [ODD_POW2_MINUS1],
      ALL_TAC] THEN
    ASM_SIMP_TAC [perfect, SIGMA_MULTIPLICATIVE, SIGMA_PRIME, SIGMA_POW2] THEN
    ASM_SIMP_TAC [h1, EXP_EQ_0,
                 MULT_EQ_0, ARITH] THEN
    CONJ_TAC THENL [ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN
    REWRITE_TAC [MULT_ASSOC] THEN GEN_REWRITE_TAC HolLight.RAND_CONV [MULT_SYM] THEN
    AP_TERM_TAC THEN REWRITE_TAC [(← HolLight.GSYM (← HolLight.CONJUNCT2 EXP))] THEN
    AP_TERM_TAC THEN UNDISCH_TAC ([[~(k = 0)]]) THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval PERFECT_EUCLID

#eval phrase 20
def PERFECT_EULER : thm := keep "PERFECT_EULER" fun _ => (do
  let h5 ← ar (← ExceptT.mk [[2 EXP 0 < a ==> 1 < a]])
  let h4 ← ar (← ExceptT.mk [[1 * d < x * d ==> x * d < 1 + d + x * d - d]])
  let h3 ← ar (← ExceptT.mk [[2 EXP 1 < a ==> 1 < a - 1]])
  let h2 ← tt (← ExceptT.mk [[a /\ ~b ==> (a ==> b) ==> c]])
  let h1 ← ar (← ExceptT.mk [[1 <= n <=> ~(n = 0)]])
  prove ([[!n. EVEN(n) /\ perfect(n)
       ==> ?k. prime(2 EXP k - 1) /\ n = 2 EXP (k - 1) * (2 EXP k - 1)]])
   (GEN_TAC THEN MP_TAC (← HolLight.SPEC ([[n:num]]) EVEN_ODD_DECOMP) THEN
    ASM_CASES_TAC ([[n = 0]]) THENL
     [ASM_REWRITE_TAC [perfect], ASM_REWRITE_TAC []] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM, (← HolLight.GSYM NOT_EVEN)] THEN
    MAP_EVERY X_GEN_TAC [([[r:num]]), ([[s:num]])] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC [EVEN_EXP, EVEN_MULT, ARITH] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [perfect] THEN
    ASM_SIMP_TAC [SIGMA_MULTIPLICATIVE, SIGMA_POW2,
                 COPRIME_ODD_POW2, (← HolLight.GSYM NOT_EVEN)] THEN
    DISCH_TAC THEN EXISTS_TAC ([[r + 1]]) THEN
    REWRITE_TAC [ADD_SUB, EQ_MULT_LCANCEL] THEN REWRITE_TAC [EXP_EQ_0, ARITH] THEN
    FIRST_X_ASSUM (MP_TAC o check (is_eq o concl)) THEN
    REWRITE_TAC [MULT_ASSOC, (← HolLight.GSYM (← HolLight.CONJUNCT2 EXP)), ADD1] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ] MULT_EQ_COPRIME)) THEN
    ANTS_TAC THENL
     [ONCE_REWRITE_TAC [COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_ODD_POW2 THEN
      SIMP_TAC [ODD_POW2_MINUS1, ADD_EQ_0, ARITH_EQ],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d:num]]) MP_TAC) THEN
    ASM_CASES_TAC ([[d = 0]]) THEN ASM_REWRITE_TAC [MULT_CLAUSES] THENL
     [ASM_MESON_TAC [EVEN], ALL_TAC] THEN
    ASM_CASES_TAC ([[d = 1]]) THENL
     [ASM_REWRITE_TAC [MULT_CLAUSES, SIGMA_PRIME_EQ] THEN
      DISCH_THEN (CONJUNCTS_THEN2 (ASSUME_TAC o HolLight.SYM) ASSUME_TAC) THEN
      ASM_REWRITE_TAC [] THEN EXPAND_TAC "s" THEN
      MATCH_MP_TAC (← HolLight.GSYM SUB_ADD) THEN
      REWRITE_TAC [h1, EXP_EQ_0, ARITH],
      ALL_TAC] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (ASSUME_TAC o HolLight.SYM) ASSUME_TAC) THEN
    MP_TAC (← HolLight.SPECL [([[2 EXP (r + 1) - 1]]), ([[d:num]])] SIGMA_MULT) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC h2 THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC h3 THEN
      REWRITE_TAC [LT_EXP, ARITH] THEN
      UNDISCH_TAC ([[~(r = 0)]]) THEN ARITH_TAC,
      MAP_EVERY UNDISCH_TAC [([[~(d = 0)]]), ([[~(d = 1)]])] THEN ARITH_TAC,
      REWRITE_TAC [NOT_LE] THEN EXPAND_TAC "s" THEN
      REWRITE_TAC [RIGHT_SUB_DISTRIB, MULT_CLAUSES] THEN
      MATCH_MP_TAC h4 THEN
      ASM_REWRITE_TAC [LT_MULT_RCANCEL] THEN
      MATCH_MP_TAC h5 THEN
      REWRITE_TAC [LT_EXP] THEN UNDISCH_TAC ([[~(r = 0)]]) THEN ARITH_TAC])
  : ExceptT String IO thm).run
#eval PERFECT_EULER

end Hol100.Perfect
