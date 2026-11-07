/- File: Hol100/PrimeRecip.lean
Translation of HOL Light's 100/primerecip.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import Hol100.Bertrand
import Hol100.DivHarmonic
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Prime SessionLibrary.Analysis SessionLibrary.Floor SessionLibrary.Iter SessionLibrary.Transc SessionLibrary.Pocklington SessionLibrary.CalcReal Hol100.DivHarmonic Hol100.Bertrand
namespace Hol100.PrimeRecip

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def nc (tm : term) : ExceptT String IO thm := ExceptT.mk (num_CONV tm)
private def rf (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_FIELD tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def rrc (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_RAT_REDUCE_CONV tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- Divergence of prime reciprocal series.                                    -/
/- ========================================================================= -/
/- ------------------------------------------------------------------------- -/
/- Now load other stuff needed.                                              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 1
-- needs "100/bertrand.ml";;
#eval Hol100.Bertrand.ensure

#eval phrase 2
-- needs "100/divharmonic.ml";;
#eval Hol100.DivHarmonic.ensure

/- ------------------------------------------------------------------------- -/
/- Variant of induction.                                                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def INDUCTION_FROM_1 : thm := keep "INDUCTION_FROM_1" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[n = 0 \/ 1 <= n]])
  let h1 ← nc (← ExceptT.mk [[1]])
  prove ([[!P. P 0 /\ P 1 /\ (!n. 1 <= n /\ P n ==> P(SUC n)) ==> !n. P n]])
   (GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [h1, h2])
  : ExceptT String IO thm).run
#eval INDUCTION_FROM_1

/- ------------------------------------------------------------------------- -/
/- Evaluate sums over explicit intervals.                                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
-- let SUM_CONV = ...;;
def SUM_CONV_pth : thm := keep "SUM_CONV_pth" fun _ => (do
  let h1 ← ExceptT.mk (ARITH_RULE (← ExceptT.mk [[1 <= SUC n]]))
  prove ([[sum(1..1) f = f 1 /\ sum(1..SUC n) f = sum(1..n) f + f(SUC n)]])
   (SIMP_TAC [SUM_CLAUSES_NUMSEG, LE_0, h1, SUM_SING_NUMSEG])
  : ExceptT String IO thm).run
partial def SUM_CONV (tm : term) : IO (Except String thm) := (do
  let econv_0 := HolLight.GEN_REWRITE_CONV HolCore.Lib.I [← HolLight.CONJUNCT1 SUM_CONV_pth]
  let econv_1 := HolLight.GEN_REWRITE_CONV HolCore.Lib.I [← HolLight.CONJUNCT2 SUM_CONV_pth]
  ExceptT.mk ((econv_0 ORELSEC
     (HolLight.LAND_CONV (HolLight.RAND_CONV num_CONV) THENC econv_1 THENC
      HolLight.COMB2_CONV (HolLight.RAND_CONV SUM_CONV) (HolLight.RAND_CONV NUM_SUC_CONV))) tm)
  : ExceptT String IO thm).run
#eval (do replay SUM_CONV_pth; IO.println "<fun>" : IO Unit)

/- ------------------------------------------------------------------------- -/
/- Lower bound relative to harmonic series.                                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
def PRIMERECIP_HARMONIC_LBOUND : thm := keep "PRIMERECIP_HARMONIC_LBOUND" fun _ => (do
  let h12 ← rr (← ExceptT.mk [[&6 * &1 * n1 <= &16 * n1 - &5 * n <=> n <= inv(inv(&2)) * n1]])
  let h11 ← rf (← ExceptT.mk [[(&3 / (&16 * l) * i) * &32 * n32 = (n32 / l) * (&6 * i)]])
  let h10 ← rf (← ExceptT.mk [[&1 / &2 * (&32 * n32) / (n1 * l) - &5 * n32 / (n * l) =
    (n32 / l) * (&16 / n1 - &5 / n)]])
  let h9 ← rr (← ExceptT.mk [[a <= x ==> b <= a ==> b <= x]])
  let h8 ← ar (← ExceptT.mk [[~(0 < i) <=> i = 0]])
  let h7 ← ar (← ExceptT.mk [[n + 31 * n = 32 * n]])
  let h6 ← ar (← ExceptT.mk [[1 <= n + 1]])
  let h5 ← ar (← ExceptT.mk [[32 * n = n + 31 * n]])
  let h4 ← rr (← ExceptT.mk [[a <= s1 /\ s2 <= b ==> a - b <= s1 - s2]])
  let h3 ← ar (← ExceptT.mk [[1 <= SUC n]])
  let h2 ← rr (← ExceptT.mk [[b - a <= s2 - s1 ==> a <= s1 ==> b <= s2]])
  let h1 ← rrc (← ExceptT.mk [[&2 pow 5]])
  prove ([[!n. (&3 / (&16 * ln(&32))) * sum(1..n) (\i. &1 / &i) <=
       sum(1..32 EXP n) (\i. if prime(i) then &1 / &i else &0)]])
   (MATCH_MP_TAC INDUCTION_FROM_1 THEN CONJ_TAC THENL
     [SIMP_TAC [SUM_TRIV_NUMSEG, ARITH, SUM_SING_NUMSEG, SessionLibrary.Analysis.REAL_MUL_RZERO] THEN
      REWRITE_TAC [PRIME_1, SessionLibrary.Analysis.REAL_LE_REFL],
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [ARITH, SUM_SING_NUMSEG] THEN
      CONV_TAC (HolLight.RAND_CONV SUM_CONV) THEN REWRITE_TAC [] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV PRIME_CONV) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [(← HolLight.SYM h1)] THEN
      SIMP_TAC [LN_POW, REAL_OF_NUM_LT, ARITH, real_div, REAL_INV_MUL] THEN
      REWRITE_TAC [REAL_MUL_ASSOC, SessionLibrary.Analysis.REAL_MUL_RID] THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      SIMP_TAC [(← HolLight.GSYM REAL_LE_RDIV_EQ), REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM REAL_INV_DIV)] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [LN_2_COMPOSITION, real_div, real_sub] THEN
      CONV_TAC REALCALC_REL_CONV,
      ALL_TAC] THEN
    X_GEN_TAC ([[n:num]]) THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC h2 THEN
    REWRITE_TAC [(← HolLight.GSYM SessionLibrary.Analysis.REAL_SUB_LDISTRIB)] THEN
    REWRITE_TAC [SUM_CLAUSES_NUMSEG, REAL_ADD_SUB, h3] THEN
    MP_TAC (← HolLight.SPEC ([[32 EXP n]]) PII_UBOUND_5) THEN ANTS_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC ([[32 EXP 1]]) THEN
      ASM_REWRITE_TAC [LE_EXP] THEN REWRITE_TAC [ARITH],
      ALL_TAC] THEN
    MP_TAC (← HolLight.SPEC ([[32 EXP (SUC n)]]) PII_LBOUND) THEN ANTS_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC ([[32 EXP 1]]) THEN
      ASM_REWRITE_TAC [LE_EXP] THEN REWRITE_TAC [ARITH] THEN ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [IMP_IMP] THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP h4) THEN
    SIMP_TAC [pii, PSUM_SUM_NUMSEG, EXP_EQ_0, ARITH, ADD_SUB2] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_POW)] THEN
    REWRITE_TAC [EXP, h5] THEN
    SIMP_TAC [SUM_ADD_SPLIT, h6, REAL_ADD_SUB] THEN
    REWRITE_TAC [h7] THEN
    REWRITE_TAC [(← HolLight.GSYM (← HolLight.CONJUNCT2 EXP))] THEN STRIP_TAC THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[inv(&32 pow (SUC n)) *
    sum(32 EXP n + 1 .. 32 EXP SUC n) (\i. if prime i then &1 else &0)]]) THEN
    CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [(← HolLight.GSYM SUM_LMUL)] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      X_GEN_TAC ([[i:num]]) THEN STRIP_TAC THEN REWRITE_TAC [] THEN
      COND_CASES_TAC THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_LE_REFL, SessionLibrary.Analysis.REAL_MUL_RZERO] THEN
      REWRITE_TAC [real_div, REAL_MUL_LID, SessionLibrary.Analysis.REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_LE, REAL_OF_NUM_LT] THEN
      UNDISCH_TAC ([[32 EXP n + 1 <= i]]) THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM CONTRAPOS_THM)] THEN
      SIMP_TAC [h8] THEN
      REWRITE_TAC [LE, ARITH, ADD_EQ_0]] THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [REAL_MUL_SYM] THEN
    SIMP_TAC [(← HolLight.GSYM real_div), REAL_POW_LT, REAL_LE_RDIV_EQ,
             REAL_OF_NUM_LT, ARITH] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h9) THEN
    SIMP_TAC [LN_POW, REAL_POW_LT, REAL_OF_NUM_LT, ARITH] THEN
    REWRITE_TAC [real_pow, (← HolLight.GSYM REAL_OF_NUM_SUC)] THEN
    REWRITE_TAC [h10] THEN
    REWRITE_TAC [h11] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    SIMP_TAC [REAL_LE_DIV, REAL_POW_LE, LN_POS, REAL_OF_NUM_LE, ARITH] THEN
    REWRITE_TAC [real_div, h12] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_INV_MUL)] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_LE)] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval PRIMERECIP_HARMONIC_LBOUND

/- ------------------------------------------------------------------------- -/
/- Hence an overall lower bound.                                             -/
/- ------------------------------------------------------------------------- -/

#eval phrase 6
def PRIMERECIP_LBOUND : thm := keep "PRIMERECIP_LBOUND" fun _ => (do
  let h1 ← rf (← ExceptT.mk [[&3 / (&32 * ln(&32)) * &n = &3 / (&16 * ln(&32)) * (&n / &2)]])
  prove ([[!n. &3 / (&32 * ln(&32)) * &n
       <= sum (1 .. 32 EXP (2 EXP n)) (\i. if prime i then &1 / &i else &0)]])
   (GEN_TAC THEN MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[&3 / (&16 * ln(&32)) * sum (1 .. 2 EXP n) (\i. &1 / &i)]]) THEN
    REWRITE_TAC [PRIMERECIP_HARMONIC_LBOUND] THEN
    REWRITE_TAC [h1] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC [(← HolLight.REWRITE_RULE [real_ge] HARMONIC_LEMMA)] THEN
    SIMP_TAC [REAL_LE_DIV, SessionLibrary.Analysis.REAL_LE_MUL, LN_POS, REAL_OF_NUM_LE, ARITH])
  : ExceptT String IO thm).run
#eval PRIMERECIP_LBOUND

/- ------------------------------------------------------------------------- -/
/- General lemma.                                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 7
def UNBOUNDED_DIVERGENT : thm := keep "UNBOUNDED_DIVERGENT" fun _ => (do
  prove ([[!s. (!k. ?N. !n. n >= N ==> sum(1..n) s >= k)
       ==> ~(convergent(\n. sum(1..n) s))]])
   (REWRITE_TAC [convergent, SEQ] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[&1]])) THEN
    REWRITE_TAC [SessionLibrary.Analysis.REAL_LT_01] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[l + &1]])) THEN
    REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC ([[M:num]]) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[M + N:num]])) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[M + N:num]])) THEN
    REWRITE_TAC [LE_ADD, (← HolLight.ONCE_REWRITE_RULE [ADD_SYM] LE_ADD), GE] THEN
    REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval UNBOUNDED_DIVERGENT

/- ------------------------------------------------------------------------- -/
/- Hence divergence.                                                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 8
def PRIMERECIP_DIVERGES_NUMSEG : thm := keep "PRIMERECIP_DIVERGES_NUMSEG" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[1 <= n + 1]])
  prove ([[~(convergent (\n. sum (1..n) (\i. if prime i then &1 / &i else &0)))]])
   (MATCH_MP_TAC UNBOUNDED_DIVERGENT THEN X_GEN_TAC ([[k:real]]) THEN
    MP_TAC (← HolLight.SPEC ([[&3 / (&32 * ln(&32))]]) SessionLibrary.Analysis.REAL_ARCH) THEN
    SIMP_TAC [REAL_LT_DIV, LN_POS_LT, REAL_LT_MUL, REAL_OF_NUM_LT, ARITH] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[k:real]])) THEN DISCH_THEN (X_CHOOSE_TAC ([[N:num]])) THEN
    EXISTS_TAC ([[32 EXP (2 EXP N)]]) THEN
    X_GEN_TAC ([[n:num]]) THEN REWRITE_TAC [GE, real_ge] THEN STRIP_TAC THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[&N * &3 / (&32 * ln (&32))]]) THEN
    ASM_SIMP_TAC [SessionLibrary.Analysis.REAL_LT_IMP_LE] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN EXISTS_TAC ([[sum(1 .. 32 EXP (2 EXP N)) (\i. if prime i then &1 / &i else &0)]]) THEN
    REWRITE_TAC [PRIMERECIP_LBOUND] THEN
    FIRST_X_ASSUM (CHOOSE_THEN SUBST1_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [LE_EXISTS]) THEN
    SIMP_TAC [SUM_ADD_SPLIT, h1, REAL_LE_ADDR] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [] THEN COND_CASES_TAC THEN SIMP_TAC [REAL_LE_DIV, SessionLibrary.Analysis.REAL_POS])
  : ExceptT String IO thm).run
#eval PRIMERECIP_DIVERGES_NUMSEG

/- ------------------------------------------------------------------------- -/
/- A perhaps more intuitive formulation.                                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 9
def PRIMERECIP_DIVERGES : thm := keep "PRIMERECIP_DIVERGES" fun _ => (do
  let h4 ← ar (← ExceptT.mk [[~(SUC n <= n)]])
  let h3 ← ar (← ExceptT.mk [[1 <= i <=> ~(i = 0)]])
  let h2 ← ar (← ExceptT.mk [[1 <= SUC n]])
  let h1 ← tt (← ExceptT.mk [[(a <=> b) ==> ~a ==> ~b]])
  prove ([[~(convergent (\n. sum {p | prime p /\ p <= n} (\p. &1 / &p)))]])
   (MP_TAC PRIMERECIP_DIVERGES_NUMSEG THEN
    MATCH_MP_TAC h1 THEN
    AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC ([[n:num]]) THEN
    SPEC_TAC (([[n:num]]), ([[n:num]])) THEN INDUCT_TAC THENL
     [SUBGOAL_THEN ([[{p | prime p /\ p <= 0} = {}]]) (fun th => SIMP_TAC [SUM_CLAUSES, SUM_TRIV_NUMSEG, th, ARITH]) THEN
      REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY, LE] THEN
      MESON_TAC [PRIME_0],
      ALL_TAC] THEN
    ASM_SIMP_TAC [SUM_CLAUSES_NUMSEG, h2] THEN
    SUBGOAL_THEN ([[{p | prime p /\ p <= SUC n} =
        if prime(SUC n) then (SUC n) INSERT {p | prime p /\ p <= n}
        else {p | prime p /\ p <= n}]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT] THEN
      GEN_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT, LE] THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_ADD_RID] THEN
    SUBGOAL_THEN ([[FINITE {p | prime p /\ p <= n}]]) (fun th => SIMP_TAC [SUM_CLAUSES, th]) THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[1..n]]) THEN
      SIMP_TAC [FINITE_NUMSEG, IN_NUMSEG, IN_ELIM_THM, SUBSET] THEN
      MESON_TAC [PRIME_0, h3],
      REWRITE_TAC [IN_ELIM_THM, h4, REAL_ADD_AC]])
  : ExceptT String IO thm).run
#eval PRIMERECIP_DIVERGES

end Hol100.PrimeRecip
