/- File: Hol100/RealsUncountable.lean
Translation of HOL Light's 100/realsuncountable.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Card
import SessionLibrary.Analysis
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Analysis SessionLibrary.Wo SessionLibrary.Card
namespace Hol100.RealsUncountable

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def ms (ths : List thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (MESON ths tm)
private def rf (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_FIELD tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)

/- ========================================================================= -/
/- #22: non-denumerability of continuum (= uncountability of the reals).     -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/card.ml";;
#eval SessionLibrary.Card.ensureCard

#eval phrase 2
#eval Session.prioritize_real

/- ------------------------------------------------------------------------- -/
/- Definition of countability.                                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def countable : thm := keep "countable" fun _ => new_definition
 [[countable s <=> s <=_c (UNIV:num->bool)]]
#eval countable

/- ------------------------------------------------------------------------- -/
/- Set of repeating digits and its countability.                             -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def repeating : thm := keep "repeating" fun _ => new_definition
 [[repeating = {s:num->bool | ?n. !m. m >= n ==> s m}]]
#eval repeating

#eval phrase 5
def BINARY_BOUND : thm := keep "BINARY_BOUND" fun _ => (do
  prove ([[!n. nsum(0..n) (\i. if b(i) then 2 EXP i else 0) < 2 EXP (n + 1)]])
   (INDUCT_TAC THEN REWRITE_TAC [NSUM_CLAUSES_NUMSEG] THENL
     [COND_CASES_TAC THEN REWRITE_TAC [ARITH], ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [LE_0, EXP_ADD, EXP_1, EXP] THEN
    ARITH_TAC)
  : ExceptT String IO thm).run
#eval BINARY_BOUND

#eval phrase 6
def BINARY_DIV_POW2 : thm := keep "BINARY_DIV_POW2" fun _ => (do
  prove ([[!n. (nsum(0..n) (\i. if b(i) then 2 EXP i else 0)) DIV (2 EXP (SUC n)) = 0]])
   (SIMP_TAC [ADD1, DIV_LT, BINARY_BOUND])
  : ExceptT String IO thm).run
#eval BINARY_DIV_POW2

#eval phrase 7
def PLUS_MOD_REFL : thm := keep "PLUS_MOD_REFL" fun _ => (do
  prove ([[!a b. ~(b = 0) ==> (a + b) MOD b = a MOD b]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_EQ THEN MESON_TAC [MULT_CLAUSES])
  : ExceptT String IO thm).run
#eval PLUS_MOD_REFL

#eval phrase 8
def BINARY_PLUS_DIV_POW2 : thm := keep "BINARY_PLUS_DIV_POW2" fun _ => (do
  prove ([[!n. (nsum(0..n) (\i. if b(i) then 2 EXP i else 0) + 2 EXP (SUC n))
       DIV (2 EXP (SUC n)) = 1]])
   (GEN_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
    EXISTS_TAC ([[nsum(0..n) (\i. if b(i) then 2 EXP i else 0)]]) THEN
    ASM_REWRITE_TAC [BINARY_BOUND, ADD1] THEN
    REWRITE_TAC [ADD_AC, MULT_CLAUSES])
  : ExceptT String IO thm).run
#eval BINARY_PLUS_DIV_POW2

#eval phrase 9
def BINARY_UNIQUE_LEMMA : thm := keep "BINARY_UNIQUE_LEMMA" fun _ => (do
  prove ([[!n. nsum(0..n) (\i. if b(i) then 2 EXP i else 0) =
       nsum(0..n) (\i. if c(i) then 2 EXP i else 0)
       ==> !i. i <= n ==> (b(i) <=> c(i))]])
   (INDUCT_TAC THEN REWRITE_TAC [NSUM_CLAUSES_NUMSEG] THENL
     [SIMP_TAC [LE] THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [ARITH]),
      REWRITE_TAC [LE_0]] THEN
    REWRITE_TAC [LE] THEN REPEAT STRIP_TAC THENL
     [UNDISCH_THEN ([[i = SUC n]]) SUBST_ALL_TAC THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.AP_TERM ([[\x. x DIV (2 EXP (SUC n))]])) THEN
      REPEAT COND_CASES_TAC THEN
      ASM_REWRITE_TAC [ADD_CLAUSES, BINARY_DIV_POW2, BINARY_PLUS_DIV_POW2] THEN
      REWRITE_TAC [ARITH_EQ],
      FIRST_X_ASSUM (MP_TAC o HolLight.AP_TERM ([[\x. x MOD (2 EXP (SUC n))]])) THEN
      REPEAT COND_CASES_TAC THEN
      SIMP_TAC [ADD_CLAUSES, BINARY_BOUND, MOD_LT, PLUS_MOD_REFL, EXP_EQ_0, ARITH,
               ADD1] THEN
      ASM_MESON_TAC [LE_REFL]])
  : ExceptT String IO thm).run
#eval BINARY_UNIQUE_LEMMA

#eval phrase 10
def COUNTABLE_REPEATING : thm := keep "COUNTABLE_REPEATING" fun _ => (do
  prove ([[countable repeating]])
   (REWRITE_TAC [countable] THEN
    TRANS_TAC CARD_LE_TRANS ([[(UNIV:num->bool) *_c (UNIV:num->bool)]]) THEN
    CONJ_TAC THENL
      [ALL_TAC,
       MATCH_MP_TAC CARD_EQ_IMP_LE THEN REWRITE_TAC [CARD_SQUARE_NUM]] THEN
    REWRITE_TAC [le_c] THEN EXISTS_TAC ([[\s:num->bool. let n = minimal n. !m. m >= n ==> s m in
                  n,nsum(0..n) (\i. if s(i) then 2 EXP i else 0)]]) THEN
    REWRITE_TAC [repeating, IN_ELIM_THM] THEN CONJ_TAC THENL
     [GEN_TAC THEN LET_TAC THEN REWRITE_TAC [mul_c, IN_ELIM_THM, IN_UNIV] THEN
      MESON_TAC [],
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [([[s:num->bool]]), ([[t:num->bool]])] THEN
    ONCE_REWRITE_TAC [MINIMAL] THEN
    ABBREV_TAC ([[k = minimal n. !m. m >= n ==> s m]]) THEN
    ABBREV_TAC ([[l = minimal n. !m. m >= n ==> t m]]) THEN
    ASM_REWRITE_TAC [LET_DEF, LET_END_DEF, PAIR_EQ] THEN
    REPEAT (POP_ASSUM ((fun _ => ALL_TAC))) THEN
    ASM_CASES_TAC ([[l:num = k]]) THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC [FUN_EQ_THM, GE] THEN
    STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP BINARY_UNIQUE_LEMMA) THEN
    ASM_MESON_TAC [LE_CASES])
  : ExceptT String IO thm).run
#eval COUNTABLE_REPEATING

/- ------------------------------------------------------------------------- -/
/- Canonical digits and their uncountability.                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 11
def canonical : thm := keep "canonical" fun _ => new_definition
 [[canonical = {s:num->bool | !n. ?m. m >= n /\ ~(s m)}]]
#eval canonical

#eval phrase 12
def UNCOUNTABLE_CANONICAL : thm := keep "UNCOUNTABLE_CANONICAL" fun _ => (do
  prove ([[~countable canonical]])
   (REWRITE_TAC [countable] THEN STRIP_TAC THEN
    MP_TAC (← HolLight.INST_TYPE [((← ExceptT.mk (HolCore.Parser.parse_type "num")), (← ExceptT.mk (HolCore.Parser.parse_type "A")))] CANTOR_THM_UNIV) THEN
    REWRITE_TAC [CARD_NOT_LT] THEN
    MP_TAC (← HolLight.ISPECL [([[canonical]]), ([[repeating]])] CARD_DISJOINT_UNION) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_INTER, NOT_IN_EMPTY, IN_ELIM_THM,
                  canonical, repeating, GE] THEN
      MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[canonical UNION repeating = UNIV]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_UNION, IN_ELIM_THM,
                  canonical, repeating, GE, IN_UNIV] THEN
      MESON_TAC [],
      ALL_TAC] THEN
    DISCH_TAC THEN TRANS_TAC CARD_LE_TRANS ([[canonical +_c repeating]]) THEN
    ASM_SIMP_TAC [CARD_EQ_IMP_LE] THEN
    TRANS_TAC CARD_LE_TRANS ([[(UNIV:num->bool) +_c (UNIV:num->bool)]]) THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC [countable, COUNTABLE_REPEATING, CARD_LE_ADD],
      MATCH_MP_TAC CARD_ADD_ABSORB_LE THEN
      REWRITE_TAC [num_INFINITE, CARD_LE_REFL]])
  : ExceptT String IO thm).run
#eval UNCOUNTABLE_CANONICAL

/- ------------------------------------------------------------------------- -/
/- Injection of canonical digits into the reals.                             -/
/- ------------------------------------------------------------------------- -/

#eval phrase 13
-- needs "Library/analysis.ml";;
#eval SessionLibrary.Analysis.ensureAnalysis

#eval phrase 14
#eval Session.prioritize_real

#eval phrase 15
def SUM_BINSEQUENCE_LBOUND : thm := keep "SUM_BINSEQUENCE_LBOUND" fun _ => (do
  prove ([[!m n. &0 <= sum(m,n) (\i. if s(i) then inv(&2 pow i) else &0)]])
   (MATCH_MP_TAC SUM_POS THEN GEN_TAC THEN REWRITE_TAC [] THEN
    COND_CASES_TAC THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_LE_REFL, REAL_LE_INV_EQ] THEN
    SIMP_TAC [REAL_POW_LE, SessionLibrary.Analysis.REAL_POS])
  : ExceptT String IO thm).run
#eval SUM_BINSEQUENCE_LBOUND

#eval phrase 16
def SUM_BINSEQUENCE_UBOUND_SHARP : thm := keep "SUM_BINSEQUENCE_UBOUND_SHARP" fun _ => (do
  let h2 ← rr (← ExceptT.mk [[x <= a ==> a + y <= b ==> x + y <= b]])
  let h1 ← rr (← ExceptT.mk [[&0 <= y /\ x + y <= a ==> x + (if b then y else &0) <= a]])
  prove ([[!s m n. sum(m,n) (\i. if s(i) then inv(&2 pow i) else &0)
             <= &2 / &2 pow m - &2 / &2 pow (m + n)]])
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [SessionLibrary.Analysis.sum] THEN
    REWRITE_TAC [ADD_CLAUSES, SessionLibrary.Analysis.REAL_SUB_REFL, SessionLibrary.Analysis.REAL_LE_REFL] THEN
    MATCH_MP_TAC h1 THEN
    SIMP_TAC [REAL_LE_INV_EQ, REAL_POW_LE, SessionLibrary.Analysis.REAL_POS] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h2) THEN
    REWRITE_TAC [real_pow, real_div, REAL_INV_MUL] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval SUM_BINSEQUENCE_UBOUND_SHARP

#eval phrase 17
def SUMMABLE_BINSEQUENCE : thm := keep "SUMMABLE_BINSEQUENCE" fun _ => (do
  let h3 ← rr (← ExceptT.mk [[&0 <= x ==> a + x >= a]])
  let h2 ← rr (← ExceptT.mk [[a - x < a <=> &0 < x]])
  let h1 ← rr (← ExceptT.mk [[&0 <= x /\ a < b ==> x <= a ==> abs x < b]])
  prove ([[!s. summable (\i. if s(i) then inv(&2 pow i) else &0)]])
   (GEN_TAC THEN REWRITE_TAC [summable, sums, (← HolLight.GSYM convergent)] THEN
    MATCH_MP_TAC SEQ_ICONV THEN REWRITE_TAC [MR1_BOUNDED] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [([[&2]]), ([[0]])] THEN
      REWRITE_TAC [GE, LE_0, LE_REFL] THEN X_GEN_TAC ([[n:num]]) THEN
      MP_TAC (← HolLight.SPECL [([[s:num->bool]]), ([[0]]), ([[n:num]])] SUM_BINSEQUENCE_UBOUND_SHARP) THEN
      MATCH_MP_TAC h1 THEN
      REWRITE_TAC [SUM_BINSEQUENCE_LBOUND, real_pow, REAL_DIV_1, ADD_CLAUSES] THEN
      REWRITE_TAC [h2] THEN
      SIMP_TAC [REAL_LT_DIV, REAL_POW_LT, REAL_OF_NUM_LT, ARITH],
      GEN_TAC THEN X_GEN_TAC ([[n:num]]) THEN REWRITE_TAC [GE, LE_EXISTS] THEN
      DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN REWRITE_TAC [(← HolLight.GSYM SUM_SPLIT)] THEN
      MATCH_MP_TAC h3 THEN
      REWRITE_TAC [SUM_BINSEQUENCE_LBOUND]])
  : ExceptT String IO thm).run
#eval SUMMABLE_BINSEQUENCE

#eval phrase 18
def SUMS_BINSEQUENCE : thm := keep "SUMS_BINSEQUENCE" fun _ => (do
  prove ([[!s. (\i. if s(i) then inv(&2 pow i) else &0) sums
       (suminf (\i. if s(i) then inv(&2 pow i) else &0))]])
   (SIMP_TAC [SUMMABLE_SUM, SUMMABLE_BINSEQUENCE])
  : ExceptT String IO thm).run
#eval SUMS_BINSEQUENCE

#eval phrase 19
def SUM_BINSEQUENCE_UBOUND_LE : thm := keep "SUM_BINSEQUENCE_UBOUND_LE" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[&0 <= b ==> x <= a - b ==> x <= a]])
  prove ([[!s m n. sum(m,n) (\i. if s(i) then inv(&2 pow i) else &0) <= &2 / &2 pow m]])
   (MP_TAC SUM_BINSEQUENCE_UBOUND_SHARP THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    MATCH_MP_TAC h1 THEN
    SIMP_TAC [REAL_LE_DIV, REAL_POW_LE, SessionLibrary.Analysis.REAL_POS])
  : ExceptT String IO thm).run
#eval SUM_BINSEQUENCE_UBOUND_LE

/- ------------------------------------------------------------------------- -/
/- The main injection and hence main theorem.                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 20
def SUMINF_INJ_LEMMA : thm := keep "SUMINF_INJ_LEMMA" fun _ => (do
  let h4 ← rf (← ExceptT.mk [[&0 < inv(x) ==> inv(x) < &2 / x]])
  let h3 ← rr (← ExceptT.mk [[a = b /\ d < c ==> a - c < b - d]])
  let h2 ← rr (← ExceptT.mk [[a = b /\ c < e - d ==> (a + c) + d < b + e]])
  let h1 ← ar (← ExceptT.mk [[p = 0 \/ p = 1 + PRE p]])
  prove ([[!s t n. ~(s n) /\ t n /\
           (!m. m < n ==> (s(m) <=> t(m))) /\
           (!n. ?m. m >= n /\ ~(s m))
           ==> suminf(\n. if s n then inv (&2 pow n) else &0)
                < suminf(\n. if t n then inv (&2 pow n) else &0)]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SessionLibrary.Analysis.REAL_LTE_TRANS THEN
    EXISTS_TAC ([[sum(0,n+1) (\n. if t n then inv (&2 pow n) else &0)]]) THEN
    CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC SEQ_LE THEN MAP_EVERY EXISTS_TAC [([[\k:num. sum(0,n+1) (\n. if t n then inv (&2 pow n) else &0)]]),
        ([[\n:num. sum(0,n) (\n. if t n then inv (&2 pow n) else &0)]])] THEN
      REWRITE_TAC [SEQ_CONST, (← HolLight.GSYM sums), SUMS_BINSEQUENCE] THEN
      EXISTS_TAC ([[n + 1]]) THEN X_GEN_TAC ([[m:num]]) THEN
      REWRITE_TAC [GE, LE_EXISTS] THEN DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN
      REWRITE_TAC [(← HolLight.GSYM ADD1)] THEN
      REWRITE_TAC [(← HolLight.GSYM SUM_SPLIT), REAL_LE_ADDR, SUM_BINSEQUENCE_LBOUND]] THEN
    ASM_REWRITE_TAC [(← HolLight.GSYM SUM_SPLIT), SUM_1, ADD_CLAUSES] THEN
    UNDISCH_THEN ([[!n:num. ?m. m >= n /\ ~s m]]) (MP_TAC o HolLight.SPEC ([[n + 1]])) THEN
    REWRITE_TAC [GE] THEN DISCH_THEN (X_CHOOSE_THEN ([[m:num]]) STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC ([[sum(0,m) (\n. if s n then inv (&2 pow n) else &0) + inv(&2 pow m)]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SEQ_LE THEN MAP_EVERY EXISTS_TAC [([[\n:num. sum(0,n) (\n. if s n then inv (&2 pow n) else &0)]]),
        ([[\k:num. sum(0,m) (\n. if s n then inv(&2 pow n) else &0) +
               inv(&2 pow m)]])] THEN
      REWRITE_TAC [SEQ_CONST, (← HolLight.GSYM sums), SUMS_BINSEQUENCE] THEN
      EXISTS_TAC ([[m:num]]) THEN REWRITE_TAC [GE, LE_REFL] THEN
      X_GEN_TAC ([[r:num]]) THEN REWRITE_TAC [LE_EXISTS] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[p:num]]) SUBST_ALL_TAC) THEN
      REWRITE_TAC [(← HolLight.GSYM SUM_SPLIT), SessionLibrary.Analysis.REAL_LE_LADD, ADD_CLAUSES] THEN
      DISJ_CASES_THEN SUBST_ALL_TAC h1 THEN
      SIMP_TAC [SessionLibrary.Analysis.sum, REAL_LE_INV_EQ, REAL_POW_LE, SessionLibrary.Analysis.REAL_POS] THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM SUM_SPLIT)] THEN
      ASM_REWRITE_TAC [SUM_1, REAL_ADD_LID] THEN
      MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN EXISTS_TAC ([[&2 / &2 pow (m + 1)]]) THEN
      REWRITE_TAC [SUM_BINSEQUENCE_UBOUND_LE] THEN
      REWRITE_TAC [REAL_POW_ADD, REAL_POW_1] THEN CONV_TAC REAL_FIELD,
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [LE_EXISTS]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[r:num]]) SUBST_ALL_TAC) THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_SPLIT)] THEN
    ASM_REWRITE_TAC [ADD_CLAUSES, SUM_1, REAL_ADD_RID] THEN
    MATCH_MP_TAC h2 THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SessionLibrary.Analysis.SUM_EQ THEN ASM_SIMP_TAC [LE_0, ADD_CLAUSES], ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC ([[&2 / &2 pow (n + 1) - &2 / &2 pow ((n + 1) + r)]]) THEN
    REWRITE_TAC [SUM_BINSEQUENCE_UBOUND_SHARP] THEN
    MATCH_MP_TAC h3 THEN
    CONJ_TAC THENL
     [REWRITE_TAC [REAL_POW_ADD, REAL_POW_1] THEN CONV_TAC REAL_FIELD,
      MATCH_MP_TAC h4 THEN
      SIMP_TAC [REAL_LT_INV_EQ, REAL_POW_LT, REAL_OF_NUM_LT, ARITH]])
  : ExceptT String IO thm).run
#eval SUMINF_INJ_LEMMA

#eval phrase 21
def UNCOUNTABLE_REALS : thm := keep "UNCOUNTABLE_REALS" fun _ => (do
  let h3 ← rr (← ExceptT.mk [[a < b ==> a = b ==> F]])
  let h2 ← rr (← ExceptT.mk [[b < a ==> a = b ==> F]])
  let h1 ← ms [] (← ExceptT.mk [[(!x. P x) <=> ~(?x. ~P x)]])
  prove ([[~countable(UNIV:real->bool)]])
   (MP_TAC UNCOUNTABLE_CANONICAL THEN REWRITE_TAC [CONTRAPOS_THM] THEN
    REWRITE_TAC [countable] THEN DISCH_TAC THEN
    TRANS_TAC CARD_LE_TRANS ([[UNIV:real->bool]]) THEN
    ASM_REWRITE_TAC [] THEN POP_ASSUM ((fun _ => ALL_TAC)) THEN REWRITE_TAC [le_c] THEN
    EXISTS_TAC ([[\s. suminf(\n. if s(n) then inv(&2 pow n) else &0)]]) THEN
    REWRITE_TAC [IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [([[s:num->bool]]), ([[t:num->bool]])] THEN
    REWRITE_TAC [canonical, IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC [FUN_EQ_THM] THEN
    GEN_REWRITE_TAC HolCore.Lib.I [h1] THEN
    ONCE_REWRITE_TAC [MINIMAL] THEN
    ABBREV_TAC ([[n = minimal x. ~(s x <=> t x)]]) THEN
    FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o check (HolCore.Kernel.is_var o HolCore.Equal.rhs o concl)) THEN
    ASM_CASES_TAC ([[(t:num->bool) n]]) THEN ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o HolLight.SYM) THENL
     [MATCH_MP_TAC h2,
      MATCH_MP_TAC h3] THEN
    MATCH_MP_TAC SUMINF_INJ_LEMMA THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval UNCOUNTABLE_REALS

end Hol100.RealsUncountable
