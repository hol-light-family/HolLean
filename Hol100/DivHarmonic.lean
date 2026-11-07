/- File: Hol100/DivHarmonic.lean
Translation of HOL Light's 100/divharmonic.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Transc
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionLibrary.Analysis (convergent SEQ)
open SessionLibrary.Transc
namespace Hol100.DivHarmonic

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)

/- ========================================================================= -/
/- Divergence of harmonic series.                                            -/
/- ========================================================================= -/

#eval phrase 1
#eval Session.prioritize_real

#eval phrase 2
def HARMONIC_DIVERGES : thm := keep "HARMONIC_DIVERGES" fun _ => (do
  let h4 ← ar (← ExceptT.mk [[(2 * x + 1) - (x + 1) = x]])
  let h3 ← rr (← ExceptT.mk [[&1 / &2 <= y
    ==> abs((x + y) - s) < &1 / &4 ==> ~(abs(x - s) < &1 / &4)]])
  let h2 ← ar (← ExceptT.mk [[1 <= (N + 1) + 1]])
  prove ([[~(?s. !e. &0 < e
             ==> ?N. !n. N <= n ==> abs(sum(1..n) (\i. &1 / &i) - s) < e)]])
   (STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[&1 / &4]])) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPEC ([[N + 1]])) THEN REWRITE_TAC [LE_ADD] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[(N + 1) + (N + 1)]])) THEN
    ANTS_TAC THENL [ARITH_TAC, ALL_TAC] THEN
    SIMP_TAC [SUM_ADD_SPLIT, h2] THEN
    MATCH_MP_TAC h3 THEN
    REWRITE_TAC [(← HolLight.GSYM MULT_2)] THEN MATCH_MP_TAC Session.REAL_LE_TRANS THEN
    EXISTS_TAC ([[sum((N + 1) + 1 .. 2 * (N + 1)) (\i. &1 / &(2 * (N + 1)))]]) THEN
    CONJ_TAC THENL
     [SIMP_TAC [SUM_CONST_NUMSEG, h4] THEN
      REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_MUL), (← HolLight.GSYM REAL_OF_NUM_ADD)] THEN
      MP_TAC (← HolLight.SPEC ([[n:num]]) Session.REAL_POS) THEN CONV_TAC REAL_FIELD,
      MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC [real_div, REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN
      REWRITE_TAC [REAL_OF_NUM_LE, REAL_OF_NUM_LT] THEN ARITH_TAC])
  : ExceptT String IO thm).run
#eval HARMONIC_DIVERGES

/- ------------------------------------------------------------------------- -/
/- Formulation in terms of limits.                                           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
-- needs "Library/analysis.ml";;
#eval SessionLibrary.Analysis.ensureAnalysis

#eval phrase 4
def HARMONIC_DIVERGES' : thm := keep "HARMONIC_DIVERGES'" fun _ => (do
  prove ([[~(convergent (\n. sum(1..n) (\i. &1 / &i)))]])
   (REWRITE_TAC [convergent, SEQ, GE, HARMONIC_DIVERGES])
  : ExceptT String IO thm).run
#eval HARMONIC_DIVERGES'

/- ------------------------------------------------------------------------- -/
/- Lower bound on the partial sums.                                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
def HARMONIC_LEMMA : thm := keep "HARMONIC_LEMMA" fun _ => (do
  let h3 ← ar (← ExceptT.mk [[(2 * x + 1) - (x + 1) = x]])
  let h2 ← ar (← ExceptT.mk [[a <= x ==> b - a <= y ==> b <= x + y]])
  let h1 ← ar (← ExceptT.mk [[1 <= 2 EXP m + 1]])
  prove ([[!m. sum(1..2 EXP m) (\n. &1 / &n) >= &m / &2]])
   (REWRITE_TAC [real_ge] THEN INDUCT_TAC THEN
    REWRITE_TAC [EXP, MULT_2, SUM_SING_NUMSEG] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC [SUM_ADD_SPLIT, h1] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h2) THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_SUC), (← HolLight.GSYM (← HolLight.CONJUNCT2 EXP)),
                 (← HolLight.GSYM MULT_2)] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[sum(2 EXP m + 1..2 EXP (SUC m))(\n. &1 / &(2 EXP (SUC m)))]]) THEN
    CONJ_TAC THENL
     [SIMP_TAC [SUM_CONST_NUMSEG, EXP, h3] THEN
      REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
      MP_TAC (← HolLight.SPECL [([[2]]), ([[m:num]])] EXP_EQ_0) THEN
      REWRITE_TAC [ARITH] THEN REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_EQ)] THEN
      CONV_TAC REAL_FIELD,
      MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC [real_div, REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN
      REWRITE_TAC [REAL_OF_NUM_LE, REAL_OF_NUM_LT] THEN ARITH_TAC])
  : ExceptT String IO thm).run
#eval HARMONIC_LEMMA

/- ------------------------------------------------------------------------- -/
/- Germ of an alternative proof.                                             -/
/- ------------------------------------------------------------------------- -/

#eval phrase 6
-- needs "Library/transc.ml";;
#eval SessionLibrary.Transc.ensureTransc

#eval phrase 7
def LOG_BOUND : thm := keep "LOG_BOUND" fun _ => (do
  prove ([[&0 < x /\ x < &1 ==> ln(&1 + x) >= x / &2]])
   (REWRITE_TAC [real_ge] THEN REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM LN_EXP)] THEN
    ASM_SIMP_TAC [LN_MONO_LE, REAL_EXP_POS_LT, SessionLibrary.Analysis.REAL_LT_ADD, SessionLibrary.Analysis.REAL_LT_01] THEN
    MP_TAC (← HolLight.SPEC ([[x / &2]]) REAL_EXP_BOUND_LEMMA) THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval LOG_BOUND

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py; keep it in step with the `#eval`s above. -/
def ensure : IO Unit := once "Hol100.DivHarmonic" do
  replay (
          Session.prioritize_real)
  replay (
          HARMONIC_DIVERGES)
  replay (
          SessionLibrary.Analysis.ensureAnalysis)
  replay (
          HARMONIC_DIVERGES')
  replay (
          HARMONIC_LEMMA)
  replay (
          SessionLibrary.Transc.ensureTransc)
  replay (
          LOG_BOUND)
-- @@ENSURE END

end Hol100.DivHarmonic
