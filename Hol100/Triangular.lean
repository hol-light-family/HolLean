/- File: Hol100/Triangular.lean
Translation of HOL Light's 100/triangular.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionMultiLib.Misc
import SessionLibrary.Analysis
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionMultiLib.Misc
open SessionLibrary.Analysis (SEQ)
namespace Hol100.Triangular

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)

/- ========================================================================= -/
/- Sum of reciprocals of triangular numbers.                                 -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Multivariate/misc.ml";;  (*** Just for REAL_ARCH_INV! ***)
#eval SessionMultiLib.Misc.ensureMisc

#eval phrase 2
#eval Session.prioritize_real

/- ------------------------------------------------------------------------- -/
/- Definition of triangular numbers.                                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def triangle : thm := keep "triangle" fun _ => new_definition
 [[triangle n = (n * (n + 1)) DIV 2]]
#eval triangle

/- ------------------------------------------------------------------------- -/
/- Mapping them into the reals: division is exact.                           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def REAL_TRIANGLE : thm := keep "REAL_TRIANGLE" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[&2 * x = y ==> x = y / &2]])
  prove ([[&(triangle n) = (&n * (&n + &1)) / &2]])
   (MATCH_MP_TAC h1 THEN
    REWRITE_TAC [triangle, REAL_OF_NUM_MUL, REAL_OF_NUM_ADD, REAL_OF_NUM_EQ] THEN
    SUBGOAL_THEN ([[EVEN(n * (n + 1))]]) MP_TAC THENL
     [REWRITE_TAC [EVEN_MULT, EVEN_ADD, ARITH] THEN CONV_TAC TAUT,
      REWRITE_TAC [EVEN_EXISTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC DIV_MULT THEN REWRITE_TAC [ARITH]])
  : ExceptT String IO thm).run
#eval REAL_TRIANGLE

/- ------------------------------------------------------------------------- -/
/- Sum of a finite number of terms.                                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
def TRIANGLE_FINITE_SUM : thm := keep "TRIANGLE_FINITE_SUM" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[1 <= SUC n]])
  prove ([[!n. sum(1..n) (\k. &1 / &(triangle k)) = &2 - &2 / (&n + &1)]])
   (INDUCT_TAC THEN
    ASM_REWRITE_TAC [SUM_CLAUSES_NUMSEG, ARITH_EQ, h1] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [REAL_TRIANGLE, (← HolLight.GSYM REAL_OF_NUM_SUC)] THEN CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval TRIANGLE_FINITE_SUM

/- ------------------------------------------------------------------------- -/
/- Hence limit.                                                              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 6
def TRIANGLE_CONVERGES : thm := keep "TRIANGLE_CONVERGES" fun _ => (do
  let h2 ← rr (← ExceptT.mk [[abs(&n + &1) = &n + &1]])
  let h1 ← rr (← ExceptT.mk [[abs(x - y - x) = abs y]])
  prove ([[!e. &0 < e
       ==> ?N. !n. n >= N
                   ==> abs(sum(1..n) (\k. &1 / &(triangle k)) - &2) < e]])
   (GEN_TAC THEN GEN_REWRITE_TAC HolLight.LAND_CONV [REAL_ARCH_INV] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[N:num]]) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC ([[2 * N + 1]]) THEN REWRITE_TAC [GE] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [TRIANGLE_FINITE_SUM, h1] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC ([[inv(&N)]]) THEN
    ASM_SIMP_TAC [REAL_ABS_DIV, REAL_ABS_NUM] THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_INV_DIV)] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    SIMP_TAC [REAL_LE_RDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN
    REWRITE_TAC [h2] THEN
    REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_MUL, REAL_OF_NUM_LE] THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval TRIANGLE_CONVERGES

/- ------------------------------------------------------------------------- -/
/- In terms of limits.                                                       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 7
-- needs "Library/analysis.ml";;
#eval SessionLibrary.Analysis.ensureAnalysis

#eval phrase 8
-- override_interface ("-->",`(tends_num_real)`);;
#eval (do discard <| override_interface "-->" [[(tends_num_real)]] : IO Unit)

#eval phrase 9
def TRIANGLE_CONVERGES' : thm := keep "TRIANGLE_CONVERGES'" fun _ => (do
  prove ([[(\n. sum(1..n) (\k. &1 / &(triangle k))) --> &2]])
   (REWRITE_TAC [SEQ, TRIANGLE_CONVERGES])
  : ExceptT String IO thm).run
#eval TRIANGLE_CONVERGES'

end Hol100.Triangular
