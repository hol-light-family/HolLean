/- File: Hol100/ArithmeticGeometricMean.lean
Translation of HOL Light's 100/arithmetic_geometric_mean.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Products
import SessionLibrary.Transc
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionLibrary.Products SessionLibrary.Transc
namespace Hol100.ArithmeticGeometricMean

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)

/- ========================================================================= -/
/- Arithmetic-geometric mean inequality.                                     -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/products.ml";;
#eval SessionLibrary.Products.ensureProducts

#eval phrase 2
#eval Session.prioritize_real

/- ------------------------------------------------------------------------- -/
/- There's already one proof of this in "Library/agm.ml". This one is from  -/
/- an article by Michael Hirschhorn, Math. Intelligencer vol. 29, p7.        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def LEMMA_1 : thm := keep "LEMMA_1" fun _ => (do
  let h3 ← rr (← ExceptT.mk [[k * x * x pow n = (k * x pow n) * x]])
  let h2 ← ar (← ExceptT.mk [[k <= n ==> SUC n - k = SUC(n - k)]])
  let h1 ← ar (← ExceptT.mk [[1 <= SUC n]])
  prove ([[!x n. x pow (n + 1) - (&n + &1) * x + &n =
         (x - &1) pow 2 * sum(1..n) (\k. &k * x pow (n - k))]])
   (CONV_TAC (HolLight.ONCE_DEPTH_CONV HolLight.SYM_CONV) THEN GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [SUM_CLAUSES_NUMSEG, ARITH_EQ, ADD_CLAUSES] THENL
     [REAL_ARITH_TAC2, REWRITE_TAC [h1]] THEN
    SIMP_TAC [h2, SUB_REFL] THEN
    REWRITE_TAC [real_pow, REAL_MUL_RID] THEN
    REWRITE_TAC [h3] THEN
    ASM_REWRITE_TAC [SUM_RMUL, REAL_MUL_ASSOC, REAL_ADD_LDISTRIB] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_SUC), REAL_POW_ADD] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval LEMMA_1

#eval phrase 4
def LEMMA_2 : thm := keep "LEMMA_2" fun _ => (do
  prove ([[!n x. &0 <= x ==> &0 <= x pow (n + 1) - (&n + &1) * x + &n]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [LEMMA_1] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [REAL_POW_2, REAL_LE_SQUARE] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    ASM_SIMP_TAC [REAL_LE_MUL, REAL_POS, REAL_POW_LE])
  : ExceptT String IO thm).run
#eval LEMMA_2

#eval phrase 5
def LEMMA_3 : thm := keep "LEMMA_3" fun _ => (do
  let h4 ← rr (← ExceptT.mk [[&0 <= x - a + b <=> a - b <= x]])
  let h3 ← ar (← ExceptT.mk [[p <= n ==> p <= n + 1]])
  let h2 ← ar (← ExceptT.mk [[1 <= n + 1]])
  let h1 ← rr (← ExceptT.mk [[~(&n + &1 = &0)]])
  prove ([[!n x. 1 <= n /\ (!i. 1 <= i /\ i <= n + 1 ==> &0 <= x i)
         ==> x(n + 1) * (sum(1..n) x / &n) pow n
                <= (sum(1..n+1) x / (&n + &1)) pow (n + 1)]])
   (REPEAT STRIP_TAC THEN
    ABBREV_TAC ([[a = sum(1..n+1) x / (&n + &1)]]) THEN
    ABBREV_TAC ([[b = sum(1..n) x / &n]]) THEN
    SUBGOAL_THEN ([[x(n + 1) = (&n + &1) * a - &n * b]]) SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a", "b"] THEN
      ASM_SIMP_TAC [REAL_DIV_LMUL, REAL_OF_NUM_EQ, LE_1, h1] THEN
      SIMP_TAC [SUM_ADD_SPLIT, h2, SUM_SING_NUMSEG] THEN
      REAL_ARITH_TAC2,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[&0 <= a /\ &0 <= b]]) STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a", "b"] THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_DIV THEN
      (CONJ_TAC THENL [MATCH_MP_TAC SUM_POS_LE_NUMSEG, REAL_ARITH_TAC2]) THEN
      ASM_SIMP_TAC [h3],
      ALL_TAC] THEN
    ASM_CASES_TAC ([[b = &0]]) THEN
    ASM_SIMP_TAC [REAL_POW_ZERO, LE_1, REAL_MUL_RZERO, REAL_POW_LE] THEN
    MP_TAC (← HolLight.ISPECL [([[n:num]]), ([[a / b]])] LEMMA_2) THEN ASM_SIMP_TAC [REAL_LE_DIV] THEN
    REWRITE_TAC [h4, REAL_POW_DIV] THEN
    SUBGOAL_THEN ([[&0 < b]]) ASSUME_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_POW_LT] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [REAL_POW_ADD] THEN UNDISCH_TAC ([[~(b = &0)]]) THEN
    CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval LEMMA_3

#eval phrase 6
def AGM : thm := keep "AGM" fun _ => (do
  let h3 ← ar (← ExceptT.mk [[i <= n ==> i <= n + 1]])
  let h2 ← ar (← ExceptT.mk [[i <= n ==> i <= n + 1]])
  let h1 ← ar (← ExceptT.mk [[1 <= SUC n]])
  prove ([[!n a. 1 <= n /\ (!i. 1 <= i /\ i <= n ==> &0 <= a(i))
         ==> product(1..n) a <= (sum(1..n) a / &n) pow n]])
   (INDUCT_TAC THEN REWRITE_TAC [ARITH, PRODUCT_CLAUSES_NUMSEG] THEN
    REWRITE_TAC [h1] THEN X_GEN_TAC ([[x:num->real]]) THEN
    ASM_CASES_TAC ([[n = 0]]) THENL
     [ASM_REWRITE_TAC [PRODUCT_CLAUSES_NUMSEG, ARITH, SUM_SING_NUMSEG] THEN
      REAL_ARITH_TAC2,
      REWRITE_TAC [ADD1] THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC ([[x(n + 1) * (sum(1..n) x / &n) pow n]]) THEN
      ASM_SIMP_TAC [LEMMA_3, (← HolLight.GSYM REAL_OF_NUM_ADD), LE_1, h2] THEN
      GEN_REWRITE_TAC HolLight.RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC [LE_REFL, LE_1, h3]])
  : ExceptT String IO thm).run
#eval AGM

/- ------------------------------------------------------------------------- -/
/- Finally, reformulate in the usual way using roots.                        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 7
-- needs "Library/transc.ml";;
#eval SessionLibrary.Transc.ensureTransc

#eval phrase 8
def AGM_ROOT : thm := keep "AGM_ROOT" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[1 <= SUC n]])
  let h1 ← ar (← ExceptT.mk [[1 <= SUC n]])
  prove ([[!n a. 1 <= n /\ (!i. 1 <= i /\ i <= n ==> &0 <= a(i))
         ==> root n (product(1..n) a) <= sum(1..n) a / &n]])
   (INDUCT_TAC THEN REWRITE_TAC [ARITH, h1] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[root(SUC n) ((sum(1..SUC n) a / &(SUC n)) pow (SUC n))]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ROOT_MONO_LE THEN
      ASM_SIMP_TAC [AGM, h2] THEN
      MATCH_MP_TAC PRODUCT_POS_LE THEN
      ASM_REWRITE_TAC [IN_NUMSEG, FINITE_NUMSEG],
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC POW_ROOT_POS THEN
      ASM_SIMP_TAC [REAL_LE_DIV, SessionLibrary.Analysis.REAL_POS, SUM_POS_LE_NUMSEG]])
  : ExceptT String IO thm).run
#eval AGM_ROOT

end Hol100.ArithmeticGeometricMean
