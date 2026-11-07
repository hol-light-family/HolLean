/- File: Hol100/Stirling.lean
Translation of HOL Light's 100/stirling.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Analysis
import SessionLibrary.Transc
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Analysis SessionLibrary.Transc
namespace Hol100.Stirling

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
/-- Run an `IO (Except String α)` once, caching under `name` (OCaml's `let`
    evaluates its right-hand side once), for the `let X,Y,Z = e` bindings
    whose result is a tuple. -/
private def keepIO {α : Type} [Inhabited α] (name : String) (f : Unit → IO (Except String α)) : α :=
  keep name fun _ =>
    match runIO (f ()) with
    | .ok (.ok v) => v
    | .ok (.error e) => panic! s!"keepIO {name}: {e}"
    | .error e => panic! s!"keepIO {name}: {e}"
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def rf (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_FIELD tm)
private def rg (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_RING tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def rrc (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_RAT_REDUCE_CONV tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- Stirling's approximation.                                                 -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/analysis.ml";;
#eval SessionLibrary.Analysis.ensureAnalysis

#eval phrase 2
-- needs "Library/transc.ml";;
#eval SessionLibrary.Transc.ensureTransc

#eval phrase 3
-- override_interface("-->",`(tends_num_real)`);;
#eval (do discard <| override_interface "-->" [[(tends_num_real)]] : IO Unit)

/- ------------------------------------------------------------------------- -/
/- This is a handy induction for Wallis's product below.                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def ODDEVEN_INDUCT : thm := keep "ODDEVEN_INDUCT" fun _ => (do
  prove ([[!P. P 0 /\ P 1 /\ (!n. P n ==> P(n + 2)) ==> !n. P n]])
   (GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[!n. P n /\ P(n + 1)]]) (fun th => MESON_TAC [th]) THEN
    INDUCT_TAC THEN ASM_SIMP_TAC [ADD1, (← HolLight.GSYM ADD_ASSOC)] THEN
    ASM_SIMP_TAC [ARITH])
  : ExceptT String IO thm).run
#eval ODDEVEN_INDUCT

/- ------------------------------------------------------------------------- -/
/- A particular limit we need below.                                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
def LN_LIM_BOUND : thm := keep "LN_LIM_BOUND" fun _ => (do
  let h2 ← rr (← ExceptT.mk [[n * --((i * i) * a) = --((n * i) * a * i)]])
  let h1 ← rf (← ExceptT.mk [[~(x = &0) ==> x * (inv(x) + a) - &1 = x * a]])
  prove ([[!n. ~(n = 0) ==> abs(&n * ln(&1 + &1 / &n) - &1) <= &1 / (&2 * &n)]])
   (REPEAT STRIP_TAC THEN MP_TAC (← HolLight.SPECL [([[&1 / &n]]), ([[2]])] MCLAURIN_LN_POS) THEN
    ASM_SIMP_TAC [SUM_2, REAL_LT_DIV, REAL_OF_NUM_LT, LT_NZ, ARITH] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[t:real]]) STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [real_div, REAL_INV_0, SessionLibrary.Analysis.REAL_MUL_RZERO, REAL_ADD_LID] THEN
    REWRITE_TAC [REAL_POW_1, REAL_POW_2, REAL_MUL_LNEG, REAL_MUL_RNEG,
                SessionLibrary.Analysis.REAL_NEG_NEG, REAL_MUL_LID, REAL_INV_1, REAL_POW_NEG,
                REAL_POW_ONE, ARITH, SessionLibrary.Analysis.REAL_MUL_RID] THEN
    ASM_SIMP_TAC [REAL_OF_NUM_EQ, h1] THEN
    REWRITE_TAC [h2] THEN
    ASM_SIMP_TAC [SessionLibrary.Analysis.REAL_MUL_RINV, REAL_OF_NUM_EQ, ARITH, REAL_MUL_LID] THEN
    REWRITE_TAC [REAL_ABS_NEG, REAL_ABS_MUL] THEN
    ONCE_REWRITE_TAC [REAL_INV_MUL] THEN REWRITE_TAC [REAL_ABS_MUL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [(← HolLight.GSYM REAL_MUL_ASSOC)] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM REAL_MUL_LID)] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC [real_div, REAL_MUL_LID, REAL_LE_INV_EQ, SessionLibrary.Analysis.REAL_POS] THEN
    REWRITE_TAC [REAL_ABS_INV] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
    REWRITE_TAC [REAL_ABS_MUL] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM REAL_MUL_LID)] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_POS] THEN
    UNDISCH_TAC ([[&0 < t]]) THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval LN_LIM_BOUND

#eval phrase 6
def LN_LIM_LEMMA : thm := keep "LN_LIM_LEMMA" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[n >= 1 <=> ~(n = 0)]])
  let h1 ← rr (← ExceptT.mk [[a = (a - &1) + &1]])
  prove ([[(\n. &n * ln(&1 + &1 / &n)) --> &1]])
   (GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.BINDER_CONV) [h1] THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM REAL_ADD_LID)] THEN
    MATCH_MP_TAC SEQ_ADD THEN REWRITE_TAC [SEQ_CONST] THEN
    MATCH_MP_TAC SEQ_LE_0 THEN EXISTS_TAC ([[\n. &1 / &n]]) THEN
    REWRITE_TAC [SEQ_HARMONIC] THEN
    EXISTS_TAC ([[1]]) THEN REWRITE_TAC [h2] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[&1 / (&2 * &n)]]) THEN ASM_SIMP_TAC [LN_LIM_BOUND] THEN
    REWRITE_TAC [real_div, REAL_MUL_LID, REAL_ABS_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN UNDISCH_TAC ([[~(n = 0)]]) THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_EQ)] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval LN_LIM_LEMMA

/- ------------------------------------------------------------------------- -/
/- Lemma for proving inequality via derivative and limit at infinity.        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 7
def POSITIVE_DIFF_LEMMA : thm := keep "POSITIVE_DIFF_LEMMA" fun _ => (do
  let h4 ← rr (← ExceptT.mk [[y < &0 /\ z < y ==> abs(z) < --y ==> F]])
  let h3 ← rr (← ExceptT.mk [[&0 < --x <=> x < &0]])
  let h2 ← rr (← ExceptT.mk [[&0 < --x <=> x < &0]])
  let h1 ← rr (← ExceptT.mk [[&0 < z * --y ==> z * y + a < a]])
  prove ([[!f f'. (!x. &0 < x ==> (f diffl f'(x)) x /\ f'(x) < &0) /\
          (\n. f(&n)) --> &0
          ==> !n. ~(n = 0) ==> &0 < f(&n)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [(← HolLight.GSYM SessionLibrary.Analysis.REAL_NOT_LE)] THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[!m p. n <= m /\ m < p ==> (f:real->real)(&p) < f(&m)]]) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC (← HolLight.SPECL [([[f:real->real]]), ([[f':real->real]]), ([[&m]]), ([[&p]])] MVT_ALT) THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC [LT_NZ, LTE_TRANS, REAL_OF_NUM_LT, SessionLibrary.Analysis.REAL_LTE_TRANS],
        ALL_TAC] THEN
      REWRITE_TAC [REAL_EQ_SUB_RADD] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC h1 THEN
      MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_LT, REAL_OF_NUM_LT] THEN
      REWRITE_TAC [h2] THEN
      ASM_MESON_TAC [LT_NZ, LTE_TRANS, REAL_OF_NUM_LT, REAL_LT_TRANS],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[f(&(n + 1)) < &0]]) ASSUME_TAC THENL
     [FIRST_ASSUM (MP_TAC o HolLight.SPECL [([[n:num]]), ([[n + 1]])]) THEN ANTS_TAC THENL
       [ARITH_TAC, UNDISCH_TAC ([[f(&n) <= &0]]) THEN REAL_ARITH_TAC2],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [SEQ]) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[--f(&(n + 1))]])) THEN
    ASM_REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_RZERO, h3] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[p:num]]) (MP_TAC o HolLight.SPEC ([[n + p + 2]]))) THEN
    ANTS_TAC THENL [ARITH_TAC, ALL_TAC] THEN
    MATCH_MP_TAC h4 THEN
    ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval POSITIVE_DIFF_LEMMA

/- ------------------------------------------------------------------------- -/
/- Auxiliary definition.                                                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 8
def stirling : thm := keep "stirling" fun _ => new_definition
 [[stirling n = ln(&(FACT n)) - ((&n + &1 / &2) * ln(&n) - &n)]]
#eval stirling

/- ------------------------------------------------------------------------- -/
/- This difference is a decreasing sequence.                                 -/
/- ------------------------------------------------------------------------- -/

#eval phrase 9
def STIRLING_DIFF : thm := keep "STIRLING_DIFF" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[(f' - f) + x = (nl' - nl) /\ n' = n + &1
    ==> (f - (nl - n)) - (f' - (nl' - n')) = x - &1]])
  prove ([[!n. ~(n = 0)
       ==> stirling(n) - stirling(n + 1) =
           (&n + &1 / &2) * ln((&n + &1) / &n) - &1]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [stirling] THEN
    MATCH_MP_TAC h1 THEN
    REWRITE_TAC [REAL_OF_NUM_ADD] THEN
    REWRITE_TAC [(← HolLight.REWRITE_RULE [ADD1] FACT), (← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
    SIMP_TAC [LN_MUL, FACT_LT, ADD_EQ_0, ARITH, LT_NZ, REAL_OF_NUM_LT] THEN
    ASM_SIMP_TAC [LN_DIV, REAL_OF_NUM_LT, ADD_EQ_0, ARITH, LT_NZ] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_ADD)] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval STIRLING_DIFF

#eval phrase 10
def STIRLING_DELTA_DERIV : thm := keep "STIRLING_DELTA_DERIV" fun _ => (do
  prove ([[!x. &0 < x
       ==> ((\x. ln ((x + &1) / x) - &1 / (x + &1 / &2)) diffl
            (-- &1 / (x * (x + &1) * (&2 * x + &1) pow 2))) x]])
   (GEN_TAC THEN DISCH_TAC THEN
    HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC (← ec (HolCore.Kernel.rand w)) (DIFF_CONV (← ec (HolCore.Equal.lhand (← ec (HolCore.Kernel.rator w)))))))) THEN
    REWRITE_TAC [IMP_IMP] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY (MATCH_MP_TAC REAL_LT_DIV) THEN
      POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD,
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [REAL_POW_2] THEN
    POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval STIRLING_DELTA_DERIV

#eval phrase 11
def STIRLING_DELTA_LIMIT : thm := keep "STIRLING_DELTA_LIMIT" fun _ => (do
  let h3 ← rf (← ExceptT.mk [[&1 <= x ==> (x + &1) / x = &1 + &1 / x]])
  let h2 ← rr (← ExceptT.mk [[&1 <= x ==> &0 < x]])
  let h1 ← rr (← ExceptT.mk [[&0 <= x /\ x <= y ==> abs x <= abs y]])
  prove ([[(\n. ln ((&n + &1) / &n) - &1 / (&n + &1 / &2)) --> &0]])
   (GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM SessionLibrary.Analysis.REAL_SUB_RZERO)] THEN
    MATCH_MP_TAC SEQ_SUB THEN CONJ_TAC THEN MATCH_MP_TAC SEQ_LE_0 THEN
    EXISTS_TAC ([[\n. &1 / &n]]) THEN REWRITE_TAC [SEQ_HARMONIC] THEN
    EXISTS_TAC ([[1]]) THEN X_GEN_TAC ([[n:num]]) THEN
    REWRITE_TAC [GE, (← HolLight.GSYM REAL_OF_NUM_LE)] THEN
    DISCH_TAC THEN MATCH_MP_TAC h1 THEN CONJ_TAC THENL
     [MATCH_MP_TAC LN_POS THEN
      ASM_SIMP_TAC [REAL_LE_RDIV_EQ, h2] THEN
      REAL_ARITH_TAC2,
      ASM_SIMP_TAC [h3] THEN
      MATCH_MP_TAC LN_LE THEN ASM_SIMP_TAC [REAL_LE_DIV, SessionLibrary.Analysis.REAL_POS],
      MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC2,
      REWRITE_TAC [real_div, REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      POP_ASSUM MP_TAC THEN REAL_ARITH_TAC2])
  : ExceptT String IO thm).run
#eval STIRLING_DELTA_LIMIT

#eval phrase 12
def STIRLING_DECREASES : thm := keep "STIRLING_DECREASES" fun _ => (do
  let h2 ← rr (← ExceptT.mk [[--x < &0 <=> &0 < x]])
  let h1 ← rr (← ExceptT.mk [[&0 < &n + &1 / &2]])
  prove ([[!n. ~(n = 0) ==> stirling(n + 1) < stirling(n)]])
   (ONCE_REWRITE_TAC [(← HolLight.GSYM SessionLibrary.Analysis.REAL_SUB_LT)] THEN SIMP_TAC [STIRLING_DIFF] THEN
    REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_LT] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    SIMP_TAC [(← HolLight.GSYM REAL_LT_LDIV_EQ), h1] THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM SessionLibrary.Analysis.REAL_SUB_LT)] THEN
    MATCH_MP_TAC POSITIVE_DIFF_LEMMA THEN
    EXISTS_TAC ([[\x. -- &1 / (x * (x + &1) * (&2 * x + &1) pow 2)]]) THEN
    SIMP_TAC [STIRLING_DELTA_DERIV, STIRLING_DELTA_LIMIT] THEN
    X_GEN_TAC ([[x:real]]) THEN DISCH_TAC THEN
    REWRITE_TAC [real_div, REAL_MUL_LNEG, REAL_MUL_LID] THEN
    REWRITE_TAC [h2, REAL_LT_INV_EQ] THEN
    REWRITE_TAC [REAL_POW_2] THEN
    REPEAT (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval STIRLING_DECREASES

/- ------------------------------------------------------------------------- -/
/- However a slight tweak gives an *increasing* sequence.                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 13
def OTHER_DERIV_LEMMA : thm := keep "OTHER_DERIV_LEMMA" fun _ => (do
  prove ([[!x. &0 < x
       ==> ((\x. &1 / (&12 * x * (x + &1) * (x + &1 / &2))) diffl
            --(&3 * x pow 2 + &3 * x + &1 / &2) /
              (&12 * (x * (x + &1) * (x + &1 / &2)) pow 2)) x]])
   (REPEAT STRIP_TAC THEN
    HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC (← ec (HolCore.Kernel.rand w)) (DIFF_CONV (← ec (HolCore.Equal.lhand (← ec (HolCore.Kernel.rator w)))))))) THEN
    REWRITE_TAC [IMP_IMP] THEN ANTS_TAC THENL
     [REWRITE_TAC [REAL_ENTIRE] THEN POP_ASSUM MP_TAC THEN ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [REAL_POW_2] THEN
    POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval OTHER_DERIV_LEMMA

#eval phrase 14
def STIRLING_INCREASES : thm := keep "STIRLING_INCREASES" fun _ => (do
  let h11 ← rf (← ExceptT.mk [[&0 < x
    ==> &1 / (x * (x + &1) * (&2 * x + &1) pow 2) =
        (&3 * x * (x + &1)) /
        (&12 * (x * (x + &1) * (x + &1 / &2)) *
               (x * (x + &1) * (x + &1 / &2)))]])
  let h10 ← rr (← ExceptT.mk [[a - b < &0 <=> a < b]])
  let h9 ← rr (← ExceptT.mk [[&1 / x - y / z = --y / z - -- &1 / x]])
  let h8 ← rrc (← ExceptT.mk [[&0 * &0 * &0]])
  let h7 ← rf (← ExceptT.mk [[inv(&12) * x * y * inv(&n + inv(&2)) = x * y * inv(&12 * &n + &6)]])
  let h6 ← rr (← ExceptT.mk [[a < b + c <=> &0 < b - (a - c)]])
  let h5 ← rr (← ExceptT.mk [[(&1 / x + &1) / y = &1 / x / y + &1 / y]])
  let h4 ← rr (← ExceptT.mk [[&0 < &n + &1 / &2]])
  let h3 ← rr (← ExceptT.mk [[a * b - &1 < c <=> b * a < c + &1]])
  let h2 ← rf (← ExceptT.mk [[~(&n = &0) ==> &1 / (&12 * &n) - &1 / (&12 * (&n + &1)) =
                    &1 / (&12 * &n * (&n + &1))]])
  let h1 ← rr (← ExceptT.mk [[a - b > c - d <=> c - a < d - b]])
  prove ([[!n. ~(n = 0)
       ==> stirling(n + 1) - &1 / (&12 * (&(n + 1)))
           > stirling(n) - &1 / (&12 * &n)]])
   (REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_EQ), (← HolLight.GSYM REAL_OF_NUM_ADD)] THEN
    REWRITE_TAC [h1] THEN
    SIMP_TAC [h2] THEN
    SIMP_TAC [REAL_OF_NUM_EQ, STIRLING_DIFF] THEN
    REWRITE_TAC [h3] THEN
    SIMP_TAC [(← HolLight.GSYM REAL_LT_RDIV_EQ), h4] THEN
    REWRITE_TAC [h5] THEN
    REWRITE_TAC [h6] THEN
    REWRITE_TAC [real_div, (← HolLight.GSYM REAL_MUL_ASSOC), (← HolLight.GSYM REAL_INV_MUL)] THEN
    REWRITE_TAC [(← HolLight.GSYM real_div)] THEN MATCH_MP_TAC POSITIVE_DIFF_LEMMA THEN
    EXISTS_TAC ([[\x. &1 / (x * (x + &1) * (&2 * x + &1) pow 2) -
                  (&3 * x pow 2 + &3 * x + &1 / &2) /
                  (&12 * (x * (x + &1) * (x + &1 / &2)) pow 2)]]) THEN
    REWRITE_TAC [] THEN CONJ_TAC THENL
     [ALL_TAC,
      GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM SessionLibrary.Analysis.REAL_SUB_RZERO)] THEN
      MATCH_MP_TAC SEQ_SUB THEN REWRITE_TAC [STIRLING_DELTA_LIMIT] THEN
      REWRITE_TAC [real_div, REAL_INV_MUL, REAL_MUL_LID] THEN
      REWRITE_TAC [h7] THEN
      GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.SYM h8)] THEN
      REPEAT (MATCH_MP_TAC SEQ_MUL THEN CONJ_TAC) THEN
      MP_TAC (← HolLight.SPEC ([[&1]]) SEQ_HARMONIC) THEN
      REWRITE_TAC [real_div, REAL_MUL_LID] THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP SEQ_SUBSEQ) THENL
       [DISCH_THEN (MP_TAC o HolLight.SPECL [([[1]]), ([[1]])]),
        DISCH_THEN (MP_TAC o HolLight.SPECL [([[12]]), ([[6]])])] THEN
      REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_MUL, ARITH, MULT_CLAUSES]] THEN
    X_GEN_TAC ([[x:real]]) THEN DISCH_TAC THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC HolLight.LAND_CONV [h9] THEN
      MATCH_MP_TAC DIFF_SUB THEN
      ASM_SIMP_TAC [STIRLING_DELTA_DERIV, OTHER_DERIV_LEMMA],
      ALL_TAC] THEN
    REWRITE_TAC [h10] THEN
    ASM_SIMP_TAC [(← HolLight.GSYM REAL_POW_2), h11] THEN
    ONCE_REWRITE_TAC [real_div] THEN MATCH_MP_TAC REAL_LT_RMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC2, ALL_TAC] THEN
    REWRITE_TAC [REAL_LT_INV_EQ, REAL_POW_2] THEN
    REPEAT (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval STIRLING_INCREASES

/- ------------------------------------------------------------------------- -/
/- Hence it converges to *something*.                                        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 15
def STIRLING_UPPERBOUND : thm := keep "STIRLING_UPPERBOUND" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[SUC(SUC n) = SUC n + 1]])
  prove ([[!n. stirling(SUC n) <= &1]])
   (INDUCT_TAC THENL
     [REWRITE_TAC [stirling] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC [LN_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV,
      ALL_TAC] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[stirling(SUC n)]]) THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [h1] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LT_IMP_LE THEN MATCH_MP_TAC STIRLING_DECREASES THEN
    ARITH_TAC)
  : ExceptT String IO thm).run
#eval STIRLING_UPPERBOUND

#eval phrase 16
def STIRLING_LOWERBOUND : thm := keep "STIRLING_LOWERBOUND" fun _ => (do
  let h3 ← rr (← ExceptT.mk [[b > a ==> a <= b]])
  let h2 ← ar (← ExceptT.mk [[SUC(SUC n) = SUC n + 1]])
  let h1 ← rr (← ExceptT.mk [[a - b <= a <=> &0 <= b]])
  prove ([[!n. -- &1 <= stirling(SUC n)]])
   (GEN_TAC THEN MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[stirling(SUC n) - &1 / (&12 * &(SUC n))]]) THEN CONJ_TAC THENL
     [ALL_TAC,
      SIMP_TAC [h1] THEN
      REWRITE_TAC [real_div, REAL_MUL_LID, REAL_LE_INV_EQ] THEN
      REWRITE_TAC [REAL_OF_NUM_MUL, SessionLibrary.Analysis.REAL_POS]] THEN
    SPEC_TAC (([[n:num]]), ([[n:num]])) THEN INDUCT_TAC THENL
     [REWRITE_TAC [stirling] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC [LN_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV,
      ALL_TAC] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[stirling(SUC n) - &1 / (&12 * &(SUC n))]]) THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [h2] THEN
    MATCH_MP_TAC h3 THEN
    MATCH_MP_TAC STIRLING_INCREASES THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval STIRLING_LOWERBOUND

#eval phrase 17
def STIRLING_MONO : thm := keep "STIRLING_MONO" fun _ => (do
  prove ([[!m n. ~(m = 0) /\ m <= n ==> stirling n <= stirling m]])
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [LE_EXISTS]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d:num]]) SUBST1_TAC) THEN
    SPEC_TAC (([[d:num]]), ([[d:num]])) THEN INDUCT_TAC THEN
    REWRITE_TAC [ADD_CLAUSES, SessionLibrary.Analysis.REAL_LE_REFL] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN EXISTS_TAC ([[stirling(m + d)]]) THEN
    ASM_SIMP_TAC [ADD1, SessionLibrary.Analysis.REAL_LT_IMP_LE, STIRLING_DECREASES, ADD_EQ_0])
  : ExceptT String IO thm).run
#eval STIRLING_MONO

#eval phrase 18
def STIRLING_CONVERGES : thm := keep "STIRLING_CONVERGES" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[-- &1 <= x /\ x <= &1 ==> abs(x) < &2]])
  prove ([[?c. stirling --> c]])
   (ONCE_REWRITE_TAC [SEQ_SUC] THEN
    REWRITE_TAC [(← HolLight.GSYM convergent)] THEN MATCH_MP_TAC SEQ_BCONV THEN CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [mono, real_ge] THEN DISJ2_TAC THEN REPEAT GEN_TAC THEN
      DISCH_TAC THEN MATCH_MP_TAC STIRLING_MONO THEN
      POP_ASSUM MP_TAC THEN ARITH_TAC] THEN
    REWRITE_TAC [MR1_BOUNDED, GE, LE_REFL] THEN
    MAP_EVERY EXISTS_TAC [([[&2]]), ([[0]])] THEN REWRITE_TAC [LE_0] THEN
    SIMP_TAC [h1,
             STIRLING_UPPERBOUND, STIRLING_LOWERBOUND])
  : ExceptT String IO thm).run
#eval STIRLING_CONVERGES

/- ------------------------------------------------------------------------- -/
/- Now derive Wallis's infinite product.                                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 19
-- let PI2_LT, PI2_LE, PI2_NZ = (CONJUNCTS o prove) ...
def PI2_LT_PI2_LE_THMS : List thm := keepIO "PI2_LT_PI2_LE_THMS" fun _ => (do
  let th ← prove ([[&0 < pi / &2 /\ &0 <= pi / &2 /\ ~(pi / &2 = &0)]])
   (MP_TAC PI_POS THEN REAL_ARITH_TAC2)
  pure (HolLight.CONJUNCTS th)
  : ExceptT String IO (List thm)).run
def PI2_LT : thm := PI2_LT_PI2_LE_THMS[0]!
def PI2_LE : thm := PI2_LT_PI2_LE_THMS[1]!
def PI2_NZ : thm := PI2_LT_PI2_LE_THMS[2]!
#eval do IO.println (repr PI2_LT); IO.println (repr PI2_LE); IO.println (repr PI2_NZ)

#eval phrase 20
def WALLIS_PARTS : thm := keep "WALLIS_PARTS" fun _ => (do
  let h3 ← rg (← ExceptT.mk [[sin(x) pow 2 + cos(x) pow 2 = &1
     ==> (n * sn * cos(x)) * --cos(x) = (n * sn) * (sin(x) pow 2 - &1)]])
  let h2 ← ar (← ExceptT.mk [[SUC(n + 1) = n + 2]])
  let h1 ← rr (← ExceptT.mk [[s pow k * s = s * s pow k]])
  prove ([[!n. (&n + &2) * integral(&0,pi / &2) (\x. sin(x) pow (n + 2)) =
       (&n + &1) * integral(&0,pi / &2) (\x. sin(x) pow n)]])
   (GEN_TAC THEN
    MP_TAC (← HolLight.SPECL [([[\x. sin(x) pow (n + 1)]]), ([[\x. --cos(x)]]),
                  ([[\x. (&n + &1) * sin(x) pow n * cos(x)]]),
                  ([[\x. sin(x)]]), ([[&0]]), ([[pi / &2]])] INTEGRAL_BY_PARTS) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [SIMP_TAC [SessionLibrary.Analysis.REAL_LT_IMP_LE, PI_POS, REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV INTEGRABLE_CONV) THEN REWRITE_TAC [] THEN
      CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN DIFF_TAC THEN
      REWRITE_TAC [REAL_OF_NUM_ADD, ADD_SUB] THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    REWRITE_TAC [SIN_PI2, COS_PI2, SIN_0, COS_0] THEN
    REWRITE_TAC [h1] THEN
    REWRITE_TAC [(← HolLight.GSYM (← HolLight.CONJUNCT2 real_pow)), h2] THEN
    REWRITE_TAC [(← HolLight.GSYM ADD1), real_pow, SessionLibrary.Analysis.REAL_MUL_LZERO, SessionLibrary.Analysis.REAL_MUL_RZERO,
                SessionLibrary.Analysis.REAL_NEG_0, SessionLibrary.Analysis.REAL_SUB_LZERO] THEN
    REWRITE_TAC [(← HolLight.MATCH_MP h3 (← HolLight.SPEC_ALL SIN_CIRCLE))] THEN
    REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_LDISTRIB, (← HolLight.GSYM REAL_MUL_ASSOC), (← HolLight.GSYM REAL_POW_ADD)] THEN
    REWRITE_TAC [SessionLibrary.Analysis.REAL_MUL_RID] THEN
    SUBGOAL_THEN ([[integral(&0,pi / &2)
        (\x. (&n + &1) * sin x pow (n + 2) - (&n + &1) * sin x pow n) =
    (&n + &1) * (integral(&0,pi / &2) (\x. sin(x) pow (n + 2)) -
                 integral(&0,pi / &2) (\x. sin(x) pow n))]]) (fun th => SUBST1_TAC th THEN REAL_ARITH_TAC2) THEN
    REWRITE_TAC [(← HolLight.GSYM SessionLibrary.Analysis.REAL_SUB_LDISTRIB)] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[(&n + &1) *
    integral(&0,pi / &2) (\x. sin x pow (n + 2) - sin x pow n)]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_CMUL,
      AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SUB] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV INTEGRABLE_CONV) THEN SIMP_TAC [PI2_LE])
  : ExceptT String IO thm).run
#eval WALLIS_PARTS

#eval phrase 21
def WALLIS_PARTS' : thm := keep "WALLIS_PARTS'" fun _ => (do
  prove ([[!n. integral(&0,pi / &2) (\x. sin(x) pow (n + 2)) =
       (&n + &1) / (&n + &2) * integral(&0,pi / &2) (\x. sin(x) pow n)]])
   (MP_TAC WALLIS_PARTS THEN MATCH_MP_TAC MONO_FORALL THEN
    CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval WALLIS_PARTS'

#eval phrase 22
def WALLIS_0 : thm := keep "WALLIS_0" fun _ => (do
  prove ([[integral(&0,pi / &2) (\x. sin(x) pow 0) = pi / &2]])
   (REWRITE_TAC [real_pow, REAL_DIV_1, REAL_MUL_LID] THEN
    SIMP_TAC [INTEGRAL_CONST, SessionLibrary.Analysis.REAL_LT_IMP_LE, PI_POS, REAL_LT_DIV,
             REAL_OF_NUM_LT, ARITH, REAL_MUL_LID, SessionLibrary.Analysis.REAL_SUB_RZERO])
  : ExceptT String IO thm).run
#eval WALLIS_0

#eval phrase 23
def WALLIS_1 : thm := keep "WALLIS_1" fun _ => (do
  prove ([[integral(&0,pi / &2) (\x. sin(x) pow 1) = &1]])
   (MATCH_MP_TAC DEFINT_INTEGRAL THEN REWRITE_TAC [PI2_LE, REAL_POW_1] THEN
    MP_TAC (← HolLight.SPECL [([[\x. --cos(x)]]), ([[\x. sin x]]), ([[&0]]), ([[pi / &2]])] FTC1) THEN
    REWRITE_TAC [COS_0, COS_PI2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [PI2_LE] THEN
    REPEAT STRIP_TAC THEN DIFF_TAC THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval WALLIS_1

#eval phrase 24
def WALLIS_EVEN : thm := keep "WALLIS_EVEN" fun _ => (do
  let h3 ← ar (← ExceptT.mk [[2 * n + 2 = SUC(SUC(2 * n))]])
  let h2 ← rr (← ExceptT.mk [[(&2 * x) * y * z = (&2 * y) * (x * z)]])
  let h1 ← ar (← ExceptT.mk [[2 * SUC n = 2 * n + 2]])
  prove ([[!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n)) =
         (&(FACT(2 * n)) / (&2 pow n * &(FACT n)) pow 2) * pi / &2]])
   (INDUCT_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [WALLIS_0] THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    ASM_REWRITE_TAC [h1, WALLIS_PARTS'] THEN
    REWRITE_TAC [REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [FACT, real_pow, (← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
    ONCE_REWRITE_TAC [h2] THEN
    GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.ONCE_DEPTH_CONV) [REAL_POW_MUL] THEN
    REWRITE_TAC [real_div, REAL_INV_MUL, REAL_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [h3] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_SUC), REAL_POW_2, FACT,
                (← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
    CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval WALLIS_EVEN

#eval phrase 25
def WALLIS_ODD : thm := keep "WALLIS_ODD" fun _ => (do
  let h3 ← ar (← ExceptT.mk [[n + 2 = SUC(SUC n)]])
  let h2 ← rr (← ExceptT.mk [[(&2 * x) * y * z = (x * z) * (&2 * y)]])
  let h1 ← ar (← ExceptT.mk [[2 * SUC n + 1 = (2 * n + 1) + 2]])
  prove ([[!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n + 1)) =
         (&2 pow n * &(FACT n)) pow 2 / &(FACT(2 * n + 1))]])
   (INDUCT_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [WALLIS_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV,
      ALL_TAC] THEN
    ASM_REWRITE_TAC [h1,
                    WALLIS_PARTS'] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC [FACT, real_pow, (← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
    ONCE_REWRITE_TAC [h2] THEN
    GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.ONCE_DEPTH_CONV) [REAL_POW_MUL] THEN
    REWRITE_TAC [real_div, (← HolLight.GSYM REAL_MUL_ASSOC)] THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC [h3] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_SUC), REAL_POW_2, FACT,
                (← HolLight.GSYM REAL_OF_NUM_ADD), (← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
    MP_TAC (← HolLight.SPEC ([[2 * n + 1]]) FACT_LT) THEN REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_LT)] THEN
    CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval WALLIS_ODD

#eval phrase 26
def WALLIS_QUOTIENT : thm := keep "WALLIS_QUOTIENT" fun _ => (do
  prove ([[!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n)) /
       integral(&0,pi / &2) (\x. sin(x) pow (2 * n + 1)) =
        (&(FACT(2 * n)) * &(FACT(2 * n + 1))) / (&2 pow n * &(FACT n)) pow 4 *
        pi / &2]])
   (GEN_TAC THEN REWRITE_TAC [WALLIS_EVEN, WALLIS_ODD] THEN
    REWRITE_TAC [real_div, REAL_INV_MUL, (← HolLight.GSYM REAL_POW_INV), REAL_INV_INV] THEN
    REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval WALLIS_QUOTIENT

#eval phrase 27
def WALLIS_QUOTIENT' : thm := keep "WALLIS_QUOTIENT'" fun _ => (do
  prove ([[!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n)) /
       integral(&0,pi / &2) (\x. sin(x) pow (2 * n + 1)) * &2 / pi =
         (&(FACT(2 * n)) * &(FACT(2 * n + 1))) / (&2 pow n * &(FACT n)) pow 4]])
   (GEN_TAC THEN REWRITE_TAC [WALLIS_QUOTIENT] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.LAND_CONV o HolLight.RAND_CONV) [(← HolLight.GSYM REAL_INV_DIV)] THEN
    REWRITE_TAC [(← HolLight.GSYM real_div)] THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    MP_TAC PI2_NZ THEN CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval WALLIS_QUOTIENT'

#eval phrase 28
def WALLIS_MONO : thm := keep "WALLIS_MONO" fun _ => (do
  prove ([[!m n. m <= n
         ==> integral(&0,pi / &2) (\x. sin(x) pow n)
                <= integral(&0,pi / &2) (\x. sin(x) pow m)]])
   (REWRITE_TAC [LE_EXISTS] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INTEGRAL_LE THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV INTEGRABLE_CONV) THEN REWRITE_TAC [PI2_LE] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [REAL_POW_ADD] THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM SessionLibrary.Analysis.REAL_MUL_RID)] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE, MATCH_MP_TAC REAL_POW_1_LE] THEN
    REWRITE_TAC [SIN_BOUNDS] THEN
    (MP_TAC (← HolLight.SPEC ([[x:real]]) SIN_POS_PI_LE) THEN
     ANTS_TAC THENL [ALL_TAC, REAL_ARITH_TAC2] THEN
     REPEAT (POP_ASSUM MP_TAC) THEN MP_TAC PI2_LT THEN REAL_ARITH_TAC2))
  : ExceptT String IO thm).run
#eval WALLIS_MONO

#eval phrase 29
def WALLIS_LT : thm := keep "WALLIS_LT" fun _ => (do
  prove ([[!n. &0 < integral(&0,pi / &2) (\x. sin(x) pow n)]])
   (MATCH_MP_TAC ODDEVEN_INDUCT THEN
    REWRITE_TAC [WALLIS_0, WALLIS_1, PI2_LT, REAL_OF_NUM_LT, ARITH] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [WALLIS_PARTS'] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval WALLIS_LT

#eval phrase 30
def WALLIS_NZ : thm := keep "WALLIS_NZ" fun _ => (do
  prove ([[!n. ~(integral(&0,pi / &2) (\x. sin(x) pow n) = &0)]])
   (MP_TAC WALLIS_LT THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval WALLIS_NZ

#eval phrase 31
def WALLIS_BOUNDS : thm := keep "WALLIS_BOUNDS" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[n + 1 <= n + 2]])
  prove ([[!n. integral(&0,pi / &2) (\x. sin(x) pow (n + 1))
        <= integral(&0,pi / &2) (\x. sin(x) pow n) /\
       integral(&0,pi / &2) (\x. sin(x) pow n) <=
        (&n + &2) / (&n + &1) * integral(&0,pi / &2) (\x. sin(x) pow (n + 1))]])
   (GEN_TAC THEN SIMP_TAC [WALLIS_MONO, LE_ADD] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[(&n + &2) / (&n + &1) *
              integral (&0,pi / &2) (\x. sin x pow (n + 2))]]) THEN
    CONJ_TAC THENL
     [REWRITE_TAC [WALLIS_PARTS'] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_FIELD,
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    SIMP_TAC [WALLIS_MONO, h1] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval WALLIS_BOUNDS

#eval phrase 32
def WALLIS_RATIO_BOUNDS : thm := keep "WALLIS_RATIO_BOUNDS" fun _ => (do
  prove ([[!n. &1 <= integral(&0,pi / &2) (\x. sin(x) pow n) /
            integral(&0,pi / &2) (\x. sin(x) pow (n + 1)) /\
      integral(&0,pi / &2) (\x. sin(x) pow n) /
      integral(&0,pi / &2) (\x. sin(x) pow (n + 1)) <= (&n + &2) / (&n + &1)]])
   (GEN_TAC THEN CONJ_TAC THENL
     [SIMP_TAC [REAL_LE_RDIV_EQ, WALLIS_LT, REAL_MUL_LID, WALLIS_BOUNDS],
      SIMP_TAC [REAL_LE_LDIV_EQ, WALLIS_LT, WALLIS_BOUNDS]])
  : ExceptT String IO thm).run
#eval WALLIS_RATIO_BOUNDS

#eval phrase 33
def WALLIS : thm := keep "WALLIS" fun _ => (do
  let h3 ← rf (← ExceptT.mk [[(&2 * &n + &2) / (&2 * &n + &1) - &1 = &1 / (&2 * &n + &1)]])
  let h2 ← rr (← ExceptT.mk [[!d. &1 <= x /\ x <= d /\ d - &1 <= e ==> abs(x - &1) <= e]])
  let h1 ← rr (← ExceptT.mk [[x = (x - &1) + &1]])
  prove ([[(\n. (&2 pow n * &(FACT n)) pow 4 / (&(FACT(2 * n)) * &(FACT(2 * n + 1))))
   --> pi / &2]])
   (ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_INV_DIV)] THEN MATCH_MP_TAC SEQ_INV THEN
    CONJ_TAC THENL [ALL_TAC, MP_TAC PI2_NZ THEN CONV_TAC REAL_FIELD] THEN
    REWRITE_TAC [(← HolLight.GSYM WALLIS_QUOTIENT')] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM SessionLibrary.Analysis.REAL_MUL_RID)] THEN
    MATCH_MP_TAC SEQ_MUL THEN REWRITE_TAC [SEQ_CONST] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ABS_CONV) [h1] THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM REAL_ADD_LID)] THEN
    MATCH_MP_TAC SEQ_ADD THEN REWRITE_TAC [SEQ_CONST] THEN
    MATCH_MP_TAC SEQ_LE_0 THEN EXISTS_TAC ([[\n. &1 / &n]]) THEN
    REWRITE_TAC [SEQ_HARMONIC] THEN EXISTS_TAC ([[1]]) THEN
    REWRITE_TAC [GE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC h2 THEN
    EXISTS_TAC ([[(&(2 * n) + &2) / (&(2 * n) + &1)]]) THEN
    REWRITE_TAC [WALLIS_RATIO_BOUNDS] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
    REWRITE_TAC [h3] THEN
    REWRITE_TAC [real_div, REAL_MUL_LID, REAL_ABS_INV, REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_LE)] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval WALLIS

/- ------------------------------------------------------------------------- -/
/- Hence determine the actual value of the limit.                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 34
def LN_WALLIS : thm := keep "LN_WALLIS" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[&4 * x + &4 * y - z = &4 * (x + y) - z]])
  prove ([[(\n. &4 * &n * ln(&2) + &4 * ln(&(FACT n)) -
        (ln(&(FACT(2 * n))) + ln(&(FACT(2 * n + 1))))) --> ln(pi / &2)]])
   (REWRITE_TAC [h1] THEN
    SUBGOAL_THEN ([[!n. &0 < &2 pow n]]) (fun th => HolLight.tactic_of do
        pure (SIMP_TAC [th, (← HolLight.GSYM LN_POW), REAL_OF_NUM_LT, ARITH, (← HolLight.GSYM LN_MUL),
                         FACT_LT, REAL_POW_LT, REAL_LT_MUL, (← HolLight.GSYM LN_DIV)])) THEN
    SIMP_TAC [REAL_POW_LT, REAL_OF_NUM_LT, ARITH] THEN
    MATCH_MP_TAC CONTL_SEQ THEN REWRITE_TAC [WALLIS] THEN
    MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC ([[inv(pi / &2)]]) THEN
    MP_TAC (← HolLight.SPEC ([[pi / &2]]) (DIFF_CONV ([[\x. ln(x)]]))) THEN
    SIMP_TAC [ETA_AX, PI2_LT, REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
    REWRITE_TAC [SessionLibrary.Analysis.REAL_MUL_RID])
  : ExceptT String IO thm).run
#eval LN_WALLIS

#eval phrase 35
def STIRLING : thm := keep "STIRLING" fun _ => (do
  let h14 ← rr (← ExceptT.mk [[&1 = &1 + &3 / &2 * &0]])
  let h13 ← rf (← ExceptT.mk [[&0 < x ==> (&2 * x + &1) / (&2 * x) = &1 + &1 / (&2 * x)]])
  let h12 ← rr (← ExceptT.mk [[&0 < &2 * &n + &1]])
  let h11 ← rr (← ExceptT.mk [[a * (b - c) = --(a * (c - b))]])
  let h10 ← rr (← ExceptT.mk [[&0 = -- &1 + &1]])
  let h9 ← rr (← ExceptT.mk [[(&2 * n + &3 / &2) * l + &1 - ((&2 * n + &1) + &1 / &2) * l' =
    (&2 * n + &3 / &2) * (l - l') + &1]])
  let h8 ← rr (← ExceptT.mk [[((&4 * n + &2) * l + &1) - ((&2 * n + &1 / &2) * l + z) =
    (&2 * n + &3 / &2) * l + &1 - z]])
  let h7 ← rr (← ExceptT.mk [[&2 * l + &4 * n * l + &4 * (n + &1 / &2) * x + &1 =
                          (&4 * n + &2) * (l + x) + &1]])
  let h6 ← rr (← ExceptT.mk [[a + (b + &4 * (c - x)) - ((d - &2 * x) + (e - (&2 * x + &1))) =
    (a + b + &4 * c + &1) - (d + e)]])
  let h5 ← tt (← ExceptT.mk [[a /\ b ==> c <=> b ==> a ==> c]])
  let h4 ← rr (← ExceptT.mk [[C = (l + p) / &2 <=> (l + p) - &2 * C = &0]])
  let h3 ← rr (← ExceptT.mk [[&2 * l + p - l - (&4 * C - (C + C)) =
                          (l + p) - &2 * C]])
  let h2 ← ar (← ExceptT.mk [[(a + &4 * x - (y + z)) - (&4 * (x - b) - ((y - c) + (z - d))) =
    (a + &4 * b) - (c + d)]])
  let h1 ← rr (← ExceptT.mk [[a - (b - c + d) = (a - (b - c)) - d]])
  prove ([[(\n. ln(&(FACT n)) - ((&n + &1 / &2) * ln(&n) - &n + ln(&2 * pi) / &2))
   --> &0]])
   (REWRITE_TAC [h1] THEN
    SUBST1_TAC (← HolLight.SYM (← HolLight.SPEC ([[ln(&2 * pi) / &2]]) SessionLibrary.Analysis.REAL_SUB_REFL)) THEN
    MATCH_MP_TAC SEQ_SUB THEN REWRITE_TAC [SEQ_CONST] THEN
    X_CHOOSE_THEN ([[C:real]]) MP_TAC STIRLING_CONVERGES THEN
    GEN_REWRITE_TAC (HolCore.Lib.funpow 2 HolLight.LAND_CONV) [(← HolLight.GSYM ETA_AX)] THEN
    REWRITE_TAC [stirling] THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPECL [([[2]]), ([[1]])] o HolLight.MATCH_MP SEQ_SUBSEQ) THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPECL [([[2]]), ([[0]])] o HolLight.MATCH_MP SEQ_SUBSEQ) THEN
    REWRITE_TAC [ARITH, ADD_CLAUSES, IMP_IMP] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP SEQ_ADD) THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP SEQ_MUL o HolLight.CONJ (← HolLight.SPEC ([[&4]]) SEQ_CONST)) THEN
    REWRITE_TAC [IMP_IMP] THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP SEQ_SUB) THEN
    MP_TAC LN_WALLIS THEN REWRITE_TAC [IMP_IMP] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP SEQ_SUB) THEN
    REWRITE_TAC [h2] THEN
    DISCH_THEN (fun th => POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
    SUBGOAL_THEN ([[C = ln(&2 * pi) / &2]]) (fun th => REWRITE_TAC [th]) THEN
    POP_ASSUM (MP_TAC o HolLight.CONJ (← HolLight.SPEC ([[&2 * ln(&2)]]) SEQ_CONST)) THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP SEQ_ADD) THEN
    SIMP_TAC [LN_DIV, PI_POS, REAL_OF_NUM_LT, ARITH, LN_MUL] THEN
    REWRITE_TAC [h3] THEN
    SIMP_TAC [h4] THEN
    MATCH_MP_TAC (← HolLight.REWRITE_RULE [h5] SEQ_UNIQ) THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_ADD), (← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
    REWRITE_TAC [h6] THEN
    REWRITE_TAC [h7] THEN
    ONCE_REWRITE_TAC [SEQ_SUC] THEN
    SIMP_TAC [(← HolLight.GSYM LN_MUL), REAL_OF_NUM_LT, ARITH, LT_0] THEN
    REWRITE_TAC [(← HolLight.GSYM SEQ_SUC)] THEN
    CONV_TAC (HolLight.LAND_CONV ((pureC (HolCore.Equal.GEN_ALPHA_CONV ([[n:num]]))))) THEN
    REWRITE_TAC [h8] THEN
    REWRITE_TAC [h9] THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [h10] THEN
    MATCH_MP_TAC SEQ_ADD THEN REWRITE_TAC [SEQ_CONST] THEN
    ONCE_REWRITE_TAC [h11] THEN
    REWRITE_TAC [(← HolLight.GSYM SEQ_NEG)] THEN
    ONCE_REWRITE_TAC [SEQ_SUC] THEN
    SIMP_TAC [(← HolLight.GSYM LN_DIV), REAL_LT_MUL, REAL_OF_NUM_LT, LT_0, ARITH,
             h12] THEN
    SIMP_TAC [REAL_OF_NUM_LT, LT_0, h13] THEN
    REWRITE_TAC [(← HolLight.GSYM SEQ_SUC)] THEN
    CONV_TAC (HolLight.LAND_CONV ((pureC (HolCore.Equal.GEN_ALPHA_CONV ([[n:num]]))))) THEN
    MP_TAC SEQ_SUBSEQ THEN REWRITE_TAC [RIGHT_IMP_FORALL_THM] THEN
    DISCH_THEN (MP_TAC o HolLight.GENL [([[f:num->real]]), ([[l:real]])] o
     HolLight.SPECL [([[f:num->real]]), ([[l:real]]), ([[2]]), ([[0]])]) THEN
    REWRITE_TAC [ADD_CLAUSES, ARITH, REAL_OF_NUM_MUL] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONV_TAC (HolLight.LAND_CONV ((pureC (HolCore.Equal.GEN_ALPHA_CONV ([[n:num]]))))) THEN
    REWRITE_TAC [REAL_ADD_RDISTRIB] THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [h14] THEN
    MATCH_MP_TAC SEQ_ADD THEN REWRITE_TAC [LN_LIM_LEMMA] THEN
    MATCH_MP_TAC SEQ_MUL THEN REWRITE_TAC [SEQ_CONST] THEN
    MP_TAC LN_LIM_LEMMA THEN MP_TAC (← HolLight.SPEC ([[&1]]) SEQ_HARMONIC) THEN
    REWRITE_TAC [IMP_IMP] THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP SEQ_MUL) THEN
    REWRITE_TAC [] THEN ONCE_REWRITE_TAC [SEQ_SUC] THEN
    SIMP_TAC [real_div, REAL_MUL_LID, REAL_MUL_ASSOC, REAL_MUL_LINV,
             SessionLibrary.Analysis.REAL_MUL_RID, REAL_OF_NUM_EQ, NOT_SUC])
  : ExceptT String IO thm).run
#eval STIRLING

end Hol100.Stirling
