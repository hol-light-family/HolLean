/- File: HolExamples/Mangoldt.lean
Translation of HOL Light's Examples/mangoldt.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
import SessionLibrary.Pocklington
import SessionMultiLib.Transcendentals
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionLibrary.Card SessionLibrary.Prime SessionLibrary.Floor SessionLibrary.Iter
open SessionLibrary.Pocklington
open SessionMultiLib.Misc SessionMultiLib.Vectors SessionMultiLib.Determinants
open SessionMultiLib.Metric SessionMultiLib.Topology SessionMultiLib.Convex
open SessionMultiLib.Paths SessionMultiLib.Integration
open SessionMultiLib.Complexes SessionMultiLib.Canal SessionMultiLib.Transcendentals
namespace HolExamples.Mangoldt

/- Helpers: the session's `prove` lifted into `ExceptT String IO`, so tactic
   scripts read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def rf (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_FIELD tm)
private def rg (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_RING tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def nd (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.new_definition tm)
private def nc (tm : term) : ExceptT String IO thm := ExceptT.mk (num_CONV tm)

-- ========================================================================= --
-- Mangoldt function and elementary Chebyshev/Mertens results.               --
-- ========================================================================= --

#eval phrase 1
-- needs "Library/pocklington.ml";;
#eval SessionLibrary.Pocklington.ensurePocklington

#eval phrase 2
-- needs "Multivariate/transcendentals.ml";;
#eval SessionMultiLib.Transcendentals.ensureTranscendentals

#eval phrase 3
-- prioritize_real();;
#eval Session.prioritize_real

-- ------------------------------------------------------------------------- --
-- Useful approximation/bound lemmas, simple rather than sharp.              --
-- ------------------------------------------------------------------------- --

#eval phrase 4
def LOG_FACT : thm := keep "LOG_FACT" fun _ => (do
  -- OCaml builds the tactic right to left: the build-time rules run
  -- bottom-first, so their traces print in that order.
  let h1 ← ar (← ExceptT.mk [[1 <= SUC n]])
  prove ([[!n. log(&(FACT n)) = sum(1..n) (\d. log(&d))]])
   (INDUCT_TAC THEN
    SIMP_TAC [FACT, SUM_CLAUSES_NUMSEG, LOG_1, ARITH, h1] THEN
    SIMP_TAC [(← HolLight.GSYM REAL_OF_NUM_MUL), LOG_MUL, REAL_OF_NUM_LT, FACT_LT, LT_0] THEN
    ASM_REWRITE_TAC [ADD1] THEN REWRITE_TAC [ADD_AC, REAL_ADD_AC])
  : ExceptT String IO thm).run
#eval LOG_FACT

#eval phrase 5
def SUM_DIVISORS_FLOOR_LEMMA : thm := keep "SUM_DIVISORS_FLOOR_LEMMA" fun _ => (do
  let h3 ← ar (← ExceptT.mk [[n < 1 <=> n = 0]])
  let h2 ← ar (← ExceptT.mk [[d = 1 * d]])
  let h1 ← ar (← ExceptT.mk [[1 <= n <=> ~(n = 0)]])
  prove ([[!n d. ~(d = 0)
         ==> sum(1..n) (\m. if d divides m then &1 else &0) = floor(&n / &d)]])
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [FLOOR_DIV_DIV] THEN
    SIMP_TAC [(← HolLight.GSYM SUM_RESTRICT_SET), FINITE_NUMSEG, SUM_CONST, FINITE_RESTRICT,
             REAL_MUL_RID, REAL_OF_NUM_EQ] THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM CARD_NUMSEG_1)] THEN
    MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
    MAP_EVERY EXISTS_TAC [([[\m:num. m DIV d]]), ([[\m:num. m * d]])] THEN
    ASM_SIMP_TAC [IN_ELIM_THM, IN_NUMSEG, LE_1, DIV_MULT, DIVIDES_DIV_MULT,
                 FINITE_NUMSEG, (← HolLight.ONCE_REWRITE_RULE [MULT_SYM] DIV_MULT),
                 DIV_MONO, LE_1] THEN
    ASM_SIMP_TAC [LE_RDIV_EQ, MULT_EQ_0, h1] THEN
    CONJ_TAC THENL [GEN_TAC THEN STRIP_TAC, ARITH_TAC] THEN
    FIRST_X_ASSUM (SUBST_ALL_TAC o HolLight.SYM) THEN ASM_SIMP_TAC [DIV_EQ_0] THEN
    GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV) [h2] THEN
    ASM_SIMP_TAC [LT_MULT_RCANCEL, h3] THEN
    ASM_MESON_TAC [MULT_CLAUSES])
  : ExceptT String IO thm).run
#eval SUM_DIVISORS_FLOOR_LEMMA

#eval phrase 6
def LOG_2_BOUNDS : thm := keep "LOG_2_BOUNDS" fun _ => (do
  prove ([[&1 / &2 <= log(&2) /\ log(&2) <= &1]])
   (CONJ_TAC THENL
     [GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM LOG_EXP)] THEN
      MP_TAC (← HolLight.SPEC ([[inv(&2)]]) REAL_EXP_BOUND_LEMMA),
      GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM LOG_EXP)] THEN
      MP_TAC (← HolLight.SPEC ([[&1]]) REAL_EXP_LE_X)] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN MATCH_MP_TAC EQ_IMP THEN
    CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC LOG_MONO_LE THEN
    REWRITE_TAC [REAL_EXP_POS_LT, REAL_OF_NUM_LT, ARITH])
  : ExceptT String IO thm).run
#eval LOG_2_BOUNDS

#eval phrase 7
def LOG_LE_REFL : thm := keep "LOG_LE_REFL" fun _ => (do
  let h2 ← rr (← ExceptT.mk [[n = &1 + (n  - &1)]])
  let h1 ← rr (← ExceptT.mk [[x <= y - &1 ==> x <= y]])
  prove ([[!n. ~(n = 0) ==> log(&n) <= &n]])
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC h1 THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV)
     [h2] THEN
    MATCH_MP_TAC LOG_LE THEN
    REWRITE_TAC [REAL_LE_SUB_LADD, REAL_OF_NUM_ADD, REAL_OF_NUM_LE] THEN
    UNDISCH_TAC ([[~(n = 0)]]) THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval LOG_LE_REFL

#eval phrase 8
def LOG_FACT_BOUNDS : thm := keep "LOG_FACT_BOUNDS" fun _ => (do
  let h13 ← rf
    (← ExceptT.mk [[~(n = &0) ==> &1 / n * (n + &1) = inv(n) + &1]])
  let h12 ← rr
    (← ExceptT.mk [[(n + &1) * (l + n') <= (n + k) * l + &1 <=>
    n' * (n + &1) <= (k - &1) * l + &1]])
  let h11 ← rf (← ExceptT.mk [[&0 < x ==> (x + &1) / x = &1 + &1 / x]])
  let h10 ← rr (← ExceptT.mk [[&0 < &n + &1]])
  let h9 ← rr (← ExceptT.mk [[x <= y + z <=> x - y <= z]])
  let h8 ← rr
    (← ExceptT.mk [[(n + &1) * l' - (n + &1) + &1 <= (n * l - n + &1) + k * l <=>
    (n + &1) * l' <= (n + k) * l + &1]])
  let h7 ← rr (← ExceptT.mk [[&0 < &n + &1]])
  let h6 ← ar (← ExceptT.mk [[2 <= n ==> 0 < n]])
  let h5 ← rr (← ExceptT.mk [[y <= x /\ a <= b ==> x <= a ==> y <= b]])
  let h4 ← ar
    (← ExceptT.mk [[~(n = 0) ==> n = 1 \/ 2 <= n]])
  let h3 ← ar (← ExceptT.mk [[1 <= n <=> ~(n = 0)]])
  let h2 ← rr (← ExceptT.mk [[abs(x - y) <= e <=> x <= y + e /\ y - e <= x]])
  let h1 ← nc (← ExceptT.mk [[1]])
  prove ([[!n. ~(n = 0)
       ==> abs(log(&(FACT n)) - (&n * log(&n) - &n + &1)) <= &2 * log(&n)]])
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC ([[n = 1]]) THENL
     [ASM_REWRITE_TAC [h1, FACT] THEN
      REWRITE_TAC [ARITH, LOG_1] THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    ASM_SIMP_TAC [LOG_FACT] THEN
    REWRITE_TAC [h2] THEN
    CONJ_TAC THENL
     [MP_TAC (← HolLight.ISPECL [([[\z. clog(z)]]), ([[\z. z * clog z - z]]), ([[1]]), ([[n:num]])]
                   SUM_INTEGRAL_UBOUND_INCREASING) THEN
      REWRITE_TAC [] THEN ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
        CONJ_TAC THENL
         [REWRITE_TAC [IN_SEGMENT_CX_GEN] THEN REPEAT STRIP_TAC THENL
           [COMPLEX_DIFF_TAC THEN CONJ_TAC THEN UNDISCH_TAC ([[&1 <= Re x]]) THENL
             [REAL_ARITH_TAC2, ALL_TAC] THEN
            ASM_CASES_TAC ([[x = Cx(&0)]]) THEN ASM_REWRITE_TAC [RE_CX] THENL
             [REAL_ARITH_TAC2,
              UNDISCH_TAC ([[~(x = Cx(&0))]]) THEN CONV_TAC COMPLEX_FIELD],
            FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I
              [(← HolLight.GSYM LT_NZ)]) THEN
            REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_LT)] THEN
            ASM_REAL_ARITH_TAC],
          MAP_EVERY X_GEN_TAC [([[a:real]]), ([[b:real]])] THEN STRIP_TAC THEN
          SUBGOAL_THEN ([[&0 < a /\ &0 < b]]) ASSUME_TAC THENL
           [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
          ASM_SIMP_TAC [(← HolLight.GSYM CX_LOG), RE_CX, LOG_MONO_LE_IMP]],
          ALL_TAC],
       ASM_SIMP_TAC [SUM_CLAUSES_LEFT, h3] THEN
       REWRITE_TAC [LOG_1, REAL_ADD_LID, ARITH] THEN
       FIRST_ASSUM (DISJ_CASES_TAC o HolLight.MATCH_MP h4)
       THENL
        [ASM_REWRITE_TAC [] THEN CONV_TAC (HolLight.ONCE_DEPTH_CONV NUMSEG_CONV) THEN
         REWRITE_TAC [LOG_1, SUM_CLAUSES] THEN REAL_ARITH_TAC2,
         ALL_TAC] THEN
       MP_TAC (← HolLight.ISPECL [([[\z. clog(z)]]), ([[\z. z * clog z - z]]), ([[2]]), ([[n:num]])]
                    SUM_INTEGRAL_LBOUND_INCREASING) THEN
       REWRITE_TAC [] THEN ANTS_TAC THENL
        [CONJ_TAC THENL [POP_ASSUM MP_TAC THEN ARITH_TAC, ALL_TAC] THEN
         CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
          [REWRITE_TAC [IN_SEGMENT_CX_GEN] THEN REPEAT STRIP_TAC THENL
            [COMPLEX_DIFF_TAC THEN CONJ_TAC THEN UNDISCH_TAC ([[&1 <= Re x]]) THENL
              [REAL_ARITH_TAC2, ALL_TAC] THEN
             ASM_CASES_TAC ([[x = Cx(&0)]]) THEN ASM_REWRITE_TAC [RE_CX] THENL
              [REAL_ARITH_TAC2,
               UNDISCH_TAC ([[~(x = Cx(&0))]]) THEN CONV_TAC COMPLEX_FIELD],
             FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I
               [(← HolLight.GSYM REAL_OF_NUM_LE)]) THEN
             ASM_REAL_ARITH_TAC],
          MAP_EVERY X_GEN_TAC [([[a:real]]), ([[b:real]])] THEN STRIP_TAC THEN
          SUBGOAL_THEN ([[&0 < a /\ &0 < b]]) ASSUME_TAC THENL
           [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
          ASM_SIMP_TAC [(← HolLight.GSYM CX_LOG), RE_CX, LOG_MONO_LE_IMP]],
         ALL_TAC]] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC h5 THEN
    ASM_SIMP_TAC [(← HolLight.GSYM CX_LOG), SUM_EQ_NUMSEG, REAL_OF_NUM_LT, LE_1, CLOG_1,
                 h6, RE_CX,
                 h7, REAL_EQ_IMP_LE] THEN
    REWRITE_TAC [(← HolLight.GSYM CX_MUL), (← HolLight.GSYM CX_SUB),
                 (← HolLight.GSYM CX_ADD), RE_CX] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [REAL_SUB_RNEG] THENL
     [REWRITE_TAC [h8] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC ([[(&n + &1) * (log(&n) + &1 / &n)]]) THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [REAL_ARITH_TAC2, ALL_TAC] THEN
        REWRITE_TAC [h9] THEN
        ASM_SIMP_TAC [(← HolLight.GSYM LOG_DIV), REAL_OF_NUM_LT, LT_NZ,
                     h10,
                     h11] THEN
        MATCH_MP_TAC LOG_LE THEN SIMP_TAC [REAL_LE_DIV, REAL_POS],
        ALL_TAC] THEN
      REWRITE_TAC [h12] THEN
      ASM_SIMP_TAC [REAL_OF_NUM_EQ, REAL_LE_RADD, h13] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC ([[inv(&2)]]) THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC [REAL_OF_NUM_LE, REAL_OF_NUM_LT] THEN
        ASM_ARITH_TAC,
        ALL_TAC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC ([[log(&2)]]) THEN
      REWRITE_TAC [LOG_2_BOUNDS] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC [REAL_OF_NUM_LE, REAL_OF_NUM_LE] THEN ASM_ARITH_TAC,
      SUBGOAL_THEN ([[&0 <= log(&n)]]) MP_TAC THENL [ALL_TAC, REAL_ARITH_TAC2] THEN
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC [REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC])
  : ExceptT String IO thm).run
#eval LOG_FACT_BOUNDS

-- ------------------------------------------------------------------------- --
-- The Mangoldt function and its key expansion.                              --
-- ------------------------------------------------------------------------- --

#eval phrase 9
def mangoldt : thm := keep "mangoldt" fun _ => (do
  nd ([[mangoldt n = if ?p k. 1 <= k /\ prime p /\ n = p EXP k
               then log(&(@p. prime p /\ p divides n))
               else &0]])
  : ExceptT String IO thm).run
#eval mangoldt

#eval phrase 10
def MANGOLDT_1 : thm := keep "MANGOLDT_1" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[~(1 <= 0)]])
  prove ([[mangoldt 1 = &0]])
   (REWRITE_TAC [mangoldt] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    REWRITE_TAC [EXP_EQ_1] THEN MESON_TAC [PRIME_1, h1])
  : ExceptT String IO thm).run
#eval MANGOLDT_1

#eval phrase 11
def MANGOLDT_PRIMEPOW : thm := keep "MANGOLDT_PRIMEPOW" fun _ => (do
  let h2 ← tt (← ExceptT.mk [[~(a /\ b ==> ~(c /\ d)) <=> d /\ c /\ a /\ b]])
  let h1 ← tt (← ExceptT.mk [[a /\ b /\ c <=> ~(a /\ b ==> ~c)]])
  prove ([[!p k. prime p ==> mangoldt(p EXP k) = if 1 <= k then log(&p) else &0]])
   (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [mangoldt] THEN
    ONCE_REWRITE_TAC [h1] THEN
    ASM_SIMP_TAC [EQ_PRIME_EXP, LE_1] THEN
    REWRITE_TAC [h2] THEN
    ASM_REWRITE_TAC [UNWIND_THM1] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN REPEAT AP_TERM_TAC THEN
    ASM_SIMP_TAC [DIVIDES_PRIMEPOW] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    ASM_MESON_TAC [PRIME_DIVEXP, prime, PRIME_1, DIVIDES_REFL, EXP_1])
  : ExceptT String IO thm).run
#eval MANGOLDT_PRIMEPOW

#eval phrase 12
def MANGOLDT_POS_LE : thm := keep "MANGOLDT_POS_LE" fun _ => (do
  prove ([[!n. &0 <= mangoldt n]])
   (GEN_TAC THEN ASM_CASES_TAC ([[?p k. 1 <= k /\ prime p /\ n = p EXP k]]) THENL
     [FIRST_X_ASSUM (REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC [MANGOLDT_PRIMEPOW] THEN MATCH_MP_TAC LOG_POS THEN
      REWRITE_TAC [REAL_OF_NUM_LE] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP PRIME_GE_2) THEN ARITH_TAC,
      ASM_REWRITE_TAC [mangoldt, REAL_LE_REFL]])
  : ExceptT String IO thm).run
#eval MANGOLDT_POS_LE

#eval phrase 13
def LOG_MANGOLDT_SUM : thm := keep "LOG_MANGOLDT_SUM" fun _ => (do
  let h6 ← ar (← ExceptT.mk [[2 <= p ==> ~(p = 0) /\ ~(p = 1)]])
  let h5 ← sr (← ExceptT.mk [[{d | ?i. i <= k /\ d = p EXP i} =
    IMAGE (\i. p EXP i) {i | i <= k}]])
  let h4 ← ar (← ExceptT.mk [[1 < n ==> ~(n = 0)]])
  let h3 ← ar (← ExceptT.mk [[1 < a ==> 0 < a]])
  let h2 ← ar (← ExceptT.mk [[~(1 <= 0)]])
  let h1 ← sr (← ExceptT.mk [[{x | x = a} = {a}]])
  prove ([[!n. ~(n = 0) ==> log(&n) = sum {d | d divides n} (\d. mangoldt(d))]])
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC ([[n = 1]]) THENL
     [ASM_REWRITE_TAC [LOG_1, DIVIDES_ONE, h1] THEN
      REWRITE_TAC [SUM_SING, mangoldt] THEN
      GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
      REWRITE_TAC [EXP_EQ_1] THEN MESON_TAC [PRIME_1, h2],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[1 < n]]) MP_TAC THENL
     [ASM_ARITH_TAC, ALL_TAC] THEN
    SPEC_TAC (([[n:num]]), ([[n:num]])) THEN POP_ASSUM_LIST (HolCore.Lib.K ALL_TAC) THEN
    MATCH_MP_TAC INDUCT_COPRIME THEN REPEAT STRIP_TAC THENL
     [ASM_SIMP_TAC [LOG_MUL, (← HolLight.GSYM REAL_OF_NUM_MUL), REAL_OF_NUM_LT,
                   h3] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC
       ([[sum ({d | d divides a} UNION {d | d divides b}) (\d. mangoldt d)]]) THEN
      CONJ_TAC THEN CONV_TAC HolLight.SYM_CONV THENL
       [MATCH_MP_TAC SUM_UNION_NONZERO THEN REWRITE_TAC [IN_INTER] THEN
        ASM_SIMP_TAC [FINITE_DIVISORS, h4] THEN
        REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [coprime, MANGOLDT_1],
        MATCH_MP_TAC SUM_SUPERSET THEN REWRITE_TAC [UNION_SUBSET, IN_UNION] THEN
        SIMP_TAC [SUBSET, IN_ELIM_THM, DIVIDES_LMUL, DIVIDES_RMUL] THEN
        X_GEN_TAC ([[d:num]]) THEN STRIP_TAC THEN REWRITE_TAC [mangoldt] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
        ASM_MESON_TAC [PRIME_DIVPROD_POW]],
      ALL_TAC] THEN
    ASM_SIMP_TAC [DIVIDES_PRIMEPOW, (← HolLight.GSYM REAL_OF_NUM_POW)] THEN
    REWRITE_TAC [h5] THEN
    ASM_SIMP_TAC [EQ_EXP, SUM_IMAGE, PRIME_GE_2,
                 h6] THEN
    ASM_SIMP_TAC [MANGOLDT_PRIMEPOW, o_DEF] THEN
    ASM_SIMP_TAC [(← HolLight.GSYM SUM_RESTRICT_SET), IN_ELIM_THM, FINITE_NUMSEG_LE] THEN
    ONCE_REWRITE_TAC [CONJ_SYM] THEN REWRITE_TAC [(← HolLight.GSYM numseg)] THEN
    ASM_SIMP_TAC [LOG_POW, PRIME_IMP_NZ, REAL_OF_NUM_LT, LT_NZ] THEN
    SIMP_TAC [SUM_CONST, CARD_NUMSEG_1, FINITE_NUMSEG])
  : ExceptT String IO thm).run
#eval LOG_MANGOLDT_SUM

#eval phrase 14
def MANGOLDT : thm := keep "MANGOLDT" fun _ => (do
  prove ([[!n. log(&(FACT n)) = sum(1..n) (\d. mangoldt(d) * floor(&n / &d))]])
   (GEN_TAC THEN REWRITE_TAC [LOG_FACT] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[sum(1..n) (\m. sum {d | d divides m} (\d. mangoldt d))]]) THEN
    SIMP_TAC [LOG_MANGOLDT_SUM, SUM_EQ_NUMSEG, LE_1] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     ([[sum (1..n) (\m. sum (1..n)
       (\d. mangoldt d * (if d divides m then &1 else &0)))]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC ([[m:num]]) THEN
      STRIP_TAC THEN REWRITE_TAC [] THEN CONV_TAC HolLight.SYM_CONV THEN
      MATCH_MP_TAC SUM_EQ_SUPERSET THEN
      ASM_SIMP_TAC [LE_1, FINITE_DIVISORS, IN_ELIM_THM, REAL_MUL_RZERO,
                   REAL_MUL_RID, SUBSET, IN_NUMSEG] THEN
      GEN_TAC THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP DIVIDES_LE_STRONG) THEN
      ASM_ARITH_TAC,
      GEN_REWRITE_TAC HolLight.LAND_CONV [SUM_SWAP_NUMSEG] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC ([[d:num]]) THEN
      ASM_SIMP_TAC [SUM_DIVISORS_FLOOR_LEMMA, LE_1, SUM_LMUL]])
  : ExceptT String IO thm).run
#eval MANGOLDT

-- ------------------------------------------------------------------------- --
-- The Chebyshev psi function and the key bounds on it.                      --
-- ------------------------------------------------------------------------- --

#eval phrase 15
def PSI_BOUND_INDUCT : thm := keep "PSI_BOUND_INDUCT" fun _ => (do
  let h6 ← ar (← ExceptT.mk [[1 <= n <=> ~(n = 0)]])
  let h5 ← rr
    (← ExceptT.mk [[a2 + e2 + &2 * (e1 - a1) <= m
    ==> abs(f2 - a2) <= e2 ==> abs(f1 - a1) <= e1 ==> f2 - &2 * f1 <= m]])
  let h4 ← rr (← ExceptT.mk [[y' <= y ==> x - y <= x - y']])
  let h3 ← rr (← ExceptT.mk [[m * (f1 - &2 * f2) = m * f1 - &2 * m * f2]])
  let h2 ← rr (← ExceptT.mk [[&1 <= a /\ b = &0 ==> &1 <= a - &2 * b]])
  let h1 ← ar
    (← ExceptT.mk [[~(n = 0) ==> 1 <= n + 1 /\ n <= 2 * n]])
  prove ([[!n. ~(n = 0)
       ==> sum(1..2*n) (\d. mangoldt(d)) -
           sum(1..n) (\d. mangoldt(d)) <= &9 * &n]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC ([[sum (n+1..2 * n) (\d. mangoldt d)]]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC [REAL_EQ_SUB_RADD] THEN
      CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC SUM_UNION_EQ THEN
      ONCE_REWRITE_TAC [UNION_COMM] THEN REWRITE_TAC [FINITE_NUMSEG] THEN
      ASM_SIMP_TAC [NUMSEG_COMBINE_R, h1] THEN
      REWRITE_TAC [EXTENSION, IN_INTER, NOT_IN_EMPTY, IN_NUMSEG] THEN ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     ([[sum (n+1..2*n)
          (\d. mangoldt(d) * (floor(&(2 * n) / &d) - &2 * floor(&n / &d)))]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC ([[r:num]]) THEN STRIP_TAC THEN
      REWRITE_TAC [] THEN GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM REAL_MUL_RID)] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [MANGOLDT_POS_LE] THEN
      MATCH_MP_TAC h2 THEN
      SUBGOAL_THEN ([[~(r = 0)]]) ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      ASM_SIMP_TAC [FLOOR_DIV_DIV, FLOOR_NUM, REAL_OF_NUM_LE, REAL_OF_NUM_EQ] THEN
      ASM_SIMP_TAC [DIV_EQ_0, LE_RDIV_EQ] THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     ([[sum (1..2*n)
          (\d. mangoldt(d) * (floor(&(2 * n) / &d) - &2 * floor(&n / &d)))]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET THEN
      REWRITE_TAC [FINITE_NUMSEG, IN_DIFF, IN_NUMSEG] THEN
      CONJ_TAC THENL [ARITH_TAC, ALL_TAC] THEN
      X_GEN_TAC ([[r:num]]) THEN STRIP_TAC THEN
      SUBGOAL_THEN ([[~(r = 0)]]) ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [MANGOLDT_POS_LE] THEN
      ASM_SIMP_TAC [FLOOR_DIV_DIV, REAL_NEG_SUB, REAL_SUB_LE] THEN
      ASM_SIMP_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_LE, MULT_DIV_LE],
      ALL_TAC] THEN
    REWRITE_TAC [h3] THEN
    REWRITE_TAC [SUM_SUB_NUMSEG, SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC ([[sum(1..2*n) (\d. mangoldt(d) * floor(&(2 * n) / &d)) -
                &2 * sum(1..n) (\d. mangoldt(d) * floor(&n / &d))]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC h4 THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_POS] THEN
      MATCH_MP_TAC SUM_SUBSET THEN
      REWRITE_TAC [FINITE_NUMSEG, IN_DIFF, IN_NUMSEG] THEN
      SIMP_TAC [FLOOR_DIV_DIV, LE_1, FLOOR_NUM, REAL_LE_MUL, REAL_POS,
               MANGOLDT_POS_LE] THEN
      ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM MANGOLDT)] THEN
    MAP_EVERY (fun t => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC t LOG_FACT_BOUNDS)))
      [([[n:num]]), ([[2 * n]])] THEN
    ASM_REWRITE_TAC [MULT_EQ_0, ARITH_EQ] THEN
    MATCH_MP_TAC h5 THEN
    ASM_SIMP_TAC [(← HolLight.GSYM REAL_OF_NUM_MUL), LOG_MUL, REAL_OF_NUM_LT, LT_NZ, ARITH] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     ([[&6 * log(&n) + (&2 * log(&2) - &1) * &1 + (&2 * log(&2)) * &n]]) THEN
    CONJ_TAC THENL [REAL_ARITH_TAC2, ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC ([[&6 * &n + (&2 * log(&2) - &1) * &n + (&2 * log(&2)) * &n]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD2 THEN
      ASM_SIMP_TAC [LOG_LE_REFL, REAL_LE_LMUL, REAL_POS, REAL_LE_RADD] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC [REAL_OF_NUM_LE, h6],
      REWRITE_TAC [(← HolLight.GSYM REAL_ADD_RDISTRIB)] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [REAL_POS]] THEN
    MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval PSI_BOUND_INDUCT

#eval phrase 16
def PSI_BOUND_EXP : thm := keep "PSI_BOUND_EXP" fun _ => (do
  let h1 ← rr
    (← ExceptT.mk [[s1 <= &9 * e ==> s2 - s1 <= &9 * e ==> s2 <= &9 * &2 * e]])
  prove ([[!n. sum(1..2 EXP n) (\d. mangoldt(d)) <= &9 * &(2 EXP n)]])
   (INDUCT_TAC THEN
    SIMP_TAC [EXP, SUM_SING_NUMSEG, MANGOLDT_1, REAL_LE_MUL, REAL_POS] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h1) THEN
    MATCH_MP_TAC PSI_BOUND_INDUCT THEN
    REWRITE_TAC [EXP_EQ_0, ARITH])
  : ExceptT String IO thm).run
#eval PSI_BOUND_EXP

#eval phrase 17
def PSI_BOUND : thm := keep "PSI_BOUND" fun _ => (do
  let h1 ← ar
    (← ExceptT.mk [[~(k = 0) ==> k = SUC(k - 1)]])
  prove ([[!n. sum(1..n) (\d. mangoldt(d)) <= &18 * &n]])
   (GEN_TAC THEN ASM_CASES_TAC ([[n <= 1]]) THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC ([[sum(1..1) (\d. mangoldt d)]]) THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUM_SUBSET, ALL_TAC] THEN
      REWRITE_TAC [SUM_SING_NUMSEG, FINITE_NUMSEG, IN_DIFF, IN_NUMSEG] THEN
      SIMP_TAC [MANGOLDT_POS_LE, MANGOLDT_1, REAL_LE_MUL, REAL_POS] THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[?k. n <= 2 EXP k /\ !l. l < k ==> ~(n <= 2 EXP l)]])
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM num_WOP)] THEN EXISTS_TAC ([[n:num]]) THEN
      MP_TAC (← HolLight.SPEC ([[n:num]]) LT_POW2_REFL) THEN REWRITE_TAC [EXP] THEN ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC ([[sum(1..2 EXP k) (\d. mangoldt d)]]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET THEN
      REWRITE_TAC [FINITE_NUMSEG, IN_DIFF, IN_NUMSEG, MANGOLDT_POS_LE] THEN
      ASM_ARITH_TAC,
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC ([[&9 * &(2 EXP k)]]) THEN
      REWRITE_TAC [PSI_BOUND_EXP] THEN
      ASM_CASES_TAC ([[k = 0]]) THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN
      FIRST_ASSUM (SUBST1_TAC o HolLight.MATCH_MP h1) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[k - 1]])) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      REWRITE_TAC [REAL_OF_NUM_MUL, EXP, REAL_OF_NUM_LE] THEN ARITH_TAC])
  : ExceptT String IO thm).run
#eval PSI_BOUND

-- ------------------------------------------------------------------------- --
-- Now Mertens's first theorem.                                              --
-- ------------------------------------------------------------------------- --

#eval phrase 18
def MERTENS_LEMMA : thm := keep "MERTENS_LEMMA" fun _ => (do
  let h6 ← rr
    (← ExceptT.mk [[x <= (k - &2) * n /\ l <= n ==> x <= k * n - &2 * l]])
  let h5 ← rr
    (← ExceptT.mk [[--(a * (x - y)):real = a * (y - x)]])
  let h4 ← rr (← ExceptT.mk [[&0 <= --x /\ --x <= y ==> abs(x) <= y]])
  let h3 ← rr (← ExceptT.mk [[n * i / x:real = i * n / x]])
  let h2 ← rr (← ExceptT.mk [[&1 <= x ==> abs(x - &1) <= x]])
  let h1 ← rr
    (← ExceptT.mk [[abs(n - &1) <= n /\ abs(s' - s) <= (k - &1) * n - a
    ==> abs(s' - (nl - n + &1)) <= a
    ==> abs(s - nl) <= n * k]])
  prove ([[!n. ~(n = 0) ==> abs(sum(1..n) (\d. mangoldt(d) / &d) - log(&n)) <= &21]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
    EXISTS_TAC ([[&n]]) THEN ASM_SIMP_TAC [REAL_OF_NUM_LT, LT_NZ] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.LAND_CONV) [(← HolLight.GSYM REAL_ABS_NUM)] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_ABS_MUL), REAL_SUB_LDISTRIB, (← HolLight.GSYM SUM_LMUL)] THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP LOG_FACT_BOUNDS) THEN REWRITE_TAC [MANGOLDT] THEN
    MATCH_MP_TAC h1 THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC h2 THEN
      REWRITE_TAC [REAL_OF_NUM_LE] THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_SUB_NUMSEG)] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ONCE_REWRITE_TAC [h3] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_SUB_LDISTRIB)] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC ([[sum(1..n) (\i. mangoldt i)]]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC h4 THEN
      REWRITE_TAC [(← HolLight.GSYM SUM_NEG), h5] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN SIMP_TAC [] THEN
        X_GEN_TAC ([[i:num]]) THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL,
        MATCH_MP_TAC SUM_LE_NUMSEG THEN SIMP_TAC [] THEN
         X_GEN_TAC ([[i:num]]) THEN STRIP_TAC THEN
        GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM REAL_MUL_RID)] THEN
        MATCH_MP_TAC REAL_LE_LMUL] THEN
      ASM_REWRITE_TAC [MANGOLDT_POS_LE, REAL_SUB_LE, REAL_LE_SUB_RADD] THEN
      MP_TAC (← HolLight.SPEC ([[&n / &i]]) FLOOR) THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    MATCH_MP_TAC h6 THEN
    ASM_SIMP_TAC [LOG_LE_REFL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC [PSI_BOUND])
  : ExceptT String IO thm).run
#eval MERTENS_LEMMA

#eval phrase 19
def MERTENS_MANGOLDT_VERSUS_LOG : thm := keep "MERTENS_MANGOLDT_VERSUS_LOG" fun _ => (do
  let h30 ← ar (← ExceptT.mk [[3 <= n ==> 1 <= n /\ 1 < n]])
  let h29 ← rr (← ExceptT.mk [[x - &1 <= x]])
  let h28 ← rr (← ExceptT.mk [[--x <= &0 <=> &0 <= x]])
  let h27 ← rr (← ExceptT.mk [[a <= b /\ --c <= e ==> a - b - c <= e]])
  let h26 ← rr
    (← ExceptT.mk [[a <= e - &2 /\ x <= &1 ==> a + &2 * x <= e]])
  let h25 ← rr (← ExceptT.mk [[a - (&0 - x - x / &1) = a + &2 * x]])
  let h24 ← ar (← ExceptT.mk [[3 <= n ==> 0 < n /\ 1 < n]])
  let h23 ← rr (← ExceptT.mk [[x = y /\ a <= b ==> x <= a ==> y <= b]])
  let h22 ← rr
    (← ExceptT.mk [[a * b <= &1 /\ &1 / &2 <= c ==> b * a <= &2 * c]])
  let h21 ← rg (← ExceptT.mk [[(x:real) pow 3 = x * x pow 2]])
  let h20 ← rr
    (← ExceptT.mk [[x <= y
    ==> (x <= u /\ u <= y \/ y <= u /\ u <= x <=> x <= u /\ u <= y)]])
  let h19 ← rr (← ExceptT.mk [[a * (y - x) <= &0 <=> &0 <= --a * (y - x)]])
  let h18 ← rr (← ExceptT.mk [[x <= y <=> x - y <= &0]])
  let h17 ← rr (← ExceptT.mk [[a <= x /\ x <= b \/ b <= x /\ x <= a <=>
    a <= x /\ x <= b \/ b < a /\ b <= x /\ x <= a]])
  let h16 ← rr (← ExceptT.mk [[&2 <= x ==> &1 < x /\ &0 < x]])
  let h15 ← rr
    (← ExceptT.mk [[x <= &1 /\ y <= e - &1 ==> x + y <= e]])
  let h14 ← rr (← ExceptT.mk [[x - &1 <= x]])
  let h13 ← ar (← ExceptT.mk [[1 < p <=> 2 <= p]])
  let h12 ← ar (← ExceptT.mk [[2 <= p ==> 1 <= p]])
  let h11 ← ar (← ExceptT.mk [[2 <= p ==> 1 <= p]])
  let h10 ← rr
    (← ExceptT.mk [[&0 <= y * z /\ x * z <= a ==> (x - y) * z <= a]])
  let h9 ← ar (← ExceptT.mk [[2 <= p ==> ~(p = 1)]])
  let h8 ← ar (← ExceptT.mk [[1 <= k <=> ~(k = 0)]])
  let h7 ← ar (← ExceptT.mk [[k >= 2 ==> 1 <= k /\ 2 <= k]])
  let h6 ← rr (← ExceptT.mk [[&0 <= x /\ x <= y ==> abs(x) <= y]])
  let h5 ← ar (← ExceptT.mk [[k >= 1 <=> k >= 2 \/ k = 1]])
  let h4 ← ar (← ExceptT.mk [[~(1 >= 2)]])
  let h3 ← ar (← ExceptT.mk [[1 <= x <=> ~(x = 0)]])
  let h2 ← ar (← ExceptT.mk [[2 <= p ==> 1 <= p]])
  let h1 ← rr (← ExceptT.mk [[&0 <= x /\ x <= y ==> abs x <= abs y]])
  prove ([[!n s. s SUBSET (1..n)
         ==> abs (sum s (\d. mangoldt d / &d) -
                  sum {p | prime p /\ p IN s} (\p. log (&p) / &p)) <= &3]])
   (REPEAT GEN_TAC THEN ASM_CASES_TAC ([[n = 0]]) THENL
     [ASM_REWRITE_TAC [NUMSEG_CLAUSES, ARITH, SUBSET_EMPTY] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      REWRITE_TAC [NOT_IN_EMPTY, EMPTY_GSPEC, SUM_CLAUSES] THEN REAL_ARITH_TAC2,
      DISCH_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC ([[abs(sum (1..n) (\d. mangoldt d / &d) -
                    sum {p | prime p /\ p IN 1..n} (\p. log (&p) / &p))]]) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN ([[FINITE(s:num->bool)]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [FINITE_SUBSET, FINITE_NUMSEG], ALL_TAC] THEN
      ONCE_REWRITE_TAC [CONJ_SYM] THEN
      ASM_SIMP_TAC [SUM_RESTRICT_SET, FINITE_NUMSEG] THEN
      ASM_SIMP_TAC [(← HolLight.GSYM SUM_SUB), FINITE_NUMSEG] THEN
      MATCH_MP_TAC h1 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE, MATCH_MP_TAC SUM_SUBSET_SIMPLE] THEN
      ASM_SIMP_TAC [IN_DIFF, FINITE_NUMSEG, REAL_SUB_LE] THEN
      X_GEN_TAC ([[x:num]]) THEN STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC [REAL_LE_DIV, MANGOLDT_POS_LE, REAL_POS] THEN
      GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.LAND_CONV o HolLight.RAND_CONV)
        [(← HolLight.GSYM EXP_1)] THEN
      ASM_SIMP_TAC [MANGOLDT_PRIMEPOW, LE_REFL, REAL_LE_REFL],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[{p | prime p /\ p IN 1..n} = {p | prime p /\ p <= n}]])
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_NUMSEG] THEN
      MESON_TAC [h2, PRIME_GE_2],
      ALL_TAC] THEN
    SUBGOAL_THEN
     ([[sum(1..n) (\d. mangoldt d / &d) -
      sum {p | prime p /\ p <= n} (\p. log (&p) / &p) =
      sum {p EXP k | prime p /\ p EXP k <= n /\ k >= 2} (\d. mangoldt d / &d)]])
    SUBST1_TAC THENL
     [SUBGOAL_THEN
       ([[sum {p | prime p /\ p <= n} (\p. log (&p) / &p) =
        sum {p | prime p /\ p <= n} (\d. mangoldt d / &d)]])
      SUBST1_TAC THENL
       [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN
        GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.LAND_CONV o HolLight.RAND_CONV)
          [(← HolLight.GSYM EXP_1)] THEN
        ASM_SIMP_TAC [MANGOLDT_PRIMEPOW, ARITH],
        ALL_TAC] THEN
      REWRITE_TAC [REAL_EQ_SUB_RADD] THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC
       ([[sum {p EXP k | prime p /\ p EXP k <= n /\ k >= 1}
            (\d. mangoldt d / &d)]]) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_SUPERSET THEN
        SIMP_TAC [IN_ELIM_THM, SUBSET, IN_NUMSEG] THEN
        CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN
        ASM_REWRITE_TAC [h3, EXP_EQ_0] THENL
         [ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN
        REWRITE_TAC [real_div, REAL_ENTIRE] THEN DISJ1_TAC THEN
        REWRITE_TAC [mangoldt] THEN ASM_MESON_TAC [GE],
        ALL_TAC] THEN
      CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC SUM_UNION_EQ THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[0..n]]) THEN
        REWRITE_TAC [SUBSET, IN_ELIM_THM, FINITE_NUMSEG, IN_NUMSEG, LE_0] THEN
        MESON_TAC [],
        ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_INTER, IN_ELIM_THM, NOT_IN_EMPTY] THEN
        MESON_TAC [PRIME_EXP, h4],
        REWRITE_TAC [h5] THEN
        REWRITE_TAC [EXTENSION, IN_UNION, IN_ELIM_THM] THEN MESON_TAC [EXP_1]],
      ALL_TAC] THEN
    MATCH_MP_TAC h6 THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN
      SIMP_TAC [REAL_LE_DIV, REAL_POS, MANGOLDT_POS_LE] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[0..n]]) THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM, FINITE_NUMSEG, IN_NUMSEG, LE_0] THEN
      MESON_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     ([[sum {p | p IN 1..n /\ prime p}
          (\p. sum (2..n) (\k. log(&p) / &p pow k))]]) THEN
    CONJ_TAC THENL
     [SIMP_TAC [SUM_SUM_PRODUCT, FINITE_NUMSEG, FINITE_RESTRICT] THEN
      MATCH_MP_TAC SUM_LE_INCLUDED THEN EXISTS_TAC ([[\(p,k). p EXP k]]) THEN
      SIMP_TAC [FINITE_PRODUCT, FINITE_NUMSEG, FINITE_RESTRICT] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[0..n]]) THEN
        REWRITE_TAC [SUBSET, IN_ELIM_THM, FINITE_NUMSEG, IN_NUMSEG, LE_0] THEN
        MESON_TAC [],
        ALL_TAC] THEN
      REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_PAIR_THM, EXISTS_PAIR_THM] THEN
      SIMP_TAC [IN_ELIM_THM, IN_NUMSEG, REAL_LE_DIV, REAL_POW_LE, REAL_POS,
               LOG_POS, REAL_OF_NUM_LE] THEN
      X_GEN_TAC ([[x:num]]) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[p:num]]) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[k:num]]) THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_SIMP_TAC [MANGOLDT_PRIMEPOW, (← HolLight.GSYM REAL_OF_NUM_POW), REAL_LE_REFL,
                   h7] THEN
      ASM_SIMP_TAC [PRIME_IMP_NZ, h8] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC ([[p EXP k]]) THEN ASM_SIMP_TAC [] THEN
        GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM EXP_1)] THEN
        ASM_SIMP_TAC [PRIME_IMP_NZ, LE_EXP] THEN ASM_ARITH_TAC,
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC ([[p EXP k]]) THEN ASM_SIMP_TAC [] THEN
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC ([[2 EXP k]]) THEN
        ASM_SIMP_TAC [LT_POW2_REFL, LT_IMP_LE, EXP_MONO_LE, PRIME_GE_2]],
      ALL_TAC] THEN
    REWRITE_TAC [real_div, SUM_LMUL, (← HolLight.GSYM REAL_POW_INV), SUM_GP] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC ([[sum {p | p IN 1..n /\ prime p}
                    (\p. log(&p) / (&p * (&p - &1)))]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN SIMP_TAC [FINITE_NUMSEG, FINITE_RESTRICT] THEN
      X_GEN_TAC ([[p:num]]) THEN REWRITE_TAC [IN_ELIM_THM, IN_NUMSEG] THEN
      ASM_SIMP_TAC [REAL_INV_EQ_1, REAL_OF_NUM_EQ, PRIME_GE_2,
                   h9] THEN
      STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC [REAL_MUL_RZERO, REAL_LE_DIV, REAL_LE_MUL, REAL_SUB_LE,
                   REAL_OF_NUM_LE, LOG_POS, LE_0] THEN
      REWRITE_TAC [real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC [LOG_POS, REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC h10 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC [REAL_POW_LE, REAL_LE_INV_EQ, REAL_POS, REAL_SUB_LE] THEN
        MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC [REAL_OF_NUM_LE],
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP PRIME_GE_2) THEN
      REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_LE)] THEN CONV_TAC REAL_FIELD,
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC ([[sum (2..n)  (\p. log(&p) / (&p * (&p - &1)))]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET THEN SIMP_TAC [FINITE_NUMSEG, FINITE_RESTRICT] THEN
      REWRITE_TAC [IN_DIFF, IN_NUMSEG, IN_ELIM_THM] THEN
      CONJ_TAC THENL [MESON_TAC [PRIME_GE_2], ALL_TAC] THEN
      ASM_SIMP_TAC [LOG_POS, REAL_OF_NUM_LE, h11,
                   REAL_LE_MUL, REAL_POS, REAL_SUB_LE, REAL_LE_DIV],
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC ([[sum (2..n) (\m. log(&m) / (&m - &1) pow 2)]]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC [real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC [LOG_POS, REAL_OF_NUM_LE, h12] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_SIMP_TAC [REAL_POW_2, REAL_LE_RMUL_EQ, REAL_LT_MUL, REAL_LT_IMP_LE,
                   REAL_SUB_LT, REAL_OF_NUM_LT, h13,
                   h14],
      ALL_TAC] THEN
    ASM_CASES_TAC ([[n < 2]]) THENL
     [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [(← HolLight.GSYM NUMSEG_EMPTY)]),
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [NOT_LT])] THEN
    ASM_SIMP_TAC [SUM_CLAUSES] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC [SUM_CLAUSES_LEFT, ARITH] THEN
    MATCH_MP_TAC h15 THEN
    CONJ_TAC THENL [MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC2, ALL_TAC] THEN
    ASM_CASES_TAC ([[n < 3]]) THENL
     [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [(← HolLight.GSYM NUMSEG_EMPTY)]),
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [NOT_LT])] THEN
    ASM_SIMP_TAC [SUM_CLAUSES] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MP_TAC (← HolLight.ISPECL
     [([[\z. clog(z) / (z - Cx(&1)) pow 2]]),
      ([[\z. clog(z - Cx(&1)) - clog(z) - clog(z) / (z - Cx(&1))]]),
      ([[3]]), ([[n:num]])] SUM_INTEGRAL_UBOUND_DECREASING) THEN
    ASM_REWRITE_TAC [] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC [IN_SEGMENT_CX_GEN] THEN X_GEN_TAC ([[z:complex]]) THEN
        STRIP_TAC THENL
         [COMPLEX_DIFF_TAC THEN SIMP_TAC [COMPLEX_SUB_RZERO, COMPLEX_MUL_LID] THEN
          ASM_SIMP_TAC [RE_SUB, RE_CX, REAL_SUB_LT] THEN
          ASM_SIMP_TAC [h16] THEN
          SUBGOAL_THEN ([[~(z = Cx(&0)) /\ ~(z = Cx(&1))]]) MP_TAC THENL
           [ALL_TAC, CONV_TAC COMPLEX_FIELD] THEN
          REPEAT STRIP_TAC THEN UNDISCH_TAC ([[&2 <= Re z]]) THEN
          ASM_REWRITE_TAC [RE_CX] THEN REAL_ARITH_TAC2,
          RULE_ASSUM_TAC (HolLight.REWRITE_RULE [(← HolLight.GSYM REAL_OF_NUM_LE)]) THEN
          ASM_ARITH_TAC],
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [([[x:real]]), ([[y:real]])] THEN STRIP_TAC THEN
      MP_TAC (← HolLight.SPECL [([[\z. clog(z) / (z - Cx(&1)) pow 2]]),
                    ([[\z. inv(z * (z - Cx(&1)) pow 2) -
                         Cx(&2) * clog(z) / (z - Cx(&1)) pow 3]]),
                    ([[Cx(x)]]), ([[Cx(y)]])] COMPLEX_MVT_LINE) THEN
      REWRITE_TAC [] THEN ANTS_TAC THENL
       [REWRITE_TAC [IN_SEGMENT_CX_GEN] THEN X_GEN_TAC ([[z:complex]]) THEN
        REWRITE_TAC [h17] THEN
        STRIP_TAC THENL [ALL_TAC, ASM_REAL_ARITH_TAC] THEN
        COMPLEX_DIFF_TAC THEN REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC)] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        SUBGOAL_THEN ([[~(z = Cx(&0)) /\ ~(z = Cx(&1))]]) MP_TAC THENL
         [ALL_TAC, CONV_TAC COMPLEX_FIELD] THEN
        CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
        REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [RE_CX, IM_CX] THEN
        REAL_ARITH_TAC2,
        ALL_TAC] THEN
      GEN_REWRITE_TAC HolLight.RAND_CONV [h18] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[w:complex]])
       (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
      REWRITE_TAC [(← HolLight.GSYM CX_SUB), RE_MUL_CX] THEN
      REWRITE_TAC [h19] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC [REAL_SUB_LE] THEN
      REWRITE_TAC [RE_SUB, REAL_NEG_SUB, REAL_SUB_LE] THEN
      SUBGOAL_THEN ([[real w]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [REAL_SEGMENT, REAL_CX], ALL_TAC] THEN
      FIRST_X_ASSUM (SUBST_ALL_TAC o HolLight.SYM o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [REAL]) THEN
      ABBREV_TAC ([[u = Re w]]) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [IN_SEGMENT_CX]) THEN
      ASM_SIMP_TAC [h20] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN ([[&0 < u /\ &1 < u /\ &2 <= u]]) STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      ASM_SIMP_TAC [(← HolLight.GSYM CX_LOG), (← HolLight.GSYM CX_SUB), (← HolLight.GSYM CX_POW),
                   (← HolLight.GSYM CX_DIV), (← HolLight.GSYM CX_MUL), (← HolLight.GSYM CX_INV),
                   RE_CX] THEN
      REWRITE_TAC [REAL_POW_2, real_div, REAL_INV_MUL, REAL_MUL_ASSOC,
                  h21] THEN
      ASM_SIMP_TAC [REAL_LE_RMUL_EQ, REAL_LT_INV_EQ, REAL_SUB_LT] THEN
      ASM_SIMP_TAC [(← HolLight.GSYM real_div), REAL_LE_RDIV_EQ, REAL_SUB_LT] THEN
      MATCH_MP_TAC h22 THEN
      ASM_SIMP_TAC [(← HolLight.GSYM real_div), REAL_LE_LDIV_EQ] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC ([[log(&2)]]) THEN
      REWRITE_TAC [LOG_2_BOUNDS] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC h23 THEN
    CONJ_TAC THENL [MATCH_MP_TAC SUM_EQ_NUMSEG, ALL_TAC] THEN
    ASM_SIMP_TAC [(← HolLight.GSYM CX_SUB), (← HolLight.GSYM CX_LOG), (← HolLight.GSYM CX_DIV),
        REAL_SUB_LT, ARITH,
        RE_CX, REAL_OF_NUM_LT, h24,
        (← HolLight.GSYM CX_POW)] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [LOG_1, h25] THEN
    MATCH_MP_TAC h26 THEN
    REWRITE_TAC [LOG_2_BOUNDS] THEN
    MATCH_MP_TAC h27 THEN
    REWRITE_TAC [REAL_SUB_REFL, h28] THEN
    ASM_SIMP_TAC [REAL_LE_DIV, REAL_SUB_LE, LOG_POS, REAL_OF_NUM_LE,
      REAL_OF_NUM_LT, LOG_MONO_LE_IMP, h29, REAL_SUB_LT,
      LE_0, h30])
  : ExceptT String IO thm).run
#eval MERTENS_MANGOLDT_VERSUS_LOG

#eval phrase 20
def MERTENS : thm := keep "MERTENS" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[2 <= p ==> 1 <= p]])
  let h1 ← rr
    (← ExceptT.mk [[abs(s1 - s2) <= k - e ==> abs(s1 - l) <= e ==> abs(s2 - l) <= k]])
  prove ([[!n. ~(n = 0)
       ==> abs(sum {p | prime p /\ p <= n}
                   (\p. log(&p) / &p) - log(&n)) <= &24]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP MERTENS_LEMMA) THEN
    MATCH_MP_TAC h1 THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SUBGOAL_THEN ([[{p | prime p /\ p <= n} = {p | prime p /\ p IN 1..n}]])
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_NUMSEG] THEN
      MESON_TAC [h2, PRIME_GE_2],
      MATCH_MP_TAC MERTENS_MANGOLDT_VERSUS_LOG THEN
      EXISTS_TAC ([[n:num]]) THEN ASM_REWRITE_TAC [SUBSET_REFL]])
  : ExceptT String IO thm).run
#eval MERTENS

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean).  Generated by
    tools/tutorialdiff/ensuregen.py; keep it in step with the `#eval`s above. -/
def ensure : IO Unit := once "HolExamples.Mangoldt" do
  replay (
          SessionLibrary.Pocklington.ensurePocklington)
  replay (
          SessionMultiLib.Transcendentals.ensureTranscendentals)
  replay (
          Session.prioritize_real)
  replay (
          LOG_FACT)
  replay (
          SUM_DIVISORS_FLOOR_LEMMA)
  replay (
          LOG_2_BOUNDS)
  replay (
          LOG_LE_REFL)
  replay (
          LOG_FACT_BOUNDS)
  replay (
          mangoldt)
  replay (
          MANGOLDT_1)
  replay (
          MANGOLDT_PRIMEPOW)
  replay (
          MANGOLDT_POS_LE)
  replay (
          LOG_MANGOLDT_SUM)
  replay (
          MANGOLDT)
  replay (
          PSI_BOUND_INDUCT)
  replay (
          PSI_BOUND_EXP)
  replay (
          PSI_BOUND)
  replay (
          MERTENS_LEMMA)
  replay (
          MERTENS_MANGOLDT_VERSUS_LOG)
  replay (
          MERTENS)
-- @@ENSURE END

end HolExamples.Mangoldt
