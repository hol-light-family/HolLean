/- File: HolExamples/Misiurewicz.lean
Translation of HOL Light's Examples/misiurewicz.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
import SessionMultiLib.Cauchy
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionLibrary.Card SessionLibrary.Floor SessionLibrary.Iter
open SessionMultiLib.Misc SessionMultiLib.Vectors SessionMultiLib.Determinants
open SessionMultiLib.Metric SessionMultiLib.Topology SessionMultiLib.Convex
open SessionMultiLib.Paths SessionMultiLib.Integration
open SessionMultiLib.ComplexAlgebra SessionMultiLib.Complexes SessionMultiLib.Canal SessionMultiLib.Transcendentals
open SessionMultiLib.RealAnalysis SessionMultiLib.MoreTop SessionMultiLib.Cauchy
namespace HolExamples.Misiurewicz

/- Helpers: the session's `prove` lifted into `ExceptT String IO`, so tactic
   scripts read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def rf (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_FIELD tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def na (tm : term) : ExceptT String IO thm := ExceptT.mk (NORM_ARITH tm)
private def cr (tm : term) : ExceptT String IO thm := ExceptT.mk (COMPLEX_RING tm)
private def ms (ths : List thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (MESON ths tm)
/- `ttac o check p o concl`: apply `ttac` to a theorem whose conclusion
   satisfies `p`, otherwise fail. -/
private def ifConcl (p : term → Bool) (ttac : thm → HolCore.Tactics.tactic) :
    thm → HolCore.Tactics.tactic :=
  fun th g => if p (concl th) then ttac th g else return .error "check"

-- ========================================================================= --
-- Proof that the complex exponential map is topologically transitive,       --
-- following Misiurewicz's original paper "On iterates of e^z".              --
-- Suggestion of problem and additional advice from Lasse Rempe-Gillen.      --
-- ========================================================================= --

#eval phrase 1
-- needs "Multivariate/cauchy.ml";;
#eval SessionMultiLib.Cauchy.ensureCauchy

-- ------------------------------------------------------------------------- --
-- Some preliminaries.                                                       --
-- ------------------------------------------------------------------------- --

#eval phrase 2
def HAS_COMPLEX_DERIVATIVE_CEXP_COMPOSE : thm := keep "HAS_COMPLEX_DERIVATIVE_CEXP_COMPOSE" fun _ => (do
  prove ([[!f z. (f has_complex_derivative f') (at z)
         ==> ((\w. cexp(f w)) has_complex_derivative (f' * cexp(f z))) (at z)]])
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [(← HolLight.GSYM o_DEF)] THEN
    ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN
    MATCH_MP_TAC COMPLEX_DIFF_CHAIN_AT THEN ASM_REWRITE_TAC [] THEN
    GEN_REWRITE_TAC (HolLight.RATOR_CONV o HolLight.LAND_CONV) [(← HolLight.GSYM ETA_AX)] THEN
    COMPLEX_DIFF_TAC THEN REWRITE_TAC [COMPLEX_MUL_LID])
  : ExceptT String IO thm).run
#eval HAS_COMPLEX_DERIVATIVE_CEXP_COMPOSE

#eval phrase 3
def COMPLEX_DIFFERENTIABLE_CEXP_COMPOSE : thm := keep "COMPLEX_DIFFERENTIABLE_CEXP_COMPOSE" fun _ => (do
  prove ([[!f z. f complex_differentiable at z
         ==> (\w. cexp(f w)) complex_differentiable at z]])
   (MESON_TAC [complex_differentiable, HAS_COMPLEX_DERIVATIVE_CEXP_COMPOSE])
  : ExceptT String IO thm).run
#eval COMPLEX_DIFFERENTIABLE_CEXP_COMPOSE

#eval phrase 4
def COMPLEX_DERIVATIVE_CEXP_COMPOSE : thm := keep "COMPLEX_DERIVATIVE_CEXP_COMPOSE" fun _ => (do
  prove ([[!f z. f complex_differentiable at z
         ==> complex_derivative (\w. cexp(f w)) z =
             complex_derivative f z * cexp(f z)]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_CEXP_COMPOSE THEN
    ASM_REWRITE_TAC [HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE])
  : ExceptT String IO thm).run
#eval COMPLEX_DERIVATIVE_CEXP_COMPOSE

#eval phrase 5
def COMPLEX_DIFFERENTIABLE_ITER_CEXP : thm := keep "COMPLEX_DIFFERENTIABLE_ITER_CEXP" fun _ => (do
  prove ([[!n z. (ITER n cexp) complex_differentiable at z]])
   (GEN_REWRITE_TAC (HolCore.Lib.funpow 2 HolLight.BINDER_CONV o HolLight.LAND_CONV)
      [(← HolLight.GSYM ETA_AX)] THEN
    INDUCT_TAC THEN ASM_SIMP_TAC [ITER, COMPLEX_DIFFERENTIABLE_ID] THEN
    ASM_SIMP_TAC [COMPLEX_DIFFERENTIABLE_CEXP_COMPOSE])
  : ExceptT String IO thm).run
#eval COMPLEX_DIFFERENTIABLE_ITER_CEXP

#eval phrase 6
def CONTINUOUS_ITER_CEXP : thm := keep "CONTINUOUS_ITER_CEXP" fun _ => (do
  prove ([[!n z. (ITER n cexp) continuous at z]])
   (SIMP_TAC [COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT,
             COMPLEX_DIFFERENTIABLE_ITER_CEXP])
  : ExceptT String IO thm).run
#eval CONTINUOUS_ITER_CEXP

#eval phrase 7
def HOLOMORPHIC_ON_ITER_CEXP : thm := keep "HOLOMORPHIC_ON_ITER_CEXP" fun _ => (do
  prove ([[!n s. (ITER n cexp) holomorphic_on s]])
   (SIMP_TAC [HOLOMORPHIC_ON_DIFFERENTIABLE, COMPLEX_DIFFERENTIABLE_AT_WITHIN,
             COMPLEX_DIFFERENTIABLE_ITER_CEXP])
  : ExceptT String IO thm).run
#eval HOLOMORPHIC_ON_ITER_CEXP

#eval phrase 8
def CONTINUOUS_ON_ITER_CEXP : thm := keep "CONTINUOUS_ON_ITER_CEXP" fun _ => (do
  prove ([[!n s. (ITER n cexp) continuous_on s]])
   (SIMP_TAC [HOLOMORPHIC_ON_IMP_CONTINUOUS_ON, HOLOMORPHIC_ON_ITER_CEXP])
  : ExceptT String IO thm).run
#eval CONTINUOUS_ON_ITER_CEXP

-- ------------------------------------------------------------------------- --
-- Lemma 1.                                                                  --
-- ------------------------------------------------------------------------- --

#eval phrase 9
def LEMMA_1 : thm := keep "LEMMA_1" fun _ => (do
  prove ([[!n z. 1 <= n
         ==> abs(Im(ITER n cexp z)) <= norm(complex_derivative(ITER n cexp) z)]])
   (INDUCT_TAC THEN REWRITE_TAC [ITER, ARITH] THEN
    X_GEN_TAC ([[z:complex]]) THEN DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
    GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV o HolLight.LAND_CONV)
      [(← HolLight.GSYM ETA_AX)] THEN
    REWRITE_TAC [ITER] THEN
    ASM_SIMP_TAC [COMPLEX_DERIVATIVE_CEXP_COMPOSE,
                 COMPLEX_DIFFERENTIABLE_ITER_CEXP, ETA_AX] THEN
    ASM_CASES_TAC ([[n = 0]]) THEN
    ASM_REWRITE_TAC [ITER_POINTLESS, I_DEF, o_DEF, COMPLEX_DERIVATIVE_ID,
                    COMPLEX_MUL_LID, COMPLEX_NORM_GE_RE_IM] THEN
    TRANS_TAC REAL_LE_TRANS
     ([[abs(Im(ITER n cexp z)) * norm(cexp (ITER n cexp z))]]) THEN
    ASM_SIMP_TAC [COMPLEX_NORM_MUL, REAL_LE_RMUL, NORM_POS_LE, LE_1] THEN
    SPEC_TAC (([[ITER n cexp z]]), ([[w:complex]])) THEN
    POP_ASSUM_LIST (HolCore.Lib.K ALL_TAC) THEN
    GEN_TAC THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    REWRITE_TAC [IM_CEXP, NORM_CEXP, REAL_ABS_MUL, REAL_ABS_EXP] THEN
    SIMP_TAC [REAL_LE_LMUL_EQ, REAL_EXP_POS_LT, REAL_ABS_SIN_BOUND_LE])
  : ExceptT String IO thm).run
#eval LEMMA_1

-- ------------------------------------------------------------------------- --
-- Lemma 2 (two parts)                                                       --
-- ------------------------------------------------------------------------- --

#eval phrase 10
def LEMMA_2a : thm := keep "LEMMA_2a" fun _ => (do
  -- OCaml builds the tactic right to left: the build-time rules run
  -- bottom-first, so their traces print in that order.
  let h2 ← rr
    (← ExceptT.mk [[(x + l) + &1 - l <= (e * &2) / &2 <=> &1 + x <= e]])
  let h1 ← rr
    (← ExceptT.mk [[z - l:real = x ==> z = x + l]])
  prove ([[!z. abs(Im z) <= pi / &3 ==> Re(cexp z) >= Re z + (&1 - log(&2))]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [RE_CEXP, real_ge] THEN
    TRANS_TAC REAL_LE_TRANS ([[exp(Re z) / &2]]) THEN CONJ_TAC THENL
     [ALL_TAC,
      SIMP_TAC [real_div, REAL_LE_LMUL_EQ, REAL_EXP_POS_LT] THEN
      MP_TAC (← HolLight.ISPECL [([[pi / &3]]), ([[abs(Im z)]])] COS_MONO_LE_EQ) THEN
      ASM_REWRITE_TAC [COS_ABS] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ] REAL_LE_TRANS) THEN
      REWRITE_TAC [COS_PI3] THEN CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    ABBREV_TAC ([[x = Re z - log(&2)]]) THEN
    FIRST_ASSUM (SUBST1_TAC o HolLight.MATCH_MP h1) THEN
    SIMP_TAC [REAL_EXP_ADD, EXP_LOG, REAL_OF_NUM_LT, ARITH] THEN
    REWRITE_TAC [REAL_EXP_LE_X, h2])
  : ExceptT String IO thm).run
#eval LEMMA_2a

#eval phrase 11
def LEMMA_2b : thm := keep "LEMMA_2b" fun _ => (do
  let h12 ← rr
    (← ExceptT.mk [[m * a <= b ==> c >= &2 * b  ==> (&2 * m) * a <= c]])
  let h11 ← rr
    (← ExceptT.mk [[p < x ==> x <= a ==> a <= p ==> F]])
  let h10 ← rr
    (← ExceptT.mk [[z + m * l <= n ==> s >= n + l ==> z + (m + &1) * l <= s]])
  let h9 ← rr (← ExceptT.mk [[&0 < &5]])
  let h8 ← rr
    (← ExceptT.mk [[&5 * b <= u * v ==> x >= (&2 / &5 * u) * v ==> x >= &2 * b]])
  let h7 ← rr
    (← ExceptT.mk [[(pi / &3) pow 2 <= a <=> pi pow 2 <= &9 * a]])
  let h6 ← rr
    (← ExceptT.mk [[x pow 3 / &2 <= a * x <=> x * x pow 2 <= x * &2 * a]])
  let h5 ← rr
    (← ExceptT.mk [[e <= (&1 - a) * x ==> abs(sin x - x / &1) <= e ==> a * x <= sin x]])
  let h4 ← rr
    (← ExceptT.mk [[&0 <= x /\ x <= pi / &3 ==> x <= pi]])
  let h3 ← ms [REAL_LE_NEGTOTAL]
    (← ExceptT.mk [[(!x. P(--x) <=> P x) /\ (!x. &0 <= x ==> P x) ==> !x. P x]])
  let h2 ← rr (← ExceptT.mk [[e * x >= (y * e) * z <=> e * y * z <= e * x]])
  let h1 ← ms [] (← ExceptT.mk [[(?n. P n) <=> (!n. ~P n) ==> F]])
  prove ([[!z. ~(real z) ==> ?n. abs(Im(ITER n cexp z)) > pi / &3]])
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [h1] THEN
    REWRITE_TAC [real_gt, REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     ([[!n. abs(Im(ITER (n + 1) cexp z)) >=
          (&2 / &5 * exp(Re(ITER n cexp z))) * abs(Im(ITER n cexp z))]])
    (LABEL_TAC "*") THENL
     [REPEAT GEN_TAC THEN
      REWRITE_TAC [ITER, (← HolLight.GSYM ADD1), IM_CEXP, REAL_ABS_EXP, REAL_ABS_MUL] THEN
      REWRITE_TAC [h2] THEN
      SIMP_TAC [REAL_LE_LMUL_EQ, REAL_EXP_POS_LT] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[n:num]])) THEN
      SPEC_TAC (([[Im(ITER n cexp z)]]), ([[x:real]])) THEN
      MATCH_MP_TAC h3 THEN
      REWRITE_TAC [SIN_NEG, REAL_ABS_NEG] THEN
      SIMP_TAC [real_abs, SIN_POS_PI_LE, h4] THEN
      REPEAT STRIP_TAC THEN MP_TAC (← HolLight.SPECL [([[0]]), ([[Cx x]])] TAYLOR_CSIN) THEN
      REWRITE_TAC [VSUM_SING_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC [IM_CX, REAL_ABS_NUM, REAL_EXP_0, (← HolLight.GSYM CX_SIN)] THEN
      REWRITE_TAC [complex_pow, COMPLEX_POW_1] THEN
      REWRITE_TAC [(← HolLight.GSYM CX_DIV), (← HolLight.GSYM CX_POW), (← HolLight.GSYM CX_MUL),
                  (← HolLight.GSYM CX_SUB), (← HolLight.GSYM CX_ADD), (← HolLight.GSYM CX_NEG),
                  COMPLEX_NORM_CX, REAL_MUL_LID] THEN
      MATCH_MP_TAC h5 THEN
      ASM_SIMP_TAC [real_abs, h6] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC [] THEN
      TRANS_TAC REAL_LE_TRANS ([[(pi / &3) pow 2]]) THEN
      ASM_SIMP_TAC [REAL_POW_LE2, h7] THEN
      TRANS_TAC REAL_LE_TRANS ([[(&16 / &5) pow 2]]) THEN
      CONJ_TAC THENL [ALL_TAC, CONV_TAC REAL_RAT_REDUCE_CONV] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!n. &0 < abs(Im(ITER n cexp z))]]) ASSUME_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM REAL_ABS_NZ)] THEN
      INDUCT_TAC THENL [ASM_MESON_TAC [ITER, real], ALL_TAC] THEN
      REMOVE_THEN "*" (MP_TAC o HolLight.SPEC ([[n:num]])) THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM CONTRAPOS_THM)] THEN
      SIMP_TAC [ADD1, real_ge, REAL_NOT_LE, REAL_ABS_NUM] THEN DISCH_TAC THEN
      REPEAT (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM REAL_ABS_NZ), REAL_EXP_POS_LT] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV,
      ALL_TAC] THEN
    SUBGOAL_THEN
     ([[?N. !n. N <= n
              ==> abs(Im(ITER (n + 1) cexp z)) >= &2 * abs(Im(ITER n cexp z))]])
    CHOOSE_TAC THENL
     [MP_TAC (← HolLight.ISPEC ([[&1 - log(&2)]]) REAL_ARCH) THEN ANTS_TAC THENL
       [MP_TAC LOG2_APPROX_32 THEN REAL_ARITH_TAC2, ALL_TAC] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[log(&5) - Re z]])) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[N:num]]) THEN DISCH_TAC THEN
      X_GEN_TAC ([[n:num]]) THEN DISCH_TAC THEN
      REMOVE_THEN "*" (MP_TAC o HolLight.SPEC ([[n:num]])) THEN MATCH_MP_TAC h8 THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [REAL_ABS_POS] THEN
      ONCE_REWRITE_TAC [(← HolLight.SYM (← HolLight.MATCH_MP EXP_LOG
        h9))] THEN
      REWRITE_TAC [REAL_EXP_MONO_LE] THEN
      TRANS_TAC REAL_LE_TRANS ([[Re z + &N * (&1 - log(&2))]]) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      TRANS_TAC REAL_LE_TRANS ([[Re z + &n * (&1 - log(&2))]]) THEN CONJ_TAC THENL
       [REWRITE_TAC [REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC [REAL_OF_NUM_LE] THEN MP_TAC LOG2_APPROX_32 THEN
        REAL_ARITH_TAC2,
        ALL_TAC] THEN
      SPEC_TAC (([[n:num]]), ([[m:num]])) THEN INDUCT_TAC THENL
       [REWRITE_TAC [ITER, REAL_MUL_LZERO, REAL_ADD_RID, REAL_LE_REFL],
        REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_SUC)]] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h10) THEN
      REWRITE_TAC [ITER] THEN MATCH_MP_TAC LEMMA_2a THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    UNDISCH_TAC ([[!n. abs(Im(ITER n cexp z)) <= pi / &3]]) THEN
    MP_TAC (← HolLight.SPECL [([[&2]]), ([[pi / &3 / abs(Im (ITER N cexp z))]])]
          REAL_ARCH_POW) THEN
    ASM_SIMP_TAC [REAL_LT_LDIV_EQ] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN (X_CHOOSE_TAC ([[d:num]])) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[N + d:num]])) THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h11) THEN
    SPEC_TAC (([[d:num]]), ([[m:num]])) THEN INDUCT_TAC THEN
    REWRITE_TAC [ADD_CLAUSES, real_pow, REAL_MUL_LID, REAL_LE_REFL] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h12) THEN
    REWRITE_TAC [ADD1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [LE_ADD])
  : ExceptT String IO thm).run
#eval LEMMA_2b

-- ------------------------------------------------------------------------- --
-- Lemma 3.                                                                  --
-- ------------------------------------------------------------------------- --

#eval phrase 12
def LEMMA_3 : thm := keep "LEMMA_3" fun _ => (do
  let h11 ← cr (← ExceptT.mk [[a * b = Cx(&1) ==> ~(a = Cx(&0))]])
  let h10 ← rr (← ExceptT.mk [[n * r / s:real = (r * n) / s]])
  let h9 ← sr
    (← ExceptT.mk [[t SUBSET IMAGE f s
    ==> (!x. x IN s ==> P(f x)) ==> !x. x IN t ==> P x]])
  let h8 ← rr (← ExceptT.mk [[t / s * r:real = r / s * t]])
  let h7 ← na
    (← ExceptT.mk [[s <= t ==> norm(w - b) <= s ==> dist(b,w) <= t]])
  let h6 ← sr
    (← ExceptT.mk [[x IN s ==> s SUBSET t ==> x IN t]])
  let h5 ← sr (← ExceptT.mk [[s SUBSET t ==> t INTER s = s]])
  let h4 ← sr
    (← ExceptT.mk [[~(y IN IMAGE f s) ==> x IN s ==> ~(f x = y)]])
  let h3 ← tt (← ExceptT.mk [[F ==> p]])
  let h2 ← sr (← ExceptT.mk [[UNIV DIFF s = {} <=> s = UNIV]])
  let h1 ← rr (← ExceptT.mk [[s <= &0 \/ &0 < s]])
  prove ([[!n b r s.
        &0 < r /\
        (!w z. w IN ball(b,r) /\ z IN ball(b,r) /\
               ITER n cexp w = ITER n cexp z
               ==> w = z) /\
        (!z. z IN ball(b,r)
             ==> s <= r * norm(complex_derivative (ITER n cexp) z))
        ==> ball(ITER n cexp b,s) SUBSET IMAGE (ITER n cexp) (ball(b,r))]])
   (REPEAT GEN_TAC THEN
    DISJ_CASES_TAC h1 THENL
     [ASM_MESON_TAC [BALL_EQ_EMPTY, EMPTY_SUBSET], ALL_TAC] THEN
    MP_TAC (← HolLight.ISPEC ([[n:num]]) COMPLEX_DIFFERENTIABLE_ITER_CEXP) THEN
    SPEC_TAC (([[ITER n cexp]]), ([[f:complex->complex]])) THEN
    REWRITE_TAC [INJECTIVE_ON_ALT] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[f:complex->complex]]), ([[ball(b:complex,r)]])]
          HOLOMORPHIC_ON_INVERSE) THEN
    ASM_REWRITE_TAC [INJECTIVE_ON_ALT, OPEN_BALL] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC [HOLOMORPHIC_ON_DIFFERENTIABLE,
                   COMPLEX_DIFFERENTIABLE_AT_WITHIN],
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN ([[g:complex->complex]]) STRIP_ASSUME_TAC))] THEN
    ABBREV_TAC
     ([[c = closest_point ((:complex) DIFF IMAGE f (ball(b:complex,r))) (f b)]]) THEN
    MP_TAC (← HolLight.ISPECL [([[(:complex) DIFF IMAGE f (ball(b:complex,r))]]),
                   ([[(f:complex->complex) b]])]
          CLOSEST_POINT_EXISTS) THEN
    ASM_REWRITE_TAC [(← HolLight.GSYM OPEN_CLOSED), IN_DIFF, IN_UNIV] THEN ANTS_TAC THENL
     [REWRITE_TAC [h2] THEN
      DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[bounded:(complex->bool)->bool]])) THEN
      REWRITE_TAC [NOT_BOUNDED_UNIV] THEN
      MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC ([[IMAGE (f:complex->complex) (cball(b,r))]]) THEN
      SIMP_TAC [IMAGE_SUBSET, BALL_SUBSET_CBALL] THEN
      MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC [COMPACT_CBALL] THEN
      ASM_SIMP_TAC [HOLOMORPHIC_ON_DIFFERENTIABLE,
                   HOLOMORPHIC_ON_IMP_CONTINUOUS_ON,
                   COMPLEX_DIFFERENTIABLE_AT_WITHIN],
      GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV o HolLight.BINDER_CONV)
       [(← HolLight.GSYM CONTRAPOS_THM)] THEN
      REWRITE_TAC [(← HolLight.GSYM IN_BALL), REAL_NOT_LE, (← HolLight.GSYM SUBSET)]] THEN
    ABBREV_TAC ([[t = dist((f:complex->complex) b,c)]]) THEN STRIP_TAC THEN
    ASM_CASES_TAC ([[s:real <= t]]) THENL
     [ASM_MESON_TAC [SUBSET_BALL, SUBSET_TRANS], ALL_TAC] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [REAL_NOT_LE]) THEN
    MATCH_MP_TAC h3 THEN
    SUBGOAL_THEN ([[&0 < t]]) ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN REWRITE_TAC [(← HolLight.GSYM DIST_NZ)] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h4) THEN
      ASM_REWRITE_TAC [CENTRE_IN_BALL],
      ALL_TAC] THEN
    SUBGOAL_THEN
     ([[c IN closure(IMAGE (f:complex->complex) (ball (b,r)) INTER
                   ball(f b,t))]])
    MP_TAC THENL
     [ASM_SIMP_TAC [h5] THEN
      ASM_SIMP_TAC [CLOSURE_BALL] THEN
      ASM_REWRITE_TAC [IN_CBALL, REAL_LE_REFL],
      REWRITE_TAC [CLOSURE_SEQUENTIAL]] THEN
    REWRITE_TAC [IN_IMAGE, IN_INTER, SKOLEM_THM, FORALL_AND_THM] THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM FUN_EQ_THM)] THEN
    REWRITE_TAC [ETA_AX, LEFT_AND_EXISTS_THM, (← HolLight.GSYM CONJ_ASSOC)] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN REWRITE_TAC [UNWIND_THM2] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[z:num->complex]]) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     ([[!n. (z:num->complex) n IN cball(b,t / s * r)]])
    ASSUME_TAC THENL
     [ALL_TAC,
      MP_TAC (← HolLight.ISPEC ([[cball(b:complex,t / s * r)]]) compact) THEN
      REWRITE_TAC [COMPACT_CBALL] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[z:num->complex]])) THEN
      ASM_REWRITE_TAC [NOT_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[w:complex]]), ([[r:num->num]])] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolLight.RAND_CONV [IN_IMAGE]) THEN
      REWRITE_TAC [] THEN EXISTS_TAC ([[w:complex]]) THEN CONJ_TAC THENL
       [MATCH_MP_TAC (← HolLight.ISPEC ([[sequentially]]) LIM_UNIQUE) THEN
        EXISTS_TAC ([[(f:complex->complex) o z o (r:num->num)]]) THEN
        REWRITE_TAC [TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
         [REWRITE_TAC [o_ASSOC] THEN MATCH_MP_TAC LIM_SUBSEQUENCE THEN
          ASM_REWRITE_TAC [o_DEF],
          MP_TAC (← HolLight.ISPECL [([[f:complex->complex]]), ([[sequentially]])]
            LIM_CONTINUOUS_FUNCTION) THEN
          REWRITE_TAC [o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
          ASM_REWRITE_TAC [(← HolLight.GSYM o_DEF)] THEN
          ASM_SIMP_TAC [COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT]],
        FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h6) THEN
        REWRITE_TAC [SUBSET_BALLS, DIST_REFL, REAL_ADD_LID] THEN
        DISJ1_TAC THEN GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM REAL_MUL_LID)] THEN
        ASM_SIMP_TAC [REAL_LT_RMUL_EQ, REAL_LT_LDIV_EQ, REAL_MUL_LID]]] THEN
    UNDISCH_TAC ([[!n:num. (f:complex->complex) (z n) IN ball (f b,t)]]) THEN
    UNDISCH_TAC ([[!n:num. z n IN ball(b:complex,r)]]) THEN
    REWRITE_TAC [AND_FORALL_THM, IMP_IMP] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC ([[nn:num]]) THEN
    SPEC_TAC (([[(z:num->complex) nn]]), ([[w:complex]])) THEN REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[g:complex->complex]]), ([[complex_derivative g]]),
                  ([[ball((f:complex->complex) b,t)]]),
                   ([[r / s:real]])]
          COMPLEX_MVT) THEN
    REWRITE_TAC [CONVEX_BALL] THEN ANTS_TAC THENL
     [ALL_TAC,
      DISCH_THEN (MP_TAC o HolLight.SPECL
       [([[(f:complex->complex) b]]), ([[(f:complex->complex) w]])]) THEN
      ASM_SIMP_TAC [CENTRE_IN_BALL, IN_CBALL] THEN
      MATCH_MP_TAC h7 THEN
      GEN_REWRITE_TAC HolLight.RAND_CONV [h8] THEN
      ASM_SIMP_TAC [REAL_LE_LMUL_EQ, REAL_LT_DIV] THEN
      ASM_MESON_TAC [IN_BALL, dist, DIST_SYM, REAL_LT_IMP_LE]] THEN
    FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [HOLOMORPHIC_ON_DIFFERENTIABLE]) THEN
    ASM_SIMP_TAC [HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN, OPEN_BALL,
                 COMPLEX_DIFFERENTIABLE_WITHIN_OPEN] THEN
    REWRITE_TAC [HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
    DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
    FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h9) THEN
    X_GEN_TAC ([[z:complex]]) THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
    EXISTS_TAC ([[norm(complex_derivative f z)]]) THEN
    ASM_SIMP_TAC [(← HolLight.GSYM COMPLEX_NORM_MUL), COMPLEX_NORM_CX, REAL_ABS_NUM] THEN
    REWRITE_TAC [h10] THEN
    ASM_SIMP_TAC [REAL_LE_RDIV_EQ, COMPLEX_NORM_NZ, REAL_MUL_LID] THEN
    ASM_MESON_TAC [h11])
  : ExceptT String IO thm).run
#eval LEMMA_3

-- ------------------------------------------------------------------------- --
-- Lemma 4.                                                                  --
-- ------------------------------------------------------------------------- --

#eval phrase 13
def LEMMA_4 : thm := keep "LEMMA_4" fun _ => (do
  let h16 ← na (← ExceptT.mk [[dist(w,w + x) = norm x /\ dist(w,w - x) = norm x]])
  let h15 ← rr (← ExceptT.mk [[&0 < pi ==> abs(pi / &2) * &1 < pi]])
  let h14 ← rr
    (← ExceptT.mk [[pi < x ==> x <= y ==> pi <= y]])
  let h13 ← sr
    (← ExceptT.mk [[DISJOINT (IMAGE f s) t ==> !P. (!z. ~(z IN t) ==> P z)
    ==> !z. z IN s ==> P(f z)]])
  let h12 ← ar (← ExceptT.mk [[m < n ==> 1 <= n - m]])
  let h11 ← rr (← ExceptT.mk [[&0 < x / &3 <=> &0 < x]])
  let h10 ← sr
    (← ExceptT.mk [[DISJOINT (IMAGE f s) t ==> (!z. ~(z IN t) ==> P z)
    ==> !z. z IN s ==> P(f z)]])
  let h9 ← ar (← ExceptT.mk [[m < n ==> 0 < n]])
  let h8 ← rr (← ExceptT.mk [[&1 <= x ==> &1 <= &2 * x]])
  let h7 ← rr (← ExceptT.mk [[pi <= &2 * x * pi <=> pi * &1 <= pi * &2 * x]])
  let h6 ← tt
    (← ExceptT.mk [[(p ==> r) ==> (~p ==> q ==> r) ==> (q ==> r)]])
  let h5 ← rf
    (← ExceptT.mk [[~(pi = &0) ==> (x * pi) / pi = x]])
  let h4 ← rr
    (← ExceptT.mk [[x + &1 <= y /\ y < floor y + &1 ==> x <= floor y]])
  let h3 ← rr (← ExceptT.mk [[&0 < &2]])
  let h2 ← sr
    (← ExceptT.mk [[(!x. real x ==> x IN t) /\ z IN s
    ==> real(f z) ==> ~DISJOINT (IMAGE f s) t]])
  let h1 ← tt (← ExceptT.mk [[(~p ==> p) ==> p]])
  prove ([[!v. ~(v = {}) /\ open v /\ connected v
        ==> FINITE {n | DISJOINT (IMAGE (ITER n cexp) v)
                                 {z | abs(Im z) <= pi / &3}}]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     ([[?N. !n. N < n
              ==> ~DISJOINT (IMAGE (ITER n cexp) v) {z | abs(Im z) <= pi / &3}]])
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC h1 THEN DISCH_TAC,
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[0..N]]) THEN
      REWRITE_TAC [FINITE_NUMSEG, SUBSET, IN_ELIM_THM, IN_NUMSEG, LE_0] THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM CONTRAPOS_THM)] THEN
      ASM_REWRITE_TAC [NOT_LE]] THEN
    SUBGOAL_THEN
     ([[?n z:complex. z IN v /\ integer(Im(ITER n cexp z) / pi)]])
    STRIP_ASSUME_TAC THENL
     [ALL_TAC,
      EXISTS_TAC ([[n:num]]) THEN REWRITE_TAC [LT_EXISTS, LEFT_IMP_EXISTS_THM] THEN
      SUBGOAL_THEN ([[!d. real(ITER (n + SUC d) cexp z)]]) ASSUME_TAC THENL
       [INDUCT_TAC THEN ONCE_REWRITE_TAC [ADD_CLAUSES] THENL
         [REWRITE_TAC [ADD_CLAUSES, ITER, real, IM_CEXP, REAL_ENTIRE] THEN
          DISJ2_TAC THEN FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP SIN_INTEGER_PI) THEN
          SIMP_TAC [REAL_DIV_RMUL, PI_NZ],
          ASM_SIMP_TAC [ITER, REAL_EXP]],
        MAP_EVERY X_GEN_TAC [([[q:num]]), ([[d:num]])] THEN DISCH_THEN SUBST1_TAC THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[d:num]])) THEN MATCH_MP_TAC h2 THEN
        ASM_SIMP_TAC [real, IN_ELIM_THM] THEN MP_TAC PI_POS THEN
        REAL_ARITH_TAC2]] THEN
    SUBGOAL_THEN
     ([[?n w z. w IN v /\ z IN v /\
              pi <= abs(Im(ITER n cexp w) - Im(ITER n cexp z))]])
    MP_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[n:num]]) THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MATCH_MP_TAC WLOG_RELATION THEN
      EXISTS_TAC ([[\w z. Im(ITER n cexp z) <= Im(ITER n cexp w)]]) THEN
      REWRITE_TAC [REAL_LE_TOTAL] THEN
      CONJ_TAC THENL [MESON_TAC [REAL_ABS_SUB], ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [([[w:complex]]), ([[z:complex]])] THEN
      SIMP_TAC [real_abs, REAL_SUB_LE] THEN REPEAT STRIP_TAC THEN
      MP_TAC (← HolLight.ISPECL
       [([[IMAGE (ITER n cexp) v]]), ([[ITER n cexp z]]), ([[ITER n cexp w]]),
        ([[floor(Im(ITER n cexp w) / pi) * pi]]), ([[2]])]
          CONNECTED_IVT_COMPONENT) THEN
      REWRITE_TAC [DIMINDEX_2, ARITH, (← HolLight.GSYM IM_DEF), EXISTS_IN_IMAGE] THEN
      SIMP_TAC [PI_POS, h3, REAL_LT_MUL,
               (← HolLight.GSYM REAL_LE_LDIV_EQ), (← HolLight.GSYM REAL_LE_RDIV_EQ)] THEN
      ANTS_TAC THENL
       [REWRITE_TAC [FLOOR] THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC [] THEN
          SIMP_TAC [HOLOMORPHIC_ON_DIFFERENTIABLE,
                   COMPLEX_DIFFERENTIABLE_ITER_CEXP,
                   HOLOMORPHIC_ON_IMP_CONTINUOUS_ON,
                   COMPLEX_DIFFERENTIABLE_AT_WITHIN],
          REPEAT (CONJ_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC]) THEN
          MATCH_MP_TAC h4 THEN
          REWRITE_TAC [FLOOR] THEN
          ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_ADD_RDISTRIB, REAL_DIV_RMUL,
                       PI_POS, REAL_LT_IMP_NZ,
                       IM_ADD, IM_MUL_II, RE_CX, REAL_LE_LADD] THEN
          ASM_REAL_ARITH_TAC],
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[y:complex]]) THEN
        STRIP_TAC THEN
        ASM_SIMP_TAC [PI_NZ, FLOOR, h5]]] THEN
    ASM_CASES_TAC
     ([[!n w z. w IN v /\ z IN v /\ ITER n cexp w = ITER n cexp z ==> w = z]])
    THENL
     [ALL_TAC,
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [NOT_FORALL_THM]) THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN INDUCT_TAC THEN SIMP_TAC [ITER] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h6) THEN
      REWRITE_TAC [] THEN DISCH_TAC THEN
      DISCH_THEN (fun th => EXISTS_TAC ([[n:num]]) THEN MP_TAC th) THEN
      REWRITE_TAC [NOT_FORALL_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[w:complex]]) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[z:complex]]) THEN
      REWRITE_TAC [NOT_IMP] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[w:complex]]), ([[z:complex]])]) THEN
      ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [CEXP_EQ]) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[i:real]]) STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC [IM_ADD, REAL_ADD_SUB, IM_MUL_II, RE_CX] THEN
      ASM_CASES_TAC ([[i = &0]]) THEN
      ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO, COMPLEX_MUL_LZERO,
                      COMPLEX_ADD_RID] THEN
      DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
      SIMP_TAC [REAL_ABS_MUL, REAL_ABS_PI, REAL_ABS_NUM] THEN
      REWRITE_TAC [h7] THEN
      SIMP_TAC [REAL_LE_LMUL_EQ, PI_POS] THEN
      MATCH_MP_TAC h8 THEN
      MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN
      ASM_REWRITE_TAC []] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [INJECTIVE_ON_ALT]) THEN
    SUBGOAL_THEN
     ([[?r. ((!n. 0 < r n) /\
           (!n. DISJOINT (IMAGE (ITER (r n) cexp) v)
                {z | abs (Im z) <= pi / &3})) /\
          (!n. r n < r(SUC n))]])
    STRIP_ASSUME_TAC THENL
     [ONCE_REWRITE_TAC [AND_FORALL_THM] THEN
      MATCH_MP_TAC DEPENDENT_CHOICE THEN
      ASM_MESON_TAC [h9],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!m n. m < n ==> (r:num->num) m < r n]]) ASSUME_TAC THENL
     [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN ASM_MESON_TAC [LT_TRANS],
      ALL_TAC] THEN
    SUBGOAL_THEN
     ([[!n z. z IN v
            ==> (pi / &3) pow n <= norm(complex_derivative (ITER (r n) cexp) z)]])
    ASSUME_TAC THENL
     [INDUCT_TAC THEN X_GEN_TAC ([[z:complex]]) THEN DISCH_TAC THENL
       [TRANS_TAC REAL_LE_TRANS ([[abs(Im(ITER (r 0) cexp z))]]) THEN
        ASM_SIMP_TAC [real_pow, LE_1, LEMMA_1] THEN
        UNDISCH_TAC ([[(z:complex) IN v]]) THEN
        SPEC_TAC (([[z:complex]]), ([[z:complex]])) THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h10 o HolLight.SPEC ([[0]])) THEN
        REWRITE_TAC [IN_ELIM_THM] THEN MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC2,
        ALL_TAC] THEN
      SUBGOAL_THEN
       ([[ITER (r (SUC n)) cexp = ITER (r(SUC n) - r n) cexp o ITER (r n) cexp]])
      SUBST1_TAC THENL
       [REWRITE_TAC [FUN_EQ_THM, o_THM, ITER_ADD] THEN
        ASM_SIMP_TAC [SUB_ADD, LT_IMP_LE],
        SIMP_TAC [COMPLEX_DERIVATIVE_CHAIN, COMPLEX_DIFFERENTIABLE_ITER_CEXP]] THEN
      REWRITE_TAC [real_pow, COMPLEX_NORM_MUL] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC [h11, PI_POS, REAL_POW_LE,
                   REAL_LT_IMP_LE] THEN
      HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Kernel.rand o HolCore.Kernel.rand) LEMMA_1 o
        HolCore.Kernel.rand o HolLight.snd) THEN
      ASM_SIMP_TAC [h12] THEN
      ASM_SIMP_TAC [ITER_ADD, SUB_ADD, LT_IMP_LE] THEN
      MATCH_MP_TAC (← HolLight.REWRITE_RULE [IMP_CONJ] REAL_LE_TRANS) THEN
      UNDISCH_TAC ([[(z:complex) IN v]]) THEN
        SPEC_TAC (([[z:complex]]), ([[z:complex]])) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP h13 o HolLight.SPEC ([[SUC n]])) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC [IN_ELIM_THM] THEN MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [(← HolLight.GSYM MEMBER_NOT_EMPTY)]) THEN
    DISCH_THEN (X_CHOOSE_TAC ([[z:complex]])) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [OPEN_CONTAINS_BALL]) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[z:complex]])) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC ([[r:real]]) THEN
    STRIP_TAC THEN MP_TAC (← HolLight.ISPECL [([[pi / &3]]), ([[pi / r]])] REAL_ARCH_POW) THEN
    ANTS_TAC THENL [MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC2, ALL_TAC] THEN
    ASM_SIMP_TAC [(← HolLight.ONCE_REWRITE_RULE [REAL_MUL_SYM] REAL_LT_LDIV_EQ)] THEN
    DISCH_THEN (X_CHOOSE_TAC ([[n:num]])) THEN EXISTS_TAC ([[(r:num->num) n]]) THEN
    MP_TAC (← HolLight.ISPECL [([[(r:num->num) n]]), ([[z:complex]]), ([[r:real]]), ([[pi]])] LEMMA_3) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [HolLight.ASM SET_TAC [], X_GEN_TAC ([[w:complex]])] THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h14) THEN
      ASM_SIMP_TAC [REAL_LE_LMUL_EQ] THEN HolLight.ASM SET_TAC [],
      ABBREV_TAC ([[w = ITER (r(n:num)) cexp z]]) THEN REWRITE_TAC [SUBSET] THEN
      DISCH_THEN (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC ([[w - pi / &2 % basis 2:complex]]) th) THEN
              MP_TAC (← HolLight.SPEC ([[w + pi / &2 % basis 2:complex]]) th))) THEN
      SIMP_TAC [IN_BALL, NORM_MUL, NORM_BASIS, DIMINDEX_2, ARITH, PI_POS,
        h15,
        h16] THEN
      REWRITE_TAC [IN_IMAGE, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC ([[a:complex]]) THEN DISCH_THEN (STRIP_ASSUME_TAC o HolLight.GSYM) THEN
      X_GEN_TAC ([[b:complex]]) THEN DISCH_THEN (STRIP_ASSUME_TAC o HolLight.GSYM) THEN
      MAP_EVERY EXISTS_TAC [([[a:complex]]), ([[b:complex]])] THEN
      REPEAT (CONJ_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC]) THEN
      ASM_REWRITE_TAC [IM_ADD, IM_SUB, COMPLEX_CMUL, IM_MUL_CX] THEN
      SIMP_TAC [IM_DEF, BASIS_COMPONENT, DIMINDEX_2, ARITH] THEN
      REAL_ARITH_TAC2])
  : ExceptT String IO thm).run
#eval LEMMA_4

-- ------------------------------------------------------------------------- --
-- Lemma 5.                                                                  --
-- ------------------------------------------------------------------------- --

#eval phrase 14
def LEMMA_5 : thm := keep "LEMMA_5" fun _ => (do
  let h27 ← tt (← ExceptT.mk [[~p /\ r ==> (~p /\ ~q ==> ~r) ==> q]])
  let h26 ← sr (← ExceptT.mk [[s DIFF t = {} <=> s SUBSET t]])
  let h25 ← sr
    (← ExceptT.mk [[u SUBSET w INTER h INTER s ==> (!x. x IN h /\ x IN s ==> f x IN h)
    ==> IMAGE f u SUBSET h]])
  let h24 ← tt (← ExceptT.mk [[p /\ (p ==> q) ==> p /\ q]])
  let h23 ← tt (← ExceptT.mk [[p /\ (p ==> q) ==> p /\ q]])
  let h22 ← rr (← ExceptT.mk [[x > y <=> ~(x <= y)]])
  let h21 ← sr (← ExceptT.mk [[s DIFF t = {} <=> s SUBSET t]])
  let h20 ← ar (← ExceptT.mk [[~(m:num <= n) ==> n <= m]])
  let h19 ← ar (← ExceptT.mk [[N + 1 <= n <=> ~(n <= N)]])
  let h18 ← sr (← ExceptT.mk [[{x | P x /\ Q x} = {x | P x} INTER {x | Q x}]])
  let h17 ← sr
    (← ExceptT.mk [[(~(s INTER (UNIV DIFF t) = {}) /\ ~(s DIFF (UNIV DIFF t) = {}) ==> F)
    ==> ~(s SUBSET t) ==> DISJOINT s t]])
  let h16 ← sr
    (← ExceptT.mk [[(!z. Q z ==> P z) ==> DISJOINT t {z | P(cexp z)}
    ==> DISJOINT (IMAGE cexp t) {z | Q z}]])
  let h15 ← sr
    (← ExceptT.mk [[(!x. x IN s ==> x IN t) ==> DISJOINT u t ==> DISJOINT u s]])
  let h14 ← sr
    (← ExceptT.mk [[s SUBSET s' /\ t SUBSET t'
    ==> (s UNION t) SUBSET (s' UNION t')]])
  let h13 ← sr
    (← ExceptT.mk [[~(~(s INTER (UNIV DIFF t) = {}) /\ ~(s DIFF (UNIV DIFF t) = {}))
    ==> s SUBSET t \/ DISJOINT s t]])
  let h12 ← sr
    (← ExceptT.mk [[((!n. f n SUBSET s \/ DISJOINT (f n) s) /\
    (!n. f n SUBSET t \/ DISJOINT (f n) t))/\
    {n | DISJOINT (f n) s} UNION {n | DISJOINT (f n) t} SUBSET u
    ==> {n | DISJOINT (f n) (s INTER t)} SUBSET u]])
  let h11 ← sr (← ExceptT.mk [[{x | P x /\ Q x} = {x | P x} INTER {x | Q x}]])
  let h10 ← ar (← ExceptT.mk [[n = (n + 1) - 1]])
  let h9 ← sr
    (← ExceptT.mk [[IMAGE f s SUBSET t /\ IMAGE f u SUBSET v
    ==> IMAGE f (s INTER u) SUBSET t INTER v]])
  let h8 ← sr
    (← ExceptT.mk [[UNIV DIFF {x | P x} = {x | ~P x}]])
  let h7 ← sr
    (← ExceptT.mk [[IMAGE f u SUBSET t
    ==> IMAGE f s INTER t = {} ==> s INTER u = {}]])
  let h6 ← rr
    (← ExceptT.mk [[abs x = a ==> x = a \/ x = --a]])
  let h5 ← sr
    (← ExceptT.mk [[(!x. x IN t ==> real(f x))
    ==> IMAGE f s INTER real = {} ==> s INTER t = {}]])
  let h4 ← rr (← ExceptT.mk [[a <= x /\ x * &1 <= x * s ==> a <= x * s]])
  let h3 ← rr
    (← ExceptT.mk [[pi < &4 /\ &2 pow 4 <= x * y ==> &2 * pi < x * y / &2]])
  let h2 ← rr
    (← ExceptT.mk [[abs x = a ==> x = a \/ x = --a]])
  let h1 ← sr
    (← ExceptT.mk [[(!x. x IN s /\ x IN u ==> ~(x IN t)) ==> DISJOINT s (t INTER u)]])
  prove ([[!v. ~(v = {}) /\ open v /\ connected v /\
       INFINITE {n | IMAGE (ITER n cexp) v SUBSET {z | Re z > &4}}
       ==> ?n. ~(IMAGE (ITER n cexp) v INTER real = {})]])
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [(← HolLight.GSYM NOT_FORALL_THM)] THEN
    DISCH_TAC THEN MAP_EVERY ABBREV_TAC
     [([[h = {z | Re z > &4}]]),
      ([[s = {z | abs(Im z) <= pi / &3}]]),
      ([[w = {z | abs(Im z) <= &2 * pi /\ abs(Im(cexp z)) <= &2 * pi}]])] THEN
    SUBGOAL_THEN ([[DISJOINT (frontier s) (w INTER h:complex->bool)]])
    ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN
      REWRITE_TAC [IM_DEF, FRONTIER_STRIP_COMPONENT_LE] THEN
      REWRITE_TAC [(← HolLight.GSYM IM_DEF)] THEN MATCH_MP_TAC h1 THEN
      MAP_EVERY EXPAND_TAC ["h", "w"] THEN REWRITE_TAC [IN_ELIM_THM] THEN
      X_GEN_TAC ([[z:complex]]) THEN REWRITE_TAC [IM_CEXP, real_gt] THEN
      STRIP_TAC THEN DISCH_THEN (MP_TAC o HolLight.CONJUNCT2) THEN
      REWRITE_TAC [REAL_NOT_LE, REAL_ABS_MUL, REAL_ABS_EXP] THEN
      SUBGOAL_THEN ([[abs(sin(Im z)) = sqrt(&3) / &2]]) SUBST1_TAC THENL
       [FIRST_X_ASSUM (DISJ_CASES_THEN SUBST1_TAC o HolLight.MATCH_MP h2) THEN
        REWRITE_TAC [SIN_NEG, SIN_PI3, REAL_ABS_NEG] THEN
        SIMP_TAC [REAL_ABS_REFL, REAL_LE_DIV, SQRT_POS_LE, REAL_POS],
        ALL_TAC] THEN
      MATCH_MP_TAC h3 THEN
      CONJ_TAC THENL [MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC2, ALL_TAC] THEN
      MATCH_MP_TAC h4 THEN
      CONJ_TAC THENL
       [TRANS_TAC REAL_LE_TRANS ([[exp(&4 * &1)]]) THEN CONJ_TAC THENL
         [REWRITE_TAC [REAL_EXP_N] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
          MP_TAC E_APPROX_32 THEN REAL_ARITH_TAC2,
          REWRITE_TAC [REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC],
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_EXP_POS_LE] THEN
        SUBST1_TAC (← HolLight.SYM SQRT_1) THEN MATCH_MP_TAC SQRT_MONO_LE THEN
        CONV_TAC REAL_RAT_REDUCE_CONV],
      ALL_TAC] THEN
    SUBGOAL_THEN
     ([[!n. IMAGE (ITER n cexp) v INTER frontier {z | abs (Im z) <= &2 * pi} = {}]])
    ASSUME_TAC THENL
     [REWRITE_TAC [IM_DEF, FRONTIER_STRIP_COMPONENT_LE] THEN
      REWRITE_TAC [(← HolLight.GSYM IM_DEF)] THEN X_GEN_TAC ([[n:num]]) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[SUC n]])) THEN
      REWRITE_TAC [ITER_POINTLESS, IMAGE_o] THEN
      MATCH_MP_TAC h5 THEN
      REWRITE_TAC [IN_ELIM_THM, real, IM_CEXP] THEN GEN_TAC THEN
      DISCH_THEN (DISJ_CASES_THEN SUBST1_TAC o HolLight.MATCH_MP h6) THEN
      REWRITE_TAC [SIN_NEG, SIN_NPI, REAL_MUL_RZERO, REAL_NEG_0],
      ALL_TAC] THEN
    SUBGOAL_THEN
     ([[!n. IMAGE (ITER n cexp) v INTER frontier {z | abs(Im(cexp z)) <= &2 * pi} =
          {}]])
    ASSUME_TAC THENL
     [X_GEN_TAC ([[n:num]]) THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[SUC n]])) THEN
      REWRITE_TAC [ITER_POINTLESS, IMAGE_o] THEN MATCH_MP_TAC h7 THEN
      REWRITE_TAC [FRONTIER_CLOSURES, REAL_NOT_LE, h8] THEN
      MATCH_MP_TAC h9 THEN
      CONJ_TAC THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC FORALL_IN_CLOSURE THEN
      REWRITE_TAC [CLOSED_CLOSURE, CONTINUOUS_ON_CEXP] THEN
      GEN_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN
      MATCH_MP_TAC (← HolLight.REWRITE_RULE [SUBSET] CLOSURE_SUBSET) THEN
      ASM_REWRITE_TAC [IN_ELIM_THM],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[FINITE {n | DISJOINT (IMAGE (ITER n cexp) v) w}]])
    ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC ([[{n | DISJOINT (IMAGE (ITER n cexp) v)
                                {z | abs(Im z) <= pi / &3}} UNION
                  {n | DISJOINT (IMAGE (ITER (n + 1) cexp) v)
                                {z | abs(Im z) <= pi / &3}}]]) THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC [FINITE_UNION, LEMMA_4] THEN
        GEN_REWRITE_TAC
         (HolLight.RAND_CONV o HolLight.RAND_CONV o HolLight.ABS_CONV o HolLight.BINDER_CONV o HolLight.RAND_CONV)
         [h10] THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC ([[IMAGE (\n. n - 1)
                          {n | DISJOINT (IMAGE (ITER n cexp) v)
                                        {z | abs (Im z) <= pi / &3}}]]) THEN
        ASM_SIMP_TAC [LEMMA_4, FINITE_IMAGE] THEN SET_TAC [],
        EXPAND_TAC "w" THEN
        REWRITE_TAC [h11] THEN
        MATCH_MP_TAC h12 THEN
        CONJ_TAC THENL
         [CONJ_TAC THEN GEN_TAC THEN MATCH_MP_TAC h13 THEN
          DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← HolLight.ONCE_REWRITE_RULE [IMP_CONJ_ALT]
            CONNECTED_INTER_FRONTIER)) THEN
          ASM_REWRITE_TAC [FRONTIER_COMPLEMENT] THEN
          ASM_SIMP_TAC [CONNECTED_CONTINUOUS_IMAGE, CONTINUOUS_ON_ITER_CEXP],
          MATCH_MP_TAC h14 THEN
          CONJ_TAC THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
          X_GEN_TAC ([[n:num]]) THENL
           [MATCH_MP_TAC h15,
            REWRITE_TAC [(← HolLight.GSYM ADD1), ITER_POINTLESS, IMAGE_o] THEN
            MATCH_MP_TAC h16] THEN
          REWRITE_TAC [IN_ELIM_THM] THEN REAL_ARITH_TAC2]],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[FINITE {n | ~(IMAGE (ITER n cexp) v SUBSET w)}]])
    ASSUME_TAC THENL
     [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ]
        FINITE_SUBSET)) THEN
      GEN_REWRITE_TAC HolCore.Lib.I [SUBSET] THEN X_GEN_TAC ([[n:num]]) THEN
      REWRITE_TAC [IN_ELIM_THM] THEN MATCH_MP_TAC h17 THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP (← HolLight.ONCE_REWRITE_RULE [IMP_CONJ_ALT]
            CONNECTED_INTER_FRONTIER)) THEN
      ASM_SIMP_TAC [CONNECTED_CONTINUOUS_IMAGE, CONTINUOUS_ON_ITER_CEXP] THEN
      REWRITE_TAC [FRONTIER_COMPLEMENT] THEN EXPAND_TAC "w" THEN
      REWRITE_TAC [h18] THEN
      HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH HolCore.Equal.lhand FRONTIER_INTER_SUBSET o
        HolCore.Kernel.rand o HolCore.Equal.lhand o HolLight.snd) THEN
      HolLight.ASM SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     ([[?N. (!n. N <= n ==> ~(IMAGE (ITER n cexp) v INTER s = {})) /\
          (!n. N <= n ==> IMAGE (ITER n cexp) v SUBSET w)]])
    STRIP_ASSUME_TAC THENL
     [MP_TAC (← HolLight.ISPECL
       [([[\n:num. n]]),
        ([[{n | ~(IMAGE (ITER n cexp) v SUBSET w)} UNION
         {n | DISJOINT (IMAGE (ITER n cexp) v) s}]])]
       UPPER_BOUND_FINITE_SET) THEN ASM_SIMP_TAC [FINITE_UNION] THEN
       ANTS_TAC THENL [ASM_MESON_TAC [LEMMA_4], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[N:num]])
       (fun th => EXISTS_TAC ([[N + 1]]) THEN MP_TAC th)) THEN
      REWRITE_TAC [h19, CONTRAPOS_THM] THEN
      REWRITE_TAC [DISJOINT, IN_ELIM_THM, IN_UNION] THEN MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     ([[~({n | IMAGE (ITER n cexp) v SUBSET w INTER h} SUBSET 0..N)]])
    MP_TAC THENL
     [DISCH_THEN (MP_TAC o
        HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ_ALT] FINITE_SUBSET)) THEN
      REWRITE_TAC [FINITE_NUMSEG, (← HolLight.GSYM INFINITE)] THEN
      MATCH_MP_TAC INFINITE_SUPERSET THEN
      EXISTS_TAC ([[{n | IMAGE (ITER n cexp) v SUBSET h} DIFF
                  {n |  ~(IMAGE (ITER n cexp) v SUBSET w)}]]) THEN
      ASM_SIMP_TAC [INFINITE_DIFF_FINITE] THEN SET_TAC [],
      ALL_TAC] THEN
    PURE_ONCE_REWRITE_TAC [SUBSET] THEN
    REWRITE_TAC [NOT_IMP, IN_ELIM_THM, IN_NUMSEG, LE_0] THEN
    X_GEN_TAC ([[n:num]]) THEN REWRITE_TAC [SUBSET_INTER] THEN STRIP_TAC THEN
    MATCH_MP_TAC h20 THEN DISCH_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[IMAGE (ITER n cexp) v]]), ([[s:complex->bool]])]
          CONNECTED_INTER_FRONTIER) THEN
    ASM_SIMP_TAC [CONNECTED_CONTINUOUS_IMAGE, CONTINUOUS_ON_ITER_CEXP,
                 NOT_IMP] THEN
    CONJ_TAC THENL [ALL_TAC, HolLight.ASM SET_TAC []] THEN
    REWRITE_TAC [h21] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     ([[?m. ~(IMAGE (ITER (n + m) cexp) v SUBSET s)]])
    MP_TAC THENL
     [SUBGOAL_THEN ([[?z. z IN IMAGE (ITER n cexp) v]]) STRIP_ASSUME_TAC THENL
       [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      MP_TAC (← HolLight.SPEC ([[z:complex]]) LEMMA_2b) THEN
      ANTS_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      REWRITE_TAC [h22] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[m:num]]) THEN
      GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV o HolLight.LAND_CONV o HolLight.LAND_CONV)
        [(← HolLight.GSYM ETA_AX)] THEN
      REWRITE_TAC [(← HolLight.ONCE_REWRITE_RULE [ADD_SYM] (← HolLight.GSYM ITER_ADD))] THEN
      HolLight.ASM SET_TAC [],
      REWRITE_TAC [NOT_EXISTS_THM]] THEN
    SUBGOAL_THEN
     ([[!m. IMAGE (ITER (n + m) cexp) v SUBSET (w INTER h INTER s)]])
    MP_TAC THENL [ALL_TAC, HolLight.ASM SET_TAC []] THEN
    INDUCT_TAC THENL
     [ASM_REWRITE_TAC [ADD_CLAUSES, ITER_POINTLESS, SUBSET_INTER], ALL_TAC] THEN
    REWRITE_TAC [ADD_CLAUSES, SUBSET_INTER] THEN
    MATCH_MP_TAC h23 THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, DISCH_TAC] THEN
    MATCH_MP_TAC h24 THEN CONJ_TAC THENL
     [REWRITE_TAC [ITER_POINTLESS, IMAGE_o] THEN FIRST_X_ASSUM (MATCH_MP_TAC o
        HolLight.MATCH_MP h25) THEN
      MAP_EVERY EXPAND_TAC ["h", "s"] THEN REWRITE_TAC [IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP LEMMA_2a) THEN
      MP_TAC LOG2_APPROX_32 THEN ASM_REAL_ARITH_TAC,
      DISCH_TAC THEN
      MP_TAC (← HolLight.ISPECL [([[IMAGE (ITER (SUC(n + m)) cexp) v]]), ([[s:complex->bool]])]
        CONNECTED_INTER_FRONTIER) THEN
       ASM_SIMP_TAC [CONNECTED_CONTINUOUS_IMAGE, CONTINUOUS_ON_ITER_CEXP] THEN
       REWRITE_TAC [h26] THEN
      MATCH_MP_TAC h27 THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, HolLight.ASM SET_TAC []]])
  : ExceptT String IO thm).run
#eval LEMMA_5

-- ------------------------------------------------------------------------- --
-- Lemma 6.                                                                  --
-- ------------------------------------------------------------------------- --

#eval phrase 15
def LEMMA_6 : thm := keep "LEMMA_6" fun _ => (do
  -- OCaml's `let lemma = prove(...) in TAC`: the local lemma is proved
  -- first (its one SET_RULE runs just before that proof, so it is written
  -- in place with `←`), then the main tactic's build-time rules run.
  let lemma ← prove
   ([[!v. ~(v = {}) /\ open v /\ connected v /\
         (!n. IMAGE (ITER n cexp) v INTER real = {})
         ==> FINITE {n | IMAGE (ITER n cexp) v INTER
                         cball(Cx(&0),exp(&4)) = {}}]])
   (REPEAT STRIP_TAC THEN MP_TAC (← HolLight.SPEC ([[v:complex->bool]]) LEMMA_5) THEN
    ASM_REWRITE_TAC [INFINITE] THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
     ([[0 INSERT (IMAGE (\n. n + 1)
                      {n | IMAGE (ITER n cexp) v SUBSET {z | Re z > &4}})]]) THEN
    ASM_SIMP_TAC [FINITE_INSERT, FINITE_IMAGE] THEN
    GEN_REWRITE_TAC HolCore.Lib.I [SUBSET] THEN REWRITE_TAC [IN_INSERT, IN_ELIM_THM] THEN
    MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC [] THEN
    X_GEN_TAC ([[n:num]]) THEN DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN DISCH_TAC THEN
    DISJ2_TAC THEN REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC ([[n:num]]) THEN
    ASM_REWRITE_TAC [ADD1, IN_ELIM_THM] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [ITER_POINTLESS, IMAGE_o]) THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← sr
     ([[IMAGE f s INTER t = {}
      ==> (!x. ~(x IN u) ==> f x IN t)
      ==> s SUBSET u]]))) THEN
    REWRITE_TAC [IN_ELIM_THM, COMPLEX_IN_CBALL_0, real_gt, REAL_NOT_LT] THEN
    REWRITE_TAC [NORM_CEXP, REAL_EXP_MONO_LE])
  let h10 ← sr
    (← ExceptT.mk [[DISJOINT s t <=> !x. x IN s ==> x IN (UNIV DIFF t)]])
  let h9 ← ms [OPEN_CONTAINS_BALL]
    (← ExceptT.mk [[ITER n f x IN s
    ==> open s ==> ?e. &0 < e /\ ball(ITER n f x,e) SUBSET s]])
  let h8 ← rr
    (← ExceptT.mk [[g + n <= Re x /\ &1 + Re x <= Re(cexp x)
    ==> g + n + &1 <= Re(cexp x)]])
  let h7 ← tt (← ExceptT.mk [[!p. p /\ q ==> q]])
  let h6 ← rr
    (← ExceptT.mk [[x + n <= y ==> &5 - x <= n ==> y > &4]])
  let h5 ← na
    (← ExceptT.mk [[dist(y,x) < e / &2 ==> norm(z - y) < e / &2 ==> norm(z - x) < e]])
  let h4 ← tt (← ExceptT.mk [[~((p /\ q) /\ r) <=> p ==> q ==> ~r]])
  let h3 ← ar
    (← ExceptT.mk [[M + N + 1 >= N /\
    (M + N + 1 <= r(M + N + 1) ==> ~(r(M + N + 1) <= M))]])
  let h2 ← tt (← ExceptT.mk [[~q ==> p /\ q ==> r]])
  let h1 ← sr
    (← ExceptT.mk [[P a /\ P b ==> IMAGE f s INTER P = {}
    ==> !x. x IN s ==> ~(f x = a) /\ ~(f x = b)]])
  prove ([[!v. ~(v = {}) /\ open v /\ connected v
       ==> ?n. ~(IMAGE (ITER n cexp) v INTER real = {})]])
   (REWRITE_TAC [(← HolLight.GSYM NOT_FORALL_THM)] THEN REPEAT STRIP_TAC THEN
    ABBREV_TAC ([[d = cball(Cx(&0),exp(&4))]]) THEN
    MAP_EVERY ABBREV_TAC
     [([[h = {z | Re z > &4}]]), ([[s = {z | abs(Im z) <= pi / &3}]])] THEN
    SUBGOAL_THEN
     ([[?g r:num->num.
          g holomorphic_on v /\
          (!m n. m < n ==> r m < r n) /\
          (!x. x IN v ==> ((\n. ITER (r n) cexp x) --> g x) sequentially) /\
          (!x e. x IN v /\ &0 < e
                 ==> ?d N. &0 < d /\
                           !n y. N <= n /\ y IN cball(x,d)
                                 ==> norm(ITER (r n) cexp y - g x) < e)]])
    STRIP_ASSUME_TAC THENL
     [MP_TAC (← HolLight.ISPECL [([[\n. ITER n cexp]]), ([[{ITER n cexp | n IN (:num)}]]),
                     ([[v:complex->bool]]), ([[Cx(&0)]]), ([[Cx(&1)]])] MONTEL_OMITTING) THEN
      ASM_REWRITE_TAC [NOT_IMP] THEN ANTS_TAC THENL
       [REWRITE_TAC [CX_INJ, REAL_OF_NUM_EQ, ARITH_EQ] THEN
        ASM_REWRITE_TAC [FORALL_IN_GSPEC, IN_UNIV, NOT_IMP] THEN
        CONJ_TAC THENL [ALL_TAC, SET_TAC []] THEN
        REWRITE_TAC [HOLOMORPHIC_ON_ITER_CEXP] THEN
        X_GEN_TAC ([[n:num]]) THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[n:num]])) THEN
        MATCH_MP_TAC h1 THEN
        REWRITE_TAC [REAL_CX],
        ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
        X_GEN_TAC ([[r:num->num]]) THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        ASM_REWRITE_TAC []] THEN
      DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
       [MATCH_MP_TAC h2 THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [(← HolLight.GSYM MEMBER_NOT_EMPTY)]) THEN
        DISCH_THEN (X_CHOOSE_TAC ([[w:complex]])) THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [OPEN_CONTAINS_CBALL]) THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[w:complex]])) THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[b:real]]) STRIP_ASSUME_TAC) THEN
        DISCH_THEN (MP_TAC o HolLight.SPECL [([[cball(w:complex,b)]]), ([[exp(&4)]])]) THEN
        ASM_REWRITE_TAC [COMPACT_CBALL, NOT_EXISTS_THM] THEN
        X_GEN_TAC ([[N:num]]) THEN MP_TAC (← HolLight.SPEC ([[ball(w:complex,b)]]) lemma) THEN
        ASM_REWRITE_TAC [OPEN_BALL, CONNECTED_BALL, BALL_EQ_EMPTY] THEN
        ASM_REWRITE_TAC [REAL_NOT_LE] THEN ANTS_TAC THENL
         [MP_TAC (← HolLight.ISPECL [([[w:complex]]), ([[b:real]])] BALL_SUBSET_CBALL) THEN
          HolLight.ASM SET_TAC [],
          DISCH_THEN (MP_TAC o HolLight.ISPEC ([[\n:num. n]]) o
             HolLight.MATCH_MP UPPER_BOUND_FINITE_SET) THEN
          REWRITE_TAC [LEFT_IMP_EXISTS_THM, FORALL_IN_GSPEC] THEN
          X_GEN_TAC ([[M:num]]) THEN DISCH_THEN (fun th => HolLight.tactic_of do
           pure (DISCH_THEN (MP_TAC o HolLight.SPEC ([[M + N + 1]])) THEN
                 MP_TAC (← HolLight.SPEC ([[r(M + N + 1):num]]) th))) THEN
          FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP MONOTONE_BIGGER) THEN
          ASM_SIMP_TAC [h3] THEN
          EXPAND_TAC "d" THEN
          REWRITE_TAC [EXTENSION, IN_INTER, IN_IMAGE, NOT_IN_EMPTY] THEN
          REWRITE_TAC [IN_BALL, IN_CBALL, CONTRAPOS_THM] THEN
          REWRITE_TAC [dist, COMPLEX_SUB_LZERO, NORM_NEG] THEN
          REWRITE_TAC [LEFT_AND_EXISTS_THM, NOT_EXISTS_THM] THEN
          ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
          X_GEN_TAC ([[y:complex]]) THEN
          REWRITE_TAC [h4] THEN
          REWRITE_TAC [FORALL_UNWIND_THM2, REAL_NOT_LE] THEN
          SIMP_TAC [REAL_LT_IMP_LE]],
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[g:complex->complex]]) THEN
        STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
        MAP_EVERY X_GEN_TAC [([[w:complex]]), ([[e:real]])] THEN STRIP_TAC THEN
        SUBGOAL_THEN ([[(g:complex->complex) continuous at w]]) MP_TAC THENL
         [ASM_MESON_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_AT,
                        HOLOMORPHIC_ON_IMP_CONTINUOUS_ON],
          REWRITE_TAC [continuous_at]] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[e / &2]])) THEN ASM_REWRITE_TAC [REAL_HALF] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[d:real]]) STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [OPEN_CONTAINS_CBALL]) THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[w:complex]])) THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[b:real]]) STRIP_ASSUME_TAC) THEN
        EXISTS_TAC ([[min b (d / &2)]]) THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[cball(w:complex,b)]]), ([[e / &2]])]) THEN
        ASM_REWRITE_TAC [COMPACT_CBALL, REAL_HALF, GE, REAL_LT_MIN, IN_CBALL] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[N:num]]) THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC ([[n:num]]) THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC ([[y:complex]]) THEN
        REWRITE_TAC [REAL_LE_MIN] THEN DISCH_THEN (fun th =>
          STRIP_TAC THEN MP_TAC th THEN ASM_REWRITE_TAC []) THEN
        MATCH_MP_TAC h5 THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC [DIST_SYM] THEN
        ASM_REAL_ARITH_TAC],
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [(← HolLight.GSYM MEMBER_NOT_EMPTY)]) THEN
      DISCH_THEN (X_CHOOSE_TAC ([[w:complex]])) THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[w:complex]]))) THEN
      ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN
       ([[?k. ITER k cexp (g(w:complex)) IN h UNION ((:complex) DIFF s)]])
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC [IN_UNION, IN_DIFF, IN_UNIV, EXISTS_OR_THM] THEN
        ASM_CASES_TAC ([[real(g(w:complex))]]) THENL
         [ALL_TAC,
          DISJ2_TAC THEN EXPAND_TAC "s" THEN
          FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP LEMMA_2b) THEN
          REWRITE_TAC [real_gt, REAL_NOT_LE, IN_ELIM_THM]] THEN
        DISJ1_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC [IN_ELIM_THM] THEN
        MP_TAC (← HolLight.SPEC ([[&5 - Re(g(w:complex))]]) REAL_ARCH_SIMPLE) THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[n:num]]) THEN
        MATCH_MP_TAC h6 THEN
        MATCH_MP_TAC h7 THEN
        EXISTS_TAC ([[real(ITER n cexp (g(w:complex)))]]) THEN
        SPEC_TAC (([[n:num]]), ([[n:num]])) THEN INDUCT_TAC THEN
        ASM_REWRITE_TAC [ITER, REAL_ADD_RID, REAL_LE_REFL] THEN
        ASM_SIMP_TAC [REAL_EXP, (← HolLight.GSYM REAL_OF_NUM_SUC)] THEN
        MATCH_MP_TAC h8 THEN
        ASM_REWRITE_TAC [] THEN RULE_ASSUM_TAC (HolLight.REWRITE_RULE [real]) THEN
        ASM_REWRITE_TAC [RE_CEXP, COS_0, REAL_MUL_RID, REAL_EXP_LE_X],
        ALL_TAC] THEN
      FIRST_X_ASSUM (DISJ_CASES_TAC o HolLight.REWRITE_RULE [IN_UNION]) THEN
      FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP h9) THEN
      (ANTS_TAC THENL
        [EXPAND_TAC "h" THEN REWRITE_TAC [RE_DEF, OPEN_HALFSPACE_COMPONENT_GT] THEN
         EXPAND_TAC "s" THEN
         REWRITE_TAC [(← HolLight.GSYM closed), IM_DEF, CLOSED_STRIP_COMPONENT_LE],
         ALL_TAC]) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[e:real]]) STRIP_ASSUME_TAC) THEN
      MP_TAC (← HolLight.ISPECL [([[k:num]]), ([[(:complex)]])] CONTINUOUS_ON_ITER_CEXP) THEN
      REWRITE_TAC [continuous_on, IN_UNIV] THEN
      DISCH_THEN (MP_TAC o HolLight.SPECL [([[(g:complex->complex) w]]), ([[e:real]])]) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[d:real]]) STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[d:real]])) THEN
      ASM_REWRITE_TAC [NOT_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[b:real]]), ([[N:num]])] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [OPEN_CONTAINS_BALL]) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[w:complex]])) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[c:real]]) STRIP_ASSUME_TAC) THENL
       [MP_TAC (← HolLight.SPEC ([[ball(w:complex,min b c)]]) LEMMA_5) THEN
        ASM_REWRITE_TAC [OPEN_BALL, CONNECTED_BALL, BALL_EQ_EMPTY] THEN
        REWRITE_TAC [NOT_IMP] THEN REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC,
          ALL_TAC,
          REWRITE_TAC [NOT_EXISTS_THM] THEN
          SUBGOAL_THEN ([[ball(w:complex,min b c) SUBSET ball(w,c)]]) MP_TAC THENL
           [REWRITE_TAC [SUBSET_BALLS, DIST_REFL] THEN REAL_ARITH_TAC2,
            HolLight.ASM SET_TAC []]],
        MP_TAC (← HolLight.SPEC ([[ball(w:complex,min b c)]]) LEMMA_4) THEN
        ASM_REWRITE_TAC [OPEN_BALL, CONNECTED_BALL, BALL_EQ_EMPTY] THEN
        REWRITE_TAC [NOT_IMP] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC, REWRITE_TAC [(← HolLight.GSYM INFINITE)]]] THEN
      (MATCH_MP_TAC INFINITE_SUPERSET THEN
        EXISTS_TAC ([[IMAGE (\n. r n + (k:num)) ((:num) DIFF (0..N))]]) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC INFINITE_IMAGE THEN
          SIMP_TAC [INFINITE_DIFF_FINITE, num_INFINITE, FINITE_NUMSEG] THEN
          REWRITE_TAC [IN_UNIV, IN_NUMSEG, IN_DIFF, LE_0, NOT_LE] THEN
          MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC [EQ_ADD_RCANCEL] THEN
          ASM_MESON_TAC [LT_REFL],
          REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_UNIV, IN_ELIM_THM, IN_DIFF] THEN
          REWRITE_TAC [FORALL_IN_IMAGE, h10] THEN
          X_GEN_TAC ([[n:num]]) THEN REWRITE_TAC [IN_NUMSEG, LE_0] THEN DISCH_TAC THEN
          X_GEN_TAC ([[y:complex]]) THEN DISCH_TAC THEN
          REWRITE_TAC [(← HolLight.ONCE_REWRITE_RULE [ADD_SYM] (← HolLight.GSYM ITER_ADD))] THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [SUBSET]) THEN
          REWRITE_TAC [IN_BALL] THEN ONCE_REWRITE_TAC [DIST_SYM] THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [dist] THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          CONJ_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [IN_CBALL]] THEN
          RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN_BALL]) THEN ASM_REAL_ARITH_TAC])])
  : ExceptT String IO thm).run
#eval LEMMA_6

-- ------------------------------------------------------------------------- --
-- Main theorem that the iterates of the exponential do not give a           --
-- "normal family" in the sense of Montel's theorem.                         --
-- ------------------------------------------------------------------------- --

#eval phrase 16
def THEOREM : thm := keep "THEOREM" fun _ => (do
  let h24 ← rr (← ExceptT.mk [[x * -- &1 <= &0 <=> &0 <= x]])
  let h23 ← ar (← ExceptT.mk [[N < n ==> N <= SUC(SUC n)]])
  let h22 ← sr (← ExceptT.mk [[IMAGE f s INTER t = {} <=> !x. x IN s ==> ~(f x IN t)]])
  let h21 ← sr (← ExceptT.mk [[x IN real <=> real x]])
  let h20 ← sr (← ExceptT.mk [[{x | P x /\ Q x} = {x | P x} INTER {x | Q x}]])
  let h19 ← sr (← ExceptT.mk [[{x | P x /\ ~Q x} = {x | P x} DIFF {x | Q x}]])
  let h18 ← rr (← ExceptT.mk [[a <= x /\ x * &1 <= x * s ==> a <= x * s]])
  let h17 ← rr
    (← ExceptT.mk [[pi < &4 /\ &2 pow 4 <= x * y ==> &2 * pi < x * y / &2]])
  let h16 ← rr
    (← ExceptT.mk [[abs x = a ==> x = a \/ x = --a]])
  let h15 ← sr
    (← ExceptT.mk [[(!x. x IN s /\ x IN u ==> ~(x IN t)) ==> DISJOINT s (t INTER u)]])
  let h14 ← sr
    (← ExceptT.mk [[~(DISJOINT s real) ==> {x | real x} SUBSET t
    ==> ~(s INTER t = {})]])
  let h13 ← ar (← ExceptT.mk [[~(n + N + 1 <= N)]])
  let h12 ← sr
    (← ExceptT.mk [[interior(IMAGE f s) = IMAGE f s /\ ~(s = {})
    ==> ~(interior(IMAGE f s) SUBSET {})]])
  let h11 ← sr (← ExceptT.mk [[~(s SUBSET t) ==> ?z. z IN s /\ ~t z]])
  let h10 ← sr
    (← ExceptT.mk [[{x | P x /\ Q x /\ R x} =
    {x | R x} DIFF ({x | ~P x} UNION {x | ~Q x})]])
  let h9 ← sr
    (← ExceptT.mk [[(!x. real x ==> real(cexp x))
    ==> ~(s INTER real = {}) ==> ~(IMAGE cexp s INTER real = {})]])
  let h8 ← ms [(← ar (← ExceptT.mk [[~(n:num <= N) ==> n = N + (n - N)]]))]
    (← ExceptT.mk [[(!d:num. ~P (N + d)) ==> (!n. P n ==> n <= N)]])
  let h7 ← ar (← ExceptT.mk [[N < n ==> SUC n >= N]])
  let h6 ← rr
    (← ExceptT.mk [[d + y <= x /\ &1 + x <= exp x ==> (d + &1) + y <= exp(x) * &1]])
  let h5 ← ar (← ExceptT.mk [[(m + n) + d:num = n + (m + d)]])
  let h4 ← rr
    (← ExceptT.mk [[g + &1 - x <= m ==> m + x <= f ==> &1 <= abs(f - g)]])
  let h3 ← ms [COMPONENT_LE_NORM, REAL_LET_TRANS]
    (← ExceptT.mk [[norm(x) < &1 ==> abs(x$1) < &1]])
  let h2 ← sr (← ExceptT.mk [[P /\ x IN real <=> real x /\ P]])
  let h1 ← ar (← ExceptT.mk [[n >= N + 1 ==> N < n]])
  prove ([[!v. open v /\ connected v /\ ~(v = {})
       ==> ?q. (!m n. m < n ==> (q:num->num) m < q n) /\
               !r. (!m n. m < n ==> r m < r n) /\
                   ((!x. x IN v
                         ==> ((\n. inv (ITER (q(r n)) cexp x)) --> Cx (&0))
                             sequentially) /\
                    (!k c.
                         compact k /\ k SUBSET v
                         ==> (?N. !n x. n >= N /\ x IN k
                                        ==> c < norm(ITER (q(r n)) cexp x))) \/
                    (?g. g holomorphic_on v /\
                         (!x. x IN v
                              ==> ((\n. ITER (q(r n)) cexp x) --> g x)
                                  sequentially) /\
                         (!k e.
                              compact k /\ k SUBSET v /\ &0 < e
                              ==> (?N. !n x.
                                           n >= N /\ x IN k
                                           ==> norm(ITER (q(r n)) cexp x - g x)
                                                < e)))) ==> F]])
   (SUBGOAL_THEN
     ([[!v. ~(open v /\ connected v /\ bounded v /\ ~(v = {}) /\
            (!c. ?N. !n x. n >= N /\ x IN v ==> c < norm(ITER n cexp x)))]])
    ASSUME_TAC THENL
     [ALL_TAC,
      X_GEN_TAC ([[v:complex->bool]]) THEN STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [(← HolLight.GSYM MEMBER_NOT_EMPTY)]) THEN
      DISCH_THEN (X_CHOOSE_TAC ([[z:complex]])) THEN
      FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [OPEN_CONTAINS_BALL]) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[z:complex]])) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[d:real]]) STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[ball(z:complex,d / &2)]])) THEN
      ASM_REWRITE_TAC [OPEN_BALL, CONNECTED_BALL, BALL_EQ_EMPTY,
                      REAL_NOT_LE, REAL_HALF, BOUNDED_BALL] THEN
      ASM_REWRITE_TAC [NOT_FORALL_THM, NOT_EXISTS_THM, NOT_IMP] THEN
      REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC), REAL_NOT_LT] THEN
      DISCH_THEN (X_CHOOSE_TAC ([[c:real]])) THEN
      SUBGOAL_THEN
       ([[?q. (!n. ?x. x IN IMAGE (ITER (q n) cexp) (ball(z,d / &2)) /\
                     norm(x) <= c) /\
            (!n. q n < q(SUC n))]])
      STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC DEPENDENT_CHOICE THEN
        REWRITE_TAC [EXISTS_IN_IMAGE] THEN
        ASM_MESON_TAC [h1],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[!m n. m < n ==> (q:num->num) m < q n]]) ASSUME_TAC THENL
       [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN ASM_MESON_TAC [LT_TRANS],
        ALL_TAC] THEN
      EXISTS_TAC ([[q:num->num]]) THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC ([[p:num->num]]) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ABBREV_TAC ([[r n = (q:num->num) (p(n:num))]]) THEN
      SUBGOAL_THEN ([[!m n. m < n ==> (r:num->num) m < r n]]) MP_TAC THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN
       ([[!n:num. ?x. x IN IMAGE (ITER (r n) cexp) (ball(z,d / &2)) /\ norm x <= c]])
      MP_TAC THENL [ASM_MESON_TAC [], REWRITE_TAC [EXISTS_IN_IMAGE]] THEN
      REPEAT (FIRST_X_ASSUM (ifConcl HolCore.Basics.is_forall (HolCore.Lib.K ALL_TAC))) THEN
      REPEAT STRIP_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[cball(z:complex,d / &2)]]), ([[c:real]])]) THEN
        REWRITE_TAC [COMPACT_CBALL, NOT_IMP] THEN CONJ_TAC THENL
         [TRANS_TAC SUBSET_TRANS ([[ball(z:complex,d)]]) THEN
          ASM_REWRITE_TAC [SUBSET_BALLS, DIST_REFL] THEN ASM_REAL_ARITH_TAC,
          DISCH_THEN (X_CHOOSE_THEN ([[n:num]]) (MP_TAC o HolLight.SPEC ([[n:num]]))) THEN
          REWRITE_TAC [GE, LE_REFL, (← HolLight.GSYM REAL_NOT_LE)] THEN
          ASM_MESON_TAC [(← HolLight.REWRITE_RULE [SUBSET] BALL_SUBSET_CBALL)]],
        MP_TAC (← HolLight.SPEC ([[v:complex->bool]]) LEMMA_6) THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [(← HolLight.GSYM MEMBER_NOT_EMPTY), IN_INTER] THEN
        REWRITE_TAC [h2] THEN
        REWRITE_TAC [EXISTS_REAL, IN_IMAGE] THEN REWRITE_TAC [NOT_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [([[n:num]]), ([[x:real]]), ([[w:complex]])] THEN
        DISCH_THEN (STRIP_ASSUME_TAC o HolLight.GSYM) THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[w:complex]])) THEN
        ASM_REWRITE_TAC [LIM_SEQUENTIALLY] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[&1]])) THEN REWRITE_TAC [REAL_LT_01] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[N:num]]) (LABEL_TAC "*")) THEN
        MP_TAC (← HolLight.SPEC ([[Re(g(w:complex)) + &1 - x]]) REAL_ARCH_SIMPLE) THEN
        DISCH_THEN (X_CHOOSE_TAC ([[M:num]])) THEN
        REMOVE_THEN "*" (MP_TAC o HolLight.SPEC ([[N + M + n:num]])) THEN
        REWRITE_TAC [LE_ADD, dist] THEN
        DISCH_THEN (MP_TAC o HolLight.MATCH_MP h3) THEN
        REWRITE_TAC [(← HolLight.GSYM RE_DEF), RE_SUB, REAL_NOT_LT] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h4) THEN
        TRANS_TAC REAL_LE_TRANS ([[(&N + &M) + x:real]]) THEN CONJ_TAC THENL
         [REAL_ARITH_TAC2, REWRITE_TAC [REAL_OF_NUM_ADD, ADD_ASSOC]] THEN
        SPEC_TAC (([[N + M:num]]), ([[m:num]])) THEN GEN_TAC THEN
        SUBGOAL_THEN ([[m + n <= (r:num->num) (m + n)]]) MP_TAC THENL
         [ASM_MESON_TAC [MONOTONE_BIGGER], REWRITE_TAC [LE_EXISTS]] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[d:num]]) SUBST1_TAC) THEN
        TRANS_TAC REAL_LE_TRANS ([[(&m + &d) + x:real]]) THEN CONJ_TAC THENL
         [REAL_ARITH_TAC2, REWRITE_TAC [REAL_OF_NUM_ADD, ADD_ASSOC]] THEN
        ONCE_REWRITE_TAC [h5] THEN
        SPEC_TAC (([[m + d:num]]), ([[d:num]])) THEN
        SUBGOAL_THEN
         ([[!d. real(ITER (n + d) cexp w) /\
              &d + x <= Re(ITER (n + d) cexp w)]])
         (fun th => MESON_TAC [th]) THEN
        INDUCT_TAC THEN
        ASM_SIMP_TAC [ADD_CLAUSES, ITER, REAL_CX, RE_CX, REAL_ADD_LID,
                     REAL_LE_REFL, REAL_EXP, RE_CEXP] THEN
        RULE_ASSUM_TAC (HolLight.REWRITE_RULE [real]) THEN
        ASM_REWRITE_TAC [COS_0, (← HolLight.GSYM REAL_OF_NUM_SUC)] THEN
        MATCH_MP_TAC h6 THEN
        ASM_REWRITE_TAC [REAL_EXP_LE_X]]] THEN
    REPEAT STRIP_TAC THEN
    MAP_EVERY ABBREV_TAC
     [([[h = {z | Re z > &4}]]),
      ([[s = {z | abs(Im z) <= pi / &3}]]),
      ([[w = {z | abs(Im z) <= &2 * pi /\ abs(Im(cexp z)) <= &2 * pi}]])] THEN
    SUBGOAL_THEN
     ([[FINITE {n | ~(IMAGE (ITER n cexp) v SUBSET h)}]])
    ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[exp(&4)]])) THEN
      DISCH_THEN (X_CHOOSE_TAC ([[N:num]])) THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[0..N]]) THEN
      REWRITE_TAC [FINITE_NUMSEG, SUBSET, IN_NUMSEG, IN_ELIM_THM, LE_0] THEN
      X_GEN_TAC ([[n:num]]) THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM CONTRAPOS_THM)] THEN
      REWRITE_TAC [NOT_LE] THEN DISCH_TAC THEN
      X_GEN_TAC ([[w:complex]]) THEN DISCH_TAC THEN EXPAND_TAC "h" THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[n + 1]]), ([[w:complex]])]) THEN
      REWRITE_TAC [IN_ELIM_THM] THEN
      ASM_SIMP_TAC [h7, (← HolLight.GSYM ADD1)] THEN
      REWRITE_TAC [real_gt, ITER, NORM_CEXP, REAL_EXP_MONO_LT],
      ALL_TAC] THEN
    SUBGOAL_THEN
      ([[FINITE {n | DISJOINT (IMAGE (ITER n cexp) v) real}]])
    ASSUME_TAC THENL
     [MP_TAC (← HolLight.SPEC ([[v:complex->bool]]) LEMMA_6) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[N:num]]) (LABEL_TAC "*")) THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC ([[0..N]]) THEN
      REWRITE_TAC [FINITE_NUMSEG, SUBSET, IN_NUMSEG, LE_0, IN_ELIM_THM] THEN
      MATCH_MP_TAC h8 THEN
      REWRITE_TAC [DISJOINT] THEN MATCH_MP_TAC num_INDUCTION THEN
      ASM_REWRITE_TAC [ADD_CLAUSES, ITER_POINTLESS] THEN X_GEN_TAC ([[d:num]]) THEN
      REWRITE_TAC [IMAGE_o] THEN MATCH_MP_TAC h9 THEN
      REWRITE_TAC [REAL_EXP],
      ALL_TAC] THEN
    SUBGOAL_THEN
      ([[INFINITE {n | IMAGE (ITER n cexp) v SUBSET h /\
                     ~(DISJOINT (IMAGE (ITER n cexp) v) real) /\
                     ~(IMAGE (ITER n cexp) v SUBSET s)}]])
    ASSUME_TAC THENL
     [REWRITE_TAC [h10] THEN
      MATCH_MP_TAC INFINITE_DIFF_FINITE THEN
      ASM_REWRITE_TAC [FINITE_UNION, INFINITE] THEN
      DISCH_THEN (MP_TAC o HolLight.ISPEC ([[\n:num. n]]) o
        HolLight.MATCH_MP UPPER_BOUND_FINITE_SET) THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM, FORALL_IN_GSPEC] THEN
      X_GEN_TAC ([[N:num]]) THEN
      SUBGOAL_THEN ([[?z. z IN IMAGE (ITER (N + 1) cexp) v /\ ~(real z)]])
      STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC h11 THEN
        DISCH_THEN (MP_TAC o HolLight.MATCH_MP SUBSET_INTERIOR) THEN
        REWRITE_TAC [INTERIOR_REAL] THEN MATCH_MP_TAC h12 THEN
        ASM_REWRITE_TAC [INTERIOR_EQ] THEN
        SPEC_TAC (([[N + 1]]), ([[n:num]])) THEN
        INDUCT_TAC THEN ASM_REWRITE_TAC [ITER_POINTLESS, IMAGE_I, IMAGE_o] THEN
        MATCH_MP_TAC (← HolLight.REWRITE_RULE [RIGHT_IMP_FORALL_THM, IMP_IMP]
           OPEN_MAPPING_THM) THEN
        EXISTS_TAC ([[IMAGE (ITER n cexp) v]]) THEN
        ASM_REWRITE_TAC [SUBSET_REFL, HOLOMORPHIC_ON_CEXP] THEN
        ASM_SIMP_TAC [CONNECTED_CONTINUOUS_IMAGE, CONTINUOUS_ON_ITER_CEXP] THEN
        DISCH_THEN (X_CHOOSE_TAC ([[c:complex]])) THEN
        SUBGOAL_THEN ([[?x. x IN IMAGE (ITER n cexp) v]]) STRIP_ASSUME_TAC THENL
         [HolLight.ASM SET_TAC [], ALL_TAC] THEN
        MP_TAC (← HolLight.ISPEC ([[x:complex]]) CEXP_NZ) THEN REWRITE_TAC [] THEN
        MATCH_MP_TAC COMPLEX_DERIVATIVE_UNIQUE_AT THEN
        MAP_EVERY EXISTS_TAC [([[cexp]]), ([[x:complex]])] THEN
        REWRITE_TAC [HAS_COMPLEX_DERIVATIVE_CEXP] THEN
        MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
        MAP_EVERY EXISTS_TAC
         [([[(\z. c):complex->complex]]), ([[IMAGE (ITER n cexp) v]])] THEN
        ASM_REWRITE_TAC [HAS_COMPLEX_DERIVATIVE_CONST] THEN ASM_MESON_TAC [],
        FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP LEMMA_2b) THEN
        EXPAND_TAC "s" THEN REWRITE_TAC [real_gt, IN_ELIM_THM, SUBSET] THEN
        DISCH_THEN (X_CHOOSE_TAC ([[n:num]])) THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[n + N + 1:num]])) THEN REWRITE_TAC [] THEN
        ONCE_REWRITE_TAC [ITER_ADD_POINTLESS] THEN
        SIMP_TAC [h13, IMAGE_o, (← HolLight.GSYM REAL_NOT_LT)] THEN
        HolLight.ASM SET_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[INFINITE {n | ~(IMAGE (ITER n cexp) v SUBSET w)}]])
    ASSUME_TAC THENL
     [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ]
          INFINITE_SUPERSET)) THEN
      GEN_REWRITE_TAC HolCore.Lib.I [SUBSET] THEN X_GEN_TAC ([[n:num]]) THEN
      REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MP_TAC (← HolLight.ISPECL [([[IMAGE (ITER n cexp) v]]), ([[s:complex->bool]])]
          CONNECTED_INTER_FRONTIER) THEN
      ASM_SIMP_TAC [CONNECTED_CONTINUOUS_IMAGE, CONTINUOUS_ON_ITER_CEXP] THEN
      REWRITE_TAC [NOT_IMP] THEN REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h14) THEN
        EXPAND_TAC "s" THEN SIMP_TAC [real, IN_ELIM_THM, SUBSET] THEN
        MP_TAC PI_POS THEN REAL_ARITH_TAC2,
        HolLight.ASM SET_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[DISJOINT (frontier s) (w INTER h:complex->bool)]])
      ASSUME_TAC THENL [ALL_TAC, HolLight.ASM SET_TAC []] THEN
      EXPAND_TAC "s" THEN
      REWRITE_TAC [IM_DEF, FRONTIER_STRIP_COMPONENT_LE] THEN
      REWRITE_TAC [(← HolLight.GSYM IM_DEF)] THEN MATCH_MP_TAC h15 THEN
      MAP_EVERY EXPAND_TAC ["h", "w"] THEN REWRITE_TAC [IN_ELIM_THM] THEN
      X_GEN_TAC ([[z:complex]]) THEN REWRITE_TAC [IM_CEXP, real_gt] THEN
      STRIP_TAC THEN DISCH_THEN (MP_TAC o HolLight.CONJUNCT2) THEN
      REWRITE_TAC [REAL_NOT_LE, REAL_ABS_MUL, REAL_ABS_EXP] THEN
      SUBGOAL_THEN ([[abs(sin(Im z)) = sqrt(&3) / &2]]) SUBST1_TAC THENL
       [FIRST_X_ASSUM (DISJ_CASES_THEN SUBST1_TAC o HolLight.MATCH_MP h16) THEN
        REWRITE_TAC [SIN_NEG, SIN_PI3, REAL_ABS_NEG] THEN
        SIMP_TAC [REAL_ABS_REFL, REAL_LE_DIV, SQRT_POS_LE, REAL_POS],
        ALL_TAC] THEN
      MATCH_MP_TAC h17 THEN
      CONJ_TAC THENL [MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC2, ALL_TAC] THEN
      MATCH_MP_TAC h18 THEN
      CONJ_TAC THENL
       [TRANS_TAC REAL_LE_TRANS ([[exp(&4 * &1)]]) THEN CONJ_TAC THENL
         [REWRITE_TAC [REAL_EXP_N] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
          MP_TAC E_APPROX_32 THEN REAL_ARITH_TAC2,
          REWRITE_TAC [REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC],
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_EXP_POS_LE] THEN
        SUBST1_TAC (← HolLight.SYM SQRT_1) THEN MATCH_MP_TAC SQRT_MONO_LE THEN
        CONV_TAC REAL_RAT_REDUCE_CONV],
      ALL_TAC] THEN
    SUBGOAL_THEN
     ([[INFINITE {n | ~(IMAGE (ITER n cexp) v SUBSET {z | abs(Im z) <= &2 * pi}) /\
                    ~DISJOINT (IMAGE (ITER n cexp) v) real}]])
    ASSUME_TAC THENL
     [REWRITE_TAC [h19] THEN
      MATCH_MP_TAC INFINITE_DIFF_FINITE THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC ([[INFINITE {n | ~(IMAGE (ITER n cexp) v SUBSET w)}]]) THEN
      REWRITE_TAC [INFINITE, CONTRAPOS_THM] THEN
      EXPAND_TAC "w" THEN
      REWRITE_TAC [h20,
                  SUBSET_INTER, FINITE_SUBSET_NUMSEG] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[n:num]]) THEN
      ONCE_REWRITE_TAC [SUBSET] THEN REWRITE_TAC [IN_NUMSEG, LE_0] THEN
      REWRITE_TAC [IN_ELIM_THM, CONTRAPOS_THM, (← HolLight.GSYM NOT_LT)] THEN
      DISCH_THEN (fun th => HolLight.tactic_of do
        pure (X_GEN_TAC ([[k:num]]) THEN DISCH_TAC THEN
              MP_TAC (← HolLight.SPEC ([[k:num]]) th) THEN
              MP_TAC (← HolLight.SPEC ([[SUC k]]) th))) THEN
      ASM_SIMP_TAC [LT_SUC_LE, LT_IMP_LE, ITER_POINTLESS] THEN
      REWRITE_TAC [IMAGE_o] THEN SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     ([[INFINITE {n | ~(IMAGE (ITER n cexp) v INTER {x | abs(Im x) = pi} = {})}]])
    MP_TAC THENL
     [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ]
        INFINITE_SUPERSET)) THEN
      GEN_REWRITE_TAC HolCore.Lib.I [SUBSET] THEN X_GEN_TAC ([[n:num]]) THEN
      REWRITE_TAC [IN_ELIM_THM] THEN
      REWRITE_TAC [(← HolLight.GSYM MEMBER_NOT_EMPTY), SUBSET, DISJOINT, IN_ELIM_THM] THEN
      REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, IN_INTER, REAL_NOT_LE, real,
                  IN_ELIM_THM, h21] THEN
      DISCH_THEN (CONJUNCTS_THEN2
       (X_CHOOSE_THEN ([[b:complex]]) STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN ([[a:complex]]) STRIP_ASSUME_TAC)) THEN
      MP_TAC (← HolLight.ISPECL
       [([[IMAGE (lift o abs o Im) (IMAGE (ITER n cexp) v)]]),
        ([[(lift o abs o Im) a]]), ([[(lift o abs o Im) b]]),
        ([[pi]]), ([[1]])] CONNECTED_IVT_COMPONENT) THEN
      ASM_SIMP_TAC [DIMINDEX_1, LE_REFL, FUN_IN_IMAGE] THEN
      GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [EXISTS_IN_IMAGE] THEN
      REWRITE_TAC [(← HolLight.GSYM drop), o_THM, LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL [ALL_TAC, MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC [CONNECTED_CONTINUOUS_IMAGE, CONTINUOUS_ON_ITER_CEXP] THEN
      REWRITE_TAC [o_DEF, IM_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS_COMPONENT THEN
      REWRITE_TAC [CONTINUOUS_ON_ID],
      REWRITE_TAC [INFINITE]] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[&1]])) THEN REWRITE_TAC [FINITE_SUBSET_NUMSEG] THEN
    REWRITE_TAC [SUBSET, GE, IN_NUMSEG, LE_0, IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[N:num]]) THEN
    REWRITE_TAC [(← HolLight.GSYM NOT_LT), CONTRAPOS_THM] THEN
    REWRITE_TAC [IN_ELIM_THM, NOT_LT,
      h22] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
     pure (X_GEN_TAC ([[n:num]]) THEN DISCH_TAC THEN X_GEN_TAC ([[x:complex]]) THEN
           DISCH_TAC THEN MP_TAC (← HolLight.ISPECL [([[SUC(SUC n)]]), ([[x:complex]])] th))) THEN
    ASM_SIMP_TAC [h23, (← HolLight.GSYM REAL_NOT_LE),
                 CONTRAPOS_THM] THEN
    SIMP_TAC [ITER, NORM_CEXP, RE_CEXP] THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM COS_ABS)] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [COS_PI, (← HolLight.GSYM REAL_EXP_0), REAL_EXP_MONO_LE] THEN
    REWRITE_TAC [REAL_EXP_0, h24] THEN
    REWRITE_TAC [REAL_EXP_POS_LE])
  : ExceptT String IO thm).run
#eval THEOREM

-- ------------------------------------------------------------------------- --
-- Hence a strong form of topological transitivity.                          --
-- ------------------------------------------------------------------------- --

#eval phrase 17
def STRONG : thm := keep "STRONG" fun _ => (do
  let h3 ← tt (← ExceptT.mk [[p ==> q /\ r <=> (p ==> q) /\ (p ==> r)]])
  let h2 ← ms [] (← ExceptT.mk [[((!x. ~P x) ==> F) ==> ?x. P x]])
  let h1 ← sr
    (← ExceptT.mk [[s SUBSET t ==> a IN IMAGE f s ==> a IN IMAGE f t]])
  prove ([[!u a. open u /\ ~(u = {}) /\ ~(a = Cx(&0))
         ==> ?n. a IN IMAGE (ITER n cexp) u]])
   (SUBGOAL_THEN
     ([[!v a. open v /\ ~(v = {}) /\ connected v /\ ~(Cx(&0) IN v) /\ ~(a = Cx(&0))
           ==> ?n. a IN IMAGE (ITER n cexp) v]])
    ASSUME_TAC THENL
     [ALL_TAC,
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN ([[~(u SUBSET {Cx(&0),a})]]) MP_TAC THENL
       [DISCH_THEN (MP_TAC o HolLight.MATCH_MP
          (← HolLight.REWRITE_RULE [IMP_CONJ_ALT] FINITE_SUBSET)) THEN
        REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY] THEN
        ASM_MESON_TAC [FINITE_IMP_NOT_OPEN],
        REWRITE_TAC [SUBSET, IN_INSERT, NOT_IN_EMPTY, NOT_FORALL_THM,
                    NOT_IMP, DE_MORGAN_THM] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[b:complex]]) STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [OPEN_CONTAINS_BALL]) THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[b:complex]])) THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[r:real]]) STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.SPECL
         [([[ball(b:complex,min r (min (norm b) (dist(b,a))))]]), ([[a:complex]])]) THEN
        ASM_REWRITE_TAC [OPEN_BALL, CONNECTED_BALL, BALL_EQ_EMPTY] THEN
        ASM_REWRITE_TAC [REAL_NOT_LE, REAL_LT_MIN, (← HolLight.GSYM DIST_NZ),
                        COMPLEX_NORM_NZ] THEN
        REWRITE_TAC [IN_BALL, dist, COMPLEX_SUB_RZERO] THEN
        ANTS_TAC THENL [REAL_ARITH_TAC2, MATCH_MP_TAC MONO_EXISTS] THEN
        GEN_TAC THEN MATCH_MP_TAC h1 THEN
        TRANS_TAC SUBSET_TRANS ([[ball(b:complex,r)]]) THEN
        ASM_REWRITE_TAC [SUBSET_BALLS, DIST_REFL] THEN REAL_ARITH_TAC2]] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC h2 THEN
    DISCH_TAC THEN MP_TAC (← HolLight.SPEC ([[v:complex->bool]]) THEOREM) THEN
    ASM_REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC ([[q:num->num]]) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC (← HolLight.ISPECL [([[\n:num. ITER (q n) cexp]]), ([[{ITER n cexp | n IN (:num)}]]),
              ([[v:complex->bool]]), ([[Cx(&0)]]), ([[a:complex]])] MONTEL_OMITTING) THEN
    ASM_REWRITE_TAC [NOT_IMP, NOT_FORALL_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [REWRITE_TAC [FORALL_IN_GSPEC], SET_TAC []] THEN
    REWRITE_TAC [IN_UNIV, HOLOMORPHIC_ON_ITER_CEXP] THEN
    REWRITE_TAC [h3] THEN
    REWRITE_TAC [FORALL_AND_THM] THEN
    CONJ_TAC THENL [ALL_TAC, HolLight.ASM SET_TAC []] THEN
    INDUCT_TAC THEN REWRITE_TAC [ITER, CEXP_NZ] THEN HolLight.ASM SET_TAC [])
  : ExceptT String IO thm).run
#eval STRONG

-- ------------------------------------------------------------------------- --
-- The usual formulation.                                                    --
-- ------------------------------------------------------------------------- --

#eval phrase 18
def COROLLARY : thm := keep "COROLLARY" fun _ => (do
  let h1 ← sr
    (← ExceptT.mk [[~(s SUBSET {z}) ==> ?a. a IN s /\ ~(a = z)]])
  prove ([[!u v. open u /\ ~(u = {}) /\ open v /\ ~(v = {})
         ==> ?n. ~(IMAGE (ITER n cexp) u INTER v = {})]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[~(v SUBSET {Cx(&0)})]]) MP_TAC THENL
     [DISCH_THEN (MP_TAC o HolLight.MATCH_MP
        (← HolLight.REWRITE_RULE [IMP_CONJ_ALT] FINITE_SUBSET)) THEN
      REWRITE_TAC [FINITE_SING] THEN ASM_MESON_TAC [FINITE_IMP_NOT_OPEN],
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP h1) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[b:complex]]) STRIP_ASSUME_TAC)] THEN
    MP_TAC (← HolLight.ISPECL [([[u:complex->bool]]), ([[b:complex]])]
          STRONG) THEN
    ASM_REWRITE_TAC [] THEN HolLight.ASM SET_TAC [])
  : ExceptT String IO thm).run
#eval COROLLARY

end HolExamples.Misiurewicz
