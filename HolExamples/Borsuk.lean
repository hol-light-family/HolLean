/- File: HolExamples/Borsuk.lean
Translation of HOL Light's Examples/borsuk.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
import SessionMultiLib.MoreTop
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionLibrary.Floor
open SessionMultiLib.Misc SessionMultiLib.Vectors SessionMultiLib.Determinants
open SessionMultiLib.Metric SessionMultiLib.Topology SessionMultiLib.Convex
open SessionMultiLib.Paths SessionMultiLib.ComplexAlgebra SessionMultiLib.Complexes SessionMultiLib.Canal
open SessionMultiLib.Transcendentals SessionMultiLib.RealAnalysis SessionMultiLib.MoreTop
namespace HolExamples.Borsuk

/- Helpers: the session's `prove` lifted into `ExceptT String IO`, so tactic
   scripts read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)
private def va (tm : term) : ExceptT String IO thm := ExceptT.mk (VECTOR_ARITH tm)
private def na (tm : term) : ExceptT String IO thm := ExceptT.mk (NORM_ARITH tm)
private def cr (tm : term) : ExceptT String IO thm := ExceptT.mk (COMPLEX_RING tm)
private def cf (tm : term) : ExceptT String IO thm := ExceptT.mk (COMPLEX_FIELD tm)

-- ========================================================================= --
-- Borsuk-Ulam theorem for an ordinary 2-sphere in real^3.                   --
-- From Andrew Browder's article, AMM vol. 113 (2006), pp. 935-6             --
-- ========================================================================= --

#eval phrase 1
-- needs "Multivariate/moretop.ml";;
#eval SessionMultiLib.MoreTop.ensureMoreTop

-- ------------------------------------------------------------------------- --
-- The Borsuk-Ulam theorem for the unit sphere.                              --
-- ------------------------------------------------------------------------- --

#eval phrase 2
def THEOREM_1 : thm := keep "THEOREM_1" fun _ => (do
  -- OCaml builds the tactic right to left: the build-time rules run
  -- bottom-first, so their traces print in that order.
  let b16 ← rr ([[a / &2 = n <=> a = &2 * n]])
  let b15 ← rr ([[&2 * n + &1 = &0 <=> n = --(&1 / &2)]])
  let b14 ← cr ([[~(z = Cx(&0)) ==> a - b = z ==> ~(b - a = z)]])
  let b13 ← rr
     ([[~(abs(x - y) < &1) ==> &1 <= abs((&2 * x + &1) - (&2 * y + &1))]])
  let b12 ← na ([[norm z = dist(vec 0,z)]])
  let b11 ← cf
     ([[~(p = Cx(&0))
    ==> (p * ii * m = p * ii + (t * n * p) * ii <=> m = t * n + Cx(&1))]])
  let b10 ← cf
     ([[~(y = Cx(&0)) /\ x = -- y ==> x / y = Cx(-- &1)]])
  let b9 ← cf
     ([[~(p = Cx(&0)) ==> p * ii * h * inv(p * ii) = h]])
  let b8 ← rr ([[r + i + s = &1 <=> s = &1 - (r + i)]])
  let b7 ← cr ([[x - y = Cx(&0) <=> y = x]])
  let b4 ← tt ([[a /\ (a /\ b ==> c) ==> (a ==> b) ==> c]])
  let b2 ← tt ([[~(a /\ b) <=> a ==> ~b]])
  let b1 ← tt ([[p <=> ~ ~ p]])
  prove ([[!f:real^3->real^2.
        f continuous_on {x | norm(x) = &1}
        ==> ?x. norm(x) = &1 /\ f(--x) = f(x)]])
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC HolCore.Lib.I [b1] THEN
    PURE_REWRITE_TAC [NOT_EXISTS_THM, b2] THEN
    DISCH_TAC THEN
    ABBREV_TAC ([[(g:real^3->real^2) = \x. f(x) - f(--x)]]) THEN
    ABBREV_TAC ([[k = \z. (g:real^3->real^2)
                        (vector[Re z; Im z; sqrt(&1 - norm z pow 2)])]]) THEN
    MP_TAC (← HolLight.ISPECL [([[k:complex->complex]]), ([[Cx(&0)]]), ([[&1]])]
          CONTINUOUS_LOGARITHM_ON_CBALL) THEN
    MATCH_MP_TAC b4 THEN
    CONJ_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "k" THEN
        MATCH_MP_TAC (← HolLight.REWRITE_RULE [o_DEF] CONTINUOUS_ON_COMPOSE) THEN
        CONJ_TAC THENL
         [REWRITE_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN,
                      CONTINUOUS_COMPONENTWISE] THEN
          SIMP_TAC [DIMINDEX_3, FORALL_3, VECTOR_3, ETA_AX] THEN
          REWRITE_TAC [REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN] THEN
          X_GEN_TAC ([[z:complex]]) THEN DISCH_TAC THEN
          MATCH_MP_TAC (← HolLight.REWRITE_RULE [o_DEF] REAL_CONTINUOUS_WITHIN_COMPOSE) THEN
          SIMP_TAC [REAL_CONTINUOUS_SUB, REAL_CONTINUOUS_POW,
                   REAL_CONTINUOUS_CONST, REAL_CONTINUOUS_NORM_WITHIN] THEN
          MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_SUBSET THEN
          EXISTS_TAC ([[{t | &0 <= t}]]) THEN
          REWRITE_TAC [REAL_CONTINUOUS_WITHIN_SQRT] THEN
          SIMP_TAC [SUBSET, FORALL_IN_IMAGE, IN_CBALL, IN_ELIM_THM, dist,
                   COMPLEX_SUB_LZERO, NORM_NEG, REAL_SUB_LE] THEN
          REWRITE_TAC [ABS_SQUARE_LE_1, REAL_ABS_NORM],
          ALL_TAC] THEN
        EXPAND_TAC "g" THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        CONJ_TAC THENL
         [ALL_TAC,
          MATCH_MP_TAC (← HolLight.REWRITE_RULE [o_DEF] CONTINUOUS_ON_COMPOSE) THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC [linear] THEN
            CONJ_TAC THEN VECTOR_ARITH_TAC,
            REWRITE_TAC [(← HolLight.GSYM IMAGE_o)]]] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC ([[{x:real^3 | norm x = &1}]]) THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, o_THM, IN_ELIM_THM] THEN
        SIMP_TAC [NORM_EQ_1, DOT_3, VECTOR_3, VECTOR_NEG_COMPONENT, dist,
                 DIMINDEX_3, ARITH, IN_CBALL, COMPLEX_SUB_LZERO, NORM_NEG] THEN
        REWRITE_TAC [REAL_NEG_MUL2] THEN X_GEN_TAC ([[z:complex]]) THEN DISCH_TAC,
        X_GEN_TAC ([[z:complex]]) THEN
        REWRITE_TAC [dist, IN_CBALL, COMPLEX_SUB_LZERO, NORM_NEG] THEN
        DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["k", "g"] THEN
        REWRITE_TAC [b7] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC [NORM_EQ_1, DOT_3, VECTOR_3]] THEN
      REWRITE_TAC [(← HolLight.GSYM REAL_POW_2), COMPLEX_SQNORM] THEN
      REWRITE_TAC [b8] THEN
      MATCH_MP_TAC SQRT_POW_2 THEN REWRITE_TAC [(← HolLight.GSYM COMPLEX_SQNORM)] THEN
      ASM_SIMP_TAC [REAL_SUB_LE, ABS_SQUARE_LE_1, REAL_ABS_NORM],
      ALL_TAC] THEN
    DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[h:complex->complex]]) STRIP_ASSUME_TAC) THEN
    ABBREV_TAC ([[m = \z:complex. (h(z) - h(--z)) / (Cx pi * ii)]]) THEN
    SUBGOAL_THEN
      ([[!z:complex. norm(z) = &1 ==> cexp(Cx pi * ii * m z) = cexp(Cx pi * ii)]])
    MP_TAC THENL
     [EXPAND_TAC "m" THEN
      REWRITE_TAC [COMPLEX_SUB_LDISTRIB, complex_div, COMPLEX_SUB_RDISTRIB] THEN
      SIMP_TAC [CX_INJ, PI_NZ, CEXP_SUB, b9] THEN
      X_GEN_TAC ([[z:complex]]) THEN DISCH_TAC THEN
      SUBGOAL_THEN ([[cexp(h z) = k z /\ cexp(h(--z:complex)) = k(--z)]])
       (CONJUNCTS_THEN SUBST1_TAC)
      THENL
       [CONJ_TAC THEN CONV_TAC HolLight.SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC [dist, IN_CBALL, COMPLEX_SUB_LZERO, NORM_NEG, REAL_LE_REFL],
        ALL_TAC] THEN
      REWRITE_TAC [EULER, RE_MUL_CX, IM_MUL_CX, RE_II, IM_II, COMPLEX_ADD_RID,
                  REAL_MUL_RZERO, REAL_MUL_RID, SIN_PI, COS_PI, REAL_EXP_0,
                  COMPLEX_MUL_RZERO, COMPLEX_MUL_LID] THEN
      MATCH_MP_TAC b10 THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC [dist, IN_CBALL, COMPLEX_SUB_LZERO, NORM_NEG, REAL_LE_REFL],
        MAP_EVERY EXPAND_TAC ["k", "g"] THEN
        REWRITE_TAC [COMPLEX_NEG_SUB] THEN BINOP_TAC THEN AP_TERM_TAC THEN
        SIMP_TAC [CART_EQ, FORALL_3, VECTOR_3, VECTOR_NEG_COMPONENT,
                 DIMINDEX_3, ARITH, RE_NEG, IM_NEG, NORM_NEG, REAL_NEG_NEG] THEN
        ASM_REWRITE_TAC [] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REWRITE_TAC [SQRT_0, REAL_NEG_0]],
      ALL_TAC] THEN
    REWRITE_TAC [CEXP_EQ, CX_MUL] THEN
    SIMP_TAC [CX_INJ, PI_NZ, b11] THEN
    REWRITE_TAC [(← HolLight.GSYM CX_ADD), (← HolLight.GSYM CX_MUL)] THEN
    DISCH_THEN (LABEL_TAC "*") THEN
    SUBGOAL_THEN
     ([[?n. !z. z IN {z | norm(z) = &1} ==> (m:complex->complex)(z) = n]])
    MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_DISCRETE_RANGE_CONSTANT THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC [b12] THEN
        SIMP_TAC [(← HolLight.GSYM sphere), CONNECTED_SPHERE, DIMINDEX_2, LE_REFL],
        ALL_TAC] THEN
      CONJ_TAC THENL
       [EXPAND_TAC "m" THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN
        SIMP_TAC [CONTINUOUS_ON_CONST, COMPLEX_ENTIRE, II_NZ, CX_INJ, PI_NZ] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
         [ALL_TAC,
          MATCH_MP_TAC (← HolLight.REWRITE_RULE [o_DEF] CONTINUOUS_ON_COMPOSE) THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC [linear] THEN
            CONJ_TAC THEN VECTOR_ARITH_TAC,
            REWRITE_TAC [(← HolLight.GSYM IMAGE_o)]]] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP
         (← HolLight.REWRITE_RULE [IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
        SIMP_TAC [SUBSET, FORALL_IN_IMAGE, NORM_NEG, IN_CBALL,
                 COMPLEX_SUB_LZERO, dist, IN_ELIM_THM, REAL_LE_REFL],
        ALL_TAC] THEN
      X_GEN_TAC ([[z:complex]]) THEN REWRITE_TAC [IN_ELIM_THM] THEN
      DISCH_TAC THEN EXISTS_TAC ([[&1]]) THEN REWRITE_TAC [REAL_LT_01] THEN
      X_GEN_TAC ([[w:complex]]) THEN STRIP_TAC THEN
      REMOVE_THEN "*" (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC ([[w:complex]]) th) THEN
              MP_TAC (← HolLight.SPEC ([[z:complex]]) th))) THEN
      ASM_REWRITE_TAC [] THEN
      REPEAT (DISCH_THEN (CHOOSE_THEN
       (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
      REWRITE_TAC [(← HolLight.GSYM CX_SUB), COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC b13 THEN
      ASM_SIMP_TAC [(← HolLight.GSYM REAL_EQ_INTEGERS)] THEN ASM_MESON_TAC [],
      REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_TAC ([[v:complex]]))] THEN
    SUBGOAL_THEN
      ([[?n. integer n /\ !z:complex. norm z = &1 ==> m z = Cx(&2 * n + &1)]])
    MP_TAC THENL
     [REMOVE_THEN "*" (MP_TAC o HolLight.SPEC ([[Cx(&1)]])) THEN
      ASM_SIMP_TAC [COMPLEX_NORM_CX, REAL_ABS_NUM] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[n:real]]) MP_TAC) THEN EXPAND_TAC "m" THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
      pure (MP_TAC (← HolLight.SPEC ([[--Cx(&1)]]) th) THEN
            MP_TAC (← HolLight.SPEC ([[Cx(&1)]]) th))) THEN
    REWRITE_TAC [NORM_NEG, COMPLEX_NORM_CX, REAL_ABS_NUM, COMPLEX_NEG_NEG] THEN
    REWRITE_TAC [complex_div, COMPLEX_SUB_RDISTRIB] THEN
    MATCH_MP_TAC b14 THEN
    REWRITE_TAC [CX_INJ, b15] THEN
    UNDISCH_TAC ([[integer n]]) THEN
    GEN_REWRITE_TAC HolCore.Lib.I [(← HolLight.GSYM CONTRAPOS_THM)] THEN
    SIMP_TAC [] THEN DISCH_TAC THEN REWRITE_TAC [integer] THEN
    REWRITE_TAC [REAL_ABS_NEG, REAL_ABS_DIV, REAL_ABS_NUM] THEN
    REWRITE_TAC [b16] THEN
    REWRITE_TAC [NOT_EXISTS_THM, REAL_OF_NUM_MUL, REAL_OF_NUM_EQ] THEN
    GEN_TAC THEN DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[EVEN]])) THEN
    REWRITE_TAC [EVEN_MULT, ARITH])
  : ExceptT String IO thm).run
#eval THEOREM_1

-- ------------------------------------------------------------------------- --
-- The Borsuk-Ulam theorem for a general sphere.                             --
-- ------------------------------------------------------------------------- --

#eval phrase 3
def BORSUK_ULAM : thm := keep "BORSUK_ULAM" fun _ => (do
  let b2 ← va ([[a - r % x:real^3 = a + r % --x]])
  prove ([[!f:real^3->real^2 a r.
        &0 <= r /\ f continuous_on {z | norm(z - a) = r}
        ==> ?x. norm(x) = r /\ f(a + x) = f(a - x)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPEC ([[\x. (f:real^3->real^2) (a + r % x)]]) THEOREM_1) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [MATCH_MP_TAC (← HolLight.REWRITE_RULE [o_DEF] CONTINUOUS_ON_COMPOSE) THEN
      SIMP_TAC [CONTINUOUS_ON_ADD, CONTINUOUS_ON_CONST,
               CONTINUOUS_ON_CMUL, CONTINUOUS_ON_ID] THEN
      FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← HolLight.REWRITE_RULE [IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM],
      DISCH_THEN (X_CHOOSE_THEN ([[x:real^3]]) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC ([[r % x:real^3]]) THEN
      ASM_REWRITE_TAC [b2]] THEN
    ASM_SIMP_TAC [VECTOR_ADD_SUB, NORM_MUL] THEN ASM_REAL_ARITH_TAC)
  : ExceptT String IO thm).run
#eval BORSUK_ULAM

end HolExamples.Borsuk
