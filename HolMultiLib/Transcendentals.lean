/- ========================================================================= -/
/- Real and complex transcendental functions.                                -/
/- ========================================================================= -/
/- File: HolMultiLib/Transcendentals.lean

  Original (c) Copyright, John Harrison 1998-2008 (see transcendentals.ml).
  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/transcendentals.ml`, in the style of
  HolMultiLib/Measure.lean: pure, the proofs translated by hand, one `let`
  per OCaml `let`, in file order.  The load-time effects are at their file
  positions.  What transcendentals.ml uses from earlier files is passed in `TranscendentalsDeps`.
  SessionMultiLib/Transcendentals.lean supplies it.
-/

import HolMultiLib.Canal

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolMultiLib.Transcendentals

/- The theorems transcendentals.ml uses that the deps chain does not carry, grouped by the
   file that proves them. -/

structure QTopologyThms where
  (CLOSED_PCROSS CONTINUOUS_AT_COMPOSE CONTINUOUS_DISCRETE_RANGE_CONSTANT
   CONTINUOUS_ON_LIFT_DET CONTINUOUS_WITHIN_CLOSED_NONTRIVIAL
   EVENTUALLY_AT_POSINFINITY LIM_CASES_FINITE_SEQUENTIALLY
   LIM_POSINFINITY_SEQUENTIALLY RIGHT_POLAR_DECOMPOSITION_INVERTIBLE
   SERIES_FINITE_SUPPORT SERIES_RATIO SERIES_TERMS_TOZERO sphere SUMMABLE_EQ
   SUMMABLE_FROM_ELSEWHERE : thm)
  deriving Inhabited

structure QVectorsThms where
  (DOT_SQUARE_NORM LINEAR_EQ_MATRIX MATRIX_ADD MATRIX_ADD_LID MATRIX_ADD_RID
   MATRIX_CMUL_LID MATRIX_CMUL_LZERO NORM_EQ_1 VSUM_ADD_SPLIT VSUM_CLAUSES_RIGHT
   VSUM_PAIR_0 : thm)
  deriving Inhabited

structure QSessionThms where
  (ADD_ASSOC ARITH_EVEN ARITH_ODD HAS_SIZE_NUMSEG_LT INT_ABS_MUL INT_ABS_NUM
   int_abstr int_congruent INT_ENTIRE INT_LT_LMUL_EQ int_mul_th int_rep INT_SUB_0
   int_sub_th is_int LT_NZ LT_POW2_REFL NOT_EVEN num_congruent ODD ODD_ADD ODD_MULT
   REAL_ADD_RINV REAL_EQ_INV2 REAL_EQ_SGN_ABS REAL_INV_1_LE REAL_INV_SGN
   REAL_LT_NEGTOTAL REAL_LT_RSQRT REAL_LT_SQUARE REAL_LT_SUB_RADD REAL_MUL_2
   REAL_MUL_POS_LE REAL_OF_NUM_SUB_CASES REAL_POW_1_LE REAL_POW_LT2 REAL_POW_LT2_REV
   REAL_POW_POW REAL_POW_SUB REAL_SGN_0 REAL_SGN_ABS REAL_SGN_INV REAL_SGN_NEG
   REAL_SGN_POW REAL_SGN_POW_2 REAL_SGN_REAL_SGN REAL_SUB_RNEG SQRT_UNIQUE_GEN
   SUC_INJ SUM_ADD_SPLIT : thm)
  deriving Inhabited

structure QFloorThms where
  (FRAC_FLOOR INTEGER_ABS INTEGER_CASES INTEGER_NEG : thm)
  deriving Inhabited

structure QDeterminantsThms where
  (POSITIVE_DEFINITE_ADD POSITIVE_DEFINITE_CMUL POSITIVE_SEMIDEFINITE_ADD
   POSITIVE_SEMIDEFINITE_CMUL ROTATION_EXISTS : thm)
  deriving Inhabited

structure QPathsThms where
  (homotopic_loops HOMOTOPIC_LOOPS_EQ HOMOTOPIC_LOOPS_REFL HOMOTOPIC_LOOPS_TRANS
   HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT
   HOMOTOPIC_WITH_ORTHOGONAL_TRANSFORMATIONS_GEN
   HOMOTOPIC_WITH_ORTHOGONAL_TRANSFORMATIONS_UNIV
   HOMOTOPY_EQUIVALENT_HOMOTOPIC_TRIVIALITY LINEPATH_REFL
   PATH_CONNECTED_EQ_HOMOTOPIC_POINTS simply_connected
   SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_SOME : thm)
  deriving Inhabited

structure QMetricThms where
  (HOMOTOPIC_WITH_IMP_PROPERTY : thm)
  deriving Inhabited

structure QConvexThms where
  (CONVEX_CONNECTED_1 CONVEX_HALFSPACE_COMPONENT_GT CONVEX_HALFSPACE_COMPONENT_LT : thm)
  deriving Inhabited

structure QDegreeThms where
  (HOMOTOPIC_LINEAR_MAPS_ALT HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_IMP : thm)
  deriving Inhabited

structure QMiscThms where
  (ABS_SQUARE_LT_1 IN_FROM : thm)
  deriving Inhabited

structure QDerivativesThms where
  (DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON HAS_DERIVATIVE_BILINEAR_AT : thm)
  deriving Inhabited

structure QMeasureThms where
  (CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET
   FUBINI_HAS_ABSOLUTE_INTEGRAL FUBINI_TONELLI
   HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES LEBESGUE_MEASURABLE_CONVEX
   LEBESGUE_MEASURABLE_INTER LEBESGUE_MEASURABLE_UNIV
   MEASURABLE_ON_CONTINUOUS_COMPOSE MEASURABLE_ON_LINEAR_IMAGE_EQ_GEN
   MEASURABLE_ON_MUL MEASURABLE_ON_SPIKE_SET MEASURABLE_ON_UNIV
   NEGLIGIBLE_DIFFERENTIABLE_PREIMAGE NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE : thm)
  deriving Inhabited

structure QIntegrationThms where
  (ABSOLUTELY_INTEGRABLE_SPIKE_EQ ABSOLUTELY_INTEGRABLE_TWIZZLE_EQ
   INTEGRAL_TWIZZLE_EQ : thm)
  deriving Inhabited

structure QPermutationsThms where
  (PERMUTES_ID : thm)
  deriving Inhabited

structure TranscendentalsDeps where
  cn : HolMultiLib.Canal.CanalDeps
  kna : HolMultiLib.Canal.KNA
  knb : HolMultiLib.Canal.KNB
  knc : HolMultiLib.Canal.KNC
  knd : HolMultiLib.Canal.KND
  kne : HolMultiLib.Canal.KNE
  knf : HolMultiLib.Canal.KNF
  kng : HolMultiLib.Canal.KNG
  knh : HolMultiLib.Canal.KNH
  kni : HolMultiLib.Canal.KNI
  knj : HolMultiLib.Canal.KNJ
  knk : HolMultiLib.Canal.KNK
  knl : HolMultiLib.Canal.KNL
  knm : HolMultiLib.Canal.KNM
  knn : HolMultiLib.Canal.KNN
  kno : HolMultiLib.Canal.KNO
  knp : HolMultiLib.Canal.KNP
  knq : HolMultiLib.Canal.KNQ
  knr : HolMultiLib.Canal.KNR
  kns : HolMultiLib.Canal.KNS
  -- procedures the deps chain does not carry
  EXPAND_VSUM_CONV : ioconv
  HORNER_SUM_CONV : ioconv
  NUMBER_RULE : term → ExceptT String IO thm
  -- theorems
  qtopology : QTopologyThms
  qvectors : QVectorsThms
  qsession : QSessionThms
  qfloor : QFloorThms
  qdeterminants : QDeterminantsThms
  qpaths : QPathsThms
  qmetric : QMetricThms
  qconvex : QConvexThms
  qdegree : QDegreeThms
  qmisc : QMiscThms
  qderivatives : QDerivativesThms
  qmeasure : QMeasureThms
  qintegration : QIntegrationThms
  qpermutations : QPermutationsThms

/- ------------------------------------------------------------------------- -/
/- prioritize_complex(); the complex exponential function; add it to the    -/
/- database; hence the main results; crude bounds.                          -/
/- (transcendentals.ml 10-313)                                              -/
/- ------------------------------------------------------------------------- -/

structure TSA where
  cexp : thm
  CEXP_0 : thm
  CEXP_CONVERGES_UNIFORMLY_CAUCHY : thm
  CEXP_CONVERGES : thm
  CEXP_CONVERGES_UNIQUE : thm
  CEXP_CONVERGES_UNIFORMLY : thm
  HAS_COMPLEX_DERIVATIVE_CEXP : thm
  COMPLEX_DIFFERENTIABLE_AT_CEXP : thm
  COMPLEX_DIFFERENTIABLE_WITHIN_CEXP : thm
  CONTINUOUS_AT_CEXP : thm
  CONTINUOUS_WITHIN_CEXP : thm
  CONTINUOUS_ON_CEXP : thm
  HOLOMORPHIC_ON_CEXP : thm
  CEXP_ADD_MUL : thm
  CEXP_NEG_RMUL : thm
  CEXP_NEG_LMUL : thm
  CEXP_NEG : thm
  CEXP_ADD : thm
  CEXP_SUB : thm
  CEXP_NZ : thm
  CEXP_N : thm
  CEXP_VSUM : thm
  LIM_CEXP_MINUS_1 : thm
  CEXP_BOUND_BLEMMA : thm
  CEXP_BOUND_HALF : thm
  CEXP_BOUND_LEMMA : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupTSA [HolBase] (D : TranscendentalsDeps) : ExceptT String IO TSA := do
  -- @@SCOPE BEGIN
  let { complex_differentiable, COMPLEX_DIFFERENTIABLE_AT_WITHIN,
        HAS_COMPLEX_DERIVATIVE_AT_WITHIN, HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV,
        HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT, HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT,
        HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN, HAS_COMPLEX_DERIVATIVE_ZERO_UNIQUE,
        holomorphic_on, .. } := D.kne
  let { HAS_COMPLEX_DERIVATIVE_AT, .. } := D.knf
  let { COMPLEX_DIFFERENTIABLE_BOUND, HAS_COMPLEX_DERIVATIVE_SERIES, .. } := D.knj
  let { add_complex_differentiation_theorems, COMPLEX_DIFF_CONV, COMPLEX_DIFF_TAC,
        .. } := D.knk
  let { SERIES_FINITE_SUPPORT, SERIES_RATIO, .. } := D.qtopology
  let { VSUM_ADD_SPLIT, .. } := D.qvectors
  let { SUC_INJ, .. } := D.qsession
  let { complex_div, complex_pow, complex_sub, prioritize_complex, .. } := D.cn.cxa
  let { COMPLEX_ADD_LID, COMPLEX_ADD_RDISTRIB, COMPLEX_ADD_RID, COMPLEX_MUL_AC,
        COMPLEX_MUL_LID, COMPLEX_MUL_LZERO, COMPLEX_MUL_RID, COMPLEX_MUL_SYM,
        COMPLEX_NEG_0, COMPLEX_SUB_LZERO, COMPLEX_SUB_REFL, COMPLEX_SUB_RZERO,
        .. } := D.cn.cxb
  let { COMPLEX_NORM_CX, COMPLEX_VEC_0, CX_ADD, CX_DIV, CX_INJ, CX_MUL, CX_POW,
        .. } := D.cn.cxc
  let { COMPLEX_RING, .. } := D.cn.cxd
  let { COMPLEX_FIELD, COMPLEX_INV_MUL, .. } := D.cn.cxe
  let { COMPLEX_DIV_1, COMPLEX_NORM_0, COMPLEX_NORM_DIV, COMPLEX_NORM_POW, .. } := D.cn.cxf
  let { VSUM_CX_NUMSEG, .. } := D.cn.cxi
  let { CPRODUCT_CLAUSES, .. } := D.cn.cxk
  let { INFSUM_UNIQUE, SERIES_CAUCHY, summable, SUMS_INFSUM, .. } := D.cn.qtopology
  let { FACT, FACT_LT, .. } := D.cn.qsession
  let { FROM_0, .. } := D.cn.ms.qmisc
  let { SUC_SUB1, .. } := D.cn.ms.qsession
  let { SERIES_UNIQUE, .. } := D.cn.ms.qtopology2
  let { ARITH_RULE, ARITH_TAC, INDUCT_TAC, MESON_TAC, new_definition, NORM_ARITH,
        NORM_ARITH_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV, SET_RULE,
        .. } := D.cn.cx.cvx
  let { LE_0, NOT_SUC, .. } := D.cn.cx.cpx
  let { LT_0, .. } := D.cn.ms.ig.qsession
  let { VSUM_NORM_LE, .. } := D.cn.ms.ig.qvec
  let { ARITH, EQ_IMP, EXISTS_IN_IMAGE, EXTENSION, FINITE_IMAGE, FINITE_INDUCT_STRONG,
        FINITE_INSERT, FINITE_NUMSEG, FINITE_RULES, FORALL_AND_THM,
        .. } := D.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, GE, IMAGE_EQ_EMPTY, INTER_UNIV, .. } := D.cn.cx.cvx.core2
  let { IN_IMAGE, IN_INSERT, IN_NUMSEG, IN_SING, IN_UNIV, LEFT_FORALL_IMP_THM, MONO_EXISTS,
        MONO_FORALL, MONO_IMP, REAL_ABS_NUM, REAL_ABS_POS, REAL_ABS_REFL, REAL_ARCH_SIMPLE,
        .. } := D.cn.cx.cvx.core3
  let { REAL_INV_MUL, REAL_LE_DIV2_EQ, REAL_LE_INV_EQ, REAL_LE_LDIV_EQ, REAL_LE_LMUL,
        REAL_LE_MUL, REAL_LT_01, REAL_LT_DIV, REAL_LT_IMP_LE, .. } := D.cn.cx.cvx.core4
  let { REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_OF_NUM_MUL, REAL_OF_NUM_SUC, REAL_POS,
        REAL_POW_LE, REAL_POW_LE2, REAL_POW_LT, REAL_SUB_LE, .. } := D.cn.cx.cvx.core5
  let { o_THM, real_div, real_pow, UNWIND_THM1, .. } := D.cn.cx.cvx.core6
  let { REAL_HALF, .. } := D.cn.cx.cvx.misc
  let { NORM_NEG, NORM_POS_LE, .. } := D.cn.cx.cvx.vec3
  let { dist, VSUM_CLAUSES, VSUM_EQ, VSUM_IMAGE, VSUM_SING, .. } := D.cn.cx.cvx.vec4
  let { CBALL_EQ_EMPTY, .. } := D.cn.cx.cvx.top1
  let { COMPACT_CBALL, COMPACT_CONTINUOUS_IMAGE, CONTINUOUS_AT_IMP_CONTINUOUS_ON,
        .. } := D.cn.cx.cvx.top2
  let { DISTANCE_ATTAINS_SUP, .. } := D.cn.cx.cvx.top3
  let { IN_BALL, IN_CBALL, LIM_SEQUENTIALLY, OPEN_BALL, .. } := D.cn.cx.cvx.top4
  let { OPEN_UNIV, .. } := D.cn.cx.cvx.top5
  let { CONTINUOUS_AT_WITHIN, .. } := D.cn.ms.ig.dv.qtopology1
  let { sums, .. } := D.cn.ms.ig.dv.qtopology2
  let { SUM_POS_LE_NUMSEG, .. } := D.cn.ms.ig.dv.dg.qsession
  let { CONVEX_BALL, CONVEX_CBALL, .. } := D.cn.ms.ig.dv.dg.pt.qcvx2
  let { CONVEX_UNIV, .. } := D.cn.ms.ig.dv.dg.pt.qcvx3
  -- @@SCOPE END

  prioritize_complex

  let cexp ← new_definition
   r"cexp z = infsum (from 0) (\n. z pow n / Cx(&(FACT n)))"

  let CEXP_0 ← prove
   r"cexp(Cx(&0)) = Cx(&1)"
   (REWRITE_TAC [cexp] THEN MATCH_MP_TAC INFSUM_UNIQUE THEN
    MP_TAC (← ISPECL [← q r"\i. Cx(&0) pow i / Cx(&(FACT i))", ← q r"{0}", ← q r"from 0"]
           SERIES_FINITE_SUPPORT) THEN
    SIMP_TAC [FROM_0, INTER_UNIV, FINITE_INSERT, FINITE_RULES] THEN ANTS_TAC THENL
     [INDUCT_TAC THEN REWRITE_TAC [IN_SING, NOT_SUC] THEN
      REWRITE_TAC [complex_div, complex_pow, COMPLEX_MUL_LZERO, COMPLEX_VEC_0],
      REWRITE_TAC [VSUM_SING, FACT, COMPLEX_DIV_1, complex_pow]])

  let CEXP_CONVERGES_UNIFORMLY_CAUCHY ← prove
   r"!R e. &0 < e /\ &0 < R
         ==> ?N. !m n z. m >= N /\ norm(z) <= R
                         ==> norm(vsum(m..n) (\i. z pow i / Cx(&(FACT i))))
                                     < e"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"&1 / &2", ← q r"\i. Cx(R) pow i / Cx(&(FACT i))",
                      ← q r"from 0"] SERIES_RATIO) THEN
    REWRITE_TAC [SERIES_CAUCHY, LEFT_FORALL_IMP_THM] THEN
    MP_TAC (← SPEC (← q r"&2 * norm(Cx(R))") REAL_ARCH_SIMPLE) THEN
    REWRITE_TAC [COMPLEX_NORM_CX, COMPLEX_NORM_DIV, COMPLEX_NORM_POW] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC (← TAUT (← q r"(a ==> b) /\ (c ==> d) ==> a ==> (b ==> c) ==> d")) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"N:num") THEN DISCH_TAC THEN
      X_GEN_TAC (← q r"n:num") THEN REWRITE_TAC [GE] THEN DISCH_TAC THEN
      SIMP_TAC [FACT, real_pow, ← GSYM REAL_OF_NUM_MUL, real_div, REAL_INV_MUL] THEN
      REWRITE_TAC [← REAL_ARITH
       (← q r"(z * zn) * (is * ik) <= (&1 * inv(&2)) * zn * ik <=>
        &0 <= (&1 - (&2 * z) * is) * zn * ik")] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      SIMP_TAC [REAL_LE_MUL, REAL_POS, REAL_POW_LE, REAL_SUB_LE,
                REAL_LE_INV_EQ, REAL_ABS_POS] THEN
      ASM_SIMP_TAC [← GSYM real_div, REAL_LE_LDIV_EQ, REAL_OF_NUM_LT, LT_0] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN
      REWRITE_TAC [← GSYM REAL_OF_NUM_LE, ← GSYM REAL_OF_NUM_SUC] THEN
      REAL_ARITH_TAC,
      DISCH_THEN (MP_TAC o SPEC (← q r"e:real")) THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"N:num") THEN
      REWRITE_TAC [FROM_0, INTER_UNIV] THEN
      REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
      DISCH_THEN (fun th => REPEAT STRIP_TAC THEN MP_TAC th) THEN
      ASM_SIMP_TAC [← GSYM CX_DIV, ← GSYM CX_POW, VSUM_CX_NUMSEG, COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"x <= y ==> y < e ==> x < e")) THEN
      SUBGOAL_THEN (← q r"abs (sum (m..n) (\i. R pow i / &(FACT i))) =
                    sum (m..n) (\i. R pow i / &(FACT i))")
      SUBST1_TAC THENL
       [REWRITE_TAC [REAL_ABS_REFL] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
        ASM_SIMP_TAC [REAL_LT_IMP_LE, REAL_LT_DIV, REAL_OF_NUM_LT,
                      FACT_LT, REAL_POW_LT],
        ALL_TAC] THEN
      MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC [IN_NUMSEG, FINITE_NUMSEG] THEN
      X_GEN_TAC (← q r"i:num") THEN
      REWRITE_TAC [COMPLEX_NORM_DIV, COMPLEX_NORM_POW, COMPLEX_NORM_CX] THEN
      SIMP_TAC [REAL_ABS_NUM, REAL_LE_DIV2_EQ, REAL_OF_NUM_LT, FACT_LT] THEN
      ASM_SIMP_TAC [REAL_POW_LE2, NORM_POS_LE]])

  let CEXP_CONVERGES ← prove
   r"!z. ((\n. z pow n / Cx(&(FACT n))) sums cexp(z)) (from 0)"
   (GEN_TAC THEN REWRITE_TAC [cexp, SUMS_INFSUM, summable, SERIES_CAUCHY] THEN
    REWRITE_TAC [FROM_0, INTER_UNIV] THEN
    MP_TAC (← SPEC (← q r"norm(z:complex) + &1") CEXP_CONVERGES_UNIFORMLY_CAUCHY) THEN
    SIMP_TAC [← REAL_ARITH (← q r"&0 <= x ==> &0 < x + &1"), NORM_POS_LE] THEN
    MESON_TAC [← REAL_ARITH (← q r"x <= x + &1")])

  let CEXP_CONVERGES_UNIQUE ← prove
   r"!w z. ((\n. z pow n / Cx(&(FACT n))) sums w) (from 0) <=> w = cexp(z)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC [CEXP_CONVERGES] THEN
    DISCH_THEN (MP_TAC o C CONJ (← SPEC (← q r"z:complex") CEXP_CONVERGES)) THEN
    REWRITE_TAC [SERIES_UNIQUE])

  let CEXP_CONVERGES_UNIFORMLY ← prove
   r"!R e. &0 < R /\ &0 < e
         ==> ?N. !n z. n >= N /\ norm(z) < R
                       ==> norm(vsum(0..n) (\i. z pow i / Cx(&(FACT i))) -
                                cexp(z)) <= e"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"R:real", ← q r"e / &2"] CEXP_CONVERGES_UNIFORMLY_CAUCHY) THEN
    ASM_REWRITE_TAC [REAL_HALF] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"N:num") THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"z:complex"] THEN STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"z:complex") CEXP_CONVERGES) THEN
    REWRITE_TAC [sums, LIM_SEQUENTIALLY, FROM_0, INTER_UNIV, dist] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"e / &2")) THEN ASM_REWRITE_TAC [REAL_HALF] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"M:num") (MP_TAC o SPEC (← q r"n + M + 1"))) THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"n + 1", ← q r"n + M + 1", ← q r"z:complex"]) THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"(n >= N ==> n + 1 >= N) /\ M <= n + M + 1")] THEN
    ASM_SIMP_TAC [REAL_LT_IMP_LE, VSUM_ADD_SPLIT, LE_0] THEN
    CONV_TAC (← (do let v ← q r"i:num"; pure (ONCE_DEPTH_CONV (fun t =>
      pure (HolCore.Equal.ALPHA_CONV v t))))) THEN
    NORM_ARITH_TAC)

  let HAS_COMPLEX_DERIVATIVE_CEXP ← prove
   r"!z. (cexp has_complex_derivative cexp(z)) (at z)"
   (REPEAT GEN_TAC THEN MP_TAC (← ISPECL
     [← q r"ball(Cx(&0),norm(z:complex) + &1)",
      ← q r"\n z. z pow n / Cx(&(FACT n))",
      ← q r"\n z. if n = 0 then Cx(&0) else z pow (n-1) / Cx(&(FACT(n-1)))",
      ← q r"cexp:complex->complex",
      ← q r"(from 0)"]
     HAS_COMPLEX_DERIVATIVE_SERIES) THEN
    REWRITE_TAC [CONVEX_BALL, OPEN_BALL, IN_BALL, dist] THEN
    SIMP_TAC [HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN, OPEN_BALL, IN_BALL,
              dist, COMPLEX_SUB_LZERO, COMPLEX_SUB_RZERO, NORM_NEG] THEN
    ANTS_TAC THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC (← q r"n:num") THEN REPEAT STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
      SPEC_TAC (← q r"n:num", ← q r"n:num") THEN INDUCT_TAC THEN
      REWRITE_TAC [ARITH, complex_div, COMPLEX_MUL_LZERO] THEN
      MP_TAC (← SPECL [← q r"&n + &1", ← q r"&0"] CX_INJ) THEN
      REWRITE_TAC [NOT_SUC, SUC_SUB1, ← GSYM REAL_OF_NUM_SUC, FACT,
           CX_ADD, CX_MUL, ← GSYM REAL_OF_NUM_MUL, COMPLEX_INV_MUL] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"~(&n + &1 = &0)")] THEN
      ABBREV_TAC (← q r"a = inv(Cx(&(FACT n)))") THEN CONV_TAC COMPLEX_FIELD,
      REPEAT STRIP_TAC THEN
      MP_TAC (← SPECL [← q r"norm(z:complex) + &1", ← q r"e:real"]
         CEXP_CONVERGES_UNIFORMLY) THEN
      ASM_SIMP_TAC [NORM_POS_LE, ← REAL_ARITH (← q r"&0 <= x ==> &0 < x + &1")] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"N:num")) THEN EXISTS_TAC (← q r"N + 1") THEN
      MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"w:complex"] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"n - 1", ← q r"w:complex"]) THEN
      ASM_SIMP_TAC [← ARITH_RULE (← q r"n >= m + 1 ==> n - 1 >= m")] THEN
      REWRITE_TAC [FROM_0, INTER_UNIV] THEN MATCH_MP_TAC EQ_IMP THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN (← q r"0..n = 0 INSERT (IMAGE SUC (0..n-1))") SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_INSERT, IN_IMAGE, IN_NUMSEG] THEN
        INDUCT_TAC THEN REWRITE_TAC [LE_0, NOT_SUC, SUC_INJ, UNWIND_THM1] THEN
        UNDISCH_TAC (← q r"n >= N + 1") THEN ARITH_TAC,
        ALL_TAC] THEN
      SIMP_TAC [VSUM_CLAUSES, FINITE_IMAGE, FINITE_NUMSEG] THEN
      REWRITE_TAC [IN_IMAGE, NOT_SUC, COMPLEX_ADD_LID] THEN
      SIMP_TAC [VSUM_IMAGE, FINITE_NUMSEG, SUC_INJ] THEN
      MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC [IN_NUMSEG, NOT_SUC, o_THM, SUC_SUB1],
      MAP_EVERY EXISTS_TAC [← q r"Cx(&0)", ← q r"cexp(Cx(&0))"] THEN
      REWRITE_TAC [CEXP_CONVERGES, COMPLEX_NORM_0] THEN
      SIMP_TAC [← REAL_ARITH (← q r"&0 <= z ==> &0 < z + &1"), NORM_POS_LE],
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:complex->complex") MP_TAC) THEN
      REWRITE_TAC [CEXP_CONVERGES_UNIQUE] THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
      MAP_EVERY EXISTS_TAC [← q r"g:complex->complex", ← q r"&1"] THEN
      REWRITE_TAC [REAL_LT_01] THEN CONJ_TAC THENL
       [ALL_TAC,
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"z:complex")) THEN
        ANTS_TAC THENL [REAL_ARITH_TAC, SIMP_TAC []]] THEN
      POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_FORALL THEN
      X_GEN_TAC (← q r"w:complex") THEN MATCH_MP_TAC MONO_IMP THEN SIMP_TAC [] THEN
      NORM_ARITH_TAC])

  let COMPLEX_DIFFERENTIABLE_AT_CEXP ← prove
   r"!z. cexp complex_differentiable at z"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_CEXP])

  let COMPLEX_DIFFERENTIABLE_WITHIN_CEXP ← prove
   r"!s z. cexp complex_differentiable (at z within s)"
   (MESON_TAC [COMPLEX_DIFFERENTIABLE_AT_WITHIN,
               COMPLEX_DIFFERENTIABLE_AT_CEXP])

  let CONTINUOUS_AT_CEXP ← prove
   r"!z. cexp continuous at z"
   (MESON_TAC [HAS_COMPLEX_DERIVATIVE_CEXP,
               HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT])

  let CONTINUOUS_WITHIN_CEXP ← prove
   r"!s z. cexp continuous (at z within s)"
   (MESON_TAC [CONTINUOUS_AT_WITHIN, CONTINUOUS_AT_CEXP])

  let CONTINUOUS_ON_CEXP ← prove
   r"!s. cexp continuous_on s"
   (MESON_TAC [CONTINUOUS_AT_IMP_CONTINUOUS_ON, CONTINUOUS_AT_CEXP])

  let HOLOMORPHIC_ON_CEXP ← prove
   r"!s. cexp holomorphic_on s"
   (REWRITE_TAC [holomorphic_on] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN, HAS_COMPLEX_DERIVATIVE_CEXP])

  add_complex_differentiation_theorems
   (CONJUNCTS (← REWRITE_RULE [FORALL_AND_THM]
     (← MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV
               HAS_COMPLEX_DERIVATIVE_CEXP)))

  let CEXP_ADD_MUL ← prove
   r"!w z. cexp(w + z) * cexp(--z) = cexp(w)"
   (GEN_TAC THEN
    ONCE_REWRITE_TAC [← SET_RULE (← q r"(!x. P x) <=> (!x. x IN UNIV ==> P x)")] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_ZERO_UNIQUE THEN
    EXISTS_TAC (← q r"Cx(&0)") THEN REWRITE_TAC [OPEN_UNIV, CONVEX_UNIV, IN_UNIV] THEN
    REWRITE_TAC [COMPLEX_ADD_RID, COMPLEX_NEG_0, CEXP_0, COMPLEX_MUL_RID] THEN
    GEN_TAC THEN COMPLEX_DIFF_TAC THEN CONV_TAC COMPLEX_RING)

  let CEXP_NEG_RMUL ← prove
   r"!z. cexp(z) * cexp(--z) = Cx(&1)"
   (MP_TAC (← SPEC (← q r"Cx(&0)") CEXP_ADD_MUL) THEN MATCH_MP_TAC MONO_FORALL THEN
    SIMP_TAC [COMPLEX_ADD_LID, CEXP_0])

  let CEXP_NEG_LMUL ← prove
   r"!z. cexp(--z) * cexp(z) = Cx(&1)"
   (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN REWRITE_TAC [CEXP_NEG_RMUL])

  let CEXP_NEG ← prove
   r"!z. cexp(--z) = inv(cexp z)"
   (MP_TAC CEXP_NEG_LMUL THEN MATCH_MP_TAC MONO_FORALL THEN
    CONV_TAC COMPLEX_FIELD)

  let CEXP_ADD ← prove
   r"!w z. cexp(w + z) = cexp(w) * cexp(z)"
   (REPEAT GEN_TAC THEN
    MP_TAC (← SPECL [← q r"w:complex", ← q r"z:complex"] CEXP_ADD_MUL) THEN
    MP_TAC (← SPEC (← q r"z:complex") CEXP_NEG_LMUL) THEN CONV_TAC COMPLEX_FIELD)

  let CEXP_SUB ← prove
   r"!w z. cexp(w - z) = cexp(w) / cexp(z)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [complex_sub, complex_div, CEXP_ADD, CEXP_NEG])

  let CEXP_NZ ← prove
   r"!z. ~(cexp(z) = Cx(&0))"
   (MP_TAC CEXP_NEG_LMUL THEN MATCH_MP_TAC MONO_FORALL THEN
    CONV_TAC COMPLEX_FIELD)

  let CEXP_N ← prove
   r"!n x. cexp(Cx(&n) * x) = cexp(x) pow n"
   (INDUCT_TAC THEN REWRITE_TAC [← GSYM REAL_OF_NUM_SUC, CX_ADD] THEN
    REWRITE_TAC [COMPLEX_MUL_LZERO, complex_pow, CEXP_0] THEN
    ASM_REWRITE_TAC [COMPLEX_ADD_RDISTRIB, CEXP_ADD, COMPLEX_MUL_LID] THEN
    REWRITE_TAC [COMPLEX_MUL_AC])

  let CEXP_VSUM ← prove
   r"!f s. FINITE s ==> cexp(vsum s f) = cproduct s (\x. cexp(f x))"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [VSUM_CLAUSES, CPRODUCT_CLAUSES, CEXP_ADD, COMPLEX_VEC_0, CEXP_0])

  let LIM_CEXP_MINUS_1 ← prove
   r"((\z. (cexp(z) - Cx(&1)) / z) --> Cx(&1)) (at (Cx(&0)))"
   (MP_TAC (← COMPLEX_DIFF_CONV
        (← q r"((\z. cexp(z) - Cx(&1)) has_complex_derivative f') (at(Cx(&0)))")) THEN
    REWRITE_TAC [HAS_COMPLEX_DERIVATIVE_AT, CEXP_0, COMPLEX_SUB_REFL] THEN
    REWRITE_TAC [COMPLEX_MUL_LID, COMPLEX_SUB_RZERO])

  let CEXP_BOUND_BLEMMA ← prove
   r"!B. (!z. norm(z) <= &1 / &2 ==> norm(cexp z) <= B)
       ==> !z. norm(z) <= &1 / &2 ==> norm(cexp z) <= &1 + B / &2"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"cexp", ← q r"cexp", ← q r"cball(Cx(&0),&1 / &2)", ← q r"B:real"]
                  COMPLEX_DIFFERENTIABLE_BOUND) THEN
    ASM_SIMP_TAC [CONVEX_CBALL, IN_CBALL, dist, COMPLEX_SUB_LZERO, NORM_NEG,
      HAS_COMPLEX_DERIVATIVE_AT_WITHIN, HAS_COMPLEX_DERIVATIVE_CEXP] THEN
    DISCH_THEN (MP_TAC o SPECL [← q r"z:complex", ← q r"Cx(&0)"]) THEN
    REWRITE_TAC [COMPLEX_NORM_0, CEXP_0, COMPLEX_SUB_RZERO] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← NORM_ARITH
     (← q r"norm(y) = &1 /\ d <= e ==> norm(x - y) <= d ==> norm(x) <= &1 + e")) THEN
    REWRITE_TAC [COMPLEX_NORM_CX, real_div, REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"Cx(&0)")) THEN
    REWRITE_TAC [COMPLEX_NORM_CX] THEN POP_ASSUM MP_TAC THEN
    NORM_ARITH_TAC)

  let CEXP_BOUND_HALF ← prove
   r"!z. norm(z) <= &1 / &2 ==> norm(cexp z) <= &2"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"IMAGE cexp (cball(Cx(&0),&1 / &2))", ← q r"Cx(&0)"]
      DISTANCE_ATTAINS_SUP) THEN
    SIMP_TAC [COMPACT_CONTINUOUS_IMAGE, COMPACT_CBALL, CONTINUOUS_ON_CEXP,
              IMAGE_EQ_EMPTY, CBALL_EQ_EMPTY, FORALL_IN_IMAGE, EXISTS_IN_IMAGE,
              IN_CBALL, dist, COMPLEX_SUB_LZERO, NORM_NEG] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"w:complex") STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"w:complex") o MATCH_MP CEXP_BOUND_BLEMMA) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"z:complex")) THEN
    ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC)

  let CEXP_BOUND_LEMMA ← prove
   r"!z. norm(z) <= &1 / &2 ==> norm(cexp z) <= &1 + &2 * norm(z)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"cexp", ← q r"cexp", ← q r"cball(Cx(&0),&1 / &2)", ← q r"&2"]
                  COMPLEX_DIFFERENTIABLE_BOUND) THEN
    ASM_SIMP_TAC [CONVEX_CBALL, IN_CBALL, dist, COMPLEX_SUB_LZERO, NORM_NEG,
                  HAS_COMPLEX_DERIVATIVE_AT_WITHIN, HAS_COMPLEX_DERIVATIVE_CEXP,
                  CEXP_BOUND_HALF] THEN
    DISCH_THEN (MP_TAC o SPECL [← q r"z:complex", ← q r"Cx(&0)"]) THEN
    REWRITE_TAC [COMPLEX_NORM_0, CEXP_0, COMPLEX_SUB_RZERO] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← NORM_ARITH
     (← q r"norm(y) = &1 ==> norm(x - y) <= d ==> norm(x) <= &1 + d")) THEN
    REWRITE_TAC [COMPLEX_NORM_CX, REAL_ABS_NUM])

  pure { cexp, CEXP_0, CEXP_CONVERGES_UNIFORMLY_CAUCHY, CEXP_CONVERGES,
         CEXP_CONVERGES_UNIQUE, CEXP_CONVERGES_UNIFORMLY, HAS_COMPLEX_DERIVATIVE_CEXP,
         COMPLEX_DIFFERENTIABLE_AT_CEXP, COMPLEX_DIFFERENTIABLE_WITHIN_CEXP,
         CONTINUOUS_AT_CEXP, CONTINUOUS_WITHIN_CEXP, CONTINUOUS_ON_CEXP,
         HOLOMORPHIC_ON_CEXP, CEXP_ADD_MUL, CEXP_NEG_RMUL, CEXP_NEG_LMUL, CEXP_NEG,
         CEXP_ADD, CEXP_SUB, CEXP_NZ, CEXP_N, CEXP_VSUM, LIM_CEXP_MINUS_1,
         CEXP_BOUND_BLEMMA, CEXP_BOUND_HALF, CEXP_BOUND_LEMMA }
/- ------------------------------------------------------------------------- -/
/- Complex trig functions; Euler and de Moivre formulas; real exponential    -/
/- function.  (transcendentals.ml 314-603)                                  -/
/- ------------------------------------------------------------------------- -/

structure TSB where
  ccos : thm
  csin : thm
  CSIN_0 : thm
  CCOS_0 : thm
  CSIN_CIRCLE : thm
  CSIN_ADD : thm
  CCOS_ADD : thm
  CSIN_NEG : thm
  CCOS_NEG : thm
  CSIN_DOUBLE : thm
  CCOS_DOUBLE : thm
  CSIN_SUB : thm
  CCOS_SUB : thm
  COMPLEX_MUL_CSIN_CSIN : thm
  COMPLEX_MUL_CSIN_CCOS : thm
  COMPLEX_MUL_CCOS_CSIN : thm
  COMPLEX_MUL_CCOS_CCOS : thm
  COMPLEX_ADD_CSIN : thm
  COMPLEX_SUB_CSIN : thm
  COMPLEX_ADD_CCOS : thm
  COMPLEX_SUB_CCOS : thm
  CCOS_DOUBLE_CCOS : thm
  CCOS_DOUBLE_CSIN : thm
  CEXP_EULER : thm
  DEMOIVRE : thm
  exp : thm
  CNJ_CEXP : thm
  REAL_EXP : thm
  CX_EXP : thm
  REAL_EXP_ADD : thm
  REAL_EXP_0 : thm
  REAL_EXP_ADD_MUL : thm
  REAL_EXP_NEG_MUL : thm
  REAL_EXP_NEG_MUL2 : thm
  REAL_EXP_NEG : thm
  REAL_EXP_N : thm
  REAL_EXP_SUB : thm
  REAL_EXP_NZ : thm
  REAL_EXP_POS_LE : thm
  REAL_EXP_POS_LT : thm
  REAL_EXP_LE_X : thm
  REAL_EXP_LT_1 : thm
  REAL_EXP_MONO_IMP : thm
  REAL_EXP_MONO_LT : thm
  REAL_EXP_MONO_LE : thm
  REAL_EXP_INJ : thm
  REAL_EXP_EQ_1 : thm
  REAL_ABS_EXP : thm
  REAL_EXP_SUM : thm
  REAL_EXP_BOUND_LEMMA : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupTSB [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) : ExceptT String IO TSB := do
  -- @@SCOPE BEGIN
  let { CEXP_0, CEXP_ADD, CEXP_ADD_MUL, CEXP_BOUND_LEMMA, CEXP_CONVERGES, CEXP_N, CEXP_NEG,
        CEXP_NEG_LMUL, CEXP_NEG_RMUL, CEXP_NZ, CEXP_SUB, .. } := BTSA
  let { SUMS_CNJ, .. } := D.knm
  let { REAL_POW_POW, .. } := D.qsession
  let { complex_sub, RE_DEF, .. } := D.cn.cxa
  let { COMPLEX_ADD_LDISTRIB, COMPLEX_ADD_SYM, COMPLEX_MUL_AC, COMPLEX_MUL_LNEG,
        COMPLEX_MUL_RNEG, COMPLEX_MUL_RZERO, COMPLEX_NEG_NEG, COMPLEX_SUB_REFL,
        .. } := D.cn.cxb
  let { COMPLEX_NORM_CX, CX_ADD, CX_DIV, CX_INJ, CX_INV, CX_MUL, CX_NEG, CX_POW, CX_SUB,
        RE_CX, .. } := D.cn.cxc
  let { COMPLEX_RING, .. } := D.cn.cxd
  let { COMPLEX_FIELD, .. } := D.cn.cxe
  let { CNJ_CX, CNJ_DIV, CNJ_POW, .. } := D.cn.cxg
  let { REAL, REAL_CNJ, REAL_CX, .. } := D.cn.cxi
  let { FACT, .. } := D.cn.qsession
  let { FROM_0, .. } := D.cn.ms.qmisc
  let { FACT_NZ, .. } := D.cn.ms.qsession
  let { LIM_COMPONENT_LBOUND, SERIES_UNIQUE, .. } := D.cn.ms.qtopology2
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC,
        new_definition, NUM_REDUCE_CONV, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD,
        .. } := D.cn.cx.cvx
  let { ADD_CLAUSES, LE_0, NOT_SUC, PRODUCT_CLAUSES, REAL_LE_SQUARE, REAL_POW_1,
        VSUM_COMPONENT, .. } := D.cn.cx.cpx
  let { LT_0, .. } := D.cn.ms.ig.qsession
  let { ADD1, ARITH, DIMINDEX_2, FINITE_INDUCT_STRONG, .. } := D.cn.cx.cvx.core1
  let { INTER_UNIV, .. } := D.cn.cx.cvx.core2
  let { MONO_FORALL, MULT_CLAUSES, REAL_ADD_ASSOC, REAL_ADD_SYM, REAL_DIV_1,
        .. } := D.cn.cx.cvx.core3
  let { REAL_LE_ADD, REAL_LE_ADDR, REAL_LE_ANTISYM, REAL_LE_DIV, REAL_LE_MUL,
        REAL_LE_POW_2, REAL_LE_RDIV_EQ, REAL_LT_LE, REAL_LT_RDIV_EQ,
        .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_LID, REAL_NOT_LT, REAL_OF_NUM_EQ, REAL_OF_NUM_LT, REAL_OF_NUM_MUL,
        REAL_OF_NUM_SUC, REAL_POS, REAL_POW_LE, REAL_SUB_LT, .. } := D.cn.cx.cvx.core5
  let { real_abs, real_pow, SUM_CLAUSES, SUM_CLAUSES_LEFT, SUM_CLAUSES_NUMSEG,
        .. } := D.cn.cx.cvx.core6
  let { EVENTUALLY_SEQUENTIALLY, TRIVIAL_LIMIT_SEQUENTIALLY, .. } := D.cn.cx.cvx.met
  let { sums, .. } := D.cn.ms.ig.dv.qtopology2
  let { EVEN_EXISTS, EVEN_OR_ODD, ODD_EXISTS, SUM_PAIR, SUM_POS_LE_NUMSEG,
        .. } := D.cn.ms.ig.dv.dg.qsession
  -- @@SCOPE END

  let ccos ← new_definition
   r"ccos z = (cexp(ii * z) + cexp(--ii * z)) / Cx(&2)"

  let csin ← new_definition
   r"csin z = (cexp(ii * z) - cexp(--ii * z)) / (Cx(&2) * ii)"

  let CSIN_0 ← prove
   r"csin(Cx(&0)) = Cx(&0)"
   (REWRITE_TAC [csin, COMPLEX_MUL_RZERO, COMPLEX_SUB_REFL] THEN
    CONV_TAC COMPLEX_FIELD)

  let CCOS_0 ← prove
   r"ccos(Cx(&0)) = Cx(&1)"
   (REWRITE_TAC [ccos, COMPLEX_MUL_RZERO, CEXP_0] THEN
    CONV_TAC COMPLEX_FIELD)

  let CSIN_CIRCLE ← prove
   r"!z. csin(z) pow 2 + ccos(z) pow 2 = Cx(&1)"
   (GEN_TAC THEN REWRITE_TAC [csin, ccos] THEN
    MP_TAC (← SPEC (← q r"ii * z") CEXP_NEG_LMUL) THEN
    REWRITE_TAC [COMPLEX_MUL_LNEG] THEN
    CONV_TAC COMPLEX_FIELD)

  let CSIN_ADD ← prove
   r"!w z. csin(w + z) = csin(w) * ccos(z) + ccos(w) * csin(z)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [csin, ccos, COMPLEX_ADD_LDISTRIB, CEXP_ADD] THEN
    CONV_TAC COMPLEX_FIELD)

  let CCOS_ADD ← prove
   r"!w z. ccos(w + z) = ccos(w) * ccos(z) - csin(w) * csin(z)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [csin, ccos, COMPLEX_ADD_LDISTRIB, CEXP_ADD] THEN
    CONV_TAC COMPLEX_FIELD)

  let CSIN_NEG ← prove
   r"!z. csin(--z) = --(csin(z))"
   (REWRITE_TAC [csin, COMPLEX_MUL_LNEG, COMPLEX_MUL_RNEG, COMPLEX_NEG_NEG] THEN
    CONV_TAC COMPLEX_FIELD)

  let CCOS_NEG ← prove
   r"!z. ccos(--z) = ccos(z)"
   (REWRITE_TAC [ccos, COMPLEX_MUL_LNEG, COMPLEX_MUL_RNEG, COMPLEX_NEG_NEG] THEN
    CONV_TAC COMPLEX_FIELD)

  let CSIN_DOUBLE ← prove
   r"!z. csin(Cx(&2) * z) = Cx(&2) * csin(z) * ccos(z)"
   (REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"Cx(&2) * x = x + x")), CSIN_ADD] THEN
    CONV_TAC COMPLEX_RING)

  let CCOS_DOUBLE ← prove
   r"!z. ccos(Cx(&2) * z) = (ccos(z) pow 2) - (csin(z) pow 2)"
   (REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"Cx(&2) * x = x + x")), CCOS_ADD] THEN
    CONV_TAC COMPLEX_RING)

  let CSIN_SUB ← prove
   r"!w z. csin(w - z) = csin(w) * ccos(z) - ccos(w) * csin(z)"
   (REWRITE_TAC [complex_sub, COMPLEX_MUL_RNEG, CSIN_ADD, CSIN_NEG, CCOS_NEG])

  let CCOS_SUB ← prove
   r"!w z. ccos(w - z) = ccos(w) * ccos(z) + csin(w) * csin(z)"
   (REWRITE_TAC [complex_sub, CCOS_ADD, CSIN_NEG, CCOS_NEG,
                 COMPLEX_MUL_RNEG, COMPLEX_NEG_NEG])

  let COMPLEX_MUL_CSIN_CSIN ← prove
   r"!w z. csin(w) * csin(z) = (ccos(w - z) - ccos(w + z)) / Cx(&2)"
   (REWRITE_TAC [CCOS_ADD, CCOS_SUB] THEN CONV_TAC COMPLEX_RING)

  let COMPLEX_MUL_CSIN_CCOS ← prove
   r"!w z. csin(w) * ccos(z) = (csin(w + z) + csin(w - z)) / Cx(&2)"
   (REWRITE_TAC [CSIN_ADD, CSIN_SUB] THEN CONV_TAC COMPLEX_RING)

  let COMPLEX_MUL_CCOS_CSIN ← prove
   r"!w z. ccos(w) * csin(z) = (csin(w + z) - csin(w - z)) / Cx(&2)"
   (REWRITE_TAC [CSIN_ADD, CSIN_SUB] THEN CONV_TAC COMPLEX_RING)

  let COMPLEX_MUL_CCOS_CCOS ← prove
   r"!w z. ccos(w) * ccos(z) = (ccos(w - z) + ccos(w + z)) / Cx(&2)"
   (REWRITE_TAC [CCOS_ADD, CCOS_SUB] THEN CONV_TAC COMPLEX_RING)

  let COMPLEX_ADD_CSIN ← prove
   r"!w z. csin(w) + csin(z) =
         Cx(&2) * csin((w + z) / Cx(&2)) * ccos((w - z) / Cx(&2))"
   (SIMP_TAC [COMPLEX_MUL_CSIN_CCOS, ← ExceptT.mk (COMPLEX_RING (← q r"Cx(&2) * x / Cx(&2) = x"))] THEN
    REPEAT GEN_TAC THEN BINOP_TAC THEN AP_TERM_TAC THEN CONV_TAC COMPLEX_RING)

  let COMPLEX_SUB_CSIN ← prove
   r"!w z. csin(w) - csin(z) =
         Cx(&2) * csin((w - z) / Cx(&2)) * ccos((w + z) / Cx(&2))"
   (SIMP_TAC [COMPLEX_MUL_CSIN_CCOS, ← ExceptT.mk (COMPLEX_RING (← q r"Cx(&2) * x / Cx(&2) = x"))] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [complex_sub, ← GSYM CSIN_NEG] THEN
    BINOP_TAC THEN AP_TERM_TAC THEN CONV_TAC COMPLEX_RING)

  let COMPLEX_ADD_CCOS ← prove
   r"!w z. ccos(w) + ccos(z) =
         Cx(&2) * ccos((w + z) / Cx(&2)) * ccos((w - z) / Cx(&2))"
   (SIMP_TAC [COMPLEX_MUL_CCOS_CCOS, ← ExceptT.mk (COMPLEX_RING (← q r"Cx(&2) * x / Cx(&2) = x"))] THEN
    REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [COMPLEX_ADD_SYM] THEN
    BINOP_TAC THEN AP_TERM_TAC THEN CONV_TAC COMPLEX_RING)

  let COMPLEX_SUB_CCOS ← prove
   r"!w z. ccos(w) - ccos(z) =
         Cx(&2) * csin((w + z) / Cx(&2)) * csin((z - w) / Cx(&2))"
   (SIMP_TAC [COMPLEX_MUL_CSIN_CSIN, ← ExceptT.mk (COMPLEX_RING (← q r"Cx(&2) * x / Cx(&2) = x"))] THEN
    REPEAT GEN_TAC THEN BINOP_TAC THEN AP_TERM_TAC THEN CONV_TAC COMPLEX_RING)

  let CCOS_DOUBLE_CCOS ← prove
   r"!z. ccos(Cx(&2) * z) = Cx(&2) * ccos z pow 2 - Cx(&1)"
   (GEN_TAC THEN REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"Cx(&2) * x = x + x")), CCOS_ADD] THEN
    MP_TAC (← SPEC (← q r"z:complex") CSIN_CIRCLE) THEN CONV_TAC COMPLEX_RING)

  let CCOS_DOUBLE_CSIN ← prove
   r"!z. ccos(Cx(&2) * z) = Cx(&1) - Cx(&2) * csin z pow 2"
   (GEN_TAC THEN REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"Cx(&2) * x = x + x")), CCOS_ADD] THEN
    MP_TAC (← SPEC (← q r"z:complex") CSIN_CIRCLE) THEN CONV_TAC COMPLEX_RING)

  let CEXP_EULER ← prove
   r"!z. cexp(ii * z) = ccos(z) + ii * csin(z)"
   (REWRITE_TAC [ccos, csin] THEN CONV_TAC COMPLEX_FIELD)

  let DEMOIVRE ← prove
   r"!z n. (ccos z + ii * csin z) pow n =
         ccos(Cx(&n) * z) + ii * csin(Cx(&n) * z)"
   (REWRITE_TAC [← GSYM CEXP_EULER, ← GSYM CEXP_N] THEN
    REWRITE_TAC [COMPLEX_MUL_AC])

  let exp ← new_definition r"exp(x) = Re(cexp(Cx x))"

  let CNJ_CEXP ← prove
   r"!z. cnj(cexp z) = cexp(cnj z)"
   (GEN_TAC THEN MATCH_MP_TAC SERIES_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [← q r"\n. cnj(z pow n / Cx(&(FACT n)))", ← q r"from 0"] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [SUMS_CNJ, CEXP_CONVERGES],
      REWRITE_TAC [CNJ_DIV, CNJ_CX, CNJ_POW, CEXP_CONVERGES]])

  let REAL_EXP ← prove
   r"!z. real z ==> real(cexp z)"
   (SIMP_TAC [REAL_CNJ, CNJ_CEXP])

  let CX_EXP ← prove
   r"!x. Cx(exp x) = cexp(Cx x)"
   (REWRITE_TAC [exp] THEN MESON_TAC [REAL, REAL_CX, REAL_EXP])

  let REAL_EXP_ADD ← prove
   r"!x y. exp(x + y) = exp(x) * exp(y)"
   (REWRITE_TAC [← GSYM CX_INJ, CX_MUL, CX_EXP, CX_ADD, CEXP_ADD])

  let REAL_EXP_0 ← prove
   r"exp(&0) = &1"
   (REWRITE_TAC [← GSYM CX_INJ, CX_EXP, CEXP_0])

  let REAL_EXP_ADD_MUL ← prove
   r"!x y. exp(x + y) * exp(--x) = exp(y)"
   (ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
    REWRITE_TAC [← GSYM CX_INJ, CX_MUL, CX_EXP, CX_ADD, CX_NEG, CEXP_ADD_MUL])

  let REAL_EXP_NEG_MUL ← prove
   r"!x. exp(x) * exp(--x) = &1"
   (REWRITE_TAC [← GSYM CX_INJ, CX_MUL, CX_EXP, CX_NEG, CEXP_NEG_RMUL])

  let REAL_EXP_NEG_MUL2 ← prove
   r"!x. exp(--x) * exp(x) = &1"
   (REWRITE_TAC [← GSYM CX_INJ, CX_MUL, CX_EXP, CX_NEG, CEXP_NEG_LMUL])

  let REAL_EXP_NEG ← prove
   r"!x. exp(--x) = inv(exp(x))"
   (REWRITE_TAC [← GSYM CX_INJ, CX_INV, CX_EXP, CX_NEG, CEXP_NEG])

  let REAL_EXP_N ← prove
   r"!n x. exp(&n * x) = exp(x) pow n"
   (REWRITE_TAC [← GSYM CX_INJ, CX_EXP, CX_POW, CX_MUL, CEXP_N])

  let REAL_EXP_SUB ← prove
   r"!x y. exp(x - y) = exp(x) / exp(y)"
   (REWRITE_TAC [← GSYM CX_INJ, CX_SUB, CX_DIV, CX_EXP, CEXP_SUB])

  let REAL_EXP_NZ ← prove
   r"!x. ~(exp(x) = &0)"
   (REWRITE_TAC [← GSYM CX_INJ, CX_EXP, CEXP_NZ])

  let REAL_EXP_POS_LE ← prove
   r"!x. &0 <= exp(x)"
   (GEN_TAC THEN SUBST1_TAC (← REAL_ARITH (← q r"x = x / &2 + x / &2")) THEN
    REWRITE_TAC [REAL_EXP_ADD, REAL_LE_SQUARE])

  let REAL_EXP_POS_LT ← prove
   r"!x. &0 < exp(x)"
   (REWRITE_TAC [REAL_LT_LE, REAL_EXP_NZ, REAL_EXP_POS_LE])

  let REAL_EXP_LE_X ← prove
   r"!x. &1 + x <= exp(x)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"&1 + x < &0") THENL
     [MP_TAC (← SPEC (← q r"x:real") REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [exp, RE_DEF] THEN
    MATCH_MP_TAC (← MATCH_MP
     (← ONCE_REWRITE_RULE [← TAUT (← q r"a /\ b /\ c ==> d <=> b ==> a /\ c ==> d")]
          LIM_COMPONENT_LBOUND)
     (← REWRITE_RULE [sums] (← SPEC (← q r"Cx x") CEXP_CONVERGES))) THEN
    SIMP_TAC [DIMINDEX_2, ARITH, TRIVIAL_LIMIT_SEQUENTIALLY,
              VSUM_COMPONENT, EVENTUALLY_SEQUENTIALLY, FROM_0, INTER_UNIV] THEN
    REWRITE_TAC [← GSYM CX_DIV, ← GSYM RE_DEF, RE_CX, ← GSYM CX_POW] THEN
    EXISTS_TAC (← q r"1") THEN SIMP_TAC [SUM_CLAUSES_LEFT, LE_0, ADD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC [real_pow, REAL_POW_1, REAL_DIV_1, REAL_LE_ADDR, REAL_ADD_ASSOC] THEN
    SUBGOAL_THEN
     (← q r"!n. &0 <= sum(2*1..2*n+1) (\k. x pow k / &(FACT k))")
    ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [SUM_PAIR] THEN
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC (← q r"k:num") THEN STRIP_TAC THEN
      REWRITE_TAC [← GSYM ADD1, real_pow, FACT, ← GSYM REAL_OF_NUM_MUL] THEN
      ASM_SIMP_TAC [REAL_OF_NUM_EQ, FACT_NZ, NOT_SUC, ← REAL_FIELD
       (← q r"~(k = &0) /\ ~(f = &0)
        ==> p / f + (x * p) / (k * f) = p / f * (&1 + x / k)")] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ALL_TAC,
        REWRITE_TAC [← REAL_ARITH (← q r"&0 <= a + b <=> --a <= b")] THEN
        ASM_SIMP_TAC [REAL_LE_RDIV_EQ, LT_0, REAL_OF_NUM_LT] THEN
        REWRITE_TAC [← GSYM REAL_OF_NUM_SUC] THEN ASM_REAL_ARITH_TAC],
      RULE_ASSUM_TAC (REWRITE_RULE [MULT_CLAUSES]) THEN
      X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN
      MP_TAC (← SPEC (← q r"n - 1") EVEN_OR_ODD) THEN
      ASM_SIMP_TAC [EVEN_EXISTS, ODD_EXISTS,
                    ← ARITH_RULE (← q r"1 <= n ==> (n - 1 = d <=> n = SUC d)")] THEN
      STRIP_TAC THENL [ASM_MESON_TAC [ADD1], ALL_TAC] THEN
      ASM_REWRITE_TAC [← ARITH_RULE (← q r"SUC(2 * n) = 2 * n + 1")] THEN
      ASM_REWRITE_TAC [SUM_CLAUSES_NUMSEG] THEN
      COND_CASES_TAC THENL [ALL_TAC, ASM_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN
      ASM_REWRITE_TAC [← ARITH_RULE (← q r"SUC(2 * m + 1) = 2 * (m + 1)")]] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC [REAL_POS] THEN
    ASM_SIMP_TAC [← GSYM REAL_POW_POW, REAL_POW_LE, REAL_LE_POW_2])

  let REAL_EXP_LT_1 ← prove
   r"!x. &0 < x ==> &1 < exp(x)"
   (MP_TAC REAL_EXP_LE_X THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC)

  let REAL_EXP_MONO_IMP ← prove
   r"!x y. x < y ==> exp(x) < exp(y)"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_SUB_LT] THEN
    DISCH_THEN (MP_TAC o MATCH_MP REAL_EXP_LT_1) THEN
    SIMP_TAC [REAL_EXP_SUB, REAL_LT_RDIV_EQ, REAL_EXP_POS_LT, REAL_MUL_LID])

  let REAL_EXP_MONO_LT ← prove
   r"!x y. exp(x) < exp(y) <=> x < y"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC (← REAL_ARITH
     (← q r"(x < y ==> f < g) /\ (x = y ==> f = g) /\ (y < x ==> g < f)
      ==> (f < g <=> x < y)")) THEN
    SIMP_TAC [REAL_EXP_MONO_IMP])

  let REAL_EXP_MONO_LE ← prove
   r"!x y. exp(x) <= exp(y) <=> x <= y"
   (REWRITE_TAC [← GSYM REAL_NOT_LT, REAL_EXP_MONO_LT])

  let REAL_EXP_INJ ← prove
   r"!x y. (exp(x) = exp(y)) <=> (x = y)"
   (REWRITE_TAC [← GSYM REAL_LE_ANTISYM, REAL_EXP_MONO_LE])

  let REAL_EXP_EQ_1 ← prove
   r"!x. exp(x) = &1 <=> x = &0"
   (ONCE_REWRITE_TAC [← GSYM REAL_EXP_0] THEN REWRITE_TAC [REAL_EXP_INJ])

  let REAL_ABS_EXP ← prove
   r"!x. abs(exp x) = exp x"
   (REWRITE_TAC [real_abs, REAL_EXP_POS_LE])

  let REAL_EXP_SUM ← prove
   r"!f s. FINITE s ==> exp(sum s f) = product s (\x. exp(f x))"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [SUM_CLAUSES, PRODUCT_CLAUSES, REAL_EXP_ADD, REAL_EXP_0])

  let REAL_EXP_BOUND_LEMMA ← prove
   r"!x. &0 <= x /\ x <= inv(&2) ==> exp(x) <= &1 + &2 * x"
   (REPEAT STRIP_TAC THEN MP_TAC (← SPEC (← q r"Cx x") CEXP_BOUND_LEMMA) THEN
    REWRITE_TAC [← GSYM CX_EXP, COMPLEX_NORM_CX, RE_CX] THEN
    ASM_REAL_ARITH_TAC)

  pure { ccos, csin, CSIN_0, CCOS_0, CSIN_CIRCLE, CSIN_ADD, CCOS_ADD, CSIN_NEG, CCOS_NEG,
         CSIN_DOUBLE, CCOS_DOUBLE, CSIN_SUB, CCOS_SUB, COMPLEX_MUL_CSIN_CSIN,
         COMPLEX_MUL_CSIN_CCOS, COMPLEX_MUL_CCOS_CSIN, COMPLEX_MUL_CCOS_CCOS,
         COMPLEX_ADD_CSIN, COMPLEX_SUB_CSIN, COMPLEX_ADD_CCOS, COMPLEX_SUB_CCOS,
         CCOS_DOUBLE_CCOS, CCOS_DOUBLE_CSIN, CEXP_EULER, DEMOIVRE, exp, CNJ_CEXP,
         REAL_EXP, CX_EXP, REAL_EXP_ADD, REAL_EXP_0, REAL_EXP_ADD_MUL, REAL_EXP_NEG_MUL,
         REAL_EXP_NEG_MUL2, REAL_EXP_NEG, REAL_EXP_N, REAL_EXP_SUB, REAL_EXP_NZ,
         REAL_EXP_POS_LE, REAL_EXP_POS_LT, REAL_EXP_LE_X, REAL_EXP_LT_1,
         REAL_EXP_MONO_IMP, REAL_EXP_MONO_LT, REAL_EXP_MONO_LE, REAL_EXP_INJ,
         REAL_EXP_EQ_1, REAL_ABS_EXP, REAL_EXP_SUM, REAL_EXP_BOUND_LEMMA }
/- ------------------------------------------------------------------------- -/
/- Real trig functions, their reality, derivatives of complex versions; a    -/
/- slew of theorems for compatibility with the old transc.ml; real/imaginary -/
/- separation in Euler's formula; special intermediate value theorems.      -/
/- (transcendentals.ml 604-938)                                             -/
/- ------------------------------------------------------------------------- -/

structure TSC where
  sin : thm
  cos : thm
  CNJ_CSIN : thm
  CNJ_CCOS : thm
  REAL_SIN : thm
  REAL_COS : thm
  CX_SIN : thm
  CX_COS : thm
  HAS_COMPLEX_DERIVATIVE_CSIN : thm
  COMPLEX_DIFFERENTIABLE_AT_CSIN : thm
  COMPLEX_DIFFERENTIABLE_WITHIN_CSIN : thm
  HAS_COMPLEX_DERIVATIVE_CCOS : thm
  COMPLEX_DIFFERENTIABLE_AT_CCOS : thm
  COMPLEX_DIFFERENTIABLE_WITHIN_CCOS : thm
  CONTINUOUS_AT_CSIN : thm
  CONTINUOUS_WITHIN_CSIN : thm
  CONTINUOUS_ON_CSIN : thm
  HOLOMORPHIC_ON_CSIN : thm
  CONTINUOUS_AT_CCOS : thm
  CONTINUOUS_WITHIN_CCOS : thm
  CONTINUOUS_ON_CCOS : thm
  HOLOMORPHIC_ON_CCOS : thm
  SIN_0 : thm
  COS_0 : thm
  SIN_CIRCLE : thm
  SIN_ADD : thm
  COS_ADD : thm
  SIN_NEG : thm
  COS_NEG : thm
  SIN_DOUBLE : thm
  COS_DOUBLE : thm
  COS_DOUBLE_COS : thm
  SIN_BOUND : thm
  COS_BOUND : thm
  SIN_BOUNDS : thm
  COS_BOUNDS : thm
  COS_ABS : thm
  SIN_SUB : thm
  COS_SUB : thm
  REAL_MUL_SIN_SIN : thm
  REAL_MUL_SIN_COS : thm
  REAL_MUL_COS_SIN : thm
  REAL_MUL_COS_COS : thm
  REAL_ADD_SIN : thm
  REAL_SUB_SIN : thm
  REAL_ADD_COS : thm
  REAL_SUB_COS : thm
  COS_DOUBLE_SIN : thm
  EULER : thm
  RE_CEXP : thm
  IM_CEXP : thm
  RE_CSIN : thm
  IM_CSIN : thm
  RE_CCOS : thm
  IM_CCOS : thm
  IVT_INCREASING_RE : thm
  IVT_DECREASING_RE : thm
  IVT_INCREASING_IM : thm
  IVT_DECREASING_IM : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupTSC [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) (BTSB : TSB) : ExceptT String IO TSC := do
  -- @@SCOPE BEGIN
  let { CEXP_ADD, .. } := BTSA
  let { ccos, CCOS_0, CCOS_ADD, CCOS_DOUBLE, CCOS_NEG, CCOS_SUB, CEXP_EULER, CNJ_CEXP,
        COMPLEX_ADD_CCOS, COMPLEX_ADD_CSIN, COMPLEX_MUL_CCOS_CCOS, COMPLEX_MUL_CCOS_CSIN,
        COMPLEX_MUL_CSIN_CCOS, COMPLEX_MUL_CSIN_CSIN, COMPLEX_SUB_CCOS, COMPLEX_SUB_CSIN,
        csin, CSIN_0, CSIN_ADD, CSIN_CIRCLE, CSIN_DOUBLE, CSIN_NEG, CSIN_SUB, CX_EXP,
        .. } := BTSB
  let { CONTINUOUS_COMPLEX_MUL, .. } := D.knc
  let { complex_differentiable, COMPLEX_DIFFERENTIABLE_AT_WITHIN,
        HAS_COMPLEX_DERIVATIVE_AT_WITHIN, HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV,
        HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT, holomorphic_on, .. } := D.kne
  let { add_complex_differentiation_theorems, COMPLEX_DIFF_TAC, .. } := D.knk
  let { CONTINUOUS_AT_COMPOSE, .. } := D.qtopology
  let { RE_DEF, .. } := D.cn.cxa
  let { COMPLEX_ADD_AC, COMPLEX_MUL_LNEG, COMPLEX_NEG_NEG, .. } := D.cn.cxb
  let { COMPLEX_EXPAND, COMPLEX_NORM_CX, CX_ADD, CX_DIV, CX_INJ, CX_MUL, CX_NEG, CX_POW,
        CX_SUB, IM_ADD, IM_CX, IM_DIV_CX, IM_MUL_CX, IM_MUL_II, IM_NEG, IM_SUB, RE_ADD,
        RE_CX, RE_DIV_CX, RE_MUL_CX, RE_MUL_II, RE_NEG, RE_SUB, .. } := D.cn.cxc
  let { COMPLEX_FIELD, .. } := D.cn.cxe
  let { CNJ_ADD, CNJ_CX, CNJ_DIV, CNJ_II, CNJ_MUL, CNJ_NEG, CNJ_SUB, .. } := D.cn.cxg
  let { REAL, REAL_CNJ, REAL_CX, .. } := D.cn.cxi
  let { IVT_INCREASING_COMPONENT_1, .. } := D.cn.ms.qconvex
  let { MESON_TAC, new_definition, REAL_ARITH_TAC, REAL_RING, .. } := D.cn.cx.cvx
  let { REAL_LE_SQUARE, .. } := D.cn.cx.cpx
  let { CONTINUOUS_NEG, .. } := D.cn.ms.ig.qtopology
  let { ARITH, CONJ_ASSOC, DIMINDEX_2, ETA_AX, FORALL_AND_THM, .. } := D.cn.cx.cvx.core1
  let { MONO_FORALL, REAL_ABS_NUM, .. } := D.cn.cx.cvx.core3
  let { REAL_EQ_NEG2, REAL_LE_NEG2, REAL_LE_SQUARE_ABS, .. } := D.cn.cx.cvx.core4
  let { REAL_NEG_NEG, .. } := D.cn.cx.cvx.core5
  let { o_THM, real_abs, .. } := D.cn.cx.cvx.core6
  let { DROP_SUB, EXISTS_DROP, LIFT_DROP, NORM_1, .. } := D.cn.cx.cvx.vec2
  let { dist, drop, .. } := D.cn.cx.cvx.vec4
  let { CONTINUOUS_AT_IMP_CONTINUOUS_ON, .. } := D.cn.cx.cvx.top2
  let { CONTINUOUS_CONST, .. } := D.cn.cx.cvx.top3
  let { IN_INTERVAL_1, .. } := D.cn.cx.cvx.top4
  let { continuous_at, .. } := D.cn.cx.cvx.top5
  let { CONTINUOUS_AT_WITHIN, .. } := D.cn.ms.ig.dv.qtopology1
  -- @@SCOPE END

  let sin ← new_definition r"sin(x) = Re(csin(Cx x))"

  let cos ← new_definition r"cos(x) = Re(ccos(Cx x))"

  let CNJ_CSIN ← prove
   r"!z. cnj(csin z) = csin(cnj z)"
   (REWRITE_TAC [csin, CNJ_DIV, CNJ_SUB, CNJ_MUL, CNJ_CX, CNJ_CEXP,
                 CNJ_NEG, CNJ_II, COMPLEX_NEG_NEG] THEN
    CONV_TAC COMPLEX_FIELD)

  let CNJ_CCOS ← prove
   r"!z. cnj(ccos z) = ccos(cnj z)"
   (REWRITE_TAC [ccos, CNJ_DIV, CNJ_ADD, CNJ_MUL, CNJ_CX, CNJ_CEXP,
                 CNJ_NEG, CNJ_II, COMPLEX_NEG_NEG, COMPLEX_ADD_AC])

  let REAL_SIN ← prove
   r"!z. real z ==> real(csin z)"
   (SIMP_TAC [REAL_CNJ, CNJ_CSIN])

  let REAL_COS ← prove
   r"!z. real z ==> real(ccos z)"
   (SIMP_TAC [REAL_CNJ, CNJ_CCOS])

  let CX_SIN ← prove
   r"!x. Cx(sin x) = csin(Cx x)"
   (REWRITE_TAC [sin] THEN MESON_TAC [REAL, REAL_CX, REAL_SIN])

  let CX_COS ← prove
   r"!x. Cx(cos x) = ccos(Cx x)"
   (REWRITE_TAC [cos] THEN MESON_TAC [REAL, REAL_CX, REAL_COS])

  let HAS_COMPLEX_DERIVATIVE_CSIN ← prove
   r"!z. (csin has_complex_derivative ccos z) (at z)"
   (GEN_TAC THEN GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [← GSYM ETA_AX] THEN
    REWRITE_TAC [csin, ccos] THEN COMPLEX_DIFF_TAC THEN
    CONV_TAC COMPLEX_FIELD)

  let COMPLEX_DIFFERENTIABLE_AT_CSIN ← prove
   r"!z. csin complex_differentiable at z"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_CSIN])

  let COMPLEX_DIFFERENTIABLE_WITHIN_CSIN ← prove
   r"!s z. csin complex_differentiable (at z within s)"
   (MESON_TAC [COMPLEX_DIFFERENTIABLE_AT_WITHIN,
               COMPLEX_DIFFERENTIABLE_AT_CSIN])

  add_complex_differentiation_theorems
   (CONJUNCTS (← REWRITE_RULE [FORALL_AND_THM]
     (← MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV
               HAS_COMPLEX_DERIVATIVE_CSIN)))

  let HAS_COMPLEX_DERIVATIVE_CCOS ← prove
   r"!z. (ccos has_complex_derivative --csin z) (at z)"
   (GEN_TAC THEN GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [← GSYM ETA_AX] THEN
    REWRITE_TAC [csin, ccos] THEN COMPLEX_DIFF_TAC THEN
    CONV_TAC COMPLEX_FIELD)

  let COMPLEX_DIFFERENTIABLE_AT_CCOS ← prove
   r"!z. ccos complex_differentiable at z"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_CCOS])

  let COMPLEX_DIFFERENTIABLE_WITHIN_CCOS ← prove
   r"!s z. ccos complex_differentiable (at z within s)"
   (MESON_TAC [COMPLEX_DIFFERENTIABLE_AT_WITHIN,
               COMPLEX_DIFFERENTIABLE_AT_CCOS])

  add_complex_differentiation_theorems
   (CONJUNCTS (← REWRITE_RULE [FORALL_AND_THM]
     (← MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV
               HAS_COMPLEX_DERIVATIVE_CCOS)))

  let CONTINUOUS_AT_CSIN ← prove
   r"!z. csin continuous at z"
   (MESON_TAC [HAS_COMPLEX_DERIVATIVE_CSIN,
               HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT])

  let CONTINUOUS_WITHIN_CSIN ← prove
   r"!s z. csin continuous (at z within s)"
   (MESON_TAC [CONTINUOUS_AT_WITHIN, CONTINUOUS_AT_CSIN])

  let CONTINUOUS_ON_CSIN ← prove
   r"!s. csin continuous_on s"
   (MESON_TAC [CONTINUOUS_AT_IMP_CONTINUOUS_ON, CONTINUOUS_AT_CSIN])

  let HOLOMORPHIC_ON_CSIN ← prove
   r"!s. csin holomorphic_on s"
   (REWRITE_TAC [holomorphic_on] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN, HAS_COMPLEX_DERIVATIVE_CSIN])

  let CONTINUOUS_AT_CCOS ← prove
   r"!z. ccos continuous at z"
   (MESON_TAC [HAS_COMPLEX_DERIVATIVE_CCOS,
               HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT])

  let CONTINUOUS_WITHIN_CCOS ← prove
   r"!s z. ccos continuous (at z within s)"
   (MESON_TAC [CONTINUOUS_AT_WITHIN, CONTINUOUS_AT_CCOS])

  let CONTINUOUS_ON_CCOS ← prove
   r"!s. ccos continuous_on s"
   (MESON_TAC [CONTINUOUS_AT_IMP_CONTINUOUS_ON, CONTINUOUS_AT_CCOS])

  let HOLOMORPHIC_ON_CCOS ← prove
   r"!s. ccos holomorphic_on s"
   (REWRITE_TAC [holomorphic_on] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN, HAS_COMPLEX_DERIVATIVE_CCOS])

  let SIN_0 ← prove
   r"sin(&0) = &0"
   (REWRITE_TAC [← GSYM CX_INJ, CX_SIN, CSIN_0])

  let COS_0 ← prove
   r"cos(&0) = &1"
   (REWRITE_TAC [← GSYM CX_INJ, CX_COS, CCOS_0])

  let SIN_CIRCLE ← prove
   r"!x. (sin(x) pow 2) + (cos(x) pow 2) = &1"
   (REWRITE_TAC [← GSYM CX_INJ, CX_COS, CX_SIN, CX_ADD, CX_POW, CSIN_CIRCLE])

  let SIN_ADD ← prove
   r"!x y. sin(x + y) = sin(x) * cos(y) + cos(x) * sin(y)"
   (REWRITE_TAC [← GSYM CX_INJ, CX_COS, CX_SIN, CX_ADD, CX_MUL, CSIN_ADD])

  let COS_ADD ← prove
   r"!x y. cos(x + y) = cos(x) * cos(y) - sin(x) * sin(y)"
   (REWRITE_TAC [← GSYM CX_INJ, CX_COS, CX_SIN, CX_ADD, CX_SUB, CX_MUL, CCOS_ADD])

  let SIN_NEG ← prove
   r"!x. sin(--x) = --(sin(x))"
   (REWRITE_TAC [← GSYM CX_INJ, CX_SIN, CX_NEG, CSIN_NEG])

  let COS_NEG ← prove
   r"!x. cos(--x) = cos(x)"
   (REWRITE_TAC [← GSYM CX_INJ, CX_COS, CX_NEG, CCOS_NEG])

  let SIN_DOUBLE ← prove
   r"!x. sin(&2 * x) = &2 * sin(x) * cos(x)"
   (REWRITE_TAC [← GSYM CX_INJ, CX_SIN, CX_COS, CX_MUL, CSIN_DOUBLE])

  let COS_DOUBLE ← prove
   r"!x. cos(&2 * x) = (cos(x) pow 2) - (sin(x) pow 2)"
   (SIMP_TAC [← GSYM CX_INJ, CX_SIN, CX_COS, CX_SUB, CX_MUL, CX_POW, CCOS_DOUBLE])

  let COS_DOUBLE_COS ← prove
   r"!x. cos(&2 * x) = &2 * cos(x) pow 2 - &1"
   (MP_TAC SIN_CIRCLE THEN MATCH_MP_TAC MONO_FORALL THEN
    REWRITE_TAC [COS_DOUBLE] THEN REAL_ARITH_TAC)

  let (SIN_BOUND, COS_BOUND) ← CONJ_PAIR (← prove
   r"(!x. abs(sin x) <= &1) /\ (!x. abs(cos x) <= &1)"
   (CONJ_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_ABS_NUM] THEN
    ONCE_REWRITE_TAC [REAL_LE_SQUARE_ABS] THEN
    MP_TAC (← SPEC (← q r"x:real") SIN_CIRCLE) THEN
    MAP_EVERY (MP_TAC o C SPEC REAL_LE_SQUARE) [← q r"sin x", ← q r"cos x"] THEN
    REAL_ARITH_TAC))

  let SIN_BOUNDS ← prove
   r"!x. --(&1) <= sin(x) /\ sin(x) <= &1"
   (MP_TAC SIN_BOUND THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC)

  let COS_BOUNDS ← prove
   r"!x. --(&1) <= cos(x) /\ cos(x) <= &1"
   (MP_TAC COS_BOUND THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC)

  let COS_ABS ← prove
   r"!x. cos(abs x) = cos(x)"
   (REWRITE_TAC [real_abs] THEN MESON_TAC [COS_NEG])

  let SIN_SUB ← prove
   r"!w z. sin(w - z) = sin(w) * cos(z) - cos(w) * sin(z)"
   (REWRITE_TAC [← GSYM CX_INJ, CX_SIN, CX_COS, CX_SUB, CX_MUL, CSIN_SUB])

  let COS_SUB ← prove
   r"!w z. cos(w - z) = cos(w) * cos(z) + sin(w) * sin(z)"
   (REWRITE_TAC [← GSYM CX_INJ, CX_SIN, CX_COS, CX_SUB, CX_ADD, CX_MUL, CCOS_SUB])

  let REAL_MUL_SIN_SIN ← prove
   r"!x y. sin(x) * sin(y) = (cos(x - y) - cos(x + y)) / &2"
   (REWRITE_TAC [← GSYM CX_INJ, CX_COS, CX_SIN, CX_ADD, CX_SUB, CX_MUL, CX_DIV] THEN
    REWRITE_TAC [COMPLEX_MUL_CSIN_CSIN])

  let REAL_MUL_SIN_COS ← prove
   r"!x y. sin(x) * cos(y) = (sin(x + y) + sin(x - y)) / &2"
   (REWRITE_TAC [← GSYM CX_INJ, CX_COS, CX_SIN, CX_ADD, CX_SUB, CX_MUL, CX_DIV] THEN
    REWRITE_TAC [COMPLEX_MUL_CSIN_CCOS])

  let REAL_MUL_COS_SIN ← prove
   r"!x y. cos(x) * sin(y) = (sin(x + y) - sin(x - y)) / &2"
   (REWRITE_TAC [← GSYM CX_INJ, CX_COS, CX_SIN, CX_ADD, CX_SUB, CX_MUL, CX_DIV] THEN
    REWRITE_TAC [COMPLEX_MUL_CCOS_CSIN])

  let REAL_MUL_COS_COS ← prove
   r"!x y. cos(x) * cos(y) = (cos(x - y) + cos(x + y)) / &2"
   (REWRITE_TAC [← GSYM CX_INJ, CX_COS, CX_SIN, CX_ADD, CX_SUB, CX_MUL, CX_DIV] THEN
    REWRITE_TAC [COMPLEX_MUL_CCOS_CCOS])

  let REAL_ADD_SIN ← prove
   r"!x y. sin(x) + sin(y) = &2 * sin((x + y) / &2) * cos((x - y) / &2)"
   (REWRITE_TAC [← GSYM CX_INJ, CX_COS, CX_SIN, CX_ADD, CX_SUB, CX_MUL, CX_DIV] THEN
    REWRITE_TAC [COMPLEX_ADD_CSIN])

  let REAL_SUB_SIN ← prove
   r"!x y. sin(x) - sin(y) = &2 * sin((x - y) / &2) * cos((x + y) / &2)"
   (REWRITE_TAC [← GSYM CX_INJ, CX_COS, CX_SIN, CX_ADD, CX_SUB, CX_MUL, CX_DIV] THEN
    REWRITE_TAC [COMPLEX_SUB_CSIN])

  let REAL_ADD_COS ← prove
   r"!x y. cos(x) + cos(y) = &2 * cos((x + y) / &2) * cos((x - y) / &2)"
   (REWRITE_TAC [← GSYM CX_INJ, CX_COS, CX_SIN, CX_ADD, CX_SUB, CX_MUL, CX_DIV] THEN
    REWRITE_TAC [COMPLEX_ADD_CCOS])

  let REAL_SUB_COS ← prove
   r"!x y. cos(x) - cos(y) = &2 * sin((x + y) / &2) * sin((y - x) / &2)"
   (REWRITE_TAC [← GSYM CX_INJ, CX_COS, CX_SIN, CX_ADD, CX_SUB, CX_MUL, CX_DIV] THEN
    REWRITE_TAC [COMPLEX_SUB_CCOS])

  let COS_DOUBLE_SIN ← prove
   r"!x. cos(&2 * x) = &1 - &2 * sin x pow 2"
   (GEN_TAC THEN REWRITE_TAC [← REAL_RING (← q r"&2 * x = x + x"), COS_ADD] THEN
    MP_TAC (← SPEC (← q r"x:real") SIN_CIRCLE) THEN CONV_TAC (fun t => REAL_RING t))

  let EULER ← prove
   r"!z. cexp(z) = Cx(exp(Re z)) * (Cx(cos(Im z)) + ii * Cx(sin(Im z)))"
   (GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [COMPLEX_EXPAND] THEN
    REWRITE_TAC [CEXP_ADD, CEXP_EULER, ← GSYM CX_SIN, ← GSYM CX_COS, ← GSYM CX_EXP])

  let RE_CEXP ← prove
   r"!z. Re(cexp z) = exp(Re z) * cos(Im z)"
   (REWRITE_TAC [EULER, RE_ADD, RE_MUL_CX, RE_MUL_II, IM_CX, RE_CX] THEN
    REAL_ARITH_TAC)

  let IM_CEXP ← prove
   r"!z. Im(cexp z) = exp(Re z) * sin(Im z)"
   (REWRITE_TAC [EULER, IM_ADD, IM_MUL_CX, IM_MUL_II, IM_CX, RE_CX] THEN
    REAL_ARITH_TAC)

  let RE_CSIN ← prove
   r"!z. Re(csin z) = (exp(Im z) + exp(--(Im z))) / &2 * sin(Re z)"
   (GEN_TAC THEN REWRITE_TAC [csin] THEN
    SIMP_TAC [← ExceptT.mk (COMPLEX_FIELD
      (← q r"x / (Cx(&2) * ii) = ii * --(x / Cx(&2))"))] THEN
    REWRITE_TAC [IM_MUL_II, IM_DIV_CX, RE_NEG, IM_SUB, IM_CEXP,
                 RE_MUL_II, COMPLEX_MUL_LNEG, IM_NEG] THEN
    REWRITE_TAC [REAL_NEG_NEG, SIN_NEG] THEN CONV_TAC (fun t => REAL_RING t))

  let IM_CSIN ← prove
   r"!z. Im(csin z) = (exp(Im z) - exp(--(Im z))) / &2 * cos(Re z)"
   (GEN_TAC THEN REWRITE_TAC [csin] THEN
    SIMP_TAC [← ExceptT.mk (COMPLEX_FIELD
      (← q r"x / (Cx(&2) * ii) = ii * --(x / Cx(&2))"))] THEN
    REWRITE_TAC [IM_MUL_II, RE_DIV_CX, RE_NEG, RE_SUB, RE_CEXP,
                 RE_MUL_II, COMPLEX_MUL_LNEG, IM_NEG] THEN
    REWRITE_TAC [REAL_NEG_NEG, COS_NEG] THEN CONV_TAC (fun t => REAL_RING t))

  let RE_CCOS ← prove
   r"!z. Re(ccos z) = (exp(Im z) + exp(--(Im z))) / &2 * cos(Re z)"
   (GEN_TAC THEN REWRITE_TAC [ccos] THEN
    REWRITE_TAC [RE_DIV_CX, RE_ADD, RE_CEXP, COMPLEX_MUL_LNEG,
                 RE_MUL_II, IM_MUL_II, RE_NEG, IM_NEG, COS_NEG] THEN
    REWRITE_TAC [REAL_NEG_NEG] THEN CONV_TAC (fun t => REAL_RING t))

  let IM_CCOS ← prove
   r"!z. Im(ccos z) = (exp(--(Im z)) - exp(Im z)) / &2 * sin(Re z)"
   (GEN_TAC THEN REWRITE_TAC [ccos] THEN
    REWRITE_TAC [IM_DIV_CX, IM_ADD, IM_CEXP, COMPLEX_MUL_LNEG,
                 RE_MUL_II, IM_MUL_II, RE_NEG, IM_NEG, SIN_NEG] THEN
    REWRITE_TAC [REAL_NEG_NEG] THEN CONV_TAC (fun t => REAL_RING t))

  let IVT_INCREASING_RE ← prove
   r"!f a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> f continuous at (Cx x)) /\
        Re(f(Cx a)) <= y /\ y <= Re(f(Cx b))
        ==> ?x. a <= x /\ x <= b /\ Re(f(Cx x)) = y"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"(f:complex->complex) o Cx o drop",
                      ← q r"lift a", ← q r"lift b", ← q r"y:real", ← q r"1"]
          IVT_INCREASING_COMPONENT_1) THEN
    REWRITE_TAC [EXISTS_DROP, ← GSYM drop, LIFT_DROP, o_THM, ← GSYM RE_DEF] THEN
    ASM_REWRITE_TAC [IN_INTERVAL_1, ← GSYM CONJ_ASSOC, LIFT_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [DIMINDEX_2, ARITH] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
    ASM_SIMP_TAC [o_THM] THEN REWRITE_TAC [continuous_at, o_THM] THEN
    REWRITE_TAC [dist, ← GSYM CX_SUB, ← GSYM DROP_SUB, COMPLEX_NORM_CX] THEN
    REWRITE_TAC [← GSYM NORM_1] THEN MESON_TAC [])

  let IVT_DECREASING_RE ← prove
   r"!f a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> f continuous at (Cx x)) /\
        Re(f(Cx b)) <= y /\ y <= Re(f(Cx a))
        ==> ?x. a <= x /\ x <= b /\ Re(f(Cx x)) = y"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_EQ_NEG2] THEN
    REWRITE_TAC [← GSYM RE_NEG] THEN MATCH_MP_TAC IVT_INCREASING_RE THEN
    ASM_SIMP_TAC [CONTINUOUS_NEG, RE_NEG, REAL_LE_NEG2])

  let IVT_INCREASING_IM ← prove
   r"!f a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> f continuous at (Cx x)) /\
        Im(f(Cx a)) <= y /\ y <= Im(f(Cx b))
        ==> ?x. a <= x /\ x <= b /\ Im(f(Cx x)) = y"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_EQ_NEG2] THEN
    REWRITE_TAC [← SYM (← CONJUNCT2 (← SPEC_ALL RE_MUL_II))] THEN
    MATCH_MP_TAC IVT_DECREASING_RE THEN
    ASM_SIMP_TAC [CONTINUOUS_COMPLEX_MUL, ETA_AX, CONTINUOUS_CONST] THEN
    ASM_REWRITE_TAC [RE_MUL_II, REAL_LE_NEG2])

  let IVT_DECREASING_IM ← prove
   r"!f a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> f continuous at (Cx x)) /\
        Im(f(Cx b)) <= y /\ y <= Im(f(Cx a))
        ==> ?x. a <= x /\ x <= b /\ Im(f(Cx x)) = y"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_EQ_NEG2] THEN
    REWRITE_TAC [← GSYM IM_NEG] THEN MATCH_MP_TAC IVT_INCREASING_IM THEN
    ASM_SIMP_TAC [CONTINUOUS_NEG, IM_NEG, REAL_LE_NEG2])

  pure { sin, cos, CNJ_CSIN, CNJ_CCOS, REAL_SIN, REAL_COS, CX_SIN, CX_COS,
         HAS_COMPLEX_DERIVATIVE_CSIN, COMPLEX_DIFFERENTIABLE_AT_CSIN,
         COMPLEX_DIFFERENTIABLE_WITHIN_CSIN, HAS_COMPLEX_DERIVATIVE_CCOS,
         COMPLEX_DIFFERENTIABLE_AT_CCOS, COMPLEX_DIFFERENTIABLE_WITHIN_CCOS,
         CONTINUOUS_AT_CSIN, CONTINUOUS_WITHIN_CSIN, CONTINUOUS_ON_CSIN,
         HOLOMORPHIC_ON_CSIN, CONTINUOUS_AT_CCOS, CONTINUOUS_WITHIN_CCOS,
         CONTINUOUS_ON_CCOS, HOLOMORPHIC_ON_CCOS, SIN_0, COS_0, SIN_CIRCLE, SIN_ADD,
         COS_ADD, SIN_NEG, COS_NEG, SIN_DOUBLE, COS_DOUBLE, COS_DOUBLE_COS, SIN_BOUND,
         COS_BOUND, SIN_BOUNDS, COS_BOUNDS, COS_ABS, SIN_SUB, COS_SUB, REAL_MUL_SIN_SIN,
         REAL_MUL_SIN_COS, REAL_MUL_COS_SIN, REAL_MUL_COS_COS, REAL_ADD_SIN,
         REAL_SUB_SIN, REAL_ADD_COS, REAL_SUB_COS, COS_DOUBLE_SIN, EULER, RE_CEXP,
         IM_CEXP, RE_CSIN, IM_CSIN, RE_CCOS, IM_CCOS, IVT_INCREASING_RE,
         IVT_DECREASING_RE, IVT_INCREASING_IM, IVT_DECREASING_IM }
/- ------------------------------------------------------------------------- -/
/- Some minimal properties of real logs help to define complex logs; deduce  -/
/- periodicity just from derivative and zero values; the definition of pi.  -/
/- (transcendentals.ml 939-1175)                                            -/
/- ------------------------------------------------------------------------- -/

structure TSD where
  log_def : thm
  EXP_LOG : thm
  LOG_EXP : thm
  REAL_EXP_LOG : thm
  LOG_MUL : thm
  LOG_INJ : thm
  LOG_1 : thm
  LOG_INV : thm
  LOG_DIV : thm
  LOG_MONO_LT : thm
  LOG_MONO_LT_IMP : thm
  LOG_MONO_LT_REV : thm
  LOG_MONO_LE : thm
  LOG_MONO_LE_IMP : thm
  LOG_MONO_LE_REV : thm
  LOG_POW : thm
  LOG_LE_STRONG : thm
  LOG_LE : thm
  LOG_LT_X : thm
  LOG_POS : thm
  LOG_POS_LT : thm
  LOG_PRODUCT : thm
  SIN_NEARZERO : thm
  SIN_NONTRIVIAL : thm
  COS_NONTRIVIAL : thm
  COS_DOUBLE_BOUND : thm
  COS_GOESNEGATIVE_LEMMA : thm
  COS_GOESNEGATIVE : thm
  COS_HASZERO : thm
  SIN_HASZERO : thm
  SIN_HASZERO_MINIMAL : thm
  pi : thm
  PI_WORKS : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupTSD [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) (BTSB : TSB) (BTSC : TSC) : ExceptT String IO TSD := do
  -- @@SCOPE BEGIN
  let { CONTINUOUS_AT_CEXP, .. } := BTSA
  let { CCOS_0, CSIN_0, CX_EXP, REAL_EXP_0, REAL_EXP_ADD, REAL_EXP_INJ, REAL_EXP_LE_X,
        REAL_EXP_MONO_LE, REAL_EXP_MONO_LT, REAL_EXP_N, REAL_EXP_NEG, REAL_EXP_POS_LT,
        .. } := BTSB
  let { CONTINUOUS_ON_CSIN, COS_0, COS_BOUNDS, COS_DOUBLE_COS, CX_COS, CX_SIN,
        HAS_COMPLEX_DERIVATIVE_CCOS, HAS_COMPLEX_DERIVATIVE_CSIN, IVT_DECREASING_RE,
        IVT_INCREASING_RE, SIN_CIRCLE, SIN_DOUBLE, .. } := BTSC
  let { CLOSED_HALFSPACE_IM_EQ, CLOSED_HALFSPACE_RE_GE, .. } := D.kna
  let { has_complex_derivative, HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT, .. } := D.kne
  let { COMPLEX_EQ, FORALL_COMPLEX, IM, RE, .. } := D.cn.cxa
  let { COMPLEX_MUL_LID, COMPLEX_MUL_LZERO, COMPLEX_SUB_RZERO, .. } := D.cn.cxb
  let { COMPLEX_NORM_CX, CX_INJ, CX_SUB, IM_CX, RE_CX, .. } := D.cn.cxc
  let { HAS_DERIVATIVE_AT_ALT, .. } := D.cn.ms.qderivatives
  let { ARITH_RULE, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INDUCT_TAC, MESON_TAC,
        new_definition, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD, REAL_RAT_REDUCE_CONV,
        SELECT_CONV, .. } := D.cn.cx.cvx
  let { PRODUCT_CLAUSES, real_sub, .. } := D.cn.cx.cpx
  let { PRODUCT_POS_LT, .. } := D.cn.ms.ig.qproducts
  let { REAL_ARCH_POW2, .. } := D.cn.ms.ig.qsession
  let { CONJ_ASSOC, EXISTS_IN_IMAGE, EXTENSION, FINITE_INDUCT_STRONG,
        .. } := D.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_IN_INSERT, IMP_CONJ, .. } := D.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, IN_INTER, IN_SING, MEMBER_NOT_EMPTY, MONO_EXISTS,
        MONO_FORALL, NOT_EXISTS_THM, .. } := D.cn.cx.cvx.core3
  let { REAL_LE_INV2, REAL_LE_INV_EQ, REAL_LE_LMUL, REAL_LE_LT, REAL_LE_REFL, REAL_LE_RMUL,
        REAL_LE_TRANS, REAL_LT_01, REAL_LT_IMP_LE, REAL_LT_INV_EQ, REAL_LT_LDIV_EQ,
        REAL_LT_MUL, REAL_LT_REFL, REAL_LTE_TRANS, .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LID, REAL_NOT_LT, REAL_POS, REAL_POW_2, REAL_POW_LT,
        REAL_SUB_LT, RIGHT_FORALL_IMP_THM, .. } := D.cn.cx.cvx.core5
  let { real_div, real_ge, real_pow, SUM_CLAUSES, .. } := D.cn.cx.cvx.core6
  let { REAL_HALF, .. } := D.cn.cx.cvx.misc
  let { dist, .. } := D.cn.cx.cvx.vec4
  let { CLOSED_INTER, CLOSED_SING, .. } := D.cn.cx.cvx.top1
  let { DISTANCE_ATTAINS_INF, .. } := D.cn.cx.cvx.top3
  let { REAL_INV_INV, .. } := D.cn.ms.ig.dv.qsession
  let { REAL_LT_TRANS, .. } := D.cn.ms.ig.dv.dg.qsession
  let { CONTINUOUS_CLOSED_PREIMAGE, .. } := D.cn.ms.ig.dv.dg.pt.qtop
  -- @@SCOPE END

  let log_def ← new_definition
   r"log y = @x. exp(x) = y"

  let EXP_LOG ← prove
   r"!x. &0 < x ==> exp(log x) = x"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [log_def] THEN CONV_TAC SELECT_CONV THEN
    SUBGOAL_THEN (← q r"?y. --inv(x) <= y /\ y <= x /\ Re(cexp(Cx y)) = x")
    MP_TAC THENL [ALL_TAC, MESON_TAC [CX_EXP, RE_CX]] THEN
    MATCH_MP_TAC IVT_INCREASING_RE THEN
    SIMP_TAC [← GSYM CX_EXP, RE_CX, CONTINUOUS_AT_CEXP] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC (← REAL_ARITH (← q r"&0 < x /\ &0 < y ==> --y <= x")) THEN
      ASM_SIMP_TAC [REAL_LT_INV_EQ],
      ONCE_REWRITE_TAC [← GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC [REAL_EXP_NEG, REAL_INV_INV, REAL_LT_INV_EQ],
      ALL_TAC] THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"&1 + x <= y ==> x <= y")) THEN
    ASM_SIMP_TAC [REAL_EXP_LE_X, REAL_LE_INV_EQ, REAL_LT_IMP_LE])

  let LOG_EXP ← prove
   r"!x. log(exp x) = x"
   (GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_EXP_INJ] THEN
    SIMP_TAC [EXP_LOG, REAL_EXP_POS_LT])

  let REAL_EXP_LOG ← prove
   r"!x. (exp(log x) = x) <=> &0 < x"
   (MESON_TAC [EXP_LOG, REAL_EXP_POS_LT])

  let LOG_MUL ← prove
   r"!x y. &0 < x /\ &0 < y ==> (log(x * y) = log(x) + log(y))"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_EXP_INJ] THEN
    ASM_SIMP_TAC [REAL_EXP_ADD, REAL_LT_MUL, EXP_LOG])

  let LOG_INJ ← prove
   r"!x y. &0 < x /\ &0 < y ==> (log(x) = log(y) <=> x = y)"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_EXP_INJ] THEN
    ASM_SIMP_TAC [EXP_LOG])

  let LOG_1 ← prove
   r"log(&1) = &0"
   (ONCE_REWRITE_TAC [← GSYM REAL_EXP_INJ] THEN
    REWRITE_TAC [REAL_EXP_0, REAL_EXP_LOG, REAL_LT_01])

  let LOG_INV ← prove
   r"!x. &0 < x ==> (log(inv x) = --(log x))"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_EXP_INJ] THEN
    ASM_SIMP_TAC [REAL_EXP_NEG, EXP_LOG, REAL_LT_INV_EQ])

  let LOG_DIV ← prove
   r"!x y. &0 < x /\ &0 < y ==> log(x / y) = log(x) - log(y)"
   (SIMP_TAC [real_div, real_sub, LOG_MUL, LOG_INV, REAL_LT_INV_EQ])

  let LOG_MONO_LT ← prove
   r"!x y. &0 < x /\ &0 < y ==> (log(x) < log(y) <=> x < y)"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_EXP_MONO_LT] THEN
    ASM_SIMP_TAC [EXP_LOG])

  let LOG_MONO_LT_IMP ← prove
   r"!x y. &0 < x /\ x < y ==> log(x) < log(y)"
   (MESON_TAC [LOG_MONO_LT, REAL_LT_TRANS])

  let LOG_MONO_LT_REV ← prove
   r"!x y. &0 < x /\ &0 < y /\ log x < log y ==> x < y"
   (MESON_TAC [LOG_MONO_LT])

  let LOG_MONO_LE ← prove
   r"!x y. &0 < x /\ &0 < y ==> (log(x) <= log(y) <=> x <= y)"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC [EXP_LOG])

  let LOG_MONO_LE_IMP ← prove
   r"!x y. &0 < x /\ x <= y ==> log(x) <= log(y)"
   (MESON_TAC [LOG_MONO_LE, REAL_LT_IMP_LE, REAL_LTE_TRANS])

  let LOG_MONO_LE_REV ← prove
   r"!x y. &0 < x /\ &0 < y /\ log x <= log y ==> x <= y"
   (MESON_TAC [LOG_MONO_LE])

  let LOG_POW ← prove
   r"!n x. &0 < x ==> (log(x pow n) = &n * log(x))"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_EXP_INJ] THEN
    ASM_SIMP_TAC [REAL_EXP_N, EXP_LOG, REAL_POW_LT])

  let LOG_LE_STRONG ← prove
   r"!x. &0 < &1 + x ==> log(&1 + x) <= x"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC [EXP_LOG, REAL_EXP_LE_X])

  let LOG_LE ← prove
   r"!x. &0 <= x ==> log(&1 + x) <= x"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC [EXP_LOG, ← REAL_ARITH (← q r"&0 <= x ==> &0 < &1 + x"), REAL_EXP_LE_X])

  let LOG_LT_X ← prove
   r"!x. &0 < x ==> log(x) < x"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_EXP_MONO_LT] THEN
    ASM_SIMP_TAC [EXP_LOG] THEN MP_TAC (← SPEC (← q r"x:real") REAL_EXP_LE_X) THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC)

  let LOG_POS ← prove
   r"!x. &1 <= x ==> &0 <= log(x)"
   (REWRITE_TAC [← GSYM LOG_1] THEN
    SIMP_TAC [LOG_MONO_LE, ← ARITH_RULE (← q r"&1 <= x ==> &0 < x"), REAL_LT_01])

  let LOG_POS_LT ← prove
   r"!x. &1 < x ==> &0 < log(x)"
   (REWRITE_TAC [← GSYM LOG_1] THEN
    SIMP_TAC [LOG_MONO_LT, ← ARITH_RULE (← q r"&1 < x ==> &0 < x"), REAL_LT_01])

  let LOG_PRODUCT ← prove
   r"!f:A->real s.
        FINITE s /\ (!x. x IN s ==> &0 < f x)
        ==> log(product s f) = sum s (\x. log(f x))"
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM, IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [PRODUCT_CLAUSES, SUM_CLAUSES, LOG_1, FORALL_IN_INSERT, LOG_MUL,
              PRODUCT_POS_LT])

  let SIN_NEARZERO ← prove
   r"?x. &0 < x /\ !y. &0 < y /\ y <= x ==> &0 < sin(y)"
   (MP_TAC (← SPEC (← q r"&1 / &2") (← CONJUNCT2
     (← REWRITE_RULE [has_complex_derivative, HAS_DERIVATIVE_AT_ALT]
      (← ISPEC (← q r"Cx(&0)") HAS_COMPLEX_DERIVATIVE_CSIN)))) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [CSIN_0, COMPLEX_SUB_RZERO, CCOS_0, COMPLEX_MUL_LZERO,
                 COMPLEX_MUL_LID] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"d / &2") THEN ASM_REWRITE_TAC [REAL_HALF] THEN
    X_GEN_TAC (← q r"y:real") THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"Cx y")) THEN
    ASM_REWRITE_TAC [← GSYM CX_SIN, COMPLEX_NORM_CX, ← GSYM CX_SUB] THEN
    ASM_REAL_ARITH_TAC)

  let SIN_NONTRIVIAL ← prove
   r"?x. &0 < x /\ ~(sin x = &0)"
   (MESON_TAC [REAL_LE_REFL, REAL_LT_REFL, SIN_NEARZERO])

  let COS_NONTRIVIAL ← prove
   r"?x. &0 < x /\ ~(cos x = &1)"
   (MP_TAC SIN_NONTRIVIAL THEN MATCH_MP_TAC MONO_EXISTS THEN
    MP_TAC SIN_CIRCLE THEN MATCH_MP_TAC MONO_FORALL THEN
    CONV_TAC REAL_FIELD)

  let COS_DOUBLE_BOUND ← prove
   r"!x. &0 <= cos x ==> &2 * (&1 - cos x) <= &1 - cos(&2 * x)"
   (REWRITE_TAC [COS_DOUBLE_COS] THEN REWRITE_TAC [← REAL_ARITH
     (← q r"&2 * (&1 - a) <= &1 - (&2 * b - &1) <=> b <= &1 * a")] THEN
    SIMP_TAC [REAL_POW_2, REAL_LE_RMUL, COS_BOUNDS])

  let COS_GOESNEGATIVE_LEMMA ← prove
   r"!x. cos(x) < &1 ==> ?n. cos(&2 pow n * x) < &0"
   (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC (← TAUT (← q r"(~p ==> p) ==> p")) THEN
    REWRITE_TAC [NOT_EXISTS_THM, REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"!n.  &2  pow n * (&1 - cos x) <= &1 - cos(&2 pow n * x)")
    ASSUME_TAC THENL
     [INDUCT_TAC THEN REWRITE_TAC [real_pow, REAL_MUL_LID, REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"&2 * (&1 - cos(&2 pow n * x))") THEN
      ASM_SIMP_TAC [← GSYM REAL_MUL_ASSOC, REAL_LE_LMUL, REAL_POS, COS_DOUBLE_BOUND],
      MP_TAC (← ISPEC (← q r"&1 / (&1 - cos(x))") REAL_ARCH_POW2) THEN
      ASM_SIMP_TAC [REAL_LT_LDIV_EQ, REAL_SUB_LT] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") MP_TAC) THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"n:num"))) THEN REAL_ARITH_TAC])

  let COS_GOESNEGATIVE ← prove
   r"?x. &0 < x /\ cos(x) < &0"
   (X_CHOOSE_TAC (← q r"x:real") COS_NONTRIVIAL THEN
    MP_TAC (← SPEC (← q r"x:real") COS_GOESNEGATIVE_LEMMA) THEN ANTS_TAC THENL
     [MP_TAC (← SPEC (← q r"x:real") COS_BOUNDS) THEN
      ASM_REAL_ARITH_TAC,
      ASM_MESON_TAC [REAL_LT_MUL, REAL_POW_LT, ← REAL_ARITH (← q r"&0 < &2")]])

  let COS_HASZERO ← prove
   r"?x. &0 < x /\ cos(x) = &0"
   (X_CHOOSE_THEN (← q r"z:real") STRIP_ASSUME_TAC COS_GOESNEGATIVE THEN
    SUBGOAL_THEN (← q r"?x. &0 <= x /\ x <= z /\ Re(ccos(Cx x)) = &0") MP_TAC THENL
     [MATCH_MP_TAC IVT_DECREASING_RE THEN
      ASM_SIMP_TAC [← GSYM CX_COS, RE_CX, REAL_LT_IMP_LE, COS_0, REAL_POS] THEN
      MESON_TAC [HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT,
                 HAS_COMPLEX_DERIVATIVE_CCOS],
      MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC [← GSYM CX_COS, RE_CX] THEN
      MESON_TAC [COS_0, REAL_LE_LT, ← REAL_ARITH (← q r"~(&1 = &0)")]])

  let SIN_HASZERO ← prove
   r"?x. &0 < x /\ sin(x) = &0"
   (X_CHOOSE_THEN (← q r"x:real") STRIP_ASSUME_TAC COS_HASZERO THEN
    EXISTS_TAC (← q r"&2 * x") THEN ASM_SIMP_TAC [SIN_DOUBLE] THEN
    ASM_REAL_ARITH_TAC)

  let SIN_HASZERO_MINIMAL ← prove
   r"?p. &0 < p /\ sin p = &0 /\ !x. &0 < x /\ x < p ==> ~(sin x = &0)"
   (X_CHOOSE_THEN (← q r"e:real") STRIP_ASSUME_TAC SIN_NEARZERO THEN
    MP_TAC (← ISPECL
      [← q r"{z | z IN IMAGE Cx {x | x >= e} /\ csin z IN {Cx(&0)}}", ← q r"Cx(&0)"]
      DISTANCE_ATTAINS_INF) THEN
    ANTS_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [IN_ELIM_THM, ← GSYM CONJ_ASSOC, IMP_CONJ] THEN
      REWRITE_TAC [FORALL_IN_IMAGE, EXISTS_IN_IMAGE] THEN
      REWRITE_TAC [IN_ELIM_THM, IN_SING, real_ge, ← GSYM CX_COS, CX_INJ] THEN
      REWRITE_TAC [dist, ← GSYM CX_SUB, ← GSYM CX_SIN, CX_INJ, COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
      REWRITE_TAC [← REAL_ARITH (← q r"abs(&0 - x) = abs x")] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [ALL_TAC,
        X_GEN_TAC (← q r"x:real") THEN
        REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real")))] THEN
      ASM_REAL_ARITH_TAC] THEN
    X_CHOOSE_TAC (← q r"a:real") SIN_HASZERO THEN CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC (← q r"Cx a") THEN
      ASM_REWRITE_TAC [IN_SING, IN_IMAGE, IN_ELIM_THM, ← GSYM CX_SIN] THEN
      ASM_MESON_TAC [← REAL_ARITH (← q r"x >= w \/ x <= w"), REAL_LT_REFL]] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
    REWRITE_TAC [CONTINUOUS_ON_CSIN, CLOSED_SING] THEN
    SUBGOAL_THEN
     (← q r"IMAGE Cx {x | x >= e} = {z | Im(z) = &0} INTER {z | Re(z) >= e}")
     (fun th => SIMP_TAC [th, CLOSED_INTER, CLOSED_HALFSPACE_IM_EQ,
                          CLOSED_HALFSPACE_RE_GE]) THEN
    REWRITE_TAC [EXTENSION, IN_IMAGE, IN_INTER, IN_ELIM_THM] THEN
    REWRITE_TAC [FORALL_COMPLEX, COMPLEX_EQ, RE, IM, RE_CX, IM_CX] THEN
    MESON_TAC [])

  let pi ← new_definition
   r"pi = @p. &0 < p /\ sin(p) = &0 /\ !x. &0 < x /\ x < p ==> ~(sin(x) = &0)"

  let PI_WORKS ← prove
   r"&0 < pi /\ sin(pi) = &0 /\ !x. &0 < x /\ x < pi ==> ~(sin x = &0)"
   (REWRITE_TAC [pi] THEN CONV_TAC SELECT_CONV THEN
    REWRITE_TAC [SIN_HASZERO_MINIMAL])

  pure { log_def, EXP_LOG, LOG_EXP, REAL_EXP_LOG, LOG_MUL, LOG_INJ, LOG_1, LOG_INV,
         LOG_DIV, LOG_MONO_LT, LOG_MONO_LT_IMP, LOG_MONO_LT_REV, LOG_MONO_LE,
         LOG_MONO_LE_IMP, LOG_MONO_LE_REV, LOG_POW, LOG_LE_STRONG, LOG_LE, LOG_LT_X,
         LOG_POS, LOG_POS_LT, LOG_PRODUCT, SIN_NEARZERO, SIN_NONTRIVIAL, COS_NONTRIVIAL,
         COS_DOUBLE_BOUND, COS_GOESNEGATIVE_LEMMA, COS_GOESNEGATIVE, COS_HASZERO,
         SIN_HASZERO, SIN_HASZERO_MINIMAL, pi, PI_WORKS }

/- ------------------------------------------------------------------------- -/
/- Now more relatively easy consequences.  (transcendentals.ml 1176-1454)   -/
/- ------------------------------------------------------------------------- -/

structure TSE where
  PI_POS : thm
  PI_POS_LE : thm
  PI_NZ : thm
  REAL_ABS_PI : thm
  SIN_PI : thm
  SIN_POS_PI : thm
  COS_PI2 : thm
  COS_PI : thm
  SIN_PI2 : thm
  SIN_COS : thm
  COS_SIN : thm
  SIN_PERIODIC_PI : thm
  COS_PERIODIC_PI : thm
  SIN_PERIODIC : thm
  COS_PERIODIC : thm
  SIN_NPI : thm
  COS_NPI : thm
  COS_POS_PI2 : thm
  SIN_POS_PI2 : thm
  COS_POS_PI : thm
  COS_POS_PI_LE : thm
  SIN_POS_PI_LE : thm
  SIN_PIMUL_EQ_0 : thm
  SIN_EQ_0 : thm
  COS_EQ_0 : thm
  SIN_ZERO_PI : thm
  COS_ZERO_PI : thm
  SIN_ZERO : thm
  COS_ZERO : thm
  COS_ONE_2PI : thm
  SIN_COS_SQRT : thm
  SIN_EQ_0_PI : thm
  COS_TREBLE_COS : thm
  COS_PI6 : thm
  SIN_PI6 : thm
  SIN_POS_PI_REV : thm
  SIN_PI3 : thm
  COS_PI3 : thm
  CEXP_II_PI : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupTSE [HolBase] (D : TranscendentalsDeps) (BTSB : TSB) (BTSC : TSC) (BTSD : TSD) : ExceptT String IO TSE := do
  -- @@SCOPE BEGIN
  let { REAL_EXP_0, .. } := BTSB
  let { CONTINUOUS_AT_CCOS, CONTINUOUS_AT_CSIN, COS_0, COS_ABS, COS_ADD, COS_DOUBLE_COS,
        COS_NEG, COS_SUB, CX_COS, CX_SIN, EULER, IVT_DECREASING_RE, SIN_0, SIN_ADD,
        SIN_CIRCLE, SIN_DOUBLE, SIN_NEG, SIN_SUB, .. } := BTSC
  let { PI_WORKS, SIN_NEARZERO, .. } := BTSD
  let { NOT_EVEN, REAL_MUL_2, .. } := D.qsession
  let { INTEGER_CASES, INTEGER_NEG, .. } := D.qfloor
  let { SIMPLE_COMPLEX_ARITH_TAC, .. } := D.cn.cxa
  let { CX_NEG, IM_CX, IM_MUL_II, RE_CX, RE_MUL_II, .. } := D.cn.cxc
  let { FLOOR_FRAC, REAL_ABS_INTEGER_LEMMA, .. } := D.cn.ms.qfloor
  let { REAL_LET_ANTISYM, .. } := D.cn.ms.qsession
  let { ARITH_RULE, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INDUCT_TAC, MESON_TAC, REAL_ARITH,
        REAL_ARITH_TAC, REAL_FIELD, REAL_RAT_REDUCE_CONV, REAL_RING, .. } := D.cn.cx.cvx
  let { REAL_LT_RMUL_EQ, .. } := D.cn.cx.cpx
  let { FLOOR, .. } := D.cn.ms.ig.qfloor
  let { ARITH, CONJ_ASSOC, CONJ_SYM, EXISTS_OR_THM, .. } := D.cn.cx.cvx.core1
  let { LEFT_AND_EXISTS_THM, MONO_EXISTS, NOT_IMP, OR_EXISTS_THM, POW_2_SQRT,
        REAL_ADD_ASSOC, REAL_ADD_LID, REAL_ADD_RDISTRIB, REAL_ADD_RID, REAL_DIV_REFL,
        REAL_DIV_RMUL, .. } := D.cn.cx.cvx.core3
  let { REAL_ENTIRE, REAL_EQ_LDIV_EQ, REAL_EQ_SUB_LADD, REAL_LE_LT, REAL_LE_MUL,
        REAL_LE_TOTAL, REAL_LET_TRANS, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_LDIV_EQ,
        REAL_LT_RDIV_EQ, REAL_LT_REFL, REAL_LTE_TRANS, .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LNEG, REAL_MUL_LZERO, REAL_MUL_RZERO,
        REAL_NEG_0, REAL_NEG_NEG, REAL_NOT_LE, REAL_OF_NUM_ADD, REAL_OF_NUM_EQ,
        REAL_OF_NUM_MUL, REAL_OF_NUM_SUB, REAL_OF_NUM_SUC, REAL_POS, REAL_POW_2,
        REAL_POW_DIV, REAL_POW_EQ_0, REAL_POW_ONE, RIGHT_OR_DISTRIB, SQRT_POW_2,
        .. } := D.cn.cx.cvx.core5
  let { real_abs, real_pow, SWAP_EXISTS_THM, UNWIND_THM1, UNWIND_THM2,
        .. } := D.cn.cx.cvx.core6
  let { REAL_HALF, .. } := D.cn.cx.cvx.misc
  let { EVEN_EXISTS, EVEN_MULT, ODD_EXISTS, REAL_POW_NEG, SQRT_UNIQUE,
        .. } := D.cn.ms.ig.dv.dg.qsession
  -- @@SCOPE END

  let PI_POS ← prove
   r"&0 < pi"
   (REWRITE_TAC [PI_WORKS])

  let PI_POS_LE ← prove
   r"&0 <= pi"
   (REWRITE_TAC [REAL_LE_LT, PI_POS])

  let PI_NZ ← prove
   r"~(pi = &0)"
   (SIMP_TAC [PI_POS, REAL_LT_IMP_NZ])

  let REAL_ABS_PI ← prove
   r"abs pi = pi"
   (REWRITE_TAC [real_abs, PI_POS_LE])

  let SIN_PI ← prove
   r"sin(pi) = &0"
   (REWRITE_TAC [PI_WORKS])

  let SIN_POS_PI ← prove
   r"!x. &0 < x /\ x < pi ==> &0 < sin(x)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    X_CHOOSE_THEN (← q r"e:real") STRIP_ASSUME_TAC SIN_NEARZERO THEN
    MP_TAC (← ISPECL [← q r"csin", ← q r"e:real", ← q r"x:real", ← q r"&0"]
      IVT_DECREASING_RE) THEN
    ASM_SIMP_TAC [NOT_IMP, CONTINUOUS_AT_CSIN, ← GSYM CX_SIN, RE_CX, SIN_0] THEN
    ASM_MESON_TAC [REAL_LE_TOTAL, REAL_LET_ANTISYM, PI_WORKS, REAL_LET_TRANS,
                   REAL_LTE_TRANS])

  let COS_PI2 ← prove
   r"cos(pi / &2) = &0"
   (MP_TAC (← SYM (← SPEC (← q r"pi / &2") SIN_DOUBLE)) THEN
    REWRITE_TAC [REAL_HALF, SIN_PI, REAL_ENTIRE, REAL_OF_NUM_EQ, ARITH] THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"&0 < y ==> y = &0 \/ z = &0 ==> z = &0")) THEN
    MATCH_MP_TAC SIN_POS_PI THEN MP_TAC PI_POS THEN REAL_ARITH_TAC)

  let COS_PI ← prove
   r"cos(pi) = -- &1"
   (ONCE_REWRITE_TAC [← REAL_ARITH (← q r"pi = &2 * pi / &2")] THEN
    REWRITE_TAC [COS_DOUBLE_COS, COS_PI2] THEN REAL_ARITH_TAC)

  let SIN_PI2 ← prove
   r"sin(pi / &2) = &1"
   (MP_TAC (← SPEC (← q r"pi / &2") SIN_CIRCLE) THEN
    REWRITE_TAC [COS_PI2, REAL_POW_2, REAL_ADD_RID, REAL_MUL_LZERO] THEN
    REWRITE_TAC [← REAL_RING (← q r"x * x = &1 <=> x = &1 \/ x = -- &1")] THEN
    MP_TAC (← SPEC (← q r"pi / &2") SIN_POS_PI) THEN MP_TAC PI_POS THEN REAL_ARITH_TAC)

  let SIN_COS ← prove
   r"!x. sin(x) = cos(pi / &2 - x)"
   (REWRITE_TAC [COS_SUB, COS_PI2, SIN_PI2] THEN REAL_ARITH_TAC)

  let COS_SIN ← prove
   r"!x. cos(x) = sin(pi / &2 - x)"
   (REWRITE_TAC [SIN_SUB, COS_PI2, SIN_PI2] THEN REAL_ARITH_TAC)

  let SIN_PERIODIC_PI ← prove
   r"!x. sin(x + pi) = --(sin(x))"
   (REWRITE_TAC [SIN_ADD, SIN_PI, COS_PI] THEN REAL_ARITH_TAC)

  let COS_PERIODIC_PI ← prove
   r"!x. cos(x + pi) = --(cos(x))"
   (REWRITE_TAC [COS_ADD, SIN_PI, COS_PI] THEN REAL_ARITH_TAC)

  let SIN_PERIODIC ← prove
   r"!x. sin(x + &2 * pi) = sin(x)"
   (REWRITE_TAC [REAL_MUL_2, REAL_ADD_ASSOC, SIN_PERIODIC_PI, REAL_NEG_NEG])

  let COS_PERIODIC ← prove
   r"!x. cos(x + &2 * pi) = cos(x)"
   (REWRITE_TAC [REAL_MUL_2, REAL_ADD_ASSOC, COS_PERIODIC_PI, REAL_NEG_NEG])

  let SIN_NPI ← prove
   r"!n. sin(&n * pi) = &0"
   (INDUCT_TAC THEN
    ASM_REWRITE_TAC [← GSYM REAL_OF_NUM_SUC, REAL_MUL_LID, REAL_ADD_RDISTRIB,
                     REAL_NEG_0, SIN_PERIODIC_PI, REAL_MUL_LZERO, SIN_0])

  let COS_NPI ← prove
   r"!n. cos(&n * pi) = --(&1) pow n"
   (INDUCT_TAC THEN
    ASM_REWRITE_TAC [real_pow, REAL_MUL_LZERO, COS_0, COS_PERIODIC_PI,
      REAL_MUL_LID, REAL_MUL_LNEG, ← GSYM REAL_OF_NUM_SUC, REAL_ADD_RDISTRIB])

  let COS_POS_PI2 ← prove
   r"!x. &0 < x /\ x < pi / &2 ==> &0 < cos(x)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"ccos", ← q r"&0", ← q r"x:real", ← q r"&0"]
      IVT_DECREASING_RE) THEN
    ASM_SIMP_TAC [CONTINUOUS_AT_CCOS, REAL_LT_IMP_LE, ← GSYM CX_COS, RE_CX] THEN
    REWRITE_TAC [COS_0, REAL_POS] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"y:real")) THEN
    MP_TAC (← SPEC (← q r"y:real") SIN_DOUBLE) THEN ASM_REWRITE_TAC [REAL_MUL_RZERO] THEN
    MATCH_MP_TAC (← liftExcept (last (CONJUNCTS PI_WORKS))) THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    ASM_CASES_TAC (← q r"y = &0") THEN ASM_REWRITE_TAC [COS_0] THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC)

  let SIN_POS_PI2 ← prove
   r"!x. &0 < x /\ x < pi / &2 ==> &0 < sin(x)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SIN_POS_PI THEN
    ASM_REAL_ARITH_TAC)

  let COS_POS_PI ← prove
   r"!x. --(pi / &2) < x /\ x < pi / &2 ==> &0 < cos(x)"
   (GEN_TAC THEN MP_TAC (← SPEC (← q r"abs x") COS_POS_PI2) THEN
    REWRITE_TAC [COS_ABS] THEN
    ASM_CASES_TAC (← q r"x = &0") THEN ASM_REWRITE_TAC [COS_0] THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC)

  let COS_POS_PI_LE ← prove
   r"!x. --(pi / &2) <= x /\ x <= pi / &2 ==> &0 <= cos(x)"
   (REWRITE_TAC [REAL_LE_LT] THEN MESON_TAC [COS_PI2, COS_NEG, COS_POS_PI])

  let SIN_POS_PI_LE ← prove
   r"!x. &0 <= x /\ x <= pi ==> &0 <= sin(x)"
   (REWRITE_TAC [REAL_LE_LT] THEN MESON_TAC [SIN_0, SIN_PI, SIN_POS_PI])

  let SIN_PIMUL_EQ_0 ← prove
   r"!n. sin(n * pi) = &0 <=> integer(n)"
   (SUBGOAL_THEN (← q r"!n. integer n ==> sin(n * pi) = &0 /\ ~(cos(n * pi) = &0)")
    ASSUME_TAC THENL
     [REWRITE_TAC [INTEGER_CASES] THEN GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
      ASM_SIMP_TAC [REAL_MUL_LNEG, COS_NPI, SIN_NPI,
                    SIN_NEG, COS_NEG, REAL_POW_EQ_0] THEN REAL_ARITH_TAC,
      ALL_TAC] THEN
    GEN_TAC THEN EQ_TAC THEN ASM_SIMP_TAC [] THEN
    SUBST1_TAC (← liftExcept (last (CONJUNCTS (← SPEC (← q r"n:real") FLOOR_FRAC)))) THEN
    ASM_SIMP_TAC [REAL_ADD_RDISTRIB, FLOOR, SIN_ADD, REAL_MUL_LZERO] THEN
    ASM_SIMP_TAC [REAL_ADD_LID, REAL_ENTIRE, FLOOR] THEN
    DISCH_TAC THEN MP_TAC (← SPEC (← q r"frac n * pi") SIN_POS_PI) THEN
    ASM_SIMP_TAC [REAL_LT_REFL, ← GSYM REAL_LT_RDIV_EQ, ← GSYM REAL_LT_LDIV_EQ,
                  PI_POS, REAL_DIV_REFL, REAL_LT_IMP_NZ] THEN
    MP_TAC (← SPEC (← q r"n:real") FLOOR_FRAC) THEN ASM_CASES_TAC (← q r"frac n = &0") THEN
    ASM_REWRITE_TAC [FLOOR, REAL_ADD_RID] THEN
    ASM_REAL_ARITH_TAC)

  let SIN_EQ_0 ← prove
   r"!x. sin(x) = &0 <=> ?n. integer n /\ x = n * pi"
   (GEN_TAC THEN MP_TAC (← SPEC (← q r"x / pi") SIN_PIMUL_EQ_0) THEN
    SIMP_TAC [REAL_DIV_RMUL, REAL_LT_IMP_NZ, ← GSYM REAL_EQ_LDIV_EQ, PI_POS] THEN
    ONCE_REWRITE_TAC [CONJ_SYM] THEN REWRITE_TAC [UNWIND_THM1])

  let COS_EQ_0 ← prove
   r"!x. cos(x) = &0 <=> ?n. integer n /\ x = (n + &1 / &2) * pi"
   (GEN_TAC THEN REWRITE_TAC [COS_SIN, SIN_EQ_0] THEN
    EQ_TAC THEN DISCH_THEN (X_CHOOSE_THEN (← q r"n:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"--n:real") THEN ASM_REWRITE_TAC [INTEGER_NEG] THEN
    ASM_REAL_ARITH_TAC)

  let SIN_ZERO_PI ← prove
   r"!x. sin(x) = &0 <=> (?n. x = &n * pi) \/ (?n. x = --(&n * pi))"
   (REWRITE_TAC [SIN_EQ_0, INTEGER_CASES] THEN MESON_TAC [REAL_MUL_LNEG])

  let COS_ZERO_PI ← prove
   r"!x. cos(x) = &0 <=>
       (?n. x = (&n + &1 / &2) * pi) \/ (?n. x = --((&n + &1 / &2) * pi))"
   (GEN_TAC THEN REWRITE_TAC [COS_EQ_0, INTEGER_CASES, RIGHT_OR_DISTRIB] THEN
    REWRITE_TAC [EXISTS_OR_THM, LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN SIMP_TAC [UNWIND_THM2] THEN EQ_TAC THEN
    DISCH_THEN (DISJ_CASES_THEN (X_CHOOSE_THEN (← q r"n:num") SUBST1_TAC)) THENL
     [DISJ1_TAC THEN EXISTS_TAC (← q r"n:num"),
      ASM_CASES_TAC (← q r"n = 0") THENL
       [DISJ1_TAC THEN EXISTS_TAC (← q r"0"),
        DISJ2_TAC THEN EXISTS_TAC (← q r"n - 1")],
      DISJ1_TAC THEN EXISTS_TAC (← q r"n:num"),
      DISJ2_TAC THEN EXISTS_TAC (← q r"n + 1")] THEN
    ASM_SIMP_TAC [← GSYM REAL_OF_NUM_SUB, ← GSYM REAL_OF_NUM_ADD,
                  ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")] THEN
    REAL_ARITH_TAC)

  let SIN_ZERO ← prove
   r"!x. (sin(x) = &0) <=> (?n. EVEN n /\ x = &n * (pi / &2)) \/
                         (?n. EVEN n /\ x = --(&n * (pi / &2)))"
   (REWRITE_TAC [SIN_ZERO_PI, EVEN_EXISTS, LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN REWRITE_TAC [UNWIND_THM2] THEN
    SIMP_TAC [← GSYM REAL_OF_NUM_MUL, ← REAL_ARITH (← q r"(&2 * x) * y / &2 = x * y")])

  let COS_ZERO ← prove
   r"!x. cos(x) = &0 <=> (?n. ~EVEN n /\ (x = &n * (pi / &2))) \/
                       (?n. ~EVEN n /\ (x = --(&n * (pi / &2))))"
   (REWRITE_TAC [COS_ZERO_PI, NOT_EVEN, ODD_EXISTS, LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN REWRITE_TAC [UNWIND_THM2] THEN
    SIMP_TAC [← GSYM REAL_OF_NUM_MUL, ← GSYM REAL_OF_NUM_SUC,
              ← REAL_ARITH (← q r"(&2 * x + &1) * y / &2 = (x + &1 / &2) * y")])

  let COS_ONE_2PI ← prove
   r"!x. (cos(x) = &1) <=> (?n. x = &n * &2 * pi) \/ (?n. x = --(&n * &2 * pi))"
   (GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [FIRST_ASSUM (MP_TAC o SPEC (← q r"sin(x)") o MATCH_MP (← REAL_RING
       (← q r"c = &1 ==> !s. s pow 2 + c pow 2 = &1 ==> s = &0"))) THEN
      REWRITE_TAC [SIN_ZERO_PI, SIN_CIRCLE] THEN
      DISCH_THEN (DISJ_CASES_THEN (X_CHOOSE_THEN (← q r"n:num") SUBST_ALL_TAC)) THEN
      POP_ASSUM MP_TAC THEN REWRITE_TAC [COS_NEG, COS_NPI, REAL_POW_NEG] THEN
      COND_CASES_TAC THEN REWRITE_TAC [REAL_POW_ONE] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [EVEN_EXISTS]) THEN
      REWRITE_TAC [OR_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      SIMP_TAC [← GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC,
      FIRST_X_ASSUM (DISJ_CASES_THEN CHOOSE_TAC) THEN
      ASM_REWRITE_TAC [COS_NEG, REAL_MUL_ASSOC, REAL_OF_NUM_MUL, COS_NPI,
                       REAL_POW_NEG, EVEN_MULT, ARITH, REAL_POW_ONE]])

  let SIN_COS_SQRT ← prove
   r"!x. &0 <= sin(x) ==> (sin(x) = sqrt(&1 - (cos(x) pow 2)))"
   (REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE THEN
    ASM_REWRITE_TAC [SIN_CIRCLE, REAL_EQ_SUB_LADD])

  let SIN_EQ_0_PI ← prove
   r"!x. --pi < x /\ x < pi /\ sin(x) = &0 ==> x = &0"
   (GEN_TAC THEN REWRITE_TAC [SIN_EQ_0, CONJ_ASSOC] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC
     (X_CHOOSE_THEN (← q r"n:real") STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC [← REAL_ARITH
     (← q r"--p < n * p /\ n * p < p <=> -- &1 * p < n * p /\ n * p < &1 * p")] THEN
    SIMP_TAC [REAL_ENTIRE, REAL_LT_IMP_NZ, REAL_LT_RMUL_EQ, PI_POS] THEN
    MP_TAC (← SPEC (← q r"n:real") REAL_ABS_INTEGER_LEMMA) THEN
    ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC)

  let COS_TREBLE_COS ← prove
   r"!x. cos(&3 * x) = &4 * cos(x) pow 3 - &3 * cos x"
   (GEN_TAC THEN REWRITE_TAC [COS_ADD, ← REAL_ARITH (← q r"&3 * x = &2 * x + x")] THEN
    REWRITE_TAC [SIN_DOUBLE, COS_DOUBLE_COS] THEN
    MP_TAC (← SPEC (← q r"x:real") SIN_CIRCLE) THEN CONV_TAC (fun t => REAL_RING t))

  let COS_PI6 ← prove
   r"cos(pi / &6) = sqrt(&3) / &2"
   (MP_TAC (← ISPEC (← q r"pi / &6") COS_TREBLE_COS) THEN
    REWRITE_TAC [← REAL_ARITH (← q r"&3 * x / &6 = x / &2"), COS_PI2] THEN
    REWRITE_TAC [← REAL_RING (← q r"&0 = &4 * c pow 3 - &3 * c <=>
                           c = &0 \/ (&2 * c) pow 2 = &3")] THEN
    SUBGOAL_THEN (← q r"&0 < cos(pi / &6)") ASSUME_TAC THENL
     [MATCH_MP_TAC COS_POS_PI THEN MP_TAC PI_POS THEN REAL_ARITH_TAC,
      DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
       [ASM_MESON_TAC [REAL_LT_REFL], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o AP_TERM (← q r"sqrt")) THEN
      ASM_SIMP_TAC [POW_2_SQRT, REAL_LE_MUL, REAL_LT_IMP_LE, REAL_POS] THEN
      REAL_ARITH_TAC])

  let SIN_PI6 ← prove
   r"sin(pi / &6) = &1 / &2"
   (MP_TAC (← SPEC (← q r"pi / &6") SIN_CIRCLE) THEN REWRITE_TAC [COS_PI6] THEN
    SIMP_TAC [REAL_POW_DIV, SQRT_POW_2, REAL_POS] THEN MATCH_MP_TAC (← REAL_FIELD
     (← q r"~(s + &1 / &2 = &0) ==> s pow 2 + &3 / &2 pow 2 = &1 ==> s = &1 / &2")) THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"&0 < x ==> ~(x + &1 / &2 = &0)")) THEN
    MATCH_MP_TAC SIN_POS_PI THEN MP_TAC PI_POS THEN REAL_ARITH_TAC)

  let SIN_POS_PI_REV ← prove
   r"!x. &0 <= x /\ x <= &2 * pi /\ &0 < sin x ==> &0 < x /\ x < pi"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"x = &0") THEN
    ASM_REWRITE_TAC [SIN_0, REAL_LT_REFL] THEN
    ASM_CASES_TAC (← q r"x = pi") THEN
    ASM_REWRITE_TAC [SIN_PI, REAL_LT_REFL] THEN
    ASM_CASES_TAC (← q r"x = &2 * pi") THEN
    ASM_REWRITE_TAC [SIN_NPI, REAL_LT_REFL] THEN
    REPEAT STRIP_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [← GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"&0 < sin(&2 * pi - x)") MP_TAC THENL
     [MATCH_MP_TAC SIN_POS_PI THEN ASM_REAL_ARITH_TAC,
      REWRITE_TAC [SIN_SUB, SIN_NPI, COS_NPI] THEN ASM_REAL_ARITH_TAC])

  let SIN_PI3 ← prove
   r"sin(pi / &3) = sqrt(&3) / &2"
   (REWRITE_TAC [SIN_DOUBLE, COS_PI6, SIN_PI6,
                 ← REAL_ARITH (← q r"x / &3 = &2 * x / &6")] THEN
    REAL_ARITH_TAC)

  let COS_PI3 ← prove
   r"cos(pi / &3) = &1 / &2"
   (REWRITE_TAC [COS_DOUBLE_COS, COS_PI6, ← REAL_ARITH (← q r"x / &3 = &2 * x / &6")] THEN
    SIMP_TAC [REAL_POW_DIV, SQRT_POW_2, REAL_POS, ← REAL_ARITH
     (← q r"&2 * s / &2 pow 2 - &1 = &1 / &2 <=> s = &3")])

  let CEXP_II_PI ← prove
   r"cexp(ii * Cx pi) = --Cx(&1)"
   (REWRITE_TAC [EULER, RE_MUL_II, IM_MUL_II, RE_CX, IM_CX] THEN
    REWRITE_TAC [REAL_NEG_0, SIN_PI, COS_PI, REAL_EXP_0] THEN
    REWRITE_TAC [CX_NEG] THEN SIMPLE_COMPLEX_ARITH_TAC)

  pure { PI_POS, PI_POS_LE, PI_NZ, REAL_ABS_PI, SIN_PI, SIN_POS_PI, COS_PI2, COS_PI,
         SIN_PI2, SIN_COS, COS_SIN, SIN_PERIODIC_PI, COS_PERIODIC_PI, SIN_PERIODIC,
         COS_PERIODIC, SIN_NPI, COS_NPI, COS_POS_PI2, SIN_POS_PI2, COS_POS_PI,
         COS_POS_PI_LE, SIN_POS_PI_LE, SIN_PIMUL_EQ_0, SIN_EQ_0, COS_EQ_0, SIN_ZERO_PI,
         COS_ZERO_PI, SIN_ZERO, COS_ZERO, COS_ONE_2PI, SIN_COS_SQRT, SIN_EQ_0_PI,
         COS_TREBLE_COS, COS_PI6, SIN_PI6, SIN_POS_PI_REV, SIN_PI3, COS_PI3, CEXP_II_PI }
/- ------------------------------------------------------------------------- -/
/- Prove totality of trigs; polar representation.                           -/
/- (transcendentals.ml 1455-1912)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSF where
  SIN_TOTAL_POS : thm
  SINCOS_TOTAL_PI2 : thm
  SINCOS_TOTAL_PI : thm
  SINCOS_TOTAL_2PI : thm
  CIRCLE_SINCOS : thm
  CX_PI_NZ : thm
  COMPLEX_UNIMODULAR_POLAR : thm
  SIN_INTEGER_2PI : thm
  SIN_INTEGER_PI : thm
  COS_INTEGER_2PI : thm
  SINCOS_PRINCIPAL_VALUE : thm
  CEXP_COMPLEX : thm
  NORM_COSSIN : thm
  NORM_CEXP : thm
  NORM_CEXP_II : thm
  NORM_CEXP_IMAGINARY : thm
  CEXP_EQ_1 : thm
  CEXP_EQ : thm
  COMPLEX_EQ_CEXP : thm
  CEXP_INTEGER_2PI : thm
  CEXP_LIPSCHITZ_BOUNDED : thm
  SIN_COS_EQ : thm
  SIN_COS_INJ : thm
  CEXP_II_NE_1 : thm
  CSIN_EQ_0 : thm
  CCOS_EQ_0 : thm
  CCOS_EQ_1 : thm
  CSIN_EQ_1 : thm
  CSIN_EQ_MINUS1 : thm
  CCOS_EQ_MINUS1 : thm
  COS_EQ_1 : thm
  SIN_EQ_1 : thm
  SIN_EQ_MINUS1 : thm
  COS_EQ_MINUS1 : thm
  DIST_CEXP_II_1 : thm
  CX_SINH : thm
  CX_COSH : thm
  NORM_CCOS_POW_2 : thm
  NORM_CSIN_POW_2 : thm
  CSIN_EQ : thm
  CCOS_EQ : thm
  SIN_EQ : thm
  COS_EQ : thm
  NORM_CCOS_LE : thm
  NORM_CCOS_PLUS1_LE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSF [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) (BTSB : TSB) (BTSC : TSC) (BTSE : TSE) : ExceptT String IO TSF := do
  -- @@SCOPE BEGIN
  let { CEXP_ADD, CEXP_N, CEXP_NEG, CEXP_NZ, CEXP_SUB, HAS_COMPLEX_DERIVATIVE_CEXP,
        .. } := BTSA
  let { ccos, CCOS_ADD, CCOS_DOUBLE_CSIN, CCOS_SUB, CEXP_EULER, COMPLEX_SUB_CCOS,
        COMPLEX_SUB_CSIN, csin, CSIN_ADD, CSIN_NEG, CSIN_SUB, CX_EXP, REAL_ABS_EXP,
        REAL_EXP_0, REAL_EXP_EQ_1, REAL_EXP_MONO_LE, REAL_EXP_N, REAL_EXP_NEG, REAL_EXP_NZ,
        REAL_EXP_POS_LT, .. } := BTSB
  let { CONTINUOUS_AT_CSIN, COS_0, COS_ABS, COS_ADD, COS_DOUBLE, COS_DOUBLE_SIN, COS_NEG,
        COS_SUB, CX_COS, CX_SIN, IVT_INCREASING_RE, SIN_0, SIN_ADD, SIN_CIRCLE, SIN_NEG,
        SIN_SUB, .. } := BTSC
  let { COS_NPI, COS_PI, COS_PI2, COS_POS_PI_LE, PI_POS, REAL_ABS_PI, SIN_EQ_0, SIN_NPI,
        SIN_PI, SIN_PI2, .. } := BTSE
  let { HAS_COMPLEX_DERIVATIVE_AT_WITHIN, .. } := D.kne
  let { COMPLEX_DIFFERENTIABLE_BOUND, .. } := D.knj
  let { REAL_POW_LT2, .. } := D.qsession
  let { FRAC_FLOOR, INTEGER_ABS, INTEGER_CASES, .. } := D.qfloor
  let { COMPLEX_EQ, complex_norm, COMPLEX_SQNORM, FORALL_COMPLEX, IM, RE,
        SIMPLE_COMPLEX_ARITH_TAC, .. } := D.cn.cxa
  let { COMPLEX_EQ_SUB_RADD, COMPLEX_MUL_LID, COMPLEX_MUL_LNEG, COMPLEX_SUB_0,
        COMPLEX_SUB_LZERO, .. } := D.cn.cxb
  let { COMPLEX_ENTIRE, COMPLEX_EXPAND, COMPLEX_NORM_CX, COMPLEX_TRAD, CX_ADD, CX_DIV,
        CX_INJ, CX_INV, CX_MUL, CX_NEG, CX_SUB, IM_ADD, IM_CX, IM_DIV_CX, IM_MUL_CX,
        IM_MUL_II, IM_NEG, IM_SUB, RE_ADD, RE_CX, RE_DIV_CX, RE_MUL_CX, RE_MUL_II, RE_NEG,
        RE_SUB, .. } := D.cn.cxc
  let { COMPLEX_RING, .. } := D.cn.cxd
  let { COMPLEX_FIELD, .. } := D.cn.cxe
  let { COMPLEX_NORM_DIV, COMPLEX_NORM_MUL, .. } := D.cn.cxf
  let { COMPLEX_NORM_GE_RE_IM, .. } := D.cn.cxg
  let { REAL_EQ_SUB_RADD, .. } := D.cn.qsession
  let { FLOOR_FRAC, REAL_ABS_INTEGER_LEMMA, .. } := D.cn.ms.qfloor
  let { integer, .. } := D.cn.ms.qsession
  let { ASM_REAL_ARITH_TAC, MESON_TAC, NORM_ARITH, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD,
        REAL_RAT_REDUCE_CONV, REAL_RING, .. } := D.cn.cx.cvx
  let { REAL_LE_SQUARE, REAL_LT_RMUL_EQ, .. } := D.cn.cx.cpx
  let { INTEGER_CLOSED, .. } := D.cn.ms.ig.qfloor
  let { ARITH, ARITH_EQ, CONTRAPOS_THM, .. } := D.cn.cx.cvx.core1
  let { FUN_EQ_THM, .. } := D.cn.cx.cvx.core2
  let { MONO_EXISTS, MONO_FORALL, OR_EXISTS_THM, REAL_ABS_DIV, REAL_ABS_MUL, REAL_ABS_NUM,
        REAL_ADD_LID, REAL_ADD_RDISTRIB, REAL_ADD_RID, REAL_ADD_SYM, REAL_DIV_LMUL,
        .. } := D.cn.cx.cvx.core3
  let { REAL_ENTIRE, REAL_LE_ADD, REAL_LE_LMUL_EQ, REAL_LT_IMP_LE, REAL_LT_IMP_NZ,
        REAL_LT_LMUL_EQ, REAL_LT_MUL, REAL_LT_MUL_EQ, REAL_LT_REFL,
        .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LNEG, REAL_MUL_LZERO, REAL_MUL_RID,
        REAL_MUL_RNEG, REAL_MUL_RZERO, REAL_NEG_0, REAL_OF_NUM_EQ, REAL_OF_NUM_LT,
        REAL_OF_NUM_MUL, REAL_POS, REAL_POW2_ABS, REAL_POW_2, REAL_POW_MUL, REAL_POW_ONE,
        REAL_SUB_0, REAL_SUB_LDISTRIB, RIGHT_AND_EXISTS_THM, SQRT_1, SQRT_POW_2,
        .. } := D.cn.cx.cvx.core5
  let { real_abs, .. } := D.cn.cx.cvx.core6
  let { NORM_EQ_SQUARE, .. } := D.cn.cx.cvx.vec2
  let { NORM_NEG, NORM_POW_2, .. } := D.cn.cx.cvx.vec3
  let { dist, .. } := D.cn.cx.cvx.vec4
  let { IN_CBALL, .. } := D.cn.cx.cvx.top4
  let { EVEN_EXISTS, EVEN_MULT, REAL_POW_NEG, .. } := D.cn.ms.ig.dv.dg.qsession
  let { CONVEX_CBALL, .. } := D.cn.ms.ig.dv.dg.pt.qcvx2
  -- @@SCOPE END

  let SIN_TOTAL_POS ← prove
   r"!y. &0 <= y /\ y <= &1
       ==> ?x. &0 <= x /\ x <= pi / &2 /\ sin(x) = y"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"csin", ← q r"&0", ← q r"pi / &2", ← q r"y:real"]
      IVT_INCREASING_RE) THEN
    ASM_REWRITE_TAC [← GSYM CX_SIN, RE_CX, SIN_0, SIN_PI2] THEN
    SIMP_TAC [CONTINUOUS_AT_CSIN, PI_POS, ← REAL_ARITH (← q r"&0 < x ==> &0 <= x / &2")])

  let SINCOS_TOTAL_PI2 ← prove
   r"!x y. &0 <= x /\ &0 <= y /\ x pow 2 + y pow 2 = &1
         ==> ?t. &0 <= t /\ t <= pi / &2 /\ x = cos t /\ y = sin t"
   (REPEAT STRIP_TAC THEN MP_TAC (← SPEC (← q r"y:real") SIN_TOTAL_POS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← REAL_ARITH
       (← q r"x pow 2 + y pow 2 = &1
        ==> (&1 < y ==> &1 pow 2 < y pow 2) /\ &0 <= x * x
            ==> y <= &1"))) THEN
      SIMP_TAC [REAL_LE_SQUARE, REAL_POW_LT2, REAL_POS, ARITH],
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:real") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"x = cos t \/ x = --(cos t)") MP_TAC THENL
       [MP_TAC (← SPEC (← q r"t:real") SIN_CIRCLE),
        MP_TAC (← SPEC (← q r"t:real") COS_POS_PI_LE)] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD])

  let SINCOS_TOTAL_PI ← prove
   r"!x y. &0 <= y /\ x pow 2 + y pow 2 = &1
         ==> ?t. &0 <= t /\ t <= pi /\ x = cos t /\ y = sin t"
   (REPEAT STRIP_TAC THEN DISJ_CASES_TAC (← REAL_ARITH (← q r"&0 <= x \/ &0 <= --x")) THENL
     [MP_TAC (← SPECL [← q r"x:real", ← q r"y:real"] SINCOS_TOTAL_PI2),
      MP_TAC (← SPECL [← q r"--x:real", ← q r"y:real"] SINCOS_TOTAL_PI2)] THEN
    ASM_REWRITE_TAC [REAL_POW_NEG, ARITH] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:real") STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC (← q r"t:real"), EXISTS_TAC (← q r"pi - t")] THEN
    ASM_REWRITE_TAC [SIN_SUB, COS_SUB, SIN_PI, COS_PI] THEN
    ASM_REAL_ARITH_TAC)

  let SINCOS_TOTAL_2PI ← prove
   r"!x y. x pow 2 + y pow 2 = &1
         ==> ?t. &0 <= t /\ t < &2 * pi /\ x = cos t /\ y = sin t"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"x = &1 /\ y = &0") THENL
     [EXISTS_TAC (← q r"&0") THEN ASM_REWRITE_TAC [SIN_0, COS_0] THEN
      MP_TAC PI_POS THEN REAL_ARITH_TAC,
      ALL_TAC] THEN
    DISJ_CASES_TAC (← REAL_ARITH (← q r"&0 <= y \/ &0 <= --y")) THENL
     [MP_TAC (← SPECL [← q r"x:real", ← q r"y:real"] SINCOS_TOTAL_PI),
      MP_TAC (← SPECL [← q r"x:real", ← q r"--y:real"] SINCOS_TOTAL_PI)] THEN
    ASM_REWRITE_TAC [REAL_POW_NEG, ARITH] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:real") STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC (← q r"t:real"), EXISTS_TAC (← q r"&2 * pi - t")] THEN
    ASM_REWRITE_TAC [SIN_SUB, COS_SUB, SIN_NPI, COS_NPI] THENL
     [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN ASM_CASES_TAC (← q r"t = &0") THEN
    ASM_REWRITE_TAC [SIN_0, COS_0] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC)

  let CIRCLE_SINCOS ← prove
   r"!x y. x pow 2 + y pow 2 = &1 ==> ?t. x = cos(t) /\ y = sin(t)"
   (MESON_TAC [SINCOS_TOTAL_2PI])

  let CX_PI_NZ ← prove
   r"~(Cx pi = Cx(&0))"
   (SIMP_TAC [CX_INJ, REAL_LT_IMP_NZ, PI_POS])

  let COMPLEX_UNIMODULAR_POLAR ← prove
   r"!z. (norm z = &1) ==> ?x. z = complex(cos(x),sin(x))"
   (GEN_TAC THEN
    DISCH_THEN (MP_TAC o C AP_THM (← q r"2") o AP_TERM (← q r"(pow):real->num->real")) THEN
    REWRITE_TAC [complex_norm] THEN
    SIMP_TAC [REAL_POW_2, ← REWRITE_RULE [REAL_POW_2] SQRT_POW_2,
              REAL_LE_SQUARE, REAL_LE_ADD] THEN
    REWRITE_TAC [← GSYM REAL_POW_2, REAL_MUL_LID] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"t:real") o MATCH_MP CIRCLE_SINCOS) THEN
    EXISTS_TAC (← q r"t:real") THEN ASM_REWRITE_TAC [COMPLEX_EQ, RE, IM])

  let SIN_INTEGER_2PI ← prove
   r"!n. integer n ==> sin((&2 * pi) * n) = &0"
   (REWRITE_TAC [SIN_EQ_0, ← REAL_ARITH (← q r"(&2 * pi) * n = (&2 * n) * pi")] THEN
    MESON_TAC [INTEGER_CLOSED])

  let SIN_INTEGER_PI ← prove
   r"!n. integer n ==> sin (n * pi) = &0"
   (REWRITE_TAC [INTEGER_CASES] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [REAL_MUL_LNEG, SIN_NPI, SIN_NEG, REAL_NEG_0])

  let COS_INTEGER_2PI ← prove
   r"!n. integer n ==> cos((&2 * pi) * n) = &1"
   (REWRITE_TAC [INTEGER_CASES, ← REAL_ARITH (← q r"(&2 * pi) * n = (&2 * n) * pi")] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [REAL_MUL_RNEG, REAL_OF_NUM_MUL] THEN
    SIMP_TAC [COS_NEG, COS_NPI, REAL_POW_NEG, REAL_MUL_LNEG,
              ARITH, EVEN_MULT, REAL_POW_ONE])

  let SINCOS_PRINCIPAL_VALUE ← prove
   r"!x. ?y. (--pi < y /\ y <= pi) /\ (sin(y) = sin(x) /\ cos(y) = cos(x))"
   (GEN_TAC THEN EXISTS_TAC (← q r"pi - (&2 * pi) * frac((pi - x) / (&2 * pi))") THEN
    CONJ_TAC THENL
     [SIMP_TAC [← REAL_ARITH (← q r"--p < p - x <=> x < (&2 * p) * &1"),
                ← REAL_ARITH (← q r"p - x <= p <=> (&2 * p) * &0 <= x"),
                REAL_LT_LMUL_EQ, REAL_LE_LMUL_EQ, REAL_LT_MUL,
                PI_POS, REAL_OF_NUM_LT, ARITH, FLOOR_FRAC],
      REWRITE_TAC [FRAC_FLOOR, REAL_SUB_LDISTRIB] THEN
      SIMP_TAC [REAL_DIV_LMUL, REAL_ENTIRE, REAL_OF_NUM_EQ, ARITH, REAL_LT_IMP_NZ,
       PI_POS, ← REAL_ARITH (← q r"a - (a - b - c):real = b + c"), SIN_ADD, COS_ADD] THEN
      SIMP_TAC [FLOOR_FRAC, SIN_INTEGER_2PI, COS_INTEGER_2PI] THEN
      CONV_TAC (fun t => REAL_RING t)])

  let CEXP_COMPLEX ← prove
   r"!r t. cexp(complex(r,t)) = Cx(exp r) * complex(cos t,sin t)"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [COMPLEX_EXPAND] THEN
    REWRITE_TAC [RE, IM, CEXP_ADD, CEXP_EULER, CX_EXP] THEN
    REWRITE_TAC [COMPLEX_TRAD, CX_SIN, CX_COS])

  let NORM_COSSIN ← prove
   r"!t. norm(complex(cos t,sin t)) = &1"
   (REWRITE_TAC [complex_norm, RE, IM] THEN ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
    REWRITE_TAC [SIN_CIRCLE, SQRT_1])

  let NORM_CEXP ← prove
   r"!z. norm(cexp z) = exp(Re z)"
   (REWRITE_TAC [FORALL_COMPLEX, CEXP_COMPLEX, COMPLEX_NORM_MUL] THEN
    REWRITE_TAC [NORM_COSSIN, RE, COMPLEX_NORM_CX] THEN
    MP_TAC REAL_EXP_POS_LT THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC)

  let NORM_CEXP_II ← prove
   r"!t. norm (cexp (ii * Cx t)) = &1"
   (REWRITE_TAC [NORM_CEXP, RE_MUL_II, IM_CX, REAL_NEG_0, REAL_EXP_0])

  let NORM_CEXP_IMAGINARY ← prove
   r"!z. norm(cexp z) = &1 ==> Re(z) = &0"
   (REWRITE_TAC [NORM_CEXP, REAL_EXP_EQ_1])

  let CEXP_EQ_1 ← prove
   r"!z. cexp z = Cx(&1) <=> Re(z) = &0 /\ ?n. integer n /\ Im(z) = &2 * n * pi"
   (REWRITE_TAC [FORALL_COMPLEX, CEXP_COMPLEX, RE, IM] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:real", ← q r"y:real"] THEN EQ_TAC THENL
     [DISCH_TAC THEN FIRST_ASSUM (MP_TAC o AP_TERM (← q r"norm:complex->real")) THEN
      SIMP_TAC [COMPLEX_NORM_MUL, CX_EXP, NORM_CEXP, RE_CX, COMPLEX_NORM_CX] THEN
      REWRITE_TAC [NORM_COSSIN, REAL_ABS_NUM, REAL_ABS_EXP, REAL_MUL_RID] THEN
      REWRITE_TAC [REAL_EXP_EQ_1] THEN DISCH_THEN SUBST_ALL_TAC THEN
      POP_ASSUM MP_TAC THEN REWRITE_TAC [REAL_EXP_0, COMPLEX_MUL_LID] THEN
      REWRITE_TAC [COMPLEX_EQ, RE, IM, RE_CX, IM_CX] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [SIN_EQ_0]) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"m:real")
       (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
      EXISTS_TAC (← q r"m / &2") THEN CONJ_TAC THENL [ALL_TAC, REAL_ARITH_TAC] THEN
      ONCE_REWRITE_TAC [← GSYM INTEGER_ABS] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE LAND_CONV [← GSYM COS_ABS]) THEN
      REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_DIV, REAL_ABS_NUM] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [integer]) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") SUBST_ALL_TAC) THEN
      SIMP_TAC [real_abs, PI_POS, REAL_LT_IMP_LE, COS_NPI] THEN
      REWRITE_TAC [REAL_POW_NEG, REAL_POW_ONE] THEN
      COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      FIRST_X_ASSUM (CHOOSE_THEN SUBST1_TAC o REWRITE_RULE [EVEN_EXISTS]) THEN
      REWRITE_TAC [← GSYM REAL_OF_NUM_MUL, ← REAL_ARITH (← q r"(&2 * x) / &2 = x")] THEN
      REWRITE_TAC [INTEGER_CLOSED],
      DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC (X_CHOOSE_TAC (← q r"n:real"))) THEN
      ASM_SIMP_TAC [REAL_EXP_0, COMPLEX_MUL_LID] THEN
      ONCE_REWRITE_TAC [← REAL_ARITH (← q r"&2 * x * y = (&2 * y) * x")] THEN
      ASM_SIMP_TAC [SIN_INTEGER_2PI, COS_INTEGER_2PI] THEN
      SIMPLE_COMPLEX_ARITH_TAC])

  let CEXP_EQ ← prove
   r"!w z. cexp w = cexp z <=> ?n. integer n /\ w = z + Cx(&2 * n * pi) * ii"
   (SIMP_TAC [CEXP_NZ, ← ExceptT.mk (COMPLEX_FIELD
     (← q r"~(z = Cx(&0)) ==> (w = z <=> w / z = Cx(&1))"))] THEN
    REWRITE_TAC [← GSYM CEXP_SUB, CEXP_EQ_1, RE_SUB, IM_SUB, REAL_SUB_0] THEN
    SIMP_TAC [COMPLEX_EQ, RE_ADD, IM_ADD, RE_MUL_II, IM_MUL_II, RE_CX, IM_CX] THEN
    REWRITE_TAC [REAL_NEG_0, REAL_ADD_RID, REAL_EQ_SUB_RADD] THEN
    MESON_TAC [REAL_ADD_SYM])

  let COMPLEX_EQ_CEXP ← prove
   r"!w z. abs(Im w - Im z) < &2 * pi /\ cexp w = cexp z ==> w = z"
   (SIMP_TAC [CEXP_NZ, ← GSYM CEXP_SUB, CEXP_EQ_1, ← ExceptT.mk (COMPLEX_FIELD
     (← q r"~(a = Cx(&0)) /\ ~(b = Cx(&0)) ==> (a = b <=> a / b = Cx(&1))"))] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"n:real") STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC (← q r"abs(Im w - Im z) < &2 * pi") THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [← GSYM IM_SUB, REAL_ABS_MUL, REAL_ABS_PI, REAL_ABS_NUM] THEN
    SIMP_TAC [REAL_MUL_ASSOC, REAL_LT_RMUL_EQ, PI_POS] THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"&1 <= x ==> ~(&2 * x < &2)")) THEN
    MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~(w:complex = z)") THEN
    REWRITE_TAC [] THEN ONCE_REWRITE_TAC [← GSYM COMPLEX_SUB_0] THEN
    ASM_REWRITE_TAC [COMPLEX_EQ, RE_CX, IM_CX, REAL_MUL_LZERO, REAL_MUL_RZERO])

  let CEXP_INTEGER_2PI ← prove
   r"!n. integer n ==> cexp(Cx(&2 * n * pi) * ii) = Cx(&1)"
   (REWRITE_TAC [CEXP_EQ_1, IM_MUL_II, RE_MUL_II, RE_CX, IM_CX] THEN
    REWRITE_TAC [REAL_NEG_0] THEN MESON_TAC [])

  let CEXP_LIPSCHITZ_BOUNDED ← prove
   r"!M a b. norm(a) <= M /\ norm(b) <= M
           ==> norm(cexp a - cexp b) <= exp(M) * norm(a - b)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"cexp", ← q r"cexp", ← q r"cball(Cx(&0):complex,M)",
                      ← q r"exp(M)"] COMPLEX_DIFFERENTIABLE_BOUND) THEN
    REWRITE_TAC [CONVEX_CBALL] THEN ANTS_TAC THENL
     [REWRITE_TAC [IN_CBALL, dist, COMPLEX_SUB_LZERO, NORM_NEG] THEN
      X_GEN_TAC (← q r"x:complex") THEN DISCH_TAC THEN CONJ_TAC THENL
       [SIMP_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN,
                  HAS_COMPLEX_DERIVATIVE_CEXP],
        REWRITE_TAC [NORM_CEXP, REAL_EXP_MONO_LE] THEN
        MP_TAC (← SPEC (← q r"x:complex") COMPLEX_NORM_GE_RE_IM) THEN
        ASM_REAL_ARITH_TAC],
      DISCH_THEN (MP_TAC o SPECL [← q r"a:complex", ← q r"b:complex"]) THEN
      REWRITE_TAC [IN_CBALL, dist, COMPLEX_SUB_LZERO, NORM_NEG] THEN
      ASM_REWRITE_TAC []])

  let SIN_COS_EQ ← prove
   r"!x y. sin y = sin x /\ cos y = cos x <=>
         ?n. integer n /\ y = x + &2 * n * pi"
   (REPEAT GEN_TAC THEN MP_TAC (← ISPECL [← q r"ii * Cx y", ← q r"ii * Cx x"] CEXP_EQ) THEN
    REWRITE_TAC [CEXP_EULER, ← GSYM CX_SIN, ← GSYM CX_COS] THEN
    REWRITE_TAC [← ExceptT.mk (COMPLEX_RING
      (← q r"ii * y = ii * x + z * ii <=> y = x + z"))] THEN
    REWRITE_TAC [← GSYM CX_ADD, CX_INJ] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [COMPLEX_EQ, RE_ADD, IM_ADD, RE_MUL_II, IM_MUL_II, RE_CX, IM_CX,
                 REAL_NEG_0, REAL_ADD_LID, REAL_ADD_RID] THEN
    MESON_TAC [])

  let SIN_COS_INJ ← prove
   r"!x y. sin x = sin y /\ cos x = cos y /\ abs(x - y) < &2 * pi ==> x = y"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM CX_INJ] THEN
    MATCH_MP_TAC (← ExceptT.mk (COMPLEX_RING (← q r"ii * x = ii * y ==> x = y"))) THEN
    MATCH_MP_TAC COMPLEX_EQ_CEXP THEN
    ASM_REWRITE_TAC [CEXP_EULER, ← GSYM CX_SIN, ← GSYM CX_COS] THEN
    ASM_REWRITE_TAC [IM_MUL_II, RE_CX])

  let CEXP_II_NE_1 ← prove
   r"!x. &0 < x /\ x < &2 * pi ==> ~(cexp(ii * Cx x) = Cx(&1))"
   (GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [CEXP_EQ_1] THEN
    REWRITE_TAC [RE_MUL_II, IM_CX, IM_MUL_II, IM_CX, REAL_NEG_0, RE_CX] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"n:real")
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    UNDISCH_TAC (← q r"&0 < &2 * n * pi") THEN ASM_CASES_TAC (← q r"n = &0") THEN
    ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_LT_REFL] THEN
    MP_TAC (← ISPEC (← q r"n:real") REAL_ABS_INTEGER_LEMMA) THEN ASM_REWRITE_TAC [] THEN
    DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o MATCH_MP (← REAL_ARITH
     (← q r"&2 * n * pi < &2 * pi ==> &0 < (&1 - n) * &2 * pi"))) THEN
    ASM_SIMP_TAC [REAL_LT_MUL_EQ, PI_POS, REAL_LT_MUL, REAL_OF_NUM_LT, ARITH] THEN
    ASM_REAL_ARITH_TAC)

  let CSIN_EQ_0 ← prove
   r"!z. csin z = Cx(&0) <=> ?n. integer n /\ z = Cx(n * pi)"
   (GEN_TAC THEN REWRITE_TAC [csin, COMPLEX_MUL_LNEG, CEXP_NEG] THEN
    SIMP_TAC [CEXP_NZ, ← ExceptT.mk (COMPLEX_FIELD (← q r"~(z = Cx(&0))
          ==> ((z - inv z) / (Cx(&2) * ii) = Cx(&0) <=> z pow 2 = Cx(&1))"))] THEN
    REWRITE_TAC [← GSYM CEXP_N, CEXP_EQ_1] THEN
    REWRITE_TAC [RE_MUL_CX, IM_MUL_CX, RE_MUL_II, IM_MUL_II] THEN
    REWRITE_TAC [COMPLEX_EQ, IM_CX, RE_CX, RIGHT_AND_EXISTS_THM] THEN
    EQ_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [] THEN REAL_ARITH_TAC)

  let CCOS_EQ_0 ← prove
   r"!z. ccos z = Cx(&0) <=> ?n. integer n /\ z = Cx((n + &1 / &2) * pi)"
   (GEN_TAC THEN MP_TAC (← SPEC (← q r"z - Cx(pi / &2)") CSIN_EQ_0) THEN
    REWRITE_TAC [CSIN_SUB, ← GSYM CX_SIN, ← GSYM CX_COS, SIN_PI2, COS_PI2] THEN
    SIMP_TAC [← ExceptT.mk (COMPLEX_RING
      (← q r"s * Cx(&0) - c * Cx(&1) = Cx(&0) <=> c = Cx(&0)"))] THEN
    REWRITE_TAC [REAL_ADD_RDISTRIB, COMPLEX_EQ_SUB_RADD, CX_ADD] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"&1 / &2 * x = x / &2")])

  let CCOS_EQ_1 ← prove
   r"!z. ccos z = Cx(&1) <=> ?n. integer n /\ z = Cx(&2 * n * pi)"
   (GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
     [← ExceptT.mk (COMPLEX_RING (← q r"z = Cx(&2) * z / Cx(&2)"))] THEN
    REWRITE_TAC [CCOS_DOUBLE_CSIN, ← ExceptT.mk (COMPLEX_RING
     (← q r"a - Cx(&2) * s pow 2 = a <=> s = Cx(&0)"))] THEN
    REWRITE_TAC [CSIN_EQ_0, CX_MUL] THEN
    EQ_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [] THEN
    CONV_TAC COMPLEX_RING)

  let CSIN_EQ_1 ← prove
   r"!z. csin z = Cx(&1) <=> ?n. integer n /\ z = Cx((&2 * n + &1 / &2) * pi)"
   (GEN_TAC THEN MP_TAC (← SPEC (← q r"z - Cx(pi / &2)") CCOS_EQ_1) THEN
    REWRITE_TAC [CCOS_SUB, ← GSYM CX_SIN, ← GSYM CX_COS, SIN_PI2, COS_PI2] THEN
    SIMP_TAC [← ExceptT.mk (COMPLEX_RING
      (← q r"s * Cx(&0) + c * Cx(&1) = Cx(&1) <=> c = Cx(&1)"))] THEN
    REWRITE_TAC [REAL_ADD_RDISTRIB, COMPLEX_EQ_SUB_RADD, CX_ADD] THEN
    REWRITE_TAC [REAL_MUL_ASSOC, ← REAL_ARITH (← q r"&1 / &2 * x = x / &2")])

  let CSIN_EQ_MINUS1 ← prove
   r"!z. csin z = --Cx(&1) <=>
       ?n. integer n /\ z = Cx((&2 * n + &3 / &2) * pi)"
   (GEN_TAC THEN REWRITE_TAC [← ExceptT.mk (COMPLEX_RING
      (← q r"z:complex = --w <=> --z = w"))] THEN
    REWRITE_TAC [← GSYM CSIN_NEG, CSIN_EQ_1] THEN
    REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"--z:complex = w <=> z = --w"))] THEN
    EQ_TAC THEN DISCH_THEN (X_CHOOSE_THEN (← q r"n:real") STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [← GSYM CX_NEG, CX_INJ] THEN
    EXISTS_TAC (← q r"--(n + &1)") THEN
    ASM_SIMP_TAC [INTEGER_CLOSED] THEN REAL_ARITH_TAC)

  let CCOS_EQ_MINUS1 ← prove
   r"!z. ccos z = --Cx(&1) <=>
       ?n. integer n /\ z = Cx((&2 * n + &1) * pi)"
   (GEN_TAC THEN MP_TAC (← SPEC (← q r"z - Cx(pi / &2)") CSIN_EQ_1) THEN
    REWRITE_TAC [CSIN_SUB, ← GSYM CX_SIN, ← GSYM CX_COS, SIN_PI2, COS_PI2] THEN
    SIMP_TAC [← ExceptT.mk (COMPLEX_RING
      (← q r"s * Cx(&0) - c * Cx(&1) = Cx(&1) <=> c = --Cx(&1)"))] THEN
    REWRITE_TAC [REAL_ADD_RDISTRIB, COMPLEX_EQ_SUB_RADD, ← GSYM CX_ADD] THEN
    DISCH_TAC THEN EQ_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
    SIMP_TAC [CX_INJ] THEN REAL_ARITH_TAC)

  let COS_EQ_1 ← prove
   r"!x. cos x = &1 <=> ?n. integer n /\ x = &2 * n * pi"
   (REWRITE_TAC [← GSYM CX_INJ, CX_COS, CCOS_EQ_1])

  let SIN_EQ_1 ← prove
   r"!x. sin x = &1 <=> ?n. integer n /\ x = (&2 * n + &1 / &2) * pi"
   (REWRITE_TAC [← GSYM CX_INJ, CX_SIN, CSIN_EQ_1])

  let SIN_EQ_MINUS1 ← prove
   r"!x. sin x = --(&1) <=> ?n. integer n /\ x = (&2 * n + &3 / &2) * pi"
   (REWRITE_TAC [← GSYM CX_INJ, CX_NEG, CX_SIN, CSIN_EQ_MINUS1])

  let COS_EQ_MINUS1 ← prove
   r"!x. cos x = --(&1) <=>
       ?n. integer n /\ x = (&2 * n + &1) * pi"
   (REWRITE_TAC [← GSYM CX_INJ, CX_NEG, CX_COS, CCOS_EQ_MINUS1])

  let DIST_CEXP_II_1 ← prove
   r"!t. norm(cexp(ii * Cx t) - Cx(&1)) = &2 * abs(sin(t / &2))"
   (GEN_TAC THEN REWRITE_TAC [NORM_EQ_SQUARE] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC, REWRITE_TAC [← GSYM NORM_POW_2]] THEN
    REWRITE_TAC [CEXP_EULER, COMPLEX_SQNORM, ← GSYM CX_COS, ← GSYM CX_SIN] THEN
    REWRITE_TAC [IM_ADD, RE_ADD, IM_SUB, RE_SUB, IM_MUL_II, RE_MUL_II] THEN
    REWRITE_TAC [RE_CX, IM_CX, REAL_POW2_ABS, REAL_POW_MUL] THEN
    MP_TAC (← ISPEC (← q r"t / &2") COS_DOUBLE_SIN) THEN
    REWRITE_TAC [← REAL_ARITH (← q r"&2 * t / &2 = t")] THEN
    MP_TAC (← SPEC (← q r"t:real") SIN_CIRCLE) THEN CONV_TAC (fun t => REAL_RING t))

  let CX_SINH ← prove
   r"Cx((exp x - inv(exp x)) / &2) = --ii * csin(ii * Cx x)"
   (REWRITE_TAC [csin, ← ExceptT.mk (COMPLEX_RING
      (← q r"--ii * ii * z = z /\ ii * ii * z = --z"))] THEN
    REWRITE_TAC [CEXP_NEG, ← GSYM CX_EXP, ← GSYM CX_INV, CX_SUB, CX_DIV] THEN
    CONV_TAC COMPLEX_FIELD)

  let CX_COSH ← prove
   r"Cx((exp x + inv(exp x)) / &2) = ccos(ii * Cx x)"
   (REWRITE_TAC [ccos, ← ExceptT.mk (COMPLEX_RING
      (← q r"--ii * ii * z = z /\ ii * ii * z = --z"))] THEN
    REWRITE_TAC [CEXP_NEG, ← GSYM CX_EXP, ← GSYM CX_INV, CX_ADD, CX_DIV] THEN
    CONV_TAC COMPLEX_FIELD)

  let NORM_CCOS_POW_2 ← prove
   r"!z. norm(ccos z) pow 2 =
       cos(Re z) pow 2 + (exp(Im z) - inv(exp(Im z))) pow 2 / &4"
   (REWRITE_TAC [FORALL_COMPLEX, RE, IM] THEN
    REWRITE_TAC [COMPLEX_TRAD, CCOS_ADD, COMPLEX_SQNORM] THEN
    SIMP_TAC [RE_SUB, IM_SUB, ← GSYM CX_COS, ← GSYM CX_SIN, IM_MUL_CX, RE_MUL_CX] THEN
    REWRITE_TAC [ccos, csin, CEXP_NEG, ← ExceptT.mk (COMPLEX_FIELD
     (← q r"--ii * ii * z = z /\ ii * ii * z = --z /\
      z / (Cx(&2) * ii) = --(ii * z / Cx(&2))"))] THEN
    REWRITE_TAC [RE_ADD, RE_SUB, IM_ADD, IM_SUB, RE_MUL_II, IM_MUL_II,
                 RE_DIV_CX, IM_DIV_CX, RE_NEG, IM_NEG] THEN
    REWRITE_TAC [← GSYM CX_EXP, ← GSYM CX_INV, IM_CX, RE_CX] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:real", ← q r"y:real"] THEN
    MP_TAC (← SPEC (← q r"x:real") SIN_CIRCLE) THEN
    MP_TAC (← SPEC (← q r"y:real") REAL_EXP_NZ) THEN
    CONV_TAC REAL_FIELD)

  let NORM_CSIN_POW_2 ← prove
   r"!z. norm(csin z) pow 2 =
       (exp(&2 * Im z) + inv(exp(&2 * Im z)) - &2 * cos(&2 * Re z)) / &4"
   (REWRITE_TAC [FORALL_COMPLEX, RE, IM] THEN
    REWRITE_TAC [COMPLEX_TRAD, CSIN_ADD, COMPLEX_SQNORM] THEN
    SIMP_TAC [RE_ADD, IM_ADD, ← GSYM CX_SIN, ← GSYM CX_SIN, IM_MUL_CX, RE_MUL_CX,
              ← GSYM CX_COS] THEN
    REWRITE_TAC [ccos, csin, CEXP_NEG, ← ExceptT.mk (COMPLEX_FIELD
     (← q r"--ii * ii * z = z /\ ii * ii * z = --z /\
      z / (Cx(&2) * ii) = --(ii * z / Cx(&2))"))] THEN
    REWRITE_TAC [RE_ADD, RE_SUB, IM_ADD, IM_SUB, RE_MUL_II, IM_MUL_II,
                 RE_DIV_CX, IM_DIV_CX, RE_NEG, IM_NEG] THEN
    REWRITE_TAC [← GSYM CX_EXP, ← GSYM CX_INV, IM_CX, RE_CX] THEN
    REWRITE_TAC [REAL_EXP_N, COS_DOUBLE] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:real", ← q r"y:real"] THEN
    MP_TAC (← SPEC (← q r"x:real") SIN_CIRCLE) THEN
    MP_TAC (← SPEC (← q r"y:real") REAL_EXP_NZ) THEN
    CONV_TAC REAL_FIELD)

  let CSIN_EQ ← prove
   r"!w z. csin w = csin z <=>
         ?n. integer n /\
             (w = z + Cx(&2 * n * pi) \/ w = --z + Cx((&2 * n + &1) * pi))"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM COMPLEX_SUB_0] THEN
    REWRITE_TAC [COMPLEX_SUB_CSIN, COMPLEX_ENTIRE, CSIN_EQ_0, CCOS_EQ_0] THEN
    REWRITE_TAC [CX_INJ, REAL_OF_NUM_EQ, ARITH_EQ, OR_EXISTS_THM] THEN
    AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"n:real") THEN
    ASM_CASES_TAC (← q r"integer(n)") THEN
    ASM_REWRITE_TAC [← ExceptT.mk (COMPLEX_FIELD
      (← q r"a / Cx(&2) = b <=> a = Cx(&2) * b"))] THEN
    REWRITE_TAC [← GSYM CX_MUL, ← REAL_ARITH
      (← q r"&2 * (n + &1 / &2) * pi = (&2 * n + &1) * pi")] THEN
    CONV_TAC COMPLEX_RING)

  let CCOS_EQ ← prove
   r"!w z. ccos(w) = ccos(z) <=>
         ?n. integer n /\
             (w = z + Cx(&2 * n * pi) \/ w = --z + Cx(&2 * n * pi))"
   (REPEAT GEN_TAC THEN CONV_TAC (LAND_CONV SYM_CONV) THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM COMPLEX_SUB_0] THEN
    REWRITE_TAC [COMPLEX_SUB_CCOS, COMPLEX_ENTIRE, CSIN_EQ_0] THEN
    REWRITE_TAC [CX_INJ, REAL_OF_NUM_EQ, ARITH_EQ, OR_EXISTS_THM] THEN
    AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"n:real") THEN
    ASM_CASES_TAC (← q r"integer(n)") THEN ASM_REWRITE_TAC [CX_MUL] THEN
    CONV_TAC COMPLEX_RING)

  let SIN_EQ ← prove
   r"!x y. sin x = sin y <=>
         ?n. integer n /\
             (x = y + &2 * n * pi \/ x = --y + (&2 * n + &1) * pi)"
   (REWRITE_TAC [← GSYM CX_INJ, CX_SIN, CSIN_EQ] THEN
    REWRITE_TAC [← GSYM CX_ADD, ← GSYM CX_NEG, CX_INJ])

  let COS_EQ ← prove
   r"!x y. cos x = cos y <=>
         ?n. integer n /\
             (x = y + &2 * n * pi \/ x = --y + &2 * n * pi)"
   (REWRITE_TAC [← GSYM CX_INJ, CX_COS, CCOS_EQ] THEN
    REWRITE_TAC [← GSYM CX_ADD, ← GSYM CX_NEG, CX_INJ])

  let NORM_CCOS_LE ← prove
   r"!z. norm(ccos z) <= exp(norm z)"
   (GEN_TAC THEN REWRITE_TAC [ccos] THEN
    REWRITE_TAC [COMPLEX_NORM_DIV, COMPLEX_NORM_CX, REAL_ABS_NUM] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"x / &2 <= y <=> x <= &2 * y")] THEN
    MATCH_MP_TAC (← NORM_ARITH
     (← q r"norm(a) + norm(b) <= d ==> norm(a + b) <= d")) THEN
    REWRITE_TAC [NORM_CEXP, COMPLEX_MUL_LNEG, RE_NEG, REAL_EXP_NEG] THEN
    REWRITE_TAC [COMPLEX_NORM_CX, RE_MUL_II, REAL_ABS_NUM] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"exp(&0) = &1 /\ (exp(&0) <= w \/ exp(&0) <= z) /\ (w <= u /\ z <= u)
      ==> w + z <= &2 * u")) THEN
    REWRITE_TAC [← GSYM REAL_EXP_NEG, REAL_EXP_MONO_LE] THEN
    REWRITE_TAC [REAL_EXP_0] THEN
    MP_TAC (← SPEC (← q r"z:complex") COMPLEX_NORM_GE_RE_IM) THEN
    REAL_ARITH_TAC)

  let NORM_CCOS_PLUS1_LE ← prove
   r"!z. norm(Cx(&1) + ccos z) <= &2 * exp(norm z)"
   (GEN_TAC THEN REWRITE_TAC [ccos] THEN
    REWRITE_TAC [COMPLEX_NORM_DIV, COMPLEX_NORM_CX, REAL_ABS_NUM, ← ExceptT.mk (COMPLEX_RING
     (← q r"Cx(&1) + (z + z') / Cx(&2) = (Cx(&2) + z + z') / Cx(&2)"))] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"x / &2 <= &2 * y <=> x <= &4 * y")] THEN
    MATCH_MP_TAC (← NORM_ARITH
     (← q r"norm(a) + norm(b) + norm(c) <= d ==> norm(a + b + c) <= d")) THEN
    REWRITE_TAC [NORM_CEXP, COMPLEX_MUL_LNEG, RE_NEG, REAL_EXP_NEG] THEN
    REWRITE_TAC [COMPLEX_NORM_CX, RE_MUL_II, REAL_ABS_NUM] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"exp(&0) = &1 /\ (exp(&0) <= w \/ exp(&0) <= z) /\ (w <= u /\ z <= u)
      ==> &2 + w + z <= &4 * u")) THEN
    REWRITE_TAC [← GSYM REAL_EXP_NEG, REAL_EXP_MONO_LE] THEN
    REWRITE_TAC [REAL_EXP_0] THEN
    MP_TAC (← SPEC (← q r"z:complex") COMPLEX_NORM_GE_RE_IM) THEN
    REAL_ARITH_TAC)

  pure { SIN_TOTAL_POS, SINCOS_TOTAL_PI2, SINCOS_TOTAL_PI, SINCOS_TOTAL_2PI, CIRCLE_SINCOS,
         CX_PI_NZ, COMPLEX_UNIMODULAR_POLAR, SIN_INTEGER_2PI, SIN_INTEGER_PI,
         COS_INTEGER_2PI, SINCOS_PRINCIPAL_VALUE, CEXP_COMPLEX, NORM_COSSIN, NORM_CEXP,
         NORM_CEXP_II, NORM_CEXP_IMAGINARY, CEXP_EQ_1, CEXP_EQ, COMPLEX_EQ_CEXP,
         CEXP_INTEGER_2PI, CEXP_LIPSCHITZ_BOUNDED, SIN_COS_EQ, SIN_COS_INJ, CEXP_II_NE_1,
         CSIN_EQ_0, CCOS_EQ_0, CCOS_EQ_1, CSIN_EQ_1, CSIN_EQ_MINUS1, CCOS_EQ_MINUS1,
         COS_EQ_1, SIN_EQ_1, SIN_EQ_MINUS1, COS_EQ_MINUS1, DIST_CEXP_II_1, CX_SINH,
         CX_COSH, NORM_CCOS_POW_2, NORM_CSIN_POW_2, CSIN_EQ, CCOS_EQ, SIN_EQ, COS_EQ,
         NORM_CCOS_LE, NORM_CCOS_PLUS1_LE }
/- ------------------------------------------------------------------------- -/
/- Taylor series for the complex exponential; approximation to e; Taylor    -/
/- series for complex sine and cosine.  (transcendentals.ml 1913-2088)      -/
/- ------------------------------------------------------------------------- -/

structure TSG where
  TAYLOR_CEXP : thm
  E_APPROX_32 : thm
  TAYLOR_CSIN_RAW : thm
  TAYLOR_CSIN : thm
  CSIN_CONVERGES : thm
  TAYLOR_CCOS_RAW : thm
  TAYLOR_CCOS : thm
  CCOS_CONVERGES : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSG [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) (BTSB : TSB) (BTSF : TSF) : ExceptT String IO TSG := do
  -- @@SCOPE BEGIN
  let { CEXP_0, CEXP_CONVERGES, .. } := BTSA
  let { ccos, csin, CX_EXP, REAL_EXP_MONO_LE, .. } := BTSB
  let { NORM_CEXP, .. } := BTSF
  let { EXPAND_VSUM_CONV, .. } := D
  let { COMPLEX_DIFF_TAC, .. } := D.knk
  let { COMPLEX_TAYLOR, .. } := D.knl
  let { SERIES_TERMS_TOZERO, .. } := D.qtopology
  let { VSUM_PAIR_0, .. } := D.qvectors
  let { ADD_ASSOC, ARITH_EVEN, ARITH_ODD, NOT_EVEN, ODD, ODD_ADD, ODD_MULT,
        .. } := D.qsession
  let { complex_div, SIMPLE_COMPLEX_ARITH_TAC, .. } := D.cn.cxa
  let { COMPLEX_ADD_LID, COMPLEX_ADD_RID, COMPLEX_ADD_RINV, COMPLEX_MUL_ASSOC,
        COMPLEX_MUL_LID, COMPLEX_MUL_LNEG, COMPLEX_MUL_RZERO, COMPLEX_SUB_REFL,
        COMPLEX_SUB_RZERO, .. } := D.cn.cxb
  let { COMPLEX_CMUL, COMPLEX_NORM_CX, COMPLEX_NORM_II, COMPLEX_POW_ADD, COMPLEX_POW_II_2,
        COMPLEX_POW_MUL, COMPLEX_POW_NEG, COMPLEX_POW_ONE, COMPLEX_POW_POW, COMPLEX_VEC_0,
        CX_ADD, CX_DIV, CX_SUB, RE_CX, RE_MUL_CX, RE_MUL_II, RE_NEG, .. } := D.cn.cxc
  let { COMPLEX_RING, .. } := D.cn.cxd
  let { COMPLEX_FIELD, .. } := D.cn.cxe
  let { COMPLEX_NORM_DIV, COMPLEX_NORM_MUL, COMPLEX_NORM_POW, .. } := D.cn.cxf
  let { VSUM_COMPLEX_LMUL, .. } := D.cn.cxi
  let { CONVEX_SEGMENT, .. } := D.cn.ms.qconvex
  let { FROM_0, .. } := D.cn.ms.qmisc
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_REAL_ARITH_TAC, NORM_ARITH, NUM_REDUCE_CONV,
        REAL_ARITH, REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV, .. } := D.cn.cx.cvx
  let { EVEN, LE_0, .. } := D.cn.cx.cpx
  let { ARITH, ETA_AX, FINITE_NUMSEG, .. } := D.cn.cx.cvx.core1
  let { INTER_UNIV, .. } := D.cn.cx.cvx.core2
  let { MONO_EXISTS, MONO_FORALL, MONO_IMP, REAL_ABS_MUL, REAL_ABS_NEG, REAL_ABS_NUM,
        .. } := D.cn.cx.cvx.core3
  let { REAL_LE_RMUL, .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_RID, REAL_MUL_SYM, .. } := D.cn.cx.cvx.core5
  let { real_div, real_pow, .. } := D.cn.cx.cvx.core6
  let { LIFT_CMUL, .. } := D.cn.cx.cvx.vec2
  let { NORM_NEG, NORM_SUB, .. } := D.cn.cx.cvx.vec3
  let { VECTOR_ADD_LID, VECTOR_MUL_ASSOC, VECTOR_MUL_RZERO, VSUM_ADD, VSUM_CLAUSES_NUMSEG,
        VSUM_EQ, VSUM_SUB, .. } := D.cn.cx.cvx.vec4
  let { EVENTUALLY_SEQUENTIALLY, .. } := D.cn.cx.cvx.met
  let { ENDS_IN_SEGMENT, .. } := D.cn.cx.cvx.top3
  let { IN_SEGMENT, LIM_NULL_COMPARISON, LIM_SEQUENTIALLY, .. } := D.cn.cx.cvx.top4
  let { LIM_NULL, LIM_NULL_CMUL, LIM_NULL_NORM, sums, .. } := D.cn.ms.ig.dv.qtopology2
  let { EVEN_ADD, EVEN_MULT, .. } := D.cn.ms.ig.dv.dg.qsession
  -- @@SCOPE END

  let TAYLOR_CEXP ← prove
   r"!n z. norm(cexp z - vsum(0..n) (\k. z pow k / Cx(&(FACT k))))
         <= exp(abs(Re z)) * (norm z) pow (n + 1) / &(FACT n)"
   (REPEAT GEN_TAC THEN MP_TAC (← ISPECL
     [← q r"\k:num. cexp", ← q r"n:num", ← q r"segment[Cx(&0),z]", ← q r"exp(abs(Re z))"]
          COMPLEX_TAYLOR) THEN
    REWRITE_TAC [CONVEX_SEGMENT, NORM_CEXP, REAL_EXP_MONO_LE] THEN ANTS_TAC THENL
     [REWRITE_TAC [IN_SEGMENT] THEN REPEAT STRIP_TAC THENL
       [GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [← GSYM ETA_AX] THEN
        COMPLEX_DIFF_TAC THEN REWRITE_TAC [COMPLEX_MUL_LID],
        ASM_REWRITE_TAC [← GSYM COMPLEX_VEC_0, VECTOR_MUL_RZERO] THEN
        REWRITE_TAC [VECTOR_ADD_LID, COMPLEX_CMUL, COMPLEX_NORM_MUL] THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC (← REAL_ARITH (← q r"abs x <= a ==> x <= a")) THEN
        REWRITE_TAC [RE_MUL_CX, REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REAL_ARITH_TAC],
      DISCH_THEN (MP_TAC o SPECL [← q r"Cx(&0)", ← q r"z:complex"]) THEN
      SIMP_TAC [ENDS_IN_SEGMENT, COMPLEX_SUB_RZERO, CEXP_0, COMPLEX_MUL_LID]])

  let E_APPROX_32 ← prove
   r"abs(exp(&1) - &5837465777 / &2147483648) <= inv(&2 pow 32)"
   (MP_TAC (← ISPECL [← q r"14", ← q r"Cx(&1)"] TAYLOR_CEXP) THEN
    SIMP_TAC [RE_CX, REAL_ABS_NUM, ← GSYM CX_EXP, ← GSYM CX_DIV, ← GSYM CX_SUB,
              COMPLEX_POW_ONE, COMPLEX_NORM_CX] THEN
    CONV_TAC (ONCE_DEPTH_CONV EXPAND_VSUM_CONV) THEN
    REWRITE_TAC [← GSYM CX_ADD, ← GSYM CX_SUB, COMPLEX_NORM_CX] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REAL_ARITH_TAC)

  let TAYLOR_CSIN_RAW ← prove
   r"!n z. norm(csin z -
              vsum(0..n) (\k. if ODD k
                              then --ii * (ii * z) pow k / Cx(&(FACT k))
                              else Cx(&0)))
         <= exp(abs(Im z)) * (norm z) pow (n + 1) / &(FACT n)"
   (MP_TAC TAYLOR_CEXP THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"n:num") THEN
    DISCH_TAC THEN X_GEN_TAC (← q r"z:complex") THEN REWRITE_TAC [csin] THEN
    REWRITE_TAC [← ExceptT.mk (COMPLEX_FIELD
      (← q r"a / (Cx(&2) * ii) - b = (a - Cx(&2) * ii * b) / (Cx(&2) * ii)"))] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (MP_TAC (← SPEC (← q r"ii * z") th) THEN MP_TAC (← SPEC (← q r"--ii * z") th))) THEN
    REWRITE_TAC [COMPLEX_MUL_LNEG, RE_NEG, REAL_ABS_NEG, RE_MUL_II] THEN
    REWRITE_TAC [COMPLEX_NORM_DIV, COMPLEX_NORM_MUL, COMPLEX_NORM_CX, NORM_NEG,
                 COMPLEX_NORM_II, REAL_ABS_NUM, REAL_MUL_RID, REAL_MUL_LID,
                 ← REAL_ARITH (← q r"x / &2 <= y <=> x <= &2 * y")] THEN
    MATCH_MP_TAC (← NORM_ARITH
     (← q r"sp - sn = s2
      ==> norm(en - sn) <= d
          ==> norm(ep - sp) <= d ==> norm(ep - en - s2) <= &2 * d")) THEN
    SIMP_TAC [← GSYM VSUM_SUB, ← GSYM VSUM_COMPLEX_LMUL, FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC (← q r"k:num") THEN DISCH_TAC THEN
    REWRITE_TAC [COMPLEX_POW_NEG, ← GSYM NOT_EVEN] THEN ASM_CASES_TAC (← q r"EVEN k") THEN
    ASM_REWRITE_TAC [COMPLEX_SUB_REFL, COMPLEX_MUL_RZERO] THEN
    REWRITE_TAC [← ExceptT.mk (COMPLEX_RING
      (← q r"Cx(&2) * ii * --(ii * z) = Cx(&2) * z"))] THEN
    SIMPLE_COMPLEX_ARITH_TAC)

  let TAYLOR_CSIN ← prove
   r"!n z. norm(csin z -
              vsum(0..n) (\k. --Cx(&1) pow k *
                              z pow (2 * k + 1) / Cx(&(FACT(2 * k + 1)))))
         <= exp(abs(Im z)) * norm(z) pow (2 * n + 3) / &(FACT(2 * n + 2))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"SUC(2 * n + 1)", ← q r"z:complex"] TAYLOR_CSIN_RAW) THEN
    SIMP_TAC [VSUM_CLAUSES_NUMSEG, VSUM_PAIR_0, ODD_ADD, ODD_MULT, ARITH_ODD,
              LE_0, ODD, COMPLEX_ADD_LID, COMPLEX_ADD_RID] THEN
    SIMP_TAC [← ARITH_RULE (← q r"SUC(2 * n + 1) = 2 * n + 2"), ← GSYM ADD_ASSOC, ARITH] THEN
    MATCH_MP_TAC (← NORM_ARITH
     (← q r"s = t ==> norm(x - s) <= e ==> norm(x - t) <= e")) THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC (← q r"k:num") THEN STRIP_TAC THEN
    REWRITE_TAC [COMPLEX_POW_MUL, complex_div, COMPLEX_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [COMPLEX_POW_ADD, ← GSYM COMPLEX_POW_POW] THEN
    REWRITE_TAC [COMPLEX_POW_II_2] THEN CONV_TAC COMPLEX_RING)

  let CSIN_CONVERGES ← prove
   r"!z. ((\n. --Cx(&1) pow n * z pow (2 * n + 1) / Cx(&(FACT(2 * n + 1))))
        sums csin(z)) (from 0)"
   (GEN_TAC THEN REWRITE_TAC [sums, FROM_0, INTER_UNIV] THEN
    ONCE_REWRITE_TAC [LIM_NULL] THEN MATCH_MP_TAC LIM_NULL_COMPARISON THEN
    EXISTS_TAC
     (← q r"\n. exp(abs(Im z)) * norm z pow (2 * n + 3) / &(FACT(2 * n + 2))") THEN
    REWRITE_TAC [EVENTUALLY_SEQUENTIALLY] THEN
    ONCE_REWRITE_TAC [NORM_SUB] THEN REWRITE_TAC [TAYLOR_CSIN] THEN
    REWRITE_TAC [LIFT_CMUL] THEN MATCH_MP_TAC LIM_NULL_CMUL THEN
    REWRITE_TAC [← ARITH_RULE (← q r"2 * n + 3 = SUC(2 * n + 2)"), real_div] THEN
    REWRITE_TAC [LIFT_CMUL, real_pow] THEN
    REWRITE_TAC [← GSYM VECTOR_MUL_ASSOC] THEN
    MATCH_MP_TAC LIM_NULL_CMUL THEN
    MP_TAC (← MATCH_MP SERIES_TERMS_TOZERO (← SPEC (← q r"z:complex") CEXP_CONVERGES)) THEN
    GEN_REWRITE_TAC LAND_CONV [LIM_NULL_NORM] THEN
    REWRITE_TAC [COMPLEX_NORM_DIV, COMPLEX_NORM_POW, COMPLEX_NORM_CX] THEN
    REWRITE_TAC [REAL_ABS_NUM, ← GSYM LIFT_CMUL, ← GSYM real_div] THEN
    REWRITE_TAC [LIM_SEQUENTIALLY] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
    REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC)

  let TAYLOR_CCOS_RAW ← prove
   r"!n z. norm(ccos z -
              vsum(0..n) (\k. if EVEN k
                              then (ii * z) pow k / Cx(&(FACT k))
                              else Cx(&0)))
         <= exp(abs(Im z)) * (norm z) pow (n + 1) / &(FACT n)"
   (MP_TAC TAYLOR_CEXP THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"n:num") THEN
    DISCH_TAC THEN X_GEN_TAC (← q r"z:complex") THEN REWRITE_TAC [ccos] THEN
    REWRITE_TAC [← ExceptT.mk (COMPLEX_FIELD
      (← q r"a / Cx(&2) - b = (a - Cx(&2) * b) / Cx(&2)"))] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (MP_TAC (← SPEC (← q r"ii * z") th) THEN MP_TAC (← SPEC (← q r"--ii * z") th))) THEN
    REWRITE_TAC [COMPLEX_MUL_LNEG, RE_NEG, REAL_ABS_NEG, RE_MUL_II] THEN
    REWRITE_TAC [COMPLEX_NORM_DIV, COMPLEX_NORM_MUL, COMPLEX_NORM_CX, NORM_NEG,
                 COMPLEX_NORM_II, REAL_ABS_NUM, REAL_MUL_RID, REAL_MUL_LID,
                 ← REAL_ARITH (← q r"x / &2 <= y <=> x <= &2 * y")] THEN
    MATCH_MP_TAC (← NORM_ARITH
     (← q r"sp + sn = s2
      ==> norm(en - sn) <= d
          ==> norm(ep - sp) <= d ==> norm((ep + en) - s2) <= &2 * d")) THEN
    SIMP_TAC [← GSYM VSUM_ADD, ← GSYM VSUM_COMPLEX_LMUL, FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC (← q r"k:num") THEN DISCH_TAC THEN
    REWRITE_TAC [COMPLEX_POW_NEG, ← GSYM NOT_EVEN] THEN ASM_CASES_TAC (← q r"EVEN k") THEN
    ASM_REWRITE_TAC [COMPLEX_ADD_RINV, COMPLEX_MUL_RZERO] THEN
    SIMPLE_COMPLEX_ARITH_TAC)

  let TAYLOR_CCOS ← prove
   r"!n z. norm(ccos z -
              vsum(0..n) (\k. --Cx(&1) pow k *
                              z pow (2 * k) / Cx(&(FACT(2 * k)))))
         <= exp(abs(Im z)) * norm(z) pow (2 * n + 2) / &(FACT(2 * n + 1))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"2 * n + 1", ← q r"z:complex"] TAYLOR_CCOS_RAW) THEN
    SIMP_TAC [VSUM_PAIR_0, EVEN_ADD, EVEN_MULT, ARITH_EVEN,
              LE_0, EVEN, COMPLEX_ADD_LID, COMPLEX_ADD_RID] THEN
    SIMP_TAC [← ARITH_RULE (← q r"(2 * n + 1) + 1 = 2 * n + 2")] THEN
    MATCH_MP_TAC (← NORM_ARITH
     (← q r"s = t ==> norm(x - s) <= e ==> norm(x - t) <= e")) THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC (← q r"k:num") THEN STRIP_TAC THEN
    REWRITE_TAC [COMPLEX_POW_MUL, complex_div, COMPLEX_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [← GSYM COMPLEX_POW_POW, COMPLEX_POW_II_2])

  let CCOS_CONVERGES ← prove
   r"!z. ((\n. --Cx(&1) pow n * z pow (2 * n) / Cx(&(FACT(2 * n))))
        sums ccos(z)) (from 0)"
   (GEN_TAC THEN REWRITE_TAC [sums, FROM_0, INTER_UNIV] THEN
    ONCE_REWRITE_TAC [LIM_NULL] THEN MATCH_MP_TAC LIM_NULL_COMPARISON THEN
    EXISTS_TAC
     (← q r"\n. exp(abs(Im z)) * norm z pow (2 * n + 2) / &(FACT(2 * n + 1))") THEN
    REWRITE_TAC [EVENTUALLY_SEQUENTIALLY] THEN
    ONCE_REWRITE_TAC [NORM_SUB] THEN REWRITE_TAC [TAYLOR_CCOS] THEN
    REWRITE_TAC [LIFT_CMUL] THEN MATCH_MP_TAC LIM_NULL_CMUL THEN
    REWRITE_TAC [← ARITH_RULE (← q r"2 * n + 2 = SUC(2 * n + 1)"), real_div] THEN
    REWRITE_TAC [LIFT_CMUL, real_pow] THEN
    REWRITE_TAC [← GSYM VECTOR_MUL_ASSOC] THEN
    MATCH_MP_TAC LIM_NULL_CMUL THEN
    MP_TAC (← MATCH_MP SERIES_TERMS_TOZERO (← SPEC (← q r"z:complex") CEXP_CONVERGES)) THEN
    GEN_REWRITE_TAC LAND_CONV [LIM_NULL_NORM] THEN
    REWRITE_TAC [COMPLEX_NORM_DIV, COMPLEX_NORM_POW, COMPLEX_NORM_CX] THEN
    REWRITE_TAC [REAL_ABS_NUM, ← GSYM LIFT_CMUL, ← GSYM real_div] THEN
    REWRITE_TAC [LIM_SEQUENTIALLY] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
    REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC)

  pure { TAYLOR_CEXP, E_APPROX_32, TAYLOR_CSIN_RAW, TAYLOR_CSIN, CSIN_CONVERGES,
         TAYLOR_CCOS_RAW, TAYLOR_CCOS, CCOS_CONVERGES }
/- ------------------------------------------------------------------------- -/
/- The argument of a complex number, where 0 <= arg(z) < 2 pi.              -/
/- (transcendentals.ml 2089-2363)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSH where
  Arg_DEF : thm
  ARG_0 : thm
  ARG : thm
  COMPLEX_NORM_EQ_1_CEXP : thm
  ARG_UNIQUE : thm
  ARG_MUL_CX : thm
  ARG_DIV_CX : thm
  ARG_LT_NZ : thm
  ARG_LE_PI : thm
  ARG_LT_PI : thm
  ARG_EQ_0 : thm
  ARG_NUM : thm
  ARG_EQ_PI : thm
  ARG_EQ_0_PI : thm
  ARG_INV : thm
  ARG_EQ : thm
  ARG_INV_EQ_0 : thm
  ARG_LE_DIV_SUM : thm
  ARG_LE_DIV_SUM_EQ : thm
  REAL_SUB_ARG : thm
  REAL_ADD_ARG : thm
  ARG_MUL : thm
  ARG_CNJ : thm
  ARG_REAL : thm
  ARG_CEXP : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSH [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) (BTSB : TSB) (BTSC : TSC) (BTSE : TSE) (BTSF : TSF) : ExceptT String IO TSH := do
  -- @@SCOPE BEGIN
  let { CEXP_ADD, CEXP_SUB, .. } := BTSA
  let { CEXP_EULER, CX_EXP, REAL_EXP_0, REAL_EXP_POS_LT, .. } := BTSB
  let { COS_0, CX_COS, CX_SIN, SIN_0, SIN_SUB, .. } := BTSC
  let { COS_NPI, COS_PI, PI_POS, PI_POS_LE, SIN_EQ_0_PI, SIN_NPI, SIN_PI, SIN_POS_PI,
        SIN_POS_PI_LE, .. } := BTSE
  let { COMPLEX_EQ_CEXP, NORM_CEXP, NORM_CEXP_II, SINCOS_TOTAL_2PI, .. } := BTSF
  let { complex_div, COMPLEX_EQ, complex_inv, COMPLEX_SQNORM, RE, .. } := D.cn.cxa
  let { COMPLEX_ADD_RID, COMPLEX_MUL_ASSOC, COMPLEX_MUL_LID, COMPLEX_MUL_LZERO,
        COMPLEX_MUL_RZERO, COMPLEX_MUL_SYM, COMPLEX_SUB_LDISTRIB, .. } := D.cn.cxb
  let { COMPLEX_ENTIRE, COMPLEX_EXPAND, COMPLEX_NORM_CX, CX_DIV, CX_INJ, CX_INV, CX_MUL,
        CX_POW, CX_SUB, IM_ADD, IM_CX, IM_MUL_CX, IM_MUL_II, RE_ADD, RE_CX, RE_MUL_CX,
        RE_MUL_II, .. } := D.cn.cxc
  let { COMPLEX_RING, .. } := D.cn.cxd
  let { COMPLEX_FIELD, COMPLEX_INV_DIV, COMPLEX_INV_MUL, .. } := D.cn.cxe
  let { COMPLEX_DIV_RMUL, COMPLEX_NORM_0, COMPLEX_NORM_DIV, COMPLEX_NORM_MUL,
        COMPLEX_NORM_NZ, COMPLEX_NORM_ZERO, .. } := D.cn.cxf
  let { CNJ_CX, COMPLEX_INV_CNJ, .. } := D.cn.cxg
  let { real, REAL_CX, REAL_IMP_CNJ, REAL_INV_EQ, REAL_MUL_CX, .. } := D.cn.cxi
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC, new_definition, REAL_ARITH,
        REAL_ARITH_TAC, REAL_FIELD, REAL_RAT_REDUCE_CONV, SELECT_CONV, .. } := D.cn.cx.cvx
  let { CONJ_ASSOC, CONTRAPOS_THM, EQ_TRANS, .. } := D.cn.cx.cvx.core1
  let { IMP_IMP, .. } := D.cn.cx.cvx.core2
  let { MONO_EXISTS, MONO_FORALL, REAL_ADD_LID, REAL_ADD_RID, REAL_ADD_SYM,
        .. } := D.cn.cx.cvx.core3
  let { REAL_LE_ADDR, REAL_LE_INV_EQ, REAL_LE_MUL_EQ, REAL_LE_REFL, REAL_LT_DIV,
        REAL_LT_IMP_NZ, REAL_LT_INV_EQ, REAL_LT_MUL, REAL_LT_MUL_EQ, REAL_LT_REFL,
        .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_LZERO, REAL_NEG_0, REAL_POS, REAL_POW_LT, REAL_SUB_LE,
        .. } := D.cn.cx.cvx.core5
  let { real_div, .. } := D.cn.cx.cvx.core6
  -- @@SCOPE END

  let Arg_DEF ← new_definition
   r"Arg z = if z = Cx(&0) then &0
            else @t. &0 <= t /\ t < &2 * pi /\
                     z = Cx(norm(z)) * cexp(ii * Cx t)"

  let ARG_0 ← prove
   r"Arg(Cx(&0)) = &0"
   (REWRITE_TAC [Arg_DEF])

  let ARG ← prove
   r"!z. &0 <= Arg(z) /\ Arg(z) < &2 * pi /\
       z = Cx(norm z) * cexp(ii * Cx(Arg z))"
   (GEN_TAC THEN REWRITE_TAC [Arg_DEF] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [COMPLEX_NORM_0, COMPLEX_MUL_LZERO] THEN
    SIMP_TAC [REAL_LE_REFL, REAL_LT_MUL, PI_POS, ← REAL_ARITH (← q r"&0 < &2")] THEN
    CONV_TAC SELECT_CONV THEN
    MP_TAC (← SPECL [← q r"Re(z) / norm z", ← q r"Im(z) / norm z"]
          SINCOS_TOTAL_2PI) THEN
    ASM_SIMP_TAC [COMPLEX_SQNORM, COMPLEX_NORM_ZERO, ← REAL_FIELD
      (← q r"~(z = &0) /\ x pow 2 + y pow 2 = z pow 2
        ==> (x / z) pow 2 + (y / z) pow 2 = &1")] THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    ASM_SIMP_TAC [COMPLEX_NORM_ZERO, ← REAL_FIELD
     (← q r"~(z = &0) ==> (x / z = y <=> x = z * y)")] THEN
    REWRITE_TAC [COMPLEX_EQ, RE_MUL_CX, IM_MUL_CX, CEXP_EULER, RE_ADD, IM_ADD,
          RE_MUL_II, IM_MUL_II, ← GSYM CX_SIN, ← GSYM CX_COS, RE_CX, IM_CX] THEN
    REAL_ARITH_TAC)

  let COMPLEX_NORM_EQ_1_CEXP ← prove
   r"!z. norm z = &1 <=> (?t. z = cexp(ii * Cx t))"
   (GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [NORM_CEXP, RE_MUL_II, IM_CX, REAL_NEG_0, REAL_EXP_0] THEN
    MP_TAC (← SPEC (← q r"z:complex") ARG) THEN ASM_REWRITE_TAC [COMPLEX_MUL_LID] THEN
    MESON_TAC [])

  let ARG_UNIQUE ← prove
   r"!a r z. &0 < r /\ Cx r * cexp(ii * Cx a) = z /\ &0 <= a /\ a < &2 * pi
           ==> Arg z = a"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM CX_INJ] THEN
    MATCH_MP_TAC (← ExceptT.mk (COMPLEX_RING (← q r"ii * x = ii * y ==> x = y"))) THEN
    MATCH_MP_TAC COMPLEX_EQ_CEXP THEN CONJ_TAC THENL
     [REWRITE_TAC [IM_MUL_II, RE_CX] THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"&0 <= x /\ x < p /\ &0 <= y /\ y < p
                               ==> abs(x - y) < p")) THEN
      ASM_SIMP_TAC [ARG],
      MATCH_MP_TAC (← ExceptT.mk (COMPLEX_RING
       (← q r"!a b. Cx a = Cx b /\ ~(Cx b = Cx(&0)) /\
              Cx a * w = Cx b * z ==> w = z"))) THEN
      MAP_EVERY EXISTS_TAC [← q r"norm(z:complex)", ← q r"r:real"] THEN
      ASM_REWRITE_TAC [← GSYM ARG] THEN ASM_SIMP_TAC [CX_INJ, REAL_LT_IMP_NZ] THEN
      EXPAND_TAC "z" THEN
      REWRITE_TAC [NORM_CEXP_II, COMPLEX_NORM_MUL, COMPLEX_NORM_CX] THEN
      ASM_REAL_ARITH_TAC])

  let ARG_MUL_CX ← prove
   r"!r z. &0 < r ==> Arg(Cx r * z) = Arg(z)"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"z = Cx(&0)") THEN ASM_REWRITE_TAC [COMPLEX_MUL_RZERO] THEN
    MATCH_MP_TAC ARG_UNIQUE THEN EXISTS_TAC (← q r"r * norm(z:complex)") THEN
    ASM_REWRITE_TAC [CX_MUL, ← GSYM COMPLEX_MUL_ASSOC, ← GSYM ARG] THEN
    ASM_SIMP_TAC [REAL_LT_MUL, COMPLEX_NORM_NZ])

  let ARG_DIV_CX ← prove
   r"!r z. &0 < r ==> Arg(z / Cx r) = Arg(z)"
   (REWRITE_TAC [← ONCE_REWRITE_RULE [COMPLEX_MUL_SYM] complex_div] THEN
    SIMP_TAC [← GSYM CX_INV, ARG_MUL_CX, REAL_LT_INV_EQ])

  let ARG_LT_NZ ← prove
   r"!z. &0 < Arg z <=> ~(Arg z = &0)"
   (MP_TAC ARG THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC)

  let ARG_LE_PI ← prove
   r"!z. Arg z <= pi <=> &0 <= Im z"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"z = Cx(&0)") THENL
     [ASM_REWRITE_TAC [Arg_DEF, IM_CX, REAL_LE_REFL, PI_POS_LE], ALL_TAC] THEN
    GEN_REWRITE_TAC (funpow 3 RAND_CONV) [ARG] THEN
    ASM_SIMP_TAC [IM_MUL_CX, CEXP_EULER, REAL_LE_MUL_EQ, COMPLEX_NORM_NZ] THEN
    REWRITE_TAC [IM_ADD, ← GSYM CX_SIN, ← GSYM CX_COS, IM_CX, IM_MUL_II, RE_CX] THEN
    REWRITE_TAC [REAL_ADD_LID] THEN EQ_TAC THEN SIMP_TAC [ARG, SIN_POS_PI_LE] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"&0 < sin(&2 * pi - Arg z)") MP_TAC THENL
     [MATCH_MP_TAC SIN_POS_PI THEN MP_TAC (← SPEC (← q r"z:complex") ARG) THEN
      ASM_REAL_ARITH_TAC,
      REWRITE_TAC [SIN_SUB, SIN_NPI, COS_NPI] THEN REAL_ARITH_TAC])

  let ARG_LT_PI ← prove
   r"!z. &0 < Arg z /\ Arg z < pi <=> &0 < Im z"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"z = Cx(&0)") THENL
     [ASM_REWRITE_TAC [Arg_DEF, IM_CX, REAL_LT_REFL, PI_POS_LE], ALL_TAC] THEN
    GEN_REWRITE_TAC (funpow 3 RAND_CONV) [ARG] THEN
    ASM_SIMP_TAC [IM_MUL_CX, CEXP_EULER, REAL_LT_MUL_EQ, COMPLEX_NORM_NZ] THEN
    REWRITE_TAC [IM_ADD, ← GSYM CX_SIN, ← GSYM CX_COS, IM_CX, IM_MUL_II, RE_CX] THEN
    REWRITE_TAC [REAL_ADD_LID] THEN EQ_TAC THEN SIMP_TAC [SIN_POS_PI] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    ASM_CASES_TAC (← q r"Arg z = &0") THEN
    ASM_REWRITE_TAC [SIN_0, REAL_LT_REFL] THEN
    ASM_SIMP_TAC [ARG, ← REAL_ARITH (← q r"~(x = &0) ==> (&0 < x <=> &0 <= x)")] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN (← q r"&0 <= sin(&2 * pi - Arg z)") MP_TAC THENL
     [MATCH_MP_TAC SIN_POS_PI_LE THEN MP_TAC (← SPEC (← q r"z:complex") ARG) THEN
      ASM_REAL_ARITH_TAC,
      REWRITE_TAC [SIN_SUB, SIN_NPI, COS_NPI] THEN REAL_ARITH_TAC])

  let ARG_EQ_0 ← prove
   r"!z. Arg z = &0 <=> real z /\ &0 <= Re z"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"z = Cx(&0)") THENL
     [ASM_REWRITE_TAC [REAL_CX, RE_CX, Arg_DEF, REAL_LE_REFL], ALL_TAC] THEN
    CONV_TAC (RAND_CONV (SUBS_CONV
      [← liftExcept (last (CONJUNCTS (← SPEC (← q r"z:complex") ARG)))])) THEN
    ASM_SIMP_TAC [RE_MUL_CX, REAL_MUL_CX, REAL_LE_MUL_EQ, COMPLEX_NORM_NZ] THEN
    ASM_REWRITE_TAC [COMPLEX_NORM_ZERO, CEXP_EULER] THEN
    REWRITE_TAC [real, RE_ADD, IM_ADD, RE_MUL_II, IM_MUL_II,
                 ← GSYM CX_SIN, ← GSYM CX_COS, RE_CX, IM_CX] THEN
    REWRITE_TAC [REAL_ADD_RID, REAL_ADD_LID, REAL_NEG_0] THEN
    EQ_TAC THEN SIMP_TAC [SIN_0, COS_0, REAL_POS] THEN
    ASM_CASES_TAC (← q r"Arg z = pi") THENL
     [ASM_REWRITE_TAC [COS_PI] THEN REAL_ARITH_TAC, ALL_TAC] THEN
    MP_TAC (← SPEC (← q r"z:complex") ARG) THEN REWRITE_TAC [CONJ_ASSOC] THEN
    DISCH_THEN (MP_TAC o CONJUNCT1) THEN DISCH_THEN (STRIP_ASSUME_TAC o MATCH_MP
     (← REAL_ARITH (← q r"&0 <= x /\ x < &2 * pi
                  ==> --pi < x /\ x < pi \/ --pi < x - pi /\ x - pi < pi"))) THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [SIN_EQ_0_PI] THEN
    UNDISCH_TAC (← q r"~(Arg z = pi)") THEN ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    DISCH_TAC THEN REWRITE_TAC [← REAL_ARITH (← q r"x = pi <=> x - pi = &0")] THEN
    MATCH_MP_TAC SIN_EQ_0_PI THEN ASM_REWRITE_TAC [SIN_SUB, SIN_PI] THEN
    REAL_ARITH_TAC)

  let ARG_NUM ← prove
   r"!n. Arg(Cx(&n)) = &0"
   (REWRITE_TAC [ARG_EQ_0, REAL_CX, RE_CX, REAL_POS])

  let ARG_EQ_PI ← prove
   r"!z. Arg z = pi <=> real z /\ Re z < &0"
   (SIMP_TAC [ARG, PI_POS, ← REAL_ARITH
      (← q r"&0 < pi /\ &0 <= z
       ==> (z = pi <=> z <= pi /\ ~(z = &0) /\ ~(&0 < z /\ z < pi))")] THEN
    REWRITE_TAC [ARG_EQ_0, ARG, ARG_LT_PI, ARG_LE_PI, real] THEN
    REAL_ARITH_TAC)

  let ARG_EQ_0_PI ← prove
   r"!z. Arg z = &0 \/ Arg z = pi <=> real z"
   (REWRITE_TAC [ARG_EQ_0, ARG_EQ_PI, real] THEN REAL_ARITH_TAC)

  let ARG_INV ← prove
   r"!z. ~(real z /\ &0 <= Re z) ==> Arg(inv z) = &2 * pi - Arg z"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"z = Cx(&0)") THEN
    ASM_REWRITE_TAC [REAL_CX, RE_CX, REAL_LE_REFL] THEN
    REWRITE_TAC [real] THEN STRIP_TAC THEN MATCH_MP_TAC ARG_UNIQUE THEN
    EXISTS_TAC (← q r"inv(norm(z:complex))") THEN
    ASM_SIMP_TAC [COMPLEX_NORM_NZ, REAL_LT_INV_EQ] THEN
    REWRITE_TAC [CX_SUB, CX_MUL, COMPLEX_SUB_LDISTRIB, CEXP_SUB] THEN
    SUBST1_TAC (← SPEC (← q r"Cx(&2) * Cx pi") CEXP_EULER) THEN
    REWRITE_TAC [← GSYM CX_MUL, ← GSYM CX_SIN, ← GSYM CX_COS] THEN
    REWRITE_TAC [SIN_NPI, COS_NPI, COMPLEX_MUL_RZERO, COMPLEX_ADD_RID] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [complex_div, COMPLEX_MUL_LID, CX_INV, ← GSYM COMPLEX_INV_MUL] THEN
    REWRITE_TAC [← GSYM ARG] THEN
    MP_TAC (← SPEC (← q r"z:complex") ARG_EQ_0) THEN ASM_REWRITE_TAC [real] THEN
    MP_TAC (← SPEC (← q r"z:complex") ARG) THEN REAL_ARITH_TAC)

  let ARG_EQ ← prove
   r"!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> (Arg w = Arg z <=> ?x. &0 < x /\ w = Cx(x) * z)"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ALL_TAC, STRIP_TAC THEN ASM_SIMP_TAC [ARG_MUL_CX]] THEN
    DISCH_TAC THEN
    MAP_EVERY (MP_TAC o CONJUNCT2 o CONJUNCT2 o C SPEC ARG)
     [← q r"z:complex", ← q r"w:complex"] THEN
    ASM_REWRITE_TAC [IMP_IMP] THEN
    DISCH_THEN (fun th => CONV_TAC (SUBS_CONV (CONJUNCTS th))) THEN
    EXISTS_TAC (← q r"norm(w:complex) / norm(z:complex)") THEN
    ASM_SIMP_TAC [REAL_LT_DIV, COMPLEX_NORM_NZ, CX_DIV] THEN
    REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC [COMPLEX_DIV_RMUL, COMPLEX_NORM_ZERO, CX_INJ])

  let ARG_INV_EQ_0 ← prove
   r"!z. Arg(inv z) = &0 <=> Arg z = &0"
   (GEN_TAC THEN REWRITE_TAC [ARG_EQ_0, REAL_INV_EQ] THEN
    MATCH_MP_TAC (← TAUT (← q r"(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)")) THEN
    REWRITE_TAC [real] THEN DISCH_TAC THEN ASM_REWRITE_TAC [complex_inv, RE] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [REAL_ADD_RID] THEN
    ASM_CASES_TAC (← q r"Re z = &0") THEN ASM_REWRITE_TAC [real_div, REAL_MUL_LZERO] THEN
    ASM_SIMP_TAC [← REAL_FIELD (← q r"~(x = &0) ==> x * inv(x pow 2) = inv x")] THEN
    REWRITE_TAC [REAL_LE_INV_EQ])

  let ARG_LE_DIV_SUM ← prove
   r"!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0)) /\ Arg(w) <= Arg(z)
         ==> Arg(z) = Arg(w) + Arg(z / w)"
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"a:real = b + c <=> c = a - b")] THEN
    MATCH_MP_TAC ARG_UNIQUE THEN EXISTS_TAC (← q r"norm(z / w)") THEN
    ASM_SIMP_TAC [ARG, ← REAL_ARITH
     (← q r"&0 <= a /\ a < &2 * pi /\ &0 <= b /\ b <= a ==> a - b < &2 * pi")] THEN
    ASM_REWRITE_TAC [REAL_SUB_LE] THEN
    ASM_SIMP_TAC [COMPLEX_NORM_DIV, CX_DIV] THEN
    ASM_SIMP_TAC [REAL_LT_DIV, COMPLEX_NORM_NZ] THEN
    REWRITE_TAC [COMPLEX_SUB_LDISTRIB, CEXP_SUB, CX_SUB] THEN
    REWRITE_TAC [complex_div] THEN
    ONCE_REWRITE_TAC [← ExceptT.mk (COMPLEX_RING
     (← q r"(a * b) * (c * d):complex = (a * c) * (b * d)"))] THEN
    REWRITE_TAC [← GSYM COMPLEX_INV_MUL] THEN ASM_SIMP_TAC [← GSYM ARG])

  let ARG_LE_DIV_SUM_EQ ← prove
   r"!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> (Arg(w) <= Arg(z) <=> Arg(z) = Arg(w) + Arg(z / w))"
   (MESON_TAC [ARG_LE_DIV_SUM, REAL_LE_ADDR, ARG])

  let REAL_SUB_ARG ← prove
   r"!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> Arg w - Arg z = if Arg(z) <= Arg(w) then Arg(w / z)
                             else Arg(w / z) - &2 * pi"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
     [MP_TAC (← ISPECL [← q r"z:complex", ← q r"w:complex"] ARG_LE_DIV_SUM) THEN
      ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC,
      MP_TAC (← ISPECL [← q r"w:complex", ← q r"z:complex"] ARG_LE_DIV_SUM) THEN
      ASM_REWRITE_TAC [] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC, DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"a - (a + b):real = --b")] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [← GSYM COMPLEX_INV_DIV] THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"x = &2 * pi - y ==> --x = y - &2 * pi")) THEN
      MATCH_MP_TAC ARG_INV THEN REWRITE_TAC [← GSYM ARG_EQ_0] THEN
      ONCE_REWRITE_TAC [← GSYM COMPLEX_INV_DIV] THEN
      REWRITE_TAC [ARG_INV_EQ_0] THEN
      MP_TAC (← ISPECL [← q r"w:complex", ← q r"z:complex"] ARG_LE_DIV_SUM) THEN
      ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC])

  let REAL_ADD_ARG ← prove
   r"!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> Arg(w) + Arg(z) =
             if Arg w + Arg z < &2 * pi
             then Arg(w * z)
             else Arg(w * z) + &2 * pi"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"w * z:complex", ← q r"z:complex"] REAL_SUB_ARG) THEN
    MP_TAC (← SPECL [← q r"z:complex", ← q r"w * z:complex"] ARG_LE_DIV_SUM_EQ) THEN
    ASM_SIMP_TAC [COMPLEX_ENTIRE, ← ExceptT.mk (COMPLEX_FIELD
     (← q r"~(z = Cx(&0)) ==> (w * z) / z = w"))] THEN
    ASM_CASES_TAC (← q r"Arg (w * z) = Arg z + Arg w") THEN ASM_REWRITE_TAC [] THENL
     [ASM_MESON_TAC [ARG, REAL_ADD_SYM],
      SIMP_TAC [← REAL_ARITH (← q r"wz - z = w - &2 * pi <=> w + z = wz + &2 * pi")] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"w + p < p <=> ~(&0 <= w)"), ARG]])

  let ARG_MUL ← prove
   r"!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> Arg(w * z) = if Arg w + Arg z < &2 * pi
                          then Arg w + Arg z
                          else (Arg w + Arg z) - &2 * pi"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP REAL_ADD_ARG) THEN
    REAL_ARITH_TAC)

  let ARG_CNJ ← prove
   r"!z. Arg(cnj z) = if real z /\ &0 <= Re z then Arg z else &2 * pi - Arg z"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"z = Cx(&0)") THEN
    ASM_REWRITE_TAC [CNJ_CX, ARG_0, REAL_CX, RE_CX, REAL_LE_REFL] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [REAL_IMP_CNJ] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"Arg(inv z)") THEN CONJ_TAC THENL
     [REWRITE_TAC [COMPLEX_INV_CNJ] THEN
      ASM_SIMP_TAC [← GSYM CX_POW, ARG_DIV_CX, REAL_POW_LT, COMPLEX_NORM_NZ],
      ASM_SIMP_TAC [ARG_INV]])

  let ARG_REAL ← prove
   r"!z. real z ==> Arg z = if &0 <= Re z then &0 else pi"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [ARG_EQ_PI, ARG_EQ_0] THEN ASM_REAL_ARITH_TAC)

  let ARG_CEXP ← prove
   r"!z. &0 <= Im z /\ Im z < &2 * pi ==> Arg(cexp(z)) = Im z"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC ARG_UNIQUE THEN
    EXISTS_TAC (← q r"exp(Re z)") THEN
    ASM_REWRITE_TAC [CX_EXP, ← GSYM CEXP_ADD, REAL_EXP_POS_LT] THEN
    REWRITE_TAC [← GSYM COMPLEX_EXPAND])

  pure { Arg_DEF, ARG_0, ARG, COMPLEX_NORM_EQ_1_CEXP, ARG_UNIQUE, ARG_MUL_CX, ARG_DIV_CX,
         ARG_LT_NZ, ARG_LE_PI, ARG_LT_PI, ARG_EQ_0, ARG_NUM, ARG_EQ_PI, ARG_EQ_0_PI,
         ARG_INV, ARG_EQ, ARG_INV_EQ_0, ARG_LE_DIV_SUM, ARG_LE_DIV_SUM_EQ, REAL_SUB_ARG,
         REAL_ADD_ARG, ARG_MUL, ARG_CNJ, ARG_REAL, ARG_CEXP }
/- ------------------------------------------------------------------------- -/
/- Properties of 2-D rotations, and their interpretation using cexp.        -/
/- (transcendentals.ml 2364-2633)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSI where
  rotate2d : thm
  LINEAR_ROTATE2D : thm
  ROTATE2D_ADD_VECTORS : thm
  ROTATE2D_SUB : thm
  NORM_ROTATE2D : thm
  ROTATE2D_0 : thm
  ROTATE2D_EQ_0 : thm
  ROTATE2D_ZERO : thm
  ORTHOGONAL_TRANSFORMATION_ROTATE2D : thm
  ROTATE2D_POLAR : thm
  MATRIX_ROTATE2D : thm
  DET_MATRIX_ROTATE2D : thm
  ROTATION_ROTATE2D : thm
  ROTATE2D_ADD : thm
  ROTATE2D_COMPLEX : thm
  ROTATE2D_PI2 : thm
  ROTATE2D_PI : thm
  ROTATE2D_NPI : thm
  ROTATE2D_2PI : thm
  ARG_ROTATE2D : thm
  ARG_ROTATE2D_UNIQUE : thm
  ARG_ROTATE2D_UNIQUE_2PI : thm
  COMPLEX_DIV_ROTATION : thm
  ROTATION_ROTATE2D_EXISTS_GEN : thm
  ROTATION_ROTATE2D_EXISTS : thm
  ROTATION_ROTATE2D_EXISTS_ORTHOGONAL : thm
  ROTATION_ROTATE2D_EXISTS_ORTHOGONAL_ORIENTED : thm
  ROTATE2D_EQ : thm
  ROTATE2D_SUB_ARG : thm
  ROTATION_MATRIX_ROTATE2D : thm
  ROTATION_MATRIX_ROTATE2D_EQ : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSI [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) (BTSB : TSB) (BTSC : TSC) (BTSE : TSE) (BTSF : TSF) (BTSH : TSH) : ExceptT String IO TSI := do
  -- @@SCOPE BEGIN
  let { CEXP_ADD, CEXP_NZ, .. } := BTSA
  let { CEXP_EULER, REAL_EXP_0, REAL_EXP_NEG, .. } := BTSB
  let { COS_0, COS_ADD, COS_NEG, CX_COS, CX_SIN, EULER, SIN_0, SIN_ADD, SIN_CIRCLE,
        SIN_NEG, .. } := BTSC
  let { COS_NPI, COS_PI, COS_PI2, PI_POS, SIN_NPI, SIN_PI, SIN_PI2, .. } := BTSE
  let { CEXP_EQ, SIN_COS_EQ, SIN_COS_INJ, SINCOS_TOTAL_2PI, .. } := BTSF
  let { ARG, ARG_UNIQUE, REAL_SUB_ARG, .. } := BTSH
  let { LINEAR_EQ_MATRIX, NORM_EQ_1, .. } := D.qvectors
  let { ROTATION_EXISTS, .. } := D.qdeterminants
  let { complex_div, complex_mul, IM, IM_DEF, RE, RE_DEF, .. } := D.cn.cxa
  let { COMPLEX_ADD_LDISTRIB, COMPLEX_ADD_RID, COMPLEX_MUL_AC, COMPLEX_MUL_LID,
        COMPLEX_MUL_RZERO, COMPLEX_NEG_0, .. } := D.cn.cxb
  let { CX_ADD, CX_INJ, CX_NEG, CX_POW, CX_SUB, IM_ADD, IM_CX, IM_MUL_II, RE_ADD, RE_CX,
        RE_MUL_II, .. } := D.cn.cxc
  let { COMPLEX_RING, .. } := D.cn.cxd
  let { COMPLEX_FIELD, COMPLEX_INV_MUL, .. } := D.cn.cxe
  let { COMPLEX_NORM_0, COMPLEX_NORM_NZ, COMPLEX_NORM_ZERO, .. } := D.cn.cxf
  let { ROTATION_MATRIX_2, .. } := D.cn.qdeterminants
  let { DET_2, .. } := D.cn.ms.qdet
  let { mat, .. } := D.cn.ms.qvec
  let { add_linear_invariants, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC,
        new_definition, REAL_ARITH, REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV, REAL_RING,
        .. } := D.cn.cx.cvx
  let { FORALL_2, REAL_LE_SQUARE, real_sub, REAL_SUB_LZERO, SUM_2, VECTOR_2,
        .. } := D.cn.cx.cpx
  let { INTEGER_CLOSED, .. } := D.cn.ms.ig.qfloor
  let { ARITH, CART_EQ, CONJ_ASSOC, CONTRAPOS_THM, DIMINDEX_2, .. } := D.cn.cx.cvx.core1
  let { FUN_EQ_THM, .. } := D.cn.cx.cvx.core2
  let { LAMBDA_BETA, LE_REFL, LEFT_IMP_EXISTS_THM, MONO_AND, MONO_EXISTS, REAL_ADD_RID,
        REAL_ADD_SYM, .. } := D.cn.cx.cvx.core3
  let { REAL_LE_ADD, REAL_LE_REFL, REAL_LT_MUL, .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_RID, REAL_MUL_RZERO, REAL_MUL_SYM, REAL_NOT_LE, REAL_OF_NUM_LT,
        REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB, REAL_SUB_RZERO, .. } := D.cn.cx.cvx.core5
  let { DOT_2, .. } := D.cn.cx.cvx.vec1
  let { LINEAR_ADD, LINEAR_CMUL, LINEAR_SUB, MATRIX_EQ, MATRIX_WORKS, NORM_EQ,
        .. } := D.cn.cx.cvx.vec2
  let { NORM_MUL, REAL_ABS_NORM, .. } := D.cn.cx.cvx.vec3
  let { linear, matrix_mul, matrix_vector_mul, orthogonal, VECTOR_ADD_COMPONENT,
        VECTOR_MUL_COMPONENT, VECTOR_MUL_LCANCEL, .. } := D.cn.cx.cvx.vec4
  let { orthogonal_matrix, ORTHOGONAL_TRANSFORMATION, ORTHOGONAL_TRANSFORMATION_INJECTIVE,
        ORTHOGONAL_TRANSFORMATION_MATRIX, .. } := D.cn.cx.cvx.det
  let { transp, .. } := D.cn.ms.ig.dv.qvec
  -- @@SCOPE END

  let rotate2d ← new_definition
   r"(rotate2d:real->real^2->real^2) t x =
          vector[x$1 * cos(t) - x$2 * sin(t);
                 x$1 * sin(t) + x$2 * cos(t)]"

  let LINEAR_ROTATE2D ← prove
   r"!t. linear(rotate2d t)"
   (SIMP_TAC [linear, CART_EQ, DIMINDEX_2, FORALL_2, VECTOR_2,
              VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, rotate2d] THEN
    REAL_ARITH_TAC)

  let ROTATE2D_ADD_VECTORS ← prove
   r"!t w z. rotate2d t (w + z) = rotate2d t w + rotate2d t z"
   (SIMP_TAC [LINEAR_ADD, LINEAR_ROTATE2D])

  let ROTATE2D_SUB ← prove
   r"!t w z. rotate2d t (w - z) = rotate2d t w - rotate2d t z"
   (SIMP_TAC [LINEAR_SUB, LINEAR_ROTATE2D])

  let NORM_ROTATE2D ← prove
   r"!t z. norm(rotate2d t z) = norm z"
   (REWRITE_TAC [NORM_EQ, rotate2d, DIMINDEX_2, DOT_2, VECTOR_2] THEN
    REPEAT GEN_TAC THEN MP_TAC (← ISPEC (← q r"t:real") SIN_CIRCLE) THEN
    CONV_TAC (fun t => REAL_RING t))

  let ROTATE2D_0 ← prove
   r"!t. rotate2d t (Cx(&0)) = Cx(&0)"
   (REWRITE_TAC [← GSYM COMPLEX_NORM_ZERO, NORM_ROTATE2D, COMPLEX_NORM_0])

  let ROTATE2D_EQ_0 ← prove
   r"!t z. rotate2d t z = Cx(&0) <=> z = Cx(&0)"
   (REWRITE_TAC [← GSYM COMPLEX_NORM_ZERO, NORM_ROTATE2D])

  let ROTATE2D_ZERO ← prove
   r"!z. rotate2d (&0) z = z"
   (REWRITE_TAC [rotate2d, SIN_0, COS_0] THEN
    REWRITE_TAC [CART_EQ, DIMINDEX_2, FORALL_2, VECTOR_2] THEN
    REAL_ARITH_TAC)

  let ORTHOGONAL_TRANSFORMATION_ROTATE2D ← prove
   r"!t. orthogonal_transformation(rotate2d t)"
   (REWRITE_TAC [ORTHOGONAL_TRANSFORMATION, LINEAR_ROTATE2D, NORM_ROTATE2D])

  let ROTATE2D_POLAR ← prove
   r"!r t s. rotate2d t (vector[r * cos(s); r * sin(s)]) =
                        vector[r * cos(t + s); r * sin(t + s)]"
   (SIMP_TAC [rotate2d, DIMINDEX_2, VECTOR_2, CART_EQ, FORALL_2] THEN
    REWRITE_TAC [SIN_ADD, COS_ADD] THEN REAL_ARITH_TAC)

  let MATRIX_ROTATE2D ← prove
   r"!t. matrix(rotate2d t) = vector[vector[cos t;--(sin t)];
                                   vector[sin t; cos t]]"
   (SIMP_TAC [MATRIX_EQ, MATRIX_WORKS, LINEAR_ROTATE2D] THEN
    SIMP_TAC [matrix_vector_mul, rotate2d, CART_EQ, DIMINDEX_2, FORALL_2,
              LAMBDA_BETA, VECTOR_2, ARITH, SUM_2] THEN
    REAL_ARITH_TAC)

  let DET_MATRIX_ROTATE2D ← prove
   r"!t. det(matrix(rotate2d t)) = &1"
   (GEN_TAC THEN REWRITE_TAC [MATRIX_ROTATE2D, DET_2, VECTOR_2] THEN
    MP_TAC (← SPEC (← q r"t:real") SIN_CIRCLE) THEN REAL_ARITH_TAC)

  let ROTATION_ROTATE2D ← prove
   r"!f. orthogonal_transformation f /\ det(matrix f) = &1
       ==> ?t. &0 <= t /\ t < &2 * pi /\ f = rotate2d t"
   (REWRITE_TAC [ORTHOGONAL_TRANSFORMATION_MATRIX] THEN
    REWRITE_TAC [matrix_mul, orthogonal_matrix, transp] THEN
    SIMP_TAC [DIMINDEX_2, SUM_2, FORALL_2, LAMBDA_BETA, ARITH,
              CART_EQ, mat, DET_2] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(matrix f)$1$1 pow 2 + (matrix f)$2$1 pow 2 = &1 /\
                  (matrix f)$1$2 = --((matrix f)$2$1) /\
                  (matrix f:real^2^2)$2$2 = (matrix f)$1$1")
    STRIP_ASSUME_TAC THENL
     [REPEAT (FIRST_X_ASSUM (MP_TAC o SYM)) THEN CONV_TAC (fun t => REAL_RING t),
      FIRST_X_ASSUM (MP_TAC o MATCH_MP SINCOS_TOTAL_2PI) THEN
      MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC LINEAR_EQ_MATRIX THEN
      ASM_REWRITE_TAC [LINEAR_ROTATE2D, MATRIX_ROTATE2D] THEN
      ASM_SIMP_TAC [CART_EQ, DIMINDEX_2, FORALL_2, VECTOR_2]])

  let ROTATE2D_ADD ← prove
   r"!s t x. rotate2d (s + t) x = rotate2d s (rotate2d t x)"
   (SIMP_TAC [CART_EQ, rotate2d, LAMBDA_BETA, DIMINDEX_2, ARITH,
              FORALL_2, VECTOR_2] THEN
    REWRITE_TAC [SIN_ADD, COS_ADD] THEN REAL_ARITH_TAC)

  let ROTATE2D_COMPLEX ← prove
   r"!t z. rotate2d t z = cexp(ii * Cx t) * z"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [complex_mul] THEN
    REWRITE_TAC [CEXP_EULER, rotate2d, ← GSYM CX_SIN, ← GSYM CX_COS,
                 RE_ADD, IM_ADD, RE_MUL_II, IM_MUL_II, IM_CX, RE_CX] THEN
    REWRITE_TAC [CART_EQ, FORALL_2, VECTOR_2, DIMINDEX_2] THEN
    REWRITE_TAC [← GSYM RE_DEF, ← GSYM IM_DEF, RE, IM] THEN
    REAL_ARITH_TAC)

  let ROTATE2D_PI2 ← prove
   r"!z. rotate2d (pi / &2) z = ii * z"
   (REWRITE_TAC [ROTATE2D_COMPLEX, CEXP_EULER, SIN_PI2, COS_PI2, ← GSYM CX_SIN,
                 ← GSYM CX_COS] THEN
    CONV_TAC COMPLEX_RING)

  let ROTATE2D_PI ← prove
   r"!z. rotate2d pi z = --z"
   (REWRITE_TAC [ROTATE2D_COMPLEX, CEXP_EULER, SIN_PI, COS_PI, ← GSYM CX_SIN,
                 ← GSYM CX_COS] THEN
    CONV_TAC COMPLEX_RING)

  let ROTATE2D_NPI ← prove
   r"!n z. rotate2d (&n * pi) z = --Cx(&1) pow n * z"
   (REWRITE_TAC [ROTATE2D_COMPLEX, CEXP_EULER, SIN_NPI, COS_NPI, ← GSYM CX_SIN,
                 ← GSYM CX_COS, CX_NEG, CX_POW] THEN
    CONV_TAC COMPLEX_RING)

  let ROTATE2D_2PI ← prove
   r"!z. rotate2d (&2 * pi) z = z"
   (REWRITE_TAC [ROTATE2D_NPI] THEN CONV_TAC COMPLEX_RING)

  let ARG_ROTATE2D ← prove
   r"!t z. ~(z = Cx(&0)) /\ &0 <= t + Arg z /\ t + Arg z < &2 * pi
         ==> Arg(rotate2d t z) = t + Arg z"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC ARG_UNIQUE THEN
    EXISTS_TAC (← q r"norm(z:complex)") THEN
    ASM_SIMP_TAC [ARG, ROTATE2D_COMPLEX, REAL_LE_ADD, COMPLEX_NORM_NZ] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ARG] THEN
    REWRITE_TAC [CX_ADD, COMPLEX_ADD_LDISTRIB, CEXP_ADD] THEN
    REWRITE_TAC [COMPLEX_MUL_AC])

  let ARG_ROTATE2D_UNIQUE ← prove
   r"!t a z. ~(z = Cx(&0)) /\ Arg(rotate2d t z) = a
           ==> ?n. integer n /\ t = &2 * n * pi + (a - Arg z)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← liftExcept (last (CONJUNCTS (← ISPEC (← q r"rotate2d t z") ARG)))) THEN
    ASM_REWRITE_TAC [NORM_ROTATE2D] THEN
    REWRITE_TAC [ROTATE2D_COMPLEX] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [ARG] THEN
    ASM_REWRITE_TAC [← ExceptT.mk (COMPLEX_RING
       (← q r"a * z * b = z * c <=> z = Cx(&0) \/ a * b = c")),
                     CX_INJ, COMPLEX_NORM_ZERO, ← GSYM CEXP_ADD, CEXP_EQ] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_AND THEN
    REWRITE_TAC [← GSYM CX_ADD, ← GSYM CX_SUB, CX_INJ, ← ExceptT.mk (COMPLEX_RING
     (← q r"ii * t + ii * z = ii * a + n * ii <=> t = n + (a - z)"))])

  let ARG_ROTATE2D_UNIQUE_2PI ← prove
   r"!s t z. ~(z = Cx(&0)) /\
           &0 <= s /\ s < &2 * pi /\ &0 <= t /\ t < &2 * pi /\
           Arg(rotate2d s z) = Arg(rotate2d t z)
           ==> s = t"
   (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"a = Arg(rotate2d t z)") THEN
    MP_TAC (← ISPECL [← q r"s:real", ← q r"a:real", ← q r"z:complex"] ARG_ROTATE2D_UNIQUE) THEN
    MP_TAC (← ISPECL [← q r"t:real", ← q r"a:real", ← q r"z:complex"] ARG_ROTATE2D_UNIQUE) THEN
    ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SIN_COS_INJ THEN
    REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC [SIN_COS_EQ, ← REAL_RING
       (← q r"x + az:real = (y + az) + z <=> x - y = z")] THEN
      REWRITE_TAC [← GSYM REAL_SUB_LDISTRIB, ← GSYM REAL_SUB_RDISTRIB] THEN
      ASM_MESON_TAC [INTEGER_CLOSED],
      ASM_REAL_ARITH_TAC])

  let COMPLEX_DIV_ROTATION ← prove
   r"!f w z. orthogonal_transformation f /\ det(matrix f) = &1
           ==> f w / f z = w / z"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP ROTATION_ROTATE2D) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:real") STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [ROTATE2D_COMPLEX] THEN
    SIMP_TAC [complex_div, COMPLEX_INV_MUL, CEXP_NZ, ← ExceptT.mk (COMPLEX_FIELD
     (← q r"~(a = Cx(&0)) ==> (a * w) * (inv a * z) = w * z"))])

  let th ← prove
   r"!f w z. linear f /\ (!x. norm(f x) = norm x) /\
             (2 <= dimindex(:2) ==> det(matrix f) = &1)
             ==> f w / f z = w / z"
   (REWRITE_TAC [CONJ_ASSOC, ← GSYM ORTHOGONAL_TRANSFORMATION,
                 DIMINDEX_2, LE_REFL, COMPLEX_DIV_ROTATION])
  add_linear_invariants [th]

  let th ← prove
   r"!f t z. linear f /\ (!x. norm(f x) = norm x) /\
             (2 <= dimindex(:2) ==> det(matrix f) = &1)
             ==> rotate2d t (f z) = f(rotate2d t z)"
   (REWRITE_TAC [DIMINDEX_2, LE_REFL] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"f:complex->complex") ROTATION_ROTATE2D) THEN
    ASM_REWRITE_TAC [ORTHOGONAL_TRANSFORMATION] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"s:real") STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [← GSYM ROTATE2D_ADD] THEN REWRITE_TAC [REAL_ADD_SYM])
  add_linear_invariants [th]

  let ROTATION_ROTATE2D_EXISTS_GEN ← prove
   r"!x y. ?t. &0 <= t /\ t < &2 * pi /\ norm(y) % rotate2d t x = norm(x) % y"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"norm(y:real^2) % x:real^2", ← q r"norm(x:real^2) % y:real^2"]
                 ROTATION_EXISTS) THEN
    ASM_REWRITE_TAC [DIMINDEX_2, NORM_MUL, ARITH, REAL_ABS_NORM,
                     ← EQT_INTRO (← SPEC_ALL REAL_MUL_SYM), CONJ_ASSOC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"f:real^2->real^2")
      (CONJUNCTS_THEN ASSUME_TAC)) THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP ROTATION_ROTATE2D) THEN
    MATCH_MP_TAC MONO_EXISTS THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [LINEAR_CMUL, LINEAR_ROTATE2D])

  let ROTATION_ROTATE2D_EXISTS ← prove
   r"!x y. norm x = norm y ==> ?t. &0 <= t /\ t < &2 * pi /\ rotate2d t x = y"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"norm(y:complex) = &0") THENL
     [ASM_REWRITE_TAC [] THEN DISCH_TAC THEN EXISTS_TAC (← q r"&0") THEN
      SIMP_TAC [REAL_LT_MUL, PI_POS, REAL_OF_NUM_LT, ARITH, REAL_LE_REFL] THEN
      ASM_MESON_TAC [COMPLEX_NORM_ZERO, ROTATE2D_0],
      DISCH_TAC THEN
      MP_TAC (← ISPECL [← q r"x:complex", ← q r"y:complex"] ROTATION_ROTATE2D_EXISTS_GEN) THEN
      ASM_REWRITE_TAC [VECTOR_MUL_LCANCEL]])

  let ROTATION_ROTATE2D_EXISTS_ORTHOGONAL ← prove
   r"!e1 e2. norm(e1) = &1 /\ norm(e2) = &1 /\ orthogonal e1 e2
           ==> e1 = rotate2d (pi / &2) e2 \/ e2 = rotate2d (pi / &2) e1"
   (REWRITE_TAC [NORM_EQ_1, orthogonal] THEN
    SIMP_TAC [DOT_2, CART_EQ, FORALL_2, DIMINDEX_2, rotate2d, VECTOR_2] THEN
    REWRITE_TAC [COS_PI2, SIN_PI2, REAL_MUL_RZERO, REAL_ADD_RID,
                 REAL_SUB_LZERO, REAL_SUB_RZERO, REAL_MUL_RID] THEN
    CONV_TAC (fun t => REAL_RING t))

  let ROTATION_ROTATE2D_EXISTS_ORTHOGONAL_ORIENTED ← prove
   r"!e1 e2. norm(e1) = &1 /\ norm(e2) = &1 /\ orthogonal e1 e2 /\
           &0 < e1$1 * e2$2 - e1$2 * e2$1
           ==> e2 = rotate2d (pi / &2) e1"
   (REPEAT GEN_TAC THEN REWRITE_TAC [CONJ_ASSOC] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC [← GSYM CONJ_ASSOC] THEN DISCH_TAC THEN
    FIRST_ASSUM (DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP
      ROTATION_ROTATE2D_EXISTS_ORTHOGONAL) THEN
    REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM REAL_NOT_LE]) THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN DISCH_THEN (K ALL_TAC) THEN
    SIMP_TAC [DOT_2, CART_EQ, FORALL_2, DIMINDEX_2, rotate2d, VECTOR_2] THEN
    REWRITE_TAC [COS_PI2, SIN_PI2, REAL_MUL_RZERO, REAL_ADD_RID,
                 REAL_SUB_LZERO, REAL_SUB_RZERO, REAL_MUL_RID] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"--x * x - y * y <= &0 <=> &0 <= x * x + y * y")] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC [REAL_LE_SQUARE])

  let ROTATE2D_EQ ← prove
   r"!t x y. rotate2d t x = rotate2d t y <=> x = y"
   (MESON_TAC [ORTHOGONAL_TRANSFORMATION_INJECTIVE,
               ORTHOGONAL_TRANSFORMATION_ROTATE2D])

  let ROTATE2D_SUB_ARG ← prove
   r"!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> rotate2d(Arg w - Arg z) = rotate2d(Arg(w / z))"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [REAL_SUB_ARG] THEN
    COND_CASES_TAC THEN REWRITE_TAC [real_sub, ROTATE2D_ADD, FUN_EQ_THM] THEN
    GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [ROTATE2D_COMPLEX] THEN
    REWRITE_TAC [EULER, RE_MUL_II, IM_MUL_II, RE_CX, IM_CX, COS_NEG, SIN_NEG] THEN
    REWRITE_TAC [SIN_NPI, COS_NPI, REAL_EXP_NEG, REAL_EXP_0, CX_NEG] THEN
    REWRITE_TAC [COMPLEX_NEG_0, COMPLEX_MUL_RZERO, COMPLEX_ADD_RID] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [COMPLEX_MUL_LID])

  let ROTATION_MATRIX_ROTATE2D ← prove
   r"!t. rotation_matrix(matrix(rotate2d t))"
   (SIMP_TAC [ROTATION_MATRIX_2, MATRIX_ROTATE2D, VECTOR_2] THEN
    MESON_TAC [SIN_CIRCLE, REAL_ADD_SYM])

  let ROTATION_MATRIX_ROTATE2D_EQ ← prove
   r"!A:real^2^2. rotation_matrix A <=> ?t. A = matrix(rotate2d t)"
   (GEN_TAC THEN EQ_TAC THEN
    SIMP_TAC [LEFT_IMP_EXISTS_THM, ROTATION_MATRIX_ROTATE2D] THEN
    REWRITE_TAC [ROTATION_MATRIX_2, MATRIX_ROTATE2D] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP SINCOS_TOTAL_2PI) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [CART_EQ, DIMINDEX_2, FORALL_2, VECTOR_2] THEN
    ASM_REAL_ARITH_TAC)

  pure { rotate2d, LINEAR_ROTATE2D, ROTATE2D_ADD_VECTORS, ROTATE2D_SUB, NORM_ROTATE2D,
         ROTATE2D_0, ROTATE2D_EQ_0, ROTATE2D_ZERO, ORTHOGONAL_TRANSFORMATION_ROTATE2D,
         ROTATE2D_POLAR, MATRIX_ROTATE2D, DET_MATRIX_ROTATE2D, ROTATION_ROTATE2D,
         ROTATE2D_ADD, ROTATE2D_COMPLEX, ROTATE2D_PI2, ROTATE2D_PI, ROTATE2D_NPI,
         ROTATE2D_2PI, ARG_ROTATE2D, ARG_ROTATE2D_UNIQUE, ARG_ROTATE2D_UNIQUE_2PI,
         COMPLEX_DIV_ROTATION, ROTATION_ROTATE2D_EXISTS_GEN, ROTATION_ROTATE2D_EXISTS,
         ROTATION_ROTATE2D_EXISTS_ORTHOGONAL, ROTATION_ROTATE2D_EXISTS_ORTHOGONAL_ORIENTED,
         ROTATE2D_EQ, ROTATE2D_SUB_ARG, ROTATION_MATRIX_ROTATE2D,
         ROTATION_MATRIX_ROTATE2D_EQ }
/- ------------------------------------------------------------------------- -/
/- Homotopy of linear maps of various kinds where the homotopy stays inside  -/
/- that class of linear maps.                                                -/
/- (transcendentals.ml 2634-3009)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSJ where
  NULLHOMOTOPIC_ORTHOGONAL_TRANSFORMATION : thm
  HOMOTOPIC_SPECIAL_ORTHOGONAL_TRANSFORMATIONS : thm
  HOMOTOPIC_WITH_ORTHOGONAL_TRANSFORMATIONS_UNIV : thm
  HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_SPHERE : thm
  HOMOTOPIC_LINEAR_MAPS : thm
  HOMOTOPIC_LINEAR_POSITIVE_SEMIDEFINITE_MAPS : thm
  HOMOTOPIC_LINEAR_POSITIVE_DEFINITE_MAPS : thm
  HOMOTOPIC_RESTRICTED_LINEAR_MAPS : thm
  HOMOTOPIC_INVERTIBLE_LINEAR_MAPS_ALT : thm
  HOMOTOPIC_INVERTIBLE_LINEAR_MAPS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSJ [HolBase] (D : TranscendentalsDeps) : ExceptT String IO TSJ := do
  -- @@SCOPE BEGIN
  let { CONTINUOUS_DISCRETE_RANGE_CONSTANT, CONTINUOUS_ON_LIFT_DET,
        RIGHT_POLAR_DECOMPOSITION_INVERTIBLE, sphere, .. } := D.qtopology
  let { MATRIX_ADD, MATRIX_ADD_LID, MATRIX_ADD_RID, MATRIX_CMUL_LID, MATRIX_CMUL_LZERO,
        .. } := D.qvectors
  let { REAL_EQ_SGN_ABS, REAL_SGN_0, .. } := D.qsession
  let { POSITIVE_DEFINITE_ADD, POSITIVE_DEFINITE_CMUL, POSITIVE_SEMIDEFINITE_ADD,
        POSITIVE_SEMIDEFINITE_CMUL, .. } := D.qdeterminants
  let { HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT,
        HOMOTOPIC_WITH_ORTHOGONAL_TRANSFORMATIONS_GEN, .. } := D.qpaths
  let { HOMOTOPIC_WITH_IMP_PROPERTY, .. } := D.qmetric
  let { CONVEX_CONNECTED_1, .. } := D.qconvex
  let { DET_CMUL, ORTHOGONAL_TRANSFORMATION_INVERSE_o, .. } := D.cn.ms.qdet
  let { real_sgn, .. } := D.cn.ms.qsession
  let { MATRIX_CMUL, .. } := D.cn.ms.qvec
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC,
        REAL_RAT_REDUCE_CONV, REAL_RING, SET_RULE, .. } := D.cn.cx.cvx
  let { matrix, .. } := D.cn.cx.cpx
  let { AND_FORALL_THM, COND_RAND, CONTRAPOS_THM, DE_MORGAN_THM, EQ_TRANS, ETA_AX,
        .. } := D.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, FSTCART_PASTECART, FUN_EQ_THM, IMP_CONJ, IMP_CONJ_ALT,
        .. } := D.cn.cx.cvx.core2
  let { IN_UNIV, LAMBDA_BETA, LEFT_IMP_EXISTS_THM, MONO_EXISTS, PASTECART_IN_PCROSS,
        .. } := D.cn.cx.cvx.core3
  let { REAL_LT_01, REAL_LT_REFL, .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_SGN_CASES, REAL_SGN_EQ, REAL_SUB_LE,
        REAL_SUB_REFL, REAL_SUB_RZERO, RIGHT_FORALL_IMP_THM, SNDCART_PASTECART, SUBSET,
        .. } := D.cn.cx.cvx.core5
  let { o_ASSOC, o_DEF, o_THM, real_gt, SUBSET_UNIV, .. } := D.cn.cx.cvx.core6
  let { DIST_0, .. } := D.cn.cx.cvx.vec1
  let { DROP_EQ, DROP_VEC, FORALL_DROP, LIFT_DROP, LIFT_EQ, LIFT_SUB, LINEAR_COMPOSE,
        LINEAR_COMPOSE_ADD, LINEAR_FSTCART, LINEAR_SNDCART, MATRIX_COMPOSE,
        MATRIX_OF_MATRIX_VECTOR_MUL, MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LINEAR,
        MATRIX_WORKS, .. } := D.cn.cx.cvx.vec2
  let { NORM_LIFT, .. } := D.cn.cx.cvx.vec3
  let { VECTOR_ADD_LID, VECTOR_ADD_RID, VECTOR_MUL_LID, VECTOR_MUL_LZERO,
        .. } := D.cn.cx.cvx.vec4
  let { DET_I, DET_MUL, DET_ORTHOGONAL_MATRIX, ORTHOGONAL_MATRIX_MATRIX,
        ORTHOGONAL_TRANSFORMATION_COMPOSE, ORTHOGONAL_TRANSFORMATION_LINEAR,
        .. } := D.cn.cx.cvx.det
  let { CONNECTED_CONTINUOUS_IMAGE, .. } := D.cn.cx.cvx.top2
  let { CONTINUOUS_ON_ADD, CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID,
        CONTINUOUS_ON_MUL, CONTINUOUS_ON_SUB, CONTINUOUS_ON_SUBSET, .. } := D.cn.cx.cvx.top3
  let { IN_INTERVAL_1, LINEAR_CONTINUOUS_ON, .. } := D.cn.cx.cvx.top4
  let { SEGMENT_1, .. } := D.cn.cx.cvx.top5
  let { CONNECTED_INTERVAL, .. } := D.cn.ms.ig.dv.qconvex
  let { CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE, .. } := D.cn.ms.ig.dv.qtopology1
  let { LINEAR_COMPOSE_CMUL, .. } := D.cn.ms.ig.dv.qvec
  let { INVERTIBLE_DET_NZ, ORTHOGONAL_MATRIX_TRANSFORMATION, ORTHOGONAL_TRANSFORMATION_I,
        .. } := D.cn.ms.ig.dv.dg.qdet
  let { HOMOTOPIC_WITH_SYM, HOMOTOPIC_WITH_TRANS, .. } := D.cn.ms.ig.dv.dg.qmetric
  let { HOMOTOPIC_WITH_COMPOSE, HOMOTOPIC_WITH_EUCLIDEAN, .. } := D.cn.ms.ig.dv.dg.qpaths1
  let { I_O_ID, REAL_SGN_INEQS, REAL_SGN_MUL, .. } := D.cn.ms.ig.dv.dg.qsession
  let { CONTINUOUS_ON_PASTECART, DET_POSITIVE_DEFINITE, .. } := D.cn.ms.ig.dv.dg.qtopology1
  let { ENDS_IN_UNIT_INTERVAL, MATRIX_I, .. } := D.cn.ms.ig.dv.dg.qvec
  let { CONVEX_CONTAINS_SEGMENT, .. } := D.cn.ms.ig.dv.dg.pt.qcvx2
  -- @@SCOPE END

  let NULLHOMOTOPIC_ORTHOGONAL_TRANSFORMATION ← prove
   r"!f:real^N->real^N.
       orthogonal_transformation f /\ det(matrix f) = &1
       ==> homotopic_with orthogonal_transformation
            (subtopology euclidean (:real^N),subtopology euclidean (:real^N))
            f I"
   (SIMP_TAC [D.qpaths.HOMOTOPIC_WITH_ORTHOGONAL_TRANSFORMATIONS_UNIV] THEN
    REWRITE_TAC [ORTHOGONAL_TRANSFORMATION_I, MATRIX_I, DET_I])

  let (HOMOTOPIC_SPECIAL_ORTHOGONAL_TRANSFORMATIONS,
       HOMOTOPIC_WITH_ORTHOGONAL_TRANSFORMATIONS_UNIV) ← CONJ_PAIR (← prove
   r"(!f g. homotopic_with
            (\h. orthogonal_transformation h /\ det(matrix h) = det(matrix f))
            (subtopology euclidean (:real^N),subtopology euclidean (:real^N))
            f g <=>
          homotopic_with
            orthogonal_transformation
             (subtopology euclidean (:real^N),
              subtopology euclidean (:real^N)) f g) /\
   !f g. homotopic_with orthogonal_transformation
          (subtopology euclidean (:real^N),
           subtopology euclidean (:real^N)) f g <=>
         orthogonal_transformation f /\ orthogonal_transformation g /\
         det(matrix f) = det(matrix g)"
   (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC (← TAUT
     (← q r"(u ==> s) /\ (s ==> t) /\ (t ==> u)
      ==> (u <=> t) /\ (t <=> s)")) THEN
    REPEAT CONJ_TAC THENL
     [DISCH_THEN (MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_PROPERTY) THEN MESON_TAC [],
      STRIP_TAC THEN
      MP_TAC (← ISPEC (← q r"g:real^N->real^N") ORTHOGONAL_TRANSFORMATION_INVERSE_o) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"h:real^N->real^N") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       (← q r"(f:real^N->real^N) = g o (h:real^N->real^N) o f /\ g = g o I")
       (fun th => ONCE_REWRITE_TAC [th])
      THENL [ASM_REWRITE_TAC [o_ASSOC, I_O_ID], ALL_TAC] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
      EXISTS_TAC (← q r"(:real^N)") THEN REWRITE_TAC [SUBSET_UNIV] THEN
      ASM_SIMP_TAC [ORTHOGONAL_TRANSFORMATION_LINEAR, LINEAR_CONTINUOUS_ON] THEN
      SUBGOAL_THEN
        (← q r"!k:real^N->real^N.
            orthogonal_transformation (g o k) <=> orthogonal_transformation k")
        (fun th => REWRITE_TAC [th, ETA_AX])
      THENL
       [GEN_TAC THEN EQ_TAC THEN
        ASM_SIMP_TAC [ORTHOGONAL_TRANSFORMATION_COMPOSE] THEN DISCH_THEN
         (MP_TAC o SPEC (← q r"h:real^N->real^N") o MATCH_MP (← ONCE_REWRITE_RULE
           [IMP_CONJ_ALT] ORTHOGONAL_TRANSFORMATION_COMPOSE)) THEN
        ASM_SIMP_TAC [o_ASSOC, I_O_ID],
        MATCH_MP_TAC NULLHOMOTOPIC_ORTHOGONAL_TRANSFORMATION THEN
        REPEAT (FIRST_X_ASSUM (MP_TAC o AP_TERM
         (← q r"\f:real^N->real^N. det(matrix f)"))) THEN
        ASM_SIMP_TAC [MATRIX_COMPOSE, ORTHOGONAL_TRANSFORMATION_LINEAR,
                      ORTHOGONAL_TRANSFORMATION_COMPOSE, DET_MUL,
                      MATRIX_I, DET_I]],
      REWRITE_TAC [HOMOTOPIC_WITH_EUCLIDEAN] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC (← q r"k:real^(1,N)finite_sum->real^N") THEN
      STRIP_TAC THEN ASM_SIMP_TAC [] THEN MP_TAC (← ISPECL
       [← q r"\t. lift(
         det(matrix((k:real^(1,N)finite_sum->real^N) o pastecart t)))",
        ← q r"interval[vec 0:real^1,vec 1]"]
       CONTINUOUS_DISCRETE_RANGE_CONSTANT) THEN
      REWRITE_TAC [CONNECTED_INTERVAL] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_LIFT_DET THEN
          SIMP_TAC [matrix, LAMBDA_BETA, o_DEF] THEN
          MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"j:num"] THEN STRIP_TAC THEN
          MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
          ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
          MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
          SIMP_TAC [CONTINUOUS_ON_PASTECART, CONTINUOUS_ON_CONST,
                    CONTINUOUS_ON_ID] THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
          SIMP_TAC [SUBSET, FORALL_IN_IMAGE, PASTECART_IN_PCROSS, IN_UNIV],
          X_GEN_TAC (← q r"t:real^1") THEN DISCH_TAC THEN EXISTS_TAC (← q r"&1") THEN
          REWRITE_TAC [REAL_LT_01] THEN X_GEN_TAC (← q r"u:real^1") THEN
          DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
          REWRITE_TAC [← GSYM LIFT_SUB, NORM_LIFT, LIFT_EQ] THEN
          SUBGOAL_THEN
           (← q r"orthogonal_transformation
             ((k:real^(1,N)finite_sum->real^N) o pastecart t) /\
            orthogonal_transformation (k o pastecart u)")
          MP_TAC THENL [ASM_SIMP_TAC [o_DEF], ALL_TAC] THEN
          DISCH_THEN (CONJUNCTS_THEN
            (STRIP_ASSUME_TAC o MATCH_MP DET_ORTHOGONAL_MATRIX o
                      MATCH_MP ORTHOGONAL_MATRIX_MATRIX)) THEN
          ASM_REWRITE_TAC [] THEN CONV_TAC REAL_RAT_REDUCE_CONV],
        REWRITE_TAC [o_DEF, LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC (← q r"a:real^1") THEN DISCH_TAC THEN
        REPEAT (FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [← GSYM FUN_EQ_THM])) THEN
        REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN
        ASM_SIMP_TAC [ENDS_IN_UNIT_INTERVAL, ← GSYM LIFT_EQ]]]))

  let HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_SPHERE ← prove
   r"!f g r.
        &0 < r
        ==> (homotopic_with orthogonal_transformation
              (subtopology euclidean (sphere(vec 0,r)),
               subtopology euclidean (sphere(vec 0,r))) f g <=>
             homotopic_with orthogonal_transformation
              (subtopology euclidean (:real^N),
               subtopology euclidean (:real^N)) f g)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [HOMOTOPIC_WITH_ORTHOGONAL_TRANSFORMATIONS_UNIV] THEN
    REWRITE_TAC [sphere, DIST_0] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_ORTHOGONAL_TRANSFORMATIONS_GEN THEN
    ASM_MESON_TAC [])

  let HOMOTOPIC_LINEAR_MAPS ← prove
   r"!f g. homotopic_with linear
          (subtopology euclidean (:real^M),subtopology euclidean (:real^N))
          f g <=>
         linear f /\ linear g"
   (REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [HOMOTOPIC_WITH_IMP_PROPERTY] THEN
    STRIP_TAC THEN REWRITE_TAC [HOMOTOPIC_WITH_EUCLIDEAN] THEN
    EXISTS_TAC (← q r"\z. (&1 - drop(fstcart z)) % (f:real^M->real^N) (sndcart z) +
                    drop(fstcart z) % (g:real^M->real^N) (sndcart z)") THEN
    REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART, DROP_VEC, SUBSET_UNIV,
                 VECTOR_MUL_LID, VECTOR_MUL_LZERO, REAL_SUB_RZERO, REAL_SUB_REFL,
                 VECTOR_ADD_LID, VECTOR_ADD_RID] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      SIMP_TAC [o_DEF, LIFT_SUB, LIFT_DROP, CONTINUOUS_ON_SUB, LINEAR_FSTCART,
        ETA_AX, LINEAR_SNDCART, CONTINUOUS_ON_CONST, LINEAR_CONTINUOUS_ON] THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC [LINEAR_CONTINUOUS_ON, LINEAR_FSTCART, LINEAR_SNDCART],
      REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN
      CONJ_TAC THEN MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN ASM_REWRITE_TAC []])

  let HOMOTOPIC_LINEAR_POSITIVE_SEMIDEFINITE_MAPS ← prove
   r"!f g. homotopic_with (\f. linear f /\ positive_semidefinite(matrix f))
          (subtopology euclidean (:real^N),
           subtopology euclidean (:real^N)) f g <=>
           linear f /\ linear g /\
           positive_semidefinite(matrix f) /\
           positive_semidefinite(matrix g)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [FIRST_ASSUM (MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_PROPERTY) THEN SIMP_TAC [],
      REWRITE_TAC [HOMOTOPIC_WITH_EUCLIDEAN]] THEN
    EXISTS_TAC (← q r"\z. (&1 - drop(fstcart z)) % (f:real^N->real^N) (sndcart z) +
                    drop(fstcart z) % (g:real^N->real^N) (sndcart z)") THEN
    REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART, DROP_VEC, SUBSET_UNIV,
                 VECTOR_MUL_LID, VECTOR_MUL_LZERO, REAL_SUB_RZERO, REAL_SUB_REFL,
                 VECTOR_ADD_LID, VECTOR_ADD_RID] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      SIMP_TAC [o_DEF, LIFT_SUB, LIFT_DROP, CONTINUOUS_ON_SUB, LINEAR_FSTCART,
        ETA_AX, LINEAR_SNDCART, CONTINUOUS_ON_CONST, LINEAR_CONTINUOUS_ON] THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC [LINEAR_CONTINUOUS_ON, LINEAR_FSTCART, LINEAR_SNDCART],
      REWRITE_TAC [IN_INTERVAL_1, ← GSYM FORALL_DROP, DROP_VEC] THEN
      ASM_SIMP_TAC [LINEAR_COMPOSE_ADD, MATRIX_ADD, LINEAR_COMPOSE_CMUL,
                    MATRIX_CMUL] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC POSITIVE_SEMIDEFINITE_ADD THEN
      CONJ_TAC THEN MATCH_MP_TAC POSITIVE_SEMIDEFINITE_CMUL THEN
      ASM_REWRITE_TAC [REAL_SUB_LE]])

  let HOMOTOPIC_LINEAR_POSITIVE_DEFINITE_MAPS ← prove
   r"!f g. homotopic_with (\f. linear f /\ positive_definite(matrix f))
           (subtopology euclidean (:real^N),
            subtopology euclidean (:real^N)) f g <=>
           linear f /\ linear g /\
           positive_definite(matrix f) /\
           positive_definite(matrix g)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [FIRST_ASSUM (MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_PROPERTY) THEN SIMP_TAC [],
      REWRITE_TAC [HOMOTOPIC_WITH_EUCLIDEAN]] THEN
    EXISTS_TAC (← q r"\z. (&1 - drop(fstcart z)) % (f:real^N->real^N) (sndcart z) +
                    drop(fstcart z) % (g:real^N->real^N) (sndcart z)") THEN
    REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART, DROP_VEC, SUBSET_UNIV,
                 VECTOR_MUL_LID, VECTOR_MUL_LZERO, REAL_SUB_RZERO, REAL_SUB_REFL,
                 VECTOR_ADD_LID, VECTOR_ADD_RID] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      SIMP_TAC [o_DEF, LIFT_SUB, LIFT_DROP, CONTINUOUS_ON_SUB, LINEAR_FSTCART,
        ETA_AX, LINEAR_SNDCART, CONTINUOUS_ON_CONST, LINEAR_CONTINUOUS_ON] THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC [LINEAR_CONTINUOUS_ON, LINEAR_FSTCART, LINEAR_SNDCART],
      REWRITE_TAC [IN_INTERVAL_1, ← GSYM FORALL_DROP, DROP_VEC] THEN
      ASM_SIMP_TAC [LINEAR_COMPOSE_ADD, MATRIX_ADD, LINEAR_COMPOSE_CMUL,
                    MATRIX_CMUL] THEN
      X_GEN_TAC (← q r"t:real") THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"t = &0") THEN
      ASM_REWRITE_TAC [REAL_SUB_RZERO, MATRIX_CMUL_LZERO, MATRIX_ADD_RID,
                       MATRIX_CMUL_LID] THEN
      ASM_CASES_TAC (← q r"t = &1") THEN
      ASM_REWRITE_TAC [REAL_SUB_REFL, MATRIX_CMUL_LZERO, MATRIX_ADD_LID,
                       MATRIX_CMUL_LID] THEN
      MATCH_MP_TAC POSITIVE_DEFINITE_ADD THEN
      CONJ_TAC THEN MATCH_MP_TAC POSITIVE_DEFINITE_CMUL THEN
      ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC])

  let HOMOTOPIC_RESTRICTED_LINEAR_MAPS ← prove
   r"!f g b. homotopic_with (\f. linear f /\ real_sgn(det(matrix f)) = b)
            (subtopology euclidean (:real^N),
             subtopology euclidean (:real^N)) f g <=>
           linear f /\ linear g /\
           real_sgn(det(matrix f)) = b /\
           real_sgn(det(matrix g)) = b"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_PROPERTY) THEN SIMP_TAC [],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"b = &0") THENL
     [ASM_REWRITE_TAC [REAL_SGN_EQ] THEN STRIP_TAC THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
      EXISTS_TAC (← q r"(\x. vec 0):real^N->real^N") THEN
      GEN_REWRITE_TAC LAND_CONV [HOMOTOPIC_WITH_SYM] THEN
      REWRITE_TAC [HOMOTOPIC_WITH_EUCLIDEAN] THEN CONJ_TAC THENL
       [EXISTS_TAC (← q r"\z. drop(fstcart z) % (f:real^N->real^N) (sndcart z)"),
        EXISTS_TAC (← q r"\z. drop(fstcart z) % (g:real^N->real^N) (sndcart z)")] THEN
      REWRITE_TAC [SUBSET_UNIV, FSTCART_PASTECART, SNDCART_PASTECART,
                   DROP_VEC, VECTOR_MUL_LZERO, VECTOR_MUL_LID] THEN
      ASM_SIMP_TAC [LINEAR_COMPOSE_CMUL, MATRIX_CMUL] THEN
      ASM_REWRITE_TAC [DET_CMUL, REAL_MUL_RZERO] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      SIMP_TAC [o_DEF, LIFT_DROP, LINEAR_FSTCART, ETA_AX, LINEAR_SNDCART,
                LINEAR_CONTINUOUS_ON] THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC [LINEAR_CONTINUOUS_ON, LINEAR_FSTCART, LINEAR_SNDCART],
      ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"(?fu fp. linear fu /\ linear fp /\
               orthogonal_transformation fu /\
               positive_definite(matrix fp) /\
               (f:real^N->real^N) = fu o fp) /\
      (?gu gp. linear gu /\ linear gp /\
               orthogonal_transformation gu /\
               positive_definite(matrix gp) /\
               (g:real^N->real^N) = gu o gp)")
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC (← ISPEC (← q r"matrix(f:real^N->real^N)")
          RIGHT_POLAR_DECOMPOSITION_INVERTIBLE),
        MP_TAC (← ISPEC (← q r"matrix(g:real^N->real^N)")
          RIGHT_POLAR_DECOMPOSITION_INVERTIBLE)] THEN
      REWRITE_TAC [INVERTIBLE_DET_NZ] THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [← GSYM REAL_SGN_EQ] THEN
      ASM_REWRITE_TAC [] THEN
      REPEAT (MATCH_MP_TAC (← MESON []
       (← q r"(!M. P M ==> Q(\x:real^N. M ** x))
        ==> (?M. P M) ==> (?f. Q f)")) THEN GEN_TAC) THEN
      SIMP_TAC [← GSYM ORTHOGONAL_MATRIX_TRANSFORMATION,
                MATRIX_VECTOR_MUL_LINEAR, MATRIX_OF_MATRIX_VECTOR_MUL] THEN
      STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM, o_DEF] THEN
      ASM_REWRITE_TAC [MATRIX_VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC [MATRIX_WORKS],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE THEN
    EXISTS_TAC (← q r"\h. linear h /\ positive_definite(matrix h:real^N^N)") THEN
    EXISTS_TAC (← q r"\h. orthogonal_transformation h /\
                  det(matrix h:real^N^N) = det (matrix fu:real^N^N)") THEN
    EXISTS_TAC (← q r"(:real^N)") THEN SIMP_TAC [SUBSET_UNIV] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_THEN (← q r"real_sgn(det(matrix f:real^N^N)) = b")
       (SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC [LINEAR_COMPOSE, MATRIX_COMPOSE, DET_MUL, REAL_SGN_MUL,
                    ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
      REPEAT STRIP_TAC THEN
      AP_TERM_TAC THEN ASM_SIMP_TAC [real_sgn, DET_POSITIVE_DEFINITE],
      ASM_REWRITE_TAC [HOMOTOPIC_LINEAR_POSITIVE_DEFINITE_MAPS],
      REWRITE_TAC [HOMOTOPIC_SPECIAL_ORTHOGONAL_TRANSFORMATIONS] THEN
      ASM_REWRITE_TAC [HOMOTOPIC_WITH_ORTHOGONAL_TRANSFORMATIONS_UNIV] THEN
      ONCE_REWRITE_TAC [REAL_EQ_SGN_ABS] THEN CONJ_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC (← REAL_ARITH
         (← q r"(a = &1 \/ a = -- &1) /\ (b = &1 \/ b = -- &1) ==> abs a = abs b")) THEN
        CONJ_TAC THEN MATCH_MP_TAC DET_ORTHOGONAL_MATRIX THEN
        ASM_SIMP_TAC [ORTHOGONAL_MATRIX_MATRIX]] THEN
      UNDISCH_TAC (← q r"real_sgn(det(matrix f:real^N^N)) = b") THEN
      UNDISCH_THEN (← q r"real_sgn(det(matrix g:real^N^N)) = b")
       (SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC [MATRIX_COMPOSE, ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
      ASM_REWRITE_TAC [DET_MUL, REAL_SGN_MUL] THEN MATCH_MP_TAC (← REAL_RING
       (← q r"x = &1 /\ y = &1 ==> a * x = b * y ==> a = b")) THEN
      ASM_SIMP_TAC [REAL_SGN_EQ, DET_POSITIVE_DEFINITE, real_gt]])

  let HOMOTOPIC_INVERTIBLE_LINEAR_MAPS_ALT ← prove
   r"!f g. homotopic_with (\h. linear h /\ invertible(matrix h))
          (subtopology euclidean (:real^N),
           subtopology euclidean (:real^N)) f g <=>
         linear f /\ linear g /\
         &0 < real_sgn(det(matrix f)) * real_sgn(det(matrix g))"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"linear f /\ linear g /\
                   invertible(matrix(f:real^N->real^N)) /\
                   invertible(matrix(g:real^N->real^N))")
    THENL
     [POP_ASSUM MP_TAC THEN REWRITE_TAC [INVERTIBLE_DET_NZ] THEN STRIP_TAC,
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← TAUT
       (← q r"~p ==> (q ==> p) /\ (r ==> p) ==> (q <=> r)"))) THEN
      CONJ_TAC THENL
       [DISCH_THEN (MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_PROPERTY) THEN
        SIMP_TAC [],
        ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
        REWRITE_TAC [INVERTIBLE_DET_NZ, DE_MORGAN_THM] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC [REAL_SGN_0] THEN
        REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_LT_REFL]]] THEN
    ASM_REWRITE_TAC [] THEN TRANS_TAC EQ_TRANS
     (← q r"homotopic_with (\h. linear h /\
                          real_sgn(det(matrix h)) = real_sgn(det(matrix f)))
        (subtopology euclidean (:real^N),
         subtopology euclidean (:real^N)) f g") THEN
    CONJ_TAC THENL
     [ALL_TAC,
      ASM_REWRITE_TAC [HOMOTOPIC_RESTRICTED_LINEAR_MAPS] THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o check (HolCore.Basics.is_neg o concl))) THEN
      ONCE_REWRITE_TAC [← GSYM (← CONJUNCT1 REAL_SGN_EQ)] THEN
      MP_TAC (← ISPEC (← q r"det(matrix(f:real^N->real^N))") REAL_SGN_CASES) THEN
      MP_TAC (← ISPEC (← q r"det(matrix(g:real^N->real^N))") REAL_SGN_CASES) THEN
      STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    REWRITE_TAC [HOMOTOPIC_WITH_EUCLIDEAN] THEN
    GEN_REWRITE_TAC
      (LAND_CONV o ONCE_DEPTH_CONV) [← GSYM (← CONJUNCT1 REAL_SGN_EQ)] THEN
    EQ_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [] THEN
    ASM_REWRITE_TAC [REAL_SGN_EQ] THEN
    X_GEN_TAC (← q r"h:real^(1,N)finite_sum->real^N") THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"t:real^1") THEN DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"(\t. lift(det(matrix((h:real^(1,N)finite_sum->real^N) o pastecart t))))
      continuous_on interval[vec 0,vec 1]")
    MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_DET THEN
      SIMP_TAC [matrix, LAMBDA_BETA, o_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"j:num"] THEN STRIP_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC [CONTINUOUS_ON_PASTECART, CONTINUOUS_ON_CONST,
                CONTINUOUS_ON_ID] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, PASTECART_IN_PCROSS, IN_UNIV],
      ALL_TAC] THEN
    DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          CONNECTED_CONTINUOUS_IMAGE)) THEN
    REWRITE_TAC [CONNECTED_INTERVAL] THEN
    REWRITE_TAC [← GSYM CONVEX_CONNECTED_1, CONVEX_CONTAINS_SEGMENT] THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, o_DEF] THEN
    REWRITE_TAC [FORALL_IN_IMAGE] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"vec 0:real^1")) THEN
    REWRITE_TAC [ENDS_IN_UNIT_INTERVAL] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"t:real^1")) THEN ASM_REWRITE_TAC [ETA_AX] THEN
    MATCH_MP_TAC (← SET_RULE
     (← q r"(!x. x IN s ==> ~(f x = vec 0)) /\ (~P ==> vec 0 IN t)
      ==> t SUBSET IMAGE f s ==> P")) THEN
    ASM_SIMP_TAC [← GSYM DROP_EQ, LIFT_DROP, DROP_VEC] THEN
    SPEC_TAC (← q r"det(matrix(\x. (h:real^(1,N)finite_sum->real^N) (pastecart t x)))",
              ← q r"a:real") THEN
    SPEC_TAC (← q r"det(matrix(f:real^N->real^N))", ← q r"b:real") THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [SEGMENT_1, LIFT_DROP] THEN
    ONCE_REWRITE_TAC [COND_RAND] THEN
    REWRITE_TAC [IN_INTERVAL_1, LIFT_DROP, DROP_VEC] THEN
    REWRITE_TAC [real_sgn] THEN REAL_ARITH_TAC)

  let HOMOTOPIC_INVERTIBLE_LINEAR_MAPS ← prove
   r"!f g. homotopic_with (\h. linear h /\ invertible(matrix h))
          (subtopology euclidean (:real^N),
           subtopology euclidean (:real^N)) f g <=>
         linear f /\ linear g /\ &0 < det(matrix f) * det(matrix g)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [HOMOTOPIC_INVERTIBLE_LINEAR_MAPS_ALT] THEN
    REWRITE_TAC [← GSYM REAL_SGN_MUL, REAL_SGN_INEQS])

  pure { NULLHOMOTOPIC_ORTHOGONAL_TRANSFORMATION, HOMOTOPIC_SPECIAL_ORTHOGONAL_TRANSFORMATIONS,
         HOMOTOPIC_WITH_ORTHOGONAL_TRANSFORMATIONS_UNIV, HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_SPHERE,
         HOMOTOPIC_LINEAR_MAPS, HOMOTOPIC_LINEAR_POSITIVE_SEMIDEFINITE_MAPS,
         HOMOTOPIC_LINEAR_POSITIVE_DEFINITE_MAPS, HOMOTOPIC_RESTRICTED_LINEAR_MAPS,
         HOMOTOPIC_INVERTIBLE_LINEAR_MAPS_ALT, HOMOTOPIC_INVERTIBLE_LINEAR_MAPS }
/- ------------------------------------------------------------------------- -/
/- "If and only if" variants of unrestricted homotopy characterization;     -/
/- complex tangent function, its analytic properties; real tangent.         -/
/- (transcendentals.ml 3010-3338)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSK where
  HOMOTOPIC_LINEAR_MAPS_EQ : thm
  HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_EQ : thm
  HOMOTOPIC_ANTIPODAL_IDENTITY_MAP : thm
  ctan : thm
  CTAN_0 : thm
  CTAN_NEG : thm
  CTAN_ADD : thm
  CTAN_DOUBLE : thm
  CCOT_DOUBLE : thm
  CTAN_CCOT_DOUBLE : thm
  CTAN_SUB : thm
  COMPLEX_ADD_CTAN : thm
  COMPLEX_SUB_CTAN : thm
  CTAN_CEXP : thm
  HAS_COMPLEX_DERIVATIVE_CTAN : thm
  COMPLEX_DIFFERENTIABLE_AT_CTAN : thm
  COMPLEX_DIFFERENTIABLE_WITHIN_CTAN : thm
  CONTINUOUS_AT_CTAN : thm
  CONTINUOUS_WITHIN_CTAN : thm
  CONTINUOUS_ON_CTAN : thm
  HOLOMORPHIC_ON_CTAN : thm
  tan_def : thm
  CNJ_CTAN : thm
  REAL_TAN : thm
  CX_TAN : thm
  tan : thm
  TAN_0 : thm
  TAN_PI : thm
  TAN_NPI : thm
  TAN_NEG : thm
  TAN_PERIODIC_PI : thm
  TAN_PERIODIC_NPI : thm
  TAN_ADD : thm
  TAN_SUB : thm
  TAN_DOUBLE : thm
  COT_DOUBLE : thm
  TAN_COT_DOUBLE : thm
  REAL_ADD_TAN : thm
  REAL_SUB_TAN : thm
  TAN_PI4 : thm
  TAN_POS_PI2 : thm
  TAN_POS_PI2_LE : thm
  COS_TAN : thm
  SIN_TAN : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSK [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) (BTSB : TSB) (BTSC : TSC) (BTSE : TSE) (BTSJ : TSJ) : ExceptT String IO TSK := do
  -- @@SCOPE BEGIN
  let { CEXP_N, CEXP_NEG, CEXP_NZ, .. } := BTSA
  let { ccos, CCOS_0, CCOS_ADD, CCOS_DOUBLE, CCOS_NEG, csin, CSIN_0, CSIN_ADD, CSIN_CIRCLE,
        CSIN_DOUBLE, CSIN_NEG, CSIN_SUB, .. } := BTSB
  let { CNJ_CCOS, CNJ_CSIN, CX_COS, CX_SIN, SIN_CIRCLE, .. } := BTSC
  let { COS_EQ_0, COS_PERIODIC_PI, COS_POS_PI, PI_NZ, SIN_COS, SIN_NPI, SIN_PERIODIC_PI,
        SIN_PI, SIN_POS_PI, .. } := BTSE
  let { HOMOTOPIC_INVERTIBLE_LINEAR_MAPS, HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_SPHERE,
        HOMOTOPIC_WITH_ORTHOGONAL_TRANSFORMATIONS_UNIV, .. } := BTSJ
  let { complex_differentiable, COMPLEX_DIFFERENTIABLE_AT_WITHIN,
        HAS_COMPLEX_DERIVATIVE_AT_WITHIN, HAS_COMPLEX_DERIVATIVE_CHAIN,
        HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT, holomorphic_on, .. } := D.kne
  let { add_complex_differentiation_theorems, COMPLEX_DIFF_TAC, .. } := D.knk
  let { HOMOTOPIC_LINEAR_MAPS_ALT, HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_IMP,
        .. } := D.qdegree
  let { complex_div, complex_sub, .. } := D.cn.cxa
  let { COMPLEX_MUL_AC, COMPLEX_MUL_ASSOC, COMPLEX_MUL_LNEG, COMPLEX_MUL_LZERO,
        COMPLEX_MUL_RNEG, COMPLEX_MUL_RZERO, COMPLEX_NEG_NEG, COMPLEX_SUB_REFL,
        .. } := D.cn.cxb
  let { COMPLEX_MUL_RINV, COMPLEX_POW_EQ_0, COMPLEX_POW_MUL, CX_ADD, CX_DIV, CX_INJ,
        CX_INV, CX_MUL, CX_NEG, CX_POW, CX_SUB, .. } := D.cn.cxc
  let { COMPLEX_RING, .. } := D.cn.cxd
  let { COMPLEX_FIELD, COMPLEX_INV_0, COMPLEX_INV_INV, COMPLEX_INV_MUL, COMPLEX_POW_INV,
        .. } := D.cn.cxe
  let { COMPLEX_DIV_1, .. } := D.cn.cxf
  let { CNJ_DIV, .. } := D.cn.cxg
  let { REAL, REAL_CNJ, REAL_CX, .. } := D.cn.cxi
  let { REAL_ABS_INTEGER_LEMMA, .. } := D.cn.ms.qfloor
  let { REAL_BOUNDS_LT, .. } := D.cn.ms.qsession
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INDUCT_TAC, MESON_TAC, new_definition,
        REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD, REAL_RAT_REDUCE_CONV, REAL_RING, SET_TAC,
        .. } := D.cn.cx.cvx
  let { REAL_LE_SQUARE, SQRT_POS_LT, .. } := D.cn.cx.cpx
  let { CONJ_SYM, CONTRAPOS_THM, ETA_AX, FORALL_AND_THM, .. } := D.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_PASTECART, FUN_EQ_THM, IMP_CONJ, IN_DELETE,
        .. } := D.cn.cx.cvx.core2
  let { I_THM, IN_UNIV, MONO_EXISTS, PASTECART_IN_PCROSS, REAL_ADD_ASSOC,
        REAL_ADD_RDISTRIB, REAL_ADD_RID, REAL_DIV_REFL, REAL_DIV_RMUL,
        .. } := D.cn.cx.cvx.core3
  let { REAL_INV_NEG, REAL_LE_LT, REAL_LT_01, REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_IMP_NZ,
        REAL_LT_MUL, .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_LNEG, REAL_MUL_LZERO, REAL_MUL_RNEG, REAL_NEG_NEG,
        REAL_OF_NUM_SUC, REAL_POW_ONE, SQRT_POW_2, SUBSET, SUBSET_PCROSS,
        .. } := D.cn.cx.cvx.core5
  let { o_THM, real_div, UNWIND_THM2, .. } := D.cn.cx.cvx.core6
  let { LINEAR_0, MATRIX_ID, .. } := D.cn.cx.cvx.vec2
  let { DET_I, ORTHOGONAL_TRANSFORMATION_ID, .. } := D.cn.cx.cvx.det
  let { CONTINUOUS_AT_IMP_CONTINUOUS_ON, .. } := D.cn.cx.cvx.top2
  let { CONTINUOUS_ON_SUBSET, .. } := D.cn.cx.cvx.top3
  let { CONTINUOUS_AT_WITHIN, .. } := D.cn.ms.ig.dv.qtopology1
  let { DET_NEG, ORTHOGONAL_TRANSFORMATION_NEG, .. } := D.cn.ms.ig.dv.dg.qdet
  let { HOMOTOPIC_WITH_EUCLIDEAN, HOMOTOPIC_WITH_MONO, .. } := D.cn.ms.ig.dv.dg.qpaths1
  let { REAL_POW_NEG, .. } := D.cn.ms.ig.dv.dg.qsession
  let { LINEAR_ID, MATRIX_INVERTIBLE, MATRIX_NEG, .. } := D.cn.ms.ig.dv.dg.qvec
  -- @@SCOPE END

  let HOMOTOPIC_LINEAR_MAPS_EQ ← prove
   r"!f g:real^N->real^N.
        linear f /\ linear g
        ==> (homotopic_with (\x. T)
               (subtopology euclidean ((:real^N) DELETE vec 0),
                subtopology euclidean ((:real^N) DELETE vec 0)) f g <=>
             &0 < det(matrix f) * det(matrix g))"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN
    ASM_SIMP_TAC [HOMOTOPIC_LINEAR_MAPS_ALT] THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^N->real^N", ← q r"g:real^N->real^N"]
        HOMOTOPIC_INVERTIBLE_LINEAR_MAPS) THEN
    ASM_REWRITE_TAC [HOMOTOPIC_WITH_EUCLIDEAN] THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"h:real^(1,N)finite_sum->real^N") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
         CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC [SUBSET_PCROSS] THEN SET_TAC [],
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [← q r"t:real^1", ← q r"x:real^N"] THEN
      REWRITE_TAC [PASTECART_IN_PCROSS, IN_UNIV, IN_DELETE] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"t:real^1")) THEN
      ASM_SIMP_TAC [IMP_CONJ, MATRIX_INVERTIBLE] THEN DISCH_THEN (K ALL_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"k:real^N->real^N") MP_TAC) THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      GEN_REWRITE_TAC id [← GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC [FUN_EQ_THM, o_THM] THEN DISCH_TAC THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"x:real^N")) THEN ASM_REWRITE_TAC [I_THM] THEN
      ASM_MESON_TAC [LINEAR_0]])

  let HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_EQ ← prove
   r"!f g:real^N->real^N.
        orthogonal_transformation f /\ orthogonal_transformation g
        ==> (homotopic_with (\x. T)
              (subtopology euclidean (sphere (vec 0,&1)),
               subtopology euclidean (sphere (vec 0,&1))) f g <=>
             det(matrix f) = det(matrix g))"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_IMP THEN
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC HOMOTOPIC_WITH_MONO THEN
      EXISTS_TAC (← q r"orthogonal_transformation:(real^N->real^N)->bool") THEN
      SIMP_TAC [HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_SPHERE, REAL_LT_01] THEN
      ASM_REWRITE_TAC [HOMOTOPIC_WITH_ORTHOGONAL_TRANSFORMATIONS_UNIV]])

  let HOMOTOPIC_ANTIPODAL_IDENTITY_MAP ← prove
   r"homotopic_with (\x. T)
      (subtopology euclidean (sphere(vec 0,&1)),
       subtopology euclidean (sphere(vec 0,&1)))
                  (\x:real^N. --x) (\x. x) <=>
   EVEN(dimindex(:N))"
   (SIMP_TAC [HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_EQ,
              ORTHOGONAL_TRANSFORMATION_NEG,
              ORTHOGONAL_TRANSFORMATION_ID] THEN
    SIMP_TAC [MATRIX_NEG, LINEAR_ID, DET_NEG, MATRIX_ID, DET_I] THEN
    REWRITE_TAC [REAL_POW_NEG, REAL_POW_ONE] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN CONV_TAC REAL_RAT_REDUCE_CONV)

  let ctan ← new_definition
   r"ctan z = csin z / ccos z"

  let CTAN_0 ← prove
   r"ctan(Cx(&0)) = Cx(&0)"
   (REWRITE_TAC [ctan, CSIN_0, CCOS_0, COMPLEX_DIV_1])

  let CTAN_NEG ← prove
   r"!z. ctan(--z) = --(ctan z)"
   (REWRITE_TAC [ctan, CSIN_NEG, CCOS_NEG, complex_div, COMPLEX_MUL_LNEG])

  let CTAN_ADD ← prove
   r"!w z. ~(ccos(w) = Cx(&0)) /\
         ~(ccos(z) = Cx(&0)) /\
         ~(ccos(w + z) = Cx(&0))
         ==> ctan(w + z) = (ctan w + ctan z) / (Cx(&1) - ctan(w) * ctan(z))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [ctan, CSIN_ADD, CCOS_ADD] THEN
    CONV_TAC COMPLEX_FIELD)

  let CTAN_DOUBLE ← prove
   r"!z. ctan(Cx(&2) * z) = (Cx(&2) * ctan z) / (Cx(&1) - ctan z pow 2)"
   (GEN_TAC THEN REWRITE_TAC [ctan, CSIN_DOUBLE, CCOS_DOUBLE] THEN
    REWRITE_TAC [complex_div, COMPLEX_INV_MUL] THEN
    MAP_EVERY ASM_CASES_TAC [← q r"csin z = Cx(&0)", ← q r"ccos z = Cx(&0)"] THEN
    ASM_REWRITE_TAC [COMPLEX_INV_0, COMPLEX_MUL_LZERO, COMPLEX_MUL_RZERO] THEN
    REWRITE_TAC [COMPLEX_POW_MUL, COMPLEX_POW_INV] THEN
    ASM_CASES_TAC (← q r"csin z pow 2 = ccos z pow 2") THEN
    ASM_SIMP_TAC [COMPLEX_MUL_RINV, COMPLEX_POW_EQ_0, COMPLEX_SUB_REFL,
                  COMPLEX_INV_0, COMPLEX_MUL_RZERO] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD)

  let CCOT_DOUBLE ← prove
   r"!z. inv(ctan(Cx(&2) * z)) = (inv(ctan z) - ctan z) / Cx(&2)"
   (GEN_TAC THEN REWRITE_TAC [ctan, CSIN_DOUBLE, CCOS_DOUBLE] THEN
    REWRITE_TAC [complex_div, COMPLEX_INV_MUL] THEN
    MAP_EVERY ASM_CASES_TAC [← q r"csin z = Cx(&0)", ← q r"ccos z = Cx(&0)"] THEN
    ASM_REWRITE_TAC [COMPLEX_INV_0, COMPLEX_MUL_LZERO, COMPLEX_MUL_RZERO] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD)

  let CTAN_CCOT_DOUBLE ← prove
   r"!z. ctan z = Cx(&1) / ctan z - Cx(&2) / ctan(Cx(&2) * z)"
   (REWRITE_TAC [complex_div, CCOT_DOUBLE] THEN CONV_TAC COMPLEX_RING)

  let CTAN_SUB ← prove
   r"!w z. ~(ccos(w) = Cx(&0)) /\
         ~(ccos(z) = Cx(&0)) /\
         ~(ccos(w - z) = Cx(&0))
         ==> ctan(w - z) = (ctan w - ctan z) / (Cx(&1) + ctan(w) * ctan(z))"
   (SIMP_TAC [complex_sub, CTAN_ADD, CCOS_NEG, CTAN_NEG] THEN
    REWRITE_TAC [COMPLEX_MUL_RNEG, COMPLEX_NEG_NEG])

  let COMPLEX_ADD_CTAN ← prove
   r"!w z. ~(ccos(w) = Cx(&0)) /\
         ~(ccos(z) = Cx(&0))
         ==> ctan(w) + ctan(z) = csin(w + z) / (ccos(w) * ccos(z))"
   (REWRITE_TAC [ctan, CSIN_ADD] THEN CONV_TAC COMPLEX_FIELD)

  let COMPLEX_SUB_CTAN ← prove
   r"!w z. ~(ccos(w) = Cx(&0)) /\
         ~(ccos(z) = Cx(&0))
         ==> ctan(w) - ctan(z) = csin(w - z) / (ccos(w) * ccos(z))"
   (REWRITE_TAC [ctan, CSIN_SUB] THEN CONV_TAC COMPLEX_FIELD)

  let CTAN_CEXP ← prove
   r"!z. ctan z =
       --ii * (cexp(Cx(&2) * ii * z) - Cx(&1)) /
              (cexp(Cx(&2) * ii * z) + Cx(&1))"
   (GEN_TAC THEN REWRITE_TAC [ctan, csin, ccos] THEN
    REWRITE_TAC [COMPLEX_MUL_LNEG, CEXP_NEG] THEN
    SIMP_TAC [CEXP_NZ, ← ExceptT.mk (COMPLEX_FIELD
     (← q r"~(c = Cx(&0))
      ==> c - inv c = (c pow 2 - Cx(&1)) / c /\
          c + inv c = (c pow 2 + Cx(&1)) / c"))] THEN
    REWRITE_TAC [← GSYM CEXP_N, complex_div, COMPLEX_INV_MUL] THEN
    REWRITE_TAC [← GSYM COMPLEX_MUL_ASSOC, COMPLEX_INV_INV] THEN
    SIMP_TAC [CEXP_NZ, ← ExceptT.mk (COMPLEX_FIELD
     (← q r"~(e = Cx(&0))
      ==> x * inv e * inv(Cx(&2)) * inv ii * y * e * Cx(&2) =
          --ii * x * y"))] THEN
    REWRITE_TAC [complex_div, COMPLEX_MUL_LNEG] THEN
    REWRITE_TAC [COMPLEX_MUL_AC])

  let HAS_COMPLEX_DERIVATIVE_CTAN ← prove
   r"!z. ~(ccos z = Cx(&0))
       ==> (ctan has_complex_derivative (inv(ccos(z) pow 2))) (at z)"
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [← GSYM ETA_AX] THEN
    REWRITE_TAC [ctan] THEN COMPLEX_DIFF_TAC THEN
    MP_TAC (← SPEC (← q r"z:complex") CSIN_CIRCLE) THEN
    POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD)

  let COMPLEX_DIFFERENTIABLE_AT_CTAN ← prove
   r"!z. ~(ccos z = Cx(&0)) ==> ctan complex_differentiable at z"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_CTAN])

  let COMPLEX_DIFFERENTIABLE_WITHIN_CTAN ← prove
   r"!s z. ~(ccos z = Cx(&0))
         ==> ctan complex_differentiable (at z within s)"
   (MESON_TAC [COMPLEX_DIFFERENTIABLE_AT_WITHIN,
               COMPLEX_DIFFERENTIABLE_AT_CTAN])

  add_complex_differentiation_theorems
   (CONJUNCTS (← REWRITE_RULE [FORALL_AND_THM]
     (← MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
               HAS_COMPLEX_DERIVATIVE_CTAN)))

  let CONTINUOUS_AT_CTAN ← prove
   r"!z. ~(ccos z = Cx(&0)) ==> ctan continuous at z"
   (MESON_TAC [HAS_COMPLEX_DERIVATIVE_CTAN,
               HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT])

  let CONTINUOUS_WITHIN_CTAN ← prove
   r"!s z. ~(ccos z = Cx(&0)) ==> ctan continuous (at z within s)"
   (MESON_TAC [CONTINUOUS_AT_WITHIN, CONTINUOUS_AT_CTAN])

  let CONTINUOUS_ON_CTAN ← prove
   r"!s. (!z. z IN s ==> ~(ccos z = Cx(&0))) ==> ctan continuous_on s"
   (MESON_TAC [CONTINUOUS_AT_IMP_CONTINUOUS_ON, CONTINUOUS_AT_CTAN])

  let HOLOMORPHIC_ON_CTAN ← prove
   r"!s. (!z. z IN s ==> ~(ccos z = Cx(&0))) ==> ctan holomorphic_on s"
   (REWRITE_TAC [holomorphic_on] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN, HAS_COMPLEX_DERIVATIVE_CTAN])

  let tan_def ← new_definition
   r"tan(x) = Re(ctan(Cx x))"

  let CNJ_CTAN ← prove
   r"!z. cnj(ctan z) = ctan(cnj z)"
   (REWRITE_TAC [ctan, CNJ_DIV, CNJ_CSIN, CNJ_CCOS])

  let REAL_TAN ← prove
   r"!z. real z ==> real(ctan z)"
   (SIMP_TAC [REAL_CNJ, CNJ_CTAN])

  let CX_TAN ← prove
   r"!x. Cx(tan x) = ctan(Cx x)"
   (REWRITE_TAC [tan_def] THEN MESON_TAC [REAL, REAL_CX, REAL_TAN])

  let tan ← prove
   r"!x. tan x = sin x / cos x"
   (REWRITE_TAC [← GSYM CX_INJ, CX_DIV, CX_TAN, CX_SIN, CX_COS, ctan])

  let TAN_0 ← prove
   r"tan(&0) = &0"
   (REWRITE_TAC [← GSYM CX_INJ, CX_TAN, CTAN_0])

  let TAN_PI ← prove
   r"tan(pi) = &0"
   (REWRITE_TAC [tan, SIN_PI, real_div, REAL_MUL_LZERO])

  let TAN_NPI ← prove
   r"!n. tan(&n * pi) = &0"
   (REWRITE_TAC [tan, SIN_NPI, real_div, REAL_MUL_LZERO])

  let TAN_NEG ← prove
   r"!x. tan(--x) = --(tan x)"
   (REWRITE_TAC [← GSYM CX_INJ, CX_TAN, CX_NEG, CTAN_NEG])

  let TAN_PERIODIC_PI ← prove
   r"!x. tan(x + pi) = tan(x)"
   (REWRITE_TAC [tan, SIN_PERIODIC_PI, COS_PERIODIC_PI, real_div] THEN
    REWRITE_TAC [REAL_MUL_LNEG, REAL_INV_NEG, REAL_MUL_RNEG, REAL_NEG_NEG])

  let TAN_PERIODIC_NPI ← prove
   r"!x n. tan(x + &n * pi) = tan(x)"
   (GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_RID] THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_SUC, REAL_ADD_RDISTRIB, REAL_MUL_LID] THEN
    ASM_REWRITE_TAC [REAL_ADD_ASSOC, TAN_PERIODIC_PI])

  let TAN_ADD ← prove
   r"!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0) /\ ~(cos(x + y) = &0)
         ==> tan(x + y) = (tan(x) + tan(y)) / (&1 - tan(x) * tan(y))"
   (REWRITE_TAC [← GSYM CX_INJ, CX_TAN, CX_SIN, CX_COS, CTAN_ADD,
                 CX_DIV, CX_ADD, CX_SUB, CX_MUL])

  let TAN_SUB ← prove
   r"!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0) /\ ~(cos(x - y) = &0)
         ==> tan(x - y) = (tan(x) - tan(y)) / (&1 + tan(x) * tan(y))"
   (REWRITE_TAC [← GSYM CX_INJ, CX_TAN, CX_SIN, CX_COS, CX_ADD, CTAN_SUB,
                 CX_DIV, CX_ADD, CX_SUB, CX_MUL])

  let TAN_DOUBLE ← prove
   r"!x. tan(&2 * x) = (&2 * tan x) / (&1 - tan x pow 2)"
   (REWRITE_TAC [← GSYM CX_INJ, CX_DIV, CX_MUL, CX_SUB, CX_POW, CX_TAN] THEN
    REWRITE_TAC [CTAN_DOUBLE])

  let COT_DOUBLE ← prove
   r"!z. inv(tan(&2 * z)) = (inv(tan z) - tan z) / &2"
   (REWRITE_TAC [← GSYM CX_INJ, CX_INV, CX_DIV, CX_MUL, CX_SUB, CX_POW, CX_TAN] THEN
    REWRITE_TAC [CCOT_DOUBLE])

  let TAN_COT_DOUBLE ← prove
   r"!z. tan z = &1 / tan z - &2 / tan(&2 * z)"
   (REWRITE_TAC [real_div, COT_DOUBLE] THEN CONV_TAC (fun t => REAL_RING t))

  let REAL_ADD_TAN ← prove
   r"!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0)
         ==> tan(x) + tan(y) = sin(x + y) / (cos(x) * cos(y))"
   (REWRITE_TAC [← GSYM CX_INJ, CX_TAN, CX_SIN, CX_COS, CX_MUL, CX_ADD, CX_DIV] THEN
    REWRITE_TAC [COMPLEX_ADD_CTAN])

  let REAL_SUB_TAN ← prove
   r"!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0)
         ==> tan(x) - tan(y) = sin(x - y) / (cos(x) * cos(y))"
   (REWRITE_TAC [← GSYM CX_INJ, CX_TAN, CX_SIN, CX_COS, CX_MUL, CX_SUB, CX_DIV] THEN
    REWRITE_TAC [COMPLEX_SUB_CTAN])

  let TAN_PI4 ← prove
   r"tan(pi / &4) = &1"
   (REWRITE_TAC [tan, SIN_COS, ← REAL_ARITH (← q r"p / &2 - p / &4 = p / &4")] THEN
    MATCH_MP_TAC REAL_DIV_REFL THEN REWRITE_TAC [COS_EQ_0, PI_NZ, ← REAL_FIELD
     (← q r"p / &4 = (n + &1 / &2) * p <=> p = &0 \/ n = -- &1 / &4")] THEN
    ONCE_REWRITE_TAC [CONJ_SYM] THEN REWRITE_TAC [UNWIND_THM2] THEN
    DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
     REAL_ABS_INTEGER_LEMMA)) THEN
    REAL_ARITH_TAC)

  let TAN_POS_PI2 ← prove
   r"!x. &0 < x /\ x < pi / &2 ==> &0 < tan x"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [tan] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
     [MATCH_MP_TAC SIN_POS_PI, MATCH_MP_TAC COS_POS_PI] THEN
    ASM_REAL_ARITH_TAC)

  let TAN_POS_PI2_LE ← prove
   r"!x. &0 <= x /\ x < pi / &2 ==> &0 <= tan x"
   (REWRITE_TAC [REAL_LE_LT] THEN MESON_TAC [TAN_0, TAN_POS_PI2])

  let COS_TAN ← prove
   r"!x. abs(x) < pi / &2 ==> cos(x) = &1 / sqrt(&1 + tan(x) pow 2)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← REAL_FIELD
     (← q r"sqrt(s) pow 2 = s /\ c pow 2 * s = &1 /\ ~(&1 + c * sqrt s = &0)
      ==> c = &1 / sqrt s")) THEN
    SUBGOAL_THEN (← q r"&0 < &1 + tan x pow 2") ASSUME_TAC THENL
     [MP_TAC (← SPEC (← q r"tan x") REAL_LE_SQUARE) THEN REAL_ARITH_TAC, ALL_TAC] THEN
    ASM_SIMP_TAC [SQRT_POW_2, REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [REWRITE_TAC [tan] THEN
      MATCH_MP_TAC (← REAL_FIELD
       (← q r"s pow 2 + c pow 2 = &1 /\ &0 < c
        ==> c pow 2 * (&1 + (s / c) pow 2) = &1")) THEN
      ASM_SIMP_TAC [SIN_CIRCLE, COS_POS_PI, REAL_BOUNDS_LT],
      MATCH_MP_TAC (← REAL_ARITH (← q r"&0 < x ==> ~(&1 + x = &0)")) THEN
      ASM_SIMP_TAC [SIN_CIRCLE, COS_POS_PI, REAL_BOUNDS_LT, SQRT_POS_LT,
                    REAL_LT_MUL]])

  let SIN_TAN ← prove
   r"!x. abs(x) < pi / &2 ==> sin(x) = tan(x) / sqrt(&1 + tan(x) pow 2)"
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"a / b = a * &1 / b")] THEN
    ASM_SIMP_TAC [← GSYM COS_TAN] THEN
    ASM_SIMP_TAC [tan, REAL_DIV_RMUL, REAL_LT_IMP_NZ, COS_POS_PI,
                  REAL_BOUNDS_LT])

  pure { HOMOTOPIC_LINEAR_MAPS_EQ, HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_EQ,
         HOMOTOPIC_ANTIPODAL_IDENTITY_MAP, ctan, CTAN_0, CTAN_NEG, CTAN_ADD, CTAN_DOUBLE,
         CCOT_DOUBLE, CTAN_CCOT_DOUBLE, CTAN_SUB, COMPLEX_ADD_CTAN, COMPLEX_SUB_CTAN,
         CTAN_CEXP, HAS_COMPLEX_DERIVATIVE_CTAN, COMPLEX_DIFFERENTIABLE_AT_CTAN,
         COMPLEX_DIFFERENTIABLE_WITHIN_CTAN, CONTINUOUS_AT_CTAN, CONTINUOUS_WITHIN_CTAN,
         CONTINUOUS_ON_CTAN, HOLOMORPHIC_ON_CTAN, tan_def, CNJ_CTAN, REAL_TAN, CX_TAN,
         tan, TAN_0, TAN_PI, TAN_NPI, TAN_NEG, TAN_PERIODIC_PI, TAN_PERIODIC_NPI,
         TAN_ADD, TAN_SUB, TAN_DOUBLE, COT_DOUBLE, TAN_COT_DOUBLE, REAL_ADD_TAN,
         REAL_SUB_TAN, TAN_PI4, TAN_POS_PI2, TAN_POS_PI2_LE, COS_TAN, SIN_TAN }
/- ------------------------------------------------------------------------- -/
/- Monotonicity theorems for the basic trig functions; approximation to pi. -/
/- (transcendentals.ml 3339-3528)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSL where
  SIN_MONO_LT : thm
  SIN_MONO_LE : thm
  SIN_MONO_LT_EQ : thm
  SIN_MONO_LE_EQ : thm
  SIN_INJ_PI : thm
  COS_MONO_LT : thm
  COS_MONO_LE : thm
  COS_MONO_LT_EQ : thm
  COS_MONO_LE_EQ : thm
  COS_INJ_PI : thm
  REAL_ABS_COS_MONO_LE_EQ : thm
  TAN_MONO_LT : thm
  TAN_MONO_LE : thm
  TAN_MONO_LT_EQ : thm
  TAN_MONO_LE_EQ : thm
  TAN_BOUND_PI2 : thm
  TAN_COT : thm
  REAL_ABS_SIN_BOUND_LT : thm
  REAL_ABS_SIN_BOUND_LE : thm
  SIN_PI6_STRADDLE : thm
  PI_APPROX_32 : thm
  PI2_BOUNDS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSL [HolBase] (D : TranscendentalsDeps) (BTSB : TSB) (BTSC : TSC) (BTSE : TSE) (BTSG : TSG) (BTSK : TSK) : ExceptT String IO TSL := do
  -- @@SCOPE BEGIN
  let { REAL_EXP_0, .. } := BTSB
  let { COS_NEG, COS_SUB, CX_SIN, REAL_SUB_COS, REAL_SUB_SIN, SIN_0, SIN_BOUND, SIN_NEG,
        SIN_SUB, .. } := BTSC
  let { COS_PI2, COS_POS_PI, COS_POS_PI_LE, PI_POS, SIN_PI, SIN_PI2, SIN_PI6, SIN_POS_PI,
        .. } := BTSE
  let { TAYLOR_CSIN, .. } := BTSG
  let { REAL_SUB_TAN, tan, TAN_NEG, TAN_PI4, .. } := BTSK
  let { HORNER_SUM_CONV, .. } := D
  let { REAL_LT_NEGTOTAL, REAL_POW_LT2, REAL_POW_POW, .. } := D.qsession
  let { complex_pow, .. } := D.cn.cxa
  let { COMPLEX_MUL_LID, .. } := D.cn.cxb
  let { COMPLEX_NORM_CX, COMPLEX_POW_1, CX_ADD, CX_DIV, CX_MUL, CX_NEG, CX_POW, CX_SUB,
        IM_CX, .. } := D.cn.cxc
  let { COMPLEX_DIV_1, .. } := D.cn.cxf
  let { VSUM_CX, .. } := D.cn.cxi
  let { VSUM_SING_NUMSEG, .. } := D.cn.qvectors
  let { ASM_REAL_ARITH_TAC, MESON, MESON_TAC, num_CONV, NUM_REDUCE_CONV, REAL_ARITH,
        REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV, .. } := D.cn.cx.cvx
  let { REAL_POW_1, REAL_POW_ADD, .. } := D.cn.cx.cpx
  let { ARITH_EQ, FINITE_NUMSEG, .. } := D.cn.cx.cvx.core1
  let { REAL_ABS_NEG, REAL_ABS_NUM, .. } := D.cn.cx.cvx.core3
  let { REAL_INV_DIV, REAL_LE_ANTISYM, REAL_LE_LT, REAL_LE_NEGTOTAL, REAL_LE_REFL,
        REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_LMUL_EQ, REAL_LT_MUL,
        REAL_LT_REFL, .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_SYM, REAL_NOT_LE, REAL_NOT_LT, REAL_POW_LT,
        REAL_POW_MUL, REAL_SUB_LT, .. } := D.cn.cx.cvx.core5
  let { real_abs, real_div, real_pow, .. } := D.cn.cx.cvx.core6
  let { VSUM_CLAUSES_NUMSEG, .. } := D.cn.cx.cvx.vec4
  let { REAL_POW_MONO_INV, .. } := D.cn.ms.ig.dv.qsession
  let { REAL_LT_TRANS, .. } := D.cn.ms.ig.dv.dg.qsession
  let { REAL_BOUNDS_LE, .. } := D.cn.ms.ig.dv.dg.pt.qses
  -- @@SCOPE END

  let SIN_MONO_LT ← prove
   r"!x y. --(pi / &2) <= x /\ x < y /\ y <= pi / &2 ==> sin(x) < sin(y)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_SUB_LT] THEN
    REWRITE_TAC [REAL_SUB_SIN, ← REAL_ARITH (← q r"&0 < &2 * x <=> &0 < x")] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SIN_POS_PI, MATCH_MP_TAC COS_POS_PI] THEN
    ASM_REAL_ARITH_TAC)

  let SIN_MONO_LE ← prove
   r"!x y. --(pi / &2) <= x /\ x <= y /\ y <= pi / &2 ==> sin(x) <= sin(y)"
   (MESON_TAC [SIN_MONO_LT, REAL_LE_LT])

  let SIN_MONO_LT_EQ ← prove
   r"!x y. --(pi / &2) <= x /\ x <= pi / &2 /\ --(pi / &2) <= y /\ y <= pi / &2
         ==> (sin(x) < sin(y) <=> x < y)"
   (MESON_TAC [REAL_NOT_LE, SIN_MONO_LT, SIN_MONO_LE])

  let SIN_MONO_LE_EQ ← prove
   r"!x y. --(pi / &2) <= x /\ x <= pi / &2 /\ --(pi / &2) <= y /\ y <= pi / &2
         ==> (sin(x) <= sin(y) <=> x <= y)"
   (MESON_TAC [REAL_NOT_LE, SIN_MONO_LT, SIN_MONO_LE])

  let SIN_INJ_PI ← prove
   r"!x y. --(pi / &2) <= x /\ x <= pi / &2 /\
         --(pi / &2) <= y /\ y <= pi / &2 /\
         sin(x) = sin(y)
         ==> x = y"
   (REWRITE_TAC [← GSYM REAL_LE_ANTISYM] THEN MESON_TAC [SIN_MONO_LE_EQ])

  let COS_MONO_LT ← prove
   r"!x y. &0 <= x /\ x < y /\ y <= pi ==> cos(y) < cos(x)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_SUB_LT] THEN
    REWRITE_TAC [REAL_SUB_COS, ← REAL_ARITH (← q r"&0 < &2 * x <=> &0 < x")] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC SIN_POS_PI THEN
    ASM_REAL_ARITH_TAC)

  let COS_MONO_LE ← prove
   r"!x y. &0 <= x /\ x <= y /\ y <= pi ==> cos(y) <= cos(x)"
   (MESON_TAC [COS_MONO_LT, REAL_LE_LT])

  let COS_MONO_LT_EQ ← prove
   r"!x y. &0 <= x /\ x <= pi /\ &0 <= y /\ y <= pi
         ==> (cos(x) < cos(y) <=> y < x)"
   (MESON_TAC [REAL_NOT_LE, COS_MONO_LT, COS_MONO_LE])

  let COS_MONO_LE_EQ ← prove
   r"!x y. &0 <= x /\ x <= pi /\ &0 <= y /\ y <= pi
         ==> (cos(x) <= cos(y) <=> y <= x)"
   (MESON_TAC [REAL_NOT_LE, COS_MONO_LT, COS_MONO_LE])

  let COS_INJ_PI ← prove
   r"!x y. &0 <= x /\ x <= pi /\ &0 <= y /\ y <= pi /\ cos(x) = cos(y)
         ==> x = y"
   (REWRITE_TAC [← GSYM REAL_LE_ANTISYM] THEN MESON_TAC [COS_MONO_LE_EQ])

  let REAL_ABS_COS_MONO_LE_EQ ← prove
   r"!x y. abs(x) <= pi / &2 /\ abs(y) <= pi / &2
         ==> (abs(cos x) <= abs(cos y) <=> abs y <= abs x)"
   (MAP_EVERY (fun t => tactic_of do pure (
      MATCH_MP_TAC (← MESON [REAL_LE_NEGTOTAL]
       (← q r"(!x. P(--x) <=> P x) /\ (!x. &0 <= x ==> P x) ==> !x. P x")) THEN
      REWRITE_TAC [REAL_ABS_NEG, COS_NEG] THEN X_GEN_TAC t THEN DISCH_TAC))
     [← q r"x:real", ← q r"y:real"] THEN
    SIMP_TAC [← REWRITE_RULE [REAL_BOUNDS_LE] COS_POS_PI_LE,
              ← REAL_ARITH (← q r"&0 <= cos x ==> abs(cos x) = cos x")] THEN
    REWRITE_TAC [REAL_BOUNDS_LE] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [real_abs] THEN MATCH_MP_TAC COS_MONO_LE_EQ THEN
    ASM_REAL_ARITH_TAC)

  let TAN_MONO_LT ← prove
   r"!x y. --(pi / &2) < x /\ x < y /\ y < pi / &2 ==> tan(x) < tan(y)"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC id [← GSYM REAL_SUB_LT] THEN
    SUBGOAL_THEN (← q r"&0 < cos(x) /\ &0 < cos(y)") STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC COS_POS_PI,
      ASM_SIMP_TAC [REAL_LT_IMP_NZ, REAL_SUB_TAN] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC [REAL_LT_MUL] THEN
      MATCH_MP_TAC SIN_POS_PI] THEN
    ASM_REAL_ARITH_TAC)

  let TAN_MONO_LE ← prove
   r"!x y. --(pi / &2) < x /\ x <= y /\ y < pi / &2 ==> tan(x) <= tan(y)"
   (REWRITE_TAC [REAL_LE_LT] THEN MESON_TAC [TAN_MONO_LT])

  let TAN_MONO_LT_EQ ← prove
   r"!x y. --(pi / &2) < x /\ x < pi / &2 /\ --(pi / &2) < y /\ y < pi / &2
         ==> (tan(x) < tan(y) <=> x < y)"
   (MESON_TAC [REAL_NOT_LE, TAN_MONO_LT, TAN_MONO_LE])

  let TAN_MONO_LE_EQ ← prove
   r"!x y. --(pi / &2) < x /\ x < pi / &2 /\ --(pi / &2) < y /\ y < pi / &2
         ==> (tan(x) <= tan(y) <=> x <= y)"
   (MESON_TAC [REAL_NOT_LE, TAN_MONO_LT, TAN_MONO_LE])

  let TAN_BOUND_PI2 ← prove
   r"!x. abs(x) < pi / &4 ==> abs(tan x) < &1"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM TAN_PI4] THEN
    REWRITE_TAC [← GSYM TAN_NEG, ← REAL_ARITH (← q r"abs(x) < a <=> --a < x /\ x < a")] THEN
    CONJ_TAC THEN MATCH_MP_TAC TAN_MONO_LT THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC)

  let TAN_COT ← prove
   r"!x. tan(pi / &2 - x) = inv(tan x)"
   (REWRITE_TAC [tan, SIN_SUB, COS_SUB, SIN_PI2, COS_PI2, REAL_INV_DIV] THEN
    GEN_TAC THEN BINOP_TAC THEN REAL_ARITH_TAC)

  let REAL_ABS_SIN_BOUND_LT ← prove
   r"!x. ~(x = &0) ==> abs(sin x) < abs x"
   (MATCH_MP_TAC (← MESON [SIN_NEG, REAL_ABS_NEG, REAL_LT_NEGTOTAL]
     (← q r"(!x. &0 < x ==> abs(sin x) < abs x)
      ==> !x. ~(x = &0) ==> abs(sin x) < abs x")) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC (← REAL_ARITH (← q r"a < x ==> a < abs x")) THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"abs s <= &1 /\ (x <= &1 ==> abs(s) < x) ==> abs s < x")) THEN
    REWRITE_TAC [SIN_BOUND] THEN DISCH_TAC THEN
    MP_TAC (← SPECL [← q r"1", ← q r"Cx x"] TAYLOR_CSIN) THEN
    REWRITE_TAC [← ExceptT.mk (num_CONV (← q r"1")), VSUM_CLAUSES_NUMSEG, IM_CX] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC [REAL_ABS_NUM, REAL_EXP_0, COMPLEX_POW_1, complex_pow,
                 COMPLEX_DIV_1] THEN
    REWRITE_TAC [← GSYM CX_SIN, ← GSYM CX_MUL, ← GSYM CX_NEG, ← GSYM CX_POW, ← GSYM CX_DIV,
                 ← GSYM CX_SUB, ← GSYM CX_ADD, REAL_MUL_LID, COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"a < x /\ e < a ==> abs(s - (x + -- &1 * a)) <= e ==> abs s < x")) THEN
    ASM_SIMP_TAC [real_abs, REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC (← REAL_ARITH (← q r"&0 < y /\ x <= y pow 1 ==> x / &6 < y")),
      MATCH_MP_TAC (← REAL_ARITH (← q r"&0 < x /\ x <= y ==> x / &24 < y / &6"))] THEN
    ASM_SIMP_TAC [REAL_POW_LT] THEN MATCH_MP_TAC REAL_POW_MONO_INV THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC)

  let REAL_ABS_SIN_BOUND_LE ← prove
   r"!x. abs(sin x) <= abs x"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"x = &0") THEN
    ASM_SIMP_TAC [REAL_ABS_SIN_BOUND_LT, REAL_LT_IMP_LE, SIN_0, REAL_LE_REFL])

  let SIN_PI6_STRADDLE ← prove
   r"!a b. &0 <= a /\ a <= b /\ b <= &4 /\
         sin(a / &6) <= &1 / &2 /\ &1 / &2 <= sin(b / &6)
         ==> a <= pi /\ pi <= b"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"pi / &6", ← q r"b / &6"] SIN_MONO_LE_EQ) THEN
    MP_TAC (← SPECL [← q r"a / &6", ← q r"pi / &6"] SIN_MONO_LE_EQ) THEN
    ASM_REWRITE_TAC [SIN_PI6] THEN
    SUBGOAL_THEN (← q r"!x. &0 < x /\ x < &7 / &5 ==> &0 < sin x")
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [← q r"0", ← q r"Cx(x)"] TAYLOR_CSIN) THEN
      REWRITE_TAC [VSUM_SING_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC [COMPLEX_DIV_1, COMPLEX_POW_1, complex_pow] THEN
      REWRITE_TAC [COMPLEX_MUL_LID, ← GSYM CX_SIN, ← GSYM CX_SUB] THEN
      REWRITE_TAC [IM_CX, COMPLEX_NORM_CX, REAL_ABS_NUM, REAL_EXP_0] THEN
      MATCH_MP_TAC (← REAL_ARITH
       (← q r"e + d < a ==> abs(s - a) <= d ==> e < s")) THEN
      ASM_SIMP_TAC [real_abs, real_pow, REAL_MUL_LID, REAL_LT_IMP_LE] THEN
      SIMP_TAC [← REAL_ARITH (← q r"&0 + x pow 3 / &2 < x <=> x * x pow 2 < x * &2")] THEN
      ASM_SIMP_TAC [REAL_LT_LMUL_EQ] THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (← q r"(&7 / &5) pow 2") THEN
      ASM_SIMP_TAC [REAL_POW_LT2, ARITH_EQ, REAL_LT_IMP_LE] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV,
      DISCH_THEN (MP_TAC o SPEC (← q r"pi")) THEN
      SIMP_TAC [SIN_PI, REAL_LT_REFL, PI_POS, REAL_NOT_LT] THEN
      ASM_REAL_ARITH_TAC])

  let PI_APPROX_32 ← prove
   r"abs(pi - &13493037705 / &4294967296) <= inv(&2 pow 32)"
   (REWRITE_TAC [← REAL_ARITH (← q r"abs(x - a) <= e <=> a - e <= x /\ x <= a + e")] THEN
    MATCH_MP_TAC SIN_PI6_STRADDLE THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONJ_TAC THENL
     [MP_TAC (← SPECL [← q r"5", ← q r"Cx(&1686629713 / &3221225472)"] TAYLOR_CSIN),
      MP_TAC (← SPECL [← q r"5", ← q r"Cx(&6746518853 / &12884901888)"] TAYLOR_CSIN)] THEN
    SIMP_TAC [COMPLEX_NORM_CX, ← GSYM CX_POW, ← GSYM CX_DIV, ← GSYM CX_MUL,
              ← GSYM CX_NEG, VSUM_CX, FINITE_NUMSEG, ← GSYM CX_SIN, ← GSYM CX_SUB] THEN
    REWRITE_TAC [IM_CX, REAL_ABS_NUM, REAL_EXP_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [REAL_POW_ADD, REAL_POW_1, ← GSYM REAL_POW_POW] THEN
    REWRITE_TAC [REAL_MUL_ASSOC, ← GSYM REAL_POW_MUL, real_div] THEN
    REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    CONV_TAC (ONCE_DEPTH_CONV HORNER_SUM_CONV) THEN REAL_ARITH_TAC)

  let PI2_BOUNDS ← prove
   r"&0 < pi / &2 /\ pi / &2 < &2"
   (MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC)

  pure { SIN_MONO_LT, SIN_MONO_LE, SIN_MONO_LT_EQ, SIN_MONO_LE_EQ, SIN_INJ_PI,
         COS_MONO_LT, COS_MONO_LE, COS_MONO_LT_EQ, COS_MONO_LE_EQ, COS_INJ_PI,
         REAL_ABS_COS_MONO_LE_EQ, TAN_MONO_LT, TAN_MONO_LE, TAN_MONO_LT_EQ,
         TAN_MONO_LE_EQ, TAN_BOUND_PI2, TAN_COT, REAL_ABS_SIN_BOUND_LT,
         REAL_ABS_SIN_BOUND_LE, SIN_PI6_STRADDLE, PI_APPROX_32, PI2_BOUNDS }
/- ------------------------------------------------------------------------- -/
/- Complex logarithms (the conventional principal value); derivative of     -/
/- clog away from the branch cut; relation to real log.                     -/
/- (transcendentals.ml 3529-3677)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSM where
  clog : thm
  EXISTS_COMPLEX' : thm
  CLOG_WORKS : thm
  CEXP_CLOG : thm
  CLOG_CEXP : thm
  CLOG_EQ : thm
  CLOG_UNIQUE : thm
  RE_CLOG : thm
  EXISTS_COMPLEX_ROOT : thm
  HAS_COMPLEX_DERIVATIVE_CLOG : thm
  COMPLEX_DIFFERENTIABLE_AT_CLOG : thm
  COMPLEX_DIFFERENTIABLE_WITHIN_CLOG : thm
  CONTINUOUS_AT_CLOG : thm
  CONTINUOUS_WITHIN_CLOG : thm
  CONTINUOUS_ON_CLOG : thm
  HOLOMORPHIC_ON_CLOG : thm
  CX_LOG : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSM [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) (BTSB : TSB) (BTSC : TSC) (BTSD : TSD) (BTSE : TSE) (BTSF : TSF) : ExceptT String IO TSM := do
  -- @@SCOPE BEGIN
  let { CEXP_N, CONTINUOUS_ON_CEXP, HAS_COMPLEX_DERIVATIVE_CEXP, .. } := BTSA
  let { CX_EXP, REAL_EXP_POS_LT, .. } := BTSB
  let { EULER, .. } := BTSC
  let { EXP_LOG, LOG_EXP, .. } := BTSD
  let { COS_PI, PI_POS, REAL_ABS_PI, SIN_PI, .. } := BTSE
  let { CEXP_COMPLEX, CEXP_EQ, COMPLEX_UNIMODULAR_POLAR, NORM_CEXP, SINCOS_PRINCIPAL_VALUE,
        .. } := BTSF
  let { OPEN_HALFSPACE_IM_GT, OPEN_HALFSPACE_IM_LT, .. } := D.kna
  let { complex_differentiable, COMPLEX_DIFFERENTIABLE_AT_WITHIN,
        HAS_COMPLEX_DERIVATIVE_AT_WITHIN, HAS_COMPLEX_DERIVATIVE_CHAIN,
        HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT, holomorphic_on, .. } := D.kne
  let { HAS_COMPLEX_DERIVATIVE_INVERSE_STRONG_X, .. } := D.knj
  let { add_complex_differentiation_theorems, .. } := D.knk
  let { COMPLEX, IM, RE, .. } := D.cn.cxa
  let { COMPLEX_ADD_RID, COMPLEX_MUL_LZERO, COMPLEX_MUL_RID, COMPLEX_MUL_RNEG,
        COMPLEX_MUL_RZERO, .. } := D.cn.cxb
  let { COMPLEX_NORM_CX, COMPLEX_POW_ZERO, CX_INJ, CX_NEG, IM_ADD, IM_CX, IM_MUL_II,
        IM_NEG, RE_CX, RE_NEG, .. } := D.cn.cxc
  let { COMPLEX_DIV_LMUL, COMPLEX_NORM_DIV, COMPLEX_NORM_NZ, COMPLEX_NORM_ZERO,
        .. } := D.cn.cxf
  let { REAL_ABS_INTEGER_LEMMA, .. } := D.cn.ms.qfloor
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC, new_definition, REAL_ARITH,
        REAL_ARITH_TAC, SELECT_CONV, SET_RULE, .. } := D.cn.cx.cvx
  let { REAL_LT_RMUL_EQ, SELECT_UNIQUE, .. } := D.cn.cx.cpx
  let { FORALL_AND_THM, .. } := D.cn.cx.cvx.core1
  let { IMP_CONJ, .. } := D.cn.cx.cvx.core2
  let { IN_ELIM_THM, REAL_ABS_MUL, REAL_DIV_REFL, .. } := D.cn.cx.cvx.core3
  let { REAL_LT_IMP_LE, REAL_LT_LE, REAL_LT_REFL, .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_NOT_LT, REAL_OF_NUM_EQ,
        .. } := D.cn.cx.cvx.core5
  let { REAL_ABS_NORM, .. } := D.cn.cx.cvx.vec3
  let { CONTINUOUS_AT_IMP_CONTINUOUS_ON, .. } := D.cn.cx.cvx.top2
  let { OPEN_INTER, .. } := D.cn.cx.cvx.top5
  let { CONTINUOUS_AT_WITHIN, .. } := D.cn.ms.ig.dv.qtopology1
  -- @@SCOPE END

  let clog ← new_definition
   r"clog z = @w. cexp(w) = z /\ --pi < Im(w) /\ Im(w) <= pi"

  let EXISTS_COMPLEX' ← prove
   r"!P. (?z. P (Re z) (Im z)) <=> ?x y. P x y"
   (MESON_TAC [RE, IM, COMPLEX])

  let CLOG_WORKS ← prove
   r"!z. ~(z = Cx(&0))
       ==> cexp(clog z) = z /\ --pi < Im(clog z) /\ Im(clog z) <= pi"
   (GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [clog] THEN CONV_TAC SELECT_CONV THEN
    MP_TAC (← SPEC (← q r"z / Cx(norm z)") COMPLEX_UNIMODULAR_POLAR) THEN ANTS_TAC THENL
     [ASM_SIMP_TAC [COMPLEX_NORM_DIV, COMPLEX_NORM_CX] THEN
      ASM_SIMP_TAC [REAL_ABS_NORM, REAL_DIV_REFL, COMPLEX_NORM_ZERO],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"x:real") STRIP_ASSUME_TAC) THEN
    MP_TAC (← SPEC (← q r"x:real") SINCOS_PRINCIPAL_VALUE) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"y:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"complex(log(norm(z:complex)),y)") THEN
    ASM_REWRITE_TAC [RE, IM, CEXP_COMPLEX] THEN
    REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o SYM)) THEN
    ASM_SIMP_TAC [EXP_LOG, COMPLEX_NORM_NZ, COMPLEX_DIV_LMUL,
                  COMPLEX_NORM_ZERO, CX_INJ])

  let CEXP_CLOG ← prove
   r"!z. ~(z = Cx(&0)) ==> cexp(clog z) = z"
   (SIMP_TAC [CLOG_WORKS])

  let CLOG_CEXP ← prove
   r"!z. --pi < Im(z) /\ Im(z) <= pi ==> clog(cexp z) = z"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [clog] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC (← q r"w:complex") THEN
    EQ_TAC THEN ASM_SIMP_TAC [] THEN REWRITE_TAC [CEXP_EQ] THEN
    REWRITE_TAC [IMP_CONJ] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"n:real")
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    REWRITE_TAC [IM_ADD, IM_MUL_II, RE_CX] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"n = &0") THEN ASM_REWRITE_TAC [REAL_MUL_LZERO] THEN
    REWRITE_TAC [REAL_MUL_RZERO, COMPLEX_ADD_RID, COMPLEX_MUL_LZERO] THEN
    SUBGOAL_THEN (← q r"abs(n * pi) < &1 * pi") MP_TAC THENL
     [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    ASM_SIMP_TAC [REAL_ABS_MUL, REAL_LT_RMUL_EQ, PI_POS, REAL_ABS_PI] THEN
    ASM_MESON_TAC [REAL_ABS_INTEGER_LEMMA, REAL_NOT_LT])

  let CLOG_EQ ← prove
   r"!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0)) ==> (clog w = clog z <=> w = z)"
   (MESON_TAC [CEXP_CLOG])

  let CLOG_UNIQUE ← prove
   r"!w z. --pi < Im(z) /\ Im(z) <= pi /\ cexp(z) = w ==> clog w = z"
   (MESON_TAC [CLOG_CEXP])

  let RE_CLOG ← prove
   r"!z. ~(z = Cx(&0)) ==> Re(clog z) = log(norm z)"
   (REPEAT STRIP_TAC THEN FIRST_X_ASSUM
     (MP_TAC o AP_TERM (← q r"norm:complex->real") o MATCH_MP CEXP_CLOG) THEN
    REWRITE_TAC [NORM_CEXP] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [LOG_EXP])

  let EXISTS_COMPLEX_ROOT ← prove
   r"!a n. ~(n = 0) ==> ?z. z pow n = a"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"a = Cx(&0)") THENL
     [EXISTS_TAC (← q r"Cx(&0)") THEN ASM_REWRITE_TAC [COMPLEX_POW_ZERO],
      EXISTS_TAC (← q r"cexp(clog(a) / Cx(&n))") THEN REWRITE_TAC [← GSYM CEXP_N] THEN
      ASM_SIMP_TAC [COMPLEX_DIV_LMUL, CX_INJ, REAL_OF_NUM_EQ, CEXP_CLOG]])

  let HAS_COMPLEX_DERIVATIVE_CLOG ← prove
   r"!z. (Im(z) = &0 ==> &0 < Re(z))
       ==> (clog has_complex_derivative inv(z)) (at z)"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_INVERSE_STRONG_X THEN
    EXISTS_TAC (← q r"cexp") THEN
    EXISTS_TAC (← q r"{w | --pi < Im(w) /\ Im(w) < pi}") THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    ASM_CASES_TAC (← q r"z = Cx(&0)") THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
       ASM_REWRITE_TAC [RE_CX, IM_CX, REAL_LT_REFL],
       ALL_TAC] THEN
    ASM_SIMP_TAC [CONTINUOUS_ON_CEXP, CEXP_CLOG, CLOG_CEXP, REAL_LT_IMP_LE] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [← SET_RULE (← q r"{x | p x /\ q x} = {x | p x} INTER {x | q x}")] THEN
      MATCH_MP_TAC OPEN_INTER THEN
      REWRITE_TAC [← REAL_ARITH (← q r"--x < w <=> w > --x")] THEN
      REWRITE_TAC [OPEN_HALFSPACE_IM_LT, OPEN_HALFSPACE_IM_GT],
      ASM_SIMP_TAC [CLOG_WORKS],
      ASM_SIMP_TAC [CLOG_WORKS, REAL_LT_LE] THEN
      DISCH_THEN (fun th =>
        FIRST_X_ASSUM (SUBST_ALL_TAC o SYM o MATCH_MP CEXP_CLOG) THEN
        POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
      ASM_REWRITE_TAC [EULER, COS_PI, SIN_PI, COMPLEX_MUL_RZERO] THEN
      REWRITE_TAC [COMPLEX_ADD_RID, CX_NEG, COMPLEX_MUL_RNEG] THEN
      REWRITE_TAC [COMPLEX_MUL_RID, IM_NEG, IM_CX, RE_NEG, RE_CX] THEN
      MP_TAC (← SPEC (← q r"Re(clog z)") REAL_EXP_POS_LT) THEN REAL_ARITH_TAC,
      ASM_MESON_TAC [HAS_COMPLEX_DERIVATIVE_CEXP, CEXP_CLOG]])

  let COMPLEX_DIFFERENTIABLE_AT_CLOG ← prove
   r"!z. (Im(z) = &0 ==> &0 < Re(z)) ==> clog complex_differentiable at z"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_CLOG])

  let COMPLEX_DIFFERENTIABLE_WITHIN_CLOG ← prove
   r"!s z. (Im(z) = &0 ==> &0 < Re(z))
         ==> clog complex_differentiable (at z within s)"
   (MESON_TAC [COMPLEX_DIFFERENTIABLE_AT_WITHIN,
               COMPLEX_DIFFERENTIABLE_AT_CLOG])

  add_complex_differentiation_theorems
   (CONJUNCTS (← REWRITE_RULE [FORALL_AND_THM]
     (← MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
               HAS_COMPLEX_DERIVATIVE_CLOG)))

  let CONTINUOUS_AT_CLOG ← prove
   r"!z. (Im(z) = &0 ==> &0 < Re(z)) ==> clog continuous at z"
   (MESON_TAC [HAS_COMPLEX_DERIVATIVE_CLOG,
               HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT])

  let CONTINUOUS_WITHIN_CLOG ← prove
   r"!s z. (Im(z) = &0 ==> &0 < Re(z)) ==> clog continuous (at z within s)"
   (MESON_TAC [CONTINUOUS_AT_WITHIN, CONTINUOUS_AT_CLOG])

  let CONTINUOUS_ON_CLOG ← prove
   r"!s. (!z. z IN s /\ Im(z) = &0 ==> &0 < Re(z)) ==> clog continuous_on s"
   (MESON_TAC [CONTINUOUS_AT_IMP_CONTINUOUS_ON, CONTINUOUS_AT_CLOG])

  let HOLOMORPHIC_ON_CLOG ← prove
   r"!s. (!z. z IN s /\ Im(z) = &0 ==> &0 < Re(z)) ==> clog holomorphic_on s"
   (REWRITE_TAC [holomorphic_on] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN, HAS_COMPLEX_DERIVATIVE_CLOG])

  let CX_LOG ← prove
   r"!z. &0 < z ==> Cx(log z) = clog(Cx z)"
   (REPEAT STRIP_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
       [← SYM (← MATCH_MP EXP_LOG th)])) THEN
    REWRITE_TAC [CX_EXP] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CLOG_CEXP THEN REWRITE_TAC [IM_CX] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC)

  pure { clog, EXISTS_COMPLEX', CLOG_WORKS, CEXP_CLOG, CLOG_CEXP, CLOG_EQ, CLOG_UNIQUE,
         RE_CLOG, EXISTS_COMPLEX_ROOT, HAS_COMPLEX_DERIVATIVE_CLOG,
         COMPLEX_DIFFERENTIABLE_AT_CLOG, COMPLEX_DIFFERENTIABLE_WITHIN_CLOG,
         CONTINUOUS_AT_CLOG, CONTINUOUS_WITHIN_CLOG, CONTINUOUS_ON_CLOG,
         HOLOMORPHIC_ON_CLOG, CX_LOG }
/- ------------------------------------------------------------------------- -/
/- Quadrant-type results for clog; various properties; relation between    -/
/- square root and exp/log, and hence its derivative.                       -/
/- (transcendentals.ml 3678-3947)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSN where
  RE_CLOG_POS_LT : thm
  RE_CLOG_POS_LE : thm
  IM_CLOG_POS_LT : thm
  IM_CLOG_POS_LE : thm
  RE_CLOG_POS_LT_IMP : thm
  IM_CLOG_POS_LT_IMP : thm
  IM_CLOG_EQ_0 : thm
  IM_CLOG_EQ_PI : thm
  CNJ_CLOG : thm
  CLOG_INV : thm
  CLOG_1 : thm
  CLOG_NEG_1 : thm
  CLOG_II : thm
  CLOG_NEG_II : thm
  CSQRT_CEXP_CLOG : thm
  CNJ_CSQRT : thm
  HAS_COMPLEX_DERIVATIVE_CSQRT : thm
  COMPLEX_DIFFERENTIABLE_AT_CSQRT : thm
  COMPLEX_DIFFERENTIABLE_WITHIN_CSQRT : thm
  CONTINUOUS_AT_CSQRT : thm
  CONTINUOUS_WITHIN_CSQRT : thm
  CONTINUOUS_ON_CSQRT : thm
  HOLOMORPHIC_ON_CSQRT : thm
  CONTINUOUS_WITHIN_CSQRT_POSREAL : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSN [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) (BTSB : TSB) (BTSC : TSC) (BTSE : TSE) (BTSF : TSF) (BTSM : TSM) : ExceptT String IO TSN := do
  -- @@SCOPE BEGIN
  let { CEXP_0, CEXP_N, CEXP_NEG, .. } := BTSA
  let { CEXP_EULER, CNJ_CEXP, REAL_EXP_NZ, REAL_EXP_POS_LT, .. } := BTSB
  let { COS_ADD, COS_SUB, CX_COS, CX_SIN, IM_CEXP, RE_CEXP, SIN_ADD, SIN_SUB, .. } := BTSC
  let { COS_PI, COS_PI2, COS_POS_PI, COS_POS_PI_LE, PI_POS, SIN_PI, SIN_PI2, SIN_POS_PI,
        SIN_POS_PI_LE, .. } := BTSE
  let { COMPLEX_EQ_CEXP, .. } := BTSF
  let { CEXP_CLOG, CLOG_CEXP, CLOG_WORKS, .. } := BTSM
  let { CLOSED_HALFSPACE_RE_GE, CLOSED_REAL_SET, .. } := D.kna
  let { complex_differentiable, COMPLEX_DIFFERENTIABLE_AT_WITHIN,
        HAS_COMPLEX_DERIVATIVE_AT_WITHIN, HAS_COMPLEX_DERIVATIVE_CHAIN,
        HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT, HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT,
        holomorphic_on, .. } := D.kne
  let { add_complex_differentiation_theorems, COMPLEX_DIFF_TAC, .. } := D.knk
  let { CONTINUOUS_WITHIN_CLOSED_NONTRIVIAL, .. } := D.qtopology
  let { REAL_SUB_RNEG, .. } := D.qsession
  let { COMPLEX_EQ, .. } := D.cn.cxa
  let { COMPLEX_ADD_LID, COMPLEX_ADD_RID, COMPLEX_MUL_LNEG, COMPLEX_MUL_RID,
        COMPLEX_MUL_RZERO, .. } := D.cn.cxb
  let { COMPLEX_NORM_CX, COMPLEX_VEC_0, CX_INJ, CX_NEG, CX_SUB, IM_CX, IM_DIV_CX, IM_II,
        IM_MUL_II, IM_NEG, RE_CX, RE_II, .. } := D.cn.cxc
  let { COMPLEX_RING, .. } := D.cn.cxd
  let { COMPLEX_FIELD, .. } := D.cn.cxe
  let { COMPLEX_DIV_LMUL, COMPLEX_INV_EQ_0, COMPLEX_NORM_NZ, .. } := D.cn.cxf
  let { CNJ_CX, CNJ_DIV, CNJ_EQ_CX, IM_CNJ, .. } := D.cn.cxg
  let { CSQRT, CSQRT_0, CSQRT_UNIQUE, CX_SQRT, .. } := D.cn.cxh
  let { FORALL_REAL, .. } := D.cn.cxi
  let { ASM_REAL_ARITH_TAC, MESON_TAC, NORM_ARITH_TAC, REAL_ARITH, REAL_ARITH_TAC,
        SET_RULE, .. } := D.cn.cx.cvx
  let { SQRT_MONO_LT, .. } := D.cn.cx.cpx
  let { ARITH, FORALL_AND_THM, .. } := D.cn.cx.cvx.core1
  let { IMP_CONJ, .. } := D.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INTER, NOT_IMP, POW_2_SQRT, .. } := D.cn.cx.cvx.core3
  let { REAL_ENTIRE, REAL_LE_LT, REAL_LE_MUL_EQ, REAL_LE_REFL, REAL_LT_IMP_LE,
        REAL_LT_MUL_EQ, REAL_LT_REFL, .. } := D.cn.cx.cvx.core4
  let { REAL_NOT_LT, REAL_OF_NUM_EQ, REAL_POS, REAL_POW_LT, REAL_SUB_RZERO, SQRT_0,
        SQRT_POS_LE, .. } := D.cn.cx.cvx.core5
  let { real_abs, real_ge, .. } := D.cn.cx.cvx.core6
  let { dist, .. } := D.cn.cx.cvx.vec4
  let { CLOSED_INTER, .. } := D.cn.cx.cvx.top1
  let { CONTINUOUS_AT_IMP_CONTINUOUS_ON, .. } := D.cn.cx.cvx.top2
  let { continuous_within, .. } := D.cn.cx.cvx.top5
  let { CONTINUOUS_AT_WITHIN, .. } := D.cn.ms.ig.dv.qtopology1
  -- @@SCOPE END

  let RE_CLOG_POS_LT ← prove
   r"!z. ~(z = Cx(&0)) ==> (abs(Im(clog z)) < pi / &2 <=> &0 < Re(z))"
   (GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP CLOG_WORKS) THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (fun th => tactic_of do pure (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [← SYM th]))
      MP_TAC) THEN
    SIMP_TAC [RE_CEXP, REAL_LT_MUL_EQ, REAL_EXP_POS_LT] THEN
    SPEC_TAC (← q r"clog z", ← q r"z:complex") THEN GEN_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP (← REAL_ARITH
     (← q r"--p < x /\ x <= p
      ==> --(p / &2) < x /\ x < p / &2 \/
          --(p / &2) <= p + x /\ p + x <= p / &2 \/
          --(p / &2) <= x - p /\ x - p <= p / &2"))) THEN
    DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
    (FIRST_ASSUM (MP_TAC o MATCH_MP COS_POS_PI) ORELSE
     FIRST_ASSUM (MP_TAC o MATCH_MP COS_POS_PI_LE)) THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    REWRITE_TAC [COS_ADD, COS_SUB, COS_PI, SIN_PI] THEN
    REAL_ARITH_TAC)

  let RE_CLOG_POS_LE ← prove
   r"!z. ~(z = Cx(&0)) ==> (abs(Im(clog z)) <= pi / &2 <=> &0 <= Re(z))"
   (GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP CLOG_WORKS) THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (fun th => tactic_of do pure (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [← SYM th]))
      MP_TAC) THEN
    SIMP_TAC [RE_CEXP, REAL_LE_MUL_EQ, REAL_EXP_POS_LT] THEN
    SPEC_TAC (← q r"clog z", ← q r"z:complex") THEN GEN_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP (← REAL_ARITH
     (← q r"--p < x /\ x <= p
      ==> --(p / &2) <= x /\ x <= p / &2 \/
          --(p / &2) < p + x /\ p + x < p / &2 \/
          --(p / &2) < x - p /\ x - p < p / &2"))) THEN
    DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
    (FIRST_ASSUM (MP_TAC o MATCH_MP COS_POS_PI) ORELSE
     FIRST_ASSUM (MP_TAC o MATCH_MP COS_POS_PI_LE)) THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    REWRITE_TAC [COS_ADD, COS_SUB, COS_PI, SIN_PI] THEN
    REAL_ARITH_TAC)

  let IM_CLOG_POS_LT ← prove
   r"!z. ~(z = Cx(&0)) ==> (&0 < Im(clog z) /\ Im(clog z) < pi <=> &0 < Im(z))"
   (GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP CLOG_WORKS) THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (fun th => tactic_of do pure (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [← SYM th]))
      MP_TAC) THEN
    SIMP_TAC [IM_CEXP, REAL_LT_MUL_EQ, REAL_EXP_POS_LT] THEN
    SPEC_TAC (← q r"clog z", ← q r"z:complex") THEN GEN_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP (← REAL_ARITH
     (← q r"--p < x /\ x <= p
      ==> &0 < x /\ x < p \/
          &0 <= x + p /\ x + p <= p \/
          &0 <= x - p /\ x - p <= p"))) THEN
    DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
    (FIRST_ASSUM (MP_TAC o MATCH_MP SIN_POS_PI) ORELSE
     FIRST_ASSUM (MP_TAC o MATCH_MP SIN_POS_PI_LE)) THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    REWRITE_TAC [SIN_ADD, SIN_SUB, COS_PI, SIN_PI] THEN
    REAL_ARITH_TAC)

  let IM_CLOG_POS_LE ← prove
   r"!z. ~(z = Cx(&0)) ==> (&0 <= Im(clog z) <=> &0 <= Im(z))"
   (GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP CLOG_WORKS) THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (fun th => tactic_of do pure (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [← SYM th]))
      MP_TAC) THEN
    SIMP_TAC [IM_CEXP, REAL_LE_MUL_EQ, REAL_EXP_POS_LT] THEN
    SPEC_TAC (← q r"clog z", ← q r"z:complex") THEN GEN_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP (← REAL_ARITH
     (← q r"--p < x /\ x <= p
      ==> &0 <= x /\ x <= p \/
          &0 < x + p /\ x + p < p \/
          &0 < p - x /\ p - x < p"))) THEN
    DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
    (FIRST_ASSUM (MP_TAC o MATCH_MP SIN_POS_PI) ORELSE
     FIRST_ASSUM (MP_TAC o MATCH_MP SIN_POS_PI_LE)) THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    REWRITE_TAC [SIN_ADD, SIN_SUB, COS_PI, SIN_PI] THEN
    REAL_ARITH_TAC)

  let RE_CLOG_POS_LT_IMP ← prove
   r"!z. &0 < Re(z) ==> abs(Im(clog z)) < pi / &2"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"z = Cx(&0)") THEN
    ASM_SIMP_TAC [RE_CLOG_POS_LT, RE_CX, REAL_LT_REFL])

  let IM_CLOG_POS_LT_IMP ← prove
   r"!z. &0 < Im(z) ==> &0 < Im(clog z) /\ Im(clog z) < pi"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"z = Cx(&0)") THEN
    ASM_SIMP_TAC [IM_CLOG_POS_LT, IM_CX, REAL_LT_REFL])

  let IM_CLOG_EQ_0 ← prove
   r"!z. ~(z = Cx(&0)) ==> (Im(clog z) = &0 <=> &0 < Re(z) /\ Im(z) = &0)"
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
     [← REAL_ARITH (← q r"z = &0 <=> &0 <= z /\ ~(&0 < z)")] THEN
    ASM_SIMP_TAC [← GSYM RE_CLOG_POS_LT, ← GSYM IM_CLOG_POS_LE,
                  ← GSYM IM_CLOG_POS_LT] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC)

  let IM_CLOG_EQ_PI ← prove
   r"!z. ~(z = Cx(&0)) ==> (Im(clog z) = pi <=> Re(z) < &0 /\ Im(z) = &0)"
   (SIMP_TAC [PI_POS, RE_CLOG_POS_LE, IM_CLOG_POS_LE, IM_CLOG_POS_LT, CLOG_WORKS,
              ← REAL_ARITH (← q r"&0 < pi ==> (x = pi <=> (&0 <= x /\ x <= pi) /\
                              ~(abs x <= pi / &2) /\ ~(&0 < x /\ x < pi))")] THEN
    REAL_ARITH_TAC)

  let CNJ_CLOG ← prove
   r"!z. (Im z = &0 ==> &0 < Re z) ==> cnj(clog z) = clog(cnj z)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"z = Cx(&0)") THEN
    ASM_REWRITE_TAC [RE_CX, IM_CX, REAL_LT_REFL] THEN
    DISCH_TAC THEN MATCH_MP_TAC COMPLEX_EQ_CEXP THEN
    REWRITE_TAC [← GSYM CNJ_CEXP] THEN
    ASM_SIMP_TAC [CEXP_CLOG, CNJ_EQ_CX, IM_CNJ] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"(--p < x /\ x <= p) /\ (--p < y /\ y <= p) /\
      ~(x = p /\ y = p)
      ==> abs(--x - y) < &2 * p")) THEN
    ASM_SIMP_TAC [IM_CLOG_EQ_PI, CNJ_EQ_CX, CLOG_WORKS] THEN
    ASM_REAL_ARITH_TAC)

  let CLOG_INV ← prove
   r"!z. (Im(z) = &0 ==> &0 < Re z) ==> clog(inv z) = --(clog z)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"z = Cx(&0)") THEN
    ASM_REWRITE_TAC [RE_CX, IM_CX, REAL_LT_REFL] THEN
    STRIP_TAC THEN MATCH_MP_TAC COMPLEX_EQ_CEXP THEN
    ASM_SIMP_TAC [CEXP_CLOG, CEXP_NEG, COMPLEX_INV_EQ_0] THEN
    REWRITE_TAC [IM_NEG, REAL_SUB_RNEG] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"--pi < x /\ x <= pi /\ --pi < y /\ y <= pi /\
      ~(x = pi /\ y = pi) ==> abs(x + y) < &2 * pi")) THEN
    ASM_SIMP_TAC [CLOG_WORKS, COMPLEX_INV_EQ_0, IM_CLOG_EQ_PI] THEN
    UNDISCH_TAC (← q r"Im z = &0 ==> &0 < Re z") THEN
    ASM_CASES_TAC (← q r"Im z = &0") THEN ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC)

  let CLOG_1 ← prove
   r"clog(Cx(&1)) = Cx(&0)"
   (REWRITE_TAC [← GSYM CEXP_0] THEN MATCH_MP_TAC CLOG_CEXP THEN
    REWRITE_TAC [IM_CX] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC)

  let CLOG_NEG_1 ← prove
   r"clog(--Cx(&1)) = ii * Cx pi"
   (MATCH_MP_TAC COMPLEX_EQ_CEXP THEN REWRITE_TAC [← GSYM CX_NEG] THEN
    SIMP_TAC [CEXP_EULER, ← GSYM CX_COS, ← GSYM CX_SIN, IM_MUL_II, IM_CX, RE_CX] THEN
    REWRITE_TAC [COS_PI, SIN_PI, COMPLEX_MUL_RZERO, COMPLEX_ADD_RID] THEN
    SIMP_TAC [CLOG_WORKS, ← ExceptT.mk (COMPLEX_RING (← q r"~(Cx(-- &1) = Cx(&0))")),
              ← REAL_ARITH (← q r"--pi < x /\ x <= pi ==> abs(x - pi) < &2 * pi")])

  let CLOG_II ← prove
   r"clog ii = ii * Cx(pi / &2)"
   (MP_TAC (← SPEC (← q r"ii * Cx(pi / &2)") CLOG_CEXP) THEN
    SIMP_TAC [CEXP_EULER, ← GSYM CX_COS, ← GSYM CX_SIN, IM_MUL_II, IM_CX, RE_CX] THEN
    REWRITE_TAC [COS_PI2, SIN_PI2] THEN ANTS_TAC THENL
     [MP_TAC PI_POS THEN REAL_ARITH_TAC,
      REWRITE_TAC [COMPLEX_ADD_LID, COMPLEX_MUL_RID]])

  let CLOG_NEG_II ← prove
   r"clog(--ii) = --ii * Cx(pi / &2)"
   (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← ExceptT.mk (COMPLEX_FIELD (← q r"--ii = inv ii"))] THEN
    SIMP_TAC [CLOG_INV, RE_II, IM_II, REAL_OF_NUM_EQ, ARITH, CLOG_II] THEN
    REWRITE_TAC [COMPLEX_MUL_LNEG])

  let CSQRT_CEXP_CLOG ← prove
   r"!z. ~(z = Cx(&0)) ==> csqrt z = cexp(clog(z) / Cx(&2))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC CSQRT_UNIQUE THEN
    REWRITE_TAC [← GSYM CEXP_N, RE_CEXP, IM_CEXP] THEN
    ASM_SIMP_TAC [COMPLEX_DIV_LMUL, CX_INJ, REAL_OF_NUM_EQ, ARITH, CEXP_CLOG] THEN
    SIMP_TAC [REAL_LT_MUL_EQ, REAL_EXP_POS_LT, REAL_LE_MUL_EQ] THEN
    REWRITE_TAC [REAL_ENTIRE, REAL_EXP_NZ, IM_DIV_CX] THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o CONJUNCT2 o MATCH_MP CLOG_WORKS) THEN
    FIRST_X_ASSUM (DISJ_CASES_TAC o REWRITE_RULE [REAL_LE_LT]) THENL
     [DISJ1_TAC THEN MATCH_MP_TAC COS_POS_PI THEN
      ASM_REAL_ARITH_TAC,
      DISJ2_TAC THEN ASM_REWRITE_TAC [COS_PI2, SIN_PI2, REAL_POS]])

  let CNJ_CSQRT ← prove
   r"!z. (Im z = &0 ==> &0 <= Re(z)) ==> cnj(csqrt z) = csqrt(cnj z)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"z = Cx(&0)") THEN
    ASM_REWRITE_TAC [CSQRT_0, CNJ_CX] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"Im z = &0 ==> &0 < Re(z)") ASSUME_TAC THENL
     [REPEAT (POP_ASSUM MP_TAC) THEN
      REWRITE_TAC [COMPLEX_EQ, IM_CX, RE_CX] THEN REAL_ARITH_TAC,
      ASM_REWRITE_TAC [RE_CX, IM_CX, REAL_LT_REFL] THEN
      ASM_SIMP_TAC [CSQRT_CEXP_CLOG, CNJ_CEXP, CNJ_CLOG,
                    CNJ_DIV, CNJ_EQ_CX, CNJ_CX]])

  let HAS_COMPLEX_DERIVATIVE_CSQRT ← prove
   r"!z. (Im z = &0 ==> &0 < Re(z))
       ==> (csqrt has_complex_derivative inv(Cx(&2) * csqrt z)) (at z)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"z = Cx(&0)") THEN
    ASM_REWRITE_TAC [IM_CX, RE_CX, REAL_LT_REFL] THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [← q r"\z. cexp(clog(z) / Cx(&2))", ← q r"norm(z:complex)"] THEN
    ASM_REWRITE_TAC [COMPLEX_NORM_NZ] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC CSQRT_CEXP_CLOG THEN REWRITE_TAC [← GSYM COMPLEX_VEC_0] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN NORM_ARITH_TAC,
      COMPLEX_DIFF_TAC THEN ASM_SIMP_TAC [← GSYM CSQRT_CEXP_CLOG] THEN
      UNDISCH_TAC (← q r"~(z = Cx(&0))") THEN MP_TAC (← SPEC (← q r"z:complex") CSQRT) THEN
      CONV_TAC COMPLEX_FIELD])

  let COMPLEX_DIFFERENTIABLE_AT_CSQRT ← prove
   r"!z. (Im z = &0 ==> &0 < Re(z)) ==> csqrt complex_differentiable at z"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_CSQRT])

  let COMPLEX_DIFFERENTIABLE_WITHIN_CSQRT ← prove
   r"!s z. (Im z = &0 ==> &0 < Re(z))
         ==> csqrt complex_differentiable (at z within s)"
   (MESON_TAC [COMPLEX_DIFFERENTIABLE_AT_WITHIN,
               COMPLEX_DIFFERENTIABLE_AT_CSQRT])

  add_complex_differentiation_theorems
   (CONJUNCTS (← REWRITE_RULE [FORALL_AND_THM]
     (← MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
               HAS_COMPLEX_DERIVATIVE_CSQRT)))

  let CONTINUOUS_AT_CSQRT ← prove
   r"!z. (Im z = &0 ==> &0 < Re(z)) ==> csqrt continuous at z"
   (MESON_TAC [HAS_COMPLEX_DERIVATIVE_CSQRT,
               HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT])

  let CONTINUOUS_WITHIN_CSQRT ← prove
   r"!s z. (Im z = &0 ==> &0 < Re(z)) ==> csqrt continuous (at z within s)"
   (MESON_TAC [CONTINUOUS_AT_WITHIN, CONTINUOUS_AT_CSQRT])

  let CONTINUOUS_ON_CSQRT ← prove
   r"!s. (!z. z IN s /\ Im z = &0 ==> &0 < Re(z)) ==> csqrt continuous_on s"
   (MESON_TAC [CONTINUOUS_AT_IMP_CONTINUOUS_ON, CONTINUOUS_AT_CSQRT])

  let HOLOMORPHIC_ON_CSQRT ← prove
   r"!s. (!z. z IN s /\ Im(z) = &0 ==> &0 < Re(z)) ==> csqrt holomorphic_on s"
   (REWRITE_TAC [holomorphic_on] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN, HAS_COMPLEX_DERIVATIVE_CSQRT])

  let CONTINUOUS_WITHIN_CSQRT_POSREAL ← prove
   r"!z. csqrt continuous (at z within {w | real w /\ &0 <= Re(w)})"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"Im z = &0 ==> &0 < Re(z)") THENL
     [ASM_SIMP_TAC [CONTINUOUS_WITHIN_CSQRT], ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [NOT_IMP, REAL_NOT_LT] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"x <= &0 <=> x < &0 \/ x = &0")] THEN STRIP_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_WITHIN_CLOSED_NONTRIVIAL THEN
      REWRITE_TAC [← SET_RULE (← q r"{x | P x /\ Q x} = {x | P x} INTER {x | Q x}")] THEN
      SIMP_TAC [CLOSED_REAL_SET, CLOSED_INTER, IN_INTER, IN_ELIM_THM,
                ← REWRITE_RULE [real_ge] CLOSED_HALFSPACE_RE_GE] THEN
      ASM_REAL_ARITH_TAC,
      SUBGOAL_THEN (← q r"z = Cx(&0)") SUBST_ALL_TAC THENL
       [ASM_REWRITE_TAC [COMPLEX_EQ, RE_CX, IM_CX], ALL_TAC] THEN
      REWRITE_TAC [continuous_within] THEN
      REWRITE_TAC [IN_ELIM_THM, IMP_CONJ, FORALL_REAL, RE_CX] THEN
      SIMP_TAC [← GSYM CX_SQRT, REAL_LE_REFL] THEN
      SIMP_TAC [dist, ← GSYM CX_SUB, COMPLEX_NORM_CX, SQRT_0, REAL_SUB_RZERO] THEN
      X_GEN_TAC (← q r"e:real") THEN STRIP_TAC THEN EXISTS_TAC (← q r"(e:real) pow 2") THEN
      ASM_SIMP_TAC [REAL_POW_LT] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"e = sqrt(e pow 2)") SUBST1_TAC THENL
       [ASM_SIMP_TAC [POW_2_SQRT, REAL_LT_IMP_LE],
        ASM_SIMP_TAC [real_abs, SQRT_POS_LE]] THEN
      MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC])

  pure { RE_CLOG_POS_LT, RE_CLOG_POS_LE, IM_CLOG_POS_LT, IM_CLOG_POS_LE,
         RE_CLOG_POS_LT_IMP, IM_CLOG_POS_LT_IMP, IM_CLOG_EQ_0, IM_CLOG_EQ_PI,
         CNJ_CLOG, CLOG_INV, CLOG_1, CLOG_NEG_1, CLOG_II, CLOG_NEG_II, CSQRT_CEXP_CLOG,
         CNJ_CSQRT, HAS_COMPLEX_DERIVATIVE_CSQRT, COMPLEX_DIFFERENTIABLE_AT_CSQRT,
         COMPLEX_DIFFERENTIABLE_WITHIN_CSQRT, CONTINUOUS_AT_CSQRT,
         CONTINUOUS_WITHIN_CSQRT, CONTINUOUS_ON_CSQRT, HOLOMORPHIC_ON_CSQRT,
         CONTINUOUS_WITHIN_CSQRT_POSREAL }
/- ------------------------------------------------------------------------- -/
/- Complex powers; product rule.                                            -/
/- (transcendentals.ml 3948-4197)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSO where
  cpow : thm
  CPOW_0 : thm
  CPOW_N : thm
  CPOW_1 : thm
  CPOW_ADD : thm
  CPOW_SUC : thm
  CPOW_NEG : thm
  CPOW_SUB : thm
  CEXP_MUL_CPOW : thm
  CPOW_EQ_0 : thm
  NORM_CPOW_REAL : thm
  CPOW_REAL_REAL : thm
  NORM_CPOW_REAL_MONO : thm
  CPOW_MUL_REAL : thm
  HAS_COMPLEX_DERIVATIVE_CPOW : thm
  HAS_COMPLEX_DERIVATIVE_CPOW_RIGHT : thm
  COMPLEX_DIFFERENTIABLE_CPOW_RIGHT : thm
  HOLOMORPHIC_ON_CPOW_RIGHT : thm
  CONTINUOUS_ON_CPOW_RIGHT : thm
  CLOG_MUL : thm
  CLOG_MUL_SIMPLE : thm
  CLOG_MUL_CX : thm
  CLOG_MUL_POS : thm
  CLOG_DIV_POS : thm
  CLOG_NEG : thm
  CLOG_MUL_II : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSO [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) (BTSB : TSB) (BTSC : TSC) (BTSD : TSD) (BTSE : TSE) (BTSF : TSF) (BTSM : TSM) (BTSN : TSN) : ExceptT String IO TSO := do
  -- @@SCOPE BEGIN
  let { CEXP_0, CEXP_ADD, CEXP_N, CEXP_NEG, CEXP_NZ, CEXP_SUB, .. } := BTSA
  let { CEXP_EULER, CX_EXP, REAL_EXP_MONO_LE, .. } := BTSB
  let { CX_COS, CX_SIN, .. } := BTSC
  let { LOG_MUL, LOG_POS_LT, .. } := BTSD
  let { COS_NPI, PI_POS, SIN_NPI, .. } := BTSE
  let { NORM_CEXP, .. } := BTSF
  let { CEXP_CLOG, CLOG_CEXP, CLOG_UNIQUE, CLOG_WORKS, CX_LOG, .. } := BTSM
  let { CLOG_1, CLOG_II, CLOG_INV, CLOG_NEG_1, IM_CLOG_EQ_PI, IM_CLOG_POS_LE,
        IM_CLOG_POS_LT, RE_CLOG_POS_LE, RE_CLOG_POS_LT, .. } := BTSN
  let { complex_differentiable, COMPLEX_DIFFERENTIABLE_AT_WITHIN,
        HAS_COMPLEX_DERIVATIVE_CHAIN, HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT, holomorphic_on,
        HOLOMORPHIC_ON_IMP_CONTINUOUS_ON, .. } := D.kne
  let { COMPLEX_DIFFERENTIABLE_CONST, .. } := D.kng
  let { HOLOMORPHIC_ON_COMPOSE, .. } := D.knh
  let { add_complex_differentiation_theorems, COMPLEX_DIFF_TAC, .. } := D.knk
  let { complex_div, complex_sub, SIMPLE_COMPLEX_ARITH, .. } := D.cn.cxa
  let { COMPLEX_ADD_LDISTRIB, COMPLEX_ADD_RDISTRIB, COMPLEX_MUL_LID, COMPLEX_MUL_LNEG,
        COMPLEX_MUL_LZERO, COMPLEX_MUL_RZERO, COMPLEX_MUL_SYM, COMPLEX_SUB_LZERO,
        COMPLEX_SUB_RDISTRIB, .. } := D.cn.cxb
  let { COMPLEX_ENTIRE, COMPLEX_POW_1, CX_ADD, CX_DIV, CX_INJ, CX_MUL, II_NZ, IM_ADD,
        IM_CX, IM_MUL_II, IM_SUB, RE_CX, RE_MUL_CX, .. } := D.cn.cxc
  let { COMPLEX_RING, .. } := D.cn.cxd
  let { COMPLEX_FIELD, COMPLEX_INV_0, RE_COMPLEX_INV_GT_0, .. } := D.cn.cxe
  let { COMPLEX_NORM_NZ, .. } := D.cn.cxf
  let { REAL, .. } := D.cn.cxi
  let { ASM_MESON_TAC, MESON, new_definition, parse_as_infix, REAL_ARITH, REAL_ARITH_TAC,
        REAL_RAT_REDUCE_CONV, .. } := D.cn.cx.cvx
  let { ARITH_EQ, CONJ_ASSOC, ETA_AX, FORALL_AND_THM, .. } := D.cn.cx.cvx.core1
  let { REAL_ADD_LID, REAL_ADD_RID, .. } := D.cn.cx.cvx.core3
  let { REAL_LE_RMUL_EQ, REAL_LT_IMP_NZ, REAL_LT_MUL, REAL_LT_REFL,
        .. } := D.cn.cx.cvx.core4
  let { REAL_OF_NUM_EQ, .. } := D.cn.cx.cvx.core5
  let { o_DEF, .. } := D.cn.cx.cvx.core6
  let { NORM_NEG, .. } := D.cn.cx.cvx.vec3
  let { dist, .. } := D.cn.cx.cvx.vec4
  let { CONTINUOUS_ON_COMPOSE, .. } := D.cn.cx.cvx.top3
  -- @@SCOPE END

  parse_as_infix ("cpow", (24, "left"))

  let cpow ← new_definition
   r"w cpow z = if w = Cx(&0) then Cx(&0)
             else cexp(z * clog w)"

  let CPOW_0 ← prove
   r"!z. Cx(&0) cpow z = Cx(&0)"
   (REWRITE_TAC [cpow])

  let CPOW_N ← prove
   r"!z. z cpow (Cx(&n)) = if z = Cx(&0) then Cx(&0) else z pow n"
   (GEN_TAC THEN REWRITE_TAC [cpow] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [CEXP_N, CEXP_CLOG])

  let CPOW_1 ← prove
   r"!z. Cx(&1) cpow z = Cx(&1)"
   (REWRITE_TAC [cpow, CX_INJ, REAL_OF_NUM_EQ, ARITH_EQ, CLOG_1] THEN
    REWRITE_TAC [CEXP_0, COMPLEX_MUL_RZERO])

  let CPOW_ADD ← prove
   r"!w z1 z2. w cpow (z1 + z2) = w cpow z1 * w cpow z2"
   (REPEAT GEN_TAC THEN REWRITE_TAC [cpow] THEN
    ASM_CASES_TAC (← q r"w = Cx(&0)") THEN ASM_REWRITE_TAC [COMPLEX_MUL_RZERO] THEN
    REWRITE_TAC [COMPLEX_ADD_RDISTRIB, CEXP_ADD])

  let CPOW_SUC ← prove
   r"!w z. w cpow (z + Cx(&1)) = w * w cpow z"
   (REPEAT GEN_TAC THEN REWRITE_TAC [CPOW_ADD, CPOW_N] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC [COMPLEX_MUL_LZERO, COMPLEX_MUL_RZERO] THEN
    REWRITE_TAC [COMPLEX_POW_1, COMPLEX_MUL_SYM])

  let CPOW_NEG ← prove
   r"!w z. w cpow (--z) = inv(w cpow z)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [cpow] THEN ASM_CASES_TAC (← q r"w = Cx(&0)") THEN
    ASM_REWRITE_TAC [COMPLEX_MUL_RZERO, COMPLEX_INV_0] THEN
    REWRITE_TAC [COMPLEX_MUL_LNEG, CEXP_NEG])

  let CPOW_SUB ← prove
   r"!w z1 z2. w cpow (z1 - z2) = w cpow z1 / w cpow z2"
   (REWRITE_TAC [complex_sub, complex_div, CPOW_ADD, CPOW_NEG])

  let CEXP_MUL_CPOW ← prove
   r"!w z. --pi < Im w /\ Im w <= pi ==> cexp(w * z) = cexp(w) cpow z"
   (SIMP_TAC [cpow, CEXP_NZ, CLOG_CEXP] THEN
    REWRITE_TAC [COMPLEX_MUL_SYM])

  let CPOW_EQ_0 ← prove
   r"!w z. w cpow z = Cx(&0) <=> w = Cx(&0)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [cpow] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [CEXP_NZ])

  let NORM_CPOW_REAL ← prove
   r"!w z. real w /\ &0 < Re w ==> norm(w cpow z) = exp(Re z * log(Re w))"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (SUBST_ALL_TAC o SYM o GEN_REWRITE_RULE id [REAL]) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [RE_CX]) THEN
    ASM_SIMP_TAC [cpow, CX_INJ, REAL_LT_IMP_NZ] THEN
    ASM_SIMP_TAC [NORM_CEXP, ← GSYM CX_LOG, RE_MUL_CX, RE_CX])

  let CPOW_REAL_REAL ← prove
   r"!w z. real w /\ real z /\ &0 < Re w
         ==> w cpow z = Cx(exp(Re z * log(Re w)))"
   (REPEAT STRIP_TAC THEN
    REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o SYM o GEN_REWRITE_RULE id [REAL])) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [RE_CX]) THEN
    ASM_SIMP_TAC [cpow, CX_INJ, REAL_LT_IMP_NZ] THEN
    ASM_SIMP_TAC [NORM_CEXP, ← GSYM CX_LOG, RE_MUL_CX, RE_CX, CX_EXP, CX_MUL])

  let NORM_CPOW_REAL_MONO ← prove
   r"!w z1 z2. real w /\ &1 < Re w
             ==> (norm(w cpow z1) <= norm(w cpow z2) <=> Re(z1) <= Re(z2))"
   (SIMP_TAC [NORM_CPOW_REAL, ← REAL_ARITH (← q r"&1 < x ==> &0 < x")] THEN
    SIMP_TAC [REAL_EXP_MONO_LE, REAL_LE_RMUL_EQ, LOG_POS_LT])

  let CPOW_MUL_REAL ← prove
   r"!x y z. real x /\ real y /\ &0 <= Re x /\ &0 <= Re y
           ==> (x * y) cpow z = x cpow z * y cpow z"
   (REPEAT STRIP_TAC THEN
    REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o SYM o GEN_REWRITE_RULE id [REAL])) THEN
    REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [RE_CX, IM_CX] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"&0 <= x <=> x = &0 \/ &0 < x")] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [COMPLEX_MUL_LZERO, COMPLEX_MUL_RZERO, CPOW_0] THEN
    ASM_SIMP_TAC [cpow, COMPLEX_ENTIRE, CX_INJ, REAL_LT_IMP_NZ] THEN
    REWRITE_TAC [← GSYM CEXP_ADD, ← GSYM COMPLEX_ADD_LDISTRIB] THEN
    ASM_SIMP_TAC [← GSYM CX_LOG, ← GSYM CX_ADD, ← GSYM CX_MUL, REAL_LT_MUL] THEN
    ASM_SIMP_TAC [LOG_MUL])

  let HAS_COMPLEX_DERIVATIVE_CPOW ← prove
   r"!s z. (Im z = &0 ==> &0 < Re z)
         ==> ((\z. z cpow s) has_complex_derivative
              (s * z cpow (s - Cx(&1)))) (at z)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"z = Cx(&0)") THEN
    ASM_REWRITE_TAC [IM_CX, RE_CX, REAL_LT_REFL] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [cpow] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [← q r"\z. cexp (s * clog z)", ← q r"norm(z:complex)"] THEN
    ASM_REWRITE_TAC [COMPLEX_NORM_NZ] THEN CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [dist] THEN
      REWRITE_TAC [COMPLEX_SUB_LZERO, NORM_NEG, REAL_LT_REFL],
      COMPLEX_DIFF_TAC THEN ASM_REWRITE_TAC [CEXP_SUB, COMPLEX_SUB_RDISTRIB] THEN
      ASM_SIMP_TAC [CEXP_CLOG, COMPLEX_MUL_LID] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD])

  add_complex_differentiation_theorems
   (CONJUNCTS (← REWRITE_RULE [FORALL_AND_THM]
     (← GEN (← q r"s:complex")
       (← MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
                 (← SPEC (← q r"s:complex") HAS_COMPLEX_DERIVATIVE_CPOW)))))

  let HAS_COMPLEX_DERIVATIVE_CPOW_RIGHT ← prove
   r"!w z. ~(w = Cx(&0))
         ==> ((\z. w cpow z) has_complex_derivative clog(w) * w cpow z) (at z)"
   (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [cpow] THEN
    COMPLEX_DIFF_TAC THEN REWRITE_TAC [COMPLEX_MUL_LID])

  add_complex_differentiation_theorems
   (CONJUNCTS (← REWRITE_RULE [FORALL_AND_THM]
     (← GEN (← q r"s:complex")
       (← MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
                 (← SPEC (← q r"s:complex") HAS_COMPLEX_DERIVATIVE_CPOW_RIGHT)))))

  let COMPLEX_DIFFERENTIABLE_CPOW_RIGHT ← prove
   r"!w z. (\z. w cpow z) complex_differentiable (at z)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"w = Cx(&0)") THENL
     [ASM_REWRITE_TAC [cpow, COMPLEX_DIFFERENTIABLE_CONST],
      REWRITE_TAC [complex_differentiable] THEN
      ASM_MESON_TAC [HAS_COMPLEX_DERIVATIVE_CPOW_RIGHT]])

  let HOLOMORPHIC_ON_CPOW_RIGHT ← prove
   r"!w f s. f holomorphic_on s
           ==> (\z. w cpow (f z)) holomorphic_on s"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN ASM_REWRITE_TAC [] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM ETA_AX] THEN
    REWRITE_TAC [holomorphic_on, ← GSYM complex_differentiable] THEN
    ASM_SIMP_TAC [COMPLEX_DIFFERENTIABLE_CPOW_RIGHT,
                  COMPLEX_DIFFERENTIABLE_AT_WITHIN])

  let CONTINUOUS_ON_CPOW_RIGHT ← prove
   r"!w f s. f continuous_on s
           ==> (\z. w cpow (f z)) continuous_on s"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC [] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM ETA_AX] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC [holomorphic_on, ← GSYM complex_differentiable] THEN
    ASM_SIMP_TAC [COMPLEX_DIFFERENTIABLE_CPOW_RIGHT,
                  COMPLEX_DIFFERENTIABLE_AT_WITHIN])

  let CLOG_MUL ← prove
   r"!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
           ==> clog(w * z) =
                if Im(clog w + clog z) <= --pi then
                  (clog(w) + clog(z)) + ii * Cx(&2 * pi)
                else if Im(clog w + clog z) > pi then
                  (clog(w) + clog(z)) - ii * Cx(&2 * pi)
                else clog(w) + clog(z)"
   (REPEAT STRIP_TAC THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    MATCH_MP_TAC CLOG_UNIQUE THEN
    ASM_SIMP_TAC [CEXP_ADD, CEXP_SUB, CEXP_EULER, CEXP_CLOG, CONJ_ASSOC,
                  ← GSYM CX_SIN, ← GSYM CX_COS, COS_NPI, SIN_NPI] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    TRY (CONJ_TAC THENL [ALL_TAC, CONV_TAC COMPLEX_FIELD]) THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP CLOG_WORKS)) THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    REWRITE_TAC [IM_ADD, IM_SUB, IM_MUL_II, RE_CX] THEN
    REAL_ARITH_TAC)

  let CLOG_MUL_SIMPLE ← prove
   r"!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0)) /\
         --pi < Im(clog(w)) + Im(clog(z)) /\
         Im(clog(w)) + Im(clog(z)) <= pi
         ==> clog(w * z) = clog(w) + clog(z)"
   (SIMP_TAC [CLOG_MUL, IM_ADD] THEN REAL_ARITH_TAC)

  let CLOG_MUL_CX ← prove
   r"(!x z. &0 < x /\ ~(z = Cx(&0)) ==> clog(Cx x * z) = Cx(log x) + clog z) /\
   (!x z. &0 < x /\ ~(z = Cx(&0)) ==> clog(z * Cx x) = clog z + Cx(log x))"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [CX_LOG] THEN
    MATCH_MP_TAC CLOG_MUL_SIMPLE THEN
    ASM_SIMP_TAC [CX_INJ, REAL_LT_IMP_NZ, ← GSYM CX_LOG] THEN
    ASM_SIMP_TAC [IM_CX, REAL_ADD_LID, REAL_ADD_RID, CLOG_WORKS])

  let CLOG_MUL_POS ← prove
   r"!w z. &0 < Re w /\ &0 < Re z ==> clog(w * z) = clog w + clog z"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOG_MUL_SIMPLE THEN
    MATCH_MP_TAC (← TAUT (← q r"(p /\ q) /\ (p /\ q ==> r) ==> p /\ q /\ r")) THEN
    CONJ_TAC THENL [ASM_MESON_TAC [RE_CX, REAL_LT_REFL], STRIP_TAC] THEN
    MATCH_MP_TAC (← REAL_ARITH
      (← q r"abs(x) < pi / &2 /\ abs(y) < pi / &2
       ==> --pi < x + y /\ x + y <= pi")) THEN
    ASM_SIMP_TAC [RE_CLOG_POS_LT])

  let CLOG_DIV_POS ← prove
   r"!w z. &0 < Re w /\ &0 < Re z ==> clog(w / z) = clog w - clog z"
   (ASM_SIMP_TAC [complex_div, CLOG_MUL_POS, CLOG_INV, RE_COMPLEX_INV_GT_0] THEN
    REWRITE_TAC [complex_sub])

  let CLOG_NEG ← prove
   r"!z. ~(z = Cx(&0))
       ==> clog(--z) = if Im(z) <= &0 /\ ~(Re(z) < &0 /\ Im(z) = &0)
                       then clog(z) + ii * Cx(pi)
                       else clog(z) - ii * Cx(pi)"
   (REPEAT STRIP_TAC THEN
    SUBST1_TAC (← SIMPLE_COMPLEX_ARITH (← q r"--z = --Cx(&1) * z")) THEN
    ASM_SIMP_TAC [CLOG_MUL, ← ExceptT.mk (COMPLEX_RING (← q r"~(--Cx(&1) = Cx(&0))"))] THEN
    REWRITE_TAC [CLOG_NEG_1, IM_ADD, IM_MUL_II, RE_CX] THEN
    ASM_SIMP_TAC [CLOG_WORKS, ← REAL_ARITH
     (← q r"--p < x /\ x <= p ==> ~(p + x <= --p)")] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"p + x > p <=> &0 < x")] THEN
    ASM_SIMP_TAC [← GSYM IM_CLOG_EQ_PI] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"Im z <= &0 <=> ~(&0 < Im z)")] THEN
    ASM_SIMP_TAC [← GSYM IM_CLOG_POS_LT] THEN
    ASM_SIMP_TAC [CLOG_WORKS, ← REAL_ARITH (← q r"x <= p ==> (x < p <=> ~(x = p))")] THEN
    REWRITE_TAC [← TAUT (← q r"~(a /\ ~b) /\ ~b <=> ~a /\ ~b")] THEN
    ASM_CASES_TAC (← q r"Im(clog z) = pi") THEN ASM_REWRITE_TAC [PI_POS] THEN
    ASM_CASES_TAC (← q r"&0 < Im(clog z)") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [CX_MUL] THEN CONV_TAC COMPLEX_RING)

  let CLOG_MUL_II ← prove
   r"!z. ~(z = Cx(&0))
       ==> clog(ii * z) = if &0 <= Re(z) \/ Im(z) < &0
                          then clog(z) + ii * Cx(pi / &2)
                          else clog(z) - ii * Cx(&3 * pi / &2)"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [CLOG_MUL, II_NZ, CLOG_II] THEN
    REWRITE_TAC [IM_ADD, IM_MUL_II, RE_CX] THEN
    ASM_SIMP_TAC [CLOG_WORKS, ← REAL_ARITH
     (← q r"--p < x /\ x <= p ==> ~(p / &2 + x <= --p)")] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"p / &2 + x > p <=> p / &2 < x")] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"Im z < &0 <=> ~(&0 <= Im z)")] THEN
    ASM_SIMP_TAC [← GSYM RE_CLOG_POS_LE, ← GSYM IM_CLOG_POS_LE] THEN
    MATCH_MP_TAC (← MESON []
     (← q r"(p <=> ~q) /\ x = a /\ y = b
      ==> ((if p then x else y) = (if q then b else a))")) THEN
    CONJ_TAC THENL
     [MP_TAC PI_POS THEN REAL_ARITH_TAC,
      REWRITE_TAC [CX_MUL, CX_DIV] THEN CONV_TAC COMPLEX_RING])

  pure { cpow, CPOW_0, CPOW_N, CPOW_1, CPOW_ADD, CPOW_SUC, CPOW_NEG, CPOW_SUB,
         CEXP_MUL_CPOW, CPOW_EQ_0, NORM_CPOW_REAL, CPOW_REAL_REAL, NORM_CPOW_REAL_MONO,
         CPOW_MUL_REAL, HAS_COMPLEX_DERIVATIVE_CPOW, HAS_COMPLEX_DERIVATIVE_CPOW_RIGHT,
         COMPLEX_DIFFERENTIABLE_CPOW_RIGHT, HOLOMORPHIC_ON_CPOW_RIGHT,
         CONTINUOUS_ON_CPOW_RIGHT, CLOG_MUL, CLOG_MUL_SIMPLE, CLOG_MUL_CX, CLOG_MUL_POS,
         CLOG_DIV_POS, CLOG_NEG, CLOG_MUL_II }
/- ------------------------------------------------------------------------- -/
/- Unwinding number; complex arctangent.                                     -/
/- (transcendentals.ml 4198-4410)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSP where
  unwinding : thm
  UNWINDING_2PI : thm
  CLOG_MUL_UNWINDING : thm
  catn : thm
  CATN_0 : thm
  IM_COMPLEX_DIV_LEMMA : thm
  RE_COMPLEX_DIV_LEMMA : thm
  CTAN_CATN : thm
  CATN_CTAN : thm
  RE_CATN_BOUNDS : thm
  HAS_COMPLEX_DERIVATIVE_CATN : thm
  COMPLEX_DIFFERENTIABLE_AT_CATN : thm
  COMPLEX_DIFFERENTIABLE_WITHIN_CATN : thm
  CONTINUOUS_AT_CATN : thm
  CONTINUOUS_WITHIN_CATN : thm
  CONTINUOUS_ON_CATN : thm
  HOLOMORPHIC_ON_CATN : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSP [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) (BTSB : TSB) (BTSC : TSC) (BTSE : TSE) (BTSF : TSF) (BTSK : TSK) (BTSM : TSM) (BTSN : TSN) : ExceptT String IO TSP := do
  -- @@SCOPE BEGIN
  let { CEXP_ADD, CEXP_N, CEXP_NEG, CEXP_NZ, CEXP_SUB, .. } := BTSA
  let { ccos, CEXP_EULER, csin, CX_EXP, .. } := BTSB
  let { CX_COS, CX_SIN, EULER, .. } := BTSC
  let { COS_PI, PI_NZ, PI_POS, REAL_ABS_PI, SIN_PI, .. } := BTSE
  let { CEXP_EQ, .. } := BTSF
  let { ctan, .. } := BTSK
  let { CEXP_CLOG, CLOG_CEXP, CLOG_WORKS, CX_LOG, .. } := BTSM
  let { CLOG_1, .. } := BTSN
  let { complex_differentiable, COMPLEX_DIFFERENTIABLE_AT_WITHIN,
        HAS_COMPLEX_DERIVATIVE_AT_WITHIN, HAS_COMPLEX_DERIVATIVE_CHAIN,
        HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT, holomorphic_on, .. } := D.kne
  let { add_complex_differentiation_theorems, COMPLEX_DIFF_TAC, .. } := D.knk
  let { complex_div, COMPLEX_EQ, complex_mul, complex_norm, COMPLEX_SQNORM, complex_sub,
        IM, RE, .. } := D.cn.cxa
  let { COMPLEX_ADD_RID, COMPLEX_MUL_ASSOC, COMPLEX_MUL_LNEG, COMPLEX_MUL_RZERO,
        COMPLEX_SUB_RNEG, COMPLEX_SUB_RZERO, .. } := D.cn.cxb
  let { COMPLEX_ENTIRE, COMPLEX_POW_2, COMPLEX_POW_II_2, CX_ADD, CX_DIV, CX_INJ, CX_INV,
        CX_NEG, CX_SUB, II_NZ, IM_ADD, IM_CX, IM_II, IM_MUL_CX, IM_MUL_II, IM_NEG, IM_SUB,
        RE_ADD, RE_CX, RE_II, RE_MUL_II, RE_NEG, RE_SUB, .. } := D.cn.cxc
  let { COMPLEX_RING, .. } := D.cn.cxd
  let { COMPLEX_FIELD, .. } := D.cn.cxe
  let { COMPLEX_DIV_1, COMPLEX_DIV_LMUL, .. } := D.cn.cxf
  let { IM_CNJ, IM_COMPLEX_DIV_EQ_0, RE_CNJ, RE_COMPLEX_DIV_GT_0, .. } := D.cn.cxg
  let { REAL_ABS_INTEGER_LEMMA, .. } := D.cn.ms.qfloor
  let { ASM_REAL_ARITH_TAC, MESON_TAC, new_definition, REAL_ARITH, REAL_ARITH_TAC,
        REAL_RAT_REDUCE_CONV, .. } := D.cn.cx.cvx
  let { POW_2_SQRT_ABS, .. } := D.cn.cx.cpx
  let { CONJ_ASSOC, ETA_AX, FORALL_AND_THM, .. } := D.cn.cx.cvx.core1
  let { REAL_ABS_MUL, REAL_ABS_NUM, REAL_ADD_LID, REAL_ADD_RID, .. } := D.cn.cx.cvx.core3
  let { REAL_ENTIRE, REAL_LE_RMUL_EQ, REAL_LT_01, REAL_LT_DIV, .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_RID, REAL_NEG_0, .. } := D.cn.cx.cvx.core5
  let { real_ge, .. } := D.cn.cx.cvx.core6
  let { NORM_POW_2, .. } := D.cn.cx.cvx.vec3
  let { CONTINUOUS_AT_IMP_CONTINUOUS_ON, .. } := D.cn.cx.cvx.top2
  let { CONTINUOUS_AT_WITHIN, .. } := D.cn.ms.ig.dv.qtopology1
  let { NORM_LT_SQUARE, .. } := D.cn.ms.ig.dv.qvec
  -- @@SCOPE END

  let unwinding ← new_definition
   r"unwinding(z) = (z - clog(cexp z)) / (Cx(&2 * pi) * ii)"

  let UNWINDING_2PI ← prove
   r"Cx(&2 * pi) * ii * unwinding(z) = z - clog(cexp z)"
   (REWRITE_TAC [unwinding, COMPLEX_MUL_ASSOC] THEN
    MATCH_MP_TAC COMPLEX_DIV_LMUL THEN
    REWRITE_TAC [COMPLEX_ENTIRE, CX_INJ, II_NZ] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC)

  let CLOG_MUL_UNWINDING ← prove
   r"!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
           ==> clog(w * z) =
               clog(w) + clog(z) -
               Cx(&2 * pi) * ii * unwinding(clog w + clog z)"
   (REWRITE_TAC [UNWINDING_2PI,
      ← ExceptT.mk (COMPLEX_RING (← q r"w + z - ((w + z) - c) = c:complex"))] THEN
    ASM_SIMP_TAC [CEXP_ADD, CEXP_CLOG])

  let catn ← new_definition
   r"catn z = (ii / Cx(&2)) * clog((Cx(&1) - ii * z) / (Cx(&1) + ii * z))"

  let CATN_0 ← prove
   r"catn(Cx(&0)) = Cx(&0)"
   (REWRITE_TAC [catn, COMPLEX_MUL_RZERO, COMPLEX_SUB_RZERO, COMPLEX_ADD_RID] THEN
    REWRITE_TAC [COMPLEX_DIV_1, CLOG_1, COMPLEX_MUL_RZERO])

  let IM_COMPLEX_DIV_LEMMA ← prove
   r"!z. Im((Cx(&1) - ii * z) / (Cx(&1) + ii * z)) = &0 <=> Re z = &0"
   (REWRITE_TAC [IM_COMPLEX_DIV_EQ_0] THEN
    REWRITE_TAC [complex_mul, IM, RE, IM_CNJ, RE_CNJ, RE_CX, IM_CX, RE_II, IM_II,
                 RE_SUB, RE_ADD, IM_SUB, IM_ADD] THEN
    REAL_ARITH_TAC)

  let RE_COMPLEX_DIV_LEMMA ← prove
   r"!z. &0 < Re((Cx(&1) - ii * z) / (Cx(&1) + ii * z)) <=> norm(z) < &1"
   (REWRITE_TAC [RE_COMPLEX_DIV_GT_0, NORM_LT_SQUARE, REAL_LT_01] THEN
    REWRITE_TAC [← GSYM NORM_POW_2, COMPLEX_SQNORM] THEN
    REWRITE_TAC [complex_mul, IM, RE, IM_CNJ, RE_CNJ, RE_CX, IM_CX, RE_II, IM_II,
                 RE_SUB, RE_ADD, IM_SUB, IM_ADD] THEN
    REAL_ARITH_TAC)

  let CTAN_CATN ← prove
   r"!z. ~(z pow 2 = --Cx(&1)) ==> ctan(catn z) = z"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [catn, ctan, csin, ccos,
                 ← ExceptT.mk (COMPLEX_RING (← q r"--i * i / Cx(&2) * z = --(i * i) / Cx(&2) * z")),
                 ← ExceptT.mk (COMPLEX_RING (← q r"i * i / Cx(&2) * z =  (i * i) / Cx(&2) * z"))] THEN
    REWRITE_TAC [COMPLEX_POW_II_2, ← GSYM COMPLEX_POW_2] THEN
    REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"--Cx(&1) / Cx(&2) * x = --(Cx(&1) / Cx(&2) * x)")),
                 CEXP_NEG] THEN
    SUBGOAL_THEN
    (← q r"~(cexp(Cx(&1) / Cx(&2) *
            (clog((Cx(&1) - ii * z) / (Cx(&1) + ii * z)))) pow 2 = --Cx(&1))")
    ASSUME_TAC THENL
     [REWRITE_TAC [← GSYM CEXP_N, CEXP_SUB, ← ExceptT.mk (COMPLEX_RING
       (← q r"Cx(&2) * Cx(&1) / Cx(&2) * z = z"))] THEN
      ASM_SIMP_TAC [CEXP_CLOG, COMPLEX_POW_II_2,
        ← ExceptT.mk (COMPLEX_FIELD (← q r"~(w = Cx(&0)) /\ ~(z = Cx(&0)) ==> ~(w / z = Cx(&0))")),
        ← ExceptT.mk (COMPLEX_FIELD (← q r"~(w = Cx(&0)) ==> (x / w = y <=> x = y * w)")),
        ← ExceptT.mk (COMPLEX_FIELD
       (← q r"ii pow 2 = --Cx(&1) /\ ~(z pow 2 = --Cx(&1))
        ==> ~(Cx(&1) - ii * z = Cx(&0)) /\ ~(Cx(&1) + ii * z = Cx(&0))"))] THEN
      POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD,
      ALL_TAC] THEN
    REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"-- --Cx (&1) / Cx (&2) = Cx(&1) / Cx(&2)"))] THEN
    ASM_SIMP_TAC [CEXP_NZ, ← ExceptT.mk (COMPLEX_FIELD
      (← q r"~(z = Cx(&0)) /\ ~(z pow 2 = --Cx(&1))
       ==> ((inv(z) - z) / (Cx(&2) * ii)) / ((inv(z) + z) / Cx(&2)) =
           inv ii * ((Cx(&1) - z pow 2) / (Cx(&1) + z pow 2))"))] THEN
    ASM_SIMP_TAC [← GSYM CEXP_N, CEXP_SUB,
                  ← ExceptT.mk (COMPLEX_RING (← q r"Cx(&2) * Cx(&1) / Cx(&2) * z = z"))] THEN
    ASM_SIMP_TAC [CEXP_CLOG, ← ExceptT.mk (COMPLEX_FIELD
       (← q r"~(z pow 2 = --Cx(&1))
        ==> ~((Cx(&1) - ii * z) / (Cx(&1) + ii * z) = Cx(&0))"))] THEN
    UNDISCH_TAC (← q r"~(z pow 2 = --Cx(&1))") THEN CONV_TAC COMPLEX_FIELD)

  let CATN_CTAN ← prove
   r"!z. abs(Re z) < pi / &2 ==> catn(ctan z) = z"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [catn, ctan, csin, ccos] THEN
    ASM_SIMP_TAC [← ExceptT.mk (COMPLEX_FIELD
     (← q r"ii * (a / (Cx(&2) * ii)) / (b / Cx(&2)) = a / b"))] THEN
    SIMP_TAC [← ExceptT.mk (COMPLEX_FIELD
     (← q r"ii / Cx(&2) * x = y <=> x = Cx(&2) * --(ii * y)"))] THEN
    SUBGOAL_THEN (← q r"~(cexp(ii * z) pow 2 = --Cx(&1))") ASSUME_TAC THENL
     [SUBGOAL_THEN (← q r"--Cx(&1) = cexp(ii * Cx pi)") SUBST1_TAC THENL
       [REWRITE_TAC [CEXP_EULER, ← GSYM CX_SIN, ← GSYM CX_COS, SIN_PI, COS_PI] THEN
        CONV_TAC COMPLEX_RING,
        ALL_TAC] THEN
      REWRITE_TAC [← GSYM CEXP_N, CEXP_EQ] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"n:real") STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o AP_TERM (← q r"Im")) THEN
      REWRITE_TAC [IM_MUL_CX, IM_MUL_II, IM_ADD, RE_CX, IM_II, REAL_MUL_RID] THEN
      MATCH_MP_TAC (← REAL_ARITH
       (← q r"abs(z) < p / &2 /\ (w = &0 \/ abs(w) >= &2 * p)
        ==> ~(&2 * z = p + w)")) THEN
      ASM_REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_PI, REAL_ABS_NUM] THEN
      SIMP_TAC [real_ge, REAL_MUL_ASSOC, REAL_LE_RMUL_EQ, PI_POS] THEN
      REWRITE_TAC [REAL_ENTIRE, PI_NZ] THEN
      MP_TAC (← SPEC (← q r"n:real") REAL_ABS_INTEGER_LEMMA) THEN
      ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC,
      ASM_SIMP_TAC [CEXP_NEG, CEXP_NZ, COMPLEX_MUL_LNEG, ← ExceptT.mk (COMPLEX_FIELD
       (← q r"~(w = Cx(&0)) /\ ~(w pow 2 = --Cx(&1))
        ==> (Cx(&1) - (w - inv w) / (w + inv w)) /
            (Cx(&1) + (w - inv w) / (w + inv w)) =
             inv(w) pow 2"))] THEN
      REWRITE_TAC [← GSYM CEXP_N, ← GSYM CEXP_NEG] THEN
      MATCH_MP_TAC CLOG_CEXP THEN REWRITE_TAC [IM_MUL_CX, IM_NEG, IM_MUL_II] THEN
      ASM_REAL_ARITH_TAC])

  let RE_CATN_BOUNDS ← prove
   r"!z. (Re z = &0 ==> abs(Im z) < &1) ==> abs(Re(catn z)) < pi / &2"
   (REWRITE_TAC [catn, complex_div, ← GSYM CX_INV, ← GSYM COMPLEX_MUL_ASSOC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [RE_MUL_II, IM_MUL_CX] THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"abs x < p ==> abs(--(inv(&2) * x)) < p / &2")) THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"(--p < x /\ x <= p) /\ ~(x = p) ==> abs x < p")) THEN
    SUBGOAL_THEN (← q r"~(z = ii) /\ ~(z = --ii)") STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      DISCH_THEN (fun th => POP_ASSUM MP_TAC THEN SUBST1_TAC th) THEN
      REWRITE_TAC [RE_II, IM_II, RE_NEG, IM_NEG] THEN REAL_ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [← GSYM complex_div] THEN CONJ_TAC THENL
     [SUBGOAL_THEN (← q r"~((Cx(&1) - ii * z) / (Cx(&1) + ii * z) = Cx(&0))")
       (fun th => MESON_TAC [th, CLOG_WORKS]) THEN
      REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD,
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC (← ISPEC (← q r"clog((Cx(&1) - ii * z) / (Cx(&1) + ii * z))") EULER) THEN
    ASM_REWRITE_TAC [SIN_PI, COS_PI, CX_NEG] THEN
    REWRITE_TAC [← ExceptT.mk (COMPLEX_RING
     (← q r"x = y * (--Cx(&1) + z * Cx(&0)) <=> x + y = Cx(&0)"))] THEN
    REWRITE_TAC [CX_EXP] THEN
    ASM_SIMP_TAC [CEXP_CLOG, ← ExceptT.mk (COMPLEX_FIELD
       (← q r"~(z = ii) /\ ~(z = --ii)
        ==> ~((Cx(&1) - ii * z) / (Cx(&1) + ii * z) = Cx(&0))"))] THEN
    REWRITE_TAC [← GSYM CX_EXP] THEN DISCH_THEN (MP_TAC o AP_TERM (← q r"Im")) THEN
    REWRITE_TAC [IM_ADD, IM_CX, REAL_ADD_RID, IM_COMPLEX_DIV_LEMMA] THEN
    DISCH_TAC THEN UNDISCH_TAC (← q r"Re z = &0 ==> abs (Im z) < &1") THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"ii * z = --Cx(Im z)") SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC [COMPLEX_EQ, RE_NEG, IM_NEG, RE_MUL_II, IM_MUL_II,
                       RE_CX, IM_CX, REAL_NEG_0],
      ALL_TAC] THEN
    UNDISCH_TAC
     (← q r"Im(clog((Cx(&1) - --Cx(Im z)) / (Cx(&1) + --Cx(Im z)))) = pi") THEN
    REWRITE_TAC [COMPLEX_SUB_RNEG, ← GSYM complex_sub] THEN
    REWRITE_TAC [← GSYM CX_ADD, ← GSYM CX_SUB, ← GSYM CX_DIV] THEN
    SUBGOAL_THEN (← q r"&0 < (&1 + Im z) / (&1 - Im z)") ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC,
      ASM_SIMP_TAC [← GSYM CX_LOG, IM_CX, PI_NZ]])

  let HAS_COMPLEX_DERIVATIVE_CATN ← prove
   r"!z. (Re z = &0 ==> abs(Im z) < &1)
       ==> (catn has_complex_derivative inv(Cx(&1) + z pow 2)) (at z)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"~(z = ii) /\ ~(z = --ii)") STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      DISCH_THEN (fun th => POP_ASSUM MP_TAC THEN SUBST1_TAC th) THEN
      REWRITE_TAC [RE_II, IM_II, RE_NEG, IM_NEG] THEN REAL_ARITH_TAC,
      ALL_TAC] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [← GSYM ETA_AX] THEN
    REWRITE_TAC [catn] THEN COMPLEX_DIFF_TAC THEN
    REWRITE_TAC [RE_SUB, RE_ADD, IM_SUB, IM_ADD,
                 RE_CX, RE_MUL_II, IM_CX, IM_MUL_II] THEN
    REWRITE_TAC [← GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC [IM_COMPLEX_DIV_LEMMA, RE_COMPLEX_DIV_LEMMA] THEN
      SIMP_TAC [complex_norm] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REWRITE_TAC [REAL_ADD_LID, POW_2_SQRT_ABS],
      REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD])

  let COMPLEX_DIFFERENTIABLE_AT_CATN ← prove
   r"!z. (Re z = &0 ==> abs(Im z) < &1) ==> catn complex_differentiable at z"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_CATN])

  let COMPLEX_DIFFERENTIABLE_WITHIN_CATN ← prove
   r"!s z. (Re z = &0 ==> abs(Im z) < &1)
         ==> catn complex_differentiable (at z within s)"
   (MESON_TAC [COMPLEX_DIFFERENTIABLE_AT_WITHIN,
               COMPLEX_DIFFERENTIABLE_AT_CATN])

  add_complex_differentiation_theorems
   (CONJUNCTS (← REWRITE_RULE [FORALL_AND_THM]
     (← MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
               HAS_COMPLEX_DERIVATIVE_CATN)))

  let CONTINUOUS_AT_CATN ← prove
   r"!z. (Re z = &0 ==> abs(Im z) < &1) ==> catn continuous at z"
   (MESON_TAC [HAS_COMPLEX_DERIVATIVE_CATN,
               HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT])

  let CONTINUOUS_WITHIN_CATN ← prove
   r"!s z. (Re z = &0 ==> abs(Im z) < &1) ==> catn continuous (at z within s)"
   (MESON_TAC [CONTINUOUS_AT_WITHIN, CONTINUOUS_AT_CATN])

  let CONTINUOUS_ON_CATN ← prove
   r"!s. (!z. z IN s /\ Re z = &0 ==> abs(Im z) < &1) ==> catn continuous_on s"
   (MESON_TAC [CONTINUOUS_AT_IMP_CONTINUOUS_ON, CONTINUOUS_AT_CATN])

  let HOLOMORPHIC_ON_CATN ← prove
   r"!s. (!z. z IN s /\ Re z = &0 ==> abs(Im z) < &1) ==> catn holomorphic_on s"
   (REWRITE_TAC [holomorphic_on] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN, HAS_COMPLEX_DERIVATIVE_CATN])

  pure { unwinding, UNWINDING_2PI, CLOG_MUL_UNWINDING, catn, CATN_0,
         IM_COMPLEX_DIV_LEMMA, RE_COMPLEX_DIV_LEMMA, CTAN_CATN, CATN_CTAN,
         RE_CATN_BOUNDS, HAS_COMPLEX_DERIVATIVE_CATN, COMPLEX_DIFFERENTIABLE_AT_CATN,
         COMPLEX_DIFFERENTIABLE_WITHIN_CATN, CONTINUOUS_AT_CATN, CONTINUOUS_WITHIN_CATN,
         CONTINUOUS_ON_CATN, HOLOMORPHIC_ON_CATN }
/- ------------------------------------------------------------------------- -/
/- Real arctangent.                                                          -/
/- (transcendentals.ml 4411-4603)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSQ where
  atn : thm
  CX_ATN : thm
  ATN_TAN : thm
  ATN_BOUND : thm
  ATN_BOUNDS : thm
  TAN_ATN : thm
  ATN_0 : thm
  ATN_1 : thm
  ATN_NEG : thm
  ATN_MONO_LT : thm
  ATN_MONO_LT_EQ : thm
  ATN_MONO_LE_EQ : thm
  ATN_INJ : thm
  ATN_POS_LT : thm
  ATN_POS_LE : thm
  ATN_LT_PI4_POS : thm
  ATN_LT_PI4_NEG : thm
  ATN_LT_PI4 : thm
  ATN_LE_PI4 : thm
  COS_ATN_NZ : thm
  TAN_SEC : thm
  COS_ATN : thm
  SIN_ATN : thm
  ATN_ABS : thm
  ATN_ADD : thm
  ATN_INV : thm
  ATN_ADD_SMALL : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSQ [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) (BTSC : TSC) (BTSE : TSE) (BTSF : TSF) (BTSK : TSK) (BTSL : TSL) (BTSM : TSM) (BTSP : TSP) : ExceptT String IO TSQ := do
  -- @@SCOPE BEGIN
  let { CEXP_SUB, .. } := BTSA
  let { SIN_CIRCLE, .. } := BTSC
  let { COS_POS_PI, PI_POS, .. } := BTSE
  let { NORM_CEXP_IMAGINARY, .. } := BTSF
  let { COS_TAN, CX_TAN, SIN_TAN, tan, TAN_0, TAN_ADD, tan_def, TAN_NEG, TAN_PI4,
        .. } := BTSK
  let { TAN_COT, TAN_MONO_LE, .. } := BTSL
  let { CEXP_CLOG, .. } := BTSM
  let { catn, CATN_CTAN, CTAN_CATN, RE_CATN_BOUNDS, .. } := BTSP
  let { complex_div, .. } := D.cn.cxa
  let { COMPLEX_MUL_ASSOC, .. } := D.cn.cxb
  let { CX_INV, IM_CX, IM_II, IM_MUL_II, IM_NEG, RE_ADD, RE_CX, RE_MUL_CX, RE_MUL_II,
        RE_SUB, .. } := D.cn.cxc
  let { COMPLEX_RING, .. } := D.cn.cxd
  let { COMPLEX_FIELD, .. } := D.cn.cxe
  let { COMPLEX_NORM_DIV, COMPLEX_NORM_ZERO, .. } := D.cn.cxf
  let { CNJ_CX, CNJ_II, CNJ_MUL, CNJ_SUB, COMPLEX_NORM_CNJ, .. } := D.cn.cxg
  let { REAL, real, .. } := D.cn.cxi
  let { ASM_REAL_ARITH_TAC, MESON, MESON_TAC, new_definition, REAL_ARITH, REAL_ARITH_TAC,
        REAL_FIELD, REAL_RAT_REDUCE_CONV, .. } := D.cn.cx.cvx
  let { CONTRAPOS_THM, EQ_TRANS, .. } := D.cn.cx.cvx.core1
  let { MONO_FORALL, REAL_ABS_DIV, REAL_ABS_NEG, REAL_ABS_NUM, REAL_ADD_LID, REAL_ADD_RID,
        REAL_DIV_1, .. } := D.cn.cx.cvx.core3
  let { REAL_LE_ANTISYM, REAL_LE_LT, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_RDIV_EQ,
        .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_NOT_LE, REAL_NOT_LT, REAL_SUB_RZERO,
        .. } := D.cn.cx.cvx.core5
  let { real_abs, .. } := D.cn.cx.cvx.core6
  -- @@SCOPE END

  let atn ← new_definition
   r"atn(x) = Re(catn(Cx x))"

  let CX_ATN ← prove
   r"!x. Cx(atn x) = catn(Cx x)"
   (GEN_TAC THEN REWRITE_TAC [atn, catn, ← GSYM REAL, real] THEN
    REWRITE_TAC [complex_div, IM_MUL_II, ← GSYM CX_INV, ← GSYM COMPLEX_MUL_ASSOC] THEN
    REWRITE_TAC [RE_MUL_CX, ← REAL_ARITH (← q r"inv(&2) * x = &0 <=> x = &0")] THEN
    MATCH_MP_TAC NORM_CEXP_IMAGINARY THEN
    SUBGOAL_THEN (← q r"~(Cx(&1) - ii * Cx(x) = Cx(&0)) /\
                  ~(Cx(&1) + ii * Cx(x) = Cx(&0))")
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_THEN (MP_TAC o AP_TERM (← q r"Re")) THEN
      REWRITE_TAC [RE_ADD, RE_SUB, RE_MUL_II, IM_CX, RE_CX] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV,
      ALL_TAC] THEN
    ASM_SIMP_TAC [CEXP_SUB, CEXP_CLOG, ← ExceptT.mk (COMPLEX_FIELD
     (← q r"~(a = Cx(&0)) /\ ~(b = Cx(&0)) ==> ~(a * inv b = Cx(&0))"))] THEN
    REWRITE_TAC [← GSYM complex_div, COMPLEX_NORM_DIV] THEN
    MATCH_MP_TAC (← REAL_FIELD (← q r"~(b = &0) /\ a = b ==> a / b = &1")) THEN
    ASM_REWRITE_TAC [COMPLEX_NORM_ZERO] THEN
    MATCH_MP_TAC (← MESON [COMPLEX_NORM_CNJ] (← q r"cnj a = b ==> norm a = norm b")) THEN
    REWRITE_TAC [CNJ_SUB, CNJ_MUL, CNJ_MUL, CNJ_II, CNJ_CX] THEN
    CONV_TAC COMPLEX_RING)

  let ATN_TAN ← prove
   r"!y. tan(atn y) = y"
   (GEN_TAC THEN REWRITE_TAC [tan_def, atn] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"Re(ctan(catn(Cx y)))") THEN
    CONJ_TAC THENL [REWRITE_TAC [← GSYM CX_ATN, RE_CX], ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM RE_CX] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CTAN_CATN THEN MATCH_MP_TAC (← ExceptT.mk (COMPLEX_RING
     (← q r"~(z = ii) /\ ~(z = --ii) ==> ~(z pow 2 = --Cx(&1))"))) THEN
    CONJ_TAC THEN DISCH_THEN (MP_TAC o AP_TERM (← q r"Im")) THEN
    REWRITE_TAC [IM_II, IM_CX, IM_NEG] THEN REAL_ARITH_TAC)

  let ATN_BOUND ← prove
   r"!y. abs(atn y) < pi / &2"
   (GEN_TAC THEN REWRITE_TAC [atn] THEN MATCH_MP_TAC RE_CATN_BOUNDS THEN
    REWRITE_TAC [IM_CX] THEN CONV_TAC REAL_RAT_REDUCE_CONV)

  let ATN_BOUNDS ← prove
   r"!y. --(pi / &2) < atn(y) /\ atn(y) < (pi / &2)"
   (MP_TAC ATN_BOUND THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC)

  let TAN_ATN ← prove
   r"!x. --(pi / &2) < x /\ x < pi / &2 ==> atn(tan(x)) = x"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [tan_def, atn] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"Re(catn(ctan(Cx x)))") THEN
    CONJ_TAC THENL [REWRITE_TAC [← GSYM CX_TAN, RE_CX], ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM RE_CX] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CATN_CTAN THEN REWRITE_TAC [RE_CX] THEN
    ASM_REAL_ARITH_TAC)

  let ATN_0 ← prove
   r"atn(&0) = &0"
   (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← SYM TAN_0] THEN
    MATCH_MP_TAC TAN_ATN THEN MP_TAC PI_POS THEN REAL_ARITH_TAC)

  let ATN_1 ← prove
   r"atn(&1) = pi / &4"
   (MP_TAC (← AP_TERM (← q r"atn") TAN_PI4) THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC TAN_ATN THEN MP_TAC PI_POS THEN REAL_ARITH_TAC)

  let ATN_NEG ← prove
   r"!x. atn(--x) = --(atn x)"
   (GEN_TAC THEN MP_TAC (← SPEC (← q r"atn(x)") TAN_NEG) THEN REWRITE_TAC [ATN_TAN] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC TAN_ATN THEN
    MP_TAC (← SPEC (← q r"x:real") ATN_BOUNDS) THEN REAL_ARITH_TAC)

  let ATN_MONO_LT ← prove
   r"!x y. x < y ==> atn(x) < atn(y)"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [← GSYM ATN_TAN] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN REWRITE_TAC [REAL_NOT_LT] THEN
    SIMP_TAC [TAN_MONO_LE, ATN_BOUNDS])

  let ATN_MONO_LT_EQ ← prove
   r"!x y. atn(x) < atn(y) <=> x < y"
   (MESON_TAC [REAL_NOT_LE, REAL_LE_LT, ATN_MONO_LT])

  let ATN_MONO_LE_EQ ← prove
   r"!x y. atn(x) <= atn(y) <=> x <= y"
   (REWRITE_TAC [← GSYM REAL_NOT_LT, ATN_MONO_LT_EQ])

  let ATN_INJ ← prove
   r"!x y. (atn x = atn y) <=> (x = y)"
   (REWRITE_TAC [← GSYM REAL_LE_ANTISYM, ATN_MONO_LE_EQ])

  let ATN_POS_LT ← prove
   r"&0 < atn(x) <=> &0 < x"
   (MESON_TAC [ATN_0, ATN_MONO_LT_EQ])

  let ATN_POS_LE ← prove
   r"&0 <= atn(x) <=> &0 <= x"
   (MESON_TAC [ATN_0, ATN_MONO_LE_EQ])

  let ATN_LT_PI4_POS ← prove
   r"!x. x < &1 ==> atn(x) < pi / &4"
   (SIMP_TAC [← GSYM ATN_1, ATN_MONO_LT])

  let ATN_LT_PI4_NEG ← prove
   r"!x. --(&1) < x ==> --(pi / &4) < atn(x)"
   (SIMP_TAC [← GSYM ATN_1, ← GSYM ATN_NEG, ATN_MONO_LT])

  let ATN_LT_PI4 ← prove
   r"!x. abs(x) < &1 ==> abs(atn x) < pi / &4"
   (GEN_TAC THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"(&0 < x ==> &0 < y) /\
      (x < &0 ==> y < &0) /\
      ((x = &0) ==> (y = &0)) /\
      (x < a ==> y < b) /\
      (--a < x ==> --b < y)
      ==> abs(x) < a ==> abs(y) < b")) THEN
    SIMP_TAC [ATN_LT_PI4_POS, ATN_LT_PI4_NEG, ATN_0] THEN CONJ_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [← GSYM ATN_0] THEN
    SIMP_TAC [ATN_MONO_LT])

  let ATN_LE_PI4 ← prove
   r"!x. abs(x) <= &1 ==> abs(atn x) <= pi / &4"
   (REWRITE_TAC [REAL_LE_LT] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [ATN_LT_PI4] THEN DISJ2_TAC THEN
    FIRST_ASSUM (DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
      (← REAL_ARITH (← q r"(abs(x) = a) ==> (x = a) \/ (x = --a)"))) THEN
    ASM_REWRITE_TAC [ATN_1, ATN_NEG] THEN
    REWRITE_TAC [REAL_ABS_DIV, REAL_ABS_NUM, REAL_ABS_NEG] THEN
    SIMP_TAC [real_abs, REAL_LT_IMP_LE, PI_POS])

  let COS_ATN_NZ ← prove
   r"!x. ~(cos(atn(x)) = &0)"
   (GEN_TAC THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    MATCH_MP_TAC COS_POS_PI THEN REWRITE_TAC [ATN_BOUNDS])

  let TAN_SEC ← prove
   r"!x. ~(cos(x) = &0) ==> (&1 + (tan(x) pow 2) = inv(cos x) pow 2)"
   (MP_TAC SIN_CIRCLE THEN MATCH_MP_TAC MONO_FORALL THEN REWRITE_TAC [tan] THEN
    CONV_TAC REAL_FIELD)

  let COS_ATN ← prove
   r"!x. cos(atn x) = &1 / sqrt(&1 + x pow 2)"
   (SIMP_TAC [COS_TAN, ATN_BOUND, ATN_TAN])

  let SIN_ATN ← prove
   r"!x. sin(atn x) = x / sqrt(&1 + x pow 2)"
   (SIMP_TAC [SIN_TAN, ATN_BOUND, ATN_TAN])

  let ATN_ABS ← prove
   r"!x. atn(abs x) = abs(atn x)"
   (GEN_TAC THEN REWRITE_TAC [real_abs, ATN_POS_LE] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [ATN_NEG])

  let ATN_ADD ← prove
   r"!x y. abs(atn x + atn y) < pi / &2
         ==> atn(x) + atn(y) = atn((x + y) / (&1 - x * y))"
   (REPEAT STRIP_TAC THEN
    TRANS_TAC EQ_TRANS (← q r"atn((tan(atn x) + tan(atn y)) /
                            (&1 - tan(atn x) * tan(atn y)))") THEN
    CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [ATN_TAN]] THEN
    W (MP_TAC o PART_MATCH (rand o rand) TAN_ADD o rand o rand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [COS_ATN_NZ] THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
      MATCH_MP_TAC COS_POS_PI THEN ASM_REAL_ARITH_TAC,
      DISCH_THEN (SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC TAN_ATN THEN ASM_REAL_ARITH_TAC])

  let ATN_INV ← prove
   r"!x. &0 < x ==> atn(inv x) = pi / &2 - atn x"
   (REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS (← q r"atn(inv(tan(atn x)))") THEN
    CONJ_TAC THENL [REWRITE_TAC [ATN_TAN], REWRITE_TAC [← GSYM TAN_COT]] THEN
    MATCH_MP_TAC TAN_ATN THEN REWRITE_TAC [ATN_BOUNDS, ← REAL_ARITH
     (← q r"--(p / &2) < p / &2 - x /\ p / &2 - x < p / &2 <=> &0 < x /\ x < p")] THEN
    ASM_REWRITE_TAC [ATN_POS_LT] THEN MP_TAC (← SPEC (← q r"x:real") ATN_BOUNDS) THEN
    ASM_REAL_ARITH_TAC)

  let ATN_ADD_SMALL ← prove
   r"!x y. abs(x * y) < &1
         ==> (atn(x) + atn(y) = atn((x + y) / (&1 - x * y)))"
   (REPEAT STRIP_TAC THEN
    MAP_EVERY ASM_CASES_TAC [← q r"x = &0", ← q r"y = &0"] THEN
    ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_SUB_RZERO,
                     REAL_DIV_1, REAL_ADD_LID, REAL_ADD_RID, ATN_0] THEN
    MATCH_MP_TAC ATN_ADD THEN MATCH_MP_TAC (← REAL_ARITH
     (← q r"abs(x) < p - abs(y) \/ abs(y) < p - abs(x) ==> abs(x + y) < p")) THEN
    REWRITE_TAC [← GSYM ATN_ABS] THEN
    ASM_SIMP_TAC [← GSYM ATN_INV, ← REAL_ARITH (← q r"~(x = &0) ==> &0 < abs x"),
          ATN_MONO_LT_EQ, ← REAL_ARITH (← q r"inv x = &1 / x"), REAL_LT_RDIV_EQ] THEN
    ASM_REAL_ARITH_TAC)

  pure { atn, CX_ATN, ATN_TAN, ATN_BOUND, ATN_BOUNDS, TAN_ATN, ATN_0, ATN_1, ATN_NEG,
         ATN_MONO_LT, ATN_MONO_LT_EQ, ATN_MONO_LE_EQ, ATN_INJ, ATN_POS_LT, ATN_POS_LE,
         ATN_LT_PI4_POS, ATN_LT_PI4_NEG, ATN_LT_PI4, ATN_LE_PI4, COS_ATN_NZ, TAN_SEC,
         COS_ATN, SIN_ATN, ATN_ABS, ATN_ADD, ATN_INV, ATN_ADD_SMALL }
/- ------------------------------------------------------------------------- -/
/- Machin-like formulas for pi; some bound theorems where a bit of simple   -/
/- calculus is handy; compatibility with old analysis theory; some slightly -/
/- ad hoc lemmas.                                                            -/
/- (transcendentals.ml 4604-4690)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSR where
  MACHIN : thm
  MACHIN_EULER : thm
  MACHIN_GAUSS : thm
  ATN_ABS_LE_X : thm
  ATN_LE_X : thm
  TAN_ABS_GE_X : thm
  TAN_TOTAL : thm
  TAN_TOTAL_POS : thm
  TAN_TOTAL_LEMMA : thm
  RE_POW_2 : thm
  IM_POW_2 : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSR [HolBase] (D : TranscendentalsDeps) (BTSP : TSP) (BTSQ : TSQ) : ExceptT String IO TSR := do
  -- @@SCOPE BEGIN
  let { HAS_COMPLEX_DERIVATIVE_CATN, .. } := BTSP
  let { ATN_0, ATN_1, ATN_ADD_SMALL, ATN_BOUNDS, ATN_NEG, ATN_POS_LE, ATN_POS_LT, ATN_TAN,
        CX_ATN, TAN_ATN, .. } := BTSQ
  let { HAS_COMPLEX_DERIVATIVE_AT_WITHIN, .. } := D.kne
  let { COMPLEX_MVT, .. } := D.knm
  let { complex_mul, IM, RE, .. } := D.cn.cxa
  let { COMPLEX_SUB_RZERO, .. } := D.cn.cxb
  let { COMPLEX_NORM_CX, COMPLEX_POW_2, CX_ADD, CX_INV, CX_POW, .. } := D.cn.cxc
  let { CONVEX_REAL, real, REAL, REAL_CX, .. } := D.cn.cxi
  let { MESON_TAC, num_CONV, REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV, .. } := D.cn.cx.cvx
  let { REAL_LE_SQUARE, real_sub, .. } := D.cn.cx.cpx
  let { IN, .. } := D.cn.cx.cvx.core2
  let { MONO_FORALL, REAL_ABS_INV, REAL_ADD_LID, REAL_ADD_RDISTRIB,
        .. } := D.cn.cx.cvx.core3
  let { REAL_EQ_IMP_LE, REAL_INV_LE_1, REAL_LE_TRANS, .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_LZERO, REAL_MUL_RNEG, REAL_OF_NUM_SUC,
        .. } := D.cn.cx.cvx.core5
  -- @@SCOPE END

  let [MACHIN, MACHIN_EULER, MACHIN_GAUSS] := CONJUNCTS (← prove
   r"(&4 * atn(&1 / &5) - atn(&1 / &239) = pi / &4) /\
   (&5 * atn(&1 / &7) + &2 * atn(&3 / &79) = pi / &4) /\
   (&12 * atn(&1 / &18) + &8 * atn(&1 / &57) - &5 * atn(&1 / &239) = pi / &4)"
   (REPEAT CONJ_TAC THEN CONV_TAC (← (do
      let mulop ← q r"( * ):real->real->real"
      pure (ONCE_DEPTH_CONV (fun tm =>
        if HolCore.Basics.is_binop mulop tm
        then LAND_CONV (RAND_CONV (TOP_DEPTH_CONV num_CONV)) tm
        else pure (.error ""))))) THEN
    REWRITE_TAC [real_sub, ← GSYM REAL_MUL_RNEG, ← GSYM ATN_NEG] THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_SUC, REAL_ADD_RDISTRIB] THEN
    REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_LID, REAL_ADD_LID] THEN
    CONV_TAC (DEPTH_CONV (fun tm => ExceptT.run do
      let th1 ← PART_MATCH (lhand o rand) ATN_ADD_SMALL tm
      let th2 ← MP th1 (← EQT_ELIM (← ExceptT.mk
        (REAL_RAT_REDUCE_CONV (← liftExcept (lhand (concl th1))))))
      CONV_RULE (RAND_CONV (RAND_CONV REAL_RAT_REDUCE_CONV)) th2)) THEN
    REWRITE_TAC [ATN_1]))
    | throw "MACHIN: CONJUNCTS match failure"

  let ATN_ABS_LE_X ← prove
   r"!x. abs(atn x) <= abs x"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"catn", ← q r"\z. inv(Cx(&1) + z pow 2)", ← q r"real", ← q r"&1"]
        COMPLEX_MVT) THEN
    REWRITE_TAC [CONVEX_REAL, IN] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC [real] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
        MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_CATN THEN
        ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC,
        GEN_TAC THEN REWRITE_TAC [REAL] THEN
        DISCH_THEN (SUBST1_TAC o SYM) THEN
        REWRITE_TAC [← GSYM CX_POW, ← GSYM CX_ADD, ← GSYM CX_INV, COMPLEX_NORM_CX] THEN
        REWRITE_TAC [REAL_ABS_INV] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
        MP_TAC (← SPEC (← q r"Re z") REAL_LE_SQUARE) THEN REAL_ARITH_TAC],
      DISCH_THEN (MP_TAC o SPECL [← q r"Cx(&0)", ← q r"Cx(x)"]) THEN
      REWRITE_TAC [← GSYM CX_ATN, COMPLEX_SUB_RZERO, REAL_CX, ATN_0] THEN
      REWRITE_TAC [COMPLEX_NORM_CX, REAL_MUL_LID]])

  let ATN_LE_X ← prove
   r"!x. &0 <= x ==> atn(x) <= x"
   (MP_TAC ATN_ABS_LE_X THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC)

  let TAN_ABS_GE_X ← prove
   r"!x. abs(x) < pi / &2 ==> abs(x) <= abs(tan x)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"abs(atn(tan x))") THEN REWRITE_TAC [ATN_ABS_LE_X] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC TAN_ATN THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC)

  let TAN_TOTAL ← prove
   r"!y. ?!x. --(pi / &2) < x /\ x < (pi / &2) /\ tan(x) = y"
   (MESON_TAC [TAN_ATN, ATN_TAN, ATN_BOUNDS])

  let TAN_TOTAL_POS ← prove
   r"!y. &0 <= y ==> ?x. &0 <= x /\ x < pi / &2 /\ tan(x) = y"
   (MESON_TAC [ATN_TAN, ATN_BOUNDS, ATN_POS_LE])

  let TAN_TOTAL_LEMMA ← prove
   r"!y. &0 < y ==> ?x. &0 < x /\ x < pi / &2 /\ y < tan(x)"
   (REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"atn(y + &1)") THEN
    REWRITE_TAC [ATN_TAN, ATN_BOUNDS, ATN_POS_LT] THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC)

  let RE_POW_2 ← prove
   r"Re(z pow 2) = Re(z) pow 2 - Im(z) pow 2"
   (REWRITE_TAC [COMPLEX_POW_2, complex_mul, RE] THEN REAL_ARITH_TAC)

  let IM_POW_2 ← prove
   r"Im(z pow 2) = &2 * Re(z) * Im(z)"
   (REWRITE_TAC [COMPLEX_POW_2, complex_mul, IM] THEN REAL_ARITH_TAC)

  pure { MACHIN, MACHIN_EULER, MACHIN_GAUSS, ATN_ABS_LE_X, ATN_LE_X, TAN_ABS_GE_X,
         TAN_TOTAL, TAN_TOTAL_POS, TAN_TOTAL_LEMMA, RE_POW_2, IM_POW_2 }
/- ------------------------------------------------------------------------- -/
/- Inverse sine.                                                             -/
/- (transcendentals.ml 4691-4888)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSS where
  casn : thm
  CASN_BODY_LEMMA : thm
  CSIN_CASN : thm
  CASN_CSIN : thm
  CASN_UNIQUE : thm
  CASN_0 : thm
  CASN_1 : thm
  CASN_NEG_1 : thm
  HAS_COMPLEX_DERIVATIVE_CASN : thm
  COMPLEX_DIFFERENTIABLE_AT_CASN : thm
  COMPLEX_DIFFERENTIABLE_WITHIN_CASN : thm
  CONTINUOUS_AT_CASN : thm
  CONTINUOUS_WITHIN_CASN : thm
  CONTINUOUS_ON_CASN : thm
  HOLOMORPHIC_ON_CASN : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSS [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) (BTSB : TSB) (BTSC : TSC) (BTSE : TSE) (BTSM : TSM) (BTSN : TSN) (BTSR : TSR) : ExceptT String IO TSS := do
  -- @@SCOPE BEGIN
  let { CEXP_NEG, CEXP_NZ, .. } := BTSA
  let { csin, CSIN_CIRCLE, REAL_EXP_0, REAL_EXP_NEG, REAL_EXP_POS_LT, .. } := BTSB
  let { CONTINUOUS_AT_CSIN, COS_NEG, HAS_COMPLEX_DERIVATIVE_CSIN, IM_CEXP, RE_CEXP,
        SIN_NEG, .. } := BTSC
  let { COS_PI2, COS_POS_PI, PI_POS, SIN_PI2, .. } := BTSE
  let { CEXP_CLOG, CLOG_CEXP, CONTINUOUS_AT_CLOG, .. } := BTSM
  let { CLOG_1, CLOG_II, CLOG_NEG_II, CONTINUOUS_AT_CSQRT, .. } := BTSN
  let { IM_POW_2, RE_POW_2, .. } := BTSR
  let { CONTINUOUS_COMPLEX_MUL, CONTINUOUS_COMPLEX_POW, .. } := D.knc
  let { complex_differentiable, COMPLEX_DIFFERENTIABLE_AT_WITHIN,
        HAS_COMPLEX_DERIVATIVE_AT_WITHIN, HAS_COMPLEX_DERIVATIVE_CHAIN,
        HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT, holomorphic_on, .. } := D.kne
  let { HAS_COMPLEX_DERIVATIVE_INVERSE_BASIC, .. } := D.knj
  let { add_complex_differentiation_theorems, .. } := D.knk
  let { CONTINUOUS_AT_COMPOSE, .. } := D.qtopology
  let { REAL_LT_RSQRT, REAL_LT_SQUARE, REAL_POW_LT2, .. } := D.qsession
  let { complex_div, complex_norm, IM, RE, .. } := D.cn.cxa
  let { COMPLEX_ADD_LID, COMPLEX_ADD_RID, COMPLEX_MUL_ASSOC, COMPLEX_MUL_LID,
        COMPLEX_MUL_LNEG, COMPLEX_MUL_RID, COMPLEX_MUL_RNEG, COMPLEX_MUL_RZERO,
        COMPLEX_NEG_NEG, COMPLEX_SUB_RZERO, .. } := D.cn.cxb
  let { COMPLEX_POW_2, COMPLEX_POW_II_2, CX_INV, CX_NEG, CX_POW, CX_SUB, IM_ADD, IM_CX,
        IM_MUL_CX, IM_MUL_II, IM_NEG, IM_SUB, RE_ADD, RE_CX, RE_MUL_CX, RE_MUL_II, RE_NEG,
        RE_SUB, .. } := D.cn.cxc
  let { COMPLEX_RING, .. } := D.cn.cxd
  let { COMPLEX_FIELD, .. } := D.cn.cxe
  let { CSQRT, csqrt, CSQRT_0, CSQRT_1, POW_2_CSQRT, .. } := D.cn.cxh
  let { ASM_REAL_ARITH_TAC, MESON_TAC, new_definition, REAL_ARITH, REAL_ARITH_TAC,
        REAL_RAT_REDUCE_CONV, REAL_RING, .. } := D.cn.cx.cvx
  let { REAL_LE_SQUARE, real_sub, SQRT_POS_LT, .. } := D.cn.cx.cpx
  let { ARITH, ETA_AX, FORALL_AND_THM, .. } := D.cn.cx.cvx.core1
  let { REAL_ABS_NUM, REAL_ABS_POS, REAL_ADD_LID, REAL_ADD_RDISTRIB,
        .. } := D.cn.cx.cvx.core3
  let { REAL_ENTIRE, REAL_INV_1, REAL_LE_ADD, REAL_LE_REFL, REAL_LE_SQUARE_ABS, REAL_LT_01,
        REAL_LT_ADD, REAL_LT_IMP_LE, REAL_LT_MUL, REAL_LT_SQUARE_ABS,
        .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_LZERO, REAL_MUL_RNEG, REAL_MUL_RZERO, REAL_NEG_NEG, REAL_POS,
        REAL_POW2_ABS, REAL_POW_2, REAL_SUB_RDISTRIB, REAL_SUB_REFL, REAL_SUB_RZERO,
        .. } := D.cn.cx.cvx.core5
  let { o_DEF, .. } := D.cn.cx.cvx.core6
  let { CENTRE_IN_BALL, .. } := D.cn.cx.cvx.top1
  let { CONTINUOUS_ADD, CONTINUOUS_AT_ID, CONTINUOUS_AT_IMP_CONTINUOUS_ON,
        .. } := D.cn.cx.cvx.top2
  let { CONTINUOUS_CONST, CONTINUOUS_SUB, .. } := D.cn.cx.cvx.top3
  let { OPEN_BALL, .. } := D.cn.cx.cvx.top4
  let { CONTINUOUS_AT_WITHIN, .. } := D.cn.ms.ig.dv.qtopology1
  -- @@SCOPE END

  let casn ← new_definition
   r"casn z = --ii * clog(ii * z + csqrt(Cx(&1) - z pow 2))"

  let CASN_BODY_LEMMA ← prove
   r"!z. ~(ii * z + csqrt(Cx(&1) - z pow 2) = Cx(&0))"
   (GEN_TAC THEN MP_TAC (← SPEC (← q r"Cx(&1) - z pow 2") CSQRT) THEN
    CONV_TAC COMPLEX_FIELD)

  let CSIN_CASN ← prove
   r"!z. csin(casn z) = z"
   (GEN_TAC THEN REWRITE_TAC [csin, casn, COMPLEX_MUL_LNEG, COMPLEX_MUL_RNEG] THEN
    REWRITE_TAC [COMPLEX_MUL_ASSOC, COMPLEX_NEG_NEG] THEN
    REWRITE_TAC [COMPLEX_POW_II_2, ← GSYM COMPLEX_POW_2] THEN
    REWRITE_TAC [COMPLEX_NEG_NEG, COMPLEX_MUL_LNEG, COMPLEX_MUL_LID] THEN
    REWRITE_TAC [CEXP_NEG] THEN
    ASM_SIMP_TAC [CASN_BODY_LEMMA, CEXP_CLOG, ← ExceptT.mk (COMPLEX_FIELD
       (← q r"~(z = Cx(&0))
        ==> ((z - inv z) / (Cx(&2) * ii) = c <=>
             z pow 2 - Cx(&1) = Cx(&2) * ii * c * z)"))] THEN
    MP_TAC (← SPEC (← q r"Cx(&1) - z pow 2") CSQRT) THEN CONV_TAC COMPLEX_FIELD)

  let CASN_CSIN ← prove
   r"!z. abs(Re z) < pi / &2 \/ (abs(Re z) = pi / &2 /\ Im z = &0)
       ==> casn(csin z) = z"
   (GEN_TAC THEN DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    REWRITE_TAC [csin, casn, COMPLEX_MUL_LNEG, CEXP_NEG] THEN
    SIMP_TAC [CEXP_NZ, ← ExceptT.mk (COMPLEX_FIELD
      (← q r"~(z = Cx(&0))
       ==> Cx(&1) - ((z - inv z) / (Cx(&2) * ii)) pow 2 =
           ((z + inv z) / Cx(&2)) pow 2"))] THEN
    SUBGOAL_THEN
     (← q r"csqrt(((cexp(ii * z) + inv(cexp(ii * z))) / Cx(&2)) pow 2) =
      (cexp(ii * z) + inv(cexp(ii * z))) / Cx(&2)")
    SUBST1_TAC THENL
     [MATCH_MP_TAC POW_2_CSQRT THEN REWRITE_TAC [← GSYM CEXP_NEG] THEN
      REWRITE_TAC [complex_div, ← GSYM CX_INV, RE_MUL_CX, IM_MUL_CX] THEN
      REWRITE_TAC [← REAL_ARITH
       (← q r"&0 < r * inv(&2) \/ r * inv(&2) = &0 /\ &0 <= i * inv(&2) <=>
        &0 < r \/ r = &0 /\ &0 <= i")] THEN
      REWRITE_TAC [RE_ADD, IM_ADD, RE_CEXP, IM_CEXP] THEN
      REWRITE_TAC [RE_MUL_II, RE_NEG, IM_MUL_II, IM_NEG] THEN
      REWRITE_TAC [SIN_NEG, COS_NEG, REAL_NEG_NEG] THEN
      REWRITE_TAC [REAL_MUL_RNEG, ← GSYM real_sub] THEN
      REWRITE_TAC [← GSYM REAL_ADD_RDISTRIB, ← GSYM REAL_SUB_RDISTRIB] THEN
      FIRST_X_ASSUM (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
       [DISJ1_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_SIMP_TAC [REAL_LT_ADD, REAL_EXP_POS_LT] THEN
        MATCH_MP_TAC COS_POS_PI THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC,
        DISJ2_TAC THEN ASM_REWRITE_TAC [SIN_PI2, COS_PI2] THEN
        REWRITE_TAC [REAL_EXP_NEG, REAL_EXP_0, REAL_INV_1, REAL_SUB_REFL] THEN
        REWRITE_TAC [REAL_MUL_LZERO, REAL_LE_REFL, REAL_ENTIRE] THEN
        FIRST_X_ASSUM (DISJ_CASES_THEN SUBST1_TAC o MATCH_MP (← REAL_ARITH
         (← q r"abs(x) = p ==> x = p \/ x = --p"))) THEN
        REWRITE_TAC [COS_PI2, COS_NEG] THEN REAL_ARITH_TAC],
      ALL_TAC] THEN
    SIMP_TAC [← ExceptT.mk (COMPLEX_FIELD
     (← q r"ii * (a - b) / (Cx(&2) * ii) + (a + b) / Cx(&2) = a"))] THEN
    SIMP_TAC [← ExceptT.mk (COMPLEX_FIELD (← q r"--(ii * w) = z <=> w = ii * z"))] THEN
    MATCH_MP_TAC CLOG_CEXP THEN REWRITE_TAC [IM_MUL_II] THEN
    MP_TAC PI_POS THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC)

  let CASN_UNIQUE ← prove
   r"!w z. csin(z) = w /\
         (abs(Re z) < pi / &2 \/ (abs(Re z) = pi / &2 /\ Im z = &0))
         ==> casn w = z"
   (MESON_TAC [CASN_CSIN])

  let CASN_0 ← prove
   r"casn(Cx(&0)) = Cx(&0)"
   (REWRITE_TAC [casn, COMPLEX_MUL_RZERO, COMPLEX_ADD_LID, COMPLEX_POW_2,
                 COMPLEX_SUB_RZERO, CSQRT_1, CLOG_1, COMPLEX_MUL_RZERO])

  let CASN_1 ← prove
   r"casn(Cx(&1)) = Cx(pi / &2)"
   (REWRITE_TAC [casn, ← GSYM CX_POW, ← GSYM CX_SUB] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [CSQRT_0, COMPLEX_MUL_RID, COMPLEX_ADD_RID] THEN
    REWRITE_TAC [CLOG_II] THEN CONV_TAC COMPLEX_RING)

  let CASN_NEG_1 ← prove
   r"casn(--Cx(&1)) = --Cx(pi / &2)"
   (REWRITE_TAC [casn, ← GSYM CX_NEG, ← GSYM CX_POW, ← GSYM CX_SUB] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [CSQRT_0, COMPLEX_MUL_RID, COMPLEX_ADD_RID] THEN
    REWRITE_TAC [CX_NEG, COMPLEX_MUL_RID, COMPLEX_MUL_RNEG] THEN
    REWRITE_TAC [CLOG_NEG_II] THEN CONV_TAC COMPLEX_RING)

  let HAS_COMPLEX_DERIVATIVE_CASN ← prove
   r"!z. (Im z = &0 ==> abs(Re z) < &1)
       ==> (casn has_complex_derivative inv(ccos(casn z))) (at z)"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_INVERSE_BASIC THEN
    EXISTS_TAC (← q r"csin") THEN
    REWRITE_TAC [CSIN_CASN, HAS_COMPLEX_DERIVATIVE_CSIN, CONTINUOUS_AT_CSIN] THEN
    EXISTS_TAC (← q r"ball(z:complex,&1)") THEN
    REWRITE_TAC [OPEN_BALL, CENTRE_IN_BALL, REAL_LT_01] THEN CONJ_TAC THENL
     [DISCH_THEN (MP_TAC o MATCH_MP (← ExceptT.mk (COMPLEX_RING
       (← q r"ccos z = Cx(&0) ==> csin(z) pow 2 + ccos(z) pow 2 = Cx(&1)
                            ==> csin(z) pow 2 = Cx(&1)")))) THEN
      REWRITE_TAC [CSIN_CASN, CSIN_CIRCLE] THEN
      REWRITE_TAC [← ExceptT.mk (COMPLEX_RING
       (← q r"z pow 2 = Cx(&1) <=> z = Cx(&1) \/ z = --Cx(&1)"))] THEN
      DISCH_THEN (DISJ_CASES_THEN SUBST_ALL_TAC) THEN
      POP_ASSUM MP_TAC THEN REWRITE_TAC [RE_CX, IM_CX, RE_NEG, IM_NEG] THEN
      REAL_ARITH_TAC,
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM ETA_AX] THEN REWRITE_TAC [casn] THEN
    MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN REWRITE_TAC [CONTINUOUS_CONST] THEN
    ONCE_REWRITE_TAC [← GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ADD THEN
      SIMP_TAC [CONTINUOUS_COMPLEX_MUL, CONTINUOUS_CONST, CONTINUOUS_AT_ID] THEN
      ONCE_REWRITE_TAC [← GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
      SIMP_TAC [CONTINUOUS_COMPLEX_POW, CONTINUOUS_SUB,
                CONTINUOUS_CONST, CONTINUOUS_AT_ID] THEN
      MATCH_MP_TAC CONTINUOUS_AT_CSQRT THEN
      REWRITE_TAC [RE_SUB, IM_SUB, RE_CX, IM_CX, RE_POW_2, IM_POW_2] THEN
      REWRITE_TAC [← REAL_RING (← q r"&0 - &2 * x * y = &0 <=> x = &0 \/ y = &0")] THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [REAL_POW_2, REAL_MUL_LZERO, REAL_SUB_RZERO,
                       ← REAL_ARITH (← q r"&1 - (&0 - x) = &1 + x")] THEN
      ASM_SIMP_TAC [REAL_LE_SQUARE, ← REAL_ARITH (← q r"&0 <= x ==> &0 < &1 + x")] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"&0 < &1 - x * x <=> x pow 2 < &1 pow 2")] THEN
      ONCE_REWRITE_TAC [← GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
      ASM_SIMP_TAC [REAL_ABS_POS, REAL_ABS_NUM, ARITH],
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_AT_CLOG THEN
    REWRITE_TAC [IM_ADD, IM_MUL_II, RE_ADD, RE_MUL_II] THEN
    ASM_CASES_TAC (← q r"Im z = &0") THENL
     [DISCH_THEN (K ALL_TAC) THEN ASM_REWRITE_TAC [csqrt] THEN
      ASM_REWRITE_TAC [IM_SUB, RE_SUB, IM_CX, RE_CX, IM_POW_2, RE_POW_2,
                       REAL_MUL_RZERO, REAL_SUB_REFL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [← REAL_ARITH (← q r"&0 <= &1 - (z pow 2 - &0) <=> z pow 2 <= &1 pow 2"),
                   ← GSYM REAL_LE_SQUARE_ABS] THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE, REAL_ABS_NUM, RE, REAL_ADD_LID] THEN
      MATCH_MP_TAC SQRT_POS_LT THEN
      REWRITE_TAC [← REAL_ARITH (← q r"&0 < &1 - (z pow 2 - &0) <=> z pow 2 < &1 pow 2"),
                   ← GSYM REAL_LT_SQUARE_ABS] THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [csqrt, IM_SUB, RE_SUB, IM_CX, RE_CX, IM_POW_2, RE_POW_2] THEN
    REWRITE_TAC [← REAL_RING (← q r"&0 - &2 * x * y = &0 <=> x = &0 \/ y = &0")] THEN
    ASM_CASES_TAC (← q r"Re z = &0") THEN ASM_REWRITE_TAC [RE, IM] THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [← REAL_ARITH (← q r"&1 - (&0 - x) = &1 + x")] THEN
      SIMP_TAC [REAL_POW_2, REAL_LE_ADD, REAL_LE_SQUARE, REAL_POS] THEN
      REWRITE_TAC [RE, IM, REAL_ADD_LID, ← REAL_ARITH (← q r"&0 < --x + y <=> x < y")] THEN
      MATCH_MP_TAC REAL_LT_RSQRT THEN REAL_ARITH_TAC,
      ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC [← REAL_ARITH (← q r"&0 < --x + y <=> x < y")] THEN
    MATCH_MP_TAC REAL_LT_RSQRT THEN
    REWRITE_TAC [REAL_POW_2, ← REAL_ARITH
     (← q r"a < (n + &1 - (b - a)) / &2 <=> (a + b) - &1 < n")] THEN
    REWRITE_TAC [complex_norm] THEN MATCH_MP_TAC REAL_LT_RSQRT THEN
    REWRITE_TAC [RE_SUB, IM_SUB, RE_CX, IM_CX, RE_POW_2, IM_POW_2] THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o
      GEN_REWRITE_RULE id [← GSYM REAL_LT_SQUARE])) THEN
    REAL_ARITH_TAC)

  let COMPLEX_DIFFERENTIABLE_AT_CASN ← prove
   r"!z. (Im z = &0 ==> abs(Re z) < &1) ==> casn complex_differentiable at z"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_CASN])

  let COMPLEX_DIFFERENTIABLE_WITHIN_CASN ← prove
   r"!s z. (Im z = &0 ==> abs(Re z) < &1)
         ==> casn complex_differentiable (at z within s)"
   (MESON_TAC [COMPLEX_DIFFERENTIABLE_AT_WITHIN,
               COMPLEX_DIFFERENTIABLE_AT_CASN])

  add_complex_differentiation_theorems
   (CONJUNCTS (← REWRITE_RULE [FORALL_AND_THM]
     (← MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
               HAS_COMPLEX_DERIVATIVE_CASN)))

  let CONTINUOUS_AT_CASN ← prove
   r"!z. (Im z = &0 ==> abs(Re z) < &1) ==> casn continuous at z"
   (MESON_TAC [HAS_COMPLEX_DERIVATIVE_CASN,
               HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT])

  let CONTINUOUS_WITHIN_CASN ← prove
   r"!s z. (Im z = &0 ==> abs(Re z) < &1) ==> casn continuous (at z within s)"
   (MESON_TAC [CONTINUOUS_AT_WITHIN, CONTINUOUS_AT_CASN])

  let CONTINUOUS_ON_CASN ← prove
   r"!s. (!z. z IN s /\ Im z = &0 ==> abs(Re z) < &1) ==> casn continuous_on s"
   (MESON_TAC [CONTINUOUS_AT_IMP_CONTINUOUS_ON, CONTINUOUS_AT_CASN])

  let HOLOMORPHIC_ON_CASN ← prove
   r"!s. (!z. z IN s /\ Im z = &0 ==> abs(Re z) < &1) ==> casn holomorphic_on s"
   (REWRITE_TAC [holomorphic_on] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN, HAS_COMPLEX_DERIVATIVE_CASN])

  pure { casn, CASN_BODY_LEMMA, CSIN_CASN, CASN_CSIN, CASN_UNIQUE, CASN_0, CASN_1,
         CASN_NEG_1, HAS_COMPLEX_DERIVATIVE_CASN, COMPLEX_DIFFERENTIABLE_AT_CASN,
         COMPLEX_DIFFERENTIABLE_WITHIN_CASN, CONTINUOUS_AT_CASN, CONTINUOUS_WITHIN_CASN,
         CONTINUOUS_ON_CASN, HOLOMORPHIC_ON_CASN }
/- ------------------------------------------------------------------------- -/
/- Inverse cosine.                                                           -/
/- (transcendentals.ml 4889-5106)                                           -/
/- ------------------------------------------------------------------------- -/

structure TST where
  cacs : thm
  CACS_BODY_LEMMA : thm
  CCOS_CACS : thm
  CACS_CCOS : thm
  CACS_UNIQUE : thm
  CACS_0 : thm
  CACS_1 : thm
  CACS_NEG_1 : thm
  HAS_COMPLEX_DERIVATIVE_CACS : thm
  COMPLEX_DIFFERENTIABLE_AT_CACS : thm
  COMPLEX_DIFFERENTIABLE_WITHIN_CACS : thm
  CONTINUOUS_AT_CACS : thm
  CONTINUOUS_WITHIN_CACS : thm
  CONTINUOUS_ON_CACS : thm
  HOLOMORPHIC_ON_CACS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTST [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) (BTSB : TSB) (BTSC : TSC) (BTSE : TSE) (BTSM : TSM) (BTSN : TSN) (BTSR : TSR) : ExceptT String IO TST := do
  -- @@SCOPE BEGIN
  let { CEXP_NEG, CEXP_NZ, .. } := BTSA
  let { ccos, CSIN_CIRCLE, REAL_EXP_MONO_LE, REAL_EXP_POS_LT, .. } := BTSB
  let { CONTINUOUS_AT_CCOS, COS_0, COS_NEG, CX_COS, HAS_COMPLEX_DERIVATIVE_CCOS, IM_CEXP,
        RE_CEXP, SIN_0, SIN_NEG, .. } := BTSC
  let { COS_PI, COS_PI2, PI_POS, SIN_PI, SIN_POS_PI, .. } := BTSE
  let { CEXP_CLOG, CLOG_CEXP, CONTINUOUS_AT_CLOG, .. } := BTSM
  let { CONTINUOUS_AT_CSQRT, .. } := BTSN
  let { IM_POW_2, RE_POW_2, .. } := BTSR
  let { CONTINUOUS_COMPLEX_MUL, CONTINUOUS_COMPLEX_POW, .. } := D.knc
  let { complex_differentiable, COMPLEX_DIFFERENTIABLE_AT_WITHIN,
        HAS_COMPLEX_DERIVATIVE_AT_WITHIN, HAS_COMPLEX_DERIVATIVE_CHAIN,
        HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT, holomorphic_on, .. } := D.kne
  let { HAS_COMPLEX_DERIVATIVE_INVERSE_BASIC, .. } := D.knj
  let { add_complex_differentiation_theorems, .. } := D.knk
  let { CONTINUOUS_AT_COMPOSE, .. } := D.qtopology
  let { REAL_LT_RSQRT, REAL_LT_SQUARE, REAL_POW_LT2, REAL_SUB_RNEG, .. } := D.qsession
  let { ABS_SQUARE_LT_1, .. } := D.qmisc
  let { complex_div, complex_norm, IM, RE, .. } := D.cn.cxa
  let { COMPLEX_MUL_ASSOC, COMPLEX_MUL_LID, COMPLEX_MUL_LNEG, COMPLEX_MUL_RNEG,
        COMPLEX_NEG_NEG, .. } := D.cn.cxb
  let { COMPLEX_POW_2, COMPLEX_POW_II_2, CX_INV, CX_NEG, IM_ADD, IM_CX, IM_MUL_CX,
        IM_MUL_II, IM_NEG, IM_SUB, RE_ADD, RE_CX, RE_MUL_CX, RE_MUL_II, RE_NEG, RE_SUB,
        .. } := D.cn.cxc
  let { COMPLEX_RING, .. } := D.cn.cxd
  let { COMPLEX_FIELD, .. } := D.cn.cxe
  let { COMPLEX_NEG_INV, .. } := D.cn.cxf
  let { CSQRT, csqrt, POW_2_CSQRT, .. } := D.cn.cxh
  let { ASM_REAL_ARITH_TAC, MESON_TAC, new_definition, REAL_ARITH, REAL_ARITH_TAC,
        REAL_RAT_REDUCE_CONV, REAL_RING, .. } := D.cn.cx.cvx
  let { REAL_LE_SQUARE, real_sub, SQRT_POS_LT, .. } := D.cn.cx.cpx
  let { ARITH, ETA_AX, FORALL_AND_THM, .. } := D.cn.cx.cvx.core1
  let { IMP_IMP, .. } := D.cn.cx.cvx.core2
  let { REAL_ABS_NUM, REAL_ABS_POS, REAL_ADD_LID, REAL_ADD_RDISTRIB,
        .. } := D.cn.cx.cvx.core3
  let { REAL_LE_ADD, REAL_LE_REFL, REAL_LE_SQUARE_ABS, REAL_LT_01, REAL_LT_ADD,
        REAL_LT_IMP_LE, REAL_LT_MUL, REAL_LT_MUL_EQ, .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RNEG, REAL_MUL_RZERO, REAL_NEG_EQ_0,
        REAL_NEG_NEG, REAL_NEG_SUB, REAL_POS, REAL_POW2_ABS, REAL_POW_2, REAL_SUB_LE,
        REAL_SUB_LT, REAL_SUB_RDISTRIB, REAL_SUB_REFL, REAL_SUB_RZERO, SQRT_POW_2,
        .. } := D.cn.cx.cvx.core5
  let { o_DEF, .. } := D.cn.cx.cvx.core6
  let { CENTRE_IN_BALL, .. } := D.cn.cx.cvx.top1
  let { CONTINUOUS_ADD, CONTINUOUS_AT_ID, CONTINUOUS_AT_IMP_CONTINUOUS_ON,
        .. } := D.cn.cx.cvx.top2
  let { CONTINUOUS_CONST, CONTINUOUS_SUB, .. } := D.cn.cx.cvx.top3
  let { OPEN_BALL, .. } := D.cn.cx.cvx.top4
  let { CONTINUOUS_AT_WITHIN, .. } := D.cn.ms.ig.dv.qtopology1
  let { REAL_POW_NEG, .. } := D.cn.ms.ig.dv.dg.qsession
  -- @@SCOPE END

  let cacs ← new_definition
   r"cacs z = --ii * clog(z + ii * csqrt(Cx(&1) - z pow 2))"

  let CACS_BODY_LEMMA ← prove
   r"!z. ~(z + ii * csqrt(Cx(&1) - z pow 2) = Cx(&0))"
   (GEN_TAC THEN MP_TAC (← SPEC (← q r"Cx(&1) - z pow 2") CSQRT) THEN
    CONV_TAC COMPLEX_FIELD)

  let CCOS_CACS ← prove
   r"!z. ccos(cacs z) = z"
   (GEN_TAC THEN REWRITE_TAC [ccos, cacs, COMPLEX_MUL_LNEG, COMPLEX_MUL_RNEG] THEN
    REWRITE_TAC [COMPLEX_MUL_ASSOC, COMPLEX_NEG_NEG] THEN
    REWRITE_TAC [COMPLEX_POW_II_2, ← GSYM COMPLEX_POW_2] THEN
    REWRITE_TAC [COMPLEX_NEG_NEG, COMPLEX_MUL_LNEG, COMPLEX_MUL_LID] THEN
    REWRITE_TAC [CEXP_NEG] THEN
    ASM_SIMP_TAC [CACS_BODY_LEMMA, CEXP_CLOG, COMPLEX_POW_II_2, ← ExceptT.mk (COMPLEX_FIELD
       (← q r"~(z = Cx(&0))
        ==> ((z + inv z) / Cx(&2) = c <=>
             z pow 2 + Cx(&1) = Cx(&2) * c * z)"))] THEN
    MP_TAC (← SPEC (← q r"Cx(&1) - z pow 2") CSQRT) THEN CONV_TAC COMPLEX_FIELD)

  let CACS_CCOS ← prove
   r"!z. &0 < Re z /\ Re z < pi \/
       Re(z) = &0 /\ &0 <= Im(z) \/
       Re(z) = pi /\ Im(z) <= &0
       ==> cacs(ccos z) = z"
   (GEN_TAC THEN DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    REWRITE_TAC [ccos, cacs, COMPLEX_MUL_LNEG, CEXP_NEG] THEN
    SIMP_TAC [CEXP_NZ, ← ExceptT.mk (COMPLEX_FIELD
      (← q r"~(z = Cx(&0))
       ==> Cx(&1) - ((z + inv z) / Cx(&2)) pow 2 =
           --(((z - inv z) / Cx(&2)) pow 2)"))] THEN
    SUBGOAL_THEN
     (← q r"csqrt(--(((cexp(ii * z) - inv(cexp(ii * z))) / Cx(&2)) pow 2)) =
      --ii * (cexp(ii * z) - inv(cexp(ii * z))) / Cx(&2)")
    SUBST1_TAC THENL
     [SIMP_TAC [← ExceptT.mk (COMPLEX_FIELD (← q r"--(x pow 2) = (--ii * x) pow 2"))] THEN
      MATCH_MP_TAC POW_2_CSQRT THEN REWRITE_TAC [← GSYM CEXP_NEG] THEN
      REWRITE_TAC [complex_div, ← GSYM CX_INV, RE_MUL_CX, IM_MUL_CX, RE_NEG, IM_NEG,
                   COMPLEX_MUL_LNEG, RE_MUL_II, IM_MUL_II, RE_SUB, IM_SUB] THEN
      REWRITE_TAC [REAL_NEG_NEG, REAL_NEG_EQ_0] THEN
      REWRITE_TAC [← REAL_ARITH
       (← q r"&0 < r * inv(&2) \/ r * inv(&2) = &0 /\ &0 <= --(i * inv(&2)) <=>
        &0 < r \/ r = &0 /\ &0 <= --i")] THEN
      REWRITE_TAC [RE_ADD, IM_ADD, RE_CEXP, IM_CEXP] THEN
      REWRITE_TAC [RE_MUL_II, RE_NEG, IM_MUL_II, IM_NEG] THEN
      REWRITE_TAC [SIN_NEG, COS_NEG, REAL_NEG_NEG] THEN
      REWRITE_TAC [REAL_MUL_RNEG, ← GSYM real_sub, REAL_SUB_RNEG, REAL_NEG_SUB] THEN
      REWRITE_TAC [← GSYM REAL_ADD_RDISTRIB, ← GSYM REAL_SUB_RDISTRIB] THEN
      ASM_SIMP_TAC [REAL_LT_ADD, REAL_EXP_POS_LT, REAL_LT_MUL_EQ] THEN
      POP_ASSUM (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC [SIN_POS_PI] THEN DISJ2_TAC THEN
      REWRITE_TAC [SIN_PI, REAL_MUL_RZERO, COS_PI, SIN_0, COS_0] THEN
      REWRITE_TAC [REAL_MUL_RID, REAL_MUL_RNEG] THEN
      REWRITE_TAC [REAL_NEG_SUB, REAL_SUB_LE, REAL_EXP_MONO_LE] THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SIMP_TAC [← ExceptT.mk (COMPLEX_FIELD
     (← q r"(e + e') / Cx(&2) + ii * --ii * (e - e') / Cx(&2) = e"))] THEN
    SIMP_TAC [← ExceptT.mk (COMPLEX_FIELD (← q r"--(ii * w) = z <=> w = ii * z"))] THEN
    MATCH_MP_TAC CLOG_CEXP THEN REWRITE_TAC [IM_MUL_II] THEN
    MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC)

  let CACS_UNIQUE ← prove
   r"!w z.
       ccos z = w /\
       (&0 < Re z /\ Re z < pi \/
        Re(z) = &0 /\ &0 <= Im(z) \/
        Re(z) = pi /\ Im(z) <= &0)
       ==> cacs(w) = z"
   (MESON_TAC [CACS_CCOS])

  let CACS_0 ← prove
   r"cacs(Cx(&0)) = Cx(pi / &2)"
   (MATCH_MP_TAC CACS_UNIQUE THEN
    REWRITE_TAC [RE_CX, IM_CX, ← GSYM CX_COS, COS_PI2] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC)

  let CACS_1 ← prove
   r"cacs(Cx(&1)) = Cx(&0)"
   (MATCH_MP_TAC CACS_UNIQUE THEN
    REWRITE_TAC [RE_CX, IM_CX, ← GSYM CX_COS, COS_0, REAL_LE_REFL])

  let CACS_NEG_1 ← prove
   r"cacs(--Cx(&1)) = Cx pi"
   (MATCH_MP_TAC CACS_UNIQUE THEN
    REWRITE_TAC [RE_CX, IM_CX, ← GSYM CX_COS, COS_PI, CX_NEG, REAL_LE_REFL])

  let HAS_COMPLEX_DERIVATIVE_CACS ← prove
   r"!z. (Im z = &0 ==> abs(Re z) < &1)
       ==> (cacs has_complex_derivative --inv(csin(cacs z))) (at z)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [COMPLEX_NEG_INV] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_INVERSE_BASIC THEN
    EXISTS_TAC (← q r"ccos") THEN
    REWRITE_TAC [CCOS_CACS, HAS_COMPLEX_DERIVATIVE_CCOS, CONTINUOUS_AT_CCOS] THEN
    EXISTS_TAC (← q r"ball(z:complex,&1)") THEN
    REWRITE_TAC [OPEN_BALL, CENTRE_IN_BALL, REAL_LT_01] THEN CONJ_TAC THENL
     [DISCH_THEN (MP_TAC o MATCH_MP (← ExceptT.mk (COMPLEX_RING
       (← q r"--(csin z) = Cx(&0) ==> csin(z) pow 2 + ccos(z) pow 2 = Cx(&1)
                                ==> ccos(z) pow 2 = Cx(&1)")))) THEN
      REWRITE_TAC [CCOS_CACS, CSIN_CIRCLE] THEN
      REWRITE_TAC [← ExceptT.mk (COMPLEX_RING
       (← q r"z pow 2 = Cx(&1) <=> z = Cx(&1) \/ z = --Cx(&1)"))] THEN
      DISCH_THEN (DISJ_CASES_THEN SUBST_ALL_TAC) THEN
      POP_ASSUM MP_TAC THEN REWRITE_TAC [RE_CX, IM_CX, RE_NEG, IM_NEG] THEN
      REAL_ARITH_TAC,
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM ETA_AX] THEN REWRITE_TAC [cacs] THEN
    MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN REWRITE_TAC [CONTINUOUS_CONST] THEN
    ONCE_REWRITE_TAC [← GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC [CONTINUOUS_AT_ID] THEN
      MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN REWRITE_TAC [CONTINUOUS_CONST] THEN
      ONCE_REWRITE_TAC [← GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
      SIMP_TAC [CONTINUOUS_COMPLEX_POW, CONTINUOUS_SUB,
                CONTINUOUS_CONST, CONTINUOUS_AT_ID] THEN
      MATCH_MP_TAC CONTINUOUS_AT_CSQRT THEN
      REWRITE_TAC [RE_SUB, IM_SUB, RE_CX, IM_CX, RE_POW_2, IM_POW_2] THEN
      REWRITE_TAC [← REAL_RING (← q r"&0 - &2 * x * y = &0 <=> x = &0 \/ y = &0")] THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [REAL_POW_2, REAL_MUL_LZERO, REAL_SUB_RZERO,
                       ← REAL_ARITH (← q r"&1 - (&0 - x) = &1 + x")] THEN
      ASM_SIMP_TAC [REAL_LE_SQUARE, ← REAL_ARITH (← q r"&0 <= x ==> &0 < &1 + x")] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"&0 < &1 - x * x <=> x pow 2 < &1 pow 2")] THEN
      ONCE_REWRITE_TAC [← GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
      ASM_SIMP_TAC [REAL_ABS_POS, REAL_ABS_NUM, ARITH],
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_AT_CLOG THEN
    REWRITE_TAC [IM_ADD, IM_MUL_II, RE_ADD, RE_MUL_II] THEN
    ASM_CASES_TAC (← q r"Im z = &0") THENL
     [ASM_REWRITE_TAC [csqrt] THEN
      ASM_REWRITE_TAC [IM_SUB, RE_SUB, IM_CX, RE_CX, IM_POW_2, RE_POW_2,
                       REAL_MUL_RZERO, REAL_SUB_REFL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [← REAL_ARITH (← q r"&0 <= &1 - (z pow 2 - &0) <=> z pow 2 <= &1 pow 2"),
                   ← GSYM REAL_LE_SQUARE_ABS] THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE, REAL_ABS_NUM, RE, REAL_ADD_LID] THEN
      REWRITE_TAC [← GSYM real_sub, IM, REAL_SUB_LT, REAL_SUB_RZERO] THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"&0 < x ==> x = &0 ==> &0 < y")) THEN
      MATCH_MP_TAC SQRT_POS_LT THEN
      ASM_SIMP_TAC [REAL_SUB_LT, ABS_SQUARE_LT_1],
      ALL_TAC] THEN
    REWRITE_TAC [csqrt, IM_SUB, RE_SUB, IM_CX, RE_CX, IM_POW_2, RE_POW_2] THEN
    REWRITE_TAC [← REAL_RING (← q r"&0 - &2 * x * y = &0 <=> x = &0 \/ y = &0")] THEN
    ASM_CASES_TAC (← q r"Re z = &0") THEN ASM_REWRITE_TAC [RE, IM] THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [← REAL_ARITH (← q r"&1 - (&0 - x) = &1 + x")] THEN
      SIMP_TAC [REAL_POW_2, REAL_LE_ADD, REAL_LE_SQUARE, REAL_POS] THEN
      REWRITE_TAC [RE, IM, REAL_ADD_LID] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← REAL_ARITH (← q r"a + b = &0 ==> a = --b"))) THEN
      DISCH_THEN (MP_TAC o AP_TERM (← q r"\x:real. x pow 2")) THEN
      SIMP_TAC [SQRT_POW_2, REAL_POW_NEG, ARITH, REAL_LE_SQUARE, REAL_LE_ADD,
                REAL_POS] THEN
      REAL_ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN (MP_TAC o MATCH_MP (← REAL_ARITH (← q r"a + b = &0 ==> a = --b"))) THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"\x:real. x pow 2")) THEN
    SUBGOAL_THEN (← q r"&0 < (norm(Cx (&1) - z pow 2) +
                        &1 - (Re z pow 2 - Im z pow 2)) / &2")
    ASSUME_TAC THENL
     [REWRITE_TAC [← REAL_ARITH (← q r"&0 < (x + y - z) / &2 <=> z - y < x")] THEN
      REWRITE_TAC [complex_norm] THEN MATCH_MP_TAC REAL_LT_RSQRT THEN
      REWRITE_TAC [RE_SUB, IM_SUB, RE_CX, IM_CX, RE_POW_2, IM_POW_2] THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o
       GEN_REWRITE_RULE id [← GSYM REAL_LT_SQUARE])) THEN
      REWRITE_TAC [IMP_IMP] THEN DISCH_THEN (MP_TAC o MATCH_MP REAL_LT_MUL) THEN
      REAL_ARITH_TAC,
      ALL_TAC] THEN
    ASM_SIMP_TAC [SQRT_POW_2, REAL_POW_NEG, ARITH, REAL_LT_IMP_LE] THEN
    REWRITE_TAC [REAL_POW_2, ← REAL_ARITH
     (← q r"a = (n + &1 - (b - a)) / &2 <=> (a + b) - &1 = n")] THEN
    REWRITE_TAC [complex_norm] THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"\x:real. x pow 2")) THEN
    SIMP_TAC [SQRT_POW_2, ← REWRITE_RULE [← GSYM REAL_POW_2] REAL_LE_SQUARE,
              REAL_LE_ADD] THEN
    REWRITE_TAC [RE_SUB, RE_CX, RE_POW_2, IM_SUB, IM_CX, IM_POW_2] THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o
     GEN_REWRITE_RULE id [← GSYM REAL_LT_SQUARE])) THEN
    REAL_ARITH_TAC)

  let COMPLEX_DIFFERENTIABLE_AT_CACS ← prove
   r"!z. (Im z = &0 ==> abs(Re z) < &1) ==> cacs complex_differentiable at z"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_CACS])

  let COMPLEX_DIFFERENTIABLE_WITHIN_CACS ← prove
   r"!s z. (Im z = &0 ==> abs(Re z) < &1)
         ==> cacs complex_differentiable (at z within s)"
   (MESON_TAC [COMPLEX_DIFFERENTIABLE_AT_WITHIN,
               COMPLEX_DIFFERENTIABLE_AT_CACS])

  add_complex_differentiation_theorems
   (CONJUNCTS (← REWRITE_RULE [FORALL_AND_THM]
     (← MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN
               HAS_COMPLEX_DERIVATIVE_CACS)))

  let CONTINUOUS_AT_CACS ← prove
   r"!z. (Im z = &0 ==> abs(Re z) < &1) ==> cacs continuous at z"
   (MESON_TAC [HAS_COMPLEX_DERIVATIVE_CACS,
               HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT])

  let CONTINUOUS_WITHIN_CACS ← prove
   r"!s z. (Im z = &0 ==> abs(Re z) < &1) ==> cacs continuous (at z within s)"
   (MESON_TAC [CONTINUOUS_AT_WITHIN, CONTINUOUS_AT_CACS])

  let CONTINUOUS_ON_CACS ← prove
   r"!s. (!z. z IN s /\ Im z = &0 ==> abs(Re z) < &1) ==> cacs continuous_on s"
   (MESON_TAC [CONTINUOUS_AT_IMP_CONTINUOUS_ON, CONTINUOUS_AT_CACS])

  let HOLOMORPHIC_ON_CACS ← prove
   r"!s. (!z. z IN s /\ Im z = &0 ==> abs(Re z) < &1) ==> cacs holomorphic_on s"
   (REWRITE_TAC [holomorphic_on] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN, HAS_COMPLEX_DERIVATIVE_CACS])

  pure { cacs, CACS_BODY_LEMMA, CCOS_CACS, CACS_CCOS, CACS_UNIQUE, CACS_0, CACS_1,
         CACS_NEG_1, HAS_COMPLEX_DERIVATIVE_CACS, COMPLEX_DIFFERENTIABLE_AT_CACS,
         COMPLEX_DIFFERENTIABLE_WITHIN_CACS, CONTINUOUS_AT_CACS, CONTINUOUS_WITHIN_CACS,
         CONTINUOUS_ON_CACS, HOLOMORPHIC_ON_CACS }
/- ------------------------------------------------------------------------- -/
/- Some crude range theorems (could be sharpened).                           -/
/- (transcendentals.ml 5107-5183)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSU where
  CASN_RANGE_LEMMA : thm
  CACS_RANGE_LEMMA : thm
  RE_CASN : thm
  RE_CACS : thm
  CASN_BOUNDS : thm
  CACS_BOUNDS : thm
  RE_CACS_BOUNDS : thm
  RE_CACS_BOUND : thm
  RE_CASN_BOUNDS : thm
  RE_CASN_BOUND : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSU [HolBase] (D : TranscendentalsDeps) (BTSM : TSM) (BTSN : TSN) (BTSS : TSS) (BTST : TST) : ExceptT String IO TSU := do
  -- @@SCOPE BEGIN
  let { CLOG_WORKS, .. } := BTSM
  let { IM_CLOG_POS_LT_IMP, RE_CLOG_POS_LT_IMP, .. } := BTSN
  let { casn, CASN_BODY_LEMMA, .. } := BTSS
  let { cacs, CACS_BODY_LEMMA, .. } := BTST
  let { REAL_LT_RSQRT, REAL_LT_SQUARE, REAL_POW_LT2, .. } := D.qsession
  let { complex_mul, complex_norm, IM, RE, .. } := D.cn.cxa
  let { COMPLEX_MUL_LNEG, .. } := D.cn.cxb
  let { COMPLEX_POW_2, COMPLEX_POW_NEG, IM_ADD, IM_CX, IM_MUL_II, IM_NEG, IM_SUB, RE_ADD,
        RE_CX, RE_MUL_II, RE_NEG, RE_SUB, .. } := D.cn.cxc
  let { csqrt, .. } := D.cn.cxh
  let { ASM_REAL_ARITH_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV,
        .. } := D.cn.cx.cvx
  let { REAL_LE_SQUARE, REAL_SUB_LZERO, SQRT_POS_LT, .. } := D.cn.cx.cpx
  let { ARITH, .. } := D.cn.cx.cvx.core1
  let { MONO_FORALL, REAL_ABS_NEG, REAL_ABS_NUM, REAL_ABS_POS, .. } := D.cn.cx.cvx.core3
  let { REAL_ENTIRE, REAL_LE_ADD, .. } := D.cn.cx.cvx.core4
  let { REAL_NEG_EQ_0, REAL_NEG_NEG, REAL_NEG_SUB, REAL_OF_NUM_EQ, REAL_POS, REAL_POW2_ABS,
        REAL_POW_2, REAL_POW_ONE, REAL_SUB_RZERO, SQRT_1, .. } := D.cn.cx.cvx.core5
  -- @@SCOPE END

  let CASN_RANGE_LEMMA ← prove
   r"!z. abs (Re z) < &1 ==> &0 < Re(ii * z + csqrt(Cx(&1) - z pow 2))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [RE_ADD, RE_MUL_II] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"&0 < --i + r <=> i < r")] THEN
    REWRITE_TAC [csqrt, IM_SUB, RE_SUB, COMPLEX_POW_2, RE_CX, IM_CX] THEN
    REWRITE_TAC [complex_mul, RE, IM] THEN REWRITE_TAC [← GSYM complex_mul] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"r * i + i * r = &2 * r * i")] THEN
    REWRITE_TAC [REAL_SUB_LZERO, REAL_NEG_EQ_0, REAL_ABS_NEG] THEN
    REWRITE_TAC [REAL_NEG_SUB, REAL_ENTIRE, REAL_OF_NUM_EQ, ARITH] THEN
    MAP_EVERY ASM_CASES_TAC [← q r"Re z = &0", ← q r"Im z = &0"] THEN
    ASM_REWRITE_TAC [REAL_SUB_LZERO, REAL_SUB_RZERO] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [RE, SQRT_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV THENL
     [REWRITE_TAC [← REAL_ARITH (← q r"&1 - (&0 - z) = &1 + z")] THEN
      SIMP_TAC [REAL_LE_ADD, REAL_POS, REAL_LE_SQUARE, RE] THEN
      MATCH_MP_TAC REAL_LT_RSQRT THEN REAL_ARITH_TAC,
      SUBGOAL_THEN (← q r"Re(z) pow 2 < &1 pow 2") MP_TAC THENL
       [ONCE_REWRITE_TAC [← GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
        ASM_REWRITE_TAC [REAL_ABS_POS, REAL_ABS_NUM, ARITH],
        REWRITE_TAC [REAL_POW_ONE] THEN STRIP_TAC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [RE] THEN
      TRY (MATCH_MP_TAC SQRT_POS_LT) THEN ASM_REAL_ARITH_TAC,
      MATCH_MP_TAC REAL_LT_RSQRT THEN
      REWRITE_TAC [REAL_POW_2, ← REAL_ARITH
       (← q r"a < (n + &1 - (b - a)) / &2 <=> (a + b) - &1 < n")] THEN
      REWRITE_TAC [complex_norm] THEN MATCH_MP_TAC REAL_LT_RSQRT THEN
      REWRITE_TAC [RE_SUB, IM_SUB, RE_CX, IM_CX] THEN
      REWRITE_TAC [complex_mul, RE, IM] THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o
        GEN_REWRITE_RULE id [← GSYM REAL_LT_SQUARE])) THEN
      REAL_ARITH_TAC])

  let CACS_RANGE_LEMMA ← prove
   r"!z. abs(Re z) < &1 ==> &0 < Im(z + ii * csqrt(Cx(&1) - z pow 2))"
   (REPEAT STRIP_TAC THEN MP_TAC (← SPEC (← q r"--z:complex") CASN_RANGE_LEMMA) THEN
    ASM_SIMP_TAC [IM_NEG, RE_NEG, IM_ADD, RE_ADD, IM_MUL_II, RE_MUL_II,
                  COMPLEX_POW_NEG, ARITH, REAL_ABS_NEG] THEN
    REAL_ARITH_TAC)

  let RE_CASN ← prove
   r"!z. Re(casn z) = Im(clog(ii * z + csqrt(Cx(&1) - z pow 2)))"
   (REWRITE_TAC [casn, COMPLEX_MUL_LNEG, RE_NEG, RE_MUL_II, REAL_NEG_NEG])

  let RE_CACS ← prove
   r"!z. Re(cacs z) = Im(clog(z + ii * csqrt(Cx(&1) - z pow 2)))"
   (REWRITE_TAC [cacs, COMPLEX_MUL_LNEG, RE_NEG, RE_MUL_II, REAL_NEG_NEG])

  let CASN_BOUNDS ← prove
   r"!z. abs(Re z) < &1 ==> abs(Re(casn z)) < pi / &2"
   (GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [RE_CASN] THEN
    MATCH_MP_TAC RE_CLOG_POS_LT_IMP THEN ASM_SIMP_TAC [CASN_RANGE_LEMMA])

  let CACS_BOUNDS ← prove
   r"!z. abs(Re z) < &1 ==> &0 < Re(cacs z) /\ Re(cacs z) < pi"
   (GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [RE_CACS] THEN
    MATCH_MP_TAC IM_CLOG_POS_LT_IMP THEN ASM_SIMP_TAC [CACS_RANGE_LEMMA])

  let RE_CACS_BOUNDS ← prove
   r"!z. --pi < Re(cacs z) /\ Re(cacs z) <= pi"
   (REWRITE_TAC [RE_CACS] THEN SIMP_TAC [CLOG_WORKS, CACS_BODY_LEMMA])

  let RE_CACS_BOUND ← prove
   r"!z. abs(Re(cacs z)) <= pi"
   (MP_TAC RE_CACS_BOUNDS THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC)

  let RE_CASN_BOUNDS ← prove
   r"!z. --pi < Re(casn z) /\ Re(casn z) <= pi"
   (REWRITE_TAC [RE_CASN] THEN SIMP_TAC [CLOG_WORKS, CASN_BODY_LEMMA])

  let RE_CASN_BOUND ← prove
   r"!z. abs(Re(casn z)) <= pi"
   (MP_TAC RE_CASN_BOUNDS THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC)

  pure { CASN_RANGE_LEMMA, CACS_RANGE_LEMMA, RE_CASN, RE_CACS, CASN_BOUNDS, CACS_BOUNDS,
         RE_CACS_BOUNDS, RE_CACS_BOUND, RE_CASN_BOUNDS, RE_CASN_BOUND }

/- ------------------------------------------------------------------------- -/
/- Interrelations between the two functions; real arcsin.                  -/
/- (transcendentals.ml 5184-5410)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSV where
  CCOS_CASN_NZ : thm
  CSIN_CACS_NZ : thm
  CCOS_CSIN_CSQRT : thm
  CSIN_CCOS_CSQRT : thm
  CASN_CACS_SQRT_POS : thm
  CACS_CASN_SQRT_POS : thm
  CSIN_CACS : thm
  CCOS_CASN : thm
  asn : thm
  REAL_ASN : thm
  CX_ASN : thm
  SIN_ASN : thm
  ASN_SIN : thm
  ASN_BOUNDS_LT : thm
  ASN_0 : thm
  ASN_1 : thm
  ASN_NEG_1 : thm
  ASN_BOUNDS : thm
  ASN_BOUNDS_PI2 : thm
  ASN_NEG : thm
  COS_ASN_NZ : thm
  ASN_MONO_LT_EQ : thm
  ASN_MONO_LE_EQ : thm
  ASN_MONO_LT : thm
  ASN_MONO_LE : thm
  COS_ASN : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSV [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) (BTSB : TSB) (BTSC : TSC) (BTSE : TSE) (BTSF : TSF) (BTSL : TSL) (BTSM : TSM) (BTSS : TSS) (BTST : TST) (BTSU : TSU) : ExceptT String IO TSV := do
  -- @@SCOPE BEGIN
  let { CEXP_NEG, .. } := BTSA
  let { ccos, csin, CSIN_CIRCLE, REAL_EXP_INJ, REAL_EXP_MONO_LT, REAL_EXP_POS_LT,
        .. } := BTSB
  let { CX_COS, CX_SIN, IM_CCOS, IM_CSIN, RE_CCOS, RE_CSIN, SIN_0, SIN_BOUND, SIN_CIRCLE,
        SIN_NEG, .. } := BTSC
  let { COS_POS_PI_LE, PI_POS, .. } := BTSE
  let { NORM_CEXP_IMAGINARY, .. } := BTSF
  let { SIN_MONO_LE_EQ, SIN_MONO_LT_EQ, .. } := BTSL
  let { CEXP_CLOG, .. } := BTSM
  let { casn, CASN_0, CASN_1, CASN_BODY_LEMMA, CASN_CSIN, CASN_NEG_1, CSIN_CASN,
        .. } := BTSS
  let { cacs, CACS_BODY_LEMMA, CCOS_CACS, .. } := BTST
  let { CASN_BOUNDS, .. } := BTSU
  let { DOT_SQUARE_NORM, .. } := D.qvectors
  let { REAL_LT_SUB_RADD, REAL_MUL_POS_LE, .. } := D.qsession
  let { COMPLEX_SQNORM, .. } := D.cn.cxa
  let { COMPLEX_ADD_SYM, COMPLEX_EQ_SUB_LADD, COMPLEX_MUL_LNEG, .. } := D.cn.cxb
  let { CX_INJ, CX_NEG, CX_POW, CX_SUB, IM_ADD, IM_CX, IM_MUL_II, IM_NEG, RE_ADD, RE_CX,
        RE_MUL_II, RE_NEG, .. } := D.cn.cxc
  let { COMPLEX_RING, .. } := D.cn.cxd
  let { COMPLEX_FIELD, .. } := D.cn.cxe
  let { CSQRT, CSQRT_UNIQUE, CX_SQRT, .. } := D.cn.cxh
  let { REAL, real, REAL_CX, .. } := D.cn.cxi
  let { REAL_EQ_SUB_RADD, .. } := D.cn.qsession
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC, new_definition, REAL_ARITH,
        REAL_ARITH_TAC, .. } := D.cn.cx.cvx
  let { ARITH, CONJ_ASSOC, EQ_TRANS, .. } := D.cn.cx.cvx.core1
  let { IMP_CONJ, .. } := D.cn.cx.cvx.core2
  let { MONO_FORALL, REAL_ADD_LID, REAL_ADD_SYM, .. } := D.cn.cx.cvx.core3
  let { REAL_LE_LT, REAL_LT_ADD, REAL_LT_LDIV_EQ, REAL_LT_MUL_EQ, REAL_LT_RDIV_EQ,
        .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_NEG_0, REAL_NEG_EQ_0, REAL_NOT_LT,
        REAL_OF_NUM_LT, REAL_SUB_0, REAL_SUB_LE, REAL_SUB_LT, SQRT_POW_2,
        .. } := D.cn.cx.cvx.core5
  let { ABS_SQUARE_LE_1, REAL_HALF, .. } := D.cn.cx.cvx.misc
  let { NORM_EQ_SQUARE, .. } := D.cn.cx.cvx.vec2
  let { SQRT_UNIQUE, .. } := D.cn.ms.ig.dv.dg.qsession
  -- @@SCOPE END

  let CCOS_CASN_NZ ← prove
   r"!z. ~(z pow 2 = Cx(&1)) ==> ~(ccos(casn z) = Cx(&0))"
   (REWRITE_TAC [ccos, casn, CEXP_NEG, ← ExceptT.mk (COMPLEX_RING (← q r"ii * --ii * z = z")),
                 ← ExceptT.mk (COMPLEX_RING (← q r"--ii * --ii * z = --z"))] THEN
    SIMP_TAC [CEXP_CLOG, CASN_BODY_LEMMA,
              ← ExceptT.mk (COMPLEX_FIELD (← q r"~(x = Cx(&0))
                             ==> ((x + inv(x)) / Cx(&2) = Cx(&0) <=>
                                   x pow 2 = --Cx(&1))"))] THEN
    SIMP_TAC [CSQRT, ← ExceptT.mk (COMPLEX_FIELD
                 (← q r"s pow 2 = Cx(&1) - z pow 2
                  ==> ((ii * z + s) pow 2 = --Cx(&1) <=>
                       ii * s * z = Cx(&1) - z pow 2)"))] THEN
    GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC (← ExceptT.mk (COMPLEX_RING
     (← q r"~(x pow 2 + y pow 2 = Cx(&0)) ==> ~(ii * x = y)"))) THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    MP_TAC (← SPEC (← q r"Cx(&1) - z pow 2") CSQRT) THEN CONV_TAC COMPLEX_RING)

  let CSIN_CACS_NZ ← prove
   r"!z. ~(z pow 2 = Cx(&1)) ==> ~(csin(cacs z) = Cx(&0))"
   (REWRITE_TAC [csin, cacs, CEXP_NEG, ← ExceptT.mk (COMPLEX_RING (← q r"ii * --ii * z = z")),
                 ← ExceptT.mk (COMPLEX_RING (← q r"--ii * --ii * z = --z"))] THEN
    SIMP_TAC [CEXP_CLOG, CACS_BODY_LEMMA,
              ← ExceptT.mk (COMPLEX_FIELD (← q r"~(x = Cx(&0))
                             ==> ((x - inv(x)) / (Cx(&2) * ii) = Cx(&0) <=>
                                   x pow 2 = Cx(&1))"))] THEN
    SIMP_TAC [CSQRT, ← ExceptT.mk (COMPLEX_FIELD
                 (← q r"s pow 2 = Cx(&1) - z pow 2
                  ==> ((z + ii * s) pow 2 = Cx(&1) <=>
                       ii * s * z = Cx(&1) - z pow 2)"))] THEN
    GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC (← ExceptT.mk (COMPLEX_RING
     (← q r"~(x pow 2 + y pow 2 = Cx(&0)) ==> ~(ii * x = y)"))) THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    MP_TAC (← SPEC (← q r"Cx(&1) - z pow 2") CSQRT) THEN CONV_TAC COMPLEX_RING)

  let CCOS_CSIN_CSQRT ← prove
   r"!z. &0 < cos(Re z) \/ cos(Re z) = &0 /\ Im(z) * sin(Re z) <= &0
       ==> ccos(z) = csqrt(Cx(&1) - csin(z) pow 2)"
   (REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CSQRT_UNIQUE THEN
    REWRITE_TAC [COMPLEX_EQ_SUB_LADD] THEN ONCE_REWRITE_TAC [COMPLEX_ADD_SYM] THEN
    REWRITE_TAC [CSIN_CIRCLE] THEN REWRITE_TAC [RE_CCOS, IM_CCOS] THEN
    ASM_SIMP_TAC [REAL_LT_MUL_EQ, REAL_HALF, REAL_LT_ADD, REAL_EXP_POS_LT] THEN
    DISJ2_TAC THEN REWRITE_TAC [REAL_MUL_RZERO] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP (← REAL_ARITH
     (← q r"x * y <= &0 ==> &0 <= --x * y"))) THEN
    REWRITE_TAC [REAL_MUL_POS_LE] THEN
    SIMP_TAC [← REAL_ARITH (← q r"x / &2 = &0 <=> x = &0"), REAL_LT_RDIV_EQ, REAL_ADD_LID,
              REAL_SUB_LT, REAL_LT_LDIV_EQ, REAL_OF_NUM_LT, ARITH, REAL_MUL_LZERO,
              REAL_SUB_0, REAL_EXP_MONO_LT, REAL_LT_SUB_RADD, REAL_EXP_INJ] THEN
    REAL_ARITH_TAC)

  let CSIN_CCOS_CSQRT ← prove
   r"!z. &0 < sin(Re z) \/ sin(Re z) = &0 /\ &0 <= Im(z) * cos(Re z)
       ==> csin(z) = csqrt(Cx(&1) - ccos(z) pow 2)"
   (REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CSQRT_UNIQUE THEN
    REWRITE_TAC [COMPLEX_EQ_SUB_LADD] THEN ONCE_REWRITE_TAC [COMPLEX_ADD_SYM] THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [COMPLEX_ADD_SYM] CSIN_CIRCLE] THEN
    REWRITE_TAC [RE_CSIN, IM_CSIN] THEN
    ASM_SIMP_TAC [REAL_LT_MUL_EQ, REAL_HALF, REAL_LT_ADD, REAL_EXP_POS_LT] THEN
    DISJ2_TAC THEN REWRITE_TAC [REAL_MUL_RZERO] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    REWRITE_TAC [REAL_MUL_POS_LE] THEN
    SIMP_TAC [← REAL_ARITH (← q r"x / &2 = &0 <=> x = &0"), REAL_LT_RDIV_EQ, REAL_ADD_LID,
              REAL_SUB_LT, REAL_LT_LDIV_EQ, REAL_OF_NUM_LT, ARITH, REAL_MUL_LZERO,

              REAL_SUB_0, REAL_EXP_MONO_LT, REAL_LT_SUB_RADD, REAL_EXP_INJ] THEN
    REAL_ARITH_TAC)

  let CASN_CACS_SQRT_POS ← prove
   r"!z. (&0 < Re z \/ Re z = &0 /\ &0 <= Im z)
       ==> casn(z) = cacs(csqrt(Cx(&1) - z pow 2))"
   (GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [casn, cacs] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC (← ExceptT.mk (COMPLEX_RING (← q r"w = z ==> ii * z + s = s + ii * w"))) THEN
    MATCH_MP_TAC CSQRT_UNIQUE THEN
    ASM_REWRITE_TAC [CSQRT] THEN CONV_TAC COMPLEX_RING)

  let CACS_CASN_SQRT_POS ← prove
   r"!z. (&0 < Re z \/ Re z = &0 /\ &0 <= Im z)
       ==> cacs(z) = casn(csqrt(Cx(&1) - z pow 2))"
   (GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [casn, cacs] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC (← ExceptT.mk (COMPLEX_RING (← q r"w = z ==> z + ii * s = ii * s + w"))) THEN
    MATCH_MP_TAC CSQRT_UNIQUE THEN
    ASM_REWRITE_TAC [CSQRT] THEN CONV_TAC COMPLEX_RING)

  let CSIN_CACS ← prove
   r"!z. &0 < Re z \/ Re(z) = &0 /\ &0 <= Im z
       ==> csin(cacs z) = csqrt(Cx(&1) - z pow 2)"
   (GEN_TAC THEN DISCH_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM CSIN_CASN] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC CACS_CASN_SQRT_POS THEN
    ASM_REWRITE_TAC [])

  let CCOS_CASN ← prove
   r"!z. &0 < Re z \/ Re(z) = &0 /\ &0 <= Im z
       ==> ccos(casn z) = csqrt(Cx(&1) - z pow 2)"
   (GEN_TAC THEN DISCH_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM CCOS_CACS] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC CASN_CACS_SQRT_POS THEN
    ASM_REWRITE_TAC [])

  let asn ← new_definition r"asn(x) = Re(casn(Cx x))"

  let REAL_ASN ← prove
   r"!z. real z /\ abs(Re z) <= &1 ==> real(casn z)"
   (GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN SPEC_TAC (← q r"Re z", ← q r"x:real") THEN
    REWRITE_TAC [real, casn, COMPLEX_MUL_LNEG, IM_NEG, IM_MUL_II] THEN
    GEN_TAC THEN REWRITE_TAC [RE_CX, REAL_NEG_EQ_0] THEN DISCH_TAC THEN
    MATCH_MP_TAC NORM_CEXP_IMAGINARY THEN
    SIMP_TAC [CEXP_CLOG, CASN_BODY_LEMMA, NORM_EQ_SQUARE] THEN
    REWRITE_TAC [DOT_SQUARE_NORM, COMPLEX_SQNORM] THEN
    REWRITE_TAC [RE_ADD, IM_ADD, RE_MUL_II, IM_MUL_II, RE_CX, IM_CX] THEN
    ASM_SIMP_TAC [← GSYM CX_POW, ← GSYM CX_SUB, ← GSYM CX_SQRT, REAL_SUB_LE,
                  ABS_SQUARE_LE_1, RE_CX, IM_CX, REAL_NEG_0, REAL_ADD_LID,
                  SQRT_POW_2] THEN
    REAL_ARITH_TAC)

  let CX_ASN ← prove
   r"!x. abs(x) <= &1 ==> Cx(asn x) = casn(Cx x)"
   (REWRITE_TAC [asn] THEN MESON_TAC [REAL, RE_CX, REAL_CX, REAL_ASN])

  let SIN_ASN ← prove
   r"!y. --(&1) <= y /\ y <= &1 ==> sin(asn(y)) = y"
   (REWRITE_TAC [← REAL_ARITH (← q r"--(&1) <= y /\ y <= &1 <=> abs(y) <= &1")] THEN
    ONCE_REWRITE_TAC [← GSYM CX_INJ] THEN SIMP_TAC [CX_ASN, CX_SIN, CSIN_CASN])

  let ASN_SIN ← prove
   r"!x. --(pi / &2) <= x /\ x <= pi / &2 ==> asn(sin(x)) = x"
   (ONCE_REWRITE_TAC [← GSYM CX_INJ] THEN SIMP_TAC [CX_ASN, SIN_BOUND, CX_SIN] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CASN_CSIN THEN
    REWRITE_TAC [IM_CX, RE_CX] THEN REPEAT (POP_ASSUM MP_TAC) THEN
    REAL_ARITH_TAC)

  let ASN_BOUNDS_LT ← prove
   r"!y. --(&1) < y /\ y < &1 ==> --(pi / &2) < asn(y) /\ asn(y) < pi / &2"
   (GEN_TAC THEN REWRITE_TAC [asn] THEN
    MP_TAC (← SPEC (← q r"Cx y") CASN_BOUNDS) THEN
    REWRITE_TAC [RE_CX] THEN REAL_ARITH_TAC)

  let ASN_0 ← prove
   r"asn(&0) = &0"
   (REWRITE_TAC [asn, CASN_0, RE_CX])

  let ASN_1 ← prove
   r"asn(&1) = pi / &2"
   (REWRITE_TAC [asn, CASN_1, RE_CX])

  let ASN_NEG_1 ← prove
   r"asn(-- &1) = --(pi / &2)"
   (REWRITE_TAC [asn, CX_NEG, CASN_NEG_1, RE_CX, RE_NEG])

  let ASN_BOUNDS ← prove
   r"!y. --(&1) <= y /\ y <= &1 ==> --(pi / &2) <= asn(y) /\ asn(y) <= pi / &2"
   (REWRITE_TAC [REAL_LE_LT] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY MP_TAC [ASN_1, ASN_NEG_1, ← SPEC (← q r"y:real") ASN_BOUNDS_LT] THEN
    ASM_REWRITE_TAC [] THEN REPEAT (POP_ASSUM MP_TAC) THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC)

  let ASN_BOUNDS_PI2 ← prove
   r"!x. &0 <= x /\ x <= &1 ==> &0 <= asn x /\ asn x <= pi / &2"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"&0", ← q r"asn x"] SIN_MONO_LE_EQ) THEN
    ASM_SIMP_TAC [SIN_0, SIN_ASN, ← REAL_ARITH (← q r"&0 <= x ==> --(&1) <= x")] THEN
    MP_TAC (← SPEC (← q r"x:real") ASN_BOUNDS) THEN MP_TAC PI_POS THEN
    ASM_REAL_ARITH_TAC)

  let ASN_NEG ← prove
   r"!x. -- &1 <= x /\ x <= &1 ==> asn(--x) = --asn(x)"
   (GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do pure (
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
       [← GSYM (← MATCH_MP SIN_ASN th)])) THEN
    REWRITE_TAC [← GSYM SIN_NEG] THEN MATCH_MP_TAC ASN_SIN THEN
    REWRITE_TAC [← REAL_ARITH (← q r"--a <= --x /\ --x <= a <=> --a <= x /\ x <= a")] THEN
    ASM_SIMP_TAC [ASN_BOUNDS])

  let COS_ASN_NZ ← prove
   r"!x. --(&1) < x /\ x < &1 ==> ~(cos(asn(x)) = &0)"
   (ONCE_REWRITE_TAC [← GSYM CX_INJ] THEN SIMP_TAC [CX_ASN, CX_COS,
      ← REAL_ARITH (← q r"--(&1) < x /\ x < &1 ==> abs(x) <= &1")] THEN
    GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CCOS_CASN_NZ THEN
    SIMP_TAC [← ExceptT.mk (COMPLEX_RING (← q r"x pow 2 = Cx(&1) <=> x = Cx(&1) \/ x = --Cx(&1)"))] THEN
    REWRITE_TAC [← GSYM CX_NEG, CX_INJ] THEN
    ASM_REAL_ARITH_TAC)

  let ASN_MONO_LT_EQ ← prove
   r"!x y. abs(x) <= &1 /\ abs(y) <= &1 ==> (asn(x) < asn(y) <=> x < y)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"sin(asn(x)) < sin(asn(y))") THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SIN_MONO_LT_EQ THEN
      ONCE_REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THEN MATCH_MP_TAC ASN_BOUNDS,
      BINOP_TAC THEN MATCH_MP_TAC SIN_ASN] THEN
    ASM_REAL_ARITH_TAC)

  let ASN_MONO_LE_EQ ← prove
   r"!x y. abs(x) <= &1 /\ abs(y) <= &1 ==> (asn(x) <= asn(y) <=> x <= y)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM REAL_NOT_LT] THEN
    ASM_SIMP_TAC [ASN_MONO_LT_EQ])

  let ASN_MONO_LT ← prove
   r"!x y. --(&1) <= x /\ x < y /\ y <= &1 ==> asn(x) < asn(y)"
   (MP_TAC ASN_MONO_LT_EQ THEN REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    REAL_ARITH_TAC)

  let ASN_MONO_LE ← prove
   r"!x y. --(&1) <= x /\ x <= y /\ y <= &1 ==> asn(x) <= asn(y)"
   (MP_TAC ASN_MONO_LE_EQ THEN REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    REAL_ARITH_TAC)

  let COS_ASN ← prove
   r"!x. --(&1) <= x /\ x <= &1 ==> cos(asn x) = sqrt(&1 - x pow 2)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← GSYM SQRT_UNIQUE) THEN
    ASM_SIMP_TAC [ASN_BOUNDS, COS_POS_PI_LE, REAL_EQ_SUB_RADD] THEN
    ASM_MESON_TAC [SIN_ASN, SIN_CIRCLE, REAL_ADD_SYM])

  pure { CCOS_CASN_NZ, CSIN_CACS_NZ, CCOS_CSIN_CSQRT, CSIN_CCOS_CSQRT,
         CASN_CACS_SQRT_POS, CACS_CASN_SQRT_POS, CSIN_CACS, CCOS_CASN, asn, REAL_ASN,
         CX_ASN, SIN_ASN, ASN_SIN, ASN_BOUNDS_LT, ASN_0, ASN_1, ASN_NEG_1, ASN_BOUNDS,
         ASN_BOUNDS_PI2, ASN_NEG, COS_ASN_NZ, ASN_MONO_LT_EQ, ASN_MONO_LE_EQ,
         ASN_MONO_LT, ASN_MONO_LE, COS_ASN }
/- ------------------------------------------------------------------------- -/
/- Real arccosine; some interrelationships among the real inverse trig      -/
/- functions; more delicate continuity results for arcsin and arccos.       -/
/- (transcendentals.ml 5411-5682)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSW where
  acs : thm
  REAL_ACS : thm
  CX_ACS : thm
  COS_ACS : thm
  ACS_COS : thm
  ACS_BOUNDS_LT : thm
  ACS_0 : thm
  ACS_1 : thm
  ACS_NEG_1 : thm
  ACS_BOUNDS : thm
  ACS_NEG : thm
  SIN_ACS_NZ : thm
  ACS_MONO_LT_EQ : thm
  ACS_MONO_LE_EQ : thm
  ACS_MONO_LT : thm
  ACS_MONO_LE : thm
  SIN_ACS : thm
  ACS_INJ : thm
  ACS_ATN : thm
  ASN_PLUS_ACS : thm
  ASN_ACS : thm
  ACS_ASN : thm
  ASN_ATN : thm
  ASN_ACS_SQRT_POS : thm
  ASN_ACS_SQRT_NEG : thm
  ACS_ASN_SQRT_POS : thm
  ACS_ASN_SQRT_NEG : thm
  CONTINUOUS_ON_CASN_REAL : thm
  CONTINUOUS_WITHIN_CASN_REAL : thm
  CONTINUOUS_ON_CACS_REAL : thm
  CONTINUOUS_WITHIN_CACS_REAL : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSW [HolBase] (D : TranscendentalsDeps) (BTSC : TSC) (BTSE : TSE) (BTSF : TSF) (BTSK : TSK) (BTSL : TSL) (BTSM : TSM) (BTSQ : TSQ) (BTSS : TSS) (BTST : TST) (BTSU : TSU) (BTSV : TSV) : ExceptT String IO TSW := do
  -- @@SCOPE BEGIN
  let { CONTINUOUS_ON_CCOS, CONTINUOUS_ON_CSIN, COS_BOUND, COS_NEG, CX_COS, CX_SIN,
        SIN_CIRCLE, SIN_SUB, .. } := BTSC
  let { COS_PERIODIC_PI, COS_PI2, PI_POS, SIN_COS, SIN_EQ_0_PI, SIN_PI2, SIN_POS_PI_LE,
        .. } := BTSE
  let { NORM_CEXP_IMAGINARY, .. } := BTSF
  let { REAL_SUB_TAN, tan, .. } := BTSK
  let { COS_MONO_LT_EQ, SIN_INJ_PI, TAN_COT, .. } := BTSL
  let { CEXP_CLOG, .. } := BTSM
  let { ATN_BOUND, ATN_TAN, COS_ATN_NZ, .. } := BTSQ
  let { CASN_CSIN, .. } := BTSS
  let { cacs, CACS_0, CACS_1, CACS_BODY_LEMMA, CACS_CCOS, CACS_NEG_1, CCOS_CACS,
        .. } := BTST
  let { CACS_BOUNDS, .. } := BTSU
  let { asn, ASN_BOUNDS, ASN_NEG, CACS_CASN_SQRT_POS, CASN_CACS_SQRT_POS, CSIN_CACS_NZ,
        SIN_ASN, .. } := BTSV
  let { CLOSED_HALFSPACE_RE_GE, CLOSED_HALFSPACE_RE_LE, CLOSED_REAL_SET, .. } := D.kna
  let { CONTINUOUS_WITHIN_CLOSED_NONTRIVIAL, .. } := D.qtopology
  let { DOT_SQUARE_NORM, .. } := D.qvectors
  let { REAL_POW_1_LE, .. } := D.qsession
  let { COMPLEX_SQNORM, .. } := D.cn.cxa
  let { COMPLEX_MUL_LNEG, COMPLEX_SUB_LZERO, .. } := D.cn.cxb
  let { CX_INJ, CX_NEG, CX_POW, CX_SUB, IM_ADD, IM_CX, IM_MUL_II, IM_NEG, RE_ADD, RE_CX,
        RE_MUL_II, RE_NEG, .. } := D.cn.cxc
  let { COMPLEX_RING, .. } := D.cn.cxd
  let { COMPLEX_NORM_LE_RE_IM, .. } := D.cn.cxg
  let { CX_SQRT, .. } := D.cn.cxh
  let { FORALL_REAL, REAL, real, REAL_CX, .. } := D.cn.cxi
  let { REAL_EQ_SUB_RADD, .. } := D.cn.qsession
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC, new_definition, REAL_ARITH,
        REAL_ARITH_TAC, REAL_FIELD, SET_RULE, .. } := D.cn.cx.cvx
  let { ARITH, CONJ_ASSOC, EQ_TRANS, .. } := D.cn.cx.cvx.core1
  let { IMP_CONJ, .. } := D.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, REAL_ADD_LID, .. } := D.cn.cx.cvx.core3
  let { REAL_EQ_SUB_LADD, REAL_INV_DIV, REAL_LE_ANTISYM, REAL_LE_LT, REAL_LT_IMP_LE,
        .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_LZERO, REAL_NEG_0, REAL_NEG_EQ_0, REAL_NEG_NEG, REAL_NOT_LT,
        REAL_SUB_0, REAL_SUB_LE, REAL_SUB_RZERO, SQRT_POW_2, SUBSET,
        .. } := D.cn.cx.cvx.core5
  let { real_ge, .. } := D.cn.cx.cvx.core6
  let { ABS_SQUARE_LE_1, .. } := D.cn.cx.cvx.misc
  let { NORM_EQ_SQUARE, .. } := D.cn.cx.cvx.vec2
  let { NORM_NEG, .. } := D.cn.cx.cvx.vec3
  let { dist, .. } := D.cn.cx.cvx.vec4
  let { BOUNDED_CBALL, BOUNDED_SUBSET, CLOSED_INTER, .. } := D.cn.cx.cvx.top1
  let { COMPACT_EQ_BOUNDED_CLOSED, .. } := D.cn.cx.cvx.top2
  let { CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN, CONTINUOUS_ON_INVERSE, CONTINUOUS_ON_SUBSET,
        .. } := D.cn.cx.cvx.top3
  let { IN_CBALL, .. } := D.cn.cx.cvx.top4
  let { REAL_POW_NEG, SQRT_UNIQUE, .. } := D.cn.ms.ig.dv.dg.qsession
  let { REAL_BOUNDS_LE, .. } := D.cn.ms.ig.dv.dg.pt.qses
  -- @@SCOPE END

  let acs ← new_definition r"acs(x) = Re(cacs(Cx x))"

  let REAL_ACS ← prove
   r"!z. real z /\ abs(Re z) <= &1 ==> real(cacs z)"
   (GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN SPEC_TAC (← q r"Re z", ← q r"x:real") THEN
    REWRITE_TAC [real, cacs, COMPLEX_MUL_LNEG, IM_NEG, IM_MUL_II] THEN
    GEN_TAC THEN REWRITE_TAC [RE_CX, REAL_NEG_EQ_0] THEN DISCH_TAC THEN
    MATCH_MP_TAC NORM_CEXP_IMAGINARY THEN
    SIMP_TAC [CEXP_CLOG, CACS_BODY_LEMMA, NORM_EQ_SQUARE] THEN
    REWRITE_TAC [DOT_SQUARE_NORM, COMPLEX_SQNORM] THEN
    REWRITE_TAC [RE_ADD, IM_ADD, RE_MUL_II, IM_MUL_II, RE_CX, IM_CX] THEN
    ASM_SIMP_TAC [← GSYM CX_POW, ← GSYM CX_SUB, ← GSYM CX_SQRT, REAL_SUB_LE,
                  ABS_SQUARE_LE_1, RE_CX, IM_CX, REAL_NEG_0, REAL_ADD_LID,
                  SQRT_POW_2] THEN
    REAL_ARITH_TAC)

  let CX_ACS ← prove
   r"!x. abs(x) <= &1 ==> Cx(acs x) = cacs(Cx x)"
   (REWRITE_TAC [acs] THEN MESON_TAC [REAL, RE_CX, REAL_CX, REAL_ACS])

  let COS_ACS ← prove
   r"!y. --(&1) <= y /\ y <= &1 ==> cos(acs(y)) = y"
   (REWRITE_TAC [← REAL_ARITH (← q r"--(&1) <= y /\ y <= &1 <=> abs(y) <= &1")] THEN
    ONCE_REWRITE_TAC [← GSYM CX_INJ] THEN SIMP_TAC [CX_ACS, CX_COS, CCOS_CACS])

  let ACS_COS ← prove
   r"!x. &0 <= x /\ x <= pi ==> acs(cos(x)) = x"
   (ONCE_REWRITE_TAC [← GSYM CX_INJ] THEN SIMP_TAC [CX_ACS, COS_BOUND, CX_COS] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CACS_CCOS THEN
    REWRITE_TAC [IM_CX, RE_CX] THEN ASM_REAL_ARITH_TAC)

  let ACS_BOUNDS_LT ← prove
   r"!y. --(&1) < y /\ y < &1 ==> &0 < acs(y) /\ acs(y) < pi"
   (GEN_TAC THEN REWRITE_TAC [acs] THEN
    MP_TAC (← SPEC (← q r"Cx y") CACS_BOUNDS) THEN
    REWRITE_TAC [RE_CX] THEN REAL_ARITH_TAC)

  let ACS_0 ← prove
   r"acs(&0) = pi / &2"
   (REWRITE_TAC [acs, CACS_0, RE_CX])

  let ACS_1 ← prove
   r"acs(&1) = &0"
   (REWRITE_TAC [acs, CACS_1, RE_CX])

  let ACS_NEG_1 ← prove
   r"acs(-- &1) = pi"
   (REWRITE_TAC [acs, CX_NEG, CACS_NEG_1, RE_CX, RE_NEG])

  let ACS_BOUNDS ← prove
   r"!y. --(&1) <= y /\ y <= &1 ==> &0 <= acs(y) /\ acs(y) <= pi"
   (REWRITE_TAC [REAL_LE_LT] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY MP_TAC [ACS_1, ACS_NEG_1, ← SPEC (← q r"y:real") ACS_BOUNDS_LT] THEN
    ASM_REWRITE_TAC [] THEN REPEAT (POP_ASSUM MP_TAC) THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC)

  let ACS_NEG ← prove
   r"!x. -- &1 <= x /\ x <= &1 ==> acs(--x) = pi - acs(x)"
   (GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do pure (
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
       [← GSYM (← MATCH_MP COS_ACS th)])) THEN
    ONCE_REWRITE_TAC [← GSYM COS_NEG] THEN REWRITE_TAC [← GSYM COS_PERIODIC_PI] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"--x + y:real = y - x")] THEN MATCH_MP_TAC ACS_COS THEN
    SIMP_TAC [← REAL_ARITH (← q r"&0 <= p - x /\ p - x <= p <=> &0 <= x /\ x <= p")] THEN
    ASM_SIMP_TAC [ACS_BOUNDS])

  let SIN_ACS_NZ ← prove
   r"!x. --(&1) < x /\ x < &1 ==> ~(sin(acs(x)) = &0)"
   (ONCE_REWRITE_TAC [← GSYM CX_INJ] THEN SIMP_TAC [CX_ACS, CX_SIN,
      ← REAL_ARITH (← q r"--(&1) < x /\ x < &1 ==> abs(x) <= &1")] THEN
    GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CSIN_CACS_NZ THEN
    SIMP_TAC [← ExceptT.mk (COMPLEX_RING (← q r"x pow 2 = Cx(&1) <=> x = Cx(&1) \/ x = --Cx(&1)"))] THEN
    REWRITE_TAC [← GSYM CX_NEG, CX_INJ] THEN
    ASM_REAL_ARITH_TAC)

  let ACS_MONO_LT_EQ ← prove
   r"!x y. abs(x) <= &1 /\ abs(y) <= &1 ==> (acs(x) < acs(y) <=> y < x)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"cos(acs(y)) < cos(acs(x))") THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC COS_MONO_LT_EQ THEN
      ONCE_REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THEN MATCH_MP_TAC ACS_BOUNDS,
      BINOP_TAC THEN MATCH_MP_TAC COS_ACS] THEN
    ASM_REAL_ARITH_TAC)

  let ACS_MONO_LE_EQ ← prove
   r"!x y. abs(x) <= &1 /\ abs(y) <= &1 ==> (acs(x) <= acs(y) <=> y <= x)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM REAL_NOT_LT] THEN
    ASM_SIMP_TAC [ACS_MONO_LT_EQ])

  let ACS_MONO_LT ← prove
   r"!x y. --(&1) <= x /\ x < y /\ y <= &1 ==> acs(y) < acs(x)"
   (REPEAT GEN_TAC THEN
    MP_TAC (← SPECL [← q r"y:real", ← q r"x:real"] ACS_MONO_LT_EQ) THEN
    REAL_ARITH_TAC)

  let ACS_MONO_LE ← prove
   r"!x y. --(&1) <= x /\ x <= y /\ y <= &1 ==> acs(y) <= acs(x)"
   (REPEAT GEN_TAC THEN
    MP_TAC (← SPECL [← q r"y:real", ← q r"x:real"] ACS_MONO_LE_EQ) THEN
    REAL_ARITH_TAC)

  let SIN_ACS ← prove
   r"!x. --(&1) <= x /\ x <= &1 ==> sin(acs x) = sqrt(&1 - x pow 2)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← GSYM SQRT_UNIQUE) THEN
    ASM_SIMP_TAC [ACS_BOUNDS, SIN_POS_PI_LE, REAL_EQ_SUB_RADD] THEN
    ASM_MESON_TAC [COS_ACS, SIN_CIRCLE])

  let ACS_INJ ← prove
   r"!x y. abs(x) <= &1 /\ abs(y) <= &1 ==> (acs x = acs y <=> x = y)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM REAL_LE_ANTISYM] THEN
    ASM_SIMP_TAC [ACS_MONO_LE_EQ] THEN REAL_ARITH_TAC)

  let ACS_ATN ← prove
   r"!x. -- &1 < x /\ x < &1 ==> acs(x) = pi / &2 - atn(x / sqrt(&1 - x pow 2))"
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"x:real = p - y <=> y - (p - x) = &0")] THEN
    MATCH_MP_TAC SIN_EQ_0_PI THEN
    ASM_SIMP_TAC [ATN_BOUND, ACS_BOUNDS, REAL_LT_IMP_LE, ← REAL_ARITH
     (← q r"abs(x) < pi / &2 /\ &0 <= y /\ y <= pi
      ==> --pi < x - (pi / &2 - y) /\ x - (pi / &2 - y) < pi")] THEN
    SUBGOAL_THEN (← q r"tan(atn(x / sqrt(&1 - x pow 2))) = tan(pi / &2 - acs x)")
    MP_TAC THENL
     [REWRITE_TAC [TAN_COT, ATN_TAN] THEN REWRITE_TAC [tan] THEN
      ASM_SIMP_TAC [SIN_ACS, COS_ACS, REAL_LT_IMP_LE, REAL_INV_DIV],
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_SUB_0] THEN
    ASM_SIMP_TAC [SIN_ACS_NZ, ← GSYM SIN_COS, COS_ATN_NZ, REAL_SUB_TAN, ← REAL_FIELD
     (← q r"~(y = &0) /\ ~(z = &0) ==> (x / (y * z) = &0 <=> x = &0)")])

  let ASN_PLUS_ACS ← prove
   r"!x. -- &1 <= x /\ x <= &1 ==> asn(x) + acs(x) = pi / &2"
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"x + y:real = p <=> x = p - y")] THEN
    MATCH_MP_TAC SIN_INJ_PI THEN
    ASM_SIMP_TAC [SIN_PI2, COS_PI2, SIN_SUB, REAL_MUL_LZERO, REAL_SUB_RZERO] THEN
    ASM_SIMP_TAC [SIN_ASN, COS_ACS, REAL_MUL_LID] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"--p <= p - x <=> x <= &2 * p"),
                 ← REAL_ARITH (← q r"p - x <= p <=> &0 <= x")] THEN
    ASM_SIMP_TAC [ASN_BOUNDS, ACS_BOUNDS, ← REAL_ARITH (← q r"&2 * x / &2 = x")])

  let ASN_ACS ← prove
   r"!x. -- &1 <= x /\ x <= &1 ==> asn(x) = pi / &2 - acs(x)"
   (SIMP_TAC [REAL_EQ_SUB_LADD, ASN_PLUS_ACS])

  let ACS_ASN ← prove
   r"!x. -- &1 <= x /\ x <= &1 ==> acs(x) = pi / &2 - asn(x)"
   (SIMP_TAC [ASN_ACS] THEN REAL_ARITH_TAC)

  let ASN_ATN ← prove
   r"!x. -- &1 < x /\ x < &1 ==> asn(x) = atn(x / sqrt(&1 - x pow 2))"
   (SIMP_TAC [ASN_ACS, REAL_LT_IMP_LE, ACS_ATN] THEN REAL_ARITH_TAC)

  let ASN_ACS_SQRT_POS ← prove
   r"!x. &0 <= x /\ x <= &1 ==> asn(x) = acs(sqrt(&1 - x pow 2))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [asn, acs] THEN
    ASM_SIMP_TAC [CX_SQRT, REAL_SUB_LE, REAL_POW_1_LE, CX_SUB, CX_POW] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC CASN_CACS_SQRT_POS THEN
    ASM_REWRITE_TAC [RE_CX, IM_CX] THEN ASM_REAL_ARITH_TAC)

  let ASN_ACS_SQRT_NEG ← prove
   r"!x. -- &1 <= x /\ x <= &0 ==> asn(x) = --acs(sqrt(&1 - x pow 2))"
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"x = --y <=> (--x:real) = y")] THEN
    ASM_SIMP_TAC [← GSYM ASN_NEG, ← REAL_ARITH (← q r"x <= &0 ==> x <= &1")] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"(x:real) pow 2 = (--x) pow 2")] THEN
    MATCH_MP_TAC ASN_ACS_SQRT_POS THEN ASM_REAL_ARITH_TAC)

  let ACS_ASN_SQRT_POS ← prove
   r"!x. &0 <= x /\ x <= &1 ==> acs(x) = asn(sqrt(&1 - x pow 2))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [asn, acs] THEN
    ASM_SIMP_TAC [CX_SQRT, REAL_SUB_LE, REAL_POW_1_LE, CX_SUB, CX_POW] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC CACS_CASN_SQRT_POS THEN
    ASM_REWRITE_TAC [RE_CX, IM_CX] THEN ASM_REAL_ARITH_TAC)

  let ACS_ASN_SQRT_NEG ← prove
   r"!x. -- &1 <= x /\ x <= &0 ==> acs(x) = pi - asn(sqrt(&1 - x pow 2))"
   (REPEAT STRIP_TAC THEN MP_TAC (← SPEC (← q r"--x:real") ACS_ASN_SQRT_POS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC, SIMP_TAC [REAL_POW_NEG, ARITH]] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM REAL_NEG_NEG] THEN
    MATCH_MP_TAC ACS_NEG THEN ASM_REAL_ARITH_TAC)

  let CONTINUOUS_ON_CASN_REAL ← prove
   r"casn continuous_on {w | real w /\ abs(Re w) <= &1}"
   (MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC (← q r"IMAGE csin {z | real z /\ abs(Re z) <= pi / &2}") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_INVERSE THEN
      REWRITE_TAC [CONTINUOUS_ON_CSIN] THEN CONJ_TAC THENL
       [REWRITE_TAC [COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
         [MATCH_MP_TAC BOUNDED_SUBSET THEN
          EXISTS_TAC (← q r"cball(Cx(&0),pi / &2)") THEN
          REWRITE_TAC [BOUNDED_CBALL, SUBSET, IN_ELIM_THM, IN_CBALL] THEN
          REWRITE_TAC [dist, COMPLEX_SUB_LZERO, NORM_NEG, real] THEN
          X_GEN_TAC (← q r"z:complex") THEN
          MP_TAC (← SPEC (← q r"z:complex") COMPLEX_NORM_LE_RE_IM) THEN REAL_ARITH_TAC,
          SIMP_TAC [← SET_RULE (← q r"{x | P x /\ Q x} = {x | P x} INTER {x | Q x}"),
                    ← GSYM REAL_BOUNDS_LE] THEN
          SIMP_TAC [CLOSED_INTER, CLOSED_REAL_SET, CLOSED_HALFSPACE_RE_LE,
                    ← REWRITE_RULE [real_ge] CLOSED_HALFSPACE_RE_GE]],
        SIMP_TAC [SUBSET, IMP_CONJ, FORALL_REAL, IN_ELIM_THM, RE_CX] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC CASN_CSIN THEN
        REWRITE_TAC [RE_CX, IM_CX] THEN ASM_REAL_ARITH_TAC],
      SIMP_TAC [SUBSET, IMP_CONJ, FORALL_REAL, IN_ELIM_THM, RE_CX, IN_IMAGE] THEN
      X_GEN_TAC (← q r"x:real") THEN DISCH_TAC THEN
      EXISTS_TAC (← q r"Cx(asn x)") THEN
      ASM_SIMP_TAC [RE_CX, ASN_BOUNDS, REAL_BOUNDS_LE, REAL_CX, SIN_ASN,
                    ← GSYM CX_SIN] THEN
      ASM_MESON_TAC [REAL_BOUNDS_LE, ASN_BOUNDS]])

  let CONTINUOUS_WITHIN_CASN_REAL ← prove
   r"!z. casn continuous (at z within {w | real w /\ abs(Re w) <= &1})"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"z IN {w | real w /\ abs(Re w) <= &1}") THENL
     [ASM_SIMP_TAC [← REWRITE_RULE [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]
        CONTINUOUS_ON_CASN_REAL],
      MATCH_MP_TAC CONTINUOUS_WITHIN_CLOSED_NONTRIVIAL THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [← GSYM REAL_BOUNDS_LE] THEN
      ASM_SIMP_TAC [← SET_RULE (← q r"{x | P x /\ Q x} = {x | P x} INTER {x | Q x}")] THEN
      SIMP_TAC [CLOSED_INTER, CLOSED_REAL_SET, CLOSED_HALFSPACE_RE_LE,
                ← REWRITE_RULE [real_ge] CLOSED_HALFSPACE_RE_GE]])

  let CONTINUOUS_ON_CACS_REAL ← prove
   r"cacs continuous_on {w | real w /\ abs(Re w) <= &1}"
   (MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC (← q r"IMAGE ccos {z | real z /\ &0 <= Re z /\ Re z <= pi}") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_INVERSE THEN
      REWRITE_TAC [CONTINUOUS_ON_CCOS] THEN CONJ_TAC THENL
       [REWRITE_TAC [COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
         [MATCH_MP_TAC BOUNDED_SUBSET THEN
          EXISTS_TAC (← q r"cball(Cx(&0),&2 * pi)") THEN
          REWRITE_TAC [BOUNDED_CBALL, SUBSET, IN_ELIM_THM, IN_CBALL] THEN
          REWRITE_TAC [dist, COMPLEX_SUB_LZERO, NORM_NEG, real] THEN
          X_GEN_TAC (← q r"z:complex") THEN
          MP_TAC (← SPEC (← q r"z:complex") COMPLEX_NORM_LE_RE_IM) THEN REAL_ARITH_TAC,
          SIMP_TAC [← SET_RULE (← q r"{x | P x /\ Q x} = {x | P x} INTER {x | Q x}")] THEN
          SIMP_TAC [CLOSED_INTER, CLOSED_REAL_SET, CLOSED_HALFSPACE_RE_LE,
                    ← REWRITE_RULE [real_ge] CLOSED_HALFSPACE_RE_GE]],
        SIMP_TAC [SUBSET, IMP_CONJ, FORALL_REAL, IN_ELIM_THM, RE_CX] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC CACS_CCOS THEN
        REWRITE_TAC [RE_CX, IM_CX] THEN ASM_REAL_ARITH_TAC],
      SIMP_TAC [SUBSET, IMP_CONJ, FORALL_REAL, IN_ELIM_THM, RE_CX, IN_IMAGE] THEN
      X_GEN_TAC (← q r"x:real") THEN DISCH_TAC THEN
      EXISTS_TAC (← q r"Cx(acs x)") THEN
      ASM_SIMP_TAC [RE_CX, ACS_BOUNDS, REAL_BOUNDS_LE, REAL_CX, COS_ACS,
                    ← GSYM CX_COS]])

  let CONTINUOUS_WITHIN_CACS_REAL ← prove
   r"!z. cacs continuous (at z within {w | real w /\ abs(Re w) <= &1})"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"z IN {w | real w /\ abs(Re w) <= &1}") THENL
     [ASM_SIMP_TAC [← REWRITE_RULE [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]
        CONTINUOUS_ON_CACS_REAL],
      MATCH_MP_TAC CONTINUOUS_WITHIN_CLOSED_NONTRIVIAL THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [← GSYM REAL_BOUNDS_LE] THEN
      ASM_SIMP_TAC [← SET_RULE (← q r"{x | P x /\ Q x} = {x | P x} INTER {x | Q x}")] THEN
      SIMP_TAC [CLOSED_INTER, CLOSED_REAL_SET, CLOSED_HALFSPACE_RE_LE,
                ← REWRITE_RULE [real_ge] CLOSED_HALFSPACE_RE_GE]])

  pure { acs, REAL_ACS, CX_ACS, COS_ACS, ACS_COS, ACS_BOUNDS_LT, ACS_0, ACS_1, ACS_NEG_1,
         ACS_BOUNDS, ACS_NEG, SIN_ACS_NZ, ACS_MONO_LT_EQ, ACS_MONO_LE_EQ, ACS_MONO_LT,
         ACS_MONO_LE, SIN_ACS, ACS_INJ, ACS_ATN, ASN_PLUS_ACS, ASN_ACS, ACS_ASN, ASN_ATN,
         ASN_ACS_SQRT_POS, ASN_ACS_SQRT_NEG, ACS_ASN_SQRT_POS, ACS_ASN_SQRT_NEG,
         CONTINUOUS_ON_CASN_REAL, CONTINUOUS_WITHIN_CASN_REAL, CONTINUOUS_ON_CACS_REAL,
         CONTINUOUS_WITHIN_CACS_REAL }
/- ------------------------------------------------------------------------- -/
/- Some limits, most involving sequences of transcendentals.                 -/
/- (transcendentals.ml 5683-6015)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSX where
  LIM_CX_OVER_CEXP : thm
  LIM_Z_TIMES_CLOG : thm
  LIM_LOG_OVER_Z : thm
  LIM_LOG_OVER_POWER : thm
  LIM_LOG_OVER_X : thm
  LIM_LOG_OVER_POWER_N : thm
  LIM_LOG_OVER_N : thm
  LIM_1_OVER_POWER : thm
  LIM_INV_Z_OFFSET : thm
  LIM_INV_Z : thm
  LIM_INV_X_OFFSET : thm
  LIM_INV_X : thm
  LIM_INV_N_OFFSET : thm
  LIM_1_OVER_N : thm
  LIM_INV_N : thm
  LIM_INV_Z_POW_OFFSET : thm
  LIM_INV_Z_POW : thm
  LIM_INV_X_POW_OFFSET : thm
  LIM_INV_X_POW : thm
  LIM_INV_N_POW_OFFSET : thm
  LIM_INV_N_POW : thm
  LIM_1_OVER_LOG : thm
  LIM_N_TIMES_POWN : thm
  LIM_N_OVER_POWN : thm
  LIM_POWN : thm
  LIM_CSIN_OVER_X : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSX [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) (BTSB : TSB) (BTSD : TSD) (BTSF : TSF) (BTSG : TSG) (BTSM : TSM) (BTSN : TSN) (BTSO : TSO) : ExceptT String IO TSX := do
  -- @@SCOPE BEGIN
  let { CONTINUOUS_AT_CEXP, .. } := BTSA
  let { CX_EXP, REAL_EXP_ADD, REAL_EXP_LE_X, REAL_EXP_MONO_LE, REAL_EXP_MONO_LT,
        REAL_EXP_N, REAL_EXP_NEG, REAL_EXP_POS_LE, REAL_EXP_POS_LT, .. } := BTSB
  let { EXP_LOG, LOG_EXP, LOG_INV, LOG_MONO_LT_REV, LOG_POS, LOG_POS_LT, .. } := BTSD
  let { NORM_CEXP, .. } := BTSF
  let { TAYLOR_CSIN, .. } := BTSG
  let { CLOG_WORKS, CX_LOG, RE_CLOG, .. } := BTSM
  let { CLOG_INV, .. } := BTSN
  let { CPOW_N, NORM_CPOW_REAL, .. } := BTSO
  let { LIM_COMPLEX_DIV, LIM_COMPLEX_POW, LIM_INFINITY_POSINFINITY_CX, LIM_NULL_COMPLEX,
        LIM_NULL_COMPLEX_ADD, LIM_NULL_COMPLEX_NORM, LIM_NULL_COMPLEX_RMUL_BOUNDED,
        LIM_NULL_COMPLEX_SUB, .. } := D.knb
  let { LIM_TAC, .. } := D.knd
  let { LIM_NULL_COMPARISON_COMPLEX, .. } := D.knm
  let { LIM_AT_INFINITY_COMPLEX_0, .. } := D.knp
  let { CONTINUOUS_AT_COMPOSE, EVENTUALLY_AT_POSINFINITY, LIM_CASES_FINITE_SEQUENTIALLY,
        LIM_POSINFINITY_SEQUENTIALLY, .. } := D.qtopology
  let { LT_NZ, REAL_ADD_RINV, .. } := D.qsession
  let { complex_div, complex_pow, .. } := D.cn.cxa
  let { COMPLEX_ADD_LDISTRIB, COMPLEX_ADD_LID, COMPLEX_ADD_RID, COMPLEX_MUL_LID,
        COMPLEX_MUL_RZERO, COMPLEX_SUB_0, COMPLEX_SUB_RZERO, .. } := D.cn.cxb
  let { COMPLEX_EXPAND, COMPLEX_NORM_CX, COMPLEX_NORM_II, COMPLEX_POW_1, COMPLEX_POW_ZERO,
        CX_DIV, CX_INJ, IM_ADD, IM_CX, RE_ADD, RE_CX, .. } := D.cn.cxc
  let { COMPLEX_RING, .. } := D.cn.cxd
  let { COMPLEX_FIELD, COMPLEX_INV_DIV, COMPLEX_INV_INV, COMPLEX_POW_INV, .. } := D.cn.cxe
  let { COMPLEX_DIV_1, COMPLEX_INV_EQ_0, COMPLEX_NORM_DIV, COMPLEX_NORM_INV,
        COMPLEX_NORM_MUL, COMPLEX_NORM_NUM, COMPLEX_NORM_NZ, COMPLEX_NORM_POW,
        .. } := D.cn.cxf
  let { COMPLEX_NORM_GE_RE_IM, .. } := D.cn.cxg
  let { REAL_CX, .. } := D.cn.cxi
  let { VSUM_SING_NUMSEG, .. } := D.cn.qvectors
  let { LIM_AT_ID, .. } := D.cn.ms.qtopology2
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_REAL_ARITH_TAC, MESON, MESON_TAC, NUM_REDUCE_CONV,
        REAL_ARITH, REAL_ARITH_TAC, .. } := D.cn.cx.cvx
  let { REAL_LE_LCANCEL_IMP, .. } := D.cn.cx.cpx
  let { REAL_ABS_BOUNDS, .. } := D.cn.ms.ig.qsession
  let { LIM_AT_POSINFINITY, .. } := D.cn.ms.ig.qtopology
  let { ARITH, COND_RAND, ETA_AX, FINITE_SING, .. } := D.cn.cx.cvx.core1
  let { IMP_CONJ, IMP_CONJ_ALT, .. } := D.cn.cx.cvx.core2
  let { LE_1, MONO_EXISTS, MONO_FORALL, REAL_ABS_DIV, REAL_ABS_NEG, REAL_ABS_NUM,
        REAL_ARCH_INV, REAL_ARCH_SIMPLE, .. } := D.cn.cx.cvx.core3
  let { REAL_EQ_IMP_LE, REAL_INV_1_LT, REAL_INV_LT_1, REAL_LE_DIV, REAL_LE_INV2,
        REAL_LE_LDIV_EQ, REAL_LE_MUL, REAL_LE_RMUL, REAL_LE_TRANS, REAL_LET_TRANS,
        REAL_LT_01, REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_INV_EQ,
        REAL_LT_LCANCEL_IMP, REAL_LT_LDIV_EQ, REAL_LT_MUL, REAL_LT_RDIV_EQ, REAL_MAX_LE,
        .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_RINV, REAL_MUL_SYM, REAL_NOT_LT,
        REAL_OF_NUM_ADD, REAL_OF_NUM_EQ, REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_POS,
        REAL_POW_INV, REAL_POW_LT, REAL_SUB_LE, .. } := D.cn.cx.cvx.core5
  let { o_DEF, real_abs, real_div, real_ge, .. } := D.cn.cx.cvx.core6
  let { REAL_HALF, .. } := D.cn.cx.cvx.misc
  let { NORM_POS_LE, REAL_ABS_NORM, .. } := D.cn.cx.cvx.vec3
  let { dist, .. } := D.cn.cx.cvx.vec4
  let { EVENTUALLY_SEQUENTIALLY, .. } := D.cn.cx.cvx.met
  let { EVENTUALLY_AT, .. } := D.cn.cx.cvx.top3
  let { LIM_CONST, LIM_SEQUENTIALLY, .. } := D.cn.cx.cvx.top4
  let { REAL_ABS_ABS, REAL_INV_INV, REAL_LT_MUL2, .. } := D.cn.ms.ig.dv.qsession
  let { CONTINUOUS_AT, LIM_AT, .. } := D.cn.ms.ig.dv.qtopology1
  let { LIM_TRANSFORM_EVENTUALLY, .. } := D.cn.ms.ig.dv.qtopology2
  let { REAL_LT_INV2, .. } := D.cn.ms.ig.dv.dg.qsession
  let { SING_GSPEC, .. } := D.cn.ms.ig.dv.dg.pt.qses
  -- @@SCOPE END

  let LIM_CX_OVER_CEXP ← prove
   r"((\x. Cx x / cexp(Cx x)) --> Cx(&0)) at_posinfinity"
   (ONCE_REWRITE_TAC [LIM_NULL_COMPLEX_NORM] THEN
    REWRITE_TAC [LIM_AT_POSINFINITY, real_ge] THEN
    X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
    EXISTS_TAC (← q r"max (&1) (&1 + &2 * log (&2 / e))") THEN
    X_GEN_TAC (← q r"x:real") THEN REWRITE_TAC [REAL_MAX_LE] THEN STRIP_TAC THEN
    REWRITE_TAC [dist, COMPLEX_SUB_RZERO, COMPLEX_NORM_CX, REAL_ABS_NORM] THEN
    ASM_SIMP_TAC [COMPLEX_NORM_DIV, NORM_CEXP, COMPLEX_NORM_CX, RE_CX] THEN
    SIMP_TAC [REAL_LT_LDIV_EQ, REAL_EXP_POS_LT] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    ASM_SIMP_TAC [← GSYM REAL_LT_LDIV_EQ] THEN GEN_REWRITE_TAC
     (RAND_CONV o RAND_CONV) [← REAL_ARITH (← q r"x = x / &2 + x / &2")] THEN
    REWRITE_TAC [REAL_EXP_ADD, ← REAL_ARITH
     (← q r"x / e < y * y <=> x / &2 * &2 / e < y * y")] THEN
    MATCH_MP_TAC REAL_LT_MUL2 THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC,
      MATCH_MP_TAC (← REAL_ARITH
       (← q r"&1 <= x /\ &1 + x / &2 <= y ==> abs x / &2 < y")) THEN
      ASM_REWRITE_TAC [REAL_EXP_LE_X],
      ASM_SIMP_TAC [REAL_LE_DIV, REAL_POS, REAL_LT_IMP_LE],
      MATCH_MP_TAC LOG_MONO_LT_REV THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH, LOG_EXP,
                    ← REAL_ARITH (← q r"&1 <= x ==> &0 < x"), REAL_EXP_POS_LT] THEN
      ASM_REAL_ARITH_TAC])

  let LIM_Z_TIMES_CLOG ← prove
   r"((\z. z * clog z) --> Cx(&0)) (at (Cx(&0)))"
   (ONCE_REWRITE_TAC [← SPEC (← q r"clog z") COMPLEX_EXPAND] THEN
    REWRITE_TAC [COMPLEX_ADD_LDISTRIB] THEN
    MATCH_MP_TAC LIM_NULL_COMPLEX_ADD THEN CONJ_TAC THENL
     [SIMP_TAC [RE_CLOG] THEN MP_TAC LIM_CX_OVER_CEXP THEN
      REWRITE_TAC [LIM_AT_POSINFINITY, LIM_AT, dist, COMPLEX_SUB_RZERO] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"e:real") THEN
      ASM_CASES_TAC (← q r"&0 < e") THEN ASM_REWRITE_TAC [real_ge] THEN
      REWRITE_TAC [COMPLEX_NORM_DIV, COMPLEX_NORM_CX, NORM_CEXP, RE_CX] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"b:real")) THEN
      REWRITE_TAC [COMPLEX_NORM_MUL, COMPLEX_NORM_CX] THEN
      EXISTS_TAC (← q r"inv(exp b)") THEN SIMP_TAC [REAL_LT_INV_EQ, REAL_EXP_POS_LT] THEN
      X_GEN_TAC (← q r"z:complex") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"log(inv(norm(z:complex)))")) THEN
      ASM_SIMP_TAC [LOG_INV, EXP_LOG, REAL_LT_INV_EQ] THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      REWRITE_TAC [real_div, REAL_INV_INV, REAL_ABS_NEG] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      GEN_REWRITE_TAC id [← GSYM REAL_EXP_MONO_LE] THEN
      ASM_SIMP_TAC [EXP_LOG, REAL_EXP_NEG] THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_INV_INV] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC,
      MATCH_MP_TAC LIM_NULL_COMPLEX_RMUL_BOUNDED THEN
      REWRITE_TAC [LIM_AT_ID] THEN EXISTS_TAC (← q r"pi") THEN
      REWRITE_TAC [COMPLEX_NORM_MUL, COMPLEX_NORM_II, COMPLEX_NORM_CX] THEN
      REWRITE_TAC [EVENTUALLY_AT, dist, COMPLEX_SUB_0, COMPLEX_NORM_NZ] THEN
      SIMP_TAC [CLOG_WORKS, REAL_MUL_LID, REAL_ABS_BOUNDS, REAL_LT_IMP_LE] THEN
      MESON_TAC [REAL_LT_01]])

  let LIM_LOG_OVER_Z ← prove
   r"((\z. clog z / z) --> Cx(&0)) at_infinity"
   (SIMP_TAC [LIM_AT_INFINITY_COMPLEX_0, o_DEF, complex_div, COMPLEX_INV_INV,
              CLOG_INV] THEN
    ONCE_REWRITE_TAC [← ExceptT.mk (COMPLEX_RING
     (← q r"clog(inv z) * z = z * (clog z + clog(inv z)) - z * clog z"))] THEN
    MATCH_MP_TAC LIM_NULL_COMPLEX_SUB THEN
    REWRITE_TAC [LIM_Z_TIMES_CLOG] THEN
    MATCH_MP_TAC LIM_NULL_COMPLEX_RMUL_BOUNDED THEN
    REWRITE_TAC [LIM_AT_ID] THEN EXISTS_TAC (← q r"&2 * pi") THEN
    REWRITE_TAC [EVENTUALLY_AT, dist, COMPLEX_SUB_RZERO, COMPLEX_NORM_NZ] THEN
    EXISTS_TAC (← q r"&1") THEN SIMP_TAC [REAL_LT_01] THEN
    X_GEN_TAC (← q r"z:complex") THEN STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [COMPLEX_EXPAND] THEN
    ASM_SIMP_TAC [RE_ADD, RE_CLOG, REAL_LT_INV_EQ, COMPLEX_INV_EQ_0,
                  COMPLEX_NORM_INV, LOG_INV, COMPLEX_NORM_NZ] THEN
    REWRITE_TAC [REAL_ADD_RINV, COMPLEX_ADD_LID, COMPLEX_NORM_MUL] THEN
    REWRITE_TAC [COMPLEX_NORM_II, COMPLEX_NORM_CX, IM_ADD] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"--pi < x /\ x <= pi /\ --pi < y /\ y <= pi
      ==> &1 * abs(x + y) <= &2 * pi")) THEN
    ASM_SIMP_TAC [CLOG_WORKS, COMPLEX_INV_EQ_0])

  let LIM_LOG_OVER_POWER ← prove
   r"!s. &0 < Re s
       ==> ((\x. clog(Cx x) / (Cx x) cpow s) --> Cx(&0)) at_posinfinity"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [LIM_AT_POSINFINITY] THEN
    X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN REWRITE_TAC [real_ge] THEN
    MP_TAC (← REWRITE_RULE [LIM_AT_POSINFINITY] LIM_CX_OVER_CEXP) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"Re s * e")) THEN
    ASM_SIMP_TAC [REAL_LT_MUL, real_ge, dist, COMPLEX_SUB_RZERO] THEN
    REWRITE_TAC [COMPLEX_NORM_DIV, COMPLEX_NORM_CX, NORM_CEXP, RE_CX] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"B:real")) THEN
    EXISTS_TAC (← q r"max (&1) (exp((abs B + &1) / Re s))") THEN X_GEN_TAC (← q r"x:real") THEN
    REWRITE_TAC [REAL_MAX_LE] THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"&0 < x") ASSUME_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    ASM_SIMP_TAC [NORM_CPOW_REAL, COMPLEX_NORM_DIV, REAL_CX, RE_CX,
                  ← GSYM CX_LOG, COMPLEX_NORM_CX, real_abs, LOG_POS] THEN
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC (← q r"Re s") THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"Re s * log x")) THEN
    ASM_SIMP_TAC [real_abs, REAL_LE_MUL, LOG_POS, REAL_LT_IMP_LE] THEN
    REWRITE_TAC [real_div, ← GSYM REAL_MUL_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"abs b + &1 <= x * y ==> b <= y * x")) THEN
    ASM_SIMP_TAC [← GSYM REAL_LE_LDIV_EQ] THEN
    ONCE_REWRITE_TAC [← GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC [EXP_LOG])

  let LIM_LOG_OVER_X ← prove
   r"((\x. clog(Cx x) / Cx x) --> Cx(&0)) at_posinfinity"
   (MP_TAC (← SPEC (← q r"Cx(&1)") LIM_LOG_OVER_POWER) THEN
    REWRITE_TAC [CPOW_N, RE_CX, REAL_LT_01, COMPLEX_POW_1] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
    REWRITE_TAC [EVENTUALLY_AT_POSINFINITY, CX_INJ] THEN
    EXISTS_TAC (← q r"&1") THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC)

  let LIM_LOG_OVER_POWER_N ← prove
   r"!s. &0 < Re s
       ==> ((\n. clog(Cx(&n)) / Cx(&n) cpow s) --> Cx(&0)) sequentially"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_POSINFINITY_SEQUENTIALLY THEN
    ASM_SIMP_TAC [LIM_LOG_OVER_POWER])

  let LIM_LOG_OVER_N ← prove
   r"((\n. clog(Cx(&n)) / Cx(&n)) --> Cx(&0)) sequentially"
   (MP_TAC (← SPEC (← q r"Cx(&1)") LIM_LOG_OVER_POWER_N) THEN
    SIMP_TAC [RE_CX, REAL_LT_01] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
    REWRITE_TAC [EVENTUALLY_SEQUENTIALLY, CPOW_N, CX_INJ] THEN EXISTS_TAC (← q r"1") THEN
    SIMP_TAC [COMPLEX_POW_1, REAL_OF_NUM_EQ, ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")])

  let LIM_1_OVER_POWER ← prove
   r"!s. &0 < Re s
       ==> ((\n. Cx(&1) / Cx(&n) cpow s) --> Cx(&0)) sequentially"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_NULL_COMPARISON_COMPLEX THEN
    EXISTS_TAC (← q r"\n. clog(Cx(&n)) / Cx(&n) cpow s") THEN
    ASM_SIMP_TAC [LIM_LOG_OVER_POWER_N] THEN
    REWRITE_TAC [EVENTUALLY_SEQUENTIALLY] THEN
    MP_TAC (← ISPEC (← q r"exp(&1)") REAL_ARCH_SIMPLE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"N:num") THEN
    ASM_CASES_TAC (← q r"N = 0") THENL
     [ASM_SIMP_TAC [← GSYM REAL_NOT_LT, REAL_EXP_POS_LT], ALL_TAC] THEN
    DISCH_TAC THEN X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN
    REWRITE_TAC [complex_div, COMPLEX_NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [NORM_POS_LE] THEN
    SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    ASM_SIMP_TAC [← GSYM CX_LOG, REAL_OF_NUM_LT, LT_NZ,
                  COMPLEX_NORM_CX, REAL_ABS_NUM] THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"x <= y ==> x <= abs y")) THEN
    ONCE_REWRITE_TAC [← GSYM REAL_EXP_MONO_LE] THEN
    ASM_SIMP_TAC [EXP_LOG, REAL_OF_NUM_LT, LT_NZ] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [← GSYM REAL_OF_NUM_LE]) THEN ASM_REAL_ARITH_TAC)

  let LIM_INV_Z_OFFSET ← prove
   r"!z. ((\w. inv(w + z)) --> Cx(&0)) at_infinity"
   (GEN_TAC THEN REWRITE_TAC [LIM_AT_INFINITY_COMPLEX_0, o_DEF] THEN
    SIMP_TAC [COMPLEX_INV_DIV, ← ExceptT.mk (COMPLEX_FIELD
     (← q r"~(w = Cx(&0)) ==> inv w + z = (Cx(&1) + w * z) / w"))] THEN
    GEN_REWRITE_TAC LAND_CONV
     [← ExceptT.mk (COMPLEX_FIELD (← q r"Cx(&0) = Cx(&0) / (Cx(&1) + Cx(&0) * z)"))] THEN
    MATCH_MP_TAC LIM_COMPLEX_DIV THEN
    REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"~(Cx(&1) + Cx(&0) * z = Cx(&0))"))] THEN
    CONJ_TAC THEN LIM_TAC)

  let LIM_INV_Z ← prove
   r"((\z. inv(z)) --> Cx(&0)) at_infinity"
   (ONCE_REWRITE_TAC [← MESON [COMPLEX_ADD_RID] (← q r"inv z = inv(z + Cx(&0))")] THEN
    REWRITE_TAC [LIM_INV_Z_OFFSET])

  let LIM_INV_X_OFFSET ← prove
   r"!z. ((\x. inv(Cx x + z)) --> Cx(&0)) at_posinfinity"
   (GEN_TAC THEN
    MATCH_MP_TAC (← REWRITE_RULE [o_DEF] LIM_INFINITY_POSINFINITY_CX) THEN
    REWRITE_TAC [LIM_INV_Z_OFFSET])

  let LIM_INV_X ← prove
   r"((\x. inv(Cx x)) --> Cx(&0)) at_posinfinity"
   (MATCH_MP_TAC (← REWRITE_RULE [o_DEF] LIM_INFINITY_POSINFINITY_CX) THEN
    REWRITE_TAC [← REWRITE_RULE [ETA_AX] LIM_INV_Z])

  let LIM_INV_N_OFFSET ← prove
   r"!z. ((\n. inv(Cx(&n) + z)) --> Cx(&0)) sequentially"
   (GEN_TAC THEN MATCH_MP_TAC LIM_POSINFINITY_SEQUENTIALLY THEN
    REWRITE_TAC [LIM_INV_X_OFFSET])

  let LIM_1_OVER_N ← prove
   r"((\n. Cx(&1) / Cx(&n)) --> Cx(&0)) sequentially"
   (MP_TAC (← SPEC (← q r"Cx(&1)") LIM_1_OVER_POWER) THEN SIMP_TAC [RE_CX, REAL_LT_01] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
    REWRITE_TAC [EVENTUALLY_SEQUENTIALLY, CPOW_N, CX_INJ] THEN EXISTS_TAC (← q r"1") THEN
    SIMP_TAC [COMPLEX_POW_1, REAL_OF_NUM_EQ, ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")])

  let LIM_INV_N ← prove
   r"((\n. inv(Cx(&n))) --> Cx(&0)) sequentially"
   (MP_TAC LIM_1_OVER_N THEN REWRITE_TAC [complex_div, COMPLEX_MUL_LID])

  let LIM_INV_Z_POW_OFFSET ← prove
   r"!z n. 1 <= n ==> ((\w. inv(w + z) pow n) --> Cx(&0)) at_infinity"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"Cx(&0) = Cx(&0) pow n") SUBST1_TAC THENL
     [ASM_SIMP_TAC [COMPLEX_POW_ZERO, LE_1],
      MATCH_MP_TAC LIM_COMPLEX_POW THEN REWRITE_TAC [LIM_INV_Z_OFFSET]])

  let LIM_INV_Z_POW ← prove
   r"!n. 1 <= n ==> ((\z. inv(z) pow n) --> Cx(&0)) at_infinity"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"Cx(&0) = Cx(&0) pow n") SUBST1_TAC THENL
     [ASM_SIMP_TAC [COMPLEX_POW_ZERO, LE_1],
      MATCH_MP_TAC LIM_COMPLEX_POW THEN
      REWRITE_TAC [← REWRITE_RULE [ETA_AX] LIM_INV_Z]])

  let LIM_INV_X_POW_OFFSET ← prove
   r"!z n. 1 <= n ==> ((\x. inv(Cx x + z) pow n) --> Cx(&0)) at_posinfinity"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← REWRITE_RULE [o_DEF] LIM_INFINITY_POSINFINITY_CX) THEN
    ASM_SIMP_TAC [LIM_INV_Z_POW_OFFSET])

  let LIM_INV_X_POW ← prove
   r"!n. 1 <= n ==> ((\x. inv(Cx x) pow n) --> Cx(&0)) at_posinfinity"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← REWRITE_RULE [o_DEF] LIM_INFINITY_POSINFINITY_CX) THEN
    ASM_SIMP_TAC [LIM_INV_Z_POW])

  let LIM_INV_N_POW_OFFSET ← prove
   r"!z m. 1 <= m ==> ((\n. inv(Cx(&n) + z) pow m) --> Cx(&0)) sequentially"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_POSINFINITY_SEQUENTIALLY THEN
    ASM_SIMP_TAC [LIM_INV_X_POW_OFFSET])

  let LIM_INV_N_POW ← prove
   r"!m. 1 <= m ==> ((\n. inv(Cx(&n)) pow m) --> Cx(&0)) sequentially"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_POSINFINITY_SEQUENTIALLY THEN
    ASM_SIMP_TAC [LIM_INV_X_POW])

  let LIM_1_OVER_LOG ← prove
   r"((\n. Cx(&1) / clog(Cx(&n))) --> Cx(&0)) sequentially"
   (REWRITE_TAC [LIM_SEQUENTIALLY] THEN X_GEN_TAC (← q r"e:real") THEN
    DISCH_TAC THEN X_CHOOSE_TAC (← q r"N:num") (← SPEC (← q r"exp(inv e)") REAL_ARCH_SIMPLE) THEN
    EXISTS_TAC (← q r"N + 1") THEN X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN
    REWRITE_TAC [dist, COMPLEX_SUB_RZERO, COMPLEX_MUL_LID, complex_div] THEN
    SUBGOAL_THEN (← q r"0 < n") ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    RULE_ASSUM_TAC (REWRITE_RULE
     [← GSYM REAL_OF_NUM_LT, ← GSYM REAL_OF_NUM_LE, ← GSYM REAL_OF_NUM_ADD]) THEN
    ASM_SIMP_TAC [← GSYM CX_LOG, COMPLEX_NORM_CX, COMPLEX_NORM_INV] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC [REAL_LT_INV_EQ] THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"a < x ==> a < abs x")) THEN
    ONCE_REWRITE_TAC [← GSYM REAL_EXP_MONO_LT] THEN
    ASM_SIMP_TAC [EXP_LOG] THEN ASM_REAL_ARITH_TAC)

  let LIM_N_TIMES_POWN ← prove
   r"!z. norm(z) < &1 ==> ((\n. Cx(&n) * z pow n) --> Cx(&0)) sequentially"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"z = Cx(&0)") THEN
    ASM_SIMP_TAC [COMPLEX_POW_ZERO, LIM_CASES_FINITE_SEQUENTIALLY, LIM_CONST,
                  COND_RAND, FINITE_SING, SING_GSPEC, COMPLEX_MUL_RZERO] THEN
    MP_TAC LIM_LOG_OVER_N THEN
    REWRITE_TAC [LIM_SEQUENTIALLY, dist, COMPLEX_SUB_RZERO] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"log(inv(norm(z:complex))) / &2")) THEN
    ASM_SIMP_TAC [LOG_POS_LT, REAL_INV_1_LT, COMPLEX_NORM_NZ, REAL_HALF] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"N1:num") (LABEL_TAC "+")) THEN
    X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q r"N2:num") STRIP_ASSUME_TAC o
                GEN_REWRITE_RULE id [REAL_ARCH_INV]) THEN
    EXISTS_TAC (← q r"MAX 1 (MAX N1 N2)") THEN
    REWRITE_TAC [← ARITH_RULE (← q r"MAX a b <= c <=> a <= c /\ b <= c")] THEN
    X_GEN_TAC (← q r"n:num") THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"n:num")) THEN
    ASM_SIMP_TAC [← GSYM CX_LOG, REAL_OF_NUM_LT, LE_1, ← GSYM CX_DIV,
                  COMPLEX_NORM_CX, REAL_ABS_DIV, REAL_ABS_NUM] THEN
    ASM_SIMP_TAC [REAL_LT_RDIV_EQ, REAL_OF_NUM_LT, ARITH, real_abs,
                  LOG_POS, REAL_OF_NUM_LE] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"a / b * &2 = (&2 * a) / b")] THEN
    ASM_SIMP_TAC [REAL_LT_LDIV_EQ, REAL_OF_NUM_LT, LE_1] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_EXP_MONO_LT] THEN
    ASM_SIMP_TAC [REAL_EXP_N, EXP_LOG, REAL_OF_NUM_LT, LE_1,
                  REAL_LT_INV_EQ, COMPLEX_NORM_NZ] THEN
    REWRITE_TAC [REAL_POW_INV] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM REAL_MUL_LID] THEN
    ASM_SIMP_TAC [← GSYM real_div, REAL_LT_RDIV_EQ, REAL_POW_LT, COMPLEX_NORM_NZ,
                  COMPLEX_NORM_MUL, COMPLEX_NORM_NUM, COMPLEX_NORM_POW] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q r"inv(&N2)") THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"inv(&n)") THEN
    ASM_SIMP_TAC [REAL_LE_INV2, REAL_OF_NUM_LE, REAL_OF_NUM_LT, LE_1] THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC (← q r"&n") THEN
    ASM_SIMP_TAC [REAL_MUL_RINV, REAL_LT_IMP_NZ, REAL_OF_NUM_LT, LE_1] THEN
    ASM_REAL_ARITH_TAC)

  let LIM_N_OVER_POWN ← prove
   r"!z. &1 < norm(z) ==> ((\n. Cx(&n) / z pow n) --> Cx(&0)) sequentially"
   (ASM_SIMP_TAC [complex_div, ← GSYM COMPLEX_POW_INV, COMPLEX_NORM_INV,
                  REAL_INV_LT_1, LIM_N_TIMES_POWN])

  let LIM_POWN ← prove
   r"!z. norm(z) < &1 ==> ((\n. z pow n) --> Cx(&0)) sequentially"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_NULL_COMPARISON_COMPLEX THEN
    EXISTS_TAC (← q r"\n. Cx(&n) * z pow n") THEN ASM_SIMP_TAC [LIM_N_TIMES_POWN] THEN
    REWRITE_TAC [EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC (← q r"1") THEN
    REWRITE_TAC [COMPLEX_NORM_MUL, COMPLEX_NORM_CX, REAL_ABS_NUM] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"a <= n * a <=> &0 <= (n - &1) * a")] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC [NORM_POS_LE, REAL_SUB_LE, REAL_OF_NUM_LE])

  let LIM_CSIN_OVER_X ← prove
   r"((\z. csin z / z) --> Cx(&1)) (at (Cx(&0)))"
   (ONCE_REWRITE_TAC [LIM_NULL_COMPLEX] THEN
    MATCH_MP_TAC LIM_NULL_COMPARISON_COMPLEX THEN
    EXISTS_TAC (← q r"\z. cexp(Cx(abs(Im z))) * z pow 2 / Cx(&2)") THEN
    REWRITE_TAC [EVENTUALLY_AT] THEN CONJ_TAC THENL
     [EXISTS_TAC (← q r"&1") THEN REWRITE_TAC [REAL_LT_01, dist, COMPLEX_SUB_RZERO] THEN
      X_GEN_TAC (← q r"z:complex") THEN SIMP_TAC [COMPLEX_NORM_NZ] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC (← q r"norm(z:complex)") THEN
      ASM_REWRITE_TAC [COMPLEX_NORM_NZ, ← GSYM COMPLEX_NORM_MUL] THEN
      ASM_SIMP_TAC [← ExceptT.mk (COMPLEX_FIELD
       (← q r"~(z = Cx(&0)) ==> z * (s / z - Cx(&1)) = s - z"))] THEN
      REWRITE_TAC [← GSYM CX_EXP, COMPLEX_NORM_MUL, COMPLEX_NORM_CX] THEN
      REWRITE_TAC [real_abs, REAL_EXP_POS_LE] THEN REWRITE_TAC [← GSYM real_abs] THEN
      MP_TAC (← ISPECL [← q r"0", ← q r"z:complex"] TAYLOR_CSIN) THEN
      REWRITE_TAC [VSUM_SING_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC [complex_pow, COMPLEX_POW_1, COMPLEX_DIV_1] THEN
      REWRITE_TAC [COMPLEX_MUL_LID] THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      REWRITE_TAC [COMPLEX_NORM_DIV, COMPLEX_NORM_CX, REAL_ABS_NUM] THEN
      REWRITE_TAC [COMPLEX_NORM_POW] THEN REAL_ARITH_TAC,
      LIM_TAC THEN TRY (CONV_TAC COMPLEX_RING) THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
      REWRITE_TAC [CONTINUOUS_AT_CEXP] THEN
      REWRITE_TAC [CONTINUOUS_AT, LIM_AT, dist, COMPLEX_SUB_RZERO,
                   IM_CX, REAL_ABS_NUM, COMPLEX_NORM_CX, REAL_ABS_ABS] THEN
      MESON_TAC [REAL_LET_TRANS, COMPLEX_NORM_GE_RE_IM]])

  pure { LIM_CX_OVER_CEXP, LIM_Z_TIMES_CLOG, LIM_LOG_OVER_Z, LIM_LOG_OVER_POWER,
         LIM_LOG_OVER_X, LIM_LOG_OVER_POWER_N, LIM_LOG_OVER_N, LIM_1_OVER_POWER,
         LIM_INV_Z_OFFSET, LIM_INV_Z, LIM_INV_X_OFFSET, LIM_INV_X, LIM_INV_N_OFFSET,
         LIM_1_OVER_N, LIM_INV_N, LIM_INV_Z_POW_OFFSET, LIM_INV_Z_POW,
         LIM_INV_X_POW_OFFSET, LIM_INV_X_POW, LIM_INV_N_POW_OFFSET, LIM_INV_N_POW,
         LIM_1_OVER_LOG, LIM_N_TIMES_POWN, LIM_N_OVER_POWN, LIM_POWN, LIM_CSIN_OVER_X }
/- ------------------------------------------------------------------------- -/
/- Roots of unity.                                                           -/
/- (transcendentals.ml 6016-6141)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSY where
  COMPLEX_ROOT_POLYFUN : thm
  COMPLEX_ROOT_UNITY : thm
  COMPLEX_ROOT_UNITY_EQ : thm
  COMPLEX_ROOT_UNITY_EQ_1 : thm
  FINITE_CARD_COMPLEX_ROOTS_UNITY : thm
  FINITE_COMPLEX_ROOTS_UNITY : thm
  FINITE_CARD_COMPLEX_ROOTS_UNITY_EXPLICIT : thm
  COMPLEX_ROOTS_UNITY : thm
  CARD_COMPLEX_ROOTS_UNITY : thm
  HAS_SIZE_COMPLEX_ROOTS_UNITY : thm
  COMPLEX_NOT_ROOT_UNITY : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSY [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) (BTSB : TSB) (BTSC : TSC) (BTSE : TSE) (BTSF : TSF) : ExceptT String IO TSY := do
  -- @@SCOPE BEGIN
  let { CEXP_N, .. } := BTSA
  let { CEXP_EULER, REAL_EXP_0, .. } := BTSB
  let { CX_COS, CX_SIN, .. } := BTSC
  let { COS_NPI, COS_PI, PI_NZ, SIN_NPI, SIN_PI, .. } := BTSE
  let { CEXP_EQ, NORM_CEXP, .. } := BTSF
  let { VSUM_CLAUSES_RIGHT, .. } := D.qvectors
  let { ARITH_EVEN, HAS_SIZE_NUMSEG_LT, INT_ABS_MUL, INT_ABS_NUM, int_abstr, int_congruent,
        INT_ENTIRE, INT_LT_LMUL_EQ, int_mul_th, int_rep, INT_SUB_0, int_sub_th,
        num_congruent, .. } := D.qsession
  let { complex_div, complex_pow, SIMPLE_COMPLEX_ARITH_TAC, .. } := D.cn.cxa
  let { COMPLEX_ADD_RID, COMPLEX_MUL_LZERO, COMPLEX_MUL_RID, COMPLEX_MUL_RZERO,
        .. } := D.cn.cxb
  let { COMPLEX_ENTIRE, COMPLEX_POW_ONE, COMPLEX_VEC_0, CX_DIV, CX_INJ, CX_MUL, CX_SUB,
        II_NZ, IM_CX, RE_CX, RE_II, RE_MUL_CX, .. } := D.cn.cxc
  let { COMPLEX_RING, .. } := D.cn.cxd
  let { COMPLEX_FIELD, .. } := D.cn.cxe
  let { COMPLEX_POLYFUN_ROOTBOUND, .. } := D.cn.cxj
  let { ARITH_RULE, ASM_ARITH_TAC, INT_ARITH, INT_ARITH_TAC, MESON_TAC, REAL_FIELD,
        .. } := D.cn.cx.cvx
  let { ADD_CLAUSES, LE_0, VSUM_CLAUSES_LEFT, .. } := D.cn.cx.cpx
  let { ARITH, CARD_SUBSET_LE, .. } := D.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, HAS_SIZE, HAS_SIZE_IMAGE_INJ, INT_OF_NUM_ADD, INT_OF_NUM_EQ,
        INT_OF_NUM_LT, .. } := D.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_NUMSEG, LE_1, LE_REFL, REAL_DIV_REFL, .. } := D.cn.cx.cvx.core3
  let { REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_OF_NUM_EQ, REAL_POW_ONE, SIMPLE_IMAGE_GEN,
        SUBSET, .. } := D.cn.cx.cvx.core5
  let { VECTOR_ADD_RID, VSUM_0, .. } := D.cn.cx.cvx.vec4
  let { int_eq, int_of_num_th, REAL_POW_NEG, .. } := D.cn.ms.ig.dv.dg.qsession
  let { NUMBER_RULE, .. } := D
  -- @@SCOPE END

  let COMPLEX_ROOT_POLYFUN ← prove
   r"!n z a.
        1 <= n
        ==> (z pow n = a <=>
             vsum(0..n) (\i. (if i = 0 then --a else if i = n then Cx(&1)
                              else Cx(&0)) * z pow i) = Cx(&0))"
   (ASM_SIMP_TAC [VSUM_CLAUSES_RIGHT, LE_1, LE_0] THEN
    SIMP_TAC [VSUM_CLAUSES_LEFT, LE_0, ADD_CLAUSES] THEN
    ASM_SIMP_TAC [LE_1, ← ARITH_RULE (← q r"1 <= n /\ 1 <= i /\ i <= n - 1
                             ==> ~(i = n)")] THEN
    REWRITE_TAC [COMPLEX_MUL_LZERO, complex_pow, COMPLEX_MUL_RID] THEN
    REWRITE_TAC [← GSYM COMPLEX_VEC_0, VSUM_0, VECTOR_ADD_RID] THEN
    REWRITE_TAC [COMPLEX_VEC_0] THEN CONV_TAC COMPLEX_RING)

  let COMPLEX_ROOT_UNITY ← prove
   r"!n j. ~(n = 0)
         ==> cexp(Cx(&2) * Cx pi * ii * Cx(&j / &n)) pow n = Cx(&1)"
   (REWRITE_TAC [← GSYM CEXP_N, CX_DIV] THEN
    ASM_SIMP_TAC [CX_INJ, complex_div, REAL_OF_NUM_EQ, ← ExceptT.mk (COMPLEX_FIELD
      (← q r"~(n = Cx(&0)) ==> n * t * p * ii * j * inv(n) = j * (ii * t * p)"))] THEN
    REWRITE_TAC [CEXP_N, ← GSYM CX_MUL] THEN
    REWRITE_TAC [CEXP_EULER, ← GSYM CX_MUL, ← GSYM CX_SIN, ← GSYM CX_COS] THEN
    REWRITE_TAC [COS_NPI, SIN_NPI, REAL_POW_NEG, COMPLEX_MUL_RZERO,
                 REAL_POW_ONE, ARITH_EVEN, COMPLEX_ADD_RID, COMPLEX_POW_ONE])

  let COMPLEX_ROOT_UNITY_EQ ← prove
   r"!n j k. ~(n = 0)
           ==> (cexp(Cx(&2) * Cx pi * ii * Cx(&j / &n)) =
                cexp(Cx(&2) * Cx pi * ii * Cx(&k / &n)) <=> (j == k) (mod n))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [CEXP_EQ, num_congruent, CX_MUL] THEN
    REWRITE_TAC [← ExceptT.mk (COMPLEX_RING
     (← q r"t * p * ii * j = t * p * ii * k + (t * n * p) * ii <=>
          (t * p * ii = Cx(&0)) \/ j - k = n"))] THEN
    SIMP_TAC [COMPLEX_ENTIRE, II_NZ, CX_INJ, PI_NZ, REAL_OF_NUM_EQ, ARITH] THEN
    REWRITE_TAC [← GSYM CX_SUB, CX_INJ] THEN
    ASM_SIMP_TAC [REAL_OF_NUM_EQ, ← REAL_FIELD
     (← q r"~(n = &0) ==> (j / n - k / n = m <=> j - k = n * m)")] THEN
    REWRITE_TAC [int_congruent] THEN
    REWRITE_TAC [int_eq, int_sub_th, int_mul_th, int_of_num_th] THEN
    MESON_TAC [int_abstr, int_rep])

  let COMPLEX_ROOT_UNITY_EQ_1 ← prove
   r"!n j. ~(n = 0)
         ==> (cexp(Cx(&2) * Cx pi * ii * Cx(&j / &n)) = Cx(&1) <=>
              n divides j)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"Cx(&1) = cexp(Cx(&2) * Cx pi * ii * Cx(&n / &n))")
    SUBST1_TAC THENL
     [ASM_SIMP_TAC [REAL_DIV_REFL, REAL_OF_NUM_EQ, COMPLEX_MUL_RID] THEN
      ONCE_REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"t * p * ii = ii * t * p"))] THEN
      REWRITE_TAC [CEXP_EULER, ← GSYM CX_MUL, ← GSYM CX_SIN, ← GSYM CX_COS] THEN
      REWRITE_TAC [COS_NPI, SIN_NPI] THEN SIMPLE_COMPLEX_ARITH_TAC,
      ASM_SIMP_TAC [COMPLEX_ROOT_UNITY_EQ] THEN CONV_TAC (fun t => NUMBER_RULE t)])

  let FINITE_CARD_COMPLEX_ROOTS_UNITY ← prove
   r"!n. 1 <= n
       ==> FINITE {z | z pow n = Cx(&1)} /\ CARD {z | z pow n = Cx(&1)} <= n"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC [COMPLEX_ROOT_POLYFUN] THEN
    MATCH_MP_TAC COMPLEX_POLYFUN_ROOTBOUND THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"n:num")) THEN
    ASM_SIMP_TAC [IN_NUMSEG, LE_1, LE_0, LE_REFL] THEN CONV_TAC COMPLEX_RING)

  let FINITE_COMPLEX_ROOTS_UNITY ← prove
   r"!n. ~(n = 0) ==> FINITE {z | z pow n = Cx(&1)}"
   (SIMP_TAC [FINITE_CARD_COMPLEX_ROOTS_UNITY, LE_1])

  let FINITE_CARD_COMPLEX_ROOTS_UNITY_EXPLICIT ← (do
    let lemma ← prove
     r"!x y n:num. (x == y) (mod n) /\ x < y + n /\ y < x + n ==> x = y"
     (REWRITE_TAC [num_congruent, ← GSYM INT_OF_NUM_EQ, ← GSYM INT_OF_NUM_LT] THEN
      REWRITE_TAC [← GSYM INT_OF_NUM_ADD] THEN
      REWRITE_TAC [← INT_ARITH (← q r"x < y + n /\ y < x + n <=> abs(x - y:int) < n")] THEN
      REPEAT GEN_TAC THEN REWRITE_TAC [int_congruent] THEN
      DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"d:int")) MP_TAC) THEN
      ONCE_REWRITE_TAC [← GSYM INT_SUB_0] THEN
      ASM_SIMP_TAC [INT_ABS_MUL, INT_ENTIRE, INT_ABS_NUM,
                    ← INT_ARITH (← q r"n * x:int < n <=> n * x < n * &1")] THEN
      DISJ_CASES_TAC (← INT_ARITH (← q r"&n:int = &0 \/ &0:int < &n")) THEN
      ASM_SIMP_TAC [INT_LT_LMUL_EQ] THEN INT_ARITH_TAC)
    prove
     r"!n. 1 <= n
       ==> FINITE {cexp(Cx(&2) * Cx pi * ii * Cx(&j / &n)) | j | j < n} /\
           CARD {cexp(Cx(&2) * Cx pi * ii * Cx(&j / &n)) | j | j < n} = n"
     (REWRITE_TAC [← GSYM HAS_SIZE] THEN
      REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN REWRITE_TAC [IN_ELIM_THM] THEN
      ASM_SIMP_TAC [HAS_SIZE_NUMSEG_LT, COMPLEX_ROOT_UNITY_EQ, LE_1] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN EXISTS_TAC (← q r"n:num") THEN
      ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC))

  let COMPLEX_ROOTS_UNITY ← prove
   r"!n. 1 <= n
       ==> {z | z pow n = Cx(&1)} =
           {cexp(Cx(&2) * Cx pi * ii * Cx(&j / &n)) | j | j < n}"
   (REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_LE THEN
    ASM_SIMP_TAC [FINITE_CARD_COMPLEX_ROOTS_UNITY,
                  FINITE_CARD_COMPLEX_ROOTS_UNITY_EXPLICIT] THEN
    GEN_REWRITE_TAC LAND_CONV [SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
    ASM_SIMP_TAC [COMPLEX_ROOT_UNITY, LE_1])

  let CARD_COMPLEX_ROOTS_UNITY ← prove
   r"!n. 1 <= n ==> CARD {z | z pow n = Cx(&1)} = n"
   (SIMP_TAC [COMPLEX_ROOTS_UNITY, FINITE_CARD_COMPLEX_ROOTS_UNITY_EXPLICIT])

  let HAS_SIZE_COMPLEX_ROOTS_UNITY ← prove
   r"!n. 1 <= n ==> {z | z pow n = Cx(&1)} HAS_SIZE n"
   (SIMP_TAC [HAS_SIZE, CARD_COMPLEX_ROOTS_UNITY, FINITE_COMPLEX_ROOTS_UNITY,
              LE_1])

  let COMPLEX_NOT_ROOT_UNITY ← prove
   r"!n. 1 <= n ==> ?u. norm u = &1 /\ ~(u pow n = Cx(&1))"
   (GEN_TAC THEN DISCH_TAC THEN
    ABBREV_TAC (← q r"u = cexp (Cx pi * ii * Cx (&1 / &n))") THEN
    EXISTS_TAC (← q r"u : complex") THEN CONJ_TAC THEN EXPAND_TAC "u" THEN
    REWRITE_TAC [NORM_CEXP, RE_MUL_CX, RE_II, REAL_MUL_LZERO,
                 REAL_MUL_RZERO, REAL_EXP_0] THEN
    EXPAND_TAC "u" THEN REWRITE_TAC [← GSYM CEXP_N] THEN
    ASM_SIMP_TAC [CX_DIV, LE_1, CX_INJ, REAL_OF_NUM_EQ, ← ExceptT.mk (COMPLEX_FIELD
         (← q r"~(n = Cx(&0)) ==> n * p * i * Cx(&1) / n = i * p"))] THEN
    REWRITE_TAC [CEXP_EULER, RE_CX, IM_CX, ← GSYM CX_COS, ← GSYM CX_SIN] THEN
    REWRITE_TAC [COS_PI, SIN_PI] THEN CONV_TAC COMPLEX_RING)

  pure { COMPLEX_ROOT_POLYFUN, COMPLEX_ROOT_UNITY, COMPLEX_ROOT_UNITY_EQ,
         COMPLEX_ROOT_UNITY_EQ_1, FINITE_CARD_COMPLEX_ROOTS_UNITY,
         FINITE_COMPLEX_ROOTS_UNITY, FINITE_CARD_COMPLEX_ROOTS_UNITY_EXPLICIT,
         COMPLEX_ROOTS_UNITY, CARD_COMPLEX_ROOTS_UNITY, HAS_SIZE_COMPLEX_ROOTS_UNITY,
         COMPLEX_NOT_ROOT_UNITY }
/- ------------------------------------------------------------------------- -/
/- Relation between clog and Arg, and hence continuity of Arg; relation     -/
/- between Arg and arctangent in upper halfplane.                           -/
/- (transcendentals.ml 6142-6372)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSZ where
  ARG_CLOG : thm
  CONTINUOUS_AT_ARG : thm
  CONTINUOUS_ON_ARG : thm
  CONTINUOUS_WITHIN_UPPERHALF_ARG : thm
  CONTINUOUS_ON_UPPERHALF_ARG : thm
  CONTINUOUS_ON_COMPOSE_ARG : thm
  OPEN_ARG_LTT : thm
  OPEN_ARG_GT : thm
  CLOSED_ARG_LE : thm
  ARG_ATAN_UPPERHALF : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSZ [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) (BTSB : TSB) (BTSC : TSC) (BTSE : TSE) (BTSH : TSH) (BTSI : TSI) (BTSM : TSM) (BTSO : TSO) (BTSQ : TSQ) : ExceptT String IO TSZ := do
  -- @@SCOPE BEGIN
  let { CEXP_ADD, CEXP_NEG, .. } := BTSA
  let { CEXP_EULER, .. } := BTSB
  let { COS_SUB, CX_COS, CX_SIN, SIN_SUB, .. } := BTSC
  let { COS_PI, COS_PI2, PI_POS, SIN_PI, SIN_PI2, .. } := BTSE
  let { ARG, ARG_CNJ, Arg_DEF, ARG_EQ_0, ARG_EQ_0_PI, ARG_LE_PI, ARG_LT_NZ, ARG_UNIQUE,
        .. } := BTSH
  let { ARG_ROTATE2D, NORM_ROTATE2D, ROTATE2D_PI2, ROTATE2D_SUB, .. } := BTSI
  let { CLOG_CEXP, CLOG_WORKS, CONTINUOUS_AT_CLOG, CX_LOG, .. } := BTSM
  let { CLOG_MUL_SIMPLE, .. } := BTSO
  let { ATN_BOUNDS, COS_ATN, SIN_ATN, .. } := BTSQ
  let { CLOSED_HALFSPACE_IM_GE, CLOSED_HALFSPACE_IM_LE, CLOSED_HALFSPACE_RE_GE,
        CLOSED_REAL, OPEN_HALFSPACE_RE_GT, OPEN_HALFSPACE_RE_LT, .. } := D.kna
  let { CONTINUOUS_AT_CX_IM, CONTINUOUS_ON_CX_LIFT, .. } := D.knd
  let { CONTINUOUS_ON_CNJ, .. } := D.knm
  let { CONTINUOUS_AT_COMPOSE, .. } := D.qtopology
  let { complex_div, COMPLEX_EQ, COMPLEX_SQNORM, SIMPLE_COMPLEX_ARITH, .. } := D.cn.cxa
  let { COMPLEX_ADD_RID, COMPLEX_MUL_RZERO, COMPLEX_NEG_EQ_0, .. } := D.cn.cxb
  let { COMPLEX_NORM_CX, CX_INJ, CX_INV, CX_NEG, CX_SUB, IM_ADD, IM_CX, IM_MUL_CX,
        IM_MUL_II, IM_NEG, RE_ADD, RE_CX, RE_MUL_CX, RE_MUL_II, RE_NEG, .. } := D.cn.cxc
  let { COMPLEX_FIELD, .. } := D.cn.cxe
  let { COMPLEX_NORM_NZ, COMPLEX_NORM_ZERO, .. } := D.cn.cxf
  let { CNJ_EQ_0, IM_CNJ, .. } := D.cn.cxg
  let { real, .. } := D.cn.cxi
  let { REAL_SUB_SUB2, .. } := D.cn.ms.qsession
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD,
        REAL_RING, SET_RULE, SET_TAC, .. } := D.cn.cx.cvx
  let { CONTINUOUS_NEG, .. } := D.cn.ms.ig.qtopology
  let { CONJ_ASSOC, DIFF, EQ_IMP, ETA_AX, EXTENSION, .. } := D.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, FUN_EQ_THM, IMP_CONJ, IMP_CONJ_ALT, IN_DIFF,
        .. } := D.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INTER, IN_SING, IN_UNIV, MONO_EXISTS, MONO_FORALL, REAL_ABS_NUM,
        REAL_ADD_LID, REAL_ADD_RID, .. } := D.cn.cx.cvx.core3
  let { REAL_INV_EQ_0, REAL_LE_ANTISYM, REAL_LE_DIV, REAL_LE_LT, REAL_LE_REFL,
        REAL_LE_TOTAL, REAL_LT_ADDR, REAL_LT_IMP_LE, REAL_LT_INV_EQ, REAL_LT_LE,
        REAL_LT_REFL, .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_LZERO, REAL_NEG_GE0, REAL_NOT_LE, REAL_POW_DIV,
        REAL_SUB_REFL, REAL_SUB_RZERO, SUBSET, .. } := D.cn.cx.cvx.core5
  let { o_ASSOC, o_DEF, o_THM, real_div, real_ge, .. } := D.cn.cx.cvx.core6
  let { DROP_VEC, LIFT_DROP, LIFT_SUB, .. } := D.cn.cx.cvx.vec2
  let { NORM_POS_LE, .. } := D.cn.cx.cvx.vec3
  let { dist, .. } := D.cn.cx.cvx.vec4
  let { CLOSED_IN_CLOSED_INTER, CLOSED_INTER, .. } := D.cn.cx.cvx.top1
  let { CONTINUOUS_ADD, CONTINUOUS_AT_ID, CONTINUOUS_AT_IMP_CONTINUOUS_ON,
        .. } := D.cn.cx.cvx.top2
  let { CONTINUOUS_CONST, CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_CONST, CONTINUOUS_ON_EQ,
        CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN, CONTINUOUS_ON_SUB, CONTINUOUS_ON_SUBSET,
        CONTINUOUS_WITHIN_SUBSET, .. } := D.cn.cx.cvx.top3
  let { IN_INTERVAL_1, .. } := D.cn.cx.cvx.top4
  let { closed, continuous_at, continuous_within, OPEN_INTER, OPEN_UNIV,
        .. } := D.cn.cx.cvx.top5
  let { CONTINUOUS_AT, CONTINUOUS_AT_WITHIN, CONTINUOUS_OPEN_PREIMAGE,
        .. } := D.cn.ms.ig.dv.qtopology1
  let { LIM_TRANSFORM_WITHIN_OPEN, .. } := D.cn.ms.ig.dv.qtopology2
  let { SQRT_UNIQUE, .. } := D.cn.ms.ig.dv.dg.qsession
  let { CONTINUOUS_ON_CASES_LOCAL, .. } := D.cn.ms.ig.dv.dg.qtopology1
  -- @@SCOPE END

  let ARG_CLOG ← prove
   r"!z. &0 < Arg z ==> Arg z = Im(clog(--z)) + pi"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"z = Cx(&0)") THENL
     [ASM_REWRITE_TAC [Arg_DEF, REAL_LT_REFL], ALL_TAC] THEN
    DISCH_TAC THEN MP_TAC (← liftExcept (last (CONJUNCTS (← SPEC (← q r"z:complex") ARG)))) THEN
    ASM_SIMP_TAC [CX_INJ, COMPLEX_NORM_ZERO, ← ExceptT.mk (COMPLEX_FIELD
     (← q r"~(z = Cx(&0)) ==> (w = z * a <=> a = w / z)"))] THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"( * ) (cexp(--(ii * Cx pi)))")) THEN
    REWRITE_TAC [← GSYM CEXP_ADD] THEN DISCH_THEN (MP_TAC o AP_TERM (← q r"clog")) THEN
    W (MP_TAC o PART_MATCH (lhs o rand) CLOG_CEXP o lhand o lhand o snd) THEN
    REWRITE_TAC [IM_ADD, IM_MUL_II, RE_CX, IM_NEG] THEN
    ASM_SIMP_TAC [REAL_LT_ADDR, ARG, ← REAL_ARITH
      (← q r"z < &2 * pi ==> --pi + z <= pi")] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [CEXP_NEG, CEXP_EULER] THEN
    REWRITE_TAC [← GSYM CX_SIN, ← GSYM CX_COS, SIN_PI, COS_PI] THEN
    REWRITE_TAC [CX_NEG, COMPLEX_MUL_RZERO, COMPLEX_ADD_RID,
                 ← SIMPLE_COMPLEX_ARITH (← q r"inv(--Cx(&1)) * z / w = --z / w")] THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"Im")) THEN
    REWRITE_TAC [IM_ADD, IM_NEG, IM_MUL_II, RE_CX] THEN
    MATCH_MP_TAC (← REAL_RING (← q r"w = z ==> --pi + x = w ==> x = z + pi")) THEN
    REWRITE_TAC [complex_div] THEN
    W (MP_TAC o PART_MATCH (lhs o rand) CLOG_MUL_SIMPLE o rand o lhand o snd) THEN
    ASM_SIMP_TAC [CX_INJ, REAL_INV_EQ_0, COMPLEX_NORM_ZERO, COMPLEX_NEG_EQ_0,
      ← GSYM CX_INV, ← GSYM CX_LOG, REAL_LT_INV_EQ, COMPLEX_NORM_NZ, IM_CX] THEN
    ASM_SIMP_TAC [REAL_ADD_RID, CLOG_WORKS, COMPLEX_NEG_EQ_0] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IM_ADD, IM_CX, REAL_ADD_RID])

  let CONTINUOUS_AT_ARG ← (do
    let lemma ← prove
     r"(\z. Cx(Im(f z) + pi)) = (Cx o Im) o (\z. f z + ii * Cx pi)"
     (REWRITE_TAC [FUN_EQ_THM, o_DEF, IM_ADD, IM_CX, IM_MUL_II, RE_CX])
    prove
     r"!z. ~(real z /\ &0 <= Re z) ==> (Cx o Arg) continuous (at z)"
     (REPEAT STRIP_TAC THEN REWRITE_TAC [CONTINUOUS_AT] THEN
      MATCH_MP_TAC LIM_TRANSFORM_WITHIN_OPEN THEN
      EXISTS_TAC (← q r"\z. Cx(Im(clog(--z)) + pi)") THEN
      EXISTS_TAC (← q r"(:complex) DIFF {z | real z /\ &0 <= Re z}") THEN
      ASM_REWRITE_TAC [IN_DIFF, IN_UNIV, IN_ELIM_THM, ← GSYM closed] THEN
      ASM_SIMP_TAC [o_THM, ARG_CLOG, ARG_LT_NZ, ARG_EQ_0] THEN CONJ_TAC THENL
       [REWRITE_TAC [← SET_RULE (← q r"{z | P z /\ Q z} = P INTER {z | Q z}")] THEN
        MATCH_MP_TAC CLOSED_INTER THEN
        REWRITE_TAC [CLOSED_REAL, ← GSYM real_ge, CLOSED_HALFSPACE_RE_GE],
        REWRITE_TAC [← GSYM CONTINUOUS_AT, lemma] THEN
        MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
        REWRITE_TAC [CONTINUOUS_AT_CX_IM] THEN
        MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC [CONTINUOUS_CONST] THEN
        MATCH_MP_TAC (← REWRITE_RULE [o_DEF] CONTINUOUS_AT_COMPOSE) THEN
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [← GSYM ETA_AX] THEN
        SIMP_TAC [CONTINUOUS_NEG, CONTINUOUS_AT_ID] THEN
        MATCH_MP_TAC CONTINUOUS_AT_CLOG THEN POP_ASSUM MP_TAC THEN
        REWRITE_TAC [real, IM_NEG, RE_NEG] THEN REAL_ARITH_TAC]))

  let CONTINUOUS_ON_ARG ← prove
   r"!s. (!z. z IN s /\ real z ==> Re z < &0) ==> (Cx o Arg) continuous_on s"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_ARG THEN
    ASM_MESON_TAC [REAL_NOT_LE])

  let CONTINUOUS_WITHIN_UPPERHALF_ARG ← prove
   r"!z. ~(z = Cx(&0))
       ==> (Cx o Arg) continuous (at z) within {z | &0 <= Im z}"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"real z /\ &0 <= Re z") THEN
    ASM_SIMP_TAC [CONTINUOUS_AT_ARG, CONTINUOUS_AT_WITHIN] THEN
    FIRST_X_ASSUM (CONJUNCTS_THEN2
     (ASSUME_TAC o GEN_REWRITE_RULE id [real]) MP_TAC) THEN
    SUBGOAL_THEN (← q r"~(Re z = &0)") ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC (← q r"~(z = Cx(&0))") THEN
      ASM_REWRITE_TAC [COMPLEX_EQ, RE_CX, IM_CX],
      GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT]] THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MP_TAC (← ISPEC (← q r"rotate2d (pi / &2) z") CONTINUOUS_AT_ARG) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC [ROTATE2D_PI2, real, IM_MUL_II], ALL_TAC] THEN
    REWRITE_TAC [continuous_at, continuous_within] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"e:real") THEN
    ASM_CASES_TAC (← q r"&0 < e") THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"d:real") THEN
    REWRITE_TAC [o_THM, dist, ← GSYM CX_SUB, COMPLEX_NORM_CX] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"w:complex") THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"Arg z = &0") ASSUME_TAC THENL
     [ASM_SIMP_TAC [ARG_EQ_0, real, REAL_LT_IMP_LE], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"Arg w = &0") THEN
    ASM_REWRITE_TAC [REAL_SUB_REFL, REAL_ABS_NUM] THEN
    SUBGOAL_THEN (← q r"&0 < Arg w") ASSUME_TAC THENL
     [ASM_REWRITE_TAC [ARG, REAL_LT_LE], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"rotate2d (pi / &2) w")) THEN
    ASM_REWRITE_TAC [← GSYM ROTATE2D_SUB, NORM_ROTATE2D] THEN
    MP_TAC (← ISPECL [← q r"pi / &2", ← q r"z:complex"] ARG_ROTATE2D) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [REAL_ADD_RID] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"w' = p + w ==> abs(w' - p) < e ==> abs(w - &0) < e")) THEN
    MATCH_MP_TAC ARG_ROTATE2D THEN CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC (← q r"&0 < Arg w") THEN
      ASM_REWRITE_TAC [Arg_DEF, REAL_LT_REFL],
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [← GSYM ARG_LE_PI]) THEN
      MP_TAC (← SPEC (← q r"w:complex") ARG) THEN REAL_ARITH_TAC])

  let CONTINUOUS_ON_UPPERHALF_ARG ← prove
   r"(Cx o Arg) continuous_on ({z | &0 <= Im z} DIFF {Cx(&0)})"
   (REWRITE_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC (← q r"z:complex") THEN REWRITE_TAC [IN_DIFF, IN_SING, IN_ELIM_THM] THEN
    STRIP_TAC THEN FIRST_ASSUM (MP_TAC o
      MATCH_MP CONTINUOUS_WITHIN_UPPERHALF_ARG) THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] CONTINUOUS_WITHIN_SUBSET) THEN
    SET_TAC [])

  let CONTINUOUS_ON_COMPOSE_ARG ← (do
    let ulemma ← prove
     r"!s. s INTER {z | &0 <= Im z} UNION s INTER {z | Im z <= &0} = s"
     (SET_TAC [REAL_LE_TOTAL])
    prove
     r"!s p:real->real^N.
        (p o drop) continuous_on interval[vec 0,lift(&2 * pi)] /\
        p(&2 * pi) = p(&0) /\ ~(Cx(&0) IN s)
        ==> (\z. p(Arg z)) continuous_on s"
     (REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
      EXISTS_TAC
       (← q r"\z. if &0 <= Im z then p(Arg z)
            else p(&2 * pi - Arg(cnj z)):real^N") THEN
      REWRITE_TAC [IN_UNIV, IN_SING, IN_DIFF] THEN CONJ_TAC THENL
       [X_GEN_TAC (← q r"z:complex") THEN DISCH_TAC THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [ARG_CNJ] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_SUB_SUB2] THEN
        SUBGOAL_THEN (← q r"Arg z = &0")
         (fun th => ASM_REWRITE_TAC [REAL_SUB_RZERO, th]) THEN
        ASM_REWRITE_TAC [ARG_EQ_0],
        GEN_REWRITE_TAC RAND_CONV [← GSYM ulemma] THEN
        MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN REWRITE_TAC [ulemma] THEN
        SIMP_TAC [CLOSED_IN_CLOSED_INTER, CLOSED_HALFSPACE_IM_LE,
                  ← REWRITE_RULE [real_ge] CLOSED_HALFSPACE_IM_GE] THEN
        REWRITE_TAC [IN_INTER, IN_DIFF, IN_UNIV, IN_SING, IN_ELIM_THM] THEN
        SIMP_TAC [← GSYM CONJ_ASSOC, REAL_LE_ANTISYM, ← TAUT (← q r"~(p /\ ~p)")] THEN
        REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL
         [GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV) [← GSYM o_DEF] THEN
          SUBGOAL_THEN (← q r"(p:real->real^N) = (p o drop) o lift") SUBST1_TAC THENL
           [REWRITE_TAC [o_DEF, LIFT_DROP, ETA_AX], ALL_TAC] THEN
          ONCE_REWRITE_TAC [← GSYM o_ASSOC] THEN
          CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
           [REWRITE_TAC [o_DEF, ← GSYM CONTINUOUS_ON_CX_LIFT] THEN
            MP_TAC CONTINUOUS_ON_UPPERHALF_ARG THEN REWRITE_TAC [o_DEF] THEN
            MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] CONTINUOUS_ON_SUBSET) THEN
            ASM SET_TAC [],
            FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
              CONTINUOUS_ON_SUBSET)) THEN
            REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_INTER, IN_ELIM_THM] THEN
            REWRITE_TAC [IN_INTERVAL_1, LIFT_DROP, o_THM, DROP_VEC] THEN
            SIMP_TAC [ARG, REAL_LT_IMP_LE],
            REWRITE_TAC [o_DEF, LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
            REWRITE_TAC [CONTINUOUS_ON_CONST] THEN
            GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [← GSYM o_DEF] THEN
            REWRITE_TAC [o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
            REWRITE_TAC [CONTINUOUS_ON_CNJ, o_DEF, ← GSYM CONTINUOUS_ON_CX_LIFT] THEN
            MP_TAC CONTINUOUS_ON_UPPERHALF_ARG THEN REWRITE_TAC [o_DEF] THEN
            MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] CONTINUOUS_ON_SUBSET) THEN
            SIMP_TAC [SUBSET, FORALL_IN_IMAGE, IN_INTER, IN_ELIM_THM, IN_DIFF] THEN
            SIMP_TAC [IN_SING, CNJ_EQ_0, IM_CNJ, REAL_NEG_GE0] THEN ASM SET_TAC [],
            FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
              CONTINUOUS_ON_SUBSET)) THEN
            REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_INTER, IN_ELIM_THM] THEN
            REWRITE_TAC [IN_INTERVAL_1, LIFT_DROP, o_THM, DROP_VEC] THEN
            X_GEN_TAC (← q r"z:complex") THEN STRIP_TAC THEN
            MP_TAC (← SPEC (← q r"cnj z") ARG) THEN REAL_ARITH_TAC],
          REWRITE_TAC [← GSYM ARG_EQ_0_PI, ← GSYM real, ARG_CNJ] THEN
          REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
          COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_SUB_SUB2, REAL_SUB_RZERO] THEN
          ASM_REWRITE_TAC [← REAL_ARITH (← q r"&2 * x - x = x")]]]))

  let OPEN_ARG_LTT ← prove
   r"!s t. &0 <= s /\ t <= &2 * pi ==> open {z | s < Arg z /\ Arg z < t}"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"Cx o Arg", ← q r"(:complex) DIFF {z | real z /\ &0 <= Re z}",
                      ← q r"{z | Re(z) > s} INTER {z | Re(z) < t}"]
             CONTINUOUS_OPEN_PREIMAGE) THEN
    ASM_SIMP_TAC [OPEN_INTER, OPEN_HALFSPACE_RE_GT, OPEN_HALFSPACE_RE_LT] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
        REWRITE_TAC [IN_DIFF, IN_UNIV, IN_ELIM_THM, CONTINUOUS_AT_ARG],
        REWRITE_TAC [← GSYM closed] THEN
        REWRITE_TAC [← SET_RULE (← q r"{z | P z /\ Q z} = P INTER {z | Q z}")] THEN
        MATCH_MP_TAC CLOSED_INTER THEN
        REWRITE_TAC [CLOSED_REAL, ← GSYM real_ge, CLOSED_HALFSPACE_RE_GE]],
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC [EXTENSION] THEN
      ASM_SIMP_TAC [IN_DIFF, IN_INTER, IN_UNIV, IN_ELIM_THM, o_THM, RE_CX,
                    ← GSYM ARG_EQ_0] THEN
      ASM_REAL_ARITH_TAC])

  let OPEN_ARG_GT ← prove
   r"!t. open {z | t < Arg z}"
   (GEN_TAC THEN DISJ_CASES_TAC (← REAL_ARITH (← q r"t < &0 \/ &0 <= t")) THENL
     [SUBGOAL_THEN (← q r"{z | t < Arg z} = (:complex)")
       (fun th => SIMP_TAC [th, OPEN_UNIV]) THEN
      REWRITE_TAC [EXTENSION, IN_UNIV, IN_ELIM_THM] THEN
      MP_TAC ARG THEN MATCH_MP_TAC MONO_FORALL THEN ASM_REAL_ARITH_TAC,
      MP_TAC (← ISPECL [← q r"t:real", ← q r"&2 * pi"] OPEN_ARG_LTT) THEN
      ASM_REWRITE_TAC [ARG, REAL_LE_REFL]])

  let CLOSED_ARG_LE ← prove
   r"!t. closed {z | Arg z <= t}"
   (REWRITE_TAC [closed, DIFF, IN_UNIV, IN_ELIM_THM] THEN
    REWRITE_TAC [REAL_NOT_LE, OPEN_ARG_GT])

  let ARG_ATAN_UPPERHALF ← prove
   r"!z. &0 < Im z ==> Arg(z) = pi / &2 - atn(Re z / Im z)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"z = Cx(&0)") THEN
    ASM_REWRITE_TAC [IM_CX, REAL_LT_REFL] THEN DISCH_TAC THEN
    MATCH_MP_TAC ARG_UNIQUE THEN EXISTS_TAC (← q r"norm(z:complex)") THEN
    ASM_REWRITE_TAC [COMPLEX_NORM_NZ] THEN CONJ_TAC THENL
     [ALL_TAC, MP_TAC (← ISPEC (← q r"Re z / Im z") ATN_BOUNDS) THEN REAL_ARITH_TAC] THEN
    REWRITE_TAC [CEXP_EULER, ← GSYM CX_SIN, ← GSYM CX_COS] THEN
    REWRITE_TAC [SIN_SUB, COS_SUB, SIN_PI2, COS_PI2] THEN
    REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_LID, SIN_ATN, COS_ATN] THEN
    SUBGOAL_THEN (← q r"sqrt(&1 + (Re z / Im z) pow 2) = norm(z) / Im z")
    SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_UNIQUE THEN
      ASM_SIMP_TAC [REAL_LE_DIV, NORM_POS_LE, REAL_LT_IMP_LE] THEN
      REWRITE_TAC [REAL_POW_DIV, COMPLEX_SQNORM] THEN
      UNDISCH_TAC (← q r"&0 < Im z") THEN CONV_TAC REAL_FIELD,
      REWRITE_TAC [REAL_ADD_LID, REAL_SUB_RZERO, real_div] THEN
      REWRITE_TAC [COMPLEX_EQ, RE_MUL_CX, IM_MUL_CX, RE_MUL_II, IM_MUL_II,
                   RE_ADD, IM_ADD, RE_CX, IM_CX] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [← GSYM COMPLEX_NORM_NZ]) THEN
      POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD])

  pure { ARG_CLOG, CONTINUOUS_AT_ARG, CONTINUOUS_ON_ARG, CONTINUOUS_WITHIN_UPPERHALF_ARG,
         CONTINUOUS_ON_UPPERHALF_ARG, CONTINUOUS_ON_COMPOSE_ARG, OPEN_ARG_LTT,
         OPEN_ARG_GT, CLOSED_ARG_LE, ARG_ATAN_UPPERHALF }
/- ------------------------------------------------------------------------- -/
/- Real n'th roots. Regardless of whether n is odd or even, we totalize by   -/
/- setting root_n(-x) = -root_n(x), which makes some convenient facts hold.  -/
/- (transcendentals.ml 6373-6572)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSAA where
  root : thm
  ROOT_0 : thm
  ROOT_1 : thm
  ROOT_2 : thm
  ROOT_NEG : thm
  ROOT_WORKS : thm
  REAL_POW_ROOT : thm
  ROOT_POS_LT : thm
  ROOT_POS_LE : thm
  ROOT_LT_0 : thm
  ROOT_LE_0 : thm
  ROOT_EQ_0 : thm
  REAL_ROOT_MUL : thm
  REAL_ROOT_POW_GEN : thm
  REAL_ROOT_POW : thm
  ROOT_UNIQUE : thm
  REAL_ROOT_INV : thm
  REAL_ROOT_DIV : thm
  ROOT_MONO_LT : thm
  ROOT_MONO_LE : thm
  ROOT_MONO_LT_EQ : thm
  ROOT_MONO_LE_EQ : thm
  ROOT_INJ : thm
  REAL_ROOT_LE : thm
  REAL_LE_ROOT : thm
  LOG_ROOT : thm
  ROOT_EXP_LOG : thm
  ROOT_PRODUCT : thm
  SQRT_PRODUCT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSAA [HolBase] (D : TranscendentalsDeps) (BTSB : TSB) (BTSD : TSD) : ExceptT String IO TSAA := do
  -- @@SCOPE BEGIN
  let { REAL_EXP_0, REAL_EXP_ADD, REAL_EXP_N, REAL_EXP_NEG, REAL_EXP_NZ, REAL_EXP_POS_LT,
        .. } := BTSB
  let { EXP_LOG, LOG_1, LOG_INV, LOG_MUL, LOG_POW, .. } := BTSD
  let { REAL_INV_SGN, REAL_POW_LT2_REV, REAL_POW_POW, REAL_SGN_0, REAL_SGN_ABS,
        REAL_SGN_INV, REAL_SGN_NEG, REAL_SGN_POW, REAL_SGN_POW_2, REAL_SGN_REAL_SGN,
        SQRT_UNIQUE_GEN, .. } := D.qsession
  let { REAL_POW_ZERO, real_sgn, .. } := D.cn.ms.qsession
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INDUCT_TAC, MESON_TAC, new_definition,
        REAL_ARITH, REAL_ARITH_TAC, .. } := D.cn.cx.cvx
  let { PRODUCT_CLAUSES, .. } := D.cn.cx.cpx
  let { REAL_EQ_RDIV_EQ, .. } := D.cn.ms.ig.qsession
  let { ARITH, CONTRAPOS_THM, FINITE_INDUCT_STRONG, .. } := D.cn.cx.cvx.core1
  let { IMP_CONJ, .. } := D.cn.cx.cvx.core2
  let { LE_1, REAL_ABS_INV, REAL_ABS_MUL, REAL_ABS_NEG, REAL_ABS_NUM, REAL_ADD_RDISTRIB,
        REAL_DIV_LMUL, .. } := D.cn.cx.cvx.core3
  let { REAL_ENTIRE, REAL_INV_0, REAL_INV_MUL, REAL_LE_ANTISYM, REAL_LE_LT, REAL_LT_01,
        REAL_LT_IMP_LE, REAL_LT_LE, REAL_LT_MUL, REAL_LT_REFL, REAL_LTE_TRANS,
        .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LNEG, REAL_MUL_LZERO, REAL_MUL_RID,
        REAL_MUL_RZERO, REAL_MUL_SYM, REAL_NOT_LE, REAL_NOT_LT, REAL_OF_NUM_EQ,
        REAL_OF_NUM_LT, REAL_POW_LE, REAL_POW_MUL, REAL_POW_ONE, RIGHT_FORALL_IMP_THM,
        SQRT_1, SQRT_MUL, .. } := D.cn.cx.cvx.core5
  let { real_abs, real_div, real_pow, .. } := D.cn.cx.cvx.core6
  let { REAL_ABS_NZ, .. } := D.cn.ms.ig.dv.qsession
  let { ODD_EXISTS, REAL_SGN_INEQS, REAL_SGN_MUL, .. } := D.cn.ms.ig.dv.dg.qsession
  -- @@SCOPE END

  let root ← new_definition
   r"root(n) x = real_sgn(x) * exp(log(abs x) / &n)"

  let ROOT_0 ← prove
   r"!n. root n (&0) = &0"
   (REWRITE_TAC [root, REAL_SGN_0, REAL_MUL_LZERO])

  let ROOT_1 ← prove
   r"!n. root n (&1) = &1"
   (REWRITE_TAC [root, REAL_ABS_NUM, LOG_1, real_div, REAL_MUL_LZERO] THEN
    REWRITE_TAC [real_sgn, REAL_EXP_0] THEN REAL_ARITH_TAC)

  let ROOT_2 ← prove
   r"!x. root 2 x = sqrt x"
   (GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE_GEN THEN
    REWRITE_TAC [root, REAL_SGN_MUL, REAL_POW_MUL, REAL_SGN_REAL_SGN] THEN
    REWRITE_TAC [REAL_SGN_POW_2, ← GSYM REAL_SGN_POW] THEN
    SIMP_TAC [real_sgn, REAL_EXP_POS_LT, REAL_MUL_RID] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"(&0 < abs x <=> ~(x = &0)) /\ ~(abs x < &0)")] THEN
    ASM_CASES_TAC (← q r"x = &0") THEN
    ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_ABS_NUM, REAL_MUL_LID] THEN
    REWRITE_TAC [← GSYM REAL_EXP_N, ← REAL_ARITH (← q r"&2 * x / &2 = x")] THEN
    ASM_SIMP_TAC [EXP_LOG, ← REAL_ARITH (← q r"&0 < abs x <=> ~(x = &0)")])

  let ROOT_NEG ← prove
   r"!n x. root n (--x) = --(root n x)"
   (REWRITE_TAC [root, REAL_SGN_NEG, REAL_ABS_NEG, REAL_MUL_LNEG])

  let ROOT_WORKS ← prove
   r"!n x. real_sgn(root n x) = real_sgn x /\
         (root n x) pow n = if n = 0 then &1
                            else real_sgn(x) pow n * abs x"
   (REWRITE_TAC [root, REAL_SGN_MUL, REAL_POW_MUL, ← GSYM REAL_EXP_N] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [real_div, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_INV_0,
                     REAL_EXP_0, REAL_MUL_RID, real_pow, REAL_SGN_REAL_SGN] THEN
    REWRITE_TAC [real_sgn, REAL_LT_01, REAL_MUL_RID] THEN
    ASM_SIMP_TAC [REAL_EXP_POS_LT, REAL_MUL_RID, ← GSYM REAL_ABS_NZ,
                  ← GSYM real_div, REAL_DIV_LMUL, REAL_OF_NUM_EQ] THEN
    ASM_CASES_TAC (← q r"x = &0") THEN
    ASM_REWRITE_TAC [REAL_LT_REFL, REAL_POW_ZERO, REAL_MUL_LZERO] THEN
    ASM_SIMP_TAC [EXP_LOG, ← GSYM REAL_ABS_NZ])

  let REAL_POW_ROOT ← prove
   r"!n x. ODD n \/ ~(n = 0) /\ &0 <= x ==> (root n x) pow n = x"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [ARITH] THEN STRIP_TAC THEN ASM_REWRITE_TAC [ROOT_WORKS] THENL
     [FIRST_ASSUM (CHOOSE_THEN SUBST1_TAC o GEN_REWRITE_RULE id [ODD_EXISTS]) THEN
      REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_MUL_SYM] real_pow] THEN
      REWRITE_TAC [← GSYM REAL_MUL_ASSOC, REAL_SGN_ABS] THEN
      REWRITE_TAC [← GSYM REAL_POW_POW] THEN
      REWRITE_TAC [← REWRITE_RULE [REAL_SGN_POW] REAL_SGN_POW_2] THEN
      REWRITE_TAC [real_sgn, ← GSYM REAL_ABS_NZ] THEN
      ASM_CASES_TAC (← q r"x = &0") THEN
      ASM_REWRITE_TAC [REAL_LT_REFL, REAL_POW_ONE] THEN ASM_REAL_ARITH_TAC,
      ASM_REWRITE_TAC [real_sgn, REAL_LT_LE] THEN
      ASM_CASES_TAC (← q r"x = &0") THEN
      ASM_REWRITE_TAC [REAL_POW_ZERO, REAL_POW_ONE] THEN
      ASM_REAL_ARITH_TAC])

  let ROOT_POS_LT ← prove
   r"!n x. &0 < x ==> &0 < root n x"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [root] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC [REAL_EXP_POS_LT, REAL_SGN_INEQS])

  let ROOT_POS_LE ← prove
   r"!n x. &0 <= x ==> &0 <= root n x"
   (MESON_TAC [REAL_LE_LT, ROOT_POS_LT, ROOT_0, REAL_LT_REFL])

  let ROOT_LT_0 ← prove
   r"!n x. &0 < root n x <=> &0 < x"
   (REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [ROOT_POS_LT] THEN
    REWRITE_TAC [← GSYM REAL_NOT_LE] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"x <= &0 <=> &0 <= --x"), ← GSYM ROOT_NEG] THEN
    REWRITE_TAC [ROOT_POS_LE])

  let ROOT_LE_0 ← prove
   r"!n x. &0 <= root n x <=> &0 <= x"
   (REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [ROOT_POS_LE] THEN
    REWRITE_TAC [← GSYM REAL_NOT_LT] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"x < &0 <=> &0 < --x"), ← GSYM ROOT_NEG] THEN
    REWRITE_TAC [ROOT_POS_LT])

  let ROOT_EQ_0 ← prove
   r"!n x. root n x = &0 <=> x = &0"
   (REWRITE_TAC [root, REAL_ENTIRE, REAL_EXP_NZ, REAL_SGN_INEQS])

  let REAL_ROOT_MUL ← prove
   r"!n x y. root n (x * y) = root n x * root n y"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"x = &0") THEN ASM_REWRITE_TAC [REAL_MUL_LZERO, ROOT_0] THEN
    ASM_CASES_TAC (← q r"y = &0") THEN ASM_REWRITE_TAC [REAL_MUL_RZERO, ROOT_0] THEN
    REWRITE_TAC [root, REAL_SGN_MUL, REAL_ABS_MUL] THEN
    ASM_SIMP_TAC [LOG_MUL, ← GSYM REAL_ABS_NZ, real_div] THEN
    REWRITE_TAC [REAL_ADD_RDISTRIB, REAL_EXP_ADD] THEN
    REAL_ARITH_TAC)

  let REAL_ROOT_POW_GEN ← prove
   r"!m n x. root n (x pow m) = (root n x) pow m"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [REAL_ROOT_MUL, ROOT_1, real_pow])

  let REAL_ROOT_POW ← prove
   r"!n x. ODD n \/ ~(n = 0) /\ &0 <= x ==> root n (x pow n) = x"
   (SIMP_TAC [REAL_ROOT_POW_GEN, REAL_POW_ROOT])

  let ROOT_UNIQUE ← prove
   r"!n x y. y pow n = x /\ (ODD n \/ ~(n = 0) /\ &0 <= y) ==> root n x = y"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
    UNDISCH_THEN (← q r"(y:real) pow n = x") (SUBST_ALL_TAC o SYM) THEN
    MATCH_MP_TAC REAL_ROOT_POW THEN ASM_REWRITE_TAC [])

  let REAL_ROOT_INV ← prove
   r"!n x. root n (inv x) = inv(root n x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [root, REAL_SGN_INV, REAL_INV_SGN] THEN
    ASM_CASES_TAC (← q r"x = &0") THEN
    ASM_REWRITE_TAC [REAL_SGN_0, REAL_MUL_LZERO, REAL_INV_0] THEN
    REWRITE_TAC [REAL_INV_MUL, REAL_INV_SGN, REAL_ABS_INV] THEN
    ASM_SIMP_TAC [← GSYM REAL_EXP_NEG, LOG_INV, ← GSYM REAL_ABS_NZ] THEN
    REWRITE_TAC [real_div, REAL_MUL_LNEG])

  let REAL_ROOT_DIV ← prove
   r"!n x y. root n (x / y) = root n x / root n y"
   (SIMP_TAC [real_div, REAL_ROOT_MUL, REAL_ROOT_INV])

  let ROOT_MONO_LT ← prove
   r"!n x y. ~(n = 0) /\ x < y ==> root n x < root n y"
   (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN (← q r"!x y. &0 <= x /\ x < y ==> root n x < root n y")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LT2_REV THEN
      EXISTS_TAC (← q r"n:num") THEN ASM_REWRITE_TAC [ROOT_WORKS, ROOT_LE_0] THEN
      ASM_REWRITE_TAC [real_sgn] THEN REPEAT
       (COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_POW_ONE, REAL_POW_ZERO]) THEN
      ASM_REAL_ARITH_TAC,
      REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"&0 <= x") THEN ASM_SIMP_TAC [] THEN
      ASM_CASES_TAC (← q r"&0 <= y") THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q r"&0") THEN
        ASM_REWRITE_TAC [← GSYM REAL_NOT_LE, ROOT_LE_0],
        FIRST_X_ASSUM (MP_TAC o SPECL [← q r"--y:real", ← q r"--x:real"]) THEN
        REWRITE_TAC [ROOT_NEG] THEN ASM_REAL_ARITH_TAC]])

  let ROOT_MONO_LE ← prove
   r"!n x y. x <= y ==> root n x <= root n y"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THENL
     [ASM_REWRITE_TAC [root, real_div, REAL_INV_0, REAL_MUL_RZERO,
                       REAL_EXP_0, REAL_MUL_RID] THEN
      REWRITE_TAC [real_sgn] THEN ASM_REAL_ARITH_TAC,
      ASM_MESON_TAC [REAL_LE_LT, ROOT_0, ROOT_MONO_LT]])

  let ROOT_MONO_LT_EQ ← prove
   r"!n x y. ~(n = 0) ==> (root n x < root n y <=> x < y)"
   (MESON_TAC [ROOT_MONO_LT, REAL_NOT_LT, ROOT_MONO_LE])

  let ROOT_MONO_LE_EQ ← prove
   r"!n x y. ~(n = 0) ==> (root n x <= root n y <=> x <= y)"
   (MESON_TAC [ROOT_MONO_LT, REAL_NOT_LT, ROOT_MONO_LE])

  let ROOT_INJ ← prove
   r"!n x y. ~(n = 0) ==> (root n x = root n y <=> x = y)"
   (SIMP_TAC [← GSYM REAL_LE_ANTISYM, ROOT_MONO_LE_EQ])

  let REAL_ROOT_LE ← prove
   r"!n x y. ~(n = 0) /\ &0 <= y
           ==> (root n x <= y <=> x <= y pow n)"
   (MESON_TAC [REAL_ROOT_POW, REAL_POW_LE, ROOT_MONO_LE_EQ])

  let REAL_LE_ROOT ← prove
   r"!n x y. ~(n = 0) /\ &0 <= x
           ==> (x <= root n y <=> x pow n <= y)"
   (MESON_TAC [REAL_ROOT_POW, REAL_POW_LE, ROOT_MONO_LE_EQ])

  let LOG_ROOT ← prove
   r"!n x. ~(n = 0) /\ &0 < x ==> log(root n x) = log x / &n"
   (SIMP_TAC [REAL_EQ_RDIV_EQ, REAL_OF_NUM_LT, LE_1] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    SIMP_TAC [← GSYM LOG_POW, ROOT_POS_LT, REAL_POW_ROOT, REAL_LT_IMP_LE])

  let ROOT_EXP_LOG ← prove
   r"!n x. ~(n = 0) /\ &0 < x ==> root n x = exp(log x / &n)"
   (SIMP_TAC [root, real_sgn, real_abs, REAL_LT_IMP_LE, REAL_MUL_LID])

  let ROOT_PRODUCT ← prove
   r"!n f s. FINITE s ==> root n (product s f) = product s (\i. root n (f i))"
   (GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [PRODUCT_CLAUSES, REAL_ROOT_MUL, ROOT_1])

  let SQRT_PRODUCT ← prove
   r"!f s. FINITE s ==> sqrt(product s f) = product s (\i. sqrt(f i))"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [PRODUCT_CLAUSES, SQRT_MUL, SQRT_1])

  pure { root, ROOT_0, ROOT_1, ROOT_2, ROOT_NEG, ROOT_WORKS, REAL_POW_ROOT, ROOT_POS_LT,
         ROOT_POS_LE, ROOT_LT_0, ROOT_LE_0, ROOT_EQ_0, REAL_ROOT_MUL, REAL_ROOT_POW_GEN,
         REAL_ROOT_POW, ROOT_UNIQUE, REAL_ROOT_INV, REAL_ROOT_DIV, ROOT_MONO_LT,
         ROOT_MONO_LE, ROOT_MONO_LT_EQ, ROOT_MONO_LE_EQ, ROOT_INJ, REAL_ROOT_LE,
         REAL_LE_ROOT, LOG_ROOT, ROOT_EXP_LOG, ROOT_PRODUCT, SQRT_PRODUCT }
/- ------------------------------------------------------------------------- -/
/- Real power function. This involves a few arbitrary choices.              -/
/- (transcendentals.ml 6573-6912)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSAB where
  rpow : thm
  RPOW_POW : thm
  RPOW_0 : thm
  RPOW_NEG : thm
  RPOW_ZERO : thm
  RPOW_POS_LT : thm
  RPOW_POS_LE : thm
  RPOW_LT2 : thm
  RPOW_LE2 : thm
  REAL_ABS_RPOW : thm
  RPOW_ONE : thm
  RPOW_RPOW : thm
  RPOW_LNEG : thm
  RPOW_EQ_0 : thm
  RPOW_MUL : thm
  RPOW_INV : thm
  REAL_INV_RPOW : thm
  RPOW_DIV : thm
  RPOW_PRODUCT : thm
  RPOW_ADD : thm
  RPOW_SUB : thm
  RPOW_ADD_ALT : thm
  RPOW_SUB_ALT : thm
  RPOW_SQRT : thm
  RPOW_MONO_LE : thm
  RPOW_MONO_LT : thm
  RPOW_MONO_LE_EQ : thm
  RPOW_MONO_LT_EQ : thm
  RPOW_INJ : thm
  RPOW_LE_1 : thm
  RPOW_LT_1 : thm
  RPOW_MONO_INV : thm
  RPOW_1_LE : thm
  REAL_ROOT_RPOW : thm
  LOG_RPOW : thm
  LOG_SQRT : thm
  RPOW_ADD_INTEGER : thm
  NORM_CPOW : thm
  REAL_MAX_RPOW : thm
  REAL_MIN_RPOW : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSAB [HolBase] (D : TranscendentalsDeps) (BTSB : TSB) (BTSD : TSD) (BTSO : TSO) (BTSAA : TSAA) : ExceptT String IO TSAB := do
  -- @@SCOPE BEGIN
  let { REAL_ABS_EXP, REAL_EXP_0, REAL_EXP_ADD, REAL_EXP_MONO_LE, REAL_EXP_MONO_LT,
        REAL_EXP_N, REAL_EXP_NEG, REAL_EXP_NZ, REAL_EXP_POS_LT, .. } := BTSB
  let { EXP_LOG, LOG_1, LOG_EXP, LOG_INV, LOG_MONO_LT_IMP, LOG_MUL, LOG_POS, LOG_POS_LT,
        .. } := BTSD
  let { NORM_CPOW_REAL, .. } := BTSO
  let { ROOT_0, ROOT_EXP_LOG, ROOT_UNIQUE, .. } := BTSAA
  let { ARITH_ODD, is_int, ODD, ODD_MULT, REAL_EQ_INV2, REAL_INV_1_LE,
        REAL_OF_NUM_SUB_CASES, REAL_POW_SUB, .. } := D.qsession
  let { RE_CX, .. } := D.cn.cxc
  let { COMPLEX_NORM_NZ, .. } := D.cn.cxf
  let { REAL_NORM, .. } := D.cn.cxj
  let { REAL_POW_ZERO, .. } := D.cn.ms.qsession
  let { ARITH_RULE, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC, new_definition,
        parse_as_infix, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD, REAL_RAT_REDUCE_CONV,
        REAL_RING, .. } := D.cn.cx.cvx
  let { PRODUCT_CLAUSES, REAL_ABS_ZERO, REAL_POW_1, REAL_POW_ADD, real_sub,
        .. } := D.cn.cx.cpx
  let { ARITH, COND_ID, FINITE_INDUCT_STRONG, .. } := D.cn.cx.cvx.core1
  let { IMP_CONJ, .. } := D.cn.cx.cvx.core2
  let { LEFT_IMP_EXISTS_THM, REAL_ABS_INV, REAL_ABS_NEG, REAL_ABS_NUM, REAL_ADD_LDISTRIB,
        REAL_ADD_LID, REAL_ADD_RDISTRIB, REAL_DIV_1, .. } := D.cn.cx.cvx.core3
  let { REAL_ENTIRE, REAL_EQ_NEG2, REAL_INV_0, REAL_INV_1, REAL_INV_1_LT, REAL_INV_EQ_0,
        REAL_INV_MUL, REAL_INV_NEG, REAL_LE_ANTISYM, REAL_LE_INV2, REAL_LE_LT,
        REAL_LE_REFL, REAL_LE_RMUL, REAL_LE_TRANS, REAL_LT_01, REAL_LT_IMP_LE,
        REAL_LT_IMP_NE, REAL_LT_IMP_NZ, REAL_LT_INV_EQ, REAL_LT_LE, REAL_LT_LMUL_EQ,
        REAL_LT_MUL, REAL_LT_REFL, .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_AC, REAL_MUL_LID, REAL_MUL_LNEG, REAL_MUL_LZERO, REAL_MUL_RNEG,
        REAL_MUL_RZERO, REAL_NEG_0, REAL_NEG_ADD, REAL_NEG_EQ_0, REAL_NEG_NEG, REAL_NOT_LE,
        REAL_NOT_LT, REAL_OF_NUM_ADD, REAL_OF_NUM_EQ, REAL_OF_NUM_MUL, REAL_POS,
        REAL_WLOG_LE, RIGHT_FORALL_IMP_THM, SQRT_POS_LE, SQRT_POW_2,
        .. } := D.cn.cx.cvx.core5
  let { real_abs, real_div, real_pow, .. } := D.cn.cx.cvx.core6
  let { REAL_ABS_NZ, REAL_INV_INV, .. } := D.cn.ms.ig.dv.qsession
  let { NOT_ODD, REAL_POW_NEG, .. } := D.cn.ms.ig.dv.dg.qsession
  let { REAL_LT_RMUL, .. } := D.cn.ms.ig.dv.dg.pt.qses
  -- @@SCOPE END

  parse_as_infix ("rpow", (24, "left"))

  let rpow ← new_definition
    r"x rpow y = if &0 < x then exp(y * log x)
               else if x = &0 then if y = &0 then &1 else &0
               else if ?m n. ODD(m) /\ ODD(n) /\ (abs y = &m / &n)
                    then --(exp(y * log(--x)))
                    else exp(y * log(--x))"

  let RPOW_POW ← prove
   r"!x n. x rpow &n = x pow n"
   (REPEAT GEN_TAC THEN REWRITE_TAC [rpow] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [REAL_EXP_N, EXP_LOG] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_POW_ZERO, REAL_OF_NUM_EQ] THEN
    ASM_SIMP_TAC [EXP_LOG, ← REAL_ARITH (← q r"~(&0 < x) /\ ~(x = &0) ==> &0 < --x")] THEN
    REWRITE_TAC [REAL_POW_NEG, REAL_ABS_NUM] THEN
    SUBGOAL_THEN (← q r"(?p q. ODD(p) /\ ODD(q) /\ &n = &p / &q) <=> ODD n")
     (fun th => tactic_of do pure (SIMP_TAC [th, ← GSYM NOT_ODD, REAL_NEG_NEG, COND_ID])) THEN
    EQ_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THENL
     [REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"q = 0") THEN
      ASM_REWRITE_TAC [ARITH_ODD] THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ASM_SIMP_TAC [REAL_OF_NUM_EQ, ← REAL_FIELD
       (← q r"~(q = &0) ==> (n = p / q <=> q * n = p)")] THEN
      REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_EQ] THEN
      ASM_MESON_TAC [ODD_MULT],
      DISCH_TAC THEN MAP_EVERY EXISTS_TAC [← q r"n:num", ← q r"1"] THEN
      ASM_REWRITE_TAC [REAL_DIV_1, ARITH_ODD]])

  let RPOW_0 ← prove
   r"!x. x rpow &0 = &1"
   (REWRITE_TAC [RPOW_POW, real_pow])

  let RPOW_NEG ← prove
   r"!x y. x rpow (--y) = inv(x rpow y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [rpow] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_MUL_LNEG, REAL_EXP_NEG] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_NEG_EQ_0] THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_INV_0, REAL_INV_1],
      REWRITE_TAC [REAL_ABS_NEG] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_INV_NEG]])

  let RPOW_ZERO ← prove
   r"!y. &0 rpow y = if y = &0 then &1 else &0"
   (REWRITE_TAC [rpow, REAL_LT_REFL])

  let RPOW_POS_LT ← prove
   r"!x y. &0 < x ==> &0 < x rpow y"
   (SIMP_TAC [rpow, REAL_EXP_POS_LT])

  let RPOW_POS_LE ← prove
   r"!x y. &0 <= x ==> &0 <= x rpow y"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"x = &0") THENL
     [ASM_REWRITE_TAC [RPOW_ZERO] THEN MESON_TAC [REAL_POS],
      ASM_SIMP_TAC [RPOW_POS_LT, REAL_LE_LT]])

  let RPOW_LT2 ← prove
   r"!x y z. &0 <= x /\ x < y /\ &0 < z ==> x rpow z < y rpow z"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"x = &0") THEN
    ASM_SIMP_TAC [RPOW_ZERO, REAL_LT_IMP_NZ, RPOW_POS_LT] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [rpow] THEN
    ASM_CASES_TAC (← q r"&0 < x /\ &0 < y") THENL
     [ALL_TAC, MATCH_MP_TAC (← TAUT (← q r"F ==> p")) THEN ASM_REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC [REAL_EXP_MONO_LT, REAL_LT_LMUL_EQ] THEN
    MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC)

  let RPOW_LE2 ← prove
   r"!x y z. &0 <= x /\ x <= y /\ &0 <= z ==> x rpow z <= y rpow z"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"z = &0") THEN
    ASM_REWRITE_TAC [RPOW_POW, real_pow, REAL_LE_REFL] THEN
    ASM_CASES_TAC (← q r"x:real = y") THEN ASM_REWRITE_TAC [REAL_LE_REFL] THEN
    ASM_MESON_TAC [RPOW_LT2, REAL_LE_LT])

  let REAL_ABS_RPOW ← prove
   r"!x y. abs(x rpow y) = abs(x) rpow y"
   (REPEAT GEN_TAC THEN REWRITE_TAC [rpow] THEN
    ASM_CASES_TAC (← q r"x = &0") THEN ASM_REWRITE_TAC [REAL_ABS_NUM, REAL_LT_REFL] THENL
     [REAL_ARITH_TAC, ALL_TAC] THEN
    ASM_REWRITE_TAC [← GSYM REAL_ABS_NZ, REAL_ABS_ZERO] THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC [REAL_ABS_EXP, ← REAL_ARITH (← q r"&0 < x ==> abs x = x")] THEN
    COND_CASES_TAC THEN REWRITE_TAC [REAL_ABS_NEG, REAL_ABS_EXP] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC)

  let RPOW_ONE ← prove
   r"!z. &1 rpow z = &1"
   (REWRITE_TAC [rpow, REAL_LT_01, LOG_1, REAL_MUL_RZERO, REAL_EXP_0])

  let RPOW_RPOW ← prove
   r"!x y z. &0 <= x ==> x rpow y rpow z = x rpow (y * z)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [REAL_LE_LT] THEN
    ASM_CASES_TAC (← q r"x = &0") THEN ASM_REWRITE_TAC [] THENL
     [ASM_REWRITE_TAC [RPOW_ZERO, REAL_ENTIRE] THEN
      ASM_CASES_TAC (← q r"y = &0") THEN ASM_REWRITE_TAC [RPOW_ZERO, RPOW_ONE],
      SIMP_TAC [rpow, REAL_EXP_POS_LT, LOG_EXP] THEN
      REWRITE_TAC [REAL_MUL_AC]])

  let RPOW_LNEG ← prove
   r"!x y. --x rpow y =
         if ?m n. ODD m /\ ODD n /\ abs y = &m / &n
         then --(x rpow y) else x rpow y"
   (REPEAT GEN_TAC THEN REWRITE_TAC [rpow] THEN
    ASM_CASES_TAC (← q r"x = &0") THEN
    ASM_REWRITE_TAC [REAL_NEG_0, REAL_ABS_NUM, REAL_LT_REFL] THENL
     [ASM_CASES_TAC (← q r"y = &0") THEN ASM_REWRITE_TAC [REAL_NEG_0, COND_ID] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"abs(&0) = m / n <=> m * inv n = &0")] THEN
      SIMP_TAC [REAL_ENTIRE, REAL_INV_EQ_0, REAL_OF_NUM_EQ] THEN MESON_TAC [ODD],
      ASM_SIMP_TAC [← REAL_ARITH (← q r"~(x = &0) ==> (&0 < --x <=> ~(&0 < x))")] THEN
      ASM_REWRITE_TAC [REAL_NEG_EQ_0] THEN
      ASM_CASES_TAC (← q r"&0 < x") THEN ASM_REWRITE_TAC [REAL_NEG_NEG, COND_ID]])

  let RPOW_EQ_0 ← prove
   r"!x y. x rpow y = &0 <=> x = &0 /\ ~(y = &0)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [rpow] THEN
    ASM_CASES_TAC (← q r"x = &0") THEN ASM_REWRITE_TAC [REAL_LT_REFL] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_NEG_EQ_0, REAL_EXP_NZ]) THEN
    REAL_ARITH_TAC)

  let RPOW_MUL ← prove
   r"!x y z. (x * y) rpow z = x rpow z * y rpow z"
   (SUBGOAL_THEN
      (← q r"!x y z. &0 <= x /\ &0 <= y ==> (x * y) rpow z = x rpow z * y rpow z")
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC [REAL_LE_LT] THEN
      ASM_CASES_TAC (← q r"z = &0") THEN
      ASM_REWRITE_TAC [RPOW_POW, real_pow, REAL_MUL_LID] THEN
      ASM_CASES_TAC (← q r"x = &0") THEN ASM_REWRITE_TAC [REAL_MUL_LZERO, RPOW_ZERO] THEN
      ASM_CASES_TAC (← q r"y = &0") THEN ASM_REWRITE_TAC [REAL_MUL_RZERO, RPOW_ZERO] THEN
      SIMP_TAC [rpow, REAL_LT_MUL, LOG_MUL, REAL_ADD_LDISTRIB, REAL_EXP_ADD],
      REPEAT GEN_TAC THEN
      REPEAT_TCL DISJ_CASES_THEN (ANTE_RES_THEN (MP_TAC o SPEC (← q r"z:real")))
       (← REAL_ARITH (← q r"&0 <= x /\ &0 <= y \/ &0 <= x /\ &0 <= --y \/
                    &0 <= --x /\ &0 <= y \/ &0 <= --x /\ &0 <= --y")) THEN
      REWRITE_TAC [RPOW_LNEG, REAL_MUL_RNEG, REAL_MUL_LNEG] THEN
      COND_CASES_TAC THEN
      ASM_REWRITE_TAC [REAL_MUL_RNEG, REAL_MUL_LNEG, REAL_EQ_NEG2]])

  let RPOW_INV ← prove
   r"!x y. inv(x) rpow y = inv(x rpow y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [rpow, REAL_LT_INV_EQ] THEN
    SIMP_TAC [LOG_INV, REAL_MUL_RNEG, REAL_EXP_NEG] THEN
    COND_CASES_TAC THEN REWRITE_TAC [] THEN
    REWRITE_TAC [REAL_INV_EQ_0] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_INV_1, REAL_INV_0]) THEN
    ASM_SIMP_TAC [← GSYM REAL_INV_NEG, LOG_INV,
                  ← REAL_ARITH (← q r"~(&0 < x) /\ ~(x = &0) ==> &0 < --x")] THEN
    REWRITE_TAC [REAL_MUL_RNEG, REAL_EXP_NEG, REAL_INV_NEG])

  let REAL_INV_RPOW ← prove
   r"!x y. inv(x rpow y) = inv(x) rpow y"
   (REWRITE_TAC [RPOW_INV])

  let RPOW_DIV ← prove
   r"!x y z. (x / y) rpow z = x rpow z / y rpow z"
   (REWRITE_TAC [real_div, RPOW_MUL, RPOW_INV])

  let RPOW_PRODUCT ← prove
   r"!s:A->bool x y.
      FINITE s ==> (product s x) rpow y = product s (\i. x i rpow y)"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [PRODUCT_CLAUSES, RPOW_MUL, RPOW_ONE])

  let RPOW_ADD ← prove
   r"!x y z. &0 < x ==> x rpow (y + z) = x rpow y * x rpow z"
   (REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [rpow, REAL_ADD_RDISTRIB, REAL_EXP_ADD])

  let RPOW_SUB ← prove
   r"!x y z. &0 < x ==> x rpow (y - z) = x rpow y / x rpow z"
   (SIMP_TAC [real_sub, RPOW_ADD, RPOW_NEG, real_div])

  let RPOW_ADD_ALT ← prove
   r"!x y z. &0 <= x /\ (x = &0 /\ y + z = &0 ==> y = &0 \/ z = &0)
           ==> x rpow (y + z) = x rpow y * x rpow z"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"x = &0") THEN ASM_SIMP_TAC [REAL_LE_LT, RPOW_ADD] THEN
    REWRITE_TAC [RPOW_ZERO] THEN
    ASM_CASES_TAC (← q r"y = &0") THEN
    ASM_REWRITE_TAC [REAL_MUL_LID, REAL_ADD_LID] THEN
    ASM_CASES_TAC (← q r"y + z = &0") THEN ASM_REWRITE_TAC [] THEN
    ASM_REAL_ARITH_TAC)

  let RPOW_SUB_ALT ← prove
   r"!x y z. &0 <= x /\ (x = &0 /\ y = z ==> y = &0 \/ z = &0)
           ==> x rpow (y - z) = x rpow y / x rpow z"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [real_sub, real_div, ← GSYM RPOW_NEG] THEN
    MATCH_MP_TAC RPOW_ADD_ALT THEN ASM_REAL_ARITH_TAC)

  let RPOW_SQRT ← prove
   r"!x. &0 <= x ==> x rpow (&1 / &2) = sqrt x"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← REAL_RING
     (← q r"x pow 2 = y pow 2 /\ (x + y = &0 ==> x = &0 /\ y = &0)
      ==> x = y")) THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC [SQRT_POW_2] THEN
      ASM_SIMP_TAC [← GSYM RPOW_POW, RPOW_RPOW] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [RPOW_POW, REAL_POW_1],
      MATCH_MP_TAC (← REAL_ARITH
       (← q r"&0 <= x /\ &0 <= y ==> x + y = &0 ==> x = &0 /\ y = &0")) THEN
      ASM_SIMP_TAC [SQRT_POS_LE, RPOW_POS_LE]])

  let RPOW_MONO_LE ← prove
   r"!a b x. &1 <= x /\ a <= b ==> x rpow a <= x rpow b"
   (SIMP_TAC [rpow, ← REAL_ARITH (← q r"&1 <= x ==> &0 < x")] THEN
    SIMP_TAC [REAL_EXP_MONO_LE, LOG_POS, REAL_LE_RMUL])

  let RPOW_MONO_LT ← prove
   r"!a b x. &1 < x /\ a < b ==> x rpow a < x rpow b"
   (SIMP_TAC [rpow, ← REAL_ARITH (← q r"&1 < x ==> &0 < x")] THEN
    SIMP_TAC [REAL_EXP_MONO_LT, LOG_POS_LT, REAL_LT_RMUL])

  let RPOW_MONO_LE_EQ ← prove
   r"!a b x. &1 < x ==> (x rpow a <= x rpow b <=> a <= b)"
   (MESON_TAC [RPOW_MONO_LT, RPOW_MONO_LE, REAL_NOT_LT, REAL_LT_IMP_LE])

  let RPOW_MONO_LT_EQ ← prove
   r"!a b x. &1 < x ==> (x rpow a < x rpow b <=> a < b)"
   (SIMP_TAC [← GSYM REAL_NOT_LE, RPOW_MONO_LE_EQ])

  let RPOW_INJ ← prove
   r"!x y z. &0 < x ==> (x rpow y = x rpow z <=> x = &1 \/ y = z)"
   (REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (← REAL_ARITH (← q r"x = &1 \/ &1 < x \/ x < &1")) THEN
    ASM_SIMP_TAC [RPOW_ONE, REAL_LT_IMP_NE] THENL
     [ALL_TAC, GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_EQ_INV2]] THEN
    ASM_SIMP_TAC [REAL_INV_RPOW, ← GSYM REAL_LE_ANTISYM, RPOW_MONO_LE_EQ,
                  REAL_INV_1_LT])

  let RPOW_LE_1 ← prove
   r"!x y. &1 <= x /\ &0 <= y ==> &1 <= x rpow y"
   (MESON_TAC [RPOW_0, RPOW_MONO_LE])

  let RPOW_LT_1 ← prove
   r"!x y. &1 < x /\ &0 < y ==> &1 < x rpow y"
   (MESON_TAC [RPOW_0, RPOW_MONO_LT])

  let RPOW_MONO_INV ← prove
   r"!a b x. &0 < x /\ x <= &1 /\ b <= a ==> x rpow a <= x rpow b"
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC BINOP_CONV [← GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_SIMP_TAC [REAL_LT_INV_EQ, RPOW_POS_LT, ← GSYM RPOW_INV] THEN
    MATCH_MP_TAC RPOW_MONO_LE THEN
    ASM_SIMP_TAC [REAL_INV_1_LE])

  let RPOW_1_LE ← prove
   r"!a x. &0 <= x /\ x <= &1 /\ &0 <= a ==> x rpow a <= &1"
   (REPEAT STRIP_TAC THEN  MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"&1 rpow a") THEN CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC,
      REWRITE_TAC [RPOW_ONE, REAL_LE_REFL]])

  let REAL_ROOT_RPOW ← prove
   r"!n x. ~(n = 0) /\ (&0 <= x \/ ODD n) ==> root n x = x rpow (inv(&n))"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"x = &0") THEN
    ASM_SIMP_TAC [ROOT_0, RPOW_ZERO, REAL_INV_EQ_0, REAL_OF_NUM_EQ] THEN
    ASM_CASES_TAC (← q r"&0 <= x") THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THENL
     [ASM_SIMP_TAC [ROOT_EXP_LOG, rpow, REAL_LT_LE] THEN AP_TERM_TAC THEN
      REAL_ARITH_TAC,
      ASM_REWRITE_TAC [rpow] THEN COND_CASES_TAC THENL
       [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      REWRITE_TAC [REAL_ABS_INV, REAL_ABS_NUM] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"inv x = &1 / x")] THEN
      COND_CASES_TAC THENL [ALL_TAC, ASM_MESON_TAC [ARITH]] THEN
      MATCH_MP_TAC ROOT_UNIQUE THEN
      ASM_REWRITE_TAC [REAL_POW_NEG, ← GSYM REAL_EXP_N, ← GSYM NOT_ODD] THEN
      ASM_SIMP_TAC [REAL_OF_NUM_EQ, ← REAL_FIELD
        (← q r"~(n = &0) ==> n * &1 / n * x = x")] THEN
      ONCE_REWRITE_TAC [← REAL_ARITH (← q r"--x:real = y <=> x = --y")] THEN
      MATCH_MP_TAC EXP_LOG THEN ASM_REAL_ARITH_TAC])

  let LOG_RPOW ← prove
   r"!x y. &0 < x ==> log(x rpow y) = y * log x"
   (SIMP_TAC [rpow, LOG_EXP])

  let LOG_SQRT ← prove
   r"!x. &0 < x ==> log(sqrt x) = log x / &2"
   (SIMP_TAC [← GSYM RPOW_SQRT, LOG_RPOW, REAL_LT_IMP_LE] THEN
    REAL_ARITH_TAC)

  let RPOW_ADD_INTEGER ← prove
   r"!x m n. integer m /\ integer n /\ ~(x = &0 /\ m + n = &0 /\ ~(n = &0))
            ==> x rpow (m + n) = x rpow m * x rpow n"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"x = &0") THENL
     [ASM_REWRITE_TAC [RPOW_ZERO] THEN REAL_ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [IMP_CONJ] THEN
    REWRITE_TAC [is_int, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"p:num") THEN DISCH_THEN (DISJ_CASES_THEN SUBST1_TAC) THEN
    X_GEN_TAC (← q r"q:num") THEN DISCH_THEN (DISJ_CASES_THEN SUBST1_TAC) THEN
    DISCH_THEN (K ALL_TAC) THEN
    REWRITE_TAC [← GSYM REAL_NEG_ADD, RPOW_NEG, RPOW_POW, REAL_OF_NUM_ADD,
                 REAL_POW_ADD, REAL_INV_MUL] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"--x + y:real = y - x"), ← GSYM real_sub] THEN
    REWRITE_TAC [REAL_OF_NUM_SUB_CASES] THEN COND_CASES_TAC THEN
    REWRITE_TAC [RPOW_NEG, RPOW_POW] THEN
    ASM_SIMP_TAC [REAL_POW_SUB, ← ARITH_RULE (← q r"~(p:num <= q) ==> q <= p")] THEN
    REWRITE_TAC [real_div, REAL_INV_MUL, REAL_INV_INV] THEN
    REAL_ARITH_TAC)

  let NORM_CPOW ← prove
   r"!w z. real w /\ &0 < Re w ==> norm(w cpow z) = norm(w) rpow (Re z)"
   (REPEAT GEN_TAC THEN
    SIMP_TAC [NORM_CPOW_REAL, rpow, COMPLEX_NORM_NZ] THEN
    ASM_CASES_TAC (← q r"w = Cx(&0)") THEN ASM_REWRITE_TAC [RE_CX, REAL_LT_REFL] THEN
    SIMP_TAC [REAL_NORM, real_abs, REAL_LT_IMP_LE])

  let REAL_MAX_RPOW ← prove
   r"!x y z. &0 <= x /\ &0 <= y /\ &0 <= z
           ==> max (x rpow z) (y rpow z) = (max x y) rpow z"
   (MATCH_MP_TAC REAL_WLOG_LE THEN CONJ_TAC THENL
     [MESON_TAC [← REAL_ARITH (← q r"max x y:real = max y x")], ALL_TAC] THEN
    SIMP_TAC [RPOW_LE2, ← REAL_ARITH (← q r"max x y:real = if x <= y then y else x")])

  let REAL_MIN_RPOW ← prove
   r"!x y z. &0 <= x /\ &0 <= y /\ &0 <= z
           ==> min (x rpow z) (y rpow z) = (min x y) rpow z"
   (MATCH_MP_TAC REAL_WLOG_LE THEN CONJ_TAC THENL
     [MESON_TAC [← REAL_ARITH (← q r"min x y:real = min y x")], ALL_TAC] THEN
    SIMP_TAC [RPOW_LE2, ← REAL_ARITH (← q r"min x y:real = if x <= y then x else y")])

  pure { rpow, RPOW_POW, RPOW_0, RPOW_NEG, RPOW_ZERO, RPOW_POS_LT, RPOW_POS_LE, RPOW_LT2,
         RPOW_LE2, REAL_ABS_RPOW, RPOW_ONE, RPOW_RPOW, RPOW_LNEG, RPOW_EQ_0, RPOW_MUL,
         RPOW_INV, REAL_INV_RPOW, RPOW_DIV, RPOW_PRODUCT, RPOW_ADD, RPOW_SUB,
         RPOW_ADD_ALT, RPOW_SUB_ALT, RPOW_SQRT, RPOW_MONO_LE, RPOW_MONO_LT,
         RPOW_MONO_LE_EQ, RPOW_MONO_LT_EQ, RPOW_INJ, RPOW_LE_1, RPOW_LT_1,
         RPOW_MONO_INV, RPOW_1_LE, REAL_ROOT_RPOW, LOG_RPOW, LOG_SQRT,
         RPOW_ADD_INTEGER, NORM_CPOW, REAL_MAX_RPOW, REAL_MIN_RPOW }
/- ------------------------------------------------------------------------- -/
/- Summability of zeta function series.                                      -/
/- (transcendentals.ml 6913-7005)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSAC where
  SUMMABLE_ZETA : thm
  SUMMABLE_ZETA_INTEGER : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSAC [HolBase] (D : TranscendentalsDeps) (BTSO : TSO) (BTSAB : TSAB) : ExceptT String IO TSAC := do
  -- @@SCOPE BEGIN
  let { CPOW_N, NORM_CPOW_REAL, .. } := BTSO
  let { REAL_INV_RPOW, rpow, RPOW_0, RPOW_ADD, RPOW_INV, RPOW_LE2, RPOW_LE_1, RPOW_LT_1,
        RPOW_MONO_LE, RPOW_NEG, RPOW_POS_LE, RPOW_POS_LT, RPOW_POW, RPOW_RPOW, .. } := BTSAB
  let { SERIES_CX_LIFT, .. } := D.knb
  let { SERIES_ABSCONV_IMP_CONV, .. } := D.knm
  let { SUMMABLE_EQ, SUMMABLE_FROM_ELSEWHERE, .. } := D.qtopology
  let { LT_POW2_REFL, SUM_ADD_SPLIT, .. } := D.qsession
  let { IN_FROM, .. } := D.qmisc
  let { CX_INJ, RE_CX, .. } := D.cn.cxc
  let { COMPLEX_NORM_INV, .. } := D.cn.cxf
  let { REAL_CX, .. } := D.cn.cxi
  let { summable, .. } := D.cn.qtopology
  let { FROM_INTER_NUMSEG, .. } := D.cn.ms.qmisc
  let { MULT_2, SUM_SING_NUMSEG, .. } := D.cn.ms.qsession
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_REAL_ARITH_TAC, INDUCT_TAC, MESON,
        REAL_ARITH, .. } := D.cn.cx.cvx
  let { LE_0, .. } := D.cn.cx.cpx
  let { CONVERGENT_BOUNDED_MONOTONE, SUM_GP, .. } := D.cn.ms.ig.qmisc
  let { SUM_CONST_NUMSEG, .. } := D.cn.ms.ig.qsession
  let { DIST_REAL, VSUM_REAL, .. } := D.cn.ms.ig.qvec
  let { ARITH, EXP, FINITE_NUMSEG, .. } := D.cn.cx.cvx.core1
  let { IMP_CONJ, .. } := D.cn.cx.cvx.core2
  let { LE_1, LE_REFL, LT_IMP_LE, REAL_DIV_1, .. } := D.cn.cx.cvx.core3
  let { REAL_INV_LE_1, REAL_INV_LT_1, REAL_INV_POW, REAL_LE_ADD2, REAL_LE_DIV,
        REAL_LE_INV2, REAL_LE_INV_EQ, REAL_LE_LMUL, REAL_LE_RMUL, REAL_LE_TRANS,
        .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_LZERO, REAL_MUL_SYM, REAL_NOT_LE, REAL_OF_NUM_EQ,
        REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_OF_NUM_POW, REAL_OF_NUM_SUC, REAL_POS,
        REAL_POW_2, REAL_POW_LE, REAL_POW_LT, REAL_SUB_LE, .. } := D.cn.cx.cvx.core5
  let { o_DEF, real_abs, real_div, real_pow, SUM_CLAUSES_NUMSEG, SUM_LE_NUMSEG, SUM_LMUL,
        SUM_SUBSET_SIMPLE, .. } := D.cn.cx.cvx.core6
  let { LIFT_DROP, .. } := D.cn.cx.cvx.vec2
  let { drop, .. } := D.cn.cx.cvx.vec4
  let { LIM_SEQUENTIALLY, .. } := D.cn.cx.cvx.top4
  let { sums, .. } := D.cn.ms.ig.dv.qtopology2
  let { LT, SUBSET_NUMSEG, SUM_POS_LE_NUMSEG, .. } := D.cn.ms.ig.dv.dg.qsession
  -- @@SCOPE END

  let SUMMABLE_ZETA ← prove
   r"!n z. &1 < Re z ==> summable (from n) (\k. inv(Cx(&k) cpow z))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUMMABLE_FROM_ELSEWHERE THEN
    EXISTS_TAC (← q r"1") THEN MATCH_MP_TAC SERIES_ABSCONV_IMP_CONV THEN
    MATCH_MP_TAC SUMMABLE_EQ THEN EXISTS_TAC (← q r"\k. Cx(inv(&k rpow (Re z)))") THEN
    CONJ_TAC THENL
     [SIMP_TAC [IN_FROM, NORM_CPOW_REAL, REAL_CX, RE_CX, REAL_OF_NUM_LT, LE_1,
                COMPLEX_NORM_INV, rpow],
      POP_ASSUM MP_TAC THEN SPEC_TAC (← q r"Re z", ← q r"x:real")] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [summable] THEN
    MATCH_MP_TAC (← MESON [] (← q r"(?x. P(Cx x)) ==> ?x. P x")) THEN
    REWRITE_TAC [SERIES_CX_LIFT] THEN
    REWRITE_TAC [sums, FROM_INTER_NUMSEG, LIM_SEQUENTIALLY, DIST_REAL] THEN
    REWRITE_TAC [← GSYM drop, LIFT_DROP, VSUM_REAL, o_DEF] THEN
    MATCH_MP_TAC CONVERGENT_BOUNDED_MONOTONE THEN
    EXISTS_TAC (← q r"&2 rpow x / (&1 - (&1 / &2) rpow (x - &1))") THEN CONJ_TAC THENL
     [ALL_TAC,
      DISJ1_TAC THEN MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"j:num"] THEN DISCH_TAC THEN
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      SIMP_TAC [REAL_LE_INV_EQ, RPOW_POS_LE, REAL_POS] THEN
      REWRITE_TAC [FINITE_NUMSEG, SUBSET_NUMSEG] THEN ASM_ARITH_TAC] THEN
    X_GEN_TAC (← q r"n:num") THEN
    TRANS_TAC REAL_LE_TRANS (← q r"sum(1..2 EXP n) (\k. inv(&k rpow x))") THEN
    CONJ_TAC THENL
     [SIMP_TAC [SUM_POS_LE_NUMSEG, REAL_LE_INV_EQ, RPOW_POS_LE, REAL_POS,
                real_abs] THEN
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      SIMP_TAC [REAL_LE_INV_EQ, RPOW_POS_LE, REAL_POS] THEN
      SIMP_TAC [FINITE_NUMSEG, SUBSET_NUMSEG, LE_REFL,
                LT_POW2_REFL, LT_IMP_LE],
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     (← q r"sum(0..n) (\k. &2 rpow x / &2 rpow (&k * (x - &1)))") THEN
    CONJ_TAC THENL
     [SPEC_TAC (← q r"n:num", ← q r"n:num") THEN INDUCT_TAC THENL
       [REWRITE_TAC [EXP, SUM_SING_NUMSEG, REAL_MUL_LZERO, RPOW_0, REAL_INV_RPOW,
                     REAL_DIV_1] THEN
        MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      MP_TAC (← ISPECL
       [← q r"\k. inv(&k rpow x)", ← q r"1", ← q r"2 EXP n", ← q r"2 EXP n"]
          SUM_ADD_SPLIT) THEN
      ANTS_TAC THENL [ARITH_TAC, REWRITE_TAC [MULT_2, EXP]] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [SUM_CLAUSES_NUMSEG, LE_0] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC [] THEN
      TRANS_TAC REAL_LE_TRANS
       (← q r"sum (2 EXP n + 1..2 EXP n + 2 EXP n) (\k. inv(&2 pow n rpow x))") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
        REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        ASM_SIMP_TAC [REAL_POW_LT, REAL_OF_NUM_LT, ARITH, RPOW_POS_LT] THEN
        MATCH_MP_TAC RPOW_LE2 THEN
        ASM_SIMP_TAC [RPOW_POW, REAL_OF_NUM_POW, REAL_OF_NUM_LE, LE_0] THEN
        ASM_ARITH_TAC,
        REWRITE_TAC [SUM_CONST_NUMSEG, ← ARITH_RULE (← q r"((n + n) + 1) - (n + 1) = n"),
                     ← GSYM REAL_OF_NUM_POW, REAL_INV_POW, REAL_POW_2] THEN
        REWRITE_TAC [real_div, ← GSYM RPOW_NEG] THEN
        SIMP_TAC [← GSYM RPOW_POW, RPOW_RPOW, REAL_POS, ← GSYM RPOW_ADD,
                  REAL_OF_NUM_LT, ARITH] THEN
        MATCH_MP_TAC RPOW_MONO_LE THEN REWRITE_TAC [← GSYM REAL_OF_NUM_SUC] THEN
        ASM_REAL_ARITH_TAC],
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      SIMP_TAC [← GSYM RPOW_RPOW, REAL_POS, real_div, RPOW_POW] THEN
      REWRITE_TAC [REAL_INV_POW, SUM_LMUL] THEN REWRITE_TAC [SUM_GP] THEN
      REWRITE_TAC [← CONJUNCT1 LT, ← CONJUNCT1 real_pow] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC [RPOW_POS_LE, REAL_POS] THEN
      COND_CASES_TAC THENL
       [MATCH_MP_TAC (← TAUT (← q r"F ==> p")) THEN
        FIRST_X_ASSUM (MP_TAC o MATCH_MP (← REAL_ARITH (← q r"x = &1 ==> &1 <= x"))) THEN
        REWRITE_TAC [REAL_NOT_LE] THEN MATCH_MP_TAC REAL_INV_LT_1 THEN
        MATCH_MP_TAC RPOW_LT_1 THEN ASM_REAL_ARITH_TAC,
        REWRITE_TAC [REAL_MUL_LID, RPOW_INV] THEN
        REWRITE_TAC [← REAL_ARITH (← q r"a / b <= inv b <=> a * inv b <= &1 * inv b")] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN
        REWRITE_TAC [← REAL_ARITH (← q r"&1 - x <= &1 <=> &0 <= x"), REAL_LE_INV_EQ] THEN
        SIMP_TAC [REAL_POW_LE, REAL_LE_DIV, REAL_POS, REAL_SUB_LE,
                  RPOW_POS_LE, REAL_LE_INV_EQ] THEN
        MATCH_MP_TAC REAL_INV_LE_1 THEN
        MATCH_MP_TAC RPOW_LE_1 THEN ASM_REAL_ARITH_TAC]])

  let SUMMABLE_ZETA_INTEGER ← prove
   r"!n m. 2 <= m ==> summable (from n) (\k. inv(Cx(&k) pow m))"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUMMABLE_FROM_ELSEWHERE THEN EXISTS_TAC (← q r"1") THEN
    MP_TAC (← SPECL [← q r"1", ← q r"Cx(&m)"] SUMMABLE_ZETA) THEN
    ASM_SIMP_TAC [RE_CX, REAL_OF_NUM_LT, ← ARITH_RULE (← q r"2 <= n ==> 1 < n")] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] SUMMABLE_EQ) THEN
    SIMP_TAC [IN_FROM, CPOW_N, CX_INJ, REAL_OF_NUM_EQ, LE_1])

  pure { SUMMABLE_ZETA, SUMMABLE_ZETA_INTEGER }
/- ------------------------------------------------------------------------- -/
/- Formulation of loop homotopy in terms of maps out of S^1                  -/
/- (transcendentals.ml 7006-7259)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSAD where
  HOMOTOPIC_CIRCLEMAPS_IMP_HOMOTOPIC_LOOPS : thm
  HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_CIRCLEMAPS : thm
  SIMPLY_CONNECTED_EQ_HOMOTOPIC_CIRCLEMAPS : thm
  SIMPLY_CONNECTED_EQ_CONTRACTIBLE_CIRCLEMAP : thm
  HOMOTOPY_EQUIVALENT_SIMPLE_CONNECTEDNESS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSAD [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) (BTSE : TSE) (BTSF : TSF) (BTSH : TSH) (BTSZ : TSZ) : ExceptT String IO TSAD := do
  -- @@SCOPE BEGIN
  let { CONTINUOUS_ON_CEXP, .. } := BTSA
  let { PI_NZ, PI_POS, .. } := BTSE
  let { CEXP_INTEGER_2PI, NORM_CEXP_II, .. } := BTSF
  let { ARG, ARG_CEXP, ARG_CNJ, ARG_EQ_0_PI, ARG_NUM, .. } := BTSH
  let { CONTINUOUS_ON_UPPERHALF_ARG, .. } := BTSZ
  let { CLOSED_HALFSPACE_IM_GE, CLOSED_HALFSPACE_IM_LE, .. } := D.kna
  let { CONTINUOUS_ON_COMPLEX_MUL, .. } := D.knc
  let { CONTINUOUS_ON_CX_DROP, CONTINUOUS_ON_CX_LIFT, .. } := D.knd
  let { CONTINUOUS_ON_CNJ, .. } := D.knm
  let { CLOSED_PCROSS, sphere, .. } := D.qtopology
  let { homotopic_loops, HOMOTOPIC_LOOPS_EQ, HOMOTOPIC_LOOPS_REFL, HOMOTOPIC_LOOPS_TRANS,
        HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT, HOMOTOPY_EQUIVALENT_HOMOTOPIC_TRIVIALITY,
        LINEPATH_REFL, PATH_CONNECTED_EQ_HOMOTOPIC_POINTS, simply_connected,
        SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_SOME, .. } := D.qpaths
  let { COMPLEX_MUL_LID, COMPLEX_MUL_SYM, .. } := D.cn.cxb
  let { COMPLEX_NORM_CX, CX_MUL, IM_MUL_II, RE_CX, .. } := D.cn.cxc
  let { COMPLEX_NORM_0, .. } := D.cn.cxf
  let { CNJ_EQ_0, IM_CNJ, .. } := D.cn.cxg
  let { real, .. } := D.cn.cxi
  let { ASM_MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD, SET_RULE, SET_TAC,
        VECTOR_ARITH, .. } := D.cn.cx.cvx
  let { INTEGER_CLOSED, .. } := D.cn.ms.ig.qfloor
  let { AND_FORALL_THM, ARITH, ARITH_EQ, COND_ID, CONJ_ASSOC, EQ_TRANS, EXTENSION,
        .. } := D.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_IN_PCROSS, FORALL_PASTECART, FSTCART_PASTECART, IMP_CONJ,
        IMP_CONJ_ALT, IN_DIFF, .. } := D.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INTER, IN_SING, IN_UNION, IN_UNIV, LEFT_IMP_EXISTS_THM,
        MONO_EXISTS, PASTECART_IN_PCROSS, REAL_ABS_NUM, REAL_DIV_REFL,
        .. } := D.cn.cx.cvx.core3
  let { REAL_ENTIRE, REAL_LE_ANTISYM, REAL_LE_LDIV_EQ, REAL_LE_MUL, REAL_LE_RDIV_EQ,
        REAL_LE_REFL, REAL_LE_TOTAL, REAL_LT_IMP_LE, REAL_LT_LE, REAL_LT_LMUL_EQ,
        .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_LZERO, REAL_MUL_SYM, REAL_NEG_GE0, REAL_OF_NUM_EQ,
        REAL_OF_NUM_LT, REAL_POS, REAL_SUB_REFL, REAL_SUB_RZERO, SNDCART_PASTECART, SUBSET,
        .. } := D.cn.cx.cvx.core5
  let { o_ASSOC, o_DEF, o_THM, real_div, real_ge, .. } := D.cn.cx.cvx.core6
  let { DIST_0, .. } := D.cn.cx.cvx.vec1
  let { DROP_SUB, DROP_VEC, FORALL_LIFT, LIFT_CMUL, LIFT_DROP, LIFT_NUM, LIFT_SUB,
        LINEAR_FSTCART, LINEAR_SNDCART, .. } := D.cn.cx.cvx.vec2
  let { CLOSED_IN_CLOSED_INTER, CLOSED_UNIV, .. } := D.cn.cx.cvx.top1
  let { CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_CONST, CONTINUOUS_ON_EQ, CONTINUOUS_ON_ID,
        CONTINUOUS_ON_SUB, CONTINUOUS_ON_SUBSET, .. } := D.cn.cx.cvx.top3
  let { IN_INTERVAL_1, IN_SPHERE_0, LINEAR_CONTINUOUS_ON, .. } := D.cn.cx.cvx.top4
  let { TOPSPACE_EUCLIDEAN_SUBTOPOLOGY, .. } := D.cn.cx.cvx.top5
  let { CONTINUOUS_ON_VMUL, .. } := D.cn.ms.ig.dv.qtopology1
  let { HOMOTOPIC_WITH_EQ, HOMOTOPIC_WITH_REFL, .. } := D.cn.ms.ig.dv.dg.qmetric
  let { HOMOTOPIC_WITH_EUCLIDEAN, HOMOTOPIC_WITH_EUCLIDEAN_ALT, HOMOTOPIC_WITH_IMP_SUBSET,
        .. } := D.cn.ms.ig.dv.dg.qpaths1
  let { pathfinish, pathstart, .. } := D.cn.ms.ig.dv.dg.qpaths2
  let { CONTINUOUS_MAP_EUCLIDEAN2, CONTINUOUS_ON_CASES_LOCAL, CONTINUOUS_ON_PASTECART,
        .. } := D.cn.ms.ig.dv.dg.qtopology1
  -- @@SCOPE END

  let HOMOTOPIC_CIRCLEMAPS_IMP_HOMOTOPIC_LOOPS ← prove
   r"!f:complex->real^N g s.
        homotopic_with (\h. T)
          (subtopology euclidean (sphere(vec 0,&1)),subtopology euclidean s)
          f g
        ==> homotopic_loops s (f o cexp o (\t. Cx(&2 * pi * drop t) * ii))
                              (g o cexp o (\t. Cx(&2 * pi * drop t) * ii))"
   (REWRITE_TAC [homotopic_loops, sphere, DIST_0] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
    EXISTS_TAC (← q r"{z:complex | norm z = &1}") THEN
    REWRITE_TAC [pathstart, pathfinish, o_THM, DROP_VEC] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"&2 * pi * n = &2 * n * pi")] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, o_THM, IN_ELIM_THM] THEN
    ASM_SIMP_TAC [CEXP_INTEGER_2PI, INTEGER_CLOSED] THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [COMPLEX_MUL_SYM] NORM_CEXP_II] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC [CONTINUOUS_ON_CEXP] THEN
    REWRITE_TAC [CX_MUL] THEN
    REPEAT (MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
            REWRITE_TAC [CONTINUOUS_ON_CONST]) THEN
    SIMP_TAC [CONTINUOUS_ON_CX_DROP, CONTINUOUS_ON_ID])

  let HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_CIRCLEMAPS ← (do
    let ulemma ← prove
     r"!s. s INTER (UNIV PCROSS {z | &0 <= Im z}) UNION
         s INTER (UNIV PCROSS {z | Im z <= &0}) = s"
     (REWRITE_TAC [EXTENSION, FORALL_PASTECART, IN_INTER, IN_UNION,
                   PASTECART_IN_PCROSS] THEN
      SET_TAC [REAL_LE_TOTAL])
    prove
     r"!p q s:real^N->bool.
        homotopic_loops s p q
        ==> homotopic_with (\h. T)
             (subtopology euclidean (sphere(vec 0,&1)),subtopology euclidean s)
                                   (p o (\z. lift(Arg z / (&2 * pi))))
                                   (q o (\z. lift(Arg z / (&2 * pi))))"
     (REPEAT GEN_TAC THEN REWRITE_TAC [homotopic_loops, sphere, DIST_0] THEN
      GEN_REWRITE_TAC LAND_CONV [HOMOTOPIC_WITH_EUCLIDEAN] THEN
      SIMP_TAC [pathstart, pathfinish, LEFT_IMP_EXISTS_THM,
                HOMOTOPIC_WITH_EUCLIDEAN_ALT] THEN
      X_GEN_TAC (← q r"h:real^(1,1)finite_sum->real^N") THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"\w. (h:real^(1,1)finite_sum->real^N)
                      (pastecart (fstcart w)
                                 (lift(Arg(sndcart w) / (&2 * pi))))") THEN
      ASM_REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART, o_THM] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
        EXISTS_TAC
         (← q r"(\z. if &0 <= Im(sndcart z)
               then h (pastecart (fstcart z) (lift(Arg(sndcart z) / (&2 * pi))))
               else h (pastecart (fstcart z)
                                 (vec 1 - lift(Arg(cnj(sndcart z)) / (&2 * pi)))))
          :real^(1,2)finite_sum->real^N") THEN
        REWRITE_TAC [FORALL_IN_PCROSS, FSTCART_PASTECART, SNDCART_PASTECART] THEN
        REWRITE_TAC [IN_ELIM_THM] THEN CONJ_TAC THENL
         [MAP_EVERY X_GEN_TAC [← q r"t:real^1", ← q r"z:complex"] THEN STRIP_TAC THEN
          COND_CASES_TAC THEN ASM_REWRITE_TAC [ARG_CNJ] THEN
          COND_CASES_TAC THENL [ASM_MESON_TAC [real, REAL_LE_REFL], ALL_TAC] THEN
          SIMP_TAC [PI_POS, LIFT_SUB, LIFT_NUM, ← REAL_FIELD
            (← q r"&0 < pi ==> (&2 * pi - z) / (&2 * pi) = &1 - z / (&2 * pi)")] THEN
          REWRITE_TAC [← VECTOR_ARITH (← q r"a - (a - b):real^N = b")],
          GEN_REWRITE_TAC RAND_CONV [← GSYM ulemma] THEN
          MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN REWRITE_TAC [ulemma] THEN
          SIMP_TAC [CLOSED_IN_CLOSED_INTER, CLOSED_HALFSPACE_IM_LE, CLOSED_UNIV,
            CLOSED_PCROSS, ← REWRITE_RULE [real_ge] CLOSED_HALFSPACE_IM_GE] THEN
          REWRITE_TAC [FORALL_PASTECART, PASTECART_IN_PCROSS, IN_INTER, IN_DIFF,
           FSTCART_PASTECART, SNDCART_PASTECART, IN_UNIV, IN_SING, IN_ELIM_THM,
           ← GSYM CONJ_ASSOC, REAL_LE_ANTISYM, ← TAUT (← q r"~(p /\ ~p)")] THEN
          REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL
           [ALL_TAC,
            REWRITE_TAC [← GSYM ARG_EQ_0_PI, ← GSYM real, ARG_CNJ] THEN
            REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
            SIMP_TAC [← REAL_ARITH (← q r"&2 * x - x = x"), COND_ID, ← GSYM LIFT_NUM, PI_POS,
             ← GSYM LIFT_SUB, ← REAL_FIELD
              (← q r"&0 < pi ==> &1 - pi / (&2 * pi) = pi / (&2 * pi)")] THEN
            COND_CASES_TAC THEN
            SIMP_TAC [REAL_SUB_RZERO, REAL_DIV_REFL, REAL_ENTIRE, REAL_OF_NUM_EQ,
                      ARITH_EQ, PI_NZ] THEN
            SIMP_TAC [real_div, REAL_MUL_LZERO, REAL_SUB_REFL, REAL_SUB_RZERO] THEN
            ASM_SIMP_TAC [LIFT_NUM]] THEN
          GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV) [← GSYM o_DEF] THEN
          CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
           [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
            SIMP_TAC [LINEAR_CONTINUOUS_ON, LINEAR_FSTCART] THEN
            REWRITE_TAC [real_div, ← REWRITE_RULE [REAL_MUL_SYM] LIFT_CMUL] THEN
            MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
            GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM o_DEF] THEN
            REWRITE_TAC [o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
            SIMP_TAC [LINEAR_CONTINUOUS_ON, LINEAR_SNDCART] THEN
            REWRITE_TAC [o_DEF, ← GSYM CONTINUOUS_ON_CX_LIFT] THEN
            MP_TAC CONTINUOUS_ON_UPPERHALF_ARG THEN REWRITE_TAC [o_DEF] THEN
            MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] CONTINUOUS_ON_SUBSET) THEN
            REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_PASTECART, IN_INTER,
                         PASTECART_IN_PCROSS, IN_ELIM_THM, SNDCART_PASTECART] THEN
            MAP_EVERY X_GEN_TAC [← q r"t:real^1", ← q r"z:complex"] THEN
            SIMP_TAC [IN_DIFF, IN_ELIM_THM, IN_SING] THEN
            ASM_CASES_TAC (← q r"z = Cx(&0)") THEN ASM_REWRITE_TAC [COMPLEX_NORM_0] THEN
            REWRITE_TAC [REAL_OF_NUM_EQ, ARITH_EQ],
            FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
              CONTINUOUS_ON_SUBSET)) THEN
            REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_PASTECART, IN_INTER,
                         PASTECART_IN_PCROSS, IN_ELIM_THM, SNDCART_PASTECART,
                         FSTCART_PASTECART] THEN
            SIMP_TAC [IN_INTERVAL_1, LIFT_DROP, DROP_VEC] THEN
            SIMP_TAC [REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ, PI_POS, REAL_MUL_LZERO,
                 REAL_MUL_LID, ← REAL_ARITH (← q r"&0 < &2 * x <=> &0 < x")] THEN
            SIMP_TAC [ARG, REAL_LT_IMP_LE],
            MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
            SIMP_TAC [LINEAR_CONTINUOUS_ON, LINEAR_FSTCART] THEN
            MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
            REWRITE_TAC [CONTINUOUS_ON_CONST] THEN
            REWRITE_TAC [real_div, ← REWRITE_RULE [REAL_MUL_SYM] LIFT_CMUL] THEN
            MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
            GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM o_DEF] THEN
            REWRITE_TAC [o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
            GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [← GSYM o_DEF] THEN
            SIMP_TAC [LINEAR_CONTINUOUS_ON, LINEAR_SNDCART, CONTINUOUS_ON_COMPOSE,
                      CONTINUOUS_ON_CNJ] THEN
            REWRITE_TAC [o_DEF, ← GSYM CONTINUOUS_ON_CX_LIFT] THEN
            MP_TAC CONTINUOUS_ON_UPPERHALF_ARG THEN REWRITE_TAC [o_DEF] THEN
            MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] CONTINUOUS_ON_SUBSET) THEN
            REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_PASTECART, IN_INTER,
                         PASTECART_IN_PCROSS, IN_ELIM_THM, SNDCART_PASTECART] THEN
            MAP_EVERY X_GEN_TAC [← q r"t:real^1", ← q r"z:complex"] THEN
            SIMP_TAC [IN_DIFF, IN_ELIM_THM, IN_SING] THEN
            SIMP_TAC [IM_CNJ, REAL_NEG_GE0, CNJ_EQ_0] THEN
            ASM_CASES_TAC (← q r"z = Cx(&0)") THEN ASM_REWRITE_TAC [COMPLEX_NORM_0] THEN
            REWRITE_TAC [REAL_OF_NUM_EQ, ARITH_EQ],
            FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
              CONTINUOUS_ON_SUBSET)) THEN
            REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_PASTECART, IN_INTER,
                         PASTECART_IN_PCROSS, IN_ELIM_THM, SNDCART_PASTECART,
                         FSTCART_PASTECART] THEN
            SIMP_TAC [IN_INTERVAL_1, DROP_SUB, DROP_VEC, LIFT_DROP] THEN
            REWRITE_TAC [← REAL_ARITH (← q r"&0 <= &1 - x /\ &1 - x <= &1 <=>
                                    &0 <= x /\ x <= &1")] THEN
            SIMP_TAC [REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ, PI_POS, REAL_MUL_LZERO,
                 REAL_MUL_LID, ← REAL_ARITH (← q r"&0 < &2 * x <=> &0 < x")] THEN
            SIMP_TAC [ARG, REAL_LT_IMP_LE]]],
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_IN_PCROSS, IN_ELIM_THM] THEN
        REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART] THEN
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
         (← q r"IMAGE h s SUBSET t ==> y IN s ==> h y IN t"))) THEN
        ASM_REWRITE_TAC [PASTECART_IN_PCROSS, IN_INTERVAL_1, LIFT_DROP] THEN
        SIMP_TAC [DROP_VEC, REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ, PI_POS,
                  ← REAL_ARITH (← q r"&0 < &2 * x <=> &0 < x")] THEN
        SIMP_TAC [REAL_MUL_LZERO, REAL_MUL_LID, ARG, REAL_LT_IMP_LE]]))

  let (SIMPLY_CONNECTED_EQ_HOMOTOPIC_CIRCLEMAPS,
       SIMPLY_CONNECTED_EQ_CONTRACTIBLE_CIRCLEMAP) ← CONJ_PAIR (← prove
   r"(!s:real^N->bool.
        simply_connected s <=>
        !f g:complex->real^N.
              f continuous_on sphere(vec 0,&1) /\
              IMAGE f (sphere(vec 0,&1)) SUBSET s /\
              g continuous_on sphere(vec 0,&1) /\
              IMAGE g (sphere(vec 0,&1)) SUBSET s
              ==> homotopic_with (\h. T)
                   (subtopology euclidean (sphere(vec 0,&1)),
                    subtopology euclidean s) f g) /\
   (!s:real^N->bool.
      simply_connected s <=>
      path_connected s /\
      !f:real^2->real^N.
              f continuous_on sphere(vec 0,&1) /\
              IMAGE f (sphere(vec 0,&1)) SUBSET s
              ==> ?a. homotopic_with (\h. T)
                       (subtopology euclidean (sphere(vec 0,&1)),
                        subtopology euclidean s) f (\x. a))"
   (REWRITE_TAC [AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC (← TAUT
     (← q r"(p ==> q) /\ (q ==> r) /\ (r ==> p) ==> (p <=> q) /\ (p <=> r)")) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [simply_connected] THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [← q r"f:complex->real^N", ← q r"g:complex->real^N"] THEN
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPECL
       [← q r"(f:complex->real^N) o cexp o (\t. Cx(&2 * pi * drop t) * ii)",
        ← q r"(g:complex->real^N) o cexp o (\t. Cx(&2 * pi * drop t) * ii)"]) THEN
      ONCE_REWRITE_TAC [← TAUT (← q r"p1 /\ q1 /\ r1 /\ p2 /\ q2 /\ r2 <=>
                             (p1 /\ r1 /\ q1) /\ (p2 /\ r2 /\ q2)")] THEN
      REWRITE_TAC [← GSYM HOMOTOPIC_LOOPS_REFL] THEN
      ASM_SIMP_TAC [HOMOTOPIC_CIRCLEMAPS_IMP_HOMOTOPIC_LOOPS,
                    HOMOTOPIC_WITH_REFL, CONTINUOUS_MAP_EUCLIDEAN2] THEN
      DISCH_THEN (MP_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_CIRCLEMAPS) THEN
      MATCH_MP_TAC (← ONCE_REWRITE_RULE [IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
      REWRITE_TAC [TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      REWRITE_TAC [IN_SPHERE_0, LIFT_DROP, o_DEF] THEN X_GEN_TAC (← q r"z:complex") THEN
      REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MP_TAC (← SPEC (← q r"z:complex") ARG) THEN
      ASM_REWRITE_TAC [COMPLEX_MUL_LID] THEN
      DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN SIMP_TAC [PI_POS,
        ← REAL_FIELD (← q r"&0 < pi ==> &2 * pi * x / (&2 * pi) = x")] THEN
      ASM_MESON_TAC [COMPLEX_MUL_SYM],
      DISCH_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC [PATH_CONNECTED_EQ_HOMOTOPIC_POINTS] THEN
        MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"b:real^N"] THEN STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPECL
         [← q r"(\x. a):complex->real^N", ← q r"(\x. b):complex->real^N"]) THEN
        REWRITE_TAC [CONTINUOUS_ON_CONST] THEN
        ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN DISCH_THEN
         (MP_TAC o MATCH_MP HOMOTOPIC_CIRCLEMAPS_IMP_HOMOTOPIC_LOOPS) THEN
        REWRITE_TAC [o_DEF, LINEPATH_REFL],
        X_GEN_TAC (← q r"f:complex->real^N") THEN STRIP_TAC THEN
        EXISTS_TAC (← q r"f(Cx(&1)):real^N") THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC [CONTINUOUS_ON_CONST] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [SUBSET, FORALL_IN_IMAGE, IN_SPHERE_0]) THEN
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_SPHERE_0] THEN
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC [COMPLEX_NORM_CX] THEN REAL_ARITH_TAC],
      STRIP_TAC THEN
      ASM_REWRITE_TAC [SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_SOME] THEN
      X_GEN_TAC (← q r"p:real^1->real^N") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC
       (← q r"(p:real^1->real^N) o (\z. lift(Arg z / (&2 * pi)))")) THEN
      ANTS_TAC THENL
       [MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"p:real^1->real^N"]
          HOMOTOPIC_LOOPS_REFL) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o MATCH_MP
          HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_CIRCLEMAPS) THEN
        SIMP_TAC [HOMOTOPIC_WITH_REFL, CONTINUOUS_MAP_EUCLIDEAN2],
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:real^N") THEN
        STRIP_TAC THEN FIRST_ASSUM
         (MP_TAC o MATCH_MP HOMOTOPIC_CIRCLEMAPS_IMP_HOMOTOPIC_LOOPS) THEN
        FIRST_ASSUM (MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_SPHERE_0, o_DEF] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"Cx(&1)") o CONJUNCT2) THEN
        REWRITE_TAC [COMPLEX_NORM_CX, REAL_ABS_NUM] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC [LINEPATH_REFL] THEN
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] HOMOTOPIC_LOOPS_TRANS) THEN
        MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [IN_INTERVAL_1, FORALL_LIFT, LIFT_DROP, DROP_VEC] THEN
        X_GEN_TAC (← q r"t:real") THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"t = &1") THENL
         [ASM_REWRITE_TAC [← REAL_ARITH (← q r"&2 * pi * &1 = &2 * &1 * pi")] THEN
          SIMP_TAC [CEXP_INTEGER_2PI, INTEGER_CLOSED, ARG_NUM] THEN
          REWRITE_TAC [real_div, REAL_MUL_LZERO, LIFT_NUM] THEN
          ASM_MESON_TAC [pathstart, pathfinish],
          AP_TERM_TAC THEN AP_TERM_TAC THEN SIMP_TAC [PI_POS, ← REAL_FIELD
           (← q r"&0 < pi ==> (t = x / (&2 * pi) <=> x = &2 * pi * t)")] THEN
          MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"Im(Cx (&2 * pi * t) * ii)") THEN
          CONJ_TAC THENL [MATCH_MP_TAC ARG_CEXP, ALL_TAC] THEN
          SIMP_TAC [IM_MUL_II, RE_CX, ← REAL_ARITH
            (← q r"a < &2 * pi <=> a < &2 * pi * &1")] THEN
          ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_LMUL_EQ, REAL_OF_NUM_LT, ARITH,
                        PI_POS, REAL_LT_IMP_LE, REAL_POS, REAL_LE_MUL] THEN
          ASM_REWRITE_TAC [REAL_LT_LE]]]]))

  let HOMOTOPY_EQUIVALENT_SIMPLE_CONNECTEDNESS ← prove
   r"!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t
        ==> (simply_connected s <=> simply_connected t)"
   (REWRITE_TAC [SIMPLY_CONNECTED_EQ_HOMOTOPIC_CIRCLEMAPS] THEN
    REWRITE_TAC [HOMOTOPY_EQUIVALENT_HOMOTOPIC_TRIVIALITY])

  pure { HOMOTOPIC_CIRCLEMAPS_IMP_HOMOTOPIC_LOOPS, HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_CIRCLEMAPS,
         SIMPLY_CONNECTED_EQ_HOMOTOPIC_CIRCLEMAPS,
         SIMPLY_CONNECTED_EQ_CONTRACTIBLE_CIRCLEMAP,
         HOMOTOPY_EQUIVALENT_SIMPLE_CONNECTEDNESS }
/- ------------------------------------------------------------------------- -/
/- Integration via polar coordinates (1).                                    -/
/- (transcendentals.ml 7260-7398)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSAE where
  HAS_DERIVATIVE_POLAR : thm
  HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES_POLAR : thm
  ABSOLUTELY_INTEGRABLE_CHANGE_OF_VARIABLES_POLAR : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSAE [HolBase] (D : TranscendentalsDeps) (BTSA : TSA) (BTSB : TSB) (BTSC : TSC) (BTSE : TSE) (BTSF : TSF) (BTSH : TSH) : ExceptT String IO TSAE := do
  -- @@SCOPE BEGIN
  let { HAS_COMPLEX_DERIVATIVE_CEXP, .. } := BTSA
  let { REAL_EXP_0, REAL_EXP_NZ, .. } := BTSB
  let { IM_CEXP, RE_CEXP, SIN_CIRCLE, SIN_SUB, .. } := BTSC
  let { CEXP_II_PI, COS_PI, SIN_EQ_0_PI, SIN_PI, .. } := BTSE
  let { NORM_CEXP_II, .. } := BTSF
  let { ARG, ARG_CEXP, ARG_EQ_0, ARG_MUL_CX, .. } := BTSH
  let { LINEAR_CX_IM, LINEAR_CX_RE, .. } := D.knd
  let { has_complex_derivative, .. } := D.kne
  let { CONVEX_HALFSPACE_COMPONENT_GT, CONVEX_HALFSPACE_COMPONENT_LT, .. } := D.qconvex
  let { HAS_DERIVATIVE_BILINEAR_AT, .. } := D.qderivatives
  let { HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES, LEBESGUE_MEASURABLE_CONVEX,
        LEBESGUE_MEASURABLE_INTER, .. } := D.qmeasure
  let { ABSOLUTELY_INTEGRABLE_SPIKE_EQ, .. } := D.qintegration
  let { COMPLEX_EQ, IM, IM_DEF, RE, RE_DEF, .. } := D.cn.cxa
  let { COMPLEX_NORM_CX, IM_ADD, IM_CX, IM_II, IM_MUL_CX, IM_MUL_II, RE_ADD, RE_CX, RE_II,
        RE_MUL_CX, RE_MUL_II, RE_NEG, .. } := D.cn.cxc
  let { COMPLEX_RING, .. } := D.cn.cxd
  let { COMPLEX_NORM_MUL, COMPLEX_NORM_NZ, .. } := D.cn.cxf
  let { BILINEAR_COMPLEX_MUL, LINEAR_COMPLEX_LMUL, .. } := D.cn.cxh
  let { real, .. } := D.cn.cxi
  let { DIFF_CHAIN_AT, .. } := D.cn.qderivatives
  let { HAS_DERIVATIVE_AT_WITHIN, HAS_DERIVATIVE_LINEAR, .. } := D.cn.ms.qderivatives
  let { DET_2, .. } := D.cn.ms.qdet
  let { ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV, .. } := D.cn.ms.qintegration1
  let { INTEGRAL_RESTRICT_UNIV, INTEGRAL_SPIKE, NEGLIGIBLE_STANDARD_HYPERPLANE,
        NEGLIGIBLE_UNION_EQ, .. } := D.cn.ms.qintegration3
  let { ASM_REAL_ARITH_TAC, MESON, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, SET_RULE,
        .. } := D.cn.cx.cvx
  let { FORALL_2, SUM_2, VECTOR_2, .. } := D.cn.cx.cpx
  let { CART_EQ, DE_MORGAN_THM, DIMINDEX_2, EQ_IMP, .. } := D.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, FUN_EQ_THM, IN_DIFF, .. } := D.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, IN_UNION, IN_UNIV, LAMBDA_BETA, .. } := D.cn.cx.cvx.core3
  let { REAL_ENTIRE, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_LE, REAL_LT_REFL,
        .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_LNEG, REAL_MUL_LZERO, REAL_MUL_RID, REAL_NEG_0, REAL_SUB_0,
        RIGHT_FORALL_IMP_THM, SUBSET, SUBSET_ANTISYM_EQ, .. } := D.cn.cx.cvx.core5
  let { o_DEF, real_gt, .. } := D.cn.cx.cvx.core6
  let { MATRIX_OF_MATRIX_VECTOR_MUL, .. } := D.cn.cx.cvx.vec2
  let { matrix_vector_mul, .. } := D.cn.cx.cvx.vec4
  -- @@SCOPE END

  let HAS_DERIVATIVE_POLAR ← prove
   r"!z. ((\w. Cx(Re w) * cexp(ii * Cx(Im w))) has_derivative
        (\h. vector[vector[cos(Im z); --Re(z) * sin(Im z)];
                    vector[sin(Im z); Re z * cos(Im z)]] ** h))
       (at z)"
   (X_GEN_TAC (← q r"z:complex") THEN
    MP_TAC (← ISPECL
     [← q r"\z. ii * Cx(Im z)", ← q r"cexp",
      ← q r"\z. ii * Cx(Im z)", ← q r"\h. cexp(ii * Cx(Im z)) * h", ← q r"z:complex"]
        DIFF_CHAIN_AT) THEN
    REWRITE_TAC [← GSYM has_complex_derivative, HAS_COMPLEX_DERIVATIVE_CEXP] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      MATCH_MP_TAC LINEAR_COMPLEX_LMUL THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM o_DEF] THEN
      REWRITE_TAC [LINEAR_CX_IM],
      REWRITE_TAC [o_DEF] THEN DISCH_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"complex_mul", ← q r"Cx o Re", ← q r"\z. cexp (ii * Cx (Im z))",
      ← q r"Cx o Re", ← q r"\x. cexp(ii * Cx (Im z)) * ii * Cx(Im x)",
      ← q r"z:complex"]
        HAS_DERIVATIVE_BILINEAR_AT) THEN
    SIMP_TAC [BILINEAR_COMPLEX_MUL, LINEAR_CX_RE, HAS_DERIVATIVE_LINEAR] THEN
    ASM_REWRITE_TAC [o_DEF] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"h:complex") THEN REWRITE_TAC [matrix_vector_mul] THEN
    SIMP_TAC [CART_EQ, LAMBDA_BETA] THEN
    SIMP_TAC [DIMINDEX_2, FORALL_2, SUM_2, VECTOR_2] THEN
    REWRITE_TAC [← GSYM IM_DEF, ← GSYM RE_DEF] THEN
    REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"a * e * ii * z:complex = a * ii * z * e"))] THEN
    REWRITE_TAC [RE_ADD, IM_ADD, RE_MUL_CX, IM_MUL_CX, RE_CEXP, IM_CEXP,
                 RE_MUL_II, IM_MUL_II, RE_CX, IM_CX] THEN
    REWRITE_TAC [REAL_NEG_0, REAL_EXP_0, RE_II, REAL_MUL_LZERO] THEN
    REWRITE_TAC [IM_II, REAL_MUL_LNEG, REAL_MUL_LID] THEN REAL_ARITH_TAC)

  let HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES_POLAR ← prove
   r"!f:complex->real^N b.
        f absolutely_integrable_on (:complex) /\ integral (:complex) f = b <=>
        (\z. Re z % f(Cx(Re z) * cexp(ii * Cx(Im z))))
        absolutely_integrable_on
        {z | &0 <= Re z /\ &0 <= Im z /\ Im z <= &2 * pi} /\
        integral {z | &0 <= Re z /\ &0 <= Im z /\ Im z <= &2 * pi}
        (\z. Re z % f(Cx(Re z) * cexp(ii * Cx(Im z)))) = b"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL
     [← q r"f:complex->real^N",
      ← q r"\z. Cx(Re z) * cexp(ii * Cx(Im z))",
      ← q r"\z h. (vector[vector[cos(Im z); --Re(z) * sin(Im z)];
                     vector[sin(Im z); Re z * cos(Im z)]]:real^2^2) ** h",
      ← q r"{z:complex | &0 < Re z /\ &0 < Im z /\ Im z < &2 * pi}"]
     HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES) THEN
    REWRITE_TAC [MATRIX_OF_MATRIX_VECTOR_MUL, IN_ELIM_THM] THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    SUBGOAL_THEN
     (← q r"IMAGE (\z. Cx (Re z) * cexp (ii * Cx (Im z)))
            {z | &0 < Re z /\ &0 < Im z /\ Im z < &2 * pi} =
      {z | Im z = &0 ==> Re z < &0}")
    SUBST1_TAC THENL
     [REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, SUBSET, FORALL_IN_IMAGE] THEN
      REWRITE_TAC [IN_ELIM_THM, IN_IMAGE, IM_MUL_CX, IM_CEXP] THEN
      CONJ_TAC THEN X_GEN_TAC (← q r"z:complex") THEN STRIP_TAC THENL
       [ASM_SIMP_TAC [REAL_ENTIRE, REAL_EXP_NZ, REAL_LT_IMP_NZ] THEN
        REWRITE_TAC [IM_II, REAL_MUL_LID] THEN DISCH_TAC THEN
        MP_TAC (← ISPEC (← q r"Im z - pi") SIN_EQ_0_PI) THEN
        ASM_REWRITE_TAC [SIN_SUB, SIN_PI, COS_PI, REAL_SUB_0] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC, DISCH_THEN SUBST1_TAC] THEN
        REWRITE_TAC [CEXP_II_PI, RE_MUL_CX, RE_NEG, RE_CX] THEN
        ASM_REAL_ARITH_TAC,
        EXISTS_TAC (← q r"complex(norm z,Arg z)") THEN
        REWRITE_TAC [RE, IM] THEN POP_ASSUM MP_TAC THEN
        ASM_CASES_TAC (← q r"z = Cx(&0)") THEN
        ASM_REWRITE_TAC [IM_CX, RE_CX, REAL_LT_REFL, COMPLEX_NORM_NZ] THEN
        REWRITE_TAC [← REAL_ARITH (← q r"&0 < x <=> &0 <= x /\ ~(x = &0)")] THEN
        MP_TAC (← SPEC (← q r"z:complex") ARG) THEN
        DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [ARG_EQ_0, real] THEN REAL_ARITH_TAC],
      ALL_TAC] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC [← SET_RULE (← q r"{x | P x /\ Q x} = {x | P x} INTER {x | Q x}")] THEN
        REPEAT (MATCH_MP_TAC LEBESGUE_MEASURABLE_INTER THEN CONJ_TAC) THEN
        MATCH_MP_TAC LEBESGUE_MEASURABLE_CONVEX THEN
        REWRITE_TAC [IM_DEF, RE_DEF, CONVEX_HALFSPACE_COMPONENT_LT,
                     ← REWRITE_RULE [real_gt] CONVEX_HALFSPACE_COMPONENT_GT],
        SIMP_TAC [HAS_DERIVATIVE_POLAR, HAS_DERIVATIVE_AT_WITHIN],
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM (fun th => tactic_of do pure (
          MP_TAC (← AP_TERM (← q r"Arg") th) THEN
          MP_TAC (← AP_TERM (← q r"\z:complex. norm z") th))) THEN
        ASM_SIMP_TAC [ARG_MUL_CX, IN_ELIM_THM] THEN
        ASM_SIMP_TAC [ARG_CEXP, IM_MUL_II, RE_CX, REAL_LT_IMP_LE] THEN
        REWRITE_TAC [COMPLEX_NORM_MUL, NORM_CEXP_II, REAL_MUL_RID] THEN
        ASM_SIMP_TAC [COMPLEX_NORM_CX, ← REAL_ARITH (← q r"&0 < x ==> abs x = x")] THEN
        SIMP_TAC [COMPLEX_EQ]],
      DISCH_THEN (MP_TAC o SPEC (← q r"b:real^N")) THEN
      REWRITE_TAC [DET_2, VECTOR_2, SIN_CIRCLE, REAL_MUL_RID, ← REAL_ARITH
       (← q r"c * r * c - (--r * s) * s:real = r * (s pow 2 + c pow 2)")] THEN
      MATCH_MP_TAC (← TAUT
       (← q r"(p <=> p') /\ (q <=> q') ==> (q <=> p) ==> (p' <=> q')")) THEN
      CONJ_TAC THEN
      ONCE_REWRITE_TAC [← GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV,
                        ← GSYM INTEGRAL_RESTRICT_UNIV] THEN
      MATCH_MP_TAC (← MESON [ABSOLUTELY_INTEGRABLE_SPIKE_EQ, INTEGRAL_SPIKE]
       (← q r"!s. negligible s /\ (!x. x IN t DIFF s ==> g x = f x)
            ==> (f absolutely_integrable_on t /\ integral t f = b <=>
                 g absolutely_integrable_on t /\ integral t g = b)"))
      THENL
       [EXISTS_TAC (← q r"{z | Im z = &0}"),
        EXISTS_TAC (← q r"{z | Re z = &0} UNION
                    {z | Im z = &0} UNION {z | Im z = &2 * pi}")] THEN
      ASM_REWRITE_TAC [IM_DEF, RE_DEF, NEGLIGIBLE_UNION_EQ,
                       NEGLIGIBLE_STANDARD_HYPERPLANE] THEN
      SIMP_TAC [← GSYM IM_DEF, ← GSYM RE_DEF, IN_DIFF, IN_UNIV, IN_UNION,
                IN_ELIM_THM, DE_MORGAN_THM] THEN
      X_GEN_TAC (← q r"z:complex") THEN SIMP_TAC [REAL_LT_LE] THEN
      STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC])

  let ABSOLUTELY_INTEGRABLE_CHANGE_OF_VARIABLES_POLAR ← prove
   r"!f:complex->real^N.
        f absolutely_integrable_on (:complex) <=>
        (\z. Re z % f(Cx(Re z) * cexp(ii * Cx(Im z))))
        absolutely_integrable_on
        {z | &0 <= Re z /\ &0 <= Im z /\ Im z <= &2 * pi}"
   (MESON_TAC [HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES_POLAR])

  pure { HAS_DERIVATIVE_POLAR, HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES_POLAR,
         ABSOLUTELY_INTEGRABLE_CHANGE_OF_VARIABLES_POLAR }
/- ------------------------------------------------------------------------- -/
/- Integration via polar coordinates (2).                                    -/
/- (transcendentals.ml 7388-7608)                                           -/
/- ------------------------------------------------------------------------- -/

structure TSAF where
  FUBINI_POLAR : thm
  FUBINI_TONELLI_POLAR : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupTSAF [HolBase] (D : TranscendentalsDeps) (BTSC : TSC) (BTSAE : TSAE) : ExceptT String IO TSAF := do
  -- @@SCOPE BEGIN
  let { SIN_CIRCLE, .. } := BTSC
  let { ABSOLUTELY_INTEGRABLE_CHANGE_OF_VARIABLES_POLAR,
        HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES_POLAR, HAS_DERIVATIVE_POLAR, .. } := BTSAE
  let { CONVEX_HALFSPACE_COMPONENT_GT, CONVEX_HALFSPACE_COMPONENT_LT, .. } := D.qconvex
  let { DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON, .. } := D.qderivatives
  let { CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET,
        FUBINI_HAS_ABSOLUTE_INTEGRAL, FUBINI_TONELLI, LEBESGUE_MEASURABLE_CONVEX,
        LEBESGUE_MEASURABLE_INTER, LEBESGUE_MEASURABLE_UNIV,
        MEASURABLE_ON_CONTINUOUS_COMPOSE, MEASURABLE_ON_LINEAR_IMAGE_EQ_GEN,
        MEASURABLE_ON_MUL, MEASURABLE_ON_SPIKE_SET, MEASURABLE_ON_UNIV,
        NEGLIGIBLE_DIFFERENTIABLE_PREIMAGE, NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE,
        .. } := D.qmeasure
  let { ABSOLUTELY_INTEGRABLE_TWIZZLE_EQ, INTEGRAL_TWIZZLE_EQ, .. } := D.qintegration
  let { PERMUTES_ID, .. } := D.qpermutations
  let { IM, IM_DEF, RE, RE_DEF, .. } := D.cn.cxa
  let { HAS_DERIVATIVE_AT_WITHIN, .. } := D.cn.ms.qderivatives
  let { DET_2, RANK_EQ_FULL_DET, .. } := D.cn.ms.qdet
  let { ABSOLUTELY_INTEGRABLE_0, ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV,
        .. } := D.cn.ms.qintegration1
  let { INTEGRABLE_RESTRICT_UNIV, INTEGRAL_0, .. } := D.cn.ms.qintegration2
  let { INTEGRAL_RESTRICT_UNIV, NEGLIGIBLE_STANDARD_HYPERPLANE, NEGLIGIBLE_SUBSET,
        NEGLIGIBLE_UNION_EQ, .. } := D.cn.ms.qintegration3
  let { ASM_MESON_TAC, MESON_TAC, NUM_REDUCE_CONV, REAL_ARITH, REAL_ARITH_TAC, SET_RULE,
        SET_TAC, .. } := D.cn.cx.cvx
  let { FORALL_2, VECTOR_2, .. } := D.cn.cx.cpx
  let { differentiable, DIFFERENTIABLE_IMP_CONTINUOUS_ON, .. } := D.cn.ms.ig.qderivatives
  let { pastecart, .. } := D.cn.ms.ig.qsession
  let { ARITH, CART_EQ, DIMINDEX_1, DIMINDEX_2, DIMINDEX_FINITE_SUM, EQ_IMP, ETA_AX,
        EXTENSION, .. } := D.cn.cx.cvx.core1
  let { FUN_EQ_THM, IMP_CONJ_ALT, IMP_IMP, IN, IN_DIFF, .. } := D.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_UNION, IN_UNIV, LAMBDA_BETA, MONO_AND, .. } := D.cn.cx.cvx.core3
  let { REAL_LT_IMP_NZ, .. } := D.cn.cx.cvx.core4
  let { REAL_MUL_RID, SUBSET, .. } := D.cn.cx.cvx.core5
  let { o_DEF, o_THM, real_abs, real_gt, SUBSET_UNIV, .. } := D.cn.cx.cvx.core6
  let { DROP_VEC, LIFT_CMUL, LIFT_DROP, LIFT_NUM, LINEAR_LIFT_COMPONENT,
        MATRIX_OF_MATRIX_VECTOR_MUL, NORM_0, .. } := D.cn.cx.cvx.vec2
  let { NORM_MUL, .. } := D.cn.cx.cvx.vec3
  let { drop, linear, VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, .. } := D.cn.cx.cvx.vec4
  let { IN_INTERVAL_1, LINEAR_CONTINUOUS_ON, .. } := D.cn.cx.cvx.top4
  -- @@SCOPE END

  let FUBINI_POLAR ← prove
   r"!f:complex->real^N.
        f absolutely_integrable_on (:complex)
        ==> negligible
             {r | &0 <= drop r /\
                  ~((\t. drop r % f(Cx(drop r) * cexp(ii * Cx(drop t))))
                    absolutely_integrable_on interval[vec 0,lift(&2 * pi)])} /\
            (\r. integral (interval[vec 0,lift(&2 * pi)])
                   (\t. drop r % f(Cx(drop r) * cexp(ii * Cx(drop t)))))
            absolutely_integrable_on {r | &0 <= drop r} /\
            integral {r | &0 <= drop r}
             (\r. integral (interval[vec 0,lift(&2 * pi)])
                    (\t. drop r % f(Cx(drop r) * cexp(ii * Cx(drop t))))) =
            integral (:complex) f"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"f:complex->real^N", ← q r"integral UNIV (f:complex->real^N)"]
          HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES_POLAR) THEN
    ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [← GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV,
                      ← GSYM INTEGRAL_RESTRICT_UNIV] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    ABBREV_TAC
     (← q r"g = \x. if &0 <= Re x /\ &0 <= Im x /\ Im x <= &2 * pi
              then Re x % (f:complex->real^N) (Cx(Re x) * cexp(ii * Cx(Im x)))
              else vec 0") THEN
    REWRITE_TAC [IN_UNIV, ETA_AX] THEN STRIP_TAC THEN
    ABBREV_TAC (← q r"h:real^(1,1)finite_sum->complex = \x. lambda i. x$i") THEN
    ABBREV_TAC (← q r"k:complex->real^(1,1)finite_sum = \x. lambda i. x$i") THEN
    SUBGOAL_THEN
     (← q r"(!x:complex. h(k x) = x) /\ (!y:real^(1,1)finite_sum. k(h y) = y)")
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["h", "k"] THEN
      SIMP_TAC [CART_EQ, LAMBDA_BETA, DIMINDEX_FINITE_SUM, DIMINDEX_2,
                ARITH, DIMINDEX_1],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"IMAGE (h:real^(1,1)finite_sum->complex) UNIV = UNIV /\
                  IMAGE (k:complex->real^(1,1)finite_sum) UNIV = UNIV")
    STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    MP_TAC (← ISPEC (← q r"(g:complex->real^N) o (h:real^(1,1)finite_sum->complex)")
          FUBINI_HAS_ABSOLUTE_INTEGRAL) THEN
    ANTS_TAC THENL
     [MP_TAC (← ISPECL [← q r"g:complex->real^N", ← q r"(:real^(1,1)finite_sum)",
                       ← q r"\n:num. n"] ABSOLUTELY_INTEGRABLE_TWIZZLE_EQ) THEN
      REWRITE_TAC [PERMUTES_ID, DIMINDEX_FINITE_SUM, DIMINDEX_1, DIMINDEX_2] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [← GSYM o_DEF] THEN
      ASM_REWRITE_TAC [],
      MP_TAC (← ISPECL [← q r"g:complex->real^N", ← q r"(:real^(1,1)finite_sum)",
                       ← q r"\n:num. n"] INTEGRAL_TWIZZLE_EQ) THEN
      REWRITE_TAC [PERMUTES_ID, DIMINDEX_FINITE_SUM, DIMINDEX_1, DIMINDEX_2] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [← GSYM o_DEF] THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM)] THEN
    SUBGOAL_THEN
     (← q r"!x y. ((g:complex->real^N) o h) (pastecart x y) =
            g(complex(drop x,drop y))")
     (fun th => REWRITE_TAC [th])
    THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC [o_THM] THEN AP_TERM_TAC THEN
      EXPAND_TAC "h" THEN
      SIMP_TAC [pastecart, CART_EQ, LAMBDA_BETA, DIMINDEX_1, DIMINDEX_2, ARITH,
                DIMINDEX_FINITE_SUM] THEN
      REWRITE_TAC [FORALL_2, ARITH] THEN
      REWRITE_TAC [← GSYM RE_DEF, ← GSYM IM_DEF, RE, IM] THEN REWRITE_TAC [drop],
      ALL_TAC] THEN
    EXPAND_TAC "g" THEN REWRITE_TAC [RE, IM] THEN
    REPEAT (MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THENL
     [MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_INTERVAL_1, DROP_VEC] THEN
      X_GEN_TAC (← q r"r:real^1") THEN ASM_CASES_TAC (← q r"&0 <= drop r") THEN
      ASM_REWRITE_TAC [LIFT_DROP],
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC id [FUN_EQ_THM] THEN
      X_GEN_TAC (← q r"r:real^1") THEN REWRITE_TAC [IN_ELIM_THM] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
       [← GSYM INTEGRAL_RESTRICT_UNIV] THEN
      ASM_CASES_TAC (← q r"&0 <= drop r") THEN
      ASM_REWRITE_TAC [INTEGRAL_0, IN_INTERVAL_1, LIFT_DROP, DROP_VEC],
      DISCH_THEN (SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC id [FUN_EQ_THM] THEN
      X_GEN_TAC (← q r"r:real^1") THEN REWRITE_TAC [IN_ELIM_THM] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [← GSYM INTEGRAL_RESTRICT_UNIV] THEN
      ASM_CASES_TAC (← q r"&0 <= drop r") THEN
      ASM_REWRITE_TAC [INTEGRAL_0, IN_INTERVAL_1, LIFT_DROP, DROP_VEC]])

  let FUBINI_TONELLI_POLAR ← prove
   r"!f:complex->real^N.
       f measurable_on (:complex)
       ==> (f absolutely_integrable_on (:complex) <=>
            negligible
             {r | &0 <= drop r /\
                  ~((\t. drop r % f(Cx(drop r) * cexp(ii * Cx(drop t))))
                    absolutely_integrable_on interval[vec 0,lift(&2 * pi)])} /\
            (\r. integral (interval[vec 0,lift(&2 * pi)])
                  (\t. drop r %
                       lift(norm(f(Cx(drop r) * cexp(ii * Cx(drop t)))))))
            integrable_on {r | &0 <= drop r})"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    ABBREV_TAC
     (← q r"g = \x. if &0 <= Re x /\ &0 <= Im x /\ Im x <= &2 * pi
              then Re x % (f:complex->real^N) (Cx(Re x) * cexp(ii * Cx(Im x)))
              else vec 0") THEN
    ABBREV_TAC (← q r"h:real^(1,1)finite_sum->complex = \x. lambda i. x$i") THEN
    ABBREV_TAC (← q r"k:complex->real^(1,1)finite_sum = \x. lambda i. x$i") THEN
    SUBGOAL_THEN
     (← q r"(!x:complex. h(k x) = x) /\ (!y:real^(1,1)finite_sum. k(h y) = y)")
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["h", "k"] THEN
      SIMP_TAC [CART_EQ, LAMBDA_BETA, DIMINDEX_FINITE_SUM, DIMINDEX_2,
                ARITH, DIMINDEX_1],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"IMAGE (h:real^(1,1)finite_sum->complex) UNIV = UNIV /\
                  IMAGE (k:complex->real^(1,1)finite_sum) UNIV = UNIV")
    STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    MP_TAC (← ISPEC (← q r"(g:complex->real^N) o (h:real^(1,1)finite_sum->complex)")
          FUBINI_TONELLI) THEN
    ANTS_TAC THENL
     [W (MP_TAC o PART_MATCH (lhand o rand)
        MEASURABLE_ON_LINEAR_IMAGE_EQ_GEN o snd) THEN
      ASM_REWRITE_TAC [DIMINDEX_2, DIMINDEX_FINITE_SUM, DIMINDEX_1, ARITH] THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [EXPAND_TAC "h", ASM_MESON_TAC []] THEN
        SIMP_TAC [linear, LAMBDA_BETA, DIMINDEX_2, DIMINDEX_FINITE_SUM,
                  DIMINDEX_1, ARITH, CART_EQ, VECTOR_ADD_COMPONENT,
                  VECTOR_MUL_COMPONENT],
        DISCH_THEN SUBST1_TAC] THEN
      EXPAND_TAC "g" THEN
      REWRITE_TAC [← REWRITE_RULE [IN] MEASURABLE_ON_UNIV] THEN
      GEN_REWRITE_TAC RAND_CONV [← SET_RULE (← q r"(\x. P x) = {x | P x}")] THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_IMP] MEASURABLE_ON_SPIKE_SET) THEN
      EXISTS_TAC (← q r"{z | &0 < Re z /\ &0 < Im z /\ Im z < &2 * pi}") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC (← q r"{z | Re z = &0} UNION {z | Im z = &0} UNION
                    {z | Im z = &2 * pi}") THEN
        REWRITE_TAC [IM_DEF, RE_DEF, NEGLIGIBLE_UNION_EQ,
                     NEGLIGIBLE_STANDARD_HYPERPLANE] THEN
        REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_DIFF, IN_UNION] THEN REAL_ARITH_TAC,
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"lebesgue_measurable {z | &0 < Re z /\ &0 < Im z /\ Im z < &2 * pi}")
      ASSUME_TAC THENL
       [REWRITE_TAC [← SET_RULE (← q r"{x | P x /\ Q x} = {x | P x} INTER {x | Q x}")] THEN
        REPEAT (MATCH_MP_TAC LEBESGUE_MEASURABLE_INTER THEN CONJ_TAC) THEN
        MATCH_MP_TAC LEBESGUE_MEASURABLE_CONVEX THEN
        REWRITE_TAC [IM_DEF, RE_DEF, CONVEX_HALFSPACE_COMPONENT_LT,
                     ← REWRITE_RULE [real_gt] CONVEX_HALFSPACE_COMPONENT_GT],
        ALL_TAC] THEN
      MATCH_MP_TAC MEASURABLE_ON_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
        REWRITE_TAC [RE_DEF, LINEAR_LIFT_COMPONENT],
        GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF]] THEN
      MATCH_MP_TAC MEASURABLE_ON_CONTINUOUS_COMPOSE THEN
      EXISTS_TAC (← q r"(:complex)") THEN
      ASM_REWRITE_TAC [LEBESGUE_MEASURABLE_UNIV, SUBSET_UNIV] THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
        MATCH_MP_TAC DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON THEN
        X_GEN_TAC (← q r"z:complex") THEN DISCH_THEN (K ALL_TAC) THEN
        REWRITE_TAC [differentiable] THEN
        MP_TAC (← SPEC (← q r"z:complex") HAS_DERIVATIVE_POLAR) THEN MESON_TAC [],
        X_GEN_TAC (← q r"k:complex->bool") THEN DISCH_TAC THEN
        MATCH_MP_TAC NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE THEN
        MATCH_MP_TAC NEGLIGIBLE_DIFFERENTIABLE_PREIMAGE THEN
        EXISTS_TAC
         (← q r"\z h. (vector[vector[cos(Im z); --Re(z) * sin(Im z)];
                     vector[sin(Im z); Re z * cos(Im z)]]:real^2^2) ** h") THEN
        ASM_REWRITE_TAC [RANK_EQ_FULL_DET, MATRIX_OF_MATRIX_VECTOR_MUL] THEN
        REWRITE_TAC [DET_2, VECTOR_2, SIN_CIRCLE, REAL_MUL_RID, ← REAL_ARITH
          (← q r"c * r * c - (--r * s) * s:real = r * (s pow 2 + c pow 2)")] THEN
        X_GEN_TAC (← q r"z:complex") THEN REWRITE_TAC [IN_ELIM_THM] THEN
        SIMP_TAC [REAL_LT_IMP_NZ] THEN DISCH_TAC THEN
        MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
        REWRITE_TAC [HAS_DERIVATIVE_POLAR]],
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV
       [ABSOLUTELY_INTEGRABLE_CHANGE_OF_VARIABLES_POLAR] THEN
      GEN_REWRITE_TAC RAND_CONV
       [← GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
      ASM_REWRITE_TAC [IN_ELIM_THM] THEN
      FIRST_X_ASSUM (fun th => tactic_of do pure (
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← GSYM th])) THEN
      CONV_TAC SYM_CONV THEN EXPAND_TAC "h" THEN REWRITE_TAC [o_DEF] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_TWIZZLE_EQ THEN
      REWRITE_TAC [PERMUTES_ID, DIMINDEX_2, DIMINDEX_1, DIMINDEX_FINITE_SUM] THEN
      CONV_TAC NUM_REDUCE_CONV,
      SUBGOAL_THEN
       (← q r"!x y. ((g:complex->real^N) o h) (pastecart x y) =
              g(complex(drop x,drop y))")
       (fun th => REWRITE_TAC [th])
      THENL
       [REPEAT GEN_TAC THEN REWRITE_TAC [o_THM] THEN AP_TERM_TAC THEN
        EXPAND_TAC "h" THEN
        SIMP_TAC [pastecart, CART_EQ, LAMBDA_BETA, DIMINDEX_1, DIMINDEX_2, ARITH,
                  DIMINDEX_FINITE_SUM] THEN
        REWRITE_TAC [FORALL_2, ARITH] THEN
        REWRITE_TAC [← GSYM RE_DEF, ← GSYM IM_DEF, RE, IM] THEN REWRITE_TAC [drop],
        ALL_TAC] THEN
      EXPAND_TAC "g" THEN REWRITE_TAC [RE, IM] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
       [← GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV,
        ← GSYM INTEGRABLE_RESTRICT_UNIV] THEN
      BINOP_TAC THENL
       [AP_TERM_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN
        X_GEN_TAC (← q r"r:real^1") THEN REWRITE_TAC [IN_ELIM_THM] THEN
        ASM_CASES_TAC (← q r"&0 <= drop r") THEN
        ASM_REWRITE_TAC [ABSOLUTELY_INTEGRABLE_0] THEN
        REWRITE_TAC [IN_INTERVAL_1, LIFT_DROP, DROP_VEC],
        AP_THM_TAC THEN AP_TERM_TAC THEN
        GEN_REWRITE_TAC id [FUN_EQ_THM] THEN X_GEN_TAC (← q r"r:real^1") THEN
        REWRITE_TAC [IN_ELIM_THM] THEN
        ASM_CASES_TAC (← q r"&0 <= drop r") THEN
        ASM_REWRITE_TAC [NORM_0, LIFT_NUM, INTEGRAL_0] THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM INTEGRAL_RESTRICT_UNIV] THEN
        AP_TERM_TAC THEN
        GEN_REWRITE_TAC id [FUN_EQ_THM] THEN X_GEN_TAC (← q r"t:real^1") THEN
        REWRITE_TAC [IN_INTERVAL_1, LIFT_DROP, DROP_VEC] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [NORM_0, LIFT_NUM] THEN
        ASM_REWRITE_TAC [NORM_MUL, LIFT_CMUL, real_abs]]])

  pure { FUBINI_POLAR, FUBINI_TONELLI_POLAR }

end HolMultiLib.Transcendentals
