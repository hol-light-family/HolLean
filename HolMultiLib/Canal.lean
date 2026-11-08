/- ========================================================================= -/
/- Complex analysis.                                                         -/
/- ========================================================================= -/
/- File: HolMultiLib/Canal.lean

  Original (c) Copyright, John Harrison 1998-2008 (see canal.ml).
  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/canal.ml`, in the style of
  HolMultiLib/Measure.lean: pure, the proofs translated by hand, one `let`
  per OCaml `let`, in file order.  The load-time effects are at their file
  positions.  What canal.ml uses from earlier files is passed in `CanalDeps`.
  SessionMultiLib/Canal.lean supplies it.
-/

import HolMultiLib.Measure
import HolMultiLib.Complexes

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolMultiLib.Canal

/- The theorems canal.ml uses that the deps chain does not carry, grouped by the
   file that proves them. -/

structure QConvexThms where
  (CONVEX_HALFSPACE_COMPONENT_SGN CONVEX_HALFSPACE_GT CONVEX_HALFSPACE_LT
   SEGMENT_BOUND : thm)
  deriving Inhabited

structure QPathsThms where
  (CONNECTED_PUNCTURED_BALL CONVEX_IMP_PATH_CONNECTED : thm)
  deriving Inhabited

structure QTopologyThms where
  (BILINEAR_UNIFORMLY_CONTINUOUS_ON_COMPOSE BOUNDED_PARTIAL_SUMS continuous
   CONTINUOUS_AT_BALL CONTINUOUS_ON_OPEN_AVOID CONTINUOUS_TRIVIAL_LIMIT
   INFSUM_RESTRICT INFSUM_UNIQUE LIM_AT_INFINITY LIM_AT_INFINITY_POS LIM_AT_LE
   LIM_COMPONENT_EQ LIM_CONTINUOUS LIM_TRANSFORM_AWAY_AT
   LINEAR_UNIFORMLY_CONTINUOUS_ON SEQUENCE_CAUCHY_WLOG SERIES_BILINEAR
   SERIES_BILINEAR_UNIQUE SERIES_CAUCHY SERIES_COMPARISON SERIES_COMPARISON_UNIFORM
   SERIES_COMPONENT SERIES_DIRICHLET SERIES_DIRICHLET_BILINEAR SERIES_FROM
   SERIES_LINEAR SERIES_RESTRICT SERIES_SUB SERIES_VSUM summable
   SUMMABLE_BILINEAR_LEFT SUMMABLE_BILINEAR_RIGHT SUMMABLE_IMP_BOUNDED SUMMABLE_RATIO
   SUMMABLE_RESTRICT SUMMABLE_SUBSET SUMMABLE_TRIVIAL SUMS_0 SUMS_INFSUM
   SUMS_REINDEX_GEN UNIFORM_LIM_BILINEAR UNIFORMLY_CAUCHY_IMP_UNIFORMLY_CONVERGENT
   UNIFORMLY_CONTINUOUS_ON_COMPOSE : thm)
  deriving Inhabited

structure QDerivativesThms where
  (DIFF_CHAIN_AT DIFFERENTIABLE_BOUND FRECHET_DERIVATIVE_AT
   FRECHET_DERIVATIVE_UNIQUE_AT HAS_DERIVATIVE_BILINEAR_WITHIN
   HAS_DERIVATIVE_INVERSE_BASIC HAS_DERIVATIVE_INVERSE_STRONG
   HAS_DERIVATIVE_INVERSE_STRONG_X HAS_DERIVATIVE_SEQUENCE HAS_DERIVATIVE_SERIES
   HAS_DERIVATIVE_TRANSFORM_WITHIN HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN
   HAS_DERIVATIVE_VSUM HAS_DERIVATIVE_ZERO_CONNECTED_CONSTANT
   HAS_DERIVATIVE_ZERO_CONNECTED_UNIQUE HAS_DERIVATIVE_ZERO_CONSTANT
   HAS_DERIVATIVE_ZERO_UNIQUE JACOBIAN_WORKS MVT_VERY_SIMPLE vector_derivative : thm)
  deriving Inhabited

structure QDeterminantsThms where
  (ROTATION_MATRIX_2 : thm)
  deriving Inhabited

structure QVectorsThms where
  (BILINEAR_VSUM_PARTIAL_PRE LINEAR_I MATRIX_CMUL_COMPONENT VSUM_COMBINE_R
   VSUM_SING_NUMSEG : thm)
  deriving Inhabited

structure QSessionThms where
  (FACT FACT_LT REAL_EQ_SUB_RADD REAL_POS_EQ_SQUARE REAL_POW_1_LT SUM_DIFFS
   SUM_EQ_0_NUMSEG : thm)
  deriving Inhabited

structure QIntegrationThms where
  (HAS_BOUNDED_SETVARIATION_ON HAS_BOUNDED_VARIATION_ON_ADD
   HAS_BOUNDED_VARIATION_ON_MUL INTEGRABLE_BOUNDED_VARIATION_BILINEAR_LMUL
   INTEGRABLE_INTEGRAL INTEGRAL_COMPONENT : thm)
  deriving Inhabited

structure QMeasureThms where
  (CONTINUOUS_IMP_MEASURABLE_ON MEASURABLE_ADDITIVE_IMP_LINEAR MEASURABLE_ON_CONST : thm)
  deriving Inhabited

structure QFloorThms where
  (FORALL_INTEGER rational : thm)
  deriving Inhabited

structure CanalDeps where
  ms : HolMultiLib.Measure.MeasureDeps
  cx : HolMultiLib.ComplexAlgebra.ComplexAlgebraDeps
  cxa : HolMultiLib.ComplexAlgebra.CXA
  cxb : HolMultiLib.ComplexAlgebra.CXB
  cxc : HolMultiLib.ComplexAlgebra.CXC
  cxd : HolMultiLib.ComplexAlgebra.CXD
  cxe : HolMultiLib.ComplexAlgebra.CXE
  cxf : HolMultiLib.ComplexAlgebra.CXF
  cxg : HolMultiLib.ComplexAlgebra.CXG
  cxh : HolMultiLib.ComplexAlgebra.CXH
  cxi : HolMultiLib.ComplexAlgebra.CXI
  cxj : HolMultiLib.ComplexAlgebra.CXJ
  cxk : HolMultiLib.ComplexAlgebra.CXK
  cxl : HolMultiLib.Complexes.CXL
  cxm : HolMultiLib.Complexes.CXM
  cxn : HolMultiLib.Complexes.CXN
  -- theorems
  qconvex : QConvexThms
  qpaths : QPathsThms
  qtopology : QTopologyThms
  qderivatives : QDerivativesThms
  qdeterminants : QDeterminantsThms
  qvectors : QVectorsThms
  qsession : QSessionThms
  qintegration : QIntegrationThms
  qmeasure : QMeasureThms
  qfloor : QFloorThms

/- ------------------------------------------------------------------------- -/
/- prioritize_complex(); some topological facts formulated for the complex  -/
/- numbers.  (canal.ml 15-214)                                              -/
/- ------------------------------------------------------------------------- -/

structure KNA where
  CLOSED_HALFSPACE_RE_GE : thm
  CLOSED_HALFSPACE_RE_LE : thm
  CLOSED_HALFSPACE_RE_EQ : thm
  OPEN_HALFSPACE_RE_GT : thm
  OPEN_HALFSPACE_RE_LT : thm
  CLOSED_HALFSPACE_IM_GE : thm
  CLOSED_HALFSPACE_IM_LE : thm
  CLOSED_HALFSPACE_IM_EQ : thm
  OPEN_HALFSPACE_IM_GT : thm
  OPEN_HALFSPACE_IM_LT : thm
  CONVEX_HALFSPACE_RE_GE : thm
  CONVEX_HALFSPACE_RE_GT : thm
  CONVEX_HALFSPACE_RE_LE : thm
  CONVEX_HALFSPACE_RE_LT : thm
  CONVEX_HALFSPACE_IM_GE : thm
  CONVEX_HALFSPACE_IM_GT : thm
  CONVEX_HALFSPACE_IM_LE : thm
  CONVEX_HALFSPACE_IM_LT : thm
  CONVEX_HALFSPACE_RE_SGN : thm
  CONVEX_HALFSPACE_IM_SGN : thm
  COMPLEX_IN_BALL_0 : thm
  COMPLEX_IN_CBALL_0 : thm
  COMPLEX_IN_SPHERE_0 : thm
  IN_BALL_RE : thm
  IN_BALL_IM : thm
  IN_CBALL_RE : thm
  IN_CBALL_IM : thm
  CLOSED_REAL_SET : thm
  CLOSED_REAL : thm
  UNBOUNDED_REAL : thm
  CONNECTED_REAL : thm
  PATH_CONNECTED_REAL : thm
  TRIVIAL_LIMIT_WITHIN_REAL : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupKNA [HolBase] (D : CanalDeps) : ExceptT String IO KNA := do
  -- @@SCOPE BEGIN
  let { ii, IM, IM_DEF, prioritize_complex, RE, RE_DEF, .. } := D.cxa
  let { COMPLEX_NORM_CX, COMPLEX_VEC_0, IM_CX, IM_SUB, RE_CX, RE_SUB, .. } := D.cxc
  let { COMPLEX_NORM_GE_RE_IM, .. } := D.cxg
  let { real, REAL_EXISTS, .. } := D.cxi
  let { CONVEX_REAL, .. } := D.cxm
  let { CONVEX_HALFSPACE_COMPONENT_SGN, CONVEX_HALFSPACE_GT, CONVEX_HALFSPACE_LT,
        .. } := D.qconvex
  let { CONVEX_IMP_PATH_CONNECTED, .. } := D.qpaths
  let { MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, SET_RULE, .. } := D.cx.cvx
  let { SUM_2, .. } := D.cx.cpx
  let { BOUNDED_SING, .. } := D.ms.ig.qtopology
  let { DIMINDEX_2, EQ_IMP, EXTENSION, .. } := D.cx.cvx.core1
  let { IN, .. } := D.cx.cvx.core2
  let { IN_ELIM_THM, LEFT_IMP_EXISTS_THM, .. } := D.cx.cvx.core3
  let { dist, dot, .. } := D.cx.cvx.vec4
  let { CLOSED_HALFSPACE_GE, CLOSED_INTER, .. } := D.cx.cvx.top1
  let { CONNECTED_IMP_PERFECT_CLOSED, .. } := D.cx.cvx.top2
  let { IN_BALL, IN_BALL_0, IN_CBALL, IN_CBALL_0, IN_SPHERE_0, .. } := D.cx.cvx.top4
  let { bounded, TRIVIAL_LIMIT_WITHIN, .. } := D.cx.cvx.top5
  let { CONVEX_CONNECTED, .. } := D.ms.ig.dv.dg.qconvex
  let { OPEN_CLOSED, .. } := D.ms.ig.dv.dg.qtopology2
  let { CLOSED_HALFSPACE_LE, .. } := D.ms.ig.dv.dg.pt.qtop
  let { CONVEX_HALFSPACE_GE, CONVEX_HALFSPACE_LE, .. } := D.ms.ig.dv.dg.pt.qcvx2
  -- @@SCOPE END

  prioritize_complex

  let CLOSED_HALFSPACE_RE_GE ← prove
   r"!b. closed {z | Re(z) >= b}"
   (GEN_TAC THEN MP_TAC (← ISPECL [← q r"Cx(&1)", ← q r"b:real"] CLOSED_HALFSPACE_GE) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, dot, SUM_2, DIMINDEX_2, ← GSYM RE_DEF, ← GSYM IM_DEF] THEN
    REWRITE_TAC [RE_CX, IM_CX, IN_ELIM_THM] THEN REAL_ARITH_TAC)

  let CLOSED_HALFSPACE_RE_LE ← prove
   r"!b. closed {z | Re(z) <= b}"
   (GEN_TAC THEN MP_TAC (← ISPECL [← q r"Cx(&1)", ← q r"b:real"] CLOSED_HALFSPACE_LE) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, dot, SUM_2, DIMINDEX_2, ← GSYM RE_DEF, ← GSYM IM_DEF] THEN
    REWRITE_TAC [RE_CX, IM_CX, IN_ELIM_THM] THEN REAL_ARITH_TAC)

  let CLOSED_HALFSPACE_RE_EQ ← prove
   r"!b. closed {z | Re(z) = b}"
   (GEN_TAC THEN REWRITE_TAC [← REAL_ARITH (← q r"x = y <=> x >= y /\ x <= y")] THEN
    REWRITE_TAC [← SET_RULE (← q r"{x | P x /\ Q x} = {x | P x} INTER {x | Q x}")] THEN
    SIMP_TAC [CLOSED_INTER, CLOSED_HALFSPACE_RE_GE, CLOSED_HALFSPACE_RE_LE])

  let OPEN_HALFSPACE_RE_GT ← prove
   r"!b. open {z | Re(z) > b}"
   (REWRITE_TAC [OPEN_CLOSED, CLOSED_HALFSPACE_RE_LE,
                 ← REAL_ARITH (← q r"x > y <=> ~(x <= y)"),
                 ← SET_RULE (← q r"UNIV DIFF {x | ~p x} = {x | p x}")])

  let OPEN_HALFSPACE_RE_LT ← prove
   r"!b. open {z | Re(z) < b}"
   (REWRITE_TAC [OPEN_CLOSED, CLOSED_HALFSPACE_RE_GE,
                 ← REAL_ARITH (← q r"x < y <=> ~(x >= y)"),
                 ← SET_RULE (← q r"UNIV DIFF {x | ~p x} = {x | p x}")])

  let CLOSED_HALFSPACE_IM_GE ← prove
   r"!b. closed {z | Im(z) >= b}"
   (GEN_TAC THEN MP_TAC (← ISPECL [← q r"ii", ← q r"b:real"] CLOSED_HALFSPACE_GE) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, dot, SUM_2, DIMINDEX_2, ← GSYM RE_DEF, ← GSYM IM_DEF] THEN
    REWRITE_TAC [ii, RE_CX, IM_CX, RE, IM, IN_ELIM_THM] THEN REAL_ARITH_TAC)

  let CLOSED_HALFSPACE_IM_LE ← prove
   r"!b. closed {z | Im(z) <= b}"
   (GEN_TAC THEN MP_TAC (← ISPECL [← q r"ii", ← q r"b:real"] CLOSED_HALFSPACE_LE) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, dot, SUM_2, DIMINDEX_2, ← GSYM RE_DEF, ← GSYM IM_DEF] THEN
    REWRITE_TAC [ii, RE_CX, IM_CX, RE, IM, IN_ELIM_THM] THEN REAL_ARITH_TAC)

  let CLOSED_HALFSPACE_IM_EQ ← prove
   r"!b. closed {z | Im(z) = b}"
   (GEN_TAC THEN REWRITE_TAC [← REAL_ARITH (← q r"x = y <=> x >= y /\ x <= y")] THEN
    REWRITE_TAC [← SET_RULE (← q r"{x | P x /\ Q x} = {x | P x} INTER {x | Q x}")] THEN
    SIMP_TAC [CLOSED_INTER, CLOSED_HALFSPACE_IM_GE, CLOSED_HALFSPACE_IM_LE])

  let OPEN_HALFSPACE_IM_GT ← prove
   r"!b. open {z | Im(z) > b}"
   (REWRITE_TAC [OPEN_CLOSED, CLOSED_HALFSPACE_IM_LE,
                 ← REAL_ARITH (← q r"x > y <=> ~(x <= y)"),
                 ← SET_RULE (← q r"UNIV DIFF {x | ~p x} = {x | p x}")])

  let OPEN_HALFSPACE_IM_LT ← prove
   r"!b. open {z | Im(z) < b}"
   (REWRITE_TAC [OPEN_CLOSED, CLOSED_HALFSPACE_IM_GE,
                 ← REAL_ARITH (← q r"x < y <=> ~(x >= y)"),
                 ← SET_RULE (← q r"UNIV DIFF {x | ~p x} = {x | p x}")])

  let CONVEX_HALFSPACE_RE_GE ← prove
   r"!b. convex {z | Re(z) >= b}"
   (GEN_TAC THEN MP_TAC (← ISPECL [← q r"Cx(&1)", ← q r"b:real"] CONVEX_HALFSPACE_GE) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, dot, SUM_2, DIMINDEX_2, ← GSYM RE_DEF, ← GSYM IM_DEF] THEN
    REWRITE_TAC [ii, RE_CX, IM_CX, RE, IM, IN_ELIM_THM] THEN REAL_ARITH_TAC)

  let CONVEX_HALFSPACE_RE_GT ← prove
   r"!b. convex {z | Re(z) > b}"
   (GEN_TAC THEN MP_TAC (← ISPECL [← q r"Cx(&1)", ← q r"b:real"] CONVEX_HALFSPACE_GT) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, dot, SUM_2, DIMINDEX_2, ← GSYM RE_DEF, ← GSYM IM_DEF] THEN
    REWRITE_TAC [ii, RE_CX, IM_CX, RE, IM, IN_ELIM_THM] THEN REAL_ARITH_TAC)

  let CONVEX_HALFSPACE_RE_LE ← prove
   r"!b. convex {z | Re(z) <= b}"
   (GEN_TAC THEN MP_TAC (← ISPECL [← q r"Cx(&1)", ← q r"b:real"] CONVEX_HALFSPACE_LE) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, dot, SUM_2, DIMINDEX_2, ← GSYM RE_DEF, ← GSYM IM_DEF] THEN
    REWRITE_TAC [ii, RE_CX, IM_CX, RE, IM, IN_ELIM_THM] THEN REAL_ARITH_TAC)

  let CONVEX_HALFSPACE_RE_LT ← prove
   r"!b. convex {z | Re(z) < b}"
   (GEN_TAC THEN MP_TAC (← ISPECL [← q r"Cx(&1)", ← q r"b:real"] CONVEX_HALFSPACE_LT) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, dot, SUM_2, DIMINDEX_2, ← GSYM RE_DEF, ← GSYM IM_DEF] THEN
    REWRITE_TAC [ii, RE_CX, IM_CX, RE, IM, IN_ELIM_THM] THEN REAL_ARITH_TAC)

  let CONVEX_HALFSPACE_IM_GE ← prove
   r"!b. convex {z | Im(z) >= b}"
   (GEN_TAC THEN MP_TAC (← ISPECL [← q r"ii", ← q r"b:real"] CONVEX_HALFSPACE_GE) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, dot, SUM_2, DIMINDEX_2, ← GSYM RE_DEF, ← GSYM IM_DEF] THEN
    REWRITE_TAC [ii, RE_CX, IM_CX, RE, IM, IN_ELIM_THM] THEN REAL_ARITH_TAC)

  let CONVEX_HALFSPACE_IM_GT ← prove
   r"!b. convex {z | Im(z) > b}"
   (GEN_TAC THEN MP_TAC (← ISPECL [← q r"ii", ← q r"b:real"] CONVEX_HALFSPACE_GT) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, dot, SUM_2, DIMINDEX_2, ← GSYM RE_DEF, ← GSYM IM_DEF] THEN
    REWRITE_TAC [ii, RE_CX, IM_CX, RE, IM, IN_ELIM_THM] THEN REAL_ARITH_TAC)

  let CONVEX_HALFSPACE_IM_LE ← prove
   r"!b. convex {z | Im(z) <= b}"
   (GEN_TAC THEN MP_TAC (← ISPECL [← q r"ii", ← q r"b:real"] CONVEX_HALFSPACE_LE) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, dot, SUM_2, DIMINDEX_2, ← GSYM RE_DEF, ← GSYM IM_DEF] THEN
    REWRITE_TAC [ii, RE_CX, IM_CX, RE, IM, IN_ELIM_THM] THEN REAL_ARITH_TAC)

  let CONVEX_HALFSPACE_IM_LT ← prove
   r"!b. convex {z | Im(z) < b}"
   (GEN_TAC THEN MP_TAC (← ISPECL [← q r"ii", ← q r"b:real"] CONVEX_HALFSPACE_LT) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, dot, SUM_2, DIMINDEX_2, ← GSYM RE_DEF, ← GSYM IM_DEF] THEN
    REWRITE_TAC [ii, RE_CX, IM_CX, RE, IM, IN_ELIM_THM] THEN REAL_ARITH_TAC)

  let CONVEX_HALFSPACE_RE_SGN ← prove
   r"!b. convex {z | real_sgn(Re z) = b}"
   (REWRITE_TAC [RE_DEF, CONVEX_HALFSPACE_COMPONENT_SGN])

  let CONVEX_HALFSPACE_IM_SGN ← prove
   r"!b. convex {z | real_sgn(Im z) = b}"
   (REWRITE_TAC [IM_DEF, CONVEX_HALFSPACE_COMPONENT_SGN])

  let COMPLEX_IN_BALL_0 ← prove
   r"!v r. v IN ball(Cx(&0),r) <=> norm v < r"
   (REWRITE_TAC [← GSYM COMPLEX_VEC_0, IN_BALL_0])

  let COMPLEX_IN_CBALL_0 ← prove
   r"!v r. v IN cball(Cx(&0),r) <=> norm v <= r"
   (REWRITE_TAC [← GSYM COMPLEX_VEC_0, IN_CBALL_0])

  let COMPLEX_IN_SPHERE_0 ← prove
   r"!v r. v IN sphere(Cx(&0),r) <=> norm v = r"
   (REWRITE_TAC [← GSYM COMPLEX_VEC_0, IN_SPHERE_0])

  let IN_BALL_RE ← prove
   r"!x z e. x IN ball(z,e) ==> abs(Re(x) - Re(z)) < e"
   (REPEAT GEN_TAC THEN REWRITE_TAC [IN_BALL, dist] THEN
    MP_TAC (← SPEC (← q r"z - x:complex") COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC [RE_SUB] THEN REAL_ARITH_TAC)

  let IN_BALL_IM ← prove
   r"!x z e. x IN ball(z,e) ==> abs(Im(x) - Im(z)) < e"
   (REPEAT GEN_TAC THEN REWRITE_TAC [IN_BALL, dist] THEN
    MP_TAC (← SPEC (← q r"z - x:complex") COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC [IM_SUB] THEN REAL_ARITH_TAC)

  let IN_CBALL_RE ← prove
   r"!x z e. x IN cball(z,e) ==> abs(Re(x) - Re(z)) <= e"
   (REPEAT GEN_TAC THEN REWRITE_TAC [IN_CBALL, dist] THEN
    MP_TAC (← SPEC (← q r"z - x:complex") COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC [RE_SUB] THEN REAL_ARITH_TAC)

  let IN_CBALL_IM ← prove
   r"!x z e. x IN cball(z,e) ==> abs(Im(x) - Im(z)) <= e"
   (REPEAT GEN_TAC THEN REWRITE_TAC [IN_CBALL, dist] THEN
    MP_TAC (← SPEC (← q r"z - x:complex") COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC [IM_SUB] THEN REAL_ARITH_TAC)

  let CLOSED_REAL_SET ← prove
   r"closed {z | real z}"
   (REWRITE_TAC [CLOSED_HALFSPACE_IM_EQ, real])

  let CLOSED_REAL ← prove
   r"closed real"
   (GEN_REWRITE_TAC RAND_CONV [← SET_RULE (← q r"s = {x | s x}")] THEN
    REWRITE_TAC [CLOSED_REAL_SET])

  let UNBOUNDED_REAL ← prove
   r"~(bounded real)"
   (REWRITE_TAC [bounded, IN, REAL_EXISTS, LEFT_IMP_EXISTS_THM] THEN
    MESON_TAC [COMPLEX_NORM_CX, ← REAL_ARITH (← q r"~(abs(abs B + &1) <= B)")])

  let CONNECTED_REAL ← prove
   r"connected real"
   (SIMP_TAC [CONVEX_REAL, CONVEX_CONNECTED])

  let PATH_CONNECTED_REAL ← prove
   r"path_connected real"
   (SIMP_TAC [CONVEX_REAL, CONVEX_IMP_PATH_CONNECTED])

  let TRIVIAL_LIMIT_WITHIN_REAL ← prove
   r"!z. trivial_limit (at z within real) <=> ~(real z)"
   (GEN_TAC THEN REWRITE_TAC [TRIVIAL_LIMIT_WITHIN] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC RAND_CONV [← GSYM IN] THEN
    MATCH_MP_TAC CONNECTED_IMP_PERFECT_CLOSED THEN
    REWRITE_TAC [CONNECTED_REAL, CLOSED_REAL] THEN
    MESON_TAC [UNBOUNDED_REAL, BOUNDED_SING])

  pure { CLOSED_HALFSPACE_RE_GE, CLOSED_HALFSPACE_RE_LE, CLOSED_HALFSPACE_RE_EQ,
         OPEN_HALFSPACE_RE_GT, OPEN_HALFSPACE_RE_LT, CLOSED_HALFSPACE_IM_GE,
         CLOSED_HALFSPACE_IM_LE, CLOSED_HALFSPACE_IM_EQ, OPEN_HALFSPACE_IM_GT,
         OPEN_HALFSPACE_IM_LT, CONVEX_HALFSPACE_RE_GE, CONVEX_HALFSPACE_RE_GT,
         CONVEX_HALFSPACE_RE_LE, CONVEX_HALFSPACE_RE_LT, CONVEX_HALFSPACE_IM_GE,
         CONVEX_HALFSPACE_IM_GT, CONVEX_HALFSPACE_IM_LE, CONVEX_HALFSPACE_IM_LT,
         CONVEX_HALFSPACE_RE_SGN, CONVEX_HALFSPACE_IM_SGN, COMPLEX_IN_BALL_0,
         COMPLEX_IN_CBALL_0, COMPLEX_IN_SPHERE_0, IN_BALL_RE, IN_BALL_IM, IN_CBALL_RE,
         IN_CBALL_IM, CLOSED_REAL_SET, CLOSED_REAL, UNBOUNDED_REAL, CONNECTED_REAL,
         PATH_CONNECTED_REAL, TRIVIAL_LIMIT_WITHIN_REAL }
/- ------------------------------------------------------------------------- -/
/- Complex-specific uniform limit composition theorems; the usual            -/
/- non-uniform versions; mapping real limits between C and R^1; special      -/
/- cases of null limits; bounds for the components of limits; the case       -/
/- analysis for the limit of a reciprocal.  (canal.ml 215-594)              -/
/- ------------------------------------------------------------------------- -/

structure KNB where
  UNIFORM_LIM_COMPLEX_MUL : thm
  UNIFORM_LIM_COMPLEX_INV : thm
  UNIFORM_LIM_COMPLEX_DIV : thm
  LIM_COMPLEX_MUL : thm
  LIM_COMPLEX_INV : thm
  LIM_COMPLEX_DIV : thm
  LIM_COMPLEX_POW : thm
  LIM_COMPLEX_LMUL : thm
  LIM_COMPLEX_RMUL : thm
  LIM_CX_LIFT : thm
  SERIES_CX_LIFT : thm
  LIM_INFINITY_POSINFINITY_CX : thm
  LIM_NULL_COMPLEX : thm
  LIM_NULL_COMPLEX_NORM : thm
  LIM_NULL_COMPLEX_NEG : thm
  LIM_NULL_COMPLEX_ADD : thm
  LIM_NULL_COMPLEX_SUB : thm
  LIM_NULL_COMPLEX_MUL : thm
  LIM_NULL_COMPLEX_LMUL : thm
  LIM_NULL_COMPLEX_RMUL : thm
  LIM_NULL_COMPLEX_POW : thm
  SUMS_COMPLEX_0 : thm
  LIM_NULL_COMPLEX_RMUL_BOUNDED : thm
  LIM_NULL_COMPLEX_LMUL_BOUNDED : thm
  LIM_RE_UBOUND : thm
  LIM_RE_LBOUND : thm
  LIM_IM_UBOUND : thm
  LIM_IM_LBOUND : thm
  LIM_COMPLEX_INV_NONDEGENERATE : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupKNB [HolBase] (D : CanalDeps) : ExceptT String IO KNB := do
  -- @@SCOPE BEGIN
  let { complex_div, complex_pow, IM_DEF, RE_DEF, .. } := D.cxa
  let { COMPLEX_ADD_LID, COMPLEX_MUL_LZERO, COMPLEX_MUL_SYM, COMPLEX_NEG_0,
        COMPLEX_SUB_LZERO, COMPLEX_SUB_REFL, COMPLEX_SUB_RZERO, .. } := D.cxb
  let { COMPLEX_ENTIRE, COMPLEX_NORM_CX, COMPLEX_POW_ZERO, COMPLEX_VEC_0, DIST_CX,
        .. } := D.cxc
  let { COMPLEX_RING, .. } := D.cxd
  let { COMPLEX_FIELD, COMPLEX_INV_0, .. } := D.cxe
  let { COMPLEX_INV_EQ_0, COMPLEX_NORM_0, COMPLEX_NORM_DIV, COMPLEX_NORM_INV,
        COMPLEX_NORM_MUL, COMPLEX_NORM_NZ, .. } := D.cxf
  let { BILINEAR_COMPLEX_MUL, .. } := D.cxh
  let { VSUM_CX, .. } := D.cxi
  let { CONNECTED_PUNCTURED_BALL, .. } := D.qpaths
  let { LIM_AT_INFINITY, SUMS_0, UNIFORM_LIM_BILINEAR, .. } := D.qtopology
  let { LIM_COMPONENT_LBOUND, LIM_COMPONENT_UBOUND, .. } := D.ms.qtopology2
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INDUCT_TAC, MESON_TAC, NORM_ARITH, REAL_ARITH,
        REAL_RAT_REDUCE_CONV, .. } := D.cx.cvx
  let { LIM_AT_POSINFINITY, LIM_NEG, .. } := D.ms.ig.qtopology
  let { ARITH, CONTRAPOS_THM, DIMINDEX_2, DISJ_SYM, FINITE_INTER, FINITE_NUMSEG,
        FORALL_AND_THM, .. } := D.cx.cvx.core1
  let { FORALL_IN_IMAGE, IMP_CONJ, IMP_IMP, IN_DELETE, INTER_SUBSET, .. } := D.cx.cvx.core2
  let { IN_IMAGE, IN_INTER, LEFT_IMP_EXISTS_THM, MONO_FORALL, NOT_EXISTS_THM,
        NOT_FORALL_THM, NOT_IMP, .. } := D.cx.cvx.core3
  let { REAL_LE_INV2, REAL_LE_LMUL_EQ, REAL_LE_MUL2, REAL_LE_REFL, REAL_LT_01,
        REAL_LT_IMP_LE, REAL_LT_LDIV_EQ, REAL_LT_MIN, REAL_LT_MUL, REAL_LT_REFL,
        REAL_LTE_TRANS, .. } := D.cx.cvx.core4
  let { REAL_POW_LT, RIGHT_FORALL_IMP_THM, SUBSET, .. } := D.cx.cvx.core5
  let { o_DEF, o_THM, real_ge, .. } := D.cx.cvx.core6
  let { REAL_HALF, .. } := D.cx.cvx.misc
  let { DIST_LIFT, .. } := D.cx.cvx.vec1
  let { LIFT_CMUL, LIFT_DROP, LIFT_EQ, NORM_EQ_0, .. } := D.cx.cvx.vec2
  let { NORM_LIFT, NORM_NEG, NORM_POS_LT, NORM_SUB, REAL_ABS_NORM, .. } := D.cx.cvx.vec3
  let { dist, VECTOR_SUB_EQ, .. } := D.cx.cvx.vec4
  let { EVENTUALLY_MONO, EVENTUALLY_TRUE, .. } := D.cx.cvx.met
  let { CONNECTED_CONTINUOUS_IMAGE, .. } := D.cx.cvx.top2
  let { CONTINUOUS_ON_LIFT_NORM_COMPOSE, CONTINUOUS_ON_SUBSET, .. } := D.cx.cvx.top3
  let { IN_BALL, IS_INTERVAL_1, LIM_ADD, LIM_CONST, LIM_NULL_VMUL_BOUNDED, LIM_SUB,
        OPEN_BALL, .. } := D.cx.cvx.top4
  let { OPEN_INTER, .. } := D.cx.cvx.top5
  let { REAL_INV_INV, .. } := D.ms.ig.dv.qsession
  let { LIM_AT, LIM_BILINEAR, .. } := D.ms.ig.dv.qtopology1
  let { LIM_NULL, LIM_NULL_NORM, open_def, sums, .. } := D.ms.ig.dv.qtopology2
  let { IS_INTERVAL_CONNECTED_1, .. } := D.ms.ig.dv.dg.qconvex
  let { EVENTUALLY_AND, .. } := D.ms.ig.dv.dg.qmetric
  let { tendsto, .. } := D.ms.ig.dv.dg.qtopology2
  let { LIFT_SUM, .. } := D.ms.ig.dv.dg.qvec
  -- @@SCOPE END

  let UNIFORM_LIM_COMPLEX_MUL ← prove
   r"!net:(A)net P f g l m b1 b2.
        eventually (\x. !n. P n ==> norm(l n) <= b1) net /\
        eventually (\x. !n. P n ==> norm(m n) <= b2) net /\
        (!e. &0 < e
             ==> eventually (\x. !n:B. P n ==> norm(f n x - l n) < e) net) /\
        (!e. &0 < e
             ==> eventually (\x. !n. P n ==> norm(g n x - m n) < e) net)
        ==> !e. &0 < e
                ==> eventually
                     (\x. !n. P n
                              ==> norm(f n x * g n x - l n * m n) < e)
                     net"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o CONJ BILINEAR_COMPLEX_MUL) THEN
    REWRITE_TAC [UNIFORM_LIM_BILINEAR])

  let UNIFORM_LIM_COMPLEX_INV ← prove
   r"!net:(A)net P f l b.
        (!e. &0 < e
             ==> eventually (\x. !n:B. P n ==> norm(f n x - l n) < e) net) /\
        &0 < b /\ eventually (\x. !n. P n ==> b <= norm(l n)) net
        ==> !e. &0 < e
                ==> eventually
                    (\x. !n. P n ==> norm(inv(f n x) - inv(l n)) < e) net"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC EVENTUALLY_MONO THEN
    EXISTS_TAC
     (← q r"\x. !n. P n ==> b <= norm(l n) /\
                    b / &2 <= norm((f:B->A->complex) n x) /\
                    norm(f n x - l n) < e * b pow 2 / &2") THEN
    REWRITE_TAC [← TAUT (← q r"(p ==> q /\ r) <=> (p ==> q) /\ (p ==> r)")] THEN
    REWRITE_TAC [FORALL_AND_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN X_GEN_TAC (← q r"n:B") THEN DISCH_TAC THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"n:B")) THEN ASM_REWRITE_TAC []) THEN
      REPEAT DISCH_TAC THEN
      SUBGOAL_THEN (← q r"~((f:B->A->complex) n x = Cx(&0)) /\ ~(l n = Cx(&0))")
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC (REWRITE_RULE [COMPLEX_NORM_CX]) THEN ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      ASM_SIMP_TAC [← ExceptT.mk (COMPLEX_FIELD
       (← q r"~(x = Cx(&0)) /\ ~(y = Cx(&0))
        ==> inv x - inv y = (y - x) / (x * y)"))] THEN
      ASM_SIMP_TAC [COMPLEX_NORM_DIV, REAL_LT_LDIV_EQ, COMPLEX_NORM_NZ,
                    COMPLEX_ENTIRE] THEN
      ONCE_REWRITE_TAC [NORM_SUB] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          REAL_LTE_TRANS)) THEN
      ASM_SIMP_TAC [REAL_LE_LMUL_EQ, ← REAL_ARITH (← q r"b pow 2 / &2 = b / &2 * b")] THEN
      REWRITE_TAC [COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REAL_ARITH_TAC,
      ASM_REWRITE_TAC [EVENTUALLY_AND] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"b / &2")) THEN
        ASM_REWRITE_TAC [REAL_HALF] THEN
        FIRST_X_ASSUM (fun th => tactic_of do
          pure (MP_TAC th THEN REWRITE_TAC [IMP_IMP] THEN
                GEN_REWRITE_TAC LAND_CONV [← GSYM EVENTUALLY_AND])) THEN
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] EVENTUALLY_MONO) THEN
        REWRITE_TAC [] THEN
        ASM_MESON_TAC [← NORM_ARITH
         (← q r"b <= norm l /\ norm(f - l) < b / &2 ==> b / &2 <= norm f")],
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC [REAL_HALF, REAL_POW_LT, REAL_LT_MUL]]])

  let UNIFORM_LIM_COMPLEX_DIV ← prove
   r"!net:(A)net P f g l m b1 b2.
        eventually (\x. !n. P n ==> norm(l n) <= b1) net /\
        &0 < b2 /\ eventually (\x. !n. P n ==> b2 <= norm(m n)) net /\
        (!e. &0 < e
             ==> eventually (\x. !n:B. P n ==> norm(f n x - l n) < e) net) /\
        (!e. &0 < e
             ==> eventually (\x. !n. P n ==> norm(g n x - m n) < e) net)
        ==> !e. &0 < e
                ==> eventually
                     (\x. !n. P n
                              ==> norm(f n x / g n x - l n / m n) < e)
                     net"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [complex_div] THEN MATCH_MP_TAC UNIFORM_LIM_COMPLEX_MUL THEN
    MAP_EVERY EXISTS_TAC [← q r"b1:real", ← q r"inv(b2):real"] THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM (CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o CONJUNCT1) o CONJUNCT2) THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] EVENTUALLY_MONO) THEN
      GEN_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC MONO_FORALL THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC [COMPLEX_NORM_INV] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC [],
      MATCH_MP_TAC UNIFORM_LIM_COMPLEX_INV THEN
      EXISTS_TAC (← q r"b2:real") THEN ASM_REWRITE_TAC []])

  let LIM_COMPLEX_MUL ← prove
   r"!net:(A)net f g l m.
         (f --> l) net /\ (g --> m) net ==> ((\x. f x * g x) --> l * m) net"
   (SIMP_TAC [LIM_BILINEAR, BILINEAR_COMPLEX_MUL])

  let LIM_COMPLEX_INV ← prove
   r"!net:(A)net f g l m.
         (f --> l) net /\ ~(l = Cx(&0)) ==> ((\x. inv(f x)) --> inv(l)) net"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL
     [← q r"net:(A)net", ← q r"\x:one. T",
      ← q r"\n:one. (f:A->complex)",
      ← q r"\n:one. (l:complex)",
      ← q r"norm(l:complex)"] UNIFORM_LIM_COMPLEX_INV) THEN
    ASM_REWRITE_TAC [REAL_LE_REFL, EVENTUALLY_TRUE] THEN
    ASM_REWRITE_TAC [← GSYM dist, ← GSYM tendsto, COMPLEX_NORM_NZ])

  let LIM_COMPLEX_DIV ← prove
   r"!net:(A)net f g l m.
         (f --> l) net /\ (g --> m) net /\ ~(m = Cx(&0))
         ==> ((\x. f x / g x) --> l / m) net"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [complex_div] THEN
    MATCH_MP_TAC LIM_COMPLEX_MUL THEN ASM_SIMP_TAC [LIM_COMPLEX_INV])

  let LIM_COMPLEX_POW ← prove
   r"!net:(A)net f l n.
         (f --> l) net ==> ((\x. f(x) pow n) --> l pow n) net"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    INDUCT_TAC THEN ASM_SIMP_TAC [LIM_COMPLEX_MUL, complex_pow, LIM_CONST])

  let LIM_COMPLEX_LMUL ← prove
   r"!f l c. (f --> l) net ==> ((\x. c * f x) --> c * l) net"
   (SIMP_TAC [LIM_COMPLEX_MUL, LIM_CONST])

  let LIM_COMPLEX_RMUL ← prove
   r"!f l c. (f --> l) net ==> ((\x. f x * c) --> l * c) net"
   (SIMP_TAC [LIM_COMPLEX_MUL, LIM_CONST])

  let LIM_CX_LIFT ← prove
   r"!net f l.
     ((\x. Cx(f x)) --> Cx l) net <=> ((\x. lift(f x)) --> lift l) net"
   (REWRITE_TAC [tendsto, DIST_LIFT, DIST_CX])

  let SERIES_CX_LIFT ← prove
   r"!f s x.
     ((\x. Cx(f x)) sums (Cx x)) s <=> ((\x. lift(f x)) sums (lift x)) s"
   (SIMP_TAC [sums, LIM_CX_LIFT, VSUM_CX, FINITE_INTER, FINITE_NUMSEG] THEN
    REWRITE_TAC [← REWRITE_RULE [o_DEF] (← GSYM LIFT_SUM)])

  let LIM_INFINITY_POSINFINITY_CX ← prove
   r"!f l:real^N. (f --> l) at_infinity ==> ((f o Cx) --> l) at_posinfinity"
   (REWRITE_TAC [LIM_AT_INFINITY, LIM_AT_POSINFINITY, o_THM] THEN
    MESON_TAC [COMPLEX_NORM_CX, ← REAL_ARITH (← q r"x >= b ==> abs(x) >= b")])

  let LIM_NULL_COMPLEX ← prove
   r"!net f. (f --> l) net <=> ((\x. f x - l) --> Cx(&0)) net"
   (REWRITE_TAC [← GSYM COMPLEX_VEC_0, ← GSYM LIM_NULL])

  let LIM_NULL_COMPLEX_NORM ← prove
   r"!net f. (f --> Cx(&0)) net <=> ((\x. Cx(norm(f x))) --> Cx(&0)) net"
   (REWRITE_TAC [← GSYM COMPLEX_VEC_0] THEN
    ONCE_REWRITE_TAC [LIM_NULL_NORM] THEN
    REWRITE_TAC [COMPLEX_NORM_CX, REAL_ABS_NORM])

  let LIM_NULL_COMPLEX_NEG ← prove
   r"!net f. (f --> Cx(&0)) net ==> ((\x. --(f x)) --> Cx(&0)) net"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP LIM_NEG) THEN
    REWRITE_TAC [COMPLEX_NEG_0])

  let LIM_NULL_COMPLEX_ADD ← prove
   r"!net f g. (f --> Cx(&0)) net /\ (g --> Cx(&0)) net
             ==> ((\x. f x + g x) --> Cx(&0)) net"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP LIM_ADD) THEN
    REWRITE_TAC [COMPLEX_ADD_LID])

  let LIM_NULL_COMPLEX_SUB ← prove
   r"!net f g. (f --> Cx(&0)) net /\ (g --> Cx(&0)) net
             ==> ((\x. f x - g x) --> Cx(&0)) net"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP LIM_SUB) THEN
    REWRITE_TAC [COMPLEX_SUB_REFL])

  let LIM_NULL_COMPLEX_MUL ← prove
   r"!net f g. (f --> Cx(&0)) net /\ (g --> Cx(&0)) net
             ==> ((\x. f x * g x) --> Cx(&0)) net"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP LIM_COMPLEX_MUL) THEN
    REWRITE_TAC [COMPLEX_MUL_LZERO])

  let LIM_NULL_COMPLEX_LMUL ← prove
   r"!net f c. (f --> Cx(&0)) net ==> ((\x. c * f x) --> Cx(&0)) net"
   (REPEAT STRIP_TAC THEN
    SUBST1_TAC (← ExceptT.mk (COMPLEX_RING (← q r"Cx(&0) = c * Cx(&0)"))) THEN
    ASM_SIMP_TAC [LIM_COMPLEX_LMUL])

  let LIM_NULL_COMPLEX_RMUL ← prove
   r"!net f c. (f --> Cx(&0)) net ==> ((\x. f x * c) --> Cx(&0)) net"
   (REPEAT STRIP_TAC THEN
    SUBST1_TAC (← ExceptT.mk (COMPLEX_RING (← q r"Cx(&0) = Cx(&0) * c"))) THEN
    ASM_SIMP_TAC [LIM_COMPLEX_RMUL])

  let LIM_NULL_COMPLEX_POW ← prove
   r"!net f n. (f --> Cx(&0)) net /\ ~(n = 0)
             ==> ((\x. (f x) pow n) --> Cx(&0)) net"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"n:num") o MATCH_MP LIM_COMPLEX_POW) THEN
    ASM_REWRITE_TAC [COMPLEX_POW_ZERO])

  let SUMS_COMPLEX_0 ← prove
   r"!f s. (!n. n IN s ==> f n = Cx(&0)) ==> (f sums Cx(&0)) s"
   (REWRITE_TAC [← GSYM COMPLEX_VEC_0, SUMS_0])

  let LIM_NULL_COMPLEX_RMUL_BOUNDED ← prove
   r"!net f g B.
        (f --> Cx(&0)) net /\
        eventually (\a. f a = Cx(&0) \/ norm(g a) <= B) net
        ==> ((\z. f(z) * g(z)) --> Cx(&0)) net"
   (REWRITE_TAC [← GSYM COMPLEX_VEC_0] THEN
    ONCE_REWRITE_TAC [LIM_NULL_NORM] THEN
    REWRITE_TAC [LIFT_CMUL, COMPLEX_NORM_MUL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_NULL_VMUL_BOUNDED THEN
    EXISTS_TAC (← q r"B:real") THEN
    ASM_REWRITE_TAC [o_DEF, NORM_LIFT, REAL_ABS_NORM, NORM_EQ_0])

  let LIM_NULL_COMPLEX_LMUL_BOUNDED ← prove
   r"!net f g B.
        eventually (\a. norm(f a) <= B \/ g a = Cx(&0)) net /\
        (g --> Cx(&0)) net
        ==> ((\z. f(z) * g(z)) --> Cx(&0)) net"
   (ONCE_REWRITE_TAC [DISJ_SYM, COMPLEX_MUL_SYM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC LIM_NULL_COMPLEX_RMUL_BOUNDED THEN
    ASM_MESON_TAC [])

  let LIM_RE_UBOUND ← prove
   r"!net:(A)net f l b.
        ~(trivial_limit net) /\ (f --> l) net /\
        eventually (\x. Re(f x) <= b) net
        ==> Re(l) <= b"
   (REWRITE_TAC [RE_DEF] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"net:(A)net", ← q r"f:A->complex", ← q r"l:complex",
                      ← q r"b:real", ← q r"1"]
                  LIM_COMPONENT_UBOUND) THEN
    ASM_REWRITE_TAC [DIMINDEX_2, ARITH])

  let LIM_RE_LBOUND ← prove
   r"!net:(A)net f l b.
        ~(trivial_limit net) /\ (f --> l) net /\
        eventually (\x. b <= Re(f x)) net
        ==> b <= Re(l)"
   (REWRITE_TAC [RE_DEF] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"net:(A)net", ← q r"f:A->complex", ← q r"l:complex",
                      ← q r"b:real", ← q r"1"]
                  LIM_COMPONENT_LBOUND) THEN
    ASM_REWRITE_TAC [DIMINDEX_2, ARITH])

  let LIM_IM_UBOUND ← prove
   r"!net:(A)net f l b.
        ~(trivial_limit net) /\ (f --> l) net /\
        eventually (\x. Im(f x) <= b) net
        ==> Im(l) <= b"
   (REWRITE_TAC [IM_DEF] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"net:(A)net", ← q r"f:A->complex", ← q r"l:complex",
                      ← q r"b:real", ← q r"2"]
                  LIM_COMPONENT_UBOUND) THEN
    ASM_REWRITE_TAC [DIMINDEX_2, ARITH])

  let LIM_IM_LBOUND ← prove
   r"!net:(A)net f l b.
        ~(trivial_limit net) /\ (f --> l) net /\
        eventually (\x. b <= Im(f x)) net
        ==> b <= Im(l)"
   (REWRITE_TAC [IM_DEF] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"net:(A)net", ← q r"f:A->complex", ← q r"l:complex",
                      ← q r"b:real", ← q r"2"]
                  LIM_COMPONENT_LBOUND) THEN
    ASM_REWRITE_TAC [DIMINDEX_2, ARITH])

  let LIM_COMPLEX_INV_NONDEGENERATE ← prove
   r"!f:real^N->complex s a l.
        2 <= dimindex(:N) /\
        a IN s /\ open s /\
        f continuous_on (s DELETE a) /\
        ((inv o f) --> l) (at a)
        ==> ?t. open t /\ t SUBSET s /\
                ((!x. x IN t DELETE a ==> f x = Cx(&0)) /\ l = Cx(&0) \/
                 (!x. x IN t DELETE a ==> ~(f x = Cx(&0))))"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC
     (← q r"!e. &0 < e ==> ?z:real^N. norm(z - a) < e /\ ~(z = a) /\ f(z) = Cx(&0)")
    THENL
     [ALL_TAC,
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
      REWRITE_TAC [NOT_IMP, NOT_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
      REWRITE_TAC [← TAUT (← q r"~(a /\ b) <=> a ==> ~b")] THEN
      X_GEN_TAC (← q r"e:real") THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"s INTER ball(a:real^N,e)") THEN
      ASM_SIMP_TAC [INTER_SUBSET, OPEN_INTER, OPEN_BALL] THEN DISJ2_TAC THEN
      REWRITE_TAC [IN_DELETE, IN_INTER, IN_BALL, dist] THEN
      ASM_MESON_TAC [NORM_SUB]] THEN
    SUBGOAL_THEN (← q r"l = Cx(&0)") SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [LIM_AT]) THEN
      ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"norm(l:complex)")) THEN
      ASM_SIMP_TAC [COMPLEX_NORM_NZ, dist] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"d:real")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"z:real^N") STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"z:real^N")) THEN
      ASM_REWRITE_TAC [NORM_POS_LT, o_THM, VECTOR_SUB_EQ, COMPLEX_INV_0] THEN
      REWRITE_TAC [COMPLEX_SUB_LZERO, NORM_NEG, REAL_LT_REFL],
      REWRITE_TAC []] THEN
    SUBGOAL_THEN
     (← q r"?e. &0 < e /\
          !z:real^N. norm(z - a) < e /\ ~(z = a)
                     ==> z IN s /\ (f z = Cx(&0) \/ norm(f z) >= &1)")
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [LIM_AT]) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"&1")) THEN REWRITE_TAC [REAL_LT_01] THEN
      REWRITE_TAC [o_THM, VECTOR_SUB_EQ, dist, COMPLEX_SUB_RZERO] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [open_def]) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"a:real^N")) THEN ASM_REWRITE_TAC [dist] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"e:real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"min d e:real") THEN ASM_SIMP_TAC [REAL_LT_MIN] THEN
      X_GEN_TAC (← q r"z:real^N") THEN DISCH_TAC THEN
      REWRITE_TAC [← TAUT (← q r"p \/ q <=> ~p ==> q")] THEN STRIP_TAC THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"z:real^N"))) THEN
      ASM_REWRITE_TAC [NORM_POS_LT, VECTOR_SUB_EQ] THEN REPEAT DISCH_TAC THEN
      SUBST1_TAC (← REAL_ARITH (← q r"&1 = inv(&1)")) THEN REWRITE_TAC [real_ge] THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_INV_INV] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_SIMP_TAC [← GSYM COMPLEX_NORM_INV, REAL_LT_IMP_LE] THEN
      ASM_REWRITE_TAC [NORM_POS_LT, COMPLEX_INV_EQ_0, COMPLEX_VEC_0],
      ALL_TAC] THEN
    EXISTS_TAC (← q r"ball(a:real^N,e)") THEN
    ASM_REWRITE_TAC [OPEN_BALL, SUBSET, IN_DELETE, IN_BALL, dist] THEN
    CONJ_TAC THENL [ASM_MESON_TAC [NORM_SUB], DISJ1_TAC] THEN
    X_GEN_TAC (← q r"z:real^N") THEN STRIP_TAC THEN
    ASM_CASES_TAC (← q r"f(z:real^N) = Cx(&0)") THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e:real")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"w:real^N") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     (← q r"connected (IMAGE (lift o norm o (f:real^N->complex)) (ball(a,e) DELETE a))")
    MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC [CONNECTED_PUNCTURED_BALL, o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC [SUBSET, IN_DELETE, IN_BALL, dist] THEN
      ASM_MESON_TAC [NORM_SUB],
      REWRITE_TAC [← GSYM IS_INTERVAL_CONNECTED_1]] THEN
    REWRITE_TAC [IS_INTERVAL_1, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC [FORALL_IN_IMAGE, IN_DELETE, IN_BALL, dist] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"w:real^N")) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [NORM_SUB], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"z:real^N")) THEN
    ASM_REWRITE_TAC [o_THM, LIFT_DROP, COMPLEX_NORM_0] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"lift(&1 / &2)")) THEN
    ASM_REWRITE_TAC [LIFT_DROP, NOT_IMP] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
     [MATCH_MP_TAC (← REAL_ARITH (← q r"x >= &1 ==> &1 / &2 <= x")) THEN
      ASM_MESON_TAC [NORM_SUB],
      REWRITE_TAC [IN_IMAGE, o_THM, LIFT_EQ, IN_BALL, IN_DELETE, dist] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"x:real^N") (STRIP_ASSUME_TAC o GSYM)) THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real^N")) THEN
      ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [NORM_SUB] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (SUBST_ALL_TAC o CONJUNCT2) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [COMPLEX_NORM_0]) THEN ASM_REAL_ARITH_TAC])

  pure { UNIFORM_LIM_COMPLEX_MUL, UNIFORM_LIM_COMPLEX_INV, UNIFORM_LIM_COMPLEX_DIV,
         LIM_COMPLEX_MUL, LIM_COMPLEX_INV, LIM_COMPLEX_DIV, LIM_COMPLEX_POW,
         LIM_COMPLEX_LMUL, LIM_COMPLEX_RMUL, LIM_CX_LIFT, SERIES_CX_LIFT,
         LIM_INFINITY_POSINFINITY_CX, LIM_NULL_COMPLEX, LIM_NULL_COMPLEX_NORM,
         LIM_NULL_COMPLEX_NEG, LIM_NULL_COMPLEX_ADD, LIM_NULL_COMPLEX_SUB,
         LIM_NULL_COMPLEX_MUL, LIM_NULL_COMPLEX_LMUL, LIM_NULL_COMPLEX_RMUL,
         LIM_NULL_COMPLEX_POW, SUMS_COMPLEX_0, LIM_NULL_COMPLEX_RMUL_BOUNDED,
         LIM_NULL_COMPLEX_LMUL_BOUNDED, LIM_RE_UBOUND, LIM_RE_LBOUND, LIM_IM_UBOUND,
         LIM_IM_LBOUND, LIM_COMPLEX_INV_NONDEGENERATE }
/- ------------------------------------------------------------------------- -/
/- Multiplication of complex series; complex-specific continuity closures;   -/
/- writing away the netlimit; "on" variants; uniform versions.              -/
/- (canal.ml 595-823)                                                       -/
/- ------------------------------------------------------------------------- -/

structure KNC where
  SERIES_COMPLEX_LMUL : thm
  SERIES_COMPLEX_RMUL : thm
  SERIES_COMPLEX_DIV : thm
  SUMMABLE_COMPLEX_LMUL : thm
  SUMMABLE_COMPLEX_RMUL : thm
  SUMMABLE_COMPLEX_DIV : thm
  SERIES_COMPLEX_MUL : thm
  SERIES_COMPLEX_MUL_UNIQUE : thm
  SUMMABLE_COMPLEX_MUL_LEFT : thm
  SUMMABLE_COMPLEX_MUL_RIGHT : thm
  CONTINUOUS_COMPLEX_MUL : thm
  CONTINUOUS_COMPLEX_LMUL : thm
  CONTINUOUS_COMPLEX_RMUL : thm
  CONTINUOUS_COMPLEX_INV : thm
  CONTINUOUS_COMPLEX_DIV : thm
  CONTINUOUS_COMPLEX_POW : thm
  CONTINUOUS_CPRODUCT : thm
  CONTINUOUS_COMPLEX_INV_WITHIN : thm
  CONTINUOUS_COMPLEX_INV_AT : thm
  CONTINUOUS_COMPLEX_DIV_WITHIN : thm
  CONTINUOUS_COMPLEX_DIV_AT : thm
  CONTINUOUS_ON_COMPLEX_MUL : thm
  CONTINUOUS_ON_COMPLEX_LMUL : thm
  CONTINUOUS_ON_COMPLEX_RMUL : thm
  CONTINUOUS_ON_COMPLEX_INV : thm
  CONTINUOUS_MAP_COMPLEX_INV : thm
  CONTINUOUS_ON_COMPLEX_DIV : thm
  CONTINUOUS_ON_COMPLEX_POW : thm
  CONTINUOUS_ON_CPRODUCT : thm
  UNIFORMLY_CONTINUOUS_ON_COMPLEX_MUL : thm
  UNIFORMLY_CONTINUOUS_ON_COMPLEX_LMUL : thm
  UNIFORMLY_CONTINUOUS_ON_COMPLEX_RMUL : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupKNC [HolBase] (D : CanalDeps) (BKNB : KNB) : ExceptT String IO KNC := do
  -- @@SCOPE BEGIN
  let { LIM_COMPLEX_DIV, LIM_COMPLEX_INV, LIM_COMPLEX_MUL, LIM_COMPLEX_POW, .. } := BKNB
  let { complex_div, .. } := D.cxa
  let { COMPLEX_MUL_SYM, .. } := D.cxb
  let { BILINEAR_COMPLEX_MUL, LINEAR_COMPLEX_MUL, .. } := D.cxh
  let { CPRODUCT_CLAUSES, .. } := D.cxk
  let { BILINEAR_UNIFORMLY_CONTINUOUS_ON_COMPOSE, continuous, CONTINUOUS_TRIVIAL_LIMIT,
        LINEAR_UNIFORMLY_CONTINUOUS_ON, SERIES_BILINEAR, SERIES_BILINEAR_UNIQUE,
        SERIES_LINEAR, summable, SUMMABLE_BILINEAR_LEFT, SUMMABLE_BILINEAR_RIGHT,
        UNIFORMLY_CONTINUOUS_ON_COMPOSE, .. } := D.qtopology
  let { ASM_MESON_TAC, MESON_TAC, .. } := D.cx.cvx
  let { CONTINUOUS_ON, NETLIMIT_AT, .. } := D.ms.ig.qtopology
  let { ETA_AX, FINITE_INDUCT_STRONG, .. } := D.cx.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_IN_INSERT, IMP_CONJ, .. } := D.cx.cvx.core2
  let { IN_ELIM_THM, .. } := D.cx.cvx.core3
  let { RIGHT_FORALL_IMP_THM, SUBSET, .. } := D.cx.cvx.core5
  let { o_DEF, .. } := D.cx.cvx.core6
  let { CONTINUOUS_CONST, CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN, CONTINUOUS_ON_ID,
        .. } := D.cx.cvx.top3
  let { LIM_CONST, .. } := D.cx.cvx.top4
  let { NETLIMIT_WITHIN, .. } := D.ms.ig.dv.qtopology2
  let { CONTINUOUS_MAP_COMPOSE, CONTINUOUS_MAP_IN_SUBTOPOLOGY, .. } := D.ms.ig.dv.dg.qmetric
  let { CONTINUOUS_MAP_EUCLIDEAN, .. } := D.ms.ig.dv.dg.qtopology1
  -- @@SCOPE END

  let SERIES_COMPLEX_LMUL ← prove
   r"!f l c s. (f sums l) s ==> ((\x. c * f x) sums c * l) s"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_LINEAR THEN
    ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC RAND_CONV [← GSYM ETA_AX] THEN
    REWRITE_TAC [LINEAR_COMPLEX_MUL])

  let SERIES_COMPLEX_RMUL ← prove
   r"!f l c s. (f sums l) s ==> ((\x. f x * c) sums l * c) s"
   (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN REWRITE_TAC [SERIES_COMPLEX_LMUL])

  let SERIES_COMPLEX_DIV ← prove
   r"!f l c s. (f sums l) s ==> ((\x. f x / c) sums (l / c)) s"
   (REWRITE_TAC [complex_div, SERIES_COMPLEX_RMUL])

  let SUMMABLE_COMPLEX_LMUL ← prove
   r"!f c s. summable s f ==> summable s (\x. c * f x)"
   (REWRITE_TAC [summable] THEN MESON_TAC [SERIES_COMPLEX_LMUL])

  let SUMMABLE_COMPLEX_RMUL ← prove
   r"!f c s. summable s f ==> summable s (\x. f x * c)"
   (REWRITE_TAC [summable] THEN MESON_TAC [SERIES_COMPLEX_RMUL])

  let SUMMABLE_COMPLEX_DIV ← prove
   r"!f c s. summable s f ==> summable s (\x. f x / c)"
   (REWRITE_TAC [summable] THEN MESON_TAC [SERIES_COMPLEX_DIV])

  let SERIES_COMPLEX_MUL ← prove
   r"!x y a b.
        (x sums a) (from 0) /\ (y sums b) (from 0) /\
        (summable (from 0) (\n. lift(norm(x n))) \/
         summable (from 0) (\n. lift(norm(y n))))
        ==> ((\n. vsum(0..n) (\i. x i * y(n - i))) sums (a * b))
            (from 0)"
   (MP_TAC (← ISPEC (← q r"( * ):complex->complex->complex") SERIES_BILINEAR) THEN
    REWRITE_TAC [BILINEAR_COMPLEX_MUL])

  let SERIES_COMPLEX_MUL_UNIQUE ← prove
   r"!x y a b c.
        (x sums a) (from 0) /\ (y sums b) (from 0) /\
        ((\n. vsum (0..n) (\i. x i * y(n - i))) sums c) (from 0)
        ==> a * b = c"
   (MP_TAC (← ISPEC (← q r"( * ):complex->complex->complex") SERIES_BILINEAR_UNIQUE) THEN
    REWRITE_TAC [BILINEAR_COMPLEX_MUL])

  let SUMMABLE_COMPLEX_MUL_LEFT ← prove
   r"!x y m n p.
        summable (from m) (\n. lift(norm(x n))) /\ summable (from n) y
        ==> summable (from p) (\n. vsum(0..n) (\i. x i * y(n - i)))"
   (MP_TAC (← ISPEC (← q r"( * ):complex->complex->complex")
       SUMMABLE_BILINEAR_LEFT) THEN
    REWRITE_TAC [BILINEAR_COMPLEX_MUL])

  let SUMMABLE_COMPLEX_MUL_RIGHT ← prove
   r"!x y m n p.
        summable (from m) x /\ summable (from n) (\n. lift(norm(y n)))
        ==> summable (from p) (\n. vsum(0..n) (\i. x i * y(n - i)))"
   (MP_TAC (← ISPEC (← q r"( * ):complex->complex->complex")
       SUMMABLE_BILINEAR_RIGHT) THEN
    REWRITE_TAC [BILINEAR_COMPLEX_MUL])

  let CONTINUOUS_COMPLEX_MUL ← prove
   r"!net f g.
    f continuous net /\ g continuous net ==> (\x. f(x) * g(x)) continuous net"
   (SIMP_TAC [continuous, LIM_COMPLEX_MUL])

  let CONTINUOUS_COMPLEX_LMUL ← prove
   r"!c f net. f continuous net ==> (\x. c * f x) continuous net"
   (SIMP_TAC [CONTINUOUS_COMPLEX_MUL, CONTINUOUS_CONST])

  let CONTINUOUS_COMPLEX_RMUL ← prove
   r"!c f net. f continuous net ==> (\x. f x * c) continuous net"
   (SIMP_TAC [CONTINUOUS_COMPLEX_MUL, CONTINUOUS_CONST])

  let CONTINUOUS_COMPLEX_INV ← prove
   r"!net f.
    f continuous net /\ ~(f(netlimit net) = Cx(&0))
    ==> (\x. inv(f x)) continuous net"
   (SIMP_TAC [continuous, LIM_COMPLEX_INV])

  let CONTINUOUS_COMPLEX_DIV ← prove
   r"!net f g.
    f continuous net /\ g continuous net /\ ~(g(netlimit net) = Cx(&0))
    ==> (\x. f(x) / g(x)) continuous net"
   (SIMP_TAC [continuous, LIM_COMPLEX_DIV])

  let CONTINUOUS_COMPLEX_POW ← prove
   r"!net f n. f continuous net ==> (\x. f(x) pow n) continuous net"
   (SIMP_TAC [continuous, LIM_COMPLEX_POW])

  let CONTINUOUS_CPRODUCT ← prove
   r"!(net:(real^N)net) f k:A->bool.
        FINITE k /\
        (!i. i IN k ==> f i continuous net)
        ==> (\z. cproduct k (\i. f i z)) continuous net"
   (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [CPRODUCT_CLAUSES, CONTINUOUS_CONST, FORALL_IN_INSERT,
              ETA_AX, CONTINUOUS_COMPLEX_MUL])

  let CONTINUOUS_COMPLEX_INV_WITHIN ← prove
   r"!f s a.
    f continuous (at a within s) /\ ~(f a = Cx(&0))
    ==> (\x. inv(f x)) continuous (at a within s)"
   (MESON_TAC [CONTINUOUS_COMPLEX_INV, CONTINUOUS_TRIVIAL_LIMIT,
               NETLIMIT_WITHIN])

  let CONTINUOUS_COMPLEX_INV_AT ← prove
   r"!f a.
    f continuous (at a) /\ ~(f a = Cx(&0))
    ==> (\x. inv(f x)) continuous (at a)"
   (SIMP_TAC [CONTINUOUS_COMPLEX_INV, NETLIMIT_AT])

  let CONTINUOUS_COMPLEX_DIV_WITHIN ← prove
   r"!f g s a.
    f continuous (at a within s) /\ g continuous (at a within s) /\
    ~(g a = Cx(&0))
    ==> (\x. f x / g x) continuous (at a within s)"
   (MESON_TAC [CONTINUOUS_COMPLEX_DIV, CONTINUOUS_TRIVIAL_LIMIT,
               NETLIMIT_WITHIN])

  let CONTINUOUS_COMPLEX_DIV_AT ← prove
   r"!f g a.
    f continuous at a /\ g continuous at a /\ ~(g a = Cx(&0))
    ==> (\x. f x / g x) continuous at a"
   (SIMP_TAC [CONTINUOUS_COMPLEX_DIV, NETLIMIT_AT])

  let CONTINUOUS_ON_COMPLEX_MUL ← prove
   r"!f g s. f continuous_on s /\ g continuous_on s
           ==> (\x. f(x) * g(x)) continuous_on s"
   (REWRITE_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    SIMP_TAC [CONTINUOUS_COMPLEX_MUL])

  let CONTINUOUS_ON_COMPLEX_LMUL ← prove
   r"!f:real^N->complex s. f continuous_on s ==> (\x. c * f(x)) continuous_on s"
   (REWRITE_TAC [CONTINUOUS_ON] THEN SIMP_TAC [LIM_COMPLEX_MUL, LIM_CONST])

  let CONTINUOUS_ON_COMPLEX_RMUL ← prove
   r"!f:real^N->complex s. f continuous_on s ==> (\x. f(x) * c) continuous_on s"
   (REWRITE_TAC [CONTINUOUS_ON] THEN SIMP_TAC [LIM_COMPLEX_MUL, LIM_CONST])

  let CONTINUOUS_ON_COMPLEX_INV ← prove
   r"!f:real^N->complex.
        f continuous_on s /\
        (!x. x IN s ==> ~(f x = Cx(&0)))
        ==> (\x. inv(f x)) continuous_on s"
   (SIMP_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN,
              CONTINUOUS_COMPLEX_INV_WITHIN])

  let CONTINUOUS_MAP_COMPLEX_INV ← prove
   r"!top (f:A->complex).
        continuous_map (top,euclidean) f /\
        (!x. x IN topspace top ==> ~(f x = Cx(&0)))
        ==> continuous_map (top,euclidean) (\x. inv(f x))"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(\x. inv((f:A->complex) x)) = (\w. inv w) o f")
    SUBST1_TAC THENL [REWRITE_TAC [o_DEF], ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC (← q r"subtopology euclidean {w:complex | ~(w = Cx(&0))}") THEN
    ASM_REWRITE_TAC [CONTINUOUS_MAP_IN_SUBTOPOLOGY, CONTINUOUS_MAP_EUCLIDEAN] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [],
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_INV THEN
      REWRITE_TAC [CONTINUOUS_ON_ID, IN_ELIM_THM]])

  let CONTINUOUS_ON_COMPLEX_DIV ← prove
   r"!f g s. f continuous_on s /\ g continuous_on s /\
           (!x. x IN s ==> ~(g x = Cx(&0)))
           ==> (\x. f(x) / g(x)) continuous_on s"
   (REWRITE_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    SIMP_TAC [CONTINUOUS_COMPLEX_DIV_WITHIN])

  let CONTINUOUS_ON_COMPLEX_POW ← prove
   r"!f n s. f continuous_on s ==> (\x. f(x) pow n) continuous_on s"
   (SIMP_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN, CONTINUOUS_COMPLEX_POW])

  let CONTINUOUS_ON_CPRODUCT ← prove
   r"!f k:A->bool s.
        FINITE k /\
        (!i. i IN k ==> f i continuous_on s)
        ==> (\z. cproduct k (\i. f i z)) continuous_on s"
   (SIMP_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN, CONTINUOUS_CPRODUCT])

  let UNIFORMLY_CONTINUOUS_ON_COMPLEX_MUL ← prove
   r"!f g s:real^N->bool.
        f uniformly_continuous_on s /\ g uniformly_continuous_on s /\
        bounded(IMAGE f s) /\ bounded(IMAGE g s)
        ==> (\x. f(x) * g(x)) uniformly_continuous_on s"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL
     [← q r"f:real^N->complex", ← q r"g:real^N->complex",
      ← q r"( * ):complex->complex->complex", ← q r"s:real^N->bool"]
      BILINEAR_UNIFORMLY_CONTINUOUS_ON_COMPOSE) THEN
    ASM_REWRITE_TAC [BILINEAR_COMPLEX_MUL])

  let UNIFORMLY_CONTINUOUS_ON_COMPLEX_LMUL ← prove
   r"!f c s:real^N->bool.
      f uniformly_continuous_on s ==> (\x. c * f x) uniformly_continuous_on s"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o ISPEC (← q r"\x:complex. c * x") o MATCH_MP
     (← REWRITE_RULE [IMP_CONJ] UNIFORMLY_CONTINUOUS_ON_COMPOSE)) THEN
    ASM_SIMP_TAC [o_DEF, LINEAR_COMPLEX_MUL, LINEAR_UNIFORMLY_CONTINUOUS_ON])

  let UNIFORMLY_CONTINUOUS_ON_COMPLEX_RMUL ← prove
   r"!f c s:real^N->bool.
      f uniformly_continuous_on s ==> (\x. f x * c) uniformly_continuous_on s"
   (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN
    REWRITE_TAC [UNIFORMLY_CONTINUOUS_ON_COMPLEX_LMUL])

  pure { SERIES_COMPLEX_LMUL, SERIES_COMPLEX_RMUL, SERIES_COMPLEX_DIV,
         SUMMABLE_COMPLEX_LMUL, SUMMABLE_COMPLEX_RMUL, SUMMABLE_COMPLEX_DIV,
         SERIES_COMPLEX_MUL, SERIES_COMPLEX_MUL_UNIQUE, SUMMABLE_COMPLEX_MUL_LEFT,
         SUMMABLE_COMPLEX_MUL_RIGHT, CONTINUOUS_COMPLEX_MUL, CONTINUOUS_COMPLEX_LMUL,
         CONTINUOUS_COMPLEX_RMUL, CONTINUOUS_COMPLEX_INV, CONTINUOUS_COMPLEX_DIV,
         CONTINUOUS_COMPLEX_POW, CONTINUOUS_CPRODUCT, CONTINUOUS_COMPLEX_INV_WITHIN,
         CONTINUOUS_COMPLEX_INV_AT, CONTINUOUS_COMPLEX_DIV_WITHIN,
         CONTINUOUS_COMPLEX_DIV_AT, CONTINUOUS_ON_COMPLEX_MUL,
         CONTINUOUS_ON_COMPLEX_LMUL, CONTINUOUS_ON_COMPLEX_RMUL,
         CONTINUOUS_ON_COMPLEX_INV, CONTINUOUS_MAP_COMPLEX_INV,
         CONTINUOUS_ON_COMPLEX_DIV, CONTINUOUS_ON_COMPLEX_POW, CONTINUOUS_ON_CPRODUCT,
         UNIFORMLY_CONTINUOUS_ON_COMPLEX_MUL, UNIFORMLY_CONTINUOUS_ON_COMPLEX_LMUL,
         UNIFORMLY_CONTINUOUS_ON_COMPLEX_RMUL }
/- ------------------------------------------------------------------------- -/
/- Continuity prover (not just for complex numbers but with more for them);  -/
/- hence a limit calculator; continuity of the norm; continuity switching    -/
/- range between complex and real^1; linearity and continuity of the        -/
/- components.  (canal.ml 824-947)                                          -/
/- ------------------------------------------------------------------------- -/

/-- The `let rec CONTINUOUS_TAC gl` of canal.ml 846-856, over the tactics
    built before it. -/
partial def continuousTacRec [HolBase] (tac_base tac_1 tac_2 tac_1' tac_2' nl : tactic) :
    tactic := fun gl =>
  let CONTINUOUS_TAC := continuousTacRec tac_base tac_1 tac_2 tac_1' tac_2' nl
  (tac_base ORELSE
   (tac_1 THEN CONTINUOUS_TAC) ORELSE
   (tac_2 THEN CONJ_TAC THEN CONTINUOUS_TAC) ORELSE
   (tac_1' THEN CONJ_TAC THENL
    [CONTINUOUS_TAC, nl]) ORELSE
   (tac_2' THEN REPEAT CONJ_TAC THENL
    [CONTINUOUS_TAC, CONTINUOUS_TAC,
     nl]) ORELSE
   ALL_TAC) gl

structure KND where
  CONTINUOUS_TAC : tactic
  LIM_TAC : tactic
  CONTINUOUS_AT_CX_NORM : thm
  CONTINUOUS_WITHIN_CX_NORM : thm
  CONTINUOUS_ON_CX_NORM : thm
  CONTINUOUS_AT_CX_DOT : thm
  CONTINUOUS_WITHIN_CX_DOT : thm
  CONTINUOUS_ON_CX_DOT : thm
  CONTINUOUS_CX_DROP : thm
  CONTINUOUS_ON_CX_DROP : thm
  CONTINUOUS_CX_LIFT : thm
  CONTINUOUS_ON_CX_LIFT : thm
  LINEAR_CX_RE : thm
  CONTINUOUS_AT_CX_RE : thm
  CONTINUOUS_ON_CX_RE : thm
  LINEAR_CX_IM : thm
  CONTINUOUS_AT_CX_IM : thm
  CONTINUOUS_ON_CX_IM : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupKND [HolBase] (D : CanalDeps) (BKNC : KNC) : ExceptT String IO KND := do
  -- @@SCOPE BEGIN
  let { CONTINUOUS_COMPLEX_DIV, CONTINUOUS_COMPLEX_INV, CONTINUOUS_COMPLEX_MUL,
        CONTINUOUS_COMPLEX_POW, .. } := BKNC
  let { COMPLEX_CMUL, COMPLEX_NORM_CX, CX_ADD, CX_MUL, CX_SUB, IM_ADD, IM_MUL_CX, RE_ADD,
        RE_MUL_CX, .. } := D.cxc
  let { continuous, LIM_CONTINUOUS, .. } := D.qtopology
  let { MESON_TAC, NORM_ARITH, .. } := D.cx.cvx
  let { CONTINUOUS_NEG, NETLIMIT_AT, .. } := D.ms.ig.qtopology
  let { ETA_AX, .. } := D.cx.cvx.core1
  let { o_THM, .. } := D.cx.cvx.core6
  let { DOT_RADD, DOT_RMUL, .. } := D.cx.cvx.vec1
  let { DROP_SUB, LIFT_SUB, NORM_1, .. } := D.cx.cvx.vec2
  let { NORM_LIFT, .. } := D.cx.cvx.vec3
  let { dist, linear, .. } := D.cx.cvx.vec4
  let { CONTINUOUS_ADD, CONTINUOUS_AT_ID, .. } := D.cx.cvx.top2
  let { CONTINUOUS_CONST, CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN, CONTINUOUS_SUB,
        CONTINUOUS_WITHIN_ID, .. } := D.cx.cvx.top3
  let { LINEAR_CONTINUOUS_AT, LINEAR_CONTINUOUS_ON, .. } := D.cx.cvx.top4
  let { continuous_at, .. } := D.cx.cvx.top5
  let { CONTINUOUS_AT_WITHIN, .. } := D.ms.ig.dv.qtopology1
  let { NETLIMIT_WITHIN, .. } := D.ms.ig.dv.qtopology2
  let { tendsto, .. } := D.ms.ig.dv.dg.qtopology2
  let { CONTINUOUS_CMUL, .. } := D.ms.ig.dv.dg.pt.qtop
  -- @@SCOPE END

  let CONTINUOUS_TAC : tactic ← do
    let ETA_THM ← prove
     r"f continuous net <=> (\x. f x) continuous net"
     (REWRITE_TAC [ETA_AX])
    let ETA_TWEAK (th : thm) : ExceptT String IO thm := do
      GEN_REWRITE_RULE (LAND_CONV o ONCE_DEPTH_CONV) [ETA_THM] (← SPEC_ALL th)
    let tac_base :=
      MATCH_ACCEPT_TAC CONTINUOUS_CONST ORELSE
      MATCH_ACCEPT_TAC CONTINUOUS_AT_ID ORELSE
      MATCH_ACCEPT_TAC CONTINUOUS_WITHIN_ID
    let tac_1 :=
      MATCH_MP_TAC (← ETA_TWEAK CONTINUOUS_CMUL) ORELSE
      MATCH_MP_TAC (← ETA_TWEAK CONTINUOUS_NEG) ORELSE
      MATCH_MP_TAC (← ETA_TWEAK CONTINUOUS_COMPLEX_POW)
    let tac_2 :=
      MATCH_MP_TAC (← ETA_TWEAK CONTINUOUS_ADD) ORELSE
      MATCH_MP_TAC (← ETA_TWEAK CONTINUOUS_SUB) ORELSE
      MATCH_MP_TAC (← ETA_TWEAK CONTINUOUS_COMPLEX_MUL)
    let tac_1' := MATCH_MP_TAC (← ETA_TWEAK CONTINUOUS_COMPLEX_INV)
    let tac_2' := MATCH_MP_TAC (← ETA_TWEAK CONTINUOUS_COMPLEX_DIV)
    pure (continuousTacRec tac_base tac_1 tac_2 tac_1' tac_2'
      (REWRITE_TAC [NETLIMIT_AT, NETLIMIT_WITHIN]))

  let LIM_TAC : tactic :=
    MATCH_MP_TAC LIM_CONTINUOUS THEN CONJ_TAC THENL
     [CONTINUOUS_TAC, REWRITE_TAC [NETLIMIT_AT, NETLIMIT_WITHIN]]

  let CONTINUOUS_AT_CX_NORM ← prove
   r"!z:real^N. (\z. Cx(norm z)) continuous at z"
   (REWRITE_TAC [continuous_at, dist, ← GSYM CX_SUB, COMPLEX_NORM_CX] THEN
    MESON_TAC [← NORM_ARITH (← q r"norm(a - b:real^N) < d ==> abs(norm a - norm b) < d")])

  let CONTINUOUS_WITHIN_CX_NORM ← prove
   r"!z:real^N s. (\z. Cx(norm z)) continuous (at z within s)"
   (SIMP_TAC [CONTINUOUS_AT_CX_NORM, CONTINUOUS_AT_WITHIN])

  let CONTINUOUS_ON_CX_NORM ← prove
   r"!s. (\z. Cx(norm z)) continuous_on s"
   (SIMP_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN, CONTINUOUS_WITHIN_CX_NORM])

  let CONTINUOUS_AT_CX_DOT ← prove
   r"!c z:real^N. (\z. Cx(c dot z)) continuous at z"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
    REWRITE_TAC [linear, DOT_RADD, DOT_RMUL, CX_ADD, COMPLEX_CMUL, CX_MUL])

  let CONTINUOUS_WITHIN_CX_DOT ← prove
   r"!c z:real^N s. (\z. Cx(c dot z)) continuous (at z within s)"
   (SIMP_TAC [CONTINUOUS_AT_CX_DOT, CONTINUOUS_AT_WITHIN])

  let CONTINUOUS_ON_CX_DOT ← prove
   r"!s c:real^N. (\z. Cx(c dot z)) continuous_on s"
   (SIMP_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN, CONTINUOUS_WITHIN_CX_DOT])

  let CONTINUOUS_CX_DROP ← prove
   r"!net f. f continuous net ==> (\x. Cx(drop(f x))) continuous net"
   (REWRITE_TAC [continuous, tendsto] THEN
    REWRITE_TAC [dist, ← GSYM CX_SUB, COMPLEX_NORM_CX, ← GSYM DROP_SUB] THEN
    REWRITE_TAC [← GSYM NORM_1])

  let CONTINUOUS_ON_CX_DROP ← prove
   r"!f s. f continuous_on s ==> (\x. Cx(drop(f x))) continuous_on s"
   (SIMP_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN, CONTINUOUS_CX_DROP])

  let CONTINUOUS_CX_LIFT ← prove
   r"!f. (\x. Cx(f x)) continuous net <=> (\x. lift(f x)) continuous net"
   (REWRITE_TAC [continuous, tendsto, dist, ← GSYM CX_SUB, ← GSYM LIFT_SUB] THEN
    REWRITE_TAC [COMPLEX_NORM_CX, NORM_LIFT])

  let CONTINUOUS_ON_CX_LIFT ← prove
   r"!f s. (\x. Cx(f x)) continuous_on s <=> (\x. lift(f x)) continuous_on s"
   (REWRITE_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN, CONTINUOUS_CX_LIFT])

  let LINEAR_CX_RE ← prove
   r"linear(Cx o Re)"
   (SIMP_TAC [linear, o_THM, COMPLEX_CMUL, RE_ADD, RE_MUL_CX, CX_MUL, CX_ADD])

  let CONTINUOUS_AT_CX_RE ← prove
   r"!z. (Cx o Re) continuous at z"
   (SIMP_TAC [LINEAR_CONTINUOUS_AT, LINEAR_CX_RE])

  let CONTINUOUS_ON_CX_RE ← prove
   r"!s. (Cx o Re) continuous_on s"
   (SIMP_TAC [LINEAR_CONTINUOUS_ON, LINEAR_CX_RE])

  let LINEAR_CX_IM ← prove
   r"linear(Cx o Im)"
   (SIMP_TAC [linear, o_THM, COMPLEX_CMUL, IM_ADD, IM_MUL_CX, CX_MUL, CX_ADD])

  let CONTINUOUS_AT_CX_IM ← prove
   r"!z. (Cx o Im) continuous at z"
   (SIMP_TAC [LINEAR_CONTINUOUS_AT, LINEAR_CX_IM])

  let CONTINUOUS_ON_CX_IM ← prove
   r"!s. (Cx o Im) continuous_on s"
   (SIMP_TAC [LINEAR_CONTINUOUS_ON, LINEAR_CX_IM])

  pure { CONTINUOUS_TAC, LIM_TAC, CONTINUOUS_AT_CX_NORM, CONTINUOUS_WITHIN_CX_NORM,
         CONTINUOUS_ON_CX_NORM, CONTINUOUS_AT_CX_DOT, CONTINUOUS_WITHIN_CX_DOT,
         CONTINUOUS_ON_CX_DOT, CONTINUOUS_CX_DROP, CONTINUOUS_ON_CX_DROP,
         CONTINUOUS_CX_LIFT, CONTINUOUS_ON_CX_LIFT, LINEAR_CX_RE, CONTINUOUS_AT_CX_RE,
         CONTINUOUS_ON_CX_RE, LINEAR_CX_IM, CONTINUOUS_AT_CX_IM, CONTINUOUS_ON_CX_IM }
/- ------------------------------------------------------------------------- -/
/- Complex differentiability: the infixes, the definitions, and the basic   -/
/- properties.  (canal.ml 948-1178)                                         -/
/- ------------------------------------------------------------------------- -/

structure KNE where
  has_complex_derivative : thm
  complex_differentiable : thm
  complex_derivative : thm
  higher_complex_derivative : thm
  holomorphic_on : thm
  HOLOMORPHIC_ON_EMPTY : thm
  HOLOMORPHIC_ON_DIFFERENTIABLE : thm
  HOLOMORPHIC_ON_OPEN : thm
  HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_WITHIN : thm
  HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT : thm
  HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT : thm
  HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_WITHIN : thm
  COMPLEX_DIFFERENTIABLE_IMP_DIFFERENTIABLE : thm
  COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT : thm
  COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN : thm
  HOLOMORPHIC_ON_IMP_CONTINUOUS_ON : thm
  HOLOMORPHIC_ON_SUBSET : thm
  HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET : thm
  COMPLEX_DIFFERENTIABLE_WITHIN_SUBSET : thm
  HAS_COMPLEX_DERIVATIVE_AT_WITHIN : thm
  HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN : thm
  COMPLEX_DIFFERENTIABLE_AT_WITHIN : thm
  HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN : thm
  HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN : thm
  HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT : thm
  HAS_COMPLEX_DERIVATIVE_ZERO_CONSTANT : thm
  HAS_COMPLEX_DERIVATIVE_ZERO_UNIQUE : thm
  HAS_COMPLEX_DERIVATIVE_ZERO_CONNECTED_CONSTANT : thm
  HAS_COMPLEX_DERIVATIVE_ZERO_CONNECTED_UNIQUE : thm
  COMPLEX_DIFF_CHAIN_WITHIN : thm
  COMPLEX_DIFF_CHAIN_AT : thm
  HAS_COMPLEX_DERIVATIVE_CHAIN : thm
  HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV : thm
  COMPLEX_DERIVATIVE_UNIQUE_AT : thm
  HIGHER_COMPLEX_DERIVATIVE_1 : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupKNE [HolBase] (D : CanalDeps) : ExceptT String IO KNE := do
  -- @@SCOPE BEGIN
  let { define, .. } := D.cx
  let { COMPLEX_MUL_ASSOC, COMPLEX_MUL_LZERO, COMPLEX_MUL_RID, COMPLEX_MUL_SYM,
        .. } := D.cxb
  let { COMPLEX_VEC_0, .. } := D.cxc
  let { FRECHET_DERIVATIVE_UNIQUE_AT, HAS_DERIVATIVE_TRANSFORM_WITHIN,
        HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN, HAS_DERIVATIVE_ZERO_CONNECTED_CONSTANT,
        HAS_DERIVATIVE_ZERO_CONNECTED_UNIQUE, HAS_DERIVATIVE_ZERO_CONSTANT,
        HAS_DERIVATIVE_ZERO_UNIQUE, .. } := D.qderivatives
  let { DIFFERENTIABLE_IMP_CONTINUOUS_AT, DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN,
        has_derivative_at, HAS_DERIVATIVE_AT_WITHIN, has_derivative_within,
        .. } := D.ms.qderivatives
  let { ASM_MESON_TAC, MESON_TAC, new_definition, num_CONV, parse_as_infix, .. } := D.cx.cvx
  let { DIFF_CHAIN_WITHIN, differentiable, HAS_DERIVATIVE_WITHIN_OPEN,
        HAS_DERIVATIVE_WITHIN_SUBSET, .. } := D.ms.ig.qderivatives
  let { IN_UNIV, NOT_IN_EMPTY, .. } := D.cx.cvx.core3
  let { SUBSET, .. } := D.cx.cvx.core5
  let { o_DEF, SUBSET_UNIV, .. } := D.cx.cvx.core6
  let { CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN, .. } := D.cx.cvx.top3
  let { LIM_WITHIN_OPEN, WITHIN_UNIV, .. } := D.ms.ig.dv.qtopology2
  -- @@SCOPE END

  parse_as_infix ("has_complex_derivative", (12, "right"))
  parse_as_infix ("complex_differentiable", (12, "right"))
  parse_as_infix ("holomorphic_on", (12, "right"))

  let has_complex_derivative ← new_definition
   r"(f has_complex_derivative f') net <=> (f has_derivative (\x. f' * x)) net"

  let complex_differentiable ← new_definition
   r"f complex_differentiable net <=> ?f'. (f has_complex_derivative f') net"

  let complex_derivative ← new_definition
   r"complex_derivative f x = @f'. (f has_complex_derivative f') (at x)"

  let higher_complex_derivative ← define
   r"higher_complex_derivative 0 f = f /\
    (!n. higher_complex_derivative (SUC n) f =
                  complex_derivative (higher_complex_derivative n f))"

  let holomorphic_on ← new_definition
   r"f holomorphic_on s <=>
       !x. x IN s ==> ?f'. (f has_complex_derivative f') (at x within s)"

  let HOLOMORPHIC_ON_EMPTY ← prove
   r"!f. f holomorphic_on {}"
   (REWRITE_TAC [holomorphic_on, NOT_IN_EMPTY])

  let HOLOMORPHIC_ON_DIFFERENTIABLE ← prove
   r"!f s. f holomorphic_on s <=>
         !x. x IN s ==> f complex_differentiable (at x within s)"
   (REWRITE_TAC [holomorphic_on, complex_differentiable])

  let HOLOMORPHIC_ON_OPEN ← prove
   r"!f s. open s
         ==> (f holomorphic_on s <=>
              !x. x IN s ==> ?f'. (f has_complex_derivative f') (at x))"
   (REWRITE_TAC [holomorphic_on, has_complex_derivative] THEN
    REWRITE_TAC [has_derivative_at, has_derivative_within] THEN
    SIMP_TAC [LIM_WITHIN_OPEN])

  let HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_WITHIN ← prove
   r"!f s x. f holomorphic_on s /\ x IN s
           ==> f complex_differentiable (at x within s)"
   (MESON_TAC [HOLOMORPHIC_ON_DIFFERENTIABLE])

  let HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT ← prove
   r"!f s x. f holomorphic_on s /\ open s /\ x IN s
           ==> f complex_differentiable (at x)"
   (MESON_TAC [HOLOMORPHIC_ON_OPEN, complex_differentiable])

  let HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT ← prove
   r"!f f' x. (f has_complex_derivative f') (at x) ==> f continuous at x"
   (REWRITE_TAC [has_complex_derivative] THEN
    MESON_TAC [differentiable, DIFFERENTIABLE_IMP_CONTINUOUS_AT])

  let HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_WITHIN ← prove
   r"!f f' x s. (f has_complex_derivative f') (at x within s)
              ==> f continuous (at x within s)"
   (REWRITE_TAC [has_complex_derivative] THEN
    MESON_TAC [differentiable, DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN])

  let COMPLEX_DIFFERENTIABLE_IMP_DIFFERENTIABLE ← prove
   r"!net f. f complex_differentiable net ==> f differentiable net"
   (SIMP_TAC [complex_differentiable, differentiable, has_complex_derivative] THEN
    MESON_TAC [])

  let COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT ← prove
   r"!f x. f complex_differentiable at x ==> f continuous at x"
   (MESON_TAC [HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT, complex_differentiable])

  let COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN ← prove
   r"!f x s. f complex_differentiable (at x within s)
           ==> f continuous (at x within s)"
   (MESON_TAC [COMPLEX_DIFFERENTIABLE_IMP_DIFFERENTIABLE,
               DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN])

  let HOLOMORPHIC_ON_IMP_CONTINUOUS_ON ← prove
   r"!f s. f holomorphic_on s ==> f continuous_on s"
   (REWRITE_TAC [holomorphic_on, CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    REWRITE_TAC [has_complex_derivative] THEN
    MESON_TAC [DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN, differentiable])

  let HOLOMORPHIC_ON_SUBSET ← prove
   r"!f s t. f holomorphic_on s /\ t SUBSET s ==> f holomorphic_on t"
   (REWRITE_TAC [holomorphic_on, has_complex_derivative] THEN
    MESON_TAC [SUBSET, HAS_DERIVATIVE_WITHIN_SUBSET])

  let HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET ← prove
   r"!f s t x. (f has_complex_derivative f') (at x within s) /\ t SUBSET s
             ==> (f has_complex_derivative f') (at x within t)"
   (REWRITE_TAC [has_complex_derivative, HAS_DERIVATIVE_WITHIN_SUBSET])

  let COMPLEX_DIFFERENTIABLE_WITHIN_SUBSET ← prove
   r"!f s t. f complex_differentiable (at x within s) /\ t SUBSET s
           ==> f complex_differentiable (at x within t)"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET])

  let HAS_COMPLEX_DERIVATIVE_AT_WITHIN ← prove
   r"!f f' x s. (f has_complex_derivative f') (at x)
              ==> (f has_complex_derivative f') (at x within s)"
   (REWRITE_TAC [has_complex_derivative, HAS_DERIVATIVE_AT_WITHIN])

  let HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN ← prove
   r"!f f' a s.
         a IN s /\ open s
         ==> ((f has_complex_derivative f') (at a within s) <=>
              (f has_complex_derivative f') (at a))"
   (REWRITE_TAC [has_complex_derivative, HAS_DERIVATIVE_WITHIN_OPEN])

  let COMPLEX_DIFFERENTIABLE_AT_WITHIN ← prove
   r"!f s z. f complex_differentiable (at z)
           ==> f complex_differentiable (at z within s)"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN])

  let HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN ← prove
   r"!f f' g x s d.
       &0 < d /\ x IN s /\
       (!x'. x' IN s /\ dist (x',x) < d ==> f x' = g x') /\
       (f has_complex_derivative f') (at x within s)
       ==> (g has_complex_derivative f') (at x within s)"
   (REWRITE_TAC [has_complex_derivative] THEN
    MESON_TAC [HAS_DERIVATIVE_TRANSFORM_WITHIN])

  let HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN ← prove
   r"!f g f' s z. open s /\ z IN s /\ (!w. w IN s ==> f w = g w) /\
                 (f has_complex_derivative f') (at z)
                 ==> (g has_complex_derivative f') (at z)"
   (REWRITE_TAC [has_complex_derivative] THEN
    ASM_MESON_TAC [HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN])

  let HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT ← prove
   r"!f f' g x d.
       &0 < d /\ (!x'. dist (x',x) < d ==> f x' = g x') /\
       (f has_complex_derivative f') (at x)
       ==> (g has_complex_derivative f') (at x)"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN, IN_UNIV])

  let HAS_COMPLEX_DERIVATIVE_ZERO_CONSTANT ← prove
   r"!f s.
        convex s /\
        (!x. x IN s ==> (f has_complex_derivative Cx(&0)) (at x within s))
        ==> ?c. !x. x IN s ==> f(x) = c"
   (REWRITE_TAC [has_complex_derivative, COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC [← GSYM COMPLEX_VEC_0, HAS_DERIVATIVE_ZERO_CONSTANT])

  let HAS_COMPLEX_DERIVATIVE_ZERO_UNIQUE ← prove
   r"!f s c a.
        convex s /\ a IN s /\ f a = c /\
        (!x. x IN s ==> (f has_complex_derivative Cx(&0)) (at x within s))
        ==> !x. x IN s ==> f(x) = c"
   (REWRITE_TAC [has_complex_derivative, COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC [← GSYM COMPLEX_VEC_0, HAS_DERIVATIVE_ZERO_UNIQUE])

  let HAS_COMPLEX_DERIVATIVE_ZERO_CONNECTED_CONSTANT ← prove
   r"!f s.
        open s /\ connected s /\
        (!x. x IN s ==> (f has_complex_derivative Cx(&0)) (at x))
        ==> ?c. !x. x IN s ==> f(x) = c"
   (REWRITE_TAC [has_complex_derivative, COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC [← GSYM COMPLEX_VEC_0, HAS_DERIVATIVE_ZERO_CONNECTED_CONSTANT])

  let HAS_COMPLEX_DERIVATIVE_ZERO_CONNECTED_UNIQUE ← prove
   r"!f s c a.
        open s /\ connected s /\ a IN s /\ f a = c /\
        (!x. x IN s ==> (f has_complex_derivative Cx(&0)) (at x))
        ==> !x. x IN s ==> f(x) = c"
   (REWRITE_TAC [has_complex_derivative, COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC [← GSYM COMPLEX_VEC_0, HAS_DERIVATIVE_ZERO_CONNECTED_UNIQUE])

  let COMPLEX_DIFF_CHAIN_WITHIN ← prove
   r"!f g f' g' x s.
        (f has_complex_derivative f') (at x within s) /\
        (g has_complex_derivative g') (at (f x) within (IMAGE f s))
        ==> ((g o f) has_complex_derivative (g' * f'))(at x within s)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [has_complex_derivative] THEN
    DISCH_THEN (MP_TAC o MATCH_MP DIFF_CHAIN_WITHIN) THEN
    REWRITE_TAC [o_DEF, COMPLEX_MUL_ASSOC])

  let COMPLEX_DIFF_CHAIN_AT ← prove
   r"!f g f' g' x.
        (f has_complex_derivative f') (at x) /\
        (g has_complex_derivative g') (at (f x))
        ==> ((g o f) has_complex_derivative (g' * f')) (at x)"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    ASM_MESON_TAC [COMPLEX_DIFF_CHAIN_WITHIN, SUBSET_UNIV,
                   HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET])

  let HAS_COMPLEX_DERIVATIVE_CHAIN ← prove
   r"!P f g.
        (!x. P x ==> (g has_complex_derivative g'(x)) (at x))
        ==> (!x s. (f has_complex_derivative f') (at x within s) /\ P(f x)
                   ==> ((\x. g(f x)) has_complex_derivative f' * g'(f x))
                       (at x within s)) /\
            (!x. (f has_complex_derivative f') (at x) /\ P(f x)
                 ==> ((\x. g(f x)) has_complex_derivative f' * g'(f x))
                     (at x))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM o_DEF] THEN
    ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN
    ASM_MESON_TAC [COMPLEX_DIFF_CHAIN_WITHIN, COMPLEX_DIFF_CHAIN_AT,
                   HAS_COMPLEX_DERIVATIVE_AT_WITHIN])

  let HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV ← prove
   r"!f g. (!x. (g has_complex_derivative g'(x)) (at x))
         ==> (!x s. (f has_complex_derivative f') (at x within s)
                    ==> ((\x. g(f x)) has_complex_derivative f' * g'(f x))
                        (at x within s)) /\
             (!x. (f has_complex_derivative f') (at x)
                  ==> ((\x. g(f x)) has_complex_derivative f' * g'(f x))
                      (at x))"
   (MP_TAC (← SPEC (← q r"\x:complex. T") HAS_COMPLEX_DERIVATIVE_CHAIN) THEN SIMP_TAC [])

  let COMPLEX_DERIVATIVE_UNIQUE_AT ← prove
   r"!f z f' f''.
        (f has_complex_derivative f') (at z) /\
        (f has_complex_derivative f'') (at z)
        ==> f' = f''"
   (REPEAT GEN_TAC THEN REWRITE_TAC [has_complex_derivative] THEN
    DISCH_THEN (MP_TAC o MATCH_MP FRECHET_DERIVATIVE_UNIQUE_AT) THEN
    DISCH_THEN (MP_TAC o C AP_THM (← q r"Cx(&1)")) THEN
    REWRITE_TAC [COMPLEX_MUL_RID])

  let HIGHER_COMPLEX_DERIVATIVE_1 ← prove
   r"!f z. higher_complex_derivative 1 f z = complex_derivative f z"
   (REWRITE_TAC [← ExceptT.mk (num_CONV (← q r"1")), higher_complex_derivative])

  pure { has_complex_derivative, complex_differentiable, complex_derivative,
         higher_complex_derivative, holomorphic_on, HOLOMORPHIC_ON_EMPTY,
         HOLOMORPHIC_ON_DIFFERENTIABLE, HOLOMORPHIC_ON_OPEN,
         HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_WITHIN, HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT,
         HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT,
         HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_WITHIN,
         COMPLEX_DIFFERENTIABLE_IMP_DIFFERENTIABLE,
         COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT,
         COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN, HOLOMORPHIC_ON_IMP_CONTINUOUS_ON,
         HOLOMORPHIC_ON_SUBSET, HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET,
         COMPLEX_DIFFERENTIABLE_WITHIN_SUBSET, HAS_COMPLEX_DERIVATIVE_AT_WITHIN,
         HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN, COMPLEX_DIFFERENTIABLE_AT_WITHIN,
         HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN,
         HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN,
         HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT, HAS_COMPLEX_DERIVATIVE_ZERO_CONSTANT,
         HAS_COMPLEX_DERIVATIVE_ZERO_UNIQUE,
         HAS_COMPLEX_DERIVATIVE_ZERO_CONNECTED_CONSTANT,
         HAS_COMPLEX_DERIVATIVE_ZERO_CONNECTED_UNIQUE, COMPLEX_DIFF_CHAIN_WITHIN,
         COMPLEX_DIFF_CHAIN_AT, HAS_COMPLEX_DERIVATIVE_CHAIN,
         HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV, COMPLEX_DERIVATIVE_UNIQUE_AT,
         HIGHER_COMPLEX_DERIVATIVE_1 }
/- ------------------------------------------------------------------------- -/
/- A more direct characterization; arithmetical combining theorems.         -/
/- (canal.ml 1179-1413)                                                     -/
/- ------------------------------------------------------------------------- -/

structure KNF where
  HAS_COMPLEX_DERIVATIVE_WITHIN : thm
  HAS_COMPLEX_DERIVATIVE_AT : thm
  HAS_DERIVATIVE_COMPLEX_CMUL : thm
  HAS_COMPLEX_DERIVATIVE_LINEAR : thm
  HAS_COMPLEX_DERIVATIVE_LMUL_WITHIN : thm
  HAS_COMPLEX_DERIVATIVE_LMUL_AT : thm
  HAS_COMPLEX_DERIVATIVE_RMUL_WITHIN : thm
  HAS_COMPLEX_DERIVATIVE_RMUL_AT : thm
  HAS_COMPLEX_DERIVATIVE_CDIV_WITHIN : thm
  HAS_COMPLEX_DERIVATIVE_CDIV_AT : thm
  HAS_COMPLEX_DERIVATIVE_ID : thm
  HAS_COMPLEX_DERIVATIVE_CONST : thm
  HAS_COMPLEX_DERIVATIVE_NEG : thm
  HAS_COMPLEX_DERIVATIVE_ADD : thm
  HAS_COMPLEX_DERIVATIVE_SUB : thm
  HAS_COMPLEX_DERIVATIVE_MUL_WITHIN : thm
  HAS_COMPLEX_DERIVATIVE_MUL_AT : thm
  HAS_COMPLEX_DERIVATIVE_POW_WITHIN : thm
  HAS_COMPLEX_DERIVATIVE_POW_AT : thm
  HAS_COMPLEX_DERIVATIVE_INV_BASIC : thm
  HAS_COMPLEX_DERIVATIVE_INV_WITHIN : thm
  HAS_COMPLEX_DERIVATIVE_INV_AT : thm
  HAS_COMPLEX_DERIVATIVE_DIV_WITHIN : thm
  HAS_COMPLEX_DERIVATIVE_DIV_AT : thm
  HAS_COMPLEX_DERIVATIVE_VSUM : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupKNF [HolBase] (D : CanalDeps) (BKND : KND) (BKNE : KNE) : ExceptT String IO KNF := do
  -- @@SCOPE BEGIN
  let { LIM_TAC, .. } := BKND
  let { COMPLEX_DIFF_CHAIN_WITHIN, has_complex_derivative,
        HAS_COMPLEX_DERIVATIVE_AT_WITHIN, .. } := BKNE
  let { complex_div, complex_pow, .. } := D.cxa
  let { COMPLEX_ADD_RDISTRIB, COMPLEX_MUL_AC, COMPLEX_MUL_LID, COMPLEX_MUL_LNEG,
        COMPLEX_MUL_LZERO, COMPLEX_MUL_SYM, COMPLEX_SUB_RDISTRIB, COMPLEX_SUB_RZERO,
        .. } := D.cxb
  let { COMPLEX_CMUL, COMPLEX_NORM_CX, COMPLEX_VEC_0, CX_ADD, .. } := D.cxc
  let { COMPLEX_RING, .. } := D.cxd
  let { COMPLEX_FIELD, .. } := D.cxe
  let { COMPLEX_NORM_INV, COMPLEX_NORM_MUL, COMPLEX_NORM_POW, .. } := D.cxf
  let { BILINEAR_COMPLEX_MUL, LINEAR_COMPLEX_MUL, .. } := D.cxh
  let { VSUM_COMPLEX_RMUL, .. } := D.cxi
  let { LIM_TRANSFORM_AWAY_AT, .. } := D.qtopology
  let { HAS_DERIVATIVE_BILINEAR_WITHIN, HAS_DERIVATIVE_VSUM, .. } := D.qderivatives
  let { has_derivative_at, HAS_DERIVATIVE_LINEAR, HAS_DERIVATIVE_NEG,
        has_derivative_within, .. } := D.ms.qderivatives
  let { SUC_SUB1, .. } := D.ms.qsession
  let { INDUCT_TAC, MESON, NUM_REDUCE_CONV, REAL_FIELD, VECTOR_ARITH, .. } := D.cx.cvx
  let { HAS_DERIVATIVE_ADD, HAS_DERIVATIVE_CONST, HAS_DERIVATIVE_ID, HAS_DERIVATIVE_SUB,
        .. } := D.ms.ig.qderivatives
  let { CONJ_ASSOC, EQ_IMP, .. } := D.cx.cvx.core1
  let { FUN_EQ_THM, IMP_IMP, .. } := D.cx.cvx.core2
  let { REAL_ABS_INV, .. } := D.cx.cvx.core3
  let { REAL_OF_NUM_SUC, RIGHT_FORALL_IMP_THM, .. } := D.cx.cvx.core5
  let { o_DEF, .. } := D.cx.cvx.core6
  let { NORM_MUL, NORM_POS_LT, REAL_ABS_NORM, .. } := D.cx.cvx.vec3
  let { dist, linear, VECTOR_SUB_EQ, VECTOR_SUB_RZERO, .. } := D.cx.cvx.vec4
  let { LIM_WITHIN, .. } := D.cx.cvx.top4
  let { LIM_AT, .. } := D.ms.ig.dv.qtopology1
  let { LIM_NULL, WITHIN_UNIV, .. } := D.ms.ig.dv.qtopology2
  -- @@SCOPE END

  let HAS_COMPLEX_DERIVATIVE_WITHIN ← prove
   r"!f s a. (f has_complex_derivative f') (at a within s) <=>
           ((\x. (f(x) - f(a)) / (x - a)) --> f') (at a within s)"
   (REWRITE_TAC [has_complex_derivative, has_derivative_within] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [LINEAR_COMPLEX_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [LIM_NULL] THEN
    REWRITE_TAC [LIM_WITHIN, dist, VECTOR_SUB_RZERO, NORM_MUL] THEN
    REWRITE_TAC [NORM_POS_LT, VECTOR_SUB_EQ] THEN SIMP_TAC [← ExceptT.mk (COMPLEX_FIELD
     (← q r"~(x:complex = a) ==> y / (x - a) - z = inv(x - a) * (y - z * (x - a))"))] THEN
    REWRITE_TAC [REAL_ABS_INV, COMPLEX_NORM_MUL, REAL_ABS_NORM,
           COMPLEX_NORM_INV, ← VECTOR_ARITH (← q r"a:complex - (b + c) = a - b - c")])

  let HAS_COMPLEX_DERIVATIVE_AT ← prove
   r"!f a. (f has_complex_derivative f') (at a) <=>
         ((\x. (f(x) - f(a)) / (x - a)) --> f') (at a)"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    REWRITE_TAC [HAS_COMPLEX_DERIVATIVE_WITHIN])

  let HAS_DERIVATIVE_COMPLEX_CMUL ← prove
   r"!net c. ((\x. c * x) has_derivative (\x. c * x)) net"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC [LINEAR_COMPLEX_MUL])

  let HAS_COMPLEX_DERIVATIVE_LINEAR ← prove
   r"!net c. ((\x. c * x) has_complex_derivative c) net"
   (REPEAT GEN_TAC THEN REWRITE_TAC [has_complex_derivative] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC [linear, COMPLEX_CMUL] THEN CONV_TAC COMPLEX_RING)

  let HAS_COMPLEX_DERIVATIVE_LMUL_WITHIN ← prove
   r"!f f' c x s.
        (f has_complex_derivative f') (at x within s)
        ==> ((\x. c * f(x)) has_complex_derivative (c * f')) (at x within s)"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"at ((f:complex->complex) x) within (IMAGE f s)",
                      ← q r"c:complex"]
      HAS_COMPLEX_DERIVATIVE_LINEAR) THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"a ==> b ==> c <=> b /\ a ==> c")] THEN
    DISCH_THEN (MP_TAC o MATCH_MP COMPLEX_DIFF_CHAIN_WITHIN) THEN
    REWRITE_TAC [o_DEF])

  let HAS_COMPLEX_DERIVATIVE_LMUL_AT ← prove
   r"!f f' c x.
        (f has_complex_derivative f') (at x)
        ==> ((\x. c * f(x)) has_complex_derivative (c * f')) (at x)"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    REWRITE_TAC [HAS_COMPLEX_DERIVATIVE_LMUL_WITHIN])

  let HAS_COMPLEX_DERIVATIVE_RMUL_WITHIN ← prove
   r"!f f' c x s.
        (f has_complex_derivative f') (at x within s)
        ==> ((\x. f(x) * c) has_complex_derivative (f' * c)) (at x within s)"
   (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN
    REWRITE_TAC [HAS_COMPLEX_DERIVATIVE_LMUL_WITHIN])

  let HAS_COMPLEX_DERIVATIVE_RMUL_AT ← prove
   r"!f f' c x.
        (f has_complex_derivative f') (at x)
        ==> ((\x. f(x) * c) has_complex_derivative (f' * c)) (at x)"
   (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN
    REWRITE_TAC [HAS_COMPLEX_DERIVATIVE_LMUL_AT])

  let HAS_COMPLEX_DERIVATIVE_CDIV_WITHIN ← prove
   r"!f f' c x s.
        (f has_complex_derivative f') (at x within s)
        ==> ((\x. f(x) / c) has_complex_derivative (f' / c)) (at x within s)"
   (SIMP_TAC [complex_div, HAS_COMPLEX_DERIVATIVE_RMUL_WITHIN])

  let HAS_COMPLEX_DERIVATIVE_CDIV_AT ← prove
   r"!f f' c x.
        (f has_complex_derivative f') (at x)
        ==> ((\x. f(x) / c) has_complex_derivative (f' / c)) (at x)"
   (SIMP_TAC [complex_div, HAS_COMPLEX_DERIVATIVE_RMUL_AT])

  let HAS_COMPLEX_DERIVATIVE_ID ← prove
   r"!net. ((\x. x) has_complex_derivative Cx(&1)) net"
   (REWRITE_TAC [has_complex_derivative, HAS_DERIVATIVE_ID, COMPLEX_MUL_LID])

  let HAS_COMPLEX_DERIVATIVE_CONST ← prove
   r"!c net. ((\x. c) has_complex_derivative Cx(&0)) net"
   (REWRITE_TAC [has_complex_derivative, COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC [← GSYM COMPLEX_VEC_0, HAS_DERIVATIVE_CONST])

  let HAS_COMPLEX_DERIVATIVE_NEG ← prove
   r"!f f' net. (f has_complex_derivative f') net
            ==> ((\x. --(f(x))) has_complex_derivative (--f')) net"
   (SIMP_TAC [has_complex_derivative, COMPLEX_MUL_LNEG, HAS_DERIVATIVE_NEG])

  let HAS_COMPLEX_DERIVATIVE_ADD ← prove
   r"!f f' g g' net.
        (f has_complex_derivative f') net /\ (g has_complex_derivative g') net
        ==> ((\x. f(x) + g(x)) has_complex_derivative (f' + g')) net"
   (SIMP_TAC [has_complex_derivative, COMPLEX_ADD_RDISTRIB, HAS_DERIVATIVE_ADD])

  let HAS_COMPLEX_DERIVATIVE_SUB ← prove
   r"!f f' g g' net.
        (f has_complex_derivative f') net /\ (g has_complex_derivative g') net
        ==> ((\x. f(x) - g(x)) has_complex_derivative (f' - g')) net"
   (SIMP_TAC [has_complex_derivative, COMPLEX_SUB_RDISTRIB, HAS_DERIVATIVE_SUB])

  let HAS_COMPLEX_DERIVATIVE_MUL_WITHIN ← prove
   r"!f f' g g' x s.
        (f has_complex_derivative f') (at x within s) /\
        (g has_complex_derivative g') (at x within s)
        ==> ((\x. f(x) * g(x)) has_complex_derivative
             (f(x) * g' + f' * g(x))) (at x within s)"
   (REPEAT GEN_TAC THEN SIMP_TAC [has_complex_derivative] THEN
    DISCH_THEN (MP_TAC o C CONJ BILINEAR_COMPLEX_MUL) THEN
    REWRITE_TAC [← GSYM CONJ_ASSOC] THEN
    DISCH_THEN (MP_TAC o MATCH_MP HAS_DERIVATIVE_BILINEAR_WITHIN) THEN
    MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
    CONV_TAC COMPLEX_RING)

  let HAS_COMPLEX_DERIVATIVE_MUL_AT ← prove
   r"!f f' g g' x.
        (f has_complex_derivative f') (at x) /\
        (g has_complex_derivative g') (at x)
        ==> ((\x. f(x) * g(x)) has_complex_derivative
             (f(x) * g' + f' * g(x))) (at x)"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    REWRITE_TAC [HAS_COMPLEX_DERIVATIVE_MUL_WITHIN])

  let HAS_COMPLEX_DERIVATIVE_POW_WITHIN ← prove
   r"!f f' x s n. (f has_complex_derivative f') (at x within s)
                ==> ((\x. f(x) pow n) has_complex_derivative
                     (Cx(&n) * f(x) pow (n - 1) * f')) (at x within s)"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    INDUCT_TAC THEN REWRITE_TAC [complex_pow] THEN
    REWRITE_TAC [HAS_COMPLEX_DERIVATIVE_CONST, COMPLEX_MUL_LZERO] THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist CONJ) THEN
    DISCH_THEN (MP_TAC o MATCH_MP HAS_COMPLEX_DERIVATIVE_MUL_WITHIN) THEN
    REWRITE_TAC [SUC_SUB1] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
    BINOP_TAC THEN REWRITE_TAC [COMPLEX_MUL_AC, ← GSYM REAL_OF_NUM_SUC] THEN
    SPEC_TAC (← q r"n:num", ← q r"n:num") THEN REWRITE_TAC [CX_ADD] THEN INDUCT_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [SUC_SUB1, complex_pow] THEN
    CONV_TAC COMPLEX_FIELD)

  let HAS_COMPLEX_DERIVATIVE_POW_AT ← prove
   r"!f f' x n. (f has_complex_derivative f') (at x)
              ==> ((\x. f(x) pow n) has_complex_derivative
                   (Cx(&n) * f(x) pow (n - 1) * f')) (at x)"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    REWRITE_TAC [HAS_COMPLEX_DERIVATIVE_POW_WITHIN])

  let HAS_COMPLEX_DERIVATIVE_INV_BASIC ← prove
   r"!x. ~(x = Cx(&0))
         ==> ((inv) has_complex_derivative (--inv(x pow 2))) (at x)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [has_complex_derivative, has_derivative_at] THEN
    REWRITE_TAC [LINEAR_COMPLEX_MUL, COMPLEX_VEC_0] THEN
    MATCH_MP_TAC LIM_TRANSFORM_AWAY_AT THEN
    MAP_EVERY EXISTS_TAC
     [← q r"\y. inv(norm(y - x)) % inv(x pow 2 * y) * (y - x) pow 2", ← q r"Cx(&0)"] THEN
    ASM_REWRITE_TAC [COMPLEX_CMUL] THEN CONJ_TAC THENL
     [POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD, ALL_TAC] THEN
    SUBGOAL_THEN (← q r"((\y. inv(x pow 2 * y) * (y - x)) --> Cx(&0)) (at x)")
    MP_TAC THENL
     [LIM_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD, ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC [LIM_AT] THEN
    REWRITE_TAC [dist, COMPLEX_SUB_RZERO] THEN
    REWRITE_TAC [COMPLEX_NORM_MUL, COMPLEX_NORM_INV, COMPLEX_NORM_POW] THEN
    REWRITE_TAC [COMPLEX_NORM_CX, REAL_ABS_INV, REAL_ABS_NORM] THEN
    REPLICATE_TAC 2 (AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC) THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    MATCH_MP_TAC (← MESON []
     (← q r"(p ==> x = y) ==> ((p ==> x < e) <=> (p ==> y < e))")) THEN
    MAP_EVERY ABBREV_TAC
     [← q r"n = norm(x' - x:complex)",
      ← q r"m = inv (norm(x:complex) pow 2 * norm(x':complex))"] THEN
    CONV_TAC REAL_FIELD)

  let HAS_COMPLEX_DERIVATIVE_INV_WITHIN ← prove
   r"!f f' x s. (f has_complex_derivative f') (at x within s) /\
              ~(f x = Cx(&0))
              ==> ((\x. inv(f(x))) has_complex_derivative (--f' / f(x) pow 2))
                  (at x within s)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM o_DEF] THEN
    ASM_SIMP_TAC [← ExceptT.mk (COMPLEX_FIELD
     (← q r"~(g = Cx(&0)) ==> --f / g pow 2 = --inv(g pow 2) * f"))] THEN
    MATCH_MP_TAC COMPLEX_DIFF_CHAIN_WITHIN THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
    ASM_SIMP_TAC [HAS_COMPLEX_DERIVATIVE_INV_BASIC])

  let HAS_COMPLEX_DERIVATIVE_INV_AT ← prove
   r"!f f' x. (f has_complex_derivative f') (at x) /\
            ~(f x = Cx(&0))
            ==> ((\x. inv(f(x))) has_complex_derivative (--f' / f(x) pow 2))
                (at x)"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    REWRITE_TAC [HAS_COMPLEX_DERIVATIVE_INV_WITHIN])

  let HAS_COMPLEX_DERIVATIVE_DIV_WITHIN ← prove
   r"!f f' g g' x s.
        (f has_complex_derivative f') (at x within s) /\
        (g has_complex_derivative g') (at x within s) /\
        ~(g(x) = Cx(&0))
        ==> ((\x. f(x) / g(x)) has_complex_derivative
             (f' * g(x) - f(x) * g') / g(x) pow 2) (at x within s)"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (fun th => tactic_of do pure (ASSUME_TAC (← CONJUNCT2 th) THEN MP_TAC th)) THEN
    DISCH_THEN (MP_TAC o MATCH_MP HAS_COMPLEX_DERIVATIVE_INV_WITHIN) THEN
    UNDISCH_TAC (← q r"(f has_complex_derivative f') (at x within s)") THEN
    REWRITE_TAC [IMP_IMP] THEN
    DISCH_THEN (MP_TAC o MATCH_MP HAS_COMPLEX_DERIVATIVE_MUL_WITHIN) THEN
    REWRITE_TAC [← GSYM complex_div] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD)

  let HAS_COMPLEX_DERIVATIVE_DIV_AT ← prove
   r"!f f' g g' x.
        (f has_complex_derivative f') (at x) /\
        (g has_complex_derivative g') (at x) /\
        ~(g(x) = Cx(&0))
        ==> ((\x. f(x) / g(x)) has_complex_derivative
             (f' * g(x) - f(x) * g') / g(x) pow 2) (at x)"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    REWRITE_TAC [HAS_COMPLEX_DERIVATIVE_DIV_WITHIN])

  let HAS_COMPLEX_DERIVATIVE_VSUM ← prove
   r"!f net s.
         FINITE s /\ (!a. a IN s ==> (f a has_complex_derivative f' a) net)
         ==> ((\x. vsum s (\a. f a x)) has_complex_derivative (vsum s f'))
             net"
   (SIMP_TAC [← GSYM VSUM_COMPLEX_RMUL, has_complex_derivative] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP HAS_DERIVATIVE_VSUM) THEN
    REWRITE_TAC [])

  pure { HAS_COMPLEX_DERIVATIVE_WITHIN, HAS_COMPLEX_DERIVATIVE_AT,
         HAS_DERIVATIVE_COMPLEX_CMUL, HAS_COMPLEX_DERIVATIVE_LINEAR,
         HAS_COMPLEX_DERIVATIVE_LMUL_WITHIN, HAS_COMPLEX_DERIVATIVE_LMUL_AT,
         HAS_COMPLEX_DERIVATIVE_RMUL_WITHIN, HAS_COMPLEX_DERIVATIVE_RMUL_AT,
         HAS_COMPLEX_DERIVATIVE_CDIV_WITHIN, HAS_COMPLEX_DERIVATIVE_CDIV_AT,
         HAS_COMPLEX_DERIVATIVE_ID, HAS_COMPLEX_DERIVATIVE_CONST,
         HAS_COMPLEX_DERIVATIVE_NEG, HAS_COMPLEX_DERIVATIVE_ADD,
         HAS_COMPLEX_DERIVATIVE_SUB, HAS_COMPLEX_DERIVATIVE_MUL_WITHIN,
         HAS_COMPLEX_DERIVATIVE_MUL_AT, HAS_COMPLEX_DERIVATIVE_POW_WITHIN,
         HAS_COMPLEX_DERIVATIVE_POW_AT, HAS_COMPLEX_DERIVATIVE_INV_BASIC,
         HAS_COMPLEX_DERIVATIVE_INV_WITHIN, HAS_COMPLEX_DERIVATIVE_INV_AT,
         HAS_COMPLEX_DERIVATIVE_DIV_WITHIN, HAS_COMPLEX_DERIVATIVE_DIV_AT,
         HAS_COMPLEX_DERIVATIVE_VSUM }

/- ------------------------------------------------------------------------- -/
/- Same thing just for complex differentiability.  (canal.ml 1414-1597)     -/
/- ------------------------------------------------------------------------- -/

structure KNG where
  COMPLEX_DIFFERENTIABLE_LINEAR : thm
  COMPLEX_DIFFERENTIABLE_CONST : thm
  COMPLEX_DIFFERENTIABLE_ID : thm
  COMPLEX_DIFFERENTIABLE_NEG : thm
  COMPLEX_DIFFERENTIABLE_ADD : thm
  COMPLEX_DIFFERENTIABLE_SUB : thm
  COMPLEX_DIFFERENTIABLE_INV_WITHIN : thm
  COMPLEX_DIFFERENTIABLE_MUL_WITHIN : thm
  COMPLEX_DIFFERENTIABLE_DIV_WITHIN : thm
  COMPLEX_DIFFERENTIABLE_POW_WITHIN : thm
  COMPLEX_DIFFERENTIABLE_CPRODUCT_WITHIN : thm
  COMPLEX_DIFFERENTIABLE_TRANSFORM_WITHIN : thm
  HOLOMORPHIC_TRANSFORM : thm
  HOLOMORPHIC_EQ : thm
  COMPLEX_DIFFERENTIABLE_INV_AT : thm
  COMPLEX_DIFFERENTIABLE_MUL_AT : thm
  COMPLEX_DIFFERENTIABLE_DIV_AT : thm
  COMPLEX_DIFFERENTIABLE_POW_AT : thm
  COMPLEX_DIFFERENTIABLE_CPRODUCT_AT : thm
  COMPLEX_DIFFERENTIABLE_TRANSFORM_AT : thm
  COMPLEX_DIFFERENTIABLE_COMPOSE_WITHIN : thm
  COMPLEX_DIFFERENTIABLE_COMPOSE_AT : thm
  COMPLEX_DIFFERENTIABLE_WITHIN_OPEN : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupKNG [HolBase] (D : CanalDeps) (BKNE : KNE) (BKNF : KNF) : ExceptT String IO KNG := do
  -- @@SCOPE BEGIN
  let { COMPLEX_DIFF_CHAIN_AT, COMPLEX_DIFF_CHAIN_WITHIN, complex_differentiable,
        HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT, HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN,
        HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN, holomorphic_on, .. } := BKNE
  let { HAS_COMPLEX_DERIVATIVE_ADD, HAS_COMPLEX_DERIVATIVE_CONST,
        HAS_COMPLEX_DERIVATIVE_DIV_AT, HAS_COMPLEX_DERIVATIVE_DIV_WITHIN,
        HAS_COMPLEX_DERIVATIVE_ID, HAS_COMPLEX_DERIVATIVE_INV_AT,
        HAS_COMPLEX_DERIVATIVE_INV_WITHIN, HAS_COMPLEX_DERIVATIVE_LINEAR,
        HAS_COMPLEX_DERIVATIVE_MUL_AT, HAS_COMPLEX_DERIVATIVE_MUL_WITHIN,
        HAS_COMPLEX_DERIVATIVE_NEG, HAS_COMPLEX_DERIVATIVE_POW_AT,
        HAS_COMPLEX_DERIVATIVE_POW_WITHIN, HAS_COMPLEX_DERIVATIVE_SUB, .. } := BKNF
  let { CPRODUCT_CLAUSES, .. } := D.cxk
  let { MESON_TAC, .. } := D.cx.cvx
  let { ETA_AX, FINITE_INDUCT_STRONG, .. } := D.cx.cvx.core1
  let { FORALL_IN_INSERT, IMP_CONJ, .. } := D.cx.cvx.core2
  let { MONO_FORALL, .. } := D.cx.cvx.core3
  let { REAL_LT_01, .. } := D.cx.cvx.core4
  let { RIGHT_FORALL_IMP_THM, .. } := D.cx.cvx.core5
  -- @@SCOPE END

  let COMPLEX_DIFFERENTIABLE_LINEAR ← prove
   r"(\z. c * z) complex_differentiable p"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_LINEAR])

  let COMPLEX_DIFFERENTIABLE_CONST ← prove
   r"!c net. (\z. c) complex_differentiable net"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_CONST])

  let COMPLEX_DIFFERENTIABLE_ID ← prove
   r"!net. (\z. z) complex_differentiable net"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_ID])

  let COMPLEX_DIFFERENTIABLE_NEG ← prove
   r"!f net.
        f complex_differentiable net
        ==> (\z. --(f z)) complex_differentiable net"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_NEG])

  let COMPLEX_DIFFERENTIABLE_ADD ← prove
   r"!f g net.
        f complex_differentiable net /\
        g complex_differentiable net
        ==> (\z. f z + g z) complex_differentiable net"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_ADD])

  let COMPLEX_DIFFERENTIABLE_SUB ← prove
   r"!f g net.
        f complex_differentiable net /\
        g complex_differentiable net
        ==> (\z. f z - g z) complex_differentiable net"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_SUB])

  let COMPLEX_DIFFERENTIABLE_INV_WITHIN ← prove
   r"!f z s.
        f complex_differentiable (at z within s) /\ ~(f z = Cx(&0))
        ==> (\z. inv(f z)) complex_differentiable (at z within s)"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_INV_WITHIN])

  let COMPLEX_DIFFERENTIABLE_MUL_WITHIN ← prove
   r"!f g z s.
        f complex_differentiable (at z within s) /\
        g complex_differentiable (at z within s)
        ==> (\z. f z * g z) complex_differentiable (at z within s)"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_MUL_WITHIN])

  let COMPLEX_DIFFERENTIABLE_DIV_WITHIN ← prove
   r"!f g z s.
        f complex_differentiable (at z within s) /\
        g complex_differentiable (at z within s) /\
        ~(g z = Cx(&0))
        ==> (\z. f z / g z) complex_differentiable (at z within s)"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_DIV_WITHIN])

  let COMPLEX_DIFFERENTIABLE_POW_WITHIN ← prove
   r"!f n z s.
        f complex_differentiable (at z within s)
        ==> (\z. f z pow n) complex_differentiable (at z within s)"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_POW_WITHIN])

  let COMPLEX_DIFFERENTIABLE_CPRODUCT_WITHIN ← prove
   r"!f k:A->bool z s.
        FINITE k /\
        (!i. i IN k ==> f i complex_differentiable (at z within s))
        ==> (\z. cproduct k (\i. f i z)) complex_differentiable
            (at z within s)"
   (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [CPRODUCT_CLAUSES, COMPLEX_DIFFERENTIABLE_CONST, FORALL_IN_INSERT,
              ETA_AX, COMPLEX_DIFFERENTIABLE_MUL_WITHIN])

  let COMPLEX_DIFFERENTIABLE_TRANSFORM_WITHIN ← prove
   r"!f g x s d.
        &0 < d /\
        x IN s /\
        (!x'. x' IN s /\ dist (x',x) < d ==> f x' = g x') /\
        f complex_differentiable (at x within s)
        ==> g complex_differentiable (at x within s)"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN])

  let HOLOMORPHIC_TRANSFORM ← prove
   r"!f g s. (!x. x IN s ==> f x = g x) /\ f holomorphic_on s
           ==> g holomorphic_on s"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [holomorphic_on, ← GSYM complex_differentiable] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [← q r"f:complex->complex", ← q r"&1"] THEN
    ASM_SIMP_TAC [REAL_LT_01])

  let HOLOMORPHIC_EQ ← prove
   r"!f g s. (!x. x IN s ==> f x = g x)
           ==> (f holomorphic_on s <=> g holomorphic_on s)"
   (MESON_TAC [HOLOMORPHIC_TRANSFORM])

  let COMPLEX_DIFFERENTIABLE_INV_AT ← prove
   r"!f z.
        f complex_differentiable at z /\ ~(f z = Cx(&0))
        ==> (\z. inv(f z)) complex_differentiable at z"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_INV_AT])

  let COMPLEX_DIFFERENTIABLE_MUL_AT ← prove
   r"!f g z.
        f complex_differentiable at z /\
        g complex_differentiable at z
        ==> (\z. f z * g z) complex_differentiable at z"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_MUL_AT])

  let COMPLEX_DIFFERENTIABLE_DIV_AT ← prove
   r"!f g z.
        f complex_differentiable at z /\
        g complex_differentiable at z /\
        ~(g z = Cx(&0))
        ==> (\z. f z / g z) complex_differentiable at z"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_DIV_AT])

  let COMPLEX_DIFFERENTIABLE_POW_AT ← prove
   r"!f n z.
        f complex_differentiable at z
        ==> (\z. f z pow n) complex_differentiable at z"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_POW_AT])

  let COMPLEX_DIFFERENTIABLE_CPRODUCT_AT ← prove
   r"!f k:A->bool z.
        FINITE k /\
        (!i. i IN k ==> f i complex_differentiable (at z))
        ==> (\z. cproduct k (\i. f i z)) complex_differentiable (at z)"
   (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [CPRODUCT_CLAUSES, COMPLEX_DIFFERENTIABLE_CONST, FORALL_IN_INSERT,
              ETA_AX, COMPLEX_DIFFERENTIABLE_MUL_AT])

  let COMPLEX_DIFFERENTIABLE_TRANSFORM_AT ← prove
   r"!f g x d.
        &0 < d /\
        (!x'. dist (x',x) < d ==> f x' = g x') /\
        f complex_differentiable at x
        ==> g complex_differentiable at x"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT])

  let COMPLEX_DIFFERENTIABLE_COMPOSE_WITHIN ← prove
   r"!f g x s.
         f complex_differentiable (at x within s) /\
         g complex_differentiable (at (f x) within IMAGE f s)
         ==> (g o f) complex_differentiable (at x within s)"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [COMPLEX_DIFF_CHAIN_WITHIN])

  let COMPLEX_DIFFERENTIABLE_COMPOSE_AT ← prove
   r"!f g x.
         f complex_differentiable (at x) /\
         g complex_differentiable (at (f x))
         ==> (g o f) complex_differentiable (at x)"
   (REWRITE_TAC [complex_differentiable] THEN
    MESON_TAC [COMPLEX_DIFF_CHAIN_AT])

  let COMPLEX_DIFFERENTIABLE_WITHIN_OPEN ← prove
   r"!f a s.
        a IN s /\ open s
        ==> (f complex_differentiable at a within s <=>
             f complex_differentiable at a)"
   (SIMP_TAC [complex_differentiable, HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN])

  pure { COMPLEX_DIFFERENTIABLE_LINEAR, COMPLEX_DIFFERENTIABLE_CONST,
         COMPLEX_DIFFERENTIABLE_ID, COMPLEX_DIFFERENTIABLE_NEG,
         COMPLEX_DIFFERENTIABLE_ADD, COMPLEX_DIFFERENTIABLE_SUB,
         COMPLEX_DIFFERENTIABLE_INV_WITHIN, COMPLEX_DIFFERENTIABLE_MUL_WITHIN,
         COMPLEX_DIFFERENTIABLE_DIV_WITHIN, COMPLEX_DIFFERENTIABLE_POW_WITHIN,
         COMPLEX_DIFFERENTIABLE_CPRODUCT_WITHIN, COMPLEX_DIFFERENTIABLE_TRANSFORM_WITHIN,
         HOLOMORPHIC_TRANSFORM, HOLOMORPHIC_EQ, COMPLEX_DIFFERENTIABLE_INV_AT,
         COMPLEX_DIFFERENTIABLE_MUL_AT, COMPLEX_DIFFERENTIABLE_DIV_AT,
         COMPLEX_DIFFERENTIABLE_POW_AT, COMPLEX_DIFFERENTIABLE_CPRODUCT_AT,
         COMPLEX_DIFFERENTIABLE_TRANSFORM_AT, COMPLEX_DIFFERENTIABLE_COMPOSE_WITHIN,
         COMPLEX_DIFFERENTIABLE_COMPOSE_AT, COMPLEX_DIFFERENTIABLE_WITHIN_OPEN }
/- ------------------------------------------------------------------------- -/
/- Same again for being holomorphic on a set, and for the actual derivative  -/
/- function; Caratheodory characterization.  (canal.ml 1598-1848)          -/
/- ------------------------------------------------------------------------- -/

structure KNH where
  HOLOMORPHIC_ON_LINEAR : thm
  HOLOMORPHIC_ON_CONST : thm
  HOLOMORPHIC_ON_ID : thm
  HOLOMORPHIC_ON_COMPOSE : thm
  HOLOMORPHIC_ON_NEG : thm
  HOLOMORPHIC_ON_ADD : thm
  HOLOMORPHIC_ON_SUB : thm
  HOLOMORPHIC_ON_MUL : thm
  HOLOMORPHIC_ON_LMUL : thm
  HOLOMORPHIC_ON_RMUL : thm
  HOLOMORPHIC_ON_INV : thm
  HOLOMORPHIC_ON_DIV : thm
  HOLOMORPHIC_ON_POW : thm
  HOLOMORPHIC_ON_VSUM : thm
  HOLOMORPHIC_ON_CPRODUCT : thm
  HOLOMORPHIC_ON_COMPOSE_GEN : thm
  HAS_COMPLEX_DERIVATIVE_DERIVATIVE : thm
  HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE : thm
  COMPLEX_DERIVATIVE_CHAIN : thm
  COMPLEX_DERIVATIVE_LINEAR : thm
  COMPLEX_DERIVATIVE_ID : thm
  COMPLEX_DERIVATIVE_CONST : thm
  COMPLEX_DERIVATIVE_ADD : thm
  COMPLEX_DERIVATIVE_SUB : thm
  COMPLEX_DERIVATIVE_MUL : thm
  COMPLEX_DERIVATIVE_LMUL : thm
  COMPLEX_DERIVATIVE_RMUL : thm
  COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN : thm
  COMPLEX_DERIVATIVE_COMPOSE_LINEAR : thm
  HAS_COMPLEX_DERIVATIVE_CARATHEODORY_AT : thm
  HAS_COMPLEX_DERIVATIVE_CARATHEODORY_WITHIN : thm
  COMPLEX_DIFFERENTIABLE_CARATHEODORY_AT : thm
  COMPLEX_DIFFERENTIABLE_CARATHEODORY_WITHIN : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupKNH [HolBase] (D : CanalDeps) (BKNE : KNE) (BKNF : KNF) (BKNG : KNG) : ExceptT String IO KNH := do
  -- @@SCOPE BEGIN
  let { complex_derivative, COMPLEX_DERIVATIVE_UNIQUE_AT, COMPLEX_DIFF_CHAIN_AT,
        COMPLEX_DIFF_CHAIN_WITHIN, complex_differentiable,
        HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN, HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET,
        holomorphic_on, HOLOMORPHIC_ON_DIFFERENTIABLE,
        HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT, .. } := BKNE
  let { HAS_COMPLEX_DERIVATIVE_ADD, HAS_COMPLEX_DERIVATIVE_AT,
        HAS_COMPLEX_DERIVATIVE_CONST, HAS_COMPLEX_DERIVATIVE_ID,
        HAS_COMPLEX_DERIVATIVE_LINEAR, HAS_COMPLEX_DERIVATIVE_LMUL_AT,
        HAS_COMPLEX_DERIVATIVE_MUL_AT, HAS_COMPLEX_DERIVATIVE_RMUL_AT,
        HAS_COMPLEX_DERIVATIVE_SUB, HAS_COMPLEX_DERIVATIVE_WITHIN, .. } := BKNF
  let { COMPLEX_DIFFERENTIABLE_ADD, COMPLEX_DIFFERENTIABLE_COMPOSE_WITHIN,
        COMPLEX_DIFFERENTIABLE_CONST, COMPLEX_DIFFERENTIABLE_CPRODUCT_WITHIN,
        COMPLEX_DIFFERENTIABLE_DIV_WITHIN, COMPLEX_DIFFERENTIABLE_ID,
        COMPLEX_DIFFERENTIABLE_INV_WITHIN, COMPLEX_DIFFERENTIABLE_LINEAR,
        COMPLEX_DIFFERENTIABLE_MUL_WITHIN, COMPLEX_DIFFERENTIABLE_NEG,
        COMPLEX_DIFFERENTIABLE_POW_WITHIN, COMPLEX_DIFFERENTIABLE_SUB, .. } := BKNG
  let { COMPLEX_MUL_SYM, COMPLEX_SUB_REFL, .. } := D.cxb
  let { COMPLEX_VEC_0, .. } := D.cxc
  let { COMPLEX_RING, .. } := D.cxd
  let { COMPLEX_FIELD, .. } := D.cxe
  let { ASM_MESON_TAC, MESON_TAC, SET_TAC, .. } := D.cx.cvx
  let { COND_RAND, COND_RATOR, ETA_AX, FINITE_INDUCT_STRONG, .. } := D.cx.cvx.core1
  let { FORALL_IN_IMAGE, FUN_EQ_THM, IMP_CONJ, IMP_CONJ_ALT, .. } := D.cx.cvx.core2
  let { IN_INSERT, NOT_IN_EMPTY, .. } := D.cx.cvx.core3
  let { o_DEF, .. } := D.cx.cvx.core6
  let { VSUM_CLAUSES, .. } := D.cx.cvx.vec4
  let { CONTINUOUS_WITHIN, .. } := D.cx.cvx.top3
  let { LIM_CONST, .. } := D.cx.cvx.top4
  let { CONTINUOUS_AT, .. } := D.ms.ig.dv.qtopology1
  let { LIM_TRANSFORM, .. } := D.ms.ig.dv.qtopology2
  -- @@SCOPE END

  let HOLOMORPHIC_ON_LINEAR ← prove
   r"!s c. (\w. c * w) holomorphic_on s"
   (REWRITE_TAC [holomorphic_on] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_LINEAR])

  let HOLOMORPHIC_ON_CONST ← prove
   r"!c s. (\z. c) holomorphic_on s"
   (REWRITE_TAC [HOLOMORPHIC_ON_DIFFERENTIABLE, COMPLEX_DIFFERENTIABLE_CONST])

  let HOLOMORPHIC_ON_ID ← prove
   r"!s. (\z. z) holomorphic_on s"
   (REWRITE_TAC [HOLOMORPHIC_ON_DIFFERENTIABLE, COMPLEX_DIFFERENTIABLE_ID])

  let HOLOMORPHIC_ON_COMPOSE ← prove
   r"!f g s. f holomorphic_on s /\ g holomorphic_on (IMAGE f s)
           ==> (g o f) holomorphic_on s"
   (SIMP_TAC [holomorphic_on, ← GSYM complex_differentiable, FORALL_IN_IMAGE] THEN
    MESON_TAC [COMPLEX_DIFFERENTIABLE_COMPOSE_WITHIN])

  let HOLOMORPHIC_ON_NEG ← prove
   r"!f s. f holomorphic_on s ==> (\z. --(f z)) holomorphic_on s"
   (SIMP_TAC [HOLOMORPHIC_ON_DIFFERENTIABLE, COMPLEX_DIFFERENTIABLE_NEG])

  let HOLOMORPHIC_ON_ADD ← prove
   r"!f g s.
        f holomorphic_on s /\ g holomorphic_on s
        ==> (\z. f z + g z) holomorphic_on s"
   (SIMP_TAC [HOLOMORPHIC_ON_DIFFERENTIABLE, COMPLEX_DIFFERENTIABLE_ADD])

  let HOLOMORPHIC_ON_SUB ← prove
   r"!f g s.
        f holomorphic_on s /\ g holomorphic_on s
        ==> (\z. f z - g z) holomorphic_on s"
   (SIMP_TAC [HOLOMORPHIC_ON_DIFFERENTIABLE, COMPLEX_DIFFERENTIABLE_SUB])

  let HOLOMORPHIC_ON_MUL ← prove
   r"!f g s.
        f holomorphic_on s /\ g holomorphic_on s
        ==> (\z. f z * g z) holomorphic_on s"
   (SIMP_TAC [HOLOMORPHIC_ON_DIFFERENTIABLE, COMPLEX_DIFFERENTIABLE_MUL_WITHIN])

  let HOLOMORPHIC_ON_LMUL ← prove
   r"!f c s. f holomorphic_on s ==> (\x. c * f x) holomorphic_on s"
   (SIMP_TAC [HOLOMORPHIC_ON_MUL, HOLOMORPHIC_ON_CONST])

  let HOLOMORPHIC_ON_RMUL ← prove
   r"!f c s. f holomorphic_on s ==> (\x. f x * c) holomorphic_on s"
   (SIMP_TAC [HOLOMORPHIC_ON_MUL, HOLOMORPHIC_ON_CONST])

  let HOLOMORPHIC_ON_INV ← prove
   r"!f s. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
         ==> (\z. inv(f z)) holomorphic_on s"
   (SIMP_TAC [HOLOMORPHIC_ON_DIFFERENTIABLE, COMPLEX_DIFFERENTIABLE_INV_WITHIN])

  let HOLOMORPHIC_ON_DIV ← prove
   r"!f g s.
        f holomorphic_on s /\ g holomorphic_on s /\
        (!z. z IN s ==> ~(g z = Cx(&0)))
        ==> (\z. f z / g z) holomorphic_on s"
   (SIMP_TAC [HOLOMORPHIC_ON_DIFFERENTIABLE, COMPLEX_DIFFERENTIABLE_DIV_WITHIN])

  let HOLOMORPHIC_ON_POW ← prove
   r"!f s n. f holomorphic_on s ==> (\z. (f z) pow n) holomorphic_on s"
   (SIMP_TAC [HOLOMORPHIC_ON_DIFFERENTIABLE, COMPLEX_DIFFERENTIABLE_POW_WITHIN])

  let HOLOMORPHIC_ON_VSUM ← prove
   r"!f s k. FINITE k /\ (!a. a IN k ==> (f a) holomorphic_on s)
           ==> (\x. vsum k (\a. f a x)) holomorphic_on s"
   (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC [VSUM_CLAUSES] THEN
    SIMP_TAC [HOLOMORPHIC_ON_CONST, IN_INSERT, NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_ADD THEN
    ASM_SIMP_TAC [ETA_AX])

  let HOLOMORPHIC_ON_CPRODUCT ← prove
   r"!f k:A->bool s.
        FINITE k /\
        (!i. i IN k ==> f i holomorphic_on s)
        ==> (\z. cproduct k (\i. f i z)) holomorphic_on s"
   (SIMP_TAC [HOLOMORPHIC_ON_DIFFERENTIABLE,
              COMPLEX_DIFFERENTIABLE_CPRODUCT_WITHIN])

  let HOLOMORPHIC_ON_COMPOSE_GEN ← prove
   r"!f g s t. f holomorphic_on s /\ g holomorphic_on t /\
             (!z. z IN s ==> f z IN t)
             ==>  g o f holomorphic_on s"
   (REWRITE_TAC [holomorphic_on] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"IMAGE (f:complex->complex) s SUBSET t") MP_TAC THENL
     [ASM SET_TAC [], ASM_MESON_TAC [HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET,
                                     COMPLEX_DIFF_CHAIN_WITHIN]])

  let HAS_COMPLEX_DERIVATIVE_DERIVATIVE ← prove
   r"!f f' x. (f has_complex_derivative f') (at x)
                ==> complex_derivative f x = f'"
   (REWRITE_TAC [complex_derivative] THEN
    MESON_TAC [COMPLEX_DERIVATIVE_UNIQUE_AT])

  let HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE ← prove
   r"!f x. (f has_complex_derivative (complex_derivative f x)) (at x) <=>
         f complex_differentiable at x"
   (REWRITE_TAC [complex_differentiable, complex_derivative] THEN MESON_TAC [])

  let COMPLEX_DERIVATIVE_CHAIN ← prove
   r"!f g z. f complex_differentiable at z /\ g complex_differentiable at (f z)
           ==> complex_derivative (g o f) z =
               complex_derivative g (f z) * complex_derivative f z"
   (MESON_TAC [HAS_COMPLEX_DERIVATIVE_DERIVATIVE, COMPLEX_DIFF_CHAIN_AT,
               HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE])

  let COMPLEX_DERIVATIVE_LINEAR ← prove
   r"!c. complex_derivative (\w. c * w) = \z. c"
   (REWRITE_TAC [FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
    REWRITE_TAC [HAS_COMPLEX_DERIVATIVE_LINEAR])

  let COMPLEX_DERIVATIVE_ID ← prove
   r"complex_derivative (\w.w) = \z. Cx(&1)"
   (REWRITE_TAC [FUN_EQ_THM] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_DERIVATIVE, HAS_COMPLEX_DERIVATIVE_ID])

  let COMPLEX_DERIVATIVE_CONST ← prove
   r"!c. complex_derivative (\w.c) = \z. Cx(&0)"
   (REWRITE_TAC [FUN_EQ_THM] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_DERIVATIVE,
               HAS_COMPLEX_DERIVATIVE_CONST])

  let COMPLEX_DERIVATIVE_ADD ← prove
   r"!f g z. f complex_differentiable at z /\ g complex_differentiable at z
           ==> complex_derivative (\w. f w + g w) z =
               complex_derivative f z + complex_derivative g z"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
    ASM_SIMP_TAC [HAS_COMPLEX_DERIVATIVE_ADD,
                  HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE])

  let COMPLEX_DERIVATIVE_SUB ← prove
   r"!f g z. f complex_differentiable at z /\ g complex_differentiable at z
           ==> complex_derivative (\w. f w - g w) z =
               complex_derivative f z - complex_derivative g z"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
    ASM_SIMP_TAC [HAS_COMPLEX_DERIVATIVE_SUB,
                  HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE])

  let COMPLEX_DERIVATIVE_MUL ← prove
   r"!f g z. f complex_differentiable at z /\ g complex_differentiable at z
           ==> complex_derivative (\w. f w * g w) z =
               f z * complex_derivative g z + complex_derivative f z * g z"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
    ASM_SIMP_TAC [HAS_COMPLEX_DERIVATIVE_MUL_AT,
                  HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE])

  let COMPLEX_DERIVATIVE_LMUL ← prove
   r"!f c z. f complex_differentiable at z
             ==> complex_derivative (\w. c * f w) z =
                 c * complex_derivative f z"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
    ASM_SIMP_TAC [HAS_COMPLEX_DERIVATIVE_LMUL_AT,
                  HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE])

  let COMPLEX_DERIVATIVE_RMUL ← prove
   r"!f c z. f complex_differentiable at z
           ==> complex_derivative (\w. f w * c) z =
               complex_derivative f z * c"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
    ASM_SIMP_TAC [HAS_COMPLEX_DERIVATIVE_RMUL_AT,
                  HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE])

  let COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN ← prove
   r"!f g s z. open s /\ f holomorphic_on s /\ g holomorphic_on s /\ z IN s /\
             (!w. w IN s ==> f w = g w)
             ==> complex_derivative f z = complex_derivative g z"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPLEX_DERIVATIVE_UNIQUE_AT THEN
    ASM_MESON_TAC [HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN,
                   HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT,
                   HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE])

  let COMPLEX_DERIVATIVE_COMPOSE_LINEAR ← prove
   r"!f c z. f complex_differentiable at (c * z)
           ==> complex_derivative (\w. f (c * w)) z =
               c * complex_derivative f (c * z)"
   (SIMP_TAC
      [COMPLEX_MUL_SYM, ← REWRITE_RULE [o_DEF, COMPLEX_DIFFERENTIABLE_ID,
                     COMPLEX_DIFFERENTIABLE_LINEAR,
                     COMPLEX_DERIVATIVE_LINEAR]
       (← SPECL [← q r"\w:complex. c * w"] COMPLEX_DERIVATIVE_CHAIN)])

  let HAS_COMPLEX_DERIVATIVE_CARATHEODORY_AT ← prove
   r"!f f' z.
        (f has_complex_derivative f') (at z) <=>
        ?g. (!w. f(w) - f(z) = g(w) * (w - z)) /\
            g continuous at z /\ g(z) = f'"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"w' - z':complex = a <=> w' = z' + a"))] THEN
    SIMP_TAC [← GSYM FUN_EQ_THM, HAS_COMPLEX_DERIVATIVE_AT, CONTINUOUS_AT] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
     [EXISTS_TAC (← q r"\w. if w = z then f':complex else (f(w) - f(z)) / (w - z)") THEN
      ASM_SIMP_TAC [FUN_EQ_THM, COND_RAND, COND_RATOR, COMPLEX_SUB_REFL] THEN
      CONV_TAC COMPLEX_FIELD,
      FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
      ASM_SIMP_TAC [← ExceptT.mk (COMPLEX_RING
        (← q r"(z + a) - (z + b * (w - w)):complex = a"))] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT]
        LIM_TRANSFORM)) THEN
      SIMP_TAC [LIM_CONST, COMPLEX_VEC_0, ← ExceptT.mk (COMPLEX_FIELD
       (← q r"~(w = z) ==> x - (x * (w - z)) / (w - z) = Cx(&0)"))]])

  let HAS_COMPLEX_DERIVATIVE_CARATHEODORY_WITHIN ← prove
   r"!f f' z s.
        (f has_complex_derivative f') (at z within s) <=>
        ?g. (!w. f(w) - f(z) = g(w) * (w - z)) /\
            g continuous (at z within s) /\ g(z) = f'"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"w' - z':complex = a <=> w' = z' + a"))] THEN
    SIMP_TAC [← GSYM FUN_EQ_THM, HAS_COMPLEX_DERIVATIVE_WITHIN,
              CONTINUOUS_WITHIN] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
     [EXISTS_TAC (← q r"\w. if w = z then f':complex else (f(w) - f(z)) / (w - z)") THEN
      ASM_SIMP_TAC [FUN_EQ_THM, COND_RAND, COND_RATOR, COMPLEX_SUB_REFL] THEN
      CONV_TAC COMPLEX_FIELD,
      FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
      ASM_SIMP_TAC [← ExceptT.mk (COMPLEX_RING
        (← q r"(z + a) - (z + b * (w - w)):complex = a"))] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT]
        LIM_TRANSFORM)) THEN
      SIMP_TAC [LIM_CONST, COMPLEX_VEC_0, ← ExceptT.mk (COMPLEX_FIELD
       (← q r"~(w = z) ==> x - (x * (w - z)) / (w - z) = Cx(&0)"))]])

  let COMPLEX_DIFFERENTIABLE_CARATHEODORY_AT ← prove
   r"!f z. f complex_differentiable at z <=>
         ?g. (!w. f(w) - f(z) = g(w) * (w - z)) /\ g continuous at z"
   (SIMP_TAC [complex_differentiable, HAS_COMPLEX_DERIVATIVE_CARATHEODORY_AT] THEN
    MESON_TAC [])

  let COMPLEX_DIFFERENTIABLE_CARATHEODORY_WITHIN ← prove
   r"!f z s.
      f complex_differentiable (at z within s) <=>
      ?g. (!w. f(w) - f(z) = g(w) * (w - z)) /\ g continuous (at z within s)"
   (SIMP_TAC [complex_differentiable,
              HAS_COMPLEX_DERIVATIVE_CARATHEODORY_WITHIN] THEN
    MESON_TAC [])

  pure { HOLOMORPHIC_ON_LINEAR, HOLOMORPHIC_ON_CONST, HOLOMORPHIC_ON_ID,
         HOLOMORPHIC_ON_COMPOSE, HOLOMORPHIC_ON_NEG, HOLOMORPHIC_ON_ADD,
         HOLOMORPHIC_ON_SUB, HOLOMORPHIC_ON_MUL, HOLOMORPHIC_ON_LMUL, HOLOMORPHIC_ON_RMUL,
         HOLOMORPHIC_ON_INV, HOLOMORPHIC_ON_DIV, HOLOMORPHIC_ON_POW, HOLOMORPHIC_ON_VSUM,
         HOLOMORPHIC_ON_CPRODUCT, HOLOMORPHIC_ON_COMPOSE_GEN,
         HAS_COMPLEX_DERIVATIVE_DERIVATIVE, HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE,
         COMPLEX_DERIVATIVE_CHAIN, COMPLEX_DERIVATIVE_LINEAR, COMPLEX_DERIVATIVE_ID,
         COMPLEX_DERIVATIVE_CONST, COMPLEX_DERIVATIVE_ADD, COMPLEX_DERIVATIVE_SUB,
         COMPLEX_DERIVATIVE_MUL, COMPLEX_DERIVATIVE_LMUL, COMPLEX_DERIVATIVE_RMUL,
         COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN, COMPLEX_DERIVATIVE_COMPOSE_LINEAR,
         HAS_COMPLEX_DERIVATIVE_CARATHEODORY_AT,
         HAS_COMPLEX_DERIVATIVE_CARATHEODORY_WITHIN,
         COMPLEX_DIFFERENTIABLE_CARATHEODORY_AT,
         COMPLEX_DIFFERENTIABLE_CARATHEODORY_WITHIN }
/- ------------------------------------------------------------------------- -/
/- A slightly stronger, more traditional notion of analyticity on a set; the -/
/- case of analyticity at a point; combining theorems for the derivative     -/
/- with analytic_at {z} hypotheses.  (canal.ml 1849-2107)                   -/
/- ------------------------------------------------------------------------- -/

structure KNI where
  analytic_on : thm
  ANALYTIC_IMP_HOLOMORPHIC : thm
  ANALYTIC_ON_OPEN : thm
  ANALYTIC_ON_IMP_DIFFERENTIABLE_AT : thm
  ANALYTIC_ON_SUBSET : thm
  ANALYTIC_ON_UNION : thm
  ANALYTIC_ON_UNIONS : thm
  ANALYTIC_ON_HOLOMORPHIC : thm
  ANALYTIC_ON_LINEAR : thm
  ANALYTIC_ON_CONST : thm
  ANALYTIC_ON_ID : thm
  ANALYTIC_ON_COMPOSE : thm
  ANALYTIC_ON_COMPOSE_GEN : thm
  ANALYTIC_ON_NEG : thm
  ANALYTIC_ON_ADD : thm
  ANALYTIC_ON_SUB : thm
  ANALYTIC_ON_MUL : thm
  ANALYTIC_ON_INV : thm
  ANALYTIC_ON_DIV : thm
  ANALYTIC_ON_POW : thm
  ANALYTIC_ON_VSUM : thm
  ANALYTIC_AT_BALL : thm
  ANALYTIC_AT : thm
  ANALYTIC_ON_ANALYTIC_AT : thm
  ANALYTIC_AT_TWO : thm
  ANALYTIC_AT_ADD : thm
  ANALYTIC_AT_SUB : thm
  ANALYTIC_AT_MUL : thm
  ANALYTIC_AT_POW : thm
  COMPLEX_DERIVATIVE_ADD_AT : thm
  COMPLEX_DERIVATIVE_SUB_AT : thm
  COMPLEX_DERIVATIVE_MUL_AT : thm
  COMPLEX_DERIVATIVE_LMUL_AT : thm
  COMPLEX_DERIVATIVE_RMUL_AT : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupKNI [HolBase] (D : CanalDeps) (BKNE : KNE) (BKNH : KNH) : ExceptT String IO KNI := do
  -- @@SCOPE BEGIN
  let { complex_differentiable, HAS_COMPLEX_DERIVATIVE_AT_WITHIN,
        HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN, holomorphic_on,
        HOLOMORPHIC_ON_IMP_CONTINUOUS_ON, HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT,
        HOLOMORPHIC_ON_OPEN, HOLOMORPHIC_ON_SUBSET, .. } := BKNE
  let { COMPLEX_DERIVATIVE_ADD, COMPLEX_DERIVATIVE_LMUL, COMPLEX_DERIVATIVE_MUL,
        COMPLEX_DERIVATIVE_RMUL, COMPLEX_DERIVATIVE_SUB, HOLOMORPHIC_ON_ADD,
        HOLOMORPHIC_ON_COMPOSE, HOLOMORPHIC_ON_CONST, HOLOMORPHIC_ON_ID,
        HOLOMORPHIC_ON_INV, HOLOMORPHIC_ON_LINEAR, HOLOMORPHIC_ON_MUL, HOLOMORPHIC_ON_NEG,
        HOLOMORPHIC_ON_POW, HOLOMORPHIC_ON_SUB, .. } := BKNH
  let { complex_div, complex_pow, complex_sub, .. } := D.cxa
  let { CONTINUOUS_AT_BALL, CONTINUOUS_ON_OPEN_AVOID, .. } := D.qtopology
  let { OPEN_UNIONS, .. } := D.ms.qtopology2
  let { ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, new_definition, parse_as_infix, SET_TAC,
        .. } := D.cx.cvx
  let { AND_FORALL_THM, EQ_TRANS, ETA_AX, FINITE_INDUCT_STRONG, .. } := D.cx.cvx.core1
  let { FORALL_IN_IMAGE, IMP_CONJ, INTER_SUBSET, .. } := D.cx.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, IN_INTER, IN_SING, IN_UNION, IN_UNIONS, MONO_FORALL,
        NOT_IN_EMPTY, .. } := D.cx.cvx.core3
  let { REAL_LT_01, REAL_LT_MIN, .. } := D.cx.cvx.core4
  let { RIGHT_FORALL_IMP_THM, SING_SUBSET, SUBSET, .. } := D.cx.cvx.core5
  let { SUBSET_UNIV, .. } := D.cx.cvx.core6
  let { VSUM_CLAUSES, .. } := D.cx.cvx.vec4
  let { BALL_MIN_INTER, CENTRE_IN_BALL, .. } := D.cx.cvx.top1
  let { IN_BALL, OPEN_BALL, OPEN_CONTAINS_BALL, .. } := D.cx.cvx.top4
  let { OPEN_INTER, OPEN_UNIV, .. } := D.cx.cvx.top5
  let { CONTINUOUS_ON_EQ_CONTINUOUS_AT, .. } := D.ms.ig.dv.qtopology1
  -- @@SCOPE END

  parse_as_infix ("analytic_on", (12, "right"))

  let analytic_on ← new_definition
   r"f analytic_on s <=>
        !x. x IN s ==> ?e. &0 < e /\ f holomorphic_on ball(x,e)"

  let ANALYTIC_IMP_HOLOMORPHIC ← prove
   r"!f s. f analytic_on s ==> f holomorphic_on s"
   (REWRITE_TAC [analytic_on, holomorphic_on] THEN
    SIMP_TAC [HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN, OPEN_BALL] THEN
    MESON_TAC [HAS_COMPLEX_DERIVATIVE_AT_WITHIN, CENTRE_IN_BALL])

  let ANALYTIC_ON_OPEN ← prove
   r"!f s. open s ==> (f analytic_on s <=> f holomorphic_on s)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC [ANALYTIC_IMP_HOLOMORPHIC] THEN
    REWRITE_TAC [analytic_on, holomorphic_on] THEN
    ASM_SIMP_TAC [HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN, OPEN_BALL] THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    REWRITE_TAC [SUBSET] THEN MESON_TAC [CENTRE_IN_BALL])

  let ANALYTIC_ON_IMP_DIFFERENTIABLE_AT ← prove
   r"!f s x. f analytic_on s /\ x IN s ==> f complex_differentiable (at x)"
   (SIMP_TAC [analytic_on, HOLOMORPHIC_ON_OPEN, OPEN_BALL,
              complex_differentiable] THEN
    MESON_TAC [CENTRE_IN_BALL])

  let ANALYTIC_ON_SUBSET ← prove
   r"!f s t. f analytic_on s /\ t SUBSET s ==> f analytic_on t"
   (REWRITE_TAC [analytic_on, SUBSET] THEN MESON_TAC [])

  let ANALYTIC_ON_UNION ← prove
   r"!f s t. f analytic_on (s UNION t) <=> f analytic_on s /\ f analytic_on t"
   (REWRITE_TAC [analytic_on, IN_UNION] THEN MESON_TAC [])

  let ANALYTIC_ON_UNIONS ← prove
   r"!f s. f analytic_on (UNIONS s) <=> (!t. t IN s ==> f analytic_on t)"
   (REWRITE_TAC [analytic_on, IN_UNIONS] THEN MESON_TAC [])

  let ANALYTIC_ON_HOLOMORPHIC ← prove
   r"!f s. f analytic_on s <=> ?t. open t /\ s SUBSET t /\ f holomorphic_on t"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"?t. open t /\ s SUBSET t /\ f analytic_on t") THEN CONJ_TAC THENL
     [EQ_TAC THENL
      [DISCH_TAC THEN EXISTS_TAC (← q r"UNIONS {u | open u /\ f analytic_on u}") THEN
       SIMP_TAC [IN_ELIM_THM, OPEN_UNIONS, ANALYTIC_ON_UNIONS] THEN
       REWRITE_TAC [SUBSET, IN_UNIONS, IN_ELIM_THM] THEN
       ASM_MESON_TAC [analytic_on, ANALYTIC_ON_OPEN, OPEN_BALL, CENTRE_IN_BALL],
       MESON_TAC [ANALYTIC_ON_SUBSET]],
      MESON_TAC [ANALYTIC_ON_OPEN]])

  let ANALYTIC_ON_LINEAR ← prove
   r"!s c. (\w. c * w) analytic_on s"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [ANALYTIC_ON_HOLOMORPHIC, HOLOMORPHIC_ON_LINEAR] THEN
    EXISTS_TAC (← q r"(:complex)") THEN REWRITE_TAC [OPEN_UNIV, SUBSET_UNIV])

  let ANALYTIC_ON_CONST ← prove
   r"!c s. (\z. c) analytic_on s"
   (REWRITE_TAC [analytic_on, HOLOMORPHIC_ON_CONST] THEN MESON_TAC [REAL_LT_01])

  let ANALYTIC_ON_ID ← prove
   r"!s. (\z. z) analytic_on s"
   (REWRITE_TAC [analytic_on, HOLOMORPHIC_ON_ID] THEN MESON_TAC [REAL_LT_01])

  let ANALYTIC_ON_COMPOSE ← prove
   r"!f g s. f analytic_on s /\ g analytic_on (IMAGE f s)
           ==> (g o f) analytic_on s"
   (REWRITE_TAC [analytic_on, FORALL_IN_IMAGE] THEN REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "f") (LABEL_TAC "g")) THEN
    X_GEN_TAC (← q r"z:complex") THEN DISCH_TAC THEN
    REMOVE_THEN "f" (MP_TAC o SPEC (← q r"z:complex")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP HOLOMORPHIC_ON_IMP_CONTINUOUS_ON) THEN
    SIMP_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_AT, OPEN_BALL] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"z:complex")) THEN
    ASM_REWRITE_TAC [CENTRE_IN_BALL, CONTINUOUS_AT_BALL] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"z:complex")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"e:real") STRIP_ASSUME_TAC) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"e:real")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"k:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"min (d:real) k") THEN ASM_REWRITE_TAC [REAL_LT_MIN] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN
    CONJ_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THENL
     [EXISTS_TAC (← q r"ball(z:complex,d)"),
      EXISTS_TAC (← q r"ball((f:complex->complex) z,e)")] THEN
    ASM_REWRITE_TAC [BALL_MIN_INTER, INTER_SUBSET] THEN ASM SET_TAC [])

  let ANALYTIC_ON_COMPOSE_GEN ← prove
   r"!f g s t. f analytic_on s /\ g analytic_on t /\ (!z. z IN s ==> f z IN t)
             ==> g o f analytic_on s"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC ANALYTIC_ON_COMPOSE THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC ANALYTIC_ON_SUBSET THEN ASM SET_TAC [])

  let ANALYTIC_ON_NEG ← prove
   r"!f s. f analytic_on s ==> (\z. --(f z)) analytic_on s"
   (SIMP_TAC [analytic_on] THEN MESON_TAC [HOLOMORPHIC_ON_NEG])

  let ANALYTIC_ON_ADD ← prove
   r"!f g s.
        f analytic_on s /\ g analytic_on s ==> (\z. f z + g z) analytic_on s"
   (REPEAT GEN_TAC THEN REWRITE_TAC [analytic_on] THEN
    REWRITE_TAC [AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
    GEN_TAC THEN DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_TAC (← q r"d:real")) (X_CHOOSE_TAC (← q r"e:real"))) THEN
    EXISTS_TAC (← q r"min (d:real) e") THEN
    ASM_REWRITE_TAC [REAL_LT_MIN, BALL_MIN_INTER, IN_INTER] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_ADD THEN
    ASM_MESON_TAC [HOLOMORPHIC_ON_SUBSET, INTER_SUBSET])

  let ANALYTIC_ON_SUB ← prove
   r"!f g s.
        f analytic_on s /\ g analytic_on s ==> (\z. f z - g z) analytic_on s"
   (SIMP_TAC [complex_sub, ANALYTIC_ON_ADD, ANALYTIC_ON_NEG])

  let ANALYTIC_ON_MUL ← prove
   r"!f g s.
        f analytic_on s /\ g analytic_on s ==> (\z. f z * g z) analytic_on s"
   (REPEAT GEN_TAC THEN REWRITE_TAC [analytic_on] THEN
    REWRITE_TAC [AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
    GEN_TAC THEN DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_TAC (← q r"d:real")) (X_CHOOSE_TAC (← q r"e:real"))) THEN
    EXISTS_TAC (← q r"min (d:real) e") THEN
    ASM_REWRITE_TAC [REAL_LT_MIN, BALL_MIN_INTER, IN_INTER] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
    ASM_MESON_TAC [HOLOMORPHIC_ON_SUBSET, INTER_SUBSET])

  let ANALYTIC_ON_INV ← prove
   r"!f s. f analytic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
         ==> (\z. inv(f z)) analytic_on s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [analytic_on] THEN
    X_GEN_TAC (← q r"z:complex") THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [analytic_on]) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"z:complex")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"?e. &0 < e /\ !y:complex. dist(z,y) < e ==> ~(f y = Cx(&0))")
    MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_OPEN_AVOID THEN
      EXISTS_TAC (← q r"ball(z:complex,d)") THEN
      ASM_SIMP_TAC [HOLOMORPHIC_ON_IMP_CONTINUOUS_ON, CENTRE_IN_BALL, OPEN_BALL],
      REWRITE_TAC [← GSYM IN_BALL] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"e:real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"min (d:real) e") THEN ASM_REWRITE_TAC [REAL_LT_MIN] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_INV THEN
      ASM_SIMP_TAC [BALL_MIN_INTER, IN_INTER] THEN
      ASM_MESON_TAC [HOLOMORPHIC_ON_SUBSET, INTER_SUBSET]])

  let ANALYTIC_ON_DIV ← prove
   r"!f g s.
        f analytic_on s /\ g analytic_on s /\
        (!z. z IN s ==> ~(g z = Cx(&0)))
        ==> (\z. f z / g z) analytic_on s"
   (SIMP_TAC [complex_div, ANALYTIC_ON_MUL, ANALYTIC_ON_INV])

  let ANALYTIC_ON_POW ← prove
   r"!f s n. f analytic_on s ==> (\z. (f z) pow n) analytic_on s"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
    DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC [complex_pow] THEN
    ASM_SIMP_TAC [ANALYTIC_ON_CONST, ANALYTIC_ON_MUL])

  let ANALYTIC_ON_VSUM ← prove
   r"!f s k. FINITE k /\ (!a. a IN k ==> (f a) analytic_on s)
           ==> (\x. vsum k (\a. f a x)) analytic_on s"
   (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC [VSUM_CLAUSES] THEN
    SIMP_TAC [ANALYTIC_ON_CONST, IN_INSERT, NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC ANALYTIC_ON_ADD THEN
    ASM_SIMP_TAC [ETA_AX])

  let ANALYTIC_AT_BALL ← prove
   r"!f z. f analytic_on {z} <=> ?e. &0<e /\ f holomorphic_on ball (z,e)"
   (REWRITE_TAC [analytic_on, IN_SING] THEN MESON_TAC [])

  let ANALYTIC_AT ← prove
   r"!f z. f analytic_on {z} <=> ?s. open s /\ z IN s /\ f holomorphic_on s"
   (REWRITE_TAC [ANALYTIC_ON_HOLOMORPHIC, SING_SUBSET])

  let ANALYTIC_ON_ANALYTIC_AT ← prove
   r"!f s. f analytic_on s <=> !z. z IN s ==> f analytic_on {z}"
   (REWRITE_TAC [ANALYTIC_AT_BALL, analytic_on])

  let ANALYTIC_AT_TWO ← prove
   r"!f g z. f analytic_on {z} /\ g analytic_on {z} <=>
    ?s. open s /\ z IN s /\ f holomorphic_on s /\ g holomorphic_on s"
   (REWRITE_TAC [ANALYTIC_AT] THEN
    MESON_TAC [HOLOMORPHIC_ON_SUBSET, OPEN_INTER, INTER_SUBSET, IN_INTER])

  let ANALYTIC_AT_ADD ← prove
   r"!f g z. f analytic_on {z} /\ g analytic_on {z}
     ==> (\w. f w + g w) analytic_on {z}"
   (REWRITE_TAC [ANALYTIC_AT_TWO] THEN REWRITE_TAC [ANALYTIC_AT] THEN
    MESON_TAC [HOLOMORPHIC_ON_ADD])

  let ANALYTIC_AT_SUB ← prove
   r"!f g z. f analytic_on {z} /\ g analytic_on {z}
     ==> (\w. f w - g w) analytic_on {z}"
   (REWRITE_TAC [ANALYTIC_AT_TWO] THEN REWRITE_TAC [ANALYTIC_AT] THEN
    MESON_TAC [HOLOMORPHIC_ON_SUB])

  let ANALYTIC_AT_MUL ← prove
   r"!f g z. f analytic_on {z} /\ g analytic_on {z}

     ==> (\w. f w * g w) analytic_on {z}"
   (REWRITE_TAC [ANALYTIC_AT_TWO] THEN REWRITE_TAC [ANALYTIC_AT] THEN
    MESON_TAC [HOLOMORPHIC_ON_MUL])

  let ANALYTIC_AT_POW ← prove
   r"!f n z. f analytic_on {z}
     ==> (\w. f w pow n) analytic_on {z}"
   (REWRITE_TAC [ANALYTIC_AT] THEN MESON_TAC [HOLOMORPHIC_ON_POW])

  let COMPLEX_DERIVATIVE_ADD_AT ← prove
   r"!f g z. f analytic_on {z} /\ g analytic_on {z}
     ==> complex_derivative (\w. f w + g w) z =
           complex_derivative f z + complex_derivative g z"
   (REWRITE_TAC [ANALYTIC_AT_TWO] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COMPLEX_DERIVATIVE_ADD THEN
    ASM_MESON_TAC [HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT])

  let COMPLEX_DERIVATIVE_SUB_AT ← prove
   r"!f g z. f analytic_on {z} /\ g analytic_on {z}
     ==> complex_derivative (\w. f w - g w) z =
           complex_derivative f z - complex_derivative g z"
   (REWRITE_TAC [ANALYTIC_AT_TWO] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COMPLEX_DERIVATIVE_SUB THEN
    ASM_MESON_TAC [HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT])

  let COMPLEX_DERIVATIVE_MUL_AT ← prove
   r"!f g z. f analytic_on {z} /\ g analytic_on {z}
     ==> complex_derivative (\w. f w * g w) z =
           f z * complex_derivative g z + complex_derivative f z * g z"
   (REWRITE_TAC [ANALYTIC_AT_TWO] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COMPLEX_DERIVATIVE_MUL THEN
    ASM_MESON_TAC [HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT])

  let COMPLEX_DERIVATIVE_LMUL_AT ← prove
   r"!f c z. f analytic_on {z}
    ==> complex_derivative (\w. c * f w) z = c * complex_derivative f z"
   (REWRITE_TAC [ANALYTIC_AT] THEN
    MESON_TAC [HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT, COMPLEX_DERIVATIVE_LMUL])

  let COMPLEX_DERIVATIVE_RMUL_AT ← prove
   r"!f c z. f analytic_on {z}
    ==> complex_derivative (\w. f w * c) z = complex_derivative f z * c"
   (REWRITE_TAC [ANALYTIC_AT] THEN
    MESON_TAC [HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT, COMPLEX_DERIVATIVE_RMUL])

  pure { analytic_on, ANALYTIC_IMP_HOLOMORPHIC, ANALYTIC_ON_OPEN,
         ANALYTIC_ON_IMP_DIFFERENTIABLE_AT, ANALYTIC_ON_SUBSET, ANALYTIC_ON_UNION,
         ANALYTIC_ON_UNIONS, ANALYTIC_ON_HOLOMORPHIC, ANALYTIC_ON_LINEAR,
         ANALYTIC_ON_CONST, ANALYTIC_ON_ID, ANALYTIC_ON_COMPOSE, ANALYTIC_ON_COMPOSE_GEN,
         ANALYTIC_ON_NEG, ANALYTIC_ON_ADD, ANALYTIC_ON_SUB, ANALYTIC_ON_MUL,
         ANALYTIC_ON_INV, ANALYTIC_ON_DIV, ANALYTIC_ON_POW, ANALYTIC_ON_VSUM,
         ANALYTIC_AT_BALL, ANALYTIC_AT, ANALYTIC_ON_ANALYTIC_AT, ANALYTIC_AT_TWO,
         ANALYTIC_AT_ADD, ANALYTIC_AT_SUB, ANALYTIC_AT_MUL, ANALYTIC_AT_POW,
         COMPLEX_DERIVATIVE_ADD_AT, COMPLEX_DERIVATIVE_SUB_AT, COMPLEX_DERIVATIVE_MUL_AT,
         COMPLEX_DERIVATIVE_LMUL_AT, COMPLEX_DERIVATIVE_RMUL_AT }
/- ------------------------------------------------------------------------- -/
/- A composition lemma for functions of mixed type; complex differentiation  -/
/- of sequences and series; bound theorem; inverse function theorem for     -/
/- complex derivatives; Cauchy-Riemann condition and relation to conformal. -/
/- (canal.ml 2108-2405)                                                     -/
/- ------------------------------------------------------------------------- -/

structure KNJ where
  HAS_VECTOR_DERIVATIVE_REAL_COMPLEX : thm
  DIFFERENTIABLE_REAL_COMPLEX : thm
  HAS_COMPLEX_DERIVATIVE_SEQUENCE : thm
  HAS_COMPLEX_DERIVATIVE_SERIES : thm
  COMPLEX_DIFFERENTIABLE_BOUND : thm
  HAS_COMPLEX_DERIVATIVE_INVERSE_BASIC : thm
  HAS_COMPLEX_DERIVATIVE_INVERSE_STRONG : thm
  HAS_COMPLEX_DERIVATIVE_INVERSE_STRONG_X : thm
  CAUCHY_RIEMANN : thm
  COMPLEX_DERIVATIVE_JACOBIAN : thm
  JACOBIAN_COMPLEX_DERIVATIVE : thm
  COMPLEX_DIFFERENTIABLE_EQ_CONFORMAL : thm
  HOLOMORPHIC_CONSTANT_RE : thm
  HOLOMORPHIC_CONSTANT_IM : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupKNJ [HolBase] (D : CanalDeps) (BKND : KND) (BKNE : KNE) (BKNH : KNH) : ExceptT String IO KNJ := do
  -- @@SCOPE BEGIN
  let { LINEAR_CX_IM, LINEAR_CX_RE, .. } := BKND
  let { COMPLEX_DERIVATIVE_UNIQUE_AT, complex_differentiable,
        COMPLEX_DIFFERENTIABLE_IMP_DIFFERENTIABLE, has_complex_derivative,
        HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT, .. } := BKNE
  let { HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE, .. } := BKNH
  let { complex, complex_mul, IM, IM_DEF, RE, RE_DEF, .. } := D.cxa
  let { COMPLEX_MUL_SYM, COMPLEX_SUB_RDISTRIB, .. } := D.cxb
  let { COMPLEX_CMUL, COMPLEX_VEC_0, CX_ADD, CX_INJ, CX_MUL, .. } := D.cxc
  let { COMPLEX_FIELD, .. } := D.cxe
  let { COMPLEX_NORM_MUL, .. } := D.cxf
  let { COMPLEX_LINEAR, LINEAR_COMPLEX_MUL, .. } := D.cxh
  let { VSUM_COMPLEX_RMUL, .. } := D.cxi
  let { DIFF_CHAIN_AT, DIFFERENTIABLE_BOUND, FRECHET_DERIVATIVE_AT,
        FRECHET_DERIVATIVE_UNIQUE_AT, HAS_DERIVATIVE_INVERSE_BASIC,
        HAS_DERIVATIVE_INVERSE_STRONG, HAS_DERIVATIVE_INVERSE_STRONG_X,
        HAS_DERIVATIVE_SEQUENCE, HAS_DERIVATIVE_SERIES,
        HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN, HAS_DERIVATIVE_ZERO_CONNECTED_CONSTANT,
        JACOBIAN_WORKS, vector_derivative, .. } := D.qderivatives
  let { ROTATION_MATRIX_2, .. } := D.qdeterminants
  let { MATRIX_CMUL_COMPONENT, .. } := D.qvectors
  let { HAS_DERIVATIVE_LINEAR, HAS_FRECHET_DERIVATIVE_UNIQUE_AT, jacobian,
        .. } := D.ms.qderivatives
  let { DET_2, .. } := D.ms.qdet
  let { ASM_MESON_TAC, MESON, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD, REAL_RING,
        .. } := D.cx.cvx
  let { FORALL_2, matrix, MATRIX_VECTOR_MUL_COMPONENT, SUM_2, VECTOR_2, .. } := D.cx.cpx
  let { differentiable, has_derivative, HAS_DERIVATIVE_CONST, has_vector_derivative,
        VECTOR_DERIVATIVE_WORKS, .. } := D.ms.ig.qderivatives
  let { ARITH, CART_EQ, DIMINDEX_2, EQ_IMP, FINITE_INTER, FINITE_NUMSEG,
        .. } := D.cx.cvx.core1
  let { FUN_EQ_THM, IMP_CONJ, .. } := D.cx.cvx.core2
  let { I_THM, LAMBDA_BETA, REAL_ADD_LDISTRIB, .. } := D.cx.cvx.core3
  let { REAL_LE_ADD, REAL_LE_POW_2, REAL_LE_RMUL, .. } := D.cx.cvx.core4
  let { REAL_MUL_RNEG, REAL_POW_2, SQRT_POW_2, .. } := D.cx.cvx.core5
  let { o_DEF, o_THM, .. } := D.cx.cvx.core6
  let { BASIS_COMPONENT, DOT_2, DOT_EQ_0, .. } := D.cx.cvx.vec1
  let { DROP_ADD, DROP_CMUL, .. } := D.cx.cvx.vec2
  let { NORM_POS_LE, NORM_POW_2, .. } := D.cx.cvx.vec3
  let { linear, matrix_vector_mul, VEC_COMPONENT, .. } := D.cx.cvx.vec4
  let { FORALL_DOT_EQ_0, ONORM, .. } := D.ms.ig.dv.qvec
  let { REAL_EQ_MUL_LCANCEL, .. } := D.ms.ig.dv.dg.pt.qses
  -- @@SCOPE END

  let HAS_VECTOR_DERIVATIVE_REAL_COMPLEX ← prove
   r"(f has_complex_derivative f') (at(Cx(drop a)))
     ==> ((\x. f(Cx(drop x))) has_vector_derivative f') (at a)"
   (REWRITE_TAC [has_complex_derivative, has_vector_derivative] THEN
    REWRITE_TAC [COMPLEX_CMUL] THEN MP_TAC (← ISPECL
     [← q r"\x. Cx(drop x)", ← q r"f:complex->complex",
      ← q r"\x. Cx(drop x)", ← q r"\x:complex. f' * x", ← q r"a:real^1"] DIFF_CHAIN_AT) THEN
    REWRITE_TAC [o_DEF, COMPLEX_MUL_SYM, IMP_CONJ] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC [linear, DROP_ADD, DROP_CMUL, CX_ADD, CX_MUL, COMPLEX_CMUL])

  let DIFFERENTIABLE_REAL_COMPLEX ← prove
   r"!f a. f complex_differentiable at (Cx(drop a))
         ==> (\x. f(Cx(drop x))) differentiable at a"
   (REWRITE_TAC [complex_differentiable, VECTOR_DERIVATIVE_WORKS] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [vector_derivative] THEN
    ASM_MESON_TAC [HAS_VECTOR_DERIVATIVE_REAL_COMPLEX])

  let HAS_COMPLEX_DERIVATIVE_SEQUENCE ← prove
   r"!s f f' g'.
         convex s /\
         (!n x. x IN s
                ==> (f n has_complex_derivative f' n x) (at x within s)) /\
         (!e. &0 < e
              ==> ?N. !n x. n >= N /\ x IN s ==> norm (f' n x - g' x) <= e) /\
         (?x l. x IN s /\ ((\n. f n x) --> l) sequentially)
         ==> ?g. !x. x IN s
                     ==> ((\n. f n x) --> g x) sequentially /\
                         (g has_complex_derivative g' x) (at x within s)"
   (REWRITE_TAC [has_complex_derivative] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SEQUENCE THEN
    EXISTS_TAC (← q r"\n x h:complex. (f':num->complex->complex) n x * h") THEN
    ASM_SIMP_TAC [] THEN CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
    REWRITE_TAC [← GSYM COMPLEX_SUB_RDISTRIB, COMPLEX_NORM_MUL] THEN
    ASM_MESON_TAC [REAL_LE_RMUL, NORM_POS_LE])

  let HAS_COMPLEX_DERIVATIVE_SERIES ← prove
   r"!s f f' g' k.
         convex s /\
         (!n x. x IN s
                ==> (f n has_complex_derivative f' n x) (at x within s)) /\
         (!e. &0 < e
              ==> ?N. !n x. n >= N /\ x IN s
                            ==> norm(vsum (k INTER (0..n)) (\i. f' i x) - g' x)
                                    <= e) /\
         (?x l. x IN s /\ ((\n. f n x) sums l) k)
         ==> ?g. !x. x IN s
                     ==> ((\n. f n x) sums g x) k /\
                         (g has_complex_derivative g' x) (at x within s)"
   (REWRITE_TAC [has_complex_derivative] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SERIES THEN
    EXISTS_TAC (← q r"\n x h:complex. (f':num->complex->complex) n x * h") THEN
    ASM_SIMP_TAC [] THEN CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
    SIMP_TAC [← GSYM COMPLEX_SUB_RDISTRIB, VSUM_COMPLEX_RMUL, FINITE_NUMSEG,
              FINITE_INTER, COMPLEX_NORM_MUL] THEN
    ASM_MESON_TAC [REAL_LE_RMUL, NORM_POS_LE])

  let COMPLEX_DIFFERENTIABLE_BOUND ← prove
   r"!f f' s B.
        convex s /\
        (!x. x IN s ==> (f has_complex_derivative f'(x)) (at x within s) /\
                        norm(f' x) <= B)
        ==> !x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [has_complex_derivative] THEN
    STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_BOUND THEN
    EXISTS_TAC (← q r"\x:complex h. f' x * h") THEN ASM_SIMP_TAC [] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"\h. (f':complex->complex) x * h") ONORM) THEN
    REWRITE_TAC [LINEAR_COMPLEX_MUL] THEN
    DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN
    GEN_TAC THEN REWRITE_TAC [COMPLEX_NORM_MUL] THEN
    ASM_MESON_TAC [REAL_LE_RMUL, NORM_POS_LE])

  let HAS_COMPLEX_DERIVATIVE_INVERSE_BASIC ← prove
   r"!f g f' t y.
        (f has_complex_derivative f') (at (g y)) /\
        ~(f' = Cx(&0)) /\
        g continuous at y /\
        open t /\
        y IN t /\
        (!z. z IN t ==> f (g z) = z)
        ==> (g has_complex_derivative inv(f')) (at y)"
   (REWRITE_TAC [has_complex_derivative] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_INVERSE_BASIC THEN
    MAP_EVERY EXISTS_TAC
     [← q r"f:complex->complex", ← q r"\x:complex. f' * x", ← q r"t:complex->bool"] THEN
    ASM_REWRITE_TAC [LINEAR_COMPLEX_MUL, FUN_EQ_THM, o_THM, I_THM] THEN
    UNDISCH_TAC (← q r"~(f' = Cx(&0))") THEN CONV_TAC COMPLEX_FIELD)

  let HAS_COMPLEX_DERIVATIVE_INVERSE_STRONG ← prove
   r"!f g f' s x.
         open s /\
         x IN s /\
         f continuous_on s /\
         (!x. x IN s ==> g (f x) = x) /\
         (f has_complex_derivative f') (at x) /\
         ~(f' = Cx(&0))
         ==> (g has_complex_derivative inv(f')) (at (f x))"
   (REWRITE_TAC [has_complex_derivative] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_INVERSE_STRONG THEN
    MAP_EVERY EXISTS_TAC [← q r"\x:complex. f' * x", ← q r"s:complex->bool"] THEN
    ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [FUN_EQ_THM, o_THM, I_THM] THEN
    UNDISCH_TAC (← q r"~(f' = Cx(&0))") THEN CONV_TAC COMPLEX_FIELD)

  let HAS_COMPLEX_DERIVATIVE_INVERSE_STRONG_X ← prove
   r"!f g f' s y.
        open s /\ (g y) IN s /\ f continuous_on s /\
        (!x. x IN s ==> (g(f(x)) = x)) /\
        (f has_complex_derivative f') (at (g y)) /\ ~(f' = Cx(&0)) /\
        f(g y) = y
        ==> (g has_complex_derivative inv(f')) (at y)"
   (REWRITE_TAC [has_complex_derivative] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_INVERSE_STRONG_X THEN MAP_EVERY EXISTS_TAC
     [← q r"f:complex->complex", ← q r"\x:complex. f' * x", ← q r"s:complex->bool"] THEN
    ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [FUN_EQ_THM, o_THM, I_THM] THEN
    UNDISCH_TAC (← q r"~(f' = Cx(&0))") THEN CONV_TAC COMPLEX_FIELD)

  let CAUCHY_RIEMANN ← prove
   r"!f z. f complex_differentiable at z <=>
         f differentiable at z  /\
         (jacobian f (at z))$1$1 = (jacobian f (at z))$2$2 /\
         (jacobian f (at z))$1$2 = --((jacobian f (at z))$2$1)"
   (REPEAT GEN_TAC THEN
    SIMP_TAC [complex_differentiable, differentiable, has_complex_derivative] THEN
    MATCH_MP_TAC (← MESON []
     (← q r"(!y. (f has_derivative y) (at z)
           ==> ((?x. y = h x) <=> P f))
      ==> ((?x. (f has_derivative (h x)) (at z)) <=>
           (?y. (f has_derivative y) (at z)) /\ P f)")) THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [jacobian] THEN
    FIRST_ASSUM (SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [has_derivative]) THEN
    ASM_REWRITE_TAC [COMPLEX_LINEAR])

  let COMPLEX_DERIVATIVE_JACOBIAN ← prove
   r"!f z.
        f complex_differentiable (at z)
        ==> complex_derivative f z =
            complex(jacobian f (at z)$1$1,jacobian f (at z)$2$1)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPLEX_DERIVATIVE_UNIQUE_AT THEN
    MAP_EVERY EXISTS_TAC [← q r"f:complex->complex", ← q r"z:complex"] THEN
    ASM_REWRITE_TAC [HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
    REWRITE_TAC [has_complex_derivative] THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [CAUCHY_RIEMANN]) THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [JACOBIAN_WORKS]) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC [CART_EQ, matrix_vector_mul, DIMINDEX_2, SUM_2, ARITH,
                  FORALL_2, FUN_EQ_THM, LAMBDA_BETA] THEN
    REWRITE_TAC [← GSYM RE_DEF, ← GSYM IM_DEF, IM, RE, complex_mul] THEN
    REAL_ARITH_TAC)

  let JACOBIAN_COMPLEX_DERIVATIVE ← prove
   r"!f f' z.
        (f has_complex_derivative f') (at z)
        ==> det(jacobian f (at z)) = norm(f') pow 2"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← EQ_IMP_RULE (← ISPECL [← q r"f:complex->complex", ← q r"z:complex"]
          CAUCHY_RIEMANN)).1 THEN
    ANTS_TAC THENL [ASM_MESON_TAC [complex_differentiable], STRIP_TAC] THEN
    ASM_REWRITE_TAC [DET_2, ← GSYM DOT_2, ← GSYM NORM_POW_2, ← REAL_ARITH
     (← q r"y * y - --x * x:real = x * x + y * y")] THEN
    REWRITE_TAC [jacobian] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [has_complex_derivative]) THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP HAS_FRECHET_DERIVATIVE_UNIQUE_AT) THEN
    SIMP_TAC [NORM_POW_2, DOT_2, matrix, LAMBDA_BETA, DIMINDEX_2, ARITH, complex,
              complex_mul, VECTOR_2, IM_DEF, RE_DEF, BASIS_COMPONENT] THEN
    REAL_ARITH_TAC)

  let COMPLEX_DIFFERENTIABLE_EQ_CONFORMAL ← prove
   r"!f z.
      f complex_differentiable at z /\ ~(complex_derivative f z = Cx(&0)) <=>
      f differentiable at z  /\
      ?a. ~(a = &0) /\ rotation_matrix (a %% jacobian f (at z))"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_SIMP_TAC [COMPLEX_DIFFERENTIABLE_IMP_DIFFERENTIABLE,
                    COMPLEX_DERIVATIVE_JACOBIAN] THEN
      REWRITE_TAC [← GSYM COMPLEX_VEC_0, ← GSYM DOT_EQ_0] THEN
      REWRITE_TAC [DOT_2, ← GSYM RE_DEF, ← GSYM IM_DEF, RE, IM, ← GSYM REAL_POW_2] THEN
      REWRITE_TAC [RE_DEF, IM_DEF, ROTATION_MATRIX_2] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [CAUCHY_RIEMANN]) THEN
      ASM_REWRITE_TAC [MATRIX_CMUL_COMPONENT] THEN DISCH_TAC THEN
      REWRITE_TAC [REAL_MUL_RNEG, ← GSYM REAL_ADD_LDISTRIB,
                   ← REAL_ARITH (← q r"(a * x:real) pow 2 = a pow 2 * x pow 2")] THEN
      EXISTS_TAC
       (← q r"inv(sqrt(jacobian (f:complex->complex) (at z)$2$2 pow 2 +
                 jacobian f (at z)$2$1 pow 2))") THEN
      MATCH_MP_TAC (← REAL_FIELD
       (← q r"x pow 2 = y /\ ~(y = &0)
        ==> ~(inv x = &0) /\ inv(x) pow 2 * y = &1")) THEN
      ASM_SIMP_TAC [SQRT_POW_2, REAL_LE_ADD, REAL_LE_POW_2],
      REWRITE_TAC [ROTATION_MATRIX_2, MATRIX_CMUL_COMPONENT] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"a:real") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ASM_REWRITE_TAC [← GSYM REAL_MUL_RNEG, REAL_EQ_MUL_LCANCEL] THEN
      STRIP_TAC THEN MATCH_MP_TAC (← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")) THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC [CAUCHY_RIEMANN], DISCH_TAC] THEN
      ASM_SIMP_TAC [COMPLEX_DERIVATIVE_JACOBIAN] THEN
      REWRITE_TAC [← GSYM COMPLEX_VEC_0, ← GSYM DOT_EQ_0] THEN
      REWRITE_TAC [DOT_2, ← GSYM RE_DEF, ← GSYM IM_DEF, RE, IM, ← GSYM REAL_POW_2] THEN
      FIRST_X_ASSUM (MP_TAC o MATCH_MP
       (← REAL_RING (← q r"(a * x) pow 2 + (a * y) pow 2 = &1
                   ==> ~(x pow 2 + y pow 2 = &0)"))) THEN
      ASM_REWRITE_TAC [RE_DEF, IM_DEF]])

  let HOLOMORPHIC_CONSTANT_RE ← prove
   r"!f s. open s /\ connected s /\
         f holomorphic_on s /\
         (?c. !z. z IN s ==> Re(f z) = c)
         ==> (?a. !z. z IN s ==> f z = a)"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ZERO_CONNECTED_CONSTANT THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"!z. z IN s ==> f complex_differentiable at z") MP_TAC
    THENL [ASM_MESON_TAC [HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT], ALL_TAC] THEN
    REWRITE_TAC [CAUCHY_RIEMANN, JACOBIAN_WORKS] THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"z:complex") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"(\h. jacobian (f:complex->complex) (at z) ** h) = (\h. vec 0)")
     (fun th => tactic_of do pure (ASM_SIMP_TAC [← GSYM th])) THEN
    SUBGOAL_THEN
     (← q r"(Cx o Re) o (\h. jacobian (f:complex->complex) (at z) ** h) = (\h. vec 0)")
    MP_TAC THENL
     [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
      MAP_EVERY EXISTS_TAC [← q r"(Cx o Re) o (f:complex->complex)", ← q r"z:complex"] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC DIFF_CHAIN_AT THEN
        ASM_SIMP_TAC [HAS_DERIVATIVE_LINEAR, LINEAR_CX_RE],
        MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
        MAP_EVERY EXISTS_TAC
         [← q r"(\z. Cx c):complex->complex", ← q r"s:complex->bool"] THEN
        ASM_SIMP_TAC [HAS_DERIVATIVE_CONST, o_THM]],
      REWRITE_TAC [COMPLEX_VEC_0] THEN
      REWRITE_TAC [FUN_EQ_THM, o_THM, RE_DEF, CX_INJ] THEN
      SIMP_TAC [MATRIX_VECTOR_MUL_COMPONENT, DIMINDEX_2, ARITH] THEN
      REWRITE_TAC [FORALL_DOT_EQ_0] THEN
      REWRITE_TAC [CART_EQ, FORALL_2, DIMINDEX_2, VEC_COMPONENT] THEN
      REWRITE_TAC [← GSYM COMPLEX_VEC_0] THEN
      SIMP_TAC [MATRIX_VECTOR_MUL_COMPONENT, DIMINDEX_2, ARITH] THEN
      SIMP_TAC [DOT_2, VEC_COMPONENT] THEN STRIP_TAC THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"z:complex"))) THEN
      ASM_REWRITE_TAC [] THEN CONV_TAC (fun t => REAL_RING t)])

  let HOLOMORPHIC_CONSTANT_IM ← prove
   r"!f s. open s /\ connected s /\
         f holomorphic_on s /\
         (?c. !z. z IN s ==> Im(f z) = c)
         ==> (?a. !z. z IN s ==> f z = a)"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ZERO_CONNECTED_CONSTANT THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"!z. z IN s ==> f complex_differentiable at z") MP_TAC
    THENL [ASM_MESON_TAC [HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT], ALL_TAC] THEN
    REWRITE_TAC [CAUCHY_RIEMANN, JACOBIAN_WORKS] THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"z:complex") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"(\h. jacobian (f:complex->complex) (at z) ** h) = (\h. vec 0)")
     (fun th => tactic_of do pure (ASM_SIMP_TAC [← GSYM th])) THEN
    SUBGOAL_THEN
     (← q r"(Cx o Im) o (\h. jacobian (f:complex->complex) (at z) ** h) = (\h. vec 0)")
    MP_TAC THENL
     [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
      MAP_EVERY EXISTS_TAC [← q r"(Cx o Im) o (f:complex->complex)", ← q r"z:complex"] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC DIFF_CHAIN_AT THEN
        ASM_SIMP_TAC [HAS_DERIVATIVE_LINEAR, LINEAR_CX_IM],
        MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
        MAP_EVERY EXISTS_TAC
         [← q r"(\z. Cx c):complex->complex", ← q r"s:complex->bool"] THEN
        ASM_SIMP_TAC [HAS_DERIVATIVE_CONST, o_THM]],
      REWRITE_TAC [COMPLEX_VEC_0] THEN
      REWRITE_TAC [FUN_EQ_THM, o_THM, IM_DEF, CX_INJ] THEN
      SIMP_TAC [MATRIX_VECTOR_MUL_COMPONENT, DIMINDEX_2, ARITH] THEN
      REWRITE_TAC [FORALL_DOT_EQ_0] THEN
      REWRITE_TAC [CART_EQ, FORALL_2, DIMINDEX_2, VEC_COMPONENT] THEN
      REWRITE_TAC [← GSYM COMPLEX_VEC_0] THEN
      SIMP_TAC [MATRIX_VECTOR_MUL_COMPONENT, DIMINDEX_2, ARITH] THEN
      SIMP_TAC [DOT_2, VEC_COMPONENT] THEN STRIP_TAC THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"z:complex"))) THEN
      ASM_REWRITE_TAC [] THEN CONV_TAC (fun t => REAL_RING t)])

  pure { HAS_VECTOR_DERIVATIVE_REAL_COMPLEX, DIFFERENTIABLE_REAL_COMPLEX,
         HAS_COMPLEX_DERIVATIVE_SEQUENCE, HAS_COMPLEX_DERIVATIVE_SERIES,
         COMPLEX_DIFFERENTIABLE_BOUND, HAS_COMPLEX_DERIVATIVE_INVERSE_BASIC,
         HAS_COMPLEX_DERIVATIVE_INVERSE_STRONG, HAS_COMPLEX_DERIVATIVE_INVERSE_STRONG_X,
         CAUCHY_RIEMANN, COMPLEX_DERIVATIVE_JACOBIAN, JACOBIAN_COMPLEX_DERIVATIVE,
         COMPLEX_DIFFERENTIABLE_EQ_CONFORMAL, HOLOMORPHIC_CONSTANT_RE,
         HOLOMORPHIC_CONSTANT_IM }

/- ------------------------------------------------------------------------- -/
/- Differentiation conversion; hence a tactic.  (canal.ml 2406-2488)        -/
/- ------------------------------------------------------------------------- -/

/-- lib.ml's `repeat` for a rule that can fail: apply `f` until it fails. -/
private partial def repeatRule (f : thm → ExceptT String IO thm) (x : thm) :
    ExceptT String IO thm :=
  tryWith (do repeatRule f (← f x)) (pure x)

mutual
/-- The `let rec COMPLEX_DIFF_CONV tm` of canal.ml 2440-2447, over the
    theorem list ref (dereferenced on every call, as `!` does), `ths'`,
    `partfn` and `is_deriv`. -/
partial def complexDiffConvGo [HolBase] (cdt : IO.Ref (List thm)) (ths' : List thm)
    (partfn : term → Except String term) (is_deriv : term → ExceptT String IO Bool)
    (tm : term) : ExceptT String IO thm := do
  let all := (← cdt.get) ++ ths'
  tryWith (do
      let ptm ← liftExcept (partfn tm)
      HolMath.IndTypes.tryfindM' (fun th => PART_MATCH partfn th ptm) all)
    (do
      let ith ← HolMath.IndTypes.tryfindM' (fun th => do
        PART_MATCH (fun t => partfn (repeat' (fun u => do pure (← HolCore.Basics.dest_imp u).2) t)) th
          (← liftExcept (partfn tm))) all
      complexDiffElimGo cdt ths' partfn is_deriv ith)

/-- The `and COMPLEX_DIFF_ELIM th` of canal.ml 2448-2453. -/
partial def complexDiffElimGo [HolBase] (cdt : IO.Ref (List thm)) (ths' : List thm)
    (partfn : term → Except String term) (is_deriv : term → ExceptT String IO Bool)
    (th : thm) : ExceptT String IO thm := do
  let tm := concl th
  if !HolCore.Basics.is_imp tm then return th
  let t ← liftExcept (lhand tm)
  if !(← is_deriv t) then UNDISCH th
  else
    let th1 ← complexDiffConvGo cdt ths' partfn is_deriv t
    complexDiffElimGo cdt ths' partfn is_deriv (← MATCH_MP th th1)
end

structure KNK where
  complex_differentiation_theorems : IO.Ref (List thm)
  add_complex_differentiation_theorems : List thm → ExceptT String IO Unit
  GEN_COMPLEX_DIFF_CONV : List thm → ExceptT String IO (term → ExceptT String IO thm)
  COMPLEX_DIFF_CONV : term → ExceptT String IO thm
  GEN_COMPLEX_DIFF_TAC : List thm → ExceptT String IO tactic
  COMPLEX_DIFF_TAC : tactic
  COMPLEX_DIFFERENTIABLE_TAC : tactic
  deriving Nonempty

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupKNK [HolBase] (D : CanalDeps) (BKNE : KNE) (BKNF : KNF) : ExceptT String IO KNK := do
  -- @@SCOPE BEGIN
  let { complex_differentiable, HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV, .. } := BKNE
  let { HAS_COMPLEX_DERIVATIVE_ADD, HAS_COMPLEX_DERIVATIVE_CDIV_AT,
        HAS_COMPLEX_DERIVATIVE_CDIV_WITHIN, HAS_COMPLEX_DERIVATIVE_CONST,
        HAS_COMPLEX_DERIVATIVE_DIV_AT, HAS_COMPLEX_DERIVATIVE_DIV_WITHIN,
        HAS_COMPLEX_DERIVATIVE_ID, HAS_COMPLEX_DERIVATIVE_INV_AT,
        HAS_COMPLEX_DERIVATIVE_INV_WITHIN, HAS_COMPLEX_DERIVATIVE_LMUL_AT,
        HAS_COMPLEX_DERIVATIVE_LMUL_WITHIN, HAS_COMPLEX_DERIVATIVE_MUL_AT,
        HAS_COMPLEX_DERIVATIVE_MUL_WITHIN, HAS_COMPLEX_DERIVATIVE_NEG,
        HAS_COMPLEX_DERIVATIVE_POW_AT, HAS_COMPLEX_DERIVATIVE_POW_WITHIN,
        HAS_COMPLEX_DERIVATIVE_RMUL_AT, HAS_COMPLEX_DERIVATIVE_RMUL_WITHIN,
        HAS_COMPLEX_DERIVATIVE_SUB, .. } := BKNF
  let { MESON, .. } := D.cx.cvx
  let { ETA_AX, FORALL_AND_THM, .. } := D.cx.cvx.core1
  let { IMP_CONJ, IMP_IMP, .. } := D.cx.cvx.core2
  -- @@SCOPE END

  let complex_differentiation_theorems ← IO.mkRef ([] : List thm)

  let add_complex_differentiation_theorems ← do
    let ETA_THM ← prove
     r"(f has_complex_derivative f') net <=>
       ((\x. f x) has_complex_derivative f') net"
     (REWRITE_TAC [ETA_AX])
    let ETA_TWEAK (th : thm) : ExceptT String IO thm := do
      PURE_REWRITE_RULE [IMP_CONJ]
        (← GEN_REWRITE_RULE (LAND_CONV o ONCE_DEPTH_CONV) [ETA_THM] (← SPEC_ALL th))
    pure (fun (l : List thm) => do
      let l' ← l.mapM ETA_TWEAK
      complex_differentiation_theorems.modify (fun c => c ++ l'))

  add_complex_differentiation_theorems
   [HAS_COMPLEX_DERIVATIVE_LMUL_WITHIN, HAS_COMPLEX_DERIVATIVE_LMUL_AT,
    HAS_COMPLEX_DERIVATIVE_RMUL_WITHIN, HAS_COMPLEX_DERIVATIVE_RMUL_AT,
    HAS_COMPLEX_DERIVATIVE_CDIV_WITHIN, HAS_COMPLEX_DERIVATIVE_CDIV_AT,
    HAS_COMPLEX_DERIVATIVE_ID,
    HAS_COMPLEX_DERIVATIVE_CONST,
    HAS_COMPLEX_DERIVATIVE_NEG,
    HAS_COMPLEX_DERIVATIVE_ADD,
    HAS_COMPLEX_DERIVATIVE_SUB,
    HAS_COMPLEX_DERIVATIVE_MUL_WITHIN, HAS_COMPLEX_DERIVATIVE_MUL_AT,
    HAS_COMPLEX_DERIVATIVE_DIV_WITHIN, HAS_COMPLEX_DERIVATIVE_DIV_AT,
    HAS_COMPLEX_DERIVATIVE_POW_WITHIN, HAS_COMPLEX_DERIVATIVE_POW_AT,
    HAS_COMPLEX_DERIVATIVE_INV_WITHIN, HAS_COMPLEX_DERIVATIVE_INV_AT]

  -- `partfn tm = let l,r = dest_comb tm in mk_pair(lhand l,r)`; pair.ml's
  -- `mk_pair` looks up `,` in the constant table, which is read once here.
  let pairc ← ExceptT.mk (mk_const "," [])
  let pat ← q r"(f has_complex_derivative f') net"
  let GEN_COMPLEX_DIFF_CONV (ths : List thm) : ExceptT String IO (term → ExceptT String IO thm) := do
    let partfn (tm : term) : Except String term := do
      let (l, r) ← dest_comb tm
      let fl ← lhand l
      mk_comb (← mk_comb (inst [(type_of fl, aty), (type_of r, bty)] pairc) fl) r
    let is_deriv (t : term) : ExceptT String IO Bool :=
      tryWith (do let _ ← term_match [] pat t; pure true) (pure false)
    let ths' := unions (← HolMath.IndTypes.mapfilterM (fun th => do
      pure (CONJUNCTS (← REWRITE_RULE [FORALL_AND_THM]
        (← MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV th)))) ths)
    pure (complexDiffConvGo complex_differentiation_theorems ths' partfn is_deriv)

  let COMPLEX_DIFF_CONV ← GEN_COMPLEX_DIFF_CONV []

  let GEN_COMPLEX_DIFF_TAC (ths : List thm) : ExceptT String IO tactic := do
    let pth ← MESON []
     (← q r"(f has_complex_derivative f') net
      ==> f' = g'
          ==> (f has_complex_derivative g') net")
    pure (W (fun (_asl, w) => tactic_of do
      let th ← MATCH_MP pth (← (← GEN_COMPLEX_DIFF_CONV ths) w)
      pure (MATCH_MP_TAC (← repeatRule (GEN_REWRITE_RULE I [IMP_IMP]) (← DISCH_ALL th)))))

  let COMPLEX_DIFF_TAC ← GEN_COMPLEX_DIFF_TAC []

  let COMPLEX_DIFFERENTIABLE_TAC : tactic :=
    let DISCH_FIRST (th : thm) : ExceptT String IO thm :=
      match hyp th with
      | h :: _ => DISCH h th
      | [] => throw "hd"
    GEN_REWRITE_TAC I [complex_differentiable] THEN
    W (fun (_asl, w) => tactic_of do
          let th ← COMPLEX_DIFF_CONV (← liftExcept (HolCore.Basics.dest_exists w)).2
          let f' ← liftExcept (do rand (← rator (concl th)))
          pure (EXISTS_TAC f' THEN
            (if (hyp th).isEmpty then MATCH_ACCEPT_TAC th else
             tactic_of do
               let th' ← repeatRule (fun x => do GEN_REWRITE_RULE I [IMP_IMP] (← DISCH_FIRST x))
                            (← DISCH_FIRST th)
               pure (MATCH_MP_TAC th'))))

  pure { complex_differentiation_theorems, add_complex_differentiation_theorems,
         GEN_COMPLEX_DIFF_CONV, COMPLEX_DIFF_CONV, GEN_COMPLEX_DIFF_TAC, COMPLEX_DIFF_TAC,
         COMPLEX_DIFFERENTIABLE_TAC }

/- ------------------------------------------------------------------------- -/
/- A kind of complex Taylor theorem.  (canal.ml 2489-2576)                  -/
/- ------------------------------------------------------------------------- -/

structure KNL where
  COMPLEX_TAYLOR : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupKNL [HolBase] (D : CanalDeps) (BKNE : KNE) (BKNF : KNF) (BKNJ : KNJ) (BKNK : KNK) : ExceptT String IO KNL := do
  -- @@SCOPE BEGIN
  let { HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET, .. } := BKNE
  let { HAS_COMPLEX_DERIVATIVE_MUL_WITHIN, HAS_COMPLEX_DERIVATIVE_VSUM, .. } := BKNF
  let { COMPLEX_DIFFERENTIABLE_BOUND, .. } := BKNJ
  let { COMPLEX_DIFF_CONV, .. } := BKNK
  let { complex_div, complex_pow, SIMPLE_COMPLEX_ARITH, .. } := D.cxa
  let { COMPLEX_ADD_ASSOC, COMPLEX_ADD_LINV, COMPLEX_ADD_RID, COMPLEX_MUL_ASSOC,
        COMPLEX_MUL_LID, COMPLEX_MUL_LNEG, COMPLEX_MUL_LZERO, COMPLEX_MUL_RNEG,
        COMPLEX_MUL_RZERO, COMPLEX_NEG_0, COMPLEX_SUB_REFL, .. } := D.cxb
  let { COMPLEX_MUL_RINV, COMPLEX_NORM_CX, COMPLEX_VEC_0, CX_INJ, CX_MUL, .. } := D.cxc
  let { COMPLEX_RING, .. } := D.cxd
  let { COMPLEX_INV_MUL, .. } := D.cxe
  let { COMPLEX_DIV_1, COMPLEX_NORM_DIV, COMPLEX_NORM_MUL, COMPLEX_NORM_POW, .. } := D.cxf
  let { SEGMENT_BOUND, .. } := D.qconvex
  let { FACT, FACT_LT, .. } := D.qsession
  let { CONVEX_SEGMENT, .. } := D.ms.qconvex
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, REAL_ARITH, REAL_ARITH_TAC,
        VECTOR_ARITH_TAC, .. } := D.cx.cvx
  let { EQ_ADD_RCANCEL, LE_0, REAL_POW_1, REAL_POW_ADD, VSUM_CLAUSES_LEFT, .. } := D.cx.cpx
  let { ADD1, ARITH, EQ_IMP, ETA_AX, FINITE_NUMSEG, .. } := D.cx.cvx.core1
  let { IN_NUMSEG, NUMSEG_OFFSET_IMAGE, REAL_ABS_NUM, .. } := D.cx.cvx.core3
  let { REAL_LE_DIV, REAL_LE_DIV2_EQ, REAL_LE_MUL2, .. } := D.cx.cvx.core4
  let { REAL_OF_NUM_LT, REAL_OF_NUM_MUL, REAL_OF_NUM_SUC, REAL_POS, REAL_POW_LE,
        REAL_POW_LE2, SUBSET, .. } := D.cx.cvx.core5
  let { o_DEF, real_div, .. } := D.cx.cvx.core6
  let { NORM_POS_LE, NORM_SUB, .. } := D.cx.cvx.vec3
  let { VSUM_0, VSUM_ADD_NUMSEG, VSUM_CLAUSES_NUMSEG, VSUM_EQ_0, VSUM_IMAGE,
        .. } := D.cx.cvx.vec4
  let { ENDS_IN_SEGMENT, .. } := D.cx.cvx.top3
  let { ADD_SUB, .. } := D.ms.ig.dv.dg.qsession
  let { CONVEX_CONTAINS_SEGMENT, .. } := D.ms.ig.dv.dg.pt.qcvx2
  -- @@SCOPE END

  let COMPLEX_TAYLOR ← (do
    let lemma ← prove
     r"!f:num->real^N.
            vsum (0..n) f = f 0 - f (n + 1) + vsum (0..n) (\i. f (i + 1))"
     (REWRITE_TAC [← GSYM (← ExceptT.mk (REWRITE_CONV [o_DEF]
        (← q r"(f:num->real^N) o (\i. i + 1)")))] THEN
      ASM_SIMP_TAC [← GSYM VSUM_IMAGE, EQ_ADD_RCANCEL, FINITE_NUMSEG] THEN
      REWRITE_TAC [← GSYM NUMSEG_OFFSET_IMAGE] THEN
      SIMP_TAC [VSUM_CLAUSES_LEFT, LE_0] THEN
      REWRITE_TAC [VSUM_CLAUSES_NUMSEG, ← GSYM ADD1] THEN
      REWRITE_TAC [ARITH, ← ARITH_RULE (← q r"1 <= SUC n")] THEN VECTOR_ARITH_TAC)
    prove
     r"!f n s B.
      convex s /\
      (!i x. x IN s /\ i <= n
             ==> ((f i) has_complex_derivative f (i + 1) x) (at x within s)) /\
      (!x. x IN s ==> norm(f (n + 1) x) <= B)
      ==> !w z. w IN s /\ z IN s
                ==> norm(f 0 z -
                         vsum (0..n) (\i. f i w * (z - w) pow i / Cx(&(FACT i))))
                    <= B * norm(z - w) pow (n + 1) / &(FACT n)"
     (REPEAT STRIP_TAC THEN MP_TAC (← SPECL
       [← q r"(\w. vsum (0..n) (\i. f i w * (z - w) pow i / Cx(&(FACT i))))",
        ← q r"\w. (f:num->complex->complex) (n + 1) w *
             (z - w) pow n / Cx(&(FACT n))", ← q r"segment[w:complex,z]",
        ← q r"B * norm(z - w:complex) pow n / &(FACT n)"]
       COMPLEX_DIFFERENTIABLE_BOUND) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [CONVEX_SEGMENT] THEN X_GEN_TAC (← q r"u:complex") THEN
        DISCH_TAC THEN SUBGOAL_THEN (← q r"(u:complex) IN s") ASSUME_TAC THENL
         [ASM_MESON_TAC [CONVEX_CONTAINS_SEGMENT, SUBSET], ALL_TAC] THEN
        CONJ_TAC THENL
         [ALL_TAC,
          REWRITE_TAC [COMPLEX_NORM_MUL, COMPLEX_NORM_DIV, COMPLEX_NORM_CX,
                       COMPLEX_NORM_POW, REAL_ABS_NUM] THEN
          MATCH_MP_TAC REAL_LE_MUL2 THEN
          ASM_SIMP_TAC [REAL_LE_DIV, NORM_POS_LE, REAL_POS, REAL_POW_LE] THEN
          ASM_SIMP_TAC [REAL_LE_DIV2_EQ, REAL_OF_NUM_LT, FACT_LT] THEN
          MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC [NORM_POS_LE] THEN
          ASM_MESON_TAC [SEGMENT_BOUND, NORM_SUB]] THEN
        MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET THEN
        EXISTS_TAC (← q r"s:complex->bool") THEN CONJ_TAC THENL
         [ALL_TAC, ASM_MESON_TAC [CONVEX_CONTAINS_SEGMENT]] THEN
        SUBGOAL_THEN
         (← q r"((\u. vsum (0..n) (\i. f i u * (z - u) pow i / Cx (&(FACT i))))
           has_complex_derivative
           vsum (0..n) (\i. f i u * (-- Cx(&i) * (z - u) pow (i - 1)) /
                                    Cx(&(FACT i)) +
                            f (i + 1) u * (z - u) pow i / Cx (&(FACT i))))
          (at u within s)")
        MP_TAC THENL
         [MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_VSUM THEN
          REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
          MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_MUL_WITHIN THEN
          ASM_SIMP_TAC [ETA_AX] THEN W (MP_TAC o COMPLEX_DIFF_CONV o snd) THEN
          MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          REWRITE_TAC [complex_div] THEN CONV_TAC COMPLEX_RING,
          ALL_TAC] THEN
        ASM_SIMP_TAC [] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
        AP_TERM_TAC THEN REWRITE_TAC [VSUM_ADD_NUMSEG] THEN
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [lemma] THEN
        REWRITE_TAC [← GSYM VSUM_ADD_NUMSEG, ← GSYM COMPLEX_ADD_ASSOC] THEN
        REWRITE_TAC [ADD_SUB] THEN REWRITE_TAC [← GSYM ADD1, FACT] THEN
        REWRITE_TAC [← GSYM REAL_OF_NUM_SUC, ← GSYM REAL_OF_NUM_MUL, CX_MUL] THEN
        REWRITE_TAC [complex_div, COMPLEX_INV_MUL, ← GSYM COMPLEX_MUL_ASSOC] THEN
        REWRITE_TAC [← ExceptT.mk (COMPLEX_RING
          (← q r"--a * b * inv a * c:complex = --(a * inv a) * b * c"))] THEN
        SIMP_TAC [COMPLEX_MUL_RINV, CX_INJ, ← REAL_ARITH (← q r"~(&n + &1 = &0)")] THEN
        REWRITE_TAC [COMPLEX_MUL_LNEG, COMPLEX_MUL_RNEG, COMPLEX_MUL_LID] THEN
        REWRITE_TAC [COMPLEX_ADD_LINV, ← GSYM COMPLEX_VEC_0, VSUM_0] THEN
        REWRITE_TAC [COMPLEX_VEC_0, COMPLEX_ADD_RID] THEN
        REWRITE_TAC [COMPLEX_MUL_LZERO, COMPLEX_MUL_RZERO, COMPLEX_NEG_0] THEN
        CONV_TAC COMPLEX_RING,
        ALL_TAC] THEN
      DISCH_THEN (MP_TAC o SPECL [← q r"z:complex", ← q r"w:complex"]) THEN ANTS_TAC THEN
      ASM_REWRITE_TAC [ENDS_IN_SEGMENT] THEN MATCH_MP_TAC EQ_IMP THEN
      BINOP_TAC THENL
       [ALL_TAC,
        REWRITE_TAC [REAL_POW_ADD, real_div, REAL_POW_1] THEN REAL_ARITH_TAC] THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC [VSUM_CLAUSES_LEFT, LE_0, complex_pow, FACT, COMPLEX_DIV_1] THEN
      REWRITE_TAC [← SIMPLE_COMPLEX_ARITH (← q r"x * Cx(&1) + y = x <=> y = Cx(&0)")] THEN
      REWRITE_TAC [← GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
      INDUCT_TAC THEN
      ASM_REWRITE_TAC [complex_pow, complex_div, COMPLEX_MUL_LZERO,
                       COMPLEX_MUL_RZERO, COMPLEX_SUB_REFL, COMPLEX_VEC_0] THEN
      REWRITE_TAC [IN_NUMSEG] THEN ARITH_TAC))

  pure { COMPLEX_TAYLOR }
/- ------------------------------------------------------------------------- -/
/- The simplest special case; something more like the traditional MVT for   -/
/- real components; further useful properties of complex conjugation; some   -/
/- limit theorems about real part of real series etc.; comparison with real  -/
/- limits of complex type.  (canal.ml 2577-2847)                            -/
/- ------------------------------------------------------------------------- -/

structure KNM where
  COMPLEX_MVT : thm
  COMPLEX_MVT_LINE : thm
  COMPLEX_TAYLOR_MVT : thm
  LIM_CNJ : thm
  SUMS_CNJ : thm
  CONTINUOUS_WITHIN_CNJ : thm
  CONTINUOUS_AT_CNJ : thm
  CONTINUOUS_ON_CNJ : thm
  REAL_LIM : thm
  REAL_LIM_SEQUENTIALLY : thm
  REAL_SERIES : thm
  LIM_NULL_COMPARISON_COMPLEX : thm
  LIM_NULL_COMPARISON_COMPLEX_RE : thm
  SERIES_COMPARISON_COMPLEX : thm
  SERIES_COMPARISON_UNIFORM_COMPLEX : thm
  SUMMABLE_SUBSET_COMPLEX : thm
  SERIES_ABSCONV_IMP_CONV : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupKNM [HolBase] (D : CanalDeps) (BKNE : KNE) (BKNF : KNF) (BKNK : KNK) (BKNL : KNL) : ExceptT String IO KNM := do
  -- @@SCOPE BEGIN
  let { has_complex_derivative, .. } := BKNE
  let { HAS_COMPLEX_DERIVATIVE_MUL_AT, HAS_COMPLEX_DERIVATIVE_VSUM, .. } := BKNF
  let { COMPLEX_DIFF_CONV, .. } := BKNK
  let { COMPLEX_TAYLOR, .. } := BKNL
  let { complex_div, complex_pow, IM_DEF, RE_DEF, .. } := D.cxa
  let { COMPLEX_ADD_ASSOC, COMPLEX_ADD_LINV, COMPLEX_ADD_RID, COMPLEX_MUL_ASSOC,
        COMPLEX_MUL_LID, COMPLEX_MUL_LNEG, COMPLEX_MUL_LZERO, COMPLEX_MUL_RID,
        COMPLEX_MUL_RNEG, COMPLEX_MUL_RZERO, COMPLEX_NEG_0, COMPLEX_SUB_REFL, .. } := D.cxb
  let { COMPLEX_MUL_RINV, COMPLEX_NORM_CX, COMPLEX_VEC_0, CX_INJ, CX_MUL, RE_ADD, RE_CMUL,
        RE_CX, .. } := D.cxc
  let { COMPLEX_RING, .. } := D.cxd
  let { COMPLEX_INV_MUL, .. } := D.cxe
  let { COMPLEX_DIV_1, .. } := D.cxf
  let { CNJ_SUB, COMPLEX_NORM_CNJ, COMPLEX_NORM_GE_RE_IM, .. } := D.cxg
  let { LINEAR_CNJ, .. } := D.cxh
  let { CNJ_VSUM, RE_VSUM, real, REAL_CX, REAL_VSUM, .. } := D.cxi
  let { REAL_NORM_POS, .. } := D.cxj
  let { LIM_COMPONENT_EQ, SERIES_COMPARISON, SERIES_COMPARISON_UNIFORM, SERIES_COMPONENT,
        summable, SUMMABLE_SUBSET, .. } := D.qtopology
  let { DIFF_CHAIN_AT, MVT_VERY_SIMPLE, .. } := D.qderivatives
  let { FACT, REAL_EQ_SUB_RADD, SUM_EQ_0_NUMSEG, .. } := D.qsession
  let { CONVEX_SEGMENT, .. } := D.ms.qconvex
  let { HAS_DERIVATIVE_AT_WITHIN, HAS_DERIVATIVE_LINEAR, .. } := D.ms.qderivatives
  let { REAL_ABS_LE, .. } := D.ms.qsession
  let { SUMS_EQ, .. } := D.ms.qtopology2
  let { ARITH_RULE, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, REAL_ARITH, REAL_RAT_REDUCE_CONV,
        VECTOR_ARITH, VECTOR_ARITH_TAC, .. } := D.cx.cvx
  let { EQ_ADD_RCANCEL, LE_0, REAL_POW_1, VSUM_CLAUSES_LEFT, .. } := D.cx.cpx
  let { HAS_DERIVATIVE_ADD, HAS_DERIVATIVE_CONST, .. } := D.ms.ig.qderivatives
  let { ADD1, ARITH, DIMINDEX_2, EQ_IMP, ETA_AX, FINITE_INTER, FINITE_NUMSEG,
        .. } := D.cx.cvx.core1
  let { GE, IMP_CONJ_ALT, .. } := D.cx.cvx.core2
  let { IN_ELIM_THM, IN_NUMSEG, LE, MONO_AND, MONO_EXISTS, NUMSEG_OFFSET_IMAGE,
        NUMSEG_SING, REAL_ADD_SYM, REAL_DIV_1, .. } := D.cx.cvx.core3
  let { REAL_LE_REFL, REAL_LE_TRANS, .. } := D.cx.cvx.core4
  let { REAL_OF_NUM_MUL, REAL_OF_NUM_SUC, REAL_POS, .. } := D.cx.cvx.core5
  let { o_DEF, o_THM, .. } := D.cx.cvx.core6
  let { DROP_ADD, DROP_CMUL, DROP_VEC, LIFT_ADD, LIFT_CMUL, LIFT_EQ, LIFT_SUB, NORM_0,
        .. } := D.cx.cvx.vec2
  let { NORM_POS_LE, REAL_ABS_NORM, .. } := D.cx.cvx.vec3
  let { dist, linear, VECTOR_ADD_LID, VECTOR_ADD_RID, VECTOR_MUL_LID, VECTOR_MUL_LZERO,
        VECTOR_SUB_RZERO, VSUM_0, VSUM_ADD_NUMSEG, VSUM_CLAUSES_NUMSEG, VSUM_IMAGE,
        VSUM_SING, .. } := D.cx.cvx.vec4
  let { EVENTUALLY_MONO, EVENTUALLY_SEQUENTIALLY, TRIVIAL_LIMIT_SEQUENTIALLY,
        .. } := D.cx.cvx.met
  let { IN_INTERVAL_1, LIM_NULL_COMPARISON, LINEAR_CONTINUOUS_AT, LINEAR_CONTINUOUS_ON,
        .. } := D.cx.cvx.top4
  let { segment, .. } := D.cx.cvx.top5
  let { SEQUENTIALLY, .. } := D.ms.ig.dv.qmetric
  let { FINITE_INTER_NUMSEG, .. } := D.ms.ig.dv.qmisc
  let { LIM_NULL_NORM, LINEAR_CONTINUOUS_WITHIN, sums, .. } := D.ms.ig.dv.qtopology2
  let { ADD_SUB, .. } := D.ms.ig.dv.dg.qsession
  let { tendsto, .. } := D.ms.ig.dv.dg.qtopology2
  -- @@SCOPE END

  let COMPLEX_MVT ← prove
   r"!f f' s B.
        convex s /\
        (!z. z IN s ==> (f has_complex_derivative f' z) (at z within s)) /\
        (!z. z IN s ==> norm (f' z) <= B)
        ==> !w z. w IN s /\ z IN s ==> norm (f z - f w) <= B * norm (z - w)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"(\n. if n = 0 then f else f'):num->complex->complex",
                     ← q r"0", ← q r"s:complex->bool", ← q r"B:real"] COMPLEX_TAYLOR) THEN
    SIMP_TAC [NUMSEG_SING, VSUM_SING, LE, ARITH] THEN
    REWRITE_TAC [complex_pow, REAL_POW_1, FACT, REAL_DIV_1] THEN
    ASM_SIMP_TAC [COMPLEX_DIV_1, COMPLEX_MUL_RID])

  let COMPLEX_MVT_LINE ← prove
   r"!f f' w z.
        (!u. u IN segment[w,z]
             ==> (f has_complex_derivative f'(u)) (at u))
        ==> ?u. u IN segment[w,z] /\ Re(f z) - Re(f w) = Re(f'(u) * (z - w))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL
     [← q r"(lift o Re) o (f:complex->complex) o
       (\t. (&1 - drop t) % w + drop t % z)",
      ← q r"\u. (lift o Re) o
           (\h. (f':complex->complex)((&1 - drop u) % w + drop u % z) * h) o
           (\t. drop t % (z - w))",
      ← q r"vec 0:real^1", ← q r"vec 1:real^1"]
          MVT_VERY_SIMPLE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [DROP_VEC, REAL_POS] THEN
      X_GEN_TAC (← q r"t:real^1") THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
        REWRITE_TAC [linear, LIFT_ADD, RE_ADD, LIFT_CMUL, RE_CMUL, o_DEF]] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
       [REWRITE_TAC [← VECTOR_ARITH (← q r"(&1 - t) % w + t % z = w + t % (z - w)")] THEN
        GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ABS_CONV)
          [← GSYM VECTOR_ADD_LID] THEN
        MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
        REWRITE_TAC [HAS_DERIVATIVE_CONST] THEN
        MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
        REWRITE_TAC [linear, DROP_ADD, DROP_CMUL] THEN
        CONJ_TAC THEN VECTOR_ARITH_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [← GSYM has_complex_derivative] THEN
      FIRST_X_ASSUM MATCH_MP_TAC,
      REWRITE_TAC [o_THM, ← GSYM LIFT_SUB, LIFT_EQ, DROP_VEC, VECTOR_SUB_RZERO] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [VECTOR_MUL_LID, VECTOR_MUL_LZERO] THEN
      REWRITE_TAC [VECTOR_ADD_LID, VECTOR_ADD_RID] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"t:real^1") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"(&1 - drop t) % w + drop t % z:complex")] THEN
    ASM_REWRITE_TAC [segment, IN_ELIM_THM] THEN
    EXISTS_TAC (← q r"drop t") THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
    REWRITE_TAC [DROP_VEC])

  let COMPLEX_TAYLOR_MVT ← (do
    let lemma ← prove
     r"!f:num->real^N.
            vsum (0..n) f = f 0 - f (n + 1) + vsum (0..n) (\i. f (i + 1))"
     (REWRITE_TAC [← GSYM (← ExceptT.mk (REWRITE_CONV [o_DEF]
        (← q r"(f:num->real^N) o (\i. i + 1)")))] THEN
      ASM_SIMP_TAC [← GSYM VSUM_IMAGE, EQ_ADD_RCANCEL, FINITE_NUMSEG] THEN
      REWRITE_TAC [← GSYM NUMSEG_OFFSET_IMAGE] THEN
      SIMP_TAC [VSUM_CLAUSES_LEFT, LE_0] THEN
      REWRITE_TAC [VSUM_CLAUSES_NUMSEG, ← GSYM ADD1] THEN
      REWRITE_TAC [ARITH, ← ARITH_RULE (← q r"1 <= SUC n")] THEN VECTOR_ARITH_TAC)
    prove
     r"!f w z n.
      (!i x. x IN segment[w,z] /\ i <= n
             ==> ((f i) has_complex_derivative f (i + 1) x) (at x))
      ==> ?u. u IN segment[w,z] /\
              Re(f 0 z) =
              Re(vsum (0..n) (\i. f i w * (z - w) pow i / Cx(&(FACT i))) +
                 (f (n + 1) u * (z - u) pow n / Cx (&(FACT n))) * (z - w))"
     (REPEAT STRIP_TAC THEN MP_TAC (← SPECL
       [← q r"(\w. vsum (0..n) (\i. f i w * (z - w) pow i / Cx(&(FACT i))))",
        ← q r"\w. (f:num->complex->complex) (n + 1) w *
             (z - w) pow n / Cx(&(FACT n))",
        ← q r"w:complex", ← q r"z:complex"]
        COMPLEX_MVT_LINE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [CONVEX_SEGMENT] THEN X_GEN_TAC (← q r"u:complex") THEN
        DISCH_TAC THEN
        SUBGOAL_THEN
         (← q r"((\u. vsum (0..n) (\i. f i u * (z - u) pow i / Cx (&(FACT i))))
           has_complex_derivative
           vsum (0..n) (\i. f i u * (-- Cx(&i) * (z - u) pow (i - 1)) /
                                    Cx(&(FACT i)) +
                            f (i + 1) u * (z - u) pow i / Cx (&(FACT i))))
          (at u)")
        MP_TAC THENL
         [MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_VSUM THEN
          REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
          MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_MUL_AT THEN
          ASM_SIMP_TAC [ETA_AX] THEN W (MP_TAC o COMPLEX_DIFF_CONV o snd) THEN
          MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          REWRITE_TAC [complex_div] THEN CONV_TAC COMPLEX_RING,
          ALL_TAC] THEN
        ASM_SIMP_TAC [] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
        AP_TERM_TAC THEN REWRITE_TAC [VSUM_ADD_NUMSEG] THEN
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [lemma] THEN
        REWRITE_TAC [← GSYM VSUM_ADD_NUMSEG, ← GSYM COMPLEX_ADD_ASSOC] THEN
        REWRITE_TAC [ADD_SUB] THEN REWRITE_TAC [← GSYM ADD1, FACT] THEN
        REWRITE_TAC [← GSYM REAL_OF_NUM_SUC, ← GSYM REAL_OF_NUM_MUL, CX_MUL] THEN
        REWRITE_TAC [complex_div, COMPLEX_INV_MUL, ← GSYM COMPLEX_MUL_ASSOC] THEN
        REWRITE_TAC [← ExceptT.mk (COMPLEX_RING
          (← q r"--a * b * inv a * c:complex = --(a * inv a) * b * c"))] THEN
        SIMP_TAC [COMPLEX_MUL_RINV, CX_INJ, ← REAL_ARITH (← q r"~(&n + &1 = &0)")] THEN
        REWRITE_TAC [COMPLEX_MUL_LNEG, COMPLEX_MUL_RNEG, COMPLEX_MUL_LID] THEN
        REWRITE_TAC [COMPLEX_ADD_LINV, ← GSYM COMPLEX_VEC_0, VSUM_0] THEN
        REWRITE_TAC [COMPLEX_VEC_0, COMPLEX_ADD_RID] THEN
        REWRITE_TAC [COMPLEX_MUL_LZERO, COMPLEX_MUL_RZERO, COMPLEX_NEG_0] THEN
        CONV_TAC COMPLEX_RING,
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"u:complex") THEN
      MATCH_MP_TAC MONO_AND THEN REWRITE_TAC [RE_ADD] THEN
      REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_ADD_SYM] REAL_EQ_SUB_RADD] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      SIMP_TAC [VSUM_CLAUSES_LEFT, LE_0, complex_pow, FACT, COMPLEX_DIV_1] THEN
      REWRITE_TAC [COMPLEX_MUL_RID, RE_ADD] THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"Re x = &0 ==> y = y + Re x")) THEN
      SIMP_TAC [RE_VSUM, FINITE_NUMSEG] THEN
      MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
      INDUCT_TAC THEN REWRITE_TAC [ARITH] THEN
      REWRITE_TAC [COMPLEX_SUB_REFL, complex_pow, complex_div] THEN
      REWRITE_TAC [COMPLEX_MUL_LZERO, COMPLEX_MUL_RZERO, RE_CX]))

  let LIM_CNJ ← prove
   r"!net f l. ((\x. cnj(f x)) --> cnj l) net <=> (f --> l) net"
   (REWRITE_TAC [tendsto, dist, ← GSYM CNJ_SUB, COMPLEX_NORM_CNJ])

  let SUMS_CNJ ← prove
   r"!net f l. ((\x. cnj(f x)) sums cnj l) net <=> (f sums l) net"
   (SIMP_TAC [sums, LIM_CNJ, ← GSYM CNJ_VSUM, FINITE_INTER_NUMSEG])

  let CONTINUOUS_WITHIN_CNJ ← prove
   r"!s z. cnj continuous (at z within s)"
   (SIMP_TAC [LINEAR_CONTINUOUS_WITHIN, LINEAR_CNJ])

  let CONTINUOUS_AT_CNJ ← prove
   r"!z. cnj continuous (at z)"
   (SIMP_TAC [LINEAR_CONTINUOUS_AT, LINEAR_CNJ])

  let CONTINUOUS_ON_CNJ ← prove
   r"!s. cnj continuous_on s"
   (SIMP_TAC [LINEAR_CONTINUOUS_ON, LINEAR_CNJ])

  let REAL_LIM ← prove
   r"!net:(A)net f l.
        (f --> l) net /\ ~(trivial_limit net) /\
        eventually (\a. real(f a)) net
        ==> real l"
   (REWRITE_TAC [IM_DEF, real] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC LIM_COMPONENT_EQ THEN
    REWRITE_TAC [DIMINDEX_2, ARITH] THEN ASM_MESON_TAC [])

  let REAL_LIM_SEQUENTIALLY ← prove
   r"!f l. (f --> l) sequentially /\ (?N. !n. n >= N ==> real(f n))
         ==> real l"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← ISPEC (← q r"sequentially") REAL_LIM) THEN
    REWRITE_TAC [SEQUENTIALLY, EVENTUALLY_SEQUENTIALLY,
                 TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    ASM_MESON_TAC [GE])

  let REAL_SERIES ← prove
   r"!f l s. (f sums l) s /\ (!n. real(f n)) ==> real l"
   (REWRITE_TAC [sums] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LIM_SEQUENTIALLY THEN
    EXISTS_TAC (← q r"\n. vsum(s INTER (0..n)) f :complex") THEN
    ASM_SIMP_TAC [REAL_VSUM, FINITE_INTER, FINITE_NUMSEG])

  let LIM_NULL_COMPARISON_COMPLEX ← prove
   r"!net:(A)net f g.
        eventually (\x. norm(f x) <= norm(g x)) net /\
        (g --> Cx(&0)) net
        ==> (f --> Cx(&0)) net"
   (REWRITE_TAC [← GSYM COMPLEX_VEC_0] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← ISPEC (← q r"net:(A)net") LIM_NULL_COMPARISON) THEN
    EXISTS_TAC (← q r"norm o (g:A->complex)") THEN
    ASM_REWRITE_TAC [o_THM, ← GSYM LIM_NULL_NORM])

  let LIM_NULL_COMPARISON_COMPLEX_RE ← prove
   r"!net:(A)net f g.
        eventually (\x. norm(f x) <= Re(g x)) net /\
        (g --> Cx(&0)) net
        ==> (f --> Cx(&0)) net"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← ISPEC (← q r"net:(A)net") LIM_NULL_COMPARISON_COMPLEX) THEN
    EXISTS_TAC (← q r"g:A->complex") THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP
     (← REWRITE_RULE [IMP_CONJ_ALT] EVENTUALLY_MONO)) THEN
    REWRITE_TAC [] THEN
    MESON_TAC [COMPLEX_NORM_GE_RE_IM, REAL_ABS_LE, REAL_LE_TRANS])

  let SERIES_COMPARISON_COMPLEX ← prove
   r"!f:num->real^N g s.
        summable s g /\
        (!n. n IN s ==> real(g n) /\ &0 <= Re(g n)) /\
        (?N. !n. n >= N /\ n IN s ==> norm(f n) <= norm(g n))
        ==> summable s f"
   (REPEAT GEN_TAC THEN REWRITE_TAC [summable] THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    MATCH_MP_TAC SERIES_COMPARISON THEN
    EXISTS_TAC (← q r"\n. norm((g:num->complex) n)") THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"l:complex") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"lift(Re l)") THEN MATCH_MP_TAC SUMS_EQ THEN
    EXISTS_TAC (← q r"\i:num. lift(Re(g i))") THEN
    ASM_SIMP_TAC [REAL_NORM_POS, o_DEF] THEN
    REWRITE_TAC [RE_DEF] THEN MATCH_MP_TAC SERIES_COMPONENT THEN
    ASM_REWRITE_TAC [DIMINDEX_2, ARITH])

  let SERIES_COMPARISON_UNIFORM_COMPLEX ← prove
   r"!f:A->num->real^N g P s.
        summable s g /\
        (!n. n IN s ==> real(g n) /\ &0 <= Re(g n)) /\
        (?N. !n x. N <= n /\ n IN s /\ P x ==> norm(f x n) <= norm(g n))
        ==> ?l. !e. &0 < e
                    ==> ?N. !n x. N <= n /\ P x
                                  ==> dist(vsum(s INTER (0..n)) (f x),l x) <
                                       e"
   (REPEAT GEN_TAC THEN REWRITE_TAC [summable] THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    MATCH_MP_TAC SERIES_COMPARISON_UNIFORM THEN
    EXISTS_TAC (← q r"\n. norm((g:num->complex) n)") THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"l:complex") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"lift(Re l)") THEN MATCH_MP_TAC SUMS_EQ THEN
    EXISTS_TAC (← q r"\i:num. lift(Re(g i))") THEN
    ASM_SIMP_TAC [REAL_NORM_POS, o_DEF] THEN
    REWRITE_TAC [RE_DEF] THEN MATCH_MP_TAC SERIES_COMPONENT THEN
    ASM_REWRITE_TAC [DIMINDEX_2, ARITH])

  let SUMMABLE_SUBSET_COMPLEX ← prove
   r"!x s t. (!n. n IN s ==> real(x n) /\ &0 <= Re(x n)) /\
           summable s x /\ t SUBSET s
           ==> summable t x"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUMMABLE_SUBSET THEN
    EXISTS_TAC (← q r"s:num->bool") THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC SERIES_COMPARISON_COMPLEX THEN
    EXISTS_TAC (← q r"x:num->complex") THEN ASM_REWRITE_TAC [] THEN
    MESON_TAC [REAL_LE_REFL, NORM_0, NORM_POS_LE])

  let SERIES_ABSCONV_IMP_CONV ← prove
   r"!x:num->real^N k. summable k (\n. Cx(norm(x n))) ==> summable k x"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_COMPARISON_COMPLEX THEN
    EXISTS_TAC (← q r"\n:num. Cx(norm(x n:real^N))") THEN
    ASM_REWRITE_TAC [REAL_CX, RE_CX, NORM_POS_LE, COMPLEX_NORM_CX] THEN
    REWRITE_TAC [REAL_ABS_NORM, REAL_LE_REFL])

  pure { COMPLEX_MVT, COMPLEX_MVT_LINE, COMPLEX_TAYLOR_MVT, LIM_CNJ, SUMS_CNJ,
         CONTINUOUS_WITHIN_CNJ, CONTINUOUS_AT_CNJ, CONTINUOUS_ON_CNJ, REAL_LIM,
         REAL_LIM_SEQUENTIALLY, REAL_SERIES, LIM_NULL_COMPARISON_COMPLEX,
         LIM_NULL_COMPARISON_COMPLEX_RE, SERIES_COMPARISON_COMPLEX,
         SERIES_COMPARISON_UNIFORM_COMPLEX, SUMMABLE_SUBSET_COMPLEX,
         SERIES_ABSCONV_IMP_CONV }
/- ------------------------------------------------------------------------- -/
/- Complex-valued geometric series; complex version (the usual one) of the   -/
/- Dirichlet convergence test; versions with explicit bounds.               -/
/- (canal.ml 2848-3002)                                                     -/
/- ------------------------------------------------------------------------- -/

structure KNN where
  SUMS_GP : thm
  SUMMABLE_GP : thm
  SERIES_DIRICHLET_COMPLEX_GEN : thm
  SERIES_DIRICHLET_COMPLEX : thm
  SERIES_DIRICHLET_COMPLEX_VERY_EXPLICIT : thm
  SERIES_DIRICHLET_COMPLEX_EXPLICIT : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupKNN [HolBase] (D : CanalDeps) (BKNB : KNB) : ExceptT String IO KNN := do
  -- @@SCOPE BEGIN
  let { LIM_COMPLEX_DIV, .. } := BKNB
  let { complex_pow, .. } := D.cxa
  let { COMPLEX_MUL_SYM, COMPLEX_SUB_0, COMPLEX_SUB_RZERO, .. } := D.cxb
  let { COMPLEX_CMUL, COMPLEX_NORM_CX, COMPLEX_VEC_0, RE_SUB, .. } := D.cxc
  let { COMPLEX_NORM_MUL, COMPLEX_NORM_NUM, COMPLEX_NORM_POW, .. } := D.cxf
  let { COMPLEX_NORM_GE_RE_IM, .. } := D.cxg
  let { BILINEAR_COMPLEX_MUL, .. } := D.cxh
  let { REAL, REAL_SUB, VSUM_CX, .. } := D.cxi
  let { REAL_NORM, VSUM_GP, .. } := D.cxj
  let { BOUNDED_PARTIAL_SUMS, SERIES_CAUCHY, SERIES_DIRICHLET, SERIES_DIRICHLET_BILINEAR,
        SERIES_FROM, summable, SUMMABLE_RATIO, .. } := D.qtopology
  let { BILINEAR_VSUM_PARTIAL_PRE, .. } := D.qvectors
  let { SUM_DIFFS, .. } := D.qsession
  let { SUM_EQ_NUMSEG, .. } := D.ms.qsession
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC, NORM_ARITH, REAL_ARITH,
        REAL_ARITH_TAC, VECTOR_ARITH_TAC, .. } := D.cx.cvx
  let { NUMSEG_RREC, VSUM_EQ_NUMSEG, .. } := D.cx.cpx
  let { VSUM_NORM_LE, .. } := D.ms.ig.qvec
  let { ARITH, EQ_IMP, FINITE_INTER, FINITE_NUMSEG, FORALL_AND_THM, .. } := D.cx.cvx.core1
  let { FUN_EQ_THM, .. } := D.cx.cvx.core2
  let { IN_ELIM_THM, IN_NUMSEG, IN_UNIV, LE_REFL, LEFT_IMP_EXISTS_THM, MONO_EXISTS, NOT_LE,
        REAL_ARCH_POW_INV, .. } := D.cx.cvx.core3
  let { REAL_EQ_IMP_LE, REAL_LE_LMUL, REAL_LE_MUL, REAL_LE_MUL2, REAL_LE_REFL,
        REAL_LE_RMUL_EQ, REAL_LE_TRANS, REAL_LET_TRANS, REAL_LT_IMP_LE, REAL_LT_MUL,
        REAL_LT_REFL, .. } := D.cx.cvx.core4
  let { REAL_MUL_ASSOC, REAL_OF_NUM_LT, REAL_POS, .. } := D.cx.cvx.core5
  let { o_DEF, o_THM, real_abs, SUM_RMUL, .. } := D.cx.cvx.core6
  let { NORM_0, .. } := D.cx.cvx.vec2
  let { NORM_LIFT, NORM_POS_LE, .. } := D.cx.cvx.vec3
  let { dist, VECTOR_SUB_RZERO, VSUM_CLAUSES, .. } := D.cx.cvx.vec4
  let { EVENTUALLY_SEQUENTIALLY, .. } := D.cx.cvx.met
  let { BOUNDED_POS, .. } := D.cx.cvx.top1
  let { LIM_CONST, LIM_SEQUENTIALLY, LIM_SUB, .. } := D.cx.cvx.top4
  let { REAL_POW_MONO_INV, .. } := D.ms.ig.dv.qsession
  let { LIM_TRANSFORM_EVENTUALLY, .. } := D.ms.ig.dv.qtopology2
  let { LIFT_SUM, .. } := D.ms.ig.dv.dg.qvec
  -- @@SCOPE END

  let SUMS_GP ← prove
   r"!n z. norm(z) < &1
         ==> ((\k. z pow k) sums (z pow n / (Cx(&1) - z))) (from n)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [SERIES_FROM, VSUM_GP] THEN
    ASM_CASES_TAC (← q r"z = Cx(&1)") THENL
     [ASM_MESON_TAC [COMPLEX_NORM_NUM, REAL_LT_REFL], ALL_TAC] THEN
    MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC (← q r"\m. (z pow n - z pow SUC m) / (Cx (&1) - z)") THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC [EVENTUALLY_SEQUENTIALLY] THEN
      EXISTS_TAC (← q r"n:num") THEN SIMP_TAC [← GSYM NOT_LE],
      MATCH_MP_TAC LIM_COMPLEX_DIV THEN
      ASM_REWRITE_TAC [COMPLEX_SUB_0, LIM_CONST] THEN
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [← GSYM COMPLEX_SUB_RZERO] THEN
      MATCH_MP_TAC LIM_SUB THEN REWRITE_TAC [LIM_CONST] THEN
      REWRITE_TAC [LIM_SEQUENTIALLY, ← GSYM COMPLEX_VEC_0] THEN
      REWRITE_TAC [← NORM_ARITH (← q r"dist(x,vec 0) = norm x")] THEN
      X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
      MP_TAC (← SPECL [← q r"norm(z:complex)", ← q r"e:real"] REAL_ARCH_POW_INV) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN X_GEN_TAC (← q r"m:num") THEN
      DISCH_TAC THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REAL_ARITH
       (← q r"x < e ==> y <= x ==> y < e"))) THEN
      REWRITE_TAC [COMPLEX_NORM_POW] THEN MATCH_MP_TAC REAL_POW_MONO_INV THEN
      ASM_SIMP_TAC [NORM_POS_LE, REAL_LT_IMP_LE] THEN
      UNDISCH_TAC (← q r"n:num <= m") THEN ARITH_TAC])

  let SUMMABLE_GP ← prove
   r"!z k. norm(z) < &1 ==> summable k (\n. z pow n)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUMMABLE_RATIO THEN
    MAP_EVERY EXISTS_TAC [← q r"norm(z:complex)", ← q r"0"] THEN
    ASM_REWRITE_TAC [complex_pow, COMPLEX_NORM_MUL, REAL_LE_REFL])

  let SERIES_DIRICHLET_COMPLEX_GEN ← prove
   r"!f g k m p l.
        bounded {vsum (m..n) f | n IN (:num)} /\
        summable (from p) (\n. Cx(norm(g(n + 1) - g(n)))) /\
        ((\n. vsum(1..n) f * g(n + 1)) --> l) sequentially
        ==> summable (from k) (\n. f(n) * g(n))"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN
    MATCH_MP_TAC SERIES_DIRICHLET_BILINEAR THEN
    MAP_EVERY EXISTS_TAC [← q r"m:num", ← q r"p:num", ← q r"l:complex"] THEN
    ASM_REWRITE_TAC [BILINEAR_COMPLEX_MUL] THEN
    ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [summable]) THEN
    REWRITE_TAC [summable, SERIES_CAUCHY] THEN
    SIMP_TAC [← GSYM (← REWRITE_RULE [o_DEF] LIFT_SUM), FINITE_NUMSEG, FINITE_INTER,
              VSUM_CX, NORM_LIFT, COMPLEX_NORM_CX])

  let SERIES_DIRICHLET_COMPLEX ← prove
   r"!f g N k m.
        bounded {vsum (m..n) f | n IN (:num)} /\
        (!n. real(g n)) /\
        (!n. N <= n ==> Re(g(n + 1)) <= Re(g n)) /\
        (g --> Cx(&0)) sequentially
        ==> summable (from k) (\n. f(n) * g(n))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:num->complex", ← q r"\n:num. Re(g n)", ← q r"N:num",
                      ← q r"k:num", ← q r"m:num"] SERIES_DIRICHLET) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
      REWRITE_TAC [LIM_SEQUENTIALLY, o_THM, dist, VECTOR_SUB_RZERO] THEN
      REWRITE_TAC [COMPLEX_SUB_RZERO, NORM_LIFT] THEN
      MESON_TAC [COMPLEX_NORM_GE_RE_IM, REAL_LET_TRANS],
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC [COMPLEX_CMUL, FUN_EQ_THM] THEN
      ASM_MESON_TAC [REAL, COMPLEX_MUL_SYM]])

  let SERIES_DIRICHLET_COMPLEX_VERY_EXPLICIT ← prove
   r"!f g B p.
        &0 < B /\ 1 <= p /\
        (!m n. p <= m ==> norm(vsum(m..n) f) <= B) /\
        (!n. p <= n ==> real(g n) /\ &0 <= Re(g n)) /\
        (!n. p <= n ==> Re(g(n + 1)) <= Re(g n))
        ==> !m n. p <= m
                  ==> norm(vsum(m..n) (\k. f k * g k)) <= &2 * B * norm(g m)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     (← q r"norm(vsum(m..n) (\k. (vsum(p..k) f - vsum(p..(k-1)) f) * g k))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
      MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC (← q r"k:num") THEN STRIP_TAC THEN
      REWRITE_TAC [] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN (← q r"p:num <= k")
       (fun th => tactic_of do pure (SIMP_TAC [← GSYM (← MATCH_MP NUMSEG_RREC th)]))
      THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      SIMP_TAC [VSUM_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
      COND_CASES_TAC THENL [ASM_ARITH_TAC, VECTOR_ARITH_TAC],
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN
    REWRITE_TAC [← MATCH_MP BILINEAR_VSUM_PARTIAL_PRE BILINEAR_COMPLEX_MUL] THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC [NORM_0, REAL_LE_MUL, REAL_POS, REAL_LT_IMP_LE, NORM_POS_LE] THEN
    MATCH_MP_TAC (← NORM_ARITH
     (← q r"norm(c) <= e - norm(a) - norm(b) ==> norm(a - b - c) <= e")) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"sum (m..n) (\k. norm(g(k + 1) - g(k)) * B)") THEN CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC [IN_NUMSEG, FINITE_NUMSEG] THEN
      X_GEN_TAC (← q r"k:num") THEN STRIP_TAC THEN REWRITE_TAC [COMPLEX_NORM_MUL] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC [REAL_LE_REFL, LE_REFL, NORM_POS_LE],
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"sum(m..n) (\k. Re(g(k)) - Re(g(k + 1))) * B") THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [SUM_RMUL, REAL_LE_RMUL_EQ] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"p <= i /\ p <= i + 1") ASSUME_TAC THENL
       [ASM_ARITH_TAC, ALL_TAC] THEN
      ASM_SIMP_TAC [REAL_NORM, REAL_SUB, RE_SUB] THEN
      ASM_SIMP_TAC [← REAL_ARITH (← q r"abs(x - y) = y - x <=> x <= y")],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [SUM_DIFFS, COMPLEX_NORM_MUL] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"w * n1 <= w * B /\ z * n2 <= z * B /\ &0 <= B * (&2 * y - (x + w + z))
      ==> x * B <= &2 * B * y - w * n1 - z * n2")) THEN
    REPEAT (CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC [NORM_POS_LE, LE_REFL], ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN
     (← q r"p <= m /\ p <= m + 1 /\ p <= n /\ p <= n + 1")
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    ASM_SIMP_TAC [REAL_NORM, real_abs] THEN REAL_ARITH_TAC)

  let SERIES_DIRICHLET_COMPLEX_EXPLICIT ← prove
   r"!f g p q.
           1 <= p /\
           bounded {vsum (q..n) f | n IN (:num)} /\
           (!n. p <= n ==> real(g n) /\ &0 <= Re(g n)) /\
           (!n. p <= n ==> Re(g(n + 1)) <= Re(g n))
           ==> ?B. &0 < B /\
                   !m n. p <= m
                         ==> norm(vsum(m..n) (\k. f k * g k))
                                 <= B * norm(g m)"
   (REWRITE_TAC [FORALL_AND_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP BOUNDED_PARTIAL_SUMS) THEN
    SIMP_TAC [BOUNDED_POS, IN_ELIM_THM, IN_UNIV, LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [← MESON [] (← q r"(!x a b. x = f a b ==> p a b) <=> (!a b. p a b)")] THEN
    X_GEN_TAC (← q r"B:real") THEN STRIP_TAC THEN EXISTS_TAC (← q r"&2 * B") THEN
    ASM_SIMP_TAC [← GSYM REAL_MUL_ASSOC, REAL_LT_MUL, REAL_OF_NUM_LT, ARITH] THEN
    MATCH_MP_TAC SERIES_DIRICHLET_COMPLEX_VERY_EXPLICIT THEN
    ASM_SIMP_TAC [])

  pure { SUMS_GP, SUMMABLE_GP, SERIES_DIRICHLET_COMPLEX_GEN, SERIES_DIRICHLET_COMPLEX,
         SERIES_DIRICHLET_COMPLEX_VERY_EXPLICIT, SERIES_DIRICHLET_COMPLEX_EXPLICIT }
/- ------------------------------------------------------------------------- -/
/- Integrals and complex multiplication; relations among convergence and    -/
/- absolute convergence for power series.  (canal.ml 3003-3229)             -/
/- ------------------------------------------------------------------------- -/

structure KNO where
  HAS_INTEGRAL_COMPLEX_LMUL : thm
  HAS_INTEGRAL_COMPLEX_RMUL : thm
  HAS_INTEGRAL_COMPLEX_0 : thm
  INTEGRABLE_COMPLEX_LMUL : thm
  INTEGRABLE_COMPLEX_RMUL : thm
  INTEGRABLE_COMPLEX_0 : thm
  INTEGRABLE_COMPLEX_LMUL_EQ : thm
  INTEGRABLE_COMPLEX_RMUL_EQ : thm
  INTEGRAL_COMPLEX_LMUL : thm
  INTEGRAL_COMPLEX_RMUL : thm
  ABSOLUTELY_INTEGRABLE_COMPLEX_LMUL : thm
  ABSOLUTELY_INTEGRABLE_COMPLEX_RMUL : thm
  REAL_COMPLEX_INTEGRAL : thm
  INTEGRABLE_BOUNDED_VARIATION_COMPLEX_LMUL : thm
  INTEGRABLE_BOUNDED_VARIATION_COMPLEX_RMUL : thm
  HAS_BOUNDED_VARIATION_ON_COMPLEX_MUL : thm
  HAS_BOUNDED_VARIATION_ON_COMPLEX_INV : thm
  ABEL_LEMMA : thm
  POWER_SERIES_CONV_IMP_ABSCONV : thm
  POWER_SERIES_CONV_IMP_ABSCONV_WEAK : thm
  POWER_SERIES_RADIUS_OF_CONVERGENCE : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupKNO [HolBase] (D : CanalDeps) (BKNC : KNC) (BKNM : KNM) (BKNN : KNN) : ExceptT String IO KNO := do
  -- @@SCOPE BEGIN
  let { SUMMABLE_COMPLEX_LMUL, .. } := BKNC
  let { SERIES_ABSCONV_IMP_CONV, SERIES_COMPARISON_COMPLEX, .. } := BKNM
  let { SUMMABLE_GP, .. } := BKNN
  let { complex_mul, IM, IM_DEF, RE, RE_DEF, .. } := D.cxa
  let { COMPLEX_MUL_ASSOC, COMPLEX_MUL_LID, COMPLEX_MUL_LZERO, COMPLEX_MUL_SYM,
        .. } := D.cxb
  let { COMPLEX_CMUL, COMPLEX_MUL_LINV, COMPLEX_NORM_CX, COMPLEX_VEC_0, CX_MUL, CX_POW,
        RE_CX, .. } := D.cxc
  let { COMPLEX_RING, .. } := D.cxd
  let { COMPLEX_FIELD, .. } := D.cxe
  let { COMPLEX_NORM_0, COMPLEX_NORM_DIV, COMPLEX_NORM_MUL, COMPLEX_NORM_POW, .. } := D.cxf
  let { BILINEAR_COMPLEX_MUL, .. } := D.cxh
  let { real, REAL_CX, .. } := D.cxi
  let { SUMMABLE_IMP_BOUNDED, SUMMABLE_TRIVIAL, .. } := D.qtopology
  let { HAS_BOUNDED_SETVARIATION_ON, HAS_BOUNDED_VARIATION_ON_ADD,
        HAS_BOUNDED_VARIATION_ON_MUL, INTEGRABLE_BOUNDED_VARIATION_BILINEAR_LMUL,
        INTEGRABLE_INTEGRAL, INTEGRAL_COMPONENT, .. } := D.qintegration
  let { DIVISION_OF_FINITE, .. } := D.ms.qintegration1
  let { FORALL_IN_DIVISION_NONEMPTY, HAS_BOUNDED_VARIATION_ON_COMPONENTWISE,
        HAS_BOUNDED_VARIATION_ON_SUB, HAS_INTEGRAL_0, HAS_INTEGRAL_LINEAR, INTEGRABLE_CMUL,
        .. } := D.ms.qintegration2
  let { absolutely_integrable_on, division_of, has_bounded_variation_on, integrable_on,
        INTEGRAL_EQ_0, INTEGRAL_UNIQUE, INTERVAL_LOWERBOUND_NONEMPTY,
        INTERVAL_UPPERBOUND_NONEMPTY, .. } := D.ms.qintegration3
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC, REAL_ARITH, .. } := D.cx.cvx
  let { FORALL_2, .. } := D.cx.cpx
  let { DIMINDEX_2, ETA_AX, .. } := D.cx.cvx.core1
  let { FORALL_IN_IMAGE, IMP_CONJ, .. } := D.cx.cvx.core2
  let { MEMBER_NOT_EMPTY, MONO_EXISTS, REAL_ABS_DIV, REAL_ABS_MUL, .. } := D.cx.cvx.core3
  let { REAL_LE_DIV, REAL_LE_INV2, REAL_LE_LMUL, REAL_LE_MUL, REAL_LE_MUL2,
        REAL_LE_RDIV_EQ, REAL_LE_REFL, REAL_LE_RMUL, REAL_LE_TRANS, REAL_LT_DIV,
        REAL_LT_IMP_LE, REAL_LT_LDIV_EQ, REAL_LT_MUL, .. } := D.cx.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LID, REAL_NOT_LT, REAL_POW_2, REAL_POW_DIV, REAL_POW_LE,
        REAL_POW_LT, SUBSET, .. } := D.cx.cvx.core5
  let { o_DEF, real_abs, real_div, SUM_LE, SUM_RMUL, .. } := D.cx.cvx.core6
  let { ENDS_IN_INTERVAL, LIFT_ADD, LIFT_CMUL, LIFT_DROP, LIFT_EQ, LIFT_NUM, LIFT_SUB,
        .. } := D.cx.cvx.vec2
  let { NORM_NEG, NORM_POS_LE, REAL_ABS_NORM, .. } := D.cx.cvx.vec3
  let { linear, .. } := D.cx.cvx.vec4
  let { BOUNDED_POS, .. } := D.cx.cvx.top1
  let { REAL_ABS_POW, .. } := D.ms.ig.dv.dg.qsession
  -- @@SCOPE END

  let HAS_INTEGRAL_COMPLEX_LMUL ← prove
   r"!f y i c. (f has_integral y) i ==> ((\x. c * f(x)) has_integral (c * y)) i"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC
     (← REWRITE_RULE [o_DEF] HAS_INTEGRAL_LINEAR) THEN
    ASM_REWRITE_TAC [linear, COMPLEX_CMUL] THEN CONV_TAC COMPLEX_RING)

  let HAS_INTEGRAL_COMPLEX_RMUL ← prove
   r"!f y i c. (f has_integral y) i ==> ((\x. f(x) * c) has_integral (y * c)) i"
   (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN
    REWRITE_TAC [HAS_INTEGRAL_COMPLEX_LMUL])

  let HAS_INTEGRAL_COMPLEX_0 ← prove
   r"!s. ((\x. Cx(&0)) has_integral Cx(&0)) s"
   (REWRITE_TAC [← GSYM COMPLEX_VEC_0, HAS_INTEGRAL_0])

  let INTEGRABLE_COMPLEX_LMUL ← prove
   r"!f:real^N->complex s c.
        f integrable_on s ==> (\x. c * f x) integrable_on s"
   (REWRITE_TAC [integrable_on] THEN MESON_TAC [HAS_INTEGRAL_COMPLEX_LMUL])

  let INTEGRABLE_COMPLEX_RMUL ← prove
   r"!f:real^N->complex s c.
        f integrable_on s ==> (\x. f x * c) integrable_on s"
   (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN
    REWRITE_TAC [INTEGRABLE_COMPLEX_LMUL])

  let INTEGRABLE_COMPLEX_0 ← prove
   r"!s. (\x. Cx(&0)) integrable_on s"
   (REWRITE_TAC [integrable_on] THEN MESON_TAC [HAS_INTEGRAL_COMPLEX_0])

  let INTEGRABLE_COMPLEX_LMUL_EQ ← prove
   r"!f:real^N->complex s c.
        (\x. c * f x) integrable_on s <=> c = Cx(&0) \/ f integrable_on s"
   (REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
    ASM_SIMP_TAC [INTEGRABLE_COMPLEX_LMUL, COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC [INTEGRABLE_COMPLEX_0] THEN
    ASM_CASES_TAC (← q r"c = Cx(&0)") THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"inv c:complex") o
      MATCH_MP INTEGRABLE_COMPLEX_LMUL) THEN
    ASM_SIMP_TAC [COMPLEX_MUL_ASSOC, COMPLEX_MUL_LID, COMPLEX_MUL_LINV, ETA_AX])

  let INTEGRABLE_COMPLEX_RMUL_EQ ← prove
   r"!f:real^N->complex s c.
        (\x. f x * c) integrable_on s <=> c = Cx(&0) \/ f integrable_on s"
   (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN
    REWRITE_TAC [INTEGRABLE_COMPLEX_LMUL_EQ])

  let INTEGRAL_COMPLEX_LMUL ← prove
   r"!f:real^N->complex s c.
        f integrable_on s ==> integral s (\x. c * f x) = c * integral s f"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    MATCH_MP_TAC HAS_INTEGRAL_COMPLEX_LMUL THEN
    ASM_SIMP_TAC [INTEGRABLE_INTEGRAL])

  let INTEGRAL_COMPLEX_RMUL ← prove
   r"!f:real^N->complex s c.
        f integrable_on s ==> integral s (\x. f x * c) = integral s f * c"
   (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN
    REWRITE_TAC [INTEGRAL_COMPLEX_LMUL])

  let ABSOLUTELY_INTEGRABLE_COMPLEX_LMUL ← prove
   r"!f s c. f absolutely_integrable_on s
           ==> (\x. c * f x) absolutely_integrable_on s"
   (SIMP_TAC [absolutely_integrable_on, INTEGRABLE_COMPLEX_LMUL] THEN
    SIMP_TAC [COMPLEX_NORM_MUL, LIFT_CMUL, INTEGRABLE_CMUL])

  let ABSOLUTELY_INTEGRABLE_COMPLEX_RMUL ← prove
   r"!f s c. f absolutely_integrable_on s
           ==> (\x. f x * c) absolutely_integrable_on s"
   (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN
    REWRITE_TAC [ABSOLUTELY_INTEGRABLE_COMPLEX_LMUL])

  let REAL_COMPLEX_INTEGRAL ← prove
   r"!f:real^N->complex s.
     f integrable_on s /\ (!x. x IN s ==> real(f x)) ==> real(integral s f)"
   (REWRITE_TAC [real, IM_DEF] THEN SIMP_TAC [INTEGRAL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM LIFT_EQ, LIFT_DROP, LIFT_NUM] THEN
    MATCH_MP_TAC INTEGRAL_EQ_0 THEN
    ASM_REWRITE_TAC [← GSYM LIFT_NUM, LIFT_EQ])

  let INTEGRABLE_BOUNDED_VARIATION_COMPLEX_LMUL ← prove
   r"!f g a b.
        f integrable_on interval[a,b] /\
        g has_bounded_variation_on interval[a,b]
        ==> (\x. g x * f x) integrable_on interval[a,b]"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC INTEGRABLE_BOUNDED_VARIATION_BILINEAR_LMUL THEN
    ASM_REWRITE_TAC [BILINEAR_COMPLEX_MUL])

  let INTEGRABLE_BOUNDED_VARIATION_COMPLEX_RMUL ← prove
   r"!f g a b.
        f integrable_on interval[a,b] /\
        g has_bounded_variation_on interval[a,b]
        ==> (\x. f x * g x) integrable_on interval[a,b]"
   (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN
    REWRITE_TAC [INTEGRABLE_BOUNDED_VARIATION_COMPLEX_LMUL])

  let HAS_BOUNDED_VARIATION_ON_COMPLEX_MUL ← prove
   r"!f g:real^1->complex s.
        f has_bounded_variation_on s /\
        g has_bounded_variation_on s /\
        is_interval s
        ==> (\x. f x * g x) has_bounded_variation_on s"
   (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [HAS_BOUNDED_VARIATION_ON_COMPONENTWISE] THEN
    REWRITE_TAC [complex_mul, DIMINDEX_2, FORALL_2, ← GSYM IM_DEF, ← GSYM RE_DEF] THEN
    SIMP_TAC [RE, IM, LIFT_ADD, LIFT_SUB, LIFT_CMUL] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUB,
      MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_ADD] THEN
    CONJ_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o LAND_CONV)
     [← GSYM LIFT_DROP] THEN
    MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_MUL THEN ASM_REWRITE_TAC [])

  let HAS_BOUNDED_VARIATION_ON_COMPLEX_INV ← prove
   r"!f s e. f has_bounded_variation_on s /\
             &0 < e /\ (!x. x IN s ==> e <= norm(f x))
           ==> (\x. inv(f x)) has_bounded_variation_on s"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    REWRITE_TAC [has_bounded_variation_on, HAS_BOUNDED_SETVARIATION_ON] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"B:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"(B / e pow 2):real") THEN
    ASM_SIMP_TAC [REAL_LT_DIV, REAL_POW_LT] THEN
    MAP_EVERY X_GEN_TAC [← q r"d:(real^1->bool)->bool", ← q r"t:real^1->bool"] THEN
    STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPECL
     [← q r"d:(real^1->bool)->bool", ← q r"t:real^1->bool"]) THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
    ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_POW_LT, ← GSYM SUM_RMUL] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] REAL_LE_TRANS) THEN
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (fun th => tactic_of do
     pure (REWRITE_TAC [← MATCH_MP FORALL_IN_DIVISION_NONEMPTY th])) THEN
    ASM_SIMP_TAC [INTERVAL_LOWERBOUND_NONEMPTY, INTERVAL_UPPERBOUND_NONEMPTY] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real^1", ← q r"b:real^1"] THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"~(f(a:real^1) = Cx(&0)) /\ ~(f(b:real^1) = Cx(&0))")
    STRIP_ASSUME_TAC THENL
     [RULE_ASSUM_TAC (REWRITE_RULE [division_of, ← GSYM REAL_NOT_LT]) THEN
      ASM_MESON_TAC [SUBSET, COMPLEX_NORM_0, ENDS_IN_INTERVAL],
      ASM_SIMP_TAC [← ExceptT.mk (COMPLEX_FIELD
       (← q r"~(w = Cx(&0)) /\ ~(z = Cx(&0))
        ==> inv w - inv z = --(w - z) / (z * w)"))]] THEN
    ASM_SIMP_TAC [← GSYM REAL_LE_RDIV_EQ, REAL_POW_LT, COMPLEX_NORM_DIV] THEN
    REWRITE_TAC [NORM_NEG, real_div] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_SIMP_TAC [COMPLEX_NORM_MUL, REAL_POW_2, REAL_LT_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [division_of, ← GSYM REAL_NOT_LT]) THEN
    ASM_MESON_TAC [SUBSET, COMPLEX_NORM_0, ENDS_IN_INTERVAL])

  let ABEL_LEMMA ← prove
   r"!a M r r0.
        &0 <= r /\ r < r0 /\
        (!n. n IN k ==> norm(a n) * r0 pow n <= M)
        ==> summable k (\n. Cx(norm(a(n)) * r pow n))"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"&0 < r0") ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    ASM_CASES_TAC (← q r"k:num->bool = {}") THEN ASM_REWRITE_TAC [SUMMABLE_TRIVIAL] THEN
    SUBGOAL_THEN (← q r"&0 <= M") ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"i:num")) THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"i:num")) THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"&0 <= x ==> x <= y ==> &0 <= y")) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC [NORM_POS_LE, REAL_POW_LE, REAL_LT_IMP_LE],
      ALL_TAC] THEN
    MATCH_MP_TAC SERIES_COMPARISON_COMPLEX THEN
    EXISTS_TAC (← q r"\n. Cx(M * (r / r0) pow n)") THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC [CX_MUL, CX_POW] THEN MATCH_MP_TAC SUMMABLE_COMPLEX_LMUL THEN
      MATCH_MP_TAC SUMMABLE_GP THEN REWRITE_TAC [COMPLEX_NORM_CX] THEN
      ASM_SIMP_TAC [REAL_ABS_DIV, real_abs, REAL_LT_IMP_LE] THEN
      ASM_SIMP_TAC [REAL_LT_LDIV_EQ, REAL_MUL_LID],
      REWRITE_TAC [REAL_CX, RE_CX] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC [] THEN
      ASM_SIMP_TAC [REAL_LE_DIV, REAL_POW_LE, REAL_LT_IMP_LE],
      EXISTS_TAC (← q r"0") THEN REWRITE_TAC [COMPLEX_NORM_CX] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_POW, REAL_ABS_NORM, REAL_ABS_DIV] THEN
      ASM_SIMP_TAC [real_abs, REAL_LT_IMP_LE, REAL_POW_DIV] THEN
      REWRITE_TAC [real_div, REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC [← GSYM real_div, REAL_LE_RDIV_EQ, REAL_POW_LT] THEN
      ONCE_REWRITE_TAC [← REAL_ARITH (← q r"(a * b) * c:real = (a * c) * b")] THEN
      ASM_SIMP_TAC [REAL_LE_RMUL, REAL_POW_LE, REAL_LT_IMP_LE]])

  let POWER_SERIES_CONV_IMP_ABSCONV ← prove
   r"!a k w z.
        summable k (\n. a(n) * z pow n) /\ norm(w) < norm(z)
        ==> summable k (\n. Cx(norm(a(n) * w pow n)))"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [COMPLEX_NORM_MUL, COMPLEX_NORM_POW] THEN
    MATCH_MP_TAC ABEL_LEMMA THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP SUMMABLE_IMP_BOUNDED) THEN
    REWRITE_TAC [BOUNDED_POS, FORALL_IN_IMAGE] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"B:real") THEN STRIP_TAC THEN
    EXISTS_TAC (← q r"norm(z:complex)") THEN REWRITE_TAC [NORM_POS_LE] THEN
    ASM_REWRITE_TAC [← GSYM COMPLEX_NORM_POW, ← GSYM COMPLEX_NORM_MUL])

  let POWER_SERIES_CONV_IMP_ABSCONV_WEAK ← prove
   r"!a k w z.
        summable k (\n. a(n) * z pow n) /\ norm(w) < norm(z)
        ==> summable k (\n. Cx(norm(a(n))) * w pow n)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_COMPARISON_COMPLEX THEN
    EXISTS_TAC (← q r"\n. Cx(norm(a(n) * w pow n))") THEN CONJ_TAC THENL
     [MATCH_MP_TAC POWER_SERIES_CONV_IMP_ABSCONV THEN
      EXISTS_TAC (← q r"z:complex") THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [REAL_CX, RE_CX, NORM_POS_LE] THEN
    REWRITE_TAC [COMPLEX_NORM_MUL, COMPLEX_NORM_CX, REAL_ABS_NORM,
                 REAL_ABS_MUL, REAL_LE_REFL])

  let POWER_SERIES_RADIUS_OF_CONVERGENCE ← prove
   r"!a k w z.
           summable k (\n. a n * z pow n) /\ norm w < norm z
           ==> summable k (\n. a n * w pow n)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_ABSCONV_IMP_CONV THEN
    REWRITE_TAC [] THEN ASM_MESON_TAC [POWER_SERIES_CONV_IMP_ABSCONV])

  pure { HAS_INTEGRAL_COMPLEX_LMUL, HAS_INTEGRAL_COMPLEX_RMUL, HAS_INTEGRAL_COMPLEX_0,
         INTEGRABLE_COMPLEX_LMUL, INTEGRABLE_COMPLEX_RMUL, INTEGRABLE_COMPLEX_0,
         INTEGRABLE_COMPLEX_LMUL_EQ, INTEGRABLE_COMPLEX_RMUL_EQ, INTEGRAL_COMPLEX_LMUL,
         INTEGRAL_COMPLEX_RMUL, ABSOLUTELY_INTEGRABLE_COMPLEX_LMUL,
         ABSOLUTELY_INTEGRABLE_COMPLEX_RMUL, REAL_COMPLEX_INTEGRAL,
         INTEGRABLE_BOUNDED_VARIATION_COMPLEX_LMUL,
         INTEGRABLE_BOUNDED_VARIATION_COMPLEX_RMUL, HAS_BOUNDED_VARIATION_ON_COMPLEX_MUL,
         HAS_BOUNDED_VARIATION_ON_COMPLEX_INV, ABEL_LEMMA, POWER_SERIES_CONV_IMP_ABSCONV,
         POWER_SERIES_CONV_IMP_ABSCONV_WEAK, POWER_SERIES_RADIUS_OF_CONVERGENCE }
/- ------------------------------------------------------------------------- -/
/- Comparing sums and "integrals" via complex antiderivatives; relating      -/
/- different kinds of complex limits; transforming complex limits to real   -/
/- ones.  (canal.ml 3230-3458)                                              -/
/- ------------------------------------------------------------------------- -/

structure KNP where
  SUM_INTEGRAL_UBOUND_INCREASING : thm
  SUM_INTEGRAL_UBOUND_DECREASING : thm
  SUM_INTEGRAL_LBOUND_INCREASING : thm
  SUM_INTEGRAL_LBOUND_DECREASING : thm
  SUM_INTEGRAL_BOUNDS_INCREASING : thm
  SUM_INTEGRAL_BOUNDS_DECREASING : thm
  LIM_INFINITY_SEQUENTIALLY_COMPLEX : thm
  LIM_AT_INFINITY_COMPLEX_0 : thm
  LIM_ZERO_INFINITY_COMPLEX : thm
  LIM_COMPLEX_REAL : thm
  LIM_COMPLEX_REAL_0 : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupKNP [HolBase] (D : CanalDeps) (BKNF : KNF) (BKNM : KNM) : ExceptT String IO KNP := do
  -- @@SCOPE BEGIN
  let { HAS_COMPLEX_DERIVATIVE_NEG, .. } := BKNF
  let { COMPLEX_MVT_LINE, .. } := BKNM
  let { complex_div, .. } := D.cxa
  let { COMPLEX_MUL_LID, COMPLEX_SUB_RZERO, .. } := D.cxb
  let { COMPLEX_NORM_CX, CX_ADD, CX_SUB, RE_CX, RE_NEG, RE_SUB, .. } := D.cxc
  let { COMPLEX_RING, .. } := D.cxd
  let { COMPLEX_INV_INV, .. } := D.cxe
  let { COMPLEX_INV_EQ_0, COMPLEX_NORM_INV, COMPLEX_NORM_NZ, .. } := D.cxf
  let { COMPLEX_NORM_GE_RE_IM, .. } := D.cxg
  let { REAL, REAL_CX, .. } := D.cxi
  let { IN_SEGMENT_CX, IN_SEGMENT_CX_GEN, REAL_SEGMENT, .. } := D.cxm
  let { LIM_AT_INFINITY, LIM_AT_INFINITY_POS, LIM_AT_LE, .. } := D.qtopology
  let { SUM_DIFFS, .. } := D.qsession
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, REAL_ARITH,
        REAL_ARITH_TAC, .. } := D.cx.cvx
  let { IN_INSERT, MONO_EXISTS, MONO_FORALL, NOT_IN_EMPTY, REAL_ARCH_SIMPLE,
        .. } := D.cx.cvx.core3
  let { REAL_LE_INV2, REAL_LE_NEG2, REAL_LE_REFL, REAL_LE_TRANS, REAL_LT_INV_EQ,
        REAL_LTE_TRANS, .. } := D.cx.cvx.core4
  let { REAL_NEG_SUB, REAL_OF_NUM_ADD, REAL_OF_NUM_LE, REAL_OF_NUM_SUB, REAL_SUB_RZERO,
        SUBSET, .. } := D.cx.cvx.core5
  let { o_DEF, real_ge, SUM_LE_NUMSEG, SUM_NEG, .. } := D.cx.cvx.core6
  let { HULL_MINIMAL, .. } := D.cx.cvx.misc
  let { DIST_NZ, .. } := D.cx.cvx.vec1
  let { dist, .. } := D.cx.cvx.vec4
  let { EVENTUALLY_SEQUENTIALLY, .. } := D.cx.cvx.met
  let { LIM_SEQUENTIALLY, .. } := D.cx.cvx.top4
  let { REAL_INV_INV, .. } := D.ms.ig.dv.qsession
  let { CONVEX_CONVEX_HULL, .. } := D.ms.ig.dv.dg.pt.qcvx2
  let { SEGMENT_CONVEX_HULL, .. } := D.ms.ig.dv.dg.pt.qcvx3
  -- @@SCOPE END

  let SUM_INTEGRAL_UBOUND_INCREASING ← prove
   r"!f g m n.
      m <= n /\
      (!x. x IN segment[Cx(&m),Cx(&n + &1)]
           ==> (g has_complex_derivative f(x)) (at x)) /\
      (!x y. &m <= x /\ x <= y /\ y <= &n + &1 ==> Re(f(Cx x)) <= Re(f(Cx y)))
      ==> sum(m..n) (\k. Re(f(Cx(&k)))) <= Re(g(Cx(&n + &1)) - g(Cx(&m)))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"--sum(m..n) (\k. Re(g(Cx(&k))) - Re(g(Cx(&(k + 1)))))") THEN
    CONJ_TAC THENL
     [ALL_TAC,
      ASM_REWRITE_TAC [SUM_DIFFS, RE_SUB, REAL_NEG_SUB, REAL_OF_NUM_ADD] THEN
      REWRITE_TAC [REAL_LE_REFL]] THEN
    REWRITE_TAC [← GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    REWRITE_TAC [REAL_NEG_SUB] THEN X_GEN_TAC (← q r"r:num") THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"g:complex->complex", ← q r"f:complex->complex",
                      ← q r"Cx(&r)", ← q r"Cx(&r + &1)"] COMPLEX_MVT_LINE) THEN
    ANTS_TAC THENL
     [X_GEN_TAC (← q r"u:complex") THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC (← q r"u IN segment[Cx(&r),Cx(&r + &1)]") THEN
      REWRITE_TAC [SEGMENT_CONVEX_HULL] THEN
      SPEC_TAC (← q r"u:complex", ← q r"u:complex") THEN REWRITE_TAC [← GSYM SUBSET] THEN
      MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_CONVEX_HULL] THEN
      REWRITE_TAC [SUBSET, IN_INSERT, NOT_IN_EMPTY, ← GSYM SEGMENT_CONVEX_HULL] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [IN_SEGMENT_CX] THEN
      REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC,
      REWRITE_TAC [← GSYM REAL_OF_NUM_ADD] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"u:complex")
       (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
      REWRITE_TAC [CX_ADD, ← ExceptT.mk (COMPLEX_RING (← q r"y * ((x + Cx(&1)) - x) = y"))] THEN
      SUBGOAL_THEN (← q r"?y. u = Cx y") (CHOOSE_THEN SUBST_ALL_TAC) THENL
       [ASM_MESON_TAC [REAL_SEGMENT, REAL_CX, REAL], ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX]) THEN
      REPEAT (FIRST_X_ASSUM
       (MP_TAC o GEN_REWRITE_RULE I [← GSYM REAL_OF_NUM_LE])) THEN
      REAL_ARITH_TAC])

  let SUM_INTEGRAL_UBOUND_DECREASING ← prove
   r"!f g m n.
      m <= n /\
      (!x. x IN segment[Cx(&m - &1),Cx(&n)]
           ==> (g has_complex_derivative f(x)) (at x)) /\
      (!x y. &m - &1 <= x /\ x <= y /\ y <= &n ==> Re(f(Cx y)) <= Re(f(Cx x)))
      ==> sum(m..n) (\k. Re(f(Cx(&k)))) <= Re(g(Cx(&n)) - g(Cx(&m - &1)))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     (← q r"--sum(m..n) (\k. Re(g(Cx(&(k) - &1))) - Re(g(Cx(&(k+1) - &1))))") THEN
    CONJ_TAC THENL
     [ALL_TAC,
      ASM_REWRITE_TAC [SUM_DIFFS, REAL_NEG_SUB] THEN
      REWRITE_TAC [← GSYM REAL_OF_NUM_ADD, ← GSYM REAL_OF_NUM_SUB] THEN
      REWRITE_TAC [RE_SUB, ← REAL_ARITH (← q r"(x + &1) - &1 = x"), REAL_LE_REFL]] THEN
    REWRITE_TAC [← GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    REWRITE_TAC [REAL_NEG_SUB] THEN X_GEN_TAC (← q r"r:num") THEN STRIP_TAC THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_ADD, ← REAL_ARITH (← q r"(x + &1) - &1 = x")] THEN
    MP_TAC (← ISPECL [← q r"g:complex->complex", ← q r"f:complex->complex",
                      ← q r"Cx(&r - &1)", ← q r"Cx(&r)"] COMPLEX_MVT_LINE) THEN
    ANTS_TAC THENL
     [X_GEN_TAC (← q r"u:complex") THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC (← q r"u IN segment[Cx(&r - &1),Cx(&r)]") THEN
      REWRITE_TAC [SEGMENT_CONVEX_HULL] THEN
      SPEC_TAC (← q r"u:complex", ← q r"u:complex") THEN REWRITE_TAC [← GSYM SUBSET] THEN
      MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_CONVEX_HULL] THEN
      REWRITE_TAC [SUBSET, IN_INSERT, NOT_IN_EMPTY, ← GSYM SEGMENT_CONVEX_HULL] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [IN_SEGMENT_CX] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN
      REWRITE_TAC [← GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC,
      REWRITE_TAC [← GSYM REAL_OF_NUM_ADD] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"u:complex")
       (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
      REWRITE_TAC [CX_SUB, ← ExceptT.mk (COMPLEX_RING (← q r"y * (x - (x - Cx(&1))) = y"))] THEN
      SUBGOAL_THEN (← q r"?y. u = Cx y") (CHOOSE_THEN SUBST_ALL_TAC) THENL
       [ASM_MESON_TAC [REAL_SEGMENT, REAL_CX, REAL], ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX]) THEN
      REPEAT (FIRST_X_ASSUM
       (MP_TAC o GEN_REWRITE_RULE I [← GSYM REAL_OF_NUM_LE])) THEN
      REAL_ARITH_TAC])

  let SUM_INTEGRAL_LBOUND_INCREASING ← prove
   r"!f g m n.
      m <= n /\
      (!x. x IN segment[Cx(&m - &1),Cx(&n)]
           ==> (g has_complex_derivative f(x)) (at x)) /\
      (!x y. &m - &1 <= x /\ x <= y /\ y <= &n ==> Re(f(Cx x)) <= Re(f(Cx y)))
      ==> Re(g(Cx(&n)) - g(Cx(&m - &1))) <= sum(m..n) (\k. Re(f(Cx(&k))))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"\z. --((f:complex->complex) z)",
                      ← q r"\z. --((g:complex->complex) z)",
                      ← q r"m:num", ← q r"n:num"] SUM_INTEGRAL_UBOUND_DECREASING) THEN
    REWRITE_TAC [RE_NEG, RE_SUB, SUM_NEG, REAL_LE_NEG2,
                 ← REAL_ARITH (← q r"--x - --y:real = --(x - y)")] THEN
    ASM_SIMP_TAC [HAS_COMPLEX_DERIVATIVE_NEG])

  let SUM_INTEGRAL_LBOUND_DECREASING ← prove
   r"!f g m n.
      m <= n /\
      (!x. x IN segment[Cx(&m),Cx(&n + &1)]
           ==> (g has_complex_derivative f(x)) (at x)) /\
      (!x y. &m <= x /\ x <= y /\ y <= &n + &1 ==> Re(f(Cx y)) <= Re(f(Cx x)))
      ==> Re(g(Cx(&n + &1)) - g(Cx(&m))) <= sum(m..n) (\k. Re(f(Cx(&k))))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"\z. --((f:complex->complex) z)",
                      ← q r"\z. --((g:complex->complex) z)",
                      ← q r"m:num", ← q r"n:num"] SUM_INTEGRAL_UBOUND_INCREASING) THEN
    REWRITE_TAC [RE_NEG, RE_SUB, SUM_NEG, REAL_LE_NEG2,
                 ← REAL_ARITH (← q r"--x - --y:real = --(x - y)")] THEN
    ASM_SIMP_TAC [HAS_COMPLEX_DERIVATIVE_NEG])

  let SUM_INTEGRAL_BOUNDS_INCREASING ← prove
   r"!f g m n.
         m <= n /\
         (!x. x IN segment[Cx(&m - &1),Cx (&n + &1)]
              ==> (g has_complex_derivative f x) (at x)) /\
         (!x y.
              &m - &1 <= x /\ x <= y /\ y <= &n + &1
              ==> Re(f(Cx x)) <= Re(f(Cx y)))
         ==> Re(g(Cx(&n)) - g(Cx(&m - &1))) <= sum(m..n) (\k. Re(f(Cx(&k)))) /\
             sum (m..n) (\k. Re(f(Cx(&k)))) <= Re(g(Cx(&n + &1)) - g(Cx(&m)))"
   (REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC SUM_INTEGRAL_LBOUND_INCREASING,
      MATCH_MP_TAC SUM_INTEGRAL_UBOUND_INCREASING] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [IN_SEGMENT_CX_GEN, ← GSYM REAL_OF_NUM_LE]) THEN
    REWRITE_TAC [IN_SEGMENT_CX_GEN] THEN ASM_REAL_ARITH_TAC)

  let SUM_INTEGRAL_BOUNDS_DECREASING ← prove
   r"!f g m n.
      m <= n /\
      (!x. x IN segment[Cx(&m - &1),Cx(&n + &1)]
           ==> (g has_complex_derivative f(x)) (at x)) /\
      (!x y. &m - &1 <= x /\ x <= y /\ y <= &n + &1
             ==> Re(f(Cx y)) <= Re(f(Cx x)))
      ==> Re(g(Cx(&n + &1)) - g(Cx(&m))) <= sum(m..n) (\k. Re(f(Cx(&k)))) /\
          sum(m..n) (\k. Re(f(Cx(&k)))) <= Re(g(Cx(&n)) - g(Cx(&m - &1)))"
   (REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC SUM_INTEGRAL_LBOUND_DECREASING,
      MATCH_MP_TAC SUM_INTEGRAL_UBOUND_DECREASING] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [IN_SEGMENT_CX_GEN, ← GSYM REAL_OF_NUM_LE]) THEN
    REWRITE_TAC [IN_SEGMENT_CX_GEN] THEN ASM_REAL_ARITH_TAC)

  let LIM_INFINITY_SEQUENTIALLY_COMPLEX ← prove
   r"!f l. (f --> l) at_infinity ==> ((\n. f(Cx(&n))) --> l) sequentially"
   (REPEAT GEN_TAC THEN REWRITE_TAC [LIM_AT_INFINITY, LIM_SEQUENTIALLY] THEN
    DISCH_TAC THEN X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e:real")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"B:real")) THEN
    MP_TAC (← ISPEC (← q r"B:real") REAL_ARCH_SIMPLE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"N:num") THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [COMPLEX_NORM_CX] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC)

  let LIM_AT_INFINITY_COMPLEX_0 ← prove
   r"!f l:real^N.
        (f --> l) at_infinity <=> ((f o inv) --> l) (at(Cx(&0)))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [LIM_AT_LE, LIM_AT_INFINITY_POS, o_DEF] THEN
    REWRITE_TAC [← GSYM DIST_NZ, real_ge] THEN
    REWRITE_TAC [dist, COMPLEX_SUB_RZERO] THEN EQ_TAC THEN DISCH_TAC THEN
    X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e:real")) THEN ASM_REWRITE_TAC [real_ge] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"inv(b:real)") THEN ASM_REWRITE_TAC [REAL_LT_INV_EQ] THEN
    X_GEN_TAC (← q r"z:complex") THEN STRIP_TAC THENL
     [ALL_TAC, SUBST1_TAC (← SYM (← SPEC (← q r"z:complex") COMPLEX_INV_INV))] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_INV_INV] THEN
      REWRITE_TAC [COMPLEX_NORM_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC [COMPLEX_NORM_NZ],
      ASM_REWRITE_TAC [COMPLEX_INV_EQ_0] THEN CONJ_TAC THENL
       [REWRITE_TAC [← GSYM COMPLEX_NORM_NZ] THEN
        TRANS_TAC REAL_LTE_TRANS (← q r"inv(b:real)") THEN
        ASM_REWRITE_TAC [REAL_LT_INV_EQ],
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_INV_INV] THEN
        REWRITE_TAC [COMPLEX_NORM_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        ASM_REWRITE_TAC [REAL_LT_INV_EQ]]])

  let LIM_ZERO_INFINITY_COMPLEX ← prove
   r"!f l:real^N.
     ((\x. f(Cx(&1) / x)) --> l) (at (Cx(&0))) ==> (f --> l) at_infinity"
   (REWRITE_TAC [LIM_AT_INFINITY_COMPLEX_0, o_DEF, complex_div] THEN
    REWRITE_TAC [COMPLEX_MUL_LID])

  let LIM_COMPLEX_REAL ← prove
   r"!f g l m.
         eventually (\n. Re(g n) = f n) sequentially /\
         Re m = l /\
         (g --> m) sequentially
         ==> !e. &0 < e ==> ?N. !n. N <= n ==> abs(f n - l) < e"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [EVENTUALLY_SEQUENTIALLY, LIM_SEQUENTIALLY] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"N1:num"))
     (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC)) THEN
    X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e:real")) THEN ASM_REWRITE_TAC [dist] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"N0:num")) THEN EXISTS_TAC (← q r"N0 + N1:num") THEN
    X_GEN_TAC (← q r"n:num") THEN DISCH_THEN (STRIP_ASSUME_TAC o MATCH_MP (← ARITH_RULE
     (← q r"N0 + N1:num <= n ==> N0 <= n /\ N1 <= n"))) THEN
    UNDISCH_THEN (← q r"!n. N0 <= n ==> norm ((g:num->complex) n - m) < e")
     (MP_TAC o SPEC (← q r"n:num")) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"n:num")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [← GSYM RE_SUB] THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"x <= y ==> y < e ==> x < e")) THEN
    REWRITE_TAC [COMPLEX_NORM_GE_RE_IM])

  let LIM_COMPLEX_REAL_0 ← prove
   r"!f g. eventually (\n. Re(g n) = f n) sequentially /\
         (g --> Cx(&0)) sequentially
         ==> !e. &0 < e ==> ?N. !n. N <= n ==> abs(f n) < e"
   (MP_TAC LIM_COMPLEX_REAL THEN
    REPLICATE_TAC 2 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN (MP_TAC o SPECL [← q r"&0", ← q r"Cx(&0)"]) THEN
    REWRITE_TAC [RE_CX, REAL_SUB_RZERO])

  pure { SUM_INTEGRAL_UBOUND_INCREASING, SUM_INTEGRAL_UBOUND_DECREASING,
         SUM_INTEGRAL_LBOUND_INCREASING, SUM_INTEGRAL_LBOUND_DECREASING,
         SUM_INTEGRAL_BOUNDS_INCREASING, SUM_INTEGRAL_BOUNDS_DECREASING,
         LIM_INFINITY_SEQUENTIALLY_COMPLEX, LIM_AT_INFINITY_COMPLEX_0,
         LIM_ZERO_INFINITY_COMPLEX, LIM_COMPLEX_REAL, LIM_COMPLEX_REAL_0 }
/- ------------------------------------------------------------------------- -/
/- Uniform convergence of power series in a "Stolz angle"; hence continuity  -/
/- and the Abel limit theorem.  (canal.ml 3459-3731)                        -/
/- ------------------------------------------------------------------------- -/

structure KNQ where
  POWER_SERIES_UNIFORM_CONVERGENCE_STOLZ_1 : thm
  POWER_SERIES_UNIFORM_CONVERGENCE_STOLZ : thm
  ABEL_POWER_SERIES_CONTINUOUS : thm
  ABEL_POWER_SERIES_CONTINUOUS_1 : thm
  ABEL_LIMIT_THEOREM : thm
  ABEL_LIMIT_THEOREM_1 : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupKNQ [HolBase] (D : CanalDeps) (BKNC : KNC) (BKNM : KNM) (BKNO : KNO) : ExceptT String IO KNQ := do
  -- @@SCOPE BEGIN
  let { CONTINUOUS_ON_COMPLEX_MUL, CONTINUOUS_ON_COMPLEX_POW, .. } := BKNC
  let { SERIES_ABSCONV_IMP_CONV, .. } := BKNM
  let { POWER_SERIES_CONV_IMP_ABSCONV, POWER_SERIES_RADIUS_OF_CONVERGENCE, .. } := BKNO
  let { complex_pow, .. } := D.cxa
  let { COMPLEX_MUL_ASSOC, COMPLEX_MUL_LZERO, COMPLEX_MUL_RID, COMPLEX_MUL_RZERO,
        COMPLEX_SUB_LZERO, COMPLEX_SUB_REFL, .. } := D.cxb
  let { COMPLEX_NORM_CX, COMPLEX_POW_MUL, COMPLEX_POW_ONE, COMPLEX_POW_ZERO, COMPLEX_VEC_0,
        .. } := D.cxc
  let { COMPLEX_RING, .. } := D.cxd
  let { COMPLEX_FIELD, .. } := D.cxe
  let { COMPLEX_DIV_LMUL, COMPLEX_DIV_RMUL, COMPLEX_NORM_0, COMPLEX_NORM_MUL,
        COMPLEX_NORM_NZ, COMPLEX_NORM_POW, .. } := D.cxf
  let { INFSUM_RESTRICT, INFSUM_UNIQUE, SEQUENCE_CAUCHY_WLOG, SUMMABLE_RESTRICT,
        SUMS_INFSUM, UNIFORMLY_CAUCHY_IMP_UNIFORMLY_CONVERGENT, .. } := D.qtopology
  let { VSUM_COMBINE_R, VSUM_SING_NUMSEG, .. } := D.qvectors
  let { REAL_POW_1_LT, .. } := D.qsession
  let { SUC_SUB1, .. } := D.ms.qsession
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INDUCT_TAC, MESON,
        NORM_ARITH, REAL_ARITH, REAL_ARITH_TAC, SET_RULE, .. } := D.cx.cvx
  let { LE_0, NOT_SUC, REAL_SUB_LZERO, .. } := D.cx.cpx
  let { SUM_GP, .. } := D.ms.ig.qmisc
  let { CONTINUOUS_ON, CONTINUOUS_UNIFORM_LIMIT, .. } := D.ms.ig.qtopology
  let { VSUM_NORM_LE, .. } := D.ms.ig.qvec
  let { COND_RAND, COND_RATOR, CONTRAPOS_THM, ETA_AX, FINITE_INTER, FINITE_NUMSEG,
        .. } := D.cx.cvx.core1
  let { FORALL_UNWIND_THM2, GE, IMP_CONJ, IMP_IMP, INTER_UNIV, .. } := D.cx.cvx.core2
  let { IN_ELIM_THM, IN_INTER, IN_NUMSEG, LT_IMP_LE, MONO_EXISTS, MONO_FORALL,
        NUMSEG_EMPTY, REAL_ABS_NUM, REAL_DIV_REFL, .. } := D.cx.cvx.core3
  let { REAL_LE_MUL, REAL_LE_MUL2, REAL_LE_MUL_EQ, REAL_LE_REFL, REAL_LE_RMUL,
        REAL_LE_TRANS, REAL_LET_TRANS, REAL_LT_DIV, REAL_LT_DIV2_EQ, REAL_LT_IMP_NZ,
        REAL_LT_LE, REAL_LT_LMUL_EQ, REAL_LT_MIN, REAL_LT_RDIV_EQ, .. } := D.cx.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_RID, REAL_MUL_RNEG, REAL_MUL_RZERO,
        REAL_NEG_SUB, REAL_POW_LE, REAL_SUB_LE, REAL_SUB_LT, REAL_SUB_RDISTRIB,
        REAL_SUB_REFL, RIGHT_IMP_FORALL_THM, .. } := D.cx.cvx.core5
  let { SUM_LMUL, .. } := D.cx.cvx.core6
  let { REAL_HALF, .. } := D.cx.cvx.misc
  let { NORM_0, .. } := D.cx.cvx.vec2
  let { NORM_LE_0, NORM_NEG, NORM_POS_LE, NORM_POS_LT, .. } := D.cx.cvx.vec3
  let { dist, VECTOR_SUB_EQ, VSUM_CLAUSES, VSUM_CLAUSES_NUMSEG, VSUM_DELTA,
        VSUM_RESTRICT_SET, .. } := D.cx.cvx.vec4
  let { EVENTUALLY_MONO, EVENTUALLY_SEQUENTIALLY, TRIVIAL_LIMIT_SEQUENTIALLY,
        .. } := D.cx.cvx.met
  let { CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID, .. } := D.cx.cvx.top3
  let { LIM_SEQUENTIALLY, .. } := D.cx.cvx.top4
  let { ALWAYS_EVENTUALLY, .. } := D.ms.ig.dv.qmetric
  let { REAL_LT_MUL2, .. } := D.ms.ig.dv.qsession
  let { CONVERGENT_IMP_CAUCHY, .. } := D.ms.ig.dv.qtopology1
  let { cauchy, LIM_EVENTUALLY, sums, .. } := D.ms.ig.dv.qtopology2
  let { EVENTUALLY_AND, .. } := D.ms.ig.dv.dg.qmetric
  let { LT, .. } := D.ms.ig.dv.dg.qsession
  let { CONTINUOUS_ON_VSUM, .. } := D.ms.ig.dv.dg.qtopology1
  let { tendsto, .. } := D.ms.ig.dv.dg.qtopology2
  let { REAL_LE_RCANCEL_IMP, .. } := D.ms.ig.dv.dg.pt.qses
  -- @@SCOPE END

  let POWER_SERIES_UNIFORM_CONVERGENCE_STOLZ_1 ← (do
    let lemma ← prove
     r"!M w z. &0 < M /\ norm(w - z) <= M * (norm w - norm z) /\ ~(z = w)
               ==> norm(z) < norm(w)"
     (REPEAT STRIP_TAC THEN REWRITE_TAC [REAL_LT_LE] THEN CONJ_TAC THENL
       [ASM_MESON_TAC [REAL_LE_MUL_EQ, REAL_SUB_LE, NORM_POS_LE, REAL_LE_TRANS],
        DISCH_THEN SUBST_ALL_TAC THEN
        ASM_MESON_TAC [REAL_SUB_REFL, REAL_MUL_RZERO, NORM_LE_0, VECTOR_SUB_EQ]])
    let lemma1 ← prove
     r"!m n. m < n
             ==> vsum (m..n) (\i. a i * z pow i) =
                 (Cx(&1) - z) * vsum(m..n-1) (\i. vsum (m..i) a * z pow i) +
                 vsum(m..n) a * z pow n"
     (GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [NOT_SUC, SUC_SUB1] THEN
      SIMP_TAC [VSUM_CLAUSES_NUMSEG, LT, LT_IMP_LE] THEN STRIP_TAC THENL
       [ASM_REWRITE_TAC [VSUM_SING_NUMSEG, complex_pow] THEN CONV_TAC COMPLEX_RING,
        ASM_SIMP_TAC [] THEN UNDISCH_TAC (← q r"m:num < n") THEN
        POP_ASSUM (K ALL_TAC)] THEN
      SPEC_TAC (← q r"n:num", ← q r"n:num") THEN
      INDUCT_TAC THEN REWRITE_TAC [← CONJUNCT1 LT] THEN POP_ASSUM (K ALL_TAC) THEN
      SIMP_TAC [SUC_SUB1, VSUM_CLAUSES_NUMSEG, LT_IMP_LE] THEN
      ASM_REWRITE_TAC [VSUM_SING_NUMSEG, complex_pow] THEN
      CONV_TAC COMPLEX_RING)
    prove
     r"!M a s e.
          summable s a /\ &0 < M /\ &0 < e
          ==> eventually
               (\n. !z. norm(Cx(&1) - z) <= M * (&1 - norm z)
                        ==> norm(vsum (s INTER (0..n)) (\i. a i * z pow i) -
                                 infsum s (\i. a i * z pow i)) < e)
               sequentially"
     (SUBGOAL_THEN
       (← q r"!M a e.
            summable (:num) a /\ &0 < M /\ &0 < e
            ==> eventually
                 (\n. !z. norm(Cx(&1) - z) <= M * (&1 - norm z)
                          ==> norm(vsum (0..n) (\i. a i * z pow i) -
                                   infsum (:num) (\i. a i * z pow i)) < e)
                 sequentially")
      ASSUME_TAC THENL
       [ALL_TAC,
        REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o ISPECL
         [← q r"M:real", ← q r"\i:num. if i IN s then a i else Cx(&0)", ← q r"e:real"]) THEN
        REWRITE_TAC [COND_RAND, COND_RATOR, COMPLEX_MUL_LZERO] THEN
        ASM_REWRITE_TAC [← GSYM COMPLEX_VEC_0, ← GSYM VSUM_RESTRICT_SET,
                         INFSUM_RESTRICT, SUMMABLE_RESTRICT] THEN
        REWRITE_TAC [← SET_RULE (← q r"{i | i IN t /\ i IN s} = s INTER t")]] THEN
      REPEAT STRIP_TAC THEN
      ONCE_REWRITE_TAC [← MESON []
       (← q r"(!z. P z) <=> P (Cx(&1)) /\ (!z. ~(z = Cx(&1)) ==> P z)")] THEN
      REWRITE_TAC [EVENTUALLY_AND] THEN CONJ_TAC THENL
       [REWRITE_TAC [COMPLEX_NORM_CX, REAL_ABS_NUM, COMPLEX_SUB_REFL,
                     REAL_SUB_REFL, REAL_MUL_RZERO, REAL_LE_REFL] THEN
        UNDISCH_TAC (← q r"&0 < e") THEN SPEC_TAC (← q r"e:real", ← q r"e:real") THEN
        REWRITE_TAC [← GSYM tendsto, COMPLEX_POW_ONE, COMPLEX_MUL_RID, ← GSYM dist,
                     ETA_AX] THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM SUMS_INFSUM]) THEN
        REWRITE_TAC [sums, INTER_UNIV],
        ALL_TAC] THEN
      REWRITE_TAC [IMP_IMP, EVENTUALLY_SEQUENTIALLY] THEN
      REWRITE_TAC [RIGHT_IMP_FORALL_THM, IMP_IMP, ← GSYM dist] THEN
      UNDISCH_TAC (← q r"&0 < e") THEN SPEC_TAC (← q r"e:real", ← q r"e:real") THEN
      MATCH_MP_TAC UNIFORMLY_CAUCHY_IMP_UNIFORMLY_CONVERGENT THEN
      REWRITE_TAC [← GSYM LIM_SEQUENTIALLY] THEN CONJ_TAC THENL
       [X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
        REWRITE_TAC [← MESON [] (← q r"(!m n z. P m /\ P n /\ Q z ==> R m n z) <=>
                             (!z. Q z ==> !m n. P m /\ P n ==> R m n z)")] THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM SUMS_INFSUM]) THEN
        REWRITE_TAC [sums] THEN
        DISCH_THEN (MP_TAC o MATCH_MP CONVERGENT_IMP_CAUCHY) THEN
        REWRITE_TAC [cauchy, ← GSYM dist] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"min (e / &2) (e / &2 / M)")) THEN
        ASM_SIMP_TAC [REAL_LT_MIN, REAL_LT_DIV, REAL_HALF, GE, INTER_UNIV] THEN
        REWRITE_TAC [← GSYM REAL_LT_MIN] THEN
        ONCE_REWRITE_TAC [SEQUENCE_CAUCHY_WLOG] THEN
        SUBGOAL_THEN
         (← q r"!f:num->complex m n. m <= n
                  ==> dist(vsum (0..m) f,vsum (0..n) f) = norm(vsum (m+1..n) f)")
         (fun th => SIMP_TAC [th])
        THENL
         [REPEAT STRIP_TAC THEN
          MATCH_MP_TAC (← NORM_ARITH (← q r"a + c = b ==> dist(a,b) = norm c")) THEN
          MATCH_MP_TAC VSUM_COMBINE_R THEN ASM_ARITH_TAC,
          ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"N:num") THEN
        REWRITE_TAC [REAL_LT_MIN] THEN STRIP_TAC THEN
        X_GEN_TAC (← q r"z:complex") THEN REWRITE_TAC [dist] THEN STRIP_TAC THEN
        SUBGOAL_THEN (← q r"norm(z:complex) < &1") ASSUME_TAC THENL
         [UNDISCH_TAC (← q r"~(z = Cx(&1))") THEN
          ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
          REWRITE_TAC [NORM_POS_LT, VECTOR_SUB_EQ] THEN DISCH_TAC THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← NORM_ARITH
           (← q r"norm(a - b) <= M ==> &0 <= --M ==> b = a"))) THEN
          REWRITE_TAC [← GSYM REAL_MUL_RNEG, REAL_NEG_SUB] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC,
          ALL_TAC] THEN
        MAP_EVERY X_GEN_TAC [← q r"m:num", ← q r"n:num"] THEN STRIP_TAC THEN
        ASM_CASES_TAC (← q r"m + 1 < n") THENL
         [ASM_SIMP_TAC [lemma1] THEN
          MATCH_MP_TAC (← NORM_ARITH
           (← q r"norm(a) < e / &2 /\ norm(b) < e / &2 ==> norm(a + b) < e")) THEN
          REWRITE_TAC [COMPLEX_NORM_MUL, COMPLEX_NORM_POW] THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LET_TRANS THEN
            EXISTS_TAC (← q r"(M * (&1 - norm(z:complex))) *
                        sum (m+1..n-1) (\i. e / &2 / M * norm(z) pow i)") THEN
            CONJ_TAC THENL
             [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC [NORM_POS_LE] THEN
              MATCH_MP_TAC VSUM_NORM_LE THEN
              REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
              X_GEN_TAC (← q r"p:num") THEN STRIP_TAC THEN
              ASM_SIMP_TAC [COMPLEX_NORM_MUL, COMPLEX_NORM_POW] THEN
              MATCH_MP_TAC REAL_LE_RMUL THEN
              SIMP_TAC [REAL_POW_LE, NORM_POS_LE] THEN
              MATCH_MP_TAC (← REAL_ARITH
                (← q r"x < e / &2 /\ x < e / &2 / M ==> x <= e / &2 / M")) THEN
              FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
              REWRITE_TAC [SUM_LMUL] THEN
              REWRITE_TAC [← REAL_ARITH
               (← q r"(M * z1) * e / &2 / M * s < e / &2 <=>
                e * (M / M) * s * z1 < e * &1")] THEN
              ASM_SIMP_TAC [REAL_LT_LMUL_EQ] THEN
              ASM_SIMP_TAC [REAL_DIV_REFL, REAL_LT_IMP_NZ, REAL_MUL_LID] THEN
              ASM_SIMP_TAC [← GSYM REAL_LT_RDIV_EQ, REAL_SUB_LT] THEN
              REWRITE_TAC [SUM_GP] THEN
              COND_CASES_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
              COND_CASES_TAC THENL
               [UNDISCH_TAC (← q r"norm(Cx(&1) - z) <= M * (&1 - norm z)") THEN
                ASM_REWRITE_TAC [REAL_SUB_REFL, REAL_MUL_RZERO] THEN
                ASM_REWRITE_TAC [← NORM_ARITH (← q r"norm(x - y:complex) <= &0 <=> x = y")],
                ALL_TAC] THEN
              ASM_SIMP_TAC [REAL_LT_DIV2_EQ, REAL_SUB_LT] THEN
              MATCH_MP_TAC (← REAL_ARITH
               (← q r"&0 <= y /\ x < &1 ==> x - y < &1")) THEN
              ASM_SIMP_TAC [REAL_POW_LE, NORM_POS_LE] THEN
              MATCH_MP_TAC REAL_POW_1_LT THEN
              ASM_REWRITE_TAC [NORM_POS_LE] THEN ARITH_TAC],
            GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_RID] THEN
            MATCH_MP_TAC REAL_LT_MUL2 THEN SIMP_TAC [NORM_POS_LE, REAL_POW_LE] THEN
            CONJ_TAC THENL
             [MATCH_MP_TAC (← REAL_ARITH
                (← q r"x < e / &2 /\ x < e / &2 / M ==> x < e / &2")) THEN
              FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
              MATCH_MP_TAC REAL_POW_1_LT THEN
              ASM_REWRITE_TAC [NORM_POS_LE] THEN ASM_ARITH_TAC]],
          ASM_CASES_TAC (← q r"(m+1)..n = {}") THENL
           [ASM_REWRITE_TAC [VSUM_CLAUSES, NORM_0], ALL_TAC] THEN
          RULE_ASSUM_TAC (REWRITE_RULE [NUMSEG_EMPTY]) THEN
          SUBGOAL_THEN (← q r"m + 1 = n") SUBST1_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
          REWRITE_TAC [VSUM_SING_NUMSEG] THEN
          REWRITE_TAC [COMPLEX_NORM_MUL, COMPLEX_NORM_POW] THEN
          GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_RID] THEN
          MATCH_MP_TAC REAL_LT_MUL2 THEN SIMP_TAC [NORM_POS_LE, REAL_POW_LE] THEN
          CONJ_TAC THENL
           [FIRST_X_ASSUM (MP_TAC o SPECL [← q r"m:num", ← q r"n:num"]) THEN
            SUBGOAL_THEN (← q r"m + 1 = n") SUBST1_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
            ANTS_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [VSUM_SING_NUMSEG]] THEN
            ASM_REAL_ARITH_TAC,
            MATCH_MP_TAC REAL_POW_1_LT THEN
            ASM_REWRITE_TAC [NORM_POS_LE] THEN ASM_ARITH_TAC]],
        X_GEN_TAC (← q r"z:complex") THEN REWRITE_TAC [dist] THEN STRIP_TAC THEN
        MP_TAC (← ISPECL [← q r"M:real", ← q r"Cx(&1)", ← q r"z:complex"] lemma) THEN
        ASM_REWRITE_TAC [COMPLEX_NORM_CX, REAL_ABS_NUM] THEN DISCH_TAC THEN
        SUBGOAL_THEN (← q r"summable (:num) (\i. a i * z pow i)") MP_TAC THENL
         [MATCH_MP_TAC SERIES_ABSCONV_IMP_CONV THEN
          REWRITE_TAC [] THEN MATCH_MP_TAC POWER_SERIES_CONV_IMP_ABSCONV THEN
          EXISTS_TAC (← q r"Cx(&1)") THEN
          REWRITE_TAC [COMPLEX_POW_ONE, COMPLEX_NORM_CX] THEN
          ASM_REWRITE_TAC [REAL_ABS_NUM, COMPLEX_MUL_RID, ETA_AX],
          REWRITE_TAC [← GSYM SUMS_INFSUM] THEN
          REWRITE_TAC [sums, INTER_UNIV]]]))

  let POWER_SERIES_UNIFORM_CONVERGENCE_STOLZ ← prove
   r"!M a w s e.
        summable s (\i. a i * w pow i) /\ &0 < M /\ &0 < e
        ==> eventually
             (\n. !z. norm(w - z) <= M * (norm w - norm z)
                      ==> norm(vsum (s INTER (0..n)) (\i. a i * z pow i) -
                               infsum s (\i. a i * z pow i)) < e)
             sequentially"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"w = Cx(&0)") THENL
     [ASM_REWRITE_TAC [COMPLEX_SUB_LZERO, REAL_SUB_LZERO, COMPLEX_NORM_0] THEN
      REWRITE_TAC [NORM_NEG, ← REAL_ARITH
        (← q r"n <= M * --n <=> &0 <= --n * (&1 + M)")] THEN
      ASM_SIMP_TAC [REAL_LE_MUL_EQ, ← REAL_ARITH (← q r"&0 < M ==> &0 < &1 + M")] THEN
      REWRITE_TAC [← NORM_ARITH (← q r"&0 <= --norm z <=> z = vec 0")] THEN
      REWRITE_TAC [EVENTUALLY_SEQUENTIALLY, FORALL_UNWIND_THM2] THEN
      EXISTS_TAC (← q r"1") THEN X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN
      REWRITE_TAC [COMPLEX_VEC_0, COMPLEX_POW_ZERO] THEN
      REWRITE_TAC [COND_RATOR, COND_RAND, COMPLEX_MUL_RZERO, COMPLEX_MUL_RID] THEN
      MATCH_MP_TAC (← NORM_ARITH (← q r"x = y /\ &0 < e ==> norm(y - x) < e")) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INFSUM_UNIQUE THEN
      REWRITE_TAC [sums] THEN MATCH_MP_TAC LIM_EVENTUALLY THEN
      REWRITE_TAC [EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC (← q r"1") THEN
      X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN
      SIMP_TAC [← GSYM COMPLEX_VEC_0, VSUM_DELTA] THEN
      REWRITE_TAC [IN_INTER, LE_0, IN_NUMSEG],
      FIRST_ASSUM (MP_TAC o MATCH_MP POWER_SERIES_UNIFORM_CONVERGENCE_STOLZ_1) THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] EVENTUALLY_MONO) THEN
      X_GEN_TAC (← q r"n:num") THEN REWRITE_TAC [] THEN DISCH_TAC THEN
      X_GEN_TAC (← q r"z:complex") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"z / w:complex")) THEN
      ASM_SIMP_TAC [← GSYM COMPLEX_MUL_ASSOC, ← GSYM COMPLEX_POW_MUL] THEN
      ASM_SIMP_TAC [COMPLEX_DIV_LMUL] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC (← q r"norm(w:complex)") THEN
      ASM_REWRITE_TAC [COMPLEX_NORM_NZ, ← GSYM COMPLEX_NORM_MUL] THEN
      ASM_SIMP_TAC [← ExceptT.mk (COMPLEX_FIELD
       (← q r"~(w = Cx(&0)) ==> (Cx(&1) - z / w) * w = w - z"))] THEN
      REWRITE_TAC [← GSYM REAL_MUL_ASSOC, REAL_SUB_RDISTRIB] THEN
      REWRITE_TAC [← GSYM COMPLEX_NORM_MUL, REAL_MUL_LID] THEN
      ASM_SIMP_TAC [COMPLEX_DIV_RMUL]])

  let ABEL_POWER_SERIES_CONTINUOUS ← prove
   r"!M s a w.
        summable s (\i. a i * w pow i) /\ &0 < M
        ==> (\z. infsum s (\i. a i * z pow i)) continuous_on
            {z | norm(w - z) <= M * (norm w - norm z)}"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← ISPEC (← q r"sequentially") CONTINUOUS_UNIFORM_LIMIT) THEN
    EXISTS_TAC (← q r"\n z. vsum (s INTER (0..n)) (\i. a i * z pow i)") THEN
    ASM_SIMP_TAC [POWER_SERIES_UNIFORM_CONVERGENCE_STOLZ, IN_ELIM_THM,
                  TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC (← q r"n:num") THEN
    REWRITE_TAC [] THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
    SIMP_TAC [CONTINUOUS_ON_COMPLEX_MUL, CONTINUOUS_ON_COMPLEX_POW,
              CONTINUOUS_ON_ID, CONTINUOUS_ON_CONST, FINITE_INTER,
              FINITE_NUMSEG])

  let ABEL_POWER_SERIES_CONTINUOUS_1 ← prove
   r"!M s a.
        summable s a /\ &0 < M
        ==> (\z. infsum s (\i. a i * z pow i)) continuous_on
            {z | norm(Cx(&1) - z) <= M * (&1 - norm z)}"
   (MP_TAC ABEL_POWER_SERIES_CONTINUOUS THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"Cx(&1)")) THEN
    REWRITE_TAC [COMPLEX_NORM_CX, REAL_ABS_NUM, COMPLEX_POW_ONE] THEN
    REWRITE_TAC [COMPLEX_MUL_RID, ETA_AX])

  let ABEL_LIMIT_THEOREM ← prove
   r"!M s a w.
        summable s (\i. a i * w pow i) /\ &0 < M
        ==> (!z. norm(z) < norm(w) ==> summable s (\i. a i * z pow i)) /\
            ((\z. infsum s (\i. a i * z pow i)) -->
             infsum s  (\i. a i * w pow i))
            (at w within {z | norm(w - z) <= M * (norm w - norm z)})"
   (MP_TAC ABEL_POWER_SERIES_CONTINUOUS THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC [POWER_SERIES_RADIUS_OF_CONVERGENCE], ALL_TAC] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE [CONTINUOUS_ON]) THEN
    REWRITE_TAC [IN_ELIM_THM, COMPLEX_SUB_REFL, REAL_SUB_REFL] THEN
    REWRITE_TAC [COMPLEX_NORM_CX] THEN REAL_ARITH_TAC)

  let ABEL_LIMIT_THEOREM_1 ← prove
   r"!M s a.
        summable s a /\ &0 < M
        ==> (!z. norm(z) < &1 ==> summable s (\i. a i * z pow i)) /\
            ((\z. infsum s (\i. a i * z pow i)) --> infsum s a)
            (at (Cx(&1)) within {z | norm(Cx(&1) - z) <= M * (&1 - norm z)})"
   (MP_TAC ABEL_LIMIT_THEOREM THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"Cx(&1)")) THEN
    REWRITE_TAC [COMPLEX_NORM_CX, REAL_ABS_NUM, COMPLEX_POW_ONE] THEN
    REWRITE_TAC [COMPLEX_MUL_RID, ETA_AX])

  pure { POWER_SERIES_UNIFORM_CONVERGENCE_STOLZ_1, POWER_SERIES_UNIFORM_CONVERGENCE_STOLZ,
         ABEL_POWER_SERIES_CONTINUOUS, ABEL_POWER_SERIES_CONTINUOUS_1, ABEL_LIMIT_THEOREM,
         ABEL_LIMIT_THEOREM_1 }

/- ------------------------------------------------------------------------- -/
/- Continuity and uniqueness of power series.  (canal.ml 3732-3925)         -/
/- ------------------------------------------------------------------------- -/

structure KNR where
  POWER_SERIES_CONTINUOUS : thm
  POWER_SERIES_LIMIT_POINT_OF_ZEROS : thm
  POWER_SERIES_UNIQUE : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupKNR [HolBase] (D : CanalDeps) (BKNC : KNC) (BKNM : KNM) (BKNO : KNO) : ExceptT String IO KNR := do
  -- @@SCOPE BEGIN
  let { CONTINUOUS_ON_COMPLEX_LMUL, CONTINUOUS_ON_COMPLEX_POW, SERIES_COMPLEX_RMUL,
        .. } := BKNC
  let { SERIES_COMPARISON_UNIFORM_COMPLEX, .. } := BKNM
  let { POWER_SERIES_CONV_IMP_ABSCONV, .. } := BKNO
  let { complex_div, complex_pow, .. } := D.cxa
  let { COMPLEX_MUL_ASSOC, COMPLEX_MUL_RID, COMPLEX_SUB_0, COMPLEX_SUB_RDISTRIB,
        COMPLEX_SUB_REFL, .. } := D.cxb
  let { COMPLEX_ENTIRE, COMPLEX_NORM_CX, COMPLEX_POW_EQ_0, COMPLEX_VEC_0, RE_CX,
        .. } := D.cxc
  let { COMPLEX_RING, .. } := D.cxd
  let { COMPLEX_DIV_EQ_0, COMPLEX_DIV_POW2, COMPLEX_NORM_MUL, COMPLEX_NORM_POW,
        .. } := D.cxf
  let { REAL_CX, .. } := D.cxi
  let { SERIES_RESTRICT, SERIES_SUB, SERIES_VSUM, summable, SUMS_REINDEX_GEN,
        .. } := D.qtopology
  let { LIMPT_INFINITE_CBALL, SERIES_UNIQUE, SUMS_EQ, .. } := D.ms.qtopology2
  let { ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON, MESON_TAC, NORM_ARITH,
        SET_RULE, .. } := D.cx.cvx
  let { ADD_CLAUSES, .. } := D.cx.cpx
  let { LE_EXISTS, .. } := D.ms.ig.qsession
  let { CONTINUOUS_UNIFORM_LIMIT, IN_CLOSURE_DELETE, .. } := D.ms.ig.qtopology
  let { ADD_SYM, FINITE_INTER, FINITE_NUMSEG, FINITE_SING, .. } := D.cx.cvx.core1
  let { IMAGE, IMP_CONJ, IN_DELETE, INTER_SUBSET, .. } := D.cx.cvx.core2
  let { IN_ELIM_THM, IN_INTER, IN_NUMSEG, IN_SING, IN_UNIV, LE_ADD, NOT_IMP, NOT_LE,
        REAL_ABS_MUL, .. } := D.cx.cvx.core3
  let { REAL_LE_LMUL, REAL_LT_MIN, .. } := D.cx.cvx.core4
  let { REAL_POW_LE2, RIGHT_IMP_EXISTS_THM, SING_SUBSET, SKOLEM_THM, SUBSET_TRANS,
        .. } := D.cx.cvx.core5
  let { num_WOP, .. } := D.cx.cvx.core6
  let { REAL_HALF, .. } := D.cx.cvx.misc
  let { DIST_REFL, DIST_SYM, .. } := D.cx.cvx.vec1
  let { NORM_POS_LE, REAL_ABS_NORM, .. } := D.cx.cvx.vec3
  let { dist, VSUM_SING, .. } := D.cx.cvx.vec4
  let { EVENTUALLY_SEQUENTIALLY, TRIVIAL_LIMIT_SEQUENTIALLY, .. } := D.cx.cvx.met
  let { BALL_MIN_INTER, CENTRE_IN_BALL, CLOSED_CBALL, CLOSED_SING, CLOSURE_CLOSED,
        .. } := D.cx.cvx.top1
  let { CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID, CONTINUOUS_ON_SUB, CONTINUOUS_ON_SUBSET,
        FORALL_IN_CLOSURE, .. } := D.cx.cvx.top3
  let { IN_BALL, IN_CBALL, INTERIOR_CBALL, LIM_SEQUENTIALLY, OPEN_BALL,
        .. } := D.cx.cvx.top4
  let { SUBSET_CLOSURE, .. } := D.cx.cvx.top5
  let { CONTINUOUS_ON_EQ_CONTINUOUS_AT, CONTINUOUS_ON_INTERIOR,
        .. } := D.ms.ig.dv.qtopology1
  let { sums, .. } := D.ms.ig.dv.qtopology2
  let { CBALL_MIN_INTER, CONTINUOUS_ON_VSUM, .. } := D.ms.ig.dv.dg.qtopology1
  let { SUBSET_BALLS, .. } := D.ms.ig.dv.dg.qtopology2
  let { INTER_ASSOC, .. } := D.ms.ig.dv.dg.pt.qses
  -- @@SCOPE END

  let POWER_SERIES_CONTINUOUS ← prove
   r"!a k f z r.
        (!w. w IN ball(z,r) ==> ((\n. a n * (w - z) pow n) sums f w) k)
        ==> f continuous_on ball(z,r)"
   (REWRITE_TAC [IN_BALL] THEN REPEAT STRIP_TAC THEN
    SIMP_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_AT, OPEN_BALL] THEN
    X_GEN_TAC (← q r"w:complex") THEN REWRITE_TAC [IN_BALL] THEN DISCH_TAC THEN
    ABBREV_TAC (← q r"R = (r + dist(z,w:complex)) / &2") THEN
    MATCH_MP_TAC CONTINUOUS_ON_INTERIOR THEN
    EXISTS_TAC (← q r"cball(z:complex,R)") THEN
    REWRITE_TAC [INTERIOR_CBALL, IN_BALL] THEN CONJ_TAC THENL
     [ALL_TAC,
      EXPAND_TAC "R" THEN UNDISCH_TAC (← q r"dist(z:complex,w) < r") THEN
      CONV_TAC (fun t => NORM_ARITH t)] THEN
    MATCH_MP_TAC (← ISPEC (← q r"sequentially") CONTINUOUS_UNIFORM_LIMIT) THEN
    EXISTS_TAC
     (← q r"\n w. vsum(k INTER (0..n)) (\i. (a:num->complex) i * (w - z) pow i)") THEN
    REWRITE_TAC [TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [REWRITE_TAC [EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC (← q r"1") THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
      SIMP_TAC [FINITE_INTER, FINITE_NUMSEG, IN_INTER, IN_NUMSEG] THEN
      X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_POW THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      REWRITE_TAC [CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID],
      ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"\w n. (a:num->complex) n * (w - z) pow n",
      ← q r"\n. Cx (norm (a n * Cx R pow n))",
      ← q r"\x:complex. x IN cball(z,R)",
      ← q r"k:num->bool"] SERIES_COMPARISON_UNIFORM_COMPLEX) THEN
    REWRITE_TAC [EVENTUALLY_SEQUENTIALLY, dist] THEN ANTS_TAC THENL
     [REWRITE_TAC [RE_CX, NORM_POS_LE, REAL_CX] THEN CONJ_TAC THENL
       [MATCH_MP_TAC POWER_SERIES_CONV_IMP_ABSCONV THEN
        EXISTS_TAC (← q r"Cx((r + R) / &2)") THEN CONJ_TAC THENL
         [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"z + Cx((r + R) / &2)")) THEN
          ANTS_TAC THENL
           [REWRITE_TAC [← NORM_ARITH (← q r"dist(z,z + r) = norm r")],
            REWRITE_TAC [summable,
              ← ExceptT.mk (COMPLEX_RING (← q r"(z + r) - z:complex = r"))] THEN
            MESON_TAC []],
          ALL_TAC] THEN
        REWRITE_TAC [COMPLEX_NORM_CX] THEN
        EXPAND_TAC "R" THEN UNDISCH_TAC (← q r"dist(z:complex,w) < r") THEN
        CONV_TAC (fun t => NORM_ARITH t),
        EXISTS_TAC (← q r"1") THEN REWRITE_TAC [IN_CBALL, dist] THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC [COMPLEX_NORM_MUL] THEN
        REWRITE_TAC [COMPLEX_NORM_CX, REAL_ABS_MUL, REAL_ABS_NORM] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [NORM_POS_LE] THEN
        REWRITE_TAC [COMPLEX_NORM_POW] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
        REWRITE_TAC [NORM_POS_LE, COMPLEX_NORM_CX] THEN
        UNDISCH_TAC (← q r"norm(z - x:complex) <= R") THEN CONV_TAC (fun t => NORM_ARITH t)],
      DISCH_THEN (X_CHOOSE_TAC (← q r"g:complex->complex")) THEN
      SUBGOAL_THEN (← q r"!x. x IN cball(z,R) ==> (f:complex->complex) x = g x")
      MP_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
      X_GEN_TAC (← q r"y:complex") THEN REWRITE_TAC [IN_CBALL] THEN DISCH_TAC THEN
      MATCH_MP_TAC SERIES_UNIQUE THEN
      EXISTS_TAC (← q r"\n. (a:num->complex) n * (y - z) pow n") THEN
      EXISTS_TAC (← q r"k:num->bool") THEN REWRITE_TAC [] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        FIRST_X_ASSUM (fun th => tactic_of do
          let _ ← SPEC (← q r"&0") th; pure ALL_TAC) THEN
        REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC (fun t => NORM_ARITH t),
        REWRITE_TAC [sums, LIM_SEQUENTIALLY, dist] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [IN_CBALL]) THEN ASM_MESON_TAC []]])

  let POWER_SERIES_LIMIT_POINT_OF_ZEROS ← prove
   r"!f c z k r s.
        &0 < r /\
        (!w. dist(w,z) < r ==> ((\i. c i * (w - z) pow i) sums f(w)) k) /\
        (!w. w IN s ==> f(w) = Cx(&0)) /\ z limit_point_of s
        ==> !i. i IN k ==> c(i) = Cx(&0)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC [← MESON [] (← q r"(!x. P x ==> Q x) <=> ~(?x. P x /\ ~Q x)")] THEN
    GEN_REWRITE_TAC RAND_CONV [num_WOP] THEN
    REWRITE_TAC [← TAUT (← q r"(p ==> ~(q /\ ~r)) <=> q /\ p ==> r")] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"m:num") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     (← q r"!w. w IN ball(z,r) /\ ~(w = z)
          ==> ((\i. c(m + i) * (w - z) pow i) sums f(w) / (w - z) pow m)
              {i | m + i IN k}")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUMS_EQ THEN
      EXISTS_TAC (← q r"\i. (c(m + i) * (w - z) pow (m + i)) / (w - z) pow m") THEN
      REWRITE_TAC [IN_ELIM_THM] THEN CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN
        REWRITE_TAC [complex_div, ← GSYM COMPLEX_MUL_ASSOC] THEN
        AP_TERM_TAC THEN REWRITE_TAC [← GSYM complex_div] THEN
        ASM_SIMP_TAC [COMPLEX_DIV_POW2, COMPLEX_SUB_0, LE_ADD] THEN
        AP_TERM_TAC THEN ARITH_TAC,
        REWRITE_TAC [complex_div] THEN
        MATCH_MP_TAC SERIES_COMPLEX_RMUL THEN
        MP_TAC (← ISPECL [← q r"m:num", ← q r"\i. (c:num->complex) i * (w - z) pow i",
                          ← q r"(f:complex->complex) w", ← q r"{i:num | m + i IN k}"]
          (← ONCE_REWRITE_RULE [ADD_SYM] SUMS_REINDEX_GEN)) THEN
        REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC [IMAGE, IN_ELIM_THM] THEN
        SUBGOAL_THEN (← q r"((\i. c i * (w - z) pow i) sums (f:complex->complex) w) k")
        MP_TAC THENL [ASM_MESON_TAC [IN_BALL, DIST_SYM], ALL_TAC] THEN
        ONCE_REWRITE_TAC [← GSYM SERIES_RESTRICT] THEN
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] SUMS_EQ) THEN
        X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_UNIV, IN_ELIM_THM] THEN
        REWRITE_TAC [← GSYM LE_EXISTS, ← MESON []
          (← q r"(?x. f x IN k /\ y = f x) <=> y IN k /\ (?x. y = f x)")] THEN
        ASM_CASES_TAC (← q r"(i:num) IN k") THEN ASM_REWRITE_TAC [] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [COMPLEX_VEC_0, COMPLEX_ENTIRE] THEN
        ASM_MESON_TAC [NOT_LE]],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"((\i. c(m + i) * (z - z) pow i) sums
       vsum {0} (\i. c(m + i) * (z - z) pow i))
      {i | m + i IN k}")
    MP_TAC THENL
     [MATCH_MP_TAC SERIES_VSUM THEN EXISTS_TAC (← q r"{0}") THEN
      REWRITE_TAC [FINITE_SING, SING_SUBSET, IN_ELIM_THM, IN_SING] THEN
      ASM_REWRITE_TAC [ADD_CLAUSES, COMPLEX_VEC_0, COMPLEX_ENTIRE] THEN
      SIMP_TAC [COMPLEX_SUB_REFL, COMPLEX_POW_EQ_0],
      REWRITE_TAC [VSUM_SING, complex_pow, ADD_CLAUSES, COMPLEX_MUL_RID] THEN
      DISCH_TAC] THEN
    SUBGOAL_THEN
     (← q r"!w. w IN ball(z,r)
          ==> summable {i | m + i IN k} (\i. c(m + i) * (w - z) pow i)")
    MP_TAC THENL
     [X_GEN_TAC (← q r"w:complex") THEN DISCH_TAC THEN REWRITE_TAC [summable] THEN
      ASM_CASES_TAC (← q r"w:complex = z") THEN ASM_MESON_TAC [],
      REWRITE_TAC [summable, RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"g:complex->complex"))] THEN
    SUBGOAL_THEN (← q r"(g:complex->complex) continuous_on ball(z,r)")
    ASSUME_TAC THENL
     [MATCH_MP_TAC POWER_SERIES_CONTINUOUS THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!x. x IN closure((s INTER cball(z,r / &2)) DELETE z)
          ==> (g:complex->complex) x IN {Cx(&0)}")
    MP_TAC THENL
     [MATCH_MP_TAC FORALL_IN_CLOSURE THEN REWRITE_TAC [CLOSED_SING, IN_SING] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        TRANS_TAC SUBSET_TRANS (← q r"closure(cball(z:complex,r / &2))") THEN
        SIMP_TAC [SUBSET_CLOSURE, INTER_SUBSET,
                  ← SET_RULE (← q r"s SUBSET t ==> (s DELETE z) SUBSET t")] THEN
        SIMP_TAC [CLOSURE_CLOSED, CLOSED_CBALL, SUBSET_BALLS, DIST_REFL] THEN
        ASM_REAL_ARITH_TAC,
        X_GEN_TAC (← q r"w:complex") THEN REWRITE_TAC [IN_INTER, IN_DELETE] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN (← q r"(g:complex->complex) w = f w / (w - z) pow m")
         (fun th => ASM_SIMP_TAC [COMPLEX_DIV_EQ_0, th]) THEN
        MATCH_MP_TAC SERIES_UNIQUE THEN
        EXISTS_TAC (← q r"\i. (c:num->complex) (m + i) * (w - z) pow i") THEN
        EXISTS_TAC (← q r"{i:num | m + i IN k}") THEN
        REWRITE_TAC [] THEN CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"w IN cball(z:complex,r / &2)") THEN
        REWRITE_TAC [IN_CBALL, IN_BALL] THEN ASM_REAL_ARITH_TAC],
      DISCH_THEN (MP_TAC o SPEC (← q r"z:complex")) THEN
      REWRITE_TAC [IN_CLOSURE_DELETE, NOT_IMP, IN_SING] THEN CONJ_TAC THENL
       [UNDISCH_TAC (← q r"(z:complex) limit_point_of s") THEN
        REWRITE_TAC [LIMPT_INFINITE_CBALL, INTER_ASSOC] THEN
        REWRITE_TAC [← GSYM CBALL_MIN_INTER] THEN
        DISCH_THEN (fun th => tactic_of do
          pure (X_GEN_TAC (← q r"e:real") THEN
                MP_TAC (← SPEC (← q r"min (r / &2) e") th))) THEN
        ASM_REWRITE_TAC [REAL_HALF, REAL_LT_MIN],
        SUBGOAL_THEN (← q r"(g:complex->complex) z = c(m:num)")
         (fun th => ASM_REWRITE_TAC [th]) THEN
        MATCH_MP_TAC SERIES_UNIQUE THEN
        EXISTS_TAC (← q r"\i. (c:num->complex) (m + i) * (z - z) pow i") THEN
        EXISTS_TAC (← q r"{i:num | m + i IN k}") THEN
        ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC [CENTRE_IN_BALL]]])

  let POWER_SERIES_UNIQUE ← prove
   r"!f g c d k r s t z.
        &0 < r /\ &0 < s /\
        (!w. w IN ball(z,r) ==> ((\i. c i * (w - z) pow i) sums f w) k) /\
        (!w. w IN ball(z,s) ==> ((\i. d i * (w - z) pow i) sums g w) k) /\
        (!w. w IN t ==> f w = g w) /\
        z limit_point_of t
        ==> (!i. i IN k ==> c i = d i)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM COMPLEX_SUB_0] THEN
    MATCH_MP_TAC POWER_SERIES_LIMIT_POINT_OF_ZEROS THEN
    MAP_EVERY EXISTS_TAC
     [← q r"\z. (f:complex->complex) z - g z", ← q r"z:complex", ← q r"min r s:real",
      ← q r"t:complex->bool"] THEN
    ONCE_REWRITE_TAC [DIST_SYM] THEN
    ASM_REWRITE_TAC [← GSYM IN_BALL, BALL_MIN_INTER, IN_INTER] THEN
    ASM_REWRITE_TAC [REAL_LT_MIN, COMPLEX_SUB_0] THEN
    REWRITE_TAC [COMPLEX_SUB_RDISTRIB] THEN
    ASM_SIMP_TAC [SERIES_SUB])

  pure { POWER_SERIES_CONTINUOUS, POWER_SERIES_LIMIT_POINT_OF_ZEROS, POWER_SERIES_UNIQUE }
/- ------------------------------------------------------------------------- -/
/- The only endomorphisms of C that are measurable or map R into R are the   -/
/- obvious ones.  (canal.ml 3926-4048)                                      -/
/- ------------------------------------------------------------------------- -/

structure KNS where
  MEASURABLE_COMPLEX_ENDOMORPHISM : thm
  REAL_COMPLEX_ENDOMORPHISM : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupKNS [HolBase] (D : CanalDeps) : ExceptT String IO KNS := do
  -- @@SCOPE BEGIN
  let { COMPLEX_EQ, .. } := D.cxa
  let { COMPLEX_ADD_LID, COMPLEX_MUL_LZERO, .. } := D.cxb
  let { COMPLEX_CMUL, COMPLEX_EXPAND, COMPLEX_MUL_LINV, CX_ADD, CX_INJ, CX_INV, CX_MUL,
        CX_NEG, IM_CX, RE_ADD, RE_CX, RE_MUL_CX, .. } := D.cxc
  let { COMPLEX_RING, .. } := D.cxd
  let { COMPLEX_FIELD, .. } := D.cxe
  let { CNJ_ADD, CNJ_CNJ, CNJ_CX, CNJ_II, CNJ_MUL, .. } := D.cxg
  let { LINEAR_CNJ, .. } := D.cxh
  let { REAL, real, REAL_CNJ, REAL_CX, REAL_NEG, .. } := D.cxi
  let { LINEAR_I, .. } := D.qvectors
  let { REAL_POS_EQ_SQUARE, .. } := D.qsession
  let { CONTINUOUS_IMP_MEASURABLE_ON, MEASURABLE_ADDITIVE_IMP_LINEAR, MEASURABLE_ON_CONST,
        .. } := D.qmeasure
  let { FORALL_INTEGER, rational, .. } := D.qfloor
  let { RATIONAL_BETWEEN, .. } := D.ms.qfloor
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INDUCT_TAC, MESON, REAL_ARITH, REAL_RING,
        .. } := D.cx.cvx
  let { REAL_LE_SQUARE, .. } := D.cx.cpx
  let { EQ_SYM_EQ, .. } := D.cx.cvx.core1
  let { FORALL_IN_IMAGE, FUN_EQ_THM, IN, .. } := D.cx.cvx.core2
  let { I_THM, LEFT_IMP_EXISTS_THM, MONO_OR, NOT_FORALL_THM, .. } := D.cx.cvx.core3
  let { REAL_LE_ADDR, REAL_LT_IMP_LE, .. } := D.cx.cvx.core4
  let { REAL_OF_NUM_SUC, REAL_SUB_LE, SUBSET, .. } := D.cx.cvx.core5
  let { real_div, .. } := D.cx.cvx.core6
  let { linear, .. } := D.cx.cvx.vec4
  let { LINEAR_CONTINUOUS_ON, .. } := D.cx.cvx.top4
  -- @@SCOPE END

  let MEASURABLE_COMPLEX_ENDOMORPHISM ← prove
   r"!f:complex->complex.
        f measurable_on (:complex) /\
        (!x y. f(x + y) = f x + f y) /\
        (!x y. f(x * y) = f x * f y) <=>
        f = (\x. Cx(&0)) \/ f = I \/ f = cnj"
   (GEN_TAC THEN EQ_TAC THENL
     [STRIP_TAC,
      STRIP_TAC THEN
      ASM_REWRITE_TAC [MEASURABLE_ON_CONST, COMPLEX_MUL_LZERO, COMPLEX_ADD_LID,
                       I_THM, CNJ_ADD, CNJ_MUL] THEN
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
      REWRITE_TAC [LINEAR_CNJ, LINEAR_I]] THEN
    SUBGOAL_THEN (← q r"linear(f:complex->complex)") ASSUME_TAC THENL
     [ASM_MESON_TAC [MEASURABLE_ADDITIVE_IMP_LINEAR], ALL_TAC] THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"p \/ q <=> ~p ==> q")] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"!x. real x ==> f x = x") ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [FUN_EQ_THM]) THEN
      REWRITE_TAC [NOT_FORALL_THM, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"z:complex") THEN STRIP_TAC THEN
      X_GEN_TAC (← q r"x:complex") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [linear]) THEN
      DISCH_THEN (MP_TAC o CONJUNCT2) THEN REWRITE_TAC [COMPLEX_CMUL] THEN
      DISCH_THEN (MP_TAC o SPECL [← q r"Re x", ← q r"z:complex"]) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [REAL]) THEN
      ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC (← q r"~(f(z:complex) = Cx(&0))") THEN CONV_TAC COMPLEX_RING,
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"f(ii) = ii \/ f(ii) = --ii") MP_TAC THENL
     [REWRITE_TAC [← ExceptT.mk (COMPLEX_RING
        (← q r"z = ii \/ z = --ii <=> z * z = --Cx(&1)"))] THEN
      ASM_MESON_TAC [REAL_NEG, REAL_CX,
        ← ExceptT.mk (COMPLEX_RING (← q r"ii * ii = --Cx(&1)"))],
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_OR THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"z:complex") THEN
    SUBST1_TAC (← SPEC (← q r"z:complex") COMPLEX_EXPAND) THEN
    ASM_REWRITE_TAC [I_THM, CNJ_ADD, CNJ_MUL, CNJ_CX, CNJ_II] THEN
    ASM_MESON_TAC [REAL_CX])

  let REAL_COMPLEX_ENDOMORPHISM ← prove
   r"!f:complex->complex.
        IMAGE f real SUBSET real /\
        (!x y. f(x + y) = f x + f y) /\
        (!x y. f(x * y) = f x * f y) <=>
        f = (\x. Cx(&0)) \/ f = I \/ f = cnj"
   (GEN_TAC THEN EQ_TAC THENL
     [STRIP_TAC,
      STRIP_TAC THEN
      ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, COMPLEX_MUL_LZERO, COMPLEX_ADD_LID,
                       I_THM, CNJ_ADD, CNJ_MUL] THEN
      REWRITE_TAC [IN, CNJ_CNJ, REAL_CX, REAL_CNJ, EQ_SYM_EQ]] THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"p \/ q <=> ~p ==> q")] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"!x. real x ==> f x = x") ASSUME_TAC THENL
     [SUBGOAL_THEN (← q r"!n. f(Cx(&n)) = Cx(&n)") ASSUME_TAC THENL
       [INDUCT_TAC THENL
         [ASM_MESON_TAC [← ExceptT.mk (COMPLEX_RING
            (← q r"z = Cx(&0) <=> z + w = w"))],
          ASM_REWRITE_TAC [← GSYM REAL_OF_NUM_SUC, CX_ADD] THEN
          FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [FUN_EQ_THM]) THEN
          REWRITE_TAC [NOT_FORALL_THM, LEFT_IMP_EXISTS_THM] THEN
          X_GEN_TAC (← q r"z:complex") THEN STRIP_TAC THEN AP_TERM_TAC THEN
          ASM_MESON_TAC [← ExceptT.mk (COMPLEX_RING
            (← q r"w * z = w <=> w = Cx(&0) \/ z = Cx(&1)"))]],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!z. (f:complex->complex) (--z) = --(f z)") ASSUME_TAC THENL
       [ASM_MESON_TAC [← ExceptT.mk (COMPLEX_RING
          (← q r"w = --z <=> w + z = Cx(&0)"))],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!z. ~(z = Cx(&0)) ==> (f:complex->complex) (inv z) = inv(f z)")
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN MATCH_MP_TAC (← ExceptT.mk (COMPLEX_FIELD
         (← q r"z * w = Cx(&1) ==> z = inv w"))) THEN
        ASM_MESON_TAC [COMPLEX_MUL_LINV],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!q. rational q ==> f(Cx q) = Cx q") ASSUME_TAC THENL
       [ASM_REWRITE_TAC [rational, LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [← q r"q:real", ← q r"m:real", ← q r"n:real"] THEN
        STRIP_TAC THEN ASM_SIMP_TAC [real_div, CX_MUL, CX_INV, CX_INJ] THEN
        BINOP_TAC THENL
         [UNDISCH_TAC (← q r"integer m") THEN SPEC_TAC (← q r"m:real", ← q r"y:real"),
          AP_TERM_TAC THEN UNDISCH_TAC (← q r"integer n") THEN
          SPEC_TAC (← q r"n:real", ← q r"y:real")] THEN
        MATCH_MP_TAC FORALL_INTEGER THEN ASM_SIMP_TAC [CX_NEG],
        ALL_TAC] THEN
      MATCH_MP_TAC (← MESON [REAL]
        (← q r"(!x. P(Cx x)) ==> (!x. real x ==> P x)")) THEN
      SUBGOAL_THEN (← q r"!x y. x <= y ==> Re(f(Cx x)) <= Re(f(Cx y))") ASSUME_TAC THENL
       [REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM REAL_SUB_LE] THEN
        REWRITE_TAC [REAL_POS_EQ_SQUARE, LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC (← q r"z:real") THEN
        REWRITE_TAC [← REAL_RING (← q r"z pow 2 = y - x <=> y:real = x + z * z")] THEN
        DISCH_THEN SUBST1_TAC THEN
        ASM_REWRITE_TAC [CX_ADD, CX_MUL, RE_ADD, REAL_LE_ADDR] THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
        REWRITE_TAC [FORALL_IN_IMAGE] THEN DISCH_THEN (MP_TAC o SPEC (← q r"Cx z")) THEN
        REWRITE_TAC [IN, REAL_CX] THEN REWRITE_TAC [REAL] THEN
        DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [RE_MUL_CX, RE_CX] THEN
        REWRITE_TAC [REAL_LE_SQUARE],
        ALL_TAC] THEN
      X_GEN_TAC (← q r"x:real") THEN REWRITE_TAC [COMPLEX_EQ, RE_CX, IM_CX] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      REWRITE_TAC [FORALL_IN_IMAGE] THEN DISCH_THEN (MP_TAC o SPEC (← q r"Cx x")) THEN
      REWRITE_TAC [IN, REAL_CX] THEN SIMP_TAC [real] THEN DISCH_TAC THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"~(x < y) /\ ~(y < x) ==> x:real = y")) THEN
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP RATIONAL_BETWEEN) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"q:real") STRIP_ASSUME_TAC) THENL
       [FIRST_X_ASSUM (MP_TAC o SPECL [← q r"q:real", ← q r"x:real"]),
        FIRST_X_ASSUM (MP_TAC o SPECL [← q r"x:real", ← q r"q:real"])] THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE, RE_CX] THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"f(ii) = ii \/ f(ii) = --ii") MP_TAC THENL
     [REWRITE_TAC [← ExceptT.mk (COMPLEX_RING
        (← q r"z = ii \/ z = --ii <=> z * z = --Cx(&1)"))] THEN
      ASM_MESON_TAC [REAL_NEG, REAL_CX,
        ← ExceptT.mk (COMPLEX_RING (← q r"ii * ii = --Cx(&1)"))],
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_OR THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"z:complex") THEN
    SUBST1_TAC (← SPEC (← q r"z:complex") COMPLEX_EXPAND) THEN
    ASM_REWRITE_TAC [I_THM, CNJ_ADD, CNJ_MUL, CNJ_CX, CNJ_II] THEN
    ASM_MESON_TAC [REAL_CX])

  pure { MEASURABLE_COMPLEX_ENDOMORPHISM, REAL_COMPLEX_ENDOMORPHISM }

end HolMultiLib.Canal
