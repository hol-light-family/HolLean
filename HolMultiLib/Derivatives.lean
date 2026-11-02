/- ========================================================================= -/
/- Multivariate calculus in Euclidean space.                                 -/
/- ========================================================================= -/
/- File: HolMultiLib/Derivatives.lean

  Original (c) Copyright, John Harrison 1998-2008.
  (c) Copyright, Marco Maggesi 2014.
  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/derivatives.ml`, in the style of
  HolMultiLib/Degree.lean: pure, the proofs translated by hand, one `let` per
  OCaml `let`, in file order.  The load-time effects are at their file
  positions.  What derivatives.ml uses from earlier files is passed in
  `DerivativesDeps`: everything degree.ml already used comes in its
  `DegreeDeps` (field `dg`), and the rest in the Q*Thms groups.
  SessionMultiLib/Derivatives.lean supplies it.
-/

import HolMultiLib.Degree

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolMultiLib.Derivatives

open HolMultiLib.Degree (DegreeDeps)

/- The theorems derivatives.ml uses that degree.ml's deps do not carry,
   grouped by the file that proves them. -/

structure QConvexThms where
  (AFFINE_DIFFS_SUBSPACE CONNECTED_BALL CONNECTED_CBALL CONNECTED_INTERVAL
   CONVEX_ON_LEFT_SECANT LIMIT_POINT_OF_INTERVAL LINEAR_CLOSEST_POINT
   SEGMENT_IMAGE_INTERVAL convex_on : thm)
  deriving Inhabited

structure QDegreeThms where
  (BROUWER HOMOTOPIC_LINEAR_MAPS_IMP : thm)
  deriving Inhabited

structure QDetThms where
  (DET_MATRIX_EQ_0 DET_MATRIX_EQ_0_RIGHT det : thm)
  deriving Inhabited

structure QMetricThms where
  (ALWAYS_EVENTUALLY ARCH_EVENTUALLY_INV1 EVENTUALLY_MP SEQUENTIALLY : thm)
  deriving Inhabited

structure QMiscThms where
  (FINITE_INTER_NUMSEG : thm)
  deriving Inhabited

structure QPathsThms where
  (CLOSED_LOCAL_HOMEOMORPHISM_GLOBAL CONNECTED_INFINITE_IFF_CARD_EQ
   CONNECTED_OPEN_PATH_CONNECTED CONTINUOUS_IVT_LOCAL_EXTREMUM path_connected : thm)
  deriving Inhabited

structure QPermutationsThms where
  (FINITE_PERMUTATIONS PERMUTES_IMAGE : thm)
  deriving Inhabited

structure QSessionThms where
  (INFINITE INJECTIVE_ON_LEFT_INVERSE REAL_ABS_ABS REAL_ABS_NZ REAL_INV_INV
   REAL_LE_LCANCEL_IMP REAL_LE_SUB_RADD REAL_LE_SUP REAL_LE_TRANS_LTE REAL_LT_MUL2
   REAL_LT_RMUL_EQ REAL_POW_MONO_INV RESTRICTION : thm)
  deriving Inhabited

structure QTopologyThms1 where
  (BAIRE_CMUL BAIRE_COMPONENTWISE BAIRE_EQ BAIRE_PRODUCT BAIRE_VSUM BILINEAR_DOT
   CBALL_DIFF_BALL CLOSED_LIMPT CLOSURE_NONEMPTY_OPEN_INTER CLOSURE_PCROSS
   COMPONENTS_NONOVERLAP CONNECTED_CARD_EQ_IFF_NONTRIVIAL
   CONNECTED_COMPONENT_IN_COMPONENTS CONNECTED_COMPONENT_REFL CONNECTED_HAUSDIST_LIMIT
   CONNECTED_PCROSS_EQ CONTINUOUS_AT CONTINUOUS_AT_WITHIN CONTINUOUS_AT_WITHIN_INV
   CONTINUOUS_LIFT_POW CONTINUOUS_ON_EQ_CONTINUOUS_AT CONTINUOUS_ON_INTERIOR
   CONTINUOUS_ON_INTERMEDIATE_CLOSURE CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE
   CONTINUOUS_ON_SEQUENTIALLY CONTINUOUS_ON_VMUL CONTINUOUS_OPEN_PREIMAGE
   CONTINUOUS_PASTECART CONTINUOUS_WITHIN_COMPOSE CONVERGENT_EQ_CAUCHY
   CONVERGENT_IMP_CAUCHY DISCRETE_EQ_FINITE_COMPACT DISCRETE_IMP_COUNTABLE DISCRETE_SET
   EVENTUALLY_AT_TOPOLOGICAL EVENTUALLY_AT_ZERO EVENTUALLY_WITHIN_TOPOLOGICAL
   EXISTS_COMPONENT_SUPERSET FRONTIER_OPEN_MAP_IMAGE_SUBSET
   HAUSDIST_UNIFORMLY_CONTINUOUS_ON HOMEOMORPHISM_EQ IMAGE_CLOSURE_SUBSET
   LIMIT_POINT_OF_IMAGE LIMPT_OF_UNIV LIMPT_SEQUENTIAL LIMPT_SUBSET LIM_AT LIM_BILINEAR
   LIM_COMPONENT : thm)
  deriving Inhabited

structure QTopologyThms2 where
  (LIM_COMPONENTWISE_LIFT LIM_COMPOSE_AT LIM_COMPOSE_WITHIN LIM_CONTINUOUS_SELF_WITHIN
   LIM_DROP_LBOUND LIM_DROP_LE LIM_EVENTUALLY LIM_INV LIM_LIFT_DET LIM_LIFT_DOT
   LIM_LINEAR LIM_MATRIX_COMPONENTWISE LIM_MATRIX_INV LIM_NORM_UBOUND LIM_NULL
   LIM_NULL_CMUL LIM_NULL_NEG LIM_NULL_NORM LIM_NULL_SUB LIM_NULL_VMUL LIM_PASTECART_EQ
   LIM_TRANSFORM LIM_TRANSFORM_EQ LIM_TRANSFORM_EVENTUALLY LIM_TRANSFORM_WITHIN
   LIM_TRANSFORM_WITHIN_OPEN LIM_TRIVIAL LIM_VMUL LIM_WITHIN_ID LIM_WITHIN_OPEN
   LIM_WITHIN_OPEN_IN LIM_WITHIN_SUBSET LINEAR_CONTINUOUS_WITHIN
   LOCALLY_CONSTANT_IMP_CONSTANT NETLIMIT_WITHIN ONORM_LE_EVENTUALLY
   OPEN_IN_TRANSLATION_EQ OPEN_PCROSS OPEN_UNION SEQ_HARMONIC_OFFSET
   SUBSET_COMPACT_HAUSDIST_LIMIT SUBSET_INTERIOR_EQ TRIVIAL_LIMIT_AT WITHIN_UNIV baire
   cauchy open_def sums : thm)
  deriving Inhabited

structure QVecThms where
  (BILINEAR_BOUNDED_POS BILINEAR_DROP_MUL BILINEAR_LADD BILINEAR_LMUL BILINEAR_LSUB
   BILINEAR_LZERO BILINEAR_RADD BILINEAR_RMUL BILINEAR_RSUB BILINEAR_RZERO DROP_BASIS
   FORALL_DIMINDEX_1 FORALL_DOT_EQ_0 IN_TRANSLATION_GALOIS LINEAR_BOUNDED_POS
   LINEAR_COMPONENTWISE LINEAR_COMPOSE_CMUL LINEAR_COMPOSE_SUB LINEAR_EQ_STDBASIS
   LINEAR_FROM_REALS LINEAR_INJECTIVE_BOUNDED_BELOW_POS
   LINEAR_INJECTIVE_IMP_SURJECTIVE_ON LINEAR_INVERTIBLE_BOUNDED_BELOW_POS LINEAR_NEG
   LINEAR_PASTECART_EQ LINEAR_SURJECTIVE_RIGHT_INVERSE_EQ LINEAR_VMUL_COMPONENT
   LINEAR_VMUL_DROP MATRIX_COMPONENT MATRIX_INVERTIBLE_LEFT MATRIX_INVERTIBLE_RIGHT
   MATRIX_INV_UNIQUE_LEFT MATRIX_VECTOR_MUL_COMPONENT NORM_LT_SQUARE NORM_PASTECART_LE
   NORM_TRIANGLE_SUB ONORM ONORM_COMPOSE ONORM_CONST ONORM_NEG ONORM_POS_LT
   PASTECART_SUB REFLECT_UNIV RIGHT_INVERSE_LINEAR TRANSLATION_SUBSET_GALOIS_LEFT
   TRANSP_COMPONENT VECTOR_EQ_ADDR VECTOR_NEG_MINUS1 matrix transp : thm)
  deriving Inhabited

structure DerivativesDeps where
  prioritize_real : IO Unit
  dg : DegreeDeps
  -- procedures degree.ml's deps do not carry
  FIX_TAC : String → tactic
  HYP_TAC : String → (thm → ExceptT String IO thm) → tactic
  CLAIM_TAC : String → term → tactic
  -- theorems
  qconvex : QConvexThms
  qdegree : QDegreeThms
  qdet : QDetThms
  qmetric : QMetricThms
  qmisc : QMiscThms
  qpaths : QPathsThms
  qpermutations : QPermutationsThms
  qsession : QSessionThms
  qtopology1 : QTopologyThms1
  qtopology2 : QTopologyThms2
  qvec : QVecThms

/- ------------------------------------------------------------------------- -/
/- Derivatives over nets, combining theorems, differentiability, Frechet     -/
/- derivative and Jacobian matrix.  (derivatives.ml 1-405)                   -/
/- ------------------------------------------------------------------------- -/

structure DVA where
  has_derivative : thm
  has_derivative_within : thm
  has_derivative_at : thm
  HAS_DERIVATIVE_WITHIN : thm
  HAS_DERIVATIVE_AT : thm
  HAS_DERIVATIVE_AT_WITHIN : thm
  HAS_DERIVATIVE_WITHIN_OPEN : thm
  HAS_DERIVATIVE_WITHIN_OPEN_IN : thm
  HAS_DERIVATIVE_LINEAR : thm
  HAS_DERIVATIVE_ID : thm
  HAS_DERIVATIVE_CONST : thm
  HAS_DERIVATIVE_LIFT_COMPONENT : thm
  HAS_DERIVATIVE_CMUL : thm
  HAS_DERIVATIVE_CMUL_EQ : thm
  HAS_DERIVATIVE_NEG : thm
  HAS_DERIVATIVE_NEG_EQ : thm
  HAS_DERIVATIVE_ADD : thm
  HAS_DERIVATIVE_SUB : thm
  HAS_DERIVATIVE_VSUM : thm
  HAS_DERIVATIVE_VSUM_NUMSEG : thm
  HAS_DERIVATIVE_COMPONENTWISE_WITHIN : thm
  HAS_DERIVATIVE_COMPONENTWISE_AT : thm
  HAS_DERIVATIVE_PASTECART_EQ : thm
  HAS_DERIVATIVE_PASTECART : thm
  HAS_DERIVATIVE_VMUL_COMPONENT : thm
  HAS_DERIVATIVE_VMUL_DROP : thm
  HAS_DERIVATIVE_LIFT_DOT : thm
  HAS_DERIVATIVE_TRANSFORM_WITHIN : thm
  HAS_DERIVATIVE_TRANSFORM_AT : thm
  HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN : thm
  differentiable : thm
  differentiable_on : thm
  HAS_DERIVATIVE_IMP_DIFFERENTIABLE : thm
  DIFFERENTIABLE_AT_WITHIN : thm
  DIFFERENTIABLE_WITHIN_OPEN : thm
  DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON : thm
  DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT : thm
  DIFFERENTIABLE_TRANSFORM_WITHIN : thm
  DIFFERENTIABLE_TRANSFORM_AT : thm
  DIFFERENTIABLE_ON_EQ : thm
  frechet_derivative : thm
  FRECHET_DERIVATIVE_WORKS : thm
  LINEAR_FRECHET_DERIVATIVE : thm
  jacobian : thm
  JACOBIAN_WORKS : thm
  deriving Inhabited

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
@[nospecialize]
def setupDVA [HolBase] (D : DerivativesDeps) : ExceptT String IO DVA := do
  -- @@SCOPE BEGIN
  let { AND_FORALL_THM, CONJ_ACI, DIMINDEX_1, EQ_IMP, ETA_AX, FINITE_INDUCT_STRONG,
        FINITE_NUMSEG, .. } := D.dg.pt.cvx.core1
  let { IMP_CONJ, .. } := D.dg.pt.cvx.core2
  let { IN_INSERT, IN_NUMSEG, IN_UNIV, LE_REFL, MONO_FORALL, MONO_IMP, REAL_ABS_INV,
        REAL_ABS_MUL, REAL_ABS_POS, .. } := D.dg.pt.cvx.core3
  let { REAL_LE_LMUL, REAL_LET_TRANS, REAL_LT_01, .. } := D.dg.pt.cvx.core4
  let { REAL_MUL_AC, REAL_MUL_LINV, .. } := D.dg.pt.cvx.core5
  let { o_DEF, o_THM, real_div, .. } := D.dg.pt.cvx.core6
  let { COMPONENT_LE_NORM, DIST_REFL, DOT_RADD, DOT_RMUL, DOT_RSUB, DOT_RZERO, .. } :=
        D.dg.pt.cvx.vec1
  let { LIFT_ADD, LIFT_CMUL, LIFT_NUM, LIFT_SUB, LINEAR_COMPOSE, LINEAR_COMPOSE_ADD,
        LINEAR_LIFT_DOT, MATRIX_WORKS, .. } := D.dg.pt.cvx.vec2
  let { NORM_LIFT, NORM_MUL, PASTECART_ADD, PASTECART_CMUL, PASTECART_VEC, REAL_ABS_NORM, ..
        } := D.dg.pt.cvx.vec3
  let { dist, drop, linear, VEC_COMPONENT, VECTOR_ADD_COMPONENT, VECTOR_ADD_LID,
        VECTOR_ADD_RDISTRIB, VECTOR_ADD_RID, VECTOR_MUL_ASSOC, VECTOR_MUL_COMPONENT,
        VECTOR_MUL_LID, VECTOR_MUL_RZERO, VECTOR_NEG_NEG, VECTOR_SUB, VECTOR_SUB_COMPONENT,
        VECTOR_SUB_RDISTRIB, VECTOR_SUB_REFL, VECTOR_SUB_RZERO, VSUM_CLAUSES, .. } :=
        D.dg.pt.cvx.vec4
  let { EVENTUALLY_MONO, .. } := D.dg.pt.cvx.met
  let { LIM_ADD, LIM_CMUL, LIM_CONST, LIM_WITHIN, .. } := D.dg.pt.cvx.top4
  let { ASM_MESON_TAC, MESON_TAC, new_definition, parse_as_infix, SELECT_CONV, VECTOR_ARITH,
        VECTOR_ARITH_TAC, .. } := D.dg.pt.cvx
  let { tendsto, .. } := D.dg.qtopology2
  let { LINEAR_ID, .. } := D.dg.qvec
  let { LIM_COMPONENTWISE_LIFT, LIM_LIFT_DOT, LIM_PASTECART_EQ, LIM_TRANSFORM_WITHIN,
        LIM_TRANSFORM_WITHIN_OPEN, LIM_TRIVIAL, LIM_VMUL, LIM_WITHIN_OPEN,
        LIM_WITHIN_OPEN_IN, NETLIMIT_WITHIN, WITHIN_UNIV, .. } := D.qtopology2
  let { LINEAR_COMPONENTWISE, LINEAR_COMPOSE_CMUL, LINEAR_PASTECART_EQ,
        LINEAR_VMUL_COMPONENT, PASTECART_SUB, VECTOR_NEG_MINUS1, .. } := D.qvec
  -- @@SCOPE END

  D.prioritize_real

  parse_as_infix ("has_derivative", (12, "right"))

  let has_derivative ← new_definition
   r"(f has_derivative f') net <=>
        linear f' /\
        ((\y. inv(norm(y - netlimit net)) %
              (f(y) -
               (f(netlimit net) + f'(y - netlimit net)))) --> vec 0) net"

  let has_derivative_within ← prove
   r"!f:real^M->real^N f' x s.
    (f has_derivative f') (at x within s) <=>
         linear f' /\
         ((\y. inv(norm(y - x)) % (f(y) - (f(x) + f'(y - x)))) --> vec 0)
         (at x within s)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [has_derivative] THEN AP_TERM_TAC THEN
    ASM_CASES_TAC (← q r"trivial_limit(at (x:real^M) within s)") THEN
    ASM_SIMP_TAC [LIM_TRIVIAL, NETLIMIT_WITHIN])

  let has_derivative_at ← prove
   r"!f:real^M->real^N f' x.
    (f has_derivative f') (at x) <=>
         linear f' /\
         ((\y. inv(norm(y - x)) % (f(y) - (f(x) + f'(y - x)))) --> vec 0)
         (at x)"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    REWRITE_TAC [has_derivative_within])

  let HAS_DERIVATIVE_WITHIN ← prove
   r"(f has_derivative f')(at x within s) <=>
        linear f' /\
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x'. x' IN s /\
                         &0 < norm(x' - x) /\ norm(x' - x) < d
                         ==> norm(f(x') - f(x) - f'(x' - x)) /
                             norm(x' - x) < e"
   (SIMP_TAC [has_derivative_within, LIM_WITHIN] THEN AP_TERM_TAC THEN
    REWRITE_TAC [dist, ← VECTOR_ARITH (← q r"(x' - (x + d)) = x' - x - d:real^N")] THEN
    REWRITE_TAC [real_div, VECTOR_SUB_RZERO, NORM_MUL] THEN
    REWRITE_TAC [REAL_MUL_AC, REAL_ABS_INV, REAL_ABS_NORM])

  let HAS_DERIVATIVE_AT ← prove
   r"(f has_derivative f')(at x) <=>
        linear f' /\
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x'. &0 < norm(x' - x) /\ norm(x' - x) < d
                         ==> norm(f(x') - f(x) - f'(x' - x)) /
                             norm(x' - x) < e"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    REWRITE_TAC [HAS_DERIVATIVE_WITHIN, IN_UNIV])

  let HAS_DERIVATIVE_AT_WITHIN ← prove
   r"!f x s. (f has_derivative f') (at x)
           ==> (f has_derivative f') (at x within s)"
   (REWRITE_TAC [HAS_DERIVATIVE_WITHIN, HAS_DERIVATIVE_AT] THEN MESON_TAC [])

  let HAS_DERIVATIVE_WITHIN_OPEN ← prove
   r"!f f' a s.
         a IN s /\ open s
         ==> ((f has_derivative f') (at a within s) <=>
              (f has_derivative f') (at a))"
   (SIMP_TAC [has_derivative_within, has_derivative_at, LIM_WITHIN_OPEN])

  let HAS_DERIVATIVE_WITHIN_OPEN_IN ← prove
   r"!f:real^M->real^N f' a s u.
        a IN s /\ open_in (subtopology euclidean u) s
        ==> ((f has_derivative f') (at a within s) <=>
             (f has_derivative f') (at a within u))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [has_derivative_within] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC LIM_WITHIN_OPEN_IN THEN ASM_REWRITE_TAC [])

  let HAS_DERIVATIVE_LINEAR ← prove
   r"!f net. linear f ==> (f has_derivative f) net"
   (REWRITE_TAC [has_derivative, linear] THEN
    SIMP_TAC [← VECTOR_ARITH (← q r"x - y = x + --(&1) % y")] THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"x + --(&1) % (y + x + --(&1) % y) = vec 0")] THEN
    REWRITE_TAC [VECTOR_MUL_RZERO, LIM_CONST])

  let HAS_DERIVATIVE_ID ← prove
   r"!net. ((\x. x) has_derivative (\h. h)) net"
   (SIMP_TAC [HAS_DERIVATIVE_LINEAR, LINEAR_ID])

  let HAS_DERIVATIVE_CONST ← prove
   r"!c net. ((\x. c) has_derivative (\h. vec 0)) net"
   (REPEAT GEN_TAC THEN REWRITE_TAC [has_derivative, linear] THEN
    REWRITE_TAC [VECTOR_ADD_RID, VECTOR_SUB_REFL, VECTOR_MUL_RZERO, LIM_CONST])

  let HAS_DERIVATIVE_LIFT_COMPONENT ← prove
   r"!net:(real^N)net. ((\x. lift(x$i)) has_derivative (\x. lift(x$i))) net"
   (GEN_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC [linear, VECTOR_MUL_COMPONENT, VECTOR_ADD_COMPONENT] THEN
    REWRITE_TAC [LIFT_ADD, LIFT_CMUL])

  let HAS_DERIVATIVE_CMUL ← prove
   r"!f f' net c. (f has_derivative f') net
                ==> ((\x. c % f(x)) has_derivative (\h. c % f'(h))) net"
   (REPEAT GEN_TAC THEN SIMP_TAC [has_derivative, LINEAR_COMPOSE_CMUL] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"c:real") o MATCH_MP LIM_CMUL o CONJUNCT2) THEN
    REWRITE_TAC [VECTOR_MUL_RZERO] THEN
    MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN VECTOR_ARITH_TAC)

  let HAS_DERIVATIVE_CMUL_EQ ← prove
   r"!f f' net c.
       ~(c = &0)
       ==> (((\x. c % f(x)) has_derivative (\h. c % f'(h))) net <=>
            (f has_derivative f') net)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP HAS_DERIVATIVE_CMUL) THENL
     [DISCH_THEN (MP_TAC o SPEC (← q r"inv(c):real")),
      DISCH_THEN (MP_TAC o SPEC (← q r"c:real"))] THEN
    ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, VECTOR_MUL_LID, ETA_AX])

  let HAS_DERIVATIVE_NEG ← prove
   r"!f f' net. (f has_derivative f') net
            ==> ((\x. --(f(x))) has_derivative (\h. --(f'(h)))) net"
   (ONCE_REWRITE_TAC [VECTOR_NEG_MINUS1] THEN
    SIMP_TAC [HAS_DERIVATIVE_CMUL])

  let HAS_DERIVATIVE_NEG_EQ ← prove
   r"!f f' net. ((\x. --(f(x))) has_derivative (\h. --(f'(h)))) net <=>
              (f has_derivative f') net"
   (REPEAT GEN_TAC THEN EQ_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP HAS_DERIVATIVE_NEG) THEN
    REWRITE_TAC [VECTOR_NEG_NEG, ETA_AX])

  let HAS_DERIVATIVE_ADD ← prove
   r"!f f' g g' net.
        (f has_derivative f') net /\ (g has_derivative g') net
        ==> ((\x. f(x) + g(x)) has_derivative (\h. f'(h) + g'(h))) net"
   (REPEAT GEN_TAC THEN SIMP_TAC [has_derivative, LINEAR_COMPOSE_ADD] THEN
    DISCH_THEN (MP_TAC o MATCH_MP (← TAUT (← q r"(a /\ b) /\ (c /\ d) ==> b /\ d"))) THEN
    DISCH_THEN (MP_TAC o MATCH_MP LIM_ADD) THEN REWRITE_TAC [VECTOR_ADD_LID] THEN
    MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN VECTOR_ARITH_TAC)

  let HAS_DERIVATIVE_SUB ← prove
   r"!f f' g g' net.
        (f has_derivative f') net /\ (g has_derivative g') net
        ==> ((\x. f(x) - g(x)) has_derivative (\h. f'(h) - g'(h))) net"
   (SIMP_TAC [VECTOR_SUB, HAS_DERIVATIVE_ADD, HAS_DERIVATIVE_NEG])

  let HAS_DERIVATIVE_VSUM ← prove
   r"!f net s.
     FINITE s /\
     (!a. a IN s ==> ((f a) has_derivative (f' a)) net)
     ==> ((\x. vsum s (\a. f a x)) has_derivative (\h. vsum s (\a. f' a h)))
          net"
   (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [VSUM_CLAUSES, HAS_DERIVATIVE_CONST] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
    REWRITE_TAC [ETA_AX] THEN ASM_SIMP_TAC [IN_INSERT])

  let HAS_DERIVATIVE_VSUM_NUMSEG ← prove
   r"!f net m n.
     (!i. m <= i /\ i <= n ==> ((f i) has_derivative (f' i)) net)
     ==> ((\x. vsum (m..n) (\i. f i x)) has_derivative
          (\h. vsum (m..n) (\i. f' i h))) net"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_VSUM THEN
    ASM_REWRITE_TAC [IN_NUMSEG, FINITE_NUMSEG])

  let HAS_DERIVATIVE_COMPONENTWISE_WITHIN ← prove
   r"!f:real^M->real^N f' a s.
        (f has_derivative f') (at a within s) <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> ((\x. lift(f(x)$i)) has_derivative (\x. lift(f'(x)$i)))
                (at a within s)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [has_derivative_within] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [LINEAR_COMPONENTWISE, LIM_COMPONENTWISE_LIFT] THEN
    SIMP_TAC [AND_FORALL_THM, ← TAUT (← q r"(p ==> q) /\ (p ==> r) <=> p ==> q /\ r")] THEN
    REWRITE_TAC [← GSYM LIFT_ADD, ← GSYM LIFT_CMUL, ← GSYM LIFT_SUB] THEN
    REWRITE_TAC [VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, VEC_COMPONENT,
                 VECTOR_SUB_COMPONENT, LIFT_NUM])

  let HAS_DERIVATIVE_COMPONENTWISE_AT ← prove
   r"!f:real^M->real^N f' a.
        (f has_derivative f') (at a) <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> ((\x. lift(f(x)$i)) has_derivative (\x. lift(f'(x)$i))) (at a)"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    MATCH_ACCEPT_TAC HAS_DERIVATIVE_COMPONENTWISE_WITHIN)

  let HAS_DERIVATIVE_PASTECART_EQ ← prove
   r"!net f:real^M->real^N g:real^M->real^P f' g'.
        ((\x. pastecart (f x) (g x)) has_derivative
        (\x. pastecart (f' x) (g' x))) net <=>
        (f has_derivative f') net /\ (g has_derivative g') net"
   (REWRITE_TAC [has_derivative, PASTECART_SUB, PASTECART_ADD] THEN
    REWRITE_TAC [← GSYM PASTECART_CMUL, ← GSYM PASTECART_VEC] THEN
    REWRITE_TAC [LIM_PASTECART_EQ, LINEAR_PASTECART_EQ] THEN
    REWRITE_TAC [CONJ_ACI])

  let HAS_DERIVATIVE_PASTECART ← prove
   r"!net f:real^M->real^N g:real^M->real^P f' g'.
        (f has_derivative f') net /\ (g has_derivative g') net
        ==> ((\x. pastecart (f x) (g x)) has_derivative
             (\x. pastecart (f' x) (g' x))) net"
   (REWRITE_TAC [HAS_DERIVATIVE_PASTECART_EQ])

  let HAS_DERIVATIVE_VMUL_COMPONENT ← prove
   r"!c:real^M->real^N c' k v:real^P.
        1 <= k /\ k <= dimindex(:N) /\ (c has_derivative c') net
        ==> ((\x. c(x)$k % v) has_derivative (\x. c'(x)$k % v)) net"
   (SIMP_TAC [has_derivative, LINEAR_VMUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC [← GSYM VECTOR_ADD_RDISTRIB, ← GSYM VECTOR_SUB_RDISTRIB] THEN
    SUBST1_TAC (← VECTOR_ARITH (← q r"vec 0 = &0 % (v:real^P)")) THEN
    REWRITE_TAC [VECTOR_MUL_ASSOC] THEN MATCH_MP_TAC LIM_VMUL THEN
    ASM_SIMP_TAC [← GSYM VECTOR_SUB_COMPONENT, ← GSYM VECTOR_ADD_COMPONENT] THEN
    ASM_SIMP_TAC [← GSYM VECTOR_MUL_COMPONENT] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [tendsto]) THEN
    REWRITE_TAC [tendsto, dist, LIFT_NUM, VECTOR_SUB_RZERO, o_THM, NORM_LIFT] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
    REWRITE_TAC [] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] EVENTUALLY_MONO) THEN
    ASM_SIMP_TAC [VECTOR_MUL_COMPONENT, REAL_ABS_MUL, NORM_MUL] THEN
    ASM_MESON_TAC [REAL_LET_TRANS, COMPONENT_LE_NORM,
                   REAL_LE_LMUL, REAL_ABS_POS])

  let HAS_DERIVATIVE_VMUL_DROP ← prove
   r"!c c' v. (c has_derivative c') net
            ==> ((\x. drop(c(x)) % v) has_derivative (\x. drop(c'(x)) % v)) net"
   (SIMP_TAC [drop, LE_REFL, DIMINDEX_1, HAS_DERIVATIVE_VMUL_COMPONENT])

  let HAS_DERIVATIVE_LIFT_DOT ← prove
   r"!f:real^M->real^N f'.
     (f has_derivative f') net
     ==> ((\x. lift(v dot f(x))) has_derivative (\t. lift(v dot (f' t)))) net"
   (REPEAT GEN_TAC THEN REWRITE_TAC [has_derivative] THEN
    REWRITE_TAC [← GSYM LIFT_SUB, ← GSYM LIFT_ADD, ← GSYM LIFT_CMUL] THEN
    REWRITE_TAC [← GSYM DOT_RADD, ← GSYM DOT_RSUB, ← GSYM DOT_RMUL] THEN
    SUBGOAL_THEN
     (← q r"(\t. lift (v dot (f':real^M->real^N) t)) = (\y. lift(v dot y)) o f'")
    SUBST1_TAC THENL [REWRITE_TAC [o_DEF], ALL_TAC] THEN
    SIMP_TAC [LINEAR_COMPOSE, LINEAR_LIFT_DOT] THEN
    DISCH_THEN (MP_TAC o MATCH_MP LIM_LIFT_DOT o CONJUNCT2) THEN
    SIMP_TAC [o_DEF, DOT_RZERO, LIFT_NUM])

  let HAS_DERIVATIVE_TRANSFORM_WITHIN ← prove
   r"!f f' g x s d.
       &0 < d /\ x IN s /\
       (!x'. x' IN s /\ dist (x',x) < d ==> f x' = g x') /\
       (f has_derivative f') (at x within s)
       ==> (g has_derivative f') (at x within s)"
   (REPEAT GEN_TAC THEN SIMP_TAC [has_derivative_within, IMP_CONJ] THEN
    REPLICATE_TAC 4 DISCH_TAC THEN
    MATCH_MP_TAC (← REWRITE_RULE [← TAUT (← q r"a /\ b /\ c ==> d <=> a /\ b ==> c ==> d")]
      LIM_TRANSFORM_WITHIN) THEN
    EXISTS_TAC (← q r"d:real") THEN ASM_SIMP_TAC [DIST_REFL])

  let HAS_DERIVATIVE_TRANSFORM_AT ← prove
   r"!f f' g x d.
       &0 < d /\ (!x'. dist (x',x) < d ==> f x' = g x') /\
       (f has_derivative f') (at x)
       ==> (g has_derivative f') (at x)"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    MESON_TAC [HAS_DERIVATIVE_TRANSFORM_WITHIN, IN_UNIV])

  let HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN ← prove
   r"!f g:real^M->real^N s x.
        open s /\ x IN s /\
        (!y. y IN s ==> f y = g y) /\
        (f has_derivative f') (at x)
        ==> (g has_derivative f') (at x)"
   (REPEAT GEN_TAC THEN SIMP_TAC [has_derivative_at, IMP_CONJ] THEN
    REPLICATE_TAC 4 DISCH_TAC THEN
    MATCH_MP_TAC (← REWRITE_RULE
      [← TAUT (← q r"a /\ b /\ c /\ d ==> e <=> a /\ b /\ c ==> d ==> e")]
      LIM_TRANSFORM_WITHIN_OPEN) THEN
    EXISTS_TAC (← q r"s:real^M->bool") THEN ASM_SIMP_TAC [])

  parse_as_infix ("differentiable", (12, "right"))
  parse_as_infix ("differentiable_on", (12, "right"))

  let differentiable ← new_definition
   r"f differentiable net <=> ?f'. (f has_derivative f') net"

  let differentiable_on ← new_definition
   r"f differentiable_on s <=> !x. x IN s ==> f differentiable (at x within s)"

  let HAS_DERIVATIVE_IMP_DIFFERENTIABLE ← prove
   r"!f f' net. (f has_derivative f') net ==> f differentiable net"
   (REWRITE_TAC [differentiable] THEN MESON_TAC [])

  let DIFFERENTIABLE_AT_WITHIN ← prove
   r"!f s x. f differentiable (at x)
           ==> f differentiable (at x within s)"
   (REWRITE_TAC [differentiable] THEN MESON_TAC [HAS_DERIVATIVE_AT_WITHIN])

  let DIFFERENTIABLE_WITHIN_OPEN ← prove
   r"!f a s.
         a IN s /\ open s
         ==> (f differentiable (at a within s) <=> (f differentiable (at a)))"
   (SIMP_TAC [differentiable, HAS_DERIVATIVE_WITHIN_OPEN])

  let DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON ← prove
   r"!f s. (!x. x IN s ==> f differentiable at x) ==> f differentiable_on s"
   (REWRITE_TAC [differentiable_on] THEN MESON_TAC [DIFFERENTIABLE_AT_WITHIN])

  let DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT ← prove
   r"!f s. open s ==> (f differentiable_on s <=>
                     !x. x IN s ==> f differentiable at x)"
   (SIMP_TAC [differentiable_on, DIFFERENTIABLE_WITHIN_OPEN])

  let DIFFERENTIABLE_TRANSFORM_WITHIN ← prove
   r"!f g x s d.
       &0 < d /\ x IN s /\
       (!x'. x' IN s /\ dist (x',x) < d ==> f x' = g x') /\
       f differentiable (at x within s)
       ==> g differentiable (at x within s)"
   (REWRITE_TAC [differentiable] THEN
    MESON_TAC [HAS_DERIVATIVE_TRANSFORM_WITHIN])

  let DIFFERENTIABLE_TRANSFORM_AT ← prove
   r"!f g x d.
       &0 < d /\
       (!x'. dist (x',x) < d ==> f x' = g x') /\
       f differentiable at x
       ==> g differentiable at x"
   (REWRITE_TAC [differentiable] THEN
    MESON_TAC [HAS_DERIVATIVE_TRANSFORM_AT])

  let DIFFERENTIABLE_ON_EQ ← prove
   r"!f g:real^M->real^N s.
        (!x. x IN s ==> f x = g x) /\ f differentiable_on s
        ==> g differentiable_on s"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [differentiable_on] THEN
    ASM_MESON_TAC [DIFFERENTIABLE_TRANSFORM_WITHIN, REAL_LT_01])

  let frechet_derivative ← new_definition
   r"frechet_derivative f net = @f'. (f has_derivative f') net"

  let FRECHET_DERIVATIVE_WORKS ← prove
   r"!f net. f differentiable net <=>
           (f has_derivative (frechet_derivative f net)) net"
   (REPEAT GEN_TAC THEN REWRITE_TAC [frechet_derivative] THEN
    CONV_TAC (RAND_CONV SELECT_CONV) THEN REWRITE_TAC [differentiable])

  let LINEAR_FRECHET_DERIVATIVE ← prove
   r"!f net. f differentiable net ==> linear(frechet_derivative f net)"
   (SIMP_TAC [FRECHET_DERIVATIVE_WORKS, has_derivative])

  let jacobian ← new_definition
   r"jacobian f net = matrix(frechet_derivative f net)"

  let JACOBIAN_WORKS ← prove
   r"!f net. f differentiable net <=>
           (f has_derivative (\h. jacobian f net ** h)) net"
   (REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC, MESON_TAC [differentiable]] THEN
    REWRITE_TAC [FRECHET_DERIVATIVE_WORKS] THEN
    SIMP_TAC [jacobian, MATRIX_WORKS, has_derivative] THEN SIMP_TAC [ETA_AX])

  pure { has_derivative, has_derivative_within, has_derivative_at,
         HAS_DERIVATIVE_WITHIN, HAS_DERIVATIVE_AT, HAS_DERIVATIVE_AT_WITHIN,
         HAS_DERIVATIVE_WITHIN_OPEN, HAS_DERIVATIVE_WITHIN_OPEN_IN, HAS_DERIVATIVE_LINEAR,
         HAS_DERIVATIVE_ID, HAS_DERIVATIVE_CONST, HAS_DERIVATIVE_LIFT_COMPONENT,
         HAS_DERIVATIVE_CMUL, HAS_DERIVATIVE_CMUL_EQ, HAS_DERIVATIVE_NEG,
         HAS_DERIVATIVE_NEG_EQ, HAS_DERIVATIVE_ADD, HAS_DERIVATIVE_SUB, HAS_DERIVATIVE_VSUM,
         HAS_DERIVATIVE_VSUM_NUMSEG, HAS_DERIVATIVE_COMPONENTWISE_WITHIN,
         HAS_DERIVATIVE_COMPONENTWISE_AT, HAS_DERIVATIVE_PASTECART_EQ,
         HAS_DERIVATIVE_PASTECART, HAS_DERIVATIVE_VMUL_COMPONENT, HAS_DERIVATIVE_VMUL_DROP,
         HAS_DERIVATIVE_LIFT_DOT, HAS_DERIVATIVE_TRANSFORM_WITHIN,
         HAS_DERIVATIVE_TRANSFORM_AT, HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN, differentiable,
         differentiable_on, HAS_DERIVATIVE_IMP_DIFFERENTIABLE, DIFFERENTIABLE_AT_WITHIN,
         DIFFERENTIABLE_WITHIN_OPEN, DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON,
         DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT, DIFFERENTIABLE_TRANSFORM_WITHIN,
         DIFFERENTIABLE_TRANSFORM_AT, DIFFERENTIABLE_ON_EQ, frechet_derivative,
         FRECHET_DERIVATIVE_WORKS, LINEAR_FRECHET_DERIVATIVE, jacobian, JACOBIAN_WORKS }

/- ------------------------------------------------------------------------- -/
/- Differentiability implies continuity; multiplied-out variant; the chain   -/
/- rule; composition rules.  (derivatives.ml 406-787)                        -/
/- ------------------------------------------------------------------------- -/

structure DVB where
  LIM_MUL_NORM_WITHIN : thm
  DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN : thm
  DIFFERENTIABLE_IMP_CONTINUOUS_AT : thm
  DIFFERENTIABLE_IMP_CONTINUOUS_ON : thm
  HAS_DERIVATIVE_WITHIN_SUBSET : thm
  DIFFERENTIABLE_WITHIN_SUBSET : thm
  DIFFERENTIABLE_ON_SUBSET : thm
  DIFFERENTIABLE_ON_EMPTY : thm
  HAS_DERIVATIVE_WITHIN_ALT : thm
  HAS_DERIVATIVE_AT_ALT : thm
  DIFF_CHAIN_WITHIN : thm
  DIFF_CHAIN_AT : thm
  HAS_DERIVATIVE_WITHIN_REFLECT : thm
  HAS_DERIVATIVE_AT_REFLECT : thm
  DIFFERENTIABLE_ON_REFLECT : thm
  DIFFERENTIABLE_LINEAR : thm
  DIFFERENTIABLE_CONST : thm
  DIFFERENTIABLE_ID : thm
  DIFFERENTIABLE_LIFT_COMPONENT : thm
  DIFFERENTIABLE_CMUL : thm
  DIFFERENTIABLE_NEG : thm
  DIFFERENTIABLE_ADD : thm
  DIFFERENTIABLE_SUB : thm
  DIFFERENTIABLE_VSUM : thm
  DIFFERENTIABLE_VSUM_NUMSEG : thm
  DIFFERENTIABLE_CHAIN_AT : thm
  DIFFERENTIABLE_CHAIN_WITHIN : thm
  DIFFERENTIABLE_COMPONENTWISE_WITHIN : thm
  DIFFERENTIABLE_COMPONENTWISE_AT : thm
  DIFFERENTIABLE_ON_LINEAR : thm
  DIFFERENTIABLE_ON_CONST : thm
  DIFFERENTIABLE_ON_ID : thm
  DIFFERENTIABLE_ON_COMPOSE : thm
  DIFFERENTIABLE_ON_NEG : thm
  DIFFERENTIABLE_ON_ADD : thm
  DIFFERENTIABLE_ON_SUB : thm
  deriving Inhabited

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
@[nospecialize]
def setupDVB [HolBase] (D : DerivativesDeps) (BDVA : DVA) : ExceptT String IO DVB := do
  -- @@SCOPE BEGIN
  let { differentiable, differentiable_on, HAS_DERIVATIVE_ADD, HAS_DERIVATIVE_CMUL,
        HAS_DERIVATIVE_COMPONENTWISE_WITHIN, HAS_DERIVATIVE_CONST, HAS_DERIVATIVE_ID,
        HAS_DERIVATIVE_LIFT_COMPONENT, HAS_DERIVATIVE_LINEAR, HAS_DERIVATIVE_NEG,
        HAS_DERIVATIVE_SUB, HAS_DERIVATIVE_VSUM, has_derivative_within, .. } := BDVA
  let { ARITH, ETA_AX, FINITE_NUMSEG, FORALL_AND_THM, .. } := D.dg.pt.cvx.core1
  let { FORALL_IN_IMAGE, IMAGE_ID, IMAGE_o, IMP_CONJ_ALT, IMP_IMP, .. } := D.dg.pt.cvx.core2
  let { IN_IMAGE, IN_NUMSEG, IN_UNIV, LAMBDA_BETA, MONO_EXISTS, MONO_FORALL, MONO_IMP,
        NOT_IN_EMPTY, REAL_ABS_INV, REAL_DOWN2, .. } := D.dg.pt.cvx.core3
  let { REAL_LE_ADD2, REAL_LE_LDIV_EQ, REAL_LE_LMUL, REAL_LE_LMUL_EQ, REAL_LE_REFL,
        REAL_LE_TRANS, REAL_LET_TRANS, REAL_LT_01, REAL_LT_ADD, REAL_LT_DIV, REAL_LT_IMP_LE,
        REAL_LT_IMP_NZ, REAL_LT_LDIV_EQ, REAL_LT_MIN, REAL_LT_RDIV_EQ, .. } :=
        D.dg.pt.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_RINV, REAL_MUL_RZERO,
        REAL_MUL_SYM, REAL_OF_NUM_LT, RIGHT_AND_EXISTS_THM, RIGHT_IMP_EXISTS_THM,
        SKOLEM_THM, SUBSET, .. } := D.dg.pt.cvx.core5
  let { o_DEF, o_THM, real_div, SUBSET_UNIV, .. } := D.dg.pt.cvx.core6
  let { DIST_NZ, .. } := D.dg.pt.cvx.vec1
  let { LIFT_DROP, LINEAR_0, LINEAR_COMPOSE, LINEAR_SUB, NORM_0, NORM_EQ_0, .. } :=
        D.dg.pt.cvx.vec2
  let { NORM_MUL, NORM_NEG, NORM_POS_LE, NORM_POS_LT, REAL_ABS_NORM, .. } :=
        D.dg.pt.cvx.vec3
  let { dist, VECTOR_MUL_ASSOC, VECTOR_MUL_LID, VECTOR_NEG_NEG, VECTOR_SUB_EQ,
        VECTOR_SUB_REFL, VECTOR_SUB_RZERO, .. } := D.dg.pt.cvx.vec4
  let { CONTINUOUS_CONST, CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN, CONTINUOUS_SUB,
        CONTINUOUS_WITHIN, CONTINUOUS_WITHIN_ID, .. } := D.dg.pt.cvx.top3
  let { LIM_ADD, LIM_WITHIN, .. } := D.dg.pt.cvx.top4
  let { ASM_MESON_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV,
        VECTOR_ARITH, .. } := D.dg.pt.cvx
  let { LINEAR_NEGATION, .. } := D.dg.pt.qvec
  let { REAL_LT_TRANS, .. } := D.dg.qsession
  let { REAL_LT_MUL2, REAL_LT_RMUL_EQ, .. } := D.qsession
  let { CONTINUOUS_WITHIN_COMPOSE, .. } := D.qtopology1
  let { LIM_WITHIN_SUBSET, LINEAR_CONTINUOUS_WITHIN, WITHIN_UNIV, .. } := D.qtopology2
  let { LINEAR_BOUNDED_POS, NORM_TRIANGLE_SUB, REFLECT_UNIV, .. } := D.qvec
  -- @@SCOPE END

  let LIM_MUL_NORM_WITHIN ← prove
   r"!f a s. (f --> vec 0) (at a within s)
           ==> ((\x. norm(x - a) % f(x)) --> vec 0) (at a within s)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [LIM_WITHIN] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"e:real") THEN
    ASM_CASES_TAC (← q r"&0 < e") THEN ASM_REWRITE_TAC [dist, VECTOR_SUB_RZERO] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"min d (&1)") THEN ASM_REWRITE_TAC [REAL_LT_MIN, REAL_LT_01] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [NORM_MUL, REAL_ABS_NORM] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
    ASM_SIMP_TAC [REAL_LT_MUL2, NORM_POS_LE])

  let DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN ← prove
   r"!f:real^M->real^N s.
        f differentiable (at x within s) ==> f continuous (at x within s)"
   (REWRITE_TAC [differentiable, has_derivative_within, CONTINUOUS_WITHIN] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"f':real^M->real^N") MP_TAC) THEN
    STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o MATCH_MP LIM_MUL_NORM_WITHIN) THEN
    SUBGOAL_THEN
     (← q r"((f':real^M->real^N) o (\y. y - x)) continuous (at x within s)")
    MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_WITHIN_COMPOSE THEN
      ASM_SIMP_TAC [LINEAR_CONTINUOUS_WITHIN] THEN
      SIMP_TAC [CONTINUOUS_SUB, CONTINUOUS_CONST, CONTINUOUS_WITHIN_ID],
      ALL_TAC] THEN
    REWRITE_TAC [CONTINUOUS_WITHIN, o_DEF] THEN
    ASM_REWRITE_TAC [VECTOR_MUL_ASSOC, IMP_IMP, IN_UNIV] THEN
    DISCH_THEN (MP_TAC o MATCH_MP LIM_ADD) THEN
    SIMP_TAC [LIM_WITHIN, ← GSYM DIST_NZ, REAL_MUL_RINV, NORM_EQ_0,
              ← VECTOR_ARITH (← q r"(x - y = vec 0) <=> (x = y)"),
              VECTOR_MUL_LID, VECTOR_SUB_REFL] THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP LINEAR_0) THEN
    REWRITE_TAC [dist, VECTOR_SUB_RZERO] THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"(a + b - (c + a)) - (vec 0 + vec 0) = b - c")])

  let DIFFERENTIABLE_IMP_CONTINUOUS_AT ← prove
   r"!f:real^M->real^N x. f differentiable (at x) ==> f continuous (at x)"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    REWRITE_TAC [DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN])

  let DIFFERENTIABLE_IMP_CONTINUOUS_ON ← prove
   r"!f:real^M->real^N s. f differentiable_on s ==> f continuous_on s"
   (SIMP_TAC [differentiable_on, CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN,
              DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN])

  let HAS_DERIVATIVE_WITHIN_SUBSET ← prove
   r"!f s t x. (f has_derivative f') (at x within s) /\ t SUBSET s
             ==> (f has_derivative f') (at x within t)"
   (REWRITE_TAC [has_derivative_within] THEN MESON_TAC [LIM_WITHIN_SUBSET])

  let DIFFERENTIABLE_WITHIN_SUBSET ← prove
   r"!f:real^M->real^N s t.
      f differentiable (at x within t) /\ s SUBSET t
      ==> f differentiable (at x within s)"
   (REWRITE_TAC [differentiable] THEN MESON_TAC [HAS_DERIVATIVE_WITHIN_SUBSET])

  let DIFFERENTIABLE_ON_SUBSET ← prove
   r"!f:real^M->real^N s t.
      f differentiable_on t /\ s SUBSET t ==> f differentiable_on s"
   (REWRITE_TAC [differentiable_on] THEN
    MESON_TAC [SUBSET, DIFFERENTIABLE_WITHIN_SUBSET])

  let DIFFERENTIABLE_ON_EMPTY ← prove
   r"!f. f differentiable_on {}"
   (REWRITE_TAC [differentiable_on, NOT_IN_EMPTY])

  let HAS_DERIVATIVE_WITHIN_ALT ← prove
   r"!f:real^M->real^N f' s x.
     (f has_derivative f') (at x within s) <=>
            linear f' /\
            !e. &0 < e
                ==> ?d. &0 < d /\
                        !y. y IN s /\ norm(y - x) < d
                            ==> norm(f(y) - f(x) - f'(y - x)) <=
                                e * norm(y - x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [has_derivative_within, LIM_WITHIN] THEN
    ASM_REWRITE_TAC [dist, VECTOR_SUB_RZERO] THEN
    ASM_CASES_TAC (← q r"linear(f':real^M->real^N)") THEN
    ASM_REWRITE_TAC [NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
    SIMP_TAC [← GSYM real_div, REAL_LT_LDIV_EQ] THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"a - (b + c) = a - b - c :real^M")] THEN
    EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e:real")) THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"d:real") THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"y:real^M") THEN DISCH_TAC THEN
      ASM_CASES_TAC (← q r"&0 < norm(y - x :real^M)") THENL
       [ASM_SIMP_TAC [REAL_LT_IMP_LE], ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [NORM_POS_LT]) THEN
      ASM_SIMP_TAC [VECTOR_SUB_EQ, VECTOR_SUB_REFL, NORM_0, REAL_MUL_RZERO,
                    ← VECTOR_ARITH (← q r"vec 0 - x = --x"), NORM_NEG] THEN
      ASM_MESON_TAC [LINEAR_0, NORM_0, REAL_LE_REFL],
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e / &2")) THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"d:real") THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"y:real^M") THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (← q r"e / &2 * norm(y - x :real^M)") THEN
      ASM_SIMP_TAC [REAL_LT_RMUL_EQ, REAL_LT_LDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN
      UNDISCH_TAC (← q r"&0 < e") THEN REAL_ARITH_TAC])

  let HAS_DERIVATIVE_AT_ALT ← prove
   r"!f:real^M->real^N f' x.
     (f has_derivative f') (at x) <=>
        linear f' /\
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !y. norm(y - x) < d
                        ==> norm(f(y) - f(x) - f'(y - x)) <= e * norm(y - x)"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    REWRITE_TAC [HAS_DERIVATIVE_WITHIN_ALT, IN_UNIV])

  let DIFF_CHAIN_WITHIN ← prove
   r"!f:real^M->real^N g:real^N->real^P f' g' x s.
        (f has_derivative f') (at x within s) /\
        (g has_derivative g') (at (f x) within (IMAGE f s))
        ==> ((g o f) has_derivative (g' o f'))(at x within s)"
   (REPEAT GEN_TAC THEN SIMP_TAC [HAS_DERIVATIVE_WITHIN_ALT, LINEAR_COMPOSE] THEN
    DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    FIRST_ASSUM (X_CHOOSE_TAC (← q r"B1:real") o MATCH_MP LINEAR_BOUNDED_POS) THEN
    DISCH_THEN (fun th => tactic_of do pure (X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN MP_TAC th)) THEN
    DISCH_THEN (CONJUNCTS_THEN2
     (fun th => tactic_of do
        pure (ASSUME_TAC th THEN X_CHOOSE_TAC (← q r"B2:real") (← MATCH_MP
                LINEAR_BOUNDED_POS th))) MP_TAC) THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      pure (MP_TAC th THEN MP_TAC (← SPEC (← q r"e / &2 / B2") th))) THEN
    ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d1:real") STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"e / &2 / (&1 + B1)")) THEN
    ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH, REAL_LT_ADD] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"de:real") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"&1")) THEN
    REWRITE_TAC [REAL_LT_01, REAL_MUL_LID] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d2:real") STRIP_ASSUME_TAC) THEN
    MP_TAC (← SPECL [← q r"d1:real", ← q r"d2:real"] REAL_DOWN2) THEN
    ASM_SIMP_TAC [REAL_LT_DIV, REAL_LT_ADD, REAL_LT_01] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d0:real") STRIP_ASSUME_TAC) THEN
    MP_TAC (← SPECL [← q r"d0:real", ← q r"de / (B1 + &1)"] REAL_DOWN2) THEN
    ASM_SIMP_TAC [REAL_LT_DIV, REAL_LT_ADD, REAL_LT_01] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"d:real") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"y:real^M") THEN
    DISCH_TAC THEN UNDISCH_TAC
     (← q r"!y. y IN s /\ norm(y - x) < d2
          ==> norm ((f:real^M->real^N) y - f x - f'(y - x)) <= norm(y - x)") THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"y:real^M")) THEN ANTS_TAC THENL
     [ASM_MESON_TAC [REAL_LT_TRANS], DISCH_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"y:real^M")) THEN ANTS_TAC THENL
     [ASM_MESON_TAC [REAL_LT_TRANS], DISCH_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(f:real^M->real^N) y")) THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC [IN_IMAGE], ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
       (← q r"norm(f'(y - x)) + norm((f:real^M->real^N) y - f x - f'(y - x))") THEN
      REWRITE_TAC [NORM_TRIANGLE_SUB] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (← q r"B1 * norm(y - x) + norm(y - x :real^M)") THEN
      ASM_SIMP_TAC [REAL_LE_ADD2] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"a * x + x = x * (a + &1)")] THEN
      ASM_SIMP_TAC [← GSYM REAL_LT_RDIV_EQ, REAL_LT_ADD, REAL_LT_01] THEN
      ASM_MESON_TAC [REAL_LT_TRANS],
      DISCH_TAC] THEN
    REWRITE_TAC [o_THM] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"norm((g:real^N->real^P)(f(y:real^M)) - g(f x) - g'(f y - f x)) +
                norm((g(f y) - g(f x) - g'(f'(y - x))) -
                     (g(f y) - g(f x) - g'(f y - f x)))") THEN
    REWRITE_TAC [NORM_TRIANGLE_SUB] THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"(a - b - c1) - (a - b - c2) = c2 - c1:real^M")] THEN
    ASM_SIMP_TAC [← GSYM LINEAR_SUB] THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← REAL_ARITH
      (← q r"a <= d ==> b <= ee - d ==> a + b <= ee"))) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"B2 * norm((f:real^M->real^N) y - f x - f'(y - x))") THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"B2 * e / &2 / B2 * norm(y - x :real^M)") THEN
    ASM_SIMP_TAC [REAL_LE_LMUL, REAL_LT_IMP_LE] THEN REWRITE_TAC [real_div] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH
     (← q r"b * ((e * h) * b') * x <= e * x - d <=>
      d <= e * (&1 - h * b' * b) * x")] THEN
    ASM_SIMP_TAC [REAL_MUL_LINV, REAL_LT_IMP_NZ] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC [REAL_LE_LMUL_EQ, REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [← GSYM real_div] THEN
    ASM_SIMP_TAC [REAL_LE_LDIV_EQ, REAL_LT_ADD, REAL_LT_01] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     (← q r"norm(f'(y - x)) + norm((f:real^M->real^N) y - f x - f'(y - x))") THEN
    REWRITE_TAC [NORM_TRIANGLE_SUB] THEN MATCH_MP_TAC (← REAL_ARITH
     (← q r"u <= x * b /\ v <= b ==> u + v <= b * (&1 + x)")) THEN
    ASM_REWRITE_TAC [])

  let DIFF_CHAIN_AT ← prove
   r"!f:real^M->real^N g:real^N->real^P f' g' x.
        (f has_derivative f') (at x) /\
        (g has_derivative g') (at (f x))
        ==> ((g o f) has_derivative (g' o f')) (at x)"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    ASM_MESON_TAC [DIFF_CHAIN_WITHIN, LIM_WITHIN_SUBSET, SUBSET_UNIV,
                   HAS_DERIVATIVE_WITHIN_SUBSET])

  let HAS_DERIVATIVE_WITHIN_REFLECT ← prove
   r"!f:real^M->real^N f' s a.
        ((\x. f(--x)) has_derivative (\x. f'(--x)))
        (at (--a) within (IMAGE (--) s)) <=>
        (f has_derivative f') (at a within s)"
   (REWRITE_TAC [← TAUT (← q r"(p <=> q) <=> (q ==> p) /\ (p ==> q)")] THEN
    REWRITE_TAC [FORALL_AND_THM] THEN
    MATCH_MP_TAC (← TAUT (← q r"q /\ (q ==> p) ==> p /\ q")) THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o SPEC (← q r"(--):real^M->real^M") o
       MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT] DIFF_CHAIN_WITHIN)) THEN
      REWRITE_TAC [o_DEF, VECTOR_NEG_NEG, ETA_AX] THEN
      SIMP_TAC [LINEAR_NEGATION, HAS_DERIVATIVE_LINEAR],
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [o_DEF, VECTOR_NEG_NEG, ETA_AX, ← GSYM IMAGE_o, IMAGE_ID]])

  let HAS_DERIVATIVE_AT_REFLECT ← prove
   r"!f:real^M->real^N f' a.
        ((\x. f(--x)) has_derivative (\x. f'(--x))) (at (--a)) <=>
        (f has_derivative f') (at a)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM HAS_DERIVATIVE_WITHIN_REFLECT] THEN
    REWRITE_TAC [REFLECT_UNIV])

  let DIFFERENTIABLE_ON_REFLECT ← prove
   r"!f:real^M->real^N s.
        (\x. f(--x)) differentiable_on (IMAGE (--) s) <=>
        f differentiable_on s"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [differentiable_on, differentiable, FORALL_IN_IMAGE] THEN
    EQ_TAC THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"x:real^M") THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC [] THEN
    DISCH_THEN (CHOOSE_THEN MP_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM HAS_DERIVATIVE_WITHIN_REFLECT] THEN
    REWRITE_TAC [o_DEF, VECTOR_NEG_NEG, ETA_AX, ← GSYM IMAGE_o, IMAGE_ID] THEN
    MESON_TAC [])

  let DIFFERENTIABLE_LINEAR ← prove
   r"!net f:real^M->real^N. linear f ==> f differentiable net"
   (REWRITE_TAC [differentiable] THEN MESON_TAC [HAS_DERIVATIVE_LINEAR])

  let DIFFERENTIABLE_CONST ← prove
   r"!c net. (\z. c) differentiable net"
   (REWRITE_TAC [differentiable] THEN MESON_TAC [HAS_DERIVATIVE_CONST])

  let DIFFERENTIABLE_ID ← prove
   r"!net. (\z. z) differentiable net"
   (REWRITE_TAC [differentiable] THEN MESON_TAC [HAS_DERIVATIVE_ID])

  let DIFFERENTIABLE_LIFT_COMPONENT ← prove
   r"!net:(real^N)net. (\x. lift(x$i)) differentiable net"
   (REWRITE_TAC [differentiable] THEN MESON_TAC [HAS_DERIVATIVE_LIFT_COMPONENT])

  let DIFFERENTIABLE_CMUL ← prove
   r"!net f c. f differentiable net ==> (\x. c % f(x)) differentiable net"
   (REWRITE_TAC [differentiable] THEN MESON_TAC [HAS_DERIVATIVE_CMUL])

  let DIFFERENTIABLE_NEG ← prove
   r"!f net. f differentiable net ==> (\z. --(f z)) differentiable net"
   (REWRITE_TAC [differentiable] THEN MESON_TAC [HAS_DERIVATIVE_NEG])

  let DIFFERENTIABLE_ADD ← prove
   r"!f g net.
        f differentiable net /\
        g differentiable net
        ==> (\z. f z + g z) differentiable net"
   (REWRITE_TAC [differentiable] THEN MESON_TAC [HAS_DERIVATIVE_ADD])

  let DIFFERENTIABLE_SUB ← prove
   r"!f g net.
        f differentiable net /\
        g differentiable net
        ==> (\z. f z - g z) differentiable net"
   (REWRITE_TAC [differentiable] THEN MESON_TAC [HAS_DERIVATIVE_SUB])

  let DIFFERENTIABLE_VSUM ← prove
   r"!f net s.
     FINITE s /\
     (!a. a IN s ==> (f a) differentiable net)
     ==> (\x. vsum s (\a. f a x)) differentiable net"
   (REPEAT GEN_TAC THEN REWRITE_TAC [differentiable] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [RIGHT_IMP_EXISTS_THM, SKOLEM_THM, RIGHT_AND_EXISTS_THM] THEN
    DISCH_THEN (CHOOSE_THEN (MP_TAC o MATCH_MP HAS_DERIVATIVE_VSUM)) THEN
    MESON_TAC [])

  let DIFFERENTIABLE_VSUM_NUMSEG ← prove
   r"!f net m n.
     FINITE s /\
     (!i. m <= i /\ i <= n ==> (f i) differentiable net)
     ==> (\x. vsum (m..n) (\a. f a x)) differentiable net"
   (SIMP_TAC [DIFFERENTIABLE_VSUM, FINITE_NUMSEG, IN_NUMSEG])

  let DIFFERENTIABLE_CHAIN_AT ← prove
   r"!f g x.
    f differentiable (at x) /\
    g differentiable (at(f x))
    ==> (g o f) differentiable (at x)"
   (REWRITE_TAC [differentiable] THEN MESON_TAC [DIFF_CHAIN_AT])

  let DIFFERENTIABLE_CHAIN_WITHIN ← prove
   r"!f g x s.
    f differentiable (at x within s) /\
    g differentiable (at(f x) within IMAGE f s)
    ==> (g o f) differentiable (at x within s)"
   (REWRITE_TAC [differentiable] THEN MESON_TAC [DIFF_CHAIN_WITHIN])

  let DIFFERENTIABLE_COMPONENTWISE_WITHIN ← prove
   r"!f:real^M->real^N a s.
        f differentiable (at a within s) <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. lift(f(x)$i)) differentiable (at a within s)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [differentiable] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [HAS_DERIVATIVE_COMPONENTWISE_WITHIN] THEN
    REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_TAC (← q r"g':real^M->real^N")) THEN
      EXISTS_TAC (← q r"\i x. lift((g':real^M->real^N) x$i)") THEN ASM_REWRITE_TAC [],
      DISCH_THEN (X_CHOOSE_TAC (← q r"g':num->real^M->real^1")) THEN
      EXISTS_TAC (← q r"(\x. lambda i. drop((g':num->real^M->real^1) i x))
                  :real^M->real^N") THEN
      ASM_SIMP_TAC [LAMBDA_BETA, LIFT_DROP, ETA_AX]])

  let DIFFERENTIABLE_COMPONENTWISE_AT ← prove
   r"!f:real^M->real^N a.
        f differentiable (at a) <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. lift(f(x)$i)) differentiable (at a)"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    MATCH_ACCEPT_TAC DIFFERENTIABLE_COMPONENTWISE_WITHIN)

  let DIFFERENTIABLE_ON_LINEAR ← prove
   r"!f:real^M->real^N s. linear f ==> f differentiable_on s"
   (SIMP_TAC [differentiable_on, DIFFERENTIABLE_LINEAR])

  let DIFFERENTIABLE_ON_CONST ← prove
   r"!s c. (\z. c) differentiable_on s"
   (REWRITE_TAC [differentiable_on, DIFFERENTIABLE_CONST])

  let DIFFERENTIABLE_ON_ID ← prove
   r"!s. (\z. z) differentiable_on s"
   (REWRITE_TAC [differentiable_on, DIFFERENTIABLE_ID])

  let DIFFERENTIABLE_ON_COMPOSE ← prove
   r"!f g s. f differentiable_on s /\ g differentiable_on (IMAGE f s)
           ==> (g o f) differentiable_on s"
   (SIMP_TAC [differentiable_on, FORALL_IN_IMAGE] THEN
    MESON_TAC [DIFFERENTIABLE_CHAIN_WITHIN])

  let DIFFERENTIABLE_ON_NEG ← prove
   r"!f s. f differentiable_on s ==> (\z. --(f z)) differentiable_on s"
   (SIMP_TAC [differentiable_on, DIFFERENTIABLE_NEG])

  let DIFFERENTIABLE_ON_ADD ← prove
   r"!f g s.
        f differentiable_on s /\ g differentiable_on s
        ==> (\z. f z + g z) differentiable_on s"
   (SIMP_TAC [differentiable_on, DIFFERENTIABLE_ADD])

  let DIFFERENTIABLE_ON_SUB ← prove
   r"!f g s.
        f differentiable_on s /\ g differentiable_on s
        ==> (\z. f z - g z) differentiable_on s"
   (SIMP_TAC [differentiable_on, DIFFERENTIABLE_SUB])

  pure { LIM_MUL_NORM_WITHIN, DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN,
         DIFFERENTIABLE_IMP_CONTINUOUS_AT, DIFFERENTIABLE_IMP_CONTINUOUS_ON,
         HAS_DERIVATIVE_WITHIN_SUBSET, DIFFERENTIABLE_WITHIN_SUBSET, DIFFERENTIABLE_ON_SUBSET,
         DIFFERENTIABLE_ON_EMPTY, HAS_DERIVATIVE_WITHIN_ALT, HAS_DERIVATIVE_AT_ALT,
         DIFF_CHAIN_WITHIN, DIFF_CHAIN_AT, HAS_DERIVATIVE_WITHIN_REFLECT,
         HAS_DERIVATIVE_AT_REFLECT, DIFFERENTIABLE_ON_REFLECT, DIFFERENTIABLE_LINEAR,
         DIFFERENTIABLE_CONST, DIFFERENTIABLE_ID, DIFFERENTIABLE_LIFT_COMPONENT,
         DIFFERENTIABLE_CMUL, DIFFERENTIABLE_NEG, DIFFERENTIABLE_ADD, DIFFERENTIABLE_SUB,
         DIFFERENTIABLE_VSUM, DIFFERENTIABLE_VSUM_NUMSEG, DIFFERENTIABLE_CHAIN_AT,
         DIFFERENTIABLE_CHAIN_WITHIN, DIFFERENTIABLE_COMPONENTWISE_WITHIN,
         DIFFERENTIABLE_COMPONENTWISE_AT, DIFFERENTIABLE_ON_LINEAR, DIFFERENTIABLE_ON_CONST,
         DIFFERENTIABLE_ON_ID, DIFFERENTIABLE_ON_COMPOSE, DIFFERENTIABLE_ON_NEG,
         DIFFERENTIABLE_ON_ADD, DIFFERENTIABLE_ON_SUB }

/- ------------------------------------------------------------------------- -/
/- Uniqueness of derivative; components of the differential at a local      -/
/- maximum or minimum.  (derivatives.ml 788-1120)                            -/
/- ------------------------------------------------------------------------- -/

structure DVC where
  FRECHET_DERIVATIVE_UNIQUE_WITHIN : thm
  FRECHET_DERIVATIVE_UNIQUE_AT : thm
  HAS_FRECHET_DERIVATIVE_UNIQUE_AT : thm
  FRECHET_DERIVATIVE_CONST_AT : thm
  FRECHET_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL : thm
  FRECHET_DERIVATIVE_UNIQUE_WITHIN_OPEN_INTERVAL : thm
  FRECHET_DERIVATIVE_AT : thm
  FRECHET_DERIVATIVE_WITHIN_CLOSED_INTERVAL : thm
  DIFFERENTIAL_COMPONENT_POS_AT_MINIMUM : thm
  DIFFERENTIAL_COMPONENT_NEG_AT_MAXIMUM : thm
  DROP_DIFFERENTIAL_POS_AT_MINIMUM : thm
  DROP_DIFFERENTIAL_NEG_AT_MAXIMUM : thm
  DIFFERENTIAL_COMPONENT_ZERO_AT_MAXMIN : thm
  DIFFERENTIAL_ZERO_MAXMIN_COMPONENT : thm
  DIFFERENTIAL_ZERO_MAXMIN : thm
  deriving Inhabited

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
@[nospecialize]
def setupDVC [HolBase] (D : DerivativesDeps) (BDVA : DVA) : ExceptT String IO DVC := do
  -- @@SCOPE BEGIN
  let { differentiable, frechet_derivative, FRECHET_DERIVATIVE_WORKS, has_derivative,
        has_derivative_at, HAS_DERIVATIVE_AT_WITHIN, HAS_DERIVATIVE_CONST,
        HAS_DERIVATIVE_NEG, has_derivative_within, JACOBIAN_WORKS, .. } := BDVA
  let { CONJ_ASSOC, DE_MORGAN_THM, DIMINDEX_1, DIMINDEX_GE_1, .. } := D.dg.pt.cvx.core1
  let { FUN_EQ_THM, IMP_IMP, .. } := D.dg.pt.cvx.core2
  let { IN_INTER, IN_UNIV, LE_REFL, LEFT_OR_DISTRIB, NOT_EXISTS_THM, NOT_IMP, REAL_ABS_DIV,
        REAL_ABS_INV, REAL_ABS_MUL, REAL_ABS_NEG, REAL_ADD_RID, REAL_DIV_RMUL, .. } :=
        D.dg.pt.cvx.core3
  let { REAL_INV_MUL, REAL_LE_DIV2_EQ, REAL_LE_NEG2, REAL_LE_RDIV_EQ, REAL_LE_REFL,
        REAL_LT_01, REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_MIN, REAL_LT_MUL,
        REAL_LT_MUL_EQ, REAL_LT_RDIV_EQ, REAL_LT_REFL, .. } := D.dg.pt.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_RID, REAL_MUL_RZERO,
        REAL_NEG_GE0, REAL_NOT_LT, SUBSET, .. } := D.dg.pt.cvx.core5
  let { real_abs, real_div, .. } := D.dg.pt.cvx.core6
  let { REAL_HALF, .. } := D.dg.pt.cvx.misc
  let { BASIS_COMPONENT, BASIS_NONZERO, COMPONENT_LE_NORM, .. } := D.dg.pt.cvx.vec1
  let { IN_INTERVAL, LIFT_DROP, LIFT_EQ, LIFT_NUM, LINEAR_0, LINEAR_CMUL, NORM_BASIS,
        NORM_EQ_0, .. } := D.dg.pt.cvx.vec2
  let { NORM_MUL, NORM_POS_LT, REAL_ABS_NORM, .. } := D.dg.pt.cvx.vec3
  let { dist, drop, VEC_COMPONENT, VECTOR_ADD_COMPONENT, VECTOR_ADD_SUB, VECTOR_MUL_ASSOC,
        VECTOR_MUL_COMPONENT, VECTOR_MUL_EQ_0, VECTOR_MUL_LID, VECTOR_NEG_COMPONENT,
        VECTOR_SUB_COMPONENT, VECTOR_SUB_EQ, VECTOR_SUB_LDISTRIB, VECTOR_SUB_REFL,
        VECTOR_SUB_RZERO, .. } := D.dg.pt.cvx.vec4
  let { CENTRE_IN_BALL, CENTRE_IN_CBALL, .. } := D.dg.pt.cvx.top1
  let { IN_BALL, IN_CBALL, LIM_SUB, LIM_WITHIN, LIMPT_APPROACHABLE, OPEN_BALL,
        OPEN_CONTAINS_CBALL, .. } := D.dg.pt.cvx.top4
  let { TRIVIAL_LIMIT_WITHIN, .. } := D.dg.pt.cvx.top5
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON, MESON_TAC, NORM_ARITH, REAL_ARITH,
        REAL_ARITH_TAC, REAL_FIELD, SELECT_CONV, VECTOR_ARITH, .. } := D.dg.pt.cvx
  let { CONVEX_CBALL, .. } := D.dg.pt.qcvx2
  let { IN_CONVEX_SET, .. } := D.dg.pt.qcvx3
  let { REAL_ABS_ABS, REAL_ABS_NZ, .. } := D.qsession
  let { NETLIMIT_WITHIN, WITHIN_UNIV, .. } := D.qtopology2
  let { FORALL_DOT_EQ_0, LINEAR_EQ_STDBASIS, LINEAR_NEG, MATRIX_VECTOR_MUL_COMPONENT, .. }
        := D.qvec
  -- @@SCOPE END

  let FRECHET_DERIVATIVE_UNIQUE_WITHIN ← prove
   r"!f:real^M->real^N f' f'' x s.
     (f has_derivative f') (at x within s) /\
     (f has_derivative f'') (at x within s) /\
     (!i e. 1 <= i /\ i <= dimindex(:M) /\ &0 < e
            ==> ?d. &0 < abs(d) /\ abs(d) < e /\ (x + d % basis i) IN s)
     ==> f' = f''"
   (REPEAT GEN_TAC THEN REWRITE_TAC [has_derivative] THEN
    ONCE_REWRITE_TAC [CONJ_ASSOC] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"(x:real^M) limit_point_of s") ASSUME_TAC THENL
     [REWRITE_TAC [LIMPT_APPROACHABLE] THEN X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"1", ← q r"e:real"]) THEN
      ASM_REWRITE_TAC [DIMINDEX_GE_1, LE_REFL] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"(x:real^M) + d % basis 1") THEN
      ASM_REWRITE_TAC [dist] THEN ONCE_REWRITE_TAC [← GSYM VECTOR_SUB_EQ] THEN
      ASM_SIMP_TAC [VECTOR_ADD_SUB, NORM_MUL, NORM_BASIS, DIMINDEX_GE_1, LE_REFL,
                    VECTOR_MUL_EQ_0, REAL_MUL_RID, DE_MORGAN_THM, REAL_ABS_NZ,
                    BASIS_NONZERO],
      ALL_TAC] THEN
    DISCH_THEN (CONJUNCTS_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC [IMP_IMP] THEN DISCH_THEN (MP_TAC o MATCH_MP LIM_SUB) THEN
    SUBGOAL_THEN (← q r"netlimit(at x within s) = x:real^M") SUBST_ALL_TAC THENL
     [ASM_MESON_TAC [NETLIMIT_WITHIN, TRIVIAL_LIMIT_WITHIN], ALL_TAC] THEN
    REWRITE_TAC [← GSYM VECTOR_SUB_LDISTRIB, NORM_MUL] THEN
    REWRITE_TAC [← VECTOR_ARITH
     (← q r"fx - (fa + f'') - (fx - (fa + f')):real^M = f' - f''")] THEN
    DISCH_TAC THEN MATCH_MP_TAC LINEAR_EQ_STDBASIS THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC [← GSYM VECTOR_SUB_EQ] THEN
    GEN_REWRITE_TAC I [← TAUT (← q r"p = ~ ~p")] THEN
    PURE_REWRITE_TAC [← GSYM NORM_POS_LT] THEN DISCH_TAC THEN ABBREV_TAC
     (← q r"e = norm((f':real^M->real^N) (basis i) - f''(basis i :real^M))") THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [LIM_WITHIN]) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"e:real")) THEN
    ASM_REWRITE_TAC [dist, VECTOR_SUB_RZERO] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"i:num", ← q r"d:real"]) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"c:real") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(x:real^M) + c % basis i")) THEN
    ASM_REWRITE_TAC [VECTOR_ADD_SUB, NORM_MUL] THEN
    ASM_SIMP_TAC [NORM_BASIS, REAL_MUL_RID] THEN
    ASM_SIMP_TAC [LINEAR_CMUL, ← GSYM VECTOR_SUB_LDISTRIB, NORM_MUL] THEN
    REWRITE_TAC [REAL_ABS_INV, REAL_ABS_ABS] THEN
    ASM_SIMP_TAC [REAL_MUL_LINV, REAL_LT_IMP_NZ, REAL_MUL_ASSOC] THEN
    REWRITE_TAC [REAL_MUL_LID, REAL_LT_REFL])

  let FRECHET_DERIVATIVE_UNIQUE_AT ← prove
   r"!f:real^M->real^N f' f'' x.
     (f has_derivative f') (at x) /\ (f has_derivative f'') (at x)
     ==> f' = f''"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_WITHIN THEN
    MAP_EVERY EXISTS_TAC
     [← q r"f:real^M->real^N", ← q r"x:real^M", ← q r"(:real^M)"] THEN
    ASM_REWRITE_TAC [IN_UNIV, WITHIN_UNIV] THEN
    MESON_TAC [← REAL_ARITH (← q r"&0 < e ==> &0 < abs(e / &2) /\ abs(e / &2) < e")])

  let HAS_FRECHET_DERIVATIVE_UNIQUE_AT ← prove
   r"!f:real^M->real^N f' x.
        (f has_derivative f') (at x)
        ==> frechet_derivative f (at x) = f'"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    MAP_EVERY EXISTS_TAC [← q r"f:real^M->real^N", ← q r"x:real^M"] THEN
    ASM_REWRITE_TAC [frechet_derivative] THEN CONV_TAC SELECT_CONV THEN
    ASM_MESON_TAC [])

  let FRECHET_DERIVATIVE_CONST_AT ← prove
   r"!c:real^N a:real^M. frechet_derivative (\x. c) (at a) = \h. vec 0"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_FRECHET_DERIVATIVE_UNIQUE_AT THEN
    REWRITE_TAC [HAS_DERIVATIVE_CONST])

  let FRECHET_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL ← prove
   r"!f:real^M->real^N f' f'' x a b.
     (!i. 1 <= i /\ i <= dimindex(:M) ==> a$i < b$i) /\
     x IN interval[a,b] /\
     (f has_derivative f') (at x within interval[a,b]) /\
     (f has_derivative f'') (at x within interval[a,b])
     ==> f' = f''"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_WITHIN THEN
    MAP_EVERY EXISTS_TAC
     [← q r"f:real^M->real^N", ← q r"x:real^M", ← q r"interval[a:real^M,b]"] THEN
    ASM_REWRITE_TAC [] THEN
    MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"e:real"] THEN STRIP_TAC  THEN
    MATCH_MP_TAC (← MESON [] (← q r"(?a. P a \/ P(--a)) ==> (?a:real. P a)")) THEN
    EXISTS_TAC (← q r"(min ((b:real^M)$i - (a:real^M)$i) e) / &2") THEN
    REWRITE_TAC [REAL_ABS_NEG, ← GSYM LEFT_OR_DISTRIB] THEN
    REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL
     [UNDISCH_TAC (← q r"&0 < e") THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"i:num")) THEN
      ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC,
      ALL_TAC] THEN
    UNDISCH_TAC (← q r"(x:real^M) IN interval[a,b]") THEN REWRITE_TAC [IN_INTERVAL] THEN
    DISCH_TAC THEN
    ASM_SIMP_TAC [VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT,
                  BASIS_COMPONENT] THEN
    SUBGOAL_THEN
     (← q r"!P. (!j. 1 <= j /\ j <= dimindex(:M) ==> P j) <=>
          P i /\
          (!j. 1 <= j /\ j <= dimindex(:M) /\ ~(j = i) ==> P j)")
     (fun th => ONCE_REWRITE_TAC [th])
    THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    ASM_SIMP_TAC [REAL_MUL_RZERO, REAL_ADD_RID, REAL_MUL_RID] THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"i:num"))) THEN
    UNDISCH_TAC (← q r"&0 < e") THEN ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC)

  let FRECHET_DERIVATIVE_UNIQUE_WITHIN_OPEN_INTERVAL ← prove
   r"!f:real^M->real^N f' f'' x a b.
     x IN interval(a,b) /\
     (f has_derivative f') (at x within interval(a,b)) /\
     (f has_derivative f'') (at x within interval(a,b))
     ==> f' = f''"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_WITHIN THEN
    MAP_EVERY EXISTS_TAC
     [← q r"f:real^M->real^N", ← q r"x:real^M", ← q r"interval(a:real^M,b)"] THEN
    ASM_REWRITE_TAC [] THEN
    MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"e:real"] THEN STRIP_TAC  THEN
    MATCH_MP_TAC (← MESON [] (← q r"(?a. P a \/ P(--a)) ==> (?a:real. P a)")) THEN
    EXISTS_TAC (← q r"(min ((b:real^M)$i - (a:real^M)$i) e) / &3") THEN
    REWRITE_TAC [REAL_ABS_NEG, ← GSYM LEFT_OR_DISTRIB] THEN
    REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL
     [UNDISCH_TAC (← q r"&0 < e") THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL]) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"i:num")) THEN
      ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC,
      ALL_TAC] THEN
    UNDISCH_TAC (← q r"(x:real^M) IN interval(a,b)") THEN REWRITE_TAC [IN_INTERVAL] THEN
    DISCH_TAC THEN
    ASM_SIMP_TAC [VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT,
                  BASIS_COMPONENT] THEN
    SUBGOAL_THEN
     (← q r"!P. (!j. 1 <= j /\ j <= dimindex(:M) ==> P j) <=>
          P i /\
          (!j. 1 <= j /\ j <= dimindex(:M) /\ ~(j = i) ==> P j)")
     (fun th => ONCE_REWRITE_TAC [th])
    THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    ASM_SIMP_TAC [REAL_MUL_RZERO, REAL_ADD_RID, REAL_MUL_RID] THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"i:num"))) THEN
    UNDISCH_TAC (← q r"&0 < e") THEN ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC)

  let FRECHET_DERIVATIVE_AT ← prove
   r"!f:real^M->real^N f' x.
     (f has_derivative f') (at x) ==> (f' = frechet_derivative f (at x))"
   (MESON_TAC [has_derivative, FRECHET_DERIVATIVE_WORKS,
               differentiable, FRECHET_DERIVATIVE_UNIQUE_AT])

  let FRECHET_DERIVATIVE_WITHIN_CLOSED_INTERVAL ← prove
   r"!f:real^M->real^N f' x a b.
     (!i. 1 <= i /\ i <= dimindex(:M) ==> a$i < b$i) /\
     x IN interval[a,b] /\
     (f has_derivative f') (at x within interval[a,b])
     ==> frechet_derivative f (at x within interval[a,b]) = f'"
   (ASM_MESON_TAC [has_derivative, FRECHET_DERIVATIVE_WORKS,
          differentiable, FRECHET_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL])

  let DIFFERENTIAL_COMPONENT_POS_AT_MINIMUM ← prove
   r"!f:real^M->real^N f' x s k e.
        1 <= k /\ k <= dimindex(:N) /\
        x IN s /\ convex s /\ (f has_derivative f') (at x within s) /\
        &0 < e /\ (!w. w IN s INTER ball(x,e) ==> (f x)$k <= (f w)$k)
        ==> !y. y IN s ==> &0 <= (f'(y - x))$k"
   (REWRITE_TAC [has_derivative_within] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"y:real^M = x") THENL
     [ASM_MESON_TAC [VECTOR_SUB_REFL, LINEAR_0, VEC_COMPONENT, REAL_LE_REFL],
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [← GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [LIM_WITHIN]) THEN
    DISCH_THEN (MP_TAC o SPEC
      (← q r"--((f':real^M->real^N)(y - x)$k) / norm(y - x)")) THEN
    ASM_SIMP_TAC [REAL_LT_DIV, NORM_POS_LT, VECTOR_SUB_EQ,
                  NOT_EXISTS_THM, ← REAL_ARITH (← q r"&0 < --x <=> x < &0")] THEN
    X_GEN_TAC (← q r"d:real") THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ABBREV_TAC (← q r"de = min (&1) ((min d e) / &2 / norm(y - x:real^M))") THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"x + de % (y - x):real^M")) THEN
    REWRITE_TAC [dist, VECTOR_ADD_SUB, NOT_IMP, ← GSYM CONJ_ASSOC] THEN
    SUBGOAL_THEN (← q r"norm(de % (y - x):real^M) < min d e") MP_TAC THENL
     [ASM_SIMP_TAC [NORM_MUL, ← GSYM REAL_LT_RDIV_EQ,
                    NORM_POS_LT, VECTOR_SUB_EQ] THEN
      EXPAND_TAC "de" THEN MATCH_MP_TAC (← REAL_ARITH
       (← q r"&0 < de / x ==> abs(min (&1) (de / &2 / x)) < de / x")) THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_LT_MIN, NORM_POS_LT, VECTOR_SUB_EQ],
      REWRITE_TAC [REAL_LT_MIN] THEN STRIP_TAC] THEN
    SUBGOAL_THEN (← q r"&0 < de /\ de <= &1") STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "de" THEN CONJ_TAC THENL [ALL_TAC, REAL_ARITH_TAC] THEN
      ASM_SIMP_TAC [REAL_LT_MIN, REAL_LT_01, REAL_HALF, REAL_LT_DIV,
                    NORM_POS_LT, VECTOR_SUB_EQ],
      ALL_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")) THEN CONJ_TAC THENL
     [REWRITE_TAC [← VECTOR_ARITH
       (← q r"x + a % (y - x):real^N = (&1 - a) % x + a % y")] THEN
      MATCH_MP_TAC IN_CONVEX_SET THEN ASM_SIMP_TAC [REAL_LT_IMP_LE],
      DISCH_TAC] THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [NORM_MUL] THEN
    ASM_SIMP_TAC [REAL_LT_MUL, ← REAL_ARITH (← q r"&0 < x ==> &0 < abs x"),
                  NORM_POS_LT, VECTOR_SUB_EQ, VECTOR_SUB_RZERO] THEN
    MATCH_MP_TAC (← NORM_ARITH
     (← q r"abs(y$k) <= norm(y) /\ ~(abs(y$k) < e) ==> ~(norm y < e)")) THEN
    ASM_SIMP_TAC [COMPONENT_LE_NORM] THEN REWRITE_TAC [VECTOR_MUL_COMPONENT] THEN
    REWRITE_TAC [REAL_ABS_INV, REAL_ABS_MUL, REAL_ABS_NORM, REAL_ABS_ABS] THEN
    REWRITE_TAC [REAL_NOT_LT, REAL_INV_MUL, ← REAL_ARITH
     (← q r"d <= (a * inv b) * c <=> d <= (c * a) / b")] THEN
    ASM_SIMP_TAC [REAL_LE_DIV2_EQ, NORM_POS_LT, VECTOR_SUB_EQ] THEN
    ASM_SIMP_TAC [← GSYM real_div, REAL_LE_RDIV_EQ, VECTOR_SUB_COMPONENT,
      VECTOR_ADD_COMPONENT, ← REAL_ARITH (← q r"&0 < x ==> &0 < abs x")] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"fx <= fy /\ a = --b /\ b < &0 ==> a <= abs(fy - (fx + b))")) THEN
    FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP LINEAR_CMUL th])) THEN
    ASM_SIMP_TAC [real_abs, VECTOR_MUL_COMPONENT, REAL_LT_IMP_LE] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"x * y < &0 <=> &0 < x * --y")] THEN
    ASM_SIMP_TAC [REAL_LT_MUL_EQ] THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC, ASM_REAL_ARITH_TAC] THEN
    ASM_REWRITE_TAC [IN_INTER, IN_BALL, ← NORM_ARITH
     (← q r"dist(x:real^M,x + e) = norm e")])

  let DIFFERENTIAL_COMPONENT_NEG_AT_MAXIMUM ← prove
   r"!f:real^M->real^N f' x s k e.
        1 <= k /\ k <= dimindex(:N) /\
        x IN s /\ convex s /\ (f has_derivative f') (at x within s) /\
        &0 < e /\ (!w. w IN s INTER ball(x,e) ==> (f w)$k <= (f x)$k)
        ==> !y. y IN s ==> (f'(y - x))$k <= &0"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL
     [← q r"\x. --((f:real^M->real^N) x)",  ← q r"\x. --((f':real^M->real^N) x)",
      ← q r"x:real^M", ← q r"s:real^M->bool", ← q r"k:num", ← q r"e:real"]
          DIFFERENTIAL_COMPONENT_POS_AT_MINIMUM) THEN
    ASM_SIMP_TAC [HAS_DERIVATIVE_NEG] THEN
    ASM_SIMP_TAC [REAL_LE_NEG2, VECTOR_NEG_COMPONENT, REAL_NEG_GE0])

  let DROP_DIFFERENTIAL_POS_AT_MINIMUM ← prove
   r"!f:real^N->real^1 f' x s e.
        x IN s /\ convex s /\ (f has_derivative f') (at x within s) /\
        &0 < e /\ (!w. w IN s INTER ball(x,e) ==> drop(f x) <= drop(f w))
        ==> !y. y IN s ==> &0 <= drop(f'(y - x))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [drop] THEN STRIP_TAC THEN
    MATCH_MP_TAC DIFFERENTIAL_COMPONENT_POS_AT_MINIMUM THEN
    MAP_EVERY EXISTS_TAC [← q r"f:real^N->real^1", ← q r"e:real"] THEN
    ASM_REWRITE_TAC [DIMINDEX_1, LE_REFL])

  let DROP_DIFFERENTIAL_NEG_AT_MAXIMUM ← prove
   r"!f:real^N->real^1 f' x s e.
        x IN s /\ convex s /\ (f has_derivative f') (at x within s) /\
        &0 < e /\ (!w. w IN s INTER ball(x,e) ==> drop(f w) <= drop(f x))
        ==> !y. y IN s ==> drop(f'(y - x)) <= &0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [drop] THEN STRIP_TAC THEN
    MATCH_MP_TAC DIFFERENTIAL_COMPONENT_NEG_AT_MAXIMUM THEN
    MAP_EVERY EXISTS_TAC [← q r"f:real^N->real^1", ← q r"e:real"] THEN
    ASM_REWRITE_TAC [DIMINDEX_1, LE_REFL])

  let DIFFERENTIAL_COMPONENT_ZERO_AT_MAXMIN ← prove
   r"!f:real^M->real^N f' x s k.
        1 <= k /\ k <= dimindex(:N) /\
        x IN s /\ open s /\ (f has_derivative f') (at x) /\
        ((!w. w IN s ==> (f w)$k <= (f x)$k) \/
         (!w. w IN s ==> (f x)$k <= (f w)$k))
        ==> !h. (f' h)$k = &0"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"x:real^M")) THEN ASM_REWRITE_TAC [SUBSET] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"e:real") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [MP_TAC (← ISPECL [← q r"f:real^M->real^N", ← q r"f':real^M->real^N",
                        ← q r"x:real^M", ← q r"cball(x:real^M,e)", ← q r"k:num", ← q r"e:real"]
          DIFFERENTIAL_COMPONENT_NEG_AT_MAXIMUM),
      MP_TAC (← ISPECL [← q r"f:real^M->real^N", ← q r"f':real^M->real^N",
                        ← q r"x:real^M", ← q r"cball(x:real^M,e)", ← q r"k:num", ← q r"e:real"]
          DIFFERENTIAL_COMPONENT_POS_AT_MINIMUM)] THEN
    ASM_SIMP_TAC [HAS_DERIVATIVE_AT_WITHIN, CENTRE_IN_CBALL,
                  CONVEX_CBALL, REAL_LT_IMP_LE, IN_INTER] THEN
    DISCH_THEN (LABEL_TAC "*") THEN X_GEN_TAC (← q r"h:real^M") THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [has_derivative_at]) THEN
    (ASM_CASES_TAC (← q r"h:real^M = vec 0") THENL
      [ASM_MESON_TAC [LINEAR_0, VEC_COMPONENT], ALL_TAC]) THEN
    REMOVE_THEN "*" (fun th => tactic_of do
      pure (MP_TAC (← SPEC (← q r"x + e / norm h % h:real^M") th) THEN
            MP_TAC (← SPEC (← q r"x - e / norm h % h:real^M") th))) THEN
    REWRITE_TAC [IN_CBALL, ← NORM_ARITH
     (← q r"dist(x:real^N,x - e) = norm e /\ dist(x:real^N,x + e) = norm e")] THEN
    REWRITE_TAC [NORM_MUL, REAL_ABS_DIV, REAL_ABS_NORM] THEN
    ASM_SIMP_TAC [real_abs, REAL_DIV_RMUL, NORM_EQ_0, REAL_LT_IMP_LE,
                  REAL_LE_REFL] THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"x - e - x:real^N = --e /\ (x + e) - x = e")] THEN
    FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP LINEAR_NEG th])) THEN
    REWRITE_TAC [IMP_IMP, ← REAL_ARITH (← q r"&0 <= --x /\ &0 <= x <=> x = &0"),
      VECTOR_NEG_COMPONENT, ← REAL_ARITH (← q r"--x <= &0 /\ x <= &0 <=> x = &0")] THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"(*) (norm(h:real^M) / e)")) THEN
    REWRITE_TAC [← GSYM VECTOR_MUL_COMPONENT] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (REWRITE_TAC [← GSYM (← MATCH_MP LINEAR_CMUL th)])) THEN
    REWRITE_TAC [REAL_MUL_RZERO, VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC [← REAL_FIELD (← q r"~(x = &0) /\ ~(y = &0) ==> x / y * y / x = &1"),
                  NORM_EQ_0, REAL_LT_IMP_NZ, VECTOR_MUL_LID])

  let DIFFERENTIAL_ZERO_MAXMIN_COMPONENT ← prove
   r"!f:real^M->real^N x e k.
        1 <= k /\ k <= dimindex(:N) /\ &0 < e /\
        ((!y. y IN ball(x,e) ==> (f y)$k <= (f x)$k) \/
         (!y. y IN ball(x,e) ==> (f x)$k <= (f y)$k)) /\
        f differentiable (at x)
        ==> (jacobian f (at x) $ k = vec 0)"
   (REWRITE_TAC [JACOBIAN_WORKS] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL
     [← q r"f:real^M->real^N", ← q r"\h:real^M. jacobian (f:real^M->real^N) (at x) ** h",
      ← q r"x:real^M", ← q r"ball(x:real^M,e)", ← q r"k:num"]
        DIFFERENTIAL_COMPONENT_ZERO_AT_MAXMIN) THEN
    ASM_REWRITE_TAC [CENTRE_IN_BALL, OPEN_BALL] THEN
    ASM_SIMP_TAC [MATRIX_VECTOR_MUL_COMPONENT, FORALL_DOT_EQ_0])

  let DIFFERENTIAL_ZERO_MAXMIN ← prove
   r"!f:real^N->real^1 f' x s.
        x IN s /\ open s /\ (f has_derivative f') (at x) /\
        ((!y. y IN s ==> drop(f y) <= drop(f x)) \/
         (!y. y IN s ==> drop(f x) <= drop(f y)))
        ==> (f' = \v. vec 0)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^N->real^1", ← q r"f':real^N->real^1",
                      ← q r"x:real^N", ← q r"s:real^N->bool", ← q r"1:num"]
          DIFFERENTIAL_COMPONENT_ZERO_AT_MAXMIN) THEN
    ASM_REWRITE_TAC [← GSYM drop, DIMINDEX_1, LE_REFL] THEN
    REWRITE_TAC [← GSYM LIFT_EQ, LIFT_NUM, FUN_EQ_THM, LIFT_DROP])

  pure { FRECHET_DERIVATIVE_UNIQUE_WITHIN, FRECHET_DERIVATIVE_UNIQUE_AT,
         HAS_FRECHET_DERIVATIVE_UNIQUE_AT, FRECHET_DERIVATIVE_CONST_AT,
         FRECHET_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL,
         FRECHET_DERIVATIVE_UNIQUE_WITHIN_OPEN_INTERVAL, FRECHET_DERIVATIVE_AT,
         FRECHET_DERIVATIVE_WITHIN_CLOSED_INTERVAL, DIFFERENTIAL_COMPONENT_POS_AT_MINIMUM,
         DIFFERENTIAL_COMPONENT_NEG_AT_MAXIMUM, DROP_DIFFERENTIAL_POS_AT_MINIMUM,
         DROP_DIFFERENTIAL_NEG_AT_MAXIMUM, DIFFERENTIAL_COMPONENT_ZERO_AT_MAXMIN,
         DIFFERENTIAL_ZERO_MAXMIN_COMPONENT, DIFFERENTIAL_ZERO_MAXMIN }

/- ------------------------------------------------------------------------- -/
/- Rolle, the mean value theorems, bounds on and from derivatives, zero      -/
/- derivatives, discreteness of preimages.  (derivatives.ml 1121-1578)       -/
/- ------------------------------------------------------------------------- -/

structure DVD where
  ROLLE : thm
  MVT : thm
  MVT_SIMPLE : thm
  MVT_VERY_SIMPLE : thm
  MVT_SEGMENT : thm
  MVT_SEGMENT_SIMPLE : thm
  MVT_GENERAL : thm
  DIFFERENTIABLE_BOUND : thm
  ONORM_DERIVATIVES_LE : thm
  HAS_DERIVATIVE_ZERO_CONSTANT : thm
  HAS_DERIVATIVE_ZERO_UNIQUE : thm
  HAS_DERIVATIVE_ZERO_CONNECTED_CONSTANT : thm
  HAS_DERIVATIVE_ZERO_CONNECTED_UNIQUE : thm
  DIFFERENTIABLE_DISCRETE_PREIMAGES : thm
  DIFFERENTIABLE_DISCRETE_PREIMAGES_CLOSED : thm
  DIFFERENTIABLE_COUNTABLE_PREIMAGES : thm
  DIFFERENTIABLE_FINITE_PREIMAGES : thm
  DIFFERENTIABLE_FINITE_PREIMAGES_GEN : thm
  deriving Inhabited

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
@[nospecialize]
def setupDVD [HolBase] (D : DerivativesDeps) (BDVA : DVA) (BDVB : DVB) (BDVC : DVC) : ExceptT String IO DVD := do
  -- @@SCOPE BEGIN
  let { differentiable, differentiable_on, DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT,
        has_derivative, HAS_DERIVATIVE_ADD, has_derivative_at, HAS_DERIVATIVE_AT_WITHIN,
        HAS_DERIVATIVE_CMUL, HAS_DERIVATIVE_CONST, HAS_DERIVATIVE_ID,
        HAS_DERIVATIVE_LIFT_DOT, HAS_DERIVATIVE_LINEAR, HAS_DERIVATIVE_SUB,
        HAS_DERIVATIVE_VMUL_DROP, has_derivative_within, HAS_DERIVATIVE_WITHIN_OPEN,
        LINEAR_FRECHET_DERIVATIVE, .. } := BDVA
  let { DIFF_CHAIN_WITHIN, DIFFERENTIABLE_IMP_CONTINUOUS_ON,
        DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN, HAS_DERIVATIVE_WITHIN_SUBSET, .. } := BDVB
  let { DIFFERENTIAL_ZERO_MAXMIN, .. } := BDVC
  let { CONJ_ASSOC, DE_MORGAN_THM, DIMINDEX_1, EQ_IMP, ETA_AX, EXISTS_IN_IMAGE, EXTENSION,
        FORALL_AND_THM, .. } := D.dg.pt.cvx.core1
  let { FORALL_IN_IMAGE, FUN_EQ_THM, IMP_CONJ, IMP_IMP, IN_DELETE, .. } := D.dg.pt.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, IN_SING, IN_UNION, LE_REFL, MEMBER_NOT_EMPTY, MONO_EXISTS,
        MONO_FORALL, NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, REAL_ABS_INV, REAL_ABS_POS,
        REAL_ADD_LDISTRIB, REAL_DIV_RMUL, .. } := D.dg.pt.cvx.core3
  let { REAL_LE_LMUL, REAL_LE_LT, REAL_LE_RDIV_EQ, REAL_LE_REFL, REAL_LE_RMUL,
        REAL_LE_TRANS, REAL_LT_01, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_LDIV_EQ,
        REAL_LT_MIN, REAL_LT_REFL, .. } := D.dg.pt.cvx.core4
  let { REAL_MUL_LZERO, REAL_MUL_SYM, REAL_NOT_LT, REAL_POW_2, REAL_SUB_LT, REAL_SUB_REFL,
        REAL_SUB_RZERO, SUBSET, SUBSET_RESTRICT, .. } := D.dg.pt.cvx.core5
  let { o_DEF, o_THM, real_div, UNWIND_THM2, .. } := D.dg.pt.cvx.core6
  let { DIST_0, DIST_NZ, DIST_REFL, DIST_SYM, DOT_RSUB, .. } := D.dg.pt.cvx.vec1
  let { DROP_CMUL, DROP_EQ, DROP_SUB, DROP_VEC, IN_INTERVAL, INTERVAL_OPEN_SUBSET_CLOSED,
        INTERVAL_SING, LIFT_ADD, LIFT_DROP, LIFT_EQ, LIFT_SUB, LINEAR_0, NORM_0,
        NORM_CAUCHY_SCHWARZ, .. } := D.dg.pt.cvx.vec2
  let { NORM_LE_0, NORM_LIFT, NORM_MUL, NORM_NEG, NORM_POS_LE, NORM_POS_LT, NORM_POW_2,
        NORM_SUB, REAL_ABS_NORM, .. } := D.dg.pt.cvx.vec3
  let { dist, drop, VEC_COMPONENT, VECTOR_ADD_LID, VECTOR_ADD_RID, VECTOR_ADD_SUB,
        VECTOR_MUL_LID, VECTOR_MUL_LZERO, VECTOR_SUB_EQ, VECTOR_SUB_REFL, VECTOR_SUB_RZERO,
        .. } := D.dg.pt.cvx.vec4
  let { TRIVIAL_LIMIT_SEQUENTIALLY, .. } := D.dg.pt.cvx.met
  let { CONNECTED_CLOPEN, .. } := D.dg.pt.cvx.top2
  let { CONTINUOUS_ON_ADD, CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_CONST,
        CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN, CONTINUOUS_ON_ID, CONTINUOUS_ON_LIFT_DOT,
        CONTINUOUS_ON_SUB, CONTINUOUS_ON_SUBSET, EVENTUALLY_AT, .. } := D.dg.pt.cvx.top3
  let { IN_BALL, LIM_CONST, LIM_NULL_ADD, LIM_NULL_COMPARISON, LIM_TRANSFORM_WITHIN_SET,
        LIM_UNIQUE, LIM_WITHIN, LIMPT_APPROACHABLE, OPEN_CONTAINS_BALL, .. } :=
        D.dg.pt.cvx.top4
  let { open_in, OPEN_INTERVAL, SEGMENT_1, SEGMENT_CLOSED_OPEN, SEGMENT_OPEN_SUBSET_CLOSED,
        .. } := D.dg.pt.cvx.top5
  let { ASM_MESON_TAC, MESON, MESON_TAC, NORM_ARITH, REAL_ARITH, SET_RULE, SET_TAC,
        VECTOR_ARITH, .. } := D.dg.pt.cvx
  let { CONVEX_ALT, CONVEX_BALL, .. } := D.dg.pt.qcvx2
  let { EVENTUALLY_AND, .. } := D.dg.qmetric
  let { CONTINUOUS_CLOSED_IN_PREIMAGE_CONSTANT, CONTINUOUS_ON_CMUL, .. } := D.dg.qtopology1
  let { tendsto, .. } := D.dg.qtopology2
  let { LINEAR_ID, .. } := D.dg.qvec
  let { SEGMENT_IMAGE_INTERVAL, .. } := D.qconvex
  let { DET_MATRIX_EQ_0, .. } := D.qdet
  let { ALWAYS_EVENTUALLY, EVENTUALLY_MP, .. } := D.qmetric
  let { CONTINUOUS_IVT_LOCAL_EXTREMUM, .. } := D.qpaths
  let { REAL_LE_LCANCEL_IMP, REAL_LE_TRANS_LTE, .. } := D.qsession
  let { CLOSED_LIMPT, CONTINUOUS_ON_SEQUENTIALLY, CONTINUOUS_ON_VMUL,
        DISCRETE_EQ_FINITE_COMPACT, DISCRETE_IMP_COUNTABLE, DISCRETE_SET,
        EVENTUALLY_AT_ZERO, LIMPT_SEQUENTIAL, LIMPT_SUBSET, .. } := D.qtopology1
  let { LIM_NULL_NORM, ONORM_LE_EVENTUALLY, .. } := D.qtopology2
  let { FORALL_DIMINDEX_1, LINEAR_INVERTIBLE_BOUNDED_BELOW_POS, LINEAR_VMUL_DROP, ONORM,
        ONORM_CONST, .. } := D.qvec
  -- @@SCOPE END

  let ROLLE ← prove
   r"!f:real^1->real^1 f' a b.
        drop a < drop b /\ (f a = f b) /\
        f continuous_on interval[a,b] /\
        (!x. x IN interval(a,b) ==> (f has_derivative f'(x)) (at x))
        ==> ?x. x IN interval(a,b) /\ (f'(x) = \v. vec 0)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^1->real^1", ← q r"a:real^1", ← q r"b:real^1"]
          CONTINUOUS_IVT_LOCAL_EXTREMUM) THEN
    ASM_SIMP_TAC [SEGMENT_1, REAL_LT_IMP_LE] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [REAL_LT_REFL], MATCH_MP_TAC MONO_EXISTS] THEN
    X_GEN_TAC (← q r"c:real^1") THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC DIFFERENTIAL_ZERO_MAXMIN THEN MAP_EVERY EXISTS_TAC
     [← q r"f:real^1->real^1", ← q r"c:real^1", ← q r"interval(a:real^1,b)"] THEN
    ASM_MESON_TAC [INTERVAL_OPEN_SUBSET_CLOSED, SUBSET, OPEN_INTERVAL])

  let MVT ← prove
   r"!f:real^1->real^1 f' a b.
        drop a < drop b /\
        f continuous_on interval[a,b] /\
        (!x. x IN interval(a,b) ==> (f has_derivative f'(x)) (at x))
        ==> ?x. x IN interval(a,b) /\ (f(b) - f(a) = f'(x) (b - a))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"\x. f(x) - (drop(f b - f a) / drop(b - a)) % x",
                     ← q r"\k:real^1 x:real^1.
                      f'(k)(x) - (drop(f b - f a) / drop(b - a)) % x",
                     ← q r"a:real^1", ← q r"b:real^1"]
                 ROLLE) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC [CONTINUOUS_ON_SUB, CONTINUOUS_ON_CMUL, CONTINUOUS_ON_ID] THEN
      CONJ_TAC THENL
       [REWRITE_TAC [← VECTOR_ARITH
         (← q r"(fa - k % a = fb - k % b) <=> (fb - fa = k % (b - a))")],
        REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
        ASM_SIMP_TAC [HAS_DERIVATIVE_CMUL, HAS_DERIVATIVE_ID, ETA_AX]],
      MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [FUN_EQ_THM] THEN
      X_GEN_TAC (← q r"x:real^1") THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC (← q r"b - a:real^1")))] THEN
    SIMP_TAC [VECTOR_SUB_EQ, ← GSYM DROP_EQ, DROP_SUB, DROP_CMUL] THEN
    ASM_SIMP_TAC [REAL_DIV_RMUL, REAL_SUB_LT, REAL_LT_IMP_NZ])

  let MVT_SIMPLE ← prove
   r"!f:real^1->real^1 f' a b.
        drop a < drop b /\
        (!x. x IN interval[a,b]
             ==> (f has_derivative f'(x)) (at x within interval[a,b]))
        ==> ?x. x IN interval(a,b) /\ (f(b) - f(a) = f'(x) (b - a))"
   (MP_TAC MVT THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
      ASM_MESON_TAC [differentiable_on, differentiable],
      ASM_MESON_TAC [HAS_DERIVATIVE_WITHIN_OPEN, OPEN_INTERVAL,
                     HAS_DERIVATIVE_WITHIN_SUBSET, INTERVAL_OPEN_SUBSET_CLOSED,
                     SUBSET]])

  let MVT_VERY_SIMPLE ← prove
   r"!f:real^1->real^1 f' a b.
        drop a <= drop b /\
        (!x. x IN interval[a,b]
             ==> (f has_derivative f'(x)) (at x within interval[a,b]))
        ==> ?x. x IN interval[a,b] /\ (f(b) - f(a) = f'(x) (b - a))"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"b:real^1 = a") THENL
     [ASM_REWRITE_TAC [VECTOR_SUB_REFL] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"a:real^1")) THEN
      REWRITE_TAC [INTERVAL_SING, IN_SING, has_derivative, UNWIND_THM2] THEN
      MESON_TAC [LINEAR_0],
      ASM_REWRITE_TAC [REAL_LE_LT, DROP_EQ] THEN
      DISCH_THEN (MP_TAC o MATCH_MP MVT_SIMPLE) THEN
      MATCH_MP_TAC MONO_EXISTS THEN
      SIMP_TAC [← REWRITE_RULE [SUBSET] INTERVAL_OPEN_SUBSET_CLOSED]])

  let MVT_SEGMENT ← prove
   r"!f:real^N->real^1 f' a b.
        ~(a = b) /\
        f continuous_on segment[a,b] /\
        (!x. x IN segment(a,b)

             ==> (f has_derivative f' x) (at x within segment(a,b)))
        ==> ?c. c IN segment(a,b) /\ f(b) - f(a) = f'(c) (b - a)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"(f:real^N->real^1) o (\x. (&1 - drop x) % a + drop x % b)",
                      ← q r"\x. (f':real^N->real^N->real^1)
                        ((&1 - drop x) % a + drop x % b) o
                        (\x. drop x % (b - a))",
                      ← q r"vec 0:real^1", ← q r"vec 1:real^1"]
          MVT) THEN
    REWRITE_TAC [DROP_VEC, REAL_LT_01, o_THM] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        ASM_SIMP_TAC [← GSYM SEGMENT_IMAGE_INTERVAL] THEN
        SIMP_TAC [CONTINUOUS_ON_ADD, CONTINUOUS_ON_VMUL, o_DEF, LIFT_DROP,
                  CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID, LIFT_SUB,
                  CONTINUOUS_ON_SUB],
        X_GEN_TAC (← q r"x:real^1") THEN DISCH_TAC THEN
        FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP
         (← MESON [HAS_DERIVATIVE_WITHIN_OPEN]
           (← q r"a IN s
            ==> open s /\ (f has_derivative f') (at a within s)
                ==> (f has_derivative f') (at a)"))) THEN
        REWRITE_TAC [OPEN_INTERVAL] THEN
        MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN
        ASM_SIMP_TAC [OPEN_INTERVAL, ← GSYM SEGMENT_IMAGE_INTERVAL] THEN
        CONJ_TAC THENL
         [GEN_REWRITE_TAC (LAND_CONV o ABS_CONV) [← GSYM VECTOR_ADD_LID] THEN
          REWRITE_TAC [← VECTOR_ARITH
           (← q r"(&1 - x) % a + x % b:real^N = a + x % (b - a)")] THEN
          MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
          REWRITE_TAC [HAS_DERIVATIVE_CONST] THEN
          MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
          MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC [LINEAR_ID],
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_SIMP_TAC [SEGMENT_IMAGE_INTERVAL] THEN ASM SET_TAC []]],
    ASM_SIMP_TAC [SEGMENT_IMAGE_INTERVAL, EXISTS_IN_IMAGE] THEN
    REWRITE_TAC [REAL_SUB_RZERO, VECTOR_SUB_RZERO, DROP_VEC] THEN
    REWRITE_TAC [VECTOR_MUL_LZERO, VECTOR_MUL_LID, REAL_SUB_REFL] THEN
    REWRITE_TAC [VECTOR_ADD_LID, VECTOR_ADD_RID]])

  let MVT_SEGMENT_SIMPLE ← prove
   r"!f:real^N->real^1 f' a b.
        ~(a = b) /\
        (!x. x IN segment[a,b]
             ==> (f has_derivative f' x) (at x within segment(a,b)))
        ==> ?c. c IN segment(a,b) /\ f(b) - f(a) = f'(c) (b - a)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC MVT_SEGMENT THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [ALL_TAC,
      ASM_MESON_TAC [← REWRITE_RULE [SUBSET] SEGMENT_OPEN_SUBSET_CLOSED]] THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC [differentiable_on] THEN
    X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
    REWRITE_TAC [differentiable] THEN
    EXISTS_TAC (← q r"(f':real^N->real^N->real^1) x") THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real^N")) THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC [has_derivative_within] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC LIM_TRANSFORM_WITHIN_SET THEN
    REWRITE_TAC [EVENTUALLY_AT] THEN
    ASM_CASES_TAC (← q r"x:real^N = a \/ x:real^N = b") THENL
     [EXISTS_TAC (← q r"dist(a:real^N,b)") THEN
      FIRST_X_ASSUM (DISJ_CASES_THEN SUBST_ALL_TAC),
      RULE_ASSUM_TAC (REWRITE_RULE [DE_MORGAN_THM]) THEN
      EXISTS_TAC (← q r"min (dist(x:real^N,a)) (dist(x,b))")] THEN
    ASM_SIMP_TAC [← GSYM DIST_NZ, REAL_LT_MIN, SEGMENT_CLOSED_OPEN, IN_UNION] THEN
    SIMP_TAC [IN_INSERT, NOT_IN_EMPTY] THEN MESON_TAC [DIST_SYM, REAL_LT_REFL])

  let MVT_GENERAL ← prove
   r"!f:real^1->real^N f' a b.
        drop a < drop b /\
        f continuous_on interval[a,b] /\
        (!x. x IN interval(a,b) ==> (f has_derivative f'(x)) (at x))
        ==> ?x. x IN interval(a,b) /\
                norm(f(b) - f(a)) <= norm(f'(x) (b - a))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"(lift o (\y. (f(b) - f(a)) dot y)) o (f:real^1->real^N)",
                     ← q r"\x t. lift((f(b:real^1) - f(a)) dot
                        ((f':real^1->real^1->real^N) x t))",
                     ← q r"a:real^1", ← q r"b:real^1"]  MVT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [CONTINUOUS_ON_LIFT_DOT, CONTINUOUS_ON_COMPOSE] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC [o_DEF] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LIFT_DOT THEN ASM_SIMP_TAC [ETA_AX],
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"x:real^1") THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC [o_THM, ← GSYM LIFT_SUB, ← GSYM DOT_RSUB, LIFT_EQ] THEN
    DISCH_TAC THEN ASM_CASES_TAC (← q r"(f:real^1->real^N) b = f a") THENL
     [ASM_REWRITE_TAC [VECTOR_SUB_REFL, NORM_0, NORM_POS_LE], ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
    EXISTS_TAC (← q r"norm((f:real^1->real^N) b - f a)") THEN
    ASM_REWRITE_TAC [NORM_POS_LT, VECTOR_SUB_EQ, ← GSYM REAL_POW_2] THEN
    ASM_REWRITE_TAC [NORM_POW_2, NORM_CAUCHY_SCHWARZ])

  let DIFFERENTIABLE_BOUND ← prove
   r"!f:real^M->real^N f' s B.
        convex s /\
        (!x. x IN s ==> (f has_derivative f'(x)) (at x within s)) /\
        (!x. x IN s ==> onorm(f'(x)) <= B)
        ==> !x y. x IN s /\ y IN s ==> norm(f(x) - f(y)) <= B * norm(x - y)"
   (ONCE_REWRITE_TAC [NORM_SUB] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
      (← q r"!x y. x IN s ==> norm((f':real^M->real^M->real^N)(x) y) <= B * norm(y)")
    ASSUME_TAC THENL
     [ASM_MESON_TAC [ONORM, has_derivative, REAL_LE_TRANS, NORM_POS_LE,
                     REAL_LE_RMUL], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!u. u IN interval[vec 0,vec 1] ==> (x + drop u % (y - x) :real^M) IN s")
    ASSUME_TAC THENL
     [REWRITE_TAC [IN_INTERVAL, FORALL_DIMINDEX_1, drop] THEN
      SIMP_TAC [VEC_COMPONENT, LE_REFL, DIMINDEX_1] THEN
      REWRITE_TAC [← VECTOR_ARITH (← q r"x + u % (y - x) = (&1 - u) % x + u % y")] THEN
      ASM_MESON_TAC [CONVEX_ALT],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!u. u IN interval(vec 0,vec 1) ==> (x + drop u % (y - x) :real^M) IN s")
    ASSUME_TAC THENL
     [ASM_MESON_TAC [SUBSET, INTERVAL_OPEN_SUBSET_CLOSED], ALL_TAC] THEN
    MP_TAC (← SPECL
     [← q r"(f:real^M->real^N) o (\u. x + drop u % (y - x))",
      ← q r"\u. (f':real^M->real^M->real^N) (x + drop u % (y - x)) o
           (\u. vec 0 + drop u % (y - x))",
      ← q r"vec 0:real^1", ← q r"vec 1:real^1"] MVT_GENERAL) THEN
    REWRITE_TAC [o_THM, DROP_VEC, ← VECTOR_ARITH (← q r"x + &1 % (y - x) = y"),
                 VECTOR_MUL_LZERO, VECTOR_SUB_RZERO, VECTOR_ADD_RID] THEN
    REWRITE_TAC [VECTOR_MUL_LID] THEN ANTS_TAC THENL
     [ALL_TAC, ASM_MESON_TAC [VECTOR_ADD_LID, REAL_LE_TRANS]] THEN
    REWRITE_TAC [REAL_LT_01] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC [CONTINUOUS_ON_ADD, CONTINUOUS_ON_CONST, CONTINUOUS_ON_VMUL,
                o_DEF, LIFT_DROP, CONTINUOUS_ON_ID] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC (← q r"s:real^M->bool") THEN
      ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC [DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN, differentiable,
                     CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN],
      ALL_TAC] THEN
    X_GEN_TAC (← q r"a:real^1") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"a IN interval(vec 0:real^1,vec 1) /\
                  open(interval(vec 0:real^1,vec 1))")
    MP_TAC THENL [ASM_MESON_TAC [OPEN_INTERVAL], ALL_TAC] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (ONCE_REWRITE_TAC [← GSYM (← MATCH_MP
        HAS_DERIVATIVE_WITHIN_OPEN th)])) THEN
    MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN
    ASM_SIMP_TAC [HAS_DERIVATIVE_ADD, HAS_DERIVATIVE_CONST,
                  HAS_DERIVATIVE_VMUL_DROP, HAS_DERIVATIVE_ID] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC (← q r"s:real^M->bool") THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC [INTERVAL_OPEN_SUBSET_CLOSED, SUBSET])

  let ONORM_DERIVATIVES_LE ← prove
   r"!f:real^M->real^N g:real^M->real^P f' g' x.
        (f has_derivative f') (at x) /\
        (g has_derivative g') (at x) /\
        eventually (\y. norm(f y - f x) <= norm(g y - g x)) (at x)
        ==> onorm f' <= onorm g'"
   (REPEAT GEN_TAC THEN REWRITE_TAC [CONJ_ASSOC] THEN
    DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
    ONCE_REWRITE_TAC [REAL_LE_TRANS_LTE] THEN
    X_GEN_TAC (← q r"b:real") THEN DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"((\y. inv(norm(y - x:real^M)) %
            lift((norm(f y - f x:real^N) - norm(g y - g x:real^P)) -
                 (norm(f'(y - x):real^N) - norm(g'(y - x):real^P))))
       --> vec 0) (at x)")
    MP_TAC THENL
     [FIRST_X_ASSUM (CONJUNCTS_THEN (MP_TAC o CONJUNCT2 o
       GEN_REWRITE_RULE I [has_derivative_at])) THEN
      REWRITE_TAC [IMP_IMP] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [LIM_NULL_NORM] THEN
      DISCH_THEN (MP_TAC o MATCH_MP LIM_NULL_ADD) THEN
      REWRITE_TAC [← GSYM LIFT_ADD] THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] LIM_NULL_COMPARISON) THEN
      MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC (← q r"y:real^M") THEN
      REWRITE_TAC [NORM_MUL, ← GSYM REAL_ADD_LDISTRIB] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_ABS_POS] THEN
      REWRITE_TAC [NORM_LIFT] THEN CONV_TAC (fun t => NORM_ARITH t),
      REWRITE_TAC [tendsto] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"b - onorm(g':real^M->real^P)")) THEN
      ASM_REWRITE_TAC [REAL_SUB_LT] THEN FIRST_ASSUM (fun th => tactic_of do
       pure (MP_TAC th THEN
        REWRITE_TAC [IMP_IMP] THEN
        GEN_REWRITE_TAC LAND_CONV [← GSYM EVENTUALLY_AND])) THEN
      FIRST_ASSUM (CONJUNCTS_THEN (ASSUME_TAC o CONJUNCT1 o
        GEN_REWRITE_RULE I [has_derivative_at])) THEN
      ASM_SIMP_TAC [ONORM_LE_EVENTUALLY] THEN
      GEN_REWRITE_TAC LAND_CONV [EVENTUALLY_AT_ZERO] THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] EVENTUALLY_MP) THEN
      REWRITE_TAC [EVENTUALLY_AT, DIST_0, VECTOR_ADD_SUB, NORM_POS_LT] THEN
      EXISTS_TAC (← q r"&1") THEN REWRITE_TAC [REAL_LT_01] THEN X_GEN_TAC (← q r"h:real^M") THEN
      STRIP_TAC THEN REWRITE_TAC [NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
      REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_MUL_SYM] (← GSYM real_div)] THEN
      ASM_SIMP_TAC [REAL_LT_LDIV_EQ, NORM_POS_LT, NORM_LIFT] THEN
      MATCH_MP_TAC (← REAL_ARITH
       (← q r"abs g <= x * h
        ==> u <= v /\ abs(u - v - (f - g)) < (b - x) * h ==> f <= b * h")) THEN
      ASM_SIMP_TAC [REAL_ABS_NORM, ONORM]])

  let HAS_DERIVATIVE_ZERO_CONSTANT ← prove
   r"!f:real^M->real^N s.
        convex s /\
        (!x. x IN s ==> (f has_derivative (\h. vec 0)) (at x within s))
        ==> ?c. !x. x IN s ==> f(x) = c"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^M->real^N", ← q r"(\x h. vec 0):real^M->real^M->real^N",
                      ← q r"s:real^M->bool", ← q r"&0"] DIFFERENTIABLE_BOUND) THEN
    ASM_REWRITE_TAC [REAL_MUL_LZERO, ONORM_CONST, NORM_0, REAL_LE_REFL] THEN
    SIMP_TAC [NORM_LE_0, VECTOR_SUB_EQ] THEN MESON_TAC [])

  let HAS_DERIVATIVE_ZERO_UNIQUE ← prove
   r"!f s a c. convex s /\ a IN s /\ f a = c /\
             (!x. x IN s ==> (f has_derivative (\h. vec 0)) (at x within s))
             ==> !x. x IN s ==> f x = c"
   (MESON_TAC [HAS_DERIVATIVE_ZERO_CONSTANT])

  let HAS_DERIVATIVE_ZERO_CONNECTED_CONSTANT ← prove
   r"!f:real^M->real^N s.
        open s /\ connected s /\
        (!x. x IN s ==> (f has_derivative (\h. vec 0)) (at x))
        ==> ?c. !x. x IN s ==> f(x) = c"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"s:real^M->bool = {}") THEN ASM_REWRITE_TAC [NOT_IN_EMPTY] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"a:real^M")) THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOPEN]) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"{x | x IN s /\ (f:real^M->real^N) x = f a}")) THEN
    ANTS_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN CONJ_TAC THENL
     [SIMP_TAC [open_in, SUBSET, IN_ELIM_THM] THEN
      X_GEN_TAC (← q r"x:real^M") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"x:real^M")) THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"e:real") THEN
      REWRITE_TAC [SUBSET, IN_BALL] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      MP_TAC (← ISPECL [← q r"f:real^M->real^N", ← q r"ball(x:real^M,e)"]
          HAS_DERIVATIVE_ZERO_CONSTANT) THEN
      REWRITE_TAC [IN_BALL, CONVEX_BALL] THEN
      ASM_MESON_TAC [HAS_DERIVATIVE_AT_WITHIN, DIST_SYM, DIST_REFL],
      MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_CONSTANT THEN
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
      ASM_SIMP_TAC [DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT] THEN
      ASM_MESON_TAC [differentiable]])

  let HAS_DERIVATIVE_ZERO_CONNECTED_UNIQUE ← prove
   r"!f s a c. open s /\ connected s /\ a IN s /\ f a = c /\
             (!x. x IN s ==> (f has_derivative (\h. vec 0)) (at x))
             ==> !x. x IN s ==> f x = c"
   (MESON_TAC [HAS_DERIVATIVE_ZERO_CONNECTED_CONSTANT])

  let DIFFERENTIABLE_DISCRETE_PREIMAGES ← prove
   r"!f f' s y:real^N.
        (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
        (!x. x IN s /\ f(x) = y ==> ~(det(matrix (f' x)) = &0))
        ==> {l | l IN s /\ l limit_point_of {x | x IN s /\ f x = y}} = {}"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"x0:real^N") THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(f:real^N->real^N) x0 = y") ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [LIMPT_SEQUENTIAL]) THEN
      REWRITE_TAC [IN_DELETE, IN_ELIM_THM, FORALL_AND_THM] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"x:num->real^N") STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC (← ISPEC (← q r"sequentially") LIM_UNIQUE) THEN
      EXISTS_TAC (← q r"(f:real^N->real^N) o (x:num->real^N)") THEN
      REWRITE_TAC [TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
       [SUBGOAL_THEN (← q r"(f:real^N->real^N) continuous_on s") MP_TAC THENL
         [ASM_MESON_TAC [DIFFERENTIABLE_IMP_CONTINUOUS_ON,
                         differentiable_on, differentiable],
          REWRITE_TAC [CONTINUOUS_ON_SEQUENTIALLY] THEN
          DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC []],
        ASM_REWRITE_TAC [o_DEF, LIM_CONST]],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x0:real^N")) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [has_derivative]) THEN
    ASM_SIMP_TAC [DET_MATRIX_EQ_0] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->real^N") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"(f':real^N->real^N->real^N) x0", ← q r"g:real^N->real^N"]
          LINEAR_INVERTIBLE_BOUNDED_BELOW_POS) THEN
    ASM_SIMP_TAC [LINEAR_FRECHET_DERIVATIVE] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [← GSYM has_derivative]) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"B:real") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"((f:real^N->real^N) has_derivative f' x0) (at x0 within s)")
    MP_TAC THENL [ASM_MESON_TAC [], ASM_REWRITE_TAC [has_derivative_within]] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [LIM_WITHIN] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"B:real")) THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [dist, VECTOR_SUB_RZERO, ← VECTOR_ARITH
     (← q r"c % (y - (x + d)):real^N = c % (y - x) - c % d")] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [LIMPT_APPROACHABLE]) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"d:real")) THEN
    ASM_REWRITE_TAC [IN_ELIM_THM, dist, NOT_FORALL_THM, NOT_IMP] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [NORM_POS_LT, VECTOR_SUB_EQ] THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"c % (p - p) - v:real^N = --v")] THEN
    REWRITE_TAC [REAL_NOT_LT, NORM_NEG, NORM_MUL, REAL_ABS_INV,
                 REAL_ABS_NORM, ← REAL_ARITH (← q r"inv x * y:real = y / x")] THEN
    ASM_SIMP_TAC [REAL_LE_RDIV_EQ, NORM_POS_LT, VECTOR_SUB_EQ])

  let DIFFERENTIABLE_DISCRETE_PREIMAGES_CLOSED ← prove
   r"!f f' s y:real^N.
        closed s /\
        (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
        (!x. x IN s /\ f(x) = y ==> ~(det(matrix (f' x)) = &0))
        ==> {l | l limit_point_of {x | x IN s /\ f x = y}} = {}"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← SET_RULE
     (← q r"!s. {x | x IN s /\ P x} = {} /\ (!x. P x ==> x IN s)
          ==> {x | P x} = {}")) THEN
    EXISTS_TAC (← q r"s:real^N->bool") THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_DISCRETE_PREIMAGES THEN ASM_MESON_TAC [],
      X_GEN_TAC (← q r"l:real^N") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE [CLOSED_LIMPT]) THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
        LIMPT_SUBSET)) THEN
      REWRITE_TAC [SUBSET_RESTRICT]])

  let DIFFERENTIABLE_COUNTABLE_PREIMAGES ← prove
   r"!f f' s y:real^N.
        (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
        (!x. x IN s /\ f(x) = y ==> ~(det(matrix (f' x)) = &0))
        ==> COUNTABLE {x | x IN s /\ f(x) = y}"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC DISCRETE_IMP_COUNTABLE THEN
    REWRITE_TAC [← GSYM DISCRETE_SET, IN_ELIM_THM] THEN
    MATCH_MP_TAC (← SET_RULE
     (← q r"{x | P x /\ R x} = {} ==> {x | (P x /\ Q x) /\ R x} = {}")) THEN
    MATCH_MP_TAC DIFFERENTIABLE_DISCRETE_PREIMAGES THEN ASM_MESON_TAC [])

  let DIFFERENTIABLE_FINITE_PREIMAGES ← prove
   r"!f f' s y:real^N.
        compact s /\
        (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
        (!x. x IN s /\ f(x) = y ==> ~(det(matrix (f' x)) = &0))
        ==> FINITE {x | x IN s /\ f(x) = y}"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (MP_TAC o MATCH_MP DIFFERENTIABLE_DISCRETE_PREIMAGES) THEN
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC DISCRETE_EQ_FINITE_COMPACT THEN
    ASM_REWRITE_TAC [SUBSET_RESTRICT])

  let DIFFERENTIABLE_FINITE_PREIMAGES_GEN ← prove
   r"!f:real^N->real^N f' s y.
         compact {x | x IN s /\ f x = y} /\
         (!x. x IN s /\ f x = y ==> (f has_derivative f' x) (at x within s)) /\
         (!x. x IN s /\ f x = y ==> ~(det (matrix (f' x)) = &0))
         ==> FINITE {x | x IN s /\ f x = y}"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← SET_RULE
     (← q r"{x | x IN s /\ f x = y} =
      {x | x IN {x | x IN s /\ f x = y} /\ f x = y}")] THEN
    MATCH_MP_TAC DIFFERENTIABLE_FINITE_PREIMAGES THEN
    EXISTS_TAC (← q r"f':real^N->real^N->real^N") THEN
    ASM_REWRITE_TAC [IN_ELIM_THM, ← GSYM CONJ_ASSOC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC (← q r"s:real^N->bool") THEN ASM_SIMP_TAC [SUBSET_RESTRICT])

  pure { ROLLE, MVT, MVT_SIMPLE, MVT_VERY_SIMPLE, MVT_SEGMENT, MVT_SEGMENT_SIMPLE,
         MVT_GENERAL, DIFFERENTIABLE_BOUND, ONORM_DERIVATIVES_LE,
         HAS_DERIVATIVE_ZERO_CONSTANT, HAS_DERIVATIVE_ZERO_UNIQUE,
         HAS_DERIVATIVE_ZERO_CONNECTED_CONSTANT, HAS_DERIVATIVE_ZERO_CONNECTED_UNIQUE,
         DIFFERENTIABLE_DISCRETE_PREIMAGES, DIFFERENTIABLE_DISCRETE_PREIMAGES_CLOSED,
         DIFFERENTIABLE_COUNTABLE_PREIMAGES, DIFFERENTIABLE_FINITE_PREIMAGES,
         DIFFERENTIABLE_FINITE_PREIMAGES_GEN }

/- ------------------------------------------------------------------------- -/
/- Differentiability of inverse functions; surjectivity via Brouwer;         -/
/- Sussmann's open mapping theorem.  (derivatives.ml 1577-2040)              -/
/- ------------------------------------------------------------------------- -/

structure DVE where
  HAS_DERIVATIVE_INVERSE_WITHIN : thm
  HAS_DERIVATIVE_INVERSE_BASIC : thm
  HAS_DERIVATIVE_INVERSE_BASIC_X : thm
  HAS_DERIVATIVE_INVERSE_DIEUDONNE : thm
  HAS_DERIVATIVE_INVERSE : thm
  BROUWER_SURJECTIVE : thm
  BROUWER_SURJECTIVE_CBALL : thm
  SUSSMANN_OPEN_MAPPING : thm
  DIFFERENTIABLE_IMP_OPEN_MAP_GEN : thm
  DIFFERENTIABLE_IMP_OPEN_MAP : thm
  DIFFERENTIABLE_IMP_OPEN_MAP_ALT : thm
  HAS_DERIVATIVE_INVERSE_STRONG : thm
  HAS_DERIVATIVE_INVERSE_STRONG_X : thm
  HAS_DERIVATIVE_INVERSE_ON : thm
  deriving Inhabited

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
@[nospecialize]
def setupDVE [HolBase] (D : DerivativesDeps) (BDVA : DVA) (BDVB : DVB) : ExceptT String IO DVE := do
  -- @@SCOPE BEGIN
  let { differentiable, DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT, has_derivative,
        HAS_DERIVATIVE_WITHIN_OPEN, .. } := BDVA
  let { DIFFERENTIABLE_IMP_CONTINUOUS_AT, DIFFERENTIABLE_IMP_CONTINUOUS_ON,
        HAS_DERIVATIVE_AT_ALT, HAS_DERIVATIVE_WITHIN_ALT, HAS_DERIVATIVE_WITHIN_SUBSET, .. }
        := BDVB
  let { ARITH, .. } := D.dg.pt.cvx.core1
  let { FORALL_IN_IMAGE, FUN_EQ_THM, IMP_CONJ, IMP_CONJ_ALT, IMP_IMP, INTER_SUBSET, .. } :=
        D.dg.pt.cvx.core2
  let { I_THM, IN_IMAGE, IN_INTER, MONO_AND, MONO_EXISTS, MONO_FORALL, MONO_IMP,
        REAL_DIV_LMUL, REAL_DOWN2, .. } := D.dg.pt.cvx.core3
  let { REAL_EQ_IMP_LE, REAL_INV_MUL, REAL_LE_DIV2_EQ, REAL_LE_LDIV_EQ, REAL_LE_LMUL_EQ,
        REAL_LE_RDIV_EQ, REAL_LE_REFL, REAL_LE_RMUL, REAL_LE_RMUL_EQ, REAL_LE_TRANS,
        REAL_LET_TRANS, REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_MIN,
        REAL_LT_MUL, REAL_LT_RDIV_EQ, .. } := D.dg.pt.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_SYM, REAL_NOT_LT, REAL_OF_NUM_LT, RIGHT_EXISTS_IMP_THM,
        RIGHT_IMP_FORALL_THM, SKOLEM_THM, SUBSET, SUBSET_REFL, SUBSET_TRANS, .. } :=
        D.dg.pt.cvx.core5
  let { o_DEF, o_THM, real_div, real_ge, .. } := D.dg.pt.cvx.core6
  let { REAL_HALF, .. } := D.dg.pt.cvx.misc
  let { DIST_SYM, .. } := D.dg.pt.cvx.vec1
  let { LINEAR_SUB, .. } := D.dg.pt.cvx.vec2
  let { NORM_NEG, NORM_POS_LE, NORM_SUB, NORM_TRIANGLE, .. } := D.dg.pt.cvx.vec3
  let { dist, VECTOR_ADD_SUB, .. } := D.dg.pt.cvx.vec4
  let { BALL_SUBSET_CBALL, CBALL_EQ_EMPTY, CENTRE_IN_BALL, .. } := D.dg.pt.cvx.top1
  let { COMPACT_CBALL, .. } := D.dg.pt.cvx.top2
  let { CONTINUOUS_ON_ADD, CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID,
        CONTINUOUS_ON_INVERSE, CONTINUOUS_ON_SUB, CONTINUOUS_ON_SUBSET, .. } :=
        D.dg.pt.cvx.top3
  let { IN_BALL, IN_CBALL, IN_INTERIOR, IN_INTERIOR_CBALL, INTERIOR_OPEN, INTERIOR_SUBSET,
        LINEAR_CONTINUOUS_ON, OPEN_BALL, .. } := D.dg.pt.cvx.top4
  let { continuous_at, continuous_within, OPEN_INTER, OPEN_INTERIOR, .. } :=
        D.dg.pt.cvx.top5
  let { ASM_MESON_TAC, MESON_TAC, NORM_ARITH, REAL_ARITH, REAL_ARITH_TAC,
        REAL_RAT_REDUCE_CONV, SET_TAC, VECTOR_ARITH, .. } := D.dg.pt.cvx
  let { CONVEX_CBALL, .. } := D.dg.pt.qcvx2
  let { REAL_LT_TRANS, .. } := D.dg.qsession
  let { LINEAR_INVERSE_LEFT, .. } := D.dg.qvec
  let { BROUWER, .. } := D.qdegree
  let { DET_MATRIX_EQ_0_RIGHT, .. } := D.qdet
  let { REAL_INV_INV, .. } := D.qsession
  let { CONTINUOUS_ON_EQ_CONTINUOUS_AT, CONTINUOUS_ON_INTERIOR, .. } := D.qtopology1
  let { open_def, SUBSET_INTERIOR_EQ, .. } := D.qtopology2
  let { LINEAR_BOUNDED_POS, LINEAR_INJECTIVE_BOUNDED_BELOW_POS, NORM_TRIANGLE_SUB,
        RIGHT_INVERSE_LINEAR, .. } := D.qvec
  -- @@SCOPE END

  let HAS_DERIVATIVE_INVERSE_WITHIN ← prove
   r"!f:real^M->real^N f' g g' s a.
        a IN s /\
        (!x. x IN s ==> g(f x) = x) /\
        (f has_derivative f') (at a within s) /\
        linear g' /\ g' o f' = I /\
        g continuous (at (f a) within IMAGE f s)
        ==> (g has_derivative g') (at (f a) within IMAGE f s)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN
    ASM_REWRITE_TAC [HAS_DERIVATIVE_WITHIN_ALT] THEN
    STRIP_TAC THEN ASM_SIMP_TAC [IMP_CONJ, FORALL_IN_IMAGE] THEN
    MP_TAC (← ISPEC (← q r"g':real^N->real^M") LINEAR_BOUNDED_POS) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"C:real") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     (← q r"?B k. &0 < B /\ &0 < k /\
            !x. x IN s /\ norm((f:real^M->real^N) x - f a) < k
                ==> norm(x - a) <= B * norm(f x - f a)")
    STRIP_ASSUME_TAC THENL
     [MP_TAC (← ISPEC (← q r"f':real^M->real^N") LINEAR_INJECTIVE_BOUNDED_BELOW_POS) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"B:real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"&2 / B") THEN
      ASM_SIMP_TAC [REAL_LT_DIV, ← REAL_ARITH (← q r"&0 < &2")] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"B / &2")) THEN ASM_REWRITE_TAC [REAL_HALF] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [continuous_within]) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"d:real")) THEN
      ASM_SIMP_TAC [IMP_CONJ, FORALL_IN_IMAGE, dist] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"e:real") THEN
      MATCH_MP_TAC MONO_AND THEN REWRITE_TAC [] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"x:real^M") THEN
      DISCH_THEN (fun th => REPEAT DISCH_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real^M")) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← NORM_ARITH
       (← q r"norm(y - b - f':real^N) <= B / &2 * norm(x - a:real^M)
        ==> norm(x - a) * B <= norm f'
            ==> norm(y - b) >= B / &2 * norm(x - a)"))) THEN
      ASM_REWRITE_TAC [real_ge] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      ASM_SIMP_TAC [← GSYM REAL_LE_RDIV_EQ, REAL_HALF] THEN
      REWRITE_TAC [real_div, REAL_INV_MUL, REAL_INV_INV] THEN REAL_ARITH_TAC,
      ALL_TAC] THEN
    X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e / (B * C):real")) THEN
    ASM_SIMP_TAC [REAL_LT_DIV, REAL_LT_MUL] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"min k (d / B)") THEN
    ASM_SIMP_TAC [REAL_LT_MIN, REAL_LT_DIV] THEN
    X_GEN_TAC (← q r"x:real^M") THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real^M")) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      TRANS_TAC REAL_LET_TRANS (← q r"B * norm((f:real^M->real^N) x - f a)") THEN
      ASM_SIMP_TAC [] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      ASM_SIMP_TAC [← GSYM REAL_LT_RDIV_EQ],
      DISCH_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     (← q r"norm((g':real^N->real^M)(f x - f a - ((f':real^M->real^N) (x - a))))") THEN
    CONJ_TAC THENL
     [RULE_ASSUM_TAC (REWRITE_RULE [FUN_EQ_THM, o_THM, I_THM]) THEN
      ASM_SIMP_TAC [LINEAR_SUB] THEN CONV_TAC (fun t => NORM_ARITH t),
      ALL_TAC] THEN
    FIRST_X_ASSUM (fun th => W (MP_TAC o PART_MATCH lhand th o lhand o snd)) THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN ASM_SIMP_TAC [← GSYM REAL_LE_RDIV_EQ] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          REAL_LE_TRANS)) THEN
    REWRITE_TAC [real_div, REAL_INV_MUL] THEN REWRITE_TAC [← GSYM real_div] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"(e * inv B / C) * n:real = (n / B * e) / C")] THEN
    ASM_SIMP_TAC [REAL_LE_DIV2_EQ, REAL_LE_RMUL_EQ] THEN
    ASM_SIMP_TAC [REAL_LE_LDIV_EQ] THEN ASM_MESON_TAC [REAL_MUL_SYM])

  let HAS_DERIVATIVE_INVERSE_BASIC ← prove
   r"!f:real^M->real^N g f' g' t y.
        (f has_derivative f') (at (g y)) /\ linear g' /\ (g' o f' = I) /\
        g continuous (at y) /\
        open t /\ y IN t /\ (!z. z IN t ==> (f(g(z)) = z))
        ==> (g has_derivative g') (at y)"
   (REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM (X_CHOOSE_TAC (← q r"C:real") o MATCH_MP LINEAR_BOUNDED_POS) THEN
    SUBGOAL_THEN
     (← q r"!e. &0 < e ==> ?d. &0 < d /\
                         !z. norm(z - y) < d
                             ==> norm((g:real^N->real^M)(z) - g(y) - g'(z - y))
                                 <= e * norm(g(z) - g(y))")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [HAS_DERIVATIVE_AT_ALT]) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC (← q r"e / C"))) THEN
      ASM_SIMP_TAC [REAL_LT_DIV] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"d0:real")
       (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN (ASSUME_TAC o GEN (← q r"z:real^N") o SPEC (← q r"(g:real^N->real^M) z")) THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [continuous_at]) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"d0:real")) THEN ASM_REWRITE_TAC [dist] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"d1:real") STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"y:real^N") o
        GEN_REWRITE_RULE I [open_def]) THEN
      ASM_REWRITE_TAC [dist] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"d2:real") STRIP_ASSUME_TAC) THEN
      MP_TAC (← SPECL [← q r"d1:real", ← q r"d2:real"] REAL_DOWN2) THEN
      ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"d:real") THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN
      X_GEN_TAC (← q r"z:real^N") THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"C * (e / C) * norm((g:real^N->real^M) z - g y)") THEN
      CONJ_TAC THENL
       [ALL_TAC,
        ASM_SIMP_TAC [REAL_MUL_ASSOC, REAL_LE_RMUL, REAL_DIV_LMUL,
                      REAL_EQ_IMP_LE, REAL_LT_IMP_NZ, NORM_POS_LE]] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"C * norm(f((g:real^N->real^M) z) - y - f'(g z - g y))") THEN
      CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [REAL_LT_TRANS, REAL_LE_LMUL_EQ]] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       (← q r"norm(g'(f((g:real^N->real^M) z) - y - f'(g z - g y)):real^M)") THEN
      ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [LINEAR_SUB] THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM NORM_NEG] THEN
      REWRITE_TAC [← VECTOR_ARITH
       (← q r"--(gz:real^N - gy - (z - y)) = z - y - (gz - gy)")] THEN
      ASM_MESON_TAC [REAL_LE_REFL, REAL_LT_TRANS],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"?B d. &0 < B /\ &0 < d /\
            !z. norm(z - y) < d
                ==> norm((g:real^N->real^M)(z) - g(y)) <= B * norm(z - y)")
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC (← q r"&2 * C") THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"&1 / &2")) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"d:real") THEN
      ASM_SIMP_TAC [REAL_LT_MUL, REAL_OF_NUM_LT, ARITH] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"z:real^N") THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC [] THEN
      MATCH_MP_TAC (← REAL_ARITH
          (← q r"norm(dg) <= norm(dg') + norm(dg - dg') /\
           ((&2 * (&1 - h)) * norm(dg) = &1 * norm(dg)) /\
           norm(dg') <= c * norm(d)
           ==> norm(dg - dg') <= h * norm(dg)
               ==> norm(dg) <= (&2 * c) * norm(d)")) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC [NORM_TRIANGLE_SUB],
      ALL_TAC] THEN
    REWRITE_TAC [HAS_DERIVATIVE_AT_ALT] THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e / B")) THEN
    ASM_SIMP_TAC [REAL_LT_DIV] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d':real") STRIP_ASSUME_TAC) THEN
    MP_TAC (← SPECL [← q r"d:real", ← q r"d':real"] REAL_DOWN2) THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"k:real") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"z:real^N") THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"e / B * norm ((g:real^N->real^M) z - g y)") THEN
    CONJ_TAC THENL [ASM_MESON_TAC [REAL_LT_TRANS], ALL_TAC] THEN
    ASM_SIMP_TAC [real_div, ← GSYM REAL_MUL_ASSOC, REAL_LE_LMUL_EQ] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    ASM_SIMP_TAC [← GSYM real_div, REAL_LE_LDIV_EQ] THEN
    ASM_MESON_TAC [REAL_MUL_SYM, REAL_LT_TRANS])

  let HAS_DERIVATIVE_INVERSE_BASIC_X ← prove
   r"!f:real^M->real^N g f' g' t x.
        (f has_derivative f') (at x) /\ linear g' /\ (g' o f' = I) /\
        g continuous (at (f(x))) /\ (g(f(x)) = x) /\
        open t /\ f(x) IN t /\ (!y. y IN t ==> (f(g(y)) = y))
        ==> (g has_derivative g') (at (f(x)))"
   (MESON_TAC [HAS_DERIVATIVE_INVERSE_BASIC])

  let HAS_DERIVATIVE_INVERSE_DIEUDONNE ← prove
   r"!f:real^M->real^N g s.
        open s /\ open (IMAGE f s) /\
        f continuous_on s /\ g continuous_on (IMAGE f s) /\
        (!x. x IN s ==> (g(f(x)) = x))
        ==> !f' g' x. x IN s /\ (f has_derivative f') (at x) /\
                      linear g' /\ (g' o f' = I)
                      ==> (g has_derivative g') (at (f(x)))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_INVERSE_BASIC_X THEN
    EXISTS_TAC (← q r"f':real^M->real^N") THEN
    EXISTS_TAC (← q r"IMAGE (f:real^M->real^N) s") THEN
    ASM_MESON_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_AT, IN_IMAGE])

  let HAS_DERIVATIVE_INVERSE ← prove
   r"!f:real^M->real^N g f' g' s x.
        compact s /\ x IN s /\ f(x) IN interior(IMAGE f s) /\
        f continuous_on s /\ (!x. x IN s ==> (g(f(x)) = x)) /\
        (f has_derivative f') (at x) /\ linear g' /\ (g' o f' = I)
        ==> (g has_derivative g') (at (f(x)))"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_INVERSE_BASIC_X THEN
    EXISTS_TAC (← q r"f':real^M->real^N") THEN
    EXISTS_TAC (← q r"interior(IMAGE (f:real^M->real^N) s)") THEN
    ASM_MESON_TAC [CONTINUOUS_ON_INTERIOR, CONTINUOUS_ON_INVERSE,
      OPEN_INTERIOR, IN_IMAGE, INTERIOR_SUBSET, SUBSET])

  let BROUWER_SURJECTIVE ← prove
   r"!f:real^N->real^N s t.
        compact t /\ convex t /\ ~(t = {}) /\ f continuous_on t /\
        (!x y. x IN s /\ y IN t ==> x + (y - f(y)) IN t)
        ==> !x. x IN s ==> ?y. y IN t /\ (f(y) = x)"
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← VECTOR_ARITH
     (← q r"((f:real^N->real^N)(y) = x) <=> (x + (y - f(y)) = y)")] THEN
    ASM_SIMP_TAC [CONTINUOUS_ON_ADD, CONTINUOUS_ON_CONST, CONTINUOUS_ON_SUB,
                  BROUWER, SUBSET, FORALL_IN_IMAGE, CONTINUOUS_ON_ID])

  let BROUWER_SURJECTIVE_CBALL ← prove
   r"!f:real^N->real^N s a e.
        &0 < e /\
        f continuous_on cball(a,e) /\
        (!x y. x IN s /\ y IN cball(a,e) ==> x + (y - f(y)) IN cball(a,e))
        ==> !x. x IN s ==> ?y. y IN cball(a,e) /\ (f(y) = x)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC BROUWER_SURJECTIVE THEN
    ASM_REWRITE_TAC [COMPACT_CBALL, CONVEX_CBALL] THEN
    ASM_SIMP_TAC [CBALL_EQ_EMPTY, REAL_LT_IMP_LE, REAL_NOT_LT])

  let SUSSMANN_OPEN_MAPPING ← prove
   r"!f:real^M->real^N f' g' s x.
        open s /\ f continuous_on s /\
        x IN s /\ (f has_derivative f') (at x) /\ linear g' /\ (f' o g' = I)
        ==> !t. t SUBSET s /\ x IN interior(t)
                ==> f(x) IN interior(IMAGE f t)"
   (REWRITE_TAC [HAS_DERIVATIVE_AT_ALT] THEN
    REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← MATCH_MP LINEAR_BOUNDED_POS (← ASSUME (← q r"linear(g':real^N->real^M)"))) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"B:real") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"&1 / (&2 * B)")) THEN
    ASM_SIMP_TAC [REAL_LT_MUL, REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"e0:real") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR_CBALL]) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"e1:real") STRIP_ASSUME_TAC) THEN
    MP_TAC (← SPECL [← q r"e0 / B", ← q r"e1 / B"] REAL_DOWN2) THEN
    ASM_SIMP_TAC [REAL_LT_DIV] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"e:real") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL
     [← q r"\y. (f:real^M->real^N)(x + g'(y - f(x)))",
      ← q r"cball((f:real^M->real^N) x,e / &2)", ← q r"(f:real^M->real^N) x", ← q r"e:real"]
     BROUWER_SURJECTIVE_CBALL) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC [← GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
          REWRITE_TAC [CONTINUOUS_ON_CONST] THEN
          ONCE_REWRITE_TAC [← GSYM o_DEF] THEN
          MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
          ASM_SIMP_TAC [CONTINUOUS_ON_SUB, CONTINUOUS_ON_CONST,
                        CONTINUOUS_ON_ID, LINEAR_CONTINUOUS_ON],
          ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC (← q r"cball(x:real^M,e1)") THEN CONJ_TAC THENL
         [ASM_MESON_TAC [CONTINUOUS_ON_SUBSET, SUBSET_TRANS], ALL_TAC] THEN
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"y:real^N") THEN
        REWRITE_TAC [IN_CBALL, dist] THEN
        REWRITE_TAC [← VECTOR_ARITH (← q r"x - (x + y) = --y:real^N")] THEN
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [NORM_SUB] THEN
        DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (← q r"B * norm(y - (f:real^M->real^N) x)") THEN
        ASM_REWRITE_TAC [NORM_NEG] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
        ASM_SIMP_TAC [← GSYM REAL_LE_RDIV_EQ] THEN
        ASM_MESON_TAC [REAL_LE_TRANS, REAL_LT_IMP_LE],
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [← q r"y:real^N", ← q r"z:real^N"] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x + g'(z - (f:real^M->real^N) x)")) THEN
      ASM_REWRITE_TAC [VECTOR_ADD_SUB] THEN ANTS_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC (← q r"B * norm(z - (f:real^M->real^N) x)") THEN
        ASM_REWRITE_TAC [NORM_NEG] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
        ASM_SIMP_TAC [← GSYM REAL_LT_RDIV_EQ] THEN
        ASM_MESON_TAC [IN_CBALL, dist, NORM_SUB, REAL_LET_TRANS],
        ALL_TAC] THEN
      REWRITE_TAC [← VECTOR_ARITH (← q r"a - b - (c - b) = a - c:real^N")] THEN
      DISCH_TAC THEN REWRITE_TAC [IN_CBALL, dist] THEN
      ONCE_REWRITE_TAC [← VECTOR_ARITH
       (← q r"f0 - (y + z - f1) = (f1 - z) + (f0 - y):real^N")] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
       (← q r"norm(f(x + g'(z - (f:real^M->real^N) x)) - z) + norm(f x - y)") THEN
      REWRITE_TAC [NORM_TRIANGLE] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REAL_ARITH
       (← q r"x <= a ==> y <= b - a ==> x + y <= b"))) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"e / &2") THEN CONJ_TAC THENL
       [ASM_MESON_TAC [IN_CBALL, dist], ALL_TAC] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"e / &2 <= e - x <=> x <= e / &2")] THEN
      REWRITE_TAC [real_div, REAL_INV_MUL, REAL_MUL_ASSOC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      SIMP_TAC [← REAL_ARITH (← q r"(&1 / &2 * b) * x <= e * &1 / &2 <=> x * b <= e")] THEN
      ASM_SIMP_TAC [← GSYM real_div, REAL_LE_LDIV_EQ] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (← q r"B * norm(z - (f:real^M->real^N) x)") THEN
      ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [REAL_LE_LMUL_EQ, REAL_MUL_SYM, IN_CBALL, dist, DIST_SYM],
      ALL_TAC] THEN
    REWRITE_TAC [IN_INTERIOR] THEN
    DISCH_THEN (fun th => tactic_of do pure (EXISTS_TAC (← q r"e / &2") THEN MP_TAC th)) THEN
    ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH, SUBSET] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"y:real^N") THEN
    MATCH_MP_TAC MONO_IMP THEN
    REWRITE_TAC [← REWRITE_RULE [SUBSET] BALL_SUBSET_CBALL] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"z:real^N") (STRIP_ASSUME_TAC o GSYM)) THEN
    ASM_REWRITE_TAC [IN_IMAGE] THEN
    EXISTS_TAC (← q r"x + g'(z - (f:real^M->real^N) x)") THEN REWRITE_TAC [] THEN
    FIRST_ASSUM (MATCH_MP_TAC o REWRITE_RULE [SUBSET]) THEN
    REWRITE_TAC [IN_CBALL, dist, ← VECTOR_ARITH (← q r"x - (x + y) = --y:real^N")] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"B * norm(z - (f:real^M->real^N) x)") THEN
    ASM_REWRITE_TAC [NORM_NEG] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    ASM_SIMP_TAC [← GSYM REAL_LE_RDIV_EQ] THEN
    ASM_MESON_TAC [IN_CBALL, dist, NORM_SUB, REAL_LT_IMP_LE, REAL_LE_TRANS])

  let DIFFERENTIABLE_IMP_OPEN_MAP_GEN ← prove
   r"!f:real^M->real^N f' g' s.
        open s /\
        (!x. x IN s
             ==> (f has_derivative f' x) (at x) /\
                 linear(g' x) /\ f' x o g' x = I)
        ==> open(IMAGE f s)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [← GSYM SUBSET_INTERIOR_EQ, SUBSET, FORALL_IN_IMAGE] THEN
    X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN
    MP_TAC (← ISPECL
     [← q r"f:real^M->real^N", ← q r"(f':real^M->real^M->real^N) x",
      ← q r"(g':real^M->real^N->real^M) x", ← q r"s:real^M->bool", ← q r"x:real^M"]
     SUSSMANN_OPEN_MAPPING) THEN
    ASM_SIMP_TAC [RIGHT_IMP_FORALL_THM, IMP_IMP] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC [SUBSET_REFL, INTERIOR_OPEN] THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
    ASM_SIMP_TAC [DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT, differentiable] THEN
    ASM_MESON_TAC [])

  let DIFFERENTIABLE_IMP_OPEN_MAP ← prove
   r"!f:real^N->real^N f' s.
        open s /\
        (!x. x IN s
             ==> (f has_derivative f' x) (at x) /\ ~(det(matrix(f' x)) = &0))
        ==> open(IMAGE f s)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_OPEN_MAP_GEN THEN
    EXISTS_TAC (← q r"f':real^N->real^N->real^N") THEN
    ASM_SIMP_TAC [← GSYM SKOLEM_THM, RIGHT_EXISTS_IMP_THM] THEN
    ASM_MESON_TAC [DET_MATRIX_EQ_0_RIGHT, has_derivative])

  let DIFFERENTIABLE_IMP_OPEN_MAP_ALT ← prove
   r"!f:real^N->real^N f' s t.
        (!x. x IN s
             ==> (f has_derivative f' x) (at x within s) /\
                 ~(det(matrix(f' x)) = &0)) /\
        open t /\ t SUBSET s
        ==> open(IMAGE f t)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_OPEN_MAP THEN
    EXISTS_TAC (← q r"f':real^N->real^N->real^N") THEN
    ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real^N")) THEN
    ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"t:real^N->bool") o
      MATCH_MP (← REWRITE_RULE [IMP_CONJ] HAS_DERIVATIVE_WITHIN_SUBSET)) THEN
    ASM_SIMP_TAC [HAS_DERIVATIVE_WITHIN_OPEN])

  let HAS_DERIVATIVE_INVERSE_STRONG ← prove
   r"!f:real^N->real^N g f' g' s x.
        open s /\ x IN s /\ f continuous_on s /\
        (!x. x IN s ==> (g(f(x)) = x)) /\
        (f has_derivative f') (at x) /\ (f' o g' = I)
        ==> (g has_derivative g') (at (f(x)))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_INVERSE_BASIC_X THEN
    SUBGOAL_THEN (← q r"linear (g':real^N->real^N) /\ (g' o f' = I)")
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [has_derivative, RIGHT_INVERSE_LINEAR, LINEAR_INVERSE_LEFT],
      ALL_TAC] THEN
    EXISTS_TAC (← q r"f':real^N->real^N") THEN
    EXISTS_TAC (← q r"interior (IMAGE (f:real^N->real^N) s)") THEN
    ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
     [ALL_TAC,
      ASM_SIMP_TAC [],
      REWRITE_TAC [OPEN_INTERIOR],
      ASM_MESON_TAC [INTERIOR_OPEN, SUSSMANN_OPEN_MAPPING, LINEAR_INVERSE_LEFT,
                     SUBSET_REFL, has_derivative],
      ASM_MESON_TAC [IN_IMAGE, SUBSET, INTERIOR_SUBSET]] THEN
    REWRITE_TAC [continuous_at] THEN
    X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"!t. t SUBSET s /\ x IN interior(t)
          ==> (f:real^N->real^N)(x) IN interior(IMAGE f t)")
    MP_TAC THENL
     [ASM_MESON_TAC [SUSSMANN_OPEN_MAPPING, LINEAR_INVERSE_LEFT, has_derivative],
      ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"ball(x:real^N,e) INTER s")) THEN ANTS_TAC THENL
     [ASM_SIMP_TAC [IN_INTER, OPEN_BALL, INTERIOR_OPEN, OPEN_INTER,
                    INTER_SUBSET, CENTRE_IN_BALL],
      ALL_TAC] THEN
    REWRITE_TAC [IN_INTERIOR] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"d:real") THEN
    ASM_CASES_TAC (← q r"&0 < d") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [SUBSET, IN_BALL, IN_IMAGE, IN_INTER] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"y:real^N") THEN
    REWRITE_TAC [DIST_SYM] THEN MATCH_MP_TAC MONO_IMP THEN
    ASM_MESON_TAC [DIST_SYM])

  let HAS_DERIVATIVE_INVERSE_STRONG_X ← prove
   r"!f:real^N->real^N g f' g' s y.
        open s /\ (g y) IN s /\ f continuous_on s /\
        (!x. x IN s ==> (g(f(x)) = x)) /\
        (f has_derivative f') (at (g y)) /\ (f' o g' = I) /\
        f(g y) = y
        ==> (g has_derivative g') (at y)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← SYM th])) THEN
    MATCH_MP_TAC HAS_DERIVATIVE_INVERSE_STRONG THEN
    MAP_EVERY EXISTS_TAC [← q r"f':real^N->real^N", ← q r"s:real^N->bool"] THEN
    ASM_REWRITE_TAC [])

  let HAS_DERIVATIVE_INVERSE_ON ← prove
   r"!f:real^N->real^N s.
        open s /\
        (!x. x IN s ==> (f has_derivative f'(x)) (at x) /\ (g(f(x)) = x) /\
                        (f'(x) o g'(x) = I))
        ==> !x. x IN s ==> (g has_derivative g'(x)) (at (f(x)))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_INVERSE_STRONG THEN
    EXISTS_TAC (← q r"(f':real^N->real^N->real^N) x") THEN
    EXISTS_TAC (← q r"s:real^N->bool") THEN
    ASM_MESON_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_AT,
                   DIFFERENTIABLE_IMP_CONTINUOUS_AT, differentiable])

  pure { HAS_DERIVATIVE_INVERSE_WITHIN, HAS_DERIVATIVE_INVERSE_BASIC,
         HAS_DERIVATIVE_INVERSE_BASIC_X, HAS_DERIVATIVE_INVERSE_DIEUDONNE,
         HAS_DERIVATIVE_INVERSE, BROUWER_SURJECTIVE, BROUWER_SURJECTIVE_CBALL,
         SUSSMANN_OPEN_MAPPING, DIFFERENTIABLE_IMP_OPEN_MAP_GEN, DIFFERENTIABLE_IMP_OPEN_MAP,
         DIFFERENTIABLE_IMP_OPEN_MAP_ALT, HAS_DERIVATIVE_INVERSE_STRONG,
         HAS_DERIVATIVE_INVERSE_STRONG_X, HAS_DERIVATIVE_INVERSE_ON }

/- ------------------------------------------------------------------------- -/
/- Uniformly convergent sequences of derivatives; antiderivatives; series.   -/
/- (derivatives.ml 2041-2300)                                                -/
/- ------------------------------------------------------------------------- -/

structure DVF where
  HAS_DERIVATIVE_SEQUENCE_LIPSCHITZ : thm
  HAS_DERIVATIVE_SEQUENCE : thm
  HAS_ANTIDERIVATIVE_SEQUENCE : thm
  HAS_ANTIDERIVATIVE_LIMIT : thm
  HAS_DERIVATIVE_SERIES : thm
  deriving Inhabited

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
@[nospecialize]
def setupDVF [HolBase] (D : DerivativesDeps) (BDVA : DVA) (BDVB : DVB) (BDVD : DVD) : ExceptT String IO DVF := do
  -- @@SCOPE BEGIN
  let { HAS_DERIVATIVE_ADD, HAS_DERIVATIVE_CONST, HAS_DERIVATIVE_SUB, HAS_DERIVATIVE_VSUM,
        has_derivative_within, .. } := BDVA
  let { HAS_DERIVATIVE_WITHIN_ALT, .. } := BDVB
  let { DIFFERENTIABLE_BOUND, .. } := BDVD
  let { ARITH, ETA_AX, .. } := D.dg.pt.cvx.core1
  let { FUN_EQ_THM, GE, .. } := D.dg.pt.cvx.core2
  let { MEMBER_NOT_EMPTY, MONO_EXISTS, MONO_FORALL, NOT_IN_EMPTY, REAL_ARCH_INV,
        REAL_DIV_RMUL, .. } := D.dg.pt.cvx.core3
  let { REAL_LE_INV2, REAL_LE_RMUL, REAL_LE_TRANS, REAL_LT_DIV, REAL_LT_IMP_LE,
        REAL_LT_INV_EQ, .. } := D.dg.pt.cvx.core4
  let { REAL_MUL_RZERO, REAL_OF_NUM_ADD, REAL_OF_NUM_LE, REAL_OF_NUM_LT,
        RIGHT_EXISTS_IMP_THM, SKOLEM_THM, .. } := D.dg.pt.cvx.core5
  let { REAL_HALF, .. } := D.dg.pt.cvx.misc
  let { NORM_0, NORM_EQ_0, .. } := D.dg.pt.cvx.vec2
  let { NORM_LE_0, NORM_NEG, NORM_POS_LE, NORM_POS_LT, NORM_SUB, NORM_TRIANGLE,
        NORM_TRIANGLE_LE, .. } := D.dg.pt.cvx.vec3
  let { dist, linear, VECTOR_SUB_EQ, VECTOR_SUB_REFL, .. } := D.dg.pt.cvx.vec4
  let { EVENTUALLY_SEQUENTIALLY, TRIVIAL_LIMIT_SEQUENTIALLY, .. } := D.dg.pt.cvx.met
  let { LIM_ADD, LIM_CMUL, LIM_CONST, LIM_SEQUENTIALLY, LIM_SUB, LIM_UNIQUE, .. } :=
        D.dg.pt.cvx.top4
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC,
        VECTOR_ARITH, VECTOR_ARITH_TAC, .. } := D.dg.pt.cvx
  let { NORM_TRIANGLE_LT, .. } := D.dg.pt.qvec
  let { REAL_LT_TRANS, .. } := D.dg.qsession
  let { SEQUENTIALLY, .. } := D.qmetric
  let { FINITE_INTER_NUMSEG, .. } := D.qmisc
  let { CONVERGENT_EQ_CAUCHY, CONVERGENT_IMP_CAUCHY, .. } := D.qtopology1
  let { cauchy, LIM_NORM_UBOUND, sums, .. } := D.qtopology2
  let { LINEAR_COMPOSE_SUB, ONORM, .. } := D.qvec
  -- @@SCOPE END

  let HAS_DERIVATIVE_SEQUENCE_LIPSCHITZ ← prove
   r"!s f:num->real^M->real^N f' g'.
        convex s /\
        (!n x. x IN s ==> ((f n) has_derivative (f' n x)) (at x within s)) /\
        (!e. &0 < e
             ==> ?N. !n x h. n >= N /\ x IN s
                             ==> norm(f' n x h - g' x h) <= e * norm(h))
        ==> !e. &0 < e
                ==> ?N. !m n x y. m >= N /\ n >= N /\ x IN s /\ y IN s
                                  ==> norm((f m x - f n x) - (f m y - f n y))
                                      <= e * norm(x - y)"
   (REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e / &2")) THEN
    ASM_REWRITE_TAC [REAL_HALF] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"N:num") THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"m:num", ← q r"n:num"] THEN
    ASM_CASES_TAC (← q r"m:num >= N") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"n:num >= N") THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC DIFFERENTIABLE_BOUND THEN
    EXISTS_TAC (← q r"\x h. (f':num->real^M->real^M->real^N) m x h - f' n x h") THEN
    ASM_SIMP_TAC [HAS_DERIVATIVE_SUB, ETA_AX] THEN
    X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"!h. norm((f':num->real^M->real^M->real^N) m x h - f' n x h) <= e * norm(h)")
    MP_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [HAS_DERIVATIVE_WITHIN_ALT]) THEN
    ASM_SIMP_TAC [ONORM, LINEAR_COMPOSE_SUB, ETA_AX] THEN
    X_GEN_TAC (← q r"h:real^M") THEN SUBST1_TAC (← VECTOR_ARITH
     (← q r"(f':num->real^M->real^M->real^N) m x h - f' n x h =
      (f' m x h - g' x h) + --(f' n x h - g' x h)")) THEN
    MATCH_MP_TAC NORM_TRIANGLE_LE THEN
    ASM_SIMP_TAC [NORM_NEG, ← REAL_ARITH
     (← q r"a <= e / &2 * h /\ b <= e / &2 * h ==> a + b <= e * h")])

  let HAS_DERIVATIVE_SEQUENCE ← prove
   r"!s f:num->real^M->real^N f' g'.
        convex s /\
        (!n x. x IN s ==> ((f n) has_derivative (f' n x)) (at x within s)) /\
        (!e. &0 < e
             ==> ?N. !n x h. n >= N /\ x IN s
                             ==> norm(f' n x h - g' x h) <= e * norm(h)) /\
        (?x l. x IN s /\ ((\n. f n x) --> l) sequentially)
        ==> ?g. !x. x IN s
                    ==> ((\n. f n x) --> g x) sequentially /\
                        (g has_derivative g'(x)) (at x within s)"
   (REPEAT GEN_TAC THEN
    REPLICATE_TAC 2 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "O") MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"x0:real^M") STRIP_ASSUME_TAC) THEN
    HolCore.Tactics.SUBGOAL_TAC HolBase.B "A"
     (← q r"!e. &0 < e
          ==> ?N. !m n x y. m >= N /\ n >= N /\ x IN s /\ y IN s
                            ==> norm(((f:num->real^M->real^N) m x - f n x) -
                                     (f m y - f n y))
                                 <= e * norm(x - y)")
     [MATCH_MP_TAC HAS_DERIVATIVE_SEQUENCE_LIPSCHITZ THEN
      ASM_REWRITE_TAC [] THEN ASM_MESON_TAC []] THEN
    SUBGOAL_THEN
     (← q r"?g:real^M->real^N. !x. x IN s ==> ((\n. f n x) --> g x) sequentially")
    MP_TAC THENL
     [REWRITE_TAC [← GSYM SKOLEM_THM, RIGHT_EXISTS_IMP_THM] THEN
      X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN
      GEN_REWRITE_TAC I [CONVERGENT_EQ_CAUCHY] THEN
      FIRST_X_ASSUM (MP_TAC o MATCH_MP CONVERGENT_IMP_CAUCHY) THEN
      REWRITE_TAC [cauchy, dist] THEN DISCH_THEN (LABEL_TAC "B") THEN
      X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
      ASM_CASES_TAC (← q r"x:real^M = x0") THEN ASM_SIMP_TAC [] THEN
      REMOVE_THEN "B" (MP_TAC o SPEC (← q r"e / &2")) THEN
      ASM_REWRITE_TAC [REAL_HALF] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"N1:num") STRIP_ASSUME_TAC) THEN
      REMOVE_THEN "A" (MP_TAC o SPEC (← q r"e / &2 / norm(x - x0:real^M)")) THEN
      ASM_SIMP_TAC [REAL_LT_DIV, NORM_POS_LT, REAL_HALF, VECTOR_SUB_EQ] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"N2:num")) THEN
      EXISTS_TAC (← q r"N1 + N2:num") THEN REPEAT GEN_TAC THEN
      DISCH_THEN (CONJUNCTS_THEN (STRIP_ASSUME_TAC o MATCH_MP
        (← ARITH_RULE (← q r"m >= N1 + N2:num ==> m >= N1 /\ m >= N2")))) THEN
      SUBST1_TAC (← VECTOR_ARITH
       (← q r"(f:num->real^M->real^N) m x - f n x =
        (f m x - f n x - (f m x0 - f n x0)) + (f m x0 - f n x0)")) THEN
      MATCH_MP_TAC NORM_TRIANGLE_LT THEN
      FIRST_X_ASSUM (MP_TAC o SPECL
        [← q r"m:num", ← q r"n:num", ← q r"x:real^M", ← q r"x0:real^M"]) THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"m:num", ← q r"n:num"]) THEN
      ASM_SIMP_TAC [REAL_DIV_RMUL, NORM_EQ_0, VECTOR_SUB_EQ] THEN REAL_ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN SIMP_TAC [] THEN
    DISCH_THEN (LABEL_TAC "B") THEN X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN
    REWRITE_TAC [HAS_DERIVATIVE_WITHIN_ALT] THEN
    HolCore.Tactics.SUBGOAL_TAC HolBase.B "C"
     (← q r"!e. &0 < e
          ==> ?N. !n x y. n >= N /\ x IN s /\ y IN s
                          ==> norm(((f:num->real^M->real^N) n x - f n y) -
                                   (g x - g y))
                               <= e * norm(x - y)")
     [X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
      REMOVE_THEN "A" (MP_TAC o SPEC (← q r"e:real")) THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"N:num") THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"n:num") THEN
      DISCH_TAC THEN MAP_EVERY X_GEN_TAC [← q r"u:real^M", ← q r"v:real^M"] THEN
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o GEN (← q r"m:num") o SPECL
        [← q r"m:num", ← q r"u:real^M", ← q r"v:real^M"]) THEN
      DISCH_TAC THEN MATCH_MP_TAC (← ISPEC (← q r"sequentially") LIM_NORM_UBOUND) THEN
      EXISTS_TAC
        (← q r"\m. ((f:num->real^M->real^N) n u - f n v) - (f m u - f m v)") THEN
      REWRITE_TAC [TRIVIAL_LIMIT_SEQUENTIALLY, EVENTUALLY_SEQUENTIALLY] THEN
      ASM_SIMP_TAC [SEQUENTIALLY, LIM_SUB, LIM_CONST] THEN EXISTS_TAC (← q r"N:num") THEN
      ONCE_REWRITE_TAC [← VECTOR_ARITH
       (← q r"(x - y) - (u - v) = (x - u) - (y -  v):real^N")] THEN
      REWRITE_TAC [← GSYM GE]  THEN ASM_MESON_TAC []] THEN
    CONJ_TAC THENL
     [HolCore.Tactics.SUBGOAL_TAC HolBase.B "D"
      (← q r"!u. ((\n. (f':num->real^M->real^M->real^N) n x u) --> g' x u) sequentially")
       [REWRITE_TAC [LIM_SEQUENTIALLY, dist] THEN REPEAT STRIP_TAC THEN
        ASM_CASES_TAC (← q r"u = vec 0:real^M") THENL
         [REMOVE_THEN "O" (MP_TAC o SPEC (← q r"e:real")),
          REMOVE_THEN "O" (MP_TAC o SPEC (← q r"e / &2 / norm(u:real^M)"))] THEN
        ASM_SIMP_TAC [NORM_POS_LT, REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
        MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
        MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
        DISCH_THEN (MP_TAC o SPECL [← q r"x:real^M", ← q r"u:real^M"]) THEN
        DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
        ASM_SIMP_TAC [GE, NORM_0, REAL_MUL_RZERO, NORM_LE_0] THEN
        ASM_SIMP_TAC [REAL_DIV_RMUL, NORM_EQ_0] THEN
        UNDISCH_TAC (← q r"&0 < e") THEN REAL_ARITH_TAC] THEN
      REWRITE_TAC [linear] THEN ONCE_REWRITE_TAC [← GSYM VECTOR_SUB_EQ] THEN
      CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [← q r"u:real^M", ← q r"v:real^M"],
        MAP_EVERY X_GEN_TAC [← q r"c:real", ← q r"u:real^M"]] THEN
      MATCH_MP_TAC (← ISPEC (← q r"sequentially") LIM_UNIQUE) THENL
       [EXISTS_TAC
         (← q r"\n. (f':num->real^M->real^M->real^N) n x (u + v) -
              (f' n x u + f' n x v)"),
        EXISTS_TAC
         (← q r"\n. (f':num->real^M->real^M->real^N) n x (c % u) -
              c % f' n x u")] THEN
      ASM_SIMP_TAC [TRIVIAL_LIMIT_SEQUENTIALLY, LIM_SUB, LIM_ADD, LIM_CMUL] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [has_derivative_within, linear]) THEN
      ASM_SIMP_TAC [VECTOR_SUB_REFL, LIM_CONST],
      ALL_TAC] THEN
    X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
    (tactic_of do
      let t ← q r"e / &3"
      pure (MAP_EVERY (fun s => REMOVE_THEN s (MP_TAC o SPEC t)) ["C", "O"])) THEN
    ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"N1:num") (LABEL_TAC "C")) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"N2:num") (LABEL_TAC "A")) THEN
    REMOVE_THEN "C" (MP_TAC o GEN (← q r"y:real^M") o
     SPECL [← q r"N1 + N2:num", ← q r"x:real^M", ← q r"y - x:real^M"]) THEN
    REMOVE_THEN "A" (MP_TAC o GEN (← q r"y:real^M") o
     SPECL [← q r"N1 + N2:num", ← q r"y:real^M", ← q r"x:real^M"]) THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"N1 + N2:num", ← q r"x:real^M"]) THEN
    ASM_REWRITE_TAC [← ARITH_RULE (← q r"m + n >= m:num /\ m + n >= n")] THEN
    REWRITE_TAC [HAS_DERIVATIVE_WITHIN_ALT] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"e / &3") o CONJUNCT2) THEN
    ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d1:real") STRIP_ASSUME_TAC) THEN
    DISCH_THEN (LABEL_TAC "D1") THEN DISCH_THEN (LABEL_TAC "D2") THEN
    EXISTS_TAC (← q r"d1:real") THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"y:real^M") THEN
    DISCH_TAC THEN REMOVE_THEN "D2" (MP_TAC o SPEC (← q r"y:real^M")) THEN
    REMOVE_THEN "D1" (MP_TAC o SPEC (← q r"y:real^M")) THEN ANTS_TAC THENL
     [ASM_MESON_TAC [REAL_LT_TRANS, NORM_SUB], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"y:real^M")) THEN ANTS_TAC THENL
     [ASM_MESON_TAC [REAL_LT_TRANS, NORM_SUB], ALL_TAC] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"d <= a + b + c
      ==> a <= e / &3 * n ==> b <= e / &3 * n ==> c <= e / &3 * n
          ==> d <= e * n")) THEN
    GEN_REWRITE_TAC (funpow 2 RAND_CONV o LAND_CONV) [NORM_SUB] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"(norm(x + y + z) = norm(a)) /\
      norm(x + y + z) <= norm(x) + norm(y + z) /\
      norm(y + z) <= norm(y) + norm(z)
      ==> norm(a) <= norm(x) + norm(y) + norm(z)")) THEN
    REWRITE_TAC [NORM_TRIANGLE] THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC)

  let HAS_ANTIDERIVATIVE_SEQUENCE ← prove
   r"!s f:num->real^M->real^N f' g'.
        convex s /\
        (!n x. x IN s ==> ((f n) has_derivative (f' n x)) (at x within s)) /\
        (!e. &0 < e
             ==> ?N. !n x h. n >= N /\ x IN s
                             ==> norm(f' n x h - g' x h) <= e * norm(h))
        ==> ?g. !x. x IN s ==> (g has_derivative g'(x)) (at x within s)"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"(s:real^M->bool) = {}") THEN
    ASM_REWRITE_TAC [NOT_IN_EMPTY] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"a:real^M")) THEN
    MP_TAC (← ISPECL
         [← q r"s:real^M->bool",
          ← q r"\n x. (f:num->real^M->real^N) n x + (f 0 a -  f n a)",
          ← q r"f':num->real^M->real^M->real^N",
          ← q r"g':real^M->real^M->real^N"]
        HAS_DERIVATIVE_SEQUENCE) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ALL_TAC, MESON_TAC []] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"(f':num->real^M->real^M->real^N) n x =
                    \h. f' n x h + vec 0")
      SUBST1_TAC THENL [SIMP_TAC [FUN_EQ_THM] THEN VECTOR_ARITH_TAC, ALL_TAC] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
      ASM_SIMP_TAC [HAS_DERIVATIVE_CONST, ETA_AX],
      MAP_EVERY EXISTS_TAC [← q r"a:real^M", ← q r"f 0 (a:real^M) :real^N"] THEN
      ASM_REWRITE_TAC [← VECTOR_ARITH (← q r"a + b - a = b:real^N"), LIM_CONST]])

  let HAS_ANTIDERIVATIVE_LIMIT ← prove
   r"!s g':real^M->real^M->real^N.
        convex s /\
        (!e. &0 < e
             ==> ?f f'. !x. x IN s
                            ==> (f has_derivative (f' x)) (at x within s) /\
                                (!h. norm(f' x h - g' x h) <= e * norm(h)))
        ==> ?g. !x. x IN s ==> (g has_derivative g'(x)) (at x within s)"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN (← q r"n:num") o SPEC (← q r"inv(&n + &1)")) THEN
    REWRITE_TAC [REAL_LT_INV_EQ, ← REAL_ARITH (← q r"&0 < &n + &1")] THEN
    REWRITE_TAC [SKOLEM_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_ANTIDERIVATIVE_SEQUENCE THEN
    UNDISCH_TAC (← q r"convex(s:real^M->bool)") THEN SIMP_TAC [] THEN
    DISCH_THEN (K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f:num->real^M->real^N") THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f':num->real^M->real^M->real^N") THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [] THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [REAL_ARCH_INV]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"N:num") THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"n:num") THEN REWRITE_TAC [GE] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:real^M", ← q r"h:real^M"] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"inv(&n + &1) * norm(h:real^M)") THEN
    ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC [NORM_POS_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"inv(&N)") THEN ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_LE, REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC)

  let HAS_DERIVATIVE_SERIES ← prove
   r"!s f:num->real^M->real^N f' g' k.
        convex s /\
        (!n x. x IN s ==> ((f n) has_derivative (f' n x)) (at x within s)) /\
        (!e. &0 < e
             ==> ?N. !n x h. n >= N /\ x IN s
                             ==> norm(vsum(k INTER (0..n)) (\i. f' i x h) -
                                      g' x h) <= e * norm(h)) /\
        (?x l. x IN s /\ ((\n. f n x) sums l) k)
        ==> ?g. !x. x IN s ==> ((\n. f n x) sums (g x)) k /\
                               (g has_derivative g'(x)) (at x within s)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [sums] THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SEQUENCE THEN EXISTS_TAC
     (← q r"\n:num x:real^M h:real^M. vsum(k INTER (0..n)) (\n. f' n x h):real^N") THEN
    ASM_SIMP_TAC [ETA_AX, FINITE_INTER_NUMSEG, HAS_DERIVATIVE_VSUM])

  pure { HAS_DERIVATIVE_SEQUENCE_LIPSCHITZ, HAS_DERIVATIVE_SEQUENCE,
         HAS_ANTIDERIVATIVE_SEQUENCE, HAS_ANTIDERIVATIVE_LIMIT, HAS_DERIVATIVE_SERIES }

/- ------------------------------------------------------------------------- -/
/- Derivative with composed bilinear function.  (derivatives.ml 2301-2501)   -/
/- ------------------------------------------------------------------------- -/

structure DVG where
  HAS_DERIVATIVE_BILINEAR_WITHIN : thm
  HAS_DERIVATIVE_BILINEAR_AT : thm
  BILINEAR_DIFFERENTIABLE_AT_COMPOSE : thm
  BILINEAR_DIFFERENTIABLE_WITHIN_COMPOSE : thm
  BILINEAR_DIFFERENTIABLE_ON_COMPOSE : thm
  DIFFERENTIABLE_AT_LIFT_DOT2 : thm
  DIFFERENTIABLE_WITHIN_LIFT_DOT2 : thm
  DIFFERENTIABLE_ON_LIFT_DOT2 : thm
  HAS_DERIVATIVE_MUL_WITHIN : thm
  HAS_DERIVATIVE_MUL_AT : thm
  HAS_DERIVATIVE_SQNORM_AT : thm
  DIFFERENTIABLE_MUL_WITHIN : thm
  DIFFERENTIABLE_MUL_AT : thm
  DIFFERENTIABLE_SQNORM_AT : thm
  DIFFERENTIABLE_ON_MUL : thm
  DIFFERENTIABLE_ON_SQNORM : thm
  deriving Inhabited

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
@[nospecialize]
def setupDVG [HolBase] (D : DerivativesDeps) (BDVA : DVA) (BDVB : DVB) : ExceptT String IO DVG := do
  -- @@SCOPE BEGIN
  let { differentiable, DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON, differentiable_on,
        FRECHET_DERIVATIVE_WORKS, has_derivative_at, HAS_DERIVATIVE_ID,
        has_derivative_within, .. } := BDVA
  let { DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN, .. } := BDVB
  let { EQ_IMP, .. } := D.dg.pt.cvx.core1
  let { FUN_EQ_THM, IMP_IMP, .. } := D.dg.pt.cvx.core2
  let { REAL_ABS_INV, REAL_ABS_MUL, .. } := D.dg.pt.cvx.core3
  let { REAL_LE_INV_EQ, REAL_LE_LMUL, REAL_LE_MUL2, REAL_LE_TRANS, REAL_LET_TRANS,
        REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_MUL, REAL_LT_RDIV_EQ, .. } :=
        D.dg.pt.cvx.core4
  let { REAL_MUL_AC, REAL_MUL_LID, REAL_MUL_LINV, .. } := D.dg.pt.cvx.core5
  let { o_DEF, .. } := D.dg.pt.cvx.core6
  let { DOT_SYM, DROP_CMUL, LIFT_DROP, LINEAR_0, .. } := D.dg.pt.cvx.vec2
  let { NORM_MUL, NORM_POS_LE, NORM_POW_2, REAL_ABS_NORM, .. } := D.dg.pt.cvx.vec3
  let { bilinear, dist, linear, VECTOR_ADD_RID, VECTOR_SUB_REFL, VECTOR_SUB_RZERO, .. } :=
        D.dg.pt.cvx.vec4
  let { CONTINUOUS_WITHIN, .. } := D.dg.pt.cvx.top3
  let { LIM_ADD, LIM_CONST, LIM_SUB, LIM_WITHIN, .. } := D.dg.pt.cvx.top4
  let { ASM_MESON_TAC, MESON_TAC, VECTOR_ARITH_TAC, .. } := D.dg.pt.cvx
  let { BILINEAR_DOT, LIM_BILINEAR, .. } := D.qtopology1
  let { LIM_LINEAR, LIM_WITHIN_ID, WITHIN_UNIV, .. } := D.qtopology2
  let { BILINEAR_BOUNDED_POS, BILINEAR_DROP_MUL, BILINEAR_LADD, BILINEAR_LMUL,
        BILINEAR_LSUB, BILINEAR_LZERO, BILINEAR_RADD, BILINEAR_RMUL, BILINEAR_RSUB,
        BILINEAR_RZERO, LINEAR_BOUNDED_POS, .. } := D.qvec
  -- @@SCOPE END

  let HAS_DERIVATIVE_BILINEAR_WITHIN ← prove
   r"!h:real^M->real^N->real^P f g f' g' x:real^Q s.
        (f has_derivative f') (at x within s) /\
        (g has_derivative g') (at x within s) /\
        bilinear h
        ==> ((\x. h (f x) (g x)) has_derivative
             (\d. h (f x) (g' d) + h (f' d) (g x))) (at x within s)"
   (REPEAT STRIP_TAC THEN
    HolCore.Tactics.SUBGOAL_TAC HolBase.B "contg"
      (← q r"((g:real^Q->real^N) --> g(x)) (at x within s)")
     [REWRITE_TAC [← GSYM CONTINUOUS_WITHIN] THEN
      ASM_MESON_TAC [differentiable, DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN]] THEN
    UNDISCH_TAC (← q r"((f:real^Q->real^M) has_derivative f') (at x within s)") THEN
    REWRITE_TAC [has_derivative_within] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "df")) THEN
    HolCore.Tactics.SUBGOAL_TAC HolBase.B "contf"
     (← q r"((\y. (f:real^Q->real^M)(x) + f'(y - x)) --> f(x)) (at x within s)")
     [GEN_REWRITE_TAC LAND_CONV [← GSYM VECTOR_ADD_RID] THEN
      MATCH_MP_TAC LIM_ADD THEN REWRITE_TAC [LIM_CONST] THEN
      SUBGOAL_THEN (← q r"vec 0 = (f':real^Q->real^M)(x - x)") SUBST1_TAC THENL
       [ASM_MESON_TAC [LINEAR_0, VECTOR_SUB_REFL], ALL_TAC] THEN
      ASM_SIMP_TAC [LIM_LINEAR, LIM_SUB, LIM_CONST, LIM_WITHIN_ID]] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [has_derivative_within]) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dg")) THEN
    CONJ_TAC THENL
     [FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [bilinear]) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [linear]) THEN ASM_REWRITE_TAC [linear] THEN
      REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC,
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"at (x:real^Q) within s", ← q r"h:real^M->real^N->real^P"]
           LIM_BILINEAR) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    REMOVE_THEN "contg" MP_TAC THEN REMOVE_THEN "df" MP_TAC THEN
    REWRITE_TAC [IMP_IMP] THEN DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
    REMOVE_THEN "dg" MP_TAC THEN REMOVE_THEN "contf" MP_TAC THEN
    ONCE_REWRITE_TAC [IMP_IMP] THEN DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
    REWRITE_TAC [IMP_IMP] THEN DISCH_THEN (MP_TAC o MATCH_MP LIM_ADD) THEN
    SUBGOAL_THEN
     (← q r"((\y:real^Q. inv(norm(y - x)) %
                   (h:real^M->real^N->real^P) (f'(y - x)) (g'(y - x)))
      --> vec 0) (at x within s)")
    MP_TAC THENL
     [FIRST_ASSUM (X_CHOOSE_THEN (← q r"B:real") STRIP_ASSUME_TAC o MATCH_MP
                  BILINEAR_BOUNDED_POS) THEN
      X_CHOOSE_THEN (← q r"C:real") STRIP_ASSUME_TAC
       (← MATCH_MP LINEAR_BOUNDED_POS (← ASSUME (← q r"linear (f':real^Q->real^M)"))) THEN
      X_CHOOSE_THEN (← q r"D:real") STRIP_ASSUME_TAC
       (← MATCH_MP LINEAR_BOUNDED_POS (← ASSUME (← q r"linear (g':real^Q->real^N)"))) THEN
      REWRITE_TAC [LIM_WITHIN, dist, VECTOR_SUB_RZERO] THEN
      X_GEN_TAC (← q r"e:real") THEN STRIP_TAC THEN EXISTS_TAC (← q r"e / (B * C * D)") THEN
      ASM_SIMP_TAC [REAL_LT_DIV, NORM_MUL, REAL_LT_MUL] THEN
      X_GEN_TAC (← q r"x':real^Q") THEN
      REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_NORM, REAL_ABS_INV] THEN
      STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC (← q r"inv(norm(x' - x :real^Q)) *
                  B * (C * norm(x' - x)) * (D * norm(x' - x))") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC [REAL_LE_INV_EQ, NORM_POS_LE] THEN
        ASM_MESON_TAC [REAL_LE_LMUL, REAL_LT_IMP_LE, REAL_LE_MUL2, NORM_POS_LE,
                       REAL_LE_TRANS],
        ONCE_REWRITE_TAC [← AC REAL_MUL_AC
         (← q r"i * b * (c * x) * (d * x) = (i * x) * x * (b * c * d)")] THEN
        ASM_SIMP_TAC [REAL_MUL_LINV, REAL_LT_IMP_NZ, REAL_MUL_LID] THEN
        ASM_SIMP_TAC [← GSYM REAL_LT_RDIV_EQ, REAL_LT_MUL]],
      REWRITE_TAC [IMP_IMP] THEN DISCH_THEN (MP_TAC o MATCH_MP LIM_ADD) THEN
      REWRITE_TAC (← (do
        let hb ← ASSUME (← q r"bilinear(h:real^M->real^N->real^P)")
        [BILINEAR_RZERO, BILINEAR_LZERO, BILINEAR_LADD, BILINEAR_RADD,
         BILINEAR_LMUL, BILINEAR_RMUL, BILINEAR_LSUB, BILINEAR_RSUB].mapM
          (fun th => MATCH_MP th hb))) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
      BINOP_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN VECTOR_ARITH_TAC])

  let HAS_DERIVATIVE_BILINEAR_AT ← prove
   r"!h:real^M->real^N->real^P f g f' g' x:real^Q.
        (f has_derivative f') (at x) /\
        (g has_derivative g') (at x) /\
        bilinear h
        ==> ((\x. h (f x) (g x)) has_derivative
             (\d. h (f x) (g' d) + h (f' d) (g x))) (at x)"
   (REWRITE_TAC [has_derivative_at] THEN
    ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    REWRITE_TAC [← GSYM has_derivative_within, HAS_DERIVATIVE_BILINEAR_WITHIN])

  let BILINEAR_DIFFERENTIABLE_AT_COMPOSE ← prove
   r"!f:real^M->real^N g:real^M->real^P h:real^N->real^P->real^Q a.
        f differentiable at a /\ g differentiable at a /\ bilinear h
        ==> (\x. h (f x) (g x)) differentiable at a"
   (REPEAT GEN_TAC THEN REWRITE_TAC [FRECHET_DERIVATIVE_WORKS] THEN
    DISCH_THEN (MP_TAC o MATCH_MP HAS_DERIVATIVE_BILINEAR_AT) THEN
    REWRITE_TAC [← GSYM FRECHET_DERIVATIVE_WORKS, differentiable] THEN
    MESON_TAC [])

  let BILINEAR_DIFFERENTIABLE_WITHIN_COMPOSE ← prove
   r"!f:real^M->real^N g:real^M->real^P h:real^N->real^P->real^Q x s.
        f differentiable at x within s /\ g differentiable at x within s /\
        bilinear h
        ==> (\x. h (f x) (g x)) differentiable at x within s"
   (REPEAT GEN_TAC THEN REWRITE_TAC [FRECHET_DERIVATIVE_WORKS] THEN
    DISCH_THEN (MP_TAC o MATCH_MP HAS_DERIVATIVE_BILINEAR_WITHIN) THEN
    REWRITE_TAC [← GSYM FRECHET_DERIVATIVE_WORKS, differentiable] THEN
    MESON_TAC [])

  let BILINEAR_DIFFERENTIABLE_ON_COMPOSE ← prove
   r"!f:real^M->real^N g:real^M->real^P h:real^N->real^P->real^Q s.
        f differentiable_on s /\ g differentiable_on s /\ bilinear h
        ==> (\x. h (f x) (g x)) differentiable_on s"
   (REWRITE_TAC [differentiable_on] THEN
    MESON_TAC [BILINEAR_DIFFERENTIABLE_WITHIN_COMPOSE])

  let DIFFERENTIABLE_AT_LIFT_DOT2 ← prove
   r"!f:real^M->real^N g x.
        f differentiable at x /\ g differentiable at x
        ==> (\x. lift(f x dot g x)) differentiable at x"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP (← MATCH_MP (← REWRITE_RULE
     [← TAUT (← q r"p /\ q /\ r ==> s <=> r ==> p /\ q ==> s")]
    BILINEAR_DIFFERENTIABLE_AT_COMPOSE) BILINEAR_DOT)) THEN REWRITE_TAC [])

  let DIFFERENTIABLE_WITHIN_LIFT_DOT2 ← prove
   r"!f:real^M->real^N g x s.
        f differentiable (at x within s) /\ g differentiable (at x within s)
        ==> (\x. lift(f x dot g x)) differentiable (at x within s)"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP (← MATCH_MP (← REWRITE_RULE
     [← TAUT (← q r"p /\ q /\ r ==> s <=> r ==> p /\ q ==> s")]
    BILINEAR_DIFFERENTIABLE_WITHIN_COMPOSE) BILINEAR_DOT)) THEN REWRITE_TAC [])

  let DIFFERENTIABLE_ON_LIFT_DOT2 ← prove
   r"!f:real^M->real^N g s.
        f differentiable_on s /\ g differentiable_on s
        ==> (\x. lift(f x dot g x)) differentiable_on s"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP (← MATCH_MP (← REWRITE_RULE
     [← TAUT (← q r"p /\ q /\ r ==> s <=> r ==> p /\ q ==> s")]
    BILINEAR_DIFFERENTIABLE_ON_COMPOSE) BILINEAR_DOT)) THEN REWRITE_TAC [])

  let HAS_DERIVATIVE_MUL_WITHIN ← prove
   r"!f f' g:real^M->real^N g' a s.
        ((lift o f) has_derivative (lift o f')) (at a within s) /\
        (g has_derivative g') (at a within s)
        ==> ((\x. f x % g x) has_derivative
             (\h. f a % g' h + f' h % g a)) (at a within s)"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE [BILINEAR_DROP_MUL]
     (← ISPEC (← q r"\x y:real^M. drop x % y") HAS_DERIVATIVE_BILINEAR_WITHIN))) THEN
    REWRITE_TAC [o_DEF, DROP_CMUL, LIFT_DROP])

  let HAS_DERIVATIVE_MUL_AT ← prove
   r"!f f' g:real^M->real^N g' a.
        ((lift o f) has_derivative (lift o f')) (at a) /\
        (g has_derivative g') (at a)
        ==> ((\x. f x % g x) has_derivative
             (\h. f a % g' h + f' h % g a)) (at a)"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    REWRITE_TAC [HAS_DERIVATIVE_MUL_WITHIN])

  let HAS_DERIVATIVE_SQNORM_AT ← prove
   r"!a:real^N.
    ((\x. lift(norm x pow 2)) has_derivative (\x. &2 % lift(a dot x))) (at a)"
   (GEN_TAC THEN MP_TAC (← ISPECL
     [← q r"\x y:real^N. lift(x dot y)",
      ← q r"\x:real^N. x", ← q r"\x:real^N. x", ← q r"\x:real^N. x", ← q r"\x:real^N. x",
      ← q r"a:real^N"] HAS_DERIVATIVE_BILINEAR_AT) THEN
    REWRITE_TAC [HAS_DERIVATIVE_ID, BILINEAR_DOT, NORM_POW_2] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [FUN_EQ_THM, DOT_SYM] THEN VECTOR_ARITH_TAC)

  let DIFFERENTIABLE_MUL_WITHIN ← prove
   r"!f g:real^M->real^N a s.
        (lift o f) differentiable (at a within s) /\
        g differentiable (at a within s)
        ==> (\x. f x % g x) differentiable (at a within s)"
   (REPEAT GEN_TAC THEN MP_TAC (← ISPECL
     [← q r"lift o (f:real^M->real)", ← q r"g:real^M->real^N", ← q r"\x y:real^N. drop x % y",
      ← q r"a:real^M", ← q r"s:real^M->bool"] BILINEAR_DIFFERENTIABLE_WITHIN_COMPOSE) THEN
    REWRITE_TAC [o_DEF, LIFT_DROP, BILINEAR_DROP_MUL])

  let DIFFERENTIABLE_MUL_AT ← prove
   r"!f g:real^M->real^N a.
        (lift o f) differentiable (at a) /\ g differentiable (at a)
        ==> (\x. f x % g x) differentiable (at a)"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    REWRITE_TAC [DIFFERENTIABLE_MUL_WITHIN])

  let DIFFERENTIABLE_SQNORM_AT ← prove
   r"!a:real^N. (\x. lift(norm x pow 2)) differentiable (at a)"
   (REWRITE_TAC [differentiable] THEN MESON_TAC [HAS_DERIVATIVE_SQNORM_AT])

  let DIFFERENTIABLE_ON_MUL ← prove
   r"!f g:real^M->real^N s.
        (lift o f) differentiable_on s /\ g differentiable_on s
        ==> (\x. f x % g x) differentiable_on s"
   (REPEAT GEN_TAC THEN MP_TAC (← ISPECL
     [← q r"lift o (f:real^M->real)", ← q r"g:real^M->real^N", ← q r"\x y:real^N. drop x % y",
      ← q r"s:real^M->bool"] BILINEAR_DIFFERENTIABLE_ON_COMPOSE) THEN
    REWRITE_TAC [o_DEF, LIFT_DROP, BILINEAR_DROP_MUL])

  let DIFFERENTIABLE_ON_SQNORM ← prove
   r"!s:real^N->bool. (\x. lift(norm x pow 2)) differentiable_on s"
   (SIMP_TAC [DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON,
              DIFFERENTIABLE_SQNORM_AT])

  pure { HAS_DERIVATIVE_BILINEAR_WITHIN, HAS_DERIVATIVE_BILINEAR_AT,
         BILINEAR_DIFFERENTIABLE_AT_COMPOSE, BILINEAR_DIFFERENTIABLE_WITHIN_COMPOSE,
         BILINEAR_DIFFERENTIABLE_ON_COMPOSE, DIFFERENTIABLE_AT_LIFT_DOT2,
         DIFFERENTIABLE_WITHIN_LIFT_DOT2, DIFFERENTIABLE_ON_LIFT_DOT2,
         HAS_DERIVATIVE_MUL_WITHIN, HAS_DERIVATIVE_MUL_AT, HAS_DERIVATIVE_SQNORM_AT,
         DIFFERENTIABLE_MUL_WITHIN, DIFFERENTIABLE_MUL_AT, DIFFERENTIABLE_SQNORM_AT,
         DIFFERENTIABLE_ON_MUL, DIFFERENTIABLE_ON_SQNORM }

/- ------------------------------------------------------------------------- -/
/- Partial derivatives and jacobians are Baire functions; Frechet and        -/
/- Gateaux derivatives.  (derivatives.ml 2502-2793)                          -/
/- ------------------------------------------------------------------------- -/

structure DVH where
  BAIRE1_PARTIAL_DERIVATIVES : thm
  BAIRE1_DET_JACOBIAN : thm
  GATEAUX_DERIVATIVE_WITHIN : thm
  GATEAUX_DERIVATIVE : thm
  GATEAUX_DERIVATIVE_LIPSCHITZ : thm
  deriving Inhabited

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
@[nospecialize]
def setupDVH [HolBase] (D : DerivativesDeps) (BDVA : DVA) (BDVB : DVB) : ExceptT String IO DVH := do
  -- @@SCOPE BEGIN
  let { differentiable, DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT, has_derivative,
        has_derivative_at, .. } := BDVA
  let { DIFFERENTIABLE_IMP_CONTINUOUS_ON, .. } := BDVB
  let { CONTRAPOS_THM, EXTENSION, FINITE_IMAGE, FINITE_NUMSEG, FORALL_AND_THM,
        FORALL_IN_GSPEC, .. } := D.dg.pt.cvx.core1
  let { FORALL_IN_IMAGE, IMAGE_CLAUSES, IMAGE_EQ_EMPTY, IMP_CONJ, IMP_CONJ_ALT, IMP_IMP, ..
        } := D.dg.pt.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, IN_NUMSEG, IN_SING, IN_UNIV, LAMBDA_BETA, LAMBDA_ETA,
        LEFT_IMP_EXISTS_THM, REAL_ABS_DIV, REAL_ABS_INV, REAL_DIV_LMUL, .. } :=
        D.dg.pt.cvx.core3
  let { REAL_EQ_IMP_LE, REAL_INV_0, REAL_INV_LT_1, REAL_INV_MUL, REAL_LE_LDIV_EQ,
        REAL_LE_LMUL_EQ, REAL_LE_TRANS, REAL_LT_01, REAL_LT_DIV, REAL_LT_IMP_LE,
        REAL_LT_IMP_NZ, REAL_LT_INF_FINITE, REAL_LT_LDIV_EQ, REAL_LT_LMUL, REAL_LT_MIN,
        REAL_LTE_TRANS, .. } := D.dg.pt.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LINV, REAL_MUL_RID, REAL_MUL_SYM, SKOLEM_THM, SUBSET,
        SUBSET_EMPTY, .. } := D.dg.pt.cvx.core5
  let { o_DEF, real_abs, real_div, SWAP_FORALL_THM, UNIONS_0, UNIONS_IMAGE, UNIV_GSPEC, .. }
        := D.dg.pt.cvx.core6
  let { DIST_0, DIST_NZ, DIST_SYM, .. } := D.dg.pt.cvx.vec1
  let { DROP_EQ, DROP_VEC, FORALL_LIFT, LIFT_CMUL, LIFT_DROP, LIFT_EQ, LIFT_NUM, LINEAR_0,
        LINEAR_CMUL, LINEAR_SUB, LIPSCHITZ_ON_POS, NORM_0, NORM_BASIS, NORM_EQ_0, .. } :=
        D.dg.pt.cvx.vec2
  let { NORM_LIFT, NORM_MUL, NORM_NEG, NORM_POS_LT, REAL_ABS_NORM, .. } := D.dg.pt.cvx.vec3
  let { dist, VECTOR_ADD_RID, VECTOR_ADD_SUB, VECTOR_MUL_ASSOC, VECTOR_MUL_COMPONENT,
        VECTOR_MUL_EQ_0, VECTOR_MUL_LID, VECTOR_MUL_LZERO, VECTOR_MUL_RCANCEL,
        VECTOR_MUL_RZERO, VECTOR_SUB_EQ, VECTOR_SUB_LDISTRIB, VECTOR_SUB_REFL,
        VECTOR_SUB_RZERO, .. } := D.dg.pt.cvx.vec4
  let { EVENTUALLY_TRUE, .. } := D.dg.pt.cvx.met
  let { CLOSURE_CLOSED, .. } := D.dg.pt.cvx.top1
  let { COMPACT_SPHERE, CONTINUOUS_ADD, .. } := D.dg.pt.cvx.top2
  let { CONTINUOUS_CONST, CONTINUOUS_MUL, CONTINUOUS_ON_ADD, CONTINUOUS_ON_COMPOSE,
        CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID, CONTINUOUS_ON_INV, CONTINUOUS_ON_MUL,
        CONTINUOUS_ON_SUB, CONTINUOUS_ON_SUBSET, CONTINUOUS_VMUL, CONTINUOUS_WITHIN,
        CONTINUOUS_WITHIN_ID, EVENTUALLY_WITHIN, .. } := D.dg.pt.cvx.top3
  let { IN_BALL, IN_CBALL, IN_SPHERE, IN_SPHERE_0, LIM_ADD, LIM_CMUL, LIM_CONST,
        OPEN_CONTAINS_CBALL, .. } := D.dg.pt.cvx.top4
  let { SETDIST_LE_DIST, SETDIST_POS_LE, TRIVIAL_LIMIT_WITHIN, .. } := D.dg.pt.cvx.top5
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC, NORM_ARITH, num_CONV, REAL_ARITH,
        REAL_FIELD, SET_RULE, SET_TAC, VECTOR_ARITH, .. } := D.dg.pt.cvx
  let { SETDIST_EQ_0_SING, .. } := D.dg.pt.qtop
  let { COMPACT_IMP_TOTALLY_BOUNDED, CONTINUOUS_ON_LIFT_SETDIST, .. } := D.dg.qtopology1
  let { OPEN_CLOSED, SETDIST_POS_LT, SPHERE_EQ_EMPTY, .. } := D.dg.qtopology2
  let { LIFT_SUM, .. } := D.dg.qvec
  let { det, .. } := D.qdet
  let { FINITE_PERMUTATIONS, PERMUTES_IMAGE, .. } := D.qpermutations
  let { REAL_ABS_ABS, .. } := D.qsession
  let { BAIRE_CMUL, BAIRE_PRODUCT, BAIRE_VSUM, CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE,
        CONTINUOUS_ON_VMUL, LIM_AT, LIM_COMPONENT, LIMIT_POINT_OF_IMAGE, LIMPT_SUBSET, .. }
        := D.qtopology1
  let { baire, LIM_COMPOSE_AT, LIM_COMPOSE_WITHIN, LIM_NULL, LIM_NULL_CMUL, LIM_NULL_NORM,
        LIM_NULL_VMUL, LIM_TRANSFORM_EVENTUALLY, LIM_TRIVIAL, NETLIMIT_WITHIN,
        SEQ_HARMONIC_OFFSET, WITHIN_UNIV, .. } := D.qtopology2
  let { LINEAR_BOUNDED_POS, MATRIX_COMPONENT, transp, TRANSP_COMPONENT, VECTOR_EQ_ADDR, .. }
        := D.qvec
  -- @@SCOPE END

  let BAIRE1_PARTIAL_DERIVATIVES ← prove
   r"!f:real^M->real^N f' s i j.
        (!x. x IN s ==> (f has_derivative f'(x)) (at x)) /\
        open s /\
        1 <= i /\ i <= dimindex(:N) /\
        1 <= j /\ j <= dimindex(:M)
        ==> baire 1 s (\x. lift(matrix(f' x)$i$j))"
   (REPEAT STRIP_TAC THEN
    ABBREV_TAC
     (← q r"d = \n x. (if s = UNIV then &1 else setdist({x},(:real^M) DIFF s)) /
                (&n + &2)") THEN
    SUBGOAL_THEN (← q r"!n x. x IN s ==> &0 < (d:num->real^M->real) n x")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "d" THEN
      REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LT_DIV THEN
      REWRITE_TAC [← REAL_ARITH (← q r"&0 < &n + &2")] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_LT_01, SETDIST_POS_LT] THEN
      ASM_SIMP_TAC [SETDIST_EQ_0_SING, CLOSURE_CLOSED, ← GSYM OPEN_CLOSED] THEN
      ASM SET_TAC [],
      REWRITE_TAC [← ExceptT.mk (num_CONV (← q r"1")), baire]] THEN
    SUBGOAL_THEN (← q r"(f:real^M->real^N) continuous_on s") ASSUME_TAC THENL
     [ASM_MESON_TAC [DIFFERENTIABLE_IMP_CONTINUOUS_ON, differentiable,
                     DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT],
      ALL_TAC] THEN
    EXISTS_TAC
     (← q r"\n:num x.
          inv(d n x) % lift((f(x + d n x % basis j) -
                            (f:real^M->real^N) x)$i)") THEN
    REWRITE_TAC [] THEN CONJ_TAC THENL
     [X_GEN_TAC (← q r"n:num") THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      REWRITE_TAC [o_DEF] THEN CONJ_TAC THENL
       [MATCH_MP_TAC (← REWRITE_RULE [o_DEF] CONTINUOUS_ON_INV) THEN
        ASM_SIMP_TAC [REAL_LT_IMP_NZ],
        MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC [] THEN
        GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
          REWRITE_TAC [CONTINUOUS_ON_ID] THEN
          MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC [o_DEF],
          FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
          REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
          X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN EXPAND_TAC "d" THEN
          COND_CASES_TAC THEN ASM_REWRITE_TAC [IN_UNIV] THEN
          ONCE_REWRITE_TAC [← SET_RULE (← q r"x IN s <=> ~(x IN UNIV DIFF s)")] THEN
          DISCH_THEN (MP_TAC o SPECL [← q r"{x:real^M}", ← q r"x:real^M"] o MATCH_MP
           (← REWRITE_RULE [IMP_CONJ_ALT] SETDIST_LE_DIST)) THEN
          REWRITE_TAC [IN_SING, ← NORM_ARITH (← q r"dist(x:real^N,x + y) = norm y")] THEN
          ASM_SIMP_TAC [NORM_MUL, REAL_ABS_DIV, NORM_BASIS, REAL_MUL_RID] THEN
          REWRITE_TAC [← REAL_ARITH (← q r"abs(&n + &2) = &n + &2")] THEN
          MATCH_MP_TAC (← REAL_ARITH
           (← q r"&0 <= x /\ x * inv n < x * &1 ==> ~(x <= abs x / n)")) THEN
          REWRITE_TAC [SETDIST_POS_LE] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
          SIMP_TAC [REAL_INV_LT_1, ← REAL_ARITH (← q r"&1 < &n + &2")] THEN
          REWRITE_TAC [SETDIST_POS_LT] THEN
          ASM_SIMP_TAC [SETDIST_EQ_0_SING, CLOSURE_CLOSED,
                        ← GSYM OPEN_CLOSED] THEN
          ASM SET_TAC []]] THEN
      EXPAND_TAC "d" THEN REWRITE_TAC [real_div, LIFT_CMUL] THEN
      ASM_CASES_TAC (← q r"s = (:real^M)") THEN
      ASM_REWRITE_TAC [CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC [o_DEF] THEN
      REWRITE_TAC [CONTINUOUS_ON_LIFT_SETDIST],
      X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN
      REWRITE_TAC [← GSYM VECTOR_MUL_COMPONENT, ← GSYM LIFT_CMUL] THEN
      ONCE_REWRITE_TAC [← GSYM TRANSP_COMPONENT] THEN
      MATCH_MP_TAC LIM_COMPONENT THEN
      ASM_SIMP_TAC [LAMBDA_BETA, MATRIX_COMPONENT, transp, LAMBDA_ETA] THEN
      ONCE_REWRITE_TAC [LIM_NULL] THEN REWRITE_TAC [] THEN
      SUBGOAL_THEN
       (← q r"(\n. inv(d n x) % (f (x + d n x % basis j) - f x) - f' x (basis j)) =
        (\y. inv(norm(y - x)) % ((f:real^M->real^N) y -
                                 (f x + f' x (y - x)))) o
        (\n:num. x + d n x % basis j)")
      SUBST1_TAC THENL
       [REWRITE_TAC [o_DEF, VECTOR_ADD_SUB, NORM_MUL] THEN
        ASM_SIMP_TAC [real_abs, REAL_LT_IMP_LE, NORM_BASIS] THEN
        SUBGOAL_THEN
         (← q r"!a y. (f':real^M->real^M->real^N) x (a % y) = a % f' x y")
        (fun th => REWRITE_TAC [th]) THENL
         [REPEAT GEN_TAC THEN MATCH_MP_TAC LINEAR_CMUL THEN
          ASM_MESON_TAC [has_derivative],
          REWRITE_TAC [← VECTOR_ARITH (← q r"x - (y + z):real^N = x - y - z")] THEN
          REWRITE_TAC [REAL_MUL_RID, VECTOR_SUB_LDISTRIB] THEN
          ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, REAL_LT_IMP_NZ] THEN
          REWRITE_TAC [VECTOR_MUL_LID]],
        MATCH_MP_TAC LIM_COMPOSE_AT THEN EXISTS_TAC (← q r"x:real^M") THEN
        RULE_ASSUM_TAC (REWRITE_RULE [has_derivative_at]) THEN
        ASM_SIMP_TAC [VECTOR_SUB_REFL] THEN
        REWRITE_TAC [NORM_0, REAL_INV_0, VECTOR_MUL_LZERO, EVENTUALLY_TRUE] THEN
        GEN_REWRITE_TAC LAND_CONV [← GSYM VECTOR_ADD_RID] THEN
        MATCH_MP_TAC LIM_ADD THEN REWRITE_TAC [LIM_CONST] THEN
        MATCH_MP_TAC LIM_NULL_VMUL THEN EXPAND_TAC "d" THEN
        REWRITE_TAC [LIFT_CMUL, real_div] THEN MATCH_MP_TAC LIM_NULL_CMUL THEN
        REWRITE_TAC [SEQ_HARMONIC_OFFSET]]])

  let BAIRE1_DET_JACOBIAN ← prove
   r"!f:real^N->real^N f' s.
        (!x. x IN s ==> (f has_derivative f'(x)) (at x)) /\ open s
        ==> baire 1 s (\x. lift(det(matrix(f' x))))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [det, LIFT_SUM, o_DEF] THEN
    MATCH_MP_TAC BAIRE_VSUM THEN
    SIMP_TAC [FINITE_PERMUTATIONS, FINITE_NUMSEG, FORALL_IN_GSPEC] THEN
    X_GEN_TAC (← q r"p:num->num") THEN DISCH_TAC THEN REWRITE_TAC [LIFT_CMUL] THEN
    MATCH_MP_TAC BAIRE_CMUL THEN MATCH_MP_TAC BAIRE_PRODUCT THEN
    REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC BAIRE1_PARTIAL_DERIVATIVES THEN
    EXISTS_TAC (← q r"f:real^N->real^N") THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP PERMUTES_IMAGE) THEN
    REWRITE_TAC [EXTENSION, IN_IMAGE, IN_NUMSEG] THEN ASM_MESON_TAC [])

  let GATEAUX_DERIVATIVE_WITHIN ← prove
   r"!f:real^M->real^N f' s x y.
        (f has_derivative f') (at x within s)
        ==> ((\t. inv(drop t) % (f(x + drop t % y) - f(x))) --> f' y)
            (at (vec 0) within {t | (x + drop t % y) IN s})"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"y:real^M = vec 0") THENL
     [DISCH_THEN (ASSUME_TAC o MATCH_MP LINEAR_0 o CONJUNCT1 o
        REWRITE_RULE [has_derivative]) THEN
      ASM_REWRITE_TAC [DROP_VEC, VECTOR_MUL_RZERO, VECTOR_ADD_RID,
                       VECTOR_SUB_REFL, LIM_CONST],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"trivial_limit (at (x:real^M) within s)") THENL
     [DISCH_THEN (K ALL_TAC) THEN MATCH_MP_TAC LIM_TRIVIAL THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [TRIVIAL_LIMIT_WITHIN]) THEN
      REWRITE_TAC [TRIVIAL_LIMIT_WITHIN, CONTRAPOS_THM] THEN
      DISCH_THEN (MP_TAC o ISPEC (← q r"\r. (x:real^M) + drop r % y") o
          MATCH_MP (← REWRITE_RULE [IMP_CONJ] LIMIT_POINT_OF_IMAGE)) THEN
      REWRITE_TAC [← VECTOR_ARITH (← q r"a + x:real^N = a + y <=> x = y")] THEN
      ASM_REWRITE_TAC [VECTOR_MUL_RCANCEL, DROP_EQ] THEN ANTS_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC [CONTINUOUS_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_VMUL THEN
        ASM_REWRITE_TAC [o_DEF, LIFT_DROP, CONTINUOUS_WITHIN_ID],
        REWRITE_TAC [DROP_VEC, VECTOR_MUL_LZERO, VECTOR_ADD_RID] THEN
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] LIMPT_SUBSET) THEN SET_TAC []],
      ALL_TAC] THEN
    ASM_SIMP_TAC [has_derivative, NETLIMIT_WITHIN] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP LINEAR_0) THEN
    FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP LINEAR_CMUL) THEN
    ASM_CASES_TAC (← q r"y:real^M = vec 0") THEN
    ASM_REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_ADD_RID,
                     VECTOR_SUB_REFL, LIM_CONST] THEN
    ONCE_REWRITE_TAC [LIM_NULL] THEN
    SUBGOAL_THEN
     (← q r"(\t. x + drop t % (y:real^M)) continuous
      (at (vec 0) within {t | (x + drop t % y:real^M) IN s})")
    MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC [CONTINUOUS_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_MUL THEN REWRITE_TAC [CONTINUOUS_CONST] THEN
      REWRITE_TAC [o_DEF, LIFT_DROP, CONTINUOUS_WITHIN_ID],
      REWRITE_TAC [CONTINUOUS_WITHIN, DROP_VEC, VECTOR_MUL_LZERO] THEN
      REWRITE_TAC [VECTOR_ADD_RID, IMP_IMP]] THEN
    DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE
     [← TAUT (← q r"p /\ q /\ r ==> s <=> p /\ r ==> q ==> s")] LIM_COMPOSE_WITHIN)) THEN
    ASM_REWRITE_TAC [o_DEF, VECTOR_EQ_ADDR, VECTOR_MUL_EQ_0] THEN
    REWRITE_TAC [← GSYM LIFT_EQ, LIFT_NUM, LIFT_DROP] THEN
    SIMP_TAC [EVENTUALLY_WITHIN, ← GSYM DIST_NZ, VECTOR_ADD_SUB, IN_ELIM_THM] THEN
    ANTS_TAC THENL [MESON_TAC [REAL_LT_01], ALL_TAC] THEN
    ASM_REWRITE_TAC [NORM_MUL, REAL_INV_MUL, VECTOR_SUB_RZERO] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"norm(y:real^M)") o MATCH_MP LIM_CMUL) THEN
    REWRITE_TAC [VECTOR_MUL_ASSOC, ← GSYM REAL_MUL_ASSOC, VECTOR_MUL_RZERO] THEN
    ASM_SIMP_TAC [NORM_EQ_0, ← REAL_FIELD (← q r"~(y = &0) ==> y * x * inv y = x")] THEN
    ONCE_REWRITE_TAC [LIM_NULL_NORM] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
    REWRITE_TAC [EVENTUALLY_WITHIN, DIST_0, NORM_POS_LT, IN_ELIM_THM] THEN
    EXISTS_TAC (← q r"&1") THEN REWRITE_TAC [REAL_LT_01, FORALL_LIFT, LIFT_DROP] THEN
    REWRITE_TAC [← GSYM DROP_EQ, DROP_VEC, LIFT_DROP] THEN
    X_GEN_TAC (← q r"t:real") THEN STRIP_TAC THEN
    REWRITE_TAC [NORM_MUL, REAL_ABS_INV, REAL_ABS_ABS] THEN
    REWRITE_TAC [← GSYM REAL_ABS_INV, ← GSYM NORM_MUL] THEN
    AP_TERM_TAC THEN REWRITE_TAC [VECTOR_SUB_LDISTRIB] THEN
    MATCH_MP_TAC (← VECTOR_ARITH
      (← q r"a % y:real^N = z ==> c - a % (x + y) = c - a % x - z")) THEN
    ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, VECTOR_MUL_LID])

  let GATEAUX_DERIVATIVE ← prove
   r"!f:real^M->real^N f' x y.
        (f has_derivative f') (at x)
        ==> ((\t. inv(drop t) % (f(x + drop t % y) - f(x))) --> f' y)
            (at (vec 0))"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN DISCH_THEN
     (MP_TAC o SPEC (← q r"y:real^M") o MATCH_MP GATEAUX_DERIVATIVE_WITHIN) THEN
    REWRITE_TAC [IN_UNIV, UNIV_GSPEC])

  let GATEAUX_DERIVATIVE_LIPSCHITZ ← prove
   r"!f:real^M->real^N f' x s.
        x IN s /\ open s /\
        (?B. !u v. u IN s /\ v IN s ==> norm(f u - f v) <= B * norm(u - v)) /\
        linear f' /\
        (!y. ((\t. inv(drop t) % (f(x + drop t % y) - f(x))) --> f' y)
             (at (vec 0)))
        ==> (f has_derivative f') (at x)"
   (REWRITE_TAC [LIPSCHITZ_ON_POS] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"x:real^M") o
      GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"r:real") STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP LINEAR_BOUNDED_POS) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"D:real") STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [has_derivative_at, LIM_AT, DIST_0] THEN
    X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
    MP_TAC (← ISPEC (← q r"sphere(vec 0:real^M,&1)") COMPACT_IMP_TOTALLY_BOUNDED) THEN
    REWRITE_TAC [COMPACT_SPHERE] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"e / (B + D + &1)")) THEN
    ASM_SIMP_TAC [REAL_LT_DIV, LEFT_IMP_EXISTS_THM,
                  ← REAL_ARITH (← q r"&0 < B /\ &0 < D ==> &0 < B + D + &1")] THEN
    X_GEN_TAC (← q r"k:real^M->bool") THEN ASM_CASES_TAC (← q r"k:real^M->bool = {}") THEN
    ASM_REWRITE_TAC [IMAGE_CLAUSES, UNIONS_0, SUBSET_EMPTY, SPHERE_EQ_EMPTY] THENL
     [ASM_REAL_ARITH_TAC, STRIP_TAC] THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE BINDER_CONV [LIM_AT]) THEN
    REWRITE_TAC [DIST_0] THEN ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"e / (B + D + &1)")) THEN
    ASM_SIMP_TAC [REAL_LT_DIV, LEFT_IMP_EXISTS_THM,
                  ← REAL_ARITH (← q r"&0 < B /\ &0 < D ==> &0 < B + D + &1")] THEN
    ASM_REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM, FORALL_AND_THM] THEN
    X_GEN_TAC (← q r"d:real^M->real") THEN STRIP_TAC THEN
    EXISTS_TAC (← q r"min r (inf (IMAGE (d:real^M->real) k))") THEN
    REWRITE_TAC [REAL_LT_MIN] THEN
    ASM_SIMP_TAC [REAL_LT_INF_FINITE, FINITE_IMAGE, IMAGE_EQ_EMPTY] THEN
    ASM_REWRITE_TAC [FORALL_IN_IMAGE, dist, NORM_POS_LT, VECTOR_SUB_EQ] THEN
    X_GEN_TAC (← q r"y:real^M") THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [UNIONS_IMAGE]) THEN
    REWRITE_TAC [SUBSET, IN_SPHERE, IN_ELIM_THM] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"inv(norm(y - x)) % (y - x):real^M")) THEN
    REWRITE_TAC [DIST_0, NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
    ASM_SIMP_TAC [REAL_MUL_LINV, NORM_EQ_0, VECTOR_SUB_EQ, IN_BALL] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:real^M") STRIP_ASSUME_TAC) THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_MUL_SYM] (← GSYM real_div)] THEN
    ASM_SIMP_TAC [REAL_LT_LDIV_EQ, NORM_POS_LT, VECTOR_SUB_EQ] THEN
    TRANS_TAC REAL_LTE_TRANS
     (← q r"(B + D + &1) * e / (B + D + &1) * norm(y - x:real^M)") THEN
    CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC [REAL_MUL_ASSOC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
     [← q r"u:real^M", ← q r"lift(norm(y - x:real^M))"]) THEN
    ASM_SIMP_TAC [NORM_LIFT, REAL_ABS_NORM] THEN
    ASM_SIMP_TAC [NORM_POS_LT, VECTOR_SUB_EQ, LIFT_DROP] THEN
    SUBGOAL_THEN
     (← q r"f' u = inv(norm(y - x:real^M)) % norm(y - x) % (f':real^M->real^N) u")
    SUBST1_TAC THENL
     [ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, NORM_EQ_0,
                    VECTOR_SUB_EQ, VECTOR_MUL_LID],
      REWRITE_TAC [dist, ← GSYM VECTOR_SUB_LDISTRIB, NORM_MUL]] THEN
    REWRITE_TAC [REAL_ABS_INV, REAL_ABS_NORM, ← GSYM DROP_EQ, DROP_VEC] THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_MUL_SYM] (← GSYM real_div)] THEN
    ASM_SIMP_TAC [REAL_LT_LDIV_EQ, NORM_POS_LT, VECTOR_SUB_EQ] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"y - x <= B * e + D * e ==> x < e ==> y < (B + D + &1) * e")) THEN
    MATCH_MP_TAC (← NORM_ARITH
     (← q r"norm(y - z:real^M) <= a /\ norm(d - e) <= b
      ==> norm(y - (x + d)) - norm(z - x - e) <= a + b")) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM (fun th =>
        W (MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE [SUBSET]) THEN
        RULE_ASSUM_TAC (REWRITE_RULE [SUBSET, IN_SPHERE_0]) THEN
        ASM_SIMP_TAC [IN_CBALL, ← ONCE_REWRITE_RULE [DIST_SYM] dist, REAL_ABS_NORM,
          REAL_LT_IMP_LE, VECTOR_ADD_SUB, NORM_MUL, REAL_MUL_RID],
        ALL_TAC],
      ASM_SIMP_TAC [← GSYM LINEAR_CMUL, ← GSYM LINEAR_SUB] THEN
      FIRST_X_ASSUM (fun th =>
        W (MP_TAC o PART_MATCH lhand th o lhand o snd))] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    ASM_SIMP_TAC [REAL_LE_LMUL_EQ, ← GSYM REAL_LE_LDIV_EQ,
                  NORM_POS_LT, VECTOR_SUB_EQ] THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_MUL_SYM] real_div] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
     [← GSYM REAL_ABS_NORM] THEN
    REWRITE_TAC [← GSYM REAL_ABS_INV, ← GSYM NORM_MUL] THEN
    REWRITE_TAC [NORM_NEG, ← VECTOR_ARITH
     (← q r"a % (y - (x + b % u)):real^M = --((a * b) % u - a % (y - x)) /\
      a % (y - x - b % u):real^M = --((a * b) % u - a % (y - x))")] THEN
    ASM_SIMP_TAC [REAL_MUL_LINV, NORM_EQ_0, VECTOR_SUB_EQ] THEN
    ONCE_REWRITE_TAC [← GSYM dist] THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_MUL_SYM] (← GSYM real_div)] THEN
    ASM_SIMP_TAC [VECTOR_MUL_LID, REAL_LT_IMP_LE])

  pure { BAIRE1_PARTIAL_DERIVATIVES, BAIRE1_DET_JACOBIAN, GATEAUX_DERIVATIVE_WITHIN,
         GATEAUX_DERIVATIVE, GATEAUX_DERIVATIVE_LIPSCHITZ }

/- ------------------------------------------------------------------------- -/
/- Strong form of the inverse function theorem not assuming continuity of    -/
/- the derivative (Saint Raymond).  (derivatives.ml 2794-3955)               -/
/- ------------------------------------------------------------------------- -/

structure DVI where
  INVERSE_FUNCTION_THEOREM : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDVI [HolBase] (D : DerivativesDeps) (BDVA : DVA) (BDVB : DVB) (BDVD : DVD) (BDVE : DVE) (BDVG : DVG) : ExceptT String IO DVI := do
  -- @@SCOPE BEGIN
  let { differentiable, DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT, has_derivative,
        HAS_DERIVATIVE_AT_WITHIN, HAS_DERIVATIVE_CONST, HAS_DERIVATIVE_SUB, .. } := BDVA
  let { DIFF_CHAIN_AT, DIFFERENTIABLE_IMP_CONTINUOUS_ON, HAS_DERIVATIVE_AT_ALT, .. } := BDVB
  let { DIFFERENTIABLE_FINITE_PREIMAGES, .. } := BDVD
  let { DIFFERENTIABLE_IMP_OPEN_MAP, HAS_DERIVATIVE_INVERSE_STRONG, SUSSMANN_OPEN_MAPPING,
        .. } := BDVE
  let { HAS_DERIVATIVE_SQNORM_AT, .. } := BDVG
  let { ARITH, CONJ_ASSOC, CONTRAPOS_THM, DE_MORGAN_THM, DISJ_SYM, DISJOINT, EMPTY_UNIONS,
        ETA_AX, EXISTS_IN_GSPEC, EXISTS_IN_IMAGE, EXISTS_PASTECART, EXTENSION,
        FINITE_DELETE, FINITE_SUBSET, FORALL_AND_THM, FORALL_IN_GSPEC, .. } :=
        D.dg.pt.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_PASTECART, FSTCART_PASTECART, FUN_EQ_THM, FUN_IN_IMAGE,
        IMAGE_EQ_EMPTY, IMP_CONJ, IMP_CONJ_ALT, IMP_IMP, IN, IN_DELETE, IN_DIFF, INF,
        INTER_COMM, INTER_SUBSET, INTER_UNIONS, .. } := D.dg.pt.cvx.core2
  let { I_THM, IN_ELIM_THM, IN_IMAGE, IN_INTER, IN_SING, IN_UNION, IN_UNIONS, IN_UNIV,
        LE_REFL, LEFT_EXISTS_AND_THM, LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY, MONO_EXISTS,
        MONO_OR, NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, PASTECART_IN_PCROSS,
        PCROSS_EQ_EMPTY, .. } := D.dg.pt.cvx.core3
  let { REAL_EQ_IMP_LE, REAL_LE_ANTISYM, REAL_LE_INV2, REAL_LE_LADD, REAL_LE_LMUL_EQ,
        REAL_LE_MIN, REAL_LE_RADD, REAL_LE_RDIV_EQ, REAL_LE_REFL, REAL_LE_RMUL,
        REAL_LE_TRANS, REAL_LET_TRANS, REAL_LT_01, REAL_LT_DIV, REAL_LT_IMP_LE,
        REAL_LT_IMP_NZ, REAL_LT_INV_EQ, REAL_LT_LADD, REAL_LT_LDIV_EQ, REAL_LT_LMUL_EQ,
        REAL_LT_MIN, REAL_LT_MUL, REAL_LT_RDIV_EQ, REAL_LTE_TRANS, REAL_MIN_LT, .. } :=
        D.dg.pt.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_RINV, REAL_MUL_SYM, REAL_NOT_LE, REAL_NOT_LT,
        REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_POW_LT, RIGHT_EXISTS_AND_THM,
        RIGHT_IMP_EXISTS_THM, RIGHT_IMP_FORALL_THM, SIMPLE_IMAGE, SKOLEM_THM,
        SNDCART_PASTECART, SUBSET, SUBSET_INTER, SUBSET_REFL, SUBSET_TRANS, SUBSET_UNION, ..
        } := D.dg.pt.cvx.core5
  let { o_DEF, o_THM, pairwise, real_div, SUP, SWAP_EXISTS_THM, UNIONS_0, UNIONS_GSPEC,
        UNIONS_INSERT, .. } := D.dg.pt.cvx.core6
  let { CARD_LE_RELATIONAL_FULL, .. } := D.dg.pt.cvx.lib
  let { MONOTONE_BIGGER, REAL_HALF, .. } := D.dg.pt.cvx.misc
  let { DIST_0, DIST_SYM, .. } := D.dg.pt.cvx.vec1
  let { DROP_CMUL, DROP_SUB, DROP_VEC, EXISTS_LIFT, FORALL_LIFT, LIFT_DROP, LINEAR_0,
        LINEAR_CMUL, LINEAR_FSTCART, LINEAR_SNDCART, LINEAR_SUB, NORM_0, NORM_1, .. } :=
        D.dg.pt.cvx.vec2
  let { NORM_LIFT, NORM_MUL, NORM_NEG, NORM_POS_LE, NORM_POS_LT, NORM_POW_2, NORM_SUB,
        PASTECART_VEC, .. } := D.dg.pt.cvx.vec3
  let { dist, VECTOR_ADD_SUB, VECTOR_MUL_ASSOC, VECTOR_MUL_EQ_0, VECTOR_MUL_LID,
        VECTOR_MUL_LZERO, VECTOR_MUL_RZERO, VECTOR_NEG_SUB, VECTOR_SUB_EQ,
        VECTOR_SUB_LDISTRIB, VECTOR_SUB_REFL, VECTOR_SUB_RZERO, .. } := D.dg.pt.cvx.vec4
  let { EVENTUALLY_SEQUENTIALLY, .. } := D.dg.pt.cvx.met
  let { BALL_MIN_INTER, BALL_SUBSET_CBALL, BOUNDED_BALL, BOUNDED_SUBSET,
        BOUNDED_TRANSLATION_EQ, CBALL_DIFF_SPHERE, CBALL_EQ_EMPTY, CENTRE_IN_BALL,
        CLOSED_CBALL, CLOSED_CLOSURE, CLOSURE_APPROACHABLE, CLOSURE_BALL, .. } :=
        D.dg.pt.cvx.top1
  let { CLOSURE_SUBSET, CLOSURE_UNION, COMPACT_CBALL, COMPACT_CONTINUOUS_IMAGE,
        COMPACT_HAUSDIST, COMPACT_IMP_BOUNDED, COMPONENTS_MAXIMAL, CONNECTED_CLOSED,
        CONNECTED_CONTINUOUS_IMAGE, CONNECTED_INSERT, CONNECTED_INTER_FRONTIER, .. } :=
        D.dg.pt.cvx.top2
  let { CONTINUOUS_ON_ADD, CONTINUOUS_ON_CONST, CONTINUOUS_ON_MUL, CONTINUOUS_ON_SUB,
        CONTINUOUS_ON_SUBSET, DISTANCE_ATTAINS_SUP, FRONTIER_BALL, HAUSDIST_SYM, .. } :=
        D.dg.pt.cvx.top3
  let { HOMEOMORPHISM, IN_BALL, IN_CBALL, IN_COMPONENTS_CONNECTED, IN_COMPONENTS_NONEMPTY,
        IN_COMPONENTS_SUBSET, IN_INTERVAL_1, IN_SPHERE, INTERIOR_OPEN, INTERVAL_EQ_EMPTY_1,
        LINEAR_CONTINUOUS_ON, OPEN_BALL, OPEN_CONTAINS_CBALL, .. } := D.dg.pt.cvx.top4
  let { bounded, continuous_at, frontier, OPEN_IN_OPEN_EQ, OPEN_INTER,
        OPEN_INTER_CLOSURE_EQ_EMPTY, OPEN_UNIV, REAL_ABS_HAUSDIST,
        REAL_LT_HAUSDIST_POINT_EXISTS, SUBSET_CBALL, SUBSET_CLOSURE, UNIONS_COMPONENTS, .. }
        := D.dg.pt.cvx.top5
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON, MESON_TAC, NORM_ARITH, REAL_ARITH,
        REAL_ARITH_TAC, REAL_FIELD, SET_RULE, SET_TAC, VECTOR_ARITH, .. } := D.dg.pt.cvx
  let { REAL_SUP_LE, .. } := D.dg.pt.qses
  let { DROP_NEG, .. } := D.dg.pt.qvec
  let { BOUNDED_INTER, SUBSET_BALL, .. } := D.dg.pt.qtop
  let { CONVEX_BALL, CONVEX_INTER, .. } := D.dg.pt.qcvx2
  let { CONVEX_CONNECTED, .. } := D.dg.qconvex
  let { INVERTIBLE_DET_NZ, .. } := D.dg.qdet
  let { CARD_LE_FINITE, .. } := D.dg.qcard
  let { EVENTUALLY_AND, .. } := D.dg.qmetric
  let { COMPACT_PATH_IMAGE, CONNECTED_PATH_IMAGE, .. } := D.dg.qpaths1
  let { OPEN_COMPONENTS, OPEN_CONNECTED_COMPONENT, PATH_IMAGE_NONEMPTY,
        PATHFINISH_IN_PATH_IMAGE, PATHSTART_IN_PATH_IMAGE, .. } := D.dg.qpaths2
  let { CBALL_MIN_INTER, CLOSURE_UNIONS, COMPACT_UNIFORMLY_CONTINUOUS, .. } :=
        D.dg.qtopology1
  let { FRONTIER_INTER_SUBSET, SEPARATION_OPEN_IN_UNION, tendsto, .. } := D.dg.qtopology2
  let { MATRIX_INVERTIBLE, .. } := D.dg.qvec
  let { CONNECTED_BALL, CONNECTED_CBALL, CONNECTED_INTERVAL, .. } := D.qconvex
  let { ARCH_EVENTUALLY_INV1, .. } := D.qmetric
  let { CONNECTED_INFINITE_IFF_CARD_EQ, CONNECTED_OPEN_PATH_CONNECTED, path_connected, .. }
        := D.qpaths
  let { INFINITE, INJECTIVE_ON_LEFT_INVERSE, REAL_LE_LCANCEL_IMP, REAL_LE_SUB_RADD,
        REAL_LE_SUP, REAL_LE_TRANS_LTE, REAL_LT_RMUL_EQ, .. } := D.qsession
  let { CBALL_DIFF_BALL, CLOSURE_NONEMPTY_OPEN_INTER, COMPONENTS_NONOVERLAP,
        CONNECTED_CARD_EQ_IFF_NONTRIVIAL, CONNECTED_COMPONENT_IN_COMPONENTS,
        CONNECTED_COMPONENT_REFL, CONNECTED_HAUSDIST_LIMIT, CONNECTED_PCROSS_EQ,
        CONTINUOUS_ON_EQ_CONTINUOUS_AT, CONTINUOUS_OPEN_PREIMAGE, EXISTS_COMPONENT_SUPERSET,
        FRONTIER_OPEN_MAP_IMAGE_SUBSET, HAUSDIST_UNIFORMLY_CONTINUOUS_ON,
        IMAGE_CLOSURE_SUBSET, .. } := D.qtopology1
  let { open_def, OPEN_UNION, SUBSET_COMPACT_HAUSDIST_LIMIT, SUBSET_INTERIOR_EQ, .. } :=
        D.qtopology2
  let { LINEAR_BOUNDED_POS, LINEAR_NEG, NORM_LT_SQUARE, NORM_PASTECART_LE, .. } := D.qvec
  -- @@SCOPE END

  let INVERSE_FUNCTION_THEOREM ← (do
    let et ← q r"e:real"
    let randIs : term → thm → Bool := fun e th =>
      match HolCore.Kernel.rand (concl th) with
      | .ok t => decide (t = e)
      | .error _ => false
    let hu ← ASSUME (← q r"(u:real^N->bool) IN U")
    prove
     r"!f:real^N->real^N f' a s.
        open s /\ a IN s /\
        (!x. x IN s
             ==> (f has_derivative f' x) (at x) /\ ~(det(matrix (f' x)) = &0))
        ==> ?t u g g'. open t /\ a IN t /\ t SUBSET s /\ open u /\ f a IN u /\
                       homeomorphism (t,u) (f,g) /\
                       (!x. x IN t
                            ==> (f has_derivative f' x) (at x) /\
                                f'(x) o g'(f x) = I /\ g'(f x) o f'(x) = I) /\
                       (!y. y IN u
                            ==> (g has_derivative g' y) (at y) /\
                                f'(g y) o g' y = I /\ g' y o f'(g y) = I)"
     (REWRITE_TAC [← TAUT (← q r"p ==> q /\ r <=> (p ==> q) /\ (p ==> r)")] THEN
      REWRITE_TAC [FORALL_AND_THM] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"!x. x IN s
            ==> ?g. linear g /\
                    (f':real^N->real^N->real^N) x o g = I /\ g o f' x = I")
      MP_TAC THENL
       [REPEAT STRIP_TAC THEN
        W (MP_TAC o PART_MATCH (rand o rand) MATRIX_INVERTIBLE o snd) THEN
        REWRITE_TAC [INVERTIBLE_DET_NZ] THEN ASM_MESON_TAC [has_derivative],
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM]] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM, SKOLEM_THM] THEN
      X_GEN_TAC (← q r"g':real^N->real^N->real^N") THEN
      REWRITE_TAC [← TAUT (← q r"p ==> q /\ r <=> (p ==> q) /\ (p ==> r)")] THEN
      REWRITE_TAC [FORALL_AND_THM] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"?u. open u /\ a IN u /\
            (!x y. x IN u /\ y IN u /\ (f:real^N->real^N) x = f y ==> x = y)")
      MP_TAC THENL
       [UNDISCH_TAC (← q r"(a:real^N) IN s") THEN
        SPEC_TAC ((← q r"a:real^N"), (← q r"x:real^N")),
        DISCH_THEN (MP_TAC o SPEC (← q r"s:real^N->bool") o MATCH_MP (← MESON [INTER_SUBSET]
         (← q r"(?t. P t)
          ==> !s. (!t. P t ==> P(s INTER t)) ==> ?t. t SUBSET s /\ P t"))) THEN
        ANTS_TAC THENL [ASM_MESON_TAC [OPEN_INTER, IN_INTER], ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:real^N->bool") THEN
        REWRITE_TAC [INJECTIVE_ON_LEFT_INVERSE] THEN
        REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"g:real^N->real^N") THEN
        DISCH_TAC THEN EXISTS_TAC (← q r"IMAGE (f:real^N->real^N) t") THEN
        EXISTS_TAC (← q r"(g':real^N->real^N->real^N) o (g:real^N->real^N)") THEN
        RULE_ASSUM_TAC (REWRITE_RULE [SUBSET]) THEN
        ASM_SIMP_TAC [FORALL_IN_IMAGE, o_THM, SUBSET, HOMEOMORPHISM] THEN
        ASM_SIMP_TAC [FUN_IN_IMAGE, ← GSYM CONJ_ASSOC] THEN
        MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
         [REWRITE_TAC [← GSYM SUBSET_INTERIOR_EQ] THEN
          REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
          X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
          MP_TAC (← ISPECL [← q r"f:real^N->real^N", ← q r"(f':real^N->real^N->real^N) x",
                            ← q r"(g':real^N->real^N->real^N) x", ← q r"s:real^N->bool",
                            ← q r"x:real^N"] SUSSMANN_OPEN_MAPPING) THEN
          ASM_SIMP_TAC [] THEN ANTS_TAC THENL
           [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
            ASM_SIMP_TAC [DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT] THEN
            ASM_MESON_TAC [differentiable],
            DISCH_THEN MATCH_MP_TAC THEN
            ASM_SIMP_TAC [SUBSET, INTERIOR_OPEN]],
          DISCH_TAC THEN
          MATCH_MP_TAC (← TAUT (← q r"(p /\ (r ==> q)) /\ r ==> p /\ q /\ r")) THEN
          CONJ_TAC THENL
           [REPEAT STRIP_TAC,
            X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
            MATCH_MP_TAC HAS_DERIVATIVE_INVERSE_STRONG THEN
            MAP_EVERY EXISTS_TAC
             [← q r"(f':real^N->real^N->real^N) x", ← q r"t:real^N->bool"] THEN
            ASM_SIMP_TAC []] THEN
          MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
          ASM_SIMP_TAC [DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT] THEN
          REWRITE_TAC [FORALL_IN_IMAGE] THEN ASM_MESON_TAC [differentiable]]] THEN
      SUBGOAL_THEN (← q r"(f:real^N->real^N) continuous_on s") ASSUME_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
        ASM_SIMP_TAC [DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT] THEN
        ASM_MESON_TAC [differentiable],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!u v. bounded u /\ open u /\ closure u SUBSET s /\ open v /\ connected v /\
              ~(v INTER IMAGE f u = {}) /\ v INTER IMAGE f (frontier u) = {}
              ==> v SUBSET IMAGE (f:real^N->real^N) u")
      (LABEL_TAC "L3") THENL
       [REPEAT STRIP_TAC THEN
        MATCH_MP_TAC (← TAUT (← q r"(~p ==> F) ==> p")) THEN DISCH_TAC THEN
        MP_TAC (← ISPECL [← q r"v:real^N->bool", ← q r"IMAGE (f:real^N->real^N) u"]
            CONNECTED_INTER_FRONTIER) THEN
        ASM_REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
         (← q r"v INTER s = {} ==> t SUBSET s ==> v INTER t = {}"))) THEN
        MATCH_MP_TAC FRONTIER_OPEN_MAP_IMAGE_SUBSET THEN ASM_REWRITE_TAC [] THEN
        CONJ_TAC THENL [ASM_MESON_TAC [CONTINUOUS_ON_SUBSET], ALL_TAC] THEN
        ASM_SIMP_TAC [INTERIOR_OPEN] THEN
        MATCH_MP_TAC DIFFERENTIABLE_IMP_OPEN_MAP THEN
        ASM_MESON_TAC [SUBSET, CLOSURE_SUBSET],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!e a b. &0 < e /\ a IN s /\ norm((f:real^N->real^N) a - b) <= e
                ==> ?h l t0 c. a IN closure c /\
                               (g':real^N->real^N->real^N) a (f a - b) = h /\
                               c IN components {x | x IN s /\ f x IN ball(b,e)} /\
                               &0 < l /\ &0 < t0 /\
                               !u t. norm(u - h) <= l /\ &0 < t /\ t < t0
                                     ==> (a - t % u) IN c")
      (LABEL_TAC "L7") THENL
       [X_GEN_TAC (← q r"e0:real") THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC (← MESON []
         (← q r"(!a b c d. Q a b c d ==> P a b c d) /\
          (?a b c d. Q a b c d)
          ==> ?a b c d. P a b c d /\ Q a b c d")) THEN
        CONJ_TAC THENL
         [MAP_EVERY X_GEN_TAC
           [← q r"h:real^N", ← q r"l:real", ← q r"t0:real", ← q r"c:real^N->bool"] THEN
          STRIP_TAC THEN
          REWRITE_TAC [CLOSURE_APPROACHABLE] THEN X_GEN_TAC (← q r"t:real") THEN
          DISCH_TAC THEN
          EXISTS_TAC (← q r"a - (min (t0 / &2) (t / (norm h + &1))) % h:real^N") THEN
          CONJ_TAC THENL
           [FIRST_X_ASSUM MATCH_MP_TAC THEN
            ASM_SIMP_TAC [VECTOR_SUB_REFL, NORM_0, REAL_LT_IMP_LE] THEN
            ASM_REWRITE_TAC [REAL_LT_MIN, REAL_HALF, REAL_MIN_LT] THEN
            ASM_SIMP_TAC [REAL_LT_DIV, ← NORM_ARITH (← q r"&0 < norm(h:real^N) + &1")] THEN
            ASM_REAL_ARITH_TAC,
            REWRITE_TAC [← NORM_ARITH (← q r"dist(a - x:real^N,a) = norm x")] THEN
            ASM_SIMP_TAC [NORM_MUL, ← REAL_ARITH (← q r"&0 < x ==> abs x = x"),
                          REAL_LT_MIN, REAL_HALF, REAL_LT_DIV,
                          ← NORM_ARITH (← q r"&0 < norm(h:real^N) + &1")] THEN
            TRANS_TAC REAL_LET_TRANS (← q r"(t / (norm h + &1)) * norm(h:real^N)") THEN
            ASM_SIMP_TAC [REAL_LE_RMUL, NORM_POS_LE,
                          ← REAL_ARITH (← q r"min a b <= b")] THEN
            ASM_SIMP_TAC [REAL_LT_LDIV_EQ, ← NORM_ARITH (← q r"&0 < norm(h:real^N) + &1"),
                          ← REAL_ARITH (← q r"x / y * z < t <=> (x * z) / y < t")] THEN
            ASM_SIMP_TAC [REAL_LT_LMUL_EQ] THEN REAL_ARITH_TAC],
          ALL_TAC] THEN
        ASM_CASES_TAC (← q r"(f:real^N->real^N) a = b") THENL
         [ABBREV_TAC
           (← q r"c = connected_component
                  {x | x IN s /\ (f:real^N->real^N) x IN ball(b,e0)} a") THEN
          SUBGOAL_THEN
           (← q r"open {z | z IN UNIV /\
                      (a - drop(fstcart z) % sndcart z:real^N) IN c}")
          MP_TAC THENL
           [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
            SIMP_TAC [CONTINUOUS_ON_SUB, CONTINUOUS_ON_CONST, CONTINUOUS_ON_MUL,
                      o_DEF, LIFT_DROP, LINEAR_CONTINUOUS_ON, OPEN_UNIV,
                      LINEAR_FSTCART, LINEAR_SNDCART, ETA_AX] THEN
            EXPAND_TAC "c" THEN MATCH_MP_TAC OPEN_CONNECTED_COMPONENT THEN
            MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
            ASM_REWRITE_TAC [OPEN_BALL],
            REWRITE_TAC [open_def, FORALL_PASTECART, IN_ELIM_THM, IN_UNIV] THEN
            REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART]] THEN
          DISCH_THEN (MP_TAC o SPECL [← q r"vec 0:real^1", ← q r"vec 0:real^N"]) THEN
          REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_SUB_RZERO] THEN ANTS_TAC THENL
           [REWRITE_TAC [IN] THEN EXPAND_TAC "c" THEN
            MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
            ASM_REWRITE_TAC [IN_ELIM_THM, CENTRE_IN_BALL],
            REWRITE_TAC [PASTECART_VEC, DIST_0, FORALL_LIFT, LIFT_DROP]] THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC) THEN
          MAP_EVERY EXISTS_TAC
           [← q r"vec 0:real^N", ← q r"d / &2", ← q r"d / &2", ← q r"c:real^N->bool"] THEN
          ASM_REWRITE_TAC [REAL_HALF] THEN REPEAT CONJ_TAC THENL
           [ASM_SIMP_TAC [VECTOR_SUB_REFL] THEN ASM_MESON_TAC [LINEAR_0],
            EXPAND_TAC "c" THEN REWRITE_TAC [CONNECTED_COMPONENT_IN_COMPONENTS] THEN
            ASM_REWRITE_TAC [IN_ELIM_THM, CENTRE_IN_BALL],
            MAP_EVERY X_GEN_TAC [← q r"z:real^N", ← q r"t:real"] THEN
            REWRITE_TAC [VECTOR_SUB_RZERO] THEN STRIP_TAC THEN
            FIRST_X_ASSUM MATCH_MP_TAC THEN
            W (MP_TAC o PART_MATCH lhand NORM_PASTECART_LE o lhand o snd) THEN
            MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LET_TRANS) THEN
            REWRITE_TAC [NORM_LIFT] THEN ASM_REAL_ARITH_TAC],
          ALL_TAC] THEN
        ABBREV_TAC (← q r"e = norm((f:real^N->real^N) a - b)") THEN
        SUBGOAL_THEN
         (← q r"?h l t0 c. c IN components
                           {x | x IN s /\ (f:real^N->real^N) x IN ball(b,e)} /\
                     (g':real^N->real^N->real^N) a (f a - b) = h /\
                     &0 < l /\ &0 < t0 /\
                     !u t. norm(u - h) <= l /\ &0 < t /\ t < t0
                           ==> (a - t % u) IN c")
        MP_TAC THENL
         [ALL_TAC,
          REPLICATE_TAC 3 (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"c:real^N->bool") STRIP_ASSUME_TAC) THEN
          MP_TAC (← ISPECL [← q r"{x | x IN s /\ (f:real^N->real^N) x IN ball(b,e0)}",
                            ← q r"c:real^N->bool"] EXISTS_COMPONENT_SUPERSET) THEN
          ANTS_TAC THENL
           [REWRITE_TAC [CONJ_ASSOC] THEN
            CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [IN_COMPONENTS_CONNECTED]] THEN
            MATCH_MP_TAC (← SET_RULE
             (← q r"~(c = {}) /\ c SUBSET s ==> c SUBSET s /\ ~(s = {})")) THEN
            CONJ_TAC THENL [ASM_MESON_TAC [IN_COMPONENTS_NONEMPTY], ALL_TAC] THEN
            FIRST_X_ASSUM (MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
            MP_TAC (← ISPECL [← q r"b:real^N", ← q r"e:real", ← q r"e0:real"] SUBSET_BALL) THEN
            ASM SET_TAC [],
            MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC []]] THEN
        SUBGOAL_THEN (← q r"&0 < e") ASSUME_TAC THENL
         [EXPAND_TAC "e" THEN REWRITE_TAC [NORM_POS_LT, VECTOR_SUB_EQ] THEN
          ASM_REWRITE_TAC [],
          ALL_TAC] THEN
        ABBREV_TAC (← q r"h = (g':real^N->real^N->real^N) a (f a - b)") THEN
        SUBGOAL_THEN (← q r"(f':real^N->real^N->real^N) a h = f a - b") ASSUME_TAC THENL
         [EXPAND_TAC "h" THEN
          RULE_ASSUM_TAC (REWRITE_RULE [o_THM, I_THM, FUN_EQ_THM]) THEN
          ASM SET_TAC [],
          UNDISCH_THEN (← q r"(g':real^N->real^N->real^N) a (f a - b) = h")
           (K ALL_TAC) THEN
          EXISTS_TAC (← q r"h:real^N") THEN ASM_REWRITE_TAC []] THEN
        ABBREV_TAC (← q r"p = \z. lift(norm((f:real^N->real^N) z - b) pow 2)") THEN
        ABBREV_TAC
         (← q r"p' = \z h. &2 % lift((f z - b) dot (f':real^N->real^N->real^N) z h)") THEN
        SUBGOAL_THEN
         (← q r"!z. z IN s ==> ((p:real^N->real^1) has_derivative p'(z)) (at z)")
        ASSUME_TAC THENL
         [REPEAT STRIP_TAC THEN EXPAND_TAC "p'" THEN REWRITE_TAC [] THEN
          MP_TAC (← ISPECL
           [← q r"\x. (f:real^N->real^N) x - b", ← q r"\x:real^N. lift (norm x pow 2)",
            ← q r"\h. (f':real^N->real^N->real^N) z h - vec 0",
            ← q r"\x:real^N. &2 % lift((f(z:real^N) - b) dot x)",
            ← q r"z:real^N"] DIFF_CHAIN_AT) THEN
          ASM_REWRITE_TAC [o_DEF, HAS_DERIVATIVE_SQNORM_AT] THEN
          ANTS_TAC THENL [ALL_TAC, REWRITE_TAC [VECTOR_SUB_RZERO]] THEN
          MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
          ASM_SIMP_TAC [HAS_DERIVATIVE_CONST, ETA_AX],
          ALL_TAC] THEN
        SUBGOAL_THEN
         (← q r"open {z | z IN UNIV /\
                    (a - drop(fstcart z) % (h + sndcart z):real^N) IN s}")
        MP_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
          ASM_REWRITE_TAC [OPEN_UNIV] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
          ASM_SIMP_TAC [CONTINUOUS_ON_CONST, CONTINUOUS_ON_MUL,
                        o_DEF, LIFT_DROP, LINEAR_CONTINUOUS_ON, OPEN_UNIV,
                        CONTINUOUS_ON_ADD, LINEAR_FSTCART, LINEAR_SNDCART, ETA_AX],
          REWRITE_TAC [open_def, FORALL_PASTECART, IN_ELIM_THM, IN_UNIV] THEN
          REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART]] THEN
        DISCH_THEN (MP_TAC o SPECL [← q r"vec 0:real^1", ← q r"vec 0:real^N"]) THEN
        ASM_REWRITE_TAC [VECTOR_MUL_LZERO, VECTOR_SUB_RZERO, DROP_VEC] THEN
        REWRITE_TAC [PASTECART_VEC, DIST_0, FORALL_LIFT, LIFT_DROP] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"m:real") STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN
         (← q r"?l. &0 < l /\
              !h'. norm(h' - h) <= l
                   ==> e pow 2 <= drop((p':real^N->real^N->real^1) a h')")
        MP_TAC THENL
         [SUBGOAL_THEN (← q r"(p':real^N->real^N->real^1) a continuous_on UNIV")
          MP_TAC THENL
           [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
            ASM_MESON_TAC [has_derivative],
            ASM_SIMP_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_AT, OPEN_UNIV, IN_UNIV]] THEN
          DISCH_THEN (MP_TAC o SPEC (← q r"h:real^N")) THEN
          REWRITE_TAC [continuous_at] THEN
          DISCH_THEN (MP_TAC o SPEC (← q r"(e:real) pow 2")) THEN
          ASM_SIMP_TAC [REAL_POW_LT] THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"d:real")
           (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*"))) THEN
          EXISTS_TAC (← q r"d / &2") THEN ASM_REWRITE_TAC [REAL_HALF] THEN
          X_GEN_TAC (← q r"h':real^N") THEN DISCH_TAC THEN
          REMOVE_THEN "*" (MP_TAC o SPEC (← q r"h':real^N")) THEN
          REWRITE_TAC [dist] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
          REWRITE_TAC [NORM_1, DROP_SUB] THEN MATCH_MP_TAC (← REAL_ARITH
           (← q r"h = &2 * e ==> abs(h' - h) < e ==> e <= h'")) THEN
          EXPAND_TAC "p'" THEN REWRITE_TAC [DROP_CMUL] THEN
          ASM_REWRITE_TAC [← GSYM NORM_POW_2, LIFT_DROP],
          DISCH_THEN (X_CHOOSE_THEN (← q r"l:real") STRIP_ASSUME_TAC) THEN
          EXISTS_TAC (← q r"min l (m / &2)") THEN
          ASM_REWRITE_TAC [REAL_LT_MIN, REAL_HALF]] THEN
        SUBGOAL_THEN (← q r"((p:real^N->real^1) has_derivative p' a) (at a)") MP_TAC THENL
         [ASM_SIMP_TAC [], ALL_TAC] THEN
        REWRITE_TAC [HAS_DERIVATIVE_AT_ALT] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"e pow 2 / &2 / (norm(h:real^N) + l)")) THEN
        ASM_SIMP_TAC [REAL_LT_DIV, REAL_POW_LT, REAL_HALF,
                      ← NORM_ARITH (← q r"&0 < l ==> &0 < norm(h:real^N) + l")] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"d:real")
         (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*"))) THEN
        EXISTS_TAC (← q r"min (d / (norm(h:real^N) + l)) (m / &2)") THEN
        ASM_SIMP_TAC [REAL_LT_DIV, REAL_LT_MIN, REAL_HALF, ← NORM_ARITH
         (← q r"&0 < l ==> &0 < norm(h:real^N) + l")] THEN
        REWRITE_TAC [← SET_RULE
         (← q r"(!u t. P u t ==> f t u IN c) <=> {f t u | P u t} SUBSET c")] THEN
        MATCH_MP_TAC EXISTS_COMPONENT_SUPERSET THEN
        REWRITE_TAC [← GSYM REAL_LT_MIN] THEN
        SUBGOAL_THEN
         (← q r"!x y. {a - t % u:real^N | norm(u - h) <= x /\ &0 < t /\ t < y} =
          IMAGE (\z. a - drop(fstcart z) % sndcart z)
                (interval(vec 0,lift y) PCROSS cball(h,x))")
         (fun th => REWRITE_TAC [th])
        THENL
         [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN
          REWRITE_TAC [EXISTS_PASTECART, PASTECART_IN_PCROSS] THEN
          REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART] THEN
          REWRITE_TAC [EXISTS_LIFT, IN_INTERVAL_1, IN_CBALL, LIFT_DROP] THEN
          REWRITE_TAC [DROP_VEC, ← ONCE_REWRITE_RULE [DIST_SYM] dist] THEN
          MESON_TAC [],
          ALL_TAC] THEN
        MATCH_MP_TAC (← TAUT (← q r"r /\ p /\ q ==> p /\ q /\ r")) THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
          SIMP_TAC [CONNECTED_PCROSS_EQ, CONNECTED_INTERVAL, CONNECTED_CBALL] THEN
          SIMP_TAC [CONTINUOUS_ON_SUB, CONTINUOUS_ON_CONST, CONTINUOUS_ON_MUL,
                    o_DEF, LIFT_DROP, LINEAR_CONTINUOUS_ON, OPEN_UNIV,
                    LINEAR_FSTCART, LINEAR_SNDCART, ETA_AX],
          ALL_TAC] THEN
        MATCH_MP_TAC (← SET_RULE
         (← q r"~(s = {}) /\ s SUBSET t ==> s SUBSET t /\ ~(t = {})")) THEN
        REWRITE_TAC [IMAGE_EQ_EMPTY, PCROSS_EQ_EMPTY, CBALL_EQ_EMPTY,
                     INTERVAL_EQ_EMPTY_1] THEN
        REWRITE_TAC [DE_MORGAN_THM, DROP_VEC, REAL_NOT_LT, REAL_NOT_LE,
                     REAL_LE_MIN] THEN
        ASM_SIMP_TAC [REAL_LT_IMP_LE, LIFT_DROP, REAL_HALF, REAL_LT_MIN] THEN
        ASM_SIMP_TAC [REAL_LT_DIV, ← NORM_ARITH
          (← q r"&0 < l ==> &0 < norm(h:real^N) + l")] THEN
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_PASTECART] THEN
        REWRITE_TAC [PASTECART_IN_PCROSS, FSTCART_PASTECART, SNDCART_PASTECART] THEN
        REWRITE_TAC [FORALL_LIFT, IN_INTERVAL_1, LIFT_DROP, DROP_VEC, IN_CBALL] THEN
        MAP_EVERY X_GEN_TAC [← q r"t:real", ← q r"u:real^N"] THEN
        REWRITE_TAC [dist, IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
         [SUBST1_TAC (← VECTOR_ARITH (← q r"u:real^N = h + (u - h)")) THEN
            FIRST_X_ASSUM MATCH_MP_TAC THEN
          W (MP_TAC o PART_MATCH lhand NORM_PASTECART_LE o lhand o snd) THEN
          MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LET_TRANS) THEN
          REWRITE_TAC [NORM_LIFT] THEN ONCE_REWRITE_TAC [NORM_SUB] THEN
          ASM_REAL_ARITH_TAC,
          REWRITE_TAC [IN_BALL]] THEN
        ASM_REWRITE_TAC [dist, NORM_LT_SQUARE, ← GSYM NORM_POW_2] THEN
        TRANS_TAC REAL_LET_TRANS (← q r"drop(p(a - t % u:real^N))") THEN CONJ_TAC THENL
         [EXPAND_TAC "p" THEN REWRITE_TAC [LIFT_DROP, NORM_SUB, REAL_LE_REFL],
          ALL_TAC] THEN
        REMOVE_THEN "*" (MP_TAC o SPEC (← q r"a - t % u:real^N")) THEN
        REWRITE_TAC [← VECTOR_ARITH (← q r"a - t - a:real^N = --t"), NORM_NEG] THEN
        ANTS_TAC THENL
         [TRANS_TAC REAL_LET_TRANS (← q r"t * (norm(h:real^N) + l)") THEN CONJ_TAC THENL
           [ASM_SIMP_TAC [NORM_MUL, REAL_LE_LMUL_EQ,
               ← REAL_ARITH (← q r"&0 < x ==> abs x = x")] THEN
            MATCH_MP_TAC (← NORM_ARITH
             (← q r"norm(y - x:real^N) <= l ==> norm(x) <= norm(y) + l")) THEN
            ASM_REAL_ARITH_TAC,
            ASM_SIMP_TAC [← GSYM REAL_LT_RDIV_EQ, ← NORM_ARITH
                          (← q r"&0 < l ==> &0 < norm(h:real^N) + l")] THEN
            ASM_REAL_ARITH_TAC],
          REWRITE_TAC [NORM_1, DROP_SUB]] THEN
        ASM_SIMP_TAC [LINEAR_NEG, DROP_NEG] THEN MATCH_MP_TAC (← REAL_ARITH
         (← q r"p + x < y + d ==> abs(q - p - --d) <= x ==> q < y")) THEN
        EXPAND_TAC "p" THEN REWRITE_TAC [LIFT_DROP] THEN
        ASM_REWRITE_TAC [REAL_LT_LADD] THEN
        ASM_SIMP_TAC [LINEAR_CMUL, NORM_MUL, DROP_CMUL] THEN
        ASM_SIMP_TAC [REAL_LT_LMUL_EQ, ← REAL_ARITH
         (← q r"&0 < t ==> (a * abs t * u < x <=> t * a * u < x)")] THEN
        TRANS_TAC REAL_LTE_TRANS (← q r"(e:real) pow 2") THEN CONJ_TAC THENL
         [REWRITE_TAC [← REAL_ARITH (← q r"a / &2 / b * x < a <=> a * x / b < a * &2")] THEN
          ASM_SIMP_TAC [REAL_LT_LMUL_EQ, REAL_POW_LT, REAL_LT_LDIV_EQ,
                        ← NORM_ARITH (← q r"&0 < l ==> &0 < norm(h:real^N) + l")] THEN
          UNDISCH_TAC (← q r"norm(h - u:real^N) <= min l (m / &2)") THEN
          UNDISCH_TAC (← q r"&0 < l") THEN CONV_TAC (fun t => NORM_ARITH t),
          FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC [NORM_SUB] THEN
          ASM_REAL_ARITH_TAC],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!x. x IN s
            ==> ?r d. &0 < r /\ &0 < d /\
                      cball(x,r) SUBSET s /\
                      !y. y IN cball(x,r)
                          ==> d * norm(y - x) <= norm(f y - (f:real^N->real^N) x)")
      (LABEL_TAC "L2") THENL
       [X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
        SUBGOAL_THEN (← q r"((f:real^N->real^N) has_derivative f'(x)) (at x)")
        MP_TAC THENL [ASM_SIMP_TAC [], REWRITE_TAC [HAS_DERIVATIVE_AT_ALT]] THEN
        STRIP_TAC THEN
        MP_TAC (← ISPEC (← q r"(g':real^N->real^N->real^N) x") LINEAR_BOUNDED_POS) THEN
        ASM_SIMP_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"B:real") THEN
        STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"&1 / (&2 * B)")) THEN
        ASM_SIMP_TAC [REAL_LT_MUL, REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"e0:real") STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"x:real^N")) THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"e1:real") STRIP_ASSUME_TAC) THEN
        MAP_EVERY EXISTS_TAC [← q r"min (e0 / &2) e1:real", ← q r"&1 / (&4 * B)"] THEN
        ASM_SIMP_TAC [REAL_LT_MIN, REAL_LT_DIV, ← REAL_ARITH (← q r"&0 < &2 /\ &0 < &4"),
                      REAL_LT_MUL, REAL_LT_01, CBALL_MIN_INTER, IN_INTER] THEN
        CONJ_TAC THENL [ASM SET_TAC [], X_GEN_TAC (← q r"y:real^N")] THEN
        REWRITE_TAC [IN_CBALL, dist] THEN STRIP_TAC THEN
        FIRST_ASSUM (MP_TAC o MATCH_MP (← NORM_ARITH
         (← q r"norm(x - y:real^N) <= e / &2 ==> &0 < e ==> norm(y - x) < e"))) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th =>
          FIRST_X_ASSUM (MP_TAC o C MATCH_MP th)) THEN
        MATCH_MP_TAC (← NORM_ARITH
         (← q r"a + d <= norm f'
          ==> norm(fy - fx - f') <= d ==> a <= norm(fy - fx:real^N)")) THEN
        MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC (← q r"B:real") THEN
        ASM_REWRITE_TAC [] THEN
        FIRST_X_ASSUM (fun th => W (MP_TAC o PART_MATCH rand th o rand o snd)) THEN
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] REAL_LE_TRANS) THEN
        RULE_ASSUM_TAC (REWRITE_RULE [FUN_EQ_THM, o_THM, I_THM]) THEN
        ASM_SIMP_TAC [← REAL_FIELD
         (← q r"&0 < B
          ==> B * (&1 / (&4 * B) * x + &1 / (&2 * B) * x) = &3 / &4 * x")] THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [NORM_POS_LE] THEN
        REAL_ARITH_TAC,
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!x e. &0 < e /\ x IN s
              ==> ?d. &0 < d /\
                       !b. ~((f:real^N->real^N) x = b)
                           ==> ball(x,d) INTER {z | z IN s /\ f z = b} SUBSET
                               ball(x + (g':real^N->real^N->real^N)(x) (b - f x),
                                    e * norm(b - f x))")
      (LABEL_TAC "L5") THENL
       [REPEAT STRIP_TAC THEN REMOVE_THEN "L2" (MP_TAC o SPEC (← q r"x:real^N")) THEN
        ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [← q r"p:real", ← q r"d:real"] THEN STRIP_TAC THEN
        SUBGOAL_THEN (← q r"linear((g':real^N->real^N->real^N) x)") MP_TAC THENL
         [ASM_MESON_TAC [], DISCH_THEN (MP_TAC o MATCH_MP LINEAR_BOUNDED_POS)] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"B:real") STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN (← q r"(f has_derivative (f':real^N->real^N->real^N) x) (at x)")
        MP_TAC THENL [ASM_MESON_TAC [], REWRITE_TAC [HAS_DERIVATIVE_AT_ALT]] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
         (MP_TAC o SPEC (← q r"d * e / &2 / B:real"))) THEN
        ASM_SIMP_TAC [REAL_LT_MUL, REAL_LT_DIV, REAL_HALF] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"r1:real")
         (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*"))) THEN
        EXISTS_TAC (← q r"min p (min r1 (d * r1)):real") THEN
        ASM_SIMP_TAC [REAL_LT_MUL, REAL_LT_MIN] THEN X_GEN_TAC (← q r"b:real^N") THEN
        DISCH_TAC THEN
        REWRITE_TAC [SUBSET, IN_INTER, IN_BALL, IN_ELIM_THM, REAL_LT_MIN] THEN
        X_GEN_TAC (← q r"z:real^N") THEN REWRITE_TAC [dist] THEN STRIP_TAC THEN
        TRANS_TAC REAL_LET_TRANS
         (← q r"norm((g':real^N->real^N->real^N) x (b - f x - f' x (z - x)))") THEN
        CONJ_TAC THENL
         [RULE_ASSUM_TAC (REWRITE_RULE [FUN_EQ_THM, o_THM, I_THM]) THEN
          MATCH_MP_TAC REAL_EQ_IMP_LE THEN ASM_SIMP_TAC [LINEAR_SUB] THEN
          AP_TERM_TAC THEN CONV_TAC (fun t => VECTOR_ARITH t),
          REMOVE_THEN "*" (MP_TAC o SPEC (← q r"z:real^N"))] THEN
        ANTS_TAC THENL [ASM_MESON_TAC [NORM_SUB], ASM_REWRITE_TAC []] THEN
        ABBREV_TAC (← q r"eta = b - (f:real^N->real^N) x - f' x (z - x)") THEN
        DISCH_TAC THEN TRANS_TAC REAL_LET_TRANS (← q r"B * norm(eta:real^N)") THEN
        ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
        MATCH_MP_TAC (← REAL_ARITH (← q r"&0 < x * e /\ y <= x * e / &2 ==> y < x * e")) THEN
        ASM_SIMP_TAC [REAL_LT_MUL, NORM_POS_LT, VECTOR_SUB_EQ] THEN
        ASM_SIMP_TAC [← GSYM REAL_LE_RDIV_EQ] THEN FIRST_X_ASSUM (MATCH_MP_TAC o
         MATCH_MP (← REAL_ARITH
          (← q r"s <= (d * e / &2 / B) * n
           ==> e / &2 / B * d * n <= e / &2 / B * n'
               ==> s <= (n' * e / &2) / B"))) THEN
        ASM_SIMP_TAC [real_div, ← GSYM REAL_MUL_ASSOC, REAL_LE_LMUL_EQ,
                      REAL_LT_INV_EQ, ← REAL_ARITH (← q r"&0 < &2")] THEN
        EXPAND_TAC "b" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC [IN_CBALL, dist] THEN ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      USE_THEN "L2" (MP_TAC o SPEC (← q r"x:real^N")) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC [], REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN
      MAP_EVERY X_GEN_TAC [← q r"r:real", ← q r"d:real"] THEN STRIP_TAC THEN
      ABBREV_TAC (← q r"w = (f:real^N->real^N) x") THEN
      SUBGOAL_THEN
       (← q r"!z. norm(z - x) = r ==> d * r <= norm((f:real^N->real^N) z - w)")
      ASSUME_TAC THENL
       [X_GEN_TAC (← q r"z:real^N") THEN DISCH_TAC THEN
        FIRST_X_ASSUM (fun th =>
          W (MP_TAC o PART_MATCH (rand o rand) th o rand o snd)) THEN
        ASM_REWRITE_TAC [IN_CBALL, ← ONCE_REWRITE_RULE [DIST_SYM] dist] THEN
        ASM_REWRITE_TAC [REAL_LE_REFL],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"?r'. &0 < r' /\ r' < r /\
             IMAGE (f:real^N->real^N) (cball(x,r')) SUBSET ball(w,(d * r) / &3)")
      STRIP_ASSUME_TAC THENL
       [MP_TAC (← ISPEC (← q r"{y | y IN s /\ (f:real^N->real^N) y IN ball(w,(d * r) / &3)}")
          OPEN_CONTAINS_CBALL) THEN
        DISCH_THEN (MP_TAC o (fun th => do pure (← EQ_IMP_RULE th).1)) THEN ANTS_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
          ASM_REWRITE_TAC [OPEN_BALL],
          DISCH_THEN (MP_TAC o SPEC (← q r"x:real^N")) THEN
          ASM_REWRITE_TAC [IN_ELIM_THM, CENTRE_IN_BALL] THEN
          ASM_SIMP_TAC [REAL_LT_DIV, REAL_LT_MUL, ← REAL_ARITH (← q r"&0 < &3")] THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"r':real") STRIP_ASSUME_TAC) THEN
          EXISTS_TAC (← q r"min r' (r / &2)") THEN
          ASM_REWRITE_TAC [REAL_LT_MIN, REAL_HALF, CBALL_MIN_INTER] THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ASM SET_TAC []]],
        ALL_TAC] THEN
      EXISTS_TAC (← q r"ball(x:real^N,r')") THEN
      ASM_REWRITE_TAC [OPEN_BALL, CENTRE_IN_BALL] THEN
      MAP_EVERY X_GEN_TAC [← q r"z1:real^N", ← q r"z2:real^N"] THEN STRIP_TAC THEN
      ABBREV_TAC (← q r"b = (f:real^N->real^N) z2") THEN
      ASM_CASES_TAC (← q r"z1:real^N = z2") THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"cball(x:real^N,r') SUBSET s") ASSUME_TAC THENL
       [ASM_MESON_TAC [SUBSET_TRANS, SUBSET_CBALL, REAL_LT_IMP_LE], ALL_TAC] THEN
      ABBREV_TAC
       (← q r"e = inf { sup { norm((f:real^N->real^N) z - b) | z IN k} |
                  compact k /\ connected k /\
                  z1 IN k /\ z2 IN k /\ k SUBSET cball(x,r)}") THEN
      MP_TAC (← SPEC
       (← q r"{sup { norm((f:real^N->real^N) z - b) | z IN k} |
               compact k /\ connected k /\
               z1 IN k /\ z2 IN k /\ k SUBSET cball(x,r)}")
       INF) THEN
      ASM_REWRITE_TAC [FORALL_IN_GSPEC, NOT_IMP] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC [← SET_RULE (← q r"~({f x | P x} = {}) <=> ?x. P x")] THEN
        EXISTS_TAC (← q r"cball(x:real^N,r')") THEN
        REWRITE_TAC [SUBSET_REFL, COMPACT_CBALL, CONNECTED_CBALL] THEN
        ASM_MESON_TAC [BALL_SUBSET_CBALL, SUBSET_CBALL, REAL_LT_IMP_LE, SUBSET],
        EXISTS_TAC (← q r"&0") THEN X_GEN_TAC (← q r"k:real^N->bool") THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_LE_SUP THEN
        REWRITE_TAC [EXISTS_IN_GSPEC, FORALL_IN_GSPEC, NORM_POS_LE] THEN
        REWRITE_TAC [LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM] THEN
        CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        MP_TAC (← ISPECL [← q r"f:real^N->real^N", ← q r"k:real^N->bool"]
          COMPACT_CONTINUOUS_IMAGE) THEN
        ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
         [ASM_MESON_TAC [CONTINUOUS_ON_SUBSET],
          DISCH_THEN (MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
          REWRITE_TAC [bounded, FORALL_IN_IMAGE] THEN
          DISCH_THEN (X_CHOOSE_TAC (← q r"B:real")) THEN
          EXISTS_TAC (← q r"B + norm(b:real^N)") THEN ASM_SIMP_TAC [← NORM_ARITH
           (← q r"norm(x:real^N) <= B ==> norm(x - b) <= B + norm b")]],
        FIRST_X_ASSUM (fun th => if randIs et th
          then ALL_TAC else HolCore.Tactics.FAIL_TAC "check") THEN
        DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "I1") (LABEL_TAC "I2"))] THEN
      SUBGOAL_THEN
       (← q r"?k. compact k /\ connected k /\
            z1 IN k /\ z2 IN k /\ k SUBSET cball(x,r) /\
            sup { norm((f:real^N->real^N) z - b) | z IN k} = e")
      STRIP_ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [← MESON [] (← q r"(?k. P k) <=> ~(!k. ~P k)")] THEN
        REWRITE_TAC [← TAUT (← q r"~(p /\ q) <=> p ==> ~q")] THEN
        REWRITE_TAC [IMP_IMP, ← GSYM CONJ_ASSOC] THEN
        ASM_SIMP_TAC [← GSYM REAL_LE_ANTISYM, REAL_NOT_LE] THEN
        REMOVE_THEN "I2" (MP_TAC o GEN (← q r"n:num") o SPEC (← q r"e + inv(&n + &1)")) THEN
        REWRITE_TAC [← REAL_ARITH (← q r"e + i <= e <=> ~(&0 < i)")] THEN
        REWRITE_TAC [REAL_LT_INV_EQ, ← REAL_ARITH (← q r"&0 < &n + &1")] THEN
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [NOT_FORALL_THM] THEN
        REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC (← q r"k:num->real^N->bool") THEN
        REWRITE_TAC [NOT_IMP, FORALL_AND_THM, REAL_NOT_LE] THEN
        STRIP_TAC THEN
        MP_TAC (← ISPECL [← q r"k:num->real^N->bool", ← q r"cball(x:real^N,r)"]
          COMPACT_HAUSDIST) THEN
        ASM_REWRITE_TAC [COMPACT_CBALL] THEN
        ANTS_TAC THENL [ASM SET_TAC [], REWRITE_TAC [NOT_FORALL_THM]] THEN
        GEN_REWRITE_TAC LAND_CONV [SWAP_EXISTS_THM] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"c:real^N->bool") THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"q:num->num") STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC [NOT_IMP, ← GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONNECTED_HAUSDIST_LIMIT THEN
          EXISTS_TAC (← q r"(k:num->real^N->bool) o (q:num->num)") THEN
          ASM_SIMP_TAC [o_THM, COMPACT_IMP_BOUNDED] THEN ASM SET_TAC [],
          ALL_TAC] THEN
        REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL
         [REWRITE_TAC [← SET_RULE (← q r"a IN s /\ b IN s <=> {a,b} SUBSET s")] THEN
          MATCH_MP_TAC SUBSET_COMPACT_HAUSDIST_LIMIT THEN
          EXISTS_TAC (← q r"(k:num->real^N->bool) o (q:num->num)") THEN
          ASM_SIMP_TAC [o_THM, COMPACT_IMP_BOUNDED] THEN ASM SET_TAC [],
          REWRITE_TAC [← REAL_ARITH (← q r"~(x < y) <=> y - x <= &0")] THEN
          ONCE_REWRITE_TAC [REAL_LE_TRANS_LTE] THEN
          X_GEN_TAC (← q r"a:real") THEN DISCH_TAC THEN REWRITE_TAC [REAL_LE_SUB_RADD] THEN
          SUBGOAL_THEN
           (← q r"(f:real^N->real^N) uniformly_continuous_on cball (x,r)")
          MP_TAC THENL
           [MATCH_MP_TAC COMPACT_UNIFORMLY_CONTINUOUS THEN
            REWRITE_TAC [COMPACT_CBALL] THEN ASM_MESON_TAC [CONTINUOUS_ON_SUBSET],
            REWRITE_TAC [HAUSDIST_UNIFORMLY_CONTINUOUS_ON]] THEN
          DISCH_THEN (MP_TAC o SPEC (← q r"a / &2")) THEN ASM_REWRITE_TAC [REAL_HALF] THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"de:real") STRIP_ASSUME_TAC) THEN
          SUBGOAL_THEN
           (← q r"eventually
             (\n. inv(&n + &1) < a / &2 /\
                  dist(lift(hausdist ((k:num->real^N->bool) (q n),c)),vec 0) < de)
             sequentially")
          MP_TAC THENL
           [ASM_REWRITE_TAC [EVENTUALLY_AND, ARCH_EVENTUALLY_INV1, REAL_HALF] THEN
            UNDISCH_TAC (← q r"&0 < de") THEN
            SPEC_TAC ((← q r"de:real"), (← q r"e:real")) THEN
            ASM_REWRITE_TAC [← GSYM tendsto],
            REWRITE_TAC [EVENTUALLY_SEQUENTIALLY, LEFT_IMP_EXISTS_THM]] THEN
          X_GEN_TAC (← q r"n:num") THEN DISCH_THEN (MP_TAC o SPEC (← q r"n:num")) THEN
          REWRITE_TAC [DIST_0, NORM_LIFT, REAL_ABS_HAUSDIST, LE_REFL] THEN
          STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPECL
           [← q r"c:real^N->bool", ← q r"(k:num->real^N->bool)(q(n:num))"]) THEN
          ASM_SIMP_TAC [COMPACT_IMP_BOUNDED] THEN
          SUBGOAL_THEN
           (← q r"sup {norm((f:real^N->real^N) z - b) | z IN k((q:num->num)n)}
            < e + a / &2")
          MP_TAC THENL
           [TRANS_TAC REAL_LTE_TRANS (← q r"e + inv(&(q(n:num)) + &1)") THEN
            ASM_REWRITE_TAC [REAL_LE_LADD] THEN FIRST_X_ASSUM (MATCH_MP_TAC o
              MATCH_MP (← REAL_ARITH (← q r"x < a ==> y <= x ==> y <= a"))) THEN
            MATCH_MP_TAC REAL_LE_INV2 THEN
            REWRITE_TAC [← REAL_ARITH (← q r"&0 < &n + &1"), REAL_LE_RADD] THEN
            ASM_MESON_TAC [MONOTONE_BIGGER, REAL_OF_NUM_LE],
            MATCH_MP_TAC (← REAL_ARITH
             (← q r"abs(x - y) <= h
              ==> x < e + a / &2 ==> h < a / &2 ==> y <= a + e"))] THEN
          ONCE_REWRITE_TAC [REAL_LE_TRANS_LTE] THEN X_GEN_TAC (← q r"h:real") THEN
          DISCH_TAC THEN REWRITE_TAC [← REAL_ARITH
           (← q r"abs(x - y) <= e <=> x <= y + e /\ y <= x + e")] THEN
          CONJ_TAC THEN MATCH_MP_TAC REAL_SUP_LE THEN
          (CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN
          REWRITE_TAC [FORALL_IN_GSPEC] THEN
          X_GEN_TAC (← q r"x1:real^N") THEN DISCH_TAC THEN
          REWRITE_TAC [← GSYM REAL_LE_SUB_RADD] THEN
          MATCH_MP_TAC REAL_LE_SUP THEN REWRITE_TAC [EXISTS_IN_GSPEC] THEN
          REWRITE_TAC [FORALL_IN_GSPEC] THEN
          REWRITE_TAC [CONJ_ASSOC, LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM] THEN
          ONCE_REWRITE_TAC [← SET_RULE
           (← q r"(!z. z IN c ==> norm(f z - b:real^N) <= B) <=>
            (!z. z IN IMAGE (\x. x - b) (IMAGE f c) ==> norm z <= B)")] THEN
          REWRITE_TAC [← GSYM bounded] THEN
          REWRITE_TAC [← VECTOR_ARITH (← q r"x - b:real^N = --b + x")] THEN
          REWRITE_TAC [BOUNDED_TRANSLATION_EQ] THEN
          (CONJ_TAC THENL
            [ONCE_REWRITE_TAC [← REAL_ARITH (← q r"x - y <= z <=> x - z <= y")],
             ASM_MESON_TAC [COMPACT_IMP_BOUNDED, COMPACT_CONTINUOUS_IMAGE,
                            CONTINUOUS_ON_SUBSET, SUBSET_TRANS]]) THEN
          MATCH_MP_TAC (← MESON [← NORM_ARITH
           (← q r"dist(x:real^N,y) < a ==> norm(b + x) - norm(b + y) <= a")]
           (← q r"(?z. z IN c /\ dist(x:real^N,f z) < a)
            ==> ?z. z IN c /\ norm(b + x) - norm(b + f z) <= a")) THEN
          ONCE_REWRITE_TAC [← SET_RULE
           (← q r"(?z. z IN c /\ dist(x:real^N,f z) < a) <=>
            (?z. z IN IMAGE f c /\ dist(x,z) < a)")] THEN
          MATCH_MP_TAC REAL_LT_HAUSDIST_POINT_EXISTS THENL
           [EXISTS_TAC (← q r"IMAGE (f:real^N->real^N) (k((q:num->num) n))"),
            EXISTS_TAC (← q r"IMAGE (f:real^N->real^N) c") THEN
            ONCE_REWRITE_TAC [HAUSDIST_SYM]] THEN
          ASM_SIMP_TAC [FUN_IN_IMAGE, IMAGE_EQ_EMPTY] THEN
          REPEAT CONJ_TAC THEN
          (MATCH_MP_TAC COMPACT_IMP_BOUNDED ORELSE ASM SET_TAC []) THEN
          MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
          ASM_MESON_TAC [CONTINUOUS_ON_SUBSET, SUBSET_TRANS]],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"~(k:real^N->bool = {})") ASSUME_TAC THENL
       [ASM SET_TAC [], ALL_TAC] THEN
      MP_TAC (← ISPEC (← q r"{norm((f:real^N->real^N) z - b) | z IN k}") SUP) THEN
      ASM_REWRITE_TAC [NOT_IMP, EXISTS_IN_GSPEC, FORALL_IN_GSPEC] THEN
      REPEAT CONJ_TAC THENL
       [ASM SET_TAC [],
        ONCE_REWRITE_TAC [← SET_RULE
         (← q r"(!z. z IN c ==> norm(f z - b:real^N) <= B) <=>
          (!z. z IN IMAGE (\x. x - b) (IMAGE f c) ==> norm z <= B)")] THEN
        REWRITE_TAC [← GSYM bounded] THEN
        REWRITE_TAC [← VECTOR_ARITH (← q r"x - b:real^N = --b + x")] THEN
        REWRITE_TAC [BOUNDED_TRANSLATION_EQ] THEN
        ASM_MESON_TAC [COMPACT_IMP_BOUNDED, COMPACT_CONTINUOUS_IMAGE,
                       CONTINUOUS_ON_SUBSET, SUBSET_TRANS],
        DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "S1") (LABEL_TAC "S2"))] THEN
      SUBGOAL_THEN (← q r"&0 < e") ASSUME_TAC THENL
       [SUBGOAL_THEN (← q r"~(IMAGE (f:real^N->real^N) k SUBSET {b})") MP_TAC THENL
         [DISCH_THEN (MP_TAC o MATCH_MP (← SET_RULE
           (← q r"IMAGE f k SUBSET {b} ==> k SUBSET {x | x IN k /\ f x = b}"))) THEN
          DISCH_THEN (MP_TAC o MATCH_MP
           (← REWRITE_RULE [IMP_CONJ_ALT] FINITE_SUBSET)) THEN
          REWRITE_TAC [NOT_IMP, ← GSYM INFINITE] THEN CONJ_TAC THENL
           [MATCH_MP_TAC DIFFERENTIABLE_FINITE_PREIMAGES THEN
            EXISTS_TAC (← q r"f':real^N->real^N->real^N") THEN
            ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
            REPEAT STRIP_TAC THEN
            MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN ASM SET_TAC [],
            ASM_SIMP_TAC [CONNECTED_INFINITE_IFF_CARD_EQ,
                          CONNECTED_CARD_EQ_IFF_NONTRIVIAL] THEN
            ASM SET_TAC []],
          REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
          REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, IN_SING] THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"z:real^N") STRIP_ASSUME_TAC) THEN
          TRANS_TAC REAL_LTE_TRANS (← q r"norm((f:real^N->real^N) z - b)") THEN
          ASM_SIMP_TAC [NORM_POS_LT, VECTOR_SUB_EQ]],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"e <= &2 / &3 * d * r") ASSUME_TAC THENL
       [REMOVE_THEN "I1" (MP_TAC o SPEC (← q r"cball(x:real^N,r')")) THEN
        ASM_SIMP_TAC [COMPACT_CBALL, CONNECTED_CBALL, SUBSET_CBALL,
                      REAL_LT_IMP_LE, ← REWRITE_RULE [SUBSET] BALL_SUBSET_CBALL] THEN
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
        MATCH_MP_TAC REAL_SUP_LE THEN
        ASM_REWRITE_TAC [← SET_RULE (← q r"{f x | x IN s} = {} <=> s = {}")] THEN
        ASM_SIMP_TAC [CBALL_EQ_EMPTY, ← REAL_ARITH (← q r"&0 < r ==> ~(r < &0)")] THEN
        REWRITE_TAC [FORALL_IN_GSPEC] THEN
        X_GEN_TAC (← q r"z:real^N") THEN DISCH_TAC THEN EXPAND_TAC "b" THEN
        MATCH_MP_TAC (← NORM_ARITH
         (← q r"!a. norm(a - x) < dr / &3 /\ norm(a - y) < dr / &3
              ==> norm(x - y:real^N) <= &2 / &3 * dr")) THEN
        EXISTS_TAC (← q r"w:real^N") THEN
        REWRITE_TAC [← GSYM dist, ← GSYM IN_BALL] THEN
        MP_TAC (← ISPECL [← q r"x:real^N", ← q r"r':real"] BALL_SUBSET_CBALL) THEN
        ASM SET_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!c. connected c /\ ~(c INTER ball(x,r) = {}) /\
            (!z. z IN c ==> norm((f:real^N->real^N) z - b) <= e)
            ==> c SUBSET ball(x,r)")
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN
        MP_TAC (← ISPECL [← q r"c:real^N->bool", ← q r"ball(x:real^N,r)"]
            CONNECTED_INTER_FRONTIER) THEN
        ASM_REWRITE_TAC [CONTRAPOS_THM] THEN
        ANTS_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
        ASM_SIMP_TAC [FRONTIER_BALL, EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
        REWRITE_TAC [IN_SPHERE, dist] THEN X_GEN_TAC (← q r"z:real^N") THEN
        ONCE_REWRITE_TAC [NORM_SUB] THEN STRIP_TAC THEN
        SUBGOAL_THEN (← q r"d * r <= norm((f:real^N->real^N) z - w)") MP_TAC THENL
         [ASM_MESON_TAC [], REWRITE_TAC [REAL_NOT_LE]] THEN
        MATCH_MP_TAC (← NORM_ARITH
         (← q r"!fz1. e <= &2 / &3 * dr /\ norm(fz - fz1) <= e /\
                dist(fx,fz1) < dr / &3
                ==> norm(fz - fx:real^N) < dr")) THEN
        EXISTS_TAC (← q r"(f:real^N->real^N) z1") THEN
        ASM_SIMP_TAC [← GSYM IN_BALL] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [SUBSET, FORALL_IN_IMAGE]) THEN
        SUBST1_TAC (← SYM (← ASSUME (← q r"(f:real^N->real^N) z1 = b"))) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC [← REWRITE_RULE [SUBSET] BALL_SUBSET_CBALL],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"k SUBSET ball(x:real^N,r)") ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN
        EXISTS_TAC (← q r"z1:real^N") THEN ASM_REWRITE_TAC [IN_INTER] THEN
        ASM_MESON_TAC [SUBSET, SUBSET_BALL, REAL_LT_IMP_LE],
        ALL_TAC] THEN
      ABBREV_TAC (← q r"U = {c | c IN components
                             {x | x IN s /\ (f:real^N->real^N) x IN ball(b,e)} /\
                           ~(c INTER ball(x,r) = {})}") THEN
      SUBGOAL_THEN (← q r"!u. u IN U ==> u SUBSET ball(x:real^N,r)") ASSUME_TAC THENL
       [EXPAND_TAC "U" THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC
        THENL [ASM_MESON_TAC [IN_COMPONENTS_CONNECTED], ALL_TAC] THEN
        FIRST_ASSUM (ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
        REWRITE_TAC [← GSYM (← ONCE_REWRITE_RULE [DIST_SYM] dist), ← GSYM IN_CBALL] THEN
        MATCH_MP_TAC (← REWRITE_RULE [SUBSET] BALL_SUBSET_CBALL) THEN ASM SET_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!u z. u IN U /\ z IN frontier u ==> (f:real^N->real^N) z IN sphere(b,e)")
      ASSUME_TAC THENL
       [EXPAND_TAC "U" THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        SUBGOAL_THEN (← q r"closure(u:real^N->bool) SUBSET s") ASSUME_TAC THENL
         [TRANS_TAC SUBSET_TRANS (← q r"closure(ball(x:real^N,r))") THEN
          CONJ_TAC THENL [ALL_TAC, ASM_SIMP_TAC [CLOSURE_BALL]] THEN
          MATCH_MP_TAC SUBSET_CLOSURE THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN  EXPAND_TAC "U" THEN
          REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [],
          ALL_TAC] THEN
        REWRITE_TAC [← GSYM CBALL_DIFF_BALL, IN_DIFF] THEN CONJ_TAC THENL
         [SUBGOAL_THEN (← q r"(z:real^N) IN closure u") MP_TAC THENL
           [RULE_ASSUM_TAC (REWRITE_RULE [frontier, IN_DIFF]) THEN ASM_REWRITE_TAC [],
            ALL_TAC] THEN
          MATCH_MP_TAC (← SET_RULE (← q r"IMAGE f s SUBSET t ==> z IN s ==> f z IN t")) THEN
          MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN
          REWRITE_TAC [CLOSED_CBALL] THEN CONJ_TAC THENL
           [ASM_MESON_TAC [CONTINUOUS_ON_SUBSET],
            FIRST_X_ASSUM (MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
            MP_TAC (← ISPECL [← q r"b:real^N", ← q r"e:real"] BALL_SUBSET_CBALL) THEN
            SET_TAC []],
          SUBGOAL_THEN (← q r"(z:real^N) IN s") ASSUME_TAC THENL
           [RULE_ASSUM_TAC (REWRITE_RULE [frontier]) THEN ASM SET_TAC [],
            ALL_TAC] THEN
          SUBGOAL_THEN (← q r"(z:real^N) IN closure u") MP_TAC THENL
           [RULE_ASSUM_TAC (REWRITE_RULE [frontier, IN_DIFF]) THEN ASM_REWRITE_TAC [],
            ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN REWRITE_TAC []] THEN
          REPEAT STRIP_TAC THEN UNDISCH_TAC (← q r"(z:real^N) IN frontier u") THEN
          REWRITE_TAC [frontier] THEN
          SUBGOAL_THEN
           (← q r"z IN UNIONS(components
               {x | x IN s /\ (f:real^N->real^N) x IN ball (b,e)})")
          MP_TAC THENL
           [REWRITE_TAC [← GSYM UNIONS_COMPONENTS] THEN ASM SET_TAC [],
            REWRITE_TAC [IN_UNIONS, LEFT_IMP_EXISTS_THM]] THEN
          X_GEN_TAC (← q r"u':real^N->bool") THEN STRIP_TAC THEN
          SUBGOAL_THEN (← q r"open(u:real^N->bool) /\ open(u':real^N->bool)")
          STRIP_ASSUME_TAC THENL
           [CONJ_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
             (← REWRITE_RULE [IMP_CONJ_ALT] OPEN_COMPONENTS)) THEN
            MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
            ASM_REWRITE_TAC [OPEN_BALL],
            ALL_TAC] THEN
          ASM_CASES_TAC (← q r"u:real^N->bool = u'") THEN
          ASM_SIMP_TAC [INTERIOR_OPEN, IN_DIFF] THEN
          MP_TAC (← ISPECL [← q r"u:real^N->bool", ← q r"u':real^N->bool"]
            SEPARATION_OPEN_IN_UNION) THEN
          ASM_SIMP_TAC [OPEN_IN_OPEN_EQ, OPEN_UNION, SUBSET_UNION] THEN
          DISCH_THEN (MP_TAC o (fun th => do pure (← EQ_IMP_RULE th).2)) THEN
          ANTS_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
          REWRITE_TAC [DISJOINT] THEN ASM_MESON_TAC [COMPONENTS_NONOVERLAP]],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!u. u IN U ==> ~(u INTER {x | x IN s /\ (f:real^N->real^N) x = b} = {})")
      ASSUME_TAC THENL
       [EXPAND_TAC "U" THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        FIRST_ASSUM (ASSUME_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
        FIRST_ASSUM (ASSUME_TAC o MATCH_MP IN_COMPONENTS_CONNECTED) THEN
        FIRST_ASSUM (ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
        SUBGOAL_THEN (← q r"u SUBSET ball(x:real^N,r)") ASSUME_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "U" THEN
          REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [],
          ALL_TAC] THEN
        SUBGOAL_THEN (← q r"closure(u:real^N->bool) SUBSET s") ASSUME_TAC THENL
         [TRANS_TAC SUBSET_TRANS (← q r"closure(ball(x:real^N,r))") THEN
          ASM_SIMP_TAC [SUBSET_CLOSURE] THEN ASM_SIMP_TAC [CLOSURE_BALL],
          ALL_TAC] THEN
        REMOVE_THEN "L3" (MP_TAC o SPECL
         [← q r"u:real^N->bool", ← q r"ball(b:real^N,e)"]) THEN
        ASM_REWRITE_TAC [OPEN_BALL, CONNECTED_BALL, NOT_IMP] THEN
        REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC [BOUNDED_SUBSET, BOUNDED_BALL],
          FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT]
            OPEN_COMPONENTS)) THEN
          MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
          ASM_REWRITE_TAC [OPEN_BALL],
          ASM SET_TAC [],
          REWRITE_TAC [← GSYM CBALL_DIFF_SPHERE] THEN MATCH_MP_TAC (← SET_RULE
           (← q r"(!x. x IN s ==> f x IN t) ==> (u DIFF t) INTER IMAGE f s = {}")) THEN
          REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          EXISTS_TAC (← q r"u:real^N->bool") THEN
          EXPAND_TAC "U" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [],
          REWRITE_TAC [SUBSET] THEN DISCH_THEN (MP_TAC o SPEC (← q r"b:real^N")) THEN
          ASM_REWRITE_TAC [CENTRE_IN_BALL] THEN ASM SET_TAC []],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"FINITE(U:(real^N->bool)->bool)") ASSUME_TAC THENL
       [SUBGOAL_THEN
         (← q r"FINITE {z | z IN cball(x,r) /\ (f:real^N->real^N) z = b}")
        MP_TAC THENL
         [MATCH_MP_TAC DIFFERENTIABLE_FINITE_PREIMAGES THEN
          EXISTS_TAC (← q r"f':real^N->real^N->real^N") THEN
          REWRITE_TAC [COMPACT_CBALL] THEN
          CONJ_TAC THENL [REPEAT STRIP_TAC, ASM SET_TAC []] THEN
          MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN ASM SET_TAC [],
          MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] CARD_LE_FINITE)] THEN
        MATCH_MP_TAC CARD_LE_RELATIONAL_FULL THEN
        EXISTS_TAC (← q r"(IN):real^N->(real^N->bool)->bool") THEN
        ASM_REWRITE_TAC [IN_ELIM_THM] THEN CONJ_TAC THENL
         [MP_TAC (← ISPECL [← q r"x:real^N", ← q r"r:real"] BALL_SUBSET_CBALL) THEN
          ASM SET_TAC [],
          REPEAT GEN_TAC THEN EXPAND_TAC "U" THEN REWRITE_TAC [IN_ELIM_THM] THEN
          DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
          DISCH_THEN (MP_TAC o MATCH_MP (← TAUT
           (← q r"(p /\ x) /\ (q /\ y) /\ r ==> (p /\ q) /\ r"))) THEN
          DISCH_THEN (CONJUNCTS_THEN2 (MP_TAC o MATCH_MP COMPONENTS_NONOVERLAP)
            MP_TAC) THEN SET_TAC []],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"k SUBSET UNIONS {closure u:real^N->bool | u IN U}")
      MP_TAC THENL
       [REWRITE_TAC [SUBSET, UNIONS_GSPEC, IN_ELIM_THM] THEN
        X_GEN_TAC (← q r"a:real^N") THEN DISCH_TAC THEN
        SUBGOAL_THEN (← q r"(a:real^N) IN s") ASSUME_TAC THENL
         [ASM SET_TAC [], ALL_TAC] THEN
        REMOVE_THEN "L7" (MP_TAC o SPECL [← q r"e:real", ← q r"a:real^N", ← q r"b:real^N"]) THEN
        ASM_SIMP_TAC [LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC
         [← q r"h:real^N", ← q r"l:real", ← q r"t0:real", ← q r"c:real^N->bool"] THEN
        STRIP_TAC THEN EXPAND_TAC "U" THEN REWRITE_TAC [EXISTS_IN_GSPEC] THEN
        EXISTS_TAC (← q r"c:real^N->bool") THEN ASM_REWRITE_TAC [] THEN
        ONCE_REWRITE_TAC [INTER_COMM] THEN
        MP_TAC (← ISPECL [← q r"ball(x:real^N,r)", ← q r"c:real^N->bool"]
          OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
        REWRITE_TAC [OPEN_BALL] THEN ASM SET_TAC [],
        ALL_TAC] THEN
      ASM_CASES_TAC (← q r"U:(real^N->bool)->bool = {}") THENL
       [ASM_REWRITE_TAC [← SET_RULE (← q r"{f x | x IN {}} = {}")] THEN
        REWRITE_TAC [UNIONS_0] THEN ASM SET_TAC [],
        DISCH_TAC] THEN
      SUBGOAL_THEN (← q r"!u:real^N->bool. u IN U ==> ~(k SUBSET closure u)")
      ASSUME_TAC THENL
       [X_GEN_TAC (← q r"u:real^N->bool") THEN REPEAT STRIP_TAC THEN
        MP_TAC hu THEN EXPAND_TAC "U" THEN
        REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN
        FIRST_ASSUM (ASSUME_TAC o MATCH_MP IN_COMPONENTS_CONNECTED) THEN
        FIRST_ASSUM (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT]
           OPEN_COMPONENTS)) THEN
        REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC [OPEN_BALL],
          DISCH_TAC] THEN
        SUBGOAL_THEN (← q r"path_connected(u:real^N->bool)") MP_TAC THENL
         [ASM_SIMP_TAC [CONNECTED_OPEN_PATH_CONNECTED],
          REWRITE_TAC [path_connected]] THEN
        DISCH_THEN (MP_TAC o SPECL [← q r"z1:real^N", ← q r"z2:real^N"]) THEN
        REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL
         [CONJ_TAC THEN
          REWRITE_TAC [← SET_RULE (← q r"z IN u <=> (z INSERT u) SUBSET u")] THEN
          FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ]
            COMPONENTS_MAXIMAL)) THEN
          FIRST_ASSUM (ASSUME_TAC o MATCH_MP IN_COMPONENTS_CONNECTED) THEN
          FIRST_ASSUM (ASSUME_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
          FIRST_ASSUM (ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
          ASM_SIMP_TAC [CONNECTED_INSERT] THEN ASM SET_TAC [],
          DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^1->real^N") STRIP_ASSUME_TAC) THEN
          REMOVE_THEN "I1" (MP_TAC o SPEC (← q r"path_image g:real^N->bool")) THEN
          ASM_SIMP_TAC [COMPACT_PATH_IMAGE, CONNECTED_PATH_IMAGE] THEN
          REWRITE_TAC [← GSYM CONJ_ASSOC, NOT_IMP] THEN
          CONJ_TAC THENL [ASM_MESON_TAC [PATHSTART_IN_PATH_IMAGE], ALL_TAC] THEN
          CONJ_TAC THENL [ASM_MESON_TAC [PATHFINISH_IN_PATH_IMAGE], ALL_TAC] THEN
          CONJ_TAC THENL
           [TRANS_TAC SUBSET_TRANS (← q r"ball(x:real^N,r)") THEN
            REWRITE_TAC [BALL_SUBSET_CBALL] THEN ASM SET_TAC [],
            REWRITE_TAC [REAL_NOT_LE]] THEN
          MP_TAC (← ISPECL [← q r"IMAGE (f:real^N->real^N) (path_image g)", ← q r"b:real^N"]
            DISTANCE_ATTAINS_SUP) THEN
          ASM_SIMP_TAC [IMAGE_EQ_EMPTY, PATH_IMAGE_NONEMPTY] THEN ANTS_TAC THENL
           [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
            ASM_SIMP_TAC [COMPACT_PATH_IMAGE] THEN
            FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
              CONTINUOUS_ON_SUBSET)) THEN
            FIRST_ASSUM (MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN ASM SET_TAC [],
            REWRITE_TAC [EXISTS_IN_IMAGE, FORALL_IN_IMAGE] THEN
            REWRITE_TAC [← ONCE_REWRITE_RULE [DIST_SYM] dist] THEN
            DISCH_THEN (X_CHOOSE_THEN (← q r"q:real^N") STRIP_ASSUME_TAC)] THEN
          TRANS_TAC REAL_LET_TRANS (← q r"norm((f:real^N->real^N) q - b)") THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_SUP_LE THEN
            ASM_SIMP_TAC [PATH_IMAGE_NONEMPTY, SIMPLE_IMAGE, IMAGE_EQ_EMPTY] THEN
            ASM_REWRITE_TAC [FORALL_IN_IMAGE],
            FIRST_X_ASSUM (MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
            REWRITE_TAC [IN_BALL, ← ONCE_REWRITE_RULE [DIST_SYM] dist] THEN
            ASM SET_TAC []]],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"?a:real^N. a IN k /\ !v. ~({u | u IN U /\ a IN closure u} SUBSET {v})")
      STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN
         (← q r"~(pairwise (\u v:real^N->bool.
               DISJOINT (k INTER closure u) (k INTER closure v)) U)")
        MP_TAC THENL [DISCH_TAC, REWRITE_TAC [pairwise] THEN SET_TAC []] THEN
        FIRST_ASSUM (MP_TAC o MATCH_MP (← SET_RULE
         (← q r"k SUBSET UNIONS {f u | u IN U}
          ==> ~(k = {}) ==> ?u. u IN U /\ ~(k INTER f u = {})"))) THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"u:real^N->bool") STRIP_ASSUME_TAC) THEN
        MP_TAC (← ISPEC (← q r"k:real^N->bool") CONNECTED_CLOSED) THEN ASM_REWRITE_TAC [] THEN
        EXISTS_TAC (← q r"closure u:real^N->bool") THEN
        EXISTS_TAC (← q r"closure(UNIONS (U DELETE u)):real^N->bool") THEN
        REWRITE_TAC [CLOSED_CLOSURE, ← GSYM CLOSURE_UNION, ← GSYM UNIONS_INSERT] THEN
        ASM_SIMP_TAC [← SET_RULE (← q r"x IN s ==> x INSERT (s DELETE x) = s")] THEN
        ASM_SIMP_TAC [CLOSURE_UNIONS, FINITE_DELETE, INTER_UNIONS] THEN
        REWRITE_TAC [EMPTY_UNIONS, FORALL_IN_GSPEC, IN_DELETE] THEN
        REPEAT STRIP_TAC THENL
         [REPEAT STRIP_TAC THEN
          ONCE_REWRITE_TAC [← SET_RULE (← q r"s INTER t INTER k = {} <=>
            (k INTER s) INTER (k INTER t) = {}")] THEN
          FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
          REWRITE_TAC [DISJOINT] THEN DISCH_THEN MATCH_MP_TAC THEN
          ASM_REWRITE_TAC [],
          ASM SET_TAC [],
          UNDISCH_TAC (← q r"k SUBSET UNIONS {closure u:real^N->bool | u IN U}") THEN
          SUBGOAL_THEN (← q r"~((k:real^N->bool) SUBSET closure u)") MP_TAC THENL
           [ASM_MESON_TAC [], ALL_TAC] THEN
          MATCH_MP_TAC (← SET_RULE
           (← q r"k INTER (t DIFF s) = {}
            ==> ~(k SUBSET s) ==> k SUBSET t ==> F")) THEN
          MATCH_MP_TAC (← SET_RULE
           (← q r"k INTER  UNIONS {f x | x IN s DELETE a} = {}
            ==> k INTER (UNIONS {f x | x IN s} DIFF f a) = {}")) THEN
          REWRITE_TAC [INTER_UNIONS, EMPTY_UNIONS, FORALL_IN_GSPEC] THEN
          ASM_MESON_TAC [IN_DELETE, INTER_COMM]],
        ALL_TAC] THEN
      REMOVE_THEN "L7" (MP_TAC o SPECL [← q r"e:real", ← q r"a:real^N", ← q r"b:real^N"]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM SET_TAC [], ALL_TAC] THEN
      REWRITE_TAC [NOT_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"h:real^N", ← q r"l:real", ← q r"t0:real", ← q r"u0:real^N->bool"] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN (← q r"(u0:real^N->bool) IN U") ASSUME_TAC THENL
       [EXPAND_TAC "U" THEN REWRITE_TAC [IN_ELIM_THM] THEN
        ASM_REWRITE_TAC [] THEN
        ONCE_REWRITE_TAC [INTER_COMM] THEN
        MP_TAC (← ISPECL [← q r"ball(x:real^N,r)", ← q r"u0:real^N->bool"]
          OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
        REWRITE_TAC [OPEN_BALL] THEN ASM SET_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"?u1:real^N->bool. u1 IN U /\ ~(u1 = u0) /\ a IN closure u1")
      STRIP_ASSUME_TAC THENL
       [FIRST_ASSUM (MP_TAC o SPEC (← q r"u0:real^N->bool") o MATCH_MP (← SET_RULE
         (← q r"(!v. ~(s SUBSET {v})) ==> !u. u IN s ==> ?v. v IN s /\ ~(v = u)"))) THEN
        ASM SET_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"?t z. &0 < t /\ t < t0 /\ z IN u1 /\
              norm(z - (a - t % h):real^N) < l * t")
      STRIP_ASSUME_TAC THENL
       [ALL_TAC,
        FIRST_X_ASSUM (MP_TAC o SPECL
         [← q r"inv(t) % (a - z):real^N", ← q r"t:real"]) THEN
        ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_RINV, REAL_LT_IMP_NZ] THEN
        REWRITE_TAC [← VECTOR_ARITH (← q r"a - &1 % (a - z):real^N = z"), NOT_IMP] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC (← q r"abs t") THEN
          REWRITE_TAC [← GSYM NORM_MUL, VECTOR_SUB_LDISTRIB] THEN
          ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_RINV, REAL_LT_IMP_NZ] THEN
          ASM_SIMP_TAC [← REAL_ARITH (← q r"&0 < x ==> abs x = x"), VECTOR_MUL_LID] THEN
          REWRITE_TAC [← NORM_ARITH (← q r"norm(a - z - h:real^N) = norm(z - (a - h))")] THEN
          ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN ASM_SIMP_TAC [REAL_LT_IMP_LE],
          FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
           (← q r"z IN u1
            ==> ~(u1 = u0) /\ (u0 INTER u1 = {} <=> ~(u0 = u1))
            ==> ~(z IN u0)"))) THEN
          CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
          MATCH_MP_TAC COMPONENTS_NONOVERLAP THEN
          EXISTS_TAC (← q r"{x | x IN s /\ (f:real^N->real^N) x IN ball(b,e)}") THEN
          ASM SET_TAC []]] THEN
      SUBGOAL_THEN (← q r"(a:real^N) IN s") ASSUME_TAC THENL
       [ASM SET_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"~((f:real^N->real^N) a = b)") ASSUME_TAC THENL
       [DISCH_TAC THEN
        UNDISCH_TAC (← q r"(u1:real^N->bool) IN U") THEN EXPAND_TAC "U" THEN
        REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN
        MP_TAC (← ISPECL
         [← q r"{x | x IN s /\ (f:real^N->real^N) x IN ball (b,e)}",
          ← q r"u0:real^N->bool", ← q r"u1:real^N->bool"]
            COMPONENTS_NONOVERLAP) THEN
        ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_INTER] THEN
        EXISTS_TAC (← q r"a:real^N") THEN CONJ_TAC THEN
        REWRITE_TAC [← SET_RULE (← q r"z IN u <=> (z INSERT u) SUBSET u")] THEN
        FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ]
            COMPONENTS_MAXIMAL)) THEN
        REPEAT (FIRST_X_ASSUM (fun th => tactic_of do
          pure (ASSUME_TAC (← MATCH_MP IN_COMPONENTS_CONNECTED th) THEN
                ASSUME_TAC (← MATCH_MP IN_COMPONENTS_NONEMPTY th) THEN
                ASSUME_TAC (← MATCH_MP IN_COMPONENTS_SUBSET th)))) THEN
        ASM_SIMP_TAC [CONNECTED_INSERT] THEN ASM SET_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!w. open w /\ a IN w
            ==> ?w'. open w' /\
                     (?t1. &0 < t1 /\
                           !t. &0 < t /\ t < t1 ==> (f(a) + t % (b - f a)) IN w') /\
                     w' SUBSET IMAGE (f:real^N->real^N) (u1 INTER w)")
      (LABEL_TAC "L8") THENL
       [X_GEN_TAC (← q r"v:real^N->bool") THEN STRIP_TAC THEN
        REMOVE_THEN "L2" (MP_TAC o SPEC (← q r"a:real^N")) THEN
        ANTS_TAC THENL [ASM SET_TAC [], REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN
        MAP_EVERY X_GEN_TAC [← q r"rr:real", ← q r"dd:real"] THEN STRIP_TAC THEN
        SUBGOAL_THEN (← q r"?q. &0 < q /\ q < rr /\ ball(a:real^N,q) SUBSET v INTER s /\
                          cball(a,q) SUBSET s")
        MP_TAC THENL
         [MP_TAC (← ISPEC (← q r"v:real^N->bool") OPEN_CONTAINS_CBALL) THEN
          ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o SPEC (← q r"a:real^N")) THEN
          ASM_REWRITE_TAC [SUBSET_INTER, LEFT_IMP_EXISTS_THM] THEN
          X_GEN_TAC (← q r"q:real") THEN STRIP_TAC THEN
          EXISTS_TAC (← q r"min q (rr / &2)") THEN
          ASM_REWRITE_TAC [REAL_HALF, BALL_MIN_INTER, CBALL_MIN_INTER, REAL_LT_MIN,
                           REAL_MIN_LT, ← REAL_ARITH (← q r"r / &2 < r <=> &0 < r")] THEN
          MATCH_MP_TAC (← SET_RULE
           (← q r"b SUBSET c /\ b' SUBSET c' /\ c' SUBSET s /\ c SUBSET v
            ==> (b INTER b' SUBSET v /\ b INTER b' SUBSET s) /\
                 c INTER c' SUBSET s")) THEN
          ASM_REWRITE_TAC [BALL_SUBSET_CBALL] THEN
          TRANS_TAC SUBSET_TRANS (← q r"cball(a:real^N,rr)") THEN ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC,
          REWRITE_TAC [SUBSET_INTER, LEFT_IMP_EXISTS_THM]] THEN
        X_GEN_TAC (← q r"q:real") THEN STRIP_TAC THEN
        ABBREV_TAC (← q r"vv = ball(b,e) INTER ball((f:real^N->real^N) a,dd * q)") THEN
        EXISTS_TAC (← q r"vv:real^N->bool") THEN
        MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
         [EXPAND_TAC "vv" THEN SIMP_TAC [OPEN_BALL, OPEN_INTER], DISCH_TAC] THEN
        CONJ_TAC THENL
         [EXPAND_TAC "vv" THEN REWRITE_TAC [IN_INTER, IN_BALL] THEN
          REWRITE_TAC [← NORM_ARITH (← q r"dist(a:real^N,a + x) = norm x")] THEN
          EXISTS_TAC (← q r"min (&1) ((dd * q) / norm(b - (f:real^N->real^N) a))") THEN
          ASM_SIMP_TAC [REAL_LT_MIN, REAL_LT_01, REAL_LT_MUL, REAL_LT_DIV,
                        NORM_POS_LT, VECTOR_SUB_EQ] THEN
          X_GEN_TAC (← q r"t:real") THEN STRIP_TAC THEN CONJ_TAC THENL
           [REWRITE_TAC [← NORM_ARITH (← q r"dist(b:real^N,a + x) = norm((b - a) - x)")] THEN
            REWRITE_TAC [← VECTOR_ARITH
             (← q r"b - a - t % (b - a):real^N = (&1 - t) % (b - a)")] THEN
            REWRITE_TAC [NORM_MUL] THEN MATCH_MP_TAC (← REAL_ARITH
             (← q r"n <= e /\ x * n < &1 * n ==> x * n < e")) THEN
            CONJ_TAC THENL
             [ONCE_REWRITE_TAC [NORM_SUB] THEN ASM_MESON_TAC [], ALL_TAC] THEN
            ASM_SIMP_TAC [REAL_LT_RMUL_EQ, NORM_POS_LT, VECTOR_SUB_EQ] THEN
            ASM_REAL_ARITH_TAC,
            ASM_SIMP_TAC [NORM_MUL, ← GSYM REAL_LT_RDIV_EQ, NORM_POS_LT,
                          VECTOR_SUB_EQ] THEN
            ASM_SIMP_TAC [← REAL_ARITH (← q r"&0 < t ==> abs t = t")]],
          ALL_TAC] THEN
        TRANS_TAC SUBSET_TRANS (← q r"IMAGE (f:real^N->real^N) (ball(a,q) INTER u1)") THEN
        CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
        EXPAND_TAC "vv" THEN REMOVE_THEN "L3" MATCH_MP_TAC THEN
        ASM_SIMP_TAC [OPEN_BALL, OPEN_INTER, BOUNDED_BALL, BOUNDED_INTER] THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC [OPEN_BALL] THEN
          UNDISCH_TAC (← q r"(u1:real^N->bool) IN U") THEN EXPAND_TAC "U" THEN
          REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (MP_TAC o CONJUNCT1) THEN
          MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] OPEN_COMPONENTS) THEN
          MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC [OPEN_BALL],
          TRANS_TAC SUBSET_TRANS (← q r"closure(ball(a:real^N,q))") THEN CONJ_TAC THENL
           [MATCH_MP_TAC SUBSET_CLOSURE THEN SET_TAC [],
            ASM_SIMP_TAC [CLOSURE_BALL]],
          EXPAND_TAC "vv" THEN MATCH_MP_TAC CONVEX_CONNECTED THEN
          SIMP_TAC [CONVEX_BALL, CONVEX_INTER],
          EXPAND_TAC "vv" THEN MATCH_MP_TAC (← SET_RULE
           (← q r"(!x. x IN t2 ==> f x IN s1) /\
            ~(t2 INTER {x | x IN t1 /\ f x IN s2} = {})
            ==> ~((s1 INTER s2) INTER IMAGE f (t1 INTER t2) = {})")) THEN
          CONJ_TAC THENL
           [UNDISCH_TAC (← q r"(u1:real^N->bool) IN U") THEN EXPAND_TAC "U" THEN
            REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (MP_TAC o CONJUNCT1) THEN
            DISCH_THEN (MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN SET_TAC [],
            FIRST_X_ASSUM (MATCH_MP_TAC o GEN_REWRITE_RULE I
             [CLOSURE_NONEMPTY_OPEN_INTER]) THEN
            ASM_SIMP_TAC [IN_ELIM_THM, CENTRE_IN_BALL, REAL_LT_MUL] THEN
            MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
            REWRITE_TAC [OPEN_BALL] THEN ASM_MESON_TAC [CONTINUOUS_ON_SUBSET]],
          REWRITE_TAC [← SET_RULE
           (← q r"s INTER IMAGE f t = {} <=> !x. x IN t ==> ~(f x IN s)")] THEN
          X_GEN_TAC (← q r"z:real^N") THEN DISCH_THEN (MP_TAC o MATCH_MP
           (← REWRITE_RULE [SUBSET] FRONTIER_INTER_SUBSET)) THEN
          EXPAND_TAC "vv" THEN REWRITE_TAC [IN_UNION, IN_INTER, DE_MORGAN_THM] THEN
          GEN_REWRITE_TAC RAND_CONV [DISJ_SYM] THEN
          MATCH_MP_TAC MONO_OR THEN CONJ_TAC THENL
           [ASM_SIMP_TAC [FRONTIER_BALL, IN_SPHERE, IN_BALL] THEN
            DISCH_THEN (fun th => tactic_of do
              pure (ASSUME_TAC th THEN SUBST1_TAC (← SYM th))) THEN
            REWRITE_TAC [← ONCE_REWRITE_RULE [DIST_SYM] dist, REAL_NOT_LT] THEN
            FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [IN_CBALL, REAL_LT_IMP_LE],
            REWRITE_TAC [← GSYM CBALL_DIFF_SPHERE] THEN ASM SET_TAC []]],
        ALL_TAC] THEN
      REMOVE_THEN "L5"
       (MP_TAC o
        SPECL [← q r"a:real^N", ← q r"l / norm((f:real^N->real^N) a - b)"]) THEN
      ASM_SIMP_TAC [REAL_LT_DIV, NORM_POS_LT, VECTOR_SUB_EQ] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"dd:real") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN (MP_TAC o GEN (← q r"t:real") o
        SPEC (← q r"(f:real^N->real^N)(a) + t % (b - f a)")) THEN
      REWRITE_TAC [← SET_RULE
       (← q r"b INTER {x | x IN s /\ f x = y} SUBSET c <=>
        !x. x IN b /\ x IN s /\ y = f x ==> x IN c")] THEN
      SIMP_TAC [] THEN
      DISCH_THEN (MP_TAC o MATCH_MP
        (← MESON [] (← q r"(!t. P t) ==> (!t. &0 < t ==> P t)"))) THEN
      SIMP_TAC [VECTOR_MUL_EQ_0, ← VECTOR_ARITH (← q r"a:real^N = a + x <=> x = vec 0"),
                VECTOR_SUB_EQ, REAL_LT_IMP_NZ] THEN
      ASM_REWRITE_TAC [] THEN
      ONCE_REWRITE_TAC [← VECTOR_ARITH (← q r"a + b:real^N = c <=> c - a = b")] THEN
      ASM_SIMP_TAC [LINEAR_CMUL] THEN
      SUBST1_TAC (← VECTOR_ARITH (← q r"b - (f:real^N->real^N) a = --(f a - b)")) THEN
      ASM_SIMP_TAC [LINEAR_NEG, ← VECTOR_ARITH (← q r"a + t % --h:real^N = a - t % h")] THEN
      REWRITE_TAC [NORM_MUL, NORM_NEG] THEN
      ASM_SIMP_TAC [NORM_POS_LT, VECTOR_SUB_EQ, ← REAL_FIELD
      (← q r"&0 < n ==> l / n * t * n = l * t")] THEN
      ASM_SIMP_TAC [IN_BALL, ← REAL_ARITH (← q r"&0 < t ==> abs t = t")] THEN
      REWRITE_TAC [RIGHT_IMP_FORALL_THM, IMP_IMP] THEN
      REWRITE_TAC [← ONCE_REWRITE_RULE [DIST_SYM] dist] THEN
      MATCH_MP_TAC (← MESON []
       (← q r"(?x t. P t /\ A t /\ B x /\ R x t)
        ==> (!t x. P t /\ R x t ==> Q x t)
            ==> (?t x. P t /\ A t /\ B x /\ Q x t)")) THEN
      REMOVE_THEN "L8" (MP_TAC o SPEC (← q r"ball(a:real^N,dd)")) THEN
      ASM_REWRITE_TAC [OPEN_BALL, CENTRE_IN_BALL] THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← MESON [SUBSET]
       (← q r"(?w. open w /\ (?t0. P t0 /\ !t. R t t0 ==> f t IN w) /\
             w SUBSET u)
        ==> ?t0. P t0 /\ !t. R t t0 ==> f t IN u"))) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"t1:real") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC [IN_IMAGE] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"(min t0 t1) / &2")) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC, REWRITE_TAC [IN_INTER, IN_BALL]] THEN
      MATCH_MP_TAC MONO_EXISTS THEN
      REWRITE_TAC [← ONCE_REWRITE_RULE [DIST_SYM] dist] THEN
      X_GEN_TAC (← q r"z:real^N") THEN DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN
      EXISTS_TAC (← q r"(min t0 t1) / &2") THEN
      ASM_REWRITE_TAC [VECTOR_ADD_SUB, VECTOR_NEG_SUB] THEN
      REPEAT (CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
      UNDISCH_TAC (← q r"(u1:real^N->bool) IN U") THEN EXPAND_TAC "U" THEN
      REWRITE_TAC [IN_ELIM_THM] THEN
      DISCH_THEN (MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET o CONJUNCT1) THEN
      ASM SET_TAC []))

  pure { INVERSE_FUNCTION_THEOREM }

/- ------------------------------------------------------------------------- -/
/- Sign invariance of nonvanishing Jacobian (also from Saint Raymond).       -/
/- (derivatives.ml 3956-4428)                                                -/
/- ------------------------------------------------------------------------- -/

structure DVJ where
  JACOBIAN_SIGN_INVARIANCE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDVJ [HolBase] (D : DerivativesDeps) (BDVA : DVA) (BDVB : DVB) (BDVI : DVI) : ExceptT String IO DVJ := do
  -- @@SCOPE BEGIN
  let { differentiable, has_derivative, has_derivative_at, .. } := BDVA
  let { DIFFERENTIABLE_IMP_CONTINUOUS_AT, .. } := BDVB
  let { INVERSE_FUNCTION_THEOREM, .. } := BDVI
  let { ARITH_EQ, CONJ_ASSOC, ETA_AX, FORALL_AND_THM, .. } := D.dg.pt.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_IN_PCROSS, FORALL_PASTECART, FSTCART_PASTECART, FUN_EQ_THM,
        IMP_CONJ, IMP_CONJ_ALT, IMP_IMP, IN_DELETE, .. } := D.dg.pt.cvx.core2
  let { I_THM, IN_INTER, IN_UNIV, LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM,
        PASTECART_IN_PCROSS, PASTECART_INJ, REAL_ABS_INV, REAL_ABS_MUL, REAL_DIV_EQ_0, .. }
        := D.dg.pt.cvx.core3
  let { REAL_ENTIRE, REAL_INV_1, REAL_INV_EQ_0, REAL_INV_MUL, REAL_LE_ADD, REAL_LE_MUL,
        REAL_LE_MUL2, REAL_LE_REFL, REAL_LE_RMUL, REAL_LE_TRANS, REAL_LT_01, REAL_LT_IMP_LE,
        REAL_LT_IMP_NE, REAL_LT_IMP_NZ, .. } := D.dg.pt.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_LZERO, REAL_MUL_RID,
        REAL_MUL_RINV, REAL_MUL_SYM, REAL_POS, REAL_POW_LE, REAL_SGN_CASES, REAL_SGN_EQ,
        REAL_SUB_0, REAL_SUB_LE, REAL_SUB_LT, SNDCART_PASTECART, SUBSET, SUBSET_PCROSS,
        SUBSET_REFL, SUBSET_TRANS, .. } := D.dg.pt.cvx.core5
  let { o_ASSOC, o_DEF, o_THM, real_div, real_gt, .. } := D.dg.pt.cvx.core6
  let { REAL_HALF, .. } := D.dg.pt.cvx.misc
  let { DROP_EQ, DROP_SUB, DROP_VEC, FORALL_LIFT, LIFT_CMUL, LIFT_DROP, LIFT_EQ, LIFT_NUM,
        LIFT_SUB, LINEAR_0, LINEAR_CMUL, LINEAR_FSTCART, LINEAR_SNDCART, NORM_0, NORM_1,
        NORM_EQ_0, .. } := D.dg.pt.cvx.vec2
  let { NORM_MUL, NORM_NEG, NORM_POS_LE, REAL_ABS_NORM, .. } := D.dg.pt.cvx.vec3
  let { VECTOR_ADD_ASSOC, VECTOR_ADD_LDISTRIB, VECTOR_ADD_RID, VECTOR_ADD_SUB,
        VECTOR_MUL_ASSOC, VECTOR_MUL_EQ_0, VECTOR_MUL_LID, VECTOR_MUL_LZERO,
        VECTOR_MUL_RCANCEL, VECTOR_MUL_RZERO, VECTOR_SUB_EQ, VECTOR_SUB_LDISTRIB,
        VECTOR_SUB_REFL, VECTOR_SUB_RZERO, .. } := D.dg.pt.cvx.vec4
  let { EVENTUALLY_TRUE, .. } := D.dg.pt.cvx.met
  let { CENTRE_IN_BALL, .. } := D.dg.pt.cvx.top1
  let { CLOSURE_INTERVAL, CLOSURE_SUBSET, CONTINUOUS_ADD, .. } := D.dg.pt.cvx.top2
  let { CONTINUOUS_CONST, CONTINUOUS_LIFT_NORM_COMPOSE, CONTINUOUS_MUL, CONTINUOUS_SUB,
        EVENTUALLY_WITHIN, .. } := D.dg.pt.cvx.top3
  let { IN_BALL, IN_INTERVAL_1, LIM_MUL, LIM_NORM, LIM_NULL_ADD, LIM_NULL_COMPARISON,
        LIM_SUB, OPEN_BALL, OPEN_CONTAINS_BALL, .. } := D.dg.pt.cvx.top4
  let { homeomorphism, OPEN_IN_OPEN_EQ, OPEN_UNIV, UNIT_INTERVAL_NONEMPTY, .. } :=
        D.dg.pt.cvx.top5
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON, MESON_TAC, NORM_ARITH, NUM_REDUCE_CONV,
        REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD, REAL_RAT_REDUCE_CONV, SET_RULE, SET_TAC,
        VECTOR_ARITH, .. } := D.dg.pt.cvx
  let { VEC_EQ, .. } := D.dg.pt.qvec
  let { CONTINUOUS_CMUL, SUBSET_BALL, .. } := D.dg.pt.qtop
  let { INVERTIBLE_DET_NZ, .. } := D.dg.qdet
  let { HOMOTOPIC_WITH_EUCLIDEAN_ALT, .. } := D.dg.qpaths1
  let { I_DEF, I_O_ID, .. } := D.dg.qsession
  let { OPEN_DELETE, .. } := D.dg.qtopology2
  let { MATRIX_INVERTIBLE, .. } := D.dg.qvec
  let { HOMOTOPIC_LINEAR_MAPS_IMP, .. } := D.qdegree
  let { ALWAYS_EVENTUALLY, .. } := D.qmetric
  let { REAL_LT_MUL2, REAL_LT_RMUL_EQ, REAL_POW_MONO_INV, .. } := D.qsession
  let { CLOSURE_PCROSS, CONTINUOUS_AT_WITHIN, CONTINUOUS_AT_WITHIN_INV, CONTINUOUS_LIFT_POW,
        CONTINUOUS_ON_INTERMEDIATE_CLOSURE, CONTINUOUS_PASTECART, CONTINUOUS_WITHIN_COMPOSE,
        EVENTUALLY_WITHIN_TOPOLOGICAL, .. } := D.qtopology1
  let { LIM_COMPOSE_AT, LIM_COMPOSE_WITHIN, LIM_CONTINUOUS_SELF_WITHIN, LIM_EVENTUALLY,
        LIM_INV, LIM_LINEAR, LIM_NULL, LIM_NULL_CMUL, LIM_NULL_NEG, LIM_NULL_NORM,
        LIM_NULL_SUB, LIM_NULL_VMUL, LIM_TRANSFORM, LIM_TRANSFORM_EVENTUALLY, LIM_VMUL,
        LINEAR_CONTINUOUS_WITHIN, LOCALLY_CONSTANT_IMP_CONSTANT, OPEN_PCROSS, .. } :=
        D.qtopology2
  -- @@SCOPE END

  let JACOBIAN_SIGN_INVARIANCE ← prove
   r"!f:real^N->real^N f' s.
        open s /\ connected s /\
        (!x. x IN s
             ==> (f has_derivative f' x) (at x) /\ ~(det(matrix (f' x)) = &0))
        ==> (!x. x IN s ==> &0 < det(matrix(f' x))) \/
            (!x. x IN s ==> det(matrix(f' x)) < &0)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [← GSYM (← REWRITE_RULE [real_gt] REAL_SGN_EQ)] THEN
    MATCH_MP_TAC (← MESON [REAL_SGN_CASES]
     (← q r"(!x. x IN s ==> ~(real_sgn(f x) = &0)) /\
      (?c. !x. x IN s ==> real_sgn(f x) = c)
      ==> (!x. x IN s ==> real_sgn(f x) = &1) \/
          (!x. x IN s ==> real_sgn(f x) = -- &1)")) THEN
    ASM_SIMP_TAC [REAL_SGN_EQ] THEN
    MATCH_MP_TAC LOCALLY_CONSTANT_IMP_CONSTANT THEN
    ASM_SIMP_TAC [OPEN_IN_OPEN_EQ] THEN X_GEN_TAC (← q r"a:real^N") THEN DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"?r. &0 < r /\ ball(a,&2 * r) SUBSET s /\
          (!x y. x IN ball(a,&2 * r) /\ y IN ball(a,&2 * r)
                 ==> ((f:real^N->real^N) x = f y <=> x = y))")
    STRIP_ASSUME_TAC THENL
     [MP_TAC (← ISPECL
       [← q r"f:real^N->real^N", ← q r"f':real^N->real^N->real^N",
        ← q r"a:real^N", ← q r"s:real^N->bool"] INVERSE_FUNCTION_THEOREM) THEN
      ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC
       [← q r"t:real^N->bool", ← q r"u:real^N->bool",
        ← q r"g:real^N->real^N", ← q r"g':real^N->real^N->real^N"] THEN
      REWRITE_TAC [homeomorphism] THEN STRIP_TAC THEN
      MP_TAC (← ISPEC (← q r"t:real^N->bool") OPEN_CONTAINS_BALL) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o SPEC (← q r"a:real^N")) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"r:real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"r / &2") THEN ASM_REWRITE_TAC [REAL_HALF] THEN ASM SET_TAC [],
      EXISTS_TAC (← q r"ball(a:real^N,r)") THEN
      ASM_REWRITE_TAC [OPEN_BALL, CENTRE_IN_BALL]] THEN
    MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
     [TRANS_TAC SUBSET_TRANS (← q r"ball(a:real^N,&2 * r)") THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC,
      DISCH_TAC] THEN
    X_GEN_TAC (← q r"b:real^N") THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC HOMOTOPIC_LINEAR_MAPS_IMP THEN
    REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL
     [ASM_MESON_TAC [has_derivative, SUBSET], ALL_TAC] THEN
    SIMP_TAC [HOMOTOPIC_WITH_EUCLIDEAN_ALT] THEN EXISTS_TAC
     (← q r"\z. if fstcart z:real^1 = vec 0
          then (f':real^N->real^N->real^N) a (sndcart z)
          else if fstcart z = vec 1
          then (f':real^N->real^N->real^N) b (sndcart z)
          else norm(sndcart z) / (drop(fstcart z) * (&1 - drop(fstcart z)) * r) %
               (f((a + (&3 * drop(fstcart z) pow 2 - &2 * drop(fstcart z) pow 3) %
                  (b - a)) +
                  (drop(fstcart z) * (&1 - drop(fstcart z)) * r) %
                  inv(norm(sndcart z)) % sndcart z)  -
                f(a + (&3 * drop(fstcart z) pow 2 - &2 * drop(fstcart z) pow 3) %
                  (b - a)))") THEN
    REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART, VEC_EQ, ARITH_EQ] THEN
    SUBGOAL_THEN
     (← q r"!x t. ~(x = vec 0) /\ &0 <= t /\ t <= &1 /\ ~(t = &0) /\ ~(t = &1)
            ==> (a + (&3 * t pow 2 - &2 * t pow 3) % (b - a:real^N)) +
                 (t * (&1 - t) * r) % inv (norm x) % x IN ball(a,&2 * r) /\
                a + (&3 * t pow 2 - &2 * t pow 3) % (b - a) IN ball(a,&2 * r)")
    MP_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [IN_BALL] THEN
      MATCH_MP_TAC (← NORM_ARITH
       (← q r"norm(x:real^N) <= r /\ norm y < r
        ==> dist(a,(a + x) + y) < &2 * r /\ dist(a,a + x) < &2 * r")) THEN
      REWRITE_TAC [NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
      ASM_SIMP_TAC [REAL_MUL_LINV, NORM_EQ_0, REAL_MUL_RID] THEN
      ASM_SIMP_TAC [REAL_ABS_MUL, REAL_MUL_ASSOC, REAL_LT_RMUL_EQ, ← REAL_ARITH
       (← q r"&0 < r ==> (x * abs r < r <=> x * r < &1 * r)")] THEN
      CONJ_TAC THENL
       [ALL_TAC,
        GEN_REWRITE_TAC RAND_CONV [← GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REAL_ARITH_TAC] THEN
      TRANS_TAC REAL_LE_TRANS (← q r"dist(a:real^N,b)") THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE, ← GSYM IN_BALL] THEN
      REWRITE_TAC [← NORM_ARITH (← q r"dist(a:real^N,b) = &1 * norm(b - a)")] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [NORM_POS_LE] THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"y <= x /\ &0 <= y - x + &1
        ==> abs(x - y) <= &1")) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_SIMP_TAC [REAL_POW_LE] THEN MATCH_MP_TAC REAL_POW_MONO_INV THEN
        CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC,
        REWRITE_TAC [← REAL_ARITH
         (← q r"&2 * t pow 3 - &3 * t pow 2 + &1 =
          (&1 - t) pow 2 + &2 * t * (&1 - t) pow 2")] THEN
        MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
        ASM_SIMP_TAC [REAL_LE_MUL, REAL_POS, REAL_POW_LE, REAL_SUB_LE]],
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [← TAUT (← q r"p ==> q /\ r <=> (p ==> q) /\ (p ==> r)")] THEN
      REWRITE_TAC [FORALL_AND_THM] THEN STRIP_TAC] THEN
    CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_IN_PCROSS] THEN
      REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART] THEN
      REWRITE_TAC [IN_INTERVAL_1, IN_UNIV, IN_DELETE, DROP_VEC] THEN
      REWRITE_TAC [FORALL_LIFT, LIFT_DROP, ← GSYM DROP_EQ, DROP_VEC] THEN
      MAP_EVERY X_GEN_TAC [← q r"t:real", ← q r"x:real^N"] THEN STRIP_TAC THEN
      ASM_CASES_TAC (← q r"t = &0") THEN ASM_REWRITE_TAC [] THENL
       [SUBGOAL_THEN
         (← q r"linear((f':real^N->real^N->real^N) a) /\ invertible(matrix(f' a))")
        MP_TAC THENL
         [ASM_MESON_TAC [has_derivative, INVERTIBLE_DET_NZ], ALL_TAC] THEN
        SIMP_TAC [IMP_CONJ, MATRIX_INVERTIBLE, FUN_EQ_THM, o_THM, I_THM] THEN
        ASM_MESON_TAC [LINEAR_0],
        ALL_TAC] THEN
      ASM_CASES_TAC (← q r"t = &1") THEN ASM_REWRITE_TAC [] THENL
       [SUBGOAL_THEN
         (← q r"linear((f':real^N->real^N->real^N) b) /\ invertible(matrix(f' b))")
        MP_TAC THENL
         [ASM_MESON_TAC [has_derivative, SUBSET, INVERTIBLE_DET_NZ], ALL_TAC] THEN
        SIMP_TAC [IMP_CONJ, MATRIX_INVERTIBLE, FUN_EQ_THM, o_THM, I_THM] THEN
        ASM_MESON_TAC [LINEAR_0],
        ALL_TAC] THEN
      REWRITE_TAC [VECTOR_MUL_EQ_0, REAL_DIV_EQ_0, REAL_ENTIRE] THEN
      ASM_SIMP_TAC [NORM_EQ_0, REAL_LT_IMP_NZ, REAL_SUB_0, VECTOR_SUB_EQ] THEN
      FIRST_X_ASSUM (fun th =>
       W (MP_TAC o PART_MATCH (lhand o rand) th o rand o snd)) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC [],
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC [← VECTOR_ARITH (← q r"x + y:real^N = x <=> y = vec 0")] THEN
      ASM_REWRITE_TAC [VECTOR_MUL_EQ_0, REAL_INV_EQ_0, NORM_EQ_0,
                       REAL_ENTIRE] THEN
      ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_INTERMEDIATE_CLOSURE THEN EXISTS_TAC
     (← q r"interval(vec 0:real^1,vec 1) PCROSS ((:real^N) DELETE vec 0)") THEN
    CONJ_TAC THENL
     [REWRITE_TAC [CLOSURE_PCROSS, CLOSURE_INTERVAL, UNIT_INTERVAL_NONEMPTY,
                   SUBSET_PCROSS, SUBSET_REFL, CLOSURE_SUBSET],
      ALL_TAC] THEN
    REWRITE_TAC [FORALL_PASTECART, PASTECART_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [← q r"t:real^1", ← q r"x:real^N"] THEN
    REWRITE_TAC [IN_DELETE, IN_UNIV] THEN STRIP_TAC THEN
    MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN EXISTS_TAC
     (← q r"\z. norm(sndcart z) / (drop(fstcart z) * (&1 - drop(fstcart z)) * r) %
          (f((a + (&3 * drop(fstcart z) pow 2 - &2 * drop(fstcart z) pow 3) %
             (b - a)) +
             (drop(fstcart z) * (&1 - drop(fstcart z)) * r) %
             inv(norm(sndcart z)) % sndcart z)  -
           (f:real^N->real^N)
           (a + (&3 * drop(fstcart z) pow 2 - &2 * drop(fstcart z) pow 3) %
             (b - a)))") THEN
    REWRITE_TAC [EVENTUALLY_WITHIN, FSTCART_PASTECART, SNDCART_PASTECART] THEN
    CONJ_TAC THENL
     [EXISTS_TAC (← q r"&1") THEN REWRITE_TAC [REAL_LT_01, FORALL_PASTECART] THEN
      SIMP_TAC [PASTECART_IN_PCROSS, FSTCART_PASTECART, REAL_LT_IMP_NE,
                IN_INTERVAL_1, DROP_VEC, ← GSYM DROP_EQ],
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [LIM_NULL] THEN
    ASM_CASES_TAC (← q r"t:real^1 = vec 0") THEN ASM_REWRITE_TAC [] THENL
     [SUBGOAL_THEN (← q r"((f:real^N->real^N) has_derivative f'(a)) (at a)")
      MP_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      SPEC_TAC ((← q r"(f':real^N->real^N->real^N) a"), (← q r"f':real^N->real^N")) THEN
      SPEC_TAC ((← q r"b - a:real^N"), (← q r"v:real^N")) THEN
      SPEC_TAC ((← q r"a:real^N"), (← q r"a:real^N")) THEN
      MAP_EVERY UNDISCH_TAC [← q r"&0 < r", ← q r"~(x:real^N = vec 0)"],
      ASM_CASES_TAC (← q r"t:real^1 = vec 1") THEN ASM_REWRITE_TAC [] THENL
       [MATCH_MP_TAC (← MESON [I_O_ID]
         (← q r"!g. g o g = I /\ ((f o g o g) --> l) net
              ==> (f --> l) net")) THEN
        EXISTS_TAC (← q r"\z:real^(1,N)finite_sum.
                          pastecart (vec 1 - fstcart z) (sndcart z)") THEN
        CONJ_TAC THENL
         [REWRITE_TAC [o_DEF, I_DEF, FUN_EQ_THM, FORALL_PASTECART] THEN
          REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART] THEN
          REWRITE_TAC [← VECTOR_ARITH (← q r"x - (x - y):real^N = y")],
          REWRITE_TAC [o_ASSOC]] THEN
        MATCH_MP_TAC LIM_COMPOSE_WITHIN THEN MAP_EVERY EXISTS_TAC
         [← q r"interval(vec 0:real^1,vec 1) PCROSS ((:real^N) DELETE vec 0)",
          ← q r"pastecart (vec 0:real^1) (x:real^N)"] THEN
        REWRITE_TAC [] THEN CONJ_TAC THENL
         [MATCH_MP_TAC LIM_CONTINUOUS_SELF_WITHIN THEN
          REWRITE_TAC [FSTCART_PASTECART, VECTOR_SUB_REFL, SNDCART_PASTECART] THEN
          MATCH_MP_TAC CONTINUOUS_PASTECART THEN
          SIMP_TAC [CONTINUOUS_SUB, CONTINUOUS_CONST, LINEAR_CONTINUOUS_WITHIN,
                    LINEAR_FSTCART, LINEAR_SNDCART],
          REWRITE_TAC [DROP_SUB, DROP_VEC, PASTECART_IN_PCROSS, PASTECART_INJ,
             IN_INTERVAL_1, ← GSYM DROP_EQ, EVENTUALLY_WITHIN,
             FORALL_PASTECART, o_DEF, FSTCART_PASTECART, SNDCART_PASTECART] THEN
          SIMP_TAC [REAL_LT_IMP_NE, REAL_SUB_0, REAL_SUB_LT,
                    ← REAL_ARITH (← q r"&1 - x < &1 <=> &0 < x")] THEN
          CONJ_TAC THENL [MESON_TAC [REAL_LT_01], ALL_TAC]] THEN
        REWRITE_TAC [← REAL_ARITH
         (← q r"(&1 - x) * (&1 - (&1 - x)) * r = x * (&1 - x) * r")] THEN
        REWRITE_TAC [← REAL_ARITH
         (← q r"&3 * (&1 - t) pow 2 - &2 * (&1 - t) pow 3 =
          &1 - (&3 * t pow 2 - &2 * t pow 3)")] THEN
        REWRITE_TAC [← VECTOR_ARITH
         (← q r"a + (&1 - x) % (b - a):real^N = b + x % (a - b)")] THEN
        SUBGOAL_THEN (← q r"((f:real^N->real^N) has_derivative f'(b)) (at b)")
        MP_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
        SPEC_TAC ((← q r"(f':real^N->real^N->real^N) b"), (← q r"f':real^N->real^N")) THEN
        SPEC_TAC ((← q r"a - b:real^N"), (← q r"v:real^N")) THEN
        SPEC_TAC ((← q r"b:real^N"), (← q r"a:real^N")) THEN
        MAP_EVERY UNDISCH_TAC [← q r"&0 < r", ← q r"~(x:real^N = vec 0)"],
        MATCH_MP_TAC LIM_CONTINUOUS_SELF_WITHIN THEN
        REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART, VECTOR_SUB_REFL] THEN
        MATCH_MP_TAC CONTINUOUS_SUB THEN REWRITE_TAC [CONTINUOUS_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_MUL THEN REWRITE_TAC [o_DEF] THEN CONJ_TAC THENL
         [REWRITE_TAC [real_div, LIFT_CMUL] THEN
          MATCH_MP_TAC CONTINUOUS_MUL THEN
          SIMP_TAC [o_DEF, CONTINUOUS_LIFT_NORM_COMPOSE, LINEAR_SNDCART,
                    LINEAR_CONTINUOUS_WITHIN] THEN
          MATCH_MP_TAC (← REWRITE_RULE [o_DEF] CONTINUOUS_AT_WITHIN_INV) THEN
          ASM_SIMP_TAC [REAL_ENTIRE, FSTCART_PASTECART, REAL_LT_IMP_NZ] THEN
          REWRITE_TAC [REAL_SUB_0] THEN
          ASM_REWRITE_TAC [← GSYM LIFT_EQ, LIFT_DROP, LIFT_NUM] THEN
          ASM_REWRITE_TAC [LIFT_CMUL, LIFT_SUB, LIFT_DROP, REAL_SUB_0] THEN
          REPEAT (MATCH_MP_TAC CONTINUOUS_MUL THEN CONJ_TAC THEN
                  REWRITE_TAC [o_DEF, LIFT_DROP, LIFT_SUB]) THEN
          SIMP_TAC [ETA_AX, CONTINUOUS_CONST, LINEAR_CONTINUOUS_WITHIN,
                    LINEAR_FSTCART, CONTINUOUS_SUB],
          ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_SUB THEN CONJ_TAC THEN
        GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_WITHIN_COMPOSE THEN
        (CONJ_TAC THENL
          [REPEAT (MATCH_MP_TAC CONTINUOUS_LIFT_POW ORELSE
                  MATCH_MP_TAC CONTINUOUS_LIFT_NORM_COMPOSE ORELSE
                  ((MATCH_MP_TAC CONTINUOUS_ADD ORELSE
                     MATCH_MP_TAC CONTINUOUS_MUL ORELSE
             MATCH_MP_TAC (← REWRITE_RULE [o_DEF] CONTINUOUS_AT_WITHIN_INV) ORELSE
                     MATCH_MP_TAC CONTINUOUS_SUB) THEN
                   CONJ_TAC) THEN
                 REWRITE_TAC [o_DEF, LIFT_SUB, LIFT_CMUL, LIFT_DROP]) THEN
           REWRITE_TAC [CONTINUOUS_CONST, ETA_AX] THEN
           SIMP_TAC [LINEAR_CONTINUOUS_WITHIN,
                     LINEAR_FSTCART, LINEAR_SNDCART] THEN
           ASM_REWRITE_TAC [NORM_EQ_0, SNDCART_PASTECART],
           ALL_TAC]) THEN
        MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
        REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART] THEN
        MATCH_MP_TAC (← MESON [DIFFERENTIABLE_IMP_CONTINUOUS_AT,
                               differentiable]
          (← q r"!f'. (f has_derivative f' x) (at x) /\ ~(det(matrix(f' x)) = &0)
                ==> (f:real^N->real^N) continuous at x")) THEN
        EXISTS_TAC (← q r"(f':real^N->real^N->real^N)") THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        MATCH_MP_TAC (← SET_RULE (← q r"!s. x IN s /\ s SUBSET t ==> x IN t")) THEN
        EXISTS_TAC (← q r"ball(a:real^N,&2 * r)") THEN ASM_REWRITE_TAC [] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN TRY (EXISTS_TAC (← q r"x:real^N")) THEN
        RULE_ASSUM_TAC (REWRITE_RULE [IN_INTERVAL_1, DROP_VEC]) THEN
        ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [← GSYM LIFT_EQ, LIFT_NUM, LIFT_DROP] THEN
        ASM_REWRITE_TAC []]] THEN
   (POP_ASSUM_LIST (K ALL_TAC) THEN REWRITE_TAC [has_derivative_at] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC [← GSYM LIM_NULL, real_div, REAL_INV_MUL] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"n * x * y * z:real = (n * y * z) * x")] THEN
    ONCE_REWRITE_TAC [← VECTOR_ARITH
      (← q r"(a * b) % (x - y):real^N = a % (b % x - b % y)")] THEN
    SUBGOAL_THEN
     (← q r"(f':real^N->real^N) x = norm(x:real^N) / r % f'(r / norm x % x)")
    SUBST1_TAC THENL
     [FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP LINEAR_CMUL th])) THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM VECTOR_MUL_LID] THEN
      REWRITE_TAC [VECTOR_MUL_RCANCEL, VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC [NORM_EQ_0, ← REAL_FIELD
       (← q r"~(x = &0) /\ &0 < r ==> x / r * r / x = &1")],
      ALL_TAC] THEN
    MATCH_MP_TAC LIM_MUL THEN REWRITE_TAC [o_DEF, LIFT_CMUL, real_div] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [VECTOR_MUL_ASSOC] THEN MATCH_MP_TAC LIM_VMUL THEN
      REWRITE_TAC [LIFT_CMUL, o_DEF] THEN REWRITE_TAC [← GSYM LIFT_CMUL] THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [LIFT_CMUL] THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM VECTOR_MUL_LID] THEN
      MATCH_MP_TAC LIM_MUL THEN REWRITE_TAC [o_DEF] THEN CONJ_TAC THENL
       [SUBST1_TAC (← GSYM REAL_INV_1) THEN
        MATCH_MP_TAC (← REWRITE_RULE [o_DEF] LIM_INV) THEN
        CONV_TAC REAL_RAT_REDUCE_CONV,
        MATCH_MP_TAC LIM_NORM] THEN
      MATCH_MP_TAC LIM_CONTINUOUS_SELF_WITHIN THEN
      REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART, DROP_VEC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      SIMP_TAC [LIFT_SUB, LIFT_DROP, CONTINUOUS_SUB, CONTINUOUS_CONST,
                LINEAR_CONTINUOUS_WITHIN, LINEAR_FSTCART, LINEAR_SNDCART],
      ALL_TAC] THEN
    MP_TAC (← VECTOR_ARITH
     (← q r"!k x y. k % (f:real^N->real^N)((a + x) + y) - k % f(a + x):real^N =
              k % (f((a + x) + y) - f a) - k % (f(a + x) - f a)")) THEN
    DISCH_THEN (fun th => ONCE_REWRITE_TAC [th]) THEN
    GEN_REWRITE_TAC LAND_CONV [← VECTOR_ARITH (← q r"x:real^N = &1 % x - &0 % x")] THEN
    SUBGOAL_THEN
     (← q r"!g c. ((\y. inv(drop(fstcart y)) % (g y - a) -
                  c % inv(norm(sndcart y)) % sndcart y)
             --> vec 0)
             (at (pastecart (vec 0) x) within
              interval(vec 0,vec 1) PCROSS ((:real^N) DELETE vec 0))
            ==> ((\y. inv(drop(fstcart y)) % (f(g y) - f a))
                 --> c % (f':real^N->real^N) (inv(norm x) % x))
                (at (pastecart (vec 0) x) within
                 interval(vec 0,vec 1) PCROSS ((:real^N) DELETE vec 0))")
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN
      FIRST_X_ASSUM (MP_TAC o ISPECL
        [← q r"at (pastecart (vec 0:real^1) (x:real^N))
          within (interval(vec 0,vec 1) PCROSS ((:real^N) DELETE vec 0))",
         ← q r"g:real^(1,N)finite_sum->real^N"] o
         MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ_ALT]
        (← REWRITE_RULE [CONJ_ASSOC] LIM_COMPOSE_AT))) THEN
      DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN SIMP_TAC [o_DEF] THEN
      REWRITE_TAC [VECTOR_SUB_REFL] THEN
      FIRST_ASSUM (SUBST1_TAC o MATCH_MP LINEAR_0) THEN
      REWRITE_TAC [VECTOR_SUB_REFL, VECTOR_ADD_RID] THEN
      REWRITE_TAC [VECTOR_MUL_RZERO, EVENTUALLY_TRUE] THEN ANTS_TAC THENL
       [ONCE_REWRITE_TAC [LIM_NULL] THEN
        FIRST_ASSUM (MP_TAC o ISPECL
         [← q r"\y:real^(1,N)finite_sum. drop(fstcart y)",
          ← q r"&0"] o
          MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ_ALT] LIM_MUL)) THEN
        REWRITE_TAC [o_DEF, o_DEF, LIFT_NUM, VECTOR_MUL_LZERO, LIFT_DROP] THEN
        ANTS_TAC THENL
         [MATCH_MP_TAC LIM_CONTINUOUS_SELF_WITHIN THEN
          REWRITE_TAC [FSTCART_PASTECART, ETA_AX] THEN
          SIMP_TAC [LINEAR_CONTINUOUS_WITHIN, LINEAR_FSTCART],
          MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] LIM_TRANSFORM) THEN
          REWRITE_TAC [VECTOR_SUB_LDISTRIB, VECTOR_MUL_ASSOC] THEN
          ONCE_REWRITE_TAC [← VECTOR_ARITH
           (← q r"(g' - a' - n) - (g - a):real^N = ((g' - g) - (a' - a)) + --n")] THEN
          MATCH_MP_TAC LIM_NULL_ADD THEN CONJ_TAC THENL
           [MATCH_MP_TAC LIM_NULL_SUB THEN CONJ_TAC THEN
            MATCH_MP_TAC LIM_EVENTUALLY THEN
            REWRITE_TAC [EVENTUALLY_WITHIN] THEN
            EXISTS_TAC (← q r"&1") THEN REWRITE_TAC [REAL_LT_01] THEN
            REWRITE_TAC [FORALL_IN_PCROSS, IN_INTERVAL_1, DROP_VEC, IMP_CONJ] THEN
            SIMP_TAC [FSTCART_PASTECART, REAL_MUL_RINV, REAL_LT_IMP_NZ] THEN
            REPEAT STRIP_TAC THEN CONV_TAC (fun t => VECTOR_ARITH t),
            MATCH_MP_TAC LIM_NULL_COMPARISON THEN
            EXISTS_TAC (← q r"\x:real^(1,N)finite_sum. abs c * norm(fstcart x)") THEN
            REWRITE_TAC [NORM_MUL, NORM_NEG] THEN CONJ_TAC THENL
             [REWRITE_TAC [EVENTUALLY_WITHIN_TOPOLOGICAL] THEN
              EXISTS_TAC (← q r"(:real^1) PCROSS ((:real^N) DELETE vec 0)") THEN
              SIMP_TAC [OPEN_PCROSS, OPEN_UNIV, OPEN_DELETE] THEN
              ASM_REWRITE_TAC [PASTECART_IN_PCROSS, IN_DELETE, IN_UNIV] THEN
              REWRITE_TAC [FORALL_IN_PCROSS, IN_INTER, IMP_CONJ] THEN
              REWRITE_TAC [IN_DELETE, IN_UNIV, FSTCART_PASTECART] THEN
              REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
              REWRITE_TAC [SNDCART_PASTECART, ← GSYM REAL_MUL_ASSOC] THEN
              SIMP_TAC [REAL_MUL_LINV, REAL_MUL_RID, NORM_EQ_0] THEN
              REWRITE_TAC [NORM_1, REAL_MUL_SYM, REAL_LE_REFL],
              REWRITE_TAC [LIFT_CMUL] THEN MATCH_MP_TAC LIM_NULL_CMUL THEN
              MATCH_MP_TAC LIM_CONTINUOUS_SELF_WITHIN THEN
              REWRITE_TAC [FSTCART_PASTECART, NORM_0, LIFT_NUM] THEN
              MATCH_MP_TAC CONTINUOUS_LIFT_NORM_COMPOSE THEN
              SIMP_TAC [LINEAR_FSTCART, LINEAR_CONTINUOUS_WITHIN]]]],
        FIRST_ASSUM (MP_TAC o
          SPEC (← q r"\y. inv(drop(fstcart y)) %
                    ((g:real^(1,N)finite_sum->real^N) y - a) -
                    c % inv(norm x) % x") o
          MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ_ALT] LIM_TRANSFORM)) THEN
        REWRITE_TAC [] THEN ANTS_TAC THENL
         [ALL_TAC,
          REWRITE_TAC [← GSYM LIM_NULL] THEN
          DISCH_THEN (MP_TAC o MATCH_MP LIM_NORM) THEN REWRITE_TAC [IMP_IMP] THEN
          DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE [o_DEF] LIM_MUL)) THEN
          REWRITE_TAC [VECTOR_MUL_RZERO] THEN
          DISCH_THEN (MP_TAC o
            SPEC (← q r"\y. inv(norm(fstcart(y:real^(1,N)finite_sum))) %
                      (f(g y) - f a - (f':real^N->real^N) (g y - a))") o
            MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT] LIM_TRANSFORM_EVENTUALLY)) THEN
          REWRITE_TAC [] THEN ANTS_TAC THENL
           [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
            X_GEN_TAC (← q r"y:real^(1,N)finite_sum") THEN
            ASM_CASES_TAC (← q r"(g:real^(1,N)finite_sum->real^N) y = a") THEN
            ASM_REWRITE_TAC [] THENL
             [REWRITE_TAC [VECTOR_SUB_REFL] THEN
              FIRST_ASSUM (SUBST1_TAC o MATCH_MP LINEAR_0) THEN
              REWRITE_TAC [VECTOR_SUB_REFL, VECTOR_ADD_RID] THEN
              REWRITE_TAC [VECTOR_MUL_RZERO],
              REWRITE_TAC [NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
              REWRITE_TAC [VECTOR_MUL_ASSOC] THEN
              BINOP_TAC THENL [ALL_TAC, CONV_TAC (fun t => VECTOR_ARITH t)] THEN
              REWRITE_TAC [← GSYM NORM_1] THEN
              MATCH_MP_TAC (← REAL_FIELD (← q r"~(y = &0) ==> (x * y) * inv y = x")) THEN
              ASM_REWRITE_TAC [NORM_EQ_0, VECTOR_SUB_EQ]],
            GEN_REWRITE_TAC LAND_CONV [LIM_NULL_NORM] THEN
            REWRITE_TAC [NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
            REWRITE_TAC [NORM_1, ← GSYM REAL_ABS_INV] THEN
            REWRITE_TAC [← GSYM NORM_MUL, ← GSYM LIM_NULL_NORM] THEN
            GEN_REWRITE_TAC RAND_CONV [LIM_NULL] THEN
            MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] LIM_TRANSFORM) THEN
            REWRITE_TAC [← VECTOR_ARITH
             (← q r"c % (x - y - z) - (c % (x - y) - d):real^N = --(c % z - d)")] THEN
            REWRITE_TAC [LIM_NULL_NEG, ← GSYM LIM_NULL] THEN
            FIRST_ASSUM (fun th => tactic_of do
              pure (REWRITE_TAC [← GSYM (← MATCH_MP LINEAR_CMUL th)])) THEN
            MATCH_MP_TAC LIM_LINEAR THEN ASM_REWRITE_TAC [] THEN
            ONCE_REWRITE_TAC [LIM_NULL] THEN REWRITE_TAC [] THEN
            FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT]
              LIM_TRANSFORM))]] THEN
        REWRITE_TAC [← VECTOR_ARITH (← q r"(a - x) - (a - y):real^N = --(x - y)")] THEN
        REWRITE_TAC [LIM_NULL_NEG, ← GSYM VECTOR_SUB_LDISTRIB] THEN
        MATCH_MP_TAC LIM_NULL_CMUL THEN REWRITE_TAC [← GSYM LIM_NULL] THEN
        MATCH_MP_TAC LIM_CONTINUOUS_SELF_WITHIN THEN
        REWRITE_TAC [SNDCART_PASTECART] THEN
        MATCH_MP_TAC CONTINUOUS_MUL THEN
        SIMP_TAC [o_DEF, LINEAR_SNDCART, LINEAR_CONTINUOUS_WITHIN] THEN
        MATCH_MP_TAC (← REWRITE_RULE [o_DEF] CONTINUOUS_AT_WITHIN_INV) THEN
        SIMP_TAC [CONTINUOUS_LIFT_NORM_COMPOSE, LINEAR_SNDCART,
                  LINEAR_CONTINUOUS_WITHIN] THEN
        ASM_REWRITE_TAC [SNDCART_PASTECART, NORM_EQ_0]],
      ALL_TAC] THEN
    MATCH_MP_TAC LIM_SUB THEN CONJ_TAC THEN
    REWRITE_TAC [← GSYM VECTOR_MUL_ASSOC] THEN
    FIRST_ASSUM (fun th => tactic_of do pure (ONCE_REWRITE_TAC [← MATCH_MP LINEAR_CMUL th])) THEN
    REWRITE_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LZERO] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [← GSYM VECTOR_ADD_ASSOC, VECTOR_ADD_SUB] THEN
    REWRITE_TAC [VECTOR_ADD_LDISTRIB, VECTOR_MUL_ASSOC, ← GSYM REAL_MUL_ASSOC] THEN
    (SUBGOAL_THEN (← q r"!z. z IN interval(vec 0,vec 1) PCROSS ((:real^N) DELETE vec 0)
                       ==> ~(drop(fstcart z) = &0)")
     MP_TAC THENL
      [SIMP_TAC [FORALL_IN_PCROSS, IN_INTERVAL_1, DROP_VEC, REAL_LT_IMP_NZ,
                 FSTCART_PASTECART],
       SIMP_TAC [← MESON [DROP_EQ, DROP_VEC] (← q r"drop x = &0 <=> x = vec 0"),
        ← REAL_FIELD (← q r"~(y = &0) ==> inv y * y * z = z"),
        ← REAL_FIELD (← q r"~(y = &0) ==> inv y * (&3 * y pow 2 - &2 * y pow 3) =
                                  y * (&3 - &2 * y)")] THEN
      DISCH_THEN (K ALL_TAC)])
    THENL
     [REWRITE_TAC [← VECTOR_ARITH (← q r"(a + b) - c:real^N = (b - c) + a")] THEN
      MATCH_MP_TAC LIM_NULL_ADD THEN CONJ_TAC THENL
       [REWRITE_TAC [← VECTOR_ARITH
         (← q r"(a * x * y) % z - (x * y) % z:real^N = (a - &1) % x % y % z")] THEN
        REWRITE_TAC [← VECTOR_ARITH (← q r"(&1 - a - &1) % x:real^N = --(a % x)")] THEN
        MATCH_MP_TAC LIM_NULL_COMPARISON THEN
        EXISTS_TAC (← q r"\x:real^(1,N)finite_sum. abs r * norm(fstcart x)") THEN
        REWRITE_TAC [NORM_MUL, NORM_NEG] THEN CONJ_TAC THENL
         [REWRITE_TAC [EVENTUALLY_WITHIN_TOPOLOGICAL] THEN
          EXISTS_TAC (← q r"(:real^1) PCROSS ((:real^N) DELETE vec 0)") THEN
          SIMP_TAC [OPEN_PCROSS, OPEN_UNIV, OPEN_DELETE] THEN
          ASM_REWRITE_TAC [PASTECART_IN_PCROSS, IN_DELETE, IN_UNIV] THEN
          REWRITE_TAC [FORALL_IN_PCROSS, IN_INTER, IMP_CONJ] THEN
          REWRITE_TAC [IN_DELETE, IN_UNIV, FSTCART_PASTECART] THEN
          REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
          REWRITE_TAC [SNDCART_PASTECART, ← GSYM REAL_MUL_ASSOC] THEN
          SIMP_TAC [REAL_MUL_LINV, REAL_MUL_RID, NORM_EQ_0] THEN
          REWRITE_TAC [NORM_1, REAL_MUL_SYM, REAL_LE_REFL],
          REWRITE_TAC [LIFT_CMUL] THEN MATCH_MP_TAC LIM_NULL_CMUL THEN
          MATCH_MP_TAC LIM_CONTINUOUS_SELF_WITHIN THEN
          REWRITE_TAC [FSTCART_PASTECART, NORM_0, LIFT_NUM] THEN
          MATCH_MP_TAC CONTINUOUS_LIFT_NORM_COMPOSE THEN
          SIMP_TAC [LINEAR_FSTCART, LINEAR_CONTINUOUS_WITHIN]],
        ALL_TAC],
      REWRITE_TAC [REAL_MUL_LZERO, VECTOR_MUL_LZERO, VECTOR_SUB_RZERO]] THEN
    MATCH_MP_TAC LIM_NULL_VMUL THEN
    MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN EXISTS_TAC
     (← q r"\y:real^(1,N)finite_sum.
        lift(&3 * drop(fstcart y) - &2 * drop(fstcart y) pow 2)") THEN
    REWRITE_TAC [EVENTUALLY_WITHIN, FORALL_PASTECART, LIFT_EQ] THEN
    REWRITE_TAC [PASTECART_IN_PCROSS, IN_INTERVAL_1, DROP_VEC] THEN
    SIMP_TAC [FSTCART_PASTECART, ← REAL_FIELD
     (← q r"&0 < x ==> inv x * (&3 * x pow 2 - &2 * x pow 3) =
                 &3 * x - &2 * x pow 2")] THEN
    REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN EXISTS_TAC (← q r"&1") THEN
    REWRITE_TAC [REAL_LT_01] THEN (CONJ_TAC THENL [REAL_ARITH_TAC, ALL_TAC]) THEN
    MATCH_MP_TAC LIM_CONTINUOUS_SELF_WITHIN THEN
    REWRITE_TAC [FSTCART_PASTECART, DROP_VEC, ← GSYM DROP_EQ, LIFT_DROP] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [LIFT_SUB, LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_CMUL THEN
    TRY (MATCH_MP_TAC CONTINUOUS_LIFT_POW) THEN
    REWRITE_TAC [LIFT_DROP, ETA_AX] THEN
    SIMP_TAC [LINEAR_CONTINUOUS_WITHIN, LINEAR_FSTCART, LINEAR_SNDCART]))

  pure { JACOBIAN_SIGN_INVARIANCE }

/- ------------------------------------------------------------------------- -/
/- Invertible derivative continuous at a point implies local injectivity;    -/
/- more conventional "C1" inverse function theorems.                         -/
/- (derivatives.ml 4429-4662)                                                -/
/- ------------------------------------------------------------------------- -/

structure DVK where
  HAS_DERIVATIVE_LOCALLY_INJECTIVE : thm
  INVERSE_FUNCTION_THEOREM_C1_POINTWISE : thm
  INVERSE_FUNCTION_C1 : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupDVK [HolBase] (D : DerivativesDeps) (BDVA : DVA) (BDVB : DVB) (BDVD : DVD) (BDVI : DVI) : ExceptT String IO DVK := do
  -- @@SCOPE BEGIN
  let { differentiable, has_derivative, HAS_DERIVATIVE_AT_WITHIN, HAS_DERIVATIVE_CONST,
        HAS_DERIVATIVE_ID, HAS_DERIVATIVE_LINEAR, HAS_DERIVATIVE_SUB, .. } := BDVA
  let { DIFF_CHAIN_WITHIN, DIFFERENTIABLE_IMP_CONTINUOUS_AT, .. } := BDVB
  let { DIFFERENTIABLE_BOUND, .. } := BDVD
  let { INVERSE_FUNCTION_THEOREM, .. } := BDVI
  let { ARITH, ARITH_EQ, CONJ_ASSOC, ETA_AX, .. } := D.dg.pt.cvx.core1
  let { FUN_EQ_THM, IMP_CONJ, IN_DELETE, INTER_SUBSET, .. } := D.dg.pt.cvx.core2
  let { I_THM, IN_INTER, LEFT_IMP_EXISTS_THM, MONO_EXISTS, MONO_FORALL, .. } :=
        D.dg.pt.cvx.core3
  let { REAL_LE_RDIV_EQ, REAL_LE_TRANS, REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_MIN, .. } :=
        D.dg.pt.cvx.core4
  let { REAL_MUL_SYM, REAL_OF_NUM_LT, RIGHT_IMP_FORALL_THM, SUBSET, .. } :=
        D.dg.pt.cvx.core5
  let { o_DEF, o_THM, real_div, .. } := D.dg.pt.cvx.core6
  let { DIST_LIFT, .. } := D.dg.pt.cvx.vec1
  let { LINEAR_0, LINEAR_SUB, MATRIX_COMPOSE, MATRIX_WORKS, .. } := D.dg.pt.cvx.vec2
  let { NORM_LE_0, .. } := D.dg.pt.cvx.vec3
  let { VECTOR_NEG_SUB, VECTOR_SUB_EQ, VECTOR_SUB_REFL, VECTOR_SUB_RZERO, .. } :=
        D.dg.pt.cvx.vec4
  let { EVENTUALLY_TRUE, .. } := D.dg.pt.cvx.met
  let { CENTRE_IN_BALL, .. } := D.dg.pt.cvx.top1
  let { IN_BALL, OPEN_BALL, OPEN_CONTAINS_BALL, .. } := D.dg.pt.cvx.top4
  let { homeomorphism, OPEN_INTER, .. } := D.dg.pt.cvx.top5
  let { ASM_MESON_TAC, MESON, REAL_ARITH, REAL_ARITH_TAC, SET_TAC, .. } := D.dg.pt.cvx
  let { VEC_EQ, .. } := D.dg.pt.qvec
  let { CONVEX_BALL, .. } := D.dg.pt.qcvx2
  let { REAL_LT_TRANS, .. } := D.dg.qsession
  let { tendsto, .. } := D.dg.qtopology2
  let { MATRIX_I, .. } := D.dg.qvec
  let { REAL_ABS_NZ, .. } := D.qsession
  let { CONTINUOUS_AT, EVENTUALLY_AT_TOPOLOGICAL, .. } := D.qtopology1
  let { LIM_COMPOSE_AT, LIM_LIFT_DET, LIM_MATRIX_COMPONENTWISE, LIM_MATRIX_INV,
        LIM_TRANSFORM_WITHIN_OPEN, .. } := D.qtopology2
  let { LINEAR_COMPOSE_SUB, MATRIX_INV_UNIQUE_LEFT, ONORM_COMPOSE, ONORM_NEG, ONORM_POS_LT,
        .. } := D.qvec
  -- @@SCOPE END

  let HAS_DERIVATIVE_LOCALLY_INJECTIVE ← prove
   r"!f:real^M->real^N f' g' s a.
        a IN s /\ open s /\ linear g' /\ (g' o f'(a) = I) /\
        (!x. x IN s ==> (f has_derivative f'(x)) (at x)) /\
        (!e. &0 < e
             ==> ?d. &0 < d /\
                     !x. dist(a,x) < d ==> onorm(\v. f'(x) v - f'(a) v) < e)
        ==> ?t. a IN t /\ open t /\
                !x x'. x IN t /\ x' IN t /\ (f x' = f x) ==> (x' = x)"
   (REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"&0 < onorm(g':real^N->real^M)") ASSUME_TAC THENL
     [ASM_SIMP_TAC [ONORM_POS_LT] THEN ASM_MESON_TAC [VEC_EQ, ARITH_EQ],
      ALL_TAC] THEN
    ABBREV_TAC (← q r"k = &1 / onorm(g':real^N->real^M) / &2") THEN
    SUBGOAL_THEN
     (← q r"?d. &0 < d /\ ball(a,d) SUBSET s /\
          !x. x IN ball(a,d)
              ==> onorm(\v. (f':real^M->real^M->real^N)(x) v - f'(a) v) < k")
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"k:real")) THEN EXPAND_TAC "k" THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"d1:real") STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"a:real^M")) THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [SUBSET, IN_BALL] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"d2:real")) THEN
      EXISTS_TAC (← q r"min d1 d2") THEN ASM_REWRITE_TAC [REAL_LT_MIN, IN_BALL] THEN
      ASM_MESON_TAC [REAL_LT_TRANS],
      ALL_TAC] THEN
    EXISTS_TAC (← q r"ball(a:real^M,d)") THEN
    ASM_SIMP_TAC [OPEN_BALL, CENTRE_IN_BALL] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:real^M", ← q r"x':real^M"] THEN STRIP_TAC THEN
    ABBREV_TAC (← q r"ph = \w. w - g'(f(w) - (f:real^M->real^N)(x))") THEN
    SUBGOAL_THEN (← q r"norm((ph:real^M->real^M) x' - ph x) <= norm(x' - x) / &2")
    MP_TAC THENL
     [ALL_TAC,
      EXPAND_TAC "ph" THEN ASM_REWRITE_TAC [VECTOR_SUB_REFL] THEN
      FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP LINEAR_0 th])) THEN
      ONCE_REWRITE_TAC [← GSYM VECTOR_SUB_EQ] THEN
      REWRITE_TAC [VECTOR_SUB_RZERO, ← GSYM NORM_LE_0] THEN REAL_ARITH_TAC] THEN
    SUBGOAL_THEN
     (← q r"!u v:real^M. u IN ball(a,d) /\ v IN ball(a,d)
                   ==> norm(ph u - ph v :real^M) <= norm(u - v) / &2")
     (fun th => ASM_SIMP_TAC [th]) THEN
    REWRITE_TAC [real_div] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    MATCH_MP_TAC DIFFERENTIABLE_BOUND THEN
    REWRITE_TAC [CONVEX_BALL, OPEN_BALL] THEN
    EXISTS_TAC (← q r"\x v. v - g'((f':real^M->real^M->real^N) x v)") THEN
    CONJ_TAC THEN X_GEN_TAC (← q r"u:real^M") THEN DISCH_TAC THEN REWRITE_TAC [] THENL
     [EXPAND_TAC "ph" THEN
      MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC [HAS_DERIVATIVE_ID] THEN
      FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP LINEAR_SUB th])) THEN
      GEN_REWRITE_TAC (RATOR_CONV o BINDER_CONV) [← GSYM VECTOR_SUB_RZERO] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC [HAS_DERIVATIVE_CONST] THEN
      ONCE_REWRITE_TAC [← GSYM o_DEF] THEN MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN
      ONCE_REWRITE_TAC [ETA_AX] THEN
      ASM_MESON_TAC [HAS_DERIVATIVE_LINEAR, SUBSET, HAS_DERIVATIVE_AT_WITHIN],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"(\w. w - g'((f':real^M->real^M->real^N) u w)) =
       g' o (\w. f' a w - f' u w)")
    SUBST1_TAC THENL
     [REWRITE_TAC [FUN_EQ_THM, o_THM] THEN ASM_MESON_TAC [LINEAR_SUB],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"linear(\w. f' a w - (f':real^M->real^M->real^N) u w)")
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN ONCE_REWRITE_TAC [ETA_AX] THEN
      ASM_MESON_TAC [has_derivative, SUBSET, CENTRE_IN_BALL],
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     (← q r"onorm(g':real^N->real^M) *
      onorm(\w. f' a w - (f':real^M->real^M->real^N) u w)") THEN
    ASM_SIMP_TAC [ONORM_COMPOSE] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN ASM_SIMP_TAC [← GSYM REAL_LE_RDIV_EQ] THEN
    REWRITE_TAC [real_div, ← REAL_ARITH (← q r"inv(&2) * x = (&1 * x) * inv(&2)")] THEN
    ASM_REWRITE_TAC [← GSYM real_div] THEN
    SUBGOAL_THEN (← q r"onorm(\w. (f':real^M->real^M->real^N) a w - f' u w) =
                  onorm(\w. f' u w - f' a w)")
     (fun th => ASM_SIMP_TAC [th, REAL_LT_IMP_LE]) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [← GSYM VECTOR_NEG_SUB] THEN
    REWRITE_TAC [ONORM_NEG])

  let INVERSE_FUNCTION_THEOREM_C1_POINTWISE ← prove
   r"!f:real^N->real^N f' s a.
        open s /\ a IN s /\
        (!x. x IN s ==> (f has_derivative f'(x)) (at x)) /\
        ~(det(matrix(f' a)) = &0) /\ (!h. (\x. f' x h) continuous at a)
        ==> ?t u g g'.
                open t /\ a IN t /\ t SUBSET s /\ open u /\ f a IN u /\
                homeomorphism (t,u) (f,g) /\
                (!x. x IN t
                     ==> (f has_derivative f' x) (at x) /\
                         f'(x) o g'(f x) = I /\ g'(f x) o f'(x) = I) /\
                (!y. y IN u
                     ==> (g has_derivative g' y) (at y) /\
                         f'(g y) o g' y = I /\ g' y o f'(g y) = I) /\
                (!x. x IN t /\ (!h. (\y. f' y h) continuous at x)
                       ==> (!h. (\z. g' z h) continuous at (f x)))"
   (REWRITE_TAC [CONTINUOUS_AT] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"?s'. a IN s' /\ s' SUBSET s /\ open s' /\
           !x. x IN s' ==> ~(det(matrix((f':real^N->real^N->real^N) x)) = &0)")
    STRIP_ASSUME_TAC THENL
     [MP_TAC (← ISPECL
       [← q r"\x. matrix((f':real^N->real^N->real^N) x)",
        ← q r"matrix((f':real^N->real^N->real^N) a)", ← q r"at(a:real^N)"]
       LIM_LIFT_DET) THEN
      REWRITE_TAC [← GSYM LIM_MATRIX_COMPONENTWISE] THEN ANTS_TAC THENL
       [X_GEN_TAC (← q r"h:real^N") THEN MATCH_MP_TAC LIM_TRANSFORM_WITHIN_OPEN THEN
        EXISTS_TAC (← q r"\a. (f':real^N->real^N->real^N) a h") THEN
        EXISTS_TAC (← q r"s:real^N->bool") THEN ASM_REWRITE_TAC [] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [has_derivative]) THEN
        ASM_SIMP_TAC [MATRIX_WORKS],
        REWRITE_TAC [tendsto] THEN DISCH_THEN (MP_TAC o SPEC
         (← q r"abs(det(matrix((f':real^N->real^N->real^N) a)))")) THEN
        ASM_REWRITE_TAC [← GSYM REAL_ABS_NZ, EVENTUALLY_AT_TOPOLOGICAL] THEN
        REWRITE_TAC [DIST_LIFT, IN_DELETE, LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC (← q r"u:real^N->bool") THEN STRIP_TAC THEN
        EXISTS_TAC (← q r"s INTER u:real^N->bool") THEN
        ASM_SIMP_TAC [IN_INTER, OPEN_INTER, INTER_SUBSET] THEN
        X_GEN_TAC (← q r"x:real^N") THEN STRIP_TAC THEN
        ASM_CASES_TAC (← q r"x:real^N = a") THEN ASM_REWRITE_TAC [] THEN
        REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real^N"))) THEN
        ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC],
      MP_TAC (← ISPECL [← q r"f:real^N->real^N", ← q r"f':real^N->real^N->real^N",
                        ← q r"a:real^N", ← q r"s':real^N->bool"]
          INVERSE_FUNCTION_THEOREM) THEN
      ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      MAP_EVERY (fun t => MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC t)
       [← q r"t:real^N->bool", ← q r"u:real^N->bool", ← q r"g:real^N->real^N",
        ← q r"g':real^N->real^N->real^N"] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      X_GEN_TAC (← q r"x:real^N") THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      TRANS_TAC (← TAUT (← q r"!q. (p ==> q) /\ (q ==> r) ==> p ==> r"))
       (← q r"!h:real^N. ((\y. matrix_inv(matrix ((f':real^N->real^N->real^N) y)) ** h)
                     --> matrix_inv(matrix(f' x)) ** h) (at x)") THEN
      CONJ_TAC THENL
       [DISCH_THEN (fun th => MATCH_MP_TAC LIM_MATRIX_INV THEN MP_TAC th) THEN
        MATCH_MP_TAC (← TAUT (← q r"r /\ (p ==> q) ==> p ==> q /\ r")) THEN CONJ_TAC THENL
         [ASM SET_TAC [], ALL_TAC] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"h:real^N") THEN
        MATCH_MP_TAC (← MESON []
         (← q r"m = l /\ ((x --> l) net ==> (y --> l) net)
          ==> (x --> l) net ==> (y --> m) net")) THEN
        CONJ_TAC THENL
         [ALL_TAC,
          MATCH_MP_TAC (← ONCE_REWRITE_RULE [IMP_CONJ]
           (← REWRITE_RULE [CONJ_ASSOC] LIM_TRANSFORM_WITHIN_OPEN)) THEN
          EXISTS_TAC (← q r"t:real^N->bool") THEN ASM_REWRITE_TAC [] THEN
          X_GEN_TAC (← q r"y:real^N") THEN STRIP_TAC THEN CONV_TAC SYM_CONV] THEN
        MATCH_MP_TAC (← REWRITE_RULE [RIGHT_IMP_FORALL_THM] MATRIX_WORKS) THEN
        ASM_MESON_TAC [has_derivative],
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"h:real^N") THEN DISCH_TAC THEN
        MATCH_MP_TAC LIM_TRANSFORM_WITHIN_OPEN THEN
        EXISTS_TAC (← q r"(\z. (g':real^N->real^N->real^N) (f z) h) o
                    (g:real^N->real^N)") THEN
        EXISTS_TAC (← q r"u:real^N->bool") THEN ASM_REWRITE_TAC [o_THM, CONJ_ASSOC] THEN
        CONJ_TAC THENL
         [RULE_ASSUM_TAC (REWRITE_RULE [homeomorphism]) THEN ASM SET_TAC [],
          ALL_TAC] THEN
        MATCH_MP_TAC LIM_COMPOSE_AT THEN EXISTS_TAC (← q r"x:real^N") THEN
        SIMP_TAC [EVENTUALLY_TRUE] THEN CONJ_TAC THENL
         [SUBGOAL_THEN (← q r"x = (g:real^N->real^N)(f x)")
           (fun th => GEN_REWRITE_TAC LAND_CONV [th])
          THENL
           [RULE_ASSUM_TAC (REWRITE_RULE [homeomorphism]) THEN ASM SET_TAC [],
            REWRITE_TAC [← GSYM CONTINUOUS_AT] THEN
            MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
            REWRITE_TAC [differentiable] THEN
            RULE_ASSUM_TAC (REWRITE_RULE [homeomorphism]) THEN ASM SET_TAC []],
          FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← MESON []
           (← q r"(x --> l) net
            ==> m = l /\ ((x --> l) net ==> (y --> l) net)
                ==> (y --> m) net"))) THEN
          CONJ_TAC THENL
           [CONV_TAC SYM_CONV,
            MATCH_MP_TAC (← ONCE_REWRITE_RULE [IMP_CONJ]
             (← REWRITE_RULE [CONJ_ASSOC] LIM_TRANSFORM_WITHIN_OPEN)) THEN
            EXISTS_TAC (← q r"t:real^N->bool") THEN ASM_REWRITE_TAC [] THEN
            X_GEN_TAC (← q r"y:real^N") THEN STRIP_TAC] THEN
          W (MP_TAC o PART_MATCH (rand o rand)
               (← REWRITE_RULE [RIGHT_IMP_FORALL_THM] MATRIX_WORKS) o
               rand o snd) THEN
          (ANTS_TAC THENL
            [RULE_ASSUM_TAC (REWRITE_RULE [homeomorphism, has_derivative]) THEN
             ASM SET_TAC [],
             DISCH_THEN (SUBST1_TAC o SYM)]) THEN
          AP_THM_TAC THEN AP_TERM_TAC THEN
          MATCH_MP_TAC MATRIX_INV_UNIQUE_LEFT THEN
          W (MP_TAC o PART_MATCH (rand o rand) MATRIX_COMPOSE o lhand o snd) THEN
          (ANTS_TAC THENL
            [RULE_ASSUM_TAC (REWRITE_RULE [homeomorphism, has_derivative]) THEN
             ASM SET_TAC [],
             DISCH_THEN (SUBST1_TAC o SYM) THEN
             ASM_SIMP_TAC [MATRIX_I]])]]])

  let INVERSE_FUNCTION_C1 ← prove
   r"!f:real^N->real^N f' s a.
        open s /\ a IN s /\
        (!x. x IN s
             ==> (f has_derivative f'(x)) (at x) /\
                 ((!h. (\y. f' y h) continuous at x))) /\
        ~(det(matrix(f' a)) = &0)
        ==> ?t u g g'.
                open t /\ a IN t /\ t SUBSET s /\ open u /\ f a IN u /\
                homeomorphism (t,u) (f,g) /\
                (!x. x IN t
                     ==> (f has_derivative f' x) (at x) /\
                         f'(x) o g'(f x) = I /\ g'(f x) o f'(x) = I) /\
                (!y. y IN u
                     ==> (g has_derivative g' y) (at y) /\
                         f'(g y) o g' y = I /\ g' y o f'(g y) = I) /\
                (!x. x IN t ==> (!h. (\z. g' z h) continuous at (f x)))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^N->real^N", ← q r"f':real^N->real^N->real^N",
                      ← q r"s:real^N->bool", ← q r"a:real^N"]
          INVERSE_FUNCTION_THEOREM_C1_POINTWISE) THEN
    ASM_SIMP_TAC [] THEN
    REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC [])

  pure { HAS_DERIVATIVE_LOCALLY_INJECTIVE, INVERSE_FUNCTION_THEOREM_C1_POINTWISE,
         INVERSE_FUNCTION_C1 }

/- ------------------------------------------------------------------------- -/
/- Hadamard-style global inverse function theorem; localized variants on     -/
/- subspaces and affine sets.  (derivatives.ml 4663-5143)                    -/
/- ------------------------------------------------------------------------- -/

structure DVL where
  INVERSE_FUNCTION_THEOREM_GLOBAL : thm
  INVERSE_FUNCTION_THEOREM_SUBSPACE : thm
  INVERSE_FUNCTION_THEOREM_AFFINE : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupDVL [HolBase] (D : DerivativesDeps) (BDVA : DVA) (BDVB : DVB) (BDVE : DVE) (BDVH : DVH) (BDVI : DVI) : ExceptT String IO DVL := do
  -- @@SCOPE BEGIN
  let { has_derivative, HAS_DERIVATIVE_ADD, HAS_DERIVATIVE_AT_WITHIN, HAS_DERIVATIVE_CONST,
        HAS_DERIVATIVE_ID, HAS_DERIVATIVE_LINEAR, HAS_DERIVATIVE_WITHIN_OPEN,
        HAS_DERIVATIVE_WITHIN_OPEN_IN, .. } := BDVA
  let { DIFF_CHAIN_WITHIN, HAS_DERIVATIVE_WITHIN_SUBSET, .. } := BDVB
  let { DIFFERENTIABLE_IMP_OPEN_MAP, HAS_DERIVATIVE_INVERSE_STRONG,
        HAS_DERIVATIVE_INVERSE_WITHIN, .. } := BDVE
  let { GATEAUX_DERIVATIVE, GATEAUX_DERIVATIVE_WITHIN, .. } := BDVH
  let { INVERSE_FUNCTION_THEOREM, .. } := BDVI
  let { AND_FORALL_THM, CONJ_ASSOC, ETA_AX, FORALL_IN_GSPEC, .. } := D.dg.pt.cvx.core1
  let { FORALL_IN_IMAGE, FUN_EQ_THM, IMAGE_ID, IMAGE_o, IMAGE_SUBSET, IMP_CONJ,
        IMP_CONJ_ALT, IN_DELETE, INTER_SUBSET, .. } := D.dg.pt.cvx.core2
  let { I_THM, IN_ELIM_THM, IN_INTER, IN_UNIV, LE_REFL, LEFT_IMP_EXISTS_THM, MONO_EXISTS,
        MONO_FORALL, .. } := D.dg.pt.cvx.core3
  let { RIGHT_EXISTS_AND_THM, RIGHT_EXISTS_IMP_THM, RIGHT_IMP_EXISTS_THM, SIMPLE_IMAGE,
        SKOLEM_THM, SUBSET, SUBSET_REFL, SUBSET_TRANS, .. } := D.dg.pt.cvx.core5
  let { o_DEF, o_THM, UNIV_GSPEC, .. } := D.dg.pt.cvx.core6
  let { DROP_VEC, FORALL_LIFT, LIFT_DROP, LINEAR_ADD, LINEAR_COMPOSE, LINEAR_COMPOSE_ADD,
        LINEAR_SUB, .. } := D.dg.pt.cvx.vec2
  let { SUBSPACE_ADD, SUBSPACE_IMP_NONEMPTY, SUBSPACE_MUL, SUBSPACE_SUB, .. } :=
        D.dg.pt.cvx.vec3
  let { VECTOR_ADD_LID, VECTOR_ADD_RID, VECTOR_ADD_SUB, VECTOR_MUL_LID, VECTOR_MUL_LZERO,
        VECTOR_SUB_REFL, .. } := D.dg.pt.cvx.vec4
  let { EVENTUALLY_MONO, OPEN_IN_IMP_SUBSET, SUBTOPOLOGY_UNIV, .. } := D.dg.pt.cvx.met
  let { CLOSED_SUBSPACE, CLOSEST_POINT_IN_SET, CLOSEST_POINT_SELF, .. } := D.dg.pt.cvx.top1
  let { CONTINUOUS_ON_ADD, CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_CONST,
        CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN, CONTINUOUS_ON_ID,
        CONTINUOUS_OPEN_IN_PREIMAGE_GEN, .. } := D.dg.pt.cvx.top3
  let { HOMEOMORPHISM, HOMEOMORPHISM_OF_SUBSETS, LIM_IN_CLOSED_SET, LINEAR_CONTINUOUS_ON, ..
        } := D.dg.pt.cvx.top4
  let { homeomorphism, OPEN_IN, OPEN_IN_OPEN_EQ, OPEN_IN_OPEN_INTER, OPEN_SUBSET, OPEN_UNIV,
        .. } := D.dg.pt.cvx.top5
  let { ASM_MESON_TAC, MESON, MESON_TAC, SET_RULE, SET_TAC, VECTOR_ARITH, .. } :=
        D.dg.pt.cvx
  let { CLOSED_IN_REFL, .. } := D.dg.pt.qtop
  let { INVERTIBLE_DET_NZ, .. } := D.dg.qdet
  let { CLOSED_IN_IMP_SUBSET, .. } := D.dg.qmetric
  let { I_DEF, I_O_ID, .. } := D.dg.qsession
  let { EVENTUALLY_IN_OPEN, .. } := D.dg.qtopology1
  let { LINEAR_ID, MATRIX_INVERTIBLE, .. } := D.dg.qvec
  let { AFFINE_DIFFS_SUBSPACE, LINEAR_CLOSEST_POINT, .. } := D.qconvex
  let { CLOSED_LOCAL_HOMEOMORPHISM_GLOBAL, CONNECTED_OPEN_PATH_CONNECTED, .. } := D.qpaths
  let { CONTINUOUS_ON_VMUL, CONTINUOUS_OPEN_PREIMAGE, EVENTUALLY_AT_TOPOLOGICAL,
        HOMEOMORPHISM_EQ, .. } := D.qtopology1
  let { OPEN_IN_TRANSLATION_EQ, TRIVIAL_LIMIT_AT, WITHIN_UNIV, .. } := D.qtopology2
  let { IN_TRANSLATION_GALOIS, LINEAR_COMPOSE_SUB, LINEAR_INJECTIVE_IMP_SURJECTIVE_ON,
        LINEAR_SURJECTIVE_RIGHT_INVERSE_EQ, MATRIX_INVERTIBLE_LEFT, MATRIX_INVERTIBLE_RIGHT,
        TRANSLATION_SUBSET_GALOIS_LEFT, .. } := D.qvec
  -- @@SCOPE END

  let INVERSE_FUNCTION_THEOREM_GLOBAL ← prove
   r"!f:real^N->real^N f' s t.
      open s /\ connected s /\ simply_connected t /\ (s = {} ==> t = {}) /\
      (!c. closed_in (subtopology euclidean s) c
           ==> closed_in (subtopology euclidean t) (IMAGE f c)) /\
      (!x. x IN s
           ==> (f has_derivative f' x) (at x) /\ ~(det(matrix(f' x)) = &0))
      ==> ?g g'. homeomorphism (s,t) (f,g) /\
                 (!y. y IN t
                      ==> (g has_derivative g' y) (at y) /\
                          f' (g y) o g' y = I /\ g' y o f' (g y) = I) /\
                 (!x. x IN s ==> f' x o g' (f x) = I /\ g' (f x) o f' x = I)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"open(IMAGE (f:real^N->real^N) s)") ASSUME_TAC THENL
     [ASM_MESON_TAC [DIFFERENTIABLE_IMP_OPEN_MAP], ALL_TAC] THEN
    MP_TAC (← ISPECL
      [← q r"f:real^N->real^N", ← q r"s:real^N->bool", ← q r"t:real^N->bool"]
      CLOSED_LOCAL_HOMEOMORPHISM_GLOBAL) THEN
    ASM_SIMP_TAC [CONNECTED_OPEN_PATH_CONNECTED, OPEN_IN_OPEN_EQ] THEN
    ANTS_TAC THENL
     [X_GEN_TAC (← q r"a:real^N") THEN DISCH_TAC THEN
      MP_TAC (← ISPECL [← q r"f:real^N->real^N", ← q r"f':real^N->real^N->real^N",
                        ← q r"a:real^N", ← q r"s:real^N->bool"]
          INVERSE_FUNCTION_THEOREM) THEN
      ASM_REWRITE_TAC [] THEN
      REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
      SIMP_TAC [LEFT_IMP_EXISTS_THM] THEN
      REWRITE_TAC [HOMEOMORPHISM] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_SUBSET THEN
      FIRST_ASSUM (MP_TAC o SPEC (← q r"s:real^N->bool")) THEN
      REWRITE_TAC [CLOSED_IN_REFL] THEN
      DISCH_THEN (MP_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
      ASM SET_TAC [],
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"g:real^N->real^N")] THEN
    MATCH_MP_TAC (← MESON []
     (← q r"(!x. P /\ Q x ==> R x) /\ (P ==> ?x. Q x)
      ==> (P ==> ?x. P /\ Q x /\ R x)")) THEN
    CONJ_TAC THENL
     [REWRITE_TAC [HOMEOMORPHISM, SUBSET, FORALL_IN_IMAGE] THEN SET_TAC [],
      REWRITE_TAC [← GSYM SKOLEM_THM, RIGHT_EXISTS_IMP_THM] THEN
      SIMP_TAC [HOMEOMORPHISM, SUBSET, FORALL_IN_IMAGE] THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"t = IMAGE (f:real^N->real^N) s") SUBST1_TAC THENL
       [ASM SET_TAC [], ASM_SIMP_TAC [FORALL_IN_IMAGE]] THEN
      X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      MP_TAC (← ISPEC (← q r"(f':real^N->real^N->real^N) x") MATRIX_INVERTIBLE) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [has_derivative], ALL_TAC] THEN
      ASM_SIMP_TAC [INVERTIBLE_DET_NZ] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"g':real^N->real^N") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_INVERSE_STRONG THEN MAP_EVERY EXISTS_TAC
       [← q r"(f':real^N->real^N->real^N) x", ← q r"s:real^N->bool"] THEN
      ASM_SIMP_TAC []])

  let INVERSE_FUNCTION_THEOREM_SUBSPACE ← prove
   r"!f:real^N->real^N f' s p a.
        subspace p /\ open_in (subtopology euclidean p) s /\
        IMAGE f s SUBSET p /\ a IN s /\
        (!x. x IN s
             ==> (f has_derivative f' x) (at x within p) /\ IMAGE (f' x) p = p)
        ==> ?t u g g'. open_in (subtopology euclidean p) t /\ a IN t /\
                       t SUBSET s /\
                       open_in (subtopology euclidean p) u /\ f(a) IN u /\
                       homeomorphism (t,u) (f,g) /\
                       (!x. x IN t
                            ==> (f has_derivative f' x) (at x within p) /\
                                (!h. h IN p
                                     ==> f' x (g' (f x) h) = h /\
                                         g' (f x) (f' x h) = h)) /\
                       (!y. y IN u
                            ==> (g has_derivative g' y) (at y within p) /\
                                (!h. h IN p
                                     ==> f' (g y) (g' y h) = h /\
                                         g' y (f' (g y) h) = h))"
   (REPEAT STRIP_TAC THEN
    MAP_EVERY ABBREV_TAC
     [← q r"h = \x:real^N. f(closest_point p x) + (x - closest_point p x)",
      ← q r"h' = \x h. (f':real^N->real^N->real^N)
                  (closest_point p x) (closest_point p h) +
                  (h - closest_point p h)"] THEN
    MP_TAC (← ISPECL
     [← q r"h:real^N->real^N", ← q r"h':real^N->real^N->real^N",
      ← q r"a:real^N",
      ← q r"{x | x IN (:real^N) /\ closest_point p x IN s}"]
     INVERSE_FUNCTION_THEOREM) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [REPEAT (FIRST_X_ASSUM (SUBST1_TAC o SYM)) THEN REWRITE_TAC [] THEN
      MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
       [REWRITE_TAC [OPEN_IN] THEN ONCE_REWRITE_TAC [← GSYM SUBTOPOLOGY_UNIV] THEN
        MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
        EXISTS_TAC (← q r"p:real^N->bool") THEN ASM_REWRITE_TAC [ETA_AX] THEN
        ASM_SIMP_TAC [LINEAR_CONTINUOUS_ON, LINEAR_CLOSEST_POINT] THEN
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_UNIV] THEN
        GEN_TAC THEN MATCH_MP_TAC CLOSEST_POINT_IN_SET THEN
        ASM_SIMP_TAC [CLOSED_SUBSPACE, SUBSPACE_IMP_NONEMPTY],
        ASM_REWRITE_TAC [IN_UNIV, IN_ELIM_THM] THEN DISCH_TAC] THEN
      MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
       [SUBGOAL_THEN (← q r"closest_point p a:real^N = a")
         (fun th => ASM_REWRITE_TAC [th]) THEN
        MATCH_MP_TAC CLOSEST_POINT_SELF THEN
        ASM_MESON_TAC [OPEN_IN_IMP_SUBSET, SUBSET],
        DISCH_TAC] THEN
      X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THENL
         [ALL_TAC,
          MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
          MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN
          ASM_SIMP_TAC [LINEAR_ID, LINEAR_CLOSEST_POINT, ETA_AX]] THEN
        MP_TAC (← ISPECL
         [← q r"closest_point(p:real^N->bool)", ← q r"f:real^N->real^N",
          ← q r"closest_point(p:real^N->bool)",
          ← q r"(f':real^N->real^N->real^N) (closest_point p x)",
          ← q r"x:real^N",
          ← q r"{x:real^N | closest_point p x IN s}"] DIFF_CHAIN_WITHIN) THEN
        ASM_SIMP_TAC [o_DEF, HAS_DERIVATIVE_LINEAR, LINEAR_CLOSEST_POINT] THEN
        ASM_SIMP_TAC [HAS_DERIVATIVE_WITHIN_OPEN, IN_ELIM_THM] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"closest_point p (x:real^N)")) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o CONJUNCT1) THEN
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT]
          HAS_DERIVATIVE_WITHIN_SUBSET) THEN
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_IN_GSPEC] THEN
        ASM_SIMP_TAC [CLOSEST_POINT_IN_SET, CLOSED_SUBSPACE,
                      SUBSPACE_IMP_NONEMPTY],
        REWRITE_TAC [← GSYM INVERTIBLE_DET_NZ] THEN
        W (MP_TAC o PART_MATCH (lhand o rand)
          MATRIX_INVERTIBLE_RIGHT o snd) THEN
        ASM_SIMP_TAC [← GSYM LINEAR_SURJECTIVE_RIGHT_INVERSE_EQ] THEN ANTS_TAC THENL
         [MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN
          ASM_SIMP_TAC [LINEAR_COMPOSE_SUB, LINEAR_ID,
                        LINEAR_CLOSEST_POINT, ETA_AX] THEN
          GEN_REWRITE_TAC RAND_CONV [← GSYM o_DEF] THEN
          MATCH_MP_TAC LINEAR_COMPOSE THEN
          ASM_SIMP_TAC [LINEAR_CLOSEST_POINT, ETA_AX] THEN
          FIRST_X_ASSUM (MP_TAC o SPEC (← q r"closest_point p (x:real^N)")) THEN
          ASM_SIMP_TAC [has_derivative],
          DISCH_THEN SUBST1_TAC] THEN
        X_GEN_TAC (← q r"y:real^N") THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"closest_point p (x:real^N)")) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o MATCH_MP
         (← SET_RULE (← q r"IMAGE f s = t ==> !y. y IN t ==> ?x. x IN s /\ f x = y")) o
         CONJUNCT2) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"closest_point p (y:real^N)")) THEN
        ASM_SIMP_TAC [CLOSEST_POINT_IN_SET, CLOSED_SUBSPACE,
                      SUBSPACE_IMP_NONEMPTY] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"w:real^N") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"w + (y - closest_point p y):real^N") THEN
        ASM_SIMP_TAC [LINEAR_CLOSEST_POINT, LINEAR_ADD, LINEAR_SUB] THEN
        ASM_SIMP_TAC [CLOSEST_POINT_SELF, CLOSEST_POINT_IN_SET, CLOSED_SUBSPACE,
                      SUBSPACE_IMP_NONEMPTY] THEN
        ASM_REWRITE_TAC [VECTOR_SUB_REFL, VECTOR_ADD_RID] THEN
        CONV_TAC (fun t => VECTOR_ARITH t)],
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC
       [← q r"t:real^N->bool", ← q r"u:real^N->bool", ← q r"g:real^N->real^N",
        ← q r"g':real^N->real^N->real^N"] THEN
      REPLICATE_TAC 6 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "*") (LABEL_TAC "+")) THEN
      MAP_EVERY EXISTS_TAC
       [← q r"p INTER t:real^N->bool", ← q r"p INTER u:real^N->bool",
        ← q r"g:real^N->real^N",
        ← q r"g':real^N->real^N->real^N"] THEN
      ASM_SIMP_TAC [OPEN_IN_OPEN_INTER, IN_INTER] THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
      MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN
      CONJ_TAC THENL [ASM SET_TAC [], DISCH_TAC] THEN
      MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
       [MP_TAC (← ISPEC (← q r"p:real^N->bool") CLOSEST_POINT_SELF) THEN ASM SET_TAC [],
        DISCH_TAC] THEN
      SUBGOAL_THEN (← q r"!x. x IN p ==> (h:real^N->real^N) x = f x") ASSUME_TAC THENL
       [EXPAND_TAC "h" THEN SIMP_TAC [CLOSEST_POINT_SELF] THEN
        REPEAT STRIP_TAC THEN CONV_TAC (fun t => VECTOR_ARITH t),
        ALL_TAC] THEN
      MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN
      CONJ_TAC THENL [ASM SET_TAC [], STRIP_TAC] THEN
      SUBGOAL_THEN
       (← q r"!x. x IN t ==> ((h:real^N->real^N) x IN p <=> x IN p)")
      ASSUME_TAC THENL
       [X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN EXPAND_TAC "h" THEN
        REWRITE_TAC [] THEN EQ_TAC THENL
         [DISCH_TAC THEN SUBST1_TAC (← VECTOR_ARITH
           (← q r"x = ((f:real^N->real^N)(closest_point p x) + x - closest_point p x) -
                (f(closest_point p x) - closest_point p x)")) THEN
          REPEAT (MATCH_MP_TAC SUBSPACE_SUB THEN REPEAT CONJ_TAC) THEN
          ASM_REWRITE_TAC [] THEN
          MP_TAC (← ISPECL [← q r"p:real^N->bool", ← q r"a:real^N"]
            CLOSEST_POINT_IN_SET) THEN
          ASM_SIMP_TAC [CLOSED_SUBSPACE, SUBSPACE_IMP_NONEMPTY],
          SIMP_TAC [CLOSEST_POINT_SELF, VECTOR_SUB_REFL, VECTOR_ADD_RID]] THEN
        ASM SET_TAC [],
        ALL_TAC] THEN
      MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
       [FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP
         (← MESON [HOMEOMORPHISM_EQ, HOMEOMORPHISM_OF_SUBSETS]
          (← q r"homeomorphism(t,u) (f',g)
           ==> (!x. x IN t' ==> f' x = f x) /\
               t' SUBSET t /\ u' SUBSET u /\ IMAGE f' t' = u'
           ==> homeomorphism(t',u') (f,g)"))) THEN
        ASM_SIMP_TAC [IN_INTER, INTER_SUBSET] THEN MATCH_MP_TAC (← SET_RULE
         (← q r"!f. (!x. x IN p ==> h x = f x) /\
              IMAGE h t = u /\ IMAGE f (t INTER p) SUBSET p /\
              (!x. x IN t ==> (h x IN p <=> x IN p))
              ==> IMAGE h (p INTER t) = p INTER u")) THEN
        EXISTS_TAC (← q r"f:real^N->real^N") THEN ASM_REWRITE_TAC [] THEN
        CONJ_TAC THENL [ASM_MESON_TAC [homeomorphism], ASM SET_TAC []],
        DISCH_TAC] THEN
      MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
       [ALL_TAC,
        DISCH_TAC THEN ASM_SIMP_TAC [HAS_DERIVATIVE_AT_WITHIN] THEN
        SUBGOAL_THEN (← q r"u = IMAGE (h:real^N->real^N) t") SUBST1_TAC THENL
         [ASM_MESON_TAC [homeomorphism], ONCE_REWRITE_TAC [IMP_CONJ_ALT]] THEN
        REWRITE_TAC [FORALL_IN_IMAGE] THEN
        REPEAT (FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHISM])) THEN
        ASM_SIMP_TAC [IN_INTER]] THEN
      MP_TAC (← ASSUME (← q r"(p INTER t:real^N->bool) SUBSET s")) THEN
      REWRITE_TAC [SUBSET] THEN ASM_SIMP_TAC [IN_INTER] THEN
      DISCH_THEN (K ALL_TAC) THEN X_GEN_TAC (← q r"x:real^N") THEN STRIP_TAC THEN
      REMOVE_THEN "*" (MP_TAC o SPEC (← q r"x:real^N")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o CONJUNCT2) THEN
      REWRITE_TAC [FUN_EQ_THM, o_THM, AND_FORALL_THM, I_THM] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"z:real^N") THEN
      DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
      ASM_SIMP_TAC [] THEN EXPAND_TAC "h'" THEN REWRITE_TAC [] THEN
      SUBGOAL_THEN
       (← q r"(g':real^N->real^N->real^N) (f(x:real^N)) z IN p")
      MP_TAC THENL
       [ALL_TAC,
        ASM_SIMP_TAC [CLOSEST_POINT_SELF, VECTOR_SUB_REFL, VECTOR_ADD_RID]] THEN
      REMOVE_THEN "+" MP_TAC THEN
      SUBGOAL_THEN (← q r"u = IMAGE (h:real^N->real^N) t") SUBST1_TAC THENL
       [ASM_MESON_TAC [homeomorphism], REWRITE_TAC [FORALL_IN_IMAGE]] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"x:real^N")) THEN ASM_SIMP_TAC [] THEN
      DISCH_THEN (MP_TAC o MATCH_MP GATEAUX_DERIVATIVE o CONJUNCT1) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"z:real^N")) THEN
      MATCH_MP_TAC (← ONCE_REWRITE_RULE [IMP_CONJ]
       (← REWRITE_RULE [CONJ_ASSOC] LIM_IN_CLOSED_SET)) THEN
      ASM_SIMP_TAC [CLOSED_SUBSPACE, TRIVIAL_LIMIT_AT] THEN
      SUBGOAL_THEN
       (← q r"eventually (\r. ((f:real^N->real^N) x + drop r % z) IN u) (at(vec 0))")
      MP_TAC THENL
       [REWRITE_TAC [EVENTUALLY_AT_TOPOLOGICAL] THEN
        EXISTS_TAC
        (← q r"{r | r IN (:real^1) /\ ((f:real^N->real^N) x + drop r % z) IN u}") THEN
        REWRITE_TAC [IN_ELIM_THM, IN_DELETE, DROP_VEC, VECTOR_MUL_LID] THEN
        SIMP_TAC [VECTOR_MUL_LZERO, VECTOR_ADD_RID] THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
          ASM_REWRITE_TAC [OPEN_UNIV] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
          REWRITE_TAC [CONTINUOUS_ON_CONST] THEN
          MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
          REWRITE_TAC [o_DEF, LIFT_DROP, CONTINUOUS_ON_ID],
          RULE_ASSUM_TAC (REWRITE_RULE [HOMEOMORPHISM]) THEN ASM SET_TAC []],
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] EVENTUALLY_MONO) THEN
        REWRITE_TAC [FORALL_LIFT, LIFT_DROP] THEN X_GEN_TAC (← q r"r:real") THEN
        DISCH_TAC THEN MATCH_MP_TAC SUBSPACE_MUL THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC SUBSPACE_SUB THEN ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN
         (← q r"(f:real^N->real^N) x IN u /\
          !w. w IN u ==> ((g:real^N->real^N) w IN p <=> w IN p)")
        STRIP_ASSUME_TAC THENL
         [RULE_ASSUM_TAC (REWRITE_RULE [HOMEOMORPHISM]) THEN ASM SET_TAC [],
          ASM_SIMP_TAC []] THEN
        CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
        MATCH_MP_TAC SUBSPACE_ADD THEN
        ASM_SIMP_TAC [SUBSPACE_MUL] THEN ASM SET_TAC []]])

  let INVERSE_FUNCTION_THEOREM_AFFINE ← (do
    let sp ← q r"subspace:(real^N->bool)->bool"
    let af ← q r"affine:(real^N->bool)->bool"
    let iC1 ← SYM (← CONJUNCT1 (← SPEC_ALL I_O_ID))
    let iC2 ← SYM (← CONJUNCT2 (← SPEC_ALL I_O_ID))
    prove
     r"!f:real^N->real^N f' s p a.
        affine p /\ open_in (subtopology euclidean p) s /\
        IMAGE f s SUBSET p /\ a IN s /\
        (!x. x IN s
             ==> (f has_derivative f' x) (at x within p) /\
                 ~(det (matrix (f' x)) = &0))
        ==> ?t u g g'. open_in (subtopology euclidean p) t /\ a IN t /\
                       t SUBSET s /\
                       open_in (subtopology euclidean p) u /\ f(a) IN u /\
                       homeomorphism (t,u) (f,g) /\
                       (!x. x IN t
                            ==> (f has_derivative f' x) (at x within p) /\
                                f' x o g' (f x) = I /\
                                g' (f x) o f' x = I) /\
                       (!y. y IN u
                            ==> (g has_derivative g' y) (at y within p) /\
                                f' (g y) o g' y = I /\
                                g' y o f' (g y) = I)"
     (W (fun (_, w) => tactic_of do
        let sf ← ExceptT.mk (HolCore.Basics.subst [(sp, af)])
        let w' ← ExceptT.mk (sf w)
        pure (SUBGOAL_THEN w' ASSUME_TAC))
      THENL
       [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL
         [← q r"f:real^N->real^N", ← q r"f':real^N->real^N->real^N",
          ← q r"s:real^N->bool", ← q r"p:real^N->bool", ← q r"a:real^N"]
              INVERSE_FUNCTION_THEOREM_SUBSPACE) THEN
        ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
         [X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
          FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real^N")) THEN
          ASM_REWRITE_TAC [← GSYM INVERTIBLE_DET_NZ] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC LINEAR_INJECTIVE_IMP_SURJECTIVE_ON THEN
          FIRST_ASSUM (ASSUME_TAC o CONJUNCT1 o REWRITE_RULE [has_derivative]) THEN
          ASM_REWRITE_TAC [LE_REFL] THEN CONJ_TAC THENL
           [ALL_TAC,
            FIRST_ASSUM (MP_TAC o MATCH_MP MATRIX_INVERTIBLE_LEFT) THEN
            ASM_REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN MESON_TAC []] THEN
          REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
          X_GEN_TAC (← q r"z:real^N") THEN DISCH_TAC THEN
          FIRST_ASSUM (MP_TAC o SPEC (← q r"z:real^N") o
            MATCH_MP GATEAUX_DERIVATIVE_WITHIN) THEN
          FIRST_ASSUM (ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
          SUBGOAL_THEN (← q r"(x:real^N) IN p") ASSUME_TAC THENL
           [ASM SET_TAC [], ALL_TAC] THEN
          ASM_SIMP_TAC [SUBSPACE_ADD, SUBSPACE_MUL, UNIV_GSPEC, WITHIN_UNIV] THEN
          MATCH_MP_TAC (← ONCE_REWRITE_RULE [IMP_CONJ]
           (← REWRITE_RULE [CONJ_ASSOC] LIM_IN_CLOSED_SET)) THEN
          ASM_SIMP_TAC [CLOSED_SUBSPACE, TRIVIAL_LIMIT_AT] THEN
          SUBGOAL_THEN
           (← q r"eventually (\r. r IN {q | (x + drop q % z:real^N) IN s}) (at(vec 0))")
          MP_TAC THENL
           [MATCH_MP_TAC EVENTUALLY_IN_OPEN THEN
            ASM_REWRITE_TAC [IN_ELIM_THM, DROP_VEC, VECTOR_MUL_LZERO] THEN
            ASM_REWRITE_TAC [VECTOR_ADD_RID] THEN ONCE_REWRITE_TAC [OPEN_IN] THEN
            ONCE_REWRITE_TAC [← GSYM SUBTOPOLOGY_UNIV] THEN
            ONCE_REWRITE_TAC [← SET_RULE (← q r"{x | P x} = {x | x IN UNIV /\ P x}")] THEN
            MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
            EXISTS_TAC (← q r"p:real^N->bool") THEN ASM_REWRITE_TAC [] THEN
            ASM_SIMP_TAC [SUBSET, FORALL_IN_IMAGE, SUBSPACE_ADD, SUBSPACE_MUL] THEN
            MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
            REWRITE_TAC [CONTINUOUS_ON_CONST] THEN
            MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
            REWRITE_TAC [o_DEF, LIFT_DROP, CONTINUOUS_ON_ID],
            MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] EVENTUALLY_MONO) THEN
            REWRITE_TAC [FORALL_LIFT, LIFT_DROP, IN_ELIM_THM] THEN
            X_GEN_TAC (← q r"r:real") THEN
            DISCH_TAC THEN MATCH_MP_TAC SUBSPACE_MUL THEN ASM_REWRITE_TAC [] THEN
            MATCH_MP_TAC SUBSPACE_SUB THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC []],
          ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:real^N->bool") THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"u:real^N->bool") THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"g:real^N->real^N") THEN
        REWRITE_TAC [RIGHT_EXISTS_AND_THM] THEN
        REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN (K ALL_TAC) THEN ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN
         (← q r"!x. x IN t
              ==> ?g. linear g /\
                      (f':real^N->real^N->real^N) x o g = I /\ g o f' x = I")
        MP_TAC THENL
         [REPEAT STRIP_TAC THEN
          W (MP_TAC o PART_MATCH (rand o rand) MATRIX_INVERTIBLE o snd) THEN
          REWRITE_TAC [INVERTIBLE_DET_NZ] THEN
          ASM_MESON_TAC [has_derivative, SUBSET],
          GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
           [RIGHT_IMP_EXISTS_THM]] THEN
        REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC (← q r"g':real^N->real^N->real^N") THEN DISCH_TAC THEN
        EXISTS_TAC (← q r"(g':real^N->real^N->real^N) o (g:real^N->real^N)") THEN
        FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHISM]) THEN
        RULE_ASSUM_TAC (REWRITE_RULE [SUBSET]) THEN
        ASM_SIMP_TAC [FORALL_IN_IMAGE, o_THM, SUBSET] THEN STRIP_TAC THEN
        SUBGOAL_THEN (← q r"u = IMAGE (f:real^N->real^N) t") SUBST1_TAC THENL
         [ASM_MESON_TAC [homeomorphism], ASM_SIMP_TAC [FORALL_IN_IMAGE]] THEN
        X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
        MP_TAC (← ISPECL
         [← q r"f:real^N->real^N", ← q r"(f':real^N->real^N->real^N) x",
          ← q r"g:real^N->real^N", ← q r"(g':real^N->real^N->real^N) x",
          ← q r"t:real^N->bool", ← q r"x:real^N"]
         HAS_DERIVATIVE_INVERSE_WITHIN) THEN
        ASM_SIMP_TAC [] THEN
        SUBGOAL_THEN (← q r"IMAGE (f:real^N->real^N) t = u") SUBST1_TAC THENL
         [ASM_MESON_TAC [homeomorphism], ALL_TAC] THEN
        ANTS_TAC THENL [ALL_TAC, ASM_MESON_TAC [HAS_DERIVATIVE_WITHIN_OPEN_IN]] THEN
        CONJ_TAC THENL [ASM_MESON_TAC [HAS_DERIVATIVE_WITHIN_OPEN_IN], ALL_TAC] THEN
        ASM_MESON_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN],
        REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o ISPECL
         [← q r"(\x:real^N. --a + x) o f o (\x. a + x)",
          ← q r"(f':real^N->real^N->real^N) o (\x. a + x)",
          ← q r"IMAGE (\x:real^N. --a + x) s",
          ← q r"IMAGE (\x:real^N. --a + x) p",
          ← q r"vec 0:real^N"]) THEN
        ASM_REWRITE_TAC [OPEN_IN_TRANSLATION_EQ] THEN ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
           [REWRITE_TAC [← VECTOR_ARITH
             (← q r"--a + x:real^N = x - a"), ← GSYM SIMPLE_IMAGE] THEN
            MATCH_MP_TAC AFFINE_DIFFS_SUBSPACE THEN
            ASM_MESON_TAC [SUBSET, OPEN_IN_IMP_SUBSET],
            REWRITE_TAC [IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
            TRANS_TAC SUBSET_TRANS (← q r"IMAGE (f:real^N->real^N) s") THEN
            ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
            REWRITE_TAC [o_DEF, ← GSYM IMAGE_o, IMAGE_ID, SUBSET_REFL, ← VECTOR_ARITH
             (← q r"a + --a + x:real^N = x")],
            ASM_REWRITE_TAC [IN_TRANSLATION_GALOIS, ← VECTOR_ARITH
             (← q r"vec 0 - --a:real^N = a")],
            REWRITE_TAC [FORALL_IN_IMAGE, o_THM, ← VECTOR_ARITH
             (← q r"a + --a + x:real^N = x")] THEN
            X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
            FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real^N")) THEN ASM_REWRITE_TAC [] THEN
            STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
            GEN_REWRITE_TAC LAND_CONV [iC1] THEN
            MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN CONJ_TAC THENL
             [GEN_REWRITE_TAC LAND_CONV [iC2] THEN
              MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN
              ASM_REWRITE_TAC [← GSYM IMAGE_o, o_DEF, IMAGE_ID, I_DEF, ← VECTOR_ARITH
               (← q r"a + --a + x:real^N = x")],
              REWRITE_TAC [I_DEF]] THEN
            GEN_REWRITE_TAC (LAND_CONV o ABS_CONV) [← GSYM VECTOR_ADD_LID] THEN
            MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
            REWRITE_TAC [HAS_DERIVATIVE_CONST, HAS_DERIVATIVE_ID]],
          REWRITE_TAC [LEFT_IMP_EXISTS_THM, o_THM, VECTOR_ADD_RID]] THEN
        MAP_EVERY X_GEN_TAC
         [← q r"t:real^N->bool", ← q r"u:real^N->bool",
          ← q r"g:real^N->real^N", ← q r"g':real^N->real^N->real^N"] THEN
        STRIP_TAC THEN MAP_EVERY EXISTS_TAC
         [← q r"IMAGE (\x:real^N. a + x) t", ← q r"IMAGE (\x:real^N. a + x) u",
          ← q r"(\x:real^N. a + x) o g o (\x. --a + x)",
          ← q r"(g':real^N->real^N->real^N) o (\x. --a + x)"] THEN
        ASM_REWRITE_TAC [IN_TRANSLATION_GALOIS, FORALL_IN_IMAGE, o_THM,
            VECTOR_SUB_REFL, ← VECTOR_ARITH (← q r"--a + a + x:real^N = x")] THEN
        ASM_SIMP_TAC [] THEN REPEAT CONJ_TAC THENL
         [SUBGOAL_THEN (← q r"p = IMAGE (\x:real^N. a + x) (IMAGE (\x. --a + x) p)")
          SUBST1_TAC THENL
           [REWRITE_TAC [← GSYM IMAGE_o, o_DEF, IMAGE_ID, ← VECTOR_ARITH
             (← q r"a + --a + x:real^N = x")],
            ASM_REWRITE_TAC [OPEN_IN_TRANSLATION_EQ]],
          ASM_REWRITE_TAC [TRANSLATION_SUBSET_GALOIS_LEFT],
          SUBGOAL_THEN (← q r"p = IMAGE (\x:real^N. a + x) (IMAGE (\x. --a + x) p)")
          SUBST1_TAC THENL
           [REWRITE_TAC [← GSYM IMAGE_o, o_DEF, IMAGE_ID, ← VECTOR_ARITH
             (← q r"a + --a + x:real^N = x")],
            ASM_REWRITE_TAC [OPEN_IN_TRANSLATION_EQ]],
          ASM_REWRITE_TAC [← VECTOR_ARITH (← q r"x - a:real^N = --a + x")],
          FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHISM]) THEN
          REWRITE_TAC [HOMEOMORPHISM] THEN
          REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, o_THM, IN_TRANSLATION_GALOIS,
                       VECTOR_ADD_SUB, ← VECTOR_ARITH (← q r"--a + a + x:real^N = x")] THEN
          REWRITE_TAC [← VECTOR_ARITH (← q r"--a + x:real^N = x - a")] THEN
          SIMP_TAC [← VECTOR_ARITH (← q r"x - a:real^N = y <=> x = a + y")] THEN
          STRIP_TAC THEN CONJ_TAC THENL
           [SUBGOAL_THEN
             (← q r"f = (\x:real^N. a + x) o
                  ((\x. --a + x) o f o (\x. a + x)) o (\x. --a + x)")
            SUBST1_TAC THENL
             [REWRITE_TAC [← GSYM IMAGE_o, o_DEF, ETA_AX, ← VECTOR_ARITH
               (← q r"a + --a + x:real^N = x")],
              ALL_TAC],
            ALL_TAC] THEN
          REWRITE_TAC [← VECTOR_ARITH (← q r"x - a:real^N = --a + x")] THEN
          MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
          SIMP_TAC [CONTINUOUS_ON_ADD, CONTINUOUS_ON_ID, CONTINUOUS_ON_CONST] THEN
          MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
          SIMP_TAC [CONTINUOUS_ON_ADD, CONTINUOUS_ON_ID, CONTINUOUS_ON_CONST] THEN
          REWRITE_TAC [← GSYM IMAGE_o] THEN
          GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [o_DEF] THEN
          ASM_REWRITE_TAC [IMAGE_ID, ← VECTOR_ARITH (← q r"--a + a + x:real^N = x")] THEN
          ASM_REWRITE_TAC [← VECTOR_ARITH (← q r"--a + x:real^N = x - a")],
          X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
          SUBGOAL_THEN
           (← q r"f =
            (\x:real^N. a + x) o ((\x. --a + x) o f o (\x. a + x)) o (\x. --a + x)")
          SUBST1_TAC THENL
           [REWRITE_TAC [← GSYM IMAGE_o, o_DEF, ETA_AX, ← VECTOR_ARITH
             (← q r"a + --a + x:real^N = x")],
            GEN_REWRITE_TAC LAND_CONV [iC1]],
          X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
          GEN_REWRITE_TAC LAND_CONV [iC1]] THEN
        (MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN CONJ_TAC THENL
          [GEN_REWRITE_TAC LAND_CONV [iC2] THEN
           MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN
           ASM_SIMP_TAC [I_DEF, ← VECTOR_ARITH (← q r"--a + a + x:real^N = x")],
           REWRITE_TAC [I_DEF]] THEN
         GEN_REWRITE_TAC (LAND_CONV o ABS_CONV) [← GSYM VECTOR_ADD_LID] THEN
         MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
         REWRITE_TAC [HAS_DERIVATIVE_CONST, HAS_DERIVATIVE_ID])]))

  pure { INVERSE_FUNCTION_THEOREM_GLOBAL, INVERSE_FUNCTION_THEOREM_SUBSPACE,
         INVERSE_FUNCTION_THEOREM_AFFINE }

/- ------------------------------------------------------------------------- -/
/- Considering derivative R(^1)->R^n as a vector.  (derivatives.ml 5144-5501) -/
/- ------------------------------------------------------------------------- -/

structure DVM where
  has_vector_derivative : thm
  vector_derivative : thm
  VECTOR_DERIVATIVE_WORKS : thm
  VECTOR_DIFFERENTIABLE : thm
  HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE : thm
  VECTOR_DERIVATIVE_UNIQUE_AT : thm
  VECTOR_DERIVATIVE_AT : thm
  HAS_VECTOR_DERIVATIVE_COMPONENTWISE_WITHIN : thm
  HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT : thm
  HAS_VECTOR_DERIVATIVE_LIFT_COMPONENT_WITHIN : thm
  HAS_VECTOR_DERIVATIVE_LIFT_COMPONENT_AT : thm
  HAS_VECTOR_DERIVATIVE_WITHIN_1D : thm
  HAS_VECTOR_DERIVATIVE_AT_1D : thm
  VECTOR_DERIVATIVE_UNIQUE_WITHIN : thm
  VECTOR_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL : thm
  VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL : thm
  HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET : thm
  HAS_VECTOR_DERIVATIVE_CONST : thm
  VECTOR_DERIVATIVE_CONST_AT : thm
  HAS_VECTOR_DERIVATIVE_ID : thm
  HAS_VECTOR_DERIVATIVE_CMUL : thm
  HAS_VECTOR_DERIVATIVE_CMUL_EQ : thm
  HAS_VECTOR_DERIVATIVE_NEG : thm
  HAS_VECTOR_DERIVATIVE_NEG_EQ : thm
  HAS_VECTOR_DERIVATIVE_ADD : thm
  HAS_VECTOR_DERIVATIVE_SUB : thm
  HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN : thm
  HAS_VECTOR_DERIVATIVE_BILINEAR_AT : thm
  HAS_VECTOR_DERIVATIVE_AT_WITHIN : thm
  HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN : thm
  HAS_VECTOR_DERIVATIVE_TRANSFORM_AT : thm
  HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN_OPEN : thm
  VECTOR_DIFF_CHAIN_AT : thm
  VECTOR_DIFF_CHAIN_WITHIN : thm
  VECTOR_DIFFERENTIABLE_BOUND : thm
  HAS_BOUNDED_VECTOR_DERIVATIVE_IMP_LIPSCHITZ : thm
  RESTRICTION_HAS_DERIVATIVE : thm
  BAIRE1_VECTOR_DERIVATIVE : thm
  deriving Inhabited

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
@[nospecialize]
def setupDVM [HolBase] (D : DerivativesDeps) (BDVA : DVA) (BDVB : DVB) (BDVC : DVC) (BDVD : DVD) (BDVG : DVG) (BDVH : DVH) : ExceptT String IO DVM := do
  -- @@SCOPE BEGIN
  let { differentiable, FRECHET_DERIVATIVE_WORKS, has_derivative, HAS_DERIVATIVE_ADD,
        HAS_DERIVATIVE_AT_WITHIN, HAS_DERIVATIVE_CMUL, HAS_DERIVATIVE_COMPONENTWISE_AT,
        HAS_DERIVATIVE_COMPONENTWISE_WITHIN, HAS_DERIVATIVE_CONST, HAS_DERIVATIVE_ID,
        HAS_DERIVATIVE_NEG, HAS_DERIVATIVE_NEG_EQ, HAS_DERIVATIVE_SUB,
        HAS_DERIVATIVE_TRANSFORM_AT, HAS_DERIVATIVE_TRANSFORM_WITHIN,
        HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN, has_derivative_within, jacobian, .. } := BDVA
  let { DIFF_CHAIN_AT, DIFF_CHAIN_WITHIN, HAS_DERIVATIVE_WITHIN_SUBSET, .. } := BDVB
  let { FRECHET_DERIVATIVE_UNIQUE_AT, .. } := BDVC
  let { DIFFERENTIABLE_BOUND, .. } := BDVD
  let { HAS_DERIVATIVE_BILINEAR_AT, HAS_DERIVATIVE_BILINEAR_WITHIN, .. } := BDVG
  let { BAIRE1_PARTIAL_DERIVATIVES, .. } := BDVH
  let { ARITH, CART_EQ, DIMINDEX_1, EQ_IMP, ETA_AX, .. } := D.dg.pt.cvx.core1
  let { FORALL_IN_IMAGE, FUN_EQ_THM, IMP_CONJ, .. } := D.dg.pt.cvx.core2
  let { LAMBDA_BETA, LE_ANTISYM, MONO_EXISTS, MONO_FORALL, REAL_ABS_INV, .. } :=
        D.dg.pt.cvx.core3
  let { REAL_LE_RMUL, REAL_LT_01, REAL_LT_REFL, .. } := D.dg.pt.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_SYM, REAL_SUB_0, .. } := D.dg.pt.cvx.core5
  let { o_DEF, .. } := D.dg.pt.cvx.core6
  let { DIST_NZ, .. } := D.dg.pt.cvx.vec1
  let { DROP_ADD, DROP_CMUL, DROP_EQ, DROP_SUB, DROP_VEC, FORALL_1, LIFT_CMUL, LIFT_DROP,
        NORM_1, .. } := D.dg.pt.cvx.vec2
  let { NORM_MUL, NORM_POS_LE, REAL_ABS_NORM, .. } := D.dg.pt.cvx.vec3
  let { bilinear, drop, linear, VEC_COMPONENT, VECTOR_ADD_LDISTRIB, VECTOR_ADD_RDISTRIB,
        VECTOR_MUL_ASSOC, VECTOR_MUL_COMPONENT, VECTOR_MUL_LID, VECTOR_MUL_RNEG,
        VECTOR_MUL_RZERO, VECTOR_SUB_EQ, VECTOR_SUB_LDISTRIB, .. } := D.dg.pt.cvx.vec4
  let { BOUNDED_POS, .. } := D.dg.pt.cvx.top1
  let { EVENTUALLY_WITHIN, .. } := D.dg.pt.cvx.top3
  let { LIM_UNIQUE, .. } := D.dg.pt.cvx.top4
  let { TRIVIAL_LIMIT_WITHIN, .. } := D.dg.pt.cvx.top5
  let { ASM_MESON_TAC, INTRO_TAC, MESON_TAC, new_definition, parse_as_infix, REAL_ARITH_TAC,
        SELECT_CONV, VECTOR_ARITH, .. } := D.dg.pt.cvx
  let { LINEAR_ID, .. } := D.dg.qvec
  let { LIMIT_POINT_OF_INTERVAL, .. } := D.qconvex
  let { RESTRICTION, .. } := D.qsession
  let { BAIRE_COMPONENTWISE, BAIRE_EQ, .. } := D.qtopology1
  let { LIM_EVENTUALLY, LIM_NULL, LIM_NULL_NORM, LIM_TRANSFORM_EQ, WITHIN_UNIV, .. } :=
        D.qtopology2
  let { DROP_BASIS, LINEAR_FROM_REALS, LINEAR_VMUL_DROP, matrix, ONORM, .. } := D.qvec
  let { CLAIM_TAC, FIX_TAC, HYP_TAC, .. } := D
  -- @@SCOPE END

  parse_as_infix ("has_vector_derivative", (12, "right"))

  let has_vector_derivative ← new_definition
   r"(f has_vector_derivative f') net <=>
        (f has_derivative (\x. drop(x) % f')) net"

  let vector_derivative ← new_definition
   r"vector_derivative (f:real^1->real^N) net =
        @f'. (f has_vector_derivative f') net"

  let VECTOR_DERIVATIVE_WORKS ← prove
   r"!net f:real^1->real^N.
        f differentiable net <=>
        (f has_vector_derivative (vector_derivative f net)) net"
   (REPEAT GEN_TAC THEN REWRITE_TAC [vector_derivative] THEN
    CONV_TAC (RAND_CONV SELECT_CONV) THEN
    SIMP_TAC [FRECHET_DERIVATIVE_WORKS, has_vector_derivative] THEN EQ_TAC THENL
     [ALL_TAC, MESON_TAC [FRECHET_DERIVATIVE_WORKS, differentiable]] THEN
    DISCH_TAC THEN EXISTS_TAC (← q r"column 1 (jacobian (f:real^1->real^N) net)") THEN
    FIRST_ASSUM MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC [jacobian] THEN
    MATCH_MP_TAC LINEAR_FROM_REALS THEN
    RULE_ASSUM_TAC (REWRITE_RULE [has_derivative]) THEN ASM_REWRITE_TAC [])

  let VECTOR_DIFFERENTIABLE ← prove
   r"!f net. f differentiable net <=> (?f'. (f has_vector_derivative f') net)"
   (MESON_TAC [differentiable, has_vector_derivative, VECTOR_DERIVATIVE_WORKS])

  let HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE ← prove
   r"!f f' net. (f has_vector_derivative f') net ==> f differentiable net"
   (MESON_TAC [VECTOR_DIFFERENTIABLE])

  let VECTOR_DERIVATIVE_UNIQUE_AT ← prove
   r"!f:real^1->real^N x f' f''.
     (f has_vector_derivative f') (at x) /\
     (f has_vector_derivative f'') (at x)
     ==> f' = f''"
   (REWRITE_TAC [has_vector_derivative, drop] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^1->real^N",
                      ← q r"\x. drop x % (f':real^N)", ← q r"\x. drop x % (f'':real^N)",
                      ← q r"x:real^1"] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
    ASM_SIMP_TAC [DIMINDEX_1, LE_ANTISYM, drop] THEN
    REWRITE_TAC [FUN_EQ_THM] THEN DISCH_THEN (MP_TAC o SPEC (← q r"vec 1:real^1")) THEN
    SIMP_TAC [VEC_COMPONENT, DIMINDEX_1, ARITH, VECTOR_MUL_LID])

  let VECTOR_DERIVATIVE_AT ← prove
   r"!f:real^1->real^N f' x.
        (f has_vector_derivative f') (at x)
        ==> vector_derivative f (at x) = f'"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
    MAP_EVERY EXISTS_TAC [← q r"f:real^1->real^N", ← q r"x:real^1"] THEN
    ASM_REWRITE_TAC [vector_derivative] THEN CONV_TAC SELECT_CONV THEN
    ASM_MESON_TAC [])

  let HAS_VECTOR_DERIVATIVE_COMPONENTWISE_WITHIN ← prove
   r"!(f:real^1->real^N) f' a s.
         (f has_vector_derivative f') (at a within s) <=>
         !i. 1 <= i /\ i <= dimindex(:N)
             ==> ((\x. lift(f x$i)) has_vector_derivative lift(f'$i))
                 (at a within s)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [has_vector_derivative] THEN
    GEN_REWRITE_TAC LAND_CONV [HAS_DERIVATIVE_COMPONENTWISE_WITHIN] THEN
    REWRITE_TAC [VECTOR_MUL_COMPONENT, LIFT_CMUL])

  let HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT ← prove
   r"!(f:real^1->real^N) f' a.
         (f has_vector_derivative f') (at a) <=>
         !i. 1 <= i /\ i <= dimindex(:N)
             ==> ((\x. lift(f x$i)) has_vector_derivative lift(f'$i)) (at a)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [has_vector_derivative] THEN
    GEN_REWRITE_TAC LAND_CONV [HAS_DERIVATIVE_COMPONENTWISE_AT] THEN
    REWRITE_TAC [VECTOR_MUL_COMPONENT, LIFT_CMUL])

  let HAS_VECTOR_DERIVATIVE_LIFT_COMPONENT_WITHIN ← prove
   r"!(f:real^1->real^N) f' a s i.
        (f has_vector_derivative f') (at a within s) /\
        1 <= i /\ i <= dimindex(:N)
        ==> ((\x. lift(f x$i)) has_vector_derivative lift(f'$i))
             (at a within s)"
   (MESON_TAC [HAS_VECTOR_DERIVATIVE_COMPONENTWISE_WITHIN])

  let HAS_VECTOR_DERIVATIVE_LIFT_COMPONENT_AT ← prove
   r"!(f:real^1->real^N) f' a i.
        (f has_vector_derivative f') (at a) /\
        1 <= i /\ i <= dimindex(:N)
        ==> ((\x. lift(f x$i)) has_vector_derivative lift(f'$i)) (at a)"
   (MESON_TAC [HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT])

  let HAS_VECTOR_DERIVATIVE_WITHIN_1D ← prove
   r"!f:real^1->real^N s x.
      (f has_vector_derivative f') (at x within s) <=>
      ((\y. inv(drop(y - x)) % (f y - f x)) --> f') (at x within s)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [has_vector_derivative, has_derivative_within] THEN
    SIMP_TAC [LINEAR_VMUL_DROP, LINEAR_ID] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [LIM_NULL] THEN
    GEN_REWRITE_TAC LAND_CONV [LIM_NULL_NORM] THEN
    REWRITE_TAC [NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
    REWRITE_TAC [NORM_1, ← GSYM REAL_ABS_INV] THEN
    REWRITE_TAC [← GSYM NORM_1, ← GSYM NORM_MUL] THEN
    REWRITE_TAC [← GSYM LIM_NULL_NORM] THEN MATCH_MP_TAC LIM_TRANSFORM_EQ THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC [EVENTUALLY_WITHIN] THEN
    REWRITE_TAC [← GSYM DIST_NZ, VECTOR_SUB_EQ] THEN
    REWRITE_TAC [VECTOR_ADD_LDISTRIB, VECTOR_SUB_LDISTRIB] THEN
    SIMP_TAC [VECTOR_MUL_ASSOC, DROP_SUB, DROP_EQ, REAL_MUL_LINV, REAL_SUB_0] THEN
    EXISTS_TAC (← q r"&1") THEN REWRITE_TAC [REAL_LT_01] THEN
    REPEAT STRIP_TAC THEN CONV_TAC (fun t => VECTOR_ARITH t))

  let HAS_VECTOR_DERIVATIVE_AT_1D ← prove
   r"!f:real^1->real^N x.
      (f has_vector_derivative f') (at x) <=>
      ((\y. inv(drop(y - x)) % (f y - f x)) --> f') (at x)"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    REWRITE_TAC [HAS_VECTOR_DERIVATIVE_WITHIN_1D])

  let VECTOR_DERIVATIVE_UNIQUE_WITHIN ← prove
   r"!(f:real^1->real^N) x s f' f''.
        ~trivial_limit (at x within s) /\
        (f has_vector_derivative f') (at x within s) /\
        (f has_vector_derivative f'') (at x within s)
        ==> f' = f''"
   (REWRITE_TAC [HAS_VECTOR_DERIVATIVE_WITHIN_1D, LIM_UNIQUE])

  let VECTOR_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL ← prove
   r"!f:real^1->real^N a b x f' f''.
        drop a < drop b /\
        x IN interval [a,b] /\
        (f has_vector_derivative f') (at x within interval [a,b]) /\
        (f has_vector_derivative f'') (at x within interval [a,b])
        ==> f' = f''"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^1->real^N", ← q r"x:real^1",
                      ← q r"interval[a:real^1,b]"] VECTOR_DERIVATIVE_UNIQUE_WITHIN) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [TRIVIAL_LIMIT_WITHIN, LIMIT_POINT_OF_INTERVAL] THEN
    ASM_MESON_TAC [REAL_LT_REFL])

  let VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL ← prove
   r"!f:real^1->real^N f' x a b.
         drop a < drop b /\ x IN interval[a,b] /\
         (f has_vector_derivative f') (at x within interval [a,b])
         ==> vector_derivative f (at x within interval [a,b]) = f'"
   (ASM_MESON_TAC [VECTOR_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL,
      VECTOR_DERIVATIVE_WORKS, differentiable, has_vector_derivative])

  let HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET ← prove
   r"!f s t x. (f has_vector_derivative f') (at x within s) /\ t SUBSET s
             ==> (f has_vector_derivative f') (at x within t)"
   (REWRITE_TAC [has_vector_derivative, HAS_DERIVATIVE_WITHIN_SUBSET])

  let HAS_VECTOR_DERIVATIVE_CONST ← prove
   r"!c net. ((\x. c) has_vector_derivative vec 0) net"
   (REWRITE_TAC [has_vector_derivative] THEN
    REWRITE_TAC [VECTOR_MUL_RZERO, HAS_DERIVATIVE_CONST])

  let VECTOR_DERIVATIVE_CONST_AT ← prove
   r"!c:real^N a. vector_derivative (\x. c) (at a) = vec 0"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    REWRITE_TAC [HAS_VECTOR_DERIVATIVE_CONST])

  let HAS_VECTOR_DERIVATIVE_ID ← prove
   r"!net. ((\x. x) has_vector_derivative (vec 1)) net"
   (REWRITE_TAC [has_vector_derivative] THEN
    SUBGOAL_THEN (← q r"(\x. drop x % vec 1) = (\x. x)")
     (fun th => REWRITE_TAC [HAS_DERIVATIVE_ID, th]) THEN
    REWRITE_TAC [FUN_EQ_THM, ← GSYM DROP_EQ, DROP_CMUL, DROP_VEC] THEN
    REAL_ARITH_TAC)

  let HAS_VECTOR_DERIVATIVE_CMUL ← prove
   r"!f f' net c. (f has_vector_derivative f') net
                ==> ((\x. c % f(x)) has_vector_derivative (c % f')) net"
   (SIMP_TAC [has_vector_derivative] THEN
    ONCE_REWRITE_TAC [← VECTOR_ARITH (← q r"a % b % x = b % a % x")] THEN
    SIMP_TAC [HAS_DERIVATIVE_CMUL])

  let HAS_VECTOR_DERIVATIVE_CMUL_EQ ← prove
   r"!f f' net c.
       ~(c = &0)
       ==> (((\x. c % f(x)) has_vector_derivative (c % f')) net <=>
            (f has_vector_derivative f') net)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP HAS_VECTOR_DERIVATIVE_CMUL) THENL
     [DISCH_THEN (MP_TAC o SPEC (← q r"inv(c):real")),
      DISCH_THEN (MP_TAC o SPEC (← q r"c:real"))] THEN
    ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, VECTOR_MUL_LID, ETA_AX])

  let HAS_VECTOR_DERIVATIVE_NEG ← prove
   r"!f f' net. (f has_vector_derivative f') net
            ==> ((\x. --(f(x))) has_vector_derivative (--f')) net"
   (SIMP_TAC [has_vector_derivative, VECTOR_MUL_RNEG, HAS_DERIVATIVE_NEG])

  let HAS_VECTOR_DERIVATIVE_NEG_EQ ← prove
   r"!f f' net. ((\x. --(f(x))) has_vector_derivative --f') net <=>
              (f has_vector_derivative f') net"
   (SIMP_TAC [has_vector_derivative, HAS_DERIVATIVE_NEG_EQ, VECTOR_MUL_RNEG])

  let HAS_VECTOR_DERIVATIVE_ADD ← prove
   r"!f f' g g' net.
        (f has_vector_derivative f') net /\ (g has_vector_derivative g') net
        ==> ((\x. f(x) + g(x)) has_vector_derivative (f' + g')) net"
   (SIMP_TAC [has_vector_derivative, VECTOR_ADD_LDISTRIB, HAS_DERIVATIVE_ADD])

  let HAS_VECTOR_DERIVATIVE_SUB ← prove
   r"!f f' g g' net.
        (f has_vector_derivative f') net /\ (g has_vector_derivative g') net
        ==> ((\x. f(x) - g(x)) has_vector_derivative (f' - g')) net"
   (SIMP_TAC [has_vector_derivative, VECTOR_SUB_LDISTRIB, HAS_DERIVATIVE_SUB])

  let HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN ← prove
   r"!h:real^M->real^N->real^P f g f' g' x s.
        (f has_vector_derivative f') (at x within s) /\
        (g has_vector_derivative g') (at x within s) /\
        bilinear h
        ==> ((\x. h (f x) (g x)) has_vector_derivative
             (h (f x) g' + h f' (g x))) (at x within s)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [has_vector_derivative] THEN
    DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP HAS_DERIVATIVE_BILINEAR_WITHIN) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [bilinear, linear]) THEN
    ASM_REWRITE_TAC [VECTOR_ADD_LDISTRIB])

  let HAS_VECTOR_DERIVATIVE_BILINEAR_AT ← prove
   r"!h:real^M->real^N->real^P f g f' g' x.
        (f has_vector_derivative f') (at x) /\
        (g has_vector_derivative g') (at x) /\
        bilinear h
        ==> ((\x. h (f x) (g x)) has_vector_derivative
             (h (f x) g' + h f' (g x))) (at x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [has_vector_derivative] THEN
    DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP HAS_DERIVATIVE_BILINEAR_AT) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [bilinear, linear]) THEN
    ASM_REWRITE_TAC [VECTOR_ADD_LDISTRIB])

  let HAS_VECTOR_DERIVATIVE_AT_WITHIN ← prove
   r"!f x s. (f has_vector_derivative f') (at x)
           ==> (f has_vector_derivative f') (at x within s)"
   (SIMP_TAC [has_vector_derivative, HAS_DERIVATIVE_AT_WITHIN])

  let HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN ← prove
   r"!f f' g x s d.
       &0 < d /\ x IN s /\
       (!x'. x' IN s /\ dist (x',x) < d ==> f x' = g x') /\
       (f has_vector_derivative f') (at x within s)
       ==> (g has_vector_derivative f') (at x within s)"
   (REWRITE_TAC [has_vector_derivative, HAS_DERIVATIVE_TRANSFORM_WITHIN])

  let HAS_VECTOR_DERIVATIVE_TRANSFORM_AT ← prove
   r"!f f' g x d.
       &0 < d /\ (!x'. dist (x',x) < d ==> f x' = g x') /\
       (f has_vector_derivative f') (at x)
       ==> (g has_vector_derivative f') (at x)"
   (REWRITE_TAC [has_vector_derivative, HAS_DERIVATIVE_TRANSFORM_AT])

  let HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN_OPEN ← prove
   r"!f g s x.
        open s /\ x IN s /\
        (!y. y IN s ==> f y = g y) /\
        (f has_vector_derivative f') (at x)
        ==> (g has_vector_derivative f') (at x)"
   (REWRITE_TAC [has_vector_derivative, HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN])

  let VECTOR_DIFF_CHAIN_AT ← prove
   r"!f g f' g' x.
         (f has_vector_derivative f') (at x) /\
         (g has_vector_derivative g') (at (f x))
         ==> ((g o f) has_vector_derivative (drop f' % g')) (at x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [has_vector_derivative] THEN
    DISCH_THEN (MP_TAC o MATCH_MP DIFF_CHAIN_AT) THEN
    REWRITE_TAC [o_DEF, DROP_CMUL, ← GSYM VECTOR_MUL_ASSOC])

  let VECTOR_DIFF_CHAIN_WITHIN ← prove
   r"!f g f' g' s x.
         (f has_vector_derivative f') (at x within s) /\
         (g has_vector_derivative g') (at (f x) within IMAGE f s)
         ==> ((g o f) has_vector_derivative (drop f' % g')) (at x within s)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [has_vector_derivative] THEN
    DISCH_THEN (MP_TAC o MATCH_MP DIFF_CHAIN_WITHIN) THEN
    REWRITE_TAC [o_DEF, DROP_CMUL, ← GSYM VECTOR_MUL_ASSOC])

  let VECTOR_DIFFERENTIABLE_BOUND ← prove
   r"!f f':real^1->real^N s B.
     convex s /\
     (!x. x IN s ==> (f has_vector_derivative f' x) (at x within s)) /\
     (!x. x IN s ==> norm (f' x) <= B)
     ==> (!x y. x IN s /\ y IN s ==> norm (f x - f y) <= B * norm (x - y))"
   (INTRO_TAC "!f f' s B; cvx diff bound; !x y; x y" THEN
    MP_TAC (← ISPECL [← q r"f:real^1->real^N", ← q r"\x:real^1 h. drop h % f' x : real^N",
                      ← q r"s:real^1->bool", ← q r"B:real"] DIFFERENTIABLE_BOUND) THEN
    ANTS_TAC THENL
    [HYP_TAC "diff" (REWRITE_RULE [has_vector_derivative]) THEN
     HYP REWRITE_TAC "cvx diff" [] THEN
     INTRO_TAC "![x0]; x0" THEN
     CLAIM_TAC "lin" (← q r"linear (\h. drop h % f' (x0:real^1):real^N)") THENL
     [REWRITE_TAC [linear, DROP_ADD, DROP_CMUL, VECTOR_MUL_ASSOC,
                   VECTOR_ADD_RDISTRIB],
      ALL_TAC] THEN
     HYP_TAC "lin -> _ onorm_le" (REWRITE_RULE [] o MATCH_MP ONORM) THEN
     REMOVE_THEN "onorm_le" MATCH_MP_TAC THEN
     FIX_TAC "[h]" THEN
     REWRITE_TAC [NORM_MUL, ← GSYM NORM_1] THEN
     GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
     HYP SIMP_TAC "x0 bound" [REAL_LE_RMUL, NORM_POS_LE],
     DISCH_THEN MATCH_MP_TAC THEN HYP REWRITE_TAC "x y" []])

  let HAS_BOUNDED_VECTOR_DERIVATIVE_IMP_LIPSCHITZ ← prove
   r"!f:real^1->real^N f' s.
      (!x. x IN s ==> (f has_vector_derivative f'(x)) (at x within s)) /\
      convex s /\ bounded(IMAGE f' s)
      ==> ?B. &0 < B /\
              !x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm (x - y)"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"B:real") THEN
    REWRITE_TAC [FORALL_IN_IMAGE] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC VECTOR_DIFFERENTIABLE_BOUND THEN ASM_MESON_TAC [])

  let RESTRICTION_HAS_DERIVATIVE ← prove
   r"!f:real^1->real^N f' s x.
     x IN s
     ==> ((RESTRICTION s f has_vector_derivative f') (at x within s) <=>
          (f has_vector_derivative f') (at x within s))"
   (INTRO_TAC "!f f' s x; x" THEN EQ_TAC THENL
    [INTRO_TAC "hp" THEN
     MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
     MAP_EVERY EXISTS_TAC [← q r"RESTRICTION s f:real^1->real^N", ← q r"&1"] THEN
     ASM_REWRITE_TAC [REAL_LT_01] THEN
     SIMP_TAC [RESTRICTION],
     INTRO_TAC "hp" THEN
     MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
     MAP_EVERY EXISTS_TAC [← q r"f:real^1->real^N", ← q r"&1"] THEN
     ASM_REWRITE_TAC [REAL_LT_01] THEN
     SIMP_TAC [RESTRICTION]])

  let BAIRE1_VECTOR_DERIVATIVE ← prove
   r"!f:real^1->real^N f' s.
        (!x. x IN s ==> (f has_vector_derivative f'(x)) (at x)) /\ open s
        ==> baire 1 s f'"
   (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [BAIRE_COMPONENTWISE] THEN
    REWRITE_TAC [has_vector_derivative] THEN
    DISCH_THEN (MP_TAC o MATCH_MP
     (← ONCE_REWRITE_RULE [← TAUT (← q r"p /\ q /\ r ==> s <=> p /\ q ==> r ==> s")]
          BAIRE1_PARTIAL_DERIVATIVES)) THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC [DIMINDEX_1, FORALL_1] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] BAIRE_EQ) THEN
    X_GEN_TAC (← q r"x:real^1") THEN DISCH_TAC THEN
    REWRITE_TAC [← GSYM drop, LIFT_DROP, matrix] THEN
    ASM_SIMP_TAC [LAMBDA_BETA, VECTOR_MUL_COMPONENT, CART_EQ,
                  FORALL_1, DIMINDEX_1, DROP_BASIS] THEN
    REWRITE_TAC [← GSYM drop, LIFT_DROP, REAL_MUL_LID])

  pure { has_vector_derivative, vector_derivative, VECTOR_DERIVATIVE_WORKS,
         VECTOR_DIFFERENTIABLE, HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE,
         VECTOR_DERIVATIVE_UNIQUE_AT, VECTOR_DERIVATIVE_AT,
         HAS_VECTOR_DERIVATIVE_COMPONENTWISE_WITHIN, HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT,
         HAS_VECTOR_DERIVATIVE_LIFT_COMPONENT_WITHIN, HAS_VECTOR_DERIVATIVE_LIFT_COMPONENT_AT,
         HAS_VECTOR_DERIVATIVE_WITHIN_1D, HAS_VECTOR_DERIVATIVE_AT_1D,
         VECTOR_DERIVATIVE_UNIQUE_WITHIN, VECTOR_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL,
         VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL, HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET,
         HAS_VECTOR_DERIVATIVE_CONST, VECTOR_DERIVATIVE_CONST_AT, HAS_VECTOR_DERIVATIVE_ID,
         HAS_VECTOR_DERIVATIVE_CMUL, HAS_VECTOR_DERIVATIVE_CMUL_EQ, HAS_VECTOR_DERIVATIVE_NEG,
         HAS_VECTOR_DERIVATIVE_NEG_EQ, HAS_VECTOR_DERIVATIVE_ADD, HAS_VECTOR_DERIVATIVE_SUB,
         HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN, HAS_VECTOR_DERIVATIVE_BILINEAR_AT,
         HAS_VECTOR_DERIVATIVE_AT_WITHIN, HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN,
         HAS_VECTOR_DERIVATIVE_TRANSFORM_AT, HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN_OPEN,
         VECTOR_DIFF_CHAIN_AT, VECTOR_DIFF_CHAIN_WITHIN, VECTOR_DIFFERENTIABLE_BOUND,
         HAS_BOUNDED_VECTOR_DERIVATIVE_IMP_LIPSCHITZ, RESTRICTION_HAS_DERIVATIVE,
         BAIRE1_VECTOR_DERIVATIVE }

/- ------------------------------------------------------------------------- -/
/- Bounds on derivatives from function properties; Kachurovskii's theorem.  -/
/- (derivatives.ml 5502-5798)                                                -/
/- ------------------------------------------------------------------------- -/

structure DVN where
  VECTOR_DERIVATIVE_INCREASING_WITHIN : thm
  NORM_VECTOR_DERIVATIVES_LE_WITHIN : thm
  NORM_VECTOR_DERIVATIVES_LE_AT : thm
  CONVEX_ON_DERIVATIVE_SECANT_IMP : thm
  CONVEX_ON_SECANT_DERIVATIVE_IMP : thm
  CONVEX_ON_DERIVATIVES_IMP : thm
  CONVEX_ON_DERIVATIVE_SECANT : thm
  CONVEX_ON_DERIVATIVES : thm
  CONVEX_ON_SECANT_DERIVATIVE : thm
  deriving Inhabited

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 8192 in
@[nospecialize]
def setupDVN [HolBase] (D : DerivativesDeps) (BDVA : DVA) (BDVB : DVB) (BDVD : DVD) (BDVM : DVM) : ExceptT String IO DVN := do
  -- @@SCOPE BEGIN
  let { has_derivative, HAS_DERIVATIVE_ADD, HAS_DERIVATIVE_CONST, HAS_DERIVATIVE_LINEAR,
        has_derivative_within, .. } := BDVA
  let { DIFF_CHAIN_WITHIN, HAS_DERIVATIVE_WITHIN_SUBSET, .. } := BDVB
  let { MVT_VERY_SIMPLE, .. } := BDVD
  let { HAS_VECTOR_DERIVATIVE_WITHIN_1D, .. } := BDVM
  let { AND_FORALL_THM, DE_MORGAN_THM, ETA_AX, .. } := D.dg.pt.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_UNWIND_THM2, FUN_EQ_THM, IMP_CONJ, IMP_CONJ_ALT, IMP_IMP,
        IN_DIFF, .. } := D.dg.pt.cvx.core2
  let { IN_INSERT, LEFT_IMP_EXISTS_THM, NOT_IN_EMPTY, REAL_ABS_POS, REAL_ADD_LID,
        REAL_ADD_RID, REAL_DIV_LMUL, .. } := D.dg.pt.cvx.core3
  let { REAL_INV_MUL, REAL_INV_NEG, REAL_LE_DIV2_EQ, REAL_LE_INV_EQ, REAL_LE_LMUL,
        REAL_LE_LMUL_EQ, REAL_LE_MUL, REAL_LE_REFL, REAL_LE_TRANS, REAL_LT_01, REAL_LT_DIV,
        REAL_LT_IMP_LE, REAL_LT_LE, REAL_LT_MIN, REAL_LT_RDIV_EQ, REAL_MIN_LT, .. } :=
        D.dg.pt.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LNEG, REAL_MUL_LZERO, REAL_MUL_RNEG,
        REAL_NEG_NEG, REAL_NEG_SUB, REAL_SUB_LE, REAL_SUB_REFL, REAL_SUB_RZERO,
        RIGHT_FORALL_IMP_THM, RIGHT_IMP_FORALL_THM, SUBSET, .. } := D.dg.pt.cvx.core5
  let { o_ASSOC, o_DEF, o_THM, real_abs, real_div, SWAP_FORALL_THM, .. } :=
        D.dg.pt.cvx.core6
  let { REAL_HALF, .. } := D.dg.pt.cvx.misc
  let { DIST_0, DIST_POS_LT, .. } := D.dg.pt.cvx.vec1
  let { DROP_ADD, DROP_CMUL, DROP_EQ, DROP_SUB, DROP_VEC, EXISTS_LIFT, LIFT_ADD, LIFT_CMUL,
        LIFT_DROP, LIFT_EQ, LIFT_SUB, LINEAR_0, LINEAR_CMUL, .. } := D.dg.pt.cvx.vec2
  let { NORM_LIFT, NORM_MUL, NORM_POS_LT, .. } := D.dg.pt.cvx.vec3
  let { dist, linear, VECTOR_ADD_LID, VECTOR_ADD_RID, VECTOR_MUL_LID, VECTOR_MUL_LZERO,
        VECTOR_NEG_SUB, VECTOR_SUB_EQ, VECTOR_SUB_REFL, VECTOR_SUB_RZERO, .. } :=
        D.dg.pt.cvx.vec4
  let { EVENTUALLY_MONO, .. } := D.dg.pt.cvx.met
  let { ENDS_IN_SEGMENT, EVENTUALLY_WITHIN, .. } := D.dg.pt.cvx.top3
  let { IN_INTERVAL_1, IN_SEGMENT, LIM_NORM, LIM_WITHIN, .. } := D.dg.pt.cvx.top4
  let { open_segment, SEGMENT_SYM, TRIVIAL_LIMIT_WITHIN, .. } := D.dg.pt.cvx.top5
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV,
        SET_TAC, VECTOR_ARITH, VECTOR_ARITH_TAC, .. } := D.dg.pt.cvx
  let { CONVEX_ALT, CONVEX_CONTAINS_SEGMENT, .. } := D.dg.pt.qcvx2
  let { I_DEF, I_O_ID, .. } := D.dg.qsession
  let { LIFT_NEG, .. } := D.dg.qvec
  let { convex_on, CONVEX_ON_LEFT_SECANT, .. } := D.qconvex
  let { LIMPT_OF_UNIV, .. } := D.qtopology1
  let { LIM_DROP_LBOUND, LIM_DROP_LE, WITHIN_UNIV, .. } := D.qtopology2
  let { LINEAR_NEG, .. } := D.qvec
  -- @@SCOPE END

  let VECTOR_DERIVATIVE_INCREASING_WITHIN ← prove
   r"!f f' s a.
        (!x y. x IN s /\ y IN s /\ drop x <= drop y
               ==> drop(f x) <= drop(f y)) /\
        a IN s /\ a limit_point_of s /\
        (f has_vector_derivative f') (at a within s)
        ==> &0 <= drop f'"
   (REWRITE_TAC [HAS_VECTOR_DERIVATIVE_WITHIN_1D] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
     (← ONCE_REWRITE_RULE [IMP_CONJ] LIM_DROP_LBOUND)) THEN
    ASM_REWRITE_TAC [TRIVIAL_LIMIT_WITHIN, EVENTUALLY_WITHIN] THEN
    EXISTS_TAC (← q r"&1") THEN REWRITE_TAC [REAL_LT_01, DROP_CMUL, DROP_SUB] THEN
    X_GEN_TAC (← q r"b:real^1") THEN STRIP_TAC THEN
    DISJ_CASES_TAC (← REAL_ARITH (← q r"drop a <= drop b \/ drop b <= drop a")) THENL
      [ALL_TAC,
       ONCE_REWRITE_TAC [← GSYM REAL_NEG_SUB] THEN
       SIMP_TAC [REAL_INV_NEG, REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_NEG]] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC [REAL_LE_INV_EQ, REAL_SUB_LE])

  let NORM_VECTOR_DERIVATIVES_LE_WITHIN ← prove
   r"!f:real^1->real^M g:real^1->real^N f' g' x s.
        x limit_point_of s /\
        (f has_vector_derivative f') (at x within s) /\
        (g has_vector_derivative g') (at x within s) /\
        eventually (\y. norm(f y - f x) <= norm(g y - g x)) (at x within s)
        ==> norm f' <= norm g'"
   (REWRITE_TAC [HAS_VECTOR_DERIVATIVE_WITHIN_1D] THEN
    REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC BINOP_CONV [← GSYM LIFT_DROP] THEN
    MATCH_MP_TAC (← ISPEC (← q r"at (x:real^1) within s") LIM_DROP_LE) THEN
    MAP_EVERY EXISTS_TAC
     [← q r"\y. lift(norm(inv(drop(y - x)) % (f y - f x:real^M)))",
      ← q r"\y. lift(norm(inv(drop(y - x)) % (g y - g x:real^N)))"] THEN
    ASM_SIMP_TAC [TRIVIAL_LIMIT_WITHIN, LIM_NORM] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT]
          EVENTUALLY_MONO)) THEN
    SIMP_TAC [NORM_MUL, LIFT_DROP, REAL_LE_LMUL, REAL_ABS_POS])

  let NORM_VECTOR_DERIVATIVES_LE_AT ← prove
   r"!f:real^1->real^M g:real^1->real^N f' g' x.
        (f has_vector_derivative f') (at x) /\
        (g has_vector_derivative g') (at x) /\
        eventually (\y. norm(f y - f x) <= norm(g y - g x)) (at x)
        ==> norm f' <= norm g'"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC NORM_VECTOR_DERIVATIVES_LE_WITHIN THEN
    MAP_EVERY EXISTS_TAC
     [← q r"f:real^1->real^M", ← q r"g:real^1->real^N", ← q r"x:real^1", ← q r"(:real^1)"] THEN
    ASM_REWRITE_TAC [LIMPT_OF_UNIV, WITHIN_UNIV])

  let CONVEX_ON_DERIVATIVE_SECANT_IMP ← prove
   r"!f f' s x y:real^N.
        f convex_on s /\ segment[x,y] SUBSET s /\
        ((lift o f) has_derivative (lift o f')) (at x within s)
        ==> f'(y - x) <= f y - f x"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(x:real^N) IN s /\ (y:real^N) IN s") ASSUME_TAC THENL
     [ASM_MESON_TAC [SUBSET, ENDS_IN_SEGMENT], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [has_derivative_within]) THEN
    REWRITE_TAC [LIM_WITHIN, DIST_0, o_THM] THEN
    REWRITE_TAC [← GSYM LIFT_ADD, ← GSYM LIFT_SUB, ← GSYM LIFT_CMUL, NORM_LIFT] THEN
    STRIP_TAC THEN ASM_CASES_TAC (← q r"y:real^N = x") THENL
     [FIRST_X_ASSUM (MP_TAC o MATCH_MP LINEAR_0) THEN
      REWRITE_TAC [o_THM, VECTOR_SUB_REFL, ← GSYM DROP_EQ, DROP_VEC, LIFT_DROP] THEN
      ASM_SIMP_TAC [REAL_SUB_REFL, REAL_LE_REFL, VECTOR_SUB_REFL],
      ALL_TAC] THEN
    ABBREV_TAC (← q r"e = (f':real^N->real)(y - x) - (f y - f x)") THEN
    ASM_CASES_TAC (← q r"&0 < e") THENL [ALL_TAC, ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e / &2 / norm(y - x:real^N)")) THEN
    ASM_SIMP_TAC [REAL_LT_DIV, REAL_HALF, NORM_POS_LT, VECTOR_SUB_EQ] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ABBREV_TAC (← q r"u = min (&1 / &2) (d / &2 / norm (y - x:real^N))") THEN
    SUBGOAL_THEN (← q r"&0 < u /\ u < &1") STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN REWRITE_TAC [REAL_LT_MIN, REAL_MIN_LT] THEN
      ASM_SIMP_TAC [REAL_LT_DIV, NORM_POS_LT, REAL_HALF, VECTOR_SUB_EQ] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV,
      ALL_TAC] THEN
    ABBREV_TAC (← q r"z:real^N = (&1 - u) % x + u % y") THEN
    SUBGOAL_THEN (← q r"(z:real^N) IN segment(x,y)") MP_TAC THENL
     [ASM_MESON_TAC [IN_SEGMENT], ALL_TAC] THEN
    SIMP_TAC [open_segment, IN_DIFF, IN_INSERT, NOT_IN_EMPTY, DE_MORGAN_THM] THEN
    STRIP_TAC THEN DISCH_THEN (MP_TAC o SPEC (← q r"z:real^N")) THEN
    SUBGOAL_THEN (← q r"(z:real^N) IN s") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [DIST_POS_LT] THEN
      EXPAND_TAC "z" THEN REWRITE_TAC [dist, NORM_MUL, ← VECTOR_ARITH
       (← q r"((&1 - u) % x + u % y) - x:real^N = u % (y - x)")] THEN
      ASM_SIMP_TAC [← GSYM REAL_LT_RDIV_EQ, NORM_POS_LT, VECTOR_SUB_EQ] THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [CONVEX_ON_LEFT_SECANT]) THEN
    DISCH_THEN (MP_TAC o SPECL [← q r"x:real^N", ← q r"y:real^N", ← q r"z:real^N"]) THEN
    ASM_REWRITE_TAC [open_segment, IN_DIFF, IN_INSERT, NOT_IN_EMPTY] THEN
    SIMP_TAC [← REAL_ARITH (← q r"inv y * (z - (x + d)):real = (z - x) / y - d / y")] THEN
    REWRITE_TAC [IMP_IMP] THEN DISCH_THEN (MP_TAC o MATCH_MP (← REAL_ARITH
     (← q r"z <= y / n /\ abs(z - d) < e / n ==> d <= (y + e) / n"))) THEN
    SUBGOAL_THEN
     (← q r"(f':real^N->real)(z - x) / norm(z - x) = f'(y - x) / norm(y - x)")
    SUBST1_TAC THENL
     [EXPAND_TAC "z" THEN
      REWRITE_TAC [← VECTOR_ARITH
       (← q r"((&1 - u) % x + u % y) - x:real^N = u % (y - x)")] THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP LINEAR_CMUL) THEN
      DISCH_THEN (MP_TAC o SPECL [← q r"u:real", ← q r"y - x:real^N"]) THEN
      ASM_REWRITE_TAC [← GSYM LIFT_CMUL, o_THM, LIFT_EQ] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [NORM_MUL] THEN
      ASM_SIMP_TAC [real_abs, REAL_LT_IMP_LE] THEN
      REWRITE_TAC [real_div, REAL_INV_MUL, REAL_MUL_ASSOC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN
      REWRITE_TAC [← GSYM real_div] THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
      ASM_REAL_ARITH_TAC,
      ASM_SIMP_TAC [REAL_LE_DIV2_EQ, NORM_POS_LT, VECTOR_SUB_EQ] THEN
      ASM_REAL_ARITH_TAC])

  let CONVEX_ON_SECANT_DERIVATIVE_IMP ← prove
   r"!f f' s x y:real^N.
        f convex_on s /\ segment[x,y] SUBSET s /\
        ((lift o f) has_derivative (lift o f')) (at y within s)
        ==> f y - f x <= f'(y - x)"
   (ONCE_REWRITE_TAC [SEGMENT_SYM] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL
     [← q r"f:real^N->real", ← q r"f':real^N->real", ← q r"s:real^N->bool",
      ← q r"y:real^N", ← q r"x:real^N"] CONVEX_ON_DERIVATIVE_SECANT_IMP) THEN
    ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [SEGMENT_SYM] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"f' = --f'' ==> f' <= x - y ==> y - x <= f''")) THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM VECTOR_NEG_SUB] THEN
    GEN_REWRITE_TAC I [← GSYM LIFT_EQ] THEN REWRITE_TAC [LIFT_NEG] THEN
    SPEC_TAC ((← q r"y - x:real^N"), (← q r"z:real^N")) THEN
    MATCH_MP_TAC (← REWRITE_RULE [RIGHT_FORALL_IMP_THM] LINEAR_NEG) THEN
    REWRITE_TAC [← GSYM o_DEF] THEN ASM_MESON_TAC [has_derivative])

  let CONVEX_ON_DERIVATIVES_IMP ← prove
   r"!f f'x f'y s x y:real^N.
        f convex_on s /\ segment[x,y] SUBSET s /\
        ((lift o f) has_derivative (lift o f'x)) (at x within s) /\
        ((lift o f) has_derivative (lift o f'y)) (at y within s)
        ==> f'x(y - x) <= f'y(y - x)"
   (ASM_MESON_TAC [CONVEX_ON_DERIVATIVE_SECANT_IMP,
                   CONVEX_ON_SECANT_DERIVATIVE_IMP,
                   SEGMENT_SYM, REAL_LE_TRANS])

  let (CONVEX_ON_DERIVATIVE_SECANT, CONVEX_ON_DERIVATIVES) ← CONJ_PAIR (← prove
   r"(!f f' s:real^N->bool.
        convex s /\
        (!x. x IN s ==> ((lift o f) has_derivative (lift o f'(x)))
                        (at x within s))
        ==> (f convex_on s <=>
             !x y. x IN s /\ y IN s ==> f'(x)(y - x) <= f y - f x)) /\
   (!f f' s:real^N->bool.
        convex s /\
        (!x. x IN s ==> ((lift o f) has_derivative (lift o f'(x)))
                        (at x within s))
        ==> (f convex_on s <=>
             !x y. x IN s /\ y IN s ==> f'(x)(y - x) <= f'(y)(y - x)))"
   (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC [← TAUT (← q r"(a ==> b) /\ (a ==> c) <=> a ==> b /\ c")] THEN
    STRIP_TAC THEN MATCH_MP_TAC (← TAUT
     (← q r"(a ==> b) /\ (b ==> c) /\ (c ==> a) ==> (a <=> b) /\ (a <=> c)")) THEN
    REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONVEX_ON_DERIVATIVE_SECANT_IMP THEN
      EXISTS_TAC (← q r"s:real^N->bool") THEN ASM_SIMP_TAC [ETA_AX] THEN
      ASM_MESON_TAC [CONVEX_CONTAINS_SEGMENT],
      DISCH_TAC THEN MAP_EVERY X_GEN_TAC [← q r"x:real^N", ← q r"y:real^N"] THEN
      STRIP_TAC THEN FIRST_X_ASSUM (fun th => tactic_of do
       pure (MP_TAC (← ISPECL [← q r"x:real^N", ← q r"y:real^N"] th) THEN
             MP_TAC (← ISPECL [← q r"y:real^N", ← q r"x:real^N"] th))) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← REAL_ARITH
       (← q r"f''' = --f'' ==> f''' <= x - y ==> f' <= y - x ==> f' <= f''")) THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM VECTOR_NEG_SUB] THEN
      GEN_REWRITE_TAC I [← GSYM LIFT_EQ] THEN REWRITE_TAC [LIFT_NEG] THEN
      SPEC_TAC ((← q r"y - x:real^N"), (← q r"z:real^N")) THEN
      MATCH_MP_TAC (← REWRITE_RULE [RIGHT_FORALL_IMP_THM] LINEAR_NEG) THEN
      REWRITE_TAC [← GSYM o_DEF] THEN REWRITE_TAC [← GSYM I_DEF, I_O_ID] THEN
      ASM_MESON_TAC [has_derivative],
      ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC [convex_on] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"b:real^N"] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    REWRITE_TAC [← TAUT (← q r"a /\ b /\ c /\ d /\ e <=> e /\ a /\ b /\ c /\ d")] THEN
    REWRITE_TAC [IMP_CONJ, ← REAL_ARITH (← q r"u + v = &1 <=> u = &1 - v")] THEN
    REWRITE_TAC [FORALL_UNWIND_THM2, REAL_SUB_LE] THEN X_GEN_TAC (← q r"u:real") THEN
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"u = &0") THEN
    ASM_SIMP_TAC [REAL_SUB_RZERO, VECTOR_MUL_LZERO, VECTOR_MUL_LID, REAL_LE_REFL,
                  REAL_MUL_LZERO, REAL_MUL_LID, VECTOR_ADD_RID, REAL_ADD_RID] THEN
    ASM_CASES_TAC (← q r"u = &1") THEN
    ASM_SIMP_TAC [REAL_SUB_REFL, VECTOR_MUL_LZERO, VECTOR_MUL_LID, REAL_LE_REFL,
                  REAL_MUL_LZERO, REAL_MUL_LID, VECTOR_ADD_LID, REAL_ADD_LID] THEN
    SUBGOAL_THEN (← q r"&0 < u /\ u < &1") STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC [REAL_LT_LE], ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"lift o (f:real^N->real) o (\u. (&1 - drop u) % a + drop u % b)",
      ← q r"\x:real^1. lift o f'((&1 - drop x) % a + drop x % b) o
       (\u. --(drop u) % a + drop u % b:real^N)"] MVT_VERY_SIMPLE) THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← ISPECL [← q r"vec 0:real^1", ← q r"lift u"] th) THEN
            MP_TAC (← ISPECL [← q r"lift u", ← q r"vec 1:real^1"] th))) THEN
    ASM_REWRITE_TAC [LIFT_DROP, o_THM] THEN
    ASM_SIMP_TAC [DROP_VEC, VECTOR_MUL_LZERO, REAL_SUB_RZERO, REAL_LT_IMP_LE,
                  VECTOR_ADD_RID, VECTOR_MUL_LID, VECTOR_SUB_RZERO] THEN
    MATCH_MP_TAC (← TAUT
     (← q r"(a1 /\ a2) /\ (b1 ==> b2 ==> c) ==> (a1 ==> b1) ==> (a2 ==> b2) ==> c")) THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN X_GEN_TAC (← q r"v:real^1") THEN DISCH_TAC THEN
      (REWRITE_TAC [o_ASSOC] THEN MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN
       REWRITE_TAC [] THEN CONJ_TAC THENL
        [MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THENL
          [ONCE_REWRITE_TAC [← VECTOR_ARITH (← q r"(&1 - a) % x:real^N = x + --a % x"),
                             ← VECTOR_ARITH (← q r"--u % a:real^N = vec 0 + --u % a")] THEN
           MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
           REWRITE_TAC [HAS_DERIVATIVE_CONST],
           ALL_TAC] THEN
         MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
         REWRITE_TAC [linear, DROP_ADD, DROP_CMUL] THEN VECTOR_ARITH_TAC,
         MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
         EXISTS_TAC (← q r"s:real^N->bool") THEN CONJ_TAC THENL
          [FIRST_X_ASSUM MATCH_MP_TAC,
           REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN GEN_TAC THEN DISCH_TAC] THEN
         FIRST_ASSUM (MATCH_MP_TAC o GEN_REWRITE_RULE I [CONVEX_ALT]) THEN
         RULE_ASSUM_TAC (REWRITE_RULE [IN_INTERVAL_1, LIFT_DROP, DROP_VEC]) THEN
         ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC]),
      REWRITE_TAC [REAL_SUB_REFL, VECTOR_MUL_LZERO, VECTOR_ADD_LID] THEN
      REWRITE_TAC [EXISTS_LIFT, LIFT_DROP, IN_INTERVAL_1, DROP_VEC] THEN
      REWRITE_TAC [← GSYM LIFT_SUB, LIFT_EQ] THEN
      REWRITE_TAC [DROP_SUB, DROP_VEC, LIFT_DROP] THEN
      REWRITE_TAC [← VECTOR_ARITH (← q r"--u % a + u % b:real^N = u % (b - a)")] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM, RIGHT_IMP_FORALL_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"w:real", ← q r"v:real"] THEN
      DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      ONCE_REWRITE_TAC [← TAUT (← q r"a ==> b /\ c ==> d <=> b ==> a ==> c ==> d")] THEN
      STRIP_TAC THEN REWRITE_TAC [IMP_IMP] THEN
      DISCH_THEN (CONJUNCTS_THEN2 (MP_TAC o AP_TERM (← q r"(*) (u:real)"))
                                 (MP_TAC o AP_TERM (← q r"(*) (&1 - u:real)"))) THEN
      MATCH_MP_TAC (← REAL_ARITH
       (← q r"f1 <= f2 /\ (xa <= xb ==> a <= b)
        ==> xa = f1 ==> xb = f2 ==> a <= b")) THEN
      CONJ_TAC THENL [ALL_TAC, REAL_ARITH_TAC] THEN
      SUBGOAL_THEN
       (← q r"((&1 - v) % a + v % b:real^N) IN s /\
        ((&1 - w) % a + w % b:real^N) IN s")
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o GEN_REWRITE_RULE I [CONVEX_ALT]) THEN
        ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"linear(lift o (f'((&1 - v) % a + v % b:real^N):real^N->real)) /\
        linear(lift o (f'((&1 - w) % a + w % b:real^N):real^N->real))")
      MP_TAC THENL [ASM_MESON_TAC [has_derivative], ALL_TAC] THEN
      DISCH_THEN (CONJUNCTS_THEN (MP_TAC o MATCH_MP LINEAR_CMUL)) THEN
      ASM_REWRITE_TAC [o_THM, ← GSYM LIFT_NEG, ← GSYM LIFT_CMUL, LIFT_EQ] THEN
      REPEAT DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      ONCE_REWRITE_TAC [← REAL_ARITH (← q r"(&1 - u) * u * x = u * (&1 - u) * x")] THEN
      REPEAT (MATCH_MP_TAC REAL_LE_LMUL THEN
              CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
      FIRST_X_ASSUM (MP_TAC o SPECL
       [← q r"(&1 - v) % a + v % b:real^N", ← q r"(&1 - w) % a + w % b:real^N"]) THEN
      ASM_REWRITE_TAC [← VECTOR_ARITH
       (← q r"((&1 - v) % a + v % b) - ((&1 - w) % a + w % b):real^N =
        (v - w) % (b - a)")] THEN
      ASM_CASES_TAC (← q r"v:real = w") THEN ASM_SIMP_TAC [REAL_LE_REFL] THEN
      SUBGOAL_THEN (← q r"&0 < w - v") (fun th => SIMP_TAC [th, REAL_LE_LMUL_EQ]) THEN
      ASM_REAL_ARITH_TAC]))

  let CONVEX_ON_SECANT_DERIVATIVE ← prove
   r"!f f' s:real^N->bool.
        convex s /\
        (!x. x IN s ==> ((lift o f) has_derivative (lift o f'(x)))
                        (at x within s))
        ==> (f convex_on s <=>
             !x y. x IN s /\ y IN s ==> f y - f x <= f'(y)(y - x))"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP CONVEX_ON_DERIVATIVE_SECANT) THEN
    GEN_REWRITE_TAC RAND_CONV [SWAP_FORALL_THM] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"x:real^N") THEN REWRITE_TAC [] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"y:real^N") THEN REWRITE_TAC [] THEN
    MAP_EVERY ASM_CASES_TAC [← q r"(x:real^N) IN s", ← q r"(y:real^N) IN s"] THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"f' = --f'' ==> (f' <= y - x <=> x - y <= f'')")) THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM VECTOR_NEG_SUB] THEN
    GEN_REWRITE_TAC I [← GSYM LIFT_EQ] THEN REWRITE_TAC [LIFT_NEG] THEN
    SPEC_TAC ((← q r"x - y:real^N"), (← q r"z:real^N")) THEN
    MATCH_MP_TAC (← REWRITE_RULE [RIGHT_FORALL_IMP_THM] LINEAR_NEG) THEN
    REWRITE_TAC [← GSYM o_DEF] THEN
    REWRITE_TAC [← GSYM I_DEF, I_O_ID] THEN ASM_MESON_TAC [has_derivative])

  pure { VECTOR_DERIVATIVE_INCREASING_WITHIN, NORM_VECTOR_DERIVATIVES_LE_WITHIN,
         NORM_VECTOR_DERIVATIVES_LE_AT, CONVEX_ON_DERIVATIVE_SECANT_IMP,
         CONVEX_ON_SECANT_DERIVATIVE_IMP, CONVEX_ON_DERIVATIVES_IMP,
         CONVEX_ON_DERIVATIVE_SECANT, CONVEX_ON_DERIVATIVES, CONVEX_ON_SECANT_DERIVATIVE }

end HolMultiLib.Derivatives
