/- ========================================================================= -/
/- Further results in topology (moretop.ml).                                 -/
/- ========================================================================= -/
/- File: HolMultiLib/MoreTop.lean

  Original (c) Copyright, John Harrison 1998-2008 (see moretop.ml).
  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/moretop.ml`, in the style of
  HolMultiLib/Measure.lean: pure, the proofs translated by hand, one `let`
  per OCaml `let`, in file order.  The load-time effects are at their file
  positions.  What moretop.ml uses from earlier files is passed in `MoreTopDeps`.
  SessionMultiLib/MoreTop.lean supplies it.
-/

import HolMultiLib.RealAnalysis

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolMultiLib.MoreTop

/- The theorems moretop.ml uses that the deps chain does not carry, grouped by the
   file that proves them. -/

structure QTopologyThms where
  (BOUNDED_SUBSET_OPEN_INTERVAL CLOPEN_IN_COMPONENTS CLOSED_COMPACT_PROJECTION
   CLOSED_IN_CONNECTED_COMPONENT CLOSED_IN_INTER_CLOSURE
   CLOSED_MAP_IFF_UPPER_HEMICONTINUOUS_PREIMAGE COBOUNDED_IMP_UNBOUNDED
   COMMON_FRONTIER_DOMAINS COMPACT_ATTAINS_INF CONNECTED_CLOSED_MONOTONE_PREIMAGE
   CONNECTED_CLOSED_SET CONNECTED_COMPONENT_DISJOINT CONNECTED_COMPONENT_EQ
   CONNECTED_COMPONENT_EQ_EQ CONNECTED_COMPONENT_IN CONNECTED_COMPONENT_SYM_EQ
   CONNECTED_COMPONENT_UNIV CONNECTED_EQ_CARD_COMPONENTS CONNECTED_IVT_HYPERPLANE
   CONNECTED_UNION CONNECTED_UNIONS CONTINUOUS_FROM_CLOSED_GRAPH
   CONTINUOUS_IMP_CLOSED_MAP_EXPLICIT CONTINUOUS_MAP_DOT CONTINUOUS_MAP_VECTOR_MUL
   CONTINUOUS_MAP_VECTOR_SUB CONTINUOUS_ON_CASES_LOCAL_OPEN CONTINUOUS_ON_SING
   FINITE_IMP_TOTALLY_DISCONNECTED FRONTIER_UNION_SUBSET FRONTIER_UNIV
   HOMEOMORPHIC_BALL_UNIV HOMEOMORPHIC_SELF_IMAGE HOMEOMORPHIC_SING
   HOMEOMORPHISM_COMPACTNESS HOMEOMORPHISM_CONNECTEDNESS HOMEOMORPHISM_IMP_CLOSED_MAP
   IN_COMPONENTS_MAXIMAL IN_COMPONENTS_SELF
   OPEN_MAP_IFF_LOWER_HEMICONTINUOUS_PREIMAGE OPEN_SEGMENT_1 OPEN_SUBOPEN
   OPEN_TRANSLATION SETDIST_EQ_0_CLOSED UPPER_LOWER_HEMICONTINUOUS_EXPLICIT : thm)
  deriving Inhabited

structure QPathsThms where
  (ARC_REVERSEPATH ARC_REVERSEPATH_EQ CLOSED_IN_UNION_COMPLEMENT_COMPONENT
   CLOSED_IRREDUCIBLE_SEPARATOR CLOSED_UNION_COMPLEMENT_COMPONENT
   CONIC_IMP_CONTRACTIBLE CONNECTED_COMPLEMENT_SUBSET_CIRCLE
   CONNECTED_COMPONENT_1_GEN CONNECTED_FINITE_IFF_SING
   CONNECTED_OPEN_IN_SPHERE_DELETE_EQ CONNECTED_SIMPLE_PATH_ENDLESS
   CONNECTED_SIMPLE_PATH_IMAGE CONNECTED_SPHERE_EQ
   CONTINUOUS_INJECTIVE_IMAGE_OPEN_SEGMENT_1 CONTINUOUS_ON_INVERSE_INTO_1D
   CONTRACTIBLE_CONVEX_TWEAK_BOUNDARY_POINTS CONTRACTIBLE_IMP_SIMPLY_CONNECTED
   CONVEX_IMP_SIMPLY_CONNECTED covering_space COVERING_SPACE_LIFT
   COVERING_SPACE_LIFT_INESSENTIAL_FUNCTION
   FRONTIER_MINIMAL_SEPARATING_CLOSED_POINTWISE FRONTIER_UNIONS_SUBSET_CLOSURE
   HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN HOMEOMORPHIC_PUNCTURED_SPHERE_UNIV
   HOMEOMORPHIC_SIMPLY_CONNECTED_EQ HOMEOMORPHISM_GROUPING_POINTS_EXISTS_GEN
   HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT HOMOTOPIC_WITH_SUBSET_RIGHT
   HOMOTOPY_EQUIVALENT_CARD_EQ_COMPONENTS
   HOMOTOPY_EQUIVALENT_COHOMOTOPIC_TRIVIALITY_NULL HOMOTOPY_EQUIVALENT_CONNECTEDNESS
   HOMOTOPY_EQUIVALENT_EMPTY HOMOTOPY_EQUIVALENT_HOMOTOPIC_TRIVIALITY_NULL
   HOMOTOPY_EQUIVALENT_SING INSIDE_INTER_OUTSIDE INSIDE_NO_OVERLAP INSIDE_OUTSIDE
   INVARIANCE_OF_DOMAIN JORDAN_BROUWER_FRONTIER JORDAN_BROUWER_NONSEPARATION
   JORDAN_BROUWER_SEPARATION JORDAN_INSIDE_OUTSIDE LOCALLY_CONNECTED_IM_KLEINEN
   LOCALLY_PATH_CONNECTED_SPHERE NONEMPTY_SIMPLE_PATH_ENDLESS
   NULLHOMOTOPIC_INTO_CONTRACTIBLE NULLHOMOTOPIC_NONSURJECTIVE_SPHERE_MAP_GEN
   NULLHOMOTOPIC_THROUGH_CONTRACTIBLE OUTSIDE OUTSIDE_IN_COMPONENTS OUTSIDE_INSIDE
   OUTSIDE_NO_OVERLAP OUTSIDE_UNION_OUTSIDE_UNION PATH_CONNECTED_ARCWISE
   PATH_CONNECTED_CONVEX_DIFF_COUNTABLE PATH_CONNECTED_OPEN_IN_DIFF_UNIONS_LOWDIM
   PATH_CONNECTED_PUNCTURED_UNIVERSE PATH_CONNECTED_SPHERE PATH_CONNECTED_UNIONS
   RELATIVE_FRONTIER_CBALL_INTER_AFFINE SIMPLE_PATH_IMP_ARC SIMPLE_PATH_JOIN_LOOP
   SIMPLE_PATH_JOIN_LOOP_EQ SIMPLE_PATH_REVERSEPATH SIMPLY_CONNECTED_EMPTY
   SIMPLY_CONNECTED_IMP_CONNECTED SIMPLY_CONNECTED_UNION STARLIKE_IMP_CONTRACTIBLE
   UNION_WITH_INSIDE : thm)
  deriving Inhabited

structure QConvexThms where
  (AFF_DIM_CBALL AFF_DIM_CONVEX_INTER_NONEMPTY_INTERIOR AFF_DIM_TRANSLATION_EQ
   AFFINE_HULL_CONVEX_INTER_NONEMPTY_INTERIOR AFFINE_HULL_OPEN_IN AFFINE_HULL_UNIV
   BOUNDED_RELATIVE_FRONTIER CHOOSE_AFFINE_SUBSET CLOSED_SEGMENT
   COMPACT_RELATIVE_FRONTIER COMPONENT_COMPLEMENT_CONNECTED
   CONVEX_CONTAINS_SEGMENT_EQ CONVEX_IMP_STARLIKE
   HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS
   RELATIVE_INTERIOR_CONVEX_INTER_AFFINE STARLIKE_UNIV SUBSPACE_EQ_AFFINE : thm)
  deriving Inhabited

structure QDerivativesThms where
  (DIFFERENTIABLE_ON_ADD DIFFERENTIABLE_ON_COMPOSE DIFFERENTIABLE_ON_ID
   DIFFERENTIABLE_ON_MUL : thm)
  deriving Inhabited

structure QVectorsThms where
  (COLLINEAR_3_DOT_MULTIPLES DIM_SUBSPACE_ORTHOGONAL_TO_VECTORS FSTCART_NEG
   ISOMETRY_SUBSET_SUBSPACE MIDPOINT_BETWEEN NORM_CAUCHY_SCHWARZ_EQUAL
   ORTHOGONAL_SUBSPACE_DECOMP_UNIQUE SNDCART_NEG SPAN_BREAKDOWN_EQ SUBSPACE_MUL_EQ
   SUBSPACE_NEG_EQ SUBSPACE_ORTHOGONAL_TO_VECTORS SUBSPACE_TRIVIAL : thm)
  deriving Inhabited

structure QMeasureThms where
  (CONTINUOUS_ON_MEASURE_IN_PORTION MEASURABLE_MEASURABLE_INTER_LEBESGUE_MEASURABLE
   NEGLIGIBLE_DIFFERENTIABLE_IMAGE_NEGLIGIBLE NEGLIGIBLE_HYPERPLANE NEGLIGIBLE_LOWDIM
   NOT_NEGLIGIBLE_UNIV : thm)
  deriving Inhabited

structure QDegreeThms where
  (ACCESSIBLE_FRONTIER_ANR_COMPLEMENT_COMPONENT
   ACCESSIBLE_FRONTIER_ANR_INTER_COMPLEMENT_COMPONENT ANR_IMP_NEIGHBOURHOOD_RETRACT
   ANR_PATH_IMAGE_SIMPLE_PATH ANR_SPHERE AR_SING BORSUK_HOMOTOPY_EXTENSION
   brouwer_degree brouwer_degree1 BROUWER_DEGREE1_CONST BROUWER_DEGREE1_EQ
   BROUWER_DEGREE1_HOMOTOPIC BROUWER_DEGREE1_ID BROUWER_DEGREE1_REFLECT_ALONG
   COHOMOTOPICALLY_TRIVIAL_1D COHOMOTOPICALLY_TRIVIAL_ON_COMPONENTS
   CONNECTED_ARC_COMPLEMENT CONNECTED_COMPLEMENT_ABSOLUTE_RETRACT CONTRACTIBLE_SPHERE
   ENR_IMP_ANR ENR_RELATIVE_FRONTIER_CONVEX
   FINITE_ANR_COMPLEMENT_COMPONENTS_CONCENTRIC HOMEOMORPHIC_ANRNESS
   HOMOTOPY_EQUIVALENT_RELATIVE_FRONTIER_PUNCTURED_AFFINE_HULL
   HOMOTOPY_EQUIVALENT_RELATIVE_FRONTIER_PUNCTURED_CONVEX
   LOCALLY_CONNECTED_SPHERE_GEN LOCALLY_PATH_CONNECTED_SPHERE_GEN
   NEIGHBOURHOOD_EXTENSION_INTO_ANR NO_RETRACTION_CBALL
   NULLHOMOTOPIC_INTO_RELATIVE_FRONTIER_EXTENSION NULLHOMOTOPIC_INTO_SPHERE_EXTENSION
   OPEN_IMP_ANR PATH_CONNECTED_INTERMEDIATE_CLOSURE_ANR_COMPLEMENT_COMPONENT
   PATH_CONNECTED_SPHERE_GEN PATH_CONNECTED_SUPERSET_COMPLEMENT_ARC_IMAGE
   RELATIVE_FRONTIER_RETRACT_OF_PUNCTURED_AFFINE_HULL retract_of RETRACTION
   retraction : thm)
  deriving Inhabited

structure QDeterminantsThms where
  (REFLECT_ALONG_GALOIS REFLECT_ALONG_NEG REFLECT_ALONG_REFL REFLECT_ALONG_SWITCH
   REFLECT_BASIS_ALONG_BASIS : thm)
  deriving Inhabited

structure QMetricThms where
  (CLOSED_IN_UNIONS CONTINUOUS_MAP_CASES_LE CONTINUOUS_MAP_EQ
   CONTINUOUS_MAP_FROM_SUBTOPOLOGY CONTINUOUS_MAP_ID
   CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE CONTINUOUS_MAP_REAL_ABS
   CONTINUOUS_MAP_REAL_CONST CONTINUOUS_MAP_REAL_MAX CONTINUOUS_MAP_REAL_MUL
   CONTINUOUS_MAP_REAL_RMUL CONTINUOUS_MAP_REAL_SUB : thm)
  deriving Inhabited

structure QHomologyThms where
  (BORSUK_ODD_MAPPING_DEGREE_STEP : thm)
  deriving Inhabited

structure QSessionThms where
  (DIMINDEX_FINITE_DIFF divides IN_GSPEC INT_MAX_LE MULT_EQ_1 num_divides
   UNIONS_MAXIMAL_SETS : thm)
  deriving Inhabited

structure QCardThms where
  (CARD_EQ_CARD_IMP CARD_EQ_IMAGE CARD_EQ_TRANS CARD_LE_CARD LE_C_IMAGE : thm)
  deriving Inhabited

structure QPolytopeThms where
  (AFFINE_IMP_POLYHEDRON CELL_COMPLEX_SUBDIVISION_EXISTS CHOOSE_POLYTOPE
   EMPTY_FACE_OF FACE_OF_AFF_DIM_LT FACE_OF_IMP_CLOSED FACE_OF_IMP_CONVEX
   FACE_OF_IMP_SUBSET FACE_OF_INTER FACE_OF_INTER_SUBFACE FACE_OF_POLYTOPE_POLYTOPE
   FACE_OF_REFL FACE_OF_REFL_EQ FACE_OF_SUBSET FACE_OF_SUBSET_RELATIVE_FRONTIER
   FACE_OF_TRANS facet_of FINITE_POLYTOPE_FACES POLYTOPE_IMP_BOUNDED
   POLYTOPE_IMP_CLOSED POLYTOPE_IMP_CONVEX POLYTOPE_IMP_POLYHEDRON
   POLYTOPE_INTER_POLYHEDRON POLYTOPE_INTERVAL RELATIVE_FRONTIER_OF_POLYHEDRON
   RELATIVE_FRONTIER_OF_POLYHEDRON_ALT RELATIVE_FRONTIER_OF_TRIANGLE : thm)
  deriving Inhabited

structure MoreTopDeps where
  ra : HolMultiLib.RealAnalysis.RealAnalysisDeps
  -- procedures added by hand (not reachable through the chain)
  INTEGER_RULE : term → ExceptT String IO thm
  EXCLUDED_MIDDLE : thm
  rza : HolMultiLib.RealAnalysis.RZA
  rzb : HolMultiLib.RealAnalysis.RZB
  rzc : HolMultiLib.RealAnalysis.RZC
  rzd : HolMultiLib.RealAnalysis.RZD
  rze : HolMultiLib.RealAnalysis.RZE
  rzf : HolMultiLib.RealAnalysis.RZF
  rzg : HolMultiLib.RealAnalysis.RZG
  rzh : HolMultiLib.RealAnalysis.RZH
  rzi : HolMultiLib.RealAnalysis.RZI
  rzj : HolMultiLib.RealAnalysis.RZJ
  rzk : HolMultiLib.RealAnalysis.RZK
  rzl : HolMultiLib.RealAnalysis.RZL
  rzm : HolMultiLib.RealAnalysis.RZM
  rzn : HolMultiLib.RealAnalysis.RZN
  rzo : HolMultiLib.RealAnalysis.RZO
  rzp : HolMultiLib.RealAnalysis.RZP
  rzq : HolMultiLib.RealAnalysis.RZQ
  rzr : HolMultiLib.RealAnalysis.RZR
  rzs : HolMultiLib.RealAnalysis.RZS
  rzt : HolMultiLib.RealAnalysis.RZT
  rzu : HolMultiLib.RealAnalysis.RZU
  rzv : HolMultiLib.RealAnalysis.RZV
  rzw : HolMultiLib.RealAnalysis.RZW
  rzx : HolMultiLib.RealAnalysis.RZX
  rzy : HolMultiLib.RealAnalysis.RZY
  rzz : HolMultiLib.RealAnalysis.RZZ
  rzaa : HolMultiLib.RealAnalysis.RZAA
  rzab : HolMultiLib.RealAnalysis.RZAB
  rzac : HolMultiLib.RealAnalysis.RZAC
  rzad : HolMultiLib.RealAnalysis.RZAD
  rzae : HolMultiLib.RealAnalysis.RZAE
  rzaf : HolMultiLib.RealAnalysis.RZAF
  rzag : HolMultiLib.RealAnalysis.RZAG
  rzah : HolMultiLib.RealAnalysis.RZAH
  rzai : HolMultiLib.RealAnalysis.RZAI
  rzaj : HolMultiLib.RealAnalysis.RZAJ
  rzak : HolMultiLib.RealAnalysis.RZAK
  rzal : HolMultiLib.RealAnalysis.RZAL
  rzam : HolMultiLib.RealAnalysis.RZAM
  rzan : HolMultiLib.RealAnalysis.RZAN
  rzao : HolMultiLib.RealAnalysis.RZAO
  rzap : HolMultiLib.RealAnalysis.RZAP
  rzaq : HolMultiLib.RealAnalysis.RZAQ
  rzar : HolMultiLib.RealAnalysis.RZAR
  rzas : HolMultiLib.RealAnalysis.RZAS
  rzat : HolMultiLib.RealAnalysis.RZAT
  rzau : HolMultiLib.RealAnalysis.RZAU
  rzav : HolMultiLib.RealAnalysis.RZAV
  rzaw : HolMultiLib.RealAnalysis.RZAW
  rzax : HolMultiLib.RealAnalysis.RZAX
  rzay : HolMultiLib.RealAnalysis.RZAY
  rzaz : HolMultiLib.RealAnalysis.RZAZ
  rzba : HolMultiLib.RealAnalysis.RZBA
  rzbb : HolMultiLib.RealAnalysis.RZBB
  rzbc : HolMultiLib.RealAnalysis.RZBC
  rzbd : HolMultiLib.RealAnalysis.RZBD
  rzbe : HolMultiLib.RealAnalysis.RZBE
  rzbf : HolMultiLib.RealAnalysis.RZBF
  rzbg : HolMultiLib.RealAnalysis.RZBG
  rzbh : HolMultiLib.RealAnalysis.RZBH
  rzbi : HolMultiLib.RealAnalysis.RZBI
  rzbj : HolMultiLib.RealAnalysis.RZBJ
  rzbk : HolMultiLib.RealAnalysis.RZBK
  rzbl : HolMultiLib.RealAnalysis.RZBL
  rzbm : HolMultiLib.RealAnalysis.RZBM
  rzbn : HolMultiLib.RealAnalysis.RZBN
  rzbo : HolMultiLib.RealAnalysis.RZBO
  rzbp : HolMultiLib.RealAnalysis.RZBP
  rzbq : HolMultiLib.RealAnalysis.RZBQ
  rzbr : HolMultiLib.RealAnalysis.RZBR
  rzbs : HolMultiLib.RealAnalysis.RZBS
  rzbt : HolMultiLib.RealAnalysis.RZBT
  rzbu : HolMultiLib.RealAnalysis.RZBU
  rzbv : HolMultiLib.RealAnalysis.RZBV
  rzbw : HolMultiLib.RealAnalysis.RZBW
  rzbx : HolMultiLib.RealAnalysis.RZBX
  rzby : HolMultiLib.RealAnalysis.RZBY
  rzbz : HolMultiLib.RealAnalysis.RZBZ
  rzca : HolMultiLib.RealAnalysis.RZCA
  rzcb : HolMultiLib.RealAnalysis.RZCB
  rzcc : HolMultiLib.RealAnalysis.RZCC
  rzcd : HolMultiLib.RealAnalysis.RZCD
  -- theorems
  qtopology : QTopologyThms
  qpaths : QPathsThms
  qconvex : QConvexThms
  qderivatives : QDerivativesThms
  qvectors : QVectorsThms
  qmeasure : QMeasureThms
  qdegree : QDegreeThms
  qdeterminants : QDeterminantsThms
  qmetric : QMetricThms
  qhomology : QHomologyThms
  qsession : QSessionThms
  qcard : QCardThms
  qpolytope : QPolytopeThms

/- ------------------------------------------------------------------------- -/
/- prioritize_complex(); injective maps into R are open maps; nonsurjectivity -/
/- of differentiable maps from a lower-dimensional sphere.                   -/
/- (moretop.ml 1-235)                                                       -/
/- ------------------------------------------------------------------------- -/

structure MOA where
  INJECTIVE_EQ_1D_OPEN_MAP_UNIV : thm
  NONSURJECTIVE_DIFFERENTIABLE_SPHEREMAP_LOWDIM : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOA [HolBase] (D : MoreTopDeps) : ExceptT String IO MOA := do
  -- @@SCOPE BEGIN
  let { REAL_DIFFERENTIABLE_AT, .. } := D.rzl
  let { REAL_DIFFERENTIABLE_ID, REAL_DIFFERENTIABLE_INV_ATREAL, .. } := D.rzo
  let { DIFFERENTIABLE_ON_NORM, .. } := D.rzq
  let { OPEN_SEGMENT_1, OPEN_SUBOPEN, .. } := D.qtopology
  let { CONTINUOUS_INJECTIVE_IMAGE_OPEN_SEGMENT_1, .. } := D.qpaths
  let { CONVEX_CONTAINS_SEGMENT_EQ, .. } := D.qconvex
  let { DIFFERENTIABLE_ON_ADD, DIFFERENTIABLE_ON_COMPOSE, DIFFERENTIABLE_ON_ID,
        DIFFERENTIABLE_ON_MUL, .. } := D.qderivatives
  let { DIM_SUBSPACE_ORTHOGONAL_TO_VECTORS, ORTHOGONAL_SUBSPACE_DECOMP_UNIQUE,
        SUBSPACE_ORTHOGONAL_TO_VECTORS, .. } := D.qvectors
  let { NEGLIGIBLE_DIFFERENTIABLE_IMAGE_NEGLIGIBLE, NEGLIGIBLE_LOWDIM, NOT_NEGLIGIBLE_UNIV,
        .. } := D.qmeasure
  let { DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON, .. } := D.ra.ts.qderivatives
  let { prioritize_complex, .. } := D.ra.ts.cn.cxa
  let { DIFFERENTIABLE_ON_LINEAR, DIFFERENTIABLE_ON_SUBSET,
        .. } := D.ra.ts.cn.ms.qderivatives
  let { NEGLIGIBLE_SUBSET, NEGLIGIBLE_UNION_EQ, .. } := D.ra.ts.cn.ms.qintegration3
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, NORM_ARITH,
        REAL_ARITH, SET_TAC, VECTOR_ARITH, .. } := D.ra.ts.cn.cx.cvx
  let { AND_FORALL_THM, CONTRAPOS_THM, EQ_IMP, ETA_AX, EXTENSION, FORALL_AND_THM,
        FORALL_IN_GSPEC, .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, FUN_IN_IMAGE, IMAGE_SUBSET, IMP_CONJ, IMP_CONJ_ALT, IN_DELETE,
        .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, IN_INTER, IN_SING, IN_UNION, IN_UNIV, LE_REFL, MONO_EXISTS,
        NOT_IMP, REAL_ABS_INV, .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_MUL_LINV, REAL_MUL_RID, REAL_MUL_RINV, RIGHT_FORALL_IMP_THM, SKOLEM_THM,
        SUBSET, SUBSET_ANTISYM_EQ, SUBSET_TRANS, .. } := D.ra.ts.cn.cx.cvx.core5
  let { o_DEF, SUBSET_UNIV, .. } := D.ra.ts.cn.cx.cvx.core6
  let { DIM_SUBSET, DIM_SUMS_INTER, DIM_UNIV, .. } := D.ra.ts.cn.cx.cvx.vec1
  let { DROP_ADD, DROP_SUB, INTERVAL_OPEN_SUBSET_CLOSED, LIFT_DROP, NORM_EQ_0,
        .. } := D.ra.ts.cn.cx.cvx.vec2
  let { NORM_LIFT, NORM_MUL, ORTHOGONAL_REFL, ORTHOGONAL_SUBSPACE_DECOMP_EXISTS,
        ORTHOGONAL_SYM, REAL_ABS_NORM, SPAN_OF_SUBSPACE, SUBSPACE_ADD, SUBSPACE_MUL,
        SUBSPACE_UNIV, .. } := D.ra.ts.cn.cx.cvx.vec3
  let { linear, VECTOR_ADD_LDISTRIB, VECTOR_ADD_LID, VECTOR_MUL_ASSOC, VECTOR_MUL_EQ_0,
        VECTOR_MUL_LID, .. } := D.ra.ts.cn.cx.cvx.vec4
  let { CONTINUOUS_ON_SUBSET, .. } := D.ra.ts.cn.cx.cvx.top3
  let { IN_INTERVAL_1, IN_SPHERE_0, OPEN_CONTAINS_CBALL, .. } := D.ra.ts.cn.cx.cvx.top4
  let { SEGMENT_1, SEGMENT_OPEN_SUBSET_CLOSED, .. } := D.ra.ts.cn.cx.cvx.top5
  let { CONTINUOUS_IVT_LOCAL_EXTREMUM, .. } := D.ra.ts.cn.ms.ig.dv.qpaths
  let { open_def, .. } := D.ra.ts.cn.ms.ig.dv.qtopology2
  let { BALL_1, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { DIM_EQ_0, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qvec
  let { CONVEX_CONTAINS_SEGMENT, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  let { IS_INTERVAL_CONVEX_1, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx3
  -- @@SCOPE END

  prioritize_complex

  -- Injective map into R is also an open map w.r.t. the universe, and this
  -- is actually an implication in both directions for an interval. Compare
  -- the local form in INJECTIVE_INTO_1D_IMP_OPEN_MAP (not a bi-implication).

  let INJECTIVE_EQ_1D_OPEN_MAP_UNIV ← prove
   r"!f:real^1->real^1 s.
        f continuous_on s /\ is_interval s
        ==>  ((!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) <=>
              (!t. open t /\ t SUBSET s ==> open(IMAGE f t)))"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
     [ONCE_REWRITE_TAC [OPEN_SUBOPEN] THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN
      X_GEN_TAC (← q r"x:real^1") THEN DISCH_TAC THEN
      FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [OPEN_CONTAINS_CBALL]) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"x:real^1")) THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [BALL_1] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"IMAGE (f:real^1->real^1)
                        (segment (x - lift d,x + lift d))") THEN
      MP_TAC (← ISPECL
       [← q r"f:real^1->real^1", ← q r"x - lift d", ← q r"x + lift d"]
       CONTINUOUS_INJECTIVE_IMAGE_OPEN_SEGMENT_1) THEN
      REWRITE_TAC [SEGMENT_1, DROP_ADD, DROP_SUB, LIFT_DROP] THEN
      ASM_CASES_TAC (← q r"drop x - d <= drop x + d") THENL
       [ASM_REWRITE_TAC [] THEN REWRITE_TAC [← GSYM SEGMENT_1],
        ASM_REAL_ARITH_TAC] THEN
      ANTS_TAC THENL [ASM_MESON_TAC [SUBSET, CONTINUOUS_ON_SUBSET], ALL_TAC] THEN
      REPEAT STRIP_TAC THENL
       [ASM_REWRITE_TAC [OPEN_SEGMENT_1],
        MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC [IN_INTERVAL_1] THEN
        REWRITE_TAC [DROP_ADD, DROP_SUB, LIFT_DROP] THEN ASM_REAL_ARITH_TAC,
        MATCH_MP_TAC IMAGE_SUBSET THEN
        ASM_MESON_TAC [INTERVAL_OPEN_SUBSET_CLOSED, SUBSET_TRANS]],
      MATCH_MP_TAC (← TAUT (← q r"(~p ==> F) ==> p")) THEN DISCH_TAC THEN
      MP_TAC (← ISPECL [← q r"f:real^1->real^1", ← q r"x:real^1", ← q r"y:real^1"]
          CONTINUOUS_IVT_LOCAL_EXTREMUM) THEN
      ASM_REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL
       [ASM_MESON_TAC [CONVEX_CONTAINS_SEGMENT_EQ, IS_INTERVAL_CONVEX_1,
                       CONTINUOUS_ON_SUBSET],
        DISCH_THEN (X_CHOOSE_TAC (← q r"z:real^1")) THEN
        FIRST_ASSUM (MP_TAC o SPEC (← q r"segment(x:real^1,y)")) THEN
        REWRITE_TAC [OPEN_SEGMENT_1, NOT_IMP] THEN CONJ_TAC THENL
         [ASM_MESON_TAC [CONVEX_CONTAINS_SEGMENT, IS_INTERVAL_CONVEX_1,
                         SUBSET_TRANS, SEGMENT_OPEN_SUBSET_CLOSED],
          FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC) THEN
          REWRITE_TAC [open_def, FORALL_IN_IMAGE] THEN
          DISCH_THEN (MP_TAC o SPEC (← q r"z:real^1")) THEN ASM_REWRITE_TAC [] THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"e:real")
           (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
          FIRST_X_ASSUM DISJ_CASES_TAC THENL
           [DISCH_THEN (MP_TAC o SPEC (← q r"(f:real^1->real^1) z + lift(e / &2)")),
            DISCH_THEN (MP_TAC o SPEC (← q r"(f:real^1->real^1) z - lift(e / &2)"))] THEN
          ASM_REWRITE_TAC [← NORM_ARITH (← q r"dist(a + b:real^N,a) = norm b"),
                           ← NORM_ARITH (← q r"dist(a - b:real^N,a) = norm b"), NORM_LIFT,
                           ← REAL_ARITH (← q r"abs(e / &2) < e <=> &0 < e")] THEN
          REWRITE_TAC [IN_IMAGE] THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"w:real^1") (STRIP_ASSUME_TAC o GSYM)) THEN
          FIRST_X_ASSUM (MP_TAC o SPEC (← q r"w:real^1")) THEN
          ASM_SIMP_TAC [← REWRITE_RULE [SUBSET] SEGMENT_OPEN_SUBSET_CLOSED] THEN
          REWRITE_TAC [DROP_ADD, DROP_SUB, LIFT_DROP] THEN
          ASM_REAL_ARITH_TAC]]])

  -- Nonsurjectivity of differentiable map from lower-dimensional sphere.

  let NONSURJECTIVE_DIFFERENTIABLE_SPHEREMAP_LOWDIM ← prove
   r"!f:real^N->real^N s t.
      subspace s /\ subspace t /\ dim s < dim t /\ s SUBSET t /\
      f differentiable_on sphere(vec 0,&1) INTER s
      ==> ~(IMAGE f (sphere(vec 0,&1) INTER s) = sphere(vec 0,&1) INTER t)"
   (REPEAT STRIP_TAC THEN
    ABBREV_TAC
     (← q r"(g:real^N->real^N) =
      \x. norm(x) % (f:real^N->real^N)(inv(norm x) % x)") THEN
    SUBGOAL_THEN
     (← q r"(g:real^N->real^N) differentiable_on s DELETE (vec 0)")
    ASSUME_TAC THENL
     [EXPAND_TAC "g" THEN MATCH_MP_TAC DIFFERENTIABLE_ON_MUL THEN
      SIMP_TAC [o_DEF, DIFFERENTIABLE_ON_NORM, IN_DELETE] THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
      MATCH_MP_TAC DIFFERENTIABLE_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_ON_MUL THEN
        REWRITE_TAC [DIFFERENTIABLE_ON_ID] THEN
        SUBGOAL_THEN
         (← q r"lift o (\x:real^N. inv(norm x)) =
          (lift o inv o drop) o (\x. lift(norm x))")
        SUBST1_TAC THENL [REWRITE_TAC [o_DEF, LIFT_DROP], ALL_TAC] THEN
        MATCH_MP_TAC DIFFERENTIABLE_ON_COMPOSE THEN
        SIMP_TAC [DIFFERENTIABLE_ON_NORM, IN_DELETE] THEN
        MATCH_MP_TAC DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON THEN
        SIMP_TAC [FORALL_IN_IMAGE, IN_DELETE, ← GSYM REAL_DIFFERENTIABLE_AT] THEN
        REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM ETA_AX] THEN
        MATCH_MP_TAC REAL_DIFFERENTIABLE_INV_ATREAL THEN
        ASM_REWRITE_TAC [REAL_DIFFERENTIABLE_ID, NORM_EQ_0],
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
            DIFFERENTIABLE_ON_SUBSET)) THEN
        ASM_SIMP_TAC [SUBSET, FORALL_IN_IMAGE, IN_SPHERE_0, IN_INTER,
                      SUBSPACE_MUL, NORM_MUL, IN_DELETE] THEN
        SIMP_TAC [REAL_ABS_INV, REAL_ABS_NORM, REAL_MUL_LINV, NORM_EQ_0]],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"IMAGE (g:real^N->real^N) (s DELETE vec 0) = t DELETE (vec 0)")
    ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"IMAGE (f:real^N->real^N) (sphere (vec 0,&1) INTER s) =
                   sphere (vec 0,&1) INTER t") THEN
      REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_DELETE,
                   IN_INTER, IN_SPHERE_0] THEN
      EXPAND_TAC "g" THEN REWRITE_TAC [IN_IMAGE, IN_INTER, IN_SPHERE_0] THEN
      SIMP_TAC [IN_DELETE, VECTOR_MUL_EQ_0, NORM_EQ_0] THEN
      MATCH_MP_TAC (← TAUT
       (← q r"(p ==> r) /\ (p ==> q ==> s) ==> p /\ q ==> r /\ s")) THEN
      CONJ_TAC THENL [ALL_TAC, DISCH_TAC] THEN
      DISCH_THEN (fun th => tactic_of do
        pure (X_GEN_TAC (← q r"x:real^N") THEN STRIP_TAC THEN
              MP_TAC (← SPEC (← q r"inv(norm x) % x:real^N") th))) THEN
      ASM_SIMP_TAC [SUBSPACE_MUL, NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM,
                    REAL_MUL_LINV, NORM_EQ_0,
                    ← NORM_ARITH (← q r"norm x = &1 ==> ~(x:real^N = vec 0)")] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"y:real^N") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"norm(x:real^N) % y:real^N") THEN
      ASM_SIMP_TAC [SUBSPACE_MUL, NORM_MUL, REAL_ABS_NORM, REAL_MUL_RID] THEN
      ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, NORM_EQ_0] THEN
      ASM_REWRITE_TAC [VECTOR_MUL_LID, VECTOR_MUL_EQ_0, NORM_EQ_0] THEN
      ASM_SIMP_TAC [← NORM_ARITH (← q r"norm x = &1 ==> ~(x:real^N = vec 0)")] THEN
      UNDISCH_THEN (← q r"inv(norm x) % x = (f:real^N->real^N) y")
       (SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_RINV, NORM_EQ_0] THEN
      REWRITE_TAC [VECTOR_MUL_LID],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"t:real^N->bool", ← q r"(:real^N)"]
          DIM_SUBSPACE_ORTHOGONAL_TO_VECTORS) THEN
    ASM_REWRITE_TAC [SUBSPACE_UNIV, DIM_UNIV, IN_UNIV, SUBSET_UNIV] THEN
    ABBREV_TAC (← q r"t' = {y:real^N | !x. x IN t ==> orthogonal x y}") THEN
    DISCH_TAC THEN
    SUBGOAL_THEN (← q r"subspace(t':real^N->bool)") ASSUME_TAC THENL
     [EXPAND_TAC "t'" THEN REWRITE_TAC [SUBSPACE_ORTHOGONAL_TO_VECTORS],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"?fst snd. linear fst /\ linear snd /\
                (!z. fst(z) IN t /\ snd z IN t' /\ fst z + snd z = z) /\
                (!x y:real^N. x IN t /\ y IN t'
                              ==> fst(x + y) = x /\ snd(x + y) = y)")
    STRIP_ASSUME_TAC THENL
     [MP_TAC (← ISPEC (← q r"t:real^N->bool") ORTHOGONAL_SUBSPACE_DECOMP_EXISTS) THEN
      REWRITE_TAC [SKOLEM_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"fst:real^N->real^N") THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"snd:real^N->real^N") THEN
      DISCH_THEN (MP_TAC o GSYM) THEN
      ASM_SIMP_TAC [SPAN_OF_SUBSPACE, FORALL_AND_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC (← TAUT (← q r"r /\ (r ==> p /\ q /\ s) ==> p /\ q /\ r /\ s")) THEN
      CONJ_TAC THENL
       [EXPAND_TAC "t'" THEN REWRITE_TAC [IN_ELIM_THM] THEN
        ASM_MESON_TAC [ORTHOGONAL_SYM],
        DISCH_TAC] THEN
      MATCH_MP_TAC (← TAUT (← q r"r /\ (r ==> p /\ q) ==> p /\ q /\ r")) THEN
      CONJ_TAC THENL
       [REPEAT GEN_TAC THEN STRIP_TAC THEN
        MATCH_MP_TAC ORTHOGONAL_SUBSPACE_DECOMP_UNIQUE THEN
        MAP_EVERY EXISTS_TAC [← q r"t:real^N->bool", ← q r"t':real^N->bool"] THEN
        ASM_SIMP_TAC [SPAN_OF_SUBSPACE] THEN ASM SET_TAC [],
        DISCH_TAC] THEN
      REWRITE_TAC [linear] THEN
      MATCH_MP_TAC (← TAUT (← q r"(p /\ r) /\ (q /\ s) ==> (p /\ q) /\ (r /\ s)")) THEN
      REWRITE_TAC [AND_FORALL_THM] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
      MATCH_MP_TAC ORTHOGONAL_SUBSPACE_DECOMP_UNIQUE THEN
      MAP_EVERY EXISTS_TAC [← q r"t:real^N->bool", ← q r"t':real^N->bool"] THEN
      ASM_SIMP_TAC [SPAN_OF_SUBSPACE, SUBSPACE_ADD, SUBSPACE_MUL] THEN
      (CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN
      ASM_REWRITE_TAC [← GSYM VECTOR_ADD_LDISTRIB] THEN
      ONCE_REWRITE_TAC [← VECTOR_ARITH
       (← q r"(x + y) + (x' + y'):real^N = (x + x') + (y + y')")] THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"\x:real^N. (g:real^N->real^N)(fst x) + snd x",
      ← q r"{x + y:real^N | x IN (s DELETE vec 0) /\ y IN t'}"]
        NEGLIGIBLE_DIFFERENTIABLE_IMAGE_NEGLIGIBLE) THEN
    REWRITE_TAC [LE_REFL, NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_LOWDIM THEN
      MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"t':real^N->bool"] DIM_SUMS_INTER) THEN
      ASM_REWRITE_TAC [IN_DELETE] THEN
      FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← ARITH_RULE
       (← q r"t' + t = n ==> s < t /\ d' <= d /\ i = 0
           ==> d + i = s + t' ==> d' < n"))) THEN
      ASM_REWRITE_TAC [DIM_EQ_0] THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIM_SUBSET THEN SET_TAC [], EXPAND_TAC "t'"] THEN
      REWRITE_TAC [SUBSET, IN_INTER, IN_SING, IN_ELIM_THM] THEN
      ASM_MESON_TAC [SUBSET, ORTHOGONAL_REFL],
      MATCH_MP_TAC DIFFERENTIABLE_ON_ADD THEN
      ASM_SIMP_TAC [DIFFERENTIABLE_ON_LINEAR] THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
      MATCH_MP_TAC DIFFERENTIABLE_ON_COMPOSE THEN
      ASM_SIMP_TAC [DIFFERENTIABLE_ON_LINEAR] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
        DIFFERENTIABLE_ON_SUBSET)) THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_IN_GSPEC] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [SUBSET]) THEN ASM_SIMP_TAC [IN_DELETE],
      SUBGOAL_THEN
       (← q r"~negligible {x + y | x IN IMAGE (g:real^N->real^N) (s DELETE vec 0) /\
                             y IN t'}")
      MP_TAC THENL
       [ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN (← q r"negligible(t':real^N->bool)") MP_TAC THENL
         [MATCH_MP_TAC NEGLIGIBLE_LOWDIM THEN ASM_ARITH_TAC,
          REWRITE_TAC [← TAUT (← q r"p ==> ~q <=> ~(p /\ q)")]] THEN
        REWRITE_TAC [← GSYM NEGLIGIBLE_UNION_EQ] THEN
        MP_TAC NOT_NEGLIGIBLE_UNIV THEN MATCH_MP_TAC EQ_IMP THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC [EXTENSION, IN_UNION, IN_UNIV, IN_ELIM_THM, IN_DELETE] THEN
        X_GEN_TAC (← q r"z:real^N") THEN
        REWRITE_TAC [← TAUT (← q r"p \/ q <=> ~p ==> q")] THEN DISCH_TAC THEN
        EXISTS_TAC (← q r"(fst:real^N->real^N) z") THEN
        EXISTS_TAC (← q r"(snd:real^N->real^N) z") THEN
        ASM_SIMP_TAC [] THEN ASM_MESON_TAC [VECTOR_ADD_LID],
        REWRITE_TAC [CONTRAPOS_THM] THEN
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
        REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, IMP_CONJ, RIGHT_FORALL_IMP_THM,
                     FORALL_IN_IMAGE, IN_DELETE] THEN
        X_GEN_TAC (← q r"x:real^N") THEN REPEAT DISCH_TAC THEN
        X_GEN_TAC (← q r"y:real^N") THEN DISCH_TAC THEN
        REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"x + y:real^N") THEN
        RULE_ASSUM_TAC (REWRITE_RULE [SUBSET]) THEN ASM_SIMP_TAC [] THEN ASM
        SET_TAC []]])

  pure { INJECTIVE_EQ_1D_OPEN_MAP_UNIV, NONSURJECTIVE_DIFFERENTIABLE_SPHEREMAP_LOWDIM }

/- ------------------------------------------------------------------------- -/
/- Map f:S^m->S^n for m < n is nullhomotopic.                                -/
/- (moretop.ml 236-517)                                                     -/
/- ------------------------------------------------------------------------- -/

structure MOB where
  INESSENTIAL_SPHEREMAP_LOWDIM_GEN : thm
  INESSENTIAL_SPHEREMAP_LOWDIM : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOB [HolBase] (D : MoreTopDeps) (BMOA : MOA) : ExceptT String IO MOB := do
  -- @@SCOPE BEGIN
  let { NONSURJECTIVE_DIFFERENTIABLE_SPHEREMAP_LOWDIM, .. } := BMOA
  let { REAL_DIFFERENTIABLE_AT, .. } := D.rzl
  let { REAL_DIFFERENTIABLE_ID, REAL_DIFFERENTIABLE_INV_ATREAL, .. } := D.rzo
  let { DIFFERENTIABLE_ON_NORM, .. } := D.rzq
  let { CONTINUOUS_ON_VECTOR_POLYNOMIAL_FUNCTION, .. } := D.rzbj
  let { STONE_WEIERSTRASS_VECTOR_POLYNOMIAL_FUNCTION_SUBSPACE, .. } := D.rzbk
  let { DIFFERENTIABLE_ON_VECTOR_POLYNOMIAL_FUNCTION, .. } := D.rzbl
  let { HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT, HOMOTOPY_EQUIVALENT_COHOMOTOPIC_TRIVIALITY_NULL,
        HOMOTOPY_EQUIVALENT_HOMOTOPIC_TRIVIALITY_NULL, NULLHOMOTOPIC_INTO_CONTRACTIBLE,
        .. } := D.qpaths
  let { AFF_DIM_CBALL, HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS,
        .. } := D.qconvex
  let { DIFFERENTIABLE_ON_COMPOSE, DIFFERENTIABLE_ON_MUL, .. } := D.qderivatives
  let { MIDPOINT_BETWEEN, SUBSPACE_TRIVIAL, .. } := D.qvectors
  let { CONTRACTIBLE_SPHERE, .. } := D.qdegree
  let { DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON, .. } := D.ra.ts.qderivatives
  let { SEGMENT_BOUND, .. } := D.ra.ts.cn.qconvex
  let { ASM_INT_ARITH_TAC, GEOM_ORIGIN_TAC, MESON, NORM_ARITH, REAL_RAT_REDUCE_CONV,
        SET_RULE, SET_TAC, VECTOR_ARITH, .. } := D.ra.ts.cn.cx.cvx
  let { DIFFERENTIABLE_IMP_CONTINUOUS_ON, .. } := D.ra.ts.cn.ms.ig.qderivatives
  let { ARITH_EQ, CONJ_ASSOC, ETA_AX, .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, IMAGE_CLAUSES, IMP_CONJ, IMP_CONJ_ALT, IMP_IMP, IN_DELETE,
        IN_DIFF, INSERT_SUBSET, INT_OF_NUM_EQ, INT_OF_NUM_LE, INT_OF_NUM_LT, INTER_COMM,
        .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_IMAGE, IN_INTER, LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY, MONO_EXISTS,
        NOT_IN_EMPTY, PCROSS_EMPTY, REAL_ABS_INV, REAL_ABS_MUL,
        .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_INV_1, REAL_LT_01, .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_LINV, REAL_NOT_LE, REAL_OF_NUM_EQ, RIGHT_FORALL_IMP_THM,
        RIGHT_IMP_FORALL_THM, SING_SUBSET, SUBSET, .. } := D.ra.ts.cn.cx.cvx.core5
  let { o_DEF, o_THM, .. } := D.ra.ts.cn.cx.cvx.core6
  let { HULL_INC, HULL_MINIMAL, .. } := D.ra.ts.cn.cx.cvx.misc
  let { CHOOSE_SUBSPACE_OF_SUBSPACE, DIM_UNIV, DIST_0, .. } := D.ra.ts.cn.cx.cvx.vec1
  let { LIFT_DROP, NORM_0, NORM_EQ_0, .. } := D.ra.ts.cn.cx.cvx.vec2
  let { NORM_MUL, NORM_NEG, REAL_ABS_NORM, SPAN_OF_SUBSPACE, SUBSPACE_0, SUBSPACE_MUL,
        SUBSPACE_NEG, SUBSPACE_UNIV, .. } := D.ra.ts.cn.cx.cvx.vec3
  let { midpoint, VECTOR_MUL_LID, .. } := D.ra.ts.cn.cx.cvx.vec4
  let { BALL_EQ_EMPTY, BETWEEN_IN_SEGMENT, BOUNDED_BALL, BOUNDED_CBALL, CENTRE_IN_BALL,
        CLOSED_SUBSPACE, .. } := D.ra.ts.cn.cx.cvx.top1
  let { COMPACT_INTER_CLOSED, COMPACT_SPHERE, .. } := D.ra.ts.cn.cx.cvx.top2
  let { CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID, CONTINUOUS_ON_INV, CONTINUOUS_ON_LIFT_NORM,
        CONTINUOUS_ON_MUL, FRONTIER_BALL, FRONTIER_CBALL, HOMEOMORPHIC_EMPTY,
        HOMEOMORPHIC_REFL, .. } := D.ra.ts.cn.cx.cvx.top3
  let { HOMEOMORPHIC_TRANS, IN_SPHERE_0, INTERIOR_CBALL, INTERIOR_OPEN, OPEN_BALL,
        .. } := D.ra.ts.cn.cx.cvx.top4
  let { TOPSPACE_EUCLIDEAN_SUBTOPOLOGY, .. } := D.ra.ts.cn.cx.cvx.top5
  let { AFF_DIM_CONVEX_INTER_OPEN, AFF_DIM_DIM_SUBSPACE, RELATIVE_FRONTIER_EMPTY,
        SUBSPACE_IMP_AFFINE, SUBSPACE_IMP_CONVEX, .. } := D.ra.ts.cn.ms.ig.dv.dg.qconvex
  let { HOMOTOPIC_WITH_EQ, HOMOTOPIC_WITH_TRANS, .. } := D.ra.ts.cn.ms.ig.dv.dg.qmetric
  let { HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT, HOMOTOPIC_WITH_EUCLIDEAN_ALT,
        HOMOTOPIC_WITH_LINEAR, .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths1
  let { NULLHOMOTOPIC_FROM_CONTRACTIBLE, RELATIVE_FRONTIER_CONVEX_INTER_AFFINE,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths2
  let { CONTINUOUS_ON_EMPTY, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { INT_NOT_LE, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qses
  let { BOUNDED_INTER, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qtop
  let { AFF_DIM_DIM_0, AFF_DIM_EMPTY, AFF_DIM_GE, AFF_DIM_LE_UNIV,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx1
  let { CONVEX_BALL, CONVEX_CBALL, CONVEX_INTER, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  let { RELATIVE_FRONTIER_NONEMPTY_INTERIOR, SEGMENT_CONVEX_HULL,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx3
  -- @@SCOPE END

  let INESSENTIAL_SPHEREMAP_LOWDIM_GEN ← (do
    let lemma1 ← prove
     r"!f:real^N->real^N s t.
            subspace s /\ subspace t /\ dim s < dim t /\ s SUBSET t /\
            f continuous_on sphere(vec 0,&1) INTER s /\
            IMAGE f (sphere(vec 0,&1) INTER s) SUBSET sphere(vec 0,&1) INTER t
            ==> ?c. homotopic_with (\x. T)
                      (subtopology euclidean (sphere(vec 0,&1) INTER s),
                       subtopology euclidean (sphere(vec 0,&1) INTER t))
                       f (\x. c)"
     (REPEAT STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"f:real^N->real^N", ← q r"sphere(vec 0:real^N,&1) INTER s",
                        ← q r"&1 / &2", ← q r"t:real^N->bool"]
            STONE_WEIERSTRASS_VECTOR_POLYNOMIAL_FUNCTION_SUBSPACE) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_SIMP_TAC [COMPACT_INTER_CLOSED, COMPACT_SPHERE, CLOSED_SUBSPACE] THEN
      ANTS_TAC THENL [ASM SET_TAC [], REWRITE_TAC [SUBSET, FORALL_IN_IMAGE]] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->real^N") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       (← q r"!x. x IN sphere(vec 0,&1) INTER s ==> ~((g:real^N->real^N) x = vec 0)")
      ASSUME_TAC THENL
       [X_GEN_TAC (← q r"x:real^N") THEN STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real^N")) THEN ASM_REWRITE_TAC [] THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [SUBSET]) THEN
        REWRITE_TAC [FORALL_IN_IMAGE, IN_SPHERE_0] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [IN_SPHERE_0]) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"x:real^N")) THEN
        ASM_REWRITE_TAC [] THEN REWRITE_TAC [IN_INTER, IN_SPHERE_0] THEN
        CONV_TAC (fun t => NORM_ARITH t),
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(g:real^N->real^N) differentiable_on
                    sphere(vec 0,&1) INTER s")
      ASSUME_TAC THENL
       [ASM_SIMP_TAC [DIFFERENTIABLE_ON_VECTOR_POLYNOMIAL_FUNCTION], ALL_TAC] THEN
      ABBREV_TAC (← q r"(h:real^N->real^N) = \x. inv(norm(g x)) % g x") THEN
      SUBGOAL_THEN
       (← q r"!x. x IN sphere(vec 0,&1) INTER s
            ==> (h:real^N->real^N) x IN sphere(vec 0,&1) INTER t")
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN
        ASM_SIMP_TAC [SUBSPACE_MUL, IN_INTER, IN_SPHERE_0, NORM_MUL] THEN
        REWRITE_TAC [REAL_ABS_INV, REAL_ABS_NORM] THEN
        ASM_SIMP_TAC [REAL_MUL_LINV, NORM_EQ_0, ← GSYM IN_SPHERE_0],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"(h:real^N->real^N) differentiable_on sphere(vec 0,&1) INTER s")
      ASSUME_TAC THENL
       [EXPAND_TAC "h" THEN MATCH_MP_TAC DIFFERENTIABLE_ON_MUL THEN
        ASM_SIMP_TAC [DIFFERENTIABLE_ON_VECTOR_POLYNOMIAL_FUNCTION, o_DEF] THEN
        SUBGOAL_THEN
         (← q r"(\x. lift(inv(norm((g:real^N->real^N) x)))) =
          (lift o inv o drop) o (\x. lift(norm x)) o (g:real^N->real^N)")
        SUBST1_TAC THENL [REWRITE_TAC [o_DEF, LIFT_DROP], ALL_TAC] THEN
        MATCH_MP_TAC DIFFERENTIABLE_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC DIFFERENTIABLE_ON_COMPOSE THEN
          ASM_SIMP_TAC [DIFFERENTIABLE_ON_VECTOR_POLYNOMIAL_FUNCTION] THEN
          MATCH_MP_TAC DIFFERENTIABLE_ON_NORM THEN
          ASM_REWRITE_TAC [← SET_RULE
           (← q r"~(z IN IMAGE f s) <=> !x. x IN s ==> ~(f x = z)")],
          MATCH_MP_TAC DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON THEN
          REWRITE_TAC [← GSYM REAL_DIFFERENTIABLE_AT] THEN
          REWRITE_TAC [FORALL_IN_IMAGE, IN_SPHERE_0] THEN
          X_GEN_TAC (← q r"x:real^N") THEN
          ASM_CASES_TAC (← q r"x:real^N = vec 0") THEN
          ASM_REWRITE_TAC [NORM_0, REAL_OF_NUM_EQ, ARITH_EQ] THEN DISCH_TAC THEN
          REWRITE_TAC [← GSYM REAL_DIFFERENTIABLE_AT, o_THM] THEN
          GEN_REWRITE_TAC LAND_CONV [← GSYM ETA_AX] THEN
          MATCH_MP_TAC REAL_DIFFERENTIABLE_INV_ATREAL THEN
          ASM_SIMP_TAC [REAL_DIFFERENTIABLE_ID, NORM_EQ_0, IN_SPHERE_0]],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"?c. homotopic_with (\z. T)
               (subtopology euclidean (sphere(vec 0,&1) INTER s),
                subtopology euclidean (sphere(vec 0,&1) INTER t))
               (h:real^N->real^N) (\x. c)")
      MP_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] HOMOTOPIC_WITH_TRANS) THEN
        SUBGOAL_THEN
         (← q r"homotopic_with (\z. T)
           (subtopology euclidean (sphere(vec 0:real^N,&1) INTER s),
            subtopology euclidean (t DELETE (vec 0:real^N)))
           f g")
        MP_TAC THENL
         [MATCH_MP_TAC HOMOTOPIC_WITH_LINEAR THEN
          ASM_SIMP_TAC [CONTINUOUS_ON_VECTOR_POLYNOMIAL_FUNCTION] THEN
          X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN REWRITE_TAC [← SET_RULE
            (← q r"s SUBSET t DELETE v <=> s SUBSET t /\ ~(v IN s)")] THEN
          CONJ_TAC THENL
           [REWRITE_TAC [SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
            ASM_SIMP_TAC [SUBSPACE_IMP_CONVEX] THEN ASM SET_TAC [],
            DISCH_THEN (MP_TAC o MATCH_MP SEGMENT_BOUND) THEN
            SUBGOAL_THEN
             (← q r"(f:real^N->real^N) x IN sphere(vec 0,&1) /\
              norm(f x - g x) < &1/ &2")
            MP_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
            REWRITE_TAC [IN_SPHERE_0] THEN CONV_TAC (fun t => NORM_ARITH t)],
          DISCH_THEN (MP_TAC o
            ISPECL [← q r"\y:real^N. inv(norm y) % y",
                    ← q r"sphere(vec 0:real^N,&1) INTER t"] o
            MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ]
            HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT)) THEN
          ASM_REWRITE_TAC [o_DEF] THEN ANTS_TAC THENL
           [CONJ_TAC THENL
             [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
              REWRITE_TAC [o_DEF, CONTINUOUS_ON_ID] THEN
              MATCH_MP_TAC (← REWRITE_RULE [o_DEF] CONTINUOUS_ON_INV) THEN
              SIMP_TAC [IN_DELETE, NORM_EQ_0] THEN
              REWRITE_TAC [← REWRITE_RULE [o_DEF] CONTINUOUS_ON_LIFT_NORM],
              REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_DELETE, IN_INTER] THEN
              ASM_SIMP_TAC [SUBSPACE_MUL, IN_SPHERE_0, NORM_MUL,
                            REAL_ABS_MUL] THEN
              SIMP_TAC [REAL_ABS_INV, REAL_ABS_NORM, REAL_MUL_LINV, NORM_EQ_0]],
            MATCH_MP_TAC (← ONCE_REWRITE_RULE [IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
            REWRITE_TAC [TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
            RULE_ASSUM_TAC (REWRITE_RULE
             [SUBSET, IN_INTER, FORALL_IN_IMAGE, IN_SPHERE_0]) THEN
            ASM_SIMP_TAC [IN_SPHERE_0, IN_INTER,
                          REAL_INV_1, VECTOR_MUL_LID]]]] THEN
      SUBGOAL_THEN
       (← q r"?c. c IN (sphere(vec 0,&1) INTER t) DIFF
                 (IMAGE (h:real^N->real^N) (sphere(vec 0,&1) INTER s))")
      MP_TAC THENL
       [MATCH_MP_TAC (← SET_RULE
         (← q r"t SUBSET s /\ ~(t = s) ==> ?a. a IN s DIFF t")) THEN CONJ_TAC THENL
         [ASM SET_TAC [],
          MATCH_MP_TAC NONSURJECTIVE_DIFFERENTIABLE_SPHEREMAP_LOWDIM] THEN
        ASM_REWRITE_TAC [],
        REWRITE_TAC [LEFT_IMP_EXISTS_THM, IN_INTER, IN_DIFF, IN_IMAGE] THEN
        REWRITE_TAC [← SET_RULE
         (← q r"~(?x. P x /\ x IN s /\ x IN t) <=>
          (!x. x IN s INTER t ==> ~(P x))")] THEN
        X_GEN_TAC (← q r"c:real^N") THEN STRIP_TAC] THEN
      EXISTS_TAC (← q r"--c:real^N") THEN
      SUBGOAL_THEN
       (← q r"homotopic_with (\z. T)
         (subtopology euclidean (sphere(vec 0:real^N,&1) INTER s),
          subtopology euclidean (t DELETE (vec 0:real^N)))
         h (\x. --c)")
      MP_TAC THENL
       [MATCH_MP_TAC HOMOTOPIC_WITH_LINEAR THEN
        ASM_SIMP_TAC [DIFFERENTIABLE_IMP_CONTINUOUS_ON, CONTINUOUS_ON_CONST] THEN
        X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN REWRITE_TAC [← SET_RULE
          (← q r"s SUBSET t DELETE v <=> s SUBSET t /\ ~(v IN s)")] THEN
        CONJ_TAC THENL
         [REWRITE_TAC [SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
          ASM_SIMP_TAC [SUBSPACE_IMP_CONVEX, INSERT_SUBSET, SUBSPACE_NEG] THEN
          ASM SET_TAC [],
          DISCH_TAC THEN MP_TAC (← ISPECL
           [← q r"(h:real^N->real^N) x", ← q r"vec 0:real^N", ← q r"--c:real^N"]
           MIDPOINT_BETWEEN) THEN
          ASM_REWRITE_TAC [BETWEEN_IN_SEGMENT, DIST_0, NORM_NEG] THEN
          SUBGOAL_THEN (← q r"((h:real^N->real^N) x) IN sphere(vec 0,&1) /\
                        (c:real^N) IN sphere(vec 0,&1)")
          MP_TAC THENL [ASM SET_TAC [], SIMP_TAC [IN_SPHERE_0]] THEN
          STRIP_TAC THEN REWRITE_TAC [midpoint, ← VECTOR_ARITH
           (← q r"vec 0:real^N = inv(&2) % (x + --y) <=> x = y")] THEN
          ASM SET_TAC []],
        DISCH_THEN (MP_TAC o
          ISPECL [← q r"\y:real^N. inv(norm y) % y",
                  ← q r"sphere(vec 0:real^N,&1) INTER t"] o
          MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ]
          HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT)) THEN
        ASM_REWRITE_TAC [o_DEF] THEN ANTS_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
            REWRITE_TAC [o_DEF, CONTINUOUS_ON_ID] THEN
            MATCH_MP_TAC (← REWRITE_RULE [o_DEF] CONTINUOUS_ON_INV) THEN
            SIMP_TAC [IN_DELETE, NORM_EQ_0] THEN
            REWRITE_TAC [← REWRITE_RULE [o_DEF] CONTINUOUS_ON_LIFT_NORM],
            REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_DELETE, IN_INTER] THEN
            ASM_SIMP_TAC [SUBSPACE_MUL, IN_SPHERE_0, NORM_MUL, REAL_ABS_MUL] THEN
            SIMP_TAC [REAL_ABS_INV, REAL_ABS_NORM, REAL_MUL_LINV, NORM_EQ_0]],
          MATCH_MP_TAC (← ONCE_REWRITE_RULE [IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
          REWRITE_TAC [TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
          RULE_ASSUM_TAC (REWRITE_RULE
           [SUBSET, IN_INTER, FORALL_IN_IMAGE, IN_SPHERE_0]) THEN
          ASM_SIMP_TAC [IN_SPHERE_0, IN_INTER, REAL_INV_1, VECTOR_MUL_LID,
                        NORM_NEG]]])
    let lemma2 ← prove
     r"!s:real^M->bool u:real^N->bool.
            bounded s /\ convex s /\ subspace u /\ aff_dim s <= &(dim u)
            ==> ?t. subspace t /\ t SUBSET u /\
                    (~(s = {}) ==> aff_dim t = aff_dim s) /\
                    (relative_frontier s) homeomorphic
                    (sphere(vec 0,&1) INTER t)"
     (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"s:real^M->bool = {}") THENL
       [STRIP_TAC THEN EXISTS_TAC (← q r"{vec 0:real^N}") THEN
        ASM_REWRITE_TAC [SUBSPACE_TRIVIAL, RELATIVE_FRONTIER_EMPTY] THEN
        ASM_SIMP_TAC [HOMEOMORPHIC_EMPTY,
                      ← SET_RULE (← q r"s INTER {a} = {} <=> ~(a IN s)"),
                      IN_SPHERE_0, NORM_0, SING_SUBSET, SUBSPACE_0] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV,
        FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"a:real^M") MP_TAC o
            GEN_REWRITE_RULE id [← GSYM MEMBER_NOT_EMPTY]) THEN
        GEOM_ORIGIN_TAC (← q r"a:real^M") THEN
        SIMP_TAC [AFF_DIM_DIM_0, HULL_INC, INT_OF_NUM_LE, ← GSYM DIM_UNIV] THEN
        REPEAT STRIP_TAC] THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP CHOOSE_SUBSPACE_OF_SUBSPACE) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:real^N->bool") THEN
      ASM_SIMP_TAC [SPAN_OF_SUBSPACE, AFF_DIM_DIM_SUBSPACE, INT_OF_NUM_EQ] THEN
      STRIP_TAC THEN
      TRANS_TAC HOMEOMORPHIC_TRANS
       (← q r"relative_frontier(ball(vec 0:real^N,&1) INTER t)") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
        ASM_SIMP_TAC [CONVEX_INTER, BOUNDED_INTER, BOUNDED_BALL,
                      SUBSPACE_IMP_CONVEX, CONVEX_BALL] THEN
        ONCE_REWRITE_TAC [INTER_COMM] THEN
        FIRST_ASSUM (ASSUME_TAC o MATCH_MP SUBSPACE_0) THEN
        SUBGOAL_THEN (← q r"~(t INTER ball(vec 0:real^N,&1) = {})") ASSUME_TAC THENL
         [REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC (← q r"vec 0:real^N") THEN
          ASM_REWRITE_TAC [IN_INTER, CENTRE_IN_BALL, REAL_LT_01],
          ASM_SIMP_TAC [AFF_DIM_CONVEX_INTER_OPEN, OPEN_BALL,
                        SUBSPACE_IMP_CONVEX] THEN
          ASM_SIMP_TAC [AFF_DIM_DIM_0, HULL_INC]],
        MATCH_MP_TAC (← MESON [HOMEOMORPHIC_REFL] (← q r"s = t ==> s homeomorphic t")) THEN
        SIMP_TAC [← GSYM FRONTIER_BALL, REAL_LT_01] THEN
        MATCH_MP_TAC RELATIVE_FRONTIER_CONVEX_INTER_AFFINE THEN
        ASM_SIMP_TAC [CONVEX_BALL, SUBSPACE_IMP_AFFINE,
                      ← GSYM MEMBER_NOT_EMPTY] THEN
        EXISTS_TAC (← q r"vec 0:real^N") THEN
        ASM_SIMP_TAC [CENTRE_IN_BALL, INTERIOR_OPEN, OPEN_BALL,
                      SUBSPACE_0, IN_INTER, REAL_LT_01]])
    prove
     r"!f:real^M->real^N s t.
       convex s /\ bounded s /\ convex t /\ bounded t /\ aff_dim s < aff_dim t /\
       f continuous_on relative_frontier s /\
       IMAGE f (relative_frontier s) SUBSET (relative_frontier t)
       ==> ?c. homotopic_with (\z. T)
                  (subtopology euclidean (relative_frontier s),
                   subtopology euclidean (relative_frontier t)) f (\x. c)"
     (ONCE_REWRITE_TAC [← MESON [] (← q r"(!a b c. P a b c) <=> (!b c a. P a b c)")] THEN
      REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC [IMP_IMP] THEN ONCE_REWRITE_TAC [RIGHT_IMP_FORALL_THM] THEN
      REWRITE_TAC [IMP_IMP, ← GSYM CONJ_ASSOC] THEN REPEAT GEN_TAC THEN
      ASM_CASES_TAC (← q r"s:real^M->bool = {}") THENL
       [ASM_SIMP_TAC [HOMOTOPIC_WITH_EUCLIDEAN_ALT, RELATIVE_FRONTIER_EMPTY,
         PCROSS_EMPTY, NOT_IN_EMPTY, IMAGE_CLAUSES, CONTINUOUS_ON_EMPTY],
        ALL_TAC] THEN
      ASM_CASES_TAC (← q r"t:real^N->bool = {}") THEN
      ASM_SIMP_TAC [AFF_DIM_EMPTY, ← GSYM INT_NOT_LE, AFF_DIM_GE] THEN
      STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"t:real^N->bool", ← q r"(:real^N)"] lemma2) THEN
      ASM_REWRITE_TAC [DIM_UNIV, SUBSPACE_UNIV, AFF_DIM_LE_UNIV] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"t':real^N->bool") STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT) THEN
      DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP
        HOMOTOPY_EQUIVALENT_HOMOTOPIC_TRIVIALITY_NULL th])) THEN
      MP_TAC (← ISPECL [← q r"s:real^M->bool", ← q r"t':real^N->bool"] lemma2) THEN
      ASM_SIMP_TAC [← GSYM AFF_DIM_DIM_SUBSPACE] THEN
      ANTS_TAC THENL [ASM_INT_ARITH_TAC, ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"s':real^N->bool") STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT) THEN
      DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP
        HOMOTOPY_EQUIVALENT_COHOMOTOPIC_TRIVIALITY_NULL th])) THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma1 THEN
      ASM_SIMP_TAC [← GSYM INT_OF_NUM_LT, ← GSYM AFF_DIM_DIM_SUBSPACE] THEN
      ASM_INT_ARITH_TAC))

  let INESSENTIAL_SPHEREMAP_LOWDIM ← prove
   r"!f:real^M->real^N a r b s.
        dimindex(:M) < dimindex(:N) /\
        f continuous_on sphere(a,r) /\
        IMAGE f (sphere(a,r)) SUBSET (sphere(b,s))
        ==> ?c. homotopic_with (\z. T)
                 (subtopology euclidean (sphere(a,r)),
                  subtopology euclidean (sphere(b,s))) f (\x. c)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"s <= &0") THEN
    ASM_SIMP_TAC [NULLHOMOTOPIC_INTO_CONTRACTIBLE, CONTRACTIBLE_SPHERE] THEN
    ASM_CASES_TAC (← q r"r <= &0") THEN
    ASM_SIMP_TAC [NULLHOMOTOPIC_FROM_CONTRACTIBLE, CONTRACTIBLE_SPHERE] THEN
    ASM_SIMP_TAC [← GSYM FRONTIER_CBALL, INTERIOR_CBALL, BALL_EQ_EMPTY,
                  ← CONV_RULE (RAND_CONV SYM_CONV) (← SPEC_ALL
                  RELATIVE_FRONTIER_NONEMPTY_INTERIOR)] THEN
    STRIP_TAC THEN MATCH_MP_TAC INESSENTIAL_SPHEREMAP_LOWDIM_GEN THEN
    ASM_REWRITE_TAC [CONVEX_CBALL, BOUNDED_CBALL, AFF_DIM_CBALL] THEN
    ASM_REWRITE_TAC [← GSYM REAL_NOT_LE, INT_OF_NUM_LT])

  pure { INESSENTIAL_SPHEREMAP_LOWDIM_GEN, INESSENTIAL_SPHEREMAP_LOWDIM }

/- ------------------------------------------------------------------------- -/
/- Homeomorphic and homotopy-equivalent spheres; simple connectedness of     -/
/- spheres and punctured convex sets.                                        -/
/- (moretop.ml 518-823)                                                     -/
/- ------------------------------------------------------------------------- -/

structure MOC where
  HOMEOMORPHIC_SPHERES_EQ : thm
  HOMOTOPY_EQUIVALENT_SPHERES_EQ : thm
  SIMPLY_CONNECTED_SPHERE_GEN : thm
  SIMPLY_CONNECTED_SPHERE : thm
  SIMPLY_CONNECTED_PUNCTURED_CONVEX : thm
  SIMPLY_CONNECTED_PUNCTURED_UNIVERSE : thm
  SIMPLY_CONNECTED_CONVEX_DIFF_FINITE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOC [HolBase] (D : MoreTopDeps) (BMOB : MOB) : ExceptT String IO MOC := do
  -- @@SCOPE BEGIN
  let { INESSENTIAL_SPHEREMAP_LOWDIM, INESSENTIAL_SPHEREMAP_LOWDIM_GEN, .. } := BMOB
  let { CONNECTED_IVT_HYPERPLANE, HOMEOMORPHIC_SING, .. } := D.qtopology
  let { CONNECTED_FINITE_IFF_SING, CONTRACTIBLE_CONVEX_TWEAK_BOUNDARY_POINTS,
        CONTRACTIBLE_IMP_SIMPLY_CONNECTED, CONVEX_IMP_SIMPLY_CONNECTED,
        HOMOTOPY_EQUIVALENT_EMPTY, HOMOTOPY_EQUIVALENT_SING,
        PATH_CONNECTED_CONVEX_DIFF_COUNTABLE, PATH_CONNECTED_SPHERE,
        SIMPLY_CONNECTED_EMPTY, SIMPLY_CONNECTED_UNION, .. } := D.qpaths
  let { AFF_DIM_CBALL, AFF_DIM_CONVEX_INTER_NONEMPTY_INTERIOR,
        RELATIVE_INTERIOR_CONVEX_INTER_AFFINE, .. } := D.qconvex
  let { CONTRACTIBLE_SPHERE, HOMOTOPY_EQUIVALENT_RELATIVE_FRONTIER_PUNCTURED_AFFINE_HULL,
        HOMOTOPY_EQUIVALENT_RELATIVE_FRONTIER_PUNCTURED_CONVEX, PATH_CONNECTED_SPHERE_GEN,
        .. } := D.qdegree
  let { HOMOTOPY_EQUIVALENT_SIMPLE_CONNECTEDNESS,
        SIMPLY_CONNECTED_EQ_CONTRACTIBLE_CIRCLEMAP, .. } := D.ra.tsad
  let { HOMOTOPY_EQUIVALENT_HOMOTOPIC_TRIVIALITY, .. } := D.ra.ts.qpaths
  let { CONVEX_HALFSPACE_COMPONENT_GT, CONVEX_HALFSPACE_COMPONENT_LT,
        .. } := D.ra.ts.qconvex
  let { ARITH_RULE, ASM_INT_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, basic_ss,
        GEN_SIMPLIFY_CONV, GEOM_EQUAL_DIMENSION_RULE, INT_ARITH, MESON, MESON_TAC,
        REAL_ARITH, REAL_RAT_REDUCE_CONV, SET_RULE, SET_TAC, TOP_DEPTH_SQCONV,
        .. } := D.ra.ts.cn.cx.cvx
  let { INFINITE, .. } := D.ra.ts.cn.cx.cpx
  let { AND_FORALL_THM, ARITH, CARD_PSUBSET, CART_EQ, CONJ_ACI, CONTRAPOS_THM, DIFF_EMPTY,
        DIMINDEX_2, DIMINDEX_GE_1, EQ_IMP, FINITE_EMPTY, FINITE_INTER, FINITE_SUBSET,
        .. } := D.ra.ts.cn.cx.cvx.core1
  let { IMAGE_ID, IMP_CONJ, IMP_CONJ_ALT, IMP_IMP, INT_OF_NUM_LE, INTER_COMM,
        .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INTER, LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY, NOT_FORALL_THM,
        NOT_IMP, .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_LT_01, REAL_LT_IMP_LE, REAL_LT_IMP_NE, REAL_LT_REFL,
        .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_OF_NUM_EQ, REAL_OF_NUM_LE, RIGHT_IMP_FORALL_THM, SUBSET, SUBSET_REFL,
        .. } := D.ra.ts.cn.cx.cvx.core5
  let { real_gt, SWAP_FORALL_THM, .. } := D.ra.ts.cn.cx.cvx.core6
  let { HULL_INC, HULL_SUBSET, .. } := D.ra.ts.cn.cx.cvx.misc
  let { DOT_BASIS, .. } := D.ra.ts.cn.cx.cvx.vec1
  let { BALL_EQ_EMPTY, BOUNDED_CBALL, CENTRE_IN_BALL, CLOSED_CBALL, CLOSED_INTER,
        CLOSURE_EQ, .. } := D.ra.ts.cn.cx.cvx.top1
  let { CLOSURE_SUBSET, .. } := D.ra.ts.cn.cx.cvx.top2
  let { CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID, HOMEOMORPHIC_EMPTY,
        .. } := D.ra.ts.cn.cx.cvx.top3
  let { INTERIOR_CBALL, OPEN_HALFSPACE_COMPONENT_GT, OPEN_HALFSPACE_COMPONENT_LT,
        .. } := D.ra.ts.cn.cx.cvx.top4
  let { OPEN_IN_OPEN_INTER, OPEN_INTER, SPHERE_EMPTY, .. } := D.ra.ts.cn.cx.cvx.top5
  let { WF_INDUCT_TAC, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt
  let { AFF_DIM_CONVEX_INTER_OPEN, AFFINE_HULL_AFFINE_INTER_NONEMPTY_INTERIOR,
        AFFINE_HULL_NONEMPTY_INTERIOR, CONVEX_CONNECTED, RELATIVE_FRONTIER_CBALL,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qconvex
  let { HOMOTOPIC_CONSTANT_MAPS, HOMOTOPIC_WITH_SYM, HOMOTOPIC_WITH_TRANS,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qmetric
  let { HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT, HOMOTOPIC_WITH_IMP_SUBSET,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths1
  let { contractible, HOMOTOPY_EQUIVALENT_SYM, PATH_COMPONENT_OF_EUCLIDEAN,
        PATH_CONNECTED_IFF_PATH_COMPONENT, .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths2
  let { HOMEOMORPHIC_SPHERES, SPHERE_EQ_EMPTY, SPHERE_SING,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology2
  let { FINITE_IMP_COUNTABLE, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcard
  let { BOUNDED_INTER, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qtop
  let { AFF_DIM_AFFINE_HULL, AFFINE_AFFINE_HULL, AFFINE_IMP_CONVEX, CLOSED_AFFINE_HULL,
        COLLINEAR_AFF_DIM, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx1
  let { CONVEX_CBALL, CONVEX_INTER, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  let { CONVEX_SING, IN_RELATIVE_INTERIOR_CBALL, relative_frontier,
        RELATIVE_INTERIOR_CBALL, RELATIVE_INTERIOR_SUBSET,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx3
  -- @@SCOPE END

  let (HOMEOMORPHIC_SPHERES_EQ, HOMOTOPY_EQUIVALENT_SPHERES_EQ) ← (do
    let lemma ← prove
     r"!a:real^M r b:real^N s.
            dimindex(:M) < dimindex(:N) /\ &0 < r /\ &0 < s
            ==> ~(sphere(a,r) homotopy_equivalent sphere(b,s))"
     (REPEAT STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o ISPEC (← q r"sphere(a:real^M,r)") o
          MATCH_MP HOMOTOPY_EQUIVALENT_HOMOTOPIC_TRIVIALITY) THEN
      MATCH_MP_TAC (← TAUT (← q r"~p /\ q ==> (p <=> q) ==> F")) THEN CONJ_TAC THENL
       [SUBGOAL_THEN (← q r"~(sphere(a:real^M,r) = {})") MP_TAC THENL
         [REWRITE_TAC [SPHERE_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC,
          REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, LEFT_IMP_EXISTS_THM]] THEN
        X_GEN_TAC (← q r"c:real^M") THEN DISCH_TAC THEN
        DISCH_THEN (MP_TAC o SPECL [← q r"\a:real^M. a", ← q r"(\a. c):real^M->real^M"]) THEN
        SIMP_TAC [CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID,
                  IMAGE_ID, SUBSET_REFL] THEN
        REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"~(contractible(sphere(a:real^M,r)))") MP_TAC THENL
         [REWRITE_TAC [CONTRACTIBLE_SPHERE] THEN ASM_REAL_ARITH_TAC,
          REWRITE_TAC [contractible] THEN MESON_TAC []],
        MAP_EVERY X_GEN_TAC [← q r"f:real^M->real^N", ← q r"g:real^M->real^N"] THEN
        STRIP_TAC THEN
        MP_TAC (← ISPEC (← q r"g:real^M->real^N") INESSENTIAL_SPHEREMAP_LOWDIM) THEN
        MP_TAC (← ISPEC (← q r"f:real^M->real^N") INESSENTIAL_SPHEREMAP_LOWDIM) THEN
        ASM_REWRITE_TAC [IMP_IMP, AND_FORALL_THM] THEN DISCH_THEN
         (MP_TAC o SPECL [← q r"a:real^M", ← q r"r:real", ← q r"b:real^N", ← q r"s:real"]) THEN
        ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM, IMP_CONJ, RIGHT_IMP_FORALL_THM] THEN
        REPEAT GEN_TAC THEN REWRITE_TAC [IMP_IMP] THEN DISCH_THEN
         (fun th => CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP
                           HOMOTOPIC_WITH_IMP_SUBSET) th THEN
                    MP_TAC th) THEN
        MATCH_MP_TAC (← MESON [HOMOTOPIC_WITH_TRANS, HOMOTOPIC_WITH_SYM]
            (← q r"homotopic_with p
              (subtopology euclidean s,subtopology euclidean t) c d
              ==> homotopic_with p
                   (subtopology euclidean s,
                    subtopology euclidean t) f c /\
                  homotopic_with p
                   (subtopology euclidean s,
                    subtopology euclidean t) g d
                  ==> homotopic_with p
                       (subtopology euclidean s,
                        subtopology euclidean t) f g")) THEN
        REWRITE_TAC [HOMOTOPIC_CONSTANT_MAPS, PATH_COMPONENT_OF_EUCLIDEAN] THEN
        DISJ2_TAC THEN
        MP_TAC (← ISPECL [← q r"b:real^N", ← q r"s:real"] PATH_CONNECTED_SPHERE) THEN
        ANTS_TAC THENL
         [FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← ARITH_RULE
           (← q r"m < n ==> 1 <= m ==> 2 <= n"))) THEN REWRITE_TAC [DIMINDEX_GE_1],
          REWRITE_TAC [PATH_CONNECTED_IFF_PATH_COMPONENT] THEN
          DISCH_THEN MATCH_MP_TAC THEN
          SUBGOAL_THEN (← q r"~(sphere(a:real^M,r) = {})") MP_TAC THENL
           [REWRITE_TAC [SPHERE_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC,
            ASM SET_TAC []]]])
    CONJ_PAIR (← prove
     r"(!a:real^M b:real^N r s.
          sphere(a,r) homeomorphic sphere(b,s) <=>
          r < &0 /\ s < &0 \/ r = &0 /\ s = &0 \/
          &0 < r /\ &0 < s /\ dimindex(:M) = dimindex(:N)) /\
     (!a:real^M b:real^N r s.
          sphere(a,r) homotopy_equivalent sphere(b,s) <=>
          r < &0 /\ s < &0 \/ r = &0 /\ s = &0 \/
          &0 < r /\ &0 < s /\ dimindex(:M) = dimindex(:N))"
     (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
      MATCH_MP_TAC (← TAUT
       (← q r"(r ==> p) /\ (q ==> r) /\ (p ==> q) ==> (r <=> q) /\ (p <=> q)")) THEN
      REWRITE_TAC [HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT] THEN
      ASM_CASES_TAC (← q r"r < &0") THEN
      ASM_SIMP_TAC [SPHERE_EMPTY, SPHERE_EQ_EMPTY,
                    HOMEOMORPHIC_EMPTY, HOMOTOPY_EQUIVALENT_EMPTY]
      THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      ASM_CASES_TAC (← q r"s < &0") THEN
      ASM_SIMP_TAC [SPHERE_EMPTY, SPHERE_EQ_EMPTY,
                    HOMEOMORPHIC_EMPTY, HOMOTOPY_EQUIVALENT_EMPTY]
      THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      ASM_CASES_TAC (← q r"r = &0") THEN
      ASM_SIMP_TAC [SPHERE_SING, REAL_LT_REFL, HOMEOMORPHIC_SING,
                    HOMOTOPY_EQUIVALENT_SING, CONTRACTIBLE_SPHERE,
                    ← ONCE_REWRITE_RULE [HOMOTOPY_EQUIVALENT_SYM]
                        HOMOTOPY_EQUIVALENT_SING]
      THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      ASM_CASES_TAC (← q r"s = &0") THEN
      ASM_SIMP_TAC [SPHERE_SING, REAL_LT_REFL, HOMEOMORPHIC_SING,
                    HOMOTOPY_EQUIVALENT_SING, CONTRACTIBLE_SPHERE,
                    ← ONCE_REWRITE_RULE [HOMOTOPY_EQUIVALENT_SYM]
                        HOMOTOPY_EQUIVALENT_SING]
      THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      SUBGOAL_THEN (← q r"&0 < r /\ &0 < s") STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC, ASM_REWRITE_TAC []] THEN
      CONJ_TAC THENL
       [DISCH_THEN (fun th => tactic_of do
          let t ← q r"?a:real^M b:real^N. ~(sphere(a,r) homeomorphic sphere(b,s))"
          pure (MP_TAC (← DISCH t (← GEOM_EQUAL_DIMENSION_RULE th (← ASSUME t))))) THEN
        ASM_SIMP_TAC [HOMEOMORPHIC_SPHERES] THEN MESON_TAC [],
        ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
        REWRITE_TAC [← ARITH_RULE (← q r"~(m:num = n) <=> m < n \/ n < m")] THEN
        STRIP_TAC THENL [ALL_TAC, ONCE_REWRITE_TAC [HOMOTOPY_EQUIVALENT_SYM]] THEN
        ASM_SIMP_TAC [lemma]])))

  let SIMPLY_CONNECTED_SPHERE_GEN ← prove
   r"!s. convex s /\ bounded s /\ &3 <= aff_dim s
       ==> simply_connected(relative_frontier s)"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [SIMPLY_CONNECTED_EQ_CONTRACTIBLE_CIRCLEMAP,
                  PATH_CONNECTED_SPHERE_GEN,
                  ← INT_ARITH (← q r"&3:int <= x ==> ~(x = &1)")] THEN
    SUBGOAL_THEN (← q r"sphere(vec 0:real^2,&1) = relative_frontier(cball(vec 0,&1))")
    SUBST1_TAC THENL
     [REWRITE_TAC [RELATIVE_FRONTIER_CBALL, REAL_OF_NUM_EQ, ARITH], ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC INESSENTIAL_SPHEREMAP_LOWDIM_GEN THEN
    ASM_REWRITE_TAC [CONVEX_CBALL, BOUNDED_CBALL, AFF_DIM_CBALL] THEN
    REWRITE_TAC [DIMINDEX_2, REAL_LT_01] THEN ASM_INT_ARITH_TAC)

  let SIMPLY_CONNECTED_SPHERE ← prove
   r"!a:real^N r. 3 <= dimindex(:N) ==> simply_connected(sphere(a,r))"
   (REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (← REAL_ARITH (← q r"r < &0 \/ r = &0 \/ &0 < r")) THEN
    ASM_SIMP_TAC [SPHERE_EMPTY, SIMPLY_CONNECTED_EMPTY] THEN
    ASM_SIMP_TAC [SPHERE_SING, CONVEX_SING, CONVEX_IMP_SIMPLY_CONNECTED] THEN
    MP_TAC (← ISPEC (← q r"cball(a:real^N,r)") SIMPLY_CONNECTED_SPHERE_GEN) THEN
    ASM_SIMP_TAC [AFF_DIM_CBALL, RELATIVE_FRONTIER_CBALL, CONVEX_CBALL,
                  BOUNDED_CBALL, REAL_LT_IMP_NE, INT_OF_NUM_LE])

  let SIMPLY_CONNECTED_PUNCTURED_CONVEX ← prove
   r"!s a:real^N.
        convex s /\ &3 <= aff_dim s ==> simply_connected(s DELETE a)"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"(a:real^N) IN relative_interior s") THENL
     [ALL_TAC,
      MATCH_MP_TAC CONTRACTIBLE_IMP_SIMPLY_CONNECTED THEN
      MATCH_MP_TAC CONTRACTIBLE_CONVEX_TWEAK_BOUNDARY_POINTS THEN
      EXISTS_TAC (← q r"s:real^N->bool") THEN ASM_REWRITE_TAC [] THEN
      MP_TAC (← ISPEC (← q r"s:real^N->bool") RELATIVE_INTERIOR_SUBSET) THEN
      MP_TAC (← ISPEC (← q r"s:real^N->bool") CLOSURE_SUBSET) THEN ASM SET_TAC []] THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [IN_RELATIVE_INTERIOR_CBALL]) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN (← q r"e:real") STRIP_ASSUME_TAC)) THEN
    MP_TAC (← ISPECL
     [← q r"cball(a:real^N,e) INTER affine hull s", ← q r"s:real^N->bool", ← q r"a:real^N"]
          HOMOTOPY_EQUIVALENT_RELATIVE_FRONTIER_PUNCTURED_CONVEX) THEN
    ANTS_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC (← MESON [HOMOTOPY_EQUIVALENT_SIMPLE_CONNECTEDNESS]
       (← q r"simply_connected s
        ==> s homotopy_equivalent t ==> simply_connected t")) THEN
      MATCH_MP_TAC SIMPLY_CONNECTED_SPHERE_GEN] THEN
    ASM_SIMP_TAC [CONVEX_INTER, AFFINE_AFFINE_HULL, AFFINE_IMP_CONVEX,
                  CONVEX_CBALL, BOUNDED_INTER, BOUNDED_CBALL] THEN
    REPEAT CONJ_TAC THENL
     [W (MP_TAC o PART_MATCH (lhs o rand) RELATIVE_INTERIOR_CONVEX_INTER_AFFINE o
          rand o snd) THEN
      REWRITE_TAC [CONVEX_CBALL, AFFINE_AFFINE_HULL, INTERIOR_CBALL] THEN
      REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, LEFT_IMP_EXISTS_THM, IN_INTER] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"a:real^N")) THEN ASM_SIMP_TAC [CENTRE_IN_BALL] THEN
      ANTS_TAC THENL
       [ALL_TAC,
        DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [CENTRE_IN_BALL, IN_INTER]] THEN
      ASM_MESON_TAC [SUBSET, HULL_SUBSET, RELATIVE_INTERIOR_SUBSET],
      REWRITE_TAC [relative_frontier] THEN FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP
       (← SET_RULE (← q r"s SUBSET u ==> c = s ==> c DIFF i SUBSET u"))) THEN
      REWRITE_TAC [CLOSURE_EQ] THEN MATCH_MP_TAC CLOSED_INTER THEN
      REWRITE_TAC [CLOSED_AFFINE_HULL, CLOSED_CBALL],
      ONCE_REWRITE_TAC [INTER_COMM] THEN
      W (MP_TAC o PART_MATCH (lhs o rand)
        AFFINE_HULL_AFFINE_INTER_NONEMPTY_INTERIOR o rand o snd),
      ONCE_REWRITE_TAC [INTER_COMM] THEN
      W (MP_TAC o PART_MATCH (lhs o rand) AFF_DIM_CONVEX_INTER_NONEMPTY_INTERIOR o
          rand o snd)] THEN
    ASM_SIMP_TAC [AFFINE_IMP_CONVEX, AFFINE_AFFINE_HULL, ← GSYM MEMBER_NOT_EMPTY,
                  LEFT_IMP_EXISTS_THM, IN_INTER] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"a:real^N")) THEN
    ASM_SIMP_TAC [INTERIOR_CBALL, CENTRE_IN_BALL, HULL_INC, HULL_SUBSET,
                  AFF_DIM_AFFINE_HULL])

  let SIMPLY_CONNECTED_PUNCTURED_UNIVERSE ← prove
   r"!a. 3 <= dimindex(:N) ==> simply_connected((:real^N) DELETE a)"
   (GEN_TAC THEN DISCH_THEN (MP_TAC o SPECL [← q r"a:real^N", ← q r"&1"] o
      MATCH_MP SIMPLY_CONNECTED_SPHERE) THEN
    MATCH_MP_TAC EQ_IMP THEN
    MATCH_MP_TAC HOMOTOPY_EQUIVALENT_SIMPLE_CONNECTEDNESS THEN
    MP_TAC (← ISPECL [← q r"cball(a:real^N,&1)", ← q r"a:real^N"]
          HOMOTOPY_EQUIVALENT_RELATIVE_FRONTIER_PUNCTURED_AFFINE_HULL) THEN
    REWRITE_TAC [CONVEX_CBALL, BOUNDED_CBALL, RELATIVE_INTERIOR_CBALL,
                 RELATIVE_FRONTIER_CBALL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC [CENTRE_IN_BALL, AFFINE_HULL_NONEMPTY_INTERIOR, INTERIOR_CBALL,
              BALL_EQ_EMPTY, REAL_OF_NUM_LE, ARITH, REAL_LT_01])

  let SIMPLY_CONNECTED_CONVEX_DIFF_FINITE ← (do
    let lemma ← prove
     r"!P. (?u v. P u /\ P v /\ ~(u = v)) /\
           (!c. P c ==> ~(s INTER {x:real^N | x$k = c} = {}))
           ==> ?u v. u IN s INTER {x | P(x$k)} /\ v IN s INTER {x | P(x$k)} /\
                     ~(u = v)"
     (REPEAT STRIP_TAC THEN FIRST_X_ASSUM (fun th => tactic_of do
        pure (MP_TAC (← SPEC (← q r"u:real") th) THEN MP_TAC (← SPEC (← q r"v:real") th))) THEN
      ASM SET_TAC [])
    prove
     r"!s t:real^N->bool.
          convex s /\ &3 <= aff_dim s /\ FINITE t
          ==> simply_connected(s DIFF t)"
     (ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN GEN_TAC THEN
      WF_INDUCT_TAC (← q r"CARD(t:real^N->bool)") THEN
      X_GEN_TAC (← q r"s:real^N->bool") THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC [← SET_RULE (← q r"s DIFF t = s DIFF (s INTER t)")] THEN
      REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC (← SET_RULE
       (← q r"s INTER t = {} \/ ?a:real^N. s INTER t = {a} \/
        ?a b. ~(a = b) /\ a IN s /\ a IN t /\ b IN s /\ b IN t")) THEN
      ASM_SIMP_TAC [CONVEX_IMP_SIMPLY_CONNECTED, SIMPLY_CONNECTED_PUNCTURED_CONVEX,
                    DIFF_EMPTY, ← SET_RULE (← q r"s DIFF {a} = s DELETE a")] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
      REWRITE_TAC [NOT_IMP, LEFT_IMP_EXISTS_THM, NOT_FORALL_THM] THEN
      X_GEN_TAC (← q r"k:num") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o MATCH_MP (← REAL_ARITH
       (← q r"~(x = y) ==> x < y \/ y < x"))) THEN
      POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist CONJ o HolLight.rev) THEN
      ONCE_REWRITE_TAC [← REWRITE_RULE [IMP_CONJ_ALT] IMP_IMP] THEN
      MAP_EVERY (fun t => SPEC_TAC (t, t)) [← q r"b:real^N", ← q r"a:real^N"] THEN
      MATCH_MP_TAC (← MESON []
       (← q r"(!a b. R a b ==> R b a) /\ (!a b. P a b ==> R a b)
        ==> !a b. P a b \/ P b a ==> R a b")) THEN
      CONJ_TAC THENL [REWRITE_TAC [CONJ_ACI], REPEAT STRIP_TAC] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [RIGHT_IMP_FORALL_THM, IMP_IMP]) THEN
      SUBGOAL_THEN
       (← q r"!s t. s DIFF t =
              {x | x IN s /\ x$k < (b:real^N)$k} DIFF
              {x | x IN t /\ x$k < b$k} UNION
              {x:real^N | x IN s /\ (a:real^N)$k < x$k} DIFF
              {x | x IN t /\ a$k < x$k}")
       (fun th => tactic_of do pure (ONCE_REWRITE_TAC [th] THEN ASSUME_TAC (← GSYM th)))
      THENL
       [FIRST_ASSUM (MP_TAC o MATCH_MP (← REAL_ARITH
         (← q r"a < b ==> !x. a < x \/ x < b"))) THEN SET_TAC [],
        MATCH_MP_TAC SIMPLY_CONNECTED_UNION THEN ASM_REWRITE_TAC []] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC [← SET_RULE (← q r"{x | x IN s /\ P x} DIFF {x | x IN t /\ P x} =
                              (s DIFF t) INTER {x | P x}")] THEN
        MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
        REWRITE_TAC [OPEN_HALFSPACE_COMPONENT_LT],
        REWRITE_TAC [← SET_RULE (← q r"{x | x IN s /\ P x} DIFF {x | x IN t /\ P x} =
                              (s DIFF t) INTER {x | P x}")] THEN
        MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
        REWRITE_TAC [← GSYM real_gt, OPEN_HALFSPACE_COMPONENT_GT],
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC [← SET_RULE (← q r"{x | x IN s /\ P x} = s INTER {x | P x}"),
          FINITE_INTER, CONVEX_INTER, CONVEX_HALFSPACE_COMPONENT_LT] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CARD_PSUBSET THEN ASM SET_TAC [REAL_LT_REFL],
          ALL_TAC] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← INT_ARITH
         (← q r"&3:int <= x ==> y = x ==> &3 <= y"))) THEN
        MATCH_MP_TAC AFF_DIM_CONVEX_INTER_OPEN THEN
        ASM_REWRITE_TAC [OPEN_HALFSPACE_COMPONENT_LT] THEN
        ASM SET_TAC [],
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC [← SET_RULE (← q r"{x | x IN s /\ P x} = s INTER {x | P x}"),
          FINITE_INTER, CONVEX_INTER,
          ← REWRITE_RULE [real_gt] CONVEX_HALFSPACE_COMPONENT_GT] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CARD_PSUBSET THEN ASM SET_TAC [REAL_LT_REFL],
          ALL_TAC] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← INT_ARITH
         (← q r"&3:int <= x ==> y = x ==> &3 <= y"))) THEN
        MATCH_MP_TAC AFF_DIM_CONVEX_INTER_OPEN THEN
        ASM_REWRITE_TAC [← REWRITE_RULE [real_gt] OPEN_HALFSPACE_COMPONENT_GT] THEN
        ASM SET_TAC [],
        ALL_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [← SET_RULE (← q r"{x | x IN s /\ P x} DIFF {x | x IN t /\ P x} =
                            (s DIFF t) INTER {x | P x}")] THEN
      REWRITE_TAC [← SET_RULE (← q r"(s INTER u) INTER (s INTER v) = s INTER (u INTER v)"),
                   ← SET_RULE (← q r"(s DIFF t) INTER u = (s INTER u) DIFF t")] THEN
      REWRITE_TAC [← SET_RULE (← q r"s INTER u DIFF s INTER t = s INTER u DIFF t")] THENL
       [MATCH_MP_TAC PATH_CONNECTED_CONVEX_DIFF_COUNTABLE THEN
        ASM_SIMP_TAC [FINITE_IMP_COUNTABLE, CONVEX_INTER, COLLINEAR_AFF_DIM,
                      CONVEX_HALFSPACE_COMPONENT_LT,
                      ← REWRITE_RULE [real_gt] CONVEX_HALFSPACE_COMPONENT_GT] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← INT_ARITH
         (← q r"&3:int <= x ==> y = x ==> ~(y <= &1)"))) THEN
        MATCH_MP_TAC AFF_DIM_CONVEX_INTER_OPEN THEN
        ASM_SIMP_TAC [OPEN_INTER, OPEN_HALFSPACE_COMPONENT_LT,
                      ← REWRITE_RULE [real_gt] OPEN_HALFSPACE_COMPONENT_GT] THEN
        MATCH_MP_TAC (← MESON [INFINITE, FINITE_EMPTY]
         (← q r"INFINITE s ==> ~(s = {})")),
        REWRITE_TAC [← SET_RULE (← q r"s DIFF t = {} <=> s SUBSET t")] THEN
        MATCH_MP_TAC (← MESON [FINITE_SUBSET, INFINITE]
         (← q r"INFINITE s /\ FINITE t ==> ~(s SUBSET t)")) THEN
        ASM_REWRITE_TAC []] THEN
     (ASM (fun ths => tactic_of do
          pure (CONV_TAC (← ExceptT.mk (GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV
            (← ExceptT.mk (basic_ss [])) 5 ths))))
       [CONNECTED_FINITE_IFF_SING, INFINITE, CONVEX_CONNECTED,
        CONVEX_INTER, CONVEX_HALFSPACE_COMPONENT_LT,
        ← REWRITE_RULE [real_gt] CONVEX_HALFSPACE_COMPONENT_GT] THEN
      MATCH_MP_TAC (← SET_RULE
       (← q r"!u v. u IN s /\ v IN s /\ ~(u = v) ==> ~(s = {} \/ ?z. s = {z})")) THEN
      REWRITE_TAC [← SET_RULE (← q r"{x | P x} INTER {x | Q x} = {x | Q x /\ P x}")] THEN
      MP_TAC lemma THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC (← q r"a$k + &1 / &3 * ((b:real^N)$k - (a:real^N)$k)") THEN
        EXISTS_TAC (← q r"a$k + &2 / &3 * ((b:real^N)$k - (a:real^N)$k)") THEN
        ASM_REAL_ARITH_TAC,
        X_GEN_TAC (← q r"c:real") THEN STRIP_TAC THEN
        REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_INTER, IN_ELIM_THM] THEN
        SUBGOAL_THEN (← q r"!x:real^N. x$k = basis k dot x") (fun t => SIMP_TAC [t]) THENL
         [ASM_MESON_TAC [DOT_BASIS], MATCH_MP_TAC CONNECTED_IVT_HYPERPLANE] THEN
        MAP_EVERY EXISTS_TAC [← q r"a:real^N", ← q r"b:real^N"] THEN
        ASM_SIMP_TAC [CONVEX_CONNECTED, DOT_BASIS, REAL_LT_IMP_LE]])))

  pure { HOMEOMORPHIC_SPHERES_EQ, HOMOTOPY_EQUIVALENT_SPHERES_EQ,
         SIMPLY_CONNECTED_SPHERE_GEN, SIMPLY_CONNECTED_SPHERE,
         SIMPLY_CONNECTED_PUNCTURED_CONVEX, SIMPLY_CONNECTED_PUNCTURED_UNIVERSE,
         SIMPLY_CONNECTED_CONVEX_DIFF_FINITE }

/- ------------------------------------------------------------------------- -/
/- Borsuk's odd mapping degree theorem: the homotopy lemma.                  -/
/- (moretop.ml 824-1335)                                                    -/
/- ------------------------------------------------------------------------- -/

structure MOD where
  ODD_MAP_HOMOTOPY_LEMMA : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOD [HolBase] (D : MoreTopDeps) (BMOA : MOA) : ExceptT String IO MOD := do
  -- @@SCOPE BEGIN
  let { NONSURJECTIVE_DIFFERENTIABLE_SPHEREMAP_LOWDIM, .. } := BMOA
  let { REAL_DIFFERENTIABLE_AT, .. } := D.rzl
  let { REAL_DIFFERENTIABLE_ID, REAL_DIFFERENTIABLE_INV_ATREAL, .. } := D.rzo
  let { DIFFERENTIABLE_ON_NORM, .. } := D.rzq
  let { CONTINUOUS_ON_VECTOR_POLYNOMIAL_FUNCTION, VECTOR_POLYNOMIAL_FUNCTION_CMUL,
        VECTOR_POLYNOMIAL_FUNCTION_REFLECT, VECTOR_POLYNOMIAL_FUNCTION_SUB, .. } := D.rzbj
  let { STONE_WEIERSTRASS_VECTOR_POLYNOMIAL_FUNCTION_SUBSPACE, .. } := D.rzbk
  let { DIFFERENTIABLE_ON_VECTOR_POLYNOMIAL_FUNCTION, .. } := D.rzbl
  let { CONTINUOUS_MAP_DOT, CONTINUOUS_MAP_VECTOR_MUL, CONTINUOUS_MAP_VECTOR_SUB,
        .. } := D.qtopology
  let { HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT, .. } := D.qpaths
  let { DIFFERENTIABLE_ON_COMPOSE, DIFFERENTIABLE_ON_MUL, .. } := D.qderivatives
  let { COLLINEAR_3_DOT_MULTIPLES, NORM_CAUCHY_SCHWARZ_EQUAL, SPAN_BREAKDOWN_EQ,
        SUBSPACE_MUL_EQ, SUBSPACE_NEG_EQ, .. } := D.qvectors
  let { REFLECT_ALONG_GALOIS, REFLECT_ALONG_NEG, REFLECT_ALONG_REFL, REFLECT_ALONG_SWITCH,
        .. } := D.qdeterminants
  let { CONTINUOUS_MAP_CASES_LE, CONTINUOUS_MAP_FROM_SUBTOPOLOGY, CONTINUOUS_MAP_ID,
        CONTINUOUS_MAP_REAL_ABS, CONTINUOUS_MAP_REAL_CONST, CONTINUOUS_MAP_REAL_MAX,
        CONTINUOUS_MAP_REAL_MUL, CONTINUOUS_MAP_REAL_RMUL, CONTINUOUS_MAP_REAL_SUB,
        .. } := D.qmetric
  let { HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT, HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT,
        .. } := D.ra.ts.qpaths
  let { DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON, .. } := D.ra.ts.qderivatives
  let { SEGMENT_BOUND, .. } := D.ra.ts.cn.qconvex
  let { DIFFERENTIABLE_ON_SUBSET, .. } := D.ra.ts.cn.ms.qderivatives
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, NORM_ARITH,
        REAL_ARITH, REAL_RAT_REDUCE_CONV, SET_RULE, SET_TAC, VECTOR_ARITH,
        .. } := D.ra.ts.cn.cx.cvx
  let { DIFFERENTIABLE_IMP_CONTINUOUS_ON, .. } := D.ra.ts.cn.ms.ig.qderivatives
  let { CONTINUOUS_ON_LIFT_ABS, .. } := D.ra.ts.cn.ms.ig.qtopology
  let { ARITH_EQ, CONJ_ASSOC, CONTRAPOS_THM, DE_MORGAN_THM, ETA_AX,
        .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, FUN_EQ_THM, IMAGE_CLAUSES, IMAGE_EQ_EMPTY, IMAGE_o, IMP_CONJ,
        IMP_CONJ_ALT, IN_DELETE, .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_IMAGE, IN_INTER, LE_REFL, LEFT_IMP_EXISTS_THM, PSUBSET, REAL_ABS_INV,
        REAL_ABS_MUL, REAL_ABS_NEG, REAL_ABS_POS, REAL_DIV_REFL,
        .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_INV_1, REAL_LE_LDIV_EQ, REAL_LE_LMUL, REAL_LE_MUL, REAL_LE_MUL2,
        REAL_LE_RDIV_EQ, REAL_LE_TRANS, REAL_LT_IMP_NE, .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_LZERO, REAL_MUL_RID,
        REAL_MUL_RNEG, REAL_OF_NUM_EQ, REAL_POW2_ABS, REAL_POW_2, REAL_SUB_0, REAL_SUB_LT,
        SING_SUBSET, SUBSET, SUBSET_DELETE, SUBSET_EMPTY, .. } := D.ra.ts.cn.cx.cvx.core5
  let { o_DEF, o_THM, real_div, real_ge, .. } := D.ra.ts.cn.cx.cvx.core6
  let { HULL_MINIMAL, .. } := D.ra.ts.cn.cx.cvx.misc
  let { DIM_EQ_SPAN, DIM_INSERT, DOT_LMUL, DOT_RMUL, DOT_RNEG, DOT_RSUB, DOT_RZERO,
        .. } := D.ra.ts.cn.cx.cvx.vec1
  let { DOT_SYM, LIFT_DROP, NORM_0, NORM_CAUCHY_SCHWARZ_ABS, NORM_EQ_0,
        .. } := D.ra.ts.cn.cx.cvx.vec2
  let { NORM_MUL, NORM_NEG, NORM_POW_2, ORTHOGONAL_MUL, ORTHOGONAL_REFL,
        ORTHOGONAL_TO_SUBSPACE_EXISTS_GEN, REAL_ABS_NORM, SPAN_EQ_SELF, SPAN_OF_SUBSPACE,
        SUBSPACE_ADD, SUBSPACE_MUL, SUBSPACE_NEG, SUBSPACE_SUB,
        .. } := D.ra.ts.cn.cx.cvx.vec3
  let { orthogonal, VECTOR_MUL_ASSOC, VECTOR_MUL_LID, VECTOR_MUL_LNEG, VECTOR_MUL_LZERO,
        VECTOR_MUL_RNEG, VECTOR_NEG_NEG, VECTOR_SUB_EQ, VECTOR_SUB_RZERO,
        .. } := D.ra.ts.cn.cx.cvx.vec4
  let { LINEAR_REFLECT_ALONG, REFLECT_ALONG_INVOLUTION, .. } := D.ra.ts.cn.cx.cvx.det
  let { CLOSED_SUBSPACE, .. } := D.ra.ts.cn.cx.cvx.top1
  let { COMPACT_CONTINUOUS_IMAGE, COMPACT_INTER_CLOSED, COMPACT_SPHERE,
        CONTINUOUS_ATTAINS_SUP, .. } := D.ra.ts.cn.cx.cvx.top2
  let { CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID, CONTINUOUS_ON_INV,
        CONTINUOUS_ON_LIFT_NORM, CONTINUOUS_ON_LIFT_NORM_COMPOSE, CONTINUOUS_ON_MUL,
        CONTINUOUS_ON_SUBSET, .. } := D.ra.ts.cn.cx.cvx.top3
  let { IN_SEGMENT, IN_SPHERE_0, LINEAR_CONTINUOUS_ON, .. } := D.ra.ts.cn.cx.cvx.top4
  let { SEGMENT_REFL, SEGMENT_SYM, TOPSPACE_EUCLIDEAN_SUBTOPOLOGY,
        .. } := D.ra.ts.cn.cx.cvx.top5
  let { SEGMENT_SUBSET_CONVEX, SUBSPACE_IMP_CONVEX, .. } := D.ra.ts.cn.ms.ig.dv.dg.qconvex
  let { NORM_REFLECT_ALONG, reflect_along, .. } := D.ra.ts.cn.ms.ig.dv.dg.qdet
  let { HOMOTOPIC_WITH_EQ, HOMOTOPIC_WITH_REFL, HOMOTOPIC_WITH_SYM, HOMOTOPIC_WITH_TRANS,
        SUBTOPOLOGY_SUBTOPOLOGY, .. } := D.ra.ts.cn.ms.ig.dv.dg.qmetric
  let { HOMOTOPIC_WITH_IMP_CONTINUOUS, HOMOTOPIC_WITH_IMP_SUBSET, HOMOTOPIC_WITH_LINEAR,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths1
  let { HOMOTOPIC_WITH_REFLECTIONS_ALONG, .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths2
  let { I_DEF, I_O_ID, .. } := D.ra.ts.cn.ms.ig.dv.dg.qsession
  let { CONTINUOUS_MAP_EUCLIDEAN, CONTINUOUS_MAP_EUCLIDEAN2, CONTINUOUS_ON_LIFT_DOT2,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { SEGMENT_CONVEX_HULL, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx3
  -- @@SCOPE END

  -- `last o CONJUNCTS` as a theorem function.
  let lastc : thm → ExceptT String IO thm := fun th =>
    liftExcept (HolCore.Lib.last (CONJUNCTS th))

  let ODD_MAP_HOMOTOPY_LEMMA ← prove
   r"!f:real^N->real^N s t.
        subspace s /\ subspace t /\ dim s + 1 = dim t /\ s SUBSET t /\
        f continuous_on (sphere(vec 0,&1) INTER t) /\
        IMAGE f (sphere(vec 0,&1) INTER t) SUBSET (sphere(vec 0,&1) INTER t) /\
        (!x. x IN (sphere(vec 0,&1) INTER t) ==> f(--x) = --(f x))
        ==> ?g. g continuous_on (sphere(vec 0,&1) INTER t) /\
                IMAGE g (sphere(vec 0,&1) INTER t) SUBSET
                sphere(vec 0,&1) INTER t /\
                IMAGE g (sphere(vec 0,&1) INTER s) SUBSET
                sphere(vec 0,&1) INTER s /\
                (!x. x IN (sphere(vec 0,&1) INTER t) ==> g(--x) = --(g x)) /\
                homotopic_with (\z. T)
                 (subtopology euclidean (sphere(vec 0,&1) INTER t),
                  subtopology euclidean (sphere(vec 0,&1) INTER t))
                 f g"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"sphere(vec 0:real^N,&1) INTER s = {}") THENL
     [EXISTS_TAC (← q r"f:real^N->real^N") THEN
      ASM_REWRITE_TAC [HOMOTOPIC_WITH_REFL, IMAGE_CLAUSES, SUBSET_EMPTY] THEN
      ASM_REWRITE_TAC [CONTINUOUS_MAP_EUCLIDEAN2],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"?g. vector_polynomial_function g /\
          (!x. x IN sphere(vec 0:real^N,&1) INTER t ==> g x IN t) /\
          (!x. x IN sphere(vec 0,&1) INTER t ==> g(--x) = --(g x)) /\
          (!x. x IN sphere (vec 0,&1) INTER t ==> norm(f x - g x) < &1 / &2)")
    STRIP_ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"f:real^N->real^N", ← q r"sphere(vec 0:real^N,&1) INTER t",
                       ← q r"&1 / &2", ← q r"t:real^N->bool"]
          STONE_WEIERSTRASS_VECTOR_POLYNOMIAL_FUNCTION_SUBSPACE) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_SIMP_TAC [COMPACT_INTER_CLOSED, COMPACT_SPHERE, CLOSED_SUBSPACE] THEN
      ANTS_TAC THENL [ASM SET_TAC [], REWRITE_TAC [SUBSET, FORALL_IN_IMAGE]] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->real^N") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"\x. inv(&2) % ((g:real^N->real^N) x - g(--x))") THEN
      REWRITE_TAC [← VECTOR_ARITH (← q r"--(a % (x - y)):real^N = a % (y - x)")] THEN
      REWRITE_TAC [VECTOR_NEG_NEG, IN_SPHERE_0, IN_INTER] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [IN_SPHERE_0, IN_INTER]) THEN
      ASM_SIMP_TAC [SUBSPACE_MUL_EQ, SUBSPACE_SUB, NORM_NEG, SUBSPACE_NEG_EQ] THEN
      ASM_SIMP_TAC [VECTOR_POLYNOMIAL_FUNCTION_CMUL, VECTOR_POLYNOMIAL_FUNCTION_SUB,
                    VECTOR_POLYNOMIAL_FUNCTION_REFLECT, ETA_AX] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC (← NORM_ARITH
       (← q r"norm(f - g:real^N) < e /\ norm(--f - g') < e
        ==> norm(f - inv(&2) % (g - g')) < e")) THEN
      ASM_MESON_TAC [NORM_NEG, SUBSPACE_NEG, VECTOR_NEG_NEG],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!x. x IN sphere(vec 0,&1) INTER t ==> ~((g:real^N->real^N) x = vec 0)")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"x:real^N") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real^N")) THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [SUBSET]) THEN
      REWRITE_TAC [FORALL_IN_IMAGE, IN_SPHERE_0] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [IN_SPHERE_0]) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"x:real^N")) THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [IN_INTER, IN_SPHERE_0] THEN
      CONV_TAC (fun t => NORM_ARITH t),
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(g:real^N->real^N) differentiable_on
                  sphere(vec 0,&1) INTER s")
    ASSUME_TAC THENL
     [ASM_SIMP_TAC [DIFFERENTIABLE_ON_VECTOR_POLYNOMIAL_FUNCTION], ALL_TAC] THEN
    ABBREV_TAC (← q r"(h:real^N->real^N) = \x. inv(norm(g x)) % g x") THEN
    SUBGOAL_THEN
     (← q r"!x. x IN sphere(vec 0,&1) INTER t
          ==> (h:real^N->real^N) x IN sphere(vec 0,&1) INTER t")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN
      ASM_SIMP_TAC [SUBSPACE_MUL, IN_INTER, IN_SPHERE_0, NORM_MUL] THEN
      REWRITE_TAC [REAL_ABS_INV, REAL_ABS_NORM] THEN
      ASM_SIMP_TAC [REAL_MUL_LINV, NORM_EQ_0, ← GSYM IN_SPHERE_0],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!x. x IN sphere(vec 0,&1) INTER t ==> h(--x) = --((h:real^N->real^N) x)")
    ASSUME_TAC THENL
     [EXPAND_TAC "h" THEN REWRITE_TAC [] THEN
      ASM_SIMP_TAC [NORM_NEG, VECTOR_MUL_RNEG],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"(h:real^N->real^N) differentiable_on sphere(vec 0,&1) INTER t")
    ASSUME_TAC THENL
     [EXPAND_TAC "h" THEN MATCH_MP_TAC DIFFERENTIABLE_ON_MUL THEN
      ASM_SIMP_TAC [DIFFERENTIABLE_ON_VECTOR_POLYNOMIAL_FUNCTION, o_DEF] THEN
      SUBGOAL_THEN
       (← q r"(\x. lift(inv(norm((g:real^N->real^N) x)))) =
        (lift o inv o drop) o (\x. lift(norm x)) o (g:real^N->real^N)")
      SUBST1_TAC THENL [REWRITE_TAC [o_DEF, LIFT_DROP], ALL_TAC] THEN
      MATCH_MP_TAC DIFFERENTIABLE_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_ON_COMPOSE THEN
        ASM_SIMP_TAC [DIFFERENTIABLE_ON_VECTOR_POLYNOMIAL_FUNCTION] THEN
        MATCH_MP_TAC DIFFERENTIABLE_ON_NORM THEN
        ASM_REWRITE_TAC [← SET_RULE
         (← q r"~(z IN IMAGE f s) <=> !x. x IN s ==> ~(f x = z)")],
        MATCH_MP_TAC DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON THEN
        REWRITE_TAC [← GSYM REAL_DIFFERENTIABLE_AT] THEN
        REWRITE_TAC [FORALL_IN_IMAGE, IN_SPHERE_0] THEN
        X_GEN_TAC (← q r"x:real^N") THEN
        ASM_CASES_TAC (← q r"x:real^N = vec 0") THEN
        ASM_REWRITE_TAC [NORM_0, REAL_OF_NUM_EQ, ARITH_EQ] THEN DISCH_TAC THEN
        REWRITE_TAC [← GSYM REAL_DIFFERENTIABLE_AT, o_THM] THEN
        GEN_REWRITE_TAC LAND_CONV [← GSYM ETA_AX] THEN
        MATCH_MP_TAC REAL_DIFFERENTIABLE_INV_ATREAL THEN
        ASM_SIMP_TAC [REAL_DIFFERENTIABLE_ID, NORM_EQ_0, IN_SPHERE_0]],
      ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"h:real^N->real^N", ← q r"s:real^N->bool", ← q r"t:real^N->bool"]
     NONSURJECTIVE_DIFFERENTIABLE_SPHEREMAP_LOWDIM) THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"s + 1 = t ==> s < t")] THEN ANTS_TAC THENL
     [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
        DIFFERENTIABLE_ON_SUBSET)) THEN
      ASM SET_TAC [],
      DISCH_THEN (MP_TAC o MATCH_MP (← SET_RULE
       (← q r"~(IMAGE f s = t)
        ==> s SUBSET t /\ IMAGE f t SUBSET t
            ==> ?q. q IN t /\ ~(q IN IMAGE f s)"))) THEN
      ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"q:real^N") STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN
     (← q r"~((--q) IN IMAGE (h:real^N->real^N) (sphere(vec 0,&1) INTER s))")
    ASSUME_TAC THENL
     [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
       (← q r"~(q IN IMAGE f s)
        ==> (!x. n(n x) = x) /\ (!x. n x IN s <=> x IN s) /\
            (!x. x IN s ==> f(n x) = n(f x))
            ==> ~(n q IN IMAGE f s)"))) THEN
      REWRITE_TAC [VECTOR_NEG_NEG] THEN
      CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      ASM_SIMP_TAC [IN_INTER, IN_SPHERE_0, SUBSPACE_NEG_EQ, NORM_NEG],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"?p. p IN sphere(vec 0,&1) INTER t /\
          !x:real^N. x IN s ==> orthogonal p x")
    STRIP_ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"t:real^N->bool"]
          ORTHOGONAL_TO_SUBSPACE_EXISTS_GEN) THEN
      ASM_SIMP_TAC [SPAN_OF_SUBSPACE, PSUBSET] THEN
      ANTS_TAC THENL [ASM_MESON_TAC [← ARITH_RULE (← q r"~(s + 1 = s)")], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"p:real^N") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"inv(norm p) % p:real^N") THEN
      ASM_SIMP_TAC [ORTHOGONAL_MUL, IN_INTER, IN_SPHERE_0, SUBSPACE_MUL] THEN
      REWRITE_TAC [NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
      ASM_SIMP_TAC [REAL_MUL_LINV, NORM_EQ_0],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"?k. homotopic_with (\x. T)
            (subtopology euclidean (sphere(vec 0,&1) INTER t),
             subtopology euclidean (sphere(vec 0,&1) INTER t))
            h k /\
          (!x. x IN (sphere(vec 0,&1) INTER t) ==> k(--x) = --(k x)) /\
          DISJOINT (IMAGE k (sphere(vec 0,&1) INTER s)) {p:real^N,--p}")
    STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC (← q r"p:real^N = q \/ p = --q") THENL
       [EXISTS_TAC (← q r"h:real^N->real^N") THEN
        FIRST_X_ASSUM (DISJ_CASES_THEN SUBST1_TAC) THEN
        ASM_REWRITE_TAC [HOMOTOPIC_WITH_REFL, VECTOR_NEG_NEG] THEN
        ASM_REWRITE_TAC [CONTINUOUS_MAP_EUCLIDEAN2] THEN
        ASM_SIMP_TAC [DIFFERENTIABLE_IMP_CONTINUOUS_ON] THEN ASM SET_TAC [],
        FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [DE_MORGAN_THM]) THEN
        STRIP_TAC] THEN
      EXISTS_TAC
       (← q r"reflect_along p o reflect_along (q - p) o (h:real^N->real^N)") THEN
      REWRITE_TAC [← SET_RULE
       (← q r"DISJOINT s {a,b} <=> !x. x IN s ==> ~(x = a) /\ ~(x = b)")] THEN
      REWRITE_TAC [FORALL_IN_IMAGE, o_THM, REFLECT_ALONG_GALOIS] THEN
      REWRITE_TAC [REFLECT_ALONG_REFL, REFLECT_ALONG_NEG] THEN
      ASM_SIMP_TAC [REFLECT_ALONG_INVOLUTION] THEN CONJ_TAC THENL
       [ALL_TAC,
        RULE_ASSUM_TAC (REWRITE_RULE [IN_IMAGE, IN_INTER, IN_SPHERE_0]) THEN
        ASM_SIMP_TAC [REFLECT_ALONG_SWITCH, IN_INTER, IN_SPHERE_0] THEN
        ASM_MESON_TAC [VECTOR_NEG_NEG]] THEN
      SUBGOAL_THEN (← q r"h:real^N->real^N = reflect_along p o reflect_along p o h")
       (fun th => GEN_REWRITE_TAC LAND_CONV [th])
      THENL [SIMP_TAC [FUN_EQ_THM, o_THM, REFLECT_ALONG_INVOLUTION], ALL_TAC] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_LEFT THEN
      EXISTS_TAC (← q r"sphere(vec 0:real^N,&1) INTER t") THEN CONJ_TAC THENL
       [ALL_TAC,
        SIMP_TAC [LINEAR_REFLECT_ALONG, LINEAR_CONTINUOUS_ON] THEN
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_INTER, IN_SPHERE_0] THEN
        SIMP_TAC [NORM_REFLECT_ALONG] THEN REPEAT STRIP_TAC THEN
        REWRITE_TAC [reflect_along] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [IN_INTER, IN_SPHERE_0]) THEN
        ASM_SIMP_TAC [SUBSPACE_MUL, SUBSPACE_SUB]] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
      EXISTS_TAC (← q r"sphere(vec 0:real^N,&1) INTER t") THEN
      ASM_SIMP_TAC [DIFFERENTIABLE_IMP_CONTINUOUS_ON] THEN
      CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_REFLECTIONS_ALONG THEN CONJ_TAC THENL
       [DISCH_TAC THEN
        REPEAT (FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [IN_INTER])) THEN
        ASM_REWRITE_TAC [IN_SPHERE_0, NORM_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV,
        ASM_REWRITE_TAC [VECTOR_SUB_EQ]] THEN
      X_GEN_TAC (← q r"r:real^N") THEN DISCH_TAC THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_INTER, IN_SPHERE_0] THEN
      SIMP_TAC [NORM_REFLECT_ALONG] THEN REWRITE_TAC [reflect_along] THEN
      X_GEN_TAC (← q r"x:real^N") THEN STRIP_TAC THEN MATCH_MP_TAC SUBSPACE_SUB THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUBSPACE_MUL THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [IN_SEGMENT]) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [IN_INTER]) THEN
      ASM_SIMP_TAC [LEFT_IMP_EXISTS_THM, SUBSPACE_ADD,
                    SUBSPACE_MUL, SUBSPACE_SUB],
      ALL_TAC] THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
    SUBGOAL_THEN
     (← q r"?r. &0 < r /\ r < &1 /\
          !x. x IN (sphere(vec 0,&1) INTER s)
              ==> abs(p dot (k:real^N->real^N) x) < r")
    STRIP_ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"\x:real^N. abs(p dot x)",
                       ← q r"IMAGE (k:real^N->real^N) (sphere (vec 0,&1) INTER s)"]
          CONTINUOUS_ATTAINS_SUP) THEN
      ASM_REWRITE_TAC [IMAGE_EQ_EMPTY] THEN ANTS_TAC THENL
       [SIMP_TAC [o_DEF, CONTINUOUS_ON_LIFT_DOT2, CONTINUOUS_ON_ID,
                  CONTINUOUS_ON_LIFT_ABS, CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
        ASM_SIMP_TAC [CLOSED_SUBSPACE, COMPACT_INTER_CLOSED, COMPACT_SPHERE] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        ASM SET_TAC [],
        REWRITE_TAC [FORALL_IN_IMAGE]] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"c:real^N") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"abs((p:real^N) dot c) < &1") ASSUME_TAC THENL
       [MATCH_MP_TAC (← REAL_ARITH
         (← q r"!y. x <= y /\ y = &1 /\ ~(x = y) ==> x < &1")) THEN
        EXISTS_TAC (← q r"norm(p:real^N) * norm(c:real^N)") THEN
        REWRITE_TAC [NORM_CAUCHY_SCHWARZ_ABS] THEN
        SUBGOAL_THEN (← q r"c IN sphere(vec 0:real^N,&1) INTER t") ASSUME_TAC THENL
         [ASM SET_TAC [],
          RULE_ASSUM_TAC (REWRITE_RULE [IN_INTER, IN_SPHERE_0])] THEN
        ASM_CASES_TAC (← q r"abs((p:real^N) dot c) = &1") THENL
         [REWRITE_TAC [NORM_CAUCHY_SCHWARZ_EQUAL],
          ASM_REWRITE_TAC [REAL_MUL_LID]] THEN
        REWRITE_TAC [COLLINEAR_3_DOT_MULTIPLES, VECTOR_SUB_RZERO] THEN
        ASM_REWRITE_TAC [← GSYM NORM_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ONCE_REWRITE_TAC [DOT_SYM] THEN FIRST_X_ASSUM (DISJ_CASES_THEN SUBST1_TAC o
          MATCH_MP (← REAL_ARITH (← q r"abs x = &1 ==> x = &1 \/ x = -- &1"))) THEN
        REWRITE_TAC [VECTOR_MUL_LNEG, VECTOR_MUL_LID] THEN ASM SET_TAC [],
        EXISTS_TAC (← q r"(&1 + abs((p:real^N) dot c)) / &2") THEN
        REPEAT (CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC (← REAL_ARITH
         (← q r"abs x <= abs a /\ abs a < &1 ==> abs x < (&1 + abs a) / &2")) THEN
        ASM_SIMP_TAC []],
      ALL_TAC] THEN
    ABBREV_TAC (← q r"r' = (&1 + r) / &2") THEN
    SUBGOAL_THEN (← q r"&0 < r' /\ r < r' /\ r' < &1") STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    ABBREV_TAC
     (← q r"i = \x. if abs(p dot x) >= r' then (x:real^N) else
              x - ((r' - max r (abs(p dot x))) / (r' - r) * (p dot x)) % p") THEN
    ABBREV_TAC (← q r"j = \x. inv(norm(i x)) % (i:real^N->real^N) x") THEN
    SUBGOAL_THEN (← q r"(i:real^N->real^N) continuous_on sphere(vec 0,&1) INTER t")
    ASSUME_TAC THENL
     [EXPAND_TAC "i" THEN REWRITE_TAC [← GSYM CONTINUOUS_MAP_EUCLIDEAN] THEN
      REWRITE_TAC [real_ge] THEN MATCH_MP_TAC CONTINUOUS_MAP_CASES_LE THEN
      REWRITE_TAC [SUBTOPOLOGY_SUBTOPOLOGY, TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      REPEAT CONJ_TAC THENL
       [SIMP_TAC [CONTINUOUS_MAP_REAL_CONST, CONTINUOUS_MAP_FROM_SUBTOPOLOGY],
        MATCH_MP_TAC CONTINUOUS_MAP_REAL_ABS THEN
        MATCH_MP_TAC CONTINUOUS_MAP_DOT THEN
        REWRITE_TAC [CONTINUOUS_MAP_EUCLIDEAN] THEN
        REWRITE_TAC [CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID],
        SIMP_TAC [CONTINUOUS_MAP_ID, CONTINUOUS_MAP_FROM_SUBTOPOLOGY],
        MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_SUB THEN
        SIMP_TAC [CONTINUOUS_MAP_ID, CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_MUL THEN
        REWRITE_TAC [CONTINUOUS_MAP_EUCLIDEAN, CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN
        SIMP_TAC [CONTINUOUS_MAP_DOT, CONTINUOUS_MAP_EUCLIDEAN,
                  CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID] THEN
        REWRITE_TAC [real_div] THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_RMUL THEN
        MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
        SIMP_TAC [CONTINUOUS_MAP_REAL_CONST, CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_REAL_MAX THEN
        SIMP_TAC [CONTINUOUS_MAP_REAL_CONST, CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_REAL_ABS THEN
        MATCH_MP_TAC CONTINUOUS_MAP_DOT THEN
        REWRITE_TAC [CONTINUOUS_MAP_EUCLIDEAN] THEN
        REWRITE_TAC [CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID],
        X_GEN_TAC (← q r"x:real^N") THEN DISCH_THEN (SUBST1_TAC o SYM o CONJUNCT2) THEN
        ASM_SIMP_TAC [← REAL_ARITH (← q r"r < r' ==> r' - max r r' = &0")] THEN
        REWRITE_TAC [real_div, REAL_MUL_LZERO, VECTOR_MUL_LZERO,
                     VECTOR_SUB_RZERO]],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x. (i:real^N->real^N) (--x) = --(i x)") ASSUME_TAC THENL
     [X_GEN_TAC (← q r"x:real^N") THEN EXPAND_TAC "i" THEN
      REWRITE_TAC [DOT_RNEG, REAL_ABS_NEG] THEN
      COND_CASES_TAC THEN REWRITE_TAC [] THEN REWRITE_TAC [REAL_MUL_RNEG] THEN
      REWRITE_TAC [VECTOR_MUL_LNEG, ← VECTOR_ARITH (← q r"--x - --a:real^N = --(x - a)")],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!x. x IN sphere(vec 0,&1) INTER t ==> ~((i:real^N->real^N) x = vec 0)")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      EXPAND_TAC "i" THEN REWRITE_TAC [] THEN
      COND_CASES_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC (REWRITE_RULE [DOT_RZERO]) THEN
        ASM_REAL_ARITH_TAC,
        REWRITE_TAC [VECTOR_SUB_EQ]] THEN
      ASM_CASES_TAC
       (← q r"(r' - max r (abs((p:real^N) dot x))) / (r' - r) * abs(p dot x) < &1")
      THENL
       [DISCH_THEN (MP_TAC o AP_TERM (← q r"\y:real^N. y dot x")) THEN
        RULE_ASSUM_TAC (REWRITE_RULE [IN_INTER, IN_SPHERE_0]) THEN
        ASM_REWRITE_TAC [← GSYM NORM_POW_2, DOT_LMUL, ← GSYM REAL_MUL_ASSOC] THEN
        REWRITE_TAC [← GSYM REAL_POW_2] THEN
        ONCE_REWRITE_TAC [← GSYM REAL_POW2_ABS] THEN
        REWRITE_TAC [REAL_POW_2, REAL_MUL_ASSOC] THEN MATCH_MP_TAC (← REAL_ARITH
         (← q r"x < &1 /\ x * y <= x * &1 ==> ~(abs(&1) * abs(&1) = x * y)")) THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [REAL_ABS_POS] THEN
          ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_SUB_LT] THEN ASM_REAL_ARITH_TAC,
          TRANS_TAC REAL_LE_TRANS (← q r"norm(p:real^N) * norm(x:real^N)") THEN
          REWRITE_TAC [NORM_CAUCHY_SCHWARZ_ABS] THEN ASM_REWRITE_TAC [] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV],
        FIRST_X_ASSUM (MP_TAC o MATCH_MP (← REAL_ARITH
         (← q r"~(x < &1) ==> x <= &1 * &1 ==> x = &1"))) THEN
        ANTS_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL2 THEN
          ASM_SIMP_TAC [REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ, REAL_SUB_LT] THEN
          REPEAT (CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
          RULE_ASSUM_TAC (REWRITE_RULE [IN_INTER, IN_SPHERE_0]) THEN
          TRANS_TAC REAL_LE_TRANS (← q r"norm(p:real^N) * norm(x:real^N)") THEN
          REWRITE_TAC [NORM_CAUCHY_SCHWARZ_ABS] THEN ASM_REWRITE_TAC [] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV,
          DISCH_THEN (MP_TAC o MATCH_MP (← REAL_ARITH
           (← q r"x * abs y = &1 ==> x * y = &1 \/ x * y = -- &1"))) THEN
          DISCH_THEN (DISJ_CASES_THEN SUBST1_TAC) THEN
          UNDISCH_TAC (← q r"~(abs((p:real^N) dot x) >= r')") THEN
          SIMP_TAC [CONTRAPOS_THM, DOT_RMUL, ← GSYM NORM_POW_2] THEN
          RULE_ASSUM_TAC (REWRITE_RULE [IN_INTER, IN_SPHERE_0]) THEN
          ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC]],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"(j:real^N->real^N) continuous_on sphere(vec 0,&1) INTER t")
    ASSUME_TAC THENL
     [EXPAND_TAC "j" THEN REWRITE_TAC [] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      ASM_REWRITE_TAC [o_DEF] THEN
      MATCH_MP_TAC (← REWRITE_RULE [o_DEF] CONTINUOUS_ON_INV) THEN
      ASM_REWRITE_TAC [NORM_EQ_0] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!x. x IN sphere(vec 0,&1) INTER t
          ==> (j:real^N->real^N) x IN sphere(vec 0,&1) INTER t")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      EXPAND_TAC "j" THEN REWRITE_TAC [IN_INTER, IN_SPHERE_0] THEN
      REWRITE_TAC [NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
      ASM_SIMP_TAC [REAL_MUL_LINV, NORM_EQ_0] THEN MATCH_MP_TAC SUBSPACE_MUL THEN
      EXPAND_TAC "i" THEN
      RULE_ASSUM_TAC (REWRITE_RULE [IN_INTER, IN_SPHERE_0]) THEN
      REWRITE_TAC [] THEN ASM_REWRITE_TAC [] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC [SUBSPACE_SUB, SUBSPACE_MUL],
      ALL_TAC] THEN
    EXISTS_TAC (← q r"(j:real^N->real^N) o (k:real^N->real^N)") THEN CONJ_TAC THENL
     [ASM_MESON_TAC [CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_SUBSET], ALL_TAC] THEN
    ONCE_REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC (← SET_RULE
       (← q r"IMAGE f (p INTER t) SUBSET p INTER t /\
        IMAGE f (p INTER s) SUBSET s /\ s SUBSET t
        ==> IMAGE f (p INTER t) SUBSET p INTER t /\
            IMAGE f (p INTER s) SUBSET p INTER s")) THEN
      ASM_REWRITE_TAC [IMAGE_o] THEN
      CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
      REPEAT STRIP_TAC THEN EXPAND_TAC "j" THEN REWRITE_TAC [] THEN
      MATCH_MP_TAC SUBSPACE_MUL THEN ASM_REWRITE_TAC [] THEN
      EXPAND_TAC "i" THEN REWRITE_TAC [real_ge] THEN
      MP_TAC (← REAL_ARITH (← q r"!x. r < r' ==> x < r ==> ~(r' <= x)")) THEN
      ASM_SIMP_TAC [] THEN DISCH_THEN (K ALL_TAC) THEN
      ASM_SIMP_TAC [← REAL_ARITH (← q r"x < r ==> max r x = r")] THEN
      ASM_SIMP_TAC [REAL_DIV_REFL, REAL_SUB_0, REAL_LT_IMP_NE] THEN
      SUBGOAL_THEN (← q r"(k:real^N->real^N) x IN t") MP_TAC THENL
       [ASM SET_TAC [], SPEC_TAC (← q r"(k:real^N->real^N) x", ← q r"y:real^N")] THEN
      X_GEN_TAC (← q r"y:real^N") THEN DISCH_TAC THEN REWRITE_TAC [REAL_MUL_LID] THEN
      SUBGOAL_THEN (← q r"(y:real^N) IN span (p INSERT s)") MP_TAC THENL
       [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
         (← q r"y IN t ==> span t = t /\ p = span t ==> y IN p"))) THEN
        ASM_REWRITE_TAC [SPAN_EQ_SELF] THEN MATCH_MP_TAC DIM_EQ_SPAN THEN
        CONJ_TAC THENL [ASM SET_TAC [], REWRITE_TAC [DIM_INSERT]] THEN
        ASM_SIMP_TAC [SPAN_OF_SUBSPACE] THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC [LE_REFL] THEN
        SUBGOAL_THEN (← q r"orthogonal (p:real^N) p") MP_TAC THENL
         [ASM SET_TAC [], REWRITE_TAC [ORTHOGONAL_REFL]] THEN
        DISCH_THEN SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC (REWRITE_RULE [IN_INTER, IN_SPHERE_0, NORM_0]) THEN
        ASM_REAL_ARITH_TAC,
        ASM_SIMP_TAC [SPAN_BREAKDOWN_EQ, SPAN_OF_SUBSPACE] THEN
        DISCH_THEN (X_CHOOSE_TAC (← q r"k:real")) THEN
        SUBGOAL_THEN (← q r"orthogonal p (y - k % p:real^N)") MP_TAC THENL
         [ASM SET_TAC [], REWRITE_TAC [orthogonal, DOT_RSUB]] THEN
        REWRITE_TAC [DOT_RMUL, ← GSYM NORM_POW_2, REAL_SUB_0] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [IN_INTER, IN_SPHERE_0]) THEN
        ASM_SIMP_TAC [REAL_POW_2, REAL_MUL_RID]],
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC [o_THM] THEN EXPAND_TAC "j" THEN REWRITE_TAC [] THEN
      ASM_SIMP_TAC [NORM_NEG, VECTOR_MUL_RNEG],
      ALL_TAC] THEN
    TRANS_TAC HOMOTOPIC_WITH_TRANS (← q r"h:real^N->real^N") THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       (← q r"homotopic_with (\z. T)
         (subtopology euclidean (sphere(vec 0:real^N,&1) INTER t),
          subtopology euclidean (t DELETE (vec 0:real^N)))
         f g")
      MP_TAC THENL
       [MATCH_MP_TAC HOMOTOPIC_WITH_LINEAR THEN
        ASM_SIMP_TAC [CONTINUOUS_ON_VECTOR_POLYNOMIAL_FUNCTION] THEN
        X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN REWRITE_TAC [← SET_RULE
          (← q r"s SUBSET t DELETE v <=> s SUBSET t /\ ~(v IN s)")] THEN
        CONJ_TAC THENL
         [REWRITE_TAC [SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
          ASM_SIMP_TAC [SUBSPACE_IMP_CONVEX] THEN ASM SET_TAC [],
          DISCH_THEN (MP_TAC o MATCH_MP SEGMENT_BOUND) THEN
          SUBGOAL_THEN
           (← q r"(f:real^N->real^N) x IN sphere(vec 0,&1) /\
            norm(f x - g x) < &1/ &2")
          MP_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
          REWRITE_TAC [IN_SPHERE_0] THEN CONV_TAC (fun t => NORM_ARITH t)],
        DISCH_THEN (MP_TAC o
          ISPECL [← q r"\y:real^N. inv(norm y) % y",
                  ← q r"sphere(vec 0:real^N,&1) INTER t"] o
          MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ]
          HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT)) THEN
        ASM_REWRITE_TAC [o_DEF] THEN ANTS_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
            REWRITE_TAC [o_DEF, CONTINUOUS_ON_ID] THEN
            MATCH_MP_TAC (← REWRITE_RULE [o_DEF] CONTINUOUS_ON_INV) THEN
            SIMP_TAC [IN_DELETE, NORM_EQ_0] THEN
            REWRITE_TAC [← REWRITE_RULE [o_DEF] CONTINUOUS_ON_LIFT_NORM],
            REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_DELETE, IN_INTER] THEN
            ASM_SIMP_TAC [SUBSPACE_MUL, IN_SPHERE_0, NORM_MUL,
                          REAL_ABS_MUL] THEN
            SIMP_TAC [REAL_ABS_INV, REAL_ABS_NORM, REAL_MUL_LINV, NORM_EQ_0]],
          MATCH_MP_TAC (← ONCE_REWRITE_RULE [IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
          REWRITE_TAC [TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
          RULE_ASSUM_TAC (REWRITE_RULE
           [SUBSET, IN_INTER, FORALL_IN_IMAGE, IN_SPHERE_0]) THEN
          ASM_SIMP_TAC [IN_SPHERE_0, IN_INTER,
                        REAL_INV_1, VECTOR_MUL_LID]]],
      ALL_TAC] THEN
    TRANS_TAC HOMOTOPIC_WITH_TRANS (← q r"I o (k:real^N->real^N)") THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC [I_O_ID], ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
    EXISTS_TAC (← q r"sphere(vec 0:real^N,&1) INTER t") THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN
     (← q r"homotopic_with (\z. T)
       (subtopology euclidean (sphere(vec 0:real^N,&1) INTER t),
        subtopology euclidean (t DELETE (vec 0:real^N)))
       i I")
    MP_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_WITH_LINEAR THEN
      ASM_REWRITE_TAC [CONTINUOUS_ON_ID, I_DEF] THEN
      X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      EXPAND_TAC "i" THEN REWRITE_TAC [real_ge] THEN COND_CASES_TAC THENL
       [REWRITE_TAC [SEGMENT_REFL, SING_SUBSET, IN_DELETE] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [IN_INTER, IN_SPHERE_0]) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC (REWRITE_RULE [NORM_0]) THEN ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [SUBSET_DELETE] THEN CONJ_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
        RULE_ASSUM_TAC (REWRITE_RULE [IN_INTER, IN_SPHERE_0]) THEN
        ASM_SIMP_TAC [SUBSPACE_IMP_CONVEX, SUBSPACE_MUL, SUBSPACE_SUB]] THEN
      ONCE_REWRITE_TAC [SEGMENT_SYM] THEN
      REWRITE_TAC [IN_SEGMENT, ← VECTOR_ARITH
       (← q r"vec 0:real^N = (&1 - u) % x + u % (x - p) <=> x = u % p")] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"u:real") MP_TAC) THEN
      DISCH_THEN (MP_TAC o lastc) THEN DISCH_THEN (fun th => tactic_of do
        pure (MP_TAC th THEN MP_TAC (← AP_TERM (← q r"norm:real^N->real") th))) THEN
      REWRITE_TAC [VECTOR_MUL_ASSOC] THEN REWRITE_TAC [NORM_MUL] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [IN_INTER, IN_SPHERE_0]) THEN
      ASM_REWRITE_TAC [← REAL_ARITH (← q r"&1 = abs x * &1 <=> x = &1 \/ x = -- &1")] THEN
      DISCH_THEN (DISJ_CASES_THEN SUBST1_TAC) THEN
      REWRITE_TAC [VECTOR_MUL_LID, VECTOR_MUL_LNEG] THEN
      UNDISCH_TAC (← q r"~(r' <= abs((p:real^N) dot x))") THEN
      SIMP_TAC [CONTRAPOS_THM, DOT_RNEG] THEN
      ASM_REWRITE_TAC [← GSYM NORM_POW_2] THEN ASM_ARITH_TAC,
      DISCH_THEN (MP_TAC o
        ISPECL [← q r"\y:real^N. inv(norm y) % y",
                ← q r"sphere(vec 0:real^N,&1) INTER t"] o
        MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ]
        HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT)) THEN
      ASM_REWRITE_TAC [o_DEF] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
          REWRITE_TAC [o_DEF, CONTINUOUS_ON_ID] THEN
          MATCH_MP_TAC (← REWRITE_RULE [o_DEF] CONTINUOUS_ON_INV) THEN
          SIMP_TAC [IN_DELETE, NORM_EQ_0] THEN
          REWRITE_TAC [← REWRITE_RULE [o_DEF] CONTINUOUS_ON_LIFT_NORM],
          REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_DELETE, IN_INTER] THEN
          ASM_SIMP_TAC [SUBSPACE_MUL, IN_SPHERE_0, NORM_MUL,
                        REAL_ABS_MUL] THEN
          SIMP_TAC [REAL_ABS_INV, REAL_ABS_NORM, REAL_MUL_LINV, NORM_EQ_0]],
        GEN_REWRITE_TAC RAND_CONV [HOMOTOPIC_WITH_SYM] THEN
        MATCH_MP_TAC (← ONCE_REWRITE_RULE [IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
        REWRITE_TAC [TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
        RULE_ASSUM_TAC (REWRITE_RULE
         [SUBSET, IN_INTER, FORALL_IN_IMAGE, IN_SPHERE_0]) THEN
        ASM_SIMP_TAC [IN_SPHERE_0, IN_INTER, I_DEF,
                      REAL_INV_1, VECTOR_MUL_LID]]])

  pure { ODD_MAP_HOMOTOPY_LEMMA }
/- ------------------------------------------------------------------------- -/
/- Borsuk's odd mapping degree theorem.                                      -/
/- (moretop.ml 1336-1521)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MOE where
  BORSUK_ODD_MAPPING_GEN : thm
  BORSUK_ODD_MAPPING : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOE [HolBase] (D : MoreTopDeps) (BMOD : MOD) : ExceptT String IO MOE := do
  -- @@SCOPE BEGIN
  let { ODD_MAP_HOMOTOPY_LEMMA, .. } := BMOD
  let { brouwer_degree, brouwer_degree1, BROUWER_DEGREE1_EQ, BROUWER_DEGREE1_HOMOTOPIC,
        BROUWER_DEGREE1_ID, BROUWER_DEGREE1_REFLECT_ALONG, .. } := D.qdegree
  let { REFLECT_ALONG_NEG, REFLECT_BASIS_ALONG_BASIS, .. } := D.qdeterminants
  let { CONTINUOUS_MAP_EQ, CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE, .. } := D.qmetric
  let { BORSUK_ODD_MAPPING_DEGREE_STEP, .. } := D.qhomology
  let { int_congruent, .. } := D.ra.ts.qsession
  let { SUC_SUB1, .. } := D.ra.ts.cn.ms.qsession
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, INT_REDUCE_CONV, MESON_TAC,
        REAL_ARITH_TAC, SET_RULE, SET_TAC, .. } := D.ra.ts.cn.cx.cvx
  let { SUB_ADD, .. } := D.ra.ts.cn.cx.cpx
  let { ARITH, CARD_NUMSEG_1, CART_EQ, COND_ID, DIMINDEX_GE_1, ETA_AX,
        .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_INSERT, FUN_EQ_THM, IMAGE_CLAUSES, IMP_CONJ, IMP_IMP, IN_DELETE,
        INTER_NUMSEG, INTER_UNIV, .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, IN_INTER, IN_NUMSEG, IN_SING, LAMBDA_BETA, LE_REFL,
        NOT_IN_EMPTY, NUMSEG_CLAUSES, NUMSEG_SING, .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_NEG_0, SIMPLE_IMAGE, .. } := D.ra.ts.cn.cx.cvx.core5
  let { num_INDUCTION, o_THM, .. } := D.ra.ts.cn.cx.cvx.core6
  let { BASIS_NONZERO, DIM_BASIS_IMAGE, DIM_SPAN, .. } := D.ra.ts.cn.cx.cvx.vec1
  let { IN_SPAN_IMAGE_BASIS, NORM_BASIS, .. } := D.ra.ts.cn.cx.cvx.vec2
  let { NORM_MUL, SPAN_MONO, SPAN_SING, SPAN_STDBASIS, SPAN_SUPERSET, SUBSPACE_SPAN,
        .. } := D.ra.ts.cn.cx.cvx.vec3
  let { VECTOR_MUL_LID, VECTOR_MUL_LNEG, VECTOR_NEG_COMPONENT, VECTOR_NEG_NEG,
        .. } := D.ra.ts.cn.cx.cvx.vec4
  let { CONTINUOUS_ON_SUBSET, .. } := D.ra.ts.cn.cx.cvx.top3
  let { IN_SPHERE_0, .. } := D.ra.ts.cn.cx.cvx.top4
  let { TOPSPACE_EUCLIDEAN_SUBTOPOLOGY, .. } := D.ra.ts.cn.cx.cvx.top5
  let { BROUWER_DEGREE2_EQ, .. } := D.ra.ts.cn.ms.ig.dv.dg.qhomology
  let { continuous_map, CONTINUOUS_MAP_COMPOSE, homeomorphic_maps, NSPHERE,
        TOPSPACE_SUBTOPOLOGY, .. } := D.ra.ts.cn.ms.ig.dv.dg.qmetric
  let { CONTINUOUS_MAP_EUCLIDEAN2, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { HOMEOMORPHIC_MAPS_NSPHERE_EUCLIDEAN_SPHERE,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology2
  let { INTEGER_RULE, .. } := D
  -- @@SCOPE END

  let BORSUK_ODD_MAPPING_GEN ← prove
   r"!n (f:real^N->real^N).
        f continuous_on (sphere(vec 0,&1) INTER span(IMAGE basis (1..n))) /\
        IMAGE f (sphere(vec 0,&1) INTER span(IMAGE basis (1..n))) SUBSET
        sphere(vec 0,&1) INTER span(IMAGE basis (1..n)) /\
        (!x. x IN sphere(vec 0,&1) INTER span(IMAGE basis (1..n))
             ==> f(--x) = --(f x))
        ==> (brouwer_degree1 n f == &1) (mod &2)"
   (MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC [brouwer_degree1, ARITH] THEN
      CONV_TAC (fun t => INTEGER_RULE t),
      X_GEN_TAC (← q r"n:num") THEN DISCH_TAC] THEN
    X_GEN_TAC (← q r"f:real^N->real^N") THEN
    ASM_CASES_TAC (← q r"SUC n <= dimindex(:N)") THENL
     [UNDISCH_TAC (← q r"SUC n <= dimindex(:N)") THEN REWRITE_TAC [IMP_IMP],
      ASM_REWRITE_TAC [brouwer_degree1] THEN REPEAT STRIP_TAC THEN
      CONV_TAC (fun t => INTEGER_RULE t)] THEN
    DISJ_CASES_TAC (← ARITH_RULE (← q r"n = 0 \/ 1 <= n")) THENL
     [ASM_REWRITE_TAC [ARITH, NUMSEG_SING, IMAGE_CLAUSES, SPAN_SING] THEN
      SUBGOAL_THEN
       (← q r"sphere (vec 0,&1) INTER {u % basis 1 | u IN (:real)} =
        {-- &1 % basis 1:real^N,&1 % basis 1}")
      ASSUME_TAC THENL
       [MATCH_MP_TAC (← SET_RULE
          (← q r"(!u. (u % b) IN s <=> u = c \/ u = d)
           ==> s INTER {u % b | u IN UNIV} = {c % b,d % b}")) THEN
        SIMP_TAC [IN_SPHERE_0, NORM_BASIS, LE_REFL, DIMINDEX_GE_1, NORM_MUL] THEN
        REAL_ARITH_TAC,
        ASM_REWRITE_TAC [VECTOR_MUL_LNEG, VECTOR_MUL_LID]] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"(f:real^N->real^N)(basis 1) = basis 1 \/
        (f:real^N->real^N) (basis 1) = --basis 1")
      MP_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN STRIP_TAC THEN
      MATCH_MP_TAC (← INTEGER_RULE
       (← q r"!b. (a:int == b) (mod n) /\ (b == c) (mod n) ==> (a == c) (mod n)"))
      THENL
       [EXISTS_TAC (← q r"brouwer_degree1 1 (\x:real^N. x)") THEN CONJ_TAC THENL
         [MATCH_MP_TAC (← INTEGER_RULE (← q r"a:int = b ==> (a == b) (mod n)")) THEN
          MATCH_MP_TAC BROUWER_DEGREE1_EQ THEN
          ASM_REWRITE_TAC [ARITH, NUMSEG_SING, IMAGE_CLAUSES, SPAN_SING] THEN
          REWRITE_TAC [VECTOR_MUL_LNEG, VECTOR_MUL_LID] THEN
          REWRITE_TAC [FORALL_IN_INSERT] THEN
          ASM_SIMP_TAC [IN_INSERT, NOT_IN_EMPTY],
          REWRITE_TAC [BROUWER_DEGREE1_ID] THEN CONV_TAC (fun t => INTEGER_RULE t)],
        EXISTS_TAC (← q r"brouwer_degree1 1 (reflect_along(basis 1:real^N))") THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC (← INTEGER_RULE (← q r"a:int = b ==> (a == b) (mod n)")) THEN
          MATCH_MP_TAC BROUWER_DEGREE1_EQ THEN
          ASM_REWRITE_TAC [ARITH, NUMSEG_SING, IMAGE_CLAUSES, SPAN_SING] THEN
          REWRITE_TAC [VECTOR_MUL_LNEG, VECTOR_MUL_LID] THEN
          REWRITE_TAC [FORALL_IN_INSERT] THEN
          ASM_SIMP_TAC [IN_INSERT, NOT_IN_EMPTY, VECTOR_NEG_NEG,
                        REFLECT_BASIS_ALONG_BASIS, REFLECT_ALONG_NEG,
                        LE_REFL, DIMINDEX_GE_1],
          W (MP_TAC o PART_MATCH (lhand o rand) BROUWER_DEGREE1_REFLECT_ALONG o
            lhand o rator o snd) THEN
          SIMP_TAC [DIMINDEX_GE_1, NUMSEG_SING, LE_REFL, IMAGE_CLAUSES] THEN
          SIMP_TAC [IN_DELETE, SPAN_SUPERSET, IN_SING] THEN
          SIMP_TAC [BASIS_NONZERO, LE_REFL, DIMINDEX_GE_1] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [int_congruent] THEN
          EXISTS_TAC (← q r"-- &1:int") THEN CONV_TAC INT_REDUCE_CONV]],
      STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"f:real^N->real^N",
                       ← q r"span(IMAGE basis (1..n)):real^N->bool",
                       ← q r"span(IMAGE basis (1..SUC n)):real^N->bool"]
       ODD_MAP_HOMOTOPY_LEMMA) THEN
      ASM_REWRITE_TAC [SUBSPACE_SPAN] THEN
      SUBGOAL_THEN
       (← q r"span(IMAGE basis (1..n):real^N->bool) SUBSET
        span(IMAGE basis (1..SUC n))")
      ASSUME_TAC THENL
       [MATCH_MP_TAC SPAN_MONO THEN
        REWRITE_TAC [NUMSEG_CLAUSES, ← ARITH_RULE (← q r"1 <= SUC n")] THEN SET_TAC [],
        ASM_REWRITE_TAC [DIM_BASIS_IMAGE, DIM_SPAN]] THEN
      REWRITE_TAC [INTER_NUMSEG, ← ARITH_RULE (← q r"MAX 1 1 = 1"), CARD_NUMSEG_1] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->real^N") STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"g:real^N->real^N")) THEN ANTS_TAC THENL
       [CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        ASM SET_TAC [],
        MATCH_MP_TAC (← INTEGER_RULE
         (← q r"(a:int == b) (mod n) ==> (b == c) (mod n) ==> (a == c) (mod n)"))] THEN
      MATCH_MP_TAC (← INTEGER_RULE
       (← q r"!b. (a:int == b) (mod n) /\ (b == c) (mod n)
            ==> (a == c) (mod n)")) THEN
      EXISTS_TAC (← q r"brouwer_degree1 (SUC n) (g:real^N->real^N)") THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC [BROUWER_DEGREE1_HOMOTOPIC,
                       ← INTEGER_RULE (← q r"a:int = b ==> (a == b) (mod n)")],
        ALL_TAC] THEN
      ASM_REWRITE_TAC [brouwer_degree1, ← ARITH_RULE (← q r"1 <= SUC n")] THEN
      COND_CASES_TAC THENL [ALL_TAC, ASM_ARITH_TAC] THEN
      REWRITE_TAC [SUC_SUB1] THEN
      MP_TAC (← SPEC (← q r"SUC n") HOMEOMORPHIC_MAPS_NSPHERE_EUCLIDEAN_SPHERE) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [SUC_SUB1]] THEN
      MAP_EVERY ABBREV_TAC
       [← q r"h:(num->real)->real^N =
          \x. lambda i. if 1 <= i /\ i <= SUC n then x i else &0",
        ← q r"h':real^N->num->real =
          \x i. if 1 <= i /\ i <= SUC n then x$i else &0"] THEN
      ASM_REWRITE_TAC [homeomorphic_maps] THEN STRIP_TAC THEN
      MP_TAC (← SPEC (← q r"n:num") HOMEOMORPHIC_MAPS_NSPHERE_EUCLIDEAN_SPHERE) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      MAP_EVERY ABBREV_TAC
       [← q r"k:(num->real)->real^N =
          \x. lambda i. if 1 <= i /\ i <= n then x i else &0",
        ← q r"k':real^N->num->real = \x i. if 1 <= i /\ i <= n then x$i else &0"] THEN
      ASM_REWRITE_TAC [homeomorphic_maps] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"!x. x IN topspace(nsphere(n - 1)) ==> (h:(num->real)->real^N) x = k x")
      ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["h", "k"] THEN REWRITE_TAC [NSPHERE, CART_EQ] THEN
        X_GEN_TAC (← q r"x:num->real") THEN ASM_SIMP_TAC [SUB_ADD, IN_NUMSEG] THEN
        REWRITE_TAC [TOPSPACE_SUBTOPOLOGY, IN_INTER, IN_ELIM_THM] THEN
        STRIP_TAC THEN SIMP_TAC [LAMBDA_BETA] THEN X_GEN_TAC (← q r"i:num") THEN
        ASM_CASES_TAC (← q r"i:num <= n") THEN ASM_SIMP_TAC [COND_ID] THEN
        COND_CASES_TAC THEN REWRITE_TAC [] THEN ASM_ARITH_TAC,
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!y. y IN (sphere (vec 0,&1) INTER span (IMAGE basis (1..n)))
            ==> (h':real^N->num->real) y = k' y")
      ASSUME_TAC THENL
       [X_GEN_TAC (← q r"y:real^N") THEN MAP_EVERY EXPAND_TAC ["h'", "k'"] THEN
        REWRITE_TAC [IN_INTER, IN_SPAN_IMAGE_BASIS, IN_NUMSEG] THEN
        STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:num") THEN
        ASM_CASES_TAC (← q r"1 <= i") THEN ASM_REWRITE_TAC [] THEN
        ASM_CASES_TAC (← q r"i:num <= n") THEN
        ASM_SIMP_TAC [← ARITH_RULE (← q r"i <= n ==> i <= SUC n")] THEN
        COND_CASES_TAC THEN REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_ARITH_TAC,
        ALL_TAC] THEN
      W (MP_TAC o PART_MATCH (lhand o rator o rand)
        BORSUK_ODD_MAPPING_DEGREE_STEP o lhand o rator o snd) THEN
      ANTS_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC (← INTEGER_RULE
         (← q r"b:int = c ==> (a == b) (mod n) ==> (a == c) (mod n)")) THEN
        MATCH_MP_TAC BROUWER_DEGREE2_EQ THEN ASM_SIMP_TAC [o_THM] THEN
        RULE_ASSUM_TAC (REWRITE_RULE
         [continuous_map, TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]) THEN
        ASM SET_TAC []] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC [CONTINUOUS_MAP_COMPOSE, CONTINUOUS_MAP_EUCLIDEAN2],
        X_GEN_TAC (← q r"x:num->real") THEN DISCH_TAC THEN REWRITE_TAC [o_THM] THEN
        SUBGOAL_THEN (← q r"(h:(num->real)->real^N) (\i. --x i) = --(h x)")
        SUBST1_TAC THENL
         [EXPAND_TAC "h" THEN
          SIMP_TAC [CART_EQ, LAMBDA_BETA, VECTOR_NEG_COMPONENT] THEN
          MESON_TAC [REAL_NEG_0],
          RULE_ASSUM_TAC (REWRITE_RULE
           [continuous_map, TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]) THEN
          ASM_SIMP_TAC [ETA_AX] THEN EXPAND_TAC "h'" THEN
          REWRITE_TAC [FUN_EQ_THM, VECTOR_NEG_COMPONENT] THEN
          MESON_TAC [REAL_NEG_0]],
        MATCH_MP_TAC CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE THEN
        MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
        EXISTS_TAC (← q r"(k':real^N->num->real) o g o (k:(num->real)->real^N)") THEN
        CONJ_TAC THENL
         [ASM_SIMP_TAC [o_THM] THEN
          RULE_ASSUM_TAC (REWRITE_RULE
           [continuous_map, TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]) THEN
          ASM SET_TAC [],
          REPEAT
           (MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC
            (← q r"subtopology euclidean
             (sphere(vec 0:real^N,&1) INTER span (IMAGE basis (1..n)))") THEN
           ASM_REWRITE_TAC []) THEN
          ASM_REWRITE_TAC [CONTINUOUS_MAP_EUCLIDEAN2] THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
          ASM SET_TAC []]]])

  let BORSUK_ODD_MAPPING ← prove
   r"!f:real^N->real^N.
        f continuous_on sphere(vec 0,&1) /\
        IMAGE f (sphere(vec 0,&1)) SUBSET sphere(vec 0,&1) /\
        (!x. x IN sphere(vec 0,&1) ==> f(--x) = --(f x))
        ==> (brouwer_degree f == &1) (mod &2)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [brouwer_degree] THEN
    MATCH_MP_TAC BORSUK_ODD_MAPPING_GEN THEN
    REWRITE_TAC [← GSYM SIMPLE_IMAGE, IN_NUMSEG, SPAN_STDBASIS, INTER_UNIV] THEN
    ASM_REWRITE_TAC [LE_REFL, SIMPLE_IMAGE])

  pure { BORSUK_ODD_MAPPING_GEN, BORSUK_ODD_MAPPING }
/- ------------------------------------------------------------------------- -/
/- Various forms and corollaries of the Borsuk-Ulam theorem.                 -/
/- (moretop.ml 1522-1979)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MOF where
  BORSUK_ULAM_NOT_NULLHOMOTOPIC_GEN : thm
  BORSUK_ULAM_NOT_NULLHOMOTOPIC : thm
  BORSUK_ULAM_SURJECTIVE_GEN : thm
  BORSUK_ULAM_SURJECTIVE : thm
  BORSUK_ULAM_ZERO_GEN : thm
  BORSUK_ULAM_ZERO : thm
  BORSUK_ULAM_ANTIPODAL_SUBSPACE : thm
  BORSUK_ULAM_ANTIPODAL_GEN : thm
  BORSUK_ULAM_ANTIPODAL : thm
  BORSUK_ULAM_FRONTIER_MAP_GEN : thm
  BORSUK_ULAM_FRONTIER_MAP : thm
  LUSTERNIK_SCHNIRELMANN : thm
  HAM_SANDWICH_THEOREM : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOF [HolBase] (D : MoreTopDeps) (BMOE : MOE) : ExceptT String IO MOF := do
  -- @@SCOPE BEGIN
  let { BORSUK_ODD_MAPPING_GEN, .. } := BMOE
  let { SETDIST_EQ_0_CLOSED, .. } := D.qtopology
  let { NULLHOMOTOPIC_NONSURJECTIVE_SPHERE_MAP_GEN, NULLHOMOTOPIC_THROUGH_CONTRACTIBLE,
        RELATIVE_FRONTIER_CBALL_INTER_AFFINE, .. } := D.qpaths
  let { AFF_DIM_TRANSLATION_EQ, SUBSPACE_EQ_AFFINE, .. } := D.qconvex
  let { FSTCART_NEG, ISOMETRY_SUBSET_SUBSPACE, SNDCART_NEG, .. } := D.qvectors
  let { CONTINUOUS_ON_MEASURE_IN_PORTION, MEASURABLE_MEASURABLE_INTER_LEBESGUE_MEASURABLE,
        NEGLIGIBLE_HYPERPLANE, .. } := D.qmeasure
  let { BROUWER_DEGREE1_CONST, BROUWER_DEGREE1_HOMOTOPIC, .. } := D.qdegree
  let { divides, IN_GSPEC, INT_MAX_LE, MULT_EQ_1, num_divides, .. } := D.qsession
  let { CARD_LE_CARD, LE_C_IMAGE, .. } := D.qcard
  let { MEASURE_NEGLIGIBLE_UNION_EQ, .. } := D.ra.qmeasure
  let { LEBESGUE_MEASURABLE_CONVEX, .. } := D.ra.ts.qmeasure
  let { NEGLIGIBLE_INTER, .. } := D.ra.ts.cn.ms.qintegration3
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_INT_ARITH_TAC, ASM_MESON_TAC, INT_ARITH,
        MESON, MESON_TAC, NORM_ARITH, NUM_REDUCE_CONV, REAL_ARITH, REAL_RAT_REDUCE_CONV,
        SET_RULE, SET_TAC, VECTOR_ARITH, .. } := D.ra.ts.cn.cx.cvx
  let { ARITH_EQ, CARD_NUMSEG_1, CART_EQ, CONJ_ASSOC, DIMINDEX_1, DIMINDEX_FINITE_SUM,
        DIMINDEX_GE_1, EQ_SYM_EQ, ETA_AX, EXISTS_IN_IMAGE, EXISTS_PASTECART, EXTENSION,
        FINITE_NUMSEG, .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_PASTECART, FSTCART_PASTECART, IMAGE_EQ_EMPTY, IMAGE_ID,
        IMAGE_o, IMAGE_SUBSET, IMP_CONJ, INT_OF_NUM_ADD, INT_OF_NUM_EQ, INT_OF_NUM_LE,
        INT_OF_NUM_LT, INTER_NUMSEG, INTER_SUBSET, INTER_UNIV,
        .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, IN_INTER, IN_NUMSEG, IN_SING, LAMBDA_BETA, LE_REFL,
        LEFT_IMP_EXISTS_THM, LT_REFL, MEMBER_NOT_EMPTY, MONO_EXISTS, NOT_EXISTS_THM,
        NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, PSUBSET, REAL_ABS_INV,
        .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_LE_NEG2, .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_LINV, REAL_MUL_RINV, REAL_NEG_SUB, REAL_OF_NUM_EQ, REAL_SUB_0,
        RIGHT_AND_EXISTS_THM, RIGHT_EXISTS_AND_THM, SNDCART_PASTECART, SUBSET,
        SUBSET_EMPTY, SUBSET_TRANS, .. } := D.ra.ts.cn.cx.cvx.core5
  let { o_DEF, o_THM, real_ge, SUBSET_UNIV, SWAP_EXISTS_THM, UNIONS_0, UNIONS_IMAGE,
        .. } := D.ra.ts.cn.cx.cvx.core6
  let { HULL_INC, .. } := D.ra.ts.cn.cx.cvx.misc
  let { DIM_BASIS_IMAGE, DIM_LINEAR_IMAGE_LE, DIM_SPAN, DIM_SUBSET_UNIV, DIM_UNIV,
        DOT_LNEG, .. } := D.ra.ts.cn.cx.cvx.vec1
  let { EXISTS_LIFT, FORALL_LIFT, IN_SPAN_IMAGE_BASIS, ISOMETRIES_SUBSPACES, LIFT_DROP,
        LIFT_EQ, LIFT_NUM, LIFT_SUB, LINEAR_0, LINEAR_CMUL, LINEAR_FSTCART, LINEAR_SNDCART,
        NORM_0, NORM_EQ_0, .. } := D.ra.ts.cn.cx.cvx.vec2
  let { NORM_MUL, NORM_NEG, PASTECART_VEC, REAL_ABS_NORM, SPAN_INC, SPAN_SUB,
        SPAN_SUPERSET, SUBSPACE_0, SUBSPACE_MUL, SUBSPACE_NEG, SUBSPACE_SPAN,
        SUBSPACE_UNIV, .. } := D.ra.ts.cn.cx.cvx.vec3
  let { VEC_COMPONENT, VECTOR_MUL_ASSOC, VECTOR_MUL_LID, VECTOR_MUL_RNEG,
        VECTOR_NEG_COMPONENT, VECTOR_NEG_NEG, VECTOR_SUB_EQ, .. } := D.ra.ts.cn.cx.cvx.vec4
  let { BOUNDED_CBALL, .. } := D.ra.ts.cn.cx.cvx.top1
  let { CONTINUOUS_ON_ADD, CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID,
        CONTINUOUS_ON_INV, CONTINUOUS_ON_LIFT_NORM, CONTINUOUS_ON_MUL, CONTINUOUS_ON_SUB,
        CONTINUOUS_ON_SUBSET, .. } := D.ra.ts.cn.cx.cvx.top3
  let { IN_SPHERE_0, LINEAR_CONTINUOUS_ON, .. } := D.ra.ts.cn.cx.cvx.top4
  let { IN_TRANSLATION_GALOIS, LINEAR_NEG, .. } := D.ra.ts.cn.ms.ig.dv.qvec
  let { AFF_DIM_DIM_SUBSPACE, SUBSPACE_IMP_CONVEX, .. } := D.ra.ts.cn.ms.ig.dv.dg.qconvex
  let { HOMOTOPIC_COMPOSE_CONTINUOUS_MAP_LEFT, HOMOTOPIC_COMPOSE_CONTINUOUS_MAP_RIGHT,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qmetric
  let { CONVEX_IMP_CONTRACTIBLE, .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths1
  let { CONTINUOUS_MAP_EUCLIDEAN2, CONTINUOUS_ON_COMPONENTWISE_LIFT,
        CONTINUOUS_ON_LIFT_DOT2, CONTINUOUS_ON_LIFT_SETDIST,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { SPHERE_EQ_EMPTY, SPHERE_SUBSET_CBALL, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology2
  let { PASTECART_EQ, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qses
  let { DIM_EQ_0, DROP_NEG, LINEAR_NEGATION, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qvec
  let { BOUNDED_INTER, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qtop
  let { AFF_DIM_DIM_0, AFF_DIM_EMPTY, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx1
  let { CONVEX_CBALL, CONVEX_HALFSPACE_GE, CONVEX_HALFSPACE_LE, CONVEX_INTER,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  let { INTEGER_RULE, .. } := D
  -- @@SCOPE END

  let BORSUK_ULAM_NOT_NULLHOMOTOPIC_GEN ← prove
   r"!(f:real^N->real^N) s a.
        subspace s /\ 1 <= dim s /\
        f continuous_on (sphere(vec 0,&1) INTER s) /\
        IMAGE f (sphere(vec 0,&1) INTER s) SUBSET sphere(vec 0,&1) INTER s /\
        (!x. x IN sphere(vec 0,&1) INTER s ==> f(--x) = --(f x))
        ==> ~(homotopic_with (\x. T)
               (subtopology euclidean (sphere(vec 0,&1) INTER s),
                subtopology euclidean (sphere(vec 0,&1) INTER s))
               f (\x. a))"
   (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL
      [← q r"s:real^N->bool",
       ← q r"span(IMAGE basis (1..dim(s:real^N->bool))):real^N->bool"]
      ISOMETRIES_SUBSPACES) THEN
    ASM_REWRITE_TAC [SUBSPACE_SPAN, DIM_SPAN, DIM_BASIS_IMAGE] THEN
    REWRITE_TAC [INTER_NUMSEG, CARD_NUMSEG_1, ← ARITH_RULE (← q r"MAX 1 1 = 1")] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"s = MIN d s <=> s <= d"), DIM_SUBSET_UNIV] THEN
    REWRITE_TAC [NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"h:real^N->real^N", ← q r"k:real^N->real^N"] THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL
     [← q r"dim(s:real^N->bool)",
      ← q r"(h:real^N->real^N) o (f:real^N->real^N) o (k:real^N->real^N)"]
     BORSUK_ODD_MAPPING_GEN) THEN
    REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP (← SET_RULE
     (← q r"IMAGE f s = t ==> !x. x IN s ==> f x IN t")))) THEN
    REWRITE_TAC [NOT_IMP, DIM_SUBSET_UNIV] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC [INTER_SUBSET] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC [LINEAR_CONTINUOUS_ON] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC [LINEAR_CONTINUOUS_ON] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
      ASM_SIMP_TAC [SUBSET, FORALL_IN_IMAGE, IN_INTER, IN_SPHERE_0],
      UNDISCH_TAC
       (← q r"IMAGE (f:real^N->real^N) (sphere(vec 0,&1) INTER s) SUBSET
       sphere(vec 0,&1) INTER s") THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_INTER, o_THM, IN_SPHERE_0] THEN
      ASM_SIMP_TAC [],
      UNDISCH_TAC
       (← q r"IMAGE (f:real^N->real^N) (sphere(vec 0,&1) INTER s) SUBSET
       sphere(vec 0,&1) INTER s") THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_INTER, o_THM, IN_SPHERE_0] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [IN_INTER, IN_SPHERE_0]) THEN
      ASM_SIMP_TAC [LINEAR_NEG],
      FIRST_ASSUM (MP_TAC o ISPECL
       [← q r"k:real^N->real^N",
        ← q r"subtopology euclidean
          (sphere(vec 0,&1) INTER
          span(IMAGE basis (1..dim(s:real^N->bool))):real^N->bool)"] o
        MATCH_MP
       (← REWRITE_RULE [IMP_CONJ] HOMOTOPIC_COMPOSE_CONTINUOUS_MAP_RIGHT)) THEN
      REWRITE_TAC [CONTINUOUS_MAP_EUCLIDEAN2] THEN
      RULE_ASSUM_TAC (REWRITE_RULE
       [SUBSET, FORALL_IN_IMAGE, IN_INTER, IN_SPHERE_0]) THEN
      ASM_SIMP_TAC [SUBSET, FORALL_IN_IMAGE, IN_INTER, IN_SPHERE_0] THEN
      ASM_SIMP_TAC [LINEAR_CONTINUOUS_ON] THEN
      DISCH_THEN (MP_TAC o ISPECL
       [← q r"h:real^N->real^N",
        ← q r"subtopology euclidean
          (sphere(vec 0,&1) INTER
          span(IMAGE basis (1..dim(s:real^N->bool))):real^N->bool)"] o
      MATCH_MP (← REWRITE_RULE [IMP_CONJ]
        HOMOTOPIC_COMPOSE_CONTINUOUS_MAP_LEFT)) THEN
      REWRITE_TAC [CONTINUOUS_MAP_EUCLIDEAN2] THEN
      ASM_SIMP_TAC [SUBSET, FORALL_IN_IMAGE, IN_INTER, IN_SPHERE_0] THEN
      ASM_SIMP_TAC [LINEAR_CONTINUOUS_ON] THEN
      DISCH_THEN (SUBST1_TAC o MATCH_MP BROUWER_DEGREE1_HOMOTOPIC) THEN
      ASM_SIMP_TAC [o_DEF, BROUWER_DEGREE1_CONST, DIM_SUBSET_UNIV] THEN
      REWRITE_TAC [← INTEGER_RULE (← q r"(&0 == x) (mod n) <=> n divides x")] THEN
      REWRITE_TAC [← GSYM num_divides, divides] THEN
      ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN REWRITE_TAC [MULT_EQ_1] THEN
      CONV_TAC NUM_REDUCE_CONV])

  let BORSUK_ULAM_NOT_NULLHOMOTOPIC ← prove
   r"!(f:real^N->real^N) a.
        f continuous_on sphere(vec 0,&1) /\
        IMAGE f (sphere(vec 0,&1)) SUBSET sphere(vec 0,&1) /\
        (!x. x IN sphere(vec 0,&1) ==> f(--x) = --(f x))
        ==> ~(homotopic_with (\x. T)
                (subtopology euclidean (sphere(vec 0,&1)),
                 subtopology euclidean (sphere(vec 0,&1)))
                f (\x. a))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^N->real^N", ← q r"(:real^N)", ← q r"a:real^N"]
          BORSUK_ULAM_NOT_NULLHOMOTOPIC_GEN) THEN
    ASM_REWRITE_TAC [INTER_UNIV, SUBSPACE_UNIV, DIM_UNIV, DIMINDEX_GE_1])

  let BORSUK_ULAM_SURJECTIVE_GEN ← prove
   r"!(f:real^N->real^N) s.
        subspace s /\
        f continuous_on (sphere(vec 0,&1) INTER s) /\
        IMAGE f (sphere(vec 0,&1) INTER s) SUBSET sphere(vec 0,&1) INTER s /\
        (!x. x IN sphere(vec 0,&1) INTER s ==> f(--x) = --(f x))
        ==> IMAGE f (sphere(vec 0,&1) INTER s) = sphere(vec 0,&1) INTER s"
   (REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC (← ARITH_RULE (← q r"dim(s:real^N->bool) = 0 \/ 1 <= dim s")) THENL
     [MATCH_MP_TAC (← SET_RULE
       (← q r"s SUBSET (UNIV DIFF p) ==> IMAGE f (p INTER s) = p INTER s")) THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [DIM_EQ_0]) THEN
      MATCH_MP_TAC (← SET_RULE
       (← q r"~(a IN t) ==> s SUBSET {a} ==> s SUBSET UNIV DIFF t")) THEN
      REWRITE_TAC [IN_SPHERE_0, NORM_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV,
      MATCH_MP_TAC (← TAUT (← q r"(~p ==> F) ==> p")) THEN DISCH_TAC THEN
      MP_TAC (← ISPECL [← q r"f:real^N->real^N", ← q r"s:real^N->bool"]
       BORSUK_ULAM_NOT_NULLHOMOTOPIC_GEN) THEN
      ASM_REWRITE_TAC [NOT_FORALL_THM] THEN
      MP_TAC (← ISPECL [← q r"f:real^N->real^N", ← q r"cball(vec 0:real^N,&1) INTER s"]
            NULLHOMOTOPIC_NONSURJECTIVE_SPHERE_MAP_GEN) THEN
      ASM_SIMP_TAC [RELATIVE_FRONTIER_CBALL_INTER_AFFINE, REAL_OF_NUM_EQ, ARITH_EQ,
                    ← GSYM SUBSPACE_EQ_AFFINE] THEN
      DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC [BOUNDED_INTER, BOUNDED_CBALL] THEN
      ASM_SIMP_TAC [CONVEX_INTER, CONVEX_CBALL, SUBSPACE_IMP_CONVEX] THEN
      ASM SET_TAC []])

  let BORSUK_ULAM_SURJECTIVE ← prove
   r"!(f:real^N->real^N).
        f continuous_on sphere(vec 0,&1) /\
        IMAGE f (sphere(vec 0,&1)) SUBSET sphere(vec 0,&1) /\
        (!x. x IN sphere(vec 0,&1) ==> f(--x) = --(f x))
        ==> IMAGE f (sphere(vec 0,&1)) = sphere(vec 0,&1)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^N->real^N", ← q r"(:real^N)"]
          BORSUK_ULAM_SURJECTIVE_GEN) THEN
    ASM_REWRITE_TAC [INTER_UNIV, SUBSPACE_UNIV, DIM_UNIV, DIMINDEX_GE_1])

  let BORSUK_ULAM_ZERO_GEN ← prove
   r"!(f:real^M->real^N) s t.
        subspace s /\ dim t + 1 <= dim s /\
        f continuous_on (sphere(vec 0,&1) INTER s) /\
        IMAGE f (sphere(vec 0,&1) INTER s) SUBSET t /\
        (!x. x IN (sphere(vec 0,&1) INTER s) ==> f(--x) = --(f x))
        ==> ?x. x IN (sphere(vec 0,&1) INTER s) /\ f x = vec 0"
   (GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC (← MESON [SUBSPACE_SPAN]
     (← q r"(!s. P(span s) ==> P s) /\ (!s. subspace s ==> P s) ==> (!s. P s)")) THEN
    CONJ_TAC THENL
     [REWRITE_TAC [DIM_SPAN] THEN MESON_TAC [SPAN_INC, SUBSET_TRANS],
      REPEAT STRIP_TAC] THEN
    ONCE_REWRITE_TAC [← MESON []
     (← q r"(?x. P x /\ Q x) <=> ((!x. P x ==> ~(Q x)) ==> F)")] THEN
    DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"t:real^N->bool", ← q r"s:real^M->bool"]
          ISOMETRY_SUBSET_SUBSPACE) THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"t + 1 <= s ==> t <= s")] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->real^M") STRIP_ASSUME_TAC) THEN
    RULE_ASSUM_TAC (REWRITE_RULE
     [SUBSET, FORALL_IN_IMAGE, IN_INTER, IN_SPHERE_0]) THEN
    MP_TAC (← ISPECL
     [← q r"(g:real^N->real^M) o (\x. inv(norm x) % x) o (f:real^M->real^N)",
      ← q r"s:real^M->bool"] BORSUK_ULAM_SURJECTIVE_GEN) THEN
    ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, o_THM, IN_INTER, IN_SPHERE_0] THEN
    ASM_SIMP_TAC [NOT_IMP, NORM_NEG, VECTOR_MUL_RNEG, LINEAR_NEG] THEN
    ASM_SIMP_TAC [← GSYM CONJ_ASSOC, SUBSPACE_MUL] THEN
    REWRITE_TAC [NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
    ASM_SIMP_TAC [REAL_MUL_LINV, NORM_EQ_0] THEN CONJ_TAC THENL
     [REPEAT (MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC) THEN
      ASM_SIMP_TAC [LINEAR_CONTINUOUS_ON] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC [CONTINUOUS_ON_ID] THEN
      REWRITE_TAC [o_DEF] THEN
      MATCH_MP_TAC (← REWRITE_RULE [o_DEF] CONTINUOUS_ON_INV) THEN
      ASM_SIMP_TAC [FORALL_IN_IMAGE, IN_INTER, IN_SPHERE_0, NORM_EQ_0] THEN
      REWRITE_TAC [← REWRITE_RULE [o_DEF] CONTINUOUS_ON_LIFT_NORM],
      SUBGOAL_THEN (← q r"IMAGE (g:real^N->real^M) t PSUBSET s") MP_TAC THENL
       [ASM_REWRITE_TAC [PSUBSET, SUBSET, FORALL_IN_IMAGE] THEN
        MATCH_MP_TAC (← MESON [LT_REFL] (← q r"dim t < dim s ==> ~(t = s)")) THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← ARITH_RULE
          (← q r"t + 1 <= s ==> t' <= t ==> t' < s"))) THEN
        ASM_MESON_TAC [DIM_LINEAR_IMAGE_LE],
        DISCH_THEN (X_CHOOSE_THEN (← q r"a:real^M") STRIP_ASSUME_TAC o MATCH_MP (← SET_RULE
         (← q r"IMAGE g t PSUBSET s ==> ?a. a IN s /\ !x. x IN t ==> ~(g x = a)"))) THEN
        SUBGOAL_THEN (← q r"~(a:real^M = vec 0)") ASSUME_TAC THENL
         [ASM_MESON_TAC [SUBSPACE_0, LINEAR_0], ALL_TAC] THEN
        GEN_REWRITE_TAC RAND_CONV [EXTENSION] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"inv(norm a) % a:real^M")) THEN
        REWRITE_TAC [IN_IMAGE, IN_INTER, IN_SPHERE_0, NORM_MUL] THEN
        ASM_SIMP_TAC [REAL_ABS_INV, REAL_ABS_NORM, REAL_MUL_LINV, NORM_EQ_0] THEN
        ASM_SIMP_TAC [SUBSPACE_MUL, NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"x:real^M") THEN
        DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
        DISCH_THEN (MP_TAC o AP_TERM (← q r"(%) (norm(a:real^M)) :real^M->real^M")) THEN
        ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_RINV, NORM_EQ_0] THEN
        ASM_SIMP_TAC [← GSYM LINEAR_CMUL, o_THM, VECTOR_MUL_LID] THEN
        CONV_TAC (RAND_CONV SYM_CONV) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC [SUBSPACE_MUL]]])

  let BORSUK_ULAM_ZERO ← prove
   r"!(f:real^M->real^N) s.
        dim s < dimindex(:M) /\
        f continuous_on sphere(vec 0,&1) /\
        IMAGE f (sphere(vec 0,&1)) SUBSET s /\
        (!x. x IN sphere(vec 0,&1) ==> f(--x) = --(f x))
        ==> ?x. x IN sphere(vec 0,&1) /\ f x = vec 0"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^M->real^N", ← q r"(:real^M)", ← q r"s:real^N->bool"]
          BORSUK_ULAM_ZERO_GEN) THEN
    ASM_REWRITE_TAC [INTER_UNIV, SUBSPACE_UNIV, DIM_UNIV] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC)

  let BORSUK_ULAM_ANTIPODAL_SUBSPACE ← prove
   r"!(f:real^M->real^N) s t.
        subspace s /\ dim t + 1 <= dim s /\
        f continuous_on (sphere(vec 0,&1) INTER s) /\
        IMAGE f (sphere(vec 0,&1) INTER s) SUBSET t
        ==> ?x. x IN (sphere(vec 0,&1) INTER s) /\ f(--x) = f(x)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM VECTOR_SUB_EQ] THEN
    MATCH_MP_TAC BORSUK_ULAM_ZERO_GEN THEN
    EXISTS_TAC (← q r"span t:real^N->bool") THEN
    ASM_REWRITE_TAC [DIM_SPAN, VECTOR_NEG_NEG] THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"--(x - y):real^N = y - x")] THEN
    RULE_ASSUM_TAC (REWRITE_RULE
     [SUBSET, FORALL_IN_IMAGE, IN_INTER, IN_SPHERE_0]) THEN
    SIMP_TAC [SUBSET, FORALL_IN_IMAGE, IN_INTER, IN_SPHERE_0] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC [ETA_AX] THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC [LINEAR_NEGATION, LINEAR_CONTINUOUS_ON] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_INTER, IN_SPHERE_0] THEN
      ASM_SIMP_TAC [SUBSPACE_NEG, NORM_NEG],
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_SUB THEN ASM_SIMP_TAC [] THEN
      CONJ_TAC THEN MATCH_MP_TAC SPAN_SUPERSET THEN
      ASM_SIMP_TAC [NORM_NEG, SUBSPACE_NEG]])

  let BORSUK_ULAM_ANTIPODAL_GEN ← prove
   r"!(f:real^M->real^N) s t.
        subspace s /\ max (&1) (aff_dim t + &1) <= &(dim s) /\
        f continuous_on (sphere(vec 0,&1) INTER s) /\
        IMAGE f (sphere(vec 0,&1) INTER s) SUBSET t
        ==> ?x. x IN (sphere(vec 0,&1) INTER s) /\ f(--x) = f(x)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"t:real^N->bool = {}") THENL
     [ASM_REWRITE_TAC [AFF_DIM_EMPTY, SUBSET_EMPTY, IMAGE_EQ_EMPTY] THEN
      MATCH_MP_TAC (← SET_RULE
       (← q r"(P ==> Q ==> ?a. a IN s) ==> P /\ Q /\ R /\ s = {} ==> Z")) THEN
      DISCH_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP (← INT_ARITH
       (← q r"max (&1:int) a <= s ==> ~(s = &0)"))) THEN
      REWRITE_TAC [INT_OF_NUM_EQ, DIM_EQ_0, SUBSET, NOT_FORALL_THM] THEN
      REWRITE_TAC [NOT_IMP, IN_SING, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"a:real^M") THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"inv(norm a) % a:real^M") THEN
      ASM_SIMP_TAC [IN_INTER, IN_SPHERE_0, SUBSPACE_MUL] THEN
      REWRITE_TAC [NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
      ASM_SIMP_TAC [REAL_MUL_LINV, NORM_EQ_0],
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [← GSYM MEMBER_NOT_EMPTY]) THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"a:real^N") THEN
      REPEAT STRIP_TAC THEN
      MP_TAC (← ISPECL
       [← q r"(\x. --a + x) o (f:real^M->real^N)",
        ← q r"s:real^M->bool", ← q r"IMAGE (\x:real^N. --a + x) t"]
          BORSUK_ULAM_ANTIPODAL_SUBSPACE) THEN
      ASM_SIMP_TAC [IMAGE_o, IMAGE_SUBSET, o_THM] THEN
      REWRITE_TAC [← VECTOR_ARITH (← q r"--a + x:real^N = --a + y <=> x = y")] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC [CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_ADD, CONTINUOUS_ON_ID,
        CONTINUOUS_ON_CONST, ← GSYM INT_OF_NUM_ADD, ← GSYM INT_OF_NUM_LE] THEN
      SUBGOAL_THEN (← q r"vec 0 IN IMAGE (\x:real^N. --a + x) t") ASSUME_TAC THENL
       [ASM_REWRITE_TAC [IN_TRANSLATION_GALOIS] THEN
        ASM_REWRITE_TAC [← VECTOR_ARITH (← q r"vec 0 - --a:real^N = a")],
        ASM_SIMP_TAC [← GSYM AFF_DIM_DIM_0, AFF_DIM_TRANSLATION_EQ, HULL_INC] THEN
                     ASM_INT_ARITH_TAC]])

  let BORSUK_ULAM_ANTIPODAL ← prove
   r"!(f:real^M->real^N) s.
        aff_dim s < &(dimindex(:M)) /\
        f continuous_on sphere(vec 0,&1) /\
        IMAGE f (sphere(vec 0,&1)) SUBSET s
        ==> ?x. x IN sphere(vec 0,&1) /\ f(--x) = f(x)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^M->real^N", ← q r"(:real^M)", ← q r"s:real^N->bool"]
          BORSUK_ULAM_ANTIPODAL_GEN) THEN
    ASM_REWRITE_TAC [INTER_UNIV, SUBSPACE_UNIV, DIM_UNIV] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [INT_MAX_LE, INT_OF_NUM_LE, DIMINDEX_GE_1] THEN
    ASM_INT_ARITH_TAC)

  let BORSUK_ULAM_FRONTIER_MAP_GEN ← prove
   r"!f s:real^N->bool.
      ~(subspace s /\ 1 <= dim s /\
        f continuous_on (cball(vec 0,&1) INTER s) /\
        IMAGE f (cball(vec 0,&1) INTER s) SUBSET sphere(vec 0,&1) INTER s /\
        !x. x IN (sphere(vec 0,&1) INTER s) ==> f(--x) = --(f x))"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"sphere(vec 0:real^N,&1) INTER s SUBSET cball(vec 0,&1) INTER s")
    ASSUME_TAC THENL
     [MATCH_MP_TAC (← SET_RULE (← q r"s SUBSET t ==> s INTER u SUBSET t INTER u")) THEN
      REWRITE_TAC [SPHERE_SUBSET_CBALL],
      ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"\x:real^N. x", ← q r"f:real^N->real^N",
      ← q r"sphere(vec 0:real^N,&1) INTER s",
      ← q r"cball(vec 0:real^N,&1) INTER s",
      ← q r"sphere(vec 0:real^N,&1) INTER s"]
     NULLHOMOTOPIC_THROUGH_CONTRACTIBLE) THEN
    ASM_REWRITE_TAC [CONTINUOUS_ON_ID, IMAGE_ID] THEN
    ASM_SIMP_TAC [CONVEX_IMP_CONTRACTIBLE, CONVEX_INTER, CONVEX_CBALL,
                  SUBSPACE_IMP_CONVEX] THEN
    REWRITE_TAC [o_DEF, NOT_EXISTS_THM, o_DEF, ETA_AX] THEN
    GEN_TAC THEN MATCH_MP_TAC BORSUK_ULAM_NOT_NULLHOMOTOPIC_GEN THEN
    ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [CONTINUOUS_ON_SUBSET, IMAGE_SUBSET, SUBSET_TRANS])

  let BORSUK_ULAM_FRONTIER_MAP ← prove
   r"!f:real^N->real^N.
      ~(f continuous_on cball(vec 0,&1) /\
        IMAGE f (cball(vec 0,&1)) SUBSET sphere(vec 0,&1) /\
        !x. x IN sphere(vec 0,&1) ==> f(--x) = --(f x))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^N->real^N", ← q r"(:real^N)"]
          BORSUK_ULAM_FRONTIER_MAP_GEN) THEN
    ASM_REWRITE_TAC [INTER_UNIV, SUBSPACE_UNIV, DIM_UNIV, DIMINDEX_GE_1])

  let LUSTERNIK_SCHNIRELMANN ← prove
   r"!u:(real^N->bool)->bool.
        FINITE u /\ CARD(u) <= dimindex(:N) /\ (!c. c IN u ==> closed c) /\
        sphere(vec 0,&1) SUBSET UNIONS u
        ==> ?c x. c IN u /\ x IN sphere(vec 0,&1) /\ x IN c /\ --x IN c"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"u:(real^N->bool)->bool = {}") THEN
    ASM_REWRITE_TAC [UNIONS_0, SUBSET_EMPTY, SPHERE_EQ_EMPTY] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"u:(real^N->bool)->bool", ← q r"1..dimindex(:N)"]
          LE_C_IMAGE) THEN
    ASM_SIMP_TAC [CARD_LE_CARD, FINITE_NUMSEG, CARD_NUMSEG_1] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->real^N->bool") (SUBST_ALL_TAC o SYM)) THEN
    RULE_ASSUM_TAC (REWRITE_RULE
     [FORALL_IN_IMAGE, IN_NUMSEG, UNIONS_IMAGE, SUBSET, IN_ELIM_THM]) THEN
    REWRITE_TAC [RIGHT_EXISTS_AND_THM, EXISTS_IN_IMAGE, IN_NUMSEG] THEN
    MP_TAC (← ISPECL
     [← q r"(\x. lambda i. if i <= dimindex(:N)-1 then setdist({x},c i) else &0)
       :real^N->real^N",
      ← q r"span(IMAGE basis (1..dimindex(:N)-1)):real^N->bool"]
     BORSUK_ULAM_ANTIPODAL) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [SIMP_TAC [AFF_DIM_DIM_SUBSPACE, INT_OF_NUM_LT, SUBSPACE_SPAN] THEN
        REWRITE_TAC [DIM_BASIS_IMAGE, DIM_SPAN, CARD_NUMSEG_1, INTER_NUMSEG,
                     ← ARITH_RULE (← q r"MAX 1 1 = 1 /\ MIN n (n - 1) = n - 1")] THEN
        REWRITE_TAC [← ARITH_RULE (← q r"n - 1 < n <=> 1 <= n"), DIMINDEX_GE_1],
        ONCE_REWRITE_TAC [CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
        SIMP_TAC [LAMBDA_BETA] THEN X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
        ASM_CASES_TAC (← q r"i <= dimindex(:N) - 1") THEN
        ASM_REWRITE_TAC [CONTINUOUS_ON_CONST, CONTINUOUS_ON_LIFT_SETDIST],
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_SPAN_IMAGE_BASIS] THEN
        SIMP_TAC [LAMBDA_BETA, IN_NUMSEG] THEN MESON_TAC []],
      REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN
      GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"x:real^N") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [CART_EQ]) THEN
      SIMP_TAC [LAMBDA_BETA] THEN DISCH_THEN (MP_TAC o MATCH_MP (← SET_RULE
       (← q r"(!i. P i /\ Q i ==> (if R i then f i else z) = (if R i then g i else z))
        ==> (!i. R i ==> Q i)
            ==> (!i. P i /\ R i ==> (f i = &0 <=> g i = &0))"))) THEN
      ASM_SIMP_TAC [SETDIST_EQ_0_CLOSED] THEN
      ANTS_TAC THENL [ARITH_TAC, ALL_TAC] THEN
      ASM_CASES_TAC (← q r"?i. 1 <= i /\ i <= dimindex(:N) - 1 /\ (x:real^N) IN c i")
      THENL
       [FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"k:num") STRIP_ASSUME_TAC) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"k:num")) THEN ASM_REWRITE_TAC [] THEN
        STRIP_TAC THENL [ASM SET_TAC [], EXISTS_TAC (← q r"k:num")] THEN
        ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
        RULE_ASSUM_TAC (REWRITE_RULE
         [NOT_EXISTS_THM, ← TAUT (← q r"~(p /\ q /\ r) <=> p /\ q ==> ~r")]) THEN
        ASM_SIMP_TAC [← SET_RULE (← q r"(s = {} \/ a IN s <=> s = {}) <=> ~(a IN s)")] THEN
        DISCH_TAC THEN EXISTS_TAC (← q r"dimindex(:N)") THEN
        REWRITE_TAC [LE_REFL, DIMINDEX_GE_1] THEN CONJ_TAC THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
         (← q r"(!x. P x ==> ?n. A n /\ x IN c n)
          ==> P x /\ (!n. A n /\ ~(n = m) ==> ~(x IN c n))
              ==> x IN c m"))) THEN
        ASM_REWRITE_TAC [← ARITH_RULE
         (← q r"(1 <= m /\ m <= n) /\ ~(m = n) <=> 1 <= m /\ m <= n - 1")] THEN
        ASM_MESON_TAC [IN_SPHERE_0, NORM_NEG]]])

  let HAM_SANDWICH_THEOREM ← prove
   r"!u:(real^N->bool)->bool.
      FINITE u /\ CARD(u) <= dimindex(:N) /\ (!s. s IN u ==> measurable s)
      ==> ?a b. !s. s IN u
                    ==> measure {x | x IN s /\ a dot x <= b} = measure s / &2"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"u:(real^N->bool)->bool = {}") THEN
    ASM_REWRITE_TAC [NOT_IN_EMPTY] THEN
    MP_TAC (← ISPECL [← q r"u:(real^N->bool)->bool", ← q r"1..dimindex(:N)"]
          LE_C_IMAGE) THEN
    ASM_SIMP_TAC [CARD_LE_CARD, FINITE_NUMSEG, CARD_NUMSEG_1] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"s:num->real^N->bool") (SUBST_ALL_TAC o SYM)) THEN
    RULE_ASSUM_TAC (REWRITE_RULE
     [FORALL_IN_IMAGE, IN_NUMSEG, UNIONS_IMAGE, SUBSET, IN_ELIM_THM]) THEN
    REWRITE_TAC [FORALL_IN_IMAGE, IN_NUMSEG] THEN
    MP_TAC (← ISPECL
     [← q r"(\z. lambda i.
          measure {x:real^N | x IN s i /\ fstcart z dot x >= drop(sndcart z)} -
          measure {x:real^N | x IN s i /\ fstcart z dot x <= drop(sndcart z)}):
       real^(N,1)finite_sum->real^N",
      ← q r"(:real^N)"] BORSUK_ULAM_ZERO) THEN
    REWRITE_TAC [SUBSET_UNIV, DIM_UNIV, DIMINDEX_FINITE_SUM, DIMINDEX_1] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"n < n + 1")] THEN ANTS_TAC THENL
     [SIMP_TAC [CART_EQ, VECTOR_NEG_COMPONENT, LAMBDA_BETA] THEN
      REWRITE_TAC [← GSYM FSTCART_NEG, DOT_LNEG, ← GSYM SNDCART_NEG] THEN
      REWRITE_TAC [DROP_NEG, real_ge, REAL_LE_NEG2, REAL_NEG_SUB] THEN
      ONCE_REWRITE_TAC [CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
      X_GEN_TAC (← q r"k:num") THEN SIMP_TAC [LAMBDA_BETA, LIFT_SUB] THEN
      STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THEN
      ONCE_REWRITE_TAC [← REAL_ARITH (← q r"a:real <= b <=> a - b <= &0")] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MEASURE_IN_PORTION THEN
      REWRITE_TAC [← REAL_ARITH (← q r"b - a dot (x:real^N) <= &0 <=> a dot x >= b")] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"a dot (x:real^N) - b <= &0 <=> a dot x <= b")] THEN
      ASM_SIMP_TAC [LEBESGUE_MEASURABLE_CONVEX, CONVEX_HALFSPACE_LE,
                    CONVEX_HALFSPACE_GE, LIFT_SUB, LIFT_DROP] THEN
      SIMP_TAC [CONTINUOUS_ON_SUB, CONTINUOUS_ON_LIFT_DOT2, LINEAR_CONTINUOUS_ON,
                LINEAR_FSTCART, LINEAR_SNDCART, CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC (← MESON []
       (← q r"~(vec 0 IN sphere(vec 0:real^N,&1)) /\
        (!x:real^N. ~(x = vec 0) ==> P x)
        ==> (!x. x IN sphere(vec 0,&1) ==> P x)")) THEN
      REWRITE_TAC [IN_SPHERE_0, NORM_0, FORALL_PASTECART] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [← GSYM PASTECART_VEC, PASTECART_EQ] THEN
      REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART] THEN
      REWRITE_TAC [FORALL_LIFT, LIFT_DROP] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"b - a dot (x:real^N) = &0 <=> a dot x = b")] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"a dot (x:real^N) - b = &0 <=> a dot x = b")] THEN
      REWRITE_TAC [← GSYM LIFT_NUM, LIFT_EQ, NEGLIGIBLE_HYPERPLANE],
      REWRITE_TAC [EXISTS_PASTECART, EXISTS_LIFT] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:real^N") THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"b:real") THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART, LIFT_DROP] THEN
      SIMP_TAC [CART_EQ, VEC_COMPONENT, LAMBDA_BETA, REAL_SUB_0] THEN
      DISCH_TAC THEN X_GEN_TAC (← q r"k:num") THEN STRIP_TAC THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"k:num"))) THEN
      ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REAL_ARITH
       (← q r"x = y ==> x + y = z ==> y = z / &2"))) THEN
      MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNION_EQ THEN
      REWRITE_TAC [← SET_RULE
       (← q r"{x | x IN s /\ P x} INTER {x | x IN s /\ Q x} =
        {x | x IN s /\ (P x /\ Q x)}")] THEN
      REWRITE_TAC [← SET_RULE
       (← q r"{x | x IN s /\ P x} UNION {x | x IN s /\ Q x} =
        {x | x IN s /\ (P x \/ Q x)}")] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"a >= b \/ a <= b"), IN_GSPEC] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"a >= b /\ a <= b <=> a = b")] THEN
      REWRITE_TAC [← SET_RULE (← q r"{x | x IN s /\ P x} = s INTER {x | P x}")] THEN
      ASM_SIMP_TAC [LEBESGUE_MEASURABLE_CONVEX, CONVEX_HALFSPACE_LE,
                    CONVEX_HALFSPACE_GE,
                    MEASURABLE_MEASURABLE_INTER_LEBESGUE_MEASURABLE] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [IN_SPHERE_0]) THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← NORM_ARITH
       (← q r"norm(x:real^N) = &1 ==> ~(x = vec 0)"))) THEN
      REWRITE_TAC [← GSYM PASTECART_VEC, PASTECART_EQ] THEN
      REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART] THEN
      REWRITE_TAC [FORALL_LIFT, LIFT_DROP, ← GSYM LIFT_NUM, LIFT_EQ] THEN
      SIMP_TAC [NEGLIGIBLE_HYPERPLANE, NEGLIGIBLE_INTER]])

  pure { BORSUK_ULAM_NOT_NULLHOMOTOPIC_GEN, BORSUK_ULAM_NOT_NULLHOMOTOPIC,
         BORSUK_ULAM_SURJECTIVE_GEN, BORSUK_ULAM_SURJECTIVE,
         BORSUK_ULAM_ZERO_GEN, BORSUK_ULAM_ZERO,
         BORSUK_ULAM_ANTIPODAL_SUBSPACE, BORSUK_ULAM_ANTIPODAL_GEN,
         BORSUK_ULAM_ANTIPODAL, BORSUK_ULAM_FRONTIER_MAP_GEN,
         BORSUK_ULAM_FRONTIER_MAP, LUSTERNIK_SCHNIRELMANN, HAM_SANDWICH_THEOREM }
/- ------------------------------------------------------------------------- -/
/- Some technical lemmas about extending maps from cell complexes.           -/
/- (moretop.ml 1980-2623)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MOG where
  EXTEND_MAP_CELL_COMPLEX_TO_SPHERE : thm
  EXTEND_MAP_CELL_COMPLEX_TO_SPHERE_COFINITE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOG [HolBase] (D : MoreTopDeps) (BMOB : MOB) : ExceptT String IO MOG := do
  -- @@SCOPE BEGIN
  let { INESSENTIAL_SPHEREMAP_LOWDIM_GEN, .. } := BMOB
  let { CONTINUOUS_ON_SING, .. } := D.qtopology
  let { ENR_IMP_ANR, ENR_RELATIVE_FRONTIER_CONVEX, NEIGHBOURHOOD_EXTENSION_INTO_ANR,
        NULLHOMOTOPIC_INTO_RELATIVE_FRONTIER_EXTENSION,
        RELATIVE_FRONTIER_RETRACT_OF_PUNCTURED_AFFINE_HULL, retract_of, retraction,
        .. } := D.qdegree
  let { UNIONS_MAXIMAL_SETS, .. } := D.qsession
  let { CELL_COMPLEX_SUBDIVISION_EXISTS, EMPTY_FACE_OF, FACE_OF_AFF_DIM_LT,
        FACE_OF_IMP_CLOSED, FACE_OF_IMP_CONVEX, FACE_OF_IMP_SUBSET, FACE_OF_INTER_SUBFACE,
        FACE_OF_POLYTOPE_POLYTOPE, FACE_OF_REFL, FACE_OF_SUBSET_RELATIVE_FRONTIER,
        FACE_OF_TRANS, facet_of, FINITE_POLYTOPE_FACES, POLYTOPE_IMP_BOUNDED,
        POLYTOPE_IMP_CLOSED, POLYTOPE_IMP_CONVEX, POLYTOPE_IMP_POLYHEDRON,
        RELATIVE_FRONTIER_OF_POLYHEDRON, .. } := D.qpolytope
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_INT_ARITH_TAC, ASM_MESON_TAC, INT_ARITH,
        INT_ARITH_TAC, MESON, MESON_TAC, SET_RULE, SET_TAC, .. } := D.ra.ts.cn.cx.cvx
  let { CARD_CLAUSES, CARD_SUBSET, CONJ_ASSOC, EMPTY_DIFF, EMPTY_SUBSET, EQ_TRANS,
        EXTENSION, FINITE_EMPTY, FINITE_IMAGE, FINITE_INDUCT_STRONG, FINITE_INSERT,
        FINITE_RESTRICT, FINITE_SUBSET, FINITE_UNION, FINITE_UNIONS, FORALL_AND_THM,
        FORALL_IN_GSPEC, .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_IN_INSERT, IMAGE_CLAUSES, IMAGE_o, IMP_CONJ, IMP_IMP,
        IN_DIFF, INT_LE_REFL, INT_OF_NUM_EXISTS, INT_OF_NUM_SUC, INTER_EMPTY, INTER_UNIONS,
        .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_SING, IN_UNION, IN_UNIONS, IN_UNIV, LE_REFL, LE_TRANS,
        LEFT_AND_EXISTS_THM, LEFT_FORALL_IMP_THM, LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY,
        MONO_EXISTS, NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_LET_TRANS, .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_NOT_LE, RIGHT_EXISTS_AND_THM, RIGHT_FORALL_IMP_THM, SIMPLE_IMAGE, SUBSET,
        SUBSET_ANTISYM, SUBSET_REFL, SUBSET_RESTRICT, SUBSET_UNION,
        .. } := D.ra.ts.cn.cx.cvx.core5
  let { num_INDUCTION, o_THM, SUBSET_UNIV, UNION_EMPTY, UNIONS_0, UNIONS_GSPEC,
        UNIONS_INSERT, UNIONS_SUBSET, UNIONS_UNION, .. } := D.ra.ts.cn.cx.cvx.core6
  let { HULL_SUBSET, .. } := D.ra.ts.cn.cx.cvx.misc
  let { dist, .. } := D.ra.ts.cn.cx.cvx.vec4
  let { BOUNDED_SUBSET, CLOSED_IN_CLOSED, .. } := D.ra.ts.cn.cx.cvx.top1
  let { COMPACT_EQ_BOUNDED_CLOSED, .. } := D.ra.ts.cn.cx.cvx.top2
  let { CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_SUBSET, DIAMETER_BOUNDED_BOUND,
        .. } := D.ra.ts.cn.cx.cvx.top3
  let { NOT_BOUNDED_UNIV, .. } := D.ra.ts.cn.cx.cvx.top4
  let { SEPARATE_COMPACT_CLOSED, .. } := D.ra.ts.cn.cx.cvx.top5
  let { AFFINE_BOUNDED_EQ_LOWDIM, RELATIVE_FRONTIER_EQ_EMPTY,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qconvex
  let { SUBSET_UNIONS, UNIONS_MONO, .. } := D.ra.ts.cn.ms.ig.dv.dg.qsession
  let { CONTINUOUS_ON_CASES, CONTINUOUS_ON_CASES_LOCAL, CONTINUOUS_ON_EMPTY,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { OPEN_CLOSED, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology2
  let { DISJOINT_EMPTY, INT_LT_IMP_LE, INT_LTE_TRANS, INT_NOT_LE, UNIONS_1,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qses
  let { BOUNDED_UNIONS, CLOSED_UNIONS, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qtop
  let { AFF_DIM_EMPTY, AFF_DIM_EQ_MINUS1, AFF_DIM_GE, AFF_DIM_SUBSET,
        AFFINE_BOUNDED_EQ_TRIVIAL, CLOSED_RELATIVE_FRONTIER,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx1
  let { relative_frontier, RELATIVE_INTERIOR_EQ_EMPTY, RELATIVE_INTERIOR_SUBSET,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx3
  let { EXCLUDED_MIDDLE, .. } := D
  -- @@SCOPE END

  let (EXTEND_MAP_CELL_COMPLEX_TO_SPHERE,
       EXTEND_MAP_CELL_COMPLEX_TO_SPHERE_COFINITE) ← (do
    let wemma ← prove
     r"!h:real^M->real^N k t f.
            (!s. s IN f ==> ?g. g continuous_on s /\
                                IMAGE g s SUBSET t /\
                                !x. x IN s INTER k ==> g x = h x) /\
            FINITE f /\ (!s. s IN f ==> closed s) /\
            (!s t. s IN f /\ t IN f /\ ~(s = t) ==> (s INTER t) SUBSET k)
            ==> ?g. g continuous_on (UNIONS f) /\
                    IMAGE g (UNIONS f) SUBSET t /\
                    !x. x IN (UNIONS f) INTER k ==> g x = h x"
     (REPLICATE_TAC 3 GEN_TAC THEN
      ONCE_REWRITE_TAC [← TAUT (← q r"p /\ q /\ r ==> s <=> q ==> p /\ r ==> s")] THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      REWRITE_TAC [UNIONS_0, IMAGE_CLAUSES, EMPTY_SUBSET, CONTINUOUS_ON_EMPTY,
                   INTER_EMPTY, NOT_IN_EMPTY] THEN
      REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_INSERT] THEN
      REWRITE_TAC [IMP_IMP, ← GSYM CONJ_ASSOC, SUBSET_REFL] THEN
      MAP_EVERY X_GEN_TAC [← q r"s:real^M->bool", ← q r"u:(real^M->bool)->bool"] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC
       (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      ASM_SIMP_TAC [UNIONS_INSERT] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^M->real^N") STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC (← q r"(s:real^M->bool) UNION UNIONS u = UNIONS u") THENL
       [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN
      FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"f:real^M->real^N") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"\x. if x IN s then (f:real^M->real^N) x else g x") THEN
      CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CASES THEN ASM_SIMP_TAC [CLOSED_UNIONS] THEN
      ASM SET_TAC [])
    let lemma ← prove
     r"!h:real^M->real^N k t f.
            (!s. s IN f ==> ?g. g continuous_on s /\
                                IMAGE g s SUBSET t /\
                                !x. x IN s INTER k ==> g x = h x) /\
            FINITE f /\ (!s. s IN f ==> closed s) /\
            (!s t. s IN f /\ t IN f /\ ~(s SUBSET t) /\ ~(t SUBSET s)
                   ==> (s INTER t) SUBSET k)
            ==> ?g. g continuous_on (UNIONS f) /\
                    IMAGE g (UNIONS f) SUBSET t /\
                    !x. x IN (UNIONS f) INTER k ==> g x = h x"
     (REPEAT STRIP_TAC THEN
      FIRST_ASSUM (SUBST1_TAC o SYM o MATCH_MP UNIONS_MAXIMAL_SETS) THEN
      MATCH_MP_TAC wemma THEN
      ASM_SIMP_TAC [FINITE_RESTRICT, IN_ELIM_THM] THEN ASM SET_TAC [])
    let zemma ← prove
     r"!f:real^M->real^N m n t.
            FINITE m /\ (!c. c IN m ==> polytope c) /\
            n SUBSET m /\ (!c. c IN m DIFF n ==> aff_dim c < aff_dim t) /\
            (!c1 c2. c1 IN m /\ c2 IN m
                     ==> (c1 INTER c2) face_of c1 /\ (c1 INTER c2) face_of c2) /\
            convex t /\ bounded t /\
            f continuous_on (UNIONS n) /\
            IMAGE f (UNIONS n) SUBSET relative_frontier t
            ==> ?g. g continuous_on (UNIONS m) /\
                    IMAGE g (UNIONS m) SUBSET relative_frontier t /\
                    (!x. x IN UNIONS n ==> g x = f x)"
     (REPEAT STRIP_TAC THEN
      ASM_CASES_TAC (← q r"m DIFF n:(real^M->bool)->bool = {}") THENL
       [SUBGOAL_THEN (← q r"(UNIONS m:real^M->bool) SUBSET UNIONS n") ASSUME_TAC THENL
         [ASM SET_TAC [], EXISTS_TAC (← q r"f:real^M->real^N")] THEN
        REWRITE_TAC [] THEN CONJ_TAC THENL
         [ASM_MESON_TAC [CONTINUOUS_ON_SUBSET], ASM SET_TAC []],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!i. &i <= aff_dim t
            ==> ?g. g continuous_on
                    (UNIONS
                     (n UNION {d | ?c. c IN m /\ d face_of c /\
                                        aff_dim d < &i})) /\
                    IMAGE g (UNIONS
                     (n UNION {d | ?c. c IN m /\ d face_of c /\
                                        aff_dim d < &i}))
                    SUBSET relative_frontier t /\
                    (!x. x IN UNIONS n ==> g x = (f:real^M->real^N) x)")
      MP_TAC THENL
       [ALL_TAC,
        MP_TAC (← ISPEC (← q r"aff_dim(t:real^N->bool)") INT_OF_NUM_EXISTS) THEN
        MATCH_MP_TAC (← TAUT (← q r"q /\ (p ==> r) ==> (p <=> q) ==> r")) THEN
        CONJ_TAC THENL
         [ASM_MESON_TAC [AFF_DIM_GE, MEMBER_NOT_EMPTY,
                         ← INT_ARITH (← q r"--(&1):int <= s /\ s < t ==> &0 <= t")],
          ALL_TAC] THEN
        DISCH_THEN (X_CHOOSE_TAC (← q r"i:num")) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"i:num")) THEN ASM_REWRITE_TAC [INT_LE_REFL] THEN
        SUBGOAL_THEN
         (← q r"UNIONS (n UNION {d | ?c. c IN m /\ d face_of c /\ aff_dim d < &i}) =
          UNIONS m:real^M->bool")
         (fun th => REWRITE_TAC [th]) THEN
        FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [MATCH_MP_TAC UNIONS_MONO THEN REWRITE_TAC [IN_UNION] THEN
          REWRITE_TAC [← TAUT (← q r"p \/ q ==> r <=> (p ==> r) /\ (q ==> r)")] THEN
          REWRITE_TAC [FORALL_AND_THM, FORALL_IN_GSPEC] THEN
          CONJ_TAC THENL [ASM_MESON_TAC [SUBSET], GEN_TAC] THEN
          MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [FACE_OF_IMP_SUBSET],
          MATCH_MP_TAC SUBSET_UNIONS THEN REWRITE_TAC [SUBSET, IN_UNION] THEN
          X_GEN_TAC (← q r"d:real^M->bool") THEN DISCH_TAC THEN
          ASM_CASES_TAC (← q r"(d:real^M->bool) IN n") THEN
          ASM_SIMP_TAC [IN_ELIM_THM] THEN
          EXISTS_TAC (← q r"d:real^M->bool") THEN
          ASM_SIMP_TAC [FACE_OF_REFL, POLYTOPE_IMP_CONVEX] THEN
          ASM SET_TAC []]] THEN
      MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
       [REWRITE_TAC [← INT_ARITH (← q r"d < &0 <=> (--(&1) <= d ==> d:int = --(&1))")] THEN
        REWRITE_TAC [AFF_DIM_GE, AFF_DIM_EQ_MINUS1] THEN
        SUBGOAL_THEN
         (← q r"{d:real^M->bool| ?c. c IN m /\ d face_of c /\ d = {}} = {{}}")
         (fun th => REWRITE_TAC [th])
        THENL
         [GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"d:real^M->bool") THEN
          REWRITE_TAC [IN_SING, IN_ELIM_THM] THEN
          ASM_CASES_TAC (← q r"d:real^M->bool = {}") THEN
          ASM_REWRITE_TAC [EMPTY_FACE_OF] THEN ASM SET_TAC [],
          REWRITE_TAC [UNIONS_UNION, UNIONS_1, UNION_EMPTY] THEN
          ASM_MESON_TAC []],
        ALL_TAC] THEN
      X_GEN_TAC (← q r"p:num") THEN REWRITE_TAC [← GSYM INT_OF_NUM_SUC] THEN
      REWRITE_TAC [← INT_ARITH (← q r"p + &1 <= x <=> p:int < x")] THEN
      DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
      ASM_SIMP_TAC [INT_LT_IMP_LE] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"h:real^M->real^N") STRIP_ASSUME_TAC) THEN
      REWRITE_TAC [← INT_ARITH (← q r"x:int < p + &1 <=> x <= p")] THEN
      SUBGOAL_THEN (← q r"~(t:real^N->bool = {})") ASSUME_TAC THENL
       [ASM_MESON_TAC [AFF_DIM_EMPTY, ← INT_ARITH (← q r"~(&p:int < --(&1))")],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"~(relative_frontier t:real^N->bool = {})") ASSUME_TAC THENL
       [ASM_REWRITE_TAC [RELATIVE_FRONTIER_EQ_EMPTY] THEN DISCH_TAC THEN
        MP_TAC (← ISPEC (← q r"t:real^N->bool") AFFINE_BOUNDED_EQ_LOWDIM) THEN
        ASM_REWRITE_TAC [] THEN ASM_INT_ARITH_TAC,
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!d. d IN n UNION {d | ?c. c IN m /\ d face_of c /\ aff_dim d <= &p}
            ==> ?g. (g:real^M->real^N) continuous_on d /\
                    IMAGE g d SUBSET relative_frontier t /\
                    !x. x IN d INTER
                        UNIONS
                      (n UNION {d | ?c. c IN m /\ d face_of c /\ aff_dim d < &p})
                        ==> g x = h x")
      MP_TAC THENL
       [X_GEN_TAC (← q r"d:real^M->bool") THEN
        ASM_CASES_TAC (← q r"(d:real^M->bool) SUBSET UNIONS
                   (n UNION {d | ?c. c IN m /\ d face_of c /\ aff_dim d < &p})")
        THENL
         [DISCH_THEN (K ALL_TAC) THEN EXISTS_TAC (← q r"h:real^M->real^N") THEN
          REWRITE_TAC [] THEN CONJ_TAC THENL
           [ASM_MESON_TAC [CONTINUOUS_ON_SUBSET], ASM SET_TAC []],
          ALL_TAC] THEN
        ASM_CASES_TAC (← q r"?a:real^M. d = {a}") THENL
         [FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"a:real^M") SUBST_ALL_TAC) THEN
          DISCH_THEN (K ALL_TAC) THEN ASM_SIMP_TAC [CONTINUOUS_ON_SING, ← SET_RULE
           (← q r"~({a} SUBSET s) ==> ~(x IN {a} INTER s)")] THEN
          REWRITE_TAC [SUBSET, FORALL_IN_IMAGE,
                       FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
          MATCH_MP_TAC (← MESON [] (← q r"(?c. P(\x. c)) ==> (?f. P f)")) THEN
          ASM SET_TAC [],
          ALL_TAC] THEN
        SUBGOAL_THEN (← q r"~(d:real^M->bool = {})") ASSUME_TAC THENL
         [ASM SET_TAC [], ALL_TAC] THEN
        FIRST_ASSUM (MP_TAC o MATCH_MP (← SET_RULE
         (← q r"~(s SUBSET UNIONS f) ==> ~(s IN f)"))) THEN
        REWRITE_TAC [IMP_IMP] THEN DISCH_THEN (MP_TAC o MATCH_MP
         (← SET_RULE (← q r"~(d IN s UNION t) /\ d IN s UNION u
                    ==> ~(d IN s) /\ d IN u DIFF t"))) THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        DISCH_THEN (MP_TAC o MATCH_MP (← SET_RULE
         (← q r"d IN
          {d | ?c. c IN m /\ d face_of c /\ aff_dim d <= &p} DIFF
          {d | ?c. c IN m /\ d face_of c /\ aff_dim d < &p}
          ==> ?c. c IN m /\ d face_of c /\
                  (aff_dim d <= &p /\ ~(aff_dim d < &p))"))) THEN
        REWRITE_TAC [← INT_ARITH (← q r"d:int <= p /\ ~(d < p) <=> d = p")] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"c:real^M->bool") STRIP_ASSUME_TAC) THEN
        MP_TAC (← ISPECL [← q r"h:real^M->real^N", ← q r"relative_frontier d:real^M->bool",
          ← q r"t:real^N->bool"] NULLHOMOTOPIC_INTO_RELATIVE_FRONTIER_EXTENSION) THEN
        ASM_REWRITE_TAC [CLOSED_RELATIVE_FRONTIER,
                         RELATIVE_FRONTIER_EQ_EMPTY] THEN
        SUBGOAL_THEN
         (← q r"relative_frontier d SUBSET
          UNIONS {e:real^M->bool | e face_of c /\ aff_dim e < &p}")
        ASSUME_TAC THENL
         [W (MP_TAC o PART_MATCH (lhs o rand) RELATIVE_FRONTIER_OF_POLYHEDRON o
            lhand o snd) THEN
          ANTS_TAC THENL
           [ASM_MESON_TAC [POLYTOPE_IMP_POLYHEDRON, FACE_OF_POLYTOPE_POLYTOPE],
            DISCH_THEN SUBST1_TAC] THEN
          MATCH_MP_TAC SUBSET_UNIONS THEN
          ASM_SIMP_TAC [SUBSET, FORALL_IN_GSPEC, IN_ELIM_THM, facet_of] THEN
          X_GEN_TAC (← q r"f:real^M->bool") THEN REPEAT STRIP_TAC THENL
           [ASM_MESON_TAC [FACE_OF_TRANS], INT_ARITH_TAC],
          ALL_TAC] THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
           [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
              CONTINUOUS_ON_SUBSET)) THEN
            ASM SET_TAC [],
            ASM_MESON_TAC [AFFINE_BOUNDED_EQ_TRIVIAL, FACE_OF_POLYTOPE_POLYTOPE,
                           POLYTOPE_IMP_BOUNDED],
            ASM SET_TAC []],
          ALL_TAC] THEN
        MATCH_MP_TAC (← TAUT (← q r"p /\ (q ==> r) ==> (p <=> q) ==> r")) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC INESSENTIAL_SPHEREMAP_LOWDIM_GEN THEN
          ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
           [ASM_MESON_TAC [FACE_OF_POLYTOPE_POLYTOPE, POLYTOPE_IMP_CONVEX],
            ASM_MESON_TAC [FACE_OF_POLYTOPE_POLYTOPE, POLYTOPE_IMP_BOUNDED],
            FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
              CONTINUOUS_ON_SUBSET)) THEN
            ASM SET_TAC [],
            ASM SET_TAC []],
          MATCH_MP_TAC MONO_EXISTS] THEN
        X_GEN_TAC (← q r"g:real^M->real^N") THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC [CONTINUOUS_ON_SUBSET, SUBSET_UNIV],
          ASM SET_TAC [],
          ALL_TAC] THEN
        REWRITE_TAC [INTER_UNIONS] THEN FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
         (← SET_RULE (← q r"(!x. x IN s ==> P x) ==> t SUBSET s
                    ==> !x. x IN t ==> P x"))) THEN
        REWRITE_TAC [UNIONS_SUBSET, FORALL_IN_GSPEC] THEN
        X_GEN_TAC (← q r"e:real^M->bool") THEN DISCH_TAC THEN
        MATCH_MP_TAC FACE_OF_SUBSET_RELATIVE_FRONTIER THEN CONJ_TAC THENL
         [MATCH_MP_TAC (← MESON []
           (← q r"(d INTER e) face_of d /\ (d INTER e) face_of e
            ==> (d INTER e) face_of d")) THEN
          MATCH_MP_TAC FACE_OF_INTER_SUBFACE THEN
          EXISTS_TAC (← q r"c:real^M->bool") THEN ASM_REWRITE_TAC [] THEN
          FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [IN_UNION]) THEN
          REWRITE_TAC [IN_ELIM_THM] THEN
          STRIP_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
          ASM_MESON_TAC [FACE_OF_REFL, SUBSET, POLYTOPE_IMP_CONVEX],
          REWRITE_TAC [← SET_RULE (← q r"d INTER e = d <=> d SUBSET e")] THEN
          DISCH_TAC THEN
          FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [IN_UNION]) THEN
          REWRITE_TAC [IN_ELIM_THM] THEN
          DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL [ASM SET_TAC [], ALL_TAC] THEN
          ASM_MESON_TAC [AFF_DIM_SUBSET, INT_NOT_LE]],
        ALL_TAC] THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ] lemma)) THEN
      ANTS_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [] THEN ASM SET_TAC []] THEN
      CONJ_TAC THENL
       [REWRITE_TAC [FINITE_UNION] THEN
        CONJ_TAC THENL [ASM_MESON_TAC [FINITE_SUBSET], ALL_TAC] THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC (← q r"UNIONS {{d:real^M->bool | d face_of c} | c IN m}") THEN
        CONJ_TAC THENL
         [REWRITE_TAC [FINITE_UNIONS, FORALL_IN_GSPEC] THEN
          ONCE_REWRITE_TAC [SIMPLE_IMAGE] THEN ASM_SIMP_TAC [FINITE_IMAGE] THEN
          ASM_MESON_TAC [FINITE_POLYTOPE_FACES],
          REWRITE_TAC [UNIONS_GSPEC] THEN SET_TAC []],
        ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN
        ASM_MESON_TAC [FACE_OF_IMP_CLOSED, POLYTOPE_IMP_CLOSED,
                       POLYTOPE_IMP_CONVEX, SUBSET],
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [← q r"d:real^M->bool", ← q r"e:real^M->bool"] THEN
      REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN
      DISCH_THEN (CONJUNCTS_THEN2 (DISJ_CASES_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN (← q r"c:real^M->bool") STRIP_ASSUME_TAC)) MP_TAC)
      THENL [ASM SET_TAC [], ALL_TAC] THEN
      DISCH_THEN (CONJUNCTS_THEN2 (DISJ_CASES_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN (← q r"k:real^M->bool") STRIP_ASSUME_TAC)) MP_TAC)
      THENL [ASM SET_TAC [], STRIP_TAC] THEN
      REWRITE_TAC [UNIONS_UNION] THEN
      MATCH_MP_TAC (← SET_RULE (← q r"s SUBSET u ==> s SUBSET t UNION u")) THEN
      MATCH_MP_TAC (← SET_RULE (← q r"x IN s ==> x SUBSET UNIONS s")) THEN
      REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC (← q r"c:real^M->bool") THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"d INTER e face_of (d:real^M->bool) /\
                    d INTER e face_of e")
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [FACE_OF_INTER_SUBFACE], ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [FACE_OF_TRANS], ALL_TAC] THEN
      TRANS_TAC INT_LTE_TRANS (← q r"aff_dim(d:real^M->bool)") THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [ASM_MESON_TAC [POLYTOPE_IMP_CONVEX, FACE_OF_IMP_CONVEX],
        ASM SET_TAC []])
    let memma ← prove
     r"!h:real^M->real^N k t u f.
            (!s. s IN f ==> ?a g. ~(a IN u) /\ g continuous_on (s DELETE a) /\
                                 IMAGE g (s DELETE a) SUBSET t /\
                                 !x. x IN s INTER k ==> g x = h x) /\
            FINITE f /\ (!s. s IN f ==> closed s) /\
            (!s t. s IN f /\ t IN f /\ ~(s = t) ==> (s INTER t) SUBSET k)
            ==> ?c g. FINITE c /\ DISJOINT c u /\ CARD c <= CARD f /\
                      g continuous_on (UNIONS f DIFF c) /\
                      IMAGE g (UNIONS f DIFF c) SUBSET t /\
                      !x. x IN (UNIONS f DIFF c) INTER k ==> g x = h x"
     (REPLICATE_TAC 4 GEN_TAC THEN
      ONCE_REWRITE_TAC [← TAUT (← q r"p /\ q /\ r ==> s <=> q ==> p /\ r ==> s")] THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      REWRITE_TAC [UNIONS_0, IMAGE_CLAUSES, EMPTY_SUBSET, CONTINUOUS_ON_EMPTY,
                   INTER_EMPTY, NOT_IN_EMPTY, EMPTY_DIFF] THEN
      CONJ_TAC THENL
       [MESON_TAC [DISJOINT_EMPTY, FINITE_EMPTY, CARD_CLAUSES, LE_REFL],
        ALL_TAC] THEN
      REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_INSERT] THEN
      REWRITE_TAC [IMP_IMP, ← GSYM CONJ_ASSOC, SUBSET_REFL] THEN
      MAP_EVERY X_GEN_TAC [← q r"s:real^M->bool", ← q r"u:(real^M->bool)->bool"] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC
       (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      ASM_SIMP_TAC [UNIONS_INSERT] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"c:real^M->bool", ← q r"g:real^M->real^N"] THEN
      STRIP_TAC THEN ASM_SIMP_TAC [CARD_CLAUSES] THEN
      ASM_CASES_TAC (← q r"(s:real^M->bool) UNION UNIONS u = UNIONS u") THENL
       [ASM_SIMP_TAC [] THEN ASM_MESON_TAC [← ARITH_RULE (← q r"x <= y ==> x <= SUC y")],
        ALL_TAC] THEN
      FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"a:real^M")
       (X_CHOOSE_THEN (← q r"f:real^M->real^N") STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC (← q r"(a:real^M) INSERT c") THEN
      ASM_SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, RIGHT_EXISTS_AND_THM] THEN
      REPEAT CONJ_TAC THENL [ASM SET_TAC [], ASM_ARITH_TAC, ALL_TAC] THEN
      EXISTS_TAC (← q r"\x. if x IN s then (f:real^M->real^N) x else g x") THEN
      CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC (← q r"(s DIFF ((a:real^M) INSERT c)) UNION
                  (UNIONS u DIFF ((a:real^M) INSERT c))") THEN
      CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC [CLOSED_IN_CLOSED] THEN
        EXISTS_TAC (← q r"s:real^M->bool") THEN ASM_REWRITE_TAC [],
        REWRITE_TAC [CLOSED_IN_CLOSED] THEN
        EXISTS_TAC (← q r"UNIONS u:real^M->bool") THEN ASM_SIMP_TAC [CLOSED_UNIONS],
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
              CONTINUOUS_ON_SUBSET)),
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
              CONTINUOUS_ON_SUBSET)),
        ALL_TAC] THEN
      ASM SET_TAC [])
    let temma ← prove
     r"!h:real^M->real^N k t u f.
            (!s. s IN f ==> ?a g. ~(a IN u) /\ g continuous_on (s DELETE a) /\
                                  IMAGE g (s DELETE a) SUBSET t /\
                                  !x. x IN s INTER k ==> g x = h x) /\
            FINITE f /\ (!s. s IN f ==> closed s) /\
            (!s t. s IN f /\ t IN f /\  ~(s SUBSET t) /\ ~(t SUBSET s)
                   ==> (s INTER t) SUBSET k)
            ==> ?c g. FINITE c /\ DISJOINT c u /\ CARD c <= CARD f /\
                      g continuous_on (UNIONS f DIFF c) /\
                      IMAGE g (UNIONS f DIFF c) SUBSET t /\
                      !x. x IN (UNIONS f DIFF c) INTER k ==> g x = h x"
     (REPEAT STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"h:real^M->real^N", ← q r"k:real^M->bool", ← q r"t:real^N->bool",
                       ← q r"u:real^M->bool",
                       ← q r"{t:real^M->bool | t IN f /\
                                          (!u. u IN f ==> ~(t PSUBSET u))}"]
            memma) THEN
      ASM_SIMP_TAC [FINITE_RESTRICT, IN_ELIM_THM, UNIONS_MAXIMAL_SETS] THEN
      ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
            LE_TRANS)) THEN
      MATCH_MP_TAC CARD_SUBSET THEN
      ASM_SIMP_TAC [] THEN SET_TAC [])
    let bemma ← prove
     r"!f:real^M->real^N m n t.
          FINITE m /\ (!c. c IN m ==> polytope c) /\
          n SUBSET m /\ (!c. c IN m DIFF n ==> aff_dim c <= aff_dim t) /\
          (!c1 c2. c1 IN m /\ c2 IN m
                   ==> (c1 INTER c2) face_of c1 /\ (c1 INTER c2) face_of c2) /\
          convex t /\ bounded t /\
          f continuous_on (UNIONS n) /\
          IMAGE f (UNIONS n) SUBSET relative_frontier t
          ==> ?k g. FINITE k /\ DISJOINT k (UNIONS n) /\ CARD k <= CARD m /\
                    g continuous_on (UNIONS m DIFF k) /\
                    IMAGE g (UNIONS m DIFF k) SUBSET relative_frontier t /\
                    (!x. x IN UNIONS n ==> g x = f x)"
     (REPEAT STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"f:real^M->real^N",
           ← q r"n UNION {d:real^M->bool | ?c. c IN m DIFF n /\ d face_of c /\
                                          aff_dim d < aff_dim(t:real^N->bool)}",
           ← q r"n:(real^M->bool)->bool", ← q r"t:real^N->bool"] zemma) THEN
      ASM_REWRITE_TAC [SUBSET_UNION, ← SET_RULE
       (← q r"(n UNION m) DIFF n = m DIFF n")] THEN
      SIMP_TAC [IN_DIFF, IN_ELIM_THM, LEFT_IMP_EXISTS_THM,
                LEFT_AND_EXISTS_THM] THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC [FINITE_UNION] THEN
          CONJ_TAC THENL [ASM_MESON_TAC [FINITE_SUBSET], ALL_TAC] THEN
          MATCH_MP_TAC FINITE_SUBSET THEN
          EXISTS_TAC (← q r"UNIONS {{d:real^M->bool | d face_of c} | c IN m}") THEN
          CONJ_TAC THENL
           [REWRITE_TAC [FINITE_UNIONS, FORALL_IN_GSPEC] THEN
            ONCE_REWRITE_TAC [SIMPLE_IMAGE] THEN ASM_SIMP_TAC [FINITE_IMAGE] THEN
            ASM_MESON_TAC [FINITE_POLYTOPE_FACES],
            REWRITE_TAC [UNIONS_GSPEC] THEN SET_TAC []],
          REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN
          ASM_MESON_TAC [FACE_OF_POLYTOPE_POLYTOPE, SUBSET],
          REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN
          ASM_MESON_TAC [FACE_OF_INTER_SUBFACE, SUBSET, FACE_OF_REFL,
                         POLYTOPE_IMP_CONVEX, FACE_OF_IMP_CONVEX]],
        ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"h:real^M->real^N") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       (← q r"!d. d IN m
            ==> ?a g. ~(a IN UNIONS n) /\
                      (g:real^M->real^N) continuous_on (d DELETE a) /\
                      IMAGE g (d DELETE a) SUBSET relative_frontier t /\
                      !x. x IN d INTER
                           UNIONS
                            (n UNION {d | ?c. (c IN m /\ ~(c IN n)) /\
                                              d face_of c /\
                                              aff_dim d < aff_dim t})
                          ==> g x = h x")
      MP_TAC THENL
       [X_GEN_TAC (← q r"d:real^M->bool") THEN DISCH_TAC THEN
        ASM_CASES_TAC (← q r"(d:real^M->bool) SUBSET
                       UNIONS(n UNION {d | ?c. (c IN m /\ ~(c IN n)) /\
                                               d face_of c /\
                                       aff_dim d < aff_dim(t:real^N->bool)})")
        THENL
         [SUBGOAL_THEN (← q r"~(UNIONS n = (:real^M))") MP_TAC THENL
           [MATCH_MP_TAC (← MESON [NOT_BOUNDED_UNIV]
             (← q r"bounded s ==> ~(s = UNIV)")) THEN
            MATCH_MP_TAC BOUNDED_UNIONS THEN
            ASM_MESON_TAC [POLYTOPE_IMP_BOUNDED, SUBSET, FINITE_SUBSET],
            GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [EXTENSION]] THEN
          REWRITE_TAC [IN_UNIV, NOT_FORALL_THM] THEN
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:real^M") THEN
          STRIP_TAC THEN EXISTS_TAC (← q r"h:real^M->real^N") THEN
          ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
           [ASM_MESON_TAC [CONTINUOUS_ON_SUBSET,
                           ← SET_RULE (← q r"s SUBSET t ==> s DELETE a SUBSET t")],
            ASM SET_TAC []],
          ALL_TAC] THEN
        ASM_CASES_TAC (← q r"(d:real^M->bool) IN n") THENL [ASM SET_TAC [], ALL_TAC] THEN
        DISJ_CASES_THEN MP_TAC (← SPEC
         (← q r"relative_interior(d:real^M->bool) = {}") EXCLUDED_MIDDLE)
        THENL
         [ASM_SIMP_TAC [RELATIVE_INTERIOR_EQ_EMPTY, POLYTOPE_IMP_CONVEX] THEN
          ASM SET_TAC [],
          REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY]] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:real^M") THEN STRIP_TAC THEN
        SUBGOAL_THEN
         (← q r"relative_frontier d SUBSET
          UNIONS {e:real^M->bool | e face_of d /\
                                   aff_dim e < aff_dim(t:real^N->bool)}")
        ASSUME_TAC THENL
         [W (MP_TAC o PART_MATCH (lhs o rand) RELATIVE_FRONTIER_OF_POLYHEDRON o
            lhand o snd) THEN
          ANTS_TAC THENL
           [ASM_MESON_TAC [POLYTOPE_IMP_POLYHEDRON, FACE_OF_POLYTOPE_POLYTOPE],
            DISCH_THEN SUBST1_TAC] THEN
          MATCH_MP_TAC SUBSET_UNIONS THEN
          ASM_SIMP_TAC [SUBSET, FORALL_IN_GSPEC, IN_ELIM_THM, facet_of] THEN
          ASM_SIMP_TAC [← INT_ARITH (← q r"d - &1:int < t <=> d <= t"), IN_DIFF],
          ALL_TAC] THEN
        MP_TAC (← ISPECL [← q r"d:real^M->bool", ← q r"a:real^M"]
            RELATIVE_FRONTIER_RETRACT_OF_PUNCTURED_AFFINE_HULL) THEN
        ASM_SIMP_TAC [POLYTOPE_IMP_CONVEX, POLYTOPE_IMP_BOUNDED] THEN
        REWRITE_TAC [retract_of, LEFT_IMP_EXISTS_THM, retraction] THEN
        X_GEN_TAC (← q r"r:real^M->real^M") THEN STRIP_TAC THEN
        EXISTS_TAC (← q r"(h:real^M->real^N) o (r:real^M->real^M)") THEN
        REPEAT CONJ_TAC THENL
         [REWRITE_TAC [IN_UNIONS] THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"e:real^M->bool") STRIP_ASSUME_TAC) THEN
          SUBGOAL_THEN
           (← q r"e INTER d face_of e /\ e INTER d face_of (d:real^M->bool)")
          MP_TAC THENL [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
          DISCH_THEN (MP_TAC o MATCH_MP
            (← REWRITE_RULE [IMP_CONJ] FACE_OF_SUBSET_RELATIVE_FRONTIER) o
            CONJUNCT2) THEN
          REWRITE_TAC [NOT_IMP, relative_frontier] THEN
          MP_TAC (← ISPEC (← q r"d:real^M->bool") RELATIVE_INTERIOR_SUBSET) THEN
          ASM SET_TAC [],
          MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
              CONTINUOUS_ON_SUBSET)) THEN
          SIMP_TAC [HULL_SUBSET, ← SET_RULE
                    (← q r"s SUBSET t ==> s DELETE a SUBSET t DELETE a")],
          REWRITE_TAC [IMAGE_o] THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
           (← q r"IMAGE h t SUBSET u ==> s SUBSET t ==> IMAGE h s SUBSET u"))),
          SIMP_TAC [INTER_UNIONS, o_THM] THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
           (← SET_RULE (← q r"(!x. x IN s ==> r x = x) ==> t SUBSET s
                      ==> !x. x IN t ==> h(r x) = h x"))) THEN
          REWRITE_TAC [UNIONS_SUBSET, FORALL_IN_GSPEC] THEN
          X_GEN_TAC (← q r"e:real^M->bool") THEN DISCH_TAC THEN
          MATCH_MP_TAC FACE_OF_SUBSET_RELATIVE_FRONTIER THEN
          CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
          MATCH_MP_TAC (← MESON []
           (← q r"(d INTER e) face_of d /\ (d INTER e) face_of e
            ==> (d INTER e) face_of d")) THEN
          FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [IN_UNION]) THEN
          REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THENL
           [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
          MATCH_MP_TAC FACE_OF_INTER_SUBFACE THEN
          MAP_EVERY EXISTS_TAC [← q r"d:real^M->bool", ← q r"c:real^M->bool"] THEN
          ASM_SIMP_TAC [FACE_OF_REFL, POLYTOPE_IMP_CONVEX]] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
         (← q r"IMAGE r (h DELETE a) SUBSET t ==> d SUBSET h /\ t SUBSET u
          ==> IMAGE r (d DELETE a) SUBSET u"))) THEN
        REWRITE_TAC [HULL_SUBSET] THEN ASM SET_TAC [],
        ALL_TAC] THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ] temma)) THEN
      ANTS_TAC THENL
       [ALL_TAC,
        REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
        STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC []] THEN
      ASM_SIMP_TAC [POLYTOPE_IMP_CLOSED] THEN
      MAP_EVERY X_GEN_TAC [← q r"d:real^M->bool", ← q r"e:real^M->bool"] THEN
      STRIP_TAC THEN REWRITE_TAC [UNIONS_UNION] THEN
      ASM_CASES_TAC (← q r"(d:real^M->bool) IN n") THENL [ASM SET_TAC [], ALL_TAC] THEN
      MATCH_MP_TAC (← SET_RULE (← q r"x IN s ==> x SUBSET t UNION UNIONS s")) THEN
      REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC (← q r"d:real^M->bool") THEN
      ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC (← q r"d INTER e:real^M->bool = d") THENL
        [ASM SET_TAC [], ALL_TAC] THEN
      ASM_SIMP_TAC [] THEN TRANS_TAC INT_LTE_TRANS (← q r"aff_dim(d:real^M->bool)") THEN
      ASM_SIMP_TAC [IN_DIFF] THEN MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
      ASM_MESON_TAC [POLYTOPE_IMP_CONVEX])
    CONJ_PAIR (← prove
     r"(!f:real^M->real^N m s t.
          FINITE m /\ (!c. c IN m ==> polytope c /\ aff_dim c < aff_dim t) /\
          (!c1 c2. c1 IN m /\ c2 IN m
                   ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2) /\
          s SUBSET UNIONS m /\ closed s /\ convex t /\ bounded t /\
          f continuous_on s /\ IMAGE f s SUBSET relative_frontier t
          ==> ?g. g continuous_on UNIONS m /\
                  IMAGE g (UNIONS m) SUBSET relative_frontier t /\
                  !x. x IN s ==> g x = f x) /\
       (!f:real^M->real^N m s t.
          FINITE m /\ (!c. c IN m ==> polytope c /\ aff_dim c <= aff_dim t) /\
          (!c1 c2. c1 IN m /\ c2 IN m
                   ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2) /\
          s SUBSET UNIONS m /\ closed s /\ convex t /\ bounded t /\
          f continuous_on s /\ IMAGE f s SUBSET relative_frontier t
          ==> ?k g. FINITE k /\ DISJOINT k s /\
                    g continuous_on (UNIONS m DIFF k) /\
                    IMAGE g (UNIONS m DIFF k) SUBSET relative_frontier t /\
                    !x. x IN s ==> g x = f x)"
     (CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN
        SUBGOAL_THEN (← q r"compact(s:real^M->bool)") ASSUME_TAC THENL
         [ASM_SIMP_TAC [COMPACT_EQ_BOUNDED_CLOSED] THEN
          ASM_MESON_TAC [BOUNDED_SUBSET, BOUNDED_UNIONS, POLYTOPE_IMP_BOUNDED],
          ALL_TAC] THEN
        MP_TAC (← ISPECL [← q r"f:real^M->real^N", ← q r"s:real^M->bool",
                         ← q r"relative_frontier t:real^N->bool"]
              NEIGHBOURHOOD_EXTENSION_INTO_ANR) THEN
        ASM_SIMP_TAC [LEFT_FORALL_IMP_THM, ENR_IMP_ANR,
                      ENR_RELATIVE_FRONTIER_CONVEX] THEN
        REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [← q r"v:real^M->bool", ← q r"g:real^M->real^N"] THEN
        STRIP_TAC THEN
        MP_TAC (← ISPECL [← q r"s:real^M->bool", ← q r"(:real^M) DIFF v"]
              SEPARATE_COMPACT_CLOSED) THEN
        ASM_SIMP_TAC [← GSYM OPEN_CLOSED, IN_DIFF, IN_UNIV] THEN
        ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
        ONCE_REWRITE_TAC [← TAUT (← q r"p /\ ~q ==> r <=> p /\ ~r ==> q")] THEN
        REWRITE_TAC [REAL_NOT_LE, LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC (← q r"d:real") THEN STRIP_TAC THEN
        MP_TAC (← ISPECL [← q r"m:(real^M->bool)->bool", ← q r"aff_dim(t:real^N->bool) - &1",
                         ← q r"d:real"] CELL_COMPLEX_SUBDIVISION_EXISTS) THEN
        ASM_SIMP_TAC [← INT_ARITH (← q r"x:int <= t - &1 <=> x < t")] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"n:(real^M->bool)->bool") STRIP_ASSUME_TAC) THEN
        MP_TAC (← ISPECL
         [← q r"g:real^M->real^N", ← q r"n:(real^M->bool)->bool",
          ← q r"{c:real^M->bool | c IN n /\ c SUBSET v}", ← q r"t:real^N->bool"]
         zemma) THEN
        ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
         [ASM_SIMP_TAC [SUBSET_RESTRICT, IN_DIFF] THEN CONJ_TAC THENL
           [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
              CONTINUOUS_ON_SUBSET)) THEN
            ASM SET_TAC [],
            ASM SET_TAC []],
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"h:real^M->real^N") THEN
          STRIP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"x:real^M") THEN
          DISCH_TAC THEN TRANS_TAC EQ_TRANS (← q r"(g:real^M->real^N) x") THEN
          CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
          SUBGOAL_THEN (← q r"(x:real^M) IN UNIONS n") MP_TAC THENL
           [ASM SET_TAC [], ALL_TAC] THEN
          REWRITE_TAC [IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
          X_GEN_TAC (← q r"c:real^M->bool") THEN STRIP_TAC THEN
          ASM_REWRITE_TAC [IN_ELIM_THM] THEN REWRITE_TAC [SUBSET] THEN
          X_GEN_TAC (← q r"y:real^M") THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          EXISTS_TAC (← q r"x:real^M") THEN ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC REAL_LET_TRANS THEN
          EXISTS_TAC (← q r"diameter(c:real^M->bool)") THEN
          ASM_SIMP_TAC [dist] THEN MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN
          ASM_SIMP_TAC [POLYTOPE_IMP_BOUNDED]],
        REPEAT STRIP_TAC THEN
        SUBGOAL_THEN (← q r"compact(s:real^M->bool)") ASSUME_TAC THENL
         [ASM_SIMP_TAC [COMPACT_EQ_BOUNDED_CLOSED] THEN
          ASM_MESON_TAC [BOUNDED_SUBSET, BOUNDED_UNIONS, POLYTOPE_IMP_BOUNDED],
          ALL_TAC] THEN
        MP_TAC (← ISPECL [← q r"f:real^M->real^N", ← q r"s:real^M->bool",
                         ← q r"relative_frontier t:real^N->bool"]
              NEIGHBOURHOOD_EXTENSION_INTO_ANR) THEN
        ASM_SIMP_TAC [LEFT_FORALL_IMP_THM, ENR_IMP_ANR,
                      ENR_RELATIVE_FRONTIER_CONVEX] THEN
        REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [← q r"v:real^M->bool", ← q r"g:real^M->real^N"] THEN
        STRIP_TAC THEN
        MP_TAC (← ISPECL [← q r"s:real^M->bool", ← q r"(:real^M) DIFF v"]
              SEPARATE_COMPACT_CLOSED) THEN
        ASM_SIMP_TAC [← GSYM OPEN_CLOSED, IN_DIFF, IN_UNIV] THEN
        ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
        ONCE_REWRITE_TAC [← TAUT (← q r"p /\ ~q ==> r <=> p /\ ~r ==> q")] THEN
        REWRITE_TAC [REAL_NOT_LE, LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC (← q r"d:real") THEN STRIP_TAC THEN
        MP_TAC (← ISPECL [← q r"m:(real^M->bool)->bool", ← q r"aff_dim(t:real^N->bool)",
                         ← q r"d:real"] CELL_COMPLEX_SUBDIVISION_EXISTS) THEN
        ASM_SIMP_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"n:(real^M->bool)->bool") STRIP_ASSUME_TAC) THEN
        MP_TAC (← ISPECL
         [← q r"g:real^M->real^N", ← q r"n:(real^M->bool)->bool",
          ← q r"{c:real^M->bool | c IN n /\ c SUBSET v}", ← q r"t:real^N->bool"]
         bemma) THEN
        ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
         [ASM_SIMP_TAC [SUBSET_RESTRICT, IN_DIFF] THEN CONJ_TAC THENL
           [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
              CONTINUOUS_ON_SUBSET)) THEN
            ASM SET_TAC [],
            ASM SET_TAC []],
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"k:real^M->bool") THEN
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"h:real^M->real^N") THEN
          STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
           [FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
             (← q r"DISJOINT k u ==> s SUBSET u ==> DISJOINT k s"))) THEN
            REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC,
            X_GEN_TAC (← q r"x:real^M") THEN
            DISCH_TAC THEN TRANS_TAC EQ_TRANS (← q r"(g:real^M->real^N) x") THEN
            CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []] THEN
          (SUBGOAL_THEN (← q r"(x:real^M) IN UNIONS n") MP_TAC THENL
            [ASM SET_TAC [], ALL_TAC] THEN
           REWRITE_TAC [IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
           X_GEN_TAC (← q r"c:real^M->bool") THEN STRIP_TAC THEN
           ASM_REWRITE_TAC [IN_ELIM_THM] THEN REWRITE_TAC [SUBSET] THEN
           X_GEN_TAC (← q r"y:real^M") THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
           EXISTS_TAC (← q r"x:real^M") THEN ASM_REWRITE_TAC [] THEN
           MATCH_MP_TAC REAL_LET_TRANS THEN
            EXISTS_TAC (← q r"diameter(c:real^M->bool)") THEN
           ASM_SIMP_TAC [dist] THEN MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN
           ASM_SIMP_TAC [POLYTOPE_IMP_BOUNDED])]])))

  pure { EXTEND_MAP_CELL_COMPLEX_TO_SPHERE,
         EXTEND_MAP_CELL_COMPLEX_TO_SPHERE_COFINITE }
/- ------------------------------------------------------------------------- -/
/- Special cases and corollaries involving spheres: the simple cofinite      -/
/- extension.                                                                -/
/- (moretop.ml 2624-2834)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MOH where
  EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_SIMPLE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOH [HolBase] (D : MoreTopDeps) (BMOG : MOG) : ExceptT String IO MOH := do
  -- @@SCOPE BEGIN
  let { EXTEND_MAP_CELL_COMPLEX_TO_SPHERE_COFINITE, .. } := BMOG
  let { AFFINE_HULL_CONVEX_INTER_NONEMPTY_INTERIOR, .. } := D.qconvex
  let { AFFINE_IMP_POLYHEDRON, FACE_OF_REFL_EQ, POLYTOPE_INTER_POLYHEDRON,
        POLYTOPE_INTERVAL, .. } := D.qpolytope
  let { FINITE_REAL_INTERVAL, .. } := D.ra.qsession
  let { BOUNDED_SUBSET_CLOSED_INTERVAL_SYMMETRIC, .. } := D.ra.ts.cn.ms.qtopology1
  let { ASM_INT_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INT_ARITH, REAL_ARITH_TAC,
        REAL_RAT_REDUCE_CONV, SET_RULE, SET_TAC, .. } := D.ra.ts.cn.cx.cvx
  let { INFINITE, .. } := D.ra.ts.cn.cx.cpx
  let { INTERIOR_INTERVAL, .. } := D.ra.ts.cn.ms.ig.qtopology
  let { DIFF_EMPTY, DIFF_EQ_EMPTY, EMPTY_DIFF, EMPTY_SUBSET, EQ_TRANS, FINITE_EMPTY,
        FINITE_IMAGE_INJ_EQ, FINITE_INTER, FINITE_SING, FINITE_SUBSET,
        .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_IN_INSERT, IMAGE_CLAUSES, IMAGE_o, IMAGE_SUBSET, IMP_CONJ,
        IMP_CONJ_ALT, IMP_IMP, IN_DIFF, INSERT_SUBSET, INT_LE_TRANS, INTER_COMM,
        INTER_IDEMPOT, INTER_SUBSET, .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INTER, LAMBDA_BETA, LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY,
        MONO_EXISTS, MONO_FORALL, MONO_IMP, NOT_IMP, NOT_IN_EMPTY,
        .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_NOT_LE, RIGHT_FORALL_IMP_THM, SKOLEM_THM, SUBSET, SUBSET_INTER, SUBSET_TRANS,
        .. } := D.ra.ts.cn.cx.cvx.core5
  let { o_THM, SWAP_EXISTS_THM, .. } := D.ra.ts.cn.cx.cvx.core6
  let { HULL_HULL, HULL_INC, HULL_P, HULL_SUBSET, .. } := D.ra.ts.cn.cx.cvx.misc
  let { VEC_COMPONENT, VECTOR_ADD_COMPONENT, VECTOR_NEG_COMPONENT,
        .. } := D.ra.ts.cn.cx.cvx.vec4
  let { CLOSED_INTER, CLOSED_INTERVAL, CLOSEST_POINT_IN_SET, CLOSEST_POINT_SELF,
        .. } := D.ra.ts.cn.cx.cvx.top1
  let { CLOSURE_INTERVAL, COMPACT_IMP_BOUNDED, COMPACT_IMP_CLOSED,
        .. } := D.ra.ts.cn.cx.cvx.top2
  let { CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_CONST, CONTINUOUS_ON_SUBSET,
        .. } := D.ra.ts.cn.cx.cvx.top3
  let { frontier, .. } := D.ra.ts.cn.cx.cvx.top5
  let { AFFINE_BOUNDED_EQ_LOWDIM, CLOSEST_POINT_IN_RELATIVE_FRONTIER,
        CONTINUOUS_ON_CLOSEST_POINT, CONVEX_INTERVAL, RELATIVE_FRONTIER_EQ_EMPTY,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qconvex
  let { RELATIVE_FRONTIER_CONVEX_INTER_AFFINE, .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths2
  let { CONTINUOUS_ON_EMPTY, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { SUBSET_INTERVAL, .. } := D.ra.ts.cn.ms.ig.dv.dg.qvec
  let { DISJOINT_EMPTY, REAL_WLOG_LT, UNIONS_1, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qses
  let { AFF_DIM_AFFINE_HULL, AFF_DIM_EQ_0, AFF_DIM_EQ_MINUS1, AFF_DIM_GE, AFF_DIM_SUBSET,
        AFFINE_AFFINE_HULL, AFFINE_IMP_CONVEX, CLOSED_AFFINE,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx1
  let { CONVEX_INTER, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  let { RELATIVE_INTERIOR_SUBSET, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx3
  -- @@SCOPE END

  let EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_SIMPLE ← (do
    let lemma ← prove
     r"!f:A->B->bool P k.
          INFINITE {x | P x} /\ FINITE k /\
          (!x y. P x /\ P y /\ ~(x = y) ==> DISJOINT (f x) (f y))
          ==> ?x. P x /\ DISJOINT k (f x)"
     (REWRITE_TAC [INFINITE] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC [← SET_RULE (← q r"(?x. P x /\ DISJOINT k (f x)) <=>
                            ~(!x. ?y. P x ==> y IN k /\ y IN f x)")] THEN
      REWRITE_TAC [SKOLEM_THM] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"g:A->B")) THEN
      MP_TAC (← ISPECL [← q r"g:A->B", ← q r"{x:A | P x}"] FINITE_IMAGE_INJ_EQ) THEN
      ASM_REWRITE_TAC [IN_ELIM_THM, NOT_IMP] THEN
      CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
        (← REWRITE_RULE [IMP_CONJ] FINITE_SUBSET)) THEN
      ASM SET_TAC [])
    prove
     r"!f:real^M->real^N s t u.
          compact s /\ convex u /\ bounded u /\ aff_dim t <= aff_dim u /\
          s SUBSET t /\ f continuous_on s /\ IMAGE f s SUBSET relative_frontier u
          ==> ?k g. FINITE k /\ k SUBSET t /\ DISJOINT k s /\
                    g continuous_on (t DIFF k) /\
                    IMAGE g (t DIFF k) SUBSET relative_frontier u /\
                    !x. x IN s ==> g x = f x"
     (SUBGOAL_THEN
       (← q r"!f:real^M->real^N s t u.
          compact s /\ convex u /\ bounded u /\ aff_dim t <= aff_dim u /\
          s SUBSET t /\ f continuous_on s /\ IMAGE f s SUBSET relative_frontier u
          ==> ?k g. FINITE k /\ DISJOINT k s /\
                    g continuous_on (t DIFF k) /\
                    IMAGE g (t DIFF k) SUBSET relative_frontier u /\
                    !x. x IN s ==> g x = f x")
      MP_TAC THENL
       [ALL_TAC,
        REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
        DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
        ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"g:real^M->real^N") THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"k:real^M->bool") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"k INTER t:real^M->bool") THEN
        ASM_SIMP_TAC [FINITE_INTER, INTER_SUBSET] THEN
        REPEAT CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC, ASM SET_TAC []] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
                CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC []] THEN
      SUBGOAL_THEN
       (← q r"!f:real^M->real^N s t u.
          compact s /\ s SUBSET t /\ affine t /\
          convex u /\ bounded u /\ aff_dim t <= aff_dim u /\
          f continuous_on s /\ IMAGE f s SUBSET relative_frontier u
          ==> ?k g. FINITE k /\ DISJOINT k s /\
                    g continuous_on (t DIFF k) /\
                    IMAGE g (t DIFF k) SUBSET relative_frontier u /\
                    !x. x IN s ==> g x = f x")
      ASSUME_TAC THENL
       [ALL_TAC,
        REPEAT STRIP_TAC THEN
        SUBGOAL_THEN
         (← q r"?k g. FINITE k /\ DISJOINT k s /\
              g continuous_on (affine hull t DIFF k) /\
              IMAGE g (affine hull t DIFF k) SUBSET relative_frontier u /\
              !x. x IN s ==> g x = (f:real^M->real^N) x")
        MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_SIMP_TAC [AFF_DIM_AFFINE_HULL, AFFINE_AFFINE_HULL] THEN
          TRANS_TAC SUBSET_TRANS (← q r"t:real^M->bool") THEN
          ASM_REWRITE_TAC [HULL_SUBSET],
          REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
          STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
          CONJ_TAC THENL
           [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
                CONTINUOUS_ON_SUBSET)),
            FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT]
                SUBSET_TRANS)) THEN
            MATCH_MP_TAC IMAGE_SUBSET] THEN
          MATCH_MP_TAC (← SET_RULE (← q r"s SUBSET t ==> s DIFF k SUBSET t DIFF k")) THEN
          REWRITE_TAC [HULL_SUBSET]]] THEN
      REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"s:real^M->bool = {}") THENL
       [ASM_CASES_TAC (← q r"relative_frontier(u:real^N->bool) = {}") THENL
         [RULE_ASSUM_TAC (REWRITE_RULE [RELATIVE_FRONTIER_EQ_EMPTY]) THEN
          UNDISCH_TAC (← q r"bounded(u:real^N->bool)") THEN
          ASM_SIMP_TAC [AFFINE_BOUNDED_EQ_LOWDIM] THEN DISCH_TAC THEN
          SUBGOAL_THEN (← q r"aff_dim(t:real^M->bool) <= &0") MP_TAC THENL
           [ASM_INT_ARITH_TAC, ALL_TAC] THEN
          SIMP_TAC [AFF_DIM_GE, ← INT_ARITH
           (← q r"--(&1):int <= x ==> (x <= &0 <=> x = --(&1) \/ x = &0)")] THEN
          REWRITE_TAC [AFF_DIM_EQ_MINUS1, AFF_DIM_EQ_0] THEN
          DISCH_THEN (DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_TAC (← q r"a:real^M"))) THEN
          EXISTS_TAC (← q r"{a:real^M}") THEN
          ASM_REWRITE_TAC [DISJOINT_EMPTY, FINITE_SING, NOT_IN_EMPTY,
                           EMPTY_DIFF, DIFF_EQ_EMPTY, IMAGE_CLAUSES,
                           CONTINUOUS_ON_EMPTY, EMPTY_SUBSET],
          EXISTS_TAC (← q r"{}:real^M->bool") THEN
          FIRST_X_ASSUM (X_CHOOSE_TAC (← q r"y:real^N") o
            GEN_REWRITE_RULE id [← GSYM MEMBER_NOT_EMPTY]) THEN
          ASM_SIMP_TAC [FINITE_EMPTY, DISJOINT_EMPTY, NOT_IN_EMPTY, DIFF_EMPTY] THEN
          EXISTS_TAC (← q r"(\x. y):real^M->real^N") THEN
          REWRITE_TAC [CONTINUOUS_ON_CONST] THEN ASM SET_TAC []],
        ALL_TAC] THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
      DISCH_THEN (MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL_SYMMETRIC) THEN
      REWRITE_TAC [INSERT_SUBSET] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"b:real^M") STRIP_ASSUME_TAC) THEN
      MP_TAC (← ISPECL
       [← q r"f:real^M->real^N",
        ← q r"{interval[--(b + vec 1):real^M,b + vec 1] INTER t}",
        ← q r"s:real^M->bool", ← q r"u:real^N->bool"]
       EXTEND_MAP_CELL_COMPLEX_TO_SPHERE_COFINITE) THEN
      SUBGOAL_THEN
       (← q r"interval[--b,b] SUBSET interval[--(b + vec 1):real^M,b + vec 1]")
      ASSUME_TAC THENL
       [REWRITE_TAC [SUBSET_INTERVAL, VECTOR_ADD_COMPONENT, VECTOR_NEG_COMPONENT,
                     VEC_COMPONENT] THEN
        REAL_ARITH_TAC,
        ALL_TAC] THEN
      ASM_REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FINITE_SING] THEN
      REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY, IMP_IMP] THEN
      REWRITE_TAC [INTER_IDEMPOT, UNIONS_1, FACE_OF_REFL_EQ, SUBSET_INTER] THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC [HULL_SUBSET, COMPACT_IMP_CLOSED] THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN
          ASM_SIMP_TAC [POLYTOPE_INTERVAL, AFFINE_IMP_POLYHEDRON],
          TRANS_TAC INT_LE_TRANS (← q r"aff_dim(t:real^M->bool)") THEN
          ASM_SIMP_TAC [AFF_DIM_SUBSET, INTER_SUBSET],
          ASM_SIMP_TAC [CONVEX_INTER, CONVEX_INTERVAL, AFFINE_IMP_CONVEX],
          ASM SET_TAC []],
        REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN
      MAP_EVERY X_GEN_TAC [← q r"k:real^M->bool", ← q r"g:real^M->real^N"] THEN
      STRIP_TAC THEN EXISTS_TAC (← q r"k:real^M->bool") THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN
       (← q r"?d:real. (&1 / &2 <= d /\ d <= &1) /\
               DISJOINT k (frontier(interval[--(b + lambda i. d):real^M,
                                               (b + lambda i. d)]))")
      STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC lemma THEN
        ASM_SIMP_TAC [INFINITE, FINITE_REAL_INTERVAL, REAL_NOT_LE] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC REAL_WLOG_LT THEN REWRITE_TAC [] THEN
        CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
        MAP_EVERY X_GEN_TAC [← q r"x:real", ← q r"y:real"] THEN REPEAT STRIP_TAC THEN
        REWRITE_TAC [frontier] THEN MATCH_MP_TAC (← SET_RULE
         (← q r"c SUBSET i' ==> DISJOINT (c DIFF i) (c' DIFF i')")) THEN
        REWRITE_TAC [INTERIOR_INTERVAL, CLOSURE_INTERVAL] THEN
        SIMP_TAC [SUBSET_INTERVAL, VECTOR_NEG_COMPONENT, VECTOR_ADD_COMPONENT,
                  LAMBDA_BETA] THEN
        ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      ABBREV_TAC (← q r"c:real^M = b + lambda i. d") THEN SUBGOAL_THEN
       (← q r"interval[--b:real^M,b] SUBSET interval(--c,c) /\
        interval[--b:real^M,b] SUBSET interval[--c,c] /\
        interval[--c,c] SUBSET interval[--(b + vec 1):real^M,b + vec 1]")
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC [SUBSET_INTERVAL] THEN EXPAND_TAC "c" THEN REPEAT CONJ_TAC THEN
        SIMP_TAC [VECTOR_NEG_COMPONENT, VECTOR_ADD_COMPONENT, LAMBDA_BETA] THEN
        MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
        REWRITE_TAC [VEC_COMPONENT] THEN ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      EXISTS_TAC
       (← q r"(g:real^M->real^N) o
        closest_point (interval[--c,c] INTER t)") THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_CLOSEST_POINT THEN
          ASM_SIMP_TAC [CONVEX_INTER, CLOSED_INTER, CLOSED_INTERVAL, CLOSED_AFFINE,
            AFFINE_IMP_CONVEX, AFFINE_AFFINE_HULL, CONVEX_INTERVAL] THEN
          ASM SET_TAC [],
          FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
              CONTINUOUS_ON_SUBSET))],
        REWRITE_TAC [IMAGE_o] THEN
        FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT]
            SUBSET_TRANS)) THEN
        MATCH_MP_TAC IMAGE_SUBSET,
        X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN REWRITE_TAC [o_THM] THEN
        TRANS_TAC EQ_TRANS (← q r"(g:real^M->real^N) x") THEN
        CONJ_TAC THENL [AP_TERM_TAC, ASM SET_TAC []] THEN
        MATCH_MP_TAC CLOSEST_POINT_SELF THEN
        ASM_SIMP_TAC [IN_INTER, HULL_INC] THEN ASM SET_TAC []] THEN
      (REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_DIFF] THEN
       X_GEN_TAC (← q r"x:real^M") THEN STRIP_TAC THEN CONJ_TAC THENL
        [MATCH_MP_TAC (← SET_RULE
          (← q r"closest_point s x IN s /\ s SUBSET u ==> closest_point s x IN u")) THEN
         CONJ_TAC THENL [MATCH_MP_TAC CLOSEST_POINT_IN_SET, ASM SET_TAC []] THEN
         ASM_SIMP_TAC [CLOSED_INTER, CLOSED_INTERVAL, CLOSED_AFFINE] THEN
         ASM SET_TAC [],
         ALL_TAC] THEN
       ASM_CASES_TAC (← q r"x IN interval[--c:real^M,c]") THEN
       ASM_SIMP_TAC [CLOSEST_POINT_SELF, IN_INTER] THEN
       MATCH_MP_TAC (← SET_RULE
        (← q r"closest_point s x IN relative_frontier s /\
         DISJOINT k (relative_frontier s)
         ==> ~(closest_point s x IN k)")) THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC CLOSEST_POINT_IN_RELATIVE_FRONTIER THEN
         ASM_SIMP_TAC [CLOSED_INTER, CLOSED_AFFINE, CLOSED_INTERVAL] THEN
         CONJ_TAC THENL [ASM SET_TAC [], REWRITE_TAC [IN_DIFF]] THEN CONJ_TAC THENL
          [ALL_TAC, ASM_MESON_TAC [SUBSET, RELATIVE_INTERIOR_SUBSET, IN_INTER]] THEN
         ONCE_REWRITE_TAC [INTER_COMM] THEN
         W (MP_TAC o PART_MATCH (lhs o rand)
           AFFINE_HULL_CONVEX_INTER_NONEMPTY_INTERIOR o rand o snd) THEN
         ASM_SIMP_TAC [HULL_HULL, AFFINE_AFFINE_HULL, AFFINE_IMP_CONVEX] THEN
         ASM_SIMP_TAC [HULL_P] THEN ANTS_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
         REWRITE_TAC [INTERIOR_INTERVAL] THEN ASM SET_TAC [],
         W (MP_TAC o PART_MATCH (lhs o rand) RELATIVE_FRONTIER_CONVEX_INTER_AFFINE o
           rand o snd) THEN
         ANTS_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
         REWRITE_TAC [CONVEX_INTERVAL, AFFINE_AFFINE_HULL, INTERIOR_INTERVAL] THEN
         ASM SET_TAC []])))

  pure { EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_SIMPLE }
/- ------------------------------------------------------------------------- -/
/- Special cases and corollaries involving spheres: the general cofinite     -/
/- extension into a sphere.                                                  -/
/- (moretop.ml 2835-3471)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MOI where
  EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_GEN : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOI [HolBase] (D : MoreTopDeps) (BMOH : MOH) : ExceptT String IO MOI := do
  -- @@SCOPE BEGIN
  let { EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_SIMPLE, .. } := BMOH
  let { IN_COMPONENTS_SELF, .. } := D.qtopology
  let { CLOSED_IN_UNION_COMPLEMENT_COMPONENT, CLOSED_UNION_COMPLEMENT_COMPONENT,
        HOMEOMORPHISM_GROUPING_POINTS_EXISTS_GEN, .. } := D.qpaths
  let { AFFINE_HULL_CONVEX_INTER_NONEMPTY_INTERIOR, AFFINE_HULL_OPEN_IN,
        RELATIVE_INTERIOR_CONVEX_INTER_AFFINE, .. } := D.qconvex
  let { RELATIVE_FRONTIER_RETRACT_OF_PUNCTURED_AFFINE_HULL, retract_of, retraction,
        .. } := D.qdegree
  let { CLOSED_IN_UNIONS, .. } := D.qmetric
  let { FINITE_REAL_INTERVAL, .. } := D.ra.qsession
  let { BOUNDED_SUBSET_CLOSED_INTERVAL_SYMMETRIC, CONNECTED_SING,
        .. } := D.ra.ts.cn.ms.qtopology1
  let { ASM_INT_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INT_ARITH, MESON, MESON_TAC,
        REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV, SET_RULE, SET_TAC, .. } := D.ra.ts.cn.cx.cvx
  let { INFINITE, .. } := D.ra.ts.cn.cx.cpx
  let { BOUNDED_SING, INTERIOR_INTERVAL, .. } := D.ra.ts.cn.ms.ig.qtopology
  let { CONJ_ASSOC, DIFF_EMPTY, DIFF_EQ_EMPTY, EMPTY_DIFF, EMPTY_SUBSET, EMPTY_UNIONS,
        EQ_TRANS, EXISTS_IN_IMAGE, FINITE_EMPTY, FINITE_IMAGE, FINITE_IMAGE_INJ_EQ,
        FINITE_INTER, FINITE_SING, FINITE_SUBSET, FINITE_UNIONS, FORALL_IN_GSPEC,
        .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, IMAGE_CLAUSES, IMAGE_o, IMAGE_SUBSET, IMP_CONJ, IMP_CONJ_ALT,
        IN_DELETE, IN_DIFF, INSERT_SUBSET, INTER_COMM, INTER_SUBSET, INTER_UNIONS,
        .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INTER, IN_UNION, IN_UNIONS, IN_UNIV, LAMBDA_BETA,
        LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY, MONO_EXISTS,
        MONO_FORALL, MONO_IMP, NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY,
        NOT_INSERT_EMPTY, .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_NOT_LE, RIGHT_EXISTS_AND_THM, RIGHT_EXISTS_IMP_THM, RIGHT_IMP_EXISTS_THM,
        SIMPLE_IMAGE, SIMPLE_IMAGE_GEN, SKOLEM_THM, SUBSET, SUBSET_DIFF, SUBSET_TRANS,
        SUBSET_UNION, .. } := D.ra.ts.cn.cx.cvx.core5
  let { o_THM, SUBSET_UNIV, SWAP_EXISTS_THM, UNION_SUBSET, UNIONS_GSPEC, UNIONS_SUBSET,
        .. } := D.ra.ts.cn.cx.cvx.core6
  let { HULL_HULL, HULL_INC, HULL_MINIMAL, HULL_P, HULL_SUBSET,
        .. } := D.ra.ts.cn.cx.cvx.misc
  let { VEC_COMPONENT, VECTOR_ADD_COMPONENT, VECTOR_NEG_COMPONENT,
        .. } := D.ra.ts.cn.cx.cvx.vec4
  let { CLOSED_IN_DIFF, OPEN_IN_DIFF, OPEN_IN_SUBSET_TRANS, OPEN_IN_TRANS,
        SUBTOPOLOGY_UNIV, .. } := D.ra.ts.cn.cx.cvx.met
  let { BALL_SUBSET_CBALL, BOUNDED_CBALL, BOUNDED_SUBSET, CENTRE_IN_BALL, CLOSED_CBALL,
        CLOSED_IN, CLOSED_IN_CLOSED, CLOSED_INTER, CLOSED_INTERVAL, CLOSEST_POINT_IN_SET,
        CLOSEST_POINT_SELF, .. } := D.ra.ts.cn.cx.cvx.top1
  let { CLOSURE_INTERVAL, COMPACT_IMP_BOUNDED, COMPACT_IMP_CLOSED, COMPONENTS_EQ,
        .. } := D.ra.ts.cn.cx.cvx.top2
  let { CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID, CONTINUOUS_ON_SUBSET,
        FRONTIER_CBALL, .. } := D.ra.ts.cn.cx.cvx.top3
  let { IN_COMPONENTS_CONNECTED, IN_COMPONENTS_SUBSET, INTERIOR_CBALL, OPEN_BALL,
        .. } := D.ra.ts.cn.cx.cvx.top4
  let { frontier, homeomorphism, OPEN_IN_OPEN_INTER, OPEN_IN_REFL,
        TOPSPACE_EUCLIDEAN_SUBTOPOLOGY, UNIONS_COMPONENTS, .. } := D.ra.ts.cn.cx.cvx.top5
  let { CBALL_DIFF_BALL, .. } := D.ra.ts.cn.ms.ig.dv.qtopology1
  let { AFFINE_BOUNDED_EQ_LOWDIM, AFFINE_HULL_AFFINE_INTER_NONEMPTY_INTERIOR,
        CLOSEST_POINT_IN_RELATIVE_FRONTIER, CONTINUOUS_ON_CLOSEST_POINT, CONVEX_INTERVAL,
        RELATIVE_FRONTIER_EQ_EMPTY, .. } := D.ra.ts.cn.ms.ig.dv.dg.qconvex
  let { CLOSED_IN_IMP_SUBSET, CLOSED_IN_SUBSET_TRANS, PASTING_LEMMA_EXISTS_CLOSED,
        SUBTOPOLOGY_SUBTOPOLOGY, .. } := D.ra.ts.cn.ms.ig.dv.dg.qmetric
  let { CONVEX_IMP_LOCALLY_CONNECTED, .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths1
  let { OPEN_IN_COMPONENTS_LOCALLY_CONNECTED, RELATIVE_FRONTIER_CONVEX_INTER_AFFINE,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths2
  let { BALL_UNION_SPHERE, CONTINUOUS_MAP_EUCLIDEAN, CONTINUOUS_ON_CASES_LOCAL,
        CONTINUOUS_ON_EMPTY, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { LOCALLY_OPEN_SUBSET, OPEN_CLOSED, OPEN_IN_CONTAINS_CBALL,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology2
  let { SUBSET_INTERVAL, .. } := D.ra.ts.cn.ms.ig.dv.dg.qvec
  let { DISJOINT_EMPTY, EMPTY_UNION, REAL_WLOG_LT, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qses
  let { OPEN_IN_UNIONS, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qmet
  let { BOUNDED_INTERVAL, CLOSED_IN_REFL, OPEN_IN_DELETE,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qtop
  let { AFF_DIM_EQ_0, AFF_DIM_EQ_MINUS1, AFF_DIM_GE, AFFINE_AFFINE_HULL, AFFINE_IMP_CONVEX,
        CLOSED_AFFINE, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx1
  let { CONVEX_CBALL, CONVEX_INTER, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  let { RELATIVE_INTERIOR_SUBSET, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx3
  -- @@SCOPE END

  let EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_GEN ← (do
    let lemma0 ← prove
     r"!u t s v. closed_in (subtopology euclidean u) v /\ t SUBSET u /\
                 s = v INTER t
                 ==> closed_in (subtopology euclidean t) s"
     (REPEAT GEN_TAC THEN REWRITE_TAC [CLOSED_IN_CLOSED, LEFT_AND_EXISTS_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN SET_TAC [])
    let lemma1 ← prove
     r"!f:A->B->bool P k.
          INFINITE {x | P x} /\ FINITE k /\
          (!x y. P x /\ P y /\ ~(x = y) ==> DISJOINT (f x) (f y))
          ==> ?x. P x /\ DISJOINT k (f x)"
     (REWRITE_TAC [INFINITE] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC [← SET_RULE (← q r"(?x. P x /\ DISJOINT k (f x)) <=>
                            ~(!x. ?y. P x ==> y IN k /\ y IN f x)")] THEN
      REWRITE_TAC [SKOLEM_THM] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"g:A->B")) THEN
      MP_TAC (← ISPECL [← q r"g:A->B", ← q r"{x:A | P x}"] FINITE_IMAGE_INJ_EQ) THEN
      ASM_REWRITE_TAC [IN_ELIM_THM, NOT_IMP] THEN
      CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
        (← REWRITE_RULE [IMP_CONJ] FINITE_SUBSET)) THEN
      ASM SET_TAC [])
    let lemma2 ← prove
     r"!f:real^M->real^N s t k p u.
            FINITE k /\ affine u /\
            f continuous_on ((u:real^M->bool) DIFF k) /\
            IMAGE f ((u:real^M->bool) DIFF k) SUBSET t /\
            (!c. c IN components((u:real^M->bool) DIFF s) /\ ~(c INTER k = {})
                 ==> ~(c INTER p = {})) /\
            closed_in (subtopology euclidean u) s /\ DISJOINT k s /\ k SUBSET u
            ==> ?g. g continuous_on ((u:real^M->bool) DIFF p) /\
                    IMAGE g ((u:real^M->bool) DIFF p) SUBSET t /\
                    !x. x IN s ==> g x = f x"
     (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"k:real^M->bool = {}") THENL
       [ASM_REWRITE_TAC [DIFF_EMPTY] THEN REPEAT STRIP_TAC THEN
        EXISTS_TAC (← q r"f:real^M->real^N") THEN REWRITE_TAC [] THEN CONJ_TAC THENL
         [ASM_MESON_TAC [CONTINUOUS_ON_SUBSET, SUBSET_DIFF], ASM SET_TAC []],
        STRIP_TAC] THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP CLOSED_IN_IMP_SUBSET) THEN
      SUBGOAL_THEN (← q r"~(((u:real^M->bool) DIFF s) INTER k = {})") MP_TAC THENL
       [ASM SET_TAC [], ALL_TAC] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o LAND_CONV)
       [UNIONS_COMPONENTS] THEN
      REWRITE_TAC [INTER_UNIONS, EMPTY_UNIONS, FORALL_IN_GSPEC] THEN
      REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"co:real^M->bool") THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"locally connected (u:real^M->bool)") ASSUME_TAC THENL
       [ASM_SIMP_TAC [AFFINE_IMP_CONVEX, CONVEX_IMP_LOCALLY_CONNECTED],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!c. c IN components ((u:real^M->bool) DIFF s) /\ ~(c INTER k = {})
            ==> ?a g. a IN c /\ a IN p /\
                      g continuous_on (s UNION (c DELETE a)) /\
                      IMAGE g (s UNION (c DELETE a)) SUBSET t /\
                      !x. x IN s ==> g x = (f:real^M->real^N) x")
      MP_TAC THENL
       [X_GEN_TAC (← q r"c:real^M->bool") THEN STRIP_TAC THEN
        FIRST_ASSUM (ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"c:real^M->bool")) THEN
        ASM_REWRITE_TAC [] THEN REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_INTER] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:real^M") THEN
        STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN (← q r"open_in (subtopology euclidean u) (c:real^M->bool)")
        MP_TAC THENL
         [MATCH_MP_TAC OPEN_IN_TRANS THEN
          EXISTS_TAC (← q r"u DIFF s:real^M->bool") THEN
          ASM_SIMP_TAC [OPEN_IN_DIFF, OPEN_IN_REFL] THEN
          MATCH_MP_TAC OPEN_IN_COMPONENTS_LOCALLY_CONNECTED THEN
          ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
          EXISTS_TAC (← q r"u:real^M->bool") THEN
          ASM_SIMP_TAC [OPEN_IN_DIFF, OPEN_IN_REFL],
          DISCH_THEN (fun th => ASSUME_TAC th THEN MP_TAC th)] THEN
        REWRITE_TAC [OPEN_IN_CONTAINS_CBALL] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC (← q r"a:real^M"))) THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN (← q r"ball(a:real^M,d) INTER u SUBSET c") ASSUME_TAC THENL
         [ASM_MESON_TAC [BALL_SUBSET_CBALL, SUBSET_TRANS,
                         ← SET_RULE (← q r"b SUBSET c ==> b INTER u SUBSET c INTER u")],
          ALL_TAC] THEN
        MP_TAC (← ISPECL
        [← q r"ball(a:real^M,d) INTER u", ← q r"c:real^M->bool",
          ← q r"s UNION c:real^M->bool", ← q r"c INTER k:real^M->bool"]
            HOMEOMORPHISM_GROUPING_POINTS_EXISTS_GEN) THEN
        ASM_REWRITE_TAC [INTER_SUBSET, SUBSET_UNION, UNION_SUBSET] THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
            EXISTS_TAC (← q r"u:real^M->bool") THEN
            ASM_SIMP_TAC [HULL_MINIMAL, HULL_SUBSET],
            MP_TAC (← ISPECL [← q r"c:real^M->bool", ← q r"u:real^M->bool"]
               AFFINE_HULL_OPEN_IN) THEN
            ASM_SIMP_TAC [HULL_P] THEN ASM SET_TAC [],
            REWRITE_TAC [HULL_SUBSET],
            ASM_MESON_TAC [IN_COMPONENTS_CONNECTED],
            ASM_MESON_TAC [FINITE_SUBSET, INTER_SUBSET],
            MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
            EXISTS_TAC (← q r"u:real^M->bool") THEN
            ASM_REWRITE_TAC [] THEN
            ASM_MESON_TAC [OPEN_IN_OPEN_INTER, OPEN_BALL, INTER_COMM],
            REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_INTER] THEN
            EXISTS_TAC (← q r"a:real^M") THEN REWRITE_TAC [CENTRE_IN_BALL] THEN
            ASM SET_TAC []],
          REWRITE_TAC [IN_INTER, LEFT_IMP_EXISTS_THM]] THEN
        MAP_EVERY X_GEN_TAC [← q r"h:real^M->real^M", ← q r"k:real^M->real^M"] THEN
        REWRITE_TAC [homeomorphism] THEN STRIP_TAC THEN
        MP_TAC (← ISPECL [← q r"cball(a:real^M,d) INTER u", ← q r"a:real^M"]
            RELATIVE_FRONTIER_RETRACT_OF_PUNCTURED_AFFINE_HULL) THEN
        MP_TAC (← ISPECL [← q r"cball(a:real^M,d)", ← q r"u:real^M->bool"]
            RELATIVE_INTERIOR_CONVEX_INTER_AFFINE) THEN
        MP_TAC (← ISPECL [← q r"cball(a:real^M,d)", ← q r"u:real^M->bool"]
            RELATIVE_FRONTIER_CONVEX_INTER_AFFINE) THEN
        MP_TAC (← ISPECL [← q r"u:real^M->bool", ← q r"cball(a:real^M,d)"]
            (← ONCE_REWRITE_RULE [INTER_COMM]
               AFFINE_HULL_AFFINE_INTER_NONEMPTY_INTERIOR)) THEN
        ASM_SIMP_TAC [CONVEX_CBALL, FRONTIER_CBALL, INTERIOR_CBALL] THEN
        SUBGOAL_THEN (← q r"a IN ball(a:real^M,d) INTER u") ASSUME_TAC THENL
         [ASM_REWRITE_TAC [CENTRE_IN_BALL, IN_INTER] THEN ASM SET_TAC [],
          ALL_TAC] THEN
        REPLICATE_TAC 3
         (ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN SUBST1_TAC]) THEN
        ASM_SIMP_TAC [CONVEX_INTER, CONVEX_CBALL, AFFINE_IMP_CONVEX] THEN
        ANTS_TAC THENL
         [ASM_MESON_TAC [BOUNDED_SUBSET, INTER_SUBSET, BOUNDED_CBALL],
          ALL_TAC] THEN
        ASM_REWRITE_TAC [retract_of, retraction] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"r:real^M->real^M") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC
         (← q r"(f:real^M->real^N) o (k:real^M->real^M) o
          (\x. if x IN ball(a,d) then r x else x)") THEN
        REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL
         [ALL_TAC,
          X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN REWRITE_TAC [o_THM] THEN
          COND_CASES_TAC THENL
           [ASM SET_TAC [], AP_TERM_TAC THEN ASM SET_TAC []]] THEN
        ABBREV_TAC (← q r"j = \x:real^M. if x IN ball(a,d) then r x else x") THEN
        SUBGOAL_THEN
         (← q r"(j:real^M->real^M) continuous_on ((u:real^M->bool) DELETE a)")
        ASSUME_TAC THENL
         [EXPAND_TAC "j" THEN
          SUBGOAL_THEN
           (← q r"u DELETE (a:real^M) =
            (cball(a,d) DELETE a) INTER u UNION
            ((u:real^M->bool) DIFF ball(a,d))")
           (fun th => tactic_of do pure (SUBST1_TAC th THEN
                      MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
                      SUBST1_TAC (← SYM th)))
          THENL
           [MP_TAC (← ISPECL [← q r"a:real^M", ← q r"d:real"] BALL_SUBSET_CBALL) THEN
            ASM SET_TAC [],
            ALL_TAC] THEN
          REWRITE_TAC [IN_DIFF, IN_INTER, IN_DELETE, CONTINUOUS_ON_ID] THEN
          REPEAT CONJ_TAC THENL
           [ALL_TAC, ALL_TAC,
            FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
              CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC [],
            REWRITE_TAC [← GSYM BALL_UNION_SPHERE] THEN ASM SET_TAC []] THEN
          REWRITE_TAC [CLOSED_IN_CLOSED] THENL
           [EXISTS_TAC (← q r"cball(a:real^M,d)") THEN REWRITE_TAC [CLOSED_CBALL],
            EXISTS_TAC (← q r"(:real^M) DIFF ball(a,d)") THEN
            REWRITE_TAC [← GSYM OPEN_CLOSED, OPEN_BALL]] THEN
          MP_TAC (← ISPECL [← q r"a:real^M", ← q r"d:real"] BALL_SUBSET_CBALL) THEN
          MP_TAC (← ISPECL [← q r"a:real^M", ← q r"d:real"] CENTRE_IN_BALL) THEN
          ASM SET_TAC [],
          ALL_TAC] THEN
        SUBGOAL_THEN
         (← q r"IMAGE (j:real^M->real^M) (s UNION c DELETE a) SUBSET
          (s UNION c DIFF ball(a,d))")
        ASSUME_TAC THENL
         [EXPAND_TAC "j" THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
          X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN
          COND_CASES_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
          SUBGOAL_THEN (← q r"(r:real^M->real^M) x IN sphere(a,d)") MP_TAC THENL
           [MP_TAC (← ISPECL [← q r"a:real^M", ← q r"d:real"] CENTRE_IN_BALL) THEN
            ASM SET_TAC [],
            REWRITE_TAC [← GSYM CBALL_DIFF_BALL] THEN ASM SET_TAC []],
          ALL_TAC] THEN
        CONJ_TAC THENL
         [REPEAT (MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC) THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
              CONTINUOUS_ON_SUBSET))
          THENL [ASM SET_TAC [], ASM SET_TAC [], ALL_TAC],
          ONCE_REWRITE_TAC [IMAGE_o] THEN FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
           (← SET_RULE (← q r"IMAGE f u SUBSET t
                      ==> s SUBSET u ==> IMAGE f s SUBSET t")))] THEN
        REWRITE_TAC [IMAGE_o] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
          (← q r"s SUBSET u ==> IMAGE f u SUBSET t ==> IMAGE f s SUBSET t"))) THEN
        REWRITE_TAC [SUBSET, IN_UNIV, IN_DIFF, FORALL_IN_IMAGE] THEN
        ASM SET_TAC [],
        ALL_TAC] THEN
      GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
      REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC
       [← q r"a:(real^M->bool)->real^M", ← q r"h:(real^M->bool)->real^M->real^N"] THEN
      DISCH_TAC THEN MP_TAC (← ISPECL
       [← q r"subtopology euclidean
          (s UNION UNIONS
           { c DELETE (a c) |
             c IN components ((u:real^M->bool) DIFF s) /\ ~(c INTER k = {})})",
        ← q r"euclidean:(real^N)topology",
        ← q r"h:(real^M->bool)->real^M->real^N",
        ← q r"\c:real^M->bool. s UNION (c DELETE (a c))",
        ← q r"{c | c IN components ((u:real^M->bool) DIFF s) /\ ~(c INTER k = {})}"]
       PASTING_LEMMA_EXISTS_CLOSED) THEN
      REWRITE_TAC [CONTINUOUS_MAP_EUCLIDEAN, TOPSPACE_EUCLIDEAN_SUBTOPOLOGY,
                   SUBTOPOLOGY_SUBTOPOLOGY] THEN
      ONCE_REWRITE_TAC [← TAUT (← q r"closed_in a b /\ c <=> ~(closed_in a b ==> ~c)")] THEN
      SIMP_TAC [← ISPEC (← q r"euclidean") CLOSED_IN_IMP_SUBSET,
                ← SET_RULE (← q r"s SUBSET u ==> u INTER s = s")] THEN
      REWRITE_TAC [NOT_IMP] THEN
      SUBGOAL_THEN
       (← q r"FINITE {c | c IN components((u:real^M->bool) DIFF s) /\
                    ~(c INTER k = {})}")
      ASSUME_TAC THENL
       [MP_TAC (← ISPECL
         [← q r"\c:real^M->bool. c INTER k",
          ← q r"{c | c IN components ((u:real^M->bool) DIFF s) /\ ~(c INTER k = {})}"]
         FINITE_IMAGE_INJ_EQ) THEN
        REWRITE_TAC [IN_ELIM_THM] THEN ANTS_TAC THENL
         [MESON_TAC [COMPONENTS_EQ,
                     ← SET_RULE
                       (← q r"s INTER k = t INTER k /\ ~(s INTER k = {})
                        ==> ~(s INTER t = {})")],
          DISCH_THEN (SUBST1_TAC o SYM) THEN
          REWRITE_TAC [← GSYM SIMPLE_IMAGE, IN_ELIM_THM]] THEN
        MP_TAC (← ISPEC
         (← q r"{c INTER k |c| c IN components((u:real^M->bool) DIFF s) /\
                         ~(c INTER k = {})}")
          FINITE_UNIONS) THEN
        MATCH_MP_TAC (← TAUT (← q r"p ==> (p <=> q /\ r) ==> q")) THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          FINITE_SUBSET)) THEN
        REWRITE_TAC [UNIONS_GSPEC] THEN ASM SET_TAC [],
        ALL_TAC] THEN
      ASM_REWRITE_TAC [IN_ELIM_THM, SUBSET_UNIV] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [REWRITE_TAC [UNIONS_GSPEC] THEN ASM SET_TAC [],
          X_GEN_TAC (← q r"c:real^M->bool") THEN DISCH_TAC THEN ASM_SIMP_TAC [] THEN
          MATCH_MP_TAC lemma0 THEN
          MAP_EVERY EXISTS_TAC [← q r"u:real^M->bool", ← q r"s UNION c:real^M->bool"] THEN
          REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC CLOSED_IN_UNION_COMPLEMENT_COMPONENT THEN
            ASM_REWRITE_TAC [],
            ASM_REWRITE_TAC [UNION_SUBSET, UNIONS_SUBSET, FORALL_IN_GSPEC] THEN
            MESON_TAC [IN_COMPONENTS_SUBSET,
                       ← SET_RULE (← q r"c SUBSET u DIFF s ==> c DELETE a SUBSET u")],
            ASM_SIMP_TAC [CLOSED_UNION_COMPLEMENT_COMPONENT, UNIONS_GSPEC] THEN
            MATCH_MP_TAC (← SET_RULE
             (← q r"~(a IN t) /\ c DELETE a SUBSET t
              ==> s UNION c DELETE a = (s UNION c) INTER (s UNION t)")) THEN
            CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
            REWRITE_TAC [IN_ELIM_THM, IN_DELETE] THEN
            DISCH_THEN (X_CHOOSE_THEN (← q r"c':real^M->bool") STRIP_ASSUME_TAC) THEN
            MP_TAC (← ISPECL [← q r"(u:real^M->bool) DIFF s",
                             ← q r"c:real^M->bool", ← q r"c':real^M->bool"]
              COMPONENTS_EQ) THEN
            ASM_CASES_TAC (← q r"c':real^M->bool = c") THENL
             [ASM_MESON_TAC [], ALL_TAC] THEN
            ASM SET_TAC []],
          MAP_EVERY X_GEN_TAC
           [← q r"c1:real^M->bool", ← q r"c2:real^M->bool", ← q r"x:real^M"] THEN
          STRIP_TAC THEN ASM_CASES_TAC (← q r"c2:real^M->bool = c1") THEN
          ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MP_TAC o MATCH_MP (← SET_RULE
            (← q r"x IN u INTER (s UNION c1 DELETE a) INTER (s UNION c2 DELETE b)
             ==> (c1 INTER c2 = {}) ==> x IN s"))) THEN
          ANTS_TAC THENL [ASM_MESON_TAC [COMPONENTS_EQ], ASM_SIMP_TAC []]],
        DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^M->real^N") STRIP_ASSUME_TAC)] THEN
      MP_TAC
       (← ISPECL [← q r"\x. x IN s UNION
                          UNIONS {c | c IN components((u:real^M->bool) DIFF s) /\
                                      c INTER k = {}}",
                ← q r"f:real^M->real^N",
                ← q r"g:real^M->real^N",
                ← q r"s UNION
                 UNIONS {c | c IN components((u:real^M->bool) DIFF s) /\
                             c INTER k = {}}",
                ← q r"s UNION
                 UNIONS { c DELETE (a c) |
                          c IN components((u:real^M->bool) DIFF s) /\
                          ~(c INTER k = {})}"]
            CONTINUOUS_ON_CASES_LOCAL) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC lemma0 THEN EXISTS_TAC (← q r"u:real^M->bool") THEN
          EXISTS_TAC (← q r"u DIFF
                      UNIONS {c DELETE a c |
                              c IN components ((u:real^M->bool) DIFF s) /\
                              ~(c INTER k = {})}") THEN
          REPEAT CONJ_TAC THENL
            [MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC [CLOSED_IN_REFL] THEN
             MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC [FORALL_IN_GSPEC] THEN
             X_GEN_TAC (← q r"c:real^M->bool") THEN DISCH_TAC THEN
             MATCH_MP_TAC OPEN_IN_DELETE THEN MATCH_MP_TAC OPEN_IN_TRANS THEN
             EXISTS_TAC (← q r"u DIFF s:real^M->bool") THEN
             ASM_SIMP_TAC [OPEN_IN_DIFF, OPEN_IN_REFL] THEN
             MATCH_MP_TAC OPEN_IN_COMPONENTS_LOCALLY_CONNECTED THEN
             ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
             EXISTS_TAC (← q r"u:real^M->bool") THEN
             ASM_SIMP_TAC [OPEN_IN_DIFF, OPEN_IN_REFL],
             ASM_REWRITE_TAC [UNION_SUBSET] THEN
             REWRITE_TAC [UNIONS_SUBSET, IN_ELIM_THM] THEN
             MESON_TAC [IN_COMPONENTS_SUBSET,
                        ← SET_RULE (← q r"c SUBSET u DIFF s ==> c DELETE a SUBSET u /\
                                                        c SUBSET u")],
             REWRITE_TAC [← SET_RULE
              (← q r"(s UNION t) UNION (s UNION u) = (s UNION t) UNION u")] THEN
             MATCH_MP_TAC (← SET_RULE
              (← q r"s SUBSET u /\ t INTER s = {}
               ==> s = (u DIFF t) INTER (s UNION t)")) THEN
             CONJ_TAC THENL
              [ASM_REWRITE_TAC [UNION_SUBSET] THEN
               REWRITE_TAC [UNIONS_SUBSET, IN_ELIM_THM] THEN
               MESON_TAC [IN_COMPONENTS_SUBSET,
                          ← SET_RULE (← q r"c SUBSET u DIFF s ==> c DELETE a SUBSET u /\
                                                          c SUBSET u")],
               ALL_TAC] THEN
             REWRITE_TAC [EMPTY_UNION, ← SET_RULE
              (← q r"c INTER (s UNION t) = (s INTER c) UNION (c INTER t)")] THEN
             CONJ_TAC THENL
              [MATCH_MP_TAC (← SET_RULE
                (← q r"t SUBSET UNIV DIFF s ==> s INTER t = {}")) THEN
               REWRITE_TAC [UNIONS_SUBSET, FORALL_IN_GSPEC] THEN GEN_TAC THEN
               DISCH_THEN (CONJUNCTS_THEN2
                 (MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)
                 MP_TAC) THEN ASM SET_TAC [],
               REWRITE_TAC [INTER_UNIONS, EMPTY_UNIONS, FORALL_IN_GSPEC] THEN
               X_GEN_TAC (← q r"c:real^M->bool") THEN STRIP_TAC THEN
               X_GEN_TAC (← q r"c':real^M->bool") THEN STRIP_TAC THEN
               MP_TAC (← ISPECL [← q r"(u:real^M->bool) DIFF s",
                                ← q r"c:real^M->bool", ← q r"c':real^M->bool"]
                 COMPONENTS_EQ) THEN
               ASM_CASES_TAC (← q r"c':real^M->bool = c") THENL
                [ASM_MESON_TAC [], ASM SET_TAC []]]],
          MATCH_MP_TAC lemma0 THEN EXISTS_TAC (← q r"u:real^M->bool") THEN
          EXISTS_TAC
           (← q r"UNIONS {s UNION c |c| c IN components ((u:real^M->bool) DIFF s) /\
                                  ~(c INTER k = {})}") THEN
          REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC CLOSED_IN_UNIONS THEN REWRITE_TAC [FORALL_IN_GSPEC] THEN
            ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
            ASM_SIMP_TAC [FINITE_IMAGE] THEN REPEAT STRIP_TAC THEN
            MATCH_MP_TAC CLOSED_IN_UNION_COMPLEMENT_COMPONENT THEN
            ASM_REWRITE_TAC [],
            ASM_REWRITE_TAC [UNION_SUBSET] THEN
            REWRITE_TAC [UNIONS_SUBSET, IN_ELIM_THM] THEN
            MESON_TAC [IN_COMPONENTS_SUBSET,
                       ← SET_RULE (← q r"c SUBSET u DIFF s ==> c DELETE a SUBSET u /\
                                                       c SUBSET u")],
            MATCH_MP_TAC (← SET_RULE
             (← q r"t SUBSET u /\ u INTER s SUBSET t ==> t = u INTER (s UNION t)")) THEN
            CONJ_TAC THENL
             [REWRITE_TAC [UNIONS_GSPEC] THEN ASM SET_TAC [], ALL_TAC] THEN
            MATCH_MP_TAC (← SET_RULE
             (← q r"u INTER t SUBSET s ==> u INTER (s UNION t) SUBSET s UNION v")) THEN
            MATCH_MP_TAC (← SET_RULE
            (← q r"((UNIV DIFF s) INTER t) INTER u SUBSET s
             ==> t INTER u SUBSET s")) THEN
            GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o TOP_DEPTH_CONV)
             [INTER_UNIONS] THEN
            REWRITE_TAC [← SET_RULE
             (← q r"{g x | x IN {f y | P y}} = {g(f y) | P y}")] THEN
            REWRITE_TAC [← SET_RULE
             (← q r"(UNIV DIFF s) INTER (s UNION c) = c DIFF s")] THEN
            REWRITE_TAC [← SET_RULE
             (← q r"t INTER u SUBSET s <=> t INTER ((UNIV DIFF s) INTER u) = {}")] THEN
            ONCE_REWRITE_TAC [INTER_UNIONS] THEN
            REWRITE_TAC [EMPTY_UNIONS, FORALL_IN_GSPEC, INTER_UNIONS] THEN
            X_GEN_TAC (← q r"c:real^M->bool") THEN STRIP_TAC THEN
            X_GEN_TAC (← q r"c':real^M->bool") THEN STRIP_TAC THEN
            MP_TAC (← ISPECL [← q r"(u:real^M->bool) DIFF s",
                 ← q r"c:real^M->bool", ← q r"c':real^M->bool"]
              COMPONENTS_EQ) THEN
            ASM_CASES_TAC (← q r"c':real^M->bool = c") THENL
             [ASM_MESON_TAC [], ASM SET_TAC []]],
          FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
          REWRITE_TAC [UNION_SUBSET] THEN
          CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
          REWRITE_TAC [UNIONS_SUBSET, IN_ELIM_THM] THEN
          GEN_TAC THEN
          DISCH_THEN (CONJUNCTS_THEN2 (MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)
            MP_TAC) THEN ASM SET_TAC [],
          REWRITE_TAC [← TAUT (← q r"p /\ ~p <=> F")] THEN X_GEN_TAC (← q r"x:real^M") THEN
          REWRITE_TAC [IN_UNION] THEN
          ASM_CASES_TAC (← q r"(x:real^M) IN s") THEN ASM_REWRITE_TAC [] THENL
           [ASM SET_TAC [], ALL_TAC] THEN
          REWRITE_TAC [UNIONS_GSPEC, IN_ELIM_THM, IN_DELETE] THEN
          DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"c:real^M->bool"))
            (X_CHOOSE_TAC (← q r"c':real^M->bool"))) THEN
          MP_TAC (← ISPECL [← q r"(u:real^M->bool) DIFF s",
                           ← q r"c:real^M->bool", ← q r"c':real^M->bool"]
              COMPONENTS_EQ) THEN
          ASM_CASES_TAC (← q r"c':real^M->bool = c") THENL
           [ASM_MESON_TAC [], ASM SET_TAC []]],
        MATCH_MP_TAC (← MESON [CONTINUOUS_ON_SUBSET]
         (← q r"t SUBSET s /\ P f
          ==> f continuous_on s ==> ?g. g continuous_on t /\ P g")) THEN
        REWRITE_TAC [] THEN CONJ_TAC THENL
         [REWRITE_TAC [← SET_RULE
           (← q r"(s UNION t) UNION (s UNION u) = s UNION (t UNION u)")] THEN
          MATCH_MP_TAC (← SET_RULE
           (← q r"(u DIFF s) DIFF p SUBSET t
            ==> u DIFF p SUBSET s UNION t")) THEN
          GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [UNIONS_COMPONENTS] THEN
          REWRITE_TAC [UNIONS_GSPEC] THEN ASM SET_TAC [],
          SIMP_TAC [IN_UNION]] THEN
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_DIFF, IN_UNION, IN_UNIV] THEN
        X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN
        ASM_CASES_TAC (← q r"(x:real^M) IN s") THENL [ASM SET_TAC [], ALL_TAC] THEN
        ASM_REWRITE_TAC [IN_UNIONS, IN_ELIM_THM] THEN COND_CASES_TAC THENL
         [ASM SET_TAC [], ALL_TAC] THEN
        SUBGOAL_THEN
          (← q r"x IN ((u:real^M->bool) DIFF s)") MP_TAC THENL
            [ASM SET_TAC [], ALL_TAC] THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [UNIONS_COMPONENTS] THEN
        REWRITE_TAC [IN_UNIONS] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"c:real^M->bool") STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [NOT_EXISTS_THM]) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"c:real^M->bool")) THEN ASM_REWRITE_TAC [] THEN
        DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPECL [← q r"x:real^M", ← q r"c:real^M->bool"]) THEN
        ASM_REWRITE_TAC [UNIONS_GSPEC] THEN ASM SET_TAC []])
    let lemma3 ← prove
     r"!f:real^M->real^N s t u p.
            compact s /\ convex u /\ bounded u /\
            affine t /\ aff_dim t <= aff_dim u /\ s SUBSET t /\
            f continuous_on s /\ IMAGE f s SUBSET relative_frontier u /\
            (!c. c IN components(t DIFF s) ==> ~(c INTER p = {}))
            ==> ?k g. FINITE k /\ k SUBSET p /\ k SUBSET t /\ DISJOINT k s /\
                      g continuous_on (t DIFF k) /\
                      IMAGE g (t DIFF k) SUBSET relative_frontier u /\
                      !x. x IN s ==> g x = f x"
     (REPEAT STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"f:real^M->real^N", ← q r"s:real^M->bool",
                       ← q r"t:real^M->bool", ← q r"u:real^N->bool"]
            EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_SIMPLE) THEN
      ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"k:real^M->bool", ← q r"g:real^M->real^N"] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"!x. ?y. x IN k
                ==> ?c. c IN components (t DIFF s:real^M->bool) /\
                        x IN c /\ y IN c /\ y IN p")
      MP_TAC THENL
       [X_GEN_TAC (← q r"x:real^M") THEN REWRITE_TAC [RIGHT_EXISTS_IMP_THM] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN (← q r"(x:real^M) IN (t DIFF s)") MP_TAC THENL
         [ASM SET_TAC [], ALL_TAC] THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [UNIONS_COMPONENTS] THEN
        ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
        REWRITE_TAC [IN_UNIONS, RIGHT_EXISTS_AND_THM] THEN
        MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC [],
        REWRITE_TAC [SKOLEM_THM] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"h:real^M->real^M") (LABEL_TAC "*"))] THEN
      EXISTS_TAC (← q r"IMAGE (h:real^M->real^M) k") THEN
      MP_TAC (← ISPECL
       [← q r"g:real^M->real^N", ← q r"s:real^M->bool",
        ← q r"relative_frontier u:real^N->bool", ← q r"k:real^M->bool",
        ← q r"IMAGE (h:real^M->real^M) k", ← q r"t:real^M->bool"] lemma2) THEN
      ASM_SIMP_TAC [AFFINE_AFFINE_HULL, FINITE_IMAGE] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [X_GEN_TAC (← q r"c:real^M->bool") THEN STRIP_TAC THEN
          FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [← GSYM MEMBER_NOT_EMPTY]) THEN
          ONCE_REWRITE_TAC [INTER_COMM] THEN
          REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, EXISTS_IN_IMAGE, IN_INTER] THEN
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"x:real^M") THEN
          STRIP_TAC THEN REMOVE_THEN "*" (MP_TAC o SPEC (← q r"x:real^M")) THEN
          ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
          X_GEN_TAC (← q r"c':real^M->bool") THEN STRIP_TAC THEN
          MP_TAC (← ISPECL [← q r"(t:real^M->bool) DIFF s",
                           ← q r"c:real^M->bool", ← q r"c':real^M->bool"]
            COMPONENTS_EQ) THEN
          ASM_CASES_TAC (← q r"c':real^M->bool = c") THENL [ALL_TAC, ASM SET_TAC []] THEN
          ASM_REWRITE_TAC [] THEN ASM SET_TAC [],
          MATCH_MP_TAC CLOSED_IN_SUBSET_TRANS THEN
          EXISTS_TAC (← q r"(:real^M)") THEN
          ASM_REWRITE_TAC [SUBTOPOLOGY_UNIV, ← GSYM CLOSED_IN] THEN
          ASM_SIMP_TAC [COMPACT_IMP_CLOSED, SUBSET_UNIV]],
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"h:real^M->real^N") THEN
        STRIP_TAC THEN ASM_SIMP_TAC [] THEN
        REWRITE_TAC [← SET_RULE (← q r"DISJOINT s t <=> !x. x IN s ==> ~(x IN t)")] THEN
        ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
        ASM_MESON_TAC [IN_COMPONENTS_SUBSET, SUBSET, IN_DIFF]])
    prove
     r"!f:real^M->real^N s t u p.
          compact s /\ convex u /\ bounded u /\
          affine t /\ aff_dim t <= aff_dim u /\ s SUBSET t /\
          f continuous_on s /\ IMAGE f s SUBSET relative_frontier u /\
          (!c. c IN components(t DIFF s) /\ bounded c ==> ~(c INTER p = {}))
          ==> ?k g. FINITE k /\ k SUBSET p /\ k SUBSET t /\ DISJOINT k s /\
                    g continuous_on (t DIFF k) /\
                    IMAGE g (t DIFF k) SUBSET relative_frontier u /\
                    !x. x IN s ==> g x = f x"
     (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"s:real^M->bool = {}") THENL
       [ASM_CASES_TAC (← q r"relative_frontier(u:real^N->bool) = {}") THENL
         [RULE_ASSUM_TAC (REWRITE_RULE [RELATIVE_FRONTIER_EQ_EMPTY]) THEN
          UNDISCH_TAC (← q r"bounded(u:real^N->bool)") THEN
          ASM_SIMP_TAC [AFFINE_BOUNDED_EQ_LOWDIM] THEN DISCH_TAC THEN
          SUBGOAL_THEN (← q r"aff_dim(t:real^M->bool) <= &0") MP_TAC THENL
           [ASM_INT_ARITH_TAC, ALL_TAC] THEN
          SIMP_TAC [AFF_DIM_GE, ← INT_ARITH
           (← q r"--(&1):int <= x ==> (x <= &0 <=> x = --(&1) \/ x = &0)")] THEN
          REWRITE_TAC [AFF_DIM_EQ_MINUS1, AFF_DIM_EQ_0] THEN
          DISCH_THEN (DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_TAC (← q r"a:real^M"))) THENL
           [EXISTS_TAC (← q r"{}:real^M->bool") THEN
            ASM_REWRITE_TAC [EMPTY_DIFF, FINITE_EMPTY, CONTINUOUS_ON_EMPTY,
                             IMAGE_CLAUSES, NOT_IN_EMPTY] THEN
            SET_TAC [],
            FIRST_X_ASSUM (MP_TAC o SPEC (← q r"{a:real^M}")) THEN
            ASM_REWRITE_TAC [DIFF_EMPTY, IN_COMPONENTS_SELF] THEN
            REWRITE_TAC [CONNECTED_SING, NOT_INSERT_EMPTY, BOUNDED_SING] THEN
            DISCH_TAC THEN EXISTS_TAC (← q r"{a:real^M}") THEN
            ASM_REWRITE_TAC [DIFF_EQ_EMPTY, CONTINUOUS_ON_EMPTY, NOT_IN_EMPTY,
                             FINITE_SING, IMAGE_CLAUSES, EMPTY_SUBSET] THEN
            ASM SET_TAC []],
          EXISTS_TAC (← q r"{}:real^M->bool") THEN
          FIRST_X_ASSUM (X_CHOOSE_TAC (← q r"y:real^N") o
            GEN_REWRITE_RULE id [← GSYM MEMBER_NOT_EMPTY]) THEN
          ASM_SIMP_TAC [FINITE_EMPTY, DISJOINT_EMPTY, NOT_IN_EMPTY, DIFF_EMPTY] THEN
          EXISTS_TAC (← q r"(\x. y):real^M->real^N") THEN
          REWRITE_TAC [CONTINUOUS_ON_CONST] THEN ASM SET_TAC []],
        ALL_TAC] THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
      DISCH_THEN (MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL_SYMMETRIC) THEN
      REWRITE_TAC [INSERT_SUBSET] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"b:real^M") STRIP_ASSUME_TAC) THEN
      MP_TAC (← ISPECL
       [← q r"f:real^M->real^N", ← q r"s:real^M->bool",
        ← q r"t:real^M->bool", ← q r"u:real^N->bool",
        ← q r"p UNION (UNIONS {c | c IN components (t DIFF s) /\ ~bounded c} DIFF
                  interval[--(b + vec 1):real^M,b + vec 1])"]
            lemma3) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [X_GEN_TAC (← q r"c:real^M->bool") THEN STRIP_TAC THEN
        ASM_CASES_TAC (← q r"bounded(c:real^M->bool)") THENL
         [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"c:real^M->bool")) THEN
          ASM_REWRITE_TAC [] THEN ASM SET_TAC [],
          ALL_TAC] THEN
        SUBGOAL_THEN
         (← q r"~(c SUBSET interval[--(b + vec 1):real^M,b + vec 1])")
        MP_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
        ASM_MESON_TAC [BOUNDED_SUBSET, BOUNDED_INTERVAL],
        ALL_TAC] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"k:real^M->bool", ← q r"g:real^M->real^N"] THEN
      STRIP_TAC THEN
      EXISTS_TAC (← q r"k INTER interval[--(b + vec 1):real^M,b + vec 1]") THEN
      ASM_SIMP_TAC [FINITE_INTER, RIGHT_EXISTS_AND_THM] THEN
      REPEAT (CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN
      SUBGOAL_THEN
       (← q r"interval[--b,b] SUBSET interval[--(b + vec 1):real^M,b + vec 1]")
      ASSUME_TAC THENL
       [REWRITE_TAC [SUBSET_INTERVAL, VECTOR_ADD_COMPONENT, VECTOR_NEG_COMPONENT,
                     VEC_COMPONENT] THEN
        REAL_ARITH_TAC,
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"?d:real. (&1 / &2 <= d /\ d <= &1) /\
               DISJOINT k (frontier(interval[--(b + lambda i. d):real^M,
                                               (b + lambda i. d)]))")
      STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC lemma1 THEN
        ASM_SIMP_TAC [INFINITE, FINITE_REAL_INTERVAL, REAL_NOT_LE] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC REAL_WLOG_LT THEN REWRITE_TAC [] THEN
        CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
        MAP_EVERY X_GEN_TAC [← q r"x:real", ← q r"y:real"] THEN REPEAT STRIP_TAC THEN
        REWRITE_TAC [frontier] THEN MATCH_MP_TAC (← SET_RULE
         (← q r"c SUBSET i' ==> DISJOINT (c DIFF i) (c' DIFF i')")) THEN
        REWRITE_TAC [INTERIOR_INTERVAL, CLOSURE_INTERVAL] THEN
        SIMP_TAC [SUBSET_INTERVAL, VECTOR_NEG_COMPONENT, VECTOR_ADD_COMPONENT,
                  LAMBDA_BETA] THEN
        ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      ABBREV_TAC (← q r"c:real^M = b + lambda i. d") THEN SUBGOAL_THEN
       (← q r"interval[--b:real^M,b] SUBSET interval(--c,c) /\
        interval[--b:real^M,b] SUBSET interval[--c,c] /\
        interval[--c,c] SUBSET interval[--(b + vec 1):real^M,b + vec 1]")
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC [SUBSET_INTERVAL] THEN EXPAND_TAC "c" THEN REPEAT CONJ_TAC THEN
        SIMP_TAC [VECTOR_NEG_COMPONENT, VECTOR_ADD_COMPONENT, LAMBDA_BETA] THEN
        MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
        REWRITE_TAC [VEC_COMPONENT] THEN ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      EXISTS_TAC
       (← q r"(g:real^M->real^N) o
        closest_point (interval[--c,c] INTER t)") THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_CLOSEST_POINT THEN
          ASM_SIMP_TAC [CONVEX_INTER, CLOSED_INTER, CLOSED_INTERVAL, CLOSED_AFFINE,
            AFFINE_IMP_CONVEX, AFFINE_AFFINE_HULL, CONVEX_INTERVAL] THEN
          ASM SET_TAC [],
          FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
              CONTINUOUS_ON_SUBSET))],
        REWRITE_TAC [IMAGE_o] THEN
        FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT]
            SUBSET_TRANS)) THEN
        MATCH_MP_TAC IMAGE_SUBSET,
        X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN REWRITE_TAC [o_THM] THEN
        TRANS_TAC EQ_TRANS (← q r"(g:real^M->real^N) x") THEN
        CONJ_TAC THENL [AP_TERM_TAC, ASM SET_TAC []] THEN
        MATCH_MP_TAC CLOSEST_POINT_SELF THEN
        ASM_SIMP_TAC [IN_INTER, HULL_INC] THEN ASM SET_TAC []] THEN
      (REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_DIFF] THEN
       X_GEN_TAC (← q r"x:real^M") THEN STRIP_TAC THEN CONJ_TAC THENL
        [MATCH_MP_TAC (← SET_RULE
          (← q r"closest_point s x IN s /\ s SUBSET u ==> closest_point s x IN u")) THEN
         CONJ_TAC THENL [MATCH_MP_TAC CLOSEST_POINT_IN_SET, ASM SET_TAC []] THEN
         ASM_SIMP_TAC [CLOSED_INTER, CLOSED_INTERVAL, CLOSED_AFFINE] THEN
         ASM SET_TAC [],
         ALL_TAC] THEN
       ASM_CASES_TAC (← q r"x IN interval[--c:real^M,c]") THEN
       ASM_SIMP_TAC [CLOSEST_POINT_SELF, IN_INTER] THENL
        [ASM SET_TAC [], ALL_TAC] THEN
       MATCH_MP_TAC (← SET_RULE
        (← q r"closest_point s x IN relative_frontier s /\
         DISJOINT k (relative_frontier s)
         ==> ~(closest_point s x IN k)")) THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC CLOSEST_POINT_IN_RELATIVE_FRONTIER THEN
         ASM_SIMP_TAC [CLOSED_INTER, CLOSED_AFFINE, CLOSED_INTERVAL] THEN
         CONJ_TAC THENL [ASM SET_TAC [], REWRITE_TAC [IN_DIFF]] THEN CONJ_TAC THENL
          [ALL_TAC, ASM_MESON_TAC [SUBSET, RELATIVE_INTERIOR_SUBSET, IN_INTER]] THEN
         ONCE_REWRITE_TAC [INTER_COMM] THEN
         W (MP_TAC o PART_MATCH (lhs o rand)
           AFFINE_HULL_CONVEX_INTER_NONEMPTY_INTERIOR o rand o snd) THEN
         ASM_SIMP_TAC [HULL_HULL, AFFINE_AFFINE_HULL, AFFINE_IMP_CONVEX] THEN
         ASM_SIMP_TAC [HULL_P] THEN ANTS_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
         REWRITE_TAC [INTERIOR_INTERVAL] THEN ASM SET_TAC [],
         W (MP_TAC o PART_MATCH (lhs o rand) RELATIVE_FRONTIER_CONVEX_INTER_AFFINE o
           rand o snd) THEN
         ANTS_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
         REWRITE_TAC [CONVEX_INTERVAL, AFFINE_AFFINE_HULL, INTERIOR_INTERVAL] THEN
         ASM SET_TAC []])))

  pure { EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_GEN }
/- ------------------------------------------------------------------------- -/
/- Special cases and corollaries involving spheres: affine, universe and     -/
/- sphere-to-sphere extensions.                                              -/
/- (moretop.ml 3472-3623)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MOJ where
  EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE : thm
  EXTEND_MAP_UNIV_TO_SPHERE_COFINITE : thm
  EXTEND_MAP_UNIV_TO_SPHERE_NO_BOUNDED_COMPONENT : thm
  EXTEND_MAP_SPHERE_TO_SPHERE_GEN : thm
  EXTEND_MAP_SPHERE_TO_SPHERE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOJ [HolBase] (D : MoreTopDeps) (BMOG : MOG) (BMOI : MOI) : ExceptT String IO MOJ := do
  -- @@SCOPE BEGIN
  let { EXTEND_MAP_CELL_COMPLEX_TO_SPHERE, .. } := BMOG
  let { EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_GEN, .. } := BMOI
  let { CONTINUOUS_ON_SING, .. } := D.qtopology
  let { AFF_DIM_CBALL, BOUNDED_RELATIVE_FRONTIER,
        HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS, .. } := D.qconvex
  let { CHOOSE_POLYTOPE, FACE_OF_AFF_DIM_LT, FACE_OF_IMP_SUBSET, FACE_OF_INTER,
        FACE_OF_POLYTOPE_POLYTOPE, FACE_OF_SUBSET, FINITE_POLYTOPE_FACES,
        POLYTOPE_IMP_BOUNDED, POLYTOPE_IMP_CONVEX, POLYTOPE_IMP_POLYHEDRON,
        RELATIVE_FRONTIER_OF_POLYHEDRON_ALT, .. } := D.qpolytope
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON, MESON_TAC, SET_TAC,
        .. } := D.ra.ts.cn.cx.cvx
  let { DIFF_EMPTY, EMPTY_SUBSET, FINITE_EMPTY, FINITE_SUBSET,
        .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, IMAGE_CLAUSES, IMAGE_o, IMP_CONJ, IMP_CONJ_ALT, INT_OF_NUM_LE,
        INTER_SUBSET, .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, LEFT_IMP_EXISTS_THM, MONO_EXISTS, NOT_IN_EMPTY,
        .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_LE_REFL, .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_NOT_LE, REAL_NOT_LT, RIGHT_EXISTS_AND_THM, SUBSET_EMPTY,
        .. } := D.ra.ts.cn.cx.cvx.core5
  let { o_THM, SUBSET_UNIV, UNWIND_THM2, .. } := D.ra.ts.cn.cx.cvx.core6
  let { BOUNDED_CBALL, BOUNDED_SUBSET, .. } := D.ra.ts.cn.cx.cvx.top1
  let { COMPACT_CONTINUOUS_IMAGE, COMPACT_EQ_BOUNDED_CLOSED, COMPACT_IMP_CLOSED,
        .. } := D.ra.ts.cn.cx.cvx.top2
  let { CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_CONST, CONTINUOUS_ON_SUBSET,
        .. } := D.ra.ts.cn.cx.cvx.top3
  let { HOMEOMORPHISM, .. } := D.ra.ts.cn.cx.cvx.top4
  let { homeomorphic, SPHERE_EMPTY, .. } := D.ra.ts.cn.cx.cvx.top5
  let { RELATIVE_FRONTIER_CBALL, .. } := D.ra.ts.cn.ms.ig.dv.dg.qconvex
  let { CONTINUOUS_ON_EMPTY, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { SPHERE_EQ_EMPTY, SPHERE_SING, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology2
  let { DISJOINT_EMPTY, INT_LTE_TRANS, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qses
  let { AFF_DIM_GE, AFF_DIM_LE_UNIV, AFF_DIM_UNIV, AFFINE_UNIV,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx1
  let { CONVEX_CBALL, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  -- @@SCOPE END

  let EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE ← prove
   r"!f:real^M->real^N s t a r p.
        compact s /\ affine t /\ aff_dim t <= &(dimindex(:N)) /\ s SUBSET t /\
        &0 <= r /\ f continuous_on s /\ IMAGE f s SUBSET sphere(a,r) /\
        (!c. c IN components(t DIFF s) /\ bounded c ==> ~(c INTER p = {}))
        ==> ?k g. FINITE k /\ k SUBSET p /\ k SUBSET t /\ DISJOINT k s /\
                  g continuous_on (t DIFF k) /\
                  IMAGE g (t DIFF k) SUBSET sphere(a,r) /\
                  !x. x IN s ==> g x = f x"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"r = &0") THENL
     [ASM_SIMP_TAC [SPHERE_SING] THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"{}:real^M->bool") THEN
      EXISTS_TAC (← q r"(\x. a):real^M->real^N") THEN
      REWRITE_TAC [CONTINUOUS_ON_CONST, FINITE_EMPTY] THEN ASM SET_TAC [],
      MP_TAC (← ISPECL [← q r"a:real^N", ← q r"r:real"] RELATIVE_FRONTIER_CBALL) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      STRIP_TAC THEN MATCH_MP_TAC EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_GEN THEN
      ASM_REWRITE_TAC [CONVEX_CBALL, BOUNDED_CBALL, AFF_DIM_CBALL] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC])

  let EXTEND_MAP_UNIV_TO_SPHERE_COFINITE ← prove
   r"!f:real^M->real^N s a r p.
     dimindex(:M) <= dimindex(:N) /\ &0 <= r /\
     compact s /\ f continuous_on s /\ IMAGE f s SUBSET sphere(a,r) /\
     (!c. c IN components((:real^M) DIFF s) /\ bounded c
          ==> ~(c INTER p = {}))
     ==> ?k g. FINITE k /\ k SUBSET p /\ DISJOINT k s /\
               g continuous_on ((:real^M) DIFF k) /\
               IMAGE g ((:real^M) DIFF k) SUBSET sphere(a,r) /\
               !x. x IN s ==> g x = f x"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^M->real^N", ← q r"s:real^M->bool", ← q r"(:real^M)",
                     ← q r"a:real^N", ← q r"r:real", ← q r"p:real^M->bool"]
          EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE) THEN
    ASM_REWRITE_TAC [AFFINE_UNIV, SUBSET_UNIV, AFF_DIM_UNIV, INT_OF_NUM_LE])

  let EXTEND_MAP_UNIV_TO_SPHERE_NO_BOUNDED_COMPONENT ← prove
   r"!f:real^M->real^N s a r.
     dimindex(:M) <= dimindex(:N) /\ &0 <= r /\
     compact s /\ f continuous_on s /\ IMAGE f s SUBSET sphere(a,r) /\
     (!c. c IN components((:real^M) DIFF s) ==> ~bounded c)
     ==> ?g. g continuous_on (:real^M) /\
             IMAGE g (:real^M) SUBSET sphere(a,r) /\
             !x. x IN s ==> g x = f x"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^M->real^N", ← q r"s:real^M->bool", ← q r"a:real^N",
                     ← q r"r:real", ← q r"{}:real^M->bool"]
          EXTEND_MAP_UNIV_TO_SPHERE_COFINITE) THEN
    ASM_SIMP_TAC [IMP_CONJ, SUBSET_EMPTY, RIGHT_EXISTS_AND_THM] THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"p /\ q /\ r <=> q /\ p /\ r")] THEN
    REWRITE_TAC [UNWIND_THM2, FINITE_EMPTY, DISJOINT_EMPTY, DIFF_EMPTY] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [])

  let EXTEND_MAP_SPHERE_TO_SPHERE_GEN ← prove
   r"!f:real^M->real^N c s t.
        closed c /\ c SUBSET relative_frontier s /\ convex s /\ bounded s /\
        convex t /\ bounded t /\ aff_dim s <= aff_dim t /\
        f continuous_on c /\ IMAGE f c SUBSET relative_frontier t
         ==> ?g. g continuous_on (relative_frontier s) /\
                 IMAGE g (relative_frontier s) SUBSET relative_frontier t /\
                 !x. x IN c ==> g x = f x"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"?p:real^M->bool. polytope p /\ aff_dim p = aff_dim(s:real^M->bool)")
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC CHOOSE_POLYTOPE THEN
      ASM_REWRITE_TAC [AFF_DIM_GE, AFF_DIM_LE_UNIV],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"s:real^M->bool", ← q r"p:real^M->bool"]
          HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS) THEN
    ASM_SIMP_TAC [POLYTOPE_IMP_CONVEX, POLYTOPE_IMP_BOUNDED, homeomorphic] THEN
    REWRITE_TAC [HOMEOMORPHISM, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"h:real^M->real^M", ← q r"k:real^M->real^M"] THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL
     [← q r"(f:real^M->real^N) o (k:real^M->real^M)",
      ← q r"{f:real^M->bool | f face_of p /\ ~(f = p)}",
      ← q r"IMAGE (h:real^M->real^M) c",
      ← q r"t:real^N->bool"] EXTEND_MAP_CELL_COMPLEX_TO_SPHERE) THEN
    ASM_SIMP_TAC [FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC [← GSYM RELATIVE_FRONTIER_OF_POLYHEDRON_ALT,
                  POLYTOPE_IMP_POLYHEDRON] THEN
    REWRITE_TAC [IN_ELIM_THM, ← GSYM IMAGE_o, o_THM] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC (← q r"{f:real^M->bool | f face_of p}") THEN
        ASM_SIMP_TAC [FINITE_POLYTOPE_FACES] THEN SET_TAC [],
        ASM_MESON_TAC [FACE_OF_POLYTOPE_POLYTOPE,
                       FACE_OF_AFF_DIM_LT, POLYTOPE_IMP_CONVEX, INT_LTE_TRANS],
        ASM_MESON_TAC [FACE_OF_INTER, FACE_OF_SUBSET,
                       INTER_SUBSET, FACE_OF_INTER, FACE_OF_IMP_SUBSET],
        ASM SET_TAC [],
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
        CONJ_TAC THENL [ASM_MESON_TAC [CONTINUOUS_ON_SUBSET], ALL_TAC] THEN
        ASM_REWRITE_TAC [COMPACT_EQ_BOUNDED_CLOSED] THEN
        FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT]
          BOUNDED_SUBSET)) THEN
        ASM_SIMP_TAC [BOUNDED_RELATIVE_FRONTIER],
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
        ASM SET_TAC [],
        REWRITE_TAC [IMAGE_o] THEN ASM SET_TAC []],
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^M->real^N") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"(g:real^M->real^N) o (h:real^M->real^M)") THEN
      REWRITE_TAC [IMAGE_o, o_THM] THEN
      CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      ASM SET_TAC []])

  let EXTEND_MAP_SPHERE_TO_SPHERE ← prove
   r"!f:real^M->real^N c a r b s.
        dimindex(:M) <= dimindex(:N) /\ closed c /\ c SUBSET sphere(a,r) /\
        f continuous_on c /\ IMAGE f c SUBSET sphere(b,s) /\
        (&0 <= r /\ c = {} ==> &0 <= s)
        ==> ?g. g continuous_on sphere(a,r) /\
                IMAGE g (sphere(a,r)) SUBSET sphere(b,s) /\
                !x. x IN c ==> g x = f x"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"r < &0") THEN
    ASM_SIMP_TAC [SPHERE_EMPTY, NOT_IN_EMPTY, CONTINUOUS_ON_EMPTY,
                  IMAGE_CLAUSES, EMPTY_SUBSET]
    THENL [MESON_TAC [], ASM_REWRITE_TAC [← GSYM REAL_NOT_LT]] THEN
    ASM_CASES_TAC (← q r"sphere(b:real^N,s) = {}") THENL
     [FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [SPHERE_EQ_EMPTY]) THEN
      ASM SET_TAC [],
      FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [SPHERE_EQ_EMPTY])] THEN
    REWRITE_TAC [REAL_NOT_LE] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [REAL_NOT_LT]) THEN
    ASM_CASES_TAC (← q r"r = &0") THEN
    ASM_SIMP_TAC [SPHERE_SING, CONTINUOUS_ON_SING, REAL_LE_REFL] THENL
     [ASM_CASES_TAC (← q r"c:real^M->bool = {}") THENL
       [DISCH_THEN (K ALL_TAC) THEN MATCH_MP_TAC (← MESON []
         (← q r"(?c. P(\x. c)) ==> ?f. P f")) THEN ASM SET_TAC [],
        DISCH_TAC THEN EXISTS_TAC (← q r"f:real^M->real^N") THEN ASM SET_TAC []],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"s = &0") THENL
     [ASM_SIMP_TAC [SPHERE_SING] THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"(\x. b):real^M->real^N") THEN
      REWRITE_TAC [CONTINUOUS_ON_CONST] THEN ASM SET_TAC [],
      ALL_TAC] THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^M->real^N", ← q r"c:real^M->bool",
                     ← q r"cball(a:real^M,r)", ← q r"cball(b:real^N,s)"]
          EXTEND_MAP_SPHERE_TO_SPHERE_GEN) THEN
    ASM_REWRITE_TAC [CONVEX_CBALL, BOUNDED_CBALL, AFF_DIM_CBALL,
                     RELATIVE_FRONTIER_CBALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [INT_OF_NUM_LE]) THEN
    ASM_REAL_ARITH_TAC)

  pure { EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE, EXTEND_MAP_UNIV_TO_SPHERE_COFINITE,
         EXTEND_MAP_UNIV_TO_SPHERE_NO_BOUNDED_COMPONENT,
         EXTEND_MAP_SPHERE_TO_SPHERE_GEN, EXTEND_MAP_SPHERE_TO_SPHERE }
/- ------------------------------------------------------------------------- -/
/- Special cases and corollaries involving spheres: cofinite sphere-to-      -/
/- sphere extensions.                                                        -/
/- (moretop.ml 3624-4003)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MOK where
  EXTEND_MAP_SPHERE_TO_SPHERE_COFINITE_GEN : thm
  EXTEND_MAP_SPHERE_TO_SPHERE_COFINITE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOK [HolBase] (D : MoreTopDeps) (BMOI : MOI) : ExceptT String IO MOK := do
  -- @@SCOPE BEGIN
  let { EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_GEN, .. } := BMOI
  let { IN_COMPONENTS_SELF, .. } := D.qtopology
  let { HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN, PATH_CONNECTED_ARCWISE, .. } := D.qpaths
  let { AFF_DIM_CBALL, CHOOSE_AFFINE_SUBSET, .. } := D.qconvex
  let { LOCALLY_CONNECTED_SPHERE_GEN, LOCALLY_PATH_CONNECTED_SPHERE_GEN, .. } := D.qdegree
  let { CONNECTED_SING, .. } := D.ra.ts.cn.ms.qtopology1
  let { ASM_INT_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INT_ARITH, INT_ARITH_TAC,
        MESON, SET_RULE, SET_TAC, .. } := D.ra.ts.cn.cx.cvx
  let { DIST_REAL, .. } := D.ra.ts.cn.ms.ig.qvec
  let { DIFF_EMPTY, DIFF_EQ_EMPTY, DIMINDEX_GE_1, EMPTY_UNIONS, EXISTS_IN_IMAGE,
        FINITE_EMPTY, FINITE_IMAGE, FINITE_INSERT, FINITE_SING,
        .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, FUN_IN_IMAGE, IMAGE_CLAUSES, IMAGE_o, IMAGE_SUBSET, IMP_CONJ,
        IN_DELETE, IN_DIFF, INT_OF_NUM_ADD, INT_OF_NUM_LE, INTER_COMM,
        .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, IN_INTER, LE_REFL, LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM,
        MEMBER_NOT_EMPTY, MONO_EXISTS, NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY,
        .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_LE_REFL, .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_NOT_LT, SUBSET, SUBSET_RESTRICT, SUBSET_TRANS, .. } := D.ra.ts.cn.cx.cvx.core5
  let { o_THM, SUBSET_UNIV, .. } := D.ra.ts.cn.cx.cvx.core6
  let { DOT_BASIS, .. } := D.ra.ts.cn.cx.cvx.vec1
  let { DROP_EQ, DROP_VEC, LIFT_DROP, .. } := D.ra.ts.cn.cx.cvx.vec2
  let { drop, .. } := D.ra.ts.cn.cx.cvx.vec4
  let { OPEN_IN_DIFF, OPEN_IN_IMP_SUBSET, OPEN_IN_TRANS, .. } := D.ra.ts.cn.cx.cvx.met
  let { BOUNDED_CBALL, BOUNDED_SUBSET, CLOSED_SUBSET, .. } := D.ra.ts.cn.cx.cvx.top1
  let { CLOSURE_MINIMAL, CLOSURE_SUBSET, COMPACT_CLOSURE, COMPACT_CONTINUOUS_IMAGE,
        COMPACT_EQ_BOUNDED_CLOSED, COMPACT_IMP_CLOSED, COMPONENTS_MAXIMAL,
        CONNECTED_COMPONENT_MAXIMAL, CONNECTED_CONTINUOUS_IMAGE,
        .. } := D.ra.ts.cn.cx.cvx.top2
  let { CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_CONST, CONTINUOUS_ON_SUBSET,
        CONTINUOUS_OPEN_IN_PREIMAGE_GEN, .. } := D.ra.ts.cn.cx.cvx.top3
  let { IN_CBALL, IN_COMPONENTS_CONNECTED, IN_COMPONENTS_NONEMPTY, IN_COMPONENTS_SUBSET,
        IN_INTERVAL_1, .. } := D.ra.ts.cn.cx.cvx.top4
  let { homeomorphic, homeomorphism, OPEN_IN_REFL, SPHERE_EMPTY, UNIONS_COMPONENTS,
        .. } := D.ra.ts.cn.cx.cvx.top5
  let { CONNECTED_INTERVAL, .. } := D.ra.ts.cn.ms.ig.dv.qconvex
  let { COMPACT_RELATIVE_FRONTIER_BOUNDED, RELATIVE_FRONTIER_CBALL,
        RELATIVE_FRONTIER_EMPTY, .. } := D.ra.ts.cn.ms.ig.dv.dg.qconvex
  let { arc, OPEN_IN_COMPONENTS_LOCALLY_CONNECTED, path, PATH_CONNECTED_EQ_CONNECTED_LPC,
        path_image, pathfinish, pathstart, .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths2
  let { CONTINUOUS_ON_EMPTY, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { IN_COMPONENTS, LOCALLY_OPEN_SUBSET, OPEN_IN_CONTAINS_CBALL, SPHERE_EQ_EMPTY,
        SPHERE_SING, SUBSET_INTERVAL_1, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology2
  let { ENDS_IN_UNIT_INTERVAL, .. } := D.ra.ts.cn.ms.ig.dv.dg.qvec
  let { AFF_DIM_LE_UNIV, AFF_DIM_POS_LE, AFF_DIM_UNIV, AFFINE_UNIV, CLOSED_AFFINE,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx1
  let { CONVEX_CBALL, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  -- @@SCOPE END

  let EXTEND_MAP_SPHERE_TO_SPHERE_COFINITE_GEN ← prove
   r"!f:real^M->real^N s t u p.
        convex t /\ bounded t /\ convex u /\ bounded u /\
        aff_dim t <= aff_dim u + &1 /\
        closed s /\ s SUBSET relative_frontier t /\
        f continuous_on s /\ IMAGE f s SUBSET relative_frontier u /\
        (!c. c IN components(relative_frontier t DIFF s) ==> ~(c INTER p = {}))
        ==> ?k g. FINITE k /\ k SUBSET p /\
                  k SUBSET relative_frontier t /\ DISJOINT k s /\
                  g continuous_on (relative_frontier t DIFF k) /\
                  IMAGE g (relative_frontier t DIFF k) SUBSET
                  relative_frontier u /\
                  !x. x IN s ==> g x = f x"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"s = (relative_frontier t:real^M->bool)") THENL
     [ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [← q r"{}:real^M->bool", ← q r"f:real^M->real^N"] THEN
      ASM_REWRITE_TAC [FINITE_EMPTY, DIFF_EMPTY] THEN SET_TAC [],
      POP_ASSUM MP_TAC] THEN
    ASM_CASES_TAC (← q r"relative_frontier t:real^M->bool = {}") THENL
     [ASM SET_TAC [], REPEAT STRIP_TAC] THEN
    SUBGOAL_THEN
     (← q r"?c q:real^M. c IN components (relative_frontier t DIFF s) /\
                   q IN c /\ q IN relative_frontier t /\ ~(q IN s) /\ q IN p")
    STRIP_ASSUME_TAC THENL
     [MP_TAC (← ISPEC (← q r"(relative_frontier t:real^M->bool) DIFF s")
        UNIONS_COMPONENTS) THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← SET_RULE
       (← q r"s = u ==> ~(s = {}) ==> ~(u = {})"))) THEN
      ANTS_TAC THENL [ASM SET_TAC [], REWRITE_TAC [EMPTY_UNIONS]] THEN
      REWRITE_TAC [NOT_FORALL_THM, NOT_IMP] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"c:real^M->bool") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"c:real^M->bool")) THEN
      ASM_REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_INTER] THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [← GSYM IN_DIFF] THEN
      ASM_MESON_TAC [SUBSET, IN_COMPONENTS_SUBSET],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"?af. affine af /\ aff_dim(t:real^M->bool) = aff_dim(af:real^M->bool) + &1")
    STRIP_ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"(:real^M)", ← q r"aff_dim(t:real^M->bool) - &1"]
          CHOOSE_AFFINE_SUBSET) THEN
      REWRITE_TAC [SUBSET_UNIV, AFFINE_UNIV] THEN ANTS_TAC THENL
       [MATCH_MP_TAC (← INT_ARITH
         (← q r"&0:int <= t /\ t <= n ==> --a <= t - a /\ t - &1 <= n")) THEN
        REWRITE_TAC [AFF_DIM_LE_UNIV, AFF_DIM_UNIV, AFF_DIM_POS_LE] THEN
        ASM_MESON_TAC [RELATIVE_FRONTIER_EMPTY, NOT_IN_EMPTY],
        MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [] THEN INT_ARITH_TAC],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"t:real^M->bool", ← q r"af:real^M->bool", ← q r"q:real^M"]
          HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN) THEN
    ASM_REWRITE_TAC [homeomorphic, homeomorphism, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"h:real^M->real^M", ← q r"k:real^M->real^M"] THEN
    STRIP_TAC THEN MP_TAC (← ISPECL
     [← q r"(f:real^M->real^N) o (k:real^M->real^M)",
      ← q r"IMAGE (h:real^M->real^M) s",
      ← q r"(af:real^M->bool)",
      ← q r"u:real^N->bool",
      ← q r"IMAGE (h:real^M->real^M) (p INTER relative_frontier t DELETE q)"]
     EXTEND_MAP_AFFINE_TO_SPHERE_COFINITE_GEN) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
         [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
          ASM SET_TAC [],
          ASM_MESON_TAC [COMPACT_EQ_BOUNDED_CLOSED, BOUNDED_SUBSET,
                         COMPACT_RELATIVE_FRONTIER_BOUNDED]],
        ASM_INT_ARITH_TAC,
        ASM SET_TAC [],
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
        ASM SET_TAC [],
        REWRITE_TAC [IMAGE_o] THEN ASM SET_TAC [],
        X_GEN_TAC (← q r"l:real^M->bool") THEN STRIP_TAC THEN
        SUBGOAL_THEN (← q r"~(l:real^M->bool = {})") ASSUME_TAC THENL
         [ASM_MESON_TAC [IN_COMPONENTS_NONEMPTY], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"?x:real^M. x IN l") STRIP_ASSUME_TAC THENL
         [ASM SET_TAC [], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"l SUBSET af DIFF IMAGE (h:real^M->real^M) s")
        ASSUME_TAC THENL
         [ASM_MESON_TAC [IN_COMPONENTS_SUBSET], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"connected(l:real^M->bool)") ASSUME_TAC THENL
         [ASM_MESON_TAC [IN_COMPONENTS_CONNECTED], ALL_TAC] THEN
        SUBGOAL_THEN
         (← q r"?r. r IN components (relative_frontier t DIFF s) /\
              IMAGE (k:real^M->real^M) l SUBSET r")
        STRIP_ASSUME_TAC THENL
         [REWRITE_TAC [IN_COMPONENTS, LEFT_AND_EXISTS_THM] THEN
          EXISTS_TAC (← q r"connected_component (relative_frontier t DIFF s)
                                          ((k:real^M->real^M) x)") THEN
          EXISTS_TAC (← q r"(k:real^M->real^M) x") THEN REWRITE_TAC [] THEN
          CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
          MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
          ASM_SIMP_TAC [FUN_IN_IMAGE] THEN
          CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
          MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC [] THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
            CONTINUOUS_ON_SUBSET)) THEN
          ASM SET_TAC [],
          ALL_TAC] THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"r:real^M->bool")) THEN
        ASM_REWRITE_TAC [] THEN
        GEN_REWRITE_TAC LAND_CONV [← GSYM MEMBER_NOT_EMPTY] THEN
        REWRITE_TAC [LEFT_IMP_EXISTS_THM, IN_INTER] THEN
        X_GEN_TAC (← q r"z:real^M") THEN STRIP_TAC THEN
        SUBGOAL_THEN (← q r"r SUBSET ((relative_frontier t:real^M->bool) DIFF s)")
        ASSUME_TAC THENL [ASM_MESON_TAC [IN_COMPONENTS_SUBSET], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"connected(r:real^M->bool)") ASSUME_TAC THENL
         [ASM_MESON_TAC [IN_COMPONENTS_CONNECTED], ALL_TAC] THEN
        ASM_CASES_TAC (← q r"(q:real^M) IN r") THENL
         [ALL_TAC,
          REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN
          EXISTS_TAC (← q r"(h:real^M->real^M) z") THEN REWRITE_TAC [IN_INTER] THEN
          CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
          MATCH_MP_TAC (← SET_RULE (← q r"!s. x IN s /\ s SUBSET t ==> x IN t")) THEN
          EXISTS_TAC (← q r"IMAGE (h:real^M->real^M) r") THEN
          ASM_SIMP_TAC [FUN_IN_IMAGE] THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
          EXISTS_TAC (← q r"af DIFF IMAGE (h:real^M->real^M) s") THEN
          ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC [] THEN
            FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
              CONTINUOUS_ON_SUBSET)) THEN
            ASM SET_TAC [],
            REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_DIFF, IN_ELIM_THM] THEN
            X_GEN_TAC (← q r"y:real^M") THEN DISCH_TAC THEN
            CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
            REWRITE_TAC [← SET_RULE
             (← q r"~(h y IN IMAGE h s) <=> !y'. y' IN s ==> ~(h y = h y')")] THEN
            X_GEN_TAC (← q r"y':real^M") THEN DISCH_TAC THEN
            DISCH_THEN (MP_TAC o AP_TERM (← q r"k:real^M->real^M")) THEN
            MATCH_MP_TAC (← MESON []
             (← q r"k(h y) = y /\ k(h y') = y' /\ ~(y = y')
              ==> k(h y) = k(h y') ==> F")) THEN
            ASM SET_TAC [],
            ASM SET_TAC []]] THEN
        SUBGOAL_THEN
         (← q r"?n. open_in (subtopology euclidean (relative_frontier t)) n /\
              (q:real^M) IN n /\ n INTER IMAGE (k:real^M->real^M) l = {}")
        STRIP_ASSUME_TAC THENL
         [EXISTS_TAC (← q r"relative_frontier t DIFF
                      IMAGE (k:real^M->real^M) (closure l)") THEN
          SUBGOAL_THEN (← q r"closure l SUBSET (af:real^M->bool)") ASSUME_TAC THENL
           [MATCH_MP_TAC CLOSURE_MINIMAL THEN
            ASM_SIMP_TAC [CLOSED_AFFINE] THEN ASM SET_TAC [],
            ALL_TAC] THEN
          REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC [OPEN_IN_REFL] THEN
            MATCH_MP_TAC CLOSED_SUBSET THEN
            CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
            MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
            MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
            ASM_REWRITE_TAC [COMPACT_CLOSURE] THEN
            FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
              CONTINUOUS_ON_SUBSET)) THEN
            ASM SET_TAC [],
            ASM SET_TAC [],
            MP_TAC (← ISPEC (← q r"l:real^M->bool") CLOSURE_SUBSET) THEN SET_TAC []],
          ALL_TAC] THEN
        FIRST_ASSUM (ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
        SUBGOAL_THEN
         (← q r"?w. connected w /\ w SUBSET r DELETE q /\
              (k:real^M->real^M) x IN w /\ ~((n DELETE q) INTER w = {})")
        STRIP_ASSUME_TAC THENL
         [ALL_TAC,
          MATCH_MP_TAC (← TAUT (← q r"F ==> p")) THEN
          SUBGOAL_THEN (← q r"IMAGE (h:real^M->real^M) w SUBSET l") MP_TAC THENL
           [ALL_TAC, ASM SET_TAC []] THEN
          MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
          EXISTS_TAC (← q r"af DIFF IMAGE (h:real^M->real^M) s") THEN
          ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC [] THEN
            FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
              CONTINUOUS_ON_SUBSET)) THEN
            ASM SET_TAC [],
            REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_DIFF, IN_ELIM_THM] THEN
            X_GEN_TAC (← q r"y:real^M") THEN DISCH_TAC THEN
            CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
            REWRITE_TAC [← SET_RULE
             (← q r"~(h y IN IMAGE h s) <=> !y'. y' IN s ==> ~(h y = h y')")] THEN
            X_GEN_TAC (← q r"y':real^M") THEN DISCH_TAC THEN
            DISCH_THEN (MP_TAC o AP_TERM (← q r"k:real^M->real^M")) THEN
            MATCH_MP_TAC (← MESON []
             (← q r"k(h y) = y /\ k(h y') = y' /\ ~(y = y')
              ==> k(h y) = k(h y') ==> F")) THEN
            ASM SET_TAC [],
            ASM SET_TAC []]] THEN
        SUBGOAL_THEN (← q r"path_connected(r:real^M->bool)") MP_TAC THENL
         [W (MP_TAC o PART_MATCH (lhand o rand) PATH_CONNECTED_EQ_CONNECTED_LPC o
            snd) THEN
          ANTS_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
          MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
          EXISTS_TAC (← q r"(relative_frontier t:real^M->bool)") THEN
          ASM_SIMP_TAC [LOCALLY_PATH_CONNECTED_SPHERE_GEN] THEN
          MATCH_MP_TAC OPEN_IN_TRANS THEN
          EXISTS_TAC (← q r"(relative_frontier t:real^M->bool) DIFF s") THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC OPEN_IN_COMPONENTS_LOCALLY_CONNECTED THEN
            ASM_REWRITE_TAC [] THEN
            MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
            EXISTS_TAC (← q r"(relative_frontier t:real^M->bool)") THEN
            ASM_SIMP_TAC [LOCALLY_CONNECTED_SPHERE_GEN],
            ALL_TAC] THEN
          MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC [OPEN_IN_REFL] THEN
          MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC [],
          ALL_TAC] THEN
        REWRITE_TAC [PATH_CONNECTED_ARCWISE] THEN
        DISCH_THEN (MP_TAC o SPECL [← q r"(k:real^M->real^M) x", ← q r"q:real^M"]) THEN
        ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^1->real^M") STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC o
          GEN_REWRITE_RULE id [arc]) THEN
        DISCH_TAC THEN
        SUBGOAL_THEN
         (← q r"open_in (subtopology euclidean (interval[vec 0,vec 1]))
                  {x | x IN interval[vec 0,vec 1] /\
                       (g:real^1->real^M) x IN n}")
        MP_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
          EXISTS_TAC (← q r"(relative_frontier t:real^M->bool)") THEN
          ASM_REWRITE_TAC [← GSYM path, ← GSYM path_image] THEN
          ASM SET_TAC [],
          ALL_TAC] THEN
        REWRITE_TAC [OPEN_IN_CONTAINS_CBALL] THEN
        REWRITE_TAC [IN_ELIM_THM, SUBSET_RESTRICT] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"vec 1:real^1")) THEN
        REWRITE_TAC [ENDS_IN_UNIT_INTERVAL] THEN
        ANTS_TAC THENL [ASM_MESON_TAC [pathfinish], ALL_TAC] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"r:real")
          (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        ABBREV_TAC (← q r"t' = lift(&1 - min (&1 / &2) r)") THEN
        SUBGOAL_THEN (← q r"t' IN interval[vec 0:real^1,vec 1]") ASSUME_TAC THENL
         [EXPAND_TAC "t'" THEN SIMP_TAC [IN_INTERVAL_1, LIFT_DROP, DROP_VEC] THEN
          ASM_REAL_ARITH_TAC,
          ALL_TAC] THEN
        GEN_REWRITE_TAC LAND_CONV [SUBSET] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"t':real^1")) THEN
        ASM_REWRITE_TAC [IN_INTER, IN_ELIM_THM, IN_CBALL, DIST_REAL,
                         DROP_VEC, ← GSYM drop] THEN
        ANTS_TAC THENL
         [EXPAND_TAC "t'" THEN REWRITE_TAC [LIFT_DROP] THEN ASM_REAL_ARITH_TAC,
          DISCH_TAC] THEN
        EXISTS_TAC (← q r"IMAGE (g:real^1->real^M) (interval[vec 0,t'])") THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
          REWRITE_TAC [CONNECTED_INTERVAL] THEN
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC (← q r"interval[vec 0:real^1,vec 1]") THEN
          ASM_REWRITE_TAC [← GSYM path, SUBSET_INTERVAL_1] THEN
          ASM_REWRITE_TAC [REAL_LE_REFL, ← GSYM IN_INTERVAL_1],
          REWRITE_TAC [← SET_RULE
           (← q r"s SUBSET t DELETE q <=> s SUBSET t /\ !x. x IN s ==> ~(x = q)")] THEN
          CONJ_TAC THENL
           [TRANS_TAC SUBSET_TRANS
              (← q r"IMAGE (g:real^1->real^M) (interval[vec 0,vec 1])") THEN
            CONJ_TAC THENL
             [MATCH_MP_TAC IMAGE_SUBSET THEN
              ASM_REWRITE_TAC [REAL_LE_REFL, ← GSYM IN_INTERVAL_1,
                               SUBSET_INTERVAL_1],
              ASM_REWRITE_TAC [← GSYM path_image]],
            REWRITE_TAC [FORALL_IN_IMAGE] THEN
            X_GEN_TAC (← q r"t'':real^1") THEN DISCH_TAC THEN
            FIRST_X_ASSUM (fun th => tactic_of do
              pure (GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← SYM th])) THEN
            REWRITE_TAC [pathfinish] THEN DISCH_TAC THEN
            FIRST_X_ASSUM (MP_TAC o SPECL [← q r"t'':real^1", ← q r"vec 1:real^1"]) THEN
            ASM_REWRITE_TAC [← GSYM DROP_EQ] THEN
            UNDISCH_TAC (← q r"t'' IN interval[vec 0:real^1,t']") THEN
            EXPAND_TAC "t'" THEN
            REWRITE_TAC [IN_INTERVAL_1, DROP_VEC, LIFT_DROP] THEN
            ASM_REAL_ARITH_TAC],
          REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"vec 0:real^1") THEN
          CONJ_TAC THENL [ASM_MESON_TAC [pathstart], ALL_TAC] THEN
          EXPAND_TAC "t'" THEN
          REWRITE_TAC [IN_INTERVAL_1, DROP_VEC, LIFT_DROP] THEN
          ASM_REAL_ARITH_TAC,
          REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN
          ONCE_REWRITE_TAC [INTER_COMM] THEN
          REWRITE_TAC [EXISTS_IN_IMAGE, IN_INTER] THEN
          EXISTS_TAC (← q r"t':real^1") THEN CONJ_TAC THENL
           [EXPAND_TAC "t'" THEN
            REWRITE_TAC [IN_INTERVAL_1, DROP_VEC, LIFT_DROP] THEN
            ASM_REAL_ARITH_TAC,
            ASM_REWRITE_TAC [IN_DELETE] THEN
            FIRST_X_ASSUM (fun th => tactic_of do
              pure (GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← SYM th])) THEN
            REWRITE_TAC [pathfinish] THEN DISCH_TAC THEN
            FIRST_X_ASSUM (MP_TAC o SPECL [← q r"t':real^1", ← q r"vec 1:real^1"]) THEN
            ASM_REWRITE_TAC [← GSYM DROP_EQ] THEN
            EXPAND_TAC "t'" THEN
            REWRITE_TAC [IN_INTERVAL_1, DROP_VEC, LIFT_DROP] THEN
            ASM_REAL_ARITH_TAC]]],
      ALL_TAC] THEN
    ASM_SIMP_TAC [DOT_BASIS, LE_REFL, DIMINDEX_GE_1, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"tk:real^M->bool", ← q r"g:real^M->real^N"] THEN
    REWRITE_TAC [o_THM] THEN
    STRIP_TAC THEN EXISTS_TAC (← q r"q INSERT IMAGE (k:real^M->real^M) tk") THEN
    EXISTS_TAC (← q r"(g:real^M->real^N) o (h:real^M->real^M)") THEN
    ASM_SIMP_TAC [FINITE_INSERT, FINITE_IMAGE, o_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC (← SET_RULE
       (← q r"a IN t /\ s SUBSET t DELETE a ==> a INSERT s SUBSET t")) THEN
      ASM_REWRITE_TAC [] THEN
      TRANS_TAC SUBSET_TRANS
        (← q r"p INTER (relative_frontier t:real^M->bool) DELETE q") THEN
      CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
       (← SET_RULE (← q r"t SUBSET IMAGE h s ==> IMAGE k (IMAGE h s) SUBSET s
              ==> IMAGE k t SUBSET s"))) THEN
      REWRITE_TAC [← GSYM IMAGE_o] THEN
      MATCH_MP_TAC (← SET_RULE
       (← q r"(!x. x IN s ==> f x = x) ==> IMAGE f s SUBSET s")) THEN
      REWRITE_TAC [o_THM] THEN ASM SET_TAC [],
      ASM SET_TAC [],
      ASM SET_TAC [],
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      ASM SET_TAC [],
      REWRITE_TAC [IMAGE_o] THEN ASM SET_TAC [],
      ASM SET_TAC []])

  let EXTEND_MAP_SPHERE_TO_SPHERE_COFINITE ← prove
   r"!f:real^M->real^N s a d b e p.
        dimindex(:M) <= dimindex(:N) + 1 /\
        (&0 < d /\ s = {} ==> &0 <= e) /\
        closed s /\ s SUBSET sphere(a,d) /\
        f continuous_on s /\ IMAGE f s SUBSET sphere(b,e) /\
        (!c. c IN components(sphere(a,d) DIFF s) ==> ~(c INTER p = {}))
        ==> ?k g. FINITE k /\ k SUBSET p /\
                  k SUBSET sphere(a,d) /\ DISJOINT k s /\
                  g continuous_on (sphere(a,d) DIFF k) /\
                  IMAGE g (sphere(a,d) DIFF k) SUBSET sphere(b,e) /\
                  !x. x IN s ==> g x = f x"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"s = sphere(a:real^M,d)") THENL
     [ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [← q r"{}:real^M->bool", ← q r"f:real^M->real^N"] THEN
      ASM_REWRITE_TAC [FINITE_EMPTY, DIFF_EMPTY] THEN SET_TAC [],
      POP_ASSUM MP_TAC] THEN
    ASM_CASES_TAC (← q r"d < &0") THENL
     [ASM_SIMP_TAC [SPHERE_EMPTY] THEN SET_TAC [], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"d = &0") THENL
     [ASM_SIMP_TAC [SPHERE_SING] THEN
      ASM_CASES_TAC (← q r"s:real^M->bool = {}") THENL
       [ASM_REWRITE_TAC [], ASM SET_TAC []] THEN
      REPEAT STRIP_TAC THEN
      EXISTS_TAC (← q r"{a:real^M}") THEN
      REWRITE_TAC [FINITE_SING, CONTINUOUS_ON_EMPTY, DIFF_EQ_EMPTY] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"{a:real^M}")) THEN
      REWRITE_TAC [DIFF_EMPTY, IN_COMPONENTS_SELF, CONNECTED_SING] THEN
      REWRITE_TAC [IMAGE_CLAUSES] THEN SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&0 < d") ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    ASM_CASES_TAC (← q r"e = &0") THENL
     [ASM_SIMP_TAC [SPHERE_SING] THEN REPEAT STRIP_TAC THEN
      EXISTS_TAC (← q r"{}:real^M->bool") THEN
      EXISTS_TAC (← q r"(\x. b):real^M->real^N") THEN
      REWRITE_TAC [CONTINUOUS_ON_CONST, FINITE_EMPTY] THEN ASM SET_TAC [],
      REPEAT STRIP_TAC] THEN
    SUBGOAL_THEN (← q r"&0 <= e") ASSUME_TAC THENL
     [ASM_CASES_TAC (← q r"s:real^M->bool = {}") THEN ASM_SIMP_TAC [] THEN
      MP_TAC (← SYM (← ISPECL [← q r"b:real^N", ← q r"e:real"] SPHERE_EQ_EMPTY)) THEN
      SIMP_TAC [← GSYM REAL_NOT_LT] THEN ASM SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&0 < e") ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"f:real^M->real^N", ← q r"s:real^M->bool", ← q r"cball(a:real^M,d)",
      ← q r"cball(b:real^N,e)", ← q r"p:real^M->bool"]
     EXTEND_MAP_SPHERE_TO_SPHERE_COFINITE_GEN) THEN
    ASM_REWRITE_TAC [CONVEX_CBALL, BOUNDED_CBALL] THEN
    REWRITE_TAC [AFF_DIM_CBALL] THEN
    MP_TAC (← ISPECL [← q r"a:real^M", ← q r"d:real"] RELATIVE_FRONTIER_CBALL) THEN
    MP_TAC (← ISPECL [← q r"b:real^N", ← q r"e:real"] RELATIVE_FRONTIER_CBALL) THEN
    ASM_REWRITE_TAC [] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN
    ASM_REWRITE_TAC [INT_OF_NUM_ADD, INT_OF_NUM_LE])

  pure { EXTEND_MAP_SPHERE_TO_SPHERE_COFINITE_GEN,
         EXTEND_MAP_SPHERE_TO_SPHERE_COFINITE }
/- ------------------------------------------------------------------------- -/
/- Borsuk-style characterization of separation.                              -/
/- (moretop.ml 4004-4399)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MOL where
  CONTINUOUS_ON_BORSUK_MAP : thm
  BORSUK_MAP_INTO_SPHERE : thm
  BORSUK_MAPS_HOMOTOPIC_IN_PATH_COMPONENT : thm
  NON_EXTENSIBLE_BORSUK_MAP : thm
  BORSUK_MAP_ESSENTIAL_BOUNDED_COMPONENT : thm
  HOMOTOPIC_BORSUK_MAPS_IN_BOUNDED_COMPONENT : thm
  BORSUK_MAPS_HOMOTOPIC_IN_CONNECTED_COMPONENT_EQ : thm
  BORSUK_SEPARATION_THEOREM_GEN : thm
  BORSUK_SEPARATION_THEOREM : thm
  HOMOTOPY_EQUIVALENT_SEPARATION : thm
  JORDAN_BROUWER_NONSEPARATION_STRONG : thm
  JORDAN_BROUWER_ACCESSIBILITY : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOL [HolBase] (D : MoreTopDeps) (BMOJ : MOJ) : ExceptT String IO MOL := do
  -- @@SCOPE BEGIN
  let { EXTEND_MAP_UNIV_TO_SPHERE_NO_BOUNDED_COMPONENT, .. } := BMOJ
  let { BOUNDED_SUBSET_OPEN_INTERVAL, COBOUNDED_IMP_UNBOUNDED, CONNECTED_COMPONENT_EQ,
        CONNECTED_COMPONENT_EQ_EQ, CONNECTED_COMPONENT_SYM_EQ, CONNECTED_COMPONENT_UNIV,
        .. } := D.qtopology
  let { CLOSED_UNION_COMPLEMENT_COMPONENT, HOMOTOPY_EQUIVALENT_COHOMOTOPIC_TRIVIALITY_NULL,
        HOMOTOPY_EQUIVALENT_EMPTY, JORDAN_BROUWER_FRONTIER, PATH_CONNECTED_UNIONS,
        .. } := D.qpaths
  let { ACCESSIBLE_FRONTIER_ANR_COMPLEMENT_COMPONENT, ANR_SPHERE,
        BORSUK_HOMOTOPY_EXTENSION, HOMEOMORPHIC_ANRNESS, NO_RETRACTION_CBALL,
        NULLHOMOTOPIC_INTO_SPHERE_EXTENSION,
        PATH_CONNECTED_INTERMEDIATE_CLOSURE_ANR_COMPLEMENT_COMPONENT, retract_of,
        retraction, .. } := D.qdegree
  let { CLOSED_DIFF, .. } := D.ra.ts.cn.ms.qtopology1
  let { ARITH_RULE, ASM_MESON_TAC, GEOM_EQUAL_DIMENSION_RULE, MESON_TAC, NORM_ARITH,
        REAL_FIELD, SET_RULE, SET_TAC, VECTOR_ARITH, .. } := D.ra.ts.cn.cx.cvx
  let { CONTRAPOS_THM, DIFF_EMPTY, DIMINDEX_1, DIMINDEX_GE_1, EMPTY_SUBSET,
        EXISTS_IN_GSPEC, EXTENSION, FORALL_IN_GSPEC, .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_IN_INSERT, FORALL_IN_PCROSS, FSTCART_PASTECART,
        IMAGE_CLAUSES, IMP_CONJ, IMP_CONJ_ALT, IN, IN_DIFF, INTERS_GSPEC,
        .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_UNION, IN_UNIV, LE_REFL, LEFT_IMP_EXISTS_THM, MONO_AND, MONO_EXISTS,
        NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, PCROSS_EMPTY, REAL_ABS_INV,
        .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_REFL, .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_LINV, REAL_MUL_RINV, REAL_POS, RIGHT_EXISTS_AND_THM, SNDCART_PASTECART,
        SUBSET, SUBSET_UNION, .. } := D.ra.ts.cn.cx.cvx.core5
  let { o_DEF, SUBSET_UNIV, UNION_SUBSET, UNIONS_GSPEC, .. } := D.ra.ts.cn.cx.cvx.core6
  let { LINEAR_FSTCART, LINEAR_SNDCART, NORM_EQ_0, .. } := D.ra.ts.cn.cx.cvx.vec2
  let { NORM_MUL, NORM_SUB, REAL_ABS_NORM, .. } := D.ra.ts.cn.cx.cvx.vec3
  let { dist, VECTOR_MUL_ASSOC, VECTOR_SUB_EQ, .. } := D.ra.ts.cn.cx.cvx.vec4
  let { BALL_SUBSET_CBALL, BOUNDED_BALL, BOUNDED_EMPTY, BOUNDED_SUBSET,
        BOUNDED_SUBSET_BALL, CENTRE_IN_CBALL, CLOSED_CBALL, CLOSED_SUBSET,
        .. } := D.ra.ts.cn.cx.cvx.top1
  let { CLOSURE_SUBSET, COMPACT_EQ_BOUNDED_CLOSED, COMPACT_IMP_BOUNDED, COMPACT_IMP_CLOSED,
        COMPACT_SPHERE, COMPONENTS_EQ_EMPTY, .. } := D.ra.ts.cn.cx.cvx.top2
  let { CONTINUOUS_ON_ADD, CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID,
        CONTINUOUS_ON_INV, CONTINUOUS_ON_LIFT_NORM_COMPOSE, CONTINUOUS_ON_MUL,
        CONTINUOUS_ON_SUB, CONTINUOUS_ON_SUBSET, .. } := D.ra.ts.cn.cx.cvx.top3
  let { IN_BALL, IN_COMPONENTS_SUBSET, IN_INTERVAL_1, IN_SPHERE, IN_SPHERE_0,
        IS_INTERVAL_1, LINEAR_CONTINUOUS_ON, NOT_BOUNDED_UNIV,
        .. } := D.ra.ts.cn.cx.cvx.top4
  let { closed, components, TOPSPACE_EUCLIDEAN_SUBTOPOLOGY, UNIONS_COMPONENTS,
        .. } := D.ra.ts.cn.cx.cvx.top5
  let { IS_INTERVAL_CONNECTED_1, .. } := D.ra.ts.cn.ms.ig.dv.dg.qconvex
  let { HOMOTOPIC_WITH_EQ, HOMOTOPIC_WITH_SYM, HOMOTOPIC_WITH_TRANS,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qmetric
  let { COBOUNDED_UNIQUE_UNBOUNDED_COMPONENT, CONTRACTIBLE_UNIV, CONVEX_IMP_CONTRACTIBLE,
        HOMOTOPIC_WITH_EUCLIDEAN_ALT, .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths1
  let { HOMOTOPIC_WITH_SUBSET_LEFT, NULLHOMOTOPIC_FROM_CONTRACTIBLE,
        OPEN_CONNECTED_COMPONENT, OPEN_PATH_CONNECTED_COMPONENT, path, path_component,
        path_image, pathfinish, pathstart, .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths2
  let { COMPL_COMPL, .. } := D.ra.ts.cn.ms.ig.dv.dg.qsession
  let { BOUNDED_UNION, CLOSURE_UNION_FRONTIER, COMPONENTS_EQ_SING,
        CONNECTED_COMPONENT_REFL_EQ, CONNECTED_EQ_CONNECTED_COMPONENT_EQ, CONNECTED_UNIV,
        CONTINUOUS_ON_CASES, CONTINUOUS_ON_CMUL, CONTINUOUS_ON_EMPTY,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { HOMEOMORPHIC_COMPACTNESS, IN_COMPONENTS, SPHERE_SUBSET_CBALL,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology2
  let { IMAGE_FSTCART_PCROSS, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qses
  let { CONVEX_BALL, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  -- @@SCOPE END

  let CONTINUOUS_ON_BORSUK_MAP ← prove
   r"!s a:real^N.
        ~(a IN s) ==> (\x. inv(norm (x - a)) % (x - a)) continuous_on s"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN SIMP_TAC [o_DEF] THEN CONJ_TAC THENL
      [MATCH_MP_TAC (← REWRITE_RULE [o_DEF] CONTINUOUS_ON_INV), ALL_TAC] THEN
    SIMP_TAC [CONTINUOUS_ON_LIFT_NORM_COMPOSE, CONTINUOUS_ON_SUB,
              CONTINUOUS_ON_ID, CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC [NORM_EQ_0, VECTOR_SUB_EQ] THEN ASM_MESON_TAC [])

  let BORSUK_MAP_INTO_SPHERE ← prove
   r"!s a:real^N.
        IMAGE (\x. inv(norm (x - a)) % (x - a)) s SUBSET sphere(vec 0,&1) <=>
        ~(a IN s)"
   (REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_SPHERE_0] THEN
    REWRITE_TAC [NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
    REWRITE_TAC [← REAL_FIELD (← q r"inv x * x = &1 <=> ~(x = &0)")] THEN
    REWRITE_TAC [NORM_EQ_0, VECTOR_SUB_EQ] THEN MESON_TAC [])

  let BORSUK_MAPS_HOMOTOPIC_IN_PATH_COMPONENT ← prove
   r"!s a b. path_component ((:real^N) DIFF s) a b
           ==> homotopic_with (\x. T)
                   (subtopology euclidean s,
                    subtopology euclidean (sphere(vec 0,&1)))
                   (\x. inv(norm(x - a)) % (x - a))
                   (\x. inv(norm(x - b)) % (x - b))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [path_component, LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [path, path_image, pathstart, pathfinish, SUBSET,
                 FORALL_IN_IMAGE, IN_UNIV, IN_DIFF] THEN
    X_GEN_TAC (← q r"g:real^1->real^N") THEN STRIP_TAC THEN
    SIMP_TAC [HOMOTOPIC_WITH_EUCLIDEAN_ALT] THEN
    EXISTS_TAC (← q r"\z. inv(norm(sndcart z - g(fstcart z))) %
                    (sndcart z - (g:real^1->real^N)(fstcart z))") THEN
    ASM_SIMP_TAC [FSTCART_PASTECART, SNDCART_PASTECART, IN_SPHERE_0,
                  SUBSET, FORALL_IN_IMAGE, FORALL_IN_PCROSS] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC [o_DEF] THEN CONJ_TAC THENL
       [MATCH_MP_TAC (← REWRITE_RULE [o_DEF] CONTINUOUS_ON_INV) THEN
        ASM_SIMP_TAC [FORALL_IN_PCROSS, FSTCART_PASTECART, SNDCART_PASTECART,
                      NORM_EQ_0, VECTOR_SUB_EQ] THEN CONJ_TAC
        THENL [MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE, ASM_MESON_TAC []],
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      SIMP_TAC [LINEAR_CONTINUOUS_ON, LINEAR_SNDCART] THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC [LINEAR_CONTINUOUS_ON, LINEAR_FSTCART] THEN
      REWRITE_TAC [IMAGE_FSTCART_PCROSS] THEN ASM_MESON_TAC [CONTINUOUS_ON_EMPTY],
      REPEAT STRIP_TAC THEN
      REWRITE_TAC [NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN
      ASM_REWRITE_TAC [NORM_EQ_0, VECTOR_SUB_EQ] THEN ASM_MESON_TAC []])

  let NON_EXTENSIBLE_BORSUK_MAP ← prove
   r"!s c a:real^N.
        compact s /\ c IN components((:real^N) DIFF s) /\ bounded c /\ a IN c
        ==> ~(?g. g continuous_on (s UNION c) /\
                  IMAGE g (s UNION c) SUBSET sphere (vec 0,&1) /\
                  (!x. x IN s ==> g x = inv(norm(x - a)) % (x - a)))"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
    REWRITE_TAC [SUBSET] THEN DISCH_THEN (MP_TAC o SPEC (← q r"a:real^N")) THEN
    ASM_REWRITE_TAC [IN_DIFF] THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"c = connected_component ((:real^N) DIFF s) a") SUBST_ALL_TAC
    THENL [ASM_MESON_TAC [IN_COMPONENTS, CONNECTED_COMPONENT_EQ], ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"s UNION connected_component ((:real^N) DIFF s) a", ← q r"a:real^N"]
        BOUNDED_SUBSET_BALL) THEN
    ASM_SIMP_TAC [BOUNDED_UNION, COMPACT_IMP_BOUNDED] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"r:real") STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"a:real^N") o MATCH_MP NO_RETRACTION_CBALL) THEN
    REWRITE_TAC [retract_of, retraction] THEN
    EXISTS_TAC (← q r"\x. if x IN connected_component ((:real^N) DIFF s) a
                    then a + r % g(x)
                    else a + r % inv(norm(x - a)) % (x - a)") THEN
    REWRITE_TAC [SPHERE_SUBSET_CBALL] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN (← q r"cball(a:real^N,r) =
                    (s UNION connected_component ((:real^N) DIFF s) a) UNION
                    (cball(a,r) DIFF connected_component ((:real^N) DIFF s) a)")
      SUBST1_TAC THENL
       [MP_TAC (← ISPECL [← q r"a:real^N", ← q r"r:real"] BALL_SUBSET_CBALL) THEN ASM
        SET_TAC [],
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CASES THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_UNION_COMPLEMENT_COMPONENT THEN
        ASM_SIMP_TAC [IN_COMPONENTS, COMPACT_IMP_CLOSED, IN_UNIV, IN_DIFF] THEN
        ASM_MESON_TAC [],
        MATCH_MP_TAC CLOSED_DIFF THEN
        ASM_SIMP_TAC [CLOSED_CBALL, OPEN_CONNECTED_COMPONENT, ← GSYM closed,
                      COMPACT_IMP_CLOSED],
        MATCH_MP_TAC CONTINUOUS_ON_ADD THEN SIMP_TAC [CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN ASM_SIMP_TAC [CONTINUOUS_ON_CONST],
        MATCH_MP_TAC CONTINUOUS_ON_ADD THEN SIMP_TAC [CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
        MATCH_MP_TAC CONTINUOUS_ON_BORSUK_MAP THEN
        ASM_SIMP_TAC [CENTRE_IN_CBALL, IN_DIFF, REAL_LT_IMP_LE] THEN
        REWRITE_TAC [IN] THEN REWRITE_TAC [CONNECTED_COMPONENT_REFL_EQ] THEN
        ASM_REWRITE_TAC [IN_DIFF, IN_UNIV],
        REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC []],
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
        REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC [IN_SPHERE, ← NORM_ARITH (← q r"dist(a:real^N,a + x) = norm x"),
                         NORM_MUL] THEN
        ASM_SIMP_TAC [REAL_ABS_INV, REAL_ABS_NORM, VECTOR_SUB_EQ,
          ← REAL_FIELD (← q r"&0 < r ==> abs r = r /\ (r * x = r <=> x = &1)"),
          ← REAL_FIELD (← q r"inv x * x = &1 <=> ~(x = &0)"), NORM_EQ_0]
        THENL
         [ONCE_REWRITE_TAC [← GSYM IN_SPHERE_0] THEN ASM SET_TAC [],
          UNDISCH_TAC (← q r"~(x IN connected_component ((:real^N) DIFF s) a)") THEN
          SIMP_TAC [CONTRAPOS_THM, IN] THEN
          ASM_REWRITE_TAC [CONNECTED_COMPONENT_REFL_EQ, IN_DIFF, IN_UNIV]],
        SIMP_TAC [IN_SPHERE, ← ONCE_REWRITE_RULE [NORM_SUB] dist] THEN
        ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_RINV, REAL_LT_IMP_NZ] THEN
        REWRITE_TAC [← VECTOR_ARITH (← q r"a + &1 % (x - a):real^N = x")] THEN
        REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
         (← q r"s UNION t SUBSET u ==> !x. x IN t /\ ~(x IN u) ==> wev"))) THEN
        EXISTS_TAC (← q r"x:real^N") THEN
        ASM_REWRITE_TAC [← ONCE_REWRITE_RULE [NORM_SUB] dist, IN_BALL,
                         REAL_LT_REFL]])

  let BORSUK_MAP_ESSENTIAL_BOUNDED_COMPONENT ← prove
   r"!s a. compact s /\ ~(a IN s)
         ==> (bounded(connected_component ((:real^N) DIFF s) a) <=>
              ~(?c. homotopic_with (\x. T)
                      (subtopology euclidean s,
                       subtopology euclidean (sphere(vec 0:real^N,&1)))
                      (\x. inv(norm(x - a)) % (x - a)) (\x. c)))"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"s:real^N->bool = {}") THENL
     [ASM_SIMP_TAC [DIFF_EMPTY, CONNECTED_COMPONENT_UNIV, NOT_BOUNDED_UNIV] THEN
      SIMP_TAC [HOMOTOPIC_WITH_EUCLIDEAN_ALT, NOT_IN_EMPTY, PCROSS_EMPTY,
                IMAGE_CLAUSES, CONTINUOUS_ON_EMPTY, EMPTY_SUBSET],
      ALL_TAC] THEN
    EQ_TAC THENL
     [ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN REWRITE_TAC [] THEN
      REPEAT DISCH_TAC THEN
      MP_TAC (← ISPECL
       [← q r"\x:real^N. inv(norm(x - a)) % (x - a)", ← q r"s:real^N->bool",
        ← q r"vec 0:real^N", ← q r"&1"]
       NULLHOMOTOPIC_INTO_SPHERE_EXTENSION) THEN
      ASM_SIMP_TAC [COMPACT_IMP_CLOSED, NOT_IMP, CONTINUOUS_ON_BORSUK_MAP,
                    BORSUK_MAP_INTO_SPHERE] THEN
      MP_TAC (← ISPECL [← q r"s:real^N->bool",
          ← q r"connected_component ((:real^N) DIFF s) a",
          ← q r"a:real^N"] NON_EXTENSIBLE_BORSUK_MAP) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [IN] THEN
        REWRITE_TAC [CONNECTED_COMPONENT_REFL_EQ] THEN
        ASM_REWRITE_TAC [IN_COMPONENTS, IN_DIFF, IN_UNIV] THEN ASM_MESON_TAC [],
        REWRITE_TAC [CONTRAPOS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
        GEN_TAC THEN MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
         [MESON_TAC [CONTINUOUS_ON_SUBSET, SUBSET_UNIV], SET_TAC []]],
      ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN REWRITE_TAC [] THEN
      DISCH_TAC THEN
      FIRST_ASSUM (MP_TAC o SPEC (← q r"vec 0:real^N") o MATCH_MP BOUNDED_SUBSET_BALL o
        MATCH_MP COMPACT_IMP_BOUNDED) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"r:real") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       (← q r"?b. b IN connected_component ((:real^N) DIFF s) a /\
            ~(b IN ball(vec 0,r))")
      MP_TAC THENL
       [REWRITE_TAC [← SET_RULE (← q r"(?b. b IN s /\ ~(b IN t)) <=> ~(s SUBSET t)")] THEN
        ASM_MESON_TAC [BOUNDED_SUBSET, BOUNDED_BALL],
        DISCH_THEN (X_CHOOSE_THEN (← q r"b:real^N") STRIP_ASSUME_TAC)] THEN
      SUBGOAL_THEN
       (← q r"?c. homotopic_with (\x. T)
             (subtopology euclidean (ball(vec 0:real^N,r)),
              subtopology euclidean (sphere(vec 0,&1)))
                           (\x. inv (norm (x - b)) % (x - b)) (\x. c)")
      MP_TAC THENL
       [MATCH_MP_TAC NULLHOMOTOPIC_FROM_CONTRACTIBLE THEN
        ASM_SIMP_TAC [CONTINUOUS_ON_BORSUK_MAP, BORSUK_MAP_INTO_SPHERE,
                      CONVEX_IMP_CONTRACTIBLE, CONVEX_BALL],
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"c:real^N") THEN STRIP_TAC] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
      EXISTS_TAC (← q r"\x:real^N. inv(norm (x - b)) % (x - b)") THEN CONJ_TAC THENL
       [MATCH_MP_TAC BORSUK_MAPS_HOMOTOPIC_IN_PATH_COMPONENT THEN
        ASM_SIMP_TAC [OPEN_PATH_CONNECTED_COMPONENT, ← GSYM closed,
                      COMPACT_IMP_CLOSED] THEN  ASM_MESON_TAC [IN],
        ASM_MESON_TAC [HOMOTOPIC_WITH_SUBSET_LEFT]]])

  let HOMOTOPIC_BORSUK_MAPS_IN_BOUNDED_COMPONENT ← prove
   r"!s a b.
        compact s /\ ~(a IN s) /\ ~(b IN s) /\
        bounded (connected_component ((:real^N) DIFF s) a) /\
        homotopic_with (\x. T)
          (subtopology euclidean s,
           subtopology euclidean (sphere(vec 0,&1)))
          (\x. inv(norm(x - a)) % (x - a))
          (\x. inv(norm(x - b)) % (x - b))
        ==> connected_component ((:real^N) DIFF s) a b"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC id [← GSYM IN] THEN
    MP_TAC (← ISPECL
     [← q r"s:real^N->bool", ← q r"connected_component ((:real^N) DIFF s) a",
      ← q r"a:real^N"] NON_EXTENSIBLE_BORSUK_MAP) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [IN] THEN
      REWRITE_TAC [CONNECTED_COMPONENT_REFL_EQ] THEN
      ASM_REWRITE_TAC [IN_COMPONENTS, IN_DIFF, IN_UNIV] THEN ASM_MESON_TAC [],
      ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM]] THEN
    DISCH_TAC THEN REWRITE_TAC [] THEN
    MATCH_MP_TAC BORSUK_HOMOTOPY_EXTENSION THEN
    EXISTS_TAC (← q r"\x:real^N. inv(norm(x - b)) % (x - b)") THEN
    ASM_SIMP_TAC [COMPACT_IMP_CLOSED, ANR_SPHERE,
                  CLOSED_SUBSET, SUBSET_UNION] THEN
    ONCE_REWRITE_TAC [HOMOTOPIC_WITH_SYM] THEN
    ASM_SIMP_TAC [CONTINUOUS_ON_BORSUK_MAP, IN_UNION, BORSUK_MAP_INTO_SPHERE] THEN
    REWRITE_TAC [RIGHT_EXISTS_AND_THM] THEN
    MATCH_MP_TAC CLOSED_UNION_COMPLEMENT_COMPONENT THEN
    ASM_SIMP_TAC [COMPACT_IMP_CLOSED, IN_COMPONENTS, IN_DIFF, IN_UNIV] THEN
    ASM_MESON_TAC [])

  let BORSUK_MAPS_HOMOTOPIC_IN_CONNECTED_COMPONENT_EQ ← prove
   r"!s a b. 2 <= dimindex(:N) /\ compact s /\ ~(a IN s) /\ ~(b IN s)
           ==> (homotopic_with (\x. T)
                   (subtopology euclidean s,
                    subtopology euclidean (sphere(vec 0,&1)))
                   (\x. inv(norm(x - a)) % (x - a))
                   (\x. inv(norm(x - b)) % (x - b)) <=>
                connected_component ((:real^N) DIFF s) a b)"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_TAC,
      ASM_SIMP_TAC [← GSYM OPEN_PATH_CONNECTED_COMPONENT, ← GSYM closed,
                    COMPACT_IMP_CLOSED] THEN
      REWRITE_TAC [BORSUK_MAPS_HOMOTOPIC_IN_PATH_COMPONENT]] THEN
    ASM_CASES_TAC (← q r"bounded(connected_component ((:real^N) DIFF s) a)") THENL
     [MATCH_MP_TAC HOMOTOPIC_BORSUK_MAPS_IN_BOUNDED_COMPONENT THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"bounded(connected_component ((:real^N) DIFF s) b)") THENL
     [ONCE_REWRITE_TAC [CONNECTED_COMPONENT_SYM_EQ] THEN
      MATCH_MP_TAC HOMOTOPIC_BORSUK_MAPS_IN_BOUNDED_COMPONENT THEN
      ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [HOMOTOPIC_WITH_SYM] THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"(:real^N) DIFF s", ← q r"a:real^N", ← q r"b:real^N"]
          COBOUNDED_UNIQUE_UNBOUNDED_COMPONENT) THEN
    ASM_REWRITE_TAC [CONNECTED_COMPONENT_EQ_EQ, IN_DIFF, IN_UNIV,
                     COMPL_COMPL] THEN
    ASM_SIMP_TAC [COMPACT_IMP_BOUNDED])

  let BORSUK_SEPARATION_THEOREM_GEN ← prove
   r"!s:real^N->bool.
    compact s
    ==> ((!c. c IN components((:real^N) DIFF s) ==> ~bounded c) <=>
         (!f. f continuous_on s /\ IMAGE f s SUBSET sphere(vec 0:real^N,&1)
              ==> ?c. homotopic_with (\x. T)
                       (subtopology euclidean s,
                        subtopology euclidean (sphere(vec 0,&1))) f (\x. c)))"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ALL_TAC,
      ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC [NOT_FORALL_THM, components, EXISTS_IN_GSPEC, NOT_IMP,
                   IN_UNIV, IN_DIFF] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"a:real^N") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"\x:real^N. inv(norm(x - a)) % (x - a)") THEN
      ASM_SIMP_TAC [← GSYM BORSUK_MAP_ESSENTIAL_BOUNDED_COMPONENT,
                    CONTINUOUS_ON_BORSUK_MAP, BORSUK_MAP_INTO_SPHERE]] THEN
    DISCH_TAC THEN X_GEN_TAC (← q r"f:real^N->real^N") THEN STRIP_TAC THEN
    MP_TAC (← ISPECL
     [← q r"f:real^N->real^N", ← q r"s:real^N->bool", ← q r"vec 0:real^N", ← q r"&1:real"]
          EXTEND_MAP_UNIV_TO_SPHERE_NO_BOUNDED_COMPONENT) THEN
    ASM_REWRITE_TAC [LE_REFL, REAL_POS] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->real^N") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL
     [← q r"g:real^N->real^N", ← q r"(:real^N)", ← q r"sphere(vec 0:real^N,&1)"]
          NULLHOMOTOPIC_FROM_CONTRACTIBLE) THEN
    ASM_REWRITE_TAC [CONTRACTIBLE_UNIV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"s:real^N->bool") o MATCH_MP
     (← REWRITE_RULE [IMP_CONJ] HOMOTOPIC_WITH_SUBSET_LEFT)) THEN
    REWRITE_TAC [SUBSET_UNIV] THEN
    MATCH_MP_TAC (← ONCE_REWRITE_RULE [IMP_CONJ_ALT]
          HOMOTOPIC_WITH_EQ) THEN
    ASM_SIMP_TAC [TOPSPACE_EUCLIDEAN_SUBTOPOLOGY])

  let BORSUK_SEPARATION_THEOREM ← prove
   r"!s:real^N->bool.
      2 <= dimindex(:N) /\ compact s
      ==> (connected((:real^N) DIFF s) <=>
           !f. f continuous_on s /\ IMAGE f s SUBSET sphere(vec 0:real^N,&1)
               ==> ?c. homotopic_with (\x. T)
                        (subtopology euclidean s,
                         subtopology euclidean (sphere(vec 0,&1))) f (\x. c))"
   (SIMP_TAC [← GSYM BORSUK_SEPARATION_THEOREM_GEN] THEN
    X_GEN_TAC (← q r"s:real^N->bool") THEN STRIP_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN
      MP_TAC (← ISPEC (← q r"(:real^N) DIFF s") COMPONENTS_EQ_SING) THEN
      MP_TAC (← ISPEC (← q r"(:real^N) DIFF s") COBOUNDED_IMP_UNBOUNDED) THEN
      ASM_CASES_TAC (← q r"(:real^N) DIFF s = {}") THEN
      ASM_SIMP_TAC [COMPACT_IMP_BOUNDED, COMPL_COMPL,
                    BOUNDED_EMPTY, FORALL_IN_INSERT, NOT_IN_EMPTY],
      REWRITE_TAC [components, FORALL_IN_GSPEC, IN_DIFF, IN_UNIV] THEN
      DISCH_TAC THEN REWRITE_TAC [CONNECTED_EQ_CONNECTED_COMPONENT_EQ] THEN
      REWRITE_TAC [IN_DIFF, IN_UNIV] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC COBOUNDED_UNIQUE_UNBOUNDED_COMPONENT THEN
      ASM_SIMP_TAC [COMPACT_IMP_BOUNDED,
                    COMPL_COMPL]])

  let HOMOTOPY_EQUIVALENT_SEPARATION ← (do
    let special ← prove
     r"!s:real^1->bool.
            bounded s /\ connected((:real^1) DIFF s) ==> s = {}"
     (REWRITE_TAC [← GSYM IS_INTERVAL_CONNECTED_1] THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP BOUNDED_SUBSET_OPEN_INTERVAL) THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM, EXTENSION, NOT_IN_EMPTY] THEN
      MAP_EVERY X_GEN_TAC [← q r"a:real^1", ← q r"b:real^1"] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [IS_INTERVAL_1]) THEN
      DISCH_THEN (MP_TAC o SPECL [← q r"a:real^1", ← q r"b:real^1"]) THEN
      REWRITE_TAC [IN_UNIV, IN_DIFF, SUBSET, IN_INTERVAL_1] THEN
      MESON_TAC [REAL_LT_REFL, REAL_LT_IMP_LE])
    prove
     r"!s t. compact s /\ compact t /\ s homotopy_equivalent t
           ==> (connected((:real^N) DIFF s) <=> connected((:real^N) DIFF t))"
     (REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"1 <= dimindex(:N)") MP_TAC THENL
       [REWRITE_TAC [DIMINDEX_GE_1],
        REWRITE_TAC [← ARITH_RULE (← q r"1 <= n <=> n = 1 \/ 2 <= n")] THEN
        REWRITE_TAC [← GSYM DIMINDEX_1]] THEN
      STRIP_TAC THENL
       [ASSUME_TAC (← GEOM_EQUAL_DIMENSION_RULE
           (← ASSUME (← q r"dimindex(:N) = dimindex(:1)")) special) THEN
        EQ_TAC THEN DISCH_TAC THENL
         [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"s:real^N->bool")),
          FIRST_X_ASSUM (MP_TAC o SPEC (← q r"t:real^N->bool"))] THEN
        ASM_SIMP_TAC [COMPACT_IMP_BOUNDED] THEN DISCH_TAC THEN
        UNDISCH_TAC (← q r"(s:real^N->bool) homotopy_equivalent (t:real^N->bool)") THEN
        ASM_REWRITE_TAC [HOMOTOPY_EQUIVALENT_EMPTY] THEN DISCH_TAC THEN
        ASM_REWRITE_TAC [CONNECTED_UNIV, DIFF_EMPTY],
        REPEAT STRIP_TAC THEN ASM_SIMP_TAC [BORSUK_SEPARATION_THEOREM] THEN
        MATCH_MP_TAC HOMOTOPY_EQUIVALENT_COHOMOTOPIC_TRIVIALITY_NULL THEN
        ASM_REWRITE_TAC []]))

  let JORDAN_BROUWER_NONSEPARATION_STRONG ← prove
   r"!s t a:real^N r.
        2 <= dimindex(:N) /\ s homeomorphic sphere(a,r) /\ t PSUBSET s
        ==> path_connected((:real^N) DIFF t)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"!c. c IN components((:real^N) DIFF s)
          ==> path_connected(c UNION (s DIFF t))")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC
       PATH_CONNECTED_INTERMEDIATE_CLOSURE_ANR_COMPLEMENT_COMPONENT THEN
      MAP_EVERY EXISTS_TAC [← q r"s:real^N->bool", ← q r"c:real^N->bool"] THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP HOMEOMORPHIC_COMPACTNESS) THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP HOMEOMORPHIC_ANRNESS) THEN
      REWRITE_TAC [COMPACT_SPHERE, ANR_SPHERE] THEN
      REPEAT DISCH_TAC THEN ASM_REWRITE_TAC [SUBSET_UNION] THEN
      REWRITE_TAC [UNION_SUBSET, CLOSURE_SUBSET, CLOSURE_UNION_FRONTIER] THEN
      MATCH_MP_TAC (← SET_RULE (← q r"f = s ==> s DIFF t SUBSET k UNION f")) THEN
      MATCH_MP_TAC JORDAN_BROUWER_FRONTIER THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
      (← q r"~(components((:real^N) DIFF s) = {})")
    ASSUME_TAC THENL
     [REWRITE_TAC [COMPONENTS_EQ_EMPTY, ← SET_RULE
       (← q r"UNIV DIFF s = {} <=> s = UNIV")] THEN
      ASM_MESON_TAC [NOT_BOUNDED_UNIV, COMPACT_EQ_BOUNDED_CLOSED,
                     HOMEOMORPHIC_COMPACTNESS, COMPACT_SPHERE],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"(:real^N) DIFF t =
      UNIONS {c UNION (s DIFF t) | c | c IN components((:real^N) DIFF s)}")
    SUBST1_TAC THENL
     [MP_TAC (← ISPEC (← q r"(:real^N) DIFF s") UNIONS_COMPONENTS) THEN
      REWRITE_TAC [UNIONS_GSPEC] THEN ASM SET_TAC [],
      MATCH_MP_TAC PATH_CONNECTED_UNIONS THEN
      ASM_REWRITE_TAC [FORALL_IN_GSPEC] THEN
      REWRITE_TAC [INTERS_GSPEC] THEN ASM SET_TAC []])

  let JORDAN_BROUWER_ACCESSIBILITY ← prove
   r"!s c a:real^N r x y.
        2 <= dimindex(:N) /\
        s homeomorphic sphere(a,r) /\
        c IN components((:real^N) DIFF s) /\ x IN c /\ y IN s
        ==> ?g. arc g /\  pathstart g = x /\ pathfinish g = y /\
                IMAGE g (interval[vec 0,vec 1] DELETE (vec 1)) SUBSET c"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
    MATCH_MP_TAC ACCESSIBLE_FRONTIER_ANR_COMPLEMENT_COMPONENT THEN
    EXISTS_TAC (← q r"s:real^N->bool") THEN ASM_REWRITE_TAC [] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM (MP_TAC o MATCH_MP HOMEOMORPHIC_COMPACTNESS) THEN
      REWRITE_TAC [COMPACT_SPHERE],
      FIRST_ASSUM (MP_TAC o MATCH_MP HOMEOMORPHIC_ANRNESS) THEN
      REWRITE_TAC [ANR_SPHERE],
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
       (← q r"x IN s ==> t = s ==> x IN t"))) THEN
      MATCH_MP_TAC JORDAN_BROUWER_FRONTIER THEN ASM_MESON_TAC []])

  pure { CONTINUOUS_ON_BORSUK_MAP, BORSUK_MAP_INTO_SPHERE,
         BORSUK_MAPS_HOMOTOPIC_IN_PATH_COMPONENT, NON_EXTENSIBLE_BORSUK_MAP,
         BORSUK_MAP_ESSENTIAL_BOUNDED_COMPONENT,
         HOMOTOPIC_BORSUK_MAPS_IN_BOUNDED_COMPONENT,
         BORSUK_MAPS_HOMOTOPIC_IN_CONNECTED_COMPONENT_EQ,
         BORSUK_SEPARATION_THEOREM_GEN, BORSUK_SEPARATION_THEOREM,
         HOMOTOPY_EQUIVALENT_SEPARATION, JORDAN_BROUWER_NONSEPARATION_STRONG,
         JORDAN_BROUWER_ACCESSIBILITY }
/- ------------------------------------------------------------------------- -/
/- Borsuk-style characterization of separation: spheres, contractible sets   -/
/- and simple path images.                                                   -/
/- (moretop.ml 4400-4634)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MOM where
  HOMOTOPY_EQUIVALENT_SEPARATION_SPHERE : thm
  CONNECTED_COMPLEMENT_CONTRACTIBLE : thm
  CONNECTED_COMPLEMENT_SIMPLE_PATH_IMAGE : thm
  PATH_CONNECTED_PSUPERSET_COMPLEMENT_SIMPLE_PATH_IMAGE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOM [HolBase] (D : MoreTopDeps) (BMOL : MOL) : ExceptT String IO MOM := do
  -- @@SCOPE BEGIN
  let { HOMOTOPY_EQUIVALENT_SEPARATION, JORDAN_BROUWER_NONSEPARATION_STRONG, .. } := BMOL
  let { CONNECTED_EQ_CARD_COMPONENTS, FINITE_IMP_TOTALLY_DISCONNECTED,
        HOMEOMORPHIC_SELF_IMAGE, HOMEOMORPHISM_COMPACTNESS, HOMEOMORPHISM_CONNECTEDNESS,
        IN_COMPONENTS_SELF, .. } := D.qtopology
  let { CONNECTED_COMPLEMENT_SUBSET_CIRCLE, CONNECTED_OPEN_IN_SPHERE_DELETE_EQ,
        HOMEOMORPHIC_PUNCTURED_SPHERE_UNIV, HOMOTOPY_EQUIVALENT_CARD_EQ_COMPONENTS,
        HOMOTOPY_EQUIVALENT_CONNECTEDNESS, HOMOTOPY_EQUIVALENT_SING,
        JORDAN_BROUWER_NONSEPARATION, JORDAN_BROUWER_SEPARATION,
        PATH_CONNECTED_OPEN_IN_DIFF_UNIONS_LOWDIM, .. } := D.qpaths
  let { AFF_DIM_CBALL, AFFINE_HULL_UNIV, CLOSED_SEGMENT, COMPACT_RELATIVE_FRONTIER,
        HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS, .. } := D.qconvex
  let { ANR_PATH_IMAGE_SIMPLE_PATH, AR_SING, CONNECTED_ARC_COMPLEMENT,
        CONNECTED_COMPLEMENT_ABSOLUTE_RETRACT,
        PATH_CONNECTED_INTERMEDIATE_CLOSURE_ANR_COMPLEMENT_COMPONENT,
        PATH_CONNECTED_SUPERSET_COMPLEMENT_ARC_IMAGE, .. } := D.qdegree
  let { DIMINDEX_FINITE_DIFF, .. } := D.qsession
  let { CARD_EQ_CARD_IMP, CARD_EQ_IMAGE, CARD_EQ_TRANS, .. } := D.qcard
  let { RELATIVE_FRONTIER_OF_TRIANGLE, .. } := D.qpolytope
  let { CARD_EQ_SYM, .. } := D.ra.ts.cn.ms.qcard
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, REAL_ARITH_TAC,
        REAL_RAT_REDUCE_CONV, SET_RULE, SET_TAC, .. } := D.ra.ts.cn.cx.cvx
  let { ARITH, ARITH_EQ, CARD_DIFF, CARD_IMAGE_INJ, CARD_SUBSET, CONJ_ASSOC, DE_MORGAN_THM,
        DIFF_EMPTY, DIFF_EQ_EMPTY, DIMINDEX_1, DIMINDEX_2, DIMINDEX_GE_1, EQ_IMP,
        FINITE_DIFF, FINITE_EMPTY, FINITE_IMAGE, FINITE_INSERT, FINITE_SUBSET,
        .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_INSERT, IMP_CONJ, IMP_IMP, INT_OF_NUM_EQ, INT_OF_NUM_LE,
        .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, IN_SING, IN_UNIV, LEFT_IMP_EXISTS_THM, NOT_IN_EMPTY,
        PSUBSET, .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_LT_01, .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_NOT_LE, REAL_OF_NUM_EQ, SUBSET_DELETE, SUBSET_DIFF,
        .. } := D.ra.ts.cn.cx.cvx.core5
  let { HULL_INC, .. } := D.ra.ts.cn.cx.cvx.misc
  let { BASIS_COMPONENT, BASIS_NONZERO, COLLINEAR_LEMMA, DIM_EMPTY, DIM_INSERT,
        DIM_INSERT_0, DIM_SING, .. } := D.ra.ts.cn.cx.cvx.vec1
  let { SPAN_EMPTY, SPAN_SING, .. } := D.ra.ts.cn.cx.cvx.vec3
  let { VECTOR_MUL_COMPONENT, .. } := D.ra.ts.cn.cx.cvx.vec4
  let { BOUNDED_CBALL, BOUNDED_EMPTY, BOUNDED_INSERT, BOUNDED_SUBSET, CLOSURE_COMPLEMENT,
        .. } := D.ra.ts.cn.cx.cvx.top1
  let { COMPACT_IMP_CLOSED, COMPACT_SING, .. } := D.ra.ts.cn.cx.cvx.top2
  let { FINITE_IMP_COMPACT, HOMEOMORPHIC_REFL, .. } := D.ra.ts.cn.cx.cvx.top3
  let { HOMEOMORPHIC_TRANS, NOT_BOUNDED_UNIV, .. } := D.ra.ts.cn.cx.cvx.top4
  let { homeomorphic, homeomorphism, OPEN_IN_REFL, .. } := D.ra.ts.cn.cx.cvx.top5
  let { INJECTIVE_ON_LEFT_INVERSE, .. } := D.ra.ts.cn.ms.ig.dv.qsession
  let { RELATIVE_FRONTIER_CBALL, .. } := D.ra.ts.cn.ms.ig.dv.dg.qconvex
  let { ARC_SIMPLE_PATH, BOUNDED_PATH_IMAGE, COMPACT_PATH_IMAGE, FINITE_SPHERE,
        HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT, HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths1
  let { HOMOTOPY_EQUIVALENT_SYM, HOMOTOPY_EQUIVALENT_TRANS, INTERIOR_SIMPLE_PATH_IMAGE,
        PATH_CONNECTED_IMP_CONNECTED, SIMPLE_PATH_IMP_PATH,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths2
  let { COMPL_COMPL, IMAGE_DIFF_INJ_ALT, .. } := D.ra.ts.cn.ms.ig.dv.dg.qsession
  let { CONNECTED_UNIV, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { OPEN_IN_DIFF_CLOSED, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology2
  let { AFF_DIM_CONVEX_HULL, AFF_DIM_DIM_0, AFF_DIM_SEGMENT, AFF_DIM_UNIV,
        BOUNDED_CONVEX_HULL_EQ, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx1
  let { COMPACT_CONVEX_HULL, CONVEX_CBALL, CONVEX_CONVEX_HULL,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  -- @@SCOPE END

  let HOMOTOPY_EQUIVALENT_SEPARATION_SPHERE ← prove
   r"!s t:real^N->bool a r.
      s SUBSET sphere(a,r) /\ t SUBSET sphere(a,r) /\
      compact s /\ compact t /\ s homotopy_equivalent t
      ==> (connected (sphere(a,r) DIFF s) <=> connected(sphere(a,r) DIFF t))"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"FINITE(sphere(a:real^N,r))") THENL
     [REWRITE_TAC [CONNECTED_EQ_CARD_COMPONENTS] THEN
      SUBGOAL_THEN (← q r"FINITE(s:real^N->bool) /\ FINITE(t:real^N->bool)")
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [FINITE_SUBSET], ALL_TAC] THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP HOMOTOPY_EQUIVALENT_CARD_EQ_COMPONENTS) THEN
      ASM_SIMP_TAC [FINITE_IMP_TOTALLY_DISCONNECTED, FINITE_DIFF, FINITE_IMAGE,
                    CARD_IMAGE_INJ, ← SET_RULE (← q r"{a} = {b} <=> a = b")] THEN
      W (MP_TAC o PART_MATCH (lhand o rand)
        CARD_EQ_IMAGE o rand o lhand o snd) THEN
      W (MP_TAC o PART_MATCH (lhand o rand)
        CARD_EQ_IMAGE o lhand o lhand o rand o snd) THEN
      SIMP_TAC [← SET_RULE (← q r"{a} = {b} <=> a = b")] THEN
      GEN_REWRITE_TAC LAND_CONV [CARD_EQ_SYM] THEN
      ONCE_REWRITE_TAC [← TAUT (← q r"p ==> q ==> r ==> s <=> p /\ r ==> q ==> s")] THEN
      DISCH_THEN (MP_TAC o MATCH_MP CARD_EQ_TRANS) THEN
      REWRITE_TAC [IMP_IMP] THEN
      DISCH_THEN (ASSUME_TAC o MATCH_MP CARD_EQ_TRANS) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC [CARD_DIFF] THEN
      MATCH_MP_TAC (← ARITH_RULE
       (← q r"m:num <= n /\ p <= n /\ m = p ==> n - m = n - p")) THEN
      ASM_SIMP_TAC [CARD_SUBSET] THEN MATCH_MP_TAC CARD_EQ_CARD_IMP THEN
      ASM_REWRITE_TAC [],
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [FINITE_SPHERE]) THEN
      REWRITE_TAC [DE_MORGAN_THM, REAL_NOT_LE] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o MATCH_MP (← ARITH_RULE
       (← q r"~(n = 1) ==> 1 <= n ==> 2 <= n"))) THEN
      REWRITE_TAC [DIMINDEX_GE_1] THEN DISCH_TAC] THEN
    ASM_CASES_TAC (← q r"dimindex(:N) = 2") THENL
     [ASM_SIMP_TAC [CONNECTED_COMPLEMENT_SUBSET_CIRCLE] THEN
      MATCH_MP_TAC HOMOTOPY_EQUIVALENT_CONNECTEDNESS THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"s PSUBSET sphere(a:real^N,r) <=> t PSUBSET sphere(a:real^N,r)")
    ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"t:real^N->bool"]
        HOMOTOPY_EQUIVALENT_SEPARATION) THEN
      ASM_REWRITE_TAC [] THEN
      MP_TAC (← ISPECL [← q r"sphere(a:real^N,r)", ← q r"s:real^N->bool", ← q r"a:real^N", ← q r"r:real"]
        JORDAN_BROUWER_NONSEPARATION) THEN
      MP_TAC (← ISPECL [← q r"sphere(a:real^N,r)", ← q r"t:real^N->bool", ← q r"a:real^N", ← q r"r:real"]
        JORDAN_BROUWER_NONSEPARATION) THEN
      MP_TAC (← ISPECL [← q r"sphere(a:real^N,r)", ← q r"a:real^N", ← q r"r:real"]
        JORDAN_BROUWER_SEPARATION) THEN
      ASM_REWRITE_TAC [HOMEOMORPHIC_REFL] THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP (← SET_RULE
       (← q r"s SUBSET t ==> s PSUBSET t \/ s = t")))) THEN
      MESON_TAC [],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP (← SET_RULE
     (← q r"(s PSUBSET u <=> t PSUBSET u)
      ==> s SUBSET u /\ t SUBSET u
          ==> s = u /\ t = u \/ s PSUBSET u /\ t PSUBSET u"))) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [DIFF_EQ_EMPTY] THEN
    SUBGOAL_THEN
    (← q r"?w z:real^N. w IN sphere(a,r) /\ z IN sphere(a,r) /\ ~(w IN s) /\ ~(z IN t)")
    STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"(sphere(a:real^N,r) DELETE w) homeomorphic (:real^(N,1)finite_diff)")
    MP_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHIC_PUNCTURED_SPHERE_UNIV THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [DIMINDEX_FINITE_DIFF, DIMINDEX_1] THEN ASM_ARITH_TAC,
      REWRITE_TAC [homeomorphic, LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"f:real^N->real^(N,1)finite_diff", ← q r"g:real^(N,1)finite_diff->real^N"] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"(sphere(a:real^N,r) DELETE z) homeomorphic (:real^(N,1)finite_diff)")
    MP_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHIC_PUNCTURED_SPHERE_UNIV THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [DIMINDEX_FINITE_DIFF, DIMINDEX_1] THEN ASM_ARITH_TAC,
      REWRITE_TAC [homeomorphic, LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"h:real^N->real^(N,1)finite_diff", ← q r"k:real^(N,1)finite_diff->real^N"] THEN
    DISCH_TAC THEN
    MP_TAC (← ISPECL
      [← q r"IMAGE (f:real^N->real^(N,1)finite_diff) s",
       ← q r"IMAGE (h:real^N->real^(N,1)finite_diff) t"]
      HOMOTOPY_EQUIVALENT_SEPARATION) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL
       [ASM_MESON_TAC [HOMEOMORPHISM_COMPACTNESS,
          ← SET_RULE (← q r"s SUBSET t /\ ~(a IN s) ==> s SUBSET t DELETE a")],
        TRANS_TAC HOMOTOPY_EQUIVALENT_TRANS (← q r"s:real^N->bool") THEN CONJ_TAC THENL
         [ALL_TAC,
          TRANS_TAC HOMOTOPY_EQUIVALENT_TRANS (← q r"t:real^N->bool") THEN
          ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [HOMOTOPY_EQUIVALENT_SYM]] THEN
        MATCH_MP_TAC HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT THEN
        MATCH_MP_TAC HOMEOMORPHIC_SELF_IMAGE THEN
        ASM_MESON_TAC [← SET_RULE
         (← q r"s SUBSET t /\ ~(a IN s) ==> s SUBSET t DELETE a")]],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"UNIV DIFF IMAGE (f:real^N->real^(N,1)finite_diff) s =
      IMAGE f ((sphere(a,r) DELETE w) DIFF s) /\
      UNIV DIFF IMAGE (h:real^N->real^(N,1)finite_diff) t =
      IMAGE h ((sphere(a,r) DELETE z) DIFF t)")
     (fun th => REWRITE_TAC [th])
    THENL
     [CONJ_TAC THEN
      MATCH_MP_TAC (← SET_RULE
       (← q r"IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t /\
        IMAGE f s DIFF IMAGE f t = u
        ==> u = IMAGE f (s DIFF t)")) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [homeomorphism, IN_UNIV]) THEN
      (CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []]) THEN
      MATCH_MP_TAC IMAGE_DIFF_INJ_ALT THEN
      ASM_REWRITE_TAC [INJECTIVE_ON_LEFT_INVERSE, SUBSET_DELETE] THEN
      ASM_MESON_TAC [],
      MATCH_MP_TAC EQ_IMP] THEN
    BINOP_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do
     pure (W (MP_TAC o PART_MATCH (lhand o rand)
     (← MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ] HOMEOMORPHISM_CONNECTEDNESS) th) o
     lhand o snd))) THEN
    REWRITE_TAC [SUBSET_DIFF] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [← SET_RULE (← q r"s DELETE a DIFF t = (s DIFF t) DELETE a")] THEN
    MATCH_MP_TAC CONNECTED_OPEN_IN_SPHERE_DELETE_EQ THEN
    MAP_EVERY EXISTS_TAC [← q r"a:real^N", ← q r"r:real"] THEN
    ASM_SIMP_TAC [OPEN_IN_DIFF_CLOSED, COMPACT_IMP_CLOSED] THEN
    ASM_ARITH_TAC)

  let CONNECTED_COMPLEMENT_CONTRACTIBLE ← prove
   r"!s. 2 <= dimindex(:N) /\ compact s /\ contractible s
       ==> connected((:real^N) DIFF s)"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"s:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [DIFF_EMPTY, CONNECTED_UNIV] THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"{a:real^N}"]
          HOMOTOPY_EQUIVALENT_SEPARATION) THEN
    ASM_SIMP_TAC [HOMOTOPY_EQUIVALENT_SING, COMPACT_SING, AR_SING,
                  CONNECTED_COMPLEMENT_ABSOLUTE_RETRACT])

  let CONNECTED_COMPLEMENT_SIMPLE_PATH_IMAGE ← prove
   r"!g. 3 <= dimindex(:N) /\ simple_path g
       ==> connected((:real^N) DIFF path_image g)"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"arc(g:real^1->real^N)") THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"3 <= n ==> 2 <= n"), CONNECTED_ARC_COMPLEMENT] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [ARC_SIMPLE_PATH]) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MP_TAC (← ISPECL
     [← q r"path_image g:real^N->bool",
      ← q r"relative_frontier(convex hull {vec 0:real^N,basis 1,basis 2})"]
      HOMOTOPY_EQUIVALENT_SEPARATION) THEN
    ASM_SIMP_TAC [COMPACT_PATH_IMAGE, SIMPLE_PATH_IMP_PATH] THEN
    SIMP_TAC [COMPACT_RELATIVE_FRONTIER, COMPACT_CONVEX_HULL,
              FINITE_IMP_COMPACT, FINITE_INSERT, FINITE_EMPTY] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT THEN
      TRANS_TAC HOMEOMORPHIC_TRANS
       (← q r"relative_frontier(cball(vec 0:real^2,&1))") THEN
      CONJ_TAC THENL
       [SIMP_TAC [RELATIVE_FRONTIER_CBALL, REAL_OF_NUM_EQ, ARITH_EQ] THEN
        ASM_SIMP_TAC [HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE, REAL_LT_01],
        MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
        REWRITE_TAC [CONVEX_CBALL, BOUNDED_CBALL, CONVEX_CONVEX_HULL] THEN
        REWRITE_TAC [BOUNDED_CONVEX_HULL_EQ, BOUNDED_INSERT, BOUNDED_EMPTY] THEN
        REWRITE_TAC [AFF_DIM_CBALL, REAL_LT_01] THEN CONV_TAC SYM_CONV THEN
        REWRITE_TAC [AFF_DIM_CONVEX_HULL, DIMINDEX_2] THEN
        SIMP_TAC [AFF_DIM_DIM_0, HULL_INC, IN_INSERT, INT_OF_NUM_EQ] THEN
        REWRITE_TAC [DIM_INSERT_0] THEN
        REWRITE_TAC [DIM_INSERT, SPAN_SING, DIM_SING, SPAN_EMPTY, IN_SING] THEN
        ASM_SIMP_TAC [BASIS_NONZERO, DIMINDEX_2, ARITH, DIM_EMPTY,
                      ← ARITH_RULE (← q r"3 <= n ==> 2 <= n")] THEN
        REWRITE_TAC [IN_ELIM_THM, IN_UNIV] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
        FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"u:real") MP_TAC) THEN
        DISCH_THEN (MP_TAC o AP_TERM (← q r"\x:real^N. x$1")) THEN
        ASM_SIMP_TAC [BASIS_COMPONENT, VECTOR_MUL_COMPONENT, ARITH,
                      ← ARITH_RULE (← q r"3 <= n ==> 1 <= n /\ 2 <= n")] THEN
        REAL_ARITH_TAC],
      DISCH_THEN SUBST1_TAC] THEN
    W (MP_TAC o PART_MATCH (lhand o rand) RELATIVE_FRONTIER_OF_TRIANGLE o
      rand o rand o snd) THEN
    ASM_SIMP_TAC [COLLINEAR_LEMMA, BASIS_NONZERO, DIMINDEX_2, ARITH, DIM_EMPTY,
                  ← ARITH_RULE (← q r"3 <= n ==> 1 <= n /\ 2 <= n")] THEN
    ANTS_TAC THENL
     [DISCH_THEN (CHOOSE_THEN (MP_TAC o AP_TERM (← q r"\x:real^N. x$2"))) THEN
      ASM_SIMP_TAC [BASIS_COMPONENT, VECTOR_MUL_COMPONENT, ARITH,
                    ← ARITH_RULE (← q r"3 <= n ==> 1 <= n /\ 2 <= n")] THEN
      REAL_ARITH_TAC,
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC [← SET_RULE (← q r"a UNION b UNION c = UNIONS {a,b,c}")] THEN
    MATCH_MP_TAC PATH_CONNECTED_IMP_CONNECTED THEN
    MATCH_MP_TAC PATH_CONNECTED_OPEN_IN_DIFF_UNIONS_LOWDIM THEN
    REWRITE_TAC [CONNECTED_UNIV, AFFINE_HULL_UNIV, OPEN_IN_REFL] THEN
    REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY, FORALL_IN_INSERT] THEN
    REWRITE_TAC [NOT_IN_EMPTY, CLOSED_SEGMENT, AFF_DIM_SEGMENT] THEN
    REWRITE_TAC [AFF_DIM_UNIV] THEN
    REPEAT CONJ_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [INT_OF_NUM_LE] THEN
    ASM_ARITH_TAC)

  let PATH_CONNECTED_PSUPERSET_COMPLEMENT_SIMPLE_PATH_IMAGE ← prove
   r"!g s:real^N->bool.
        2 <= dimindex(:N) /\ simple_path g /\
        (:real^N) DIFF path_image g PSUBSET s
        ==> path_connected s"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"arc(g:real^1->real^N)") THENL
     [MATCH_MP_TAC PATH_CONNECTED_SUPERSET_COMPLEMENT_ARC_IMAGE THEN
      ASM_MESON_TAC [PSUBSET],
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [ARC_SIMPLE_PATH]) THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC] THEN
    ASM_CASES_TAC (← q r"3 <= dimindex(:N)") THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC
       PATH_CONNECTED_INTERMEDIATE_CLOSURE_ANR_COMPLEMENT_COMPONENT THEN
      EXISTS_TAC (← q r"path_image g:real^N->bool") THEN
      EXISTS_TAC (← q r"(:real^N) DIFF path_image g") THEN
      ASM_SIMP_TAC [COMPACT_PATH_IMAGE, SIMPLE_PATH_IMP_PATH] THEN
      ASM_SIMP_TAC [ANR_PATH_IMAGE_SIMPLE_PATH, IN_COMPONENTS_SELF] THEN
      ASM_SIMP_TAC [CONNECTED_COMPLEMENT_SIMPLE_PATH_IMAGE] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC [← SET_RULE (← q r"s DIFF t = {} <=> s SUBSET t")] THEN
        ASM_MESON_TAC [SIMPLE_PATH_IMP_PATH, BOUNDED_PATH_IMAGE, BOUNDED_SUBSET,
                       NOT_BOUNDED_UNIV],
        ASM SET_TAC [],
        REWRITE_TAC [CLOSURE_COMPLEMENT] THEN
        ASM_SIMP_TAC [INTERIOR_SIMPLE_PATH_IMAGE] THEN SET_TAC []],
      GEN_REWRITE_TAC RAND_CONV [← GSYM COMPL_COMPL] THEN
      MATCH_MP_TAC JORDAN_BROUWER_NONSEPARATION_STRONG THEN
      MAP_EVERY EXISTS_TAC
       [← q r"path_image g:real^N->bool", ← q r"vec 0:real^N", ← q r"&1"] THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      TRANS_TAC HOMEOMORPHIC_TRANS (← q r"sphere(vec 0:real^2,&1)") THEN
      ASM_SIMP_TAC [HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE, REAL_LT_01] THEN
      REWRITE_TAC [← GSYM
       (← CONV_RULE REAL_RAT_REDUCE_CONV
         (← ISPECL [← q r"x:real^N", ← q r"&1"] RELATIVE_FRONTIER_CBALL))] THEN
      MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
      REWRITE_TAC [CONVEX_CBALL, BOUNDED_CBALL, AFF_DIM_CBALL] THEN
      REWRITE_TAC [REAL_LT_01, INT_OF_NUM_EQ, DIMINDEX_2] THEN ASM_ARITH_TAC])

  pure { HOMOTOPY_EQUIVALENT_SEPARATION_SPHERE, CONNECTED_COMPLEMENT_CONTRACTIBLE,
         CONNECTED_COMPLEMENT_SIMPLE_PATH_IMAGE,
         PATH_CONNECTED_PSUPERSET_COMPLEMENT_SIMPLE_PATH_IMAGE }
/- ------------------------------------------------------------------------- -/
/- A few additional invariance of domain/dimension corollaries; the          -/
/- exponential function as a covering map.                                   -/
/- (moretop.ml 4635-4800)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MON where
  REAL_CONTINUOUS_ON_INVERSE : thm
  REAL_CONTINUOUS_ON_INVERSE_ALT : thm
  SIMPLY_CONNECTED_SPHERE_EQ : thm
  SIMPLY_CONNECTED_PUNCTURED_UNIVERSE_EQ : thm
  NOT_SIMPLY_CONNECTED_CIRCLE : thm
  COVERING_SPACE_CEXP_PUNCTURED_PLANE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMON [HolBase] (D : MoreTopDeps) (BMOC : MOC) : ExceptT String IO MON := do
  -- @@SCOPE BEGIN
  let { SIMPLY_CONNECTED_SPHERE, .. } := BMOC
  let { real_compact, REAL_OPEN, .. } := D.rza
  let { REAL_CONTINUOUS_ON, .. } := D.rzj
  let { OPEN_TRANSLATION, .. } := D.qtopology
  let { CONNECTED_SPHERE_EQ, CONTINUOUS_ON_INVERSE_INTO_1D, CONVEX_IMP_SIMPLY_CONNECTED,
        covering_space, HOMEOMORPHIC_SIMPLY_CONNECTED_EQ, INVARIANCE_OF_DOMAIN,
        SIMPLY_CONNECTED_EMPTY, SIMPLY_CONNECTED_IMP_CONNECTED, .. } := D.qpaths
  let { CONTRACTIBLE_SPHERE, HOMOTOPY_EQUIVALENT_RELATIVE_FRONTIER_PUNCTURED_AFFINE_HULL,
        .. } := D.qdegree
  let { CEXP_ADD, CEXP_NZ, CONTINUOUS_ON_CEXP, .. } := D.ra.tsa
  let { PI_POS, REAL_ABS_PI, .. } := D.ra.tse
  let { CEXP_EQ, CEXP_INTEGER_2PI, COMPLEX_EQ_CEXP, .. } := D.ra.tsf
  let { PI_APPROX_32, .. } := D.ra.tsl
  let { CEXP_CLOG, .. } := D.ra.tsm
  let { HOMOTOPY_EQUIVALENT_SIMPLE_CONNECTEDNESS,
        SIMPLY_CONNECTED_EQ_CONTRACTIBLE_CIRCLEMAP, .. } := D.ra.tsad
  let { IS_REALINTERVAL_IS_INTERVAL, .. } := D.ra.qtopology
  let { COMPLEX_MUL_RID, COMPLEX_SUB_RDISTRIB, .. } := D.ra.ts.cn.cxb
  let { COMPLEX_NORM_CX, COMPLEX_NORM_II, CX_SUB, IM_SUB, .. } := D.ra.ts.cn.cxc
  let { COMPLEX_NORM_MUL, .. } := D.ra.ts.cn.cxf
  let { COMPLEX_NORM_GE_RE_IM, .. } := D.ra.ts.cn.cxg
  let { REAL_ABS_INTEGER_LEMMA, .. } := D.ra.ts.cn.ms.qfloor
  let { ARITH_RULE, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, GEOM_EQUAL_DIMENSION_RULE,
        MESON_TAC, NORM_ARITH, REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV, SET_RULE, SET_TAC,
        .. } := D.ra.ts.cn.cx.cvx
  let { INTEGER_CLOSED, .. } := D.ra.ts.cn.ms.ig.qfloor
  let { IS_INTERVAL_PATH_CONNECTED_1, .. } := D.ra.ts.cn.ms.ig.qpaths
  let { ARITH, CONTRAPOS_THM, DIMINDEX_2, DIMINDEX_GE_1, EQ_SYM_EQ, EQ_TRANS,
        FORALL_IN_GSPEC, .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, IMAGE_ID, IMAGE_o, IMAGE_SUBSET, IMP_CONJ, IN_DIFF,
        INJECTIVE_ON_ALT, .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_IMAGE, IN_SING, IN_UNIV, LEFT_IMP_EXISTS_THM, REAL_ABS_MUL, REAL_ABS_NUM,
        .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_LE_LMUL, REAL_LE_LT, REAL_LE_REFL, REAL_LE_RMUL_EQ, REAL_LE_TRANS,
        REAL_LET_TRANS, REAL_LT_01, REAL_LT_IMP_LE, .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_RID, REAL_OF_NUM_LE, REAL_POS, REAL_SUB_0, REAL_SUB_LDISTRIB,
        REAL_SUB_RDISTRIB, RIGHT_FORALL_IMP_THM, SUBSET, SUBSET_REFL,
        .. } := D.ra.ts.cn.cx.cvx.core5
  let { o_DEF, o_THM, pairwise, SUBSET_UNIV, UNIONS_GSPEC, .. } := D.ra.ts.cn.cx.cvx.core6
  let { LIFT_DROP, .. } := D.ra.ts.cn.cx.cvx.vec2
  let { dist, VECTOR_ADD_SYM, .. } := D.ra.ts.cn.cx.cvx.vec4
  let { BALL_EQ_EMPTY, BALL_SUBSET_CBALL, BOUNDED_CBALL, CENTRE_IN_BALL, CLOSED_SING,
        .. } := D.ra.ts.cn.cx.cvx.top1
  let { COMPACT_CBALL, .. } := D.ra.ts.cn.cx.cvx.top2
  let { CONTINUOUS_ON_ADD, CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_CONST, CONTINUOUS_ON_ID,
        CONTINUOUS_ON_SUBSET, .. } := D.ra.ts.cn.cx.cvx.top3
  let { HOMEOMORPHISM_COMPACT, IN_BALL, IN_CBALL, INTERIOR_CBALL, OPEN_BALL,
        .. } := D.ra.ts.cn.cx.cvx.top4
  let { homeomorphism, OPEN_IN_OPEN_EQ, OPEN_UNIV, SPHERE_EMPTY,
        .. } := D.ra.ts.cn.cx.cvx.top5
  let { AFFINE_HULL_NONEMPTY_INTERIOR, RELATIVE_FRONTIER_CBALL,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qconvex
  let { contractible, .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths2
  let { HOMEOMORPHIC_SPHERES, OPEN_DIFF, SPHERE_SING,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology2
  let { CONVEX_CBALL, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  let { CONVEX_SING, RELATIVE_INTERIOR_CBALL, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx3
  -- @@SCOPE END

  let REAL_CONTINUOUS_ON_INVERSE ← prove
   r"!f g s. f real_continuous_on s /\
           (is_realinterval s \/ real_compact s \/ real_open s) /\
           (!x. x IN s ==> g(f x) = x)
           ==> g real_continuous_on (IMAGE f s)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [REAL_CONTINUOUS_ON, real_compact, REAL_OPEN,
                 IS_REALINTERVAL_IS_INTERVAL] THEN
    DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_INVERSE_INTO_1D THEN
    MAP_EVERY EXISTS_TAC [← q r"lift o f o drop", ← q r"IMAGE lift s"] THEN
    ASM_REWRITE_TAC [← GSYM IS_INTERVAL_PATH_CONNECTED_1] THEN
    ASM_SIMP_TAC [FORALL_IN_IMAGE, o_DEF, LIFT_DROP, ← GSYM IMAGE_o] THEN
    ASM_MESON_TAC [])

  let REAL_CONTINUOUS_ON_INVERSE_ALT ← prove
   r"!f g s t. f real_continuous_on s /\
             (is_realinterval s \/ real_compact s \/ real_open s) /\
             IMAGE f s = t /\ (!x. x IN s ==> g(f x) = x)
           ==> g real_continuous_on t"
   (MESON_TAC [REAL_CONTINUOUS_ON_INVERSE])

  let SIMPLY_CONNECTED_SPHERE_EQ ← (do
    let hslemma ← prove
     r"!a:real^M r b:real^N s.
          dimindex(:M) = dimindex(:N)
          ==> &0 < r /\ &0 < s  ==> (sphere(a,r) homeomorphic sphere(b,s))"
     (REPEAT STRIP_TAC THEN FIRST_ASSUM (fun th => tactic_of do
        let t ← q r"?a:real^M b:real^N. ~(sphere(a,r) homeomorphic sphere(b,s))"
        pure (MP_TAC (← DISCH t (← GEOM_EQUAL_DIMENSION_RULE th (← ASSUME t))))) THEN
      ASM_SIMP_TAC [HOMEOMORPHIC_SPHERES] THEN MESON_TAC [])
    prove
     r"!a:real^N r.
          simply_connected(sphere(a,r)) <=> 3 <= dimindex(:N) \/ r <= &0"
     (REPEAT GEN_TAC THEN
      ASM_CASES_TAC (← q r"r < &0") THEN
      ASM_SIMP_TAC [SPHERE_EMPTY, REAL_LT_IMP_LE, SIMPLY_CONNECTED_EMPTY] THEN
      ASM_CASES_TAC (← q r"r = &0") THEN
      ASM_SIMP_TAC [SPHERE_SING, REAL_LE_REFL, CONVEX_IMP_SIMPLY_CONNECTED,
                    CONVEX_SING] THEN
      ASM_REWRITE_TAC [REAL_LE_LT] THEN
      EQ_TAC THEN REWRITE_TAC [SIMPLY_CONNECTED_SPHERE] THEN
      ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC [← ARITH_RULE (← q r"~(3 <= n) <=> (1 <= n ==> n = 1 \/ n = 2)")] THEN
      REWRITE_TAC [DIMINDEX_GE_1] THEN STRIP_TAC THENL
       [DISCH_THEN (MP_TAC o MATCH_MP SIMPLY_CONNECTED_IMP_CONNECTED) THEN
        ASM_REWRITE_TAC [CONNECTED_SPHERE_EQ, ARITH] THEN ASM_REAL_ARITH_TAC,
        RULE_ASSUM_TAC (REWRITE_RULE [← GSYM DIMINDEX_2]) THEN
        FIRST_ASSUM (MP_TAC o ISPECL [← q r"a:real^N", ← q r"r:real", ← q r"vec 0:real^2",
              ← q r"&1:real"] o MATCH_MP hslemma) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
        DISCH_THEN (SUBST1_TAC o MATCH_MP HOMEOMORPHIC_SIMPLY_CONNECTED_EQ) THEN
        REWRITE_TAC [SIMPLY_CONNECTED_EQ_CONTRACTIBLE_CIRCLEMAP] THEN
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"\x:real^2. x")) THEN
        REWRITE_TAC [CONTINUOUS_ON_ID, IMAGE_ID, SUBSET_REFL] THEN
        REWRITE_TAC [← GSYM contractible, CONTRACTIBLE_SPHERE] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV]))

  let SIMPLY_CONNECTED_PUNCTURED_UNIVERSE_EQ ← prove
   r"!a. simply_connected((:real^N) DELETE a) <=> 3 <= dimindex(:N)"
   (GEN_TAC THEN TRANS_TAC EQ_TRANS (← q r"simply_connected(sphere(a:real^N,&1))") THEN
    CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [SIMPLY_CONNECTED_SPHERE_EQ]] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    MATCH_MP_TAC HOMOTOPY_EQUIVALENT_SIMPLE_CONNECTEDNESS THEN
    MP_TAC (← ISPECL [← q r"cball(a:real^N,&1)", ← q r"a:real^N"]
          HOMOTOPY_EQUIVALENT_RELATIVE_FRONTIER_PUNCTURED_AFFINE_HULL) THEN
    REWRITE_TAC [CONVEX_CBALL, BOUNDED_CBALL, RELATIVE_INTERIOR_CBALL,
                 RELATIVE_FRONTIER_CBALL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC [CENTRE_IN_BALL, AFFINE_HULL_NONEMPTY_INTERIOR, INTERIOR_CBALL,
              BALL_EQ_EMPTY, REAL_OF_NUM_LE, ARITH, REAL_LT_01])

  let NOT_SIMPLY_CONNECTED_CIRCLE ← prove
   r"!a:real^2 r. &0 < r ==> ~simply_connected(sphere(a,r))"
   (REWRITE_TAC [SIMPLY_CONNECTED_SPHERE_EQ, DIMINDEX_2, ARITH] THEN
    REAL_ARITH_TAC)

  -- The exponential function as a covering map.

  let COVERING_SPACE_CEXP_PUNCTURED_PLANE ← prove
   r"covering_space((:complex),cexp) ((:complex) DIFF {Cx(&0)})"
   (SIMP_TAC [covering_space, IN_UNIV, CONTINUOUS_ON_CEXP, IN_DIFF, IN_SING] THEN
    CONJ_TAC THENL [SET_TAC [CEXP_CLOG, CEXP_NZ], ALL_TAC] THEN
    SIMP_TAC [OPEN_IN_OPEN_EQ, OPEN_DIFF, OPEN_UNIV, CLOSED_SING] THEN
    SIMP_TAC [SUBSET_UNIV, ← SET_RULE (← q r"s SUBSET UNIV DIFF {a} <=> ~(a IN s)")] THEN
    X_GEN_TAC (← q r"z:complex") THEN DISCH_TAC THEN
    EXISTS_TAC (← q r"IMAGE cexp (ball(clog z,&1))") THEN
    REWRITE_TAC [← SET_RULE (← q r"~(z IN IMAGE f s) <=> !x. x IN s ==> ~(f x = z)")] THEN
    REWRITE_TAC [CEXP_NZ] THEN CONJ_TAC THENL
     [REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"clog z") THEN
      ASM_SIMP_TAC [CEXP_CLOG, CENTRE_IN_BALL, REAL_LT_01],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!x y. x IN cball(clog z,&1) /\ y IN cball(clog z,&1) /\ cexp x = cexp y
            ==> x = y")
    ASSUME_TAC THENL
     [REWRITE_TAC [IN_CBALL] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC COMPLEX_EQ_CEXP THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q r"norm(x - y:complex)") THEN
      REWRITE_TAC [← GSYM IM_SUB, COMPLEX_NORM_GE_RE_IM] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q r"&2") THEN CONJ_TAC THENL
       [REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC (fun t => NORM_ARITH t),
        MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC],
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN
      REWRITE_TAC [OPEN_BALL, CONTINUOUS_ON_CEXP] THEN
      ASM_MESON_TAC [SUBSET, BALL_SUBSET_CBALL],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"cball(clog z,&1)", ← q r"cexp",
                     ← q r"IMAGE cexp (cball(clog z,&1))"] HOMEOMORPHISM_COMPACT) THEN
    ASM_REWRITE_TAC [COMPACT_CBALL, CONTINUOUS_ON_CEXP] THEN
    REWRITE_TAC [homeomorphism, LEFT_IMP_EXISTS_THM, FORALL_IN_IMAGE] THEN
    X_GEN_TAC (← q r"l:complex->complex") THEN STRIP_TAC THEN
    EXISTS_TAC (← q r"{ IMAGE (\x. x + Cx (&2 * n * pi) * ii)
                        (ball(clog z,&1))
                  | integer n}") THEN
    SIMP_TAC [FORALL_IN_GSPEC, OPEN_BALL,
              ← ONCE_REWRITE_RULE [VECTOR_ADD_SYM] OPEN_TRANSLATION] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [UNIONS_GSPEC, IN_IMAGE, CEXP_EQ] THEN SET_TAC [],
      REWRITE_TAC [pairwise, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC [FORALL_IN_GSPEC] THEN
      X_GEN_TAC (← q r"m:real") THEN DISCH_TAC THEN
      X_GEN_TAC (← q r"n:real") THEN DISCH_TAC THEN
      ASM_CASES_TAC (← q r"m:real = n") THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
      REWRITE_TAC [IN_BALL, dist, ← SET_RULE
       (← q r"DISJOINT (IMAGE f s) (IMAGE g s) <=>
        !x y. x IN s /\ y IN s ==> ~(f x = g y)")] THEN
      REPEAT GEN_TAC THEN MATCH_MP_TAC (← NORM_ARITH
       (← q r"&2 <= norm(m - n)
        ==> norm(c - x) < &1 /\ norm(c - y) < &1 ==> ~(x + m = y + n)")) THEN
      REWRITE_TAC [← GSYM COMPLEX_SUB_RDISTRIB, COMPLEX_NORM_MUL] THEN
      REWRITE_TAC [COMPLEX_NORM_II, ← GSYM CX_SUB, COMPLEX_NORM_CX] THEN
      REWRITE_TAC [← GSYM REAL_SUB_LDISTRIB, ← GSYM REAL_SUB_RDISTRIB] THEN
      REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_NUM, REAL_ABS_PI, REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"&2 * &1 * pi") THEN
      CONJ_TAC THENL [MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC, ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      SIMP_TAC [REAL_LE_RMUL_EQ, PI_POS, REAL_POS] THEN
      MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN
      ASM_SIMP_TAC [REAL_SUB_0, INTEGER_CLOSED],
      X_GEN_TAC (← q r"n:real") THEN DISCH_TAC THEN
      EXISTS_TAC (← q r"(\x. x + Cx(&2 * n * pi) * ii) o (l:complex->complex)") THEN
      ASM_REWRITE_TAC [CONTINUOUS_ON_CEXP, o_THM, IMAGE_o, FORALL_IN_IMAGE] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [INJECTIVE_ON_ALT]) THEN
      ASM_SIMP_TAC [CEXP_ADD, CEXP_INTEGER_2PI, COMPLEX_MUL_RID,
                    ← REWRITE_RULE [SUBSET] BALL_SUBSET_CBALL] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC (← SET_RULE
         (← q r"(!x. e(f x) = e x) ==> IMAGE e (IMAGE f s) = IMAGE e s")) THEN
        ASM_SIMP_TAC [CEXP_ADD, CEXP_INTEGER_2PI, COMPLEX_MUL_RID],
        MATCH_MP_TAC (← SET_RULE
         (← q r"(!x. x IN s ==> l(e x) = x)
          ==> IMAGE t (IMAGE l (IMAGE e s)) = IMAGE t s")) THEN
        ASM_SIMP_TAC [← REWRITE_RULE [SUBSET] BALL_SUBSET_CBALL],
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC [CONTINUOUS_ON_ADD, CONTINUOUS_ON_ID,
                  CONTINUOUS_ON_CONST] THEN
        ASM_MESON_TAC [BALL_SUBSET_CBALL, IMAGE_SUBSET,
                       CONTINUOUS_ON_SUBSET]]])

  pure { REAL_CONTINUOUS_ON_INVERSE, REAL_CONTINUOUS_ON_INVERSE_ALT,
         SIMPLY_CONNECTED_SPHERE_EQ, SIMPLY_CONNECTED_PUNCTURED_UNIVERSE_EQ,
         NOT_SIMPLY_CONNECTED_CIRCLE, COVERING_SPACE_CEXP_PUNCTURED_PLANE }
/- ------------------------------------------------------------------------- -/
/- Hence the Borsukian results about mappings into circle.                   -/
/- (moretop.ml 4801-4970)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MOO where
  INESSENTIAL_EQ_CONTINUOUS_LOGARITHM : thm
  INESSENTIAL_IMP_CONTINUOUS_LOGARITHM_CIRCLE : thm
  INESSENTIAL_EQ_CONTINUOUS_LOGARITHM_CIRCLE : thm
  HOMOTOPIC_CIRCLEMAPS_DIV : thm
  HOMOTOPIC_CIRCLEMAPS_DIV_1 : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOO [HolBase] (D : MoreTopDeps) (BMON : MON) : ExceptT String IO MOO := do
  -- @@SCOPE BEGIN
  let { COVERING_SPACE_CEXP_PUNCTURED_PLANE, .. } := BMON
  let { COVERING_SPACE_LIFT_INESSENTIAL_FUNCTION, NULLHOMOTOPIC_THROUGH_CONTRACTIBLE,
        PATH_CONNECTED_SPHERE, STARLIKE_IMP_CONTRACTIBLE, .. } := D.qpaths
  let { CONVEX_IMP_STARLIKE, STARLIKE_UNIV, .. } := D.qconvex
  let { CEXP_NZ, CONTINUOUS_ON_CEXP, .. } := D.ra.tsa
  let { REAL_EXP_0, .. } := D.ra.tsb
  let { EULER, .. } := D.ra.tsc
  let { NORM_CEXP, .. } := D.ra.tsf
  let { CONVEX_STANDARD_HYPERPLANE, .. } := D.ra.qconvex
  let { CONTINUOUS_ON_COMPLEX_INV, CONTINUOUS_ON_COMPLEX_LMUL, CONTINUOUS_ON_COMPLEX_MUL,
        .. } := D.ra.ts.knc
  let { CONTINUOUS_ON_CX_IM, .. } := D.ra.ts.knd
  let { sphere, .. } := D.ra.ts.qtopology
  let { complex_div, IM_DEF, .. } := D.ra.ts.cn.cxa
  let { COMPLEX_MUL_LID, .. } := D.ra.ts.cn.cxb
  let { COMPLEX_DIV_REFL, COMPLEX_MUL_RINV, COMPLEX_NORM_CX, IM_CX, IM_MUL_II, RE_CX,
        RE_MUL_II, .. } := D.ra.ts.cn.cxc
  let { COMPLEX_DIV_RMUL, COMPLEX_NORM_INV, COMPLEX_NORM_MUL, COMPLEX_NORM_ZERO,
        .. } := D.ra.ts.cn.cxf
  let { ASM_MESON_TAC, MESON_TAC, REAL_ARITH_TAC, SET_TAC, .. } := D.ra.ts.cn.cx.cvx
  let { AND_FORALL_THM, ARITH_EQ, CONJ_ASSOC, CONTRAPOS_THM, DIMINDEX_2, FORALL_IN_GSPEC,
        .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_IN_PCROSS, IMP_CONJ, IMP_CONJ_ALT, IN_DIFF,
        .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_SING, IN_UNIV, LE_REFL, LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY,
        MONO_EXISTS, REAL_ABS_NUM, .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_INV_1, .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_LID, REAL_NEG_0, REAL_OF_NUM_EQ, SNDCART_PASTECART, SUBSET, SUBSET_TRANS,
        .. } := D.ra.ts.cn.cx.cvx.core5
  let { o_ASSOC, o_DEF, o_THM, SUBSET_UNIV, .. } := D.ra.ts.cn.cx.cvx.core6
  let { DIST_0, .. } := D.ra.ts.cn.cx.cvx.vec1
  let { LINEAR_SNDCART, .. } := D.ra.ts.cn.cx.cvx.vec2
  let { CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_ID, .. } := D.ra.ts.cn.cx.cvx.top3
  let { IN_SPHERE_0, LINEAR_CONTINUOUS_ON, .. } := D.ra.ts.cn.cx.cvx.top4
  let { TOPSPACE_EUCLIDEAN_SUBTOPOLOGY, UNIT_INTERVAL_NONEMPTY,
        .. } := D.ra.ts.cn.cx.cvx.top5
  let { HOMOTOPIC_CONSTANT_MAPS, HOMOTOPIC_WITH_EQ, HOMOTOPIC_WITH_TRANS,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qmetric
  let { HOMOTOPIC_WITH_EUCLIDEAN, HOMOTOPIC_WITH_EUCLIDEAN_ALT,
        HOMOTOPIC_WITH_IMP_CONTINUOUS, HOMOTOPIC_WITH_IMP_SUBSET,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths1
  let { PATH_COMPONENT_OF_EUCLIDEAN, PATH_CONNECTED_IFF_PATH_COMPONENT,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths2
  let { IMAGE_SNDCART_PCROSS, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qses
  -- @@SCOPE END

  let INESSENTIAL_EQ_CONTINUOUS_LOGARITHM ← prove
   r"!f:real^N->complex s.
      (?a. homotopic_with (\h. T)
             (subtopology euclidean s,
              subtopology euclidean ((:complex) DIFF {Cx(&0)})) f (\t. a)) <=>
      (?g. g continuous_on s /\ (!x. x IN s ==> f x = cexp(g x)))"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (CHOOSE_THEN
       (MP_TAC o CONJ COVERING_SPACE_CEXP_PUNCTURED_PLANE)) THEN
      DISCH_THEN (MP_TAC o MATCH_MP COVERING_SPACE_LIFT_INESSENTIAL_FUNCTION) THEN
      REWRITE_TAC [SUBSET_UNIV] THEN MESON_TAC [],
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->complex") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       (← q r"?a. homotopic_with (\h. T)
                (subtopology euclidean s,
                 subtopology euclidean ((:complex) DIFF {Cx(&0)}))
                (cexp o g) (\x:real^N. a)")
      MP_TAC THENL
       [MATCH_MP_TAC NULLHOMOTOPIC_THROUGH_CONTRACTIBLE THEN
        EXISTS_TAC (← q r"(:complex)") THEN ASM_REWRITE_TAC [SUBSET_UNIV] THEN
        ASM_SIMP_TAC [STARLIKE_IMP_CONTRACTIBLE, STARLIKE_UNIV] THEN
        REWRITE_TAC [CONTINUOUS_ON_CEXP, SUBSET, FORALL_IN_IMAGE] THEN
        REWRITE_TAC [IN_UNIV, IN_DIFF, IN_SING, CEXP_NZ],
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:complex") THEN
        MATCH_MP_TAC (← ONCE_REWRITE_RULE [IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
        ASM_SIMP_TAC [TOPSPACE_EUCLIDEAN_SUBTOPOLOGY, o_THM]]])

  let INESSENTIAL_IMP_CONTINUOUS_LOGARITHM_CIRCLE ← prove
   r"!f:real^N->complex s.
        (?a. homotopic_with (\h. T)
              (subtopology euclidean s,
               subtopology euclidean (sphere(vec 0,&1))) f (\t. a))
        ==> ?g. g continuous_on s /\ !x. x IN s ==> f x = cexp(g x)"
   (REPEAT GEN_TAC THEN
    SIMP_TAC [sphere, ← GSYM INESSENTIAL_EQ_CONTINUOUS_LOGARITHM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:complex") THEN
    REWRITE_TAC [HOMOTOPIC_WITH_EUCLIDEAN] THEN MATCH_MP_TAC MONO_EXISTS THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
      (← REWRITE_RULE [IMP_CONJ] SUBSET_TRANS)) THEN
    SIMP_TAC [SUBSET, DIST_0, FORALL_IN_GSPEC, IN_UNIV, IN_DIFF, IN_SING] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    SIMP_TAC [COMPLEX_NORM_CX] THEN REAL_ARITH_TAC)

  let INESSENTIAL_EQ_CONTINUOUS_LOGARITHM_CIRCLE ← prove
   r"!f:real^N->complex s.
        (?a. homotopic_with (\h. T)
              (subtopology euclidean s,
               subtopology euclidean (sphere(vec 0,&1))) f (\t. a)) <=>
        (?g. (Cx o g) continuous_on s /\
             !x. x IN s ==> f x = cexp(ii * Cx(g x)))"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN FIRST_ASSUM (MP_TAC o
        MATCH_MP INESSENTIAL_IMP_CONTINUOUS_LOGARITHM_CIRCLE) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->complex") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"Im o (g:real^N->complex)") THEN CONJ_TAC THENL
       [REWRITE_TAC [o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        ASM_REWRITE_TAC [CONTINUOUS_ON_CX_IM],
        FIRST_X_ASSUM (CHOOSE_THEN (MP_TAC o CONJUNCT1 o
          MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET)) THEN
        ASM_SIMP_TAC [SUBSET, FORALL_IN_IMAGE, IN_SPHERE_0, NORM_CEXP] THEN
        REWRITE_TAC [EULER, o_THM, RE_MUL_II, IM_MUL_II] THEN
        SIMP_TAC [RE_CX, IM_CX, REAL_NEG_0, REAL_EXP_0]],
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->real") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       (← q r"?a. homotopic_with (\h. T)
              (subtopology euclidean s,
               subtopology euclidean (sphere(vec 0,&1)))
               ((cexp o (\z. ii * z)) o (Cx o g)) (\x:real^N. a)")
      MP_TAC THENL
       [MATCH_MP_TAC NULLHOMOTOPIC_THROUGH_CONTRACTIBLE THEN
        EXISTS_TAC (← q r"{z | Im z = &0}") THEN ASM_REWRITE_TAC [] THEN
        ASM_SIMP_TAC [CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_CEXP, CONJ_ASSOC,
                      CONTINUOUS_ON_COMPLEX_LMUL, CONTINUOUS_ON_ID] THEN
        CONJ_TAC THENL
         [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, IN_SPHERE_0,
                       o_THM, IM_CX] THEN
          SIMP_TAC [NORM_CEXP, RE_MUL_II, REAL_EXP_0, REAL_NEG_0],
          MATCH_MP_TAC STARLIKE_IMP_CONTRACTIBLE THEN
          MATCH_MP_TAC CONVEX_IMP_STARLIKE THEN CONJ_TAC THENL
           [REWRITE_TAC [IM_DEF, CONVEX_STANDARD_HYPERPLANE],
            REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM] THEN
            MESON_TAC [IM_CX]]],
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:complex") THEN
        MATCH_MP_TAC (← ONCE_REWRITE_RULE [IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
        ASM_SIMP_TAC [TOPSPACE_EUCLIDEAN_SUBTOPOLOGY, o_THM]]])

  let (HOMOTOPIC_CIRCLEMAPS_DIV, HOMOTOPIC_CIRCLEMAPS_DIV_1) ← (do
    let lemma ← prove
     r"!f g h:real^N->real^2 s.
            homotopic_with (\x. T)
              (subtopology euclidean s,
               subtopology euclidean (sphere(vec 0,&1))) f g
            ==> h continuous_on s /\ (!x. x IN s ==> h(x) IN sphere(vec 0,&1))
                 ==> homotopic_with (\x. T)
                      (subtopology euclidean s,
                       subtopology euclidean (sphere(vec 0,&1)))
                      (\x. f x * h x) (\x. g x * h x)"
     (REWRITE_TAC [IN_SPHERE_0] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [HOMOTOPIC_WITH_EUCLIDEAN]) THEN
      ASM_SIMP_TAC [HOMOTOPIC_WITH_EUCLIDEAN_ALT, LEFT_IMP_EXISTS_THM] THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_SPHERE_0, FORALL_IN_PCROSS] THEN
      X_GEN_TAC (← q r"k:real^((1,N)finite_sum)->real^2") THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"\z. (k:real^(1,N)finite_sum->real^2) z * h(sndcart z)") THEN
      ASM_SIMP_TAC [COMPLEX_NORM_MUL, SNDCART_PASTECART, REAL_MUL_LID] THEN
      ASM_REWRITE_TAC [SNDCART_PASTECART] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
      ASM_REWRITE_TAC [← GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC [LINEAR_CONTINUOUS_ON, LINEAR_SNDCART, IMAGE_SNDCART_PCROSS] THEN
      ASM_REWRITE_TAC [UNIT_INTERVAL_NONEMPTY])
    CONJ_PAIR (← prove
     r"(!f g:real^N->real^2 s.
      homotopic_with (\x. T)
       (subtopology euclidean s,
        subtopology euclidean (sphere(vec 0,&1))) f g <=>
      f continuous_on s /\ IMAGE f s SUBSET sphere(vec 0,&1) /\
      g continuous_on s /\ IMAGE g s SUBSET sphere(vec 0,&1) /\
      ?c. homotopic_with (\x. T)
           (subtopology euclidean s,
            subtopology euclidean (sphere(vec 0,&1)))
           (\x. f x / g x) (\x. c)) /\
     (!f g:real^N->real^2 s.
      homotopic_with (\x. T)
       (subtopology euclidean s,
        subtopology euclidean (sphere(vec 0,&1))) f g <=>
      f continuous_on s /\ IMAGE f s SUBSET sphere(vec 0,&1) /\
      g continuous_on s /\ IMAGE g s SUBSET sphere(vec 0,&1) /\
      homotopic_with (\x. T)
       (subtopology euclidean s,
        subtopology euclidean (sphere(vec 0,&1)))
       (\x. f x / g x) (\x. Cx(&1)))"
     (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC
       (← TAUT (← q r"(q <=> r) /\ (p <=> r) ==> (p <=> q) /\ (p <=> r)")) THEN
      CONJ_TAC THENL
       [REPEAT (MATCH_MP_TAC (← TAUT (← q r"(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)")) THEN
               DISCH_TAC) THEN
        EQ_TAC THENL
         [ALL_TAC, DISCH_TAC THEN EXISTS_TAC (← q r"Cx(&1)") THEN ASM_MESON_TAC []] THEN
        REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"c:complex") THEN
        DISCH_THEN (fun th => tactic_of do
          pure (ASSUME_TAC (← MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET th) THEN MP_TAC th)) THEN
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] HOMOTOPIC_WITH_TRANS) THEN
        REWRITE_TAC [HOMOTOPIC_CONSTANT_MAPS, PATH_COMPONENT_OF_EUCLIDEAN,
                     TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
        ASM_CASES_TAC (← q r"s:real^N->bool = {}") THEN ASM_REWRITE_TAC [] THEN
        MP_TAC (← ISPECL [← q r"vec 0:real^2", ← q r"&1"] PATH_CONNECTED_SPHERE) THEN
        REWRITE_TAC [DIMINDEX_2, LE_REFL, PATH_CONNECTED_IFF_PATH_COMPONENT] THEN
        DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
         [ASM SET_TAC [], REWRITE_TAC [IN_SPHERE_0, COMPLEX_NORM_CX, REAL_ABS_NUM]],
        EQ_TAC THEN STRIP_TAC THEN FIRST_ASSUM (MP_TAC o MATCH_MP lemma) THENL
         [FIRST_ASSUM (STRIP_ASSUME_TAC o
             MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS) THEN
          FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
          DISCH_THEN (MP_TAC o SPEC (← q r"\x. inv((g:real^N->complex) x)")),
          DISCH_THEN (MP_TAC o SPEC (← q r"g:real^N->complex"))] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [SUBSET, FORALL_IN_IMAGE, IN_SPHERE_0]) THEN
        ASM_SIMP_TAC [IN_SPHERE_0, COMPLEX_NORM_INV, REAL_INV_1] THEN
        ASM_SIMP_TAC [← GSYM COMPLEX_NORM_ZERO, REAL_OF_NUM_EQ, ARITH_EQ,
                      CONTINUOUS_ON_COMPLEX_INV] THEN
        ASM_REWRITE_TAC [SUBSET, IN_SPHERE_0, FORALL_IN_IMAGE] THEN
        MATCH_MP_TAC (← ONCE_REWRITE_RULE [IMP_CONJ_ALT]
         HOMOTOPIC_WITH_EQ) THEN
        ASM_SIMP_TAC [COMPLEX_DIV_RMUL, COMPLEX_MUL_LID, COMPLEX_MUL_RINV,
                      ← GSYM complex_div, COMPLEX_DIV_REFL,
                      TOPSPACE_EUCLIDEAN_SUBTOPOLOGY,
                      ← GSYM COMPLEX_NORM_ZERO, REAL_OF_NUM_EQ, ARITH_EQ]])))

  pure { INESSENTIAL_EQ_CONTINUOUS_LOGARITHM,
         INESSENTIAL_IMP_CONTINUOUS_LOGARITHM_CIRCLE,
         INESSENTIAL_EQ_CONTINUOUS_LOGARITHM_CIRCLE,
         HOMOTOPIC_CIRCLEMAPS_DIV, HOMOTOPIC_CIRCLEMAPS_DIV_1 }
/- ------------------------------------------------------------------------- -/
/- Complex logs and square roots on "well-behaved" sets; holomorphic         -/
/- logarithms and square roots.                                              -/
/- (moretop.ml 4971-5167)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MOP where
  CONTINUOUS_LOGARITHM_ON_CONTRACTIBLE : thm
  CONTINUOUS_LOGARITHM_ON_SIMPLY_CONNECTED : thm
  CONTINUOUS_LOGARITHM_ON_CBALL : thm
  CONTINUOUS_LOGARITHM_ON_BALL : thm
  CONTINUOUS_SQRT_ON_CONTRACTIBLE : thm
  CONTINUOUS_SQRT_ON_SIMPLY_CONNECTED : thm
  CONTRACTIBLE_IMP_HOLOMORPHIC_LOG : thm
  SIMPLY_CONNECTED_IMP_HOLOMORPHIC_LOG : thm
  CONTRACTIBLE_IMP_HOLOMORPHIC_SQRT : thm
  SIMPLY_CONNECTED_IMP_HOLOMORPHIC_SQRT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOP [HolBase] (D : MoreTopDeps) (BMON : MON) (BMOO : MOO) : ExceptT String IO MOP := do
  -- @@SCOPE BEGIN
  let { COVERING_SPACE_CEXP_PUNCTURED_PLANE, .. } := BMON
  let { INESSENTIAL_EQ_CONTINUOUS_LOGARITHM, .. } := BMOO
  let { COVERING_SPACE_LIFT, STARLIKE_IMP_CONTRACTIBLE, .. } := D.qpaths
  let { CONVEX_IMP_STARLIKE, .. } := D.qconvex
  let { CEXP_ADD, CEXP_N, CEXP_NZ, CONTINUOUS_ON_CEXP, HOLOMORPHIC_ON_CEXP,
        LIM_CEXP_MINUS_1, .. } := D.ra.tsa
  let { PI_POS, .. } := D.ra.tse
  let { COMPLEX_EQ_CEXP, .. } := D.ra.tsf
  let { LIM_COMPLEX_DIV, LIM_COMPLEX_LMUL, .. } := D.ra.ts.knb
  let { CONTINUOUS_ON_COMPLEX_DIV, .. } := D.ra.ts.knc
  let { holomorphic_on, HOLOMORPHIC_ON_IMP_CONTINUOUS_ON, .. } := D.ra.ts.kne
  let { HAS_COMPLEX_DERIVATIVE_WITHIN, .. } := D.ra.ts.knf
  let { HOLOMORPHIC_ON_COMPOSE, HOLOMORPHIC_ON_CONST, HOLOMORPHIC_ON_DIV,
        .. } := D.ra.ts.knh
  let { complex_div, SIMPLE_COMPLEX_ARITH_TAC, .. } := D.ra.ts.cn.cxa
  let { COMPLEX_ADD_SUB, COMPLEX_EQ_ADD_LCANCEL_0, COMPLEX_MUL_LZERO, COMPLEX_MUL_RID,
        COMPLEX_SUB_REFL, .. } := D.ra.ts.cn.cxb
  let { COMPLEX_VEC_0, IM_SUB, .. } := D.ra.ts.cn.cxc
  let { COMPLEX_RING, .. } := D.ra.ts.cn.cxd
  let { COMPLEX_FIELD, .. } := D.ra.ts.cn.cxe
  let { COMPLEX_NORM_GE_RE_IM, .. } := D.ra.ts.cn.cxg
  let { LIM_AT_ZERO, .. } := D.ra.ts.cn.ms.qtopology2
  let { ASM_MESON_TAC, REAL_ARITH, SET_TAC, .. } := D.ra.ts.cn.cx.cvx
  let { CONTINUOUS_ON, .. } := D.ra.ts.cn.ms.ig.qtopology
  let { CONTRAPOS_THM, .. } := D.ra.ts.cn.cx.cvx.core1
  let { IMP_CONJ, IMP_CONJ_ALT, .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_UNIV, MONO_EXISTS, MONO_FORALL, NOT_IN_EMPTY, .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_LET_TRANS, REAL_LT_01, .. } := D.ra.ts.cn.cx.cvx.core4
  let { o_DEF, .. } := D.ra.ts.cn.cx.cvx.core6
  let { DIST_NZ, .. } := D.ra.ts.cn.cx.cvx.vec1
  let { dist, .. } := D.ra.ts.cn.cx.cvx.vec4
  let { EVENTUALLY_MONO, EVENTUALLY_TRUE, .. } := D.ra.ts.cn.cx.cvx.met
  let { CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_CONST, CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN,
        CONTINUOUS_WITHIN, EVENTUALLY_AT, .. } := D.ra.ts.cn.cx.cvx.top3
  let { LIM_COMPOSE_AT, LIM_TRANSFORM_EVENTUALLY, LIM_TRANSFORM_WITHIN,
        .. } := D.ra.ts.cn.ms.ig.dv.qtopology2
  let { NULLHOMOTOPIC_FROM_CONTRACTIBLE, .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths2
  let { CONTINUOUS_ON_EMPTY, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { tendsto, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology2
  let { CONVEX_BALL, CONVEX_CBALL, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  -- @@SCOPE END

  let CONTINUOUS_LOGARITHM_ON_CONTRACTIBLE ← prove
   r"!f:real^N->complex s.
        f continuous_on s /\ contractible s /\
        (!x. x IN s ==> ~(f x = Cx(&0)))
        ==> ?g. g continuous_on s /\ !x. x IN s ==> f x = cexp(g x)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [← GSYM INESSENTIAL_EQ_CONTINUOUS_LOGARITHM] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC NULLHOMOTOPIC_FROM_CONTRACTIBLE THEN
    ASM_REWRITE_TAC [] THEN ASM SET_TAC [])

  let CONTINUOUS_LOGARITHM_ON_SIMPLY_CONNECTED ← prove
   r"!f:real^N->complex s.
        f continuous_on s /\ simply_connected s /\ locally path_connected s /\
        (!x. x IN s ==> ~(f x = Cx(&0)))
        ==> ?g. g continuous_on s /\ !x. x IN s ==> f x = cexp(g x)"
   (REPEAT STRIP_TAC THEN MP_TAC
    (← ISPECL [← q r"f:real^N->complex", ← q r"s:real^N->bool"]
      (← MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ] COVERING_SPACE_LIFT)
          COVERING_SPACE_CEXP_PUNCTURED_PLANE)) THEN
    ASM_REWRITE_TAC [IN_UNIV] THEN ASM SET_TAC [])

  let CONTINUOUS_LOGARITHM_ON_CBALL ← prove
   r"!f:real^N->complex a r.
        f continuous_on cball(a,r) /\
        (!z. z IN cball(a,r) ==> ~(f z = Cx(&0)))
        ==> ?h. h continuous_on cball(a,r) /\
                !z. z IN cball(a,r) ==> f z = cexp(h z)"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"cball(a:real^N,r) = {}") THEN
    ASM_REWRITE_TAC [CONTINUOUS_ON_EMPTY, NOT_IN_EMPTY] THEN
    MATCH_MP_TAC CONTINUOUS_LOGARITHM_ON_CONTRACTIBLE THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC STARLIKE_IMP_CONTRACTIBLE THEN
    MATCH_MP_TAC CONVEX_IMP_STARLIKE THEN
    ASM_REWRITE_TAC [CONVEX_CBALL])

  let CONTINUOUS_LOGARITHM_ON_BALL ← prove
   r"!f:real^N->complex a r.
        f continuous_on ball(a,r) /\
        (!x. x IN ball(a,r) ==> ~(f x = Cx(&0)))
        ==> ?h. h continuous_on ball(a,r) /\
                !x. x IN ball(a,r) ==> f x = cexp(h x)"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"ball(a:real^N,r) = {}") THEN
    ASM_REWRITE_TAC [CONTINUOUS_ON_EMPTY, NOT_IN_EMPTY] THEN
    MATCH_MP_TAC CONTINUOUS_LOGARITHM_ON_CONTRACTIBLE THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC STARLIKE_IMP_CONTRACTIBLE THEN
    MATCH_MP_TAC CONVEX_IMP_STARLIKE THEN
    ASM_REWRITE_TAC [CONVEX_BALL])

  let CONTINUOUS_SQRT_ON_CONTRACTIBLE ← prove
   r"!f:real^N->complex s.
        f continuous_on s /\ contractible s /\
        (!x. x IN s ==> ~(f x = Cx(&0)))
        ==> ?g. g continuous_on s /\ !x. x IN s ==> f x = (g x) pow 2"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP CONTINUOUS_LOGARITHM_ON_CONTRACTIBLE) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->complex") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"\z:real^N. cexp(g z / Cx(&2))") THEN
    ASM_SIMP_TAC [← GSYM CEXP_N,
                  ← ExceptT.mk (COMPLEX_RING (← q r"Cx(&2) * z / Cx(&2) = z"))] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    REWRITE_TAC [CONTINUOUS_ON_CEXP] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN
    ASM_SIMP_TAC [CONTINUOUS_ON_CONST] THEN
    CONV_TAC COMPLEX_RING)

  let CONTINUOUS_SQRT_ON_SIMPLY_CONNECTED ← prove
   r"!f:real^N->complex s.
        f continuous_on s /\ simply_connected s /\ locally path_connected s /\
        (!x. x IN s ==> ~(f x = Cx(&0)))
        ==> ?g. g continuous_on s /\ !x. x IN s ==> f x = (g x) pow 2"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP CONTINUOUS_LOGARITHM_ON_SIMPLY_CONNECTED) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->complex") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"\z:real^N. cexp(g z / Cx(&2))") THEN
    ASM_SIMP_TAC [← GSYM CEXP_N,
                  ← ExceptT.mk (COMPLEX_RING (← q r"Cx(&2) * z / Cx(&2) = z"))] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    REWRITE_TAC [CONTINUOUS_ON_CEXP] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN
    ASM_SIMP_TAC [CONTINUOUS_ON_CONST] THEN
    CONV_TAC COMPLEX_RING)

  -- Analogously, holomorphic logarithms and square roots.

  let (CONTRACTIBLE_IMP_HOLOMORPHIC_LOG, SIMPLY_CONNECTED_IMP_HOLOMORPHIC_LOG) ←
   CONJ_PAIR (← prove
   r"(!s:complex->bool.
      contractible s
      ==> !f. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
              ==> ?g. g holomorphic_on s /\ !z. z IN s ==> f z = cexp(g z)) /\
     (!s:complex->bool.
      simply_connected s /\ locally path_connected s
      ==> !f. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
              ==> ?g. g holomorphic_on s /\ !z. z IN s ==> f z = cexp(g z))"
   (REPEAT STRIP_TAC THENL
     [MP_TAC (← ISPECL [← q r"f:complex->complex", ← q r"s:complex->bool"]
          CONTINUOUS_LOGARITHM_ON_CONTRACTIBLE),
      MP_TAC (← ISPECL [← q r"f:complex->complex", ← q r"s:complex->bool"]
          CONTINUOUS_LOGARITHM_ON_SIMPLY_CONNECTED)] THEN
    ASM_SIMP_TAC [HOLOMORPHIC_ON_IMP_CONTINUOUS_ON] THEN
   (MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"g:complex->complex") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC (← q r"f holomorphic_on s") THEN
    REWRITE_TAC [holomorphic_on] THEN MATCH_MP_TAC MONO_FORALL THEN
    X_GEN_TAC (← q r"z:complex") THEN ASM_CASES_TAC (← q r"(z:complex) IN s") THEN
    ASM_REWRITE_TAC [HAS_COMPLEX_DERIVATIVE_WITHIN] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"f':complex") MP_TAC) THEN
    DISCH_THEN (MP_TAC o
     ISPECL [← q r"\x. (cexp(g x) - cexp(g z)) / (x - z)", ← q r"&1"] o
     MATCH_MP (← REWRITE_RULE [← TAUT (← q r"p /\ q /\ r ==> s <=> r ==> p /\ q ==> s")]
      LIM_TRANSFORM_WITHIN)) THEN
    ASM_SIMP_TAC [REAL_LT_01] THEN
    DISCH_THEN (MP_TAC o
      SPECL [← q r"\x:complex. if g x = g z then cexp(g z)
                          else (cexp(g x) - cexp(g z)) / (g x - g z)",
             ← q r"cexp(g(z:complex))"] o
      MATCH_MP (← REWRITE_RULE [IMP_CONJ] LIM_COMPLEX_DIV)) THEN
    REWRITE_TAC [CEXP_NZ] THEN ANTS_TAC THENL
     [SUBGOAL_THEN
       (← q r"(\x. if g x = g z then cexp(g z)
             else (cexp(g x) - cexp(g(z:complex))) / (g x - g z)) =
        (\y. if y = g z then cexp(g z)
             else (cexp y - cexp(g z)) / (y - g z)) o g")
      SUBST1_TAC THENL [REWRITE_TAC [o_DEF], ALL_TAC] THEN
      MATCH_MP_TAC LIM_COMPOSE_AT THEN
      EXISTS_TAC (← q r"(g:complex->complex) z") THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC [CONTINUOUS_ON],
        REWRITE_TAC [EVENTUALLY_TRUE],
        ONCE_REWRITE_TAC [LIM_AT_ZERO] THEN
        SIMP_TAC [COMPLEX_VEC_0, COMPLEX_ADD_SUB, COMPLEX_EQ_ADD_LCANCEL_0] THEN
        MP_TAC (← SPEC (← q r"cexp(g(z:complex))") (← MATCH_MP LIM_COMPLEX_LMUL
         LIM_CEXP_MINUS_1)) THEN REWRITE_TAC [COMPLEX_MUL_RID] THEN
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
        SIMP_TAC [EVENTUALLY_AT, ← GSYM DIST_NZ, CEXP_ADD] THEN
        EXISTS_TAC (← q r"&1") THEN REWRITE_TAC [REAL_LT_01] THEN
        SIMPLE_COMPLEX_ARITH_TAC],
      DISCH_THEN (fun th => tactic_of do
          pure (EXISTS_TAC (← q r"f' / cexp(g(z:complex))") THEN MP_TAC th)) THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ]
          LIM_TRANSFORM_EVENTUALLY) THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id
       [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"z:complex")) THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [CONTINUOUS_WITHIN, tendsto] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"&2 * pi")) THEN
      REWRITE_TAC [← REAL_ARITH (← q r"&0 < &2 * x <=> &0 < x"), PI_POS] THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] EVENTUALLY_MONO) THEN
      X_GEN_TAC (← q r"w:complex") THEN REWRITE_TAC [dist] THEN DISCH_TAC THEN
      COND_CASES_TAC THENL
       [ASM_REWRITE_TAC [COMPLEX_SUB_REFL, complex_div, COMPLEX_MUL_LZERO],
        ASM_CASES_TAC (← q r"w:complex = z") THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"~(cexp(g(w:complex)) = cexp(g z))") MP_TAC THENL
         [UNDISCH_TAC (← q r"~((g:complex->complex) w = g z)") THEN
          REWRITE_TAC [CONTRAPOS_THM] THEN
          MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] COMPLEX_EQ_CEXP) THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT]
           REAL_LET_TRANS)) THEN
          REWRITE_TAC [← GSYM IM_SUB, COMPLEX_NORM_GE_RE_IM],
          REPEAT (FIRST_X_ASSUM (MP_TAC o check (HolCore.Basics.is_neg o concl))) THEN
          CONV_TAC COMPLEX_FIELD]]])))

  let (CONTRACTIBLE_IMP_HOLOMORPHIC_SQRT, SIMPLY_CONNECTED_IMP_HOLOMORPHIC_SQRT) ←
   CONJ_PAIR (← prove
   r"(!s:complex->bool.
      contractible s
      ==> !f. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
              ==> ?g. g holomorphic_on s /\  !z. z IN s ==> f z = g z pow 2) /\
     (!s:complex->bool.
      simply_connected s /\ locally path_connected s
      ==> !f. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
              ==> ?g. g holomorphic_on s /\  !z. z IN s ==> f z = g z pow 2)"
   (CONJ_TAC THEN GEN_TAC THENL
     [DISCH_THEN (ASSUME_TAC o MATCH_MP CONTRACTIBLE_IMP_HOLOMORPHIC_LOG),
      DISCH_THEN (ASSUME_TAC o
        MATCH_MP SIMPLY_CONNECTED_IMP_HOLOMORPHIC_LOG)] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"f:complex->complex")) THEN ASM_SIMP_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"g:complex->complex") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"\z:complex. cexp(g z / Cx(&2))") THEN
    ASM_SIMP_TAC [← GSYM CEXP_N,
                  ← ExceptT.mk (COMPLEX_RING (← q r"Cx(&2) * z / Cx(&2) = z"))] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN
    REWRITE_TAC [HOLOMORPHIC_ON_CEXP] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
    ASM_SIMP_TAC [HOLOMORPHIC_ON_CONST] THEN
    CONV_TAC COMPLEX_RING))

  pure { CONTINUOUS_LOGARITHM_ON_CONTRACTIBLE, CONTINUOUS_LOGARITHM_ON_SIMPLY_CONNECTED,
         CONTINUOUS_LOGARITHM_ON_CBALL, CONTINUOUS_LOGARITHM_ON_BALL,
         CONTINUOUS_SQRT_ON_CONTRACTIBLE, CONTINUOUS_SQRT_ON_SIMPLY_CONNECTED,
         CONTRACTIBLE_IMP_HOLOMORPHIC_LOG, SIMPLY_CONNECTED_IMP_HOLOMORPHIC_LOG,
         CONTRACTIBLE_IMP_HOLOMORPHIC_SQRT, SIMPLY_CONNECTED_IMP_HOLOMORPHIC_SQRT }
/- ------------------------------------------------------------------------- -/
/- Holomorphic inverse cosines; extension property for inessential maps.     -/
/- (moretop.ml 5168-5420)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MOQ where
  CONTRACTIBLE_IMP_HOLOMORPHIC_ACS : thm
  CONTRACTIBLE_IMP_HOLOMORPHIC_ACS_BOUNDED : thm
  INESSENTIAL_NEIGHBOURHOOD_EXTENSION_LOGARITHM : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOQ [HolBase] (D : MoreTopDeps) (BMOP : MOP) : ExceptT String IO MOQ := do
  -- @@SCOPE BEGIN
  let { CONTRACTIBLE_IMP_HOLOMORPHIC_LOG, CONTRACTIBLE_IMP_HOLOMORPHIC_SQRT, .. } := BMOP
  let { REAL_LE_ABS_SINH, .. } := D.rzah
  let { CEXP_ADD, CEXP_NEG, CEXP_NZ, .. } := D.ra.tsa
  let { ccos, .. } := D.ra.tsb
  let { PI_POS_LE, REAL_ABS_PI, .. } := D.ra.tse
  let { CCOS_EQ, COMPLEX_EQ_CEXP, NORM_CCOS_POW_2, .. } := D.ra.tsf
  let { PI_APPROX_32, .. } := D.ra.tsl
  let { CEXP_CLOG, CONTINUOUS_ON_CLOG, .. } := D.ra.tsm
  let { RE_CLOG_POS_LT_IMP, .. } := D.ra.tsn
  let { CCOS_CACS, .. } := D.ra.tst
  let { RE_CACS_BOUND, .. } := D.ra.tsu
  let { CONTINUOUS_COMPLEX_MUL, CONTINUOUS_ON_COMPLEX_RMUL, .. } := D.ra.ts.knc
  let { HOLOMORPHIC_ON_ADD, HOLOMORPHIC_ON_CONST, HOLOMORPHIC_ON_MUL, HOLOMORPHIC_ON_NEG,
        HOLOMORPHIC_ON_POW, HOLOMORPHIC_ON_SUB, .. } := D.ra.ts.knh
  let { complex_div, COMPLEX_SQNORM, .. } := D.ra.ts.cn.cxa
  let { COMPLEX_DIV_REFL, COMPLEX_NORM_CX, COMPLEX_VEC_0, IM_ADD, IM_SUB, RE_ADD, RE_CX,
        .. } := D.ra.ts.cn.cxc
  let { COMPLEX_RING, .. } := D.ra.ts.cn.cxd
  let { COMPLEX_FIELD, .. } := D.ra.ts.cn.cxe
  let { COMPLEX_DIV_EQ_0, COMPLEX_DIV_LMUL, .. } := D.ra.ts.cn.cxf
  let { COMPLEX_NORM_GE_RE_IM, .. } := D.ra.ts.cn.cxg
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON, NORM_ARITH, REAL_ARITH, REAL_ARITH_TAC,
        REAL_RAT_REDUCE_CONV, SET_RULE, SET_TAC, .. } := D.ra.ts.cn.cx.cvx
  let { DE_MORGAN_THM, FORALL_IN_GSPEC, .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_IN_UNIONS, IMP_CONJ, IMP_IMP, INTER_SUBSET,
        .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_INTER, LEFT_IMP_EXISTS_THM, NOT_IMP, REAL_ABS_NUM,
        .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_LE_ADD, REAL_LE_ADD2, REAL_LE_MUL, REAL_LE_POW_2, REAL_LE_SQUARE_ABS,
        REAL_LET_TRANS, REAL_LT_MIN, .. } := D.ra.ts.cn.cx.cvx.core4
  let { RIGHT_FORALL_IMP_THM, RIGHT_IMP_EXISTS_THM, SKOLEM_THM, SUBSET, SUBSET_REFL,
        .. } := D.ra.ts.cn.cx.cvx.core5
  let { o_DEF, SUBSET_UNIV, UNIONS_SUBSET, .. } := D.ra.ts.cn.cx.cvx.core6
  let { REAL_HALF, .. } := D.ra.ts.cn.cx.cvx.misc
  let { DIST_SYM, .. } := D.ra.ts.cn.cx.cvx.vec1
  let { NORM_LE_SQUARE, NORM_POS_LE, NORM_POW_2, NORM_SUB, .. } := D.ra.ts.cn.cx.cvx.vec3
  let { dist, .. } := D.ra.ts.cn.cx.cvx.vec4
  let { OPEN_IN_IMP_SUBSET, OPEN_IN_SUBSET_TRANS, .. } := D.ra.ts.cn.cx.cvx.met
  let { CENTRE_IN_BALL, .. } := D.ra.ts.cn.cx.cvx.top1
  let { CONTINUOUS_CONST, CONTINUOUS_ON_ADD, CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_CONST,
        CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN, CONTINUOUS_ON_SUBSET,
        .. } := D.ra.ts.cn.cx.cvx.top3
  let { IN_BALL, OPEN_BALL, .. } := D.ra.ts.cn.cx.cvx.top4
  let { continuous_within, OPEN_IN_OPEN_INTER, TOPSPACE_EUCLIDEAN_SUBTOPOLOGY,
        .. } := D.ra.ts.cn.cx.cvx.top5
  let { PASTING_LEMMA_EXISTS, SUBTOPOLOGY_SUBTOPOLOGY,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qmetric
  let { REAL_LT_TRANS, .. } := D.ra.ts.cn.ms.ig.dv.dg.qsession
  let { CONTINUOUS_MAP_EUCLIDEAN, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { OPEN_IN_UNIONS, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qmet
  -- @@SCOPE END

  -- `el n o CONJUNCTS` and `last o CONJUNCTS` as theorem functions.
  let elc : Nat → thm → ExceptT String IO thm := fun n th =>
    liftExcept (HolCore.Lib.el n (CONJUNCTS th))
  let lastc : thm → ExceptT String IO thm := fun th =>
    liftExcept (HolCore.Lib.last (CONJUNCTS th))

  let CONTRACTIBLE_IMP_HOLOMORPHIC_ACS ← prove
   r"!f s. f holomorphic_on s /\ contractible s /\
         (!z. z IN s ==> ~(f z = Cx(&1)) /\ ~(f z = --Cx(&1)))
         ==> ?g. g holomorphic_on s /\ !z. z IN s ==> f z = ccos(g z)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"\z:complex. Cx(&1) - f(z) pow 2") o
      MATCH_MP CONTRACTIBLE_IMP_HOLOMORPHIC_SQRT) THEN
    ASM_SIMP_TAC [HOLOMORPHIC_ON_SUB, HOLOMORPHIC_ON_CONST, HOLOMORPHIC_ON_POW,
                  ← ExceptT.mk (COMPLEX_RING (← q r"~(Cx(&1) - z pow 2 = Cx(&0)) <=>
                                ~(z = Cx(&1)) /\ ~(z = --Cx(&1))"))] THEN
    REWRITE_TAC [← ExceptT.mk (COMPLEX_RING
     (← q r"Cx(&1) - w pow 2 = z pow 2 <=>
      (w + ii * z) * (w - ii * z) = Cx(&1)"))] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"g:complex->complex") STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"\z:complex. f(z) + ii * g(z)") o
        MATCH_MP CONTRACTIBLE_IMP_HOLOMORPHIC_LOG) THEN
    ASM_SIMP_TAC [HOLOMORPHIC_ON_ADD, HOLOMORPHIC_ON_MUL, HOLOMORPHIC_ON_CONST,
      ← ExceptT.mk (COMPLEX_RING (← q r"(a + b) * (a - b) = Cx(&1) ==> ~(a + b = Cx(&0))"))] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"h:complex->complex") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"\z:complex. --ii * h(z)") THEN
    ASM_SIMP_TAC [HOLOMORPHIC_ON_MUL, HOLOMORPHIC_ON_CONST, ccos] THEN
    X_GEN_TAC (← q r"z:complex") THEN
    DISCH_TAC THEN REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"z:complex"))) THEN
    ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP (← ExceptT.mk (COMPLEX_FIELD
     (← q r"a * b = Cx(&1) ==> b = inv a")))) THEN
    ASM_SIMP_TAC [← GSYM CEXP_NEG] THEN
    FIRST_X_ASSUM (ASSUME_TAC o SYM) THEN DISCH_THEN (ASSUME_TAC o SYM) THEN
    ASM_REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"ii * --ii * z = z")),
                     ← ExceptT.mk (COMPLEX_RING (← q r"--ii * --ii * z = --z"))] THEN
    CONV_TAC COMPLEX_RING)

  let CONTRACTIBLE_IMP_HOLOMORPHIC_ACS_BOUNDED ← (do
    let lemma ← prove
     r"!w. ?v. ccos(v) = w /\ norm(v) <= pi + norm(w)"
     (GEN_TAC THEN EXISTS_TAC (← q r"cacs w") THEN ABBREV_TAC (← q r"v = cacs w") THEN
      MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
       [ASM_MESON_TAC [CCOS_CACS], DISCH_THEN (SUBST1_TAC o SYM)] THEN
      SIMP_TAC [NORM_LE_SQUARE, PI_POS_LE, NORM_POS_LE, REAL_LE_ADD] THEN
      MATCH_MP_TAC (← REAL_ARITH
       (← q r"&0 <= b * c /\ a <= b pow 2 + c pow 2 ==> a <= (b + c) pow 2")) THEN
      SIMP_TAC [REAL_LE_MUL, PI_POS_LE, NORM_POS_LE] THEN
      REWRITE_TAC [COMPLEX_SQNORM, ← GSYM NORM_POW_2, NORM_CCOS_POW_2] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN REWRITE_TAC [← GSYM REAL_LE_SQUARE_ABS] THEN
      EXPAND_TAC "v" THEN REWRITE_TAC [REAL_ABS_PI, RE_CACS_BOUND] THEN
      MATCH_MP_TAC (← REAL_ARITH
       (← q r"&0 <= c /\ x <= (d / &2) pow 2 ==> x <= c + d pow 2 / &4")) THEN
      REWRITE_TAC [REAL_LE_POW_2, ← GSYM REAL_LE_SQUARE_ABS, REAL_LE_ABS_SINH])
    prove
     r"!f s a.
          f holomorphic_on s /\ contractible s /\ a IN s /\
          (!z. z IN s ==> ~(f z = Cx(&1)) /\ ~(f z = --Cx(&1)))
          ==> ?g. g holomorphic_on s /\ norm(g a) <= pi + norm(f a) /\
                  !z. z IN s ==> f z = ccos(g z)"
     (REPEAT STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"f:complex->complex", ← q r"s:complex->bool"]
            CONTRACTIBLE_IMP_HOLOMORPHIC_ACS) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:complex->complex") STRIP_ASSUME_TAC) THEN
      MP_TAC (← SPEC (← q r"(f:complex->complex) a") lemma) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"b:complex") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"ccos b = ccos(g(a:complex))") MP_TAC THENL
       [ASM_MESON_TAC [], REWRITE_TAC [CCOS_EQ]] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"n:real") (STRIP_ASSUME_TAC o GSYM)) THENL
       [EXISTS_TAC (← q r"\z:complex. g z + Cx(&2 * n * pi)"),
        EXISTS_TAC (← q r"\z:complex. --(g z) + Cx(&2 * n * pi)")] THEN
      ASM_SIMP_TAC [HOLOMORPHIC_ON_ADD, HOLOMORPHIC_ON_NEG,
                    HOLOMORPHIC_ON_CONST] THEN
      CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN REWRITE_TAC [CCOS_EQ] THEN
      ASM_MESON_TAC []))

  -- Extension property for inessential maps.  This almost follows from
  -- INESSENTIAL_NEIGHBOURHOOD_EXTENSION except that here we don't need to
  -- assume that t is closed in s.

  let INESSENTIAL_NEIGHBOURHOOD_EXTENSION_LOGARITHM ← prove
   r"!f:real^N->complex s t.
        f continuous_on s /\ t SUBSET s /\
        (?g. g continuous_on t /\ !x. x IN t ==> f x = cexp(g x))
        ==> ?u. t SUBSET u /\ open_in (subtopology euclidean s) u /\
                (?g. g continuous_on u /\ !x. x IN u ==> f x = cexp(g x))"
   (REPEAT GEN_TAC THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"h:real^N->complex") (STRIP_ASSUME_TAC o GSYM)) THEN
    SUBGOAL_THEN
     (← q r"!x. x IN t
          ==> ?d. &0 < d /\
                  (!y. y IN s /\ dist(x,y) < d
                       ==> norm(f y / f x - Cx(&1)) < &1 / &7) /\
                  (!z:real^N. z IN t /\ dist(x,z) < &2 * d
                              ==> norm(h z - h x) < &1 / &5)")
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      UNDISCH_TAC (← q r"(h:real^N->complex) continuous_on t") THEN
      GEN_REWRITE_TAC LAND_CONV [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"x:real^N")) THEN
      ASM_REWRITE_TAC [continuous_within] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"&1 / &5")) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [dist] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"e:real") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"~((f:real^N->complex) x = Cx(&0))") ASSUME_TAC THENL
       [ASM_MESON_TAC [CEXP_NZ], ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"(\y:real^N. f y / f x) continuous (at x within s)")
      MP_TAC THENL
       [REWRITE_TAC [complex_div] THEN MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN
        REWRITE_TAC [CONTINUOUS_CONST] THEN
        ASM_MESON_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN, SUBSET],
        REWRITE_TAC [continuous_within] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"&1 / &7")) THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_SIMP_TAC [COMPLEX_DIV_REFL, dist] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC)] THEN
      EXISTS_TAC (← q r"min d (e / &2)") THEN
      ASM_REWRITE_TAC [REAL_LT_MIN, REAL_HALF] THEN CONJ_TAC THENL
       [ASM_MESON_TAC [NORM_SUB],
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ONCE_REWRITE_TAC [NORM_SUB] THEN ASM_REWRITE_TAC [] THEN
        ASM_REAL_ARITH_TAC],
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
      REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"d:real^N->real") THEN DISCH_THEN (LABEL_TAC "*")] THEN
    ABBREV_TAC (← q r"u = \x. s INTER ball(x:real^N,d x)") THEN
    ABBREV_TAC (← q r"g = \x y. h(x:real^N) + clog(f y / f x)") THEN
    SUBGOAL_THEN
     (← q r"(!x:real^N. x IN t ==> x IN u x) /\
      (!x. x IN t ==> open_in (subtopology euclidean s) (u x))")
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN
      ASM_SIMP_TAC [IN_INTER, CENTRE_IN_BALL, OPEN_IN_OPEN_INTER, OPEN_BALL] THEN
      ASM SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x:real^N y:real^N. x IN t /\ y IN u x ==> cexp(g x y) = f y")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      EXPAND_TAC "g" THEN REWRITE_TAC [CEXP_ADD] THEN ASM_SIMP_TAC [] THEN
      REMOVE_THEN "*" (MP_TAC o SPEC (← q r"x:real^N")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"y:real^N") o elc 1) THEN
      MP_TAC (← ASSUME (← q r"y IN (u:real^N->real^N->bool) x")) THEN
      EXPAND_TAC "u" THEN REWRITE_TAC [IN_INTER, IN_BALL] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← NORM_ARITH
       (← q r"norm(x - y) < &1 / &7 ==> norm(y) = &1 ==> ~(x = vec 0)"))) THEN
      SIMP_TAC [COMPLEX_NORM_CX, REAL_ABS_NUM, CEXP_CLOG, COMPLEX_VEC_0] THEN
      SIMP_TAC [COMPLEX_DIV_LMUL, COMPLEX_DIV_EQ_0, DE_MORGAN_THM],
      ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"subtopology euclidean (UNIONS {(u:real^N->real^N->bool) x | x IN t})",
      ← q r"euclidean:(complex)topology",
      ← q r"g:real^N->real^N->complex",
      ← q r"u:real^N->real^N->bool",
       ← q r"t:real^N->bool"]
      PASTING_LEMMA_EXISTS) THEN
    REWRITE_TAC [CONTINUOUS_MAP_EUCLIDEAN, TOPSPACE_EUCLIDEAN_SUBTOPOLOGY,
                 SUBTOPOLOGY_SUBTOPOLOGY] THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"open_in a b /\ c <=> ~(open_in a b ==> ~c)")] THEN
    SIMP_TAC [← ISPEC (← q r"euclidean") OPEN_IN_IMP_SUBSET,
              ← SET_RULE (← q r"s SUBSET u ==> u INTER s = s")] THEN
    REWRITE_TAC [NOT_IMP] THEN
    REWRITE_TAC [SUBSET_REFL, SUBSET_UNIV] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC (← q r"s:real^N->bool") THEN
          ASM_SIMP_TAC [] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
          REWRITE_TAC [UNIONS_SUBSET, FORALL_IN_GSPEC] THEN
          ASM_MESON_TAC [OPEN_IN_IMP_SUBSET],
          EXPAND_TAC "g" THEN REWRITE_TAC [] THEN
          MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
          REWRITE_TAC [CONTINUOUS_ON_CONST] THEN
          GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
          MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
           [REWRITE_TAC [complex_div] THEN
            MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_RMUL THEN
            ASM_MESON_TAC [CONTINUOUS_ON_SUBSET, INTER_SUBSET],
            MATCH_MP_TAC CONTINUOUS_ON_CLOG THEN
            REWRITE_TAC [IMP_CONJ, FORALL_IN_IMAGE, IN_INTER] THEN
            X_GEN_TAC (← q r"y:real^N") THEN REPEAT STRIP_TAC THEN
            ONCE_REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"z = (z - Cx(&1)) + Cx(&1)"))] THEN
            REWRITE_TAC [RE_ADD, RE_CX] THEN MATCH_MP_TAC (← REAL_ARITH
             (← q r"abs x < &1 ==> &0 < x + &1")) THEN
            MATCH_MP_TAC (← MESON [COMPLEX_NORM_GE_RE_IM, REAL_LET_TRANS]
             (← q r"norm z < &1 ==> abs(Re z) < &1")) THEN
            MATCH_MP_TAC (← REAL_ARITH (← q r"x < &1 / &7 ==> x < &1")) THEN
            REMOVE_THEN "*" (MP_TAC o SPEC (← q r"x:real^N")) THEN ASM_SIMP_TAC [] THEN
            DISCH_THEN (MP_TAC o SPEC (← q r"y:real^N") o elc 1) THEN
            MP_TAC (← ASSUME (← q r"y IN (u:real^N->real^N->bool) x")) THEN
            EXPAND_TAC "u" THEN REWRITE_TAC [IN_INTER, IN_BALL] THEN
            STRIP_TAC THEN ASM_REWRITE_TAC []]],
        MAP_EVERY X_GEN_TAC  [← q r"a:real^N", ← q r"b:real^N", ← q r"x:real^N"] THEN
        REWRITE_TAC [IN_INTER] THEN STRIP_TAC THEN
        MATCH_MP_TAC COMPLEX_EQ_CEXP THEN
        CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
        EXPAND_TAC "g" THEN REWRITE_TAC [IM_ADD] THEN
        MATCH_MP_TAC (← REAL_ARITH
         (← q r"&5 < a /\ abs(ha - hb) < &1 / &5 /\ abs(fa) < &2 /\ abs(fb) < &2
          ==> abs((ha + fa) - (hb + fb)) < a")) THEN
        CONJ_TAC THENL [MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC, ALL_TAC] THEN
        CONJ_TAC THENL
         [REWRITE_TAC [← GSYM IM_SUB] THEN
          MATCH_MP_TAC (← MESON [COMPLEX_NORM_GE_RE_IM, REAL_LET_TRANS]
           (← q r"norm z < a ==> abs(Im z) < a")) THEN
          MP_TAC (← ASSUME (← q r"x IN (u:real^N->real^N->bool) b")) THEN
          MP_TAC (← ASSUME (← q r"x IN (u:real^N->real^N->bool) a")) THEN
          EXPAND_TAC "u" THEN REWRITE_TAC [IMP_IMP, IN_INTER, IN_BALL] THEN
          DISCH_THEN (MP_TAC o MATCH_MP (← TAUT
           (← q r"(p /\ q) /\ (p /\ r) ==> q /\ r"))) THEN
          DISCH_THEN (MP_TAC o MATCH_MP (← NORM_ARITH
           (← q r"dist(a,x) < d /\ dist(b,x) < e
            ==> dist(a,b) < &2 * d \/ dist(a,b) < &2 * e"))) THEN
          STRIP_TAC THENL
           [REMOVE_THEN "*" (MP_TAC o SPEC (← q r"a:real^N")),
            REMOVE_THEN "*" (MP_TAC o SPEC (← q r"b:real^N"))] THEN
          ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o lastc) THEN
          ASM_MESON_TAC [NORM_SUB, DIST_SYM],
          CONJ_TAC THEN TRANS_TAC REAL_LT_TRANS (← q r"pi / &2") THEN
          (CONJ_TAC THENL
            [ALL_TAC, MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC]) THEN
          MATCH_MP_TAC RE_CLOG_POS_LT_IMP THEN
          ONCE_REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"z = (z - Cx(&1)) + Cx(&1)"))] THEN
          REWRITE_TAC [RE_ADD, RE_CX] THEN MATCH_MP_TAC (← REAL_ARITH
           (← q r"abs x < &1 ==> &0 < x + &1")) THEN
          MATCH_MP_TAC (← MESON [COMPLEX_NORM_GE_RE_IM, REAL_LET_TRANS]
           (← q r"norm z < &1 ==> abs(Re z) < &1")) THEN
          MATCH_MP_TAC (← REAL_ARITH (← q r"x < &1 / &7 ==> x < &1")) THENL
           [REMOVE_THEN "*" (MP_TAC o SPEC (← q r"a:real^N")),
            REMOVE_THEN "*" (MP_TAC o SPEC (← q r"b:real^N"))] THEN
          ASM_REWRITE_TAC [] THEN
          DISCH_THEN (MP_TAC o SPEC (← q r"x:real^N") o elc 1) THEN
          DISCH_THEN MATCH_MP_TAC THENL
           [MP_TAC (← ASSUME (← q r"x IN (u:real^N->real^N->bool) a")),
            MP_TAC (← ASSUME (← q r"x IN (u:real^N->real^N->bool) b"))] THEN
          EXPAND_TAC "u" THEN REWRITE_TAC [IN_INTER, IN_BALL] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC []]],
      DISCH_THEN (X_CHOOSE_THEN (← q r"h':real^N->complex") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"UNIONS {(u:real^N->real^N->bool) x | x IN t}") THEN
      CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      ASM_SIMP_TAC [OPEN_IN_UNIONS, FORALL_IN_GSPEC] THEN
      EXISTS_TAC (← q r"h':real^N->complex") THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [FORALL_IN_UNIONS, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC [FORALL_IN_GSPEC] THEN
      X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      X_GEN_TAC (← q r"y:real^N") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"y:real^N", ← q r"x:real^N"]) THEN
      ASM_REWRITE_TAC [] THEN
      ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN SUBST1_TAC] THEN
      ASM_MESON_TAC []])

  pure { CONTRACTIBLE_IMP_HOLOMORPHIC_ACS, CONTRACTIBLE_IMP_HOLOMORPHIC_ACS_BOUNDED,
         INESSENTIAL_NEIGHBOURHOOD_EXTENSION_LOGARITHM }
/- ------------------------------------------------------------------------- -/
/- The "borsukian" property of sets: definition and basic characterizations. -/
/- (moretop.ml 5421-5688)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MOR where
  borsukian : thm
  BORSUKIAN_RETRACTION_GEN : thm
  RETRACT_OF_BORSUKIAN : thm
  HOMEOMORPHIC_BORSUKIAN : thm
  HOMEOMORPHIC_BORSUKIAN_EQ : thm
  BORSUKIAN_TRANSLATION : thm
  BORSUKIAN_INJECTIVE_LINEAR_IMAGE : thm
  HOMEOMORPHISM_BORSUKIANNESS : thm
  HOMOTOPY_EQUIVALENT_BORSUKIANNESS : thm
  BORSUKIAN_ALT : thm
  BORSUKIAN_CONTINUOUS_LOGARITHM : thm
  BORSUKIAN_CONTINUOUS_LOGARITHM_CIRCLE : thm
  BORSUKIAN_CONTINUOUS_LOGARITHM_CIRCLE_CX : thm
  BORSUKIAN_CIRCLE : thm
  BORSUKIAN_CIRCLE_ALT : thm
  CONTRACTIBLE_IMP_BORSUKIAN : thm
  CONIC_IMP_BORSUKIAN : thm
  SIMPLY_CONNECTED_IMP_BORSUKIAN : thm
  STARLIKE_IMP_BORSUKIAN : thm
  BORSUKIAN_EMPTY : thm
  BORSUKIAN_UNIV : thm
  CONVEX_IMP_BORSUKIAN : thm
  BORSUKIAN_1_GEN : thm
  BORSUKIAN_1 : thm
  BORSUKIAN_SPHERE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOR [HolBase] (D : MoreTopDeps) (BMOC : MOC) (BMON : MON) (BMOO : MOO) (BMOP : MOP) : ExceptT String IO MOR := do
  -- @@SCOPE BEGIN
  let { HOMEOMORPHIC_SPHERES_EQ, SIMPLY_CONNECTED_SPHERE, .. } := BMOC
  let { SIMPLY_CONNECTED_SPHERE_EQ, .. } := BMON
  let { INESSENTIAL_EQ_CONTINUOUS_LOGARITHM, INESSENTIAL_EQ_CONTINUOUS_LOGARITHM_CIRCLE,
        .. } := BMOO
  let { CONTINUOUS_LOGARITHM_ON_SIMPLY_CONNECTED, .. } := BMOP
  let { CONIC_IMP_CONTRACTIBLE, CONNECTED_SPHERE_EQ,
        HOMOTOPY_EQUIVALENT_COHOMOTOPIC_TRIVIALITY_NULL, LOCALLY_PATH_CONNECTED_SPHERE,
        PATH_CONNECTED_PUNCTURED_UNIVERSE, PATH_CONNECTED_SPHERE,
        STARLIKE_IMP_CONTRACTIBLE, .. } := D.qpaths
  let { CONVEX_IMP_STARLIKE, .. } := D.qconvex
  let { ANR_SPHERE, COHOMOTOPICALLY_TRIVIAL_1D, CONTRACTIBLE_SPHERE, retract_of,
        RETRACTION, .. } := D.qdegree
  let { CEXP_ADD, .. } := D.ra.tsa
  let { REAL_EXP_EQ_1, .. } := D.ra.tsb
  let { NORM_CEXP, .. } := D.ra.tsf
  let { CEXP_CLOG, CONTINUOUS_ON_CLOG, .. } := D.ra.tsm
  let { COMPLEX_IN_SPHERE_0, .. } := D.ra.ts.kna
  let { CONTINUOUS_ON_COMPLEX_DIV, CONTINUOUS_ON_COMPLEX_LMUL, .. } := D.ra.ts.knc
  let { CONTINUOUS_ON_CX_IM, CONTINUOUS_ON_CX_LIFT, .. } := D.ra.ts.knd
  let { COMPLEX_EQ, .. } := D.ra.ts.cn.cxa
  let { COMPLEX_NORM_CX, COMPLEX_VEC_0, CX_INJ, IM_CX, IM_MUL_II, RE_CX, RE_MUL_II,
        .. } := D.ra.ts.cn.cxc
  let { COMPLEX_FIELD, .. } := D.ra.ts.cn.cxe
  let { COMPLEX_NORM_0, COMPLEX_NORM_DIV, COMPLEX_NORM_NZ, COMPLEX_NORM_ZERO,
        .. } := D.ra.ts.cn.cxf
  let { add_linear_invariants, add_translation_invariants, ARITH_RULE, ASM_MESON_TAC,
        ASM_REAL_ARITH_TAC, MESON_TAC, new_definition, REAL_ARITH_TAC, SET_RULE, SET_TAC,
        .. } := D.ra.ts.cn.cx.cvx
  let { ARITH, CONJ_ASSOC, CONTRAPOS_THM, DIMINDEX_1, DIMINDEX_2, DIMINDEX_GE_1,
        .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, IMAGE_ID, IMP_CONJ, .. } := D.ra.ts.cn.cx.cvx.core2
  let { LE_REFL, LEFT_IMP_EXISTS_THM, MONO_EXISTS, MONO_FORALL, REAL_DIV_REFL,
        .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_LT_01, REAL_LT_IMP_LE, REAL_LT_REFL, .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_NEG_0, REAL_NOT_LT, SUBSET, SUBSET_REFL, .. } := D.ra.ts.cn.cx.cvx.core5
  let { o_ASSOC, o_DEF, .. } := D.ra.ts.cn.cx.cvx.core6
  let { DIST_SYM, .. } := D.ra.ts.cn.cx.cvx.vec1
  let { NORM_EQ_0, .. } := D.ra.ts.cn.cx.cvx.vec2
  let { REAL_ABS_NORM, .. } := D.ra.ts.cn.cx.cvx.vec3
  let { dist, .. } := D.ra.ts.cn.cx.cvx.vec4
  let { CONTINUOUS_ON_ADD, CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_ID,
        CONTINUOUS_ON_LIFT_NORM_COMPOSE, HOMEOMORPHIC_REFL, .. } := D.ra.ts.cn.cx.cvx.top3
  let { HOMEOMORPHIC_SYM, HOMEOMORPHISM_OF_SUBSETS, .. } := D.ra.ts.cn.cx.cvx.top4
  let { homeomorphic, homeomorphism, SPHERE_EMPTY, .. } := D.ra.ts.cn.cx.cvx.top5
  let { COHOMOTOPICALLY_TRIVIAL_RETRACTION_NULL_GEN, CONTRACTIBLE_EMPTY,
        CONTRACTIBLE_IMP_PATH_CONNECTED, CONTRACTIBLE_UNIV, HOMOTOPIC_TRIVIALITY,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths1
  let { contractible, NULLHOMOTOPIC_FROM_CONTRACTIBLE,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths2
  let { HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF, HOMEOMORPHIC_TRANSLATION_SELF,
        SPHERE_SING, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology2
  let { CONVEX_SING, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx3
  -- @@SCOPE END

  let borsukian ← new_definition
   r"borsukian(s:real^N->bool) <=>
        !f. f continuous_on s /\ IMAGE f s SUBSET ((:real^2) DIFF {Cx(&0)})
            ==> ?a. homotopic_with (\h. T)
                     (subtopology euclidean s,
                      subtopology euclidean ((:real^2) DIFF {Cx(&0)}))
                                   f (\x. a)"

  let BORSUKIAN_RETRACTION_GEN ← prove
   r"!s:real^M->bool t:real^N->bool h k.
        h continuous_on s /\ IMAGE h s = t /\
        k continuous_on t /\ IMAGE k t SUBSET s /\
        (!y. y IN t ==> h(k y) = y) /\
        borsukian s
        ==> borsukian t"
   (REPEAT GEN_TAC THEN REWRITE_TAC [borsukian] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o check (HolCore.Basics.is_forall o concl)) THEN
    PURE_ONCE_REWRITE_TAC [← TAUT (← q r"p /\ q <=> p /\ q /\ T")] THEN
    MATCH_MP_TAC (← ONCE_REWRITE_RULE [IMP_CONJ]
      COHOMOTOPICALLY_TRIVIAL_RETRACTION_NULL_GEN) THEN
    REWRITE_TAC [] THEN ASM_MESON_TAC [])

  let RETRACT_OF_BORSUKIAN ← prove
   r"!s t:real^N->bool. borsukian t /\ s retract_of t ==> borsukian s"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    MATCH_MP_TAC (← ONCE_REWRITE_RULE [IMP_CONJ] (← REWRITE_RULE [CONJ_ASSOC]
          BORSUKIAN_RETRACTION_GEN)) THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [retract_of]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"r:real^N->real^N") THEN
    REWRITE_TAC [RETRACTION] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC (← q r"\x:real^N. x") THEN ASM_REWRITE_TAC [CONTINUOUS_ON_ID, IMAGE_ID])

  let HOMEOMORPHIC_BORSUKIAN ← prove
   r"!s:real^M->bool t:real^N->bool.
        s homeomorphic t /\ borsukian s ==> borsukian t"
   (REWRITE_TAC [homeomorphic, homeomorphism] THEN
    MESON_TAC [BORSUKIAN_RETRACTION_GEN, SUBSET_REFL])

  let HOMEOMORPHIC_BORSUKIAN_EQ ← prove
   r"!s:real^M->bool t:real^N->bool.
     s homeomorphic t ==> (borsukian s <=> borsukian t)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] HOMEOMORPHIC_BORSUKIAN) THEN
    ASM_MESON_TAC [HOMEOMORPHIC_SYM])

  let BORSUKIAN_TRANSLATION ← prove
   r"!a:real^N s. borsukian (IMAGE (\x. a + x) s) <=> borsukian s"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_BORSUKIAN_EQ THEN
    REWRITE_TAC [HOMEOMORPHIC_TRANSLATION_SELF])

  add_translation_invariants [BORSUKIAN_TRANSLATION]

  let BORSUKIAN_INJECTIVE_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (borsukian(IMAGE f s) <=> borsukian s)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_BORSUKIAN_EQ THEN
    ASM_MESON_TAC [HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF,
                   HOMEOMORPHIC_REFL])

  add_linear_invariants [BORSUKIAN_INJECTIVE_LINEAR_IMAGE]

  let HOMEOMORPHISM_BORSUKIANNESS ← prove
   r"!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (borsukian(IMAGE f k) <=> borsukian k)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_BORSUKIAN_EQ THEN
    ONCE_REWRITE_TAC [HOMEOMORPHIC_SYM] THEN REWRITE_TAC [homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [← q r"f:real^M->real^N", ← q r"g:real^N->real^M"] THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ]
            HOMEOMORPHISM_OF_SUBSETS)) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [homeomorphism]) THEN ASM SET_TAC [])

  let HOMOTOPY_EQUIVALENT_BORSUKIANNESS ← prove
   r"!s:real^M->bool t:real^N->bool.
        s homotopy_equivalent t
        ==> (borsukian s <=> borsukian t)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [borsukian] THEN
    MATCH_MP_TAC HOMOTOPY_EQUIVALENT_COHOMOTOPIC_TRIVIALITY_NULL THEN
    ASM_REWRITE_TAC [])

  let BORSUKIAN_ALT ← prove
   r"!s:real^N->bool.
        borsukian s <=>
        !f g:real^N->real^2.
           f continuous_on s /\ IMAGE f s SUBSET ((:real^2) DIFF {Cx(&0)}) /\
           g continuous_on s /\ IMAGE g s SUBSET ((:real^2) DIFF {Cx(&0)})
           ==> homotopic_with (\h. T)
                (subtopology euclidean s,
                 subtopology euclidean ((:real^2) DIFF {Cx (&0)})) f g"
   (REWRITE_TAC [borsukian, HOMOTOPIC_TRIVIALITY] THEN
    SIMP_TAC [PATH_CONNECTED_PUNCTURED_UNIVERSE, DIMINDEX_2, LE_REFL])

  let BORSUKIAN_CONTINUOUS_LOGARITHM ← prove
   r"!s:real^N->bool.
        borsukian s <=>
        !f. f continuous_on s /\ IMAGE f s SUBSET ((:real^2) DIFF {Cx(&0)})
            ==> ?g. g continuous_on s /\ (!x. x IN s ==> f(x) = cexp(g x))"
   (REWRITE_TAC [borsukian, INESSENTIAL_EQ_CONTINUOUS_LOGARITHM])

  let BORSUKIAN_CONTINUOUS_LOGARITHM_CIRCLE ← prove
   r"!s:real^N->bool.
        borsukian s <=>
           !f. f continuous_on s /\ IMAGE f s SUBSET sphere(Cx(&0),&1)
               ==> ?g. g continuous_on s /\ (!x. x IN s ==> f(x) = cexp(g x))"
   (GEN_TAC THEN REWRITE_TAC [BORSUKIAN_CONTINUOUS_LOGARITHM] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, COMPLEX_IN_SPHERE_0, ← SET_RULE
     (← q r"IMAGE f s SUBSET UNIV DIFF {a} <=> !z. z IN s ==> ~(f z = a)")] THEN
    EQ_TAC THEN DISCH_TAC THEN
    X_GEN_TAC (← q r"f:real^N->complex") THEN STRIP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC (← q r"x:real^N") THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real^N")) THEN
      ASM_REWRITE_TAC [COMPLEX_NORM_0] THEN REAL_ARITH_TAC,
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"\x:real^N. f(x) / Cx(norm(f x))")) THEN
      ASM_SIMP_TAC [COMPLEX_NORM_DIV, COMPLEX_NORM_CX, REAL_ABS_NORM,
                    REAL_DIV_REFL, NORM_EQ_0, COMPLEX_NORM_ZERO] THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN
        ASM_REWRITE_TAC [CX_INJ, COMPLEX_NORM_ZERO, CONTINUOUS_ON_CX_LIFT] THEN
        ASM_SIMP_TAC [CONTINUOUS_ON_LIFT_NORM_COMPOSE],
        ASM_SIMP_TAC [CX_INJ, COMPLEX_NORM_ZERO, ← ExceptT.mk (COMPLEX_FIELD
         (← q r"~(z = Cx(&0)) ==> (w / z = u <=> w = z * u)"))] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->complex") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC
         (← q r"\x. clog(Cx(norm(f x:complex))) + (g:real^N->complex)(x)") THEN
        ASM_SIMP_TAC [CEXP_ADD, CEXP_CLOG, CX_INJ, COMPLEX_NORM_ZERO] THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
        ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        ASM_SIMP_TAC [CONTINUOUS_ON_CX_LIFT, CONTINUOUS_ON_LIFT_NORM_COMPOSE] THEN
        MATCH_MP_TAC CONTINUOUS_ON_CLOG THEN
        ASM_SIMP_TAC [IMP_CONJ, FORALL_IN_IMAGE, RE_CX, COMPLEX_NORM_NZ]]])

  let BORSUKIAN_CONTINUOUS_LOGARITHM_CIRCLE_CX ← prove
   r"!s:real^N->bool.
        borsukian s <=>
            !f. f continuous_on s /\ IMAGE f s SUBSET sphere(Cx(&0),&1)
            ==> ?g. (Cx o g) continuous_on s /\
                    (!x. x IN s ==> f x = cexp(ii * Cx(g x)))"
   (GEN_TAC THEN REWRITE_TAC [BORSUKIAN_CONTINUOUS_LOGARITHM_CIRCLE] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, COMPLEX_IN_SPHERE_0] THEN EQ_TAC THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"f:real^N->complex") THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THENL
     [X_GEN_TAC (← q r"g:real^N->complex") THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"Im o (g:real^N->complex)") THEN
      ASM_SIMP_TAC [CONTINUOUS_ON_CX_IM, CONTINUOUS_ON_COMPOSE, o_ASSOC] THEN
      X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real^N"))) THEN ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC (← q r"(f:real^N->complex) x = cexp(g x)") THEN
      ASM_REWRITE_TAC [NORM_CEXP, o_DEF, REAL_EXP_EQ_1] THEN
      DISCH_TAC THEN AP_TERM_TAC THEN
      ASM_REWRITE_TAC [COMPLEX_EQ, RE_MUL_II, IM_MUL_II, RE_CX, IM_CX] THEN
      REWRITE_TAC [REAL_NEG_0],
      X_GEN_TAC (← q r"g:real^N->real") THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"\x:real^N. ii * Cx(g x)") THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
      ASM_REWRITE_TAC [← GSYM o_DEF]])

  let BORSUKIAN_CIRCLE ← prove
   r"!s:real^N->bool.
        borsukian s <=>
            !f. f continuous_on s /\ IMAGE f s SUBSET sphere(Cx(&0),&1)
                ==> ?a. homotopic_with (\h. T)
                         (subtopology euclidean s,
                          subtopology euclidean (sphere(Cx(&0),&1)))
                         f (\x. a)"
   (REWRITE_TAC [← GSYM COMPLEX_VEC_0] THEN
    REWRITE_TAC [INESSENTIAL_EQ_CONTINUOUS_LOGARITHM_CIRCLE] THEN
    REWRITE_TAC [BORSUKIAN_CONTINUOUS_LOGARITHM_CIRCLE_CX] THEN
    REWRITE_TAC [COMPLEX_VEC_0])

  let BORSUKIAN_CIRCLE_ALT ← prove
   r"!s:real^N->bool.
        borsukian s <=>
        !f g:real^N->real^2.
           f continuous_on s /\ IMAGE f s SUBSET sphere(Cx(&0),&1) /\
           g continuous_on s /\ IMAGE g s SUBSET sphere(Cx(&0),&1)
           ==> homotopic_with (\h. T)
                (subtopology euclidean s,
                 subtopology euclidean (sphere(Cx(&0),&1))) f g"
   (REWRITE_TAC [BORSUKIAN_CIRCLE, HOMOTOPIC_TRIVIALITY] THEN
    SIMP_TAC [PATH_CONNECTED_SPHERE, DIMINDEX_2, LE_REFL])

  let CONTRACTIBLE_IMP_BORSUKIAN ← prove
   r"!s:real^N->bool. contractible s ==> borsukian s"
   (SIMP_TAC [borsukian, CONTRACTIBLE_IMP_PATH_CONNECTED] THEN
    MESON_TAC [NULLHOMOTOPIC_FROM_CONTRACTIBLE])

  let CONIC_IMP_BORSUKIAN ← prove
   r"!s:real^N->bool. conic s ==> borsukian s"
   (MESON_TAC [CONIC_IMP_CONTRACTIBLE, CONTRACTIBLE_IMP_BORSUKIAN])

  let SIMPLY_CONNECTED_IMP_BORSUKIAN ← prove
   r"!s:real^N->bool.
        simply_connected s /\ locally path_connected s ==> borsukian s"
   (SIMP_TAC [BORSUKIAN_CONTINUOUS_LOGARITHM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_LOGARITHM_ON_SIMPLY_CONNECTED THEN
    ASM SET_TAC [])

  let STARLIKE_IMP_BORSUKIAN ← prove
   r"!s:real^N->bool. starlike s ==> borsukian s"
   (SIMP_TAC [CONTRACTIBLE_IMP_BORSUKIAN, STARLIKE_IMP_CONTRACTIBLE])

  let BORSUKIAN_EMPTY ← prove
   r"borsukian({}:real^N->bool)"
   (SIMP_TAC [CONTRACTIBLE_IMP_BORSUKIAN, CONTRACTIBLE_EMPTY])

  let BORSUKIAN_UNIV ← prove
   r"borsukian(:real^N)"
   (SIMP_TAC [CONTRACTIBLE_IMP_BORSUKIAN, CONTRACTIBLE_UNIV])

  let CONVEX_IMP_BORSUKIAN ← prove
   r"!s:real^N->bool. convex s ==> borsukian s"
   (MESON_TAC [STARLIKE_IMP_BORSUKIAN, CONVEX_IMP_STARLIKE, BORSUKIAN_EMPTY])

  let BORSUKIAN_1_GEN ← prove
   r"!s:real^N->bool.
        (dimindex(:N) = 1 \/ ?r:real^1->bool. s homeomorphic r)
        ==> borsukian s"
   (GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [BORSUKIAN_CIRCLE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC COHOMOTOPICALLY_TRIVIAL_1D THEN
    ASM_REWRITE_TAC [ANR_SPHERE, CONNECTED_SPHERE_EQ] THEN
    REWRITE_TAC [DIMINDEX_2, LE_REFL])

  let BORSUKIAN_1 ← prove
   r"!s:real^1->bool. borsukian s"
   (GEN_TAC THEN MATCH_MP_TAC BORSUKIAN_1_GEN THEN
    REWRITE_TAC [DIMINDEX_1])

  let BORSUKIAN_SPHERE ← prove
   r"!a:real^N r. borsukian(sphere(a,r)) <=> r <= &0 \/ ~(dimindex(:N) = 2)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"r < &0") THEN
    ASM_SIMP_TAC [SPHERE_EMPTY, BORSUKIAN_EMPTY, REAL_LT_IMP_LE] THEN
    ASM_CASES_TAC (← q r"r = &0") THEN
    ASM_SIMP_TAC [REAL_LT_REFL, SPHERE_SING, CONVEX_IMP_BORSUKIAN, CONVEX_SING,
                  ← GSYM REAL_NOT_LT] THEN
    SUBGOAL_THEN (← q r"&0 < r") ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC, ASM_REWRITE_TAC []] THEN
    ASM_CASES_TAC (← q r"dimindex(:N) = 1") THENL
     [ASM_SIMP_TAC [ARITH, BORSUKIAN_1_GEN], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"dimindex(:N) = 2") THEN ASM_REWRITE_TAC [] THENL
     [SUBGOAL_THEN (← q r"~borsukian(sphere(Cx(&0),&1))") MP_TAC THENL
       [REWRITE_TAC [BORSUKIAN_CIRCLE] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"\z:complex. z")) THEN
        REWRITE_TAC [CONTINUOUS_ON_ID, IMAGE_ID, SUBSET_REFL] THEN
        ASM_REWRITE_TAC [← GSYM contractible, CONTRACTIBLE_SPHERE] THEN
        REAL_ARITH_TAC,
        REWRITE_TAC [CONTRAPOS_THM] THEN MATCH_MP_TAC
         (← ONCE_REWRITE_RULE [IMP_CONJ] HOMEOMORPHIC_BORSUKIAN) THEN
        REWRITE_TAC [HOMEOMORPHIC_SPHERES_EQ] THEN
        ASM_REWRITE_TAC [DIMINDEX_2, REAL_LT_01]],
      MATCH_MP_TAC SIMPLY_CONNECTED_IMP_BORSUKIAN THEN
      ASM_SIMP_TAC [SIMPLY_CONNECTED_SPHERE] THEN
      REWRITE_TAC [← ONCE_REWRITE_RULE [DIST_SYM] (← GSYM dist)] THEN
      ASM_SIMP_TAC [LOCALLY_PATH_CONNECTED_SPHERE,
                    SIMPLY_CONNECTED_SPHERE_EQ] THEN
      DISJ1_TAC THEN
      MATCH_MP_TAC (← ARITH_RULE (← q r"1 <= n /\ ~(n = 1) /\ ~(n = 2) ==> 3 <= n")) THEN
      ASM_REWRITE_TAC [DIMINDEX_GE_1]])

  pure { borsukian, BORSUKIAN_RETRACTION_GEN, RETRACT_OF_BORSUKIAN,
         HOMEOMORPHIC_BORSUKIAN, HOMEOMORPHIC_BORSUKIAN_EQ, BORSUKIAN_TRANSLATION,
         BORSUKIAN_INJECTIVE_LINEAR_IMAGE, HOMEOMORPHISM_BORSUKIANNESS,
         HOMOTOPY_EQUIVALENT_BORSUKIANNESS, BORSUKIAN_ALT,
         BORSUKIAN_CONTINUOUS_LOGARITHM, BORSUKIAN_CONTINUOUS_LOGARITHM_CIRCLE,
         BORSUKIAN_CONTINUOUS_LOGARITHM_CIRCLE_CX, BORSUKIAN_CIRCLE,
         BORSUKIAN_CIRCLE_ALT, CONTRACTIBLE_IMP_BORSUKIAN, CONIC_IMP_BORSUKIAN,
         SIMPLY_CONNECTED_IMP_BORSUKIAN, STARLIKE_IMP_BORSUKIAN, BORSUKIAN_EMPTY,
         BORSUKIAN_UNIV, CONVEX_IMP_BORSUKIAN, BORSUKIAN_1_GEN, BORSUKIAN_1,
         BORSUKIAN_SPHERE }
/- ------------------------------------------------------------------------- -/
/- The "borsukian" property: unions, components and images.                  -/
/- (moretop.ml 5689-5997)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MOS where
  BORSUKIAN_OPEN_UNION : thm
  BORSUKIAN_CLOSED_UNION : thm
  BORSUKIAN_SEPARATION_COMPACT : thm
  BORSUKIAN_COMPONENTWISE_EQ : thm
  BORSUKIAN_COMPONENTWISE : thm
  BORSUKIAN_MONOTONE_IMAGE_COMPACT : thm
  BORSUKIAN_OPEN_MAP_IMAGE_COMPACT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOS [HolBase] (D : MoreTopDeps) (BMOL : MOL) (BMOR : MOR) : ExceptT String IO MOS := do
  -- @@SCOPE BEGIN
  let { BORSUK_SEPARATION_THEOREM, .. } := BMOL
  let { BORSUKIAN_ALT, BORSUKIAN_CIRCLE, BORSUKIAN_CONTINUOUS_LOGARITHM,
        BORSUKIAN_CONTINUOUS_LOGARITHM_CIRCLE_CX, .. } := BMOR
  let { CLOSED_COMPACT_PROJECTION, CLOSED_MAP_IFF_UPPER_HEMICONTINUOUS_PREIMAGE,
        COMPACT_ATTAINS_INF, CONTINUOUS_FROM_CLOSED_GRAPH,
        CONTINUOUS_IMP_CLOSED_MAP_EXPLICIT, CONTINUOUS_ON_CASES_LOCAL_OPEN,
        OPEN_MAP_IFF_LOWER_HEMICONTINUOUS_PREIMAGE, UPPER_LOWER_HEMICONTINUOUS_EXPLICIT,
        .. } := D.qtopology
  let { COHOMOTOPICALLY_TRIVIAL_ON_COMPONENTS, OPEN_IMP_ANR, .. } := D.qdegree
  let { CEXP_ADD, CEXP_NZ, CEXP_SUB, .. } := D.ra.tsa
  let { PI_POS, .. } := D.ra.tse
  let { COMPLEX_EQ_CEXP, .. } := D.ra.tsf
  let { CONTINUOUS_ON_CX_LIFT, .. } := D.ra.ts.knd
  let { CLOSED_PCROSS, CONTINUOUS_DISCRETE_RANGE_CONSTANT, .. } := D.ra.ts.qtopology
  let { COMPLEX_EQ_SUB_RADD, COMPLEX_MUL_LID, .. } := D.ra.ts.cn.cxb
  let { COMPLEX_VEC_0, DIST_CX, IM_SUB, .. } := D.ra.ts.cn.cxc
  let { COMPLEX_RING, .. } := D.ra.ts.cn.cxd
  let { COMPLEX_NORM_GE_RE_IM, .. } := D.ra.ts.cn.cxg
  let { CLOSED_IN_COMPACT, .. } := D.ra.ts.cn.ms.qtopology1
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC, REAL_ARITH, SET_RULE, SET_TAC,
        .. } := D.ra.ts.cn.cx.cvx
  let { CONJ_ASSOC, CONTRAPOS_THM, DIMINDEX_2, EXISTS_IN_GSPEC, EXTENSION, FORALL_IN_GSPEC,
        .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_PASTECART, FSTCART_PASTECART, IMAGE_o, IMP_CONJ, IMP_CONJ_ALT, INTER_SUBSET,
        .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INTER, IN_SING, IN_UNIV, LE_REFL, LEFT_IMP_EXISTS_THM, MONO_EXISTS,
        PASTECART_IN_PCROSS, PASTECART_INJ, .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_LET_TRANS, .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_NOT_LE, RIGHT_EXISTS_IMP_THM, SIMPLE_IMAGE_GEN, SKOLEM_THM, SNDCART_PASTECART,
        SUBSET_REFL, SUBSET_RESTRICT, SUBSET_UNION, .. } := D.ra.ts.cn.cx.cvx.core5
  let { o_DEF, o_THM, UNIV_NOT_EMPTY, UNWIND_THM1, .. } := D.ra.ts.cn.cx.cvx.core6
  let { DIST_SYM, .. } := D.ra.ts.cn.cx.cvx.vec1
  let { LINEAR_FSTCART, LINEAR_SNDCART, .. } := D.ra.ts.cn.cx.cvx.vec2
  let { VECTOR_SUB_EQ, VECTOR_SUB_REFL, .. } := D.ra.ts.cn.cx.cvx.vec4
  let { CLOSED_SING, CLOSED_UNIV, .. } := D.ra.ts.cn.cx.cvx.top1
  let { COMPACT_CONTINUOUS_IMAGE, COMPACT_IMP_BOUNDED, COMPACT_IMP_CLOSED,
        .. } := D.ra.ts.cn.cx.cvx.top2
  let { CONTINUOUS_ON_ADD, CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_CONST, CONTINUOUS_ON_SUB,
        CONTINUOUS_ON_SUBSET, .. } := D.ra.ts.cn.cx.cvx.top3
  let { LINEAR_CONTINUOUS_ON, .. } := D.ra.ts.cn.cx.cvx.top4
  let { continuous_on, OPEN_UNIV, PROPER_MAP_FROM_COMPACT, .. } := D.ra.ts.cn.cx.cvx.top5
  let { CLOSED_IN_SING, COMPACT_UNIFORMLY_CONTINUOUS, CONTINUOUS_CLOSED_IN_PREIMAGE_GEN,
        CONTINUOUS_ON_CASES_LOCAL, CONTINUOUS_ON_PASTECART,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { OPEN_DIFF, uniformly_continuous_on, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology2
  let { IMAGE_FSTCART_PCROSS, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qses
  let { CONTINUOUS_CLOSED_PREIMAGE, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qtop
  -- @@SCOPE END

  -- The common part of the open and closed union proofs: `cases` is
  -- CONTINUOUS_ON_CASES_LOCAL_OPEN or CONTINUOUS_ON_CASES_LOCAL.
  let unionTac (cases : thm) : ExceptT String IO tactic := do
    pure (REPEAT GEN_TAC THEN SIMP_TAC [BORSUKIAN_CONTINUOUS_LOGARITHM] THEN
    STRIP_TAC THEN X_GEN_TAC (← q r"f:real^N->complex") THEN STRIP_TAC THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"f:real^N->complex"))) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC [CONTINUOUS_ON_SUBSET, SUBSET_UNION], ASM SET_TAC []],
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->complex") STRIP_ASSUME_TAC)] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC [CONTINUOUS_ON_SUBSET, SUBSET_UNION], ASM SET_TAC []],
      DISCH_THEN (X_CHOOSE_THEN (← q r"h:real^N->complex") STRIP_ASSUME_TAC)] THEN
    ASM_CASES_TAC (← q r"s INTER t:real^N->bool = {}") THENL
     [EXISTS_TAC (← q r"(\x. if x IN s then g x else h x):real^N->complex") THEN
      CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      MATCH_MP_TAC cases THEN
      ASM_REWRITE_TAC [] THEN ASM SET_TAC [],
      ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"(\x. g x - h x):real^N->complex", ← q r"s INTER t:real^N->bool"]
     CONTINUOUS_DISCRETE_RANGE_CONSTANT) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        ASM_MESON_TAC [CONTINUOUS_ON_SUBSET, INTER_SUBSET],
        X_GEN_TAC (← q r"x:real^N") THEN REWRITE_TAC [IN_INTER] THEN STRIP_TAC THEN
        EXISTS_TAC (← q r"&2 * pi") THEN
        REWRITE_TAC [← REAL_ARITH (← q r"&0 < &2 * x <=> &0 < x"), PI_POS] THEN
        X_GEN_TAC (← q r"y:real^N") THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN REWRITE_TAC [REAL_NOT_LE] THEN
        ONCE_REWRITE_TAC [← ExceptT.mk (COMPLEX_RING
         (← q r"a - b:complex = c - d <=> a - c = b - d"))] THEN
        DISCH_TAC THEN MATCH_MP_TAC COMPLEX_EQ_CEXP THEN
        REWRITE_TAC [CEXP_SUB] THEN CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT]
         REAL_LET_TRANS)) THEN
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← ExceptT.mk (COMPLEX_RING
         (← q r"(a - b) - (c - d):complex = (a - c) - (b - d)"))] THEN
        REWRITE_TAC [← GSYM IM_SUB, COMPLEX_NORM_GE_RE_IM]],
      REWRITE_TAC [IN_INTER, COMPLEX_EQ_SUB_RADD] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"a:complex")) THEN
      EXISTS_TAC (← q r"(\x. if x IN s then g x else a + h x):real^N->complex") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC cases THEN
        ASM_SIMP_TAC [CONTINUOUS_ON_ADD, CONTINUOUS_ON_CONST] THEN
        ASM SET_TAC [],
        GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
         [ASM_MESON_TAC [], REWRITE_TAC [CEXP_ADD]] THEN
        SUBGOAL_THEN (← q r"?y:real^N. y IN s /\ y IN t") STRIP_ASSUME_TAC THENL
         [ASM SET_TAC [], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"cexp(a + h(y:real^N)) = cexp(h y)") MP_TAC THENL
         [ASM_MESON_TAC [], REWRITE_TAC [CEXP_ADD]] THEN
        SIMP_TAC [← ExceptT.mk (COMPLEX_RING (← q r"a * z = z <=> a = Cx(&1) \/ z = Cx(&0)")),
                  CEXP_NZ, COMPLEX_MUL_LID] THEN
        ASM SET_TAC []]])

  let BORSUKIAN_OPEN_UNION ← prove
   r"!s t:real^N->bool.
        open_in (subtopology euclidean (s UNION t)) s /\
        open_in (subtopology euclidean (s UNION t)) t /\
        borsukian s /\ borsukian t /\ connected(s INTER t)
        ==> borsukian(s UNION t)"
   (← unionTac CONTINUOUS_ON_CASES_LOCAL_OPEN)

  let BORSUKIAN_CLOSED_UNION ← prove
   r"!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        borsukian s /\ borsukian t /\ connected(s INTER t)
        ==> borsukian(s UNION t)"
   (← unionTac CONTINUOUS_ON_CASES_LOCAL)

  let BORSUKIAN_SEPARATION_COMPACT ← prove
   r"!s:real^2->bool.
        compact s ==> (borsukian s <=> connected((:real^2) DIFF s))"
   (SIMP_TAC [BORSUKIAN_CIRCLE, BORSUK_SEPARATION_THEOREM, DIMINDEX_2, LE_REFL,
              COMPLEX_VEC_0])

  let BORSUKIAN_COMPONENTWISE_EQ ← prove
   r"!s:real^N->bool.
        locally connected s \/ compact s
        ==> (borsukian s <=> !c. c IN components s ==> borsukian c)"
   (GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [BORSUKIAN_ALT] THEN
    MATCH_MP_TAC COHOMOTOPICALLY_TRIVIAL_ON_COMPONENTS THEN
    ASM_SIMP_TAC [OPEN_IMP_ANR, OPEN_DIFF, OPEN_UNIV, CLOSED_SING])

  let BORSUKIAN_COMPONENTWISE ← prove
   r"!s:real^N->bool.
        (locally connected s \/ compact s) /\
        (!c. c IN components s ==> borsukian c)
        ==> borsukian s"
   (MESON_TAC [BORSUKIAN_COMPONENTWISE_EQ])

  let BORSUKIAN_MONOTONE_IMAGE_COMPACT ← prove
   r"!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\ compact s /\
        (!y. y IN t ==> connected {x | x IN s /\ f x = y}) /\
        borsukian s
        ==> borsukian t"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [BORSUKIAN_CONTINUOUS_LOGARITHM] THEN
    X_GEN_TAC (← q r"g:real^N->complex") THEN STRIP_TAC THEN FIRST_X_ASSUM
     (MP_TAC o GEN_REWRITE_RULE id [BORSUKIAN_CONTINUOUS_LOGARITHM]) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"(g:real^N->complex) o (f:real^M->real^N)")) THEN
    ASM_SIMP_TAC [IMAGE_o, CONTINUOUS_ON_COMPOSE, o_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"h:real^M->complex") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     (← q r"!y. ?x. y IN t ==> x IN s /\ (f:real^M->real^N) x = y")
    MP_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"f':real^N->real^M") THEN STRIP_TAC THEN
    EXISTS_TAC (← q r"(h:real^M->complex) o (f':real^N->real^M)") THEN
    REWRITE_TAC [o_THM] THEN CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
    MATCH_MP_TAC CONTINUOUS_FROM_CLOSED_GRAPH THEN
    EXISTS_TAC (← q r"IMAGE (h:real^M->complex) s") THEN
    ASM_SIMP_TAC [COMPACT_CONTINUOUS_IMAGE, IMAGE_o] THEN
    CONJ_TAC THENL [ASM SET_TAC [], REWRITE_TAC [o_THM]] THEN
    SUBGOAL_THEN
     (← q r"{pastecart x ((h:real^M->complex) ((f':real^N->real^M) x)) | x IN t} =
      {p | ?x. x IN s /\ pastecart x p IN
                         {z | z IN s PCROSS UNIV /\
                              (sndcart z - pastecart (f(fstcart z))
                                                    (h(fstcart z))) IN {vec 0}}}")
    SUBST1_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC CLOSED_COMPACT_PROJECTION THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
      ASM_SIMP_TAC [CLOSED_UNIV, CLOSED_PCROSS, COMPACT_IMP_CLOSED] THEN
      REWRITE_TAC [CLOSED_SING] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      SIMP_TAC [LINEAR_CONTINUOUS_ON, LINEAR_SNDCART] THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC [← GSYM o_DEF] THEN
      CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC [LINEAR_CONTINUOUS_ON, LINEAR_FSTCART, IMAGE_FSTCART_PCROSS] THEN
      ASM_REWRITE_TAC [UNIV_NOT_EMPTY]] THEN
    REWRITE_TAC [IN_ELIM_THM, PASTECART_IN_PCROSS, FSTCART_PASTECART,
                 SNDCART_PASTECART, IN_UNIV, IN_SING, VECTOR_SUB_EQ] THEN
    REWRITE_TAC [EXTENSION, FORALL_PASTECART, IN_ELIM_THM] THEN
    REWRITE_TAC [CONJ_ASSOC, PASTECART_INJ] THEN
    MAP_EVERY X_GEN_TAC [← q r"y:real^N", ← q r"z:complex"] THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"(p /\ q) /\ r <=> q /\ p /\ r")] THEN
    REWRITE_TAC [UNWIND_THM1] THEN EQ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"w:real^M") STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"?a. !x. x IN {x | x IN s /\ (f:real^M->real^N) x = y}
              ==> h x - h(f' y):complex = a")
    MP_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"a:complex") THEN
      DISCH_THEN (fun th => ASSUME_TAC th THEN MP_TAC th) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"(f':real^N->real^M) y")) THEN
      ANTS_TAC THENL [ASM SET_TAC [], REWRITE_TAC [VECTOR_SUB_REFL]] THEN
      DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [VECTOR_SUB_EQ]) THEN ASM SET_TAC []] THEN
    MATCH_MP_TAC CONTINUOUS_DISCRETE_RANGE_CONSTANT THEN
    REWRITE_TAC [IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC [],
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC [CONTINUOUS_ON_CONST] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN SET_TAC [],
      ALL_TAC] THEN
    X_GEN_TAC (← q r"v:real^M") THEN STRIP_TAC THEN
    EXISTS_TAC (← q r"&2 * pi") THEN
    REWRITE_TAC [← REAL_ARITH (← q r"&0 < &2 * x <=> &0 < x"), PI_POS] THEN
    X_GEN_TAC (← q r"u:real^M") THEN
    REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"a - x:complex = b - x <=> a = b"))] THEN
    DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN REWRITE_TAC [REAL_NOT_LE] THEN
    REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"(a - x) - (b - x):complex = a - b"))] THEN
    DISCH_TAC THEN MATCH_MP_TAC COMPLEX_EQ_CEXP THEN
    CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN REWRITE_TAC [← GSYM IM_SUB] THEN
    ASM_MESON_TAC [REAL_LET_TRANS, COMPLEX_NORM_GE_RE_IM])

  let BORSUKIAN_OPEN_MAP_IMAGE_COMPACT ← prove
   r"!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\ compact s /\
        (!u. open_in (subtopology euclidean s) u
             ==> open_in (subtopology euclidean t) (IMAGE f u)) /\
        borsukian s
        ==> borsukian t"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [BORSUKIAN_CONTINUOUS_LOGARITHM_CIRCLE_CX] THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"g:real^N->complex") THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(g:real^N->complex) o (f:real^M->real^N)")) THEN
    ASM_SIMP_TAC [IMAGE_o, CONTINUOUS_ON_COMPOSE, o_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"h:real^M->real") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     (← q r"!y. ?x. y IN t ==> x IN s /\ (f:real^M->real^N) x = y /\
                         (!x'. x' IN s /\ f x' = y ==> h x <= h x')")
    MP_TAC THENL
     [REWRITE_TAC [RIGHT_EXISTS_IMP_THM] THEN REPEAT STRIP_TAC THEN
      MP_TAC (← ISPEC (← q r"{ h x:real | x IN s /\ (f:real^M->real^N) x = y}")
           COMPACT_ATTAINS_INF) THEN
      REWRITE_TAC [FORALL_IN_GSPEC, EXISTS_IN_GSPEC, ← GSYM CONJ_ASSOC] THEN
      DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN REWRITE_TAC [← GSYM IMAGE_o] THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [REWRITE_TAC [o_DEF, ← GSYM CONTINUOUS_ON_CX_LIFT] THEN
        GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN SET_TAC [],
        ONCE_REWRITE_TAC [← SET_RULE (← q r"x = y <=> x IN {y}")] THEN
        MATCH_MP_TAC PROPER_MAP_FROM_COMPACT THEN
        ASM_MESON_TAC [CLOSED_IN_SING, SUBSET_REFL]],
      REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC (← q r"k:real^N->real^M") THEN DISCH_TAC THEN
    EXISTS_TAC (← q r"(h:real^M->real) o (k:real^N->real^M)") THEN
    REWRITE_TAC [o_THM] THEN CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
    REWRITE_TAC [continuous_on] THEN X_GEN_TAC (← q r"y:real^N") THEN
    DISCH_TAC THEN X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"Cx o (h:real^M->real)", ← q r"s:real^M->bool"]
          COMPACT_UNIFORMLY_CONTINUOUS) THEN
    ASM_REWRITE_TAC [uniformly_continuous_on] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"e:real")) THEN ASM_REWRITE_TAC [o_THM, DIST_CX] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL
     [← q r"\y. {x | x IN s /\ (f:real^M->real^N) x = y}",
      ← q r"s:real^M->bool", ← q r"t:real^N->bool"]
      UPPER_LOWER_HEMICONTINUOUS_EXPLICIT) THEN
    ASM_SIMP_TAC [← GSYM CLOSED_MAP_IFF_UPPER_HEMICONTINUOUS_PREIMAGE,
                  ← GSYM OPEN_MAP_IFF_LOWER_HEMICONTINUOUS_PREIMAGE,
                  SUBSET_REFL, SUBSET_RESTRICT] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [CONTINUOUS_IMP_CLOSED_MAP_EXPLICIT], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPECL [← q r"y:real^N", ← q r"d:real"]) THEN
    ASM_REWRITE_TAC [FORALL_IN_GSPEC, EXISTS_IN_GSPEC] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC COMPACT_IMP_BOUNDED, ASM SET_TAC []] THEN
      MATCH_MP_TAC CLOSED_IN_COMPACT THEN EXISTS_TAC (← q r"s:real^M->bool") THEN
      ASM_REWRITE_TAC [← SET_RULE (← q r"x IN s /\ f x = y <=> x IN s /\ f x IN {y}")] THEN
      MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_GEN THEN
      EXISTS_TAC (← q r"t:real^N->bool") THEN
      ASM_REWRITE_TAC [CLOSED_IN_SING, SUBSET_REFL],
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"q:real") THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*"))] THEN
    ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"y':real^N") THEN STRIP_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPEC (← q r"y':real^N")) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [DIST_SYM], ALL_TAC] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (MP_TAC o SPEC (← q r"(k:real^N->real^M) y"))
                               (MP_TAC o SPEC (← q r"(k:real^N->real^M) y'"))) THEN
    ASM_SIMP_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"w:real^M") STRIP_ASSUME_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"w':real^M") STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"y':real^N")) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"y:real^N")) THEN
    ASM_SIMP_TAC [] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"w:real^M")) THEN ASM_SIMP_TAC [] THEN DISCH_TAC THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"w':real^M")) THEN ASM_SIMP_TAC [] THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o SPECL [← q r"w:real^M", ← q r"(k:real^N->real^M) y'"]) THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"w':real^M", ← q r"(k:real^N->real^M) y"]) THEN
    ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC)

  pure { BORSUKIAN_OPEN_UNION, BORSUKIAN_CLOSED_UNION, BORSUKIAN_SEPARATION_COMPACT,
         BORSUKIAN_COMPONENTWISE_EQ, BORSUKIAN_COMPONENTWISE,
         BORSUKIAN_MONOTONE_IMAGE_COMPACT, BORSUKIAN_OPEN_MAP_IMAGE_COMPACT }
/- ------------------------------------------------------------------------- -/
/- Unicoherence (closed).                                                    -/
/- (moretop.ml 5998-6268)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MOT where
  unicoherent : thm
  HOMEOMORPHIC_UNICOHERENT : thm
  HOMEOMORPHIC_UNICOHERENT_EQ : thm
  UNICOHERENT_TRANSLATION : thm
  UNICOHERENT_INJECTIVE_LINEAR_IMAGE : thm
  HOMEOMORPHISM_UNICOHERENCE : thm
  BORSUKIAN_IMP_UNICOHERENT : thm
  CONTRACTIBLE_IMP_UNICOHERENT : thm
  CONVEX_IMP_UNICOHERENT : thm
  UNICOHERENT_UNIV : thm
  UNICOHERENT_MONOTONE_IMAGE_COMPACT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOT [HolBase] (D : MoreTopDeps) (BMOO : MOO) (BMOR : MOR) : ExceptT String IO MOT := do
  -- @@SCOPE BEGIN
  let { INESSENTIAL_EQ_CONTINUOUS_LOGARITHM, .. } := BMOO
  let { BORSUKIAN_CIRCLE, CONTRACTIBLE_IMP_BORSUKIAN, CONVEX_IMP_BORSUKIAN, .. } := BMOR
  let { CONNECTED_CLOSED_MONOTONE_PREIMAGE, CONTINUOUS_IMP_CLOSED_MAP_EXPLICIT,
        HOMEOMORPHISM_IMP_CLOSED_MAP, .. } := D.qtopology
  let { HOMOTOPIC_WITH_SUBSET_RIGHT, .. } := D.qpaths
  let { CEXP_0, CEXP_NEG, CEXP_NZ, CONTINUOUS_ON_CEXP, .. } := D.ra.tsa
  let { REAL_EXP_0, .. } := D.ra.tsb
  let { EULER, .. } := D.ra.tsc
  let { COS_PI, PI_NZ, PI_POS, PI_POS_LE, REAL_ABS_PI, SIN_PI, .. } := D.ra.tse
  let { CEXP_EQ, NORM_CEXP, .. } := D.ra.tsf
  let { CONTINUOUS_ON_COMPLEX_INV, CONTINUOUS_ON_COMPLEX_MUL, .. } := D.ra.ts.knc
  let { CONTINUOUS_ON_CX_DROP, .. } := D.ra.ts.knd
  let { CONTINUOUS_DISCRETE_RANGE_CONSTANT, sphere, .. } := D.ra.ts.qtopology
  let { COMPLEX_ADD_RID, COMPLEX_MUL_ASSOC, COMPLEX_MUL_LID, COMPLEX_MUL_RID,
        COMPLEX_MUL_RZERO, COMPLEX_SUB_RDISTRIB, .. } := D.ra.ts.cn.cxb
  let { COMPLEX_ENTIRE, COMPLEX_NORM_CX, COMPLEX_NORM_II, COMPLEX_VEC_0, CX_INJ, CX_SUB,
        II_NZ, IM_CX, IM_II, IM_MUL_CX, IM_MUL_II, RE_II, RE_MUL_CX, RE_MUL_II,
        .. } := D.ra.ts.cn.cxc
  let { COMPLEX_RING, .. } := D.ra.ts.cn.cxd
  let { COMPLEX_EQ_MUL_RCANCEL, COMPLEX_INV_1, .. } := D.ra.ts.cn.cxe
  let { COMPLEX_NORM_INV, COMPLEX_NORM_MUL, .. } := D.ra.ts.cn.cxf
  let { REAL_ABS_INTEGER_LEMMA, .. } := D.ra.ts.cn.ms.qfloor
  let { REAL_EQ_MUL_RCANCEL, .. } := D.ra.ts.cn.ms.qsession
  let { add_linear_invariants, add_translation_invariants, ASM_MESON_TAC, DESTRUCT_TAC,
        MESON, new_definition, REAL_ARITH, REAL_ARITH_TAC, SET_RULE, SET_TAC,
        .. } := D.ra.ts.cn.cx.cvx
  let { INTEGER_CLOSED, .. } := D.ra.ts.cn.ms.ig.qfloor
  let { ARITH_EQ, CONJ_ASSOC, EQ_IMP, .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, IMP_CONJ, IMP_CONJ_ALT, .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_UNION, LEFT_IMP_EXISTS_THM, MONO_EXISTS, NOT_EXISTS_THM,
        REAL_ABS_MUL, REAL_ABS_NUM, .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_INV_1, REAL_LE_MUL, .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_RID, REAL_MUL_RZERO, REAL_NEG_0, REAL_OF_NUM_EQ, REAL_POS, REAL_SUB_0,
        REAL_SUB_LDISTRIB, REAL_SUB_LE, REAL_SUB_RDISTRIB, SUBSET, SUBSET_RESTRICT,
        SUBSET_UNION, .. } := D.ra.ts.cn.cx.cvx.core5
  let { o_DEF, .. } := D.ra.ts.cn.cx.cvx.core6
  let { DIST_0, DIST_REFL, .. } := D.ra.ts.cn.cx.cvx.vec1
  let { DROP_VEC, .. } := D.ra.ts.cn.cx.cvx.vec2
  let { CLOSED_IN_TRANS, .. } := D.ra.ts.cn.cx.cvx.met
  let { COMPACT_CONTINUOUS_IMAGE, COMPACT_IMP_CLOSED, CONNECTED_CLOSED_IN_EQ,
        CONNECTED_CONTINUOUS_IMAGE, .. } := D.ra.ts.cn.cx.cvx.top2
  let { CONTINUOUS_ON_ADD, CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_CONST, CONTINUOUS_ON_SUB,
        CONTINUOUS_ON_SUBSET, HOMEOMORPHIC_REFL, .. } := D.ra.ts.cn.cx.cvx.top3
  let { HOMEOMORPHIC_SYM, HOMEOMORPHISM_OF_SUBSETS, IN_SPHERE,
        .. } := D.ra.ts.cn.cx.cvx.top4
  let { homeomorphic, homeomorphism, .. } := D.ra.ts.cn.cx.cvx.top5
  let { CLOSED_IN_INTER, .. } := D.ra.ts.cn.ms.ig.dv.dg.qmetric
  let { CLOSED_IN_CLOSED_EQ, CONTINUOUS_ON_CASES_LOCAL,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF, HOMEOMORPHIC_TRANSLATION_SELF,
        URYSOHN_LOCAL, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology2
  let { REAL_EQ_MUL_LCANCEL, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qses
  let { CONTINUOUS_CLOSED_PREIMAGE, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qtop
  let { CONVEX_UNIV, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx3
  -- @@SCOPE END

  let unicoherent ← new_definition
   r"unicoherent(u:real^N->bool) <=>
  !s t. connected s /\ connected t /\ s UNION t = u /\
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t
        ==> connected (s INTER t)"

  let HOMEOMORPHIC_UNICOHERENT ← prove
   r"!s:real^M->bool t:real^N->bool.
        s homeomorphic t /\ unicoherent s ==> unicoherent t"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [homeomorphic]) THEN
    REWRITE_TAC [homeomorphism, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"f:real^M->real^N", ← q r"g:real^N->real^M"] THEN
    STRIP_TAC THEN REWRITE_TAC [unicoherent] THEN
    MAP_EVERY X_GEN_TAC [← q r"u:real^N->bool", ← q r"v:real^N->bool"] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"u INTER v = IMAGE (f:real^M->real^N)
                  (IMAGE (g:real^N->real^M) u INTER IMAGE g v)")
    SUBST1_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC [],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o GEN_REWRITE_RULE id [unicoherent]) THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"p /\ q /\ r /\ s <=> r /\ (p /\ q) /\ s")] THEN
    CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
       (← REWRITE_RULE [IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC [],
      CONJ_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_CLOSED_MAP THEN
      MAP_EVERY EXISTS_TAC [← q r"f:real^M->real^N", ← q r"t:real^N->bool"] THEN
      ASM_REWRITE_TAC [homeomorphism]])

  let HOMEOMORPHIC_UNICOHERENT_EQ ← prove
   r"!s:real^M->bool t:real^N->bool.
     s homeomorphic t ==> (unicoherent s <=> unicoherent t)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] HOMEOMORPHIC_UNICOHERENT) THEN
    ASM_MESON_TAC [HOMEOMORPHIC_SYM])

  let UNICOHERENT_TRANSLATION ← prove
   r"!a:real^N s. unicoherent (IMAGE (\x. a + x) s) <=> unicoherent s"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_UNICOHERENT_EQ THEN
    REWRITE_TAC [HOMEOMORPHIC_TRANSLATION_SELF])

  add_translation_invariants [UNICOHERENT_TRANSLATION]

  let UNICOHERENT_INJECTIVE_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (unicoherent(IMAGE f s) <=> unicoherent s)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_UNICOHERENT_EQ THEN
    ASM_MESON_TAC [HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF,
                   HOMEOMORPHIC_REFL])

  add_linear_invariants [UNICOHERENT_INJECTIVE_LINEAR_IMAGE]

  let HOMEOMORPHISM_UNICOHERENCE ← prove
   r"!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (unicoherent(IMAGE f k) <=> unicoherent k)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_UNICOHERENT_EQ THEN
    ONCE_REWRITE_TAC [HOMEOMORPHIC_SYM] THEN REWRITE_TAC [homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [← q r"f:real^M->real^N", ← q r"g:real^N->real^M"] THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ]
            HOMEOMORPHISM_OF_SUBSETS)) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [homeomorphism]) THEN ASM SET_TAC [])

  let BORSUKIAN_IMP_UNICOHERENT ← prove
   r"!u:real^N->bool. borsukian u ==> unicoherent u"
   (GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [unicoherent] THEN
    SUBGOAL_THEN
     (← q r"!f. f continuous_on u /\ IMAGE f u SUBSET sphere(vec 0,&1)
               ==> ?a. homotopic_with (\h. T)
                        (subtopology euclidean u,
                         subtopology euclidean ((:complex) DIFF {Cx (&0)}))
                        (f:real^N->complex) (\t. a)")
    MP_TAC THENL
     [FIRST_X_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE id
       [BORSUKIAN_CIRCLE]) THEN
      X_GEN_TAC (← q r"f:real^N->complex") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"f:real^N->complex")) THEN
      ASM_REWRITE_TAC [← GSYM COMPLEX_VEC_0] THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] HOMOTOPIC_WITH_SUBSET_RIGHT) THEN
      REWRITE_TAC [← SET_RULE (← q r"s SUBSET UNIV DIFF {a} <=> ~(a IN s)")] THEN
      REWRITE_TAC [IN_SPHERE, DIST_REFL] THEN REAL_ARITH_TAC,
      POP_ASSUM (K ALL_TAC)] THEN
    REWRITE_TAC [sphere, DIST_0, INESSENTIAL_EQ_CONTINUOUS_LOGARITHM] THEN
    REPEAT STRIP_TAC THEN SIMP_TAC [CONNECTED_CLOSED_IN_EQ, NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"v:real^N->bool", ← q r"w:real^N->bool"] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"closed_in (subtopology euclidean u) (v:real^N->bool) /\
      closed_in (subtopology euclidean u) (w:real^N->bool)")
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [CLOSED_IN_INTER, CLOSED_IN_TRANS], ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"v:real^N->bool", ← q r"w:real^N->bool", ← q r"u:real^N->bool",
      ← q r"vec 0:real^1", ← q r"vec 1:real^1"] URYSOHN_LOCAL) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"q:real^N->real^1") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     (← q r"?g:real^N->real^2.
          g continuous_on u /\ IMAGE g u SUBSET {x | norm x = &1} /\
          (!x. x IN s ==> g(x) = cexp(Cx pi * ii * Cx(drop(q x)))) /\
          (!x. x IN t ==> g(x) = inv(cexp(Cx pi * ii * Cx(drop(q x)))))")
    (DESTRUCT_TAC "@g. cont circle s t") THENL
     [EXISTS_TAC
       (← q r"\x. if (x:real^N) IN s then cexp(Cx pi * ii * Cx(drop(q x)))
            else inv(cexp(Cx pi * ii * Cx(drop(q x))))") THEN
      SUBGOAL_THEN
       (← q r"!x:real^N.
          x IN s INTER t
          ==> cexp(Cx pi * ii * Cx(drop(q x))) =
              inv(cexp(Cx pi * ii * Cx(drop (q x))))")
      ASSUME_TAC THENL
       [SUBST1_TAC (← SYM (← ASSUME (← q r"v UNION w:real^N->bool = s INTER t"))) THEN
        REWRITE_TAC [IN_UNION] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [] THEN
        REWRITE_TAC [DROP_VEC, COMPLEX_MUL_RZERO, CEXP_0, COMPLEX_INV_1] THEN
        REWRITE_TAC [COMPLEX_MUL_RID, EULER] THEN
        REWRITE_TAC [RE_MUL_CX, IM_MUL_CX, RE_MUL_II, IM_MUL_II] THEN
        REWRITE_TAC [RE_II, IM_II, REAL_MUL_RZERO, REAL_MUL_RID] THEN
        REWRITE_TAC [REAL_EXP_0, COMPLEX_MUL_LID, COS_PI, SIN_PI] THEN
        REWRITE_TAC [COMPLEX_MUL_RZERO, COMPLEX_ADD_RID] THEN
        CONV_TAC COMPLEX_RING,
        ALL_TAC] THEN
      SIMP_TAC [] THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "u" THEN MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
        ASM_REWRITE_TAC [← SET_RULE
         (← q r"P /\ ~P \/ x IN t /\ x IN s <=> x IN s INTER t")] THEN
        CONJ_TAC THENL
         [ALL_TAC,
          MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_INV THEN REWRITE_TAC [CEXP_NZ]] THEN
        GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        REWRITE_TAC [CONTINUOUS_ON_CEXP] THEN
        REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
        REWRITE_TAC [CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN
        ASM_MESON_TAC [CONTINUOUS_ON_SUBSET, SUBSET_UNION],
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
        REWRITE_TAC [COMPLEX_NORM_INV, NORM_CEXP] THEN
        REWRITE_TAC [RE_MUL_CX, RE_MUL_II, IM_CX] THEN
        REWRITE_TAC [REAL_MUL_RZERO, REAL_NEG_0, REAL_EXP_0, REAL_INV_1],
        GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC [] THEN ASM SET_TAC []],
       FIRST_X_ASSUM (MP_TAC o SPEC (← q r"g:real^N->complex")) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN (X_CHOOSE_THEN (← q r"h:real^N->complex") STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN
     (← q r"(?n. integer n /\
           !x:real^N. x IN s
                      ==> h(x) - Cx pi * ii * Cx (drop (q x)) =
                          Cx(&2 * n * pi) * ii) /\
      (?n. integer n /\
           !x:real^N. x IN t
                      ==> h(x) + Cx pi * ii * Cx (drop (q x)) =
                          Cx(&2 * n * pi) * ii)")
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN (← q r"m:real") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))
      (X_CHOOSE_THEN (← q r"n:real") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))
    THENL
     [CONJ_TAC THEN MATCH_MP_TAC (← MESON []
       (← q r"(?x. x IN s) /\
        (!x. x IN s ==> ?n. P n /\ f x = k n) /\
        (?a. !x. x IN s ==> f x = a)
        ==> (?n. P n /\ !x. x IN s ==> f x = k n)")) THEN
      (CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN
      MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN
     (CONJ_TAC THENL
       [REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"a + b:complex = c <=> a = --b + c")),
                     ← ExceptT.mk (COMPLEX_RING (← q r"a - b:complex = c <=> a = b + c"))] THEN
        REWRITE_TAC [← GSYM CEXP_EQ, CEXP_NEG] THEN ASM SET_TAC [],
        ALL_TAC] THEN
      DISCH_THEN (LABEL_TAC "*") THEN
      MATCH_MP_TAC CONTINUOUS_DISCRETE_RANGE_CONSTANT THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [(MATCH_MP_TAC CONTINUOUS_ON_ADD ORELSE
         MATCH_MP_TAC CONTINUOUS_ON_SUB) THEN
        CONJ_TAC THENL
         [ASM_MESON_TAC [CONTINUOUS_ON_SUBSET, SUBSET_UNION], ALL_TAC] THEN
        REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
        REWRITE_TAC [CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN
        ASM_MESON_TAC [CONTINUOUS_ON_SUBSET, SUBSET_UNION],
        X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN EXISTS_TAC (← q r"&2 * pi") THEN
        REWRITE_TAC [← REAL_ARITH (← q r"&0 < &2 * x <=> &0 < x"), PI_POS] THEN
        X_GEN_TAC (← q r"y:real^N") THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        REMOVE_THEN "*" (fun th => tactic_of do
         pure (MP_TAC (← SPEC (← q r"y:real^N") th) THEN
               MP_TAC (← SPEC (← q r"x:real^N") th))) THEN
        ASM_REWRITE_TAC [] THEN STRIP_TAC THEN STRIP_TAC THEN
        ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [COMPLEX_EQ_MUL_RCANCEL, II_NZ, ← GSYM COMPLEX_SUB_RDISTRIB,
              COMPLEX_NORM_MUL, CX_INJ, COMPLEX_NORM_II, REAL_MUL_RID] THEN
        REWRITE_TAC [← GSYM CX_SUB, COMPLEX_NORM_CX] THEN
        REWRITE_TAC [REAL_EQ_MUL_LCANCEL, ← GSYM REAL_SUB_LDISTRIB] THEN
        REWRITE_TAC [← GSYM REAL_SUB_RDISTRIB, REAL_ABS_MUL] THEN
        REWRITE_TAC [REAL_EQ_MUL_RCANCEL, PI_NZ, REAL_ABS_PI] THEN
        REWRITE_TAC [REAL_ABS_NUM, REAL_OF_NUM_EQ, ARITH_EQ] THEN
        DISCH_TAC THEN REWRITE_TAC [← REAL_ARITH
         (← q r"&2 * p <= &2 * a * p <=> &0 <= &2 * p * (a - &1)")] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [PI_POS_LE, REAL_SUB_LE] THEN
        MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN
        ASM_SIMP_TAC [INTEGER_CLOSED, REAL_SUB_0]]),
        ALL_TAC] THEN
    GEN_REWRITE_TAC id [← TAUT (← q r"p ==> q ==> F <=> ~(p /\ q)")] THEN
    DISCH_THEN (MP_TAC o MATCH_MP (← SET_RULE
     (← q r"(!x. x IN s ==> P x) /\ (!x. x IN t ==> Q x)
      ==> ~(v = {}) /\ ~(w = {}) /\ v UNION w SUBSET s INTER t
           ==> ~(!y z. y IN v /\ z IN w ==> ~(P y /\ Q y /\ P z /\ Q z))"))) THEN
    ANTS_TAC THENL [ASM SET_TAC [], ASM_SIMP_TAC []] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP (← ExceptT.mk (COMPLEX_RING
     (← q r"y + p = n /\ y - p = m /\ z + q = n /\ z - q = m ==> q:complex = p")))) THEN
    REWRITE_TAC [DROP_VEC, COMPLEX_MUL_RZERO, COMPLEX_ENTIRE, CX_INJ] THEN
    REWRITE_TAC [PI_NZ, II_NZ, REAL_OF_NUM_EQ, ARITH_EQ])

  let CONTRACTIBLE_IMP_UNICOHERENT ← prove
   r"!u:real^N->bool. contractible u ==> unicoherent u"
   (SIMP_TAC [BORSUKIAN_IMP_UNICOHERENT, CONTRACTIBLE_IMP_BORSUKIAN])

  let CONVEX_IMP_UNICOHERENT ← prove
   r"!u:real^N->bool. convex u ==> unicoherent u"
   (SIMP_TAC [BORSUKIAN_IMP_UNICOHERENT, CONVEX_IMP_BORSUKIAN])

  let UNICOHERENT_UNIV ← prove
   r"unicoherent(:real^N)"
   (SIMP_TAC [CONVEX_IMP_UNICOHERENT, CONVEX_UNIV])

  let UNICOHERENT_MONOTONE_IMAGE_COMPACT ← prove
   r"!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\ compact s /\
        (!y. y IN t ==> connected {x | x IN s /\ f x = y}) /\
        unicoherent s
        ==> unicoherent t"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"compact(t:real^N->bool)") ASSUME_TAC THENL
     [ASM_MESON_TAC [COMPACT_CONTINUOUS_IMAGE], REWRITE_TAC [unicoherent]] THEN
    MAP_EVERY X_GEN_TAC [← q r"u:real^N->bool", ← q r"v:real^N->bool"] THEN
    ASM_SIMP_TAC [CLOSED_IN_CLOSED_EQ, COMPACT_IMP_CLOSED] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [unicoherent]) THEN
    DISCH_THEN (MP_TAC o SPECL
     [← q r"{x | x IN s /\ (f:real^M->real^N) x IN u}",
      ← q r"{x | x IN s /\ (f:real^M->real^N) x IN v}"]) THEN
    ASM_SIMP_TAC [CLOSED_IN_CLOSED_EQ, COMPACT_IMP_CLOSED, SUBSET_RESTRICT,
                  CONTINUOUS_CLOSED_PREIMAGE, CONJ_ASSOC] THEN
    REWRITE_TAC [IMP_CONJ_ALT] THEN ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"f:real^M->real^N", ← q r"s:real^M->bool", ← q r"t:real^N->bool"]
      CONNECTED_CLOSED_MONOTONE_PREIMAGE) THEN
    ASM_REWRITE_TAC [] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [CONTINUOUS_IMP_CLOSED_MAP_EXPLICIT], ALL_TAC] THEN
    DISCH_TAC THEN ASM_SIMP_TAC [] THEN
    DISCH_THEN (MP_TAC o ISPEC (← q r"f:real^M->real^N") o MATCH_MP
     (← REWRITE_RULE [IMP_CONJ_ALT] CONNECTED_CONTINUOUS_IMAGE)) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN SET_TAC [],
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC []])

  pure { unicoherent, HOMEOMORPHIC_UNICOHERENT, HOMEOMORPHIC_UNICOHERENT_EQ,
         UNICOHERENT_TRANSLATION, UNICOHERENT_INJECTIVE_LINEAR_IMAGE,
         HOMEOMORPHISM_UNICOHERENCE, BORSUKIAN_IMP_UNICOHERENT,
         CONTRACTIBLE_IMP_UNICOHERENT, CONVEX_IMP_UNICOHERENT, UNICOHERENT_UNIV,
         UNICOHERENT_MONOTONE_IMAGE_COMPACT }
/- ------------------------------------------------------------------------- -/
/- Several common variants of unicoherence for R^n: frontiers and           -/
/- separation by components and unions.                                      -/
/- (moretop.ml 6269-6529)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MOU where
  CONNECTED_FRONTIER_SIMPLE : thm
  CONNECTED_FRONTIER_COMPONENT_COMPLEMENT : thm
  CONNECTED_FRONTIER_DISJOINT : thm
  SEPARATION_BY_COMPONENT_CLOSED_POINTWISE : thm
  SEPARATION_BY_COMPONENT_CLOSED : thm
  SEPARATION_BY_UNION_CLOSED_POINTWISE : thm
  SEPARATION_BY_UNION_CLOSED : thm
  OPEN_UNICOHERENT_UNIV : thm
  SEPARATION_BY_COMPONENT_OPEN : thm
  SEPARATION_BY_UNION_OPEN : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOU [HolBase] (D : MoreTopDeps) (BMOT : MOT) : ExceptT String IO MOU := do
  -- @@SCOPE BEGIN
  let { unicoherent, UNICOHERENT_UNIV, .. } := BMOT
  let { CONNECTED_CLOSED_SET, CONNECTED_COMPONENT_DISJOINT, CONNECTED_COMPONENT_IN,
        CONNECTED_COMPONENT_SYM_EQ, FRONTIER_UNION_SUBSET, FRONTIER_UNIV,
        .. } := D.qtopology
  let { CLOSED_IRREDUCIBLE_SEPARATOR, FRONTIER_MINIMAL_SEPARATING_CLOSED_POINTWISE,
        FRONTIER_UNIONS_SUBSET_CLOSURE, .. } := D.qpaths
  let { COMPONENT_COMPLEMENT_CONNECTED, .. } := D.qconvex
  let { CONNECTED_CLOSURE, CONNECTED_CONNECTED_COMPONENT,
        CONNECTED_IFF_CONNECTED_COMPONENT, .. } := D.ra.ts.cn.ms.qtopology1
  let { ASM_MESON_TAC, MESON, MESON_TAC, SET_RULE, SET_TAC, .. } := D.ra.ts.cn.cx.cvx
  let { DE_MORGAN_THM, ETA_AX, FORALL_IN_GSPEC, .. } := D.ra.ts.cn.cx.cvx.core1
  let { IMP_CONJ, IMP_CONJ_ALT, IN, IN_DIFF, .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_UNION, IN_UNIV, LEFT_IMP_EXISTS_THM, MONO_EXISTS, MONO_FORALL,
        NOT_EXISTS_THM, .. } := D.ra.ts.cn.cx.cvx.core3
  let { SUBSET, SUBSET_ANTISYM, SUBSET_REFL, SUBSET_TRANS, .. } := D.ra.ts.cn.cx.cvx.core5
  let { SUBSET_UNIV, UNION_SUBSET, UNIONS_SUBSET, UNIONS_UNION,
        .. } := D.ra.ts.cn.cx.cvx.core6
  let { SUBTOPOLOGY_UNIV, .. } := D.ra.ts.cn.cx.cvx.met
  let { CLOSED_CLOSURE, CLOSED_IN, .. } := D.ra.ts.cn.cx.cvx.top1
  let { CLOSURE_MINIMAL, CLOSURE_SUBSET, CONNECTED_CLOSED, .. } := D.ra.ts.cn.cx.cvx.top2
  let { FRONTIER_COMPLEMENT, FRONTIER_EQ_EMPTY, FRONTIER_SUBSET_EQ,
        .. } := D.ra.ts.cn.cx.cvx.top3
  let { IN_COMPONENTS_CONNECTED, IN_COMPONENTS_NONEMPTY, IN_COMPONENTS_SUBSET,
        .. } := D.ra.ts.cn.cx.cvx.top4
  let { frontier, SUBSET_CLOSURE, SUBSET_INTERIOR, UNIONS_COMPONENTS,
        .. } := D.ra.ts.cn.cx.cvx.top5
  let { COMPONENTS_NONOVERLAP, EXISTS_COMPONENT_SUPERSET,
        .. } := D.ra.ts.cn.ms.ig.dv.qtopology1
  let { FRONTIER_OF_COMPONENTS_SUBSET, .. } := D.ra.ts.cn.ms.ig.dv.dg.qconvex
  let { COMPL_COMPL, SUBSET_UNIONS, .. } := D.ra.ts.cn.ms.ig.dv.dg.qsession
  let { CLOSED_UNION, CONNECTED_COMPONENT_MONO, CONNECTED_COMPONENT_REFL_EQ,
        CONNECTED_EMPTY, CONNECTED_UNIV, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { FRONTIER_CLOSURES, IN_COMPONENTS, OPEN_CLOSED,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology2
  -- @@SCOPE END

  let CONNECTED_FRONTIER_SIMPLE ← prove
   r"!s. connected(s) /\ connected((:real^N) DIFF s) ==> connected(frontier s)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [FRONTIER_CLOSURES] THEN
    MATCH_MP_TAC (← REWRITE_RULE [unicoherent] UNICOHERENT_UNIV) THEN
    REWRITE_TAC [SUBTOPOLOGY_UNIV, ← GSYM CLOSED_IN] THEN
    ASM_SIMP_TAC [CLOSED_CLOSURE, CONNECTED_CLOSURE] THEN
    MATCH_MP_TAC (← SET_RULE
     (← q r"s SUBSET closure s /\ t SUBSET closure t /\ s UNION t = UNIV
      ==> closure s UNION closure t = UNIV")) THEN
    REWRITE_TAC [CLOSURE_SUBSET] THEN SET_TAC [])

  let CONNECTED_FRONTIER_COMPONENT_COMPLEMENT ← prove
   r"!s c:real^N->bool.
        connected s /\ c IN components((:real^N) DIFF s)
        ==> connected(frontier c)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_FRONTIER_SIMPLE THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC [IN_COMPONENTS_CONNECTED],
      MATCH_MP_TAC COMPONENT_COMPLEMENT_CONNECTED THEN
      EXISTS_TAC (← q r"s:real^N->bool") THEN
      ASM_REWRITE_TAC [SUBSET_UNIV, CONNECTED_UNIV]])

  let CONNECTED_FRONTIER_DISJOINT ← prove
   r"!s t:real^N->bool.
     connected s /\ connected t /\ DISJOINT s t /\ frontier s SUBSET frontier t
     ==> connected(frontier s)"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"s = (:real^N)") THEN
    ASM_REWRITE_TAC [FRONTIER_UNIV, CONNECTED_EMPTY] THEN
    SUBGOAL_THEN (← q r"?c. c IN components((:real^N) DIFF s) /\ t SUBSET c")
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC EXISTS_COMPONENT_SUPERSET THEN ASM SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"frontier s:real^N->bool = frontier c") SUBST1_TAC THENL
     [ALL_TAC, ASM_MESON_TAC [CONNECTED_FRONTIER_COMPONENT_COMPLEMENT]] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      REWRITE_TAC [frontier, IN_DIFF] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE [SUBSET] o
         MATCH_MP SUBSET_CLOSURE) THEN
        ASM_MESON_TAC [SUBSET, frontier, IN_DIFF],
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV
          [← GSYM FRONTIER_COMPLEMENT]) THEN
        REWRITE_TAC [frontier] THEN
        MATCH_MP_TAC (← SET_RULE (← q r"u SUBSET t ==> x IN s DIFF t ==> ~(x IN u)")) THEN
        MATCH_MP_TAC SUBSET_INTERIOR THEN
        ASM_MESON_TAC [IN_COMPONENTS_SUBSET]],
      GEN_REWRITE_TAC RAND_CONV [← GSYM FRONTIER_COMPLEMENT] THEN
      ASM_MESON_TAC [FRONTIER_OF_COMPONENTS_SUBSET]])

  let SEPARATION_BY_COMPONENT_CLOSED_POINTWISE ← prove
   r"!s a b. closed s /\ ~connected_component ((:real^N) DIFF s) a b
           ==> ?c. c IN components s /\
                   ~connected_component((:real^N) DIFF c) a b"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"(a:real^N) IN s") THENL
     [EXISTS_TAC (← q r"connected_component s (a:real^N)") THEN
      ASM_REWRITE_TAC [IN_COMPONENTS] THEN
      CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o MATCH_MP CONNECTED_COMPONENT_IN) THEN
      REWRITE_TAC [IN_UNIV, IN_DIFF] THEN REWRITE_TAC [IN] THEN
      ASM_REWRITE_TAC [CONNECTED_COMPONENT_REFL_EQ],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"(b:real^N) IN s") THENL
     [EXISTS_TAC (← q r"connected_component s (b:real^N)") THEN
      ASM_REWRITE_TAC [IN_COMPONENTS] THEN
      CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o MATCH_MP CONNECTED_COMPONENT_IN) THEN
      REWRITE_TAC [IN_UNIV, IN_DIFF] THEN REWRITE_TAC [IN] THEN
      ASM_REWRITE_TAC [CONNECTED_COMPONENT_REFL_EQ],
      ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP CLOSED_IRREDUCIBLE_SEPARATOR) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:real^N->bool") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"?c:real^N->bool. c IN components s /\ t SUBSET c") MP_TAC THENL
     [MATCH_MP_TAC EXISTS_COMPONENT_SUPERSET THEN ASM_REWRITE_TAC [],
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
       (← q r"~(t b) ==> s SUBSET t ==> ~(s b)"))) THEN
      REWRITE_TAC [ETA_AX] THEN MATCH_MP_TAC CONNECTED_COMPONENT_MONO THEN
      ASM SET_TAC []] THEN
    CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"connected_component ((:real^N) DIFF t) a",
                     ← q r"connected_component ((:real^N) DIFF t) b"]
          CONNECTED_FRONTIER_DISJOINT) THEN
    REWRITE_TAC [CONNECTED_CONNECTED_COMPONENT, CONNECTED_COMPONENT_DISJOINT] THEN
    ASM_REWRITE_TAC [IN] THEN ONCE_REWRITE_TAC [CONNECTED_COMPONENT_SYM_EQ] THEN
    SUBGOAL_THEN
     (← q r"frontier(connected_component ((:real^N) DIFF t) a) = t /\
      frontier(connected_component ((:real^N) DIFF t) b) = t")
     (fun th => ASM_REWRITE_TAC [th, SUBSET_REFL]) THEN
    CONJ_TAC THEN MATCH_MP_TAC FRONTIER_MINIMAL_SEPARATING_CLOSED_POINTWISE THENL
     [EXISTS_TAC (← q r"b:real^N"), EXISTS_TAC (← q r"a:real^N")] THEN
    ASM_SIMP_TAC [] THEN ONCE_REWRITE_TAC [CONNECTED_COMPONENT_SYM_EQ] THEN
    ASM_SIMP_TAC [] THEN ASM SET_TAC [])

  let SEPARATION_BY_COMPONENT_CLOSED ← prove
   r"!s. closed s /\ ~connected((:real^N) DIFF s)
       ==> ?c. c IN components s /\ ~connected((:real^N) DIFF c)"
   (REWRITE_TAC [CONNECTED_IFF_CONNECTED_COMPONENT, IN_DIFF, IN_UNIV] THEN
    MP_TAC SEPARATION_BY_COMPONENT_CLOSED_POINTWISE THEN
    MATCH_MP_TAC MONO_FORALL THEN
    MESON_TAC [← REWRITE_RULE [SUBSET] IN_COMPONENTS_SUBSET])

  let SEPARATION_BY_UNION_CLOSED_POINTWISE ← prove
   r"!s t a b. closed s /\ closed t /\ DISJOINT s t /\
             connected_component ((:real^N) DIFF s) a b /\
             connected_component ((:real^N) DIFF t) a b
             ==> connected_component ((:real^N) DIFF (s UNION t)) a b"
   (REPEAT GEN_TAC THEN
    REPLICATE_TAC 3 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (CONJUNCTS_THEN (fun th => tactic_of do
      pure (ASSUME_TAC th THEN MP_TAC (← MATCH_MP CONNECTED_COMPONENT_IN th)))) THEN
    REWRITE_TAC [IN_DIFF, IN_UNIV] THEN REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC id [← TAUT (← q r"p <=> ~ ~ p")] THEN DISCH_THEN (MP_TAC o MATCH_MP
     (← REWRITE_RULE [IMP_CONJ_ALT] SEPARATION_BY_COMPONENT_CLOSED_POINTWISE)) THEN
    ASM_SIMP_TAC [CLOSED_UNION, NOT_EXISTS_THM] THEN
    X_GEN_TAC (← q r"c:real^N->bool") THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"(c:real^N->bool) SUBSET s \/ c SUBSET t") STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM (MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP IN_COMPONENTS_CONNECTED) THEN
      REWRITE_TAC [CONNECTED_CLOSED, NOT_EXISTS_THM] THEN
      DISCH_THEN (MP_TAC o SPECL [← q r"s:real^N->bool", ← q r"t:real^N->bool"]) THEN
      ASM_REWRITE_TAC [] THEN ASM SET_TAC [],
      UNDISCH_TAC (← q r"connected_component ((:real^N) DIFF s) a b"),
      UNDISCH_TAC (← q r"connected_component ((:real^N) DIFF t) a b")] THEN
    MATCH_MP_TAC (← SET_RULE (← q r"s SUBSET t ==> s b ==> t b")) THEN
    REWRITE_TAC [ETA_AX] THEN MATCH_MP_TAC CONNECTED_COMPONENT_MONO THEN
    ASM SET_TAC [])

  let SEPARATION_BY_UNION_CLOSED ← prove
   r"!s t:real^N->bool.
        closed s /\ closed t /\ DISJOINT s t /\
        connected((:real^N) DIFF s) /\
        connected((:real^N) DIFF t)
        ==> connected((:real^N) DIFF (s UNION t))"
   (SIMP_TAC [CONNECTED_IFF_CONNECTED_COMPONENT, IN_DIFF, IN_UNION, IN_UNIV] THEN
    MESON_TAC [SEPARATION_BY_UNION_CLOSED_POINTWISE])

  let OPEN_UNICOHERENT_UNIV ← prove
   r"!s t. open s /\ open t /\ connected s /\ connected t /\
         s UNION t = (:real^N)
         ==> connected(s INTER t)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← SET_RULE
     (← q r"s INTER t = UNIV DIFF ((UNIV DIFF s) UNION (UNIV DIFF t))")] THEN
    MATCH_MP_TAC SEPARATION_BY_UNION_CLOSED THEN
    ASM_SIMP_TAC [← GSYM OPEN_CLOSED, COMPL_COMPL] THEN
    ASM SET_TAC [])

  let SEPARATION_BY_COMPONENT_OPEN ← (do
    let lemma ← prove
     r"!s t u. closed s /\ closed t /\ s INTER t = {} /\
               connected u /\ ~(u INTER s = {}) /\ ~(u INTER t = {})
               ==> ?c. c IN components((:real^N) DIFF (s UNION t)) /\
                       ~(c INTER u = {}) /\
                       ~(frontier c INTER s = {}) /\
                       ~(frontier c INTER t = {})"
     (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← MESON []
       (← q r"(?x. P x /\ Q x /\ R x) <=> ~(!x. P x /\ Q x ==> ~R x)")] THEN
      DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [CONNECTED_CLOSED]) THEN
      REWRITE_TAC [] THEN MAP_EVERY EXISTS_TAC
       [← q r"s UNION
         UNIONS {c | c IN components((:real^N) DIFF (s UNION t)) /\
                     frontier c SUBSET s}",
        ← q r"t UNION
          UNIONS {c | c IN components((:real^N) DIFF (s UNION t)) /\
                      frontier c SUBSET t}"] THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL
       [REWRITE_TAC [← GSYM FRONTIER_SUBSET_EQ] THEN
        MATCH_MP_TAC (← SET_RULE (← q r"s SUBSET t ==> s SUBSET t UNION u")) THEN
        MATCH_MP_TAC (← MATCH_MP (← REWRITE_RULE [IMP_CONJ] SUBSET_TRANS)
            (← SPEC_ALL FRONTIER_UNION_SUBSET)) THEN
        ASM_REWRITE_TAC [UNION_SUBSET, FRONTIER_SUBSET_EQ] THEN
        MATCH_MP_TAC (← MATCH_MP (← REWRITE_RULE [IMP_CONJ] SUBSET_TRANS)
            (← SPEC_ALL FRONTIER_UNIONS_SUBSET_CLOSURE)) THEN
        MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC [UNIONS_SUBSET] THEN
        SIMP_TAC [FORALL_IN_GSPEC],
        ALL_TAC]) THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC (← q r"(s UNION t) UNION
                     UNIONS {c | c IN components((:real^N) DIFF (s UNION t)) /\
                     ~(c INTER u = {})}") THEN
        CONJ_TAC THENL
         [MP_TAC (← ISPEC (← q r"(:real^N) DIFF (s UNION t)") UNIONS_COMPONENTS) THEN
          SET_TAC [],
          MATCH_MP_TAC (← SET_RULE
           (← q r"c SUBSET d UNION e
            ==> (s UNION t) UNION c SUBSET (s UNION d) UNION (t UNION e)")) THEN
          REWRITE_TAC [← GSYM UNIONS_UNION] THEN MATCH_MP_TAC SUBSET_UNIONS THEN
          ONCE_REWRITE_TAC [SUBSET] THEN REWRITE_TAC [IN_ELIM_THM, IN_UNION] THEN
          X_GEN_TAC (← q r"c:real^N->bool") THEN STRIP_TAC THEN
          FIRST_X_ASSUM (MP_TAC o SPEC (← q r"c:real^N->bool")) THEN
          ASM_REWRITE_TAC [DE_MORGAN_THM] THEN
          MATCH_MP_TAC (← SET_RULE
           (← q r"c SUBSET s UNION t
            ==> c INTER s = {} \/ c INTER t = {}
                ==> c SUBSET s \/ c SUBSET t")) THEN
          FIRST_ASSUM (MP_TAC o MATCH_MP FRONTIER_OF_COMPONENTS_SUBSET) THEN
          REWRITE_TAC [FRONTIER_COMPLEMENT] THEN
          MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] SUBSET_TRANS) THEN
          ASM_SIMP_TAC [FRONTIER_SUBSET_EQ, CLOSED_UNION]],
        MATCH_MP_TAC (← SET_RULE
         (← q r"c UNION d SUBSET UNIV DIFF (s UNION t) /\ s INTER t = {} /\
          DISJOINT c d
          ==> (s UNION c) INTER (t UNION d) INTER u = {}")) THEN
        ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
         [REWRITE_TAC [← GSYM UNIONS_UNION] THEN
          GEN_REWRITE_TAC RAND_CONV [UNIONS_COMPONENTS] THEN
          MATCH_MP_TAC SUBSET_UNIONS THEN SET_TAC [],
          MATCH_MP_TAC (← SET_RULE
           (← q r"(!s. s IN c ==> !t. t IN c' ==> s INTER t = {})
            ==> DISJOINT (UNIONS c) (UNIONS c')")) THEN
          REWRITE_TAC [FORALL_IN_GSPEC] THEN
          MP_TAC (← ISPEC (← q r"(:real^N) DIFF (s UNION t)") COMPONENTS_NONOVERLAP) THEN
          SIMP_TAC [] THEN DISCH_THEN (K ALL_TAC) THEN
          X_GEN_TAC (← q r"c:real^N->bool") THEN STRIP_TAC THEN
          X_GEN_TAC (← q r"c':real^N->bool") THEN
          ASM_CASES_TAC (← q r"c':real^N->bool = c") THEN ASM_REWRITE_TAC [] THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
           (← q r"c SUBSET s ==> s INTER t = {} /\ ~(c = {}) ==> ~(c SUBSET t)"))) THEN
          ASM_REWRITE_TAC [FRONTIER_EQ_EMPTY] THEN
          FIRST_ASSUM (ASSUME_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
          FIRST_ASSUM (ASSUME_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
          ASM SET_TAC []],
        ASM SET_TAC [],
        ASM SET_TAC []])
    prove
     r"!s. open s /\ ~connected((:real^N) DIFF s)
         ==> ?c. c IN components s /\ ~connected((:real^N) DIFF c)"
     (GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_SIMP_TAC [CONNECTED_CLOSED_SET, ← GSYM OPEN_CLOSED,
                    LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"t:real^N->bool", ← q r"u:real^N->bool"] THEN STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"t:real^N->bool", ← q r"u:real^N->bool", ← q r"(:real^N)"]
              lemma) THEN
      ASM_REWRITE_TAC [CONNECTED_UNIV, COMPL_COMPL] THEN
      ANTS_TAC THENL [ASM SET_TAC [], MATCH_MP_TAC MONO_EXISTS] THEN
      X_GEN_TAC (← q r"c:real^N->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      DISCH_TAC THEN MP_TAC (← ISPEC (← q r"c:real^N->bool") CONNECTED_FRONTIER_SIMPLE) THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP IN_COMPONENTS_CONNECTED) THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [CONNECTED_CLOSED] THEN
      MAP_EVERY EXISTS_TAC [← q r"t:real^N->bool", ← q r"u:real^N->bool"] THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP FRONTIER_OF_COMPONENTS_SUBSET) THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] SUBSET_TRANS) THEN
      ONCE_REWRITE_TAC [← GSYM FRONTIER_COMPLEMENT] THEN
      ASM_REWRITE_TAC [FRONTIER_SUBSET_EQ, ← GSYM OPEN_CLOSED]))

  let SEPARATION_BY_UNION_OPEN ← prove
   r"!s t:real^N->bool.
        open s /\ open t /\ DISJOINT s t /\
        connected((:real^N) DIFF s) /\
        connected((:real^N) DIFF t)
        ==> connected((:real^N) DIFF (s UNION t))"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← SET_RULE
     (← q r"UNIV DIFF (s UNION t) = (UNIV DIFF s) INTER (UNIV DIFF t)")] THEN
    MATCH_MP_TAC (← REWRITE_RULE [unicoherent] UNICOHERENT_UNIV) THEN
    REWRITE_TAC [SUBTOPOLOGY_UNIV, ← GSYM CLOSED_IN] THEN
    ASM_REWRITE_TAC [← GSYM OPEN_CLOSED] THEN ASM SET_TAC [])

  pure { CONNECTED_FRONTIER_SIMPLE, CONNECTED_FRONTIER_COMPONENT_COMPLEMENT,
         CONNECTED_FRONTIER_DISJOINT, SEPARATION_BY_COMPONENT_CLOSED_POINTWISE,
         SEPARATION_BY_COMPONENT_CLOSED, SEPARATION_BY_UNION_CLOSED_POINTWISE,
         SEPARATION_BY_UNION_CLOSED, OPEN_UNICOHERENT_UNIV,
         SEPARATION_BY_COMPONENT_OPEN, SEPARATION_BY_UNION_OPEN }
/- ------------------------------------------------------------------------- -/
/- Several common variants of unicoherence for R^n: open sets with disjoint  -/
/- frontiers; nonseparation by components; common frontier domains.          -/
/- (moretop.ml 6530-6735)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MOV where
  CONNECTED_INTER_DISJOINT_OPEN_FRONTIERS : thm
  NONSEPARATION_BY_COMPONENT_EQ : thm
  CONNECTED_COMMON_FRONTIER_DOMAINS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOV [HolBase] (D : MoreTopDeps) (BMOU : MOU) : ExceptT String IO MOV := do
  -- @@SCOPE BEGIN
  let { CONNECTED_FRONTIER_COMPONENT_COMPLEMENT, CONNECTED_FRONTIER_DISJOINT,
        OPEN_UNICOHERENT_UNIV, SEPARATION_BY_COMPONENT_CLOSED,
        SEPARATION_BY_COMPONENT_OPEN, .. } := BMOU
  let { COMMON_FRONTIER_DOMAINS, CONNECTED_UNION, CONNECTED_UNIONS, .. } := D.qtopology
  let { COMPONENT_COMPLEMENT_CONNECTED, .. } := D.qconvex
  let { SUBSET_INTERS, .. } := D.ra.ts.cn.ms.qsession
  let { CONNECTED_CLOSURE, .. } := D.ra.ts.cn.ms.qtopology1
  let { OPEN_UNIONS, .. } := D.ra.ts.cn.ms.qtopology2
  let { ASM_MESON_TAC, MESON, MESON_TAC, SET_RULE, SET_TAC, .. } := D.ra.ts.cn.cx.cvx
  let { DE_MORGAN_THM, EMPTY_UNIONS, EQ_IMP, EXTENSION, FORALL_IN_GSPEC,
        .. } := D.ra.ts.cn.cx.cvx.core1
  let { IN_DIFF, INTER_COMM, INTER_EMPTY, INTER_UNIONS, INTER_UNIV,
        .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_UNION, IN_UNIONS, IN_UNIV, .. } := D.ra.ts.cn.cx.cvx.core3
  let { SUBSET_ANTISYM, SUBSET_REFL, SUBSET_TRANS, SUBSET_UNION,
        .. } := D.ra.ts.cn.cx.cvx.core5
  let { SUBSET_UNIV, UNION_COMM, UNION_EMPTY, UNIONS_0, UNIONS_GSPEC, UNIONS_SUBSET,
        .. } := D.ra.ts.cn.cx.cvx.core6
  let { CLOSED_CLOSURE, .. } := D.ra.ts.cn.cx.cvx.top1
  let { CLOSURE_EQ_EMPTY, CLOSURE_SUBSET, COMPONENTS_MAXIMAL, CONNECTED_INTER_FRONTIER,
        .. } := D.ra.ts.cn.cx.cvx.top2
  let { FRONTIER_CLOSURE_SUBSET, FRONTIER_COMPLEMENT, FRONTIER_EQ_EMPTY,
        .. } := D.ra.ts.cn.cx.cvx.top3
  let { IN_COMPONENTS_CONNECTED, IN_COMPONENTS_NONEMPTY, IN_COMPONENTS_SUBSET,
        INTERIOR_OPEN, .. } := D.ra.ts.cn.cx.cvx.top4
  let { closed, frontier, OPEN_INTER_CLOSURE_EQ_EMPTY, UNIONS_COMPONENTS,
        .. } := D.ra.ts.cn.cx.cvx.top5
  let { OPEN_UNION, .. } := D.ra.ts.cn.ms.ig.dv.qtopology2
  let { FRONTIER_OF_COMPONENTS_SUBSET, .. } := D.ra.ts.cn.ms.ig.dv.dg.qconvex
  let { OPEN_COMPONENTS, .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths2
  let { COMPL_COMPL, .. } := D.ra.ts.cn.ms.ig.dv.dg.qsession
  let { CONNECTED_EMPTY, CONNECTED_UNIV, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  -- @@SCOPE END

  let CONNECTED_INTER_DISJOINT_OPEN_FRONTIERS ← (do
    let lemma ← prove
     r"~(f = {}) ==> s UNION UNIONS f = UNIONS {s UNION c | c IN f}"
     (REWRITE_TAC [UNIONS_GSPEC] THEN SET_TAC [])
    prove
     r"!s t:real^N->bool.
          open s /\ connected s /\ open t /\ connected t /\
          DISJOINT (frontier s) (frontier t)
          ==> connected(s INTER t)"
     (REPEAT STRIP_TAC THEN
      MAP_EVERY ASM_CASES_TAC [← q r"s:real^N->bool = {}", ← q r"t:real^N->bool = {}"] THEN
      ASM_REWRITE_TAC [INTER_EMPTY, CONNECTED_EMPTY] THEN
      MAP_EVERY ASM_CASES_TAC [← q r"s = (:real^N)", ← q r"t = (:real^N)"] THEN
      ASM_REWRITE_TAC [INTER_UNIV, CONNECTED_UNIV] THEN
      ASM_CASES_TAC (← q r"s INTER t:real^N->bool = {}") THEN
      ASM_REWRITE_TAC [CONNECTED_EMPTY] THEN
      MP_TAC (← ISPECL
       [← q r"s UNION UNIONS {c | c IN components((:real^N) DIFF closure t) /\
                             ~(c INTER s = {})}",
        ← q r"t UNION UNIONS {c | c IN components((:real^N) DIFF closure s) /\
                             ~(c INTER t = {})}"]
       OPEN_UNICOHERENT_UNIV) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC OPEN_UNION THEN ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC [IN_ELIM_THM] THEN
          MESON_TAC [OPEN_COMPONENTS, closed, CLOSED_CLOSURE],
          MATCH_MP_TAC OPEN_UNION THEN ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC [IN_ELIM_THM] THEN
          MESON_TAC [OPEN_COMPONENTS, closed, CLOSED_CLOSURE],
          MATCH_MP_TAC (← MESON []
           (← q r"(s = {} \/ ~(s = {}) ==> connected(u UNION UNIONS s))
            ==> connected(u UNION UNIONS s)")) THEN
          STRIP_TAC THEN ASM_REWRITE_TAC [UNION_EMPTY, UNIONS_0] THEN
          ASM_SIMP_TAC [lemma] THEN MATCH_MP_TAC CONNECTED_UNIONS THEN
          REWRITE_TAC [FORALL_IN_GSPEC] THEN
          CONJ_TAC THENL
           [ASM_MESON_TAC [CONNECTED_UNION, IN_COMPONENTS_CONNECTED, UNION_COMM],
            ALL_TAC] THEN
          MATCH_MP_TAC (← SET_RULE (← q r"!s. s SUBSET t /\ ~(s = {}) ==> ~(t = {})")) THEN
          EXISTS_TAC (← q r"s:real^N->bool") THEN ASM_REWRITE_TAC [SUBSET_INTERS] THEN
          REWRITE_TAC [FORALL_IN_GSPEC, SUBSET_UNION],
          MATCH_MP_TAC (← MESON []
           (← q r"(s = {} \/ ~(s = {}) ==> connected(u UNION UNIONS s))
            ==> connected(u UNION UNIONS s)")) THEN
          STRIP_TAC THEN ASM_REWRITE_TAC [UNION_EMPTY, UNIONS_0] THEN
          ASM_SIMP_TAC [lemma] THEN MATCH_MP_TAC CONNECTED_UNIONS THEN
          REWRITE_TAC [FORALL_IN_GSPEC] THEN
          CONJ_TAC THENL
           [ASM_MESON_TAC [CONNECTED_UNION, IN_COMPONENTS_CONNECTED, UNION_COMM],
            ALL_TAC] THEN
          MATCH_MP_TAC (← SET_RULE (← q r"!s. s SUBSET t /\ ~(s = {}) ==> ~(t = {})")) THEN
          EXISTS_TAC (← q r"t:real^N->bool") THEN ASM_REWRITE_TAC [SUBSET_INTERS] THEN
          REWRITE_TAC [FORALL_IN_GSPEC, SUBSET_UNION],
          GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"x:real^N") THEN
          REWRITE_TAC [IN_UNION, UNIONS_GSPEC, IN_UNIV, IN_ELIM_THM] THEN
          ASM_CASES_TAC (← q r"(x:real^N) IN s") THEN ASM_REWRITE_TAC [] THEN
          ASM_CASES_TAC (← q r"(x:real^N) IN t") THEN ASM_REWRITE_TAC [] THEN
          FIRST_ASSUM (MP_TAC o SPEC (← q r"x:real^N") o MATCH_MP (← SET_RULE
           (← q r"DISJOINT s t ==> !x. ~(x IN s) \/ ~(x IN t)"))) THEN
          ASM_SIMP_TAC [frontier, INTERIOR_OPEN, IN_DIFF] THEN STRIP_TAC THENL
           [SUBGOAL_THEN (← q r"x IN UNIONS(components((:real^N) DIFF closure s))")
            MP_TAC THENL
             [ASM_REWRITE_TAC [← GSYM UNIONS_COMPONENTS, IN_DIFF, IN_UNIV],
              ALL_TAC] THEN
            REWRITE_TAC [IN_UNIONS] THEN
            DISCH_THEN (X_CHOOSE_THEN (← q r"c:real^N->bool") STRIP_ASSUME_TAC) THEN
            ASM_CASES_TAC (← q r"c INTER t:real^N->bool = {}") THENL
             [ALL_TAC, ASM_MESON_TAC []] THEN
            SUBGOAL_THEN (← q r"c INTER closure(t:real^N->bool) = {}") ASSUME_TAC THENL
             [ASM_MESON_TAC [OPEN_INTER_CLOSURE_EQ_EMPTY, OPEN_COMPONENTS,
                             closed, CLOSED_CLOSURE],
              ALL_TAC] THEN
            SUBGOAL_THEN (← q r"x IN UNIONS(components((:real^N) DIFF closure t))")
            MP_TAC THENL
             [ASM_REWRITE_TAC [← GSYM UNIONS_COMPONENTS, IN_DIFF, IN_UNIV] THEN
              ASM SET_TAC [],
              ALL_TAC] THEN
            REWRITE_TAC [IN_UNIONS] THEN
            DISCH_THEN (X_CHOOSE_THEN (← q r"d:real^N->bool") STRIP_ASSUME_TAC) THEN
            ASM_CASES_TAC (← q r"d INTER s:real^N->bool = {}") THENL
             [ALL_TAC, ASM_MESON_TAC []] THEN
            SUBGOAL_THEN (← q r"d INTER closure(s:real^N->bool) = {}") ASSUME_TAC THENL
             [ASM_MESON_TAC [OPEN_INTER_CLOSURE_EQ_EMPTY, OPEN_COMPONENTS,
                             closed, CLOSED_CLOSURE],
              ALL_TAC],
            SUBGOAL_THEN (← q r"x IN UNIONS(components((:real^N) DIFF closure t))")
            MP_TAC THENL
             [ASM_REWRITE_TAC [← GSYM UNIONS_COMPONENTS, IN_DIFF, IN_UNIV],
              ALL_TAC] THEN
            REWRITE_TAC [IN_UNIONS] THEN
            DISCH_THEN (X_CHOOSE_THEN (← q r"d:real^N->bool") STRIP_ASSUME_TAC) THEN
            ASM_CASES_TAC (← q r"d INTER s:real^N->bool = {}") THENL
             [ALL_TAC, ASM_MESON_TAC []] THEN
            SUBGOAL_THEN (← q r"d INTER closure(s:real^N->bool) = {}") ASSUME_TAC THENL
             [ASM_MESON_TAC [OPEN_INTER_CLOSURE_EQ_EMPTY, OPEN_COMPONENTS,
                             closed, CLOSED_CLOSURE],
              ALL_TAC] THEN
            SUBGOAL_THEN (← q r"x IN UNIONS(components((:real^N) DIFF closure s))")
            MP_TAC THENL
             [ASM_REWRITE_TAC [← GSYM UNIONS_COMPONENTS, IN_DIFF, IN_UNIV] THEN
              ASM SET_TAC [],
              ALL_TAC] THEN
            REWRITE_TAC [IN_UNIONS] THEN
            DISCH_THEN (X_CHOOSE_THEN (← q r"c:real^N->bool") STRIP_ASSUME_TAC) THEN
            ASM_CASES_TAC (← q r"c INTER t:real^N->bool = {}") THENL
             [ALL_TAC, ASM_MESON_TAC []] THEN
            SUBGOAL_THEN (← q r"c INTER closure(t:real^N->bool) = {}") ASSUME_TAC THENL
             [ASM_MESON_TAC [OPEN_INTER_CLOSURE_EQ_EMPTY, OPEN_COMPONENTS,
                             closed, CLOSED_CLOSURE],
              ALL_TAC]] THEN
         (FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
           (← q r"DISJOINT s t ==> !c d. ~(c = {}) /\ c SUBSET s /\ d SUBSET t /\ c = d
                                   ==> p"))) THEN
          MAP_EVERY EXISTS_TAC
           [← q r"frontier c:real^N->bool", ← q r"frontier d:real^N->bool"] THEN
          REPEAT CONJ_TAC THENL
           [REWRITE_TAC [FRONTIER_EQ_EMPTY, DE_MORGAN_THM] THEN
            ASM_MESON_TAC [IN_COMPONENTS_NONEMPTY, IN_COMPONENTS_SUBSET,
                           ← SET_RULE (← q r"s SUBSET UNIV DIFF t /\ s = UNIV ==> t = {}"),
                           CLOSURE_EQ_EMPTY],
            ASM_MESON_TAC [FRONTIER_OF_COMPONENTS_SUBSET, FRONTIER_COMPLEMENT,
                           FRONTIER_CLOSURE_SUBSET, SUBSET_TRANS],
            ASM_MESON_TAC [FRONTIER_OF_COMPONENTS_SUBSET, FRONTIER_COMPLEMENT,
                           FRONTIER_CLOSURE_SUBSET, SUBSET_TRANS],
            AP_TERM_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
            MATCH_MP_TAC COMPONENTS_MAXIMAL THENL
             [EXISTS_TAC (← q r"(:real^N) DIFF closure t"),
              EXISTS_TAC (← q r"(:real^N) DIFF closure s")] THEN
            ASM_REWRITE_TAC [] THEN
            (CONJ_TAC THENL [ASM_MESON_TAC [IN_COMPONENTS_CONNECTED],
             ASM SET_TAC []])])],
        ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      MATCH_MP_TAC (← SET_RULE
       (← q r"s INTER t' = {} /\ t INTER s' = {} /\ s' INTER t' = {}
        ==> (s UNION s') INTER (t UNION t') = s INTER t")) THEN
      REWRITE_TAC [INTER_UNIONS, EMPTY_UNIONS, FORALL_IN_GSPEC,
                   UNIONS_SUBSET] THEN
      REPEAT CONJ_TAC THEN X_GEN_TAC (← q r"d:real^N->bool") THENL
       [MP_TAC (← ISPEC (← q r"s:real^N->bool") CLOSURE_SUBSET) THEN
        MP_TAC (← ISPECL [← q r"(:real^N) DIFF closure s", ← q r"d:real^N->bool"]
          IN_COMPONENTS_SUBSET) THEN
        SET_TAC [],
        MP_TAC (← ISPEC (← q r"t:real^N->bool") CLOSURE_SUBSET) THEN
        MP_TAC (← ISPECL [← q r"(:real^N) DIFF closure t", ← q r"d:real^N->bool"]
          IN_COMPONENTS_SUBSET) THEN
        SET_TAC [],
        STRIP_TAC THEN X_GEN_TAC (← q r"c:real^N->bool") THEN STRIP_TAC] THEN
      MATCH_MP_TAC (← TAUT (← q r"(~p ==> F) ==> p")) THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
       (← q r"DISJOINT s t
        ==> !c d. c SUBSET s /\ d SUBSET t /\ ~(c INTER d = {}) ==> F"))) THEN
      MAP_EVERY EXISTS_TAC
       [← q r"frontier c:real^N->bool", ← q r"frontier d:real^N->bool"] THEN
      REPEAT (CONJ_TAC THENL
       [ASM_MESON_TAC [FRONTIER_OF_COMPONENTS_SUBSET, FRONTIER_COMPLEMENT,
                        FRONTIER_CLOSURE_SUBSET, SUBSET_TRANS], ALL_TAC]) THEN
      MATCH_MP_TAC CONNECTED_INTER_FRONTIER THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_FRONTIER_COMPONENT_COMPLEMENT THEN
        EXISTS_TAC (← q r"closure s:real^N->bool") THEN
        ASM_MESON_TAC [CONNECTED_CLOSURE],
        ALL_TAC] THEN
      ONCE_REWRITE_TAC [← SET_RULE (← q r"c DIFF d = c INTER (UNIV DIFF d)")] THEN
      ONCE_REWRITE_TAC [INTER_COMM] THEN CONJ_TAC THEN
      MATCH_MP_TAC CONNECTED_INTER_FRONTIER THEN
      ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC [IN_COMPONENTS_CONNECTED],
        ALL_TAC,
        MATCH_MP_TAC COMPONENT_COMPLEMENT_CONNECTED THEN
        EXISTS_TAC (← q r"closure t:real^N->bool") THEN
        ASM_SIMP_TAC [CONNECTED_UNIV, SUBSET_UNIV, CONNECTED_CLOSURE],
        ALL_TAC,
        ALL_TAC] THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
      MP_TAC (← ISPEC (← q r"s:real^N->bool") CLOSURE_SUBSET) THEN
      MP_TAC (← ISPEC (← q r"t:real^N->bool") CLOSURE_SUBSET) THEN ASM SET_TAC []))

  let NONSEPARATION_BY_COMPONENT_EQ ← prove
   r"!s. (open s \/ closed s)
       ==> ((!c. c IN components s ==> connected((:real^N) DIFF c)) <=>
            connected((:real^N) DIFF s))"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC [SEPARATION_BY_COMPONENT_OPEN],
      ALL_TAC,
      ASM_MESON_TAC [SEPARATION_BY_COMPONENT_CLOSED],
      ALL_TAC] THEN
    MATCH_MP_TAC COMPONENT_COMPLEMENT_CONNECTED THEN
    EXISTS_TAC (← q r"(:real^N) DIFF s") THEN
    ASM_REWRITE_TAC [CONNECTED_UNIV, SUBSET_UNIV,
                     COMPL_COMPL])

  let CONNECTED_COMMON_FRONTIER_DOMAINS ← prove
   r"!s t c:real^N->bool.
        open s /\ connected s /\
        open t /\ connected t /\
        ~(s = t) /\ frontier s = c /\ frontier t = c
        ==> connected c"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"t:real^N->bool"]
          COMMON_FRONTIER_DOMAINS) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"t:real^N->bool"]
      CONNECTED_FRONTIER_DISJOINT) THEN
    ASM_REWRITE_TAC [SUBSET_REFL])

  pure { CONNECTED_INTER_DISJOINT_OPEN_FRONTIERS, NONSEPARATION_BY_COMPONENT_EQ,
         CONNECTED_COMMON_FRONTIER_DOMAINS }

/- ------------------------------------------------------------------------- -/
/- The frontier of an ANR is locally connected (this is only this late       -/
/- since it's handy to use basics about unicoherence).                       -/
/- (moretop.ml 6736-7182)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MOW where
  LOCALLY_CONNECTED_FRONTIER_ANR : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOW [HolBase] (D : MoreTopDeps) (BMOT : MOT) : ExceptT String IO MOW := do
  -- @@SCOPE BEGIN
  let { CONVEX_IMP_UNICOHERENT, unicoherent, .. } := BMOT
  let { CLOSED_IN_CONNECTED_COMPONENT, CLOSED_IN_INTER_CLOSURE, .. } := D.qtopology
  let { LOCALLY_CONNECTED_IM_KLEINEN, .. } := D.qpaths
  let { COMPONENT_COMPLEMENT_CONNECTED, .. } := D.qconvex
  let { ACCESSIBLE_FRONTIER_ANR_INTER_COMPLEMENT_COMPONENT, ANR_IMP_NEIGHBOURHOOD_RETRACT,
        FINITE_ANR_COMPLEMENT_COMPONENTS_CONCENTRIC, retract_of, retraction,
        .. } := D.qdegree
  let { CONNECTED_CLOSURE, CONNECTED_CONNECTED_COMPONENT, .. } := D.ra.ts.cn.ms.qtopology1
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON, MESON_TAC, NORM_ARITH, REAL_ARITH,
        REAL_RAT_REDUCE_CONV, SET_RULE, SET_TAC, VECTOR_ARITH, .. } := D.ra.ts.cn.cx.cvx
  let { reversepath, .. } := D.ra.ts.cn.ms.ig.qpaths
  let { CLOSED_OPEN_INTERVAL_1, .. } := D.ra.ts.cn.ms.ig.qtopology
  let { ARITH_EQ, CONJ_ASSOC, CONTRAPOS_THM, EXISTS_IN_GSPEC, EXISTS_IN_IMAGE,
        EXISTS_IN_INSERT, EXTENSION, FINITE_IMAGE, FINITE_INSERT, FINITE_RESTRICT,
        FORALL_IN_GSPEC, .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_IN_INSERT, FORALL_UNWIND_THM2, FUN_IN_IMAGE, IMP_CONJ,
        IMP_CONJ_ALT, IMP_IMP, IN_DELETE, IN_DIFF, .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, IN_INTER, IN_SING, IN_UNION, IN_UNIV, LEFT_IMP_EXISTS_THM,
        MEMBER_NOT_EMPTY, MONO_AND, NOT_IN_EMPTY, NOT_INSERT_EMPTY,
        .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_INF_LE_FINITE, REAL_LE_MIN, REAL_LE_TRANS, REAL_LT_01, REAL_LT_IMP_LE,
        REAL_LT_INF_FINITE, REAL_LT_MIN, .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_NOT_LT, REAL_POS, RIGHT_FORALL_IMP_THM, SUBSET, SUBSET_INTER, SUBSET_REFL,
        SUBSET_TRANS, .. } := D.ra.ts.cn.cx.cvx.core5
  let { SUBSET_UNIV, SWAP_FORALL_THM, UNIONS_GSPEC, UNIONS_SUBSET, UNIONS_UNION,
        .. } := D.ra.ts.cn.cx.cvx.core6
  let { REAL_HALF, .. } := D.ra.ts.cn.cx.cvx.misc
  let { DIST_0, DIST_REFL, DIST_SYM, .. } := D.ra.ts.cn.cx.cvx.vec1
  let { DROP_CMUL, DROP_EQ, DROP_SUB, DROP_VEC, INTERVAL_OPEN_SUBSET_CLOSED, LIFT_DROP,
        .. } := D.ra.ts.cn.cx.cvx.vec2
  let { dist, VECTOR_ADD_RID, .. } := D.ra.ts.cn.cx.cvx.vec4
  let { CLOSED_IN_DIFF, CLOSED_IN_TRANS, OPEN_IN_DIFF, OPEN_IN_TRANS, SUBTOPOLOGY_UNIV,
        .. } := D.ra.ts.cn.cx.cvx.met
  let { BALL_SUBSET_CBALL, CENTRE_IN_BALL, CENTRE_IN_CBALL, CLOSED_CBALL, CLOSED_CLOSURE,
        CLOSED_IN, CLOSED_IN_CLOSED_INTER, CLOSED_SUBSET, CLOSURE_APPROACHABLE,
        .. } := D.ra.ts.cn.cx.cvx.top1
  let { CLOSURE_INC, CLOSURE_MINIMAL, CLOSURE_OPEN_INTERVAL, CLOSURE_SUBSET, CLOSURE_UNION,
        COMPACT_CBALL, COMPACT_IMP_CLOSED, COMPACT_SUMS, COMPONENTS_MAXIMAL,
        CONNECTED_COMPONENT_MAXIMAL, CONNECTED_COMPONENT_SUBSET,
        CONNECTED_CONTINUOUS_IMAGE, .. } := D.ra.ts.cn.cx.cvx.top2
  let { CONTINUOUS_ON_ID, CONTINUOUS_ON_SUBSET, FORALL_IN_CLOSURE, FRONTIER_COMPLEMENT,
        FRONTIER_SUBSET_EQ, .. } := D.ra.ts.cn.cx.cvx.top3
  let { IN_BALL, IN_CBALL, IN_CBALL_0, IN_COMPONENTS_CONNECTED, IN_COMPONENTS_NONEMPTY,
        IN_COMPONENTS_SUBSET, IN_INTERIOR_CBALL, IN_INTERVAL_1, INTERIOR_CBALL,
        INTERIOR_MAXIMAL_EQ, INTERIOR_SUBSET, OPEN_BALL, .. } := D.ra.ts.cn.cx.cvx.top4
  let { components, continuous_on, frontier, OPEN_IN, OPEN_IN_OPEN_INTER, OPEN_IN_REFL,
        OPEN_INTER_CLOSURE_EQ_EMPTY, SETDIST_LE_DIST, SUBSET_CLOSURE, UNIONS_COMPONENTS,
        UNIT_INTERVAL_NONEMPTY, .. } := D.ra.ts.cn.cx.cvx.top5
  let { CONNECTED_CBALL, CONNECTED_INTERVAL, .. } := D.ra.ts.cn.ms.ig.dv.qconvex
  let { EXISTS_COMPONENT_SUPERSET, .. } := D.ra.ts.cn.ms.ig.dv.qtopology1
  let { open_def, .. } := D.ra.ts.cn.ms.ig.dv.qtopology2
  let { CONVEX_CONNECTED, .. } := D.ra.ts.cn.ms.ig.dv.dg.qconvex
  let { ARC_IMP_PATH, CONNECTED_PATH_IMAGE, CONVEX_IMP_LOCALLY_CONNECTED,
        CONVEX_IMP_LOCALLY_PATH_CONNECTED, .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths1
  let { joinpaths, OPEN_IN_COMPONENTS_LOCALLY_CONNECTED,
        OPEN_IN_CONNECTED_COMPONENT_LOCALLY_CONNECTED, path, path_component,
        PATH_COMPONENT_EQ_CONNECTED_COMPONENT, path_image, PATH_JOIN, PATH_REVERSEPATH,
        pathfinish, PATHFINISH_IN_PATH_IMAGE, PATHFINISH_JOIN, PATHFINISH_REVERSEPATH,
        pathstart, PATHSTART_IN_PATH_IMAGE, PATHSTART_JOIN, PATHSTART_REVERSEPATH,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths2
  let { BALL_UNION_SPHERE, CBALL_MIN_INTER, CLOSED_IN_COMPONENT, CLOSURE_UNION_FRONTIER,
        CLOSURE_UNIONS, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { connected_component, LOCALLY_OPEN_SUBSET, OPEN_CLOSED, OPEN_IN_CONTAINS_CBALL,
        OPEN_IN_DIFF_CLOSED, OPEN_INTER_CLOSURE_SUBSET, OPEN_SUMS,
        SETDIST_EQ_0_COMPACT_CLOSED, SETDIST_POS_LT, SUBSET_BALLS,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology2
  let { ENDS_IN_UNIT_INTERVAL, .. } := D.ra.ts.cn.ms.ig.dv.dg.qvec
  let { VEC_EQ, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qvec
  let { CLOSED_IN_REFL, REAL_LE_SETDIST, SETDIST_EQ_0_SING,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qtop
  let { CONVEX_BALL, CONVEX_CBALL, CONVEX_INTER, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  -- @@SCOPE END

  let LOCALLY_CONNECTED_FRONTIER_ANR ← prove
   r"!s:real^N->bool.
        compact s /\ ANR s ==> locally connected (frontier s)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [LOCALLY_CONNECTED_IM_KLEINEN] THEN
    MAP_EVERY X_GEN_TAC [← q r"v:real^N->bool", ← q r"p:real^N"] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [OPEN_IN_CONTAINS_CBALL]) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC (← q r"p:real^N"))) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"e:real") THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"(:real^N)"]
          ANR_IMP_NEIGHBOURHOOD_RETRACT) THEN
    REWRITE_TAC [SUBTOPOLOGY_UNIV, ← GSYM OPEN_IN, ← GSYM CLOSED_IN] THEN
    ASM_SIMP_TAC [COMPACT_IMP_CLOSED] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:real^N->bool") STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [retract_of]) THEN
    REWRITE_TAC [retraction, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"r:real^N->real^N") THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"frontier(s:real^N->bool) SUBSET s") ASSUME_TAC THENL
     [ASM_SIMP_TAC [FRONTIER_SUBSET_EQ, COMPACT_IMP_CLOSED], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(p:real^N) IN s") ASSUME_TAC THENL
     [ASM SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"?d. &0 < d /\ d < e /\
          {x + l:real^N | x IN s /\ l IN cball(vec 0,d)} SUBSET u /\
          !y:real^N. dist(p,y) <= d ==> dist(p,r y) <= e")
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN
       (← q r"?d. &0 < d /\ {x + l:real^N | x IN s /\ l IN cball(vec 0,d)} SUBSET u")
      STRIP_ASSUME_TAC THENL
       [ASM_CASES_TAC (← q r"s:real^N->bool = {}") THEN
        ASM_REWRITE_TAC [← SET_RULE (← q r"{f x y | x IN {} /\ P y} SUBSET u")] THENL
         [MESON_TAC [REAL_LT_01], ALL_TAC] THEN
        ASM_CASES_TAC (← q r"u = (:real^N)") THEN ASM_REWRITE_TAC [SUBSET_UNIV] THENL
         [MESON_TAC [REAL_LT_01], ALL_TAC] THEN
        EXISTS_TAC (← q r"setdist(s,(:real^N) DIFF u) / &2") THEN
        MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
         [REWRITE_TAC [REAL_HALF, SETDIST_POS_LT] THEN
          ASM_SIMP_TAC [SETDIST_EQ_0_COMPACT_CLOSED, ← GSYM OPEN_CLOSED] THEN
          ASM SET_TAC [],
          REWRITE_TAC [REAL_HALF, SUBSET, FORALL_IN_GSPEC] THEN DISCH_TAC THEN
          MAP_EVERY X_GEN_TAC [← q r"x:real^N", ← q r"l:real^N"] THEN
          DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
          ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN REWRITE_TAC [IN_CBALL_0] THEN
          DISCH_TAC THEN MATCH_MP_TAC (← REAL_ARITH
           (← q r"&0 < s /\ s <= e ==> ~(e <= s / &2)")) THEN
          ASM_REWRITE_TAC [] THEN
          SUBST1_TAC (← NORM_ARITH (← q r"norm(l:real^N) = dist(x,x + l)")) THEN
          MATCH_MP_TAC SETDIST_LE_DIST THEN ASM SET_TAC []],
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [continuous_on]) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"p:real^N")) THEN
        ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN (MP_TAC o SPEC (← q r"e:real"))] THEN
        ASM_SIMP_TAC [LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC (← q r"d':real") THEN STRIP_TAC THEN
        EXISTS_TAC (← q r"min (e / &2) (min d (d' / &2))") THEN
        ASM_SIMP_TAC [REAL_LT_MIN, REAL_LE_MIN, REAL_HALF, CBALL_MIN_INTER] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
        CONJ_TAC THENL [ASM SET_TAC [], REWRITE_TAC [CONJ_ASSOC]] THEN
        X_GEN_TAC (← q r"y:real^N") THEN STRIP_TAC THEN ONCE_REWRITE_TAC [DIST_SYM] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ONCE_REWRITE_TAC [DIST_SYM] THEN
        CONJ_TAC THENL [ALL_TAC, ASM_REAL_ARITH_TAC] THEN
        UNDISCH_TAC
         (← q r"{x + l:real^N | x IN s /\ l IN cball(vec 0,d)} SUBSET u") THEN
        REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC [IN_ELIM_THM, IN_CBALL_0] THEN
        MAP_EVERY EXISTS_TAC [← q r"p:real^N", ← q r"y - p:real^N"] THEN
        ASM_REWRITE_TAC [← ONCE_REWRITE_RULE [DIST_SYM] (← GSYM dist)] THEN
        CONV_TAC (fun t => VECTOR_ARITH t)],
      ABBREV_TAC (← q r"sd = {x + l:real^N | x IN s /\ l IN cball(vec 0,d)}")] THEN
    SUBGOAL_THEN (← q r"(s:real^N->bool) SUBSET interior sd") ASSUME_TAC THENL
     [TRANS_TAC SUBSET_TRANS
       (← q r"{x + l:real^N | x IN s /\ l IN ball(vec 0,d)}") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC (← SET_RULE
         (← q r"vec 0 IN t /\ (!x:real^N. f x (vec 0) = x)
          ==> s SUBSET {f x y | x IN s /\ y IN t}")) THEN
        ASM_REWRITE_TAC [CENTRE_IN_BALL, VECTOR_ADD_RID],
        SIMP_TAC [INTERIOR_MAXIMAL_EQ, OPEN_SUMS, OPEN_BALL] THEN
        EXPAND_TAC "sd" THEN REWRITE_TAC [← GSYM BALL_UNION_SPHERE] THEN
        SET_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(s:real^N->bool) SUBSET sd") ASSUME_TAC THENL
     [ASM_MESON_TAC [SUBSET_TRANS, INTERIOR_SUBSET], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"compact(sd:real^N->bool)") ASSUME_TAC THENL
     [EXPAND_TAC "sd" THEN ASM_SIMP_TAC [COMPACT_SUMS, COMPACT_CBALL],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"?k. &0 < k /\ k <= d /\
          (!x. ~(x IN u) ==> k <= dist(p,x)) /\
          (!c x. c IN components(cball(p,d) DIFF s) /\
                 ~(p IN closure c) /\ x IN c
                 ==> k <= dist(p:real^N,x))")
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [open_def]) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"p:real^N")) THEN
      ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"k:real") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [← GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC [REAL_NOT_LT] THEN STRIP_TAC THEN
      EXISTS_TAC
       (← q r"inf (k INSERT (d / &2) INSERT
             IMAGE (\c. setdist({p:real^N},c))
                   {c | c IN components (cball (p,d) DIFF s) /\
                        ~(closure c INTER cball (p,d / &2) = {}) /\
                        ~(p IN closure c)})") THEN
      MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"p:real^N", ← q r"d / &2", ← q r"d:real"]
        FINITE_ANR_COMPLEMENT_COMPONENTS_CONCENTRIC) THEN
      ASM_REWRITE_TAC [← REAL_ARITH (← q r"e / &2 < e <=> &0 < e")] THEN
      DISCH_TAC THEN
      ONCE_REWRITE_TAC [← SET_RULE
        (← q r"{x | P x /\ Q x /\ R x} = {x | x IN {y | P y /\ Q y} /\ R x}")] THEN
      ASM_SIMP_TAC [REAL_LT_INF_FINITE, NOT_INSERT_EMPTY, FINITE_INSERT,
                    FINITE_IMAGE, FINITE_RESTRICT, REAL_INF_LE_FINITE] THEN
      REWRITE_TAC [EXISTS_IN_INSERT, FORALL_IN_INSERT] THEN
      REWRITE_TAC [FORALL_IN_IMAGE, EXISTS_IN_IMAGE] THEN
      REWRITE_TAC [← GSYM CONJ_ASSOC, EXISTS_IN_GSPEC] THEN
      ASM_REWRITE_TAC [IMP_CONJ, FORALL_IN_GSPEC, REAL_HALF] THEN
      REPEAT CONJ_TAC THENL
       [X_GEN_TAC (← q r"c:real^N->bool") THEN REPEAT DISCH_TAC THEN
        REWRITE_TAC [SETDIST_POS_LT, SETDIST_EQ_0_SING] THEN
        ASM_MESON_TAC [IN_COMPONENTS_NONEMPTY],
        DISJ2_TAC THEN DISJ1_TAC THEN ASM_REAL_ARITH_TAC,
        ASM_MESON_TAC [DIST_SYM],
        MAP_EVERY X_GEN_TAC [← q r"c:real^N->bool", ← q r"x:real^N"] THEN
        REPEAT DISCH_TAC THEN DISJ2_TAC THEN
        ASM_CASES_TAC (← q r"closure c INTER cball(p:real^N,d / &2) = {}") THENL
         [DISJ1_TAC THEN TRANS_TAC REAL_LE_TRANS (← q r"setdist({p:real^N},c)") THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_SETDIST THEN
            FIRST_ASSUM (ASSUME_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
            ASM_REWRITE_TAC [NOT_INSERT_EMPTY, IMP_CONJ, IN_SING] THEN
            REWRITE_TAC [RIGHT_FORALL_IMP_THM, FORALL_UNWIND_THM2] THEN
            X_GEN_TAC (← q r"y:real^N") THEN DISCH_TAC THEN
            FIRST_X_ASSUM (MP_TAC o SPEC (← q r"y:real^N") o
              GEN_REWRITE_RULE id [EXTENSION]) THEN
            ASM_SIMP_TAC [IN_INTER, CLOSURE_INC, NOT_IN_EMPTY, IN_CBALL] THEN
            CONV_TAC (fun t => NORM_ARITH t),
            MATCH_MP_TAC SETDIST_LE_DIST THEN ASM_REWRITE_TAC [IN_SING]],
          DISJ2_TAC THEN EXISTS_TAC (← q r"c:real^N->bool") THEN ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC SETDIST_LE_DIST THEN ASM_REWRITE_TAC [IN_SING]]],
      ALL_TAC] THEN
    EXISTS_TAC (← q r"frontier s INTER ball(p:real^N,k)") THEN
    SIMP_TAC [OPEN_IN_OPEN_INTER, OPEN_BALL, IN_INTER] THEN
    ASM_REWRITE_TAC [CENTRE_IN_BALL] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC [],
      SUBGOAL_THEN (← q r"ball(p:real^N,k) SUBSET cball(p,e)") MP_TAC THENL
       [REWRITE_TAC [SUBSET_BALLS, DIST_REFL] THEN ASM_REAL_ARITH_TAC,
        ASM SET_TAC []],
      X_GEN_TAC (← q r"q:real^N") THEN REWRITE_TAC [IN_BALL] THEN STRIP_TAC] THEN
    SUBGOAL_THEN
     (← q r"?c. c IN components(cball(p:real^N,d) DIFF s) /\ q IN closure c")
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN
       (← q r"q IN closure
         (UNIONS {c | c IN components (cball(p:real^N,d) DIFF s) /\
                      ~(closure c INTER cball(p,(k + dist (p,q)) / &2) = {})}
          UNION
          UNIONS {c | c IN components (cball(p,d) DIFF s) /\
                      closure c INTER cball(p,(k + dist (p,q)) / &2) = {}})")
      MP_TAC THENL
       [REWRITE_TAC [← GSYM UNIONS_UNION, ← GSYM UNIONS_COMPONENTS, ← SET_RULE
         (← q r"{x | x IN s /\ ~P x} UNION {x | x IN s /\ P x} = s")] THEN
        MATCH_MP_TAC (← SET_RULE (← q r"!s. s SUBSET t /\ x IN s ==> x IN t")) THEN
        EXISTS_TAC (← q r"closure(ball(p:real^N,d) DIFF s)") THEN
        SIMP_TAC [SUBSET_CLOSURE, BALL_SUBSET_CBALL, ← SET_RULE
          (← q r"s SUBSET t ==> s DIFF c SUBSET t DIFF c")] THEN
        ONCE_REWRITE_TAC [← SET_RULE (← q r"s DIFF t = s INTER (UNIV DIFF t)")] THEN
        W (MP_TAC o PART_MATCH (rand o rand) OPEN_INTER_CLOSURE_SUBSET o
          rand o snd) THEN
        REWRITE_TAC [OPEN_BALL] THEN MATCH_MP_TAC (← SET_RULE
         (← q r"x IN s ==> s SUBSET t ==> x IN t")) THEN
        ASM_REWRITE_TAC [IN_BALL, IN_INTER] THEN
        ASM_REWRITE_TAC [CLOSURE_UNION_FRONTIER, FRONTIER_COMPLEMENT,
                         IN_UNION] THEN
        ASM_REAL_ARITH_TAC,
        REWRITE_TAC [CLOSURE_UNION, IN_UNION] THEN
        MATCH_MP_TAC (← TAUT (← q r"~q /\ (p ==> r) ==> p \/ q ==> r")) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC (← SET_RULE
           (← q r"!t. ~(x IN t) /\ s SUBSET t ==> ~(x IN s)")) THEN
          EXISTS_TAC (← q r"(:real^N) DIFF ball(p,(k + dist(p,q)) / &2)") THEN
          ASM_REWRITE_TAC [IN_DIFF, IN_UNIV, IN_BALL] THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
          MATCH_MP_TAC CLOSURE_MINIMAL THEN
          REWRITE_TAC [← GSYM OPEN_CLOSED, OPEN_BALL] THEN
          REWRITE_TAC [UNIONS_SUBSET, FORALL_IN_GSPEC] THEN
          X_GEN_TAC (← q r"d:real^N->bool") THEN STRIP_TAC THEN
          FIRST_X_ASSUM (MP_TAC o MATCH_MP (← SET_RULE
          (← q r"d INTER cball(x:real^N,r) = {} ==> ball(x,r) SUBSET cball(x,r)
                  ==> ball(x,r) INTER d = {}"))) THEN
          SIMP_TAC [BALL_SUBSET_CBALL, OPEN_INTER_CLOSURE_EQ_EMPTY,
                    OPEN_BALL] THEN
          SET_TAC [],
          MP_TAC (← ISPECL
           [← q r"s:real^N->bool", ← q r"p:real^N",
            ← q r"(k + dist(p:real^N,q)) / &2", ← q r"d:real"]
            FINITE_ANR_COMPLEMENT_COMPONENTS_CONCENTRIC) THEN
          ASM_REWRITE_TAC [] THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC, SIMP_TAC [CLOSURE_UNIONS]] THEN
          DISCH_THEN (K ALL_TAC) THEN REWRITE_TAC [UNIONS_GSPEC, IN_ELIM_THM] THEN
          MESON_TAC []]],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"c:real^N->bool")) THEN
    ASM_REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [REWRITE_TAC [← GSYM REAL_NOT_LT, ← GSYM IN_BALL] THEN
      REWRITE_TAC [← SET_RULE (← q r"~(x IN s) <=> x IN (UNIV DIFF s)")] THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ_ALT]
       (← REWRITE_RULE [CONJ_ASSOC] FORALL_IN_CLOSURE))) THEN
      REWRITE_TAC [CONTINUOUS_ON_ID, ← GSYM OPEN_CLOSED, OPEN_BALL] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"q:real^N")) THEN
      ASM_REWRITE_TAC [IN_UNIV, IN_DIFF, IN_BALL],
      DISCH_TAC] THEN
    SUBGOAL_THEN
     (← q r"(p:real^N) IN frontier c /\ (q:real^N) IN frontier c")
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [CLOSURE_UNION_FRONTIER]) THEN
      ASM SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"?g. path g /\ pathstart g:real^N = p /\ pathfinish g = q /\
          (!t. t IN interval(vec 0,vec 1) ==> g t IN c)")
    STRIP_ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"c:real^N->bool"]
           ACCESSIBLE_FRONTIER_ANR_INTER_COMPLEMENT_COMPONENT) THEN
      ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"cball(p:real^N,d)")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (fun th => tactic_of do
          pure (MP_TAC (← SPEC (← q r"q:real^N") th) THEN
                MP_TAC (← SPEC (← q r"p:real^N") th))) THEN
      ASM_REWRITE_TAC [INTERIOR_CBALL, CENTRE_IN_BALL] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g1:real^1->real^N") STRIP_ASSUME_TAC) THEN
      REWRITE_TAC [IN_BALL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g2:real^1->real^N") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"path_component c (pathstart g1:real^N) (pathstart g2)")
      MP_TAC THENL
       [W (MP_TAC o PART_MATCH (lhand o rand)
          PATH_COMPONENT_EQ_CONNECTED_COMPONENT o rator o snd) THEN
        ANTS_TAC THENL
         [MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
          EXISTS_TAC (← q r"cball(p:real^N,d) DIFF s") THEN
          CONJ_TAC THENL
           [ALL_TAC,
            MATCH_MP_TAC OPEN_IN_COMPONENTS_LOCALLY_CONNECTED THEN
            ASM_REWRITE_TAC []] THEN
          MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
          EXISTS_TAC (← q r"cball(p:real^N,d)") THEN
          ASM_SIMP_TAC [OPEN_IN_DIFF_CLOSED, COMPACT_IMP_CLOSED] THEN
          SIMP_TAC [CONVEX_IMP_LOCALLY_PATH_CONNECTED, CONVEX_CBALL,
                    CONVEX_IMP_LOCALLY_CONNECTED],
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [connected_component] THEN
          EXISTS_TAC (← q r"c:real^N->bool") THEN REWRITE_TAC [SUBSET_REFL] THEN
          CONJ_TAC THENL [ASM_MESON_TAC [IN_COMPONENTS_CONNECTED], ALL_TAC] THEN
          REWRITE_TAC [pathstart] THEN
          REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC [IN_DELETE, ENDS_IN_UNIT_INTERVAL, VEC_EQ, ARITH_EQ]],
        REWRITE_TAC [path_component] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"g3:real^1->real^N") STRIP_ASSUME_TAC)] THEN
      EXISTS_TAC (← q r"reversepath g1 ++ g3 ++ g2:real^1->real^N") THEN
      ASM_SIMP_TAC [PATH_JOIN, PATHSTART_JOIN, PATHFINISH_JOIN,
                    PATHSTART_REVERSEPATH, PATHFINISH_REVERSEPATH] THEN
      ASM_SIMP_TAC [PATH_REVERSEPATH, ARC_IMP_PATH] THEN
      X_GEN_TAC (← q r"t:real^1") THEN REWRITE_TAC [IN_INTERVAL_1, DROP_VEC] THEN
      STRIP_TAC THEN REWRITE_TAC [joinpaths, reversepath] THEN
      REWRITE_TAC [DROP_SUB, DROP_VEC, DROP_CMUL] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [path_image, SUBSET, FORALL_IN_IMAGE]) THEN
      REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC [IN_DELETE, ← GSYM DROP_EQ, IN_INTERVAL_1, DROP_VEC,
                   DROP_SUB, DROP_CMUL] THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"path_image g SUBSET cball(p:real^N,d)") ASSUME_TAC THENL
     [TRANS_TAC SUBSET_TRANS (← q r"closure c:real^N->bool") THEN CONJ_TAC THENL
       [REWRITE_TAC [path_image, SUBSET, FORALL_IN_IMAGE] THEN
        SIMP_TAC [CLOSED_OPEN_INTERVAL_1, DROP_VEC, REAL_POS] THEN
        REWRITE_TAC [IN_UNION, IN_INSERT, NOT_IN_EMPTY] THEN
        ASM_MESON_TAC [CLOSURE_INC, pathstart, pathfinish],
        MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC [CLOSED_CBALL] THEN
        FIRST_X_ASSUM (MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
        SET_TAC []],
      ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"cball(p:real^N,e) INTER s",
      ← q r"IMAGE (r:real^N->real^N) (path_image g)"]
     EXISTS_COMPONENT_SUPERSET) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [SUBSET_INTER] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_CBALL] THEN
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC [← GSYM IN_CBALL] THEN ASM SET_TAC [],
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
         (← q r"IMAGE r u SUBSET s ==> t SUBSET u ==> IMAGE r t SUBSET s"))),
        REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_INTER] THEN
        EXISTS_TAC (← q r"p:real^N") THEN ASM_REWRITE_TAC [CENTRE_IN_CBALL] THEN
        ASM_REAL_ARITH_TAC,
        MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
        ASM_SIMP_TAC [CONNECTED_PATH_IMAGE] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
             (← REWRITE_RULE [IMP_CONJ] CONTINUOUS_ON_SUBSET))] THEN
      TRANS_TAC SUBSET_TRANS (← q r"sd:real^N->bool") THEN ASM_REWRITE_TAC [] THEN
      TRANS_TAC SUBSET_TRANS (← q r"cball(p:real^N,d)") THEN ASM_REWRITE_TAC [] THEN
      EXPAND_TAC "sd" THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
      X_GEN_TAC (← q r"y:real^N") THEN REWRITE_TAC [IN_CBALL] THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [← q r"p:real^N", ← q r"y - p:real^N"] THEN
      ASM_REWRITE_TAC [DIST_0] THEN
      ASM_REWRITE_TAC [← ONCE_REWRITE_RULE [DIST_SYM] (← GSYM dist)] THEN
      CONV_TAC (fun t => VECTOR_ARITH t),
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:real^N->bool") STRIP_ASSUME_TAC)] THEN
    ABBREV_TAC
     (← q r"h = connected_component (cball(p:real^N,e) DIFF f) (g(lift(&1 / &2)))") THEN
    MP_TAC (← ISPEC (← q r"cball(p:real^N,e)") CONVEX_IMP_UNICOHERENT) THEN
    REWRITE_TAC [CONVEX_CBALL, unicoherent] THEN DISCH_THEN (MP_TAC o SPECL
     [← q r"cball(p:real^N,e) DIFF h:real^N->bool", ← q r"closure h:real^N->bool"]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC COMPONENT_COMPLEMENT_CONNECTED THEN
        EXISTS_TAC (← q r"f:real^N->bool") THEN REWRITE_TAC [CONNECTED_CBALL] THEN
        REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC [IN_COMPONENTS_CONNECTED],
          ASM_MESON_TAC [IN_COMPONENTS_SUBSET, SUBSET_INTER],
          EXPAND_TAC "h" THEN REWRITE_TAC [components, IN_ELIM_THM] THEN
          EXISTS_TAC (← q r"g(lift(&1 / &2)):real^N") THEN REWRITE_TAC [] THEN
          FIRST_X_ASSUM (MP_TAC o SPEC (← q r"lift(&1 / &2)")) THEN
          REWRITE_TAC [IN_INTERVAL_1, DROP_VEC, LIFT_DROP] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV THEN
          REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
          SUBGOAL_THEN (← q r"cball(p:real^N,d) SUBSET cball(p,e)") MP_TAC THENL
           [ASM_REWRITE_TAC [SUBSET_BALLS, DIST_REFL] THEN ASM_REAL_ARITH_TAC,
            ASM SET_TAC []]],
        MATCH_MP_TAC CONNECTED_CLOSURE THEN EXPAND_TAC "h" THEN
        REWRITE_TAC [CONNECTED_CONNECTED_COMPONENT],
        MATCH_MP_TAC (← SET_RULE
         (← q r"h SUBSET c /\ c SUBSET b ==> (b DIFF h) UNION c = b")) THEN
        REWRITE_TAC [CLOSURE_SUBSET] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
        REWRITE_TAC [CLOSED_CBALL] THEN EXPAND_TAC "h" THEN
        TRANS_TAC SUBSET_TRANS (← q r"cball(p:real^N,e) DIFF f") THEN
        REWRITE_TAC [CONNECTED_COMPONENT_SUBSET] THEN SET_TAC [],
        MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC [CLOSED_IN_REFL] THEN
        MATCH_MP_TAC OPEN_IN_TRANS THEN
        EXISTS_TAC (← q r"cball(p:real^N,e) DIFF f") THEN CONJ_TAC THENL
         [EXPAND_TAC "h" THEN
          MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENT_LOCALLY_CONNECTED THEN
          MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
          EXISTS_TAC (← q r"cball(p:real^N,e)") THEN
          SIMP_TAC [CONVEX_CBALL, CONVEX_IMP_LOCALLY_CONNECTED],
          ALL_TAC] THEN
        MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC [OPEN_IN_REFL] THEN
        TRANS_TAC CLOSED_IN_TRANS (← q r"cball(p:real^N,e) INTER s") THEN
        ASM_SIMP_TAC [CLOSED_IN_CLOSED_INTER, COMPACT_IMP_CLOSED] THEN
        ASM_SIMP_TAC [CLOSED_IN_COMPONENT],
        MATCH_MP_TAC CLOSED_SUBSET THEN REWRITE_TAC [CLOSED_CLOSURE] THEN
        MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC [CLOSED_CBALL] THEN
        EXPAND_TAC "h" THEN
        TRANS_TAC SUBSET_TRANS (← q r"cball(p:real^N,e) DIFF f") THEN
        REWRITE_TAC [CONNECTED_COMPONENT_SUBSET] THEN SET_TAC []],
      ABBREV_TAC (← q r"j = (cball(p:real^N,e) DIFF h) INTER closure h") THEN
      DISCH_TAC] THEN
    EXISTS_TAC (← q r"j:real^N->bool") THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [TRANS_TAC SUBSET_TRANS (← q r"cball(p:real^N,e) INTER frontier s") THEN
      ASM_REWRITE_TAC [SUBSET_INTER] THEN
      CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      EXPAND_TAC "j" THEN REWRITE_TAC [SUBSET] THEN
      X_GEN_TAC (← q r"x:real^N") THEN REWRITE_TAC [IN_DIFF, IN_INTER] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN (← q r"(x:real^N) IN f") ASSUME_TAC THENL
       [MP_TAC (← ISPECL [← q r"cball(p:real^N,e) DIFF f", ← q r"g(lift(&1 / &2)):real^N"]
          CLOSED_IN_CONNECTED_COMPONENT) THEN
        ASM_REWRITE_TAC [CLOSED_IN_INTER_CLOSURE] THEN ASM SET_TAC [],
        ALL_TAC] THEN
      REWRITE_TAC [frontier, IN_DIFF] THEN REPEAT STRIP_TAC THENL
       [MATCH_MP_TAC CLOSURE_INC THEN
        REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
        ASM SET_TAC [],
        ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [IN_INTERIOR_CBALL]) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"r:real") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"cball(p:real^N,e) INTER ball(x,r) SUBSET f") ASSUME_TAC THENL
       [MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
        EXISTS_TAC (← q r"cball(p:real^N,e) INTER s") THEN
        ASM_SIMP_TAC [CONVEX_CONNECTED, CONVEX_INTER,
                      CONVEX_BALL, CONVEX_CBALL] THEN
        CONJ_TAC THENL
         [MP_TAC (← ISPECL [← q r"x:real^N", ← q r"r:real"] BALL_SUBSET_CBALL) THEN
          ASM SET_TAC [],
          REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_INTER] THEN
          EXISTS_TAC (← q r"x:real^N") THEN ASM_REWRITE_TAC [CENTRE_IN_BALL]],
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [CLOSURE_APPROACHABLE]) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"r:real")) THEN
        ASM_REWRITE_TAC [← ONCE_REWRITE_RULE [DIST_SYM] (← GSYM IN_BALL)] THEN
        MP_TAC (← ISPECL [← q r"cball(p:real^N,e) DIFF f", ← q r"g(lift(&1 / &2)):real^N"]
          CONNECTED_COMPONENT_SUBSET) THEN
        ASM_REWRITE_TAC [] THEN ASM SET_TAC []],
      SUBGOAL_THEN
       (← q r"!t. t IN closure(interval(vec 0,vec 1))
            ==> (g:real^1->real^N) t IN closure h")
      MP_TAC THENL
       [MATCH_MP_TAC FORALL_IN_CLOSURE THEN REWRITE_TAC [CLOSED_CLOSURE] THEN
        SIMP_TAC [CLOSURE_OPEN_INTERVAL, UNIT_INTERVAL_NONEMPTY] THEN
        ASM_REWRITE_TAC [← GSYM path] THEN
        REWRITE_TAC [← SET_RULE
         (← q r"(!x. x IN s ==> f x IN t) <=> IMAGE f s SUBSET t")] THEN
        TRANS_TAC SUBSET_TRANS (← q r"h:real^N->bool") THEN
        REWRITE_TAC [CLOSURE_SUBSET] THEN EXPAND_TAC "h" THEN
        MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC FUN_IN_IMAGE THEN
          REWRITE_TAC [IN_INTERVAL_1, DROP_VEC, LIFT_DROP] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV,
          MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
          REWRITE_TAC [CONNECTED_INTERVAL] THEN
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC (← q r"interval[vec 0:real^1,vec 1]") THEN
          ASM_REWRITE_TAC [← GSYM path, INTERVAL_OPEN_SUBSET_CLOSED],
          REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
          SUBGOAL_THEN (← q r"cball(p:real^N,d) SUBSET cball(p,e)") MP_TAC THENL
           [ASM_REWRITE_TAC [SUBSET_BALLS, DIST_REFL] THEN ASM_REAL_ARITH_TAC,
            ASM SET_TAC []]],
          SIMP_TAC [CLOSURE_OPEN_INTERVAL, UNIT_INTERVAL_NONEMPTY] THEN
          DISCH_THEN (fun th => tactic_of do
            pure (MP_TAC (← SPEC (← q r"vec 1:real^1") th) THEN
                  MP_TAC (← SPEC (← q r"vec 0:real^1") th))) THEN
          RULE_ASSUM_TAC (REWRITE_RULE [pathstart, pathfinish]) THEN
          ASM_REWRITE_TAC [IMP_IMP, ENDS_IN_UNIT_INTERVAL] THEN
          EXPAND_TAC "j" THEN MATCH_MP_TAC MONO_AND THEN
          SIMP_TAC [IN_INTER] THEN
          CONJ_TAC THEN DISCH_TAC THEN REWRITE_TAC [IN_DIFF] THEN
          (MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
            [REWRITE_TAC [IN_CBALL, DIST_REFL] THEN ASM_REAL_ARITH_TAC,
             DISCH_TAC]) THEN
          EXPAND_TAC "h" THEN
          MATCH_MP_TAC (← MESON [CONNECTED_COMPONENT_SUBSET, SUBSET]
           (← q r"~(p IN s) ==> ~(p IN connected_component s r)")) THEN
          ASM_REWRITE_TAC [IN_DIFF] THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o GEN_REWRITE_RULE id [SUBSET]) THEN
          MATCH_MP_TAC (← SET_RULE (← q r"r x = x /\ x IN s ==> x IN IMAGE r s")) THEN
          (CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN
          ASM_MESON_TAC [PATHSTART_IN_PATH_IMAGE, PATHFINISH_IN_PATH_IMAGE,
                         pathstart, pathfinish]]])

  pure { LOCALLY_CONNECTED_FRONTIER_ANR }
/- ------------------------------------------------------------------------- -/
/- Another equivalent of an inessential mapping into C-{0}; a simple case     -/
/- where sphere maps are nullhomotopic; Janiszewski's theorem.                -/
/- (moretop.ml 7183-7476)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MOX where
  INESSENTIAL_EQ_EXTENSIBLE : thm
  INESSENTIAL_SPHEREMAP_2 : thm
  JANISZEWSKI : thm
  JANISZEWSKI_GEN : thm
  JANISZEWSKI_CONNECTED : thm
  JANISZEWSKI_DUAL : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOX [HolBase] (D : MoreTopDeps) (BMOL : MOL) (BMON : MON) (BMOO : MOO) (BMOP : MOP) (BMOS : MOS) (BMOT : MOT) : ExceptT String IO MOX := do
  -- @@SCOPE BEGIN
  let { BORSUK_MAP_INTO_SPHERE, BORSUK_MAPS_HOMOTOPIC_IN_CONNECTED_COMPONENT_EQ,
        CONTINUOUS_ON_BORSUK_MAP, .. } := BMOL
  let { SIMPLY_CONNECTED_SPHERE_EQ, .. } := BMON
  let { HOMOTOPIC_CIRCLEMAPS_DIV, INESSENTIAL_EQ_CONTINUOUS_LOGARITHM,
        INESSENTIAL_EQ_CONTINUOUS_LOGARITHM_CIRCLE, .. } := BMOO
  let { CONTINUOUS_LOGARITHM_ON_BALL, CONTINUOUS_LOGARITHM_ON_SIMPLY_CONNECTED, .. } := BMOP
  let { BORSUKIAN_SEPARATION_COMPACT, .. } := BMOS
  let { BORSUKIAN_IMP_UNICOHERENT, unicoherent, .. } := BMOT
  let { CONNECTED_COMPONENT_IN, HOMEOMORPHIC_BALL_UNIV, .. } := D.qtopology
  let { CONNECTED_COMPONENT_1_GEN, HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT,
        LOCALLY_PATH_CONNECTED_SPHERE, NULLHOMOTOPIC_INTO_CONTRACTIBLE, .. } := D.qpaths
  let { BORSUK_HOMOTOPY_EXTENSION, CONTRACTIBLE_SPHERE, OPEN_IMP_ANR, .. } := D.qdegree
  let { CEXP_ADD, CEXP_NZ, CEXP_SUB, .. } := D.ra.tsa
  let { REAL_EXP_EQ_1, .. } := D.ra.tsb
  let { PI_POS, .. } := D.ra.tse
  let { COMPLEX_EQ_CEXP, NORM_CEXP, .. } := D.ra.tsf
  let { CONTINUOUS_ON_CX_IM, CONTINUOUS_ON_CX_LIFT, .. } := D.ra.ts.knd
  let { CONTINUOUS_DISCRETE_RANGE_CONSTANT, .. } := D.ra.ts.qtopology
  let { COMPLEX_EQ, .. } := D.ra.ts.cn.cxa
  let { COMPLEX_ADD_LDISTRIB, COMPLEX_SUB_LDISTRIB, .. } := D.ra.ts.cn.cxb
  let { CX_ADD, CX_INJ, CX_SUB, IM_CX, IM_MUL_II, RE_CX, RE_MUL_II, .. } := D.ra.ts.cn.cxc
  let { COMPLEX_RING, .. } := D.ra.ts.cn.cxd
  let { COMPLEX_FIELD, .. } := D.ra.ts.cn.cxe
  let { COMPLEX_NORM_0, .. } := D.ra.ts.cn.cxf
  let { REAL_EQ_SUB_RADD, .. } := D.ra.ts.cn.qsession
  let { CONNECTED_IFF_CONNECTED_COMPONENT, .. } := D.ra.ts.cn.ms.qtopology1
  let { ARITH_RULE, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, GEOM_EQUAL_DIMENSION_RULE,
        MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_RING, SET_RULE, SET_TAC,
        .. } := D.ra.ts.cn.cx.cvx
  let { COMPACT_UNION, .. } := D.ra.ts.cn.ms.ig.qtopology
  let { COND_RAND, CONJ_ASSOC, CONTRAPOS_THM, DIMINDEX_2, DIMINDEX_GE_1, EQ_IMP,
        .. } := D.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, IMAGE_o, IMP_CONJ, IMP_CONJ_ALT, IN_DIFF, INTER_SUBSET,
        .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_INTER, IN_UNION, IN_UNIV, LE_REFL, LEFT_IMP_EXISTS_THM, MONO_EXISTS,
        NOT_IN_EMPTY, .. } := D.ra.ts.cn.cx.cvx.core3
  let { REAL_LT_01, .. } := D.ra.ts.cn.cx.cvx.core4
  let { REAL_NOT_LE, SUBSET, SUBSET_REFL, .. } := D.ra.ts.cn.cx.cvx.core5
  let { o_ASSOC, o_DEF, o_THM, .. } := D.ra.ts.cn.cx.cvx.core6
  let { EXISTS_LIFT, LIFT_EQ, LIFT_SUB, .. } := D.ra.ts.cn.cx.cvx.vec2
  let { NORM_LIFT, .. } := D.ra.ts.cn.cx.cvx.vec3
  let { SUBTOPOLOGY_UNIV, .. } := D.ra.ts.cn.cx.cvx.met
  let { BALL_SUBSET_CBALL, BOUNDED_SUBSET_BALL, CBALL_DIFF_SPHERE, CLOSED_IN,
        CLOSED_IN_CLOSED, CLOSED_INTER_COMPACT, CLOSED_SING, CLOSED_SUBSET, CLOSED_UNIV,
        .. } := D.ra.ts.cn.cx.cvx.top1
  let { COMPACT_CBALL, COMPACT_IMP_BOUNDED, COMPACT_IMP_CLOSED, COMPACT_SPHERE,
        CONNECTED_INTER_FRONTIER, .. } := D.ra.ts.cn.cx.cvx.top2
  let { CONTINUOUS_ON_ADD, CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_CONST, CONTINUOUS_ON_SUB,
        CONTINUOUS_ON_SUBSET, FRONTIER_CBALL, .. } := D.ra.ts.cn.cx.cvx.top3
  let { IN_SPHERE_0, .. } := D.ra.ts.cn.cx.cvx.top4
  let { closed, homeomorphic, homeomorphism, OPEN_UNIV, TOPSPACE_EUCLIDEAN_SUBTOPOLOGY,
        .. } := D.ra.ts.cn.cx.cvx.top5
  let { HOMOTOPIC_WITH_EQ, HOMOTOPIC_WITH_SYM, .. } := D.ra.ts.cn.ms.ig.dv.dg.qmetric
  let { COMPACT_PATH_IMAGE, CONNECTED_PATH_IMAGE, HOMOTOPIC_WITH_IMP_CONTINUOUS,
        HOMOTOPIC_WITH_IMP_SUBSET, .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths1
  let { OPEN_PATH_CONNECTED_COMPONENT, path_component, PATHFINISH_IN_PATH_IMAGE,
        PATHSTART_IN_PATH_IMAGE, .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths2
  let { BOUNDED_UNION, CONTINUOUS_ON_CASES_LOCAL, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { connected_component, HOMEOMORPHIC_SPHERES, OPEN_DIFF,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology2
  -- @@SCOPE END

  let INESSENTIAL_EQ_EXTENSIBLE ← prove
   r"!f s.
   closed s
   ==> ((?a. homotopic_with (\h. T)
              (subtopology euclidean s,
               subtopology euclidean ((:complex) DIFF {Cx(&0)}))
              f (\t. a)) <=>
        (?g. g continuous_on (:real^N) /\
             (!x. x IN s ==> g x = f x) /\ (!x. ~(g x = Cx(&0)))))"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_TAC (← q r"a:complex")) THEN
      ASM_CASES_TAC (← q r"s:real^N->bool = {}") THENL
       [EXISTS_TAC (← q r"\x:real^N. Cx(&1)") THEN
        ASM_REWRITE_TAC [CONTINUOUS_ON_CONST, NOT_IN_EMPTY] THEN
        CONV_TAC COMPLEX_RING,
        ALL_TAC] THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS) THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
      FIRST_ASSUM (MP_TAC o
        SPEC (← q r"(:real^N)") o
        MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ_ALT]
          (← REWRITE_RULE [CONJ_ASSOC] BORSUK_HOMOTOPY_EXTENSION)) o
        GEN_REWRITE_RULE id [HOMOTOPIC_WITH_SYM]) THEN
      ASM_REWRITE_TAC [← GSYM CLOSED_IN, SUBTOPOLOGY_UNIV] THEN
      SIMP_TAC [OPEN_IMP_ANR, OPEN_DIFF, OPEN_UNIV, CLOSED_SING] THEN
      ASM_SIMP_TAC [CLOSED_UNIV, CONTINUOUS_ON_CONST] THEN
      ANTS_TAC THENL [ASM SET_TAC [], MATCH_MP_TAC MONO_EXISTS] THEN
      ASM SET_TAC [],
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->complex") STRIP_ASSUME_TAC) THEN
      REWRITE_TAC [INESSENTIAL_EQ_CONTINUOUS_LOGARITHM] THEN
      MP_TAC (← ISPECL [← q r"vec 0:real^N", ← q r"&1"] HOMEOMORPHIC_BALL_UNIV) THEN
      REWRITE_TAC [REAL_LT_01, homeomorphic, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"h:real^N->real^N", ← q r"k:real^N->real^N"] THEN
      REWRITE_TAC [homeomorphism, IN_UNIV] THEN STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"(g:real^N->complex) o (h:real^N->real^N)",
                       ← q r"vec 0:real^N", ← q r"&1"] CONTINUOUS_LOGARITHM_ON_BALL) THEN
      ASM_SIMP_TAC [CONTINUOUS_ON_COMPOSE, o_THM] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"j:real^N->complex") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"(j:real^N->complex) o (k:real^N->real^N)") THEN
      ASM_SIMP_TAC [o_THM] THEN CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC []])

  -- Another simple case where sphere maps are nullhomotopic.

  let INESSENTIAL_SPHEREMAP_2 ← (do
    let lemma ← prove
     r"!f:real^N->real^2 a r.
            2 < dimindex(:N) /\
            f continuous_on sphere(a,r) /\
            IMAGE f (sphere(a,r)) SUBSET (sphere(vec 0,&1))
            ==> ?c. homotopic_with (\z. T)
                     (subtopology euclidean (sphere(a,r)),
                      subtopology euclidean (sphere(vec 0,&1)))
                     f (\x. c)"
     (REPEAT STRIP_TAC THEN
      REWRITE_TAC [INESSENTIAL_EQ_CONTINUOUS_LOGARITHM_CIRCLE] THEN
      MP_TAC (← ISPECL [← q r"f:real^N->real^2", ← q r"sphere(a:real^N,r)"]
            CONTINUOUS_LOGARITHM_ON_SIMPLY_CONNECTED) THEN
      ASM_SIMP_TAC [SIMPLY_CONNECTED_SPHERE_EQ,
                    LOCALLY_PATH_CONNECTED_SPHERE] THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [← ARITH_RULE (← q r"3 <= n <=> 2 < n")] THEN FIRST_X_ASSUM
         (MATCH_MP_TAC o MATCH_MP (← SET_RULE
            (← q r"IMAGE f s SUBSET t ==> (!x. P x ==> ~(x IN t))
            ==> !x. x IN s ==> ~P(f x)"))) THEN
        SIMP_TAC [COMPLEX_NORM_0, IN_SPHERE_0] THEN REAL_ARITH_TAC,
        DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->real^2") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"Im o (g:real^N->real^2)") THEN CONJ_TAC THENL
         [REWRITE_TAC [o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
          ASM_REWRITE_TAC [CONTINUOUS_ON_CX_IM],
          X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
          ASM_SIMP_TAC [] THEN AP_TERM_TAC THEN
          REWRITE_TAC [o_DEF, COMPLEX_EQ, RE_MUL_II, IM_MUL_II, RE_CX, IM_CX] THEN
          FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [SUBSET]) THEN
          REWRITE_TAC [FORALL_IN_IMAGE] THEN
          DISCH_THEN (MP_TAC o SPEC (← q r"x:real^N")) THEN
          ASM_SIMP_TAC [IN_SPHERE_0, NORM_CEXP, REAL_EXP_EQ_1] THEN
          REAL_ARITH_TAC]])
    let hslemma ← prove
     r"!a:real^M r b:real^N s.
          dimindex(:M) = dimindex(:N) /\ &0 < r /\ &0 < s
          ==> (sphere(a,r) homeomorphic sphere(b,s))"
     (REPEAT STRIP_TAC THEN FIRST_ASSUM (fun th => tactic_of do
        let t ← q r"?a:real^M b:real^N. ~(sphere(a,r) homeomorphic sphere(b,s))"
        pure (MP_TAC (← DISCH t (← GEOM_EQUAL_DIMENSION_RULE th (← ASSUME t))))) THEN
      ASM_SIMP_TAC [HOMEOMORPHIC_SPHERES] THEN MESON_TAC [])
    prove
     r"!f:real^M->real^N a r b s.
          2 < dimindex(:M) /\ dimindex(:N) = 2 /\
          f continuous_on sphere(a,r) /\
          IMAGE f (sphere(a,r)) SUBSET (sphere(b,s))
          ==> ?c. homotopic_with (\z. T)
                    (subtopology euclidean (sphere(a,r)),
                     subtopology euclidean (sphere(b,s))) f (\x. c)"
     (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"s <= &0") THEN
      ASM_SIMP_TAC [NULLHOMOTOPIC_INTO_CONTRACTIBLE, CONTRACTIBLE_SPHERE] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [REAL_NOT_LE]) THEN
      SUBGOAL_THEN
       (← q r"(sphere(b:real^N,s)) homeomorphic (sphere(vec 0:real^2,&1))")
      MP_TAC THENL
       [ASM_SIMP_TAC [hslemma, REAL_LT_01, DIMINDEX_2],
        REWRITE_TAC [homeomorphic, LEFT_IMP_EXISTS_THM]] THEN
      MAP_EVERY X_GEN_TAC [← q r"h:real^N->real^2", ← q r"k:real^2->real^N"] THEN
      REWRITE_TAC [homeomorphism] THEN STRIP_TAC THEN
      MP_TAC (← ISPECL
       [← q r"(h:real^N->real^2) o (f:real^M->real^N)",
        ← q r"a:real^M", ← q r"r:real"] lemma) THEN
      ASM_REWRITE_TAC [IMAGE_o] THEN ANTS_TAC THENL
       [CONJ_TAC THENL [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE, ASM SET_TAC []] THEN
        ASM_MESON_TAC [CONTINUOUS_ON_SUBSET],
        DISCH_THEN (X_CHOOSE_THEN (← q r"c:real^2") (fun th => tactic_of do
          pure (EXISTS_TAC (← q r"(k:real^2->real^N) c") THEN MP_TAC th))) THEN
        DISCH_THEN (MP_TAC o ISPEC (← q r"k:real^2->real^N") o MATCH_MP
         (← ONCE_REWRITE_RULE [IMP_CONJ] HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT)) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"sphere(b:real^N,s)")) THEN
        ASM_REWRITE_TAC [SUBSET_REFL] THEN
        MATCH_MP_TAC (← ONCE_REWRITE_RULE [IMP_CONJ_ALT] HOMOTOPIC_WITH_EQ) THEN
        REWRITE_TAC [o_DEF, TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC []]))

  -- Janiszewski's theorem.

  let JANISZEWSKI ← (do
    let lemma ← prove
     r"!s t a b:real^2.
            compact s /\ compact t /\ connected(s INTER t) /\
            connected_component ((:real^2) DIFF s) a b /\
            connected_component ((:real^2) DIFF t) a b
            ==> connected_component ((:real^2) DIFF (s UNION t)) a b"
     (REPEAT GEN_TAC THEN
      REPLICATE_TAC 3 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN (fun th => ASSUME_TAC th THEN MP_TAC th) THEN
      FIRST_X_ASSUM (CONJUNCTS_THEN (MP_TAC o
        MATCH_MP CONNECTED_COMPONENT_IN)) THEN
      REWRITE_TAC [IN_DIFF, IN_UNIV] THEN STRIP_TAC THEN STRIP_TAC THEN
      ASM_SIMP_TAC [← GSYM BORSUK_MAPS_HOMOTOPIC_IN_CONNECTED_COMPONENT_EQ,
                    DIMINDEX_2, LE_REFL, COMPACT_UNION, IN_UNION] THEN
      ONCE_REWRITE_TAC [HOMOTOPIC_CIRCLEMAPS_DIV] THEN
      REWRITE_TAC [INESSENTIAL_EQ_CONTINUOUS_LOGARITHM_CIRCLE] THEN
      ASM_SIMP_TAC [BORSUK_MAP_INTO_SPHERE, CONTINUOUS_ON_BORSUK_MAP,
                    IN_UNION] THEN
      DISCH_THEN (CONJUNCTS_THEN2
       (X_CHOOSE_THEN (← q r"g:real^2->real") STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN (← q r"h:real^2->real") STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN
       (← q r"closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) (t:real^2->bool)")
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC [CLOSED_IN_CLOSED] THEN CONJ_TAC THENL
         [EXISTS_TAC (← q r"s:real^2->bool"), EXISTS_TAC (← q r"t:real^2->bool")] THEN
        ASM_SIMP_TAC [COMPACT_IMP_CLOSED] THEN ASM SET_TAC [],
        ALL_TAC] THEN
      ASM_CASES_TAC (← q r"s INTER t:real^2->bool = {}") THENL
       [EXISTS_TAC (← q r"(\x. if x IN s then g x else h x):real^2->real") THEN
        CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
        REWRITE_TAC [o_DEF, COND_RAND] THEN
        MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
        ASM_REWRITE_TAC [← GSYM o_DEF] THEN ASM SET_TAC [],
        ALL_TAC] THEN
      MP_TAC (← ISPECL
       [← q r"\x:real^2. lift(g x) - lift(h x)", ← q r"s INTER t:real^2->bool"]
       CONTINUOUS_DISCRETE_RANGE_CONSTANT) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
          REWRITE_TAC [← GSYM CONTINUOUS_ON_CX_LIFT] THEN
          REWRITE_TAC [← GSYM o_DEF] THEN
          ASM_MESON_TAC [CONTINUOUS_ON_SUBSET, INTER_SUBSET],
          REWRITE_TAC [o_DEF]] THEN
        X_GEN_TAC (← q r"x:real^2") THEN REWRITE_TAC [IN_INTER] THEN STRIP_TAC THEN
        EXISTS_TAC (← q r"&2 * pi") THEN
        REWRITE_TAC [← REAL_ARITH (← q r"&0 < &2 * x <=> &0 < x"), PI_POS] THEN
        X_GEN_TAC (← q r"y:real^2") THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN REWRITE_TAC [REAL_NOT_LE] THEN
        REWRITE_TAC [← GSYM LIFT_SUB, LIFT_EQ, NORM_LIFT] THEN DISCH_TAC THEN
        ONCE_REWRITE_TAC [← REAL_RING (← q r"a - b:real = c - d <=> a - c = b - d")] THEN
        REWRITE_TAC [← GSYM CX_INJ] THEN
        MATCH_MP_TAC (← ExceptT.mk (COMPLEX_RING (← q r"ii * w = ii * z ==> w = z"))) THEN
        MATCH_MP_TAC COMPLEX_EQ_CEXP THEN CONJ_TAC THENL
         [REWRITE_TAC [IM_MUL_II, RE_CX] THEN ASM_REAL_ARITH_TAC,
          REWRITE_TAC [CX_SUB, COMPLEX_SUB_LDISTRIB, CEXP_SUB] THEN
          ASM_MESON_TAC []],
        REWRITE_TAC [EXISTS_LIFT, ← GSYM LIFT_SUB, LIFT_EQ, IN_INTER] THEN
        REWRITE_TAC [REAL_EQ_SUB_RADD, LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC (← q r"z:real") THEN DISCH_TAC THEN
        EXISTS_TAC (← q r"(\x. if x IN s then g x else z + h x):real^2->real") THEN
        CONJ_TAC THENL
         [REWRITE_TAC [o_DEF, COND_RAND] THEN
          MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
          ASM_SIMP_TAC [← TAUT (← q r"~(p /\ ~p)"), CX_ADD, ← GSYM o_DEF] THEN
          REWRITE_TAC [o_DEF, CX_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
          ASM_REWRITE_TAC [CONTINUOUS_ON_CONST, ← GSYM o_DEF],
          X_GEN_TAC (← q r"x:real^2") THEN REWRITE_TAC [] THEN
          COND_CASES_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
          ASM_SIMP_TAC [] THEN DISCH_TAC THEN
          SUBGOAL_THEN
           (← q r"?w:real^2. cexp(ii * Cx(h w)) = cexp (ii * Cx(z + h w))")
           (CHOOSE_THEN MP_TAC) THENL [ASM SET_TAC [], ALL_TAC] THEN
          REWRITE_TAC [CX_ADD, COMPLEX_ADD_LDISTRIB, CEXP_ADD] THEN
          REWRITE_TAC [← ExceptT.mk (COMPLEX_FIELD
                         (← q r"a = b * a <=> a = Cx(&0) \/ b = Cx(&1)")),
                       CEXP_NZ]]])
    prove
     r"!s t a b:real^2.
          compact s /\ closed t /\ connected(s INTER t) /\
          connected_component ((:real^2) DIFF s) a b /\
          connected_component ((:real^2) DIFF t) a b
          ==> connected_component ((:real^2) DIFF (s UNION t)) a b"
     (REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"?c:real^2->bool.
           compact c /\ connected c /\ a IN c /\ b IN c /\ c INTER t = {}")
      STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN (← q r"path_component((:real^2) DIFF t) a b") MP_TAC THENL
         [ASM_MESON_TAC [OPEN_PATH_CONNECTED_COMPONENT, closed, COMPACT_IMP_CLOSED],
          REWRITE_TAC [path_component, ← SET_RULE
            (← q r"s SUBSET UNIV DIFF t <=> s INTER t = {}")]] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^1->real^2") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"path_image(g:real^1->real^2)") THEN
        ASM_SIMP_TAC [CONNECTED_PATH_IMAGE, COMPACT_PATH_IMAGE] THEN
        ASM_MESON_TAC [PATHSTART_IN_PATH_IMAGE, PATHFINISH_IN_PATH_IMAGE],
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"c UNION s:real^2->bool", ← q r"vec 0:real^2"]
            BOUNDED_SUBSET_BALL) THEN
      ASM_SIMP_TAC [BOUNDED_UNION, COMPACT_IMP_BOUNDED, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"r:real") THEN STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"s:real^2->bool",
                       ← q r"(t INTER cball(vec 0,r)) UNION sphere(vec 0:real^2,r)",
                       ← q r"a:real^2", ← q r"b:real^2"] lemma) THEN
      ASM_SIMP_TAC [COMPACT_UNION, CLOSED_INTER_COMPACT,
                    COMPACT_SPHERE, COMPACT_CBALL] THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC (← q r"connected(s INTER t:real^2->bool)") THEN
          MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC,
          REWRITE_TAC [connected_component] THEN EXISTS_TAC (← q r"c:real^2->bool")] THEN
        MP_TAC (← ISPECL [← q r"vec 0:real^2", ← q r"r:real"] CBALL_DIFF_SPHERE) THEN
        ASM SET_TAC [],
        REWRITE_TAC [connected_component] THEN MATCH_MP_TAC MONO_EXISTS THEN
        X_GEN_TAC (← q r"u:real^2->bool") THEN
        SIMP_TAC [← SET_RULE (← q r"s SUBSET UNIV DIFF t <=> s INTER t = {}")] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
        MP_TAC (← ISPECL
         [← q r"u:real^2->bool", ← q r"cball(vec 0:real^2,r)"] CONNECTED_INTER_FRONTIER) THEN
        ASM_REWRITE_TAC [FRONTIER_CBALL] THEN
        MP_TAC (← ISPECL [← q r"vec 0:real^2", ← q r"r:real"] BALL_SUBSET_CBALL) THEN
        ASM SET_TAC []]))

  let JANISZEWSKI_GEN ← prove
   r"!s t a b:real^N.
        dimindex(:N) <= 2 /\
        compact s /\ closed t /\ connected(s INTER t) /\
        connected_component ((:real^N) DIFF s) a b /\
        connected_component ((:real^N) DIFF t) a b
        ==> connected_component ((:real^N) DIFF (s UNION t)) a b"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"dimindex(:N) = 1") THENL
     [ASM_SIMP_TAC [CONNECTED_COMPONENT_1_GEN] THEN SET_TAC [],
      ASM_SIMP_TAC [← ARITH_RULE (← q r"1 <= n /\ ~(n = 1) ==> (n <= 2 <=> n = 2)"),
                    DIMINDEX_GE_1] THEN
      ONCE_REWRITE_TAC [IMP_CONJ] THEN REWRITE_TAC [← GSYM DIMINDEX_2] THEN
      DISCH_THEN (fun th => tactic_of do
       pure (MATCH_ACCEPT_TAC (← GEOM_EQUAL_DIMENSION_RULE th JANISZEWSKI)))])

  let JANISZEWSKI_CONNECTED ← prove
   r"!s t:real^2->bool.
       compact s /\ closed t /\ connected(s INTER t) /\
       connected ((:real^2) DIFF s) /\ connected ((:real^2) DIFF t)
       ==> connected((:real^2) DIFF (s UNION t))"
   (REPEAT GEN_TAC THEN
    REPLICATE_TAC 3 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC [CONNECTED_IFF_CONNECTED_COMPONENT] THEN
    REWRITE_TAC [IN_DIFF, IN_UNIV, IN_UNION] THEN
    ASM_MESON_TAC [JANISZEWSKI])

  let JANISZEWSKI_DUAL ← prove
   r"!s t:real^2->bool.
        compact s /\ compact t /\ connected s /\ connected t /\
        connected((:real^2) DIFF (s UNION t))
         ==> connected(s INTER t)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"s UNION t:real^2->bool") BORSUKIAN_IMP_UNICOHERENT) THEN
    ASM_SIMP_TAC [BORSUKIAN_SEPARATION_COMPACT, COMPACT_UNION, unicoherent] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
    CONJ_TAC THEN MATCH_MP_TAC CLOSED_SUBSET THEN
    ASM_SIMP_TAC [COMPACT_IMP_CLOSED] THEN SET_TAC [])

  pure { INESSENTIAL_EQ_EXTENSIBLE, INESSENTIAL_SPHEREMAP_2, JANISZEWSKI,
         JANISZEWSKI_GEN, JANISZEWSKI_CONNECTED, JANISZEWSKI_DUAL }
/- ------------------------------------------------------------------------- -/
/- Triple-curve or "theta-curve" theorem.  Proof that there is no fourth      -/
/- component taken from Kuratowski's Topology vol 2, para 61, II.             -/
/- (moretop.ml 7477-7851)                                                   -/
/- ------------------------------------------------------------------------- -/

structure MOY where
  THETA_CURVE_INSIDE_CASES : thm
  SPLIT_INSIDE_SIMPLE_CLOSED_CURVE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMOY [HolBase] (D : MoreTopDeps) (BMOX : MOX) : ExceptT String IO MOY := do
  -- @@SCOPE BEGIN
  let { JANISZEWSKI_CONNECTED, .. } := BMOX
  let { CLOPEN_IN_COMPONENTS, CLOSED_IN_INTER_CLOSURE, COBOUNDED_IMP_UNBOUNDED,
        CONNECTED_COMPONENT_EQ, IN_COMPONENTS_MAXIMAL, .. } := D.qtopology
  let { ARC_REVERSEPATH, ARC_REVERSEPATH_EQ, CONNECTED_SIMPLE_PATH_ENDLESS,
        CONNECTED_SIMPLE_PATH_IMAGE, INSIDE_INTER_OUTSIDE, INSIDE_NO_OVERLAP,
        INSIDE_OUTSIDE, JORDAN_INSIDE_OUTSIDE, NONEMPTY_SIMPLE_PATH_ENDLESS, OUTSIDE,
        OUTSIDE_IN_COMPONENTS, OUTSIDE_INSIDE, OUTSIDE_NO_OVERLAP,
        OUTSIDE_UNION_OUTSIDE_UNION, SIMPLE_PATH_IMP_ARC, SIMPLE_PATH_JOIN_LOOP,
        SIMPLE_PATH_JOIN_LOOP_EQ, SIMPLE_PATH_REVERSEPATH, UNION_WITH_INSIDE,
        .. } := D.qpaths
  let { CONNECTED_COMPONENT_TRANS, .. } := D.ra.ts.cn.ms.qtopology1
  let { ASM_MESON_TAC, MESON, SET_RULE, SET_TAC, .. } := D.ra.ts.cn.cx.cvx
  let { CONJ_ASSOC, CONTRAPOS_THM, EQ_IMP, EXTENSION, .. } := D.ra.ts.cn.cx.cvx.core1
  let { IMP_CONJ_ALT, IN, IN_DIFF, .. } := D.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_UNION, IN_UNIV, LEFT_IMP_EXISTS_THM, NOT_IMP,
        .. } := D.ra.ts.cn.cx.cvx.core3
  let { SUBSET, SUBSET_ANTISYM, SUBSET_REFL, .. } := D.ra.ts.cn.cx.cvx.core5
  let { UNION_COMM, .. } := D.ra.ts.cn.cx.cvx.core6
  let { DIST_SYM, .. } := D.ra.ts.cn.cx.cvx.vec1
  let { CLOSED_CLOSURE, CLOSURE_APPROACHABLE, .. } := D.ra.ts.cn.cx.cvx.top1
  let { COMPACT_CLOSURE, COMPONENTS_MAXIMAL, CONNECTED_INTER_FRONTIER,
        .. } := D.ra.ts.cn.cx.cvx.top2
  let { IN_BALL, IN_COMPONENTS_NONEMPTY, IN_COMPONENTS_SUBSET, OPEN_CONTAINS_BALL,
        .. } := D.ra.ts.cn.cx.cvx.top4
  let { connected, frontier, OPEN_SUBSET, .. } := D.ra.ts.cn.cx.cvx.top5
  let { COMPONENTS_NONOVERLAP, .. } := D.ra.ts.cn.ms.ig.dv.qtopology1
  let { ARC_IMP_PATH, ARC_IMP_SIMPLE_PATH, CONNECTED_PATH_IMAGE,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths1
  let { PATH_IMAGE_JOIN, PATH_IMAGE_REVERSEPATH, PATHFINISH_JOIN, PATHFINISH_REVERSEPATH,
        PATHSTART_JOIN, PATHSTART_REVERSEPATH, SIMPLE_PATH_IMP_PATH,
        .. } := D.ra.ts.cn.ms.ig.dv.dg.qpaths2
  let { COMPL_COMPL, .. } := D.ra.ts.cn.ms.ig.dv.dg.qsession
  let { BOUNDED_UNION, CLOSURE_UNION_FRONTIER, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { connected_component, .. } := D.ra.ts.cn.ms.ig.dv.dg.qtopology2
  let { BOUNDED_CLOSURE_EQ, .. } := D.ra.ts.cn.ms.ig.dv.dg.pt.qtop
  -- @@SCOPE END

  -- `last o CONJUNCTS` as a theorem function.
  let lastc : thm → ExceptT String IO thm := fun th =>
    liftExcept (HolCore.Lib.last (CONJUNCTS th))

  let THETA_CURVE_INSIDE_CASES ← prove
   r"!c1 c2 c3 a b:real^2.
        arc c1 /\ pathstart c1 = a /\ pathfinish c1 = b /\
        arc c2 /\ pathstart c2 = a /\ pathfinish c2 = b /\
        arc c3 /\ pathstart c3 = a /\ pathfinish c3 = b /\
        path_image c1 INTER path_image c2 = {a,b} /\
        path_image c2 INTER path_image c3 = {a,b} /\
        path_image c3 INTER path_image c1 = {a,b}
        ==> path_image c1 DIFF {a,b} SUBSET
            inside(path_image c2 UNION path_image c3) \/
            path_image c2 DIFF {a,b} SUBSET
            inside(path_image c3 UNION path_image c1) \/
            path_image c3 DIFF {a,b} SUBSET
            inside(path_image c1 UNION path_image c2)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"c3 ++ reversepath c1:real^1->real^2")
      JORDAN_INSIDE_OUTSIDE) THEN
    MP_TAC (← ISPEC (← q r"c2 ++ reversepath c3:real^1->real^2")
      JORDAN_INSIDE_OUTSIDE) THEN
    MP_TAC (← ISPEC (← q r"c1 ++ reversepath c2:real^1->real^2")
     JORDAN_INSIDE_OUTSIDE) THEN
    ASM_SIMP_TAC [PATHSTART_JOIN, PATHFINISH_JOIN,
                  PATHSTART_REVERSEPATH, PATHFINISH_REVERSEPATH,
                  SIMPLE_PATH_JOIN_LOOP_EQ, ARC_REVERSEPATH_EQ,
                  PATH_IMAGE_REVERSEPATH, SUBSET_REFL, PATH_IMAGE_JOIN,
                  PATH_IMAGE_REVERSEPATH] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC [← TAUT (← q r"p \/ q <=> ~(~p /\ ~q)")] THEN
    REWRITE_TAC [← SET_RULE (← q r"s SUBSET t <=> s DIFF t = {}")] THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN
     (MP_TAC o MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ_ALT]
          (← REWRITE_RULE [CONJ_ASSOC] CONNECTED_INTER_FRONTIER)))) THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [← TAUT (← q r"p /\ ~q ==> ~r <=> p /\ r ==> q")] THEN
    PURE_ONCE_REWRITE_TAC [← TAUT (← q r"~p <=> p ==> F")] THEN
    REPEAT (ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      ASM_MESON_TAC [CONNECTED_SIMPLE_PATH_ENDLESS, ARC_IMP_SIMPLE_PATH],
      DISCH_TAC]) THEN
    SUBGOAL_THEN
     (← q r"inside(path_image c1 UNION path_image c2:real^2->bool) IN
      components((:real^2) DIFF
                 (path_image c1 UNION path_image c2 UNION path_image c3)) /\
      inside(path_image c2 UNION path_image c3:real^2->bool) IN
      components((:real^2) DIFF
                 (path_image c1 UNION path_image c2 UNION path_image c3)) /\
      inside(path_image c3 UNION path_image c1:real^2->bool) IN
      components((:real^2) DIFF
                 (path_image c1 UNION path_image c2 UNION path_image c3))")
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC CLOPEN_IN_COMPONENTS THEN
      ASM_REWRITE_TAC [] THEN
      (CONJ_TAC THENL
        [ASM_REWRITE_TAC [CLOSED_IN_INTER_CLOSURE, CLOSURE_UNION_FRONTIER],
         MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC []]) THEN
      ASM SET_TAC [],
      ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"closure(inside(path_image c1 UNION path_image c2)):real^2->bool",
      ← q r"closure(inside(path_image c2 UNION path_image c3)):real^2->bool"]
     JANISZEWSKI_CONNECTED) THEN
    ASM_REWRITE_TAC [COMPACT_CLOSURE, CLOSED_CLOSURE, NOT_IMP] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC (← ISPEC (← q r"c2:real^1->real^2") CONNECTED_PATH_IMAGE) THEN
      ASM_SIMP_TAC [ARC_IMP_PATH] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      ASM_REWRITE_TAC [CLOSURE_UNION_FRONTIER] THEN MATCH_MP_TAC (← SET_RULE
       (← q r"i INTER (c1 UNION c2 UNION c3) = {} /\
        j INTER (c1 UNION c2 UNION c3) = {} /\
        i INTER j = {} /\ c1 INTER c3 SUBSET c2
        ==> c2 = (i UNION c1 UNION c2) INTER (j UNION c2 UNION c3)")) THEN
      REPEAT CONJ_TAC THENL
       [REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
        SET_TAC [],
        REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET)) THEN
        SET_TAC [],
        MP_TAC (← ISPEC (← q r"(:real^2) DIFF
                 (path_image c1 UNION path_image c2 UNION path_image c3)")
          COMPONENTS_NONOVERLAP) THEN
        ASM_SIMP_TAC [] THEN DISCH_THEN (K ALL_TAC) THEN
        DISCH_THEN (MP_TAC o AP_TERM (← q r"frontier:(real^2->bool)->real^2->bool")) THEN
        ASM_REWRITE_TAC [] THEN
        MP_TAC (← ISPEC (← q r"c1:real^1->real^2") NONEMPTY_SIMPLE_PATH_ENDLESS) THEN
        ASM_SIMP_TAC [ARC_IMP_SIMPLE_PATH] THEN ASM SET_TAC [],
        ASM SET_TAC []],
      UNDISCH_TAC
       (← q r"connected(outside(path_image c1 UNION path_image c2):real^2->bool)") THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      ASM_REWRITE_TAC [CLOSURE_UNION_FRONTIER] THEN ASM SET_TAC [],
      UNDISCH_TAC
       (← q r"connected(outside(path_image c2 UNION path_image c3):real^2->bool)") THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      ASM_REWRITE_TAC [CLOSURE_UNION_FRONTIER] THEN ASM SET_TAC [],
      MP_TAC (← ASSUME
       (← q r"inside(path_image c3 UNION path_image c1:real^2->bool) IN
        components((:real^2) DIFF
                   (path_image c1 UNION path_image c2 UNION path_image c3))")) THEN
      REWRITE_TAC [IN_COMPONENTS_MAXIMAL] THEN
      DISCH_THEN (MP_TAC o lastc) THEN
      MATCH_MP_TAC (← MESON []
       (← q r"R s /\ ~(s = i) /\ P s /\ Q s
        ==> (!c. P c /\ Q c /\ R c /\ connected c ==> c = i)
        ==> ~connected s")) THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC [CLOSURE_UNION_FRONTIER] THEN ASM SET_TAC [], ALL_TAC] THEN
      CONJ_TAC THENL
       [DISCH_THEN (MP_TAC o AP_TERM (← q r"bounded:(real^2->bool)->bool")) THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC COBOUNDED_IMP_UNBOUNDED THEN
        REWRITE_TAC [COMPL_COMPL] THEN
        ASM_REWRITE_TAC [BOUNDED_UNION, BOUNDED_CLOSURE_EQ],
        ALL_TAC] THEN
      ASM_REWRITE_TAC [CLOSURE_UNION_FRONTIER, ← SET_RULE
       (← q r"(i UNION c1 UNION c2) UNION (j UNION c2 UNION c3) =
        (i UNION j) UNION (c1 UNION c2 UNION c3)")] THEN
      MATCH_MP_TAC (← SET_RULE
       (← q r"i3 SUBSET UNIV DIFF c /\
        ~(i3 = {}) /\ i1 INTER i3 = {} /\ i2 INTER i3 = {}
        ==> ~(UNIV DIFF ((i1 UNION i2) UNION c) = {}) /\
            i3 SUBSET UNIV DIFF ((i1 UNION i2) UNION c)")) THEN
      ASM_SIMP_TAC [IN_COMPONENTS_SUBSET, IN_COMPONENTS_NONEMPTY] THEN
      MP_TAC (← ISPEC (← q r"(:real^2) DIFF
                    (path_image c1 UNION path_image c2 UNION path_image c3)")
      COMPONENTS_NONOVERLAP) THEN
      ASM_SIMP_TAC [] THEN DISCH_THEN (K ALL_TAC) THEN CONJ_TAC THEN
      DISCH_THEN (MP_TAC o AP_TERM (← q r"frontier:(real^2->bool)->real^2->bool")) THEN
      ASM_REWRITE_TAC [] THEN
      MP_TAC (← ISPEC (← q r"c2:real^1->real^2") NONEMPTY_SIMPLE_PATH_ENDLESS) THEN
      ASM_SIMP_TAC [ARC_IMP_SIMPLE_PATH] THEN ASM SET_TAC []])

  -- The two symmetric halves of the "inside SUBSET outside" step below.
  let insideOutsideTac (ci cj : String) : ExceptT String IO tactic := do
    let pc (s : String) : ExceptT String IO term :=
      q (s.replace "CI" ci |>.replace "CJ" cj)
    pure (SUBGOAL_THEN (← pc r"?z:real^2. z IN path_image CI /\
                                 z IN outside(path_image CJ UNION path_image c)")
        (CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THENL
         [REWRITE_TAC [OUTSIDE_INSIDE, IN_DIFF, IN_UNION, IN_UNIV] THEN
          MP_TAC (← ISPEC (← pc r"CI:real^1->real^2") NONEMPTY_SIMPLE_PATH_ENDLESS) THEN
          ASM_REWRITE_TAC [] THEN ASM SET_TAC [],
          ALL_TAC] THEN
        DISCH_THEN (fun th => ASSUME_TAC th THEN MP_TAC th) THEN
        REWRITE_TAC [OUTSIDE, IN_ELIM_THM, CONTRAPOS_THM] THEN
        MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
        MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN REWRITE_TAC [IN] THEN
        MP_TAC (← ASSUME
         (← pc r"open(outside(path_image CJ UNION path_image c):real^2->bool)")) THEN
        REWRITE_TAC [OPEN_CONTAINS_BALL] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"z:real^2")) THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"e:real") STRIP_ASSUME_TAC) THEN
        MP_TAC (← ASSUME
         (← pc r"frontier(inside(path_image CI UNION path_image c):real^2->bool) =
          path_image CI UNION path_image c")) THEN
        GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"z:real^2")) THEN REWRITE_TAC [frontier] THEN
        ASM_SIMP_TAC [IN_UNION, IN_DIFF, CLOSURE_APPROACHABLE, IN_ELIM_THM] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"e:real") o CONJUNCT1) THEN
        ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC (← q r"w:real^2") THEN STRIP_TAC THEN
        MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN EXISTS_TAC (← q r"w:real^2") THEN
        REWRITE_TAC [connected_component] THEN CONJ_TAC THENL
         [EXISTS_TAC
           (← pc r"outside(path_image CJ UNION path_image c:real^2->bool)") THEN
          ASM_REWRITE_TAC [← SET_RULE (← q r"s SUBSET UNIV DIFF t <=> s INTER t = {}"),
                           OUTSIDE_NO_OVERLAP] THEN
          FIRST_X_ASSUM (MATCH_MP_TAC o GEN_REWRITE_RULE id [SUBSET]) THEN
          ASM_REWRITE_TAC [← ONCE_REWRITE_RULE [DIST_SYM] IN_BALL],
          EXISTS_TAC (← pc r"inside(path_image CI UNION path_image c:real^2->bool)") THEN
          ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC (← SET_RULE
           (← pc r"inside(CI UNION c) INTER (CI UNION c) = {} /\
            CJ INTER inside(CI UNION c) = {}
            ==> inside(CI UNION c) SUBSET UNIV DIFF (CJ UNION c)")) THEN
          ASM_REWRITE_TAC [INSIDE_NO_OVERLAP]])

  let SPLIT_INSIDE_SIMPLE_CLOSED_CURVE ← prove
   r"!c1 c2 c a b:real^2.
        ~(a = b) /\
        simple_path c1 /\ pathstart c1 = a /\ pathfinish c1 = b /\
        simple_path c2 /\ pathstart c2 = a /\ pathfinish c2 = b /\
        simple_path c /\ pathstart c = a /\ pathfinish c = b /\
        path_image c1 INTER path_image c2 = {a,b} /\
        path_image c1 INTER path_image c = {a,b} /\
        path_image c2 INTER path_image c = {a,b} /\
        ~(path_image c INTER inside(path_image c1 UNION path_image c2) = {})
        ==> inside(path_image c1 UNION path_image c) INTER
            inside(path_image c2 UNION path_image c) = {} /\
            inside(path_image c1 UNION path_image c) UNION
            inside(path_image c2 UNION path_image c) UNION
            (path_image c DIFF {a,b}) =
            inside(path_image c1 UNION path_image c2)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MAP_EVERY (MP_TAC o C ISPEC JORDAN_INSIDE_OUTSIDE)
     [← q r"(c1 ++ reversepath c2):real^1->real^2",
      ← q r"(c1 ++ reversepath c):real^1->real^2",
      ← q r"(c2 ++ reversepath c):real^1->real^2"] THEN
    ASM_SIMP_TAC [PATHSTART_JOIN, PATHFINISH_JOIN,
                  PATHSTART_REVERSEPATH, PATHFINISH_REVERSEPATH,
                  SIMPLE_PATH_JOIN_LOOP, SIMPLE_PATH_IMP_ARC,
                  PATH_IMAGE_JOIN, SIMPLE_PATH_IMP_PATH, PATH_IMAGE_REVERSEPATH,
                  SIMPLE_PATH_REVERSEPATH, ARC_REVERSEPATH,
                  SUBSET_REFL] THEN
    REPLICATE_TAC 3 STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"path_image(c:real^1->real^2) INTER
      outside(path_image c1 UNION path_image c2) = {}")
    ASSUME_TAC THENL
     [MATCH_MP_TAC (← TAUT (← q r"(~p ==> F) ==> p")) THEN DISCH_TAC THEN
      SUBGOAL_THEN
       (← q r"connected(path_image(c:real^1->real^2) DIFF
                  {pathstart c,pathfinish c})")
      MP_TAC THENL [ASM_SIMP_TAC [CONNECTED_SIMPLE_PATH_ENDLESS], ALL_TAC] THEN
      ASM_REWRITE_TAC [connected] THEN
      MAP_EVERY EXISTS_TAC
       [← q r"inside(path_image c1 UNION path_image c2):real^2->bool",
        ← q r"outside(path_image c1 UNION path_image c2):real^2->bool"] THEN
      ASM_REWRITE_TAC [] THEN ASM SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"outside(path_image c1 UNION path_image c2) SUBSET
      outside(path_image c1 UNION path_image (c:real^1->real^2)) /\
      outside(path_image c1 UNION path_image c2) SUBSET
      outside(path_image c2 UNION path_image c)")
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ALL_TAC, GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [UNION_COMM]] THEN
      MATCH_MP_TAC OUTSIDE_UNION_OUTSIDE_UNION THEN ASM_REWRITE_TAC [] THEN
      ONCE_REWRITE_TAC [UNION_COMM] THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"path_image(c1:real^1->real^2) INTER
      inside(path_image c2 UNION path_image c) = {}")
    ASSUME_TAC THENL
     [MATCH_MP_TAC (← TAUT (← q r"(~p ==> F) ==> p")) THEN DISCH_TAC THEN
      SUBGOAL_THEN
       (← q r"frontier(outside(path_image c1 UNION path_image c2)):real^2->bool =
        frontier(outside(path_image c2 UNION path_image c))")
      MP_TAC THENL
       [AP_TERM_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC [] THEN
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [UNION_COMM] THEN
        MATCH_MP_TAC OUTSIDE_UNION_OUTSIDE_UNION THEN
        MATCH_MP_TAC (← TAUT (← q r"(~p ==> F) ==> p")) THEN DISCH_TAC THEN
        SUBGOAL_THEN
         (← q r"connected(path_image(c1:real^1->real^2) DIFF
                    {pathstart c1,pathfinish c1})")
        MP_TAC THENL [ASM_SIMP_TAC [CONNECTED_SIMPLE_PATH_ENDLESS], ALL_TAC] THEN
        ASM_REWRITE_TAC [connected] THEN
        MAP_EVERY EXISTS_TAC
         [← q r"inside(path_image c2 UNION path_image c):real^2->bool",
          ← q r"outside(path_image c2 UNION path_image c):real^2->bool"] THEN
        ASM_REWRITE_TAC [] THEN ASM SET_TAC [],
        MP_TAC (← ISPEC (← q r"c:real^1->real^2") NONEMPTY_SIMPLE_PATH_ENDLESS) THEN
        ASM_REWRITE_TAC [] THEN ASM SET_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"path_image(c2:real^1->real^2) INTER
      inside(path_image c1 UNION path_image c) = {}")
    ASSUME_TAC THENL
     [MATCH_MP_TAC (← TAUT (← q r"(~p ==> F) ==> p")) THEN DISCH_TAC THEN
      SUBGOAL_THEN
       (← q r"frontier(outside(path_image c1 UNION path_image c2)):real^2->bool =
        frontier(outside(path_image c1 UNION path_image c))")
      MP_TAC THENL
       [AP_TERM_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC OUTSIDE_UNION_OUTSIDE_UNION THEN
        MATCH_MP_TAC (← TAUT (← q r"(~p ==> F) ==> p")) THEN DISCH_TAC THEN
        SUBGOAL_THEN
         (← q r"connected(path_image(c2:real^1->real^2) DIFF
                    {pathstart c2,pathfinish c2})")
        MP_TAC THENL [ASM_SIMP_TAC [CONNECTED_SIMPLE_PATH_ENDLESS], ALL_TAC] THEN
        ASM_REWRITE_TAC [connected] THEN
        MAP_EVERY EXISTS_TAC
         [← q r"inside(path_image c1 UNION path_image c):real^2->bool",
          ← q r"outside(path_image c1 UNION path_image c):real^2->bool"] THEN
        ASM_REWRITE_TAC [] THEN ASM SET_TAC [],
        MP_TAC (← ISPEC (← q r"c:real^1->real^2") NONEMPTY_SIMPLE_PATH_ENDLESS) THEN
        ASM_REWRITE_TAC [] THEN ASM SET_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"inside(path_image c1 UNION path_image (c:real^1->real^2)) SUBSET
      inside(path_image c1 UNION path_image c2) /\
      inside(path_image c2 UNION path_image (c:real^1->real^2)) SUBSET
      inside(path_image c1 UNION path_image c2)")
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN REWRITE_TAC [INSIDE_OUTSIDE] THEN
      REWRITE_TAC [← SET_RULE (← q r"UNIV DIFF t SUBSET UNIV DIFF s <=> s SUBSET t")] THENL
       [ALL_TAC, GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [UNION_COMM]] THEN
      MATCH_MP_TAC (← SET_RULE
       (← q r"out1 SUBSET out2 /\ c2 DIFF (c1 UNION c) SUBSET out2
        ==> (c1 UNION c2) UNION out1 SUBSET (c1 UNION c) UNION out2")) THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [OUTSIDE_INSIDE] THEN ASM SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"inside(path_image c1 UNION path_image c :real^2->bool) SUBSET
      outside(path_image c2 UNION path_image c) /\
      inside(path_image c2 UNION path_image c) SUBSET
      outside(path_image c1 UNION path_image c)")
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [SUBSET] THEN CONJ_TAC THEN
      X_GEN_TAC (← q r"x:real^2") THEN DISCH_TAC THENL
       [← insideOutsideTac "c1" "c2",
        ← insideOutsideTac "c2" "c1"],
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC (← SET_RULE
       (← q r"!u. s SUBSET u /\ t INTER u = {} ==> s INTER t = {}")) THEN
      EXISTS_TAC (← q r"outside(path_image c2 UNION path_image c):real^2->bool") THEN
      ASM_REWRITE_TAC [INSIDE_INTER_OUTSIDE],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"outside (path_image c1 UNION path_image c) INTER
      outside (path_image c2 UNION path_image c):real^2->bool
      SUBSET outside (path_image c1 UNION path_image c2)")
    MP_TAC THENL
     [ALL_TAC,
      ONCE_REWRITE_TAC [← SET_RULE (← q r"s INTER t = u <=>
                          (UNIV DIFF s) UNION (UNIV DIFF t) = UNIV DIFF u")] THEN
      REWRITE_TAC [← GSYM UNION_WITH_INSIDE] THEN ASM SET_TAC []] THEN
    MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC (← q r"(:real^2) DIFF (path_image c1 UNION path_image c2)") THEN
    MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC [OUTSIDE_IN_COMPONENTS], DISCH_TAC] THEN
    CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
    MP_TAC (← ISPECL
     [← q r"closure(inside(path_image c1 UNION path_image c)):real^2->bool",
      ← q r"closure(inside(path_image c2 UNION path_image c)):real^2->bool"]
     JANISZEWSKI_CONNECTED) THEN
    ASM_REWRITE_TAC [COMPACT_CLOSURE, CLOSED_CLOSURE] THEN
    ASM_REWRITE_TAC [CLOSURE_UNION_FRONTIER,
                     COMPL_COMPL,
                     ← ONCE_REWRITE_RULE [UNION_COMM] UNION_WITH_INSIDE] THEN
    REWRITE_TAC [← SET_RULE
     (← q r"UNIV DIFF ((UNIV DIFF s) UNION (UNIV DIFF t)) = s INTER t")] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN (← q r"connected(path_image c:real^2->bool)") MP_TAC THENL
     [ASM_SIMP_TAC [CONNECTED_SIMPLE_PATH_IMAGE], ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [← GSYM UNION_WITH_INSIDE] THEN ASM SET_TAC [])

  pure { THETA_CURVE_INSIDE_CASES, SPLIT_INSIDE_SIMPLE_CLOSED_CURVE }

end HolMultiLib.MoreTop
