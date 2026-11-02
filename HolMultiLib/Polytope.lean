/- ========================================================================= -/
/- Faces, extreme points, polytopes, polyhedra etc.                          -/
/- ========================================================================= -/
/- File: HolMultiLib/Polytope.lean

  Original (c) Copyright, John Harrison 2010.
  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/polytope.ml`, in the style of
  HolMultiLib/Paths.lean: pure, the proofs translated by hand, one `let` per
  OCaml `let`, in file order.  The load-time effects (`parse_as_infix`) are at
  their file positions.  What polytope.ml uses from earlier files is passed in
  `PolytopeDeps`: everything convex.ml already used comes in its `ConvexDeps`
  (field `cvx`), and the rest in the Q*Thms groups and the procedure fields.
  SessionMultiLib/Polytope.lean supplies it.
-/

import HolMultiLib.Paths

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolMultiLib.Polytope

open HolMultiLib.Convex (ConvexDeps)

/- The theorems polytope.ml uses that convex.ml's deps do not carry, grouped
   by the file that proves them. -/

structure QSesThms where
  (CARD_IMAGE_LE DELETE_INSERT DELETE_SUBSET DISJOINT_EMPTY DISJOINT_INSERT DISJ_ACI
   EMPTY_DELETE EMPTY_UNION EXISTS_FINITE_SUBSET_IMAGE EXISTS_IN_UNION EXISTS_IN_UNIONS
   EXISTS_UNIQUE_DEF FINITE_FINITE_PREIMAGE FINITE_PCROSS FINITE_PRODUCT_DEPENDENT
   HAS_SIZE_POWERSET IMAGE_FSTCART_PCROSS IMAGE_SNDCART_PCROSS INJECTIVE_IMAGE
   INTER_ASSOC INT_ADD_LID INT_LTE_TRANS INT_LT_IMP_LE INT_LT_IMP_NE INT_LT_REFL
   INT_NOT_LE INT_SUB_RZERO NUM_OF_INT_OF_NUM PASTECART_EQ PCROSS_EQ PSUBSET_ALT
   PSUBSET_IRREFL REAL_BOUNDS_LE REAL_EQ_MUL_LCANCEL REAL_LET_ADD2 REAL_LE_INF_FINITE
   REAL_LE_RCANCEL_IMP REAL_LTE_ADD2 REAL_LT_RCANCEL_IMP REAL_LT_RMUL REAL_SUP_LE
   REAL_WLOG_LT SING_GSPEC SUBSET_INTER_ABSORPTION SUM_BOUND_GEN SURJECTIVE_IMAGE
   UNIONS_1 UNION_ACI UNION_OVER_INTER num_RECURSION num_WF real_sub : thm)
  deriving Inhabited

structure QVecThms where
  (ADJOINT_CLAUSES ADJOINT_LINEAR ADJOINT_SURJECTIVE ADJOINT_WORKS BETWEEN_ANTISYM
   BETWEEN_TRANS DIM_EQ_0 DIM_ORTHOGONAL_SUM DOT_1 DOT_LMUL_MATRIX DOT_PASTECART
   DROP_NEG FSTCART_VEC HYPERPLANE_EQ_EMPTY INDEPENDENT_IMP_FINITE LINEAR_NEGATION
   LINEAR_SURJECTIVE_RIGHT_INVERSE MATRIX_VECTOR_MUL_RZERO MIDPOINT_REFL
   NORM_TRIANGLE_LT PASTECART_EQ_VEC QUANTIFY_SURJECTION_THM SNDCART_VEC SPAN_2
   VECTOR_EQ VECTOR_MATRIX_MUL_TRANSP VECTOR_NEG_0 VEC_EQ between : thm)
  deriving Inhabited

structure QMiscThms where
  (HULL_INSERT HULL_UNION_RIGHT : thm)
  deriving Inhabited

structure QCardThms where
  (FINITE_IMP_COUNTABLE : thm)
  deriving Inhabited

structure QFloorThms where
  (FINITE_INTSEG INTEGER_EXISTS_BETWEEN_ABS_LT : thm)
  deriving Inhabited

structure QMetThms where
  (OPEN_IN_SUBTOPOLOGY_EMPTY OPEN_IN_UNIONS : thm)
  deriving Inhabited

structure QTopThms where
  (BAIRE BALL_SCALING BOUNDED_CLOSURE_EQ BOUNDED_INTER BOUNDED_INTERIOR BOUNDED_INTERVAL
   BOUNDED_PCROSS BOUNDED_UNIONS CLOSED_HALFSPACE_LE CLOSED_INJECTIVE_LINEAR_IMAGE_EQ
   CLOSED_IN_REFL CLOSED_PCROSS_EQ CLOSED_UNIONS CLOSURE_INSERT
   CLOSURE_INTERIOR_UNION_CLOSED COMPACT_EQ_HEINE_BOREL COMPACT_TRANSLATION_EQ
   CONTINUOUS_AT_LIFT_DOT CONTINUOUS_CLOSED_PREIMAGE CONTINUOUS_CMUL DIAMETER_LE
   FRONTIER_HALFSPACE_LE HAUSDIST_INSERT_LE HAUSDIST_REFL INTERIOR_HALFSPACE_LE
   IN_OPEN_SEGMENT_ALT NOWHERE_DENSE_COUNTABLE_UNIONS_CLOSED OPEN_INTERS OPEN_IN_DELETE
   OPEN_SEGMENT_LINEAR_IMAGE PROPER_MAP REAL_HAUSDIST_LE_EQ REAL_LE_SETDIST
   REAL_LE_SETDIST_EQ REGULAR_CLOSED_UNIONS SETDIST_EQ_0_SING SETDIST_FRONTIER
   SETDIST_HAUSDIST_TRIANGLE SETDIST_SINGS SETDIST_SING_FRONTIER SETDIST_SING_IN_SET
   SETDIST_SING_LE_HAUSDIST SETDIST_TRIANGLE SUBSET_BALL : thm)
  deriving Inhabited

structure QCvxThms1 where
  (AFFINE_AFFINE_HULL AFFINE_ALT AFFINE_BOUNDED_EQ_TRIVIAL AFFINE_DEPENDENT_MONO
   AFFINE_HULLS_EQ AFFINE_HULL_0_2_EXPLICIT AFFINE_HULL_3 AFFINE_HULL_CLOSURE
   AFFINE_HULL_CONIC_HULL AFFINE_HULL_CONVEX_HULL AFFINE_HULL_EMPTY AFFINE_HULL_EQ
   AFFINE_HULL_EQ_EMPTY AFFINE_HULL_EQ_SPAN AFFINE_HULL_EXPLICIT AFFINE_HULL_FINITE
   AFFINE_HULL_FINITE_INTERSECTION_HYPERPLANES AFFINE_HULL_SING AFFINE_HYPERPLANE
   AFFINE_IMP_CONVEX AFFINE_INDEPENDENT_1 AFFINE_INDEPENDENT_2 AFFINE_INDEPENDENT_EMPTY
   AFFINE_INDEPENDENT_IFF_CARD AFFINE_INDEPENDENT_IMP_FINITE AFFINE_INDEPENDENT_INSERT
   AFFINE_INDEPENDENT_SUBSET AFFINE_PARALLEL_SLICE AFFINE_SING AFFINE_SPAN AFFINE_UNIV
   AFF_DIM_AFFINE_HULL AFF_DIM_AFFINE_INDEPENDENT AFF_DIM_AFFINE_INTER_HYPERPLANE
   AFF_DIM_CONVEX_HULL AFF_DIM_DIM_0 AFF_DIM_EMPTY AFF_DIM_EQ_0 AFF_DIM_EQ_AFFINE_HULL
   AFF_DIM_EQ_FULL AFF_DIM_EQ_MINUS1 AFF_DIM_GE AFF_DIM_HALFSPACE_GE
   AFF_DIM_HALFSPACE_LE AFF_DIM_HYPERPLANE AFF_DIM_INSERT AFF_DIM_LE_CARD
   AFF_DIM_LE_UNIV AFF_DIM_NONEMPTY_INTERIOR AFF_DIM_POS_LE AFF_DIM_SEGMENT AFF_DIM_SING
   AFF_DIM_SUBSET AFF_DIM_UNIV BOUNDED_CONVEX_HULL BOUNDED_CONVEX_HULL_EQ
   CARATHEODORY_AFF_DIM CLOSED_AFFINE CLOSED_AFFINE_HULL CLOSED_INTERVAL_AS_CONVEX_HULL
   CLOSED_RELATIVE_FRONTIER CLOSURE_CONVEX_HULL CLOSURE_SEGMENT
   CLOSURE_SUBSET_AFFINE_HULL COLLINEAR_3_EQ_AFFINE_DEPENDENT COLLINEAR_AFF_DIM
   COMPACT_CONVEX_COLLINEAR_SEGMENT : thm)
  deriving Inhabited

structure QCvxThms2 where
  (COMPACT_CONVEX_HULL COMPACT_SEGMENT CONIC_CONIC_HULL CONIC_CONTAINS_0
   CONIC_CONVEX_CONE_HULL CONIC_HULL_AS_IMAGE CONIC_HULL_CONTAINS_0 CONIC_HULL_EMPTY
   CONIC_HULL_EQ_AFFINE_HULL CONIC_HULL_EQ_EMPTY CONIC_HULL_EQ_SING CONIC_HULL_EQ_SPAN
   CONIC_HULL_EQ_SPAN_EQ CONIC_HULL_EXPLICIT CONIC_HULL_INTER_AFFINE_HULL
   CONIC_HULL_SUBSET_SPAN CONIC_IMAGE_MULTIPLE CONIC_SPAN CONIC_UNIV
   CONNECTED_INTER_RELATIVE_FRONTIER CONVEX_ALT CONVEX_BALL CONVEX_CBALL CONVEX_CLOSURE
   CONVEX_CLOSURE_INTERIOR CONVEX_CONE_CONVEX_CONE_HULL CONVEX_CONE_HALFSPACE_LE
   CONVEX_CONE_HULL_ADD CONVEX_CONE_HULL_CONTAINS_0
   CONVEX_CONE_HULL_CONVEX_HULL_NONEMPTY CONVEX_CONE_HULL_EMPTY
   CONVEX_CONE_HULL_LINEAR_IMAGE CONVEX_CONE_HULL_MUL CONVEX_CONE_HULL_SEPARATE_NONEMPTY
   CONVEX_CONE_HULL_UNION CONVEX_CONE_INTERS CONVEX_CONE_MUL CONVEX_CONE_NONEMPTY
   CONVEX_CONIC_HULL CONVEX_CONTAINS_SEGMENT CONVEX_CONVEX_CONE_HULL CONVEX_CONVEX_HULL
   CONVEX_EMPTY CONVEX_HALFSPACE_GE CONVEX_HALFSPACE_LE CONVEX_HULL_2
   CONVEX_HULL_CLOSURE CONVEX_HULL_EMPTY CONVEX_HULL_EQ CONVEX_HULL_EQ_EMPTY
   CONVEX_HULL_FINITE CONVEX_HULL_INSERT_ALT CONVEX_HULL_INSERT_SEGMENTS
   CONVEX_HULL_LINEAR_IMAGE CONVEX_HULL_PCROSS CONVEX_HULL_SCALING CONVEX_HULL_SING
   CONVEX_HULL_SUBSET_AFFINE_HULL CONVEX_HULL_SUBSET_CONVEX_CONE_HULL CONVEX_HULL_SUMS
   CONVEX_HULL_TRANSLATION CONVEX_HYPERPLANE CONVEX_INTER CONVEX_INTERIOR CONVEX_INTERS
   CONVEX_LINEAR_IMAGE CONVEX_LINEAR_IMAGE_EQ : thm)
  deriving Inhabited

structure QCvxThms3 where
  (CONVEX_NEGATIONS CONVEX_PCROSS CONVEX_POSITIVE_ORTHANT
   CONVEX_RELATIVE_INTERIOR_CLOSURE CONVEX_SING CONVEX_SUMS CONVEX_TRANSLATION_EQ
   CONVEX_UNIV DENSE_COMPLEMENT_CONVEX_CLOSED DEPENDENT_AFFINE_DEPENDENT_CASES
   DIFFERENT_NORM_3_COLLINEAR_POINTS DISJOINT_AFFINE_HULL FRONTIER_CLOSURE_CONVEX
   HAUSDIST_COMPLEMENTS_CONVEX_EXPLICIT HAUSDIST_CONVEX_HULLS
   INDEPENDENT_IMP_AFFINE_DEPENDENT_0 INTERIOR_CONVEX_HULL_EQ_EMPTY INTERIOR_SEGMENT
   INTERIOR_SUBSET_RELATIVE_INTERIOR INTER_CONVEX_HULL_INSERT_RELATIVE_EXTERIOR
   INTER_RELATIVE_FRONTIER_CONIC_HULL INTER_RELATIVE_INTERIOR_SUBSET
   IN_AFFINE_ADD_MUL_DIFF IN_CONVEX_SET IN_RELATIVE_INTERIOR IN_RELATIVE_INTERIOR_CBALL
   IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT IN_RELATIVE_INTERIOR_IN_OPEN_SEGMENT_EQ
   IS_INTERVAL_CONVEX_1 KREIN_MILMAN_FRONTIER OPEN_IN_RELATIVE_INTERIOR
   OPEN_SEGMENT_DESCALE RAY_TO_FRONTIER RELATIVE_FRONTIER_NONEMPTY_INTERIOR
   RELATIVE_FRONTIER_SING RELATIVE_FRONTIER_SUBSET_FRONTIER RELATIVE_INTERIOR
   RELATIVE_INTERIOR_AFFINE RELATIVE_INTERIOR_CBALL RELATIVE_INTERIOR_CLOSURE_SUBSET
   RELATIVE_INTERIOR_EMPTY RELATIVE_INTERIOR_EQ_CLOSURE RELATIVE_INTERIOR_EQ_EMPTY
   RELATIVE_INTERIOR_INTERIOR RELATIVE_INTERIOR_LINEAR_IMAGE_CONVEX
   RELATIVE_INTERIOR_MAXIMAL RELATIVE_INTERIOR_PCROSS RELATIVE_INTERIOR_SING
   RELATIVE_INTERIOR_SUBSET RELATIVE_INTERIOR_TRANSLATION SEGMENT_CONVEX_HULL
   SEGMENT_TO_RELATIVE_FRONTIER SEPARATING_HYPERPLANE_AFFINE_AFFINE
   SEPARATING_HYPERPLANE_CLOSED_0 SEPARATING_HYPERPLANE_CLOSED_POINT
   SUBSET_RELATIVE_INTERIOR SUBSET_SUMS_RCANCEL SUPPORTING_HYPERPLANE_FRONTIER
   SUPPORTING_HYPERPLANE_RELATIVE_BOUNDARY SUPPORTING_HYPERPLANE_RELATIVE_FRONTIER
   affine affine_dependent conic convex convex_cone relative_frontier : thm)
  deriving Inhabited

structure QPthThms where
  (INSIDE_FRONTIER_EQ_INTERIOR : thm)
  deriving Inhabited

structure PolytopeDeps where
  prioritize_real : IO Unit
  cvx : ConvexDeps
  -- procedures and state convex.ml's deps do not carry
  WF_INDUCT_TAC : term → tactic
  prove_recursive_functions_exist : thm → term → ExceptT String IO thm
  invariant_under_translation : IO.Ref (List thm)
  -- theorems
  qses : QSesThms
  qvec : QVecThms
  qmisc : QMiscThms
  qcard : QCardThms
  qfloor : QFloorThms
  qmet : QMetThms
  qtop : QTopThms
  qcvx1 : QCvxThms1
  qcvx2 : QCvxThms2
  qcvx3 : QCvxThms3
  qpth : QPthThms

/- ------------------------------------------------------------------------- -/
/- Faces of a (usually convex) set.  (polytope.ml 1-410)                     -/
/- ------------------------------------------------------------------------- -/

structure POA where
  face_of : thm
  FACE_OF_TRANSLATION_EQ : thm
  FACE_OF_LINEAR_IMAGE : thm
  FACE_OF_REFL : thm
  FACE_OF_REFL_EQ : thm
  EMPTY_FACE_OF : thm
  FACE_OF_EMPTY : thm
  FACE_OF_TRANS : thm
  FACE_OF_FACE : thm
  FACE_OF_SUBSET : thm
  FACE_OF_SLICE : thm
  FACE_OF_INTER : thm
  FACE_OF_INTERS : thm
  FACE_OF_INTER_INTER : thm
  FACE_OF_STILLCONVEX : thm
  FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE_STRONG : thm
  FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE_STRONG : thm
  FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE : thm
  FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE : thm
  FACE_OF_IMP_SUBSET : thm
  FACE_OF_IMP_CONVEX : thm
  FACE_OF_IMP_CLOSED : thm
  FACE_OF_IMP_COMPACT : thm
  FACE_OF_INTER_SUBFACE : thm
  SUBSET_OF_FACE_OF : thm
  FACE_OF_EQ : thm
  FACE_OF_DISJOINT_RELATIVE_INTERIOR : thm
  FACE_OF_DISJOINT_INTERIOR : thm
  SUBSET_OF_FACE_OF_AFFINE_HULL : thm
  AFFINE_HULL_FACE_OF_DISJOINT_RELATIVE_INTERIOR : thm
  FACE_OF_SUBSET_RELATIVE_BOUNDARY : thm
  FACE_OF_SUBSET_RELATIVE_FRONTIER : thm
  FACE_OF_SUBSET_RELATIVE_FRONTIER_AFF_DIM : thm
  FACE_OF_SUBSET_FRONTIER_AFF_DIM : thm
  FACE_OF_AFF_DIM_LT : thm
  deriving Inhabited

set_option maxHeartbeats 4000000 in
@[nospecialize]
def setupPOA [HolBase] (D : PolytopeDeps) : ExceptT String IO POA := do
  -- @@SCOPE BEGIN
  let { add_linear_invariants, add_translation_invariants, ASM_MESON_TAC,
        ASM_REAL_ARITH_TAC, GEOM_TRANSLATE_TAC, invariant_under_linear, MESON_TAC,
        new_definition, NORM_ARITH, parse_as_infix, REAL_ARITH, REAL_FIELD,
        REAL_RAT_REDUCE_CONV, SET_RULE, SET_TAC, VECTOR_ARITH, .. } := D.cvx
  let { CONJ_SYM, CONTRAPOS_THM, DIFF_EMPTY, DISJOINT, EXISTS_IN_GSPEC, EXTENSION, .. } :=
        D.cvx.core1
  let { FORALL_IN_IMAGE, IMP_CONJ, IN_DIFF, INT_LE_REFL, INT_LT_LE, INTER_SUBSET, .. } :=
        D.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, IN_INTER, LEFT_FORALL_IMP_THM, LEFT_IMP_EXISTS_THM,
        MEMBER_NOT_EMPTY, NOT_IN_EMPTY, REAL_ABS_DIV, REAL_DIV_RMUL, .. } := D.cvx.core3
  let { REAL_EQ_NEG2, REAL_LE_ADDL, REAL_LE_LDIV_EQ, REAL_LE_LMUL_EQ, REAL_LE_NEG2,
        REAL_LE_RDIV_EQ, REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_LMUL_EQ,
        REAL_LT_MIN, REAL_MIN_LT, .. } := D.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_LZERO, REAL_SUB_LT, RIGHT_FORALL_IMP_THM,
        SUBSET, SUBSET_ANTISYM, SUBSET_DIFF, SUBSET_EMPTY, SUBSET_TRANS, .. } := D.cvx.core5
  let { real_ge, .. } := D.cvx.core6
  let { HULL_INC, .. } := D.cvx.misc
  let { DOT_LNEG, DOT_RADD, DOT_RMUL, .. } := D.cvx.vec1
  let { NORM_EQ_0, .. } := D.cvx.vec2
  let { NORM_MUL, NORM_POS_LT, NORM_SUB, REAL_ABS_NORM, .. } := D.cvx.vec3
  let { dist, VECTOR_ADD_LDISTRIB, VECTOR_MUL_ASSOC, VECTOR_MUL_EQ_0, VECTOR_SUB_EQ, .. } :=
        D.cvx.vec4
  let { BOUNDED_SUBSET, CLOSED_INTER, .. } := D.cvx.top1
  let { CLOSURE_SUBSET, COMPACT_EQ_BOUNDED_CLOSED, .. } := D.cvx.top2
  let { IN_CBALL, .. } := D.cvx.top4
  let { frontier, open_segment, OPEN_SEGMENT_ALT, segment, SEGMENT_REFL, SEGMENT_SYM, .. }
        := D.cvx.top5
  let { INT_LT_REFL, REAL_LET_ADD2, REAL_LTE_ADD2, .. } := D.qses
  let { AFF_DIM_EMPTY, AFF_DIM_EQ_AFFINE_HULL, AFF_DIM_EQ_MINUS1, AFF_DIM_NONEMPTY_INTERIOR,
        AFF_DIM_SUBSET, AFFINE_AFFINE_HULL, AFFINE_ALT, AFFINE_HULL_EMPTY,
        AFFINE_IMP_CONVEX, CLOSED_AFFINE, .. } := D.qcvx1
  let { CONVEX_CONTAINS_SEGMENT, CONVEX_EMPTY, CONVEX_HYPERPLANE, CONVEX_INTER,
        CONVEX_INTERS, .. } := D.qcvx2
  let { affine, IN_RELATIVE_INTERIOR_CBALL, INTERIOR_SUBSET_RELATIVE_INTERIOR,
        relative_frontier, RELATIVE_FRONTIER_SUBSET_FRONTIER, RELATIVE_INTERIOR_EQ_EMPTY,
        RELATIVE_INTERIOR_SUBSET, SUBSET_RELATIVE_INTERIOR, .. } := D.qcvx3
  -- @@SCOPE END

  D.prioritize_real
  parse_as_infix ("face_of", (12, "right"))

  let face_of ← new_definition
   r"t face_of s <=>
        t SUBSET s /\ convex t /\
        !a b x. a IN s /\ b IN s /\ x IN t /\ x IN segment(a,b)
                ==> a IN t /\ b IN t"

  let FACE_OF_TRANSLATION_EQ ← prove
   r"!a f s:real^N->bool.
        (IMAGE (\x. a + x) f) face_of (IMAGE (\x. a + x) s) <=> f face_of s"
   (REWRITE_TAC [face_of] THEN GEOM_TRANSLATE_TAC [])

  add_translation_invariants [FACE_OF_TRANSLATION_EQ]

  let FACE_OF_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N c s.
      linear f /\ (!x y. f x = f y ==> x = y)
      ==> ((IMAGE f c) face_of (IMAGE f s) <=> c face_of s)"
   (REWRITE_TAC [face_of, IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN MP_TAC (← HolLight.end_itlist CONJ
     (← HolMath.IndTypes.mapfilterM (ISPEC (← q r"f:real^M->real^N"))
          (← invariant_under_linear.get))) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [])

  add_linear_invariants [FACE_OF_LINEAR_IMAGE]

  let FACE_OF_REFL ← prove
   r"!s. convex s ==> s face_of s"
   (SIMP_TAC [face_of] THEN SET_TAC [])

  let FACE_OF_REFL_EQ ← prove
   r"!s. s face_of s <=> convex s"
   (SIMP_TAC [face_of] THEN SET_TAC [])

  let EMPTY_FACE_OF ← prove
   r"!s. {} face_of s"
   (REWRITE_TAC [face_of, CONVEX_EMPTY] THEN SET_TAC [])

  let FACE_OF_EMPTY ← prove
   r"!s. s face_of {} <=> s = {}"
   (REWRITE_TAC [face_of, SUBSET_EMPTY, NOT_IN_EMPTY] THEN
    MESON_TAC [CONVEX_EMPTY])

  let FACE_OF_TRANS ← prove
   r"!s t u. s face_of t /\ t face_of u
           ==> s face_of u"
   (REWRITE_TAC [face_of] THEN SET_TAC [])

  let FACE_OF_FACE ← prove
   r"!f s t.
        t face_of s
        ==> (f face_of t <=> f face_of s /\ f SUBSET t)"
   (REWRITE_TAC [face_of] THEN SET_TAC [])

  let FACE_OF_SUBSET ← prove
   r"!f s t. f face_of s /\ f SUBSET t /\ t SUBSET s ==> f face_of t"
   (REWRITE_TAC [face_of] THEN SET_TAC [])

  let FACE_OF_SLICE ← prove
   r"!f s t.
        f face_of s /\ convex t
        ==> (f INTER t) face_of (s INTER t)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [face_of, IN_INTER] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC [],
      ASM_MESON_TAC [CONVEX_INTER],
      ASM_MESON_TAC []])

  let FACE_OF_INTER ← prove
   r"!s t1 t2. t1 face_of s /\ t2 face_of s
             ==> (t1 INTER t2) face_of s"
   (SIMP_TAC [face_of, CONVEX_INTER] THEN SET_TAC [])

  let FACE_OF_INTERS ← prove
   r"!P s. ~(P = {}) /\ (!t. t IN P ==> t face_of s)
         ==> (INTERS P) face_of s"
   (REWRITE_TAC [face_of] THEN REPEAT STRIP_TAC THENL
     [ASM SET_TAC [], ASM_SIMP_TAC [CONVEX_INTERS], ASM SET_TAC [], ASM SET_TAC []])

  let FACE_OF_INTER_INTER ← prove
   r"!f t f' t'.
     f face_of t /\ f' face_of t' ==> (f INTER f') face_of (t INTER t')"
   (REWRITE_TAC [face_of, SUBSET, IN_INTER] THEN MESON_TAC [CONVEX_INTER])

  let FACE_OF_STILLCONVEX ← prove
   r"!s t:real^N->bool.
        convex s
        ==> (t face_of s <=>
             t SUBSET s /\
             convex(s DIFF t) /\
             t = (affine hull t) INTER s)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [face_of] THEN
    ASM_CASES_TAC (← q r"(t:real^N->bool) SUBSET s") THEN ASM_REWRITE_TAC [] THEN
    EQ_TAC THEN STRIP_TAC THENL
     [CONJ_TAC THENL
       [REPEAT (POP_ASSUM MP_TAC) THEN
        REWRITE_TAC [CONVEX_CONTAINS_SEGMENT, open_segment, IN_DIFF] THEN
        REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, SUBSET_DIFF] THEN SET_TAC [],
        ALL_TAC] THEN
      REWRITE_TAC [EXTENSION] THEN X_GEN_TAC (← q r"x:real^N") THEN EQ_TAC THENL
       [ASM MESON_TAC [HULL_INC, SUBSET, IN_INTER], ALL_TAC] THEN
      ASM_CASES_TAC (← q r"t:real^N -> bool = {}") THEN
      ASM_REWRITE_TAC [IN_INTER, AFFINE_HULL_EMPTY, NOT_IN_EMPTY] THEN
      MP_TAC (← ISPEC (← q r"t:real^N->bool") RELATIVE_INTERIOR_EQ_EMPTY) THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"y:real^N") THEN REWRITE_TAC [IN_RELATIVE_INTERIOR_CBALL] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"e:real") STRIP_ASSUME_TAC) THEN
      STRIP_TAC THEN ASM_CASES_TAC (← q r"x:real^N = y") THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"x:real^N", ← q r"y:real^N"]) THEN
      REWRITE_TAC [] THEN ONCE_REWRITE_TAC [SEGMENT_SYM] THEN
      ASM_SIMP_TAC [LEFT_FORALL_IMP_THM, OPEN_SEGMENT_ALT] THEN
      ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [SUBSET]) THEN ASM_SIMP_TAC [] THEN
      ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [CONJ_SYM] THEN
      REWRITE_TAC [EXISTS_IN_GSPEC] THEN
      EXISTS_TAC (← q r"min (&1 / &2) (e / norm(x - y:real^N))") THEN
      REWRITE_TAC [REAL_LT_MIN, REAL_MIN_LT] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_SIMP_TAC [REAL_LT_DIV, NORM_POS_LT, VECTOR_SUB_EQ] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [IN_INTER, IN_CBALL, dist] THEN
      CONJ_TAC THENL
       [REWRITE_TAC [NORM_MUL, ← VECTOR_ARITH
         (← q r"y - ((&1 - u) % y + u % x):real^N = u % (y - x)")] THEN
        ASM_SIMP_TAC [← GSYM REAL_LE_RDIV_EQ, NORM_POS_LT, VECTOR_SUB_EQ] THEN
        REWRITE_TAC [NORM_SUB] THEN
        MATCH_MP_TAC (← REAL_ARITH (← q r"&0 < e ==> abs(min (&1 / &2) e) <= e")) THEN
        ASM_SIMP_TAC [REAL_LT_DIV, NORM_POS_LT, VECTOR_SUB_EQ],
        MATCH_MP_TAC (← REWRITE_RULE [AFFINE_ALT] AFFINE_AFFINE_HULL) THEN
        ASM_SIMP_TAC [HULL_INC]],
      CONJ_TAC THENL
       [ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC CONVEX_INTER THEN
        ASM_SIMP_TAC [AFFINE_IMP_CONVEX, AFFINE_AFFINE_HULL],
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"b:real^N", ← q r"x:real^N"] THEN
      SUBGOAL_THEN
       (← q r"!a b x:real^N. a IN s /\ b IN s /\ x IN t /\ x IN segment(a,b) /\
                       (a IN affine hull t ==> b IN affine hull t)
                       ==> a IN t /\ b IN t")
       (fun th => MESON_TAC [th, SEGMENT_SYM]) THEN
      REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"(a:real^N) IN affine hull t") THEN
      ASM_REWRITE_TAC [] THENL [ASM SET_TAC [], STRIP_TAC] THEN
      ASM_CASES_TAC (← q r"a:real^N = b") THENL
       [ASM_MESON_TAC [SEGMENT_REFL, NOT_IN_EMPTY], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(a:real^N) IN (s DIFF t) /\ b IN  (s DIFF t)")
      STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC [IN_DIFF] THEN ONCE_ASM_REWRITE_TAC [] THEN
        ASM_REWRITE_TAC [IN_INTER] THEN
        UNDISCH_TAC (← q r"~((a:real^N) IN affine hull t)") THEN
        UNDISCH_TAC (← q r"(x:real^N) IN segment(a,b)") THEN
        ASM_SIMP_TAC [OPEN_SEGMENT_ALT, CONTRAPOS_THM, IN_ELIM_THM] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"u:real") STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM (MP_TAC o AP_TERM (← q r"(%) (inv(&1 - u)) :real^N->real^N")) THEN
        REWRITE_TAC [VECTOR_ADD_LDISTRIB, VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC [REAL_MUL_LINV, ← REAL_ARITH (← q r"x < &1 ==> ~(&1 - x = &0)")] THEN
        REWRITE_TAC [← VECTOR_ARITH
         (← q r"x:real^N = &1 % a + u % b <=> a = x + --u %  b")] THEN
        DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
        MATCH_MP_TAC (← REWRITE_RULE [affine] AFFINE_AFFINE_HULL) THEN
        ASM_SIMP_TAC [HULL_INC] THEN
        UNDISCH_TAC (← q r"u < &1") THEN CONV_TAC (fun t => REAL_FIELD t),
        MP_TAC (← ISPEC (← q r"s DIFF t:real^N->bool") CONVEX_CONTAINS_SEGMENT) THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (MP_TAC o SPECL [← q r"a:real^N", ← q r"b:real^N"]) THEN
        ASM_REWRITE_TAC [SUBSET, IN_DIFF] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"x:real^N")) THEN
        ASM_MESON_TAC [segment, IN_DIFF]]])

  let FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE_STRONG ← prove
   r"!s a:real^N b.
        convex(s INTER {x | a dot x = b}) /\ (!x. x IN s ==> a dot x <= b)
        ==> (s INTER {x | a dot x = b}) face_of s"
   (MAP_EVERY X_GEN_TAC [← q r"s:real^N->bool", ← q r"c:real^N", ← q r"d:real"] THEN
    SIMP_TAC [face_of, INTER_SUBSET] THEN
    STRIP_TAC THEN REWRITE_TAC [IN_INTER, IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"b:real^N", ← q r"x:real^N"] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"a <= x /\ b <= x /\ ~(a < x) /\ ~(b < x) ==> a = x /\ b = x")) THEN
    ASM_SIMP_TAC [] THEN UNDISCH_TAC (← q r"(x:real^N) IN segment(a,b)") THEN
    ASM_CASES_TAC (← q r"a:real^N = b") THEN
    ASM_REWRITE_TAC [SEGMENT_REFL, NOT_IN_EMPTY] THEN
    ASM_SIMP_TAC [OPEN_SEGMENT_ALT, IN_ELIM_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:real") STRIP_ASSUME_TAC) THEN
    CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC (← q r"(c:real^N) dot x = d") THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"x < a ==> x = a ==> F")) THEN
    SUBST1_TAC (← REAL_ARITH (← q r"d = (&1 - u) * d + u * d")) THEN
    ASM_REWRITE_TAC [DOT_RADD, DOT_RMUL] THENL
     [MATCH_MP_TAC REAL_LTE_ADD2, MATCH_MP_TAC REAL_LET_ADD2] THEN
    ASM_SIMP_TAC [REAL_LE_LMUL_EQ, REAL_LT_LMUL_EQ, REAL_SUB_LT])

  let FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE_STRONG ← prove
   r"!s a:real^N b.
        convex(s INTER {x | a dot x = b}) /\ (!x. x IN s ==> a dot x >= b)
        ==> (s INTER {x | a dot x = b}) face_of s"
   (REWRITE_TAC [real_ge] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"--a:real^N", ← q r"--b:real"]
      FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE_STRONG) THEN
    ASM_REWRITE_TAC [DOT_LNEG, REAL_EQ_NEG2, REAL_LE_NEG2])

  let FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE ← prove
   r"!s a:real^N b.
        convex s /\ (!x. x IN s ==> a dot x <= b)
        ==> (s INTER {x | a dot x = b}) face_of s"
   (SIMP_TAC [FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE_STRONG,
              CONVEX_INTER, CONVEX_HYPERPLANE])

  let FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE ← prove
   r"!s a:real^N b.
        convex s /\ (!x. x IN s ==> a dot x >= b)
        ==> (s INTER {x | a dot x = b}) face_of s"
   (SIMP_TAC [FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE_STRONG,
              CONVEX_INTER, CONVEX_HYPERPLANE])

  let FACE_OF_IMP_SUBSET ← prove
   r"!s t. t face_of s ==> t SUBSET s"
   (SIMP_TAC [face_of])

  let FACE_OF_IMP_CONVEX ← prove
   r"!s t. t face_of s ==> convex t"
   (SIMP_TAC [face_of])

  let FACE_OF_IMP_CLOSED ← prove
   r"!s t. convex s /\ closed s /\ t face_of s ==> closed t"
   (REPEAT GEN_TAC THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC [FACE_OF_STILLCONVEX] THEN
    STRIP_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [CLOSED_AFFINE, AFFINE_AFFINE_HULL, CLOSED_INTER])

  let FACE_OF_IMP_COMPACT ← prove
   r"!s t. convex s /\ compact s /\ t face_of s ==> compact t"
   (SIMP_TAC [COMPACT_EQ_BOUNDED_CLOSED] THEN
    ASM_MESON_TAC [BOUNDED_SUBSET, FACE_OF_IMP_SUBSET, FACE_OF_IMP_CLOSED])

  let FACE_OF_INTER_SUBFACE ← prove
   r"!c1 c2 d1 d2:real^N->bool.
        (c1 INTER c2) face_of c1 /\ (c1 INTER c2) face_of c2 /\
        d1 face_of c1 /\ d2 face_of c2
        ==> (d1 INTER d2) face_of d1 /\ (d1 INTER d2) face_of d2"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FACE_OF_SUBSET THENL
     [EXISTS_TAC (← q r"c1:real^N->bool"), EXISTS_TAC (← q r"c2:real^N->bool")] THEN
    ASM_SIMP_TAC [FACE_OF_IMP_SUBSET, INTER_SUBSET] THEN
    TRANS_TAC FACE_OF_TRANS (← q r"c1 INTER c2:real^N->bool") THEN
    ASM_SIMP_TAC [FACE_OF_INTER_INTER])

  let SUBSET_OF_FACE_OF ← prove
   r"!s t u:real^N->bool.
      t face_of s /\ u SUBSET s /\
      ~(DISJOINT t (relative_interior u))
      ==> u SUBSET t"
   (REWRITE_TAC [DISJOINT] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"c:real^N") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC [IN_INTER, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"b:real^N") THEN
    REWRITE_TAC [IN_RELATIVE_INTERIOR_CBALL] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"e:real") MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [SUBSET, IN_CBALL, IN_INTER] THEN
    ASM_CASES_TAC (← q r"c:real^N = b") THEN ASM_REWRITE_TAC [] THEN
    ABBREV_TAC (← q r"d:real^N = b + e / norm(b - c) % (b - c)") THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"d:real^N")) THEN ANTS_TAC THENL
     [EXPAND_TAC "d" THEN CONJ_TAC THENL
       [REWRITE_TAC [← NORM_ARITH (← q r"dist(b:real^N,b + e) = norm e")] THEN
        REWRITE_TAC [NORM_MUL, REAL_ABS_DIV, REAL_ABS_NORM] THEN
        ASM_SIMP_TAC [REAL_DIV_RMUL, NORM_EQ_0, VECTOR_SUB_EQ] THEN
        ASM_REAL_ARITH_TAC,
        REWRITE_TAC [← VECTOR_ARITH
         (← q r"b + u % (b - c):real^N = (&1 - --u) % b + --u % c")] THEN
        MATCH_MP_TAC (← REWRITE_RULE [AFFINE_ALT] AFFINE_AFFINE_HULL) THEN
        ASM_SIMP_TAC [HULL_INC]],
      STRIP_TAC THEN
      SUBGOAL_THEN (← q r"(d:real^N) IN t /\ c IN t") (fun th => MESON_TAC [th]) THEN
      FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [face_of]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC (← q r"b:real^N") THEN
      REPEAT (CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN
      SUBGOAL_THEN (← q r"~(b:real^N = d)") ASSUME_TAC THENL
       [EXPAND_TAC "d" THEN
        REWRITE_TAC [← VECTOR_ARITH (← q r"b:real^N = b + e <=> e = vec 0")] THEN
        ASM_SIMP_TAC [REAL_LT_DIV, NORM_POS_LT, VECTOR_SUB_EQ,
                      VECTOR_MUL_EQ_0, REAL_LT_IMP_NZ],
        ASM_REWRITE_TAC [segment, IN_DIFF, IN_INSERT, NOT_IN_EMPTY] THEN
        REWRITE_TAC [IN_ELIM_THM] THEN
        EXISTS_TAC (← q r"(e / norm(b - c:real^N)) / (&1 + e / norm(b - c))") THEN
        ASM_SIMP_TAC [REAL_LT_DIV, NORM_POS_LT, VECTOR_SUB_EQ,
                      ← REAL_ARITH (← q r"&0 < x ==> &0 < &1 + x"),
                      REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ, REAL_MUL_LID] THEN
        REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_LID] THEN
        ASM_SIMP_TAC [← REAL_FIELD (← q r"&0 < n ==> (&1 + e / n) * n = n + e"),
                      NORM_POS_LT, VECTOR_SUB_EQ, REAL_LE_ADDL] THEN
        ASM_SIMP_TAC [NORM_POS_LT, REAL_LT_IMP_LE, VECTOR_SUB_EQ] THEN
        EXPAND_TAC "d" THEN REWRITE_TAC [← VECTOR_ARITH
         (← q r"b:real^N = (&1 - u) % (b + e % (b - c)) + u % c <=>
          (u - e * (&1 - u)) % (b - c) = vec 0")] THEN
        ASM_REWRITE_TAC [VECTOR_MUL_EQ_0, VECTOR_SUB_EQ] THEN
        MATCH_MP_TAC (← REAL_FIELD
         (← q r"&0 < e ==> e / (&1 + e) - e * (&1 - e / (&1 + e)) = &0")) THEN
        ASM_SIMP_TAC [REAL_LT_DIV, NORM_POS_LT, VECTOR_SUB_EQ]]])

  let FACE_OF_EQ ← prove
   r"!s t u:real^N->bool.
        t face_of s /\ u face_of s /\
        ~(DISJOINT (relative_interior t) (relative_interior u))
        ==> t = u"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    CONJ_TAC THEN MATCH_MP_TAC SUBSET_OF_FACE_OF THEN
    EXISTS_TAC (← q r"s:real^N->bool") THEN ASM_SIMP_TAC [FACE_OF_IMP_SUBSET] THENL
     [MP_TAC (← ISPEC (← q r"u:real^N->bool") RELATIVE_INTERIOR_SUBSET),
      MP_TAC (← ISPEC (← q r"t:real^N->bool") RELATIVE_INTERIOR_SUBSET)] THEN
    ASM SET_TAC [])

  let FACE_OF_DISJOINT_RELATIVE_INTERIOR ← prove
   r"!f s:real^N->bool.
        f face_of s /\ ~(f = s) ==> f INTER relative_interior s = {}"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"f:real^N->bool", ← q r"s:real^N->bool"]
          SUBSET_OF_FACE_OF) THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
    ASM SET_TAC [])

  let FACE_OF_DISJOINT_INTERIOR ← prove
   r"!f s:real^N->bool.
        f face_of s /\ ~(f = s) ==> f INTER interior s = {}"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    MP_TAC (← ISPEC (← q r"s:real^N->bool") INTERIOR_SUBSET_RELATIVE_INTERIOR) THEN
    SET_TAC [])

  let SUBSET_OF_FACE_OF_AFFINE_HULL ← prove
   r"!s t u:real^N->bool.
        t face_of s /\ convex s /\ u SUBSET s /\
        ~DISJOINT (affine hull t) (relative_interior u)
        ==> u SUBSET t"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_OF_FACE_OF THEN
    EXISTS_TAC (← q r"s:real^N->bool") THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"t:real^N->bool"] FACE_OF_STILLCONVEX) THEN
    MP_TAC (← ISPEC (← q r"u:real^N->bool") RELATIVE_INTERIOR_SUBSET) THEN
    ASM_REWRITE_TAC [] THEN ASM SET_TAC [])

  let AFFINE_HULL_FACE_OF_DISJOINT_RELATIVE_INTERIOR ← prove
   r"!s f:real^N->bool.
        convex s /\ f face_of s /\ ~(f = s)
        ==> affine hull f INTER relative_interior s = {}"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"f:real^N->bool", ← q r"s:real^N->bool"]
          SUBSET_OF_FACE_OF_AFFINE_HULL) THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN ASM SET_TAC [])

  let FACE_OF_SUBSET_RELATIVE_BOUNDARY ← prove
   r"!s f:real^N->bool.
        f face_of s /\ ~(f = s) ==> f SUBSET (s DIFF relative_interior s)"
   (ASM_SIMP_TAC [← SET_RULE (← q r"s SUBSET u DIFF t <=> s SUBSET u /\ s INTER t = {}"),
                  FACE_OF_DISJOINT_RELATIVE_INTERIOR, FACE_OF_IMP_SUBSET])

  let FACE_OF_SUBSET_RELATIVE_FRONTIER ← prove
   r"!s f:real^N->bool.
        f face_of s /\ ~(f = s) ==> f SUBSET relative_frontier s"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP FACE_OF_SUBSET_RELATIVE_BOUNDARY) THEN
    REWRITE_TAC [relative_frontier] THEN
    MP_TAC (← ISPEC (← q r"s:real^N->bool") CLOSURE_SUBSET) THEN SET_TAC [])

  let FACE_OF_SUBSET_RELATIVE_FRONTIER_AFF_DIM ← prove
   r"!f s:real^N->bool.
        f face_of s /\ aff_dim f < aff_dim s
        ==> f SUBSET relative_frontier s"
   (MESON_TAC [FACE_OF_SUBSET_RELATIVE_FRONTIER, INT_LT_REFL])

  let FACE_OF_SUBSET_FRONTIER_AFF_DIM ← prove
   r"!f s:real^N->bool.
        f face_of s /\ aff_dim f < &(dimindex(:N))
        ==> f SUBSET frontier s"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"interior s:real^N->bool = {}") THENL
     [ASM_SIMP_TAC [frontier, DIFF_EMPTY] THEN
      ASM_MESON_TAC [FACE_OF_IMP_SUBSET, SUBSET_TRANS, CLOSURE_SUBSET],
      TRANS_TAC SUBSET_TRANS (← q r"relative_frontier s:real^N->bool") THEN
      REWRITE_TAC [RELATIVE_FRONTIER_SUBSET_FRONTIER] THEN
      ASM_MESON_TAC [AFF_DIM_NONEMPTY_INTERIOR,
                     FACE_OF_SUBSET_RELATIVE_FRONTIER_AFF_DIM]])

  let FACE_OF_AFF_DIM_LT ← prove
   r"!f s:real^N->bool.
        convex s /\ f face_of s /\ ~(f = s) ==> aff_dim f < aff_dim s"
   (REPEAT GEN_TAC THEN
    SIMP_TAC [INT_LT_LE, FACE_OF_IMP_SUBSET, AFF_DIM_SUBSET] THEN
    REWRITE_TAC [IMP_CONJ, CONTRAPOS_THM] THEN
    ASM_CASES_TAC (← q r"f:real^N->bool = {}") THENL
     [CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
      ASM_REWRITE_TAC [AFF_DIM_EQ_MINUS1, AFF_DIM_EMPTY],
      REPEAT STRIP_TAC THEN MATCH_MP_TAC FACE_OF_EQ THEN
      EXISTS_TAC (← q r"s:real^N->bool") THEN ASM_SIMP_TAC [FACE_OF_REFL] THEN
      MATCH_MP_TAC (← SET_RULE (← q r"~(f = {}) /\ f SUBSET s ==> ~DISJOINT f s")) THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP FACE_OF_IMP_CONVEX) THEN
      ASM_SIMP_TAC [RELATIVE_INTERIOR_EQ_EMPTY] THEN
      MATCH_MP_TAC SUBSET_RELATIVE_INTERIOR THEN
      ASM_MESON_TAC [FACE_OF_IMP_SUBSET, AFF_DIM_EQ_AFFINE_HULL, INT_LE_REFL]])

  pure { face_of, FACE_OF_TRANSLATION_EQ, FACE_OF_LINEAR_IMAGE, FACE_OF_REFL,
         FACE_OF_REFL_EQ, EMPTY_FACE_OF, FACE_OF_EMPTY, FACE_OF_TRANS, FACE_OF_FACE,
         FACE_OF_SUBSET, FACE_OF_SLICE, FACE_OF_INTER, FACE_OF_INTERS,
         FACE_OF_INTER_INTER, FACE_OF_STILLCONVEX,
         FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE_STRONG,
         FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE_STRONG,
         FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE, FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE,
         FACE_OF_IMP_SUBSET, FACE_OF_IMP_CONVEX, FACE_OF_IMP_CLOSED, FACE_OF_IMP_COMPACT,
         FACE_OF_INTER_SUBFACE, SUBSET_OF_FACE_OF, FACE_OF_EQ,
         FACE_OF_DISJOINT_RELATIVE_INTERIOR, FACE_OF_DISJOINT_INTERIOR,
         SUBSET_OF_FACE_OF_AFFINE_HULL, AFFINE_HULL_FACE_OF_DISJOINT_RELATIVE_INTERIOR,
         FACE_OF_SUBSET_RELATIVE_BOUNDARY, FACE_OF_SUBSET_RELATIVE_FRONTIER,
         FACE_OF_SUBSET_RELATIVE_FRONTIER_AFF_DIM, FACE_OF_SUBSET_FRONTIER_AFF_DIM,
         FACE_OF_AFF_DIM_LT }

/- ------------------------------------------------------------------------- -/
/- Faces of convex hulls; affine sets; finite bounds on intersections of     -/
/- faces.  (polytope.ml 411-784)                                             -/
/- ------------------------------------------------------------------------- -/

structure POB where
  FACE_OF_CONVEX_HULLS : thm
  FACE_OF_CONVEX_HULL_INSERT : thm
  FACE_OF_AFFINE_TRIVIAL : thm
  FACE_OF_AFFINE_EQ : thm
  INTERS_FACES_FINITE_BOUND : thm
  INTERS_FACES_FINITE_ALTBOUND : thm
  deriving Inhabited

set_option maxHeartbeats 4000000 in
@[nospecialize]
def setupPOB [HolBase] (D : PolytopeDeps) (BPOA : POA) : ExceptT String IO POB := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INDUCT_TAC,
        INT_ARITH, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD, REAL_RAT_REDUCE_CONV,
        SET_RULE, SET_TAC, VECTOR_ARITH, VECTOR_ARITH_TAC, .. } := D.cvx
  let { prove_recursive_functions_exist, .. } := D
  let { CARD_CLAUSES, CONJ_ASSOC, EMPTY_SUBSET, ETA_AX, FINITE_DIFF, FINITE_EMPTY,
        FINITE_INSERT, FINITE_SUBSET, .. } := D.cvx.core1
  let { IN_DELETE, IN_DIFF, IN_DISJOINT, INSERT_SUBSET, INT_NOT_LT, INT_OF_NUM_ADD,
        INT_OF_NUM_SUC, INTER_SUBSET, INTERS_INSERT, .. } := D.cvx.core2
  let { IN_ELIM_THM, IN_INTERS, LE_REFL, LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY, MONO_EXISTS,
        NOT_FORALL_THM, NOT_IMP, PSUBSET, .. } := D.cvx.core3
  let { REAL_ENTIRE, REAL_LE_ADD, REAL_LE_INV_EQ, REAL_LE_MUL, REAL_LT_IMP_LE,
        REAL_LT_IMP_NE, REAL_LT_LE, .. } := D.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LINV, REAL_SUB_0, REAL_SUB_LT, RIGHT_IMP_EXISTS_THM,
        SKOLEM_THM, SUBSET, SUBSET_ANTISYM, SUBSET_DELETE, SUBSET_REFL, SUBSET_TRANS, .. }
        := D.cvx.core5
  let { SUM_ADD, SUM_DIFF, SUM_LMUL, SUM_POS_EQ_0, SUM_POS_LE, SUM_SUPERSET, .. } :=
        D.cvx.core6
  let { HULL_MINIMAL, HULL_MONO, .. } := D.cvx.misc
  let { VECTOR_ADD_RDISTRIB, VECTOR_ADD_SUB, VECTOR_MUL_ASSOC, VECTOR_MUL_EQ_0,
        VECTOR_MUL_LZERO, VECTOR_SUB_RZERO, VSUM_0, VSUM_ADD, VSUM_DIFF, VSUM_LMUL,
        VSUM_SUPERSET, .. } := D.cvx.vec4
  let { IN_SEGMENT, .. } := D.cvx.top4
  let { INT_LTE_TRANS, INT_NOT_LE, INT_SUB_RZERO, num_RECURSION, .. } := D.qses
  let { AFF_DIM_GE, AFF_DIM_LE_UNIV, AFFINE_AFFINE_HULL, AFFINE_ALT, AFFINE_HULL_FINITE,
        AFFINE_IMP_CONVEX, .. } := D.qcvx1
  let { CONVEX_CONVEX_HULL, CONVEX_HULL_FINITE, CONVEX_HULL_SUBSET_AFFINE_HULL,
        CONVEX_INTERS, .. } := D.qcvx2
  let { CONVEX_SING, IN_AFFINE_ADD_MUL_DIFF, .. } := D.qcvx3
  let { EMPTY_FACE_OF, face_of, FACE_OF_AFF_DIM_LT, FACE_OF_FACE, FACE_OF_IMP_CONVEX,
        FACE_OF_IMP_SUBSET, FACE_OF_INTERS, FACE_OF_REFL, FACE_OF_TRANS, .. } := BPOA
  -- @@SCOPE END

  let FACE_OF_CONVEX_HULLS ← (do
    let lemma ← prove
     r"!s x y:real^N.
          affine s /\ ~(k = &0) /\ ~(k = &1) /\ x IN s /\ inv(&1 - k) % y IN s
          ==> inv(k) % (x - y) IN s"
     (REWRITE_TAC [AFFINE_ALT] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"inv(k) % (x - y):real^N = (&1 - inv k) % inv(&1 - k) % y + inv(k) % x")
       (fun th => ASM_SIMP_TAC [th]) THEN
      REWRITE_TAC [VECTOR_MUL_EQ_0, ← VECTOR_ARITH
       (← q r"k % (x - y):real^N = a % b % y + k % x <=> (a * b + k) % y = vec 0")] THEN
      DISJ1_TAC THEN MAP_EVERY UNDISCH_TAC [← q r"~(k = &0)", ← q r"~(k = &1)"] THEN
      CONV_TAC (fun t => REAL_FIELD t))
    prove
     r"!f s:real^N->bool.
        FINITE s /\ f SUBSET s /\
        DISJOINT (affine hull f) (convex hull (s DIFF f))
        ==> (convex hull f) face_of (convex hull s)"
     (REPEAT STRIP_TAC THEN REWRITE_TAC [face_of] THEN
      SUBGOAL_THEN (← q r"FINITE(f:real^N->bool)") ASSUME_TAC THENL
       [ASM_MESON_TAC [FINITE_SUBSET], ALL_TAC] THEN
      FIRST_ASSUM (ASSUME_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      ASM_SIMP_TAC [HULL_MONO, CONVEX_CONVEX_HULL] THEN
      MAP_EVERY X_GEN_TAC [← q r"x:real^N", ← q r"y:real^N", ← q r"w:real^N"] THEN
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT]) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN (← q r"u:real") STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN (← q r"(w:real^N) IN affine hull f") ASSUME_TAC THENL
       [ASM_MESON_TAC [CONVEX_HULL_SUBSET_AFFINE_HULL, SUBSET], ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [← q r"(y:real^N) IN convex hull s", ← q r"(x:real^N) IN convex hull s"] THEN
      REWRITE_TAC [CONVEX_HULL_FINITE, IN_ELIM_THM] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"a:real^N->real") STRIP_ASSUME_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"b:real^N->real") STRIP_ASSUME_TAC) THEN
      ABBREV_TAC (← q r"(c:real^N->real) = \x. (&1 - u) * a x + u * b x") THEN
      SUBGOAL_THEN (← q r"!x:real^N. x IN s ==> &0 <= c x") ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN EXPAND_TAC "c" THEN REWRITE_TAC [] THEN
        MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC [] THEN ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      ASM_CASES_TAC (← q r"sum (s DIFF f:real^N->bool) c = &0") THENL
       [SUBGOAL_THEN (← q r"!x:real^N. x IN (s DIFF f) ==> c x = &0") MP_TAC THENL
         [MATCH_MP_TAC SUM_POS_EQ_0 THEN ASM_MESON_TAC [FINITE_DIFF, IN_DIFF],
          ALL_TAC] THEN
        EXPAND_TAC "c" THEN
        ASM_SIMP_TAC [IN_DIFF, REAL_LE_MUL, REAL_LT_IMP_LE, REAL_SUB_LT,
         ← REAL_ARITH (← q r"&0 <= x /\ &0 <= y ==> (x + y = &0 <=> x = &0 /\ y = &0)"),
         REAL_ENTIRE, REAL_SUB_0, REAL_LT_IMP_NE] THEN
        STRIP_TAC THEN CONJ_TAC THENL
         [EXISTS_TAC (← q r"a:real^N->real"), EXISTS_TAC (← q r"b:real^N->real")] THEN
        ASM_SIMP_TAC [] THEN CONJ_TAC THEN FIRST_X_ASSUM (fun th => tactic_of do
          pure (GEN_REWRITE_TAC RAND_CONV [← GSYM th] THEN CONV_TAC SYM_CONV THEN
           (MATCH_MP_TAC SUM_SUPERSET ORELSE MATCH_MP_TAC VSUM_SUPERSET))) THEN
        ASM_SIMP_TAC [VECTOR_MUL_LZERO],
        ALL_TAC] THEN
      ABBREV_TAC (← q r"k = sum (s DIFF f:real^N->bool) c") THEN
      SUBGOAL_THEN (← q r"&0 < k") ASSUME_TAC THENL
       [ASM_REWRITE_TAC [REAL_LT_LE] THEN EXPAND_TAC "k" THEN
        MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC [FINITE_DIFF, IN_DIFF],
        ALL_TAC] THEN
      ASM_CASES_TAC (← q r"k = &1") THENL
       [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [IN_DISJOINT]) THEN
        MATCH_MP_TAC (← TAUT (← q r"b ==> ~b ==> c")) THEN
        EXISTS_TAC (← q r"w:real^N") THEN
        ASM_REWRITE_TAC [CONVEX_HULL_FINITE, IN_ELIM_THM] THEN
        EXISTS_TAC (← q r"c:real^N->real") THEN
        ASM_SIMP_TAC [IN_DIFF, SUM_DIFF, VSUM_DIFF] THEN
        SUBGOAL_THEN (← q r"vsum f (\x:real^N. c x % x) = vec 0") SUBST1_TAC THENL
         [ALL_TAC,
          EXPAND_TAC "c" THEN REWRITE_TAC [VECTOR_ADD_RDISTRIB] THEN
          ASM_SIMP_TAC [VSUM_ADD, ← GSYM VECTOR_MUL_ASSOC, VSUM_LMUL] THEN
          REWRITE_TAC [VECTOR_SUB_RZERO]] THEN
        SUBGOAL_THEN (← q r"sum(s DIFF f) c = sum s c - sum f (c:real^N->real)")
        MP_TAC THENL [ASM_MESON_TAC [SUM_DIFF], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN (← q r"sum s (c:real^N->real) = &1") SUBST1_TAC THENL
         [EXPAND_TAC "c" THEN REWRITE_TAC [VECTOR_ADD_RDISTRIB] THEN
          ASM_SIMP_TAC [SUM_ADD, ← GSYM REAL_MUL_ASSOC, SUM_LMUL] THEN
          REAL_ARITH_TAC,
          ALL_TAC] THEN
        REWRITE_TAC [← REAL_ARITH (← q r"&1 = &1 - x <=> x = &0")] THEN DISCH_TAC THEN
        MP_TAC (← ISPECL [← q r"c:real^N->real", ← q r"f:real^N->bool"] SUM_POS_EQ_0) THEN
        ANTS_TAC THENL [ASM_MESON_TAC [FINITE_SUBSET, SUBSET], ALL_TAC] THEN
        SIMP_TAC [VECTOR_MUL_LZERO, VSUM_0],
        ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [IN_DISJOINT]) THEN
      MATCH_MP_TAC (← TAUT (← q r"b ==> ~b ==> c")) THEN
      EXISTS_TAC (← q r"inv(k) % (w - vsum f (\x:real^N. c x % x))") THEN CONJ_TAC THENL
       [ALL_TAC,
        SUBGOAL_THEN (← q r"w = vsum f (\x:real^N. c x % x) +
                          vsum (s DIFF f) (\x:real^N. c x % x)")
        SUBST1_TAC THENL
         [ASM_SIMP_TAC [VSUM_DIFF, ← VECTOR_ARITH (← q r"a + b - a:real^N = b")] THEN
          EXPAND_TAC "c" THEN REWRITE_TAC [VECTOR_ADD_RDISTRIB] THEN
          ASM_SIMP_TAC [VSUM_ADD, ← GSYM VECTOR_MUL_ASSOC, VSUM_LMUL],
          REWRITE_TAC [VECTOR_ADD_SUB]] THEN
        ASM_SIMP_TAC [← GSYM VSUM_LMUL, FINITE_DIFF] THEN
        REWRITE_TAC [CONVEX_HULL_FINITE, IN_ELIM_THM] THEN
        EXISTS_TAC (← q r"\x. inv k * (c:real^N->real) x") THEN
        ASM_REWRITE_TAC [VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC [IN_DIFF, REAL_LE_MUL, REAL_LE_INV_EQ, REAL_LT_IMP_LE] THEN
        ASM_SIMP_TAC [SUM_LMUL, ETA_AX, REAL_MUL_LINV]] THEN
      MATCH_MP_TAC lemma THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC [AFFINE_AFFINE_HULL],
        ASM_REWRITE_TAC [],
        ASM_REWRITE_TAC [],
        ASM_MESON_TAC [CONVEX_HULL_SUBSET_AFFINE_HULL, SUBSET],
        ALL_TAC] THEN
      ASM_SIMP_TAC [← GSYM VSUM_LMUL, AFFINE_HULL_FINITE, IN_ELIM_THM] THEN
      EXISTS_TAC (← q r"(\x. inv(&1 - k) * c x):real^N->real") THEN
      REWRITE_TAC [VECTOR_MUL_ASSOC, SUM_LMUL] THEN
      MATCH_MP_TAC (← REAL_FIELD
       (← q r"~(k = &1) /\ f = &1 - k ==> inv(&1 - k) * f = &1")) THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"sum(s DIFF f) c = sum s c - sum f (c:real^N->real)")
      MP_TAC THENL [ASM_MESON_TAC [SUM_DIFF], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"sum s (c:real^N->real) = &1") SUBST1_TAC THENL
       [EXPAND_TAC "c" THEN REWRITE_TAC [VECTOR_ADD_RDISTRIB] THEN
        ASM_SIMP_TAC [SUM_ADD, ← GSYM REAL_MUL_ASSOC, SUM_LMUL],
        ALL_TAC] THEN
      REAL_ARITH_TAC))

  let FACE_OF_CONVEX_HULL_INSERT ← prove
   r"!f s a:real^N.
        FINITE s /\ ~(a IN affine hull s) /\ f face_of (convex hull s)
        ==> f face_of (convex hull (a INSERT s))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FACE_OF_TRANS THEN
    EXISTS_TAC (← q r"convex hull s:real^N->bool") THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC FACE_OF_CONVEX_HULLS THEN
    ASM_REWRITE_TAC [FINITE_INSERT, ← SET_RULE (← q r"s SUBSET a INSERT s")] THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
     (← q r"~(a IN s) ==> t SUBSET {a} ==> DISJOINT s t"))) THEN
    MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_SING] THEN SET_TAC [])

  let FACE_OF_AFFINE_TRIVIAL ← prove
   r"!s f:real^N->bool.
        affine s /\ f face_of s ==> f = {} \/ f = s"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"f:real^N->bool = {}") THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"a:real^N")) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"b:real^N") THEN DISCH_TAC THEN
    ASM_CASES_TAC (← q r"(b:real^N) IN f") THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [face_of]) THEN
    DISCH_THEN (MP_TAC o SPECL [← q r"&2 % a - b:real^N", ← q r"b:real^N", ← q r"a:real^N"] o
               CONJUNCT2 o CONJUNCT2) THEN
    SUBGOAL_THEN (← q r"~(a:real^N = b)") ASSUME_TAC THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    ASM_SIMP_TAC [IN_SEGMENT, ← VECTOR_ARITH (← q r"&2 % a - b:real^N = b <=> a = b")] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [← VECTOR_ARITH (← q r"&2 % a - b:real^N = a + &1 % (a - b)")] THEN
      MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN ASM SET_TAC [],
      EXISTS_TAC (← q r"&1 / &2") THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      VECTOR_ARITH_TAC])

  let FACE_OF_AFFINE_EQ ← prove
   r"!s:real^N->bool f. affine s ==> (f face_of s <=> f = {} \/ f = s)"
   (MESON_TAC [FACE_OF_AFFINE_TRIVIAL, EMPTY_FACE_OF, FACE_OF_REFL,
               AFFINE_IMP_CONVEX])

  let INTERS_FACES_FINITE_BOUND ← prove
   r"!s f:(real^N->bool)->bool.
        convex s /\ (!c. c IN f ==> c face_of s)
        ==> ?f'. FINITE f' /\ f' SUBSET f /\ CARD f' <= dimindex(:N) + 1 /\
                 INTERS f' = INTERS f"
   (SUBGOAL_THEN
     (← q r"!s f:(real^N->bool)->bool.
          convex s /\ (!c. c IN f ==> c face_of s /\ ~(c = s))
          ==> ?f'. FINITE f' /\ f' SUBSET f /\ CARD f' <= dimindex(:N) + 1 /\
                   INTERS f' = INTERS f")
    ASSUME_TAC THENL
     [ALL_TAC,
      REPEAT STRIP_TAC THEN
      ASM_CASES_TAC (← q r"(s:real^N->bool) IN f") THENL
       [ALL_TAC, FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC []] THEN
      FIRST_ASSUM (DISJ_CASES_THEN2 SUBST1_TAC MP_TAC o MATCH_MP (← SET_RULE
       (← q r"s IN f ==> f = {s} \/ ?t. ~(t = s) /\ t IN f"))) THENL
       [EXISTS_TAC (← q r"{s:real^N->bool}") THEN
        SIMP_TAC [FINITE_INSERT, FINITE_EMPTY, SUBSET_REFL, CARD_CLAUSES] THEN
        ARITH_TAC,
        DISCH_THEN (X_CHOOSE_THEN (← q r"t:real^N->bool") STRIP_ASSUME_TAC)] THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"s:real^N->bool", ← q r"f DELETE
        (s:real^N->bool)"]) THEN
      ASM_SIMP_TAC [IN_DELETE, SUBSET_DELETE] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f':(real^N->bool)->bool") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"f = (s:real^N->bool) INSERT (f DELETE s)") MP_TAC THENL
       [ASM SET_TAC [],
        DISCH_THEN (fun th => GEN_REWRITE_TAC (funpow 2 RAND_CONV) [th])] THEN
      REWRITE_TAC [INTERS_INSERT] THEN
      MATCH_MP_TAC (← SET_RULE (← q r"t SUBSET s ==> t = s INTER t")) THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"t:real^N->bool")) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (ASSUME_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC (← q r"t:real^N->bool") THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET, IN_INTERS, IN_DELETE] THEN
      ASM SET_TAC []] THEN
    REPEAT STRIP_TAC THEN ASM_CASES_TAC
     (← q r"!f':(real^N->bool)->bool.
          FINITE f' /\ f' SUBSET f /\ CARD f' <= dimindex(:N) + 1
          ==> ?c. c IN f /\ c INTER (INTERS f') PSUBSET (INTERS f')")
    THENL
     [ALL_TAC,
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
      SIMP_TAC [NOT_IMP, ← GSYM CONJ_ASSOC] THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ASM_REWRITE_TAC [PSUBSET, INTER_SUBSET] THEN ASM SET_TAC []] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE BINDER_CONV
     [RIGHT_IMP_EXISTS_THM]) THEN
    REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"c:((real^N->bool)->bool)->real^N->bool") THEN DISCH_TAC THEN
    CHOOSE_TAC (← prove_recursive_functions_exist num_RECURSION
     (← q r"d 0 = {c {} :real^N->bool} /\ !n. d(SUC n) = c(d n) INSERT d n")) THEN
    SUBGOAL_THEN (← q r"!n:num. ~(d n:(real^N->bool)->bool = {})") ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM_REWRITE_TAC [] THEN SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!n. n <= dimindex(:N) + 1
          ==> (d n) SUBSET (f:(real^N->bool)->bool) /\
              FINITE(d n) /\ CARD(d n) <= n + 1")
    ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM_REWRITE_TAC [] THEN
      ASM_SIMP_TAC [INSERT_SUBSET, CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY,
        EMPTY_SUBSET, ← ARITH_RULE (← q r"SUC n <= m + 1 ==> n <= m + 1")] THEN
      REPEAT STRIP_TAC THEN TRY ASM_ARITH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(d:num->(real^N->bool)->bool) n")) THEN
      FIRST_X_ASSUM (MP_TAC o check (HolCore.Basics.is_imp o concl)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, STRIP_TAC] THEN ASM_REWRITE_TAC [] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, SIMP_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!n. n <= dimindex(:N)
          ==> (INTERS(d(SUC n)):real^N->bool) PSUBSET INTERS(d n)")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [INTERS_INSERT] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(d:num->(real^N->bool)->bool) n")) THEN
      ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"n:num"))) THEN
      ASM_SIMP_TAC [← ARITH_RULE (← q r"n <= N ==> n <= N + 1")] THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    FIRST_X_ASSUM (CONJUNCTS_THEN (K ALL_TAC : thm → tactic)) THEN
    SUBGOAL_THEN
     (← q r"!n. n <= dimindex(:N) + 1
          ==> aff_dim(INTERS(d n):real^N->bool) < &(dimindex(:N)) - &n")
    MP_TAC THENL
     [INDUCT_TAC THENL
       [DISCH_TAC THEN REWRITE_TAC [INT_SUB_RZERO] THEN
        MATCH_MP_TAC INT_LTE_TRANS THEN
        EXISTS_TAC (← q r"aff_dim(s:real^N->bool)") THEN
        REWRITE_TAC [AFF_DIM_LE_UNIV] THEN
        MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
        ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
         [MATCH_MP_TAC FACE_OF_INTERS THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC [],
          FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY] o
            SPEC (← q r"0")) THEN
          DISCH_THEN (X_CHOOSE_TAC (← q r"e:real^N->bool")) THEN
          FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e:real^N->bool")) THEN
          ANTS_TAC THENL [ASM SET_TAC [], STRIP_TAC] THEN
          MATCH_MP_TAC (← SET_RULE
           (← q r"!t. t PSUBSET s /\ u SUBSET t ==> ~(u = s)")) THEN
          EXISTS_TAC (← q r"e:real^N->bool") THEN
          FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
          ASM SET_TAC []],
        DISCH_TAC THEN REWRITE_TAC [← GSYM INT_OF_NUM_SUC] THEN
        MATCH_MP_TAC (← INT_ARITH
         (← q r"!d':int. d < d' /\ d' < m - n ==> d < m - (n + &1)")) THEN
        EXISTS_TAC (← q r"aff_dim(INTERS(d(n:num)):real^N->bool)") THEN
        ASM_SIMP_TAC [← ARITH_RULE (← q r"SUC n <= k + 1 ==> n <= k + 1")] THEN
        MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
        ASM_SIMP_TAC [← ARITH_RULE (← q r"SUC n <= m + 1 ==> n <= m"),
                      ← SET_RULE (← q r"s PSUBSET t ==> ~(s = t)")] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CONVEX_INTERS THEN
          REPEAT STRIP_TAC THEN MATCH_MP_TAC FACE_OF_IMP_CONVEX THEN
          EXISTS_TAC (← q r"s:real^N->bool") THEN
          ASM_MESON_TAC [SUBSET, ← ARITH_RULE (← q r"SUC n <= m + 1 ==> n <= m + 1")],
          ALL_TAC] THEN
        MP_TAC (← ISPECL [← q r"INTERS(d(SUC n)):real^N->bool", ← q r"s:real^N->bool",
                          ← q r"INTERS(d(n:num)):real^N->bool"] FACE_OF_FACE) THEN
        ASM_SIMP_TAC [← SET_RULE (← q r"s PSUBSET t ==> s SUBSET t"),
                      ← ARITH_RULE (← q r"SUC n <= m + 1 ==> n <= m")] THEN
        MATCH_MP_TAC (← TAUT (← q r"a /\ b ==> (a ==> (c <=> b)) ==> c")) THEN
        CONJ_TAC THEN MATCH_MP_TAC FACE_OF_INTERS THEN ASM_REWRITE_TAC [] THEN
        ASM_MESON_TAC [SUBSET, ← ARITH_RULE (← q r"SUC n <= m + 1 ==> n <= m + 1")]],
      ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"dimindex(:N) + 1")) THEN REWRITE_TAC [LE_REFL] THEN
    MATCH_MP_TAC (← TAUT (← q r"~p ==> p ==> q")) THEN REWRITE_TAC [INT_NOT_LT] THEN
    REWRITE_TAC [← GSYM INT_OF_NUM_ADD, ← INT_ARITH (← q r"d - (d + &1):int = -- &1")] THEN
    REWRITE_TAC [AFF_DIM_GE])

  let INTERS_FACES_FINITE_ALTBOUND ← prove
   r"!s f:(real^N->bool)->bool.
        (!c. c IN f ==> c face_of s)
        ==> ?f'. FINITE f' /\ f' SUBSET f /\ CARD f' <= dimindex(:N) + 2 /\
                 INTERS f' = INTERS f"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC
     (← q r"!f':(real^N->bool)->bool.
          FINITE f' /\ f' SUBSET f /\ CARD f' <= dimindex(:N) + 2
          ==> ?c. c IN f /\ c INTER (INTERS f') PSUBSET (INTERS f')")
    THENL
     [ALL_TAC,
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
      SIMP_TAC [NOT_IMP, ← GSYM CONJ_ASSOC] THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ASM_REWRITE_TAC [PSUBSET, INTER_SUBSET] THEN ASM SET_TAC []] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE BINDER_CONV
     [RIGHT_IMP_EXISTS_THM]) THEN
    REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"c:((real^N->bool)->bool)->real^N->bool") THEN DISCH_TAC THEN
    CHOOSE_TAC (← prove_recursive_functions_exist num_RECURSION
     (← q r"d 0 = {c {} :real^N->bool} /\ !n. d(SUC n) = c(d n) INSERT d n")) THEN
    SUBGOAL_THEN (← q r"!n:num. ~(d n:(real^N->bool)->bool = {})") ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM_REWRITE_TAC [] THEN SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!n. n <= dimindex(:N) + 2
          ==> (d n) SUBSET (f:(real^N->bool)->bool) /\
              FINITE(d n) /\ CARD(d n) <= n + 1")
    ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM_REWRITE_TAC [] THEN
      ASM_SIMP_TAC [INSERT_SUBSET, CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY,
        EMPTY_SUBSET, ← ARITH_RULE (← q r"SUC n <= m + 2 ==> n <= m + 2")] THEN
      REPEAT STRIP_TAC THEN TRY ASM_ARITH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(d:num->(real^N->bool)->bool) n")) THEN
      FIRST_X_ASSUM (MP_TAC o check (HolCore.Basics.is_imp o concl)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, STRIP_TAC] THEN ASM_REWRITE_TAC [] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, SIMP_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!n. n <= dimindex(:N) + 1
          ==> (INTERS(d(SUC n)):real^N->bool) PSUBSET INTERS(d n)")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [INTERS_INSERT] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(d:num->(real^N->bool)->bool) n")) THEN
      ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"n:num"))) THEN
      ASM_SIMP_TAC [← ARITH_RULE (← q r"n <= N + 1 ==> n <= N + 2")] THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    FIRST_X_ASSUM (CONJUNCTS_THEN (K ALL_TAC : thm → tactic)) THEN
    SUBGOAL_THEN
     (← q r"!n. n <= dimindex(:N) + 2
          ==> aff_dim(INTERS(d n):real^N->bool) <= &(dimindex(:N)) - &n")
    MP_TAC THENL
     [INDUCT_TAC THEN REWRITE_TAC [INT_SUB_RZERO, AFF_DIM_LE_UNIV] THEN
      DISCH_TAC THEN REWRITE_TAC [← GSYM INT_OF_NUM_SUC] THEN
      MATCH_MP_TAC (← INT_ARITH
       (← q r"!d':int. d < d' /\ d' <= m - n ==> d <= m - (n + &1)")) THEN
      EXISTS_TAC (← q r"aff_dim(INTERS(d(n:num)):real^N->bool)") THEN
      ASM_SIMP_TAC [← ARITH_RULE (← q r"SUC n <= k + 2 ==> n <= k + 2")] THEN
      MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
      ASM_SIMP_TAC [← ARITH_RULE (← q r"SUC n <= m + 2 ==> n <= m + 1"),
                    ← SET_RULE (← q r"s PSUBSET t ==> ~(s = t)")] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONVEX_INTERS THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC FACE_OF_IMP_CONVEX THEN
        EXISTS_TAC (← q r"s:real^N->bool") THEN
        ASM_MESON_TAC [SUBSET, ← ARITH_RULE (← q r"SUC n <= m + 2 ==> n <= m + 2")],
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"INTERS(d(SUC n)):real^N->bool", ← q r"s:real^N->bool",
                        ← q r"INTERS(d(n:num)):real^N->bool"] FACE_OF_FACE) THEN
      ASM_SIMP_TAC [← SET_RULE (← q r"s PSUBSET t ==> s SUBSET t"),
                    ← ARITH_RULE (← q r"SUC n <= m + 2 ==> n <= m + 1")] THEN
      MATCH_MP_TAC (← TAUT (← q r"a /\ b ==> (a ==> (c <=> b)) ==> c")) THEN
      CONJ_TAC THEN MATCH_MP_TAC FACE_OF_INTERS THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [SUBSET, ← ARITH_RULE (← q r"SUC n <= m + 2 ==> n <= m + 2")],
      ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"dimindex(:N) + 2")) THEN REWRITE_TAC [LE_REFL] THEN
    MATCH_MP_TAC (← TAUT (← q r"~p ==> p ==> q")) THEN REWRITE_TAC [INT_NOT_LE] THEN
    REWRITE_TAC [← GSYM INT_OF_NUM_ADD, ← INT_ARITH
      (← q r"d - (d + &2):int < i <=> -- &1 <= i")] THEN
    REWRITE_TAC [AFF_DIM_GE])

  pure { FACE_OF_CONVEX_HULLS, FACE_OF_CONVEX_HULL_INSERT, FACE_OF_AFFINE_TRIVIAL,
         FACE_OF_AFFINE_EQ, INTERS_FACES_FINITE_BOUND, INTERS_FACES_FINITE_ALTBOUND }

/- ------------------------------------------------------------------------- -/
/- Faces under images and products; halfspaces; facial partitions.          -/
/- (polytope.ml 785-1184)                                                    -/
/- ------------------------------------------------------------------------- -/

structure POC where
  FACES_OF_TRANSLATION : thm
  FACES_OF_LINEAR_IMAGE : thm
  FACE_OF_CONIC : thm
  FACE_OF_PCROSS : thm
  FACE_OF_PCROSS_DECOMP : thm
  FACE_OF_PCROSS_EQ : thm
  HYPERPLANE_FACE_OF_HALFSPACE_LE : thm
  HYPERPLANE_FACE_OF_HALFSPACE_GE : thm
  FACE_OF_HALFSPACE_LE : thm
  FACE_OF_HALFSPACE_GE : thm
  RELATIVE_BOUNDARY_POINT_IN_PROPER_FACE : thm
  RELATIVE_FRONTIER_OF_CONVEX_CLOSED : thm
  IN_RELATIVE_INTERIOR_OF_FACE : thm
  CONVEX_FACIAL_PARTITION : thm
  IN_RELATIVE_INTERIOR_OF_UNIQUE_FACE : thm
  RELATIVE_INTERIOR_SUBSET_OF_PROPER_FACE : thm
  CONVEX_RELATIVE_BOUNDARY_SUBSET_OF_PROPER_FACE : thm
  RELATIVE_FRONTIER_FACIAL_PARTITION_ALT : thm
  RELATIVE_FRONTIER_FACIAL_PARTITION : thm
  FRONTIER_OF_CONVEX_CLOSED : thm
  FACE_OF_INTER_AS_INTER_OF_FACE : thm
  deriving Inhabited

set_option maxHeartbeats 4000000 in
@[nospecialize]
def setupPOC [HolBase] (D : PolytopeDeps) (BPOA : POA) (BPOB : POB) : ExceptT String IO POC := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC, REAL_ARITH, REAL_FIELD, SET_RULE,
        SET_TAC, VECTOR_ARITH, .. } := D.cvx
  let { AND_FORALL_THM, CONJ_ASSOC, DISJOINT, EMPTY_UNIONS, EQ_SYM_EQ, EXISTS_PASTECART,
        EXISTS_REFL, EXTENSION, FORALL_IN_GSPEC, .. } := D.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_IN_PCROSS, FORALL_PASTECART, FSTCART_PASTECART,
        IMAGE_SUBSET, IMP_CONJ, IMP_CONJ_ALT, IMP_IMP, IN_DIFF, INT_LT_LE, INTER_EMPTY,
        INTER_UNIONS, .. } := D.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, IN_INTER, LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM,
        MEMBER_NOT_EMPTY, MONO_EXISTS, NOT_IMP, PASTECART_IN_PCROSS, PASTECART_INJ,
        PCROSS_EMPTY, PCROSS_MONO, .. } := D.cvx.core3
  let { REAL_EQ_NEG2, REAL_LE_NEG2, REAL_LT_IMP_NE, REAL_LT_LDIV_EQ, REAL_LT_RDIV_EQ, .. }
        := D.cvx.core4
  let { REAL_SUB_LT, RIGHT_AND_EXISTS_THM, RIGHT_EXISTS_AND_THM, RIGHT_FORALL_IMP_THM,
        RIGHT_IMP_FORALL_THM, SNDCART_PASTECART, SUBSET, SUBSET_ANTISYM_EQ, SUBSET_IMAGE,
        SUBSET_REFL, .. } := D.cvx.core5
  let { real_ge, SURJECTIVE_IMAGE_EQ, UNIONS_GSPEC, UNIONS_INSERT, UNIONS_SUBSET,
        UNWIND_THM1, .. } := D.cvx.core6
  let { DOT_LNEG, DOT_LZERO, .. } := D.cvx.vec1
  let { HALFSPACE_EQ_EMPTY_LT, LINEAR_FSTCART, LINEAR_SNDCART, .. } := D.cvx.vec2
  let { PASTECART_ADD, PASTECART_CMUL, TRANSLATION_GALOIS, .. } := D.cvx.vec3
  let { VECTOR_ADD_RDISTRIB, VECTOR_MUL_ASSOC, VECTOR_MUL_EQ_0, VECTOR_MUL_LID,
        VECTOR_MUL_RCANCEL, VECTOR_MUL_RZERO, .. } := D.cvx.vec4
  let { CLOSURE_CLOSED, .. } := D.cvx.top1
  let { CLOSURE_SUBSET, .. } := D.cvx.top2
  let { IN_SEGMENT, .. } := D.cvx.top4
  let { frontier, SUBSET_INTERIOR, .. } := D.cvx.top5
  let { DISJ_ACI, EXISTS_UNIQUE_DEF, IMAGE_FSTCART_PCROSS, IMAGE_SNDCART_PCROSS,
        INT_LT_REFL, PCROSS_EQ, .. } := D.qses
  let { CLOSED_HALFSPACE_LE, FRONTIER_HALFSPACE_LE, INTERIOR_HALFSPACE_LE,
        OPEN_SEGMENT_LINEAR_IMAGE, .. } := D.qtop
  let { AFF_DIM_EQ_FULL, AFF_DIM_LE_UNIV, AFFINE_HYPERPLANE, AFFINE_UNIV, .. } := D.qcvx1
  let { CONVEX_HALFSPACE_GE, CONVEX_HALFSPACE_LE, CONVEX_LINEAR_IMAGE,
        CONVEX_LINEAR_IMAGE_EQ, .. } := D.qcvx2
  let { conic, CONVEX_PCROSS, INTER_RELATIVE_INTERIOR_SUBSET, relative_frontier,
        RELATIVE_FRONTIER_NONEMPTY_INTERIOR, RELATIVE_INTERIOR_EQ_EMPTY,
        RELATIVE_INTERIOR_INTERIOR, RELATIVE_INTERIOR_LINEAR_IMAGE_CONVEX,
        RELATIVE_INTERIOR_PCROSS, RELATIVE_INTERIOR_SUBSET,
        SUPPORTING_HYPERPLANE_RELATIVE_FRONTIER, .. } := D.qcvx3
  let { EMPTY_FACE_OF, face_of, FACE_OF_AFF_DIM_LT, FACE_OF_EMPTY, FACE_OF_EQ,
        FACE_OF_IMP_CONVEX, FACE_OF_IMP_SUBSET, FACE_OF_INTER_INTER,
        FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE, FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE,
        FACE_OF_INTERS, FACE_OF_REFL, FACE_OF_SUBSET, FACE_OF_SUBSET_FRONTIER_AFF_DIM,
        FACE_OF_SUBSET_RELATIVE_BOUNDARY, FACE_OF_SUBSET_RELATIVE_FRONTIER, FACE_OF_TRANS,
        FACE_OF_TRANSLATION_EQ, SUBSET_OF_FACE_OF, .. } := BPOA
  let { FACE_OF_AFFINE_EQ, .. } := BPOB
  -- @@SCOPE END

  let FACES_OF_TRANSLATION ← prove
   r"!s a:real^N.
        {f | f face_of IMAGE (\x. a + x) s} =
        IMAGE (IMAGE (\x. a + x)) {f | f face_of s}"
   (REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    REWRITE_TAC [IN_ELIM_THM, FACE_OF_TRANSLATION_EQ] THEN
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    ONCE_REWRITE_TAC [TRANSLATION_GALOIS] THEN
    REWRITE_TAC [EXISTS_REFL])

  let FACES_OF_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> {t | t face_of (IMAGE f s)} = IMAGE (IMAGE f) {t | t face_of s}"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [face_of, SUBSET_IMAGE, ← SET_RULE
     (← q r"{y | (?x. P x /\ y = f x) /\ Q y} = {f x |x| P x /\ Q(f x)}")] THEN
    REWRITE_TAC [← SET_RULE (← q r"IMAGE f {x | P x} = {f x | P x}")] THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE] THEN
    FIRST_ASSUM (fun th => tactic_of do
     pure (REWRITE_TAC [← MATCH_MP CONVEX_LINEAR_IMAGE_EQ th,
                        ← MATCH_MP OPEN_SEGMENT_LINEAR_IMAGE th,
                        ← MATCH_MP (← SET_RULE
     (← q r"(!x y. f x = f y ==> x = y)  ==> (!s x. f x IN IMAGE f s <=> x IN s)"))
     (← CONJUNCT2 th)])))

  let FACE_OF_CONIC ← prove
   r"!s f:real^N->bool. conic s /\ f face_of s ==> conic f"
   (REPEAT GEN_TAC THEN REWRITE_TAC [face_of, conic] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"x:real^N", ← q r"c:real"] THEN STRIP_TAC THEN
    ASM_CASES_TAC (← q r"x:real^N = vec 0") THENL
     [ASM_MESON_TAC [VECTOR_MUL_RZERO], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"c = &1") THENL
     [ASM_MESON_TAC [VECTOR_MUL_LID], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"?d e. &0 <= d /\ &0 <= e /\ d < &1 /\ &1 < e /\ d < e /\
                        (d = c \/ e = c)")
    MP_TAC THENL
     [FIRST_X_ASSUM (DISJ_CASES_TAC o MATCH_MP (← REAL_ARITH
       (← q r"~(c = &1) ==> c < &1 \/ &1 < c")))
      THENL
       [MAP_EVERY EXISTS_TAC [← q r"c:real", ← q r"&2"] THEN ASM_REAL_ARITH_TAC,
        MAP_EVERY EXISTS_TAC [← q r"&1 / &2", ← q r"c:real"] THEN ASM_REAL_ARITH_TAC],
      DISCH_THEN (REPEAT_TCL CHOOSE_THEN
        (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      FIRST_X_ASSUM (MP_TAC o SPECL
       [← q r"d % x :real^N", ← q r"e % x:real^N", ← q r"x:real^N"]) THEN
      ANTS_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
      SUBGOAL_THEN (← q r"(x:real^N) IN s") ASSUME_TAC THENL
       [ASM SET_TAC [], ASM_SIMP_TAC [IN_SEGMENT]] THEN
      ASM_SIMP_TAC [VECTOR_MUL_RCANCEL, REAL_LT_IMP_NE] THEN
      EXISTS_TAC (← q r"(&1 - d) / (e - d)") THEN
      ASM_SIMP_TAC [REAL_LT_LDIV_EQ, REAL_LT_RDIV_EQ, REAL_SUB_LT] THEN
      REPEAT (CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
      REWRITE_TAC [VECTOR_MUL_ASSOC, ← GSYM VECTOR_ADD_RDISTRIB] THEN
      REWRITE_TAC [← VECTOR_ARITH (← q r"x:real^N = a % x <=> (a - &1) % x = vec 0")] THEN
      ASM_REWRITE_TAC [VECTOR_MUL_EQ_0] THEN
      UNDISCH_TAC (← q r"d:real < e") THEN CONV_TAC (fun t => REAL_FIELD t)])

  let FACE_OF_PCROSS ← prove
   r"!f s:real^M->bool f' s':real^N->bool.
        f face_of s /\ f' face_of s' ==> (f PCROSS f') face_of (s PCROSS s')"
   (REPEAT GEN_TAC THEN SIMP_TAC [face_of, CONVEX_PCROSS, PCROSS_MONO] THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC [IN_SEGMENT, FORALL_IN_PCROSS] THEN
    REWRITE_TAC [RIGHT_IMP_FORALL_THM, IMP_IMP, ← GSYM CONJ_ASSOC] THEN
    REWRITE_TAC [← GSYM PASTECART_CMUL, PASTECART_ADD, PASTECART_INJ] THEN
    REWRITE_TAC [PASTECART_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"a:real^M", ← q r"a':real^N", ← q r"b:real^M", ← q r"b':real^N"] THEN
    MAP_EVERY ASM_CASES_TAC [← q r"b:real^M = a", ← q r"b':real^N = a'"] THEN
    ASM_REWRITE_TAC [← VECTOR_ARITH (← q r"(&1 - u) % a + u % a:real^N = a")] THEN
    ASM_MESON_TAC [])

  let FACE_OF_PCROSS_DECOMP ← prove
   r"!s:real^M->bool s':real^N->bool c.
        c face_of (s PCROSS s') <=>
        ?f f'. f face_of s /\ f' face_of s' /\ c = f PCROSS f'"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [ALL_TAC, STRIP_TAC THEN ASM_SIMP_TAC [FACE_OF_PCROSS]] THEN
    ASM_CASES_TAC (← q r"c:real^(M,N)finite_sum->bool = {}") THENL
     [ASM_MESON_TAC [EMPTY_FACE_OF, PCROSS_EMPTY], DISCH_TAC] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP FACE_OF_IMP_CONVEX) THEN
    MAP_EVERY EXISTS_TAC
     [← q r"IMAGE fstcart (c:real^(M,N)finite_sum->bool)",
      ← q r"IMAGE sndcart (c:real^(M,N)finite_sum->bool)"] THEN
    MATCH_MP_TAC (← TAUT (← q r"(p /\ q ==> r) /\ p /\ q ==> p /\ q /\ r")) THEN
    CONJ_TAC THENL
     [STRIP_TAC THEN MATCH_MP_TAC FACE_OF_EQ THEN
      EXISTS_TAC (← q r"(s:real^M->bool) PCROSS (s':real^N->bool)") THEN
      ASM_SIMP_TAC [FACE_OF_PCROSS, RELATIVE_INTERIOR_PCROSS] THEN
      ASM_SIMP_TAC [RELATIVE_INTERIOR_LINEAR_IMAGE_CONVEX,
                    LINEAR_FSTCART, LINEAR_SNDCART] THEN
      MATCH_MP_TAC (← SET_RULE (← q r"~(s = {}) /\ s SUBSET t ==> ~DISJOINT s t")) THEN
      ASM_SIMP_TAC [RELATIVE_INTERIOR_EQ_EMPTY] THEN
      REWRITE_TAC [SUBSET, FORALL_PASTECART, PASTECART_IN_PCROSS, IN_IMAGE] THEN
      REWRITE_TAC [EXISTS_PASTECART, FSTCART_PASTECART, SNDCART_PASTECART] THEN
      MESON_TAC [],
      ALL_TAC] THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [face_of]) THEN
    REWRITE_TAC [face_of] THEN
    ASM_SIMP_TAC [CONVEX_LINEAR_IMAGE, LINEAR_FSTCART, LINEAR_SNDCART] THEN
    FIRST_ASSUM (MP_TAC o ISPEC (← q r"fstcart:real^(M,N)finite_sum->real^M") o
          MATCH_MP IMAGE_SUBSET) THEN
    FIRST_ASSUM (MP_TAC o ISPEC (← q r"sndcart:real^(M,N)finite_sum->real^N") o
          MATCH_MP IMAGE_SUBSET) THEN
    REWRITE_TAC [IMAGE_FSTCART_PCROSS, IMAGE_SNDCART_PCROSS] THEN
    REPEAT (DISCH_THEN (ASSUME_TAC o MATCH_MP (← SET_RULE
     (← q r"s SUBSET (if p then {} else t) ==> s SUBSET t")))) THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q r"a:real^M", ← q r"b:real^M", ← q r"x:real^M"] THEN
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
      REWRITE_TAC [EXISTS_PASTECART, FSTCART_PASTECART] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"y:real^N")) THEN FIRST_X_ASSUM (MP_TAC o SPECL
       [← q r"pastecart (a:real^M) (y:real^N)",
        ← q r"pastecart (b:real^M) (y:real^N)",
        ← q r"pastecart (x:real^M) (y:real^N)"]) THEN
      ASM_REWRITE_TAC [PASTECART_IN_PCROSS, IN_IMAGE, EXISTS_PASTECART] THEN
      REWRITE_TAC [FSTCART_PASTECART, RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
      ANTS_TAC THENL [ALL_TAC, MESON_TAC []] THEN
      UNDISCH_TAC (← q r"(c:real^(M,N)finite_sum->bool) SUBSET s PCROSS s'") THEN
      REWRITE_TAC [SUBSET] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"pastecart (x:real^M) (y:real^N)")),
      MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"b:real^N", ← q r"x:real^N"] THEN
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
      REWRITE_TAC [EXISTS_PASTECART, SNDCART_PASTECART] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"y:real^M")) THEN FIRST_X_ASSUM (MP_TAC o SPECL
       [← q r"pastecart (y:real^M) (a:real^N)",
        ← q r"pastecart (y:real^M) (b:real^N)",
        ← q r"pastecart (y:real^M) (x:real^N)"]) THEN
      ASM_REWRITE_TAC [PASTECART_IN_PCROSS, IN_IMAGE, EXISTS_PASTECART] THEN
      REWRITE_TAC [SNDCART_PASTECART, RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
      ANTS_TAC THENL [ALL_TAC, MESON_TAC []] THEN
      UNDISCH_TAC (← q r"(c:real^(M,N)finite_sum->bool) SUBSET s PCROSS s'") THEN
      REWRITE_TAC [SUBSET] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"pastecart (y:real^M) (x:real^N)"))] THEN
    ASM_REWRITE_TAC [PASTECART_IN_PCROSS] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT]) THEN
    REWRITE_TAC [IN_SEGMENT, PASTECART_INJ] THEN
    REWRITE_TAC [PASTECART_ADD, ← GSYM PASTECART_CMUL,
                 ← VECTOR_ARITH (← q r"(&1 - u) % a + u % a:real^N = a")] THEN
    MESON_TAC [])

  let FACE_OF_PCROSS_EQ ← prove
   r"!f s:real^M->bool f' s':real^N->bool.
        (f PCROSS f') face_of (s PCROSS s') <=>
        f = {} \/ f' = {} \/ f face_of s /\ f' face_of s'"
   (REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC
     [← q r"f:real^M->bool = {}", ← q r"f':real^N->bool = {}"] THEN
    ASM_REWRITE_TAC [PCROSS_EMPTY, EMPTY_FACE_OF] THEN
    ASM_REWRITE_TAC [FACE_OF_PCROSS_DECOMP, PCROSS_EQ] THEN MESON_TAC [])

  let HYPERPLANE_FACE_OF_HALFSPACE_LE ← prove
   r"!a:real^N b. {x | a dot x = b} face_of {x | a dot x <= b}"
   (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"a:real = b <=> a <= b /\ a = b")] THEN
    REWRITE_TAC [← SET_RULE (← q r"{x | P x /\ Q x} = {x | P x} INTER {x | Q x}")] THEN
    MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
    REWRITE_TAC [IN_ELIM_THM, CONVEX_HALFSPACE_LE])

  let HYPERPLANE_FACE_OF_HALFSPACE_GE ← prove
   r"!a:real^N b. {x | a dot x = b} face_of {x | a dot x >= b}"
   (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"a:real = b <=> a >= b /\ a = b")] THEN
    REWRITE_TAC [← SET_RULE (← q r"{x | P x /\ Q x} = {x | P x} INTER {x | Q x}")] THEN
    MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE THEN
    REWRITE_TAC [IN_ELIM_THM, CONVEX_HALFSPACE_GE])

  let FACE_OF_HALFSPACE_LE ← prove
   r"!f a:real^N b.
         f face_of {x | a dot x <= b} <=>
         f = {} \/ f = {x | a dot x = b} \/ f = {x | a dot x <= b}"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"a:real^N = vec 0") THENL
     [ASM_SIMP_TAC [DOT_LZERO, ← SET_RULE (← q r"{x | p} = if p then UNIV else {}")] THEN
      REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [FACE_OF_EMPTY]) THEN
      ASM_SIMP_TAC [FACE_OF_AFFINE_EQ, AFFINE_UNIV, DISJ_ACI] THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    EQ_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC [EMPTY_FACE_OF, FACE_OF_REFL, CONVEX_HALFSPACE_LE,
                  HYPERPLANE_FACE_OF_HALFSPACE_LE] THEN
    MATCH_MP_TAC (← TAUT (← q r"(~r ==> p \/ q) ==> p \/ q \/ r")) THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"f face_of {x:real^N | a dot x = b}") MP_TAC THENL
     [ASM_SIMP_TAC [← GSYM FRONTIER_HALFSPACE_LE] THEN
      ASM_SIMP_TAC [← CONV_RULE (RAND_CONV SYM_CONV)
                     (← SPEC_ALL RELATIVE_FRONTIER_NONEMPTY_INTERIOR),
                    INTERIOR_HALFSPACE_LE, HALFSPACE_EQ_EMPTY_LT] THEN
      MATCH_MP_TAC FACE_OF_SUBSET THEN
      EXISTS_TAC (← q r"{x:real^N | a dot x <= b}") THEN
      ASM_SIMP_TAC [FACE_OF_SUBSET_RELATIVE_FRONTIER] THEN
      ASM_SIMP_TAC [relative_frontier, CLOSURE_CLOSED, CLOSED_HALFSPACE_LE] THEN
      SET_TAC [],
      ASM_SIMP_TAC [FACE_OF_AFFINE_EQ, AFFINE_HYPERPLANE]])

  let FACE_OF_HALFSPACE_GE ← prove
   r"!f a:real^N b.
         f face_of {x | a dot x >= b} <=>
         f = {} \/ f = {x | a dot x = b} \/ f = {x | a dot x >= b}"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^N->bool", ← q r"--a:real^N", ← q r"--b:real"]
          FACE_OF_HALFSPACE_LE) THEN
    REWRITE_TAC [DOT_LNEG, REAL_LE_NEG2, REAL_EQ_NEG2, real_ge])

  let RELATIVE_BOUNDARY_POINT_IN_PROPER_FACE ← prove
   r"!s x:real^N.
        convex s /\ x IN s /\ ~(x IN relative_interior s)
        ==> ?f. f face_of s /\ ~(f = s) /\ x IN f"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"x:real^N"]
          SUPPORTING_HYPERPLANE_RELATIVE_FRONTIER) THEN
    ASM_SIMP_TAC [relative_frontier, IN_DIFF,
                  ← REWRITE_RULE [SUBSET] CLOSURE_SUBSET] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"a:real^N") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"s INTER {y:real^N | a dot y = a dot x}") THEN
    ASM_REWRITE_TAC [IN_INTER, IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE THEN
      ASM_MESON_TAC [SUBSET, CLOSURE_SUBSET, real_ge],
      SUBGOAL_THEN (← q r"~(relative_interior s:real^N->bool = {})") MP_TAC THENL
       [ASM_SIMP_TAC [RELATIVE_INTERIOR_EQ_EMPTY] THEN ASM SET_TAC [],
        MATCH_MP_TAC (← SET_RULE
         (← q r"(!x. x IN i ==> x IN s /\ ~(x IN t)) ==> ~(i = {}) ==> ~(t = s)")) THEN
        X_GEN_TAC (← q r"y:real^N") THEN DISCH_TAC THEN
        ASM_SIMP_TAC [IN_INTER, ← REWRITE_RULE [SUBSET]
                      RELATIVE_INTERIOR_SUBSET] THEN
        ASM_SIMP_TAC [IN_ELIM_THM, REAL_LT_IMP_NE]]])

  let RELATIVE_FRONTIER_OF_CONVEX_CLOSED ← prove
   r"!s:real^N->bool.
        convex s /\ closed s
        ==> relative_frontier s = UNIONS {f | f face_of s /\ ~(f = s)}"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [EXTENSION] THEN
    ASM_SIMP_TAC [relative_frontier, UNIONS_GSPEC, IN_ELIM_THM,
                  CLOSURE_CLOSED, IN_DIFF] THEN
    X_GEN_TAC (← q r"x:real^N") THEN EQ_TAC THENL
     [ASM_MESON_TAC [RELATIVE_BOUNDARY_POINT_IN_PROPER_FACE], ALL_TAC] THEN
    DISCH_THEN (CHOOSE_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_THEN (MP_TAC o MATCH_MP FACE_OF_SUBSET_RELATIVE_BOUNDARY) THEN
    ASM SET_TAC [])

  let IN_RELATIVE_INTERIOR_OF_FACE ← prove
   r"!s:real^N->bool x.
        convex s /\ x IN s ==> ?f. f face_of s /\ x IN relative_interior f"
   (REPEAT STRIP_TAC THEN
    EXISTS_TAC (← q r"INTERS {f | f face_of s /\ (x:real^N) IN f}") THEN
    MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
     [MATCH_MP_TAC FACE_OF_INTERS THEN
      SIMP_TAC [FORALL_IN_GSPEC, ← GSYM MEMBER_NOT_EMPTY] THEN
      REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [FACE_OF_REFL],
      DISCH_TAC] THEN
    MATCH_MP_TAC (← SET_RULE
     (← q r"x IN s /\ ~(x IN s /\ ~(x IN relative_interior s))
      ==> x IN relative_interior s")) THEN
    CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN DISCH_THEN (MP_TAC o MATCH_MP
     (← ONCE_REWRITE_RULE [IMP_CONJ_ALT]
        RELATIVE_BOUNDARY_POINT_IN_PROPER_FACE)) THEN
    REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL
     [ASM_MESON_TAC [FACE_OF_IMP_CONVEX], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"f:real^N->bool") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
     (← q r"~(s = t) ==> s SUBSET t /\ t SUBSET s ==> F"))) THEN
    ASM_SIMP_TAC [FACE_OF_IMP_SUBSET] THEN
    MATCH_MP_TAC (← SET_RULE (← q r"f IN t ==> INTERS t SUBSET f")) THEN
    ASM_REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [FACE_OF_TRANS])

  let CONVEX_FACIAL_PARTITION ← prove
   r"!s:real^N->bool.
        convex s ==> UNIONS {relative_interior f | f face_of s} = s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [UNIONS_GSPEC, EXTENSION, IN_ELIM_THM] THEN
    ASM_MESON_TAC [IN_RELATIVE_INTERIOR_OF_FACE, FACE_OF_IMP_SUBSET, SUBSET,
                   RELATIVE_INTERIOR_SUBSET])

  let IN_RELATIVE_INTERIOR_OF_UNIQUE_FACE ← prove
   r"!s:real^N->bool x.
        convex s /\ x IN s ==> ?!f. f face_of s /\ x IN relative_interior f"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [EXISTS_UNIQUE_DEF] THEN
    ASM_SIMP_TAC [IN_RELATIVE_INTERIOR_OF_FACE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FACE_OF_EQ THEN
    EXISTS_TAC (← q r"s:real^N->bool") THEN ASM SET_TAC [])

  let RELATIVE_INTERIOR_SUBSET_OF_PROPER_FACE ← prove
   r"!s t:real^N->bool.
        convex s /\ t SUBSET s /\
        ~(relative_interior t DIFF relative_interior s = {})
        ==> ?f. f face_of s /\ ~(f = s) /\ t SUBSET f"
   (REPEAT GEN_TAC THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"a:real^N") THEN REWRITE_TAC [IN_INTER, IN_DIFF] THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"a:real^N"]
          RELATIVE_BOUNDARY_POINT_IN_PROPER_FACE) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [SUBSET, RELATIVE_INTERIOR_SUBSET], ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC (← q r"s:real^N->bool") THEN
    ASM SET_TAC [])

  let CONVEX_RELATIVE_BOUNDARY_SUBSET_OF_PROPER_FACE ← prove
   r"!s t:real^N->bool.
        convex s /\ ~(s = {}) /\
        convex t /\ t SUBSET s DIFF relative_interior s
        ==> ?f. f face_of s /\ ~(f = s) /\ t SUBSET f"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"t:real^N->bool = {}") THENL
     [EXISTS_TAC (← q r"{}:real^N->bool") THEN
      ASM_REWRITE_TAC [EMPTY_FACE_OF, SUBSET_REFL],
      MATCH_MP_TAC RELATIVE_INTERIOR_SUBSET_OF_PROPER_FACE THEN
      MP_TAC (← ISPEC (← q r"t:real^N->bool") RELATIVE_INTERIOR_EQ_EMPTY) THEN
      MP_TAC (← ISPEC (← q r"t:real^N->bool") RELATIVE_INTERIOR_SUBSET) THEN
      ASM SET_TAC []])

  let RELATIVE_FRONTIER_FACIAL_PARTITION_ALT ← prove
   r"!s:real^N->bool.
        convex s /\ closed s
        ==> UNIONS { relative_interior f | f face_of s /\ ~(f = s)} =
            relative_frontier s"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [relative_frontier, CLOSURE_CLOSED] THEN
    FIRST_ASSUM (fun th => tactic_of do
     pure (GEN_REWRITE_TAC (RAND_CONV o LAND_CONV)
       [← GSYM (← MATCH_MP CONVEX_FACIAL_PARTITION th)])) THEN
    MATCH_MP_TAC (← SET_RULE
     (← q r"u UNION s = t /\ DISJOINT u s ==> s = t DIFF u")) THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC [FACE_OF_REFL, ← GSYM UNIONS_INSERT, ← SET_RULE
       (← q r"P a ==> f a INSERT {f x | P x /\ ~(x = a)} = {f x | P x}")],
      REWRITE_TAC [DISJOINT, INTER_UNIONS, EMPTY_UNIONS, FORALL_IN_GSPEC] THEN
      REWRITE_TAC [← GSYM DISJOINT] THEN ASM_MESON_TAC [FACE_OF_EQ, FACE_OF_REFL]])

  let RELATIVE_FRONTIER_FACIAL_PARTITION ← prove
   r"!s:real^N->bool.
        convex s /\ closed s
        ==> UNIONS { relative_interior f |
                     f face_of s /\ aff_dim f < aff_dim s} =
            relative_frontier s"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [← GSYM RELATIVE_FRONTIER_FACIAL_PARTITION_ALT] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC (← SET_RULE
     (← q r"(!x. P x ==> (Q x <=> R x))
      ==> {f x | P x /\ Q x} = {f x | P x /\ R x}")) THEN
    ASM_MESON_TAC [FACE_OF_AFF_DIM_LT, INT_LT_REFL, FACE_OF_REFL])

  let FRONTIER_OF_CONVEX_CLOSED ← prove
   r"!s:real^N->bool.
        convex s /\ closed s
        ==> frontier s =
            UNIONS {f | f face_of s /\ aff_dim f < &(dimindex(:N))}"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN
    REWRITE_TAC [UNIONS_SUBSET, FORALL_IN_GSPEC] THEN
    CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [FACE_OF_SUBSET_FRONTIER_AFF_DIM]] THEN
    ASM_SIMP_TAC [frontier, CLOSURE_CLOSED] THEN FIRST_ASSUM (fun th => tactic_of do
     pure (GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
          [← SYM (← MATCH_MP CONVEX_FACIAL_PARTITION th)])) THEN
    REWRITE_TAC [UNIONS_GSPEC, SUBSET, IN_DIFF, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"z:real^N") THEN DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_THEN (← q r"f:real^N->bool") STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    EXISTS_TAC (← q r"f:real^N->bool") THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [ALL_TAC, ASM_MESON_TAC [SUBSET, RELATIVE_INTERIOR_SUBSET]] THEN
    REWRITE_TAC [INT_LT_LE, AFF_DIM_LE_UNIV] THEN DISCH_TAC THEN
    MP_TAC (← ISPEC (← q r"f:real^N->bool") RELATIVE_INTERIOR_INTERIOR) THEN
    ASM_REWRITE_TAC [← GSYM AFF_DIM_EQ_FULL] THEN DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^N->bool", ← q r"s:real^N->bool"] SUBSET_INTERIOR) THEN
    ASM_SIMP_TAC [FACE_OF_IMP_SUBSET] THEN ASM SET_TAC [])

  let FACE_OF_INTER_AS_INTER_OF_FACE ← prove
   r"!s t f:real^N->bool.
        convex s /\ convex t /\ f face_of (s INTER t)
        ==> ?k l. k face_of s /\ l face_of t /\ k INTER l = f"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"relative_interior f:real^N->bool = {}") THENL
     [REPEAT (EXISTS_TAC (← q r"{}:real^N->bool")) THEN REWRITE_TAC [EMPTY_FACE_OF] THEN
      MP_TAC (← ISPEC (← q r"f:real^N->bool") RELATIVE_INTERIOR_EQ_EMPTY) THEN
      REWRITE_TAC [INTER_EMPTY] THEN ASM_MESON_TAC [face_of],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"x:real^N") STRIP_ASSUME_TAC) THEN
    MAP_EVERY (MP_TAC o C SPEC CONVEX_FACIAL_PARTITION)
     [← q r"t:real^N->bool", ← q r"s:real^N->bool"] THEN
    ASM_REWRITE_TAC [EXTENSION, IMP_IMP, AND_FORALL_THM] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"x:real^N")) THEN REWRITE_TAC [UNIONS_GSPEC] THEN
    SUBGOAL_THEN (← q r"(x:real^N) IN s /\ x IN t") STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM (MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
      MP_TAC (← ISPEC (← q r"f:real^N->bool") RELATIVE_INTERIOR_SUBSET) THEN
      ASM SET_TAC [],
      ASM_REWRITE_TAC [IN_ELIM_THM]] THEN
    REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"k:real^N->bool") THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"l:real^N->bool") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [← GSYM EXTENSION] THEN
    MATCH_MP_TAC FACE_OF_EQ THEN
    EXISTS_TAC (← q r"s INTER t:real^N->bool") THEN
    ASM_SIMP_TAC [FACE_OF_INTER_INTER] THEN
    MP_TAC (← ISPECL [← q r"k:real^N->bool", ← q r"l:real^N->bool"]
          INTER_RELATIVE_INTERIOR_SUBSET) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [FACE_OF_IMP_CONVEX], ASM SET_TAC []])

  pure { FACES_OF_TRANSLATION, FACES_OF_LINEAR_IMAGE, FACE_OF_CONIC, FACE_OF_PCROSS,
         FACE_OF_PCROSS_DECOMP, FACE_OF_PCROSS_EQ, HYPERPLANE_FACE_OF_HALFSPACE_LE,
         HYPERPLANE_FACE_OF_HALFSPACE_GE, FACE_OF_HALFSPACE_LE, FACE_OF_HALFSPACE_GE,
         RELATIVE_BOUNDARY_POINT_IN_PROPER_FACE, RELATIVE_FRONTIER_OF_CONVEX_CLOSED,
         IN_RELATIVE_INTERIOR_OF_FACE, CONVEX_FACIAL_PARTITION,
         IN_RELATIVE_INTERIOR_OF_UNIQUE_FACE, RELATIVE_INTERIOR_SUBSET_OF_PROPER_FACE,
         CONVEX_RELATIVE_BOUNDARY_SUBSET_OF_PROPER_FACE,
         RELATIVE_FRONTIER_FACIAL_PARTITION_ALT, RELATIVE_FRONTIER_FACIAL_PARTITION,
         FRONTIER_OF_CONVEX_CLOSED, FACE_OF_INTER_AS_INTER_OF_FACE }

/- ------------------------------------------------------------------------- -/
/- Exposed faces (faces that are intersection with supporting hyperplane).   -/
/- (polytope.ml 1183-1483)                                                   -/
/- ------------------------------------------------------------------------- -/

structure POD where
  exposed_face_of : thm
  EXPOSED_FACE_OF_IMP_FACE_OF : thm
  EMPTY_EXPOSED_FACE_OF : thm
  EXPOSED_FACE_OF_REFL_EQ : thm
  EXPOSED_FACE_OF_REFL : thm
  EXPOSED_FACE_OF : thm
  EXPOSED_FACE_OF_TRANSLATION_EQ : thm
  EXPOSED_FACE_OF_LINEAR_IMAGE : thm
  EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE : thm
  EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE : thm
  EXPOSED_FACE_OF_INTER : thm
  EXPOSED_FACE_OF_INTERS : thm
  EXPOSED_FACE_OF_SUMS : thm
  EXPOSED_FACE_OF_PARALLEL : thm
  RELATIVE_BOUNDARY_POINT_IN_EXPOSED_FACE : thm
  deriving Inhabited

set_option maxHeartbeats 4000000 in
@[nospecialize]
def setupPOD [HolBase] (D : PolytopeDeps) (BPOA : POA) (BPOB : POB) : ExceptT String IO POD := do
  -- @@SCOPE BEGIN
  let { add_translation_invariants, ASM_MESON_TAC, ASM_REAL_ARITH_TAC,
        invariant_under_linear, MESON_TAC, new_definition, parse_as_infix, REAL_ARITH,
        REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV, SET_RULE, SET_TAC, VECTOR_ARITH, .. } := D.cvx
  let { invariant_under_translation, .. } := D
  let { EMPTY_GSPEC, EXISTS_IN_GSPEC, EXTENSION, FINITE_INDUCT_STRONG, FORALL_IN_GSPEC, .. }
        := D.cvx.core1
  let { FORALL_IN_INSERT, FUN_EQ_THM, IMP_CONJ, IN_DIFF, INTER_EMPTY, INTER_UNIV, INTERS_0,
        INTERS_INSERT, .. } := D.cvx.core2
  let { I_THM, IN_ELIM_THM, IN_INTER, IN_UNION, IN_UNIV, LEFT_AND_EXISTS_THM,
        LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY, MONO_EXISTS, NOT_FORALL_THM, REAL_ADD_SYM, ..
        } := D.cvx.core3
  let { REAL_EQ_NEG2, REAL_EQ_SUB_LADD, REAL_LE_ADD2, REAL_LE_ANTISYM, REAL_LE_NEG2,
        REAL_LE_REFL, REAL_LE_SUB_LADD, REAL_LT_IMP_NE, .. } := D.cvx.core4
  let { REAL_POS, RIGHT_AND_EXISTS_THM, SUBSET, SUBSET_ANTISYM, SUBSET_TRANS, .. } :=
        D.cvx.core5
  let { o_THM, real_ge, SUBSET_UNIV, SWAP_EXISTS_THM, .. } := D.cvx.core6
  let { HULL_SUBSET, .. } := D.cvx.misc
  let { DOT_LADD, DOT_LNEG, DOT_LZERO, DOT_RADD, .. } := D.cvx.vec1
  let { DOT_SYM, .. } := D.cvx.vec2
  let { VECTOR_ADD_RID, VECTOR_NEG_EQ_0, .. } := D.cvx.vec4
  let { SUBSET_INTER_ABSORPTION, .. } := D.qses
  let { ADJOINT_LINEAR, ADJOINT_SURJECTIVE, ADJOINT_WORKS, LINEAR_SURJECTIVE_RIGHT_INVERSE,
        QUANTIFY_SURJECTION_THM, .. } := D.qvec
  let { AFFINE_AFFINE_HULL, AFFINE_PARALLEL_SLICE, .. } := D.qcvx1
  let { IN_AFFINE_ADD_MUL_DIFF, RELATIVE_INTERIOR_EQ_EMPTY, RELATIVE_INTERIOR_SUBSET,
        SUPPORTING_HYPERPLANE_RELATIVE_BOUNDARY, .. } := D.qcvx3
  let { EMPTY_FACE_OF, FACE_OF_INTER, FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE,
        FACE_OF_LINEAR_IMAGE, FACE_OF_REFL_EQ, FACE_OF_TRANSLATION_EQ, .. } := BPOA
  let { INTERS_FACES_FINITE_ALTBOUND, .. } := BPOB
  -- @@SCOPE END
  parse_as_infix ("exposed_face_of", (12, "right"))

  let exposed_face_of ← new_definition
   r"t exposed_face_of s <=>
    t face_of s /\
    ?a b. s SUBSET {x | a dot x <= b} /\ t = s INTER {x | a dot x = b}"

  let EXPOSED_FACE_OF_IMP_FACE_OF ← prove
   r"!s t:real^N->bool. t exposed_face_of s ==> t face_of s"
   (SIMP_TAC [exposed_face_of])

  let EMPTY_EXPOSED_FACE_OF ← prove
   r"!s:real^N->bool. {} exposed_face_of s"
   (GEN_TAC THEN REWRITE_TAC [exposed_face_of, EMPTY_FACE_OF] THEN
    MAP_EVERY EXISTS_TAC [← q r"vec 0:real^N", ← q r"&1:real"] THEN
    REWRITE_TAC [DOT_LZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SET_TAC [])

  let EXPOSED_FACE_OF_REFL_EQ ← prove
   r"!s:real^N->bool. s exposed_face_of s <=> convex s"
   (GEN_TAC THEN REWRITE_TAC [exposed_face_of, FACE_OF_REFL_EQ] THEN
    ASM_CASES_TAC (← q r"convex(s:real^N->bool)") THEN ASM_REWRITE_TAC [] THEN
    MAP_EVERY EXISTS_TAC [← q r"vec 0:real^N", ← q r"&0:real"] THEN
    REWRITE_TAC [DOT_LZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SET_TAC [])

  let EXPOSED_FACE_OF_REFL ← prove
   r"!s:real^N->bool. convex s ==> s exposed_face_of s"
   (REWRITE_TAC [EXPOSED_FACE_OF_REFL_EQ])

  let EXPOSED_FACE_OF ← prove
   r"!s t. t exposed_face_of s <=>
             t face_of s /\
             (t = {} \/ t = s \/
              ?a b. ~(a = vec 0) /\
                    s SUBSET {x:real^N | a dot x <= b} /\
                    t = s INTER {x | a dot x = b})"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"t:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [EMPTY_EXPOSED_FACE_OF, EMPTY_FACE_OF] THEN
    ASM_CASES_TAC (← q r"t:real^N->bool = s") THEN
    ASM_REWRITE_TAC [EXPOSED_FACE_OF_REFL_EQ, FACE_OF_REFL_EQ] THEN
    REWRITE_TAC [exposed_face_of] THEN AP_TERM_TAC THEN
    EQ_TAC THENL [REWRITE_TAC [LEFT_IMP_EXISTS_THM], MESON_TAC []] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"b:real"] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MAP_EVERY EXISTS_TAC [← q r"a:real^N", ← q r"b:real"] THEN
    ASM_CASES_TAC (← q r"a:real^N = vec 0") THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN
    REWRITE_TAC [DOT_LZERO] THEN SET_TAC [])

  let EXPOSED_FACE_OF_TRANSLATION_EQ ← prove
   r"!a f s:real^N->bool.
        (IMAGE (\x. a + x) f) exposed_face_of (IMAGE (\x. a + x) s) <=>
        f exposed_face_of s"
   (REPEAT GEN_TAC THEN REWRITE_TAC [exposed_face_of, FACE_OF_TRANSLATION_EQ] THEN
    MP_TAC (← ISPEC (← q r"\x:real^N. a + x") QUANTIFY_SURJECTION_THM) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [MESON_TAC [← VECTOR_ARITH (← q r"y + (x - y):real^N = x")], ALL_TAC] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
        [← liftExcept (last (CONJUNCTS th))])) THEN
    REWRITE_TAC [← HolLight.end_itlist CONJ (← invariant_under_translation.get)] THEN
    REWRITE_TAC [DOT_RADD] THEN ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
    REWRITE_TAC [← GSYM REAL_LE_SUB_LADD, ← GSYM REAL_EQ_SUB_LADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"c:real^N") THEN REWRITE_TAC [] THEN
    EQ_TAC THEN DISCH_THEN (X_CHOOSE_THEN (← q r"b:real") STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC (← q r"b - (c:real^N) dot a"),
      EXISTS_TAC (← q r"b + (c:real^N) dot a")] THEN
    ASM_REWRITE_TAC [← REAL_ARITH (← q r"(x + y) - y:real = x")])

  add_translation_invariants [EXPOSED_FACE_OF_TRANSLATION_EQ]

  let EXPOSED_FACE_OF_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N c s.
      linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
      ==> ((IMAGE f c) exposed_face_of (IMAGE f s) <=> c exposed_face_of s)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [exposed_face_of] THEN
    BINOP_TAC THENL [ASM_MESON_TAC [FACE_OF_LINEAR_IMAGE], ALL_TAC] THEN
    MP_TAC (← ISPEC (← q r"f:real^M->real^N") QUANTIFY_SURJECTION_THM) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
        [← liftExcept (last (CONJUNCTS th))])) THEN
    ONCE_REWRITE_TAC [DOT_SYM] THEN ASM_SIMP_TAC [ADJOINT_WORKS] THEN
    MP_TAC (← HolLight.end_itlist CONJ
     (← HolMath.IndTypes.mapfilterM (ISPEC (← q r"f:real^M->real^N"))
          (← invariant_under_linear.get))) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
    EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"a:real^N") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"adjoint(f:real^M->real^N) a") THEN ASM_REWRITE_TAC [],
      DISCH_THEN (X_CHOOSE_THEN (← q r"a:real^M") STRIP_ASSUME_TAC) THEN
      MP_TAC (← ISPEC (← q r"adjoint(f:real^M->real^N)")
        LINEAR_SURJECTIVE_RIGHT_INVERSE) THEN
      ASM_SIMP_TAC [ADJOINT_SURJECTIVE, ADJOINT_LINEAR] THEN
      REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"g:real^M->real^N") THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"(g:real^M->real^N) a") THEN ASM_REWRITE_TAC []])

  let EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE ← prove
   r"!s a:real^N b.
        convex s /\ (!x. x IN s ==> a dot x <= b)
        ==> (s INTER {x | a dot x = b}) exposed_face_of s"
   (SIMP_TAC [FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE, exposed_face_of] THEN
    SET_TAC [])

  let EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE ← prove
   r"!s a:real^N b.
        convex s /\ (!x. x IN s ==> a dot x >= b)
        ==> (s INTER {x | a dot x = b}) exposed_face_of s"
   (REWRITE_TAC [real_ge] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"--a:real^N", ← q r"--b:real"]
      EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE) THEN
    ASM_REWRITE_TAC [DOT_LNEG, REAL_EQ_NEG2, REAL_LE_NEG2])

  let EXPOSED_FACE_OF_INTER ← prove
   r"!s t u:real^N->bool.
        t exposed_face_of s /\ u exposed_face_of s
        ==> (t INTER u) exposed_face_of s"
   (REPEAT GEN_TAC THEN SIMP_TAC [exposed_face_of, FACE_OF_INTER] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN
    REWRITE_TAC [LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"a':real^N", ← q r"b':real", ← q r"a:real^N", ← q r"b:real"] THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    MAP_EVERY EXISTS_TAC [← q r"a + a':real^N", ← q r"b + b':real"] THEN
    REWRITE_TAC [← SET_RULE
     (← q r"(s INTER t1) INTER (s INTER t2) = s INTER u <=>
      !x. x IN s ==> (x IN t1 /\ x IN t2 <=> x IN u)")] THEN
    ASM_SIMP_TAC [DOT_LADD, REAL_LE_ADD2, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real^N"))) THEN
    ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC)

  let EXPOSED_FACE_OF_INTERS ← prove
   r"!P s:real^N->bool.
        ~(P = {}) /\ (!t. t IN P ==> t exposed_face_of s)
        ==> INTERS P exposed_face_of s"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"P:(real^N->bool)->bool"]
      INTERS_FACES_FINITE_ALTBOUND) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [exposed_face_of], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"Q:(real^N->bool)->bool") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o SYM) THEN
    ASM_CASES_TAC (← q r"Q:(real^N->bool)->bool = {}") THENL
     [ASM_SIMP_TAC [INTERS_0] THEN
      REWRITE_TAC [← SET_RULE (← q r"INTERS s = UNIV <=> !t. t IN s ==> t = UNIV")] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
      ASM_MESON_TAC [],
      DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM (MP_TAC o check (HolCore.Basics.is_neg o concl)) THEN
      SUBGOAL_THEN (← q r"!t:real^N->bool. t IN Q ==> t exposed_face_of s") MP_TAC THENL
       [ASM SET_TAC [], UNDISCH_TAC (← q r"FINITE(Q:(real^N->bool)->bool)")] THEN
      SPEC_TAC (← q r"Q:(real^N->bool)->bool", ← q r"Q:(real^N->bool)->bool") THEN
      POP_ASSUM_LIST (K ALL_TAC) THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC [FORALL_IN_INSERT] THEN
      MAP_EVERY X_GEN_TAC [← q r"t:real^N->bool", ← q r"P:(real^N->bool)->bool"] THEN
      DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [INTERS_INSERT] THEN
      ASM_CASES_TAC (← q r"P:(real^N->bool)->bool = {}") THEN
      ASM_SIMP_TAC [INTERS_0, INTER_UNIV, EXPOSED_FACE_OF_INTER]])

  let EXPOSED_FACE_OF_SUMS ← prove
   r"!s t f:real^N->bool.
        convex s /\ convex t /\
        f exposed_face_of {x + y | x IN s /\ y IN t}
        ==> ?k l. k exposed_face_of s /\ l exposed_face_of t /\
                  f = {x + y | x IN k /\ y IN l}"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [EXPOSED_FACE_OF]) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_CASES_TAC (← q r"f:real^N->bool = {}") THENL
     [DISCH_TAC THEN REPEAT (EXISTS_TAC (← q r"{}:real^N->bool")) THEN
      ASM_REWRITE_TAC [EMPTY_EXPOSED_FACE_OF] THEN SET_TAC [],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"f = {x + y :real^N | x IN s /\ y IN t}") THENL
     [DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [← q r"s:real^N->bool", ← q r"t:real^N->bool"] THEN
      ASM_SIMP_TAC [EXPOSED_FACE_OF_REFL],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"u:real^N", ← q r"z:real"] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, IN_ELIM_THM] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [← GSYM SUBSET_INTER_ABSORPTION]) THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC [EXISTS_IN_GSPEC, IN_INTER] THEN
    REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"a0:real^N", ← q r"b0:real^N"] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
    EXISTS_TAC (← q r"s INTER {x:real^N | u dot x = u dot a0}") THEN
    EXISTS_TAC (← q r"t INTER {y:real^N | u dot y = u dot b0}") THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
      ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"a:real^N") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"a:real^N", ← q r"b0:real^N"]) THEN
      ASM_REWRITE_TAC [DOT_RADD] THEN REAL_ARITH_TAC,
      MATCH_MP_TAC EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
      ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"b:real^N") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"a0:real^N", ← q r"b:real^N"]) THEN
      ASM_REWRITE_TAC [DOT_RADD] THEN REAL_ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
    REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, IN_INTER, IMP_CONJ] THENL
     [ALL_TAC, SIMP_TAC [IN_INTER, IN_ELIM_THM, DOT_RADD] THEN MESON_TAC []] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"b:real^N"] THEN
    DISCH_TAC THEN DISCH_TAC THEN REWRITE_TAC [IN_ELIM_THM, DOT_RADD] THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [← q r"a:real^N", ← q r"b:real^N"] THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (MP_TAC o SPECL [← q r"a:real^N", ← q r"b0:real^N"]) THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"a0:real^N", ← q r"b:real^N"]) THEN
    ASM_REWRITE_TAC [DOT_RADD] THEN ASM_REAL_ARITH_TAC)

  let EXPOSED_FACE_OF_PARALLEL ← prove
   r"!t s. t exposed_face_of s <=>
         t face_of s /\
          ?a b. s SUBSET {x:real^N | a dot x <= b} /\
                t = s INTER {x | a dot x = b} /\
                (~(t = {}) /\ ~(t = s) ==> ~(a = vec 0)) /\
                (!w. w IN affine hull s /\ ~(t = s)
                     ==> (w + a) IN affine hull s)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [exposed_face_of] THEN
    AP_TERM_TAC THEN EQ_TAC THENL
     [REWRITE_TAC [LEFT_IMP_EXISTS_THM],
      REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN SIMP_TAC []] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"b:real"] THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"affine hull s:real^N->bool", ← q r"--a:real^N", ← q r"--b:real"]
          AFFINE_PARALLEL_SLICE) THEN
    SIMP_TAC [AFFINE_AFFINE_HULL, DOT_LNEG, REAL_LE_NEG2, REAL_EQ_NEG2] THEN
    DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
     [MAP_EVERY EXISTS_TAC [← q r"vec 0:real^N", ← q r"&1"] THEN
      REWRITE_TAC [DOT_LZERO, REAL_POS, ← SET_RULE (← q r"{x | T} = UNIV")] THEN
      SIMP_TAC [SUBSET_UNIV, VECTOR_ADD_RID, ← REAL_ARITH (← q r"~(&0 = &1)")] THEN
      REWRITE_TAC [EMPTY_GSPEC] THEN ASM_REWRITE_TAC [INTER_EMPTY] THEN
      MATCH_MP_TAC (← TAUT (← q r"p ==> p /\ ~(~p /\ q)")) THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
       (← q r"s' INTER t' = {}
        ==> s SUBSET s' /\ t SUBSET t' ==> s INTER t = {}"))) THEN
      REWRITE_TAC [HULL_SUBSET] THEN SIMP_TAC [SUBSET, IN_ELIM_THM, REAL_LE_REFL],
      SUBGOAL_THEN (← q r"t:real^N->bool = s") SUBST1_TAC THENL
       [FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC [← GSYM REAL_LE_ANTISYM] THEN
        SUBGOAL_THEN (← q r"s SUBSET affine hull (s:real^N->bool)") MP_TAC THENL
         [REWRITE_TAC [HULL_SUBSET], ASM SET_TAC []],
        MAP_EVERY EXISTS_TAC [← q r"vec 0:real^N", ← q r"&0"] THEN
        REWRITE_TAC [DOT_LZERO, ← SET_RULE (← q r"{x | T} = UNIV"), REAL_LE_REFL] THEN
        SET_TAC []],
      FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"a':real^N") MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"b':real") STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [← q r"--a':real^N", ← q r"--b':real"] THEN
      ASM_REWRITE_TAC [DOT_LNEG, REAL_LE_NEG2, REAL_EQ_NEG2] THEN
      REPEAT CONJ_TAC THENL
       [ONCE_REWRITE_TAC [← REAL_ARITH (← q r"b <= a <=> ~(a <= b) \/ a = b")] THEN
        MATCH_MP_TAC (← SET_RULE
         (← q r"!s'. s SUBSET s' /\
              s SUBSET (UNIV DIFF (s' INTER {x | P x})) UNION
                       (s' INTER {x | Q x})
              ==> s SUBSET {x | ~P x \/ Q x}")) THEN
        EXISTS_TAC (← q r"affine hull s:real^N->bool") THEN
        ASM_REWRITE_TAC [HULL_SUBSET] THEN
        MATCH_MP_TAC (← SET_RULE
         (← q r"s SUBSET s' /\ s SUBSET (UNIV DIFF {x | P x}) UNION {x | Q x}
          ==> s SUBSET (UNIV DIFF (s' INTER {x | P x})) UNION
                       (s' INTER {x | Q x})")) THEN
        REWRITE_TAC [HULL_SUBSET] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC (← q r"{x:real^N | a dot x <= b}") THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [SUBSET, IN_DIFF, IN_UNIV, IN_UNION, IN_ELIM_THM] THEN
        REAL_ARITH_TAC,
        FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
         (← q r"s' INTER a = s' INTER b
          ==> s SUBSET s' ==> s INTER b = s INTER a"))) THEN
        REWRITE_TAC [HULL_SUBSET],
        ASM_REWRITE_TAC [VECTOR_NEG_EQ_0],
        ONCE_REWRITE_TAC [← VECTOR_ARITH
         (← q r"w + --a:real^N = w + &1 % (w - (w + a))")] THEN
        ASM_SIMP_TAC [IN_AFFINE_ADD_MUL_DIFF, AFFINE_AFFINE_HULL]]])

  let RELATIVE_BOUNDARY_POINT_IN_EXPOSED_FACE ← prove
   r"!s x:real^N.
           convex s /\ x IN s /\ ~(x IN relative_interior s)
           ==> ?f. f exposed_face_of s /\ ~(f = s) /\ x IN f"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"x:real^N"]
          SUPPORTING_HYPERPLANE_RELATIVE_BOUNDARY) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"a:real^N") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"s INTER {y:real^N | a dot y = a dot x}") THEN
    ASM_REWRITE_TAC [IN_ELIM_THM, IN_INTER] THEN CONJ_TAC THENL
     [MATCH_MP_TAC EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE THEN
      ASM_REWRITE_TAC [real_ge],
      SUBGOAL_THEN (← q r"~(relative_interior s:real^N->bool = {})") MP_TAC THENL
       [ASM_SIMP_TAC [RELATIVE_INTERIOR_EQ_EMPTY] THEN ASM SET_TAC [],
        REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, EXTENSION, NOT_FORALL_THM]] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"z:real^N") THEN
      SIMP_TAC [IN_INTER, ← REWRITE_RULE [SUBSET] RELATIVE_INTERIOR_SUBSET] THEN
      ASM_SIMP_TAC [IN_ELIM_THM, REAL_LT_IMP_NE]])

  pure { exposed_face_of, EXPOSED_FACE_OF_IMP_FACE_OF, EMPTY_EXPOSED_FACE_OF,
         EXPOSED_FACE_OF_REFL_EQ, EXPOSED_FACE_OF_REFL, EXPOSED_FACE_OF,
         EXPOSED_FACE_OF_TRANSLATION_EQ, EXPOSED_FACE_OF_LINEAR_IMAGE,
         EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE,
         EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE, EXPOSED_FACE_OF_INTER,
         EXPOSED_FACE_OF_INTERS, EXPOSED_FACE_OF_SUMS, EXPOSED_FACE_OF_PARALLEL,
         RELATIVE_BOUNDARY_POINT_IN_EXPOSED_FACE }

/- ------------------------------------------------------------------------- -/
/- Extreme points of a set, which are its singleton faces.                   -/
/- (polytope.ml 1483-1961)                                                   -/
/- ------------------------------------------------------------------------- -/

structure POE where
  extreme_point_of : thm
  EXTREME_POINT_RELATIVE_FRONTIER : thm
  EXTREME_POINT_OF_STILLCONVEX_IMP : thm
  EXTREME_POINTS_OF_STILLCONVEX : thm
  EXTREME_POINT_OF_STILLCONVEX : thm
  FACE_OF_SING : thm
  FACE_OF_AFF_DIM_0 : thm
  EXTREME_POINT_NOT_IN_RELATIVE_INTERIOR : thm
  EXTREME_POINT_NOT_IN_INTERIOR : thm
  EXTREME_POINT_IN_RELATIVE_FRONTIER : thm
  EXTREME_POINT_IN_FRONTIER : thm
  EXTREME_POINT_OF_FACE : thm
  EXTREME_POINT_OF_MIDPOINT : thm
  EXTREME_POINT_OF_CONVEX_HULL : thm
  EXTREME_POINTS_OF_CONVEX_HULL : thm
  EXTREME_POINT_OF_EMPTY : thm
  EXTREME_POINT_OF_SING : thm
  EXTREME_POINT_OF_TRANSLATION_EQ : thm
  EXTREME_POINT_OF_LINEAR_IMAGE : thm
  EXTREME_POINTS_OF_TRANSLATION : thm
  EXTREME_POINT_OF_INTER : thm
  EXTREME_POINT_OF_INTER_GEN : thm
  EXTREME_POINTS_OF_LINEAR_IMAGE : thm
  EXTREME_POINT_OF_INTER_SUPPORTING_HYPERPLANE_LE : thm
  EXTREME_POINT_OF_INTER_SUPPORTING_HYPERPLANE_GE : thm
  EXPOSED_POINT_OF_INTER_SUPPORTING_HYPERPLANE_LE : thm
  EXPOSED_POINT_OF_INTER_SUPPORTING_HYPERPLANE_GE : thm
  EXPOSED_POINT_OF_FURTHEST_POINT : thm
  COLLINEAR_EXTREME_POINTS : thm
  EXTREME_POINT_OF_CONIC : thm
  EXTREME_POINT_OF_CONVEX_HULL_INSERT : thm
  FACE_OF_CONIC_HULL : thm
  FACE_OF_CONIC_HULL_REV : thm
  EXTREME_POINT_OF_CONIC_HULL : thm
  FACE_OF_CONIC_HULL_EQ : thm
  EXTREME_POINT_OF_CBALL : thm
  deriving Inhabited

set_option maxHeartbeats 4000000 in
@[nospecialize]
def setupPOE [HolBase] (D : PolytopeDeps) (BPOA : POA) (BPOB : POB) (BPOC : POC) (BPOD : POD) : ExceptT String IO POE := do
  -- @@SCOPE BEGIN
  let { add_linear_invariants, add_translation_invariants, ARITH_RULE, ASM_MESON_TAC,
        ASM_REAL_ARITH_TAC, GEOM_ORIGIN_TAC, GEOM_TRANSFORM_TAC, GEOM_TRANSLATE_TAC,
        HAS_SIZE_CONV, MESON_TAC, new_definition, parse_as_infix, REAL_ARITH,
        REAL_ARITH_TAC, REAL_FIELD, SET_RULE, SET_TAC, VECTOR_ARITH, VECTOR_ARITH_TAC, .. }
        := D.cvx
  let { CHOOSE_SUBSET_STRONG, CONJ_ASSOC, CONTRAPOS_THM, DE_MORGAN_THM, EMPTY_SUBSET,
        EXISTS_REFL, FINITE_INSERT, FINITE_SING, FORALL_IN_GSPEC, .. } := D.cvx.core1
  let { FORALL_IN_IMAGE, FUN_IN_IMAGE, IMP_CONJ, IMP_CONJ_ALT, IMP_IMP, IN_DELETE, IN_DIFF,
        INSERT_SUBSET, INTER_SUBSET, .. } := D.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, IN_INTER, IN_SING, IN_UNION, NOT_EXISTS_THM, NOT_IMP,
        NOT_IN_EMPTY, NOT_INSERT_EMPTY, NOT_LT, .. } := D.cvx.core3
  let { REAL_ENTIRE, REAL_EQ_NEG2, REAL_LE_ANTISYM, REAL_LE_DIV, REAL_LE_INV_EQ,
        REAL_LE_MUL, REAL_LE_NEG2, REAL_LE_REFL, REAL_LT_ADD, REAL_LT_IMP_LE,
        REAL_LT_IMP_NZ, REAL_LT_LE, REAL_LT_MUL, REAL_LT_REFL, .. } := D.cvx.core4
  let { REAL_MUL_AC, REAL_MUL_LINV, REAL_SUB_0, REAL_SUB_LE, REAL_SUB_LT,
        RIGHT_AND_EXISTS_THM, RIGHT_FORALL_IMP_THM, SING_SUBSET, SUBSET, SUBSET_ANTISYM,
        SUBSET_DELETE, SUBSET_EMPTY, SUBSET_REFL, .. } := D.cvx.core5
  let { real_div, real_ge, SURJECTIVE_IMAGE_EQ, SWAP_EXISTS_THM, .. } := D.cvx.core6
  let { HULL_INC, HULL_MINIMAL, HULL_MONO, HULL_SUBSET, .. } := D.cvx.misc
  let { COLLINEAR_BETWEEN_CASES, COLLINEAR_SUBSET, DIST_0, DOT_LNEG, DOT_LSUB, DOT_POS_LE,
        DOT_RSUB, .. } := D.cvx.vec1
  let { DOT_SYM, NORM_EQ_0, NORM_LE, .. } := D.cvx.vec2
  let { midpoint, VECTOR_ADD_LID, VECTOR_ADD_RDISTRIB, VECTOR_ADD_RID, VECTOR_MUL_ASSOC,
        VECTOR_MUL_EQ_0, VECTOR_MUL_LID, VECTOR_MUL_LZERO, VECTOR_MUL_RZERO, VECTOR_SUB_EQ,
        .. } := D.cvx.vec4
  let { BETWEEN_IN_SEGMENT, CBALL_SING, .. } := D.cvx.top1
  let { CLOSURE_INC, CLOSURE_SUBSET, .. } := D.cvx.top2
  let { EMPTY_INTERIOR_FINITE, ENDS_NOT_IN_SEGMENT, FRONTIER_CBALL, .. } := D.cvx.top3
  let { IN_BALL_0, IN_CBALL_0, IN_SEGMENT, IN_SPHERE_0, MIDPOINT_IN_SEGMENT, .. } :=
        D.cvx.top4
  let { frontier, open_segment, SEGMENT_CLOSED_OPEN, SEGMENT_REFL, SEGMENT_SYM, .. } :=
        D.cvx.top5
  let { MIDPOINT_REFL, VECTOR_EQ, .. } := D.qvec
  let { OPEN_SEGMENT_LINEAR_IMAGE, .. } := D.qtop
  let { AFF_DIM_EQ_0, AFFINE_AFFINE_HULL, AFFINE_HULL_0_2_EXPLICIT, AFFINE_HULL_SING,
        AFFINE_IMP_CONVEX, .. } := D.qcvx1
  let { CONIC_CONIC_HULL, CONIC_CONTAINS_0, CONIC_HULL_CONTAINS_0, CONIC_HULL_EMPTY,
        CONIC_HULL_EQ_EMPTY, CONIC_HULL_EQ_SING, CONIC_HULL_EXPLICIT,
        CONIC_HULL_INTER_AFFINE_HULL, CONVEX_ALT, CONVEX_CBALL, CONVEX_CONIC_HULL,
        CONVEX_CONTAINS_SEGMENT, CONVEX_CONVEX_HULL, CONVEX_HULL_SING, .. } := D.qcvx2
  let { conic, CONVEX_SING, DIFFERENT_NORM_3_COLLINEAR_POINTS,
        IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT, INTERIOR_SUBSET_RELATIVE_INTERIOR,
        OPEN_SEGMENT_DESCALE, relative_frontier, RELATIVE_INTERIOR_CBALL, .. } := D.qcvx3
  let { EMPTY_FACE_OF, face_of, FACE_OF_DISJOINT_RELATIVE_INTERIOR, FACE_OF_EMPTY,
        FACE_OF_FACE, FACE_OF_IMP_SUBSET, FACE_OF_INTER_INTER,
        FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE_STRONG,
        FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE_STRONG, FACE_OF_REFL, .. } := BPOA
  let { FACE_OF_CONVEX_HULLS, .. } := BPOB
  let { FACE_OF_CONIC, .. } := BPOC
  let { exposed_face_of, .. } := BPOD
  -- @@SCOPE END
  parse_as_infix ("extreme_point_of", (12, "right"))

  let extreme_point_of ← new_definition
   r"x extreme_point_of s <=>
    x IN s /\ !a b. a IN s /\ b IN s ==> ~(x IN segment(a,b))"

  let EXTREME_POINT_RELATIVE_FRONTIER ← prove
   r"!s x:real^N.
       convex s /\ x IN s DIFF relative_interior s /\
       (!a b. {a,b} SUBSET s DIFF relative_interior s ==> ~(x IN segment(a,b)))
       ==> x extreme_point_of s"
   (REWRITE_TAC [IN_DIFF] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [extreme_point_of] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"b:real^N"] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"a:real^N", ← q r"b:real^N"]) THEN
    ASM_REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET, IN_DIFF] THEN
    ASM_MESON_TAC [IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT, SUBSET,
                   CLOSURE_INC, SEGMENT_SYM])

  let EXTREME_POINT_OF_STILLCONVEX_IMP ← prove
   r"!s x:real^N. x IN s /\ convex(s DELETE x) ==> x extreme_point_of s"
   (REWRITE_TAC [CONVEX_CONTAINS_SEGMENT, extreme_point_of, open_segment] THEN
    REWRITE_TAC [IN_DIFF, IN_DELETE, IN_INSERT, NOT_IN_EMPTY, SUBSET_DELETE] THEN
    SET_TAC [])

  let EXTREME_POINTS_OF_STILLCONVEX ← prove
   r"!s t:real^N->bool.
        convex s /\ t SUBSET {x | x extreme_point_of s} ==> convex(s DIFF t)"
   (REWRITE_TAC [extreme_point_of, open_segment, CONVEX_CONTAINS_SEGMENT] THEN
    SET_TAC [])

  let EXTREME_POINT_OF_STILLCONVEX ← prove
   r"!s x:real^N.
        convex s ==> (x extreme_point_of s <=> x IN s /\ convex(s DELETE x))"
   (REWRITE_TAC [CONVEX_CONTAINS_SEGMENT, extreme_point_of, open_segment] THEN
    REWRITE_TAC [IN_DIFF, IN_DELETE, IN_INSERT, NOT_IN_EMPTY, SUBSET_DELETE] THEN
    SET_TAC [])

  let FACE_OF_SING ← prove
   r"!x s. {x} face_of s <=> x extreme_point_of s"
   (SIMP_TAC [face_of, extreme_point_of, SING_SUBSET, CONVEX_SING, IN_SING] THEN
    MESON_TAC [SEGMENT_REFL, NOT_IN_EMPTY])

  let FACE_OF_AFF_DIM_0 ← prove
   r"!s f:real^N->bool.
        f face_of s /\ aff_dim f = &0 <=> ?a. a extreme_point_of s /\ f = {a}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [AFF_DIM_EQ_0] THEN MESON_TAC [FACE_OF_SING])

  let EXTREME_POINT_NOT_IN_RELATIVE_INTERIOR ← prove
   r"!s x:real^N.
        x extreme_point_of s /\ ~(s = {x})
        ==> ~(x IN relative_interior s)"
   (REPEAT GEN_TAC THEN CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
    REWRITE_TAC [← GSYM FACE_OF_SING] THEN
    DISCH_THEN (MP_TAC o MATCH_MP FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    SET_TAC [])

  let EXTREME_POINT_NOT_IN_INTERIOR ← prove
   r"!s x:real^N. x extreme_point_of s ==> ~(x IN interior s)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"s = {x:real^N}") THEN
    ASM_SIMP_TAC [EMPTY_INTERIOR_FINITE, FINITE_SING, NOT_IN_EMPTY] THEN
    DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE [SUBSET]
      INTERIOR_SUBSET_RELATIVE_INTERIOR)) THEN
    ASM_SIMP_TAC [EXTREME_POINT_NOT_IN_RELATIVE_INTERIOR])

  let EXTREME_POINT_IN_RELATIVE_FRONTIER ← prove
   r"!s x:real^N.
        x extreme_point_of s /\ ~(s = {x}) ==> x IN relative_frontier s"
   (SIMP_TAC [EXTREME_POINT_NOT_IN_RELATIVE_INTERIOR,
              relative_frontier, IN_DIFF] THEN
    SIMP_TAC [extreme_point_of, ← REWRITE_RULE [SUBSET] CLOSURE_SUBSET])

  let EXTREME_POINT_IN_FRONTIER ← prove
   r"!s x:real^N. x extreme_point_of s ==> x IN frontier s"
   (SIMP_TAC [frontier, IN_DIFF, EXTREME_POINT_NOT_IN_INTERIOR] THEN
    SIMP_TAC [extreme_point_of, CLOSURE_INC])

  let EXTREME_POINT_OF_FACE ← prove
   r"!f s v. f face_of s
           ==> (v extreme_point_of f <=> v extreme_point_of s /\ v IN f)"
   (REWRITE_TAC [← GSYM FACE_OF_SING, ← GSYM SING_SUBSET, FACE_OF_FACE])

  let EXTREME_POINT_OF_MIDPOINT ← prove
   r"!s x:real^N.
        convex s
        ==> (x extreme_point_of s <=>
             x IN s /\
             !a b. a IN s /\ b IN s /\ x = midpoint(a,b) ==> x = a /\ x = b)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [extreme_point_of] THEN
    AP_TERM_TAC THEN EQ_TAC THEN
    DISCH_TAC THEN MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"b:real^N"] THEN
    DISCH_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o SPECL [← q r"a:real^N", ← q r"b:real^N"]) THEN
      ASM_SIMP_TAC [MIDPOINT_IN_SEGMENT, MIDPOINT_REFL],
      ALL_TAC] THEN
    REWRITE_TAC [IN_SEGMENT] THEN DISCH_THEN (CONJUNCTS_THEN2
      ASSUME_TAC (X_CHOOSE_THEN (← q r"u:real") STRIP_ASSUME_TAC)) THEN
    ABBREV_TAC (← q r"d = min (&1 - u) u") THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
     [← q r"x - d / &2 % (b - a):real^N", ← q r"x + d / &2 % (b - a):real^N"]) THEN
    REWRITE_TAC [NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [CONVEX_ALT]) THEN
      ASM_REWRITE_TAC [← VECTOR_ARITH
       (← q r"((&1 - u) % a + u % b) - d / &2 % (b - a):real^N =
        (&1 - (u - d / &2)) % a + (u - d / &2) % b")] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC,
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [CONVEX_ALT]) THEN
      ASM_REWRITE_TAC [← VECTOR_ARITH
       (← q r"((&1 - u) % a + u % b) + d / &2 % (b - a):real^N =
        (&1 - (u + d / &2)) % a + (u + d / &2) % b")] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC,
      REWRITE_TAC [midpoint] THEN VECTOR_ARITH_TAC,
      REWRITE_TAC [← VECTOR_ARITH (← q r"x:real^N = x - d <=> d = vec 0"),
                   ← VECTOR_ARITH (← q r"x:real^N = x + d <=> d = vec 0")] THEN
      ASM_REWRITE_TAC [VECTOR_MUL_EQ_0, VECTOR_SUB_EQ] THEN ASM_REAL_ARITH_TAC])

  let EXTREME_POINT_OF_CONVEX_HULL ← prove
   r"!x:real^N s. x extreme_point_of (convex hull s) ==> x IN s"
   (REPEAT GEN_TAC THEN
    SIMP_TAC [EXTREME_POINT_OF_STILLCONVEX, CONVEX_CONVEX_HULL] THEN
    MP_TAC (← ISPECL [← q r"convex:(real^N->bool)->bool", ← q r"s:real^N->bool",
                      ← q r"(convex hull s) DELETE (x:real^N)"] HULL_MINIMAL) THEN
    MP_TAC (← ISPECL [← q r"convex:(real^N->bool)->bool", ← q r"s:real^N->bool"]
          HULL_SUBSET) THEN
    ASM SET_TAC [])

  let EXTREME_POINTS_OF_CONVEX_HULL ← prove
   r"!s. {x | x extreme_point_of (convex hull s)} SUBSET s"
   (REWRITE_TAC [SUBSET, IN_ELIM_THM, EXTREME_POINT_OF_CONVEX_HULL])

  let EXTREME_POINT_OF_EMPTY ← prove
   r"!x. ~(x extreme_point_of {})"
   (REWRITE_TAC [extreme_point_of, NOT_IN_EMPTY])

  let EXTREME_POINT_OF_SING ← prove
   r"!a x. x extreme_point_of {a} <=> x = a"
   (REWRITE_TAC [extreme_point_of, IN_SING] THEN
    MESON_TAC [SEGMENT_REFL, NOT_IN_EMPTY])

  let EXTREME_POINT_OF_TRANSLATION_EQ ← prove
   r"!a:real^N x s.
           (a + x) extreme_point_of (IMAGE (\x. a + x) s) <=>
           x extreme_point_of s"
   (REWRITE_TAC [extreme_point_of] THEN GEOM_TRANSLATE_TAC [])

  add_translation_invariants [EXTREME_POINT_OF_TRANSLATION_EQ]

  let EXTREME_POINT_OF_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N.
      linear f /\ (!x y. f x = f y ==> x = y)
      ==> ((f x) extreme_point_of (IMAGE f s) <=> x extreme_point_of s)"
   (REWRITE_TAC [← GSYM FACE_OF_SING] THEN GEOM_TRANSFORM_TAC [])

  add_linear_invariants [EXTREME_POINT_OF_LINEAR_IMAGE]

  let EXTREME_POINTS_OF_TRANSLATION ← prove
   r"!a s. {x:real^N | x extreme_point_of (IMAGE (\x. a + x) s)} =
         IMAGE (\x. a + x) {x | x extreme_point_of s}"
   (REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"a + x:real^N = y <=> x = y - a"), EXISTS_REFL] THEN
    REWRITE_TAC [IN_ELIM_THM, EXTREME_POINT_OF_TRANSLATION_EQ])

  let EXTREME_POINT_OF_INTER ← prove
   r"!x s t. x extreme_point_of s /\ x extreme_point_of t
           ==> x extreme_point_of (s INTER t)"
   (REWRITE_TAC [extreme_point_of, IN_INTER] THEN MESON_TAC [])

  let EXTREME_POINT_OF_INTER_GEN ← prove
   r"!x s t. (x extreme_point_of s \/ x extreme_point_of t) /\ x IN s INTER t
           ==> x extreme_point_of (s INTER t)"
   (REWRITE_TAC [extreme_point_of, IN_INTER] THEN MESON_TAC [])

  let EXTREME_POINTS_OF_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> {y | y extreme_point_of (IMAGE f s)} =
            IMAGE f {x | x extreme_point_of s}"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP OPEN_SEGMENT_LINEAR_IMAGE) THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC [FORALL_IN_IMAGE, FORALL_IN_GSPEC, SUBSET,
                 extreme_point_of, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    ASM_SIMP_TAC [FUN_IN_IMAGE, IN_ELIM_THM, IMP_IMP, ← GSYM CONJ_ASSOC] THEN
    ASM SET_TAC [])

  let EXTREME_POINT_OF_INTER_SUPPORTING_HYPERPLANE_LE ← prove
   r"!s a b c. (!x. x IN s ==> a dot x <= b) /\
             s INTER {x | a dot x = b} = {c}
             ==> c extreme_point_of s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM FACE_OF_SING] THEN
    FIRST_ASSUM (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE_STRONG THEN
    ASM_REWRITE_TAC [CONVEX_SING])

  let EXTREME_POINT_OF_INTER_SUPPORTING_HYPERPLANE_GE ← prove
   r"!s a b c. (!x. x IN s ==> a dot x >= b) /\
             s INTER {x | a dot x = b} = {c}
             ==> c extreme_point_of s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM FACE_OF_SING] THEN
    FIRST_ASSUM (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE_STRONG THEN
    ASM_REWRITE_TAC [CONVEX_SING])

  let EXPOSED_POINT_OF_INTER_SUPPORTING_HYPERPLANE_LE ← prove
   r"!s a b c:real^N.
        (!x. x IN s ==> a dot x <= b) /\
        s INTER {x | a dot x = b} = {c}
        ==> {c} exposed_face_of s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [exposed_face_of] THEN CONJ_TAC THENL
     [REWRITE_TAC [FACE_OF_SING] THEN
      MATCH_MP_TAC EXTREME_POINT_OF_INTER_SUPPORTING_HYPERPLANE_LE,
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [← q r"a:real^N", ← q r"b:real"] THEN ASM SET_TAC [])

  let EXPOSED_POINT_OF_INTER_SUPPORTING_HYPERPLANE_GE ← prove
   r"!s a b c:real^N.
        (!x. x IN s ==> a dot x >= b) /\
        s INTER {x | a dot x = b} = {c}
        ==> {c} exposed_face_of s"
   (REWRITE_TAC [real_ge] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"--a:real^N", ← q r"--b:real",
                      ← q r"c:real^N"]
      EXPOSED_POINT_OF_INTER_SUPPORTING_HYPERPLANE_LE) THEN
    ASM_REWRITE_TAC [DOT_LNEG, REAL_EQ_NEG2, REAL_LE_NEG2])

  let EXPOSED_POINT_OF_FURTHEST_POINT ← prove
   r"!s a b:real^N.
        b IN s /\ (!x. x IN s ==> dist(a,x) <= dist(a,b))
        ==> {b} exposed_face_of s"
   (REPEAT GEN_TAC THEN GEOM_ORIGIN_TAC (← q r"a:real^N") THEN
    REWRITE_TAC [DIST_0, NORM_LE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC EXPOSED_POINT_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
    MAP_EVERY EXISTS_TAC [← q r"b:real^N", ← q r"(b:real^N) dot b"] THEN CONJ_TAC THENL
     [X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real^N")) THEN
      ASM_REWRITE_TAC [],
      MATCH_MP_TAC SUBSET_ANTISYM THEN
      ASM_REWRITE_TAC [IN_INTER, SING_SUBSET, IN_ELIM_THM] THEN
      REWRITE_TAC [SUBSET, IN_SING, IN_INTER, IN_ELIM_THM] THEN
      X_GEN_TAC (← q r"x:real^N") THEN STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC [VECTOR_EQ] THEN
      ASM_SIMP_TAC [← GSYM REAL_LE_ANTISYM] THEN
      UNDISCH_TAC (← q r"(b:real^N) dot x = b dot b")] THEN
    MP_TAC (← ISPEC (← q r"b - x:real^N") DOT_POS_LE) THEN
    REWRITE_TAC [DOT_LSUB, DOT_RSUB, DOT_SYM] THEN REAL_ARITH_TAC)

  let COLLINEAR_EXTREME_POINTS ← prove
   r"!s. collinear s
       ==> FINITE {x:real^N | x extreme_point_of s} /\
           CARD {x | x extreme_point_of s} <= 2"
   (REWRITE_TAC [← GSYM NOT_LT, ← TAUT (← q r"a /\ ~b <=> ~(a ==> b)")] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"2 < n <=> 3 <= n")] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP CHOOSE_SUBSET_STRONG) THEN
    CONV_TAC (ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN REWRITE_TAC [NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"t:real^N->bool", ← q r"a:real^N", ← q r"b:real^N", ← q r"c:real^N"] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN
     (← q r"(a:real^N) extreme_point_of s /\
      b extreme_point_of s /\ c extreme_point_of s")
    STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(a:real^N) IN s /\ b IN s /\ c IN s") STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [extreme_point_of], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"collinear {a:real^N,b,c}") MP_TAC THENL
     [MATCH_MP_TAC COLLINEAR_SUBSET THEN EXISTS_TAC (← q r"s:real^N->bool") THEN
      ASM SET_TAC [],
      REWRITE_TAC [COLLINEAR_BETWEEN_CASES, BETWEEN_IN_SEGMENT] THEN
      ASM_SIMP_TAC [SEGMENT_CLOSED_OPEN, IN_INSERT, NOT_IN_EMPTY, IN_UNION] THEN
      ASM_MESON_TAC [extreme_point_of]])

  let EXTREME_POINT_OF_CONIC ← prove
   r"!s x:real^N.
        conic s /\ x extreme_point_of s ==> x = vec 0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM FACE_OF_SING] THEN
    DISCH_THEN (MP_TAC o MATCH_MP FACE_OF_CONIC) THEN
    SIMP_TAC [conic, IN_SING, VECTOR_MUL_EQ_0, REAL_SUB_0, ← VECTOR_ARITH
      (← q r"c % x:real^N = x <=> (c - &1) % x = vec 0")] THEN
    MESON_TAC [← REAL_ARITH (← q r"&0 <= &0 /\ ~(&1 = &0)")])

  let EXTREME_POINT_OF_CONVEX_HULL_INSERT ← prove
   r"!s a:real^N.
        FINITE s /\ ~(a IN convex hull s)
        ==> a extreme_point_of (convex hull (a INSERT s))"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"(a:real^N) IN s") THEN ASM_SIMP_TAC [HULL_INC] THEN
    STRIP_TAC THEN MP_TAC (← ISPECL [← q r"{a:real^N}", ← q r"(a:real^N) INSERT s"]
      FACE_OF_CONVEX_HULLS) THEN
    ASM_REWRITE_TAC [FINITE_INSERT, AFFINE_HULL_SING, CONVEX_HULL_SING] THEN
    REWRITE_TAC [FACE_OF_SING] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC [← SET_RULE (← q r"~(a IN s) ==> a INSERT s DIFF {a} = s")] THEN
    ASM SET_TAC [])

  let FACE_OF_CONIC_HULL ← prove
   r"!f s:real^N->bool.
      f face_of s /\ ~(vec 0 IN affine hull s)
      ==> (conic hull f) face_of (conic hull s)"
   (REPEAT GEN_TAC THEN SIMP_TAC [face_of, HULL_MONO, CONVEX_CONIC_HULL] THEN
    STRIP_TAC THEN REWRITE_TAC [IMP_CONJ, CONIC_HULL_EXPLICIT] THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real", ← q r"x:real^N"] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"c:real", ← q r"z:real^N"] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"b:real", ← q r"y:real^N"] THEN STRIP_TAC THEN
    ASM_CASES_TAC (← q r"z:real^N = x") THENL
     [ASM_REWRITE_TAC [IN_SEGMENT] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"u:real") MP_TAC) THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC [← GSYM VECTOR_ADD_RDISTRIB, VECTOR_MUL_ASSOC] THEN
      DISCH_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN
      SUBGOAL_THEN (← q r"?c. &0 <= c /\ x:real^N = c % y")
       (fun th => ASM_MESON_TAC [VECTOR_MUL_ASSOC, REAL_LE_MUL, th]) THEN
      EXISTS_TAC (← q r"b / ((&1 - u) * a + u * c)") THEN
      FIRST_X_ASSUM ((K ALL_TAC : thm → tactic) o SPEC (← q r"z:real^N")) THEN
      FIRST_X_ASSUM (MP_TAC o
       AP_TERM (← q r"(%) (inv((&1 - u) * a + u * c)):real^N->real^N")) THEN
      SUBGOAL_THEN (← q r"&0 < (&1 - u) * a + u * c") ASSUME_TAC THENL
       [MATCH_MP_TAC (← REAL_ARITH
         (← q r"&0 <= x /\ &0 <= y /\ ~(x = &0 /\ y = &0) ==> &0 < x + y")) THEN
        ASM_SIMP_TAC [REAL_LE_MUL, REAL_SUB_LE, REAL_LT_IMP_LE, REAL_ENTIRE,
                      REAL_SUB_LT, REAL_LT_IMP_NZ] THEN
        ASM_MESON_TAC [VECTOR_MUL_LZERO],
        REWRITE_TAC [VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC [REAL_MUL_LINV, REAL_LT_IMP_NZ, REAL_LE_DIV,
                      REAL_LT_IMP_LE, VECTOR_MUL_LID] THEN
        DISCH_THEN (SUBST1_TAC o SYM) THEN
        REWRITE_TAC [real_div, REAL_MUL_AC]],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"a = &0") THENL
     [ASM_REWRITE_TAC [IN_ELIM_THM, VECTOR_MUL_LZERO] THEN
      ASM_CASES_TAC (← q r"c = &0") THEN
      ASM_REWRITE_TAC [VECTOR_MUL_LZERO, SEGMENT_REFL, NOT_IN_EMPTY] THEN
      REWRITE_TAC [IN_SEGMENT, VECTOR_MUL_RZERO, VECTOR_ADD_LID] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o AP_TERM (← q r"(%) (inv(u * c)):real^N->real^N")) THEN
      FIRST_X_ASSUM ((K ALL_TAC : thm → tactic) o SPEC (← q r"z:real^N")) THEN
      ASM_SIMP_TAC [VECTOR_MUL_ASSOC, VECTOR_MUL_LID, ← REAL_FIELD
       (← q r"&0 < u /\ ~(c = &0) ==> (inv(u * c) * u) * c = &1")] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN CONJ_TAC THEN
      ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN EXISTS_TAC (← q r"y:real^N") THEN
      REWRITE_TAC [VECTOR_MUL_ASSOC] THEN
      ASM_MESON_TAC [REAL_LE_MUL, REAL_LE_INV_EQ, VECTOR_MUL_LZERO, REAL_LE_REFL,
                     REAL_LT_IMP_LE],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"c = &0") THENL
     [ASM_REWRITE_TAC [IN_ELIM_THM, VECTOR_MUL_LZERO] THEN
      REWRITE_TAC [IN_SEGMENT, VECTOR_MUL_RZERO, VECTOR_ADD_RID] THEN
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o AP_TERM
       (← q r"(%) (inv((&1 - u) * a)):real^N->real^N")) THEN
      FIRST_X_ASSUM ((K ALL_TAC : thm → tactic) o SPEC (← q r"z:real^N")) THEN
      ASM_SIMP_TAC [VECTOR_MUL_ASSOC, VECTOR_MUL_LID, ← REAL_FIELD
       (← q r"u < &1 /\ ~(a = &0) ==> (inv((&1 - u) * a) * (&1 - u)) * a = &1")] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN CONJ_TAC THEN
      ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN EXISTS_TAC (← q r"y:real^N") THEN
      REWRITE_TAC [VECTOR_MUL_ASSOC] THEN
      ASM_MESON_TAC [REAL_LE_MUL, REAL_LE_INV_EQ, VECTOR_MUL_LZERO, REAL_LE_REFL,
                     REAL_LT_IMP_LE, REAL_SUB_LE],
      ALL_TAC] THEN
    DISCH_TAC THEN MP_TAC (← ISPECL
     [← q r"a:real", ← q r"b:real", ← q r"c:real", ← q r"x:real^N", ← q r"y:real^N",
      ← q r"z:real^N"]
          OPEN_SEGMENT_DESCALE) THEN
    ASM_REWRITE_TAC [REAL_LT_LE] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
       (← q r"~(z IN s) ==> t SUBSET s ==> ~(z IN t)"))) THEN
      MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC [],
      DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"x:real^N", ← q r"z:real^N", ← q r"y:real^N"]) THEN
      ASM_REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC []])

  let FACE_OF_CONIC_HULL_REV ← prove
   r"!s f:real^N->bool.
        f face_of (conic hull s) /\ ~(vec 0 IN affine hull s)
        ==> f = {vec 0} \/ ?f'. f' face_of s /\ conic hull f' = f"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"f = {vec 0:real^N}") THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC (← q r"f INTER affine hull s:real^N->bool") THEN CONJ_TAC THENL
     [MP_TAC (← SPECL [← q r"s:real^N->bool", ← q r"s:real^N->bool"]
       CONIC_HULL_INTER_AFFINE_HULL) THEN ASM_REWRITE_TAC [SUBSET_REFL] THEN
      DISCH_THEN (fun th => tactic_of do
        pure (GEN_REWRITE_TAC RAND_CONV [← GSYM th])) THEN
      MATCH_MP_TAC FACE_OF_INTER_INTER THEN
      ASM_SIMP_TAC [FACE_OF_REFL, AFFINE_AFFINE_HULL, AFFINE_IMP_CONVEX],
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [INTER_SUBSET] THEN
        ASM_MESON_TAC [FACE_OF_CONIC, CONIC_CONIC_HULL],
        SUBGOAL_THEN
         (← q r"!x:real^N. x IN conic hull s /\ x IN f /\ ~(x = vec 0)
                     ==> x IN conic hull (f INTER affine hull s)")
        ASSUME_TAC THENL
         [REWRITE_TAC [CONIC_HULL_EXPLICIT, IMP_CONJ, FORALL_IN_GSPEC] THEN
          MAP_EVERY X_GEN_TAC [← q r"c:real", ← q r"x:real^N"] THEN
          REWRITE_TAC [VECTOR_MUL_EQ_0, DE_MORGAN_THM] THEN
          REPEAT STRIP_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN
          MAP_EVERY EXISTS_TAC [← q r"c:real", ← q r"x:real^N"] THEN
          ASM_SIMP_TAC [IN_INTER, HULL_INC] THEN
          FIRST_X_ASSUM (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT]
            FACE_OF_CONIC)) THEN
          REWRITE_TAC [CONIC_CONIC_HULL] THEN REWRITE_TAC [conic] THEN
          DISCH_THEN (MP_TAC o SPECL [← q r"c % x:real^N", ← q r"inv c:real"]) THEN
          ASM_SIMP_TAC [REAL_LE_INV_EQ, VECTOR_MUL_ASSOC, REAL_MUL_LINV] THEN
          REWRITE_TAC [VECTOR_MUL_LID],
          REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:real^N") THEN
          ASM_CASES_TAC (← q r"x:real^N = vec 0") THENL
           [ASM_SIMP_TAC [CONIC_CONIC_HULL, CONIC_CONTAINS_0], ALL_TAC] THEN
          FIRST_ASSUM (MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
          ASM SET_TAC []]]])

  let EXTREME_POINT_OF_CONIC_HULL ← prove
   r"!s x:real^N.
        ~(vec 0 IN affine hull s)
        ==> (x extreme_point_of conic hull s <=> x = vec 0 /\ ~(s = {}))"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN
      FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM FACE_OF_SING]) THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
        FACE_OF_CONIC_HULL_REV)) THEN
      FIRST_ASSUM (MP_TAC o
        CONJUNCT1 o GEN_REWRITE_RULE I [extreme_point_of]) THEN
      ASM_REWRITE_TAC [← SET_RULE (← q r"{a} = {b} <=> a = b")] THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← SET_RULE (← q r"x IN s ==> ~(s = {})"))) THEN
      REWRITE_TAC [CONIC_HULL_EQ_EMPTY] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [CONIC_HULL_EQ_SING]) THEN
      ASM_MESON_TAC [FACE_OF_EMPTY, NOT_INSERT_EMPTY],
      STRIP_TAC THEN
      ASM_REWRITE_TAC [extreme_point_of, CONIC_HULL_CONTAINS_0] THEN
      REWRITE_TAC [CONIC_HULL_EXPLICIT, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC [FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [← q r"a:real", ← q r"u:real^N"] THEN STRIP_TAC THEN
      MAP_EVERY X_GEN_TAC [← q r"b:real", ← q r"v:real^N"] THEN STRIP_TAC THEN
      ASM_CASES_TAC (← q r"a = &0") THEN
      ASM_REWRITE_TAC [VECTOR_MUL_LZERO, ENDS_NOT_IN_SEGMENT] THEN
      ASM_CASES_TAC (← q r"b = &0") THEN
      ASM_REWRITE_TAC [VECTOR_MUL_LZERO, ENDS_NOT_IN_SEGMENT] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"affine hull {u:real^N,v}") o MATCH_MP (← SET_RULE
       (← q r"~(z IN s) ==> !t. t SUBSET s ==> ~(z IN t)"))) THEN
      ASM_SIMP_TAC [HULL_MONO, INSERT_SUBSET, EMPTY_SUBSET] THEN
      REWRITE_TAC [AFFINE_HULL_0_2_EXPLICIT, IN_SEGMENT, VECTOR_MUL_ASSOC] THEN
      REWRITE_TAC [CONTRAPOS_THM] THEN DISCH_THEN (CONJUNCTS_THEN2
       ASSUME_TAC (X_CHOOSE_THEN (← q r"u:real") STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [← q r"(&1 - u) * a", ← q r"u * b:real"] THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
      MATCH_MP_TAC REAL_LT_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REAL_ARITH_TAC])

  let FACE_OF_CONIC_HULL_EQ ← prove
   r"!s f:real^N->bool.
     ~(vec 0 IN affine hull s)
     ==> (f face_of (conic hull s) <=>
          f = {vec 0} /\ ~(s = {}) \/ ?f'. f' face_of s /\ conic hull f' = f)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [ASM_CASES_TAC (← q r"s:real^N->bool = {}") THENL
       [ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"{}:real^N->bool") THEN
        FIRST_X_ASSUM (MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
        ASM_SIMP_TAC [EMPTY_FACE_OF, CONIC_HULL_EMPTY, SUBSET_EMPTY],
        ASM_SIMP_TAC [FACE_OF_CONIC_HULL_REV]],
      ASM_SIMP_TAC [FACE_OF_SING, EXTREME_POINT_OF_CONIC_HULL],
      ASM_MESON_TAC [FACE_OF_CONIC_HULL]])

  let EXTREME_POINT_OF_CBALL ← prove
   r"!a r x:real^N.
        x extreme_point_of cball(a,r) <=> x IN sphere(a,r)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [MESON_TAC [EXTREME_POINT_IN_FRONTIER, FRONTIER_CBALL],
      GEOM_ORIGIN_TAC (← q r"a:real^N") THEN REWRITE_TAC [IN_SPHERE_0] THEN
      REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"r = &0") THEN
      ASM_SIMP_TAC [CBALL_SING, EXTREME_POINT_OF_SING, NORM_EQ_0] THEN
      STRIP_TAC THEN MATCH_MP_TAC EXTREME_POINT_RELATIVE_FRONTIER THEN
      ASM_REWRITE_TAC [CONVEX_CBALL, IN_CBALL_0, IN_DIFF, RELATIVE_INTERIOR_CBALL,
                       REAL_LE_REFL, IN_BALL_0, REAL_LT_REFL,
                       INSERT_SUBSET, EMPTY_SUBSET, IN_DIFF] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"x <= y /\ ~(x < y) <=> x = y")] THEN
      ASM_MESON_TAC [DIFFERENT_NORM_3_COLLINEAR_POINTS]])

  pure { extreme_point_of, EXTREME_POINT_RELATIVE_FRONTIER,
         EXTREME_POINT_OF_STILLCONVEX_IMP, EXTREME_POINTS_OF_STILLCONVEX,
         EXTREME_POINT_OF_STILLCONVEX, FACE_OF_SING, FACE_OF_AFF_DIM_0,
         EXTREME_POINT_NOT_IN_RELATIVE_INTERIOR, EXTREME_POINT_NOT_IN_INTERIOR,
         EXTREME_POINT_IN_RELATIVE_FRONTIER, EXTREME_POINT_IN_FRONTIER,
         EXTREME_POINT_OF_FACE, EXTREME_POINT_OF_MIDPOINT, EXTREME_POINT_OF_CONVEX_HULL,
         EXTREME_POINTS_OF_CONVEX_HULL, EXTREME_POINT_OF_EMPTY, EXTREME_POINT_OF_SING,
         EXTREME_POINT_OF_TRANSLATION_EQ, EXTREME_POINT_OF_LINEAR_IMAGE,
         EXTREME_POINTS_OF_TRANSLATION, EXTREME_POINT_OF_INTER, EXTREME_POINT_OF_INTER_GEN,
         EXTREME_POINTS_OF_LINEAR_IMAGE, EXTREME_POINT_OF_INTER_SUPPORTING_HYPERPLANE_LE,
         EXTREME_POINT_OF_INTER_SUPPORTING_HYPERPLANE_GE,
         EXPOSED_POINT_OF_INTER_SUPPORTING_HYPERPLANE_LE,
         EXPOSED_POINT_OF_INTER_SUPPORTING_HYPERPLANE_GE, EXPOSED_POINT_OF_FURTHEST_POINT,
         COLLINEAR_EXTREME_POINTS, EXTREME_POINT_OF_CONIC,
         EXTREME_POINT_OF_CONVEX_HULL_INSERT, FACE_OF_CONIC_HULL, FACE_OF_CONIC_HULL_REV,
         EXTREME_POINT_OF_CONIC_HULL, FACE_OF_CONIC_HULL_EQ, EXTREME_POINT_OF_CBALL }

/- ------------------------------------------------------------------------- -/
/- Closure and (relative) openness of conic hulls etc.                       -/
/- (polytope.ml 1960-2614)                                                   -/
/- ------------------------------------------------------------------------- -/

structure POF where
  CLOSED_IN_CONIC_HULL : thm
  CLOSED_CONIC_HULL : thm
  CONIC_CLOSURE : thm
  CLOSURE_CONIC_HULL : thm
  OPEN_IN_SAME_CONIC_HULL : thm
  OPEN_CONIC_HULL : thm
  OPEN_IN_CONIC_HULL : thm
  CONIC_INTERIOR_INSERT : thm
  CONIC_INTERIOR : thm
  CONIC_RELATIVE_INTERIOR_INSERT : thm
  CONIC_RELATIVE_INTERIOR : thm
  CONIC_HULL_RELATIVE_INTERIOR_SUBSET : thm
  CONIC_SUBSET_AS_CONIC_HULL : thm
  RELATIVE_INTERIOR_CONIC_HULL : thm
  CONIC_HULL_RELATIVE_INTERIOR : thm
  CONIC_HULL_DIFF : thm
  CONIC_HULL_INTER : thm
  INTER_CONIC_HULL_SUBSETS_CONVEX_RELATIVE_FRONTIER : thm
  RELATIVE_FRONTIER_CONIC_HULL : thm
  CONIC_HULL_RELATIVE_FRONTIER : thm
  INTER_CONIC_HULL : thm
  RELATIVE_INTERIOR_CONIC_HULL_0 : thm
  deriving Inhabited

set_option maxHeartbeats 4000000 in
@[nospecialize]
def setupPOF [HolBase] (D : PolytopeDeps) (BPOE : POE) : ExceptT String IO POF := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC, NORM_ARITH, REAL_ARITH, REAL_FIELD,
        REAL_RAT_REDUCE_CONV, REAL_RING, SET_RULE, SET_TAC, VECTOR_ARITH, .. } := D.cvx
  let { CONTRAPOS_THM, DE_MORGAN_THM, DIFF_EQ_EMPTY, EMPTY_DIFF, EMPTY_SUBSET, ETA_AX,
        EXISTS_REFL, EXTENSION, FORALL_IN_GSPEC, .. } := D.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_IN_INSERT, FORALL_PASTECART, FSTCART_PASTECART,
        IMAGE_SUBSET, IMP_CONJ, IMP_CONJ_ALT, IN_DELETE, IN_DIFF, INSERT_SUBSET, INTER_COMM,
        INTER_EMPTY, INTER_SUBSET, .. } := D.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_INTER, IN_SING, LEFT_IMP_EXISTS_THM,
        MEMBER_NOT_EMPTY, NOT_EXISTS_THM, NOT_IMP, NOT_IN_EMPTY, NOT_INSERT_EMPTY,
        PASTECART_IN_PCROSS, REAL_DIV_RMUL, .. } := D.cvx.core3
  let { REAL_ENTIRE, REAL_LE_INV_EQ, REAL_LE_LMUL, REAL_LE_LT, REAL_LE_RDIV_EQ,
        REAL_LE_REFL, REAL_LE_TRANS, REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_IMP_NZ,
        REAL_LT_LCANCEL_IMP, REAL_LT_LDIV_EQ, REAL_LT_LE, REAL_LT_MIN, REAL_LT_MUL,
        REAL_LT_RDIV_EQ, REAL_LT_REFL, .. } := D.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_LZERO, REAL_MUL_RINV, REAL_MUL_SYM, REAL_POS,
        RIGHT_EXISTS_AND_THM, SING_SUBSET, SNDCART_PASTECART, SUBSET, SUBSET_ANTISYM,
        SUBSET_ANTISYM_EQ, SUBSET_INTER, SUBSET_PCROSS, SUBSET_REFL, SUBSET_TRANS, .. } :=
        D.cvx.core5
  let { o_DEF, real_abs, real_div, real_ge, SUBSET_UNIV, SUM_CLAUSES, SUM_EQ, SUM_LMUL,
        SWAP_FORALL_THM, UNION_COMM, UNIONS_GSPEC, UNWIND_THM1, .. } := D.cvx.core6
  let { HULL_INC, HULL_MINIMAL, HULL_MONO, HULL_SUBSET, HULL_UNIV, .. } := D.cvx.misc
  let { DIST_0, DIST_LIFT, DOT_RMUL, DOT_RSUM, DOT_RZERO, .. } := D.cvx.vec1
  let { DROP_VEC, FORALL_DROP, LIFT_CMUL, LIFT_DROP, LINEAR_FSTCART, LINEAR_SCALING,
        LINEAR_SNDCART, .. } := D.cvx.vec2
  let { NORM_MUL, NORM_POS_LT, SPAN_0, SPAN_EXPLICIT, SPAN_INSERT_0, SPAN_MUL, SPAN_NEG,
        SPAN_SUPERSET, .. } := D.cvx.vec3
  let { dist, drop, VECTOR_ADD_LID, VECTOR_MUL_ASSOC, VECTOR_MUL_EQ_0, VECTOR_MUL_LCANCEL,
        VECTOR_MUL_LID, VECTOR_MUL_LZERO, VECTOR_MUL_RZERO, VECTOR_NEG_EQ_0, VECTOR_NEG_NEG,
        VECTOR_SUB_LDISTRIB, VECTOR_SUB_LZERO, VECTOR_SUB_RZERO, .. } := D.cvx.vec4
  let { OPEN_IN_EMPTY, OPEN_IN_IMP_SUBSET, OPEN_IN_INTER, OPEN_IN_SUBSET_TRANS,
        OPEN_IN_SUBTOPOLOGY_INTER_SUBSET, SUBTOPOLOGY_UNIV, .. } := D.cvx.met
  let { BETWEEN_IN_SEGMENT, BOUNDED_SUBSET, BOUNDED_SUBSET_CBALL,
        CLOSED_HALFSPACE_COMPONENT_GE, CLOSED_IN, CLOSURE_CLOSED, CLOSURE_EMPTY, .. } :=
        D.cvx.top1
  let { CLOSURE_MINIMAL, CLOSURE_SEQUENTIAL, CLOSURE_SING, CLOSURE_SUBSET, COMPACT_CLOSURE,
        COMPACT_EQ_BOUNDED_CLOSED, COMPACT_IMP_BOUNDED, COMPACT_IMP_CLOSED,
        CONTINUOUS_AT_ID, CONTINUOUS_AT_INV, .. } := D.cvx.top2
  let { CONTINUOUS_MUL, CONTINUOUS_ON_MUL, .. } := D.cvx.top3
  let { IN_BALL, IN_CBALL_0, IN_INTERIOR, IN_INTERVAL_1, IN_OPEN_SEGMENT, IN_SEGMENT,
        LIM_ADD, LIM_CMUL, LINEAR_CONTINUOUS_ON, .. } := D.cvx.top4
  let { continuous_at, OPEN_IN, open_in, OPEN_IN_INJECTIVE_LINEAR_IMAGE, OPEN_IN_REFL,
        SETDIST_LE_DIST, SETDIST_POS_LE, SUBSET_CLOSURE, .. } := D.cvx.top5
  let { DISJOINT_EMPTY, DISJOINT_INSERT, EMPTY_DELETE, EMPTY_UNION, REAL_WLOG_LT, .. } :=
        D.qses
  let { between, VECTOR_NEG_0, .. } := D.qvec
  let { HULL_INSERT, .. } := D.qmisc
  let { OPEN_IN_SUBTOPOLOGY_EMPTY, OPEN_IN_UNIONS, .. } := D.qmet
  let { BOUNDED_INTERVAL, BOUNDED_PCROSS, CLOSED_IN_REFL, CLOSED_PCROSS_EQ,
        CONTINUOUS_AT_LIFT_DOT, CONTINUOUS_CLOSED_PREIMAGE, CONTINUOUS_CMUL,
        FRONTIER_HALFSPACE_LE, INTERIOR_HALFSPACE_LE, OPEN_IN_DELETE, PROPER_MAP,
        SETDIST_EQ_0_SING, .. } := D.qtop
  let { AFFINE_AFFINE_HULL, AFFINE_BOUNDED_EQ_TRIVIAL, AFFINE_HULL_0_2_EXPLICIT,
        AFFINE_HULL_CLOSURE, AFFINE_HULL_CONIC_HULL, AFFINE_HULL_EMPTY,
        AFFINE_HULL_EQ_EMPTY, AFFINE_HULL_EQ_SPAN, AFFINE_HULL_EXPLICIT, AFFINE_HULLS_EQ,
        AFFINE_SING, AFFINE_SPAN, CLOSED_AFFINE_HULL, CLOSURE_SUBSET_AFFINE_HULL, .. } :=
        D.qcvx1
  let { CONIC_CONIC_HULL, CONIC_HULL_AS_IMAGE, CONIC_HULL_CONTAINS_0, CONIC_HULL_EMPTY,
        CONIC_HULL_EQ_AFFINE_HULL, CONIC_HULL_EQ_EMPTY, CONIC_HULL_EQ_SING,
        CONIC_HULL_EQ_SPAN, CONIC_HULL_EQ_SPAN_EQ, CONIC_HULL_EXPLICIT,
        CONIC_HULL_INTER_AFFINE_HULL, CONIC_HULL_SUBSET_SPAN, CONIC_IMAGE_MULTIPLE,
        CONIC_SPAN, CONIC_UNIV, CONVEX_HALFSPACE_LE, .. } := D.qcvx2
  let { conic, IN_RELATIVE_INTERIOR, IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT,
        IN_RELATIVE_INTERIOR_IN_OPEN_SEGMENT_EQ, INTERIOR_SUBSET_RELATIVE_INTERIOR,
        OPEN_IN_RELATIVE_INTERIOR, relative_frontier, RELATIVE_FRONTIER_NONEMPTY_INTERIOR,
        RELATIVE_FRONTIER_SING, RELATIVE_INTERIOR_AFFINE, RELATIVE_INTERIOR_CLOSURE_SUBSET,
        RELATIVE_INTERIOR_EMPTY, RELATIVE_INTERIOR_EQ_CLOSURE, RELATIVE_INTERIOR_MAXIMAL,
        RELATIVE_INTERIOR_SING, RELATIVE_INTERIOR_SUBSET,
        SEPARATING_HYPERPLANE_AFFINE_AFFINE, .. } := D.qcvx3
  let { EXTREME_POINT_NOT_IN_RELATIVE_INTERIOR, EXTREME_POINT_OF_CONIC_HULL, .. } := BPOE
  -- @@SCOPE END

  let CLOSED_IN_CONIC_HULL ← prove
   r"!s t:real^N->bool.
        compact t /\ ~(vec 0 IN t) /\ t SUBSET s
        ==> closed_in (subtopology euclidean (conic hull s))
                      (conic hull t)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [CONIC_HULL_AS_IMAGE] THEN
    MP_TAC (← ISPECL
     [← q r"\z. drop(fstcart z) % (sndcart z:real^N)",
      ← q r"{t | &0 <= drop t} PCROSS (t:real^N->bool)",
      ← q r"IMAGE (\z. drop(fstcart z) % (sndcart z:real^N))
             ({t | &0 <= drop t} PCROSS s)"]
     PROPER_MAP) THEN
    ASM_SIMP_TAC [IMAGE_SUBSET, SUBSET_PCROSS, SUBSET_REFL] THEN
    DISCH_THEN (MP_TAC o MATCH_MP (← TAUT (← q r"(p <=> q /\ r) ==> p ==> q"))) THEN
    ANTS_TAC THENL [ALL_TAC, SIMP_TAC [CLOSED_IN_REFL]] THEN
    REWRITE_TAC [← GSYM CONIC_HULL_AS_IMAGE] THEN
    X_GEN_TAC (← q r"k:real^N->bool") THEN STRIP_TAC THEN
    REWRITE_TAC [COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
      SIMP_TAC [CONTINUOUS_ON_MUL, o_DEF, LIFT_DROP, ETA_AX, LINEAR_CONTINUOUS_ON,
                LINEAR_FSTCART, LINEAR_SNDCART] THEN
      ASM_SIMP_TAC [CLOSED_PCROSS_EQ, COMPACT_IMP_CLOSED] THEN
      REWRITE_TAC [drop, ← GSYM real_ge, CLOSED_HALFSPACE_COMPONENT_GE]] THEN
    MP_TAC (← ISPECL [← q r"k:real^N->bool", ← q r"vec 0:real^N"]
          BOUNDED_SUBSET_CBALL) THEN
    ASM_SIMP_TAC [SUBSET, IN_CBALL_0, COMPACT_IMP_BOUNDED] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"r:real") STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC (← q r"interval[vec 0,lift(r / setdist({vec 0:real^N},t))] PCROSS
                (t:real^N->bool)") THEN
    ASM_SIMP_TAC [BOUNDED_PCROSS, BOUNDED_INTERVAL, COMPACT_IMP_BOUNDED] THEN
    REWRITE_TAC [SUBSET, FORALL_PASTECART, PASTECART_IN_PCROSS, IN_ELIM_THM] THEN
    REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART, IN_INTERVAL_1] THEN
    SIMP_TAC [← GSYM FORALL_DROP, LIFT_DROP, DROP_VEC] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real", ← q r"x:real^N"] THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"~(t:real^N->bool = {})") ASSUME_TAC THENL
     [ASM SET_TAC [], ALL_TAC] THEN
    ASM_SIMP_TAC [REAL_LE_RDIV_EQ, SETDIST_EQ_0_SING, CLOSURE_CLOSED,
                  COMPACT_IMP_CLOSED, SETDIST_POS_LE,
                  ← REAL_ARITH (← q r"&0 < x <=> &0 <= x /\ ~(x = &0)")] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"a % x:real^N")) THEN
    ASM_REWRITE_TAC [NORM_MUL, real_abs] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] REAL_LE_TRANS) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC [← NORM_ARITH (← q r"norm(x:real^N) = dist(vec 0,x)")] THEN
    MATCH_MP_TAC SETDIST_LE_DIST THEN ASM_REWRITE_TAC [IN_SING])

  let CLOSED_CONIC_HULL ← prove
   r"!s:real^N->bool.
     vec 0 IN relative_interior s \/ compact s /\ ~(vec 0 IN s)
     ==> closed(conic hull s)"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [CONIC_HULL_EQ_AFFINE_HULL, CLOSED_AFFINE_HULL] THEN
    MP_TAC (← ISPECL [← q r"(:real^N)", ← q r"s:real^N->bool"] CLOSED_IN_CONIC_HULL) THEN
    ASM_REWRITE_TAC [SUBSET_UNIV, HULL_UNIV, SUBTOPOLOGY_UNIV] THEN
    ASM_SIMP_TAC [← GSYM CLOSED_IN, COMPACT_IMP_CLOSED])

  let CONIC_CLOSURE ← prove
   r"!s:real^N->bool. conic s ==> conic(closure s)"
   (REWRITE_TAC [conic, CLOSURE_SEQUENTIAL] THEN
    GEN_TAC THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [← q r"x:real^N", ← q r"c:real"] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"a:num->real^N")) ASSUME_TAC) THEN
    EXISTS_TAC (← q r"\n. c % (a:num->real^N) n") THEN
    ASM_SIMP_TAC [LIM_ADD, LIM_CMUL])

  let CLOSURE_CONIC_HULL ← prove
   r"!s:real^N->bool.
        vec 0 IN relative_interior s \/ bounded s /\ ~(vec 0 IN closure s)
        ==> closure(conic hull s) = conic hull (closure s)"
   (REPEAT STRIP_TAC THENL
     [ASM_SIMP_TAC [CONIC_HULL_EQ_AFFINE_HULL, CLOSED_AFFINE_HULL,
                    CLOSURE_CLOSED] THEN
      CONV_TAC SYM_CONV THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM AFFINE_HULL_CLOSURE] THEN
      MATCH_MP_TAC CONIC_HULL_EQ_AFFINE_HULL THEN
      MP_TAC (← ISPEC (← q r"s:real^N->bool") RELATIVE_INTERIOR_CLOSURE_SUBSET) THEN
      ASM SET_TAC [],
      REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSURE_MINIMAL THEN
        SIMP_TAC [HULL_MONO, CLOSURE_SUBSET] THEN
        MATCH_MP_TAC CLOSED_CONIC_HULL THEN ASM_REWRITE_TAC [COMPACT_CLOSURE],
        MATCH_MP_TAC HULL_MINIMAL THEN SIMP_TAC [SUBSET_CLOSURE, HULL_SUBSET] THEN
        MATCH_MP_TAC CONIC_CLOSURE THEN REWRITE_TAC [CONIC_CONIC_HULL]]])

  let OPEN_IN_SAME_CONIC_HULL ← prove
   r"!u s:real^N->bool.
        conic u /\ open_in (subtopology euclidean u) s
        ==> open_in (subtopology euclidean u) (conic hull s DELETE vec 0)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
      (← q r"conic hull s DELETE (vec 0:real^N) =
       UNIONS {IMAGE (\x. c % x) s | &0 < c} DELETE vec 0")
    SUBST1_TAC THENL
     [REWRITE_TAC [UNIONS_GSPEC, CONIC_HULL_EXPLICIT] THEN
      REWRITE_TAC [EXTENSION, IN_ELIM_THM, REAL_LE_LT, IN_IMAGE, IN_DELETE] THEN
      MESON_TAC [VECTOR_MUL_EQ_0],
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_DELETE THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
    REWRITE_TAC [FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"c:real") THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"\x:real^N. c % x", ← q r"s:real^N->bool", ← q r"u:real^N->bool"]
     OPEN_IN_INJECTIVE_LINEAR_IMAGE) THEN
    ASM_SIMP_TAC [LINEAR_SCALING, VECTOR_MUL_LCANCEL, REAL_LT_IMP_NZ] THEN
    MATCH_MP_TAC (← ONCE_REWRITE_RULE [IMP_CONJ_ALT] OPEN_IN_SUBSET_TRANS) THEN
    ASM_SIMP_TAC [CONIC_IMAGE_MULTIPLE, SUBSET_REFL] THEN
    FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC [conic, SUBSET, REAL_LT_IMP_LE])

  let OPEN_CONIC_HULL ← prove
   r"!s:real^N->bool. open s ==> open(conic hull s DELETE vec 0)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"(:real^N)", ← q r"s:real^N->bool"] OPEN_IN_SAME_CONIC_HULL) THEN
    ASM_REWRITE_TAC [CONIC_UNIV, SUBTOPOLOGY_UNIV, ← GSYM OPEN_IN])

  let OPEN_IN_CONIC_HULL ← prove
   r"!u s:real^N->bool.
        open_in (subtopology euclidean (affine hull u)) s
        ==> open_in (subtopology euclidean (affine hull (conic hull u)))
                    (conic hull s DELETE vec 0)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"s:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [CONIC_HULL_EMPTY, EMPTY_DELETE, OPEN_IN_EMPTY] THEN
    ASM_REWRITE_TAC [AFFINE_HULL_CONIC_HULL] THEN
    ASM_CASES_TAC (← q r"u:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [AFFINE_HULL_EMPTY, OPEN_IN_SUBTOPOLOGY_EMPTY] THEN
    ASM_CASES_TAC (← q r"(vec 0:real^N) IN affine hull u") THENL
     [SUBGOAL_THEN
        (← q r"affine hull (vec 0 INSERT u:real^N->bool) = affine hull u")
      SUBST1_TAC THENL
       [MATCH_MP_TAC AFFINE_HULLS_EQ THEN
        ASM_REWRITE_TAC [INSERT_SUBSET, HULL_SUBSET] THEN
        MATCH_MP_TAC (← SET_RULE (← q r"vec 0 INSERT s SUBSET t ==> s SUBSET t")) THEN
        REWRITE_TAC [HULL_SUBSET],
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] OPEN_IN_SAME_CONIC_HULL) THEN
        ASM_SIMP_TAC [AFFINE_HULL_EQ_SPAN, CONIC_SPAN]],
      MP_TAC (← ISPECL [← q r"{vec 0:real^N}", ← q r"affine hull u:real^N->bool"]
          SEPARATING_HYPERPLANE_AFFINE_AFFINE) THEN
      ASM_REWRITE_TAC [AFFINE_SING, AFFINE_AFFINE_HULL, NOT_INSERT_EMPTY,
                       AFFINE_HULL_EQ_EMPTY, DISJOINT_INSERT, DISJOINT_EMPTY] THEN
      REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY, DOT_RZERO] THEN
      ONCE_REWRITE_TAC [← TAUT (← q r"p /\ q /\ r /\ s <=> r /\ p /\ q /\ s")] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"a:real^N")
        (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"b:real")
        (CONJUNCTS_THEN2 (ASSUME_TAC o GSYM) ASSUME_TAC)) THEN
      REWRITE_TAC [open_in] THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC (← SET_RULE (← q r"s SUBSET t ==> s DELETE a SUBSET t")) THEN
        TRANS_TAC SUBSET_TRANS (← q r"conic hull (affine hull u):real^N->bool") THEN
        ASM_SIMP_TAC [HULL_MONO] THEN ONCE_REWRITE_TAC [HULL_INSERT] THEN
        ASM_SIMP_TAC [AFFINE_HULL_EQ_SPAN, HULL_INC, IN_INSERT] THEN
        REWRITE_TAC [SPAN_INSERT_0, CONIC_HULL_SUBSET_SPAN],
        ALL_TAC] THEN
      SIMP_TAC [AFFINE_HULL_EQ_SPAN, HULL_INC, IN_INSERT, SPAN_INSERT_0] THEN
      REWRITE_TAC [IN_DELETE, IMP_CONJ, CONIC_HULL_EXPLICIT, FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [← q r"c:real", ← q r"x:real^N"] THEN
      REWRITE_TAC [VECTOR_MUL_EQ_0, DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC [← GSYM CONIC_HULL_EXPLICIT] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real^N")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"e:real") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"!x:real^N. x IN s ==> a dot x = b")
      ASSUME_TAC THENL [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(\y:real^N. lift(a dot y)) continuous (at (c % x))")
      ASSUME_TAC THENL
       [REWRITE_TAC [← REWRITE_RULE [o_DEF] CONTINUOUS_AT_LIFT_DOT],
        ALL_TAC] THEN
      FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [continuous_at]) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"a dot (c % x:real^N)")) THEN
      SUBGOAL_THEN (← q r"&0 < c") ASSUME_TAC THENL
       [ASM_REWRITE_TAC [REAL_LT_LE], ALL_TAC] THEN
      ASM_SIMP_TAC [DOT_RMUL, HULL_INC, REAL_LT_MUL, DIST_LIFT] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"k:real") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       (← q r"(\y:real^N. (b / (a dot y)) % y) continuous (at (c % x))")
      MP_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MUL THEN
        REWRITE_TAC [CONTINUOUS_AT_ID, o_DEF, LIFT_CMUL, real_div] THEN
        MATCH_MP_TAC CONTINUOUS_CMUL THEN
        MATCH_MP_TAC (← REWRITE_RULE [o_DEF] CONTINUOUS_AT_INV) THEN
        ASM_SIMP_TAC [DOT_RMUL, HULL_INC, REAL_ENTIRE, REAL_LT_IMP_NZ],
        ALL_TAC] THEN
      REWRITE_TAC [continuous_at] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"min e (norm(x:real^N))")) THEN
      ASM_REWRITE_TAC [REAL_LT_MIN, NORM_POS_LT] THEN
      ASM_SIMP_TAC [DOT_RMUL, HULL_INC, VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC [VECTOR_MUL_LID, ← REAL_FIELD
       (← q r"&0 < b /\ &0 < c ==> b / (c * b) * c = &1")] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN (fun th => tactic_of do pure (
        EXISTS_TAC (← q r"min d k:real") THEN ASM_REWRITE_TAC [REAL_LT_MIN] THEN
        X_GEN_TAC (← q r"y:real^N") THEN REPEAT DISCH_TAC THEN
        MP_TAC (← SPEC (← q r"y:real^N") th))) THEN
      ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
      UNDISCH_TAC (← q r"dist (b / (a dot y) % y:real^N,x) < norm x") THEN
      ASM_CASES_TAC (← q r"y:real^N = vec 0") THEN
      ASM_REWRITE_TAC [VECTOR_MUL_RZERO, DIST_0, REAL_LT_REFL] THEN
      DISCH_TAC THEN REWRITE_TAC [CONIC_HULL_EXPLICIT, IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC
       [← q r"(a dot (y:real^N)) / b", ← q r"(b / (a dot y)) % y:real^N"] THEN
      SUBGOAL_THEN (← q r"&0 < (a:real^N) dot y") ASSUME_TAC THENL
       [MATCH_MP_TAC (← REAL_ARITH (← q r"!y. &0 < y /\ abs(x - y) < y ==> &0 < x")) THEN
        EXISTS_TAC (← q r"c * b:real") THEN ASM_SIMP_TAC [REAL_LT_MUL],
        ASM_SIMP_TAC [REAL_LT_DIV, REAL_LT_IMP_LE]] THEN
      ASM_SIMP_TAC [VECTOR_MUL_ASSOC, VECTOR_MUL_LID, ← REAL_FIELD
       (← q r"&0 < a /\ &0 < b ==> a / b * b / a = &1")] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN
       (← q r"!z:real^N. z IN span u /\ a dot z = b ==> z IN affine hull u")
      MATCH_MP_TAC THENL
       [ALL_TAC,
        ASM_SIMP_TAC [SPAN_MUL, DOT_RMUL, REAL_DIV_RMUL, REAL_LT_IMP_NZ]] THEN
      X_GEN_TAC (← q r"z:real^N") THEN
      REWRITE_TAC [SPAN_EXPLICIT, AFFINE_HULL_EXPLICIT, IMP_CONJ] THEN
      REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"t:real^N->bool", ← q r"q:real^N->real"] THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [DOT_RSUM] THEN
      SUBGOAL_THEN
       (← q r"sum t (\x:real^N. a dot q x % x) = b * sum t q")
      SUBST1_TAC THENL
       [REWRITE_TAC [← GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
        RULE_ASSUM_TAC (REWRITE_RULE [SUBSET]) THEN
        ASM_SIMP_TAC [HULL_INC, DOT_RMUL, REAL_MUL_SYM],
        ASM_SIMP_TAC [← REAL_FIELD (← q r"&0 < b ==> (b * t = b <=> t = &1)")] THEN
        STRIP_TAC] THEN
      MAP_EVERY EXISTS_TAC [← q r"t:real^N->bool", ← q r"q:real^N->real"] THEN
      ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"sum (t:real^N->bool) q = &1") THEN
      ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
      SIMP_TAC [SUM_CLAUSES] THEN CONV_TAC REAL_RAT_REDUCE_CONV])

  let CONIC_INTERIOR_INSERT ← prove
   r"!s:real^N->bool. conic s ==> conic(vec 0 INSERT interior s)"
   (REWRITE_TAC [conic, IN_INTERIOR, SUBSET, IN_BALL, dist, IN_INSERT] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"x:real^N", ← q r"c:real"] THEN
    REWRITE_TAC [REAL_LE_LT] THEN
    ASM_CASES_TAC (← q r"c = &0") THEN ASM_REWRITE_TAC [VECTOR_MUL_EQ_0] THEN
    ASM_CASES_TAC (← q r"x:real^N = vec 0") THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"e:real") STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    EXISTS_TAC (← q r"c * e:real") THEN ASM_SIMP_TAC [REAL_LT_MUL] THEN
    X_GEN_TAC (← q r"y:real^N") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"inv(c) % y:real^N", ← q r"c:real"]) THEN
    ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_RINV, REAL_LT_IMP_NZ] THEN
    ASM_SIMP_TAC [VECTOR_MUL_LID, REAL_LT_IMP_LE] THEN
    DISCH_THEN MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC (← q r"abs c:real") THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC, REWRITE_TAC [← GSYM NORM_MUL]] THEN
    ASM_SIMP_TAC [real_abs, REAL_LT_IMP_LE, VECTOR_SUB_LDISTRIB] THEN
    ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_RINV, REAL_LT_IMP_NZ] THEN
    ASM_REWRITE_TAC [VECTOR_MUL_LID])

  let CONIC_INTERIOR ← prove
   r"!s:real^N->bool. conic s /\ vec 0 IN interior s ==> conic(interior s)"
   (MESON_TAC [← SET_RULE (← q r"a IN s ==> a INSERT s = s"), CONIC_INTERIOR_INSERT])

  let CONIC_RELATIVE_INTERIOR_INSERT ← prove
   r"!s:real^N->bool. conic s ==> conic(vec 0 INSERT relative_interior s)"
   (REWRITE_TAC [conic, IN_RELATIVE_INTERIOR, SUBSET,
                 IN_INTER, IN_BALL, dist, IN_INSERT] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"x:real^N", ← q r"c:real"] THEN
    REWRITE_TAC [REAL_LE_LT] THEN
    ASM_CASES_TAC (← q r"c = &0") THEN ASM_REWRITE_TAC [VECTOR_MUL_EQ_0] THEN
    ASM_CASES_TAC (← q r"x:real^N = vec 0") THEN
    ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN
    DISCH_THEN (CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"e:real") STRIP_ASSUME_TAC))
      ASSUME_TAC) THEN
    EXISTS_TAC (← q r"c * e:real") THEN ASM_SIMP_TAC [REAL_LT_MUL] THEN
    X_GEN_TAC (← q r"y:real^N") THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o SPECL [← q r"x:real^N", ← q r"&0"]) THEN
    REWRITE_TAC [REAL_LE_REFL, VECTOR_MUL_LZERO] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"inv(c) % y:real^N", ← q r"c:real"]) THEN
    ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_RINV, REAL_LT_IMP_NZ] THEN
    ASM_SIMP_TAC [VECTOR_MUL_LID, REAL_LT_IMP_LE] THEN
    DISCH_THEN MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [ALL_TAC, ASM_MESON_TAC [SPAN_MUL, AFFINE_HULL_EQ_SPAN, HULL_INC]] THEN
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC (← q r"abs c:real") THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC, REWRITE_TAC [← GSYM NORM_MUL]] THEN
    ASM_SIMP_TAC [real_abs, REAL_LT_IMP_LE, VECTOR_SUB_LDISTRIB] THEN
    ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_RINV, REAL_LT_IMP_NZ] THEN
    ASM_REWRITE_TAC [VECTOR_MUL_LID])

  let CONIC_RELATIVE_INTERIOR ← prove
   r"!s:real^N->bool.
        conic s /\ vec 0 IN relative_interior s
        ==> conic(relative_interior s)"
   (MESON_TAC [← SET_RULE (← q r"a IN s ==> a INSERT s = s"),
               CONIC_RELATIVE_INTERIOR_INSERT])

  let CONIC_HULL_RELATIVE_INTERIOR_SUBSET ← prove
   r"!s:real^N->bool.
        conic hull (relative_interior s) DELETE (vec 0) SUBSET
        relative_interior(conic hull s)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC RELATIVE_INTERIOR_MAXIMAL THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC (← SET_RULE (← q r"s SUBSET t ==> s DELETE a SUBSET t")) THEN
      MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC [RELATIVE_INTERIOR_SUBSET],
      MATCH_MP_TAC OPEN_IN_CONIC_HULL THEN
      REWRITE_TAC [OPEN_IN_RELATIVE_INTERIOR]])

  let CONIC_SUBSET_AS_CONIC_HULL ← prove
   r"!s c:real^N->bool.
        conic c /\ ~(c = {vec 0}) /\ c SUBSET conic hull s
        ==> conic hull (s INTER c) = c"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN
    ASM_SIMP_TAC [HULL_MINIMAL, INTER_SUBSET] THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
     (← q r"c SUBSET k ==> (!x. x IN k ==> x IN c ==> x IN u) ==> c SUBSET u"))) THEN
    REWRITE_TAC [CONIC_HULL_EXPLICIT, FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real", ← q r"x:real^N"] THEN
    ASM_CASES_TAC (← q r"a % x:real^N = vec 0") THENL
     [ASM_REWRITE_TAC [← GSYM CONIC_HULL_EXPLICIT] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC [CONIC_HULL_CONTAINS_0] THEN
      SUBGOAL_THEN (← q r"?y:real^N. ~(y = vec 0) /\ y IN c") STRIP_ASSUME_TAC THENL
       [ASM SET_TAC [], ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"y:real^N") o REWRITE_RULE [SUBSET]) THEN
      ASM_REWRITE_TAC [IN_ELIM_THM, CONIC_HULL_EXPLICIT, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"b:real", ← q r"z:real^N"] THEN
      ASM_CASES_TAC (← q r"b = &0") THEN ASM_REWRITE_TAC [VECTOR_MUL_LZERO] THEN
      ASM_REWRITE_TAC [REAL_LE_LT, ← GSYM MEMBER_NOT_EMPTY] THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"z:real^N") THEN ASM_REWRITE_TAC [IN_INTER] THEN
      SUBGOAL_THEN (← q r"z:real^N = inv b % y") SUBST1_TAC THENL
       [ASM_SIMP_TAC [VECTOR_MUL_ASSOC, VECTOR_MUL_LID, REAL_MUL_LINV],
        ASM_MESON_TAC [conic, REAL_LT_IMP_LE, REAL_LE_INV_EQ]],
      UNDISCH_TAC (← q r"~(a % x:real^N = vec 0)") THEN
      SIMP_TAC [VECTOR_MUL_EQ_0, DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC [IN_ELIM_THM, IN_INTER] THEN
      MAP_EVERY EXISTS_TAC [← q r"a:real", ← q r"x:real^N"] THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"x:real^N = inv a % a % x") SUBST1_TAC THENL
       [ASM_SIMP_TAC [VECTOR_MUL_ASSOC, VECTOR_MUL_LID, REAL_MUL_LINV],
        ASM_MESON_TAC [conic, REAL_LT_IMP_LE, REAL_LE_INV_EQ]]])

  let RELATIVE_INTERIOR_CONIC_HULL ← prove
   r"!s:real^N->bool.
        ~(vec 0 IN affine hull s)
        ==> relative_interior(conic hull s) =
            conic hull (relative_interior s) DELETE (vec 0)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC [CONIC_HULL_RELATIVE_INTERIOR_SUBSET] THEN
    ASM_CASES_TAC (← q r"s:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [CONIC_HULL_EMPTY, RELATIVE_INTERIOR_EMPTY, EMPTY_SUBSET] THEN
    ASM_CASES_TAC (← q r"relative_interior (conic hull s):real^N->bool = {}") THEN
    ASM_REWRITE_TAC [EMPTY_SUBSET] THEN
    SUBGOAL_THEN
     (← q r"~((vec 0:real^N) IN relative_interior(conic hull s))")
    ASSUME_TAC THENL
     [MATCH_MP_TAC EXTREME_POINT_NOT_IN_RELATIVE_INTERIOR THEN
      ASM_SIMP_TAC [EXTREME_POINT_OF_CONIC_HULL, CONIC_HULL_EQ_SING] THEN
      ASM_MESON_TAC [IN_SING, HULL_INC],
      ALL_TAC] THEN
    MATCH_MP_TAC (← SET_RULE
     (← q r"~(a IN t) /\ a INSERT t SUBSET s ==> t SUBSET s DELETE a")) THEN
    ASM_REWRITE_TAC [] THEN
    TRANS_TAC SUBSET_TRANS
     (← q r"conic hull
        ((vec 0 INSERT relative_interior (conic hull s:real^N->bool)) INTER
          affine hull s)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC (← SET_RULE (← q r"s = t ==> t SUBSET s")) THEN
      ONCE_REWRITE_TAC [INTER_COMM] THEN
      MATCH_MP_TAC CONIC_SUBSET_AS_CONIC_HULL THEN REPEAT CONJ_TAC THENL
       [SIMP_TAC [CONIC_RELATIVE_INTERIOR_INSERT, CONIC_CONIC_HULL],
        ASM SET_TAC [],
        ASM_REWRITE_TAC [INSERT_SUBSET, CONIC_HULL_CONTAINS_0] THEN
        ASM_REWRITE_TAC [AFFINE_HULL_EQ_EMPTY] THEN
        TRANS_TAC SUBSET_TRANS (← q r"conic hull s:real^N->bool") THEN
        SIMP_TAC [RELATIVE_INTERIOR_SUBSET, HULL_MONO, HULL_SUBSET]],
      MATCH_MP_TAC HULL_MINIMAL THEN
      ASM_SIMP_TAC [CONIC_CONIC_HULL, ← SET_RULE
       (← q r"~(a IN t) ==> (a INSERT s) INTER t = s INTER t")] THEN
      TRANS_TAC SUBSET_TRANS (← q r"relative_interior s:real^N->bool") THEN
      REWRITE_TAC [HULL_SUBSET] THEN MATCH_MP_TAC RELATIVE_INTERIOR_MAXIMAL THEN
      CONJ_TAC THENL
       [MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"s:real^N->bool"]
          CONIC_HULL_INTER_AFFINE_HULL) THEN
        ASM_REWRITE_TAC [SUBSET_REFL] THEN DISCH_THEN (fun th => tactic_of do
          pure (GEN_REWRITE_TAC RAND_CONV [← SYM th])) THEN
        MP_TAC (← ISPEC (← q r"conic hull s:real^N->bool") RELATIVE_INTERIOR_SUBSET) THEN
        SET_TAC [],
        ONCE_REWRITE_TAC [INTER_COMM] THEN
        MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_SUBSET THEN
        EXISTS_TAC (← q r"affine hull (conic hull s):real^N->bool") THEN
        SIMP_TAC [HULL_SUBSET, HULL_MONO] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
        REWRITE_TAC [OPEN_IN_REFL, OPEN_IN_RELATIVE_INTERIOR]]])

  let CONIC_HULL_RELATIVE_INTERIOR ← prove
   r"!s:real^N->bool.
        ~(vec 0 IN affine hull s)
        ==> conic hull (relative_interior s) =
            if relative_interior s = {} then {}
            else (vec 0) INSERT relative_interior(conic hull s)"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [RELATIVE_INTERIOR_EMPTY, CONIC_HULL_EMPTY] THEN
    ASM_SIMP_TAC [RELATIVE_INTERIOR_CONIC_HULL] THEN MATCH_MP_TAC (← SET_RULE
     (← q r"a IN s ==> s = a INSERT (s DELETE a)")) THEN
    ASM_REWRITE_TAC [CONIC_HULL_CONTAINS_0])

  let CONIC_HULL_DIFF ← prove
   r"!s t:real^N->bool.
        ~(vec 0 IN affine hull s) /\ t SUBSET s
        ==> conic hull (s DIFF t) =
            if t = s then {}
            else conic hull s DIFF (conic hull t DELETE vec 0)"
   (REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [DIFF_EQ_EMPTY, CONIC_HULL_EMPTY] THEN
    REWRITE_TAC [EXTENSION, IN_DIFF, IN_DELETE,
                 CONIC_HULL_EXPLICIT, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"y:real^N") THEN ASM_CASES_TAC (← q r"y:real^N = vec 0") THEN
    ASM_REWRITE_TAC [] THENL
     [EQ_TAC THENL [MESON_TAC [], STRIP_TAC] THEN
      EXISTS_TAC (← q r"&0") THEN REWRITE_TAC [VECTOR_MUL_LZERO, REAL_LE_REFL] THEN
      ASM SET_TAC [],
      ALL_TAC] THEN
    EQ_TAC THENL [REWRITE_TAC [LEFT_IMP_EXISTS_THM], MESON_TAC []] THEN
    MAP_EVERY X_GEN_TAC [← q r"c:real", ← q r"x:real^N"] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC [], REWRITE_TAC [NOT_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [← q r"d:real", ← q r"z:real^N"] THEN ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN SUBGOAL_THEN (← q r"vec 0 IN affine hull {x:real^N,z}") MP_TAC THENL
     [REWRITE_TAC [AFFINE_HULL_0_2_EXPLICIT] THEN
      MAP_EVERY EXISTS_TAC [← q r"c:real", ← q r"--d:real"] THEN
      ASM_REWRITE_TAC [← VECTOR_ARITH
       (← q r"a + --b % y:real^N = vec 0 <=> a = b % y")] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"a + --b = &0 <=> a = b")] THEN DISCH_TAC THEN
      UNDISCH_TAC (← q r"c % x:real^N = d % z") THEN
      ASM_SIMP_TAC [VECTOR_MUL_LCANCEL, REAL_LT_IMP_NZ] THEN
      ASM_MESON_TAC [VECTOR_MUL_LZERO],
      FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
       (← q r"~(z IN s) ==> t SUBSET s ==> z IN t ==> F"))) THEN
      MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC []])

  let CONIC_HULL_INTER ← prove
   r"!s t:real^N->bool.
        ~(vec 0 IN affine hull (s UNION t))
        ==> conic hull (s INTER t) =
            if s INTER t = {} then {}
            else conic hull s INTER conic hull t"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"s INTER t:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [CONIC_HULL_EMPTY] THEN REWRITE_TAC [CONIC_HULL_EXPLICIT] THEN
    REWRITE_TAC [EXTENSION, IN_INTER, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"z:real^N") THEN EQ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
    REWRITE_TAC [IMP_CONJ, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"c:real", ← q r"x:real^N"] THEN REPEAT DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"d:real", ← q r"y:real^N"] THEN REPEAT DISCH_TAC THEN
    ASM_CASES_TAC (← q r"z:real^N = vec 0") THENL
     [EXISTS_TAC (← q r"&0") THEN ASM_REWRITE_TAC [REAL_POS, VECTOR_MUL_LZERO] THEN
      ASM SET_TAC [],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"c:real = d") THENL
     [SUBGOAL_THEN (← q r"x:real^N = y") SUBST_ALL_TAC THEN
      ASM_MESON_TAC [VECTOR_MUL_RZERO, VECTOR_MUL_LCANCEL],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"vec 0 IN affine hull {x:real^N,y}") MP_TAC THENL
     [REWRITE_TAC [AFFINE_HULL_0_2_EXPLICIT] THEN
      MAP_EVERY EXISTS_TAC [← q r"c:real", ← q r"--d:real"] THEN
      ASM_REWRITE_TAC [← VECTOR_ARITH
       (← q r"a + --b % y:real^N = vec 0 <=> a = b % y")] THEN
      ASM_REWRITE_TAC [← REAL_ARITH (← q r"a + --b = &0 <=> a = b")] THEN
      ASM_MESON_TAC [],
      FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
       (← q r"!q t. ~(z IN s) ==> t SUBSET s ==> z IN t ==> q"))) THEN
      MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC []])

  let INTER_CONIC_HULL_SUBSETS_CONVEX_RELATIVE_FRONTIER ← prove
   r"!s t u:real^N->bool.
        convex u /\ vec 0 IN relative_interior u /\
        s UNION t SUBSET relative_frontier u
        ==> conic hull s INTER conic hull t =
            if s = {} \/ t = {} then {}
            else if s INTER t = {} then {vec 0}
            else conic hull (s INTER t)"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"s:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [CONIC_HULL_EMPTY, INTER_EMPTY] THEN
    ASM_CASES_TAC (← q r"t:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [CONIC_HULL_EMPTY, INTER_EMPTY] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC,
      COND_CASES_TAC THEN REWRITE_TAC [SUBSET_INTER] THEN
      SIMP_TAC [HULL_MONO, INTER_SUBSET, SING_SUBSET] THEN
      ASM_REWRITE_TAC [CONIC_HULL_CONTAINS_0]] THEN
    MATCH_MP_TAC (← SET_RULE
     (← q r"s DELETE vec 0 SUBSET t /\ vec 0 IN t ==> s SUBSET t")) THEN
    CONJ_TAC THENL [ALL_TAC, MESON_TAC [CONIC_HULL_CONTAINS_0, IN_SING]] THEN
    TRANS_TAC SUBSET_TRANS (← q r"conic hull (s INTER t) DELETE (vec 0:real^N)") THEN
    CONJ_TAC THENL
     [ALL_TAC,
      COND_CASES_TAC THEN ASM_REWRITE_TAC [CONIC_HULL_EMPTY] THEN SET_TAC []] THEN
    REWRITE_TAC [CONIC_HULL_EXPLICIT, SUBSET, IN_DELETE, IN_INTER] THEN
    X_GEN_TAC (← q r"z:real^N") THEN
    ASM_CASES_TAC (← q r"z:real^N = vec 0") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [IN_ELIM_THM, IMP_CONJ, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"c:real", ← q r"x:real^N"] THEN REPEAT DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"d:real", ← q r"y:real^N"] THEN REPEAT DISCH_TAC THEN
    ASM_CASES_TAC (← q r"z:real^N = vec 0") THENL
     [EXISTS_TAC (← q r"&0") THEN ASM_REWRITE_TAC [REAL_POS, VECTOR_MUL_LZERO] THEN
      ASM SET_TAC [],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"c:real = d") THENL
     [SUBGOAL_THEN (← q r"x:real^N = y") SUBST_ALL_TAC THEN
      ASM_MESON_TAC [VECTOR_MUL_RZERO, VECTOR_MUL_LCANCEL],
      ALL_TAC] THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist CONJ) THEN
    MAP_EVERY (fun t => SPEC_TAC (t, t))
     [← q r"y:real^N", ← q r"x:real^N", ← q r"z:real^N", ← q r"t:real^N->bool",
      ← q r"s:real^N->bool", ← q r"d:real", ← q r"c:real"] THEN
    MATCH_MP_TAC REAL_WLOG_LT THEN REWRITE_TAC [] THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [SWAP_FORALL_THM] THEN
      REPLICATE_TAC 3 (AP_TERM_TAC THEN ABS_TAC) THEN
      GEN_REWRITE_TAC RAND_CONV [SWAP_FORALL_THM] THEN
      REPLICATE_TAC 2 (AP_TERM_TAC THEN ABS_TAC) THEN
      MESON_TAC [INTER_COMM, UNION_COMM],
      REPEAT STRIP_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"u:real^N->bool", ← q r"vec 0:real^N", ← q r"x:real^N"]
          IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← TAUT (← q r"p /\ ~q ==> (p ==> q) ==> r")) THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC (REWRITE_RULE [relative_frontier]) THEN ASM SET_TAC [],
      REWRITE_TAC [SUBSET, IN_SEGMENT]] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"y:real^N")) THEN
    REWRITE_TAC [NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [VECTOR_MUL_RZERO],
      EXISTS_TAC (← q r"c / d:real"),
      RULE_ASSUM_TAC (REWRITE_RULE [relative_frontier]) THEN ASM SET_TAC []] THEN
    SUBGOAL_THEN (← q r"&0 < d") ASSUME_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    ASM_SIMP_TAC [REAL_LT_LDIV_EQ, REAL_LT_RDIV_EQ] THEN
    ASM_REWRITE_TAC [REAL_MUL_LID, VECTOR_MUL_RZERO, VECTOR_ADD_LID] THEN
    ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_LT_LE] THEN
    CONJ_TAC THENL [ASM_MESON_TAC [VECTOR_MUL_LZERO], ALL_TAC] THEN
    UNDISCH_TAC (← q r"z:real^N = c % x") THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"(%) (inv d):real^N->real^N")) THEN
    ASM_REWRITE_TAC [VECTOR_MUL_ASSOC, real_div] THEN
    ASM_SIMP_TAC [REAL_MUL_LINV, REAL_LT_IMP_NZ, VECTOR_MUL_LID] THEN
    REWRITE_TAC [real_div, REAL_MUL_SYM])

  let RELATIVE_FRONTIER_CONIC_HULL ← prove
   r"!s:real^N->bool.
        bounded s /\ ~(vec 0 IN affine hull s)
        ==> relative_frontier(conic hull s) =
            if ?a. s = {a} then {vec 0}
            else conic hull (relative_frontier s)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"~((vec 0:real^N) IN closure s)") ASSUME_TAC THENL
     [MP_TAC (← ISPEC (← q r"s:real^N->bool") CLOSURE_SUBSET_AFFINE_HULL) THEN
      ASM SET_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [relative_frontier] THEN ASM_SIMP_TAC [CLOSURE_CONIC_HULL] THEN
    ASM_SIMP_TAC [RELATIVE_INTERIOR_CONIC_HULL] THEN
    ASM_CASES_TAC (← q r"affine(s:real^N->bool)") THENL
     [FIRST_ASSUM (fun th => tactic_of do
       pure (REWRITE_TAC [← GEN_REWRITE_RULE I
         [← GSYM RELATIVE_INTERIOR_EQ_CLOSURE] th])) THEN
      REWRITE_TAC [DIFF_EQ_EMPTY, CONIC_HULL_EMPTY] THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP AFFINE_BOUNDED_EQ_TRIVIAL) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (DISJ_CASES_THEN2
       SUBST1_TAC (X_CHOOSE_THEN (← q r"a:real^N") SUBST_ALL_TAC)) THEN
      ASM_REWRITE_TAC [CLOSURE_EMPTY, CONIC_HULL_EMPTY, EMPTY_DIFF,
        CLOSURE_SING, RELATIVE_INTERIOR_SING, NOT_INSERT_EMPTY] THEN
      REWRITE_TAC [← SET_RULE (← q r"{a} = {b} <=> b = a"), EXISTS_REFL] THEN
      MATCH_MP_TAC (← SET_RULE (← q r"a IN s ==> s DIFF (s DELETE a) = {a}")) THEN
      ASM_REWRITE_TAC [CONIC_HULL_CONTAINS_0, CONIC_HULL_EQ_EMPTY] THEN
      REWRITE_TAC [NOT_INSERT_EMPTY],
      COND_CASES_TAC THENL [ASM_MESON_TAC [AFFINE_SING], ALL_TAC] THEN
      W (MP_TAC o PART_MATCH (lhs o rand) CONIC_HULL_DIFF o rand o snd) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [AFFINE_HULL_CLOSURE] THEN
        MESON_TAC [RELATIVE_INTERIOR_SUBSET, CLOSURE_SUBSET, SUBSET],
        ASM_SIMP_TAC [RELATIVE_INTERIOR_EQ_CLOSURE]]])

  let CONIC_HULL_RELATIVE_FRONTIER ← prove
   r"!s:real^N->bool.
        bounded s /\ ~(vec 0 IN affine hull s)
        ==> conic hull (relative_frontier s) =
            if ?a. s = {a} then {}
            else relative_frontier(conic hull s)"
   (REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [RELATIVE_FRONTIER_CONIC_HULL] THEN
    FIRST_X_ASSUM (CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC [RELATIVE_FRONTIER_SING, CONIC_HULL_EMPTY])

  let INTER_CONIC_HULL ← prove
   r"!s t:real^N->bool.
        ~(vec 0 IN affine hull (s UNION t))
        ==> conic hull s INTER conic hull t =
            if s = {} \/ t = {} then {}
            else if s INTER t = {} then {vec 0}
            else conic hull (s INTER t)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"{vec 0:real^N}", ← q r"affine hull (s UNION t):real^N->bool"]
        SEPARATING_HYPERPLANE_AFFINE_AFFINE) THEN
    REWRITE_TAC [AFFINE_SING, AFFINE_AFFINE_HULL, NOT_INSERT_EMPTY] THEN
    REWRITE_TAC [AFFINE_HULL_EQ_EMPTY, EMPTY_UNION] THEN
    ASM_REWRITE_TAC [← SET_RULE (← q r"DISJOINT {x} s <=> ~(x IN s)")] THEN
    ASM_CASES_TAC (← q r"s:real^N->bool = {} /\ t:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [CONIC_HULL_EMPTY, INTER_EMPTY, LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY, DOT_RZERO] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"b:real", ← q r"c:real"] THEN
    ASM_CASES_TAC (← q r"b:real = &0") THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    MATCH_MP_TAC INTER_CONIC_HULL_SUBSETS_CONVEX_RELATIVE_FRONTIER THEN
    EXISTS_TAC (← q r"{x:real^N | a dot x <= c}") THEN
    REWRITE_TAC [CONVEX_HALFSPACE_LE] THEN
    SUBGOAL_THEN (← q r"(vec 0:real^N) IN interior {x | a dot x <= c}") ASSUME_TAC THENL
     [ASM_SIMP_TAC [INTERIOR_HALFSPACE_LE, IN_ELIM_THM, DOT_RZERO], ALL_TAC] THEN
    ASM_SIMP_TAC [← REWRITE_RULE [SUBSET] INTERIOR_SUBSET_RELATIVE_INTERIOR] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP (← SET_RULE (← q r"a IN s ==> ~(s = {})"))) THEN
    ASM_SIMP_TAC [RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN
    ASM_SIMP_TAC [FRONTIER_HALFSPACE_LE, SUBSET, IN_ELIM_THM] THEN
    ASM_MESON_TAC [HULL_INC])

  let RELATIVE_INTERIOR_CONIC_HULL_0 ← prove
   r"!s:real^N->bool.
        convex s
        ==> (vec 0 IN relative_interior(conic hull s) <=>
             vec 0 IN relative_interior s)"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"s:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [CONIC_HULL_EMPTY, RELATIVE_INTERIOR_EMPTY, NOT_IN_EMPTY] THEN
    ASM_CASES_TAC (← q r"(vec 0:real^N) IN affine hull s") THENL
     [ALL_TAC,
      ASM_SIMP_TAC [RELATIVE_INTERIOR_CONIC_HULL, IN_DELETE] THEN
      ASM_MESON_TAC [SUBSET, HULL_INC, RELATIVE_INTERIOR_SUBSET]] THEN
    ASM_CASES_TAC (← q r"conic hull s:real^N->bool = span s") THENL
     [ALL_TAC,
      ASM_MESON_TAC [CONIC_HULL_EQ_SPAN, CONIC_HULL_EQ_SPAN_EQ]] THEN
    ASM_SIMP_TAC [RELATIVE_INTERIOR_AFFINE, AFFINE_SPAN, SPAN_0] THEN
    ASM_SIMP_TAC [IN_RELATIVE_INTERIOR_IN_OPEN_SEGMENT_EQ] THEN
    X_GEN_TAC (← q r"x:real^N") THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(--x:real^N) IN conic hull s") MP_TAC THENL
     [ASM_SIMP_TAC [SPAN_NEG, SPAN_SUPERSET], ALL_TAC] THEN
    REWRITE_TAC [CONIC_HULL_EXPLICIT, IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"a:real") THEN ASM_CASES_TAC (← q r"a = &0") THEN
    ASM_REWRITE_TAC [VECTOR_MUL_LZERO, VECTOR_NEG_EQ_0, REAL_LE_LT] THEN
    X_GEN_TAC (← q r"y:real^N") THEN STRIP_TAC THEN EXISTS_TAC (← q r"y:real^N") THEN
    ASM_REWRITE_TAC [IN_OPEN_SEGMENT] THEN CONJ_TAC THENL
     [REWRITE_TAC [← GSYM BETWEEN_IN_SEGMENT, between] THEN
      ONCE_REWRITE_TAC [← NORM_ARITH (← q r"dist(a:real^N,b) = dist(--a,--b)")] THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [dist, VECTOR_SUB_LZERO, VECTOR_NEG_0, VECTOR_NEG_NEG,
         VECTOR_SUB_RZERO, ← VECTOR_ARITH (← q r"a % y - --y:real^N = (a + &1) % y")] THEN
      REWRITE_TAC [NORM_MUL] THEN MATCH_MP_TAC (← REAL_RING
       (← q r"a = b + &1 ==> a * y = b * y + y")) THEN
      ASM_REAL_ARITH_TAC,
      ASM_MESON_TAC [VECTOR_MUL_RZERO, VECTOR_NEG_EQ_0]])

  pure { CLOSED_IN_CONIC_HULL, CLOSED_CONIC_HULL, CONIC_CLOSURE, CLOSURE_CONIC_HULL,
         OPEN_IN_SAME_CONIC_HULL, OPEN_CONIC_HULL, OPEN_IN_CONIC_HULL,
         CONIC_INTERIOR_INSERT, CONIC_INTERIOR, CONIC_RELATIVE_INTERIOR_INSERT,
         CONIC_RELATIVE_INTERIOR, CONIC_HULL_RELATIVE_INTERIOR_SUBSET,
         CONIC_SUBSET_AS_CONIC_HULL, RELATIVE_INTERIOR_CONIC_HULL,
         CONIC_HULL_RELATIVE_INTERIOR, CONIC_HULL_DIFF, CONIC_HULL_INTER,
         INTER_CONIC_HULL_SUBSETS_CONVEX_RELATIVE_FRONTIER, RELATIVE_FRONTIER_CONIC_HULL,
         CONIC_HULL_RELATIVE_FRONTIER, INTER_CONIC_HULL, RELATIVE_INTERIOR_CONIC_HULL_0 }

/- ------------------------------------------------------------------------- -/
/- Facets; extreme points in low dimension; edges; existence of extreme      -/
/- points; Krein-Milman.  (polytope.ml 2615-3053)                            -/
/- ------------------------------------------------------------------------- -/

structure POG where
  facet_of : thm
  FACET_OF_EMPTY : thm
  FACET_OF_REFL : thm
  FACET_OF_IMP_FACE_OF : thm
  FACET_OF_IMP_SUBSET : thm
  FACET_OF_IMP_PROPER : thm
  FACET_OF_TRANSLATION_EQ : thm
  FACET_OF_LINEAR_IMAGE : thm
  HYPERPLANE_FACET_OF_HALFSPACE_LE : thm
  HYPERPLANE_FACET_OF_HALFSPACE_GE : thm
  FACET_OF_HALFSPACE_LE : thm
  FACET_OF_HALFSPACE_GE : thm
  EXPOSED_FACET_OF : thm
  OPEN_IN_RELATIVE_FRONTIER_INTERIOR_FACET : thm
  CLOSED_EXTREME_POINTS_2D : thm
  edge_of : thm
  EDGE_OF_TRANSLATION_EQ : thm
  EDGE_OF_LINEAR_IMAGE : thm
  EDGE_OF_IMP_SUBSET : thm
  EXTREME_POINT_EXISTS_CONVEX : thm
  KREIN_MILMAN : thm
  KREIN_MILMAN_MINKOWSKI : thm
  KREIN_MILMAN_EQ : thm
  deriving Inhabited

set_option maxHeartbeats 4000000 in
@[nospecialize]
def setupPOG [HolBase] (D : PolytopeDeps) (BPOA : POA) (BPOC : POC) (BPOD : POD) (BPOE : POE) (BPOF : POF) : ExceptT String IO POG := do
  -- @@SCOPE BEGIN
  let { add_linear_invariants, add_translation_invariants, ASM_MESON_TAC,
        ASM_REAL_ARITH_TAC, GEOM_ORIGIN_TAC, GEOM_TRANSFORM_TAC, GEOM_TRANSLATE_TAC,
        INT_ARITH, INT_ARITH_TAC, MESON_TAC, new_definition, parse_as_infix, REAL_ARITH,
        REAL_RING, SET_RULE, SET_TAC, VECTOR_ARITH, .. } := D.cvx
  let { WF_INDUCT_TAC, .. } := D
  let { DISJOINT, EMPTY_GSPEC, EMPTY_UNIONS, EQ_IMP, EXTENSION, FORALL_IN_GSPEC, .. } :=
        D.cvx.core1
  let { IMP_IMP, IN_DIFF, INSERT_SUBSET, INTER_SUBSET, INTER_UNIONS, .. } := D.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, IN_INTER, LEFT_IMP_EXISTS_THM, LEFT_OR_DISTRIB,
        MEMBER_NOT_EMPTY, MONO_EXISTS, NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IN_EMPTY, NOT_LE,
        .. } := D.cvx.core3
  let { REAL_EQ_NEG2, REAL_LE_LMUL_EQ, REAL_LE_NEG2, REAL_LE_REFL, REAL_LE_TRANS,
        REAL_LT_IMP_LE, REAL_LT_LMUL_EQ, REAL_LT_REFL, .. } := D.cvx.core4
  let { REAL_NOT_LT, REAL_SUB_LT, SUBSET, SUBSET_ANTISYM, SUBSET_REFL, SUBSET_TRANS, .. } :=
        D.cvx.core5
  let { real_ge, real_gt, UNIONS_GSPEC, UNIONS_UNION, UNWIND_THM2, .. } := D.cvx.core6
  let { HULL_INC, HULL_MINIMAL, HULL_MONO, HULL_SUBSET, .. } := D.cvx.misc
  let { DIM_EQ_SPAN, DIST_0, DOT_LNEG, DOT_LZERO, DOT_RADD, DOT_RMUL, DOT_RZERO, .. } :=
        D.cvx.vec1
  let { NORM_MUL, SPAN_INC, SPAN_INDUCT, .. } := D.cvx.vec3
  let { subspace, VECTOR_NEG_EQ_0, .. } := D.cvx.vec4
  let { CLOSED_IN_DIFF, OPEN_IN_INTER, OPEN_IN_SUBTOPOLOGY_INTER_SUBSET, .. } := D.cvx.met
  let { CLOSED_CLOSURE, CLOSED_EMPTY, CLOSED_HYPERPLANE, CLOSED_IN_CLOSED_TRANS,
        CLOSED_SING, CLOSURE_EMPTY, .. } := D.cvx.top1
  let { CLOSURE_MINIMAL, CLOSURE_SUBSET, COMPACT_IMP_CLOSED, COMPACT_INTER_CLOSED,
        CONTINUOUS_ATTAINS_INF, .. } := D.cvx.top2
  let { CONTINUOUS_ON_LIFT_DOT, DISTANCE_ATTAINS_SUP, .. } := D.cvx.top3
  let { OPEN_IN_REFL, OPEN_SEGMENT_ALT, SEGMENT_REFL, .. } := D.cvx.top5
  let { INT_LT_REFL, REAL_LET_ADD2, REAL_LTE_ADD2, SING_GSPEC, UNIONS_1, .. } := D.qses
  let { HYPERPLANE_EQ_EMPTY, NORM_TRIANGLE_LT, .. } := D.qvec
  let { OPEN_IN_UNIONS, .. } := D.qmet
  let { CLOSED_IN_REFL, COMPACT_TRANSLATION_EQ, .. } := D.qtop
  let { AFF_DIM_EQ_0, AFF_DIM_EQ_AFFINE_HULL, AFF_DIM_EQ_MINUS1, AFF_DIM_GE,
        AFF_DIM_HALFSPACE_GE, AFF_DIM_HALFSPACE_LE, AFF_DIM_HYPERPLANE, AFF_DIM_INSERT,
        AFF_DIM_UNIV, AFFINE_HULL_CONIC_HULL, CLOSED_RELATIVE_FRONTIER,
        CLOSURE_SUBSET_AFFINE_HULL, .. } := D.qcvx1
  let { CONVEX_CLOSURE, CONVEX_CONVEX_HULL, CONVEX_HULL_EMPTY, CONVEX_HULL_TRANSLATION,
        CONVEX_HYPERPLANE, CONVEX_INTER, .. } := D.qcvx2
  let { CONVEX_RELATIVE_INTERIOR_CLOSURE, CONVEX_TRANSLATION_EQ,
        DIFFERENT_NORM_3_COLLINEAR_POINTS, INTER_RELATIVE_FRONTIER_CONIC_HULL,
        OPEN_IN_RELATIVE_INTERIOR, relative_frontier, RELATIVE_INTERIOR_EMPTY,
        RELATIVE_INTERIOR_EQ_EMPTY, RELATIVE_INTERIOR_SING, RELATIVE_INTERIOR_SUBSET,
        SEPARATING_HYPERPLANE_CLOSED_POINT, SUPPORTING_HYPERPLANE_RELATIVE_BOUNDARY, .. } :=
        D.qcvx3
  let { AFFINE_HULL_FACE_OF_DISJOINT_RELATIVE_INTERIOR, face_of, FACE_OF_AFF_DIM_LT,
        FACE_OF_EMPTY, FACE_OF_EQ, FACE_OF_IMP_SUBSET,
        FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE, FACE_OF_REFL, FACE_OF_SUBSET,
        FACE_OF_SUBSET_RELATIVE_BOUNDARY, FACE_OF_SUBSET_RELATIVE_FRONTIER, FACE_OF_TRANS,
        SUBSET_OF_FACE_OF, .. } := BPOA
  let { FACE_OF_HALFSPACE_LE, HYPERPLANE_FACE_OF_HALFSPACE_GE,
        HYPERPLANE_FACE_OF_HALFSPACE_LE, RELATIVE_FRONTIER_FACIAL_PARTITION, .. } := BPOC
  let { exposed_face_of, EXPOSED_FACE_OF_IMP_FACE_OF,
        RELATIVE_BOUNDARY_POINT_IN_EXPOSED_FACE, .. } := BPOD
  let { extreme_point_of, EXTREME_POINT_OF_EMPTY, EXTREME_POINT_OF_SING,
        EXTREME_POINTS_OF_CONVEX_HULL, EXTREME_POINTS_OF_TRANSLATION, FACE_OF_SING, .. } :=
        BPOE
  let { CONIC_HULL_RELATIVE_INTERIOR, .. } := BPOF
  -- @@SCOPE END
  parse_as_infix ("facet_of", (12, "right"))

  let facet_of ← new_definition
   r"f facet_of s <=> f face_of s /\ ~(f = {}) /\ aff_dim f = aff_dim s - &1"

  let FACET_OF_EMPTY ← prove
   r"!s. ~(s facet_of {})"
   (REWRITE_TAC [facet_of, FACE_OF_EMPTY] THEN CONV_TAC (fun t => TAUT t))

  let FACET_OF_REFL ← prove
   r"!s. ~(s facet_of s)"
   (REWRITE_TAC [facet_of, ← INT_ARITH (← q r"~(x:int = x - &1)")])

  let FACET_OF_IMP_FACE_OF ← prove
   r"!f s. f facet_of s ==> f face_of s"
   (SIMP_TAC [facet_of])

  let FACET_OF_IMP_SUBSET ← prove
   r"!f s. f facet_of s ==> f SUBSET s"
   (SIMP_TAC [FACET_OF_IMP_FACE_OF, FACE_OF_IMP_SUBSET])

  let FACET_OF_IMP_PROPER ← prove
   r"!f s. f facet_of s ==> ~(f = {}) /\ ~(f = s)"
   (REWRITE_TAC [facet_of] THEN MESON_TAC [← INT_ARITH (← q r"~(x - &1:int = x)")])

  let FACET_OF_TRANSLATION_EQ ← prove
   r"!a:real^N f s.
        (IMAGE (\x. a + x) f) facet_of (IMAGE (\x. a + x) s) <=> f facet_of s"
   (REWRITE_TAC [facet_of] THEN GEOM_TRANSLATE_TAC [])

  add_translation_invariants [FACET_OF_TRANSLATION_EQ]

  let FACET_OF_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N c s.
      linear f /\ (!x y. f x = f y ==> x = y)
      ==> ((IMAGE f c) facet_of (IMAGE f s) <=> c facet_of s)"
   (REWRITE_TAC [facet_of] THEN GEOM_TRANSFORM_TAC [])

  add_linear_invariants [FACET_OF_LINEAR_IMAGE]

  let HYPERPLANE_FACET_OF_HALFSPACE_LE ← prove
   r"!a:real^N b.
        ~(a = vec 0) ==> {x | a dot x = b} facet_of {x | a dot x <= b}"
   (SIMP_TAC [facet_of, HYPERPLANE_FACE_OF_HALFSPACE_LE, HYPERPLANE_EQ_EMPTY,
              AFF_DIM_HYPERPLANE, AFF_DIM_HALFSPACE_LE])

  let HYPERPLANE_FACET_OF_HALFSPACE_GE ← prove
   r"!a:real^N b.
        ~(a = vec 0) ==> {x | a dot x = b} facet_of {x | a dot x >= b}"
   (SIMP_TAC [facet_of, HYPERPLANE_FACE_OF_HALFSPACE_GE, HYPERPLANE_EQ_EMPTY,
              AFF_DIM_HYPERPLANE, AFF_DIM_HALFSPACE_GE])

  let FACET_OF_HALFSPACE_LE ← prove
   r"!f a:real^N b.
        f facet_of {x | a dot x <= b} <=>
        ~(a = vec 0) /\ f = {x | a dot x = b}"
   (REPEAT GEN_TAC THEN
    EQ_TAC THEN ASM_SIMP_TAC [HYPERPLANE_FACET_OF_HALFSPACE_LE] THEN
    SIMP_TAC [AFF_DIM_HALFSPACE_LE, facet_of, FACE_OF_HALFSPACE_LE] THEN
    REWRITE_TAC [← TAUT (← q r"(p \/ q) /\ ~p /\ r <=> (~p /\ q) /\ r")] THEN
    ASM_CASES_TAC (← q r"a:real^N = vec 0") THENL
     [ASM_REWRITE_TAC [DOT_LZERO, ← SET_RULE
       (← q r"{x | p} = if p then UNIV else {}")] THEN
      REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [← TAUT (← q r"~(~p /\ p)")]) THEN
      TRY ASM_REAL_ARITH_TAC THEN
      DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC [AFF_DIM_UNIV] THEN TRY INT_ARITH_TAC THEN ASM SET_TAC [],
      DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC [AFF_DIM_HALFSPACE_LE] THEN INT_ARITH_TAC])

  let FACET_OF_HALFSPACE_GE ← prove
   r"!f a:real^N b.
        f facet_of {x | a dot x >= b} <=>
        ~(a = vec 0) /\ f = {x | a dot x = b}"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^N->bool", ← q r"--a:real^N", ← q r"--b:real"]
          FACET_OF_HALFSPACE_LE) THEN
    SIMP_TAC [DOT_LNEG, REAL_LE_NEG2, REAL_EQ_NEG2, VECTOR_NEG_EQ_0, real_ge])

  let EXPOSED_FACET_OF ← prove
   r"!s t:real^N->bool. convex s /\ t facet_of s ==> t exposed_face_of s"
   (REWRITE_TAC [facet_of] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"~(relative_interior t:real^N->bool = {})") MP_TAC THENL
     [ASM_MESON_TAC [RELATIVE_INTERIOR_EQ_EMPTY, face_of],
      REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC (← q r"a:real^N") THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"a:real^N"]
          RELATIVE_BOUNDARY_POINT_IN_EXPOSED_FACE) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"t:real^N->bool"]
          FACE_OF_SUBSET_RELATIVE_BOUNDARY) THEN
      ASM_REWRITE_TAC [SUBSET, IN_DIFF] THEN
      ASM_MESON_TAC [SUBSET, face_of, RELATIVE_INTERIOR_SUBSET,
                     ← INT_ARITH (← q r"~(t:int = t - &1)")],
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:real^N->bool") STRIP_ASSUME_TAC)] THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"f:real^N->bool", ← q r"t:real^N->bool"]
          SUBSET_OF_FACE_OF) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [EXPOSED_FACE_OF_IMP_FACE_OF, FACE_OF_IMP_SUBSET] THEN
      ASM SET_TAC [],
      DISCH_TAC] THEN
    ASM_CASES_TAC (← q r"t:real^N->bool = f") THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP (← INT_ARITH
     (← q r"t:int = s - &1 ==> !f. t < f /\ f < s ==> F"))) THEN
    MATCH_MP_TAC (← TAUT (← q r"~p ==> p ==> q")) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"aff_dim(f:real^N->bool)")) THEN
    REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
    ASM_SIMP_TAC [EXPOSED_FACE_OF_IMP_FACE_OF] THEN
    CONJ_TAC THENL [ASM_MESON_TAC [exposed_face_of, face_of], ALL_TAC] THEN
    MATCH_MP_TAC FACE_OF_SUBSET THEN EXISTS_TAC (← q r"s:real^N->bool") THEN
    ASM_MESON_TAC [exposed_face_of, face_of])

  let OPEN_IN_RELATIVE_FRONTIER_INTERIOR_FACET ← prove
   r"!s f:real^N->bool.
        convex s /\ f facet_of s
        ==> open_in (subtopology euclidean (relative_frontier s))
                    (relative_interior f)"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"relative_interior s:real^N->bool = {}") THENL
     [ASM_MESON_TAC [RELATIVE_INTERIOR_EQ_EMPTY, FACET_OF_EMPTY],
      POP_ASSUM MP_TAC] THEN
    REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"z:real^N") THEN GEOM_ORIGIN_TAC (← q r"z:real^N") THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"relative_interior f:real^N->bool"]
          INTER_RELATIVE_FRONTIER_CONIC_HULL) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [ASM_MESON_TAC [FACE_OF_SUBSET_RELATIVE_FRONTIER, FACET_OF_REFL, facet_of,
                     SUBSET_TRANS, RELATIVE_INTERIOR_SUBSET],
      DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN
     (← q r"~(vec 0 IN affine hull (f:real^N->bool))")
    ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"f:real^N->bool"]
          AFFINE_HULL_FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [facet_of, FACET_OF_REFL], ASM SET_TAC []],
      ASM_SIMP_TAC [CONIC_HULL_RELATIVE_INTERIOR]] THEN
    COND_CASES_TAC THENL
     [ASM_MESON_TAC [RELATIVE_INTERIOR_EQ_EMPTY, facet_of, face_of], ALL_TAC] THEN
    ASM_SIMP_TAC [relative_frontier, ← SET_RULE
      (← q r"z IN i ==> (c DIFF i) INTER (z INSERT s) = (c DIFF i) INTER s")] THEN
    REWRITE_TAC [← GSYM relative_frontier] THEN
    MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_SUBSET THEN
    EXISTS_TAC (← q r"affine hull s:real^N->bool") THEN
    SIMP_TAC [CLOSURE_SUBSET_AFFINE_HULL, relative_frontier,
              ← SET_RULE (← q r"s SUBSET t ==> s DIFF u SUBSET t")] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN REWRITE_TAC [OPEN_IN_REFL] THEN
    MP_TAC (← ISPEC (← q r"conic hull f:real^N->bool") OPEN_IN_RELATIVE_INTERIOR) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [AFFINE_HULL_CONIC_HULL] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC [facet_of], ALL_TAC] THEN
    MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN
    RULE_ASSUM_TAC (REWRITE_RULE [facet_of]) THEN
    ASM_REWRITE_TAC [INSERT_SUBSET, AFF_DIM_INSERT] THEN
    CONJ_TAC THENL [ALL_TAC, INT_ARITH_TAC] THEN
    ASM_MESON_TAC [face_of, SUBSET, RELATIVE_INTERIOR_SUBSET, SUBSET])

  /- ----------------------------------------------------------------------- -/
  /- Extreme points of convex closed set with aff_dim <= 2 are closed.       -/
  /- ----------------------------------------------------------------------- -/

  let CLOSED_EXTREME_POINTS_2D ← prove
   r"!s:real^N->bool.
        closed s /\ convex s /\ aff_dim s <= &2
        ==> closed {x | x extreme_point_of s}"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP (← INT_ARITH
     (← q r"a:int <= &2
      ==> -- &1 <= a ==> a = -- &1 \/ a = &0 \/ &1 <= a"))) THEN
    REWRITE_TAC [AFF_DIM_GE, AFF_DIM_EQ_MINUS1, AFF_DIM_EQ_0] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THENL
     [ASM_REWRITE_TAC [EXTREME_POINT_OF_EMPTY, EMPTY_GSPEC, CLOSED_EMPTY],
      ASM_REWRITE_TAC [EXTREME_POINT_OF_SING, SING_GSPEC, CLOSED_SING],
      MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
      EXISTS_TAC (← q r"relative_frontier s:real^N->bool") THEN
      REWRITE_TAC [CLOSED_RELATIVE_FRONTIER]] THEN
    SUBGOAL_THEN
     (← q r"{x:real^N | x extreme_point_of s} =
      relative_frontier s DIFF
      UNIONS {relative_interior f | f face_of s /\ aff_dim f = &1}")
    SUBST1_TAC THENL
     [ASM_SIMP_TAC [← GSYM RELATIVE_FRONTIER_FACIAL_PARTITION] THEN
      ASM_SIMP_TAC [AFF_DIM_GE, ← INT_ARITH
       (← q r"-- &1:int <= f /\ &1 <= s /\ s <= &2
        ==> (f < s <=> f = -- &1 /\ &0 <= s \/
                       f = &0 \/
                       f = &1 /\ s = &2)")] THEN
      REWRITE_TAC [UNIONS_UNION, LEFT_OR_DISTRIB,
        ← SET_RULE (← q r"{f x | P x \/ Q x} = {f x | P x} UNION {f x | Q x}")] THEN
      MATCH_MP_TAC (← SET_RULE
       (← q r"f1 SUBSET f /\ DISJOINT f f0 /\ fn = {} /\ f0 = e
        ==>  e = (fn UNION f0 UNION f1) DIFF f")) THEN
      REPEAT CONJ_TAC THENL
       [SET_TAC [],
        REWRITE_TAC [DISJOINT, INTER_UNIONS, EMPTY_UNIONS, FORALL_IN_GSPEC] THEN
        REWRITE_TAC [← GSYM DISJOINT] THEN
        MESON_TAC [FACE_OF_EQ, ← INT_ARITH (← q r"~(&1:int = &0)")],
        SIMP_TAC [EMPTY_UNIONS, FORALL_IN_GSPEC, AFF_DIM_EQ_MINUS1,
                  RELATIVE_INTERIOR_EMPTY],
        REWRITE_TAC [AFF_DIM_EQ_0, ← SET_RULE
         (← q r"{f x | P x /\ (?a. x = s a)} = {f (s a) |a| P (s a)}")] THEN
        REWRITE_TAC [RELATIVE_INTERIOR_SING, FACE_OF_SING, UNIONS_GSPEC] THEN
        SET_TAC []],
       FIRST_ASSUM (MP_TAC o MATCH_MP (← INT_ARITH
        (← q r"&1:int <= a ==> a <= &2 ==> a = &1 \/ a = &2"))) THEN
       ASM_REWRITE_TAC [] THEN STRIP_TAC THENL
        [SUBGOAL_THEN
          (← q r"!f:real^N->bool. f face_of s /\ aff_dim f = &1 <=> f = s")
          (fun th => REWRITE_TAC [th])
         THENL
          [ASM_MESON_TAC [FACE_OF_AFF_DIM_LT, INT_LT_REFL, FACE_OF_REFL],
           REWRITE_TAC [← SET_RULE (← q r"{f x | x = a} = {f a}"), UNIONS_1] THEN
           REWRITE_TAC [relative_frontier, CLOSED_IN_REFL,
              ← SET_RULE (← q r"(s DIFF i) DIFF i = s DIFF i")]],
         FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC
          [← MATCH_MP (← INT_ARITH
             (← q r"s:int = &2 ==> (f = &1 <=> ~(f = -- &1) /\ f = s - &1)")) th])) THEN
         REWRITE_TAC [AFF_DIM_EQ_MINUS1, ← GSYM facet_of] THEN
         MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC [CLOSED_IN_REFL] THEN
         MATCH_MP_TAC OPEN_IN_UNIONS THEN
         ASM_SIMP_TAC [FORALL_IN_GSPEC,
                       OPEN_IN_RELATIVE_FRONTIER_INTERIOR_FACET]]])

  /- ----------------------------------------------------------------------- -/
  /- Edges, i.e. faces of affine dimension 1.                                -/
  /- ----------------------------------------------------------------------- -/

  parse_as_infix ("edge_of", (12, "right"))

  let edge_of ← new_definition
   r"e edge_of s <=> e face_of s /\ aff_dim e = &1"

  let EDGE_OF_TRANSLATION_EQ ← prove
   r"!a:real^N f s.
        (IMAGE (\x. a + x) f) edge_of (IMAGE (\x. a + x) s) <=> f edge_of s"
   (REWRITE_TAC [edge_of] THEN GEOM_TRANSLATE_TAC [])

  add_translation_invariants [EDGE_OF_TRANSLATION_EQ]

  let EDGE_OF_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N c s.
      linear f /\ (!x y. f x = f y ==> x = y)
      ==> ((IMAGE f c) edge_of (IMAGE f s) <=> c edge_of s)"
   (REWRITE_TAC [edge_of] THEN GEOM_TRANSFORM_TAC [])

  add_linear_invariants [EDGE_OF_LINEAR_IMAGE]

  let EDGE_OF_IMP_SUBSET ← prove
   r"!s t. s edge_of t ==> s SUBSET t"
   (SIMP_TAC [edge_of, face_of])

  /- ----------------------------------------------------------------------- -/
  /- Existence of extreme points.                                            -/
  /- ----------------------------------------------------------------------- -/

  let EXTREME_POINT_EXISTS_CONVEX ← prove
   r"!s:real^N->bool.
        compact s /\ convex s /\ ~(s = {}) ==> ?x. x extreme_point_of s"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"vec 0:real^N"] DISTANCE_ATTAINS_SUP) THEN
    ASM_REWRITE_TAC [DIST_0, extreme_point_of] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"x:real^N") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"b:real^N"] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"a:real^N", ← q r"b:real^N", ← q r"x:real^N"]
       DIFFERENT_NORM_3_COLLINEAR_POINTS) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"a <= x /\ b <= x /\ (a < x ==> x < x) /\ (b < x ==> x < x)
      ==> a = b /\ x = b")) THEN
    ASM_SIMP_TAC [] THEN
    UNDISCH_TAC (← q r"(x:real^N) IN segment(a,b)") THEN
    ASM_CASES_TAC (← q r"a:real^N = b") THEN
    ASM_REWRITE_TAC [SEGMENT_REFL, NOT_IN_EMPTY] THEN
    ASM_SIMP_TAC [OPEN_SEGMENT_ALT, IN_ELIM_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:real") STRIP_ASSUME_TAC) THEN
    CONJ_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM (fun th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    MATCH_MP_TAC NORM_TRIANGLE_LT THEN REWRITE_TAC [NORM_MUL] THEN
    ASM_SIMP_TAC [← REAL_ARITH
     (← q r"&0 < u /\ u < &1 ==> abs u = u /\ abs(&1 - u) = &1 - u")] THEN
    SUBST1_TAC (← REAL_RING (← q r"norm(x:real^N) = (&1 - u) * norm x + u * norm x")) THENL
     [MATCH_MP_TAC REAL_LTE_ADD2, MATCH_MP_TAC REAL_LET_ADD2] THEN
    ASM_SIMP_TAC [REAL_LE_LMUL_EQ, REAL_LT_LMUL_EQ, REAL_SUB_LT])

  /- ----------------------------------------------------------------------- -/
  /- Krein-Milman, the weaker form as in more general spaces first.          -/
  /- ----------------------------------------------------------------------- -/

  let KREIN_MILMAN ← prove
   r"!s:real^N->bool.
        convex s /\ compact s
        ==> s = closure(convex hull {x | x extreme_point_of s})"
   (GEN_TAC THEN
    ASM_CASES_TAC (← q r"s:real^N->bool = {}") THENL
     [ASM_REWRITE_TAC [extreme_point_of, NOT_IN_EMPTY, EMPTY_GSPEC] THEN
      REWRITE_TAC [CONVEX_HULL_EMPTY, CLOSURE_EMPTY],
      ALL_TAC] THEN
    STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC [COMPACT_IMP_CLOSED] THEN
      MATCH_MP_TAC HULL_MINIMAL THEN
      ASM_SIMP_TAC [SUBSET, IN_ELIM_THM, extreme_point_of]] THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"u:real^N") THEN DISCH_TAC THEN
    MATCH_MP_TAC (← TAUT (← q r"(~p ==> F) ==> p")) THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"closure(convex hull {x:real^N | x extreme_point_of s})",
                      ← q r"u:real^N"] SEPARATING_HYPERPLANE_CLOSED_POINT) THEN
    ASM_SIMP_TAC [CONVEX_CLOSURE, CLOSED_CLOSURE, CONVEX_CONVEX_HULL] THEN
    REWRITE_TAC [NOT_EXISTS_THM, ← TAUT (← q r"~(a /\ b) <=> a ==> ~b")] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"b:real"] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"\x:real^N. a dot x", ← q r"s:real^N->bool"]
      CONTINUOUS_ATTAINS_INF) THEN
    ASM_REWRITE_TAC [CONTINUOUS_ON_LIFT_DOT] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"m:real^N") STRIP_ASSUME_TAC) THEN
    ABBREV_TAC (← q r"t = {x:real^N | x IN s /\ a dot x = a dot m}") THEN
    SUBGOAL_THEN (← q r"?x:real^N. x extreme_point_of t") (X_CHOOSE_TAC (← q r"v:real^N"))
    THENL
     [MATCH_MP_TAC EXTREME_POINT_EXISTS_CONVEX THEN
      EXPAND_TAC "t" THEN REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM] THEN
      REWRITE_TAC [← SET_RULE (← q r"{x | x IN s /\ P x} = s INTER {x | P x}")] THEN
      ASM_SIMP_TAC [CONVEX_INTER, CONVEX_HYPERPLANE, COMPACT_INTER_CLOSED,
                    CLOSED_HYPERPLANE] THEN
      ASM SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(v:real^N) extreme_point_of s") ASSUME_TAC THENL
     [REWRITE_TAC [← GSYM FACE_OF_SING] THEN MATCH_MP_TAC FACE_OF_TRANS THEN
      EXISTS_TAC (← q r"t:real^N->bool") THEN ASM_SIMP_TAC [FACE_OF_SING] THEN
      EXPAND_TAC "t" THEN
      REWRITE_TAC [← SET_RULE (← q r"{x | x IN s /\ P x} = s INTER {x | P x}")] THEN
      MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE THEN
      ASM_SIMP_TAC [real_ge],
      SUBGOAL_THEN (← q r"(a:real^N) dot v > b") MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        MATCH_MP_TAC (← REWRITE_RULE [SUBSET] CLOSURE_SUBSET) THEN
        MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC [IN_ELIM_THM],
        ALL_TAC] THEN
      REWRITE_TAC [real_gt, REAL_NOT_LT] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"(a:real^N) dot u") THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"(a:real^N) dot m") THEN
      ASM_SIMP_TAC [] THEN
      UNDISCH_TAC (← q r"(v:real^N) extreme_point_of t") THEN EXPAND_TAC "t" THEN
      SIMP_TAC [extreme_point_of, IN_ELIM_THM, REAL_LE_REFL]])

  /- ----------------------------------------------------------------------- -/
  /- Now the sharper form.                                                   -/
  /- ----------------------------------------------------------------------- -/

  let KREIN_MILMAN_MINKOWSKI ← prove
   r"!s:real^N->bool.
        convex s /\ compact s
        ==> s = convex hull {x | x extreme_point_of s}"
   (SUBGOAL_THEN
     (← q r"!s:real^N->bool.
          convex s /\ compact s /\ (vec 0) IN s
          ==> (vec 0) IN convex hull {x | x extreme_point_of s}")
    ASSUME_TAC THENL
     [GEN_TAC THEN WF_INDUCT_TAC (← q r"dim(s:real^N->bool)") THEN STRIP_TAC THEN
      ASM_CASES_TAC (← q r"(vec 0:real^N) IN relative_interior s") THENL
       [MP_TAC (← ISPEC (← q r"s:real^N->bool") KREIN_MILMAN) THEN
        ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
        UNDISCH_TAC (← q r"(vec 0:real^N) IN relative_interior s") THEN
        FIRST_X_ASSUM (fun th => GEN_REWRITE_TAC
         (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
        SIMP_TAC [CONVEX_RELATIVE_INTERIOR_CLOSURE, CONVEX_CONVEX_HULL] THEN
        MESON_TAC [RELATIVE_INTERIOR_SUBSET, SUBSET],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"~(relative_interior(s:real^N->bool) = {})") ASSUME_TAC THENL
       [ASM_SIMP_TAC [RELATIVE_INTERIOR_EQ_EMPTY] THEN ASM SET_TAC [],
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"vec 0:real^N"]
            SUPPORTING_HYPERPLANE_RELATIVE_BOUNDARY) THEN
      ASM_REWRITE_TAC [DOT_RZERO] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"a:real^N") STRIP_ASSUME_TAC) THEN
      MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"a:real^N", ← q r"&0"]
        FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE) THEN
      ASM_REWRITE_TAC [real_ge] THEN DISCH_TAC THEN
      SUBGOAL_THEN
       (← q r"(vec 0:real^N) IN convex hull
            {x | x extreme_point_of (s INTER {x | a dot x = &0})}")
      MP_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC (← SET_RULE (← q r"s SUBSET t ==> x IN s ==> x IN t")) THEN
        MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC [SUBSET] THEN
        GEN_TAC THEN REWRITE_TAC [IN_ELIM_THM, ← GSYM FACE_OF_SING] THEN
        ASM_MESON_TAC [FACE_OF_TRANS]] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [IMP_IMP]) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC [CONVEX_INTER, CONVEX_HYPERPLANE, COMPACT_INTER_CLOSED,
                    CLOSED_HYPERPLANE, IN_INTER, IN_ELIM_THM, DOT_RZERO] THEN
      REWRITE_TAC [← GSYM NOT_LE] THEN DISCH_TAC THEN
      MP_TAC (← ISPECL
       [← q r"s INTER {x:real^N | a dot x = &0}", ← q r"s:real^N->bool"]
            DIM_EQ_SPAN) THEN
      ASM_REWRITE_TAC [INTER_SUBSET, EXTENSION, NOT_FORALL_THM] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"c:real^N") THEN DISCH_TAC THEN
      MATCH_MP_TAC (← TAUT (← q r"b /\ ~a ==> ~(a <=> b)")) THEN CONJ_TAC THENL
       [ASM_MESON_TAC [SUBSET, SPAN_INC, RELATIVE_INTERIOR_SUBSET], ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!x:real^N. x IN span (s INTER {x | a dot x = &0}) ==> a dot x = &0")
       (fun th => ASM_MESON_TAC [th, REAL_LT_REFL]) THEN
      MATCH_MP_TAC SPAN_INDUCT THEN SIMP_TAC [IN_INTER, IN_ELIM_THM] THEN
      REWRITE_TAC [subspace, DOT_RZERO, DOT_RADD, DOT_RMUL, IN_ELIM_THM] THEN
      CONV_TAC (fun t => REAL_RING t),
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"a:real^N") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"IMAGE (\x:real^N. --a + x) s")) THEN
      ASM_SIMP_TAC [CONVEX_TRANSLATION_EQ, COMPACT_TRANSLATION_EQ] THEN
      REWRITE_TAC [IN_IMAGE, ← VECTOR_ARITH (← q r"vec 0:real^N = --a + x <=> x = a")] THEN
      ASM_REWRITE_TAC [UNWIND_THM2] THEN
      REWRITE_TAC [EXTREME_POINTS_OF_TRANSLATION, CONVEX_HULL_TRANSLATION] THEN
      REWRITE_TAC [IN_IMAGE, ← VECTOR_ARITH (← q r"vec 0:real^N = --a + x <=> x = a")] THEN
      REWRITE_TAC [UNWIND_THM2],
      MATCH_MP_TAC HULL_MINIMAL THEN
      ASM_SIMP_TAC [SUBSET, extreme_point_of, IN_ELIM_THM]])

  let KREIN_MILMAN_EQ ← prove
   r"!s e:real^N->bool.
        compact s /\ convex s
        ==> (convex hull e = s <=>
             e SUBSET s /\ {x | x extreme_point_of s} SUBSET e)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [EXPAND_TAC "s" THEN
      REWRITE_TAC [HULL_SUBSET, EXTREME_POINTS_OF_CONVEX_HULL],
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC [],
        TRANS_TAC SUBSET_TRANS
         (← q r"convex hull {x:real^N | x extreme_point_of s}") THEN
        ASM_SIMP_TAC [HULL_MONO] THEN
        ASM_MESON_TAC [KREIN_MILMAN_MINKOWSKI, SUBSET_REFL]]])

  pure { facet_of, FACET_OF_EMPTY, FACET_OF_REFL, FACET_OF_IMP_FACE_OF, FACET_OF_IMP_SUBSET,
         FACET_OF_IMP_PROPER, FACET_OF_TRANSLATION_EQ, FACET_OF_LINEAR_IMAGE,
         HYPERPLANE_FACET_OF_HALFSPACE_LE, HYPERPLANE_FACET_OF_HALFSPACE_GE,
         FACET_OF_HALFSPACE_LE, FACET_OF_HALFSPACE_GE, EXPOSED_FACET_OF,
         OPEN_IN_RELATIVE_FRONTIER_INTERIOR_FACET, CLOSED_EXTREME_POINTS_2D, edge_of,
         EDGE_OF_TRANSLATION_EQ, EDGE_OF_LINEAR_IMAGE, EDGE_OF_IMP_SUBSET,
         EXTREME_POINT_EXISTS_CONVEX, KREIN_MILMAN, KREIN_MILMAN_MINKOWSKI,
         KREIN_MILMAN_EQ }

/- ------------------------------------------------------------------------- -/
/- Applying it to convex hulls of explicitly indicated finite sets.          -/
/- (polytope.ml 3053-3692)                                                   -/
/- ------------------------------------------------------------------------- -/

structure POH where
  KREIN_MILMAN_POLYTOPE : thm
  EXTREME_POINTS_OF_CONVEX_HULL_EQ : thm
  EXTREME_POINT_OF_CONVEX_HULL_EQ : thm
  EXTREME_POINT_OF_CONVEX_HULL_CONVEX_INDEPENDENT : thm
  EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT : thm
  EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT : thm
  SIMPLEX_VERTICES_UNIQUE : thm
  EXTREME_POINT_OF_CONVEX_HULL_2 : thm
  EXTREME_POINT_OF_SEGMENT : thm
  FACE_OF_CONVEX_HULL_SUBSET : thm
  FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT : thm
  FACET_OF_CONVEX_HULL_AFFINE_INDEPENDENT : thm
  FACET_OF_CONVEX_HULL_AFFINE_INDEPENDENT_ALT : thm
  SEGMENT_FACE_OF : thm
  SEGMENT_EDGE_OF : thm
  EXTREME_POINT_OF_CONVEX_HULL_INSERT_EQ : thm
  FACE_OF_CONVEX_HULL_INSERT_EQ : thm
  CONVEX_HULL_REDUNDANT_SUBSET_GEN : thm
  CONVEX_HULL_REDUNDANT_SUBSET : thm
  CONVEX_HULL_REDUNDANT_SUBSET_REV : thm
  CONVEX_HULL_INSERT_REDUNDANT_POINT : thm
  CONVEX_HULL_REDUNDANT_POINT : thm
  HAUSDIST_FRONTIERS_CONVEX : thm
  deriving Inhabited

set_option maxHeartbeats 8000000 in
@[nospecialize]
def setupPOH [HolBase] (D : PolytopeDeps) (BPOA : POA) (BPOB : POB) (BPOE : POE) (BPOG : POG) : ExceptT String IO POH := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, HAS_SIZE_CONV, INT_ARITH,
        INT_ARITH_TAC, MESON_TAC, NORM_ARITH, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD,
        REAL_RING, SET_RULE, SET_TAC, VECTOR_ARITH, .. } := D.cvx
  let { CARD_CLAUSES, CARD_DELETE, CARD_DIFF, CARD_EQ_0, CONJ_ASSOC, CONTRAPOS_THM,
        DISJ_SYM, EMPTY_SUBSET, EXTENSION, FINITE_DELETE, FINITE_DIFF, FINITE_INSERT,
        FINITE_SUBSET, FORALL_IN_GSPEC, .. } := D.cvx.core1
  let { FORALL_UNWIND_THM2, FUN_EQ_THM, HAS_SIZE, IMP_CONJ, IMP_CONJ_ALT, IMP_IMP,
        IN_DELETE, IN_DIFF, INSERT_SUBSET, INT_OF_NUM_ADD, INT_OF_NUM_EQ, INTER_SUBSET, .. }
        := D.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, IN_INTER, IN_SING, LEFT_EXISTS_AND_THM, LEFT_IMP_EXISTS_THM,
        MONO_EXISTS, NOT_INSERT_EMPTY, .. } := D.cvx.core3
  let { REAL_ENTIRE, REAL_LE_ANTISYM, REAL_LE_LDIV_EQ, REAL_LE_LMUL_EQ, REAL_LE_MUL,
        REAL_LE_RDIV_EQ, REAL_LE_REFL, REAL_LE_TRANS, REAL_LT_IMP_LE, REAL_LT_IMP_NE,
        REAL_LT_IMP_NZ, REAL_LT_LDIV_EQ, REAL_LT_MUL, REAL_LT_RDIV_EQ, REAL_LTE_TRANS, .. }
        := D.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_MUL_SYM,
        REAL_SUB_0, REAL_SUB_LE, REAL_SUB_LT, RIGHT_AND_EXISTS_THM, RIGHT_EXISTS_AND_THM,
        RIGHT_FORALL_IMP_THM, SUBSET, SUBSET_ANTISYM, SUBSET_ANTISYM_EQ, SUBSET_TRANS, .. }
        := D.cvx.core5
  let { real_abs, real_div, .. } := D.cvx.core6
  let { HULL_INC, HULL_MINIMAL, HULL_MONO, HULL_SUBSET, .. } := D.cvx.misc
  let { DIST_SYM, DOT_RADD, DOT_RMUL, DOT_RNEG, DOT_RSUB, .. } := D.cvx.vec1
  let { NORM_CAUCHY_SCHWARZ, .. } := D.cvx.vec2
  let { NORM_MUL, NORM_NEG, NORM_POS_LT, NORM_POW_2, .. } := D.cvx.vec3
  let { dist, VECTOR_ADD_ASSOC, VECTOR_ADD_LDISTRIB, VECTOR_ADD_LID, VECTOR_ADD_RDISTRIB,
        VECTOR_ADD_RID, VECTOR_MUL_ASSOC, VECTOR_MUL_LCANCEL, VECTOR_MUL_LID,
        VECTOR_MUL_LNEG, VECTOR_MUL_LZERO, VECTOR_NEG_EQ_0, VECTOR_SUB_EQ, .. } :=
        D.cvx.vec4
  let { BOUNDED_FRONTIER, CLOSURE_CLOSED, .. } := D.cvx.top1
  let { CLOSURE_EQ_EMPTY, CLOSURE_SUBSET, COMPACT_CLOSURE, COMPACT_EQ_BOUNDED_CLOSED,
        COMPACT_IMP_CLOSED, COMPACT_INSERT, .. } := D.cvx.top2
  let { ENDS_NOT_IN_SEGMENT, FINITE_IMP_COMPACT, FRONTIER_CLOSED, FRONTIER_EMPTY,
        FRONTIER_EQ_EMPTY, HAUSDIST_CLOSURE, HAUSDIST_EMPTY, HAUSDIST_SYM, .. } :=
        D.cvx.top3
  let { IN_SEGMENT, NOT_BOUNDED_UNIV, .. } := D.cvx.top4
  let { frontier, REAL_HAUSDIST_LE, REAL_LE_HAUSDIST, SEGMENT_REFL, SETDIST_LE_DIST,
        SETDIST_POS_LE, SETDIST_SUBSET_RIGHT, .. } := D.cvx.top5
  let { DELETE_SUBSET, PSUBSET_ALT, REAL_EQ_MUL_LCANCEL, .. } := D.qses
  let { HULL_UNION_RIGHT, .. } := D.qmisc
  let { REAL_HAUSDIST_LE_EQ, REAL_LE_SETDIST, SETDIST_SING_FRONTIER, SETDIST_SING_IN_SET, ..
        } := D.qtop
  let { AFF_DIM_AFFINE_INDEPENDENT, AFF_DIM_CONVEX_HULL, AFF_DIM_SING, AFFINE_AFFINE_HULL,
        AFFINE_HULL_3, AFFINE_HULL_CONVEX_HULL, AFFINE_HULL_SING, AFFINE_INDEPENDENT_2,
        AFFINE_INDEPENDENT_IMP_FINITE, AFFINE_INDEPENDENT_SUBSET, .. } := D.qcvx1
  let { COMPACT_CONVEX_HULL, CONVEX_CLOSURE, CONVEX_CONVEX_HULL, CONVEX_HULL_EMPTY,
        CONVEX_HULL_EQ, CONVEX_HULL_EQ_EMPTY, CONVEX_HULL_INSERT_ALT, CONVEX_HULL_SING,
        CONVEX_HULL_SUBSET_AFFINE_HULL, .. } := D.qcvx2
  let { affine_dependent, DISJOINT_AFFINE_HULL, FRONTIER_CLOSURE_CONVEX,
        HAUSDIST_CONVEX_HULLS, IN_CONVEX_SET, KREIN_MILMAN_FRONTIER, RAY_TO_FRONTIER,
        SEGMENT_CONVEX_HULL, SUPPORTING_HYPERPLANE_FRONTIER, .. } := D.qcvx3
  let { face_of, FACE_OF_EMPTY, FACE_OF_IMP_COMPACT, FACE_OF_IMP_CONVEX, FACE_OF_IMP_SUBSET,
        FACE_OF_INTER, FACE_OF_REFL_EQ, FACE_OF_SUBSET, FACE_OF_TRANS, .. } := BPOA
  let { FACE_OF_CONVEX_HULL_INSERT, FACE_OF_CONVEX_HULLS, .. } := BPOB
  let { EXTREME_POINT_NOT_IN_INTERIOR, extreme_point_of, EXTREME_POINT_OF_CONVEX_HULL,
        EXTREME_POINT_OF_CONVEX_HULL_INSERT, EXTREME_POINTS_OF_CONVEX_HULL, FACE_OF_SING, ..
        } := BPOE
  let { edge_of, facet_of, KREIN_MILMAN_MINKOWSKI, .. } := BPOG
  -- @@SCOPE END

  let KREIN_MILMAN_POLYTOPE ← prove
   r"!s. FINITE s
       ==> convex hull s =
           convex hull {x | x extreme_point_of (convex hull s)}"
   (SIMP_TAC [KREIN_MILMAN_MINKOWSKI, CONVEX_CONVEX_HULL,
              COMPACT_CONVEX_HULL, FINITE_IMP_COMPACT])

  let EXTREME_POINTS_OF_CONVEX_HULL_EQ ← prove
   r"!s:real^N->bool.
        compact s /\
        (!t. t PSUBSET s ==> ~(convex hull t = convex hull s))
        ==> {x | x extreme_point_of (convex hull s)} = s"
   (REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC
     (← q r"{x:real^N | x extreme_point_of (convex hull s)}")) THEN
    MATCH_MP_TAC (← SET_RULE
     (← q r"P /\ t SUBSET s ==> (t PSUBSET s ==> ~P) ==> t = s")) THEN
    REWRITE_TAC [EXTREME_POINTS_OF_CONVEX_HULL] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
    ASM_SIMP_TAC [CONVEX_CONVEX_HULL, COMPACT_CONVEX_HULL])

  let EXTREME_POINT_OF_CONVEX_HULL_EQ ← prove
   r"!s x:real^N.
        compact s /\
        (!t. t PSUBSET s ==> ~(convex hull t = convex hull s))
        ==> (x extreme_point_of (convex hull s) <=> x IN s)"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP EXTREME_POINTS_OF_CONVEX_HULL_EQ) THEN
    SET_TAC [])

  let EXTREME_POINT_OF_CONVEX_HULL_CONVEX_INDEPENDENT ← prove
   r"!s x:real^N.
        compact s /\
        (!a. a IN s ==> ~(a IN convex hull (s DELETE a)))
        ==> (x extreme_point_of (convex hull s) <=> x IN s)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC EXTREME_POINT_OF_CONVEX_HULL_EQ THEN
    ASM_REWRITE_TAC [PSUBSET_ALT] THEN X_GEN_TAC (← q r"t:real^N->bool") THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC (← q r"a:real^N"))) THEN
    DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"a:real^N")) THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"s SUBSET convex hull (s DELETE (a:real^N))") MP_TAC THENL
     [ALL_TAC, ASM SET_TAC []] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC (← q r"convex hull t:real^N->bool") THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC [HULL_SUBSET],
      MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC []])

  let EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT ← prove
   r"!s x. ~affine_dependent s
         ==> (x extreme_point_of (convex hull s) <=> x IN s)"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC EXTREME_POINT_OF_CONVEX_HULL_CONVEX_INDEPENDENT THEN
    ASM_SIMP_TAC [AFFINE_INDEPENDENT_IMP_FINITE, FINITE_IMP_COMPACT] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [affine_dependent]) THEN
    MESON_TAC [SUBSET, CONVEX_HULL_SUBSET_AFFINE_HULL])

  let EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT ← prove
   r"!s:real^N->bool.
        ~affine_dependent s ==> {x | x extreme_point_of convex hull s} = s"
   (SIMP_TAC [EXTENSION, IN_ELIM_THM,
              EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT])

  let SIMPLEX_VERTICES_UNIQUE ← prove
   r"!s t:real^N->bool.
        ~affine_dependent s /\ ~affine_dependent t /\
        convex hull s = convex hull t
        ==> s = t"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [EXTENSION] THEN
    ASM_MESON_TAC [EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT])

  let EXTREME_POINT_OF_CONVEX_HULL_2 ← prove
   r"!a b x. x extreme_point_of (convex hull {a,b}) <=> x = a \/ x = b"
   (REWRITE_TAC [← SET_RULE (← q r"x = a \/ x = b <=> x IN {a,b}")] THEN
    SIMP_TAC [EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT,
              AFFINE_INDEPENDENT_2])

  let EXTREME_POINT_OF_SEGMENT ← prove
   r"!a b x:real^N. x extreme_point_of segment[a,b] <=> x = a \/ x = b"
   (REWRITE_TAC [SEGMENT_CONVEX_HULL, EXTREME_POINT_OF_CONVEX_HULL_2])

  let FACE_OF_CONVEX_HULL_SUBSET ← prove
   r"!s t:real^N->bool.
        compact s /\ t face_of (convex hull s)
        ==> ?s'. s' SUBSET s /\ t = convex hull s'"
   (REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"{x:real^N | x extreme_point_of t}") THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      MATCH_MP_TAC EXTREME_POINT_OF_CONVEX_HULL THEN
      ASM_MESON_TAC [FACE_OF_SING, FACE_OF_TRANS],
      MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
      ASM_MESON_TAC [FACE_OF_IMP_CONVEX, FACE_OF_IMP_COMPACT,
                     COMPACT_CONVEX_HULL, CONVEX_CONVEX_HULL]])

  let FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT ← prove
   r"!s t:real^N->bool.
        ~affine_dependent s
        ==> (t face_of (convex hull s) <=>
             ?c. c SUBSET s /\ t = convex hull c)"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ASM_MESON_TAC [AFFINE_INDEPENDENT_IMP_FINITE, FINITE_IMP_COMPACT,
                     FACE_OF_CONVEX_HULL_SUBSET],
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC FACE_OF_CONVEX_HULLS THEN
      ASM_SIMP_TAC [AFFINE_INDEPENDENT_IMP_FINITE] THEN
      MATCH_MP_TAC (← SET_RULE (← q r"
       !t. u SUBSET t /\ DISJOINT s t ==> DISJOINT s u")) THEN
      EXISTS_TAC (← q r"affine hull (s DIFF c:real^N->bool)") THEN
      REWRITE_TAC [CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
      MATCH_MP_TAC DISJOINT_AFFINE_HULL THEN
      EXISTS_TAC (← q r"s:real^N->bool") THEN ASM SET_TAC []])

  let FACET_OF_CONVEX_HULL_AFFINE_INDEPENDENT ← prove
   r"!s t:real^N->bool.
        ~affine_dependent s
        ==> (t facet_of (convex hull s) <=>
             ~(t = {}) /\ ?u. u IN s /\ t = convex hull (s DELETE u))"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [facet_of, FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC [AFF_DIM_CONVEX_HULL] THEN EQ_TAC THENL
     [DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"c:real^N->bool") MP_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
      UNDISCH_TAC
       (← q r"aff_dim(convex hull c:real^N->bool) = aff_dim(s:real^N->bool) - &1") THEN
      SUBGOAL_THEN (← q r"~affine_dependent(c:real^N->bool)") ASSUME_TAC THENL
       [ASM_MESON_TAC [AFFINE_INDEPENDENT_SUBSET],
        ASM_SIMP_TAC [AFF_DIM_AFFINE_INDEPENDENT, AFF_DIM_CONVEX_HULL]] THEN
      REWRITE_TAC [← INT_ARITH (← q r"x - &1:int = y - &1 - &1 <=> y = x + &1")] THEN
      REWRITE_TAC [INT_OF_NUM_ADD, INT_OF_NUM_EQ] THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"(s DIFF c:real^N->bool) HAS_SIZE 1") MP_TAC THENL
       [ASM_SIMP_TAC [HAS_SIZE, FINITE_DIFF, CARD_DIFF,
                      AFFINE_INDEPENDENT_IMP_FINITE] THEN ARITH_TAC,
        CONV_TAC (LAND_CONV HAS_SIZE_CONV) THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"u:real^N") THEN
        DISCH_THEN (MP_TAC o MATCH_MP (← SET_RULE
         (← q r"s DIFF t = {a} ==> t SUBSET s ==> s = a INSERT t"))) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC (← q r"CARD((u:real^N) INSERT c) = CARD c + 1") THEN
        ASM_SIMP_TAC [CARD_CLAUSES, AFFINE_INDEPENDENT_IMP_FINITE] THEN
        COND_CASES_TAC THENL [ARITH_TAC, DISCH_THEN (K ALL_TAC : thm → tactic)] THEN
        CONJ_TAC THENL [ALL_TAC, AP_TERM_TAC] THEN ASM SET_TAC []],
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"u:real^N") MP_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
      CONJ_TAC THENL [MESON_TAC [DELETE_SUBSET], ALL_TAC] THEN
      ASM_SIMP_TAC [AFF_DIM_CONVEX_HULL] THEN
      SUBGOAL_THEN (← q r"~affine_dependent(s DELETE (u:real^N))") ASSUME_TAC THENL
       [ASM_MESON_TAC [AFFINE_INDEPENDENT_SUBSET, DELETE_SUBSET],
        ASM_SIMP_TAC [AFF_DIM_AFFINE_INDEPENDENT]] THEN
      REWRITE_TAC [← INT_ARITH (← q r"x - &1:int = y - &1 - &1 <=> y = x + &1")] THEN
      REWRITE_TAC [INT_OF_NUM_ADD, INT_OF_NUM_EQ] THEN
      ASM_SIMP_TAC [CARD_DELETE, AFFINE_INDEPENDENT_IMP_FINITE] THEN
      MATCH_MP_TAC (← ARITH_RULE (← q r"~(s = 0) ==> s = s - 1 + 1")) THEN
      ASM_SIMP_TAC [CARD_EQ_0, AFFINE_INDEPENDENT_IMP_FINITE] THEN
      ASM SET_TAC []])

  let FACET_OF_CONVEX_HULL_AFFINE_INDEPENDENT_ALT ← prove
   r"!s t:real^N->bool.
        ~affine_dependent s
        ==> (t facet_of (convex hull s) <=>
             2 <= CARD s /\ ?u. u IN s /\ t = convex hull (s DELETE u))"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [FACET_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"u:real^N") THEN
    ASM_CASES_TAC (← q r"t = convex hull (s DELETE (u:real^N))") THEN
    ASM_REWRITE_TAC [CONVEX_HULL_EQ_EMPTY] THEN
    ASM_CASES_TAC (← q r"(u:real^N) IN s") THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"CARD s = 1 + CARD(s DELETE (u:real^N))") SUBST1_TAC THENL
     [ASM_SIMP_TAC [CARD_DELETE, AFFINE_INDEPENDENT_IMP_FINITE] THEN
      MATCH_MP_TAC (← ARITH_RULE (← q r"~(s = 0) ==> s = 1 + s - 1")) THEN
      ASM_SIMP_TAC [CARD_EQ_0, AFFINE_INDEPENDENT_IMP_FINITE] THEN
      ASM SET_TAC [],
      REWRITE_TAC [← ARITH_RULE (← q r"2 <= 1 + x <=> ~(x = 0)")] THEN
      ASM_SIMP_TAC [CARD_EQ_0, AFFINE_INDEPENDENT_IMP_FINITE, FINITE_DELETE]])

  let SEGMENT_FACE_OF ← prove
   r"!s a b:real^N.
    segment[a,b] face_of s ==> a extreme_point_of s /\ b extreme_point_of s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM FACE_OF_SING] THEN
    MATCH_MP_TAC FACE_OF_TRANS THEN EXISTS_TAC (← q r"segment[a:real^N,b]") THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [FACE_OF_SING, EXTREME_POINT_OF_SEGMENT])

  let SEGMENT_EDGE_OF ← prove
   r"!s a b:real^N.
        segment[a,b] edge_of s
        ==> ~(a = b) /\ a extreme_point_of s /\ b extreme_point_of s"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [ALL_TAC, ASM_MESON_TAC [edge_of, SEGMENT_FACE_OF]] THEN
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    SIMP_TAC [SEGMENT_REFL, edge_of, AFF_DIM_SING] THEN INT_ARITH_TAC)

  let EXTREME_POINT_OF_CONVEX_HULL_INSERT_EQ ← prove
   r"!s a x:real^N.
        FINITE s /\ ~(a IN affine hull s)
        ==> (x extreme_point_of (convex hull (a INSERT s)) <=>
             x = a \/ x extreme_point_of (convex hull s))"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM AFFINE_HULL_CONVEX_HULL] THEN
    STRIP_TAC THEN ONCE_REWRITE_TAC [← SET_RULE (← q r"a INSERT s = {a} UNION s")] THEN
    ONCE_REWRITE_TAC [HULL_UNION_RIGHT] THEN
    MP_TAC (← ISPEC (← q r"convex hull s:real^N->bool") KREIN_MILMAN_MINKOWSKI) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [CONVEX_CONVEX_HULL, COMPACT_CONVEX_HULL, FINITE_IMP_COMPACT],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ] FINITE_SUBSET)) THEN
    DISCH_THEN (MP_TAC o SPEC
     (← q r"{x:real^N | x extreme_point_of convex hull s}")) THEN
    REWRITE_TAC [EXTREME_POINTS_OF_CONVEX_HULL] THEN
    ABBREV_TAC (← q r"v = {x:real^N | x extreme_point_of (convex hull s)}") THEN
    DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE (RAND_CONV o RAND_CONV)
     [AFFINE_HULL_CONVEX_HULL]) THEN
    ASM_CASES_TAC (← q r"(a:real^N) IN v") THEN ASM_SIMP_TAC [HULL_INC] THEN
    STRIP_TAC THEN REWRITE_TAC [← GSYM HULL_UNION_RIGHT] THEN
    REWRITE_TAC [← SET_RULE (← q r"{a} UNION s = a INSERT s")] THEN EQ_TAC THENL
     [DISCH_THEN (MP_TAC o MATCH_MP EXTREME_POINT_OF_CONVEX_HULL) THEN
      ASM SET_TAC [],
      STRIP_TAC THENL
       [ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC EXTREME_POINT_OF_CONVEX_HULL_INSERT THEN
        ASM_MESON_TAC [CONVEX_HULL_SUBSET_AFFINE_HULL, SUBSET],
        REWRITE_TAC [← GSYM FACE_OF_SING] THEN
        MATCH_MP_TAC FACE_OF_TRANS THEN
        EXISTS_TAC (← q r"convex hull v:real^N->bool") THEN
        ASM_REWRITE_TAC [FACE_OF_SING] THEN
        MATCH_MP_TAC FACE_OF_CONVEX_HULLS THEN
        ASM_SIMP_TAC [FINITE_INSERT, AFFINE_HULL_SING, CONVEX_HULL_SING,
                 ← SET_RULE (← q r"~(a IN s) ==> a INSERT s DIFF s = {a}")] THEN
        ASM SET_TAC []]])

  let FACE_OF_CONVEX_HULL_INSERT_EQ ← (do
    let lemma ← prove
     r"!a b c p:real^N u v w x.
          x % p = u % a + v % b + w % c
          ==> !s. u + v + w = x /\ ~(x = &0) /\ affine s /\
                  a IN s /\ b IN s /\ c IN s
                  ==> p IN s"
     (REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o AP_TERM (← q r"(%) (inv x):real^N->real^N")) THEN
      ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, VECTOR_MUL_LID] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [VECTOR_ADD_LDISTRIB, VECTOR_MUL_ASSOC] THEN
      MATCH_MP_TAC (← SET_RULE (← q r"!t. x IN t /\ t SUBSET s ==> x IN s")) THEN
      EXISTS_TAC (← q r"affine hull {a:real^N,b,c}") THEN
      ASM_SIMP_TAC [HULL_MINIMAL, INSERT_SUBSET, EMPTY_SUBSET] THEN
      REWRITE_TAC [AFFINE_HULL_3, IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC
       [← q r"inv x * u:real", ← q r"inv x * v:real", ← q r"inv x * w:real"] THEN
      REWRITE_TAC [] THEN UNDISCH_TAC (← q r"u + v + w:real = x") THEN
      UNDISCH_TAC (← q r"~(x = &0)") THEN CONV_TAC (fun t => REAL_FIELD t))
    prove
     r"!f s a:real^N.
        FINITE s /\ ~(a IN affine hull s)
        ==> (f face_of (convex hull (a INSERT s)) <=>
             f face_of (convex hull s) \/
             ?f'. f' face_of (convex hull s) /\
                  f = convex hull (a INSERT f'))"
     (REPEAT STRIP_TAC THEN EQ_TAC THENL
       [DISCH_TAC THEN FIRST_ASSUM (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT]
          FACE_OF_CONVEX_HULL_SUBSET)) THEN
        ASM_SIMP_TAC [COMPACT_INSERT, FINITE_IMP_COMPACT] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"t:real^N->bool") STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_CASES_TAC (← q r"(a:real^N) IN t") THENL
         [ALL_TAC,
          DISJ1_TAC THEN MATCH_MP_TAC FACE_OF_SUBSET THEN
          EXISTS_TAC (← q r"convex hull ((a:real^N) INSERT s)") THEN
          ASM_REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN
          ASM SET_TAC []] THEN
        DISJ2_TAC THEN
        EXISTS_TAC (← q r"(convex hull t) INTER (convex hull s):real^N->bool") THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC FACE_OF_SUBSET THEN
          EXISTS_TAC (← q r"convex hull ((a:real^N) INSERT s)") THEN
          SIMP_TAC [INTER_SUBSET, HULL_MONO, ← SET_RULE (← q r"s SUBSET (a INSERT s)")] THEN
          MATCH_MP_TAC FACE_OF_INTER THEN ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC FACE_OF_CONVEX_HULL_INSERT THEN
          ASM_REWRITE_TAC [FACE_OF_REFL_EQ, CONVEX_CONVEX_HULL],
          MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
          MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_CONVEX_HULL] THEN
          ASM_SIMP_TAC [INSERT_SUBSET, HULL_INC, INTER_SUBSET] THEN
          REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_INC THEN
          ASM_CASES_TAC (← q r"x:real^N = a") THEN ASM_REWRITE_TAC [IN_INSERT] THEN
          REWRITE_TAC [IN_INTER] THEN CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN
          ASM SET_TAC []],
        ALL_TAC] THEN
      DISCH_THEN (DISJ_CASES_THEN ASSUME_TAC) THENL
       [MATCH_MP_TAC FACE_OF_CONVEX_HULL_INSERT THEN ASM_REWRITE_TAC [],
        FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"f':real^N->bool") MP_TAC)] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC) THEN
      SPEC_TAC (← q r"f':real^N->bool", ← q r"f:real^N->bool") THEN REPEAT STRIP_TAC THEN
      ASM_CASES_TAC (← q r"s:real^N->bool = {}") THENL
       [UNDISCH_TAC (← q r"(f:real^N->bool) face_of convex hull s") THEN
        ASM_SIMP_TAC [FACE_OF_EMPTY, CONVEX_HULL_EMPTY, FACE_OF_REFL_EQ] THEN
        REWRITE_TAC [CONVEX_CONVEX_HULL],
        ALL_TAC] THEN
      ASM_CASES_TAC (← q r"f:real^N->bool = {}") THENL
       [ASM_REWRITE_TAC [CONVEX_HULL_SING, FACE_OF_SING] THEN
        MATCH_MP_TAC EXTREME_POINT_OF_CONVEX_HULL_INSERT THEN
        ASM_REWRITE_TAC [] THEN
        ASM_MESON_TAC [CONVEX_HULL_SUBSET_AFFINE_HULL, SUBSET],
        ALL_TAC] THEN
      REWRITE_TAC [face_of, CONVEX_CONVEX_HULL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC HULL_MINIMAL THEN
        SIMP_TAC [INSERT_SUBSET, HULL_INC, IN_INSERT, CONVEX_CONVEX_HULL] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC (← q r"convex hull s:real^N->bool") THEN
        ASM_SIMP_TAC [HULL_MONO, ← SET_RULE (← q r"s SUBSET (a INSERT s)")] THEN
        ASM_MESON_TAC [FACE_OF_IMP_SUBSET],
        ALL_TAC] THEN
      ASM_REWRITE_TAC [CONVEX_HULL_INSERT_ALT] THEN
      REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC] THEN
      REWRITE_TAC [IMP_IMP, ← GSYM CONJ_ASSOC] THEN
      X_GEN_TAC (← q r"ub:real") THEN STRIP_TAC THEN
      X_GEN_TAC (← q r"b:real^N") THEN STRIP_TAC THEN
      X_GEN_TAC (← q r"uc:real") THEN STRIP_TAC THEN
      X_GEN_TAC (← q r"c:real^N") THEN STRIP_TAC THEN
      X_GEN_TAC (← q r"ux:real") THEN STRIP_TAC THEN
      X_GEN_TAC (← q r"x:real^N") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [face_of]) THEN
      SUBGOAL_THEN (← q r"convex hull f:real^N->bool = f") SUBST_ALL_TAC THENL
       [ASM_MESON_TAC [CONVEX_HULL_EQ], ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT]) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"v:real") MP_TAC)) THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC [← VECTOR_ARITH
       (← q r"(&1 - ux) % a + ux % x:real^N =
        (&1 - v) % ((&1 - ub) % a + ub % b) + v % ((&1 - uc) % a + uc % c) <=>
        ((&1 - ux) - ((&1 - v) * (&1 - ub) + v * (&1 - uc))) % a +
        (ux % x - (((&1 - v) * ub) % b + (v * uc) % c)) = vec 0")] THEN
      ASM_CASES_TAC (← q r"&1 - ux - ((&1 - v) * (&1 - ub) + v * (&1 - uc)) = &0") THENL
       [ASM_REWRITE_TAC [VECTOR_MUL_LZERO, VECTOR_ADD_LID] THEN
        FIRST_ASSUM (ASSUME_TAC o MATCH_MP (← REAL_RING
         (← q r"(&1 - ux) - ((&1 - v) * (&1 - ub) + v * (&1 - uc)) = &0
          ==> (&1 - v) * ub + v * uc = ux"))) THEN
        ASM_CASES_TAC (← q r"uc = &0") THENL
         [UNDISCH_THEN (← q r"uc = &0") SUBST_ALL_TAC THEN
          FIRST_X_ASSUM (SUBST_ALL_TAC o MATCH_MP (← REAL_ARITH
           (← q r"a + v * &0 = b ==> b = a"))) THEN
          REWRITE_TAC [REAL_MUL_RZERO, VECTOR_MUL_LZERO, VECTOR_ADD_RID] THEN
          REWRITE_TAC [VECTOR_SUB_EQ, VECTOR_MUL_LCANCEL, REAL_ENTIRE] THEN
          STRIP_TAC THENL
           [ASM_REAL_ARITH_TAC,
            ASM_MESON_TAC [VECTOR_MUL_LZERO],
            ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
            REWRITE_TAC [IN_ELIM_THM] THEN
            MAP_EVERY EXISTS_TAC [← q r"&0", ← q r"x:real^N"] THEN
            ASM_REWRITE_TAC [] THEN CONV_TAC (fun t => VECTOR_ARITH t)],
          ALL_TAC] THEN
        ASM_CASES_TAC (← q r"ub = &0") THENL
         [UNDISCH_THEN (← q r"ub = &0") SUBST_ALL_TAC THEN
          FIRST_X_ASSUM (SUBST_ALL_TAC o MATCH_MP (← REAL_ARITH
           (← q r"v * &0 + a = b ==> b = a"))) THEN
          REWRITE_TAC [REAL_MUL_RZERO, VECTOR_MUL_LZERO, VECTOR_ADD_LID] THEN
          REWRITE_TAC [VECTOR_SUB_EQ, VECTOR_MUL_LCANCEL, REAL_ENTIRE] THEN
          STRIP_TAC THENL
           [ASM_REAL_ARITH_TAC,
            ASM_MESON_TAC [VECTOR_MUL_LZERO],
            ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
            REWRITE_TAC [IN_ELIM_THM] THEN
            MAP_EVERY EXISTS_TAC [← q r"&0", ← q r"x:real^N"] THEN
            ASM_REWRITE_TAC [] THEN CONV_TAC (fun t => VECTOR_ARITH t)],
          ALL_TAC] THEN
        DISCH_THEN (fun th => tactic_of do pure (
          SUBGOAL_THEN
           (← q r"(b:real^N) IN f /\ (c:real^N) IN f")
          MP_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN MP_TAC th)) THEN
        ASM_CASES_TAC (← q r"ux = &0") THENL
         [DISCH_THEN (K ALL_TAC : thm → tactic) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          EXISTS_TAC (← q r"x:real^N") THEN ASM_REWRITE_TAC [] THEN
          FIRST_X_ASSUM (MP_TAC o MATCH_MP (← REAL_ARITH
           (← q r"&1 - ux - a = &0 ==> ux = &0 ==> ~(a < &1)"))) THEN
          ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← TAUT (← q r"p ==> ~p ==> q")) THEN
          MATCH_MP_TAC REAL_LTE_TRANS THEN
          EXISTS_TAC (← q r"(&1 - v) * &1 + v * &1") THEN
          CONJ_TAC THENL [ALL_TAC, REAL_ARITH_TAC] THEN
          MATCH_MP_TAC (← REAL_ARITH
           (← q r"x <= y /\ w <= z /\ ~(x = y /\ w = z) ==> x + w < y + z")) THEN
          ASM_SIMP_TAC [REAL_LE_LMUL_EQ, REAL_SUB_LT, REAL_EQ_MUL_LCANCEL] THEN
          REPEAT (CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
          ASM_SIMP_TAC [REAL_SUB_0, REAL_LT_IMP_NE] THEN
          REWRITE_TAC [← REAL_ARITH (← q r"&1 - x = &1 <=> x = &0")] THEN
          DISCH_THEN (CONJUNCTS_THEN SUBST_ALL_TAC) THEN
          ASM_MESON_TAC [VECTOR_MUL_LZERO],
          ALL_TAC] THEN
        REWRITE_TAC [VECTOR_SUB_EQ] THEN ASM_CASES_TAC (← q r"c:real^N = b") THENL
         [ASM_REWRITE_TAC [← GSYM VECTOR_ADD_RDISTRIB, VECTOR_MUL_LCANCEL] THEN
          ASM_MESON_TAC [],
          ALL_TAC] THEN
        DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        EXISTS_TAC (← q r"x:real^N") THEN ASM_REWRITE_TAC [IN_SEGMENT] THEN
        EXISTS_TAC (← q r"(v * uc) / ux:real") THEN
        ASM_SIMP_TAC [REAL_LT_RDIV_EQ, REAL_LT_LDIV_EQ, ← REAL_ARITH
         (← q r"&0 <= x /\ ~(x = &0) ==> &0 < x")] THEN
        REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_LID] THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC,
          EXPAND_TAC "ux" THEN REWRITE_TAC [← REAL_ARITH (← q r"b < a + b <=> &0 < a")] THEN
          MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC,
          FIRST_X_ASSUM (MP_TAC o AP_TERM (← q r"(%) (inv ux) :real^N->real^N")) THEN
          ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV] THEN
          REWRITE_TAC [VECTOR_MUL_LID] THEN DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC [VECTOR_ADD_LDISTRIB, VECTOR_MUL_ASSOC] THEN
          BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          REWRITE_TAC [← REAL_ARITH (← q r"inv u * v * uc:real = (v * uc) / u")] THEN
          UNDISCH_TAC (← q r"(&1 - v) * ub + v * uc = ux") THEN
          UNDISCH_TAC (← q r"~(ux = &0)") THEN CONV_TAC (fun t => REAL_FIELD t)],
        DISCH_THEN (MP_TAC o MATCH_MP (← VECTOR_ARITH
         (← q r"a + (b - c):real^N = vec 0 ==> a = c + --b"))) THEN
        REWRITE_TAC [← GSYM VECTOR_ADD_ASSOC, ← GSYM VECTOR_MUL_LNEG] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"affine hull s:real^N->bool") o
          MATCH_MP lemma) THEN
        ASM_REWRITE_TAC [AFFINE_AFFINE_HULL] THEN
        MATCH_MP_TAC (← TAUT (← q r"p ==> ~p ==> q")) THEN
        CONJ_TAC THENL [CONV_TAC (fun t => REAL_RING t), REPEAT CONJ_TAC] THEN
        MATCH_MP_TAC (← REWRITE_RULE [SUBSET] CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
        ASM_REWRITE_TAC [] THEN ASM SET_TAC []]))

  let CONVEX_HULL_REDUNDANT_SUBSET_GEN ← prove
   r"!s t:real^N->bool.
        compact s /\ t SUBSET s /\
        DISJOINT (s DIFF t) {x | x extreme_point_of convex hull s}
        ==> convex hull s = convex hull t"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    ASM_SIMP_TAC [HULL_MONO] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_CONVEX_HULL] THEN
    MP_TAC (← ISPEC (← q r"s:real^N->bool") EXTREME_POINTS_OF_CONVEX_HULL) THEN
    DISCH_THEN (DISJ_CASES_TAC o SPEC (← q r"t:real^N->bool") o MATCH_MP (← SET_RULE
     (← q r"e SUBSET s ==> !t. e SUBSET t \/ ~DISJOINT e (s DIFF t)")))
    THENL
     [TRANS_TAC SUBSET_TRANS (← q r"convex hull s:real^N->bool") THEN
      REWRITE_TAC [HULL_SUBSET] THEN
      MP_TAC (← ISPEC (← q r"convex hull s:real^N->bool") KREIN_MILMAN_MINKOWSKI) THEN
      ASM_SIMP_TAC [COMPACT_CONVEX_HULL, CONVEX_CONVEX_HULL] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [HULL_MONO],
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
        (← q r"~DISJOINT {x | P x} t ==> (!x. x IN t ==> ~P x) ==> Q"))) THEN
      ASM SET_TAC []])

  let CONVEX_HULL_REDUNDANT_SUBSET ← prove
   r"!s t:real^N->bool.
        compact s /\ t SUBSET s /\
        s DIFF t SUBSET interior(convex hull s)
        ==> convex hull s = convex hull t"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC CONVEX_HULL_REDUNDANT_SUBSET_GEN THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (← ISPEC (← q r"convex hull s:real^N->bool") EXTREME_POINT_NOT_IN_INTERIOR) THEN
    ASM SET_TAC [])

  let CONVEX_HULL_REDUNDANT_SUBSET_REV ← prove
   r"!s t:real^N->bool.
        convex hull s = convex hull t
        ==> DISJOINT (s DIFF t) {x | x extreme_point_of (convex hull s)}"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"t:real^N->bool") EXTREME_POINTS_OF_CONVEX_HULL) THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ASM SET_TAC [])

  let CONVEX_HULL_INSERT_REDUNDANT_POINT ← prove
   r"!s a b c:real^N.
        a IN convex hull (c INSERT s) /\
        b IN convex hull (c INSERT s) /\
        c IN segment(a,b)
        ==> convex hull (c INSERT s) = convex hull s"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"s:real^N->bool = {}") THENL
     [ASM_SIMP_TAC [CONVEX_HULL_SING, IN_SING] THEN
      MESON_TAC [ENDS_NOT_IN_SEGMENT],
      DISCH_TAC] THEN
    REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN
    SIMP_TAC [HULL_MONO, ← SET_RULE (← q r"s SUBSET x INSERT s")] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN
    SIMP_TAC [CONVEX_CONVEX_HULL, INSERT_SUBSET, HULL_SUBSET] THEN
    FIRST_X_ASSUM (MP_TAC o check (HolCore.Basics.is_conj o concl)) THEN
    ASM_REWRITE_TAC [CONVEX_HULL_INSERT_ALT] THEN
    REWRITE_TAC [IN_SEGMENT, IN_ELIM_THM] THEN
    REWRITE_TAC [IMP_CONJ, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"u:real", ← q r"x:real^N"] THEN REPEAT DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"v:real", ← q r"y:real^N"] THEN REPEAT DISCH_TAC THEN
    X_GEN_TAC (← q r"w:real") THEN DISCH_TAC THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [← VECTOR_ARITH
     (← q r"c:real^N = (&1 - w) % ((&1 - u) % c + u % x) + w % ((&1 - v) % c + v % y)
      <=> (u - w * u) % x + (w * v) % y = ((u - w * u) + w * v) % c")] THEN
    SUBGOAL_THEN (← q r"&0 < u - w * u + w * v") ASSUME_TAC THENL
     [MATCH_MP_TAC (← REAL_ARITH
       (← q r"~((&1 - w) * u = &0 /\ w * v = &0) /\
         &0 <= (&1 - w) * u /\ &0 <= w * v
         ==> &0 < u - w * u + w * v")) THEN
      ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_IMP_LE, REAL_SUB_LE, REAL_ENTIRE] THEN
      ASM_CASES_TAC (← q r"u = &0 /\ v = &0") THENL
       [ASM_MESON_TAC [VECTOR_MUL_LZERO], ASM_REAL_ARITH_TAC],
      DISCH_THEN (MP_TAC o AP_TERM
       (← q r"(%) (inv(u - w * u + w * v)):real^N->real^N")) THEN
      ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, REAL_LT_IMP_NZ] THEN
      REWRITE_TAC [VECTOR_MUL_LID, VECTOR_ADD_LDISTRIB, VECTOR_MUL_ASSOC] THEN
      DISCH_THEN (SUBST1_TAC o SYM)] THEN
    SUBGOAL_THEN
     (← q r"inv(u - w * u + w * v) * (u - w * u) =
      &1 - inv(u - w * u + w * v) * w * v")
    SUBST1_TAC THENL
     [UNDISCH_TAC (← q r"&0 < u - w * u + w * v") THEN CONV_TAC (fun t => REAL_FIELD t),
      MATCH_MP_TAC IN_CONVEX_SET] THEN
    ASM_REWRITE_TAC [CONVEX_CONVEX_HULL] THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_MUL_SYM] (← GSYM real_div)] THEN
    ASM_SIMP_TAC [REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ] THEN
    REWRITE_TAC [← REAL_ARITH
     (← q r"w * v <= &1 * (u - w * u + w * v) <=> &0 <= (&1 - w) * u")] THEN
    ASM_SIMP_TAC [REAL_MUL_LZERO, REAL_LE_MUL, REAL_LT_IMP_LE, REAL_SUB_LE])

  let CONVEX_HULL_REDUNDANT_POINT ← prove
   r"!s a:real^N. convex hull (s DELETE a) = convex hull s <=>
                ~(a extreme_point_of convex hull s)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (SUBST1_TAC o SYM) THEN DISCH_THEN (MP_TAC o MATCH_MP (← SET_RULE
       (← q r"a extreme_point_of convex hull s
        ==> {x | x extreme_point_of convex hull s} SUBSET s ==> a IN s"))) THEN
      REWRITE_TAC [EXTREME_POINTS_OF_CONVEX_HULL, IN_DELETE],
      DISJ_CASES_TAC (← SET_RULE (← q r"s DELETE (a:real^N) = s \/ a IN s")) THEN
      ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"t = s DELETE (a:real^N)") THEN
      SUBGOAL_THEN (← q r"s = (a:real^N) INSERT t") SUBST1_TAC THENL
       [ASM SET_TAC [], REWRITE_TAC [extreme_point_of]] THEN
      SIMP_TAC [HULL_INC, IN_INSERT] THEN DISCH_TAC THEN
      MATCH_MP_TAC (← GSYM CONVEX_HULL_INSERT_REDUNDANT_POINT) THEN
      ASM_MESON_TAC []])

  let HAUSDIST_FRONTIERS_CONVEX ← prove
   r"!s t:real^N->bool.
        convex s /\ convex t /\ bounded s /\ bounded t
        ==> hausdist(frontier s,frontier t) = hausdist(s,t)"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"s:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [HAUSDIST_EMPTY, REAL_LE_REFL] THEN
    ASM_CASES_TAC (← q r"t:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [HAUSDIST_EMPTY, FRONTIER_EMPTY, REAL_LE_REFL] THEN
    ONCE_REWRITE_TAC [← GSYM (← CONJUNCT2 HAUSDIST_CLOSURE)] THEN
    ONCE_REWRITE_TAC [← GSYM (← CONJUNCT1 HAUSDIST_CLOSURE)] THEN
    SUBGOAL_THEN
     (← q r"closure(frontier s):real^N->bool = frontier(closure s) /\
      closure(frontier t):real^N->bool = frontier(closure t)")
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_SIMP_TAC [FRONTIER_CLOSURE_CONVEX] THEN
      SIMP_TAC [CLOSURE_CLOSED, FRONTIER_CLOSED],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"compact(closure s:real^N->bool) /\
      compact(closure t:real^N->bool) /\
      convex(closure s:real^N->bool) /\
      convex(closure t:real^N->bool) /\
      ~(closure s = {}) /\ ~(closure t = {})")
    MP_TAC THENL
     [ASM_SIMP_TAC [COMPACT_CLOSURE, CONVEX_CLOSURE, CLOSURE_EQ_EMPTY],
      POP_ASSUM_LIST (K ALL_TAC) THEN
      SPEC_TAC (← q r"closure t:real^N->bool", ← q r"t:real^N->bool") THEN
      SPEC_TAC (← q r"closure s:real^N->bool", ← q r"s:real^N->bool") THEN
      REWRITE_TAC [COMPACT_EQ_BOUNDED_CLOSED] THEN
      MAP_EVERY X_GEN_TAC [← q r"s:real^N->bool", ← q r"t:real^N->bool"] THEN
      REPEAT STRIP_TAC] THEN
    REWRITE_TAC [← GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [ALL_TAC,
      MP_TAC (← ISPECL [← q r"frontier s:real^N->bool", ← q r"frontier t:real^N->bool"]
          HAUSDIST_CONVEX_HULLS) THEN
      ASM_SIMP_TAC [← GSYM KREIN_MILMAN_FRONTIER, COMPACT_EQ_BOUNDED_CLOSED,
                    BOUNDED_FRONTIER]] THEN
    MATCH_MP_TAC REAL_HAUSDIST_LE THEN
    ASM_REWRITE_TAC [FRONTIER_EQ_EMPTY] THEN
    REPLICATE_TAC 2
     (CONJ_TAC THENL [ASM_MESON_TAC [NOT_BOUNDED_UNIV], ALL_TAC]) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_HAUSDIST THEN
    ASM_REWRITE_TAC [LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM] THEN
    MP_TAC (← ISPECL
     [← q r"s:real^N->bool", ← q r"t:real^N->bool", ← q r"hausdist(s:real^N->bool,t)"]
          REAL_HAUSDIST_LE_EQ) THEN
    ASM_REWRITE_TAC [REAL_LE_REFL] THEN STRIP_TAC THEN
    REPEAT (CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC]) THENL
     [ALL_TAC,
      ONCE_REWRITE_TAC [DISJ_SYM] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN
      ONCE_REWRITE_TAC [HAUSDIST_SYM] THEN
      SPEC_TAC (← q r"y:real^N", ← q r"x:real^N") THEN
      SPEC_TAC (← q r"t:real^N->bool", ← q r"t:real^N->bool") THEN
      SPEC_TAC (← q r"s:real^N->bool", ← q r"s:real^N->bool") THEN
      MAP_EVERY X_GEN_TAC [← q r"t:real^N->bool", ← q r"s:real^N->bool"] THEN
      REPEAT STRIP_TAC] THEN
    (ASM_CASES_TAC (← q r"(x:real^N) IN frontier t") THENL
       [EXISTS_TAC (← q r"x:real^N") THEN
        ASM_SIMP_TAC [SETDIST_SING_IN_SET, SETDIST_POS_LE] THEN
        UNDISCH_TAC (← q r"(x:real^N) IN frontier s") THEN
        ASM_REWRITE_TAC [frontier, IN_DIFF] THEN
        ASM_SIMP_TAC [CLOSURE_CLOSED],
        ALL_TAC] THEN
      ASM_CASES_TAC (← q r"(x:real^N) IN t") THENL
       [ALL_TAC,
        EXISTS_TAC (← q r"x:real^N") THEN
        ASM_SIMP_TAC [SETDIST_SING_FRONTIER, REAL_LE_REFL] THEN
        UNDISCH_TAC (← q r"(x:real^N) IN frontier s") THEN
        ASM_REWRITE_TAC [frontier, IN_DIFF] THEN
        ASM_SIMP_TAC [CLOSURE_CLOSED]] THEN
      MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"x:real^N"]
          SUPPORTING_HYPERPLANE_FRONTIER) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"a:real^N") STRIP_ASSUME_TAC) THEN
      MP_TAC (← ISPECL [← q r"t:real^N->bool", ← q r"x:real^N", ← q r"--a:real^N"]
          RAY_TO_FRONTIER) THEN
      ASM_REWRITE_TAC [VECTOR_NEG_EQ_0] THEN ANTS_TAC THENL
       [UNDISCH_TAC (← q r"~((x:real^N) IN frontier t)") THEN
        ASM_REWRITE_TAC [frontier, IN_DIFF] THEN
        ASM_SIMP_TAC [CLOSURE_CLOSED, COMPACT_IMP_CLOSED],
        DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC)] THEN
      EXISTS_TAC (← q r"x + d % --a:real^N") THEN DISJ2_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC (← q r"(x + d % --a:real^N) IN frontier t") THEN
        ASM_SIMP_TAC [frontier, IN_DIFF, CLOSURE_CLOSED, COMPACT_IMP_CLOSED],
        ALL_TAC] THEN
      TRANS_TAC REAL_LE_TRANS (← q r"dist(x:real^N,x + d % --a)") THEN CONJ_TAC THENL
       [MATCH_MP_TAC SETDIST_LE_DIST THEN ASM_REWRITE_TAC [IN_SING],
        ALL_TAC] THEN
      TRANS_TAC REAL_LE_TRANS
       (← q r"setdist({x + d % --a:real^N},{y | a dot x <= a dot y})") THEN
      CONJ_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC SETDIST_SUBSET_RIGHT THEN
        MP_TAC (← ISPEC (← q r"s:real^N->bool") CLOSURE_SUBSET) THEN ASM SET_TAC []] THEN
      MATCH_MP_TAC REAL_LE_SETDIST THEN
      REWRITE_TAC [NOT_INSERT_EMPTY] THEN CONJ_TAC THENL
       [MP_TAC (← ISPEC (← q r"s:real^N->bool") CLOSURE_SUBSET) THEN ASM SET_TAC [],
        ALL_TAC] THEN
      REWRITE_TAC [IMP_CONJ, IN_SING, RIGHT_FORALL_IMP_THM, FORALL_UNWIND_THM2,
                   IN_ELIM_THM] THEN
      X_GEN_TAC (← q r"y:real^N") THEN DISCH_TAC THEN
      REWRITE_TAC [← NORM_ARITH (← q r"dist(x:real^N,x + a) = norm a")] THEN
      MP_TAC (← ISPECL [← q r"a:real^N", ← q r"y - (x + d % --a):real^N"]
          NORM_CAUCHY_SCHWARZ) THEN
      REWRITE_TAC [DOT_RSUB, DOT_RADD, DOT_RNEG,
                   ← ONCE_REWRITE_RULE [DIST_SYM] dist, DOT_RMUL] THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← REAL_ARITH
       (← q r"ay - (ax + d * --a) <= b ==> ax <= ay ==> d * a <= b"))) THEN
      ASM_REWRITE_TAC [← GSYM NORM_POW_2, NORM_MUL, NORM_NEG] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"(d * a pow 2):real = a * d * a")] THEN
      ASM_SIMP_TAC [REAL_LE_LMUL_EQ, NORM_POS_LT] THEN
      ASM_SIMP_TAC [real_abs, REAL_LT_IMP_LE]))

  pure { KREIN_MILMAN_POLYTOPE, EXTREME_POINTS_OF_CONVEX_HULL_EQ,
         EXTREME_POINT_OF_CONVEX_HULL_EQ, EXTREME_POINT_OF_CONVEX_HULL_CONVEX_INDEPENDENT,
         EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT,
         EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT, SIMPLEX_VERTICES_UNIQUE,
         EXTREME_POINT_OF_CONVEX_HULL_2, EXTREME_POINT_OF_SEGMENT, FACE_OF_CONVEX_HULL_SUBSET,
         FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT, FACET_OF_CONVEX_HULL_AFFINE_INDEPENDENT,
         FACET_OF_CONVEX_HULL_AFFINE_INDEPENDENT_ALT, SEGMENT_FACE_OF, SEGMENT_EDGE_OF,
         EXTREME_POINT_OF_CONVEX_HULL_INSERT_EQ, FACE_OF_CONVEX_HULL_INSERT_EQ,
         CONVEX_HULL_REDUNDANT_SUBSET_GEN, CONVEX_HULL_REDUNDANT_SUBSET,
         CONVEX_HULL_REDUNDANT_SUBSET_REV, CONVEX_HULL_INSERT_REDUNDANT_POINT,
         CONVEX_HULL_REDUNDANT_POINT, HAUSDIST_FRONTIERS_CONVEX }

/- ------------------------------------------------------------------------- -/
/- If we perturb a set little enough, a point stays inside or outside it.    -/
/- The "inside" needs convexity in general or we could just remove a         -/
/- thin path to the point without changing the Hausdorff distance at all.    -/
/- (polytope.ml 3692-4034)                                                   -/
/- ------------------------------------------------------------------------- -/

structure POI where
  HAUSDIST_STILL_OUTSIDE : thm
  HAUSDIST_STILL_INSIDE : thm
  HAUSDIST_STILL_INSIDE_INTERIOR : thm
  HAUSDIST_STILL_NONEMPTY_INTERIOR : thm
  HAUSDIST_STILL_SAME_PLACE_STRONG : thm
  HAUSDIST_STILL_SAME_PLACE : thm
  HAUSDIST_STILL_SAME_PLACE_CONIC_HULL_STRONG : thm
  HAUSDIST_STILL_SAME_PLACE_CONIC_HULL : thm
  CONVEX_SYMDIFF_CLOSE_TO_FRONTIER : thm
  deriving Inhabited

set_option maxHeartbeats 8000000 in
@[nospecialize]
def setupPOI [HolBase] (D : PolytopeDeps) (BPOF : POF) : ExceptT String IO POI := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON, MESON_TAC, NORM_ARITH, REAL_ARITH,
        SET_RULE, SET_TAC, VECTOR_ARITH, .. } := D.cvx
  let { CONJ_ASSOC, CONTRAPOS_THM, DE_MORGAN_THM, .. } := D.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_UNWIND_THM2, IMP_CONJ, IMP_CONJ_ALT, IN_DIFF, .. } :=
        D.cvx.core2
  let { IN_ELIM_THM, IN_INTER, IN_SING, IN_UNIV, LEFT_EXISTS_AND_THM, LEFT_IMP_EXISTS_THM,
        MEMBER_NOT_EMPTY, MONO_EXISTS, MONO_IMP, NOT_EXISTS_THM, NOT_IMP, NOT_IN_EMPTY,
        NOT_INSERT_EMPTY, PAIR_EQ, REAL_DIV_LMUL, REAL_DIV_RMUL, .. } := D.cvx.core3
  let { REAL_EQ_IMP_LE, REAL_LE_INV_EQ, REAL_LE_LMUL_EQ, REAL_LE_MUL, REAL_LE_REFL,
        REAL_LE_TRANS, REAL_LET_TRANS, REAL_LT_01, REAL_LT_DIV, REAL_LT_IMP_LE,
        REAL_LT_IMP_NZ, REAL_LT_LE, REAL_LT_MIN, REAL_LT_MUL_EQ, REAL_LT_RDIV_EQ,
        REAL_LT_REFL, REAL_LT_SUB_LADD, REAL_LTE_TRANS, REAL_MIN_LE, .. } := D.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_LZERO, REAL_MUL_SYM, REAL_NOT_LE, REAL_NOT_LT,
        REAL_SUB_LT, RIGHT_EXISTS_AND_THM, RIGHT_FORALL_IMP_THM, SUBSET, SUBSET_TRANS, .. }
        := D.cvx.core5
  let { real_abs, UNWIND_THM2, .. } := D.cvx.core6
  let { HULL_HULL, HULL_P, REAL_HALF, .. } := D.cvx.misc
  let { NORM_MUL, NORM_POS_LT, .. } := D.cvx.vec3
  let { dist, VECTOR_ADD_LID, VECTOR_MUL_ASSOC, VECTOR_MUL_EQ_0, VECTOR_MUL_LID,
        VECTOR_MUL_RZERO, .. } := D.cvx.vec4
  let { BALL_MIN_INTER, BOUNDED_CLOSURE, BOUNDED_INSERT, CLOSURE_CLOSED, CLOSURE_COMPLEMENT,
        .. } := D.cvx.top1
  let { CLOSURE_EQ_EMPTY, CLOSURE_SUBSET, .. } := D.cvx.top2
  let { FRONTIER_CLOSED, FRONTIER_COMPLEMENT, FRONTIER_EQ_EMPTY, HAUSDIST_CLOSURE,
        HAUSDIST_EMPTY, HAUSDIST_POS_LE, HAUSDIST_SYM, .. } := D.cvx.top3
  let { IN_BALL, IN_BALL_0, IN_INTERIOR, INTERIOR_SUBSET, NOT_BOUNDED_UNIV, .. } :=
        D.cvx.top4
  let { frontier, REAL_LE_HAUSDIST, REAL_SETDIST_LT_EXISTS, SETDIST_CLOSURE, SETDIST_EMPTY,
        SETDIST_LE_DIST, SETDIST_POS_LE, .. } := D.cvx.top5
  let { REAL_LE_RCANCEL_IMP, .. } := D.qses
  let { HULL_INSERT, .. } := D.qmisc
  let { BALL_SCALING, BOUNDED_CLOSURE_EQ, BOUNDED_INTERIOR, CLOSURE_INSERT,
        HAUSDIST_INSERT_LE, HAUSDIST_REFL, REAL_HAUSDIST_LE_EQ, REAL_LE_SETDIST_EQ,
        SETDIST_EQ_0_SING, SETDIST_FRONTIER, SETDIST_HAUSDIST_TRIANGLE, SETDIST_SING_IN_SET,
        SETDIST_SINGS, SETDIST_TRIANGLE, SUBSET_BALL, .. } := D.qtop
  let { BOUNDED_CONVEX_HULL, BOUNDED_CONVEX_HULL_EQ, .. } := D.qcvx1
  let { CONIC_HULL_CONTAINS_0, CONIC_HULL_EXPLICIT, CONVEX_CLOSURE, CONVEX_CLOSURE_INTERIOR,
        CONVEX_CONVEX_HULL, CONVEX_HULL_CLOSURE, CONVEX_HULL_EQ_EMPTY,
        CONVEX_HULL_INSERT_ALT, CONVEX_INTERIOR, .. } := D.qcvx2
  let { HAUSDIST_COMPLEMENTS_CONVEX_EXPLICIT, HAUSDIST_CONVEX_HULLS, .. } := D.qcvx3
  let { CLOSURE_CONIC_HULL, .. } := BPOF
  -- @@SCOPE END

  let HAUSDIST_STILL_OUTSIDE ← prove
   r"!s t x:real^N.

        bounded s /\ bounded t /\ hausdist(s,t) < setdist({x},s)
        ==> ~(x IN t)"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"s:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [HAUSDIST_EMPTY, SETDIST_EMPTY, REAL_LT_REFL] THEN
    ASM_CASES_TAC (← q r"t:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [NOT_IN_EMPTY] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [REAL_NOT_LT] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_HAUSDIST THEN
    ASM_REWRITE_TAC [RIGHT_EXISTS_AND_THM, LEFT_EXISTS_AND_THM] THEN
    ASM_MESON_TAC [REAL_HAUSDIST_LE_EQ, REAL_LE_REFL])

  let HAUSDIST_STILL_INSIDE ← prove
   r"!s t x:real^N.
        bounded s /\ bounded t /\ convex s /\ convex t /\ ~(t = {}) /\
        hausdist(s,t) < setdist({x},(:real^N) DIFF s)
        ==> x IN t"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← TAUT (← q r"(~p ==> F) ==> p")) THEN
    DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"t:real^N->bool", ← q r"s:real^N->bool",
                      ← q r"setdist({x},(:real^N) DIFF s)", ← q r"x:real^N"]
          HAUSDIST_COMPLEMENTS_CONVEX_EXPLICIT) THEN
    ASM_REWRITE_TAC [NOT_IMP, NOT_EXISTS_THM, DE_MORGAN_THM, REAL_NOT_LT] THEN
    CONJ_TAC THENL [ASM_MESON_TAC [HAUSDIST_SYM], ALL_TAC] THEN
    X_GEN_TAC (← q r"y:real^N") THEN ASM_CASES_TAC (← q r"(y:real^N) IN s") THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SETDIST_LE_DIST THEN
    ASM SET_TAC [])

  let HAUSDIST_STILL_INSIDE_INTERIOR ← prove
   r"!s t x:real^N.
        bounded s /\ bounded t /\ convex s /\ convex t /\ ~(t = {}) /\
        hausdist(s,t) < setdist({x},(:real^N) DIFF s)
        ==> x IN interior t"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [IN_INTERIOR] THEN
    EXISTS_TAC
       (← q r"setdist({x},(:real^N) DIFF s) - hausdist(s:real^N->bool,t)") THEN
    ASM_REWRITE_TAC [REAL_SUB_LT] THEN
    REWRITE_TAC [SUBSET, IN_BALL] THEN X_GEN_TAC (← q r"y:real^N") THEN DISCH_TAC THEN
    MATCH_MP_TAC HAUSDIST_STILL_INSIDE THEN
    EXISTS_TAC (← q r"s:real^N->bool") THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REAL_ARITH
      (← q r"d < f - h ==> f <= d + g ==> h < g"))) THEN
    REWRITE_TAC [← GSYM SETDIST_SINGS, SETDIST_TRIANGLE])

  let HAUSDIST_STILL_NONEMPTY_INTERIOR ← prove
   r"!s:real^N->bool.
      bounded s /\ convex s /\ ~(interior s = {})
      ==> ?e. &0 < e /\
              !s'. bounded s' /\ convex s' /\ ~(s' = {}) /\ hausdist(s,s') < e
                   ==> ~(interior s' = {})"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC [IN_INTERIOR] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"a:real^N") MP_TAC) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"r:real") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"t:real^N->bool") THEN
    STRIP_TAC THEN REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC (← q r"a:real^N") THEN MATCH_MP_TAC HAUSDIST_STILL_INSIDE_INTERIOR THEN
    EXISTS_TAC (← q r"s:real^N->bool") THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
     REAL_LTE_TRANS)) THEN
    ASM_REWRITE_TAC [REAL_LE_SETDIST_EQ, IN_SING, NOT_INSERT_EMPTY] THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_UNWIND_THM2] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    ASM_REWRITE_TAC [IN_DIFF, IN_UNIV, REAL_NOT_LE] THEN
    ASM_REWRITE_TAC [← GSYM IN_BALL, ← GSYM SUBSET] THEN
    REWRITE_TAC [← SET_RULE (← q r"UNIV DIFF s = {} <=> s = UNIV")] THEN
    ASM_MESON_TAC [NOT_BOUNDED_UNIV])

  let HAUSDIST_STILL_SAME_PLACE_STRONG ← prove
   r"!s t x:real^N.
        bounded s /\ bounded t /\ convex s /\ convex t /\
        ~(t = {}) /\ hausdist(s,t) < setdist({x},frontier s)
        ==> ~(x IN frontier s) /\ ~(x IN frontier t) /\ (x IN t <=> x IN s)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"~((x:real^N) IN frontier s)") ASSUME_TAC THENL
     [ASM_MESON_TAC [SETDIST_SING_IN_SET, REAL_NOT_LT, HAUSDIST_POS_LE],
      ASM_REWRITE_TAC []] THEN
    FIRST_X_ASSUM (MP_TAC o
      GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [frontier]) THEN
    REWRITE_TAC [IN_DIFF, DE_MORGAN_THM] THEN STRIP_TAC THENL
     [MP_TAC (← ISPECL
       [← q r"closure s:real^N->bool", ← q r"closure t:real^N->bool", ← q r"x:real^N"]
          HAUSDIST_STILL_OUTSIDE) THEN
      ASM_SIMP_TAC [HAUSDIST_CLOSURE, BOUNDED_CLOSURE, SETDIST_CLOSURE] THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REAL_ARITH
         (← q r"x < a ==> a = b ==> x < b"))) THEN
        MATCH_MP_TAC (← CONJUNCT2 SETDIST_FRONTIER),
        REWRITE_TAC [frontier] THEN
        MP_TAC (← ISPEC (← q r"t:real^N->bool") CLOSURE_SUBSET)] THEN
      MP_TAC (← ISPEC (← q r"s:real^N->bool") CLOSURE_SUBSET) THEN ASM SET_TAC [],
      SUBGOAL_THEN (← q r"(x:real^N) IN interior t") MP_TAC THENL
       [ALL_TAC,
        ASM_SIMP_TAC [frontier, IN_DIFF,
                      ← REWRITE_RULE [SUBSET] INTERIOR_SUBSET]] THEN
      REWRITE_TAC [IN_INTERIOR] THEN EXISTS_TAC
       (← q r"setdist({x:real^N},frontier s) - hausdist(s:real^N->bool,t)") THEN
      ASM_REWRITE_TAC [REAL_SUB_LT] THEN
      REWRITE_TAC [SUBSET, IN_BALL] THEN X_GEN_TAC (← q r"y:real^N") THEN DISCH_TAC THEN
      MATCH_MP_TAC HAUSDIST_STILL_INSIDE THEN
      EXISTS_TAC (← q r"interior s:real^N->bool") THEN
      ASM_SIMP_TAC [BOUNDED_INTERIOR, CONVEX_INTERIOR] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REAL_ARITH
        (← q r"d < f - h ==> h' = h /\ f <= d + g ==> h' < g"))) THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC [← GSYM (← CONJUNCT1 HAUSDIST_CLOSURE)] THEN
        AP_TERM_TAC THEN REWRITE_TAC [PAIR_EQ] THEN
        MATCH_MP_TAC CONVEX_CLOSURE_INTERIOR THEN ASM SET_TAC [],
        TRANS_TAC REAL_LE_TRANS (← q r"setdist({x},(:real^N) DIFF interior s)") THEN
        REWRITE_TAC [← GSYM SETDIST_SINGS, SETDIST_TRIANGLE] THEN
        REWRITE_TAC [← GSYM CLOSURE_COMPLEMENT, SETDIST_CLOSURE] THEN
        ONCE_REWRITE_TAC [← GSYM FRONTIER_COMPLEMENT] THEN
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        MATCH_MP_TAC (← CONJUNCT2 SETDIST_FRONTIER) THEN
        FIRST_ASSUM (MP_TAC o MATCH_MP (← REWRITE_RULE [SUBSET] INTERIOR_SUBSET)) THEN
        SET_TAC []]])

  let HAUSDIST_STILL_SAME_PLACE ← prove
   r"!s t x:real^N.
        bounded s /\ bounded t /\ convex s /\ convex t /\
        ~(t = {}) /\ hausdist(s,t) < setdist({x},frontier s)
        ==> (x IN t <=> x IN s)"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP HAUSDIST_STILL_SAME_PLACE_STRONG) THEN
    MESON_TAC [])

  let HAUSDIST_STILL_SAME_PLACE_CONIC_HULL_STRONG ← (do
    let lemma ← prove
     r"!a x:real^N s.
          convex s /\ &0 < a /\ ~(x = vec 0) /\ ~(s = {}) /\
          a * norm(x) < setdist({vec 0},s)
          ==> (x IN conic hull s <=>
               a % x IN convex hull (vec 0 INSERT s))"
     (ONCE_REWRITE_TAC [IMP_CONJ] THEN
      REWRITE_TAC [← MESON [HULL_HULL, CONVEX_CONVEX_HULL, HULL_P]
       (← q r"(!s. convex s ==> p s) <=> (!s. p (convex hull s))")] THEN
      REWRITE_TAC [← GSYM HULL_INSERT, CONVEX_HULL_EQ_EMPTY] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC [CONVEX_HULL_INSERT_ALT] THEN
      REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_ADD_LID] THEN
      REWRITE_TAC [CONIC_HULL_EXPLICIT, IN_ELIM_THM] THEN
      EQ_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"u:real", ← q r"y:real^N"] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
       [EXISTS_TAC (← q r"a * u:real"), EXISTS_TAC (← q r"inv(a) * u:real")] THEN
      EXISTS_TAC (← q r"y:real^N") THEN ASM_REWRITE_TAC [VECTOR_MUL_ASSOC] THENL
       [ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC (← REAL_ARITH (← q r"abs x <= a ==> x <= a")) THEN
        MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC (← q r"norm(y:real^N)") THEN
        CONJ_TAC THENL [ASM_MESON_TAC [NORM_POS_LT, VECTOR_MUL_EQ_0], ALL_TAC] THEN
        REWRITE_TAC [← GSYM NORM_MUL, ← GSYM VECTOR_MUL_ASSOC] THEN
        FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
        ASM_SIMP_TAC [NORM_MUL, real_abs, REAL_LT_IMP_LE, REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
           REAL_LTE_TRANS)) THEN
        ONCE_REWRITE_TAC [← NORM_ARITH (← q r"norm(x:real^N) = dist(vec 0,x)")] THEN
        MATCH_MP_TAC SETDIST_LE_DIST THEN ASM_REWRITE_TAC [IN_SING],
        ASM_SIMP_TAC [REAL_LE_INV_EQ, REAL_LE_MUL, REAL_LT_IMP_LE] THEN
        FIRST_X_ASSUM (MP_TAC o AP_TERM (← q r"(%) (inv a):real^N->real^N")) THEN
        ASM_SIMP_TAC [REAL_MUL_LINV, VECTOR_MUL_ASSOC, REAL_MUL_LINV,
                      VECTOR_MUL_LID, REAL_LT_IMP_NZ]])
    let clemma ← prove
     r"!a x:real^N s.
        convex s /\ bounded s /\ ~(vec 0 IN closure s) /\
        &0 < a /\ ~(x = vec 0) /\ ~(s = {}) /\
        a * norm(x) < setdist({vec 0},s)
        ==> (x IN closure(conic hull s) <=>
             a % x IN closure(convex hull (vec 0 INSERT s)))"
     (REPEAT STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"a:real", ← q r"x:real^N", ← q r"closure s:real^N->bool"] lemma) THEN
      ASM_SIMP_TAC [SETDIST_CLOSURE, CLOSURE_EQ_EMPTY, CONVEX_CLOSURE] THEN
      ASM_SIMP_TAC [CLOSURE_CONIC_HULL] THEN
      ASM_SIMP_TAC [← GSYM CONVEX_HULL_CLOSURE, BOUNDED_INSERT, CLOSURE_INSERT])
    let ilemma ← prove
     r"!a x:real^N s.
       convex s /\ &0 < a /\ ~(x = vec 0) /\ ~(s = {}) /\
       a * norm(x) < setdist({vec 0},s)
       ==> (x IN interior(conic hull s) <=>
            a % x IN interior(convex hull (vec 0 INSERT s)))"
     (REPEAT STRIP_TAC THEN REWRITE_TAC [IN_INTERIOR] THEN
      SUBGOAL_THEN
        (← q r"?d. &0 < d /\
          !y. y IN ball(x:real^N,d) ==> a * norm y < setdist({vec 0:real^N},s)")
      STRIP_ASSUME_TAC THENL
       [EXISTS_TAC (← q r"setdist({vec 0:real^N},s) / a - norm(x:real^N)") THEN
        ASM_SIMP_TAC [REAL_LT_RDIV_EQ, IN_BALL, REAL_LT_SUB_LADD] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC, X_GEN_TAC (← q r"y:real^N")] THEN
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] REAL_LET_TRANS) THEN
        GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
        ASM_SIMP_TAC [REAL_LE_LMUL_EQ] THEN CONV_TAC (fun t => NORM_ARITH t),
        MATCH_MP_TAC (← MESON []
         (← q r"(!e. &0 < e <=> &0 < a * e) /\ (!e. &0 < e <=> &0 < e / a) /\
          (!e. a * e / a = e) /\ (!d e. a * d <= a * e <=> d <= e) /\
          ((!d e. d <= e ==> P e ==> P d) /\ (!d e. d <= e ==> Q e ==> Q d)) /\
          (!e. &0 < e ==> ?d. &0 < d /\ d <= e /\ (P d <=> Q(a * d)))
          ==> ((?e. &0 < e /\ P e) <=> (?e. &0 < e /\ Q e))")) THEN
        ASM_SIMP_TAC [BALL_SCALING, REAL_LT_MUL_EQ, REAL_LE_LMUL_EQ,
          REAL_LT_IMP_NZ, REAL_LT_RDIV_EQ, REAL_MUL_LZERO, REAL_DIV_LMUL] THEN
        CONJ_TAC THENL [MESON_TAC [SUBSET_BALL, SUBSET_TRANS], ALL_TAC] THEN
        X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
        EXISTS_TAC (← q r"min d (min e (norm(x:real^N)))") THEN
        ASM_REWRITE_TAC [REAL_LT_MIN, REAL_MIN_LE, REAL_LE_REFL, NORM_POS_LT] THEN
        MATCH_MP_TAC (← MESON []
         (← q r"(!x. P x ==> (Q x <=> R x))
          ==> ((!x. P x ==> Q x) <=> (!x. P x ==> R x))")) THEN
        X_GEN_TAC (← q r"y:real^N") THEN REWRITE_TAC [BALL_MIN_INTER, IN_INTER] THEN
        STRIP_TAC THEN MATCH_MP_TAC lemma THEN ASM_SIMP_TAC [] THEN
        UNDISCH_TAC (← q r"y IN ball(x:real^N,norm x)") THEN
        REWRITE_TAC [IN_BALL] THEN CONV_TAC (fun t => NORM_ARITH t)])
    let flemma ← prove
     r"!a x:real^N s.
       convex s /\ bounded s /\ ~(vec 0 IN closure s) /\
       &0 < a /\ ~(x = vec 0) /\ ~(s = {}) /\
       a * norm(x) < setdist({vec 0},s)
       ==> (x IN frontier(conic hull s) <=>
            a % x IN frontier(convex hull (vec 0 INSERT s)))"
     (REWRITE_TAC [frontier, IN_DIFF] THEN
      SIMP_TAC [← GSYM ilemma, ← GSYM clemma])
    prove
     r"!s x:real^N.
       convex s /\ bounded s /\ ~(s = {}) /\ ~(vec 0 IN closure s) /\
       ~(x = vec 0) /\ ~(x IN frontier(conic hull s))
       ==> ?e. &0 < e /\
               !s'. convex s' /\ bounded s' /\ ~(s' = {}) /\ hausdist(s,s') < e
                    ==> ~(x IN frontier(conic hull s')) /\
                        (x IN conic hull s' <=> x IN conic hull s)"
     (REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"&0 < setdist({vec 0:real^N},s)") ASSUME_TAC THENL
       [REWRITE_TAC [REAL_LT_LE, SETDIST_POS_LE] THEN
        ASM_MESON_TAC [SETDIST_EQ_0_SING],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"?a d. &0 < a /\ &0 < d /\
              a * norm(x:real^N) < setdist({vec 0:real^N},s) /\
              !s'. convex s' /\ bounded s' /\ ~(s' = {}) /\ hausdist(s,s') < d
                   ==> a * norm(x) < setdist({vec 0:real^N},s')")
      STRIP_ASSUME_TAC THENL
       [EXISTS_TAC (← q r"setdist({vec 0:real^N},s) / &2 / norm(x:real^N)") THEN
        EXISTS_TAC (← q r"setdist({vec 0:real^N},s) / &2") THEN
        ASM_SIMP_TAC [REAL_HALF, REAL_DIV_RMUL, REAL_LT_IMP_NZ, NORM_POS_LT,
                      REAL_LT_DIV, ← REAL_ARITH (← q r"x / &2 < x <=> &0 < x")] THEN
        X_GEN_TAC (← q r"s':real^N->bool") THEN STRIP_TAC THEN
        MP_TAC (← ISPECL [← q r"{vec 0:real^N}", ← q r"s':real^N->bool", ← q r"s:real^N->bool"]
          SETDIST_HAUSDIST_TRIANGLE) THEN
        ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [HAUSDIST_SYM] THEN
        ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      EXISTS_TAC (← q r"min (min d (setdist({vec 0:real^N},s)))
         (setdist({a % x:real^N},frontier (convex hull (vec 0 INSERT s))))") THEN
      ASM_REWRITE_TAC [REAL_LT_MIN] THEN CONJ_TAC THENL
       [REWRITE_TAC [← REAL_ARITH (← q r"&0 < x <=> &0 <= x /\ ~(x = &0)")] THEN
        REWRITE_TAC [SETDIST_POS_LE, SETDIST_EQ_0_SING] THEN
        SIMP_TAC [CLOSURE_CLOSED, FRONTIER_CLOSED, FRONTIER_EQ_EMPTY] THEN
        ASM_SIMP_TAC [← GSYM flemma, HAUSDIST_REFL] THEN
        SIMP_TAC [CONVEX_HULL_EQ_EMPTY, NOT_INSERT_EMPTY] THEN
        ASM_MESON_TAC [BOUNDED_CONVEX_HULL, BOUNDED_INSERT, NOT_BOUNDED_UNIV],
        ALL_TAC] THEN
      X_GEN_TAC (← q r"s':real^N->bool") THEN STRIP_TAC THEN
      MP_TAC (← ISPECL
       [← q r"convex hull ((vec 0:real^N) INSERT s)",
        ← q r"convex hull ((vec 0:real^N) INSERT s')", ← q r"a % x:real^N"]
            HAUSDIST_STILL_SAME_PLACE_STRONG) THEN
      ASM_REWRITE_TAC [CONVEX_CONVEX_HULL, BOUNDED_CONVEX_HULL_EQ,
                       BOUNDED_INSERT, CONVEX_HULL_EQ_EMPTY, NOT_INSERT_EMPTY] THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT]
          REAL_LET_TRANS)) THEN
        W (MP_TAC o PART_MATCH (lhand o rand) HAUSDIST_CONVEX_HULLS o
          lhand o snd) THEN
        ASM_SIMP_TAC [BOUNDED_INSERT] THEN
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
        W (MP_TAC o PART_MATCH (lhand o rand) HAUSDIST_INSERT_LE o
          lhand o snd) THEN
        ASM_SIMP_TAC [BOUNDED_INSERT] THEN
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
        ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"a:real", ← q r"x:real^N"] lemma) THEN
      ASM_SIMP_TAC [HAUSDIST_REFL] THEN DISCH_THEN (K ALL_TAC : thm → tactic) THEN
      DISCH_THEN (fun th => tactic_of do
        pure (MP_TAC (← liftExcept (el 1 (CONJUNCTS th))))) THEN
      MP_TAC (← ISPECL [← q r"a:real", ← q r"x:real^N", ← q r"s':real^N->bool"] flemma) THEN
      ASM_SIMP_TAC [] THEN ANTS_TAC THENL [ALL_TAC, MESON_TAC []] THEN
      MATCH_MP_TAC HAUSDIST_STILL_OUTSIDE THEN EXISTS_TAC (← q r"s:real^N->bool") THEN
      ASM_REWRITE_TAC [BOUNDED_CLOSURE_EQ, HAUSDIST_CLOSURE]))

  let HAUSDIST_STILL_SAME_PLACE_CONIC_HULL ← prove
   r"!s x:real^N.
       convex s /\ bounded s /\ ~(s = {}) /\ ~(vec 0 IN closure s) /\
       ~(x IN frontier(conic hull s))
       ==> ?e. &0 < e /\
               !s'. convex s' /\ bounded s' /\ ~(s' = {}) /\ hausdist(s,s') < e
                    ==> (x IN conic hull s' <=> x IN conic hull s)"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"x:real^N = vec 0") THEN ASM_SIMP_TAC [CONIC_HULL_CONTAINS_0]
    THENL [MESON_TAC [REAL_LT_01], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&0 < setdist({vec 0:real^N},s)") ASSUME_TAC THENL
     [REWRITE_TAC [REAL_LT_LE, SETDIST_POS_LE] THEN
      ASM_MESON_TAC [SETDIST_EQ_0_SING],
      MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"x:real^N"]
          HAUSDIST_STILL_SAME_PLACE_CONIC_HULL_STRONG) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
      MESON_TAC []])

  let CONVEX_SYMDIFF_CLOSE_TO_FRONTIER ← prove
   r"!s t:real^N->bool e.
        bounded s /\ convex s /\ ~(s = {}) /\
        bounded t /\ convex t /\ ~(t = {}) /\
        hausdist(s,t) < e
        ==> (s DIFF t) UNION (t DIFF s) SUBSET
            {u + v:real^N | u IN frontier s /\ v IN ball(vec 0,e)}"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"x:real^N") THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"t:real^N->bool", ← q r"x:real^N"]
          HAUSDIST_STILL_SAME_PLACE) THEN
    ASM_REWRITE_TAC [] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [REAL_NOT_LT] THEN MATCH_MP_TAC MONO_IMP THEN
    CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"e:real") o MATCH_MP
     (← REAL_ARITH (← q r"a <= b ==> !c. b < c ==> a < c"))) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o MATCH_MP
     (← ONCE_REWRITE_RULE [IMP_CONJ_ALT] (← REWRITE_RULE [CONJ_ASSOC]
          REAL_SETDIST_LT_EXISTS))) THEN
    ASM_REWRITE_TAC [NOT_INSERT_EMPTY, FRONTIER_EQ_EMPTY] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [NOT_BOUNDED_UNIV], ALL_TAC] THEN
    REWRITE_TAC [IN_SING, RIGHT_EXISTS_AND_THM, UNWIND_THM2, ← GSYM CONJ_ASSOC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"u:real^N") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"x - u:real^N") THEN
    ASM_REWRITE_TAC [IN_BALL_0, ← GSYM dist] THEN CONV_TAC (fun t => VECTOR_ARITH t))

  pure { HAUSDIST_STILL_OUTSIDE, HAUSDIST_STILL_INSIDE, HAUSDIST_STILL_INSIDE_INTERIOR,
         HAUSDIST_STILL_NONEMPTY_INTERIOR, HAUSDIST_STILL_SAME_PLACE_STRONG,
         HAUSDIST_STILL_SAME_PLACE, HAUSDIST_STILL_SAME_PLACE_CONIC_HULL_STRONG,
         HAUSDIST_STILL_SAME_PLACE_CONIC_HULL, CONVEX_SYMDIFF_CLOSE_TO_FRONTIER }

/- ------------------------------------------------------------------------- -/
/- Polytopes; approximation of bounded convex sets by polytopes; polyhedra.  -/
/- (polytope.ml 4034-4499)                                                   -/
/- ------------------------------------------------------------------------- -/

structure POJ where
  polytope : thm
  POLYTOPE_TRANSLATION_EQ : thm
  POLYTOPE_LINEAR_IMAGE : thm
  POLYTOPE_LINEAR_IMAGE_EQ : thm
  POLYTOPE_EMPTY : thm
  POLYTOPE_NEGATIONS : thm
  POLYTOPE_CONVEX_HULL : thm
  POLYTOPE_SEGMENT : thm
  POLYTOPE_PCROSS : thm
  POLYTOPE_PCROSS_EQ : thm
  FACE_OF_POLYTOPE_POLYTOPE : thm
  FINITE_POLYTOPE_FACES : thm
  FINITE_POLYTOPE_FACETS : thm
  POLYTOPE_INTERVAL : thm
  POLYTOPE_SING : thm
  POLYTOPE_SCALING : thm
  POLYTOPE_SCALING_EQ : thm
  POLYTOPE_AFFINITY_EQ : thm
  POLYTOPE_AFFINITY : thm
  POLYTOPE_SUMS : thm
  POLYTOPE_IMP_COMPACT : thm
  POLYTOPE_IMP_CONVEX : thm
  POLYTOPE_IMP_CLOSED : thm
  POLYTOPE_IMP_BOUNDED : thm
  POLYTOPE_1 : thm
  POLYTOPE_AFF_DIM_1 : thm
  FACE_OF_POLYTOPE_INSERT_EQ : thm
  CONVEX_INNER_APPROXIMATION : thm
  CONVEX_OUTER_APPROXIMATION : thm
  CONVEX_INNER_POLYTOPE : thm
  CONVEX_OUTER_POLYTOPE : thm
  polyhedron : thm
  POLYHEDRON_INTER : thm
  POLYHEDRON_UNIV : thm
  POLYHEDRON_POSITIVE_ORTHANT : thm
  POLYHEDRON_INTERS : thm
  POLYHEDRON_EMPTY : thm
  POLYHEDRON_HALFSPACE_LE : thm
  POLYHEDRON_HALFSPACE_GE : thm
  POLYHEDRON_HYPERPLANE : thm
  AFFINE_IMP_POLYHEDRON : thm
  POLYHEDRON_IMP_CLOSED : thm
  POLYHEDRON_IMP_CONVEX : thm
  POLYHEDRON_AFFINE_HULL : thm
  deriving Inhabited

set_option maxHeartbeats 8000000 in
@[nospecialize]
def setupPOJ [HolBase] (D : PolytopeDeps) (BPOG : POG) (BPOH : POH) : ExceptT String IO POJ := do
  -- @@SCOPE BEGIN
  let { add_translation_invariants, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, GEOM_TRANSLATE_TAC,
        INT_ARITH, INT_REDUCE_CONV, invariant_under_linear, MESON_TAC, new_definition,
        REAL_ARITH, SET_RULE, SET_TAC, VECTOR_ARITH, .. } := D.cvx
  let { CONJ_ASSOC, CONJ_SYM, CONTRAPOS_THM, DE_MORGAN_THM, DIMINDEX_GE_1, EMPTY_GSPEC,
        EMPTY_SUBSET, EQ_IMP, EXISTS_PASTECART, EXTENSION, FINITE_EMPTY, FINITE_IMAGE,
        FINITE_INDUCT_STRONG, FINITE_INSERT, FINITE_NUMSEG, FINITE_POWERSET,
        FINITE_RESTRICT, FINITE_RULES, FINITE_SING, FINITE_SUBSET, FINITE_UNION,
        FORALL_AND_THM, FORALL_IN_GSPEC, .. } := D.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_IN_INSERT, FSTCART_PASTECART, IMAGE_CLAUSES, IMAGE_CONST,
        IMAGE_ID, IMAGE_o, IMP_CONJ, IMP_CONJ_ALT, INT_LE_REFL, INTER, INTERS_0, INTERS_1,
        INTERS_2, INTERS_IMAGE, INTERS_INSERT, .. } := D.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, IN_NUMSEG, IN_SING, IN_UNION, LE_REFL, LEFT_FORALL_IMP_THM,
        LEFT_IMP_EXISTS_THM, MONO_EXISTS, NOT_IN_EMPTY, NOT_INSERT_EMPTY,
        PASTECART_IN_PCROSS, PCROSS_EMPTY, .. } := D.cvx.core3
  let { REAL_LE_TRANS, REAL_LT_IMP_LE, .. } := D.cvx.core4
  let { REAL_MUL_LINV, REAL_NOT_LE, REAL_NOT_LT, RIGHT_EXISTS_AND_THM, RIGHT_FORALL_IMP_THM,
        RIGHT_IMP_EXISTS_THM, SIMPLE_IMAGE, SKOLEM_THM, SNDCART_PASTECART, SUBSET,
        SUBSET_EMPTY, SUBSET_REFL, .. } := D.cvx.core5
  let { o_DEF, UNIONS_0, UNIONS_GSPEC, UNIONS_IMAGE, UNWIND_THM1, UNWIND_THM2, .. } :=
        D.cvx.core6
  let { HULL_INC, HULL_MINIMAL, HULL_P, REAL_HALF, .. } := D.cvx.misc
  let { AFFINITY_SCALING_TRANSLATION, BASIS_NONZERO, DIST_SYM, DOT_BASIS, DOT_LNEG,
        DOT_LZERO, .. } := D.cvx.vec1
  let { INTERVAL_SING, LINEAR_FSTCART, LINEAR_SNDCART, .. } := D.cvx.vec2
  let { dist, VECTOR_ADD_RID, VECTOR_MUL_ASSOC, VECTOR_MUL_LID, VECTOR_MUL_LZERO,
        VECTOR_NEG_EQ_0, .. } := D.cvx.vec4
  let { BALL_EQ_EMPTY, BOUNDED_BALL, BOUNDED_SUMS, CENTRE_IN_BALL, CLOSED_INTERS,
        CLOSURE_APPROACHABLE, .. } := D.cvx.top1
  let { CLOSURE_EQ_EMPTY, CLOSURE_SUBSET, COMPACT_CLOSURE, COMPACT_IMP_BOUNDED,
        COMPACT_IMP_CLOSED, .. } := D.cvx.top2
  let { FINITE_IMP_BOUNDED, FINITE_IMP_COMPACT, HAUSDIST_EMPTY, HAUSDIST_SYM, .. } :=
        D.cvx.top3
  let { IN_BALL, IN_BALL_0, IS_INTERVAL_COMPACT, OPEN_BALL, .. } := D.cvx.top4
  let { REAL_HAUSDIST_LE, REAL_LE_HAUSDIST, REAL_SETDIST_LT_EXISTS, SEGMENT_REFL,
        SETDIST_LE_DIST, .. } := D.cvx.top5
  let { EXISTS_FINITE_SUBSET_IMAGE, FINITE_PCROSS, FINITE_PRODUCT_DEPENDENT, .. } := D.qses
  let { LINEAR_NEGATION, QUANTIFY_SURJECTION_THM, .. } := D.qvec
  let { HULL_UNION_RIGHT, .. } := D.qmisc
  let { CLOSED_HALFSPACE_LE, COMPACT_EQ_HEINE_BOREL, HAUSDIST_REFL, SETDIST_SING_IN_SET,
        SETDIST_SING_LE_HAUSDIST, .. } := D.qtop
  let { AFF_DIM_EMPTY, AFF_DIM_SEGMENT, AFF_DIM_SING, AFFINE_AFFINE_HULL,
        AFFINE_HULL_CONVEX_HULL, AFFINE_HULL_FINITE_INTERSECTION_HYPERPLANES,
        BOUNDED_CONVEX_HULL, CLOSED_INTERVAL_AS_CONVEX_HULL, COLLINEAR_AFF_DIM,
        COMPACT_CONVEX_COLLINEAR_SEGMENT, .. } := D.qcvx1
  let { COMPACT_CONVEX_HULL, CONVEX_BALL, CONVEX_CONVEX_HULL, CONVEX_HALFSPACE_LE,
        CONVEX_HULL_EMPTY, CONVEX_HULL_EQ_EMPTY, CONVEX_HULL_LINEAR_IMAGE,
        CONVEX_HULL_PCROSS, CONVEX_HULL_SCALING, CONVEX_HULL_SUMS, CONVEX_INTERS, .. } :=
        D.qcvx2
  let { CONVEX_SUMS, IS_INTERVAL_CONVEX_1, SEGMENT_CONVEX_HULL, SUBSET_SUMS_RCANCEL, .. } :=
        D.qcvx3
  let { facet_of, .. } := BPOG
  let { FACE_OF_CONVEX_HULL_INSERT_EQ, FACE_OF_CONVEX_HULL_SUBSET, .. } := BPOH
  -- @@SCOPE END

  let polytope ← new_definition
   r"polytope s <=> ?v. FINITE v /\ s = convex hull v"

  let POLYTOPE_TRANSLATION_EQ ← prove
   r"!a s. polytope (IMAGE (\x:real^N. a + x) s) <=> polytope s"
   (REWRITE_TAC [polytope] THEN GEOM_TRANSLATE_TAC [])

  add_translation_invariants [POLYTOPE_TRANSLATION_EQ]

  let POLYTOPE_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N p.
        linear f /\ polytope p ==> polytope(IMAGE f p)"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [polytope] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"s:real^M->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"IMAGE (f:real^M->real^N) s") THEN
    ASM_SIMP_TAC [CONVEX_HULL_LINEAR_IMAGE, FINITE_IMAGE])

  let POLYTOPE_LINEAR_IMAGE_EQ ← prove
   r"!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> (polytope (IMAGE f s) <=> polytope s)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [polytope] THEN
    MP_TAC (← ISPEC (← q r"f:real^M->real^N") QUANTIFY_SURJECTION_THM) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th => GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    MP_TAC (← HolLight.end_itlist CONJ
     (← HolMath.IndTypes.mapfilterM (ISPEC (← q r"f:real^M->real^N"))
          (← invariant_under_linear.get))) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [])

  let POLYTOPE_EMPTY ← prove
   r"polytope {}"
   (REWRITE_TAC [polytope] THEN MESON_TAC [FINITE_EMPTY, CONVEX_HULL_EMPTY])

  let POLYTOPE_NEGATIONS ← prove
   r"!s:real^N->bool. polytope s ==> polytope(IMAGE (--) s)"
   (SIMP_TAC [POLYTOPE_LINEAR_IMAGE, LINEAR_NEGATION])

  let POLYTOPE_CONVEX_HULL ← prove
   r"!s. FINITE s ==> polytope(convex hull s)"
   (REWRITE_TAC [polytope] THEN MESON_TAC [])

  let POLYTOPE_SEGMENT ← prove
   r"!a b:real^N. polytope(segment[a,b])"
   (REPEAT GEN_TAC THEN REWRITE_TAC [polytope] THEN
    EXISTS_TAC (← q r"{a:real^N,b}") THEN
    ASM_REWRITE_TAC [SEGMENT_CONVEX_HULL, FINITE_INSERT, FINITE_EMPTY])

  let POLYTOPE_PCROSS ← prove
   r"!s:real^M->bool t:real^N->bool.
        polytope s /\ polytope t ==> polytope(s PCROSS t)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [polytope] THEN
    MESON_TAC [CONVEX_HULL_PCROSS, FINITE_PCROSS])

  let POLYTOPE_PCROSS_EQ ← prove
   r"!s:real^M->bool t:real^N->bool.
        polytope(s PCROSS t) <=>
        s = {} \/ t = {} \/ polytope s /\ polytope t"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"s:real^M->bool = {}") THEN
    ASM_REWRITE_TAC [PCROSS_EMPTY, POLYTOPE_EMPTY] THEN
    ASM_CASES_TAC (← q r"t:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [PCROSS_EMPTY, POLYTOPE_EMPTY] THEN
    EQ_TAC THEN REWRITE_TAC [POLYTOPE_PCROSS] THEN REPEAT STRIP_TAC THENL
     [MP_TAC (← ISPECL [← q r"fstcart:real^(M,N)finite_sum->real^M",
                        ← q r"(s:real^M->bool) PCROSS (t:real^N->bool)"]
         POLYTOPE_LINEAR_IMAGE) THEN
      ASM_REWRITE_TAC [LINEAR_FSTCART],
      MP_TAC (← ISPECL [← q r"sndcart:real^(M,N)finite_sum->real^N",
                        ← q r"(s:real^M->bool) PCROSS (t:real^N->bool)"]
         POLYTOPE_LINEAR_IMAGE) THEN
      ASM_REWRITE_TAC [LINEAR_SNDCART]] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, IN_IMAGE, EXISTS_PASTECART, PASTECART_IN_PCROSS,
                 FSTCART_PASTECART, SNDCART_PASTECART] THEN
    ASM SET_TAC [])

  let FACE_OF_POLYTOPE_POLYTOPE ← prove
   r"!f s:real^N->bool. polytope s /\ f face_of s ==> polytope f"
   (REWRITE_TAC [polytope] THEN
    MESON_TAC [FINITE_SUBSET, FACE_OF_CONVEX_HULL_SUBSET, FINITE_IMP_COMPACT])

  let FINITE_POLYTOPE_FACES ← prove
   r"!s:real^N->bool. polytope s ==> FINITE {f | f face_of s}"
   (GEN_TAC THEN REWRITE_TAC [polytope, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"v:real^N->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC (← q r"IMAGE ((hull) convex) {t:real^N->bool | t SUBSET v}") THEN
    ASM_SIMP_TAC [FINITE_POWERSET, FINITE_IMAGE] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC [FORALL_IN_GSPEC, IN_IMAGE, IN_ELIM_THM] THEN
    ASM_MESON_TAC [FACE_OF_CONVEX_HULL_SUBSET, FINITE_IMP_COMPACT])

  let FINITE_POLYTOPE_FACETS ← prove
   r"!s:real^N->bool. polytope s ==> FINITE {f | f facet_of s}"
   (REWRITE_TAC [facet_of] THEN ONCE_REWRITE_TAC [← SET_RULE
     (← q r"{x | P x /\ Q x} = {x | x IN {x | P x} /\ Q x}")] THEN
    SIMP_TAC [FINITE_RESTRICT, FINITE_POLYTOPE_FACES])

  let POLYTOPE_INTERVAL ← prove
   r"!a b. polytope(interval[a,b])"
   (REWRITE_TAC [polytope] THEN MESON_TAC [CLOSED_INTERVAL_AS_CONVEX_HULL])

  let POLYTOPE_SING ← prove
   r"!a. polytope {a}"
   (MESON_TAC [POLYTOPE_INTERVAL, INTERVAL_SING])

  let POLYTOPE_SCALING ← prove
   r"!c s:real^N->bool. polytope s ==> polytope (IMAGE (\x. c % x) s)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [polytope] THEN DISCH_THEN
     (X_CHOOSE_THEN (← q r"u:real^N->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"IMAGE (\x:real^N. c % x) u") THEN
    ASM_SIMP_TAC [CONVEX_HULL_SCALING, FINITE_IMAGE])

  let POLYTOPE_SCALING_EQ ← prove
   r"!s:real^N->bool c.
        polytope (IMAGE (\x. c % x) s) <=> c = &0 \/ polytope s"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"c = &0") THEN ASM_REWRITE_TAC [] THENL
     [REWRITE_TAC [IMAGE_CONST, VECTOR_MUL_LZERO] THEN
      MESON_TAC [POLYTOPE_SING, POLYTOPE_EMPTY],
      EQ_TAC THEN REWRITE_TAC [POLYTOPE_SCALING] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"inv(c):real") o MATCH_MP POLYTOPE_SCALING) THEN
      REWRITE_TAC [← GSYM IMAGE_o, o_DEF, VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC [REAL_MUL_LINV, VECTOR_MUL_LID, IMAGE_ID]])

  let POLYTOPE_AFFINITY_EQ ← prove
   r"!s m c:real^N.
        polytope (IMAGE (\x. m % x + c) s) <=> m = &0 \/ polytope s"
   (REWRITE_TAC [AFFINITY_SCALING_TRANSLATION, POLYTOPE_TRANSLATION_EQ,
                 POLYTOPE_SCALING_EQ, IMAGE_o])

  let POLYTOPE_AFFINITY ← prove
   r"!s m c:real^N. polytope s ==> polytope (IMAGE (\x. m % x + c) s)"
   (SIMP_TAC [POLYTOPE_AFFINITY_EQ])

  let POLYTOPE_SUMS ← prove
   r"!s t:real^N->bool.
        polytope s /\ polytope t ==> polytope {x + y | x IN s /\ y IN t}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [polytope] THEN DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_THEN (← q r"u:real^N->bool") STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN (← q r"v:real^N->bool") STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC (← q r"{x + y:real^N | x IN u /\ y IN v}") THEN
    ASM_SIMP_TAC [FINITE_PRODUCT_DEPENDENT, CONVEX_HULL_SUMS])

  let POLYTOPE_IMP_COMPACT ← prove
   r"!s. polytope s ==> compact s"
   (SIMP_TAC [polytope, LEFT_IMP_EXISTS_THM, COMPACT_CONVEX_HULL,
              FINITE_IMP_COMPACT, FINITE_INSERT, FINITE_EMPTY])

  let POLYTOPE_IMP_CONVEX ← prove
   r"!s. polytope s ==> convex s"
   (SIMP_TAC [polytope, LEFT_IMP_EXISTS_THM, CONVEX_CONVEX_HULL])

  let POLYTOPE_IMP_CLOSED ← prove
   r"!s. polytope s ==> closed s"
   (SIMP_TAC [POLYTOPE_IMP_COMPACT, COMPACT_IMP_CLOSED])

  let POLYTOPE_IMP_BOUNDED ← prove
   r"!s. polytope s ==> bounded s"
   (SIMP_TAC [POLYTOPE_IMP_COMPACT, COMPACT_IMP_BOUNDED])

  let POLYTOPE_1 ← prove
   r"!s:real^1->bool. polytope s <=> ?a b. s = interval[a,b]"
   (MESON_TAC [IS_INTERVAL_COMPACT, POLYTOPE_IMP_COMPACT, POLYTOPE_IMP_CONVEX,
               IS_INTERVAL_CONVEX_1, POLYTOPE_INTERVAL])

  let POLYTOPE_AFF_DIM_1 ← prove
   r"!p:real^N->bool.
        polytope p /\ aff_dim p = &1 <=> ?a b. ~(a = b) /\ p = segment[a,b]"
   (GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [POLYTOPE_SEGMENT, AFF_DIM_SEGMENT] THEN
    MP_TAC (← ISPEC (← q r"p:real^N->bool") COMPACT_CONVEX_COLLINEAR_SEGMENT) THEN
    ASM_SIMP_TAC [COLLINEAR_AFF_DIM, INT_LE_REFL] THEN
    ASM_SIMP_TAC [POLYTOPE_IMP_COMPACT, POLYTOPE_IMP_CONVEX] THEN
    UNDISCH_TAC (← q r"aff_dim(p:real^N->bool) = &1") THEN
    ASM_CASES_TAC (← q r"p:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [AFF_DIM_EMPTY] THEN CONV_TAC INT_REDUCE_CONV THEN
    DISCH_TAC THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:real^N") THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"b:real^N") THEN
    ASM_CASES_TAC (← q r"a:real^N = b") THEN ASM_REWRITE_TAC [SEGMENT_REFL] THEN
    ASM_MESON_TAC [AFF_DIM_SING, ← INT_ARITH (← q r"~(&1:int = &0)")])

  let FACE_OF_POLYTOPE_INSERT_EQ ← prove
   r"!f s a:real^N.
         polytope s /\ ~(a IN affine hull s)
         ==> (f face_of convex hull (a INSERT s) <=>
              f face_of s \/
              (?f'. f' face_of s /\ f = convex hull (a INSERT f')))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [IMP_CONJ, polytope] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"c:real^N->bool") STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [AFFINE_HULL_CONVEX_HULL] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC [← SET_RULE (← q r"z INSERT i = {z} UNION i")] THEN
    REWRITE_TAC [← GSYM HULL_UNION_RIGHT] THEN
    REWRITE_TAC [← SET_RULE (← q r"{z} UNION i = z INSERT i")] THEN
    MP_TAC (← ISPECL [← q r"f:real^N->bool", ← q r"c:real^N->bool", ← q r"a:real^N"]
          FACE_OF_CONVEX_HULL_INSERT_EQ) THEN
    ASM_SIMP_TAC [])

  /- ----------------------------------------------------------------------- -/
  /- Approximation of bounded convex sets by polytopes.                      -/
  /- ----------------------------------------------------------------------- -/

  let CONVEX_INNER_APPROXIMATION ← prove
   r"!s:real^N->bool e.
        bounded s /\ convex s /\ &0 < e
        ==> ?k. FINITE k /\ convex hull k SUBSET s /\
                hausdist(convex hull k,s) < e /\
                (k = {} ==> s = {})"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"s:real^N->bool = {}") THENL
     [EXISTS_TAC (← q r"{}:real^N->bool") THEN
      ASM_SIMP_TAC [FINITE_EMPTY, CONVEX_HULL_EMPTY, HAUSDIST_REFL, SUBSET_REFL],
      ALL_TAC] THEN
    MP_TAC (← ISPEC (← q r"closure s:real^N->bool") COMPACT_EQ_HEINE_BOREL) THEN
    ASM_REWRITE_TAC [COMPACT_CLOSURE] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"{ball(x:real^N,e / &2) | x IN s}")) THEN
    REWRITE_TAC [FORALL_IN_GSPEC, OPEN_BALL] THEN ANTS_TAC THENL
     [REWRITE_TAC [SUBSET, UNIONS_GSPEC, IN_ELIM_THM, CLOSURE_APPROACHABLE] THEN
      X_GEN_TAC (← q r"x:real^N") THEN DISCH_THEN (MP_TAC o SPEC (← q r"e / &2")) THEN
      ASM_REWRITE_TAC [IN_BALL, REAL_HALF],
      ONCE_REWRITE_TAC [← TAUT (← q r"p /\ q /\ r <=> q /\ p /\ r")] THEN
      REWRITE_TAC [SIMPLE_IMAGE, EXISTS_FINITE_SUBSET_IMAGE]] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"k:real^N->bool") THEN
    ASM_CASES_TAC (← q r"k:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [IMAGE_CLAUSES, UNIONS_0, SUBSET_EMPTY, CLOSURE_EQ_EMPTY] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [HULL_MINIMAL], DISCH_TAC] THEN
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← REAL_ARITH
     (← q r"&0 < e ==> x <= e / &2 ==> x < e"))) THEN
    MATCH_MP_TAC REAL_HAUSDIST_LE THEN
    ASM_REWRITE_TAC [CONVEX_HULL_EQ_EMPTY] THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC (REWRITE_RULE [SUBSET]) THEN
      ASM_SIMP_TAC [SETDIST_SING_IN_SET] THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN UNDISCH_TAC
     (← q r"closure s SUBSET UNIONS (IMAGE (\x:real^N. ball (x,e / &2)) k)") THEN
    REWRITE_TAC [SUBSET] THEN DISCH_THEN (MP_TAC o SPEC (← q r"x:real^N")) THEN
    ASM_SIMP_TAC [← REWRITE_RULE [SUBSET] CLOSURE_SUBSET] THEN
    REWRITE_TAC [UNIONS_IMAGE, IN_ELIM_THM, IN_BALL] THEN
    ONCE_REWRITE_TAC [DIST_SYM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"y:real^N") STRIP_ASSUME_TAC) THEN
    TRANS_TAC REAL_LE_TRANS (← q r"dist(x:real^N,y)") THEN
    ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN MATCH_MP_TAC SETDIST_LE_DIST THEN
    ASM_SIMP_TAC [IN_SING, HULL_INC])

  let CONVEX_OUTER_APPROXIMATION ← prove
   r"!s:real^N->bool e.
        bounded s /\ convex s /\ &0 < e
        ==> ?k. FINITE k /\ s SUBSET convex hull k /\
                hausdist(convex hull k,s) < e"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"s:real^N->bool = {}") THENL
     [EXISTS_TAC (← q r"{}:real^N->bool") THEN
      ASM_REWRITE_TAC [FINITE_EMPTY, EMPTY_SUBSET, HAUSDIST_EMPTY,
                       CONVEX_HULL_EMPTY],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"{x + y:real^N | x IN s /\ y IN ball(vec 0,e / &2)}",
                      ← q r"e / &2"] CONVEX_INNER_APPROXIMATION) THEN
    ASM_SIMP_TAC [CONVEX_SUMS, CONVEX_BALL, BOUNDED_SUMS, BOUNDED_BALL] THEN
    ASM_REWRITE_TAC [REAL_HALF, BALL_EQ_EMPTY, ← GSYM REAL_NOT_LT, ← SET_RULE
     (← q r"{f x y | x IN s /\ y IN t} = {} <=> s = {} \/ t = {}")] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"k:real^N->bool") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP (← REWRITE_RULE [REAL_NOT_LE]
     (← ONCE_REWRITE_RULE [← GSYM CONTRAPOS_THM] REAL_LE_HAUSDIST))) THEN
    REWRITE_TAC [← TAUT (← q r"~(p /\ q) <=> p ==> ~q"), RIGHT_FORALL_IMP_THM] THEN
    ASM_REWRITE_TAC [CONVEX_HULL_EQ_EMPTY, LEFT_FORALL_IMP_THM] THEN
    ASM_REWRITE_TAC [REAL_HALF, BALL_EQ_EMPTY, ← GSYM REAL_NOT_LT, ← SET_RULE
     (← q r"{f x y | x IN s /\ y IN t} = {} <=> s = {} \/ t = {}")] THEN
    REWRITE_TAC [DE_MORGAN_THM, REAL_NOT_LT, FORALL_AND_THM] THEN ANTS_TAC THENL
     [EXISTS_TAC (← q r"hausdist(convex hull k,
                        {x + y:real^N | x IN s /\ y IN ball(vec 0,e / &2)})") THEN
      X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      MATCH_MP_TAC SETDIST_SING_LE_HAUSDIST THEN
      ASM_SIMP_TAC [BOUNDED_CONVEX_HULL, FINITE_IMP_BOUNDED] THEN
      ASM_SIMP_TAC [BOUNDED_SUMS, BOUNDED_BALL],
      ALL_TAC] THEN
    ANTS_TAC THENL
     [EXISTS_TAC (← q r"hausdist(convex hull k,
                        {x + y:real^N | x IN s /\ y IN ball(vec 0,e / &2)})") THEN
      X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC [HAUSDIST_SYM] THEN
      MATCH_MP_TAC SETDIST_SING_LE_HAUSDIST THEN
      ASM_SIMP_TAC [BOUNDED_CONVEX_HULL, FINITE_IMP_BOUNDED] THEN
      ASM_SIMP_TAC [BOUNDED_SUMS, BOUNDED_BALL],
      REWRITE_TAC [← TAUT (← q r"~p \/ q <=> p ==> q")] THEN DISCH_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_SUMS_RCANCEL THEN
      EXISTS_TAC (← q r"ball(vec 0:real^N,e / &2)") THEN
      ASM_SIMP_TAC [COMPACT_IMP_CLOSED, COMPACT_CONVEX_HULL, FINITE_IMP_COMPACT,
        CONVEX_CONVEX_HULL, BALL_EQ_EMPTY, BOUNDED_BALL, REAL_NOT_LE] THEN
      ASM_REWRITE_TAC [REAL_HALF, SUBSET] THEN X_GEN_TAC (← q r"z:real^N") THEN
      DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"z:real^N") o CONJUNCT2) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o MATCH_MP
       (← ONCE_REWRITE_RULE [IMP_CONJ_ALT] (← REWRITE_RULE [CONJ_ASSOC]
          REAL_SETDIST_LT_EXISTS))) THEN
      ASM_REWRITE_TAC [NOT_INSERT_EMPTY, CONVEX_HULL_EQ_EMPTY, IN_SING] THEN
      REWRITE_TAC [IN_BALL_0, IN_ELIM_THM, ← GSYM CONJ_ASSOC] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM2] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"y:real^N") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"z - y:real^N") THEN
      ASM_REWRITE_TAC [← GSYM dist] THEN CONV_TAC (fun t => VECTOR_ARITH t),
      FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← REAL_ARITH
       (← q r"&0 < e ==> x <= e / &2 ==> x < e"))) THEN
      MATCH_MP_TAC REAL_HAUSDIST_LE THEN
      ASM_REWRITE_TAC [CONVEX_HULL_EQ_EMPTY] THEN CONJ_TAC THENL
       [X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"x:real^N")) THEN
        ASM_REWRITE_TAC [IN_ELIM_THM] THEN ONCE_REWRITE_TAC [CONJ_SYM] THEN
        REWRITE_TAC [← VECTOR_ARITH (← q r"x:real^N = z + y <=> x - z = y")] THEN
        REWRITE_TAC [UNWIND_THM1, IN_BALL_0, ← GSYM dist] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"y:real^N") STRIP_ASSUME_TAC) THEN
        TRANS_TAC REAL_LE_TRANS (← q r"dist(x:real^N,y)") THEN
        ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN MATCH_MP_TAC SETDIST_LE_DIST THEN
        ASM_REWRITE_TAC [IN_SING],
        X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real^N") o CONJUNCT2) THEN
        ANTS_TAC THENL [ALL_TAC, REWRITE_TAC [REAL_LT_IMP_LE]] THEN
        REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC (← q r"x:real^N") THEN
        EXISTS_TAC (← q r"vec 0:real^N") THEN ASM_REWRITE_TAC [CENTRE_IN_BALL] THEN
        ASM_REWRITE_TAC [REAL_HALF, VECTOR_ADD_RID]]])

  let CONVEX_INNER_POLYTOPE ← prove
   r"!s:real^N->bool e.
        bounded s /\ convex s /\ &0 < e
        ==> ?p. polytope p /\ p SUBSET s /\ hausdist(p,s) < e /\
                (p = {} ==> s = {})"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q r"k:real^N->bool") STRIP_ASSUME_TAC o
          MATCH_MP CONVEX_INNER_APPROXIMATION) THEN
    EXISTS_TAC (← q r"convex hull k:real^N->bool") THEN
    ASM_SIMP_TAC [CONVEX_HULL_EQ_EMPTY, POLYTOPE_CONVEX_HULL])

  let CONVEX_OUTER_POLYTOPE ← prove
   r"!s:real^N->bool e.
        bounded s /\ convex s /\ &0 < e
        ==> ?p. polytope p /\ s SUBSET p /\ hausdist(p,s) < e"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q r"k:real^N->bool") STRIP_ASSUME_TAC o
          MATCH_MP CONVEX_OUTER_APPROXIMATION) THEN
    EXISTS_TAC (← q r"convex hull k:real^N->bool") THEN
    ASM_SIMP_TAC [CONVEX_HULL_EQ_EMPTY, POLYTOPE_CONVEX_HULL])

  /- ----------------------------------------------------------------------- -/
  /- Polyhedra.                                                              -/
  /- ----------------------------------------------------------------------- -/

  let polyhedron ← new_definition
   r"polyhedron s <=>
        ?f. FINITE f /\
            s = INTERS f /\
            (!h. h IN f ==> ?a b. ~(a = vec 0) /\ h = {x | a dot x <= b})"

  let POLYHEDRON_INTER ← prove
   r"!s t:real^N->bool.
        polyhedron s /\ polyhedron t ==> polyhedron (s INTER t)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [polyhedron] THEN
    DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_TAC (← q r"f:(real^N->bool)->bool"))
     (X_CHOOSE_TAC (← q r"g:(real^N->bool)->bool"))) THEN
    EXISTS_TAC (← q r"f UNION g:(real^N->bool)->bool") THEN
    ASM_REWRITE_TAC [← SET_RULE (← q r"INTERS(f UNION g) = INTERS f INTER INTERS g")] THEN
    REWRITE_TAC [FINITE_UNION, IN_UNION] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [])

  let POLYHEDRON_UNIV ← prove
   r"polyhedron(:real^N)"
   (REWRITE_TAC [polyhedron] THEN EXISTS_TAC (← q r"{}:(real^N->bool)->bool") THEN
    REWRITE_TAC [INTERS_0, NOT_IN_EMPTY, FINITE_RULES])

  let POLYHEDRON_POSITIVE_ORTHANT ← prove
   r"polyhedron {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= x$i}"
   (REWRITE_TAC [polyhedron] THEN
    EXISTS_TAC (← q r"IMAGE (\i. {x:real^N | &0 <= x$i}) (1..dimindex(:N))") THEN
    SIMP_TAC [FINITE_IMAGE, FINITE_NUMSEG, FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC [INTERS_IMAGE] THEN
      REWRITE_TAC [IN_ELIM_THM, IN_NUMSEG],
      X_GEN_TAC (← q r"k:num") THEN REWRITE_TAC [IN_NUMSEG] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [← q r"--basis k:real^N", ← q r"&0"] THEN
      ASM_SIMP_TAC [VECTOR_NEG_EQ_0, DOT_LNEG, DOT_BASIS, BASIS_NONZERO] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"--x <= &0 <=> &0 <= x")]])

  let POLYHEDRON_INTERS ← prove
   r"!f:(real^N->bool)->bool.
        FINITE f /\ (!s. s IN f ==> polyhedron s) ==> polyhedron(INTERS f)"
   (REWRITE_TAC [IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [NOT_IN_EMPTY, INTERS_0, POLYHEDRON_UNIV] THEN
    ASM_SIMP_TAC [INTERS_INSERT, FORALL_IN_INSERT, POLYHEDRON_INTER])

  let POLYHEDRON_EMPTY ← prove
   r"polyhedron({}:real^N->bool)"
   (REWRITE_TAC [polyhedron] THEN
    EXISTS_TAC (← q r"{{x:real^N | basis 1 dot x <= -- &1},
                 {x | --(basis 1) dot x <= -- &1}}") THEN
    REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY, INTERS_2, FORALL_IN_INSERT] THEN
    REWRITE_TAC [NOT_IN_EMPTY, INTER, IN_ELIM_THM, DOT_LNEG] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"~(a <= -- &1 /\ --a <= -- &1)"), EMPTY_GSPEC] THEN
    CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [← q r"basis 1:real^N", ← q r"-- &1"],
      MAP_EVERY EXISTS_TAC [← q r"--(basis 1):real^N", ← q r"-- &1"]] THEN
    SIMP_TAC [VECTOR_NEG_EQ_0, BASIS_NONZERO, DOT_LNEG,
              DIMINDEX_GE_1, LE_REFL])

  let POLYHEDRON_HALFSPACE_LE ← prove
   r"!a b. polyhedron {x:real^N | a dot x <= b}"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"a:real^N = vec 0") THENL
     [ASM_SIMP_TAC [DOT_LZERO, ← SET_RULE (← q r"{x | p} = if p then UNIV else {}")] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [POLYHEDRON_EMPTY, POLYHEDRON_UNIV],
      REWRITE_TAC [polyhedron] THEN EXISTS_TAC (← q r"{{x:real^N | a dot x <= b}}") THEN
      REWRITE_TAC [FINITE_SING, INTERS_1, FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
      MAP_EVERY EXISTS_TAC [← q r"a:real^N", ← q r"b:real"] THEN ASM_REWRITE_TAC []])

  let POLYHEDRON_HALFSPACE_GE ← prove
   r"!a b. polyhedron {x:real^N | a dot x >= b}"
   (REWRITE_TAC [← REAL_ARITH (← q r"a:real >= b <=> --a <= --b")] THEN
    REWRITE_TAC [← GSYM DOT_LNEG, POLYHEDRON_HALFSPACE_LE])

  let POLYHEDRON_HYPERPLANE ← prove
   r"!a b. polyhedron {x:real^N | a dot x = b}"
   (REWRITE_TAC [← REAL_ARITH (← q r"x:real = b <=> x <= b /\ x >= b")] THEN
    REWRITE_TAC [← SET_RULE (← q r"{x | P x /\ Q x} = {x | P x} INTER {x | Q x}")] THEN
    SIMP_TAC [POLYHEDRON_INTER, POLYHEDRON_HALFSPACE_LE,
              POLYHEDRON_HALFSPACE_GE])

  let AFFINE_IMP_POLYHEDRON ← prove
   r"!s:real^N->bool. affine s ==> polyhedron s"
   (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"s:real^N->bool")
      AFFINE_HULL_FINITE_INTERSECTION_HYPERPLANES) THEN
    ASM_SIMP_TAC [HULL_P, RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN
    STRIP_TAC THEN ASM_SIMP_TAC [] THEN
    MATCH_MP_TAC POLYHEDRON_INTERS THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"h:real^N->bool") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"h:real^N->bool")) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT2) THEN
    REWRITE_TAC [POLYHEDRON_HYPERPLANE])

  let POLYHEDRON_IMP_CLOSED ← prove
   r"!s:real^N->bool. polyhedron s ==> closed s"
   (REWRITE_TAC [polyhedron, RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC CLOSED_INTERS THEN
    X_GEN_TAC (← q r"h:real^N->bool") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"h:real^N->bool")) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT2) THEN
    REWRITE_TAC [CLOSED_HALFSPACE_LE])

  let POLYHEDRON_IMP_CONVEX ← prove
   r"!s:real^N->bool. polyhedron s ==> convex s"
   (REWRITE_TAC [polyhedron, RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC CONVEX_INTERS THEN
    X_GEN_TAC (← q r"h:real^N->bool") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"h:real^N->bool")) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT2) THEN
    REWRITE_TAC [CONVEX_HALFSPACE_LE])

  let POLYHEDRON_AFFINE_HULL ← prove
   r"!s. polyhedron(affine hull s)"
   (SIMP_TAC [AFFINE_IMP_POLYHEDRON, AFFINE_AFFINE_HULL])

  pure { polytope, POLYTOPE_TRANSLATION_EQ, POLYTOPE_LINEAR_IMAGE, POLYTOPE_LINEAR_IMAGE_EQ,
         POLYTOPE_EMPTY, POLYTOPE_NEGATIONS, POLYTOPE_CONVEX_HULL, POLYTOPE_SEGMENT,
         POLYTOPE_PCROSS, POLYTOPE_PCROSS_EQ, FACE_OF_POLYTOPE_POLYTOPE,
         FINITE_POLYTOPE_FACES, FINITE_POLYTOPE_FACETS, POLYTOPE_INTERVAL, POLYTOPE_SING,
         POLYTOPE_SCALING, POLYTOPE_SCALING_EQ, POLYTOPE_AFFINITY_EQ, POLYTOPE_AFFINITY,
         POLYTOPE_SUMS, POLYTOPE_IMP_COMPACT, POLYTOPE_IMP_CONVEX, POLYTOPE_IMP_CLOSED,
         POLYTOPE_IMP_BOUNDED, POLYTOPE_1, POLYTOPE_AFF_DIM_1, FACE_OF_POLYTOPE_INSERT_EQ,
         CONVEX_INNER_APPROXIMATION, CONVEX_OUTER_APPROXIMATION, CONVEX_INNER_POLYTOPE,
         CONVEX_OUTER_POLYTOPE, polyhedron, POLYHEDRON_INTER, POLYHEDRON_UNIV,
         POLYHEDRON_POSITIVE_ORTHANT, POLYHEDRON_INTERS, POLYHEDRON_EMPTY,
         POLYHEDRON_HALFSPACE_LE, POLYHEDRON_HALFSPACE_GE, POLYHEDRON_HYPERPLANE,
         AFFINE_IMP_POLYHEDRON, POLYHEDRON_IMP_CLOSED, POLYHEDRON_IMP_CONVEX,
         POLYHEDRON_AFFINE_HULL }

/- ------------------------------------------------------------------------- -/
/- Canonical polyedron representation making facial structure explicit.     -/
/- (polytope.ml 4499-5187)                                                   -/
/- ------------------------------------------------------------------------- -/

structure POK where
  POLYHEDRON_INTER_AFFINE : thm
  POLYHEDRON_INTER_AFFINE_PARALLEL : thm
  POLYHEDRON_INTER_AFFINE_PARALLEL_MINIMAL : thm
  POLYHEDRON_INTER_AFFINE_MINIMAL : thm
  RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT : thm
  FACET_OF_POLYHEDRON_EXPLICIT : thm
  FACE_OF_POLYHEDRON_SUBSET_EXPLICIT : thm
  FACE_OF_POLYHEDRON_EXPLICIT : thm
  deriving Inhabited

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 2048 in
@[nospecialize]
def setupPOK [HolBase] (D : PolytopeDeps) (BPOA : POA) (BPOB : POB) (BPOG : POG) (BPOJ : POJ) : ExceptT String IO POK := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INT_ARITH, MESON, MESON_TAC, REAL_ARITH,
        REAL_ARITH_TAC, REAL_FIELD, REAL_RAT_REDUCE_CONV, REAL_RING, SET_RULE, SET_TAC,
        VECTOR_ARITH, VECTOR_ARITH_TAC, .. } := D.cvx
  let { CARD_PSUBSET, COND_ID, COND_RAND, COND_RATOR, CONTRAPOS_THM, DISJOINT,
        EXISTS_IN_GSPEC, EXISTS_IN_IMAGE, EXTENSION, FINITE_DELETE, FINITE_EMPTY,
        FINITE_IMAGE, FINITE_RESTRICT, FINITE_SUBSET, FORALL_IN_GSPEC, .. } := D.cvx.core1
  let { FORALL_IN_IMAGE, HAS_SIZE, IMAGE_EQ_EMPTY, IN_DELETE, INTER_EMPTY, INTER_UNIV,
        INTERS_0, INTERS_2, INTERS_IMAGE, INTERS_INSERT, .. } := D.cvx.core2
  let { IN_ELIM_THM, IN_INTER, IN_INTERS, LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY,
        MONO_EXISTS, NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, PSUBSET,
        REAL_ABS_NEG, REAL_DIV_RMUL, .. } := D.cvx.core3
  let { REAL_EQ_IMP_LE, REAL_INF_LE_FINITE, REAL_LE_LMUL_EQ, REAL_LE_LT, REAL_LE_MUL_EQ,
        REAL_LE_RDIV_EQ, REAL_LE_REFL, REAL_LT_01, REAL_LT_DIV, REAL_LT_IMP_LE,
        REAL_LT_IMP_NE, REAL_LT_IMP_NZ, REAL_LT_INF_FINITE, REAL_LT_INV_EQ, REAL_LT_LDIV_EQ,
        REAL_LT_LMUL_EQ, REAL_LT_MIN, REAL_LT_RADD, REAL_LT_RDIV_EQ, REAL_LT_REFL,
        REAL_LTE_TRANS, REAL_MIN_LT, .. } := D.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LINV, REAL_MUL_RNEG, REAL_SUB_0, REAL_SUB_LT,
        RIGHT_IMP_EXISTS_THM, SIMPLE_IMAGE, SIMPLE_IMAGE_GEN, SKOLEM_THM, SUBSET,
        SUBSET_ANTISYM, SUBSET_INTER, .. } := D.cvx.core5
  let { num_WOP, real_div, real_gt, .. } := D.cvx.core6
  let { HULL_INC, HULL_MINIMAL, HULL_MONO, HULL_SUBSET, REAL_HALF, .. } := D.cvx.misc
  let { DOT_RADD, DOT_RMUL, DOT_RSUB, .. } := D.cvx.vec1
  let { NORM_MUL, NORM_POS_LT, .. } := D.cvx.vec3
  let { dist, VECTOR_ADD_LDISTRIB, VECTOR_ADD_SYM, VECTOR_MUL_ASSOC, VECTOR_SUB_EQ, .. } :=
        D.cvx.vec4
  let { IN_BALL, INTERIOR_SUBSET, OPEN_CONTAINS_BALL, .. } := D.cvx.top4
  let { OPEN_HALFSPACE_LT, OPEN_INTERIOR, .. } := D.cvx.top5
  let { INT_LT_REFL, PSUBSET_ALT, REAL_LT_RCANCEL_IMP, REAL_LT_RMUL, .. } := D.qses
  let { INTERIOR_HALFSPACE_LE, OPEN_INTERS, .. } := D.qtop
  let { AFF_DIM_AFFINE_HULL, AFF_DIM_AFFINE_INTER_HYPERPLANE, AFFINE_AFFINE_HULL,
        AFFINE_ALT, AFFINE_HULL_EMPTY, AFFINE_HULL_EQ, AFFINE_HYPERPLANE,
        AFFINE_PARALLEL_SLICE, .. } := D.qcvx1
  let { CONVEX_ALT, CONVEX_HALFSPACE_LE, CONVEX_HYPERPLANE, CONVEX_INTER, .. } := D.qcvx2
  let { IN_RELATIVE_INTERIOR, RELATIVE_INTERIOR, RELATIVE_INTERIOR_EQ_EMPTY,
        RELATIVE_INTERIOR_SUBSET, .. } := D.qcvx3
  let { FACE_OF_AFF_DIM_LT, FACE_OF_EQ, FACE_OF_FACE, FACE_OF_IMP_CONVEX,
        FACE_OF_IMP_SUBSET, FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE, FACE_OF_INTERS,
        FACE_OF_REFL, SUBSET_OF_FACE_OF, .. } := BPOA
  let { FACE_OF_AFFINE_TRIVIAL, .. } := BPOB
  let { facet_of, FACET_OF_EMPTY, .. } := BPOG
  let { polyhedron, POLYHEDRON_AFFINE_HULL, POLYHEDRON_HALFSPACE_LE, POLYHEDRON_IMP_CONVEX,
        POLYHEDRON_INTER, POLYHEDRON_INTERS, .. } := BPOJ
  -- @@SCOPE END

  let POLYHEDRON_INTER_AFFINE ← prove
   r"!s. polyhedron s <=>
        ?f. FINITE f /\
            s = (affine hull s) INTER (INTERS f) /\
            (!h. h IN f
                 ==> ?a b. ~(a = vec 0) /\ h = {x:real^N | a dot x <= b})"
   (GEN_TAC THEN EQ_TAC THENL
     [REWRITE_TAC [polyhedron] THEN MATCH_MP_TAC MONO_EXISTS THEN
      GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
      TRY (FIRST_ASSUM ACCEPT_TAC) THEN
      MATCH_MP_TAC (← SET_RULE (← q r"s = t /\ s SUBSET u ==> s = u INTER t")) THEN
      REWRITE_TAC [HULL_SUBSET] THEN ASM_REWRITE_TAC [],
      STRIP_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC POLYHEDRON_INTER THEN REWRITE_TAC [POLYHEDRON_AFFINE_HULL] THEN
      MATCH_MP_TAC POLYHEDRON_INTERS THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [POLYHEDRON_HALFSPACE_LE]])

  let POLYHEDRON_INTER_AFFINE_PARALLEL ← prove
   r"!s:real^N->bool.
        polyhedron s <=>
        ?f. FINITE f /\
            s = (affine hull s) INTER (INTERS f) /\
            (!h. h IN f
                 ==> ?a b. ~(a = vec 0) /\ h = {x:real^N | a dot x <= b} /\
                           (!x. x IN affine hull s
                                ==> (x + a) IN affine hull s))"
   (GEN_TAC THEN REWRITE_TAC [POLYHEDRON_INTER_AFFINE] THEN EQ_TAC THENL
     [ALL_TAC, MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC []] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"f:(real^N->bool)->bool") MP_TAC) THEN
    ASM_CASES_TAC (← q r"s:real^N->bool = {}") THENL
     [DISCH_THEN (K ALL_TAC : thm → tactic) THEN EXISTS_TAC (← q r"{}:(real^N->bool)->bool") THEN
      ASM_SIMP_TAC [AFFINE_HULL_EMPTY, INTER_EMPTY, NOT_IN_EMPTY, FINITE_EMPTY],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"f:(real^N->bool)->bool = {}") THENL
     [ASM_REWRITE_TAC [NOT_IN_EMPTY, INTERS_0, INTER_UNIV] THEN
      DISCH_THEN (ASSUME_TAC o SYM o CONJUNCT2) THEN
      EXISTS_TAC (← q r"{}:(real^N->bool)->bool") THEN
      ASM_REWRITE_TAC [NOT_IN_EMPTY, INTERS_0, INTER_UNIV, FINITE_EMPTY],
      ALL_TAC] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 (ASSUME_TAC o GSYM) MP_TAC)) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM, SKOLEM_THM] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"a:(real^N->bool)->real^N", ← q r"b:(real^N->bool)->real"] THEN
    DISCH_THEN (ASSUME_TAC o GSYM) THEN
    SUBGOAL_THEN
     (← q r"!h. h IN f /\ ~(affine hull s SUBSET h)
          ==> ?a' b'. ~(a' = vec 0) /\
                    affine hull s INTER {x:real^N | a' dot x <= b'} =
                    affine hull s INTER h /\
                    !w. w IN affine hull s ==> (w + a') IN affine hull s")
    MP_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o SPEC (← q r"h:real^N->bool")) THEN
      REWRITE_TAC [← ASSUME (← q r"(h:real^N->bool) IN f")] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC o GSYM) THEN
      MP_TAC (← ISPECL [← q r"affine hull s:real^N->bool",
                        ← q r"(a:(real^N->bool)->real^N) h",
                        ← q r"(b:(real^N->bool)->real) h"]
                  AFFINE_PARALLEL_SLICE) THEN
      REWRITE_TAC [AFFINE_AFFINE_HULL] THEN MATCH_MP_TAC (← TAUT
       (← q r"~p /\ ~q /\ (r ==> r') ==> (p \/ q \/ r ==> r')")) THEN
      ASM_SIMP_TAC [] THEN CONJ_TAC THENL [ALL_TAC, MESON_TAC []] THEN
      DISCH_TAC THEN
      UNDISCH_TAC (← q r"~(s:real^N->bool = {})") THEN
      EXPAND_TAC "s" THEN REWRITE_TAC [← GSYM INTERS_INSERT] THEN
      MATCH_MP_TAC (← SET_RULE
       (← q r"!t. t SUBSET s /\ INTERS t = {} ==> INTERS s = {}")) THEN
      EXISTS_TAC (← q r"{affine hull s,h:real^N->bool}") THEN
      ASM_REWRITE_TAC [INTERS_2] THEN ASM SET_TAC [],
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
    FIRST_X_ASSUM ((K ALL_TAC : thm → tactic) o SPEC (← q r"{}:real^N->bool")) THEN
    MAP_EVERY X_GEN_TAC
      [← q r"a:(real^N->bool)->real^N", ← q r"b:(real^N->bool)->real"] THEN
    DISCH_TAC THEN
    EXISTS_TAC (← q r"IMAGE (\h:real^N->bool. {x:real^N | a h dot x <= b h})
                      {h | h IN f /\ ~(affine hull s SUBSET h)}") THEN
    ASM_SIMP_TAC [FINITE_IMAGE, FINITE_RESTRICT, FORALL_IN_IMAGE] THEN
    REWRITE_TAC [FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [ALL_TAC,
      X_GEN_TAC (← q r"h:real^N->bool") THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC
       [← q r"(a:(real^N->bool)->real^N) h", ← q r"(b:(real^N->bool)->real) h"] THEN
      ASM_MESON_TAC []] THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      pure (GEN_REWRITE_TAC LAND_CONV [← GSYM th])) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC (← q r"x:real^N") THEN
    REWRITE_TAC [INTERS_IMAGE, IN_INTER, IN_ELIM_THM] THEN
    ASM_CASES_TAC (← q r"(x:real^N) IN affine hull s") THEN
    ASM_REWRITE_TAC [IN_INTERS] THEN AP_TERM_TAC THEN ABS_TAC THEN
    ASM SET_TAC [])

  let POLYHEDRON_INTER_AFFINE_PARALLEL_MINIMAL ← prove
   r"!s. polyhedron s <=>
        ?f. FINITE f /\
            s = (affine hull s) INTER (INTERS f) /\
            (!h. h IN f
                 ==> ?a b. ~(a = vec 0) /\ h = {x:real^N | a dot x <= b} /\
                           (!x. x IN affine hull s
                                ==> (x + a) IN affine hull s)) /\
            !f'. f' PSUBSET f ==> s PSUBSET (affine hull s) INTER (INTERS f')"
   (GEN_TAC THEN REWRITE_TAC [POLYHEDRON_INTER_AFFINE_PARALLEL] THEN
    EQ_TAC THENL [ALL_TAC, MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC []] THEN
    GEN_REWRITE_TAC LAND_CONV
     [← MESON [HAS_SIZE]
       (← q r"(?f. FINITE f /\ P f) <=> (?n f. f HAS_SIZE n /\ P f)")] THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC [HAS_SIZE] THEN
    X_GEN_TAC (← q r"f:(real^N->bool)->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
    X_GEN_TAC (← q r"f':(real^N->bool)->bool") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"CARD(f':(real^N->bool)->bool)")) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [CARD_PSUBSET], ALL_TAC] THEN
    REWRITE_TAC [NOT_EXISTS_THM, HAS_SIZE] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"f':(real^N->bool)->bool")) THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ c /\ (~b ==> d) ==> ~(a /\ b /\ c) ==> d")) THEN
    CONJ_TAC THENL [ASM_MESON_TAC [PSUBSET, FINITE_SUBSET], ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC [],
      MATCH_MP_TAC (← SET_RULE (← q r"s SUBSET t ==> ~(s = t) ==> s PSUBSET t")) THEN
      FIRST_X_ASSUM (fun th => GEN_REWRITE_TAC LAND_CONV [th]) THEN
      ASM SET_TAC []])

  let POLYHEDRON_INTER_AFFINE_MINIMAL ← prove
   r"!s. polyhedron s <=>
        ?f. FINITE f /\
            s = (affine hull s) INTER (INTERS f) /\
            (!h. h IN f
                 ==> ?a b. ~(a = vec 0) /\ h = {x:real^N | a dot x <= b}) /\
            !f'. f' PSUBSET f ==> s PSUBSET (affine hull s) INTER (INTERS f')"
   (GEN_TAC THEN EQ_TAC THENL
     [REWRITE_TAC [POLYHEDRON_INTER_AFFINE_PARALLEL_MINIMAL],
      REWRITE_TAC [POLYHEDRON_INTER_AFFINE]] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [] THEN MESON_TAC [])

  let RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT ← prove
   r"!s:real^N->bool f a b.
        FINITE f /\
        s = affine hull s INTER INTERS f /\
        (!h. h IN f ==> ~(a h = vec 0) /\ h = {x | a h dot x <= b h}) /\
        (!f'. f' PSUBSET f ==> s PSUBSET affine hull s INTER INTERS f')
        ==> relative_interior s =
                {x | x IN s /\ !h. h IN f ==> a h dot x < b h}"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"x:real^N") THEN EQ_TAC THENL
     [ALL_TAC,
      STRIP_TAC THEN ASM_REWRITE_TAC [RELATIVE_INTERIOR, IN_ELIM_THM] THEN
      EXISTS_TAC (← q r"INTERS {interior h | (h:real^N->bool) IN f}") THEN
      ASM_SIMP_TAC [SIMPLE_IMAGE, OPEN_INTERS, FINITE_IMAGE, OPEN_INTERIOR,
                    FORALL_IN_IMAGE, IN_INTERS] THEN
      CONJ_TAC THENL
       [X_GEN_TAC (← q r"h:real^N->bool") THEN DISCH_TAC THEN
        REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"h:real^N->bool"))) THEN
        ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN
        FIRST_ASSUM (SUBST1_TAC o CONJUNCT2) THEN
        ASM_SIMP_TAC [INTERIOR_HALFSPACE_LE, IN_ELIM_THM],
        FIRST_X_ASSUM (fun th => tactic_of do
          pure (GEN_REWRITE_TAC RAND_CONV [← SYM th])) THEN
        MATCH_MP_TAC (← SET_RULE
         (← q r"(!s. s IN f ==> i s SUBSET s)
          ==> INTERS (IMAGE i f) INTER t SUBSET t INTER INTERS f")) THEN
        REWRITE_TAC [INTERIOR_SUBSET]]] THEN
    DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [IN_RELATIVE_INTERIOR]) THEN
    DISCH_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"i:real^N->bool") THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"f DELETE (i:real^N->bool)")) THEN ANTS_TAC THENL
     [ASM SET_TAC [],
      REWRITE_TAC [PSUBSET_ALT, IN_INTER, IN_INTERS, IN_DELETE]] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"z:real^N") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"(a:(real^N->bool)->real^N) i dot z > b i") ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"~((z:real^N) IN s)") THEN
      FIRST_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [IN_INTER, IN_INTERS] THEN
      ASM_REWRITE_TAC [← REAL_ARITH (← q r"a:real > b <=> ~(a <= b)")] THEN ASM SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(z:real^N = x)") ASSUME_TAC THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"?l. &0 < l /\ l < &1 /\ (l % z + (&1 - l) % x:real^N) IN s")
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM (X_CHOOSE_THEN (← q r"e:real") MP_TAC o CONJUNCT2) THEN
      REWRITE_TAC [SUBSET, IN_INTER, IN_BALL, dist] THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"min (&1 / &2) (e / &2 / norm(z - x:real^N))") THEN
      REWRITE_TAC [REAL_MIN_LT, REAL_LT_MIN] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_SIMP_TAC [REAL_HALF, REAL_LT_DIV, NORM_POS_LT, VECTOR_SUB_EQ] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC [← VECTOR_ARITH
         (← q r"x - (l % z + (&1 - l) % x):real^N = --l % (z - x)")] THEN
        REWRITE_TAC [NORM_MUL, REAL_ABS_NEG] THEN
        ASM_SIMP_TAC [← GSYM REAL_LT_RDIV_EQ, NORM_POS_LT, VECTOR_SUB_EQ] THEN
        MATCH_MP_TAC (← REAL_ARITH
         (← q r"&0 < a /\ &0 < b /\ b < c ==> abs(min a b) < c")) THEN
        ASM_SIMP_TAC [REAL_HALF, REAL_LT_DIV, NORM_POS_LT, VECTOR_SUB_EQ] THEN
        REWRITE_TAC [REAL_LT_01, real_div, REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC REAL_LT_RMUL THEN
        ASM_REWRITE_TAC [REAL_LT_INV_EQ, NORM_POS_LT, VECTOR_SUB_EQ] THEN
        UNDISCH_TAC (← q r"&0 < e") THEN REAL_ARITH_TAC,
        ONCE_REWRITE_TAC [VECTOR_ADD_SYM] THEN
        MATCH_MP_TAC (← REWRITE_RULE [AFFINE_ALT] AFFINE_AFFINE_HULL) THEN
        ASM SET_TAC []],
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC (← q r"&1 - l") THEN
    ASM_REWRITE_TAC [REAL_SUB_LT] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"a < b * (&1 - l) <=> l * b + a < b")] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC
     (← q r"l * (a:(real^N->bool)->real^N) i dot z + (a i dot x) * (&1 - l)") THEN
    ASM_SIMP_TAC [REAL_LT_RADD, REAL_LT_LMUL_EQ, ← GSYM real_gt] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"a * (&1 - b) = (&1 - b) * a")] THEN
    REWRITE_TAC [← GSYM DOT_RMUL, ← GSYM DOT_RADD] THEN ASM SET_TAC [])

  let FACET_OF_POLYHEDRON_EXPLICIT ← prove
   r"!s:real^N->bool f a b.
        FINITE f /\
        s = affine hull s INTER INTERS f /\
        (!h. h IN f ==> ~(a h = vec 0) /\ h = {x | a h dot x <= b h}) /\
        (!f'. f' PSUBSET f ==> s PSUBSET affine hull s INTER INTERS f')
        ==> !c. c facet_of s <=>
                ?h. h IN f /\ c = s INTER {x | a h dot x = b h}"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"s:real^N->bool = {}") THENL
     [ASM_REWRITE_TAC [INTER_EMPTY, AFFINE_HULL_EMPTY, ← SET_RULE (← q r"~(s PSUBSET s)"),
                       FACET_OF_EMPTY] THEN
      ASM_CASES_TAC (← q r"f:(real^N->bool)->bool = {}") THEN
      ASM_REWRITE_TAC [NOT_IN_EMPTY] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"h:real^N->bool")) THEN DISCH_THEN
       (fun th => tactic_of do
         pure (MP_TAC (← SPEC (← q r"f DELETE (h:real^N->bool)")
           (← liftExcept (last (CONJUNCTS th)))))) THEN
      ASM SET_TAC [],
      STRIP_TAC] THEN
    SUBGOAL_THEN (← q r"polyhedron(s:real^N->bool)") ASSUME_TAC THENL
     [REWRITE_TAC [POLYHEDRON_INTER_AFFINE] THEN
      REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP POLYHEDRON_IMP_CONVEX) THEN
    SUBGOAL_THEN
     (← q r"!h:real^N->bool.
         h IN f ==> (s INTER {x:real^N | a h dot x = b h}) facet_of s")
    (LABEL_TAC "face") THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC [facet_of] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC POLYHEDRON_IMP_CONVEX THEN
          REWRITE_TAC [POLYHEDRON_INTER_AFFINE] THEN
          REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN ASM_MESON_TAC [],
          X_GEN_TAC (← q r"x:real^N") THEN FIRST_X_ASSUM SUBST1_TAC THEN
          REWRITE_TAC [IN_INTER, IN_INTERS] THEN
          DISCH_THEN (MP_TAC o SPEC (← q r"h:real^N->bool") o CONJUNCT2) THEN
          ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
          FIRST_X_ASSUM (MP_TAC o SPEC (← q r"h:real^N->bool")) THEN
          ASM_REWRITE_TAC [] THEN ASM SET_TAC []],
        ALL_TAC] THEN
      MP_TAC (← ISPEC (← q r"s:real^N->bool") RELATIVE_INTERIOR_EQ_EMPTY) THEN
      ASM_SIMP_TAC [] THEN REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"x:real^N")) THEN
      FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [IN_RELATIVE_INTERIOR]) THEN
      DISCH_TAC THEN
      FIRST_ASSUM (MP_TAC o SPEC (← q r"f DELETE (h:real^N->bool)")) THEN
      ANTS_TAC THENL
       [ASM SET_TAC [],
        REWRITE_TAC [PSUBSET_ALT, IN_INTER, IN_INTERS, IN_DELETE]] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"z:real^N") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"(a:(real^N->bool)->real^N) h dot z > b h") ASSUME_TAC THENL
       [UNDISCH_TAC (← q r"~((z:real^N) IN s)") THEN
        FIRST_ASSUM (SUBST1_TAC o SYM) THEN
        REWRITE_TAC [IN_INTER, IN_INTERS] THEN
        ASM_REWRITE_TAC [← REAL_ARITH (← q r"a:real > b <=> ~(a <= b)")] THEN
        ASM SET_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"~(z:real^N = x)") ASSUME_TAC THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"f:(real^N->bool)->bool",
                        ← q r"a:(real^N->bool)->real^N", ← q r"b:(real^N->bool)->real"]
             RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"x:real^N")) THEN
      ASM_REWRITE_TAC [IN_ELIM_THM] THEN
      DISCH_THEN (fun th => tactic_of do pure (
        MP_TAC (← SPEC (← q r"h:real^N->bool") th) THEN ASM_REWRITE_TAC [] THEN
        DISCH_TAC THEN ASSUME_TAC th)) THEN
      SUBGOAL_THEN (← q r"(a:(real^N->bool)->real^N) h dot x < a h dot z")
      ASSUME_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      ABBREV_TAC (← q r"l = (b h - (a:(real^N->bool)->real^N) h dot x) /
                      (a h dot z - a h dot x)") THEN
      SUBGOAL_THEN (← q r"&0 < l /\ l < &1") STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "l" THEN
        ASM_SIMP_TAC [REAL_LT_LDIV_EQ, REAL_LT_RDIV_EQ, REAL_SUB_LT] THEN
        ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      ABBREV_TAC (← q r"w:real^N = (&1 - l) % x + l % z:real^N") THEN
      SUBGOAL_THEN
       (← q r"!i. i IN f /\ ~(i = h) ==> (a:(real^N->bool)->real^N) i dot w < b i")
      ASSUME_TAC THENL
       [X_GEN_TAC (← q r"i:real^N->bool") THEN STRIP_TAC THEN EXPAND_TAC "w" THEN
        REWRITE_TAC [DOT_RADD, DOT_RMUL] THEN
        MATCH_MP_TAC (← REAL_ARITH
         (← q r"(&1 - l) * x < (&1 - l) * z /\ l * y <= l * z
          ==> (&1 - l) * x + l * y < z")) THEN
        ASM_SIMP_TAC [REAL_LE_LMUL_EQ, REAL_LT_IMP_LE,
                      REAL_LT_LMUL_EQ, REAL_SUB_LT] THEN
        UNDISCH_TAC (← q r"!t:real^N->bool. t IN f /\ ~(t = h) ==> z IN t") THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"i:real^N->bool")) THEN ASM SET_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(a:(real^N->bool)->real^N) h dot w = b h") ASSUME_TAC THENL
       [EXPAND_TAC "w" THEN REWRITE_TAC [← VECTOR_ARITH
           (← q r"(&1 - l) % x + l % z:real^N = x + l % (z - x)")] THEN
        EXPAND_TAC "l" THEN REWRITE_TAC [DOT_RADD, DOT_RSUB, DOT_RMUL] THEN
        ASM_SIMP_TAC [REAL_DIV_RMUL, REAL_LT_IMP_NE, REAL_SUB_0] THEN
        REAL_ARITH_TAC,
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(w:real^N) IN s") ASSUME_TAC THENL
       [FIRST_ASSUM (fun th => GEN_REWRITE_TAC RAND_CONV [th]) THEN
        REWRITE_TAC [IN_INTER, IN_INTERS] THEN CONJ_TAC THENL
         [EXPAND_TAC "w" THEN
          MATCH_MP_TAC (← REWRITE_RULE [AFFINE_ALT] AFFINE_AFFINE_HULL) THEN
          ASM_REWRITE_TAC [] THEN MATCH_MP_TAC HULL_INC THEN
          ASM_MESON_TAC [RELATIVE_INTERIOR_SUBSET, SUBSET],
          ALL_TAC] THEN
        X_GEN_TAC (← q r"i:real^N->bool") THEN DISCH_TAC THEN
        ASM_CASES_TAC (← q r"i:real^N->bool = h") THENL
         [ASM SET_TAC [REAL_LE_REFL], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"convex(i:real^N->bool)") MP_TAC THENL
         [REPEAT (FIRST_X_ASSUM (MP_TAC o C MATCH_MP
           (← ASSUME (← q r"(i:real^N->bool) IN f")))) THEN
          REPEAT (DISCH_THEN (fun th => ONCE_REWRITE_TAC [th])) THEN
          REWRITE_TAC [CONVEX_HALFSPACE_LE],
          ALL_TAC] THEN
        REWRITE_TAC [CONVEX_ALT] THEN EXPAND_TAC "w" THEN
        DISCH_THEN MATCH_MP_TAC THEN
        ASM_SIMP_TAC [] THEN FIRST_X_ASSUM (MP_TAC o CONJUNCT1) THEN
        FIRST_ASSUM (fun t => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [t]) THEN
        REWRITE_TAC [IN_INTER, IN_INTERS] THEN ASM_SIMP_TAC [REAL_LT_IMP_LE],
        ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      ONCE_REWRITE_TAC [← GSYM AFF_DIM_AFFINE_HULL] THEN
      SUBGOAL_THEN
       (← q r"affine hull (s INTER {x | (a:(real^N->bool)->real^N) h dot x = b h}) =
        (affine hull s) INTER {x | a h dot x = b h}")
      SUBST1_TAC THENL
       [ALL_TAC,
        SIMP_TAC [AFF_DIM_AFFINE_INTER_HYPERPLANE, AFFINE_AFFINE_HULL] THEN
        COND_CASES_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
        COND_CASES_TAC THENL [ASM SET_TAC [REAL_LT_REFL], REFL_TAC]] THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC [SUBSET_INTER] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC HULL_MONO THEN SET_TAC [],
        MATCH_MP_TAC (← SET_RULE
         (← q r"s SUBSET affine hull t /\ affine hull t = t ==> s SUBSET t")) THEN
        REWRITE_TAC [AFFINE_HULL_EQ, AFFINE_HYPERPLANE] THEN
        MATCH_MP_TAC HULL_MONO THEN SET_TAC [],
        ALL_TAC] THEN
      REWRITE_TAC [SUBSET, IN_INTER, IN_ELIM_THM] THEN
      X_GEN_TAC (← q r"y:real^N") THEN STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"?t. &0 < t /\
            !j. j IN f /\ ~(j:real^N->bool = h)
                ==> t * (a j dot y - a j dot w) <= b j - a j dot (w:real^N)")
      STRIP_ASSUME_TAC THENL
       [ASM_CASES_TAC (← q r"f DELETE (h:real^N->bool) = {}") THENL
         [ASM_REWRITE_TAC [← GSYM IN_DELETE, NOT_IN_EMPTY] THEN
          EXISTS_TAC (← q r"&1") THEN REWRITE_TAC [REAL_LT_01],
          ALL_TAC] THEN
        EXISTS_TAC (← q r"inf (IMAGE
         (\j. if &0 < a j dot y - a j dot (w:real^N)
              then (b j - a j dot w) / (a j dot y - a j dot w)
              else &1) (f DELETE (h:real^N->bool)))") THEN
        MATCH_MP_TAC (← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")) THEN CONJ_TAC THENL
         [ASM_SIMP_TAC [REAL_LT_INF_FINITE, FINITE_IMAGE, FINITE_DELETE,
                        IMAGE_EQ_EMPTY, FORALL_IN_IMAGE, IN_DELETE] THEN
          ONCE_REWRITE_TAC [COND_RAND] THEN ONCE_REWRITE_TAC [COND_RATOR] THEN
          ASM_SIMP_TAC [REAL_LT_DIV, REAL_SUB_LT, REAL_LT_01, COND_ID],
          REWRITE_TAC [REAL_SUB_LT] THEN DISCH_TAC] THEN
        X_GEN_TAC (← q r"j:real^N->bool") THEN STRIP_TAC THEN
        ASM_CASES_TAC (← q r"a j dot (w:real^N) < a(j:real^N->bool) dot y") THENL
         [ASM_SIMP_TAC [← GSYM REAL_LE_RDIV_EQ, REAL_INF_LE_FINITE, REAL_SUB_LT,
                        FINITE_IMAGE, FINITE_DELETE, IMAGE_EQ_EMPTY] THEN
          REWRITE_TAC [EXISTS_IN_IMAGE] THEN EXISTS_TAC (← q r"j:real^N->bool") THEN
          ASM_REWRITE_TAC [IN_DELETE, REAL_LE_REFL],
          MATCH_MP_TAC (← REAL_ARITH (← q r"&0 <= --x /\ &0 < y ==> x <= y")) THEN
          ASM_SIMP_TAC [REAL_SUB_LT, ← GSYM REAL_MUL_RNEG, REAL_LE_MUL_EQ] THEN
          ASM_REAL_ARITH_TAC],
        ALL_TAC] THEN
      ABBREV_TAC (← q r"c:real^N = (&1 - t) % w + t % y") THEN
      SUBGOAL_THEN (← q r"y:real^N = (&1 - inv t) % w + inv(t) % c") SUBST1_TAC THENL
       [EXPAND_TAC "c" THEN
        REWRITE_TAC [VECTOR_ADD_LDISTRIB, VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC [REAL_MUL_LINV, REAL_LT_IMP_NZ,
                  ← REAL_FIELD (← q r"&0 < x ==> inv x * (&1 - x) = inv x - &1")] THEN
        VECTOR_ARITH_TAC,
        ALL_TAC] THEN
      MATCH_MP_TAC (← REWRITE_RULE [AFFINE_ALT] AFFINE_AFFINE_HULL) THEN
      CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN
      ASM_REWRITE_TAC [IN_INTER, IN_ELIM_THM] THEN
      MATCH_MP_TAC (← TAUT (← q r"b /\ (b ==> a) ==> a /\ b")) THEN CONJ_TAC THENL
       [EXPAND_TAC "c" THEN REWRITE_TAC [DOT_RADD, DOT_RMUL] THEN
        ASM_REWRITE_TAC [] THEN CONV_TAC (fun t => REAL_RING t),
        DISCH_TAC] THEN
      FIRST_ASSUM (fun t => GEN_REWRITE_TAC RAND_CONV [t]) THEN
      REWRITE_TAC [IN_INTER, IN_INTERS] THEN CONJ_TAC THENL
       [EXPAND_TAC "c" THEN
        MATCH_MP_TAC (← REWRITE_RULE [AFFINE_ALT] AFFINE_AFFINE_HULL) THEN
        ASM_SIMP_TAC [HULL_INC],
        ALL_TAC] THEN
      X_GEN_TAC (← q r"j:real^N->bool") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC o C MATCH_MP
        (← ASSUME (← q r"(j:real^N->bool) IN f"))) THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN
      ASM_CASES_TAC (← q r"j:real^N->bool = h") THEN ASM_SIMP_TAC [REAL_EQ_IMP_LE] THEN
      EXPAND_TAC "c" THEN REWRITE_TAC [DOT_RADD, DOT_RMUL] THEN
      REWRITE_TAC [← REAL_ARITH
       (← q r"(&1 - t) * x + t * y <= z <=> t * (y - x) <= z - x")] THEN
      ASM_SIMP_TAC [],
      ALL_TAC] THEN
    X_GEN_TAC (← q r"c:real^N->bool") THEN EQ_TAC THENL
     [ALL_TAC, STRIP_TAC THEN ASM_SIMP_TAC []] THEN
    REWRITE_TAC [facet_of] THEN STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP FACE_OF_IMP_CONVEX) THEN
    SUBGOAL_THEN (← q r"~(relative_interior(c:real^N->bool) = {})") MP_TAC THENL
     [ASM_SIMP_TAC [RELATIVE_INTERIOR_EQ_EMPTY], ALL_TAC] THEN
    REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"x:real^N")) THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"f:(real^N->bool)->bool",
                      ← q r"a:(real^N->bool)->real^N", ← q r"b:(real^N->bool)->real"]
           RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"x:real^N")) THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN
    SUBGOAL_THEN (← q r"~(c:real^N->bool = s)") ASSUME_TAC THENL
     [ASM_MESON_TAC [← INT_ARITH (← q r"~(i:int = i - &1)")], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~((x:real^N) IN relative_interior s)") ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"~(c:real^N->bool = s)") THEN REWRITE_TAC [CONTRAPOS_THM] THEN
      DISCH_TAC THEN MATCH_MP_TAC FACE_OF_EQ THEN
      EXISTS_TAC (← q r"s:real^N->bool") THEN ASM_SIMP_TAC [FACE_OF_REFL] THEN
      ASM SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(x:real^N) IN s") MP_TAC THENL
     [FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE [SUBSET] o MATCH_MP
         FACE_OF_IMP_SUBSET) THEN
      ASM_SIMP_TAC [← REWRITE_RULE [SUBSET] RELATIVE_INTERIOR_SUBSET],
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN DISCH_THEN (fun th => ASSUME_TAC th THEN MP_TAC th) THEN
    FIRST_ASSUM (fun t => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [t]) THEN
    REWRITE_TAC [IN_INTER, IN_INTERS] THEN STRIP_TAC THEN
    REWRITE_TAC [NOT_FORALL_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"i:real^N->bool") THEN REWRITE_TAC [NOT_IMP] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"(a:(real^N->bool)->real^N) i dot x = b i") ASSUME_TAC THENL
     [MATCH_MP_TAC (← REAL_ARITH (← q r"x <= y /\ ~(x < y) ==> x = y")) THEN
      ASM_REWRITE_TAC [] THEN UNDISCH_THEN
       (← q r"!t:real^N->bool. t IN f ==> x IN t") (MP_TAC o SPEC (← q r"i:real^N->bool")) THEN
      ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o CONJUNCT2 o C MATCH_MP
       (← ASSUME (← q r"(i:real^N->bool) IN f"))) THEN SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"c SUBSET (s INTER {x:real^N | a(i:real^N->bool) dot x = b i})")
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC (← q r"s:real^N->bool") THEN
      ASM_SIMP_TAC [FACE_OF_IMP_SUBSET] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [facet_of]) THEN ASM_SIMP_TAC [] THEN
      REWRITE_TAC [DISJOINT, ← GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC (← q r"x:real^N") THEN ASM_REWRITE_TAC [IN_INTER, IN_ELIM_THM],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"c face_of (s INTER {x:real^N | a(i:real^N->bool) dot x = b i})")
    ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"c:real^N->bool", ← q r"s:real^N->bool",
                        ← q r"s INTER {x:real^N | a(i:real^N->bool) dot x = b i}"]
                  FACE_OF_FACE) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [facet_of]) THEN ASM_SIMP_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"(~p ==> F) ==> p")) THEN DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"aff_dim(c:real^N->bool) <
      aff_dim(s INTER {x:real^N | a(i:real^N->bool) dot x = b i})")
    MP_TAC THENL
     [MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
      ASM_SIMP_TAC [CONVEX_INTER, CONVEX_HYPERPLANE],
      RULE_ASSUM_TAC (REWRITE_RULE [facet_of]) THEN ASM_SIMP_TAC [INT_LT_REFL]])

  let FACE_OF_POLYHEDRON_SUBSET_EXPLICIT ← prove
   r"!s:real^N->bool f a b.
        FINITE f /\
        s = affine hull s INTER INTERS f /\
        (!h. h IN f ==> ~(a h = vec 0) /\ h = {x | a h dot x <= b h}) /\
        (!f'. f' PSUBSET f ==> s PSUBSET affine hull s INTER INTERS f')
        ==> !c. c face_of s /\ ~(c = {}) /\ ~(c = s)
                ==> ?h. h IN f /\ c SUBSET (s INTER {x | a h dot x = b h})"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"f:(real^N->bool)->bool = {}") THENL
     [DISCH_THEN (MP_TAC o SYM o CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC [INTERS_0, INTER_UNIV, AFFINE_HULL_EQ] THEN
      MESON_TAC [FACE_OF_AFFINE_TRIVIAL],
      ALL_TAC] THEN
    DISCH_THEN (fun th => STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN (ASSUME_TAC o MATCH_MP FACET_OF_POLYHEDRON_EXPLICIT) THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP FACE_OF_IMP_CONVEX) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
    SUBGOAL_THEN (← q r"polyhedron(s:real^N->bool)") ASSUME_TAC THENL
     [REWRITE_TAC [POLYHEDRON_INTER_AFFINE] THEN
      REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP POLYHEDRON_IMP_CONVEX) THEN
    SUBGOAL_THEN
     (← q r"!h:real^N->bool.
          h IN f ==> (s INTER {x:real^N | a h dot x = b h}) face_of s")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN CONJ_TAC THENL
       [MATCH_MP_TAC POLYHEDRON_IMP_CONVEX THEN
        REWRITE_TAC [POLYHEDRON_INTER_AFFINE] THEN
        REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN ASM_MESON_TAC [],
        X_GEN_TAC (← q r"x:real^N") THEN FIRST_X_ASSUM SUBST1_TAC THEN
        REWRITE_TAC [IN_INTER, IN_INTERS] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"h:real^N->bool") o CONJUNCT2) THEN
        ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"h:real^N->bool")) THEN
        ASM_REWRITE_TAC [] THEN ASM SET_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(relative_interior(c:real^N->bool) = {})") MP_TAC THENL
     [ASM_SIMP_TAC [RELATIVE_INTERIOR_EQ_EMPTY], ALL_TAC] THEN
    REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"x:real^N")) THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"f:(real^N->bool)->bool",
                      ← q r"a:(real^N->bool)->real^N", ← q r"b:(real^N->bool)->real"]
           RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"x:real^N")) THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN
    SUBGOAL_THEN (← q r"~((x:real^N) IN relative_interior s)") ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"~(c:real^N->bool = s)") THEN REWRITE_TAC [CONTRAPOS_THM] THEN
      DISCH_TAC THEN MATCH_MP_TAC FACE_OF_EQ THEN
      EXISTS_TAC (← q r"s:real^N->bool") THEN ASM_SIMP_TAC [FACE_OF_REFL] THEN
      ASM SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(x:real^N) IN s") MP_TAC THENL
     [FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE [SUBSET] o MATCH_MP
         FACE_OF_IMP_SUBSET) THEN
      ASM_SIMP_TAC [← REWRITE_RULE [SUBSET] RELATIVE_INTERIOR_SUBSET],
      ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN DISCH_THEN (fun th => ASSUME_TAC th THEN MP_TAC th) THEN
    FIRST_ASSUM (fun t => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [t]) THEN
    REWRITE_TAC [IN_INTER, IN_INTERS] THEN STRIP_TAC THEN
    REWRITE_TAC [NOT_FORALL_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"i:real^N->bool") THEN REWRITE_TAC [NOT_IMP] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"(a:(real^N->bool)->real^N) i dot x = b i") ASSUME_TAC THENL
     [MATCH_MP_TAC (← REAL_ARITH (← q r"x <= y /\ ~(x < y) ==> x = y")) THEN
      ASM_REWRITE_TAC [] THEN UNDISCH_THEN
       (← q r"!t:real^N->bool. t IN f ==> x IN t") (MP_TAC o SPEC (← q r"i:real^N->bool")) THEN
      ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o CONJUNCT2 o C MATCH_MP
       (← ASSUME (← q r"(i:real^N->bool) IN f"))) THEN SET_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC (← q r"s:real^N->bool") THEN
    ASM_SIMP_TAC [FACE_OF_IMP_SUBSET] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [facet_of]) THEN ASM_SIMP_TAC [] THEN
    REWRITE_TAC [DISJOINT, ← GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC (← q r"x:real^N") THEN ASM_REWRITE_TAC [IN_INTER, IN_ELIM_THM])

  let FACE_OF_POLYHEDRON_EXPLICIT ← (do
    let lemma ← prove
     r"!t s. (!a. P a ==> t SUBSET s INTER INTERS {f x | P x})
           ==> t SUBSET INTERS {s INTER f x | P x}"
     (ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
      REWRITE_TAC [INTERS_IMAGE] THEN SET_TAC [])
    prove
     r"!s:real^N->bool f a b.
        FINITE f /\
        s = affine hull s INTER INTERS f /\
        (!h. h IN f ==> ~(a h = vec 0) /\ h = {x | a h dot x <= b h}) /\
        (!f'. f' PSUBSET f ==> s PSUBSET affine hull s INTER INTERS f')
        ==> !c. c face_of s /\ ~(c = {}) /\ ~(c = s)
                ==> c = INTERS {s INTER {x | a h dot x = b h} |h|
                                h IN f /\
                                c SUBSET (s INTER {x | a h dot x = b h})}"
     (REPEAT GEN_TAC THEN
      DISCH_THEN (fun th => STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
      DISCH_THEN (ASSUME_TAC o MATCH_MP FACET_OF_POLYHEDRON_EXPLICIT) THEN
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP FACE_OF_IMP_CONVEX) THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
      SUBGOAL_THEN (← q r"polyhedron(s:real^N->bool)") ASSUME_TAC THENL
       [REWRITE_TAC [POLYHEDRON_INTER_AFFINE] THEN
        REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP POLYHEDRON_IMP_CONVEX) THEN
      SUBGOAL_THEN
       (← q r"!h:real^N->bool.
            h IN f ==> (s INTER {x:real^N | a h dot x = b h}) face_of s")
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN
        MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN CONJ_TAC THENL
         [MATCH_MP_TAC POLYHEDRON_IMP_CONVEX THEN
          REWRITE_TAC [POLYHEDRON_INTER_AFFINE] THEN
          REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN ASM_MESON_TAC [],
          X_GEN_TAC (← q r"x:real^N") THEN FIRST_X_ASSUM SUBST1_TAC THEN
          REWRITE_TAC [IN_INTER, IN_INTERS] THEN
          DISCH_THEN (MP_TAC o SPEC (← q r"h:real^N->bool") o CONJUNCT2) THEN
          ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
          FIRST_X_ASSUM (MP_TAC o SPEC (← q r"h:real^N->bool")) THEN
          ASM_REWRITE_TAC [] THEN ASM SET_TAC []],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"~(relative_interior(c:real^N->bool) = {})") MP_TAC THENL
       [ASM_SIMP_TAC [RELATIVE_INTERIOR_EQ_EMPTY], ALL_TAC] THEN
      REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"z:real^N") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"(z:real^N) IN s") ASSUME_TAC THENL
       [FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE [SUBSET]) THEN
        MATCH_MP_TAC (← REWRITE_RULE [SUBSET] RELATIVE_INTERIOR_SUBSET) THEN
        ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      MATCH_MP_TAC FACE_OF_EQ THEN EXISTS_TAC (← q r"s:real^N->bool") THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FACE_OF_INTERS THEN ASM_SIMP_TAC [FORALL_IN_GSPEC] THEN
        ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN REWRITE_TAC [IMAGE_EQ_EMPTY] THEN
        REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM] THEN
        MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"f:(real^N->bool)->bool",
                          ← q r"a:(real^N->bool)->real^N", ← q r"b:(real^N->bool)->real"]
             FACE_OF_POLYHEDRON_SUBSET_EXPLICIT) THEN
        ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"{s INTER {x | a(h:real^N->bool) dot x = b h} |h|
         h IN f /\ c SUBSET (s INTER {x:real^N | a h dot x = b h})} =
        {s INTER {x | a(h:real^N->bool) dot x = b h} |h|
         h IN f /\ z IN s INTER {x:real^N | a h dot x = b h}}")
      SUBST1_TAC THENL
       [MATCH_MP_TAC (← SET_RULE
         (← q r"(!x. P x <=> Q x) ==> {f x | P x} = {f x | Q x}")) THEN
        X_GEN_TAC (← q r"h:real^N->bool") THEN EQ_TAC THEN STRIP_TAC THEN
        ASM_REWRITE_TAC [] THENL
         [FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE [SUBSET]) THEN
          MATCH_MP_TAC (← REWRITE_RULE [SUBSET] RELATIVE_INTERIOR_SUBSET) THEN
          ASM_REWRITE_TAC [],
          MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC (← q r"s:real^N->bool") THEN
          ASM_SIMP_TAC [] THEN ASM SET_TAC []],
        ALL_TAC] THEN
      REWRITE_TAC [DISJOINT, ← GSYM MEMBER_NOT_EMPTY, IN_INTER] THEN
      EXISTS_TAC (← q r"z:real^N") THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN
      SUBGOAL_THEN
       (← q r"?e. &0 < e /\ !h. h IN f /\ a(h:real^N->bool) dot z < b h
                          ==> ball(z,e) SUBSET {w:real^N | a h dot w < b h}")
      (CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*"))) THENL
       [REWRITE_TAC [← SET_RULE
         (← q r"(!h. P h ==> s SUBSET t h) <=> s SUBSET INTERS (IMAGE t {h | P h})")] THEN
        MATCH_MP_TAC (← MESON [OPEN_CONTAINS_BALL]
         (← q r"open s /\ x IN s ==> ?e. &0 < e /\ ball(x,e) SUBSET s")) THEN
        SIMP_TAC [IN_INTERS, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
        MATCH_MP_TAC OPEN_INTERS THEN
        ASM_SIMP_TAC [FORALL_IN_IMAGE, FINITE_IMAGE, FINITE_RESTRICT] THEN
        REWRITE_TAC [OPEN_HALFSPACE_LT],
        ALL_TAC] THEN
      ASM_REWRITE_TAC [IN_RELATIVE_INTERIOR] THEN
      ASM_SIMP_TAC [IN_INTERS, FORALL_IN_GSPEC, IN_ELIM_THM, IN_INTER] THEN
      EXISTS_TAC (← q r"e:real") THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC lemma THEN X_GEN_TAC (← q r"i:real^N->bool") THEN STRIP_TAC THEN
      FIRST_ASSUM (fun th => GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [th]) THEN
      MATCH_MP_TAC (← SET_RULE
       (← q r"ae SUBSET as /\ ae SUBSET hs /\
        b INTER hs SUBSET fs
        ==> (b INTER ae) SUBSET (as INTER fs) INTER hs")) THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC HULL_MONO THEN
        REWRITE_TAC [SUBSET, IN_INTERS, FORALL_IN_GSPEC] THEN ASM SET_TAC [],
        SIMP_TAC [← SET_RULE (← q r"s SUBSET INTERS f <=> !t. t IN f ==> s SUBSET t")] THEN
        REWRITE_TAC [FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"j:real^N->bool") THEN
        STRIP_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
        REWRITE_TAC [AFFINE_HYPERPLANE] THEN
        REWRITE_TAC [SUBSET, IN_INTERS, FORALL_IN_GSPEC] THEN ASM SET_TAC [],
        ALL_TAC] THEN
      REWRITE_TAC [← SET_RULE (← q r"s SUBSET INTERS f <=> !t. t IN f ==> s SUBSET t")] THEN
      X_GEN_TAC (← q r"j:real^N->bool") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"(a:(real^N->bool)->real^N) j dot z <= b j") MP_TAC THENL
       [ASM SET_TAC [], REWRITE_TAC [REAL_LE_LT]] THEN
      STRIP_TAC THENL [ASM SET_TAC [REAL_LT_IMP_LE], ALL_TAC] THEN
      MATCH_MP_TAC (← SET_RULE
      (← q r"(?s. s IN f /\ s SUBSET t) ==> u INTER INTERS f SUBSET t")) THEN
      REWRITE_TAC [EXISTS_IN_GSPEC] THEN EXISTS_TAC (← q r"j:real^N->bool") THEN
      ASM SET_TAC [REAL_LE_REFL]))

  pure { POLYHEDRON_INTER_AFFINE, POLYHEDRON_INTER_AFFINE_PARALLEL,
         POLYHEDRON_INTER_AFFINE_PARALLEL_MINIMAL, POLYHEDRON_INTER_AFFINE_MINIMAL,
         RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT, FACET_OF_POLYHEDRON_EXPLICIT,
         FACE_OF_POLYHEDRON_SUBSET_EXPLICIT, FACE_OF_POLYHEDRON_EXPLICIT }

/- ------------------------------------------------------------------------- -/
/- More general corollaries from the explicit representation.               -/
/- (polytope.ml 5187-5567)                                                   -/
/- ------------------------------------------------------------------------- -/

structure POL where
  FACET_OF_POLYHEDRON : thm
  FACE_OF_POLYHEDRON : thm
  FACE_OF_POLYHEDRON_SUBSET_FACET : thm
  FACE_OF_POLYHEDRON_FACE_OF_FACET : thm
  EXPOSED_FACE_OF_POLYHEDRON : thm
  FACE_OF_POLYHEDRON_POLYHEDRON : thm
  FINITE_POLYHEDRON_FACES : thm
  FINITE_POLYHEDRON_EXPOSED_FACES : thm
  FINITE_POLYHEDRON_EXTREME_POINTS : thm
  FINITE_POLYHEDRON_FACETS : thm
  RELATIVE_INTERIOR_OF_POLYHEDRON : thm
  RELATIVE_BOUNDARY_OF_POLYHEDRON : thm
  RELATIVE_FRONTIER_OF_POLYHEDRON : thm
  RELATIVE_FRONTIER_OF_POLYHEDRON_ALT : thm
  FACETS_OF_POLYHEDRON_EXPLICIT_DISTINCT : thm
  POLYHEDRON_MINIMAL_LEMMA : thm
  POLYHEDRON : thm
  deriving Inhabited

set_option maxHeartbeats 8000000 in
@[nospecialize]
def setupPOL [HolBase] (D : PolytopeDeps) (BPOA : POA) (BPOC : POC) (BPOD : POD) (BPOE : POE) (BPOG : POG) (BPOJ : POJ) (BPOK : POK) : ExceptT String IO POL := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, REAL_ARITH, SET_RULE, SET_TAC, .. } := D.cvx
  let { WF_INDUCT_TAC, .. } := D
  let { CARD_PSUBSET, EMPTY_GSPEC, EXTENSION, FINITE_DELETE, FINITE_EMPTY, FINITE_IMAGE,
        FINITE_POWERSET, FINITE_RESTRICT, FINITE_SING, FINITE_SUBSET, FINITE_UNION,
        FORALL_IN_GSPEC, .. } := D.cvx.core1
  let { FORALL_IN_UNION, FORALL_IN_UNIONS, IMAGE_ID, IMP_CONJ, IN_DELETE, IN_DIFF,
        INTER_EMPTY, INTERS_UNION, .. } := D.cvx.core2
  let { IN_ELIM_THM, IN_INTER, IN_INTERS, IN_UNIONS, LEFT_AND_EXISTS_THM,
        LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY, MONO_EXISTS, MONO_FORALL, NOT_FORALL_THM,
        NOT_IMP, NOT_IN_EMPTY, PSUBSET, .. } := D.cvx.core3
  let { REAL_LE_LMUL_EQ, REAL_LE_LT, REAL_LT_LMUL_EQ, REAL_LT_REFL, .. } := D.cvx.core4
  let { REAL_SUB_LT, RIGHT_AND_EXISTS_THM, RIGHT_FORALL_IMP_THM, RIGHT_IMP_EXISTS_THM,
        SIMPLE_IMAGE_GEN, SKOLEM_THM, SUBSET, SUBSET_REFL, SUBSET_TRANS, .. } := D.cvx.core5
  let { SWAP_EXISTS_THM, UNIONS_IMAGE, UNWIND_THM2, .. } := D.cvx.core6
  let { HULL_INC, HULL_SUBSET, .. } := D.cvx.misc
  let { DOT_RADD, DOT_RMUL, .. } := D.cvx.vec1
  let { CLOSURE_CLOSED, .. } := D.cvx.top1
  let { CONNECTED_SEGMENT, .. } := D.cvx.top2
  let { ENDS_IN_SEGMENT, .. } := D.cvx.top3
  let { IN_SEGMENT, .. } := D.cvx.top4
  let { FINITE_FINITE_PREIMAGE, PSUBSET_ALT, PSUBSET_IRREFL, .. } := D.qses
  let { IN_OPEN_SEGMENT_ALT, .. } := D.qtop
  let { AFFINE_AFFINE_HULL, AFFINE_HULL_EMPTY, AFFINE_IMP_CONVEX, .. } := D.qcvx1
  let { CONNECTED_INTER_RELATIVE_FRONTIER, CONVEX_CONTAINS_SEGMENT, .. } := D.qcvx2
  let { relative_frontier, RELATIVE_INTERIOR_EQ_EMPTY, .. } := D.qcvx3
  let { FACE_OF_IMP_SUBSET, FACE_OF_SUBSET, .. } := BPOA
  let { RELATIVE_FRONTIER_OF_CONVEX_CLOSED, .. } := BPOC
  let { EMPTY_EXPOSED_FACE_OF, exposed_face_of, EXPOSED_FACE_OF_INTERS,
        EXPOSED_FACE_OF_REFL, .. } := BPOD
  let { FACE_OF_SING, .. } := BPOE
  let { facet_of, FACET_OF_IMP_FACE_OF, FACET_OF_IMP_SUBSET, .. } := BPOG
  let { AFFINE_IMP_POLYHEDRON, polyhedron, POLYHEDRON_EMPTY, POLYHEDRON_HYPERPLANE,
        POLYHEDRON_IMP_CLOSED, POLYHEDRON_IMP_CONVEX, POLYHEDRON_INTER, POLYHEDRON_INTERS,
        .. } := BPOJ
  let { FACE_OF_POLYHEDRON_EXPLICIT, FACET_OF_POLYHEDRON_EXPLICIT, POLYHEDRON_INTER_AFFINE,
        POLYHEDRON_INTER_AFFINE_MINIMAL, RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT, .. } := BPOK
  -- @@SCOPE END

  let FACET_OF_POLYHEDRON ← prove
   r"!s:real^N->bool c.
        polyhedron s /\ c facet_of s
        ==> ?a b. ~(a = vec 0) /\
                  s SUBSET {x | a dot x <= b} /\
                  c = s INTER {x | a dot x = b}"
   (REPEAT STRIP_TAC THEN FIRST_ASSUM
     (MP_TAC o GEN_REWRITE_RULE I [POLYHEDRON_INTER_AFFINE_MINIMAL]) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN
    SIMP_TAC [LEFT_IMP_EXISTS_THM, RIGHT_AND_EXISTS_THM, LEFT_AND_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"f:(real^N->bool)->bool", ← q r"a:(real^N->bool)->real^N",
      ← q r"b:(real^N->bool)->real"] THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"f:(real^N->bool)->bool",
                      ← q r"a:(real^N->bool)->real^N", ← q r"b:(real^N->bool)->real"]
          FACET_OF_POLYHEDRON_EXPLICIT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"c:real^N->bool")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"i:real^N->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"(a:(real^N->bool)->real^N) i") THEN
    EXISTS_TAC (← q r"(b:(real^N->bool)->real) i") THEN ASM_SIMP_TAC [] THEN
    FIRST_X_ASSUM (fun th => GEN_REWRITE_TAC LAND_CONV [th]) THEN
    MATCH_MP_TAC (← SET_RULE (← q r"t SUBSET u ==> (s INTER t) SUBSET u")) THEN
    MATCH_MP_TAC (← SET_RULE (← q r"t IN f ==> INTERS f SUBSET t")) THEN ASM_MESON_TAC [])

  let FACE_OF_POLYHEDRON ← prove
   r"!s:real^N->bool c.
        polyhedron s /\ c face_of s /\ ~(c = {}) /\ ~(c = s)
        ==> c = INTERS {f | f facet_of s /\ c SUBSET f}"
   (REPEAT STRIP_TAC THEN FIRST_ASSUM
     (MP_TAC o GEN_REWRITE_RULE I [POLYHEDRON_INTER_AFFINE_MINIMAL]) THEN
    REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN
    SIMP_TAC [LEFT_IMP_EXISTS_THM, RIGHT_AND_EXISTS_THM, LEFT_AND_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"f:(real^N->bool)->bool", ← q r"a:(real^N->bool)->real^N",
      ← q r"b:(real^N->bool)->real"] THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"f:(real^N->bool)->bool",
                      ← q r"a:(real^N->bool)->real^N", ← q r"b:(real^N->bool)->real"]
           FACET_OF_POLYHEDRON_EXPLICIT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"f:(real^N->bool)->bool",
                      ← q r"a:(real^N->bool)->real^N", ← q r"b:(real^N->bool)->real"]
           FACE_OF_POLYHEDRON_EXPLICIT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"c:real^N->bool")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th => GEN_REWRITE_TAC LAND_CONV [th]) THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    X_GEN_TAC (← q r"h:real^N->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [])

  let FACE_OF_POLYHEDRON_SUBSET_FACET ← prove
   r"!s:real^N->bool c.
        polyhedron s /\ c face_of s /\ ~(c = {}) /\ ~(c = s)
        ==> ?f. f facet_of s /\ c SUBSET f"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"c:real^N->bool"] FACE_OF_POLYHEDRON) THEN
    ASM_CASES_TAC (← q r"{f:real^N->bool | f facet_of s /\ c SUBSET f} = {}") THEN
    ASM SET_TAC [])

  let FACE_OF_POLYHEDRON_FACE_OF_FACET ← prove
   r"!s c:real^N->bool.
        polyhedron s /\ c face_of s /\ ~(c = {}) /\ ~(c = s)
        ==> ?f. c face_of f /\ f facet_of s"
   (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"c:real^N->bool"]
          FACE_OF_POLYHEDRON_SUBSET_FACET) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FACE_OF_SUBSET THEN
    EXISTS_TAC (← q r"s:real^N->bool") THEN ASM_SIMP_TAC [FACET_OF_IMP_SUBSET])

  let EXPOSED_FACE_OF_POLYHEDRON ← prove
   r"!s f:real^N->bool. polyhedron s ==> (f exposed_face_of s <=> f face_of s)"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL [SIMP_TAC [exposed_face_of], ALL_TAC] THEN
    DISCH_TAC THEN ASM_CASES_TAC (← q r"f:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [EMPTY_EXPOSED_FACE_OF] THEN
    ASM_CASES_TAC (← q r"f:real^N->bool = s") THEN
    ASM_SIMP_TAC [EXPOSED_FACE_OF_REFL, POLYHEDRON_IMP_CONVEX] THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"f:real^N->bool"] FACE_OF_POLYHEDRON) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC EXPOSED_FACE_OF_INTERS THEN
    REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, FORALL_IN_GSPEC] THEN
    ASM_SIMP_TAC [FACE_OF_POLYHEDRON_SUBSET_FACET, IN_ELIM_THM] THEN
    ASM_SIMP_TAC [exposed_face_of, FACET_OF_IMP_FACE_OF] THEN
    ASM_MESON_TAC [FACET_OF_POLYHEDRON])

  let FACE_OF_POLYHEDRON_POLYHEDRON ← prove
   r"!s:real^N->bool c. polyhedron s /\ c face_of s ==> polyhedron c"
   (REPEAT STRIP_TAC THEN FIRST_ASSUM
     (MP_TAC o GEN_REWRITE_RULE I [POLYHEDRON_INTER_AFFINE_MINIMAL]) THEN
    REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN
    SIMP_TAC [LEFT_IMP_EXISTS_THM, RIGHT_AND_EXISTS_THM, LEFT_AND_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"f:(real^N->bool)->bool", ← q r"a:(real^N->bool)->real^N",
      ← q r"b:(real^N->bool)->real"] THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"f:(real^N->bool)->bool",
                      ← q r"a:(real^N->bool)->real^N", ← q r"b:(real^N->bool)->real"]
           FACE_OF_POLYHEDRON_EXPLICIT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"c:real^N->bool")) THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"c:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [POLYHEDRON_EMPTY] THEN
    ASM_CASES_TAC (← q r"c:real^N->bool = s") THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC POLYHEDRON_INTERS THEN
    REWRITE_TAC [FORALL_IN_GSPEC] THEN
    ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
    ASM_SIMP_TAC [FINITE_IMAGE, FINITE_RESTRICT] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [IMAGE_ID] THEN
    MATCH_MP_TAC POLYHEDRON_INTER THEN
    ASM_REWRITE_TAC [POLYHEDRON_HYPERPLANE])

  let FINITE_POLYHEDRON_FACES ← prove
   r"!s:real^N->bool. polyhedron s ==> FINITE {f | f face_of s}"
   (REPEAT STRIP_TAC THEN FIRST_ASSUM
     (MP_TAC o GEN_REWRITE_RULE I [POLYHEDRON_INTER_AFFINE_MINIMAL]) THEN
    REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN
    SIMP_TAC [LEFT_IMP_EXISTS_THM, RIGHT_AND_EXISTS_THM, LEFT_AND_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"f:(real^N->bool)->bool", ← q r"a:(real^N->bool)->real^N",
      ← q r"b:(real^N->bool)->real"] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC (← MESON [FINITE_DELETE]
     (← q r"!a b. FINITE (s DELETE a DELETE b) ==> FINITE s")) THEN
    MAP_EVERY EXISTS_TAC [← q r"{}:real^N->bool", ← q r"s:real^N->bool"] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     (← q r"{INTERS {s INTER {x:real^N | a(h:real^N->bool) dot x = b h} | h | h IN f'}
      |f'| f' SUBSET f}") THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SIMPLE_IMAGE_GEN] THEN
    ASM_SIMP_TAC [FINITE_POWERSET, FINITE_IMAGE] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC [IN_DELETE, IN_ELIM_THM] THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"f:(real^N->bool)->bool",
                      ← q r"a:(real^N->bool)->real^N", ← q r"b:(real^N->bool)->real"]
           FACE_OF_POLYHEDRON_EXPLICIT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"c:real^N->bool") THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC [] THEN
    DISCH_TAC THEN EXISTS_TAC
     (← q r"{h:real^N->bool |
       h IN f /\ c SUBSET s INTER {x:real^N | a h dot x = b h}}") THEN
    CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
    ASM_REWRITE_TAC [IN_ELIM_THM] THEN FIRST_ASSUM ACCEPT_TAC)

  let FINITE_POLYHEDRON_EXPOSED_FACES ← prove
   r"!s:real^N->bool. polyhedron s ==> FINITE {f | f exposed_face_of s}"
   (SIMP_TAC [EXPOSED_FACE_OF_POLYHEDRON, FINITE_POLYHEDRON_FACES])

  let FINITE_POLYHEDRON_EXTREME_POINTS ← prove
   r"!s:real^N->bool. polyhedron s ==> FINITE {v | v extreme_point_of s}"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM FACE_OF_SING] THEN
    ONCE_REWRITE_TAC [← SET_RULE (← q r"{v} face_of s <=> {v} IN {f | f face_of s}")] THEN
    MATCH_MP_TAC FINITE_FINITE_PREIMAGE THEN
    ASM_SIMP_TAC [FINITE_POLYHEDRON_FACES] THEN X_GEN_TAC (← q r"f:real^N->bool") THEN
    DISCH_TAC THEN ASM_CASES_TAC (← q r"!a:real^N. ~({a} = f)") THEN
    ASM_REWRITE_TAC [EMPTY_GSPEC, FINITE_EMPTY] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [← SET_RULE (← q r"{v | {v} = {a}} = {a}"), FINITE_SING])

  let FINITE_POLYHEDRON_FACETS ← prove
   r"!s:real^N->bool. polyhedron s ==> FINITE {f | f facet_of s}"
   (REWRITE_TAC [facet_of] THEN ONCE_REWRITE_TAC [← SET_RULE
     (← q r"{x | P x /\ Q x} = {x | x IN {x | P x} /\ Q x}")] THEN
    SIMP_TAC [FINITE_RESTRICT, FINITE_POLYHEDRON_FACES])

  let RELATIVE_INTERIOR_OF_POLYHEDRON ← prove
   r"!s:real^N->bool.
        polyhedron s
        ==> relative_interior s = s DIFF UNIONS {f | f facet_of s}"
   (REPEAT STRIP_TAC THEN FIRST_ASSUM
     (MP_TAC o GEN_REWRITE_RULE I [POLYHEDRON_INTER_AFFINE_MINIMAL]) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN
    SIMP_TAC [LEFT_IMP_EXISTS_THM, RIGHT_AND_EXISTS_THM, LEFT_AND_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"f:(real^N->bool)->bool", ← q r"a:(real^N->bool)->real^N",
      ← q r"b:(real^N->bool)->real"] THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"f:(real^N->bool)->bool",
                      ← q r"a:(real^N->bool)->real^N", ← q r"b:(real^N->bool)->real"]
          FACET_OF_POLYHEDRON_EXPLICIT) THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"f:(real^N->bool)->bool",
                      ← q r"a:(real^N->bool)->real^N", ← q r"b:(real^N->bool)->real"]
          RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT) THEN
    ASM_REWRITE_TAC [] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← SET_RULE
     (← q r"(!x. x IN s ==> P x \/ x IN t) /\ (!x. x IN t ==> ~P x)
      ==> {x | x IN s /\ P x} = s DIFF t")) THEN
    REWRITE_TAC [FORALL_IN_UNIONS] THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM, IMP_CONJ, FORALL_IN_GSPEC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      REWRITE_TAC [IN_UNIONS, IN_ELIM_THM] THEN
      REWRITE_TAC [LEFT_AND_EXISTS_THM, ← TAUT (← q r"(a /\ b) /\ c <=> b /\ a /\ c")] THEN
      ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
      ASM_REWRITE_TAC [UNWIND_THM2, IN_ELIM_THM, IN_INTER] THEN
      MATCH_MP_TAC (← SET_RULE
       (← q r"(!x. P x ==> Q x \/ R x) ==> (!x. P x ==> Q x) \/ (?x. P x /\ R x)")) THEN
      X_GEN_TAC (← q r"h:real^N->bool") THEN DISCH_TAC THEN
      REWRITE_TAC [← GSYM REAL_LE_LT] THEN
      SUBGOAL_THEN (← q r"(x:real^N) IN INTERS f") MP_TAC THENL
       [ASM SET_TAC [], ALL_TAC] THEN
      REWRITE_TAC [IN_INTERS] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"h:real^N->bool")) THEN
      SUBGOAL_THEN (← q r"h = {x:real^N | a h dot x <= b h}") MP_TAC THENL
       [ASM_MESON_TAC [], ASM_REWRITE_TAC [] THEN SET_TAC []],
      X_GEN_TAC (← q r"h:real^N->bool") THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->bool") STRIP_ASSUME_TAC) THEN
      X_GEN_TAC (← q r"x:real^N") THEN ASM_REWRITE_TAC [IN_INTER, IN_ELIM_THM] THEN
      ASM_MESON_TAC [REAL_LT_REFL]])

  let RELATIVE_BOUNDARY_OF_POLYHEDRON ← prove
   r"!s:real^N->bool.
        polyhedron s
        ==> s DIFF relative_interior s = UNIONS {f | f facet_of s}"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [RELATIVE_INTERIOR_OF_POLYHEDRON] THEN
    MATCH_MP_TAC (← SET_RULE (← q r"f SUBSET s ==> s DIFF (s DIFF f) = f")) THEN
    REWRITE_TAC [SUBSET, FORALL_IN_UNIONS, IN_ELIM_THM] THEN
    MESON_TAC [FACET_OF_IMP_SUBSET, SUBSET])

  let RELATIVE_FRONTIER_OF_POLYHEDRON ← prove
   r"!s:real^N->bool.
        polyhedron s ==> relative_frontier s = UNIONS {f | f facet_of s}"
   (SIMP_TAC [relative_frontier, POLYHEDRON_IMP_CLOSED, CLOSURE_CLOSED] THEN
    REWRITE_TAC [RELATIVE_BOUNDARY_OF_POLYHEDRON])

  let RELATIVE_FRONTIER_OF_POLYHEDRON_ALT ← prove
   r"!s:real^N->bool.
        polyhedron s
        ==> relative_frontier s = UNIONS {f | f face_of s /\ ~(f = s)}"
   (ASM_SIMP_TAC [RELATIVE_FRONTIER_OF_CONVEX_CLOSED,
                  POLYHEDRON_IMP_CLOSED, POLYHEDRON_IMP_CONVEX])

  let FACETS_OF_POLYHEDRON_EXPLICIT_DISTINCT ← prove
   r"!s:real^N->bool f a b.
        FINITE f /\
        s = affine hull s INTER INTERS f /\
        (!h. h IN f ==> ~(a h = vec 0) /\ h = {x | a h dot x <= b h}) /\
        (!f'. f' PSUBSET f ==> s PSUBSET affine hull s INTER INTERS f')
        ==> !h1 h2. h1 IN f /\ h2 IN f /\
                    s INTER {x | a h1 dot x = b h1} =
                    s INTER {x | a h2 dot x = b h2}
                    ==> h1 = h2"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"s:real^N->bool = {}") THENL
     [ASM_REWRITE_TAC [AFFINE_HULL_EMPTY, INTER_EMPTY, PSUBSET_IRREFL] THEN
      ASM_CASES_TAC (← q r"f:(real^N->bool)->bool = {}") THEN
      ASM_REWRITE_TAC [NOT_IN_EMPTY] THEN
      ASM_MESON_TAC [← SET_RULE (← q r"~(s = {}) ==> {} PSUBSET s")],
      STRIP_TAC] THEN
    SUBGOAL_THEN (← q r"polyhedron(s:real^N->bool)") ASSUME_TAC THENL
     [REWRITE_TAC [POLYHEDRON_INTER_AFFINE] THEN
      REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(relative_interior s:real^N->bool = {})") MP_TAC THENL
     [ASM_SIMP_TAC [RELATIVE_INTERIOR_EQ_EMPTY, POLYHEDRON_IMP_CONVEX],
      REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"z:real^N") MP_TAC)] THEN
    DISCH_THEN (fun th => ASSUME_TAC th THEN MP_TAC th) THEN
    MP_TAC (← ISPECL
      [← q r"s:real^N->bool", ← q r"f:(real^N->bool)->bool", ← q r"a:(real^N->bool)->real^N",
       ← q r"b:(real^N->bool)->real"] RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [] THEN ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← TAUT (← q r"(~p ==> F) ==> p")) THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"f DELETE (h2:real^N->bool)")) THEN
    ANTS_TAC THENL [ASM SET_TAC [], REWRITE_TAC [PSUBSET_ALT]] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"x:real^N") MP_TAC)) THEN
    REWRITE_TAC [IN_INTER, IN_INTERS, IN_DELETE] THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"segment[x:real^N,z]", ← q r"s:real^N->bool"]
          CONNECTED_INTER_RELATIVE_FRONTIER) THEN
    PURE_REWRITE_TAC [relative_frontier] THEN ANTS_TAC THENL
     [REWRITE_TAC [CONNECTED_SEGMENT, ← GSYM MEMBER_NOT_EMPTY] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC [CONVEX_CONTAINS_SEGMENT, AFFINE_AFFINE_HULL,
                       HULL_INC, AFFINE_IMP_CONVEX],
        EXISTS_TAC (← q r"z:real^N") THEN ASM_REWRITE_TAC [IN_INTER, ENDS_IN_SEGMENT],
        EXISTS_TAC (← q r"x:real^N") THEN ASM_REWRITE_TAC [IN_DIFF, ENDS_IN_SEGMENT]],
      ALL_TAC] THEN
    PURE_REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN
    ASM_SIMP_TAC [POLYHEDRON_IMP_CLOSED, CLOSURE_CLOSED,
           LEFT_IMP_EXISTS_THM, IN_INTER] THEN
    X_GEN_TAC (← q r"y:real^N") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (fun th => tactic_of do
      pure (STRIP_ASSUME_TAC (← REWRITE_RULE [IN_DIFF] th) THEN
          MP_TAC th)) THEN
    ASM_SIMP_TAC [RELATIVE_BOUNDARY_OF_POLYHEDRON] THEN
    MP_TAC (← ISPECL
      [← q r"s:real^N->bool", ← q r"f:(real^N->bool)->bool", ← q r"a:(real^N->bool)->real^N",
       ← q r"b:(real^N->bool)->real"] FACET_OF_POLYHEDRON_EXPLICIT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [] THEN ASM_MESON_TAC [],
      DISCH_THEN (fun th => ONCE_REWRITE_TAC [th])] THEN
    REWRITE_TAC [← SET_RULE (← q r"{y | ?x. x IN s /\ y = f x} = IMAGE f s")] THEN
    REWRITE_TAC [UNIONS_IMAGE, IN_ELIM_THM, IN_INTER] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"h:real^N->bool") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     (← q r"?k:real^N->bool. k IN f /\ ~(k = h2) /\ a k dot (y:real^N) = b k")
    STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC (← q r"h:real^N->bool = h2") THENL
       [EXISTS_TAC (← q r"h1:real^N->bool") THEN ASM_REWRITE_TAC [] THEN
        UNDISCH_TAC (← q r"s INTER {x:real^N | a(h1:real^N->bool) dot x = b h1} =
                     s INTER {x | a h2 dot x = b h2}") THEN
        REWRITE_TAC [EXTENSION, IN_INTER, IN_ELIM_THM] THEN ASM_MESON_TAC [],
        ASM_MESON_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"(a:(real^N->bool)->real^N) k dot z < b k /\ a k dot x <= b k")
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [] THEN ASM SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"y IN segment(x:real^N,z)") MP_TAC THENL
     [ASM_REWRITE_TAC [IN_OPEN_SEGMENT_ALT] THEN ASM_MESON_TAC [],
      REWRITE_TAC [IN_SEGMENT] THEN STRIP_TAC] THEN
    UNDISCH_TAC (← q r"(a:(real^N->bool)->real^N) k dot y = b k") THEN
    ASM_REWRITE_TAC [DOT_RADD, DOT_RMUL] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"(&1 - u) * x <= (&1 - u) * b /\ u * y < u * b
      ==> ~((&1 - u) * x + u * y = b)")) THEN
    ASM_SIMP_TAC [REAL_LT_LMUL_EQ, REAL_LE_LMUL_EQ, REAL_SUB_LT])

  let POLYHEDRON_MINIMAL_LEMMA ← prove
   r"!f s:real^N->bool.
        FINITE f /\
        affine hull s INTER INTERS f = s
        ==> ?f'. FINITE f' /\ f' SUBSET f /\
                 affine hull s INTER INTERS f' = s /\
                 (!f''. f'' PSUBSET f'
                        ==> s PSUBSET affine hull s INTER INTERS f'')"
   (REPEAT GEN_TAC THEN
    WF_INDUCT_TAC (← q r"CARD(f:(real^N->bool)->bool)") THEN STRIP_TAC THEN
    ASM_CASES_TAC
     (← q r"!f'. f' PSUBSET f
           ==> (s:real^N->bool) PSUBSET affine hull s INTER INTERS f'")
    THENL [ASM_MESON_TAC [SUBSET_REFL], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    REWRITE_TAC [NOT_IMP, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"f':(real^N->bool)->bool") THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"f':(real^N->bool)->bool")) THEN
    ASM_SIMP_TAC [CARD_PSUBSET] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC [FINITE_SUBSET, PSUBSET], ALL_TAC] THEN
      MATCH_MP_TAC (← SET_RULE (← q r"t SUBSET s /\ ~(t PSUBSET s) ==> s = t")) THEN
      ASM_REWRITE_TAC [] THEN
      TRANS_TAC SUBSET_TRANS (← q r"affine hull s INTER INTERS f:real^N->bool") THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC [SUBSET_REFL], ASM SET_TAC []],
      MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [] THEN ASM SET_TAC []])

  let POLYHEDRON ← prove
   r"!s. polyhedron s <=>
        ?f. FINITE f /\
            affine hull s INTER INTERS f = s /\
            (!f'. f' PSUBSET f ==> s PSUBSET affine hull s INTER INTERS f') /\
            (!h. h IN f
                 ==> (?a:real^N b. ~(a = vec 0) /\ h = {x | a dot x <= b}))"
   (GEN_TAC THEN REWRITE_TAC [polyhedron] THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"f:(real^N->bool)->bool") STRIP_ASSUME_TAC) THEN
      MP_TAC (← ISPECL [← q r"f:(real^N->bool)->bool", ← q r"s:real^N->bool"]
          POLYHEDRON_MINIMAL_LEMMA) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
        MATCH_MP_TAC (← SET_RULE
         (← q r"s SUBSET t /\ u = s ==> t INTER u = s")) THEN
        REWRITE_TAC [HULL_SUBSET] THEN ASM_MESON_TAC [],
        MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [] THEN ASM SET_TAC []],
      DISCH_THEN (X_CHOOSE_THEN (← q r"f':(real^N->bool)->bool") STRIP_ASSUME_TAC) THEN
      MP_TAC (← ISPEC (← q r"affine hull s:real^N->bool") AFFINE_IMP_POLYHEDRON) THEN
      REWRITE_TAC [polyhedron, AFFINE_AFFINE_HULL] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f'':(real^N->bool)->bool") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"f' UNION f'':(real^N->bool)->bool") THEN
      ASM_REWRITE_TAC [FINITE_UNION, FORALL_IN_UNION, INTERS_UNION] THEN
      ASM SET_TAC []])

  pure { FACET_OF_POLYHEDRON, FACE_OF_POLYHEDRON, FACE_OF_POLYHEDRON_SUBSET_FACET,
         FACE_OF_POLYHEDRON_FACE_OF_FACET, EXPOSED_FACE_OF_POLYHEDRON,
         FACE_OF_POLYHEDRON_POLYHEDRON, FINITE_POLYHEDRON_FACES,
         FINITE_POLYHEDRON_EXPOSED_FACES, FINITE_POLYHEDRON_EXTREME_POINTS,
         FINITE_POLYHEDRON_FACETS, RELATIVE_INTERIOR_OF_POLYHEDRON,
         RELATIVE_BOUNDARY_OF_POLYHEDRON, RELATIVE_FRONTIER_OF_POLYHEDRON,
         RELATIVE_FRONTIER_OF_POLYHEDRON_ALT, FACETS_OF_POLYHEDRON_EXPLICIT_DISTINCT,
         POLYHEDRON_MINIMAL_LEMMA, POLYHEDRON }

/- ------------------------------------------------------------------------- -/
/- Polyhedra as having finitely many faces; polytopes vs polyhedra;         -/
/- polytope as union of convex hulls of facets. (polytope.ml 5567-5965)      -/
/- ------------------------------------------------------------------------- -/

structure POM where
  POLYHEDRON_EQ_FINITE_EXPOSED_FACES : thm
  POLYHEDRON_EQ_FINITE_FACES : thm
  POLYHEDRON_TRANSLATION_EQ : thm
  POLYHEDRON_LINEAR_IMAGE_EQ : thm
  POLYHEDRON_NEGATIONS : thm
  POLYHEDRON_LINEAR_PREIMAGE : thm
  POLYTOPE_EQ_BOUNDED_POLYHEDRON : thm
  POLYTOPE_INTER : thm
  POLYTOPE_INTER_POLYHEDRON : thm
  POLYHEDRON_INTER_POLYTOPE : thm
  POLYTOPE_IMP_POLYHEDRON : thm
  POLYTOPE_FACET_EXISTS : thm
  POLYHEDRON_INTERVAL : thm
  POLYHEDRON_CONVEX_HULL : thm
  POLYTOPE_UNION_CONVEX_HULL_FACETS : thm
  deriving Inhabited

set_option maxHeartbeats 8000000 in
@[nospecialize]
def setupPOM [HolBase] (D : PolytopeDeps) (BPOA : POA) (BPOD : POD) (BPOE : POE) (BPOG : POG) (BPOJ : POJ) (BPOL : POL) : ExceptT String IO POM := do
  -- @@SCOPE BEGIN
  let { add_linear_invariants, add_translation_invariants, ASM_MESON_TAC, GEOM_ORIGIN_TAC,
        INT_REDUCE_CONV, MESON, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, SET_RULE, SET_TAC,
        VECTOR_ARITH, VECTOR_ARITH_TAC, .. } := D.cvx
  let { CONJ_ASSOC, CONTRAPOS_THM, EMPTY_SUBSET, EQ_IMP, EXISTS_IN_GSPEC, EXISTS_REFL,
        EXTENSION, FINITE_IMAGE, FINITE_IMAGE_INJ_EQ, FINITE_RESTRICT, FINITE_SUBSET,
        FORALL_AND_THM, FORALL_IN_GSPEC, .. } := D.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_IN_UNIONS, IMP_CONJ, IMP_IMP, IN_DIFF, INSERT_SUBSET,
        INTER_SUBSET, INTERS_GSPEC, .. } := D.cvx.core2
  let { IN_ELIM_THM, IN_INTER, IN_INTERS, IN_UNION, IN_UNIONS, IN_UNIV, LEFT_AND_EXISTS_THM,
        LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY, MONO_EXISTS, NOT_EXISTS_THM, NOT_IMP,
        NOT_INSERT_EMPTY, REAL_ABS_NEG, .. } := D.cvx.core3
  let { REAL_ENTIRE, REAL_INV_LE_1, REAL_LE_INV_EQ, REAL_LE_LDIV_EQ, REAL_LE_LT,
        REAL_LE_MUL, REAL_LE_RDIV_EQ, REAL_LE_REFL, REAL_LE_RMUL_EQ, REAL_LT_DIV,
        REAL_LT_DIV2_EQ, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_INV_EQ, REAL_LT_LE,
        REAL_LT_MIN, REAL_LT_REFL, .. } := D.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LINV, REAL_NOT_LE, REAL_SUB_LE, REAL_SUB_LT,
        REAL_SUB_REFL, REAL_SUB_RZERO, RIGHT_EXISTS_AND_THM, RIGHT_FORALL_IMP_THM,
        RIGHT_IMP_EXISTS_THM, SET_PROVE_CASES, SIMPLE_IMAGE, SKOLEM_THM, SUBSET,
        SUBSET_ANTISYM, SUBSET_INTER, SUBSET_REFL, SUBSET_TRANS, .. } := D.cvx.core5
  let { real_abs, real_div, real_ge, SUBSET_UNIV, SWAP_EXISTS_THM, UNWIND_THM2, .. } :=
        D.cvx.core6
  let { HULL_INC, HULL_MINIMAL, HULL_MONO, HULL_SUBSET, REAL_HALF, SUBSET_HULL, .. } :=
        D.cvx.misc
  let { DIST_0, .. } := D.cvx.vec1
  let { NORM_MUL, NORM_POS_LT, SPAN_MUL, SPAN_SUPERSET, .. } := D.cvx.vec3
  let { dist, VECTOR_ADD_LID, VECTOR_ADD_RID, VECTOR_MUL_ASSOC, VECTOR_MUL_EQ_0,
        VECTOR_MUL_LID, VECTOR_MUL_LZERO, VECTOR_MUL_RZERO, .. } := D.cvx.vec4
  let { OPEN_IN_INTER, OPEN_IN_SUBTOPOLOGY_INTER_SUBSET, OPEN_IN_SUBTOPOLOGY_REFL, .. } :=
        D.cvx.met
  let { BOUNDED_POS, BOUNDED_SUBSET, CLOSED_TRANSLATION_EQ, .. } := D.cvx.top1
  let { CLOSURE_SUBSET, COMPACT_EQ_BOUNDED_CLOSED, COMPACT_INTER_CLOSED, CONNECTED_OPEN_IN,
        CONNECTED_SEGMENT, .. } := D.cvx.top2
  let { DISTANCE_ATTAINS_SUP, ENDS_IN_SEGMENT, .. } := D.cvx.top3
  let { IN_BALL, IN_SEGMENT, .. } := D.cvx.top4
  let { closed, OPEN_IN_OPEN, segment, TOPSPACE_EUCLIDEAN, TOPSPACE_EUCLIDEAN_SUBTOPOLOGY,
        .. } := D.cvx.top5
  let { INJECTIVE_IMAGE, INT_LT_REFL, SURJECTIVE_IMAGE, .. } := D.qses
  let { ADJOINT_CLAUSES, LINEAR_NEGATION, QUANTIFY_SURJECTION_THM, .. } := D.qvec
  let { BOUNDED_INTER, CLOSED_INJECTIVE_LINEAR_IMAGE_EQ, .. } := D.qtop
  let { AFF_DIM_EMPTY, AFF_DIM_SING, AFFINE_AFFINE_HULL, AFFINE_HULL_EQ_SPAN,
        AFFINE_IMP_CONVEX, .. } := D.qcvx1
  let { COMPACT_SEGMENT, CONVEX_CONVEX_HULL, CONVEX_HALFSPACE_LE, CONVEX_HULL_2,
        CONVEX_HULL_EQ, CONVEX_LINEAR_IMAGE_EQ, .. } := D.qcvx2
  let { CONVEX_TRANSLATION_EQ, IN_RELATIVE_INTERIOR, OPEN_IN_RELATIVE_INTERIOR,
        relative_frontier, RELATIVE_INTERIOR_EQ_EMPTY, RELATIVE_INTERIOR_SUBSET,
        SEGMENT_CONVEX_HULL, SUPPORTING_HYPERPLANE_RELATIVE_FRONTIER, .. } := D.qcvx3
  let { face_of, FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE, FACE_OF_LINEAR_IMAGE,
        FACE_OF_TRANSLATION_EQ, SUBSET_OF_FACE_OF, .. } := BPOA
  let { EXPOSED_FACE_OF, exposed_face_of, EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE, ..
        } := BPOD
  let { FACE_OF_SING, .. } := BPOE
  let { EXTREME_POINT_EXISTS_CONVEX, FACET_OF_IMP_SUBSET, KREIN_MILMAN_MINKOWSKI, .. } :=
        BPOG
  let { FINITE_POLYTOPE_FACES, polyhedron, POLYHEDRON_AFFINE_HULL, POLYHEDRON_EMPTY,
        POLYHEDRON_HALFSPACE_LE, POLYHEDRON_IMP_CLOSED, POLYHEDRON_IMP_CONVEX,
        POLYHEDRON_INTER, POLYHEDRON_INTERS, polytope, POLYTOPE_CONVEX_HULL,
        POLYTOPE_IMP_BOUNDED, POLYTOPE_IMP_CLOSED, POLYTOPE_IMP_COMPACT,
        POLYTOPE_IMP_CONVEX, POLYTOPE_INTERVAL, .. } := BPOJ
  let { FACE_OF_POLYHEDRON_SUBSET_FACET, FINITE_POLYHEDRON_EXPOSED_FACES,
        FINITE_POLYHEDRON_EXTREME_POINTS, FINITE_POLYHEDRON_FACES,
        RELATIVE_INTERIOR_OF_POLYHEDRON, .. } := BPOL
  -- @@SCOPE END

  let POLYHEDRON_EQ_FINITE_EXPOSED_FACES ← prove
   r"!s:real^N->bool.
    polyhedron s <=> closed s /\ convex s /\ FINITE {f | f exposed_face_of s}"
   (GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC [POLYHEDRON_IMP_CLOSED, POLYHEDRON_IMP_CONVEX,
                  FINITE_POLYHEDRON_EXPOSED_FACES] THEN
    ASM_CASES_TAC (← q r"s:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [POLYHEDRON_EMPTY] THEN
    ABBREV_TAC
     (← q r"f = {h:real^N->bool | h exposed_face_of s /\ ~(h = {}) /\ ~(h = s)}") THEN
    SUBGOAL_THEN (← q r"FINITE(f:(real^N->bool)->bool)") ASSUME_TAC THENL
     [EXPAND_TAC "f" THEN
      ONCE_REWRITE_TAC [← SET_RULE
       (← q r"{x | P x /\ Q x} = {x | x IN {x | P x} /\ Q x}")] THEN
      ASM_SIMP_TAC [FINITE_RESTRICT],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!h:real^N->bool.
          h IN f
          ==> h face_of s /\
              ?a b. ~(a = vec 0) /\
                    s SUBSET {x | a dot x <= b} /\
                    h = s INTER {x | a dot x = b}")
    MP_TAC THENL
     [EXPAND_TAC "f" THEN REWRITE_TAC [EXPOSED_FACE_OF, IN_ELIM_THM] THEN
      MESON_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM, FORALL_AND_THM,
                 ← TAUT (← q r"a ==> b /\ c <=> (a ==> b) /\ (a ==> c)")] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"a:(real^N->bool)->real^N") MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:(real^N->bool)->real") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     (← q r"s = affine hull s INTER
          INTERS {{x:real^N | a(h:real^N->bool) dot x <= b h} | h IN f}")
    SUBST1_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC POLYHEDRON_INTER THEN REWRITE_TAC [POLYHEDRON_AFFINE_HULL] THEN
      MATCH_MP_TAC POLYHEDRON_INTERS THEN ONCE_REWRITE_TAC [SIMPLE_IMAGE] THEN
      ASM_SIMP_TAC [FINITE_IMAGE, FORALL_IN_IMAGE, POLYHEDRON_HALFSPACE_LE]] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC [SUBSET_INTER, HULL_SUBSET,
                 ← SET_RULE (← q r"s SUBSET INTERS f <=> !h. h IN f ==> s SUBSET h")] THEN
    ASM_REWRITE_TAC [FORALL_IN_GSPEC] THEN
    REWRITE_TAC [SUBSET, IN_INTER, IN_INTERS, FORALL_IN_GSPEC] THEN
    X_GEN_TAC (← q r"p:real^N") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC (← TAUT (← q r"(~p ==> F) ==> p")) THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"~(relative_interior(s:real^N->bool) = {})") MP_TAC THENL
     [ASM_SIMP_TAC [RELATIVE_INTERIOR_EQ_EMPTY],
      GEN_REWRITE_TAC LAND_CONV [← GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"c:real^N"))] THEN
    SUBGOAL_THEN
     (← q r"?x:real^N. x IN segment[c,p] /\ x IN (s DIFF relative_interior s)")
    MP_TAC THENL
     [MP_TAC (← ISPEC (← q r"segment[c:real^N,p]") CONNECTED_OPEN_IN) THEN
      REWRITE_TAC [CONNECTED_SEGMENT, NOT_EXISTS_THM] THEN
      DISCH_THEN (MP_TAC o SPECL
       [← q r"segment[c:real^N,p] INTER relative_interior s",
        ← q r"segment[c:real^N,p] INTER (UNIV DIFF s)"]) THEN
      ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC [IN_DIFF, NOT_EXISTS_THM] THEN DISCH_TAC THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_SUBSET THEN
        EXISTS_TAC (← q r"affine hull s:real^N->bool") THEN
        SIMP_TAC [OPEN_IN_RELATIVE_INTERIOR, TOPSPACE_EUCLIDEAN_SUBTOPOLOGY,
          OPEN_IN_SUBTOPOLOGY_REFL, SUBSET_UNIV, OPEN_IN_INTER,
          TOPSPACE_EUCLIDEAN] THEN
        REWRITE_TAC [SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
        SIMP_TAC [AFFINE_IMP_CONVEX, AFFINE_AFFINE_HULL] THEN
        ASM_REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET] THEN
        ASM_MESON_TAC [RELATIVE_INTERIOR_SUBSET, HULL_INC, SUBSET],
        REWRITE_TAC [OPEN_IN_OPEN] THEN EXISTS_TAC (← q r"(:real^N) DIFF s") THEN
        ASM_REWRITE_TAC [← GSYM closed],
       MP_TAC (← ISPEC (← q r"s:real^N->bool") RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC [],
       MP_TAC (← ISPEC (← q r"s:real^N->bool") RELATIVE_INTERIOR_SUBSET) THEN SET_TAC [],
        REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_INTER] THEN
        ASM_MESON_TAC [ENDS_IN_SEGMENT],
        REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_DIFF, IN_INTER, IN_UNIV] THEN
        ASM_MESON_TAC [ENDS_IN_SEGMENT]],
      REWRITE_TAC [IN_SEGMENT, LEFT_AND_EXISTS_THM] THEN
      ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
      REWRITE_TAC [← GSYM CONJ_ASSOC, RIGHT_EXISTS_AND_THM, UNWIND_THM2] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"l:real") MP_TAC) THEN
      ASM_CASES_TAC (← q r"l = &0") THEN
      ASM_REWRITE_TAC [VECTOR_ADD_RID, VECTOR_MUL_LZERO, REAL_SUB_RZERO,
                       VECTOR_MUL_LID, IN_DIFF] THEN
      ASM_CASES_TAC (← q r"l = &1") THEN
      ASM_REWRITE_TAC [VECTOR_ADD_LID, VECTOR_MUL_LZERO, REAL_SUB_REFL,
                       VECTOR_MUL_LID, IN_DIFF] THEN
      ASM_REWRITE_TAC [REAL_LE_LT] THEN STRIP_TAC] THEN
    ABBREV_TAC (← q r"x:real^N = (&1 - l) % c + l % p") THEN
    SUBGOAL_THEN (← q r"?h:real^N->bool. h IN f /\ x IN h") STRIP_ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"(&1 - l) % c + l % p:real^N"]
        SUPPORTING_HYPERPLANE_RELATIVE_FRONTIER) THEN
      REWRITE_TAC [relative_frontier, IN_DIFF] THEN
      ASM_SIMP_TAC [← REWRITE_RULE [SUBSET] CLOSURE_SUBSET] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"d:real^N") STRIP_ASSUME_TAC) THEN
      EXPAND_TAC "f" THEN
      EXISTS_TAC (← q r"s INTER {y:real^N | d dot y = d dot x}") THEN
      ASM_REWRITE_TAC [IN_INTER, IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC EXPOSED_FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE THEN
        ASM_SIMP_TAC [real_ge, ← REWRITE_RULE [SUBSET] CLOSURE_SUBSET],
        ASM SET_TAC [],
        REWRITE_TAC [EXTENSION, IN_INTER, IN_ELIM_THM] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"c:real^N")) THEN
        ASM_MESON_TAC [SUBSET, REAL_LT_REFL, RELATIVE_INTERIOR_SUBSET]],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"{y:real^N | a(h:real^N->bool) dot y = b h} face_of
                  {y | a h dot y <= b h}")
    MP_TAC THENL
     [MATCH_MP_TAC (← MESON []
       (← q r"(t INTER s) face_of t /\ t INTER s = s ==> s face_of t")) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
        REWRITE_TAC [IN_ELIM_THM, CONVEX_HALFSPACE_LE],
        SET_TAC [REAL_LE_REFL]],
      ALL_TAC] THEN
    REWRITE_TAC [face_of] THEN
    DISCH_THEN (MP_TAC o SPECL [← q r"c:real^N", ← q r"p:real^N", ← q r"x:real^N"] o
          CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC [IN_ELIM_THM, NOT_IMP, ← GSYM CONJ_ASSOC] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP (← REWRITE_RULE [SUBSET]
        RELATIVE_INTERIOR_SUBSET)) THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC [],
      ASM SET_TAC [],
      REWRITE_TAC [IN_SEGMENT] THEN ASM SET_TAC [],
      STRIP_TAC] THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"h:real^N->bool", ← q r"s:real^N->bool"]
          SUBSET_OF_FACE_OF) THEN
    ASM SET_TAC [])

  let POLYHEDRON_EQ_FINITE_FACES ← prove
   r"!s:real^N->bool.
        polyhedron s <=>
        closed s /\ convex s /\ FINITE {f | f face_of s}"
   (GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC [POLYHEDRON_IMP_CLOSED, POLYHEDRON_IMP_CONVEX,
                  FINITE_POLYHEDRON_FACES] THEN
    REWRITE_TAC [POLYHEDRON_EQ_FINITE_EXPOSED_FACES] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC (← q r"{f:real^N->bool | f face_of s}") THEN
    ASM_REWRITE_TAC [] THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM, exposed_face_of])

  let POLYHEDRON_TRANSLATION_EQ ← prove
   r"!a s. polyhedron (IMAGE (\x:real^N. a + x) s) <=> polyhedron s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [POLYHEDRON_EQ_FINITE_FACES] THEN
    REWRITE_TAC [CLOSED_TRANSLATION_EQ] THEN AP_TERM_TAC THEN
    REWRITE_TAC [CONVEX_TRANSLATION_EQ] THEN AP_TERM_TAC THEN
    MP_TAC (← ISPEC (← q r"IMAGE (\x:real^N. a + x)") QUANTIFY_SURJECTION_THM) THEN
    REWRITE_TAC [SURJECTIVE_IMAGE, EXISTS_REFL,
      ← VECTOR_ARITH (← q r"a + x:real^N = y <=> x = y - a")] THEN
    DISCH_THEN (fun th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC [FACE_OF_TRANSLATION_EQ] THEN
    MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
    MATCH_MP_TAC (← MESON []
     (← q r"(!x y. Q x y ==> R x y) ==> (!x y. P x /\ P y /\ Q x y ==> R x y)")) THEN
    REWRITE_TAC [INJECTIVE_IMAGE] THEN VECTOR_ARITH_TAC)

  add_translation_invariants [POLYHEDRON_TRANSLATION_EQ]

  let POLYHEDRON_LINEAR_IMAGE_EQ ← prove
   r"!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> (polyhedron (IMAGE f s) <=> polyhedron s)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [POLYHEDRON_EQ_FINITE_FACES] THEN
    BINOP_TAC THENL
     [ASM_MESON_TAC [CLOSED_INJECTIVE_LINEAR_IMAGE_EQ], ALL_TAC] THEN
    BINOP_TAC THENL [ASM_MESON_TAC [CONVEX_LINEAR_IMAGE_EQ], ALL_TAC] THEN
    MP_TAC (← ISPEC (← q r"IMAGE (f:real^M->real^N)") QUANTIFY_SURJECTION_THM) THEN
    ASM_REWRITE_TAC [SURJECTIVE_IMAGE] THEN
    DISCH_THEN (fun th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    MP_TAC (← ISPEC (← q r"f:real^M->real^N") FACE_OF_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
    FIRST_ASSUM (ASSUME_TAC o GEN_REWRITE_RULE I [← GSYM INJECTIVE_IMAGE]) THEN
    ASM_REWRITE_TAC [IMP_CONJ])

  add_linear_invariants [POLYHEDRON_LINEAR_IMAGE_EQ]

  let POLYHEDRON_NEGATIONS ← prove
   r"!s:real^N->bool. polyhedron s ==> polyhedron(IMAGE (--) s)"
   (GEN_TAC THEN MATCH_MP_TAC EQ_IMP THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC POLYHEDRON_LINEAR_IMAGE_EQ THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"--x:real^N = y <=> x = --y"), EXISTS_REFL] THEN
    REWRITE_TAC [LINEAR_NEGATION] THEN VECTOR_ARITH_TAC)

  let POLYHEDRON_LINEAR_PREIMAGE ← (do
    let lemma ← prove
     r"{x | f x IN INTERS s} = INTERS {{x | f x IN c} | c IN s}"
     (REWRITE_TAC [INTERS_GSPEC] THEN SET_TAC [])
    prove
     r"!f:real^M->real^N s.
        linear f /\ polyhedron s ==> polyhedron {x | f x IN s}"
     (REPEAT GEN_TAC THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [polyhedron] THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
      ONCE_REWRITE_TAC [lemma] THEN MATCH_MP_TAC POLYHEDRON_INTERS THEN
      ASM_SIMP_TAC [SIMPLE_IMAGE, FINITE_IMAGE, FORALL_IN_IMAGE] THEN
      X_GEN_TAC (← q r"h:real^N->bool") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"h:real^N->bool")) THEN
      ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        pure (ONCE_REWRITE_TAC [← GSYM (← MATCH_MP ADJOINT_CLAUSES th)])) THEN
      REWRITE_TAC [POLYHEDRON_HALFSPACE_LE]))

  /- ----------------------------------------------------------------------- -/
  /- Relation between polytopes and polyhedra.                               -/
  /- ----------------------------------------------------------------------- -/

  let POLYTOPE_EQ_BOUNDED_POLYHEDRON ← prove
   r"!s:real^N->bool. polytope s <=> polyhedron s /\ bounded s"
   (GEN_TAC THEN EQ_TAC THENL
     [SIMP_TAC [FINITE_POLYTOPE_FACES, POLYHEDRON_EQ_FINITE_FACES,
                POLYTOPE_IMP_CLOSED, POLYTOPE_IMP_CONVEX, POLYTOPE_IMP_BOUNDED],
      STRIP_TAC THEN REWRITE_TAC [polytope] THEN
      EXISTS_TAC (← q r"{v:real^N | v extreme_point_of s}") THEN
      ASM_SIMP_TAC [FINITE_POLYHEDRON_EXTREME_POINTS] THEN
      MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
      ASM_SIMP_TAC [COMPACT_EQ_BOUNDED_CLOSED, POLYHEDRON_IMP_CLOSED,
                    POLYHEDRON_IMP_CONVEX]])

  let POLYTOPE_INTER ← prove
   r"!s t. polytope s /\ polytope t ==> polytope(s INTER t)"
   (SIMP_TAC [POLYTOPE_EQ_BOUNDED_POLYHEDRON, POLYHEDRON_INTER, BOUNDED_INTER])

  let POLYTOPE_INTER_POLYHEDRON ← prove
   r"!s t:real^N->bool. polytope s /\ polyhedron t ==> polytope(s INTER t)"
   (SIMP_TAC [POLYTOPE_EQ_BOUNDED_POLYHEDRON, POLYHEDRON_INTER] THEN
    MESON_TAC [BOUNDED_SUBSET, INTER_SUBSET])

  let POLYHEDRON_INTER_POLYTOPE ← prove
   r"!s t:real^N->bool. polyhedron s /\ polytope t ==> polytope(s INTER t)"
   (SIMP_TAC [POLYTOPE_EQ_BOUNDED_POLYHEDRON, POLYHEDRON_INTER] THEN
    MESON_TAC [BOUNDED_SUBSET, INTER_SUBSET])

  let POLYTOPE_IMP_POLYHEDRON ← prove
   r"!p. polytope p ==> polyhedron p"
   (SIMP_TAC [POLYTOPE_EQ_BOUNDED_POLYHEDRON])

  let POLYTOPE_FACET_EXISTS ← prove
   r"!p:real^N->bool. polytope p /\ &0 < aff_dim p ==> ?f. f facet_of p"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"p:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [AFF_DIM_EMPTY] THEN CONV_TAC INT_REDUCE_CONV THEN
    STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"p:real^N->bool") EXTREME_POINT_EXISTS_CONVEX) THEN
    ASM_SIMP_TAC [POLYTOPE_IMP_COMPACT, POLYTOPE_IMP_CONVEX] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"v:real^N")) THEN
    MP_TAC (← ISPECL [← q r"p:real^N->bool", ← q r"{v:real^N}"]
      FACE_OF_POLYHEDRON_SUBSET_FACET) THEN
    ANTS_TAC THENL [ALL_TAC, MESON_TAC []] THEN
    ASM_SIMP_TAC [POLYTOPE_IMP_POLYHEDRON, FACE_OF_SING, NOT_INSERT_EMPTY] THEN
    ASM_MESON_TAC [AFF_DIM_SING, INT_LT_REFL])

  let POLYHEDRON_INTERVAL ← prove
   r"!a b. polyhedron(interval[a,b])"
   (MESON_TAC [POLYTOPE_IMP_POLYHEDRON, POLYTOPE_INTERVAL])

  let POLYHEDRON_CONVEX_HULL ← prove
   r"!s. FINITE s ==> polyhedron(convex hull s)"
   (SIMP_TAC [POLYTOPE_CONVEX_HULL, POLYTOPE_IMP_POLYHEDRON])

  /- ----------------------------------------------------------------------- -/
  /- Polytope is union of convex hulls of facets plus any point inside.      -/
  /- ----------------------------------------------------------------------- -/

  let POLYTOPE_UNION_CONVEX_HULL_FACETS ← (do
    let lemma ← SET_RULE (← q r"{f x | p x} = {y | ?x. p x /\ y = f x}")
    prove
     r"!s p:real^N->bool.
        polytope p /\ &0 < aff_dim p /\ ~(s = {}) /\ s SUBSET p
        ==> p = UNIONS { convex hull (s UNION f) | f facet_of p}"
     (MATCH_MP_TAC SET_PROVE_CASES THEN REWRITE_TAC [] THEN
      X_GEN_TAC (← q r"a:real^N") THEN ONCE_REWRITE_TAC [lemma] THEN
      GEOM_ORIGIN_TAC (← q r"a:real^N") THEN ONCE_REWRITE_TAC [← GSYM lemma] THEN
      X_GEN_TAC (← q r"s:real^N->bool") THEN DISCH_THEN (K ALL_TAC : thm → tactic) THEN
      MP_TAC (← SET_RULE (← q r"(vec 0:real^N) IN (vec 0 INSERT s)")) THEN
      SPEC_TAC (← q r"(vec 0:real^N) INSERT s", ← q r"s:real^N->bool") THEN
      X_GEN_TAC (← q r"s:real^N->bool") THEN DISCH_TAC THEN
      X_GEN_TAC (← q r"p:real^N->bool") THEN STRIP_TAC THEN
      FIRST_ASSUM (STRIP_ASSUME_TAC o
       GEN_REWRITE_RULE I [POLYTOPE_EQ_BOUNDED_POLYHEDRON]) THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [ALL_TAC,
        REWRITE_TAC [SUBSET, FORALL_IN_UNIONS, IMP_CONJ] THEN
        REWRITE_TAC [FORALL_IN_GSPEC, RIGHT_FORALL_IMP_THM] THEN
        X_GEN_TAC (← q r"f:real^N->bool") THEN DISCH_TAC THEN
        REWRITE_TAC [← GSYM SUBSET] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC (← q r"convex hull p:real^N->bool") THEN CONJ_TAC THENL
         [MATCH_MP_TAC HULL_MONO THEN
          FIRST_ASSUM (MP_TAC o MATCH_MP FACET_OF_IMP_SUBSET) THEN ASM SET_TAC [],
          ASM_MESON_TAC [CONVEX_HULL_EQ, POLYHEDRON_IMP_CONVEX, SUBSET_REFL]]] THEN
      REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"v:real^N") THEN DISCH_TAC THEN
      ASM_CASES_TAC (← q r"v:real^N = vec 0") THENL
       [MP_TAC (← ISPEC (← q r"p:real^N->bool") POLYTOPE_FACET_EXISTS) THEN
        ASM_REWRITE_TAC [IN_UNIONS, EXISTS_IN_GSPEC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
        ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [HULL_INC, IN_UNION],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"?t. &1 < t /\ ~((t % v:real^N) IN p)") STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"B:real") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"max (&2) ((B + &1) / norm (v:real^N))") THEN
        CONJ_TAC THENL [REAL_ARITH_TAC, ALL_TAC] THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o
         GEN_REWRITE_RULE BINDER_CONV [← GSYM CONTRAPOS_THM]) THEN
        ASM_SIMP_TAC [NORM_MUL, ← GSYM REAL_LE_RDIV_EQ, NORM_POS_LT] THEN
        MATCH_MP_TAC (← REAL_ARITH (← q r"a < b ==> ~(abs(max (&2) b) <= a)")) THEN
        ASM_SIMP_TAC [REAL_LT_DIV2_EQ, NORM_POS_LT] THEN REAL_ARITH_TAC,
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(vec 0:real^N) IN p") ASSUME_TAC THENL
       [ASM SET_TAC [], ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"segment[vec 0,t % v:real^N] INTER p", ← q r"vec 0:real^N"]
            DISTANCE_ATTAINS_SUP) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC [COMPACT_INTER_CLOSED, POLYHEDRON_IMP_CLOSED, COMPACT_SEGMENT,
                      ← GSYM MEMBER_NOT_EMPTY, IN_INTER] THEN
        ASM_MESON_TAC [ENDS_IN_SEGMENT],
        REWRITE_TAC [IN_INTER, ← GSYM CONJ_ASSOC, IMP_CONJ] THEN
        REWRITE_TAC [segment, FORALL_IN_GSPEC, EXISTS_IN_GSPEC] THEN
        REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_ADD_LID, DIST_0] THEN
        REWRITE_TAC [IMP_IMP, ← GSYM CONJ_ASSOC, NORM_MUL, REAL_MUL_ASSOC] THEN
        ASM_SIMP_TAC [REAL_LE_RMUL_EQ, NORM_POS_LT, LEFT_IMP_EXISTS_THM,
                      ← REAL_ARITH (← q r"&1 < t ==> &0 < abs t")] THEN
        X_GEN_TAC (← q r"u:real") THEN
        ASM_CASES_TAC (← q r"u = &1") THEN ASM_REWRITE_TAC [VECTOR_MUL_LID] THEN
        REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        ASM_SIMP_TAC [real_abs] THEN DISCH_TAC] THEN
      SUBGOAL_THEN (← q r"inv(t) <= u") ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC [REAL_INV_LE_1, REAL_LT_IMP_LE, REAL_LE_INV_EQ,
                      ← REAL_ARITH (← q r"&1 < t ==> &0 <= t")] THEN
        ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, VECTOR_MUL_LID,
                      ← REAL_ARITH (← q r"&1 < t ==> ~(t = &0)")],
        ALL_TAC] THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP (← REAL_ARITH (← q r"&1 < t ==> &0 < t"))) THEN
      SUBGOAL_THEN (← q r"&0 < u /\ u < &1") STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC [REAL_LT_LE] THEN
        DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
        UNDISCH_TAC (← q r"inv t <= &0") THEN REWRITE_TAC [REAL_NOT_LE] THEN
        ASM_REWRITE_TAC [REAL_LT_INV_EQ],
        ALL_TAC] THEN
      MATCH_MP_TAC (← SET_RULE (← q r"!t. t SUBSET s /\ x IN t ==> x IN s")) THEN
      EXISTS_TAC (← q r"convex hull {vec 0:real^N,u % t % v}") THEN CONJ_TAC THENL
       [ALL_TAC,
        REWRITE_TAC [CONVEX_HULL_2, VECTOR_MUL_RZERO, VECTOR_ADD_LID] THEN
        REWRITE_TAC [IN_ELIM_THM] THEN
        MAP_EVERY EXISTS_TAC [← q r"&1 - inv(u * t)", ← q r"inv(u * t):real"] THEN
        REWRITE_TAC [← REAL_ARITH (← q r"&1 - x + x = &1"), REAL_SUB_LE, REAL_LE_INV_EQ] THEN
        ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_IMP_LE, VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC [← GSYM REAL_MUL_ASSOC, REAL_ENTIRE, REAL_MUL_LINV,
                      REAL_LT_IMP_NZ, VECTOR_MUL_LID] THEN
        MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_SIMP_TAC [← GSYM REAL_LE_LDIV_EQ] THEN
        ASM_REWRITE_TAC [real_div, REAL_MUL_LID]] THEN
      SUBGOAL_THEN
       (← q r"(u % t % v:real^N) IN (p DIFF relative_interior p)")
      MP_TAC THENL
       [ALL_TAC,
        ASM_SIMP_TAC [RELATIVE_INTERIOR_OF_POLYHEDRON] THEN
        DISCH_THEN (MP_TAC o MATCH_MP (← SET_RULE
         (← q r"x IN s DIFF (s DIFF t) ==> x IN t"))) THEN
        REWRITE_TAC [IN_UNIONS, EXISTS_IN_GSPEC] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"f:real^N->bool") STRIP_ASSUME_TAC) THEN
        MATCH_MP_TAC (← SET_RULE
         (← q r"(?s. s IN f /\ t SUBSET s) ==> t SUBSET UNIONS f")) THEN
        REWRITE_TAC [EXISTS_IN_GSPEC] THEN EXISTS_TAC (← q r"f:real^N->bool") THEN
        ASM_SIMP_TAC [SUBSET_HULL, CONVEX_CONVEX_HULL] THEN
        ASM_SIMP_TAC [HULL_INC, IN_UNION, INSERT_SUBSET, EMPTY_SUBSET]] THEN
      ASM_REWRITE_TAC [IN_DIFF, IN_RELATIVE_INTERIOR] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"e:real") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC [SUBSET, IN_BALL, IN_INTER, dist] THEN
      ABBREV_TAC (← q r"k = min (e / &2 / norm(t % v:real^N)) (&1 - u)") THEN
      SUBGOAL_THEN (← q r"&0 < k") ASSUME_TAC THENL
       [EXPAND_TAC "k" THEN REWRITE_TAC [REAL_LT_MIN] THEN
        ASM_REWRITE_TAC [REAL_SUB_LT] THEN MATCH_MP_TAC REAL_LT_DIV THEN
        ASM_SIMP_TAC [REAL_HALF, NORM_POS_LT, VECTOR_MUL_EQ_0, REAL_LT_IMP_NZ],
        ALL_TAC] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"(u + k) % t % v:real^N")) THEN
      REWRITE_TAC [← VECTOR_ARITH (← q r"u % x - (u + k) % x:real^N = --k % x")] THEN
      ONCE_REWRITE_TAC [NORM_MUL] THEN REWRITE_TAC [REAL_ABS_NEG, NOT_IMP] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC (← REAL_ARITH (← q r"&0 < e /\ x <= e / &2 ==> x < e")) THEN
        ASM_SIMP_TAC [← GSYM REAL_LE_RDIV_EQ, NORM_POS_LT, VECTOR_MUL_EQ_0,
                      REAL_LT_IMP_NZ] THEN
        ASM_SIMP_TAC [real_abs, REAL_LT_IMP_LE] THEN
        EXPAND_TAC "k" THEN REAL_ARITH_TAC,
        ASM_SIMP_TAC [AFFINE_HULL_EQ_SPAN, HULL_INC] THEN
        REPEAT (MATCH_MP_TAC SPAN_MUL) THEN ASM_SIMP_TAC [SPAN_SUPERSET],
        DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"u + k:real")) THEN
        ASM_REWRITE_TAC [NOT_IMP] THEN
        MATCH_MP_TAC (← REAL_ARITH
         (← q r"&0 <= u /\ &0 < x /\ x <= &1 - u
          ==> (&0 <= u + x /\ u + x <= &1) /\ ~(u + x <= u)")) THEN
        ASM_REWRITE_TAC [] THEN EXPAND_TAC "k" THEN REAL_ARITH_TAC]))

  pure { POLYHEDRON_EQ_FINITE_EXPOSED_FACES, POLYHEDRON_EQ_FINITE_FACES,
         POLYHEDRON_TRANSLATION_EQ, POLYHEDRON_LINEAR_IMAGE_EQ, POLYHEDRON_NEGATIONS,
         POLYHEDRON_LINEAR_PREIMAGE, POLYTOPE_EQ_BOUNDED_POLYHEDRON, POLYTOPE_INTER,
         POLYTOPE_INTER_POLYHEDRON, POLYHEDRON_INTER_POLYTOPE, POLYTOPE_IMP_POLYHEDRON,
         POLYTOPE_FACET_EXISTS, POLYHEDRON_INTERVAL, POLYHEDRON_CONVEX_HULL,
         POLYTOPE_UNION_CONVEX_HULL_FACETS }

/- ------------------------------------------------------------------------- -/
/- Finitely generated cone is polyhedral, and conversely.                    -/
/- (polytope.ml 5965-6194)                                                   -/
/- ------------------------------------------------------------------------- -/

structure PON where
  POLYHEDRON_CONVEX_CONE_HULL : thm
  CLOSED_CONVEX_CONE_HULL : thm
  POLYHEDRON_CONVEX_CONE_HULL_POLYTOPE : thm
  POLYHEDRON_CONIC_HULL_POLYTOPE : thm
  CLOSED_CONIC_HULL_STRONG : thm
  CLOSED_CONVEX_CONE_HULL_STRONG : thm
  FINITELY_GENERATED_CONIC_POLYHEDRON : thm
  deriving Inhabited

set_option maxHeartbeats 8000000 in
@[nospecialize]
def setupPON [HolBase] (D : PolytopeDeps) (BPOF : POF) (BPOJ : POJ) (BPOM : POM) : ExceptT String IO PON := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC, REAL_RAT_REDUCE_CONV, SET_RULE,
        SET_TAC, .. } := D.cvx
  let { EXISTS_IN_IMAGE, EXTENSION, FINITE_EMPTY, FINITE_IMAGE, FINITE_INSERT,
        FINITE_RESTRICT, .. } := D.cvx.core1
  let { FORALL_IN_IMAGE, IMAGE_EQ_EMPTY, INSERT_SUBSET, INTER_SUBSET, INTERS_0, .. } :=
        D.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, IN_INTER, IN_INTERS, LEFT_IMP_EXISTS_THM, MONO_EXISTS,
        REAL_ABS_DIV, REAL_ABS_NUM, REAL_DIV_RMUL, .. } := D.cvx.core3
  let { REAL_INF_LE_FINITE, REAL_LE_INV_EQ, REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ, REAL_LE_REFL,
        REAL_LT_01, REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_INF_FINITE,
        REAL_LT_LE, .. } := D.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_LZERO, RIGHT_IMP_EXISTS_THM, SKOLEM_THM,
        SUBSET, SUBSET_ANTISYM, SUBSET_TRANS, .. } := D.cvx.core5
  let { HULL_HULL, HULL_INC, HULL_MINIMAL, HULL_P, HULL_SUBSET, REAL_HALF, SUBSET_HULL, .. }
        := D.cvx.misc
  let { DOT_RZERO, .. } := D.cvx.vec1
  let { IN_INTERVAL, NORM_0, NORM_EQ_0, .. } := D.cvx.vec2
  let { NORM_MUL, NORM_POS_LT, REAL_ABS_NORM, .. } := D.cvx.vec3
  let { VEC_COMPONENT, VECTOR_ADD_LID, VECTOR_MUL_ASSOC, VECTOR_MUL_LID, VECTOR_MUL_RZERO,
        VECTOR_NEG_COMPONENT, .. } := D.cvx.vec4
  let { CLOSED_SING, .. } := D.cvx.top1
  let { FINITE_IMP_BOUNDED, .. } := D.cvx.top3
  let { IN_BALL_0, IN_INTERIOR, INTERIOR_CLOSED_INTERVAL, NOT_BOUNDED_UNIV, .. } :=
        D.cvx.top4
  let { REAL_LE_INF_FINITE, .. } := D.qses
  let { BOUNDED_INTER, INTERIOR_HALFSPACE_LE, .. } := D.qtop
  let { BOUNDED_CONVEX_HULL, .. } := D.qcvx1
  let { COMPACT_CONVEX_HULL, CONIC_CONVEX_CONE_HULL, CONIC_HULL_EMPTY,
        CONVEX_CONE_HALFSPACE_LE, CONVEX_CONE_HULL_CONTAINS_0, CONVEX_CONE_HULL_EMPTY,
        CONVEX_CONE_HULL_SEPARATE_NONEMPTY, CONVEX_CONE_INTERS, CONVEX_CONVEX_CONE_HULL,
        CONVEX_HALFSPACE_LE, CONVEX_HULL_EMPTY, CONVEX_HULL_EQ_EMPTY,
        CONVEX_HULL_SUBSET_CONVEX_CONE_HULL, .. } := D.qcvx2
  let { conic, convex_cone, IN_CONVEX_SET, .. } := D.qcvx3
  let { CLOSED_CONIC_HULL, .. } := BPOF
  let { polyhedron, POLYHEDRON_EMPTY, POLYHEDRON_IMP_CLOSED, POLYHEDRON_IMP_CONVEX,
        POLYHEDRON_INTER, polytope, POLYTOPE_IMP_BOUNDED, POLYTOPE_IMP_CONVEX,
        POLYTOPE_INTERVAL, POLYTOPE_SING, .. } := BPOJ
  let { POLYTOPE_EQ_BOUNDED_POLYHEDRON, POLYTOPE_IMP_POLYHEDRON, .. } := BPOM
  -- @@SCOPE END

  let POLYHEDRON_CONVEX_CONE_HULL ← prove
   r"!s:real^N->bool. FINITE s ==> polyhedron(convex_cone hull s)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"s:real^N->bool = {}") THEN DISCH_TAC THENL
     [ASM_REWRITE_TAC [CONVEX_CONE_HULL_EMPTY] THEN
      ASM_SIMP_TAC [POLYTOPE_IMP_POLYHEDRON, POLYTOPE_SING],
      ALL_TAC] THEN
    SUBGOAL_THEN
      (← q r"polyhedron(convex hull ((vec 0:real^N) INSERT s))")
    MP_TAC THENL
     [MATCH_MP_TAC POLYTOPE_IMP_POLYHEDRON THEN
      REWRITE_TAC [polytope] THEN ASM_MESON_TAC [FINITE_INSERT],
      REWRITE_TAC [polyhedron] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:(real^N->bool)->bool") STRIP_ASSUME_TAC) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [SKOLEM_THM, RIGHT_IMP_EXISTS_THM]) THEN
      FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"a:(real^N->bool)->real^N") MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"b:(real^N->bool)->real"))] THEN
    SUBGOAL_THEN (← q r"~(f:(real^N->bool)->bool = {})") ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN FIRST_X_ASSUM (MP_TAC o
       GEN_REWRITE_RULE RAND_CONV [INTERS_0]) THEN
      DISCH_THEN (MP_TAC o AP_TERM (← q r"bounded:(real^N->bool)->bool")) THEN
      ASM_SIMP_TAC [NOT_BOUNDED_UNIV, BOUNDED_CONVEX_HULL, FINITE_IMP_BOUNDED,
                    FINITE_INSERT, FINITE_EMPTY],
      ALL_TAC] THEN
    EXISTS_TAC (← q r"{h:real^N->bool | h IN f /\ b h = &0}") THEN
    ASM_SIMP_TAC [FINITE_RESTRICT, IN_ELIM_THM] THEN CONJ_TAC THENL
     [ALL_TAC,
      X_GEN_TAC (← q r"h:real^N->bool") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"h:real^N->bool")) THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
      MAP_EVERY EXISTS_TAC
       [← q r"(a:(real^N->bool)->real^N) h", ← q r"(b:(real^N->bool)->real) h"] THEN
      ASM_REWRITE_TAC []] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC (← q r"convex hull ((vec 0:real^N) INSERT s)") THEN CONJ_TAC THENL
         [SIMP_TAC [SUBSET, HULL_INC, IN_INSERT], ASM_REWRITE_TAC []] THEN
        MATCH_MP_TAC (← SET_RULE (← q r"s SUBSET t ==> INTERS t SUBSET INTERS s")) THEN
        SET_TAC [],
        MATCH_MP_TAC CONVEX_CONE_INTERS THEN
        X_GEN_TAC (← q r"h:real^N->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN
        STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"h:real^N->bool")) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT2) THEN
        REWRITE_TAC [CONVEX_CONE_HALFSPACE_LE]],
      ALL_TAC] THEN
    REWRITE_TAC [SUBSET, IN_INTERS, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:real^N") THEN
    DISCH_TAC THEN
    SUBGOAL_THEN (← q r"!h:real^N->bool. h IN f ==> ?t. &0 < t /\ (t % x) IN h")
    MP_TAC THENL
     [X_GEN_TAC (← q r"h:real^N->bool") THEN DISCH_TAC THEN
      ASM_CASES_TAC (← q r"(b:(real^N->bool)->real) h = &0") THENL
       [EXISTS_TAC (← q r"&1") THEN ASM_SIMP_TAC [REAL_LT_01, VECTOR_MUL_LID],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"&0 < (b:(real^N->bool)->real) h") ASSUME_TAC THENL
       [ASM_REWRITE_TAC [REAL_LT_LE] THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"vec 0:real^N")) THEN
        SIMP_TAC [HULL_INC, IN_INSERT, IN_INTERS] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"h:real^N->bool")) THEN ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN (← q r"h = {x:real^N | a h dot x <= b h}")
         (fun th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th])
        THENL [ASM_MESON_TAC [], REWRITE_TAC [IN_ELIM_THM, DOT_RZERO]],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(vec 0:real^N) IN interior h") MP_TAC THENL
       [SUBGOAL_THEN (← q r"h = {x:real^N | a h dot x <= b h}") SUBST1_TAC THENL
         [ASM_MESON_TAC [],
          ASM_SIMP_TAC [INTERIOR_HALFSPACE_LE, IN_ELIM_THM, DOT_RZERO]],
        REWRITE_TAC [IN_INTERIOR, SUBSET, IN_BALL_0, LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC (← q r"e:real") THEN STRIP_TAC THEN
        ASM_CASES_TAC (← q r"x:real^N = vec 0") THENL
         [EXISTS_TAC (← q r"&1") THEN
          ASM_SIMP_TAC [VECTOR_MUL_RZERO, REAL_LT_01, NORM_0],
          EXISTS_TAC (← q r"e / &2 / norm(x:real^N)") THEN
          ASM_SIMP_TAC [REAL_HALF, REAL_LT_DIV, NORM_POS_LT] THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC [NORM_MUL, REAL_ABS_DIV, REAL_ABS_NUM, REAL_ABS_NORM] THEN
          ASM_SIMP_TAC [REAL_DIV_RMUL, NORM_EQ_0] THEN ASM_REAL_ARITH_TAC]],
      ALL_TAC] THEN
    REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"t:(real^N->bool)->real") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"x:real^N = inv(inf(IMAGE t (f:(real^N->bool)->bool))) %
                             inf(IMAGE t f) % x")
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [← GSYM VECTOR_MUL_LID] THEN
      REWRITE_TAC [VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_MUL_LINV THEN
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN
      ASM_SIMP_TAC [REAL_LT_INF_FINITE, FINITE_IMAGE, IMAGE_EQ_EMPTY] THEN
      ASM_SIMP_TAC [FORALL_IN_IMAGE],
      ALL_TAC] THEN
    MATCH_MP_TAC (← REWRITE_RULE [conic] CONIC_CONVEX_CONE_HULL) THEN
    ASM_SIMP_TAC [REAL_LE_INV_EQ, REAL_LE_INF_FINITE, FINITE_IMAGE,
                  IMAGE_EQ_EMPTY, REAL_LT_IMP_LE, FORALL_IN_IMAGE] THEN
    MATCH_MP_TAC (← SET_RULE (← q r"!s t. s SUBSET t /\ x IN s ==> x IN t")) THEN
    EXISTS_TAC (← q r"convex hull ((vec 0:real^N) INSERT s)") THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC [CONVEX_CONVEX_CONE_HULL] THEN
      ASM_SIMP_TAC [INSERT_SUBSET, HULL_SUBSET, CONVEX_CONE_HULL_CONTAINS_0],
      ASM_REWRITE_TAC [IN_INTERS] THEN X_GEN_TAC (← q r"h:real^N->bool") THEN
      DISCH_TAC THEN
      SUBGOAL_THEN (← q r"inf(IMAGE (t:(real^N->bool)->real) f) % x:real^N =
                    (&1 - inf(IMAGE t f) / t h) % vec 0 +
                    (inf(IMAGE t f) / t h) % t h % x")
      SUBST1_TAC THENL
       [ASM_SIMP_TAC [VECTOR_MUL_ASSOC, VECTOR_MUL_RZERO, VECTOR_ADD_LID,
                      REAL_DIV_RMUL, REAL_LT_IMP_NZ],
        ALL_TAC] THEN
      MATCH_MP_TAC IN_CONVEX_SET THEN
      ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_LE_LDIV_EQ] THEN
      REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_LID] THEN
      ASM_SIMP_TAC [REAL_INF_LE_FINITE, REAL_LE_INF_FINITE,
                    FINITE_IMAGE, IMAGE_EQ_EMPTY] THEN
      ASM_REWRITE_TAC [FORALL_IN_IMAGE, EXISTS_IN_IMAGE] THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN REPEAT CONJ_TAC THENL
       [SUBGOAL_THEN (← q r"h = {x:real^N | a h dot x <= b h}") SUBST1_TAC THENL
         [ASM_MESON_TAC [], ASM_SIMP_TAC [CONVEX_HALFSPACE_LE]],
        SUBGOAL_THEN (← q r"(vec 0:real^N) IN convex hull (vec 0 INSERT s)") MP_TAC
        THENL [SIMP_TAC [HULL_INC, IN_INSERT], ALL_TAC] THEN
        ASM_REWRITE_TAC [IN_INTERS] THEN ASM_MESON_TAC [],
        ASM SET_TAC [REAL_LE_REFL]]])

  let CLOSED_CONVEX_CONE_HULL ← prove
   r"!s:real^N->bool. FINITE s ==> closed(convex_cone hull s)"
   (MESON_TAC [POLYHEDRON_IMP_CLOSED, POLYHEDRON_CONVEX_CONE_HULL])

  let POLYHEDRON_CONVEX_CONE_HULL_POLYTOPE ← prove
   r"!s:real^N->bool. polytope s ==> polyhedron(convex_cone hull s)"
   (GEN_TAC THEN REWRITE_TAC [polytope, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"c:real^N->bool") THEN STRIP_TAC THEN
    ASM_CASES_TAC (← q r"c:real^N->bool = {}") THEN
    ASM_SIMP_TAC [CONVEX_HULL_EMPTY, CONVEX_CONE_HULL_EMPTY,
                  POLYTOPE_IMP_POLYHEDRON, POLYTOPE_SING] THEN
    ASM_SIMP_TAC [CONVEX_CONE_HULL_SEPARATE_NONEMPTY, CONVEX_HULL_EQ_EMPTY] THEN
    REWRITE_TAC [HULL_HULL] THEN
    ASM_SIMP_TAC [← GSYM CONVEX_CONE_HULL_SEPARATE_NONEMPTY, CONVEX_HULL_EQ_EMPTY,
                  POLYHEDRON_CONVEX_CONE_HULL])

  let POLYHEDRON_CONIC_HULL_POLYTOPE ← prove
   r"!s:real^N->bool. polytope s ==> polyhedron(conic hull s)"
   (GEN_TAC THEN  REWRITE_TAC [polytope, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"c:real^N->bool") THEN STRIP_TAC THEN
    ASM_CASES_TAC (← q r"c:real^N->bool = {}") THEN
    ASM_SIMP_TAC [POLYHEDRON_EMPTY, CONVEX_HULL_EMPTY, CONIC_HULL_EMPTY] THEN
    ASM_SIMP_TAC [← GSYM CONVEX_CONE_HULL_SEPARATE_NONEMPTY] THEN
    ASM_SIMP_TAC [POLYHEDRON_CONVEX_CONE_HULL])

  let CLOSED_CONIC_HULL_STRONG ← prove
   r"!s:real^N->bool.
    vec 0 IN relative_interior s \/ polytope s \/ compact s /\ ~(vec 0 IN s)
    ==> closed(conic hull s)"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [CLOSED_CONIC_HULL] THEN
    MATCH_MP_TAC POLYHEDRON_IMP_CLOSED THEN
    ASM_SIMP_TAC [POLYHEDRON_CONIC_HULL_POLYTOPE])

  let CLOSED_CONVEX_CONE_HULL_STRONG ← prove
   r"!s:real^N->bool.
        FINITE s \/
        polytope s \/
        vec 0 IN relative_interior (convex hull s) \/
        compact s /\ ~(vec 0 IN convex hull s)
        ==> closed(convex_cone hull s)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"s:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [CONVEX_CONE_HULL_EMPTY, CLOSED_SING] THEN
    DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
     [ASM_MESON_TAC [CLOSED_CONVEX_CONE_HULL], ALL_TAC] THEN
    ASM_SIMP_TAC [CONVEX_CONE_HULL_SEPARATE_NONEMPTY] THEN
    DISCH_THEN (fun th =>
      MATCH_MP_TAC CLOSED_CONIC_HULL_STRONG THEN MP_TAC th) THEN
    MESON_TAC [COMPACT_CONVEX_HULL, HULL_P, POLYTOPE_IMP_CONVEX])

  /- ----------------------------------------------------------------------- -/
  /- And conversely, a polyhedral cone is finitely generated.                -/
  /- ----------------------------------------------------------------------- -/

  let FINITELY_GENERATED_CONIC_POLYHEDRON ← prove
   r"!s:real^N->bool.
        polyhedron s /\ conic s /\ ~(s = {})
        ==> ?c. FINITE c /\ s = convex_cone hull c"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"?p:real^N->bool. polytope p /\ vec 0 IN interior p")
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC (← q r"interval[--vec 1:real^N,vec 1:real^N]") THEN
      REWRITE_TAC [POLYTOPE_INTERVAL, INTERIOR_CLOSED_INTERVAL] THEN
      SIMP_TAC [IN_INTERVAL, VECTOR_NEG_COMPONENT, VEC_COMPONENT] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV,
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"polytope(s INTER p:real^N->bool)") MP_TAC THENL
     [REWRITE_TAC [POLYTOPE_EQ_BOUNDED_POLYHEDRON] THEN
      ASM_SIMP_TAC [BOUNDED_INTER, POLYTOPE_IMP_BOUNDED] THEN
      ASM_SIMP_TAC [POLYHEDRON_INTER, POLYTOPE_IMP_POLYHEDRON],
      REWRITE_TAC [polytope] THEN MATCH_MP_TAC MONO_EXISTS] THEN
    X_GEN_TAC (← q r"c:real^N->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC,
      ASM_SIMP_TAC [SUBSET_HULL, POLYHEDRON_IMP_CONVEX, convex_cone] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC (← q r"s INTER p:real^N->bool") THEN
      REWRITE_TAC [INTER_SUBSET] THEN ASM_REWRITE_TAC [HULL_SUBSET]] THEN
    REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"?t. &0 < t /\ (t % x:real^N) IN p") STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
      REWRITE_TAC [SUBSET, IN_BALL_0, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"e:real") THEN STRIP_TAC THEN
      ASM_CASES_TAC (← q r"x:real^N = vec 0") THENL
       [EXISTS_TAC (← q r"&1") THEN ASM_REWRITE_TAC [VECTOR_MUL_RZERO, REAL_LT_01] THEN
        ASM_SIMP_TAC [NORM_0],
        EXISTS_TAC (← q r"e / &2 / norm(x:real^N)") THEN
        ASM_SIMP_TAC [REAL_HALF, REAL_LT_DIV, NORM_POS_LT] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC [NORM_MUL, REAL_ABS_DIV, REAL_ABS_NORM, REAL_ABS_NUM] THEN
        ASM_SIMP_TAC [REAL_DIV_RMUL, NORM_EQ_0] THEN ASM_REAL_ARITH_TAC],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"x:real^N = inv t % t % x") SUBST1_TAC THENL
     [ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, VECTOR_MUL_LID,
                    REAL_LT_IMP_NZ],
      ALL_TAC] THEN
    MATCH_MP_TAC (← REWRITE_RULE [conic] CONIC_CONVEX_CONE_HULL) THEN
    ASM_SIMP_TAC [REAL_LE_INV_EQ, REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC (← SET_RULE (← q r"!s. x IN s /\ s SUBSET t ==> x IN t")) THEN
    EXISTS_TAC (← q r"convex hull c:real^N->bool") THEN
    REWRITE_TAC [CONVEX_HULL_SUBSET_CONVEX_CONE_HULL] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [IN_INTER] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o GEN_REWRITE_RULE I [conic]) THEN
    ASM_SIMP_TAC [REAL_LT_IMP_LE])

  pure { POLYHEDRON_CONVEX_CONE_HULL, CLOSED_CONVEX_CONE_HULL,
         POLYHEDRON_CONVEX_CONE_HULL_POLYTOPE, POLYHEDRON_CONIC_HULL_POLYTOPE,
         CLOSED_CONIC_HULL_STRONG, CLOSED_CONVEX_CONE_HULL_STRONG,
         FINITELY_GENERATED_CONIC_POLYHEDRON }

/- ------------------------------------------------------------------------- -/
/- Decomposition of polyhedron into cone plus polytope and more corollaries. -/
/- (polytope.ml 6194-6475)                                                   -/
/- ------------------------------------------------------------------------- -/

structure POO where
  POLYHEDRON_POLYTOPE_SUMS : thm
  POLYHEDRON_AS_CONE_PLUS_CONV : thm
  POLYHEDRON_LINEAR_IMAGE : thm
  POLYHEDRON_SUMS : thm
  POLYHEDRAL_CONVEX_CONE : thm
  deriving Inhabited

set_option maxHeartbeats 8000000 in
@[nospecialize]
def setupPOO [HolBase] (D : PolytopeDeps) (BPOD : POD) (BPOJ : POJ) (BPOL : POL) (BPOM : POM) (BPON : PON) : ExceptT String IO POO := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC, NORM_ARITH, REAL_ARITH, REAL_ARITH_TAC,
        REAL_FIELD, SET_RULE, SET_TAC, VECTOR_ARITH, .. } := D.cvx
  let { ARITH_EQ, CONJ_ASSOC, EXISTS_IN_IMAGE, EXTENSION, FINITE_IMAGE, FINITE_INSERT,
        FINITE_RESTRICT, FINITE_SUBSET, FINITE_UNION, FORALL_IN_GSPEC, .. } := D.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_IN_INSERT, FORALL_PASTECART, FSTCART_PASTECART, FUN_EQ_THM,
        INTERS_IMAGE, INTERS_INSERT, .. } := D.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, IN_INTER, IN_INTERS, IN_SING, IN_UNION, LEFT_AND_EXISTS_THM,
        LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY, NOT_IN_EMPTY, REAL_ABS_DIV, REAL_ADD_RID, ..
        } := D.cvx.core3
  let { REAL_LE_ADD, REAL_LE_DIV, REAL_LE_INV_EQ, REAL_LE_LMUL, REAL_LE_MUL, REAL_LE_REFL,
        REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_LDIV_EQ, REAL_LT_LMUL_EQ, .. } :=
        D.cvx.core4
  let { REAL_MUL_AC, REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_LNEG, REAL_MUL_RID,
        REAL_MUL_RINV, REAL_MUL_RZERO, REAL_POS, REAL_SUB_0, RIGHT_AND_EXISTS_THM,
        RIGHT_EXISTS_AND_THM, RIGHT_IMP_EXISTS_THM, SIMPLE_IMAGE, SKOLEM_THM,
        SNDCART_PASTECART, SUBSET, SUBSET_ANTISYM, SUBSET_TRANS, SUBSET_UNION, .. } :=
        D.cvx.core5
  let { UNION_SUBSET, .. } := D.cvx.core6
  let { HULL_INC, HULL_INDUCT, HULL_MINIMAL, HULL_MONO, .. } := D.cvx.misc
  let { DOT_LZERO, DOT_RMUL, DOT_RZERO, .. } := D.cvx.vec1
  let { DROP_ADD, DROP_CMUL, DROP_EQ, DROP_VEC, FSTCART_ADD, FSTCART_CMUL, LIFT_DROP,
        LINEAR_ADD, LINEAR_FSTCART, .. } := D.cvx.vec2
  let { NORM_MUL, NORM_POS_LE, SNDCART_ADD, SNDCART_CMUL, VECTOR_ADD_AC, .. } := D.cvx.vec3
  let { drop, VECTOR_ADD_LDISTRIB, VECTOR_ADD_LID, VECTOR_MUL_ASSOC, VECTOR_MUL_EQ_0,
        VECTOR_MUL_LID, VECTOR_NEG_EQ_0, .. } := D.cvx.vec4
  let { CLOSED_APPROACHABLE, CLOSED_COMPACT_SUMS, .. } := D.cvx.top1
  let { LIMPT_APPROACHABLE, .. } := D.cvx.top4
  let { FINITE_PRODUCT_DEPENDENT, PASTECART_EQ, real_sub, .. } := D.qses
  let { DOT_1, DOT_PASTECART, DROP_NEG, FSTCART_VEC, PASTECART_EQ_VEC, SNDCART_VEC, VEC_EQ,
        .. } := D.qvec
  let { CONVEX_CONE_CONVEX_CONE_HULL, CONVEX_CONE_HULL_ADD, CONVEX_CONE_HULL_CONTAINS_0,
        CONVEX_CONE_HULL_CONVEX_HULL_NONEMPTY, CONVEX_CONE_HULL_EMPTY,
        CONVEX_CONE_HULL_LINEAR_IMAGE, CONVEX_CONE_HULL_MUL, CONVEX_CONE_HULL_UNION,
        CONVEX_CONE_MUL, CONVEX_CONE_NONEMPTY, CONVEX_HULL_EMPTY, CONVEX_HULL_LINEAR_IMAGE,
        CONVEX_HULL_SUBSET_CONVEX_CONE_HULL, CONVEX_HULL_SUMS, .. } := D.qcvx2
  let { conic, convex, convex_cone, CONVEX_SUMS, .. } := D.qcvx3
  let { EXPOSED_FACE_OF_SUMS, .. } := BPOD
  let { polyhedron, POLYHEDRON_IMP_CLOSED, POLYHEDRON_IMP_CONVEX, POLYTOPE_CONVEX_HULL,
        POLYTOPE_IMP_COMPACT, POLYTOPE_IMP_CONVEX, .. } := BPOJ
  let { FINITE_POLYHEDRON_EXPOSED_FACES, .. } := BPOL
  let { POLYHEDRON_EQ_FINITE_EXPOSED_FACES, POLYTOPE_IMP_POLYHEDRON, .. } := BPOM
  let { FINITELY_GENERATED_CONIC_POLYHEDRON, POLYHEDRON_CONVEX_CONE_HULL, .. } := BPON
  -- @@SCOPE END

  let POLYHEDRON_POLYTOPE_SUMS ← prove
   r"!s t:real^N->bool.
    polyhedron s /\ polytope t ==> polyhedron {x + y | x IN s /\ y IN t}"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [POLYHEDRON_EQ_FINITE_EXPOSED_FACES] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_COMPACT_SUMS THEN
      ASM_SIMP_TAC [POLYHEDRON_IMP_CLOSED, POLYTOPE_IMP_COMPACT],
      MATCH_MP_TAC CONVEX_SUMS THEN
      ASM_SIMP_TAC [POLYHEDRON_IMP_CONVEX, POLYTOPE_IMP_CONVEX],
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC (← q r"{ {x + y:real^N | x IN k /\ y IN l} |
                    k exposed_face_of s /\ l exposed_face_of t}") THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC [← SET_RULE (← q r"k exposed_face_of s <=>
                                   k IN {f | f exposed_face_of s}")] THEN
        MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
        ASM_SIMP_TAC [FINITE_POLYHEDRON_EXPOSED_FACES,
                      POLYTOPE_IMP_POLYHEDRON],
        REWRITE_TAC [SUBSET, IN_ELIM_THM, ← GSYM CONJ_ASSOC] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC EXPOSED_FACE_OF_SUMS THEN
        ASM_SIMP_TAC [POLYHEDRON_IMP_CONVEX, POLYTOPE_IMP_CONVEX]]])

  let POLYHEDRON_AS_CONE_PLUS_CONV ← prove
   r"!s:real^N->bool.
        polyhedron s <=> ?t u. FINITE t /\ FINITE u /\
                               s = {x + y | x IN convex_cone hull t /\
                                            y IN convex hull u}"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [REWRITE_TAC [polyhedron, LEFT_IMP_EXISTS_THM],
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC POLYHEDRON_POLYTOPE_SUMS THEN
      ASM_SIMP_TAC [POLYTOPE_CONVEX_HULL, POLYHEDRON_CONVEX_CONE_HULL]] THEN
    REWRITE_TAC [polyhedron, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"f:(real^N->bool)->bool") THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) MP_TAC) THEN
    GEN_REWRITE_TAC (LAND_CONV o REDEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
     [← q r"a:(real^N->bool)->real^N", ← q r"b:(real^N->bool)->real"] THEN
    ONCE_REWRITE_TAC [← MESON [] (← q r"h = {x | P x} <=> {x | P x} = h")] THEN
    DISCH_TAC THEN
    ABBREV_TAC
     (← q r"s':real^(N,1)finite_sum->bool =
          {x | &0 <= drop(sndcart x) /\
               !h:real^N->bool.
                  h IN f ==> a h dot (fstcart x) <= b h * drop(sndcart x)}") THEN
    SUBGOAL_THEN
     (← q r"?t u. FINITE t /\ FINITE u /\
            (!y:real^(N,1)finite_sum. y IN t ==> drop(sndcart y) = &0) /\
            (!y. y IN u ==> drop(sndcart y) = &1) /\
            s' = convex_cone hull (t UNION u)")
    STRIP_ASSUME_TAC THENL
     [MP_TAC (← ISPEC (← q r"s':real^(N,1)finite_sum->bool")
          FINITELY_GENERATED_CONIC_POLYHEDRON) THEN
      ANTS_TAC THENL
       [EXPAND_TAC "s'" THEN REPEAT CONJ_TAC THENL
         [REWRITE_TAC [polyhedron] THEN
          EXISTS_TAC
           (← q r"{ x:real^(N,1)finite_sum |
              pastecart (vec 0) (--vec 1) dot x <= &0} INSERT
            { {x | pastecart (a h) (--lift(b h)) dot x <= &0} |
              (h:real^N->bool) IN f}") THEN
          REWRITE_TAC [FINITE_INSERT, INTERS_INSERT, SIMPLE_IMAGE] THEN
          ASM_SIMP_TAC [FINITE_IMAGE, FORALL_IN_INSERT, FORALL_IN_IMAGE] THEN
          REPEAT CONJ_TAC THENL
           [EXPAND_TAC "s'" THEN
            REWRITE_TAC [EXTENSION, IN_ELIM_THM, FORALL_PASTECART, IN_INTER,
             DOT_PASTECART, INTERS_IMAGE, FSTCART_PASTECART,
             SNDCART_PASTECART, DOT_1, ← GSYM drop, DROP_NEG, LIFT_DROP] THEN
            REWRITE_TAC [DROP_VEC, DOT_LZERO, REAL_MUL_LNEG, ← GSYM real_sub] THEN
            REWRITE_TAC [REAL_MUL_LID, ← REAL_ARITH (← q r"x - y <= &0 <=> x <= y")],
            EXISTS_TAC (← q r"pastecart (vec 0) (--vec 1):real^(N,1)finite_sum") THEN
            EXISTS_TAC (← q r"&0") THEN
            REWRITE_TAC [PASTECART_EQ_VEC, VECTOR_NEG_EQ_0, VEC_EQ] THEN
            ARITH_TAC,
            X_GEN_TAC (← q r"h:real^N->bool") THEN DISCH_TAC THEN MAP_EVERY EXISTS_TAC
             [← q r"pastecart (a(h:real^N->bool)) (--lift(b h)):real^(N,1)finite_sum",
              ← q r"&0"] THEN
            ASM_SIMP_TAC [PASTECART_EQ_VEC]],
          REWRITE_TAC [conic, IN_ELIM_THM, FSTCART_CMUL, SNDCART_CMUL] THEN
          SIMP_TAC [DROP_CMUL, DOT_RMUL, REAL_LE_MUL] THEN
          MESON_TAC [REAL_LE_LMUL, REAL_MUL_AC],
          REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN
          EXISTS_TAC (← q r"vec 0:real^(N,1)finite_sum") THEN
          REWRITE_TAC [IN_ELIM_THM, FSTCART_VEC, SNDCART_VEC] THEN
          REWRITE_TAC [DROP_VEC, DOT_RZERO, REAL_LE_REFL, REAL_MUL_RZERO]],
        DISCH_THEN (X_CHOOSE_THEN (← q r"c:real^(N,1)finite_sum->bool")
          STRIP_ASSUME_TAC) THEN
        MAP_EVERY EXISTS_TAC
         [← q r"{x:real^(N,1)finite_sum | x IN c /\ drop(sndcart x) = &0}",
          ← q r"IMAGE (\x. inv(drop(sndcart x)) % x)
             {x:real^(N,1)finite_sum | x IN c /\ ~(drop(sndcart x) = &0)}"] THEN
        ASM_SIMP_TAC [FINITE_IMAGE, FINITE_RESTRICT, FORALL_IN_IMAGE] THEN
        SIMP_TAC [IN_ELIM_THM, SNDCART_CMUL, DROP_CMUL, REAL_MUL_LINV] THEN
        SUBGOAL_THEN
         (← q r"!x:real^(N,1)finite_sum. x IN c ==> &0 <= drop(sndcart x)")
        ASSUME_TAC THENL
         [GEN_TAC THEN DISCH_TAC THEN
          SUBGOAL_THEN (← q r"(x:real^(N,1)finite_sum) IN s'") MP_TAC THENL
           [ASM_MESON_TAC [HULL_INC], EXPAND_TAC "s'"] THEN
          SIMP_TAC [IN_ELIM_THM],
          ALL_TAC] THEN
        MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
        MATCH_MP_TAC HULL_MINIMAL THEN
        REWRITE_TAC [CONVEX_CONE_CONVEX_CONE_HULL, UNION_SUBSET] THEN
        SIMP_TAC [SUBSET, IN_ELIM_THM, HULL_INC, FORALL_IN_IMAGE] THEN
        X_GEN_TAC (← q r"x:real^(N,1)finite_sum") THEN DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x:real^(N,1)finite_sum")) THEN
        ASM_SIMP_TAC [CONVEX_CONE_HULL_MUL, HULL_INC, REAL_LE_INV_EQ] THEN
        ASM_REWRITE_TAC [← REAL_ARITH (← q r"&0 <= x <=> x = &0 \/ &0 < x")] THEN
        STRIP_TAC THENL
         [MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC [IN_UNION, IN_ELIM_THM],
          SUBGOAL_THEN
           (← q r"x:real^(N,1)finite_sum =
                  drop(sndcart x) % inv(drop(sndcart x)) % x")
          SUBST1_TAC THENL
           [ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_RINV, REAL_LT_IMP_NZ] THEN
            REWRITE_TAC [VECTOR_MUL_LID],
            MATCH_MP_TAC CONVEX_CONE_HULL_MUL THEN
            ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN MATCH_MP_TAC HULL_INC THEN
            REWRITE_TAC [IN_UNION] THEN DISJ2_TAC THEN
            REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"x:real^(N,1)finite_sum") THEN
            ASM_SIMP_TAC [IN_ELIM_THM, REAL_LT_IMP_NZ]]]],
      EXISTS_TAC (← q r"IMAGE fstcart (t:real^(N,1)finite_sum->bool)") THEN
      EXISTS_TAC (← q r"IMAGE fstcart (u:real^(N,1)finite_sum->bool)") THEN
      ASM_SIMP_TAC [FINITE_IMAGE] THEN
      SUBGOAL_THEN (← q r"s = {x:real^N | pastecart x (vec 1:real^1) IN s'}")
      SUBST1_TAC THENL
       [MAP_EVERY EXPAND_TAC ["s", "s'"] THEN
        REWRITE_TAC [IN_ELIM_THM, SNDCART_PASTECART, DROP_VEC, REAL_POS] THEN
        GEN_REWRITE_TAC I [EXTENSION] THEN
        REWRITE_TAC [FSTCART_PASTECART, IN_ELIM_THM, IN_INTERS, REAL_MUL_RID] THEN
        ASM SET_TAC [],
        ASM_REWRITE_TAC [CONVEX_CONE_HULL_UNION]] THEN
      REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"z:real^N") THEN
      SIMP_TAC [CONVEX_CONE_HULL_LINEAR_IMAGE, CONVEX_HULL_LINEAR_IMAGE,
                LINEAR_FSTCART] THEN
      REWRITE_TAC [← GSYM CONJ_ASSOC, RIGHT_EXISTS_AND_THM] THEN
      REWRITE_TAC [EXISTS_IN_IMAGE] THEN
      AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
      X_GEN_TAC (← q r"a:real^(N,1)finite_sum") THEN REWRITE_TAC [] THEN
      MATCH_MP_TAC (← TAUT (← q r"(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)")) THEN
      DISCH_TAC THEN AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
      X_GEN_TAC (← q r"b:real^(N,1)finite_sum") THEN REWRITE_TAC [PASTECART_EQ] THEN
      REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART, FSTCART_ADD,
                   SNDCART_ADD] THEN
      ASM_CASES_TAC (← q r"fstcart(a:real^(N,1)finite_sum) +
                     fstcart(b:real^(N,1)finite_sum) = z") THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"sndcart(a:real^(N,1)finite_sum) = vec 0") SUBST1_TAC THENL
       [UNDISCH_TAC (← q r"(a:real^(N,1)finite_sum) IN convex_cone hull t") THEN
        SPEC_TAC (← q r"a:real^(N,1)finite_sum", ← q r"a:real^(N,1)finite_sum") THEN
        MATCH_MP_TAC HULL_INDUCT THEN ASM_SIMP_TAC [← GSYM DROP_EQ, DROP_VEC] THEN
        REWRITE_TAC [convex_cone, convex, conic, IN_ELIM_THM] THEN
        SIMP_TAC [SNDCART_ADD, SNDCART_CMUL, DROP_ADD, DROP_CMUL] THEN
        REWRITE_TAC [REAL_MUL_RZERO, REAL_ADD_RID, ← GSYM MEMBER_NOT_EMPTY] THEN
        EXISTS_TAC (← q r"vec 0:real^(N,1)finite_sum") THEN
        REWRITE_TAC [IN_ELIM_THM, SNDCART_VEC, DROP_VEC],
        REWRITE_TAC [VECTOR_ADD_LID]] THEN
      ASM_CASES_TAC (← q r"u:real^(N,1)finite_sum->bool = {}") THENL
       [ASM_REWRITE_TAC [CONVEX_CONE_HULL_EMPTY, CONVEX_HULL_EMPTY] THEN
        REWRITE_TAC [IN_SING, NOT_IN_EMPTY] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        ASM_REWRITE_TAC [SNDCART_VEC, VEC_EQ] THEN ARITH_TAC,
        ALL_TAC] THEN
      ASM_SIMP_TAC [CONVEX_CONE_HULL_CONVEX_HULL_NONEMPTY, IN_ELIM_THM] THEN
      SUBGOAL_THEN
       (← q r"!y:real^(N,1)finite_sum. y IN convex hull u ==> sndcart y = vec 1")
       (LABEL_TAC "*")
      THENL
       [MATCH_MP_TAC HULL_INDUCT THEN ASM_SIMP_TAC [← GSYM DROP_EQ, DROP_VEC] THEN
        REWRITE_TAC [convex, IN_ELIM_THM] THEN
        SIMP_TAC [SNDCART_ADD, SNDCART_CMUL, DROP_ADD, DROP_CMUL] THEN
        SIMP_TAC [REAL_MUL_RID],
        ALL_TAC] THEN
      EQ_TAC THEN REWRITE_TAC [LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THENL
       [MAP_EVERY X_GEN_TAC [← q r"c:real", ← q r"d:real^(N,1)finite_sum"] THEN
        DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
        ASM_SIMP_TAC [SNDCART_CMUL, VECTOR_MUL_EQ_0, ← VECTOR_ARITH
         (← q r"x:real^N = c % x <=> (c - &1) % x = vec 0")] THEN
        ASM_SIMP_TAC [REAL_SUB_0, VEC_EQ, ARITH_EQ, VECTOR_MUL_LID],
        DISCH_TAC THEN ASM_SIMP_TAC [] THEN EXISTS_TAC (← q r"&1") THEN
        ASM_REWRITE_TAC [REAL_POS, VECTOR_MUL_LID] THEN ASM_MESON_TAC []]])

  let POLYHEDRON_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N s.
        linear f /\ polyhedron s ==> polyhedron(IMAGE f s)"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [POLYHEDRON_AS_CONE_PLUS_CONV, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"t:real^M->bool", ← q r"u:real^M->bool"] THEN STRIP_TAC THEN
    EXISTS_TAC (← q r"IMAGE (f:real^M->real^N) t") THEN
    EXISTS_TAC (← q r"IMAGE (f:real^M->real^N) u") THEN
    ASM_SIMP_TAC [FINITE_IMAGE] THEN
    ASM_SIMP_TAC [CONVEX_CONE_HULL_LINEAR_IMAGE, CONVEX_HULL_LINEAR_IMAGE] THEN
    REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP LINEAR_ADD) THEN MESON_TAC [])

  let POLYHEDRON_SUMS ← prove
   r"!s t:real^N->bool.
    polyhedron s /\ polyhedron t ==> polyhedron {x + y | x IN s /\ y IN t}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [POLYHEDRON_AS_CONE_PLUS_CONV] THEN
    REWRITE_TAC [LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"t1:real^N->bool", ← q r"u1:real^N->bool",
      ← q r"t2:real^N->bool", ← q r"u2:real^N->bool"] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC (← q r"t1 UNION t2:real^N->bool") THEN
    EXISTS_TAC (← q r"{u + v:real^N | u IN u1 /\ v IN u2}") THEN
    REWRITE_TAC [CONVEX_CONE_HULL_UNION, CONVEX_HULL_SUMS] THEN
    ASM_SIMP_TAC [FINITE_PRODUCT_DEPENDENT, FINITE_UNION] THEN
    REWRITE_TAC [← SET_RULE
     (← q r"{h x y | x IN {f a b | P a /\ Q b} /\
               y IN {g a b | R a /\ S b}} =
      {h (f a b) (g c d) | P a /\ Q b /\ R c /\ S d}")] THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN MESON_TAC [VECTOR_ADD_AC])

  let POLYHEDRAL_CONVEX_CONE ← prove
   r"!s:real^N->bool.
        polyhedron s /\ convex_cone s <=>
        ?k. FINITE k /\ s = convex_cone hull k"
   (GEN_TAC THEN EQ_TAC THENL
     [ALL_TAC, MESON_TAC [POLYHEDRON_CONVEX_CONE_HULL,
                          CONVEX_CONE_CONVEX_CONE_HULL]] THEN
    STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [POLYHEDRON_AS_CONE_PLUS_CONV]) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"k:real^N->bool", ← q r"c:real^N->bool"] THEN
    ASM_CASES_TAC (← q r"c:real^N->bool = {}") THENL
     [ASM_REWRITE_TAC [CONVEX_HULL_EMPTY, NOT_IN_EMPTY] THEN
      REWRITE_TAC [← SET_RULE (← q r"{f x y | x,y | F} = {}")] THEN
      ASM_MESON_TAC [CONVEX_CONE_NONEMPTY],
      DISCH_THEN (STRIP_ASSUME_TAC o GSYM)] THEN
    EXISTS_TAC (← q r"k UNION c:real^N->bool") THEN
    ASM_REWRITE_TAC [FINITE_UNION] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    CONJ_TAC THENL
     [EXPAND_TAC "s" THEN REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CONVEX_CONE_HULL_ADD THEN
      CONJ_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
       (← q r"x IN s ==> s SUBSET t ==> x IN t"))) THEN
      MESON_TAC [HULL_MONO, SUBSET_UNION, SUBSET_TRANS,
          CONVEX_HULL_SUBSET_CONVEX_CONE_HULL],
      MATCH_MP_TAC HULL_MINIMAL THEN
      CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []]] THEN
    REWRITE_TAC [UNION_SUBSET] THEN REWRITE_TAC [SUBSET] THEN
    CONJ_TAC THEN X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THENL
     [ALL_TAC,
      EXPAND_TAC "s" THEN REWRITE_TAC [IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [← q r"vec 0:real^N", ← q r"x:real^N"] THEN
      ASM_SIMP_TAC [HULL_INC, VECTOR_ADD_LID, CONVEX_CONE_HULL_CONTAINS_0]] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP POLYHEDRON_IMP_CLOSED) THEN
    DISCH_THEN (MP_TAC o MATCH_MP CLOSED_APPROACHABLE) THEN
    DISCH_THEN (fun th => tactic_of do
      pure (GEN_REWRITE_TAC I [← GSYM th])) THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"y:real^N")) THEN REWRITE_TAC [LIMPT_APPROACHABLE] THEN
    X_GEN_TAC (← q r"e:real") THEN DISCH_TAC THEN
    EXISTS_TAC (← q r"e / (norm y + &1) % ((norm y + &1) / e % x + y):real^N") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONE_MUL THEN
      ASM_SIMP_TAC [REAL_LE_DIV, REAL_LE_ADD, NORM_POS_LE, REAL_POS,
                    REAL_LT_IMP_LE] THEN
      EXPAND_TAC "s" THEN REWRITE_TAC [IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC
       [← q r"(norm(y:real^N) + &1) / e % x:real^N", ← q r"y:real^N"] THEN
      ASM_SIMP_TAC [HULL_INC] THEN MATCH_MP_TAC CONVEX_CONE_HULL_MUL THEN
      ASM_SIMP_TAC [HULL_INC] THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN CONV_TAC (fun t => NORM_ARITH t),
      REWRITE_TAC [VECTOR_ADD_LDISTRIB, VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC [NORM_POS_LE, VECTOR_MUL_LID, ← REAL_FIELD
       (← q r"&0 <= y /\ &0 < e ==> e / (y + &1) * (y + &1) / e = &1")] THEN
      REWRITE_TAC [← NORM_ARITH (← q r"dist(x + e:real^N,x) = norm e")] THEN
      REWRITE_TAC [NORM_MUL, REAL_ABS_DIV] THEN
      MATCH_MP_TAC (← REAL_ARITH
       (← q r"&0 < e /\ e * z / y < e * &1 ==> abs e / y * z < e")) THEN
      ASM_SIMP_TAC [REAL_LT_LMUL_EQ, REAL_LT_LDIV_EQ,
                    ← NORM_ARITH (← q r"&0 < abs(norm(y:real^N) + &1)")] THEN
      REAL_ARITH_TAC])

  pure { POLYHEDRON_POLYTOPE_SUMS, POLYHEDRON_AS_CONE_PLUS_CONV, POLYHEDRON_LINEAR_IMAGE,
         POLYHEDRON_SUMS, POLYHEDRAL_CONVEX_CONE }

/- ------------------------------------------------------------------------- -/
/- Farkas's lemma, separation for polyhedra, frontier of a polytope,         -/
/- triangles. (polytope.ml 6475-6837)                                        -/
/- ------------------------------------------------------------------------- -/

structure POP where
  FARKAS_LEMMA : thm
  FARKAS_LEMMA_ALT : thm
  SEPARATING_HYPERPLANE_POLYHEDRA : thm
  RELATIVE_BOUNDARY_OF_CONVEX_HULL : thm
  FRONTIER_OF_CONVEX_HULL : thm
  RELATIVE_BOUNDARY_OF_TRIANGLE : thm
  RELATIVE_FRONTIER_OF_TRIANGLE : thm
  FRONTIER_OF_TRIANGLE : thm
  INSIDE_OF_TRIANGLE : thm
  INTERIOR_OF_TRIANGLE : thm
  deriving Inhabited

set_option maxHeartbeats 8000000 in
@[nospecialize]
def setupPOP [HolBase] (D : PolytopeDeps) (BPOH : POH) (BPOJ : POJ) (BPOL : POL) (BPOM : POM) (BPOO : POO) : ExceptT String IO POP := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, HAS_SIZE_CONV, INT_ARITH,
        INT_ARITH_TAC, NUM_REDUCE_CONV, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD, SET_RULE,
        SET_TAC, VECTOR_ARITH, .. } := D.cvx
  let { CARD_CLAUSES, CARD_EQ_0, CONJ_ASSOC, CONJ_SYM, CONTRAPOS_THM, DE_MORGAN_THM,
        DIFF_EMPTY, DIFF_EQ_EMPTY, DIMINDEX_2, DIMINDEX_GE_1, EMPTY_UNIONS, EQ_TRANS,
        FINITE_EMPTY, FINITE_INSERT, FINITE_NUMSEG, FORALL_IN_GSPEC, .. } := D.cvx.core1
  let { FORALL_IN_IMAGE, FORALL_UNWIND_THM2, HAS_SIZE, IMAGE_CLAUSES, IMAGE_EQ_EMPTY,
        IMP_CONJ, IMP_IMP, INF, INSERT_AC, INT_LE_TRANS, INT_OF_NUM_ADD, INT_OF_NUM_LE, .. }
        := D.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_NUMSEG, IN_SING, LE_REFL, LEFT_IMP_EXISTS_THM,
        MEMBER_NOT_EMPTY, MONO_EXISTS, NOT_IN_EMPTY, PSUBSET, REAL_DIV_RMUL, .. } :=
        D.cvx.core3
  let { REAL_LE_ADDR, REAL_LE_DIV, REAL_LE_INF, REAL_LE_MUL, REAL_LE_REFL, REAL_LE_SUB_LADD,
        REAL_LET_TRANS, REAL_LT_INV_EQ, REAL_LT_NEG2, REAL_LT_REFL, REAL_LTE_TRANS, .. } :=
        D.cvx.core4
  let { REAL_MUL_RID, REAL_MUL_RZERO, REAL_NEG_NEG, REAL_NOT_LE, REAL_NOT_LT, REAL_SUB_0,
        REAL_SUB_LE, RIGHT_FORALL_IMP_THM, RIGHT_IMP_FORALL_THM, SIMPLE_IMAGE,
        SIMPLE_IMAGE_GEN, SUBSET, SUBSET_ANTISYM, .. } := D.cvx.core5
  let { real_gt, SUM_POS_LE, SUP, SWAP_FORALL_THM, UNION_EMPTY, UNIONS_0, UNIONS_IMAGE,
        UNIONS_INSERT, UNWIND_THM1, UNWIND_THM2, .. } := D.cvx.core6
  let { HULL_MONO, .. } := D.cvx.misc
  let { BASIS_COMPONENT, DOT_BASIS, DOT_EQ_0, DOT_LNEG, DOT_LSUB, DOT_LZERO, DOT_RMUL,
        DOT_RSUB, DOT_RZERO, .. } := D.cvx.vec1
  let { DOT_SYM, MATRIX_VECTOR_MUL_LINEAR, .. } := D.cvx.vec2
  let { NORM_POW_2, .. } := D.cvx.vec3
  let { dot, VEC_COMPONENT, VECTOR_ADD_COMPONENT, VECTOR_ADD_LID, VECTOR_ADD_RID,
        VECTOR_MUL_COMPONENT, VECTOR_NEG_EQ_0, VECTOR_NEG_NEG, VECTOR_SUB,
        VECTOR_SUB_COMPONENT, VECTOR_SUB_REFL, .. } := D.cvx.vec4
  let { CLOSURE_CLOSED, .. } := D.cvx.top1
  let { COMPACT_IMP_CLOSED, .. } := D.cvx.top2
  let { ENDS_IN_SEGMENT, FINITE_IMP_BOUNDED, FINITE_IMP_COMPACT, .. } := D.cvx.top3
  let { INTERIOR_SUBSET, .. } := D.cvx.top4
  let { frontier, .. } := D.cvx.top5
  let { REAL_SUP_LE, UNION_ACI, .. } := D.qses
  let { DOT_LMUL_MATRIX, MATRIX_VECTOR_MUL_RZERO, VECTOR_MATRIX_MUL_TRANSP, .. } := D.qvec
  let { AFF_DIM_EQ_FULL, AFF_DIM_LE_UNIV, AFFINE_HULL_CONVEX_HULL,
        AFFINE_INDEPENDENT_IFF_CARD, AFFINE_INDEPENDENT_IMP_FINITE, BOUNDED_CONVEX_HULL,
        CARATHEODORY_AFF_DIM, CLOSURE_CONVEX_HULL, CLOSURE_SEGMENT,
        COLLINEAR_3_EQ_AFFINE_DEPENDENT, .. } := D.qcvx1
  let { COMPACT_CONVEX_HULL, CONVEX_CONVEX_HULL, CONVEX_HULL_EMPTY, CONVEX_HULL_EQ_EMPTY,
        CONVEX_HULL_SING, CONVEX_LINEAR_IMAGE, .. } := D.qcvx2
  let { CONVEX_NEGATIONS, CONVEX_POSITIVE_ORTHANT, CONVEX_SUMS, CONVEX_UNIV,
        INTERIOR_CONVEX_HULL_EQ_EMPTY, INTERIOR_SEGMENT, relative_frontier,
        RELATIVE_INTERIOR_INTERIOR, RELATIVE_INTERIOR_SING, SEGMENT_CONVEX_HULL,
        SEPARATING_HYPERPLANE_CLOSED_0, SEPARATING_HYPERPLANE_CLOSED_POINT, .. } := D.qcvx3
  let { INSIDE_FRONTIER_EQ_INTERIOR, .. } := D.qpth
  let { FACET_OF_CONVEX_HULL_AFFINE_INDEPENDENT_ALT, .. } := BPOH
  let { POLYHEDRON_IMP_CLOSED, POLYHEDRON_IMP_CONVEX, POLYHEDRON_POSITIVE_ORTHANT,
        POLYHEDRON_UNIV, .. } := BPOJ
  let { RELATIVE_BOUNDARY_OF_POLYHEDRON, .. } := BPOL
  let { POLYHEDRON_CONVEX_HULL, POLYHEDRON_NEGATIONS, .. } := BPOM
  let { POLYHEDRON_LINEAR_IMAGE, POLYHEDRON_SUMS, .. } := BPOO
  -- @@SCOPE END

  let FARKAS_LEMMA ← prove
   r"!A:real^N^M b.
        (?x:real^N.
            A ** x = b /\
            (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= x$i)) <=>
        ~(?y:real^M.
            b dot y < &0 /\
            (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= (transp A ** y)$i))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← TAUT
     (← q r"(q ==> ~p) /\ (~p ==> q) ==> (p <=> ~q)")) THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"y dot ((A:real^N^M) ** x - b) = &0") MP_TAC THENL
       [ASM_REWRITE_TAC [VECTOR_SUB_REFL, DOT_RZERO], ALL_TAC] THEN
      RULE_ASSUM_TAC (ONCE_REWRITE_RULE [DOT_SYM]) THEN
      REWRITE_TAC [DOT_RSUB, REAL_SUB_0] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REAL_ARITH
       (← q r"y < &0 ==> &0 <= x ==> ~(x = y)"))) THEN
      ONCE_REWRITE_TAC [← GSYM DOT_LMUL_MATRIX] THEN
      REWRITE_TAC [VECTOR_MATRIX_MUL_TRANSP, dot] THEN
      MATCH_MP_TAC SUM_POS_LE THEN
      ASM_SIMP_TAC [REAL_LE_MUL, IN_NUMSEG, FINITE_NUMSEG],
      DISCH_TAC THEN MP_TAC (← ISPECL
       [← q r"{(A:real^N^M) ** (x:real^N) |
          !i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= x$i}",
        ← q r"b:real^M"] SEPARATING_HYPERPLANE_CLOSED_POINT) THEN
      REWRITE_TAC [FORALL_IN_GSPEC] THEN ANTS_TAC THENL
       [REWRITE_TAC [IN_ELIM_THM, CONJ_ASSOC] THEN
        CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
        ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
        SIMP_TAC [CONVEX_POSITIVE_ORTHANT, CONVEX_LINEAR_IMAGE,
                  MATRIX_VECTOR_MUL_LINEAR] THEN
        MATCH_MP_TAC POLYHEDRON_IMP_CLOSED THEN
        MATCH_MP_TAC POLYHEDRON_LINEAR_IMAGE THEN
        REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR, POLYHEDRON_POSITIVE_ORTHANT],
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"y:real^M") THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"c:real") STRIP_ASSUME_TAC) THEN
        ONCE_REWRITE_TAC [DOT_SYM] THEN
        FIRST_ASSUM (MP_TAC o SPEC (← q r"vec 0:real^N")) THEN
        REWRITE_TAC [MATRIX_VECTOR_MUL_RZERO, DOT_RZERO] THEN
        REWRITE_TAC [real_gt, VEC_COMPONENT, REAL_LE_REFL] THEN
        DISCH_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
        X_GEN_TAC (← q r"k:num") THEN STRIP_TAC THEN
        ONCE_REWRITE_TAC [← GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC
         (← q r"c / (transp(A:real^N^M) ** (y:real^M))$k % basis k:real^N")) THEN
        ASM_SIMP_TAC [VECTOR_MUL_COMPONENT, BASIS_COMPONENT] THEN
        ONCE_REWRITE_TAC [← GSYM DOT_LMUL_MATRIX] THEN
        ASM_SIMP_TAC [DOT_RMUL, DOT_BASIS, VECTOR_MATRIX_MUL_TRANSP] THEN
        ASM_SIMP_TAC [← REAL_FIELD (← q r"y < &0 ==> x / y * y = x")] THEN
        REWRITE_TAC [REAL_LT_REFL, real_gt] THEN
        GEN_TAC THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC [REAL_MUL_RZERO, REAL_LE_REFL, REAL_MUL_RID] THEN
        ONCE_REWRITE_TAC [← REAL_ARITH (← q r"x / y:real = --x * -- inv y")] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC [← REAL_ARITH (← q r"&0 <= --x <=> ~(&0 < x)"), REAL_LT_INV_EQ] THEN
        ASM_REAL_ARITH_TAC]])

  let FARKAS_LEMMA_ALT ← prove
   r"!A:real^N^M b.
        (?x:real^N.
            (!i. 1 <= i /\ i <= dimindex(:M) ==> (A ** x)$i <= b$i)) <=>
        ~(?y:real^M.
            (!i. 1 <= i /\ i <= dimindex(:M) ==> &0 <= y$i) /\
            y ** A = vec 0 /\ b dot y < &0)"
   (REPEAT GEN_TAC THEN
    MATCH_MP_TAC (← TAUT (← q r"~(p /\ q) /\ (~p ==> q) ==> (p <=> ~q)")) THEN
    REPEAT STRIP_TAC THENL
     [SUBGOAL_THEN (← q r"&0 <= (b - (A:real^N^M) ** x) dot y") MP_TAC THENL
       [REWRITE_TAC [dot] THEN MATCH_MP_TAC SUM_POS_LE THEN
        REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC [VECTOR_SUB_COMPONENT, REAL_SUB_LE],
        REWRITE_TAC [DOT_LSUB, REAL_SUB_LE] THEN REWRITE_TAC [REAL_NOT_LE] THEN
        GEN_REWRITE_TAC RAND_CONV [DOT_SYM] THEN
        REWRITE_TAC [← GSYM DOT_LMUL_MATRIX] THEN
        ASM_REWRITE_TAC [DOT_LZERO]],
      MP_TAC (← ISPECL
       [← q r"{(A:real^N^M) ** (x:real^N) + s |x,s|
          !i. 1 <= i /\ i <= dimindex(:M) ==> &0 <= s$i}",
        ← q r"b:real^M"] SEPARATING_HYPERPLANE_CLOSED_POINT) THEN
      REWRITE_TAC [FORALL_IN_GSPEC] THEN ANTS_TAC THENL
       [REWRITE_TAC [IN_ELIM_THM, CONJ_ASSOC] THEN CONJ_TAC THENL
         [ONCE_REWRITE_TAC [← SET_RULE
           (← q r"{f x + y | x,y | P y} =
            {z + y | z,y | z IN IMAGE (f:real^M->real^N) (:real^M) /\
                           y IN {w | P w}}")] THEN
          SIMP_TAC [CONVEX_SUMS, CONVEX_POSITIVE_ORTHANT, CONVEX_LINEAR_IMAGE,
                    MATRIX_VECTOR_MUL_LINEAR, CONVEX_UNIV] THEN
          MATCH_MP_TAC POLYHEDRON_IMP_CLOSED THEN
          MATCH_MP_TAC POLYHEDRON_SUMS THEN
          ASM_SIMP_TAC [POLYHEDRON_LINEAR_IMAGE, POLYHEDRON_UNIV,
            MATRIX_VECTOR_MUL_LINEAR, POLYHEDRON_POSITIVE_ORTHANT],
          POP_ASSUM MP_TAC THEN REWRITE_TAC [CONTRAPOS_THM] THEN
          MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
          ASM_SIMP_TAC [VECTOR_ADD_COMPONENT, REAL_LE_ADDR]],
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"y:real^M") THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"c:real") STRIP_ASSUME_TAC) THEN
        ONCE_REWRITE_TAC [DOT_SYM] THEN
        FIRST_ASSUM (MP_TAC o SPECL [← q r"vec 0:real^N", ← q r"vec 0:real^M"]) THEN
        REWRITE_TAC [MATRIX_VECTOR_MUL_RZERO, VECTOR_ADD_RID, DOT_RZERO] THEN
        REWRITE_TAC [real_gt, VEC_COMPONENT, REAL_LE_REFL] THEN
        DISCH_TAC THEN REWRITE_TAC [CONJ_ASSOC] THEN
        CONJ_TAC THENL [ALL_TAC, ASM_REAL_ARITH_TAC] THEN CONJ_TAC THENL
         [X_GEN_TAC (← q r"k:num") THEN STRIP_TAC THEN
          ONCE_REWRITE_TAC [← GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
          FIRST_X_ASSUM (MP_TAC o SPECL
           [← q r"vec 0:real^N", ← q r"--c / --((y:real^M)$k) % basis k:real^M"]) THEN
          ASM_SIMP_TAC [MATRIX_VECTOR_MUL_RZERO, VECTOR_ADD_LID,
                        DOT_RMUL, DOT_BASIS, ← REAL_FIELD
                         (← q r"y < &0 ==> c / --y * y = --c")] THEN
          SIMP_TAC [REAL_NEG_NEG, REAL_LT_REFL, VECTOR_MUL_COMPONENT, real_gt] THEN
          ASM_SIMP_TAC [BASIS_COMPONENT] THEN REPEAT STRIP_TAC THEN
          COND_CASES_TAC THEN
          ASM_REWRITE_TAC [REAL_MUL_RZERO, REAL_MUL_RID, REAL_LE_REFL] THEN
          MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC,
          FIRST_X_ASSUM (MP_TAC o SPECL
           [← q r"c / norm((y:real^M) ** (A:real^N^M)) pow 2 %
             (transp A ** y)", ← q r"vec 0:real^M"]) THEN
          SIMP_TAC [VEC_COMPONENT, REAL_LE_REFL, VECTOR_ADD_RID] THEN
          ONCE_REWRITE_TAC [← GSYM DOT_LMUL_MATRIX] THEN
          REWRITE_TAC [← GSYM VECTOR_MATRIX_MUL_TRANSP, DOT_RMUL] THEN
          ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
          ASM_SIMP_TAC [REAL_DIV_RMUL, NORM_POW_2, DOT_EQ_0] THEN
          REAL_ARITH_TAC]]])

  let SEPARATING_HYPERPLANE_POLYHEDRA ← prove
   r"!s t:real^N->bool.
        polyhedron s /\ polyhedron t /\ ~(s = {}) /\ ~(t = {}) /\ DISJOINT s t
        ==> ?a b. ~(a = vec 0) /\
                  (!x. x IN s ==> a dot x < b) /\
                  (!x. x IN t ==> a dot x > b)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"{x + y:real^N | x IN s /\ y IN IMAGE (--) t}")
          SEPARATING_HYPERPLANE_CLOSED_0) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [CONVEX_SUMS, CONVEX_NEGATIONS, POLYHEDRON_IMP_CONVEX] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC POLYHEDRON_IMP_CLOSED THEN
        MATCH_MP_TAC POLYHEDRON_SUMS THEN ASM_SIMP_TAC [POLYHEDRON_NEGATIONS],
        REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN
        REWRITE_TAC [← VECTOR_ARITH (← q r"y = --x:real^N <=> --y = x")] THEN
        REWRITE_TAC [UNWIND_THM1] THEN ONCE_REWRITE_TAC [CONJ_SYM] THEN
        REWRITE_TAC [← VECTOR_ARITH (← q r"vec 0:real^N = x + y <=> y = --x")] THEN
        REWRITE_TAC [UNWIND_THM2, VECTOR_NEG_NEG] THEN ASM SET_TAC []],
      REWRITE_TAC [FORALL_IN_GSPEC, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC [FORALL_IN_IMAGE, ← GSYM VECTOR_SUB, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"k:real"] THEN
      REWRITE_TAC [RIGHT_IMP_FORALL_THM, IMP_IMP, DOT_RSUB] THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"--a:real^N") THEN ASM_REWRITE_TAC [VECTOR_NEG_EQ_0] THEN
      MP_TAC (← ISPEC (← q r"IMAGE (\x:real^N. a dot x) s") INF) THEN
      MP_TAC (← ISPEC (← q r"IMAGE (\x:real^N. a dot x) t") SUP) THEN
      ASM_REWRITE_TAC [FORALL_IN_IMAGE, IMAGE_EQ_EMPTY] THEN
      MAP_EVERY ABBREV_TAC
       [← q r"u = inf(IMAGE (\x:real^N. a dot x) s)",
        ← q r"v = sup(IMAGE (\x:real^N. a dot x) t)"] THEN
      ANTS_TAC THENL
       [MP_TAC (← GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]
          (← ASSUME (← q r"~(s:real^N->bool = {})"))) THEN
        DISCH_THEN (X_CHOOSE_TAC (← q r"z:real^N")) THEN
        EXISTS_TAC (← q r"a dot (z:real^N) - k") THEN
        X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPECL [← q r"z:real^N", ← q r"x:real^N"]) THEN
        ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC,
        STRIP_TAC] THEN
      ANTS_TAC THENL
       [MP_TAC (← GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]
          (← ASSUME (← q r"~(t:real^N->bool = {})"))) THEN
        DISCH_THEN (X_CHOOSE_TAC (← q r"z:real^N")) THEN
        EXISTS_TAC (← q r"a dot (z:real^N) + k") THEN
        X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPECL [← q r"x:real^N", ← q r"z:real^N"]) THEN
        ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC,
        STRIP_TAC] THEN
      SUBGOAL_THEN (← q r"k <= u - v") ASSUME_TAC THENL
       [REWRITE_TAC [REAL_LE_SUB_LADD] THEN EXPAND_TAC "u" THEN
        MATCH_MP_TAC REAL_LE_INF THEN
        ASM_REWRITE_TAC [IMAGE_EQ_EMPTY, FORALL_IN_IMAGE] THEN
        GEN_TAC THEN DISCH_TAC THEN
        ONCE_REWRITE_TAC [← REAL_ARITH (← q r"k + v <= u <=> v <= u - k")] THEN
        EXPAND_TAC "v" THEN MATCH_MP_TAC REAL_SUP_LE THEN
        ASM_REWRITE_TAC [IMAGE_EQ_EMPTY, FORALL_IN_IMAGE] THEN
        ASM_MESON_TAC [← REAL_ARITH (← q r"x - y > k ==> y <= x - k")],
        EXISTS_TAC (← q r"--((u + v) / &2)") THEN REWRITE_TAC [real_gt] THEN
        REWRITE_TAC [DOT_LNEG, REAL_LT_NEG2] THEN REPEAT STRIP_TAC THENL
         [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (← q r"u:real"),
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (← q r"v:real")] THEN
        ASM_SIMP_TAC [] THEN ASM_REAL_ARITH_TAC]])

  /- ----------------------------------------------------------------------- -/
  /- Relative and absolute frontier of a polytope.                           -/
  /- ----------------------------------------------------------------------- -/

  let RELATIVE_BOUNDARY_OF_CONVEX_HULL ← prove
   r"!s:real^N->bool.
        ~affine_dependent s
        ==> (convex hull s) DIFF relative_interior(convex hull s) =
            UNIONS { convex hull (s DELETE a) | a | a IN s}"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
    REPEAT_TCL DISJ_CASES_THEN MP_TAC (← ARITH_RULE
      (← q r"CARD(s:real^N->bool) = 0 \/ CARD s = 1 \/ 2 <= CARD s"))
    THENL
     [ASM_SIMP_TAC [CARD_EQ_0, CONVEX_HULL_EMPTY] THEN SET_TAC [],
      DISCH_TAC THEN MP_TAC (← ExceptT.mk (HAS_SIZE_CONV (← q r"(s:real^N->bool) HAS_SIZE 1"))) THEN
      ASM_SIMP_TAC [HAS_SIZE, LEFT_IMP_EXISTS_THM, CONVEX_HULL_SING] THEN
      REWRITE_TAC [RELATIVE_INTERIOR_SING, DIFF_EQ_EMPTY] THEN
      REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC [EMPTY_UNIONS] THEN
      REWRITE_TAC [FORALL_IN_GSPEC, IN_SING, FORALL_UNWIND_THM2] THEN
      REWRITE_TAC [CONVEX_HULL_EQ_EMPTY] THEN SET_TAC [],
      DISCH_TAC THEN
      ASM_SIMP_TAC [POLYHEDRON_CONVEX_HULL, RELATIVE_BOUNDARY_OF_POLYHEDRON] THEN
      ASM_SIMP_TAC [FACET_OF_CONVEX_HULL_AFFINE_INDEPENDENT_ALT] THEN
      SET_TAC []])

  let FRONTIER_OF_CONVEX_HULL ← prove
   r"!s:real^N->bool.
        s HAS_SIZE (dimindex(:N) + 1)
        ==> frontier(convex hull s) =
               UNIONS { convex hull (s DELETE a) | a | a IN s}"
   (REWRITE_TAC [HAS_SIZE] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"affine_dependent(s:real^N->bool)") THENL
     [REWRITE_TAC [frontier] THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC (← q r"(convex hull s:real^N->bool) DIFF {}") THEN CONJ_TAC THENL
       [BINOP_TAC THEN
        ASM_SIMP_TAC [INTERIOR_CONVEX_HULL_EQ_EMPTY, frontier, HAS_SIZE] THEN
        MATCH_MP_TAC CLOSURE_CLOSED THEN
        ASM_SIMP_TAC [CLOSURE_CLOSED, COMPACT_IMP_CLOSED, COMPACT_CONVEX_HULL,
                      FINITE_IMP_COMPACT, FINITE_INSERT, FINITE_EMPTY],
        REWRITE_TAC [DIFF_EMPTY] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
        CONJ_TAC THENL
         [GEN_REWRITE_TAC LAND_CONV [CARATHEODORY_AFF_DIM] THEN
          ONCE_REWRITE_TAC [SIMPLE_IMAGE] THEN
          GEN_REWRITE_TAC I [SUBSET] THEN
          REWRITE_TAC [IN_ELIM_THM, UNIONS_IMAGE] THEN
          X_GEN_TAC (← q r"x:real^N") THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"t:real^N->bool") STRIP_ASSUME_TAC) THEN
          MP_TAC (← ISPEC (← q r"s:real^N->bool") AFFINE_INDEPENDENT_IFF_CARD) THEN
          ASM_REWRITE_TAC [← GSYM INT_OF_NUM_ADD] THEN
          REWRITE_TAC [← INT_ARITH (← q r"(x + &1) - &1:int = x")] THEN DISCH_TAC THEN
          SUBGOAL_THEN (← q r"(t:real^N->bool) PSUBSET s") ASSUME_TAC THENL
           [ASM_REWRITE_TAC [PSUBSET] THEN
            DISCH_THEN (MP_TAC o AP_TERM (← q r"CARD:(real^N->bool)->num")) THEN
            MATCH_MP_TAC (← ARITH_RULE (← q r"t:num < s ==> t = s ==> F")) THEN
            ASM_REWRITE_TAC [← ARITH_RULE (← q r"x < n + 1 <=> x <= n")] THEN
            REWRITE_TAC [← GSYM INT_OF_NUM_LE] THEN MATCH_MP_TAC INT_LE_TRANS THEN
            EXISTS_TAC (← q r"aff_dim(s:real^N->bool) + &1") THEN
            ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← INT_ARITH
             (← q r"s:int <= n /\ ~(s = n) ==> s + &1 <= n")) THEN
            ASM_REWRITE_TAC [AFF_DIM_LE_UNIV],
            SUBGOAL_THEN (← q r"?a:real^N. a IN s /\ ~(a IN t)") MP_TAC THENL
             [ASM SET_TAC [], MATCH_MP_TAC MONO_EXISTS] THEN
            X_GEN_TAC (← q r"a:real^N") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
            SUBGOAL_THEN
             (← q r"(convex hull t) SUBSET convex hull (s DELETE (a:real^N))")
            MP_TAC THENL
             [MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC [], ASM SET_TAC []]],
          ONCE_REWRITE_TAC [SIMPLE_IMAGE] THEN REWRITE_TAC [UNIONS_IMAGE] THEN
          REWRITE_TAC [SUBSET, IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
          ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
          REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, ← GSYM SUBSET] THEN
          REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC []]],
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC
       (← q r"(convex hull s) DIFF relative_interior(convex hull s):real^N->bool") THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC [← GSYM RELATIVE_BOUNDARY_OF_CONVEX_HULL, frontier] THEN
        BINOP_TAC THENL
         [MATCH_MP_TAC CLOSURE_CLOSED THEN
          ASM_SIMP_TAC [CLOSURE_CLOSED, COMPACT_IMP_CLOSED, COMPACT_CONVEX_HULL,
                        FINITE_IMP_COMPACT, FINITE_INSERT, FINITE_EMPTY],
          CONV_TAC SYM_CONV THEN MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
          REWRITE_TAC [AFFINE_HULL_CONVEX_HULL] THEN
          REWRITE_TAC [← GSYM AFF_DIM_EQ_FULL] THEN
          FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I
            [AFFINE_INDEPENDENT_IFF_CARD]) THEN
          ASM_REWRITE_TAC [← GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC],
        ASM_SIMP_TAC [RELATIVE_BOUNDARY_OF_POLYHEDRON,
                      POLYHEDRON_CONVEX_HULL, FINITE_INSERT, FINITE_EMPTY] THEN
        ASM_SIMP_TAC [FACET_OF_CONVEX_HULL_AFFINE_INDEPENDENT_ALT] THEN
        REWRITE_TAC [← ARITH_RULE (← q r"2 <= n + 1 <=> 1 <= n"), DIMINDEX_GE_1] THEN
        ASM SET_TAC []]])

  /- ----------------------------------------------------------------------- -/
  /- Special case of a triangle.                                             -/
  /- ----------------------------------------------------------------------- -/

  let RELATIVE_BOUNDARY_OF_TRIANGLE ← prove
   r"!a b c:real^N.
        ~collinear {a,b,c}
        ==> convex hull {a,b,c} DIFF relative_interior(convex hull {a,b,c}) =
            segment[a,b] UNION segment[b,c] UNION segment[c,a]"
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← SET_RULE (← q r"s UNION t UNION u = t UNION u UNION s")] THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV
     [COLLINEAR_3_EQ_AFFINE_DEPENDENT]) THEN
    REWRITE_TAC [DE_MORGAN_THM, SEGMENT_CONVEX_HULL] THEN STRIP_TAC THEN
    ASM_SIMP_TAC [RELATIVE_BOUNDARY_OF_CONVEX_HULL] THEN
    ONCE_REWRITE_TAC [SIMPLE_IMAGE] THEN
    REWRITE_TAC [IMAGE_CLAUSES, UNIONS_INSERT, UNIONS_0, UNION_EMPTY] THEN
    REPEAT BINOP_TAC THEN REWRITE_TAC [] THEN ASM SET_TAC [])

  let RELATIVE_FRONTIER_OF_TRIANGLE ← prove
   r"!a b c:real^N.
        ~collinear {a,b,c}
        ==> relative_frontier(convex hull {a,b,c}) =
            segment[a,b] UNION segment[b,c] UNION segment[c,a]"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [← GSYM RELATIVE_BOUNDARY_OF_TRIANGLE, relative_frontier] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC CLOSURE_CLOSED THEN
    ASM_SIMP_TAC [COMPACT_IMP_CLOSED, FINITE_IMP_COMPACT, COMPACT_CONVEX_HULL,
                  FINITE_INSERT, FINITE_EMPTY])

  let FRONTIER_OF_TRIANGLE ← prove
   r"!a b c:real^2.
        frontier(convex hull {a,b,c}) =
            segment[a,b] UNION segment[b,c] UNION segment[c,a]"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [SEGMENT_CONVEX_HULL] THEN
    ONCE_REWRITE_TAC [← SET_RULE (← q r"s UNION t UNION u = t UNION u UNION s")] THEN
    MAP_EVERY (fun t => tactic_of do pure (ASM_CASES_TAC t THENL
     [ASM_REWRITE_TAC [INSERT_AC, UNION_ACI] THEN
      SIMP_TAC [← GSYM SEGMENT_CONVEX_HULL, frontier, CLOSURE_SEGMENT,
                INTERIOR_SEGMENT, DIMINDEX_2, LE_REFL, DIFF_EMPTY] THEN
      REWRITE_TAC [CONVEX_HULL_SING] THEN
      REWRITE_TAC [← SET_RULE (← q r"s = s UNION {a} <=> a IN s"),
                   ← SET_RULE (← q r"s = {a} UNION s <=> a IN s")] THEN
      REWRITE_TAC [ENDS_IN_SEGMENT],
      ALL_TAC]))
     [← q r"b:real^2 = a", ← q r"c:real^2 = a", ← q r"c:real^2 = b"] THEN
    SUBGOAL_THEN (← q r"{a:real^2,b,c} HAS_SIZE (dimindex(:2) + 1)") ASSUME_TAC THENL
     [SIMP_TAC [HAS_SIZE, CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY] THEN
      ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, DIMINDEX_2] THEN
      CONV_TAC NUM_REDUCE_CONV,
      ASM_SIMP_TAC [FRONTIER_OF_CONVEX_HULL] THEN
      ONCE_REWRITE_TAC [SIMPLE_IMAGE] THEN
      REWRITE_TAC [IMAGE_CLAUSES, UNIONS_INSERT, UNIONS_0, UNION_EMPTY] THEN
      REPEAT BINOP_TAC THEN REWRITE_TAC [] THEN ASM SET_TAC []])

  let INSIDE_OF_TRIANGLE ← prove
   r"!a b c:real^2.
        inside(segment[a,b] UNION segment[b,c] UNION segment[c,a]) =
                interior(convex hull {a,b,c})"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM FRONTIER_OF_TRIANGLE] THEN
    MATCH_MP_TAC INSIDE_FRONTIER_EQ_INTERIOR THEN
    REWRITE_TAC [CONVEX_CONVEX_HULL] THEN MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN
    MATCH_MP_TAC FINITE_IMP_BOUNDED THEN
    REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY])

  let INTERIOR_OF_TRIANGLE ← prove
   r"!a b c:real^2.
        interior(convex hull {a,b,c}) =
        (convex hull {a,b,c}) DIFF
        (segment[a,b] UNION segment[b,c] UNION segment[c,a])"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM FRONTIER_OF_TRIANGLE, frontier] THEN
    MATCH_MP_TAC (← SET_RULE (← q r"i SUBSET s /\ c = s ==> i = s DIFF (c DIFF i)")) THEN
    REWRITE_TAC [INTERIOR_SUBSET] THEN MATCH_MP_TAC CLOSURE_CONVEX_HULL THEN
    SIMP_TAC [FINITE_IMP_COMPACT, FINITE_INSERT, FINITE_EMPTY])

  pure { FARKAS_LEMMA, FARKAS_LEMMA_ALT, SEPARATING_HYPERPLANE_POLYHEDRA,
         RELATIVE_BOUNDARY_OF_CONVEX_HULL, FRONTIER_OF_CONVEX_HULL,
         RELATIVE_BOUNDARY_OF_TRIANGLE, RELATIVE_FRONTIER_OF_TRIANGLE,
         FRONTIER_OF_TRIANGLE, INSIDE_OF_TRIANGLE, INTERIOR_OF_TRIANGLE }

/- ------------------------------------------------------------------------- -/
/- A ridge is the intersection of precisely two facets.                      -/
/- (polytope.ml 6837-7219)                                                   -/
/- ------------------------------------------------------------------------- -/

structure POQ where
  POLYHEDRON_RIDGE_TWO_FACETS : thm
  deriving Inhabited

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 2048 in
@[nospecialize]
def setupPOQ [HolBase] (D : PolytopeDeps) (BPOA : POA) (BPOG : POG) (BPOJ : POJ) (BPOK : POK) (BPOL : POL) : ExceptT String IO POQ := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_INT_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC,
        GEN_GEOM_ORIGIN_TAC, INT_ARITH, INT_ARITH_TAC, MESON, REAL_ARITH, REAL_ARITH_TAC,
        SET_RULE, SET_TAC, VECTOR_ARITH, .. } := D.cvx
  let { ARITH, CARD_CLAUSES, CONJ_ACI, CONJ_ASSOC, CONTRAPOS_THM, DIMINDEX_3, EQ_SYM_EQ,
        EXISTS_IN_INSERT, EXTENSION, FINITE_EMPTY, FINITE_INSERT, .. } := D.cvx.core1
  let { FORALL_IN_INSERT, IMAGE_CLAUSES, IMP_CONJ, IMP_IMP, INT_OF_NUM_ADD, INT_OF_NUM_LE,
        INTERS_0, INTERS_1, INTERS_2, INTERS_INSERT, .. } := D.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, IN_INTER, IN_UNIV, LEFT_AND_EXISTS_THM, LEFT_FORALL_IMP_THM,
        LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY, MONO_EXISTS, NOT_EXISTS_THM, NOT_IN_EMPTY, ..
        } := D.cvx.core3
  let { REAL_LE_ADD, REAL_LE_MUL, REAL_LE_MUL_EQ, REAL_LT_IMP_LE, REAL_LT_MUL,
        REAL_LT_MUL_EQ, .. } := D.cvx.core4
  let { REAL_MUL_RNEG, REAL_NEG_ADD, RIGHT_AND_EXISTS_THM, RIGHT_FORALL_IMP_THM,
        RIGHT_IMP_EXISTS_THM, SKOLEM_THM, SUBSET, SUBSET_TRANS, .. } := D.cvx.core5
  let { HULL_INC, HULL_SUBSET, .. } := D.cvx.misc
  let { DEPENDENT_BIGGERSET_GENERAL, DIM_SPAN, DIM_SUBSET, DOT_LADD, DOT_LMUL, DOT_RADD, ..
        } := D.cvx.vec1
  let { dependent, VECTOR_ADD_LID, VECTOR_ADD_RID, VECTOR_MUL_LZERO, .. } := D.cvx.vec4
  let { DELETE_INSERT, EMPTY_DELETE, INTER_ASSOC, .. } := D.qses
  let { DIM_ORTHOGONAL_SUM, SPAN_2, .. } := D.qvec
  let { AFF_DIM_DIM_0, AFF_DIM_EMPTY, AFF_DIM_EQ_MINUS1, AFF_DIM_GE, AFF_DIM_LE_UNIV,
        AFF_DIM_UNIV, AFFINE_HULL_EQ_SPAN, .. } := D.qcvx1
  let { RELATIVE_INTERIOR_EQ_EMPTY, .. } := D.qcvx3
  let { FACE_OF_IMP_SUBSET, .. } := BPOA
  let { facet_of, .. } := BPOG
  let { POLYHEDRON_IMP_CONVEX, .. } := BPOJ
  let { FACET_OF_POLYHEDRON_EXPLICIT, POLYHEDRON_INTER_AFFINE_PARALLEL_MINIMAL,
        RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT, .. } := BPOK
  let { FACE_OF_POLYHEDRON, .. } := BPOL
  -- @@SCOPE END

  let POLYHEDRON_RIDGE_TWO_FACETS ← (do
    let av := [← q r"a1:real^N", ← q r"a2:real^N", ← q r"a3:real^N"]
    prove
     r"!p:real^N->bool r.
    polyhedron p /\ r face_of p /\ ~(r = {}) /\ aff_dim r = aff_dim p - &2
    ==> ?f1 f2. f1 face_of p /\ aff_dim f1 = aff_dim p - &1 /\
                f2 face_of p /\ aff_dim f2 = aff_dim p - &1 /\
                 ~(f1 = f2) /\ r SUBSET f1 /\ r SUBSET f2 /\ f1 INTER f2 = r /\
                !f. f face_of p /\ aff_dim f = aff_dim p - &1 /\ r SUBSET f
                    ==> f = f1 \/ f = f2"
     (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"p:real^N->bool", ← q r"r:real^N->bool"] FACE_OF_POLYHEDRON) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [← INT_ARITH (← q r"~(p:int = p - &2)")], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&2 <= aff_dim(p:real^N->bool)") ASSUME_TAC THENL
     [MP_TAC (← ISPEC (← q r"r:real^N->bool") AFF_DIM_GE) THEN
      MP_TAC (← ISPEC (← q r"r:real^N->bool") AFF_DIM_EQ_MINUS1) THEN
      ASM_REWRITE_TAC [] THEN INT_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"{f:real^N->bool | f facet_of p /\ r SUBSET f} =
      {f | f face_of p /\ aff_dim f = aff_dim p - &1 /\ r SUBSET f}")
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN
      ASM_REWRITE_TAC [IN_ELIM_THM, facet_of] THEN
      X_GEN_TAC (← q r"f:real^N->bool") THEN
      ASM_CASES_TAC (← q r"f:real^N->bool = {}") THEN
      ASM_REWRITE_TAC [AFF_DIM_EMPTY, ← GSYM CONJ_ASSOC] THEN ASM_INT_ARITH_TAC,
      DISCH_THEN (MP_TAC o SYM)] THEN
    ASM_CASES_TAC
     (← q r"{f:real^N->bool | f face_of p /\ aff_dim f = aff_dim p - &1 /\ r SUBSET f}
      = {}")
    THENL
     [ASM_REWRITE_TAC [INTERS_0] THEN DISCH_THEN (ASSUME_TAC o SYM) THEN
      UNDISCH_TAC (← q r"aff_dim(r:real^N->bool) = aff_dim(p:real^N->bool) - &2") THEN
      ASM_REWRITE_TAC [AFF_DIM_UNIV, DIMINDEX_3] THEN
      MP_TAC (← ISPEC (← q r"p:real^N->bool") AFF_DIM_LE_UNIV) THEN INT_ARITH_TAC,
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"f1:real^N->bool") THEN STRIP_TAC THEN
    ASM_CASES_TAC
     (← q r"{f:real^N->bool | f face_of p /\ aff_dim f = aff_dim p - &1 /\ r SUBSET f}
      = {f1}")
    THENL
     [ASM_REWRITE_TAC [INTERS_1] THEN
      ASM_MESON_TAC [← INT_ARITH (← q r"~(x - &2:int = x - &1)")],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP (← SET_RULE
     (← q r"~(s = {a}) ==> a IN s ==> ?b. ~(b = a) /\ b IN s"))) THEN
    ASM_REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"f2:real^N->bool") THEN STRIP_TAC THEN
    ASM_CASES_TAC
     (← q r"{f:real^N->bool | f face_of p /\ aff_dim f = aff_dim p - &1 /\ r SUBSET f}
      = {f1,f2}")
    THENL
     [ASM_REWRITE_TAC [INTERS_2] THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [← q r"f1:real^N->bool", ← q r"f2:real^N->bool"] THEN
      ASM_REWRITE_TAC [] THEN ASM SET_TAC [],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP (← SET_RULE
     (← q r"~(s = {a,b})
      ==> a IN s /\ b IN s ==> ?c. ~(c = a) /\ ~(c = b) /\ c IN s"))) THEN
    ASM_REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"f3:real^N->bool") THEN STRIP_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC (← q r"aff_dim(r:real^N->bool) = aff_dim(p:real^N->bool) - &2") THEN
    MATCH_MP_TAC (← TAUT (← q r"~p ==> p ==> q")) THEN
    MATCH_MP_TAC (← INT_ARITH (← q r"~(p - &2:int <= x:int) ==> ~(x = p - &2)")) THEN
    DISCH_TAC THEN SUBGOAL_THEN
     (← q r"~(f1:real^N->bool = {}) /\
      ~(f2:real^N->bool = {}) /\
      ~(f3:real^N->bool = {})")
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE [AFF_DIM_EMPTY]) THEN ASM_INT_ARITH_TAC,
      ALL_TAC] THEN
    MP_TAC (← ISPEC (← q r"p:real^N->bool") POLYHEDRON_INTER_AFFINE_PARALLEL_MINIMAL) THEN
    REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM, LEFT_AND_EXISTS_THM] THEN
    ASM_REWRITE_TAC [NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
     [← q r"f:(real^N->bool)->bool", ← q r"a:(real^N->bool)->real^N",
      ← q r"b:(real^N->bool)->real"] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"vec 0:real^N = v <=> v = vec 0")] THEN
    STRIP_TAC THEN MP_TAC (← ISPECL
     [← q r"p:real^N->bool", ← q r"f:(real^N->bool)->bool", ← q r"a:(real^N->bool)->real^N",
      ← q r"b:(real^N->bool)->real"] FACET_OF_POLYHEDRON_EXPLICIT) THEN
    ASM_SIMP_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (
      MP_TAC (← SPEC (← q r"f1:real^N->bool") th) THEN
      MP_TAC (← SPEC (← q r"f2:real^N->bool") th) THEN
      MP_TAC (← SPEC (← q r"f3:real^N->bool") th))) THEN
    ASM_REWRITE_TAC [facet_of] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"h3:real^N->bool") (STRIP_ASSUME_TAC o GSYM)) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"h2:real^N->bool") (STRIP_ASSUME_TAC o GSYM)) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"h1:real^N->bool") (STRIP_ASSUME_TAC o GSYM)) THEN
    SUBGOAL_THEN (← q r"~((a:(real^N->bool)->real^N) h1 = a h2) /\
                   ~(a h2 = a h3) /\ ~(a h1 = a h3)")
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [DISJ_CASES_TAC (← REAL_ARITH
         (← q r"b(h1:real^N->bool) <= b h2 \/ b h2 <= b h1"))
        THENL
         [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"f DELETE (h2:real^N->bool)")),
          FIRST_X_ASSUM (MP_TAC o SPEC (← q r"f DELETE (h1:real^N->bool)"))] THEN
        (ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
         MATCH_MP_TAC (← SET_RULE (← q r"(p ==> s = t) ==> s PSUBSET t ==> ~p")) THEN
         DISCH_TAC THEN
         FIRST_X_ASSUM (fun th => tactic_of do
           pure (GEN_REWRITE_TAC LAND_CONV [← SYM th])) THEN
         AP_TERM_TAC)
        THENL
         [SUBGOAL_THEN (← q r"f DELETE h2 = h1 INSERT (f DIFF {h1,h2}) /\
                        f = (h2:real^N->bool) INSERT h1 INSERT (f DIFF {h1,h2})")
           (fun th => ONCE_REWRITE_TAC [th]) THENL [ASM SET_TAC [], ALL_TAC],
          SUBGOAL_THEN (← q r"f DELETE h1 = h2 INSERT (f DIFF {h1,h2}) /\
                        f = (h1:real^N->bool) INSERT h2 INSERT (f DIFF {h1,h2})")
           (fun th => ONCE_REWRITE_TAC [th]) THENL [ASM SET_TAC [], ALL_TAC]] THEN
        REWRITE_TAC [INTERS_INSERT] THEN MATCH_MP_TAC (← SET_RULE
         (← q r"b SUBSET a ==> a INTER b INTER s = b INTER s")) THEN
        FIRST_X_ASSUM (fun th => tactic_of do pure (
         MP_TAC (← SPEC (← q r"h1:real^N->bool") th) THEN
         MP_TAC (← SPEC (← q r"h2:real^N->bool") th))) THEN
        ASM_REWRITE_TAC [IMP_IMP] THEN
        DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [← GSYM th])) THEN
        REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC,
        DISJ_CASES_TAC (← REAL_ARITH
         (← q r"b(h2:real^N->bool) <= b h3 \/ b h3 <= b h2"))
        THENL
         [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"f DELETE (h3:real^N->bool)")),
          FIRST_X_ASSUM (MP_TAC o SPEC (← q r"f DELETE (h2:real^N->bool)"))] THEN
        (ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
         MATCH_MP_TAC (← SET_RULE (← q r"(p ==> s = t) ==> s PSUBSET t ==> ~p")) THEN
         DISCH_TAC THEN
         FIRST_X_ASSUM (fun th => tactic_of do
           pure (GEN_REWRITE_TAC LAND_CONV [← SYM th])) THEN
         AP_TERM_TAC)
        THENL
         [SUBGOAL_THEN (← q r"f DELETE h3 = h2 INSERT (f DIFF {h2,h3}) /\
                        f = (h3:real^N->bool) INSERT h2 INSERT (f DIFF {h2,h3})")
           (fun th => ONCE_REWRITE_TAC [th]) THENL [ASM SET_TAC [], ALL_TAC],
          SUBGOAL_THEN (← q r"f DELETE h2 = h3 INSERT (f DIFF {h2,h3}) /\
                        f = (h2:real^N->bool) INSERT h3 INSERT (f DIFF {h2,h3})")
           (fun th => ONCE_REWRITE_TAC [th]) THENL [ASM SET_TAC [], ALL_TAC]] THEN
        REWRITE_TAC [INTERS_INSERT] THEN MATCH_MP_TAC (← SET_RULE
         (← q r"b SUBSET a ==> a INTER b INTER s = b INTER s")) THEN
        FIRST_X_ASSUM (fun th => tactic_of do pure (
         MP_TAC (← SPEC (← q r"h2:real^N->bool") th) THEN
         MP_TAC (← SPEC (← q r"h3:real^N->bool") th))) THEN
        ASM_REWRITE_TAC [IMP_IMP] THEN
        DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [← GSYM th])) THEN
        REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC,
        DISJ_CASES_TAC (← REAL_ARITH
         (← q r"b(h1:real^N->bool) <= b h3 \/ b h3 <= b h1"))
        THENL
         [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"f DELETE (h3:real^N->bool)")),
          FIRST_X_ASSUM (MP_TAC o SPEC (← q r"f DELETE (h1:real^N->bool)"))] THEN
        (ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
         MATCH_MP_TAC (← SET_RULE (← q r"(p ==> s = t) ==> s PSUBSET t ==> ~p")) THEN
         DISCH_TAC THEN
         FIRST_X_ASSUM (fun th => tactic_of do
           pure (GEN_REWRITE_TAC LAND_CONV [← SYM th])) THEN
         AP_TERM_TAC)
        THENL
         [SUBGOAL_THEN (← q r"f DELETE h3 = h1 INSERT (f DIFF {h1,h3}) /\
                        f = (h3:real^N->bool) INSERT h1 INSERT (f DIFF {h1,h3})")
           (fun th => ONCE_REWRITE_TAC [th]) THENL [ASM SET_TAC [], ALL_TAC],
          SUBGOAL_THEN (← q r"f DELETE h1 = h3 INSERT (f DIFF {h1,h3}) /\
                        f = (h1:real^N->bool) INSERT h3 INSERT (f DIFF {h1,h3})")
           (fun th => ONCE_REWRITE_TAC [th]) THENL [ASM SET_TAC [], ALL_TAC]] THEN
        REWRITE_TAC [INTERS_INSERT] THEN MATCH_MP_TAC (← SET_RULE
         (← q r"b SUBSET a ==> a INTER b INTER s = b INTER s")) THEN
        FIRST_X_ASSUM (fun th => tactic_of do pure (
         MP_TAC (← SPEC (← q r"h1:real^N->bool") th) THEN
         MP_TAC (← SPEC (← q r"h3:real^N->bool") th))) THEN
        ASM_REWRITE_TAC [IMP_IMP] THEN
        DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [← GSYM th])) THEN
        REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"~({x | a h1 dot x <= b h1} INTER {x | a h2 dot x <= b h2}
        SUBSET {x | a h3 dot x <= b h3}) /\
      ~({x | a h1 dot x <= b h1} INTER {x | a h3 dot x <= b h3}
        SUBSET {x | a h2 dot x <= b h2}) /\
      ~({x | a h2 dot x <= b h2} INTER {x | a h3 dot x <= b h3}
        SUBSET {x:real^N | a(h1:real^N->bool) dot x <= b h1})")
    MP_TAC THENL
     [ASM_SIMP_TAC [] THEN REPEAT STRIP_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"f DELETE (h3:real^N->bool)")),
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"f DELETE (h2:real^N->bool)")),
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"f DELETE (h1:real^N->bool)"))] THEN
      (ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
       FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC
         (LAND_CONV o LAND_CONV) [← SYM th])) THEN
       MATCH_MP_TAC (← SET_RULE (← q r"s = t ==> s PSUBSET t ==> F")) THEN
       AP_TERM_TAC)
      THENL
       [SUBGOAL_THEN
         (← q r"f DELETE (h3:real^N->bool) = h1 INSERT h2 INSERT (f DELETE h3) /\
          f =  h1 INSERT h2 INSERT h3 INSERT (f DELETE h3)")
         (fun th => ONCE_REWRITE_TAC [th]) THENL [ASM SET_TAC [], ALL_TAC],
        SUBGOAL_THEN
         (← q r"f DELETE (h2:real^N->bool) = h1 INSERT h3 INSERT (f DELETE h2) /\
          f =  h2 INSERT h1 INSERT h3 INSERT (f DELETE h2)")
         (fun th => ONCE_REWRITE_TAC [th]) THENL [ASM SET_TAC [], ALL_TAC],
        SUBGOAL_THEN
         (← q r"f DELETE (h1:real^N->bool) = h2 INSERT h3 INSERT (f DELETE h1) /\
          f =  h1 INSERT h2 INSERT h3 INSERT (f DELETE h1)")
         (fun th => ONCE_REWRITE_TAC [th]) THENL [ASM SET_TAC [], ALL_TAC]] THEN
      REWRITE_TAC [INTERS_INSERT] THEN REWRITE_TAC [← GSYM INTER_ASSOC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"?w. (a:(real^N->bool)->real^N) h1 dot w < b h1 /\
          a h2 dot w < b h2 /\ a h3 dot w < b h3")
     (CHOOSE_THEN MP_TAC)
    THENL
     [SUBGOAL_THEN (← q r"~(relative_interior p :real^N->bool = {})") MP_TAC THENL
       [ASM_SIMP_TAC [RELATIVE_INTERIOR_EQ_EMPTY, POLYHEDRON_IMP_CONVEX] THEN
        ASM SET_TAC [],
        ALL_TAC] THEN
      MP_TAC (← ISPECL
       [← q r"p:real^N->bool", ← q r"f:(real^N->bool)->bool", ← q r"a:(real^N->bool)->real^N",
        ← q r"b:(real^N->bool)->real"] RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT) THEN
      ASM_SIMP_TAC [] THEN DISCH_THEN (K ALL_TAC : thm → tactic) THEN
      REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
      DISCH_THEN (MP_TAC o CONJUNCT2) THEN ASM_SIMP_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!x. x IN r ==> (a h1) dot (x:real^N) = b h1 /\
                     (a h2) dot x = b h2 /\
                     (a (h3:real^N->bool)) dot x = b h3")
    MP_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"?z:real^N. z IN r") CHOOSE_TAC THENL
     [ASM SET_TAC [], ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [← q r"~((a:(real^N->bool)->real^N) h1 = a h2)",
      ← q r"~((a:(real^N->bool)->real^N) h1 = a h3)",
      ← q r"~((a:(real^N->bool)->real^N) h2 = a h3)",
      ← q r"aff_dim(p:real^N->bool) - &2 <= aff_dim(r:real^N->bool)"] THEN
    MAP_EVERY (fun t => tactic_of do pure (
      FIRST_X_ASSUM (fun th => tactic_of do pure (MP_TAC (← SPEC t th) THEN ASM_REWRITE_TAC [] THEN
                              ASSUME_TAC th)) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"z:real^N") o CONJUNCT2 o CONJUNCT2)))
     [← q r"h1:real^N->bool", ← q r"h2:real^N->bool", ← q r"h3:real^N->bool"] THEN
    SUBGOAL_THEN (← q r"(z:real^N) IN (affine hull p)") ASSUME_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN ASM SET_TAC [],
      ASM_REWRITE_TAC []] THEN
    UNDISCH_TAC (← q r"(z:real^N) IN (affine hull p)") THEN
    SUBGOAL_THEN (← q r"(a h1) dot (z:real^N) = b h1 /\
                  (a h2) dot z = b h2 /\
                  (a (h3:real^N->bool)) dot z = b h3")
    (REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM))
    THENL [ASM SET_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(r:real^N->bool) SUBSET affine hull p") MP_TAC THENL
     [ASM_MESON_TAC [FACE_OF_IMP_SUBSET, HULL_SUBSET, SUBSET_TRANS], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"~((a:(real^N->bool)->real^N) h1 = vec 0) /\
      ~((a:(real^N->bool)->real^N) h2 = vec 0) /\
      ~((a:(real^N->bool)->real^N) h3 = vec 0)")
    MP_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN
    UNDISCH_TAC (← q r"(z:real^N) IN r") THEN POP_ASSUM_LIST (K ALL_TAC) THEN
    MAP_EVERY SPEC_TAC
     [(← q r"(a:(real^N->bool)->real^N) h1", ← q r"a1:real^N"),
      (← q r"(a:(real^N->bool)->real^N) h2", ← q r"a2:real^N"),
      (← q r"(a:(real^N->bool)->real^N) h3", ← q r"a3:real^N")] THEN
    REPEAT GEN_TAC THEN
    GEN_GEOM_ORIGIN_TAC (← q r"z:real^N") ["a1", "a2", "a3"] THEN
    REWRITE_TAC [VECTOR_ADD_RID, VECTOR_ADD_LID] THEN
    REWRITE_TAC [DOT_RADD, IMAGE_CLAUSES,
     ← REAL_ARITH (← q r"a + b:real <= a <=> b <= &0"),
     ← REAL_ARITH (← q r"a + b:real < a <=> b < &0"),
     ← REAL_ARITH (← q r"a + b:real = a <=> b = &0")] THEN

    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"aff_dim(p:real^N->bool) = &(dim p)") SUBST_ALL_TAC THENL
     [ASM_SIMP_TAC [AFF_DIM_DIM_0, HULL_INC], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"aff_dim(r:real^N->bool) = &(dim r)") SUBST_ALL_TAC THENL
     [ASM_SIMP_TAC [AFF_DIM_DIM_0, HULL_INC], ALL_TAC] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [INT_OF_NUM_ADD, INT_OF_NUM_LE,
      ← INT_ARITH (← q r"p - &2:int <= q <=> p <= q + &2")]) THEN
    MP_TAC (← ISPECL
     [← q r"{a1:real^N,a2,a3}", ← q r"r:real^N->bool"] DIM_ORTHOGONAL_SUM) THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    ASM_SIMP_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← ARITH_RULE
      (← q r"p <= r + 2 ==> u <= p /\ 3 <= t ==> ~(u = t + r)"))) THEN
    SUBGOAL_THEN (← q r"affine hull p :real^N->bool = span p") SUBST_ALL_TAC THENL
     [ASM_MESON_TAC [AFFINE_HULL_EQ_SPAN], ALL_TAC] THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [← GSYM DIM_SPAN] THEN
      MATCH_MP_TAC DIM_SUBSET THEN ASM SET_TAC [],
      ALL_TAC] THEN
    MP_TAC (← ISPEC (← q r"{a1:real^N,a2,a3}") DEPENDENT_BIGGERSET_GENERAL) THEN
    SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY, ARITH] THEN
    ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, ARITH] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"~(3 > x) <=> 3 <= x")] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC [dependent, EXISTS_IN_INSERT, NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC [DELETE_INSERT, EMPTY_DELETE] THEN
    REWRITE_TAC [SPAN_2, IN_ELIM_THM, IN_UNIV] THEN
    POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o HolLight.rev) THEN
    W (fun (_, w) => let fv := frees w
       MAP_EVERY (fun t => SPEC_TAC (t, t)) (subtract fv av ++ av)) THEN
    REWRITE_TAC [LEFT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC (← MESON []
     (← q r"(!a1 a2 a3. P a1 a2 a3 ==> P a2 a1 a3 /\ P a3 a1 a2) /\
      (!a1 a2 a3. Q a1 a2 a3 ==> ~(P a1 a2 a3))
      ==> !a3 a2 a1. P a1 a2 a3
                     ==> ~(Q a1 a2 a3 \/ Q a2 a1 a3 \/ Q a3 a1 a2)")) THEN
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC (← TAUT
       (← q r"(p ==> q) /\ (p ==> r) ==> p ==> q /\ r")) THEN
      CONJ_TAC THEN REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
      REWRITE_TAC [CONJ_ACI] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      ASM SET_TAC [],
      ALL_TAC] THEN
    REPEAT GEN_TAC THEN DISCH_THEN
     (X_CHOOSE_THEN (← q r"u:real") (X_CHOOSE_TAC (← q r"v:real"))) THEN
    REWRITE_TAC [NOT_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"u = &0") THENL
     [ASM_REWRITE_TAC [VECTOR_ADD_LID, VECTOR_MUL_LZERO] THEN
      REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (← REAL_ARITH
       (← q r"v = &0 \/ &0 < v \/ &0 < --v"))
      THENL
       [ASM_REWRITE_TAC [VECTOR_MUL_LZERO],
        REWRITE_TAC [DOT_LMUL, ← REAL_ARITH (← q r"a * b <= &0 <=> &0 <= a * --b")] THEN
        ASM_SIMP_TAC [REAL_LE_MUL_EQ] THEN
        REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_INTER] THEN REAL_ARITH_TAC,
        REWRITE_TAC [DOT_LMUL, ← REAL_ARITH (← q r"a * b < &0 <=> &0 < --a * b")] THEN
        ASM_SIMP_TAC [REAL_LT_MUL_EQ] THEN REAL_ARITH_TAC],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"v = &0") THENL
     [ASM_REWRITE_TAC [VECTOR_ADD_RID, VECTOR_MUL_LZERO] THEN
      REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (← REAL_ARITH
       (← q r"u = &0 \/ &0 < u \/ &0 < --u"))
      THENL
       [ASM_REWRITE_TAC [VECTOR_MUL_LZERO],
        REWRITE_TAC [DOT_LMUL, ← REAL_ARITH (← q r"a * b <= &0 <=> &0 <= a * --b")] THEN
        ASM_SIMP_TAC [REAL_LE_MUL_EQ] THEN
        REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_INTER] THEN REAL_ARITH_TAC,
        REWRITE_TAC [DOT_LMUL, ← REAL_ARITH (← q r"a * b < &0 <=> &0 < --a * b")] THEN
        ASM_SIMP_TAC [REAL_LT_MUL_EQ] THEN REAL_ARITH_TAC],
      ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"&0 < u /\ &0 < v \/ &0 < u /\ &0 < --v \/
      &0 < --u /\ &0 < v \/ &0 < --u /\ &0 < --v")
    STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC,
      UNDISCH_TAC
       (← q r"~({x | a2 dot x <= &0} INTER {x | a3 dot x <= &0} SUBSET
          {x:real^N | a1 dot x <= &0})") THEN
      ASM_REWRITE_TAC [SUBSET, IN_INTER, IN_ELIM_THM] THEN
      REWRITE_TAC [DOT_LADD, DOT_LMUL] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"x <= &0 <=> &0 <= --x")] THEN
      REWRITE_TAC [REAL_NEG_ADD, ← GSYM REAL_MUL_RNEG] THEN
      ASM_SIMP_TAC [REAL_LE_MUL, REAL_LE_ADD, REAL_LT_IMP_LE],
      UNDISCH_TAC
       (← q r"~({x | a1 dot x <= &0} INTER {x | a3 dot x <= &0} SUBSET
          {x:real^N | a2 dot x <= &0})") THEN
      ASM_REWRITE_TAC [SUBSET, IN_INTER, IN_ELIM_THM] THEN
      GEN_TAC THEN REWRITE_TAC [DOT_LADD, DOT_LMUL] THEN
      MATCH_MP_TAC (← REAL_ARITH
       (← q r"(&0 < u * a2 <=> &0 < a2) /\ (&0 < --v * a3 <=> &0 < a3)
        ==> u * a2 + v * a3 <= &0 /\ a3 <= &0 ==> a2 <= &0")) THEN
      ASM_SIMP_TAC [REAL_LT_MUL_EQ],
      UNDISCH_TAC
       (← q r"~({x | a1 dot x <= &0} INTER {x | a2 dot x <= &0} SUBSET
          {x:real^N | a3 dot x <= &0})") THEN
      ASM_REWRITE_TAC [SUBSET, IN_INTER, IN_ELIM_THM] THEN
      GEN_TAC THEN REWRITE_TAC [DOT_LADD, DOT_LMUL] THEN
      MATCH_MP_TAC (← REAL_ARITH
       (← q r"(&0 < --u * a2 <=> &0 < a2) /\ (&0 < v * a3 <=> &0 < a3)
        ==> u * a2 + v * a3 <= &0 /\ a2 <= &0 ==> a3 <= &0")) THEN
      ASM_SIMP_TAC [REAL_LT_MUL_EQ],
      UNDISCH_TAC (← q r"(a1:real^N) dot w < &0") THEN
      ASM_REWRITE_TAC [DOT_LADD, DOT_LMUL] THEN
      MATCH_MP_TAC (← REAL_ARITH
       (← q r"&0 < --u * --a /\ &0 < --v * --b ==> ~(u * a + v * b < &0)")) THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC]))

  pure { POLYHEDRON_RIDGE_TWO_FACETS }

/- ------------------------------------------------------------------------- -/
/- Lower bounds on then number of 0 and n-1 dimensional faces.               -/
/- (polytope.ml 7219-7359)                                                   -/
/- ------------------------------------------------------------------------- -/

structure POR where
  POLYTOPE_VERTEX_LOWER_BOUND : thm
  POLYTOPE_FACET_LOWER_BOUND : thm
  deriving Inhabited

set_option maxHeartbeats 8000000 in
@[nospecialize]
def setupPOR [HolBase] (D : PolytopeDeps) (BPOG : POG) (BPOJ : POJ) (BPOK : POK) (BPOL : POL) (BPOM : POM) : ExceptT String IO POR := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, GEOM_ORIGIN_TAC, INT_REDUCE_CONV,
        MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, SET_RULE, SET_TAC, VECTOR_ARITH, .. } :=
        D.cvx
  let { CARD_CLAUSES, CARD_DELETE, CARD_EQ_0, CARD_IMAGE_INJ, EMPTY_GSPEC, EQ_SYM_EQ,
        FINITE_DELETE, FINITE_IMAGE, .. } := D.cvx.core1
  let { FORALL_IN_IMAGE, HAS_SIZE, IN_DELETE, INT_LE_REFL, INT_LE_SUB_LADD, INT_LE_TRANS,
        INT_OF_NUM_ADD, INT_OF_NUM_EQ, INT_OF_NUM_LE, INTER_UNIV, INTERS_0, .. } :=
        D.cvx.core2
  let { IN_ELIM_THM, IN_INTER, IN_INTERS, LE_TRANS, LEFT_AND_EXISTS_THM,
        LEFT_IMP_EXISTS_THM, LET_TRANS, MEMBER_NOT_EMPTY, MONO_FORALL, NOT_EXISTS_THM,
        PSUBSET, REAL_ABS_DIV, REAL_ABS_NEG, REAL_DIV_RMUL, .. } := D.cvx.core3
  let { REAL_ENTIRE, REAL_LE_MUL, REAL_LE_RDIV_EQ, .. } := D.cvx.core4
  let { REAL_NEG_NEG, RIGHT_AND_EXISTS_THM, RIGHT_IMP_EXISTS_THM, SKOLEM_THM, SUBSET, .. }
        := D.cvx.core5
  let { HULL_INC, .. } := D.cvx.misc
  let { DIM_LE_CARD, DIM_SPAN, DOT_RMUL, DOT_RZERO, .. } := D.cvx.vec1
  let { DOT_SYM, NORM_EQ_0, .. } := D.cvx.vec2
  let { NORM_MUL, NORM_POS_LT, ORTHOGONAL_TO_SUBSPACE_EXISTS_GEN, REAL_ABS_NORM, SPAN_ADD,
        SPAN_MUL, SPAN_SUBSET_SUBSPACE, SPAN_SUPERSET, SUBSPACE_SPAN, .. } := D.cvx.vec3
  let { orthogonal, VECTOR_ADD_LID, .. } := D.cvx.vec4
  let { BOUNDED_POS, .. } := D.cvx.top1
  let { CARD_IMAGE_LE, .. } := D.qses
  let { DIM_EQ_0, .. } := D.qvec
  let { AFF_DIM_CONVEX_HULL, AFF_DIM_DIM_0, AFF_DIM_EMPTY, AFF_DIM_LE_CARD,
        AFFINE_HULL_EQ_SPAN, .. } := D.qcvx1
  let { FACET_OF_EMPTY, KREIN_MILMAN_MINKOWSKI, .. } := BPOG
  let { FINITE_POLYTOPE_FACETS, POLYTOPE_IMP_BOUNDED, POLYTOPE_IMP_COMPACT,
        POLYTOPE_IMP_CONVEX, .. } := BPOJ
  let { FACET_OF_POLYHEDRON_EXPLICIT, POLYHEDRON_INTER_AFFINE_PARALLEL_MINIMAL, .. } := BPOK
  let { FACETS_OF_POLYHEDRON_EXPLICIT_DISTINCT, FINITE_POLYHEDRON_EXTREME_POINTS, .. } :=
        BPOL
  let { POLYTOPE_IMP_POLYHEDRON, .. } := BPOM
  -- @@SCOPE END

  let POLYTOPE_VERTEX_LOWER_BOUND ← prove
   r"!p:real^N->bool.
        polytope p ==> aff_dim p + &1 <= &(CARD {v | v extreme_point_of p})"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC (← q r"aff_dim(convex hull {v:real^N | v extreme_point_of p}) + &1") THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC [← GSYM KREIN_MILMAN_MINKOWSKI, POLYTOPE_IMP_CONVEX,
                    POLYTOPE_IMP_COMPACT, INT_LE_REFL],
      REWRITE_TAC [AFF_DIM_CONVEX_HULL, ← GSYM INT_LE_SUB_LADD] THEN
      MATCH_MP_TAC AFF_DIM_LE_CARD THEN
      MATCH_MP_TAC FINITE_POLYHEDRON_EXTREME_POINTS THEN
      ASM_SIMP_TAC [POLYTOPE_IMP_POLYHEDRON]])

  let POLYTOPE_FACET_LOWER_BOUND ← prove
   r"!p:real^N->bool.
        polytope p /\ ~(aff_dim p = &0)
        ==> aff_dim p + &1 <= &(CARD {f | f facet_of p})"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"p:real^N->bool = {}") THEN
    ASM_SIMP_TAC [AFF_DIM_EMPTY, FACET_OF_EMPTY, EMPTY_GSPEC, CARD_CLAUSES] THEN
    CONV_TAC INT_REDUCE_CONV THEN STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"?n. {f:real^N->bool | f facet_of p} HAS_SIZE n /\ aff_dim p + &1 <= &n")
      (fun th => MESON_TAC [th, HAS_SIZE]) THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"z:real^N") MP_TAC) THEN
    POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o HolLight.rev) THEN
    GEOM_ORIGIN_TAC (← q r"z:real^N") THEN REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC (← q r"CARD {f:real^N->bool | f facet_of p}") THEN
    ASM_SIMP_TAC [FINITE_POLYTOPE_FACETS, HAS_SIZE] THEN
    UNDISCH_TAC (← q r"~(aff_dim(p:real^N->bool) = &0)") THEN
    ASM_SIMP_TAC [AFF_DIM_DIM_0, HULL_INC, INT_OF_NUM_ADD, INT_OF_NUM_LE] THEN
    REWRITE_TAC [INT_OF_NUM_EQ] THEN DISCH_TAC THEN
    MP_TAC (← ISPEC (← q r"p:real^N->bool") POLYHEDRON_INTER_AFFINE_PARALLEL_MINIMAL) THEN
    ASM_SIMP_TAC [POLYTOPE_IMP_POLYHEDRON] THEN
    REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM, LEFT_AND_EXISTS_THM] THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
     [← q r"H:(real^N->bool)->bool", ← q r"a:(real^N->bool)->real^N",
      ← q r"b:(real^N->bool)->real"] THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"vec 0:real^N = v <=> v = vec 0")] THEN
    ASM_SIMP_TAC [AFFINE_HULL_EQ_SPAN, HULL_INC] THEN
    STRIP_TAC THEN MP_TAC (← ISPECL
     [← q r"p:real^N->bool", ← q r"H:(real^N->bool)->bool", ← q r"a:(real^N->bool)->real^N",
      ← q r"b:(real^N->bool)->real"] FACET_OF_POLYHEDRON_EXPLICIT) THEN
    ASM_SIMP_TAC [AFFINE_HULL_EQ_SPAN, HULL_INC] THEN DISCH_THEN (K ALL_TAC : thm → tactic) THEN
    SUBGOAL_THEN (← q r"!h:real^N->bool. h IN H ==> &0 <= b h") ASSUME_TAC THENL
     [UNDISCH_TAC (← q r"(vec 0:real^N) IN p") THEN EXPAND_TAC "p" THEN
      REWRITE_TAC [IN_INTER, IN_INTERS] THEN DISCH_THEN (MP_TAC o CONJUNCT2) THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"h:real^N->bool") THEN
      ASM_CASES_TAC (← q r"(h:real^N->bool) IN H") THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"h:real^N->bool")) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (fun t => tactic_of do
        pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM t])) THEN
      REWRITE_TAC [IN_ELIM_THM, DOT_RZERO],
      ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC (← q r"(CARD(H:(real^N->bool)->bool))") THEN CONJ_TAC THENL
     [MATCH_MP_TAC (← ARITH_RULE (← q r"~(h <= a) ==> a + 1 <= h")) THEN DISCH_TAC THEN
      ASM_CASES_TAC (← q r"H:(real^N->bool)->bool = {}") THENL
       [UNDISCH_THEN (← q r"H:(real^N->bool)->bool = {}") SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC (REWRITE_RULE [INTERS_0, INTER_UNIV]) THEN
        UNDISCH_TAC (← q r"~(dim(p:real^N->bool) = 0)") THEN
        REWRITE_TAC [DIM_EQ_0] THEN EXPAND_TAC "p" THEN
        REWRITE_TAC [← ASSUME (← q r"H:(real^N->bool)->bool = {}"), INTERS_0] THEN
        REWRITE_TAC [INTER_UNIV] THEN
        ASM_CASES_TAC (← q r"?n:real^N. n IN span p /\ ~(n = vec 0)") THENL
         [ALL_TAC, ASM SET_TAC []] THEN
        FIRST_X_ASSUM (CHOOSE_THEN STRIP_ASSUME_TAC) THEN
        FIRST_ASSUM (MP_TAC o MATCH_MP POLYTOPE_IMP_BOUNDED) THEN
        REWRITE_TAC [BOUNDED_POS] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"B:real")
         (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"(B + &1) / norm n % n:real^N")) THEN
        ANTS_TAC THENL [ASM_MESON_TAC [SPAN_MUL], ALL_TAC] THEN
        REWRITE_TAC [NORM_MUL, REAL_ABS_DIV, REAL_ABS_NORM] THEN
        ASM_SIMP_TAC [REAL_DIV_RMUL, NORM_EQ_0] THEN REAL_ARITH_TAC,
        ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"h:real^N->bool")) THEN
      SUBGOAL_THEN
       (← q r"span(IMAGE (a:(real^N->bool)->real^N) (H DELETE h))
        PSUBSET span(p)")
      MP_TAC THENL
       [REWRITE_TAC [PSUBSET] THEN CONJ_TAC THENL
         [MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
          REWRITE_TAC [SUBSPACE_SPAN, SUBSET, FORALL_IN_IMAGE, IN_DELETE] THEN
          ASM_MESON_TAC [SPAN_ADD, SPAN_SUPERSET, VECTOR_ADD_LID],
          DISCH_THEN (MP_TAC o AP_TERM (← q r"dim:(real^N->bool)->num")) THEN
          REWRITE_TAC [DIM_SPAN] THEN FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
           (← ARITH_RULE (← q r"h <= p ==> h':num < h ==> ~(h' = p)"))) THEN
          MATCH_MP_TAC LET_TRANS THEN
          EXISTS_TAC (← q r"CARD(IMAGE (a:(real^N->bool)->real^N) (H DELETE h))") THEN
          ASM_SIMP_TAC [DIM_LE_CARD, FINITE_DELETE, FINITE_IMAGE] THEN
          MATCH_MP_TAC LET_TRANS THEN
          EXISTS_TAC (← q r"CARD(H DELETE (h:real^N->bool))") THEN
          ASM_SIMP_TAC [CARD_IMAGE_LE, FINITE_DELETE] THEN
          ASM_SIMP_TAC [CARD_DELETE, ← ARITH_RULE (← q r"n - 1 < n <=> ~(n = 0)")] THEN
          ASM_SIMP_TAC [CARD_EQ_0] THEN ASM SET_TAC []],
        DISCH_THEN (MP_TAC o MATCH_MP ORTHOGONAL_TO_SUBSPACE_EXISTS_GEN)] THEN
      REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"n:real^N") THEN STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP POLYTOPE_IMP_BOUNDED) THEN
      REWRITE_TAC [BOUNDED_POS] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"B:real") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISJ_CASES_TAC (← REAL_ARITH
       (← q r"&0 <= (a:(real^N->bool)->real^N) h dot n \/
        &0 <= --((a:(real^N->bool)->real^N) h dot n)"))
      THENL
       [DISCH_THEN (MP_TAC o SPEC (← q r"--(B + &1) / norm(n) % n:real^N")),
        DISCH_THEN (MP_TAC o SPEC (← q r"(B + &1) / norm(n) % n:real^N"))] THEN
      (ASM_SIMP_TAC [NORM_MUL, REAL_ABS_DIV, REAL_ABS_NORM,
                     REAL_DIV_RMUL, NORM_EQ_0, REAL_ABS_NEG,
                     ← REAL_ARITH (← q r"~(abs(B + &1) <= B)")] THEN
       EXPAND_TAC "p" THEN REWRITE_TAC [IN_INTER, IN_INTERS] THEN
       ASM_SIMP_TAC [SPAN_MUL] THEN X_GEN_TAC (← q r"k:real^N->bool") THEN
       DISCH_TAC THEN
       SUBGOAL_THEN (← q r"k = {x:real^N | a k dot x <= b k}") SUBST1_TAC THENL
        [ASM_SIMP_TAC [], ALL_TAC] THEN
       ASM_CASES_TAC (← q r"k:real^N->bool = h") THEN
       ASM_REWRITE_TAC [IN_ELIM_THM, DOT_RMUL] THENL
        [ALL_TAC,
         MATCH_MP_TAC (← REAL_ARITH (← q r"x = &0 /\ &0 <= y ==> x <= y")) THEN
         ASM_SIMP_TAC [REAL_ENTIRE] THEN DISJ2_TAC THEN
         FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(a:(real^N->bool)->real^N) k")) THEN
         REWRITE_TAC [orthogonal, DOT_SYM] THEN DISCH_THEN MATCH_MP_TAC THEN
         MATCH_MP_TAC SPAN_SUPERSET THEN ASM SET_TAC []]) THENL
       [MATCH_MP_TAC (← REAL_ARITH (← q r"&0 <= --x * y /\ &0 <= z ==> x * y <= z")),
        MATCH_MP_TAC (← REAL_ARITH (← q r"&0 <= x * --y /\ &0 <= z ==> x * y <= z"))] THEN
      ASM_SIMP_TAC [] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC [← REAL_ARITH (← q r"--a / b:real = --(a / b)"), REAL_NEG_NEG] THEN
      ASM_SIMP_TAC [REAL_LE_RDIV_EQ, NORM_POS_LT] THEN ASM_REAL_ARITH_TAC,
      REWRITE_TAC [← SET_RULE (← q r"{f | ?h. h IN s /\ f = g h} = IMAGE g s")] THEN
      MATCH_MP_TAC (← ARITH_RULE (← q r"m:num = n ==> n <= m")) THEN
      MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC FACETS_OF_POLYHEDRON_EXPLICIT_DISTINCT THEN
      ASM_SIMP_TAC [AFFINE_HULL_EQ_SPAN, HULL_INC]])

  pure { POLYTOPE_VERTEX_LOWER_BOUND, POLYTOPE_FACET_LOWER_BOUND }

/- ------------------------------------------------------------------------- -/
/- The notion of n-simplex where n is an integer >= -1.                      -/
/- (polytope.ml 7359-7759)                                                   -/
/- ------------------------------------------------------------------------- -/

structure POS where
  simplex : thm
  SIMPLEX_TRANSLATION_EQ : thm
  SIMPLEX_LINEAR_IMAGE_EQ : thm
  SIMPLEX : thm
  SIMPLEX_CONVEX_HULL : thm
  SIMPLEX_IMP_POLYTOPE : thm
  SIMPLEX_IMP_POLYHEDRON : thm
  SIMPLEX_IMP_CONVEX : thm
  SIMPLEX_IMP_COMPACT : thm
  SIMPLEX_IMP_CLOSED : thm
  SIMPLEX_DIM_GE : thm
  SIMPLEX_EMPTY : thm
  SIMPLEX_MINUS_1 : thm
  AFF_DIM_SIMPLEX : thm
  SIMPLEX_EXTREME_POINTS : thm
  SIMPLEX_FACE_OF_SIMPLEX : thm
  FACE_OF_SIMPLEX_SUBSET : thm
  SUBSET_FACE_OF_SIMPLEX : thm
  FACES_OF_SIMPLEX : thm
  HAS_SIZE_FACES_OF_SIMPLEX : thm
  FINITE_FACES_OF_SIMPLEX : thm
  CARD_FACES_OF_SIMPLEX : thm
  CHOOSE_SIMPLEX : thm
  CHOOSE_SURROUNDING_SIMPLEX : thm
  CHOOSE_SURROUNDING_SIMPLEX_FULL : thm
  CHOOSE_POLYTOPE : thm
  SIMPLEX_SING : thm
  SIMPLEX_ZERO : thm
  SIMPLEX_SEGMENT_CASES : thm
  SIMPLEX_SEGMENT : thm
  POLYTOPE_LOWDIM_IMP_SIMPLEX : thm
  SIMPLEX_INSERT_DIMPLUS1 : thm
  SIMPLEX_INSERT : thm
  SIMPLEX_ALT : thm
  SIMPLEX_ALT1 : thm
  SIMPLEX_0_NOT_IN_AFFINE_HULL : thm
  SIMPLEX_EXTREME_POINTS_NONEMPTY : thm
  deriving Inhabited

set_option maxHeartbeats 8000000 in
@[nospecialize]
def setupPOS [HolBase] (D : PolytopeDeps) (BPOB : POB) (BPOE : POE) (BPOG : POG) (BPOH : POH) (BPOJ : POJ) (BPOM : POM) : ExceptT String IO POS := do
  -- @@SCOPE BEGIN
  let { add_linear_invariants, add_translation_invariants, ASM_INT_ARITH_TAC, ASM_MESON_TAC,
        GEOM_TRANSFORM_TAC, GEOM_TRANSLATE_TAC, HAS_SIZE_CONV, INT_ARITH, INT_ARITH_TAC,
        MESON, MESON_TAC, new_definition, parse_as_infix, SET_RULE, SET_TAC, VECTOR_ARITH,
        .. } := D.cvx
  let { CARD_CLAUSES, CARD_EQ_0, CARD_SING, CARD_SUBSET, CONJ_ASSOC, CONJ_SYM,
        CONTRAPOS_THM, DIMINDEX_GE_1, EQ_SYM_EQ, EXISTS_REFL, EXTENSION, FINITE_EMPTY,
        FINITE_SING, .. } := D.cvx.core1
  let { HAS_SIZE, HAS_SIZE_IMAGE_INJ, IMP_CONJ, INT_ADD_LINV, INT_LE_REFL, INT_OF_NUM_EQ,
        INT_OF_NUM_EXISTS, INT_OF_NUM_LE, INT_OF_NUM_SUC, INT_POS, INT_SUB_ADD, .. } :=
        D.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, IN_SING, LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY, MONO_EXISTS,
        NOT_EXISTS_THM, NOT_IMP, .. } := D.cvx.core3
  let { RIGHT_IMP_FORALL_THM, SIMPLE_IMAGE_GEN, SUBSET, SUBSET_ANTISYM_EQ, .. } :=
        D.cvx.core5
  let { UNWIND_THM2, .. } := D.cvx.core6
  let { HULL_INC, HULL_MONO, HULL_SUBSET, .. } := D.cvx.misc
  let { BASIS_EXISTS, CHOOSE_SUBSPACE_OF_SUBSPACE, DIM_UNIV, .. } := D.cvx.vec1
  let { INDEPENDENT_NONZERO, .. } := D.cvx.vec2
  let { independent, .. } := D.cvx.vec4
  let { FINITE_IMP_COMPACT, .. } := D.cvx.top3
  let { SEGMENT_REFL, .. } := D.cvx.top5
  let { HAS_SIZE_POWERSET, INT_ADD_LID, NUM_OF_INT_OF_NUM, PSUBSET_ALT, .. } := D.qses
  let { INDEPENDENT_IMP_FINITE, .. } := D.qvec
  let { HULL_UNION_RIGHT, .. } := D.qmisc
  let { AFF_DIM_AFFINE_INDEPENDENT, AFF_DIM_CONVEX_HULL, AFF_DIM_EMPTY, AFF_DIM_EQ_FULL,
        AFF_DIM_SING, AFFINE_DEPENDENT_MONO, AFFINE_HULL_CONVEX_HULL, AFFINE_INDEPENDENT_1,
        AFFINE_INDEPENDENT_2, AFFINE_INDEPENDENT_EMPTY, AFFINE_INDEPENDENT_IMP_FINITE,
        AFFINE_INDEPENDENT_INSERT, COLLINEAR_AFF_DIM, COMPACT_CONVEX_COLLINEAR_SEGMENT, .. }
        := D.qcvx1
  let { COMPACT_CONVEX_HULL, CONVEX_CONVEX_HULL, CONVEX_HULL_EMPTY, CONVEX_HULL_EQ_EMPTY,
        CONVEX_HULL_SING, CONVEX_HULL_SUBSET_AFFINE_HULL, .. } := D.qcvx2
  let { affine_dependent, DEPENDENT_AFFINE_DEPENDENT_CASES, DISJOINT_AFFINE_HULL,
        INDEPENDENT_IMP_AFFINE_DEPENDENT_0, RELATIVE_INTERIOR_EQ_EMPTY,
        RELATIVE_INTERIOR_INTERIOR, RELATIVE_INTERIOR_TRANSLATION, SEGMENT_CONVEX_HULL, .. }
        := D.qcvx3
  let { FACE_OF_CONVEX_HULLS, .. } := BPOB
  let { EXTREME_POINT_OF_CONVEX_HULL, .. } := BPOE
  let { EXTREME_POINT_EXISTS_CONVEX, KREIN_MILMAN_MINKOWSKI, .. } := BPOG
  let { FACE_OF_CONVEX_HULL_SUBSET, .. } := BPOH
  let { polytope, POLYTOPE_IMP_CLOSED, POLYTOPE_IMP_COMPACT, POLYTOPE_IMP_CONVEX, .. } :=
        BPOJ
  let { POLYTOPE_IMP_POLYHEDRON, .. } := BPOM
  -- @@SCOPE END

  parse_as_infix ("simplex", (12, "right"))

  let simplex ← new_definition
   r"n simplex s <=> ?c. ~(affine_dependent c) /\
                      &(CARD c):int = n + &1 /\
                      s = convex hull c"

  let SIMPLEX_TRANSLATION_EQ ← prove
   r"!a:real^N s n. n simplex (IMAGE (\x. a + x) s) <=> n simplex s"
   (REWRITE_TAC [simplex] THEN
    ONCE_REWRITE_TAC [← MESON [HAS_SIZE, AFFINE_INDEPENDENT_IMP_FINITE]
     (← q r"~affine_dependent c /\ P(CARD c) <=>
      ~affine_dependent c /\ ?n. c HAS_SIZE n /\ P n")] THEN
    GEOM_TRANSLATE_TAC [])

  add_translation_invariants [SIMPLEX_TRANSLATION_EQ]

  let SIMPLEX_LINEAR_IMAGE_EQ ← prove
   r"!f:real^M->real^N s n.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (n simplex (IMAGE f s) <=> n simplex s)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [simplex] THEN
    ONCE_REWRITE_TAC [← MESON [HAS_SIZE, AFFINE_INDEPENDENT_IMP_FINITE]
     (← q r"~affine_dependent c /\ P(CARD c) <=>
      ~affine_dependent c /\ ?n. c HAS_SIZE n /\ P n")]  THEN
    MATCH_MP_TAC (← MESON []
     (← q r"!f. (!a. P(f a) <=> Q a) /\ (!b. P b ==> ?a. b = f a)
          ==> ((?b. P b) <=> (?a. Q a))")) THEN
    EXISTS_TAC (← q r"IMAGE (f:real^M->real^N)") THEN CONJ_TAC THENL
     [POP_ASSUM MP_TAC THEN REWRITE_TAC [RIGHT_IMP_FORALL_THM] THEN
      MAP_EVERY (fun x => SPEC_TAC (x, x))
       [← q r"n:num", ← q r"s:real^N->bool", ← q r"f:real^M->real^N"] THEN
      GEOM_TRANSFORM_TAC [],
      X_GEN_TAC (← q r"d:real^N->bool") THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"{x | (f:real^M->real^N) x IN d}") THEN
      SUBGOAL_THEN (← q r"(d:real^N->bool) SUBSET convex hull d") MP_TAC THENL
       [REWRITE_TAC [HULL_SUBSET], ASM SET_TAC []]])

  add_linear_invariants [SIMPLEX_LINEAR_IMAGE_EQ]

  let SIMPLEX ← prove
   r"n simplex s <=> ?c. FINITE c /\
                       ~(affine_dependent c) /\
                       &(CARD c):int = n + &1 /\
                       s = convex hull c"
   (REWRITE_TAC [simplex] THEN MESON_TAC [AFFINE_INDEPENDENT_IMP_FINITE])

  let SIMPLEX_CONVEX_HULL ← prove
   r"!c:real^N->bool n.
    ~affine_dependent c /\ &(CARD c) = n + &1 ==> n simplex (convex hull c)"
   (REWRITE_TAC [simplex] THEN MESON_TAC [])

  let SIMPLEX_IMP_POLYTOPE ← prove
   r"!n s. n simplex s ==> polytope s"
   (REWRITE_TAC [simplex, polytope] THEN
    MESON_TAC [AFFINE_INDEPENDENT_IMP_FINITE])

  let SIMPLEX_IMP_POLYHEDRON ← prove
   r"!s n. n simplex s ==> polyhedron s"
   (MESON_TAC [SIMPLEX_IMP_POLYTOPE, POLYTOPE_IMP_POLYHEDRON])

  let SIMPLEX_IMP_CONVEX ← prove
   r"!s:real^N->bool n. n simplex s ==> convex s"
   (MESON_TAC [SIMPLEX_IMP_POLYTOPE, POLYTOPE_IMP_CONVEX])

  let SIMPLEX_IMP_COMPACT ← prove
   r"!s:real^N->bool n. n simplex s ==> compact s"
   (MESON_TAC [SIMPLEX_IMP_POLYTOPE, POLYTOPE_IMP_COMPACT])

  let SIMPLEX_IMP_CLOSED ← prove
   r"!s:real^N->bool n. n simplex s ==> closed s"
   (MESON_TAC [SIMPLEX_IMP_POLYTOPE, POLYTOPE_IMP_CLOSED])

  let SIMPLEX_DIM_GE ← prove
   r"!n s. n simplex s ==> -- &1 <= n"
   (REWRITE_TAC [simplex] THEN INT_ARITH_TAC)

  let SIMPLEX_EMPTY ← prove
   r"!n. n simplex {} <=> n = -- &1"
   (GEN_TAC THEN REWRITE_TAC [SIMPLEX] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    REWRITE_TAC [CONVEX_HULL_EQ_EMPTY, CONJ_ASSOC] THEN
    ONCE_REWRITE_TAC [CONJ_SYM] THEN REWRITE_TAC [UNWIND_THM2] THEN
    REWRITE_TAC [FINITE_EMPTY, CARD_CLAUSES, AFFINE_INDEPENDENT_EMPTY] THEN
    INT_ARITH_TAC)

  let SIMPLEX_MINUS_1 ← prove
   r"!s. (-- &1) simplex s <=> s = {}"
   (GEN_TAC THEN REWRITE_TAC [SIMPLEX, INT_ADD_LINV, INT_OF_NUM_EQ] THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"a /\ b <=> ~(a ==> ~b)")] THEN
    SIMP_TAC [CARD_EQ_0] THEN REWRITE_TAC [NOT_IMP] THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"a /\ b /\ c /\ d <=> c /\ a /\ b /\ d")] THEN
    REWRITE_TAC [UNWIND_THM2, FINITE_EMPTY, AFFINE_INDEPENDENT_EMPTY] THEN
    REWRITE_TAC [CONVEX_HULL_EMPTY])

  let AFF_DIM_SIMPLEX ← prove
   r"!s n. n simplex s ==> aff_dim s = n"
   (REWRITE_TAC [simplex, ← INT_ARITH (← q r"x:int = n + &1 <=> n = x - &1")] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [AFF_DIM_CONVEX_HULL, AFF_DIM_AFFINE_INDEPENDENT])

  let SIMPLEX_EXTREME_POINTS ← prove
   r"!n s:real^N->bool.
       n simplex s
       ==> FINITE {v | v extreme_point_of s} /\
           ~(affine_dependent {v | v extreme_point_of s}) /\
           &(CARD {v | v extreme_point_of s}) = n + &1 /\
           s = convex hull {v | v extreme_point_of s}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [SIMPLEX, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"c:real^N->bool") THEN DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN
    SUBGOAL_THEN (← q r"{v:real^N | v extreme_point_of s} = c")
     (fun th => ASM_REWRITE_TAC [th]) THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC (← SET_RULE (← q r"s SUBSET t /\ ~(s PSUBSET t) ==> s = t")) THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM, EXTREME_POINT_OF_CONVEX_HULL] THEN
    ABBREV_TAC (← q r"c' = {v:real^N | v extreme_point_of (convex hull c)}") THEN
    DISCH_TAC THEN
    SUBGOAL_THEN (← q r"convex hull c:real^N->bool = convex hull c'") ASSUME_TAC THENL
     [EXPAND_TAC "c'" THEN MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
      REWRITE_TAC [CONVEX_CONVEX_HULL] THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
      ASM_MESON_TAC [HAS_SIZE, FINITE_IMP_COMPACT],
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [PSUBSET_ALT]) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"a:real^N") STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [affine_dependent]) THEN
      REWRITE_TAC [] THEN EXISTS_TAC (← q r"a:real^N") THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"(a:real^N) IN convex hull c'") MP_TAC THENL
       [ASM_MESON_TAC [HULL_INC], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE [SUBSET]
        CONVEX_HULL_SUBSET_AFFINE_HULL)) THEN
      SUBGOAL_THEN (← q r"c' SUBSET (c DELETE (a:real^N))") MP_TAC THENL
       [ASM SET_TAC [], ASM_MESON_TAC [HULL_MONO, SUBSET]]])

  let SIMPLEX_FACE_OF_SIMPLEX ← prove
   r"!n s f:real^N->bool.
        n simplex s /\ f face_of s ==> ?m. m <= n /\ m simplex f"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [SIMPLEX]) THEN
    REWRITE_TAC [HAS_SIZE, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"c:real^N->bool") THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN (← q r"?c':real^N->bool. c' SUBSET c /\ f = convex hull c'")
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC [FACE_OF_CONVEX_HULL_SUBSET, FINITE_IMP_COMPACT], ALL_TAC] THEN
    EXISTS_TAC (← q r"&(CARD(c':real^N->bool)) - &1:int") THEN ASM_REWRITE_TAC [] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ] CARD_SUBSET)) THEN
      ASM_REWRITE_TAC [← GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC,
      REWRITE_TAC [simplex] THEN EXISTS_TAC (← q r"c':real^N->bool") THEN
      ASM_REWRITE_TAC [← INT_ARITH (← q r"a - &1 + &1:int = a")] THEN
      ASM_MESON_TAC [AFFINE_DEPENDENT_MONO]])

  let FACE_OF_SIMPLEX_SUBSET ← prove
   r"!n s f:real^N->bool.
        n simplex s /\ f face_of s
        ==> ?c. c SUBSET {x | x extreme_point_of s} /\ f = convex hull c"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP SIMPLEX_EXTREME_POINTS) THEN
    ABBREV_TAC (← q r"c = {x:real^N | x extreme_point_of s}") THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [HAS_SIZE]) THEN
    ASM_MESON_TAC [FACE_OF_CONVEX_HULL_SUBSET, FINITE_IMP_COMPACT])

  let SUBSET_FACE_OF_SIMPLEX ← prove
   r"!s n c:real^N->bool.
      n simplex s /\ c SUBSET {x | x extreme_point_of s}
      ==> (convex hull c) face_of s"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP SIMPLEX_EXTREME_POINTS) THEN
    REWRITE_TAC [HAS_SIZE] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC FACE_OF_CONVEX_HULLS THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← SET_RULE (← q r"!t. u SUBSET t /\ DISJOINT s t ==> DISJOINT s u")) THEN
    EXISTS_TAC (← q r"affine hull ({v:real^N | v extreme_point_of s} DIFF c)") THEN
    REWRITE_TAC [CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
    MATCH_MP_TAC DISJOINT_AFFINE_HULL THEN
    EXISTS_TAC (← q r"{v:real^N | v extreme_point_of s}") THEN
    ASM_REWRITE_TAC [] THEN SET_TAC [])

  let FACES_OF_SIMPLEX ← prove
   r"!n s. n simplex s
         ==> {f | f face_of s} =
             {convex hull c | c SUBSET {v | v extreme_point_of s}}"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    ASM_MESON_TAC [FACE_OF_SIMPLEX_SUBSET, SUBSET_FACE_OF_SIMPLEX])

  let HAS_SIZE_FACES_OF_SIMPLEX ← prove
   r"!n s:real^N->bool.
        n simplex s
        ==> {f | f face_of s} HAS_SIZE 2 EXP (num_of_int(n + &1))"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP FACES_OF_SIMPLEX) THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o GSYM o MATCH_MP SIMPLEX_EXTREME_POINTS) THEN
    ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    REWRITE_TAC [IN_ELIM_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ],
      MATCH_MP_TAC HAS_SIZE_POWERSET THEN
      ASM_REWRITE_TAC [HAS_SIZE, NUM_OF_INT_OF_NUM]] THEN
    SUBGOAL_THEN
     (← q r"!a b. a SUBSET {v:real^N | v extreme_point_of s} /\
            b SUBSET {v | v extreme_point_of s} /\
            convex hull a SUBSET convex hull b
            ==> a SUBSET b")
     (fun th => MESON_TAC [th]) THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:real^N") THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [affine_dependent]) THEN
    REWRITE_TAC [NOT_EXISTS_THM] THEN DISCH_THEN (MP_TAC o SPEC (← q r"x:real^N")) THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN REWRITE_TAC [] THEN
    CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC (← SET_RULE
     (← q r"!s t u. x IN s /\ s SUBSET t /\ t SUBSET u /\ u SUBSET v ==> x IN v")) THEN
    MAP_EVERY EXISTS_TAC
     [← q r"convex hull a:real^N->bool", ← q r"convex hull b:real^N->bool",
      ← q r"affine hull b:real^N->bool"] THEN
    ASM_SIMP_TAC [HULL_INC, CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
    MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC [])

  let FINITE_FACES_OF_SIMPLEX ← prove
   r"!n s. n simplex s ==> FINITE {f | f face_of s}"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP HAS_SIZE_FACES_OF_SIMPLEX) THEN
    SIMP_TAC [HAS_SIZE])

  let CARD_FACES_OF_SIMPLEX ← prove
   r"!n s. n simplex s ==> CARD {f | f face_of s} = 2 EXP (num_of_int(n + &1))"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP HAS_SIZE_FACES_OF_SIMPLEX) THEN
    SIMP_TAC [HAS_SIZE])

  let CHOOSE_SIMPLEX ← prove
   r"!n. --(&1) <= n /\ n <= &(dimindex(:N)) ==> ?s:real^N->bool. n simplex s"
   (X_GEN_TAC (← q r"d:int") THEN
    REWRITE_TAC [← INT_ARITH (← q r"--(&1):int <= n <=> n = --(&1) \/ &0 <= n")] THEN
    DISCH_THEN (CONJUNCTS_THEN2 DISJ_CASES_TAC MP_TAC) THENL
     [ASM_MESON_TAC [SIMPLEX_EMPTY], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM INT_OF_NUM_EXISTS]) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") SUBST1_TAC) THEN
    REWRITE_TAC [INT_OF_NUM_LE, ← GSYM DIM_UNIV] THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP CHOOSE_SUBSPACE_OF_SUBSPACE) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"s:real^N->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPEC (← q r"s:real^N->bool") BASIS_EXISTS) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"c:real^N->bool") THEN STRIP_TAC THEN
    EXISTS_TAC (← q r"convex hull ((vec 0:real^N) INSERT c)") THEN
    REWRITE_TAC [simplex] THEN EXISTS_TAC (← q r"(vec 0:real^N) INSERT c") THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP INDEPENDENT_NONZERO) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP INDEPENDENT_IMP_FINITE) THEN
    ASM_SIMP_TAC [CARD_CLAUSES, ← GSYM INT_OF_NUM_SUC] THEN
    ASM_SIMP_TAC [INDEPENDENT_IMP_AFFINE_DEPENDENT_0] THEN
    ASM_MESON_TAC [HAS_SIZE])

  let CHOOSE_SURROUNDING_SIMPLEX ← prove
   r"!a:real^N n.
        &0 <= n /\ n <= &(dimindex (:N))
        ==>  ?s. n simplex s /\ a IN relative_interior s"
   (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"n:int") CHOOSE_SIMPLEX) THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"c:real^N->bool")) THEN
    SUBGOAL_THEN (← q r"~(relative_interior c:real^N->bool = {})") MP_TAC THENL
     [FIRST_ASSUM (ASSUME_TAC o MATCH_MP SIMPLEX_IMP_CONVEX) THEN
      ASM_SIMP_TAC [RELATIVE_INTERIOR_EQ_EMPTY] THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
      ASM_REWRITE_TAC [AFF_DIM_EMPTY] THEN ASM_INT_ARITH_TAC,
      REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"b:real^N") THEN STRIP_TAC THEN
      EXISTS_TAC (← q r"IMAGE (\x:real^N. (a - b) + x) c") THEN
      ASM_REWRITE_TAC [SIMPLEX_TRANSLATION_EQ, RELATIVE_INTERIOR_TRANSLATION] THEN
      REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"b:real^N") THEN
      ASM_REWRITE_TAC [] THEN CONV_TAC (fun t => VECTOR_ARITH t)])

  let CHOOSE_SURROUNDING_SIMPLEX_FULL ← prove
   r"!a:real^N. ?s. &(dimindex(:N)) simplex s /\ a IN interior s"
   (GEN_TAC THEN MP_TAC (← ISPECL [← q r"a:real^N", ← q r"&(dimindex(:N)):int"]
      CHOOSE_SURROUNDING_SIMPLEX) THEN
    REWRITE_TAC [INT_POS, INT_LE_REFL] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_MESON_TAC [RELATIVE_INTERIOR_INTERIOR, AFF_DIM_EQ_FULL,
                   AFF_DIM_SIMPLEX])

  let CHOOSE_POLYTOPE ← prove
   r"!n. --(&1) <= n /\ n <= &(dimindex(:N))
       ==> ?s:real^N->bool. polytope s /\ aff_dim s = n"
   (MESON_TAC [CHOOSE_SIMPLEX, SIMPLEX_IMP_POLYTOPE, AFF_DIM_SIMPLEX])

  let SIMPLEX_SING ← prove
   r"!n a:real^N. n simplex {a} <=> n = &0"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
      REWRITE_TAC [AFF_DIM_SING, EQ_SYM_EQ],
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [simplex] THEN
      EXISTS_TAC (← q r"{a:real^N}") THEN
      REWRITE_TAC [AFFINE_INDEPENDENT_1, CONVEX_HULL_SING] THEN
      REWRITE_TAC [CARD_SING, INT_ADD_LID]])

  let SIMPLEX_ZERO ← prove
   r"!s:real^N->bool. &0 simplex s <=> ?a. s = {a}"
   (GEN_TAC THEN EQ_TAC THENL [ALL_TAC, MESON_TAC [SIMPLEX_SING]] THEN
    REWRITE_TAC [simplex, INT_ADD_LID, INT_OF_NUM_EQ] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:real^N->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ExceptT.mk (HAS_SIZE_CONV (← q r"(t:real^N->bool) HAS_SIZE 1"))) THEN
    ASM_SIMP_TAC [AFFINE_INDEPENDENT_IMP_FINITE, HAS_SIZE] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [CONVEX_HULL_SING] THEN MESON_TAC [])

  let SIMPLEX_SEGMENT_CASES ← prove
   r"!a b:real^N. (if a = b then &0 else &1) simplex segment[a,b]"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [SEGMENT_REFL, SIMPLEX_SING] THEN
    REWRITE_TAC [simplex] THEN EXISTS_TAC (← q r"{a:real^N,b}") THEN
    ASM_REWRITE_TAC [SEGMENT_CONVEX_HULL, AFFINE_INDEPENDENT_2] THEN
    ASM_SIMP_TAC [CARD_CLAUSES, FINITE_SING, IN_SING, CARD_SING] THEN
    REWRITE_TAC [← GSYM INT_OF_NUM_SUC] THEN INT_ARITH_TAC)

  let SIMPLEX_SEGMENT ← prove
   r"!a b. ?n. n simplex segment[a,b]"
   (MESON_TAC [SIMPLEX_SEGMENT_CASES])

  let POLYTOPE_LOWDIM_IMP_SIMPLEX ← prove
   r"!p:real^N->bool. polytope p /\ aff_dim p <= &1 ==> ?n. n simplex p"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"p:real^N->bool = {}") THEN
    ASM_REWRITE_TAC [SIMPLEX_EMPTY, EXISTS_REFL, ← GSYM COLLINEAR_AFF_DIM] THEN
    STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"p:real^N->bool") COMPACT_CONVEX_COLLINEAR_SEGMENT) THEN
    ASM_SIMP_TAC [POLYTOPE_IMP_CONVEX, POLYTOPE_IMP_COMPACT] THEN
    MESON_TAC [SIMPLEX_SEGMENT])

  let SIMPLEX_INSERT_DIMPLUS1 ← prove
   r"!n s a:real^N.
        n simplex s /\ ~(a IN affine hull s)
        ==> (n + &1) simplex (convex hull (a INSERT s))"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [simplex]) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"k:real^N->bool") STRIP_ASSUME_TAC) THEN
    REWRITE_TAC [simplex] THEN EXISTS_TAC (← q r"(a:real^N) INSERT k") THEN
    UNDISCH_TAC (← q r"~((a:real^N) IN affine hull s)") THEN
    ASM_SIMP_TAC [AFFINE_HULL_CONVEX_HULL, AFFINE_INDEPENDENT_INSERT] THEN
    ASM_CASES_TAC (← q r"(a:real^N) IN k") THENL [ASM_MESON_TAC [HULL_INC], ALL_TAC] THEN
    ASM_SIMP_TAC [CARD_CLAUSES, AFFINE_INDEPENDENT_IMP_FINITE] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC [← GSYM INT_OF_NUM_SUC] THEN
    ONCE_REWRITE_TAC [← SET_RULE (← q r"a INSERT s = {a} UNION s")] THEN
    REWRITE_TAC [← GSYM HULL_UNION_RIGHT])

  let SIMPLEX_INSERT ← prove
   r"!s a:real^N.
        (?n. n simplex s) /\ ~(a IN affine hull s)
        ==> ?n. n simplex (convex hull (a INSERT s))"
   (MESON_TAC [SIMPLEX_INSERT_DIMPLUS1])

  let SIMPLEX_ALT ← prove
   r"!s:real^N->bool i.
        i simplex s <=>
          convex s /\ compact s /\
          FINITE {v | v extreme_point_of s} /\
          &(CARD {v | v extreme_point_of s}) = i + &1 /\
          ~affine_dependent {v | v extreme_point_of s}"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [MESON_TAC [SIMPLEX_EXTREME_POINTS, SIMPLEX_IMP_CONVEX, SIMPLEX_IMP_COMPACT],
      STRIP_TAC THEN REWRITE_TAC [simplex] THEN
      EXISTS_TAC (← q r"{v:real^N | v extreme_point_of s}") THEN
      ASM_MESON_TAC [KREIN_MILMAN_MINKOWSKI]])

  let SIMPLEX_ALT1 ← prove
   r"!s:real^N->bool.
        (&n - &1) simplex s <=>
          convex s /\ compact s /\
          {v | v extreme_point_of s} HAS_SIZE n /\
          ~affine_dependent {v | v extreme_point_of s}"
   (REWRITE_TAC [SIMPLEX_ALT, INT_SUB_ADD, INT_OF_NUM_EQ, HAS_SIZE] THEN
    CONV_TAC (fun t => TAUT t))

  let SIMPLEX_0_NOT_IN_AFFINE_HULL ← prove
   r"!s:real^N->bool.
        (&n - &1) simplex s /\ ~(vec 0 IN affine hull s) <=>
        convex s /\ compact s /\
        {v | v extreme_point_of s} HAS_SIZE n /\
        independent {v | v extreme_point_of s}"
   (GEN_TAC THEN
    MP_TAC (← ISPEC (← q r"s:real^N->bool") KREIN_MILMAN_MINKOWSKI) THEN
    REWRITE_TAC [independent, DEPENDENT_AFFINE_DEPENDENT_CASES,
                 SIMPLEX_ALT1] THEN
    MESON_TAC [AFFINE_HULL_CONVEX_HULL])

  let SIMPLEX_EXTREME_POINTS_NONEMPTY ← prove
   r"!c. &(dimindex (:N)) - &1 simplex c ==> ~({v | v extreme_point_of c} = {})"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM] THEN
    MATCH_MP_TAC EXTREME_POINT_EXISTS_CONVEX THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [SIMPLEX_IMP_COMPACT],
      ASM_MESON_TAC [SIMPLEX_IMP_CONVEX],
      DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [SIMPLEX_EMPTY]) THEN
      MATCH_MP_TAC (← INT_ARITH (← q r"&1:int <= d ==> d - &1 = -- &1 ==> F")) THEN
      REWRITE_TAC [INT_OF_NUM_LE, DIMINDEX_GE_1]])

  pure { simplex, SIMPLEX_TRANSLATION_EQ, SIMPLEX_LINEAR_IMAGE_EQ, SIMPLEX,
         SIMPLEX_CONVEX_HULL, SIMPLEX_IMP_POLYTOPE, SIMPLEX_IMP_POLYHEDRON,
         SIMPLEX_IMP_CONVEX, SIMPLEX_IMP_COMPACT, SIMPLEX_IMP_CLOSED, SIMPLEX_DIM_GE,
         SIMPLEX_EMPTY, SIMPLEX_MINUS_1, AFF_DIM_SIMPLEX, SIMPLEX_EXTREME_POINTS,
         SIMPLEX_FACE_OF_SIMPLEX, FACE_OF_SIMPLEX_SUBSET, SUBSET_FACE_OF_SIMPLEX,
         FACES_OF_SIMPLEX, HAS_SIZE_FACES_OF_SIMPLEX, FINITE_FACES_OF_SIMPLEX,
         CARD_FACES_OF_SIMPLEX, CHOOSE_SIMPLEX, CHOOSE_SURROUNDING_SIMPLEX,
         CHOOSE_SURROUNDING_SIMPLEX_FULL, CHOOSE_POLYTOPE, SIMPLEX_SING, SIMPLEX_ZERO,
         SIMPLEX_SEGMENT_CASES, SIMPLEX_SEGMENT, POLYTOPE_LOWDIM_IMP_SIMPLEX,
         SIMPLEX_INSERT_DIMPLUS1, SIMPLEX_INSERT, SIMPLEX_ALT, SIMPLEX_ALT1,
         SIMPLEX_0_NOT_IN_AFFINE_HULL, SIMPLEX_EXTREME_POINTS_NONEMPTY }

/- ------------------------------------------------------------------------- -/
/- Simplicial complexes and triangulations. (polytope.ml 7759-7975)          -/
/- ------------------------------------------------------------------------- -/

structure POT where
  simplicial_complex : thm
  triangulation : thm
  SIMPLICIAL_COMPLEX_TRANSLATION : thm
  SIMPLICIAL_COMPLEX_LINEAR_IMAGE : thm
  TRIANGULATION_TRANSLATION : thm
  TRIANGULATION_LINEAR_IMAGE : thm
  SIMPLICIAL_COMPLEX_IMP_TRIANGULATION : thm
  TRIANGULATION_SUBSET : thm
  TRIANGULATION_UNION : thm
  TRIANGULATION_INTER_SIMPLEX : thm
  TRIANGULATION_SIMPLICIAL_COMPLEX : thm
  TRIANGULATION_SIMPLEX_FACES : thm
  TRIANGULATION_SIMPLEX_FACETS : thm
  CELL_COMPLEX_DISJOINT_RELATIVE_INTERIORS : thm
  TRIANGULATION_DISJOINT_RELATIVE_INTERIORS : thm
  SIMPLICIAL_COMPLEX_DISJOINT_RELATIVE_INTERIORS : thm
  NOT_IN_AFFINE_HULL_SURFACE_TRIANGULATION : thm
  TRIANGULATION_SUBFACES : thm
  deriving Inhabited

set_option maxHeartbeats 8000000 in
@[nospecialize]
def setupPOT [HolBase] (D : PolytopeDeps) (BPOA : POA) (BPOC : POC) (BPOE : POE) (BPOG : POG) (BPOJ : POJ) (BPOS : POS) : ExceptT String IO POT := do
  -- @@SCOPE BEGIN
  let { add_linear_invariants, add_translation_invariants, ASM_MESON_TAC, GEOM_ORIGIN_TAC,
        GEOM_TRANSFORM_TAC, GEOM_TRANSLATE_TAC, MESON_TAC, new_definition, SET_RULE,
        SET_TAC, .. } := D.cvx
  let { CONJ_ASSOC, EXTENSION, FINITE_IMAGE, FINITE_RESTRICT, FINITE_SUBSET, FINITE_UNION,
        FINITE_UNIONS, FORALL_IN_GSPEC, .. } := D.cvx.core1
  let { FORALL_IN_IMAGE, IMP_CONJ, IMP_IMP, INTER_COMM, INTER_SUBSET, .. } := D.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, IN_INTER, IN_UNION, IN_UNIONS, LEFT_AND_EXISTS_THM,
        LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY, NOT_IMP, NOT_IN_EMPTY, .. } := D.cvx.core3
  let { RIGHT_FORALL_IMP_THM, RIGHT_IMP_FORALL_THM, SIMPLE_IMAGE, SUBSET, SUBSET_ANTISYM,
        SUBSET_INTER, SUBSET_TRANS, .. } := D.cvx.core5
  let { SWAP_EXISTS_THM, UNIONS_IMAGE, UNWIND_THM2, .. } := D.cvx.core6
  let { HULL_MINIMAL, HULL_MONO, .. } := D.cvx.misc
  let { CLOSURE_EQ_EMPTY, COMPACT_INTER, .. } := D.cvx.top2
  let { INTERIOR_EMPTY, .. } := D.cvx.top4
  let { CONVEX_CLOSURE, CONVEX_INTER, .. } := D.qcvx2
  let { CONVEX_RELATIVE_INTERIOR_CLOSURE, INTERIOR_SUBSET_RELATIVE_INTERIOR,
        relative_frontier, RELATIVE_FRONTIER_NONEMPTY_INTERIOR, RELATIVE_INTERIOR_SUBSET, ..
        } := D.qcvx3
  let { AFFINE_HULL_FACE_OF_DISJOINT_RELATIVE_INTERIOR, FACE_OF_DISJOINT_RELATIVE_INTERIOR,
        FACE_OF_IMP_SUBSET, FACE_OF_INTER, FACE_OF_INTER_SUBFACE, FACE_OF_SUBSET,
        FACE_OF_TRANS, .. } := BPOA
  let { CONVEX_RELATIVE_BOUNDARY_SUBSET_OF_PROPER_FACE, .. } := BPOC
  let { extreme_point_of, EXTREME_POINT_OF_CONVEX_HULL, .. } := BPOE
  let { facet_of, KREIN_MILMAN_MINKOWSKI, .. } := BPOG
  let { FINITE_POLYTOPE_FACES, .. } := BPOJ
  let { FACE_OF_SIMPLEX_SUBSET, FINITE_FACES_OF_SIMPLEX, SIMPLEX_FACE_OF_SIMPLEX,
        SIMPLEX_IMP_COMPACT, SIMPLEX_IMP_CONVEX, SIMPLEX_IMP_POLYTOPE, .. } := BPOS
  -- @@SCOPE END

  let simplicial_complex ← new_definition
   r"simplicial_complex c <=>
        FINITE c /\
        (!s. s IN c ==> ?n. n simplex s) /\
        (!f s. s IN c /\ f face_of s ==> f IN c) /\
        (!s s'. s IN c /\ s' IN c
                ==> (s INTER s') face_of s /\ (s INTER s') face_of s')"

  let triangulation ← new_definition
   r"triangulation(tr:(real^N->bool)->bool) <=>
        FINITE tr /\
        (!t. t IN tr ==> ?n. n simplex t) /\
        (!t t'. t IN tr /\ t' IN tr
                ==> (t INTER t') face_of t /\ (t INTER t') face_of t')"

  let SIMPLICIAL_COMPLEX_TRANSLATION ← prove
   r"!a:real^N tr.
   simplicial_complex(IMAGE (IMAGE (\x. a + x)) tr) <=> simplicial_complex tr"
   (REWRITE_TAC [simplicial_complex] THEN GEOM_TRANSLATE_TAC [])

  add_translation_invariants [SIMPLICIAL_COMPLEX_TRANSLATION]

  let SIMPLICIAL_COMPLEX_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N tr.
       linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
       ==> (simplicial_complex(IMAGE (IMAGE f) tr) <=> simplicial_complex tr)"
   (REWRITE_TAC [simplicial_complex] THEN GEOM_TRANSFORM_TAC [])

  add_linear_invariants [SIMPLICIAL_COMPLEX_LINEAR_IMAGE]

  let TRIANGULATION_TRANSLATION ← prove
   r"!a:real^N tr.
        triangulation(IMAGE (IMAGE (\x. a + x)) tr) <=> triangulation tr"
   (REWRITE_TAC [triangulation] THEN GEOM_TRANSLATE_TAC [])

  add_translation_invariants [TRIANGULATION_TRANSLATION]

  let TRIANGULATION_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N tr.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> (triangulation(IMAGE (IMAGE f) tr) <=> triangulation tr)"
   (REWRITE_TAC [triangulation] THEN GEOM_TRANSFORM_TAC [])

  add_linear_invariants [TRIANGULATION_LINEAR_IMAGE]

  let SIMPLICIAL_COMPLEX_IMP_TRIANGULATION ← prove
   r"!tr. simplicial_complex tr ==> triangulation tr"
   (REWRITE_TAC [triangulation, simplicial_complex] THEN MESON_TAC [])

  let TRIANGULATION_SUBSET ← prove
   r"!tr:(real^N->bool)->bool tr'.
        triangulation tr /\ tr' SUBSET tr ==> triangulation tr'"
   (REWRITE_TAC [triangulation] THEN
    MESON_TAC [SUBSET, FINITE_SUBSET])

  let TRIANGULATION_UNION ← prove
   r"!tr1 tr2.
        triangulation(tr1 UNION tr2) <=>
        triangulation tr1 /\ triangulation tr2 /\
        (!s t. s IN tr1 /\ t IN tr2
               ==> s INTER t face_of s /\ s INTER t face_of t)"
   (REWRITE_TAC [triangulation, FINITE_UNION, IN_UNION] THEN
    MESON_TAC [INTER_COMM])

  let TRIANGULATION_INTER_SIMPLEX ← prove
   r"!tr t t':real^N->bool.
        triangulation tr /\ t IN tr /\ t' IN tr
        ==> t INTER t' = convex hull ({x | x extreme_point_of t} INTER
                                      {x | x extreme_point_of t'})"
   (REWRITE_TAC [triangulation] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"t:real^N->bool", ← q r"t':real^N->bool"]) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (fun th => tactic_of do pure (MAP_EVERY
      (fun t => tactic_of do pure (MP_TAC (← SPEC t th)))
     [← q r"t:real^N->bool", ← q r"t':real^N->bool"])) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"m:int") THEN DISCH_TAC THEN X_GEN_TAC (← q r"n:int") THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"m:int", ← q r"t':real^N->bool",
                      ← q r"t INTER t':real^N->bool"] FACE_OF_SIMPLEX_SUBSET) THEN
    MP_TAC (← ISPECL [← q r"n:int", ← q r"t:real^N->bool",
                      ← q r"t INTER t':real^N->bool"] FACE_OF_SIMPLEX_SUBSET) THEN
    ASM_SIMP_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:real^N->bool") (STRIP_ASSUME_TAC o GSYM)) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d':real^N->bool") (STRIP_ASSUME_TAC o GSYM)) THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC HULL_MINIMAL THEN
      CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [CONVEX_INTER, SIMPLEX_IMP_CONVEX]] THEN
      SIMP_TAC [SUBSET, IN_INTER, IN_ELIM_THM, extreme_point_of]] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC (← q r"convex hull {x:real^N | x extreme_point_of (t INTER t')}") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC (← SET_RULE (← q r"s = t ==> s SUBSET t")) THEN
      MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
      ASM_MESON_TAC [COMPACT_INTER, CONVEX_INTER, SIMPLEX_IMP_COMPACT, SIMPLEX_IMP_CONVEX],
      MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC [SUBSET_INTER] THEN CONJ_TAC THENL
       [SUBST1_TAC (← SYM (← ASSUME (← q r"convex hull d:real^N->bool = t INTER t'"))),
        SUBST1_TAC (← SYM (← ASSUME (← q r"convex hull d':real^N->bool = t INTER t'")))] THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN GEN_TAC THEN
      DISCH_THEN (MP_TAC o MATCH_MP EXTREME_POINT_OF_CONVEX_HULL) THEN
      ASM SET_TAC []])

  let TRIANGULATION_SIMPLICIAL_COMPLEX ← (do
    let lemma ← prove
     r"{f | ?t. t IN tr /\ P f t} = UNIONS (IMAGE (\t. {f | P f t}) tr)"
     (GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC [IN_ELIM_THM, IN_UNIONS, IN_IMAGE, LEFT_AND_EXISTS_THM] THEN
      ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
      REWRITE_TAC [← GSYM CONJ_ASSOC, UNWIND_THM2, IN_ELIM_THM])
    prove
     r"!tr. triangulation tr
        ==> simplicial_complex {f:real^N->bool | ?t. t IN tr /\ f face_of t}"
     (REWRITE_TAC [triangulation, simplicial_complex] THEN
      REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC] THEN
      REWRITE_TAC [IN_ELIM_THM] THEN GEN_TAC THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      REWRITE_TAC [RIGHT_IMP_FORALL_THM, IMP_IMP] THEN STRIP_TAC THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC [lemma] THEN ASM_SIMP_TAC [FINITE_UNIONS, FINITE_IMAGE] THEN
        ASM_REWRITE_TAC [FORALL_IN_IMAGE] THEN
        ASM_MESON_TAC [FINITE_FACES_OF_SIMPLEX],
        ASM_MESON_TAC [SIMPLEX_FACE_OF_SIMPLEX],
        ASM_MESON_TAC [FACE_OF_TRANS],
        ASM_MESON_TAC [FACE_OF_INTER_SUBFACE]]))

  let TRIANGULATION_SIMPLEX_FACES ← prove
   r"!s:real^N->bool n d.
        n simplex s ==> triangulation {c | c face_of s /\ aff_dim c = d}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [triangulation, IN_ELIM_THM] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC [← SET_RULE
       (← q r"{x | P x /\ Q x} = {x | x IN {y | P y} /\ Q x}")] THEN
      MATCH_MP_TAC FINITE_RESTRICT THEN
      MATCH_MP_TAC FINITE_POLYTOPE_FACES THEN
      ASM_MESON_TAC [SIMPLEX_IMP_POLYTOPE],
      ASM_MESON_TAC [SIMPLEX_FACE_OF_SIMPLEX],
      REPEAT STRIP_TAC THEN MATCH_MP_TAC FACE_OF_SUBSET THEN
      EXISTS_TAC (← q r"s:real^N->bool") THEN ASM_SIMP_TAC [FACE_OF_INTER] THEN
      ASM_SIMP_TAC [FACE_OF_IMP_SUBSET, INTER_SUBSET]])

  let TRIANGULATION_SIMPLEX_FACETS ← prove
   r"!s:real^N->bool n. n simplex s ==> triangulation {c | c facet_of s}"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [facet_of] THEN
    MATCH_MP_TAC TRIANGULATION_SUBSET THEN EXISTS_TAC
     (← q r"{c:real^N->bool | c face_of s /\ aff_dim c = aff_dim s - &1}") THEN
    CONJ_TAC THENL [ALL_TAC, SET_TAC []] THEN
    MATCH_MP_TAC TRIANGULATION_SIMPLEX_FACES THEN ASM_MESON_TAC [])

  let CELL_COMPLEX_DISJOINT_RELATIVE_INTERIORS ← prove
   r"!c d:real^N->bool.
        c INTER d face_of c /\ c INTER d face_of d /\ ~(c = d)
        ==> relative_interior c INTER relative_interior d = {}"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"c INTER d:real^N->bool") FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    DISCH_THEN (fun th => tactic_of do pure (
      MP_TAC (← SPEC (← q r"d:real^N->bool") th) THEN
      MP_TAC (← SPEC (← q r"c:real^N->bool") th))) THEN
    ASM_REWRITE_TAC [] THEN
    MAP_EVERY (fun t => tactic_of do pure (MP_TAC (← ISPEC t RELATIVE_INTERIOR_SUBSET)))
     [← q r"c:real^N->bool", ← q r"d:real^N->bool"] THEN
    ASM SET_TAC [])

  let TRIANGULATION_DISJOINT_RELATIVE_INTERIORS ← prove
   r"!t c d:real^N->bool.
        triangulation t /\ c IN t /\ d IN t /\ ~(c = d)
        ==> relative_interior c INTER relative_interior d = {}"
   (REWRITE_TAC [triangulation] THEN
    MESON_TAC [CELL_COMPLEX_DISJOINT_RELATIVE_INTERIORS])

  let SIMPLICIAL_COMPLEX_DISJOINT_RELATIVE_INTERIORS ← prove
   r"!t c d:real^N->bool.
        simplicial_complex t /\ c IN t /\ d IN t /\ ~(c = d)
        ==> relative_interior c INTER relative_interior d = {}"
   (MESON_TAC [TRIANGULATION_DISJOINT_RELATIVE_INTERIORS,
               SIMPLICIAL_COMPLEX_IMP_TRIANGULATION])

  let NOT_IN_AFFINE_HULL_SURFACE_TRIANGULATION ← prove
   r"!t u z. convex u /\ bounded u /\ z IN interior u /\
           triangulation t /\ UNIONS t SUBSET frontier u
           ==> !c:real^N->bool. c IN t ==> ~(z IN affine hull c)"
   (REPEAT GEN_TAC THEN GEOM_ORIGIN_TAC (← q r"z:real^N") THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"closure u:real^N->bool", ← q r"c:real^N->bool"]
          CONVEX_RELATIVE_BOUNDARY_SUBSET_OF_PROPER_FACE) THEN
    ASM_SIMP_TAC [CONVEX_RELATIVE_INTERIOR_CLOSURE, CONVEX_CLOSURE] THEN
    REWRITE_TAC [← GSYM relative_frontier, CLOSURE_EQ_EMPTY, NOT_IMP] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [INTERIOR_EMPTY, NOT_IN_EMPTY],
      ASM_MESON_TAC [triangulation, SIMPLEX_IMP_CONVEX],
      MP_TAC (← ISPEC (← q r"u:real^N->bool") RELATIVE_FRONTIER_NONEMPTY_INTERIOR) THEN
      ASM SET_TAC [],
      DISCH_THEN (X_CHOOSE_THEN (← q r"k:real^N->bool") STRIP_ASSUME_TAC)] THEN
    MP_TAC (← ISPECL [← q r"closure u:real^N->bool", ← q r"k:real^N->bool"]
     AFFINE_HULL_FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_SIMP_TAC [CONVEX_RELATIVE_INTERIOR_CLOSURE, CONVEX_CLOSURE] THEN
    REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_INTER] THEN
    EXISTS_TAC (← q r"vec 0:real^N") THEN
    ASM_SIMP_TAC [← REWRITE_RULE [SUBSET] INTERIOR_SUBSET_RELATIVE_INTERIOR] THEN
    ASM_MESON_TAC [SUBSET, HULL_MONO])

  let TRIANGULATION_SUBFACES ← prove
   r"!tr:(real^N->bool)->bool tr'.
        triangulation tr /\ (!c'. c' IN tr' ==> ?c. c IN tr /\ c' face_of c)
        ==> triangulation tr'"
   (REPEAT GEN_TAC THEN REWRITE_TAC [triangulation] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC (← q r"UNIONS {{f:real^N->bool | f face_of c} | c IN tr}") THEN
      REWRITE_TAC [FINITE_UNIONS, SIMPLE_IMAGE, FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC [FINITE_IMAGE] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [FINITE_FACES_OF_SIMPLEX], ALL_TAC] THEN
      REWRITE_TAC [UNIONS_IMAGE] THEN ASM SET_TAC [],
      ASM_MESON_TAC [SIMPLEX_FACE_OF_SIMPLEX],
      ASM_MESON_TAC [FACE_OF_INTER_SUBFACE]])

  pure { simplicial_complex, triangulation, SIMPLICIAL_COMPLEX_TRANSLATION,
         SIMPLICIAL_COMPLEX_LINEAR_IMAGE, TRIANGULATION_TRANSLATION,
         TRIANGULATION_LINEAR_IMAGE, SIMPLICIAL_COMPLEX_IMP_TRIANGULATION,
         TRIANGULATION_SUBSET, TRIANGULATION_UNION, TRIANGULATION_INTER_SIMPLEX,
         TRIANGULATION_SIMPLICIAL_COMPLEX, TRIANGULATION_SIMPLEX_FACES,
         TRIANGULATION_SIMPLEX_FACETS, CELL_COMPLEX_DISJOINT_RELATIVE_INTERIORS,
         TRIANGULATION_DISJOINT_RELATIVE_INTERIORS,
         SIMPLICIAL_COMPLEX_DISJOINT_RELATIVE_INTERIORS,
         NOT_IN_AFFINE_HULL_SURFACE_TRIANGULATION, TRIANGULATION_SUBFACES }

/- ------------------------------------------------------------------------- -/
/- Subdividing a cell complex (not necessarily simplicial).                  -/
/- (polytope.ml 7975-8132)                                                   -/
/- ------------------------------------------------------------------------- -/

structure POU where
  CELL_COMPLEX_SUBDIVISION_EXISTS : thm
  deriving Inhabited

set_option maxHeartbeats 8000000 in
@[nospecialize]
def setupPOU [HolBase] (D : PolytopeDeps) (BPOA : POA) (BPOC : POC) (BPOJ : POJ) (BPOM : POM) : ExceptT String IO POU := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, SET_RULE,
        SET_TAC, .. } := D.cvx
  let { CARD_NUMSEG_1, DIMINDEX_GE_1, EXISTS_IN_GSPEC, FINITE_IMAGE, FINITE_INDUCT_STRONG,
        FINITE_NUMSEG, FINITE_UNION, FORALL_AND_THM, FORALL_IN_GSPEC, .. } := D.cvx.core1
  let { FORALL_IN_UNION, FORALL_PAIR_THM, IMP_CONJ, IMP_CONJ_ALT, INT_LE_TRANS, INTER,
        INTER_SUBSET, INTER_UNIONS, .. } := D.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, IN_INTER, IN_NUMSEG, IN_UNION, LE_1, LEFT_IMP_EXISTS_THM,
        MONO_EXISTS, NOT_IMP, NOT_IN_EMPTY, NOT_LT, NUMSEG_EMPTY, OR_EXISTS_THM, PAIR_EQ,
        REAL_ABS_INV, REAL_ABS_MUL, .. } := D.cvx.core3
  let { REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ, REAL_LE_TOTAL, REAL_LE_TRANS, REAL_LT_DIV,
        REAL_LT_IMP_LE, REAL_LT_LDIV_EQ, REAL_LT_RDIV_EQ, .. } := D.cvx.core4
  let { REAL_MUL_LID, REAL_NOT_LT, REAL_OF_NUM_LT, REAL_SUB_RDISTRIB, RIGHT_FORALL_IMP_THM,
        SIMPLE_IMAGE, SUBSET_REFL, SUBSET_TRANS, .. } := D.cvx.core5
  let { real_div, real_ge, UNIONS_UNION, .. } := D.cvx.core6
  let { REAL_HALF, .. } := D.cvx.misc
  let { COMPONENT_LE_NORM, DOT_BASIS, .. } := D.cvx.vec1
  let { NORM_LE_L1, .. } := D.cvx.vec3
  let { VECTOR_SUB_COMPONENT, .. } := D.cvx.vec4
  let { BOUNDED_POS_LT, .. } := D.cvx.top1
  let { EXISTS_IN_UNION, FINITE_PRODUCT_DEPENDENT, REAL_BOUNDS_LE, SUM_BOUND_GEN,
        UNION_OVER_INTER, .. } := D.qses
  let { FINITE_INTSEG, INTEGER_EXISTS_BETWEEN_ABS_LT, .. } := D.qfloor
  let { BOUNDED_UNIONS, DIAMETER_LE, .. } := D.qtop
  let { AFF_DIM_SUBSET, .. } := D.qcvx1
  let { CONVEX_HALFSPACE_GE, CONVEX_HALFSPACE_LE, .. } := D.qcvx2
  let { FACE_OF_INTER_INTER, FACE_OF_REFL, .. } := BPOA
  let { HYPERPLANE_FACE_OF_HALFSPACE_GE, HYPERPLANE_FACE_OF_HALFSPACE_LE, .. } := BPOC
  let { POLYHEDRON_HALFSPACE_GE, POLYHEDRON_HALFSPACE_LE, POLYTOPE_IMP_BOUNDED, .. } := BPOJ
  let { POLYTOPE_INTER_POLYHEDRON, .. } := BPOM
  -- @@SCOPE END

  let CELL_COMPLEX_SUBDIVISION_EXISTS ← (do
    let lemma1 ← prove
     r"a < abs(x - y)
     ==> &0 < a
         ==> ?n. integer n /\ (x < n * a /\ n * a < y \/
                               y <  n * a /\ n * a < x)"
     (REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC [← GSYM REAL_LT_LDIV_EQ, ← GSYM REAL_LT_RDIV_EQ] THEN
      MATCH_MP_TAC INTEGER_EXISTS_BETWEEN_ABS_LT THEN
      REWRITE_TAC [real_div, ← GSYM REAL_SUB_RDISTRIB, REAL_ABS_MUL] THEN
      ASM_SIMP_TAC [REAL_ABS_INV, ← REAL_ARITH (← q r"&0 < x ==> abs x = x")] THEN
      ASM_SIMP_TAC [← GSYM real_div, REAL_LT_RDIV_EQ,
                    REAL_MUL_LID, REAL_LT_IMP_LE])
    let lemma2 ← prove
     r"!m:(real^N->bool)->bool d.
        FINITE m /\
        (!c. c IN m ==> polytope c) /\
        (!c. c IN m ==> aff_dim c <= d) /\
        (!c1 c2. c1 IN m /\ c2 IN m
                 ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2)
        ==> !i. FINITE i
                ==> ?m'. UNIONS m' = UNIONS m /\
                         FINITE m' /\
                         (!c. c IN m' ==> ?d. d IN m /\ c SUBSET d) /\
                         (!c x. c IN m /\ x IN c
                                ==> ?d. d IN m' /\ x IN d /\ d SUBSET c) /\
                         (!c. c IN m' ==> polytope c) /\
                         (!c. c IN m' ==> aff_dim c <= d) /\
                         (!c1 c2. c1 IN m' /\ c2 IN m'
                                  ==> c1 INTER c2 face_of c1 /\
                                      c1 INTER c2 face_of c2) /\
                         (!c x y. c IN m' /\ x IN c /\ y IN c
                                  ==> !a b. (a,b) IN i
                                            ==> a dot x <= b /\ a dot y <= b \/
                                                a dot x >= b /\ a dot y >= b)"
     (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      REWRITE_TAC [NOT_IN_EMPTY, FORALL_PAIR_THM] THEN CONJ_TAC THENL
       [EXISTS_TAC (← q r"m:(real^N->bool)->bool") THEN ASM_REWRITE_TAC [] THEN
        MESON_TAC [SUBSET_REFL],
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"b:real", ← q r"i:(real^N#real)->bool"] THEN
      GEN_REWRITE_TAC I [IMP_CONJ] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"n:(real^N->bool)->bool") MP_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) MP_TAC) THEN
      POP_ASSUM_LIST (K ALL_TAC) THEN REPEAT STRIP_TAC THEN
      EXISTS_TAC (← q r"{c INTER {x:real^N | a dot x <= b} | c IN n} UNION
                  {c INTER {x:real^N | a dot x >= b} | c IN n}") THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC [UNIONS_UNION, ← GSYM INTER_UNIONS, ← GSYM UNION_OVER_INTER] THEN
        MATCH_MP_TAC (← SET_RULE (← q r"(!x. x IN s) ==> t INTER s = t")) THEN
        REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN REAL_ARITH_TAC,
        ASM_SIMP_TAC [FINITE_UNION, SIMPLE_IMAGE, FINITE_IMAGE],
        REWRITE_TAC [FORALL_IN_UNION, FORALL_IN_GSPEC] THEN
        ASM_MESON_TAC [SUBSET_TRANS, INTER_SUBSET],
        REWRITE_TAC [EXISTS_IN_UNION, EXISTS_IN_GSPEC] THEN
        MAP_EVERY X_GEN_TAC [← q r"c:real^N->bool", ← q r"x:real^N"] THEN STRIP_TAC THEN
        REWRITE_TAC [OR_EXISTS_THM] THEN
        UNDISCH_THEN
         (← q r"!c x:real^N. c IN m /\ x IN c ==> ?d. d IN n /\ x IN d /\ d SUBSET c")
         (MP_TAC o SPECL [← q r"c:real^N->bool", ← q r"x:real^N"]) THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
        SIMP_TAC [IN_INTER, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        MP_TAC (← ISPECL [← q r"(a:real^N) dot x", ← q r"b:real"] REAL_LE_TOTAL) THEN
        REWRITE_TAC [real_ge] THEN ASM SET_TAC [],
        REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC [POLYTOPE_INTER_POLYHEDRON, POLYHEDRON_HALFSPACE_LE,
                      POLYHEDRON_HALFSPACE_GE],
        REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        ASM_MESON_TAC [INT_LE_TRANS, AFF_DIM_SUBSET, INTER_SUBSET],
        REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC [] THEN
        ONCE_REWRITE_TAC [← SET_RULE
        (← q r"(s INTER t) INTER (s' INTER t') = (s INTER s') INTER (t INTER t')")] THEN
        MATCH_MP_TAC FACE_OF_INTER_INTER THEN ASM_SIMP_TAC [] THEN
        SIMP_TAC [← SET_RULE (← q r"s INTER s = s"), FACE_OF_REFL, CONVEX_HALFSPACE_LE,
                  CONVEX_HALFSPACE_GE] THEN
        REWRITE_TAC [INTER, IN_ELIM_THM, HYPERPLANE_FACE_OF_HALFSPACE_LE,
                     HYPERPLANE_FACE_OF_HALFSPACE_GE,
                     ← REAL_ARITH (← q r"a <= b /\ a >= b <=> a = b"),
                     ← REAL_ARITH (← q r"a >= b /\ a <= b <=> a = b")],
        REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, IN_UNION, FORALL_AND_THM,
                     IN_INSERT,
                     ← TAUT (← q r"p \/ q ==> r <=> (p ==> r) /\ (q ==> r)")] THEN
        REWRITE_TAC [FORALL_IN_GSPEC, IN_INTER, IN_ELIM_THM, PAIR_EQ] THEN
        SIMP_TAC [] THEN ASM_MESON_TAC []])
    prove
     r"!m:(real^N->bool)->bool d e.
     &0 < e /\
     FINITE m /\
     (!c. c IN m ==> polytope c) /\
     (!c. c IN m ==> aff_dim c <= d) /\
     (!c1 c2. c1 IN m /\ c2 IN m
              ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2)
     ==> ?m'. (!c. c IN m' ==> diameter c < e) /\
              UNIONS m' = UNIONS m /\
              FINITE m' /\
              (!c. c IN m' ==> ?d. d IN m /\ c SUBSET d) /\
              (!c x. c IN m /\ x IN c
                     ==> ?d. d IN m' /\ x IN d /\ d SUBSET c) /\
              (!c. c IN m' ==> polytope c) /\
              (!c. c IN m' ==> aff_dim c <= d) /\
              (!c1 c2. c1 IN m' /\ c2 IN m'
                       ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2)"
     (REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"bounded(UNIONS m:real^N->bool)") MP_TAC THENL
       [ASM_SIMP_TAC [BOUNDED_UNIONS, POLYTOPE_IMP_BOUNDED], ALL_TAC] THEN
      REWRITE_TAC [BOUNDED_POS_LT, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"B:real") THEN REWRITE_TAC [] THEN STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"--B / (e / &2 / &(dimindex(:N)))",
                        ← q r"B / (e / &2 / &(dimindex(:N)))"] FINITE_INTSEG) THEN
      ASM_SIMP_TAC [REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ, REAL_HALF,
                    REAL_LT_DIV, REAL_OF_NUM_LT, DIMINDEX_GE_1, LE_1] THEN
      REWRITE_TAC [REAL_BOUNDS_LE] THEN ABBREV_TAC
       (← q r"k = {i | integer i /\ abs(i * e / &2 / &(dimindex(:N))) <= B}") THEN
      DISCH_TAC THEN
      MP_TAC (← ISPECL [← q r"m:(real^N->bool)->bool", ← q r"d:int"] lemma2) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o SPEC
       (← q r"{ (basis i:real^N,j * e / &2 / &(dimindex(:N))) |
          i IN 1..dimindex(:N) /\ j IN k}")) THEN
      ASM_SIMP_TAC [FINITE_PRODUCT_DEPENDENT, FINITE_NUMSEG] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"n:(real^N->bool)->bool") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC (← q r"c:real^N->bool") THEN DISCH_TAC THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"&0 < e /\ x <= e / &2 ==> x < e")) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC DIAMETER_LE THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [← q r"x:real^N", ← q r"y:real^N"] THEN STRIP_TAC THEN
      W (MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      MATCH_MP_TAC SUM_BOUND_GEN THEN
      REWRITE_TAC [FINITE_NUMSEG, CARD_NUMSEG_1, NUMSEG_EMPTY] THEN
      REWRITE_TAC [NOT_LT, DIMINDEX_GE_1, IN_NUMSEG, VECTOR_SUB_COMPONENT] THEN
      X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN REWRITE_TAC [← GSYM REAL_NOT_LT] THEN
      DISCH_THEN (MP_TAC o MATCH_MP lemma1) THEN
      ASM_SIMP_TAC [REAL_HALF, REAL_LT_DIV,
                    REAL_OF_NUM_LT, DIMINDEX_GE_1, LE_1] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"j:real") (CONJUNCTS_THEN ASSUME_TAC)) THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"c:real^N->bool", ← q r"x:real^N", ← q r"y:real^N"]) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o
        SPECL [← q r"basis i:real^N", ← q r"j * e / &2 / &(dimindex(:N))"]) THEN
      ASM_SIMP_TAC [DOT_BASIS, IN_ELIM_THM, NOT_IMP] THEN
      CONJ_TAC THENL [ALL_TAC, ASM_REAL_ARITH_TAC] THEN
      MAP_EVERY EXISTS_TAC [← q r"i:num", ← q r"j:real"] THEN ASM_REWRITE_TAC [IN_NUMSEG] THEN
      EXPAND_TAC "k" THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN
      FIRST_X_ASSUM DISJ_CASES_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
       (← REAL_ARITH (← q r"a < x /\ x < b
                    ==> abs a <= c /\ abs b <= c ==> abs x <= c"))) THEN
      CONJ_TAC THEN
      W (MP_TAC o PART_MATCH lhand COMPONENT_LE_NORM o lhand o snd) THEN
      ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM SET_TAC []))

  pure { CELL_COMPLEX_SUBDIVISION_EXISTS }

/- ------------------------------------------------------------------------- -/
/- Refining a cell complex to a simplicial complex.                          -/
/- (polytope.ml 8132-8781)                                                   -/
/- ------------------------------------------------------------------------- -/

structure POV where
  SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX_LOWDIM : thm
  SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX : thm
  FINE_SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX : thm
  deriving Inhabited

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 4096 in
@[nospecialize]
def setupPOV [HolBase] (D : PolytopeDeps) (BPOA : POA) (BPOH : POH) (BPOJ : POJ) (BPOL : POL) (BPOM : POM) (BPOS : POS) (BPOT : POT) (BPOU : POU) : ExceptT String IO POV := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, INT_ARITH, INT_ARITH_TAC, MESON, MESON_TAC, SELECT_CONV,
        SET_RULE, SET_TAC, .. } := D.cvx
  let { CONJ_ASSOC, CONJ_SYM, CONTRAPOS_THM, EXISTS_IN_GSPEC, FINITE_IMAGE, FINITE_INTER,
        FINITE_RESTRICT, FINITE_SING, FINITE_SUBSET, FINITE_UNION, FINITE_UNIONS,
        FORALL_IN_GSPEC, .. } := D.cvx.core1
  let { FORALL_IN_UNION, FORALL_IN_UNIONS, IMP_CONJ, IMP_IMP, IN_DIFF, INSERT_AC,
        INSERT_SUBSET, INT_LE_TRANS, INT_LET_TRANS, INT_OF_NUM_EQ, INT_OF_NUM_EXISTS,
        INT_OF_NUM_LE, INT_OF_NUM_SUB, INTER_COMM, INTER_EMPTY, INTER_SUBSET, .. } :=
        D.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, IN_INTER, IN_SING, IN_UNION, IN_UNIONS, LEFT_IMP_EXISTS_THM,
        LT_IMP_LE, MEMBER_NOT_EMPTY, MONO_AND, MONO_EXISTS, NOT_IMP, NOT_IN_EMPTY, NOT_LE,
        .. } := D.cvx.core3
  let { REAL_LET_TRANS, .. } := D.cvx.core4
  let { RIGHT_FORALL_IMP_THM, RIGHT_IMP_FORALL_THM, SIMPLE_IMAGE, SING_SUBSET, SUBSET,
        SUBSET_ANTISYM, SUBSET_ANTISYM_EQ, SUBSET_INTER, SUBSET_REFL, SUBSET_RESTRICT,
        SUBSET_TRANS, .. } := D.cvx.core5
  let { SWAP_EXISTS_THM, UNIONS_GSPEC, .. } := D.cvx.core6
  let { HULL_INC, HULL_MINIMAL, HULL_MONO, HULL_P, .. } := D.cvx.misc
  let { BETWEEN_IMP_COLLINEAR, BETWEEN_SYM, BETWEEN_TRANS_2, COLLINEAR_3_TRANS,
        COLLINEAR_BETWEEN_CASES, .. } := D.cvx.vec1
  let { BETWEEN_IN_SEGMENT, CLOSURE_CLOSED, .. } := D.cvx.top1
  let { COMPACT_INSERT, .. } := D.cvx.top2
  let { DIAMETER_SUBSET, ENDS_IN_SEGMENT, FINITE_IMP_COMPACT, .. } := D.cvx.top3
  let { segment, SEGMENT_SYM, .. } := D.cvx.top5
  let { EXISTS_IN_UNIONS, FINITE_PRODUCT_DEPENDENT, INT_LT_IMP_LE, INT_LT_IMP_NE,
        INT_LT_REFL, num_WF, UNIONS_1, .. } := D.qses
  let { BETWEEN_ANTISYM, BETWEEN_TRANS, .. } := D.qvec
  let { HULL_UNION_RIGHT, .. } := D.qmisc
  let { AFF_DIM_CONVEX_HULL, AFF_DIM_EMPTY, AFF_DIM_INSERT, AFF_DIM_LE_UNIV, AFF_DIM_POS_LE,
        AFF_DIM_SING, AFF_DIM_SUBSET, AFFINE_HULL_CONVEX_HULL,
        AFFINE_INDEPENDENT_IMP_FINITE, AFFINE_INDEPENDENT_INSERT, .. } := D.qcvx1
  let { CONVEX_HULL_EQ_EMPTY, CONVEX_HULL_INSERT_SEGMENTS, .. } := D.qcvx2
  let { IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT,
        INTER_CONVEX_HULL_INSERT_RELATIVE_EXTERIOR, relative_frontier,
        RELATIVE_INTERIOR_EQ_EMPTY, RELATIVE_INTERIOR_SUBSET, SEGMENT_CONVEX_HULL,
        SEGMENT_TO_RELATIVE_FRONTIER, .. } := D.qcvx3
  let { AFFINE_HULL_FACE_OF_DISJOINT_RELATIVE_INTERIOR, FACE_OF_AFF_DIM_LT,
        FACE_OF_DISJOINT_RELATIVE_INTERIOR, FACE_OF_EMPTY, FACE_OF_IMP_SUBSET,
        FACE_OF_INTER_SUBFACE, FACE_OF_REFL, FACE_OF_SUBSET_RELATIVE_FRONTIER,
        FACE_OF_TRANS, .. } := BPOA
  let { FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT, FACE_OF_CONVEX_HULL_SUBSET, .. } := BPOH
  let { FACE_OF_POLYTOPE_INSERT_EQ, FACE_OF_POLYTOPE_POLYTOPE, FINITE_POLYTOPE_FACES,
        POLYTOPE_IMP_BOUNDED, POLYTOPE_IMP_CLOSED, POLYTOPE_IMP_CONVEX, .. } := BPOJ
  let { RELATIVE_FRONTIER_OF_POLYHEDRON_ALT, .. } := BPOL
  let { POLYTOPE_IMP_POLYHEDRON, .. } := BPOM
  let { AFF_DIM_SIMPLEX, POLYTOPE_LOWDIM_IMP_SIMPLEX, simplex, SIMPLEX_EMPTY,
        SIMPLEX_IMP_POLYTOPE, SIMPLEX_INSERT, .. } := BPOS
  let { simplicial_complex, .. } := BPOT
  let { CELL_COMPLEX_SUBDIVISION_EXISTS, .. } := BPOU
  -- @@SCOPE END

  let SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX_LOWDIM ← (do
    let lemma1 ← prove
     r"!s t u z:real^N.
          convex s /\ convex t /\ convex u /\ z IN relative_interior s /\
          t SUBSET relative_frontier s /\ u SUBSET relative_frontier s
          ==> convex hull (z INSERT t) INTER convex hull (z INSERT u) =
              convex hull (z INSERT (t INTER u))"
     (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN
      REWRITE_TAC [SUBSET_INTER] THEN
      SIMP_TAC [HULL_MONO, INTER_SUBSET, ← SET_RULE
       (← q r"s SUBSET t ==> z INSERT s SUBSET z INSERT t")] THEN
      REWRITE_TAC [CONVEX_HULL_INSERT_SEGMENTS] THEN
      ASM_CASES_TAC (← q r"t:real^N->bool = {}") THEN
      ASM_REWRITE_TAC [INTER_EMPTY, INTER_SUBSET] THEN
      ASM_CASES_TAC (← q r"u:real^N->bool = {}") THEN
      ASM_REWRITE_TAC [INTER_EMPTY, INTER_SUBSET] THEN
      REWRITE_TAC [SUBSET, IN_INTER, UNIONS_GSPEC, IN_ELIM_THM] THEN
      ASM_SIMP_TAC [HULL_P] THEN
      X_GEN_TAC (← q r"x:real^N") THEN DISCH_THEN (CONJUNCTS_THEN2
       (X_CHOOSE_THEN (← q r"v:real^N") STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN (← q r"w:real^N") STRIP_ASSUME_TAC)) THEN
      ASM_CASES_TAC (← q r"v:real^N = w") THENL
       [COND_CASES_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
        REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC (← q r"w:real^N") THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC HULL_INC THEN ASM SET_TAC [],
        ASM_CASES_TAC (← q r"x:real^N = z") THENL
         [COND_CASES_TAC THEN ASM_REWRITE_TAC [IN_SING, IN_ELIM_THM] THEN
          REWRITE_TAC [ENDS_IN_SEGMENT] THEN
          ASM_MESON_TAC [MEMBER_NOT_EMPTY, CONVEX_HULL_EQ_EMPTY],
          MATCH_MP_TAC (← TAUT (← q r"F ==> p"))]] THEN
      SUBGOAL_THEN (← q r"~(v:real^N = z) /\ ~(w:real^N = z)")
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC [relative_frontier, SUBSET, IN_DIFF], ALL_TAC] THEN
      MP_TAC (← ISPECL
       [← q r"v:real^N", ← q r"z:real^N", ← q r"x:real^N", ← q r"w:real^N"]
            COLLINEAR_3_TRANS) THEN
      ASM_REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL
       [REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP BETWEEN_IMP_COLLINEAR o
           GEN_REWRITE_RULE I [← GSYM BETWEEN_IN_SEGMENT])) THEN
        SIMP_TAC [INSERT_AC],
        ONCE_REWRITE_TAC [← SET_RULE (← q r"{a,b,c} = {b,a,c}")] THEN
        REWRITE_TAC [COLLINEAR_BETWEEN_CASES]] THEN
      DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
       [RULE_ASSUM_TAC (REWRITE_RULE [← GSYM BETWEEN_IN_SEGMENT]) THEN
        ASM_MESON_TAC [BETWEEN_SYM, BETWEEN_TRANS, BETWEEN_TRANS_2,
                       BETWEEN_ANTISYM],
        REWRITE_TAC [BETWEEN_IN_SEGMENT]] THEN
      STRIP_TAC THENL
       [MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"z:real^N", ← q r"w:real^N"]
            IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
        ASM_REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL
         [ASM_MESON_TAC [relative_frontier, SUBSET, IN_DIFF],
          REWRITE_TAC [SUBSET] THEN DISCH_THEN (MP_TAC o SPEC (← q r"v:real^N"))] THEN
        REWRITE_TAC [NOT_IMP] THEN ONCE_REWRITE_TAC [SEGMENT_SYM] THEN
        ONCE_REWRITE_TAC [segment] THEN
        ASM_REWRITE_TAC [IN_DIFF, IN_INSERT, NOT_IN_EMPTY] THEN
        ASM_MESON_TAC [relative_frontier, SUBSET, IN_DIFF],
        MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"z:real^N", ← q r"v:real^N"]
            IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
        ASM_REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL
         [ASM_MESON_TAC [relative_frontier, SUBSET, IN_DIFF],
          REWRITE_TAC [SUBSET] THEN DISCH_THEN (MP_TAC o SPEC (← q r"w:real^N"))] THEN
        REWRITE_TAC [NOT_IMP] THEN ONCE_REWRITE_TAC [segment] THEN
        ASM_REWRITE_TAC [IN_DIFF, IN_INSERT, NOT_IN_EMPTY] THEN
        ASM_MESON_TAC [relative_frontier, SUBSET, IN_DIFF]])
    let lemma2 ← prove
     r"!n m:(real^N->bool)->bool.
          FINITE m /\
          (!c. c IN m ==> polytope c) /\
          (!c. c IN m ==> aff_dim c <= &n) /\
          (!c f. c IN m /\ f face_of c ==> f IN m) /\
          (!c1 c2. c1 IN m /\ c2 IN m
                   ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2)
          ==> ?t. simplicial_complex t /\
                  (!k. k IN t ==> aff_dim k <= &n) /\
                  UNIONS t = UNIONS m /\
                  (!c. c IN m
                       ==> ?f. FINITE f /\ f SUBSET t /\ c = UNIONS f) /\
                  (!k. k IN t ==> ?c. c IN m /\ k SUBSET c)"
     (MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN
      X_GEN_TAC (← q r"m:(real^N->bool)->bool") THEN STRIP_TAC THEN
      ASM_CASES_TAC (← q r"n <= 1") THENL
       [EXISTS_TAC (← q r"m:(real^N->bool)->bool") THEN
        ASM_REWRITE_TAC [simplicial_complex] THEN CONJ_TAC THENL
         [REPEAT STRIP_TAC THEN MATCH_MP_TAC POLYTOPE_LOWDIM_IMP_SIMPLEX THEN
          ASM_MESON_TAC [INT_OF_NUM_LE, INT_LE_TRANS],
          MESON_TAC [SING_SUBSET, UNIONS_1, FINITE_SING, SUBSET_REFL]],
        RULE_ASSUM_TAC (REWRITE_RULE [NOT_LE]) THEN
        FIRST_ASSUM (ASSUME_TAC o MATCH_MP (← ARITH_RULE
         (← q r"1 < n ==> ~(n = 0)")))] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"n - 1")) THEN
      ASM_REWRITE_TAC [← ARITH_RULE (← q r"n - 1 < n <=> ~(n = 0)")] THEN
      ABBREV_TAC (← q r"sk = {c:real^N->bool | c IN m /\ aff_dim c < &n}") THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"sk:(real^N->bool)->bool")) THEN
      ASM_SIMP_TAC [← GSYM INT_OF_NUM_SUB, LT_IMP_LE] THEN
      REWRITE_TAC [← INT_ARITH (← q r"x:int <= y - &1 <=> x < y")] THEN ANTS_TAC THENL
       [EXPAND_TAC "sk" THEN
        CONJ_TAC THENL [ASM_SIMP_TAC [FINITE_RESTRICT], ALL_TAC] THEN
        REWRITE_TAC [IN_ELIM_THM] THEN
        REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC]) THEN
        CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
        ASM_MESON_TAC [FACE_OF_IMP_SUBSET, AFF_DIM_SUBSET, INT_LET_TRANS],
        DISCH_THEN (X_CHOOSE_THEN (← q r"sc:(real^N->bool)->bool")
          STRIP_ASSUME_TAC)] THEN
      SUBGOAL_THEN
       (← q r"?t. simplicial_complex t /\
           (!k. k IN t ==> aff_dim k <= &n) /\
           (!c. c IN m ==> (?f. f SUBSET t /\ c = UNIONS f)) /\
           (!k. k IN t ==> (?c:real^N->bool. c IN m /\ k SUBSET c))")
      MP_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:(real^N->bool)->bool") THEN
        ASM_CASES_TAC (← q r"FINITE(t:(real^N->bool)->bool)") THENL
         [ALL_TAC, ASM_MESON_TAC [simplicial_complex]] THEN
        REPLICATE_TAC 2 (MATCH_MP_TAC MONO_AND THEN REWRITE_TAC []) THEN
        MATCH_MP_TAC (← TAUT
         (← q r"(q /\ r ==> p) /\ (q ==> q')
          ==> q /\ r ==> p /\ q' /\ r")) THEN
        CONJ_TAC THENL [SET_TAC [], ASM_MESON_TAC [FINITE_SUBSET]]] THEN
      FIRST_ASSUM (STRIP_ASSUME_TAC o
        GEN_REWRITE_RULE I [simplicial_complex]) THEN
      REWRITE_TAC [simplicial_complex, ← GSYM CONJ_ASSOC] THEN
      ABBREV_TAC (← q r"fat = {c:real^N->bool | c IN m /\ aff_dim c = &n}") THEN
      SUBGOAL_THEN
       (← q r"(!c:real^N->bool. c IN fat ==> polytope c) /\
        (!c. c IN fat ==> convex c) /\
        (!c. c IN fat ==> closed c) /\
        (!c. c IN fat ==> (@z. z IN relative_interior c) IN relative_interior c)")
      STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC (← TAUT
          (← q r"(p ==> q /\ r) /\ p /\ (q ==> s) ==> p /\ q /\ r /\ s")) THEN
        REPEAT CONJ_TAC THENL
         [MESON_TAC [POLYTOPE_IMP_CONVEX, POLYTOPE_IMP_CLOSED],
          ASM SET_TAC [],
          REPEAT STRIP_TAC THEN CONV_TAC SELECT_CONV THEN
          ASM_SIMP_TAC [MEMBER_NOT_EMPTY, RELATIVE_INTERIOR_EQ_EMPTY] THEN
          UNDISCH_TAC (← q r"(c:real^N->bool) IN fat") THEN EXPAND_TAC "fat" THEN
          ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN SIMP_TAC [IN_ELIM_THM] THEN
          REWRITE_TAC [AFF_DIM_EMPTY] THEN INT_ARITH_TAC],
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"!k. k IN sc ==> ?t. ~affine_dependent t /\
                            CARD t <= n /\ aff_dim k < &n /\
                            k:real^N->bool = convex hull t")
       (LABEL_TAC "*")
      THENL
       [REPEAT STRIP_TAC THEN
        SUBGOAL_THEN (← q r"?r. r simplex (k:real^N->bool)") CHOOSE_TAC THENL
         [ASM SET_TAC [], ALL_TAC] THEN
        ASM_CASES_TAC (← q r"r = aff_dim(k:real^N->bool)") THENL
         [ALL_TAC, ASM_MESON_TAC [AFF_DIM_SIMPLEX]] THEN
        FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [simplex]) THEN
        MATCH_MP_TAC MONO_EXISTS THEN ASM_REWRITE_TAC [] THEN
        X_GEN_TAC (← q r"t:real^N->bool") THEN SIMP_TAC [] THEN
        REPEAT STRIP_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
        ASM_REWRITE_TAC [← GSYM INT_OF_NUM_LE] THEN
        MATCH_MP_TAC (← INT_ARITH (← q r"x:int < n ==> x + &1 <= n")) THEN
        ASM_MESON_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN
        (← q r"!c k. c IN fat /\ k IN sc /\ k SUBSET relative_frontier c
               ==> affine hull k INTER relative_interior c:real^N->bool = {}")
        (LABEL_TAC "-")
      THENL
       [REPEAT STRIP_TAC THEN
        SUBGOAL_THEN
         (← q r"?f:real^N->bool. f face_of c /\ ~(f = c) /\ k SUBSET f")
        STRIP_ASSUME_TAC THENL
         [SUBGOAL_THEN
           (← q r"?l:real^N->bool. l IN sk /\ k SUBSET l")
          STRIP_ASSUME_TAC THENL [ASM MESON_TAC [], ALL_TAC] THEN
          EXISTS_TAC (← q r"l INTER c:real^N->bool") THEN
          CONJ_TAC THENL [ASM SET_TAC [], ASM_REWRITE_TAC [SUBSET_INTER]] THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC (← MESON [INT_LT_REFL]
             (← q r"aff_dim s < aff_dim t ==> ~(s = t)")) THEN
            TRANS_TAC INT_LET_TRANS (← q r"aff_dim(l:real^N->bool)") THEN
            SIMP_TAC [AFF_DIM_SUBSET, INTER_SUBSET] THEN ASM SET_TAC [],
            TRANS_TAC SUBSET_TRANS (← q r"relative_frontier c:real^N->bool") THEN
            ASM_SIMP_TAC [relative_frontier, CLOSURE_CLOSED] THEN ASM SET_TAC []],
          MP_TAC (← ISPECL [← q r"c:real^N->bool", ← q r"f:real^N->bool"]
            AFFINE_HULL_FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
          ASM_SIMP_TAC [] THEN MATCH_MP_TAC (← SET_RULE
           (← q r"s SUBSET t ==> t INTER u = {} ==> s INTER u = {}")) THEN
          ASM_SIMP_TAC [HULL_MONO]],
        ALL_TAC] THEN
      EXISTS_TAC
       (← q r"sc UNION { convex hull ((@z:real^N. z IN relative_interior c) INSERT k) |
                   c IN fat /\ k IN sc /\ k SUBSET relative_frontier c}") THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC [FINITE_UNION] THEN
        REWRITE_TAC [← SET_RULE
         (← q r"A /\ x IN s /\ P x <=> A /\ x IN (s INTER {x | P x})")] THEN
        MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
        ASM_SIMP_TAC [FINITE_INTER] THEN EXPAND_TAC "fat" THEN
        ASM_SIMP_TAC [FINITE_RESTRICT],
        ASM_REWRITE_TAC [FORALL_IN_UNION, FORALL_IN_GSPEC] THEN
        MAP_EVERY X_GEN_TAC [← q r"c:real^N->bool", ← q r"k:real^N->bool"] THEN
        STRIP_TAC THEN MATCH_MP_TAC SIMPLEX_INSERT THEN
        ASM_SIMP_TAC [] THEN REMOVE_THEN "-"
         (MP_TAC o SPECL [← q r"c:real^N->bool", ← q r"k:real^N->bool"]) THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← SET_RULE
           (← q r"z IN r ==> a INTER r = {} ==> ~(z IN a)")) THEN
        ASM_SIMP_TAC [],
        REWRITE_TAC [FORALL_IN_UNION, IMP_CONJ] THEN
        X_GEN_TAC (← q r"f:real^N->bool") THEN
        CONJ_TAC THENL [ASM_MESON_TAC [IN_UNION], ALL_TAC] THEN
        REWRITE_TAC [FORALL_IN_GSPEC] THEN
        MAP_EVERY X_GEN_TAC [← q r"c:real^N->bool", ← q r"k:real^N->bool"] THEN
        STRIP_TAC THEN
        ABBREV_TAC (← q r"z:real^N = @z. z IN relative_interior c") THEN
        SUBGOAL_THEN (← q r"(z:real^N) IN relative_interior c") ASSUME_TAC THENL
         [ASM_MESON_TAC [], ALL_TAC] THEN
        REMOVE_THEN "*" (MP_TAC o SPEC (← q r"k:real^N->bool")) THEN
        ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC (← q r"i:real^N->bool") THEN SIMP_TAC [] THEN
        DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN
        ONCE_REWRITE_TAC [← SET_RULE (← q r"z INSERT i = {z} UNION i")] THEN
        REWRITE_TAC [← GSYM HULL_UNION_RIGHT] THEN
        REWRITE_TAC [← SET_RULE (← q r"{z} UNION i = z INSERT i")] THEN
        SUBGOAL_THEN (← q r"~((z:real^N) IN affine hull i)") ASSUME_TAC THENL
         [REMOVE_THEN "-"
           (MP_TAC o SPECL [← q r"c:real^N->bool", ← q r"k:real^N->bool"]) THEN
          ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← SET_RULE
           (← q r"a SUBSET a' /\ z IN r ==> a' INTER r = {} ==> ~(z IN a)")) THEN
          EXPAND_TAC "k" THEN
          ASM_REWRITE_TAC [SUBSET_REFL, AFFINE_HULL_CONVEX_HULL],
          ALL_TAC] THEN
        FIRST_ASSUM (ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
        DISCH_TAC THEN
        MP_TAC (← ISPECL [← q r"(z:real^N) INSERT i", ← q r"f:real^N->bool"]
            FACE_OF_CONVEX_HULL_SUBSET) THEN
        ASM_SIMP_TAC [COMPACT_INSERT, FINITE_IMP_COMPACT] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"j:real^N->bool") (STRIP_ASSUME_TAC o GSYM)) THEN
        REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN
        ASM_CASES_TAC (← q r"(z:real^N) IN j") THENL
         [DISJ2_TAC THEN MAP_EVERY EXISTS_TAC
           [← q r"c:real^N->bool", ← q r"convex hull (j DELETE (z:real^N))"] THEN
          ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
           [FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC (← q r"k:real^N->bool") THEN
            ASM_REWRITE_TAC [] THEN EXPAND_TAC "k" THEN
            ASM_SIMP_TAC [FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
            EXISTS_TAC (← q r"j DELETE (z:real^N)") THEN ASM SET_TAC [],
            TRANS_TAC SUBSET_TRANS (← q r"k:real^N->bool") THEN ASM_REWRITE_TAC [] THEN
            EXPAND_TAC "k" THEN MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC [],
            ONCE_REWRITE_TAC [← SET_RULE (← q r"z INSERT i = {z} UNION i")] THEN
            REWRITE_TAC [← GSYM HULL_UNION_RIGHT] THEN
            REWRITE_TAC [← SET_RULE (← q r"{z} UNION i = z INSERT i")] THEN
            EXPAND_TAC "f" THEN AP_TERM_TAC THEN ASM SET_TAC []],
          DISJ1_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
          EXISTS_TAC (← q r"k:real^N->bool") THEN ASM_REWRITE_TAC [] THEN
          EXPAND_TAC "k" THEN
          ASM_SIMP_TAC [FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
          EXISTS_TAC (← q r"j:real^N->bool") THEN ASM SET_TAC []],
          REWRITE_TAC [IN_UNION] THEN MATCH_MP_TAC (← MESON []
           (← q r"(!x y. R x y ==> R y x) /\
            (!x y. P x /\ P y ==> R x y) /\
            (!x y. P x /\ Q y ==> R x y) /\
            (!x y. Q x /\ Q y ==> R x y)
            ==> !x y. (P x \/ Q x) /\ (P y \/ Q y) ==> R x y")) THEN
          CONJ_TAC THENL [MESON_TAC [INTER_COMM], ASM_REWRITE_TAC []] THEN
          REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC] THEN
          REWRITE_TAC [IMP_IMP, RIGHT_IMP_FORALL_THM] THEN CONJ_TAC THENL
           [MAP_EVERY X_GEN_TAC
             [← q r"l:real^N->bool", ← q r"c:real^N->bool", ← q r"k:real^N->bool"] THEN
            STRIP_TAC THEN
            ABBREV_TAC (← q r"z:real^N = @z. z IN relative_interior c") THEN
            SUBGOAL_THEN (← q r"(z:real^N) IN relative_interior c") ASSUME_TAC THENL
             [ASM_MESON_TAC [], ALL_TAC] THEN
            SUBGOAL_THEN
             (← q r"l INTER convex hull (z INSERT k):real^N->bool =
              l INTER convex hull k")
            SUBST1_TAC THENL
             [MATCH_MP_TAC INTER_CONVEX_HULL_INSERT_RELATIVE_EXTERIOR THEN
              EXISTS_TAC (← q r"c:real^N->bool") THEN ASM_SIMP_TAC [] THEN
              CONJ_TAC THENL
               [TRANS_TAC SUBSET_TRANS (← q r"relative_frontier c:real^N->bool") THEN
                ASM_SIMP_TAC [relative_frontier, CLOSURE_CLOSED] THEN
                ASM SET_TAC [],
                ALL_TAC] THEN
              SUBGOAL_THEN (← q r"?d:real^N->bool. d IN sk /\ l SUBSET d") MP_TAC THENL
               [ASM_MESON_TAC [], REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN
              X_GEN_TAC (← q r"d:real^N->bool") THEN
              DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
              MATCH_MP_TAC (← SET_RULE
               (← q r"d INTER s = {} ==> l SUBSET d ==> DISJOINT l s")) THEN
              MATCH_MP_TAC (← SET_RULE
               (← q r"relative_interior c SUBSET c /\
                (c INTER d) INTER relative_interior c = {}
                ==> d INTER relative_interior c = {}")) THEN
              REWRITE_TAC [RELATIVE_INTERIOR_SUBSET] THEN
              MATCH_MP_TAC FACE_OF_DISJOINT_RELATIVE_INTERIOR THEN
              CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
              MATCH_MP_TAC (← MESON [INT_LT_REFL]
              (← q r"aff_dim s < aff_dim t ==> ~(s = t)")) THEN
             TRANS_TAC INT_LET_TRANS (← q r"aff_dim(d:real^N->bool)") THEN
             SIMP_TAC [AFF_DIM_SUBSET, INTER_SUBSET] THEN ASM SET_TAC [],
             ALL_TAC] THEN
           SUBGOAL_THEN (← q r"convex hull k:real^N->bool = k") SUBST1_TAC THENL
            [MATCH_MP_TAC HULL_P THEN MATCH_MP_TAC POLYTOPE_IMP_CONVEX THEN
             MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN ASM SET_TAC [],
             ALL_TAC] THEN
           CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
           TRANS_TAC FACE_OF_TRANS (← q r"k:real^N->bool") THEN
           CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
           REMOVE_THEN "*" (MP_TAC o SPEC (← q r"k:real^N->bool")) THEN
           ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
           X_GEN_TAC (← q r"i:real^N->bool") THEN
           DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN
           SUBGOAL_THEN (← q r"~((z:real^N) IN affine hull i)") ASSUME_TAC THENL
            [REMOVE_THEN "-"
              (MP_TAC o SPECL [← q r"c:real^N->bool", ← q r"k:real^N->bool"]) THEN
             ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← SET_RULE
              (← q r"a SUBSET a' /\ z IN r ==> a' INTER r = {} ==> ~(z IN a)")) THEN
             EXPAND_TAC "k" THEN
             ASM_REWRITE_TAC [SUBSET_REFL, AFFINE_HULL_CONVEX_HULL],
             ALL_TAC] THEN
            EXPAND_TAC "k" THEN
            ONCE_REWRITE_TAC [← SET_RULE (← q r"z INSERT i = {z} UNION i")] THEN
            REWRITE_TAC [← GSYM HULL_UNION_RIGHT] THEN
            REWRITE_TAC [← SET_RULE (← q r"{z} UNION i = z INSERT i")]  THEN
            ASM_SIMP_TAC [FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT,
                          AFFINE_INDEPENDENT_INSERT] THEN
            EXISTS_TAC (← q r"i:real^N->bool") THEN ASM SET_TAC [],
            ALL_TAC] THEN
         MAP_EVERY X_GEN_TAC
          [← q r"c:real^N->bool", ← q r"k:real^N->bool",
           ← q r"d:real^N->bool", ← q r"l:real^N->bool"] THEN
         STRIP_TAC THEN
         ABBREV_TAC (← q r"z:real^N = @z. z IN relative_interior c") THEN
         SUBGOAL_THEN (← q r"(z:real^N) IN relative_interior c") ASSUME_TAC THENL
          [ASM_MESON_TAC [], ALL_TAC] THEN
         ASM_CASES_TAC (← q r"d:real^N->bool = c") THENL
          [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC [],
           ABBREV_TAC (← q r"w:real^N = @z. z IN relative_interior d") THEN
           SUBGOAL_THEN (← q r"(w:real^N) IN relative_interior d") ASSUME_TAC THENL
            [ASM_MESON_TAC [], ALL_TAC] THEN
           SUBGOAL_THEN
            (← q r"convex hull (z INSERT k) INTER
             convex hull (w INSERT l):real^N->bool =
             convex hull (z INSERT k) INTER convex hull l")
           SUBST1_TAC THENL
            [MATCH_MP_TAC INTER_CONVEX_HULL_INSERT_RELATIVE_EXTERIOR THEN
             EXISTS_TAC (← q r"d:real^N->bool") THEN ASM_SIMP_TAC [] THEN
             CONJ_TAC THENL
              [TRANS_TAC SUBSET_TRANS (← q r"relative_frontier d:real^N->bool") THEN
               ASM_SIMP_TAC [relative_frontier, CLOSURE_CLOSED] THEN
               ASM SET_TAC [],
               ALL_TAC] THEN
             MATCH_MP_TAC (← SET_RULE
              (← q r"!c. s SUBSET c /\ c INTER d = {} ==> DISJOINT s d")) THEN
             EXISTS_TAC (← q r"c:real^N->bool") THEN CONJ_TAC THENL
              [MATCH_MP_TAC HULL_MINIMAL THEN ASM_SIMP_TAC [INSERT_SUBSET] THEN
               CONJ_TAC THENL
                [ASM_MESON_TAC [RELATIVE_INTERIOR_SUBSET, SUBSET], ALL_TAC] THEN
               TRANS_TAC SUBSET_TRANS (← q r"relative_frontier c:real^N->bool") THEN
               ASM_SIMP_TAC [relative_frontier, CLOSURE_CLOSED] THEN SET_TAC [],
               ALL_TAC] THEN
             MATCH_MP_TAC (← SET_RULE
              (← q r"relative_interior c SUBSET c /\
               (c INTER d) INTER relative_interior c = {}
               ==> d INTER relative_interior c = {}")) THEN
             REWRITE_TAC [RELATIVE_INTERIOR_SUBSET] THEN
             MATCH_MP_TAC FACE_OF_DISJOINT_RELATIVE_INTERIOR THEN
             CONJ_TAC THENL [ASM SET_TAC [], DISCH_TAC] THEN
             SUBGOAL_THEN
               (← q r"~(aff_dim (d:real^N->bool) = aff_dim (c:real^N->bool))")
             ASSUME_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
             MATCH_MP_TAC INT_LT_IMP_NE THEN EXPAND_TAC "d" THEN
             MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
             CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
             MATCH_MP_TAC POLYTOPE_IMP_CONVEX THEN ASM SET_TAC [],
             ALL_TAC] THEN
           SUBGOAL_THEN (← q r"convex hull l:real^N->bool = l") SUBST1_TAC THENL
            [MATCH_MP_TAC HULL_P THEN MATCH_MP_TAC POLYTOPE_IMP_CONVEX THEN
             MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN ASM SET_TAC [],
             ALL_TAC] THEN
           SUBGOAL_THEN
            (← q r"convex hull (z INSERT k) INTER l:real^N->bool =
             convex hull k INTER l")
           SUBST1_TAC THENL
            [ONCE_REWRITE_TAC [INTER_COMM] THEN
             MATCH_MP_TAC INTER_CONVEX_HULL_INSERT_RELATIVE_EXTERIOR THEN
             EXISTS_TAC (← q r"c:real^N->bool") THEN ASM_SIMP_TAC [] THEN
             CONJ_TAC THENL
              [TRANS_TAC SUBSET_TRANS (← q r"relative_frontier c:real^N->bool") THEN
               ASM_SIMP_TAC [relative_frontier, CLOSURE_CLOSED] THEN
               ASM SET_TAC [],
               ALL_TAC] THEN
             MATCH_MP_TAC (← SET_RULE
              (← q r"!c. s SUBSET c /\ c INTER d = {} ==> DISJOINT s d")) THEN
             EXISTS_TAC (← q r"d:real^N->bool") THEN CONJ_TAC THENL
              [TRANS_TAC SUBSET_TRANS (← q r"relative_frontier d:real^N->bool") THEN
               ASM_SIMP_TAC [relative_frontier, CLOSURE_CLOSED] THEN SET_TAC [],
               ALL_TAC] THEN
             MATCH_MP_TAC (← SET_RULE
              (← q r"relative_interior c SUBSET c /\
               (c INTER d) INTER relative_interior c = {}
               ==> d INTER relative_interior c = {}")) THEN
             REWRITE_TAC [RELATIVE_INTERIOR_SUBSET] THEN
             MATCH_MP_TAC FACE_OF_DISJOINT_RELATIVE_INTERIOR THEN
             CONJ_TAC THENL [ASM SET_TAC [], DISCH_TAC] THEN
             SUBGOAL_THEN
              (← q r"~(aff_dim (c:real^N->bool) = aff_dim (d:real^N->bool))")
             ASSUME_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
             MATCH_MP_TAC INT_LT_IMP_NE THEN EXPAND_TAC "c" THEN
             MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
             CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
             MATCH_MP_TAC POLYTOPE_IMP_CONVEX THEN ASM SET_TAC [],
             ALL_TAC] THEN
           SUBGOAL_THEN (← q r"convex hull k:real^N->bool = k") SUBST1_TAC THENL
            [MATCH_MP_TAC HULL_P THEN MATCH_MP_TAC POLYTOPE_IMP_CONVEX THEN
             MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN ASM SET_TAC [],
             ALL_TAC] THEN
           CONJ_TAC THEN MATCH_MP_TAC FACE_OF_TRANS THENL
            [EXISTS_TAC (← q r"k:real^N->bool"), EXISTS_TAC (← q r"l:real^N->bool")] THEN
           (CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC]) THENL
            [REMOVE_THEN "*" (MP_TAC o SPEC (← q r"k:real^N->bool")),
             REMOVE_THEN "*" (MP_TAC o SPEC (← q r"l:real^N->bool"))] THEN
           ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
           X_GEN_TAC (← q r"i:real^N->bool") THEN
           DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN
           FIRST_ASSUM (SUBST1_TAC o SYM) THEN
           ONCE_REWRITE_TAC [← SET_RULE (← q r"z INSERT i = {z} UNION i")] THEN
           REWRITE_TAC [← GSYM HULL_UNION_RIGHT] THEN
           REWRITE_TAC [← SET_RULE (← q r"{z} UNION i = z INSERT i")] THEN
           W (MP_TAC o PART_MATCH (lhand o rand)
             FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT o snd) THEN
           (ANTS_TAC THENL
             [ALL_TAC,
              DISCH_THEN SUBST1_TAC THEN EXISTS_TAC (← q r"i:real^N->bool") THEN
              ASM SET_TAC []]) THEN
           MATCH_MP_TAC AFFINE_INDEPENDENT_INSERT THEN ASM_REWRITE_TAC [] THENL
            [REMOVE_THEN "-"
              (MP_TAC o SPECL [← q r"c:real^N->bool", ← q r"k:real^N->bool"]),
             REMOVE_THEN "-"
              (MP_TAC o SPECL [← q r"d:real^N->bool", ← q r"l:real^N->bool"])] THEN
           ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← SET_RULE
            (← q r"a SUBSET a' /\ z IN r ==> a' INTER r = {} ==> ~(z IN a)")) THEN
           FIRST_ASSUM (SUBST1_TAC o SYM) THEN
           ASM_REWRITE_TAC [SUBSET_REFL, AFFINE_HULL_CONVEX_HULL]] THEN
         CONJ_TAC THEN
         MP_TAC (← ISPEC (← q r"c:real^N->bool") lemma1) THEN DISCH_THEN (fun th =>
           W (MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
         ASM_REWRITE_TAC [] THEN
         (ANTS_TAC THENL
           [ASM_SIMP_TAC [] THEN CONJ_TAC THEN
            MATCH_MP_TAC POLYTOPE_IMP_CONVEX THEN
            MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN ASM SET_TAC [],
            DISCH_THEN SUBST1_TAC] THEN
          W (MP_TAC o PART_MATCH (lhand o rand) FACE_OF_POLYTOPE_INSERT_EQ o
            snd) THEN
          ANTS_TAC THENL
           [ALL_TAC,
            DISCH_THEN SUBST1_TAC THEN DISJ2_TAC THEN
            EXISTS_TAC (← q r"k INTER l:real^N->bool") THEN
            ASM_MESON_TAC []] THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN ASM SET_TAC [],
            ASM_MESON_TAC [MEMBER_NOT_EMPTY, IN_INTER]]),
         ASM_SIMP_TAC [FORALL_IN_UNION, INT_LT_IMP_LE] THEN
         REWRITE_TAC [FORALL_IN_GSPEC] THEN
         REWRITE_TAC [AFF_DIM_CONVEX_HULL, AFF_DIM_INSERT] THEN
         REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
         ASM_SIMP_TAC [INT_LT_IMP_LE, ← INT_ARITH (← q r"k:int < n ==> k + &1 <= n")],
         X_GEN_TAC (← q r"c:real^N->bool") THEN DISCH_TAC THEN
         ASM_CASES_TAC (← q r"(c:real^N->bool) IN sk") THENL
          [ASM_MESON_TAC [SUBSET, IN_UNION], ALL_TAC] THEN
         SUBGOAL_THEN (← q r"(c:real^N->bool) IN fat") ASSUME_TAC THENL
          [EXPAND_TAC "fat" THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN
           MATCH_MP_TAC (← INT_ARITH (← q r"x:int <= n /\ ~(x < n) ==> x = n")) THEN
           ASM SET_TAC [],
           ALL_TAC] THEN
         EXISTS_TAC
          (← q r"{ convex hull ((@z:real^N. z IN relative_interior c) INSERT k) |k|
             k IN sc /\ k SUBSET relative_frontier c}") THEN
         CONJ_TAC THENL
          [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC [FORALL_IN_GSPEC] THEN
           X_GEN_TAC (← q r"k:real^N->bool") THEN STRIP_TAC THEN
           REWRITE_TAC [IN_UNION] THEN DISJ2_TAC THEN
           REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [],
           ALL_TAC] THEN
         REWRITE_TAC [← GSYM (← ONCE_REWRITE_RULE [CONJ_SYM] SUBSET_ANTISYM_EQ)] THEN
         CONJ_TAC THEN GEN_REWRITE_TAC I [SUBSET] THENL
          [REWRITE_TAC [FORALL_IN_UNIONS, FORALL_IN_GSPEC, IMP_CONJ,
                        RIGHT_FORALL_IMP_THM] THEN
           X_GEN_TAC (← q r"k:real^N->bool") THEN REPEAT DISCH_TAC THEN
           REWRITE_TAC [← GSYM SUBSET] THEN MATCH_MP_TAC HULL_MINIMAL THEN
           ASM_SIMP_TAC [INSERT_SUBSET] THEN CONJ_TAC THENL
            [ASM_MESON_TAC [RELATIVE_INTERIOR_SUBSET, SUBSET], ALL_TAC] THEN
           TRANS_TAC SUBSET_TRANS (← q r"relative_frontier c:real^N->bool") THEN
           ASM_SIMP_TAC [relative_frontier, CLOSURE_CLOSED] THEN SET_TAC [],
           ALL_TAC] THEN
         X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
         REWRITE_TAC [UNIONS_GSPEC, IN_ELIM_THM] THEN
         ABBREV_TAC (← q r"z:real^N = @z. z IN relative_interior c") THEN
         SUBGOAL_THEN (← q r"(z:real^N) IN relative_interior c") ASSUME_TAC THENL
          [ASM_MESON_TAC [], ALL_TAC] THEN
         MP_TAC (← ISPECL [← q r"c:real^N->bool", ← q r"z:real^N", ← q r"x:real^N"]
            SEGMENT_TO_RELATIVE_FRONTIER) THEN
         ANTS_TAC THENL
          [ASM_SIMP_TAC [POLYTOPE_IMP_BOUNDED] THEN
           DISCH_THEN (MP_TAC o AP_TERM (← q r"aff_dim:(real^N->bool)->int") o
            CONJUNCT2) THEN
           REWRITE_TAC [AFF_DIM_SING] THEN DISCH_TAC THEN
           UNDISCH_TAC (← q r"(c:real^N->bool) IN fat") THEN EXPAND_TAC "fat" THEN
           ASM_REWRITE_TAC [IN_ELIM_THM, INT_OF_NUM_EQ],
           DISCH_THEN (X_CHOOSE_THEN (← q r"y:real^N") STRIP_ASSUME_TAC)] THEN
         MP_TAC (← SPEC (← q r"c:real^N->bool") RELATIVE_FRONTIER_OF_POLYHEDRON_ALT) THEN
         ANTS_TAC THENL [ASM_SIMP_TAC [POLYTOPE_IMP_POLYHEDRON], ALL_TAC] THEN
         DISCH_THEN (MP_TAC o AP_TERM (← q r"\s. (y:real^N) IN s")) THEN
         ASM_REWRITE_TAC [IN_UNIONS, IN_ELIM_THM] THEN
         DISCH_THEN (X_CHOOSE_THEN (← q r"f:real^N->bool") STRIP_ASSUME_TAC) THEN
         SUBGOAL_THEN
          (← q r"?g. FINITE g /\ g SUBSET sc /\ f:real^N->bool = UNIONS g")
         MP_TAC THENL
          [FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "sk" THEN
           REWRITE_TAC [IN_ELIM_THM] THEN
           CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
           MP_TAC (← ISPECL [← q r"f:real^N->bool", ← q r"c:real^N->bool"]
             FACE_OF_AFF_DIM_LT) THEN
           ASM SET_TAC [],
           DISCH_TAC THEN
           SUBGOAL_THEN (← q r"?k:real^N->bool. k IN sc /\ y IN k /\ k SUBSET f")
           MP_TAC THENL [ASM SET_TAC [], MATCH_MP_TAC MONO_EXISTS]] THEN
         X_GEN_TAC (← q r"k:real^N->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
         CONJ_TAC THENL
          [ASM_MESON_TAC [FACE_OF_SUBSET_RELATIVE_FRONTIER, SUBSET_TRANS],
           ALL_TAC] THEN
         FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
          (← q r"x IN s ==> s SUBSET t ==> x IN t"))) THEN
         REWRITE_TAC [SEGMENT_CONVEX_HULL] THEN
         MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC [],
         REWRITE_TAC [FORALL_IN_UNION, FORALL_IN_GSPEC] THEN
         CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
         MAP_EVERY X_GEN_TAC [← q r"c:real^N->bool", ← q r"k:real^N->bool"] THEN
         STRIP_TAC THEN EXISTS_TAC (← q r"c:real^N->bool") THEN
         CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
         MATCH_MP_TAC HULL_MINIMAL THEN ASM_SIMP_TAC [INSERT_SUBSET] THEN
         CONJ_TAC THENL
          [ASM_MESON_TAC [RELATIVE_INTERIOR_SUBSET, SUBSET], ALL_TAC] THEN
         TRANS_TAC SUBSET_TRANS (← q r"relative_frontier c:real^N->bool") THEN
         ASM_SIMP_TAC [relative_frontier, CLOSURE_CLOSED] THEN SET_TAC []])
    prove
     r"!m:(real^N->bool)->bool d.
        FINITE m /\
        (!c. c IN m ==> polytope c) /\
        (!c. c IN m ==> aff_dim c <= d) /\
        (!c1 c2. c1 IN m /\ c2 IN m
                 ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2)
        ==> ?t. simplicial_complex t /\
                (!k. k IN t ==> aff_dim k <= d) /\
                UNIONS t = UNIONS m /\
                (!c. c IN m ==> ?f. FINITE f /\ f SUBSET t /\ c = UNIONS f) /\
                (!k. k IN t ==> ?c. c IN m /\ k SUBSET c)"
     (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"&0:int <= d") THENL
       [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM INT_OF_NUM_EXISTS]) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") SUBST1_TAC) THEN STRIP_TAC THEN
        MP_TAC (← ISPECL
          [← q r"n:num", ← q r"UNIONS {{f:real^N->bool | f face_of c} | c IN m}"]
          lemma2) THEN
        REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FINITE_UNIONS,
                     FORALL_IN_UNIONS, FORALL_IN_GSPEC, EXISTS_IN_UNIONS] THEN
        ANTS_TAC THENL [ASM_SIMP_TAC [SIMPLE_IMAGE, FINITE_IMAGE], ALL_TAC] THEN
        ANTS_TAC THENL [ASM_MESON_TAC [FINITE_POLYTOPE_FACES], ALL_TAC] THEN
        ANTS_TAC THENL [ASM_MESON_TAC [FACE_OF_POLYTOPE_POLYTOPE], ALL_TAC] THEN
        ANTS_TAC THENL
         [ASM_MESON_TAC [FACE_OF_IMP_SUBSET, AFF_DIM_SUBSET, INT_LE_TRANS],
          ALL_TAC] THEN
        ANTS_TAC THENL
         [REWRITE_TAC [UNIONS_GSPEC, IN_ELIM_THM] THEN ASM_MESON_TAC [FACE_OF_TRANS],
          ALL_TAC] THEN
        ANTS_TAC THENL [ASM_MESON_TAC [FACE_OF_INTER_SUBFACE], ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:(real^N->bool)->bool") THEN
        ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN REWRITE_TAC [EXISTS_IN_GSPEC] THEN
        REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN
        REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC]) THEN
        MATCH_MP_TAC (← TAUT (← q r"(q ==> p) /\ q ==> p /\ q")) THEN
        CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN CONJ_TAC THENL
         [ASM_MESON_TAC [FACE_OF_REFL, POLYTOPE_IMP_CONVEX],
          ASM_MESON_TAC [FACE_OF_IMP_SUBSET, SUBSET_TRANS]],
        STRIP_TAC THEN EXISTS_TAC (← q r"m:(real^N->bool)->bool") THEN
        ASM_REWRITE_TAC [simplicial_complex] THEN CONJ_TAC THENL
         [SUBGOAL_THEN (← q r"!c:real^N->bool. c IN m ==> c = {}")
           (fun th => SIMP_TAC [th, IMP_CONJ, SIMPLEX_EMPTY, FACE_OF_EMPTY] THEN
                      MESON_TAC [th]) THEN
          ASM_MESON_TAC [INT_LE_TRANS, AFF_DIM_POS_LE],
          CONJ_TAC THENL [ALL_TAC, MESON_TAC [SUBSET_REFL]] THEN
          MESON_TAC [SING_SUBSET, UNIONS_1, FINITE_SING]]]))

  let SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX ← prove
   r"!m:(real^N->bool)->bool.
        FINITE m /\
        (!c. c IN m ==> polytope c) /\
        (!c1 c2. c1 IN m /\ c2 IN m
                 ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2)
        ==> ?t. simplicial_complex t /\
                UNIONS t = UNIONS m /\
                (!c. c IN m ==> ?f. FINITE f /\ f SUBSET t /\ c = UNIONS f) /\
                (!k. k IN t ==> ?c. c IN m /\ k SUBSET c)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"m:(real^N->bool)->bool", ← q r"&(dimindex(:N)):int"]
          SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX_LOWDIM) THEN
    ASM_REWRITE_TAC [AFF_DIM_LE_UNIV])

  let FINE_SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX ← prove
   r"!m:(real^N->bool)->bool e.
        &0 < e /\ FINITE m /\
        (!c. c IN m ==> polytope c) /\
        (!c1 c2. c1 IN m /\ c2 IN m
                 ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2)
        ==> ?t. simplicial_complex t /\
                (!k. k IN t ==> diameter k < e) /\
                UNIONS t = UNIONS m /\
                (!c. c IN m ==> ?f. FINITE f /\ f SUBSET t /\ c = UNIONS f) /\
                (!k. k IN t ==> ?c. c IN m /\ k SUBSET c)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"m:(real^N->bool)->bool", ← q r"&(dimindex(:N)):int", ← q r"e:real"]
          CELL_COMPLEX_SUBDIVISION_EXISTS) THEN
    ASM_REWRITE_TAC [AFF_DIM_LE_UNIV] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"n:(real^N->bool)->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPEC (← q r"n:(real^N->bool)->bool")
     SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"t:(real^N->bool)->bool") THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [REAL_LET_TRANS, DIAMETER_SUBSET, SIMPLEX_IMP_POLYTOPE,
                     POLYTOPE_IMP_BOUNDED],
      ALL_TAC,
      ASM_MESON_TAC [SUBSET_TRANS]] THEN
    X_GEN_TAC (← q r"c:real^N->bool") THEN DISCH_TAC THEN
    EXISTS_TAC (← q r"{k:real^N->bool | k IN t /\ k SUBSET c}") THEN
    RULE_ASSUM_TAC (REWRITE_RULE [simplicial_complex]) THEN
    ASM_SIMP_TAC [FINITE_RESTRICT, SUBSET_RESTRICT] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN ONCE_REWRITE_TAC [SUBSET] THEN
    REWRITE_TAC [FORALL_IN_UNIONS, FORALL_IN_GSPEC] THEN
    CONJ_TAC THENL [REWRITE_TAC [UNIONS_GSPEC], SET_TAC []] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:real^N") THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"?d. d IN n /\ (x:real^N) IN d /\ d SUBSET c")
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"?f. FINITE f /\ f SUBSET t /\ d:real^N->bool = UNIONS f")
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(x:real^N) IN UNIONS f") MP_TAC THENL
     [ASM SET_TAC [], REWRITE_TAC [IN_UNIONS]] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC [])

  pure { SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX_LOWDIM,
         SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX,
         FINE_SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX }

/- ------------------------------------------------------------------------- -/
/- Some results on cell division with full-dimensional cells only.           -/
/- (polytope.ml 8781-8941)                                                   -/
/- ------------------------------------------------------------------------- -/

structure POW where
  REGULAR_CLOSED_UNIONS_FAT_CELLS_UNIV : thm
  CONVEX_UNIONS_FULLDIM_CELLS : thm
  TRIANGULAR_SUBDIVISION_OF_CELL_COMPLEX : thm
  FINE_TRIANGULAR_SUBDIVISION_OF_CELL_COMPLEX : thm
  deriving Inhabited

set_option maxHeartbeats 8000000 in
@[nospecialize]
def setupPOW [HolBase] (D : PolytopeDeps) (BPOJ : POJ) (BPOS : POS) (BPOT : POT) (BPOV : POV) : ExceptT String IO POW := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, SET_RULE, SET_TAC, .. } := D.cvx
  let { FINITE_RESTRICT, FORALL_IN_GSPEC, .. } := D.cvx.core1
  let { IN_DIFF, INT_LE_ANTISYM, INT_LT_LE, INT_NOT_LT, INTERS_GSPEC, .. } := D.cvx.core2
  let { IN_ELIM_THM, IN_UNIONS, MONO_EXISTS, NOT_FORALL_THM, NOT_IMP, .. } := D.cvx.core3
  let { SIMPLE_IMAGE_GEN, SUBSET, SUBSET_ANTISYM, SUBSET_TRANS, .. } := D.cvx.core5
  let { UNIONS_GSPEC, UNIONS_UNION, .. } := D.cvx.core6
  let { COUNTABLE_IMAGE, .. } := D.cvx.lib
  let { OPEN_IN_DIFF, .. } := D.cvx.met
  let { CLOSED_CLOSURE, CLOSED_IMP_LOCALLY_COMPACT, CLOSED_SUBSET, CLOSURE_CLOSED,
        CLOSURE_EQ, .. } := D.cvx.top1
  let { CLOSURE_EQ_EMPTY, .. } := D.cvx.top2
  let { OPEN_IN_REFL, SUBSET_CLOSURE, .. } := D.cvx.top5
  let { FINITE_IMP_COUNTABLE, .. } := D.qcard
  let { BAIRE, CLOSED_UNIONS, CLOSURE_INTERIOR_UNION_CLOSED,
        NOWHERE_DENSE_COUNTABLE_UNIONS_CLOSED, REGULAR_CLOSED_UNIONS, .. } := D.qtop
  let { AFF_DIM_SUBSET, .. } := D.qcvx1
  let { CONVEX_CLOSURE_INTERIOR, .. } := D.qcvx2
  let { DENSE_COMPLEMENT_CONVEX_CLOSED, .. } := D.qcvx3
  let { POLYTOPE_IMP_CLOSED, POLYTOPE_IMP_CONVEX, .. } := BPOJ
  let { SIMPLEX_IMP_POLYTOPE, .. } := BPOS
  let { simplicial_complex, triangulation, .. } := BPOT
  let { FINE_SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX, SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX,
        .. } := BPOV
  -- @@SCOPE END

  let REGULAR_CLOSED_UNIONS_FAT_CELLS_UNIV ← (do
    let lemma ← prove
     r"!s t:real^N->bool.
          closed t /\
          closure(interior(s UNION t)) = s UNION t /\
          closure(interior s) = s /\ closure(interior t) = {}
          ==> s UNION t = s"
     (REPEAT STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"t:real^N->bool"]
          CLOSURE_INTERIOR_UNION_CLOSED) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [CLOSED_CLOSURE], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN SET_TAC [])
    prove
     r"!s u:real^N->bool.
        closure(interior u) = u /\
        FINITE s /\ (!c. c IN s ==> closed c /\ convex c) /\ UNIONS s = u
        ==> UNIONS {c | c IN s /\ ~(interior c = {})} = u"
     (REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       (← q r"u = UNIONS {c | c IN s /\ ~(interior c = {})} UNION
            UNIONS {c:real^N->bool | c IN s /\ interior c = {}}")
      SUBST1_TAC THENL
       [REWRITE_TAC [← GSYM UNIONS_UNION] THEN EXPAND_TAC "u" THEN AP_TERM_TAC THEN
        SET_TAC [],
        ALL_TAC] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC lemma THEN
      ASM_REWRITE_TAC [← GSYM UNIONS_UNION, ← SET_RULE
       (← q r"{x | x IN s /\ ~P x} UNION {x | x IN s /\ P x} = s")] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_UNIONS THEN
        ASM_SIMP_TAC [FINITE_RESTRICT, IN_ELIM_THM],
        MATCH_MP_TAC REGULAR_CLOSED_UNIONS THEN
        ASM_SIMP_TAC [FINITE_RESTRICT, IN_ELIM_THM, CONVEX_CLOSURE_INTERIOR,
                      CLOSURE_EQ],
        REWRITE_TAC [CLOSURE_EQ_EMPTY] THEN
        MATCH_MP_TAC NOWHERE_DENSE_COUNTABLE_UNIONS_CLOSED THEN
        ASM_SIMP_TAC [FINITE_IMP_COUNTABLE, FINITE_RESTRICT, IN_ELIM_THM]]))

  let CONVEX_UNIONS_FULLDIM_CELLS ← prove
   r"!s u:real^N->bool.
        FINITE s /\ (!c. c IN s ==> closed c /\ convex c) /\
        UNIONS s = u /\ convex u
        ==> UNIONS {c | c IN s /\ aff_dim c = aff_dim u} = u"
   (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"closed(u:real^N->bool)") ASSUME_TAC THENL
     [ASM_MESON_TAC [CLOSED_UNIONS], ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    ASM_CASES_TAC
     (← q r"!c. c IN s ==> aff_dim(c:real^N->bool) = aff_dim(u:real^N->bool)")
    THENL [ASM SET_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC (← MESON [CLOSURE_CLOSED]
       (← q r"closed s /\ u SUBSET closure s ==> u SUBSET s")) THEN
    ASM_SIMP_TAC [CLOSED_UNIONS, FINITE_RESTRICT, FORALL_IN_GSPEC] THEN
    TRANS_TAC SUBSET_TRANS
     (← q r"closure(INTERS
       {u DIFF c:real^N->bool |c| c IN s /\ aff_dim c < aff_dim u})") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC BAIRE THEN
      ASM_SIMP_TAC [FORALL_IN_GSPEC, CLOSED_IMP_LOCALLY_COMPACT] THEN
      ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
      ASM_SIMP_TAC [COUNTABLE_IMAGE, FINITE_IMP_COUNTABLE, FINITE_RESTRICT] THEN
      X_GEN_TAC (← q r"c:real^N->bool") THEN REPEAT STRIP_TAC THENL
       [MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC [OPEN_IN_REFL] THEN
        MATCH_MP_TAC CLOSED_SUBSET THEN ASM SET_TAC [],
        MATCH_MP_TAC (← SET_RULE (← q r"t = s ==> s SUBSET t")) THEN
        MATCH_MP_TAC DENSE_COMPLEMENT_CONVEX_CLOSED THEN ASM_REWRITE_TAC []],
      MATCH_MP_TAC SUBSET_CLOSURE THEN
      REWRITE_TAC [SUBSET, INTERS_GSPEC, FORALL_IN_GSPEC] THEN
      X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      REWRITE_TAC [UNIONS_GSPEC, IN_ELIM_THM]  THEN
      SUBGOAL_THEN
       (← q r"?c. c IN s /\ aff_dim(c:real^N->bool) < aff_dim(u:real^N->bool)")
      ASSUME_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
        MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [NOT_IMP, INT_LT_LE] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM SET_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(x:real^N) IN u /\ x IN UNIONS s")
       (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THENL [ASM SET_TAC [], ALL_TAC] THEN
      REWRITE_TAC [IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
      SIMP_TAC [] THEN X_GEN_TAC (← q r"c:real^N->bool") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"c:real^N->bool")) THEN
      ASM_SIMP_TAC [IN_DIFF, INT_NOT_LT, ← GSYM INT_LE_ANTISYM] THEN
      DISCH_TAC THEN MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM SET_TAC []])

  let TRIANGULAR_SUBDIVISION_OF_CELL_COMPLEX ← prove
   r"!m:(real^N->bool)->bool d.
        FINITE m /\
        (!c. c IN m ==> polytope c) /\
        (!c. c IN m ==> aff_dim c = d) /\
        (!c1 c2. c1 IN m /\ c2 IN m
                 ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2)
        ==> ?t. triangulation t /\
                (!k. k IN t ==> aff_dim k = d) /\
                UNIONS t = UNIONS m /\
                (!c. c IN m ==> ?f. FINITE f /\ f SUBSET t /\ c = UNIONS f) /\
                (!k. k IN t ==> ?c. c IN m /\ k SUBSET c)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"m:(real^N->bool)->bool")
      SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX) THEN
    ASM_REWRITE_TAC [simplicial_complex, triangulation] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:(real^N->bool)->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"{k:real^N->bool | k IN t /\ aff_dim k = d}") THEN
    ASM_SIMP_TAC [FINITE_RESTRICT, IN_ELIM_THM] THEN
    MATCH_MP_TAC (← TAUT (← q r"(q ==> p) /\ q ==> p /\ q")) THEN CONJ_TAC THENL
     [ASM SET_TAC [], ALL_TAC] THEN
    X_GEN_TAC (← q r"c:real^N->bool") THEN DISCH_TAC THEN
    UNDISCH_THEN
     (← q r"!c:real^N->bool. c IN m ==> ?f. FINITE f /\ f SUBSET t /\ c = UNIONS f")
     (MP_TAC o SPEC (← q r"c:real^N->bool")) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"f:(real^N->bool)->bool")
      (STRIP_ASSUME_TAC o GSYM)) THEN
    EXISTS_TAC (← q r"{k:real^N->bool | k IN f /\ aff_dim k = d}") THEN
    ASM_SIMP_TAC [FINITE_RESTRICT] THEN
    CONJ_TAC THENL [ASM SET_TAC [], CONV_TAC SYM_CONV] THEN
    SUBGOAL_THEN (← q r"d = aff_dim(c:real^N->bool)") SUBST1_TAC THENL
     [ASM_MESON_TAC [], MATCH_MP_TAC CONVEX_UNIONS_FULLDIM_CELLS] THEN
    ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [SUBSET, POLYTOPE_IMP_CONVEX, POLYTOPE_IMP_CLOSED,
                   SIMPLEX_IMP_POLYTOPE])

  let FINE_TRIANGULAR_SUBDIVISION_OF_CELL_COMPLEX ← prove
   r"!m:(real^N->bool)->bool d e.
        &0 < e /\ FINITE m /\
        (!c. c IN m ==> polytope c) /\
        (!c. c IN m ==> aff_dim c = d) /\
        (!c1 c2. c1 IN m /\ c2 IN m
                 ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2)
        ==> ?t. triangulation t /\
                (!k. k IN t ==> diameter k < e) /\
                (!k. k IN t ==> aff_dim k = d) /\
                UNIONS t = UNIONS m /\
                (!c. c IN m ==> ?f. FINITE f /\ f SUBSET t /\ c = UNIONS f) /\
                (!k. k IN t ==> ?c. c IN m /\ k SUBSET c)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"m:(real^N->bool)->bool", ← q r"e:real"]
      FINE_SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX) THEN
    ASM_REWRITE_TAC [simplicial_complex, triangulation] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:(real^N->bool)->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"{k:real^N->bool | k IN t /\ aff_dim k = d}") THEN
    ASM_SIMP_TAC [FINITE_RESTRICT, IN_ELIM_THM] THEN
    MATCH_MP_TAC (← TAUT (← q r"(q ==> p) /\ q ==> p /\ q")) THEN CONJ_TAC THENL
     [ASM SET_TAC [], ALL_TAC] THEN
    X_GEN_TAC (← q r"c:real^N->bool") THEN DISCH_TAC THEN
    UNDISCH_THEN
     (← q r"!c:real^N->bool. c IN m ==> ?f. FINITE f /\ f SUBSET t /\ c = UNIONS f")
     (MP_TAC o SPEC (← q r"c:real^N->bool")) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"f:(real^N->bool)->bool")
      (STRIP_ASSUME_TAC o GSYM)) THEN
    EXISTS_TAC (← q r"{k:real^N->bool | k IN f /\ aff_dim k = d}") THEN
    ASM_SIMP_TAC [FINITE_RESTRICT] THEN
    CONJ_TAC THENL [ASM SET_TAC [], CONV_TAC SYM_CONV] THEN
    SUBGOAL_THEN (← q r"d = aff_dim(c:real^N->bool)") SUBST1_TAC THENL
     [ASM_MESON_TAC [], MATCH_MP_TAC CONVEX_UNIONS_FULLDIM_CELLS] THEN
    ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [SUBSET, POLYTOPE_IMP_CONVEX, POLYTOPE_IMP_CLOSED,
                   SIMPLEX_IMP_POLYTOPE])

  pure { REGULAR_CLOSED_UNIONS_FAT_CELLS_UNIV, CONVEX_UNIONS_FULLDIM_CELLS,
         TRIANGULAR_SUBDIVISION_OF_CELL_COMPLEX, FINE_TRIANGULAR_SUBDIVISION_OF_CELL_COMPLEX }

end HolMultiLib.Polytope
