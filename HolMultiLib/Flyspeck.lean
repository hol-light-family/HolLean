/- ========================================================================= -/
/- Multivariate/flyspeck.ml: results intended for Flyspeck                   -/
/- ========================================================================= -/
/- File: HolMultiLib/Flyspeck.lean

  Original (c) Copyright, John Harrison 1998-2008 (see flyspeck.ml).
  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/flyspeck.ml`, in the style of
  HolMultiLib/Measure.lean: pure, the proofs translated by hand, one `let`
  per OCaml `let`, in file order.  The load-time effects are at their file
  positions.  What flyspeck.ml uses from earlier files is passed in `FlyspeckDeps`.
  SessionMultiLib/Flyspeck.lean supplies it.
-/

import HolMultiLib.Geom
import HolMultiLib.Cross
import HolMultiLib.Determinants

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolMultiLib.Flyspeck

/- The theorems flyspeck.ml uses that the deps chain does not carry, grouped by the
   file that proves them. -/

structure QConvexThms where
  (AFFINE_HULL_FINITE_STEP_GEN AFFINE_HULL_INSERT_SPAN AFFINE_HULL_INSERT_SUBSET_SPAN
   AFFINE_HULL_LINEAR_IMAGE COLLINEAR_3_AFFINE_HULL COLLINEAR_3_IN_AFFINE_HULL
   COLLINEAR_AFFINE_HULL COLLINEAR_AFFINE_HULL_COLLINEAR coplanar COPLANAR_3
   COPLANAR_AFFINE_HULL_COPLANAR COPLANAR_EMPTY COPLANAR_SUBSET
   SPAN_CONVEX_CONE_ALLSIGNS : thm)
  deriving Inhabited

structure QVectorsThms where
  (BASIS_EQ_0 CARD_EQ_DIM COLLINEAR_3_DOT_MULTIPLES DIM_INJECTIVE_LINEAR_IMAGE
   DOT_CAUCHY_SCHWARZ_EQUAL DROPOUT_ADD DROPOUT_MUL DROPOUT_SUB INDEPENDENT_3
   INDEPENDENT_BOUND INDEPENDENT_BOUND_GENERAL INDEPENDENT_EXPLICIT INDEPENDENT_MONO
   LOWDIM_EXPAND_BASIS NORM_LT_SQUARE_ALT RANK_ROW SPAN_3 SPAN_BREAKDOWN_EQ
   SPAN_CARD_GE_DIM SPAN_LINEAR_IMAGE SPAN_MUL_EQ SPAN_NEG_EQ VSUM_ADD_GEN : thm)
  deriving Inhabited

structure QMeasureThms where
  (HAS_MEASURE_EMPTY HAS_MEASURE_MEASURE HAS_MEASURE_STRETCH MEASURABLE_BALL
   MEASURABLE_CBALL MEASURABLE_CONVEX_HULL MEASURABLE_LINEAR_IMAGE
   MEASURABLE_NEGLIGIBLE_SYMDIFF MEASURABLE_TRANSLATION MEASURE_DISJOINT_UNION
   MEASURE_INTERIOR MEASURE_NEGLIGIBLE_SYMDIFF MEASURE_ORTHOGONAL_IMAGE_EQ
   MEASURE_TETRAHEDRON MEASURE_TRANSLATION MEASURE_UNION MEASURE_UNIQUE
   NEGLIGIBLE_AFFINE_HULL_3 NEGLIGIBLE_CONVEX_FRONTIER NEGLIGIBLE_CONVEX_HULL
   NEGLIGIBLE_HYPERPLANE NEGLIGIBLE_LOWDIM NEGLIGIBLE_SPHERE
   NEGLIGIBLE_TRANSLATION_REV STARLIKE_NEGLIGIBLE_STRONG : thm)
  deriving Inhabited

structure QDeterminantsThms where
  (COLLINEAR_LINEAR_IMAGE_EQ COLLINEAR_TRANSLATION_EQ
   ORTHOGONAL_TRANSFORMATION_INVERSE ORTHOGONAL_TRANSFORMATION_SURJECTIVE
   ROTATION_LOWDIM_HORIZONTAL : thm)
  deriving Inhabited

structure QSessionThms where
  (EXISTS_PAIRED_THM INSERT_UNION INSERT_UNION_EQ ITERATE_EXPAND_CASES LET_DEF LET_END_DEF
   REAL_CONVEX_BOUND2_LT SUM_CASES_1 : thm)
  deriving Inhabited

structure QPolytopeThms where
  (EDGE_OF_IMP_SUBSET EDGE_OF_LINEAR_IMAGE EXTREME_POINTS_OF_LINEAR_IMAGE face_of
   FACE_OF_IMP_SUBSET FACE_OF_POLYHEDRON_SUBSET_FACET facet_of FACET_OF_REFL
   POLYHEDRON_CONVEX_CONE_HULL POLYHEDRON_IMP_CLOSED polytope POLYTOPE_IMP_POLYHEDRON
   SUBSET_OF_FACE_OF : thm)
  deriving Inhabited

structure QFloorThms where
  (REAL_EQ_INTEGERS_IMP : thm)
  deriving Inhabited

structure QTopologyThms where
  (ball BOUNDED_SUBSET_OPEN_INTERVAL CONTINUOUS_CLOSED_PREIMAGE_CONSTANT
   CONTINUOUS_ON_UNION_LOCAL : thm)
  deriving Inhabited

structure FlyspeckDeps where
  gm : HolMultiLib.Geom.GeomDeps
  gea : HolMultiLib.Geom.GEA
  geb : HolMultiLib.Geom.GEB
  gec : HolMultiLib.Geom.GEC
  ged : HolMultiLib.Geom.GED
  gee : HolMultiLib.Geom.GEE
  crd : HolMultiLib.Cross.CrossDeps
  crs : HolMultiLib.Cross.CRS
  -- theorems
  qconvex : QConvexThms
  qvectors : QVectorsThms
  qmeasure : QMeasureThms
  qdeterminants : QDeterminantsThms
  qsession : QSessionThms
  qpolytope : QPolytopeThms
  qfloor : QFloorThms
  qtopology : QTopologyThms
  -- procedures not reachable through the chain
  geominv : HolMultiLib.Determinants.GeomInv
  geomorigin : HolMultiLib.Determinants.GeomOrigin
  /-- vectors.ml's `EXPAND_QUANTS_CONV`. -/
  EXPAND_QUANTS_CONV : thm → ExceptT String IO ioconv
  /-- vectors.ml's `PARTIAL_EXPAND_QUANTS_CONV`. -/
  PARTIAL_EXPAND_QUANTS_CONV : List String → thm → ExceptT String IO ioconv
  let_CONV : ioconv
  /-- preterm.ml's `override_interface` (load-time effect). -/
  override_interface : String → term → ExceptT String IO Unit
  /-- simp.ml's `basic_congs` and `set_basic_congs` (load-time effect). -/
  basic_congs : IO (List thm)
  set_basic_congs : List thm → IO Unit

/- ------------------------------------------------------------------------- -/
/- prioritize_vector(); norm of a cross product; miscellaneous lemmas;       -/
/- special scaling theorems; "dropout"; the "padding" injection pad2d3d.     -/
/- (flyspeck.ml 1-271)                                                       -/
/- ------------------------------------------------------------------------- -/

structure FYA where
  NORM_CROSS_SIN : thm
  COPLANAR_INSERT_0_NEG : thm
  COPLANAR_IMP_NEGLIGIBLE : thm
  NOT_COPLANAR_0_4_IMP_INDEPENDENT : thm
  NOT_COPLANAR_NOT_COLLINEAR : thm
  SUBSET_AFFINE_HULL_SPECIAL_SCALE : thm
  COLLINEAR_SPECIAL_SCALE : thm
  COLLINEAR_SCALE_ALL : thm
  COPLANAR_SPECIAL_SCALE : thm
  COPLANAR_SCALE_ALL : thm
  DROPOUT_BASIS_3 : thm
  COLLINEAR_BASIS_3 : thm
  OPEN_DROPOUT_3 : thm
  SLICE_DROPOUT_3 : thm
  NOT_COPLANAR_IMP_NOT_COLLINEAR_DROPOUT_3 : thm
  SLICE_312 : thm
  SLICE_123 : thm
  pad2d3d : thm
  FORALL_PAD2D3D_THM : thm
  QUANTIFY_PAD2D3D_THM : thm
  LINEAR_PAD2D3D : thm
  INJECTIVE_PAD2D3D : thm
  NORM_PAD2D3D : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYA [HolBase] (D : FlyspeckDeps) : ExceptT String IO FYA := do
  -- @@SCOPE BEGIN
  let { prioritize_vector, .. } := D.gm
  let { SIN_VECTOR_ANGLE_POS, VECTOR_ANGLE, .. } := D.gea
  let { ASM_MESON_TAC, MESON_TAC, new_definition, REAL_ARITH_TAC, REAL_RING, .. } := D.crd
  let { NORM_CROSS_DOT, .. } := D.crs
  let { COLLINEAR_AFFINE_HULL, coplanar, .. } := D.qconvex
  let { SPAN_3, SPAN_MUL_EQ, SPAN_NEG_EQ, .. } := D.qvectors
  let { NEGLIGIBLE_AFFINE_HULL_3, .. } := D.qmeasure
  let { IN_SLICE, slice, .. } := D.gm.rzaz
  let { DOT_3, .. } := D.gm.qvectors
  let { REAL_POW_EQ, .. } := D.gm.qsession
  let { AFFINE_HULL_2, .. } := D.gm.qconvex
  let { ARITH, basis, CART_EQ, DIMINDEX_3, FORALL_3, LAMBDA_BETA, linear, NORM_POS_LE,
        REAL_LE_MUL, REAL_MUL_LZERO, VECTOR_3, VECTOR_MUL_COMPONENT, .. } := D.crd.thms
  let { SIN_CIRCLE, .. } := D.gm.ra.tsc
  let { dropout, DROPOUT_PUSHIN, LINEAR_DROPOUT, pushin, .. } := D.gm.ra.qvectors
  let { NEGLIGIBLE_SUBSET, .. } := D.gm.ra.ts.cn.ms.qintegration3
  let { ARITH_RULE, ARITH_TAC, MESON, REAL_ARITH, REAL_FIELD, SET_RULE, SET_TAC,
        .. } := D.gm.ra.ts.cn.cx.cvx
  let { FORALL_2, .. } := D.gm.ra.ts.cn.cx.cpx
  let { CONTINUOUS_OPEN_PREIMAGE_UNIV, .. } := D.gm.ra.ts.cn.ms.ig.qtopology
  let { ARITH_EQ, CONTRAPOS_THM, DIMINDEX_2, EMPTY_SUBSET, EQ_IMP, EXISTS_REFL, EXTENSION,
        .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { INSERT_AC, INSERT_SUBSET, .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_INTER, IN_UNIV, LEFT_IMP_EXISTS_THM,
        LT_IMP_LE, LT_REFL, MONO_EXISTS, NOT_IN_EMPTY, REAL_ADD_LID, REAL_ADD_RID,
        .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_MUL_LID, REAL_MUL_RID, REAL_MUL_RZERO, RIGHT_EXISTS_AND_THM, SUBSET,
        .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { UNWIND_THM1, .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { HULL_INC, HULL_MONO, .. } := D.gm.ra.ts.cn.cx.cvx.misc
  let { BASIS_COMPONENT, COLLINEAR_LEMMA, DOT_2, .. } := D.gm.ra.ts.cn.cx.cvx.vec1
  let { NORM_EQ, .. } := D.gm.ra.ts.cn.cx.cvx.vec2
  let { SPAN_MONO, SPAN_SUPERSET, .. } := D.gm.ra.ts.cn.cx.cvx.vec3
  let { dependent, independent, VEC_COMPONENT, VECTOR_ADD_COMPONENT,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { LINEAR_CONTINUOUS_AT, .. } := D.gm.ra.ts.cn.cx.cvx.top4
  let { SPAN_2, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qvec
  let { AFFINE_HULL_3, AFFINE_HULL_EQ_SPAN, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qcvx1
  -- @@SCOPE END

  prioritize_vector

  /- Not really Flyspeck-specific but needs both angles and cross products. -/

  let NORM_CROSS_SIN ← prove
   r"!x y. norm(x cross y) = norm(x) * norm(y) * sin(vector_angle x y)"
   (REPEAT GEN_TAC THEN
    MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC (← q r"2") THEN
    SIMP_TAC [NORM_POS_LE, SIN_VECTOR_ANGLE_POS, REAL_LE_MUL, ARITH_EQ] THEN
    MP_TAC (← SPECL [← q r"x:real^3", ← q r"y:real^3"] NORM_CROSS_DOT) THEN
    REWRITE_TAC [VECTOR_ANGLE] THEN
    MP_TAC (← SPEC (← q r"vector_angle (x:real^3) y") SIN_CIRCLE) THEN
    CONV_TAC REAL_RING)

  /- Other miscelleneous lemmas. -/

  let COPLANAR_INSERT_0_NEG ← prove
   r"coplanar(vec 0 INSERT --x INSERT s) <=> coplanar(vec 0 INSERT x INSERT s)"
   (REWRITE_TAC [coplanar, INSERT_SUBSET] THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"a /\ b /\ c <=> ~(a ==> ~(b /\ c))")] THEN
    SIMP_TAC [AFFINE_HULL_EQ_SPAN, SPAN_NEG_EQ])

  let COPLANAR_IMP_NEGLIGIBLE ← prove
   r"!s:real^3->bool. coplanar s ==> negligible s"
   (REWRITE_TAC [coplanar] THEN
    MESON_TAC [NEGLIGIBLE_AFFINE_HULL_3, NEGLIGIBLE_SUBSET])

  let NOT_COPLANAR_0_4_IMP_INDEPENDENT ← prove
   r"!v1 v2 v3:real^N. ~coplanar {vec 0,v1,v2,v3} ==> independent {v1,v2,v3}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [independent, CONTRAPOS_THM] THEN
    REWRITE_TAC [dependent] THEN
    SUBGOAL_THEN
     (← q r"!v1 v2 v3:real^N. v1 IN span {v2,v3} ==> coplanar{vec 0,v1,v2,v3}")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC [coplanar] THEN
      MAP_EVERY EXISTS_TAC [← q r"vec 0:real^N", ← q r"v2:real^N", ← q r"v3:real^N"] THEN
      SIMP_TAC [AFFINE_HULL_EQ_SPAN, HULL_INC, IN_INSERT] THEN
      REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET] THEN
      ASM_SIMP_TAC [SPAN_SUPERSET, IN_INSERT] THEN
      POP_ASSUM MP_TAC THEN SPEC_TAC (← q r"v1:real^N", ← q r"v1:real^N") THEN
      REWRITE_TAC [← GSYM SUBSET] THEN MATCH_MP_TAC SPAN_MONO THEN SET_TAC [],
      REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o SPECL [← q r"v1:real^N", ← q r"v2:real^N", ← q r"v3:real^N"]),
        FIRST_X_ASSUM (MP_TAC o SPECL [← q r"v2:real^N", ← q r"v3:real^N", ← q r"v1:real^N"]),
        FIRST_X_ASSUM (MP_TAC o SPECL [← q r"v3:real^N", ← q r"v1:real^N", ← q r"v2:real^N"])]
      THEN REWRITE_TAC [INSERT_AC] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE
       (← q r"a IN s ==> s SUBSET t ==> a IN t"))) THEN
      MATCH_MP_TAC SPAN_MONO THEN SET_TAC []])

  let NOT_COPLANAR_NOT_COLLINEAR ← prove
   r"!v1 v2 v3 w:real^N. ~coplanar {v1, v2, v3, w} ==> ~collinear {v1, v2, v3}"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [COLLINEAR_AFFINE_HULL, coplanar, CONTRAPOS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"x:real^N") THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"y:real^N") THEN
    REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET] THEN STRIP_TAC THEN
    EXISTS_TAC (← q r"w:real^N") THEN ASM_SIMP_TAC [HULL_INC, IN_INSERT] THEN
    REPEAT CONJ_TAC THEN
    MATCH_MP_TAC (← SET_RULE (← q r"!t. t SUBSET s /\ x IN t ==> x IN s")) THEN
    EXISTS_TAC (← q r"affine hull {x:real^N,y}") THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC [])

  /- Some special scaling theorems. -/

  let SUBSET_AFFINE_HULL_SPECIAL_SCALE ← prove
   r"!a x s t.
          ~(a = &0)
          ==> (vec 0 INSERT (a % x) INSERT s SUBSET affine hull t <=>
               vec 0 INSERT x INSERT s SUBSET affine hull t)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [INSERT_SUBSET] THEN
    MATCH_MP_TAC (← TAUT (← q r"(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)")) THEN
    ASM_SIMP_TAC [AFFINE_HULL_EQ_SPAN, SPAN_MUL_EQ])

  let COLLINEAR_SPECIAL_SCALE ← prove
   r"!a x y. ~(a = &0) ==> (collinear {vec 0,a % x,y} <=> collinear{vec 0,x,y})"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [COLLINEAR_AFFINE_HULL] THEN
    ASM_SIMP_TAC [SUBSET_AFFINE_HULL_SPECIAL_SCALE])

  let COLLINEAR_SCALE_ALL ← prove
   r"!a b v w. ~(a = &0) /\ ~(b = &0)
               ==> (collinear {vec 0,a % v,b % w} <=> collinear {vec 0,v,w})"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [COLLINEAR_SPECIAL_SCALE] THEN
    ONCE_REWRITE_TAC [← SET_RULE (← q r"{a,b,c} = {a,c,b}")] THEN
    ASM_SIMP_TAC [COLLINEAR_SPECIAL_SCALE])

  let COPLANAR_SPECIAL_SCALE ← prove
   r"!a x y z.
      ~(a = &0) ==> (coplanar {vec 0,a % x,y,z} <=> coplanar {vec 0,x,y,z})"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [coplanar] THEN
    ASM_SIMP_TAC [SUBSET_AFFINE_HULL_SPECIAL_SCALE])

  let COPLANAR_SCALE_ALL ← prove
   r"!a b c x y z.
          ~(a = &0) /\ ~(b = &0) /\ ~(c = &0)
          ==> (coplanar {vec 0,a % x,b % y,c % z} <=> coplanar {vec 0,x,y,z})"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [COPLANAR_SPECIAL_SCALE] THEN
    ONCE_REWRITE_TAC [← SET_RULE (← q r"{a,b,c,d} = {a,c,d,b}")] THEN
    ASM_SIMP_TAC [COPLANAR_SPECIAL_SCALE] THEN
    ONCE_REWRITE_TAC [← SET_RULE (← q r"{a,b,c,d} = {a,c,d,b}")] THEN
    ASM_SIMP_TAC [COPLANAR_SPECIAL_SCALE])

  /- Specialized lemmas about "dropout". -/

  let DROPOUT_BASIS_3 ← prove
   r"(dropout 3:real^3->real^2) (basis 1) = basis 1 /\
     (dropout 3:real^3->real^2) (basis 2) = basis 2 /\
     (dropout 3:real^3->real^2) (basis 3) = vec 0"
   (SIMP_TAC [LAMBDA_BETA, dropout, basis, CART_EQ, DIMINDEX_2, DIMINDEX_3, ARITH,
             VEC_COMPONENT, LT_IMP_LE, ← ARITH_RULE (← q r"i <= 2 ==> i + 1 <= 3"),
             ← ARITH_RULE (← q r"1 <= i + 1")] THEN
    ARITH_TAC)

  let COLLINEAR_BASIS_3 ← prove
   r"collinear {vec 0,basis 3,x} <=> (dropout 3:real^3->real^2) x = vec 0"
   (SIMP_TAC [CART_EQ, FORALL_2, FORALL_3, DIMINDEX_2, DIMINDEX_3,
             dropout, LAMBDA_BETA, BASIS_COMPONENT, ARITH, REAL_MUL_RID,
             VECTOR_MUL_COMPONENT, VEC_COMPONENT, REAL_MUL_RZERO, UNWIND_THM1,
             COLLINEAR_LEMMA] THEN
    REWRITE_TAC [RIGHT_EXISTS_AND_THM, ← GSYM EXISTS_REFL] THEN REAL_ARITH_TAC)

  let OPEN_DROPOUT_3 ← prove
   r"!P. open {x | P x} ==> open {x | P((dropout 3:real^3->real^2) x)}"
   (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL
     [← q r"dropout 3:real^3->real^2", ← q r"{x:real^2 | P x}"]
     CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
    ASM_REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
    SIMP_TAC [LINEAR_DROPOUT, DIMINDEX_2, DIMINDEX_3, ARITH])

  let SLICE_DROPOUT_3 ← prove
   r"!P t. slice 3 t {x | P((dropout 3:real^3->real^2) x)} = {x | P x}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [slice] THEN
    REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM, IN_INTER] THEN
    X_GEN_TAC (← q r"y:real^2") THEN EQ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
    DISCH_TAC THEN EXISTS_TAC (← q r"(pushin 3 t:real^2->real^3) y") THEN
    ASM_SIMP_TAC [DIMINDEX_2, DIMINDEX_3, DROPOUT_PUSHIN, ARITH] THEN
    SIMP_TAC [pushin, LAMBDA_BETA, LT_REFL, DIMINDEX_3, ARITH])

  let NOT_COPLANAR_IMP_NOT_COLLINEAR_DROPOUT_3 ← prove
   r"!x y:real^3.
          ~coplanar {vec 0,basis 3, x, y}
          ==> ~collinear {vec 0,dropout 3 x:real^2,dropout 3 y}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [COLLINEAR_AFFINE_HULL, coplanar] THEN
    REWRITE_TAC [CONTRAPOS_THM, INSERT_SUBSET, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"u:real^2", ← q r"v:real^2"] THEN
    REWRITE_TAC [EMPTY_SUBSET] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC [AFFINE_HULL_EQ_SPAN] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [AFFINE_HULL_2]) THEN
    REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real", ← q r"b:real"] THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"?r s. a * r + b * s = -- &1") STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC (← q r"a = &0") THENL
       [UNDISCH_TAC (← q r"a + b = &1") THEN
        ASM_SIMP_TAC [REAL_MUL_LZERO, REAL_ADD_LID, REAL_MUL_LID, EXISTS_REFL],
        ASM_SIMP_TAC [← REAL_FIELD
         (← q r"~(a = &0) ==> (a * r + x = y <=> r = (y - x) / a)")] THEN
        MESON_TAC []],
      ALL_TAC] THEN
    EXISTS_TAC (← q r"vector[(u:real^2)$1; u$2; r]:real^3") THEN
    EXISTS_TAC (← q r"vector[(v:real^2)$1; v$2; s]:real^3") THEN
    EXISTS_TAC (← q r"basis 3:real^3") THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")) THEN CONJ_TAC THENL
     [REWRITE_TAC [AFFINE_HULL_3, IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY EXISTS_TAC [← q r"a / &2", ← q r"b / &2", ← q r"&1 / &2"] THEN
      ASM_REWRITE_TAC [← REAL_ARITH
        (← q r"a / &2 + b / &2 + &1 / &2 = &1 <=> a + b = &1")] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [CART_EQ]) THEN
      SIMP_TAC [CART_EQ, DIMINDEX_2, DIMINDEX_3, FORALL_2, FORALL_3,
               VEC_COMPONENT, VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT,
               VECTOR_3, BASIS_COMPONENT, ARITH] THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o SYM)) THEN CONV_TAC REAL_RING,
      ALL_TAC] THEN
    SIMP_TAC [AFFINE_HULL_EQ_SPAN] THEN DISCH_TAC THEN
    SIMP_TAC [SPAN_SUPERSET, IN_INSERT] THEN
    SUBGOAL_THEN
      (← q r"!x. (dropout 3:real^3->real^2) x IN span {u,v}
           ==> x IN span {vector [u$1; u$2; r], vector [v$1; v$2; s], basis 3}")
      (fun th => ASM_MESON_TAC [th]) THEN
    GEN_TAC THEN REWRITE_TAC [SPAN_2, SPAN_3] THEN
    SIMP_TAC [IN_ELIM_THM, IN_UNIV, CART_EQ, DIMINDEX_2, DIMINDEX_3,
             FORALL_2, FORALL_3, dropout, VECTOR_ADD_COMPONENT, LAMBDA_BETA,
             VECTOR_MUL_COMPONENT, VECTOR_3, BASIS_COMPONENT, ARITH] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"c:real") THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"d:real") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [REAL_MUL_RZERO, REAL_ADD_RID] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"x = a + b + c * &1 <=> c = x - a - b")] THEN
    REWRITE_TAC [EXISTS_REFL])

  let SLICE_312 ← prove
   r"!s:real^3->bool. slice 1 t s = {y:real^2 | vector[t;y$1;y$2] IN s}"
   (SIMP_TAC [EXTENSION, IN_SLICE, DIMINDEX_2, DIMINDEX_3, ARITH] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC [CART_EQ, pushin, LAMBDA_BETA, FORALL_3, DIMINDEX_3, ARITH,
             VECTOR_3])

  let SLICE_123 ← prove
   r"!s:real^3->bool. slice 3 t s = {y:real^2 | vector[y$1;y$2;t] IN s}"
   (SIMP_TAC [EXTENSION, IN_SLICE, DIMINDEX_2, DIMINDEX_3, ARITH] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC [CART_EQ, pushin, LAMBDA_BETA, FORALL_3, DIMINDEX_3, ARITH,
             VECTOR_3])

  /- "Padding" injection from real^2 -> real^3 with zero last coordinate. -/

  let pad2d3d ← new_definition
   r"(pad2d3d:real^2->real^3) x = lambda i. if i < 3 then x$i else &0"

  let FORALL_PAD2D3D_THM ← prove
   r"!P. (!y:real^3. y$3 = &0 ==> P y) <=> (!x. P(pad2d3d x))"
   (GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [pad2d3d] THEN
      SIMP_TAC [LAMBDA_BETA, DIMINDEX_3, ARITH, LT_REFL],
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(lambda i. (y:real^3)$i):real^2")) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      SIMP_TAC [CART_EQ, pad2d3d, DIMINDEX_3, ARITH, LAMBDA_BETA, DIMINDEX_2,
               ← ARITH_RULE (← q r"i < 3 <=> i <= 2")] THEN
      REWRITE_TAC [← ARITH_RULE (← q r"i <= 3 <=> i <= 2 \/ i = 3")] THEN
      ASM_MESON_TAC []])

  let QUANTIFY_PAD2D3D_THM ← prove
   r"(!P. (!y:real^3. y$3 = &0 ==> P y) <=> (!x. P(pad2d3d x))) /\
     (!P. (?y:real^3. y$3 = &0 /\ P y) <=> (?x. P(pad2d3d x)))"
   (REWRITE_TAC [← MESON [] (← q r"(?y. P y) <=> ~(!x. ~P x)")] THEN
    REWRITE_TAC [← GSYM FORALL_PAD2D3D_THM] THEN MESON_TAC [])

  let LINEAR_PAD2D3D ← prove
   r"linear pad2d3d"
   (REWRITE_TAC [linear, pad2d3d] THEN
    SIMP_TAC [CART_EQ, VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT,
             LAMBDA_BETA, DIMINDEX_2, DIMINDEX_3, ARITH,
             ← ARITH_RULE (← q r"i < 3 ==> i <= 2")] THEN
    REPEAT STRIP_TAC THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REAL_ARITH_TAC)

  let INJECTIVE_PAD2D3D ← prove
   r"!x y. pad2d3d x = pad2d3d y ==> x = y"
   (SIMP_TAC [CART_EQ, pad2d3d, LAMBDA_BETA, DIMINDEX_3, DIMINDEX_2] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"i < 3 <=> i <= 2")] THEN
    MESON_TAC [← ARITH_RULE (← q r"i <= 2 ==> i <= 3")])

  let NORM_PAD2D3D ← prove
   r"!x. norm(pad2d3d x) = norm x"
   (SIMP_TAC [NORM_EQ, DOT_2, DOT_3, pad2d3d, LAMBDA_BETA,
             DIMINDEX_2, DIMINDEX_3, ARITH] THEN
    REAL_ARITH_TAC)

  pure { NORM_CROSS_SIN, COPLANAR_INSERT_0_NEG, COPLANAR_IMP_NEGLIGIBLE,
         NOT_COPLANAR_0_4_IMP_INDEPENDENT, NOT_COPLANAR_NOT_COLLINEAR,
         SUBSET_AFFINE_HULL_SPECIAL_SCALE, COLLINEAR_SPECIAL_SCALE, COLLINEAR_SCALE_ALL,
         COPLANAR_SPECIAL_SCALE, COPLANAR_SCALE_ALL, DROPOUT_BASIS_3, COLLINEAR_BASIS_3,
         OPEN_DROPOUT_3, SLICE_DROPOUT_3, NOT_COPLANAR_IMP_NOT_COLLINEAR_DROPOUT_3,
         SLICE_312, SLICE_123, pad2d3d, FORALL_PAD2D3D_THM, QUANTIFY_PAD2D3D_THM,
         LINEAR_PAD2D3D, INJECTIVE_PAD2D3D, NORM_PAD2D3D }
/- ------------------------------------------------------------------------- -/
/- Apply 3D->2D conversion to a goal. Take care to preserve variable names.  -/
/- The notion of a plane, and using it to characterize coplanarity.          -/
/- (flyspeck.ml 272-604)                                                     -/
/- ------------------------------------------------------------------------- -/

structure FYB where
  PAD2D3D_QUANTIFY_CONV : ioconv
  PAD2D3D_TAC : tactic
  plane : thm
  PLANE_TRANSLATION_EQ : thm
  PLANE_TRANSLATION : thm
  PLANE_LINEAR_IMAGE_EQ : thm
  PLANE_LINEAR_IMAGE : thm
  AFFINE_PLANE : thm
  ROTATION_PLANE_HORIZONTAL : thm
  ROTATION_HORIZONTAL_PLANE : thm
  COPLANAR : thm
  COPLANAR_DET_EQ_0 : thm
  COPLANAR_CROSS_DOT : thm
  PLANE_AFFINE_HULL_3 : thm
  AFFINE_HULL_3_GENERATED : thm
  deriving Nonempty

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYB [HolBase] (D : FlyspeckDeps) (BFYA : FYA) : ExceptT String IO FYB := do
  -- @@SCOPE BEGIN
  let { INJECTIVE_PAD2D3D, LINEAR_PAD2D3D, NORM_PAD2D3D, QUANTIFY_PAD2D3D_THM, .. } := BFYA
  let { add_linear_invariants, ASM_MESON_TAC, MESON_TAC, new_definition, REAL_ARITH_TAC,
        REAL_RING, .. } := D.crd
  let { CROSS_TRIPLE, DOT_CROSS_DET, .. } := D.crs
  let { AFFINE_HULL_INSERT_SPAN, AFFINE_HULL_INSERT_SUBSET_SPAN, AFFINE_HULL_LINEAR_IMAGE,
        COLLINEAR_AFFINE_HULL_COLLINEAR, coplanar, .. } := D.qconvex
  let { DIM_INJECTIVE_LINEAR_IMAGE, INDEPENDENT_BOUND_GENERAL, LOWDIM_EXPAND_BASIS,
        RANK_ROW, SPAN_BREAKDOWN_EQ, SPAN_CARD_GE_DIM, SPAN_LINEAR_IMAGE, .. } := D.qvectors
  let { COLLINEAR_LINEAR_IMAGE_EQ, ORTHOGONAL_TRANSFORMATION_INVERSE,
        ROTATION_LOWDIM_HORIZONTAL, .. } := D.qdeterminants
  let { LINEAR_INVARIANTS, .. } := D.geominv
  let { COLLINEAR_3, .. } := D.gm.qvectors
  let { ARITH, CONJ_ASSOC, DIMINDEX_3, o_DEF, ORTHOGONAL_TRANSFORMATION_LINEAR, VECTOR_3,
        VECTOR_MUL_COMPONENT, VECTOR_SUB_EQ, .. } := D.crd.thms
  let { DET_EQ_0_RANK, .. } := D.gm.ra.ts.cn.ms.qdet
  let { add_translation_invariants, ARITH_RULE, ARITH_TAC, ASM_INT_ARITH_TAC,
        GEOM_TRANSLATE_TAC, HAS_SIZE_CONV, MESON, NUMSEG_CONV, SET_RULE, SET_TAC,
        VECTOR_ARITH, VECTOR_ARITH_TAC, .. } := D.gm.ra.ts.cn.cx.cvx
  let { CARD_CLAUSES, CONTRAPOS_THM, DE_MORGAN_THM, EMPTY_SUBSET, EQ_TRANS,
        EXISTS_IN_IMAGE, EXISTS_OR_THM, EXTENSION, FINITE_EMPTY, FINITE_INSERT,
        FINITE_RULES, .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, IMAGE_CLAUSES, IMAGE_ID, IMAGE_o, IMAGE_SUBSET, IMP_CONJ,
        IMP_CONJ_ALT, INSERT_AC, INSERT_SUBSET, INT_LE_SUB_RADD, INT_LE_TRANS,
        INT_OF_NUM_ADD, INT_OF_NUM_LE, .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_SING, IN_UNIV, LAMBDA_ETA, LE_REFL, LE_TRANS,
        LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, LET_TRANS, MONO_EXISTS, NOT_IN_EMPTY,
        .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { RIGHT_AND_EXISTS_THM, RIGHT_EXISTS_AND_THM, RIGHT_OR_DISTRIB, SIMPLE_IMAGE,
        SIMPLE_IMAGE_GEN, SUBSET, SUBSET_REFL, SUBSET_TRANS,
        .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { numseg, SUBSET_UNIV, UNWIND_THM2, .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { HULL_HULL, HULL_SUBSET, .. } := D.gm.ra.ts.cn.cx.cvx.misc
  let { COLLINEAR_2, COLLINEAR_LEMMA, DEPENDENT_EXPLICIT, DIM_EQ_SPAN, DIM_LE_CARD,
        DIM_SPAN, DIM_UNIV, .. } := D.gm.ra.ts.cn.cx.cvx.vec1
  let { DOT_SYM, INDEPENDENT_NONZERO, LINEAR_0, MATRIX_COMPOSE, MATRIX_ID,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec2
  let { SPAN_0, SPAN_EMPTY, SPAN_EQ_SELF, SPAN_INC, SPAN_MONO, SPAN_SUB, SPAN_SUPERSET,
        SPAN_UNIV, .. } := D.gm.ra.ts.cn.cx.cvx.vec3
  let { dependent, independent, row, rows, subspace, VEC_COMPONENT, VECTOR_ADD_COMPONENT,
        VECTOR_ADD_RID, VECTOR_ADD_SUB, VECTOR_ADD_SYM, VECTOR_SUB_ADD, VSUM_CLAUSES,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { DET_I, DET_MUL, ORTHOGONAL_TRANSFORMATION_INJECTIVE,
        .. } := D.gm.ra.ts.cn.cx.cvx.det
  let { SPAN_SPAN, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.qvec
  let { INT_NOT_LE, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qses
  let { AFF_DIM_AFFINE_HULL, AFF_DIM_EQ_AFFINE_HULL, AFF_DIM_LE_CARD, AFFINE_AFFINE_HULL,
        COLLINEAR_AFF_DIM, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qcvx1
  -- @@SCOPE END

  let PAD2D3D_QUANTIFY_CONV : ioconv ← do
    let gv ← HolCore.Basics.genvar (← qty "real^2")
    let pth ← CONV_RULE (BINOP_CONV (BINDER_CONV (RAND_CONV
                (fun t => pure (HolCore.Equal.GEN_ALPHA_CONV gv t)))))
                        QUANTIFY_PAD2D3D_THM
    let conv1 := GEN_REWRITE_CONV id [pth]
    let dest_quant (tm : term) : Except String (term × term) :=
      match HolCore.Basics.dest_forall tm with
      | .ok r => .ok r
      | .error _ => HolCore.Basics.dest_exists tm
    pure (fun tm => (do
      let th ← ExceptT.mk (conv1 tm)
      let name := (← liftExcept (dest_var (← liftExcept (dest_quant tm)).1)).1
      let ty := (← liftExcept (dest_var
                  (← liftExcept (dest_quant (← liftExcept (rand (concl th))))).1)).2
      CONV_RULE (RAND_CONV (fun t => pure (HolCore.Equal.GEN_ALPHA_CONV (mk_var name ty) t)))
        th : ExceptT String IO thm).run)

  let PAD2D3D_TAC : tactic ← do
    let pad2d3d_tm ← q r"pad2d3d"
    let pths := [LINEAR_PAD2D3D, INJECTIVE_PAD2D3D, NORM_PAD2D3D]
    let cth ← prove
     r"{} = IMAGE pad2d3d {} /\
       vec 0 = pad2d3d(vec 0)"
     (REWRITE_TAC [IMAGE_CLAUSES] THEN MESON_TAC [LINEAR_PAD2D3D, LINEAR_0])
    let lasttac :=
      GEN_REWRITE_TAC REDEPTH_CONV [← LINEAR_INVARIANTS pad2d3d_tm pths]
    pure (GEN_REWRITE_TAC ONCE_DEPTH_CONV [cth] THEN
          CONV_TAC (DEPTH_CONV PAD2D3D_QUANTIFY_CONV) THEN
          lasttac)

  /- The notion of a plane, and using it to characterize coplanarity. -/

  let plane ← new_definition
   r"plane x = (?u v w. ~(collinear {u,v,w}) /\ x = affine hull {u,v,w})"

  let PLANE_TRANSLATION_EQ ← prove
   r"!a:real^N s. plane(IMAGE (\x. a + x) s) <=> plane s"
   (REWRITE_TAC [plane] THEN GEOM_TRANSLATE_TAC [])

  let PLANE_TRANSLATION ← prove
   r"!a:real^N s. plane s ==> plane(IMAGE (\x. a + x) s)"
   (REWRITE_TAC [PLANE_TRANSLATION_EQ])

  add_translation_invariants [PLANE_TRANSLATION_EQ]

  let PLANE_LINEAR_IMAGE_EQ ← prove
   r"!f:real^M->real^N p.
          linear f /\ (!x y. f x = f y ==> x = y)
          ==> (plane(IMAGE f p) <=> plane p)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [plane] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     (← q r"?u. u IN IMAGE f (:real^M) /\
          ?v. v IN IMAGE f (:real^M) /\
              ?w. w IN IMAGE (f:real^M->real^N) (:real^M) /\
                  ~collinear {u, v, w} /\ IMAGE f p = affine hull {u, v, w}") THEN
    CONJ_TAC THENL
     [REWRITE_TAC [RIGHT_AND_EXISTS_THM, IN_IMAGE, IN_UNIV] THEN
      REPEAT (AP_TERM_TAC THEN ABS_TAC) THEN
      EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"{u,v,w} SUBSET IMAGE (f:real^M->real^N) p") MP_TAC THENL
       [ASM_REWRITE_TAC [HULL_SUBSET], SET_TAC []],
      REWRITE_TAC [EXISTS_IN_IMAGE, IN_UNIV] THEN
      REWRITE_TAC [← SET_RULE (← q r"{f a,f b,f c} = IMAGE f {a,b,c}")] THEN
      ASM_SIMP_TAC [AFFINE_HULL_LINEAR_IMAGE] THEN
      REPEAT (AP_TERM_TAC THEN ABS_TAC) THEN BINOP_TAC THENL
       [ASM_MESON_TAC [COLLINEAR_LINEAR_IMAGE_EQ], ASM SET_TAC []]])

  let PLANE_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N p.
          linear f /\ plane p /\ (!x y. f x = f y ==> x = y)
          ==> plane(IMAGE f p)"
   (MESON_TAC [PLANE_LINEAR_IMAGE_EQ])

  add_linear_invariants [PLANE_LINEAR_IMAGE_EQ]

  let AFFINE_PLANE ← prove
   r"!p. plane p ==> affine p"
   (SIMP_TAC [plane, LEFT_IMP_EXISTS_THM, AFFINE_AFFINE_HULL])

  let ROTATION_PLANE_HORIZONTAL ← (do
    let lemma ← prove
     r"span {z:real^3 | z$3 = &0} = {z:real^3 | z$3 = &0}"
     (REWRITE_TAC [SPAN_EQ_SELF, subspace, IN_ELIM_THM] THEN
      SIMP_TAC [VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, VEC_COMPONENT,
               DIMINDEX_3, ARITH] THEN REAL_ARITH_TAC)
    prove
     r"!s. plane s
           ==>  ?a f. orthogonal_transformation f /\ det(matrix f) = &1 /\
                      IMAGE f (IMAGE (\x. a + x) s) = {z:real^3 | z$3 = &0}"
      (REPEAT STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [plane]) THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"a:real^3", ← q r"b:real^3", ← q r"c:real^3"] THEN
      MAP_EVERY (fun t =>
        ASM_CASES_TAC t THENL [ASM_REWRITE_TAC [COLLINEAR_2, INSERT_AC],
                               ALL_TAC])
       [← q r"a:real^3 = b", ← q r"a:real^3 = c", ← q r"b:real^3 = c"] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
      ASM_SIMP_TAC [AFFINE_HULL_INSERT_SPAN, IN_INSERT, NOT_IN_EMPTY] THEN
      EXISTS_TAC (← q r"--a:real^3") THEN
      REWRITE_TAC [← SET_RULE (← q r"IMAGE (\x:real^3. --a + x) {a + x | x | x IN s} =
                            IMAGE (\x. --a + a + x) s")] THEN
      REWRITE_TAC [← VECTOR_ARITH (← q r"--a + a + x:real^3 = x"), IMAGE_ID] THEN
      REWRITE_TAC [← SET_RULE (← q r"{x - a:real^x | x = b \/ x = c} = {b - a,c - a}")] THEN
      MP_TAC (← ISPEC (← q r"span{b - a:real^3,c - a}")
        ROTATION_LOWDIM_HORIZONTAL) THEN
      REWRITE_TAC [DIMINDEX_3] THEN ANTS_TAC THENL
       [MATCH_MP_TAC LET_TRANS THEN
        EXISTS_TAC (← q r"CARD{b - a:real^3,c - a}") THEN
        SIMP_TAC [DIM_SPAN, DIM_LE_CARD, FINITE_RULES] THEN
        SIMP_TAC [CARD_CLAUSES, FINITE_RULES] THEN ARITH_TAC,
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f:real^3->real^3") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
      ASM_SIMP_TAC [← GSYM SPAN_LINEAR_IMAGE] THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM lemma] THEN
      MATCH_MP_TAC DIM_EQ_SPAN THEN CONJ_TAC THENL
       [ASM_MESON_TAC [IMAGE_SUBSET, SPAN_INC, SUBSET_TRANS], ALL_TAC] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"2") THEN CONJ_TAC THENL
       [MP_TAC (← ISPECL [← q r"{z:real^3 | z$3 = &0}", ← q r"(:real^3)"] DIM_EQ_SPAN) THEN
        REWRITE_TAC [SUBSET_UNIV, DIM_UNIV, DIMINDEX_3, lemma] THEN
        MATCH_MP_TAC (← TAUT (← q r"~r /\ (~p ==> q) ==> (q ==> r) ==> p")) THEN
        REWRITE_TAC [← ARITH_RULE (← q r"~(x <= 2) <=> 3 <= x")] THEN
        REWRITE_TAC [EXTENSION, SPAN_UNIV, IN_ELIM_THM] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"vector[&0;&0;&1]:real^3")) THEN
        REWRITE_TAC [IN_UNIV, VECTOR_3] THEN REAL_ARITH_TAC,
        ALL_TAC] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"dim {b - a:real^3,c - a}") THEN
      CONJ_TAC THENL
       [ALL_TAC, ASM_MESON_TAC [LE_REFL, DIM_INJECTIVE_LINEAR_IMAGE,
                 ORTHOGONAL_TRANSFORMATION_INJECTIVE]] THEN
      MP_TAC (← ISPEC (← q r"{b - a:real^3,c - a}") INDEPENDENT_BOUND_GENERAL) THEN
      SIMP_TAC [CARD_CLAUSES, FINITE_RULES, IN_SING, NOT_IN_EMPTY] THEN
      ASM_REWRITE_TAC [← VECTOR_ARITH (← q r"b - a:real^3 = c - a <=> b = c"), ARITH] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE (RAND_CONV o RAND_CONV)
        [← SET_RULE (← q r"{a,b,c} = {b,a,c}")]) THEN
      REWRITE_TAC [] THEN ONCE_REWRITE_TAC [COLLINEAR_3] THEN
      REWRITE_TAC [independent, CONTRAPOS_THM, dependent] THEN
      REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, RIGHT_OR_DISTRIB] THEN
      REWRITE_TAC [EXISTS_OR_THM, UNWIND_THM2] THEN
      ASM_SIMP_TAC [← SET_RULE (← q r"~(a = b) ==> {a,b} DELETE b = {a}"),
                   ← SET_RULE (← q r"~(a = b) ==> {a,b} DELETE a = {b}"),
                   ← VECTOR_ARITH (← q r"b - a:real^3 = c - a <=> b = c")] THEN
      REWRITE_TAC [SPAN_BREAKDOWN_EQ, SPAN_EMPTY, IN_SING] THEN
      ONCE_REWRITE_TAC [VECTOR_SUB_EQ] THEN MESON_TAC [COLLINEAR_LEMMA, INSERT_AC]))

  let ROTATION_HORIZONTAL_PLANE ← prove
   r"!p. plane p
         ==>  ?a f. orthogonal_transformation f /\ det(matrix f) = &1 /\
                    IMAGE (\x. a + x) (IMAGE f {z:real^3 | z$3 = &0}) = p"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP ROTATION_PLANE_HORIZONTAL) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"a:real^3")
     (X_CHOOSE_THEN (← q r"f:real^3->real^3") STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q r"g:real^3->real^3") STRIP_ASSUME_TAC o MATCH_MP
      ORTHOGONAL_TRANSFORMATION_INVERSE) THEN
    MAP_EVERY EXISTS_TAC [← q r"--a:real^3", ← q r"g:real^3->real^3"] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC [← GSYM IMAGE_o, o_DEF, IMAGE_ID,
                    ← VECTOR_ARITH (← q r"--a + a + x:real^3 = x")] THEN
    MATCH_MP_TAC (← REAL_RING (← q r"!f. f * g = &1 /\ f = &1 ==> g = &1")) THEN
    EXISTS_TAC (← q r"det(matrix(f:real^3->real^3))") THEN
    REWRITE_TAC [← GSYM DET_MUL] THEN
    ASM_SIMP_TAC [← GSYM MATRIX_COMPOSE, ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
    ASM_REWRITE_TAC [o_DEF, MATRIX_ID, DET_I])

  let COPLANAR ← prove
   r"2 <= dimindex(:N)
     ==> !s:real^N->bool. coplanar s <=> ?x. plane x /\ s SUBSET x"
   (DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC [coplanar, plane] THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [← MESON []
     (← q r"(?x u v w. p x u v w) <=> (?u v w x. p x u v w)")] THEN
    REWRITE_TAC [← GSYM CONJ_ASSOC, RIGHT_EXISTS_AND_THM, UNWIND_THM2] THEN
    EQ_TAC THENL [MESON_TAC [], REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [← q r"u:real^N", ← q r"v:real^N", ← q r"w:real^N"] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"s SUBSET {u + x:real^N | x | x IN span {y - u | y IN {v,w}}}")
    MP_TAC THENL
     [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
       (← REWRITE_RULE [IMP_CONJ] SUBSET_TRANS)) THEN
      REWRITE_TAC [AFFINE_HULL_INSERT_SUBSET_SPAN],
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
    DISCH_THEN (MP_TAC o ISPEC (← q r"\x:real^N. x - u") o MATCH_MP IMAGE_SUBSET) THEN
    REWRITE_TAC [← GSYM IMAGE_o, o_DEF, VECTOR_ADD_SUB, IMAGE_ID, SIMPLE_IMAGE] THEN
    REWRITE_TAC [IMAGE_CLAUSES] THEN
    MP_TAC (← ISPECL [← q r"{v - u:real^N,w - u}", ← q r"2"] LOWDIM_EXPAND_BASIS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC (← q r"CARD{v - u:real^N,w - u}") THEN
      SIMP_TAC [DIM_LE_CARD, FINITE_INSERT, FINITE_RULES] THEN
      SIMP_TAC [CARD_CLAUSES, FINITE_RULES] THEN ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:real^N->bool")
     (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
    CONV_TAC (LAND_CONV HAS_SIZE_CONV) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"b:real^N"] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
    UNDISCH_TAC (← q r"span {v - u, w - u} SUBSET span {a:real^N, b}") THEN
    REWRITE_TAC [← GSYM IMP_CONJ_ALT] THEN
    DISCH_THEN (ASSUME_TAC o MATCH_MP SUBSET_TRANS) THEN
    MAP_EVERY EXISTS_TAC [← q r"u:real^N", ← q r"u + a:real^N", ← q r"u + b:real^N"] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [COLLINEAR_3, COLLINEAR_LEMMA,
                  ← VECTOR_ARITH (← q r"--x = vec 0 <=> x = vec 0"),
                  ← VECTOR_ARITH (← q r"u - (u + a):real^N = --a"),
                  ← VECTOR_ARITH (← q r"(u + b) - (u + a):real^N = b - a")] THEN
      REWRITE_TAC [DE_MORGAN_THM, VECTOR_SUB_EQ,
        ← VECTOR_ARITH (← q r"b - a = c % -- a <=> (c - &1) % a + &1 % b = vec 0")] THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [ASM_MESON_TAC [IN_INSERT, INDEPENDENT_NONZERO], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"u:real")) THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [independent]) THEN
      REWRITE_TAC [DEPENDENT_EXPLICIT] THEN
      MAP_EVERY EXISTS_TAC [← q r"{a:real^N,b}",
                            ← q r"\x:real^N. if x = a then u - &1 else &1"] THEN
      REWRITE_TAC [FINITE_INSERT, FINITE_RULES, SUBSET_REFL] THEN
      CONJ_TAC THENL
       [EXISTS_TAC (← q r"b:real^N") THEN ASM_REWRITE_TAC [IN_INSERT] THEN
        REAL_ARITH_TAC,
        ALL_TAC] THEN
      SIMP_TAC [VSUM_CLAUSES, FINITE_RULES] THEN
      ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, VECTOR_ADD_RID],
      ALL_TAC] THEN
    W (MP_TAC o PART_MATCH (lhs o rand) AFFINE_HULL_INSERT_SPAN o rand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
      REWRITE_TAC [← VECTOR_ARITH (← q r"u = u + a <=> a = vec 0")] THEN
      ASM_MESON_TAC [INDEPENDENT_NONZERO, IN_INSERT],
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM (MP_TAC o ISPEC (← q r"\x:real^N. u + x") o MATCH_MP IMAGE_SUBSET) THEN
    REWRITE_TAC [← GSYM IMAGE_o, o_DEF, IMAGE_ID,
                ← ONCE_REWRITE_RULE [VECTOR_ADD_SYM] VECTOR_SUB_ADD] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] SUBSET_TRANS) THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
    REWRITE_TAC [SIMPLE_IMAGE, IMAGE_CLAUSES, VECTOR_ADD_SUB] THEN
    SET_TAC [])

  let COPLANAR_DET_EQ_0 ← prove
   r"!v0 v1 (v2: real^3) v3.
          coplanar {v0,v1,v2,v3} <=>
          det(vector[v1 - v0; v2 - v0; v3 - v0]) = &0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [DET_EQ_0_RANK, RANK_ROW] THEN
    REWRITE_TAC [rows, row, LAMBDA_ETA] THEN
    ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC [← GSYM numseg, DIMINDEX_3] THEN
    CONV_TAC (ONCE_DEPTH_CONV NUMSEG_CONV) THEN
    SIMP_TAC [IMAGE_CLAUSES, coplanar, VECTOR_3] THEN EQ_TAC THENL
     [REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"a:real^3", ← q r"b:real^3", ← q r"c:real^3"] THEN
      W (MP_TAC o PART_MATCH lhand AFFINE_HULL_INSERT_SUBSET_SPAN o
          rand o lhand o snd) THEN
      REWRITE_TAC [← GSYM IMP_CONJ_ALT] THEN
      DISCH_THEN (MP_TAC o MATCH_MP SUBSET_TRANS) THEN
      DISCH_THEN (MP_TAC o ISPEC (← q r"\x:real^3. x - a") o MATCH_MP IMAGE_SUBSET) THEN
      ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
      REWRITE_TAC [IMAGE_CLAUSES, ← GSYM IMAGE_o, o_DEF, VECTOR_ADD_SUB, IMAGE_ID,
                  SIMPLE_IMAGE] THEN
      REWRITE_TAC [INSERT_SUBSET] THEN STRIP_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM DIM_SPAN] THEN MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC (← q r"CARD {b - a:real^3,c - a}") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SPAN_CARD_GE_DIM,
        SIMP_TAC [CARD_CLAUSES, FINITE_RULES] THEN ARITH_TAC] THEN
      REWRITE_TAC [FINITE_INSERT, FINITE_RULES] THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM SPAN_SPAN] THEN
      MATCH_MP_TAC SPAN_MONO THEN REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET] THEN
      MP_TAC (← VECTOR_ARITH (← q r"!x y:real^3. x - y = (x - a) - (y - a)")) THEN
      DISCH_THEN (fun th => REPEAT CONJ_TAC THEN
        GEN_REWRITE_TAC LAND_CONV [th]) THEN
      MATCH_MP_TAC SPAN_SUB THEN ASM_REWRITE_TAC [],
      DISCH_TAC THEN
      MP_TAC (← ISPECL [← q r"{v1 - v0,v2 - v0,v3 - v0}:real^3->bool", ← q r"2"]
                    LOWDIM_EXPAND_BASIS) THEN
      ASM_REWRITE_TAC [← ARITH_RULE (← q r"n <= 2 <=> n < 3"), DIMINDEX_3, ARITH] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"t:real^3->bool")
       (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
      CONV_TAC (LAND_CONV HAS_SIZE_CONV) THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"a:real^3", ← q r"b:real^3"] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
      SIMP_TAC [COPLANAR, DIMINDEX_3, ARITH, plane] THEN
      MAP_EVERY EXISTS_TAC [← q r"v0:real^3", ← q r"v0 + a:real^3", ← q r"v0 + b:real^3"] THEN
      W (MP_TAC o PART_MATCH (lhs o rand) AFFINE_HULL_INSERT_SPAN o
        rand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
        REWRITE_TAC [← VECTOR_ARITH (← q r"u = u + a <=> a = vec 0")] THEN
        ASM_MESON_TAC [INDEPENDENT_NONZERO, IN_INSERT],
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
      REWRITE_TAC [SIMPLE_IMAGE, IMAGE_CLAUSES, IMAGE_ID, VECTOR_ADD_SUB] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
       (← q r"IMAGE (\v:real^3. v0 + v) (span{v1 - v0, v2 - v0, v3 - v0})") THEN
      ASM_SIMP_TAC [IMAGE_SUBSET] THEN
      REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET, IN_IMAGE] THEN CONJ_TAC THENL
       [EXISTS_TAC (← q r"vec 0:real^3") THEN REWRITE_TAC [SPAN_0] THEN VECTOR_ARITH_TAC,
        REWRITE_TAC [← VECTOR_ARITH (← q r"v1:real^N = v0 + x <=> x = v1 - v0")] THEN
        REWRITE_TAC [UNWIND_THM2] THEN REPEAT CONJ_TAC THEN
        MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC [IN_INSERT]]])

  let COPLANAR_CROSS_DOT ← prove
   r"!v w x y. coplanar {v,w,x,y} <=> ((w - v) cross (x - v)) dot (y - v) = &0"
   (REWRITE_TAC [COPLANAR_DET_EQ_0, ← GSYM DOT_CROSS_DET] THEN
    MESON_TAC [CROSS_TRIPLE, DOT_SYM])

  let PLANE_AFFINE_HULL_3 ← prove
   r"!a b c:real^N. plane(affine hull {a,b,c}) <=> ~collinear{a,b,c}"
   (REWRITE_TAC [plane] THEN MESON_TAC [COLLINEAR_AFFINE_HULL_COLLINEAR])

  let AFFINE_HULL_3_GENERATED ← prove
   r"!s u v w:real^N.
          s SUBSET affine hull {u,v,w} /\ ~collinear s
          ==> affine hull {u,v,w} = affine hull s"
   (REWRITE_TAC [COLLINEAR_AFF_DIM, INT_NOT_LE] THEN REPEAT STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM HULL_HULL] THEN
    MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC (← q r"&2:int") THEN
    CONJ_TAC THENL [ALL_TAC, ASM_INT_ARITH_TAC] THEN
    REWRITE_TAC [AFF_DIM_AFFINE_HULL] THEN
    W (MP_TAC o PART_MATCH (lhand o rand) AFF_DIM_LE_CARD o lhand o snd) THEN
    REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] INT_LE_TRANS) THEN
    REWRITE_TAC [INT_LE_SUB_RADD, INT_OF_NUM_ADD, INT_OF_NUM_LE] THEN
    SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY] THEN ARITH_TAC)

  pure { PAD2D3D_QUANTIFY_CONV, PAD2D3D_TAC, plane, PLANE_TRANSLATION_EQ,
         PLANE_TRANSLATION, PLANE_LINEAR_IMAGE_EQ, PLANE_LINEAR_IMAGE, AFFINE_PLANE,
         ROTATION_PLANE_HORIZONTAL, ROTATION_HORIZONTAL_PLANE, COPLANAR,
         COPLANAR_DET_EQ_0, COPLANAR_CROSS_DOT, PLANE_AFFINE_HULL_3,
         AFFINE_HULL_3_GENERATED }
/- ------------------------------------------------------------------------- -/
/- Additional WLOG tactic to rotate any plane p to {z | z$3 = &0}.           -/
/- Affsign and its special cases, with invariance theorems.                  -/
/- (flyspeck.ml 605-918)                                                     -/
/- ------------------------------------------------------------------------- -/

structure FYC where
  GEOM_HORIZONTAL_PLANE_RULE : term → ExceptT String IO thm
  GEOM_HORIZONTAL_PLANE_TAC : term → tactic
  lin_combo : thm
  affsign : thm
  sgn_gt : thm
  sgn_ge : thm
  sgn_lt : thm
  sgn_le : thm
  aff_gt_def : thm
  aff_ge_def : thm
  aff_lt_def : thm
  aff_le_def : thm
  AFFSIGN : thm
  AFFSIGN_ALT : thm
  IN_AFFSIGN : thm
  AFFSIGN_DISJOINT_DIFF : thm
  AFF_GE_DISJOINT_DIFF : thm
  AFFSIGN_INJECTIVE_LINEAR_IMAGE : thm
  AFF_GE_INJECTIVE_LINEAR_IMAGE : thm
  AFF_GT_INJECTIVE_LINEAR_IMAGE : thm
  AFF_LE_INJECTIVE_LINEAR_IMAGE : thm
  AFF_LT_INJECTIVE_LINEAR_IMAGE : thm
  IN_AFFSIGN_TRANSLATION : thm
  AFFSIGN_TRANSLATION : thm
  AFF_GE_TRANSLATION : thm
  AFF_GT_TRANSLATION : thm
  AFF_LE_TRANSLATION : thm
  AFF_LT_TRANSLATION : thm
  deriving Nonempty

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYC [HolBase] (D : FlyspeckDeps) (BFYB : FYB) : ExceptT String IO FYC := do
  -- @@SCOPE BEGIN
  let { ROTATION_HORIZONTAL_PLANE, .. } := BFYB
  let { EXPAND_QUANTS_CONV, .. } := D
  let { add_linear_invariants, ASM_MESON_TAC, MESON_TAC, new_definition, .. } := D.crd
  let { ORTHOGONAL_TRANSFORMATION_SURJECTIVE, .. } := D.qdeterminants
  let { ITERATE_EXPAND_CASES, .. } := D.qsession
  let { LINEAR_INVARIANTS, TRANSLATION_INVARIANTS, .. } := D.geominv
  let { EXISTS_GENVAR_RULE, .. } := D.geomorigin
  let { MONO_FORALL, o_DEF, ORTHOGONAL_TRANSFORMATION, ORTHOGONAL_TRANSFORMATION_LINEAR,
        VECTOR_MUL_LID, .. } := D.crd.thms
  let { add_translation_invariants, MESON, SET_RULE, SET_TAC, VECTOR_ARITH,
        VECTOR_ARITH_TAC, .. } := D.gm.ra.ts.cn.cx.cvx
  let { ARITH_EQ, EQ_TRANS, ETA_AX, EXTENSION, .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, FUN_EQ_THM, IMAGE, IMAGE_CLAUSES, IMAGE_ID, IMAGE_o, IMAGE_UNION,
        IMP_CONJ, IN, .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { I_THM, IN_ELIM_THM, IN_IMAGE, NEUTRAL_REAL_ADD, .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_OF_NUM_EQ, SUBSET, SUBSET_ANTISYM, .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { o_THM, sum, SUM_IMAGE, SUM_SUPERSET, support, .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { LINEAR_CMUL, LINEAR_INJECTIVE_LEFT_INVERSE, LINEAR_VSUM,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec2
  let { VECTOR_ADD_LDISTRIB, VECTOR_ADD_SUB, VECTOR_MUL_EQ_0, VECTOR_MUL_LZERO, VSUM_ADD,
        VSUM_IMAGE, VSUM_RMUL, VSUM_SUPERSET, .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { ORTHOGONAL_TRANSFORMATION_INJECTIVE, .. } := D.gm.ra.ts.cn.cx.cvx.det
  let { QUANTIFY_SURJECTION_THM, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qvec
  -- @@SCOPE END
  let { FORALL_SIMP, .. } := HolBase.T

  let GEOM_HORIZONTAL_PLANE_RULE : term → ExceptT String IO thm ← do
    let ifn := MATCH_MP
     (← TAUT (← q r"(p ==> (x <=> x')) /\ (~p ==> (x <=> T)) ==> (x' ==> x)"))
    let pth ← prove
     r"!a f. orthogonal_transformation (f:real^N->real^N)
             ==> ((!P. (!x. P x) <=> (!x. P (a + f x))) /\
                  (!P. (?x. P x) <=> (?x. P (a + f x))) /\
                  (!Q. (!s. Q s) <=> (!s. Q (IMAGE (\x. a + x) (IMAGE f s)))) /\
                  (!Q. (?s. Q s) <=> (?s. Q (IMAGE (\x. a + x) (IMAGE f s))))) /\
                 (!P. {x | P x} =
                      IMAGE (\x. a + x) (IMAGE f {x | P(a + f x)}))"
     (REPEAT GEN_TAC THEN DISCH_TAC THEN
      MP_TAC (← ISPEC (← q r"(\x. a + x) o (f:real^N->real^N)")
        QUANTIFY_SURJECTION_THM) THEN REWRITE_TAC [o_THM, IMAGE_o] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION_SURJECTIVE,
                     ← VECTOR_ARITH (← q r"a + (x - a:real^N) = x")])
    let cth ← prove
     r"!a f. {} = IMAGE (\x:real^3. a + x) (IMAGE f {})"
     (REWRITE_TAC [IMAGE_CLAUSES])
    let oth ← prove
     r"!f:real^3->real^3.
          orthogonal_transformation f /\ det(matrix f) = &1
          ==> linear f /\
              (!x y. f x = f y ==> x = y) /\
              (!y. ?x. f x = y) /\
              (!x. norm(f x) = norm x) /\
              (2 <= dimindex(:3) ==> det(matrix f) = &1)"
     (GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC [ORTHOGONAL_TRANSFORMATION_LINEAR],
        ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION_INJECTIVE],
        ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION_SURJECTIVE],
        ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION]])
    let fth ← MESON []
     (← q r"(!a f. q a f ==> (p <=> p' a f))
      ==> ((?a f. q a f) ==> (p <=> !a f. q a f ==> p' a f))")
    pure (fun tm => do
      let (x, bod) ← liftExcept (HolCore.Basics.dest_forall tm)
      let th1 ← EXISTS_GENVAR_RULE
        (← UNDISCH (← ISPEC x ROTATION_HORIZONTAL_PLANE))
      let (a, f, tm1) ← match HolCore.Basics.strip_exists (concl th1) with
        | ([a, f], tm1) => pure (a, f, tm1)
        | _ => throw "GEOM_HORIZONTAL_PLANE_RULE: match failure"
      let (th_orth, th_det, th_im) ← match CONJUNCTS (← ASSUME tm1) with
        | [t1, t2, t3] => pure (t1, t2, t3)
        | _ => throw "GEOM_HORIZONTAL_PLANE_RULE: match failure"
      let th2 ← PROVE_HYP th_orth (← UNDISCH (← ISPECL [a, f] pth))
      let th3 ← ExceptT.mk (((← EXPAND_QUANTS_CONV (← ASSUME (concl th2))) THENC
                 SUBS_CONV [← GSYM th_im, ← ISPECL [a, f] cth]) bod)
      let th4 ← PROVE_HYP th2 th3
      let th5 ← TRANSLATION_INVARIANTS a
      let th6 ← GEN_REWRITE_RULE (RAND_CONV o REDEPTH_CONV)
                  [← ASSUME (concl th5)] th4
      let th7 ← PROVE_HYP th5 th6
      let th8s := CONJUNCTS (← MATCH_MP oth (← CONJ th_orth th_det))
      let th9 ← LINEAR_INVARIANTS f th8s
      let th10 ← GEN_REWRITE_RULE (RAND_CONV o REDEPTH_CONV) [th9] th7
      let th11 ← if (intersect (frees (concl th10)) [a, f]).isEmpty
                 then do PROVE_HYP th1 (← HolMultiLib.Determinants.itlistIO SIMPLE_CHOOSE [a, f] th10)
                 else do MP (← MATCH_MP fth (← GENL [a, f] (← DISCH_ALL th10))) th1
      let h ← match hyp th11 with
        | h :: _ => pure h
        | [] => throw "hd"
      let th12 ← ExceptT.mk (REWRITE_CONV [← ASSUME (← liftExcept (HolCore.Bool.mk_neg h))] bod)
      let th13 ← ifn (← CONJ (← DISCH_ALL th11) (← DISCH_ALL th12))
      let th14 ← MATCH_MP MONO_FORALL (← GEN x th13)
      GEN_REWRITE_RULE (fun c => TRY_CONV (LAND_CONV c)) [FORALL_SIMP] th14)

  let GEOM_HORIZONTAL_PLANE_TAC (p : term) : tactic :=
    W (fun (asl, w) =>
          let (_avs, _bod) := HolCore.Basics.strip_forall w
          let avs' := subtract (frees w) (freesl (asl.map (fun (_, th) => concl th)))
          let (avs, _bod) := HolCore.Basics.strip_forall w
          MAP_EVERY X_GEN_TAC avs THEN
          MAP_EVERY (fun t => SPEC_TAC (t, t)) (subtract (avs ++ avs') [p]).reverse THEN
          SPEC_TAC (p, p) THEN
          W (MATCH_MP_TAC o GEOM_HORIZONTAL_PLANE_RULE o snd))

  /- Affsign and its special cases, with invariance theorems. -/

  let lin_combo ← new_definition
   r"lin_combo V f = vsum V (\v. f v % (v:real^N))"

  let affsign ← new_definition
   r"affsign sgn s t (v:real^A) <=>
       (?f. (v = lin_combo (s UNION t) f) /\
            (!w. t w ==> sgn (f w)) /\
            (sum (s UNION t) f = &1))"

  let sgn_gt ← new_definition r"sgn_gt = (\t. (&0 < t))"
  let sgn_ge ← new_definition r"sgn_ge = (\t. (&0 <= t))"
  let sgn_lt ← new_definition r"sgn_lt = (\t. (t < &0))"
  let sgn_le ← new_definition r"sgn_le = (\t. (t <= &0))"

  let aff_gt_def ← new_definition r"aff_gt = affsign sgn_gt"
  let aff_ge_def ← new_definition r"aff_ge = affsign sgn_ge"
  let aff_lt_def ← new_definition r"aff_lt = affsign sgn_lt"
  let aff_le_def ← new_definition r"aff_le = affsign sgn_le"

  let AFFSIGN ← prove
   r"affsign sgn s t =
          {y | ?f. y = vsum (s UNION t) (\v. f v % v) /\
                  (!w. w IN t ==> sgn(f w)) /\
                  sum (s UNION t) f = &1}"
   (REWRITE_TAC [FUN_EQ_THM, affsign, lin_combo, IN_ELIM_THM] THEN
    REWRITE_TAC [IN])

  let AFFSIGN_ALT ← prove
   r"affsign sgn s t =
          {y | ?f. (!w. w IN (s UNION t) ==> w IN t ==> sgn(f w)) /\
                   sum (s UNION t) f = &1 /\
                   vsum (s UNION t) (\v. f v % v) = y}"
   (REWRITE_TAC [← SET_RULE (← q r"(w IN (s UNION t) ==> w IN t ==> P w) <=>
                          (w IN t ==> P w)")] THEN
    REWRITE_TAC [AFFSIGN, EXTENSION, IN_ELIM_THM] THEN MESON_TAC [])

  let IN_AFFSIGN ← prove
   r"y IN affsign sgn s t <=>
          ?u. (!x. x IN t ==> sgn(u x)) /\
              sum (s UNION t) u = &1 /\
              vsum (s UNION t) (\x. u(x) % x) = y"
   (REWRITE_TAC [AFFSIGN, IN_ELIM_THM] THEN SET_TAC [])

  let AFFSIGN_DISJOINT_DIFF ← prove
   r"!s t. affsign sgn s t = affsign sgn (s DIFF t) t"
   (REWRITE_TAC [AFFSIGN, ← SET_RULE (← q r"(s DIFF t) UNION t = s UNION t")])

  let AFF_GE_DISJOINT_DIFF ← prove
   r"!s t. aff_ge s t = aff_ge (s DIFF t) t"
   (REWRITE_TAC [aff_ge_def] THEN MATCH_ACCEPT_TAC AFFSIGN_DISJOINT_DIFF)

  let AFFSIGN_INJECTIVE_LINEAR_IMAGE ← (do
    let lemma0 ← prove
     r"vsum s (\x. u x % x) = vsum {x | x IN s /\ ~(u x = &0)} (\x. u x % x)"
     (MATCH_MP_TAC VSUM_SUPERSET THEN SIMP_TAC [SUBSET, IN_ELIM_THM] THEN
      REWRITE_TAC [← TAUT (← q r"p /\ ~(p /\ ~q) <=> p /\ q")] THEN
      SIMP_TAC [o_THM, VECTOR_MUL_LZERO])
    let lemma1 ← prove
     r"!f:real^M->real^N s.
             linear f /\ (!x y. f x = f y ==> x = y)
             ==> (sum(IMAGE f s) u = &1 /\ vsum(IMAGE f s) (\x. u x % x) = y <=>
                  sum s (u o f) = &1 /\ f(vsum s (\x. (u o f) x % x)) = y)"
     (REPEAT STRIP_TAC THEN
      W (MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE o funpowM 3 lhand o snd) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC (← MESON [] (← q r"(p ==> z = x) ==> (p /\ x = y <=> p /\ z = y)")) THEN
      DISCH_TAC THEN ONCE_REWRITE_TAC [lemma0] THEN
      SUBGOAL_THEN
       (← q r"{y | y IN IMAGE (f:real^M->real^N) s /\ ~(u y = &0)} =
        IMAGE f {x | x IN s /\ ~(u(f x) = &0)}")
      SUBST1_TAC THENL [ASM SET_TAC [], CONV_TAC SYM_CONV] THEN
      SUBGOAL_THEN (← q r"FINITE {x | x IN s /\ ~(u((f:real^M->real^N) x) = &0)}")
      ASSUME_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE
         (LAND_CONV o RATOR_CONV o RATOR_CONV) [sum]) THEN
        ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES] THEN
        REWRITE_TAC [← GSYM sum, support, NEUTRAL_REAL_ADD, o_THM] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_OF_NUM_EQ, ARITH_EQ],
        W (MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhand o snd) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [o_DEF] THEN
        ASM_SIMP_TAC [LINEAR_VSUM, o_DEF, ← GSYM LINEAR_CMUL]])
    prove
     r"!f:real^M->real^N sgn s t v.
          linear f /\ (!x y. f x = f y ==> x = y)
          ==> (affsign sgn (IMAGE f s) (IMAGE f t) =
               IMAGE f (affsign sgn s t))"
      (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [EXTENSION, IN_AFFSIGN] THEN
      REWRITE_TAC [FORALL_IN_IMAGE] THEN REWRITE_TAC [IN_IMAGE, IN_AFFSIGN] THEN
      REWRITE_TAC [← GSYM IMAGE_UNION] THEN
      FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP lemma1 th])) THEN
      X_GEN_TAC (← q r"y:real^N") THEN EQ_TAC THENL
       [DISCH_THEN (X_CHOOSE_THEN (← q r"u:real^N->real") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"vsum (s UNION t) (\x. (u o (f:real^M->real^N)) x % x)") THEN
        ASM_REWRITE_TAC [] THEN
        EXISTS_TAC (← q r"(u:real^N->real) o (f:real^M->real^N)") THEN
        ASM_REWRITE_TAC [] THEN ASM_REWRITE_TAC [o_THM],
        MP_TAC (← ISPEC (← q r"f:real^M->real^N") LINEAR_INJECTIVE_LEFT_INVERSE) THEN
        ASM_REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->real^M") STRIP_ASSUME_TAC) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"x:real^M")
         (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"u:real^M->real") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"(u:real^M->real) o (g:real^N->real^M)") THEN
        ASM_REWRITE_TAC [o_DEF, ETA_AX]]))

  let AFF_GE_INJECTIVE_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N s t.
          linear f /\ (!x y. f x = f y ==> x = y)
          ==> aff_ge (IMAGE f s) (IMAGE f t) = IMAGE f (aff_ge s t)"
   (REWRITE_TAC [aff_ge_def, AFFSIGN_INJECTIVE_LINEAR_IMAGE])

  let AFF_GT_INJECTIVE_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N s t.
          linear f /\ (!x y. f x = f y ==> x = y)
          ==> aff_gt (IMAGE f s) (IMAGE f t) = IMAGE f (aff_gt s t)"
   (REWRITE_TAC [aff_gt_def, AFFSIGN_INJECTIVE_LINEAR_IMAGE])

  let AFF_LE_INJECTIVE_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N s t.
          linear f /\ (!x y. f x = f y ==> x = y)
          ==> aff_le (IMAGE f s) (IMAGE f t) = IMAGE f (aff_le s t)"
   (REWRITE_TAC [aff_le_def, AFFSIGN_INJECTIVE_LINEAR_IMAGE])

  let AFF_LT_INJECTIVE_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N s t.
          linear f /\ (!x y. f x = f y ==> x = y)
          ==> aff_lt (IMAGE f s) (IMAGE f t) = IMAGE f (aff_lt s t)"
   (REWRITE_TAC [aff_lt_def, AFFSIGN_INJECTIVE_LINEAR_IMAGE])

  add_linear_invariants
    [AFFSIGN_INJECTIVE_LINEAR_IMAGE,
     AFF_GE_INJECTIVE_LINEAR_IMAGE,
     AFF_GT_INJECTIVE_LINEAR_IMAGE,
     AFF_LE_INJECTIVE_LINEAR_IMAGE,
     AFF_LT_INJECTIVE_LINEAR_IMAGE]

  let IN_AFFSIGN_TRANSLATION ← prove
   r"!sgn s t a v:real^N.
          affsign sgn s t v
          ==> affsign sgn (IMAGE (\x. a + x) s) (IMAGE (\x. a + x) t) (a + v)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [affsign, lin_combo] THEN
    ONCE_REWRITE_TAC [← SET_RULE (← q r"(!x. s x ==> p x) <=> (!x. x IN s ==> p x)")] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"f:real^N->real")
     (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC (← q r"\x. (f:real^N->real)(x - a)") THEN
    ASM_REWRITE_TAC [← GSYM IMAGE_UNION] THEN REPEAT CONJ_TAC THENL
     [ALL_TAC,
      ASM_REWRITE_TAC [FORALL_IN_IMAGE, ETA_AX,
                      ← VECTOR_ARITH (← q r"(a + x) - a:real^N = x")],
      W (MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE o lhs o snd) THEN
      SIMP_TAC [← VECTOR_ARITH (← q r"a + x:real^N = a + y <=> x = y")] THEN
      ASM_REWRITE_TAC [o_DEF, VECTOR_ADD_SUB, ETA_AX]] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     (← q r"a + vsum {x | x IN s UNION t /\ ~(f x = &0)} (\v:real^N. f v % v)") THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC VSUM_SUPERSET THEN
      REWRITE_TAC [VECTOR_MUL_EQ_0, SUBSET, IN_ELIM_THM] THEN MESON_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"vsum (IMAGE (\x:real^N. a + x)
                            {x | x IN s UNION t /\ ~(f x = &0)})
                     (\v. f(v - a) % v)") THEN
    CONJ_TAC THENL
     [ALL_TAC,
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
      CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
      ASM_REWRITE_TAC [IMP_CONJ, FORALL_IN_IMAGE, VECTOR_MUL_EQ_0] THEN
      REWRITE_TAC [VECTOR_ADD_SUB] THEN SET_TAC []] THEN
    SUBGOAL_THEN (← q r"FINITE {x:real^N | x IN s UNION t /\ ~(f x = &0)}")
    ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE
       (LAND_CONV o RATOR_CONV o RATOR_CONV) [sum]) THEN
      ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES] THEN
      REWRITE_TAC [← GSYM sum, support, NEUTRAL_REAL_ADD] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_OF_NUM_EQ, ARITH_EQ],
      ALL_TAC] THEN
    W (MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o rhs o snd) THEN
    ASM_SIMP_TAC [← VECTOR_ARITH (← q r"a + x:real^N = a + y <=> x = y")] THEN
    DISCH_THEN (K ALL_TAC : thm → tactic) THEN REWRITE_TAC [o_DEF, VECTOR_ADD_SUB] THEN
    ASM_SIMP_TAC [VECTOR_ADD_LDISTRIB, VSUM_ADD] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [VSUM_RMUL] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM VECTOR_MUL_LID] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUM_SUPERSET THEN SET_TAC [])

  let AFFSIGN_TRANSLATION ← prove
   r"!a:real^N sgn s t.
          affsign sgn (IMAGE (\x. a + x) s) (IMAGE (\x. a + x) t) =
          IMAGE (\x. a + x) (affsign sgn s t)"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC [SUBSET, IN] THEN GEN_TAC THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"--a:real^N") o
        MATCH_MP IN_AFFSIGN_TRANSLATION) THEN
      REWRITE_TAC [← GSYM IMAGE_o, o_DEF, ← VECTOR_ARITH (← q r"--a + a + x:real^N = x"),
                  IMAGE_ID] THEN
      DISCH_TAC THEN REWRITE_TAC [IMAGE, IN_ELIM_THM] THEN
      EXISTS_TAC (← q r"--a + x:real^N") THEN ASM_REWRITE_TAC [IN] THEN VECTOR_ARITH_TAC,
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN GEN_TAC THEN REWRITE_TAC [IN] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"a:real^N") o MATCH_MP IN_AFFSIGN_TRANSLATION) THEN
      REWRITE_TAC []])

  let AFF_GE_TRANSLATION ← prove
   r"!a:real^N s t.
          aff_ge (IMAGE (\x. a + x) s) (IMAGE (\x. a + x) t) =
          IMAGE (\x. a + x) (aff_ge s t)"
   (REWRITE_TAC [aff_ge_def, AFFSIGN_TRANSLATION])

  let AFF_GT_TRANSLATION ← prove
   r"!a:real^N s t.
          aff_gt (IMAGE (\x. a + x) s) (IMAGE (\x. a + x) t) =
          IMAGE (\x. a + x) (aff_gt s t)"
   (REWRITE_TAC [aff_gt_def, AFFSIGN_TRANSLATION])

  let AFF_LE_TRANSLATION ← prove
   r"!a:real^N s t.
          aff_le (IMAGE (\x. a + x) s) (IMAGE (\x. a + x) t) =
          IMAGE (\x. a + x) (aff_le s t)"
   (REWRITE_TAC [aff_le_def, AFFSIGN_TRANSLATION])

  let AFF_LT_TRANSLATION ← prove
   r"!a:real^N s t.
          aff_lt (IMAGE (\x. a + x) s) (IMAGE (\x. a + x) t) =
          IMAGE (\x. a + x) (aff_lt s t)"
   (REWRITE_TAC [aff_lt_def, AFFSIGN_TRANSLATION])

  add_translation_invariants
    [AFFSIGN_TRANSLATION,
     AFF_GE_TRANSLATION,
     AFF_GT_TRANSLATION,
     AFF_LE_TRANSLATION,
     AFF_LT_TRANSLATION]

  pure { GEOM_HORIZONTAL_PLANE_RULE, GEOM_HORIZONTAL_PLANE_TAC, lin_combo, affsign,
         sgn_gt, sgn_ge, sgn_lt, sgn_le, aff_gt_def, aff_ge_def, aff_lt_def, aff_le_def,
         AFFSIGN, AFFSIGN_ALT, IN_AFFSIGN, AFFSIGN_DISJOINT_DIFF, AFF_GE_DISJOINT_DIFF,
         AFFSIGN_INJECTIVE_LINEAR_IMAGE, AFF_GE_INJECTIVE_LINEAR_IMAGE,
         AFF_GT_INJECTIVE_LINEAR_IMAGE, AFF_LE_INJECTIVE_LINEAR_IMAGE,
         AFF_LT_INJECTIVE_LINEAR_IMAGE, IN_AFFSIGN_TRANSLATION, AFFSIGN_TRANSLATION,
         AFF_GE_TRANSLATION, AFF_GT_TRANSLATION, AFF_LE_TRANSLATION, AFF_LT_TRANSLATION }
/- ------------------------------------------------------------------------- -/
/- Automate special cases of affsign.                                        -/
/- (flyspeck.ml 919-1067)                                                    -/
/- ------------------------------------------------------------------------- -/

structure FYD where
  AFF_TAC : tactic
  AFF_GE_1_1 : thm
  AFF_GE_1_2 : thm
  AFF_GE_2_1 : thm
  AFF_GT_1_1 : thm
  AFF_GT_1_2 : thm
  AFF_GT_2_1 : thm
  AFF_GT_3_1 : thm
  AFF_LT_1_1 : thm
  AFF_LT_2_1 : thm
  AFF_GE_1_2_0 : thm
  AFF_GE_1_1_0 : thm
  AFF_GE_2_1_0 : thm
  deriving Nonempty

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYD [HolBase] (D : FlyspeckDeps) (BFYC : FYC) : ExceptT String IO FYD := do
  -- @@SCOPE BEGIN
  let { aff_ge_def, aff_gt_def, aff_le_def, aff_lt_def, AFFSIGN_ALT, sgn_ge, sgn_gt,
        sgn_le, sgn_lt, .. } := BFYC
  let { MESON_TAC, .. } := D.crd
  let { AFFINE_HULL_FINITE_STEP_GEN, .. } := D.qconvex
  let { MESON, REAL_ARITH, SET_RULE, SET_TAC, VECTOR_ARITH, .. } := D.gm.ra.ts.cn.cx.cvx
  let { DE_MORGAN_THM, EXISTS_REFL, EXTENSION, FINITE_EMPTY, FINITE_INSERT, FINITE_UNION,
        .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY, REAL_ADD_RID,
        .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_LE_ADD, REAL_LT_ADD, .. } := D.gm.ra.ts.cn.cx.cvx.core4
  let { RIGHT_AND_EXISTS_THM, RIGHT_EXISTS_AND_THM, .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { real_ge, UNION_EMPTY, UNWIND_THM2, .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { VECTOR_ADD_LID, VECTOR_ADD_RDISTRIB, VECTOR_ADD_RID, VECTOR_MUL_RZERO,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { DISJOINT_EMPTY, DISJOINT_INSERT, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qses
  -- @@SCOPE END

  let AFF_TAC : tactic :=
    REWRITE_TAC [DISJOINT_INSERT, DISJOINT_EMPTY] THEN
    REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, DE_MORGAN_THM] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC [aff_ge_def, aff_gt_def, aff_le_def, aff_lt_def,
                sgn_ge, sgn_gt, sgn_le, sgn_lt, AFFSIGN_ALT] THEN
    REWRITE_TAC [← SET_RULE (← q r"(x INSERT s) UNION t = x INSERT (s UNION t)")] THEN
    REWRITE_TAC [UNION_EMPTY] THEN
    SIMP_TAC [FINITE_INSERT, FINITE_UNION, AFFINE_HULL_FINITE_STEP_GEN,
             FINITE_EMPTY, RIGHT_EXISTS_AND_THM, REAL_LT_ADD,
             REAL_LE_ADD, ← REAL_ARITH (← q r"&0 <= a / &2 <=> &0 <= a"),
             ← REAL_ARITH (← q r"&0 < a / &2 <=> &0 < a"),
             ← REAL_ARITH (← q r"a / &2 <= &0 <=> a <= &0"),
             ← REAL_ARITH (← q r"a / &2 < &0 <=> a < &0"),
             ← REAL_ARITH (← q r"a < &0 /\ b < &0 ==> a + b < &0"),
             ← REAL_ARITH (← q r"a < &0 /\ b <= &0 ==> a + b <= &0")] THEN
    ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, real_ge] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"x - y:real = z <=> x = y + z"),
                ← VECTOR_ARITH (← q r"x - y:real^N = z <=> x = y + z")] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM, REAL_ADD_RID, VECTOR_ADD_RID] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"&1 = x <=> x = &1")] THEN
    REWRITE_TAC [] THEN SET_TAC []

  let AFF_GE_1_1 ← prove
   r"!x v w.
          DISJOINT {x} {v}
          ==> aff_ge {x} {v} =
               {y | ?t1 t2.
                       &0 <= t2 /\
                       t1 + t2 = &1 /\
                       y = t1 % x + t2 % v }"
   (AFF_TAC)

  let AFF_GE_1_2 ← prove
   r"!x v w.
          DISJOINT {x} {v,w}
          ==> aff_ge {x} {v,w} =
               {y | ?t1 t2 t3.

                       &0 <= t2 /\ &0 <= t3 /\

                       t1 + t2 + t3 = &1 /\
                       y = t1 % x + t2 % v + t3 % w}"
   (AFF_TAC)

  let AFF_GE_2_1 ← prove
   r"!x v w.
          DISJOINT {x,v} {w}
          ==> aff_ge {x,v} {w} =
               {y | ?t1 t2 t3.
                       &0 <= t3 /\
                       t1 + t2 + t3 = &1 /\
                       y = t1 % x + t2 % v + t3 % w}"
   (AFF_TAC)

  let AFF_GT_1_1 ← prove
   r"!x v w.
          DISJOINT {x} {v}
          ==> aff_gt {x} {v} =
               {y | ?t1 t2.
                       &0 < t2 /\
                       t1 + t2 = &1 /\
                       y = t1 % x + t2 % v}"
   (AFF_TAC)

  let AFF_GT_1_2 ← prove
   r"!x v w.
          DISJOINT {x} {v,w}
          ==> aff_gt {x} {v,w} =
               {y | ?t1 t2 t3.
                       &0 < t2 /\ &0 < t3 /\
                       t1 + t2 + t3 = &1 /\
                       y = t1 % x + t2 % v + t3 % w}"
   (AFF_TAC)

  let AFF_GT_2_1 ← prove
   r"!x v w.
          DISJOINT {x,v} {w}
          ==> aff_gt {x,v} {w} =
               {y | ?t1 t2 t3.
                       &0 < t3 /\
                       t1 + t2 + t3 = &1 /\
                       y = t1 % x + t2 % v + t3 % w}"
   (AFF_TAC)

  let AFF_GT_3_1 ← prove
   r"!v w x y.
          DISJOINT {v,w,x} {y}
          ==> aff_gt {v,w,x} {y} =
               {z | ?t1 t2 t3 t4.
                       &0 < t4 /\
                       t1 + t2 + t3 + t4 = &1 /\
                       z = t1 % v + t2 % w + t3 % x + t4 % y}"
   (AFF_TAC)

  let AFF_LT_1_1 ← prove
   r"!x v.
          DISJOINT {x} {v}
          ==> aff_lt {x} {v} =
               {y | ?t1 t2.
                       t2 < &0 /\
                       t1 + t2 = &1 /\
                       y = t1 % x + t2 % v}"
   (AFF_TAC)

  let AFF_LT_2_1 ← prove
   r"!x v w.
          DISJOINT {x,v} {w}
          ==> aff_lt {x,v} {w} =
               {y | ?t1 t2 t3.
                       t3 < &0 /\
                       t1 + t2 + t3 = &1 /\
                       y = t1 % x + t2 % v + t3 % w}"
   (AFF_TAC)

  let AFF_GE_1_2_0 ← prove
   r"!v w.
          ~(v = vec 0) /\ ~(w = vec 0)
          ==> aff_ge {vec 0} {v,w} = {a % v + b % w | &0 <= a /\ &0 <= b}"
   (SIMP_TAC [AFF_GE_1_2,
             ← SET_RULE (← q r"DISJOINT {a} {b,c} <=> ~(b = a) /\ ~(c = a)")] THEN
    REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_ADD_LID] THEN
    ONCE_REWRITE_TAC [← MESON []
     (← q r"(?a b c. P b c /\ Q b c /\ R a b c /\ S b c) <=>
      (?b c. P b c /\ Q b c /\ S b c /\ ?a. R a b c)")] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"t + s:real = &1 <=> t = &1 - s"), EXISTS_REFL] THEN
    SET_TAC [])

  let AFF_GE_1_1_0 ← prove
   r"!v. ~(v = vec 0) ==> aff_ge {vec 0} {v} = {a % v | &0 <= a}"
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← SET_RULE (← q r"{a} = {a,a}")] THEN
    ASM_SIMP_TAC [AFF_GE_1_2_0, ← GSYM VECTOR_ADD_RDISTRIB] THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
    MESON_TAC [REAL_LE_ADD, ← REAL_ARITH
     (← q r"&0 <= a ==> &0 <= a / &2 /\ a / &2 + a / &2 = a")])

  let AFF_GE_2_1_0 ← prove
   r"!v w. DISJOINT {vec 0, v} {w}
           ==> aff_ge {vec 0, v} {w} = {s % v + t % w |s,t| &0 <= t}"
   (SIMP_TAC [AFF_GE_2_1, VECTOR_MUL_RZERO, VECTOR_ADD_LID] THEN
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"p /\ q /\ r <=> q /\ p /\ r")] THEN
    ONCE_REWRITE_TAC [← MESON [] (← q r"(?a b c. P a b c) <=> (?c b a. P a b c)")] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"t + u = &1 <=> t = &1 - u"), UNWIND_THM2] THEN
    SET_TAC [])

  pure { AFF_TAC, AFF_GE_1_1, AFF_GE_1_2, AFF_GE_2_1, AFF_GT_1_1, AFF_GT_1_2,
         AFF_GT_2_1, AFF_GT_3_1, AFF_LT_1_1, AFF_LT_2_1, AFF_GE_1_2_0, AFF_GE_1_1_0,
         AFF_GE_2_1_0 }
/- ------------------------------------------------------------------------- -/
/- Properties of affsign variants.                                           -/
/- (flyspeck.ml 1068-1383)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FYE where
  CONVEX_AFFSIGN : thm
  CONVEX_AFF_GE : thm
  CONVEX_AFF_LE : thm
  CONVEX_AFF_GT : thm
  CONVEX_AFF_LT : thm
  AFFSIGN_SUBSET_AFFINE_HULL : thm
  AFF_GE_SUBSET_AFFINE_HULL : thm
  AFF_LE_SUBSET_AFFINE_HULL : thm
  AFF_GT_SUBSET_AFFINE_HULL : thm
  AFF_LT_SUBSET_AFFINE_HULL : thm
  AFFSIGN_EQ_AFFINE_HULL : thm
  AFF_GE_EQ_AFFINE_HULL : thm
  AFF_LE_EQ_AFFINE_HULL : thm
  AFF_GT_EQ_AFFINE_HULL : thm
  AFF_LT_EQ_AFFINE_HULL : thm
  AFFSIGN_SUBSET_AFFSIGN : thm
  AFF_GT_SUBSET_AFF_GE : thm
  AFFSIGN_MONO_LEFT : thm
  AFFSIGN_MONO_SHUFFLE : thm
  AFF_GT_MONO_LEFT : thm
  AFF_GE_MONO_LEFT : thm
  AFF_LT_MONO_LEFT : thm
  AFF_LE_MONO_LEFT : thm
  AFFSIGN_MONO_RIGHT : thm
  AFF_GE_MONO_RIGHT : thm
  AFF_LE_MONO_RIGHT : thm
  AFFINE_HULL_SUBSET_AFFSIGN : thm
  AFFINE_HULL_SUBSET_AFF_GE : thm
  AFF_GE_AFF_GT_DECOMP : thm
  AFFSIGN_SPECIAL_SCALE : thm
  AFF_GE_SPECIAL_SCALE : thm
  AFF_LE_SPECIAL_SCALE : thm
  AFF_GT_SPECIAL_SCALE : thm
  AFF_LT_SPECIAL_SCALE : thm
  AFF_GE_SCALE_LEMMA : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYE [HolBase] (D : FlyspeckDeps) (BFYC : FYC) (BFYD : FYD) : ExceptT String IO FYE := do
  -- @@SCOPE BEGIN
  let { aff_ge_def, aff_gt_def, aff_le_def, aff_lt_def, AFFSIGN, AFFSIGN_ALT, sgn_ge,
        sgn_gt, sgn_le, sgn_lt, .. } := BFYC
  let { AFF_GE_1_2_0, .. } := BFYD
  let { EXPAND_QUANTS_CONV, .. } := D
  let { ASM_MESON_TAC, REAL_ARITH_TAC, .. } := D.crd
  let { AFFINE_HULL_FINITE_STEP_GEN, .. } := D.qconvex
  let { VSUM_ADD_GEN, .. } := D.qvectors
  let { INSERT_UNION_EQ, .. } := D.qsession
  let { CONJ_ASSOC, REAL_LE_MUL, REAL_MUL_LZERO, REAL_SUB_RZERO, .. } := D.crd.thms
  let { SUM_ADD_GEN, .. } := D.gm.ra.qsession
  let { MESON, REAL_ARITH, REAL_FIELD, REAL_RAT_REDUCE_CONV, SET_RULE, SET_TAC,
        .. } := D.gm.ra.ts.cn.cx.cvx
  let { ARITH_EQ, COND_RAND, COND_RATOR, CONTRAPOS_THM, EXISTS_REFL, EXTENSION,
        FINITE_INSERT, FINITE_SUBSET, FINITE_UNION, FORALL_IN_GSPEC,
        .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { IMP_CONJ, IMP_IMP, IN_DELETE, .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_UNION, LEFT_EXISTS_AND_THM, LEFT_IMP_EXISTS_THM, MONO_AND,
        MONO_EXISTS, NEUTRAL_REAL_ADD, NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, REAL_ADD_LID,
        REAL_ADD_RID, REAL_DIV_LMUL, .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_LE_ADD, REAL_LE_DIV, REAL_LE_REFL, REAL_LT_ADD, REAL_LT_IMP_LE,
        REAL_LT_IMP_NZ, REAL_LT_MUL, .. } := D.gm.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_RID, REAL_MUL_RNEG, REAL_MUL_RZERO, REAL_MUL_SYM,
        REAL_NEG_ADD, REAL_OF_NUM_EQ, REAL_POS, REAL_SUB_ADD, REAL_SUB_LE, REAL_SUB_LT,
        RIGHT_EXISTS_AND_THM, SUBSET, SUBSET_ANTISYM_EQ, SUBSET_REFL, SUBSET_TRANS,
        .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { iterate, sum, SUM_DELETE, SUM_LMUL, SUM_RESTRICT_SET, support, SWAP_EXISTS_THM,
        UNION_EMPTY, .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { VECTOR_ADD_RDISTRIB, VECTOR_MUL_ASSOC, VECTOR_MUL_EQ_0, VECTOR_MUL_LZERO,
        VECTOR_MUL_RZERO, VECTOR_SUB_RZERO, VSUM_DELETE, VSUM_LMUL, VSUM_RESTRICT_SET,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { DELETE_SUBSET, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qses
  let { QUANTIFY_SURJECTION_THM, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qvec
  let { AFFINE_HULL_FINITE, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qcvx1
  let { CONVEX_ALT, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  -- @@SCOPE END

  let CONVEX_AFFSIGN ← prove
   r"!sgn. (!x y u. sgn(x) /\ sgn(y) /\ &0 <= u /\ u <= &1
                    ==> sgn((&1 - u) * x + u * y))
           ==> !s t:real^N->bool. convex(affsign sgn s t)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [AFFSIGN, CONVEX_ALT] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:real^N", ← q r"y:real^N", ← q r"u:real"] THEN
    REWRITE_TAC [IN_ELIM_THM, IMP_CONJ, LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [IMP_IMP, ← GSYM CONJ_ASSOC] THEN
    X_GEN_TAC (← q r"f:real^N->real") THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"g:real^N->real") THEN STRIP_TAC THEN
    EXISTS_TAC (← q r"\x:real^N. (&1 - u) * f x + u * g x") THEN
    ASM_REWRITE_TAC [VECTOR_ADD_RDISTRIB] THEN REPEAT CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN
      W (MP_TAC o PART_MATCH (lhs o rand) VSUM_ADD_GEN o lhand o snd) THEN
      REWRITE_TAC [← GSYM VECTOR_MUL_ASSOC, VSUM_LMUL] THEN
      DISCH_THEN MATCH_MP_TAC,
      ASM_MESON_TAC [],
      W (MP_TAC o PART_MATCH (lhs o rand) SUM_ADD_GEN o lhand o snd) THEN
      ASM_REWRITE_TAC [← GSYM VECTOR_MUL_ASSOC, SUM_LMUL] THEN
      REWRITE_TAC [REAL_MUL_RID, REAL_SUB_ADD] THEN DISCH_THEN MATCH_MP_TAC] THEN
    (CONJ_TAC THENL
      [MP_TAC (← ASSUME (← q r"sum (s UNION t:real^N->bool) f = &1")),
       MP_TAC (← ASSUME (← q r"sum (s UNION t:real^N->bool) g = &1"))]) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [sum] THEN
    ONCE_REWRITE_TAC [iterate] THEN
    REWRITE_TAC [support, NEUTRAL_REAL_ADD] THEN
    COND_CASES_TAC THEN REWRITE_TAC [REAL_OF_NUM_EQ, ARITH_EQ] THEN
    DISCH_THEN (K ALL_TAC : thm → tactic) THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
     (← REWRITE_RULE [IMP_CONJ] FINITE_SUBSET)) THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC [CONTRAPOS_THM] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [VECTOR_MUL_LZERO, VECTOR_MUL_RZERO, REAL_MUL_RZERO])

  let CONVEX_AFF_GE ← prove
   r"!s t. convex(aff_ge s t)"
   (REWRITE_TAC [aff_ge_def, sgn_ge] THEN MATCH_MP_TAC CONVEX_AFFSIGN THEN
    SIMP_TAC [REAL_LE_MUL, REAL_LE_ADD, REAL_SUB_LE])

  let CONVEX_AFF_LE ← prove
   r"!s t. convex(aff_le s t)"
   (REWRITE_TAC [aff_le_def, sgn_le] THEN MATCH_MP_TAC CONVEX_AFFSIGN THEN
    REWRITE_TAC [← REAL_ARITH (← q r"x <= &0 <=> &0 <= --x"), REAL_NEG_ADD, ← GSYM
      REAL_MUL_RNEG] THEN
    SIMP_TAC [REAL_LE_MUL, REAL_LE_ADD, REAL_SUB_LE])

  let CONVEX_AFF_GT ← prove
   r"!s t. convex(aff_gt s t)"
   (REWRITE_TAC [aff_gt_def, sgn_gt] THEN MATCH_MP_TAC CONVEX_AFFSIGN THEN
    REWRITE_TAC [← REAL_ARITH (← q r"&0 <= x <=> x = &0 \/ &0 < x"),
                ← REAL_ARITH (← q r"x <= &1 <=> x = &1 \/ x < &1")] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_LID, REAL_ADD_RID, REAL_MUL_LID] THEN
    ASM_SIMP_TAC [REAL_LT_ADD, REAL_LT_MUL, REAL_SUB_LT])

  let CONVEX_AFF_LT ← prove
   r"!s t. convex(aff_lt s t)"
   (REWRITE_TAC [aff_lt_def, sgn_lt] THEN MATCH_MP_TAC CONVEX_AFFSIGN THEN
    REWRITE_TAC [← REAL_ARITH (← q r"x < &0 <=> &0 < --x"), REAL_NEG_ADD, ← GSYM
      REAL_MUL_RNEG] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"&0 <= x <=> x = &0 \/ &0 < x"),
                ← REAL_ARITH (← q r"x <= &1 <=> x = &1 \/ x < &1")] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_LID, REAL_ADD_RID, REAL_MUL_LID] THEN
    ASM_SIMP_TAC [REAL_LT_ADD, REAL_LT_MUL, REAL_SUB_LT])

  let AFFSIGN_SUBSET_AFFINE_HULL ← prove
   r"!sgn s t. (affsign sgn s t) SUBSET (affine hull (s UNION t))"
   (REWRITE_TAC [AFFINE_HULL_FINITE, AFFSIGN] THEN SET_TAC [])

  let AFF_GE_SUBSET_AFFINE_HULL ← prove
   r"!s t. (aff_ge s t) SUBSET (affine hull (s UNION t))"
   (REWRITE_TAC [aff_ge_def, AFFSIGN_SUBSET_AFFINE_HULL])

  let AFF_LE_SUBSET_AFFINE_HULL ← prove
   r"!s t. (aff_le s t) SUBSET (affine hull (s UNION t))"
   (REWRITE_TAC [aff_le_def, AFFSIGN_SUBSET_AFFINE_HULL])

  let AFF_GT_SUBSET_AFFINE_HULL ← prove
   r"!s t. (aff_gt s t) SUBSET (affine hull (s UNION t))"
   (REWRITE_TAC [aff_gt_def, AFFSIGN_SUBSET_AFFINE_HULL])

  let AFF_LT_SUBSET_AFFINE_HULL ← prove
   r"!s t. (aff_lt s t) SUBSET (affine hull (s UNION t))"
   (REWRITE_TAC [aff_lt_def, AFFSIGN_SUBSET_AFFINE_HULL])

  let AFFSIGN_EQ_AFFINE_HULL ← prove
   r"!sgn s t. affsign sgn s {} = affine hull s"
   (REWRITE_TAC [AFFSIGN, AFFINE_HULL_FINITE] THEN
    REWRITE_TAC [UNION_EMPTY, NOT_IN_EMPTY] THEN SET_TAC [])

  let AFF_GE_EQ_AFFINE_HULL ← prove
   r"!s t. aff_ge s {} = affine hull s"
   (REWRITE_TAC [aff_ge_def, AFFSIGN_EQ_AFFINE_HULL])

  let AFF_LE_EQ_AFFINE_HULL ← prove
   r"!s t. aff_le s {} = affine hull s"
   (REWRITE_TAC [aff_le_def, AFFSIGN_EQ_AFFINE_HULL])

  let AFF_GT_EQ_AFFINE_HULL ← prove
   r"!s t. aff_gt s {} = affine hull s"
   (REWRITE_TAC [aff_gt_def, AFFSIGN_EQ_AFFINE_HULL])

  let AFF_LT_EQ_AFFINE_HULL ← prove
   r"!s t. aff_lt s {} = affine hull s"
   (REWRITE_TAC [aff_lt_def, AFFSIGN_EQ_AFFINE_HULL])

  let AFFSIGN_SUBSET_AFFSIGN ← prove
   r"!sgn1 sgn2 s t.
          (!x. sgn1 x ==> sgn2 x) ==> affsign sgn1 s t SUBSET affsign sgn2 s t"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [AFFSIGN, SUBSET, IN_ELIM_THM] THEN
    GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC [])

  let AFF_GT_SUBSET_AFF_GE ← prove
   r"!s t. aff_gt s t SUBSET aff_ge s t"
   (REPEAT GEN_TAC THEN REWRITE_TAC [aff_gt_def, aff_ge_def] THEN
    MATCH_MP_TAC AFFSIGN_SUBSET_AFFSIGN THEN
    SIMP_TAC [sgn_gt, sgn_ge, REAL_LT_IMP_LE])

  let AFFSIGN_MONO_LEFT ← prove
   r"!sgn s s' t:real^N->bool.
          s SUBSET s' ==> affsign sgn s t SUBSET affsign sgn s' t"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [AFFSIGN, SUBSET, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"y:real^N") THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:real^N->real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"\x:real^N. if x IN s UNION t then u x else &0") THEN
    REWRITE_TAC [COND_RAND, COND_RATOR, VECTOR_MUL_LZERO] THEN
    REWRITE_TAC [← GSYM SUM_RESTRICT_SET, ← GSYM VSUM_RESTRICT_SET] THEN
    ASM_SIMP_TAC [← SET_RULE
     (← q r"s SUBSET s' ==> {x | x IN s' UNION t /\ x IN s UNION t} = s UNION t")] THEN
    ASM SET_TAC [])

  let AFFSIGN_MONO_SHUFFLE ← prove
   r"!sgn s t s' t'.
          s' UNION t' = s UNION t /\ t' SUBSET t
          ==> affsign sgn s t SUBSET affsign sgn s' t'"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [AFFSIGN, SUBSET, IN_ELIM_THM] THEN
    GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_REWRITE_TAC [] THEN ASM SET_TAC [])

  let AFF_GT_MONO_LEFT ← prove
   r"!s s' t. s SUBSET s' ==> aff_gt s t SUBSET aff_gt s' t"
   (REWRITE_TAC [aff_gt_def, AFFSIGN_MONO_LEFT])

  let AFF_GE_MONO_LEFT ← prove
   r"!s s' t. s SUBSET s' ==> aff_ge s t SUBSET aff_ge s' t"
   (REWRITE_TAC [aff_ge_def, AFFSIGN_MONO_LEFT])

  let AFF_LT_MONO_LEFT ← prove
   r"!s s' t. s SUBSET s' ==> aff_lt s t SUBSET aff_lt s' t"
   (REWRITE_TAC [aff_lt_def, AFFSIGN_MONO_LEFT])

  let AFF_LE_MONO_LEFT ← prove
   r"!s s' t. s SUBSET s' ==> aff_le s t SUBSET aff_le s' t"
   (REWRITE_TAC [aff_le_def, AFFSIGN_MONO_LEFT])

  let AFFSIGN_MONO_RIGHT ← prove
   r"!sgn s t t':real^N->bool.
          sgn(&0) /\ t SUBSET t' /\ DISJOINT s t'
          ==> affsign sgn s t SUBSET affsign sgn s t'"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [AFFSIGN, SUBSET, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"y:real^N") THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:real^N->real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"\x:real^N. if x IN s UNION t then u x else &0") THEN
    REWRITE_TAC [COND_RAND, COND_RATOR, VECTOR_MUL_LZERO] THEN
    REWRITE_TAC [← GSYM SUM_RESTRICT_SET, ← GSYM VSUM_RESTRICT_SET] THEN
    ASM_SIMP_TAC [← SET_RULE
     (← q r"t SUBSET t' ==> {x | x IN s UNION t' /\ x IN s UNION t} = s UNION t")] THEN
    ASM SET_TAC [])

  let AFF_GE_MONO_RIGHT ← prove
   r"!s t t'. t SUBSET t' /\ DISJOINT s t' ==> aff_ge s t SUBSET aff_ge s t'"
   (SIMP_TAC [aff_ge_def, AFFSIGN_MONO_RIGHT, sgn_ge, REAL_POS])

  let AFF_LE_MONO_RIGHT ← prove
   r"!s t t'. t SUBSET t' /\ DISJOINT s t' ==> aff_le s t SUBSET aff_le s t'"
   (SIMP_TAC [aff_le_def, AFFSIGN_MONO_RIGHT, sgn_le, REAL_LE_REFL])

  let AFFINE_HULL_SUBSET_AFFSIGN ← prove
   r"!sgn s t:real^N->bool.
          sgn(&0) /\ DISJOINT s t
          ==> affine hull s SUBSET affsign sgn s t"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC (← q r"affsign sgn (s:real^N->bool) {}") THEN CONJ_TAC THENL
     [REWRITE_TAC [AFFSIGN_EQ_AFFINE_HULL, SUBSET_REFL],
      MATCH_MP_TAC AFFSIGN_MONO_RIGHT THEN ASM SET_TAC []])

  let AFFINE_HULL_SUBSET_AFF_GE ← prove
   r"!s t. DISJOINT s t ==> affine hull s SUBSET aff_ge s t"
   (SIMP_TAC [aff_ge_def, sgn_ge, REAL_LE_REFL, AFFINE_HULL_SUBSET_AFFSIGN])

  let AFF_GE_AFF_GT_DECOMP ← prove
   r"!s:real^N->bool.
          FINITE s /\ FINITE t /\ DISJOINT s t
          ==> aff_ge s t = aff_gt s t UNION
                           UNIONS {aff_ge s (t DELETE a) | a | a IN t}"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← SET_RULE
     (← q r"t' SUBSET t /\ (!a. a IN s ==> f(a) SUBSET t) /\
      (!y. y IN t ==> y IN t' \/ ?a. a IN s /\ y IN f(a))
      ==> t = t' UNION UNIONS {f a | a IN s}")) THEN
    REWRITE_TAC [AFF_GT_SUBSET_AFF_GE] THEN
    ASM_SIMP_TAC [DELETE_SUBSET, AFF_GE_MONO_RIGHT] THEN
    REWRITE_TAC [aff_ge_def, aff_gt_def, AFFSIGN, sgn_ge, sgn_gt] THEN
    X_GEN_TAC (← q r"y:real^N") THEN REWRITE_TAC [IN_ELIM_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:real^N->real") STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC (← q r"!x:real^N. x IN t ==> &0 < u x") THENL
     [DISJ1_TAC THEN EXISTS_TAC (← q r"u:real^N->real") THEN ASM_REWRITE_TAC [],
      DISJ2_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [NOT_FORALL_THM]) THEN
      ASM_SIMP_TAC [← REAL_ARITH (← q r"&0 <= x ==> (&0 < x <=> ~(x = &0))")] THEN
      REWRITE_TAC [NOT_IMP] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC (← q r"a:real^N") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      EXISTS_TAC (← q r"u:real^N->real") THEN
      ASM_SIMP_TAC [← SET_RULE
       (← q r"a IN t /\ DISJOINT s t
        ==> s UNION (t DELETE a) = (s UNION t) DELETE a")] THEN
      ASM_SIMP_TAC [IN_DELETE, SUM_DELETE, VSUM_DELETE, REAL_SUB_RZERO,
                   FINITE_UNION, IN_UNION] THEN
      REWRITE_TAC [VECTOR_MUL_LZERO, VECTOR_SUB_RZERO]])

  let AFFSIGN_SPECIAL_SCALE ← prove
   r"!sgn s t a v.
          FINITE s /\ FINITE t /\
          ~(vec 0 IN t) /\ ~(v IN t) /\ ~((a % v) IN t) /\
          (!x. sgn x ==> sgn(x / &2)) /\
          (!x y. sgn x /\ sgn y ==> sgn(x + y)) /\
          &0 < a
          ==> affsign sgn (vec 0 INSERT (a % v) INSERT s) t =
              affsign sgn (vec 0 INSERT v INSERT s) t"
   (REWRITE_TAC [EXTENSION] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [AFFSIGN_ALT, IN_ELIM_THM, INSERT_UNION_EQ] THEN
    ASM_SIMP_TAC [FINITE_INSERT, FINITE_UNION, AFFINE_HULL_FINITE_STEP_GEN,
                 RIGHT_EXISTS_AND_THM] THEN
    REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_SUB_RZERO] THEN
    GEN_REWRITE_TAC BINOP_CONV [SWAP_EXISTS_THM] THEN
    GEN_REWRITE_TAC (BINOP_CONV o BINDER_CONV) [SWAP_EXISTS_THM] THEN
    REWRITE_TAC [LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"x = &1 - v - v' <=> v = &1 - (x + v')")] THEN
    REWRITE_TAC [EXISTS_REFL] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP (← MESON [REAL_LT_IMP_NZ, REAL_DIV_LMUL]
     (← q r"!a. &0 < a ==> (!y. ?x. a * x = y)"))) THEN
    DISCH_THEN (MP_TAC o MATCH_MP QUANTIFY_SURJECTION_THM) THEN
    DISCH_THEN (fun th => tactic_of do
      pure (CONV_TAC (RAND_CONV (← EXPAND_QUANTS_CONV th)))) THEN
    REWRITE_TAC [VECTOR_MUL_ASSOC, REAL_MUL_SYM])

  let AFF_GE_SPECIAL_SCALE ← prove
   r"!s t a v.
          FINITE s /\ FINITE t /\
          ~(vec 0 IN t) /\ ~(v IN t) /\ ~((a % v) IN t) /\
          &0 < a
          ==> aff_ge (vec 0 INSERT (a % v) INSERT s) t =
              aff_ge (vec 0 INSERT v INSERT s) t"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [aff_ge_def] THEN
    MATCH_MP_TAC AFFSIGN_SPECIAL_SCALE THEN
    ASM_REWRITE_TAC [sgn_ge] THEN REAL_ARITH_TAC)

  let AFF_LE_SPECIAL_SCALE ← prove
   r"!s t a v.
          FINITE s /\ FINITE t /\
          ~(vec 0 IN t) /\ ~(v IN t) /\ ~((a % v) IN t) /\
          &0 < a
          ==> aff_le (vec 0 INSERT (a % v) INSERT s) t =
              aff_le (vec 0 INSERT v INSERT s) t"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [aff_le_def] THEN
    MATCH_MP_TAC AFFSIGN_SPECIAL_SCALE THEN
    ASM_REWRITE_TAC [sgn_le] THEN REAL_ARITH_TAC)

  let AFF_GT_SPECIAL_SCALE ← prove
   r"!s t a v.
          FINITE s /\ FINITE t /\
          ~(vec 0 IN t) /\ ~(v IN t) /\ ~((a % v) IN t) /\
          &0 < a
          ==> aff_gt (vec 0 INSERT (a % v) INSERT s) t =
              aff_gt (vec 0 INSERT v INSERT s) t"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [aff_gt_def] THEN
    MATCH_MP_TAC AFFSIGN_SPECIAL_SCALE THEN
    ASM_REWRITE_TAC [sgn_gt] THEN REAL_ARITH_TAC)

  let AFF_LT_SPECIAL_SCALE ← prove
   r"!s t a v.
          FINITE s /\ FINITE t /\
          ~(vec 0 IN t) /\ ~(v IN t) /\ ~((a % v) IN t) /\
          &0 < a
          ==> aff_lt (vec 0 INSERT (a % v) INSERT s) t =
              aff_lt (vec 0 INSERT v INSERT s) t"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [aff_lt_def] THEN
    MATCH_MP_TAC AFFSIGN_SPECIAL_SCALE THEN
    ASM_REWRITE_TAC [sgn_lt] THEN REAL_ARITH_TAC)

  let AFF_GE_SCALE_LEMMA ← prove
   r"!a u v:real^N.
          &0 < a /\ ~(v = vec 0)
          ==> aff_ge {vec 0} {a % u,v} = aff_ge {vec 0} {u,v}"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"u:real^N = vec 0") THEN
    ASM_REWRITE_TAC [VECTOR_MUL_RZERO] THEN
    ASM_SIMP_TAC [AFF_GE_1_2_0, VECTOR_MUL_EQ_0, REAL_LT_IMP_NZ,
     ← SET_RULE (← q r"DISJOINT {a} {b,c} <=> ~(b = a) /\ ~(c = a)")] THEN
    REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, SUBSET, FORALL_IN_GSPEC] THEN
    CONJ_TAC THEN MAP_EVERY X_GEN_TAC [← q r"b:real", ← q r"c:real"] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THENL
     [EXISTS_TAC (← q r"a * b:real"), EXISTS_TAC (← q r"b / a:real")] THEN
    EXISTS_TAC (← q r"c:real") THEN
    ASM_SIMP_TAC [REAL_LE_DIV, REAL_LE_MUL, REAL_LT_IMP_LE] THEN
    REWRITE_TAC [VECTOR_MUL_ASSOC] THEN
    REPLICATE_TAC 2 (AP_THM_TAC THEN AP_TERM_TAC) THEN
    UNDISCH_TAC (← q r"&0 < a") THEN CONV_TAC REAL_FIELD)

  pure { CONVEX_AFFSIGN, CONVEX_AFF_GE, CONVEX_AFF_LE, CONVEX_AFF_GT, CONVEX_AFF_LT,
         AFFSIGN_SUBSET_AFFINE_HULL, AFF_GE_SUBSET_AFFINE_HULL, AFF_LE_SUBSET_AFFINE_HULL,
         AFF_GT_SUBSET_AFFINE_HULL, AFF_LT_SUBSET_AFFINE_HULL, AFFSIGN_EQ_AFFINE_HULL,
         AFF_GE_EQ_AFFINE_HULL, AFF_LE_EQ_AFFINE_HULL, AFF_GT_EQ_AFFINE_HULL,
         AFF_LT_EQ_AFFINE_HULL, AFFSIGN_SUBSET_AFFSIGN, AFF_GT_SUBSET_AFF_GE,
         AFFSIGN_MONO_LEFT, AFFSIGN_MONO_SHUFFLE, AFF_GT_MONO_LEFT, AFF_GE_MONO_LEFT,
         AFF_LT_MONO_LEFT, AFF_LE_MONO_LEFT, AFFSIGN_MONO_RIGHT, AFF_GE_MONO_RIGHT,
         AFF_LE_MONO_RIGHT, AFFINE_HULL_SUBSET_AFFSIGN, AFFINE_HULL_SUBSET_AFF_GE,
         AFF_GE_AFF_GT_DECOMP, AFFSIGN_SPECIAL_SCALE, AFF_GE_SPECIAL_SCALE,
         AFF_LE_SPECIAL_SCALE, AFF_GT_SPECIAL_SCALE, AFF_LT_SPECIAL_SCALE,
         AFF_GE_SCALE_LEMMA }
/- ------------------------------------------------------------------------- -/
/- Properties of affsign variants, continued; the special case of           -/
/- aff_ge {x} {y}, i.e. rays or half-lines.                                  -/
/- (flyspeck.ml 1384-1781)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FYF where
  AFFSIGN_0 : thm
  AFF_GE_0_AFFINE_MULTIPLE_CONVEX : thm
  AFF_GE_0_MULTIPLE_AFFINE_CONVEX : thm
  AFF_GE_0_AFFINE_CONVEX_CONE : thm
  AFF_GE_0_N : thm
  AFF_GE_0_CONVEX_HULL : thm
  AFF_GE_0_CONVEX_HULL_ALT : thm
  AFF_GE_0_CONVEX_CONE_NEGATIONS : thm
  CONVEX_HULL_AFF_GE : thm
  POLYHEDRON_AFF_GE : thm
  CLOSED_AFF_GE : thm
  CONIC_AFF_GE_0 : thm
  ANGLES_ADD_AFF_GE : thm
  AFF_GE_2_1_0_DROPOUT_3 : thm
  AFF_GE_2_1_0_SEMIALGEBRAIC : thm
  HALFLINE_REFL : thm
  HALFLINE_EXPLICIT : thm
  HALFLINE : thm
  CLOSED_HALFLINE : thm
  SEGMENT_SUBSET_HALFLINE : thm
  ENDS_IN_HALFLINE : thm
  HALFLINE_SUBSET_AFFINE_HULL : thm
  HALFLINE_INTER_COMPACT_SEGMENT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYF [HolBase] (D : FlyspeckDeps) (BFYA : FYA) (BFYC : FYC) (BFYD : FYD) (BFYE : FYE) : ExceptT String IO FYF := do
  -- @@SCOPE BEGIN
  let { COLLINEAR_BASIS_3, DROPOUT_BASIS_3, .. } := BFYA
  let { aff_ge_def, AFF_GE_DISJOINT_DIFF, AFFSIGN, AFFSIGN_DISJOINT_DIFF, sgn_ge,
        .. } := BFYC
  let { AFF_GE_1_1_0, AFF_GE_1_2_0, AFF_GE_2_1_0, AFF_TAC, .. } := BFYD
  let { AFF_GE_EQ_AFFINE_HULL, AFF_GE_SUBSET_AFFINE_HULL, AFFINE_HULL_SUBSET_AFF_GE,
        CONVEX_AFF_GE, .. } := BFYE
  let { VECTOR_ANGLE_LMUL, VECTOR_ANGLE_RMUL, .. } := D.gea
  let { angle, .. } := D.gec
  let { ANGLES_ADD_BETWEEN, .. } := D.gee
  let { ASM_MESON_TAC, MESON_TAC, REAL_ARITH_TAC, REAL_RING, .. } := D.crd
  let { CROSS_EQ_0, CROSS_RMUL, CROSS_RSUB, .. } := D.crs
  let { COLLINEAR_AFFINE_HULL_COLLINEAR, SPAN_CONVEX_CONE_ALLSIGNS, .. } := D.qconvex
  let { DROPOUT_ADD, DROPOUT_MUL, .. } := D.qvectors
  let { INSERT_UNION, .. } := D.qsession
  let { POLYHEDRON_CONVEX_CONE_HULL, POLYHEDRON_IMP_CLOSED, polytope,
        POLYTOPE_IMP_POLYHEDRON, .. } := D.qpolytope
  let { GEOM_ORIGIN_TAC, .. } := D.geomorigin
  let { ARITH, CART_EQ, DIMINDEX_3, FORALL_3, LAMBDA_BETA, REAL_ENTIRE, REAL_LE_MUL,
        REAL_MUL_LZERO, REAL_SUB_RZERO, VECTOR_MUL_COMPONENT, VECTOR_MUL_LID,
        VECTOR_SUB_EQ, .. } := D.crd.thms
  let { dropout, .. } := D.gm.ra.qvectors
  let { ASM_REAL_ARITH_TAC, MESON, REAL_ARITH, REAL_FIELD, SET_RULE, SET_TAC, VECTOR_ARITH,
        VECTOR_ARITH_TAC, .. } := D.gm.ra.ts.cn.cx.cvx
  let { FORALL_2, .. } := D.gm.ra.ts.cn.cx.cpx
  let { DIFF_EMPTY, DIFF_EQ_EMPTY, DIMINDEX_2, ETA_AX, EXISTS_REFL, EXTENSION,
        FINITE_DELETE, FINITE_DIFF, FINITE_EMPTY, FINITE_IMAGE, FINITE_INSERT, FINITE_SING,
        FINITE_UNION, FORALL_IN_GSPEC, .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { FUN_EQ_THM, IN_DELETE, IN_DIFF, INSERT_AC, .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, IN_INTER, IN_SING, IN_UNION, LEFT_AND_EXISTS_THM,
        LEFT_IMP_EXISTS_THM, MEMBER_NOT_EMPTY, NOT_IN_EMPTY,
        .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_INV_EQ_0, REAL_LE_DIV, REAL_LE_INV_EQ, REAL_LE_LT, REAL_LE_MUL_EQ,
        REAL_LE_REFL, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_LE, REAL_LT_REFL,
        .. } := D.gm.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_AC, REAL_MUL_LINV, REAL_MUL_RINV, REAL_POS, REAL_SUB_ADD, REAL_SUB_LE,
        RIGHT_EXISTS_AND_THM, SET_PROVE_CASES, SUBSET, SUBSET_ANTISYM,
        .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { real_div, SUM_CLAUSES, SUM_DELTA, SUM_LMUL, SUM_POS_EQ_0, SUM_POS_LE,
        SWAP_EXISTS_THM, UNION_EMPTY, UNION_SUBSET, .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { HULL_INC, .. } := D.gm.ra.ts.cn.cx.cvx.misc
  let { BASIS_COMPONENT, COLLINEAR_2, COLLINEAR_LEMMA_ALT, COLLINEAR_SUBSET, DOT_LMUL,
        DOT_POS_LT, .. } := D.gm.ra.ts.cn.cx.cvx.vec1
  let { SPAN_FINITE, SPAN_MUL, .. } := D.gm.ra.ts.cn.cx.cvx.vec3
  let { VECTOR_ADD_COMPONENT, VECTOR_ADD_LDISTRIB, VECTOR_ADD_LID, VECTOR_ADD_RID,
        VECTOR_MUL_ASSOC, VECTOR_MUL_EQ_0, VECTOR_MUL_LZERO, VECTOR_MUL_RZERO,
        VECTOR_SUB_RZERO, VSUM_0, VSUM_CLAUSES, VSUM_EQ, VSUM_LMUL, VSUM_UNION,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { BETWEEN_IN_SEGMENT, CLOSED_INTER_COMPACT, .. } := D.gm.ra.ts.cn.cx.cvx.top1
  let { ENDS_IN_SEGMENT, .. } := D.gm.ra.ts.cn.cx.cvx.top3
  let { IN_SEGMENT, .. } := D.gm.ra.ts.cn.cx.cvx.top4
  let { SEGMENT_REFL, SEGMENT_SYM, .. } := D.gm.ra.ts.cn.cx.cvx.top5
  let { AFFINE_HULL_EQ_SPAN, AFFINE_HULL_SING, COMPACT_CONVEX_COLLINEAR_SEGMENT,
        .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qcvx1
  let { CONVEX_CONE_HULL_CONVEX_HULL_NONEMPTY, CONVEX_CONE_HULL_EMPTY,
        CONVEX_CONE_HULL_UNION, CONVEX_HULL_2, CONVEX_HULL_EMPTY, CONVEX_HULL_EQ_EMPTY,
        CONVEX_HULL_FINITE, CONVEX_HULL_SING, CONVEX_INTER,
        .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  let { conic, SEGMENT_CONVEX_HULL, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qcvx3
  -- @@SCOPE END

  let AFFSIGN_0 ← prove
   r"!sgn s t.
          FINITE s /\ FINITE t /\ (vec 0) IN (s DIFF t)
          ==> affsign sgn s t =
               { vsum (s UNION t) (\v. f v % v) |f|
                 !x:real^N. x IN t ==> sgn(f x)}"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [AFFSIGN] THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP (← SET_RULE
     (← q r"x IN s DIFF t ==> s UNION t = x INSERT ((s UNION t) DELETE x)"))) THEN
    ASM_SIMP_TAC [SUM_CLAUSES, VSUM_CLAUSES, FINITE_UNION, FINITE_DELETE] THEN
    REWRITE_TAC [IN_DELETE, VECTOR_MUL_RZERO, VECTOR_ADD_LID] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC [FORALL_IN_GSPEC, SUBSET, LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q r"y:real^N", ← q r"f:real^N->real"] THEN
      STRIP_TAC THEN EXISTS_TAC (← q r"f:real^N->real") THEN ASM_REWRITE_TAC [],
      X_GEN_TAC (← q r"f:real^N->real") THEN DISCH_TAC THEN
      EXISTS_TAC
       (← q r"\x:real^N. if x = vec 0
                   then &1 - sum ((s UNION t) DELETE vec 0) (\x. f x)
                   else f x") THEN
      MP_TAC (← SET_RULE
       (← q r"!x:real^N. x IN (s UNION t) DELETE vec 0 ==> ~(x = vec 0)")) THEN
      SIMP_TAC [ETA_AX, REAL_SUB_ADD] THEN DISCH_THEN (K ALL_TAC : thm → tactic) THEN
      ASM SET_TAC []])

  let AFF_GE_0_AFFINE_MULTIPLE_CONVEX ← prove
   r"!s t:real^N->bool.
          FINITE s /\ FINITE t /\ vec 0 IN (s DIFF t) /\ ~(t = {})
          ==> aff_ge s t =
                 {x + c % y | x IN affine hull (s DIFF t) /\
                              y IN convex hull t /\ &0 <= c}"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [aff_ge_def, AFFSIGN_0, sgn_ge] THEN
    ONCE_REWRITE_TAC [← SET_RULE (← q r"s UNION t = (s DIFF t) UNION t")] THEN
    ASM_SIMP_TAC [VSUM_UNION, FINITE_DIFF,
                 ← SET_RULE (← q r"DISJOINT (s DIFF t) t")] THEN
    ASM_SIMP_TAC [AFFINE_HULL_EQ_SPAN, HULL_INC] THEN
    ASM_SIMP_TAC [SPAN_FINITE, FINITE_DIFF, CONVEX_HULL_FINITE] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC (← q r"f:real^N->real") THEN DISCH_TAC THEN
      EXISTS_TAC (← q r"vsum (s DIFF t) (\x:real^N. f x % x)") THEN
      ASM_CASES_TAC (← q r"sum t (f:real^N->real) = &0") THENL
       [MP_TAC (← ISPECL [← q r"f:real^N->real", ← q r"t:real^N->bool"] SUM_POS_EQ_0) THEN
        ASM_SIMP_TAC [VECTOR_MUL_LZERO, REAL_MUL_LZERO, VSUM_0] THEN
        DISCH_TAC THEN EXISTS_TAC (← q r"&0") THEN
        REWRITE_TAC [VECTOR_MUL_LZERO, REAL_LE_REFL] THEN
        REWRITE_TAC [RIGHT_EXISTS_AND_THM] THEN CONJ_TAC THENL
         [EXISTS_TAC (← q r"f:real^N->real") THEN REWRITE_TAC [], ALL_TAC] THEN
        ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
        REWRITE_TAC [RIGHT_EXISTS_AND_THM, ← GSYM EXISTS_REFL] THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [← GSYM MEMBER_NOT_EMPTY]) THEN
        DISCH_THEN (X_CHOOSE_TAC (← q r"a:real^N")) THEN
        EXISTS_TAC (← q r"\x:real^N. if x = a then &1 else &0") THEN
        ASM_REWRITE_TAC [SUM_DELTA] THEN MESON_TAC [REAL_POS],
        EXISTS_TAC (← q r"sum t (f:real^N->real)") THEN
        EXISTS_TAC (← q r"inv(sum t (f:real^N->real)) % vsum t (\v. f v % v)") THEN
        REPEAT CONJ_TAC THENL
         [EXISTS_TAC (← q r"f:real^N->real") THEN REWRITE_TAC [],
          EXISTS_TAC (← q r"\x:real^N. f x / sum t (f:real^N->real)") THEN
          ASM_SIMP_TAC [REAL_LE_DIV, SUM_POS_LE] THEN
          ONCE_REWRITE_TAC [← REAL_ARITH (← q r"x / y:real = inv y * x")] THEN
          ASM_SIMP_TAC [← GSYM VECTOR_MUL_ASSOC, SUM_LMUL, VSUM_LMUL] THEN
          ASM_SIMP_TAC [REAL_MUL_LINV],
          ASM_SIMP_TAC [SUM_POS_LE],
          AP_TERM_TAC THEN ASM_CASES_TAC (← q r"sum t (f:real^N->real) = &0") THEN
          ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_RINV, VECTOR_MUL_LID]]],
      MAP_EVERY X_GEN_TAC [← q r"x:real^N", ← q r"c:real", ← q r"y:real^N"] THEN
      DISCH_THEN (CONJUNCTS_THEN2
       (X_CHOOSE_THEN (← q r"u:real^N->real") (SUBST1_TAC o SYM)) MP_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2
       (X_CHOOSE_THEN (← q r"v:real^N->real") MP_TAC) ASSUME_TAC) THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      EXISTS_TAC (← q r"(\x. if x IN t then c * v x else u x):real^N->real") THEN
      ASM_SIMP_TAC [REAL_LE_MUL, VSUM_LMUL, ← GSYM VECTOR_MUL_ASSOC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
      SIMP_TAC [IN_DIFF]])

  let AFF_GE_0_MULTIPLE_AFFINE_CONVEX ← prove
   r"!s t:real^N->bool.
          FINITE s /\ FINITE t /\ vec 0 IN (s DIFF t) /\ ~(t = {})
          ==> aff_ge s t =
                 affine hull (s DIFF t) UNION
                 {c % (x + y) | x IN affine hull (s DIFF t) /\
                                y IN convex hull t /\ &0 <= c}"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC [UNION_SUBSET] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC [AFF_GE_0_AFFINE_MULTIPLE_CONVEX,
                   AFFINE_HULL_EQ_SPAN, HULL_INC] THEN
      REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [← q r"x:real^N", ← q r"c:real", ← q r"y:real^N"] THEN STRIP_TAC THEN
      REWRITE_TAC [IN_ELIM_THM, IN_UNION] THEN ASM_CASES_TAC (← q r"c = &0") THENL
       [DISJ1_TAC THEN ASM_REWRITE_TAC [VECTOR_MUL_LZERO, VECTOR_ADD_RID],
        DISJ2_TAC THEN MAP_EVERY EXISTS_TAC
         [← q r"c:real", ← q r"inv(c) % x:real^N", ← q r"y:real^N"] THEN
        ASM_SIMP_TAC [SPAN_MUL, VECTOR_ADD_LDISTRIB, VECTOR_MUL_ASSOC,
                     REAL_MUL_RINV, VECTOR_MUL_LID]],
      REWRITE_TAC [aff_ge_def] THEN ONCE_REWRITE_TAC [AFFSIGN_DISJOINT_DIFF] THEN
      REWRITE_TAC [← GSYM aff_ge_def] THEN
      MATCH_MP_TAC AFFINE_HULL_SUBSET_AFF_GE THEN SET_TAC [],
      ASM_SIMP_TAC [AFF_GE_0_AFFINE_MULTIPLE_CONVEX,
                   AFFINE_HULL_EQ_SPAN, HULL_INC] THEN
      REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [← q r"c:real", ← q r"x:real^N", ← q r"y:real^N"] THEN STRIP_TAC THEN
      REWRITE_TAC [IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC
       [← q r"c % x:real^N", ← q r"c:real", ← q r"y:real^N"] THEN
      ASM_SIMP_TAC [SPAN_MUL, VECTOR_ADD_LDISTRIB]])

  let AFF_GE_0_AFFINE_CONVEX_CONE ← prove
   r"!s t:real^N->bool.
          FINITE s /\ FINITE t /\ vec 0 IN (s DIFF t)
          ==> aff_ge s t =
                 {x + y | x IN affine hull (s DIFF t) /\
                          y IN convex_cone hull t}"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"t:real^N->bool = {}") THENL
     [ASM_REWRITE_TAC [AFF_GE_EQ_AFFINE_HULL, CONVEX_CONE_HULL_EMPTY] THEN
      REWRITE_TAC [IN_SING, DIFF_EMPTY] THEN
      REWRITE_TAC [← SET_RULE (← q r"{x + y:real^N | P x /\ y = a} = {x + a | P x}")] THEN
      REWRITE_TAC [VECTOR_ADD_RID] THEN SET_TAC [],
      ASM_SIMP_TAC [CONVEX_CONE_HULL_CONVEX_HULL_NONEMPTY,
                    AFF_GE_0_AFFINE_MULTIPLE_CONVEX] THEN
     SET_TAC []])

  let AFF_GE_0_N ← prove
   r"!s:real^N->bool.
          FINITE s /\ ~(vec 0 IN s)
          ==> aff_ge {vec 0} s =
                  {y | ?u. (!x. x IN s ==> &0 <= u x) /\
                           y = vsum s (\x. u x % x)}"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [aff_ge_def] THEN
    ASM_SIMP_TAC [AFFSIGN_0, IN_DIFF, IN_INSERT, NOT_IN_EMPTY,
                 FINITE_INSERT, FINITE_EMPTY] THEN
    ASM_SIMP_TAC [EXTENSION, sgn_ge, IN_ELIM_THM, INSERT_UNION, UNION_EMPTY] THEN
    ASM_SIMP_TAC [VSUM_CLAUSES, VECTOR_MUL_RZERO, VECTOR_ADD_LID])

  let AFF_GE_0_CONVEX_HULL ← prove
   r"!s:real^N->bool.
          FINITE s /\ ~(s = {}) /\ ~(vec 0 IN s)
          ==> aff_ge {vec 0} s = {t % y | &0 <= t /\ y IN convex hull s}"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [AFF_GE_0_AFFINE_MULTIPLE_CONVEX, IN_DIFF,
                 FINITE_INSERT, FINITE_EMPTY, IN_INSERT] THEN
    ASM_SIMP_TAC [← SET_RULE (← q r"~(a IN s) ==> {a} DIFF s = {a}")] THEN
    REWRITE_TAC [AFFINE_HULL_SING, IN_SING] THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN MESON_TAC [VECTOR_ADD_LID])

  let AFF_GE_0_CONVEX_HULL_ALT ← prove
   r"!s:real^N->bool.
          FINITE s /\ ~(vec 0 IN s)
          ==> aff_ge {vec 0} s =
              vec 0 INSERT {t % y | &0 < t /\ y IN convex hull s}"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"s:real^N->bool = {}") THENL
     [ASM_REWRITE_TAC [AFF_GE_EQ_AFFINE_HULL, CONVEX_HULL_EMPTY] THEN
      REWRITE_TAC [AFFINE_HULL_SING, NOT_IN_EMPTY] THEN SET_TAC [],
      ASM_SIMP_TAC [AFF_GE_0_CONVEX_HULL, EXTENSION, IN_ELIM_THM, IN_INSERT] THEN
      X_GEN_TAC (← q r"y:real^N") THEN ASM_CASES_TAC (← q r"y:real^N = vec 0") THEN
      ASM_REWRITE_TAC [] THENL
       [EXISTS_TAC (← q r"&0") THEN ASM_REWRITE_TAC [REAL_POS, VECTOR_MUL_LZERO] THEN
        ASM_REWRITE_TAC [MEMBER_NOT_EMPTY, CONVEX_HULL_EQ_EMPTY],
        AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"t:real") THEN
        AP_TERM_TAC THEN ABS_TAC THEN
        ASM_CASES_TAC (← q r"t = &0") THEN
        ASM_REWRITE_TAC [VECTOR_MUL_LZERO, REAL_LT_REFL] THEN
        ASM_REWRITE_TAC [REAL_LT_LE]]])

  let AFF_GE_0_CONVEX_CONE_NEGATIONS ← prove
   r"!s t:real^N->bool.
          FINITE s /\ FINITE t /\ vec 0 IN (s DIFF t)
          ==> aff_ge s t =
              convex_cone hull (s UNION t UNION IMAGE (--) (s DIFF t))"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [AFF_GE_0_AFFINE_CONVEX_CONE] THEN
    ASM_SIMP_TAC [AFFINE_HULL_EQ_SPAN, HULL_INC] THEN
    REWRITE_TAC [SPAN_CONVEX_CONE_ALLSIGNS, ← GSYM CONVEX_CONE_HULL_UNION] THEN
    AP_TERM_TAC THEN SET_TAC [])

  let CONVEX_HULL_AFF_GE ← prove
   r"!s. convex hull s = aff_ge {} s"
   (SIMP_TAC [aff_ge_def, AFFSIGN, CONVEX_HULL_FINITE, sgn_ge, UNION_EMPTY] THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN REPEAT GEN_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN MESON_TAC [])

  let POLYHEDRON_AFF_GE ← prove
   r"!s t:real^N->bool. FINITE s /\ FINITE t ==> polyhedron(aff_ge s t)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [aff_ge_def] THEN
    ONCE_REWRITE_TAC [AFFSIGN_DISJOINT_DIFF] THEN
    REWRITE_TAC [← GSYM aff_ge_def] THEN
    SUBGOAL_THEN (← q r"FINITE(s DIFF t) /\ FINITE(t:real^N->bool) /\
                  DISJOINT (s DIFF t) t")
    MP_TAC THENL [ASM_SIMP_TAC [FINITE_DIFF] THEN ASM SET_TAC [], ALL_TAC] THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN
    SPEC_TAC (← q r"s DIFF t:real^N->bool", ← q r"s:real^N->bool") THEN
    MATCH_MP_TAC SET_PROVE_CASES THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM CONVEX_HULL_AFF_GE] THEN
      MATCH_MP_TAC POLYTOPE_IMP_POLYHEDRON THEN REWRITE_TAC [polytope] THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"s:real^N->bool"] THEN
    GEOM_ORIGIN_TAC (← q r"a:real^N") THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(vec 0:real^N) IN ((vec 0 INSERT s) DIFF t)") ASSUME_TAC THENL
     [ASM SET_TAC [], ALL_TAC] THEN
    ASM_SIMP_TAC [AFF_GE_0_CONVEX_CONE_NEGATIONS, FINITE_INSERT] THEN
    MATCH_MP_TAC POLYHEDRON_CONVEX_CONE_HULL THEN
    ASM_SIMP_TAC [FINITE_INSERT, FINITE_UNION, FINITE_DIFF, FINITE_IMAGE])

  let CLOSED_AFF_GE ← prove
   r"!s t:real^N->bool. FINITE s /\ FINITE t ==> closed(aff_ge s t)"
   (SIMP_TAC [POLYHEDRON_AFF_GE, POLYHEDRON_IMP_CLOSED])

  let CONIC_AFF_GE_0 ← prove
   r"!s:real^N->bool. FINITE s /\ ~(vec 0 IN s) ==> conic(aff_ge {vec 0} s)"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [AFF_GE_0_N, conic] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN GEN_TAC THEN X_GEN_TAC (← q r"c:real") THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:real^N->real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"\v. c * (u:real^N->real) v") THEN
    REWRITE_TAC [← GSYM VECTOR_MUL_ASSOC, VSUM_LMUL] THEN
    ASM_MESON_TAC [REAL_LE_MUL])

  let ANGLES_ADD_AFF_GE ← prove
   r"!u v w x:real^N.
          ~(v = u) /\ ~(w = u) /\ ~(x = u) /\ x IN aff_ge {u} {v,w}
          ==> angle(v,u,x) + angle(x,u,w) = angle(v,u,w)"
   (GEOM_ORIGIN_TAC (← q r"u:real^N") THEN REPEAT GEN_TAC THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC [AFF_GE_1_2_0] THEN
    REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real", ← q r"b:real"] THEN
    DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    SUBGOAL_THEN (← q r"a = &0 /\ b = &0 \/ &0 < a + b") STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC,
      ASM_REWRITE_TAC [VECTOR_MUL_LZERO, VECTOR_ADD_LID],
      ALL_TAC] THEN
    DISCH_TAC THEN MP_TAC (← ISPECL
     [← q r"v:real^N", ← q r"w:real^N", ← q r"inv(a + b) % x:real^N", ← q r"vec 0:real^N"]
     ANGLES_ADD_BETWEEN) THEN
    ASM_REWRITE_TAC [angle, VECTOR_SUB_RZERO] THEN
    ASM_SIMP_TAC [VECTOR_ANGLE_RMUL, VECTOR_ANGLE_LMUL,
      REAL_INV_EQ_0, REAL_LE_INV_EQ, REAL_LT_IMP_NZ, REAL_LT_IMP_LE] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC [BETWEEN_IN_SEGMENT, CONVEX_HULL_2, SEGMENT_CONVEX_HULL] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [← q r"a / (a + b):real", ← q r"b / (a + b):real"] THEN
    ASM_SIMP_TAC [REAL_LE_DIV, REAL_LT_IMP_LE, VECTOR_ADD_LDISTRIB] THEN
    REWRITE_TAC [VECTOR_MUL_ASSOC, real_div, REAL_MUL_AC] THEN
    UNDISCH_TAC (← q r"&0 < a + b") THEN CONV_TAC REAL_FIELD)

  let AFF_GE_2_1_0_DROPOUT_3 ← prove
   r"!w z:real^3.
          ~collinear{vec 0,basis 3,z}
          ==> (w IN aff_ge {vec 0,basis 3} {z} <=>
               (dropout 3 w) IN aff_ge {vec 0:real^2} {dropout 3 z})"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"z:real^3 = vec 0") THENL
     [ASM_REWRITE_TAC [COLLINEAR_2, INSERT_AC], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"z:real^3 = basis 3") THENL
     [ASM_REWRITE_TAC [COLLINEAR_2, INSERT_AC], ALL_TAC] THEN
    REWRITE_TAC [COLLINEAR_BASIS_3] THEN DISCH_TAC THEN
    ASM_SIMP_TAC [AFF_GE_2_1_0, ← SET_RULE (← q r"DISJOINT s {a} <=> ~(a IN s)"),
                 IN_INSERT, NOT_IN_EMPTY, AFF_GE_1_1_0] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    MATCH_MP_TAC (← MESON []
     (← q r"(!t. ((?s. P s t) <=> Q t)) ==> ((?s t. P s t) <=> (?t. Q t))")) THEN
    X_GEN_TAC (← q r"t:real") THEN EQ_TAC THENL
     [STRIP_TAC THEN
      ASM_REWRITE_TAC [DROPOUT_ADD, DROPOUT_MUL, DROPOUT_BASIS_3] THEN
      VECTOR_ARITH_TAC,
      STRIP_TAC THEN EXISTS_TAC (← q r"(w:real^3)$3 - t * (z:real^3)$3") THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [CART_EQ]) THEN
      ASM_REWRITE_TAC [CART_EQ, FORALL_2, FORALL_3, DIMINDEX_2, DIMINDEX_3] THEN
      REWRITE_TAC [VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
      SIMP_TAC [dropout, LAMBDA_BETA, DIMINDEX_2, ARITH, BASIS_COMPONENT,
               DIMINDEX_3] THEN
      CONV_TAC REAL_RING])

  let AFF_GE_2_1_0_SEMIALGEBRAIC ← (do
    let lemma0 ← prove
     r"~(y = vec 0) ==> ((?s. x = s % y) <=> y cross x = vec 0)"
     (REWRITE_TAC [CROSS_EQ_0] THEN SIMP_TAC [COLLINEAR_LEMMA_ALT])
    let lemma1 ← prove
     r"!x y:real^N.
            ~(y = vec 0)
            ==> ((?t. &0 <= t /\ x = t % y) <=>
                 (?t. x = t % y) /\ &0 <= x dot y)"
     (REPEAT STRIP_TAC THEN REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
      AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"t:real") THEN
      ASM_CASES_TAC (← q r"x:real^N = t % y") THEN
      ASM_SIMP_TAC [DOT_LMUL, REAL_LE_MUL_EQ, DOT_POS_LT])
    prove
     r"!x y z:real^3.
          ~collinear {vec 0,x,y} /\ ~collinear {vec 0,x,z}
          ==> (z IN aff_ge {vec 0,x} {y} <=>
               (x cross y) cross x cross z = vec 0 /\
               &0 <= (x cross z) dot (x cross y))"
      (REPEAT GEN_TAC THEN
      MAP_EVERY (fun t => ASM_CASES_TAC t THENL
       [ASM_REWRITE_TAC [COLLINEAR_2, INSERT_AC], ALL_TAC])
       [← q r"x:real^3 = vec 0", ← q r"y:real^3 = vec 0", ← q r"y:real^3 = x"] THEN
      STRIP_TAC THEN
      ASM_SIMP_TAC [AFF_GE_2_1_0, IN_ELIM_THM, ← SET_RULE
        (← q r"DISJOINT {a,b} {c} <=> ~(a = c) /\ ~(b = c)")] THEN
      ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM, ← VECTOR_ARITH
        (← q r"a:real^N = b + c <=> a - c = b")] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [← GSYM CROSS_EQ_0]) THEN
      ASM_SIMP_TAC [lemma0, lemma1, CROSS_RMUL, CROSS_RSUB, VECTOR_SUB_EQ]))

  /- Special case of aff_ge {x} {y}, i.e. rays or half-lines. -/

  let HALFLINE_REFL ← prove
   r"!x. aff_ge {x} {x} = {x}"
   (ONCE_REWRITE_TAC [AFF_GE_DISJOINT_DIFF] THEN
    ASM_REWRITE_TAC [DIFF_EQ_EMPTY, ← GSYM CONVEX_HULL_AFF_GE, CONVEX_HULL_SING])

  let HALFLINE_EXPLICIT ← prove
   r"!x y:real^N.
          aff_ge {x} {y} =
            {z | ?t1 t2. &0 <= t2 /\ t1 + t2 = &1 /\ z = t1 % x + t2 % y}"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"x:real^N = y") THENL
     [ASM_REWRITE_TAC [HALFLINE_REFL], AFF_TAC] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"x + y = &1 <=> x = &1 - y")] THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"(&1 - x) % v + x % v:real^N = v"),
      ← MESON [] (← q r"(?x y. P y /\ x = f y /\ Q x y) <=> (?y. P y /\ Q (f y) y)")] THEN
    REWRITE_TAC [IN_ELIM_THM, IN_SING, EXTENSION] THEN MESON_TAC [REAL_POS])

  let HALFLINE ← prove
   r"!x y:real^N.
          aff_ge {x} {y} =
            {z | ?t. &0 <= t /\ z = (&1 - t) % x + t % y}"
   (REWRITE_TAC [HALFLINE_EXPLICIT,  ← REAL_ARITH (← q r"x + y = &1 <=> x = &1 - y")] THEN
    SET_TAC [])

  let CLOSED_HALFLINE ← prove
   r"!x y. closed(aff_ge {x} {y})"
   (SIMP_TAC [CLOSED_AFF_GE, FINITE_SING])

  let SEGMENT_SUBSET_HALFLINE ← prove
   r"!x y. segment[x,y] SUBSET aff_ge {x} {y}"
   (REWRITE_TAC [SEGMENT_CONVEX_HULL, CONVEX_HULL_2, HALFLINE_EXPLICIT] THEN
    SET_TAC [])

  let ENDS_IN_HALFLINE ← prove
   r"(!x y. x IN aff_ge {x} {y}) /\ (!x y. y IN aff_ge {x} {y})"
   (MESON_TAC [SEGMENT_SUBSET_HALFLINE, SUBSET, ENDS_IN_SEGMENT])

  let HALFLINE_SUBSET_AFFINE_HULL ← prove
   r"!x y. aff_ge {x} {y} SUBSET affine hull {x,y}"
   (REWRITE_TAC [AFF_GE_SUBSET_AFFINE_HULL, ← SET_RULE (← q r"{x,y} = {x} UNION {y}")])

  let HALFLINE_INTER_COMPACT_SEGMENT ← prove
   r"!s a b:real^N.
          compact s /\ convex s /\ a IN s
          ==> ?c. aff_ge {a} {b} INTER s = segment[a,c]"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"b:real^N = a") THENL
     [EXISTS_TAC (← q r"a:real^N") THEN
      ASM_REWRITE_TAC [SEGMENT_REFL, HALFLINE_REFL] THEN ASM SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"?u v:real^N. aff_ge {a} {b} INTER s = segment[u,v]")
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC COMPACT_CONVEX_COLLINEAR_SEGMENT THEN
      ASM_SIMP_TAC [CLOSED_INTER_COMPACT, CLOSED_AFF_GE, FINITE_SING] THEN
      ASM_SIMP_TAC [CONVEX_INTER, CONVEX_AFF_GE] THEN CONJ_TAC THENL
       [REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_INTER] THEN
        ASM_MESON_TAC [ENDS_IN_HALFLINE],
        MATCH_MP_TAC COLLINEAR_SUBSET THEN
        EXISTS_TAC (← q r"affine hull {a:real^N,b}") THEN
        REWRITE_TAC [COLLINEAR_AFFINE_HULL_COLLINEAR, COLLINEAR_2] THEN
        MATCH_MP_TAC (← SET_RULE (← q r"s SUBSET u ==> (s INTER t) SUBSET u")) THEN
        REWRITE_TAC [HALFLINE_SUBSET_AFFINE_HULL]],
      ASM_CASES_TAC (← q r"u:real^N = a") THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      ASM_CASES_TAC (← q r"v:real^N = a") THENL
       [ASM_MESON_TAC [SEGMENT_SYM], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"u IN aff_ge {a:real^N} {b} /\ v IN aff_ge {a} {b}")
      MP_TAC THENL [ASM_MESON_TAC [IN_INTER, ENDS_IN_SEGMENT], ALL_TAC] THEN
      GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [HALFLINE, IN_ELIM_THM] THEN
      DISCH_THEN (CONJUNCTS_THEN2
       (X_CHOOSE_THEN (← q r"s:real") MP_TAC) (X_CHOOSE_THEN (← q r"t:real") MP_TAC)) THEN
      MAP_EVERY ASM_CASES_TAC [← q r"s = &0", ← q r"t = &0"] THEN
      ASM_REWRITE_TAC [REAL_SUB_RZERO, VECTOR_MUL_LID, VECTOR_MUL_LZERO,
                      VECTOR_ADD_RID] THEN
      ASM_REWRITE_TAC [REAL_LE_LT] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"(a:real^N) IN segment[u,v]") MP_TAC THENL
       [ASM_MESON_TAC [IN_INTER, ENDS_IN_HALFLINE], ALL_TAC] THEN
      ASM_REWRITE_TAC [IN_SEGMENT, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"u:real") THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC [← VECTOR_ARITH
       (← q r"a = (&1 - u) % ((&1 - s) % a + s % b) + u % ((&1 - t) % a + t % b) <=>
        ((&1 - u) * s + u * t) % (b - a):real^N = vec 0")] THEN
      ASM_REWRITE_TAC [VECTOR_MUL_EQ_0, VECTOR_SUB_EQ] THEN
      ASM_SIMP_TAC [REAL_LE_MUL, REAL_SUB_LE, REAL_LT_IMP_LE, ← REAL_ARITH
       (← q r"&0 <= x /\ &0 <= y ==> (x + y = &0 <=> x = &0 /\ y = &0)")] THEN
      ASM_SIMP_TAC [REAL_ENTIRE, REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC])

  pure { AFFSIGN_0, AFF_GE_0_AFFINE_MULTIPLE_CONVEX, AFF_GE_0_MULTIPLE_AFFINE_CONVEX,
         AFF_GE_0_AFFINE_CONVEX_CONE, AFF_GE_0_N, AFF_GE_0_CONVEX_HULL,
         AFF_GE_0_CONVEX_HULL_ALT, AFF_GE_0_CONVEX_CONE_NEGATIONS, CONVEX_HULL_AFF_GE,
         POLYHEDRON_AFF_GE, CLOSED_AFF_GE, CONIC_AFF_GE_0, ANGLES_ADD_AFF_GE,
         AFF_GE_2_1_0_DROPOUT_3, AFF_GE_2_1_0_SEMIALGEBRAIC, HALFLINE_REFL,
         HALFLINE_EXPLICIT, HALFLINE, CLOSED_HALFLINE, SEGMENT_SUBSET_HALFLINE,
         ENDS_IN_HALFLINE, HALFLINE_SUBSET_AFFINE_HULL, HALFLINE_INTER_COMPACT_SEGMENT }
/- ------------------------------------------------------------------------- -/
/- Definition and properties of conv0; orthonormal triples of vectors in    -/
/- 3D; Flyspeck arcV is the same as angle even in degenerate cases.          -/
/- (flyspeck.ml 1782-2003)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FYG where
  conv0 : thm
  CONV0_INJECTIVE_LINEAR_IMAGE : thm
  CONV0_TRANSLATION : thm
  CONV0_SUBSET_CONVEX_HULL : thm
  CONV0_AFF_GT : thm
  CONVEX_HULL_CONV0_DECOMP : thm
  CONVEX_CONV0 : thm
  BOUNDED_CONV0 : thm
  MEASURABLE_CONV0 : thm
  NEGLIGIBLE_CONVEX_HULL_DIFF_CONV0 : thm
  MEASURE_CONV0_CONVEX_HULL : thm
  orthonormal : thm
  ORTHONORMAL_LINEAR_IMAGE : thm
  ORTHONORMAL_PERMUTE : thm
  ORTHONORMAL_CROSS : thm
  ORTHONORMAL_IMP_NONZERO : thm
  ORTHONORMAL_IMP_DISTINCT : thm
  ORTHONORMAL_IMP_INDEPENDENT : thm
  ORTHONORMAL_IMP_SPANNING : thm
  ORTHONORMAL_IMP_INDEPENDENT_EXPLICIT_0 : thm
  ORTHONORMAL_IMP_INDEPENDENT_EXPLICIT : thm
  arcV : thm
  ARCV_ANGLE : thm
  ARCV_LINEAR_IMAGE_EQ : thm
  ARCV_TRANSLATION_EQ : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYG [HolBase] (D : FlyspeckDeps) (BFYC : FYC) (BFYE : FYE) (BFYF : FYF) : ExceptT String IO FYG := do
  -- @@SCOPE BEGIN
  let { aff_gt_def, AFFSIGN, AFFSIGN_INJECTIVE_LINEAR_IMAGE, AFFSIGN_TRANSLATION, sgn_gt,
        .. } := BFYC
  let { AFF_GE_AFF_GT_DECOMP, CONVEX_AFF_GT, .. } := BFYE
  let { CONVEX_HULL_AFF_GE, .. } := BFYF
  let { vector_angle, .. } := D.gea
  let { angle, ANGLE_LINEAR_IMAGE_EQ, ANGLE_TRANSLATION_EQ, .. } := D.gec
  let { add_linear_invariants, ASM_MESON_TAC, MESON_TAC, new_definition, REAL_ARITH_TAC,
        REAL_RING, .. } := D.crd
  let { cross, CROSS_ORTHOGONAL_TRANSFORMATION, CROSS_TRIPLE, .. } := D.crs
  let { CARD_EQ_DIM, INDEPENDENT_3, .. } := D.qvectors
  let { MEASURABLE_CONVEX_HULL, MEASURE_NEGLIGIBLE_SYMDIFF, NEGLIGIBLE_CONVEX_HULL,
        .. } := D.qmeasure
  let { DOT_3, .. } := D.gm.qvectors
  let { ARITH, CART_EQ, CONJ_ASSOC, DIMINDEX_3, DOT_LZERO, DOT_RZERO, FORALL_3, orthogonal,
        ORTHOGONAL_TRANSFORMATION, REAL_MUL_LZERO, REAL_SUB_0, REAL_SUB_RZERO, VECTOR_3,
        VECTOR_MUL_LID, VECTOR_SUB_EQ, .. } := D.crd.thms
  let { ACS_0, .. } := D.gm.ra.tsw
  let { MEASURABLE_CONVEX, .. } := D.gm.ra.qmeasure
  let { NEGLIGIBLE_DIFF, NEGLIGIBLE_EMPTY, NEGLIGIBLE_UNION, NEGLIGIBLE_UNIONS,
        .. } := D.gm.ra.ts.cn.ms.qintegration3
  let { add_translation_invariants, ASM_ARITH_TAC, ASM_REAL_ARITH_TAC,
        GEOM_BASIS_MULTIPLE_TAC, REAL_ARITH, SET_RULE, SET_TAC, VECTOR_ARITH,
        .. } := D.gm.ra.ts.cn.cx.cvx
  let { REAL_LE_SQUARE, REAL_SUB_LZERO, .. } := D.gm.ra.ts.cn.cx.cpx
  let { CARD_CLAUSES, CARD_DELETE, CONTRAPOS_THM, DE_MORGAN_THM, FINITE_DELETE,
        FINITE_EMPTY, FINITE_IMAGE, FINITE_INSERT, .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, HAS_SIZE, IMAGE_CLAUSES, .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, MONO_EXISTS, NOT_IN_EMPTY, REAL_ADD_LID, REAL_ADD_RID,
        .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_LT_IMP_LE, .. } := D.gm.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_RID, REAL_MUL_RZERO, REAL_POS, SIMPLE_IMAGE, SUBSET,
        .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { pairwise, real_div, SUBSET_UNIV, UNION_EMPTY, .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { BASIS_COMPONENT, DIM_UNIV, DOT_BASIS_BASIS, DOT_LMUL, DOT_RMUL,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec1
  let { DOT_SYM, NORM_0, .. } := D.gm.ra.ts.cn.cx.cvx.vec2
  let { PAIRWISE_ORTHOGONAL_INDEPENDENT, .. } := D.gm.ra.ts.cn.cx.cvx.vec3
  let { VECTOR_SUB_REFL, .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { orthogonal_transformation, .. } := D.gm.ra.ts.cn.cx.cvx.det
  let { BOUNDED_SUBSET, .. } := D.gm.ra.ts.cn.cx.cvx.top1
  let { FINITE_IMP_BOUNDED, .. } := D.gm.ra.ts.cn.cx.cvx.top3
  let { BOUNDED_CONVEX_HULL, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qcvx1
  let { CONVEX_HULL_FINITE, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  -- @@SCOPE END

  let conv0 ← new_definition r"conv0 S:real^A->bool = affsign sgn_gt {} S"

  let CONV0_INJECTIVE_LINEAR_IMAGE ← prove
   r"!f s. linear f /\ (!x y. f x = f y ==> x = y)
           ==> conv0(IMAGE f s) = IMAGE f (conv0 s)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o GSYM o MATCH_MP AFFSIGN_INJECTIVE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC [conv0, IMAGE_CLAUSES])

  add_linear_invariants [CONV0_INJECTIVE_LINEAR_IMAGE]

  let CONV0_TRANSLATION ← prove
   r"!a s. conv0(IMAGE (\x. a + x) s) = IMAGE (\x. a + x) (conv0 s)"
   (REWRITE_TAC [conv0, ← GSYM AFFSIGN_TRANSLATION, IMAGE_CLAUSES])

  add_translation_invariants [CONV0_TRANSLATION]

  let CONV0_SUBSET_CONVEX_HULL ← prove
   r"!s. conv0 s SUBSET convex hull s"
   (REWRITE_TAC [conv0, AFFSIGN, sgn_gt, CONVEX_HULL_FINITE, UNION_EMPTY] THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
    REPEAT GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
    MESON_TAC [REAL_LT_IMP_LE])

  let CONV0_AFF_GT ← prove
   r"!s. conv0 s = aff_gt {} s"
   (REWRITE_TAC [conv0, aff_gt_def])

  let CONVEX_HULL_CONV0_DECOMP ← prove
   r"!s:real^N->bool.
          FINITE s
          ==> convex hull s = conv0 s UNION
                              UNIONS {convex hull (s DELETE a) | a | a IN s}"
   (REWRITE_TAC [CONV0_AFF_GT, CONVEX_HULL_AFF_GE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC AFF_GE_AFF_GT_DECOMP THEN
    ASM_REWRITE_TAC [FINITE_EMPTY] THEN SET_TAC [])

  let CONVEX_CONV0 ← prove
   r"!s. convex(conv0 s)"
   (REWRITE_TAC [CONV0_AFF_GT, CONVEX_AFF_GT])

  let BOUNDED_CONV0 ← prove
   r"!s:real^N->bool. bounded s ==> bounded(conv0 s)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC (← q r"convex hull s:real^N->bool") THEN
    ASM_SIMP_TAC [BOUNDED_CONVEX_HULL, CONV0_SUBSET_CONVEX_HULL])

  let MEASURABLE_CONV0 ← prove
   r"!s. bounded s ==> measurable(conv0 s)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_CONVEX THEN
    ASM_SIMP_TAC [CONVEX_CONV0, BOUNDED_CONV0])

  let NEGLIGIBLE_CONVEX_HULL_DIFF_CONV0 ← prove
   r"!s:real^N->bool.
          FINITE s /\ CARD s <= dimindex(:N) + 1
          ==> negligible(convex hull s DIFF conv0 s)"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [CONVEX_HULL_CONV0_DECOMP] THEN
    REWRITE_TAC [← SET_RULE (← q r"(s UNION t) DIFF s = t DIFF s")] THEN
    MATCH_MP_TAC NEGLIGIBLE_DIFF THEN MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
    ONCE_REWRITE_TAC [SIMPLE_IMAGE] THEN ASM_SIMP_TAC [FINITE_IMAGE] THEN
    REWRITE_TAC [FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC NEGLIGIBLE_CONVEX_HULL THEN
    ASM_SIMP_TAC [FINITE_DELETE, CARD_DELETE] THEN ASM_ARITH_TAC)

  let MEASURE_CONV0_CONVEX_HULL ← prove
   r"!s:real^N->bool.
          FINITE s /\ CARD s <= dimindex(:N) + 1
          ==> measure(conv0 s) = measure(convex hull s)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
    ASM_SIMP_TAC [MEASURABLE_CONVEX_HULL, FINITE_IMP_BOUNDED] THEN
    MATCH_MP_TAC NEGLIGIBLE_UNION THEN
    ASM_SIMP_TAC [NEGLIGIBLE_CONVEX_HULL_DIFF_CONV0] THEN
    ASM_SIMP_TAC [CONV0_SUBSET_CONVEX_HULL, NEGLIGIBLE_EMPTY,
                 ← SET_RULE (← q r"s SUBSET t ==> s DIFF t = {}")])

  /- Orthonormal triples of vectors in 3D. -/

  let orthonormal ← new_definition
   r"orthonormal e1 e2 e3 <=>
       e1 dot e1 = &1 /\ e2 dot e2 = &1 /\ e3 dot e3 = &1 /\
       e1 dot e2 = &0 /\ e1 dot e3 = &0 /\ e2 dot e3 = &0 /\
       &0 < (e1 cross e2) dot e3"

  let ORTHONORMAL_LINEAR_IMAGE ← prove
   r"!f. linear(f) /\ (!x. norm(f x) = norm x) /\
         (2 <= dimindex(:3) ==> det(matrix f) = &1)
         ==> !e1 e2 e3. orthonormal (f e1) (f e2) (f e3) <=>
                        orthonormal e1 e2 e3"
   (SIMP_TAC [DIMINDEX_3, ARITH, CONJ_ASSOC, ← GSYM ORTHOGONAL_TRANSFORMATION] THEN
    SIMP_TAC [orthonormal, CROSS_ORTHOGONAL_TRANSFORMATION] THEN
    SIMP_TAC [orthogonal_transformation, VECTOR_MUL_LID])

  add_linear_invariants [ORTHONORMAL_LINEAR_IMAGE]

  let ORTHONORMAL_PERMUTE ← prove
   r"!e1 e2 e3. orthonormal e1 e2 e3 ==> orthonormal e2 e3 e1"
   (REWRITE_TAC [orthonormal] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [← GSYM CROSS_TRIPLE] THEN ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [DOT_SYM] THEN ASM_REWRITE_TAC [])

  let ORTHONORMAL_CROSS ← prove
   r"!e1 e2 e3.
          orthonormal e1 e2 e3
          ==> e2 cross e3 = e1 /\ e3 cross e1 = e2 /\ e1 cross e2 = e3"
   (SUBGOAL_THEN
     (← q r"!e1 e2 e3. orthonormal e1 e2 e3 ==> e3 cross e1 = e2")
     (fun th => MESON_TAC [th, ORTHONORMAL_PERMUTE]) THEN
    GEOM_BASIS_MULTIPLE_TAC 1 (← q r"e1:real^3") THEN X_GEN_TAC (← q r"k:real") THEN
    REWRITE_TAC [orthonormal, DOT_LMUL, DOT_RMUL] THEN
    SIMP_TAC [DOT_BASIS_BASIS, DIMINDEX_3, ARITH, REAL_MUL_RID] THEN
    REWRITE_TAC [← REAL_RING (← q r"k * k = &1 <=> k = &1 \/ k = -- &1")] THEN
    ASM_CASES_TAC (← q r"k = -- &1") THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    ASM_CASES_TAC (← q r"k = &1") THEN
    ASM_REWRITE_TAC [VECTOR_MUL_LID, REAL_MUL_LID, REAL_MUL_RID] THEN
    SIMP_TAC [cross, DOT_3, VECTOR_3, CART_EQ, FORALL_3, DIMINDEX_3,
             BASIS_COMPONENT, DIMINDEX_3, ARITH, REAL_POS] THEN
    REWRITE_TAC [REAL_MUL_LZERO, REAL_SUB_RZERO, REAL_ADD_RID,
                REAL_MUL_LID] THEN
    REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"(e2:real^3)$1 = &0") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"(e3:real^3)$1 = &0") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [REAL_MUL_RZERO, REAL_SUB_RZERO, REAL_ADD_LID] THEN
    REWRITE_TAC [REAL_SUB_LZERO, REAL_MUL_RID] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"(u = &1 /\ v = &1 /\ w = &0 ==> a = b /\ --c = d \/ a = --b /\ c = d) /\
      (a = --b /\ c = d ==> x <= &0)
      ==> (u = &1 /\ v = &1 /\ w = &0 /\ &0 < x
           ==> a:real = b /\ --c:real = d)")) THEN
    CONJ_TAC THENL [CONV_TAC REAL_RING, ALL_TAC] THEN
    DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC) THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"&0 <= x * x /\ &0 <= y * y ==> --x * x + y * -- y <= &0")) THEN
    REWRITE_TAC [REAL_LE_SQUARE])

  let ORTHONORMAL_IMP_NONZERO ← prove
   r"!e1 e2 e3. orthonormal e1 e2 e3
                ==> ~(e1 = vec 0) /\ ~(e2 = vec 0) /\ ~(e3 = vec 0)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [DE_MORGAN_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [orthonormal, DOT_LZERO] THEN REAL_ARITH_TAC)

  let ORTHONORMAL_IMP_DISTINCT ← prove
   r"!e1 e2 e3. orthonormal e1 e2 e3 ==> ~(e1 = e2) /\ ~(e1 = e3) /\ ~(e2 = e3)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [DE_MORGAN_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [orthonormal, DOT_LZERO] THEN REAL_ARITH_TAC)

  let ORTHONORMAL_IMP_INDEPENDENT ← prove
   r"!e1 e2 e3. orthonormal e1 e2 e3 ==> independent {e1,e2,e3}"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN
    CONJ_TAC THENL [ALL_TAC, ASM SET_TAC [ORTHONORMAL_IMP_NONZERO]] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [orthonormal]) THEN
    REWRITE_TAC [pairwise, IN_INSERT, NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [orthogonal] THEN
    ASM_MESON_TAC [DOT_SYM])

  let ORTHONORMAL_IMP_SPANNING ← prove
   r"!e1 e2 e3. orthonormal e1 e2 e3 ==> span {e1,e2,e3} = (:real^3)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"(:real^3)", ← q r"{e1:real^3,e2,e3}"] CARD_EQ_DIM) THEN
    ASM_SIMP_TAC [ORTHONORMAL_IMP_INDEPENDENT, SUBSET_UNIV] THEN
    REWRITE_TAC [DIM_UNIV, DIMINDEX_3, HAS_SIZE, FINITE_INSERT, FINITE_EMPTY] THEN
    SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY, IN_INSERT] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP ORTHONORMAL_IMP_DISTINCT) THEN
    ASM_REWRITE_TAC [NOT_IN_EMPTY, ARITH] THEN SET_TAC [])

  let ORTHONORMAL_IMP_INDEPENDENT_EXPLICIT_0 ← prove
   r"!e1 e2 e3 t1 t2 t3.
          orthonormal e1 e2 e3
          ==> (t1 % e1 + t2 % e2 + t3 % e3 = vec 0 <=>
               t1 = &0 /\ t2 = &0 /\ t3 = &0)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC INDEPENDENT_3 THEN
    ASM_MESON_TAC [ORTHONORMAL_IMP_INDEPENDENT, ORTHONORMAL_IMP_DISTINCT])

  let ORTHONORMAL_IMP_INDEPENDENT_EXPLICIT ← prove
   r"!e1 e2 e3 s1 s2 s3 t1 t2 t3.
          orthonormal e1 e2 e3
          ==> (s1 % e1 + s2 % e2 + s3 % e3 = t1 % e1 + t2 % e2 + t3 % e3 <=>
               s1 = t1 /\ s2 = t2 /\ s3 = t3)"
   (SIMP_TAC [ORTHONORMAL_IMP_INDEPENDENT_EXPLICIT_0, REAL_SUB_0, ← VECTOR_ARITH
     (← q r"a % x + b % y + c % z:real^3 = a' % x + b' % y + c' % z <=>
      (a - a') % x + (b - b') % y + (c - c') % z = vec 0")])

  /- Flyspeck arcV is the same as angle even in degenerate cases. -/

  let arcV ← new_definition
   r"arcV u v w = acs (( (v - u) dot (w - u))/((norm (v-u)) * (norm (w-u))))"

  let ARCV_ANGLE ← prove
   r"!u v w:real^N. arcV u v w = angle(v,u,w)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [arcV, angle, vector_angle] THEN
    REWRITE_TAC [VECTOR_SUB_EQ] THEN
    ASM_CASES_TAC (← q r"v:real^N = u") THEN
    ASM_REWRITE_TAC [VECTOR_SUB_REFL, NORM_0, DOT_LZERO] THEN
    REWRITE_TAC [real_div, REAL_MUL_LZERO, ACS_0] THEN
    ASM_CASES_TAC (← q r"w:real^N = u") THEN
    ASM_REWRITE_TAC [VECTOR_SUB_REFL, NORM_0, DOT_RZERO] THEN
    REWRITE_TAC [real_div, REAL_MUL_LZERO, ACS_0])

  let ARCV_LINEAR_IMAGE_EQ ← prove
   r"!f a b c.
          linear f /\ (!x. norm(f x) = norm x)
          ==> arcV (f a) (f b) (f c) = arcV a b c"
   (REWRITE_TAC [ARCV_ANGLE, ANGLE_LINEAR_IMAGE_EQ])

  add_linear_invariants [ARCV_LINEAR_IMAGE_EQ]

  let ARCV_TRANSLATION_EQ ← prove
   r"!a b c d. arcV (a + b) (a + c) (a + d) = arcV b c d"
   (REWRITE_TAC [ARCV_ANGLE, ANGLE_TRANSLATION_EQ])

  add_translation_invariants [ARCV_TRANSLATION_EQ]

  pure { conv0, CONV0_INJECTIVE_LINEAR_IMAGE, CONV0_TRANSLATION, CONV0_SUBSET_CONVEX_HULL,
         CONV0_AFF_GT, CONVEX_HULL_CONV0_DECOMP, CONVEX_CONV0, BOUNDED_CONV0,
         MEASURABLE_CONV0, NEGLIGIBLE_CONVEX_HULL_DIFF_CONV0, MEASURE_CONV0_CONVEX_HULL,
         orthonormal, ORTHONORMAL_LINEAR_IMAGE, ORTHONORMAL_PERMUTE, ORTHONORMAL_CROSS,
         ORTHONORMAL_IMP_NONZERO, ORTHONORMAL_IMP_DISTINCT, ORTHONORMAL_IMP_INDEPENDENT,
         ORTHONORMAL_IMP_SPANNING, ORTHONORMAL_IMP_INDEPENDENT_EXPLICIT_0,
         ORTHONORMAL_IMP_INDEPENDENT_EXPLICIT, arcV, ARCV_ANGLE, ARCV_LINEAR_IMAGE_EQ,
         ARCV_TRANSLATION_EQ }
/- ------------------------------------------------------------------------- -/
/- Azimuth angle: existence.                                                 -/
/- (flyspeck.ml 2004-2146)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FYH where
  AZIM_EXISTS : thm
  azim_spec : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYH [HolBase] (D : FlyspeckDeps) (BFYA : FYA) (BFYB : FYB) (BFYG : FYG) : ExceptT String IO FYH := do
  -- @@SCOPE BEGIN
  let { pad2d3d, .. } := BFYA
  let { PAD2D3D_TAC, .. } := BFYB
  let { orthonormal, .. } := BFYG
  let { REAL_ARITH_TAC, .. } := D.crd
  let { cross, .. } := D.crs
  let { GEN_GEOM_ORIGIN_TAC, .. } := D.geomorigin
  let { ARITH, CART_EQ, CONJ_ASSOC, DIMINDEX_3, FORALL_3, LAMBDA_BETA, NORM_EQ_0,
        orthogonal, REAL_MUL_LZERO, REAL_SUB_RZERO, VECTOR_3, VECTOR_MUL_COMPONENT,
        VECTOR_MUL_LID, VECTOR_SUB_EQ, .. } := D.crd.thms
  let { COS_PI2, PI_POS, SIN_PI2, .. } := D.gm.ra.tse
  let { LINEAR_ROTATE2D, rotate2d, ROTATE2D_ADD, ROTATION_ROTATE2D_EXISTS_GEN,
        ROTATION_ROTATE2D_EXISTS_ORTHOGONAL_ORIENTED, .. } := D.gm.ra.tsi
  let { NORM_EQ_1, .. } := D.gm.ra.ts.qvectors
  let { GEOM_BASIS_MULTIPLE_TAC, MESON, REAL_ARITH, REAL_FIELD, VECTOR_ARITH,
        .. } := D.gm.ra.ts.cn.cx.cvx
  let { FORALL_2, VECTOR_2, .. } := D.gm.ra.ts.cn.cx.cpx
  let { REAL_EQ_RDIV_EQ, .. } := D.gm.ra.ts.cn.ms.ig.qsession
  let { VECTOR_MUL_LCANCEL_IMP, .. } := D.gm.ra.ts.cn.ms.ig.qvec
  let { DIMINDEX_2, EXISTS_REFL, .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { IMP_CONJ, IMP_IMP, .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { MONO_EXISTS, REAL_ADD_SYM, .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_LT_IMP_NZ, .. } := D.gm.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_RID, REAL_MUL_RZERO, RIGHT_AND_EXISTS_THM, RIGHT_EXISTS_AND_THM,
        RIGHT_EXISTS_IMP_THM, RIGHT_FORALL_IMP_THM, SKOLEM_THM,
        .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { SWAP_EXISTS_THM, .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { BASIS_COMPONENT, BASIS_NONZERO, COLLINEAR_LEMMA, DIST_0, DOT_BASIS, DOT_LMUL,
        DOT_RMUL, .. } := D.gm.ra.ts.cn.cx.cvx.vec1
  let { LINEAR_CMUL, NORM_0, NORM_BASIS, .. } := D.gm.ra.ts.cn.cx.cvx.vec2
  let { NORM_MUL, NORM_POS_LT, .. } := D.gm.ra.ts.cn.cx.cvx.vec3
  let { VEC_COMPONENT, VECTOR_ADD_COMPONENT, VECTOR_ADD_LDISTRIB, VECTOR_ADD_RID,
        VECTOR_MUL_ASSOC, VECTOR_MUL_EQ_0, VECTOR_MUL_LZERO, VECTOR_MUL_RZERO,
        VECTOR_SUB_COMPONENT, VECTOR_SUB_RZERO, .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  -- @@SCOPE END

  let AZIM_EXISTS ← (do
    let lemma ← prove
     r"cos(p) % e + sin(p) % rotate2d (pi / &2) e = rotate2d p e"
     (SIMP_TAC [CART_EQ, VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT,
        FORALL_2, rotate2d, LAMBDA_BETA, DIMINDEX_2, ARITH, VECTOR_2] THEN
      REWRITE_TAC [SIN_PI2, COS_PI2] THEN REAL_ARITH_TAC)
    prove
     r"!v w w1 w2.
            ?theta. &0 <= theta /\ theta < &2 * pi /\
                    ?h1 h2.
                       !e1 e2 e3.
                          orthonormal e1 e2 e3 /\
                          dist(w,v) % e3 = w - v /\
                          ~(w = v)
                          ==> ?psi r1 r2.
                                  w1 - v = (r1 * cos psi) % e1 +
                                           (r1 * sin psi) % e2 +
                                           h1 % (w - v) /\
                                  w2 - v = (r2 * cos (psi + theta)) % e1 +
                                           (r2 * sin (psi + theta)) % e2 +
                                           h2 % (w - v) /\
                                  (~collinear {v, w, w1} ==> &0 < r1) /\
                                  (~collinear {v, w, w2} ==> &0 < r2)"
      (GEN_GEOM_ORIGIN_TAC (← q r"v:real^3") ["e1", "e2", "e3"] THEN
      REWRITE_TAC [VECTOR_SUB_RZERO, DIST_0] THEN
      REPEAT GEN_TAC THEN REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN
      GEN_REWRITE_TAC id [SWAP_EXISTS_THM] THEN
      EXISTS_TAC (← q r"(w dot (w1:real^3)) / (w dot w)") THEN
      GEN_REWRITE_TAC id [SWAP_EXISTS_THM] THEN
      EXISTS_TAC (← q r"(w dot (w2:real^3)) / (w dot w)") THEN
      GEOM_BASIS_MULTIPLE_TAC 3 (← q r"w:real^3") THEN
      X_GEN_TAC (← q r"w:real") THEN GEN_REWRITE_TAC LAND_CONV
       [← REAL_ARITH (← q r"&0 <= w <=> w = &0 \/ &0 < w")] THEN
      STRIP_TAC THENL
       [ASM_REWRITE_TAC [VECTOR_MUL_LZERO, VECTOR_MUL_RZERO, NORM_0] THEN
        EXISTS_TAC (← q r"&0") THEN MP_TAC PI_POS THEN REAL_ARITH_TAC,
        ALL_TAC] THEN
      SIMP_TAC [DOT_LMUL, NORM_MUL, DIMINDEX_3, ARITH, DOT_RMUL, DOT_BASIS,
               VECTOR_MUL_COMPONENT, NORM_BASIS, BASIS_COMPONENT] THEN
      REWRITE_TAC [VECTOR_MUL_ASSOC, REAL_MUL_RID] THEN
      ASM_SIMP_TAC [← REAL_FIELD (← q r"&0 < w ==> (w * x) / (w * w) * w = x"),
                   ← REAL_ARITH (← q r"&0 < w ==> abs w = w")] THEN
      ASM_REWRITE_TAC [← VECTOR_ARITH
        (← q r"a % x:real^3 = a % y <=> a % (x - y) = vec 0")] THEN
      ASM_SIMP_TAC [VECTOR_MUL_EQ_0, REAL_LT_IMP_NZ, BASIS_NONZERO,
                   DIMINDEX_3, ARITH, VECTOR_SUB_EQ] THEN
      REWRITE_TAC [← MESON [] (← q r"(!e3. p e3 /\ e3 = a ==> q e3) <=> p a ==> q a")] THEN
      ONCE_REWRITE_TAC [← VECTOR_ARITH (← q r"x:real^3 = a + b + c <=> x - c = a + b")] THEN
      REPEAT GEN_TAC THEN
      ABBREV_TAC (← q r"v1:real^3 = w1 - (w1$3) % basis 3") THEN
      ABBREV_TAC (← q r"v2:real^3 = w2 - (w2$3) % basis 3") THEN
      SUBGOAL_THEN
       (← q r"(collinear{vec 0, w % basis 3, w1} <=>
         w1 - w1$3 % basis 3:real^3 = vec 0) /\
        (collinear{vec 0, w % basis 3, w2} <=>
         w2 - w2$3 % basis 3:real^3 = vec 0)")
       (fun th => REWRITE_TAC [th])
      THENL
       [ASM_SIMP_TAC [COLLINEAR_LEMMA, VECTOR_MUL_EQ_0, REAL_LT_IMP_NZ,
                     BASIS_NONZERO, DIMINDEX_3, ARITH] THEN
        MAP_EVERY EXPAND_TAC ["v1", "v2"] THEN
        SIMP_TAC [CART_EQ, VEC_COMPONENT, VECTOR_ADD_COMPONENT, FORALL_3,
                 VECTOR_MUL_COMPONENT, BASIS_COMPONENT, DIMINDEX_3, ARITH,
                 VECTOR_SUB_COMPONENT, REAL_MUL_RZERO, REAL_MUL_RID,
                 REAL_SUB_RZERO] THEN
        REWRITE_TAC [RIGHT_EXISTS_AND_THM] THEN
        CONV_TAC (BINOP_CONV (BINOP_CONV (ONCE_DEPTH_CONV SYM_CONV))) THEN
        ASM_SIMP_TAC [← GSYM REAL_EQ_RDIV_EQ, EXISTS_REFL] THEN REAL_ARITH_TAC,
        ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"(v1:real^3)$3 = &0 /\ (v2:real^3)$3 = &0") MP_TAC THENL
       [MAP_EVERY EXPAND_TAC ["v1", "v2"] THEN
        REWRITE_TAC [VECTOR_SUB_COMPONENT, VECTOR_MUL_COMPONENT, VECTOR_SUB_EQ] THEN
        SIMP_TAC [BASIS_COMPONENT, DIMINDEX_3, ARITH] THEN REAL_ARITH_TAC,
        ALL_TAC] THEN
      MAP_EVERY (fun t => SPEC_TAC (t, t)) [← q r"v2:real^3", ← q r"v1:real^3"] THEN
      POP_ASSUM_LIST (K ALL_TAC) THEN REWRITE_TAC [orthonormal] THEN
      SIMP_TAC [DOT_BASIS, BASIS_COMPONENT, DIMINDEX_3, ARITH] THEN
      ONCE_REWRITE_TAC [← TAUT (← q r"a /\ b /\ c /\ d /\ e /\ f <=>
                             d /\ e /\ a /\ b /\ c /\ f")] THEN
      REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
      PAD2D3D_TAC THEN REPEAT STRIP_TAC THEN
      SIMP_TAC [cross, VECTOR_3, pad2d3d, LAMBDA_BETA, DIMINDEX_3, ARITH] THEN
      REWRITE_TAC [IMP_IMP, ← GSYM CONJ_ASSOC] THEN
      ASM_CASES_TAC (← q r"v1:real^2 = vec 0") THEN ASM_REWRITE_TAC [NORM_POS_LT] THENL
       [MP_TAC (← ISPECL [← q r"basis 1:real^2", ← q r"v2:real^2"]
          ROTATION_ROTATE2D_EXISTS_GEN) THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:real") THEN
        STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
        MP_TAC (← ISPECL [← q r"e1:real^2", ← q r"basis 1:real^2"]
          ROTATION_ROTATE2D_EXISTS_GEN) THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"p:real") THEN STRIP_TAC THEN
        MAP_EVERY EXISTS_TAC [← q r"&0", ← q r"norm(v2:real^2)"] THEN
        ASM_REWRITE_TAC [NORM_POS_LT] THEN
        REWRITE_TAC [REAL_MUL_LZERO, VECTOR_MUL_LZERO, VECTOR_ADD_RID] THEN
        SUBGOAL_THEN (← q r"norm(e1:real^2) = &1 /\ norm(e2:real^2) = &1")
        STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC [NORM_EQ_1], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"e2 = rotate2d (pi / &2) e1") SUBST1_TAC THENL
         [MATCH_MP_TAC ROTATION_ROTATE2D_EXISTS_ORTHOGONAL_ORIENTED THEN
          ASM_REWRITE_TAC [NORM_EQ_1, orthogonal],
          ALL_TAC] THEN
        REWRITE_TAC [← GSYM VECTOR_MUL_ASSOC, ← GSYM VECTOR_ADD_LDISTRIB] THEN
        REWRITE_TAC [lemma] THEN ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
        REWRITE_TAC [ROTATE2D_ADD] THEN ASM_REWRITE_TAC [VECTOR_MUL_LID] THEN
        MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN
        EXISTS_TAC (← q r"norm(basis 1:real^2)") THEN
        ASM_SIMP_TAC [NORM_EQ_0, BASIS_NONZERO, DIMINDEX_2, ARITH] THEN
        FIRST_X_ASSUM (fun th => tactic_of do
          pure (GEN_REWRITE_TAC LAND_CONV [← SYM th])) THEN
        ONCE_REWRITE_TAC [← VECTOR_ARITH (← q r"a % b % x:real^2 = b % a % x")] THEN
        AP_TERM_TAC THEN
        SIMP_TAC [← GSYM (← MATCH_MP LINEAR_CMUL (← SPEC_ALL LINEAR_ROTATE2D))] THEN
        AP_TERM_TAC THEN
        ASM_SIMP_TAC [LINEAR_CMUL, LINEAR_ROTATE2D, VECTOR_MUL_LID],
        MP_TAC (← ISPECL [← q r"v1:real^2", ← q r"v2:real^2"] ROTATION_ROTATE2D_EXISTS_GEN) THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:real") THEN
        STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
        MP_TAC (← ISPECL [← q r"e1:real^2", ← q r"v1:real^2"] ROTATION_ROTATE2D_EXISTS_GEN) THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"p:real") THEN STRIP_TAC THEN
        MAP_EVERY EXISTS_TAC [← q r"norm(v1:real^2)", ← q r"norm(v2:real^2)"] THEN
        ASM_REWRITE_TAC [NORM_POS_LT] THEN
        SUBGOAL_THEN (← q r"norm(e1:real^2) = &1 /\ norm(e2:real^2) = &1")
        STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC [NORM_EQ_1], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"e2 = rotate2d (pi / &2) e1") SUBST1_TAC THENL
         [MATCH_MP_TAC ROTATION_ROTATE2D_EXISTS_ORTHOGONAL_ORIENTED THEN
          ASM_REWRITE_TAC [NORM_EQ_1, orthogonal],
          ALL_TAC] THEN
        REWRITE_TAC [← GSYM VECTOR_MUL_ASSOC, ← GSYM VECTOR_ADD_LDISTRIB] THEN
        REWRITE_TAC [lemma] THEN ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
        REWRITE_TAC [ROTATE2D_ADD] THEN ASM_REWRITE_TAC [VECTOR_MUL_LID] THEN
        MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN EXISTS_TAC (← q r"norm(v1:real^2)") THEN
        ASM_REWRITE_TAC [NORM_EQ_0] THEN
        FIRST_X_ASSUM (fun th => tactic_of do
          pure (GEN_REWRITE_TAC LAND_CONV [← SYM th])) THEN
        ONCE_REWRITE_TAC [← VECTOR_ARITH (← q r"a % b % x:real^2 = b % a % x")] THEN
        AP_TERM_TAC THEN
        SIMP_TAC [← GSYM (← MATCH_MP LINEAR_CMUL (← SPEC_ALL LINEAR_ROTATE2D))] THEN
        AP_TERM_TAC THEN
        ASM_SIMP_TAC [LINEAR_CMUL, LINEAR_ROTATE2D, VECTOR_MUL_LID]]))

  let azim_spec ←
     (REWRITE_RULE [SKOLEM_THM]
      (← REWRITE_RULE [RIGHT_EXISTS_IMP_THM] AZIM_EXISTS))

  pure { AZIM_EXISTS, azim_spec }
/- ------------------------------------------------------------------------- -/
/- Azimuth angle: definition and basic properties.                           -/
/- (flyspeck.ml 2147-2569)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FYI where
  azim_def : thm
  azim : thm
  AZIM_UNIQUE : thm
  AZIM_TRANSLATION : thm
  AZIM_LINEAR_IMAGE : thm
  AZIM_DEGENERATE : thm
  AZIM_REFL_ALT : thm
  AZIM_SPECIAL_SCALE : thm
  AZIM_SCALE_ALL : thm
  AZIM_ARG : thm
  REAL_CONTINUOUS_AT_AZIM_SHARP : thm
  REAL_CONTINUOUS_AT_AZIM : thm
  AZIM_REFL : thm
  AZIM_EQ : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYI [HolBase] (D : FlyspeckDeps) (BFYA : FYA) (BFYD : FYD) (BFYE : FYE) (BFYF : FYF) (BFYG : FYG) (BFYH : FYH) : ExceptT String IO FYI := do
  -- @@SCOPE BEGIN
  let { COLLINEAR_BASIS_3, COLLINEAR_SCALE_ALL, COLLINEAR_SPECIAL_SCALE, DROPOUT_BASIS_3,
        NOT_COPLANAR_NOT_COLLINEAR, .. } := BFYA
  let { AFF_GE_1_1_0, AFF_GT_2_1, .. } := BFYD
  let { AFF_GE_SPECIAL_SCALE, AFF_GE_SUBSET_AFFINE_HULL, AFF_GT_SPECIAL_SCALE, .. } := BFYE
  let { AFF_GE_2_1_0_DROPOUT_3, .. } := BFYF
  let { orthonormal, ORTHONORMAL_IMP_INDEPENDENT_EXPLICIT,
        ORTHONORMAL_IMP_INDEPENDENT_EXPLICIT_0, ORTHONORMAL_LINEAR_IMAGE, .. } := BFYG
  let { AZIM_EXISTS, .. } := BFYH
  let { EXPAND_QUANTS_CONV, PARTIAL_EXPAND_QUANTS_CONV, .. } := D
  let { add_linear_invariants, ASM_MESON_TAC, MESON_TAC, new_definition, REAL_RING,
        .. } := D.crd
  let { CROSS_BASIS, .. } := D.crs
  let { coplanar, .. } := D.qconvex
  let { DOT_CAUCHY_SCHWARZ_EQUAL, DROPOUT_ADD, DROPOUT_MUL, .. } := D.qvectors
  let { COLLINEAR_LINEAR_IMAGE_EQ, COLLINEAR_TRANSLATION_EQ,
        ORTHOGONAL_TRANSFORMATION_SURJECTIVE, .. } := D.qdeterminants
  let { REAL_EQ_INTEGERS_IMP, .. } := D.qfloor
  let { GEOM_ORIGIN_TAC, .. } := D.geomorigin
  let { REAL_CONTINUOUS_AT_WITHIN, .. } := D.gm.rzh
  let { REAL_CONTINUOUS_CONTINUOUS_AT_COMPOSE, .. } := D.gm.rzi
  let { REAL_CONTINUOUS_AT_ARG, .. } := D.gm.rzn
  let { COLLINEAR_3, .. } := D.gm.qvectors
  let { ARITH, CART_EQ, CONJ_ASSOC, DIMINDEX_3, DOT_LZERO, FORALL_3, LAMBDA_BETA, o_DEF,
        ORTHOGONAL_TRANSFORMATION, REAL_EQ_SQUARE_ABS, REAL_MUL_LZERO, REAL_SUB_RZERO,
        VECTOR_MUL_COMPONENT, VECTOR_MUL_LID, VECTOR_SUB_EQ, .. } := D.crd.thms
  let { CEXP_SUB, .. } := D.gm.ra.tsa
  let { CEXP_EULER, .. } := D.gm.ra.tsb
  let { CX_COS, CX_SIN, SIN_CIRCLE, .. } := D.gm.ra.tsc
  let { PI_POS, REAL_ABS_PI, .. } := D.gm.ra.tse
  let { SIN_COS_EQ, .. } := D.gm.ra.tsf
  let { ARG_0, ARG_EQ, ARG_EQ_0, ARG_UNIQUE, .. } := D.gm.ra.tsh
  let { dropout, DROPOUT_0, LINEAR_DROPOUT, .. } := D.gm.ra.qvectors
  let { CONTINUOUS_COMPLEX_MUL, .. } := D.gm.ra.ts.knc
  let { complex_div, COMPLEX_EQ, .. } := D.gm.ra.ts.cn.cxa
  let { COMPLEX_MUL_LZERO, COMPLEX_MUL_RID, COMPLEX_MUL_RZERO, .. } := D.gm.ra.ts.cn.cxb
  let { COMPLEX_CMUL, COMPLEX_DIV_REFL, COMPLEX_ENTIRE, COMPLEX_VEC_0, CX_ADD, CX_DIV,
        CX_INJ, CX_MUL, IM_CX, IM_DIV_CX, RE_CX, RE_DIV_CX, .. } := D.gm.ra.ts.cn.cxc
  let { COMPLEX_RING, .. } := D.gm.ra.ts.cn.cxd
  let { COMPLEX_FIELD, COMPLEX_INV_0, COMPLEX_INV_MUL, .. } := D.gm.ra.ts.cn.cxe
  let { COMPLEX_DIV_RMUL, COMPLEX_INV_EQ_0, .. } := D.gm.ra.ts.cn.cxf
  let { COMPLEX_BASIS, .. } := D.gm.ra.ts.cn.cxh
  let { real, REAL_CX, .. } := D.gm.ra.ts.cn.cxi
  let { add_translation_invariants, GEOM_BASIS_MULTIPLE_TAC, MESON, NORM_ARITH, REAL_ARITH,
        REAL_FIELD, SELECT_CONV, SET_RULE, VECTOR_ARITH, .. } := D.gm.ra.ts.cn.cx.cvx
  let { FORALL_2, .. } := D.gm.ra.ts.cn.cx.cpx
  let { INTEGER_CLOSED, .. } := D.gm.ra.ts.cn.ms.ig.qfloor
  let { CONTRAPOS_THM, DE_MORGAN_THM, DIMINDEX_2, ETA_AX, EXISTS_REFL, FINITE_EMPTY,
        FINITE_INSERT, .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { FUN_EQ_THM, INSERT_AC, .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, IN_SING, LEFT_IMP_EXISTS_THM, MONO_EXISTS, NOT_IN_EMPTY,
        REAL_ABS_DIV, REAL_ABS_MUL, REAL_ABS_NUM, REAL_ADD_LID, REAL_ADD_RID,
        REAL_DIV_EQ_0, REAL_DIV_LMUL, .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_LE_DIV, REAL_LE_LT, REAL_LE_RDIV_EQ, REAL_LE_REFL, REAL_LT_01, REAL_LT_DIV,
        REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_LDIV_EQ, REAL_LT_MUL, REAL_LT_MUL_EQ,
        .. } := D.gm.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_AC, REAL_MUL_LID, REAL_MUL_RID, REAL_MUL_RZERO, REAL_MUL_SYM,
        REAL_OF_NUM_LT, REAL_POS, REAL_POW_EQ_0, RIGHT_EXISTS_AND_THM, SUBSET,
        .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { UNWIND_THM1, .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { HULL_SUBSET, .. } := D.gm.ra.ts.cn.cx.cvx.misc
  let { BASIS_COMPONENT, BASIS_NONZERO, COLLINEAR_2, COLLINEAR_LEMMA, COLLINEAR_LEMMA_ALT,
        DIST_0, DIST_EQ_0, DOT_BASIS_BASIS, DOT_LADD, DOT_LMUL, DOT_RADD, DOT_RMUL,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec1
  let { DOT_SYM, LINEAR_ADD, LINEAR_CMUL, LINEAR_SUB, NORM_BASIS,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec2
  let { NORM_MUL, PRESERVES_NORM_INJECTIVE, .. } := D.gm.ra.ts.cn.cx.cvx.vec3
  let { dist, VEC_COMPONENT, VECTOR_ADD_COMPONENT, VECTOR_ADD_LDISTRIB, VECTOR_ADD_LID,
        VECTOR_ADD_RID, VECTOR_MUL_ASSOC, VECTOR_MUL_EQ_0, VECTOR_MUL_LCANCEL,
        VECTOR_MUL_LZERO, VECTOR_MUL_RZERO, VECTOR_SUB_RZERO,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { CONTINUOUS_CONST, .. } := D.gm.ra.ts.cn.cx.cvx.top3
  let { LINEAR_CONTINUOUS_AT, .. } := D.gm.ra.ts.cn.cx.cvx.top4
  let { REAL_EQ_ADD_LCANCEL, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.qsession
  let { QUANTIFY_SURJECTION_THM, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qvec
  -- @@SCOPE END

  let azim_def ← new_definition
   r"azim v w w1 w2 =
          if collinear {v,w,w1} \/ collinear {v,w,w2} then &0
          else @theta. &0 <= theta /\ theta < &2 * pi /\
                       ?h1 h2.
                           !e1 e2 e3.
                              orthonormal e1 e2 e3 /\
                              dist(w,v) % e3 = w - v /\
                              ~(w = v)
                              ==> ?psi r1 r2.
                                      w1 - v = (r1 * cos psi) % e1 +
                                               (r1 * sin psi) % e2 +
                                               h1 % (w - v) /\
                                      w2 - v = (r2 * cos (psi + theta)) % e1 +
                                               (r2 * sin (psi + theta)) % e2 +
                                               h2 % (w - v) /\
                                      &0 < r1 /\ &0 < r2"

  let azim ← prove
   r"!v w w1 w2:real^3.
          &0 <= azim v w w1 w2 /\ azim v w w1 w2 < &2 * pi /\
          ?h1 h2.
             !e1 e2 e3.
                orthonormal e1 e2 e3 /\
                dist(w,v) % e3 = w - v /\
                ~(w = v)
                ==> ?psi r1 r2.
                        w1 - v = (r1 * cos psi) % e1 +
                                 (r1 * sin psi) % e2 +
                                 h1 % (w - v) /\
                        w2 - v = (r2 * cos (psi + azim v w w1 w2)) % e1 +
                                 (r2 * sin (psi + azim v w w1 w2)) % e2 +
                                 h2 % (w - v) /\
                        (~collinear {v, w, w1} ==> &0 < r1) /\
                        (~collinear {v, w, w2} ==> &0 < r2)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [azim_def] THEN
    COND_CASES_TAC THENL
     [ALL_TAC,
      RULE_ASSUM_TAC (REWRITE_RULE [DE_MORGAN_THM]) THEN ASM_REWRITE_TAC [] THEN
      CONV_TAC SELECT_CONV THEN
      MP_TAC (← ISPECL [← q r"v:real^3", ← q r"w:real^3", ← q r"w1:real^3", ← q r"w2:real^3"]
          AZIM_EXISTS) THEN
      ASM_REWRITE_TAC []] THEN
    SIMP_TAC [PI_POS, REAL_LT_MUL, REAL_OF_NUM_LT, ARITH, REAL_LE_REFL] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [MP_TAC (← ISPECL [← q r"v:real^3", ← q r"w:real^3", ← q r"w2:real^3", ← q r"w1:real^3"]
       AZIM_EXISTS) THEN
      DISCH_THEN (CHOOSE_THEN (MP_TAC o CONJUNCT2 o CONJUNCT2)) THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"h2:real", ← q r"h1:real"] THEN
      DISCH_TAC THEN MAP_EVERY EXISTS_TAC [← q r"h1:real", ← q r"h2:real"] THEN
      MAP_EVERY X_GEN_TAC [← q r"e1:real^3", ← q r"e2:real^3", ← q r"e3:real^3"] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"e1:real^3", ← q r"e2:real^3", ← q r"e3:real^3"]) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC (← q r"psi:real") THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM, REAL_ADD_RID] THEN
      MAP_EVERY X_GEN_TAC [← q r"r2:real", ← q r"r1:real"] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [← q r"&0", ← q r"r2:real"],
      MP_TAC (← ISPECL [← q r"v:real^3", ← q r"w:real^3", ← q r"w1:real^3", ← q r"w2:real^3"]
         AZIM_EXISTS) THEN
      DISCH_THEN (CHOOSE_THEN (MP_TAC o CONJUNCT2 o CONJUNCT2)) THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"h1:real", ← q r"h2:real"] THEN
      DISCH_TAC THEN MAP_EVERY EXISTS_TAC [← q r"h1:real", ← q r"h2:real"] THEN
      MAP_EVERY X_GEN_TAC [← q r"e1:real^3", ← q r"e2:real^3", ← q r"e3:real^3"] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"e1:real^3", ← q r"e2:real^3", ← q r"e3:real^3"]) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC (← q r"psi:real") THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM, REAL_ADD_RID] THEN
      MAP_EVERY X_GEN_TAC [← q r"r1:real", ← q r"r2:real"] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [← q r"r1:real", ← q r"&0"]] THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV
     [← SET_RULE (← q r"{v,w,x} = {w,v,x}")]) THEN
    ONCE_REWRITE_TAC [COLLINEAR_3] THEN ASM_REWRITE_TAC [] THEN
    UNDISCH_THEN (← q r"dist(w:real^3,v) % e3 = w - v") (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [← GSYM DOT_CAUCHY_SCHWARZ_EQUAL] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [orthonormal]) THEN
    ASM_REWRITE_TAC [DOT_LADD, DOT_RADD, DOT_LMUL, DOT_RMUL, REAL_MUL_RZERO] THEN
    ONCE_REWRITE_TAC [DOT_SYM] THEN ASM_REWRITE_TAC [REAL_MUL_RZERO] THEN
    REWRITE_TAC [REAL_ADD_LID, REAL_ADD_RID, REAL_MUL_RID] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"(r * c) * (r * c):real = r pow 2 * c pow 2")] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"r * c + r * s + f:real = r * (s + c) + f")] THEN
    REWRITE_TAC [SIN_CIRCLE] THEN REWRITE_TAC [← REAL_RING
     (← q r"(d * h * d) pow 2 = (d * d) * (r * &1 + h * d * h * d) <=>
      d = &0 \/ r = &0")] THEN
    ASM_REWRITE_TAC [DIST_EQ_0, REAL_POW_EQ_0, ARITH] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [REAL_MUL_LZERO, DOT_LZERO])

  let AZIM_UNIQUE ← prove
   r"!v w w1 w2 h1 h2 r1 r2 e1 e2 e3 psi theta.
          &0 <= theta /\
          theta < &2 * pi /\
          orthonormal e1 e2 e3 /\
          dist(w,v) % e3 = w - v /\
          ~(w = v) /\
          &0 < r1 /\ &0 < r2 /\
          w1 - v = (r1 * cos psi) % e1 +
                   (r1 * sin psi) % e2 +
                   h1 % (w - v) /\
          w2 - v = (r2 * cos (psi + theta)) % e1 +
                   (r2 * sin (psi + theta)) % e2 +
                   h2 % (w - v)
          ==> azim v w w1 w2 = theta"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"~collinear{v:real^3,w,w2} /\ ~collinear {v,w,w1}")
    STRIP_ASSUME_TAC THENL
     [ONCE_REWRITE_TAC [← SET_RULE (← q r"{a,b,c} = {b,a,c}")] THEN
      ONCE_REWRITE_TAC [COLLINEAR_3] THEN REWRITE_TAC [COLLINEAR_LEMMA] THEN
      ASM_REWRITE_TAC [] THEN ASM_REWRITE_TAC [VECTOR_SUB_EQ] THEN
      UNDISCH_THEN (← q r"dist(w:real^3,v) % e3 = w - v") (SUBST1_TAC o SYM) THEN
      REWRITE_TAC [VECTOR_MUL_ASSOC, ← VECTOR_ARITH
       (← q r"a + b + c % x:real^N = d % x <=> a + b + (c - d) % x = vec 0")] THEN
      ASM_SIMP_TAC [ORTHONORMAL_IMP_INDEPENDENT_EXPLICIT_0] THEN
      ASM_SIMP_TAC [CONJ_ASSOC, REAL_LT_IMP_NZ, SIN_CIRCLE, ← REAL_RING
       (← q r"s pow 2 + c pow 2 = &1 ==> (r * c = &0 /\ r * s = &0 <=> r = &0)")],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(azim v w w1 w2 - theta) / (&2 * pi) = &0") MP_TAC THENL
     [ALL_TAC, MP_TAC PI_POS THEN CONV_TAC REAL_FIELD] THEN
    MATCH_MP_TAC REAL_EQ_INTEGERS_IMP THEN
    ASM_SIMP_TAC [REAL_SUB_RZERO, REAL_ABS_DIV, REAL_ABS_MUL, REAL_ABS_NUM,
         REAL_ABS_PI, REAL_LT_LDIV_EQ, REAL_LT_MUL, REAL_OF_NUM_LT, ARITH,
         PI_POS, INTEGER_CLOSED, REAL_MUL_LID] THEN
    MP_TAC (← ISPECL [← q r"v:real^3", ← q r"w:real^3", ← q r"w1:real^3", ← q r"w2:real^3"] azim) THEN
    ASM_REWRITE_TAC [] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC [← REAL_ARITH
     (← q r"&0 <= x /\ x < k /\ &0 <= y /\ y < k ==> abs(x - y) < k")] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"k1:real", ← q r"k2:real"] THEN
    DISCH_THEN (MP_TAC o SPECL [← q r"e1:real^3", ← q r"e2:real^3", ← q r"e3:real^3"]) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"phi:real", ← q r"s1:real", ← q r"s2:real"] THEN
    UNDISCH_THEN (← q r"dist(w:real^3,v) % e3 = w - v") (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC [ORTHONORMAL_IMP_INDEPENDENT_EXPLICIT] THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"a /\ b /\ c /\ d <=> (c /\ d) /\ a /\ b")] THEN
    DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN (MP_TAC o MATCH_MP (← REAL_FIELD
     (← q r"r * c = r' * c' /\ r * s = r' * s' /\ u:real = v
      ==> s pow 2 + c pow 2 = &1 /\ s' pow 2 + c' pow 2 = &1 /\
          &0 < r /\ (r pow 2 = r' pow 2 ==> r = r')
          ==> s = s' /\ c = c'")))) THEN
    ASM_REWRITE_TAC [SIN_CIRCLE, ← GSYM REAL_EQ_SQUARE_ABS] THEN
    ASM_SIMP_TAC [← REAL_ARITH
     (← q r"&0 < x /\ &0 < y ==> (abs x = abs y <=> x = y)")] THEN
    REWRITE_TAC [SIN_COS_EQ] THEN
    REWRITE_TAC [← REAL_ARITH
     (← q r"psi + theta = (phi + az) + x:real <=> psi = phi + x + (az - theta)")] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"m:real") STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [REAL_EQ_ADD_LCANCEL] THEN
    REWRITE_TAC [← REAL_ARITH
     (← q r"&2 * m * pi + x = &2 * n * pi <=> x = (n - m) * &2 * pi")] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"n:real") STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC [PI_POS, ← REAL_FIELD (← q r"&0 < pi ==> (x * &2 * pi) / (&2 * pi) = x"),
                 INTEGER_CLOSED])

  let AZIM_TRANSLATION ← prove
   r"!a v w w1 w2. azim (a + v) (a + w) (a + w1) (a + w2) = azim v w w1 w2"
   (REPEAT GEN_TAC THEN REWRITE_TAC [azim_def] THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"(a + w) - (a + v):real^3 = w - v"),
                ← VECTOR_ARITH (← q r"a + w:real^3 = a + v <=> w = v"),
                ← NORM_ARITH (← q r"dist(a + v,a + w) = dist(v,w)")] THEN
    REWRITE_TAC [← SET_RULE
     (← q r"{a + x,a + y,a + z} = IMAGE (\x:real^3. a + x) {x,y,z}")] THEN
    REWRITE_TAC [COLLINEAR_TRANSLATION_EQ])

  add_translation_invariants [AZIM_TRANSLATION]

  let AZIM_LINEAR_IMAGE ← prove
   r"!f. linear f /\ (!x. norm(f x) = norm x) /\
         (2 <= dimindex(:3) ==> det(matrix f) = &1)
         ==> !v w w1 w2. azim (f v) (f w) (f w1) (f w2) = azim v w w1 w2"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [azim_def] THEN
    ASM_SIMP_TAC [← GSYM LINEAR_SUB, dist] THEN
    MP_TAC (← ISPEC (← q r"f:real^3->real^3") QUANTIFY_SURJECTION_THM) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION,
                    ORTHOGONAL_TRANSFORMATION_SURJECTIVE],
      ALL_TAC] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (CONV_TAC (LAND_CONV (← EXPAND_QUANTS_CONV th)))) THEN
    ASM_SIMP_TAC [ORTHONORMAL_LINEAR_IMAGE] THEN
    ASM_SIMP_TAC [← GSYM LINEAR_CMUL, ← GSYM LINEAR_ADD] THEN
    SUBGOAL_THEN (← q r"!x y. (f:real^3->real^3) x = f y <=> x = y") ASSUME_TAC THENL
     [ASM_MESON_TAC [PRESERVES_NORM_INJECTIVE], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [← SET_RULE (← q r"{f x,f y,f z} = IMAGE f {x,y,z}")] THEN
    ASM_SIMP_TAC [COLLINEAR_LINEAR_IMAGE_EQ])

  add_linear_invariants [AZIM_LINEAR_IMAGE]

  let AZIM_DEGENERATE ← prove
   r"(!v w w1 w2. v = w ==> azim v w w1 w2 = &0) /\
     (!v w w1 w2. collinear{v,w,w1} ==> azim v w w1 w2 = &0) /\
     (!v w w1 w2. collinear{v,w,w2} ==> azim v w w1 w2 = &0)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [azim_def] THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [INSERT_AC, COLLINEAR_2])

  let AZIM_REFL_ALT ← prove
   r"!v x y. azim v v x y = &0"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC (← liftExcept (last (CONJUNCTS AZIM_DEGENERATE))) THEN
    REWRITE_TAC [COLLINEAR_2, INSERT_AC])

  let AZIM_SPECIAL_SCALE ← prove
   r"!a v w1 w2.
          &0 < a
          ==> azim (vec 0) (a % v) w1 w2 = azim (vec 0) v w1 w2"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [azim_def] THEN
    REWRITE_TAC [VECTOR_SUB_RZERO, DIST_0] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP (← MESON [REAL_LT_IMP_NZ, REAL_DIV_LMUL]
     (← q r"!a. &0 < a ==> (!y. ?x. a * x = y)"))) THEN
    DISCH_THEN (MP_TAC o MATCH_MP QUANTIFY_SURJECTION_THM) THEN
    DISCH_THEN (fun th => tactic_of do
      pure (CONV_TAC (RAND_CONV
        (← PARTIAL_EXPAND_QUANTS_CONV ["psi", "r1", "r2"] th)))) THEN
    REWRITE_TAC [VECTOR_MUL_ASSOC, REAL_MUL_SYM] THEN
    ASM_SIMP_TAC [VECTOR_MUL_EQ_0, REAL_LT_IMP_NZ] THEN
    ASM_SIMP_TAC [NORM_MUL, ← REAL_ARITH (← q r"&0 < a ==> abs a = a")] THEN
    REWRITE_TAC [← GSYM VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"a % x:real^3 = a % y <=> a % (x - y) = vec 0")] THEN
    ASM_SIMP_TAC [REAL_LT_IMP_NZ, VECTOR_MUL_EQ_0] THEN
    REWRITE_TAC [VECTOR_SUB_EQ] THEN
    ASM_SIMP_TAC [COLLINEAR_SPECIAL_SCALE, REAL_LT_IMP_NZ])

  let AZIM_SCALE_ALL ← (do
    let lemma ← MESON [REAL_LT_IMP_NZ, REAL_DIV_LMUL]
     (← q r"!a. &0 < a ==> (!y. ?x. a * x = y)")
    let SCALE_QUANT_TAC (side : ioconv → ioconv) (asm : term) (avoid : List String) :
        tactic := tactic_of do
      pure (MP_TAC (← MATCH_MP lemma (← ASSUME asm)) THEN
        DISCH_THEN (MP_TAC o MATCH_MP QUANTIFY_SURJECTION_THM) THEN
        DISCH_THEN (fun th => tactic_of do
          pure (CONV_TAC (side (← PARTIAL_EXPAND_QUANTS_CONV avoid th)))))
    prove
     r"!a v w1 w2.
          &0 < a /\ &0 < b /\ &0 < c
          ==> azim (vec 0) (a % v) (b % w1) (c % w2) = azim (vec 0) v w1 w2"
      (REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC [azim_def, COLLINEAR_SCALE_ALL, REAL_LT_IMP_NZ] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [VECTOR_SUB_RZERO] THEN
      ASM_SIMP_TAC [DIST_0, NORM_MUL, ← GSYM VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC [← REAL_ARITH (← q r"&0 < a ==> abs a = a"), VECTOR_MUL_LCANCEL] THEN
      ASM_SIMP_TAC [VECTOR_MUL_EQ_0, REAL_LT_IMP_NZ] THEN
      SCALE_QUANT_TAC RAND_CONV (← q r"&0 < a")  ["psi", "r1", "r2"] THEN
      SCALE_QUANT_TAC LAND_CONV (← q r"&0 < b")  ["psi", "h2", "r2"] THEN
      SCALE_QUANT_TAC LAND_CONV (← q r"&0 < c")  ["psi", "h1", "r1"] THEN
      ASM_SIMP_TAC [← GSYM VECTOR_MUL_ASSOC, ← GSYM VECTOR_ADD_LDISTRIB,
                   VECTOR_MUL_LCANCEL, REAL_LT_IMP_NZ, REAL_LT_MUL_EQ] THEN
      REWRITE_TAC [VECTOR_MUL_ASSOC, REAL_MUL_AC]))

  let AZIM_ARG ← (do
    let lemma ← prove
     r"(r * cos t) % basis 1 + (r * sin t) % basis 2 = Cx r * cexp(ii * Cx t)"
     (REWRITE_TAC [CEXP_EULER, COMPLEX_BASIS, ← GSYM CX_SIN, ← GSYM CX_COS,
                  COMPLEX_CMUL, CX_MUL] THEN
      CONV_TAC COMPLEX_RING)
    prove
     r"!x y:real^3. azim (vec 0) (basis 3) x y = Arg(dropout 3 y / dropout 3 x)"
      (REPEAT STRIP_TAC THEN
      ASM_CASES_TAC (← q r"collinear {vec 0:real^3,basis 3,x}") THENL
       [ASM_SIMP_TAC [AZIM_DEGENERATE] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [COLLINEAR_BASIS_3]) THEN
        ASM_REWRITE_TAC [COMPLEX_VEC_0, complex_div, COMPLEX_INV_0,
                        COMPLEX_MUL_RZERO, ARG_0],
        ALL_TAC] THEN
      ASM_CASES_TAC (← q r"collinear {vec 0:real^3,basis 3,y}") THENL
       [ASM_SIMP_TAC [AZIM_DEGENERATE] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [COLLINEAR_BASIS_3]) THEN
        ASM_REWRITE_TAC [COMPLEX_VEC_0, complex_div, COMPLEX_MUL_LZERO, ARG_0],
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"vec 0:real^3", ← q r"basis 3:real^3", ← q r"x:real^3", ← q r"y:real^3"]
            azim) THEN
      ABBREV_TAC (← q r"a = azim (vec 0) (basis 3) x (y:real^3)") THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM, VECTOR_SUB_RZERO, DIST_0] THEN
      MAP_EVERY X_GEN_TAC [← q r"h1:real", ← q r"h2:real"] THEN
      DISCH_THEN (MP_TAC o SPECL
       [← q r"basis 1:real^3", ← q r"basis 2:real^3", ← q r"basis 3:real^3"]) THEN
      SIMP_TAC [orthonormal, DOT_BASIS_BASIS, CROSS_BASIS, DIMINDEX_3, NORM_BASIS,
        ARITH, VECTOR_MUL_LID, BASIS_NONZERO, REAL_LT_01, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"psi:real", ← q r"r1:real", ← q r"r2:real"] THEN
      DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN
      REWRITE_TAC [DROPOUT_ADD, DROPOUT_MUL, DROPOUT_BASIS_3] THEN
      REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_ADD_RID, lemma] THEN
      REWRITE_TAC [complex_div, COMPLEX_INV_MUL] THEN
      ONCE_REWRITE_TAC [← ExceptT.mk (COMPLEX_RING
       (← q r"(a * b) * (c * d):complex = (a * c) * b * d"))] THEN
      REWRITE_TAC [← GSYM complex_div, ← GSYM CX_DIV, ← GSYM CEXP_SUB] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC ARG_UNIQUE THEN
      EXISTS_TAC (← q r"r2 / r1:real") THEN ASM_SIMP_TAC [REAL_LT_DIV] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [CX_ADD] THEN
      CONV_TAC COMPLEX_RING))

  let REAL_CONTINUOUS_AT_AZIM_SHARP ← prove
   r"!v w w1 w2.
          ~collinear{v,w,w1} /\ ~(w2 IN aff_ge {v,w} {w1})
          ==> (azim v w w1) real_continuous at w2"
   (GEOM_ORIGIN_TAC (← q r"v:real^3") THEN
    GEOM_BASIS_MULTIPLE_TAC 3 (← q r"w:real^3") THEN
    X_GEN_TAC (← q r"w:real") THEN ASM_CASES_TAC (← q r"w = &0") THENL
     [ASM_REWRITE_TAC [VECTOR_MUL_LZERO, INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    ASM_SIMP_TAC [REAL_LE_LT, COLLINEAR_SPECIAL_SCALE] THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    W (MP_TAC o PART_MATCH (lhs o rand) AFF_GE_SPECIAL_SCALE o
      rand o rand o lhand o snd) THEN
    ASM_REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY, IN_SING] THEN ANTS_TAC THENL
     [POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist CONJ) THEN
      ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN REWRITE_TAC [DE_MORGAN_THM] THEN
      DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THENL
       [ASM_REWRITE_TAC [COLLINEAR_2, INSERT_AC],
        ASM_REWRITE_TAC [COLLINEAR_2, INSERT_AC],
        ASM_SIMP_TAC [COLLINEAR_LEMMA_ALT, BASIS_NONZERO, DIMINDEX_3, ARITH] THEN
        MESON_TAC []],
      DISCH_THEN SUBST1_TAC THEN DISCH_TAC] THEN
    ASM_SIMP_TAC [AZIM_SPECIAL_SCALE, AZIM_ARG] THEN
    MATCH_MP_TAC (← REWRITE_RULE [o_DEF]
      REAL_CONTINUOUS_CONTINUOUS_AT_COMPOSE) THEN
    CONJ_TAC THENL
     [REWRITE_TAC [complex_div] THEN MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN
      REWRITE_TAC [CONTINUOUS_CONST, ETA_AX] THEN
      SIMP_TAC [LINEAR_CONTINUOUS_AT, LINEAR_DROPOUT, DIMINDEX_3, DIMINDEX_2,
               ARITH],
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_AT_WITHIN THEN
    MATCH_MP_TAC REAL_CONTINUOUS_AT_ARG THEN
    MP_TAC (← ISPECL [← q r"w2:real^3", ← q r"w1:real^3"] AFF_GE_2_1_0_DROPOUT_3) THEN
    ASM_REWRITE_TAC [] THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o
      GEN_REWRITE_RULE RAND_CONV [COLLINEAR_BASIS_3])) THEN
    SPEC_TAC (← q r"(dropout 3:real^3->real^2) w2", ← q r"v2:real^2") THEN
    SPEC_TAC (← q r"(dropout 3:real^3->real^2) w1", ← q r"v1:real^2") THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN
    GEOM_BASIS_MULTIPLE_TAC 1 (← q r"v1:complex") THEN
    X_GEN_TAC (← q r"w:real") THEN ASM_CASES_TAC (← q r"w = &0") THEN
    ASM_REWRITE_TAC [VECTOR_MUL_LZERO] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN ASM_REWRITE_TAC [] THEN
    DISCH_TAC THEN X_GEN_TAC (← q r"z:complex") THEN
    DISCH_THEN (K ALL_TAC : thm → tactic) THEN
    REWRITE_TAC [CONTRAPOS_THM, COMPLEX_BASIS, COMPLEX_CMUL] THEN
    REWRITE_TAC [COMPLEX_MUL_RID, RE_DIV_CX, IM_DIV_CX, real] THEN
    ASM_SIMP_TAC [REAL_DIV_EQ_0, REAL_LE_RDIV_EQ, REAL_MUL_LZERO] THEN
    STRIP_TAC THEN
    W (MP_TAC o PART_MATCH (lhs o rand) AFF_GE_1_1_0 o rand o snd) THEN
    ASM_REWRITE_TAC [COMPLEX_VEC_0, CX_INJ] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC (← q r"Re z / w") THEN
    ASM_SIMP_TAC [REAL_LE_DIV, REAL_LT_IMP_LE, COMPLEX_EQ] THEN
    ASM_SIMP_TAC [COMPLEX_CMUL, CX_DIV, COMPLEX_DIV_RMUL, CX_INJ] THEN
    REWRITE_TAC [RE_CX, IM_CX])

  let REAL_CONTINUOUS_AT_AZIM ← prove
   r"!v w w1 w2. ~coplanar{v,w,w1,w2} ==> (azim v w w1) real_continuous at w2"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_AT_AZIM_SHARP THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC [NOT_COPLANAR_NOT_COLLINEAR, INSERT_AC],
      DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE [SUBSET]
         AFF_GE_SUBSET_AFFINE_HULL)) THEN
      POP_ASSUM MP_TAC THEN REWRITE_TAC [coplanar, CONTRAPOS_THM] THEN
      REWRITE_TAC [← SET_RULE (← q r"{a,b} UNION {c} = {a,b,c}")] THEN
      DISCH_TAC THEN MAP_EVERY EXISTS_TAC
       [← q r"v:real^3", ← q r"w:real^3", ← q r"w1:real^3"] THEN
      SIMP_TAC [← SET_RULE (← q r"{a,b,c,d} SUBSET s <=> {a,b,c} SUBSET s /\ d IN s")] THEN
      ASM_REWRITE_TAC [HULL_SUBSET]])

  let AZIM_REFL ← prove
   r"!v0 v1 w. azim v0 v1 w w = &0"
   (GEOM_ORIGIN_TAC (← q r"v0:real^3") THEN
    GEOM_BASIS_MULTIPLE_TAC 3 (← q r"v1:real^3") THEN
    GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [← REAL_ARITH (← q r"&0 <= x <=> x = &0 \/ &0 < x")] THEN
    STRIP_TAC THEN ASM_SIMP_TAC [VECTOR_MUL_LZERO, AZIM_DEGENERATE] THEN
    ASM_SIMP_TAC [AZIM_SPECIAL_SCALE, AZIM_ARG, ARG_EQ_0] THEN
    X_GEN_TAC (← q r"w:real^3") THEN
    ASM_CASES_TAC (← q r"(dropout 3 :real^3->real^2) w = Cx(&0)") THEN
    ASM_SIMP_TAC [COMPLEX_DIV_REFL, REAL_CX, RE_CX, REAL_POS] THEN
    ASM_SIMP_TAC [complex_div, COMPLEX_MUL_LZERO, REAL_CX, RE_CX, REAL_POS])

  let AZIM_EQ ← prove
   r"!v0 v1 w x y.
          ~collinear{v0,v1,w} /\ ~collinear{v0,v1,x} /\ ~collinear{v0,v1,y}
          ==> (azim v0 v1 w x = azim v0 v1 w y <=> y IN aff_gt {v0,v1} {x})"
   (GEOM_ORIGIN_TAC (← q r"v0:real^3") THEN
    GEOM_BASIS_MULTIPLE_TAC 3 (← q r"v1:real^3") THEN
    GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [← REAL_ARITH (← q r"&0 <= x <=> x = &0 \/ &0 < x")] THEN
    STRIP_TAC THENL
     [ASM_REWRITE_TAC [VECTOR_MUL_LZERO, INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    ASM_SIMP_TAC [AZIM_SPECIAL_SCALE, REAL_LT_IMP_NZ, COLLINEAR_SPECIAL_SCALE] THEN
    REPEAT STRIP_TAC THEN
    W (MP_TAC o PART_MATCH (lhs o rand) AFF_GT_SPECIAL_SCALE o
      rand o rand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [IN_INSERT, FINITE_INSERT, FINITE_EMPTY, NOT_IN_EMPTY] THEN
      REPEAT CONJ_TAC THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
      TRY (RULE_ASSUM_TAC (REWRITE_RULE [INSERT_AC, COLLINEAR_2]) THEN
          FIRST_X_ASSUM (HolCore.Tactics.CONTR_TAC HolLight.HolBase.B)) THEN
      UNDISCH_TAC (← q r"~collinear {vec 0:real^3, basis 3, v1 % basis 3}") THEN
      REWRITE_TAC [COLLINEAR_LEMMA] THEN MESON_TAC [],
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC [AZIM_ARG] THEN CONV_TAC (LAND_CONV SYM_CONV) THEN
    W (MP_TAC o PART_MATCH (lhs o rand) ARG_EQ o lhand o snd) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [COLLINEAR_BASIS_3]) THEN
    ASM_REWRITE_TAC [complex_div, COMPLEX_ENTIRE, COMPLEX_INV_EQ_0] THEN
    ASM_REWRITE_TAC [← GSYM complex_div, ← GSYM COMPLEX_VEC_0] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC [← GSYM COMPLEX_VEC_0, ← ExceptT.mk (COMPLEX_FIELD
      (← q r"~(w = Cx(&0)) ==> (y / w = x * u / w <=> y = x * u)"))] THEN
    W (MP_TAC o PART_MATCH (lhs o rand) AFF_GT_2_1 o rand o rand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [← SET_RULE (← q r"DISJOINT {a,b} {x} <=> ~(x = a) /\ ~(x = b)")] THEN
      ASM_MESON_TAC [DROPOUT_BASIS_3, DROPOUT_0],
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC [IN_ELIM_THM, VECTOR_MUL_RZERO, VECTOR_ADD_LID] THEN
    ONCE_REWRITE_TAC [← MESON []
     (← q r"(?a b c. p c /\ q a b c /\ r b c) <=>
      (?c. p c /\ ?b. r b c /\ ?a. q a b c)")] THEN
    SIMP_TAC [← REAL_ARITH (← q r"a + b + c = &1 <=> a = &1 - b - c"), EXISTS_REFL] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"t:real") THEN REWRITE_TAC [] THEN AP_TERM_TAC THEN
    REWRITE_TAC [← GSYM COMPLEX_CMUL] THEN
    SIMP_TAC [CART_EQ, FORALL_2, FORALL_3, DIMINDEX_2, DIMINDEX_3,
             dropout, LAMBDA_BETA, BASIS_COMPONENT, ARITH, REAL_MUL_RID,
             VECTOR_MUL_COMPONENT, VEC_COMPONENT, REAL_MUL_RZERO, UNWIND_THM1,
             VECTOR_ADD_COMPONENT, REAL_ADD_LID, RIGHT_EXISTS_AND_THM] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"y:real = t + z <=> t = y - z"), EXISTS_REFL])

  pure { azim_def, azim, AZIM_UNIQUE, AZIM_TRANSLATION, AZIM_LINEAR_IMAGE,
         AZIM_DEGENERATE, AZIM_REFL_ALT, AZIM_SPECIAL_SCALE, AZIM_SCALE_ALL, AZIM_ARG,
         REAL_CONTINUOUS_AT_AZIM_SHARP, REAL_CONTINUOUS_AT_AZIM, AZIM_REFL, AZIM_EQ }
/- ------------------------------------------------------------------------- -/
/- Azimuth angle: equality, complement, pi and coplanarity.                  -/
/- (flyspeck.ml 2570-2991)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FYJ where
  AZIM_EQ_ALT : thm
  AZIM_EQ_0 : thm
  AZIM_EQ_0_ALT : thm
  AZIM_EQ_0_GE : thm
  AZIM_COMPL_EQ_0 : thm
  AZIM_COMPL : thm
  AZIM_EQ_PI_SYM : thm
  AZIM_EQ_0_SYM : thm
  AZIM_EQ_0_GE_ALT : thm
  AZIM_EQ_PI : thm
  AZIM_EQ_PI_ALT : thm
  AZIM_EQ_0_PI_IMP_COPLANAR : thm
  AZIM_SAME_WITHIN_AFF_GE : thm
  AZIM_SAME_WITHIN_AFF_GE_ALT : thm
  COLLINEAR_WITHIN_AFF_GE_COLLINEAR : thm
  AZIM_EQ_IMP : thm
  AZIM_EQ_0_GE_IMP : thm
  REAL_SGN_SIN_AZIM : thm
  AZIM_IN_UPPER_HALFSPACE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYJ [HolBase] (D : FlyspeckDeps) (BFYA : FYA) (BFYC : FYC) (BFYD : FYD) (BFYE : FYE) (BFYF : FYF) (BFYI : FYI) : ExceptT String IO FYJ := do
  -- @@SCOPE BEGIN
  let { COLLINEAR_BASIS_3, COLLINEAR_SPECIAL_SCALE, DROPOUT_BASIS_3,
        NOT_COPLANAR_NOT_COLLINEAR, .. } := BFYA
  let { AFF_GE_DISJOINT_DIFF, .. } := BFYC
  let { AFF_GE_1_2_0, AFF_GT_2_1, AFF_LT_1_1, AFF_LT_2_1, .. } := BFYD
  let { AFF_GE_AFF_GT_DECOMP, AFF_GE_EQ_AFFINE_HULL, AFF_GE_SCALE_LEMMA,
        AFF_LT_SPECIAL_SCALE, .. } := BFYE
  let { CONVEX_HULL_AFF_GE, .. } := BFYF
  let { azim, AZIM_ARG, AZIM_DEGENERATE, AZIM_EQ, AZIM_REFL, AZIM_REFL_ALT,
        AZIM_SPECIAL_SCALE, .. } := BFYI
  let { ASM_MESON_TAC, MESON_TAC, REAL_ARITH_TAC, REAL_RING, .. } := D.crd
  let { cross, CROSS_LMUL, CROSS_LZERO, .. } := D.crs
  let { COLLINEAR_3_AFFINE_HULL, COLLINEAR_3_IN_AFFINE_HULL, coplanar, .. } := D.qconvex
  let { DROPOUT_ADD, DROPOUT_MUL, SPAN_BREAKDOWN_EQ, .. } := D.qvectors
  let { GEOM_ORIGIN_TAC, .. } := D.geomorigin
  let { DOT_3, .. } := D.gm.qvectors
  let { AFFINE_HULL_2, .. } := D.gm.qconvex
  let { ARITH, CART_EQ, DIMINDEX_3, DOT_LZERO, FORALL_3, LAMBDA_BETA, REAL_MUL_LZERO,
        REAL_SUB_RZERO, VECTOR_3, VECTOR_MUL_COMPONENT, .. } := D.crd.thms
  let { REAL_EXP_POS_LT, .. } := D.gm.ra.tsb
  let { IM_CEXP, SIN_0, SIN_SUB, .. } := D.gm.ra.tsc
  let { COS_PI, SIN_PI, SIN_POS_PI, SIN_POS_PI_LE, .. } := D.gm.ra.tse
  let { ARG, ARG_0, ARG_DIV_CX, ARG_EQ_0, ARG_EQ_0_PI, ARG_EQ_PI, ARG_INV, ARG_MUL_CX,
        .. } := D.gm.ra.tsh
  let { dropout, .. } := D.gm.ra.qvectors
  let { REAL_SGN_0, .. } := D.gm.ra.ts.qsession
  let { complex, complex_div, complex_mul, IM, IM_DEF, RE, RE_DEF, .. } := D.gm.ra.ts.cn.cxa
  let { COMPLEX_ADD_LID, COMPLEX_MUL_RID, COMPLEX_MUL_RZERO, .. } := D.gm.ra.ts.cn.cxb
  let { COMPLEX_CMUL, COMPLEX_VEC_0, CX_DIV, CX_INJ, CX_INV, CX_MUL, IM_CX, IM_DIV_CX,
        IM_MUL_CX, IM_MUL_II, RE_CX, RE_DIV_CX, RE_MUL_II, .. } := D.gm.ra.ts.cn.cxc
  let { COMPLEX_RING, .. } := D.gm.ra.ts.cn.cxd
  let { COMPLEX_FIELD, COMPLEX_INV_0, COMPLEX_INV_DIV, COMPLEX_INV_MUL,
        .. } := D.gm.ra.ts.cn.cxe
  let { COMPLEX_NORM_NZ, .. } := D.gm.ra.ts.cn.cxf
  let { cnj, IM_COMPLEX_DIV_EQ_0, RE_COMPLEX_DIV_GE_0, REAL_SGN_IM_COMPLEX_DIV,
        .. } := D.gm.ra.ts.cn.cxg
  let { COMPLEX_BASIS, .. } := D.gm.ra.ts.cn.cxh
  let { real, REAL, .. } := D.gm.ra.ts.cn.cxi
  let { real_sgn, .. } := D.gm.ra.ts.cn.ms.qsession
  let { ASM_REAL_ARITH_TAC, GEOM_BASIS_MULTIPLE_TAC, REAL_ARITH, REAL_FIELD, SET_RULE,
        VECTOR_ARITH, VECTOR_ARITH_TAC, .. } := D.gm.ra.ts.cn.cx.cvx
  let { FORALL_2, REAL_SGN_DIV, VECTOR_2, .. } := D.gm.ra.ts.cn.cx.cpx
  let { DIMINDEX_2, EQ_TRANS, EXISTS_REFL, FINITE_EMPTY, FINITE_INSERT,
        .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { FUN_EQ_THM, IMAGE_CLAUSES, IMP_CONJ, INSERT_AC, INSERT_SUBSET,
        .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, IN_SING, IN_UNION, LEFT_AND_EXISTS_THM,
        LEFT_IMP_EXISTS_THM, NOT_IN_EMPTY, REAL_ADD_LID, REAL_DIV_1,
        .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_EQ_LDIV_EQ, REAL_INV_NEG, REAL_LE_LT, REAL_LT_IMP_NZ, REAL_LT_INV_EQ,
        REAL_LT_LDIV_EQ, REAL_LT_LE, REAL_LT_MUL, .. } := D.gm.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_RID, REAL_MUL_RNEG, REAL_MUL_RZERO,
        RIGHT_AND_EXISTS_THM, RIGHT_EXISTS_AND_THM, SIMPLE_IMAGE, SUBSET,
        .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { real_div, SWAP_EXISTS_THM, UNWIND_THM1, UNWIND_THM2,
        .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { HULL_INC, HULL_SUBSET, .. } := D.gm.ra.ts.cn.cx.cvx.misc
  let { BASIS_COMPONENT, BASIS_NONZERO, COLLINEAR_2, COLLINEAR_LEMMA, COLLINEAR_LEMMA_ALT,
        DOT_LMUL, .. } := D.gm.ra.ts.cn.cx.cvx.vec1
  let { SPAN_EMPTY, .. } := D.gm.ra.ts.cn.cx.cvx.vec3
  let { VEC_COMPONENT, VECTOR_ADD_COMPONENT, VECTOR_ADD_LDISTRIB, VECTOR_ADD_LID,
        VECTOR_ADD_RDISTRIB, VECTOR_MUL_ASSOC, VECTOR_MUL_LZERO, VECTOR_MUL_RZERO,
        VECTOR_SUB_COMPONENT, VECTOR_SUB_RZERO, .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { REAL_SGN_INEQS, REAL_SGN_MUL, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.qsession
  let { DISJOINT_EMPTY, DISJOINT_INSERT, UNIONS_1, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qses
  let { AFFINE_HULL_EQ_SPAN, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qcvx1
  let { CONVEX_HULL_SUBSET_AFFINE_HULL, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  -- @@SCOPE END

  let AZIM_EQ_ALT ← prove
   r"!v0 v1 w x y.
          ~collinear{v0,v1,w} /\ ~collinear{v0,v1,x} /\ ~collinear{v0,v1,y}
          ==> (azim v0 v1 w x = azim v0 v1 w y <=> x IN aff_gt {v0,v1} {y})"
   (ASM_SIMP_TAC [← GSYM AZIM_EQ] THEN MESON_TAC [])

  let AZIM_EQ_0 ← prove
   r"!v0 v1 w x.
          ~collinear{v0,v1,w} /\ ~collinear{v0,v1,x}
          ==> (azim v0 v1 w x = &0 <=> w IN aff_gt {v0,v1} {x})"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"azim v0 v1 w x = azim v0 v1 w w") THEN CONJ_TAC THENL
     [REWRITE_TAC [AZIM_REFL],
      ASM_SIMP_TAC [AZIM_EQ]])

  let AZIM_EQ_0_ALT ← prove
   r"!v0 v1 w x.
          ~collinear{v0,v1,w} /\ ~collinear{v0,v1,x}
          ==> (azim v0 v1 w x = &0 <=> x IN aff_gt {v0,v1} {w})"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"azim v0 v1 w x = azim v0 v1 w w") THEN CONJ_TAC THENL
     [REWRITE_TAC [AZIM_REFL],
      ASM_SIMP_TAC [AZIM_EQ_ALT]])

  let AZIM_EQ_0_GE ← prove
   r"!v0 v1 w x.
          ~collinear{v0,v1,w} /\ ~collinear{v0,v1,x}
          ==> (azim v0 v1 w x = &0 <=> w IN aff_ge {v0,v1} {x})"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"v1:real^3 = v0") THENL
     [ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2], STRIP_TAC] THEN
    W (MP_TAC o PART_MATCH (lhs o rand) AFF_GE_AFF_GT_DECOMP o
        rand o rand o snd) THEN
    ANTS_TAC THENL
     [SIMP_TAC [FINITE_INSERT, FINITE_EMPTY, DISJOINT_INSERT, DISJOINT_EMPTY] THEN
      REWRITE_TAC [IN_SING] THEN
      CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE [COLLINEAR_2, INSERT_AC]) THEN
      FIRST_ASSUM (HolCore.Tactics.CONTR_TAC HolLight.HolBase.B),
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC [AZIM_EQ_0] THEN
    REWRITE_TAC [SIMPLE_IMAGE, IMAGE_CLAUSES, UNIONS_1] THEN
    REWRITE_TAC [← SET_RULE (← q r"{x} DELETE x = {}")] THEN
    REWRITE_TAC [AFF_GE_EQ_AFFINE_HULL, IN_UNION] THEN
    ASM_SIMP_TAC [← GSYM COLLINEAR_3_AFFINE_HULL])

  let AZIM_COMPL_EQ_0 ← prove
   r"!z w w1 w2.
          ~collinear {z,w,w1} /\ ~collinear {z,w,w2} /\ azim z w w1 w2 = &0
          ==> azim z w w2 w1 = &0"
   (REWRITE_TAC [IMP_CONJ] THEN
    GEOM_ORIGIN_TAC (← q r"z:real^3") THEN
    GEOM_BASIS_MULTIPLE_TAC 3 (← q r"w:real^3") THEN
    X_GEN_TAC (← q r"w:real") THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
    ASM_CASES_TAC (← q r"w = &0") THEN ASM_REWRITE_TAC [] THENL
     [ASM_REWRITE_TAC [VECTOR_MUL_LZERO, INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    ASM_SIMP_TAC [AZIM_SPECIAL_SCALE, COLLINEAR_SPECIAL_SCALE, AZIM_ARG] THEN
    REWRITE_TAC [ARG_EQ_0, real, IM_COMPLEX_DIV_EQ_0, RE_COMPLEX_DIV_GE_0] THEN
    REWRITE_TAC [complex_mul, RE, IM, cnj] THEN REAL_ARITH_TAC)

  let AZIM_COMPL ← prove
   r"!z w w1 w2.
          ~collinear {z,w,w1} /\ ~collinear {z,w,w2}
          ==> azim z w w2 w1 = if azim z w w1 w2 = &0 then &0
                               else &2 * pi - azim z w w1 w2"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THENL
     [ASM_MESON_TAC [AZIM_COMPL_EQ_0], ALL_TAC] THEN
    DISCH_THEN (fun th => POP_ASSUM MP_TAC THEN MP_TAC th) THEN
    GEOM_ORIGIN_TAC (← q r"z:real^3") THEN
    GEOM_BASIS_MULTIPLE_TAC 3 (← q r"w:real^3") THEN
    X_GEN_TAC (← q r"w:real") THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
    ASM_CASES_TAC (← q r"w = &0") THEN ASM_REWRITE_TAC [] THENL
     [ASM_REWRITE_TAC [VECTOR_MUL_LZERO, INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    ASM_SIMP_TAC [AZIM_SPECIAL_SCALE, COLLINEAR_SPECIAL_SCALE, AZIM_ARG] THEN
    REWRITE_TAC [COLLINEAR_BASIS_3] THEN REWRITE_TAC [ARG_EQ_0] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"(dropout 3:real^3->real^2) w2 /
                  (dropout 3:real^3->real^2) w1") ARG_INV) THEN
    ASM_REWRITE_TAC [COMPLEX_INV_DIV])

  let AZIM_EQ_PI_SYM ← prove
   r"!z w w1 w2.
          ~collinear {z, w, w1} /\ ~collinear {z, w, w2}
          ==> (azim z w w1 w2 = pi <=> azim z w w2 w1 = pi)"
   (REPEAT STRIP_TAC THEN
    W (MP_TAC o PART_MATCH (lhs o rand) AZIM_COMPL o lhand o rand o snd) THEN
    ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC)

  let AZIM_EQ_0_SYM ← prove
   r"!z w w1 w2.
          ~collinear {z, w, w1} /\ ~collinear {z, w, w2}
          ==> (azim z w w1 w2 = &0 <=> azim z w w2 w1 = &0)"
   (MESON_TAC [AZIM_COMPL_EQ_0])

  let AZIM_EQ_0_GE_ALT ← prove
   r"!v0 v1 w x.
          ~collinear{v0,v1,w} /\ ~collinear{v0,v1,x}
          ==> (azim v0 v1 w x = &0 <=> x IN aff_ge {v0,v1} {w})"
   (ASM_MESON_TAC [AZIM_EQ_0_SYM, AZIM_EQ_0_GE])

  let AZIM_EQ_PI ← prove
   r"!v0 v1 w x.
          ~collinear{v0,v1,w} /\ ~collinear{v0,v1,x}
          ==> (azim v0 v1 w x = pi <=> w IN aff_lt {v0,v1} {x})"
   (GEOM_ORIGIN_TAC (← q r"v0:real^3") THEN
    GEOM_BASIS_MULTIPLE_TAC 3 (← q r"v1:real^3") THEN
    GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [← REAL_ARITH (← q r"&0 <= x <=> x = &0 \/ &0 < x")] THEN
    STRIP_TAC THENL
     [ASM_REWRITE_TAC [VECTOR_MUL_LZERO, INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    ASM_SIMP_TAC [AZIM_SPECIAL_SCALE, REAL_LT_IMP_NZ,
                 COLLINEAR_SPECIAL_SCALE] THEN
    REPEAT STRIP_TAC THEN
    W (MP_TAC o PART_MATCH (lhs o rand) AFF_LT_SPECIAL_SCALE o
      rand o rand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [IN_INSERT, FINITE_INSERT, FINITE_EMPTY, NOT_IN_EMPTY] THEN
      REPEAT CONJ_TAC THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
      TRY (RULE_ASSUM_TAC (REWRITE_RULE [INSERT_AC, COLLINEAR_2]) THEN
          FIRST_X_ASSUM (HolCore.Tactics.CONTR_TAC HolLight.HolBase.B)) THEN
      UNDISCH_TAC (← q r"~collinear {vec 0:real^3, basis 3, v1 % basis 3}") THEN
      REWRITE_TAC [COLLINEAR_LEMMA] THEN MESON_TAC [],
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC [AZIM_ARG] THEN CONV_TAC (LAND_CONV SYM_CONV) THEN
    CONV_TAC (LAND_CONV SYM_CONV) THEN REWRITE_TAC [ARG_EQ_PI] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
    (← q r"(dropout 3 (w:real^3)) IN aff_lt {vec 0:real^2} {dropout 3 (x:real^3)}") THEN
    CONJ_TAC THENL
     [REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [COLLINEAR_BASIS_3] THEN
      SPEC_TAC (← q r"(dropout 3:real^3->real^2) x", ← q r"y:complex") THEN
      SPEC_TAC (← q r"(dropout 3:real^3->real^2) w", ← q r"v:complex") THEN
      GEOM_BASIS_MULTIPLE_TAC 1 (← q r"v:complex") THEN
      X_GEN_TAC (← q r"v:real") THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
      ASM_CASES_TAC (← q r"v = &0") THEN ASM_REWRITE_TAC [VECTOR_MUL_LZERO] THEN
      REWRITE_TAC [COMPLEX_CMUL, COMPLEX_BASIS, COMPLEX_VEC_0] THEN
      SIMP_TAC [ARG_DIV_CX, COMPLEX_MUL_RID] THEN
      REWRITE_TAC [real, RE_DIV_CX, IM_DIV_CX, CX_INJ] THEN
      ASM_SIMP_TAC [REAL_LT_LDIV_EQ, REAL_EQ_LDIV_EQ, REAL_MUL_LZERO] THEN
      REPEAT STRIP_TAC THEN
      W (MP_TAC o PART_MATCH (lhs o rand) AFF_LT_1_1 o rand o rand o snd) THEN
      ASM_REWRITE_TAC [DISJOINT_INSERT, DISJOINT_EMPTY, IN_SING] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [COMPLEX_CMUL, IN_ELIM_THM, COMPLEX_MUL_RZERO] THEN
      ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"t1 + t2 = &1 <=> t1 = &1 - t2")] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM2, COMPLEX_ADD_LID] THEN
      EQ_TAC THENL
       [REWRITE_TAC [← GSYM real, REAL] THEN
        DISCH_THEN (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
        EXISTS_TAC (← q r"v / Re y") THEN REWRITE_TAC [← GSYM CX_MUL, CX_INJ] THEN
        CONJ_TAC THENL
         [ALL_TAC, REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD],
        DISCH_THEN (X_CHOOSE_THEN (← q r"t:real")
         (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        ASM_SIMP_TAC [CX_INJ, ← REAL_ARITH (← q r"x < &0 ==> ~(x = &0)"), ← ExceptT.mk (COMPLEX_FIELD
          (← q r"~(t = Cx(&0)) ==> (v = t * y <=> y = v / t)"))] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [← GSYM CX_DIV] THEN
        REWRITE_TAC [RE_CX, IM_CX]] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"x < &0 <=> &0 < --x")] THEN
      REWRITE_TAC [real_div, ← GSYM REAL_MUL_RNEG, ← GSYM REAL_INV_NEG] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [REAL_LT_INV_EQ] THEN
      ASM_REAL_ARITH_TAC,
      W (MP_TAC o PART_MATCH (lhs o rand) AFF_LT_2_1 o rand o rand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [← SET_RULE (← q r"DISJOINT {a,b} {x} <=> ~(x = a) /\ ~(x = b)")] THEN
        CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC (REWRITE_RULE [COLLINEAR_2, INSERT_AC]) THEN
        FIRST_ASSUM (HolCore.Tactics.CONTR_TAC HolLight.HolBase.B),
        DISCH_THEN SUBST1_TAC] THEN
      W (MP_TAC o PART_MATCH (lhs o rand) AFF_LT_1_1 o rand o lhand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [← SET_RULE (← q r"DISJOINT {a} {x} <=> ~(x = a)")] THEN
        ASM_MESON_TAC [COLLINEAR_BASIS_3],
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_ADD_LID, IN_ELIM_THM] THEN
      ONCE_REWRITE_TAC [← REAL_ARITH (← q r"s + t = &1 <=> s = &1- t")] THEN
      ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM2] THEN
      GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV) [SWAP_EXISTS_THM] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM2] THEN
      ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN AP_TERM_TAC THEN
      REWRITE_TAC [FUN_EQ_THM, RIGHT_EXISTS_AND_THM] THEN X_GEN_TAC (← q r"t:real") THEN
      AP_TERM_TAC THEN
      SIMP_TAC [CART_EQ, FORALL_2, FORALL_3, DIMINDEX_2, DIMINDEX_3,
               dropout, LAMBDA_BETA, BASIS_COMPONENT, ARITH, REAL_MUL_RID,
               VECTOR_MUL_COMPONENT, VEC_COMPONENT, REAL_MUL_RZERO, UNWIND_THM1,
               VECTOR_ADD_COMPONENT, REAL_ADD_LID, RIGHT_EXISTS_AND_THM] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"x:real = t + y <=> t = x - y")] THEN
      REWRITE_TAC [EXISTS_REFL]])

  let AZIM_EQ_PI_ALT ← prove
   r"!v0 v1 w x.
          ~collinear{v0,v1,w} /\ ~collinear{v0,v1,x}
          ==> (azim v0 v1 w x = pi <=> x IN aff_lt {v0,v1} {w})"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP AZIM_EQ_PI_SYM) THEN
    ASM_SIMP_TAC [AZIM_EQ_PI])

  let AZIM_EQ_0_PI_IMP_COPLANAR ← prove
   r"!v0 v1 w1 w2.
          azim v0 v1 w1 w2 = &0 \/ azim v0 v1 w1 w2 = pi
          ==> coplanar {v0,v1,w1,w2}"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"collinear {v0:real^3,v1,w1}") THENL
     [MP_TAC (← ISPECL [← q r"v0:real^3", ← q r"v1:real^3", ← q r"w1:real^3", ← q r"w2:real^3"]
                  NOT_COPLANAR_NOT_COLLINEAR) THEN
      ASM_REWRITE_TAC [] THEN CONV_TAC (fun t => TAUT t),
      POP_ASSUM MP_TAC] THEN
    ASM_CASES_TAC (← q r"collinear {v0:real^3,v1,w2}") THENL
     [MP_TAC (← ISPECL [← q r"v0:real^3", ← q r"v1:real^3", ← q r"w2:real^3", ← q r"w1:real^3"]
                  NOT_COPLANAR_NOT_COLLINEAR) THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [INSERT_AC] THEN CONV_TAC (fun t => TAUT t),
      POP_ASSUM MP_TAC] THEN
    MAP_EVERY (fun t => SPEC_TAC (t, t))
     [← q r"w2:real^3", ← q r"w1:real^3", ← q r"v1:real^3", ← q r"v0:real^3"] THEN
    GEOM_ORIGIN_TAC (← q r"v0:real^3") THEN
    GEOM_BASIS_MULTIPLE_TAC 3 (← q r"v1:real^3") THEN
    X_GEN_TAC (← q r"w:real") THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
    ASM_CASES_TAC (← q r"w = &0") THEN ASM_REWRITE_TAC [] THENL
     [ASM_REWRITE_TAC [VECTOR_MUL_LZERO, INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    SIMP_TAC [AZIM_SPECIAL_SCALE] THEN
    ASM_SIMP_TAC [AZIM_ARG, COLLINEAR_SPECIAL_SCALE] THEN
    REWRITE_TAC [COLLINEAR_BASIS_3, ARG_EQ_0_PI] THEN
    REWRITE_TAC [real, IM_COMPLEX_DIV_EQ_0] THEN
    REWRITE_TAC [complex_mul, cnj, IM, RE] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"x * --y + a * b = &0 <=> x * y = a * b")] THEN
    REWRITE_TAC [RE_DEF, IM_DEF] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    DISCH_TAC THEN DISCH_TAC THEN
    SIMP_TAC [dropout, LAMBDA_BETA, DIMINDEX_3, ARITH, DIMINDEX_2] THEN
    DISCH_TAC THEN REWRITE_TAC [coplanar] THEN
    MAP_EVERY EXISTS_TAC [← q r"vec 0:real^3", ← q r"w % basis 3:real^3", ← q r"w1:real^3"] THEN
    ONCE_REWRITE_TAC [← SET_RULE (← q r"{a,b,c,d} = d INSERT {a,b,c}")] THEN
    ONCE_REWRITE_TAC [INSERT_SUBSET] THEN REWRITE_TAC [HULL_SUBSET] THEN
    SIMP_TAC [AFFINE_HULL_EQ_SPAN, IN_INSERT, HULL_INC] THEN
    REWRITE_TAC [SPAN_BREAKDOWN_EQ, SPAN_EMPTY, IN_SING] THEN
    REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_SUB_RZERO] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    SIMP_TAC [CART_EQ, DIMINDEX_2, FORALL_2, FORALL_3, dropout, LAMBDA_BETA,
             DIMINDEX_2, DIMINDEX_3, ARITH, VEC_COMPONENT, ARITH,
             VECTOR_SUB_COMPONENT, VECTOR_MUL_COMPONENT, BASIS_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC [REAL_MUL_RZERO, REAL_SUB_RZERO] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
    REWRITE_TAC [RIGHT_EXISTS_AND_THM] THEN
    ASM_SIMP_TAC [EXISTS_REFL, ← REAL_FIELD
     (← q r"&0 < w ==> (x - k * w * &1 - y = &0 <=> k = (x - y) / w)")] THEN
    SUBGOAL_THEN (← q r"~((w1:real^3)$2 = &0) \/ ~((w2:real^3)$1 = &0)")
    STRIP_ASSUME_TAC THENL
     [REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING,
      EXISTS_TAC (← q r"(w2:real^3)$2 / (w1:real^3)$2") THEN
      REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD,
      EXISTS_TAC (← q r"(w2:real^3)$1 / (w1:real^3)$1") THEN
      REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD])

  let AZIM_SAME_WITHIN_AFF_GE ← prove
   r"!a u v w z.
          v IN aff_ge {a} {u,w} /\ ~collinear{a,u,v} /\ ~collinear{a,u,w}
          ==> azim a u v z = azim a u w z"
   (GEOM_ORIGIN_TAC (← q r"a:real^3") THEN
    GEOM_BASIS_MULTIPLE_TAC 3 (← q r"u:real^3") THEN
    X_GEN_TAC (← q r"u:real") THEN ASM_CASES_TAC (← q r"u = &0") THEN
    ASM_SIMP_TAC [AZIM_DEGENERATE, VECTOR_MUL_LZERO, REAL_LE_LT] THEN
    ASM_SIMP_TAC [AZIM_SPECIAL_SCALE, COLLINEAR_SPECIAL_SCALE] THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"w:real^3 = vec 0") THENL
     [ASM_REWRITE_TAC [COLLINEAR_2, INSERT_AC], ALL_TAC] THEN
    ASM_SIMP_TAC [AFF_GE_SCALE_LEMMA] THEN
    REWRITE_TAC [COLLINEAR_BASIS_3, AZIM_ARG] THEN
    ASM_SIMP_TAC [AFF_GE_1_2_0, BASIS_NONZERO, ARITH, DIMINDEX_3,
     ← SET_RULE (← q r"DISJOINT {a} {b,c} <=> ~(b = a) /\ ~(c = a)")] THEN
    REWRITE_TAC [IMP_CONJ, LEFT_IMP_EXISTS_THM, IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real", ← q r"b:real"] THEN DISCH_TAC THEN DISCH_TAC THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"dropout 3:real^3->real^2")) THEN
    REWRITE_TAC [DROPOUT_ADD, DROPOUT_MUL, DROPOUT_BASIS_3] THEN
    REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_ADD_LID] THEN
    DISCH_THEN SUBST1_TAC THEN REPEAT DISCH_TAC THEN
    REWRITE_TAC [COMPLEX_CMUL] THEN
    REWRITE_TAC [complex_div, COMPLEX_INV_MUL, ← GSYM CX_INV] THEN
    ONCE_REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"a * b * c:complex = b * a * c"))] THEN
    MATCH_MP_TAC ARG_MUL_CX THEN REWRITE_TAC [REAL_LT_INV_EQ] THEN
    ASM_REWRITE_TAC [REAL_LT_LE] THEN ASM_MESON_TAC [VECTOR_MUL_LZERO])

  let AZIM_SAME_WITHIN_AFF_GE_ALT ← prove
   r"!a u v w z.
          v IN aff_ge {a} {u,w} /\ ~collinear{a,u,v} /\ ~collinear{a,u,w}
          ==> azim a u z v = azim a u z w"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP AZIM_SAME_WITHIN_AFF_GE) THEN
    ASM_CASES_TAC (← q r"collinear {a:real^3,u,z}") THEN
    ASM_SIMP_TAC [AZIM_DEGENERATE] THEN
    W (MP_TAC o PART_MATCH (lhs o rand) AZIM_COMPL o lhand o snd) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
    W (MP_TAC o PART_MATCH (lhs o rand) AZIM_COMPL o rand o snd) THEN
    ASM_SIMP_TAC [])

  let COLLINEAR_WITHIN_AFF_GE_COLLINEAR ← prove
   r"!a u v w:real^N.
          v IN aff_ge {a} {u,w} /\ collinear{a,u,w} ==> collinear{a,v,w}"
   (GEOM_ORIGIN_TAC (← q r"a:real^N") THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"w:real^N = vec 0") THENL
     [ASM_REWRITE_TAC [COLLINEAR_2, INSERT_AC], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"u:real^N = vec 0") THENL
     [ONCE_REWRITE_TAC [AFF_GE_DISJOINT_DIFF] THEN
      ASM_REWRITE_TAC [← SET_RULE (← q r"{a} DIFF {a,b} = {}")] THEN
      REWRITE_TAC [← GSYM CONVEX_HULL_AFF_GE] THEN
      ONCE_REWRITE_TAC [← SET_RULE (← q r"{z,v,w} = {z,w,v}")] THEN
      ASM_SIMP_TAC [COLLINEAR_3_AFFINE_HULL] THEN
      MESON_TAC [CONVEX_HULL_SUBSET_AFFINE_HULL, SUBSET],
      ONCE_REWRITE_TAC [← SET_RULE (← q r"{z,v,w} = {z,w,v}")] THEN
      ASM_REWRITE_TAC [COLLINEAR_LEMMA_ALT] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_TAC (← q r"a:real"))) THEN
      ASM_SIMP_TAC [AFF_GE_1_2_0, ← SET_RULE
       (← q r"DISJOINT {a} {b,c} <=> ~(b = a) /\ ~(c = a)")] THEN
      REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"b:real", ← q r"c:real"] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [← GSYM VECTOR_ADD_RDISTRIB, VECTOR_MUL_ASSOC] THEN
      MESON_TAC []])

  let AZIM_EQ_IMP ← prove
   r"!v0 v1 w x y.
       ~collinear {v0, v1, w} /\
       ~collinear {v0, v1, y} /\
       x IN aff_gt {v0, v1} {y}
       ==> azim v0 v1 w x = azim v0 v1 w y"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"v1:real^3 = v0") THENL
     [ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"collinear {v0:real^3,v1,x}") THENL
     [ALL_TAC, ASM_SIMP_TAC [AZIM_EQ_ALT]] THEN
    UNDISCH_TAC (← q r"collinear {v0:real^3,v1,x}") THEN
    MATCH_MP_TAC (← TAUT
     (← q r"(s /\ p ==> r) ==> p ==> ~q /\ ~r /\ s ==> t")) THEN
    ASM_SIMP_TAC [COLLINEAR_3_IN_AFFINE_HULL] THEN
    ASM_CASES_TAC (← q r"y:real^3 = v0") THEN
    ASM_SIMP_TAC [HULL_INC, IN_INSERT] THEN
    ASM_CASES_TAC (← q r"y:real^3 = v1") THEN
    ASM_SIMP_TAC [HULL_INC, IN_INSERT] THEN
    ASM_SIMP_TAC [AFF_GT_2_1, ← SET_RULE
     (← q r"DISJOINT {a,b} {c} <=> ~(c = a) /\ ~(c = b)")] THEN
    REWRITE_TAC [AFFINE_HULL_2, IN_ELIM_THM, LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"t1:real", ← q r"t2:real", ← q r"t3:real", ← q r"s1:real", ← q r"s2:real"] THEN
    DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o AP_TERM (← q r"(%) (inv t3) :real^3->real^3")) THEN
    ASM_SIMP_TAC [VECTOR_ADD_LDISTRIB, VECTOR_MUL_ASSOC, REAL_MUL_LINV,
                 REAL_LT_IMP_NZ, ← VECTOR_ARITH
                  (← q r"x:real^N = y + z + &1 % w <=> w = x - (y + z)")] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC (← q r"inv t3 * s1 - inv t3 * t1:real") THEN
    EXISTS_TAC (← q r"inv t3 * s2 - inv t3 * t2:real") THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [← REAL_FIELD
       (← q r"&0 < t ==> (inv t * a - inv t * b + inv t * c - inv t * d = &1 <=>
                    (a + c) - (b + d) = t)")] THEN
      ASM_REAL_ARITH_TAC,
      VECTOR_ARITH_TAC])

  let AZIM_EQ_0_GE_IMP ← prove
   r"!v0 v1 w x. x IN aff_ge {v0, v1} {w} ==> azim v0 v1 w x = &0"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"collinear {v0:real^3,v1,w}") THEN
    ASM_SIMP_TAC [AZIM_DEGENERATE] THEN
    ASM_CASES_TAC (← q r"collinear {v0:real^3,v1,x}") THEN
    ASM_SIMP_TAC [AZIM_DEGENERATE] THEN ASM_MESON_TAC [AZIM_EQ_0_GE_ALT])

  let REAL_SGN_SIN_AZIM ← prove
   r"!v w x y. real_sgn(sin(azim v w x y)) =
               real_sgn(((w - v) cross (x - v)) dot (y - v))"
   (GEOM_ORIGIN_TAC (← q r"v:real^3") THEN REWRITE_TAC [VECTOR_SUB_RZERO] THEN
    GEOM_BASIS_MULTIPLE_TAC 3 (← q r"w:real^3") THEN
    X_GEN_TAC (← q r"w:real") THEN ASM_CASES_TAC (← q r"w = &0") THEN
    ASM_REWRITE_TAC [VECTOR_MUL_LZERO, CROSS_LZERO, DOT_LZERO, REAL_SGN_0,
                    AZIM_REFL_ALT, SIN_0] THEN
    ASM_REWRITE_TAC [REAL_LE_LT] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [AZIM_SPECIAL_SCALE, CROSS_LMUL, DOT_LMUL] THEN
    REWRITE_TAC [REAL_SGN_MUL] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [real_sgn] THEN
    ASM_REWRITE_TAC [REAL_MUL_LID, AZIM_ARG] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"real_sgn(Im(dropout 3 (y:real^3) / dropout 3 (x:real^3)))") THEN
    CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [REAL_SGN_IM_COMPLEX_DIV] THEN AP_TERM_TAC THEN
      SIMP_TAC [CART_EQ, DIMINDEX_3, FORALL_3, cross, VECTOR_3, DOT_3, dropout,
               LAMBDA_BETA, ARITH, cnj, complex_mul, RE_DEF, IM_DEF, DIMINDEX_2,
               complex, VECTOR_2, BASIS_COMPONENT] THEN REAL_ARITH_TAC] THEN

    SPEC_TAC (← q r"(dropout 3:real^3->real^2) x", ← q r"z:complex") THEN
    SPEC_TAC (← q r"(dropout 3:real^3->real^2) y", ← q r"w:complex") THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN GEOM_BASIS_MULTIPLE_TAC 1 (← q r"z:complex") THEN
    REWRITE_TAC [COMPLEX_CMUL, COMPLEX_BASIS, COMPLEX_MUL_RID] THEN
    X_GEN_TAC (← q r"x:real") THEN DISCH_TAC THEN X_GEN_TAC (← q r"z:complex") THEN
    ASM_CASES_TAC (← q r"x = &0") THENL
     [ASM_REWRITE_TAC [complex_div, COMPLEX_INV_0, COMPLEX_MUL_RZERO] THEN
      REWRITE_TAC [ARG_0, SIN_0, IM_CX, REAL_SGN_0],
      SUBGOAL_THEN (← q r"&0 < x") ASSUME_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]] THEN
    ASM_SIMP_TAC [ARG_DIV_CX, IM_DIV_CX, REAL_SGN_DIV] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [real_sgn] THEN
    ASM_REWRITE_TAC [REAL_DIV_1] THEN ASM_CASES_TAC (← q r"z = Cx(&0)") THEN
    ASM_REWRITE_TAC [IM_CX, ARG_0, SIN_0] THEN
    GEN_REWRITE_TAC (funpow 3 RAND_CONV) [ARG] THEN
    REWRITE_TAC [IM_MUL_CX, REAL_SGN_MUL] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [real_sgn] THEN
    ASM_REWRITE_TAC [COMPLEX_NORM_NZ, REAL_MUL_LID] THEN
    REWRITE_TAC [IM_CEXP, RE_MUL_II, IM_MUL_II, RE_CX, REAL_SGN_MUL] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [real_sgn] THEN
    REWRITE_TAC [REAL_EXP_POS_LT, REAL_MUL_LID])

  let AZIM_IN_UPPER_HALFSPACE ← prove
   r"!v w x y. azim v w x y <= pi <=>
               &0 <= ((w - v) cross (x - v)) dot (y - v)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"&0 <= sin(azim v w x y)") THEN CONJ_TAC THENL
     [EQ_TAC THEN SIMP_TAC [SIN_POS_PI_LE, azim] THEN
      MP_TAC (← ISPEC (← q r"azim v w x y - pi") SIN_POS_PI) THEN
      REWRITE_TAC [SIN_SUB, SIN_PI, COS_PI, azim,
                  ← REAL_ARITH (← q r"x - pi < pi <=> x < &2 * pi")] THEN
      REAL_ARITH_TAC,
      ONCE_REWRITE_TAC [← GSYM REAL_SGN_INEQS] THEN
      REWRITE_TAC [REAL_SGN_SIN_AZIM]])

  pure { AZIM_EQ_ALT, AZIM_EQ_0, AZIM_EQ_0_ALT, AZIM_EQ_0_GE, AZIM_COMPL_EQ_0, AZIM_COMPL,
         AZIM_EQ_PI_SYM, AZIM_EQ_0_SYM, AZIM_EQ_0_GE_ALT, AZIM_EQ_PI, AZIM_EQ_PI_ALT,
         AZIM_EQ_0_PI_IMP_COPLANAR, AZIM_SAME_WITHIN_AFF_GE, AZIM_SAME_WITHIN_AFF_GE_ALT,
         COLLINEAR_WITHIN_AFF_GE_COLLINEAR, AZIM_EQ_IMP, AZIM_EQ_0_GE_IMP,
         REAL_SGN_SIN_AZIM, AZIM_IN_UPPER_HALFSPACE }
/- ------------------------------------------------------------------------- -/
/- Dihedral angle and relation to azimuth angle.                             -/
/- (flyspeck.ml 2992-3330)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FYK where
  dihV : thm
  DIHV : thm
  DIHV_TRANSLATION_EQ : thm
  DIHV_LINEAR_IMAGE : thm
  DIHV_SPECIAL_SCALE : thm
  DIHV_RANGE : thm
  COS_AZIM_DIHV : thm
  AZIM_DIHV_SAME : thm
  AZIM_DIHV_COMPL : thm
  AZIM_DIVH : thm
  AZIM_DIHV_EQ_0 : thm
  AZIM_DIHV_EQ_PI : thm
  AZIM_EQ_0_PI_EQ_COPLANAR : thm
  DIHV_EQ_0_PI_EQ_COPLANAR : thm
  DIHV_SYM : thm
  DIHV_NEG : thm
  DIHV_NEG_0 : thm
  DIHV_ARCV : thm
  AZIM_DIHV_SAME_STRONG : thm
  AZIM_ARCV : thm
  COLLINEAR_AZIM_0_OR_PI : thm
  REAL_CONTINUOUS_WITHIN_DIHV_COMPOSE : thm
  REAL_CONTINUOUS_AT_DIHV_COMPOSE : thm
  REAL_CONTINUOUS_WITHINREAL_DIHV_COMPOSE : thm
  REAL_CONTINUOUS_ATREAL_DIHV_COMPOSE : thm
  REAL_CONTINUOUS_AT_DIHV : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYK [HolBase] (D : FlyspeckDeps) (BFYA : FYA) (BFYB : FYB) (BFYC : FYC) (BFYG : FYG) (BFYI : FYI) (BFYJ : FYJ) : ExceptT String IO FYK := do
  -- @@SCOPE BEGIN
  let { COLLINEAR_BASIS_3, COLLINEAR_SPECIAL_SCALE, NOT_COPLANAR_NOT_COLLINEAR, .. } := BFYA
  let { COPLANAR, PAD2D3D_TAC, .. } := BFYB
  let { GEOM_HORIZONTAL_PLANE_TAC, .. } := BFYC
  let { ARCV_ANGLE, orthonormal, .. } := BFYG
  let { azim, AZIM_DEGENERATE, AZIM_SPECIAL_SCALE, .. } := BFYI
  let { AZIM_EQ_0_PI_IMP_COPLANAR, .. } := BFYJ
  let { let_CONV, .. } := D
  let { VECTOR_ANGLE_LINEAR_IMAGE_EQ, VECTOR_ANGLE_LMUL, VECTOR_ANGLE_NEG2,
        VECTOR_ANGLE_RMUL, .. } := D.gea
  let { COLLINEAR_VECTOR_ANGLE, CONTINUOUS_WITHIN_CX_VECTOR_ANGLE_COMPOSE,
        REAL_CONTINUOUS_WITHIN_VECTOR_ANGLE, .. } := D.geb
  let { angle, ANGLE_RANGE, ANGLE_SYM, COS_ANGLE, .. } := D.gec
  let { add_linear_invariants, ASM_MESON_TAC, MESON_TAC, new_definition, REAL_ARITH_TAC,
        REAL_RING, .. } := D.crd
  let { CROSS_BASIS, .. } := D.crs
  let { COLLINEAR_3_DOT_MULTIPLES, DOT_CAUCHY_SCHWARZ_EQUAL, .. } := D.qvectors
  let { GEOM_ORIGIN_TAC, .. } := D.geomorigin
  let { WITHINREAL_UNIV, .. } := D.gm.rzf
  let { REAL_CONTINUOUS_CONTINUOUS_AT_COMPOSE, .. } := D.gm.rzi
  let { CONTINUOUS_CONTINUOUS_WITHINREAL, REAL_CONTINUOUS_CONTINUOUS,
        REAL_CONTINUOUS_REAL_CONTINUOUS_WITHINREAL, .. } := D.gm.rzn
  let { DOT_3, PRESERVES_NORM_PRESERVES_DOT, .. } := D.gm.qvectors
  let { ARITH, CART_EQ, CONJ_ASSOC, CONTINUOUS_MUL, CONTINUOUS_SUB, DIMINDEX_3, DOT_EQ_0,
        FORALL_3, o_DEF, orthogonal, REAL_ENTIRE, REAL_MUL_LZERO, VECTOR_MUL_COMPONENT,
        VECTOR_MUL_LID, VECTOR_SUB_EQ, .. } := D.crd.thms
  let { COS_ADD, COS_NEG, COS_SUB, SIN_CIRCLE, SIN_NEG, .. } := D.gm.ra.tsc
  let { COS_NPI, SIN_NPI, .. } := D.gm.ra.tse
  let { COS_INJ_PI, .. } := D.gm.ra.tsl
  let { add_translation_invariants, GEOM_BASIS_MULTIPLE_TAC, REAL_ARITH, REAL_FIELD,
        REAL_RAT_REDUCE_CONV, SET_RULE, VECTOR_ARITH, .. } := D.gm.ra.ts.cn.cx.cvx
  let { FORALL_2, REAL_LE_SQUARE, vector_norm, .. } := D.gm.ra.ts.cn.cx.cpx
  let { CONTRAPOS_THM, DIMINDEX_2, EMPTY_SUBSET, ETA_AX, .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { IMP_CONJ, IMP_CONJ_ALT, IMP_IMP, INSERT_AC, INSERT_SUBSET,
        .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, LEFT_IMP_EXISTS_THM, POW_2_SQRT, REAL_ADD_LID, REAL_ADD_RID,
        .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_LE_LT, REAL_LT_01, REAL_LT_IMP_LE, REAL_LT_IMP_NZ,
        .. } := D.gm.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_RID, REAL_MUL_RZERO, REAL_NEG_NEG,
        REAL_NOT_LT, REAL_POW_EQ_0, RIGHT_FORALL_IMP_THM, .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { BASIS_COMPONENT, BASIS_NONZERO, COLLINEAR_2, COLLINEAR_LEMMA_ALT, DIST_0, DOT_2,
        DOT_BASIS, DOT_BASIS_BASIS, DOT_LMUL, DOT_LNEG, DOT_POS_LE, DOT_RMUL, DOT_RNEG,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec1
  let { DOT_SYM, LIFT_DROP, LINEAR_CMUL, LINEAR_SUB, NORM_BASIS,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec2
  let { VEC_COMPONENT, VECTOR_ADD_COMPONENT, VECTOR_MUL_ASSOC, VECTOR_MUL_LZERO,
        VECTOR_MUL_RNEG, VECTOR_SUB_COMPONENT, VECTOR_SUB_RZERO,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { CONTINUOUS_AT_ID, .. } := D.gm.ra.ts.cn.cx.cvx.top2
  let { CONTINUOUS_CONST, CONTINUOUS_LIFT_DOT2, .. } := D.gm.ra.ts.cn.cx.cvx.top3
  let { WITHIN_UNIV, .. } := D.gm.ra.ts.cn.ms.ig.dv.qtopology2
  let { VECTOR_NEG_0, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qvec
  -- @@SCOPE END

  let dihV ← new_definition
   r"dihV w0 w1 w2 w3 =
       let va = w2 - w0 in
       let vb = w3 - w0 in
       let vc = w1 - w0 in
       let vap = ( vc dot vc) % va - ( va dot vc) % vc in
       let vbp = ( vc dot vc) % vb - ( vb dot vc) % vc in
       arcV (vec 0) vap vbp"

  let DIHV ← prove
   r"dihV (w0:real^N) w1 w2 w3 =
       let va = w2 - w0 in
       let vb = w3 - w0 in
       let vc = w1 - w0 in
       let vap = (vc dot vc) % va - (va dot vc) % vc in
       let vbp = (vc dot vc) % vb - (vb dot vc) % vc in
       angle(vap,vec 0,vbp)"
   (REWRITE_TAC [dihV, ARCV_ANGLE])

  let DIHV_TRANSLATION_EQ ← prove
   r"!a w0 w1 w2 w3:real^N.
          dihV (a + w0) (a + w1) (a + w2) (a + w3) = dihV w0 w1 w2 w3"
   (REWRITE_TAC [DIHV, ← VECTOR_ARITH (← q r"(a + x) - (a + y):real^N = x - y")])

  add_translation_invariants [DIHV_TRANSLATION_EQ]

  let DIHV_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N w0 w1 w2 w3.
          linear f /\ (!x. norm(f x) = norm x)
          ==> dihV (f w0) (f w1) (f w2) (f w3) = dihV w0 w1 w2 w3"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [DIHV] THEN
    ASM_SIMP_TAC [← GSYM LINEAR_SUB] THEN
    CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    ASM_SIMP_TAC [PRESERVES_NORM_PRESERVES_DOT] THEN
    ASM_SIMP_TAC [← GSYM LINEAR_CMUL, ← GSYM LINEAR_SUB] THEN
    REWRITE_TAC [angle, VECTOR_SUB_RZERO] THEN
    ASM_SIMP_TAC [VECTOR_ANGLE_LINEAR_IMAGE_EQ])

  add_linear_invariants [DIHV_LINEAR_IMAGE]

  let DIHV_SPECIAL_SCALE ← prove
   r"!a v w1 w2:real^N.
          ~(a = &0)
          ==> dihV (vec 0) (a % v) w1 w2 = dihV (vec 0) v w1 w2"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [DIHV, VECTOR_SUB_RZERO] THEN
    CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC [DOT_LMUL, DOT_RMUL, ← GSYM VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"a % a % x - a % b % a % y:real^N =
                              (a * a) % (x - b % y)")] THEN
    REWRITE_TAC [angle, VECTOR_SUB_RZERO] THEN
    REWRITE_TAC [VECTOR_ANGLE_LMUL, VECTOR_ANGLE_RMUL] THEN
    ASM_REWRITE_TAC [REAL_LE_SQUARE, REAL_ENTIRE])

  let DIHV_RANGE ← prove
   r"!w0 w1 w2 w3. &0 <= dihV w0 w1 w2 w3 /\ dihV w0 w1 w2 w3 <= pi"
   (REWRITE_TAC [DIHV] THEN CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC [ANGLE_RANGE])

  let COS_AZIM_DIHV ← prove
   r"!v w v1 v2:real^3.
          ~collinear {v,w,v1} /\ ~collinear {v,w,v2}
          ==> cos(azim v w v1 v2) = cos(dihV v w v1 v2)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"w:real^3 = v") THENL
     [ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2], POP_ASSUM MP_TAC] THEN
    REWRITE_TAC [IMP_IMP, ← GSYM CONJ_ASSOC] THEN
    GEOM_ORIGIN_TAC (← q r"v:real^3") THEN GEOM_BASIS_MULTIPLE_TAC 3 (← q r"w:real^3") THEN
    X_GEN_TAC (← q r"w:real") THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
    ASM_CASES_TAC (← q r"w = &0") THEN ASM_REWRITE_TAC [VECTOR_MUL_LZERO] THEN
    ASM_SIMP_TAC [AZIM_SPECIAL_SCALE, DIHV_SPECIAL_SCALE, REAL_LT_IMP_NZ,
                 COLLINEAR_SPECIAL_SCALE, COLLINEAR_BASIS_3] THEN
    DISCH_TAC THEN POP_ASSUM_LIST (K ALL_TAC) THEN
    MAP_EVERY X_GEN_TAC [← q r"w1:real^3", ← q r"w2:real^3"] THEN
    DISCH_THEN (STRIP_ASSUME_TAC o CONJUNCT2) THEN
    REWRITE_TAC [DIHV, VECTOR_SUB_RZERO] THEN
    CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    SIMP_TAC [DOT_BASIS_BASIS, DIMINDEX_3, ARITH] THEN
    SIMP_TAC [DOT_BASIS, DIMINDEX_3, ARITH, VECTOR_MUL_LID] THEN
    MP_TAC (← ISPECL [← q r"vec 0:real^3", ← q r"basis 3:real^3", ← q r"w1:real^3", ← q r"w2:real^3"]
          azim) THEN
    ABBREV_TAC (← q r"a = azim (vec 0) (basis 3) w1 (w2:real^3)") THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM, VECTOR_SUB_RZERO, DIST_0] THEN
    MAP_EVERY X_GEN_TAC [← q r"h1:real", ← q r"h2:real"] THEN
    DISCH_THEN (MP_TAC o SPECL
     [← q r"basis 1:real^3", ← q r"basis 2:real^3", ← q r"basis 3:real^3"]) THEN
    SIMP_TAC [orthonormal, DOT_BASIS_BASIS, CROSS_BASIS, DIMINDEX_3, NORM_BASIS,
      ARITH, VECTOR_MUL_LID, BASIS_NONZERO, REAL_LT_01, LEFT_IMP_EXISTS_THM] THEN
    ASM_REWRITE_TAC [COLLINEAR_BASIS_3] THEN
    MAP_EVERY X_GEN_TAC [← q r"psi:real", ← q r"r1:real", ← q r"r2:real"] THEN
    DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN
    REWRITE_TAC [VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC [BASIS_COMPONENT, DIMINDEX_3, ARITH, REAL_MUL_RZERO] THEN
    REWRITE_TAC [REAL_MUL_RID, REAL_ADD_LID] THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"(a + b + c) - c:real^N = a + b")] THEN
    REWRITE_TAC [COS_ANGLE, VECTOR_SUB_RZERO] THEN
    REWRITE_TAC [vector_norm, ← GSYM DOT_EQ_0, DIMINDEX_3, FORALL_3, DOT_3] THEN
    REWRITE_TAC [VEC_COMPONENT, VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC [BASIS_COMPONENT, DIMINDEX_3, ARITH, REAL_MUL_RZERO] THEN
    REWRITE_TAC [REAL_MUL_RID, REAL_ADD_LID, REAL_ADD_RID, REAL_MUL_RZERO] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"(r * c) * (r * c) + (r * s) * (r * s):real =
                            r pow 2 * (s pow 2 + c pow 2)")] THEN
    ASM_SIMP_TAC [SIN_CIRCLE, REAL_MUL_RID, REAL_POW_EQ_0, REAL_LT_IMP_NZ] THEN
    ASM_SIMP_TAC [POW_2_SQRT, REAL_LT_IMP_LE] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"(r1 * c1) * (r2 * c2) + (r1 * s1) * (r2 * s2):real =
                            (r1 * r2) * (c1 * c2 + s1 * s2)")] THEN
    ASM_SIMP_TAC [← REAL_FIELD
     (← q r"&0 < r1 /\ &0 < r2 ==> ((r1 * r2) * x) / (r1 * r2) = x")] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"a:real = b + c * d <=> b - --c * d = a")] THEN
    GEN_REWRITE_TAC (funpow 3 LAND_CONV) [← GSYM COS_NEG] THEN
    REWRITE_TAC [← GSYM SIN_NEG, ← GSYM COS_ADD] THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC)

  let AZIM_DIHV_SAME ← prove
   r"!v w v1 v2:real^3.
          ~collinear {v,w,v1} /\ ~collinear {v,w,v2} /\
          azim v w v1 v2 < pi
          ==> azim v w v1 v2 = dihV v w v1 v2"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC COS_INJ_PI THEN
    ASM_SIMP_TAC [COS_AZIM_DIHV, azim, REAL_LT_IMP_LE, DIHV_RANGE])

  let AZIM_DIHV_COMPL ← prove
   r"!v w v1 v2:real^3.
          ~collinear {v,w,v1} /\ ~collinear {v,w,v2} /\
          pi <= azim v w v1 v2
          ==> azim v w v1 v2 = &2 * pi - dihV v w v1 v2"
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"x = &2 * pi - y <=> y = &2 * pi - x")] THEN
    MATCH_MP_TAC COS_INJ_PI THEN
    REWRITE_TAC [COS_SUB, SIN_NPI, COS_NPI, REAL_MUL_LZERO] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC [COS_AZIM_DIHV, REAL_ADD_RID, REAL_MUL_LID] THEN
    ASM_REWRITE_TAC [DIHV_RANGE] THEN MATCH_MP_TAC (← REAL_ARITH
     (← q r"p <= x /\ x < &2 * p ==> &0 <= &2 * p - x /\ &2 * p - x <= p")) THEN
    ASM_SIMP_TAC [azim])

  let AZIM_DIVH ← prove
   r"!v w v1 v2:real^3.
          ~collinear {v,w,v1} /\ ~collinear {v,w,v2}
          ==> azim v w v1 v2 = if azim v w v1 v2 < pi then dihV v w v1 v2
                               else &2 * pi - dihV v w v1 v2"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [REAL_NOT_LT]) THEN
    ASM_SIMP_TAC [AZIM_DIHV_SAME, AZIM_DIHV_COMPL])

  let AZIM_DIHV_EQ_0 ← prove
   r"!v0 v1 w1 w2.
          ~collinear {v0,v1,w1} /\ ~collinear {v0,v1,w2}
          ==> (azim v0 v1 w1 w2 = &0 <=> dihV v0 v1 w1 w2 = &0)"
   (REPEAT STRIP_TAC THEN
    W (MP_TAC o PART_MATCH (lhs o rand) AZIM_DIVH o lhs o lhs o snd) THEN
    ASM_REWRITE_TAC [] THEN COND_CASES_TAC THEN ASM_SIMP_TAC [] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"a:real = p - b <=> b = p - a")] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [← REAL_ARITH (← q r"&2 * p - (&2 * p - a) = &0 <=> a = &0")] THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"a < &2 * pi /\ ~(a < pi) ==> (a = &0 <=> &2 * pi - a = &0)")) THEN
    ASM_REWRITE_TAC [azim])

  let AZIM_DIHV_EQ_PI ← prove
   r"!v0 v1 w1 w2.
          ~collinear {v0,v1,w1} /\ ~collinear {v0,v1,w2}
          ==> (azim v0 v1 w1 w2 = pi <=> dihV v0 v1 w1 w2 = pi)"
   (REPEAT STRIP_TAC THEN
    W (MP_TAC o PART_MATCH (lhs o rand) AZIM_DIVH o lhs o lhs o snd) THEN
    ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC)

  let AZIM_EQ_0_PI_EQ_COPLANAR ← prove
   r"!v0 v1 w1 w2.
          ~collinear {v0,v1,w1} /\ ~collinear {v0,v1,w2}
          ==> (azim v0 v1 w1 w2 = &0 \/ azim v0 v1 w1 w2 = pi <=>
               coplanar {v0,v1,w1,w2})"
   (REWRITE_TAC [← TAUT (← q r"(a <=> b) <=> (a ==> b) /\ (b ==> a)")] THEN
    REWRITE_TAC [AZIM_EQ_0_PI_IMP_COPLANAR] THEN
    SIMP_TAC [← GSYM IMP_CONJ_ALT, COPLANAR, DIMINDEX_3, ARITH] THEN
    REWRITE_TAC [IMP_CONJ, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"v0:real^3", ← q r"v1:real^3", ← q r"v2:real^3", ← q r"v3:real^3", ← q r"p:real^3->bool"] THEN
    GEOM_HORIZONTAL_PLANE_TAC (← q r"p:real^3->bool") THEN
    REWRITE_TAC [INSERT_SUBSET, IN_ELIM_THM, IMP_CONJ, RIGHT_FORALL_IMP_THM,
                EMPTY_SUBSET] THEN
    SIMP_TAC [AZIM_DIHV_EQ_0, AZIM_DIHV_EQ_PI] THEN
    REWRITE_TAC [DIHV] THEN
    CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    DISCH_THEN (K ALL_TAC : thm → tactic) THEN PAD2D3D_TAC THEN
    REWRITE_TAC [angle, VECTOR_SUB_RZERO] THEN
    GEOM_ORIGIN_TAC (← q r"v0:real^2") THEN REWRITE_TAC [VECTOR_SUB_RZERO] THEN
    REPEAT STRIP_TAC THEN
    W (MP_TAC o PART_MATCH (rand o rand) COLLINEAR_VECTOR_ANGLE o snd) THEN
    ANTS_TAC THENL
     [REPEAT (POP_ASSUM MP_TAC), DISCH_THEN (SUBST1_TAC o SYM)] THEN
    REWRITE_TAC [← GSYM DOT_CAUCHY_SCHWARZ_EQUAL] THEN
    REWRITE_TAC [DOT_2, CART_EQ, FORALL_2, DIMINDEX_2, VEC_COMPONENT,
                VECTOR_SUB_COMPONENT, VECTOR_MUL_COMPONENT] THEN
    CONV_TAC REAL_RING)

  let DIHV_EQ_0_PI_EQ_COPLANAR ← prove
   r"!v0 v1 w1 w2:real^3.
          ~collinear {v0,v1,w1} /\ ~collinear {v0,v1,w2}
          ==> (dihV v0 v1 w1 w2 = &0 \/ dihV v0 v1 w1 w2 = pi <=>
               coplanar {v0,v1,w1,w2})"
   (SIMP_TAC [← GSYM AZIM_DIHV_EQ_0, ← GSYM AZIM_DIHV_EQ_PI,
             AZIM_EQ_0_PI_EQ_COPLANAR])

  let DIHV_SYM ← prove
   r"!v0 v1 v2 v3:real^N.
          dihV v0 v1 v3 v2 = dihV v0 v1 v2 v3"
   (REPEAT GEN_TAC THEN REWRITE_TAC [DIHV] THEN
    CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC [DOT_SYM, ANGLE_SYM])

  let DIHV_NEG ← prove
   r"!v0 v1 v2 v3. dihV (--v0) (--v1) (--v2) (--v3) = dihV v0 v1 v2 v3"
   (REWRITE_TAC [DIHV, ← VECTOR_ARITH (← q r"--a - --b:real^N = --(a - b)")] THEN
    CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC [DOT_RNEG, DOT_LNEG, REAL_NEG_NEG] THEN
    REWRITE_TAC [VECTOR_MUL_RNEG] THEN
    REWRITE_TAC [angle, ← VECTOR_ARITH (← q r"--a - --b:real^N = --(a - b)")] THEN
    REWRITE_TAC [VECTOR_SUB_RZERO, VECTOR_ANGLE_NEG2])

  let DIHV_NEG_0 ← prove
   r"!v1 v2 v3. dihV (vec 0) (--v1) (--v2) (--v3) = dihV (vec 0) v1 v2 v3"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM DIHV_NEG] THEN
    REWRITE_TAC [VECTOR_NEG_0])

  let DIHV_ARCV ← prove
   r"!e u v w:real^N.
        orthogonal (e - u) (v - u) /\ orthogonal (e - u) (w - u) /\ ~(e = u)
        ==> dihV u e v w = arcV u v w"
   (GEOM_ORIGIN_TAC (← q r"u:real^N") THEN
    REWRITE_TAC [dihV, orthogonal, VECTOR_SUB_RZERO] THEN
    CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    SIMP_TAC [DOT_SYM, VECTOR_MUL_LZERO, VECTOR_SUB_RZERO] THEN
    REWRITE_TAC [ARCV_ANGLE, angle, VECTOR_SUB_RZERO] THEN
    REWRITE_TAC [VECTOR_ANGLE_LMUL, VECTOR_ANGLE_RMUL] THEN
    SIMP_TAC [DOT_POS_LE, DOT_EQ_0])

  let AZIM_DIHV_SAME_STRONG ← prove
   r"!v w v1 v2:real^3.
          ~collinear {v,w,v1} /\ ~collinear {v,w,v2} /\
          azim v w v1 v2 <= pi
          ==> azim v w v1 v2 = dihV v w v1 v2"
   (REWRITE_TAC [REAL_LE_LT] THEN
    MESON_TAC [AZIM_DIHV_SAME, AZIM_DIHV_EQ_PI])

  let AZIM_ARCV ← prove
   r"!e u v w:real^3.
          orthogonal (e - u) (v - u) /\ orthogonal (e - u) (w - u) /\
          ~collinear{u,e,v} /\ ~collinear{u,e,w} /\
          azim u e v w <= pi
          ==> azim u e v w = arcV u v w"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"u:real^3 = e") THENL
     [ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    STRIP_TAC THEN ASM_SIMP_TAC [← GSYM DIHV_ARCV] THEN
    MATCH_MP_TAC AZIM_DIHV_SAME_STRONG THEN ASM_REWRITE_TAC [])

  let COLLINEAR_AZIM_0_OR_PI ← prove
   r"!u e v w. collinear {u,v,w} ==> azim u e v w = &0 \/ azim u e v w = pi"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"collinear{u:real^3,e,v}") THEN
    ASM_SIMP_TAC [AZIM_DEGENERATE] THEN
    ASM_CASES_TAC (← q r"collinear{u:real^3,e,w}") THEN
    ASM_SIMP_TAC [AZIM_DEGENERATE] THEN
    ASM_SIMP_TAC [AZIM_EQ_0_PI_EQ_COPLANAR] THEN
    ONCE_REWRITE_TAC [← SET_RULE (← q r"{u,e,v,w} = {u,v,w,e}")] THEN
    ASM_MESON_TAC [NOT_COPLANAR_NOT_COLLINEAR])

  let REAL_CONTINUOUS_WITHIN_DIHV_COMPOSE ← prove
   r"!f:real^M->real^N g h k x s.
        ~collinear {f x,g x,h x} /\ ~collinear {f x,g x,k x} /\
        f continuous (at x within s) /\ g continuous (at x within s) /\
        h continuous (at x within s) /\ k continuous (at x within s)
        ==> (\x. dihV (f x) (g x) (h x) (k x)) real_continuous (at x within s)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [dihV] THEN
    CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC [ARCV_ANGLE, angle, REAL_CONTINUOUS_CONTINUOUS, o_DEF] THEN
    REWRITE_TAC [VECTOR_SUB_RZERO] THEN
    MATCH_MP_TAC CONTINUOUS_WITHIN_CX_VECTOR_ANGLE_COMPOSE THEN
    ASM_REWRITE_TAC [VECTOR_SUB_EQ, ← GSYM COLLINEAR_3_DOT_MULTIPLES] THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_MUL THEN REWRITE_TAC [o_DEF] THEN
    ASM_SIMP_TAC [CONTINUOUS_LIFT_DOT2, o_DEF, CONTINUOUS_SUB])

  let REAL_CONTINUOUS_AT_DIHV_COMPOSE ← prove
   r"!f:real^M->real^N g h k x.
        ~collinear {f x,g x,h x} /\ ~collinear {f x,g x,k x} /\
        f continuous (at x) /\ g continuous (at x) /\
        h continuous (at x) /\ k continuous (at x)
        ==> (\x. dihV (f x) (g x) (h x) (k x)) real_continuous (at x)"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    REWRITE_TAC [REAL_CONTINUOUS_WITHIN_DIHV_COMPOSE])

  let REAL_CONTINUOUS_WITHINREAL_DIHV_COMPOSE ← prove
   r"!f:real->real^N g h k x s.
        ~collinear {f x,g x,h x} /\ ~collinear {f x,g x,k x} /\
        f continuous (atreal x within s) /\ g continuous (atreal x within s) /\
        h continuous (atreal x within s) /\ k continuous (atreal x within s)
        ==> (\x. dihV (f x) (g x) (h x) (k x)) real_continuous
            (atreal x within s)"
   (REWRITE_TAC [CONTINUOUS_CONTINUOUS_WITHINREAL,
                REAL_CONTINUOUS_REAL_CONTINUOUS_WITHINREAL] THEN
    SIMP_TAC [o_DEF, REAL_CONTINUOUS_WITHIN_DIHV_COMPOSE, LIFT_DROP])

  let REAL_CONTINUOUS_ATREAL_DIHV_COMPOSE ← prove
   r"!f:real->real^N g h k x.
        ~collinear {f x,g x,h x} /\ ~collinear {f x,g x,k x} /\
        f continuous (atreal x) /\ g continuous (atreal x) /\
        h continuous (atreal x) /\ k continuous (atreal x)
        ==> (\x. dihV (f x) (g x) (h x) (k x)) real_continuous (atreal x)"
   (ONCE_REWRITE_TAC [← GSYM WITHINREAL_UNIV] THEN
    REWRITE_TAC [REAL_CONTINUOUS_WITHINREAL_DIHV_COMPOSE])

  let REAL_CONTINUOUS_AT_DIHV ← prove
   r"!v w w1 w2:real^N.
          ~collinear {v, w, w2} ==> dihV v w w1 real_continuous at w2"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM ETA_AX] THEN
    REWRITE_TAC [dihV] THEN CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_SUB THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_MUL THEN
      SIMP_TAC [CONTINUOUS_CONST, o_DEF, CONTINUOUS_SUB, CONTINUOUS_AT_ID,
               CONTINUOUS_LIFT_DOT2],
      GEN_REWRITE_TAC LAND_CONV [← GSYM ETA_AX] THEN
      REWRITE_TAC [ARCV_ANGLE, angle] THEN
      REWRITE_TAC [VECTOR_SUB_RZERO, ETA_AX] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_WITHIN_VECTOR_ANGLE THEN
      POP_ASSUM MP_TAC THEN GEOM_ORIGIN_TAC (← q r"v:real^N") THEN
      REWRITE_TAC [VECTOR_SUB_RZERO, CONTRAPOS_THM, VECTOR_SUB_EQ] THEN
      MAP_EVERY X_GEN_TAC [← q r"z:real^N", ← q r"w:real^N"] THEN
      ASM_CASES_TAC (← q r"w:real^N = vec 0") THEN
      ASM_REWRITE_TAC [COLLINEAR_LEMMA_ALT] THEN DISCH_THEN (MP_TAC o AP_TERM
       (← q r"(%) (inv((w:real^N) dot w)):real^N->real^N")) THEN
      ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, DOT_EQ_0] THEN
      MESON_TAC [VECTOR_MUL_LID]])

  pure { dihV, DIHV, DIHV_TRANSLATION_EQ, DIHV_LINEAR_IMAGE, DIHV_SPECIAL_SCALE,
         DIHV_RANGE, COS_AZIM_DIHV, AZIM_DIHV_SAME, AZIM_DIHV_COMPL, AZIM_DIVH,
         AZIM_DIHV_EQ_0, AZIM_DIHV_EQ_PI, AZIM_EQ_0_PI_EQ_COPLANAR,
         DIHV_EQ_0_PI_EQ_COPLANAR, DIHV_SYM, DIHV_NEG, DIHV_NEG_0, DIHV_ARCV,
         AZIM_DIHV_SAME_STRONG, AZIM_ARCV, COLLINEAR_AZIM_0_OR_PI,
         REAL_CONTINUOUS_WITHIN_DIHV_COMPOSE, REAL_CONTINUOUS_AT_DIHV_COMPOSE,
         REAL_CONTINUOUS_WITHINREAL_DIHV_COMPOSE, REAL_CONTINUOUS_ATREAL_DIHV_COMPOSE,
         REAL_CONTINUOUS_AT_DIHV }
/- ------------------------------------------------------------------------- -/
/- Continuity of the azimuth angle.                                          -/
/- (flyspeck.ml 3331-3528)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FYL where
  REAL_CONTINUOUS_WITHIN_AZIM_COMPOSE : thm
  REAL_CONTINUOUS_AT_AZIM_COMPOSE : thm
  REAL_CONTINUOUS_WITHINREAL_AZIM_COMPOSE : thm
  REAL_CONTINUOUS_ATREAL_AZIM_COMPOSE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYL [HolBase] (D : FlyspeckDeps) (BFYB : FYB) (BFYC : FYC) (BFYF : FYF) (BFYI : FYI) (BFYJ : FYJ) (BFYK : FYK) : ExceptT String IO FYL := do
  -- @@SCOPE BEGIN
  let { COPLANAR_CROSS_DOT, .. } := BFYB
  let { AFF_GE_TRANSLATION, .. } := BFYC
  let { AFF_GE_2_1_0_SEMIALGEBRAIC, .. } := BFYF
  let { AZIM_TRANSLATION, .. } := BFYI
  let { AZIM_EQ_0_GE_ALT, AZIM_IN_UPPER_HALFSPACE, .. } := BFYJ
  let { AZIM_DIHV_COMPL, AZIM_DIHV_SAME_STRONG, AZIM_EQ_0_PI_EQ_COPLANAR,
        REAL_CONTINUOUS_AT_DIHV_COMPOSE, .. } := BFYK
  let { ASM_MESON_TAC, REAL_ARITH_TAC, .. } := D.crd
  let { CONTINUOUS_ON_CROSS, .. } := D.crs
  let { DOT_CAUCHY_SCHWARZ_EQUAL, .. } := D.qvectors
  let { CONTINUOUS_ON_UNION_LOCAL, .. } := D.qtopology
  let { WITHINREAL_UNIV, .. } := D.gm.rzf
  let { CONTINUOUS_CONTINUOUS_WITHINREAL, REAL_CONTINUOUS_CONTINUOUS,
        REAL_CONTINUOUS_REAL_CONTINUOUS_WITHINREAL, .. } := D.gm.rzn
  let { COLLINEAR_3, .. } := D.gm.qvectors
  let { CONTINUOUS_SUB, LIFT_CMUL, LIFT_SUB, o_DEF, REAL_SUB_0, .. } := D.crd.thms
  let { CONTINUOUS_AT_COMPOSE, .. } := D.gm.ra.ts.qtopology
  let { CX_INJ, CX_SUB, .. } := D.gm.ra.ts.cn.cxc
  let { MESON, REAL_ARITH, SET_RULE, SET_TAC, VECTOR_ARITH, .. } := D.gm.ra.ts.cn.cx.cvx
  let { DE_MORGAN_THM, EXTENSION, .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { FORALL_PASTECART, FSTCART_PASTECART, FUN_EQ_THM, IMAGE_UNION, IN_DIFF, INSERT_AC,
        .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, IN_INTER, IN_UNION, IN_UNIV,
        .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_POW_2, SNDCART_PASTECART, .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { o_THM, real_ge, UNWIND_THM1, .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { LIFT_DROP, LIFT_EQ, LIFT_NUM, LINEAR_FSTCART, LINEAR_SNDCART,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec2
  let { drop, VECTOR_ADD_SYM, VECTOR_SUB, VECTOR_SUB_RZERO,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { CLOSED_HALFSPACE_COMPONENT_GE, CLOSED_HALFSPACE_COMPONENT_LE, CLOSED_IN_CLOSED,
        CLOSED_INTER, CLOSED_SING, CLOSED_UNIV, .. } := D.gm.ra.ts.cn.cx.cvx.top1
  let { CONTINUOUS_AT_IMP_CONTINUOUS_ON, .. } := D.gm.ra.ts.cn.cx.cvx.top2
  let { CONTINUOUS_CONST, CONTINUOUS_ON_COMPOSE, CONTINUOUS_ON_EQ, CONTINUOUS_ON_MUL,
        CONTINUOUS_ON_SUB, .. } := D.gm.ra.ts.cn.cx.cvx.top3
  let { LINEAR_CONTINUOUS_AT, LINEAR_CONTINUOUS_ON, .. } := D.gm.ra.ts.cn.cx.cvx.top4
  let { closed, .. } := D.gm.ra.ts.cn.cx.cvx.top5
  let { CONTINUOUS_AT_WITHIN, CONTINUOUS_ON_EQ_CONTINUOUS_AT, CONTINUOUS_PASTECART,
        CONTINUOUS_WITHIN_COMPOSE, .. } := D.gm.ra.ts.cn.ms.ig.dv.qtopology1
  let { WITHIN_UNIV, .. } := D.gm.ra.ts.cn.ms.ig.dv.qtopology2
  let { CLOSED_UNION, CONTINUOUS_ON_LIFT_DOT2, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { CONTINUOUS_CLOSED_PREIMAGE, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qtop
  -- @@SCOPE END

  let REAL_CONTINUOUS_WITHIN_AZIM_COMPOSE ← (do
    let lemma ← prove
     r"!s t u f:real^M->real^N g h.
            (closed s /\ closed t) /\ s UNION t = UNIV /\
            (g continuous_on (u INTER s) /\ h continuous_on (u INTER t)) /\
            (!x. x IN u INTER s ==> g x = f x) /\
            (!x. x IN u INTER t ==> h x = f x)
            ==> f continuous_on u"
     (REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"u:real^M->bool = (u INTER s) UNION (u INTER t)")
      SUBST1_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_UNION_LOCAL THEN
      REWRITE_TAC [CLOSED_IN_CLOSED] THEN REPEAT CONJ_TAC THENL
       [EXISTS_TAC (← q r"s:real^M->bool") THEN ASM SET_TAC [],
        EXISTS_TAC (← q r"t:real^M->bool") THEN ASM SET_TAC [],
        ASM_MESON_TAC [CONTINUOUS_ON_EQ],
        ASM_MESON_TAC [CONTINUOUS_ON_EQ]])
    prove
     r"!f:real^M->real^3 g h k x s.
        ~collinear {f x,g x,h x} /\ ~collinear {f x,g x,k x} /\
        ~(k x IN aff_ge {f x,g x} {h x}) /\
        f continuous (at x within s) /\ g continuous (at x within s) /\
        h continuous (at x within s) /\ k continuous (at x within s)
        ==> (\x. azim (f x) (g x) (h x) (k x)) real_continuous (at x within s)"
      (REPEAT STRIP_TAC THEN REWRITE_TAC [REAL_CONTINUOUS_CONTINUOUS, o_DEF] THEN
      SUBGOAL_THEN
       (← q r"(\x:real^M. Cx(azim (f x) (g x) (h x) (k x))) =
        (\z. Cx(azim (vec 0) (fstcart z)
                     (fstcart(sndcart z)) (sndcart(sndcart z)))) o
        (\x. pastecart (g x - f x) (pastecart (h x - f x) (k x - f x)))")
      SUBST1_TAC THENL
       [REWRITE_TAC [FUN_EQ_THM, o_THM, FSTCART_PASTECART, SNDCART_PASTECART] THEN
        X_GEN_TAC (← q r"y:real^M") THEN
        SUBST1_TAC (← VECTOR_ARITH (← q r"vec 0 = (f:real^M->real^3) y - f y")) THEN
        SIMP_TAC [← ONCE_REWRITE_RULE [VECTOR_ADD_SYM] AZIM_TRANSLATION, VECTOR_SUB],
        MATCH_MP_TAC CONTINUOUS_WITHIN_COMPOSE THEN
        ASM_SIMP_TAC [CONTINUOUS_PASTECART, CONTINUOUS_SUB]] THEN
      MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
      SUBGOAL_THEN
       (← q r"!z. ~collinear {vec 0,fstcart z,fstcart(sndcart z)} /\
            ~collinear {vec 0,fstcart z,sndcart(sndcart z)} /\
            ~(sndcart(sndcart z) IN aff_ge {vec 0,fstcart z} {fstcart(sndcart z)})
            ==> (\z. Cx(azim (vec 0) (fstcart z) (fstcart(sndcart z))
                                                 (sndcart(sndcart z))))
                continuous (at z)")
      MATCH_MP_TAC THENL
       [ALL_TAC,
        ASM_SIMP_TAC [FSTCART_PASTECART, SNDCART_PASTECART, ← GSYM COLLINEAR_3] THEN
        REPEAT (CONJ_TAC THENL [ASM_MESON_TAC [INSERT_AC], ALL_TAC]) THEN
        SUBST1_TAC (← VECTOR_ARITH (← q r"vec 0 = (f:real^M->real^3) x - f x")) THEN
        ONCE_REWRITE_TAC [← SET_RULE (← q r"{a,b} = {a} UNION {b}")] THEN
        REWRITE_TAC [← GSYM IMAGE_UNION, ← SET_RULE
         (← q r"{a - b:real^3} = IMAGE (\x. x - b) {a}")] THEN
        REWRITE_TAC [← ONCE_REWRITE_RULE [VECTOR_ADD_SYM] AFF_GE_TRANSLATION,
                    VECTOR_SUB] THEN
        ASM_REWRITE_TAC [IN_IMAGE, ← VECTOR_ARITH (← q r"a + x:real^3 = b + x <=> a = b"),
                        UNWIND_THM1, ← SET_RULE (← q r"{a} UNION {b} = {a,b}")]] THEN
      ONCE_REWRITE_TAC [← SET_RULE
       (← q r"(!x. ~P x /\ ~Q x /\ ~R x ==> J x) <=>
        (!x. x IN UNIV DIFF (({x | P x} UNION {x | Q x}) UNION {x | R x})
             ==> J x)")] THEN
      MATCH_MP_TAC (← MESON [CONTINUOUS_ON_EQ_CONTINUOUS_AT]
       (← q r"open s /\ f continuous_on s ==> !z. z IN s ==> f continuous at z")) THEN
      CONJ_TAC THENL
       [REWRITE_TAC [← GSYM closed] THEN
        MATCH_MP_TAC (← MESON []
         (← q r"!t'. s UNION t = s UNION t' /\ closed(s UNION t')
               ==> closed(s UNION t)")) THEN
        EXISTS_TAC
          (← q r"{z | (fstcart z cross fstcart(sndcart z)) cross
                 fstcart z cross sndcart(sndcart z) = vec 0 /\
                &0 <= (fstcart z cross sndcart(sndcart z)) dot
                      (fstcart z cross fstcart(sndcart z))}") THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC (← SET_RULE
           (← q r"(!x. ~(x IN s) ==> (x IN t <=> x IN t'))
            ==> s UNION t = s UNION t'")) THEN
          REWRITE_TAC [AFF_GE_2_1_0_SEMIALGEBRAIC, IN_UNION, IN_ELIM_THM,
                      DE_MORGAN_THM],
          ALL_TAC] THEN
        MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THENL
         [MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THEN
          REWRITE_TAC [← GSYM DOT_CAUCHY_SCHWARZ_EQUAL] THEN
          ONCE_REWRITE_TAC [← GSYM REAL_SUB_0] THEN
          REWRITE_TAC [← GSYM LIFT_EQ, LIFT_NUM] THEN
          SIMP_TAC [← SET_RULE (← q r"{x | f x = a} = {x | x IN UNIV /\ f x IN {a}}")] THEN
          MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
          SIMP_TAC [CLOSED_UNIV, CLOSED_SING, LIFT_SUB, REAL_POW_2, LIFT_CMUL] THEN
          MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
          CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
          REWRITE_TAC [o_DEF] THEN REPEAT CONJ_TAC THEN
          MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN CONJ_TAC,
          ONCE_REWRITE_TAC [← MESON [LIFT_DROP, real_ge]
           (← q r"&0 <= x <=> drop(lift x) >= &0")] THEN
          REWRITE_TAC [← SET_RULE
           (← q r"{z | f z = vec 0 /\ drop(g z) >= &0} =
            {z | z IN UNIV /\ f z IN {vec 0}} INTER
            {z | z IN UNIV /\ g z IN {k | drop(k) >= &0}}")] THEN
          MATCH_MP_TAC CLOSED_INTER THEN
          CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
          REWRITE_TAC [CLOSED_SING, drop, CLOSED_UNIV,
                      CLOSED_HALFSPACE_COMPONENT_GE] THEN
          REPEAT ((MATCH_MP_TAC CONTINUOUS_ON_CROSS ORELSE
                  MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2) THEN CONJ_TAC)] THEN
        TRY (GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF]) THEN
        SIMP_TAC [CONTINUOUS_ON_COMPOSE, LINEAR_CONTINUOUS_ON,
                 LINEAR_FSTCART, LINEAR_SNDCART],
        MATCH_MP_TAC lemma THEN
        MAP_EVERY EXISTS_TAC
         [← q r"{z | z IN UNIV /\ lift((fstcart z cross (fstcart(sndcart z))) dot
                                  (sndcart(sndcart z))) IN {x | x$1 >= &0}}",
          ← q r"{z | z IN UNIV /\ lift((fstcart z cross (fstcart(sndcart z))) dot
                                  (sndcart(sndcart z))) IN {x | x$1 <= &0}}",
          ← q r"\z. Cx(dihV (vec 0:real^3) (fstcart z)
                       (fstcart(sndcart z)) (sndcart(sndcart z)))",
          ← q r"\z. Cx(&2 * pi - dihV (vec 0:real^3) (fstcart z)
                                 (fstcart(sndcart z)) (sndcart(sndcart z)))"] THEN
        CONJ_TAC THENL
         [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
          REWRITE_TAC [CLOSED_UNIV, CLOSED_HALFSPACE_COMPONENT_GE,
                      CLOSED_HALFSPACE_COMPONENT_LE] THEN
          MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
          (CONJ_TAC THENL [MATCH_MP_TAC CONTINUOUS_ON_CROSS, ALL_TAC]) THEN
          ONCE_REWRITE_TAC [← GSYM o_DEF] THEN
          SIMP_TAC [CONTINUOUS_ON_COMPOSE, LINEAR_CONTINUOUS_ON,
                   LINEAR_FSTCART, LINEAR_SNDCART],
          ALL_TAC] THEN
        CONJ_TAC THENL
         [REWRITE_TAC [EXTENSION, IN_UNION, IN_UNIV, IN_ELIM_THM] THEN
          REAL_ARITH_TAC,
          ALL_TAC] THEN
        CONJ_TAC THENL
         [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
          REWRITE_TAC [FORALL_PASTECART, IN_DIFF, IN_UNIV, IN_UNION, IN_INTER,
            FSTCART_PASTECART, SNDCART_PASTECART, IN_ELIM_THM, DE_MORGAN_THM] THEN
          MAP_EVERY X_GEN_TAC [← q r"x:real^3", ← q r"y:real^3", ← q r"z:real^3"] THEN
          REPEAT STRIP_TAC THEN REWRITE_TAC [CX_SUB] THEN
          TRY (MATCH_MP_TAC CONTINUOUS_SUB THEN REWRITE_TAC [CONTINUOUS_CONST]) THEN
          GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
          REWRITE_TAC [← GSYM REAL_CONTINUOUS_CONTINUOUS] THEN
          MATCH_MP_TAC REAL_CONTINUOUS_AT_DIHV_COMPOSE THEN
          ASM_REWRITE_TAC [FSTCART_PASTECART, SNDCART_PASTECART,
                          CONTINUOUS_CONST] THEN
          ONCE_REWRITE_TAC [← GSYM o_DEF] THEN
          SIMP_TAC [CONTINUOUS_AT_COMPOSE, LINEAR_CONTINUOUS_AT,
                   LINEAR_FSTCART, LINEAR_SNDCART],
          ALL_TAC] THEN
        REWRITE_TAC [FORALL_PASTECART, IN_DIFF, IN_UNIV, IN_UNION, IN_INTER, CX_INJ,
            FSTCART_PASTECART, SNDCART_PASTECART, IN_ELIM_THM, DE_MORGAN_THM] THEN
        CONJ_TAC THENL
         [REWRITE_TAC [← GSYM drop, LIFT_DROP, real_ge] THEN
          MAP_EVERY X_GEN_TAC [← q r"x:real^3", ← q r"y:real^3", ← q r"z:real^3"] THEN
          REPEAT STRIP_TAC THEN MATCH_MP_TAC (← GSYM AZIM_DIHV_SAME_STRONG) THEN
          ASM_REWRITE_TAC [AZIM_IN_UPPER_HALFSPACE, VECTOR_SUB_RZERO],
          REWRITE_TAC [← GSYM drop, LIFT_DROP] THEN
          MAP_EVERY X_GEN_TAC [← q r"x:real^3", ← q r"y:real^3", ← q r"z:real^3"] THEN
          REPEAT STRIP_TAC THEN MATCH_MP_TAC (← GSYM AZIM_DIHV_COMPL) THEN
          ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC (← REAL_ARITH
           (← q r"(x <= pi ==> x = pi) ==> pi <= x")) THEN
          ASM_REWRITE_TAC [AZIM_IN_UPPER_HALFSPACE, VECTOR_SUB_RZERO] THEN
          ASM_SIMP_TAC [← REAL_ARITH (← q r"x <= &0 ==> (&0 <= x <=> x = &0)")] THEN
          REWRITE_TAC [← REWRITE_RULE [VECTOR_SUB_RZERO]
             (← SPEC (← q r"vec 0:real^3") (← GSYM COPLANAR_CROSS_DOT))] THEN
          ASM_SIMP_TAC [← GSYM AZIM_EQ_0_PI_EQ_COPLANAR, AZIM_EQ_0_GE_ALT]]]))

  let REAL_CONTINUOUS_AT_AZIM_COMPOSE ← prove
   r"!f:real^M->real^3 g h k x.
        ~collinear {f x,g x,h x} /\ ~collinear {f x,g x,k x} /\
        ~(k x IN aff_ge {f x,g x} {h x}) /\
        f continuous (at x) /\ g continuous (at x) /\
        h continuous (at x) /\ k continuous (at x)
        ==> (\x. azim (f x) (g x) (h x) (k x)) real_continuous (at x)"
   (ONCE_REWRITE_TAC [← GSYM WITHIN_UNIV] THEN
    REWRITE_TAC [REAL_CONTINUOUS_WITHIN_AZIM_COMPOSE])

  let REAL_CONTINUOUS_WITHINREAL_AZIM_COMPOSE ← prove
   r"!f:real->real^3 g h k x s.
        ~collinear {f x,g x,h x} /\ ~collinear {f x,g x,k x} /\
        ~(k x IN aff_ge {f x,g x} {h x}) /\
        f continuous (atreal x within s) /\ g continuous (atreal x within s) /\
        h continuous (atreal x within s) /\ k continuous (atreal x within s)
        ==> (\x. azim (f x) (g x) (h x) (k x)) real_continuous
            (atreal x within s)"
   (REWRITE_TAC [CONTINUOUS_CONTINUOUS_WITHINREAL,
                REAL_CONTINUOUS_REAL_CONTINUOUS_WITHINREAL] THEN
    SIMP_TAC [o_DEF, REAL_CONTINUOUS_WITHIN_AZIM_COMPOSE, LIFT_DROP])

  let REAL_CONTINUOUS_ATREAL_AZIM_COMPOSE ← prove
   r"!f:real->real^3 g h k x.
        ~collinear {f x,g x,h x} /\ ~collinear {f x,g x,k x} /\
        ~(k x IN aff_ge {f x,g x} {h x}) /\
        f continuous (atreal x) /\ g continuous (atreal x) /\
        h continuous (atreal x) /\ k continuous (atreal x)
        ==> (\x. azim (f x) (g x) (h x) (k x)) real_continuous (atreal x)"
   (ONCE_REWRITE_TAC [← GSYM WITHINREAL_UNIV] THEN
    REWRITE_TAC [REAL_CONTINUOUS_WITHINREAL_AZIM_COMPOSE])

  pure { REAL_CONTINUOUS_WITHIN_AZIM_COMPOSE, REAL_CONTINUOUS_AT_AZIM_COMPOSE,
         REAL_CONTINUOUS_WITHINREAL_AZIM_COMPOSE, REAL_CONTINUOUS_ATREAL_AZIM_COMPOSE }
/- ------------------------------------------------------------------------- -/
/- Angle as a zenith angle; spherical coordinates; definition of a wedge    -/
/- and invariance theorems.                                                  -/
/- (flyspeck.ml 3529-3773)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FYM where
  ZENITH_EXISTS : thm
  SPHERICAL_COORDINATES : thm
  wedge : thm
  WEDGE_ALT : thm
  WEDGE_TRANSLATION : thm
  WEDGE_LINEAR_IMAGE : thm
  WEDGE_SPECIAL_SCALE : thm
  WEDGE_DEGENERATE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYM [HolBase] (D : FlyspeckDeps) (BFYA : FYA) (BFYG : FYG) (BFYI : FYI) (BFYJ : FYJ) : ExceptT String IO FYM := do
  -- @@SCOPE BEGIN
  let { COLLINEAR_BASIS_3, COLLINEAR_SPECIAL_SCALE, .. } := BFYA
  let { ARCV_ANGLE, orthonormal, ORTHONORMAL_CROSS, .. } := BFYG
  let { AZIM_ARG, AZIM_DEGENERATE, AZIM_LINEAR_IMAGE, AZIM_SPECIAL_SCALE, AZIM_TRANSLATION,
        .. } := BFYI
  let { AZIM_EQ_0_ALT, .. } := BFYJ
  let { SIN_VECTOR_ANGLE_POS, VECTOR_ANGLE, VECTOR_ANGLE_RMUL, .. } := D.gea
  let { angle, .. } := D.gec
  let { add_linear_invariants, ASM_MESON_TAC, MESON_TAC, new_definition, REAL_ARITH_TAC,
        REAL_RING, .. } := D.crd
  let { cross, CROSS_LZERO, .. } := D.crs
  let { COLLINEAR_3_AFFINE_HULL, .. } := D.qconvex
  let { COLLINEAR_LINEAR_IMAGE_EQ, COLLINEAR_TRANSLATION_EQ,
        ORTHOGONAL_TRANSFORMATION_SURJECTIVE, .. } := D.qdeterminants
  let { TRANSLATION_INVARIANTS, .. } := D.geominv
  let { GEN_GEOM_ORIGIN_TAC, .. } := D.geomorigin
  let { DOT_3, .. } := D.gm.qvectors
  let { ARITH, CART_EQ, DIMINDEX_3, DOT_LZERO, FORALL_3, LAMBDA_BETA, NORM_POS_LE,
        NORM_POW_2, ORTHOGONAL_TRANSFORMATION, REAL_LE_MUL, REAL_POW_MUL, VECTOR_3,
        VECTOR_MUL_COMPONENT, .. } := D.crd.thms
  let { CEXP_EULER, .. } := D.gm.ra.tsb
  let { CX_COS, CX_SIN, SIN_CIRCLE, .. } := D.gm.ra.tsc
  let { ARG, ARG_DIV_CX, ARG_EQ_0, .. } := D.gm.ra.tsh
  let { dropout, .. } := D.gm.ra.qvectors
  let { NORM_EQ_1, .. } := D.gm.ra.ts.qvectors
  let { complex, COMPLEX_EQ, complex_mul, ii, IM_DEF, RE_DEF, .. } := D.gm.ra.ts.cn.cxa
  let { COMPLEX_MUL_LID, COMPLEX_MUL_RID, .. } := D.gm.ra.ts.cn.cxb
  let { COMPLEX_CMUL, COMPLEX_NORM_CX, COMPLEX_VEC_0, IM_CX, RE_CX,
        .. } := D.gm.ra.ts.cn.cxc
  let { COMPLEX_RING, .. } := D.gm.ra.ts.cn.cxd
  let { COMPLEX_FIELD, .. } := D.gm.ra.ts.cn.cxe
  let { COMPLEX_DIV_1, .. } := D.gm.ra.ts.cn.cxf
  let { COMPLEX_BASIS, .. } := D.gm.ra.ts.cn.cxh
  let { real, .. } := D.gm.ra.ts.cn.cxi
  let { REAL_NORM, .. } := D.gm.ra.ts.cn.cxj
  let { add_translation_invariants, GEOM_BASIS_MULTIPLE_TAC, REAL_ARITH, SET_RULE,
        VECTOR_ARITH, .. } := D.gm.ra.ts.cn.cx.cvx
  let { FORALL_2, VECTOR_2, .. } := D.gm.ra.ts.cn.cx.cpx
  let { ARITH_EQ, CONJ_SYM, DIMINDEX_2, EMPTY_GSPEC, .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { INSERT_AC, .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, REAL_ABS_NUM, REAL_ADD_LDISTRIB, .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_LE_LT, REAL_LT_ANTISYM, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_REFL,
        .. } := D.gm.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_RID, REAL_OF_NUM_EQ, RIGHT_EXISTS_AND_THM,
        .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { SURJECTIVE_IMAGE_EQ, UNWIND_THM2, .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { BASIS_COMPONENT, BASIS_NONZERO, COLLINEAR_2, COLLINEAR_LEMMA, DIST_0, DOT_2,
        DOT_BASIS, DOT_BASIS_BASIS, DOT_LMUL, DOT_LSUB, DOT_RMUL,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec1
  let { NORM_BASIS, NORM_EQ_SQUARE, .. } := D.gm.ra.ts.cn.cx.cvx.vec2
  let { NORM_MUL, PRESERVES_NORM_INJECTIVE, .. } := D.gm.ra.ts.cn.cx.cvx.vec3
  let { VECTOR_ADD_COMPONENT, VECTOR_ADD_LID, VECTOR_ADD_RID, VECTOR_MUL_EQ_0,
        VECTOR_MUL_LCANCEL, VECTOR_MUL_LZERO, VECTOR_SUB_RZERO,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { REAL_EQ_MUL_LCANCEL, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qses
  -- @@SCOPE END

  let ZENITH_EXISTS ← prove
   r"!u v w:real^3.
         ~(u = v) /\ ~(w = v)
         ==> (?u' r phi e3.
                  phi = arcV v u w /\
                  r = dist(u,v) /\
                  dist(w,v) % e3 = w - v /\
                  u' dot e3 = &0 /\
                  u = v + u' + (r * cos phi) % e3)"
   (ONCE_REWRITE_TAC [← VECTOR_ARITH
     (← q r"u:real^3 = v + u' + x <=> u - v = u' + x")] THEN
    GEN_GEOM_ORIGIN_TAC (← q r"v:real^3") ["u'", "e3"] THEN
    REWRITE_TAC [VECTOR_SUB_RZERO, DIST_0] THEN
    ONCE_REWRITE_TAC [← VECTOR_ARITH
     (← q r"u:real^3 = u' + x <=> u - u' = x")] THEN
    GEOM_BASIS_MULTIPLE_TAC 3 (← q r"w:real^3") THEN
    X_GEN_TAC (← q r"w:real") THEN ASM_CASES_TAC (← q r"w = &0") THEN
    ASM_REWRITE_TAC [VECTOR_MUL_LZERO, REAL_LE_LT] THEN DISCH_TAC THEN
    SIMP_TAC [NORM_MUL, NORM_BASIS, DIMINDEX_3, ARITH] THEN
    ASM_SIMP_TAC [← REAL_ARITH (← q r"&0 < w ==> abs w * &1 = w")] THEN
    ASM_SIMP_TAC [VECTOR_MUL_LCANCEL, REAL_LT_IMP_NZ] THEN
    REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM2] THEN
    REWRITE_TAC [ARCV_ANGLE, angle, VECTOR_SUB_RZERO] THEN
    ASM_SIMP_TAC [VECTOR_MUL_EQ_0, REAL_LT_IMP_NZ] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"u:real^3", ← q r"w % basis 3:real^3"] VECTOR_ANGLE) THEN
    REWRITE_TAC [DOT_RMUL, NORM_MUL] THEN
    ASM_SIMP_TAC [← REAL_ARITH
     (← q r"&0 < w ==> n * ((abs w) * x) * y = w * n * x * y")] THEN
    ASM_REWRITE_TAC [REAL_EQ_MUL_LCANCEL] THEN
    SIMP_TAC [NORM_BASIS, DIMINDEX_3, ARITH, REAL_MUL_LID] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"u - u':real^3 = x <=> u' = u - x")] THEN
    ONCE_REWRITE_TAC [CONJ_SYM] THEN REWRITE_TAC [UNWIND_THM2] THEN
    REWRITE_TAC [DOT_LSUB, DOT_RMUL, DOT_LMUL] THEN
    SIMP_TAC [DOT_BASIS_BASIS, DIMINDEX_3, ARITH] THEN REAL_ARITH_TAC)

  /- Spherical coordinates. -/

  let SPHERICAL_COORDINATES ← prove
   r"!u v w u' e1 e2 e3 r phi theta.
         ~collinear {v, w, u} /\
         ~collinear {v, w, u'} /\
         orthonormal e1 e2 e3 /\
         dist(w,v) % e3 = w - v /\
         (v + e1) IN aff_gt {v, w} {u} /\
         r = dist(v,u') /\
         phi = arcV v u' w /\
         theta = azim v w u u'
         ==> u' = v + (r * cos theta * sin phi) % e1 +
                      (r * sin theta * sin phi) % e2 +
                      (r * cos phi) % e3"
   (ONCE_REWRITE_TAC [← VECTOR_ARITH
     (← q r"u':real^3 = u + v + w <=> u' - u = v + w")] THEN
    GEN_GEOM_ORIGIN_TAC (← q r"v:real^3") ["e1", "e2", "e3"] THEN
    REWRITE_TAC [VECTOR_ADD_RID, VECTOR_ADD_LID] THEN
    REWRITE_TAC [← TRANSLATION_INVARIANTS (← q r"v:real^3")] THEN
    GEOM_BASIS_MULTIPLE_TAC 3 (← q r"w:real^3") THEN
    REWRITE_TAC [VECTOR_SUB_RZERO, DIST_0] THEN
    X_GEN_TAC (← q r"w:real") THEN ASM_CASES_TAC (← q r"w = &0") THENL
     [ASM_REWRITE_TAC [VECTOR_MUL_LZERO, INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    ASM_REWRITE_TAC [REAL_LE_LT] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC
     [← q r"u:real^3", ← q r"v:real^3", ← q r"e1:real^3", ← q r"e2:real^3", ← q r"e3:real^3",
      ← q r"r:real", ← q r"phi:real", ← q r"theta:real"] THEN
    ASM_CASES_TAC (← q r"u:real^3 = w % basis 3") THENL
     [ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"v:real^3 = w % basis 3") THENL
     [ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o GSYM) THEN
    ASM_SIMP_TAC [AZIM_SPECIAL_SCALE, COLLINEAR_SPECIAL_SCALE] THEN
    SIMP_TAC [NORM_MUL, NORM_BASIS, DIMINDEX_3, ARITH] THEN
    ASM_SIMP_TAC [← REAL_ARITH (← q r"&0 < w ==> abs w * &1 = w")] THEN
    ASM_REWRITE_TAC [VECTOR_MUL_LCANCEL] THEN
    ASM_CASES_TAC (← q r"e3:real^3 = basis 3") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [ARCV_ANGLE, angle, VECTOR_SUB_RZERO] THEN
    ASM_SIMP_TAC [VECTOR_ANGLE_RMUL, REAL_LT_IMP_LE] THEN
    ASM_CASES_TAC (← q r"u:real^3 = vec 0") THENL
     [ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"v:real^3 = vec 0") THENL
     [ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"u:real^3 = basis 3") THENL
     [ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"v:real^3 = basis 3") THENL
     [ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"v:real^3", ← q r"basis 3:real^3"] VECTOR_ANGLE) THEN
    ASM_SIMP_TAC [DOT_BASIS, NORM_BASIS, DIMINDEX_3, ARITH, REAL_MUL_LID] THEN
    DISCH_TAC THEN
    MP_TAC (← ISPECL
     [← q r"vec 0:real^3", ← q r"w % basis 3:real^3", ← q r"u:real^3", ← q r"e1:real^3"]
          AZIM_EQ_0_ALT) THEN
    ASM_SIMP_TAC [AZIM_SPECIAL_SCALE, COLLINEAR_SPECIAL_SCALE] THEN
    ANTS_TAC THENL
     [SIMP_TAC [COLLINEAR_LEMMA, BASIS_NONZERO, DIMINDEX_3, ARITH] THEN
      STRIP_TAC THEN UNDISCH_TAC (← q r"orthonormal e1 e2 (basis 3)") THEN
      ASM_REWRITE_TAC [orthonormal, DOT_LZERO, REAL_OF_NUM_EQ, ARITH_EQ] THEN
      ASM_CASES_TAC (← q r"c = &0") THEN
      ASM_SIMP_TAC [VECTOR_MUL_LZERO, CROSS_LZERO, DOT_LZERO, REAL_LT_REFL,
                   DOT_LMUL, DOT_BASIS_BASIS, DIMINDEX_3, ARITH, REAL_MUL_RID],
      DISCH_TAC] THEN
    SUBGOAL_THEN
     (← q r"dropout 3 (v:real^3):real^2 =
      norm(dropout 3 (v:real^3):real^2) %
      (cos theta % (dropout 3 (e1:real^3)) +
       sin theta % (dropout 3 (e2:real^3)))")
    MP_TAC THENL
     [ALL_TAC,
      SUBGOAL_THEN (← q r"norm((dropout 3:real^3->real^2) v) = r * sin phi")
      SUBST1_TAC THENL
       [REWRITE_TAC [NORM_EQ_SQUARE] THEN CONJ_TAC THENL
         [ASM_MESON_TAC [REAL_LE_MUL, NORM_POS_LE, SIN_VECTOR_ANGLE_POS],
          ALL_TAC] THEN
        UNDISCH_TAC (← q r"(v:real^3)$3 = r * cos phi") THEN
        MATCH_MP_TAC (← REAL_RING
         (← q r"x + a pow 2 = y + b pow 2 ==> a:real = b ==> x = y")) THEN
        REWRITE_TAC [REAL_POW_MUL, ← GSYM REAL_ADD_LDISTRIB] THEN
        REWRITE_TAC [SIN_CIRCLE, REAL_MUL_RID] THEN
        UNDISCH_THEN (← q r"norm(v:real^3) = r") (SUBST1_TAC o SYM) THEN
        REWRITE_TAC [NORM_POW_2, DOT_2, DOT_3] THEN
        SIMP_TAC [dropout, LAMBDA_BETA, DIMINDEX_2, DIMINDEX_3, ARITH] THEN
        REAL_ARITH_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [CART_EQ, DIMINDEX_3, DIMINDEX_2, FORALL_3, FORALL_2] THEN
      SIMP_TAC [dropout, LAMBDA_BETA, DIMINDEX_2, ARITH, VECTOR_ADD_COMPONENT,
               VECTOR_MUL_COMPONENT, BASIS_COMPONENT, DIMINDEX_3] THEN
      REPEAT STRIP_TAC THEN TRY REAL_ARITH_TAC THEN
      ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [orthonormal]) THEN
      SIMP_TAC [DOT_BASIS, DIMINDEX_3, ARITH] THEN CONV_TAC REAL_RING] THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o
      GEN_REWRITE_RULE LAND_CONV [AZIM_ARG])) THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o
      GEN_REWRITE_RULE RAND_CONV [COLLINEAR_BASIS_3])) THEN
    SUBGOAL_THEN (← q r"norm((dropout 3:real^3->real^2) e1) = &1 /\
                  norm((dropout 3:real^3->real^2) e2) = &1 /\
                  dropout 3 (e2:real^3) / dropout 3 (e1:real^3) = ii")
    MP_TAC THENL
     [MATCH_MP_TAC (← TAUT (← q r"(a /\ b) /\ (a /\ b ==> c) ==> a /\ b /\ c")) THEN
      CONJ_TAC THENL
       [REWRITE_TAC [NORM_EQ_1] THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [orthonormal]) THEN
        SIMP_TAC [DOT_BASIS, DIMINDEX_3, ARITH, dropout, LAMBDA_BETA,
                 DOT_2, DIMINDEX_2, DOT_3] THEN
        CONV_TAC REAL_RING,
        ALL_TAC] THEN
      ASM_CASES_TAC (← q r"dropout 3 (e1:real^3) = Cx(&0)") THEN
      ASM_SIMP_TAC [COMPLEX_NORM_CX, REAL_OF_NUM_EQ, ARITH_EQ, REAL_ABS_NUM] THEN
      ASM_SIMP_TAC [← ExceptT.mk (COMPLEX_FIELD
       (← q r"~(x = Cx(&0)) ==> (y / x = ii <=> y = ii * x)"))] THEN
      DISCH_TAC THEN FIRST_ASSUM (MP_TAC o MATCH_MP ORTHONORMAL_CROSS) THEN
      SIMP_TAC [CART_EQ, DIMINDEX_2, DIMINDEX_3, FORALL_2, FORALL_3,
               cross, VECTOR_3, BASIS_COMPONENT, ARITH, dropout, LAMBDA_BETA,
               complex_mul, ii, complex, RE_DEF, IM_DEF, VECTOR_2] THEN
      CONV_TAC REAL_RING,
      ALL_TAC] THEN
    SPEC_TAC (← q r"(dropout 3:real^3->real^2) e2", ← q r"d2:real^2") THEN
    SPEC_TAC (← q r"(dropout 3:real^3->real^2) e1", ← q r"d1:real^2") THEN
    SPEC_TAC (← q r"(dropout 3:real^3->real^2) v", ← q r"z:real^2") THEN
    SPEC_TAC (← q r"(dropout 3:real^3->real^2) u", ← q r"w:real^2") THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN
    GEOM_BASIS_MULTIPLE_TAC 1 (← q r"w:real^2") THEN
    X_GEN_TAC (← q r"k:real") THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
    ASM_CASES_TAC (← q r"k = &0") THEN ASM_REWRITE_TAC [VECTOR_MUL_LZERO] THEN
    REWRITE_TAC [COMPLEX_CMUL, COMPLEX_BASIS, COMPLEX_VEC_0] THEN
    SIMP_TAC [ARG_DIV_CX, COMPLEX_MUL_RID] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"d1 = Cx(&1)") THENL
     [ASM_SIMP_TAC [COMPLEX_DIV_1, COMPLEX_MUL_LID] THEN
      REPEAT STRIP_TAC THEN MP_TAC (← SPEC (← q r"z:complex") ARG) THEN
      ASM_REWRITE_TAC [CEXP_EULER, CX_SIN, CX_COS, COMPLEX_MUL_RID] THEN
      CONV_TAC COMPLEX_RING,
      ASM_REWRITE_TAC [ARG_EQ_0] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [COMPLEX_EQ]) THEN
      REWRITE_TAC [RE_CX, IM_CX, real] THEN
      ASM_CASES_TAC (← q r"Im d1 = &0") THEN ASM_REWRITE_TAC [] THEN
      ASM_SIMP_TAC [REAL_NORM, real] THEN REAL_ARITH_TAC])

  /- Definition of a wedge and invariance theorems. -/

  let wedge ← new_definition
   r"wedge v0 v1 w1 w2 = {y | ~collinear {v0,v1,y} /\
                           &0 < azim v0 v1 w1 y /\
                           azim v0 v1 w1 y < azim v0 v1 w1 w2}"

  let WEDGE_ALT ← prove
   r"!v0 v1 w1 w2.
          ~(v0 = v1)
          ==> wedge v0 v1 w1 w2 = {y | ~(y IN affine hull {v0,v1}) /\
                                       &0 < azim v0 v1 w1 y /\
                                       azim v0 v1 w1 y < azim v0 v1 w1 w2}"
   (SIMP_TAC [wedge, COLLINEAR_3_AFFINE_HULL])

  let WEDGE_TRANSLATION ← prove
   r"!a v w w1 w2. wedge (a + v) (a + w) (a + w1) (a + w2) =
                   IMAGE (\x. a + x) (wedge v w w1 w2)"
   (REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN CONJ_TAC THENL
     [MESON_TAC [← VECTOR_ARITH (← q r"a + (x - a):real^3 = x")], ALL_TAC] THEN
    REWRITE_TAC [wedge, IN_ELIM_THM, AZIM_TRANSLATION] THEN
    REWRITE_TAC [← SET_RULE
     (← q r"{a + x,a + y,a + z} = IMAGE (\x:real^N. a + x) {x,y,z}")] THEN
    REWRITE_TAC [COLLINEAR_TRANSLATION_EQ])

  add_translation_invariants [WEDGE_TRANSLATION]

  let WEDGE_LINEAR_IMAGE ← prove
   r"!f. linear f /\ (!x. norm(f x) = norm x) /\
         (2 <= dimindex(:3) ==> det(matrix f) = &1)
         ==> !v w w1 w2. wedge (f v) (f w) (f w1) (f w2) =
                         IMAGE f (wedge v w w1 w2)"
   (REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN CONJ_TAC THENL
     [ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION_SURJECTIVE,
                    ORTHOGONAL_TRANSFORMATION],
      ALL_TAC] THEN
    X_GEN_TAC (← q r"y:real^3") THEN REWRITE_TAC [wedge, IN_ELIM_THM] THEN
    BINOP_TAC THEN ASM_SIMP_TAC [AZIM_LINEAR_IMAGE] THEN
    SUBST1_TAC (← SET_RULE (← q r"{f v,f w,f y} = IMAGE (f:real^3->real^3) {v,w,y}")) THEN
    ASM_MESON_TAC [COLLINEAR_LINEAR_IMAGE_EQ, PRESERVES_NORM_INJECTIVE])

  add_linear_invariants [WEDGE_LINEAR_IMAGE]

  let WEDGE_SPECIAL_SCALE ← prove
   r"!a v w1 w2.
          &0 < a /\
          ~collinear{vec 0,a % v,w1} /\
          ~collinear{vec 0,a % v,w2}
          ==> wedge (vec 0) (a % v) w1 w2 = wedge (vec 0) v w1 w2"
   (SIMP_TAC [wedge, AZIM_SPECIAL_SCALE, COLLINEAR_SPECIAL_SCALE,
             REAL_LT_IMP_NZ])

  let WEDGE_DEGENERATE ← prove
   r"(!z w w1 w2. z = w ==> wedge z w w1 w2 = {}) /\
     (!z w w1 w2. collinear{z,w,w1} ==> wedge z w w1 w2 = {}) /\
     (!z w w1 w2. collinear{z,w,w2} ==> wedge z w w1 w2 = {})"
   (REWRITE_TAC [wedge] THEN SIMP_TAC [AZIM_DEGENERATE] THEN
    REWRITE_TAC [REAL_LT_REFL, REAL_LT_ANTISYM, EMPTY_GSPEC])

  pure { ZENITH_EXISTS, SPHERICAL_COORDINATES, wedge, WEDGE_ALT, WEDGE_TRANSLATION,
         WEDGE_LINEAR_IMAGE, WEDGE_SPECIAL_SCALE, WEDGE_DEGENERATE }
/- ------------------------------------------------------------------------- -/
/- Basic relation between wedge and aff, so Tarski-type characterization.    -/
/- (flyspeck.ml 3774-4053)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FYN where
  AFF_GT_LEMMA : thm
  WEDGE_LUNE_GT : thm
  WEDGE_LUNE_GE : thm
  WEDGE_LUNE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYN [HolBase] (D : FlyspeckDeps) (BFYA : FYA) (BFYC : FYC) (BFYE : FYE) (BFYI : FYI) (BFYJ : FYJ) (BFYM : FYM) : ExceptT String IO FYN := do
  -- @@SCOPE BEGIN
  let { COLLINEAR_BASIS_3, COLLINEAR_SPECIAL_SCALE, DROPOUT_BASIS_3,
        NOT_COPLANAR_NOT_COLLINEAR, .. } := BFYA
  let { aff_gt_def, AFFSIGN_ALT, sgn_gt, .. } := BFYC
  let { AFF_GE_AFF_GT_DECOMP, AFF_GE_EQ_AFFINE_HULL, AFF_GT_SPECIAL_SCALE,
        AFFINE_HULL_SUBSET_AFF_GE, .. } := BFYE
  let { azim, AZIM_ARG, AZIM_DEGENERATE, AZIM_REFL, AZIM_SPECIAL_SCALE, .. } := BFYI
  let { AZIM_EQ_0_ALT, AZIM_EQ_0_PI_IMP_COPLANAR, AZIM_EQ_ALT, .. } := BFYJ
  let { wedge, .. } := BFYM
  let { ASM_MESON_TAC, MESON_TAC, REAL_ARITH_TAC, .. } := D.crd
  let { AFFINE_HULL_FINITE_STEP_GEN, COLLINEAR_3_AFFINE_HULL, .. } := D.qconvex
  let { DROPOUT_MUL, DROPOUT_SUB, .. } := D.qvectors
  let { GEOM_ORIGIN_TAC, .. } := D.geomorigin
  let { REAL_CONTINUOUS_CONST, REAL_CONTINUOUS_SUB, REAL_CONTINUOUS_WITHIN_ID,
        .. } := D.gm.rzh
  let { CONTINUOUS_WITHINREAL_COMPOSE, .. } := D.gm.rzi
  let { REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN, .. } := D.gm.rzj
  let { REAL_CONTINUOUS_CONTINUOUS, .. } := D.gm.rzn
  let { REAL_IVT_DECREASING, .. } := D.gm.rzs
  let { ARITH, CART_EQ, CONJ_ASSOC, DIMINDEX_3, FORALL_3, LAMBDA_BETA, o_DEF, REAL_ENTIRE,
        REAL_LE_MUL, REAL_SUB_0, REAL_SUB_RZERO, VECTOR_MUL_COMPONENT, .. } := D.crd.thms
  let { ARG, ARG_0, ARG_DIV_CX, ARG_LE_PI, ARG_LT_PI, ARG_NUM, .. } := D.gm.ra.tsh
  let { ATN_BOUNDS, ATN_MONO_LT_EQ, .. } := D.gm.ra.tsq
  let { ARG_ATAN_UPPERHALF, CONTINUOUS_WITHIN_UPPERHALF_ARG, .. } := D.gm.ra.tsz
  let { dropout, DROPOUT_0, .. } := D.gm.ra.qvectors
  let { IN_REAL_INTERVAL, .. } := D.gm.ra.qmisc
  let { CONTINUOUS_COMPLEX_MUL, .. } := D.gm.ra.ts.knc
  let { COMPLEX_EQ, IM, RE, .. } := D.gm.ra.ts.cn.cxa
  let { COMPLEX_ADD_LDISTRIB, COMPLEX_ADD_LID, COMPLEX_ADD_RID, COMPLEX_MUL_AC,
        COMPLEX_MUL_ASSOC, COMPLEX_MUL_LID, COMPLEX_MUL_LZERO, COMPLEX_MUL_RID,
        .. } := D.gm.ra.ts.cn.cxb
  let { COMPLEX_CMUL, COMPLEX_VEC_0, CX_DIV, CX_INJ, CX_MUL, IM_ADD, IM_CX, IM_MUL_CX,
        RE_ADD, RE_CX, RE_MUL_CX, .. } := D.gm.ra.ts.cn.cxc
  let { COMPLEX_RING, .. } := D.gm.ra.ts.cn.cxd
  let { COMPLEX_FIELD, .. } := D.gm.ra.ts.cn.cxe
  let { COMPLEX_NORM_NZ, COMPLEX_NORM_ZERO, .. } := D.gm.ra.ts.cn.cxf
  let { COMPLEX_BASIS, .. } := D.gm.ra.ts.cn.cxh
  let { REAL_EQ_SUB_RADD, .. } := D.gm.ra.ts.cn.qsession
  let { ASM_REAL_ARITH_TAC, GEOM_BASIS_MULTIPLE_TAC, MESON, REAL_ARITH, REAL_FIELD,
        SET_RULE, VECTOR_ARITH, .. } := D.gm.ra.ts.cn.cx.cvx
  let { FORALL_2, .. } := D.gm.ra.ts.cn.cx.cpx
  let { DIMINDEX_2, DIMINDEX_GE_1, EQ_TRANS, EXTENSION, FINITE_EMPTY, FINITE_INSERT,
        FINITE_UNION, FORALL_IN_GSPEC, .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, FUN_EQ_THM, IMAGE_CLAUSES, INSERT_AC,
        .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, IN_UNION, LE_REFL, LEFT_EXISTS_AND_THM, NOT_IMP,
        NOT_IN_EMPTY, REAL_ADD_LID, REAL_DIV_RMUL, .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_LE_LT, REAL_LT_ADD, REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_LE,
        REAL_LT_MUL, REAL_LT_RDIV_EQ, REAL_LT_REFL, .. } := D.gm.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_RID, REAL_MUL_RZERO, REAL_POS, REAL_SUB_LT, REAL_SUB_REFL,
        RIGHT_AND_EXISTS_THM, RIGHT_EXISTS_AND_THM, SIMPLE_IMAGE, SUBSET, SUBSET_ANTISYM,
        .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { o_ASSOC, SWAP_EXISTS_THM, UNIONS_2, UNWIND_THM1, UNWIND_THM2,
        .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { REAL_HALF, .. } := D.gm.ra.ts.cn.cx.cvx.misc
  let { BASIS_COMPONENT, BASIS_NONZERO, COLLINEAR_2, .. } := D.gm.ra.ts.cn.cx.cvx.vec1
  let { VEC_COMPONENT, VECTOR_ADD_SYM, VECTOR_MUL_ASSOC, VECTOR_MUL_EQ_0, VECTOR_MUL_LZERO,
        VECTOR_MUL_RZERO, VECTOR_SUB_RZERO, .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { CONTINUOUS_ADD, .. } := D.gm.ra.ts.cn.cx.cvx.top2
  let { CONTINUOUS_CONST, CONTINUOUS_WITHIN_SUBSET, .. } := D.gm.ra.ts.cn.cx.cvx.top3
  let { I_DEF, I_O_ID, REAL_LT_TRANS, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.qsession
  let { DISJ_ACI, DISJOINT_EMPTY, DISJOINT_INSERT, UNIONS_1,
        .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qses
  -- @@SCOPE END

  let AFF_GT_LEMMA ← prove
   r"!v1 v2:real^N.
          &0 < t1 /\ ~(v2 = vec 0)
          ==> aff_gt {vec 0} {t1 % basis 1, v2} =
                  {a % basis 1 + b % v2 | &0 < a /\ &0 < b}"
   (REWRITE_TAC [AFFSIGN_ALT, aff_gt_def, sgn_gt, IN_ELIM_THM] THEN
    REWRITE_TAC [← SET_RULE (← q r"{a} UNION {b,c} = {a,b,c}")] THEN
    REWRITE_TAC [← SET_RULE (← q r"x IN {a} <=> a = x")] THEN
    ASM_SIMP_TAC [FINITE_INSERT, FINITE_UNION, AFFINE_HULL_FINITE_STEP_GEN,
                 RIGHT_EXISTS_AND_THM, REAL_LT_ADD, REAL_HALF, FINITE_EMPTY] THEN
    ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
    REWRITE_TAC [IN_INSERT, ← VECTOR_ARITH (← q r"vec 0 = a % x <=> a % x = vec 0")] THEN
    ASM_SIMP_TAC [VECTOR_MUL_EQ_0, REAL_LT_IMP_NZ, BASIS_NONZERO,
                 DIMINDEX_GE_1, LE_REFL] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_SUB_RZERO] THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"y:real^N") THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"&1 - v - v' - v'' = &0 <=> v = &1 - v' - v''")] THEN
    ONCE_REWRITE_TAC [← MESON [] (← q r"(?a b c. P a b c) <=> (?b c a. P a b c)")] THEN
    REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM2] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
    AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"b:real") THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"y - a - b:real^N = vec 0 <=> y = a + b")] THEN
    EQ_TAC THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:real") STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC (← q r"a * t1:real"), EXISTS_TAC (← q r"a / t1:real")] THEN
    ASM_SIMP_TAC [REAL_LT_DIV, REAL_LT_MUL, VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC [REAL_DIV_RMUL, REAL_LT_IMP_NZ])

  let WEDGE_LUNE_GT ← (do
    let lemma ← prove
     r"!a x:real^3. (?a. x = a % basis 3) <=> dropout 3 x:real^2 = vec 0"
     (SIMP_TAC [CART_EQ, FORALL_2, FORALL_3, DIMINDEX_2, DIMINDEX_3,
          dropout, LAMBDA_BETA, BASIS_COMPONENT, ARITH, REAL_MUL_RID,
          VECTOR_MUL_COMPONENT, VEC_COMPONENT, REAL_MUL_RZERO, UNWIND_THM1] THEN
      MESON_TAC [])
    prove
     r"!v0 v1 w1 w2.
          ~collinear {v0,v1,w1} /\ ~collinear {v0,v1,w2} /\
          &0 < azim v0 v1 w1 w2 /\ azim v0 v1 w1 w2 < pi
          ==> wedge v0 v1 w1 w2 = aff_gt {v0,v1} {w1,w2}"
      (REWRITE_TAC [wedge] THEN GEOM_ORIGIN_TAC (← q r"v0:real^3") THEN
      GEOM_BASIS_MULTIPLE_TAC 3 (← q r"v1:real^3") THEN
      X_GEN_TAC (← q r"w:real") THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
      ASM_CASES_TAC (← q r"w = &0") THEN ASM_REWRITE_TAC [] THENL
       [ASM_REWRITE_TAC [VECTOR_MUL_LZERO, INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
      ASM_SIMP_TAC [AZIM_SPECIAL_SCALE, COLLINEAR_SPECIAL_SCALE] THEN
      POP_ASSUM_LIST (K ALL_TAC) THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [← q r"w1:real^3", ← q r"w2:real^3"] THEN
      REPLICATE_TAC 2 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ONCE_REWRITE_TAC [← TAUT (← q r"~a /\ b /\ c <=> ~(~a ==> ~(b /\ c))")] THEN
      ASM_SIMP_TAC [AZIM_ARG] THEN REWRITE_TAC [COLLINEAR_BASIS_3] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [COLLINEAR_BASIS_3]) THEN STRIP_TAC THEN
      REWRITE_TAC [NOT_IMP, ← GSYM CONJ_ASSOC] THEN
      W (MP_TAC o PART_MATCH (lhs o rand) AFF_GT_SPECIAL_SCALE o rand o snd) THEN
      SUBGOAL_THEN
       (← q r"~(w1:real^3 = vec 0) /\ ~(w2:real^3 = vec 0) /\
        ~(w1 = basis 3) /\ ~(w2 = basis 3)")
      STRIP_ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN
        REPEAT (FIRST_X_ASSUM (MP_TAC o check (HolCore.Basics.is_neg o concl))) THEN
        ASM_REWRITE_TAC [DROPOUT_BASIS_3, DROPOUT_0, DROPOUT_MUL, VECTOR_MUL_RZERO],
        ALL_TAC] THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY, IN_INSERT, NOT_IN_EMPTY] THEN
        DISCH_THEN (DISJ_CASES_THEN (SUBST_ALL_TAC o SYM)) THEN
        REPEAT (FIRST_X_ASSUM (MP_TAC o check (HolCore.Basics.is_neg o concl))) THEN
        ASM_REWRITE_TAC [DROPOUT_BASIS_3, DROPOUT_0, DROPOUT_MUL, VECTOR_MUL_RZERO],
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC [AFFSIGN_ALT, aff_gt_def, sgn_gt, IN_ELIM_THM] THEN
      REWRITE_TAC [← SET_RULE (← q r"{a,b} UNION {c,d} = {a,b,d,c}")] THEN
      REWRITE_TAC [← SET_RULE (← q r"x IN {a} <=> a = x")] THEN
      ASM_SIMP_TAC [FINITE_INSERT, FINITE_UNION, AFFINE_HULL_FINITE_STEP_GEN,
                   RIGHT_EXISTS_AND_THM, REAL_LT_ADD, REAL_HALF, FINITE_EMPTY] THEN
      ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
      REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_SUB_RZERO] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC (← q r"{y | (dropout 3:real^3->real^2) y IN
                       aff_gt {vec 0}
                       {dropout 3 (w1:real^3),dropout 3 (w2:real^3)}}") THEN
      CONJ_TAC THENL
       [ALL_TAC,
        REWRITE_TAC [AFFSIGN_ALT, aff_gt_def, sgn_gt, IN_ELIM_THM] THEN
        REWRITE_TAC [← SET_RULE (← q r"{a} UNION {b,c} = {a,b,c}")] THEN
        REWRITE_TAC [← SET_RULE (← q r"x IN {a} <=> a = x")] THEN
        ASM_SIMP_TAC [FINITE_INSERT, FINITE_UNION, AFFINE_HULL_FINITE_STEP_GEN,
                   RIGHT_EXISTS_AND_THM, REAL_LT_ADD, REAL_HALF, FINITE_EMPTY] THEN
        ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
        REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_SUB_RZERO] THEN
        REWRITE_TAC [REAL_EQ_SUB_RADD, RIGHT_AND_EXISTS_THM] THEN
        REWRITE_TAC [← REAL_ARITH (← q r"&1 = x + v <=> v = &1 - x")] THEN
        ONCE_REWRITE_TAC [← TAUT (← q r"a /\ b /\ c /\ d <=> c /\ d /\ a /\ b")] THEN
        ONCE_REWRITE_TAC [← MESON []
          (← q r"(?a b c d. P a b c d) <=> (?b c d a. P a b c d)")] THEN
        REWRITE_TAC [UNWIND_THM2] THEN
        ONCE_REWRITE_TAC [← MESON []
          (← q r"(?a b c. P a b c) <=> (?c b a. P a b c)")] THEN
        REWRITE_TAC [UNWIND_THM2] THEN REWRITE_TAC [← VECTOR_ARITH
         (← q r"y - a - b - c:real^N = vec 0 <=> y - b - c = a")] THEN
        REWRITE_TAC [LEFT_EXISTS_AND_THM, lemma] THEN
        REWRITE_TAC [DROPOUT_SUB, DROPOUT_MUL] THEN
        REWRITE_TAC [← VECTOR_ARITH (← q r"y - a - b:real^2 = vec 0 <=> y = a + b")] THEN
        REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN MESON_TAC [VECTOR_ADD_SYM]] THEN
      MATCH_MP_TAC (← SET_RULE
       (← q r"{x | P x} = s ==> {y | P(dropout 3 y)} = {y | dropout 3 y IN s}")) THEN
      MP_TAC (← CONJ (← ASSUME (← q r"~((dropout 3:real^3->real^2) w1 = vec 0)"))
                  (← ASSUME (← q r"~((dropout 3:real^3->real^2) w2 = vec 0)"))) THEN
      UNDISCH_TAC (← q r"Arg(dropout 3 (w2:real^3) / dropout 3 (w1:real^3)) < pi") THEN
      UNDISCH_TAC (← q r"&0 < Arg(dropout 3 (w2:real^3) / dropout 3 (w1:real^3))") THEN
      SPEC_TAC (← q r"(dropout 3:real^3->real^2) w2", ← q r"v2:complex") THEN
      SPEC_TAC (← q r"(dropout 3:real^3->real^2) w1", ← q r"v1:complex") THEN
      POP_ASSUM_LIST (K ALL_TAC) THEN GEOM_BASIS_MULTIPLE_TAC 1 (← q r"v1:complex") THEN
      X_GEN_TAC (← q r"v1:real") THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
      ASM_CASES_TAC (← q r"v1 = &0") THEN ASM_REWRITE_TAC [VECTOR_MUL_LZERO] THEN
      SIMP_TAC [AFF_GT_LEMMA] THEN
      REWRITE_TAC [COMPLEX_CMUL, COMPLEX_BASIS, COMPLEX_VEC_0] THEN
      ASM_SIMP_TAC [ARG_DIV_CX, COMPLEX_MUL_RID, CX_INJ] THEN DISCH_TAC THEN
      POP_ASSUM_LIST (K ALL_TAC) THEN X_GEN_TAC (← q r"z:complex") THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
      REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, IN_ELIM_THM] THEN CONJ_TAC THENL
       [X_GEN_TAC (← q r"w:complex") THEN STRIP_TAC THEN
        MP_TAC (← SPECL [← q r"\t. Arg(Cx t + Cx(&1 - t) * z)",
                      ← q r"&0", ← q r"&1", ← q r"Arg w"] REAL_IVT_DECREASING) THEN
        REWRITE_TAC [REAL_POS, REAL_SUB_REFL, COMPLEX_MUL_LZERO] THEN
        REWRITE_TAC [REAL_SUB_RZERO, COMPLEX_ADD_LID, COMPLEX_MUL_LID] THEN
        ASM_SIMP_TAC [COMPLEX_ADD_RID, ARG_NUM, REAL_LT_IMP_LE] THEN ANTS_TAC THENL
         [REWRITE_TAC [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
          REWRITE_TAC [REAL_CONTINUOUS_CONTINUOUS, IN_REAL_INTERVAL] THEN
          X_GEN_TAC (← q r"t:real") THEN STRIP_TAC THEN
          ONCE_REWRITE_TAC [← GSYM o_DEF] THEN REWRITE_TAC [o_ASSOC] THEN
          MATCH_MP_TAC CONTINUOUS_WITHINREAL_COMPOSE THEN
          REWRITE_TAC [] THEN CONJ_TAC THENL
           [MATCH_MP_TAC CONTINUOUS_ADD THEN CONJ_TAC THENL
             [GEN_REWRITE_TAC LAND_CONV [← SYM (← CONJUNCT2 (← SPEC_ALL I_O_ID))] THEN
              REWRITE_TAC [← GSYM REAL_CONTINUOUS_CONTINUOUS] THEN
              REWRITE_TAC [I_DEF, REAL_CONTINUOUS_WITHIN_ID],
              MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN
              REWRITE_TAC [CONTINUOUS_CONST] THEN ONCE_REWRITE_TAC [← GSYM o_DEF] THEN
              REWRITE_TAC [← GSYM REAL_CONTINUOUS_CONTINUOUS] THEN
              SIMP_TAC [REAL_CONTINUOUS_SUB, REAL_CONTINUOUS_CONST,
                       REAL_CONTINUOUS_WITHIN_ID]],
            MATCH_MP_TAC CONTINUOUS_WITHIN_SUBSET THEN
            EXISTS_TAC (← q r"{z | &0 <= Im z}") THEN CONJ_TAC THENL
             [MATCH_MP_TAC CONTINUOUS_WITHIN_UPPERHALF_ARG THEN
              ASM_CASES_TAC (← q r"t = &1") THENL
               [ASM_REWRITE_TAC [REAL_SUB_REFL] THEN CONV_TAC COMPLEX_RING,
                ALL_TAC] THEN
              DISCH_THEN (MP_TAC o AP_TERM (← q r"Im")) THEN
              REWRITE_TAC [IM_ADD, IM_CX, IM_MUL_CX, REAL_ADD_LID, REAL_ENTIRE] THEN
              ASM_REWRITE_TAC [REAL_SUB_0] THEN
              ASM_MESON_TAC [ARG_LT_PI, REAL_LT_IMP_NZ, REAL_LT_TRANS],
              REWRITE_TAC [FORALL_IN_IMAGE, SUBSET, IN_REAL_INTERVAL] THEN
              REWRITE_TAC [IN_ELIM_THM, IM_ADD, IM_CX, IM_MUL_CX] THEN
              REPEAT STRIP_TAC THEN REWRITE_TAC [REAL_ADD_LID] THEN
              MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [← GSYM ARG_LE_PI] THEN
              ASM_REAL_ARITH_TAC]],
          REWRITE_TAC [IN_REAL_INTERVAL] THEN
          DISCH_THEN (X_CHOOSE_THEN (← q r"t:real") MP_TAC) THEN
          ASM_CASES_TAC (← q r"t = &0") THENL
           [ASM_REWRITE_TAC [REAL_SUB_RZERO, COMPLEX_ADD_LID, COMPLEX_MUL_LID] THEN
            ASM_MESON_TAC [REAL_LT_REFL],
            ALL_TAC] THEN
          ASM_CASES_TAC (← q r"t = &1") THENL
           [ASM_REWRITE_TAC [REAL_SUB_REFL, COMPLEX_MUL_LZERO] THEN
            REWRITE_TAC [COMPLEX_ADD_RID, ARG_NUM] THEN ASM_MESON_TAC [REAL_LT_REFL],
            ALL_TAC] THEN
          GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_LE_LT] THEN
          ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"u = Cx t + Cx(&1 - t) * z") THEN
          ASM_CASES_TAC (← q r"u = Cx(&0)") THENL
           [ASM_MESON_TAC [ARG_0, REAL_LT_REFL], ALL_TAC] THEN
          STRIP_TAC THEN
          EXISTS_TAC (← q r"norm(w:complex) / norm(u:complex) * t") THEN
          EXISTS_TAC (← q r"norm(w:complex) / norm(u:complex) * (&1 - t)") THEN
          ASM_SIMP_TAC [REAL_LT_MUL, REAL_LT_DIV, COMPLEX_NORM_NZ, REAL_SUB_LT] THEN
          SIMP_TAC [CX_MUL, ← GSYM COMPLEX_MUL_ASSOC, ← GSYM COMPLEX_ADD_LDISTRIB] THEN
          ASM_REWRITE_TAC [CX_DIV] THEN
          ASM_SIMP_TAC [CX_INJ, COMPLEX_NORM_ZERO, ← ExceptT.mk (COMPLEX_FIELD
            (← q r"~(nu = Cx(&0)) ==> (w = nw / nu * u <=> nu * w = nw * u)"))] THEN
          GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV) [ARG] THEN
          ASM_REWRITE_TAC [COMPLEX_MUL_AC]],
        MAP_EVERY X_GEN_TAC [← q r"a:real", ← q r"b:real"] THEN STRIP_TAC THEN
        SUBGOAL_THEN (← q r"Cx a + Cx b * z = complex(a + b * Re z,b * Im z)")
        SUBST1_TAC THENL
         [REWRITE_TAC [COMPLEX_EQ, RE, IM, RE_ADD, IM_ADD, RE_CX, IM_CX,
                      RE_MUL_CX, IM_MUL_CX] THEN
          REAL_ARITH_TAC,
          ALL_TAC] THEN
        REWRITE_TAC [COMPLEX_EQ, IM, IM_CX] THEN
        SUBGOAL_THEN (← q r"&0 < Im z") ASSUME_TAC THENL
         [ASM_REWRITE_TAC [← GSYM ARG_LT_PI], ALL_TAC] THEN
        ASM_SIMP_TAC [ARG_ATAN_UPPERHALF, REAL_LT_MUL, REAL_LT_IMP_NZ, IM] THEN
        REWRITE_TAC [RE, REAL_SUB_LT, ATN_BOUNDS] THEN
        REWRITE_TAC [← REAL_ARITH (← q r"pi / &2 - x < pi / &2 - y <=> y < x")] THEN
        REWRITE_TAC [ATN_MONO_LT_EQ] THEN
        ASM_SIMP_TAC [REAL_LT_RDIV_EQ, REAL_LT_MUL] THEN
        ASM_SIMP_TAC [← REAL_FIELD (← q r"&0 < z ==> w / z * b * z = b * w")] THEN
        ASM_REAL_ARITH_TAC]))

  let WEDGE_LUNE_GE ← prove
   r"!v0 v1 w1 w2.
          ~collinear {v0,v1,w1} /\ ~collinear {v0,v1,w2} /\
          &0 < azim v0 v1 w1 w2 /\ azim v0 v1 w1 w2 < pi
          ==> {x | &0 <= azim v0 v1 w1 x /\
                   azim v0 v1 w1 x <= azim v0 v1 w1 w2} =
              aff_ge {v0,v1} {w1,w2}"
   (REPEAT GEN_TAC THEN
    MAP_EVERY (fun t => ASM_CASES_TAC t THENL
         [ASM_REWRITE_TAC [COLLINEAR_2, INSERT_AC] THEN HolCore.Tactics.NO_TAC, ALL_TAC])
     [← q r"v1:real^3 = v0", ← q r"w1:real^3 = v0", ← q r"w2:real^3 = v0",
      ← q r"w1:real^3 = v1", ← q r"w2:real^3 = v1"] THEN
    ASM_CASES_TAC (← q r"w1:real^3 = w2") THEN
    ASM_REWRITE_TAC [AZIM_REFL, REAL_LT_REFL] THEN
    STRIP_TAC THEN ASM_SIMP_TAC [← REAL_ARITH
     (← q r"&0 < a
      ==> (&0 <= x /\ x <= a <=> x = &0 \/ x = a \/ &0 < x /\ x < a)")] THEN
    MATCH_MP_TAC (← SET_RULE
     (← q r"!c. c SUBSET {x | p x} /\ c SUBSET s /\
          ({x | ~(~c x ==> ~p x)} UNION {x | ~(~c x ==> ~q x)} UNION
           ({x | ~c x /\ r x} DIFF c) = s DIFF c)
          ==> {x | p x \/ q x \/ r x} = s")) THEN
    EXISTS_TAC (← q r"{x:real^3 | collinear {v0,v1,x}}") THEN
    ASM_SIMP_TAC [IN_ELIM_THM, AZIM_EQ_ALT, AZIM_EQ_0_ALT,
                 ← GSYM wedge, WEDGE_LUNE_GT] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC [SUBSET, IN_ELIM_THM, AZIM_DEGENERATE],
      ASM_SIMP_TAC [COLLINEAR_3_AFFINE_HULL] THEN
      REWRITE_TAC [← SET_RULE (← q r"{x | x IN s} = s")] THEN
      MATCH_MP_TAC AFFINE_HULL_SUBSET_AFF_GE THEN
      ASM_REWRITE_TAC [DISJOINT_INSERT, IN_INSERT, NOT_IN_EMPTY, DISJOINT_EMPTY],
      ALL_TAC] THEN
    REWRITE_TAC [NOT_IMP] THEN MATCH_MP_TAC (← SET_RULE
     (← q r"(!x. ~c x ==> (p x \/ q x \/ x IN t <=> x IN e))
      ==> {x | ~c x /\ p x} UNION {x | ~c x /\ q x} UNION (t DIFF {x | c x}) =
          e DIFF {x | c x}")) THEN
    X_GEN_TAC (← q r"y:real^3") THEN DISCH_TAC THEN
    W (MP_TAC o PART_MATCH (lhs o rand) AFF_GE_AFF_GT_DECOMP o rand o
      rand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY] THEN
      ASM_REWRITE_TAC [DISJOINT_INSERT, IN_INSERT, NOT_IN_EMPTY, DISJOINT_EMPTY],
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC [IN_UNION] THEN
    REWRITE_TAC [SIMPLE_IMAGE, IMAGE_CLAUSES, UNIONS_2] THEN
    ASM_SIMP_TAC [← SET_RULE (← q r"~(w1 = w2) ==> {w1,w2} DELETE w1 = {w2}"),
                 ← SET_RULE (← q r"~(w1 = w2) ==> {w1,w2} DELETE w2 = {w1}")] THEN
    REWRITE_TAC [IN_UNION, DISJ_ACI] THEN
    W (MP_TAC o PART_MATCH (lhs o rand) AFF_GE_AFF_GT_DECOMP o rand o lhand o
      rand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY] THEN
      ASM_REWRITE_TAC [DISJOINT_INSERT, IN_INSERT, NOT_IN_EMPTY, DISJOINT_EMPTY],
      DISCH_THEN SUBST1_TAC] THEN
    W (MP_TAC o PART_MATCH (lhs o rand) AFF_GE_AFF_GT_DECOMP o rand o lhand o
      rand o rand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY] THEN
      ASM_REWRITE_TAC [DISJOINT_INSERT, IN_INSERT, NOT_IN_EMPTY, DISJOINT_EMPTY],
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC [IN_UNION] THEN
    REWRITE_TAC [SIMPLE_IMAGE, IMAGE_CLAUSES, UNIONS_1] THEN
    REWRITE_TAC [← SET_RULE (← q r"{a} DELETE a = {}"), AFF_GE_EQ_AFFINE_HULL] THEN
    ASM_MESON_TAC [COLLINEAR_3_AFFINE_HULL])

  let WEDGE_LUNE ← prove
   r"!v0 v1 w1 w2.
          ~coplanar{v0,v1,w1,w2} /\ azim v0 v1 w1 w2 < pi
          ==> wedge v0 v1 w1 w2 = aff_gt {v0,v1} {w1,w2}"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC WEDGE_LUNE_GT THEN
    ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
     [MP_TAC (← ISPECL [← q r"v0:real^3", ← q r"v1:real^3", ← q r"w1:real^3", ← q r"w2:real^3"]
                  NOT_COPLANAR_NOT_COLLINEAR) THEN
      ASM_REWRITE_TAC [],
      MP_TAC (← ISPECL [← q r"v0:real^3", ← q r"v1:real^3", ← q r"w2:real^3", ← q r"w1:real^3"]
                  NOT_COPLANAR_NOT_COLLINEAR) THEN
      ONCE_REWRITE_TAC [← SET_RULE (← q r"{a,b,c,d} = {a,b,d,c}")] THEN
      ASM_REWRITE_TAC [],
      REWRITE_TAC [azim, REAL_LT_LE] THEN
      ASM_MESON_TAC [AZIM_EQ_0_PI_IMP_COPLANAR]])

  pure { AFF_GT_LEMMA, WEDGE_LUNE_GT, WEDGE_LUNE_GE, WEDGE_LUNE }
/- ------------------------------------------------------------------------- -/
/- Explicit form of a wedge; openness; azimuth level sets are coplanar.      -/
/- (flyspeck.ml 4054-4395)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FYO where
  WEDGE : thm
  OPEN_WEDGE : thm
  ARG_EQ_SUBSET_HALFLINE : thm
  ARG_DIV_EQ_SUBSET_HALFLINE : thm
  COPLANAR_AZIM_EQ : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYO [HolBase] (D : FlyspeckDeps) (BFYA : FYA) (BFYD : FYD) (BFYE : FYE) (BFYF : FYF) (BFYI : FYI) (BFYJ : FYJ) (BFYK : FYK) (BFYM : FYM) (BFYN : FYN) : ExceptT String IO FYO := do
  -- @@SCOPE BEGIN
  let { COLLINEAR_BASIS_3, COLLINEAR_SPECIAL_SCALE, OPEN_DROPOUT_3, .. } := BFYA
  let { AFF_GT_2_1, AFF_GT_3_1, .. } := BFYD
  let { AFF_GT_SPECIAL_SCALE, .. } := BFYE
  let { ENDS_IN_HALFLINE, HALFLINE, HALFLINE_EXPLICIT, .. } := BFYF
  let { AZIM_ARG, azim_def, AZIM_SPECIAL_SCALE, .. } := BFYI
  let { AZIM_EQ_0_GE_ALT, AZIM_EQ_PI_ALT, .. } := BFYJ
  let { AZIM_EQ_0_PI_EQ_COPLANAR, .. } := BFYK
  let { wedge, WEDGE_DEGENERATE, WEDGE_SPECIAL_SCALE, .. } := BFYM
  let { WEDGE_LUNE, WEDGE_LUNE_GE, .. } := BFYN
  let { ASM_MESON_TAC, MESON_TAC, REAL_ARITH_TAC, .. } := D.crd
  let { cross, CROSS_EQ_0, CROSS_EQ_SELF, CROSS_LMUL, .. } := D.crs
  let { coplanar, COPLANAR_EMPTY, .. } := D.qconvex
  let { LET_DEF, LET_END_DEF, .. } := D.qsession
  let { TRANSLATION_INVARIANTS, .. } := D.geominv
  let { GEOM_ORIGIN_TAC, .. } := D.geomorigin
  let { DOT_3, .. } := D.gm.qvectors
  let { ARITH, CART_EQ, CONJ_ASSOC, DIMINDEX_3, FORALL_3, LAMBDA_BETA, REAL_MUL_LZERO,
        REAL_SUB_RZERO, VECTOR_3, VECTOR_MUL_COMPONENT, .. } := D.crd.thms
  let { PI_POS, .. } := D.gm.ra.tse
  let { ARG, ARG_0, ARG_DIV_CX, ARG_EQ, ARG_EQ_0, ARG_INV, ARG_INV_EQ_0, ARG_LE_DIV_SUM,
        ARG_LT_NZ, ARG_LT_PI, ARG_MUL_CX, .. } := D.gm.ra.tsh
  let { ROTATE2D_PI2, .. } := D.gm.ra.tsi
  let { OPEN_ARG_LTT, .. } := D.gm.ra.tsz
  let { dropout, DROPOUT_0, pushin, .. } := D.gm.ra.qvectors
  let { REAL_LT_SUB_RADD, .. } := D.gm.ra.ts.qsession
  let { complex, complex_div, COMPLEX_EQ, complex_mul, IM_DEF, RE_DEF,
        .. } := D.gm.ra.ts.cn.cxa
  let { COMPLEX_ADD_LID, COMPLEX_MUL_LZERO, COMPLEX_MUL_RID, COMPLEX_MUL_RZERO,
        .. } := D.gm.ra.ts.cn.cxb
  let { COMPLEX_CMUL, COMPLEX_ENTIRE, COMPLEX_VEC_0, CX_INJ, CX_MUL, II_NZ, IM_ADD, IM_CX,
        IM_DIV_CX, IM_II, IM_MUL_CX, IM_MUL_II, RE_ADD, RE_CX, RE_DIV_CX, RE_II, RE_MUL_CX,
        RE_MUL_II, .. } := D.gm.ra.ts.cn.cxc
  let { COMPLEX_RING, .. } := D.gm.ra.ts.cn.cxd
  let { COMPLEX_FIELD, COMPLEX_INV_DIV, .. } := D.gm.ra.ts.cn.cxe
  let { cnj, IM_COMPLEX_DIV_GT_0, .. } := D.gm.ra.ts.cn.cxg
  let { COMPLEX_BASIS, .. } := D.gm.ra.ts.cn.cxh
  let { real, REAL, .. } := D.gm.ra.ts.cn.cxi
  let { ASM_REAL_ARITH_TAC, GEOM_BASIS_MULTIPLE_TAC, MESON, REAL_ARITH, REAL_FIELD,
        SET_RULE, .. } := D.gm.ra.ts.cn.cx.cvx
  let { FORALL_2, REAL_SUB_LZERO, VECTOR_2, .. } := D.gm.ra.ts.cn.cx.cpx
  let { DE_MORGAN_THM, DIMINDEX_2, EMPTY_GSPEC, EQ_TRANS, EXISTS_REFL, EXTENSION,
        FINITE_EMPTY, FINITE_INSERT, .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { FUN_EQ_THM, IMP_CONJ, IMP_IMP, IN_DIFF, INSERT_AC,
        .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, IN_SING, IN_UNIV, LEFT_IMP_EXISTS_THM, MONO_EXISTS,
        NOT_IMP, NOT_IN_EMPTY, REAL_ADD_LID, REAL_ADD_RID, REAL_ADD_SYM, REAL_DIV_RMUL,
        .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_EQ_LDIV_EQ, REAL_LE_LT, REAL_LE_REFL, REAL_LT_ANTISYM, REAL_LT_DIV,
        REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_LDIV_EQ, REAL_LT_LE, REAL_LT_MUL,
        REAL_LT_MUL_EQ, .. } := D.gm.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_RID, REAL_MUL_RNEG, REAL_MUL_RZERO,
        REAL_NEG_0, REAL_NOT_LE, REAL_NOT_LT, REAL_SUB_LT, REAL_SUB_REFL,
        RIGHT_AND_EXISTS_THM, RIGHT_EXISTS_AND_THM, SUBSET, SUBSET_TRANS,
        .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { SWAP_EXISTS_THM, UNWIND_THM1, UNWIND_THM2, .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { BASIS_COMPONENT, BASIS_NONZERO, COLLINEAR_2, COLLINEAR_LEMMA,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec1
  let { VEC_COMPONENT, VECTOR_ADD_COMPONENT, VECTOR_ADD_LID, VECTOR_ADD_RID,
        VECTOR_MUL_EQ_0, VECTOR_MUL_LZERO, VECTOR_MUL_RZERO, VECTOR_SUB_RZERO,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { CLOSED_SING, .. } := D.gm.ra.ts.cn.cx.cvx.top1
  let { OPEN_DIFF, OPEN_EMPTY, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.qtopology2
  let { DISJOINT_EMPTY, DISJOINT_INSERT, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qses
  let { AFFINE_HULL_3, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qcvx1
  -- @@SCOPE END

  let WEDGE ← prove
   r"wedge v1 v2 w1 w2 =
          if collinear{v1,v2,w1} \/ collinear{v1,v2,w2} then {}
          else
            let z = v2 - v1 in
            let u1 = w1 - v1 in
            let u2 = w2 - v1 in
            let n = z cross u1 in
            let d =  n dot u2 in
            if w2 IN (aff_ge {v1,v2} {w1}) then {}
            else if w2 IN (aff_lt {v1,v2} {w1}) then aff_gt {v1,v2,w1} {v1 + n}
            else if d > &0 then aff_gt {v1,v2} {w1,w2}
            else (:real^3) DIFF aff_ge {v1,v2} {w1,w2}"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM DISJ_CASES_TAC THEN
      ASM_SIMP_TAC [WEDGE_DEGENERATE],
      POP_ASSUM MP_TAC THEN REWRITE_TAC [DE_MORGAN_THM] THEN STRIP_TAC] THEN
    ASM_SIMP_TAC [← GSYM AZIM_EQ_0_GE_ALT] THEN
    ASM_CASES_TAC (← q r"azim v1 v2 w1 w2 = &0") THENL
     [ASM_REWRITE_TAC [wedge] THEN
      ASM_REWRITE_TAC [REAL_LT_ANTISYM, LET_DEF, LET_END_DEF, EMPTY_GSPEC],
      ALL_TAC] THEN
    ASM_SIMP_TAC [← GSYM AZIM_EQ_PI_ALT] THEN
    ASM_CASES_TAC (← q r"azim v1 v2 w1 w2 = pi") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [LET_DEF, LET_END_DEF] THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist CONJ) THEN
    GEOM_ORIGIN_TAC (← q r"v1:real^3") THEN
    REWRITE_TAC [VECTOR_ADD_RID, ← TRANSLATION_INVARIANTS (← q r"v1:real^3")] THEN
    REWRITE_TAC [VECTOR_SUB_RZERO, VECTOR_ADD_LID] THEN
    GEOM_BASIS_MULTIPLE_TAC 3 (← q r"v2:real^3") THEN
    X_GEN_TAC (← q r"v2:real") THEN
    GEN_REWRITE_TAC LAND_CONV [← REAL_ARITH (← q r"&0 <= x <=> x = &0 \/ &0 < x")] THEN
    (STRIP_TAC THENL
      [ASM_REWRITE_TAC [VECTOR_MUL_LZERO, INSERT_AC, COLLINEAR_2], ALL_TAC]) THEN
    ASM_SIMP_TAC [AZIM_SPECIAL_SCALE, COLLINEAR_SPECIAL_SCALE, REAL_LT_IMP_NZ,
                 WEDGE_SPECIAL_SCALE] THEN
    (REPEAT GEN_TAC THEN
     MAP_EVERY (fun t => ASM_CASES_TAC t THENL
          [ASM_REWRITE_TAC [COLLINEAR_2, INSERT_AC] THEN HolCore.Tactics.NO_TAC, ALL_TAC])
      [← q r"w1:real^3 = vec 0", ← q r"w2:real^3 = vec 0", ← q r"w1:real^3 = basis 3",
       ← q r"w2:real^3 = basis 3"] THEN
     ASM_CASES_TAC (← q r"w1:real^3 = v2 % basis 3") THENL
      [ASM_REWRITE_TAC [COLLINEAR_LEMMA] THEN MESON_TAC [], ALL_TAC] THEN
     ASM_CASES_TAC (← q r"w2:real^3 = v2 % basis 3") THENL
      [ASM_REWRITE_TAC [COLLINEAR_LEMMA] THEN MESON_TAC [], ALL_TAC])
    THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC [EXTENSION] THEN X_GEN_TAC (← q r"y:real^3") THEN
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
       (← q r"(dropout 3 (y:real^3)) IN
        aff_gt {vec 0:real^2,dropout 3 (w1:real^3)}
                {rotate2d (pi / &2) (dropout 3 (w1:real^3))}") THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE LAND_CONV [AZIM_ARG]) THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE (RAND_CONV o LAND_CONV)
         [AZIM_ARG]) THEN
        REPEAT (FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV
          [COLLINEAR_BASIS_3])) THEN
        POP_ASSUM_LIST (K ALL_TAC) THEN
        REWRITE_TAC [wedge, IN_ELIM_THM, AZIM_ARG, COLLINEAR_BASIS_3] THEN
        SPEC_TAC (← q r"(dropout 3:real^3->real^2) y", ← q r"x:real^2") THEN
        SPEC_TAC (← q r"(dropout 3:real^3->real^2) w2", ← q r"v2:real^2") THEN
        SPEC_TAC (← q r"(dropout 3:real^3->real^2) w1", ← q r"v1:real^2") THEN
        GEOM_BASIS_MULTIPLE_TAC 1 (← q r"v1:complex") THEN
        X_GEN_TAC (← q r"v:real") THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
        ASM_CASES_TAC (← q r"v = &0") THEN ASM_REWRITE_TAC [VECTOR_MUL_LZERO] THEN
        REWRITE_TAC [COMPLEX_CMUL, COMPLEX_BASIS, COMPLEX_VEC_0] THEN
        SIMP_TAC [ARG_DIV_CX, COMPLEX_MUL_RID] THEN
        REWRITE_TAC [real, RE_DIV_CX, IM_DIV_CX, CX_INJ] THEN
        ASM_SIMP_TAC [REAL_LT_LDIV_EQ, REAL_EQ_LDIV_EQ, REAL_MUL_LZERO] THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC [ARG_LT_PI, ROTATE2D_PI2] THEN
        W (MP_TAC o PART_MATCH (lhs o rand) AFF_GT_2_1 o rand o rand o snd) THEN
        ASM_REWRITE_TAC [DISJOINT_INSERT, DISJOINT_EMPTY, IN_SING] THEN
        ANTS_TAC THENL
         [CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
          ASM_REWRITE_TAC [COMPLEX_ENTIRE, II_NZ, CX_INJ] THEN
          DISCH_THEN (MP_TAC o AP_TERM (← q r"Re")) THEN
          REWRITE_TAC [RE_MUL_II, RE_CX, IM_CX] THEN ASM_REAL_ARITH_TAC,
          DISCH_THEN SUBST1_TAC] THEN
        REWRITE_TAC [COMPLEX_CMUL, IN_ELIM_THM, COMPLEX_MUL_RZERO] THEN
        ONCE_REWRITE_TAC [← MESON [] (← q r"(?a b c. P a b c) <=> (?b c a. P a b c)")] THEN
        REWRITE_TAC [← REAL_ARITH (← q r"t1 + t2 = &1 <=> t1 = &1 - t2")] THEN
        REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM2, COMPLEX_ADD_LID] THEN
        EQ_TAC THENL
         [DISCH_TAC THEN
          MAP_EVERY EXISTS_TAC [← q r"Re x / v", ← q r"Im x / v"] THEN
          ASM_SIMP_TAC [REAL_LT_DIV, COMPLEX_EQ, IM_ADD, RE_ADD] THEN
          REWRITE_TAC [RE_MUL_CX, IM_MUL_CX, RE_CX, IM_CX, RE_II, IM_II] THEN
          UNDISCH_TAC (← q r"~(v = &0)") THEN CONV_TAC REAL_FIELD,
          REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
          MAP_EVERY X_GEN_TAC [← q r"s:real", ← q r"t:real"] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC [COMPLEX_EQ, IM_ADD, RE_ADD] THEN
          REWRITE_TAC [RE_MUL_CX, IM_MUL_CX, RE_CX, IM_CX, RE_II, IM_II] THEN
          ASM_SIMP_TAC [REAL_MUL_RZERO, REAL_MUL_LID, REAL_LT_MUL, REAL_ADD_LID,
                       REAL_MUL_LZERO] THEN
          MAP_EVERY UNDISCH_TAC [← q r"&0 < v", ← q r"&0 < t"] THEN
          CONV_TAC REAL_FIELD],
        ALL_TAC] THEN
      W (MP_TAC o PART_MATCH (lhs o rand) AFF_GT_3_1 o rand o rand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [← SET_RULE
         (← q r"DISJOINT {a,b,c} {x} <=> ~(x = a) /\ ~(x = b) /\ ~(x = c)")] THEN
        ASM_SIMP_TAC [CROSS_EQ_0, CROSS_EQ_SELF, VECTOR_MUL_EQ_0, REAL_LT_IMP_NZ,
                     REAL_LT_IMP_NZ, BASIS_NONZERO, DIMINDEX_3,
                     ARITH, COLLINEAR_SPECIAL_SCALE],
        DISCH_THEN SUBST1_TAC] THEN
      W (MP_TAC o PART_MATCH (lhs o rand) AFF_GT_2_1 o rand o lhand o snd) THEN
      REWRITE_TAC [ROTATE2D_PI2] THEN ANTS_TAC THENL
       [REWRITE_TAC [← SET_RULE (← q r"DISJOINT {a,b} {x} <=> ~(x = a) /\ ~(x = b)")] THEN
        REWRITE_TAC [COMPLEX_ENTIRE, ← ExceptT.mk (COMPLEX_RING (← q r"ii * x = x <=> x = Cx(&0)")),
                    COMPLEX_VEC_0, II_NZ] THEN
        ASM_REWRITE_TAC [← GSYM COMPLEX_VEC_0, ← GSYM COLLINEAR_BASIS_3],
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC [IN_ELIM_THM, VECTOR_MUL_RZERO, VECTOR_ADD_LID] THEN
      ONCE_REWRITE_TAC [← MESON []
       (← q r"(?a b c d. P a b c d) <=> (?d c b a. P a b c d)")] THEN
      ONCE_REWRITE_TAC [← REAL_ARITH (← q r"s + t = &1 <=> s = &1 - t")] THEN
      REWRITE_TAC [UNWIND_THM2, RIGHT_EXISTS_AND_THM] THEN
      ONCE_REWRITE_TAC [← MESON [] (← q r"(?a b c. P a b c) <=> (?c b a. P a b c)")] THEN
      REWRITE_TAC [UNWIND_THM2, RIGHT_EXISTS_AND_THM] THEN
      REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN
      SIMP_TAC [CART_EQ, FORALL_2, FORALL_3, DIMINDEX_2, DIMINDEX_3,
        dropout, LAMBDA_BETA, BASIS_COMPONENT, ARITH, REAL_MUL_RID,
        VECTOR_MUL_COMPONENT, VEC_COMPONENT, REAL_MUL_RZERO, UNWIND_THM1,
        VECTOR_ADD_COMPONENT, cross, VECTOR_3,
        ← REWRITE_RULE [RE_DEF, IM_DEF] RE_MUL_II,
        ← REWRITE_RULE [RE_DEF, IM_DEF] IM_MUL_II,
        REAL_ADD_LID, REAL_MUL_LZERO, REAL_SUB_REFL, REAL_ADD_RID,
        REAL_SUB_LZERO, REAL_SUB_RZERO] THEN
      ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
      AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"s:real") THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM] THEN
      ASM_SIMP_TAC [EXISTS_REFL, ← REAL_FIELD
       (← q r"&0 < v ==> (x = a * v + b <=> a = (x - b) / v)")] THEN
      REWRITE_TAC [REAL_MUL_RNEG, REAL_MUL_ASSOC] THEN EQ_TAC THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"t:real") STRIP_ASSUME_TAC) THENL
       [EXISTS_TAC (← q r"t / v2:real"), EXISTS_TAC (← q r"t * v2:real")] THEN
      ASM_SIMP_TAC [REAL_DIV_RMUL, REAL_LT_DIV, REAL_LT_IMP_NZ, REAL_LT_MUL],
      ALL_TAC] THEN
    REWRITE_TAC [CROSS_LMUL] THEN
    SIMP_TAC [cross, BASIS_COMPONENT, DIMINDEX_3, ARITH, DOT_3, VECTOR_3,
        VECTOR_MUL_COMPONENT, REAL_MUL_LZERO, REAL_SUB_RZERO, REAL_NEG_0,
             REAL_MUL_RZERO, REAL_SUB_LZERO, REAL_MUL_LID, REAL_ADD_RID] THEN
    REWRITE_TAC [← REAL_ARITH
    (← q r"(v * --x2) * y1 + (v * x1) * y2 > &0 <=> &0 < v * (x1 * y2 - x2 * y1)")] THEN
    ASM_SIMP_TAC [REAL_LT_MUL_EQ, REAL_SUB_LT] THEN
    REWRITE_TAC [AZIM_ARG, COLLINEAR_BASIS_3] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"w1$2 * w2$1 < w1$1 * w2$2 <=>
      Arg(dropout 3 (w2:real^3) / dropout 3 (w1:real^3)) < pi")
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC (← q r"&0 < Im(dropout 3 (w2:real^3) / dropout 3 (w1:real^3))") THEN
      CONJ_TAC THENL
       [REWRITE_TAC [IM_COMPLEX_DIV_GT_0] THEN
        REWRITE_TAC [complex_mul, cnj, RE_DEF, IM_DEF, complex] THEN
        SIMP_TAC [dropout, VECTOR_2, LAMBDA_BETA, DIMINDEX_3, ARITH,
                 DIMINDEX_2] THEN
        REAL_ARITH_TAC,
        REWRITE_TAC [← GSYM ARG_LT_PI] THEN ASM_MESON_TAC [ARG_LT_NZ]],
      ALL_TAC] THEN
    COND_CASES_TAC THENL
     [W (MP_TAC o PART_MATCH (lhs o rand) AFF_GT_SPECIAL_SCALE o rand o snd) THEN
      ASM_REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY, IN_INSERT, NOT_IN_EMPTY] THEN
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC WEDGE_LUNE THEN
      ASM_SIMP_TAC [← GSYM AZIM_EQ_0_PI_EQ_COPLANAR, COLLINEAR_BASIS_3] THEN
      ASM_REWRITE_TAC [AZIM_ARG],
      ALL_TAC] THEN
    REWRITE_TAC [wedge] THEN
    GEN_REWRITE_TAC (funpow 3 RAND_CONV) [← SET_RULE (← q r"{a,b} = {b,a}")] THEN
    W (MP_TAC o PART_MATCH (rand o rand) WEDGE_LUNE_GE o rand o rand o snd) THEN
    ASM_SIMP_TAC [COLLINEAR_SPECIAL_SCALE, REAL_LT_IMP_NZ, AZIM_SPECIAL_SCALE] THEN
    ASM_REWRITE_TAC [AZIM_ARG, COLLINEAR_BASIS_3] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC [ARG_LT_NZ] THEN
      ONCE_REWRITE_TAC [← GSYM ARG_INV_EQ_0] THEN
      ASM_REWRITE_TAC [COMPLEX_INV_DIV] THEN
      ONCE_REWRITE_TAC [← GSYM COMPLEX_INV_DIV] THEN
      ASM_SIMP_TAC [ARG_INV, ← GSYM ARG_EQ_0] THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [EXTENSION, IN_DIFF, IN_UNIV, IN_ELIM_THM, ARG] THEN
    REWRITE_TAC [REAL_NOT_LE] THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist CONJ) THEN
    SPEC_TAC (← q r"(dropout 3:real^3->real^2) w1", ← q r"w:complex") THEN
    SPEC_TAC (← q r"(dropout 3:real^3->real^2) w2", ← q r"z:complex") THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC (← q r"x3:real^3") THEN
    SPEC_TAC (← q r"(dropout 3:real^3->real^2) x3", ← q r"x:complex") THEN
    GEN_TAC THEN REWRITE_TAC [COMPLEX_VEC_0] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [COMPLEX_VEC_0]) THEN
    ASM_CASES_TAC (← q r"x = Cx(&0)") THEN ASM_REWRITE_TAC [] THENL
     [ASM_REWRITE_TAC [complex_div, COMPLEX_MUL_LZERO, REAL_NOT_LT, ARG, ARG_0],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [ARG_LT_NZ] THEN
    MAP_EVERY UNDISCH_TAC
     [← q r"~(Arg (z / w) < pi)",
      ← q r"~(Arg (z / w) = pi)",
      ← q r"~(Arg (z / w) = &0)",
      ← q r"~(x = Cx (&0))",
      ← q r"~(w = Cx (&0))",
      ← q r"~(z = Cx (&0))"] THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN REWRITE_TAC [← GSYM COMPLEX_VEC_0] THEN
    GEOM_BASIS_MULTIPLE_TAC 1 (← q r"w:complex") THEN
    X_GEN_TAC (← q r"w:real") THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
    ASM_CASES_TAC (← q r"w = &0") THEN ASM_REWRITE_TAC [VECTOR_MUL_LZERO] THEN
    REWRITE_TAC [COMPLEX_CMUL, COMPLEX_BASIS, COMPLEX_VEC_0] THEN
    SIMP_TAC [ARG_DIV_CX, COMPLEX_MUL_RID] THEN
    REWRITE_TAC [real, RE_DIV_CX, IM_DIV_CX, CX_INJ] THEN
    SIMP_TAC [complex_div, ARG_MUL_CX] THEN
    SIMP_TAC [ARG_INV, ← GSYM ARG_EQ_0, ARG_INV_EQ_0] THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM complex_div] THEN
    ASM_CASES_TAC (← q r"Arg x = &0") THEN ASM_REWRITE_TAC [] THENL
     [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [ARG_EQ_0]) THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      REWRITE_TAC [REAL] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      REWRITE_TAC [complex_div, CX_INJ] THEN
      ASM_SIMP_TAC [ARG_MUL_CX, REAL_LT_LE] THEN
      ASM_SIMP_TAC [ARG_INV, ← GSYM ARG_EQ_0],
      ALL_TAC] THEN
    REWRITE_TAC [IMP_IMP, ← GSYM CONJ_ASSOC] THEN
    SIMP_TAC [PI_POS, ← REAL_ARITH
     (← q r"&0 < pi ==> (~(z = &0) /\ ~(z = pi) /\ ~(z < pi) <=> pi < z)")] THEN
    STRIP_TAC THEN REWRITE_TAC [REAL_LT_SUB_RADD] THEN
    DISJ_CASES_TAC (← REAL_ARITH (← q r"Arg z <= Arg x \/ Arg x < Arg z")) THENL
     [ASM_REWRITE_TAC [← GSYM REAL_NOT_LE] THEN
      ONCE_REWRITE_TAC [REAL_ADD_SYM] THEN
      ASM_SIMP_TAC [← GSYM ARG_LE_DIV_SUM] THEN
      SIMP_TAC [ARG, REAL_LT_IMP_LE],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (← ISPECL [← q r"x:complex", ← q r"z:complex"] ARG_LE_DIV_SUM) THEN
    ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"&0 <= x /\ ~(x = &0) /\ y = k - z ==> k < y + x + z")) THEN
    ASM_REWRITE_TAC [ARG] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM COMPLEX_INV_DIV] THEN
    MATCH_MP_TAC ARG_INV THEN REWRITE_TAC [REAL] THEN
    DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN
    ABBREV_TAC (← q r"t = Re(z / x)") THEN UNDISCH_TAC (← q r"Arg x < Arg z") THEN
    UNDISCH_TAC (← q r"z / x = Cx t") THEN
    ASM_SIMP_TAC [← ExceptT.mk (COMPLEX_FIELD
     (← q r"~(x = Cx(&0)) ==> (z / x = t <=> z = t * x)"))] THEN
    ASM_CASES_TAC (← q r"t = &0") THEN ASM_REWRITE_TAC [COMPLEX_MUL_LZERO] THEN
    ASM_SIMP_TAC [ARG_MUL_CX, REAL_LT_LE])

  let OPEN_WEDGE ← prove
   r"!z:real^3 w w1 w2. open(wedge z w w1 w2)"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"z:real^3 = w \/  collinear{z,w,w1} \/ collinear{z,w,w2}") THENL
     [FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
      ASM_SIMP_TAC [WEDGE_DEGENERATE, OPEN_EMPTY],
      FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC [DE_MORGAN_THM]] THEN
    REWRITE_TAC [wedge] THEN GEOM_ORIGIN_TAC (← q r"z:real^3") THEN
    GEOM_BASIS_MULTIPLE_TAC 3 (← q r"w:real^3") THEN
    X_GEN_TAC (← q r"w:real") THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
    ASM_CASES_TAC (← q r"w = &0") THEN ASM_REWRITE_TAC [VECTOR_MUL_LZERO] THEN
    ASM_SIMP_TAC [AZIM_SPECIAL_SCALE, COLLINEAR_SPECIAL_SCALE] THEN
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"~a /\ b /\ c <=> ~(~a ==> ~(b /\ c))")] THEN
    ASM_SIMP_TAC [AZIM_ARG] THEN REWRITE_TAC [COLLINEAR_BASIS_3] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [COLLINEAR_BASIS_3]) THEN
    REWRITE_TAC [NOT_IMP, ← GSYM CONJ_ASSOC, DROPOUT_0] THEN
    MATCH_MP_TAC OPEN_DROPOUT_3 THEN
    UNDISCH_TAC (← q r"~((dropout 3:real^3->real^2) w1 = vec 0)") THEN
    UNDISCH_TAC (← q r"~((dropout 3:real^3->real^2) w2 = vec 0)") THEN
    SPEC_TAC (← q r"(dropout 3:real^3->real^2) w2", ← q r"v2:complex") THEN
    SPEC_TAC (← q r"(dropout 3:real^3->real^2) w1", ← q r"v1:complex") THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN GEOM_BASIS_MULTIPLE_TAC 1 (← q r"v1:complex") THEN
    X_GEN_TAC (← q r"v1:real") THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
    ASM_CASES_TAC (← q r"v1 = &0") THEN ASM_REWRITE_TAC [VECTOR_MUL_LZERO] THEN
    REWRITE_TAC [COMPLEX_CMUL, COMPLEX_BASIS, COMPLEX_VEC_0] THEN
    SIMP_TAC [ARG_DIV_CX, COMPLEX_MUL_RID] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [← SET_RULE (← q r"{x | ~(x = a) /\ P x} = {x | P x} DIFF {a}")] THEN
    MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC [CLOSED_SING] THEN
    MATCH_MP_TAC OPEN_ARG_LTT THEN
    SIMP_TAC [REAL_LT_IMP_LE, REAL_LE_REFL, ARG])

  let ARG_EQ_SUBSET_HALFLINE ← prove
   r"!a. ?b. ~(b = vec 0) /\ {z | Arg z = a} SUBSET aff_ge {vec 0} {b}"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"{z | Arg z = a} SUBSET {vec 0}") THENL
     [EXISTS_TAC (← q r"basis 1:real^2") THEN
      SIMP_TAC [BASIS_NONZERO, DIMINDEX_2, ARITH] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
         SUBSET_TRANS)) THEN SIMP_TAC [SUBSET, IN_SING, ENDS_IN_HALFLINE],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP (← SET_RULE
     (← q r"~(s SUBSET {a}) ==> ?z. ~(a = z) /\ z IN s"))) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"z:complex") THEN
    REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"x:complex") THEN
    ASM_CASES_TAC (← q r"x:complex = vec 0") THEN ASM_REWRITE_TAC [ENDS_IN_HALFLINE] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [COMPLEX_VEC_0]) THEN ASM_SIMP_TAC [ARG_EQ] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:real") STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [← GSYM COMPLEX_CMUL] THEN
    REWRITE_TAC [HALFLINE_EXPLICIT, IN_ELIM_THM, VECTOR_MUL_RZERO] THEN
    MAP_EVERY EXISTS_TAC [← q r"&1 - u", ← q r"u:real"] THEN
    ASM_SIMP_TAC [VECTOR_ADD_LID, REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC)

  let ARG_DIV_EQ_SUBSET_HALFLINE ← prove
   r"!w a. ~(w = vec 0)
           ==> ?b. ~(b = vec 0) /\
                   {z | Arg(z / w) = a} SUBSET aff_ge {vec 0} {b}"
   (REPEAT GEN_TAC THEN GEOM_BASIS_MULTIPLE_TAC 1 (← q r"w:complex") THEN
    X_GEN_TAC (← q r"w:real") THEN ASM_CASES_TAC (← q r"w = &0") THEN
    ASM_REWRITE_TAC [VECTOR_MUL_LZERO, REAL_LE_LT] THEN DISCH_TAC THEN
    X_GEN_TAC (← q r"a:real") THEN DISCH_THEN (K ALL_TAC : thm → tactic) THEN
    ASM_SIMP_TAC [ARG_DIV_CX, COMPLEX_CMUL, COMPLEX_BASIS, ← GSYM CX_MUL,
                 REAL_MUL_RID, ARG_EQ_SUBSET_HALFLINE])

  let COPLANAR_AZIM_EQ ← prove
   r"!v0 v1 w1 a.
       (collinear{v0,v1,w1} ==> ~(a = &0))
       ==> coplanar {z | azim v0 v1 w1 z = a}"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"collinear{v0:real^3,v1,w1}") THENL
     [ASM_SIMP_TAC [azim_def, EMPTY_GSPEC, COPLANAR_EMPTY], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN POP_ASSUM MP_TAC THEN
    GEOM_ORIGIN_TAC (← q r"v0:real^3") THEN
    GEOM_BASIS_MULTIPLE_TAC 3 (← q r"v1:real^3") THEN
    X_GEN_TAC (← q r"v1:real") THEN ASM_CASES_TAC (← q r"v1 = &0") THENL
     [ASM_REWRITE_TAC [VECTOR_MUL_LZERO, INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    ASM_SIMP_TAC [REAL_LE_LT, COLLINEAR_SPECIAL_SCALE] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [AZIM_SPECIAL_SCALE, AZIM_ARG] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [COLLINEAR_BASIS_3]) THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"b:real^2")
     STRIP_ASSUME_TAC o SPEC (← q r"a:real") o MATCH_MP ARG_DIV_EQ_SUBSET_HALFLINE) THEN
    REWRITE_TAC [coplanar] THEN MAP_EVERY EXISTS_TAC
     [← q r"vec 0:real^3", ← q r"pushin 3 (&0) (b:real^2):real^3", ← q r"basis 3:real^3"] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [SUBSET]) THEN
    REWRITE_TAC [AFFINE_HULL_3, HALFLINE, SUBSET, IN_ELIM_THM] THEN
    DISCH_THEN (fun th => tactic_of do pure (X_GEN_TAC (← q r"x:real^3") THEN DISCH_TAC THEN
     MP_TAC (← SPEC (← q r"(dropout 3:real^3->real^2) x") th))) THEN
    ASM_REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_ADD_LID] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"v:real") STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [← q r"&1 - v - (x:real^3)$3", ← q r"v:real", ← q r"(x:real^3)$3"] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC, ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [CART_EQ]) THEN
    SIMP_TAC [CART_EQ, DIMINDEX_2, DIMINDEX_3, FORALL_2, FORALL_3, LAMBDA_BETA,
             dropout, pushin, VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, ARITH,
             BASIS_COMPONENT] THEN
    REAL_ARITH_TAC)

  pure { WEDGE, OPEN_WEDGE, ARG_EQ_SUBSET_HALFLINE, ARG_DIV_EQ_SUBSET_HALFLINE,
         COPLANAR_AZIM_EQ }
/- ------------------------------------------------------------------------- -/
/- Volume of a tetrahedron defined by conv0; circle area; volume of a ball;  -/
/- frustum.                                                                  -/
/- (flyspeck.ml 4396-4777)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FYP where
  delta_x : thm
  VOLUME_OF_CLOSED_TETRAHEDRON : thm
  VOLUME_OF_TETRAHEDRON : thm
  AREA_UNIT_CBALL : thm
  AREA_CBALL : thm
  AREA_BALL : thm
  VOLUME_CBALL : thm
  VOLUME_BALL : thm
  rconesgn : thm
  rcone_gt : thm
  rcone_ge : thm
  rcone_eq : thm
  frustum : thm
  frustt : thm
  FRUSTUM_DEGENERATE : thm
  CONVEX_RCONE_GT : thm
  OPEN_RCONE_GT : thm
  RCONE_GT_NEG : thm
  VOLUME_FRUSTT_STRONG : thm
  VOLUME_FRUSTT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYP [HolBase] (D : FlyspeckDeps) (BFYA : FYA) (BFYG : FYG) : ExceptT String IO FYP := do
  -- @@SCOPE BEGIN
  let { SLICE_312, .. } := BFYA
  let { MEASURE_CONV0_CONVEX_HULL, .. } := BFYG
  let { let_CONV, .. } := D
  let { ASM_MESON_TAC, MESON_TAC, new_definition, REAL_ARITH_TAC, REAL_RING, .. } := D.crd
  let { MEASURABLE_CBALL, MEASURE_INTERIOR, MEASURE_TETRAHEDRON, MEASURE_UNIQUE,
        NEGLIGIBLE_CONVEX_FRONTIER, .. } := D.qmeasure
  let { LET_DEF, LET_END_DEF, REAL_CONVEX_BOUND2_LT, .. } := D.qsession
  let { GEOM_ORIGIN_TAC, .. } := D.geomorigin
  let { REAL_CONTINUOUS_ON_ADD, REAL_CONTINUOUS_ON_COMPOSE, REAL_CONTINUOUS_ON_CONST,
        REAL_CONTINUOUS_ON_ID, REAL_CONTINUOUS_ON_MUL, REAL_CONTINUOUS_ON_POW,
        REAL_CONTINUOUS_ON_SUB, .. } := D.gm.rzj
  let { REAL_CONTINUOUS_ON_SQRT, .. } := D.gm.rzp
  let { REAL_CONTINUOUS_ON_ASN, REAL_DIFF_TAC, .. } := D.gm.rzq
  let { HAS_REAL_INTEGRAL_EMPTY, HAS_REAL_INTEGRAL_EQ, .. } := D.gm.rzal
  let { REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS, .. } := D.gm.rzan
  let { HAS_REAL_INTEGRAL_RESTRICT_UNIV, REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR,
        .. } := D.gm.rzao
  let { HAS_REAL_INTEGRAL_OPEN_INTERVAL, .. } := D.gm.rzap
  let { SLICE_CBALL, .. } := D.gm.rzaz
  let { FUBINI_SIMPLE_COMPACT, FUBINI_SIMPLE_CONVEX_STRONG, .. } := D.gm.rzbc
  let { DOT_3, .. } := D.gm.qvectors
  let { ARITH, CONJ_ASSOC, CONTINUOUS_SUB, DIMINDEX_3, DOT_RZERO, LIFT_CMUL, LIFT_SUB,
        NORM_POS_LE, NORM_POW_2, o_DEF, real_abs, REAL_LE_MUL, REAL_MUL_LZERO,
        REAL_POW_MUL, REAL_SUB_RZERO, VECTOR_3, .. } := D.crd.thms
  let { ASN_1, ASN_NEG_1, .. } := D.gm.ra.tsv
  let { DROPOUT_0, .. } := D.gm.ra.qvectors
  let { IN_REAL_INTERVAL, REAL_INTERVAL_EQ_EMPTY, .. } := D.gm.ra.qmisc
  let { HAS_MEASURE_0, HAS_MEASURE_AFFINITY, HAS_MEASURE_MEASURABLE_MEASURE,
        MEASURABLE_EMPTY, MEASURE_EMPTY, MEASURE_INTERVAL, .. } := D.gm.ra.qmeasure
  let { CONVEX_HALFSPACE_COMPONENT_LT, .. } := D.gm.ra.ts.qconvex
  let { ABS_SQUARE_LT_1, .. } := D.gm.ra.ts.qmisc
  let { REAL_POW_1_LT, .. } := D.gm.ra.ts.cn.qsession
  let { CONTENT_1, .. } := D.gm.ra.ts.cn.ms.qintegration1
  let { NEGLIGIBLE_SING, .. } := D.gm.ra.ts.cn.ms.qintegration3
  let { REAL_BOUNDS_LT, .. } := D.gm.ra.ts.cn.ms.qsession
  let { ARITH_TAC, ASM_REAL_ARITH_TAC, GEOM_BASIS_MULTIPLE_TAC, NORM_ARITH, NORM_ARITH_TAC,
        NUM_REDUCE_CONV, REAL_ARITH, REAL_FIELD, REAL_RAT_REDUCE_CONV, SET_RULE, SET_TAC,
        VECTOR_ARITH, .. } := D.gm.ra.ts.cn.cx.cvx
  let { REAL_POW_1, REAL_SUB_LZERO, SQRT_POS_LT, .. } := D.gm.ra.ts.cn.cx.cpx
  let { CONTINUOUS_OPEN_PREIMAGE_UNIV, .. } := D.gm.ra.ts.cn.ms.ig.qtopology
  let { CARD_CLAUSES, COND_RAND, DIMINDEX_1, DIMINDEX_2, EMPTY_GSPEC, EQ_IMP, EQ_TRANS,
        EXTENSION, FINITE_EMPTY, FINITE_INSERT, .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, IMP_CONJ, IN_DIFF, .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, IN_UNIV, REAL_ABS_INV, REAL_ABS_MUL, REAL_ABS_NUM,
        REAL_ABS_POS, REAL_ADD_RDISTRIB, REAL_ADD_RID, .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_INV_1_LT, REAL_INV_MUL, REAL_LE_LDIV_EQ, REAL_LE_LMUL, REAL_LE_MUL2,
        REAL_LE_RMUL, REAL_LE_SQUARE_ABS, REAL_LET_TRANS, REAL_LT_IMP_LE, REAL_LT_IMP_NZ,
        REAL_LT_LMUL_EQ, REAL_LT_MUL, REAL_LT_MUL_EQ, REAL_LT_RDIV_EQ, REAL_LT_REFL,
        REAL_LTE_TRANS, .. } := D.gm.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_RID, REAL_MUL_RINV, REAL_MUL_RNEG,
        REAL_MUL_RZERO, REAL_MUL_SYM, REAL_NOT_LE, REAL_NOT_LT, REAL_POS, REAL_POW2_ABS,
        REAL_POW_2, REAL_POW_DIV, REAL_POW_LE2, REAL_POW_LT, REAL_POW_ONE, REAL_SUB_LE,
        REAL_SUB_LT, SQRT_0, SQRT_POS_LE, SQRT_POW_2, SUBSET, SUBSET_ANTISYM,
        .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { real_div, real_gt, SURJECTIVE_IMAGE_EQ, .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { BASIS_NONZERO, COMPONENT_LE_NORM, DIST_0, DOT_2, DOT_BASIS, DOT_LADD, DOT_LMUL,
        DOT_LNEG, DOT_RMUL, .. } := D.gm.ra.ts.cn.cx.cvx.vec1
  let { DOT_SYM, LIFT_DROP, NORM_0, NORM_BASIS, .. } := D.gm.ra.ts.cn.cx.cvx.vec2
  let { NORM_MUL, NORM_POS_LT, NORM_SUB, .. } := D.gm.ra.ts.cn.cx.cvx.vec3
  let { dist, drop, VEC_COMPONENT, VECTOR_ADD_LID, VECTOR_MUL_ASSOC, VECTOR_MUL_EQ_0,
        VECTOR_MUL_LZERO, VECTOR_SUB_COMPONENT, VECTOR_SUB_LZERO, VECTOR_SUB_REFL,
        VECTOR_SUB_RZERO, .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { BOUNDED_BALL, BOUNDED_CBALL, BOUNDED_EMPTY, BOUNDED_SUBSET, CBALL_SING,
        .. } := D.gm.ra.ts.cn.cx.cvx.top1
  let { COMPACT_CBALL, CONTINUOUS_AT_LIFT_NORM, .. } := D.gm.ra.ts.cn.cx.cvx.top2
  let { IN_BALL_0, IN_CBALL, IN_CBALL_0, INTERIOR_CBALL, OPEN_HALFSPACE_COMPONENT_GT,
        .. } := D.gm.ra.ts.cn.cx.cvx.top4
  let { NORM_LT_SQUARE, .. } := D.gm.ra.ts.cn.ms.ig.dv.qvec
  let { SQRT_UNIQUE, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.qsession
  let { BALL_1, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.qtopology1
  let { REAL_BOUNDS_LE, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qses
  let { DROP_NEG, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qvec
  let { CONTINUOUS_AT_LIFT_DOT, CONTINUOUS_CMUL, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qtop
  let { CONVEX_ALT, CONVEX_CBALL, CONVEX_EMPTY, CONVEX_INTER,
        .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  -- @@SCOPE END

  let delta_x ← new_definition
   r"delta_x x1 x2 x3 x4 x5 x6 =
          x1*x4*(--x1 + x2 + x3 -x4 + x5 + x6) +
          x2*x5*(x1 - x2 + x3 + x4 -x5 + x6) +
          x3*x6*(x1 + x2 - x3 + x4 + x5 - x6)
          -x2*x3*x4 - x1*x3*x5 - x1*x2*x6 -x4*x5*x6:real"

  let VOLUME_OF_CLOSED_TETRAHEDRON ← prove
   r"!x1 x2 x3 x4:real^3.
       measure(convex hull {x1,x2,x3,x4}) =
       sqrt(delta_x (dist(x1,x2) pow 2) (dist(x1,x3) pow 2) (dist(x1,x4) pow 2)
                    (dist(x3,x4) pow 2) (dist(x2,x4) pow 2) (dist(x2,x3) pow 2))
        / &12"
   (REPEAT GEN_TAC THEN REWRITE_TAC [LET_DEF, LET_END_DEF] THEN
    REWRITE_TAC [MEASURE_TETRAHEDRON] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"x / &6 = y / &12 <=> y = &2 * x")] THEN
    MATCH_MP_TAC SQRT_UNIQUE THEN
    SIMP_TAC [REAL_LE_MUL, REAL_ABS_POS, REAL_POS] THEN
    REWRITE_TAC [REAL_POW_MUL, REAL_POW2_ABS, delta_x] THEN
    REWRITE_TAC [dist, NORM_POW_2] THEN
    SIMP_TAC [DOT_3, VECTOR_SUB_COMPONENT, DIMINDEX_3, ARITH] THEN
    CONV_TAC REAL_RING)

  let VOLUME_OF_TETRAHEDRON ← prove
   r"!v1 v2 v3 v4:real^3.
          measure(conv0 {v1,v2,v3,v4}) =
              let x12 = dist(v1,v2) pow 2 in
              let x13 = dist(v1,v3) pow 2 in
              let x14 = dist(v1,v4) pow 2 in
              let x23 = dist(v2,v3) pow 2 in
              let x24 = dist(v2,v4) pow 2 in
              let x34 = dist(v3,v4) pow 2 in
              sqrt(delta_x x12 x13 x14 x34 x24 x23)/(&12)"
   (REPEAT GEN_TAC THEN CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    ASM_SIMP_TAC [← GSYM VOLUME_OF_CLOSED_TETRAHEDRON] THEN
    MATCH_MP_TAC MEASURE_CONV0_CONVEX_HULL THEN
    SIMP_TAC [DIMINDEX_3, FINITE_INSERT, FINITE_EMPTY, CARD_CLAUSES] THEN
    ARITH_TAC)

  /- Circle area. Should maybe extend WLOG tactics for such scaling. -/

  let AREA_UNIT_CBALL ← prove
   r"measure(cball(vec 0:real^2,&1)) = pi"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← HolLight.INST_TYPE [(← qty "1", ← qty "M"), (← qty "2", ← qty "N")]
      FUBINI_SIMPLE_COMPACT) THEN
    EXISTS_TAC (← q r"1") THEN
    SIMP_TAC [DIMINDEX_1, DIMINDEX_2, ARITH, COMPACT_CBALL, SLICE_CBALL] THEN
    REWRITE_TAC [VEC_COMPONENT, DROPOUT_0, REAL_SUB_RZERO] THEN
    ONCE_REWRITE_TAC [COND_RAND] THEN REWRITE_TAC [MEASURE_EMPTY] THEN
    SUBGOAL_THEN (← q r"!t. abs(t) <= &1 <=> t IN real_interval[-- &1,&1]")
     (fun th => REWRITE_TAC [th])
    THENL [REWRITE_TAC [IN_REAL_INTERVAL] THEN REAL_ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [HAS_REAL_INTEGRAL_RESTRICT_UNIV, BALL_1] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
    EXISTS_TAC (← q r"\t. &2 * sqrt(&1 - t pow 2)") THEN CONJ_TAC THENL
     [X_GEN_TAC (← q r"t:real") THEN SIMP_TAC [IN_REAL_INTERVAL, MEASURE_INTERVAL] THEN
      REWRITE_TAC [REAL_BOUNDS_LE, VECTOR_ADD_LID, VECTOR_SUB_LZERO] THEN
      DISCH_TAC THEN
      W (MP_TAC o PART_MATCH (lhs o rand) CONTENT_1 o rand o snd) THEN
      REWRITE_TAC [LIFT_DROP, DROP_NEG] THEN
      ANTS_TAC THENL [ALL_TAC, SIMP_TAC [REAL_POW_ONE] THEN REAL_ARITH_TAC] THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"&0 <= x ==> --x <= x")) THEN
      ASM_SIMP_TAC [SQRT_POS_LE, REAL_SUB_LE, ← GSYM REAL_LE_SQUARE_ABS,
                   REAL_ABS_NUM],
      ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"\x.  asn(x) + x * sqrt(&1 - x pow 2)",
      ← q r"\x. &2 * sqrt(&1 - x pow 2)",
      ← q r"-- &1", ← q r"&1"] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR) THEN
    REWRITE_TAC [ASN_1, ASN_NEG_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [SQRT_0, REAL_MUL_RZERO, REAL_ADD_RID] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"x / &2 - --(x / &2) = x")] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN
      SIMP_TAC [REAL_CONTINUOUS_ON_ASN, IN_REAL_INTERVAL, REAL_BOUNDS_LE] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
      REWRITE_TAC [REAL_CONTINUOUS_ON_ID] THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM o_DEF] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC [REAL_CONTINUOUS_ON_SUB, REAL_CONTINUOUS_ON_POW,
               REAL_CONTINUOUS_ON_ID, REAL_CONTINUOUS_ON_CONST] THEN
      REWRITE_TAC [REAL_CONTINUOUS_ON_SQRT],
      REWRITE_TAC [IN_REAL_INTERVAL, REAL_BOUNDS_LT] THEN REPEAT STRIP_TAC THEN
      REAL_DIFF_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC [REAL_MUL_LID, REAL_POW_1, REAL_MUL_RID] THEN
      REWRITE_TAC [REAL_SUB_LZERO, REAL_MUL_RNEG, REAL_INV_MUL] THEN
      ASM_REWRITE_TAC [REAL_SUB_LT, ABS_SQUARE_LT_1] THEN
      MATCH_MP_TAC (← REAL_FIELD
       (← q r"s pow 2 = &1 - x pow 2 /\ x pow 2 < &1
        ==> (inv s + x * --(&2 * x) * inv (&2) * inv s + s) = &2 * s")) THEN
      ASM_SIMP_TAC [ABS_SQUARE_LT_1, SQRT_POW_2, REAL_SUB_LE, REAL_LT_IMP_LE]])

  let AREA_CBALL ← prove
   r"!z:real^2 r. &0 <= r ==> measure(cball(z,r)) = pi * r pow 2"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"r = &0") THENL
     [ASM_SIMP_TAC [CBALL_SING, REAL_POW_2, REAL_MUL_RZERO] THEN
      MATCH_MP_TAC MEASURE_UNIQUE THEN
      REWRITE_TAC [HAS_MEASURE_0, NEGLIGIBLE_SING],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&0 < r") ASSUME_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"cball(vec 0:real^2,&1)", ← q r"r:real", ← q r"z:real^2", ← q r"pi"]
          HAS_MEASURE_AFFINITY) THEN
    REWRITE_TAC [HAS_MEASURE_MEASURABLE_MEASURE, MEASURABLE_CBALL,
                AREA_UNIT_CBALL] THEN
    ASM_REWRITE_TAC [real_abs, DIMINDEX_2] THEN
    DISCH_THEN (MP_TAC o CONJUNCT2) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
    REWRITE_TAC [IN_CBALL_0, IN_IMAGE] THEN REWRITE_TAC [IN_CBALL] THEN
    REWRITE_TAC [← NORM_ARITH (← q r"dist(z,a + z) = norm a"), NORM_MUL] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"abs r * x <= r <=> abs r * x <= r * &1")] THEN
    ASM_SIMP_TAC [real_abs, REAL_LE_LMUL, dist] THEN X_GEN_TAC (← q r"w:real^2") THEN
    DISCH_TAC THEN EXISTS_TAC (← q r"inv(r) % (w - z):real^2") THEN
    ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_RINV] THEN
    CONJ_TAC THENL [NORM_ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [NORM_MUL, REAL_ABS_INV] THEN ASM_REWRITE_TAC [real_abs] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    ASM_SIMP_TAC [← GSYM real_div, REAL_LE_LDIV_EQ, REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC [NORM_SUB] THEN ASM_REWRITE_TAC [])

  let AREA_BALL ← prove
   r"!z:real^2 r. &0 <= r ==> measure(ball(z,r)) = pi * r pow 2"
   (SIMP_TAC [← GSYM INTERIOR_CBALL, ← GSYM AREA_CBALL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_INTERIOR THEN
    SIMP_TAC [BOUNDED_CBALL, NEGLIGIBLE_CONVEX_FRONTIER, CONVEX_CBALL])

  /- Volume of a ball. -/

  let VOLUME_CBALL ← prove
   r"!z:real^3 r. &0 <= r ==> measure(cball(z,r)) = &4 / &3 * pi * r pow 3"
   (GEOM_ORIGIN_TAC (← q r"z:real^3") THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← HolLight.INST_TYPE [(← qty "2", ← qty "M"), (← qty "3", ← qty "N")]
      FUBINI_SIMPLE_COMPACT) THEN
    EXISTS_TAC (← q r"1") THEN
    SIMP_TAC [DIMINDEX_2, DIMINDEX_3, ARITH, COMPACT_CBALL, SLICE_CBALL] THEN
    REWRITE_TAC [VEC_COMPONENT, DROPOUT_0, REAL_SUB_RZERO] THEN
    ONCE_REWRITE_TAC [COND_RAND] THEN REWRITE_TAC [MEASURE_EMPTY] THEN
    SUBGOAL_THEN (← q r"!t. abs(t) <= r <=> t IN real_interval[--r,r]")
     (fun th => REWRITE_TAC [th])
    THENL [REWRITE_TAC [IN_REAL_INTERVAL] THEN REAL_ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
    EXISTS_TAC (← q r"\t. pi * (r pow 2 - t pow 2)") THEN CONJ_TAC THENL
     [X_GEN_TAC (← q r"t:real") THEN REWRITE_TAC [IN_REAL_INTERVAL, REAL_BOUNDS_LE] THEN
      SIMP_TAC [AREA_CBALL, SQRT_POS_LE, REAL_SUB_LE, ← GSYM REAL_LE_SQUARE_ABS,
               SQRT_POW_2, ← REAL_ARITH (← q r"abs x <= r ==> abs x <= abs r")],
      ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"\t. pi * (r pow 2 * t - &1 / &3 * t pow 3)",
      ← q r"\t. pi * (r pow 2 - t pow 2)",
      ← q r"--r:real", ← q r"r:real"] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING,
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC REAL_RING])

  let VOLUME_BALL ← prove
   r"!z:real^3 r. &0 <= r ==> measure(ball(z,r)) =  &4 / &3 * pi * r pow 3"
   (SIMP_TAC [← GSYM INTERIOR_CBALL, ← GSYM VOLUME_CBALL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_INTERIOR THEN
    SIMP_TAC [BOUNDED_CBALL, NEGLIGIBLE_CONVEX_FRONTIER, CONVEX_CBALL])

  /- Frustum. -/

  let rconesgn ← new_definition
   r"rconesgn sgn v w h =
         {x:real^A | sgn ((x-v) dot (w-v)) (dist(x,v)*dist(w,v)*h)}"

  let rcone_gt ← new_definition r"rcone_gt = rconesgn ( > )"

  let rcone_ge ← new_definition r"rcone_ge = rconesgn ( >= )"

  let rcone_eq ← new_definition r"rcone_eq = rconesgn ( = )"

  let frustum ← new_definition
   r"frustum v0 v1 h1 h2 a =
       { y:real^N | rcone_gt v0 v1 a y /\
                    let d = (y - v0) dot (v1 - v0) in
                    let n = norm(v1 - v0) in
                    (h1*n < d /\ d < h2*n)}"

  let frustt ← new_definition r"frustt v0 v1 h a = frustum v0 v1 (&0) h a"

  let FRUSTUM_DEGENERATE ← prove
   r"!v0 h1 h2 a. frustum v0 v0 h1 h2 a = {}"
   (REWRITE_TAC [frustum, VECTOR_SUB_REFL, NORM_0, DOT_RZERO] THEN
    CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC [REAL_MUL_RZERO, REAL_LT_REFL] THEN SET_TAC [])

  let CONVEX_RCONE_GT ← prove
   r"!v0 v1:real^N a. &0 <= a ==> convex(rcone_gt v0 v1 a)"
   (REWRITE_TAC [rcone_gt, rconesgn] THEN
    GEOM_ORIGIN_TAC (← q r"v0:real^N") THEN REPEAT GEN_TAC THEN
    REWRITE_TAC [VECTOR_SUB_RZERO, DIST_0] THEN
    REWRITE_TAC [CONVEX_ALT, IN_ELIM_THM, real_gt, DOT_LADD, DOT_LMUL] THEN
    DISCH_TAC THEN MAP_EVERY X_GEN_TAC [← q r"x:real^N", ← q r"y:real^N", ← q r"t:real"] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (← q r"(&1 - t) * norm(x:real^N) * norm v1 * a +
                t * norm(y:real^N) * norm(v1:real^N) * a") THEN
    CONJ_TAC THENL
     [REWRITE_TAC [← GSYM REAL_ADD_RDISTRIB, REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [NORM_POS_LE] THEN
      MATCH_MP_TAC (← NORM_ARITH
       (← q r"norm(x:real^N) = a /\ norm(y) = b ==> norm(x + y) <= a + b")) THEN
      REWRITE_TAC [NORM_MUL] THEN CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_REAL_ARITH_TAC,
      MATCH_MP_TAC REAL_CONVEX_BOUND2_LT THEN ASM_REAL_ARITH_TAC])

  let OPEN_RCONE_GT ← prove
   r"!v0 v1:real^N a. open(rcone_gt v0 v1 a)"
   (REWRITE_TAC [rcone_gt, rconesgn] THEN
    GEOM_ORIGIN_TAC (← q r"v0:real^N") THEN REPEAT GEN_TAC THEN
    REWRITE_TAC [VECTOR_SUB_RZERO, DIST_0] THEN
    MP_TAC (← ISPECL [← q r"\x:real^N. lift(x dot v1 - norm x * norm v1 * a)",
                   ← q r"{x:real^1 | x$1 > &0}"]
          CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
    REWRITE_TAC [OPEN_HALFSPACE_COMPONENT_GT] THEN REWRITE_TAC [← GSYM drop] THEN
    REWRITE_TAC [IN_ELIM_THM, real_gt, REAL_SUB_LT, LIFT_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN GEN_TAC THEN REWRITE_TAC [LIFT_SUB] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_SUB THEN ONCE_REWRITE_TAC [DOT_SYM] THEN
    REWRITE_TAC [← REWRITE_RULE [o_DEF] CONTINUOUS_AT_LIFT_DOT] THEN
    MATCH_MP_TAC CONTINUOUS_CMUL THEN
    REWRITE_TAC [← REWRITE_RULE [o_DEF] CONTINUOUS_AT_LIFT_NORM])

  let RCONE_GT_NEG ← prove
   r"!v0 v1:real^N a.
          rcone_gt v0 v1 (--a) =
           IMAGE (\x. &2 % v0 - x) ((:real^N) DIFF rcone_ge v0 v1 a)"
   (REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN REWRITE_TAC [] THEN CONJ_TAC THENL
     [MESON_TAC [← VECTOR_ARITH (← q r"a - (a - b):real^N = b")],
      REWRITE_TAC [rcone_gt, rconesgn, rcone_ge,
                  IN_ELIM_THM, IN_DIFF, IN_UNIV] THEN
      REWRITE_TAC [← NORM_ARITH (← q r"dist(&2 % x - y,x) = dist(y,x)")] THEN
      REWRITE_TAC [← VECTOR_ARITH (← q r"&2 % v - x - v:real^N = --(x - v)")] THEN
      REWRITE_TAC [DOT_LNEG] THEN REAL_ARITH_TAC])

  let VOLUME_FRUSTT_STRONG ← prove
   r"!v0 v1:real^3 h a.
         &0 < a
         ==> bounded(frustt v0 v1 h a) /\
             convex(frustt v0 v1 h a) /\
             measurable(frustt v0 v1 h a) /\
             measure(frustt v0 v1 h a) =
             if v1 = v0 \/ &1 <= a \/ h < &0 then &0
             else pi * ((h / a) pow 2 - h pow 2) * h / &3"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [frustt, frustum, rcone_gt, rconesgn, IN_ELIM_THM] THEN
    CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN GEOM_ORIGIN_TAC (← q r"v0:real^3") THEN
    REWRITE_TAC [VECTOR_SUB_RZERO, REAL_MUL_LZERO, DIST_0, real_gt] THEN
    GEOM_BASIS_MULTIPLE_TAC 1 (← q r"v1:real^3") THEN
    X_GEN_TAC (← q r"b:real") THEN REPEAT (GEN_TAC ORELSE DISCH_TAC) THEN
    FIRST_ASSUM (DISJ_CASES_TAC o MATCH_MP (← REAL_ARITH
     (← q r"&0 <= x ==> x = &0 \/ &0 < x"))) THEN
    ASM_REWRITE_TAC [DOT_RZERO, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_LT_REFL,
      MEASURABLE_EMPTY, MEASURE_EMPTY, EMPTY_GSPEC, VECTOR_MUL_LZERO,
      BOUNDED_EMPTY, CONVEX_EMPTY] THEN
    ASM_CASES_TAC (← q r"&1 <= a") THEN ASM_REWRITE_TAC [] THENL
     [SUBGOAL_THEN
       (← q r"!y:real^3. ~(norm(y) * norm(b % basis 1:real^3) * a
                     < y dot (b % basis 1))")
       (fun th => REWRITE_TAC [th, EMPTY_GSPEC, MEASURABLE_EMPTY,
         BOUNDED_EMPTY, CONVEX_EMPTY, MEASURE_EMPTY]) THEN
      REWRITE_TAC [REAL_NOT_LT] THEN X_GEN_TAC (← q r"y:real^3") THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"abs(x) <= a ==> x <= a")) THEN
      SIMP_TAC [DOT_RMUL, NORM_MUL, REAL_ABS_MUL, DOT_BASIS, NORM_BASIS,
               DIMINDEX_3, ARITH] THEN
      REWRITE_TAC [← REAL_ARITH
       (← q r"b * y <= n * (b * &1) * a <=> b * &1 * y <= b * a * n")] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC [REAL_POS, REAL_ABS_POS, COMPONENT_LE_NORM, DIMINDEX_3, ARITH],
      ALL_TAC] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [REAL_NOT_LE]) THEN
    SIMP_TAC [NORM_MUL, NORM_BASIS, DOT_BASIS, DOT_RMUL, DIMINDEX_3, ARITH] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"n * x * a:real = x * n * a")] THEN
    ASM_REWRITE_TAC [real_abs, REAL_MUL_RID] THEN
    ASM_SIMP_TAC [REAL_MUL_RID, REAL_LT_LMUL_EQ, REAL_LT_MUL_EQ, NORM_POS_LT] THEN
    ASM_SIMP_TAC [VECTOR_MUL_EQ_0, BASIS_NONZERO, DIMINDEX_3, ARITH,
                 REAL_LT_IMP_NZ] THEN
    ASM_SIMP_TAC [← GSYM REAL_LT_RDIV_EQ, NORM_LT_SQUARE] THEN
    ASM_SIMP_TAC [REAL_POW_DIV, REAL_POW_LT, REAL_LT_RDIV_EQ] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"(&0 * x < y /\ u < v) /\ &0 < y /\ y < h <=>
                            &0 < y /\ y < h /\ u < v")] THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ b /\ (a /\ b ==> c) ==> a /\ b /\ c")) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC (← q r"ball(vec 0:real^3,h / a)") THEN
      REWRITE_TAC [BOUNDED_BALL, IN_BALL_0, SUBSET, IN_ELIM_THM] THEN
      REWRITE_TAC [NORM_LT_SQUARE] THEN
      ASM_SIMP_TAC [REAL_POW_DIV, REAL_LT_RDIV_EQ, REAL_POW_LT] THEN
      X_GEN_TAC (← q r"x:real^3") THEN STRIP_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
          (← REWRITE_RULE [IMP_CONJ] REAL_LTE_TRANS)) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC,
      REWRITE_TAC [← SET_RULE (← q r"{x | P x /\ Q x /\ R x} =
                            {x | Q x} INTER {x | P x /\ R x}")] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"&0 < y <=> y > &0")] THEN
      MATCH_MP_TAC CONVEX_INTER THEN
      REWRITE_TAC [CONVEX_HALFSPACE_COMPONENT_LT] THEN
      MP_TAC (← ISPECL [← q r"vec 0:real^3", ← q r"basis 1:real^3", ← q r"a:real"]
          CONVEX_RCONE_GT) THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE, rcone_gt, rconesgn] THEN
      REWRITE_TAC [VECTOR_SUB_RZERO, DIST_0] THEN
      SIMP_TAC [DOT_BASIS, NORM_BASIS, DIMINDEX_3, ARITH] THEN
      REWRITE_TAC [real_gt, REAL_MUL_LID] THEN
      ASM_SIMP_TAC [← GSYM REAL_LT_RDIV_EQ] THEN
      REWRITE_TAC [NORM_LT_SQUARE] THEN
      ASM_SIMP_TAC [REAL_POW_DIV, REAL_LT_RDIV_EQ, REAL_POW_LT] THEN
      REWRITE_TAC [REAL_MUL_LZERO],
      ALL_TAC] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC (← HolLight.INST_TYPE [(← qty "2", ← qty "M")] FUBINI_SIMPLE_CONVEX_STRONG) THEN
    EXISTS_TAC (← q r"1") THEN REWRITE_TAC [DIMINDEX_2, DIMINDEX_3, ARITH] THEN
    ASM_REWRITE_TAC [] THEN
    SIMP_TAC [SLICE_312, DIMINDEX_2, DIMINDEX_3, ARITH, IN_ELIM_THM,
             VECTOR_3, DOT_3, ← GSYM DOT_2] THEN
    SUBGOAL_THEN (← q r"&0 < inv(a pow 2) - &1") ASSUME_TAC THENL
     [REWRITE_TAC [REAL_SUB_LT] THEN MATCH_MP_TAC REAL_INV_1_LT THEN
      ASM_SIMP_TAC [REAL_POW_1_LT, REAL_LT_IMP_LE, ARITH, REAL_POW_LT],
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
    EXISTS_TAC (← q r"\t. if &0 < t /\ t < h then pi * (inv(a pow 2) - &1) * t pow 2
                    else &0") THEN
    CONJ_TAC THENL
     [X_GEN_TAC (← q r"t:real") THEN DISCH_TAC THEN REWRITE_TAC [] THEN
      COND_CASES_TAC THEN
      ASM_REWRITE_TAC [EMPTY_GSPEC, CONJ_ASSOC,
                      MEASURE_EMPTY, MEASURABLE_EMPTY] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC (← q r"measure(ball(vec 0:real^2,sqrt(inv(a pow 2) - &1) * t))") THEN
      CONJ_TAC THENL
       [W (MP_TAC o PART_MATCH (lhs o rand) AREA_BALL o rand o snd) THEN
        ASM_SIMP_TAC [REAL_LT_IMP_LE, SQRT_POS_LT, REAL_LT_MUL] THEN
        ASM_SIMP_TAC [SQRT_POW_2, REAL_LT_IMP_LE, REAL_POW_MUL],
        AP_TERM_TAC THEN REWRITE_TAC [IN_BALL_0, EXTENSION, IN_ELIM_THM] THEN
        REWRITE_TAC [NORM_LT_SQUARE] THEN
        ASM_SIMP_TAC [SQRT_POS_LT, SQRT_POW_2, REAL_LT_IMP_LE, REAL_LT_MUL,
                     REAL_POW_MUL, ← GSYM REAL_LT_RDIV_EQ, REAL_POW_LT] THEN
        REAL_ARITH_TAC],
      ALL_TAC] THEN
    REWRITE_TAC [← GSYM IN_REAL_INTERVAL, HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
    REWRITE_TAC [HAS_REAL_INTEGRAL_OPEN_INTERVAL] THEN
    COND_CASES_TAC THENL
     [ASM_MESON_TAC [REAL_INTERVAL_EQ_EMPTY, HAS_REAL_INTEGRAL_EMPTY],
      RULE_ASSUM_TAC (REWRITE_RULE [REAL_NOT_LT])] THEN
    MP_TAC (← ISPECL
     [← q r"\t. pi / &3 * (inv (a pow 2) - &1) * t pow 3",
      ← q r"\t. pi * (inv (a pow 2) - &1) * t pow 2",
      ← q r"&0", ← q r"h:real"] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING,
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC (← q r"&0 < a") THEN CONV_TAC REAL_FIELD])

  let VOLUME_FRUSTT ← prove
   r"!v0 v1:real^3 h a.
         &0 < a
         ==> measurable(frustt v0 v1 h a) /\
             measure(frustt v0 v1 h a) =
             if v1 = v0 \/ &1 <= a \/ h < &0 then &0
             else pi * ((h / a) pow 2 - h pow 2) * h / &3"
   (SIMP_TAC [VOLUME_FRUSTT_STRONG])

  pure { delta_x, VOLUME_OF_CLOSED_TETRAHEDRON, VOLUME_OF_TETRAHEDRON, AREA_UNIT_CBALL,
         AREA_CBALL, AREA_BALL, VOLUME_CBALL, VOLUME_BALL, rconesgn, rcone_gt, rcone_ge,
         rcone_eq, frustum, frustt, FRUSTUM_DEGENERATE, CONVEX_RCONE_GT, OPEN_RCONE_GT,
         RCONE_GT_NEG, VOLUME_FRUSTT_STRONG, VOLUME_FRUSTT }
/- ------------------------------------------------------------------------- -/
/- Ellipsoid; conic cap.                                                     -/
/- (flyspeck.ml 4778-5065)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FYQ where
  scale : thm
  normball : thm
  ellipsoid : thm
  NORMBALL_BALL : thm
  MEASURE_SCALE : thm
  MEASURE_ELLIPSOID : thm
  MEASURABLE_ELLIPSOID : thm
  conic_cap : thm
  CONIC_CAP_DEGENERATE : thm
  BOUNDED_CONIC_CAP : thm
  MEASURABLE_CONIC_CAP : thm
  VOLUME_CONIC_CAP_STRONG : thm
  VOLUME_CONIC_CAP : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYQ [HolBase] (D : FlyspeckDeps) (BFYA : FYA) (BFYP : FYP) : ExceptT String IO FYQ := do
  -- @@SCOPE BEGIN
  let { SLICE_312, .. } := BFYA
  let { AREA_BALL, CONVEX_RCONE_GT, OPEN_RCONE_GT, rcone_gt, rconesgn, VOLUME_BALL,
        .. } := BFYP
  let { let_CONV, .. } := D
  let { MESON_TAC, new_definition, REAL_RING, .. } := D.crd
  let { NORM_LT_SQUARE_ALT, .. } := D.qvectors
  let { HAS_MEASURE_MEASURE, HAS_MEASURE_STRETCH, MEASURABLE_BALL, MEASURE_UNIQUE,
        .. } := D.qmeasure
  let { ball, .. } := D.qtopology
  let { GEOM_ORIGIN_TAC, .. } := D.geomorigin
  let { REAL_DIFF_TAC, .. } := D.gm.rzq
  let { HAS_REAL_INTEGRAL_EQ, .. } := D.gm.rzal
  let { HAS_REAL_INTEGRAL_COMBINE, REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS, .. } := D.gm.rzan
  let { HAS_REAL_INTEGRAL_RESTRICT_UNIV, .. } := D.gm.rzao
  let { HAS_REAL_INTEGRAL_OPEN_INTERVAL, .. } := D.gm.rzap
  let { FUBINI_SIMPLE_CONVEX_STRONG, .. } := D.gm.rzbc
  let { DOT_3, .. } := D.gm.qvectors
  let { ARITH, CART_EQ, DIMINDEX_3, DOT_RZERO, FORALL_3, LAMBDA_BETA, NORM_POS_LE,
        NORM_POW_2, real_abs, REAL_LE_MUL, REAL_MUL_LZERO, REAL_POW_MUL, VECTOR_3,
        .. } := D.crd.thms
  let { IN_REAL_INTERVAL, .. } := D.gm.ra.qmisc
  let { measurable, MEASURABLE_EMPTY, MEASURABLE_OPEN, MEASURE_EMPTY,
        .. } := D.gm.ra.qmeasure
  let { REAL_POW_1_LT, .. } := D.gm.ra.ts.cn.qsession
  let { PRODUCT_3, .. } := D.gm.ra.ts.cn.ms.qdet
  let { ASM_REAL_ARITH_TAC, GEOM_BASIS_MULTIPLE_TAC, NORM_ARITH, NUM_REDUCE_CONV,
        REAL_ARITH, REAL_FIELD, SET_RULE, SET_TAC, .. } := D.gm.ra.ts.cn.cx.cvx
  let { REAL_LE_SQUARE, SQRT_POS_LT, .. } := D.gm.ra.ts.cn.cx.cpx
  let { DIMINDEX_2, EMPTY_GSPEC, EQ_IMP, EXTENSION, .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { FUN_EQ_THM, IMAGE, IMAGE_ID, INTER, INTER_EMPTY, .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, REAL_ABS_MUL, REAL_ABS_POS, .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_INV_1_LT, REAL_LE_LDIV_EQ, REAL_LE_LMUL, REAL_LE_MUL2, REAL_LE_RDIV_EQ,
        REAL_LE_SQUARE_ABS, REAL_LE_TRANS, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_LMUL_EQ,
        REAL_LT_MUL_EQ, REAL_LT_RDIV_EQ, REAL_LT_REFL, .. } := D.gm.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_RID, REAL_MUL_RZERO, REAL_MUL_SYM, REAL_NOT_LE, REAL_NOT_LT,
        REAL_POS, REAL_POW_2, REAL_POW_DIV, REAL_POW_LE2, REAL_POW_LT, REAL_SUB_LE,
        REAL_SUB_LT, SIMPLE_IMAGE, SQRT_POS_LE, SQRT_POW_2, SUBSET,
        .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { real_div, real_gt, .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { BASIS_NONZERO, COMPONENT_LE_NORM, DIST_0, DIST_REFL, DIST_SYM, DOT_2, DOT_BASIS,
        DOT_RMUL, .. } := D.gm.ra.ts.cn.cx.cvx.vec1
  let { NORM_BASIS, .. } := D.gm.ra.ts.cn.cx.cvx.vec2
  let { NORM_MUL, NORM_POS_LT, REAL_ABS_NORM, .. } := D.gm.ra.ts.cn.cx.cvx.vec3
  let { VECTOR_MUL_EQ_0, VECTOR_MUL_LZERO, VECTOR_SUB_REFL, VECTOR_SUB_RZERO,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { BOUNDED_BALL, BOUNDED_EMPTY, BOUNDED_SUBSET, .. } := D.gm.ra.ts.cn.cx.cvx.top1
  let { IN_BALL_0, OPEN_BALL, .. } := D.gm.ra.ts.cn.cx.cvx.top4
  let { OPEN_INTER, .. } := D.gm.ra.ts.cn.cx.cvx.top5
  let { NORM_LT_SQUARE, .. } := D.gm.ra.ts.cn.ms.ig.dv.qvec
  let { CONVEX_BALL, CONVEX_EMPTY, CONVEX_INTER, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  -- @@SCOPE END

  let scale ← new_definition
   r"scale (t:real^3) (u:real^3):real^3 =
         vector[t$1 * u$1; t$2 * u$2; t$3 * u$3]"

  let normball ← new_definition r"normball x r = { y:real^A | dist(y,x) < r}"

  let ellipsoid ← new_definition
   r"ellipsoid t r = IMAGE (scale t) (normball(vec 0) r)"

  let NORMBALL_BALL ← prove
   r"!z r. normball z r = ball(z,r)"
   (REWRITE_TAC [normball, ball, DIST_SYM])

  let MEASURE_SCALE ← prove
   r"!s. measurable s
         ==> measurable(IMAGE (scale t) s) /\
             measure(IMAGE (scale t) s) = abs(t$1 * t$2 * t$3) * measure s"
   (GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [HAS_MEASURE_MEASURE] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"\i. (t:real^3)$i") o
      MATCH_MP HAS_MEASURE_STRETCH) THEN
    REWRITE_TAC [DIMINDEX_3, PRODUCT_3] THEN
    SUBGOAL_THEN (← q r"(\x:real^3. (lambda k. t$k * x$k):real^3) = scale t")
    SUBST1_TAC THENL
     [SIMP_TAC [CART_EQ, FUN_EQ_THM, scale, LAMBDA_BETA, DIMINDEX_3,
               VECTOR_3, ARITH, FORALL_3],
      MESON_TAC [measurable, MEASURE_UNIQUE]])

  let MEASURE_ELLIPSOID ← prove
   r"!t r. &0 <= r
           ==> measurable(ellipsoid t r) /\
               measure(ellipsoid t r) =
                  abs(t$1 * t$2 * t$3) * &4 / &3 * pi * r pow 3"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM o
      SPEC (← q r"vec 0:real^3") o MATCH_MP VOLUME_BALL) THEN
    REWRITE_TAC [normball, ellipsoid] THEN ONCE_REWRITE_TAC [DIST_SYM] THEN
    REWRITE_TAC [← GSYM ball] THEN MATCH_MP_TAC MEASURE_SCALE THEN
    REWRITE_TAC [MEASURABLE_BALL])

  let MEASURABLE_ELLIPSOID ← prove
   r"!t r. measurable(ellipsoid t r)"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"&0 <= r") THEN ASM_SIMP_TAC [MEASURE_ELLIPSOID] THEN
    REWRITE_TAC [ellipsoid, NORMBALL_BALL, IMAGE, IN_BALL_0] THEN
    ASM_SIMP_TAC [← NORM_ARITH (← q r"~(&0 <= r) ==> ~(norm(x:real^3) < r)")] THEN
    REWRITE_TAC [EMPTY_GSPEC, MEASURABLE_EMPTY])

  /- Conic cap. -/

  let conic_cap ← new_definition
   r"conic_cap v0 v1 r a = normball v0 r INTER rcone_gt v0 v1 a"

  let CONIC_CAP_DEGENERATE ← prove
   r"!v0 r a. conic_cap v0 v0 r a = {}"
   (REWRITE_TAC [conic_cap, rcone_gt, rconesgn, VECTOR_SUB_REFL] THEN
    REWRITE_TAC [DIST_REFL, DOT_RZERO, REAL_MUL_RZERO, REAL_MUL_LZERO] THEN
    REWRITE_TAC [real_gt, REAL_LT_REFL] THEN SET_TAC [])

  let BOUNDED_CONIC_CAP ← prove
   r"!v0 v1:real^3 r a. bounded(conic_cap v0 v1 r a)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [conic_cap, NORMBALL_BALL] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC (← q r"ball(v0:real^3,r)") THEN
    REWRITE_TAC [BOUNDED_BALL] THEN SET_TAC [])

  let MEASURABLE_CONIC_CAP ← prove
   r"!v0 v1:real^3 r a. measurable(conic_cap v0 v1 r a)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [conic_cap, NORMBALL_BALL] THEN
    MATCH_MP_TAC MEASURABLE_OPEN THEN
    SIMP_TAC [OPEN_INTER, OPEN_RCONE_GT, OPEN_BALL] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC (← q r"ball(v0:real^3,r)") THEN
    REWRITE_TAC [BOUNDED_BALL] THEN SET_TAC [])

  let VOLUME_CONIC_CAP_STRONG ← prove
   r"!v0 v1:real^3 r a.
         &0 < a
         ==> bounded(conic_cap v0 v1 r a) /\
             convex(conic_cap v0 v1 r a) /\
             measurable(conic_cap v0 v1 r a) /\
             measure(conic_cap v0 v1 r a) =
               if v1 = v0 \/ &1 <= a \/ r < &0 then &0
               else &2 / &3 * pi * (&1 - a) * r pow 3"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [conic_cap, rcone_gt, rconesgn, IN_ELIM_THM] THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [DIST_SYM] normball, ← GSYM ball] THEN
    CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN GEOM_ORIGIN_TAC (← q r"v0:real^3") THEN
    REWRITE_TAC [VECTOR_SUB_RZERO, REAL_MUL_LZERO, DIST_0, real_gt] THEN
    GEOM_BASIS_MULTIPLE_TAC 1 (← q r"v1:real^3") THEN
    X_GEN_TAC (← q r"b:real") THEN REPEAT (GEN_TAC ORELSE DISCH_TAC) THEN
    FIRST_ASSUM (DISJ_CASES_TAC o MATCH_MP (← REAL_ARITH
     (← q r"&0 <= x ==> x = &0 \/ &0 < x")))
    THENL
     [ASM_REWRITE_TAC [VECTOR_MUL_LZERO, ← GSYM REAL_NOT_LE, DOT_RZERO] THEN
      ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_IMP_LE, NORM_POS_LE] THEN
      REWRITE_TAC [EMPTY_GSPEC, INTER_EMPTY, MEASURE_EMPTY, MEASURABLE_EMPTY,
                  CONVEX_EMPTY, BOUNDED_EMPTY],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"&1 <= a") THEN ASM_REWRITE_TAC [] THENL
     [SUBGOAL_THEN
       (← q r"!y:real^3. ~(norm(y) * norm(b % basis 1:real^3) * a
                     < y dot (b % basis 1))")
       (fun th => REWRITE_TAC [th, EMPTY_GSPEC, INTER_EMPTY, MEASURE_EMPTY,
                           MEASURABLE_EMPTY, BOUNDED_EMPTY, CONVEX_EMPTY]) THEN
      REWRITE_TAC [REAL_NOT_LT] THEN X_GEN_TAC (← q r"y:real^3") THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"abs(x) <= a ==> x <= a")) THEN
      SIMP_TAC [DOT_RMUL, NORM_MUL, REAL_ABS_MUL, DOT_BASIS, NORM_BASIS,
               DIMINDEX_3, ARITH] THEN
      REWRITE_TAC [← REAL_ARITH
       (← q r"b * y <= n * (b * &1) * a <=> b * &1 * y <= b * a * n")] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC [REAL_POS, REAL_ABS_POS, COMPONENT_LE_NORM, DIMINDEX_3, ARITH],
      ALL_TAC] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [REAL_NOT_LE]) THEN
    SIMP_TAC [DOT_RMUL, NORM_MUL, REAL_ABS_NORM, DOT_BASIS,
             DIMINDEX_3, ARITH, NORM_BASIS] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"n * x * a:real = x * n * a")] THEN
    ASM_REWRITE_TAC [real_abs, REAL_MUL_RID] THEN
    ASM_SIMP_TAC [REAL_MUL_RID, REAL_LT_LMUL_EQ, REAL_LT_MUL_EQ, NORM_POS_LT] THEN
    ASM_SIMP_TAC [← GSYM REAL_LT_RDIV_EQ, NORM_LT_SQUARE] THEN
    ASM_SIMP_TAC [REAL_POW_DIV, REAL_POW_LT, REAL_LT_RDIV_EQ] THEN
    REWRITE_TAC [INTER, REAL_MUL_LZERO, IN_BALL_0, IN_ELIM_THM] THEN
    ASM_SIMP_TAC [VECTOR_MUL_EQ_0, BASIS_NONZERO, DIMINDEX_3, ARITH,
                 REAL_LT_IMP_NZ] THEN
    COND_CASES_TAC THENL
     [ASM_SIMP_TAC [← NORM_ARITH (← q r"r < &0 ==> ~(norm x < r)")] THEN
      REWRITE_TAC [EMPTY_GSPEC, MEASURE_EMPTY, MEASURABLE_EMPTY,
                  BOUNDED_EMPTY, CONVEX_EMPTY],
      RULE_ASSUM_TAC (ONCE_REWRITE_RULE [REAL_NOT_LT])] THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ b /\ (a /\ b ==> c /\ d) ==> a /\ b /\ c /\ d")) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC (← q r"ball(vec 0:real^3,r)") THEN
      SIMP_TAC [BOUNDED_BALL, IN_BALL_0, SUBSET, IN_ELIM_THM],
      ONCE_REWRITE_TAC [← SET_RULE
        (← q r"{x | P x /\ Q x} = {x | P x} INTER {x | Q x}")] THEN
      MATCH_MP_TAC CONVEX_INTER THEN
      REWRITE_TAC [← GSYM IN_BALL_0, CONVEX_BALL, SIMPLE_IMAGE, IMAGE_ID] THEN
      MP_TAC (← ISPECL [← q r"vec 0:real^3", ← q r"basis 1:real^3", ← q r"a:real"]
          CONVEX_RCONE_GT) THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE, rcone_gt, rconesgn] THEN
      REWRITE_TAC [VECTOR_SUB_RZERO, DIST_0] THEN
      SIMP_TAC [DOT_BASIS, NORM_BASIS, DIMINDEX_3, ARITH] THEN
      REWRITE_TAC [real_gt, REAL_MUL_LID] THEN
      ASM_SIMP_TAC [← GSYM REAL_LT_RDIV_EQ] THEN
      REWRITE_TAC [NORM_LT_SQUARE] THEN
      ASM_SIMP_TAC [REAL_POW_DIV, REAL_LT_RDIV_EQ, REAL_POW_LT] THEN
      REWRITE_TAC [REAL_MUL_LZERO],
      STRIP_TAC] THEN
    MATCH_MP_TAC (← HolLight.INST_TYPE [(← qty "2", ← qty "M")] FUBINI_SIMPLE_CONVEX_STRONG) THEN
    EXISTS_TAC (← q r"1") THEN ASM_REWRITE_TAC [DIMINDEX_2, DIMINDEX_3, ARITH] THEN
    SIMP_TAC [SLICE_312, DIMINDEX_2, DIMINDEX_3, ARITH, IN_ELIM_THM,
             VECTOR_3, DOT_3, ← GSYM DOT_2] THEN
    SUBGOAL_THEN (← q r"&0 < inv(a pow 2) - &1") ASSUME_TAC THENL
     [REWRITE_TAC [REAL_SUB_LT] THEN MATCH_MP_TAC REAL_INV_1_LT THEN
      ASM_SIMP_TAC [REAL_POW_1_LT, REAL_LT_IMP_LE, ARITH, REAL_POW_LT],
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
    EXISTS_TAC (← q r"\t. if &0 < t /\ t < r
                    then measure
                      {y:real^2 | norm(vector[t; y$1; y$2]:real^3) pow 2
                                   < r pow 2 /\
                                  (t * t + y dot y) * a pow 2 < t pow 2}
                    else &0") THEN
    CONJ_TAC THENL
     [X_GEN_TAC (← q r"t:real") THEN DISCH_TAC THEN REWRITE_TAC [] THEN
      ASM_CASES_TAC (← q r"&0 < t") THEN
      ASM_REWRITE_TAC [EMPTY_GSPEC, MEASURE_EMPTY, MEASURABLE_EMPTY] THEN
      ASM_CASES_TAC (← q r"t:real < r") THEN ASM_REWRITE_TAC [] THENL
       [REWRITE_TAC [NORM_LT_SQUARE] THEN
        SUBGOAL_THEN (← q r"&0 < r") (fun th => REWRITE_TAC [th, NORM_POW_2]) THEN
        ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"!y. ~(norm(vector[t; (y:real^2)$1; y$2]:real^3) < r)")
       (fun th => REWRITE_TAC [th, EMPTY_GSPEC, MEASURE_EMPTY,
                              MEASURABLE_EMPTY]) THEN
      ASM_REWRITE_TAC [NORM_LT_SQUARE, DOT_3, VECTOR_3] THEN
      GEN_TAC THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"&0 <= a /\ &0 <= b /\ c <= d
                               ==> ~(&0 < r /\ d + a + b < c)")) THEN
      REWRITE_TAC [REAL_LE_SQUARE] THEN
      REWRITE_TAC [REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [← GSYM IN_REAL_INTERVAL, HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
    REWRITE_TAC [HAS_REAL_INTEGRAL_OPEN_INTERVAL] THEN
    REWRITE_TAC [NORM_POW_2, DOT_3, VECTOR_3, DOT_2] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH
     (← q r"pi * &2 / &3 * (&1 - a) * r pow 3 =
      pi / &3 * (inv (a pow 2) - &1) * (a * r) pow 3 +
      (pi * &2 / &3 * (&1 - a) * r pow 3 -
       pi / &3 * (inv (a pow 2) - &1) * (a * r) pow 3)")] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_COMBINE THEN
    EXISTS_TAC (← q r"a * r:real") THEN
    REWRITE_TAC [← REAL_ARITH (← q r"a * r <= r <=> &0 <= r * (&1 - a)")] THEN
    ASM_SIMP_TAC [REAL_LE_MUL, REAL_SUB_LE, REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN EXISTS_TAC
       (← q r"\t. measure(ball(vec 0:real^2,sqrt(inv(a pow 2) - &1) * t))") THEN
      CONJ_TAC THENL
       [X_GEN_TAC (← q r"t:real") THEN REWRITE_TAC [IN_REAL_INTERVAL] THEN
        STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
        REWRITE_TAC [IN_BALL_0, NORM_LT_SQUARE_ALT] THEN
        ASM_SIMP_TAC [SQRT_POS_LE, REAL_LE_MUL, SQRT_POW_2, REAL_LT_IMP_LE,
                     REAL_POW_MUL] THEN
        REWRITE_TAC [← REAL_ARITH (← q r"x < (a - &1) * t <=> t + x < t * a")] THEN
        ASM_SIMP_TAC [← GSYM real_div, REAL_LT_RDIV_EQ, REAL_POW_LT] THEN
        X_GEN_TAC (← q r"x:real^2") THEN REWRITE_TAC [DOT_2] THEN
        ASM_SIMP_TAC [← GSYM REAL_POW_2, ← GSYM REAL_LT_RDIV_EQ, REAL_POW_LT] THEN
        MATCH_MP_TAC (← REAL_ARITH (← q r"b <= a ==> (x < b <=> x < a /\ x < b)")) THEN
        ASM_SIMP_TAC [REAL_LE_LDIV_EQ, REAL_POW_LT, ← GSYM REAL_POW_MUL] THEN
        ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
        REWRITE_TAC [← GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
      EXISTS_TAC (← q r"\t. pi * (inv(a pow 2) - &1) * t pow 2") THEN
      CONJ_TAC THENL
       [X_GEN_TAC (← q r"t:real") THEN REWRITE_TAC [IN_REAL_INTERVAL] THEN
        STRIP_TAC THEN
        W (MP_TAC o PART_MATCH (lhs o rand) AREA_BALL o rand o snd) THEN
        ASM_SIMP_TAC [REAL_POW_MUL, REAL_LT_IMP_LE, SQRT_POS_LT, REAL_LE_MUL,
                     SQRT_POW_2],
        ALL_TAC] THEN
      MP_TAC (← ISPECL
       [← q r"\t. pi / &3 * (inv (a pow 2) - &1) * t pow 3",
        ← q r"\t. pi * (inv (a pow 2) - &1) * t pow 2",
        ← q r"&0", ← q r"a * r:real"] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
      ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_IMP_LE] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN
        REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
        CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING,
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        UNDISCH_TAC (← q r"&0 < a") THEN CONV_TAC REAL_FIELD],
      MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN EXISTS_TAC
       (← q r"\t. measure(ball(vec 0:real^2,sqrt(r pow 2 - t pow 2)))") THEN
      CONJ_TAC THENL
       [X_GEN_TAC (← q r"t:real") THEN REWRITE_TAC [IN_REAL_INTERVAL] THEN
        STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
        REWRITE_TAC [IN_BALL_0, NORM_LT_SQUARE_ALT] THEN
        SUBGOAL_THEN (← q r"&0 <= t") ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"a * r:real") THEN
          ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_IMP_LE],
          ALL_TAC] THEN
        ASM_SIMP_TAC [SQRT_POS_LE, SQRT_POW_2, REAL_SUB_LE, REAL_POW_LE2] THEN
        X_GEN_TAC (← q r"x:real^2") THEN REWRITE_TAC [DOT_2] THEN
        REWRITE_TAC [← REAL_ARITH (← q r"x < r - t <=> t + x < r")] THEN
        ASM_SIMP_TAC [← GSYM REAL_POW_2, ← GSYM REAL_LT_RDIV_EQ, REAL_POW_LT] THEN
        MATCH_MP_TAC (← REAL_ARITH (← q r"a <= b ==> (x < a <=> x < a /\ x < b)")) THEN
        ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_POW_LT, ← GSYM REAL_POW_MUL] THEN
        ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
        ASM_SIMP_TAC [REAL_POW_LE2, REAL_LE_MUL, REAL_LT_IMP_LE],
        ALL_TAC] THEN
      MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
      EXISTS_TAC (← q r"\t. pi * (r pow 2 - t pow 2)") THEN
      CONJ_TAC THENL
       [X_GEN_TAC (← q r"t:real") THEN REWRITE_TAC [IN_REAL_INTERVAL] THEN
        STRIP_TAC THEN
        W (MP_TAC o PART_MATCH (lhs o rand) AREA_BALL o rand o snd) THEN
        SUBGOAL_THEN (← q r"&0 <= t") ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"a * r:real") THEN
          ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_IMP_LE],
          ALL_TAC] THEN
        ASM_SIMP_TAC [SQRT_POS_LE, SQRT_POW_2, REAL_SUB_LE, REAL_POW_LE2],
        ALL_TAC] THEN
      MP_TAC (← ISPECL
       [← q r"\t. pi * (r pow 2 * t - t pow 3 / &3)",
        ← q r"\t. pi * (r pow 2 - t pow 2)",
        ← q r"a * r:real", ← q r"r:real"] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
      ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_IMP_LE] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC [← REAL_ARITH (← q r"a * r <= r <=> &0 <= r * (&1 - a)")] THEN
        ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_IMP_LE, REAL_SUB_LE] THEN
        REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
        CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING,
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        UNDISCH_TAC (← q r"&0 < a") THEN CONV_TAC REAL_FIELD]])

  let VOLUME_CONIC_CAP ← prove
   r"!v0 v1:real^3 r a.
         &0 < a
         ==> measurable(conic_cap v0 v1 r a) /\ measure(conic_cap v0 v1 r a) =
             if v1 = v0 \/ &1 <= a \/ r < &0 then &0
             else &2 / &3 * pi * (&1 - a) * r pow 3"
   (SIMP_TAC [VOLUME_CONIC_CAP_STRONG])

  pure { scale, normball, ellipsoid, NORMBALL_BALL, MEASURE_SCALE, MEASURE_ELLIPSOID,
         MEASURABLE_ELLIPSOID, conic_cap, CONIC_CAP_DEGENERATE, BOUNDED_CONIC_CAP,
         MEASURABLE_CONIC_CAP, VOLUME_CONIC_CAP_STRONG, VOLUME_CONIC_CAP }
/- ------------------------------------------------------------------------- -/
/- Negligibility of a circular cone; area of sector of a circle delimited   -/
/- by Arg values.                                                            -/
/- (flyspeck.ml 5066-5441)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FYR where
  NEGLIGIBLE_CIRCULAR_CONE_0_NONPARALLEL : thm
  NEGLIGIBLE_CIRCULAR_CONE_0 : thm
  NEGLIGIBLE_CIRCULAR_CONE : thm
  NEGLIGIBLE_RCONE_EQ : thm
  NEGLIGIBLE_ARG_EQ : thm
  MEASURABLE_CLOSED_SECTOR_LE : thm
  MEASURABLE_CLOSED_SECTOR_LT : thm
  MEASURABLE_CLOSED_SECTOR_LTE : thm
  MEASURE_CLOSED_SECTOR_LE : thm
  HAS_MEASURE_OPEN_SECTOR_LT : thm
  MEASURE_OPEN_SECTOR_LT : thm
  HAS_MEASURE_OPEN_SECTOR_LT_GEN : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYR [HolBase] (D : FlyspeckDeps) (BFYP : FYP) : ExceptT String IO FYR := do
  -- @@SCOPE BEGIN
  let { AREA_CBALL, rcone_eq, rconesgn, .. } := BFYP
  let { ORTHOGONAL_VECTOR_ANGLE, vector_angle, VECTOR_ANGLE_REFL, VECTOR_ANGLE_RMUL,
        VECTOR_ANGLE_SYM, .. } := D.gea
  let { CONTINUOUS_ON_CX_VECTOR_ANGLE, VECTOR_ANGLE_EQ_0_LEFT, VECTOR_ANGLE_EQ_0_RIGHT,
        VECTOR_ANGLE_EQ_PI_LEFT, VECTOR_ANGLE_EQ_PI_RIGHT, .. } := D.geb
  let { angle, .. } := D.gec
  let { CONGRUENT_TRIANGLES_ASA_FULL, .. } := D.gee
  let { ASM_MESON_TAC, MESON_TAC, REAL_ARITH_TAC, .. } := D.crd
  let { BASIS_EQ_0, .. } := D.qvectors
  let { HAS_MEASURE_EMPTY, MEASURABLE_NEGLIGIBLE_SYMDIFF, MEASURE_NEGLIGIBLE_SYMDIFF,
        MEASURE_ORTHOGONAL_IMAGE_EQ, MEASURE_UNION, NEGLIGIBLE_HYPERPLANE,
        NEGLIGIBLE_SPHERE, NEGLIGIBLE_TRANSLATION_REV, STARLIKE_NEGLIGIBLE_STRONG,
        .. } := D.qmeasure
  let { ORTHOGONAL_TRANSFORMATION_SURJECTIVE, .. } := D.qdeterminants
  let { CONTINUOUS_CLOSED_PREIMAGE_CONSTANT, .. } := D.qtopology
  let { GEOM_ORIGIN_TAC, .. } := D.geomorigin
  let { REALLIM_NULL_COMPARISON, .. } := D.gm.rzb
  let { EVENTUALLY_WITHINREAL, REALLIM_ATREAL_WITHINREAL, .. } := D.gm.rzf
  let { REAL_CONTINUOUS_ATREAL, REAL_CONTINUOUS_LMUL, .. } := D.gm.rzh
  let { REAL_CONTINUOUS_AT_SIN, .. } := D.gm.rzp
  let { REAL_CONTINUOUS_ADDITIVE_IMP_LINEAR_INTERVAL, .. } := D.gm.rzbe
  let { NORM_CAUCHY_SCHWARZ_DIV, .. } := D.gm.qvectors
  let { ARITH, DIMINDEX_3, MONO_FORALL, NORM_EQ_0, NORM_POS_LE, o_DEF, real_abs,
        REAL_ENTIRE, REAL_LE_MUL, REAL_SUB_0, REAL_SUB_RZERO, VECTOR_MUL_LID,
        .. } := D.crd.thms
  let { CEXP_NZ, .. } := D.gm.ra.tsa
  let { CEXP_EULER, .. } := D.gm.ra.tsb
  let { COS_ADD, COS_BOUND, CX_COS, CX_SIN, SIN_0, SIN_ADD, .. } := D.gm.ra.tsc
  let { COS_PI2, COS_POS_PI_LE, PI_POS, SIN_PI2, SIN_POS_PI_LE, .. } := D.gm.ra.tse
  let { ARG, Arg_DEF, ARG_DIV_CX, .. } := D.gm.ra.tsh
  let { ARG_ROTATE2D, NORM_ROTATE2D, ORTHOGONAL_TRANSFORMATION_ROTATE2D, ROTATE2D_0,
        ROTATE2D_ADD, ROTATE2D_EQ_0, ROTATE2D_ZERO, .. } := D.gm.ra.tsi
  let { SIN_MONO_LE, .. } := D.gm.ra.tsl
  let { ACS_INJ, .. } := D.gm.ra.tsw
  let { CLOSED_ARG_LE, .. } := D.gm.ra.tsz
  let { HAS_MEASURE_0, HAS_MEASURE_MEASURABLE_MEASURE, HAS_MEASURE_NEGLIGIBLE_SYMDIFF,
        MEASURABLE_COMPACT, MEASURABLE_DIFF, MEASURABLE_INTERVAL, MEASURE_EMPTY,
        MEASURE_INTERVAL, MEASURE_POS_LE, MEASURE_SUBSET, .. } := D.gm.ra.qmeasure
  let { sphere, .. } := D.gm.ra.ts.qtopology
  let { IM, IM_DEF, RE, RE_DEF, .. } := D.gm.ra.ts.cn.cxa
  let { COMPLEX_MUL_RID, .. } := D.gm.ra.ts.cn.cxb
  let { COMPLEX_CMUL, COMPLEX_VEC_0, CX_INJ, IM_ADD, IM_CX, IM_MUL_CX, IM_MUL_II, RE_ADD,
        RE_CX, RE_MUL_CX, RE_MUL_II, .. } := D.gm.ra.ts.cn.cxc
  let { COMPLEX_BASIS, .. } := D.gm.ra.ts.cn.cxh
  let { PRODUCT_2, .. } := D.gm.ra.ts.cn.ms.qdet
  let { CONTENT_CLOSED_INTERVAL_CASES, .. } := D.gm.ra.ts.cn.ms.qintegration1
  let { NEGLIGIBLE_COUNTABLE_UNIONS, NEGLIGIBLE_INSERT, NEGLIGIBLE_SING, NEGLIGIBLE_SUBSET,
        NEGLIGIBLE_UNION_EQ, .. } := D.gm.ra.ts.cn.ms.qintegration3
  let { CLOSED_DIFF, .. } := D.gm.ra.ts.cn.ms.qtopology1
  let { ARITH_RULE, ASM_REAL_ARITH_TAC, GEOM_BASIS_MULTIPLE_TAC, MESON, NORM_ARITH,
        REAL_ARITH, REAL_FIELD, SET_RULE, VECTOR_ARITH, .. } := D.gm.ra.ts.cn.cx.cvx
  let { FORALL_2, .. } := D.gm.ra.ts.cn.cx.cpx
  let { DE_MORGAN_THM, DIMINDEX_2, EMPTY_GSPEC, EQ_TRANS, ETA_AX,
        .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, IMP_CONJ_ALT, IN_DIFF, .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, IN_NUMSEG, IN_UNION, IN_UNIONS, IN_UNIV,
        LEFT_AND_EXISTS_THM, MONO_EXISTS, REAL_ABS_MUL, REAL_ABS_POS, REAL_ADD_LID,
        REAL_ADD_LINV, REAL_ADD_RID, REAL_ARCH_INV, .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_LE_INV2, REAL_LE_LT, REAL_LE_MUL2, REAL_LE_REFL, REAL_LE_TRANS, REAL_LT_DIV,
        REAL_LT_IMP_LE, REAL_LT_INV_EQ, REAL_LT_MUL, .. } := D.gm.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_ASSOC, REAL_MUL_LINV, REAL_MUL_RZERO, REAL_NEG_0, REAL_NOT_LE,
        REAL_NOT_LT, REAL_OF_NUM_LT, REAL_POW_2, SUBSET, .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { SURJECTIVE_IMAGE_EQ, SWAP_EXISTS_THM, UNWIND_THM2,
        .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { COLLINEAR_LEMMA, DIST_0, DOT_2, DOT_RMUL, .. } := D.gm.ra.ts.cn.cx.cvx.vec1
  let { DOT_SYM, IN_INTERVAL, NORM_0, NORM_CAUCHY_SCHWARZ_ABS,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec2
  let { NORM_MUL, NORM_POS_LT, ORTHOGONAL_BASIS_BASIS, REAL_ABS_NORM,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec3
  let { VEC_COMPONENT, VECTOR_ADD_LDISTRIB, VECTOR_ADD_RID, VECTOR_ADD_SUB,
        VECTOR_MUL_ASSOC, VECTOR_MUL_EQ_0, VECTOR_MUL_LZERO, VECTOR_SUB_RZERO,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { CLOSED_UNIV, .. } := D.gm.ra.ts.cn.cx.cvx.top1
  let { COMPACT_CBALL, COMPACT_INTER_CLOSED, .. } := D.gm.ra.ts.cn.cx.cvx.top2
  let { IN_BALL_0, OPEN_BALL, .. } := D.gm.ra.ts.cn.cx.cvx.top4
  let { cball, .. } := D.gm.ra.ts.cn.cx.cvx.top5
  let { REAL_EQ_ADD_LCANCEL, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.qsession
  -- @@SCOPE END

  /- Negligibility of a circular cone.  This isn't exactly using the
     Flyspeck definition of "cone" but we use it to get that later on.
     Could now simplify this using WLOG tactics. -/

  let NEGLIGIBLE_CIRCULAR_CONE_0_NONPARALLEL ← prove
   r"!c:real^N k. ~(c = vec 0) /\ ~(k = &0) /\ ~(k = pi)
                  ==> negligible {x | vector_angle c x = k}"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC (← q r"(vec 0:real^N) INSERT
                UNIONS { {x | x IN ((:real^N) DIFF ball(vec 0,inv(&n + &1))) /\
                              Cx(vector_angle c x) = Cx k} |
                         n IN (:num)  }") THEN
    CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [SUBSET, IN_INSERT, IN_UNIONS, IN_ELIM_THM, CX_INJ] THEN
      X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN REWRITE_TAC [IN_UNIV] THEN
      ASM_CASES_TAC (← q r"x:real^N = vec 0") THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [LEFT_AND_EXISTS_THM, IN_DIFF, IN_UNIV] THEN
      ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN REWRITE_TAC [UNWIND_THM2] THEN
      ASM_REWRITE_TAC [IN_ELIM_THM] THEN
      MP_TAC (← SPEC (← q r"norm(x:real^N)") REAL_ARCH_INV) THEN
      ASM_REWRITE_TAC [NORM_POS_LT, IN_BALL_0, REAL_NOT_LT, REAL_LT_INV_EQ] THEN
      MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"inv(&n)") THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC [NEGLIGIBLE_INSERT] THEN
    MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN X_GEN_TAC (← q r"n:num") THEN
    MATCH_MP_TAC STARLIKE_NEGLIGIBLE_STRONG THEN EXISTS_TAC (← q r"c:real^N") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_CONSTANT THEN
      SIMP_TAC [CLOSED_DIFF, CLOSED_UNIV, OPEN_BALL] THEN
      MATCH_MP_TAC (← REWRITE_RULE [o_DEF] CONTINUOUS_ON_CX_VECTOR_ANGLE) THEN
      REWRITE_TAC [IN_DIFF, IN_BALL_0, NORM_0, IN_UNIV] THEN
      REWRITE_TAC [REAL_LT_INV_EQ] THEN REAL_ARITH_TAC,
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real", ← q r"x:real^N"] THEN
    SIMP_TAC [IN_ELIM_THM, IN_UNIV, IN_DIFF, IN_BALL_0, REAL_NOT_LT, CX_INJ] THEN
    REWRITE_TAC [DE_MORGAN_THM] THEN ASM_CASES_TAC (← q r"(c + x:real^N) = vec 0") THENL
     [ASM_REWRITE_TAC [← GSYM REAL_NOT_LT, REAL_LT_INV_EQ, NORM_0] THEN
      REAL_ARITH_TAC,
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"c + a % x:real^N = vec 0") THENL
     [ASM_REWRITE_TAC [← GSYM REAL_NOT_LT, REAL_LT_INV_EQ, NORM_0] THEN
      REAL_ARITH_TAC,
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"x:real^N = vec 0") THENL
     [ASM_REWRITE_TAC [VECTOR_ADD_RID, VECTOR_ANGLE_REFL],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"a = &0") THENL
     [ASM_REWRITE_TAC [VECTOR_MUL_LZERO, VECTOR_ADD_RID, VECTOR_ANGLE_REFL],
      ALL_TAC] THEN
    REWRITE_TAC [← TAUT (← q r"~a \/ ~b <=> a ==> ~b")] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"vec 0:real^N", ← q r"c:real^N", ← q r"c + a % x:real^N",
                   ← q r"vec 0:real^N", ← q r"c:real^N", ← q r"c + x:real^N"]
                  CONGRUENT_TRIANGLES_ASA_FULL) THEN
    REWRITE_TAC [angle, VECTOR_ADD_SUB] THEN ASM_SIMP_TAC [VECTOR_SUB_RZERO] THEN
    REWRITE_TAC [← NORM_ARITH (← q r"dist(x,x + a) = norm(a)"), NORM_MUL] THEN
    REWRITE_TAC [← REAL_FIELD (← q r"a * x = x <=> a = &1 \/ x = &0")] THEN
    ASM_SIMP_TAC [← REAL_ARITH (← q r"&0 <= a /\ a < &1 ==> ~(abs a = &1)")] THEN
    ASM_REWRITE_TAC [NORM_EQ_0, VECTOR_ANGLE_RMUL, COLLINEAR_LEMMA] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:real") MP_TAC) THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"\x:real^N. inv(a) % x")) THEN
    ASM_SIMP_TAC [VECTOR_MUL_ASSOC, VECTOR_ADD_LDISTRIB,
                 VECTOR_MUL_LID, REAL_MUL_LINV] THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"a % c + x = b % c <=> x = (b - a) % c")] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [← VECTOR_ARITH (← q r"c + a % c = (a + &1) % c")]) THEN
    UNDISCH_TAC (← q r"vector_angle c ((inv a * u - inv a + &1) % c:real^N) = k") THEN
    RULE_ASSUM_TAC (REWRITE_RULE
     [VECTOR_ANGLE_RMUL, VECTOR_MUL_EQ_0, DE_MORGAN_THM]) THEN
    ASM_REWRITE_TAC [VECTOR_ANGLE_RMUL, VECTOR_ANGLE_REFL] THEN
    ASM_REAL_ARITH_TAC)

  let NEGLIGIBLE_CIRCULAR_CONE_0 ← prove
   r"!c:real^N k. 2 <= dimindex(:N) /\ ~(c = vec 0)
                  ==> negligible {x | vector_angle c x = k}"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"orthogonal (basis 1:real^N) (basis 2)") ASSUME_TAC THENL
     [ASM_SIMP_TAC [ORTHOGONAL_BASIS_BASIS, ARITH,
                   ← ARITH_RULE (← q r"2 <= d ==> 1 <= d")],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"k = &0 \/ k = pi") THENL
     [ALL_TAC, ASM_MESON_TAC [NEGLIGIBLE_CIRCULAR_CONE_0_NONPARALLEL]] THEN
    SUBGOAL_THEN
     (← q r"?b:real^N. ~(b = vec 0) /\
                 ~(vector_angle c b = &0) /\
                 ~(vector_angle c b = pi)")
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC (← MESON [] (← q r"!a b. P a \/ P b ==> ?x. P x")) THEN
      MAP_EVERY EXISTS_TAC [← q r"basis 1:real^N", ← q r"basis 2:real^N"] THEN
      REWRITE_TAC [BASIS_EQ_0] THEN
      ASM_SIMP_TAC [← ARITH_RULE (← q r"2 <= d ==> 1 <= d"), IN_NUMSEG, ARITH] THEN
      REWRITE_TAC [← GSYM DE_MORGAN_THM] THEN STRIP_TAC THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"basis 1:real^N") o
        MATCH_MP VECTOR_ANGLE_EQ_0_LEFT)) THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC (← q r"basis 1:real^N") o
        MATCH_MP VECTOR_ANGLE_EQ_PI_LEFT)) THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [VECTOR_ANGLE_REFL, BASIS_EQ_0] THEN
      ASM_SIMP_TAC [← ARITH_RULE (← q r"2 <= d ==> 1 <= d"), IN_NUMSEG, ARITH] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [ORTHOGONAL_VECTOR_ANGLE]) THEN
      REWRITE_TAC [VECTOR_ANGLE_SYM] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC,
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"k = &0 \/ k = pi") THENL
     [ALL_TAC, ASM_MESON_TAC [NEGLIGIBLE_CIRCULAR_CONE_0_NONPARALLEL]] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    FIRST_X_ASSUM (DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [EXISTS_TAC (← q r"{x:real^N | vector_angle b x = vector_angle c b}") THEN
      ASM_SIMP_TAC [NEGLIGIBLE_CIRCULAR_CONE_0_NONPARALLEL] THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
      MESON_TAC [VECTOR_ANGLE_EQ_0_RIGHT, VECTOR_ANGLE_SYM],
      EXISTS_TAC (← q r"{x:real^N | vector_angle b x = pi - vector_angle c b}") THEN
      ASM_SIMP_TAC [NEGLIGIBLE_CIRCULAR_CONE_0_NONPARALLEL,
                   REAL_SUB_0, ← REAL_ARITH (← q r"p - x = p <=> x = &0")] THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
      MESON_TAC [VECTOR_ANGLE_EQ_PI_RIGHT, VECTOR_ANGLE_SYM]])

  let NEGLIGIBLE_CIRCULAR_CONE ← prove
   r"!a:real^N c k.
        2 <= dimindex(:N) /\ ~(c = vec 0)
        ==> negligible(a INSERT {x | vector_angle c (x - a) = k})"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [NEGLIGIBLE_INSERT] THEN
    MATCH_MP_TAC NEGLIGIBLE_TRANSLATION_REV THEN EXISTS_TAC (← q r"--a:real^N") THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC (← q r"{x:real^N | vector_angle c x = k}") THEN
    ASM_SIMP_TAC [NEGLIGIBLE_CIRCULAR_CONE_0] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"--a + x:real^N = x - a")])

  let NEGLIGIBLE_RCONE_EQ ← prove
   r"!w z:real^3 h. ~(w = z) ==> negligible(rcone_eq z w h)"
   (REWRITE_TAC [rcone_eq, rconesgn] THEN GEOM_ORIGIN_TAC (← q r"z:real^3") THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [DIST_0, VECTOR_SUB_RZERO] THEN
    ASM_CASES_TAC (← q r"abs(h) <= &1") THENL
     [MP_TAC (← ISPECL [← q r"w:real^3", ← q r"acs h"] NEGLIGIBLE_CIRCULAR_CONE_0) THEN
      ASM_REWRITE_TAC [DIMINDEX_3, ARITH] THEN
      REWRITE_TAC [← GSYM HAS_MEASURE_0] THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT]
        HAS_MEASURE_NEGLIGIBLE_SYMDIFF) THEN
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC (← q r"{vec 0:real^3}") THEN
      REWRITE_TAC [NEGLIGIBLE_SING] THEN MATCH_MP_TAC (← SET_RULE
       (← q r"(!x. ~(x = a) ==> (x IN s <=> x IN t))
        ==> (s DIFF t) UNION (t DIFF s) SUBSET {a}")) THEN
      X_GEN_TAC (← q r"x:real^3") THEN DISCH_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN
      ASM_SIMP_TAC [vector_angle] THEN ASM_SIMP_TAC [NORM_EQ_0, ← REAL_FIELD
       (← q r"~(x = &0) /\ ~(w = &0) ==> (a = x * w * b <=> a / (w * x) = b)")] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [DOT_SYM] THEN
      MATCH_MP_TAC ACS_INJ THEN ASM_REWRITE_TAC [NORM_CAUCHY_SCHWARZ_DIV],
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC (← q r"{vec 0}:real^3->bool") THEN
      REWRITE_TAC [NEGLIGIBLE_SING] THEN
      REWRITE_TAC [← SET_RULE (← q r"{x | P x} SUBSET {a} <=> !x. ~(x = a) ==> ~P x")] THEN
      X_GEN_TAC (← q r"x:real^3") THEN REPEAT DISCH_TAC THEN
      MP_TAC (← ISPECL [← q r"x:real^3", ← q r"w:real^3"] NORM_CAUCHY_SCHWARZ_ABS) THEN
      ASM_REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_NORM, ← REAL_ARITH
       (← q r"~(x * w * h <= x * w) <=> &0 < x * w * (h - &1)")] THEN
      REPEAT (MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [NORM_POS_LT]) THEN
      ASM_REAL_ARITH_TAC])

  /- Area of sector of a circle delimited by Arg values. -/

  let NEGLIGIBLE_ARG_EQ ← prove
   r"!t. negligible {z | Arg z = t}"
   (GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC (← q r"{z | cexp(ii * Cx(pi / &2 + t)) dot z = &0}") THEN
    SIMP_TAC [NEGLIGIBLE_HYPERPLANE, COMPLEX_VEC_0, CEXP_NZ] THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"z:complex") THEN
    DISCH_TAC THEN MP_TAC (← SPEC (← q r"z:complex") ARG) THEN ASM_REWRITE_TAC [] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [← GSYM COMPLEX_CMUL, DOT_RMUL, REAL_ENTIRE] THEN
    DISJ2_TAC THEN REWRITE_TAC [CEXP_EULER] THEN
    REWRITE_TAC [DOT_2, ← GSYM RE_DEF, ← GSYM IM_DEF] THEN
    REWRITE_TAC [← GSYM CX_SIN, ← GSYM CX_COS, RE_ADD, IM_ADD,
                RE_MUL_II, IM_MUL_II, RE_CX, IM_CX] THEN
    REWRITE_TAC [SIN_ADD, COS_ADD, SIN_PI2, COS_PI2] THEN
    REAL_ARITH_TAC)

  let MEASURABLE_CLOSED_SECTOR_LE ← prove
   r"!r t. measurable {z | norm(z) <= r /\ Arg z <= t}"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC MEASURABLE_COMPACT THEN
    REWRITE_TAC [← SET_RULE (← q r"{z | P z /\ Q z} = {z | P z} INTER {z | Q z}")] THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN REWRITE_TAC [CLOSED_ARG_LE] THEN
    REWRITE_TAC [← NORM_ARITH (← q r"norm z = dist(vec 0,z)"), ← GSYM cball] THEN
    REWRITE_TAC [COMPACT_CBALL])

  let MEASURABLE_CLOSED_SECTOR_LT ← prove
   r"!r t. measurable {z | norm(z) <= r /\ Arg z < t}"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC MEASURABLE_NEGLIGIBLE_SYMDIFF THEN
    EXISTS_TAC (← q r"{z | norm(z) <= r /\ Arg z <= t}") THEN
    REWRITE_TAC [MEASURABLE_CLOSED_SECTOR_LE] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC (← q r"{z | Arg z = t}") THEN
    REWRITE_TAC [NEGLIGIBLE_ARG_EQ, NEGLIGIBLE_UNION_EQ] THEN
    REWRITE_TAC [SUBSET, IN_DIFF, IN_UNION, IN_ELIM_THM] THEN REAL_ARITH_TAC)

  let MEASURABLE_CLOSED_SECTOR_LTE ← prove
   r"!r s t. measurable {z | norm(z) <= r /\ s < Arg z /\ Arg z <= t}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← SET_RULE
     (← q r"{z | P z /\ Q z /\ R z} = {z | P z /\ R z} DIFF {z | P z /\ ~Q z}")] THEN
    SIMP_TAC [MEASURABLE_DIFF, REAL_NOT_LT, MEASURABLE_CLOSED_SECTOR_LE])

  let MEASURE_CLOSED_SECTOR_LE ← prove
   r"!t r. &0 <= r /\ &0 <= t /\ t <= &2 * pi
           ==> measure {x:real^2 | norm(x) <= r /\ Arg(x) <= t} =
               t * r pow 2 / &2"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL
     [← q r"\t. measure {z:real^2 | norm(z) <= r /\ Arg(z) <= t}",
      ← q r"&2 * pi"] REAL_CONTINUOUS_ADDITIVE_IMP_LINEAR_INTERVAL) THEN
    ANTS_TAC THENL
     [ALL_TAC,
      DISCH_THEN (MP_TAC o SPECL [← q r"t / (&2 * pi)", ← q r"&2 * pi"]) THEN
      MP_TAC (← SPECL [← q r"vec 0:real^2", ← q r"r:real"] AREA_CBALL) THEN
      ASM_REWRITE_TAC [cball, ← NORM_ARITH (← q r"dist(vec 0,z) = norm z")] THEN
      SIMP_TAC [ARG, REAL_LT_IMP_LE] THEN DISCH_THEN (K ALL_TAC : thm → tactic) THEN
      SIMP_TAC [PI_POS, ← REAL_FIELD (← q r"&0 < p ==> t / (&2 * p) * p * r = t * r / &2"),
               ← REAL_FIELD (← q r"&0 < p ==> t / (&2 * p) * &2 * p = t")] THEN
      DISCH_THEN MATCH_MP_TAC THEN MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC [] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
      EXISTS_TAC (← q r"\t. r pow 2 * sin(t)") THEN REWRITE_TAC [] THEN CONJ_TAC THENL
       [REWRITE_TAC [EVENTUALLY_WITHINREAL] THEN EXISTS_TAC (← q r"pi / &2") THEN
        SIMP_TAC [PI_POS, REAL_LT_DIV, IN_ELIM_THM, REAL_OF_NUM_LT, ARITH] THEN
        X_GEN_TAC (← q r"x:real") THEN REWRITE_TAC [REAL_SUB_RZERO] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        ASM_SIMP_TAC [real_abs, MEASURE_POS_LE, MEASURABLE_CLOSED_SECTOR_LE] THEN
        STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (← q r"measure(interval[vec 0,complex(r,r * sin x)])") THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC MEASURE_SUBSET THEN
          REWRITE_TAC [MEASURABLE_CLOSED_SECTOR_LE, MEASURABLE_INTERVAL] THEN
          REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_INTERVAL] THEN
          X_GEN_TAC (← q r"z:complex") THEN STRIP_TAC THEN
          REWRITE_TAC [DIMINDEX_2, FORALL_2, VEC_COMPONENT] THEN
          REWRITE_TAC [← GSYM IM_DEF, ← GSYM RE_DEF, IM, RE] THEN
          SUBST1_TAC (← liftExcept (last (CONJUNCTS (← SPEC (← q r"z:complex") ARG)))) THEN
          REWRITE_TAC [RE_MUL_CX, IM_MUL_CX, CEXP_EULER] THEN
          REWRITE_TAC [RE_ADD, ← GSYM CX_COS, ← GSYM CX_SIN, RE_CX, IM_CX,
                      RE_MUL_II, IM_MUL_II, IM_ADD] THEN
          REWRITE_TAC [REAL_NEG_0, REAL_ADD_LID, REAL_ADD_RID] THEN
          SUBGOAL_THEN (← q r"&0 <= Arg z /\ Arg z < pi / &2 /\ Arg z <= pi / &2")
          STRIP_ASSUME_TAC THENL
           [REWRITE_TAC [ARG] THEN ASM_REAL_ARITH_TAC, ALL_TAC] THEN
          REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [NORM_POS_LE] THEN
            MATCH_MP_TAC COS_POS_PI_LE THEN ASM_REAL_ARITH_TAC,
            MATCH_MP_TAC (← REAL_ARITH (← q r"abs(a * b) <= c * &1 ==> a * b <= c")) THEN
            REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_NORM] THEN
            MATCH_MP_TAC REAL_LE_MUL2 THEN
            ASM_REWRITE_TAC [NORM_POS_LE, REAL_ABS_POS, COS_BOUND],
            MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [NORM_POS_LE] THEN
            MATCH_MP_TAC SIN_POS_PI_LE THEN ASM_REAL_ARITH_TAC,
            MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC [NORM_POS_LE] THEN
            CONJ_TAC THENL
             [MATCH_MP_TAC SIN_POS_PI_LE THEN ASM_REAL_ARITH_TAC,
              MATCH_MP_TAC SIN_MONO_LE THEN ASM_REAL_ARITH_TAC]],
          REWRITE_TAC [MEASURE_INTERVAL, CONTENT_CLOSED_INTERVAL_CASES] THEN
          REWRITE_TAC [FORALL_2, PRODUCT_2, DIMINDEX_2, VEC_COMPONENT] THEN
          REWRITE_TAC [← GSYM IM_DEF, ← GSYM RE_DEF, IM, RE] THEN
          REWRITE_TAC [REAL_SUB_RZERO, REAL_POW_2, REAL_MUL_ASSOC] THEN
          SUBGOAL_THEN (← q r"&0 <= sin x") (fun th =>
            ASM_SIMP_TAC [REAL_LE_MUL, REAL_LE_REFL, REAL_LE_MUL, th]) THEN
          MATCH_MP_TAC SIN_POS_PI_LE THEN ASM_REAL_ARITH_TAC],
        MATCH_MP_TAC REALLIM_ATREAL_WITHINREAL THEN
        SUBGOAL_THEN (← q r"(\t. r pow 2 * sin t) real_continuous atreal (&0)")
        MP_TAC THENL
         [MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN
          REWRITE_TAC [ETA_AX, REAL_CONTINUOUS_AT_SIN],
          REWRITE_TAC [REAL_CONTINUOUS_ATREAL, SIN_0, REAL_MUL_RZERO]]],
      ASM_SIMP_TAC [← REAL_ARITH
        (← q r"&0 <= x /\ &0 <= y
         ==> (norm z <= r /\ Arg z <= x + y <=>
              norm z <= r /\ Arg z <= x \/
              norm z <= r /\ x < Arg z /\ Arg z <= x + y)")] THEN
      REWRITE_TAC [← SET_RULE (← q r"{z | Q z \/ R z} = {z | Q z} UNION {z | R z}")] THEN
      SIMP_TAC [MEASURE_UNION, MEASURABLE_CLOSED_SECTOR_LE,
               MEASURABLE_CLOSED_SECTOR_LTE] THEN
      REWRITE_TAC [← GSYM REAL_NOT_LE, ← SET_RULE
       (← q r"{z | P z /\ Q z} INTER {z | P z /\ ~Q z /\ R z} = {}")] THEN
      REWRITE_TAC [MEASURE_EMPTY, REAL_SUB_RZERO, REAL_EQ_ADD_LCANCEL] THEN
      REWRITE_TAC [REAL_NOT_LE] THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC (← q r"measure {z | norm z <= r /\ x < Arg z /\ Arg z < x + y}") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
        REWRITE_TAC [MEASURABLE_CLOSED_SECTOR_LTE] THEN
        MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC (← q r"{z | Arg z = x + y}") THEN
        REWRITE_TAC [NEGLIGIBLE_ARG_EQ, NEGLIGIBLE_UNION_EQ] THEN
        REWRITE_TAC [SUBSET, IN_DIFF, IN_UNION, IN_ELIM_THM] THEN REAL_ARITH_TAC,
        ALL_TAC] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC (← q r"measure {z | norm z <= r /\ &0 < Arg z /\ Arg z < y}") THEN
      CONJ_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
        REWRITE_TAC [MEASURABLE_CLOSED_SECTOR_LE] THEN
        MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC (← q r"{z | Arg z = &0} UNION {z | Arg z = y}") THEN
        REWRITE_TAC [NEGLIGIBLE_ARG_EQ, NEGLIGIBLE_UNION_EQ] THEN
        REWRITE_TAC [SUBSET, IN_DIFF, IN_UNION, IN_ELIM_THM] THEN
        MP_TAC ARG THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC] THEN
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
       (← q r"measure (IMAGE (rotate2d x)
                {z | norm z <= r /\ &0 < Arg z /\ Arg z < y})") THEN
      CONJ_TAC THENL
       [ALL_TAC,
        ASM_SIMP_TAC [MEASURE_ORTHOGONAL_IMAGE_EQ,
                     ORTHOGONAL_TRANSFORMATION_ROTATE2D]] THEN
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN CONJ_TAC THENL
       [ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION_SURJECTIVE,
                      ORTHOGONAL_TRANSFORMATION_ROTATE2D], ALL_TAC] THEN
      X_GEN_TAC (← q r"z:complex") THEN REWRITE_TAC [IN_ELIM_THM] THEN
      ASM_CASES_TAC (← q r"z = Cx(&0)") THENL
       [ASM_REWRITE_TAC [Arg_DEF, ROTATE2D_0] THEN
        ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [NORM_ROTATE2D] THEN AP_TERM_TAC THEN EQ_TAC THENL
       [STRIP_TAC THEN
        SUBGOAL_THEN (← q r"z = rotate2d (--x) (rotate2d x z)") SUBST1_TAC THENL
         [REWRITE_TAC [← GSYM ROTATE2D_ADD, REAL_ADD_LINV, ROTATE2D_ZERO],
          ALL_TAC] THEN
        MP_TAC (← ISPECL [← q r"--x:real", ← q r"rotate2d x z"] ARG_ROTATE2D) THEN
        ASM_REWRITE_TAC [ROTATE2D_EQ_0] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC, DISCH_THEN SUBST1_TAC] THEN
        ASM_REAL_ARITH_TAC,
        STRIP_TAC THEN
        MP_TAC (← ISPECL [← q r"x:real", ← q r"z:complex"] ARG_ROTATE2D) THEN
        ASM_REWRITE_TAC [ROTATE2D_EQ_0] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC, DISCH_THEN SUBST1_TAC] THEN
        ASM_REAL_ARITH_TAC]])

  let HAS_MEASURE_OPEN_SECTOR_LT ← prove
   r"!t r. &0 <= t /\ t <= &2 * pi
           ==> {x:real^2 | norm(x) < r /\ &0 < Arg x /\ Arg x < t}
               has_measure (if &0 <= r then t * r pow 2 / &2 else &0)"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [← NORM_ARITH (← q r"~(&0 <= r) ==> ~(norm x < r)"),
                 EMPTY_GSPEC, HAS_MEASURE_EMPTY] THEN
    MATCH_MP_TAC HAS_MEASURE_NEGLIGIBLE_SYMDIFF THEN
    EXISTS_TAC (← q r"{x | norm x <= r /\ Arg x <= t}") THEN
    REWRITE_TAC [HAS_MEASURE_MEASURABLE_MEASURE] THEN
    ASM_SIMP_TAC [MEASURE_CLOSED_SECTOR_LE, MEASURABLE_CLOSED_SECTOR_LE] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC (← q r"{x | dist(vec 0,x) = r} UNION
                {z | Arg z = &0} UNION {z | Arg z = t}") THEN
    REWRITE_TAC [NEGLIGIBLE_ARG_EQ, ← REWRITE_RULE [sphere] NEGLIGIBLE_SPHERE,
                NEGLIGIBLE_UNION_EQ] THEN
    REWRITE_TAC [DIST_0, SUBSET, IN_DIFF, IN_UNION, IN_ELIM_THM] THEN
        MP_TAC ARG THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC)

  let MEASURE_OPEN_SECTOR_LT ← prove
   r"!t r. &0 <= t /\ t <= &2 * pi
           ==> measure {x:real^2 | norm(x) < r /\ &0 < Arg x /\ Arg x < t} =
               if &0 <= r then t * r pow 2 / &2 else &0"
   (SIMP_TAC [← REWRITE_RULE [HAS_MEASURE_MEASURABLE_MEASURE]
             HAS_MEASURE_OPEN_SECTOR_LT])

  let HAS_MEASURE_OPEN_SECTOR_LT_GEN ← prove
   r"!w z.
          ~(w = vec 0)
          ==> {x | norm(x) < r /\ &0 < Arg(x / w) /\ Arg(x / w) < Arg(z / w)}
              has_measure (if &0 <= r then Arg(z / w) * r pow 2 / &2 else &0)"
   (GEOM_BASIS_MULTIPLE_TAC 1 (← q r"w:complex") THEN
    X_GEN_TAC (← q r"w:real") THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
    ASM_CASES_TAC (← q r"w = &0") THEN ASM_REWRITE_TAC [VECTOR_MUL_LZERO] THEN
    REWRITE_TAC [COMPLEX_CMUL, COMPLEX_BASIS, COMPLEX_VEC_0] THEN
    SIMP_TAC [ARG_DIV_CX, COMPLEX_MUL_RID] THEN ASM_REWRITE_TAC [CX_INJ] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_MEASURE_OPEN_SECTOR_LT THEN
    SIMP_TAC [ARG, REAL_LT_IMP_LE])

  pure { NEGLIGIBLE_CIRCULAR_CONE_0_NONPARALLEL, NEGLIGIBLE_CIRCULAR_CONE_0,
         NEGLIGIBLE_CIRCULAR_CONE, NEGLIGIBLE_RCONE_EQ, NEGLIGIBLE_ARG_EQ,
         MEASURABLE_CLOSED_SECTOR_LE, MEASURABLE_CLOSED_SECTOR_LT,
         MEASURABLE_CLOSED_SECTOR_LTE, MEASURE_CLOSED_SECTOR_LE,
         HAS_MEASURE_OPEN_SECTOR_LT, MEASURE_OPEN_SECTOR_LT,
         HAS_MEASURE_OPEN_SECTOR_LT_GEN }
/- ------------------------------------------------------------------------- -/
/- Hence volume of a wedge of a ball; hence volume of lune.                  -/
/- (flyspeck.ml 5442-5632)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FYS where
  MEASURABLE_BALL_WEDGE : thm
  VOLUME_BALL_WEDGE : thm
  HAS_MEASURE_LUNE : thm
  HAS_MEASURE_LUNE_SIMPLE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYS [HolBase] (D : FlyspeckDeps) (BFYA : FYA) (BFYC : FYC) (BFYE : FYE) (BFYI : FYI) (BFYJ : FYJ) (BFYK : FYK) (BFYM : FYM) (BFYN : FYN) (BFYO : FYO) (BFYP : FYP) (BFYR : FYR) : ExceptT String IO FYS := do
  -- @@SCOPE BEGIN
  let { COLLINEAR_BASIS_3, COLLINEAR_SPECIAL_SCALE, COPLANAR_IMP_NEGLIGIBLE,
        NOT_COPLANAR_NOT_COLLINEAR, SLICE_DROPOUT_3, .. } := BFYA
  let { aff_gt_def, AFFSIGN, sgn_gt, .. } := BFYC
  let { AFF_GT_SPECIAL_SCALE, .. } := BFYE
  let { azim, AZIM_ARG, AZIM_DEGENERATE, AZIM_SPECIAL_SCALE, .. } := BFYI
  let { AZIM_COMPL, AZIM_EQ_0_PI_IMP_COPLANAR, .. } := BFYJ
  let { AZIM_DIHV_COMPL, AZIM_DIHV_SAME, AZIM_DIVH, DIHV_SPECIAL_SCALE, .. } := BFYK
  let { wedge, WEDGE_DEGENERATE, .. } := BFYM
  let { WEDGE_LUNE_GT, .. } := BFYN
  let { OPEN_WEDGE, .. } := BFYO
  let { AREA_CBALL, .. } := BFYP
  let { MEASURE_OPEN_SECTOR_LT, .. } := BFYR
  let { ASM_MESON_TAC, MESON_TAC, REAL_ARITH_TAC, REAL_RING, .. } := D.crd
  let { COPLANAR_3, COPLANAR_AFFINE_HULL_COPLANAR, COPLANAR_SUBSET, .. } := D.qconvex
  let { GEOM_ORIGIN_TAC, .. } := D.geomorigin
  let { REAL_DIFF_TAC, .. } := D.gm.rzq
  let { HAS_REAL_INTEGRAL_EQ, .. } := D.gm.rzal
  let { REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS, .. } := D.gm.rzan
  let { HAS_REAL_INTEGRAL_RESTRICT_UNIV, .. } := D.gm.rzao
  let { HAS_REAL_INTEGRAL_OPEN_INTERVAL, .. } := D.gm.rzap
  let { SLICE_BALL, SLICE_INTER, .. } := D.gm.rzaz
  let { FUBINI_SIMPLE_OPEN, .. } := D.gm.rzbc
  let { ARITH, CONJ_ASSOC, DIMINDEX_3, REAL_MUL_LZERO, REAL_SUB_RZERO, .. } := D.crd.thms
  let { PI_POS, .. } := D.gm.ra.tse
  let { ARG, ARG_0, ARG_DIV_CX, .. } := D.gm.ra.tsh
  let { DROPOUT_0, .. } := D.gm.ra.qvectors
  let { IN_REAL_INTERVAL, .. } := D.gm.ra.qmisc
  let { HAS_MEASURE_0, HAS_MEASURE_MEASURABLE_MEASURE, MEASURABLE_OPEN, MEASURE_EMPTY,
        .. } := D.gm.ra.qmeasure
  let { COMPLEX_MUL_RID, .. } := D.gm.ra.ts.cn.cxb
  let { COMPLEX_CMUL, COMPLEX_VEC_0, CX_INJ, .. } := D.gm.ra.ts.cn.cxc
  let { COMPLEX_BASIS, .. } := D.gm.ra.ts.cn.cxh
  let { ASM_REAL_ARITH_TAC, GEOM_BASIS_MULTIPLE_TAC, NUM_REDUCE_CONV, REAL_ARITH, SET_RULE,
        .. } := D.gm.ra.ts.cn.cx.cvx
  let { COND_ID, COND_RAND, COND_RATOR, DE_MORGAN_THM, DIMINDEX_2, EQ_IMP, FINITE_EMPTY,
        FINITE_INSERT, .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { IMP_IMP, INSERT_AC, INTER, INTER_EMPTY, INTER_SUBSET,
        .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, MONO_EXISTS, NOT_IMP, NOT_IN_EMPTY,
        .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_LE_LT, REAL_LE_REFL, REAL_LE_SQUARE_ABS, REAL_LT_IMP_LE, REAL_LT_IMP_NZ,
        REAL_LT_LE, REAL_LT_REFL, .. } := D.gm.ra.ts.cn.cx.cvx.core4
  let { REAL_NOT_LT, REAL_SUB_LE, RIGHT_IMP_FORALL_THM, SQRT_POS_LE, SQRT_POW_2, SUBSET,
        .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { COLLINEAR_2, .. } := D.gm.ra.ts.cn.cx.cvx.vec1
  let { VEC_COMPONENT, VECTOR_MUL_EQ_0, VECTOR_MUL_LZERO, .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { BOUNDED_BALL, BOUNDED_SUBSET, .. } := D.gm.ra.ts.cn.cx.cvx.top1
  let { IN_BALL_0, OPEN_BALL, .. } := D.gm.ra.ts.cn.cx.cvx.top4
  let { OPEN_INTER, .. } := D.gm.ra.ts.cn.cx.cvx.top5
  let { REAL_BOUNDS_LE, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qses
  let { BOUNDED_INTER, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qtop
  let { AFFINE_HULL_FINITE, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qcvx1
  -- @@SCOPE END

  let MEASURABLE_BALL_WEDGE ← prove
   r"!z:real^3 w w1 w2. measurable(ball(z,r) INTER wedge z w w1 w2)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_OPEN THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_INTER THEN REWRITE_TAC [BOUNDED_BALL],
      MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC [OPEN_BALL] THEN
      ASM_SIMP_TAC [OPEN_WEDGE]])

  let VOLUME_BALL_WEDGE ← prove
   r"!z:real^3 w r w1 w2.
          &0 <= r ==> measure(ball(z,r) INTER wedge z w w1 w2) =
                         azim z w w1 w2 * &2 * r pow 3 / &3"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"z:real^3 = w \/  collinear{z,w,w1} \/ collinear{z,w,w2}") THENL
     [FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
      ASM_SIMP_TAC [WEDGE_DEGENERATE, AZIM_DEGENERATE, INTER_EMPTY, REAL_MUL_LZERO,
                   MEASURE_EMPTY],
      FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC [IMP_IMP, DE_MORGAN_THM]] THEN
    REWRITE_TAC [wedge] THEN GEOM_ORIGIN_TAC (← q r"z:real^3") THEN
    GEOM_BASIS_MULTIPLE_TAC 3 (← q r"w:real^3") THEN
    X_GEN_TAC (← q r"w:real") THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
    ASM_CASES_TAC (← q r"w = &0") THEN ASM_REWRITE_TAC [VECTOR_MUL_LZERO] THEN
    ASM_SIMP_TAC [AZIM_SPECIAL_SCALE, COLLINEAR_SPECIAL_SCALE] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← HolLight.INST_TYPE [(← qty "2", ← qty "M"), (← qty "3", ← qty "N")]
      FUBINI_SIMPLE_OPEN) THEN
    EXISTS_TAC (← q r"3") THEN REWRITE_TAC [DIMINDEX_2, DIMINDEX_3, ARITH] THEN
    REPEAT CONJ_TAC THENL
     [MESON_TAC [BOUNDED_SUBSET, INTER_SUBSET, BOUNDED_BALL],
      REWRITE_TAC [← GSYM wedge] THEN MATCH_MP_TAC OPEN_INTER THEN
      ASM_REWRITE_TAC [OPEN_BALL, OPEN_WEDGE],
      SIMP_TAC [SLICE_INTER, DIMINDEX_2, DIMINDEX_3, ARITH, SLICE_BALL]] THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"~a /\ b /\ c <=> ~(~a ==> ~(b /\ c))")] THEN
    ASM_SIMP_TAC [AZIM_ARG] THEN REWRITE_TAC [COLLINEAR_BASIS_3] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [COLLINEAR_BASIS_3]) THEN
    REWRITE_TAC [NOT_IMP, ← GSYM CONJ_ASSOC, DROPOUT_0] THEN
    MAP_EVERY ABBREV_TAC
     [← q r"v1:real^2 = dropout 3 (w1:real^3)",
      ← q r"v2:real^2 = dropout 3 (w2:real^3)"] THEN
    REWRITE_TAC [SLICE_DROPOUT_3, VEC_COMPONENT, REAL_SUB_RZERO] THEN
    ONCE_REWRITE_TAC [COND_RAND] THEN
    ONCE_REWRITE_TAC [COND_RATOR] THEN
    REWRITE_TAC [INTER_EMPTY] THEN REWRITE_TAC [INTER, IN_BALL_0, IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC [COND_RAND] THEN REWRITE_TAC [MEASURE_EMPTY] THEN
    MAP_EVERY UNDISCH_TAC
     [← q r"~(v1:complex = vec 0)", ← q r"~(v2:complex = vec 0)"] THEN
    MAP_EVERY (fun t => SPEC_TAC (t, t)) [← q r"v2:complex", ← q r"v1:complex"] THEN
    UNDISCH_TAC (← q r"&0 <= r") THEN SPEC_TAC (← q r"r:real", ← q r"r:real") THEN
    REWRITE_TAC [RIGHT_IMP_FORALL_THM, IMP_IMP, ← GSYM CONJ_ASSOC] THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN GEOM_BASIS_MULTIPLE_TAC 1 (← q r"v1:complex") THEN
    X_GEN_TAC (← q r"v1:real") THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
    ASM_CASES_TAC (← q r"v1 = &0") THEN ASM_REWRITE_TAC [VECTOR_MUL_LZERO] THEN
    REWRITE_TAC [COMPLEX_CMUL, COMPLEX_BASIS, COMPLEX_VEC_0] THEN
    SIMP_TAC [ARG_DIV_CX, COMPLEX_MUL_RID, CX_INJ] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"!t z. ~(z = Cx(&0)) /\ &0 < Arg z /\ Arg z < t <=>
            &0 < Arg z /\ Arg z < t")
     (fun th => REWRITE_TAC [th])
    THENL [MESON_TAC [ARG_0, REAL_LT_REFL], ALL_TAC] THEN
    ASM_SIMP_TAC [MEASURE_OPEN_SECTOR_LT, REAL_LE_REFL, ARG, REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN (← q r"!t. abs(t) < r <=> t IN real_interval(--r,r)")
     (fun th => REWRITE_TAC [th])
    THENL [REWRITE_TAC [IN_REAL_INTERVAL] THEN REAL_ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
    REWRITE_TAC [HAS_REAL_INTEGRAL_OPEN_INTERVAL] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
    EXISTS_TAC (← q r"\t. Arg v2 * (r pow 2 - t pow 2) / &2") THEN CONJ_TAC THENL
     [X_GEN_TAC (← q r"t:real") THEN REWRITE_TAC [IN_REAL_INTERVAL, REAL_BOUNDS_LE] THEN
      SIMP_TAC [AREA_CBALL, SQRT_POS_LE, REAL_SUB_LE, ← GSYM REAL_LE_SQUARE_ABS,
               SQRT_POW_2, ← REAL_ARITH (← q r"abs x <= r ==> abs x <= abs r")],
      ALL_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"\t. Arg v2 * (r pow 2 * t - &1 / &3 * t pow 3) / &2",
      ← q r"\t. Arg v2 * (r pow 2 - t pow 2) / &2",
      ← q r"--r:real", ← q r"r:real"] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING,
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC REAL_RING])

  /- Hence volume of lune. -/

  let HAS_MEASURE_LUNE ← prove
   r"!z:real^3 w r w1 w2.
          &0 <= r /\ ~(w = z) /\
          ~collinear {z,w,w1} /\ ~collinear {z,w,w2} /\ ~(dihV z w w1 w2 = pi)
          ==> (ball(z,r) INTER aff_gt {z,w} {w1,w2})
              has_measure (dihV z w w1 w2 * &2 * r pow 3 / &3)"
   (GEOM_ORIGIN_TAC (← q r"z:real^3") THEN
    GEOM_BASIS_MULTIPLE_TAC 3 (← q r"w:real^3") THEN
    X_GEN_TAC (← q r"w:real") THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
    ASM_CASES_TAC (← q r"w = &0") THEN ASM_REWRITE_TAC [] THENL
     [ASM_REWRITE_TAC [VECTOR_MUL_LZERO, INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    ASM_SIMP_TAC [DIHV_SPECIAL_SCALE] THEN
    MP_TAC (← ISPECL [← q r"{}:real^3->bool", ← q r"{w1:real^3,w2:real^3}",
                   ← q r"w:real", ← q r"basis 3:real^3"] AFF_GT_SPECIAL_SCALE) THEN
    ASM_CASES_TAC (← q r"w1:real^3 = vec 0") THENL
     [ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"w2:real^3 = vec 0") THENL
     [ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    ASM_REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY, IN_INSERT, NOT_IN_EMPTY] THEN
    ASM_CASES_TAC (← q r"w1:real^3 = w % basis 3") THENL
     [ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"w2:real^3 = w % basis 3") THENL
     [ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    ASM_SIMP_TAC [COLLINEAR_SPECIAL_SCALE] THEN
    ASM_CASES_TAC (← q r"w1:real^3 = basis 3") THENL
     [ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"w2:real^3 = basis 3") THENL
     [ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC [VECTOR_MUL_EQ_0, REAL_LT_IMP_NZ] THEN STRIP_TAC THEN
    ASM_CASES_TAC (← q r"azim (vec 0) (basis 3) w1 w2 = &0") THENL
     [MP_TAC (← ASSUME (← q r"azim (vec 0) (basis 3) w1 w2 = &0")) THEN
      W (MP_TAC o PART_MATCH (lhs o rand) AZIM_DIVH o lhs o lhand o snd) THEN
      ASM_REWRITE_TAC [PI_POS] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      REWRITE_TAC [REAL_MUL_LZERO, HAS_MEASURE_0] THEN
      MATCH_MP_TAC COPLANAR_IMP_NEGLIGIBLE THEN
      MATCH_MP_TAC COPLANAR_SUBSET THEN
      EXISTS_TAC (← q r"affine hull {vec 0:real^3,basis 3,w1,w2}") THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC [COPLANAR_AFFINE_HULL_COPLANAR, AZIM_EQ_0_PI_IMP_COPLANAR],
        ALL_TAC] THEN
      MATCH_MP_TAC (← SET_RULE (← q r"t SUBSET u ==> (s INTER t) SUBSET u")) THEN
      SIMP_TAC [aff_gt_def, AFFSIGN, sgn_gt, AFFINE_HULL_FINITE,
               FINITE_INSERT, FINITE_EMPTY] THEN
      REWRITE_TAC [← SET_RULE (← q r"{a,b} UNION {c,d} = {a,b,c,d}")] THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN GEN_TAC THEN
      MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&0 < azim (vec 0) (basis 3) w1 w2") ASSUME_TAC THENL
     [ASM_REWRITE_TAC [REAL_LT_LE, azim], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"azim (vec 0) (basis 3) w1 w2 < pi") THENL
     [ASM_SIMP_TAC [← GSYM AZIM_DIHV_SAME, ← GSYM WEDGE_LUNE_GT] THEN
      ASM_SIMP_TAC [HAS_MEASURE_MEASURABLE_MEASURE, MEASURABLE_BALL_WEDGE,
                   VOLUME_BALL_WEDGE],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"azim (vec 0) (basis 3) w1 w2 = pi") THENL
     [MP_TAC (← ISPECL [← q r"vec 0:real^3", ← q r"basis 3:real^3", ← q r"w1:real^3", ← q r"w2:real^3"]
             AZIM_DIVH) THEN
      ASM_REWRITE_TAC [REAL_LT_REFL] THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"dihV (vec 0) (basis 3) w1 w2 = azim (vec 0) (basis 3) w2 w1")
    SUBST1_TAC THENL
     [W (MP_TAC o PART_MATCH (lhs o rand) AZIM_COMPL o rand o snd) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
      ONCE_REWRITE_TAC [← REAL_ARITH (← q r"x:real = y - z <=> z = y - x")] THEN
      MATCH_MP_TAC AZIM_DIHV_COMPL THEN
      ASM_REWRITE_TAC [← GSYM REAL_NOT_LT],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&0 < azim (vec 0) (basis 3) w2 w1 /\
                  azim (vec 0) (basis 3) w2 w1 < pi")
    ASSUME_TAC THENL
     [W (MP_TAC o PART_MATCH (lhs o rand) AZIM_COMPL o lhand o rand o snd) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC (← ISPECL [← q r"vec 0:real^3", ← q r"basis 3:real^3", ← q r"w1:real^3", ← q r"w2:real^3"]
          azim) THEN
      REWRITE_TAC [CONJ_ASSOC] THEN DISCH_THEN (MP_TAC o CONJUNCT1) THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    SUBST1_TAC (← SET_RULE (← q r"{w1:real^3,w2} = {w2,w1}")) THEN
    ASM_SIMP_TAC [← GSYM AZIM_DIHV_SAME, ← GSYM WEDGE_LUNE_GT] THEN
    ASM_SIMP_TAC [HAS_MEASURE_MEASURABLE_MEASURE, MEASURABLE_BALL_WEDGE,
                 VOLUME_BALL_WEDGE])

  let HAS_MEASURE_LUNE_SIMPLE ← prove
   r"!z:real^3 w r w1 w2.
          &0 <= r /\ ~coplanar{z,w,w1,w2}
          ==> (ball(z,r) INTER aff_gt {z,w} {w1,w2})
              has_measure (dihV z w w1 w2 * &2 * r pow 3 / &3)"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"w:real^3 = z") THENL
     [ASM_REWRITE_TAC [INSERT_AC, COPLANAR_3], ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_MEASURE_LUNE THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ b /\ (a /\ b ==> c) ==> a /\ b /\ c")) THEN
    REPEAT (CONJ_TAC THENL
     [ASM_MESON_TAC [NOT_COPLANAR_NOT_COLLINEAR, INSERT_AC], ALL_TAC]) THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"z:real^3", ← q r"w:real^3", ← q r"w1:real^3", ← q r"w2:real^3"]
          AZIM_DIVH) THEN
    ASM_REWRITE_TAC [← REAL_ARITH (← q r"&2 * pi - pi = pi"), COND_ID] THEN
    ASM_MESON_TAC [AZIM_EQ_0_PI_IMP_COPLANAR])

  pure { MEASURABLE_BALL_WEDGE, VOLUME_BALL_WEDGE, HAS_MEASURE_LUNE,
         HAS_MEASURE_LUNE_SIMPLE }
/- ------------------------------------------------------------------------- -/
/- Now the volume of a solid triangle.                                       -/
/- (flyspeck.ml 5634-5971)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FYT where
  MEASURABLE_BALL_AFF_GT : thm
  AFF_GT_SHUFFLE : thm
  MEASURE_BALL_AFF_GT_SHUFFLE_LEMMA : thm
  MEASURE_BALL_AFF_GT_SHUFFLE : thm
  MEASURE_LUNE_DECOMPOSITION : thm
  SOLID_TRIANGLE_CONGRUENT_NEG : thm
  VOLUME_SOLID_TRIANGLE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYT [HolBase] (D : FlyspeckDeps) (BFYA : FYA) (BFYC : FYC) (BFYE : FYE) (BFYK : FYK) (BFYP : FYP) (BFYS : FYS) : ExceptT String IO FYT := do
  -- @@SCOPE BEGIN
  let { COPLANAR_INSERT_0_NEG, NOT_COPLANAR_0_4_IMP_INDEPENDENT, .. } := BFYA
  let { aff_gt_def, AFFSIGN_ALT, sgn_gt, .. } := BFYC
  let { AFF_GT_EQ_AFFINE_HULL, AFF_GT_SUBSET_AFFINE_HULL, CONVEX_AFF_GT, .. } := BFYE
  let { DIHV_NEG_0, .. } := BFYK
  let { VOLUME_BALL, .. } := BFYP
  let { HAS_MEASURE_LUNE_SIMPLE, .. } := BFYS
  let { let_CONV, .. } := D
  let { ASM_MESON_TAC, MESON_TAC, REAL_ARITH_TAC, .. } := D.crd
  let { AFFINE_HULL_FINITE_STEP_GEN, COPLANAR_3, .. } := D.qconvex
  let { INDEPENDENT_BOUND, INDEPENDENT_EXPLICIT, INDEPENDENT_MONO, .. } := D.qvectors
  let { MEASURE_DISJOINT_UNION, MEASURE_NEGLIGIBLE_SYMDIFF, MEASURE_ORTHOGONAL_IMAGE_EQ,
        NEGLIGIBLE_LOWDIM, .. } := D.qmeasure
  let { SUM_CASES_1, .. } := D.qsession
  let { GEOM_ORIGIN_TAC, .. } := D.geomorigin
  let { DIMINDEX_3, linear, ORTHOGONAL_TRANSFORMATION, REAL_SUB_RZERO, .. } := D.crd.thms
  let { HAS_MEASURE_MEASURABLE_MEASURE, MEASURABLE_CONVEX, MEASURABLE_UNION,
        .. } := D.gm.ra.qmeasure
  let { NEGLIGIBLE_SUBSET, .. } := D.gm.ra.ts.cn.ms.qintegration3
  let { ARITH_RULE, ASM_REAL_ARITH_TAC, NUM_REDUCE_CONV, SET_RULE, SET_TAC, VECTOR_ARITH,
        VECTOR_ARITH_TAC, .. } := D.gm.ra.ts.cn.cx.cvx
  let { CARD_CLAUSES, CARD_DELETE, CONTRAPOS_THM, DE_MORGAN_THM, DIMINDEX_GE_1, DISJOINT,
        EQ_TRANS, EXTENSION, FINITE_DELETE, FINITE_EMPTY, FINITE_INSERT, FINITE_UNION,
        .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { IMP_CONJ, IN_DELETE, INSERT_AC, INTER_SUBSET, .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INSERT, IN_INTER, IN_UNION, LET_TRANS, MONO_EXISTS, NOT_IMP,
        NOT_IN_EMPTY, .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_LT_ADD, REAL_LT_IMP_LE, .. } := D.gm.ra.ts.cn.cx.cvx.core4
  let { RIGHT_EXISTS_AND_THM, .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { SUBSET_UNIV, SURJECTIVE_IMAGE_EQ, SWAP_EXISTS_THM, UNION_ASSOC, UNION_EMPTY,
        .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { HULL_INC, REAL_HALF, .. } := D.gm.ra.ts.cn.cx.cvx.misc
  let { CARD_GE_DIM_INDEPENDENT, DIM_LE_CARD, DIM_SPAN, DIM_UNIV,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec1
  let { INDEPENDENT_NONZERO, .. } := D.gm.ra.ts.cn.cx.cvx.vec2
  let { NORM_NEG, SPAN_DELETE_0, SPAN_INSERT_0, SPAN_NEG, SPAN_SUPERSET,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec3
  let { dependent, independent, VECTOR_MUL_LZERO, VECTOR_MUL_RZERO, VECTOR_NEG_EQ_0,
        VECTOR_NEG_NEG, VECTOR_SUB_RZERO, VSUM_CLAUSES, VSUM_DELETE_CASES, VSUM_EQ,
        VSUM_SUB, .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { BOUNDED_BALL, .. } := D.gm.ra.ts.cn.cx.cvx.top1
  let { IN_BALL_0, .. } := D.gm.ra.ts.cn.cx.cvx.top4
  let { UNION_OVER_INTER, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qses
  let { BOUNDED_INTER, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qtop
  let { AFFINE_HULL_EQ_SPAN, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qcvx1
  let { CONVEX_BALL, CONVEX_INTER, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  -- @@SCOPE END

  let MEASURABLE_BALL_AFF_GT ← prove
   r"!z r s t. measurable(ball(z,r) INTER aff_gt s t)"
   (MESON_TAC [MEASURABLE_CONVEX, CONVEX_INTER, CONVEX_AFF_GT, CONVEX_BALL,
              BOUNDED_INTER, BOUNDED_BALL])

  let AFF_GT_SHUFFLE ← prove
   r"!s t v:real^N.
          FINITE s /\ FINITE t /\
          vec 0 IN s /\ ~(vec 0 IN t) /\
          ~(v IN s) /\ ~(--v IN s) /\ ~(v IN t)
          ==> aff_gt (v INSERT s) t =
              aff_gt s (v INSERT t) UNION
              aff_gt s (--v INSERT t) UNION
              aff_gt s t"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [aff_gt_def, AFFSIGN_ALT, sgn_gt] THEN
    REWRITE_TAC [← SET_RULE (← q r"(v INSERT s) UNION t = v INSERT (s UNION t)"),
                ← SET_RULE (← q r"s UNION (v INSERT t) = v INSERT (s UNION t)")] THEN
    ASM_SIMP_TAC [FINITE_INSERT, FINITE_UNION, AFFINE_HULL_FINITE_STEP_GEN,
                 RIGHT_EXISTS_AND_THM, REAL_LT_ADD, REAL_HALF, FINITE_EMPTY] THEN
    REWRITE_TAC [IN_INSERT] THEN
    ASM_SIMP_TAC [← SET_RULE
     (← q r"~(a IN s)
      ==> ((w IN s UNION t ==> w = a \/ w IN t ==> P w) <=>
           (w IN t ==> P w))")] THEN
    REWRITE_TAC [← SET_RULE (← q r"x IN (s UNION t)
                          ==> x IN t ==> P x <=> x IN t ==> P  x")] THEN
    REWRITE_TAC [EXTENSION, IN_UNION, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"y:real^N") THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"v:real") ASSUME_TAC) THEN
      ASM_CASES_TAC (← q r"&0 < v") THENL
       [DISJ1_TAC THEN EXISTS_TAC (← q r"v:real") THEN ASM_REWRITE_TAC [],
        DISJ2_TAC] THEN
      ASM_CASES_TAC (← q r"v = &0") THENL
       [DISJ2_TAC THEN
        FIRST_ASSUM (fun th => MP_TAC th THEN MATCH_MP_TAC MONO_EXISTS) THEN
        ASM_REWRITE_TAC [REAL_SUB_RZERO, VECTOR_MUL_LZERO, VECTOR_SUB_RZERO],
        DISJ1_TAC] THEN
      EXISTS_TAC (← q r"--v:real") THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"f:real^N->real") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"\x:real^N. if x = vec 0 then f(x) + &2 * v else f(x)") THEN
      REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC [],
        ASM_SIMP_TAC [SUM_CASES_1, FINITE_UNION, IN_UNION] THEN REAL_ARITH_TAC,
        REWRITE_TAC [← VECTOR_ARITH (← q r"--a % --x:real^N = a % x")] THEN
        FIRST_X_ASSUM (fun th => tactic_of do
          pure (GEN_REWRITE_TAC RAND_CONV [← GSYM th])) THEN
        MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC [] THEN
        REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC [VECTOR_MUL_RZERO]],
      DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL [MESON_TAC [], ALL_TAC] THEN
      DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
       [DISCH_THEN (X_CHOOSE_THEN (← q r"a:real")
         (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"f:real^N->real") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"--a:real") THEN
        EXISTS_TAC (← q r"\x:real^N. if x = vec 0 then &2 * a + f(vec 0) else f x") THEN
        ASM_SIMP_TAC [SUM_CASES_1, FINITE_UNION, IN_UNION] THEN
        CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC, ALL_TAC] THEN
        ONCE_REWRITE_TAC [← VECTOR_ARITH (← q r"y - --a % v:real^N = y - a % --v")] THEN
        FIRST_X_ASSUM (fun th => tactic_of do
          pure (GEN_REWRITE_TAC RAND_CONV [← SYM th])) THEN
        MATCH_MP_TAC VSUM_EQ THEN REPEAT GEN_TAC THEN REWRITE_TAC [] THEN
        DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [VECTOR_MUL_RZERO],
        GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
        MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
        EXISTS_TAC (← q r"&0") THEN ASM_REWRITE_TAC [REAL_SUB_RZERO] THEN
        VECTOR_ARITH_TAC]])

  let MEASURE_BALL_AFF_GT_SHUFFLE_LEMMA ← (do
    let lemma ← prove
     r"!s t u:real^N->bool.
            measurable s /\ measurable t /\ s INTER t = {} /\ negligible u
            ==> measure(s UNION t UNION u) = measure s + measure t"
     (REPEAT STRIP_TAC THEN REWRITE_TAC [UNION_ASSOC] THEN
      ASM_SIMP_TAC [← GSYM MEASURE_DISJOINT_UNION, DISJOINT] THEN
      MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
      ASM_SIMP_TAC [MEASURABLE_UNION] THEN
      FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP
       (← REWRITE_RULE [IMP_CONJ] NEGLIGIBLE_SUBSET)) THEN SET_TAC [])
    prove
     r"!r s t v:real^N.
          &0 <= r /\
          independent(v INSERT((s DELETE vec 0) UNION t)) /\
          FINITE s /\ FINITE t /\ CARD(s UNION t) <= dimindex(:N) /\
          vec 0 IN s /\ ~(vec 0 IN t) /\
          ~(v IN s) /\ ~(--v IN s) /\ ~(v IN t)
          ==> measure(ball(vec 0,r) INTER aff_gt (v INSERT s) t) =
              measure(ball(vec 0,r) INTER aff_gt s (v INSERT t)) +
              measure(ball(vec 0,r) INTER aff_gt s (--v INSERT t))"
      (REPEAT STRIP_TAC THEN
      W (MP_TAC o PART_MATCH (lhs o rand) AFF_GT_SHUFFLE o
        rand o rand o lhand o snd) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [UNION_OVER_INTER] THEN MATCH_MP_TAC lemma THEN
      ASM_REWRITE_TAC [MEASURABLE_BALL_AFF_GT] THEN CONJ_TAC THENL
       [MATCH_MP_TAC (← SET_RULE
         (← q r"t INTER u = {} ==> (s INTER t) INTER (s INTER u) = {}")) THEN
        REWRITE_TAC [aff_gt_def, AFFSIGN_ALT, sgn_gt] THEN
        REWRITE_TAC [← SET_RULE (← q r"(v INSERT s) UNION t = v INSERT (s UNION t)"),
                    ← SET_RULE (← q r"s UNION (v INSERT t) = v INSERT (s UNION t)")] THEN
        ASM_SIMP_TAC [FINITE_INSERT, FINITE_UNION, AFFINE_HULL_FINITE_STEP_GEN,
                     RIGHT_EXISTS_AND_THM, REAL_LT_ADD,
                     REAL_HALF, FINITE_EMPTY] THEN
        REWRITE_TAC [IN_INSERT] THEN
        ASM_SIMP_TAC [← SET_RULE
         (← q r"~(a IN s) ==> ((w IN s UNION t ==> w = a \/ w IN t ==> P w) <=>
                         (w IN t ==> P w))")] THEN
        GEN_REWRITE_TAC id [EXTENSION] THEN
        REWRITE_TAC [IN_INTER, NOT_IN_EMPTY, IN_ELIM_THM] THEN
        X_GEN_TAC (← q r"y:real^N") THEN
        DISCH_THEN (CONJUNCTS_THEN2
         (X_CHOOSE_THEN (← q r"a:real")
           (CONJUNCTS_THEN2 ASSUME_TAC
             (X_CHOOSE_THEN (← q r"f:real^N->real") STRIP_ASSUME_TAC)))
         (X_CHOOSE_THEN (← q r"b:real")
           (CONJUNCTS_THEN2 ASSUME_TAC
             (X_CHOOSE_THEN (← q r"g:real^N->real") STRIP_ASSUME_TAC)))) THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [INDEPENDENT_EXPLICIT]) THEN
        REWRITE_TAC [FINITE_INSERT, FINITE_DELETE, FINITE_UNION] THEN
        DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
        DISCH_THEN (MP_TAC o SPEC
         (← q r"\x. if x = v then a + b else (f:real^N->real) x - g x")) THEN
        ASM_SIMP_TAC [VSUM_CLAUSES, FINITE_DELETE, FINITE_UNION] THEN
        ASM_REWRITE_TAC [IN_DELETE, IN_UNION] THEN
        REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL
         [ALL_TAC, DISCH_THEN (MP_TAC o SPEC (← q r"v:real^N")) THEN
          REWRITE_TAC [IN_INSERT] THEN ASM_REAL_ARITH_TAC] THEN
        ASM_SIMP_TAC [← SET_RULE
          (← q r"~(a IN t) ==> (s DELETE a) UNION t = (s UNION t) DELETE a")] THEN
        ASM_SIMP_TAC [VSUM_DELETE_CASES, FINITE_UNION, IN_UNION] THEN
        REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_SUB_RZERO] THEN
        SUBGOAL_THEN
         (← q r"!x:real^N. (if x = v then a + b else f x - g x) % x =
                     (if x = v then a else f x) % x -
                     (if x = v then --b else g x) % x")
         (fun th => REWRITE_TAC [th])
        THENL
         [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN VECTOR_ARITH_TAC,
          ASM_SIMP_TAC [VSUM_SUB, FINITE_UNION]] THEN
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC (← q r"(a + b) % v + (y - a % v) - (y - b % --v):real^N") THEN
        CONJ_TAC THENL [ALL_TAC, VECTOR_ARITH_TAC] THEN
        AP_TERM_TAC THEN BINOP_TAC THEN
        FIRST_X_ASSUM (fun th => tactic_of do
          pure (GEN_REWRITE_TAC RAND_CONV [← GSYM th])) THEN
        MATCH_MP_TAC VSUM_EQ THEN GEN_TAC THEN REWRITE_TAC [] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [IN_UNION],
        MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC (← q r"aff_gt s t :real^N->bool") THEN
        REWRITE_TAC [INTER_SUBSET] THEN
        MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC (← q r"affine hull (s UNION t:real^N->bool)") THEN
        REWRITE_TAC [AFF_GT_SUBSET_AFFINE_HULL] THEN
        ASM_SIMP_TAC [AFFINE_HULL_EQ_SPAN, IN_UNION, HULL_INC] THEN
        ONCE_REWRITE_TAC [← GSYM SPAN_DELETE_0] THEN
        MATCH_MP_TAC NEGLIGIBLE_LOWDIM THEN
        MATCH_MP_TAC LET_TRANS THEN
        EXISTS_TAC (← q r"CARD((s UNION t) DELETE (vec 0:real^N))") THEN
        ASM_SIMP_TAC [DIM_LE_CARD, FINITE_DELETE, FINITE_UNION, DIM_SPAN] THEN
        ASM_SIMP_TAC [CARD_DELETE, IN_UNION, FINITE_UNION] THEN
        MATCH_MP_TAC (← ARITH_RULE (← q r"1 <= n /\ x <= n ==> x - 1 < n")) THEN
        ASM_REWRITE_TAC [DIMINDEX_GE_1]]))

  let MEASURE_BALL_AFF_GT_SHUFFLE ← prove
   r"!r s t v:real^N.
          &0 <= r /\ ~(v IN (s UNION t)) /\
          independent(v INSERT (s UNION t))
          ==> measure(ball(vec 0,r) INTER aff_gt (vec 0 INSERT v INSERT s) t) =
              measure(ball(vec 0,r) INTER aff_gt (vec 0 INSERT s) (v INSERT t)) +
              measure(ball(vec 0,r) INTER
                      aff_gt (vec 0 INSERT s) (--v INSERT t))"
   (REWRITE_TAC [IN_UNION, DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"r:real", ← q r"(vec 0:real^N) INSERT s",
                   ← q r"t:real^N->bool", ← q r"v:real^N"]
          MEASURE_BALL_AFF_GT_SHUFFLE_LEMMA) THEN
    ANTS_TAC THENL [ALL_TAC, REWRITE_TAC [INSERT_AC]] THEN
    ASM_REWRITE_TAC [IN_INSERT, FINITE_INSERT] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP INDEPENDENT_NONZERO) THEN
    REWRITE_TAC [IN_INSERT, IN_UNION, DE_MORGAN_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP INDEPENDENT_BOUND) THEN
    REWRITE_TAC [FINITE_INSERT, FINITE_UNION] THEN
    DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [← SET_RULE (← q r"(a INSERT s) UNION t = a INSERT (s UNION t)")] THEN
    ASM_SIMP_TAC [CARD_CLAUSES, FINITE_UNION, IN_UNION, FINITE_INSERT] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC [VECTOR_NEG_EQ_0] THEN CONJ_TAC THENL
     [FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP
       (← REWRITE_RULE [IMP_CONJ] INDEPENDENT_MONO)) THEN
      SET_TAC [],
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [independent]) THEN
      REWRITE_TAC [dependent, CONTRAPOS_THM] THEN DISCH_TAC THEN
      EXISTS_TAC (← q r"v:real^N") THEN REWRITE_TAC [IN_INSERT] THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM VECTOR_NEG_NEG] THEN
      MATCH_MP_TAC SPAN_NEG THEN MATCH_MP_TAC SPAN_SUPERSET THEN
      ASM_REWRITE_TAC [IN_DELETE, ← VECTOR_ARITH (← q r"--v:real^N = v <=> v = vec 0"),
                      IN_INSERT, IN_UNION]])

  let MEASURE_LUNE_DECOMPOSITION ← (do
    let distinctpairs (l : List term) : List (term × term) :=
      (l.zip (List.range l.length)).flatMap
        (fun (x, i) => (l.drop (i + 1)).map (fun y => (x, y)))
    let mkEq ← ExceptT.mk (mk_eq : IO _)
    let eqs ← liftExcept ((distinctpairs
      [← q r"v3:real^3", ← q r"v2:real^3", ← q r"v1:real^3", ← q r"vec 0:real^3"]).mapM mkEq)
    prove
     r"!v1 v2 v3:real^3.
           &0 <= r /\ ~coplanar {vec 0, v1, v2, v3}
           ==> measure(ball(vec 0,r) INTER aff_gt {vec 0} {v1,v2,v3}) +
               measure(ball(vec 0,r) INTER aff_gt {vec 0} {--v1,v2,v3}) =
               dihV (vec 0) v1 v2 v3 * &2 * r pow 3 / &3"
      (REPEAT GEN_TAC THEN MAP_EVERY
       (fun t => ASM_CASES_TAC t THENL
        [ASM_REWRITE_TAC [INSERT_AC, COPLANAR_3], ALL_TAC])
       eqs THEN
      REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC [← GSYM (← REWRITE_RULE [HAS_MEASURE_MEASURABLE_MEASURE]
        HAS_MEASURE_LUNE_SIMPLE)] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MEASURE_BALL_AFF_GT_SHUFFLE THEN
      ASM_REWRITE_TAC [UNION_EMPTY, IN_INSERT, NOT_IN_EMPTY] THEN
      ASM_SIMP_TAC [NOT_COPLANAR_0_4_IMP_INDEPENDENT]))

  let SOLID_TRIANGLE_CONGRUENT_NEG ← prove
   r"!r v1 v2 v3:real^N.
          measure(ball(vec 0,r) INTER aff_gt {vec 0} {--v1, --v2, --v3}) =
          measure(ball(vec 0,r) INTER aff_gt {vec 0} {v1, v2, v3})"
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN
     (← q r"ball(vec 0:real^N,r) INTER aff_gt {vec 0} {--v1, --v2, --v3} =
      IMAGE (--)
            (ball(vec 0,r) INTER aff_gt {vec 0} {v1, v2, v3})")
    SUBST1_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC MEASURE_ORTHOGONAL_IMAGE_EQ THEN
      REWRITE_TAC [ORTHOGONAL_TRANSFORMATION, linear, NORM_NEG] THEN
      CONJ_TAC THEN VECTOR_ARITH_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    CONJ_TAC THENL [MESON_TAC [VECTOR_NEG_NEG], ALL_TAC] THEN
    REWRITE_TAC [IN_INTER, IN_BALL_0, NORM_NEG] THEN
    REWRITE_TAC [AFFSIGN_ALT, aff_gt_def, sgn_gt, IN_ELIM_THM] THEN
    REWRITE_TAC [← SET_RULE (← q r"{a} UNION {b,c,d} = {a,b,d,c}")] THEN
    REWRITE_TAC [← SET_RULE (← q r"x IN {a} <=> a = x")] THEN
    ASM_SIMP_TAC [FINITE_INSERT, FINITE_UNION, AFFINE_HULL_FINITE_STEP_GEN,
                 RIGHT_EXISTS_AND_THM, REAL_LT_ADD, REAL_HALF, FINITE_EMPTY] THEN
    ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
    REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_SUB_RZERO] THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"vec 0:real^N = --x <=> vec 0 = x")] THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"--x - a % --w:real^N = --(x - a % w)")] THEN
    REWRITE_TAC [VECTOR_NEG_EQ_0])

  let VOLUME_SOLID_TRIANGLE ← (do
    let insert_union ← SET_RULE (← q r"(a INSERT s) UNION t = a INSERT (s UNION t)")
    let tac (convl : term → Except String term) : tactic :=
      W (MP_TAC o PART_MATCH (lhs o rand) MEASURE_BALL_AFF_GT_SHUFFLE o
        convl o lhand o lhand o snd) THEN
      ASM_REWRITE_TAC [UNION_EMPTY, IN_INSERT, IN_UNION, NOT_IN_EMPTY] THEN
      REWRITE_TAC [insert_union] THEN
      ASM_SIMP_TAC [UNION_EMPTY, REAL_LT_IMP_LE] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [DISCH_THEN (HolCore.Tactics.STRIP_THM_THEN HolLight.HolBase.B SUBST_ALL_TAC) THEN
          RULE_ASSUM_TAC (REWRITE_RULE [INSERT_AC]) THEN
          RULE_ASSUM_TAC (REWRITE_RULE [COPLANAR_3]) THEN
          FIRST_ASSUM (HolCore.Tactics.CONTR_TAC HolLight.HolBase.B),
          MATCH_MP_TAC NOT_COPLANAR_0_4_IMP_INDEPENDENT THEN
          RULE_ASSUM_TAC (REWRITE_RULE [INSERT_AC]) THEN
          ASM_REWRITE_TAC [INSERT_AC]],
        DISCH_THEN SUBST1_TAC]
    let convls : List (term → Except String term) :=
      [(fun t => .ok t), lhand, rand,
       lhand o lhand, rand o lhand, lhand o rand, rand o rand]
    prove
     r"!r v0 v1 v2 v3:real^3.
         &0 < r /\ ~coplanar{v0, v1, v2, v3}
         ==> measure(ball(v0,r) INTER aff_gt {v0} {v1,v2,v3}) =
                  let a123 = dihV v0 v1 v2 v3 in
                  let a231 = dihV v0 v2 v3 v1 in
                  let a312 = dihV v0 v3 v1 v2 in
                    (a123 + a231 + a312 - pi) * r pow 3 / &3"
      (GEN_TAC THEN GEOM_ORIGIN_TAC (← q r"v0:real^3") THEN
      CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
        (← q r"measure(ball(vec 0:real^3,r) INTER aff_gt {vec 0,v1,v2,v3} {}) =
         &4 / &3 * pi * r pow 3")
      MP_TAC THENL
       [MP_TAC (← SPECL [← q r"vec 0:real^3", ← q r"r:real"] VOLUME_BALL) THEN
        ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN
        DISCH_THEN (SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
        MATCH_MP_TAC (← SET_RULE (← q r"t = UNIV ==> s INTER t = s")) THEN
        REWRITE_TAC [AFF_GT_EQ_AFFINE_HULL] THEN
        SIMP_TAC [AFFINE_HULL_EQ_SPAN, HULL_INC, IN_INSERT, SPAN_INSERT_0] THEN
        REWRITE_TAC [← SET_RULE (← q r"s = UNIV <=> UNIV SUBSET s")] THEN
        MATCH_MP_TAC CARD_GE_DIM_INDEPENDENT THEN
        ASM_SIMP_TAC [DIM_UNIV, DIMINDEX_3, SUBSET_UNIV] THEN
        ASM_SIMP_TAC [NOT_COPLANAR_0_4_IMP_INDEPENDENT] THEN
        SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY] THEN
        REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
        MAP_EVERY (fun t =>
          ASM_CASES_TAC t THENL
           [FIRST_X_ASSUM SUBST_ALL_TAC THEN
            RULE_ASSUM_TAC (REWRITE_RULE [INSERT_AC, COPLANAR_3]) THEN
            ASM_MESON_TAC [],
            ASM_REWRITE_TAC []])
         [← q r"v3:real^3 = v2", ← q r"v3:real^3 = v1", ← q r"v2:real^3 = v1"] THEN
        CONV_TAC NUM_REDUCE_CONV,
        ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"~(coplanar {vec 0:real^3,v1,v2,v3}) /\
        ~(coplanar {vec 0,--v1,v2,v3}) /\
        ~(coplanar {vec 0,v1,--v2,v3}) /\
        ~(coplanar {vec 0,--v1,--v2,v3}) /\
        ~(coplanar {vec 0,--v1,--v2,v3}) /\
        ~(coplanar {vec 0,--v1,v2,--v3}) /\
        ~(coplanar {vec 0,v1,--v2,--v3}) /\
        ~(coplanar {vec 0,--v1,--v2,--v3}) /\
        ~(coplanar {vec 0,--v1,--v2,--v3})")
      STRIP_ASSUME_TAC THENL
       [REPLICATE_TAC 3
         (REWRITE_TAC [COPLANAR_INSERT_0_NEG] THEN
          ONCE_REWRITE_TAC [← SET_RULE (← q r"{vec 0,a,b,c} = {vec 0,b,c,a}")]) THEN
        ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      MAP_EVERY tac convls THEN
      MP_TAC (← ISPECL [← q r"v1:real^3", ← q r"v2:real^3", ← q r"v3:real^3"]
        MEASURE_LUNE_DECOMPOSITION) THEN
      MP_TAC (← ISPECL [← q r"v2:real^3", ← q r"v3:real^3", ← q r"v1:real^3"]
        MEASURE_LUNE_DECOMPOSITION) THEN
      MP_TAC (← ISPECL [← q r"v3:real^3", ← q r"v1:real^3", ← q r"v2:real^3"]
        MEASURE_LUNE_DECOMPOSITION) THEN
      MP_TAC (← ISPECL [← q r"--v1:real^3", ← q r"--v2:real^3", ← q r"--v3:real^3"]
        MEASURE_LUNE_DECOMPOSITION) THEN
      MP_TAC (← ISPECL [← q r"--v2:real^3", ← q r"--v3:real^3", ← q r"--v1:real^3"]
        MEASURE_LUNE_DECOMPOSITION) THEN
      MP_TAC (← ISPECL [← q r"--v3:real^3", ← q r"--v1:real^3", ← q r"--v2:real^3"]
        MEASURE_LUNE_DECOMPOSITION) THEN
      ASM_REWRITE_TAC [VECTOR_NEG_NEG] THEN
      ASM_SIMP_TAC [REAL_LT_IMP_LE, INSERT_AC] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [INSERT_AC]) THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [DIHV_NEG_0] THEN
      REWRITE_TAC [SOLID_TRIANGLE_CONGRUENT_NEG] THEN
      REWRITE_TAC [INSERT_AC] THEN REAL_ARITH_TAC))

  pure { MEASURABLE_BALL_AFF_GT, AFF_GT_SHUFFLE, MEASURE_BALL_AFF_GT_SHUFFLE_LEMMA,
         MEASURE_BALL_AFF_GT_SHUFFLE, MEASURE_LUNE_DECOMPOSITION,
         SOLID_TRIANGLE_CONGRUENT_NEG, VOLUME_SOLID_TRIANGLE }
/- ------------------------------------------------------------------------- -/
/- Volume of wedge of a frustum.                                             -/
/- (flyspeck.ml 5972-6143)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FYU where
  MEASURABLE_BOUNDED_INTER_OPEN : thm
  SLICE_SPECIAL_WEDGE : thm
  VOLUME_FRUSTT_WEDGE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYU [HolBase] (D : FlyspeckDeps) (BFYA : FYA) (BFYI : FYI) (BFYM : FYM) (BFYO : FYO) (BFYP : FYP) (BFYR : FYR) : ExceptT String IO FYU := do
  -- @@SCOPE BEGIN
  let { COLLINEAR_BASIS_3, COLLINEAR_SPECIAL_SCALE, SLICE_123, SLICE_DROPOUT_3, .. } := BFYA
  let { AZIM_ARG, AZIM_SPECIAL_SCALE, .. } := BFYI
  let { wedge, WEDGE_SPECIAL_SCALE, .. } := BFYM
  let { OPEN_WEDGE, .. } := BFYO
  let { frustt, frustum, rcone_gt, rconesgn, VOLUME_FRUSTT_STRONG, .. } := BFYP
  let { HAS_MEASURE_OPEN_SECTOR_LT_GEN, .. } := BFYR
  let { let_CONV, .. } := D
  let { ASM_MESON_TAC, REAL_ARITH_TAC, REAL_RING, .. } := D.crd
  let { BOUNDED_SUBSET_OPEN_INTERVAL, .. } := D.qtopology
  let { GEOM_ORIGIN_TAC, .. } := D.geomorigin
  let { REAL_DIFF_TAC, .. } := D.gm.rzq
  let { HAS_REAL_INTEGRAL_EMPTY, HAS_REAL_INTEGRAL_EQ, .. } := D.gm.rzal
  let { REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS, .. } := D.gm.rzan
  let { HAS_REAL_INTEGRAL_RESTRICT_UNIV, .. } := D.gm.rzao
  let { HAS_REAL_INTEGRAL_OPEN_INTERVAL, .. } := D.gm.rzap
  let { SLICE_INTER, .. } := D.gm.rzaz
  let { FUBINI_SIMPLE_ALT, .. } := D.gm.rzbc
  let { DOT_3, .. } := D.gm.qvectors
  let { ARITH, CONJ_ASSOC, DIMINDEX_3, NORM_POS_LE, real_abs, REAL_LE_MUL, REAL_MUL_LZERO,
        REAL_POW_MUL, REAL_SUB_RZERO, VECTOR_3, .. } := D.crd.thms
  let { ARG_0, .. } := D.gm.ra.tsh
  let { DROPOUT_0, .. } := D.gm.ra.qvectors
  let { IN_REAL_INTERVAL, REAL_INTERVAL_EQ_EMPTY, .. } := D.gm.ra.qmisc
  let { HAS_MEASURE_MEASURABLE_MEASURE, MEASURABLE_EMPTY, MEASURABLE_INTER,
        MEASURABLE_OPEN, MEASURE_EMPTY, .. } := D.gm.ra.qmeasure
  let { complex_div, .. } := D.gm.ra.ts.cn.cxa
  let { COMPLEX_MUL_LZERO, .. } := D.gm.ra.ts.cn.cxb
  let { COMPLEX_VEC_0, .. } := D.gm.ra.ts.cn.cxc
  let { REAL_POW_1_LT, .. } := D.gm.ra.ts.cn.qsession
  let { GEOM_BASIS_MULTIPLE_TAC, NUM_REDUCE_CONV, REAL_ARITH, REAL_FIELD,
        REAL_RAT_REDUCE_CONV, SET_RULE, .. } := D.gm.ra.ts.cn.cx.cvx
  let { SQRT_POS_LT, .. } := D.gm.ra.ts.cn.cx.cpx
  let { COND_ID, COND_RAND, COND_RATOR, DIMINDEX_2, EMPTY_GSPEC, EQ_IMP, EXTENSION,
        .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { IN_DELETE, INSERT_AC, INTER, INTER_EMPTY, .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, LEFT_IMP_EXISTS_THM, NOT_IMP, NOT_IN_EMPTY, REAL_ABS_MUL,
        REAL_ABS_POS, .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_INV_1_LT, REAL_INV_POW, REAL_LE_LMUL, REAL_LE_LT, REAL_LE_MUL2,
        REAL_LE_MUL_EQ, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_INV_EQ, REAL_LT_LMUL_EQ,
        REAL_LT_MUL, REAL_LT_MUL_EQ, REAL_LT_RDIV_EQ, REAL_LT_REFL,
        .. } := D.gm.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_RID, REAL_MUL_RZERO, REAL_NOT_LE, REAL_NOT_LT, REAL_POS, REAL_POW_DIV,
        REAL_POW_LT, REAL_SUB_LT, SQRT_0, SQRT_POW_2, .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { real_div, real_gt, .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { BASIS_NONZERO, COLLINEAR_2, COMPONENT_LE_NORM, DIST_0, DOT_2, DOT_BASIS, DOT_RMUL,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec1
  let { NORM_BASIS, .. } := D.gm.ra.ts.cn.cx.cvx.vec2
  let { NORM_MUL, NORM_POS_LT, .. } := D.gm.ra.ts.cn.cx.cvx.vec3
  let { VEC_COMPONENT, VECTOR_MUL_EQ_0, VECTOR_MUL_LZERO, VECTOR_SUB_RZERO,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { IN_BALL_0, .. } := D.gm.ra.ts.cn.cx.cvx.top4
  let { OPEN_INTER, OPEN_INTERVAL, .. } := D.gm.ra.ts.cn.cx.cvx.top5
  let { NORM_LT_SQUARE, .. } := D.gm.ra.ts.cn.ms.ig.dv.qvec
  let { BOUNDED_INTER, BOUNDED_INTERVAL, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qtop
  -- @@SCOPE END

  let MEASURABLE_BOUNDED_INTER_OPEN ← prove
   r"!s t:real^N->bool.
         measurable s /\ bounded s /\ open t ==> measurable(s INTER t)"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP BOUNDED_SUBSET_OPEN_INTERVAL) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"b:real^N"] THEN
    DISCH_THEN (SUBST1_TAC o MATCH_MP (← SET_RULE
     (← q r"s SUBSET i ==> s INTER t = s INTER (t INTER i)"))) THEN
    MATCH_MP_TAC MEASURABLE_INTER THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC MEASURABLE_OPEN THEN
    ASM_SIMP_TAC [OPEN_INTER, OPEN_INTERVAL, BOUNDED_INTER, BOUNDED_INTERVAL])

  let SLICE_SPECIAL_WEDGE ← prove
   r"!w1 w2.
          ~collinear {vec 0, basis 3, w1} /\ ~collinear {vec 0, basis 3, w2}
          ==> slice 3 t (wedge (vec 0) (basis 3) w1 w2) =
              {z | &0 < Arg(z / dropout 3 w1) /\
                   Arg(z / dropout 3 w1) < Arg(dropout 3 w2 / dropout 3 w1)}"
   (REWRITE_TAC [wedge] THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"~a /\ b /\ c <=> ~(~a ==> ~(b /\ c))")] THEN
    ASM_SIMP_TAC [AZIM_ARG] THEN REWRITE_TAC [COLLINEAR_BASIS_3] THEN
    REWRITE_TAC [NOT_IMP, ← GSYM CONJ_ASSOC, DROPOUT_0] THEN
    MAP_EVERY ABBREV_TAC
     [← q r"v1:real^2 = dropout 3 (w1:real^3)",
      ← q r"v2:real^2 = dropout 3 (w2:real^3)"] THEN
    REWRITE_TAC [SLICE_DROPOUT_3, VEC_COMPONENT, REAL_SUB_RZERO] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM, COMPLEX_VEC_0] THEN
    X_GEN_TAC (← q r"w:complex") THEN
    ASM_CASES_TAC (← q r"w = Cx(&0)") THEN ASM_REWRITE_TAC [] THEN
    ASM_REWRITE_TAC [complex_div, COMPLEX_MUL_LZERO, ARG_0, REAL_LT_REFL])

  let VOLUME_FRUSTT_WEDGE ← prove
   r"!v0 v1:real^3 w1 w2 h a.
         &0 < a /\ ~collinear {v0,v1,w1} /\ ~collinear {v0,v1,w2}
         ==> bounded(frustt v0 v1 h a INTER wedge v0 v1 w1 w2) /\
             measurable(frustt v0 v1 h a INTER wedge v0 v1 w1 w2) /\
             measure(frustt v0 v1 h a INTER wedge v0 v1 w1 w2) =
             if &1 <= a \/ h < &0 then &0
             else azim v0 v1 w1 w2 * ((h / a) pow 2 - h pow 2) * h / &6"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"v1:real^3 = v0") THENL
     [ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2], STRIP_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ b /\ (a /\ b ==> c) ==> a /\ b /\ c")) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_INTER THEN ASM_SIMP_TAC [VOLUME_FRUSTT_STRONG],
      MATCH_MP_TAC MEASURABLE_BOUNDED_INTER_OPEN THEN
      ASM_SIMP_TAC [VOLUME_FRUSTT_STRONG, OPEN_WEDGE],
      ALL_TAC] THEN
    REWRITE_TAC [frustt, frustum, rcone_gt, rconesgn, IN_ELIM_THM] THEN
    CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist CONJ) THEN
    GEOM_ORIGIN_TAC (← q r"v0:real^3") THEN
    REWRITE_TAC [VECTOR_SUB_RZERO, REAL_MUL_LZERO, DIST_0, real_gt] THEN
    GEOM_BASIS_MULTIPLE_TAC 3 (← q r"v1:real^3") THEN
    X_GEN_TAC (← q r"b:real") THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
    ASM_CASES_TAC (← q r"b = &0") THEN ASM_REWRITE_TAC [VECTOR_MUL_LZERO] THEN
    ASM_SIMP_TAC [COLLINEAR_SPECIAL_SCALE, WEDGE_SPECIAL_SCALE] THEN
    ASM_REWRITE_TAC [VECTOR_MUL_EQ_0] THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_CASES_TAC (← q r"&1 <= a") THEN ASM_REWRITE_TAC [] THENL
     [SUBGOAL_THEN
       (← q r"!y:real^3. ~(norm(y) * norm(b % basis 3:real^3) * a
                     < y dot (b % basis 3))")
       (fun th => REWRITE_TAC [th, EMPTY_GSPEC, MEASURABLE_EMPTY,
                      INTER_EMPTY, MEASURE_EMPTY]) THEN
      REWRITE_TAC [REAL_NOT_LT] THEN X_GEN_TAC (← q r"y:real^3") THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"abs(x) <= a ==> x <= a")) THEN
      SIMP_TAC [DOT_RMUL, NORM_MUL, REAL_ABS_MUL, DOT_BASIS, NORM_BASIS,
               DIMINDEX_3, ARITH] THEN
      REWRITE_TAC [← REAL_ARITH
       (← q r"b * y <= n * (b * &1) * a <=> b * &1 * y <= b * a * n")] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC [REAL_POS, REAL_ABS_POS, COMPONENT_LE_NORM, DIMINDEX_3, ARITH],
      ALL_TAC] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [REAL_NOT_LE]) THEN
    SIMP_TAC [NORM_MUL, NORM_BASIS, DOT_BASIS, DOT_RMUL, DIMINDEX_3, ARITH] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"n * x * a:real = x * n * a")] THEN
    ASM_REWRITE_TAC [real_abs, REAL_MUL_RID] THEN
    ASM_SIMP_TAC [REAL_MUL_RID, REAL_LT_LMUL_EQ, REAL_LT_MUL_EQ, NORM_POS_LT] THEN
    ASM_SIMP_TAC [VECTOR_MUL_EQ_0, BASIS_NONZERO, DIMINDEX_3, ARITH,
                 REAL_LT_IMP_NZ] THEN
    ASM_SIMP_TAC [← GSYM REAL_LT_RDIV_EQ, NORM_LT_SQUARE] THEN
    ASM_SIMP_TAC [REAL_POW_DIV, REAL_POW_LT, REAL_LT_RDIV_EQ] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"(&0 * x < y /\ u < v) /\ &0 < y /\ y < h <=>
                            &0 < y /\ y < h /\ u < v")] THEN
    DISCH_TAC THEN MATCH_MP_TAC (← HolLight.INST_TYPE [(← qty "2", ← qty "M")] FUBINI_SIMPLE_ALT) THEN
    EXISTS_TAC (← q r"3") THEN ASM_REWRITE_TAC [DIMINDEX_2, DIMINDEX_3, ARITH] THEN
    ASM_SIMP_TAC [WEDGE_SPECIAL_SCALE, REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC [REAL_LT_LMUL_EQ, SLICE_INTER, DIMINDEX_2,
                 DIMINDEX_3, ARITH] THEN
    SUBGOAL_THEN
     (← q r"!t. slice 3 t {y:real^3 | norm y * a < y$3 /\ &0 < y$3 /\ y$3 < h} =
          if t < h
          then ball(vec 0:real^2,sqrt(inv(a pow 2) - &1) * t)
          else {}")
     (fun th => ASM_SIMP_TAC [th, SLICE_SPECIAL_WEDGE])
    THENL
     [REWRITE_TAC [EXTENSION] THEN
      MAP_EVERY X_GEN_TAC [← q r"t:real", ← q r"z:real^2"] THEN
      SIMP_TAC [SLICE_123, DIMINDEX_2, DIMINDEX_3, ARITH, IN_ELIM_THM,
               VECTOR_3, DOT_3, ← GSYM DOT_2] THEN
      ASM_CASES_TAC (← q r"t < h") THEN ASM_REWRITE_TAC [NOT_IN_EMPTY] THEN
      REWRITE_TAC [IN_BALL_0, IN_DELETE] THEN
      MATCH_MP_TAC (← REAL_ARITH
       (← q r"&0 <= a /\ (a < t <=> u < v) ==> (a < t /\ &0 < t <=> u < v)")) THEN
      ASM_SIMP_TAC [REAL_LE_MUL, NORM_POS_LE, REAL_LT_IMP_LE] THEN
      ASM_SIMP_TAC [← GSYM REAL_LT_RDIV_EQ, NORM_LT_SQUARE] THEN
      SUBGOAL_THEN (← q r"&0 < inv(a pow 2) - &1") ASSUME_TAC THENL
       [REWRITE_TAC [REAL_SUB_LT] THEN MATCH_MP_TAC REAL_INV_1_LT THEN
        ASM_SIMP_TAC [REAL_POW_1_LT, REAL_LT_IMP_LE, ARITH, REAL_POW_LT],
        ALL_TAC] THEN
      ASM_SIMP_TAC [REAL_LT_MUL, SQRT_POS_LT, REAL_POW_MUL, SQRT_POW_2,
                   REAL_LT_IMP_LE, REAL_LT_MUL_EQ] THEN
      ASM_SIMP_TAC [real_div, REAL_LT_MUL_EQ, REAL_LT_INV_EQ] THEN
      ASM_CASES_TAC (← q r"&0 < t") THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [DOT_3, DOT_2, VECTOR_3, REAL_INV_POW] THEN
      REAL_ARITH_TAC,
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [COND_RATOR, COND_RAND] THEN
    GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o LAND_CONV o TOP_DEPTH_CONV)
     [COND_RATOR, COND_RAND] THEN
    REWRITE_TAC [INTER_EMPTY, MEASURABLE_EMPTY, MEASURE_EMPTY] THEN
    REWRITE_TAC [INTER, IN_BALL_0, IN_ELIM_THM] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [COLLINEAR_BASIS_3]) THEN
    ASM_SIMP_TAC [← REWRITE_RULE [HAS_MEASURE_MEASURABLE_MEASURE]
                   HAS_MEASURE_OPEN_SECTOR_LT_GEN] THEN
    REWRITE_TAC [COND_ID] THEN
    SUBGOAL_THEN (← q r"&0 < inv(a pow 2) - &1") ASSUME_TAC THENL
     [REWRITE_TAC [REAL_SUB_LT] THEN MATCH_MP_TAC REAL_INV_1_LT THEN
      ASM_SIMP_TAC [REAL_POW_1_LT, REAL_LT_IMP_LE, ARITH, REAL_POW_LT],
      ALL_TAC] THEN
    ASM_SIMP_TAC [REAL_LE_MUL_EQ, SQRT_POS_LT] THEN
    ASM_SIMP_TAC [AZIM_SPECIAL_SCALE, AZIM_ARG, COLLINEAR_BASIS_3] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
    EXISTS_TAC
     (← q r"\t. if &0 < t /\ t < h
          then Arg(dropout 3 (w2:real^3) / dropout 3 (w1:real^3)) / &2 *
               (inv(a pow 2) - &1) * t pow 2
          else &0") THEN
    CONJ_TAC THENL
     [X_GEN_TAC (← q r"t:real") THEN DISCH_TAC THEN REWRITE_TAC [] THEN
      ASM_CASES_TAC (← q r"t < h") THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"&0 <= t <=> t = &0 \/ &0 < t")] THEN
      ASM_CASES_TAC (← q r"t = &0") THEN
      ASM_REWRITE_TAC [REAL_LT_REFL, REAL_MUL_RZERO, SQRT_0] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [REAL_MUL_RZERO] THEN
      ASM_SIMP_TAC [REAL_POW_MUL, SQRT_POW_2, REAL_LT_IMP_LE] THEN
      REAL_ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [← GSYM IN_REAL_INTERVAL, HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
    REWRITE_TAC [HAS_REAL_INTEGRAL_OPEN_INTERVAL] THEN
    COND_CASES_TAC THENL
     [ASM_MESON_TAC [REAL_INTERVAL_EQ_EMPTY, HAS_REAL_INTEGRAL_EMPTY],
      RULE_ASSUM_TAC (REWRITE_RULE [REAL_NOT_LT])] THEN
    ABBREV_TAC (← q r"g = Arg(dropout 3 (w2:real^3) / dropout 3 (w1:real^3))") THEN
    MP_TAC (← ISPECL
     [← q r"\t. g / &6 * (inv (a pow 2) - &1) * t pow 3",
      ← q r"\t. g / &2 * (inv (a pow 2) - &1) * t pow 2",
      ← q r"&0", ← q r"h:real"] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING,
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC (← q r"&0 < a") THEN CONV_TAC REAL_FIELD])

  pure { MEASURABLE_BOUNDED_INTER_OPEN, SLICE_SPECIAL_WEDGE, VOLUME_FRUSTT_WEDGE }
/- ------------------------------------------------------------------------- -/
/- Wedge of a conic cap.                                                     -/
/- (flyspeck.ml 6144-6544)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FYV where
  VOLUME_CONIC_CAP_WEDGE_WEAK : thm
  BOUNDED_CONIC_CAP_WEDGE : thm
  MEASURABLE_CONIC_CAP_WEDGE : thm
  VOLUME_CONIC_CAP_COMPL : thm
  VOLUME_CONIC_CAP_WEDGE_MEDIUM : thm
  VOLUME_CONIC_CAP_WEDGE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYV [HolBase] (D : FlyspeckDeps) (BFYA : FYA) (BFYI : FYI) (BFYM : FYM) (BFYO : FYO) (BFYP : FYP) (BFYQ : FYQ) (BFYR : FYR) (BFYS : FYS) (BFYU : FYU) : ExceptT String IO FYV := do
  -- @@SCOPE BEGIN
  let { COLLINEAR_BASIS_3, COLLINEAR_SPECIAL_SCALE, SLICE_123, .. } := BFYA
  let { AZIM_ARG, AZIM_DEGENERATE, AZIM_SPECIAL_SCALE, .. } := BFYI
  let { wedge, WEDGE_DEGENERATE, WEDGE_SPECIAL_SCALE, .. } := BFYM
  let { OPEN_WEDGE, .. } := BFYO
  let { rcone_eq, rcone_gt, rconesgn, .. } := BFYP
  let { BOUNDED_CONIC_CAP, conic_cap, MEASURABLE_CONIC_CAP, normball, NORMBALL_BALL,
        VOLUME_CONIC_CAP_STRONG, .. } := BFYQ
  let { HAS_MEASURE_OPEN_SECTOR_LT_GEN, NEGLIGIBLE_RCONE_EQ, .. } := BFYR
  let { MEASURABLE_BALL_WEDGE, VOLUME_BALL_WEDGE, .. } := BFYS
  let { MEASURABLE_BOUNDED_INTER_OPEN, SLICE_SPECIAL_WEDGE, .. } := BFYU
  let { let_CONV, .. } := D
  let { ASM_MESON_TAC, MESON_TAC, REAL_ARITH_TAC, REAL_RING, .. } := D.crd
  let { MEASURABLE_LINEAR_IMAGE, MEASURE_DISJOINT_UNION, MEASURE_NEGLIGIBLE_SYMDIFF,
        MEASURE_ORTHOGONAL_IMAGE_EQ, .. } := D.qmeasure
  let { ORTHOGONAL_TRANSFORMATION_SURJECTIVE, .. } := D.qdeterminants
  let { ball, .. } := D.qtopology
  let { GEOM_ORIGIN_TAC, .. } := D.geomorigin
  let { REAL_DIFF_TAC, .. } := D.gm.rzq
  let { HAS_REAL_INTEGRAL_EQ, .. } := D.gm.rzal
  let { HAS_REAL_INTEGRAL_COMBINE, REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS, .. } := D.gm.rzan
  let { HAS_REAL_INTEGRAL_RESTRICT_UNIV, .. } := D.gm.rzao
  let { HAS_REAL_INTEGRAL_OPEN_INTERVAL, .. } := D.gm.rzap
  let { SLICE_INTER, .. } := D.gm.rzaz
  let { FUBINI_SIMPLE_ALT, .. } := D.gm.rzbc
  let { DOT_3, .. } := D.gm.qvectors
  let { ARITH, CART_EQ, DIMINDEX_3, FORALL_3, LAMBDA_BETA, linear, NORM_POS_LE, NORM_POW_2,
        ORTHOGONAL_TRANSFORMATION, ORTHOGONAL_TRANSFORMATION_LINEAR, real_abs, REAL_LE_MUL,
        REAL_MUL_LZERO, REAL_POW_MUL, VECTOR_3, VECTOR_MUL_COMPONENT, .. } := D.crd.thms
  let { dropout, .. } := D.gm.ra.qvectors
  let { IN_REAL_INTERVAL, .. } := D.gm.ra.qmisc
  let { HAS_MEASURE_MEASURABLE_MEASURE, MEASURABLE_EMPTY, MEASURE_EMPTY,
        .. } := D.gm.ra.qmeasure
  let { REAL_POW_LT2, .. } := D.gm.ra.ts.qsession
  let { REAL_POW_1_LT, .. } := D.gm.ra.ts.cn.qsession
  let { NEGLIGIBLE_SUBSET, .. } := D.gm.ra.ts.cn.ms.qintegration3
  let { REAL_POW_LE2_REV, .. } := D.gm.ra.ts.cn.ms.qsession
  let { ASM_REAL_ARITH_TAC, GEOM_BASIS_MULTIPLE_TAC, NORM_ARITH, NUM_REDUCE_CONV,
        REAL_ARITH, REAL_FIELD, REAL_RAT_REDUCE_CONV, SET_RULE, SET_TAC,
        .. } := D.gm.ra.ts.cn.cx.cvx
  let { FORALL_2, REAL_LE_SQUARE, SQRT_POS_LT, vector_norm, .. } := D.gm.ra.ts.cn.cx.cpx
  let { COND_ID, COND_RAND, COND_RATOR, DE_MORGAN_THM, DIMINDEX_2, DISJOINT, EMPTY_GSPEC,
        EQ_IMP, EQ_TRANS, EXTENSION, .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { IMP_CONJ, IN_DIFF, INSERT_AC, INTER, INTER_EMPTY, .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_INTER, IN_UNION, NOT_IN_EMPTY, REAL_ABS_MUL, REAL_ABS_NEG,
        REAL_ABS_POS, .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_INV_1_LT, REAL_INV_POW, REAL_LE_LDIV_EQ, REAL_LE_LMUL, REAL_LE_LT,
        REAL_LE_MIN, REAL_LE_MUL2, REAL_LE_RDIV_EQ, REAL_LE_SQUARE_ABS, REAL_LE_TRANS,
        REAL_LT_ANTISYM, REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, REAL_LT_LMUL_EQ,
        REAL_LT_MIN, REAL_LT_MUL, REAL_LT_MUL_EQ, REAL_LT_RDIV_EQ,
        .. } := D.gm.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_RID, REAL_NEG_0, REAL_NOT_LE, REAL_NOT_LT, REAL_POS,
        REAL_POW_2, REAL_POW_DIV, REAL_POW_LE2, REAL_POW_LT, REAL_SUB_LE, REAL_SUB_LT,
        SQRT_POS_LE, SQRT_POW_2, SUBSET, .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { real_div, real_gt, SURJECTIVE_IMAGE_EQ, .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { BASIS_NONZERO, COLLINEAR_2, COMPONENT_LE_NORM, DIST_0, DIST_SYM, DOT_2, DOT_BASIS,
        DOT_RMUL, .. } := D.gm.ra.ts.cn.cx.cvx.vec1
  let { NORM_BASIS, NORM_EQ, .. } := D.gm.ra.ts.cn.cx.cvx.vec2
  let { NORM_MUL, NORM_POS_LT, REAL_ABS_NORM, .. } := D.gm.ra.ts.cn.cx.cvx.vec3
  let { VECTOR_ADD_COMPONENT, VECTOR_MUL_EQ_0, VECTOR_MUL_LZERO, VECTOR_SUB_RZERO,
        .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { BALL_EQ_EMPTY, BOUNDED_EMPTY, BOUNDED_SUBSET, .. } := D.gm.ra.ts.cn.cx.cvx.top1
  let { IN_BALL_0, .. } := D.gm.ra.ts.cn.cx.cvx.top4
  let { NORM_LT_SQUARE, .. } := D.gm.ra.ts.cn.ms.ig.dv.qvec
  let { BOUNDED_INTER, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qtop
  let { CONVEX_EMPTY, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qcvx2
  -- @@SCOPE END

  let VOLUME_CONIC_CAP_WEDGE_WEAK ← prove
   r"!v0 v1:real^3 w1 w2 r a.
         &0 < a /\ ~collinear {v0,v1,w1} /\ ~collinear {v0,v1,w2}
         ==> bounded(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) /\
             measurable(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) /\
             measure(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) =
             if &1 <= a \/ r < &0 then &0
             else azim v0 v1 w1 w2 / &3 * (&1 - a) * r pow 3"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"v1:real^3 = v0") THENL
     [ASM_REWRITE_TAC [COLLINEAR_2, INSERT_AC], STRIP_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ b /\ (a /\ b ==> c) ==> a /\ b /\ c")) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_INTER THEN ASM_SIMP_TAC [VOLUME_CONIC_CAP_STRONG],
      MATCH_MP_TAC MEASURABLE_BOUNDED_INTER_OPEN THEN
      ASM_SIMP_TAC [VOLUME_CONIC_CAP_STRONG, OPEN_WEDGE],
      ALL_TAC] THEN
    REWRITE_TAC [conic_cap, rcone_gt, rconesgn, IN_ELIM_THM] THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [DIST_SYM] normball, ← GSYM ball] THEN
    CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist CONJ) THEN
    GEOM_ORIGIN_TAC (← q r"v0:real^3") THEN
    REWRITE_TAC [VECTOR_SUB_RZERO, REAL_MUL_LZERO, DIST_0, real_gt] THEN
    GEOM_BASIS_MULTIPLE_TAC 3 (← q r"v1:real^3") THEN
    X_GEN_TAC (← q r"b:real") THEN
    ASM_CASES_TAC (← q r"b = &0") THEN ASM_REWRITE_TAC [VECTOR_MUL_LZERO] THEN
    SIMP_TAC [COLLINEAR_SPECIAL_SCALE, WEDGE_SPECIAL_SCALE] THEN
    ASM_REWRITE_TAC [VECTOR_MUL_EQ_0] THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_CASES_TAC (← q r"&1 <= a") THEN ASM_REWRITE_TAC [] THENL
     [SUBGOAL_THEN
       (← q r"!y:real^3. ~(norm(y) * norm(b % basis 3:real^3) * a
                     < y dot (b % basis 3))")
       (fun th => REWRITE_TAC [th, EMPTY_GSPEC, INTER_EMPTY, MEASURE_EMPTY,
                           MEASURABLE_EMPTY, BOUNDED_EMPTY, CONVEX_EMPTY]) THEN
      REWRITE_TAC [REAL_NOT_LT] THEN X_GEN_TAC (← q r"y:real^3") THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"abs(x) <= a ==> x <= a")) THEN
      SIMP_TAC [DOT_RMUL, NORM_MUL, REAL_ABS_MUL, DOT_BASIS, NORM_BASIS,
               DIMINDEX_3, ARITH] THEN
      REWRITE_TAC [← REAL_ARITH
       (← q r"b * y <= n * (b * &1) * a <=> b * &1 * y <= b * a * n")] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC [REAL_POS, REAL_ABS_POS, COMPONENT_LE_NORM, DIMINDEX_3, ARITH],
      ALL_TAC] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [REAL_NOT_LE]) THEN
    SIMP_TAC [DOT_RMUL, NORM_MUL, REAL_ABS_NORM, DOT_BASIS,
             DIMINDEX_3, ARITH, NORM_BASIS] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"n * x * a:real = x * n * a")] THEN
    ASM_REWRITE_TAC [real_abs, REAL_MUL_RID] THEN
    ASM_SIMP_TAC [REAL_MUL_RID, REAL_LT_LMUL_EQ, REAL_LT_MUL_EQ, NORM_POS_LT] THEN
    ASM_SIMP_TAC [← GSYM REAL_LT_RDIV_EQ, NORM_LT_SQUARE] THEN
    ASM_SIMP_TAC [REAL_POW_DIV, REAL_POW_LT, REAL_LT_RDIV_EQ] THEN
    REWRITE_TAC [INTER, REAL_MUL_LZERO, IN_BALL_0, IN_ELIM_THM] THEN
    ASM_SIMP_TAC [VECTOR_MUL_EQ_0, BASIS_NONZERO, DIMINDEX_3, ARITH,
                 REAL_LT_IMP_NZ] THEN
    COND_CASES_TAC THENL
     [ASM_SIMP_TAC [← NORM_ARITH (← q r"r < &0 ==> ~(norm x < r)")] THEN
      REWRITE_TAC [EMPTY_GSPEC, MEASURE_EMPTY, MEASURABLE_EMPTY,
                  BOUNDED_EMPTY, CONVEX_EMPTY],
      RULE_ASSUM_TAC (ONCE_REWRITE_RULE [REAL_NOT_LT])] THEN
    STRIP_TAC THEN MATCH_MP_TAC (← HolLight.INST_TYPE [(← qty "2", ← qty "M")] FUBINI_SIMPLE_ALT) THEN
    EXISTS_TAC (← q r"3") THEN ASM_REWRITE_TAC [DIMINDEX_2, DIMINDEX_3, ARITH] THEN
    SUBGOAL_THEN (← q r"&0 < b") ASSUME_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    ASM_SIMP_TAC [WEDGE_SPECIAL_SCALE, AZIM_SPECIAL_SCALE] THEN
    ONCE_REWRITE_TAC [← SET_RULE (← q r"{x | P x /\ x IN s} = {x | P x} INTER s")] THEN
    ASM_SIMP_TAC [REAL_LT_LMUL_EQ, SLICE_INTER, DIMINDEX_2,
                 DIMINDEX_3, ARITH] THEN
    RULE_ASSUM_TAC
     (REWRITE_RULE [← MATCH_MP COLLINEAR_SPECIAL_SCALE (← ASSUME (← q r"~(b = &0)"))]) THEN
    SUBGOAL_THEN (← q r"&0 < inv(a pow 2) - &1") ASSUME_TAC THENL
     [REWRITE_TAC [REAL_SUB_LT] THEN MATCH_MP_TAC REAL_INV_1_LT THEN
      ASM_SIMP_TAC [REAL_POW_1_LT, REAL_LT_IMP_LE, ARITH, REAL_POW_LT],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!t. slice 3 t {y:real^3 | norm y < r /\ norm y * a < y$3} =
          if &0 < t /\ t < r
          then ball(vec 0:real^2,min (sqrt(r pow 2 - t pow 2))
                                     (t * sqrt(inv(a pow 2) - &1)))
          else {}")
     (fun th => ASM_SIMP_TAC [th, SLICE_SPECIAL_WEDGE])
    THENL
     [REWRITE_TAC [EXTENSION] THEN
      MAP_EVERY X_GEN_TAC [← q r"t:real", ← q r"z:real^2"] THEN
      SIMP_TAC [SLICE_123, DIMINDEX_2, DIMINDEX_3, ARITH, IN_ELIM_THM,
               VECTOR_3, DOT_3, ← GSYM DOT_2] THEN
      ASM_CASES_TAC (← q r"&0 < t") THEN ASM_REWRITE_TAC [] THENL
       [ALL_TAC,
        REWRITE_TAC [NOT_IN_EMPTY, DE_MORGAN_THM] THEN DISJ2_TAC THEN
        FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REAL_ARITH
         (← q r"~(&0 < t) ==> &0 <= a ==> ~(a < t)"))) THEN
        ASM_SIMP_TAC [REAL_LE_MUL, NORM_POS_LE, REAL_LT_IMP_LE]] THEN
      ASM_CASES_TAC (← q r"t < r") THEN ASM_REWRITE_TAC [] THENL
       [ALL_TAC,
        REWRITE_TAC [NOT_IN_EMPTY, DE_MORGAN_THM] THEN DISJ1_TAC THEN
        REWRITE_TAC [NORM_LT_SQUARE, DE_MORGAN_THM] THEN DISJ2_TAC THEN
        REWRITE_TAC [DOT_3, VECTOR_3] THEN
        MATCH_MP_TAC (← REAL_ARITH
         (← q r"r <= t /\ &0 <= a /\ &0 <= b ==> ~(a + b + t < r)")) THEN
        REWRITE_TAC [REAL_LE_SQUARE, REAL_POW_2] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC] THEN
      REWRITE_TAC [IN_BALL_0, REAL_LT_MIN] THEN
      ASM_SIMP_TAC [← GSYM REAL_LT_RDIV_EQ] THEN REWRITE_TAC [NORM_LT_SQUARE] THEN
      SUBGOAL_THEN (← q r"&0 < r") ASSUME_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
      SUBGOAL_THEN (← q r"t pow 2 < r pow 2") ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC [ARITH] THEN
        ASM_REAL_ARITH_TAC,
        ALL_TAC] THEN
      ASM_SIMP_TAC [REAL_LT_DIV, SQRT_POS_LT, REAL_LT_MUL, REAL_SUB_LT,
                   SQRT_POW_2, REAL_LT_IMP_LE, REAL_POW_MUL] THEN
      REWRITE_TAC [DOT_2, DOT_3, VECTOR_3] THEN
      ONCE_REWRITE_TAC [← REAL_ARITH (← q r"a + b + c < d <=> a + b < d - c")] THEN
      BINOP_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC (← q r"&0 < a") THEN CONV_TAC REAL_FIELD,
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [COND_RATOR, COND_RAND] THEN
    GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o LAND_CONV o TOP_DEPTH_CONV)
     [COND_RATOR, COND_RAND] THEN
    REWRITE_TAC [INTER_EMPTY, MEASURABLE_EMPTY, MEASURE_EMPTY] THEN
    REWRITE_TAC [INTER, IN_BALL_0, IN_ELIM_THM] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [COLLINEAR_BASIS_3]) THEN
    ASM_SIMP_TAC [← REWRITE_RULE [HAS_MEASURE_MEASURABLE_MEASURE]
                   HAS_MEASURE_OPEN_SECTOR_LT_GEN] THEN
    REWRITE_TAC [COND_ID] THEN
    ASM_SIMP_TAC [REAL_LE_MIN, SQRT_POS_LE, REAL_LT_IMP_LE, REAL_LE_MUL,
                 REAL_POW_LE2, ARITH, REAL_SUB_LE, REAL_LT_MUL, SQRT_POS_LT] THEN
    REWRITE_TAC [← GSYM IN_REAL_INTERVAL, HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
    REWRITE_TAC [HAS_REAL_INTEGRAL_OPEN_INTERVAL] THEN
    REWRITE_TAC [NORM_POW_2, DOT_3, VECTOR_3, DOT_2] THEN
    ASM_SIMP_TAC [AZIM_ARG, COLLINEAR_BASIS_3] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH
     (← q r"(&1 - a) * az / &3 * r pow 3 =
      az / &6 * (inv (a pow 2) - &1) * (a * r) pow 3 +
      (az * &1 / &3 * (&1 - a) * r pow 3 -
       az / &6 * (inv (a pow 2) - &1) * (a * r) pow 3)")] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_COMBINE THEN
    EXISTS_TAC (← q r"a * r:real") THEN
    REWRITE_TAC [← REAL_ARITH (← q r"a * r <= r <=> &0 <= r * (&1 - a)")] THEN
    ASM_SIMP_TAC [REAL_LE_MUL, REAL_SUB_LE, REAL_LT_IMP_LE] THEN
    ABBREV_TAC (← q r"k = Arg(dropout 3 (w2:real^3) / dropout 3 (w1:real^3))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN EXISTS_TAC
       (← q r"\t. k * t pow 2 * (inv(a pow 2) - &1) / &2") THEN
      CONJ_TAC THENL
       [X_GEN_TAC (← q r"t:real") THEN REWRITE_TAC [IN_REAL_INTERVAL] THEN
        STRIP_TAC THEN AP_TERM_TAC THEN
        SUBGOAL_THEN (← q r"t pow 2 * (inv(a pow 2) - &1) <= r pow 2 - t pow 2")
        ASSUME_TAC THENL
         [REWRITE_TAC [← REAL_ARITH (← q r"t * (a - &1) <= r - t <=> t * a <= r")] THEN
          ASM_SIMP_TAC [← GSYM real_div, REAL_LE_LDIV_EQ, REAL_POW_LT] THEN
          REWRITE_TAC [← GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
          ASM_REAL_ARITH_TAC,
          ALL_TAC] THEN
        SUBGOAL_THEN (← q r"t * sqrt(inv(a pow 2) - &1) <= sqrt(r pow 2 - t pow 2)")
          (fun th => tactic_of do pure (SIMP_TAC [th, ← REAL_ARITH (← q r"a <= b ==> min b a = a")]))
        THENL
         [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC (← q r"2") THEN
          REWRITE_TAC [ARITH] THEN
          SUBGOAL_THEN (← q r"&0 <= r pow 2 - t pow 2") ASSUME_TAC THENL
           [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REAL_ARITH
             (← q r"a <= x ==> &0 <= a ==> &0 <= x"))) THEN
            ASM_SIMP_TAC [REAL_POW_2, REAL_LE_MUL, REAL_LE_SQUARE, REAL_LT_IMP_LE],
            ASM_SIMP_TAC [SQRT_POS_LE, REAL_POW_MUL, SQRT_POW_2,
                         REAL_LT_IMP_LE]],
          ASM_SIMP_TAC [REAL_POW_MUL, SQRT_POW_2, SQRT_POW_2, REAL_LT_IMP_LE] THEN
          REAL_ARITH_TAC],
        MP_TAC (← ISPECL
         [← q r"\t. k / &6 * (inv (a pow 2) - &1) * t pow 3",
          ← q r"\t. k * t pow 2 * (inv (a pow 2) - &1) / &2",
          ← q r"&0", ← q r"a * r:real"] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
        ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_IMP_LE] THEN ANTS_TAC THENL
         [ASM_REWRITE_TAC [] THEN
          REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
          CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING,
          MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          UNDISCH_TAC (← q r"&0 < a") THEN CONV_TAC REAL_FIELD]],
      MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN EXISTS_TAC
       (← q r"\t:real. k * (r pow 2 - t pow 2) / &2") THEN
      CONJ_TAC THENL
       [X_GEN_TAC (← q r"t:real") THEN REWRITE_TAC [IN_REAL_INTERVAL] THEN
        STRIP_TAC THEN AP_TERM_TAC THEN
        SUBGOAL_THEN (← q r"&0 <= t") ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"a * r:real") THEN
          ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_IMP_LE],
          ALL_TAC] THEN
        MATCH_MP_TAC (← REAL_ARITH
         (← q r"a <= b /\ a pow 2 = x ==> x / &2 = (min a b pow 2) / &2")) THEN
        SUBGOAL_THEN (← q r"&0 <= r pow 2 - t pow 2") ASSUME_TAC THENL
         [REWRITE_TAC [← GSYM REAL_LE_SQUARE_ABS, REAL_SUB_LE] THEN
          ASM_REAL_ARITH_TAC,
          ALL_TAC] THEN
        ASM_SIMP_TAC [SQRT_POW_2] THEN MATCH_MP_TAC REAL_POW_LE2_REV THEN
        EXISTS_TAC (← q r"2") THEN REWRITE_TAC [ARITH] THEN
        ASM_SIMP_TAC [SQRT_POW_2, REAL_POW_MUL, REAL_LE_MUL, SQRT_POS_LT,
                     REAL_LT_MUL, REAL_LT_IMP_LE, SQRT_POS_LE] THEN
        REWRITE_TAC [← REAL_ARITH (← q r"r - t <= t * (a - &1) <=> r <= t * a")] THEN
        REWRITE_TAC [REAL_INV_POW, ← GSYM REAL_POW_MUL] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN
        ASM_SIMP_TAC [← GSYM real_div, REAL_LE_RDIV_EQ] THEN
        ASM_REAL_ARITH_TAC,
        MP_TAC (← ISPECL
         [← q r"\t. k / &2 * (r pow 2 * t - t pow 3 / &3)",
          ← q r"\t. k * (r pow 2 - t pow 2) / &2",
          ← q r"a * r:real", ← q r"r:real"] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
        ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_IMP_LE] THEN ANTS_TAC THENL
         [ASM_REWRITE_TAC [← REAL_ARITH (← q r"a * r <= r <=> &0 <= r * (&1 - a)")] THEN
          ASM_SIMP_TAC [REAL_LE_MUL, REAL_LT_IMP_LE, REAL_SUB_LE] THEN
          REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
          CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING,
          MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          UNDISCH_TAC (← q r"&0 < a") THEN CONV_TAC REAL_FIELD]]])

  let BOUNDED_CONIC_CAP_WEDGE ← prove
   r"!v0 v1:real^3 w1 w2 r a.
          bounded(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2)"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC (← q r"conic_cap (v0:real^3) v1 r a") THEN
    REWRITE_TAC [BOUNDED_CONIC_CAP] THEN SET_TAC [])

  let MEASURABLE_CONIC_CAP_WEDGE ← prove
   r"!v0 v1:real^3 w1 w2 r a.
          measurable(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2)"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC MEASURABLE_BOUNDED_INTER_OPEN THEN
    REWRITE_TAC [BOUNDED_CONIC_CAP, MEASURABLE_CONIC_CAP, OPEN_WEDGE])

  let VOLUME_CONIC_CAP_COMPL ← (do
    let lemma ← prove
     r"!f:real^N->real^N s t t' u.
            measurable(s) /\ measurable(t) /\ measurable(u) /\
            orthogonal_transformation f /\
            s SUBSET u /\ t' SUBSET u /\ s INTER t' = {} /\
            negligible(u DIFF (s UNION t')) /\
            ((!y. ?x. f x = y) ==> IMAGE f t = t')
            ==> measure s + measure t = measure u"
     (REPEAT GEN_TAC THEN
      ASM_CASES_TAC (← q r"orthogonal_transformation(f:real^N->real^N)") THEN
      ASM_SIMP_TAC [ORTHOGONAL_TRANSFORMATION_SURJECTIVE] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC
       (← q r"measure(s:real^N->bool) + measure(t':real^N->bool)") THEN
      CONJ_TAC THENL [ASM_MESON_TAC [MEASURE_ORTHOGONAL_IMAGE_EQ], ALL_TAC] THEN
      W (MP_TAC o PART_MATCH (rhs o rand) MEASURE_DISJOINT_UNION o
        lhand o snd) THEN
      ASM_REWRITE_TAC [DISJOINT] THEN ANTS_TAC THENL
       [ASM_MESON_TAC [MEASURABLE_LINEAR_IMAGE, ORTHOGONAL_TRANSFORMATION_LINEAR],
        DISCH_THEN (SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          NEGLIGIBLE_SUBSET)) THEN
      REPEAT (POP_ASSUM MP_TAC) THEN SET_TAC [])
    prove
     r"!v0 v1:real^3 w1 w2 r a.
          &0 <= r
          ==> measure(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) +
              measure(conic_cap v0 v1 r (--a) INTER wedge v0 v1 w1 w2) =
              azim v0 v1 w1 w2 * &2 * r pow 3 / &3"
      (REWRITE_TAC [conic_cap, rcone_gt, NORMBALL_BALL, rconesgn] THEN
      GEOM_ORIGIN_TAC (← q r"v0:real^3") THEN
      REWRITE_TAC [VECTOR_SUB_RZERO, DIST_0, real_gt] THEN
      GEOM_BASIS_MULTIPLE_TAC 3 (← q r"v1:real^3") THEN
      X_GEN_TAC (← q r"v1:real") THEN
      GEN_REWRITE_TAC LAND_CONV [← REAL_ARITH (← q r"&0 <= x <=> x = &0 \/ &0 < x")] THEN
      STRIP_TAC THENL
       [ASM_SIMP_TAC [VECTOR_MUL_LZERO, WEDGE_DEGENERATE, AZIM_DEGENERATE] THEN
        REWRITE_TAC [INTER_EMPTY, MEASURE_EMPTY] THEN REAL_ARITH_TAC,
        ALL_TAC] THEN
      ASM_SIMP_TAC [← GSYM VOLUME_BALL_WEDGE] THEN REPEAT STRIP_TAC THEN
      ASM_CASES_TAC (← q r"collinear {vec 0:real^3,v1 % basis 3,w1}") THENL
       [ASM_SIMP_TAC [WEDGE_DEGENERATE, AZIM_DEGENERATE] THEN
        REWRITE_TAC [INTER_EMPTY, MEASURE_EMPTY] THEN REAL_ARITH_TAC,
        ALL_TAC] THEN
      ASM_SIMP_TAC [← GSYM VOLUME_BALL_WEDGE] THEN REPEAT STRIP_TAC THEN
      ASM_CASES_TAC (← q r"collinear {vec 0:real^3,v1 % basis 3,w2}") THENL
       [ASM_SIMP_TAC [WEDGE_DEGENERATE, AZIM_DEGENERATE] THEN
        REWRITE_TAC [INTER_EMPTY, MEASURE_EMPTY] THEN REAL_ARITH_TAC,
        ALL_TAC] THEN
      ASM_SIMP_TAC [WEDGE_SPECIAL_SCALE] THEN
      MAP_EVERY UNDISCH_TAC
       [← q r"~collinear{vec 0:real^3,v1 % basis 3,w1}",
        ← q r"~collinear{vec 0:real^3,v1 % basis 3,w2}"] THEN
      ASM_SIMP_TAC [COLLINEAR_SPECIAL_SCALE] THEN REPEAT DISCH_TAC THEN
      REWRITE_TAC [NORM_MUL, DOT_RMUL] THEN
      ASM_SIMP_TAC [REAL_LT_LMUL_EQ, ← REAL_ARITH
        (← q r"&0 < v1 ==> n * (abs v1 * y) * a = v1 * n * y * a")] THEN
      MATCH_MP_TAC lemma THEN
      MP_TAC (← ISPECL
       [← q r"vec 0:real^3", ← q r"basis 3:real^3", ← q r"w1:real^3", ← q r"w2:real^3",
        ← q r"r:real", ← q r"a:real"] MEASURABLE_CONIC_CAP_WEDGE) THEN
      MP_TAC (← ISPECL
       [← q r"vec 0:real^3", ← q r"basis 3:real^3", ← q r"w1:real^3", ← q r"w2:real^3",
        ← q r"r:real", ← q r"--a:real"] MEASURABLE_CONIC_CAP_WEDGE) THEN
      REWRITE_TAC [conic_cap, rcone_gt, NORMBALL_BALL, rconesgn] THEN
      REWRITE_TAC [VECTOR_SUB_RZERO, DIST_0, real_gt] THEN
      REPEAT DISCH_TAC THEN ASM_REWRITE_TAC [MEASURABLE_BALL_WEDGE] THEN
      SIMP_TAC [NORM_BASIS, DOT_BASIS, DIMINDEX_3, ARITH, REAL_MUL_LID] THEN
      EXISTS_TAC (← q r"(\x. vector[x$1; x$2; --(x$3)]):real^3->real^3") THEN
      EXISTS_TAC (← q r"(ball(vec 0,r) INTER {x | norm x * a > x$3}) INTER
                  wedge (vec 0:real^3) (basis 3) w1 w2") THEN
      CONJ_TAC THENL
       [REWRITE_TAC [ORTHOGONAL_TRANSFORMATION, linear] THEN
        REWRITE_TAC [CART_EQ, DIMINDEX_3, FORALL_3, VECTOR_3, vector_norm, DOT_3,
                    VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
        REPEAT (GEN_TAC ORELSE CONJ_TAC ORELSE AP_TERM_TAC) THEN
        REAL_ARITH_TAC,
        ALL_TAC] THEN
      CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
      CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_ELIM_THM, real_gt] THEN
        MESON_TAC [REAL_LT_ANTISYM],
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC (← q r"rcone_eq (vec 0:real^3) (basis 3) a") THEN
        SIMP_TAC [NEGLIGIBLE_RCONE_EQ, BASIS_NONZERO, DIMINDEX_3, ARITH] THEN
        REWRITE_TAC [SUBSET, rcone_eq, rconesgn, VECTOR_SUB_RZERO, DIST_0] THEN
        SIMP_TAC [DOT_BASIS, NORM_BASIS, DIMINDEX_3, ARITH] THEN
        REWRITE_TAC [IN_DIFF, IN_ELIM_THM, IN_INTER, IN_UNION] THEN
        GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [] THEN DISCH_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [IN_INTER, IN_BALL_0, IN_ELIM_THM, VECTOR_3] THEN
      X_GEN_TAC (← q r"x:real^3") THEN
      SUBGOAL_THEN (← q r"norm(vector [x$1; x$2; --(x$3)]:real^3) = norm(x:real^3)")
      SUBST1_TAC THENL
       [REWRITE_TAC [NORM_EQ, DOT_3, VECTOR_3] THEN REAL_ARITH_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"n * a > --x <=> n * --a < x")] THEN
      MATCH_MP_TAC (← TAUT (← q r"(a ==> (b <=> b')) ==> (a /\ b <=> a /\ b')")) THEN
      STRIP_TAC THEN
      REWRITE_TAC [COLLINEAR_BASIS_3, wedge, AZIM_ARG] THEN
      REWRITE_TAC [IN_ELIM_THM] THEN
      SUBGOAL_THEN (← q r"(dropout 3 :real^3->real^2) (vector [x$1; x$2; --(x$3)]) =
                    (dropout 3 :real^3->real^2) x")
       (fun th => REWRITE_TAC [th]) THEN
      SIMP_TAC [CART_EQ, DIMINDEX_2, FORALL_2, dropout, LAMBDA_BETA, ARITH,
               DIMINDEX_3, VECTOR_3]))

  let VOLUME_CONIC_CAP_WEDGE_MEDIUM ← prove
   r"!v0 v1:real^3 w1 w2 r a.
         &0 <= a /\ ~collinear {v0,v1,w1} /\ ~collinear {v0,v1,w2}
         ==> bounded(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) /\
             measurable(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) /\
             measure(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) =
             if &1 < abs a \/ r < &0 then &0
             else azim v0 v1 w1 w2 / &3 * (&1 - a) * r pow 3"
   (REWRITE_TAC [BOUNDED_CONIC_CAP_WEDGE, MEASURABLE_CONIC_CAP_WEDGE] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM (DISJ_CASES_TAC o MATCH_MP (← REAL_ARITH
     (← q r"&0 <= a ==> &0 < a \/ a = &0")))
    THENL
     [ASM_SIMP_TAC [VOLUME_CONIC_CAP_WEDGE_WEAK] THEN
      REWRITE_TAC [REAL_LE_LT] THEN
      ASM_CASES_TAC (← q r"a = &1") THEN ASM_REWRITE_TAC [] THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    COND_CASES_TAC THENL
     [REWRITE_TAC [conic_cap, NORMBALL_BALL] THEN
      SUBGOAL_THEN (← q r"ball(v0:real^3,r) = {}")
       (fun th => SIMP_TAC [th, INTER_EMPTY, MEASURE_EMPTY]) THEN
      REWRITE_TAC [BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC,
      MP_TAC (← ISPECL [← q r"v0:real^3", ← q r"v1:real^3", ← q r"w1:real^3", ← q r"w2:real^3",
                     ← q r"r:real", ← q r"&0"] VOLUME_CONIC_CAP_COMPL) THEN
      REWRITE_TAC [REAL_NEG_0] THEN ASM_REAL_ARITH_TAC])

  let VOLUME_CONIC_CAP_WEDGE ← prove
   r"!v0 v1:real^3 w1 w2 r a.
         ~collinear {v0,v1,w1} /\ ~collinear {v0,v1,w2}
         ==> bounded(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) /\
             measurable(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) /\
             measure(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) =
                  if &1 < a \/ r < &0 then &0
                  else azim v0 v1 w1 w2 / &3 * (&1 - max a (-- &1)) * r pow 3"
   (REWRITE_TAC [BOUNDED_CONIC_CAP_WEDGE, MEASURABLE_CONIC_CAP_WEDGE] THEN
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"&0 <= a") THEN
    ASM_SIMP_TAC [VOLUME_CONIC_CAP_WEDGE_MEDIUM,
                 ← REAL_ARITH (← q r"&0 <= a ==> abs a = a /\ max a (-- &1) = a")] THEN
    MP_TAC (← ISPECL [← q r"v0:real^3", ← q r"v1:real^3", ← q r"w1:real^3", ← q r"w2:real^3",
                     ← q r"r:real", ← q r"--a:real"] VOLUME_CONIC_CAP_WEDGE_MEDIUM) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"v0:real^3", ← q r"v1:real^3", ← q r"w1:real^3", ← q r"w2:real^3",
                   ← q r"r:real", ← q r"a:real"] VOLUME_CONIC_CAP_COMPL) THEN
    ASM_CASES_TAC (← q r"r < &0") THENL
     [REWRITE_TAC [conic_cap, NORMBALL_BALL] THEN
      SUBGOAL_THEN (← q r"ball(v0:real^3,r) = {}")
       (fun th => SIMP_TAC [th, INTER_EMPTY, MEASURE_EMPTY]) THEN
      REWRITE_TAC [BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    ASM_REWRITE_TAC [← GSYM REAL_NOT_LT, REAL_ABS_NEG] THEN
    ASM_SIMP_TAC [← REAL_ARITH (← q r"~(&0 <= a) ==> ~(&1 < a) /\ abs a = --a")] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
     [ASM_SIMP_TAC [← REAL_ARITH (← q r"&1 < --a ==> max a (-- &1) = -- &1")] THEN
      REAL_ARITH_TAC,
      ASM_SIMP_TAC [← REAL_ARITH (← q r"~(&1 < --a) ==> max a (-- &1) = a")] THEN
      REAL_ARITH_TAC])

  pure { VOLUME_CONIC_CAP_WEDGE_WEAK, BOUNDED_CONIC_CAP_WEDGE, MEASURABLE_CONIC_CAP_WEDGE,
         VOLUME_CONIC_CAP_COMPL, VOLUME_CONIC_CAP_WEDGE_MEDIUM, VOLUME_CONIC_CAP_WEDGE }
/- ------------------------------------------------------------------------- -/
/- Precise formulation of Flyspeck volume properties.                        -/
/- (flyspeck.ml 6545-6816)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FYW where
  cone : thm
  cone0 : thm
  solid_triangle : thm
  rect : thm
  RECT_INTERVAL : thm
  RCONE_GE_GT : thm
  RCONE_GT_GE : thm
  is_sphere : thm
  c_cone : thm
  circular_cone : thm
  NULLSET_RULES : thm
  primitive : thm
  MEASURABLE_RULES : thm
  vol_solid_triangle : thm
  vol_frustt_wedge : thm
  vol_conic_cap_wedge : thm
  vol_conv : thm
  vol_rect : thm
  vol_ball_wedge : thm
  SDIFF : thm
  volume_props : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYW [HolBase] (D : FlyspeckDeps) (BFYA : FYA) (BFYB : FYB) (BFYC : FYC) (BFYG : FYG) (BFYM : FYM) (BFYO : FYO) (BFYP : FYP) (BFYQ : FYQ) (BFYR : FYR) (BFYS : FYS) (BFYT : FYT) (BFYU : FYU) (BFYV : FYV) : ExceptT String IO FYW := do
  -- @@SCOPE BEGIN
  let { COPLANAR_IMP_NEGLIGIBLE, .. } := BFYA
  let { COPLANAR, .. } := BFYB
  let { aff_gt_def, .. } := BFYC
  let { MEASURABLE_CONV0, .. } := BFYG
  let { WEDGE_DEGENERATE, .. } := BFYM
  let { OPEN_WEDGE, .. } := BFYO
  let { rcone_eq, rcone_ge, rcone_gt, rconesgn, VOLUME_OF_TETRAHEDRON, .. } := BFYP
  let { BOUNDED_CONIC_CAP, MEASURABLE_CONIC_CAP, MEASURABLE_ELLIPSOID, NORMBALL_BALL,
        scale, .. } := BFYQ
  let { NEGLIGIBLE_RCONE_EQ, .. } := BFYR
  let { MEASURABLE_BALL_WEDGE, VOLUME_BALL_WEDGE, .. } := BFYS
  let { MEASURABLE_BALL_AFF_GT, VOLUME_SOLID_TRIANGLE, .. } := BFYT
  let { MEASURABLE_BOUNDED_INTER_OPEN, VOLUME_FRUSTT_WEDGE, .. } := BFYU
  let { VOLUME_CONIC_CAP_WEDGE, .. } := BFYV
  let { override_interface, .. } := D
  let { ASM_MESON_TAC, MESON_TAC, new_definition, REAL_ARITH_TAC, .. } := D.crd
  let { HAS_MEASURE_MEASURE, HAS_MEASURE_STRETCH, MEASURABLE_TRANSLATION,
        MEASURE_NEGLIGIBLE_SYMDIFF, MEASURE_TRANSLATION, NEGLIGIBLE_SPHERE,
        .. } := D.qmeasure
  let { EXISTS_PAIRED_THM, .. } := D.qsession
  let { ARITH, CART_EQ, DIMINDEX_3, FORALL_3, LAMBDA_BETA, REAL_MUL_LZERO, VECTOR_3,
        .. } := D.crd.thms
  let { HAS_MEASURE_0, HAS_MEASURE_MEASURABLE_MEASURE, MEASURABLE_DIFF, MEASURABLE_EMPTY,
        MEASURABLE_INTER, MEASURABLE_INTERVAL, MEASURABLE_UNION, MEASURE_INTERVAL,
        MEASURE_POS_LE, .. } := D.gm.ra.qmeasure
  let { sphere, .. } := D.gm.ra.ts.qtopology
  let { PRODUCT_3, .. } := D.gm.ra.ts.cn.ms.qdet
  let { CONTENT_CLOSED_INTERVAL_CASES, .. } := D.gm.ra.ts.cn.ms.qintegration1
  let { NEGLIGIBLE_SUBSET, NEGLIGIBLE_UNION, .. } := D.gm.ra.ts.cn.ms.qintegration3
  let { REAL_ARITH, REAL_FIELD, SET_TAC, VECTOR_ARITH, .. } := D.gm.ra.ts.cn.cx.cvx
  let { COND_ID, EQ_IMP, ETA_AX, EXTENSION, FINITE_EMPTY, FINITE_INDEX_INRANGE,
        FINITE_INSERT, .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { FUN_EQ_THM, IMP_CONJ, IN_DIFF, INTER_EMPTY, .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_UNION, LEFT_IMP_EXISTS_THM, .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_LE_LT, REAL_LT_REFL, .. } := D.gm.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_AC, REAL_MUL_RZERO, REAL_SUB_REFL, SUBSET_REFL,
        .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { real_ge, real_gt, .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { DIST_SYM, .. } := D.gm.ra.ts.cn.cx.cvx.vec1
  let { IN_INTERVAL, .. } := D.gm.ra.ts.cn.cx.cvx.vec2
  let { NORM_SUB, .. } := D.gm.ra.ts.cn.cx.cvx.vec3
  let { dist, .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { FINITE_IMP_BOUNDED, .. } := D.gm.ra.ts.cn.cx.cvx.top3
  -- @@SCOPE END

  let cone ← new_definition r"cone v S:real^A->bool = affsign sgn_ge {v} S"

  let cone0 ← new_definition r"cone0 v S:real^A->bool = affsign sgn_gt {v} S"

  let solid_triangle ← new_definition
   r"solid_triangle v0 S r = normball v0 r INTER cone0 v0 S"

  let rect ← new_definition
   r"rect (a:real^3) (b:real^3) =
        {(v:real^3) | !i. (a$i < v$i /\ v$i < b$i )}"

  let RECT_INTERVAL ← prove
   r"!a b. rect a b = interval(a,b)"
   (REWRITE_TAC [rect, EXTENSION, IN_INTERVAL, IN_ELIM_THM] THEN
    MESON_TAC [FINITE_INDEX_INRANGE])

  let RCONE_GE_GT ← prove
   r"rcone_ge z w h =
        rcone_gt z w h UNION
        { x | (x - z) dot (w - z) = norm(x - z) * norm(w - z) * h}"
   (REWRITE_TAC [rcone_ge, rcone_gt, rconesgn] THEN
    REWRITE_TAC [dist, EXTENSION, IN_UNION, NORM_SUB, IN_ELIM_THM] THEN
    REAL_ARITH_TAC)

  let RCONE_GT_GE ← prove
   r"rcone_gt z w h =
        rcone_ge z w h DIFF
        { x | (x - z) dot (w - z) = norm(x - z) * norm(w - z) * h}"
   (REWRITE_TAC [rcone_ge, rcone_gt, rconesgn] THEN
    REWRITE_TAC [dist, EXTENSION, IN_DIFF, NORM_SUB, IN_ELIM_THM] THEN
    REAL_ARITH_TAC)

  override_interface "NULLSET" (← q r"negligible:(real^3->bool)->bool")
  override_interface "vol" (← q r"measure:(real^3->bool)->real")

  let is_sphere ← new_definition
   r"is_sphere x=(?(v:real^3)(r:real). (r> &0)/\ (x={w:real^3 | norm (w-v)= r}))"

  let c_cone ← new_definition
   r"c_cone (v,w:real^3, r:real)=
       {x:real^3 | ((x-v) dot w = norm (x-v)* norm w* r)}"

  let circular_cone ← new_definition
   r"circular_cone (V:real^3-> bool)=
   (? (v,w:real^3)(r:real). ~(w = vec 0) /\ V = c_cone (v,w,r))"

  let NULLSET_RULES ← prove
   r"(!P. ((plane P)\/ (is_sphere P) \/ (circular_cone P)) ==> NULLSET P) /\
   (!(s:real^3->bool) t. (NULLSET s /\ NULLSET t) ==> NULLSET (s UNION t))"
   (SIMP_TAC [NEGLIGIBLE_UNION] THEN
    X_GEN_TAC (← q r"s:real^3->bool") THEN STRIP_TAC THENL
     [MATCH_MP_TAC COPLANAR_IMP_NEGLIGIBLE THEN
      SIMP_TAC [COPLANAR, DIMINDEX_3, ARITH] THEN ASM_MESON_TAC [SUBSET_REFL],
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [is_sphere]) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [← GSYM dist] THEN
      ONCE_REWRITE_TAC [DIST_SYM] THEN
      REWRITE_TAC [← REWRITE_RULE [sphere] NEGLIGIBLE_SPHERE],
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [circular_cone]) THEN
      REWRITE_TAC [EXISTS_PAIRED_THM, c_cone] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN
      MP_TAC (← ISPECL [← q r"w + v:real^3", ← q r"v:real^3", ← q r"r:real"]
       NEGLIGIBLE_RCONE_EQ) THEN
      ASM_REWRITE_TAC [rcone_eq, rconesgn] THEN
      REWRITE_TAC [dist, ← VECTOR_ARITH (← q r"(w + v) - v:real^N = w")] THEN
      ASM_REWRITE_TAC [← VECTOR_ARITH (← q r"w + v:real^N = v <=> w = vec 0")]])

  let primitive ← new_definition r"primitive (C:real^3->bool) =
  ((?v0 v1 v2 v3 r.  (C = solid_triangle v0 {v1,v2,v3} r)) \/
  (?v0 v1 v2 v3. (C = conv0 {v0,v1,v2,v3})) \/
  (?v0 v1 v2 v3 h a. &0 < a /\
                     (C = frustt v0 v1 h a INTER wedge v0 v1 v2 v3)) \/
  (?v0 v1 v2 v3 r c. (C = conic_cap v0 v1 r c INTER wedge v0 v1 v2 v3)) \/
  (?a b.  (C = rect a b)) \/
  (?t r. (C = ellipsoid t r)) \/
  (?v0 v1 v2 v3 r. (C = normball v0 r INTER wedge v0 v1 v2 v3)))"

  let MEASURABLE_RULES ← prove
   r"(!C. primitive C ==> measurable C) /\
   (!Z. NULLSET Z ==> measurable Z) /\
   (!X t. measurable X ==> (measurable (IMAGE (scale t) X))) /\
   (!X v. measurable X ==> (measurable (IMAGE ((+) v) X))) /\
   (!(s:real^3->bool) t. (measurable s /\ measurable t)
                         ==> measurable (s UNION t)) /\
   (!(s:real^3->bool) t. (measurable s /\ measurable t)
                         ==> measurable (s INTER t)) /\
   (!(s:real^3->bool) t. (measurable s /\ measurable t)
                         ==> measurable (s DIFF t))"
   (SIMP_TAC [MEASURABLE_UNION, MEASURABLE_INTER, MEASURABLE_DIFF] THEN
    REWRITE_TAC [← REWRITE_RULE [ETA_AX] MEASURABLE_TRANSLATION] THEN
    SIMP_TAC [← GSYM HAS_MEASURE_0, HAS_MEASURE_MEASURABLE_MEASURE] THEN
    CONJ_TAC THENL
     [ALL_TAC,
      MAP_EVERY X_GEN_TAC [← q r"X:real^3->bool", ← q r"t:real^3"] THEN
      REWRITE_TAC [HAS_MEASURE_MEASURE] THEN
      DISCH_THEN (MP_TAC o MATCH_MP HAS_MEASURE_STRETCH) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"\i. (t:real^3)$i")) THEN
      REWRITE_TAC [HAS_MEASURE_MEASURABLE_MEASURE] THEN
      DISCH_THEN (MP_TAC o CONJUNCT1) THEN MATCH_MP_TAC EQ_IMP THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC [FUN_EQ_THM, scale, CART_EQ, LAMBDA_BETA,
               DIMINDEX_3, VECTOR_3, FORALL_3]] THEN
    X_GEN_TAC (← q r"C:real^3->bool") THEN REWRITE_TAC [primitive] THEN
    REWRITE_TAC [NORMBALL_BALL, RECT_INTERVAL] THEN
    DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN MP_TAC) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THENL
     [REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [solid_triangle, NORMBALL_BALL, cone0, ← GSYM aff_gt_def] THEN
      REWRITE_TAC [MEASURABLE_BALL_AFF_GT],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC MEASURABLE_CONV0 THEN MATCH_MP_TAC FINITE_IMP_BOUNDED THEN
      REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY],
      MAP_EVERY X_GEN_TAC
       [← q r"v0:real^3", ← q r"v1:real^3", ← q r"v2:real^3", ← q r"v3:real^3",
        ← q r"h:real", ← q r"a:real"] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
      ASM_CASES_TAC (← q r"collinear {v0:real^3, v1, v2}") THENL
       [ASM_SIMP_TAC [WEDGE_DEGENERATE, INTER_EMPTY, MEASURABLE_EMPTY],
        ALL_TAC] THEN
      ASM_CASES_TAC (← q r"collinear {v0:real^3, v1, v3}") THENL
       [ASM_SIMP_TAC [WEDGE_DEGENERATE, INTER_EMPTY, MEASURABLE_EMPTY],
        ALL_TAC] THEN
      ASM_SIMP_TAC [VOLUME_FRUSTT_WEDGE],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC MEASURABLE_BOUNDED_INTER_OPEN THEN
      REWRITE_TAC [MEASURABLE_CONIC_CAP, BOUNDED_CONIC_CAP, OPEN_WEDGE],
      SIMP_TAC [MEASURABLE_INTERVAL],
      SIMP_TAC [MEASURABLE_ELLIPSOID],
      SIMP_TAC [MEASURABLE_BALL_WEDGE]])

  let vol_solid_triangle ← new_definition r"vol_solid_triangle v0 v1 v2 v3 r =
   let a123 = dihV v0 v1 v2 v3 in
   let a231 = dihV v0 v2 v3 v1 in
   let a312 = dihV v0 v3 v1 v2 in
     (a123 + a231 + a312 - pi)*(r pow 3)/(&3)"

  let vol_frustt_wedge ← new_definition r"vol_frustt_wedge v0 v1 v2 v3 h a =
       (azim v0 v1 v2 v3)*(h pow 3)*(&1/(a*a) - &1)/(&6)"

  let vol_conic_cap_wedge ← new_definition r"vol_conic_cap_wedge v0 v1 v2 v3 r c =
       (azim v0 v1 v2 v3)*(&1 - c)*(r pow 3)/(&3)"

  let vol_conv ← new_definition r"vol_conv v1 v2 v3 v4 =
   let x12 = dist(v1,v2) pow 2 in
   let x13 = dist(v1,v3) pow 2 in
   let x14 = dist(v1,v4) pow 2 in
   let x23 = dist(v2,v3) pow 2 in
   let x24 = dist(v2,v4) pow 2 in
   let x34 = dist(v3,v4) pow 2 in
   sqrt(delta_x x12 x13 x14 x34 x24 x23)/(&12)"

  let vol_rect ← new_definition r"vol_rect a b =
   if (a$1 < b$1) /\ (a$2 < b$2) /\ (a$3 < b$3) then
   (b$3-a$3)*(b$2-a$2)*(b$1-a$1) else &0"

  let vol_ball_wedge ← new_definition r"vol_ball_wedge v0 v1 v2 v3 r =
   (azim v0 v1 v2 v3)*(&2)*(r pow 3)/(&3)"

  let SDIFF ← new_definition r"SDIFF X Y = (X DIFF Y) UNION (Y DIFF X)"

  let volume_props ← prove
   r"(!C. measurable C ==> vol C >= &0) /\
   (!Z. NULLSET Z ==> (vol Z = &0)) /\
   (!X Y. measurable X /\ measurable Y /\ NULLSET (SDIFF X Y)
          ==> (vol X = vol Y)) /\
   (!X t. (measurable X) /\ (measurable (IMAGE (scale t) X))
          ==> (vol (IMAGE (scale t) X) = abs(t$1 * t$2 * t$3)*vol(X))) /\
   (!X v. measurable X ==> (vol (IMAGE ((+) v) X) = vol X)) /\
   (!v0 v1 v2 v3 r. (r > &0) /\ ~coplanar{v0,v1,v2,v3}
                    ==> vol (solid_triangle v0 {v1,v2,v3} r) =
                        vol_solid_triangle v0 v1 v2 v3 r) /\
   (!v0 v1 v2 v3. vol(conv0 {v0,v1,v2,v3}) = vol_conv v0 v1 v2 v3) /\
   (!v0 v1 v2 v3 h a. ~(collinear {v0,v1,v2}) /\ ~(collinear {v0,v1,v3}) /\
                      (h >= &0) /\ (a > &0) /\ (a <= &1)
                      ==> vol(frustt v0 v1 h a INTER wedge v0 v1 v2 v3) =
                          vol_frustt_wedge v0 v1 v2 v3 h a) /\
   (!v0 v1 v2 v3 r c.  ~(collinear {v0,v1,v2}) /\ ~(collinear {v0,v1,v3}) /\
                       (r >= &0) /\ (c >= -- (&1)) /\ (c <= &1)
                       ==> (vol(conic_cap v0 v1 r c INTER wedge v0 v1 v2 v3) =
                           vol_conic_cap_wedge v0 v1 v2 v3 r c)) /\
   (!(a:real^3) (b:real^3). vol(rect a b) = vol_rect a b) /\
   (!v0 v1 v2 v3 r. ~(collinear {v0,v1,v2}) /\ ~(collinear {v0,v1,v3}) /\
                    (r >= &0)
                    ==> (vol(normball v0 r INTER wedge v0 v1 v2 v3) =
                         vol_ball_wedge v0 v1 v2 v3 r))"
   (SIMP_TAC [MEASURE_POS_LE, real_ge, real_gt] THEN REPEAT CONJ_TAC THENL
     [SIMP_TAC [← GSYM HAS_MEASURE_0, HAS_MEASURE_MEASURABLE_MEASURE],
      MAP_EVERY X_GEN_TAC [← q r"s:real^3->bool", ← q r"t:real^3->bool"] THEN
      STRIP_TAC THEN MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
      ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          NEGLIGIBLE_SUBSET)) THEN
      REWRITE_TAC [SDIFF] THEN SET_TAC [],
      MAP_EVERY X_GEN_TAC [← q r"X:real^3->bool", ← q r"t:real^3"] THEN
      REWRITE_TAC [HAS_MEASURE_MEASURE] THEN
      DISCH_THEN (MP_TAC o MATCH_MP HAS_MEASURE_STRETCH o CONJUNCT1) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"\i. (t:real^3)$i")) THEN
      REWRITE_TAC [HAS_MEASURE_MEASURABLE_MEASURE] THEN
      DISCH_THEN (MP_TAC o CONJUNCT2) THEN
      REWRITE_TAC [DIMINDEX_3, PRODUCT_3] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC [FUN_EQ_THM, scale, CART_EQ, LAMBDA_BETA,
               DIMINDEX_3, VECTOR_3, FORALL_3],
      REWRITE_TAC [← REWRITE_RULE [ETA_AX] MEASURE_TRANSLATION],
      REPEAT STRIP_TAC THEN
      REWRITE_TAC [solid_triangle, vol_solid_triangle, NORMBALL_BALL] THEN
      REWRITE_TAC [cone0, ← GSYM aff_gt_def] THEN
      MATCH_MP_TAC VOLUME_SOLID_TRIANGLE THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [vol_conv, VOLUME_OF_TETRAHEDRON],
      SIMP_TAC [VOLUME_FRUSTT_WEDGE, vol_frustt_wedge] THEN
      SIMP_TAC [← REAL_ARITH (← q r"&0 <= h ==> ~(h < &0)")] THEN
      SIMP_TAC [← REAL_ARITH (← q r"a <= &1 ==> (&1 <= a <=> a = &1)")] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD,
      SIMP_TAC [VOLUME_CONIC_CAP_WEDGE, vol_conic_cap_wedge] THEN
      SIMP_TAC [← REAL_ARITH (← q r"&0 <= r ==> ~(r < &0)")] THEN
      SIMP_TAC [← REAL_ARITH (← q r"c <= &1 ==> ~(&1 < c)")] THEN
      ASM_SIMP_TAC [← REAL_ARITH (← q r"-- &1 <= c ==> max c (-- &1) = c")] THEN
      REPEAT STRIP_TAC THEN REAL_ARITH_TAC,
      REWRITE_TAC [vol_rect, RECT_INTERVAL, MEASURE_INTERVAL] THEN
      REWRITE_TAC [CONTENT_CLOSED_INTERVAL_CASES] THEN
      REWRITE_TAC [DIMINDEX_3, FORALL_3, PRODUCT_3] THEN
      MAP_EVERY X_GEN_TAC [← q r"a:real^3", ← q r"b:real^3"] THEN
      REWRITE_TAC [REAL_LE_LT] THEN
      ASM_CASES_TAC (← q r"(a:real^3)$1 = (b:real^3)$1") THEN
      ASM_REWRITE_TAC [REAL_LT_REFL, REAL_MUL_LZERO, REAL_MUL_RZERO,
                      REAL_SUB_REFL, COND_ID] THEN
      ASM_CASES_TAC (← q r"(a:real^3)$2 = (b:real^3)$2") THEN
      ASM_REWRITE_TAC [REAL_LT_REFL, REAL_MUL_LZERO, REAL_MUL_RZERO,
                      REAL_SUB_REFL, COND_ID] THEN
      ASM_CASES_TAC (← q r"(a:real^3)$3 = (b:real^3)$3") THEN
      ASM_REWRITE_TAC [REAL_LT_REFL, REAL_MUL_LZERO, REAL_MUL_RZERO,
                      REAL_SUB_REFL, COND_ID] THEN
      REWRITE_TAC [REAL_MUL_AC],
      SIMP_TAC [VOLUME_BALL_WEDGE, NORMBALL_BALL, vol_ball_wedge]])

  pure { cone, cone0, solid_triangle, rect, RECT_INTERVAL, RCONE_GE_GT, RCONE_GT_GE,
         is_sphere, c_cone, circular_cone, NULLSET_RULES, primitive, MEASURABLE_RULES,
         vol_solid_triangle, vol_frustt_wedge, vol_conic_cap_wedge, vol_conv, vol_rect,
         vol_ball_wedge, SDIFF, volume_props }
/- ------------------------------------------------------------------------- -/
/- Additional results on polyhedra and relation to fans, then the load-time  -/
/- `set_basic_congs` fixing the congruence rules as expected in Flyspeck.    -/
/- (flyspeck.ml 6817-7010)                                                   -/
/- ------------------------------------------------------------------------- -/

structure FYX where
  POLYHEDRON_COLLINEAR_FACES_STRONG : thm
  POLYHEDRON_COLLINEAR_FACES : thm
  vertices : thm
  edges : thm
  VERTICES_TRANSLATION : thm
  VERTICES_LINEAR_IMAGE : thm
  EDGES_TRANSLATION : thm
  EDGES_LINEAR_IMAGE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFYX [HolBase] (D : FlyspeckDeps) : ExceptT String IO FYX := do
  -- @@SCOPE BEGIN
  let { basic_congs, set_basic_congs, .. } := D
  let { add_linear_invariants, ASM_MESON_TAC, MESON_TAC, new_definition, .. } := D.crd
  let { EDGE_OF_IMP_SUBSET, EDGE_OF_LINEAR_IMAGE, EXTREME_POINTS_OF_LINEAR_IMAGE, face_of,
        FACE_OF_IMP_SUBSET, FACE_OF_POLYHEDRON_SUBSET_FACET, facet_of, FACET_OF_REFL,
        SUBSET_OF_FACE_OF, .. } := D.qpolytope
  let { GEOM_TRANSLATE_TAC, .. } := D.geomorigin
  let { REAL_MUL_LZERO, VECTOR_MUL_LID, .. } := D.crd.thms
  let { add_translation_invariants, MESON, SET_TAC, VECTOR_ARITH_TAC,
        .. } := D.gm.ra.ts.cn.cx.cvx
  let { CONJ_SYM, EXISTS_IN_GSPEC, FORALL_IN_GSPEC, .. } := D.gm.ra.ts.cn.cx.cvx.core1
  let { FORALL_IN_IMAGE, IMAGE_CLAUSES, .. } := D.gm.ra.ts.cn.cx.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, MONO_EXISTS, NOT_IMP, .. } := D.gm.ra.ts.cn.cx.cvx.core3
  let { REAL_INV_LT_1, REAL_LT_IMP_NZ, REAL_LT_INV_EQ, REAL_LT_RDIV_EQ,
        .. } := D.gm.ra.ts.cn.cx.cvx.core4
  let { REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_SYM, SUBSET, SUBSET_ANTISYM, SUBSET_REFL,
        .. } := D.gm.ra.ts.cn.cx.cvx.core5
  let { real_div, real_gt, .. } := D.gm.ra.ts.cn.cx.cvx.core6
  let { VECTOR_MUL_ASSOC, VECTOR_MUL_EQ_0, .. } := D.gm.ra.ts.cn.cx.cvx.vec4
  let { CLOSED_SEGMENT_LINEAR_IMAGE, .. } := D.gm.ra.ts.cn.cx.cvx.top1
  let { ENDS_IN_SEGMENT, .. } := D.gm.ra.ts.cn.cx.cvx.top3
  let { IN_SEGMENT, .. } := D.gm.ra.ts.cn.cx.cvx.top4
  let { REAL_WLOG_LT, .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qses
  let { INTERIOR_SUBSET_RELATIVE_INTERIOR, RELATIVE_INTERIOR_SUBSET,
        .. } := D.gm.ra.ts.cn.ms.ig.dv.dg.pt.qcvx3
  -- @@SCOPE END

  let POLYHEDRON_COLLINEAR_FACES_STRONG ← prove
   r"!P:real^N->bool f f' p q s t.
        polyhedron P /\ vec 0 IN relative_interior P /\
        f face_of P /\ ~(f = P) /\ f' face_of P /\ ~(f' = P) /\
        p IN f /\ q IN f' /\ s > &0 /\ t > &0 /\ s % p = t % q
        ==> s = t"
   (ONCE_REWRITE_TAC [← MESON []
     (← q r"(!P f f' p q s t. Q P f f' p q s t) <=>
      (!s t P f f' p q. Q P f f' p q s t)")] THEN
    MATCH_MP_TAC REAL_WLOG_LT THEN
    REWRITE_TAC [real_gt] THEN CONJ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC (← TAUT (← q r"F ==> p")) THEN
    FIRST_X_ASSUM (MP_TAC o AP_TERM (← q r"(%) (inv s):real^N->real^N")) THEN
    ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, REAL_LT_IMP_NZ] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    REWRITE_TAC [VECTOR_MUL_LID, ← GSYM real_div] THEN
    ABBREV_TAC (← q r"u:real = t / s") THEN
    SUBGOAL_THEN (← q r"&0 < u /\ &1 < u") MP_TAC THENL
     [EXPAND_TAC "u" THEN ASM_SIMP_TAC [REAL_LT_RDIV_EQ] THEN
      ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_LID],
      ALL_TAC] THEN
    MAP_EVERY (fun t => UNDISCH_THEN t (fun _ => ALL_TAC))
     [← q r"s < t", ← q r"&0 < s", ← q r"&0 < t", ← q r"t:real / s = u"] THEN
    SPEC_TAC (← q r"u:real", ← q r"t:real") THEN GEN_TAC THEN STRIP_TAC THEN
    DISCH_THEN (ASSUME_TAC o SYM) THEN
    SUBGOAL_THEN (← q r"?g:real^N->bool. g facet_of P /\ f' SUBSET g")
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC FACE_OF_POLYHEDRON_SUBSET_FACET THEN ASM SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~((vec 0:real^N) IN g)") ASSUME_TAC THENL
     [DISCH_TAC THEN
      MP_TAC (← ISPECL [← q r"P:real^N->bool", ← q r"g:real^N->bool", ← q r"P:real^N->bool"]
                     SUBSET_OF_FACE_OF) THEN
      ASM_REWRITE_TAC [SUBSET_REFL, NOT_IMP] THEN CONJ_TAC THENL
       [CONJ_TAC THENL [ASM_MESON_TAC [facet_of], ASM SET_TAC []],
        ASM_MESON_TAC [facet_of, FACET_OF_REFL,
                      SUBSET_ANTISYM, FACE_OF_IMP_SUBSET]],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(g:real^N->bool) face_of P") MP_TAC THENL
     [ASM_MESON_TAC [facet_of], ALL_TAC] THEN
    REWRITE_TAC [face_of] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← liftExcept (last (CONJUNCTS th))))) THEN
    DISCH_THEN (MP_TAC o SPECL [← q r"vec 0:real^N", ← q r"t % q:real^N", ← q r"q:real^N"]) THEN
    ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [RELATIVE_INTERIOR_SUBSET, SUBSET],
      ASM_MESON_TAC [FACE_OF_IMP_SUBSET, SUBSET],
      ASM_MESON_TAC [FACE_OF_IMP_SUBSET, SUBSET],
      ALL_TAC] THEN
    EXPAND_TAC "p" THEN REWRITE_TAC [IN_SEGMENT] THEN CONJ_TAC THENL
     [CONV_TAC (RAND_CONV SYM_CONV) THEN
      ASM_SIMP_TAC [VECTOR_MUL_EQ_0, REAL_LT_IMP_NZ] THEN ASM SET_TAC [],
      EXISTS_TAC (← q r"inv t:real") THEN
      ASM_SIMP_TAC [REAL_LT_INV_EQ, REAL_INV_LT_1] THEN
      EXPAND_TAC "p" THEN REWRITE_TAC [VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC [REAL_MUL_LINV, REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC])

  let POLYHEDRON_COLLINEAR_FACES ← prove
   r"!P:real^N->bool f f' p q s t.
        polyhedron P /\ vec 0 IN interior P /\
        f face_of P /\ ~(f = P) /\ f' face_of P /\ ~(f' = P) /\
        p IN f /\ q IN f' /\ s > &0 /\ t > &0 /\ s % p = t % q
        ==> s = t"
   (MESON_TAC [POLYHEDRON_COLLINEAR_FACES_STRONG,
              INTERIOR_SUBSET_RELATIVE_INTERIOR, SUBSET])

  let vertices ← new_definition
   r"vertices s = {x:real^N | x extreme_point_of s}"

  let edges ← new_definition
   r"edges s = {{v,w} | segment[v,w] edge_of s}"

  let VERTICES_TRANSLATION ← prove
   r"!a s. vertices (IMAGE (\x. a + x) s) = IMAGE (\x. a + x) (vertices s)"
   (REWRITE_TAC [vertices] THEN GEOM_TRANSLATE_TAC [])

  let VERTICES_LINEAR_IMAGE ← prove
   r"!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> vertices(IMAGE f s) = IMAGE f (vertices s)"
   (REWRITE_TAC [vertices, EXTREME_POINTS_OF_LINEAR_IMAGE])

  let EDGES_TRANSLATION ← prove
   r"!a s. edges (IMAGE (\x. a + x) s) = IMAGE (IMAGE (\x. a + x)) (edges s)"
   (REWRITE_TAC [edges] THEN GEOM_TRANSLATE_TAC [] THEN SET_TAC [])

  let EDGES_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> edges(IMAGE f s) = IMAGE (IMAGE f) (edges s)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [edges] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q r"x:real^N", ← q r"y:real^N"] THEN STRIP_TAC THEN
      REWRITE_TAC [IN_IMAGE] THEN ONCE_REWRITE_TAC [CONJ_SYM] THEN
      REWRITE_TAC [EXISTS_IN_GSPEC] THEN
      SUBGOAL_THEN (← q r"?v w. x = (f:real^M->real^N) v /\ y = f w") MP_TAC THENL
       [ASM_MESON_TAC [ENDS_IN_SEGMENT, EDGE_OF_IMP_SUBSET, SUBSET, IN_IMAGE],
        REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
        DISCH_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)],
      MAP_EVERY X_GEN_TAC [← q r"v:real^M", ← q r"w:real^M"] THEN DISCH_TAC THEN
      REWRITE_TAC [IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [← q r"(f:real^M->real^N) v", ← q r"(f:real^M->real^N) w"]] THEN
    REWRITE_TAC [IMAGE_CLAUSES] THEN
    ASM_MESON_TAC [EDGE_OF_LINEAR_IMAGE, CLOSED_SEGMENT_LINEAR_IMAGE])

  add_translation_invariants [VERTICES_TRANSLATION, EDGES_TRANSLATION]
  add_linear_invariants [VERTICES_LINEAR_IMAGE, EDGES_LINEAR_IMAGE]

  -- Fix the congruence rules as expected in Flyspeck (load-time effect).
  let bcs ← [
    r"(p <=> p') ==> (p' ==> (q <=> q')) ==> (p ==> q <=> p' ==> q')",
    r"(g <=> g')
    ==> (g' ==> t = t')
    ==> (~g' ==> e = e')
    ==> (if g then t else e) = (if g' then t' else e')",
    r"(!x. p x ==> f x = g x) ==> nsum {y | p y} (\i. f i) = nsum {y | p y} g",
    r"(!i. a <= i /\ i <= b ==> f i = g i)
    ==> nsum (a..b) (\i. f i) = nsum (a..b) g",
    r"(!x. x IN s ==> f x = g x) ==> nsum s (\i. f i) = nsum s g",
    r"(!x. p x ==> f x = g x) ==> sum {y | p y} (\i. f i) = sum {y | p y} g",
    r"(!i. a <= i /\ i <= b ==> f i = g i)
    ==> sum (a..b) (\i. f i) = sum (a..b) g",
    r"(!x. x IN s ==> f x = g x) ==> sum s (\i. f i) = sum s g",
    r"(!x. p x ==> f x = g x) ==> vsum {y | p y} (\i. f i) = vsum {y | p y} g",
    r"(!i. a <= i /\ i <= b ==> f i = g i)
    ==> vsum (a..b) (\i. f i) = vsum (a..b) g",
    r"(!x. x IN s ==> f x = g x) ==> vsum s (\i. f i) = vsum s g",
    r"(!x. p x ==> f x = g x)
    ==> product {y | p y} (\i. f i) = product {y | p y} g",
    r"(!i. a <= i /\ i <= b ==> f i = g i)
    ==> product (a..b) (\i. f i) = product (a..b) g",
    r"(!x. x IN s ==> f x = g x) ==> product s (\i. f i) = product s g",
    r"(!x. ~(x = a) ==> f x = g x)
    ==> (((\x. f x) --> l) (at a) <=> (g --> l) (at a))",
    r"(!x. ~(x = a) ==> f x = g x)
    ==> (((\x. f x) --> l) (at a within s) <=> (g --> l) (at a within s))"].mapM q
  let can_match (t1 t2 : term) : ExceptT String IO Bool :=
    tryWith (do let _ ← term_match [] t1 t2; pure true) (pure false)
  let equiv (t1 t2 : term) : ExceptT String IO Bool := do
    pure ((← can_match t1 t2) && (← can_match t2 t1))
  let congs' ← (← basic_congs).filterM (fun th => bcs.anyM (equiv (concl th)))
  set_basic_congs congs'

  pure { POLYHEDRON_COLLINEAR_FACES_STRONG, POLYHEDRON_COLLINEAR_FACES, vertices, edges,
         VERTICES_TRANSLATION, VERTICES_LINEAR_IMAGE, EDGES_TRANSLATION,
         EDGES_LINEAR_IMAGE }
end HolMultiLib.Flyspeck
