/- ========================================================================= -/
/- The type "real^2" regarded as the complex numbers.                        -/
/-                                                                           -/
/- The algebra (the type, Re, Im, Cx, ii, the field operations, norms,       -/
/- conjugation, square roots, sums, products, roots of polynomials) is in    -/
/- Multivariate/complex_algebra.ml; this file adds the results that need     -/
/- topology.                                                                 -/
/- ========================================================================= -/
/- File: HolMultiLib/Complexes.lean

  Original (c) Copyright, John Harrison 1998-2008 / Valentina Bruno 2010.
  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/complexes.ml` (e7fbefd), in the
  style of HolMultiLib/Convex.lean: pure, the proofs translated by hand, one
  `let` per OCaml `let`, in file order.  complexes.ml `needs` convex.ml and
  complex_algebra.ml (HolMultiLib/ComplexAlgebra.lean) and keeps 12 lets
  that need topology; they were moved here unchanged from the earlier
  translation of the whole file.  The deps are complex_algebra.ml's
  (`ComplexAlgebraDeps`, which carries convex.ml's `ConvexDeps` and the
  theorems these lets use) and its bundles.  SessionMultiLib/Complexes.lean
  supplies them.
-/

import HolMultiLib.ComplexAlgebra

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax
open HolMultiLib.ComplexAlgebra

namespace HolMultiLib.Complexes

/- ------------------------------------------------------------------------- -/
/- Conjugation and multiplication as orthogonal transformations.             -/
/- (complexes.ml 18-91)                                                      -/
/- ------------------------------------------------------------------------- -/

structure CXL where
  ORTHOGONAL_TRANSFORMATION_CNJ : thm
  ORTHOGONAL_TRANSFORMATION_COMPLEX_MUL : thm
  COMPLEX_ORTHOGONAL_ROTATION : thm
  COMPLEX_ORTHOGONAL_ROTOINVERSION : thm
  COMPLEX_ORTHOGONAL_TRANSFORMATION : thm
  deriving Inhabited

@[nospecialize]
def setupCXL [HolBase] (D : ComplexAlgebraDeps) (BCXA : CXA) (BCXC : CXC) (BCXF : CXF) (BCXG : CXG) (BCXH : CXH) :
    ExceptT String IO CXL := do
  -- @@SCOPE BEGIN
  let { DET_2, MATRIX_COMPONENT, ORTHOGONAL_MATRIX_2, .. } := D.cpx
  let { MESON_TAC, REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV, REAL_RING, .. } := D.cvx
  let { ARITH, CONJ_ASSOC, DIMINDEX_2, EQ_TRANS, EXISTS_OR_THM, .. } := D.cvx.core1
  let { FUN_EQ_THM, .. } := D.cvx.core2
  let { LEFT_OR_DISTRIB, .. } := D.cvx.core3
  let { RIGHT_AND_EXISTS_THM, .. } := D.cvx.core5
  let { o_THM, .. } := D.cvx.core6
  let { DET_MUL, DET_ORTHOGONAL_MATRIX, orthogonal_transformation,
        ORTHOGONAL_TRANSFORMATION, ORTHOGONAL_TRANSFORMATION_COMPOSE,
        ORTHOGONAL_TRANSFORMATION_LINEAR, ORTHOGONAL_TRANSFORMATION_MATRIX,
        .. } := D.cvx.det
  let { MATRIX_COMPOSE, .. } := D.cvx.vec2
  let { complex_neg, CX_DEF, ii, IM, IM_DEF, RE, RE_DEF, .. } := BCXA
  let { COMPLEX_NORM_CX, .. } := BCXC
  let { COMPLEX_NORM_MUL, .. } := BCXF
  let { CNJ_CNJ, CNJ_CX, CNJ_II, CNJ_MUL, .. } := BCXG
  let { COMPLEX_BASIS, COMPLEX_LINEAR, DOT_CNJ, LINEAR_CNJ, LINEAR_COMPLEX_MUL, .. } := BCXH
  -- @@SCOPE END
  -- prioritize_complex() (complexes.ml 16)
  BCXA.prioritize_complex

  let ORTHOGONAL_TRANSFORMATION_CNJ ← prove
   r"orthogonal_transformation cnj"
   (REWRITE_TAC [orthogonal_transformation, LINEAR_CNJ, DOT_CNJ])

  let ORTHOGONAL_TRANSFORMATION_COMPLEX_MUL ← prove
   r"!c. orthogonal_transformation(\z. c * z) <=> norm c = &1"
   (REWRITE_TAC [ORTHOGONAL_TRANSFORMATION, LINEAR_COMPLEX_MUL] THEN
    GEN_TAC THEN REWRITE_TAC [COMPLEX_NORM_MUL] THEN
    REWRITE_TAC [← REAL_RING (← q r"c * v:real = v <=> c = &1 \/ v = &0")] THEN
    ASM_CASES_TAC (← q r"norm(c:complex) = &1") THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"Cx(&1)")) THEN REWRITE_TAC [COMPLEX_NORM_CX] THEN
    REAL_ARITH_TAC)

  let COMPLEX_ORTHOGONAL_ROTATION ← prove
   r"!f:complex->complex.
          orthogonal_transformation f /\ det(matrix f) = &1 <=>
          ?c. norm c = &1 /\ f = \z. c * z"
   (GEN_TAC THEN TRANS_TAC EQ_TRANS
     (← q r"(!z. norm(f z) = norm z) /\ (?c. f = \z:complex. c * z)") THEN
    CONJ_TAC THENL
     [REWRITE_TAC [COMPLEX_LINEAR] THEN
      ONCE_REWRITE_TAC [← TAUT (← q r"p /\ q /\ r <=> (q /\ p) /\ r")] THEN
      REWRITE_TAC [← GSYM ORTHOGONAL_TRANSFORMATION] THEN
      REWRITE_TAC [ORTHOGONAL_TRANSFORMATION_MATRIX] THEN
      REWRITE_TAC [← GSYM CONJ_ASSOC] THEN AP_TERM_TAC THEN
      REWRITE_TAC [ORTHOGONAL_MATRIX_2, DET_2] THEN CONV_TAC (fun t => REAL_RING t),
      REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN
      AP_TERM_TAC THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN
      X_GEN_TAC (← q r"c:complex") THEN REWRITE_TAC [] THEN
      ASM_CASES_TAC (← q r"f:complex->complex = \z. c * z") THEN
      ASM_REWRITE_TAC [COMPLEX_NORM_MUL] THEN
      REWRITE_TAC [← REAL_RING (← q r"c * v:real = v <=> c = &1 \/ v = &0")] THEN
      ASM_CASES_TAC (← q r"norm(c:complex) = &1") THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"Cx(&1)")) THEN REWRITE_TAC [COMPLEX_NORM_CX] THEN
      REAL_ARITH_TAC])

  let COMPLEX_ORTHOGONAL_ROTOINVERSION ← prove
   r"!f:complex->complex.
          orthogonal_transformation f /\ det(matrix f) = -- &1 <=>
          ?c. norm c = &1 /\ f = \z. c * cnj z"
   (GEN_TAC THEN
    SUBGOAL_THEN
     (← q r"!c. (f = \z. c * cnj z) = (f o cnj = \z. c * z)")
     (fun th => REWRITE_TAC [th])
    THENL
     [REWRITE_TAC [FUN_EQ_THM, o_THM] THEN MESON_TAC [CNJ_CNJ, CNJ_MUL],
      REWRITE_TAC [← GSYM COMPLEX_ORTHOGONAL_ROTATION]] THEN
    EQ_TAC THEN DISCH_TAC THENL
     [ALL_TAC,
      SUBGOAL_THEN (← q r"(f:complex->complex) = (f o cnj) o cnj") SUBST1_TAC THENL
       [REWRITE_TAC [FUN_EQ_THM, o_THM, CNJ_CNJ],
        POP_ASSUM MP_TAC THEN
        SPEC_TAC ((← q r"(f:complex->complex) o cnj"), (← q r"f:complex->complex")) THEN
        REPEAT STRIP_TAC]] THEN
    ASM_SIMP_TAC [ORTHOGONAL_TRANSFORMATION_COMPOSE, MATRIX_COMPOSE, DET_MUL,
      ORTHOGONAL_TRANSFORMATION_CNJ, ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
    SIMP_TAC [DET_2, MATRIX_COMPONENT, DIMINDEX_2, ARITH] THEN
    REWRITE_TAC [COMPLEX_BASIS, CNJ_II, CNJ_CX] THEN
    REWRITE_TAC [← GSYM IM_DEF, ← GSYM RE_DEF, IM, RE, CX_DEF, ii, complex_neg] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV)

  let COMPLEX_ORTHOGONAL_TRANSFORMATION ← prove
   r"!f:complex->complex.
          orthogonal_transformation f <=>
          ?c. norm c = &1 /\ ((f = \z. c * z) \/ (f = \z. c * cnj z))"
   (GEN_TAC THEN
    REWRITE_TAC [LEFT_OR_DISTRIB, EXISTS_OR_THM] THEN
    REWRITE_TAC [← GSYM COMPLEX_ORTHOGONAL_ROTATION,
                 ← GSYM COMPLEX_ORTHOGONAL_ROTOINVERSION] THEN
    MESON_TAC [DET_ORTHOGONAL_MATRIX, ORTHOGONAL_TRANSFORMATION_MATRIX])

  return { ORTHOGONAL_TRANSFORMATION_CNJ, ORTHOGONAL_TRANSFORMATION_COMPLEX_MUL, COMPLEX_ORTHOGONAL_ROTATION, COMPLEX_ORTHOGONAL_ROTOINVERSION, COMPLEX_ORTHOGONAL_TRANSFORMATION }

/- ------------------------------------------------------------------------- -/
/- Segments, convexity and the interior of the real numbers in C.            -/
/- (complexes.ml 93-164)                                                     -/
/- ------------------------------------------------------------------------- -/

structure CXM where
  REAL_SEGMENT : thm
  IN_SEGMENT_CX : thm
  IN_SEGMENT_CX_GEN : thm
  RE_POS_SEGMENT : thm
  CONVEX_REAL : thm
  INTERIOR_REAL : thm
  deriving Inhabited

@[nospecialize]
def setupCXM [HolBase] (D : ComplexAlgebraDeps) (BCXA : CXA) (BCXC : CXC) (BCXI : CXI) :
    ExceptT String IO CXM := do
  -- @@SCOPE BEGIN
  let { convex, .. } := D.cpx
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD,
        .. } := D.cvx
  let { ARITH, DIMINDEX_2, .. } := D.cvx.core1
  let { IN, .. } := D.cvx.core2
  let { IN_ELIM_THM, LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, .. } := D.cvx.core3
  let { REAL_ENTIRE, REAL_LE_ANTISYM, REAL_LE_LDIV_EQ, REAL_LE_MUL, REAL_LE_RDIV_EQ,
        REAL_LT_IMP_LE, .. } := D.cvx.core4
  let { REAL_POS, REAL_SUB_LE, .. } := D.cvx.core5
  let { EMPTY_INTERIOR_LOWDIM, .. } := D.cvx.top3
  let { segment, .. } := D.cvx.top5
  let { COMPLEX_EQ, .. } := BCXA
  let { COMPLEX_CMUL, CX_ADD, CX_INJ, CX_MUL, IM_ADD, IM_CMUL, RE_ADD, RE_CMUL, RE_CX,
        .. } := BCXC
  let { DIM_REAL, real, REAL, REAL_ADD, REAL_CX, REAL_MUL, .. } := BCXI
  -- @@SCOPE END

  let REAL_SEGMENT ← prove
   r"!a b x. x IN segment[a,b] /\ real a /\ real b ==> real x"
   (SIMP_TAC [segment, IN_ELIM_THM, real, COMPLEX_EQ, LEFT_AND_EXISTS_THM,
              LEFT_IMP_EXISTS_THM, IM_ADD, IM_CMUL] THEN
    REAL_ARITH_TAC)

  let IN_SEGMENT_CX ← prove
   r"!a b x. Cx(x) IN segment[Cx(a),Cx(b)] <=>
                  a <= x /\ x <= b \/ b <= x /\ x <= a"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [segment, IN_ELIM_THM] THEN
    REWRITE_TAC [COMPLEX_CMUL, ← GSYM CX_ADD, CX_INJ, ← GSYM CX_MUL] THEN
    ASM_CASES_TAC (← q r"a:real = b") THENL
     [ASM_REWRITE_TAC [← REAL_ARITH (← q r"(&1 - u) * b + u * b = b")] THEN
      ASM_CASES_TAC (← q r"x:real = b") THEN ASM_REWRITE_TAC [REAL_LE_ANTISYM] THEN
      EXISTS_TAC (← q r"&0") THEN REWRITE_TAC [REAL_POS],
      ALL_TAC] THEN
    EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"u:real")
       (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST1_TAC)) THEN
      REWRITE_TAC [← REAL_ARITH (← q r"a <= (&1 - u) * a + u * b <=> &0 <= u * (b - a)"),
        ← REAL_ARITH (← q r"b <= (&1 - u) * a + u * b <=> &0 <= (&1 - u) * (a - b)"),
        ← REAL_ARITH (← q r"(&1 - u) * a + u * b <= a <=> &0 <= u * (a - b)"),
        ← REAL_ARITH (← q r"(&1 - u) * a + u * b <= b <=> &0 <= (&1 - u) * (b - a)")] THEN
      DISJ_CASES_TAC (← REAL_ARITH (← q r"a <= b \/ b <= a")) THENL
       [DISJ1_TAC, DISJ2_TAC] THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REAL_ARITH_TAC,
      ALL_TAC] THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN (← q r"&0 < b - a") ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC,
        EXISTS_TAC (← q r"(x - a:real) / (b - a)")],
      SUBGOAL_THEN (← q r"&0 < a - b") ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC,
        EXISTS_TAC (← q r"(a - x:real) / (a - b)")]] THEN
    (CONJ_TAC THENL
      [ALL_TAC,
       UNDISCH_TAC (← q r"~(a:real = b)") THEN CONV_TAC (fun t => REAL_FIELD t)]) THEN
    ASM_SIMP_TAC [REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ] THEN
    ASM_REAL_ARITH_TAC)

  let IN_SEGMENT_CX_GEN ← prove
   r"!a b x.
          x IN segment[Cx a,Cx b] <=>
          Im(x) = &0 /\ (a <= Re x /\ Re x <= b \/ b <= Re x /\ Re x <= a)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM real] THEN
    ASM_CASES_TAC (← q r"real x") THENL
     [FIRST_X_ASSUM (SUBST1_TAC o SYM o REWRITE_RULE [REAL]) THEN
      REWRITE_TAC [IN_SEGMENT_CX, REAL_CX, RE_CX] THEN REAL_ARITH_TAC,
      ASM_MESON_TAC [REAL_SEGMENT, REAL_CX]])

  let RE_POS_SEGMENT ← prove
   r"!a b x. x IN segment[a,b] /\ &0 < Re a /\ &0 < Re b ==> &0 < Re x"
   (SIMP_TAC [segment, IN_ELIM_THM, real, COMPLEX_EQ, LEFT_AND_EXISTS_THM,
              LEFT_IMP_EXISTS_THM, RE_ADD, RE_CMUL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC (← REAL_ARITH
      (← q r"&0 <= x /\ &0 <= y /\ ~(x = &0 /\ y = &0) ==> &0 < x + y")) THEN
    ASM_SIMP_TAC [REAL_LE_MUL, REAL_SUB_LE, REAL_LT_IMP_LE, REAL_ENTIRE] THEN
    ASM_REAL_ARITH_TAC)

  let CONVEX_REAL ← prove
   r"convex real"
   (REWRITE_TAC [convex, IN, COMPLEX_CMUL] THEN
    SIMP_TAC [REAL_ADD, REAL_MUL, REAL_CX])

  let INTERIOR_REAL ← prove
   r"interior real = {}"
   (MATCH_MP_TAC EMPTY_INTERIOR_LOWDIM THEN
    REWRITE_TAC [DIM_REAL, DIMINDEX_2, ARITH])

  return { REAL_SEGMENT, IN_SEGMENT_CX, IN_SEGMENT_CX_GEN, RE_POS_SEGMENT, CONVEX_REAL, INTERIOR_REAL }

/- ------------------------------------------------------------------------- -/
/- Nonconstant polynomials are unbounded at infinity.                        -/
/- (complexes.ml 166-204)                                                    -/
/- ------------------------------------------------------------------------- -/

structure CXN where
  COMPLEX_POLYFUN_EXTREMAL : thm
  deriving Inhabited

@[nospecialize]
def setupCXN [HolBase] (D : ComplexAlgebraDeps) (BCXB : CXB) (BCXF : CXF) (BCXJ : CXJ) :
    ExceptT String IO CXN := do
  -- @@SCOPE BEGIN
  let { EVENTUALLY_AT_INFINITY, num_WF, NUMSEG_RREC, REAL_POW_1, REAL_POW_MONO, SUB_ADD,
        .. } := D.cpx
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, NORM_ARITH, REAL_ARITH, .. } := D.cvx
  let { ARITH, COND_ID, FINITE_NUMSEG, .. } := D.cvx.core1
  let { IN_INSERT, IN_NUMSEG, LE_1, NOT_IN_EMPTY, NUMSEG_CLAUSES, .. } := D.cvx.core3
  let { REAL_LE_LDIV_EQ, REAL_LE_TRANS, REAL_LT_DIV, REAL_MAX_LE, .. } := D.cvx.core4
  let { REAL_OF_NUM_LT, .. } := D.cvx.core5
  let { real_ge, .. } := D.cvx.core6
  let { VSUM_CLAUSES, .. } := D.cvx.vec4
  let { COMPLEX_ADD_LID, COMPLEX_MUL_LZERO, .. } := BCXB
  let { COMPLEX_NORM_MUL, COMPLEX_NORM_NZ, COMPLEX_NORM_POW, .. } := BCXF
  let { COMPLEX_POLYFUN_EXTREMAL_LEMMA, .. } := BCXJ
  -- @@SCOPE END

  let COMPLEX_POLYFUN_EXTREMAL ← prove
   r"!c n. (!k. k IN 1..n ==> c(k) = Cx(&0)) \/
           !B. eventually (\z. norm(vsum(0..n) (\i. c(i) * z pow i)) >= B)
                          at_infinity"
   (GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN
    ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [NUMSEG_CLAUSES, ARITH, NOT_IN_EMPTY] THEN
    MP_TAC (← ARITH_RULE (← q r"0 <= n")) THEN SIMP_TAC [← GSYM NUMSEG_RREC] THEN
    DISCH_THEN (K ALL_TAC : thm → tactic) THEN ASM_CASES_TAC (← q r"c(n:num) = Cx(&0)") THENL
     [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"n - 1")) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      ASM_SIMP_TAC [← GSYM NUMSEG_RREC, LE_1] THEN
      SIMP_TAC [IN_INSERT, VSUM_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
      ASM_REWRITE_TAC [COMPLEX_MUL_LZERO, COMPLEX_ADD_LID, COND_ID] THEN
      ASM_MESON_TAC [],
      DISJ2_TAC THEN MP_TAC (← ISPECL
        [← q r"c:num->complex", ← q r"n - 1", ← q r"norm(c(n:num):complex) / &2"]
        COMPLEX_POLYFUN_EXTREMAL_LEMMA) THEN ASM_SIMP_TAC [SUB_ADD, LE_1] THEN
      ASM_SIMP_TAC [COMPLEX_NORM_NZ, REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      SIMP_TAC [IN_INSERT, VSUM_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
      ASM_SIMP_TAC [← ARITH_RULE (← q r"~(n = 0) ==> ~(n <= n - 1)")] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"M:real")) THEN X_GEN_TAC (← q r"B:real") THEN
      REWRITE_TAC [EVENTUALLY_AT_INFINITY] THEN EXISTS_TAC
       (← q r"max M (max (&1) ((abs B + &1) / (norm(c(n:num):complex) / &2)))") THEN
      X_GEN_TAC (← q r"z:complex") THEN REWRITE_TAC [real_ge, REAL_MAX_LE] THEN
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"z:complex")) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← NORM_ARITH
       (← q r"abs b + &1 <= norm(y) - a ==> norm(x) <= a ==> b <= norm(y + x)")) THEN
      REWRITE_TAC [COMPLEX_NORM_MUL, COMPLEX_NORM_POW] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"c * x - c / &2 * x = x * c / &2")] THEN
      ASM_SIMP_TAC [← GSYM REAL_LE_LDIV_EQ, COMPLEX_NORM_NZ, REAL_LT_DIV,
                    REAL_OF_NUM_LT, ARITH] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (← q r"norm(z:complex) pow 1") THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC [REAL_POW_1], ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_SIMP_TAC [LE_1]])

  return { COMPLEX_POLYFUN_EXTREMAL }

end HolMultiLib.Complexes
