/- ========================================================================= -/
/- Proof that Tarski's axioms for geometry hold in Euclidean space.          -/
/- ========================================================================= -/
/- File: HolMultiLib/Tarski.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/tarski.ml`, in the style of
  HolMultiLib/Convex.lean: pure, the proofs translated by hand, one `let` per
  OCaml `let`, in file order.  tarski.ml needs convex.ml, so it is given
  convex.ml's `ConvexDeps` and the few further theorems in `TarskiThms`;
  SessionMultiLib/Tarski.lean supplies them.
-/

import HolMultiLib.Convex

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolMultiLib.Tarski

/-- The theorems tarski.ml uses that convex.ml's deps do not carry. -/
structure TarskiThms where
  (REAL_EQ_MUL_LCANCEL REAL_EQ_MUL_RCANCEL BETWEEN_EXISTS_EXTENSION BETWEEN_REFL_EQ
   BETWEEN_TRANSLATION FORALL_2 between BETWEEN_LINEAR_IMAGE_EQ
   RIGID_TRANSFORMATION_BETWEEN_3 : thm)
  deriving Inhabited

/- ------------------------------------------------------------------------- -/
/- Axioms 1 to 11.  (tarski.ml 12-262)                                       -/
/- ------------------------------------------------------------------------- -/

structure TAR where
  TARSKI_AXIOM_1_EUCLIDEAN : thm
  TARSKI_AXIOM_2_EUCLIDEAN : thm
  TARSKI_AXIOM_3_EUCLIDEAN : thm
  TARSKI_AXIOM_4_EUCLIDEAN : thm
  TARSKI_AXIOM_5_EUCLIDEAN : thm
  TARSKI_AXIOM_6_EUCLIDEAN : thm
  TARSKI_AXIOM_7_EUCLIDEAN : thm
  TARSKI_AXIOM_8_EUCLIDEAN : thm
  TARSKI_AXIOM_9_EUCLIDEAN : thm
  TARSKI_AXIOM_10_EUCLIDEAN : thm
  TARSKI_AXIOM_11_EUCLIDEAN : thm
  deriving Inhabited

@[nospecialize]
def setupTAR [HolBase] (D : HolMultiLib.Convex.ConvexDeps) (T : TarskiThms) :
    ExceptT String IO TAR := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD, REAL_RING,
        SET_TAC, REAL_RAT_REDUCE_CONV, VECTOR_ARITH, NORM_ARITH, NORM_ARITH_TAC,
        GEOM_BASIS_MULTIPLE_TAC, GEOM_NORMALIZE_TAC, GEOM_ORIGIN_TAC, .. } := D
  let { ARITH, CART_EQ, CONJ_SYM, DE_MORGAN_THM, DIMINDEX_2, DIMINDEX_GE_1, .. } := D.core1
  let { FORALL_IN_IMAGE, IMAGE_EQ_EMPTY, IMP_CONJ, IMP_IMP, .. } := D.core2
  let { IN_ELIM_THM, IN_IMAGE, LEFT_IMP_EXISTS_THM, LE_REFL, MEMBER_NOT_EMPTY, NOT_FORALL_THM,
        NOT_IMP, NOT_IN_EMPTY, REAL_ABS_DIV, REAL_ABS_REFL, REAL_ADD_LDISTRIB,
        REAL_DIV_RMUL, .. } := D.core3
  let { REAL_LE_ADD, REAL_LE_DIV, REAL_LE_INV_EQ, REAL_LE_LDIV_EQ, REAL_LE_MUL,
        REAL_LE_RDIV_EQ, .. } := D.core4
  let { REAL_MUL_LINV, REAL_MUL_RID, REAL_POS, REAL_SUB_REFL, RIGHT_FORALL_IMP_THM, SUBSET,
        SUBSET_IMAGE, .. } := D.core5
  let { SUP, UNWIND_THM2, real_abs, .. } := D.core6
  let { BASIS_COMPONENT, BETWEEN_REFL, BETWEEN_SYM, COLLINEAR_3_2D, COLLINEAR_BETWEEN_CASES,
        DIST_0, DIST_EQ_0, DIST_POS_LE, DIST_SYM, DOT_2, .. } := D.vec1
  let { NORM_BASIS, NORM_EQ, NORM_EQ_0, .. } := D.vec2
  let { NORM_MUL, NORM_NEG, NORM_POS_LE, NORM_POW_2, REAL_ABS_NORM, .. } := D.vec3
  let { VECTOR_ADD_COMPONENT, VECTOR_ADD_LID, VECTOR_ADD_RID, VECTOR_CHOOSE_SIZE,
        VECTOR_MUL_ASSOC, VECTOR_MUL_COMPONENT, VECTOR_MUL_EQ_0, VECTOR_MUL_LID,
        VECTOR_MUL_LZERO, VECTOR_MUL_RZERO, VECTOR_SUB_COMPONENT, VECTOR_SUB_EQ,
        VECTOR_SUB_LDISTRIB, VECTOR_SUB_LZERO, VECTOR_SUB_RDISTRIB, VEC_COMPONENT, dist, .. } :=
    D.vec4
  let { ORTHOGONAL_TRANSFORMATION_INJECTIVE, ORTHOGONAL_TRANSFORMATION_ISOMETRY,
        orthogonal_transformation, .. } := D.det
  let { BETWEEN_IN_SEGMENT, .. } := D.top1
  let { IN_SEGMENT, .. } := D.top4
  let { REAL_EQ_MUL_LCANCEL, REAL_EQ_MUL_RCANCEL, BETWEEN_EXISTS_EXTENSION, BETWEEN_REFL_EQ,
        BETWEEN_TRANSLATION, FORALL_2, between, BETWEEN_LINEAR_IMAGE_EQ,
        RIGID_TRANSFORMATION_BETWEEN_3, .. } := T
  -- @@SCOPE END

  D.prioritize_real

  -- Axiom 1 (reflexivity for equidistance).

  let TARSKI_AXIOM_1_EUCLIDEAN ← prove
   r"!a b:real^2. dist(a,b) = dist(b,a)"
   NORM_ARITH_TAC

  -- Axiom 2 (transitivity for equidistance).

  let TARSKI_AXIOM_2_EUCLIDEAN ← prove
   r"!a b p q r s.
          dist(a,b) = dist(p,q) /\ dist(a,b) = dist(r,s)
          ==> dist(p,q) = dist(r,s)"
   REAL_ARITH_TAC

  -- Axiom 3 (identity for equidistance).

  let TARSKI_AXIOM_3_EUCLIDEAN ← prove
   r"!a b c. dist(a,b) = dist(c,c) ==> a = b"
   NORM_ARITH_TAC

  -- Axiom 4 (segment construction).

  let TARSKI_AXIOM_4_EUCLIDEAN ← prove
   r"!a q b c:real^2. ?x:real^2. between a (q,x) /\ dist(a,x) = dist(b,c)"
   (GEOM_ORIGIN_TAC (← q r"a:real^2") THEN REPEAT GEN_TAC THEN
    REWRITE_TAC [DIST_0] THEN ASM_CASES_TAC (← q r"q:real^2 = vec 0") THENL
     [ASM_SIMP_TAC [BETWEEN_REFL, VECTOR_CHOOSE_SIZE, DIST_POS_LE],
      EXISTS_TAC (← q r"--(dist(b:real^2,c) / norm(q) % q):real^2") THEN
      REWRITE_TAC [between, DIST_0] THEN
      REWRITE_TAC [dist, NORM_MUL, NORM_NEG, REAL_ABS_DIV, REAL_ABS_NORM,
                   ← VECTOR_ARITH (← q r"q - --(a % q) = (&1 + a) % q")] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC (← REAL_RING (← q r"a = &1 + b ==> a * q = q + b * q")) THEN
        SIMP_TAC [REAL_ABS_REFL, REAL_POS, REAL_LE_ADD, REAL_LE_DIV, NORM_POS_LE],
        ASM_SIMP_TAC [REAL_DIV_RMUL, NORM_EQ_0]]])

  -- Axiom 5 (five-segments axiom).

  let TARSKI_AXIOM_5_EUCLIDEAN ← do
    let lemma ← prove
     r"!a b x y:real^N.
        ~(b = a) /\ between b (a,x) /\ between b (a,y) /\ dist(b,x) = dist(b,y)
        ==> x = y"
     (REPEAT STRIP_TAC THEN REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP (← REWRITE_RULE
       [IMP_CONJ] BETWEEN_EXISTS_EXTENSION))) THEN ASM_SIMP_TAC [] THEN
      REPEAT STRIP_TAC THEN UNDISCH_TAC (← q r"dist(b:real^N,x) = dist(b,y)") THEN
      ASM_REWRITE_TAC [← NORM_ARITH (← q r"dist(b:real^N,b + x) = norm x"), NORM_MUL] THEN
      ASM_SIMP_TAC [REAL_EQ_MUL_RCANCEL, NORM_EQ_0, real_abs, VECTOR_SUB_EQ])
    prove
     r"!a b c x:real^2 a' b' c' x':real^2.
          ~(a = b) /\
          dist(a,b) = dist(a',b') /\
          dist(a,c) = dist(a',c') /\
          dist(b,c) = dist(b',c') /\
          between b (a,x) /\ between b' (a',x') /\ dist(b,x) = dist(b',x')
          ==> dist(c,x) = dist(c',x')"
     (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL
       [← q r"a:real^2", ← q r"b:real^2", ← q r"c:real^2", ← q r"a':real^2",
        ← q r"b':real^2", ← q r"c':real^2"]
       RIGID_TRANSFORMATION_BETWEEN_3) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [DIST_EQ_0, DIST_SYM], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"k:real^2")
       (X_CHOOSE_THEN (← q r"f:real^2->real^2") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
      DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      SUBGOAL_THEN (← q r"x' = k + (f:real^2->real^2) x") SUBST1_TAC THENL
       [MATCH_MP_TAC lemma THEN MAP_EVERY EXISTS_TAC
          [← q r"k + (f:real^2->real^2) a", ← q r"k + (f:real^2->real^2) b"],
        ALL_TAC] THEN
      ASM_REWRITE_TAC [← NORM_ARITH (← q r"dist(a + x:real^N,a + y) = dist(x,y)"),
        BETWEEN_TRANSLATION, ← VECTOR_ARITH (← q r"a + x:real^N = a + y <=> x = y")] THEN
      ASM_MESON_TAC [BETWEEN_TRANSLATION, orthogonal_transformation,
                     ← NORM_ARITH (← q r"dist(a + x:real^N,a + y) = dist(x,y)"),
                     ORTHOGONAL_TRANSFORMATION_ISOMETRY, BETWEEN_LINEAR_IMAGE_EQ,
                     DIST_EQ_0, ORTHOGONAL_TRANSFORMATION_INJECTIVE])

  -- Axiom 6 (identity for between-ness).

  let TARSKI_AXIOM_6_EUCLIDEAN ← prove
   r"!a b. between b (a,a) ==> a = b"
   (SIMP_TAC [BETWEEN_REFL_EQ])

  -- Axiom 7 (Pasch's axiom).

  let TARSKI_AXIOM_7_EUCLIDEAN ← prove
   r"!a b c p q:real^2.
          between p (a,c) /\ between q (b,c)
          ==> ?x. between x (p,b) /\ between x (q,a)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"q:real^2 = c") THENL
     [ASM_MESON_TAC [BETWEEN_REFL, BETWEEN_SYM], POP_ASSUM MP_TAC] THEN
    ASM_CASES_TAC (← q r"p:real^2 = a /\ b:real^2 = q") THENL
     [ASM_MESON_TAC [BETWEEN_REFL, BETWEEN_SYM], POP_ASSUM MP_TAC] THEN
    GEOM_ORIGIN_TAC (← q r"a:real^2") THEN GEOM_NORMALIZE_TAC (← q r"q:real^2") THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC [CONJ_SYM] THEN REWRITE_TAC [BETWEEN_REFL_EQ] THEN
      REWRITE_TAC [UNWIND_THM2, between, DIST_0] THEN NORM_ARITH_TAC,
      ALL_TAC] THEN
    GEOM_BASIS_MULTIPLE_TAC 1 (← q r"q:real^2") THEN SIMP_TAC
     [NORM_MUL, NORM_BASIS, real_abs, DIMINDEX_2, ARITH, REAL_MUL_RID] THEN
    GEN_TAC THEN REPEAT (DISCH_THEN (K ALL_TAC : thm → tactic)) THEN
    SIMP_TAC [VECTOR_MUL_LID] THEN
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [BETWEEN_SYM] THEN DISCH_TAC THEN
    DISCH_TAC THEN DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC o
       REWRITE_RULE [BETWEEN_IN_SEGMENT, IN_SEGMENT])
     (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ] BETWEEN_EXISTS_EXTENSION))) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"e:real") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [BETWEEN_IN_SEGMENT, IN_SEGMENT] THEN
    REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_ADD_LID] THEN
    SUBGOAL_THEN (← q r"&0 < &1 - d + e") ASSUME_TAC THENL
     [ASM_CASES_TAC (← q r"d = &1 /\ e = &0") THENL [ALL_TAC, ASM_REAL_ARITH_TAC] THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o
        check (fun (th : thm) => _root_.is_eq (concl th)))) THEN
      ASM_REWRITE_TAC [REAL_SUB_REFL, VECTOR_MUL_LZERO, VECTOR_MUL_RZERO] THEN
      ASM_REWRITE_TAC [VECTOR_ADD_RID, IMP_IMP],
      EXISTS_TAC (← q r"(&1 - d + e - d * e) / (&1 - d + e) % basis 1:real^2") THEN
      CONJ_TAC THENL
       [EXISTS_TAC (← q r"e / (&1 - d + e)") THEN
        ASM_SIMP_TAC [REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ] THEN
        REPEAT (CONJ_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC]) THEN
        SIMP_TAC [CART_EQ, DIMINDEX_2, FORALL_2, BASIS_COMPONENT, VEC_COMPONENT,
         ARITH, VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT,
         VECTOR_SUB_COMPONENT] THEN
        UNDISCH_TAC (← q r"&0 < &1 - d + e") THEN CONV_TAC (fun t => REAL_FIELD t),
        EXISTS_TAC (← q r"(&1 - d + e - d * e) / (&1 - d + e)") THEN
        ASM_SIMP_TAC [REAL_LE_LDIV_EQ, REAL_LE_RDIV_EQ] THEN
        SUBGOAL_THEN (← q r"&0 <= (&1 - d) * (&1 + e) /\ &0 <= d * e") MP_TAC THENL
         [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL, ALL_TAC] THEN
        ASM_REAL_ARITH_TAC]])

  -- Axiom 8 (lower 2-dimensional axiom).

  let TARSKI_AXIOM_8_EUCLIDEAN ← prove
   r"?a b c:real^2. ~between b (a,c) /\ ~between c (b,a) /\ ~between a (c,b)"
   (REWRITE_TAC [← GSYM DE_MORGAN_THM] THEN ONCE_REWRITE_TAC [BETWEEN_SYM] THEN
    REWRITE_TAC [← GSYM COLLINEAR_BETWEEN_CASES, COLLINEAR_3_2D] THEN
    MAP_EVERY EXISTS_TAC
     [← q r"vec 0:real^2", ← q r"basis 1:real^2", ← q r"basis 2:real^2"] THEN
    SIMP_TAC [BASIS_COMPONENT, VEC_COMPONENT, DIMINDEX_2, ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV)

  -- Axiom 9 (upper 2-dimensional axiom).

  let TARSKI_AXIOM_9_EUCLIDEAN ← prove
   r"!p q a b c:real^2.
          ~(p = q) /\
          dist(a,p) = dist(a,q) /\ dist(b,p) = dist(b,q) /\ dist(c,p) = dist(c,q)
          ==> between b (a,c) \/ between c (b,a) \/ between a (c,b)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [BETWEEN_SYM] THEN
    REWRITE_TAC [← GSYM COLLINEAR_BETWEEN_CASES] THEN
    REWRITE_TAC [dist, NORM_EQ, ← NORM_ARITH
      (← q r"~(p = q) <=> ~(norm(p - q) = &0)")] THEN
    ONCE_REWRITE_TAC [← REAL_RING (← q r"~(x = &0) <=> ~(x pow 2 = &0)")] THEN
    REWRITE_TAC [NORM_POW_2, COLLINEAR_3_2D] THEN
    REWRITE_TAC [DOT_2, VECTOR_SUB_COMPONENT] THEN
    CONV_TAC (fun t => REAL_FIELD t))

  -- Axiom 10 (Euclidean axiom).

  let TARSKI_AXIOM_10_EUCLIDEAN ← prove
   r"!a b c d t:real^N.
          between d (a,t) /\ between d (b,c) /\ ~(a = d)
          ==> ?x y. between b (a,x) /\ between c (a,y) /\ between t (x,y)"
   (REPEAT GEN_TAC THEN GEOM_ORIGIN_TAC (← q r"a:real^N") THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"vec 0:real^N", ← q r"d:real^N", ← q r"t:real^N"]
          BETWEEN_EXISTS_EXTENSION) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM, ← VECTOR_ARITH
     (← q r"d + u % (d - vec 0):real^N = (&1 + u) % d")] THEN
    X_GEN_TAC (← q r"u:real") THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [← q r"(&1 + u) % b:real^N", ← q r"(&1 + u) % c:real^N"] THEN
    ASM_REWRITE_TAC [between, dist, ← GSYM VECTOR_SUB_LDISTRIB] THEN
    ASM_REWRITE_TAC [VECTOR_SUB_LZERO, NORM_NEG,
                     ← VECTOR_ARITH (← q r"b - (&1 + u) % b:real^N = --(u % b)")] THEN
    ASM_SIMP_TAC [NORM_MUL, REAL_LE_ADD, REAL_POS, real_abs] THEN
    REWRITE_TAC [← GSYM REAL_ADD_LDISTRIB, REAL_EQ_MUL_LCANCEL] THEN
    ASM_REWRITE_TAC [← GSYM dist, ← GSYM between] THEN REAL_ARITH_TAC)

  -- Axiom 11 (Continuity).

  let TARSKI_AXIOM_11_EUCLIDEAN ← prove
   r"!X Y:real^2->bool.
          (?a. !x y. x IN X /\ y IN Y ==> between x (a,y))
          ==> (?b. !x y. x IN X /\ y IN Y ==> between b (x,y))"
   (REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN GEOM_ORIGIN_TAC (← q r"a:real^2") THEN
    REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"!x:real^2. x IN X ==> x = vec 0") THENL
     [ASM_MESON_TAC [BETWEEN_REFL], POP_ASSUM MP_TAC] THEN
    ASM_CASES_TAC (← q r"Y:real^2->bool = {}") THEN ASM_REWRITE_TAC [NOT_IN_EMPTY] THEN
    SUBGOAL_THEN (← q r"?c:real^2. c IN Y") (CHOOSE_THEN MP_TAC) THENL
     [ASM SET_TAC [], REPEAT (POP_ASSUM MP_TAC)] THEN
    GEOM_BASIS_MULTIPLE_TAC 1 (← q r"c:real^2") THEN
    X_GEN_TAC (← q r"c:real") THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    DISCH_TAC THEN DISCH_TAC THEN REWRITE_TAC [NOT_FORALL_THM, NOT_IMP] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"z:real^2") STRIP_ASSUME_TAC) THEN
    DISCH_THEN (LABEL_TAC "*") THEN
    SUBGOAL_THEN (← q r"X SUBSET IMAGE (\c. c % basis 1:real^2) {c | &0 <= c} /\
                  Y SUBSET IMAGE (\c. c % basis 1:real^2) {c | &0 <= c}")
    MP_TAC THENL
     [REWRITE_TAC [SUBSET, IN_IMAGE, IN_ELIM_THM] THEN
      MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
       [X_GEN_TAC (← q r"x:real^2") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o SPECL
         [← q r"x:real^2", ← q r"c % basis 1:real^2"]) THEN
        ASM_REWRITE_TAC [BETWEEN_IN_SEGMENT, IN_SEGMENT] THEN
        REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_ADD_LID, IN_ELIM_THM] THEN
        ASM_MESON_TAC [VECTOR_MUL_ASSOC, REAL_LE_MUL],
        DISCH_THEN (MP_TAC o SPEC (← q r"z:real^2")) THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") STRIP_ASSUME_TAC) THEN
        UNDISCH_TAC (← q r"~(z:real^2 = vec 0)") THEN
        ASM_REWRITE_TAC [VECTOR_MUL_EQ_0, DE_MORGAN_THM] THEN
        STRIP_TAC THEN X_GEN_TAC (← q r"y:real^2") THEN DISCH_TAC THEN
        REMOVE_THEN "*" (MP_TAC o SPECL [← q r"z:real^2", ← q r"y:real^2"]) THEN
        ASM_REWRITE_TAC [VECTOR_MUL_ASSOC] THEN
        REWRITE_TAC [BETWEEN_IN_SEGMENT, IN_SEGMENT] THEN
        REWRITE_TAC [VECTOR_MUL_RZERO, VECTOR_ADD_LID, IN_ELIM_THM] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"u:real") MP_TAC) THEN
        ASM_CASES_TAC (← q r"u = &0") THEN
        ASM_REWRITE_TAC [VECTOR_MUL_LZERO, VECTOR_MUL_EQ_0] THEN
        STRIP_TAC THEN EXISTS_TAC (← q r"inv(u) * d:real") THEN
        ASM_REWRITE_TAC [← GSYM VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC [REAL_LE_MUL, REAL_LE_INV_EQ, VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC [REAL_MUL_LINV, VECTOR_MUL_LID]],
      REWRITE_TAC [SUBSET_IMAGE] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
      DISCH_THEN (CONJUNCTS_THEN2
       (X_CHOOSE_THEN (← q r"s:real->bool") STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN (← q r"t:real->bool") STRIP_ASSUME_TAC)) THEN
      REMOVE_THEN "*" MP_TAC THEN
      ASM_REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE] THEN
      DISCH_THEN (fun th => tactic_of do
        pure (EXISTS_TAC (← q r"sup s % basis 1 :real^2") THEN MP_TAC th)) THEN
      REWRITE_TAC [between, dist, ← NORM_ARITH (← q r"norm(vec 0 - x) = norm x")] THEN
      REWRITE_TAC [← GSYM VECTOR_SUB_RDISTRIB, NORM_MUL] THEN
      SIMP_TAC [NORM_BASIS, DIMINDEX_GE_1, LE_REFL, REAL_MUL_RID] THEN
      ASM_SIMP_TAC [← REAL_ARITH
       (← q r"&0 <= x /\ &0 <= y ==> (abs y = abs x + abs(x - y) <=> x <= y)")] THEN
      DISCH_TAC THEN X_GEN_TAC (← q r"x:real") THEN DISCH_TAC THEN
      X_GEN_TAC (← q r"y:real") THEN DISCH_TAC THEN MATCH_MP_TAC (← REAL_ARITH
       (← q r"x <= s /\ s <= y ==> abs(x - y) = abs(x - s) + abs(s - y)")) THEN
      MP_TAC (← SPEC (← q r"s:real->bool") SUP) THEN
      ASM_MESON_TAC [IMAGE_EQ_EMPTY, MEMBER_NOT_EMPTY]])

  return { TARSKI_AXIOM_1_EUCLIDEAN, TARSKI_AXIOM_2_EUCLIDEAN, TARSKI_AXIOM_3_EUCLIDEAN,
           TARSKI_AXIOM_4_EUCLIDEAN, TARSKI_AXIOM_5_EUCLIDEAN, TARSKI_AXIOM_6_EUCLIDEAN,
           TARSKI_AXIOM_7_EUCLIDEAN, TARSKI_AXIOM_8_EUCLIDEAN, TARSKI_AXIOM_9_EUCLIDEAN,
           TARSKI_AXIOM_10_EUCLIDEAN, TARSKI_AXIOM_11_EUCLIDEAN }

end HolMultiLib.Tarski
