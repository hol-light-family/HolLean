/- ========================================================================= -/
/- Cross products in real^3.                                                 -/
/- ========================================================================= -/
/- File: HolMultiLib/Cross.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/cross.ml`, in the style of
  HolMultiLib/Convex.lean: pure, the proofs translated by hand, one `let` per
  OCaml `let`, in file order.  The load-time effects (`prioritize_vector()`,
  `parse_as_infix` and `add_linear_invariants`) are at their file positions.
  What cross.ml uses from earlier files is passed in `CrossDeps`;
  SessionMultiLib/Cross.lean supplies it.
-/

import HolMultiLib.Topology

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolMultiLib.Cross

/-- The theorems cross.ml uses, from the core library, vectors.ml,
    determinants.ml and topology.ml. -/
structure CrossThms where
  (ARITH CART_EQ CONJ_ASSOC DIMINDEX_3 EQ_SYM_EQ LAMBDA_BETA MONO_FORALL REAL_ENTIRE
   REAL_EQ_SQUARE_ABS REAL_LE_MUL REAL_MUL_LZERO REAL_POW_MUL REAL_SUB_0 REAL_SUB_RZERO o_DEF
   real_abs
   DOT_EQ_0 DOT_LZERO DOT_RZERO FORALL_3 LIFT_CMUL LIFT_SUB MATRIX_VECTOR_MUL_ASSOC
   MATRIX_VECTOR_MUL_LID MATRIX_VECTOR_MUL_RMUL MATRIX_WORKS NORM_CAUCHY_SCHWARZ_EQUAL
   NORM_EQ_0 NORM_POS_LE NORM_POW_2 ORTHOGONAL_REFL SUM_3 VECTOR_3 VECTOR_MUL_COMPONENT
   VECTOR_MUL_LID VECTOR_MUL_LNEG VECTOR_SUB_EQ basis bilinear dot linear matrix_vector_mul
   orthogonal transp vec vector_add vector_mul vector_neg vector_sub
   DET_3 ORTHOGONAL_TRANSFORMATION ORTHOGONAL_TRANSFORMATION_LINEAR
   ORTHOGONAL_TRANSFORMATION_MATRIX orthogonal_matrix rotation_matrix rotoinversion_matrix
   CONTINUOUS_COMPONENTWISE_LIFT CONTINUOUS_LIFT_COMPONENT_COMPOSE CONTINUOUS_MUL
   CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN CONTINUOUS_SUB : thm)
  deriving Inhabited

structure CrossDeps where
  new_definition : String → ExceptT String IO thm
  parse_as_infix : String × (Int × String) → IO Unit
  prioritize_vector : IO Unit
  add_linear_invariants : List thm → ExceptT String IO Unit
  ASM_MESON_TAC : List thm → tactic
  MESON_TAC : List thm → tactic
  REAL_ARITH_TAC : tactic
  REAL_RING : term → ExceptT String IO thm
  thms : CrossThms

/- ------------------------------------------------------------------------- -/
/- The definition; some simple automation; basic lemmas; preservation by     -/
/- rotation, or other orthogonal transformation up to sign; continuity; a    -/
/- weaker variant for more convenient interface with functions intended to   -/
/- work in 1 dimension.  (cross.ml 7-279)                                    -/
/- ------------------------------------------------------------------------- -/

structure CRS where
  cross : thm
  VEC3_TAC : tactic
  VEC3_RULE : term → ExceptT String IO thm
  ORTHOGONAL_CROSS : thm
  CROSS_LZERO : thm
  CROSS_RZERO : thm
  CROSS_SKEW : thm
  CROSS_REFL : thm
  CROSS_LADD : thm
  CROSS_RADD : thm
  CROSS_LMUL : thm
  CROSS_RMUL : thm
  CROSS_LNEG : thm
  CROSS_RNEG : thm
  CROSS_LSUB : thm
  CROSS_RSUB : thm
  CROSS_JACOBI : thm
  CROSS_LAGRANGE : thm
  CROSS_TRIPLE : thm
  DOT_CROSS_SELF : thm
  CROSS_COMPONENTS : thm
  CROSS_BASIS : thm
  CROSS_BASIS_NONZERO : thm
  CROSS_DOT_CANCEL : thm
  NORM_CROSS_DOT : thm
  DOT_CROSS_DET : thm
  CROSS_CROSS_DET : thm
  DOT_CROSS : thm
  NORM_CROSS : thm
  CROSS_EQ_0 : thm
  CROSS_0 : thm
  CROSS_EQ_SELF : thm
  NORM_AND_CROSS_EQ_0 : thm
  BILINEAR_CROSS : thm
  CROSS_MATRIX_MUL : thm
  CROSS_ORTHOGONAL_MATRIX : thm
  CROSS_ROTATION_MATRIX : thm
  CROSS_ROTOINVERSION_MATRIX : thm
  CROSS_ORTHOGONAL_TRANSFORMATION : thm
  CROSS_LINEAR_IMAGE : thm
  CONTINUOUS_CROSS : thm
  CONTINUOUS_ON_CROSS : thm
  CROSS_LINEAR_IMAGE_WEAK : thm
  deriving Inhabited

@[nospecialize]
def setupCRS [HolBase] (D : CrossDeps) : ExceptT String IO CRS := do
  let { new_definition, parse_as_infix, prioritize_vector, add_linear_invariants,
        ASM_MESON_TAC, MESON_TAC, REAL_ARITH_TAC, REAL_RING, .. } := D
  let { ARITH, CART_EQ, CONJ_ASSOC, DIMINDEX_3, EQ_SYM_EQ, LAMBDA_BETA, MONO_FORALL,
        REAL_ENTIRE, REAL_EQ_SQUARE_ABS, REAL_LE_MUL, REAL_MUL_LZERO, REAL_POW_MUL, REAL_SUB_0,
        REAL_SUB_RZERO, o_DEF, real_abs, DOT_EQ_0, DOT_LZERO, DOT_RZERO, FORALL_3, LIFT_CMUL,
        LIFT_SUB, MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID, MATRIX_VECTOR_MUL_RMUL,
        MATRIX_WORKS, NORM_CAUCHY_SCHWARZ_EQUAL, NORM_EQ_0, NORM_POS_LE, NORM_POW_2,
        ORTHOGONAL_REFL, SUM_3, VECTOR_3, VECTOR_MUL_COMPONENT, VECTOR_MUL_LID,
        VECTOR_MUL_LNEG, VECTOR_SUB_EQ, basis, bilinear, dot, linear, matrix_vector_mul,
        orthogonal, transp, vec, vector_add, vector_mul, vector_neg, vector_sub, DET_3,
        ORTHOGONAL_TRANSFORMATION, ORTHOGONAL_TRANSFORMATION_LINEAR,
        ORTHOGONAL_TRANSFORMATION_MATRIX, orthogonal_matrix, rotation_matrix,
        rotoinversion_matrix, CONTINUOUS_COMPONENTWISE_LIFT, CONTINUOUS_LIFT_COMPONENT_COMPOSE,
        CONTINUOUS_MUL, CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN, CONTINUOUS_SUB, .. } := D.thms

  prioritize_vector

  -- The definition.

  parse_as_infix ("cross", (20, "right"))

  let cross ← new_definition
   r"(a:real^3) cross (b:real^3) =
      vector [a$2 * b$3 - a$3 * b$2;
              a$3 * b$1 - a$1 * b$3;
              a$1 * b$2 - a$2 * b$1] :real^3"

  -- Some simple automation.

  let VEC3_TAC : tactic :=
    SIMP_TAC [CART_EQ, LAMBDA_BETA, FORALL_3, SUM_3, DIMINDEX_3, VECTOR_3,
              vector_add, vec, dot, cross, orthogonal, basis, DET_3,
              vector_neg, vector_sub, vector_mul, ARITH] THEN
    CONV_TAC (fun t => REAL_RING t)

  let VEC3_RULE (tm : term) : ExceptT String IO thm :=
    ExceptT.mk (HolCore.Tactics.prove HolBase.B tm VEC3_TAC)

  -- Basic lemmas.

  let ORTHOGONAL_CROSS ← prove
   r"!x y. orthogonal (x cross y) x /\ orthogonal (x cross y) y /\
           orthogonal x (x cross y) /\ orthogonal y (x cross y)"
   VEC3_TAC

  let CROSS_LZERO ← prove
   r"!x. (vec 0) cross x = vec 0"
   VEC3_TAC

  let CROSS_RZERO ← prove
   r"!x. x cross (vec 0) = vec 0"
   VEC3_TAC

  let CROSS_SKEW ← prove
   r"!x y. (x cross y) = --(y cross x)"
   VEC3_TAC

  let CROSS_REFL ← prove
   r"!x. x cross x = vec 0"
   VEC3_TAC

  let CROSS_LADD ← prove
   r"!x y z. (x + y) cross z = (x cross z) + (y cross z)"
   VEC3_TAC

  let CROSS_RADD ← prove
   r"!x y z. x cross (y + z) = (x cross y) + (x cross z)"
   VEC3_TAC

  let CROSS_LMUL ← prove
   r"!c x y. (c % x) cross y = c % (x cross y)"
   VEC3_TAC

  let CROSS_RMUL ← prove
   r"!c x y. x cross (c % y) = c % (x cross y)"
   VEC3_TAC

  let CROSS_LNEG ← prove
   r"!x y. (--x) cross y = --(x cross y)"
   VEC3_TAC

  let CROSS_RNEG ← prove
   r"!x y. x cross (--y) = --(x cross y)"
   VEC3_TAC

  let CROSS_LSUB ← prove
   r"!x y z. (x - y) cross z = x cross z - y cross z"
   VEC3_TAC

  let CROSS_RSUB ← prove
   r"!x y z. x cross (y - z) = x cross y - x cross z"
   VEC3_TAC

  let CROSS_JACOBI ← prove
   r"!x y z.
      x cross (y cross z) + y cross (z cross x) + z cross (x cross y) = vec 0"
   VEC3_TAC

  let CROSS_LAGRANGE ← prove
   r"!x y z. x cross (y cross z) = (x dot z) % y - (x dot y) % z"
   VEC3_TAC

  let CROSS_TRIPLE ← prove
   r"!x y z.  (x cross y) dot z = (y cross z) dot x"
   VEC3_TAC

  let DOT_CROSS_SELF ← prove
   r"(!x y. x dot (x cross y) = &0) /\
     (!x y. x dot (y cross x) = &0) /\
     (!x y. (x cross y) dot y = &0) /\
     (!x y. (y cross x) dot y = &0)"
   VEC3_TAC

  let CROSS_COMPONENTS ← prove
   r"!x y. (x cross y)$1 = x$2 * y$3 - y$2 * x$3 /\
           (x cross y)$2 = x$3 * y$1 - y$3 * x$1 /\
           (x cross y)$3 = x$1 * y$2 - y$1 * x$2"
   VEC3_TAC

  let CROSS_BASIS ← prove
   r"(basis 1) cross (basis 2) = basis 3 /\
     (basis 2) cross (basis 1) = --(basis 3) /\
     (basis 2) cross (basis 3) = basis 1 /\
     (basis 3) cross (basis 2) = --(basis 1) /\
     (basis 3) cross (basis 1) = basis 2 /\
     (basis 1) cross (basis 3) = --(basis 2)"
   VEC3_TAC

  let CROSS_BASIS_NONZERO ← prove
   r"!u. ~(u = vec 0)
         ==> ~(u cross basis 1 = vec 0) \/
             ~(u cross basis 2 = vec 0) \/
             ~(u cross basis 3 = vec 0)"
   VEC3_TAC

  let CROSS_DOT_CANCEL ← prove
   r"!x y z.
       x dot y = x dot z /\ x cross y = x cross z /\ ~(x = vec 0) ==> y = z"
   (ONCE_REWRITE_TAC [← GSYM VECTOR_SUB_EQ] THEN REWRITE_TAC [← GSYM DOT_EQ_0] THEN
    VEC3_TAC)

  let NORM_CROSS_DOT ← prove
   r"!x y. norm(x cross y) pow 2 + (x dot y) pow 2 = (norm(x) * norm y) pow 2"
   (REWRITE_TAC [REAL_POW_MUL, NORM_POW_2] THEN VEC3_TAC)

  let DOT_CROSS_DET ← prove
   r"!x y z. x dot (y cross z) = det(vector[x;y;z]:real^3^3)"
   VEC3_TAC

  let CROSS_CROSS_DET ← prove
   r"!w x y z. (w cross x) cross (y cross z) =
                  det(vector[w;x;z]:real^3^3) % y -
                  det(vector[w;x;y]:real^3^3) % z"
   VEC3_TAC

  let DOT_CROSS ← prove
   r"!w x y z. (w cross x) dot (y cross z) =
                  (w dot y) * (x dot z) - (w dot z) * (x dot y)"
   VEC3_TAC

  let NORM_CROSS ← prove
   r"!x y. norm(x cross y) pow 2 =
             norm(x) pow 2 * norm(y) pow 2 - (x dot y) pow 2"
   (REWRITE_TAC [NORM_POW_2] THEN VEC3_TAC)

  let CROSS_EQ_0 ← prove
   r"!x y. x cross y = vec 0 <=> collinear{vec 0,x,y}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM NORM_EQ_0] THEN
    ONCE_REWRITE_TAC [← REAL_RING (← q r"x = &0 <=> x pow 2 = &0")] THEN
    REWRITE_TAC [NORM_CROSS, REAL_SUB_0, ← GSYM REAL_POW_MUL] THEN
    REWRITE_TAC [← GSYM REAL_EQ_SQUARE_ABS, ← GSYM NORM_CAUCHY_SCHWARZ_EQUAL] THEN
    SIMP_TAC [real_abs, REAL_LE_MUL, NORM_POS_LE, EQ_SYM_EQ])

  let CROSS_0 ← prove
   r"(!x. vec 0 cross x = vec 0) /\
     (!x. x cross vec 0 = vec 0)"
   VEC3_TAC

  let CROSS_EQ_SELF ← prove
   r"(!x y. x cross y = x <=> x = vec 0) /\
     (!x y. x cross y = y <=> y = vec 0)"
   (MESON_TAC [ORTHOGONAL_CROSS, CROSS_0, ORTHOGONAL_REFL])

  let NORM_AND_CROSS_EQ_0 ← prove
   r"!x y. x dot y = &0 /\ x cross y = vec 0 <=> x = vec 0 \/ y = vec 0"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"x:real^3 = vec 0") THEN
    ASM_REWRITE_TAC [CROSS_0, DOT_LZERO] THEN ASM_CASES_TAC (← q r"y:real^3 = vec 0") THEN
    ASM_REWRITE_TAC [CROSS_0, DOT_RZERO] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC [← GSYM DOT_EQ_0, DOT_CROSS, REAL_MUL_LZERO] THEN
    ASM_REWRITE_TAC [REAL_SUB_RZERO, REAL_ENTIRE, DOT_EQ_0])

  let BILINEAR_CROSS ← prove
   r"bilinear(cross)"
   (REWRITE_TAC [linear, bilinear, CROSS_LADD, CROSS_RADD,
                 CROSS_LMUL, CROSS_RMUL])

  -- Preservation by rotation, or other orthogonal transformation up to sign.

  let CROSS_MATRIX_MUL ← prove
   r"!A x y. transp A ** ((A ** x) cross (A ** y)) = det A % (x cross y)"
   (SIMP_TAC [CART_EQ, DIMINDEX_3, FORALL_3, SUM_3, matrix_vector_mul,
              CROSS_COMPONENTS, LAMBDA_BETA, ARITH, transp, DET_3,
              VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC)

  let CROSS_ORTHOGONAL_MATRIX ← prove
   r"!A x y. orthogonal_matrix A
             ==> (A ** x) cross (A ** y) = det A % (A ** (x cross y))"
   (MP_TAC CROSS_MATRIX_MUL THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    REWRITE_TAC [orthogonal_matrix] THEN
    DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"matrix_vector_mul (A:real^3^3)")) THEN
    ASM_REWRITE_TAC [MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [MATRIX_VECTOR_MUL_RMUL])

  let CROSS_ROTATION_MATRIX ← prove
   r"!A x y. rotation_matrix A
             ==> (A ** x) cross (A ** y) =  A ** (x cross y)"
   (SIMP_TAC [rotation_matrix, CROSS_ORTHOGONAL_MATRIX, VECTOR_MUL_LID])

  let CROSS_ROTOINVERSION_MATRIX ← prove
   r"!A x y. rotoinversion_matrix A
             ==> (A ** x) cross (A ** y) =  --(A ** (x cross y))"
   (SIMP_TAC [rotoinversion_matrix, CROSS_ORTHOGONAL_MATRIX, VECTOR_MUL_LID,
              VECTOR_MUL_LNEG])

  let CROSS_ORTHOGONAL_TRANSFORMATION ← prove
   r"!f x y.
          orthogonal_transformation f
          ==> (f x) cross (f y) = det(matrix f) % f(x cross y)"
   (GEN_TAC THEN
    MP_TAC (← ISPEC (← q r"matrix(f:real^3->real^3)") CROSS_ORTHOGONAL_MATRIX) THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION_MATRIX,
                     ORTHOGONAL_TRANSFORMATION_LINEAR],
      ASM_SIMP_TAC [MATRIX_WORKS, ORTHOGONAL_TRANSFORMATION_LINEAR]])

  let CROSS_LINEAR_IMAGE ← prove
   r"!f x y. linear f /\ (!x. norm(f x) = norm x) /\ det(matrix f) = &1
             ==> (f x) cross (f y) = f(x cross y)"
   (SIMP_TAC [ORTHOGONAL_TRANSFORMATION, CONJ_ASSOC, VECTOR_MUL_LID,
              CROSS_ORTHOGONAL_TRANSFORMATION])

  -- Continuity.

  let CONTINUOUS_CROSS ← prove
   r"!net:(A)net f g.
          f continuous net /\ g continuous net
          ==> (\x. (f x) cross (g x)) continuous net"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [CONTINUOUS_COMPONENTWISE_LIFT] THEN
    REWRITE_TAC [cross, VECTOR_3, DIMINDEX_3, FORALL_3, LIFT_SUB] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_SUB THEN
    REWRITE_TAC [LIFT_CMUL] THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_MUL THEN
    ASM_SIMP_TAC [o_DEF, CONTINUOUS_LIFT_COMPONENT_COMPOSE])

  let CONTINUOUS_ON_CROSS ← prove
   r"!f:real^N->real^3 g s.
          f continuous_on s /\ g continuous_on s
          ==> (\x. (f x) cross (g x)) continuous_on s"
   (SIMP_TAC [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN, CONTINUOUS_CROSS])

  -- Prove a weaker variant for more convenient interface with functions
  -- intended to work in 1 dimension.

  let CROSS_LINEAR_IMAGE_WEAK ← prove
   r"!f x y. linear f /\ (!x. norm(f x) = norm x) /\
             (2 <= dimindex(:3) ==> det(matrix f) = &1)
             ==> (f x) cross (f y) = f(x cross y)"
   (REWRITE_TAC [DIMINDEX_3, ARITH] THEN
    SIMP_TAC [ORTHOGONAL_TRANSFORMATION, CONJ_ASSOC, VECTOR_MUL_LID,
              CROSS_ORTHOGONAL_TRANSFORMATION])

  add_linear_invariants [CROSS_LINEAR_IMAGE_WEAK]

  return { cross, VEC3_TAC, VEC3_RULE, ORTHOGONAL_CROSS, CROSS_LZERO, CROSS_RZERO, CROSS_SKEW,
           CROSS_REFL, CROSS_LADD, CROSS_RADD, CROSS_LMUL, CROSS_RMUL, CROSS_LNEG, CROSS_RNEG,
           CROSS_LSUB, CROSS_RSUB, CROSS_JACOBI, CROSS_LAGRANGE, CROSS_TRIPLE, DOT_CROSS_SELF,
           CROSS_COMPONENTS, CROSS_BASIS, CROSS_BASIS_NONZERO, CROSS_DOT_CANCEL,
           NORM_CROSS_DOT, DOT_CROSS_DET, CROSS_CROSS_DET, DOT_CROSS, NORM_CROSS, CROSS_EQ_0,
           CROSS_0, CROSS_EQ_SELF, NORM_AND_CROSS_EQ_0, BILINEAR_CROSS, CROSS_MATRIX_MUL,
           CROSS_ORTHOGONAL_MATRIX, CROSS_ROTATION_MATRIX, CROSS_ROTOINVERSION_MATRIX,
           CROSS_ORTHOGONAL_TRANSFORMATION, CROSS_LINEAR_IMAGE, CONTINUOUS_CROSS,
           CONTINUOUS_ON_CROSS, CROSS_LINEAR_IMAGE_WEAK }

end HolMultiLib.Cross
