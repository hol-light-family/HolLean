/- ========================================================================= -/
/- The type "real^2" regarded as the complex numbers: the algebra, which     -/
/- needs only Multivariate/vectors.ml. The results that need topology are in -/
/- Multivariate/complexes.ml, which loads this file.                         -/
/- ========================================================================= -/
/- File: HolMultiLib/ComplexAlgebra.lean

  Original (c) Copyright, John Harrison 1998-2008 / Valentina Bruno 2010.
  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/complex_algebra.ml`, in the
  style of HolMultiLib/Convex.lean: pure, the proofs translated by hand, one
  `let` per OCaml `let`, in file order.  The load-time effects
  (`new_type_abbrev`, `prioritize_complex()` and `extend_basic_congs`) are at
  their file positions.  HOL Light split this file off complexes.ml in
  e7fbefd (2026-11); until then its 322 lets were part of complexes.ml.
  What complex_algebra.ml uses from earlier files is passed in
  `ComplexAlgebraDeps`: what convex.ml was given comes in its `ConvexDeps`
  (field `cvx`), and the rest in `CpxThms` and the procedure fields.
  complex_algebra.ml itself needs only vectors.ml; the deps come through
  convex.ml's because HOL Light loads it after convex.ml (make_complex.ml,
  and complexes.ml's `needs`), so SessionMultiLib/ComplexAlgebra.lean, which
  supplies them, imports SessionMultiLib.Convex.
-/

import HolMultiLib.Convex

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolMultiLib.ComplexAlgebra

/-- The theorems complex_algebra.ml uses that convex.ml did not, from the
    core library, vectors.ml and determinants.ml; and those the lets now in
    complexes.ml use from topology.ml and convex.ml (NUMSEG_RREC
    REAL_POW_MONO num_WF DET_2 ORTHOGONAL_MATRIX_2 EVENTUALLY_AT_INFINITY
    MATRIX_COMPONENT convex), which HolMultiLib/Complexes.lean reads from
    here. -/
structure CpxThms where
  (ADD_CLAUSES EQ_ADD_RCANCEL EVEN INFINITE ITERATE_CLAUSES ITERATE_EQ ITERATE_EQ_NEUTRAL
   ITERATE_IMAGE ITERATE_PAIR ITERATE_REFLECT ITERATE_SUPERSET ITERATE_UNION LE_0 NOT_SUC
   NUMSEG_LREC NUMSEG_RREC POW_2_SQRT_ABS PRODUCT_CLAUSES REAL_ABS_ZERO REAL_ADD_SUB
   REAL_DIFFSQ REAL_LE_LCANCEL_IMP REAL_LE_SQUARE REAL_LE_SUB_RADD REAL_LT_RMUL_EQ
   REAL_MUL_RINV_UNIQ REAL_POW_1 REAL_POW_ADD REAL_POW_EQ_1 REAL_POW_MONO REAL_SGN_DIV
   REAL_SOS_EQ_0 REAL_SUB_LZERO SELECT_UNIQUE SQRT_MONO_LE SQRT_MONO_LT SQRT_POS_LT SUB_0
   SUB_ADD SUB_REFL SUC_SUB1 SUM_SUBSET monoidal neutral num_WF real_sgn real_sub
   DET_2 ORTHOGONAL_MATRIX_2 EVENTUALLY_AT_INFINITY
   EUCLIDEAN_SPACE_INFINITE FORALL_2 L1_LE_NORM MATRIX_COMPONENT MATRIX_VECTOR_MUL
   MATRIX_VECTOR_MUL_COMPONENT SUM_2 VECTOR_2 VSUM_CLAUSES_LEFT VSUM_COMPONENT
   VSUM_CONST_NUMSEG VSUM_DIFFS_ALT VSUM_EQ_GENERAL_INVERSES VSUM_EQ_NUMSEG VSUM_NORM
   VSUM_OFFSET_0 VSUM_SUB_NUMSEG VSUM_TRIV_NUMSEG VSUM_VSUM_PRODUCT matrix vector_norm
   convex : thm)
  deriving Inhabited

structure ComplexAlgebraDeps where
  /-- What convex.ml was given. -/
  cvx : HolMultiLib.Convex.ConvexDeps
  -- definitions and parser state
  define : String → ExceptT String IO thm
  new_type_abbrev : String → hol_type → IO Unit
  overload_interface : String → term → ExceptT String IO Unit
  extend_basic_congs : List thm → IO Unit
  -- conversions
  REAL_RAT_ADD_CONV : ioconv
  REAL_RAT_EQ_CONV : ioconv
  REAL_RAT_INV_CONV : ioconv
  REAL_RAT_MUL_CONV : ioconv
  NNF_CONV : ioconv
  NNFC_CONV : ioconv
  PRENEX_CONV : ioconv
  WEAK_CNF_CONV : ioconv
  CONJ_CANON_CONV : ioconv
  CONDS_CELIM_CONV : ioconv
  /-- calc_int.ml's syntax record, for `term_of_rat`. -/
  ratSyntax : HolMath.CalcInt.RatSyntax
  /-- normalizer.ml's `SEMIRING_NORMALIZERS_CONV sth rth (is_const,add,mul,pow)
      variable_order`, with the natural-number pieces supplied. -/
  SEMIRING_NORMALIZERS_CONV : thm → thm → (term → Bool) → ioconv → ioconv → ioconv →
    (term → term → Bool) → ExceptT String IO HolMath.Normalizer.PolynomialConvs
  /-- grobner.ml's `RING_AND_IDEAL_CONV`, with its globals supplied. -/
  RING_AND_IDEAL_CONV : HolMath.Grobner.RingParms →
    ExceptT String IO ((term → IO (Except String thm)) ×
                       (List term → term → IO (Except String (List term))))
  cpx : CpxThms

/- ------------------------------------------------------------------------- -/
/- The type "real^2" regarded as the complex numbers; real and imaginary   -/
/- parts; real injection and imaginary unit; complex multiplication; various -/
/- handy rewrites; pseudo-definitions of other general vector concepts over  -/
/- R^2; crude tactic to automate very simple algebraic equivalences.       -/
/- (complex_algebra.ml 12-141)                                             -/
/- ------------------------------------------------------------------------- -/

structure CXA where
  prioritize_complex : ExceptT String IO Unit
  RE_DEF : thm
  IM_DEF : thm
  complex : thm
  CX_DEF : thm
  ii : thm
  complex_mul : thm
  complex_inv : thm
  complex_div : thm
  complex_pow : thm
  RE : thm
  IM : thm
  COMPLEX_EQ : thm
  COMPLEX : thm
  COMPLEX_EQ_0 : thm
  FORALL_COMPLEX : thm
  EXISTS_COMPLEX : thm
  complex_neg : thm
  complex_add : thm
  complex_sub : thm
  complex_norm : thm
  COMPLEX_SQNORM : thm
  SIMPLE_COMPLEX_ARITH_TAC : tactic
  SIMPLE_COMPLEX_ARITH : term → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupCXA [HolBase] (D : ComplexAlgebraDeps) : ExceptT String IO CXA := do
  -- @@SCOPE BEGIN
  let { new_definition, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD,
        REAL_RAT_REDUCE_CONV, VECTOR_ARITH, .. } := D.cvx
  let { define, new_type_abbrev, overload_interface, .. } := D
  let { ARITH, CART_EQ, DIMINDEX_2, .. } := D.cvx.core1
  let { REAL_ENTIRE, .. } := D.cvx.core4
  let { REAL_POW_2, .. } := D.cvx.core5
  let { NORM_POW_2, .. } := D.cvx.vec3
  let { VECTOR_ADD_COMPONENT, VECTOR_NEG_COMPONENT, dot, .. } := D.cvx.vec4
  let { FORALL_2, REAL_LE_SQUARE, SUM_2, VECTOR_2, vector_norm, .. } := D.cpx
  -- @@SCOPE END

  new_type_abbrev "complex" (← qty "real^2")

  let prioritize_complex : ExceptT String IO Unit := do
    D.cvx.prioritize_real
    overload_interface "--" (← q r"vector_neg:complex->complex")
    overload_interface "+" (← q r"vector_add:complex->complex->complex")
    overload_interface "-" (← q r"vector_sub:complex->complex->complex")
    overload_interface "*" (← q r"complex_mul:complex->complex->complex")
    overload_interface "/" (← q r"complex_div:complex->complex->complex")
    overload_interface "pow" (← q r"complex_pow:complex->num->complex")
    overload_interface "inv" (← q r"complex_inv:complex->complex")

  prioritize_complex

  -- Real and imaginary parts of a number.

  let RE_DEF ← new_definition
   r"Re(z:complex) = z$1"

  let IM_DEF ← new_definition
   r"Im(z:complex) = z$2"

  -- Real injection and imaginary unit.

  let complex ← new_definition
   r"complex(x,y) = vector[x;y]:complex"

  let CX_DEF ← new_definition
   r"Cx(a) = complex(a,&0)"

  let ii ← new_definition
   r"ii = complex(&0,&1)"

  -- Complex multiplication.

  let complex_mul ← new_definition
   r"w * z = complex(Re(w) * Re(z) - Im(w) * Im(z),
                     Re(w) * Im(z) + Im(w) * Re(z))"

  let complex_inv ← new_definition
   r"inv(z) = complex(Re(z) / (Re(z) pow 2 + Im(z) pow 2),
                      --(Im(z)) / (Re(z) pow 2 + Im(z) pow 2))"

  let complex_div ← new_definition
   r"w / z = w * inv(z)"

  let complex_pow ← define
   r"(x pow 0 = Cx(&1)) /\
     (!n. x pow (SUC n) = x * x pow n)"

  -- Various handy rewrites.

  let RE ← prove
   r"(Re(complex(x,y)) = x)"
   (REWRITE_TAC [RE_DEF, complex, VECTOR_2])

  let IM ← prove
   r"Im(complex(x,y)) = y"
   (REWRITE_TAC [IM_DEF, complex, VECTOR_2])

  let COMPLEX_EQ ← prove
   r"!w z. (w = z) <=> (Re(w) = Re(z)) /\ (Im(w) = Im(z))"
   (SIMP_TAC [CART_EQ, FORALL_2, DIMINDEX_2, RE_DEF, IM_DEF])

  let COMPLEX ← prove
   r"!z. complex(Re(z),Im(z)) = z"
   (REWRITE_TAC [COMPLEX_EQ, RE, IM])

  let COMPLEX_EQ_0 ← prove
   r"z = Cx(&0) <=> Re(z) pow 2 + Im(z) pow 2 = &0"
   (REWRITE_TAC [COMPLEX_EQ, CX_DEF, RE, IM] THEN
    EQ_TAC THEN SIMP_TAC [] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN (MP_TAC o MATCH_MP (← REAL_ARITH
     (← q r"!x y:real. x + y = &0 ==> &0 <= x /\ &0 <= y ==> x = &0 /\ y = &0"))) THEN
    REWRITE_TAC [REAL_POW_2, REAL_LE_SQUARE, REAL_ENTIRE])

  let FORALL_COMPLEX ← prove
   r"(!z. P z) <=> (!x y. P(complex(x,y)))"
   (MESON_TAC [COMPLEX])

  let EXISTS_COMPLEX ← prove
   r"(?z. P z) <=> (?x y. P(complex(x,y)))"
   (MESON_TAC [COMPLEX])

  -- Pseudo-definitions of other general vector concepts over R^2.

  let complex_neg ← prove
   r"--z = complex(--(Re(z)),--(Im(z)))"
   (REWRITE_TAC [COMPLEX_EQ, RE, IM] THEN REWRITE_TAC [RE_DEF, IM_DEF] THEN
    SIMP_TAC [VECTOR_NEG_COMPONENT, DIMINDEX_2, ARITH])

  let complex_add ← prove
   r"w + z = complex(Re(w) + Re(z),Im(w) + Im(z))"
   (REWRITE_TAC [COMPLEX_EQ, RE, IM] THEN REWRITE_TAC [RE_DEF, IM_DEF] THEN
    SIMP_TAC [VECTOR_ADD_COMPONENT, DIMINDEX_2, ARITH])

  let complex_sub ← VECTOR_ARITH (← q r"(w:complex) - z = w + --z")

  let complex_norm ← prove
   r"norm(z) = sqrt(Re(z) pow 2 + Im(z) pow 2)"
   (REWRITE_TAC [vector_norm, dot, RE_DEF, IM_DEF, SUM_2, DIMINDEX_2] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC)

  let COMPLEX_SQNORM ← prove
   r"norm(z) pow 2 = Re(z) pow 2 + Im(z) pow 2"
   (REWRITE_TAC [NORM_POW_2, dot, RE_DEF, IM_DEF, SUM_2, DIMINDEX_2] THEN
    REAL_ARITH_TAC)

  -- Crude tactic to automate very simple algebraic equivalences.

  let SIMPLE_COMPLEX_ARITH_TAC : tactic :=
    REWRITE_TAC [COMPLEX_EQ, RE, IM, CX_DEF,
                 complex_add, complex_neg, complex_sub, complex_mul,
                 complex_inv, complex_div] THEN
    CONV_TAC (fun t => REAL_FIELD t)

  let SIMPLE_COMPLEX_ARITH (tm : term) : ExceptT String IO thm :=
    ExceptT.mk (HolCore.Tactics.prove HolBase.B tm SIMPLE_COMPLEX_ARITH_TAC)

  return { prioritize_complex, RE_DEF, IM_DEF, complex, CX_DEF, ii, complex_mul, complex_inv,
           complex_div, complex_pow, RE, IM, COMPLEX_EQ, COMPLEX, COMPLEX_EQ_0,
           FORALL_COMPLEX, EXISTS_COMPLEX, complex_neg, complex_add, complex_sub,
           complex_norm, COMPLEX_SQNORM, SIMPLE_COMPLEX_ARITH_TAC, SIMPLE_COMPLEX_ARITH }

/- ------------------------------------------------------------------------- -/
/- Basic algebraic properties that can be proved automatically by this.    -/
/- (complex_algebra.ml 143-369)                                            -/
/- ------------------------------------------------------------------------- -/

structure CXB where
  COMPLEX_ADD_SYM : thm
  COMPLEX_ADD_ASSOC : thm
  COMPLEX_ADD_LID : thm
  COMPLEX_ADD_LINV : thm
  COMPLEX_MUL_SYM : thm
  COMPLEX_MUL_ASSOC : thm
  COMPLEX_MUL_LID : thm
  COMPLEX_ADD_LDISTRIB : thm
  COMPLEX_ADD_AC : thm
  COMPLEX_MUL_AC : thm
  COMPLEX_ADD_RID : thm
  COMPLEX_MUL_RID : thm
  COMPLEX_ADD_RINV : thm
  COMPLEX_ADD_RDISTRIB : thm
  COMPLEX_EQ_ADD_LCANCEL : thm
  COMPLEX_EQ_ADD_RCANCEL : thm
  COMPLEX_MUL_RZERO : thm
  COMPLEX_MUL_LZERO : thm
  COMPLEX_NEG_NEG : thm
  COMPLEX_MUL_RNEG : thm
  COMPLEX_MUL_LNEG : thm
  COMPLEX_NEG_ADD : thm
  COMPLEX_NEG_0 : thm
  COMPLEX_EQ_ADD_LCANCEL_0 : thm
  COMPLEX_EQ_ADD_RCANCEL_0 : thm
  COMPLEX_LNEG_UNIQ : thm
  COMPLEX_RNEG_UNIQ : thm
  COMPLEX_NEG_LMUL : thm
  COMPLEX_NEG_RMUL : thm
  COMPLEX_NEG_MUL2 : thm
  COMPLEX_SUB_ADD : thm
  COMPLEX_SUB_ADD2 : thm
  COMPLEX_SUB_REFL : thm
  COMPLEX_SUB_0 : thm
  COMPLEX_NEG_EQ_0 : thm
  COMPLEX_NEG_SUB : thm
  COMPLEX_ADD_SUB : thm
  COMPLEX_NEG_EQ : thm
  COMPLEX_NEG_MINUS1 : thm
  COMPLEX_SUB_SUB : thm
  COMPLEX_ADD2_SUB2 : thm
  COMPLEX_SUB_LZERO : thm
  COMPLEX_SUB_RZERO : thm
  COMPLEX_SUB_LNEG : thm
  COMPLEX_SUB_RNEG : thm
  COMPLEX_SUB_NEG2 : thm
  COMPLEX_SUB_TRIANGLE : thm
  COMPLEX_EQ_SUB_LADD : thm
  COMPLEX_EQ_SUB_RADD : thm
  COMPLEX_SUB_SUB2 : thm
  COMPLEX_ADD_SUB2 : thm
  COMPLEX_DIFFSQ : thm
  COMPLEX_EQ_NEG2 : thm
  COMPLEX_SUB_LDISTRIB : thm
  COMPLEX_SUB_RDISTRIB : thm
  COMPLEX_MUL_2 : thm
  deriving Inhabited

@[nospecialize]
def setupCXB [HolBase] (BCXA : CXA) : ExceptT String IO CXB := do
  -- @@SCOPE BEGIN
  let { SIMPLE_COMPLEX_ARITH_TAC, .. } := BCXA
  -- @@SCOPE END

  let COMPLEX_ADD_SYM ← prove
   r"!x y. x + y = y + x"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_ADD_ASSOC ← prove
   r"!x y z. x + y + z = (x + y) + z"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_ADD_LID ← prove
   r"!x. Cx(&0) + x = x"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_ADD_LINV ← prove
   r"!x. --x + x = Cx(&0)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_MUL_SYM ← prove
   r"!x y. x * y = y * x"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_MUL_ASSOC ← prove
   r"!x y z. x * y * z = (x * y) * z"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_MUL_LID ← prove
   r"!x. Cx(&1) * x = x"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_ADD_LDISTRIB ← prove
   r"!x y z. x * (y + z) = x * y + x * z"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_ADD_AC ← prove
   r"(m + n = n + m) /\ ((m + n) + p = m + n + p) /\ (m + n + p = n + m + p)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_MUL_AC ← prove
   r"(m * n = n * m) /\ ((m * n) * p = m * n * p) /\ (m * n * p = n * m * p)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_ADD_RID ← prove
   r"!x. x + Cx(&0) = x"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_MUL_RID ← prove
   r"!x. x * Cx(&1) = x"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_ADD_RINV ← prove
   r"!x. x + --x = Cx(&0)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_ADD_RDISTRIB ← prove
   r"!x y z. (x + y) * z = x * z + y * z"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_EQ_ADD_LCANCEL ← prove
   r"!x y z. (x + y = x + z) <=> (y = z)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_EQ_ADD_RCANCEL ← prove
   r"!x y z. (x + z = y + z) <=> (x = y)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_MUL_RZERO ← prove
   r"!x. x * Cx(&0) = Cx(&0)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_MUL_LZERO ← prove
   r"!x. Cx(&0) * x = Cx(&0)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_NEG_NEG ← prove
   r"!x. --(--x) = x"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_MUL_RNEG ← prove
   r"!x y. x * --y = --(x * y)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_MUL_LNEG ← prove
   r"!x y. --x * y = --(x * y)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_NEG_ADD ← prove
   r"!x y. --(x + y) = --x + --y"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_NEG_0 ← prove
   r"--Cx(&0) = Cx(&0)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_EQ_ADD_LCANCEL_0 ← prove
   r"!x y. (x + y = x) <=> (y = Cx(&0))"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_EQ_ADD_RCANCEL_0 ← prove
   r"!x y. (x + y = y) <=> (x = Cx(&0))"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_LNEG_UNIQ ← prove
   r"!x y. (x + y = Cx(&0)) <=> (x = --y)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_RNEG_UNIQ ← prove
   r"!x y. (x + y = Cx(&0)) <=> (y = --x)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_NEG_LMUL ← prove
   r"!x y. --(x * y) = --x * y"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_NEG_RMUL ← prove
   r"!x y. --(x * y) = x * --y"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_NEG_MUL2 ← prove
   r"!x y. --x * --y = x * y"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_SUB_ADD ← prove
   r"!x y. x - y + y = x"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_SUB_ADD2 ← prove
   r"!x y. y + x - y = x"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_SUB_REFL ← prove
   r"!x. x - x = Cx(&0)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_SUB_0 ← prove
   r"!x y. (x - y = Cx(&0)) <=> (x = y)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_NEG_EQ_0 ← prove
   r"!x. (--x = Cx(&0)) <=> (x = Cx(&0))"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_NEG_SUB ← prove
   r"!x y. --(x - y) = y - x"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_ADD_SUB ← prove
   r"!x y. (x + y) - x = y"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_NEG_EQ ← prove
   r"!x y. (--x = y) <=> (x = --y)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_NEG_MINUS1 ← prove
   r"!x. --x = --Cx(&1) * x"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_SUB_SUB ← prove
   r"!x y. x - y - x = --y"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_ADD2_SUB2 ← prove
   r"!a b c d. (a + b) - (c + d) = a - c + b - d"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_SUB_LZERO ← prove
   r"!x. Cx(&0) - x = --x"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_SUB_RZERO ← prove
   r"!x. x - Cx(&0) = x"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_SUB_LNEG ← prove
   r"!x y. --x - y = --(x + y)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_SUB_RNEG ← prove
   r"!x y. x - --y = x + y"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_SUB_NEG2 ← prove
   r"!x y. --x - --y = y - x"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_SUB_TRIANGLE ← prove
   r"!a b c. a - b + b - c = a - c"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_EQ_SUB_LADD ← prove
   r"!x y z. (x = y - z) <=> (x + z = y)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_EQ_SUB_RADD ← prove
   r"!x y z. (x - y = z) <=> (x = z + y)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_SUB_SUB2 ← prove
   r"!x y. x - (x - y) = y"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_ADD_SUB2 ← prove
   r"!x y. x - (x + y) = --y"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_DIFFSQ ← prove
   r"!x y. (x + y) * (x - y) = x * x - y * y"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_EQ_NEG2 ← prove
   r"!x y. (--x = --y) <=> (x = y)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_SUB_LDISTRIB ← prove
   r"!x y z. x * (y - z) = x * y - x * z"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_SUB_RDISTRIB ← prove
   r"!x y z. (x - y) * z = x * z - y * z"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_MUL_2 ← prove
   r"!x. Cx(&2) * x = x + x"
   SIMPLE_COMPLEX_ARITH_TAC

  return { COMPLEX_ADD_SYM, COMPLEX_ADD_ASSOC, COMPLEX_ADD_LID, COMPLEX_ADD_LINV,
           COMPLEX_MUL_SYM, COMPLEX_MUL_ASSOC, COMPLEX_MUL_LID, COMPLEX_ADD_LDISTRIB,
           COMPLEX_ADD_AC, COMPLEX_MUL_AC, COMPLEX_ADD_RID, COMPLEX_MUL_RID, COMPLEX_ADD_RINV,
           COMPLEX_ADD_RDISTRIB, COMPLEX_EQ_ADD_LCANCEL, COMPLEX_EQ_ADD_RCANCEL,
           COMPLEX_MUL_RZERO, COMPLEX_MUL_LZERO, COMPLEX_NEG_NEG, COMPLEX_MUL_RNEG,
           COMPLEX_MUL_LNEG, COMPLEX_NEG_ADD, COMPLEX_NEG_0, COMPLEX_EQ_ADD_LCANCEL_0,
           COMPLEX_EQ_ADD_RCANCEL_0, COMPLEX_LNEG_UNIQ, COMPLEX_RNEG_UNIQ, COMPLEX_NEG_LMUL,
           COMPLEX_NEG_RMUL, COMPLEX_NEG_MUL2, COMPLEX_SUB_ADD, COMPLEX_SUB_ADD2,
           COMPLEX_SUB_REFL, COMPLEX_SUB_0, COMPLEX_NEG_EQ_0, COMPLEX_NEG_SUB, COMPLEX_ADD_SUB,
           COMPLEX_NEG_EQ, COMPLEX_NEG_MINUS1, COMPLEX_SUB_SUB, COMPLEX_ADD2_SUB2,
           COMPLEX_SUB_LZERO, COMPLEX_SUB_RZERO, COMPLEX_SUB_LNEG, COMPLEX_SUB_RNEG,
           COMPLEX_SUB_NEG2, COMPLEX_SUB_TRIANGLE, COMPLEX_EQ_SUB_LADD, COMPLEX_EQ_SUB_RADD,
           COMPLEX_SUB_SUB2, COMPLEX_ADD_SUB2, COMPLEX_DIFFSQ, COMPLEX_EQ_NEG2,
           COMPLEX_SUB_LDISTRIB, COMPLEX_SUB_RDISTRIB, COMPLEX_MUL_2 }

/- ------------------------------------------------------------------------- -/
/- Sometimes here we need to tweak non-zeroness assertions; more about     -/
/- powers; homomorphic embedding properties for Cx mapping; some "linear"  -/
/- things hold for Re and Im too; an "expansion" theorem into the          -/
/- traditional notation; real and complex parts of ii and multiples; limited -/
/- "multiplicative" theorems for Re and Im.  (complex_algebra.ml 371-615)  -/
/- ------------------------------------------------------------------------- -/

structure CXC where
  II_NZ : thm
  COMPLEX_MUL_LINV : thm
  COMPLEX_ENTIRE : thm
  COMPLEX_MUL_RINV : thm
  COMPLEX_DIV_REFL : thm
  COMPLEX_VEC_0 : thm
  COMPLEX_CMUL : thm
  COMPLEX_POW_ADD : thm
  COMPLEX_POW_POW : thm
  COMPLEX_POW_1 : thm
  COMPLEX_POW_2 : thm
  COMPLEX_POW_NEG : thm
  COMPLEX_POW_ONE : thm
  COMPLEX_POW_MUL : thm
  COMPLEX_POW_II_2 : thm
  COMPLEX_POW_EQ_0 : thm
  COMPLEX_POW_ZERO : thm
  CX_INJ : thm
  CX_NEG : thm
  CX_ADD : thm
  CX_SUB : thm
  CX_INV : thm
  CX_MUL : thm
  CX_POW : thm
  CX_DIV : thm
  CX_ABS : thm
  COMPLEX_NORM_CX : thm
  DIST_CX : thm
  RE_CX : thm
  RE_NEG : thm
  RE_ADD : thm
  RE_SUB : thm
  IM_CX : thm
  IM_NEG : thm
  IM_ADD : thm
  IM_SUB : thm
  COMPLEX_EXPAND : thm
  COMPLEX_TRAD : thm
  RE_II : thm
  IM_II : thm
  RE_MUL_II : thm
  IM_MUL_II : thm
  COMPLEX_NORM_II : thm
  RE_CMUL : thm
  IM_CMUL : thm
  RE_MUL_CX : thm
  IM_MUL_CX : thm
  RE_DIV_CX : thm
  IM_DIV_CX : thm
  deriving Inhabited

@[nospecialize]
def setupCXC [HolBase] (D : ComplexAlgebraDeps) (BCXA : CXA) (BCXB : CXB) :
    ExceptT String IO CXC := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, REAL_ARITH_TAC, REAL_FIELD, REAL_RAT_REDUCE_CONV, num_CONV,
        .. } := D.cvx
  let { ARITH, CART_EQ, DIMINDEX_2, .. } := D.cvx.core1
  let { MULT_CLAUSES, REAL_ADD_LID, REAL_ADD_RID, .. } := D.cvx.core3
  let { REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_NEG_0, REAL_POW_2, REAL_SUB_RZERO, SQRT_1,
        .. } := D.cvx.core5
  let { real_div, real_pow, .. } := D.cvx.core6
  let { VECTOR_MUL_COMPONENT, VEC_COMPONENT, dist, .. } := D.cvx.vec4
  let { ADD_CLAUSES, EVEN, NOT_SUC, POW_2_SQRT_ABS, real_sub, FORALL_2, VECTOR_2,
        .. } := D.cpx
  let { RE_DEF, IM_DEF, complex, CX_DEF, ii, complex_mul, complex_inv, complex_div,
        complex_pow, RE, IM, COMPLEX_EQ, COMPLEX_EQ_0, complex_neg, complex_add,
        complex_sub, complex_norm, SIMPLE_COMPLEX_ARITH_TAC, .. } := BCXA
  let { COMPLEX_MUL_ASSOC, COMPLEX_MUL_LID, COMPLEX_MUL_AC, COMPLEX_MUL_RID,
        COMPLEX_MUL_LZERO, COMPLEX_NEG_NEG, COMPLEX_MUL_RNEG, COMPLEX_MUL_LNEG, .. } := BCXB
  -- @@SCOPE END

  -- Sometimes here we need to tweak non-zeroness assertions.

  let II_NZ ← prove
   r"~(ii = Cx(&0))"
   (REWRITE_TAC [ii] THEN SIMPLE_COMPLEX_ARITH_TAC)

  let COMPLEX_MUL_LINV ← prove
   r"!z. ~(z = Cx(&0)) ==> (inv(z) * z = Cx(&1))"
   (REWRITE_TAC [COMPLEX_EQ_0] THEN SIMPLE_COMPLEX_ARITH_TAC)

  let COMPLEX_ENTIRE ← prove
   r"!x y. (x * y = Cx(&0)) <=> (x = Cx(&0)) \/ (y = Cx(&0))"
   (REWRITE_TAC [COMPLEX_EQ_0] THEN SIMPLE_COMPLEX_ARITH_TAC)

  let COMPLEX_MUL_RINV ← prove
   r"!z. ~(z = Cx(&0)) ==> (z * inv(z) = Cx(&1))"
   (REWRITE_TAC [COMPLEX_EQ_0] THEN SIMPLE_COMPLEX_ARITH_TAC)

  let COMPLEX_DIV_REFL ← prove
   r"!x. ~(x = Cx(&0)) ==> (x / x = Cx(&1))"
   (REWRITE_TAC [COMPLEX_EQ_0] THEN SIMPLE_COMPLEX_ARITH_TAC)

  let COMPLEX_VEC_0 ← prove
   r"vec 0 = Cx(&0)"
   (SIMP_TAC [CART_EQ, VEC_COMPONENT, CX_DEF, complex,
              DIMINDEX_2, FORALL_2, VECTOR_2])

  let COMPLEX_CMUL ← prove
   r"!c x. c % x = Cx(c) * x"
   (SIMP_TAC [CART_EQ, VECTOR_MUL_COMPONENT, CX_DEF, complex,
              complex_mul, DIMINDEX_2, FORALL_2, IM_DEF, RE_DEF, VECTOR_2] THEN
    REAL_ARITH_TAC)

  -- More about powers.

  let COMPLEX_POW_ADD ← prove
   r"!x m n. x pow (m + n) = x pow m * x pow n"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [ADD_CLAUSES, complex_pow,
                     COMPLEX_MUL_LID, COMPLEX_MUL_ASSOC])

  let COMPLEX_POW_POW ← prove
   r"!x m n. (x pow m) pow n = x pow (m * n)"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [complex_pow, MULT_CLAUSES, COMPLEX_POW_ADD])

  let COMPLEX_POW_1 ← prove
   r"!x. x pow 1 = x"
   (REWRITE_TAC [← ExceptT.mk (num_CONV (← q r"1"))] THEN
    REWRITE_TAC [complex_pow, COMPLEX_MUL_RID])

  let COMPLEX_POW_2 ← prove
   r"!x. x pow 2 = x * x"
   (REWRITE_TAC [← ExceptT.mk (num_CONV (← q r"2"))] THEN
    REWRITE_TAC [complex_pow, COMPLEX_POW_1])

  let COMPLEX_POW_NEG ← prove
   r"!x n. (--x) pow n = if EVEN n then x pow n else --(x pow n)"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [complex_pow, EVEN] THEN
    ASM_CASES_TAC (← q r"EVEN n") THEN
    ASM_REWRITE_TAC [COMPLEX_MUL_RNEG, COMPLEX_MUL_LNEG, COMPLEX_NEG_NEG])

  let COMPLEX_POW_ONE ← prove
   r"!n. Cx(&1) pow n = Cx(&1)"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [complex_pow, COMPLEX_MUL_LID])

  let COMPLEX_POW_MUL ← prove
   r"!x y n. (x * y) pow n = (x pow n) * (y pow n)"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [complex_pow, COMPLEX_MUL_LID, COMPLEX_MUL_AC])

  let COMPLEX_POW_II_2 ← prove
   r"ii pow 2 = --Cx(&1)"
   (REWRITE_TAC [ii, COMPLEX_POW_2, complex_mul, CX_DEF, RE, IM, complex_neg] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV)

  let COMPLEX_POW_EQ_0 ← prove
   r"!x n. (x pow n = Cx(&0)) <=> (x = Cx(&0)) /\ ~(n = 0)"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [NOT_SUC, complex_pow, COMPLEX_ENTIRE] THENL
     [SIMPLE_COMPLEX_ARITH_TAC, CONV_TAC (fun t => TAUT t)])

  let COMPLEX_POW_ZERO ← prove
   r"!n. Cx(&0) pow n = if n = 0 then Cx(&1) else Cx(&0)"
   (INDUCT_TAC THEN REWRITE_TAC [complex_pow, COMPLEX_MUL_LZERO, NOT_SUC])

  -- Homomorphic embedding properties for Cx mapping.

  let CX_INJ ← prove
   r"!x y. (Cx(x) = Cx(y)) <=> (x = y)"
   (REWRITE_TAC [CX_DEF, COMPLEX_EQ, RE, IM])

  let CX_NEG ← prove
   r"!x. Cx(--x) = --(Cx(x))"
   (REWRITE_TAC [CX_DEF, complex_neg, RE, IM, REAL_NEG_0])

  let CX_ADD ← prove
   r"!x y. Cx(x + y) = Cx(x) + Cx(y)"
   (REWRITE_TAC [CX_DEF, complex_add, RE, IM, REAL_ADD_LID])

  let CX_SUB ← prove
   r"!x y. Cx(x - y) = Cx(x) - Cx(y)"
   (REWRITE_TAC [complex_sub, real_sub, CX_ADD, CX_NEG])

  let CX_INV ← prove
   r"!x. Cx(inv x) = inv(Cx x)"
   (GEN_TAC THEN REWRITE_TAC [CX_DEF, complex_inv, RE, IM, COMPLEX_EQ] THEN
    ASM_CASES_TAC (← q r"x = &0") THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    POP_ASSUM MP_TAC THEN CONV_TAC (fun t => REAL_FIELD t))

  let CX_MUL ← prove
   r"!x y. Cx(x * y) = Cx(x) * Cx(y)"
   (REWRITE_TAC [CX_DEF, complex_mul, RE, IM, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
    REWRITE_TAC [REAL_SUB_RZERO, REAL_ADD_RID])

  let CX_POW ← prove
   r"!x n. Cx(x pow n) = Cx(x) pow n"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [complex_pow, real_pow, CX_MUL])

  let CX_DIV ← prove
   r"!x y. Cx(x / y) = Cx(x) / Cx(y)"
   (REWRITE_TAC [complex_div, real_div, CX_MUL, CX_INV])

  let CX_ABS ← prove
   r"!x. Cx(abs x) = Cx(norm(Cx(x)))"
   (REWRITE_TAC [CX_DEF, complex_norm, COMPLEX_EQ, RE, IM] THEN
    REWRITE_TAC [REAL_POW_2, REAL_MUL_LZERO, REAL_ADD_RID] THEN
    REWRITE_TAC [← GSYM REAL_POW_2, POW_2_SQRT_ABS])

  let COMPLEX_NORM_CX ← prove
   r"!x. norm(Cx(x)) = abs(x)"
   (REWRITE_TAC [← GSYM CX_INJ, CX_ABS])

  let DIST_CX ← prove
   r"!x y. dist(Cx x,Cx y) = abs(x - y)"
   (REWRITE_TAC [dist, ← GSYM CX_SUB, COMPLEX_NORM_CX])

  -- Some "linear" things hold for Re and Im too.

  let RE_CX ← prove
   r"!x. Re(Cx x) = x"
   (REWRITE_TAC [RE, CX_DEF])

  let RE_NEG ← prove
   r"!x. Re(--x) = --Re(x)"
   (REWRITE_TAC [complex_neg, RE])

  let RE_ADD ← prove
   r"!x y. Re(x + y) = Re(x) + Re(y)"
   (REWRITE_TAC [complex_add, RE])

  let RE_SUB ← prove
   r"!x y. Re(x - y) = Re(x) - Re(y)"
   (REWRITE_TAC [complex_sub, real_sub, RE_ADD, RE_NEG])

  let IM_CX ← prove
   r"!x. Im(Cx x) = &0"
   (REWRITE_TAC [IM, CX_DEF])

  let IM_NEG ← prove
   r"!x. Im(--x) = --Im(x)"
   (REWRITE_TAC [complex_neg, IM])

  let IM_ADD ← prove
   r"!x y. Im(x + y) = Im(x) + Im(y)"
   (REWRITE_TAC [complex_add, IM])

  let IM_SUB ← prove
   r"!x y. Im(x - y) = Im(x) - Im(y)"
   (REWRITE_TAC [complex_sub, real_sub, IM_ADD, IM_NEG])

  -- An "expansion" theorem into the traditional notation.

  let COMPLEX_EXPAND ← prove
   r"!z. z = Cx(Re z) + ii * Cx(Im z)"
   (REWRITE_TAC [ii] THEN SIMPLE_COMPLEX_ARITH_TAC)

  let COMPLEX_TRAD ← prove
   r"!x y. complex(x,y) = Cx(x) + ii * Cx(y)"
   (REWRITE_TAC [ii] THEN SIMPLE_COMPLEX_ARITH_TAC)

  -- Real and complex parts of ii and multiples.

  let RE_II ← prove
   r"Re ii = &0"
   (REWRITE_TAC [ii] THEN SIMPLE_COMPLEX_ARITH_TAC)

  let IM_II ← prove
   r"Im ii = &1"
   (REWRITE_TAC [ii] THEN SIMPLE_COMPLEX_ARITH_TAC)

  let RE_MUL_II ← prove
   r"!z. Re(z * ii) = --(Im z) /\ Re(ii * z) = --(Im z)"
   (REWRITE_TAC [ii] THEN SIMPLE_COMPLEX_ARITH_TAC)

  let IM_MUL_II ← prove
   r"!z. Im(z * ii) = Re z /\ Im(ii * z) = Re z"
   (REWRITE_TAC [ii] THEN SIMPLE_COMPLEX_ARITH_TAC)

  let COMPLEX_NORM_II ← prove
   r"norm ii = &1"
   (REWRITE_TAC [complex_norm, RE_II, IM_II] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [SQRT_1])

  -- Limited "multiplicative" theorems for Re and Im.

  let RE_CMUL ← prove
   r"!a z. Re(a % z) = a * Re z"
   (SIMP_TAC [RE_DEF, VECTOR_MUL_COMPONENT, DIMINDEX_2, ARITH])

  let IM_CMUL ← prove
   r"!a z. Im(a % z) = a * Im z"
   (SIMP_TAC [IM_DEF, VECTOR_MUL_COMPONENT, DIMINDEX_2, ARITH])

  let RE_MUL_CX ← prove
   r"!x z. Re(Cx(x) * z) = x * Re z /\
           Re(z * Cx(x)) = Re z * x"
   SIMPLE_COMPLEX_ARITH_TAC

  let IM_MUL_CX ← prove
   r"!x z. Im(Cx(x) * z) = x * Im z /\
           Im(z * Cx(x)) = Im z * x"
   SIMPLE_COMPLEX_ARITH_TAC

  let RE_DIV_CX ← prove
   r"!z x. Re(z / Cx(x)) = Re(z) / x"
   (REWRITE_TAC [complex_div, real_div, ← GSYM CX_INV, RE_MUL_CX])

  let IM_DIV_CX ← prove
   r"!z x. Im(z / Cx(x)) = Im(z) / x"
   (REWRITE_TAC [complex_div, real_div, ← GSYM CX_INV, IM_MUL_CX])

  return { II_NZ, COMPLEX_MUL_LINV, COMPLEX_ENTIRE, COMPLEX_MUL_RINV, COMPLEX_DIV_REFL,
           COMPLEX_VEC_0, COMPLEX_CMUL, COMPLEX_POW_ADD, COMPLEX_POW_POW, COMPLEX_POW_1,
           COMPLEX_POW_2, COMPLEX_POW_NEG, COMPLEX_POW_ONE, COMPLEX_POW_MUL, COMPLEX_POW_II_2,
           COMPLEX_POW_EQ_0, COMPLEX_POW_ZERO, CX_INJ, CX_NEG, CX_ADD, CX_SUB, CX_INV, CX_MUL,
           CX_POW, CX_DIV, CX_ABS, COMPLEX_NORM_CX, DIST_CX, RE_CX, RE_NEG, RE_ADD, RE_SUB,
           IM_CX, IM_NEG, IM_ADD, IM_SUB, COMPLEX_EXPAND, COMPLEX_TRAD, RE_II, IM_II,
           RE_MUL_II, IM_MUL_II, COMPLEX_NORM_II, RE_CMUL, IM_CMUL, RE_MUL_CX, IM_MUL_CX,
           RE_DIV_CX, IM_DIV_CX }

/- ------------------------------------------------------------------------- -/
/- Syntax constructors etc. for complex constants; conversions for         -/
/- arithmetic on complex constants; complex polynomial normalizer, extended  -/
/- to handle "inv" and division by constants; complex number version of the  -/
/- usual ring procedure.  (complex_algebra.ml 618-771)                     -/
/- ------------------------------------------------------------------------- -/

/-- What the redefined `COMPLEX_POLY_CONV` binds before its `let rec`
    (complex_algebra.ml 701-708), with the conversions it calls. -/
structure ComplexPolyConvEnv where
  neg_tm : term
  inv_tm : term
  add_tm : term
  sub_tm : term
  mul_tm : term
  div_tm : term
  pow_tm : term
  div_conv : ioconv
  P : HolMath.Normalizer.PolynomialConvs
  COMPLEX_RAT_INV_CONV : ioconv

/-- The `let rec COMPLEX_POLY_CONV tm` of complex_algebra.ml 709-734. -/
partial def COMPLEX_POLY_CONV_rec [HolBase] (E : ComplexPolyConvEnv) : ioconv :=
  fun tm => ExceptT.run do
  let COMPLEX_POLY_CONV := COMPLEX_POLY_CONV_rec E
  let P := E.P
  if !(is_comb tm) || HolMath.CalcInt.is_ratconst tm then return REFL tm
  let (lop, r) ← liftExcept (dest_comb tm)
  if lop == E.neg_tm then
    let th1 ← AP_TERM lop (← ExceptT.mk (COMPLEX_POLY_CONV r))
    HolLight.TRANS th1 (← ExceptT.mk (P.POLYNOMIAL_NEG_CONV (← liftExcept (rand (concl th1)))))
  else if lop == E.inv_tm then
    let th1 ← AP_TERM lop (← ExceptT.mk (COMPLEX_POLY_CONV r))
    HolLight.TRANS th1 (← ExceptT.mk (TRY_CONV E.COMPLEX_RAT_INV_CONV (← liftExcept (rand (concl th1)))))
  else if !(is_comb lop) then return REFL tm
  else
  let (op, l) ← liftExcept (dest_comb lop)
  if op == E.pow_tm then
    let th1 ← AP_THM (← AP_TERM op (← ExceptT.mk (COMPLEX_POLY_CONV l))) r
    HolLight.TRANS th1 (← ExceptT.mk (TRY_CONV P.POLYNOMIAL_POW_CONV (← liftExcept (rand (concl th1)))))
  else if op == E.add_tm || op == E.mul_tm || op == E.sub_tm then
    let thr ← ExceptT.mk (COMPLEX_POLY_CONV r)
    let th1 ← MK_COMB (← AP_TERM op (← ExceptT.mk (COMPLEX_POLY_CONV l)), thr)
    let fn := if op == E.add_tm then P.POLYNOMIAL_ADD_CONV
              else if op == E.mul_tm then P.POLYNOMIAL_MUL_CONV
              else P.POLYNOMIAL_SUB_CONV
    HolLight.TRANS th1 (← ExceptT.mk (fn (← liftExcept (rand (concl th1)))))
  else if op == E.div_tm then
    let th1 ← ExceptT.mk (E.div_conv tm)
    HolLight.TRANS th1 (← ExceptT.mk (COMPLEX_POLY_CONV (← liftExcept (rand (concl th1)))))
  else return REFL tm

structure CXD where
  is_complex_const : term → Bool
  dest_complex_const : term → Except String Rat
  mk_complex_const : Rat → Except String term
  COMPLEX_RAT_EQ_CONV : ioconv
  COMPLEX_RAT_MUL_CONV : ioconv
  COMPLEX_RAT_ADD_CONV : ioconv
  COMPLEX_RAT_POW_CONV : ioconv
  COMPLEX_POLY_CLAUSES : thm
  COMPLEX_POLY_NEG_CLAUSES : thm
  COMPLEX_POLY_NEG_CONV : ioconv
  COMPLEX_POLY_ADD_CONV : ioconv
  COMPLEX_POLY_SUB_CONV : ioconv
  COMPLEX_POLY_MUL_CONV : ioconv
  COMPLEX_POLY_POW_CONV : ioconv
  COMPLEX_RAT_INV_CONV : ioconv
  /-- The redefined `COMPLEX_POLY_CONV` (complex_algebra.ml 700). -/
  COMPLEX_POLY_CONV : ioconv
  COMPLEX_RING : term → IO (Except String thm)
  complex_ideal_cofactors : List term → term → IO (Except String (List term))
  deriving Inhabited

@[nospecialize]
def setupCXD [HolBase] (D : ComplexAlgebraDeps) (BCXA : CXA) (BCXB : CXB) (BCXC : CXC) :
    ExceptT String IO CXD := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV, .. } := D.cvx
  let { REAL_RAT_ADD_CONV, REAL_RAT_EQ_CONV, REAL_RAT_INV_CONV, REAL_RAT_MUL_CONV,
        SEMIRING_NORMALIZERS_CONV, RING_AND_IDEAL_CONV, .. } := D
  let { CX_DEF, ii, complex_mul, complex_div, complex_pow, RE, IM, complex_add,
        SIMPLE_COMPLEX_ARITH_TAC, SIMPLE_COMPLEX_ARITH, .. } := BCXA
  let { COMPLEX_MUL_LZERO, COMPLEX_SUB_0, .. } := BCXB
  let { COMPLEX_ENTIRE, COMPLEX_MUL_RINV, CX_INJ, CX_ADD, CX_INV, CX_MUL, CX_POW,
        .. } := BCXC
  -- @@SCOPE END

  -- Syntax constructors etc. for complex constants.

  let is_complex_const ← do
    let cx_tm ← q r"Cx"
    pure (fun (tm : term) =>
      is_comb tm &&
      match dest_comb tm with
      | .ok (l, r) => l == cx_tm && HolMath.CalcInt.is_ratconst r
      | .error _ => false)

  let dest_complex_const ← do
    let cx_tm ← q r"Cx"
    pure (fun (tm : term) => do
      let (l, r) ← dest_comb tm
      if l == cx_tm then HolMath.CalcInt.rat_of_term r
      else throw "dest_complex_const")

  let mk_complex_const ← do
    let cx_tm ← q r"Cx"
    pure (fun (r : Rat) => do
      mk_comb cx_tm (← HolMath.CalcInt.term_of_rat D.ratSyntax r))

  -- Conversions for arithmetic on complex constants.

  let COMPLEX_RAT_EQ_CONV : ioconv :=
    (← GEN_REWRITE_CONV_NET id [CX_INJ]) THENC REAL_RAT_EQ_CONV

  let COMPLEX_RAT_MUL_CONV : ioconv :=
    (← GEN_REWRITE_CONV_NET id [← GSYM CX_MUL]) THENC RAND_CONV REAL_RAT_MUL_CONV

  let COMPLEX_RAT_ADD_CONV : ioconv :=
    (← GEN_REWRITE_CONV_NET id [← GSYM CX_ADD]) THENC RAND_CONV REAL_RAT_ADD_CONV

  let COMPLEX_RAT_POW_CONV : ioconv ← do
    let x_tm ← q r"x:real"
    let n_tm ← q r"n:num"
    let pth ← SYM (← SPECL [x_tm, n_tm] CX_POW)
    pure (fun tm => ExceptT.run do
      let (lop, r) ← liftExcept (dest_comb tm)
      let (_op, bod) ← liftExcept (dest_comb lop)
      let th1 ← INST [(← liftExcept (rand bod), x_tm), (r, n_tm)] pth
      let (tm1, tm2) ← liftExcept (dest_comb (concl th1))
      if (← liftExcept (rand tm1)) != tm then throw "COMPLEX_RAT_POW_CONV" else
      let (tm3, tm4) ← liftExcept (dest_comb tm2)
      HolLight.TRANS th1 (← AP_TERM tm3 (← ExceptT.mk (REAL_RAT_REDUCE_CONV tm4))))

  -- Complex polynomial normalizer.

  let COMPLEX_POLY_CLAUSES ← prove
   r"(!x y z. x + (y + z) = (x + y) + z) /\
     (!x y. x + y = y + x) /\
     (!x. Cx(&0) + x = x) /\
     (!x y z. x * (y * z) = (x * y) * z) /\
     (!x y. x * y = y * x) /\
     (!x. Cx(&1) * x = x) /\
     (!x. Cx(&0) * x = Cx(&0)) /\
     (!x y z. x * (y + z) = x * y + x * z) /\
     (!x. x pow 0 = Cx(&1)) /\
     (!x n. x pow (SUC n) = x * x pow n)"
   (REWRITE_TAC [complex_pow] THEN SIMPLE_COMPLEX_ARITH_TAC)

  let COMPLEX_POLY_NEG_CLAUSES ← prove
   r"(!x. --x = Cx(-- &1) * x) /\
     (!x y. x - y = x + Cx(-- &1) * y)"
   SIMPLE_COMPLEX_ARITH_TAC

  let P0 ← SEMIRING_NORMALIZERS_CONV COMPLEX_POLY_CLAUSES COMPLEX_POLY_NEG_CLAUSES
    is_complex_const COMPLEX_RAT_ADD_CONV COMPLEX_RAT_MUL_CONV COMPLEX_RAT_POW_CONV
    HolMath.RealArith.term_lt
  let COMPLEX_POLY_NEG_CONV := P0.POLYNOMIAL_NEG_CONV
  let COMPLEX_POLY_ADD_CONV := P0.POLYNOMIAL_ADD_CONV
  let COMPLEX_POLY_SUB_CONV := P0.POLYNOMIAL_SUB_CONV
  let COMPLEX_POLY_MUL_CONV := P0.POLYNOMIAL_MUL_CONV
  let COMPLEX_POLY_POW_CONV := P0.POLYNOMIAL_POW_CONV

  -- Extend it to handle "inv" and division, by constants after normalization.

  let COMPLEX_RAT_INV_CONV : ioconv :=
    REWR_CONV (← GSYM CX_INV) THENC RAND_CONV REAL_RAT_INV_CONV

  let COMPLEX_POLY_CONV : ioconv ← do
    let neg_tm ← q r"(--):complex->complex"
    let inv_tm ← q r"inv:complex->complex"
    let add_tm ← q r"(+):complex->complex->complex"
    let sub_tm ← q r"(-):complex->complex->complex"
    let mul_tm ← q r"(*):complex->complex->complex"
    let div_tm ← q r"(/):complex->complex->complex"
    let pow_tm ← q r"(pow):complex->num->complex"
    let div_conv := REWR_CONV complex_div
    let E : ComplexPolyConvEnv :=
      { neg_tm, inv_tm, add_tm, sub_tm, mul_tm, div_tm, pow_tm, div_conv, P := P0,
        COMPLEX_RAT_INV_CONV }
    pure (COMPLEX_POLY_CONV_rec E)

  -- Complex number version of usual ring procedure.

  let (COMPLEX_RING, complex_ideal_cofactors) ← do
    let COMPLEX_INTEGRAL ← prove
     r"(!x. Cx(&0) * x = Cx(&0)) /\
       (!x y z. (x + y = x + z) <=> (y = z)) /\
       (!w x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))"
     (REWRITE_TAC [COMPLEX_ENTIRE, ← SIMPLE_COMPLEX_ARITH
       (← q r"(w * y + x * z = w * z + x * y) <=>
        (w - x) * (y - z) = Cx(&0)")] THEN
      SIMPLE_COMPLEX_ARITH_TAC)
    let COMPLEX_RABINOWITSCH ← prove
     r"!x y:complex. ~(x = y) <=> ?z. (x - y) * z = Cx(&1)"
     (REPEAT GEN_TAC THEN
      GEN_REWRITE_TAC (fun c => LAND_CONV (RAND_CONV c)) [← GSYM COMPLEX_SUB_0] THEN
      MESON_TAC [COMPLEX_MUL_RINV, COMPLEX_MUL_LZERO,
                 ← SIMPLE_COMPLEX_ARITH (← q r"~(Cx(&1) = Cx(&0))")])
    let COMPLEX_IIII ← prove
     r"ii * ii + Cx(&1) = Cx(&0)"
     (REWRITE_TAC [ii, CX_DEF, complex_mul, complex_add, RE, IM] THEN
      AP_TERM_TAC THEN BINOP_TAC THEN REAL_ARITH_TAC)
    let (ring, ideal) ← RING_AND_IDEAL_CONV
      { ring_dest_const := dest_complex_const
        ring_mk_const := mk_complex_const
        RING_EQ_CONV := COMPLEX_RAT_EQ_CONV
        ring_neg_tm := ← q r"(--):complex->complex"
        ring_add_tm := ← q r"(+):complex->complex->complex"
        ring_sub_tm := ← q r"(-):complex->complex->complex"
        ring_inv_tm := ← q r"(inv):complex->complex"
        ring_mul_tm := ← q r"(*):complex->complex->complex"
        ring_div_tm := ← q r"(/):complex->complex->complex"
        ring_pow_tm := ← q r"(pow):complex->num->complex"
        RING_INTEGRAL := COMPLEX_INTEGRAL
        RABINOWITSCH_THM := COMPLEX_RABINOWITSCH
        RING_NORMALIZE_CONV := COMPLEX_POLY_CONV }
    let ii_tm ← q r"ii"
    let iiii_tm := concl COMPLEX_IIII
    let COMPLEX_RING : term → IO (Except String thm) := fun tm => ExceptT.run do
      if HolCore.Basics.free_in ii_tm tm then
        MP (← ExceptT.mk (ring (← liftExcept (HolCore.Bool.mk_imp iiii_tm tm)))) COMPLEX_IIII
      else ExceptT.mk (ring tm)
    pure (COMPLEX_RING, ideal)

  return { is_complex_const, dest_complex_const, mk_complex_const, COMPLEX_RAT_EQ_CONV,
           COMPLEX_RAT_MUL_CONV, COMPLEX_RAT_ADD_CONV, COMPLEX_RAT_POW_CONV,
           COMPLEX_POLY_CLAUSES, COMPLEX_POLY_NEG_CLAUSES, COMPLEX_POLY_NEG_CONV,
           COMPLEX_POLY_ADD_CONV, COMPLEX_POLY_SUB_CONV, COMPLEX_POLY_MUL_CONV,
           COMPLEX_POLY_POW_CONV, COMPLEX_RAT_INV_CONV, COMPLEX_POLY_CONV, COMPLEX_RING,
           complex_ideal_cofactors }

/- ------------------------------------------------------------------------- -/
/- Most basic properties of inverses; and also field procedure.            -/
/- (complex_algebra.ml 774-896)                                            -/
/- ------------------------------------------------------------------------- -/

structure CXE where
  COMPLEX_INV_0 : thm
  COMPLEX_INV_1 : thm
  COMPLEX_INV_MUL : thm
  COMPLEX_POW_INV : thm
  COMPLEX_INV_INV : thm
  COMPLEX_INV_DIV : thm
  COMPLEX_EQ_INV2 : thm
  SGN_RE_COMPLEX_INV : thm
  RE_COMPLEX_INV_GT_0 : thm
  RE_COMPLEX_INV_GE_0 : thm
  COMPLEX_EQ_MUL_LCANCEL : thm
  COMPLEX_EQ_MUL_RCANCEL : thm
  COMPLEX_FIELD : term → IO (Except String thm)
  deriving Inhabited

@[nospecialize]
def setupCXE [HolBase] (D : ComplexAlgebraDeps) (BCXA : CXA) (BCXB : CXB) (BCXC : CXC)
    (BCXD : CXD) : ExceptT String IO CXE := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, MESON, MESON_TAC, REAL_FIELD, NUM_REDUCE_CONV, .. } := D.cvx
  let { REAL_RAT_EQ_CONV, NNF_CONV, NNFC_CONV, PRENEX_CONV, WEAK_CNF_CONV, CONJ_CANON_CONV,
        CONDS_CELIM_CONV, .. } := D
  let { REAL_DIV_1, .. } := D.cvx.core3
  let { REAL_NOT_LT, REAL_OF_NUM_EQ, REAL_POW_LT, REAL_SGN_EQ, .. } := D.cvx.core5
  let { real_gt, .. } := D.cvx.core6
  let { NORM_POS_LT, .. } := D.cvx.vec3
  let { REAL_SGN_DIV, REAL_SOS_EQ_0, .. } := D.cpx
  let { CX_DEF, complex_mul, complex_inv, complex_div, complex_pow, RE, IM, COMPLEX_EQ,
        COMPLEX_SQNORM, SIMPLE_COMPLEX_ARITH_TAC, .. } := BCXA
  let { COMPLEX_MUL_AC, COMPLEX_MUL_RZERO, COMPLEX_MUL_LZERO, .. } := BCXB
  let { COMPLEX_MUL_RINV, COMPLEX_VEC_0, COMPLEX_POW_ADD, COMPLEX_POW_EQ_0, CX_INJ,
        .. } := BCXC
  let { COMPLEX_RING, .. } := BCXD
  -- @@SCOPE END

  -- Most basic properties of inverses.

  let COMPLEX_INV_0 ← prove
   r"inv(Cx(&0)) = Cx(&0)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_INV_1 ← prove
   r"inv(Cx(&1)) = Cx(&1)"
   SIMPLE_COMPLEX_ARITH_TAC

  let COMPLEX_INV_MUL ← prove
   r"!w z. inv(w * z) = inv(w) * inv(z)"
   (REPEAT GEN_TAC THEN
    MAP_EVERY ASM_CASES_TAC [← q r"w = Cx(&0)", ← q r"z = Cx(&0)"] THEN
    ASM_REWRITE_TAC [COMPLEX_INV_0, COMPLEX_MUL_LZERO, COMPLEX_MUL_RZERO] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    REWRITE_TAC [complex_mul, complex_inv, RE, IM, COMPLEX_EQ, CX_DEF] THEN
    REWRITE_TAC [← GSYM REAL_SOS_EQ_0] THEN CONV_TAC (fun t => REAL_FIELD t))

  let COMPLEX_POW_INV ← prove
   r"!x n. (inv x) pow n = inv(x pow n)"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [complex_pow, COMPLEX_INV_1, COMPLEX_INV_MUL])

  let COMPLEX_INV_INV ← prove
   r"!x:complex. inv(inv x) = x"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"x = Cx(&0)") THEN
    ASM_REWRITE_TAC [COMPLEX_INV_0] THEN
    POP_ASSUM MP_TAC THEN
    MAP_EVERY (MP_TAC o C SPEC COMPLEX_MUL_RINV)
     [← q r"x:complex", ← q r"inv(x):complex"] THEN
    CONV_TAC COMPLEX_RING)

  let COMPLEX_INV_DIV ← prove
   r"!w z:complex. inv(w / z) = z / w"
   (REWRITE_TAC [complex_div, COMPLEX_INV_MUL, COMPLEX_INV_INV] THEN
    REWRITE_TAC [COMPLEX_MUL_AC])

  let COMPLEX_EQ_INV2 ← prove
   r"!w z:complex. inv w = inv z <=> w = z"
   (MESON_TAC [COMPLEX_INV_INV])

  let SGN_RE_COMPLEX_INV ← prove
   r"!z. real_sgn(Re(inv z)) = real_sgn(Re z)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"z = Cx(&0)") THEN
    ASM_REWRITE_TAC [COMPLEX_INV_0] THEN
    REWRITE_TAC [RE, complex_inv, REAL_SGN_DIV] THEN
    SUBGOAL_THEN (← q r"real_sgn (Re z pow 2 + Im z pow 2) = &1")
     (fun th => REWRITE_TAC [REAL_DIV_1, th]) THEN
    REWRITE_TAC [REAL_SGN_EQ, real_gt, ← GSYM COMPLEX_SQNORM] THEN
    ASM_SIMP_TAC [REAL_POW_LT, NORM_POS_LT, COMPLEX_VEC_0])

  let RE_COMPLEX_INV_GT_0 ← prove
   r"!z. &0 < Re(inv z) <=> &0 < Re z"
   (REWRITE_TAC [← GSYM real_gt, ← GSYM REAL_SGN_EQ, SGN_RE_COMPLEX_INV])

  let RE_COMPLEX_INV_GE_0 ← prove
   r"!z. &0 <= Re(inv z) <=> &0 <= Re z"
   (REWRITE_TAC [← GSYM REAL_NOT_LT] THEN
    REWRITE_TAC [← GSYM REAL_SGN_EQ, SGN_RE_COMPLEX_INV])

  -- And also field procedure.

  let COMPLEX_EQ_MUL_LCANCEL ← prove
   r"!x y z. (x * y = x * z) <=> (x = Cx(&0)) \/ (y = z)"
   (CONV_TAC COMPLEX_RING)

  let COMPLEX_EQ_MUL_RCANCEL ← prove
   r"!x y z. (x * z = y * z) <=> (x = y) \/ (z = Cx(&0))"
   (CONV_TAC COMPLEX_RING)

  let COMPLEX_FIELD : term → IO (Except String thm) ← do
    let { FORALL_SIMP, EXISTS_SIMP, .. } := HolBase.T
    let gsymPowInv ← GSYM COMPLEX_POW_INV
    let powInvConv : ioconv := fun tm =>
      let ok := match (do rand (← rand tm) : Except String term) with
        | .ok r => HolMath.Nums.is_numeral r
        | .error _ => false
      if ok then REWR_CONV gsymPowInv tm else pure (.error "check")
    let seed ← ExceptT.mk (Simp.net_of_conv (← q r"inv((x:complex) pow n)") powInvConv
      HolCore.Nets.empty_net)
    let norm_net ← [FORALL_SIMP, EXISTS_SIMP, complex_div, COMPLEX_INV_INV, COMPLEX_INV_MUL,
        COMPLEX_POW_ADD].foldrM
      (fun th acc => do ExceptT.mk (Simp.net_of_thm HolBase.B false (← SPEC_ALL th) acc)) seed
    let easy_nz_conv :=
      LAND_CONV
       ((← GEN_REWRITE_CONV_NET TRY_CONV [← MESON [COMPLEX_POW_EQ_0, REAL_OF_NUM_EQ, CX_INJ]
         (← q r"~(x pow n = Cx(&0)) <=>
          ~((x:complex) = Cx(&0)) \/
          (Cx(&n) = Cx(&0)) \/
          ~(x pow n = Cx(&0))")]) THENC
        TOP_DEPTH_CONV (REWR_CONV CX_INJ THENC REAL_RAT_EQ_CONV)) THENC
      (← GEN_REWRITE_CONV_NET TRY_CONV [← TAUT (← q r"(T ==> p) <=> p")])
    let prenex_conv :=
      TOP_DEPTH_CONV BETA_CONV THENC
      NUM_REDUCE_CONV THENC
      TOP_DEPTH_CONV (REWRITES_CONV norm_net) THENC
      NNFC_CONV THENC DEPTH_BINOP_CONV (← q r"(/\)") CONDS_CELIM_CONV THENC
      PRENEX_CONV
    let setup_conv := NNF_CONV THENC WEAK_CNF_CONV THENC CONJ_CANON_CONV
    let is_inv ← do
      let inv_tm ← q r"inv:complex->complex"
      let is_div := HolCore.Basics.is_binop (← q r"(/):complex->complex->complex")
      pure (fun (tm : term) =>
        (is_div tm ||
          (is_comb tm && (match rator tm with | .ok r => r == inv_tm | .error _ => false)))
        && (match rand tm with
            | .ok r => !(HolMath.CalcInt.is_ratconst r) | .error _ => false))
    let BASIC_COMPLEX_FIELD (tm : term) : ExceptT String IO thm := do
      let is_freeinv (t : term) : Bool := is_inv t && HolCore.Basics.free_in t tm
      let itms := setify (← liftExcept ((HolCore.Basics.find_terms is_freeinv tm).mapM rand))
      let hyps ← itms.mapM (fun t => do CONV_RULE easy_nz_conv (← SPEC t COMPLEX_MUL_RINV))
      let tm' ← liftExcept (hyps.foldrM (fun th t => HolCore.Bool.mk_imp (concl th) t) tm)
      let th1 ← ExceptT.mk (setup_conv tm')
      let cjs := HolCore.Basics.conjuncts (← liftExcept (rand (concl th1)))
      let ths ← cjs.mapM (fun c => ExceptT.mk (COMPLEX_RING c))
      let th2 ← HolLight.EQ_MP (← SYM th1) (← HolLight.end_itlist CONJ ths)
      hyps.foldlM (fun th h => MP th h) th2
    pure (fun tm => ExceptT.run do
      let th0 ← ExceptT.mk (prenex_conv tm)
      let tm0 ← liftExcept (rand (concl th0))
      let (avs, bod) := HolCore.Basics.strip_forall tm0
      let th1 ← ExceptT.mk (setup_conv bod)
      let ths ← (HolCore.Basics.conjuncts (← liftExcept (rand (concl th1)))).mapM
        BASIC_COMPLEX_FIELD
      HolLight.EQ_MP (← SYM th0)
        (← GENL avs (← HolLight.EQ_MP (← SYM th1) (← HolLight.end_itlist CONJ ths))))

  return { COMPLEX_INV_0, COMPLEX_INV_1, COMPLEX_INV_MUL, COMPLEX_POW_INV, COMPLEX_INV_INV,
           COMPLEX_INV_DIV, COMPLEX_EQ_INV2, SGN_RE_COMPLEX_INV, RE_COMPLEX_INV_GT_0,
           RE_COMPLEX_INV_GE_0, COMPLEX_EQ_MUL_LCANCEL, COMPLEX_EQ_MUL_RCANCEL, COMPLEX_FIELD }

/- ------------------------------------------------------------------------- -/
/- More trivial lemmas; norms (aka "moduli").  (complex_algebra.ml 898-1039)       -/
/- ------------------------------------------------------------------------- -/

structure CXF where
  COMPLEX_DIV_1 : thm
  COMPLEX_DIV_LMUL : thm
  COMPLEX_DIV_RMUL : thm
  COMPLEX_INV_II : thm
  COMPLEX_INV_EQ_0 : thm
  COMPLEX_INV_NEG : thm
  COMPLEX_NEG_INV : thm
  COMPLEX_INV_EQ_1 : thm
  COMPLEX_DIV_EQ_0 : thm
  COMPLEX_POW_DIV : thm
  COMPLEX_DIV_POW : thm
  COMPLEX_DIV_POW2 : thm
  COMPLEX_NORM_ZERO : thm
  COMPLEX_NORM_NUM : thm
  COMPLEX_NORM_0 : thm
  COMPLEX_NORM_NZ : thm
  COMPLEX_NORM_MUL : thm
  COMPLEX_NORM_POW : thm
  COMPLEX_NORM_INV : thm
  COMPLEX_NORM_DIV : thm
  COMPLEX_NORM_TRIANGLE_SUB : thm
  COMPLEX_NORM_ABS_NORM : thm
  COMPLEX_POW_EQ_1 : thm
  deriving Inhabited

@[nospecialize]
def setupCXF [HolBase] (D : ComplexAlgebraDeps) (BCXA : CXA) (BCXB : CXB) (BCXC : CXC)
    (BCXE : CXE) : ExceptT String IO CXF := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON, MESON_TAC, REAL_ARITH,
        REAL_ARITH_TAC, .. } := D.cvx
  let { REAL_ABS_NUM, .. } := D.cvx.core3
  let { REAL_INV_0, REAL_LE_ADD, REAL_LE_INV_EQ, REAL_LE_MUL, .. } := D.cvx.core4
  let { REAL_MUL_AC, REAL_MUL_LID, REAL_MUL_LZERO, REAL_MUL_RINV, REAL_POW_2, SQRT_0,
        SQRT_1, SQRT_MUL, .. } := D.cvx.core5
  let { real_div, real_pow, .. } := D.cvx.core6
  let { NORM_EQ_0, .. } := D.cvx.vec2
  let { NORM_NEG, NORM_POS_LT, NORM_TRIANGLE, REAL_ABS_NORM, .. } := D.cvx.vec3
  let { REAL_LE_SQUARE, REAL_LE_SUB_RADD, REAL_MUL_RINV_UNIQ, REAL_POW_EQ_1, SUB_ADD,
        .. } := D.cpx
  let { complex_mul, complex_inv, complex_div, complex_pow, RE, IM, complex_sub,
        complex_norm, .. } := BCXA
  let { COMPLEX_ADD_ASSOC, COMPLEX_ADD_RID, COMPLEX_ADD_RINV, COMPLEX_NEG_0,
        COMPLEX_NEG_SUB, .. } := BCXB
  let { COMPLEX_ENTIRE, COMPLEX_VEC_0, COMPLEX_POW_ADD, COMPLEX_POW_MUL, COMPLEX_POW_EQ_0,
        COMPLEX_NORM_CX, .. } := BCXC
  let { COMPLEX_INV_0, COMPLEX_POW_INV, COMPLEX_EQ_MUL_RCANCEL, COMPLEX_FIELD, .. } := BCXE
  -- @@SCOPE END

  let COMPLEX_DIV_1 ← prove
   r"!z. z / Cx(&1) = z"
   (CONV_TAC COMPLEX_FIELD)

  let COMPLEX_DIV_LMUL ← prove
   r"!x y. ~(y = Cx(&0)) ==> y * x / y = x"
   (CONV_TAC COMPLEX_FIELD)

  let COMPLEX_DIV_RMUL ← prove
   r"!x y. ~(y = Cx(&0)) ==> x / y * y = x"
   (CONV_TAC COMPLEX_FIELD)

  let COMPLEX_INV_II ← prove
   r"inv ii = --ii"
   (CONV_TAC COMPLEX_FIELD)

  let COMPLEX_INV_EQ_0 ← prove
   r"!x. inv x = Cx(&0) <=> x = Cx(&0)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"x = Cx(&0)") THEN
    ASM_REWRITE_TAC [COMPLEX_INV_0] THEN POP_ASSUM MP_TAC THEN
    CONV_TAC COMPLEX_FIELD)

  let COMPLEX_INV_NEG ← prove
   r"!x:complex. inv(--x) = --(inv x)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"x = Cx(&0)") THEN
    ASM_REWRITE_TAC [COMPLEX_INV_0, COMPLEX_NEG_0] THEN
    POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD)

  let COMPLEX_NEG_INV ← prove
   r"!x:complex. --(inv x) = inv(--x)"
   (REWRITE_TAC [COMPLEX_INV_NEG])

  let COMPLEX_INV_EQ_1 ← prove
   r"!x. inv x = Cx(&1) <=> x = Cx(&1)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"x = Cx(&0)") THEN
    ASM_REWRITE_TAC [COMPLEX_INV_0] THEN POP_ASSUM MP_TAC THEN
    CONV_TAC COMPLEX_FIELD)

  let COMPLEX_DIV_EQ_0 ← prove
   r"!w z. w / z = Cx(&0) <=> w = Cx(&0) \/ z = Cx(&0)"
   (REWRITE_TAC [complex_div, COMPLEX_INV_EQ_0, COMPLEX_ENTIRE])

  let COMPLEX_POW_DIV ← prove
   r"!x y n. (x / y) pow n = (x pow n) / (y pow n)"
   (REWRITE_TAC [complex_div, COMPLEX_POW_MUL, COMPLEX_POW_INV])

  let COMPLEX_DIV_POW ← prove
   r"!x:complex n k:num.
        ~(x= Cx(&0)) /\ k <= n /\ ~(k = 0)
        ==> x pow (n - k) = x pow n / x pow k"
   (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"x:complex pow (n - k) * x pow k =
    x pow n / x pow k * x pow k") (fun th => ASM_MESON_TAC
    [th, COMPLEX_POW_EQ_0, COMPLEX_EQ_MUL_RCANCEL])
    THEN ASM_SIMP_TAC [← GSYM COMPLEX_POW_ADD, SUB_ADD] THEN
    MP_TAC (← MESON [COMPLEX_POW_EQ_0, ← ASSUME (← q r"~(k = 0)"),
                     ← ASSUME (← q r"~(x = Cx(&0))")]
    (← q r"~(x pow k = Cx(&0))")) THEN ASM_SIMP_TAC [COMPLEX_DIV_RMUL])

  let COMPLEX_DIV_POW2 ← prove
   r"!z m n. ~(z = Cx(&0))
             ==> z pow m / z pow n =
                 if n <= m then z pow (m - n) else inv(z pow (n - m))"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [COMPLEX_POW_EQ_0, ← ExceptT.mk (COMPLEX_FIELD
      (← q r"~(b = Cx(&0)) /\ ~(c = Cx(&0))
       ==> (a / b = inv c <=> a * c = b)"))] THEN
    ASM_SIMP_TAC [COMPLEX_POW_EQ_0, ← ExceptT.mk (COMPLEX_FIELD
     (← q r"~(b = Cx(&0)) ==> (a / b = c <=> b * c = a)"))] THEN
    REWRITE_TAC [← GSYM COMPLEX_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC)

  -- Norms (aka "moduli").

  let COMPLEX_NORM_ZERO ← prove
   r"!z. (norm z = &0) <=> (z = Cx(&0))"
   (REWRITE_TAC [NORM_EQ_0, COMPLEX_VEC_0])

  let COMPLEX_NORM_NUM ← prove
   r"!n. norm(Cx(&n)) = &n"
   (REWRITE_TAC [COMPLEX_NORM_CX, REAL_ABS_NUM])

  let COMPLEX_NORM_0 ← prove
   r"norm(Cx(&0)) = &0"
   (MESON_TAC [COMPLEX_NORM_ZERO])

  let COMPLEX_NORM_NZ ← prove
   r"!z. &0 < norm(z) <=> ~(z = Cx(&0))"
   (REWRITE_TAC [NORM_POS_LT, COMPLEX_VEC_0])

  let COMPLEX_NORM_MUL ← prove
   r"!w z. norm(w * z) = norm(w) * norm(z)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [complex_norm, complex_mul, RE, IM] THEN
    SIMP_TAC [← GSYM SQRT_MUL, REAL_POW_2, REAL_LE_ADD, REAL_LE_SQUARE] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC)

  let COMPLEX_NORM_POW ← prove
   r"!z n. norm(z pow n) = norm(z) pow n"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [complex_pow, real_pow, COMPLEX_NORM_NUM, COMPLEX_NORM_MUL])

  let COMPLEX_NORM_INV ← prove
   r"!z. norm(inv z) = inv(norm z)"
   (GEN_TAC THEN REWRITE_TAC [complex_norm, complex_inv, RE, IM] THEN
    REWRITE_TAC [REAL_POW_2, real_div] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"(r * d) * r * d + (--i * d) * --i * d =
                            (r * r + i * i) * d * d:real")] THEN
    ASM_CASES_TAC (← q r"Re z * Re z + Im z * Im z = &0") THENL
     [ASM_REWRITE_TAC [REAL_INV_0, SQRT_0, REAL_MUL_LZERO], ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_MUL_RINV_UNIQ THEN
    SIMP_TAC [← GSYM SQRT_MUL, REAL_LE_MUL, REAL_LE_INV_EQ, REAL_LE_ADD,
              REAL_LE_SQUARE] THEN
    ONCE_REWRITE_TAC [← AC REAL_MUL_AC
     (← q r"a * a * b * b:real = (a * b) * (a * b)")] THEN
    ASM_SIMP_TAC [REAL_MUL_RINV, REAL_MUL_LID, SQRT_1])

  let COMPLEX_NORM_DIV ← prove
   r"!w z. norm(w / z) = norm(w) / norm(z)"
   (REWRITE_TAC [complex_div, real_div, COMPLEX_NORM_INV, COMPLEX_NORM_MUL])

  let COMPLEX_NORM_TRIANGLE_SUB ← prove
   r"!w z. norm(w) <= norm(w + z) + norm(z)"
   (MESON_TAC [NORM_TRIANGLE, NORM_NEG, COMPLEX_ADD_ASSOC,
               COMPLEX_ADD_RINV, COMPLEX_ADD_RID])

  let COMPLEX_NORM_ABS_NORM ← prove
   r"!w z. abs(norm w - norm z) <= norm(w - z)"
   (REPEAT GEN_TAC THEN
    MATCH_MP_TAC (← REAL_ARITH
     (← q r"a - b <= x /\ b - a <= x ==> abs(a - b) <= x:real")) THEN
    MESON_TAC [COMPLEX_NEG_SUB, NORM_NEG, REAL_LE_SUB_RADD, complex_sub,
               COMPLEX_NORM_TRIANGLE_SUB])

  let COMPLEX_POW_EQ_1 ← prove
   r"!z n. z pow n = Cx(&1) ==> norm(z) = &1 \/ n = 0"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"norm:complex->real")) THEN
    SIMP_TAC [COMPLEX_NORM_POW, COMPLEX_NORM_CX, REAL_POW_EQ_1, REAL_ABS_NUM] THEN
    SIMP_TAC [REAL_ABS_NORM] THEN CONV_TAC (fun t => TAUT t))

  return { COMPLEX_DIV_1, COMPLEX_DIV_LMUL, COMPLEX_DIV_RMUL, COMPLEX_INV_II,
           COMPLEX_INV_EQ_0, COMPLEX_INV_NEG, COMPLEX_NEG_INV, COMPLEX_INV_EQ_1,
           COMPLEX_DIV_EQ_0, COMPLEX_POW_DIV, COMPLEX_DIV_POW, COMPLEX_DIV_POW2,
           COMPLEX_NORM_ZERO, COMPLEX_NORM_NUM, COMPLEX_NORM_0, COMPLEX_NORM_NZ,
           COMPLEX_NORM_MUL, COMPLEX_NORM_POW, COMPLEX_NORM_INV, COMPLEX_NORM_DIV,
           COMPLEX_NORM_TRIANGLE_SUB, COMPLEX_NORM_ABS_NORM, COMPLEX_POW_EQ_1 }

/- ------------------------------------------------------------------------- -/
/- Complex conjugate; conjugation is an automorphism; slightly ad hoc      -/
/- theorems relating multiplication, inverse and conjugation; norm versus  -/
/- components for complex numbers.  (complex_algebra.ml 1041-1304)         -/
/- ------------------------------------------------------------------------- -/

structure CXG where
  cnj : thm
  CNJ_INJ : thm
  CNJ_CNJ : thm
  CNJ_CX : thm
  COMPLEX_NORM_CNJ : thm
  CNJ_NEG : thm
  CNJ_INV : thm
  CNJ_ADD : thm
  CNJ_SUB : thm
  CNJ_MUL : thm
  CNJ_DIV : thm
  CNJ_POW : thm
  RE_CNJ : thm
  IM_CNJ : thm
  CNJ_EQ_CX : thm
  CNJ_EQ_0 : thm
  COMPLEX_ADD_CNJ : thm
  CNJ_II : thm
  CX_RE_CNJ : thm
  CX_IM_CNJ : thm
  FORALL_CNJ : thm
  EXISTS_CNJ : thm
  COMPLEX_NORM_POW_2 : thm
  COMPLEX_MUL_CNJ : thm
  COMPLEX_INV_CNJ : thm
  COMPLEX_DIV_CNJ : thm
  RE_COMPLEX_DIV_EQ_0 : thm
  IM_COMPLEX_DIV_EQ_0 : thm
  RE_COMPLEX_DIV_GT_0 : thm
  IM_COMPLEX_DIV_GT_0 : thm
  RE_COMPLEX_DIV_GE_0 : thm
  IM_COMPLEX_DIV_GE_0 : thm
  RE_COMPLEX_DIV_LE_0 : thm
  IM_COMPLEX_DIV_LE_0 : thm
  RE_COMPLEX_DIV_LT_0 : thm
  IM_COMPLEX_DIV_LT_0 : thm
  IM_COMPLEX_INV_GE_0 : thm
  IM_COMPLEX_INV_LE_0 : thm
  IM_COMPLEX_INV_GT_0 : thm
  IM_COMPLEX_INV_LT_0 : thm
  IM_COMPLEX_INV_EQ_0 : thm
  REAL_SGN_RE_COMPLEX_DIV : thm
  REAL_SGN_IM_COMPLEX_DIV : thm
  COMPLEX_NORM_GE_RE_IM : thm
  COMPLEX_NORM_LE_RE_IM : thm
  COMPLEX_L1_LE_NORM : thm
  deriving Inhabited

@[nospecialize]
def setupCXG [HolBase] (D : ComplexAlgebraDeps) (BCXA : CXA) (BCXB : CXB) (BCXC : CXC)
    (BCXE : CXE) (BCXF : CXF) : ExceptT String IO CXG := do
  -- @@SCOPE BEGIN
  let { new_definition, INDUCT_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_RING,
        .. } := D.cvx
  let { ARITH, DIMINDEX_2, .. } := D.cvx.core1
  let { REAL_ENTIRE, REAL_EQ_NEG2, REAL_INV_EQ_0, REAL_LE_ADDL, REAL_LE_ADDR,
        REAL_LE_ANTISYM, REAL_LT_INV_EQ, .. } := D.cvx.core4
  let { REAL_MUL_LNEG, REAL_MUL_LZERO, REAL_MUL_RNEG, REAL_NEG_0, REAL_NEG_ADD,
        REAL_NEG_NEG, REAL_NOT_LE, REAL_NOT_LT, REAL_OF_NUM_LT, REAL_POS, REAL_POW_2,
        REAL_POW_EQ_0, REAL_POW_LT, SQRT_POW_2, .. } := D.cvx.core5
  let { real_div, .. } := D.cvx.core6
  let { NORM_LE_L1, .. } := D.cvx.vec3
  let { POW_2_SQRT_ABS, REAL_LE_LCANCEL_IMP, REAL_LE_SQUARE, REAL_LT_RMUL_EQ, SQRT_MONO_LE,
        SQRT_POS_LT, real_sgn, L1_LE_NORM, SUM_2, .. } := D.cpx
  let { RE_DEF, IM_DEF, CX_DEF, ii, complex_mul, complex_inv, complex_div, complex_pow, RE,
        IM, COMPLEX_EQ, complex_neg, complex_add, complex_sub, complex_norm,
        COMPLEX_SQNORM, .. } := BCXA
  let { COMPLEX_MUL_SYM, COMPLEX_MUL_ASSOC, COMPLEX_MUL_LID, COMPLEX_MUL_RZERO,
        COMPLEX_MUL_LZERO, COMPLEX_MUL_LNEG, .. } := BCXB
  let { CX_INJ, CX_INV, CX_POW, RE_CX, RE_NEG, RE_ADD, RE_SUB, IM_CX, IM_NEG, IM_ADD,
        IM_SUB, RE_MUL_II, IM_MUL_II, RE_MUL_CX, IM_MUL_CX, RE_DIV_CX, IM_DIV_CX,
        .. } := BCXC
  let { COMPLEX_INV_0, COMPLEX_INV_INV, COMPLEX_FIELD, .. } := BCXE
  let { COMPLEX_NORM_ZERO, COMPLEX_NORM_NZ, .. } := BCXF
  -- @@SCOPE END

  -- Complex conjugate.

  let cnj ← new_definition
   r"cnj(z) = complex(Re(z),--(Im(z)))"

  -- Conjugation is an automorphism.

  let CNJ_INJ ← prove
   r"!w z. (cnj(w) = cnj(z)) <=> (w = z)"
   (REWRITE_TAC [cnj, COMPLEX_EQ, RE, IM, REAL_EQ_NEG2])

  let CNJ_CNJ ← prove
   r"!z. cnj(cnj z) = z"
   (REWRITE_TAC [cnj, COMPLEX_EQ, RE, IM, REAL_NEG_NEG])

  let CNJ_CX ← prove
   r"!x. cnj(Cx x) = Cx x"
   (REWRITE_TAC [cnj, COMPLEX_EQ, CX_DEF, REAL_NEG_0, RE, IM])

  let COMPLEX_NORM_CNJ ← prove
   r"!z. norm(cnj z) = norm(z)"
   (REWRITE_TAC [complex_norm, cnj, REAL_POW_2] THEN
    REWRITE_TAC [REAL_MUL_LNEG, REAL_MUL_RNEG, RE, IM, REAL_NEG_NEG])

  let CNJ_NEG ← prove
   r"!z. cnj(--z) = --(cnj z)"
   (REWRITE_TAC [cnj, complex_neg, COMPLEX_EQ, RE, IM])

  let CNJ_INV ← prove
   r"!z. cnj(inv z) = inv(cnj z)"
   (REWRITE_TAC [cnj, complex_inv, COMPLEX_EQ, RE, IM] THEN
    REWRITE_TAC [real_div, REAL_NEG_NEG, REAL_POW_2,
                 REAL_MUL_LNEG, REAL_MUL_RNEG])

  let CNJ_ADD ← prove
   r"!w z. cnj(w + z) = cnj(w) + cnj(z)"
   (REWRITE_TAC [cnj, complex_add, COMPLEX_EQ, RE, IM] THEN
    REWRITE_TAC [REAL_NEG_ADD, REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_NEG])

  let CNJ_SUB ← prove
   r"!w z. cnj(w - z) = cnj(w) - cnj(z)"
   (REWRITE_TAC [complex_sub, CNJ_ADD, CNJ_NEG])

  let CNJ_MUL ← prove
   r"!w z. cnj(w * z) = cnj(w) * cnj(z)"
   (REWRITE_TAC [cnj, complex_mul, COMPLEX_EQ, RE, IM] THEN
    REWRITE_TAC [REAL_NEG_ADD, REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_NEG])

  let CNJ_DIV ← prove
   r"!w z. cnj(w / z) = cnj(w) / cnj(z)"
   (REWRITE_TAC [complex_div, CNJ_MUL, CNJ_INV])

  let CNJ_POW ← prove
   r"!z n. cnj(z pow n) = cnj(z) pow n"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [complex_pow, CNJ_MUL, CNJ_CX])

  let RE_CNJ ← prove
   r"!z. Re(cnj z) = Re z"
   (REWRITE_TAC [cnj, RE])

  let IM_CNJ ← prove
   r"!z. Im(cnj z) = --Im z"
   (REWRITE_TAC [cnj, IM])

  let CNJ_EQ_CX ← prove
   r"!x z. cnj z = Cx x <=> z = Cx x"
   (REWRITE_TAC [COMPLEX_EQ, RE_CNJ, IM_CNJ, RE_CX, IM_CX] THEN
    CONV_TAC (fun t => REAL_RING t))

  let CNJ_EQ_0 ← prove
   r"!z. cnj z = Cx(&0) <=> z = Cx(&0)"
   (REWRITE_TAC [CNJ_EQ_CX])

  let COMPLEX_ADD_CNJ ← prove
   r"(!z. z + cnj z = Cx(&2 * Re z)) /\ (!z. cnj z + z = Cx(&2 * Re z))"
   (REWRITE_TAC [COMPLEX_EQ, RE_CX, IM_CX, RE_ADD, IM_ADD, RE_CNJ, IM_CNJ] THEN
    REAL_ARITH_TAC)

  let CNJ_II ← prove
   r"cnj ii = --ii"
   (REWRITE_TAC [cnj, ii, RE, IM, complex_neg, REAL_NEG_0])

  let CX_RE_CNJ ← prove
   r"!z. Cx(Re z) = (z + cnj z) / Cx(&2)"
   (REWRITE_TAC [COMPLEX_EQ, RE_DIV_CX, IM_DIV_CX, RE_CX, IM_CX] THEN
    REWRITE_TAC [RE_ADD, IM_ADD, RE_CNJ, IM_CNJ] THEN REAL_ARITH_TAC)

  let CX_IM_CNJ ← prove
   r"!z. Cx(Im z) = --ii * (z - cnj z) / Cx(&2)"
   (REWRITE_TAC [COMPLEX_EQ, RE_DIV_CX, IM_DIV_CX, RE_CX, IM_CX,
                 COMPLEX_MUL_LNEG, RE_NEG, IM_NEG, RE_MUL_II, IM_MUL_II] THEN
    REWRITE_TAC [RE_SUB, IM_SUB, RE_CNJ, IM_CNJ] THEN REAL_ARITH_TAC)

  let FORALL_CNJ ← prove
   r"(!z. P(cnj z)) <=> (!z. P z)"
   (MESON_TAC [CNJ_CNJ])

  let EXISTS_CNJ ← prove
   r"(?z. P(cnj z)) <=> (?z. P z)"
   (MESON_TAC [CNJ_CNJ])

  -- Slightly ad hoc theorems relating multiplication, inverse and conjugation.

  let COMPLEX_NORM_POW_2 ← prove
   r"!z. Cx(norm z) pow 2 = z * cnj z"
   (GEN_TAC THEN REWRITE_TAC [← GSYM CX_POW, COMPLEX_SQNORM] THEN
    REWRITE_TAC [cnj, complex_mul, CX_DEF, RE, IM, COMPLEX_EQ] THEN
    CONV_TAC (fun t => REAL_RING t))

  let COMPLEX_MUL_CNJ ← prove
   r"!z. cnj z * z = Cx(norm(z)) pow 2 /\ z * cnj z = Cx(norm(z)) pow 2"
   (GEN_TAC THEN REWRITE_TAC [COMPLEX_MUL_SYM] THEN
    REWRITE_TAC [cnj, complex_mul, RE, IM, ← GSYM CX_POW, COMPLEX_SQNORM] THEN
    REWRITE_TAC [CX_DEF] THEN AP_TERM_TAC THEN BINOP_TAC THEN
    CONV_TAC (fun t => REAL_RING t))

  let COMPLEX_INV_CNJ ← prove
   r"!z. inv z = cnj z / Cx(norm z) pow 2"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"z = Cx(&0)") THENL
     [ASM_REWRITE_TAC [CNJ_CX, complex_div, COMPLEX_INV_0, COMPLEX_MUL_LZERO],
      MATCH_MP_TAC (← ExceptT.mk (COMPLEX_FIELD
       (← q r"x * y = z /\ ~(x = Cx(&0)) /\ ~(z = Cx(&0)) ==> inv x = y / z"))) THEN
      ASM_REWRITE_TAC [COMPLEX_MUL_CNJ, ← GSYM CX_POW, CX_INJ, REAL_POW_EQ_0] THEN
      ASM_REWRITE_TAC [COMPLEX_NORM_ZERO, ARITH]])

  let COMPLEX_DIV_CNJ ← prove
   r"!a b. a / b = (a * cnj b) / Cx(norm b) pow 2"
   (REPEAT GEN_TAC THEN REWRITE_TAC [complex_div, ← GSYM COMPLEX_MUL_ASSOC] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC LAND_CONV [COMPLEX_INV_CNJ] THEN
    REWRITE_TAC [complex_div])

  let RE_COMPLEX_DIV_EQ_0 ← prove
   r"!a b. Re(a / b) = &0 <=> Re(a * cnj b) = &0"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [COMPLEX_DIV_CNJ] THEN
    REWRITE_TAC [complex_div, ← GSYM CX_POW, ← GSYM CX_INV] THEN
    REWRITE_TAC [RE_MUL_CX, REAL_INV_EQ_0, REAL_POW_EQ_0, ARITH,
                 REAL_ENTIRE, COMPLEX_NORM_ZERO] THEN
    ASM_CASES_TAC (← q r"b = Cx(&0)") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [CNJ_CX, COMPLEX_MUL_RZERO, RE_CX])

  let IM_COMPLEX_DIV_EQ_0 ← prove
   r"!a b. Im(a / b) = &0 <=> Im(a * cnj b) = &0"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [COMPLEX_DIV_CNJ] THEN
    REWRITE_TAC [complex_div, ← GSYM CX_POW, ← GSYM CX_INV] THEN
    REWRITE_TAC [IM_MUL_CX, REAL_INV_EQ_0, REAL_POW_EQ_0, ARITH,
                 REAL_ENTIRE, COMPLEX_NORM_ZERO] THEN
    ASM_CASES_TAC (← q r"b = Cx(&0)") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [CNJ_CX, COMPLEX_MUL_RZERO, IM_CX])

  let RE_COMPLEX_DIV_GT_0 ← prove
   r"!a b. &0 < Re(a / b) <=> &0 < Re(a * cnj b)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [COMPLEX_DIV_CNJ] THEN
    REWRITE_TAC [complex_div, ← GSYM CX_POW, ← GSYM CX_INV] THEN
    REWRITE_TAC [RE_MUL_CX, REAL_INV_EQ_0, REAL_POW_EQ_0, ARITH,
                 REAL_ENTIRE, COMPLEX_NORM_ZERO] THEN
    ASM_CASES_TAC (← q r"b = Cx(&0)") THEN
    ASM_REWRITE_TAC [CNJ_CX, COMPLEX_MUL_RZERO, RE_CX, REAL_MUL_LZERO] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"&0 < a * x <=> &0 * x < a * x")] THEN
    ASM_SIMP_TAC [REAL_LT_RMUL_EQ, REAL_LT_INV_EQ, REAL_POW_LT, ARITH,
                  COMPLEX_NORM_NZ])

  let IM_COMPLEX_DIV_GT_0 ← prove
   r"!a b. &0 < Im(a / b) <=> &0 < Im(a * cnj b)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [COMPLEX_DIV_CNJ] THEN
    REWRITE_TAC [complex_div, ← GSYM CX_POW, ← GSYM CX_INV] THEN
    REWRITE_TAC [IM_MUL_CX, REAL_INV_EQ_0, REAL_POW_EQ_0, ARITH,
                 REAL_ENTIRE, COMPLEX_NORM_ZERO] THEN
    ASM_CASES_TAC (← q r"b = Cx(&0)") THEN
    ASM_REWRITE_TAC [CNJ_CX, COMPLEX_MUL_RZERO, IM_CX, REAL_MUL_LZERO] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"&0 < a * x <=> &0 * x < a * x")] THEN
    ASM_SIMP_TAC [REAL_LT_RMUL_EQ, REAL_LT_INV_EQ, REAL_POW_LT, ARITH,
                  COMPLEX_NORM_NZ])

  let RE_COMPLEX_DIV_GE_0 ← prove
   r"!a b. &0 <= Re(a / b) <=> &0 <= Re(a * cnj b)"
   (REWRITE_TAC [← REAL_ARITH (← q r"&0 <= x <=> &0 < x \/ x = &0")] THEN
    REWRITE_TAC [RE_COMPLEX_DIV_GT_0, RE_COMPLEX_DIV_EQ_0])

  let IM_COMPLEX_DIV_GE_0 ← prove
   r"!a b. &0 <= Im(a / b) <=> &0 <= Im(a * cnj b)"
   (REWRITE_TAC [← REAL_ARITH (← q r"&0 <= x <=> &0 < x \/ x = &0")] THEN
    REWRITE_TAC [IM_COMPLEX_DIV_GT_0, IM_COMPLEX_DIV_EQ_0])

  let RE_COMPLEX_DIV_LE_0 ← prove
   r"!a b. Re(a / b) <= &0 <=> Re(a * cnj b) <= &0"
   (REWRITE_TAC [← GSYM REAL_NOT_LT, RE_COMPLEX_DIV_GT_0])

  let IM_COMPLEX_DIV_LE_0 ← prove
   r"!a b. Im(a / b) <= &0 <=> Im(a * cnj b) <= &0"
   (REWRITE_TAC [← GSYM REAL_NOT_LT, IM_COMPLEX_DIV_GT_0])

  let RE_COMPLEX_DIV_LT_0 ← prove
   r"!a b. Re(a / b) < &0 <=> Re(a * cnj b) < &0"
   (REWRITE_TAC [← GSYM REAL_NOT_LE, RE_COMPLEX_DIV_GE_0])

  let IM_COMPLEX_DIV_LT_0 ← prove
   r"!a b. Im(a / b) < &0 <=> Im(a * cnj b) < &0"
   (REWRITE_TAC [← GSYM REAL_NOT_LE, IM_COMPLEX_DIV_GE_0])

  let IM_COMPLEX_INV_GE_0 ← prove
   r"!z. &0 <= Im(inv z) <=> Im(z) <= &0"
   (GEN_TAC THEN MP_TAC (← ISPECL [← q r"Cx(&1)", ← q r"z:complex"] IM_COMPLEX_DIV_GE_0) THEN
    REWRITE_TAC [complex_div, COMPLEX_MUL_LID, IM_CNJ] THEN REAL_ARITH_TAC)

  let IM_COMPLEX_INV_LE_0 ← prove
   r"!z. Im(inv z) <= &0 <=> &0 <= Im(z)"
   (MESON_TAC [IM_COMPLEX_INV_GE_0, COMPLEX_INV_INV])

  let IM_COMPLEX_INV_GT_0 ← prove
   r"!z. &0 < Im(inv z) <=> Im(z) < &0"
   (REWRITE_TAC [← REAL_ARITH (← q r"&0 < a <=> ~(a <= &0)"), IM_COMPLEX_INV_LE_0] THEN
    REAL_ARITH_TAC)

  let IM_COMPLEX_INV_LT_0 ← prove
   r"!z. Im(inv z) < &0 <=> &0 < Im(z)"
   (REWRITE_TAC [← REAL_ARITH (← q r"a < &0 <=> ~(&0 <= a)"), IM_COMPLEX_INV_GE_0] THEN
    REAL_ARITH_TAC)

  let IM_COMPLEX_INV_EQ_0 ← prove
   r"!z. Im(inv z) = &0 <=> Im(z) = &0"
   (SIMP_TAC [← GSYM REAL_LE_ANTISYM, IM_COMPLEX_INV_LE_0, IM_COMPLEX_INV_GE_0] THEN
    REAL_ARITH_TAC)

  let REAL_SGN_RE_COMPLEX_DIV ← prove
   r"!w z. real_sgn(Re(w / z)) = real_sgn(Re(w * cnj z))"
   (REWRITE_TAC [real_sgn, RE_COMPLEX_DIV_GT_0, RE_COMPLEX_DIV_GE_0,
                 ← REAL_ARITH (← q r"x < &0 <=> ~(&0 <= x)")])

  let REAL_SGN_IM_COMPLEX_DIV ← prove
   r"!w z. real_sgn(Im(w / z)) = real_sgn(Im(w * cnj z))"
   (REWRITE_TAC [real_sgn, IM_COMPLEX_DIV_GT_0, IM_COMPLEX_DIV_GE_0,
                 ← REAL_ARITH (← q r"x < &0 <=> ~(&0 <= x)")])

  -- Norm versus components for complex numbers.

  let COMPLEX_NORM_GE_RE_IM ← prove
   r"!z. abs(Re(z)) <= norm(z) /\ abs(Im(z)) <= norm(z)"
   (GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM POW_2_SQRT_ABS] THEN
    REWRITE_TAC [complex_norm] THEN
    CONJ_TAC THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN
    ASM_SIMP_TAC [REAL_LE_ADDR, REAL_LE_ADDL, REAL_POW_2, REAL_LE_SQUARE])

  let COMPLEX_NORM_LE_RE_IM ← prove
   r"!z. norm(z) <= abs(Re z) + abs(Im z)"
   (GEN_TAC THEN MP_TAC (← ISPEC (← q r"z:complex") NORM_LE_L1) THEN
    REWRITE_TAC [DIMINDEX_2, SUM_2, RE_DEF, IM_DEF])

  let COMPLEX_L1_LE_NORM ← prove
   r"!z. sqrt(&2) / &2 * (abs(Re z) + abs(Im z)) <= norm z"
   (GEN_TAC THEN MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC (← q r"sqrt(&2)") THEN
    SIMP_TAC [← REAL_ARITH (← q r"x * x / &2 * y = (x pow 2) / &2 * y"),
              SQRT_POW_2, REAL_POS, SQRT_POS_LT, REAL_OF_NUM_LT, ARITH] THEN
    MP_TAC (← ISPEC (← q r"z:complex") L1_LE_NORM) THEN
    REWRITE_TAC [DIMINDEX_2, SUM_2, RE_DEF, IM_DEF] THEN REAL_ARITH_TAC)

  return { cnj, CNJ_INJ, CNJ_CNJ, CNJ_CX, COMPLEX_NORM_CNJ, CNJ_NEG, CNJ_INV, CNJ_ADD,
           CNJ_SUB, CNJ_MUL, CNJ_DIV, CNJ_POW, RE_CNJ, IM_CNJ, CNJ_EQ_CX, CNJ_EQ_0,
           COMPLEX_ADD_CNJ, CNJ_II, CX_RE_CNJ, CX_IM_CNJ, FORALL_CNJ, EXISTS_CNJ,
           COMPLEX_NORM_POW_2, COMPLEX_MUL_CNJ, COMPLEX_INV_CNJ, COMPLEX_DIV_CNJ,
           RE_COMPLEX_DIV_EQ_0, IM_COMPLEX_DIV_EQ_0, RE_COMPLEX_DIV_GT_0, IM_COMPLEX_DIV_GT_0,
           RE_COMPLEX_DIV_GE_0, IM_COMPLEX_DIV_GE_0, RE_COMPLEX_DIV_LE_0, IM_COMPLEX_DIV_LE_0,
           RE_COMPLEX_DIV_LT_0, IM_COMPLEX_DIV_LT_0, IM_COMPLEX_INV_GE_0, IM_COMPLEX_INV_LE_0,
           IM_COMPLEX_INV_GT_0, IM_COMPLEX_INV_LT_0, IM_COMPLEX_INV_EQ_0,
           REAL_SGN_RE_COMPLEX_DIV, REAL_SGN_IM_COMPLEX_DIV, COMPLEX_NORM_GE_RE_IM,
           COMPLEX_NORM_LE_RE_IM, COMPLEX_L1_LE_NORM }

/- ------------------------------------------------------------------------- -/
/- Complex square roots; a few more complex-specific cases of vector notions. -/
/- (complex_algebra.ml 1306-1498)                                          -/
/- ------------------------------------------------------------------------- -/

structure CXH where
  csqrt : thm
  CSQRT : thm
  CX_SQRT : thm
  CSQRT_CX : thm
  CSQRT_0 : thm
  CSQRT_1 : thm
  CSQRT_PRINCIPAL : thm
  RE_CSQRT : thm
  CSQRT_UNIQUE : thm
  POW_2_CSQRT : thm
  CSQRT_EQ_0 : thm
  DOT_COMPLEX_MUL_CNJ : thm
  DOT_CNJ : thm
  LINEAR_COMPLEX_MUL : thm
  BILINEAR_COMPLEX_MUL : thm
  LINEAR_CNJ : thm
  LINEAR_COMPLEX_LMUL : thm
  LINEAR_COMPLEX_RMUL : thm
  COMPLEX_CAUCHY_SCHWARZ_EQ : thm
  COMPLEX_BASIS : thm
  COMPLEX_LINEAR : thm
  COMPLEX_LINEAR_ALT : thm
  deriving Inhabited

@[nospecialize]
def setupCXH [HolBase] (D : ComplexAlgebraDeps) (BCXA : CXA) (BCXB : CXB) (BCXC : CXC)
    (BCXD : CXD) (BCXG : CXG) : ExceptT String IO CXH := do
  -- @@SCOPE BEGIN
  let { new_definition, ASM_REAL_ARITH_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC,
        REAL_RAT_REDUCE_CONV, .. } := D.cvx
  let { ARITH, CART_EQ, DIMINDEX_2, .. } := D.cvx.core1
  let { FUN_EQ_THM, .. } := D.cvx.core2
  let { LAMBDA_BETA, MONO_FORALL, REAL_ABS_INV, REAL_ABS_MUL, REAL_ABS_NUM, REAL_ADD_LID,
        REAL_DIV_REFL, .. } := D.cvx.core3
  let { REAL_ENTIRE, REAL_LE_ADD, REAL_LE_DIV, REAL_LT_ADDR, .. } := D.cvx.core4
  let { REAL_MUL_AC, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LZERO, REAL_MUL_RID,
        REAL_MUL_RZERO, REAL_NEG_EQ, REAL_POS, REAL_POW2_ABS, REAL_POW_2, REAL_POW_DIV,
        REAL_POW_EQ_0, REAL_POW_MUL, REAL_SUB_RDISTRIB, REAL_SUB_RZERO, SQRT_0, SQRT_1,
        SQRT_MUL, SQRT_POS_LE, SQRT_POW_2, .. } := D.cvx.core5
  let { real_div, real_ge, .. } := D.cvx.core6
  let { BASIS_COMPONENT, DOT_2, .. } := D.cvx.vec1
  let { NORM_POW_2, .. } := D.cvx.vec3
  let { bilinear, linear, matrix_vector_mul, .. } := D.cvx.vec4
  let { POW_2_SQRT_ABS, REAL_ABS_ZERO, REAL_ADD_SUB, REAL_DIFFSQ, REAL_LE_SQUARE,
        REAL_SUB_LZERO, SQRT_MONO_LT, SQRT_POS_LT, FORALL_2, MATRIX_VECTOR_MUL,
        MATRIX_VECTOR_MUL_COMPONENT, SUM_2, matrix, .. } := D.cpx
  let { RE_DEF, IM_DEF, CX_DEF, ii, complex_mul, RE, IM, COMPLEX_EQ, complex_norm,
        SIMPLE_COMPLEX_ARITH_TAC, .. } := BCXA
  let { COMPLEX_MUL_SYM, .. } := BCXB
  let { COMPLEX_CMUL, COMPLEX_POW_2, RE_CX, RE_NEG, IM_CX, IM_NEG, RE_II, IM_II, RE_MUL_II,
        IM_MUL_II, .. } := BCXC
  let { COMPLEX_RING, .. } := BCXD
  let { cnj, CNJ_CX, CNJ_ADD, CNJ_MUL, COMPLEX_NORM_GE_RE_IM, .. } := BCXG
  -- @@SCOPE END

  -- Complex square roots.

  let csqrt ← new_definition
   r"csqrt(z) = if Im(z) = &0 then
                  if &0 <= Re(z) then complex(sqrt(Re(z)),&0)
                  else complex(&0,sqrt(--Re(z)))
                else complex(sqrt((norm(z) + Re(z)) / &2),
                             (Im(z) / abs(Im(z))) *
                             sqrt((norm(z) - Re(z)) / &2))"

  let CSQRT ← prove
   r"!z. csqrt(z) pow 2 = z"
   (GEN_TAC THEN REWRITE_TAC [COMPLEX_POW_2, csqrt] THEN COND_CASES_TAC THENL
     [COND_CASES_TAC THEN
      ASM_REWRITE_TAC [CX_DEF, complex_mul, RE, IM, REAL_MUL_RZERO, REAL_MUL_LZERO,
        REAL_SUB_LZERO, REAL_SUB_RZERO, REAL_ADD_LID, COMPLEX_EQ] THEN
      REWRITE_TAC [REAL_NEG_EQ, ← GSYM REAL_POW_2] THEN
      ASM_SIMP_TAC [SQRT_POW_2, ← REAL_ARITH (← q r"~(&0 <= x) ==> &0 <= --x")],
      ALL_TAC] THEN
    REWRITE_TAC [complex_mul, RE, IM] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH
     (← q r"(s * s - (i * s') * (i * s') = s * s - (i * i) * (s' * s')) /\
      (s * i * s' + (i * s')* s = &2 * i * s * s')")] THEN
    REWRITE_TAC [← GSYM REAL_POW_2] THEN
    SUBGOAL_THEN (← q r"&0 <= norm(z) + Re(z) /\ &0 <= norm(z) - Re(z)")
    STRIP_ASSUME_TAC THENL
     [MP_TAC (← SPEC (← q r"z:complex") COMPLEX_NORM_GE_RE_IM) THEN REAL_ARITH_TAC,
      ALL_TAC] THEN
    ASM_SIMP_TAC [REAL_LE_DIV, REAL_POS, ← GSYM SQRT_MUL, SQRT_POW_2] THEN
    REWRITE_TAC [COMPLEX_EQ, RE, IM] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [REAL_POW_DIV, REAL_POW2_ABS,
                    REAL_POW_EQ_0, REAL_DIV_REFL] THEN
      REWRITE_TAC [real_div, REAL_MUL_LID, ← GSYM REAL_SUB_RDISTRIB] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"(m + r) - (m - r) = r * &2")] THEN
      REWRITE_TAC [← GSYM REAL_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [REAL_MUL_RID], ALL_TAC] THEN
    REWRITE_TAC [real_div] THEN
    ONCE_REWRITE_TAC [← AC REAL_MUL_AC
      (← q r"(a * b) * a' * b = (a * a') * (b * b:real)")] THEN
    REWRITE_TAC [REAL_DIFFSQ] THEN
    REWRITE_TAC [complex_norm, ← GSYM REAL_POW_2] THEN
    SIMP_TAC [SQRT_POW_2, REAL_LE_ADD,
              ← REWRITE_RULE [← GSYM REAL_POW_2] REAL_LE_SQUARE] THEN
    REWRITE_TAC [REAL_ADD_SUB, ← GSYM REAL_POW_MUL] THEN
    REWRITE_TAC [POW_2_SQRT_ABS] THEN
    REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_INV, REAL_ABS_NUM] THEN
    ONCE_REWRITE_TAC [← AC REAL_MUL_AC
      (← q r"&2 * (i * a') * a * h = i * (&2 * h) * a * a'")] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [REAL_MUL_LID, ← GSYM real_div] THEN
    ASM_SIMP_TAC [REAL_DIV_REFL, REAL_ABS_ZERO, REAL_MUL_RID])

  let CX_SQRT ← prove
   r"!x. &0 <= x ==> Cx(sqrt x) = csqrt(Cx x)"
   (SIMP_TAC [csqrt, IM_CX, RE_CX, COMPLEX_EQ, RE, IM])

  let CSQRT_CX ← prove
   r"!x. &0 <= x ==> csqrt(Cx x) = Cx(sqrt x)"
   (SIMP_TAC [CX_SQRT])

  let CSQRT_0 ← prove
   r"csqrt(Cx(&0)) = Cx(&0)"
   (SIMP_TAC [CSQRT_CX, REAL_POS, SQRT_0])

  let CSQRT_1 ← prove
   r"csqrt(Cx(&1)) = Cx(&1)"
   (SIMP_TAC [CSQRT_CX, REAL_POS, SQRT_1])

  let CSQRT_PRINCIPAL ← prove
   r"!z. &0 < Re(csqrt(z)) \/ Re(csqrt(z)) = &0 /\ &0 <= Im(csqrt(z))"
   (GEN_TAC THEN REWRITE_TAC [csqrt] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [RE, IM]) THENL
     [FIRST_ASSUM (MP_TAC o MATCH_MP SQRT_POS_LE) THEN REAL_ARITH_TAC,
      DISJ2_TAC THEN REWRITE_TAC [real_ge] THEN MATCH_MP_TAC SQRT_POS_LE THEN
      ASM_REAL_ARITH_TAC,
      DISJ1_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"abs(y) < x ==> &0 < (x + y) / &2")) THEN
      REWRITE_TAC [complex_norm] THEN REWRITE_TAC [← GSYM POW_2_SQRT_ABS] THEN
      MATCH_MP_TAC SQRT_MONO_LT THEN
      REWRITE_TAC [REAL_POW_2, REAL_LE_SQUARE, REAL_LT_ADDR] THEN
      REWRITE_TAC [← REAL_ARITH (← q r"&0 < x <=> &0 <= x /\ ~(x = &0)")] THEN
      ASM_REWRITE_TAC [REAL_LE_SQUARE, REAL_ENTIRE]])

  let RE_CSQRT ← prove
   r"!z. &0 <= Re(csqrt z)"
   (MP_TAC CSQRT_PRINCIPAL THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC)

  let CSQRT_UNIQUE ← prove
   r"!s z. s pow 2 = z /\ (&0 < Re s \/ Re s = &0 /\ &0 <= Im s)
           ==> csqrt z = s"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
    MP_TAC (← SPEC (← q r"(s:complex) pow 2") CSQRT) THEN
    SIMP_TAC [← ExceptT.mk (COMPLEX_RING
      (← q r"a pow 2 = b pow 2 <=> a = b \/ a = --b:complex"))] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"--z = z <=> z = Cx(&0)"))] THEN
    FIRST_ASSUM (MP_TAC o AP_TERM (← q r"Re")) THEN
    FIRST_X_ASSUM (MP_TAC o AP_TERM (← q r"Im")) THEN
    REWRITE_TAC [RE_NEG, IM_NEG, COMPLEX_EQ, RE_CX, IM_CX] THEN
    MP_TAC (← SPEC (← q r"(s:complex) pow 2") CSQRT_PRINCIPAL) THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC)

  let POW_2_CSQRT ← prove
   r"!z. &0 < Re z \/ Re(z) = &0 /\ &0 <= Im(z) ==> csqrt(z pow 2) = z"
   (MESON_TAC [CSQRT_UNIQUE])

  let CSQRT_EQ_0 ← prove
   r"!z. csqrt z = Cx(&0) <=> z = Cx(&0)"
   (GEN_TAC THEN MP_TAC (← SPEC (← q r"z:complex") CSQRT) THEN CONV_TAC COMPLEX_RING)

  -- A few more complex-specific cases of vector notions.

  let DOT_COMPLEX_MUL_CNJ ← prove
   r"!w z. w dot z = Re(w * cnj z)"
   (REWRITE_TAC [cnj, complex_mul, RE, IM] THEN
    REWRITE_TAC [DOT_2, RE_DEF, IM_DEF] THEN REAL_ARITH_TAC)

  let DOT_CNJ ← prove
   r"!w z. cnj w dot cnj z = w dot z"
   (REWRITE_TAC [DOT_2, ← GSYM RE_DEF, ← GSYM IM_DEF] THEN
    REWRITE_TAC [cnj, RE, IM] THEN REAL_ARITH_TAC)

  let LINEAR_COMPLEX_MUL ← prove
   r"!c. linear (\x. c * x)"
   (REWRITE_TAC [linear, COMPLEX_CMUL] THEN CONV_TAC COMPLEX_RING)

  let BILINEAR_COMPLEX_MUL ← prove
   r"bilinear( * )"
   (REWRITE_TAC [bilinear, linear, COMPLEX_CMUL] THEN  CONV_TAC COMPLEX_RING)

  let LINEAR_CNJ ← prove
   r"linear cnj"
   (REWRITE_TAC [linear, COMPLEX_CMUL, CNJ_ADD, CNJ_MUL, CNJ_CX])

  let LINEAR_COMPLEX_LMUL ← prove
   r"!f:real^N->complex c. linear f ==> linear (\x. c * f x)"
   (SIMP_TAC [linear, COMPLEX_CMUL] THEN
    REPEAT STRIP_TAC THEN CONV_TAC COMPLEX_RING)

  let LINEAR_COMPLEX_RMUL ← prove
   r"!f:real^N->complex c. linear f ==> linear (\x. f x * c)"
   (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN REWRITE_TAC [LINEAR_COMPLEX_LMUL])

  let COMPLEX_CAUCHY_SCHWARZ_EQ ← prove
   r"!w z. (w dot z) pow 2 + ((ii * w) dot z) pow 2 =
            norm(w) pow 2 * norm(z) pow 2"
   (REWRITE_TAC [NORM_POW_2, DOT_2, ← GSYM RE_DEF, ← GSYM IM_DEF] THEN
    REWRITE_TAC [ii, complex_mul, RE, IM] THEN REAL_ARITH_TAC)

  let COMPLEX_BASIS ← prove
   r"basis 1 = Cx(&1) /\ basis 2 = ii"
   (SIMP_TAC [CART_EQ, FORALL_2, BASIS_COMPONENT, DIMINDEX_2, ARITH] THEN
    REWRITE_TAC [← GSYM RE_DEF, ← GSYM IM_DEF, RE_CX, IM_CX] THEN
    REWRITE_TAC [ii] THEN SIMPLE_COMPLEX_ARITH_TAC)

  let COMPLEX_LINEAR ← prove
   r"!f:complex->complex.
          (?c. f = \z. c * z) <=>
          linear f /\
          (matrix f)$1$1 = (matrix f)$2$2 /\
          (matrix f)$1$2 = --((matrix f)$2$1)"
   (GEN_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC [LINEAR_COMPLEX_MUL] THEN
      SIMP_TAC [matrix, LAMBDA_BETA, DIMINDEX_2, ARITH] THEN
      REWRITE_TAC [COMPLEX_BASIS, ← GSYM RE_DEF, ← GSYM IM_DEF, ii] THEN
      SIMPLE_COMPLEX_ARITH_TAC,
      STRIP_TAC THEN
      EXISTS_TAC (← q r"complex(matrix(f:complex->complex)$1$1,matrix f$2$1)") THEN
      FIRST_ASSUM (fun th => tactic_of do
        pure (GEN_REWRITE_TAC LAND_CONV [← MATCH_MP MATRIX_VECTOR_MUL th])) THEN
      ASM_SIMP_TAC [CART_EQ, matrix_vector_mul, DIMINDEX_2, SUM_2, ARITH,
                    FORALL_2, FUN_EQ_THM, LAMBDA_BETA] THEN
      REWRITE_TAC [← GSYM RE_DEF, ← GSYM IM_DEF, IM, RE, complex_mul] THEN
      REAL_ARITH_TAC])

  let COMPLEX_LINEAR_ALT ← prove
   r"!f:complex->complex.
          (?c. f = \z. c * z) <=> linear f /\ f(ii) = ii * f(Cx(&1))"
   (GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [LINEAR_COMPLEX_MUL] THENL
     [SIMPLE_COMPLEX_ARITH_TAC, ASM_REWRITE_TAC [COMPLEX_LINEAR]] THEN
    FIRST_ASSUM (MP_TAC o SYM) THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
        [← MATCH_MP MATRIX_VECTOR_MUL th])) THEN
    REWRITE_TAC [CART_EQ, FORALL_2, DIMINDEX_2] THEN
    REWRITE_TAC [← GSYM RE_DEF, ← GSYM IM_DEF, RE_MUL_II, IM_MUL_II] THEN
    REWRITE_TAC [MATRIX_VECTOR_MUL_COMPONENT, IM_DEF, RE_DEF] THEN
    SIMP_TAC [MATRIX_VECTOR_MUL_COMPONENT, DIMINDEX_2, ARITH, DOT_2] THEN
    REWRITE_TAC [← GSYM RE_DEF, ← GSYM IM_DEF, CX_DEF, RE, IM, RE_II, IM_II] THEN
    REAL_ARITH_TAC)

  return { csqrt, CSQRT, CX_SQRT, CSQRT_CX, CSQRT_0, CSQRT_1, CSQRT_PRINCIPAL, RE_CSQRT,
           CSQRT_UNIQUE, POW_2_CSQRT, CSQRT_EQ_0, DOT_COMPLEX_MUL_CNJ, DOT_CNJ,
           LINEAR_COMPLEX_MUL, BILINEAR_COMPLEX_MUL, LINEAR_CNJ, LINEAR_COMPLEX_LMUL,
           LINEAR_COMPLEX_RMUL, COMPLEX_CAUCHY_SCHWARZ_EQ, COMPLEX_BASIS,
           COMPLEX_LINEAR, COMPLEX_LINEAR_ALT }

/- ------------------------------------------------------------------------- -/
/- Complex-specific theorems about sums; the complex numbers that are real -/
/- (zero imaginary part).  (complex_algebra.ml 1500-1656)                  -/
/- ------------------------------------------------------------------------- -/

structure CXI where
  RE_VSUM : thm
  IM_VSUM : thm
  VSUM_COMPLEX_LMUL : thm
  VSUM_COMPLEX_RMUL : thm
  VSUM_CX : thm
  CNJ_VSUM : thm
  VSUM_CX_NUMSEG : thm
  COMPLEX_SUB_POW : thm
  COMPLEX_SUB_POW_R1 : thm
  COMPLEX_SUB_POW_L1 : thm
  real : thm
  REAL : thm
  REAL_CNJ : thm
  REAL_IMP_CNJ : thm
  REAL_EXISTS : thm
  FORALL_REAL : thm
  EXISTS_REAL : thm
  REAL_CX : thm
  REAL_MUL_CX : thm
  REAL_ADD : thm
  REAL_NEG : thm
  REAL_SUB : thm
  REAL_MUL : thm
  REAL_POW : thm
  REAL_INV : thm
  REAL_INV_EQ : thm
  REAL_DIV : thm
  REAL_VSUM : thm
  REAL_MUL_CNJ : thm
  IMAGE_CX : thm
  SUBSPACE_REAL : thm
  DIM_REAL : thm
  deriving Inhabited

@[nospecialize]
def setupCXI [HolBase] (D : ComplexAlgebraDeps) (BCXA : CXA) (BCXB : CXB) (BCXC : CXC)
    (BCXD : CXD) (BCXE : CXE) (BCXG : CXG) : ExceptT String IO CXI := do
  -- @@SCOPE BEGIN
  let { new_definition, ARITH_RULE, MESON_TAC, REAL_ARITH_TAC, SET_RULE, .. } := D.cvx
  let { ADD1, ARITH, CART_EQ, DIMINDEX_2, ETA_AX, EXTENSION, FINITE_INDUCT_STRONG,
        FINITE_NUMSEG, .. } := D.cvx.core1
  let { IN, .. } := D.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, .. } := D.cvx.core3
  let { REAL_ENTIRE, .. } := D.cvx.core4
  let { SUM_0, .. } := D.cvx.core6
  let { DIM_SPECIAL_HYPERPLANE, .. } := D.cvx.vec1
  let { VSUM_CLAUSES, subspace, .. } := D.cvx.vec4
  let { LE_0, SUB_0, SUB_ADD, SUB_REFL, FORALL_2, VSUM_COMPONENT, VSUM_DIFFS_ALT,
        .. } := D.cpx
  let { RE_DEF, IM_DEF, CX_DEF, complex_pow, RE, IM, COMPLEX_EQ, SIMPLE_COMPLEX_ARITH_TAC,
        .. } := BCXA
  let { COMPLEX_MUL_SYM, COMPLEX_MUL_LID, COMPLEX_MUL_RID, COMPLEX_MUL_RZERO,
        COMPLEX_MUL_LNEG, COMPLEX_NEG_SUB, .. } := BCXB
  let { COMPLEX_VEC_0, COMPLEX_CMUL, COMPLEX_POW_ONE, CX_POW, RE_CX, IM_CX, IM_MUL_CX,
        .. } := BCXC
  let { COMPLEX_RING, .. } := BCXD
  let { COMPLEX_INV_INV, .. } := BCXE
  let { cnj, CNJ_CX, CNJ_NEG, CNJ_INV, CNJ_ADD, CNJ_SUB, CNJ_MUL, CNJ_DIV, CNJ_POW,
        COMPLEX_MUL_CNJ, .. } := BCXG
  -- @@SCOPE END

  -- Complex-specific theorems about sums.

  let RE_VSUM ← prove
   r"!f s. FINITE s ==> Re(vsum s f) = sum s (\x. Re(f x))"
   (SIMP_TAC [RE_DEF, VSUM_COMPONENT, DIMINDEX_2, ARITH])

  let IM_VSUM ← prove
   r"!f s. FINITE s ==> Im(vsum s f) = sum s (\x. Im(f x))"
   (SIMP_TAC [IM_DEF, VSUM_COMPONENT, DIMINDEX_2, ARITH])

  let VSUM_COMPLEX_LMUL ← prove
   r"!c f s. FINITE(s) ==> vsum s (\x. c * f x) = c * vsum s f"
   (GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [VSUM_CLAUSES, COMPLEX_VEC_0, COMPLEX_MUL_RZERO] THEN
    SIMPLE_COMPLEX_ARITH_TAC)

  let VSUM_COMPLEX_RMUL ← prove
   r"!c f s. FINITE(s) ==> vsum s (\x. f x * c) = vsum s f * c"
   (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM] THEN REWRITE_TAC [VSUM_COMPLEX_LMUL])

  let VSUM_CX ← prove
   r"!f:A->real s. vsum s (\a. Cx(f a)) = Cx(sum s f)"
   (SIMP_TAC [CART_EQ, VSUM_COMPONENT] THEN
    REWRITE_TAC [DIMINDEX_2, FORALL_2, ← GSYM RE_DEF, ← GSYM IM_DEF] THEN
    REWRITE_TAC [IM_CX, SUM_0, RE_CX, ETA_AX])

  let CNJ_VSUM ← prove
   r"!f s. FINITE s ==> cnj(vsum s f) = vsum s (\x. cnj(f x))"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [VSUM_CLAUSES, CNJ_ADD, CNJ_CX, COMPLEX_VEC_0])

  let VSUM_CX_NUMSEG ← prove
   r"!f m n. vsum (m..n) (\a. Cx(f a)) = Cx(sum (m..n) f)"
   (SIMP_TAC [VSUM_CX, FINITE_NUMSEG])

  let COMPLEX_SUB_POW ← prove
   r"!x y n.
          1 <= n ==> x pow n - y pow n =
                     (x - y) * vsum(0..n-1) (\i. x pow i * y pow (n - 1 - i))"
   (SIMP_TAC [← GSYM VSUM_COMPLEX_LMUL, FINITE_NUMSEG] THEN
    REWRITE_TAC [← ExceptT.mk (COMPLEX_RING
     (← q r"(x - y) * (a * b):complex = (x * a) * b - a * (y * b)"))] THEN
    SIMP_TAC [← GSYM complex_pow, ADD1, ← ARITH_RULE
      (← q r"1 <= n /\ x <= n - 1
       ==> n - 1 - x = n - (x + 1) /\ SUC(n - 1 - x) = n - x")] THEN
    REWRITE_TAC [VSUM_DIFFS_ALT, LE_0] THEN
    SIMP_TAC [SUB_0, SUB_ADD, SUB_REFL,
              complex_pow, COMPLEX_MUL_LID, COMPLEX_MUL_RID])

  let COMPLEX_SUB_POW_R1 ← prove
   r"!x n. 1 <= n
           ==> x pow n - Cx(&1) = (x - Cx(&1)) * vsum(0..n-1) (\i. x pow i)"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o SPECL [← q r"x:complex", ← q r"Cx(&1)"] o
      MATCH_MP COMPLEX_SUB_POW) THEN
    REWRITE_TAC [COMPLEX_POW_ONE, COMPLEX_MUL_RID])

  let COMPLEX_SUB_POW_L1 ← prove
   r"!x n. 1 <= n
           ==> Cx(&1) - x pow n = (Cx(&1) - x) * vsum(0..n-1) (\i. x pow i)"
   (ONCE_REWRITE_TAC [← GSYM COMPLEX_NEG_SUB] THEN
    SIMP_TAC [COMPLEX_SUB_POW_R1] THEN REWRITE_TAC [COMPLEX_MUL_LNEG])

  -- The complex numbers that are real (zero imaginary part).

  let real ← new_definition
   r"real z <=> Im z = &0"

  let REAL ← prove
   r"!z. real z <=> Cx(Re z) = z"
   (REWRITE_TAC [COMPLEX_EQ, real, CX_DEF, RE, IM] THEN REAL_ARITH_TAC)

  let REAL_CNJ ← prove
   r"!z. real z <=> cnj z = z"
   (REWRITE_TAC [real, cnj, COMPLEX_EQ, RE, IM] THEN REAL_ARITH_TAC)

  let REAL_IMP_CNJ ← prove
   r"!z. real z ==> cnj z = z"
   (REWRITE_TAC [REAL_CNJ])

  let REAL_EXISTS ← prove
   r"!z. real z <=> ?x. z = Cx x"
   (MESON_TAC [REAL, real, IM_CX])

  let FORALL_REAL ← prove
   r"(!z. real z ==> P z) <=> (!x. P(Cx x))"
   (MESON_TAC [REAL_EXISTS])

  let EXISTS_REAL ← prove
   r"(?z. real z /\ P z) <=> (?x. P(Cx x))"
   (MESON_TAC [REAL_EXISTS])

  let REAL_CX ← prove
   r"!x. real(Cx x)"
   (REWRITE_TAC [REAL_CNJ, CNJ_CX])

  let REAL_MUL_CX ← prove
   r"!x z. real(Cx x * z) <=> x = &0 \/ real z"
   (REWRITE_TAC [real, IM_MUL_CX, REAL_ENTIRE])

  let REAL_ADD ← prove
   r"!w z. real w /\ real z ==> real(w + z)"
   (SIMP_TAC [REAL_CNJ, CNJ_ADD])

  let REAL_NEG ← prove
   r"!z. real z ==> real(--z)"
   (SIMP_TAC [REAL_CNJ, CNJ_NEG])

  let REAL_SUB ← prove
   r"!w z. real w /\ real z ==> real(w - z)"
   (SIMP_TAC [REAL_CNJ, CNJ_SUB])

  let REAL_MUL ← prove
   r"!w z. real w /\ real z ==> real(w * z)"
   (SIMP_TAC [REAL_CNJ, CNJ_MUL])

  let REAL_POW ← prove
   r"!z n. real z ==> real(z pow n)"
   (SIMP_TAC [REAL_CNJ, CNJ_POW])

  let REAL_INV ← prove
   r"!z. real z ==> real(inv z)"
   (SIMP_TAC [REAL_CNJ, CNJ_INV])

  let REAL_INV_EQ ← prove
   r"!z. real(inv z) = real z"
   (MESON_TAC [REAL_INV, COMPLEX_INV_INV])

  let REAL_DIV ← prove
   r"!w z. real w /\ real z ==> real(w / z)"
   (SIMP_TAC [REAL_CNJ, CNJ_DIV])

  let REAL_VSUM ← prove
   r"!f s. FINITE s /\ (!a. a IN s ==> real(f a)) ==> real(vsum s f)"
   (SIMP_TAC [CNJ_VSUM, REAL_CNJ])

  let REAL_MUL_CNJ ← prove
   r"(!z. real(z * cnj z)) /\ (!z. real(cnj z * z))"
   (REWRITE_TAC [COMPLEX_MUL_CNJ, ← GSYM CX_POW, REAL_CX])

  let IMAGE_CX ← prove
   r"!s. IMAGE Cx s = {z | real z /\ Re(z) IN s}"
   (REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_IMAGE] THEN MESON_TAC [RE_CX, REAL])

  let SUBSPACE_REAL ← prove
   r"subspace real"
   (REWRITE_TAC [subspace] THEN
    SIMP_TAC [COMPLEX_CMUL, COMPLEX_VEC_0, IN, REAL_CX, REAL_ADD, REAL_MUL])

  let DIM_REAL ← prove
   r"dim real = 1"
   (ONCE_REWRITE_TAC [← SET_RULE (← q r"real = {x | real x}")] THEN
    SIMP_TAC [real, IM_DEF, DIM_SPECIAL_HYPERPLANE, DIMINDEX_2, ARITH])

  return { RE_VSUM, IM_VSUM, VSUM_COMPLEX_LMUL, VSUM_COMPLEX_RMUL, VSUM_CX, CNJ_VSUM,
           VSUM_CX_NUMSEG, COMPLEX_SUB_POW, COMPLEX_SUB_POW_R1, COMPLEX_SUB_POW_L1, real, REAL,
           REAL_CNJ, REAL_IMP_CNJ, REAL_EXISTS, FORALL_REAL, EXISTS_REAL, REAL_CX, REAL_MUL_CX,
           REAL_ADD, REAL_NEG, REAL_SUB, REAL_MUL, REAL_POW, REAL_INV, REAL_INV_EQ, REAL_DIV,
           REAL_VSUM, REAL_MUL_CNJ, IMAGE_CX, SUBSPACE_REAL, DIM_REAL }

/- ------------------------------------------------------------------------- -/
/- Useful bound-type theorems for real quantities; geometric progression;  -/
/- basics about polynomial functions: extremal behaviour and root counts.  -/
/- (complex_algebra.ml 1658-1924)                                          -/
/- ------------------------------------------------------------------------- -/

structure CXJ where
  REAL_NORM : thm
  REAL_NORM_POS : thm
  COMPLEX_NORM_VSUM_SUM_RE : thm
  COMPLEX_NORM_VSUM_BOUND : thm
  COMPLEX_NORM_VSUM_BOUND_SUBSET : thm
  VSUM_GP_BASIC : thm
  VSUM_GP_MULTIPLIED : thm
  VSUM_GP : thm
  VSUM_GP_OFFSET : thm
  COMPLEX_SUB_POLYFUN : thm
  COMPLEX_SUB_POLYFUN_ALT : thm
  COMPLEX_POLYFUN_LINEAR_FACTOR : thm
  COMPLEX_POLYFUN_LINEAR_FACTOR_ROOT : thm
  COMPLEX_POLYFUN_EXTREMAL_LEMMA : thm
  COMPLEX_POLYFUN_ROOTBOUND : thm
  COMPLEX_POLYFUN_FINITE_ROOTS : thm
  COMPLEX_POLYFUN_EQ_0 : thm
  COMPLEX_POLYFUN_EQ_CONST : thm
  deriving Inhabited

@[nospecialize]
def setupCXJ [HolBase] (D : ComplexAlgebraDeps) (BCXA : CXA) (BCXB : CXB) (BCXC : CXC)
    (BCXD : CXD) (BCXE : CXE) (BCXF : CXF) (BCXI : CXI) : ExceptT String IO CXJ := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON, MESON_TAC,
        REAL_ARITH, REAL_ARITH_TAC, SET_RULE, REAL_RAT_REDUCE_CONV, NORM_ARITH,
        .. } := D.cvx
  let { ADD1, ADD_SYM, ARITH, CARD_CLAUSES, CONTRAPOS_THM, DE_MORGAN_THM, EMPTY_GSPEC,
        EQ_TRANS, FINITE_INSERT, FINITE_NUMSEG, FINITE_RULES, FINITE_SUBSET, FORALL_IN_GSPEC,
        .. } := D.cvx.core1
  let { IN_DIFF, IN_ELIM_PAIR_THM, .. } := D.cvx.core2
  let { IN_ELIM_THM, IN_NUMSEG, IN_SING, LE, LE_1, LE_REFL, MEMBER_NOT_EMPTY, MONO_OR, NOT_FORALL_THM,
        NUMSEG_SING, REAL_ADD_RDISTRIB, REAL_ADD_RID, .. } := D.cvx.core3
  let { REAL_LE_LDIV_EQ, REAL_LE_RMUL, REAL_LE_TRANS, REAL_MAX_LE, .. } := D.cvx.core4
  let { REAL_MUL_AC, REAL_MUL_ASSOC, REAL_MUL_SYM, REAL_OF_NUM_ADD, REAL_POW_LE, SUBSET,
        .. } := D.cvx.core5
  let { SUM_LE, SUM_POS_LE, .. } := D.cvx.core6
  let { NORM_POS_LE, .. } := D.cvx.vec3
  let { VSUM_0, VSUM_CLAUSES_NUMSEG, VSUM_EQ, VSUM_SING, .. } := D.cvx.vec4
  let { ADD_CLAUSES, INFINITE, LE_0, POW_2_SQRT_ABS, REAL_POW_1, REAL_POW_ADD, SUB_REFL, SUC_SUB1,
        SUM_SUBSET, EUCLIDEAN_SPACE_INFINITE, VSUM_CLAUSES_LEFT, VSUM_CONST_NUMSEG,
        VSUM_EQ_GENERAL_INVERSES, VSUM_EQ_NUMSEG, VSUM_NORM, VSUM_OFFSET_0,
        VSUM_SUB_NUMSEG, VSUM_TRIV_NUMSEG, VSUM_VSUM_PRODUCT, .. } := D.cpx
  let { complex_div, complex_pow, complex_norm, SIMPLE_COMPLEX_ARITH_TAC, .. } := BCXA
  let { COMPLEX_ADD_LID, COMPLEX_MUL_ASSOC, COMPLEX_MUL_LID, COMPLEX_ADD_LDISTRIB,
        COMPLEX_MUL_AC, COMPLEX_ADD_RID, COMPLEX_MUL_RID, COMPLEX_MUL_RZERO,
        COMPLEX_MUL_LZERO, COMPLEX_SUB_REFL, COMPLEX_SUB_0, COMPLEX_EQ_SUB_RADD,
        COMPLEX_SUB_LDISTRIB, COMPLEX_SUB_RDISTRIB, COMPLEX_SUB_RZERO, .. } := BCXB
  let { COMPLEX_ENTIRE, COMPLEX_VEC_0, COMPLEX_CMUL, COMPLEX_POW_ADD, COMPLEX_POW_ONE,
        CX_ADD, .. } := BCXC
  let { COMPLEX_RING, .. } := BCXD
  let { COMPLEX_FIELD, .. } := BCXE
  let { COMPLEX_DIV_LMUL, COMPLEX_NORM_MUL, COMPLEX_NORM_POW, .. } := BCXF
  let { RE_VSUM, VSUM_COMPLEX_LMUL, VSUM_COMPLEX_RMUL, COMPLEX_SUB_POW, real, REAL_VSUM,
        .. } := BCXI
  -- @@SCOPE END

  -- Useful bound-type theorems for real quantities.

  let REAL_NORM ← prove
   r"!z. real z ==> norm(z) = abs(Re z)"
   (SIMP_TAC [real, complex_norm] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [POW_2_SQRT_ABS, REAL_ADD_RID])

  let REAL_NORM_POS ← prove
   r"!z. real z /\ &0 <= Re z ==> norm(z) = Re(z)"
   (SIMP_TAC [REAL_NORM] THEN REAL_ARITH_TAC)

  let COMPLEX_NORM_VSUM_SUM_RE ← prove
   r"!f s. FINITE s /\ (!x. x IN s ==> real(f x) /\ &0 <= Re(f x))
           ==> norm(vsum s f) = sum s (\x. Re(f x))"
   (SIMP_TAC [← GSYM RE_VSUM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_NORM_POS THEN
    ASM_SIMP_TAC [REAL_VSUM, RE_VSUM, SUM_POS_LE])

  let COMPLEX_NORM_VSUM_BOUND ← prove
   r"!s f:A->complex g:A->complex.
          FINITE s /\ (!x. x IN s ==> real(g x) /\ norm(f x) <= Re(g x))
          ==> norm(vsum s f) <= norm(vsum s g)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"sum s (\x. norm((f:A->complex) x))") THEN
    ASM_SIMP_TAC [VSUM_NORM] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"sum s (\x. Re((g:A->complex) x))") THEN
    ASM_SIMP_TAC [SUM_LE] THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"x:real = y ==> y <= x")) THEN
    MATCH_MP_TAC COMPLEX_NORM_VSUM_SUM_RE THEN
    ASM_MESON_TAC [REAL_LE_TRANS, NORM_POS_LE])

  let COMPLEX_NORM_VSUM_BOUND_SUBSET ← prove
   r"!f:A->complex g:A->complex s t.
          FINITE s /\ t SUBSET s /\
          (!x. x IN s ==> real(g x) /\ norm(f x) <= Re(g x))
          ==> norm(vsum t f) <= norm(vsum s g)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"norm(vsum t (g:A->complex))") THEN CONJ_TAC THENL
     [ASM_MESON_TAC [COMPLEX_NORM_VSUM_BOUND, SUBSET, FINITE_SUBSET], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"norm(vsum t (g:A->complex)) = sum t (\x. Re(g x)) /\
      norm(vsum s g) = sum s (\x. Re(g x))")
     (CONJUNCTS_THEN SUBST1_TAC)
    THENL
     [CONJ_TAC THEN MATCH_MP_TAC COMPLEX_NORM_VSUM_SUM_RE,
      MATCH_MP_TAC SUM_SUBSET THEN REWRITE_TAC [IN_DIFF]] THEN
    ASM_MESON_TAC [REAL_LE_TRANS, NORM_POS_LE, FINITE_SUBSET, SUBSET])

  -- Geometric progression.

  let VSUM_GP_BASIC ← prove
   r"!x n. (Cx(&1) - x) * vsum(0..n) (\i. x pow i) = Cx(&1) - x pow (SUC n)"
   (GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC [complex_pow, COMPLEX_MUL_RID, LE_0] THEN
    ASM_REWRITE_TAC [COMPLEX_ADD_LDISTRIB, complex_pow] THEN
    SIMPLE_COMPLEX_ARITH_TAC)

  let VSUM_GP_MULTIPLIED ← prove
   r"!x m n. m <= n
             ==> ((Cx(&1) - x) * vsum(m..n) (\i. x pow i) =
                  x pow m - x pow (SUC n))"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [VSUM_OFFSET_0, COMPLEX_POW_ADD, FINITE_NUMSEG,
                  COMPLEX_MUL_ASSOC, VSUM_GP_BASIC, VSUM_COMPLEX_RMUL] THEN
    REWRITE_TAC [COMPLEX_SUB_RDISTRIB, ← GSYM COMPLEX_POW_ADD, COMPLEX_MUL_LID] THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"m <= n ==> (SUC(n - m) + m = SUC n)")])

  let VSUM_GP ← prove
   r"!x m n.
          vsum(m..n) (\i. x pow i) =
                  if n < m then Cx(&0)
                  else if x = Cx(&1) then Cx(&((n + 1) - m))
                  else (x pow m - x pow (SUC n)) / (Cx(&1) - x)"
   (REPEAT GEN_TAC THEN
    DISJ_CASES_TAC (← ARITH_RULE (← q r"n < m \/ ~(n < m) /\ m <= n:num")) THEN
    ASM_SIMP_TAC [VSUM_TRIV_NUMSEG, COMPLEX_VEC_0] THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC [COMPLEX_POW_ONE, VSUM_CONST_NUMSEG, COMPLEX_MUL_RID],
      ALL_TAC] THEN
    REWRITE_TAC [COMPLEX_CMUL, COMPLEX_MUL_RID] THEN
    MATCH_MP_TAC (← ExceptT.mk (COMPLEX_FIELD
     (← q r"~(z = Cx(&1)) /\ (Cx(&1) - z) * x = y ==> x = y / (Cx(&1) - z)"))) THEN
    ASM_SIMP_TAC [COMPLEX_DIV_LMUL, COMPLEX_SUB_0, VSUM_GP_MULTIPLIED])

  let VSUM_GP_OFFSET ← prove
   r"!x m n. vsum(m..m+n) (\i. x pow i) =
                  if x = Cx(&1) then Cx(&n) + Cx(&1)
                  else x pow m * (Cx(&1) - x pow (SUC n)) / (Cx(&1) - x)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [VSUM_GP, ← ARITH_RULE (← q r"~(m + n < m:num)")] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
     [REWRITE_TAC [REAL_OF_NUM_ADD, ← GSYM CX_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC,
      REWRITE_TAC [complex_div, complex_pow, COMPLEX_POW_ADD] THEN
      SIMPLE_COMPLEX_ARITH_TAC])

  -- Basics about polynomial functions: extremal behaviour and root counts.

  let COMPLEX_SUB_POLYFUN ← prove
   r"!a x y n.
     1 <= n
     ==> vsum(0..n) (\i. a i * x pow i) - vsum(0..n) (\i. a i * y pow i) =
         (x - y) *
         vsum(0..n-1) (\j. vsum(j+1..n) (\i. a i * y pow (i - j - 1)) * x pow j)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [← GSYM VSUM_SUB_NUMSEG, ← GSYM COMPLEX_SUB_LDISTRIB] THEN
    GEN_REWRITE_TAC LAND_CONV [← MATCH_MP VSUM_CLAUSES_LEFT (← SPEC_ALL LE_0)] THEN
    REWRITE_TAC [COMPLEX_SUB_REFL, complex_pow, COMPLEX_MUL_RZERO,
        COMPLEX_ADD_LID] THEN
    SIMP_TAC [COMPLEX_SUB_POW, ADD_CLAUSES] THEN
    ONCE_REWRITE_TAC [← ExceptT.mk (COMPLEX_RING (← q r"a * x * s:complex = x * a * s"))] THEN
    SIMP_TAC [VSUM_COMPLEX_LMUL, FINITE_NUMSEG] THEN AP_TERM_TAC THEN
    SIMP_TAC [← GSYM VSUM_COMPLEX_LMUL, ← GSYM VSUM_COMPLEX_RMUL, FINITE_NUMSEG,
              VSUM_VSUM_PRODUCT, FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ_GENERAL_INVERSES THEN
    REPEAT (EXISTS_TAC (← q r"\(x:num,y:num). (y,x)")) THEN
    REWRITE_TAC [FORALL_IN_GSPEC, IN_ELIM_PAIR_THM, IN_NUMSEG] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"a - b - c:num = a - (b + c)"), ADD_SYM] THEN
    REWRITE_TAC [COMPLEX_MUL_AC] THEN ARITH_TAC)

  let COMPLEX_SUB_POLYFUN_ALT ← prove
   r"!a x y n.
      1 <= n
      ==> vsum(0..n) (\i. a i * x pow i) - vsum(0..n) (\i. a i * y pow i) =
          (x - y) *
          vsum(0..n-1) (\j. vsum(0..n-j-1) (\k. a(j+k+1) * y pow k) * x pow j)"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [COMPLEX_SUB_POLYFUN] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC (← q r"j:num") THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC VSUM_EQ_GENERAL_INVERSES THEN
    MAP_EVERY EXISTS_TAC
     [← q r"\i. i - (j + 1)", ← q r"\k. j + k + 1"] THEN
    REWRITE_TAC [IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    TRY (BINOP_TAC THEN AP_TERM_TAC) THEN ASM_ARITH_TAC)

  let COMPLEX_POLYFUN_LINEAR_FACTOR ← prove
   r"!a c n. ?b. !z. vsum(0..n) (\i. c(i) * z pow i) =
                     (z - a) * vsum(0..n-1) (\i. b(i) * z pow i) +
                      vsum(0..n) (\i. c(i) * a pow i)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM COMPLEX_EQ_SUB_RADD] THEN
    ASM_CASES_TAC (← q r"n = 0") THENL
     [EXISTS_TAC (← q r"\i:num. Cx(&0)") THEN
      ASM_SIMP_TAC [VSUM_SING, NUMSEG_SING, complex_pow, COMPLEX_MUL_LZERO] THEN
      REWRITE_TAC [COMPLEX_SUB_REFL, ← GSYM COMPLEX_VEC_0, VSUM_0] THEN
      REWRITE_TAC [COMPLEX_VEC_0, COMPLEX_MUL_RZERO],
      ASM_SIMP_TAC [COMPLEX_SUB_POLYFUN, LE_1] THEN
      EXISTS_TAC (← q r"\j. vsum (j + 1..n) (\i. c i * a pow (i - j - 1))") THEN
      REWRITE_TAC []])

  let COMPLEX_POLYFUN_LINEAR_FACTOR_ROOT ← prove
   r"!a c n. vsum(0..n) (\i. c(i) * a pow i) = Cx(&0)
             ==> ?b. !z. vsum(0..n) (\i. c(i) * z pow i) =
                        (z - a) * vsum(0..n-1) (\i. b(i) * z pow i)"
   (MESON_TAC [COMPLEX_POLYFUN_LINEAR_FACTOR, COMPLEX_ADD_RID])

  let COMPLEX_POLYFUN_EXTREMAL_LEMMA ← prove
   r"!c n e. &0 < e
             ==> ?M. !z. M <= norm(z)
                         ==> norm(vsum(0..n) (\i. c(i) * z pow i))
                                 <= e * norm(z) pow (n + 1)"
   (GEN_TAC THEN INDUCT_TAC THEN SIMP_TAC [VSUM_CLAUSES_NUMSEG, LE_0] THEN
    REPEAT STRIP_TAC THENL
     [REWRITE_TAC [ADD_CLAUSES, complex_pow, REAL_POW_1, COMPLEX_MUL_RID] THEN
      EXISTS_TAC (← q r"norm(c 0:complex) / e") THEN ASM_SIMP_TAC [REAL_LE_LDIV_EQ] THEN
      REWRITE_TAC [REAL_MUL_AC],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o C MATCH_MP (← REAL_ARITH (← q r"&0 < &1 / &2"))) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"M:real")) THEN
    EXISTS_TAC (← q r"max M ((&1 / &2 + norm(c(n+1):complex)) / e)") THEN
    X_GEN_TAC (← q r"z:complex") THEN REWRITE_TAC [REAL_MAX_LE] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"z:complex")) THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← NORM_ARITH
     (← q r"a + norm(y) <= b ==> norm(x) <= a ==> norm(x + y) <= b")) THEN
    SIMP_TAC [ADD1, COMPLEX_NORM_MUL, COMPLEX_NORM_POW,
              ← GSYM REAL_ADD_RDISTRIB, ← ARITH_RULE (← q r"(n + 1) + 1 = 1 + n + 1")] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_POW_ADD] THEN
    REWRITE_TAC [REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    ASM_SIMP_TAC [← GSYM REAL_LE_LDIV_EQ, REAL_POW_LE, NORM_POS_LE, REAL_POW_1])

  let COMPLEX_POLYFUN_ROOTBOUND ← prove
   r"!n c. ~(!i. i IN 0..n ==> c(i) = Cx(&0))
           ==> FINITE {z | vsum(0..n) (\i. c(i) * z pow i) = Cx(&0)} /\
               CARD {z | vsum(0..n) (\i. c(i) * z pow i) = Cx(&0)} <= n"
   (← do
    let a5 ← ARITH_RULE (← q r"SUC n - n - 1 = 0")
    let t4 ← TAUT (← q r"~p /\ (q ==> r) ==> p \/ q ==> r")
    let s3 ← SET_RULE (← q r"{z:complex | z = a \/ P z} = a INSERT {z | P z}")
    let a2 ← ARITH_RULE (← q r"1 <= SUC n")
    let t1 ← TAUT (← q r"~a ==> b <=> a \/ b")
    pure (REWRITE_TAC [t1] THEN INDUCT_TAC THEN GEN_TAC THENL
     [SIMP_TAC [NUMSEG_SING, VSUM_SING, IN_SING, complex_pow] THEN
      ASM_CASES_TAC (← q r"c 0 = Cx(&0)") THEN ASM_REWRITE_TAC [COMPLEX_MUL_RID] THEN
      REWRITE_TAC [EMPTY_GSPEC, FINITE_RULES, CARD_CLAUSES, LE_REFL],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"c(SUC n) = Cx(&0)") THENL
     [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"c:num->complex")) THEN
      ASM_REWRITE_TAC [VSUM_CLAUSES_NUMSEG, LE_0, COMPLEX_MUL_LZERO,
                       COMPLEX_ADD_RID] THEN
      MATCH_MP_TAC MONO_OR THEN CONJ_TAC THENL
       [REWRITE_TAC [IN_NUMSEG, LE_0, LE] THEN ASM_MESON_TAC [],
        SIMP_TAC [] THEN ARITH_TAC],
      DISJ2_TAC] THEN
    ASM_CASES_TAC (← q r"{z | vsum(0..SUC n) (\i. c(i) * z pow i) = Cx(&0)} = {}") THEN
    ASM_REWRITE_TAC [FINITE_RULES, CARD_CLAUSES, LE_0] THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"a:complex") MP_TAC o
      GEN_REWRITE_RULE id [← GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN
    ABBREV_TAC (← q r"b = \j. vsum(j+1..SUC n) (\i. c i * a pow (i - j - 1))") THEN
    SUBGOAL_THEN (← q r"!z. vsum(0..SUC n) (\i. c(i) * z pow i) =
                    (z - a) * vsum(0..n) (\j. b j * z pow j)")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"z:complex") THEN
      MP_TAC (← SPECL [← q r"c:num->complex", ← q r"z:complex", ← q r"a:complex", ← q r"SUC n"]
        COMPLEX_SUB_POLYFUN) THEN
      ASM_REWRITE_TAC [a2, SUC_SUB1, COMPLEX_SUB_RZERO] THEN
      DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "b" THEN REWRITE_TAC [],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [COMPLEX_ENTIRE, COMPLEX_SUB_0] THEN
    REWRITE_TAC [s3] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"b:num->complex")) THEN
    MATCH_MP_TAC t4 THEN CONJ_TAC THENL
     [DISCH_THEN (MP_TAC o SPEC (← q r"n:num")) THEN
      REWRITE_TAC [IN_NUMSEG, LE_0, LE_REFL] THEN EXPAND_TAC "b" THEN
      REWRITE_TAC [← GSYM ADD1, NUMSEG_SING, VSUM_SING, SUB_REFL, complex_pow,
                   a5] THEN
      ASM_REWRITE_TAC [COMPLEX_MUL_RID],
      SIMP_TAC [CARD_CLAUSES, FINITE_INSERT] THEN ARITH_TAC]))

  let COMPLEX_POLYFUN_FINITE_ROOTS ← prove
   r"!n c. FINITE {x | vsum(0..n) (\i. c i * x pow i) = Cx(&0)} <=>
           ?i. i IN 0..n /\ ~(c i = Cx(&0))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← TAUT (← q r"a /\ ~b <=> ~(a ==> b)")] THEN
    REWRITE_TAC [← GSYM NOT_FORALL_THM] THEN EQ_TAC THEN
    SIMP_TAC [COMPLEX_POLYFUN_ROOTBOUND] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    SIMP_TAC [COMPLEX_MUL_LZERO] THEN SIMP_TAC [← GSYM COMPLEX_VEC_0, VSUM_0] THEN
    REWRITE_TAC [← SET_RULE (← q r"{x | T} = (:complex)"), ← GSYM INFINITE,
                 EUCLIDEAN_SPACE_INFINITE])

  let COMPLEX_POLYFUN_EQ_0 ← prove
   r"!n c. (!z. vsum(0..n) (\i. c i * z pow i) = Cx(&0)) <=>
           (!i. i IN 0..n ==> c i = Cx(&0))"
   (REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [GEN_REWRITE_TAC id [← TAUT (← q r"p <=> ~ ~p")] THEN DISCH_THEN (MP_TAC o MATCH_MP
       COMPLEX_POLYFUN_ROOTBOUND) THEN
      ASM_REWRITE_TAC [EUCLIDEAN_SPACE_INFINITE, ← GSYM INFINITE, DE_MORGAN_THM,
                       ← SET_RULE (← q r"{x | T} = (:complex)")],
      ASM_SIMP_TAC [IN_NUMSEG, LE_0, COMPLEX_MUL_LZERO] THEN
      REWRITE_TAC [← GSYM COMPLEX_VEC_0, VSUM_0]])

  let COMPLEX_POLYFUN_EQ_CONST ← prove
   r"!n c k. (!z. vsum(0..n) (\i. c i * z pow i) = k) <=>
             c 0 = k /\ (!i. i IN 1..n ==> c i = Cx(&0))"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     (← q r"!x. vsum(0..n) (\i. (if i = 0 then c 0 - k else c i) * x pow i) =
          Cx(&0)") THEN
    CONJ_TAC THENL
     [SIMP_TAC [VSUM_CLAUSES_LEFT, LE_0, complex_pow, COMPLEX_MUL_RID] THEN
      REWRITE_TAC [← ExceptT.mk (COMPLEX_RING
        (← q r"(c - k) + s = Cx(&0) <=> c + s = k"))] THEN
      AP_TERM_TAC THEN ABS_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN GEN_TAC THEN
      REWRITE_TAC [IN_NUMSEG] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [ARITH],
      REWRITE_TAC [COMPLEX_POLYFUN_EQ_0, IN_NUMSEG, LE_0] THEN
      GEN_REWRITE_TAC LAND_CONV [← MESON []
       (← q r"(!n. P n) <=> P 0 /\ (!n. ~(n = 0) ==> P n)")] THEN
      SIMP_TAC [LE_0, COMPLEX_SUB_0] THEN MESON_TAC [LE_1]])

  return { REAL_NORM, REAL_NORM_POS, COMPLEX_NORM_VSUM_SUM_RE, COMPLEX_NORM_VSUM_BOUND,
           COMPLEX_NORM_VSUM_BOUND_SUBSET, VSUM_GP_BASIC, VSUM_GP_MULTIPLIED, VSUM_GP,
           VSUM_GP_OFFSET, COMPLEX_SUB_POLYFUN, COMPLEX_SUB_POLYFUN_ALT,
           COMPLEX_POLYFUN_LINEAR_FACTOR, COMPLEX_POLYFUN_LINEAR_FACTOR_ROOT,
           COMPLEX_POLYFUN_EXTREMAL_LEMMA, COMPLEX_POLYFUN_ROOTBOUND,
           COMPLEX_POLYFUN_FINITE_ROOTS, COMPLEX_POLYFUN_EQ_0, COMPLEX_POLYFUN_EQ_CONST }

/- ------------------------------------------------------------------------- -/
/- Complex products.  (complex_algebra.ml 1926-2084)                       -/
/- ------------------------------------------------------------------------- -/

structure CXK where
  cproduct : thm
  NEUTRAL_COMPLEX_MUL : thm
  MONOIDAL_COMPLEX_MUL : thm
  CPRODUCT_CLAUSES : thm
  CPRODUCT_EQ_0 : thm
  CPRODUCT_INV : thm
  CPRODUCT_MUL : thm
  CPRODUCT_EQ_1 : thm
  CPRODUCT_1 : thm
  CPRODUCT_POW : thm
  NORM_CPRODUCT : thm
  CPRODUCT_EQ : thm
  CPRODUCT_SING : thm
  CPRODUCT_CLAUSES_NUMSEG : thm
  CPRODUCT_CLAUSES_RIGHT : thm
  CPRODUCT_CLAUSES_LEFT : thm
  CPRODUCT_IMAGE : thm
  CPRODUCT_OFFSET : thm
  CPRODUCT_CONST : thm
  CPRODUCT_CONST_NUMSEG : thm
  CPRODUCT_PAIR : thm
  CPRODUCT_REFLECT : thm
  CNJ_CPRODUCT : thm
  CX_PRODUCT : thm
  CPRODUCT_SUPERSET : thm
  CPRODUCT_UNION : thm
  deriving Inhabited

@[nospecialize]
def setupCXK [HolBase] (D : ComplexAlgebraDeps) (BCXA : CXA) (BCXB : CXB) (BCXC : CXC)
    (BCXE : CXE) (BCXF : CXF) (BCXG : CXG) : ExceptT String IO CXK := do
  -- @@SCOPE BEGIN
  let { new_definition, ARITH_RULE, ARITH_TAC, INDUCT_TAC, MESON_TAC, .. } := D.cvx
  let { extend_basic_congs, .. } := D
  let { ARITH, CARD_CLAUSES, CARD_NUMSEG, FINITE_INDUCT_STRONG, FINITE_NUMSEG,
        FINITE_RULES, .. } := D.cvx.core1
  let { IN_ELIM_THM, IN_INSERT, IN_NUMSEG, LT_REFL, NOT_IN_EMPTY, NUMSEG_CLAUSES,
        NUMSEG_OFFSET_IMAGE, REAL_ABS_NUM, .. } := D.cvx.core3
  let { REAL_OF_NUM_EQ, RIGHT_FORALL_IMP_THM, .. } := D.cvx.core5
  let { SWAP_FORALL_THM, o_DEF, .. } := D.cvx.core6
  let { EQ_ADD_RCANCEL, ITERATE_CLAUSES, ITERATE_EQ, ITERATE_EQ_NEUTRAL, ITERATE_IMAGE,
        ITERATE_PAIR, ITERATE_REFLECT, ITERATE_SUPERSET, ITERATE_UNION, NUMSEG_LREC,
        PRODUCT_CLAUSES, SELECT_UNIQUE, SUC_SUB1, monoidal, neutral, .. } := D.cpx
  let { complex_pow, SIMPLE_COMPLEX_ARITH_TAC, .. } := BCXA
  let { COMPLEX_MUL_LID, COMPLEX_MUL_AC, COMPLEX_MUL_RID, .. } := BCXB
  let { COMPLEX_ENTIRE, CX_INJ, CX_MUL, COMPLEX_NORM_CX, .. } := BCXC
  let { COMPLEX_INV_1, COMPLEX_INV_MUL, .. } := BCXE
  let { COMPLEX_NORM_MUL, .. } := BCXF
  let { CNJ_CX, CNJ_MUL, .. } := BCXG
  -- @@SCOPE END

  let cproduct ← new_definition
   r"cproduct = iterate (( * ):complex->complex->complex)"

  let NEUTRAL_COMPLEX_MUL ← prove
   r"neutral(( * ):complex->complex->complex) = Cx(&1)"
   (REWRITE_TAC [neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    MESON_TAC [COMPLEX_MUL_LID, COMPLEX_MUL_RID])

  let MONOIDAL_COMPLEX_MUL ← prove
   r"monoidal(( * ):complex->complex->complex)"
   (REWRITE_TAC [monoidal, NEUTRAL_COMPLEX_MUL] THEN SIMPLE_COMPLEX_ARITH_TAC)

  let CPRODUCT_CLAUSES ← prove
   r"(!f. cproduct {} f = Cx(&1)) /\
     (!x f s. FINITE(s)
              ==> (cproduct (x INSERT s) f =
                   if x IN s then cproduct s f else f(x) * cproduct s f))"
   (REWRITE_TAC [cproduct, ← GSYM NEUTRAL_COMPLEX_MUL] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC [MONOIDAL_COMPLEX_MUL])

  let CPRODUCT_EQ_0 ← prove
   r"!f s. FINITE s ==> (cproduct s f = Cx(&0) <=> ?x. x IN s /\ f(x) = Cx(&0))"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [CPRODUCT_CLAUSES, COMPLEX_ENTIRE, IN_INSERT, CX_INJ, REAL_OF_NUM_EQ,
              ARITH, NOT_IN_EMPTY] THEN
    MESON_TAC [])

  let CPRODUCT_INV ← prove
   r"!f s. FINITE s ==> cproduct s (\x. inv(f x)) = inv(cproduct s f)"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [CPRODUCT_CLAUSES, COMPLEX_INV_1, COMPLEX_INV_MUL])

  let CPRODUCT_MUL ← prove
   r"!f g s. FINITE s
             ==> cproduct s (\x. f x * g x) = cproduct s f * cproduct s g"
   (GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [CPRODUCT_CLAUSES, COMPLEX_MUL_AC, COMPLEX_MUL_LID])

  let CPRODUCT_EQ_1 ← prove
   r"!f s. (!x:A. x IN s ==> (f(x) = Cx(&1))) ==> (cproduct s f = Cx(&1))"
   (REWRITE_TAC [cproduct, ← GSYM NEUTRAL_COMPLEX_MUL] THEN
    SIMP_TAC [ITERATE_EQ_NEUTRAL, MONOIDAL_COMPLEX_MUL])

  let CPRODUCT_1 ← prove
   r"!s. cproduct s (\n. Cx(&1)) = Cx(&1)"
   (SIMP_TAC [CPRODUCT_EQ_1])

  let CPRODUCT_POW ← prove
   r"!f s n. FINITE s
             ==> cproduct s (\x. f x pow n) = (cproduct s f) pow n"
   (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    DISCH_TAC THEN INDUCT_TAC THEN
    ASM_SIMP_TAC [complex_pow, CPRODUCT_MUL, CPRODUCT_1])

  let NORM_CPRODUCT ← prove
   r"!f s. FINITE s ==> norm(cproduct s f) = product s (\x. norm(f x))"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [CPRODUCT_CLAUSES, COMPLEX_NORM_CX, REAL_ABS_NUM,
              CPRODUCT_MUL, PRODUCT_CLAUSES, COMPLEX_NORM_MUL])

  let CPRODUCT_EQ ← prove
   r"!f g s. (!x. x IN s ==> (f x = g x)) ==> cproduct s f = cproduct s g"
   (REWRITE_TAC [cproduct] THEN MATCH_MP_TAC ITERATE_EQ THEN
    REWRITE_TAC [MONOIDAL_COMPLEX_MUL])

  let CPRODUCT_SING ← prove
   r"!f x. cproduct {x} f = f(x)"
   (SIMP_TAC [CPRODUCT_CLAUSES, FINITE_RULES, NOT_IN_EMPTY, COMPLEX_MUL_RID])

  let CPRODUCT_CLAUSES_NUMSEG ← prove
   r"(!m. cproduct(m..0) f = if m = 0 then f(0) else Cx(&1)) /\
     (!m n. cproduct(m..SUC n) f = if m <= SUC n then cproduct(m..n) f * f(SUC n)
                                   else cproduct(m..n) f)"
   (REWRITE_TAC [NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC [CPRODUCT_SING, CPRODUCT_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"~(SUC n <= n)"), COMPLEX_MUL_AC])

  let CPRODUCT_CLAUSES_RIGHT ← prove
   r"!f m n. 0 < n /\ m <= n ==> cproduct(m..n) f = cproduct(m..n-1) f * (f n)"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    SIMP_TAC [LT_REFL, CPRODUCT_CLAUSES_NUMSEG, SUC_SUB1])

  let CPRODUCT_CLAUSES_LEFT ← prove
   r"!f m n. m <= n ==> cproduct(m..n) f = f m * cproduct(m + 1..n) f"
   (SIMP_TAC [← GSYM NUMSEG_LREC, CPRODUCT_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
    ARITH_TAC)

  let CPRODUCT_IMAGE ← prove
   r"!f g s. (!x y. x IN s /\ y IN s /\ f x = f y ==> (x = y))
             ==> (cproduct (IMAGE f s) g = cproduct s (g o f))"
   (REWRITE_TAC [cproduct, ← GSYM NEUTRAL_COMPLEX_MUL] THEN
    MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC [MONOIDAL_COMPLEX_MUL])

  let CPRODUCT_OFFSET ← prove
   r"!f m p. cproduct(m+p..n+p) f = cproduct(m..n) (\i. f(i + p))"
   (SIMP_TAC [NUMSEG_OFFSET_IMAGE, CPRODUCT_IMAGE,
              EQ_ADD_RCANCEL, FINITE_NUMSEG] THEN
    REWRITE_TAC [o_DEF])

  let CPRODUCT_CONST ← prove
   r"!c s. FINITE s ==> cproduct s (\x. c) = c pow (CARD s)"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [CPRODUCT_CLAUSES, CARD_CLAUSES, complex_pow])

  let CPRODUCT_CONST_NUMSEG ← prove
   r"!c m n. cproduct (m..n) (\x. c) = c pow ((n + 1) - m)"
   (SIMP_TAC [CPRODUCT_CONST, CARD_NUMSEG, FINITE_NUMSEG])

  let CPRODUCT_PAIR ← prove
   r"!f m n. cproduct(2*m..2*n+1) f = cproduct(m..n) (\i. f(2*i) * f(2*i+1))"
   (MP_TAC (← MATCH_MP ITERATE_PAIR MONOIDAL_COMPLEX_MUL) THEN
    REWRITE_TAC [cproduct, NEUTRAL_COMPLEX_MUL])

  let CPRODUCT_REFLECT ← prove
   r"!x m n. cproduct(m..n) x =
             if n < m then Cx(&1) else cproduct(0..n-m) (\i. x(n - i))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [cproduct] THEN
    GEN_REWRITE_TAC LAND_CONV
     [← MATCH_MP ITERATE_REFLECT MONOIDAL_COMPLEX_MUL] THEN
    REWRITE_TAC [NEUTRAL_COMPLEX_MUL])

  let CNJ_CPRODUCT ← prove
   r"!f s. FINITE s ==> cnj(cproduct s f) = cproduct s (\i. cnj(f i))"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [CPRODUCT_CLAUSES, CNJ_MUL, CNJ_CX])

  let CX_PRODUCT ← prove
   r"!f s. FINITE s ==> Cx(product s f) = cproduct s (\i. Cx(f i))"
   (GEN_TAC THEN CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [CPRODUCT_CLAUSES, PRODUCT_CLAUSES, ← GSYM CX_MUL])

  let CPRODUCT_SUPERSET ← prove
   r"!f:A->complex u v.
          u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> f(x) = Cx(&1))
          ==> cproduct v f = cproduct u f"
   (REWRITE_TAC [cproduct, ← GSYM NEUTRAL_COMPLEX_MUL] THEN
    REWRITE_TAC [← MATCH_MP ITERATE_SUPERSET MONOIDAL_COMPLEX_MUL])

  let CPRODUCT_UNION ← prove
   r"!f s t. FINITE s /\ FINITE t /\ DISJOINT s t
             ==> (cproduct (s UNION t) f = cproduct s f * cproduct t f)"
   (SIMP_TAC [cproduct, ITERATE_UNION, MONOIDAL_COMPLEX_MUL])

  do
    let th ← prove
     r"(!f g s.   (!x. x IN s ==> f(x) = g(x))
                  ==> cproduct s (\i. f(i)) = cproduct s g) /\
       (!f g a b. (!i. a <= i /\ i <= b ==> f(i) = g(i))
                  ==> cproduct(a..b) (\i. f(i)) = cproduct(a..b) g) /\
       (!f g p.   (!x. p x ==> f x = g x)
                  ==> cproduct {y | p y} (\i. f(i)) = cproduct {y | p y} g)"
     (REPEAT STRIP_TAC THEN MATCH_MP_TAC CPRODUCT_EQ THEN
      ASM_SIMP_TAC [IN_ELIM_THM, IN_NUMSEG])
    extend_basic_congs (← (CONJUNCTS th).mapM SPEC_ALL)

  return { cproduct, NEUTRAL_COMPLEX_MUL, MONOIDAL_COMPLEX_MUL, CPRODUCT_CLAUSES,
           CPRODUCT_EQ_0, CPRODUCT_INV, CPRODUCT_MUL, CPRODUCT_EQ_1, CPRODUCT_1, CPRODUCT_POW,
           NORM_CPRODUCT, CPRODUCT_EQ, CPRODUCT_SING, CPRODUCT_CLAUSES_NUMSEG,
           CPRODUCT_CLAUSES_RIGHT, CPRODUCT_CLAUSES_LEFT, CPRODUCT_IMAGE, CPRODUCT_OFFSET,
           CPRODUCT_CONST, CPRODUCT_CONST_NUMSEG, CPRODUCT_PAIR, CPRODUCT_REFLECT,
           CNJ_CPRODUCT, CX_PRODUCT, CPRODUCT_SUPERSET, CPRODUCT_UNION }

end HolMultiLib.ComplexAlgebra
