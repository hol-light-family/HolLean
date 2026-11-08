/- ========================================================================= -/
/- The complex numbers as a ring: complex_ring, a field of characteristic 0, -/
/- and its ring operations, sums, products, powers and polynomial            -/
/- evaluation in the complex notation; complex conjugation as a ring         -/
/- automorphism. Needs only the algebra of the complex numbers               -/
/- (Multivariate/complex_algebra.ml) and Library/ringtheory.ml.              -/
/- ========================================================================= -/
/- File: HolMultiLib/ComplexRing.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/complex_ring.ml` (new in
  e7fbefd), in the style of HolMultiLib/Complexes.lean: pure, the proofs
  translated by hand, one `let` per OCaml `let`, in file order.  The
  load-time effects (`prioritize_real()`, `prioritize_complex()`) are at
  their file positions.  The deps are complex_algebra.ml's
  (`ComplexAlgebraDeps`) and bundles, and in `CrThms` the theorems used from
  the core library, vectors.ml and Library/ringtheory.ml.
  SessionMultiLib/ComplexRing.lean supplies them.
-/

import HolMultiLib.ComplexAlgebra

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax
open HolMultiLib.ComplexAlgebra

namespace HolMultiLib.ComplexRing

/-- The theorems complex_ring.ml uses from the core library, vectors.ml and
    Library/ringtheory.ml. -/
structure CrThms where
  (BETA_THM COND_SWAP FINITE_INDUCT_STRONG FINITE_NUMSEG FORALL_INT_CASES FUN_EQ_THM
   IN_UNIV PAIR PAIR_EQ REAL_OF_NUM_EQ REAL_OF_NUM_SUC RIGHT_FORALL_IMP_THM SELECT_UNIQUE
   SUBSET_UNIV int_neg_th int_of_num_th
   VSUM_CLAUSES
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_UNIT POLY_EVAL_EXPAND RING_CHAR_EQ_0 RING_OF_INT_CASES
   RING_PRODUCT_CLAUSES RING_SUM_CLAUSES field ring_0 ring_1 ring_add ring_automorphism
   ring_carrier ring_div ring_homomorphism ring_inv ring_isomorphism ring_isomorphisms
   ring_mul ring_neg ring_of_num ring_pow ring_sub ring_tybij : thm)
  deriving Inhabited

structure ComplexRingDeps where
  /-- What complex_algebra.ml was given. -/
  ca : ComplexAlgebraDeps
  cr : CrThms

/- ------------------------------------------------------------------------- -/
/- The ring complex_ring and its operations.  (complex_ring.ml 9-109)       -/
/- ------------------------------------------------------------------------- -/

structure CR where
  complex_ring : thm
  COMPLEX_RING_CLAUSES : thm
  FIELD_COMPLEX_RING : thm
  INTEGRAL_DOMAIN_COMPLEX_RING : thm
  COMPLEX_RING_OF_NUM : thm
  COMPLEX_RING_OF_INT : thm
  RING_CHAR_COMPLEX_RING : thm
  COMPLEX_RING_SUB : thm
  COMPLEX_RING_INV : thm
  COMPLEX_RING_DIV : thm
  COMPLEX_RING_POW : thm
  COMPLEX_RING_SUM : thm
  COMPLEX_RING_PRODUCT : thm
  POLY_EVAL_COMPLEX_RING : thm
  RING_HOMOMORPHISM_CNJ : thm
  RING_AUTOMORPHISM_CNJ : thm
  deriving Inhabited

@[nospecialize]
def setupCR [HolBase] (D : ComplexRingDeps) (BCXA : CXA) (BCXC : CXC) (BCXD : CXD)
    (BCXE : CXE) (BCXG : CXG) (BCXK : CXK) : ExceptT String IO CR := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, MESON_TAC, new_definition, REAL_RAT_REDUCE_CONV, .. } := D.ca.cvx
  let { BETA_THM, COND_SWAP, field, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_UNIT,
        FINITE_INDUCT_STRONG, FINITE_NUMSEG, FORALL_INT_CASES, FUN_EQ_THM, IN_UNIV,
        int_neg_th, int_of_num_th, PAIR, PAIR_EQ, POLY_EVAL_EXPAND, REAL_OF_NUM_EQ,
        REAL_OF_NUM_SUC, RIGHT_FORALL_IMP_THM, ring_0, ring_1, ring_add, ring_automorphism,
        ring_carrier, RING_CHAR_EQ_0, ring_div, ring_homomorphism, ring_inv,
        ring_isomorphism, ring_isomorphisms, ring_mul, ring_neg, ring_of_num,
        RING_OF_INT_CASES, ring_pow, RING_PRODUCT_CLAUSES, ring_sub, RING_SUM_CLAUSES,
        ring_tybij, SELECT_UNIQUE, SUBSET_UNIV, VSUM_CLAUSES, .. } := D.cr
  let { complex_div, complex_pow, complex_sub, prioritize_complex, .. } := BCXA
  let { COMPLEX_MUL_RINV, COMPLEX_VEC_0, CX_ADD, CX_INJ, CX_NEG, .. } := BCXC
  let { COMPLEX_RING, .. } := BCXD
  let { COMPLEX_FIELD, COMPLEX_INV_0, .. } := BCXE
  let { CNJ_ADD, CNJ_CNJ, CNJ_CX, CNJ_MUL, CNJ_NEG, .. } := BCXG
  let { CPRODUCT_CLAUSES, .. } := BCXK
  -- @@SCOPE END

  -- prioritize_real() (complex_ring.ml 9), before the `needs`, which the
  -- imports have done
  D.ca.cvx.prioritize_real
  -- prioritize_complex() (complex_ring.ml 13)
  prioritize_complex

  let complex_ring ← new_definition
   r"complex_ring = ring((:complex),Cx(&0),Cx(&1),( -- ),( + ),( * ))"

  let COMPLEX_RING_CLAUSES ← prove
   r"ring_carrier complex_ring = (:complex) /\
   ring_0 complex_ring = Cx(&0) /\
   ring_1 complex_ring = Cx(&1) /\
   ring_neg complex_ring = ( -- ) /\
   ring_add complex_ring = ( + ) /\
   ring_mul complex_ring = ( * )"
   (PURE_REWRITE_TAC
     [← GSYM PAIR_EQ, ring_carrier, ring_0, ring_1, ring_neg, ring_add, ring_mul,
      BETA_THM, PAIR] THEN
    PURE_REWRITE_TAC [complex_ring, ← GSYM (← CONJUNCT2 ring_tybij)] THEN
    REWRITE_TAC [IN_UNIV] THEN CONV_TAC COMPLEX_RING)

  let FIELD_COMPLEX_RING ← prove
   r"field complex_ring"
   (REWRITE_TAC [field, COMPLEX_RING_CLAUSES, IN_UNIV, CX_INJ] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN MESON_TAC [COMPLEX_MUL_RINV])

  let INTEGRAL_DOMAIN_COMPLEX_RING ← prove
   r"integral_domain complex_ring"
   (SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, FIELD_COMPLEX_RING])

  let COMPLEX_RING_OF_NUM ← prove
   r"ring_of_num complex_ring = \n. Cx(&n)"
   (REWRITE_TAC [FUN_EQ_THM] THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [ring_of_num, COMPLEX_RING_CLAUSES, ← GSYM REAL_OF_NUM_SUC,
                     CX_ADD])

  let COMPLEX_RING_OF_INT ← prove
   r"ring_of_int complex_ring = \n. Cx(real_of_int n)"
   (REWRITE_TAC [FUN_EQ_THM, RING_OF_INT_CASES, FORALL_INT_CASES] THEN
    REWRITE_TAC [int_neg_th, int_of_num_th, COMPLEX_RING_OF_NUM] THEN
    REWRITE_TAC [COMPLEX_RING_CLAUSES, CX_NEG])

  let RING_CHAR_COMPLEX_RING ← prove
   r"ring_char complex_ring = 0"
   (REWRITE_TAC [RING_CHAR_EQ_0, COMPLEX_RING_OF_NUM, COMPLEX_RING_CLAUSES,
                 CX_INJ, REAL_OF_NUM_EQ])

  let COMPLEX_RING_SUB ← prove
   r"ring_sub complex_ring = ( - )"
   (REWRITE_TAC [FUN_EQ_THM, ring_sub, COMPLEX_RING_CLAUSES, complex_sub])

  let COMPLEX_RING_INV ← prove
   r"ring_inv complex_ring = inv"
   (REWRITE_TAC [FUN_EQ_THM, ring_inv, COMPLEX_RING_CLAUSES] THEN
    SIMP_TAC [FIELD_UNIT, FIELD_COMPLEX_RING, COMPLEX_RING_CLAUSES,
              IN_UNIV, COND_SWAP] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [COMPLEX_INV_0] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN POP_ASSUM MP_TAC THEN
    CONV_TAC COMPLEX_FIELD)

  let COMPLEX_RING_DIV ← prove
   r"ring_div complex_ring = ( / )"
   (REWRITE_TAC [FUN_EQ_THM, ring_div, COMPLEX_RING_INV, COMPLEX_RING_CLAUSES,
                 complex_div])

  let COMPLEX_RING_POW ← prove
   r"ring_pow complex_ring = (pow)"
   (REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [ring_pow, complex_pow, COMPLEX_RING_CLAUSES])

  let COMPLEX_RING_SUM ← prove
   r"!s (f:A->complex). FINITE s ==> ring_sum complex_ring s f = vsum s f"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [RING_SUM_CLAUSES, VSUM_CLAUSES, COMPLEX_RING_CLAUSES, IN_UNIV,
              COMPLEX_VEC_0])

  let COMPLEX_RING_PRODUCT ← prove
   r"!s (f:A->complex).
        FINITE s ==> ring_product complex_ring s f = cproduct s f"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [RING_PRODUCT_CLAUSES, CPRODUCT_CLAUSES, COMPLEX_RING_CLAUSES,
              IN_UNIV])

  let POLY_EVAL_COMPLEX_RING ← prove
   r"!p z. p IN ring_carrier(poly_ring complex_ring (:1))
         ==> poly_eval complex_ring p z =
             vsum(0..poly_deg complex_ring p) (\i. coeff i p * z pow i)"
   (SIMP_TAC [POLY_EVAL_EXPAND, COMPLEX_RING_CLAUSES, IN_UNIV,
              COMPLEX_RING_SUM, FINITE_NUMSEG, COMPLEX_RING_POW])

  let RING_HOMOMORPHISM_CNJ ← prove
   r"ring_homomorphism(complex_ring,complex_ring) cnj"
   (REWRITE_TAC [ring_homomorphism, COMPLEX_RING_CLAUSES, SUBSET_UNIV, IN_UNIV,
                 CNJ_ADD, CNJ_MUL, CNJ_NEG, CNJ_CX])

  let RING_AUTOMORPHISM_CNJ ← prove
   r"ring_automorphism complex_ring cnj"
   (REWRITE_TAC [ring_automorphism, ring_isomorphism, ring_isomorphisms] THEN
    EXISTS_TAC (← q r"cnj") THEN
    REWRITE_TAC [RING_HOMOMORPHISM_CNJ, COMPLEX_RING_CLAUSES, IN_UNIV, CNJ_CNJ])

  return { complex_ring, COMPLEX_RING_CLAUSES, FIELD_COMPLEX_RING,
           INTEGRAL_DOMAIN_COMPLEX_RING, COMPLEX_RING_OF_NUM, COMPLEX_RING_OF_INT,
           RING_CHAR_COMPLEX_RING, COMPLEX_RING_SUB, COMPLEX_RING_INV, COMPLEX_RING_DIV,
           COMPLEX_RING_POW, COMPLEX_RING_SUM, COMPLEX_RING_PRODUCT,
           POLY_EVAL_COMPLEX_RING, RING_HOMOMORPHISM_CNJ, RING_AUTOMORPHISM_CNJ }

end HolMultiLib.ComplexRing
