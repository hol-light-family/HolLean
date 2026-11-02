/- ========================================================================= -/
/- Determinant and trace of a square matrix.                                 -/
/- ========================================================================= -/
/- File: HolMultiLib/Determinants.lean

  Original (c) Copyright, John Harrison 1998-2008
  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/determinants.ml`, in the style
  of HolMultiLib/Vectors.lean: pure, the proofs translated by hand, one `let`
  per OCaml `let`, in file order.  What determinants.ml uses from the core
  library, from Multivariate/vectors.ml (with misc.ml) and from
  Library/permutations.ml, floor.ml and products.ml is passed in
  `DeterminantsDeps`; SessionMultiLib/Determinants.lean supplies it.

  determinants.ml's `needs` are the wiring's imports.  Its load-time effects
  (`prioritize_real` and the additions to the invariance lists) are made
  inside the bundles at their file positions.
-/

import HolMath

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolMultiLib.Determinants

set_option maxHeartbeats 4000000

/- ------------------------------------------------------------------------- -/
/- What determinants.ml uses from the core library (supplied by Session).    -/
/- (Three structures, each under 128 fields.)                                 -/
/- ------------------------------------------------------------------------- -/

/-- Core theorems, ADD1 to LE_0. -/
structure CoreThms1 where
  (ADD1 ADD_CLAUSES ADD_SUB ADD_SUB2 ADD_SYM ADMISSIBLE_IMP_SUPERADMISSIBLE
   AND_FORALL_THM ARITH ARITH_EQ CARD_DELETE CARD_DIFF CARD_EQ_BIJECTION
   CARD_IMAGE_EQ_INJ CARD_IMAGE_INJ CARD_LE_INJ CARD_NUMSEG CARD_NUMSEG_1 CARD_UNION
   CART_EQ COND_ID COND_RAND COND_RATOR CONJ_ACI CONJ_ASSOC CONJ_SYM DIMINDEX_1
   DIMINDEX_2 DIMINDEX_3 DIMINDEX_4 DIMINDEX_FINITE_PROD DIMINDEX_GE_1 DISJOINT
   DISJOINT_SYM DIVISION DIV_UNIQ EMPTY_SUBSET EQ_TRANS ETA_AX EXISTS_IN_IMAGE
   EXISTS_REFL EXTENSION FINITE_DELETE FINITE_DIFF FINITE_EMPTY FINITE_IMAGE
   FINITE_IMAGE_INJ_EQ FINITE_INDEX_NUMSEG FINITE_INDUCT_STRONG FINITE_INSERT
   FINITE_NUMSEG FINITE_PRODUCT FINITE_PRODUCT_DEPENDENT FINITE_RESTRICT FINITE_RULES
   FINITE_UNION FORALL_IN_GSPEC FORALL_IN_IMAGE FUN_EQ_THM HAS_SIZE IMAGE_CLAUSES
   IMAGE_EQ_EMPTY IMAGE_I IMAGE_ID IMAGE_o IMP_CONJ IMP_IMP IN INJECTIVE_ON_ALT
   INSERT_DELETE IN_DELETE IN_ELIM_PAIR_THM IN_ELIM_THM IN_IMAGE IN_INSERT IN_NUMSEG
   IN_SING IN_UNION IN_UNIV I_DEF LAMBDA_BETA LAMBDA_ETA LE LEFT_FORALL_IMP_THM
   LEFT_IMP_EXISTS_THM LE_0 : thm)
  deriving Inhabited

/-- Core theorems, LE_1 to REAL_POLYFUN_FINITE_ROOTS. -/
structure CoreThms2 where
  (LE_1 LE_ADD LE_ADD_LCANCEL LE_ANTISYM LE_MULT_RCANCEL LE_REFL LE_SUC LE_TRANS
   LTE_ANTISYM LT_IMP_LE LT_REFL MEMBER_NOT_EMPTY MOD_UNIQ MONOIDAL_REAL_MUL MONO_EXISTS
   MONO_FORALL NOT_FORALL_THM NOT_IMP NOT_IN_EMPTY NOT_LT NOT_SUC NUMSEG_EMPTY
   NUMSEG_SING PAIRWISE_IMAGE PAIRWISE_MONO PRODUCT_CLAUSES PSUBSET_ALT RDIV_LT_EQ
   REAL_ABS_ABS REAL_ABS_INV REAL_ABS_MUL REAL_ABS_POS REAL_ADD_LDISTRIB REAL_ADD_LID
   REAL_ADD_RID REAL_DIV_1 REAL_DIV_LMUL REAL_DIV_REFL REAL_DIV_RMUL REAL_ENTIRE
   REAL_EQ_IMP_LE REAL_EQ_MUL_RCANCEL REAL_EQ_RDIV_EQ REAL_INV_0 REAL_INV_1
   REAL_INV_EQ_0 REAL_LET_ADD REAL_LE_ADD REAL_LE_ANTISYM REAL_LE_DIV REAL_LE_MUL
   REAL_LE_POW_2 REAL_LE_RCANCEL_IMP REAL_LE_REFL REAL_LE_RMUL REAL_LE_RMUL_EQ
   REAL_LE_SQUARE REAL_LE_SQUARE_ABS REAL_LE_SUP_FINITE REAL_LE_TRANS REAL_LTE_ADD
   REAL_LTE_TRANS REAL_LT_ADD REAL_LT_IMP_LE REAL_LT_IMP_NZ REAL_LT_INV_EQ REAL_LT_LE
   REAL_LT_MUL REAL_LT_POW_2 REAL_LT_RDIV_EQ REAL_MUL_AC REAL_MUL_ASSOC REAL_MUL_LID
   REAL_MUL_LINV REAL_MUL_LZERO REAL_MUL_RID REAL_MUL_RINV REAL_MUL_RZERO REAL_MUL_SYM
   REAL_NEG_0 REAL_NEG_NEG REAL_NOT_LE REAL_OF_NUM_EQ REAL_OF_NUM_LT
   REAL_POLYFUN_FINITE_ROOTS : thm)
  deriving Inhabited

/-- Core theorems, REAL_POS to real_pow, and the list theorems. -/
structure CoreThms3 where
  (REAL_POS REAL_POW2_ABS REAL_POW_1 REAL_POW_2 REAL_POW_ADD REAL_POW_EQ_0 REAL_POW_MUL
   REAL_POW_ONE REAL_POW_ZERO REAL_RSQRT_LE REAL_SUB_0 REAL_SUB_LDISTRIB
   REAL_SUB_RDISTRIB REAL_SUB_REFL REAL_SUB_RZERO REAL_SUP_LE RIGHT_FORALL_IMP_THM
   RIGHT_IMP_FORALL_THM SIMPLE_IMAGE SIMPLE_IMAGE_GEN SKOLEM_THM SQRT_MUL SQRT_UNIQUE
   SUBSET SUBSET_ANTISYM_EQ SUBSET_REFL SUBSET_UNIV SUB_ADD SUC_SUB1 SUM_0 SUM_ADD
   SUM_ADD_NUMSEG SUM_CASES SUM_CLAUSES SUM_CLAUSES_LEFT SUM_CLAUSES_NUMSEG
   SUM_CONST_NUMSEG SUM_DELETE SUM_DELTA SUM_EQ SUM_EQ_0 SUM_EQ_GENERAL_INVERSES
   SUM_EQ_NUMSEG SUM_LE SUM_LE_NUMSEG SUM_LMUL SUM_MUL_BOUND SUM_NEG SUM_OFFSET
   SUM_POS_LE_NUMSEG SUM_POS_LT SUM_POS_LT_ALL SUM_RMUL SUM_SING SUM_SUB_NUMSEG
   SUM_SUM_PRODUCT SUM_SUPERSET SUM_SWAP SUM_SWAP_NUMSEG SUP_EQ SUP_UNIQUE
   SURJECTIVE_IFF_INJECTIVE SURJECTIVE_IMAGE SWAP_FORALL_THM UNION_COMM UNION_UNIV
   UNWIND_THM2 WF_num WLOG_LT list_INDUCT num_INDUCTION num_WF numseg o_DEF o_THM
   pairwise product real_abs real_div real_pow admissible
   ALL ITLIST LENGTH MAP LENGTH_EQ_NIL : thm)
  deriving Inhabited

/-- Core theorems Session defines without a type ascription. -/
structure CoreThms4 where
  (BETA_THM CONTRAPOS_THM DE_MORGAN_THM EQ_IMP FORALL_AND_THM FORALL_PAIR_THM
   FORALL_SIMP FORALL_UNWIND_THM2 I_O_ID I_THM LEFT_AND_EXISTS_THM MONO_AND MONO_IMP
   MONO_OR PAIR_EQ RIGHT_AND_EXISTS_THM RIGHT_IMP_EXISTS_THM EQ_SYM_EQ IMP_CONJ_ALT : thm)
  deriving Inhabited

/- ------------------------------------------------------------------------- -/
/- What determinants.ml uses from vectors.ml and misc.ml.                    -/
/- ------------------------------------------------------------------------- -/

/-- vectors.ml theorems, ADJOINT_ADJOINT to MATRIX_I. -/
structure VecThms1 where
  (ADJOINT_ADJOINT ADJOINT_LINEAR ADJOINT_WORKS BASIS_CARD_EQ_DIM BASIS_COMPONENT
   BASIS_EXPANSION BASIS_INJ_EQ BASIS_NONZERO CARD_GE_DIM_INDEPENDENT
   COLLINEAR_LEMMA_ALT COLUMN_TRANSP COMPONENT_LE_NORM COND_COMPONENT DIM_EQ_0
   DIM_EQ_CARD DIM_EQ_FULL DIM_EQ_SPAN DIM_INJECTIVE_LINEAR_IMAGE DIM_INSERT_0
   DIM_PSUBSET DIM_SPAN DIM_SUBSET_UNIV DIM_UNIV DIST_MIDPOINT DOT_2 DOT_BASIS
   DOT_CAUCHY_SCHWARZ_EQUAL DOT_EQ_0 DOT_LADD DOT_LMUL DOT_LMUL_MATRIX DOT_LNEG DOT_LSUB
   DOT_LSUM DOT_LZERO DOT_MATRIX_PRODUCT DOT_MATRIX_VECTOR_MUL DOT_NORM DOT_NORM_SUB
   DOT_POS_LE DOT_RADD DOT_RMUL DOT_RNEG DOT_RSUB DOT_RSUM DOT_RZERO DOT_SYM
   EXISTS_VECTOR_2 FORALL_1 FORALL_2 FORALL_3 FULL_RANK_INJECTIVE HYPERPLANE_EQ_EMPTY
   HYPERPLANE_EQ_UNIV INDEPENDENT_BOUND INDEPENDENT_IMP_FINITE INDEPENDENT_MONO
   INDEPENDENT_SPAN_BOUND INDEPENDENT_STDBASIS INVERTIBLE_LEFT_INVERSE INVERTIBLE_MAT
   INVERTIBLE_MATRIX_INV INVERTIBLE_RIGHT_INVERSE INVERTIBLE_TRANSP
   ISOMETRY_UNIV_SUBSPACE ISOMETRY_UNIV_UNIV LINEAR_0 LINEAR_1_GEN LINEAR_ADD
   LINEAR_CMUL LINEAR_COMPOSE LINEAR_COMPOSE_CMUL LINEAR_COMPOSE_NEG_EQ
   LINEAR_COMPOSE_VSUM LINEAR_ID LINEAR_INDEPENDENT_EXTEND LINEAR_INJECTIVE_0
   LINEAR_INJECTIVE_IMP_SURJECTIVE LINEAR_INJECTIVE_LEFT_INVERSE LINEAR_INVERSE_LEFT
   LINEAR_NEG LINEAR_NEGATION LINEAR_SUB LINEAR_SURJECTIVE_IFF_INJECTIVE LINEAR_VSUM
   LOWDIM_SUBSET_HYPERPLANE MATRIX_ADD_ASSOC MATRIX_ADD_COMPONENT MATRIX_ADD_LID
   MATRIX_ADD_RNEG MATRIX_CMUL_ASSOC MATRIX_CMUL_COMPONENT MATRIX_CMUL_LID
   MATRIX_CMUL_LZERO MATRIX_EQ MATRIX_EQ_0 MATRIX_FULL_LINEAR_EQUATIONS MATRIX_I : thm)
  deriving Inhabited

/-- vectors.ml theorems, MATRIX_ID to SPAN_EMPTY. -/
structure VecThms2 where
  (MATRIX_ID MATRIX_INV MATRIX_INVERTIBLE MATRIX_INV_EQ_0 MATRIX_INV_I MATRIX_INV_INV
   MATRIX_INV_MUL_INNER MATRIX_INV_MUL_OUTER MATRIX_INV_UNIQUE MATRIX_INV_UNIQUE_STRONG
   MATRIX_LEFT_INVERTIBLE_INJECTIVE MATRIX_LEFT_INVERTIBLE_KER MATRIX_LEFT_RIGHT_INVERSE
   MATRIX_MUL_ASSOC MATRIX_MUL_COMPONENT MATRIX_MUL_DOT MATRIX_MUL_LCANCEL
   MATRIX_MUL_LID MATRIX_MUL_RCANCEL MATRIX_MUL_RID MATRIX_MUL_VSUM MATRIX_NEG_0
   MATRIX_NEG_ADD MATRIX_NEG_COMPONENT MATRIX_NEG_MINUS1 MATRIX_NEG_NEG MATRIX_NEG_SUB
   MATRIX_NONFULL_LINEAR_EQUATIONS_EQ MATRIX_OF_MATRIX_VECTOR_MUL
   MATRIX_RIGHT_INVERTIBLE_INDEPENDENT_ROWS MATRIX_SUB MATRIX_SUB_COMPONENT
   MATRIX_SUB_EQ MATRIX_SUB_LDISTRIB MATRIX_SUB_RDISTRIB MATRIX_SUB_RZERO
   MATRIX_TRANSP_MUL MATRIX_VECTOR_LMUL MATRIX_VECTOR_MUL_ADD_LDISTRIB
   MATRIX_VECTOR_MUL_ADD_RDISTRIB MATRIX_VECTOR_MUL_ASSOC MATRIX_VECTOR_MUL_BASIS
   MATRIX_VECTOR_MUL_COMPONENT MATRIX_VECTOR_MUL_LID MATRIX_VECTOR_MUL_LINEAR
   MATRIX_VECTOR_MUL_LNEG MATRIX_VECTOR_MUL_RMUL MATRIX_VECTOR_MUL_SUB_RDISTRIB
   MATRIX_VECTOR_MUL_TRANSP MATRIX_WORKS MAT_COMPONENT NORM_0 NORM_BASIS
   NORM_CAUCHY_SCHWARZ NORM_CAUCHY_SCHWARZ_ABS NORM_EQ NORM_EQ_0 NORM_EQ_1
   NORM_EQ_SQUARE NORM_LE NORM_LE_COMPONENTWISE NORM_LE_SQUARE NORM_MUL NORM_NEG
   NORM_POS_LE NORM_POS_LT NORM_POW_2 NORM_VSUM_PYTHAGOREAN ONORM ONORM_COMPOSE
   ONORM_COVARIANCE ONORM_LE_EQ ONORM_NEG ONORM_POS_LE ONORM_POS_LT ORTHOGONAL_0
   ORTHOGONAL_BASIS_BASIS ORTHOGONAL_CLAUSES ORTHOGONAL_LNEG ORTHOGONAL_MUL
   ORTHOGONAL_REFL ORTHOGONAL_RNEG ORTHOGONAL_SYM ORTHONORMAL_BASIS_SUBSPACE
   ORTHONORMAL_EXTENSION PAIRWISE_ORTHOGONAL_IMP_FINITE PAIRWISE_ORTHOGONAL_INDEPENDENT
   PRESERVES_NORM_INJECTIVE PRESERVES_NORM_PRESERVES_DOT QUANTIFY_SURJECTION_HIGHER_THM
   RANK_BOUND RANK_DIM_IM RANK_GRAM REAL_ABS_NORM ROWS_TRANSP ROW_TRANSP SPAN_CLAUSES
   SPAN_EMPTY : thm)
  deriving Inhabited

/-- vectors.ml theorems, SPAN_EQ_DIM to vector_norm, and two from misc.ml. -/
structure VecThms3 where
  (SPAN_EQ_DIM SPAN_FINITE SPAN_INDUCT_ALT SPAN_LINEAR_IMAGE SPAN_MONO SPAN_MUL SPAN_NEG
   SPAN_OF_SUBSPACE SPAN_STDBASIS SPAN_SUBSET_SUBSPACE SPAN_SUPERSET SPAN_UNIV SPAN_VSUM
   SUBSPACE_LINEAR_FIXED_POINTS SUBSPACE_MUL SUBSPACE_SPAN SUBSPACE_SUB SUBSPACE_UNIV
   SUM_1 SUM_2 SUM_3 SUM_4 SURJECTIVE_SCALING SYMMETRIC_MATRIX_ADD SYMMETRIC_MATRIX_CMUL
   SYMMETRIC_MATRIX_INV_LMUL SYMMETRIC_MATRIX_INV_RMUL TRANSP_COMPONENT TRANSP_EQ
   TRANSP_MAT TRANSP_MATRIX_CMUL TRANSP_MATRIX_INV TRANSP_MATRIX_SUB TRANSP_TRANSP
   VECTORIZE_EQ_0 VECTOR_2 VECTOR_3 VECTOR_4 VECTOR_ADD_COMPONENT VECTOR_ADD_RID
   VECTOR_EQ VECTOR_EQ_LDOT VECTOR_IN_ORTHONORMAL_BASIS VECTOR_MATRIX_MUL_TRANSP
   VECTOR_MUL_ASSOC VECTOR_MUL_COMPONENT VECTOR_MUL_EQ_0 VECTOR_MUL_LID VECTOR_MUL_LNEG
   VECTOR_MUL_LZERO VECTOR_MUL_RZERO VECTOR_NEG_0 VECTOR_NEG_COMPONENT VECTOR_NEG_EQ_0
   VECTOR_NEG_MINUS1 VECTOR_SUB VECTOR_SUB_COMPONENT VECTOR_SUB_EQ VECTOR_SUB_LDISTRIB
   VECTOR_SUB_LZERO VECTOR_SUB_REFL VECTOR_SUB_RZERO VEC_COMPONENT VEC_EQ VSUM_CLAUSES
   VSUM_COMPONENT VSUM_DELETE_CASES VSUM_DELTA VSUM_EQ VSUM_LMUL basis collinear column
   columnvector dependent dist dot invertible linear mat matrix matrix_add matrix_mul
   matrix_sub matrix_vector_mul midpoint onorm orthogonal row rows rowvector
   symmetric_matrix transp vector_norm
   FINITE_INDEX_NUMSEG_SPECIAL VECTORIZE_COMPONENT : thm)
  deriving Inhabited

/-- What determinants.ml uses from Library/permutations.ml, floor.ml and products.ml. -/
structure LibThms where
  (FINITE_PERMUTATIONS INTEGER_CLOSED INTEGER_MUL INTEGER_SUM ITERATE_PERMUTE
   PERMUTATION_COMPOSE PERMUTATION_PERMUTES PERMUTATION_SWAP PERMUTES_EMPTY PERMUTES_I
   PERMUTES_IMAGE PERMUTES_INJECTIVE PERMUTES_INVERSE PERMUTES_INVERSES
   PERMUTES_INVERSES_o PERMUTES_INVERSE_EQ PERMUTES_IN_IMAGE PERMUTES_IN_NUMSEG
   PERMUTES_NUMSET_GE PERMUTES_NUMSET_LE PERMUTES_SING PERMUTES_SWAP
   PRODUCT_CLAUSES_LEFT PRODUCT_CLAUSES_NUMSEG PRODUCT_CLOSED PRODUCT_CONST
   PRODUCT_CONST_NUMSEG_1 PRODUCT_EQ PRODUCT_EQ_0 PRODUCT_EQ_0_NUMSEG PRODUCT_EQ_1
   PRODUCT_EQ_1_NUMSEG PRODUCT_EQ_NUMSEG PRODUCT_IMAGE PRODUCT_LE_NUMSEG PRODUCT_MUL
   PRODUCT_MUL_NUMSEG PRODUCT_POS_LE_NUMSEG PRODUCT_SING PRODUCT_SING_NUMSEG
   SIGN_COMPOSE SIGN_I SIGN_IDEMPOTENT SIGN_INVERSE SIGN_NZ SIGN_SWAP
   SUM_OVER_PERMUTATIONS_INSERT SUM_PERMUTATIONS_COMPOSE_R SUM_PERMUTATIONS_INVERSE
   SWAP_REFL permutes sign swap : thm)
  deriving Inhabited

/-- What determinants.ml uses from the core library's and vectors.ml's procedures. -/
structure DeterminantsDeps where
  -- definitions and parser state
  new_definition : String → ExceptT String IO thm
  prioritize_real : IO Unit
  -- decision procedures
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  ASM_MESON_TAC : List thm → tactic
  ASM_REAL_ARITH_TAC : tactic
  INDUCT_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  REAL_ARITH : term → ExceptT String IO thm
  REAL_ARITH_TAC : tactic
  REAL_FIELD : term → ExceptT String IO thm
  REAL_RING : term → ExceptT String IO thm
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  -- conversions
  NUMSEG_CONV : ioconv
  NUM_REDUCE_CONV : ioconv
  REAL_RAT_REDUCE_CONV : ioconv
  num_CONV : ioconv
  instantiate_casewise_recursion : ioconv
  GEN_BETA_CONV : ioconv
  mk_small_numeral : Int → Except String term
  -- vectors.ml's procedures and invariance lists
  VECTOR_ARITH : term → ExceptT String IO thm
  VECTOR_ARITH_TAC : tactic
  NORM_ARITH : term → ExceptT String IO thm
  MATRIX_ARITH : term → ExceptT String IO thm
  LINEAR_INVARIANT_RULE : thm → ExceptT String IO thm
  PARTIAL_EXPAND_QUANTS_CONV : List String → thm → ExceptT String IO ioconv
  EXPAND_QUANTS_CONV : thm → ExceptT String IO ioconv
  add_linear_invariants : List thm → ExceptT String IO Unit
  add_translation_invariants : List thm → ExceptT String IO Unit
  invariant_under_linear : IO.Ref (List thm)
  invariant_under_translation : IO.Ref (List thm)
  scaling_theorems : IO.Ref (List thm)
  -- theorems
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3
  core4 : CoreThms4
  vec1 : VecThms1
  vec2 : VecThms2
  vec3 : VecThms3
  lib : LibThms

/- ------------------------------------------------------------------------- -/
/- Trace of a matrix; definition of determinant; a few general lemmas.       -/
/- (determinants.ml 12-112)                                                   -/
/- ------------------------------------------------------------------------- -/

structure Trace where
  trace : thm
  TRACE_0 : thm
  TRACE_I : thm
  TRACE_ADD : thm
  TRACE_SUB : thm
  TRACE_CMUL : thm
  TRACE_NEG : thm
  TRACE_MUL_SYM : thm
  TRACE_TRANSP : thm
  TRACE_SIMILAR : thm
  TRACE_MUL_CYCLIC : thm
  det : thm
  IN_DIMINDEX_SWAP : thm
  LAMBDA_BETA_PERM : thm
  PRODUCT_PERMUTE : thm
  PRODUCT_PERMUTE_NUMSEG : thm
  REAL_MUL_SUM : thm
  REAL_MUL_SUM_NUMSEG : thm
  deriving Inhabited

@[nospecialize]
def setupTrace [HolBase] (D : DeterminantsDeps) : ExceptT String IO Trace := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, MESON_TAC, new_definition, prioritize_real, .. } := D
  let { FINITE_NUMSEG, IN_NUMSEG, LAMBDA_BETA, .. } := D.core1
  let { MONOIDAL_REAL_MUL, REAL_MUL_RID, REAL_MUL_SYM, .. } := D.core2
  let { SUM_0, SUM_ADD_NUMSEG, SUM_CONST_NUMSEG, SUM_LMUL, SUM_NEG, SUM_SUB_NUMSEG,
        SUM_SWAP_NUMSEG, product, .. } := D.core3
  let { MATRIX_CMUL_COMPONENT, .. } := D.vec1
  let { MATRIX_INV, MATRIX_MUL_ASSOC, MATRIX_MUL_RID, MATRIX_NEG_COMPONENT, .. } := D.vec2
  let { mat, matrix_add, matrix_mul, matrix_sub, transp, .. } := D.vec3
  let { ITERATE_PERMUTE, PERMUTES_IN_IMAGE, swap, .. } := D.lib
  -- @@SCOPE END

  prioritize_real

  let trace ← new_definition
   r"(trace:real^N^N->real) A = sum(1..dimindex(:N)) (\i. A$i$i)"

  let TRACE_0 ← prove
   r"trace(mat 0) = &0"
   (SIMP_TAC [trace, mat, LAMBDA_BETA, SUM_0])

  let TRACE_I ← prove
   r"trace(mat 1 :real^N^N) = &(dimindex(:N))"
   (SIMP_TAC [trace, mat, LAMBDA_BETA, SUM_CONST_NUMSEG, REAL_MUL_RID] THEN
    AP_TERM_TAC THEN ARITH_TAC)

  let TRACE_ADD ← prove
   r"!A B:real^N^N. trace(A + B) = trace(A) + trace(B)"
   (SIMP_TAC [trace, matrix_add, SUM_ADD_NUMSEG, LAMBDA_BETA])

  let TRACE_SUB ← prove
   r"!A B:real^N^N. trace(A - B) = trace(A) - trace(B)"
   (SIMP_TAC [trace, matrix_sub, SUM_SUB_NUMSEG, LAMBDA_BETA])

  let TRACE_CMUL ← prove
   r"!c A:real^N^N. trace(c %% A) = c * trace A"
   (REWRITE_TAC [trace, MATRIX_CMUL_COMPONENT, SUM_LMUL])

  let TRACE_NEG ← prove
   r"!A:real^N^N. trace(--A) = --(trace A)"
   (REWRITE_TAC [trace, MATRIX_NEG_COMPONENT, SUM_NEG])

  let TRACE_MUL_SYM ← prove
   r"!A B:real^N^M. trace(A ** B) = trace(B ** A)"
   (REPEAT GEN_TAC THEN SIMP_TAC [trace, matrix_mul, LAMBDA_BETA] THEN
    GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC [REAL_MUL_SYM])

  let TRACE_TRANSP ← prove
   r"!A:real^N^N. trace(transp A) = trace A"
   (SIMP_TAC [trace, transp, LAMBDA_BETA])

  let TRACE_SIMILAR ← prove
   r"!A:real^N^N U:real^N^N.
        invertible U ==> trace(matrix_inv U ** A ** U) = trace A"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [TRACE_MUL_SYM] THEN
    ASM_SIMP_TAC [← GSYM MATRIX_MUL_ASSOC, MATRIX_INV, MATRIX_MUL_RID])

  let TRACE_MUL_CYCLIC ← prove
   r"!A:real^P^M B C:real^M^N. trace(A ** B ** C) = trace(B ** C ** A)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [MATRIX_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [TRACE_MUL_SYM] THEN
    REWRITE_TAC [MATRIX_MUL_ASSOC])

  let det ← new_definition
   r"det(A:real^N^N) =
        sum { p | p permutes 1..dimindex(:N) }
            (\p. sign(p) * product (1..dimindex(:N)) (\i. A$i$(p i)))"

  let IN_DIMINDEX_SWAP ← prove
   r"!m n j. 1 <= m /\ m <= dimindex(:N) /\
             1 <= n /\ n <= dimindex(:N) /\
             1 <= j /\ j <= dimindex(:N)
           ==> 1 <= swap(m,n) j /\ swap(m,n) j <= dimindex(:N)"
   (REWRITE_TAC [swap] THEN ARITH_TAC)

  let LAMBDA_BETA_PERM ← prove
   r"!p i. p permutes 1..dimindex(:N) /\ 1 <= i /\ i <= dimindex(:N)
         ==> ((lambda) g :A^N) $ p(i) = g(p i)"
   (ASM_MESON_TAC [LAMBDA_BETA, PERMUTES_IN_IMAGE, IN_NUMSEG])

  let PRODUCT_PERMUTE ← prove
   r"!f p s. p permutes s ==> product s f = product s (f o p)"
   (REWRITE_TAC [product] THEN MATCH_MP_TAC ITERATE_PERMUTE THEN
    REWRITE_TAC [MONOIDAL_REAL_MUL])

  let PRODUCT_PERMUTE_NUMSEG ← prove
   r"!f p m n. p permutes m..n ==> product(m..n) f = product(m..n) (f o p)"
   (MESON_TAC [PRODUCT_PERMUTE, FINITE_NUMSEG])

  let REAL_MUL_SUM ← prove
   r"!s t f g.
        FINITE s /\ FINITE t
        ==> sum s f * sum t g = sum s (\i. sum t (\j. f(i) * g(j)))"
   (SIMP_TAC [SUM_LMUL] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN SIMP_TAC [SUM_LMUL])

  let REAL_MUL_SUM_NUMSEG ← prove
   r"!m n p q. sum(m..n) f * sum(p..q) g =
             sum(m..n) (\i. sum(p..q) (\j. f(i) * g(j)))"
   (SIMP_TAC [REAL_MUL_SUM, FINITE_NUMSEG])

  return { trace, TRACE_0, TRACE_I, TRACE_ADD, TRACE_SUB, TRACE_CMUL, TRACE_NEG,
           TRACE_MUL_SYM, TRACE_TRANSP, TRACE_SIMILAR, TRACE_MUL_CYCLIC, det,
           IN_DIMINDEX_SWAP, LAMBDA_BETA_PERM, PRODUCT_PERMUTE, PRODUCT_PERMUTE_NUMSEG,
           REAL_MUL_SUM, REAL_MUL_SUM_NUMSEG }

/- ------------------------------------------------------------------------- -/
/- Basic determinant properties.  (determinants.ml 114-348)                  -/
/- ------------------------------------------------------------------------- -/

structure DetBasic where
  DET_CMUL : thm
  DET_NEG : thm
  DET_TRANSP : thm
  DET_LOWERTRIANGULAR : thm
  DET_UPPERTRIANGULAR : thm
  DET_I : thm
  DET_0 : thm
  DET_PERMUTE_ROWS : thm
  DET_PERMUTE_COLUMNS : thm
  DET_IDENTICAL_ROWS : thm
  DET_IDENTICAL_COLUMNS : thm
  DET_ZERO_ROW : thm
  DET_ZERO_COLUMN : thm
  DET_ROW_ADD : thm
  DET_ROW_MUL : thm
  DET_ROW_OPERATION : thm
  DET_ROW_SPAN : thm
  deriving Inhabited

@[nospecialize]
def setupDetBasic [HolBase] (D : DeterminantsDeps) (BTrace : Trace) :
    ExceptT String IO DetBasic := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, REAL_ARITH, REAL_RING, VECTOR_ARITH, .. } := D
  let { CART_EQ, COND_ID, DIMINDEX_GE_1, EQ_TRANS, FINITE_DELETE, FINITE_NUMSEG,
        FINITE_RULES, FUN_EQ_THM, IMP_CONJ, INSERT_DELETE, IN_DELETE, IN_ELIM_THM,
        IN_NUMSEG, IN_SING, LAMBDA_BETA, .. } := D.core1
  let { LE_REFL, LT_REFL, NOT_LT, PRODUCT_CLAUSES, REAL_ADD_LDISTRIB, REAL_ENTIRE,
        REAL_MUL_AC, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_SYM, .. } := D.core2
  let { RIGHT_FORALL_IMP_THM, SUBSET, SUM_ADD, SUM_EQ, SUM_EQ_0, SUM_LMUL, SUM_SING,
        SUM_SUPERSET, o_THM, .. } := D.core3
  let { I_THM, .. } := D.core4
  let { MATRIX_CMUL_COMPONENT, .. } := D.vec1
  let { MATRIX_NEG_MINUS1, ROW_TRANSP, .. } := D.vec2
  let { SPAN_INDUCT_ALT, VECTOR_ADD_COMPONENT, VECTOR_ADD_RID, VECTOR_MUL_COMPONENT,
        VEC_COMPONENT, mat, row, transp, .. } := D.vec3
  let { FINITE_PERMUTATIONS, PERMUTATION_PERMUTES, PERMUTES_I, PERMUTES_IMAGE,
        PERMUTES_INJECTIVE, PERMUTES_INVERSE, PERMUTES_INVERSES, PERMUTES_INVERSES_o,
        PERMUTES_IN_IMAGE, PERMUTES_IN_NUMSEG, PERMUTES_NUMSET_GE, PERMUTES_NUMSET_LE,
        PERMUTES_SWAP, PRODUCT_CONST_NUMSEG_1, PRODUCT_EQ, PRODUCT_EQ_0,
        PRODUCT_EQ_0_NUMSEG, PRODUCT_EQ_1_NUMSEG, PRODUCT_IMAGE, PRODUCT_MUL, SIGN_COMPOSE,
        SIGN_I, SIGN_INVERSE, SIGN_NZ, SIGN_SWAP, SUM_PERMUTATIONS_COMPOSE_R,
        SUM_PERMUTATIONS_INVERSE, swap, .. } := D.lib
  let { LAMBDA_BETA_PERM, PRODUCT_PERMUTE_NUMSEG, det, .. } := BTrace
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let DET_CMUL ← prove
   r"!A:real^N^N c. det(c %% A) = c pow dimindex(:N) * det A"
   (REPEAT GEN_TAC THEN
    SIMP_TAC [det, MATRIX_CMUL_COMPONENT, PRODUCT_MUL, FINITE_NUMSEG] THEN
    SIMP_TAC [PRODUCT_CONST_NUMSEG_1, ← GSYM SUM_LMUL] THEN
    REWRITE_TAC [REAL_MUL_AC])

  let DET_NEG ← prove
   r"!A:real^N^N. det(--A) = --(&1) pow dimindex(:N) * det A"
   (REWRITE_TAC [MATRIX_NEG_MINUS1, DET_CMUL])

  let DET_TRANSP ← prove
   r"!A:real^N^N. det(transp A) = det A"
   (GEN_TAC THEN REWRITE_TAC [det] THEN
    GEN_REWRITE_TAC LAND_CONV [SUM_PERMUTATIONS_INVERSE] THEN
    MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC [FINITE_PERMUTATIONS, FINITE_NUMSEG] THEN X_GEN_TAC (← q r"p:num->num") THEN
    REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN BINOP_TAC THENL
     [ASM_MESON_TAC [SIGN_INVERSE, PERMUTATION_PERMUTES, FINITE_NUMSEG],
      ALL_TAC] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
        [← GSYM (← MATCH_MP PERMUTES_IMAGE th)])) THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     (← q r"product(1..dimindex(:N))
       ((\i. (transp A:real^N^N)$i$inverse p(i)) o p)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_IMAGE THEN
      ASM_MESON_TAC [FINITE_NUMSEG, PERMUTES_INJECTIVE, PERMUTES_INVERSE],
      MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
      SIMP_TAC [transp, LAMBDA_BETA, o_THM] THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
      SIMP_TAC [FUN_EQ_THM, I_THM, o_THM] THEN STRIP_TAC THEN
      ASM_SIMP_TAC [PERMUTES_IN_NUMSEG, LAMBDA_BETA_PERM, LAMBDA_BETA]])

  let DET_LOWERTRIANGULAR ← prove
   r"!A:real^N^N.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N) /\ i < j ==> A$i$j = &0)
        ==> det(A) = product(1..dimindex(:N)) (\i. A$i$i)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [det] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"sum {I}
     (\p. sign p * product(1..dimindex(:N)) (\i. (A:real^N^N)$i$p(i)))") THEN
    CONJ_TAC THENL
     [ALL_TAC, REWRITE_TAC [SUM_SING, SIGN_I, REAL_MUL_LID, I_THM]] THEN
    MATCH_MP_TAC SUM_SUPERSET THEN
    SIMP_TAC [IN_SING, FINITE_RULES, SUBSET, IN_ELIM_THM, PERMUTES_I] THEN
    X_GEN_TAC (← q r"p:num->num") THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [PRODUCT_EQ_0_NUMSEG, REAL_ENTIRE, SIGN_NZ] THEN
    MP_TAC (← SPECL [← q r"p:num->num", ← q r"1..dimindex(:N)"] PERMUTES_NUMSET_LE) THEN
    ASM_MESON_TAC [PERMUTES_IN_IMAGE, IN_NUMSEG, NOT_LT])

  let DET_UPPERTRIANGULAR ← prove
   r"!A:real^N^N.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N) /\ j < i ==> A$i$j = &0)
        ==> det(A) = product(1..dimindex(:N)) (\i. A$i$i)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [det] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"sum {I}
     (\p. sign p * product(1..dimindex(:N)) (\i. (A:real^N^N)$i$p(i)))") THEN
    CONJ_TAC THENL
     [ALL_TAC, REWRITE_TAC [SUM_SING, SIGN_I, REAL_MUL_LID, I_THM]] THEN
    MATCH_MP_TAC SUM_SUPERSET THEN
    SIMP_TAC [IN_SING, FINITE_RULES, SUBSET, IN_ELIM_THM, PERMUTES_I] THEN
    X_GEN_TAC (← q r"p:num->num") THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [PRODUCT_EQ_0_NUMSEG, REAL_ENTIRE, SIGN_NZ] THEN
    MP_TAC (← SPECL [← q r"p:num->num", ← q r"1..dimindex(:N)"] PERMUTES_NUMSET_GE) THEN
    ASM_MESON_TAC [PERMUTES_IN_IMAGE, IN_NUMSEG, NOT_LT])

  let DET_I ← prove
   r"det(mat 1 :real^N^N) = &1"
   (MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"product(1..dimindex(:N)) (\i. (mat 1:real^N^N)$i$i)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DET_LOWERTRIANGULAR,
      MATCH_MP_TAC PRODUCT_EQ_1_NUMSEG] THEN
    SIMP_TAC [mat, LAMBDA_BETA] THEN MESON_TAC [LT_REFL])

  let DET_0 ← prove
   r"det(mat 0 :real^N^N) = &0"
   (MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"product(1..dimindex(:N)) (\i. (mat 0:real^N^N)$i$i)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DET_LOWERTRIANGULAR,
      REWRITE_TAC [PRODUCT_EQ_0_NUMSEG] THEN EXISTS_TAC (← q r"1")] THEN
    SIMP_TAC [mat, LAMBDA_BETA, COND_ID, DIMINDEX_GE_1, LE_REFL])

  let DET_PERMUTE_ROWS ← prove
   r"!A:real^N^N p.
        p permutes 1..dimindex(:N)
        ==> det(lambda i. A$p(i)) = sign(p) * det(A)"
   (REWRITE_TAC [det] THEN SIMP_TAC [LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
    SIMP_TAC [← GSYM SUM_LMUL, FINITE_PERMUTATIONS, FINITE_NUMSEG] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (GEN_REWRITE_TAC LAND_CONV [← MATCH_MP SUM_PERMUTATIONS_COMPOSE_R th])) THEN
    MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC [FINITE_PERMUTATIONS, FINITE_NUMSEG] THEN X_GEN_TAC (← q r"q:num->num") THEN
    REWRITE_TAC [IN_ELIM_THM, REAL_MUL_ASSOC] THEN DISCH_TAC THEN BINOP_TAC THENL
     [ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      ASM_MESON_TAC [SIGN_COMPOSE, PERMUTATION_PERMUTES, FINITE_NUMSEG],
      ALL_TAC] THEN
    MP_TAC (← MATCH_MP PERMUTES_INVERSE (← ASSUME (← q r"p permutes 1..dimindex(:N)"))) THEN
    DISCH_THEN (fun th => tactic_of do
      pure (GEN_REWRITE_TAC LAND_CONV [← MATCH_MP PRODUCT_PERMUTE_NUMSEG th])) THEN
    MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC [IN_NUMSEG, FINITE_NUMSEG] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [o_THM] THEN
    ASM_MESON_TAC [PERMUTES_INVERSES])

  let DET_PERMUTE_COLUMNS ← prove
   r"!A:real^N^N p.
        p permutes 1..dimindex(:N)
        ==> det((lambda i j. A$i$p(j)):real^N^N) = sign(p) * det(A)"
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (funpow 2 RAND_CONV) [← GSYM DET_TRANSP] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (ONCE_REWRITE_TAC [← GSYM (← MATCH_MP DET_PERMUTE_ROWS th)])) THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM DET_TRANSP] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC [CART_EQ, transp, LAMBDA_BETA, LAMBDA_BETA_PERM])

  let DET_IDENTICAL_ROWS ← prove
   r"!A:real^N^N i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N) /\ ~(i = j) /\
                    row i A = row j A
                    ==> det A = &0"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"A:real^N^N", ← q r"swap(i:num,j:num)"] DET_PERMUTE_ROWS) THEN
    ASM_SIMP_TAC [PERMUTES_SWAP, IN_NUMSEG, SIGN_SWAP] THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"a = b ==> b = -- &1 * a ==> a = &0")) THEN
    AP_TERM_TAC THEN FIRST_X_ASSUM (MP_TAC o SYM) THEN
    SIMP_TAC [row, CART_EQ, LAMBDA_BETA] THEN
    REWRITE_TAC [swap] THEN ASM_MESON_TAC [])

  let DET_IDENTICAL_COLUMNS ← prove
   r"!A:real^N^N i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N) /\ ~(i = j) /\
                    column i A = column j A
                    ==> det A = &0"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM DET_TRANSP] THEN
    MATCH_MP_TAC DET_IDENTICAL_ROWS THEN ASM_MESON_TAC [ROW_TRANSP])

  let DET_ZERO_ROW ← prove
   r"!A:real^N^N i.
       1 <= i /\ i <= dimindex(:N) /\ row i A = vec 0  ==> det A = &0"
   (SIMP_TAC [det, row, CART_EQ, LAMBDA_BETA, VEC_COMPONENT] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_0 THEN
    REWRITE_TAC [IN_ELIM_THM, REAL_ENTIRE, SIGN_NZ] THEN REPEAT STRIP_TAC THEN
    SIMP_TAC [PRODUCT_EQ_0, FINITE_NUMSEG, IN_NUMSEG] THEN
    ASM_MESON_TAC [PERMUTES_IN_IMAGE, IN_NUMSEG])

  let DET_ZERO_COLUMN ← prove
   r"!A:real^N^N i.
       1 <= i /\ i <= dimindex(:N) /\ column i A = vec 0  ==> det A = &0"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM DET_TRANSP] THEN
    MATCH_MP_TAC DET_ZERO_ROW THEN ASM_MESON_TAC [ROW_TRANSP])

  let DET_ROW_ADD ← prove
   r"!a b c k.
         1 <= k /\ k <= dimindex(:N)
         ==> det((lambda i. if i = k then a + b else c i):real^N^N) =
             det((lambda i. if i = k then a else c i):real^N^N) +
             det((lambda i. if i = k then b else c i):real^N^N)"
   (SIMP_TAC [det, LAMBDA_BETA, ← GSYM SUM_ADD,
              FINITE_PERMUTATIONS, FINITE_NUMSEG] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC [FINITE_PERMUTATIONS, FINITE_NUMSEG] THEN
    X_GEN_TAC (← q r"p:num->num") THEN REWRITE_TAC [IN_ELIM_THM] THEN
    DISCH_TAC THEN REWRITE_TAC [← GSYM REAL_ADD_LDISTRIB] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN (← q r"1..dimindex(:N) = k INSERT ((1..dimindex(:N)) DELETE k)")
    SUBST1_TAC THENL [ASM_MESON_TAC [INSERT_DELETE, IN_NUMSEG], ALL_TAC] THEN
    SIMP_TAC [PRODUCT_CLAUSES, FINITE_DELETE, FINITE_NUMSEG, IN_DELETE] THEN
    MATCH_MP_TAC (← REAL_RING (← q
     r"c = a + b /\ y = x:real /\ z = x ==> c * x = a * y + b * z")) THEN
    REWRITE_TAC [VECTOR_ADD_COMPONENT] THEN
    CONJ_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
    SIMP_TAC [IN_DELETE, FINITE_DELETE, FINITE_NUMSEG])

  let DET_ROW_MUL ← prove
   r"!a b c k.
        1 <= k /\ k <= dimindex(:N)
        ==> det((lambda i. if i = k then c % a else b i):real^N^N) =
            c * det((lambda i. if i = k then a else b i):real^N^N)"
   (SIMP_TAC [det, LAMBDA_BETA, ← GSYM SUM_LMUL,
              FINITE_PERMUTATIONS, FINITE_NUMSEG] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC [FINITE_PERMUTATIONS, FINITE_NUMSEG] THEN
    X_GEN_TAC (← q r"p:num->num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"1..dimindex(:N) = k INSERT ((1..dimindex(:N)) DELETE k)")
    SUBST1_TAC THENL [ASM_MESON_TAC [INSERT_DELETE, IN_NUMSEG], ALL_TAC] THEN
    SIMP_TAC [PRODUCT_CLAUSES, FINITE_DELETE, FINITE_NUMSEG, IN_DELETE] THEN
    MATCH_MP_TAC (← REAL_RING (← q
     r"cp = c * p /\ p1 = p2:real ==> s * cp * p1 = c * s * p * p2")) THEN
    REWRITE_TAC [VECTOR_MUL_COMPONENT] THEN MATCH_MP_TAC PRODUCT_EQ THEN
    SIMP_TAC [IN_DELETE, FINITE_DELETE, FINITE_NUMSEG])

  let DET_ROW_OPERATION ← prove
   r"!A:real^N^N i.
        1 <= i /\ i <= dimindex(:N) /\
        1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
        ==> det(lambda k. if k = i then row i A + c % row j A else row k A) =
            det A"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [DET_ROW_ADD, DET_ROW_MUL] THEN
    MATCH_MP_TAC (← REAL_RING (← q r"a = b /\ d = &0 ==> a + c * d = b")) THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN ASM_SIMP_TAC [LAMBDA_BETA, CART_EQ] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC [row, LAMBDA_BETA, CART_EQ],
      MATCH_MP_TAC DET_IDENTICAL_ROWS THEN
      MAP_EVERY EXISTS_TAC [← q r"i:num", ← q r"j:num"] THEN
      ASM_SIMP_TAC [row, LAMBDA_BETA, CART_EQ]])

  let DET_ROW_SPAN ← prove
   r"!A:real^N^N i x.
        1 <= i /\ i <= dimindex(:N) /\
        x IN span {row j A | 1 <= j /\ j <= dimindex(:N) /\ ~(j = i)}
        ==> det(lambda k. if k = i then row i A + x else row k A) =
            det A"
   (GEN_TAC THEN GEN_TAC THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC SPAN_INDUCT_ALT THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN SIMP_TAC [CART_EQ, LAMBDA_BETA, VECTOR_ADD_RID] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [row, LAMBDA_BETA],
      ALL_TAC] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"j:num")) (SUBST_ALL_TAC o SYM)) THEN
    ONCE_REWRITE_TAC [← va
       r"a + c % x + y:real^N = (a + y) + c % x"] THEN
    ABBREV_TAC (← q r"z = row i (A:real^N^N) + y") THEN
    ASM_SIMP_TAC [DET_ROW_MUL, DET_ROW_ADD] THEN
    MATCH_MP_TAC (← REAL_RING (← q r"d = &0 ==> a + c * d = a")) THEN
    MATCH_MP_TAC DET_IDENTICAL_ROWS THEN
    MAP_EVERY EXISTS_TAC [← q r"i:num", ← q r"j:num"] THEN
    ASM_SIMP_TAC [row, LAMBDA_BETA, CART_EQ])

  return { DET_CMUL, DET_NEG, DET_TRANSP, DET_LOWERTRIANGULAR, DET_UPPERTRIANGULAR, DET_I,
           DET_0, DET_PERMUTE_ROWS, DET_PERMUTE_COLUMNS, DET_IDENTICAL_ROWS,
           DET_IDENTICAL_COLUMNS, DET_ZERO_ROW, DET_ZERO_COLUMN, DET_ROW_ADD, DET_ROW_MUL,
           DET_ROW_OPERATION, DET_ROW_SPAN }

/- ------------------------------------------------------------------------- -/
/- Dependent rows and columns; multilinearity and the multiplication        -/
/- formula.  (determinants.ml 354-608)                                       -/
/- ------------------------------------------------------------------------- -/

structure Multilinear where
  DET_DEPENDENT_ROWS : thm
  DET_DEPENDENT_COLUMNS : thm
  DET_LINEAR_ROW_VSUM : thm
  BOUNDED_FUNCTIONS_BIJECTIONS_1 : thm
  BOUNDED_FUNCTIONS_BIJECTIONS_2 : thm
  FINITE_BOUNDED_FUNCTIONS : thm
  DET_LINEAR_ROWS_VSUM_LEMMA : thm
  DET_LINEAR_ROWS_VSUM : thm
  MATRIX_MUL_VSUM_ALT : thm
  DET_ROWS_MUL : thm
  DET_MUL : thm
  DET_LINEAR_ROWS : thm
  deriving Inhabited

@[nospecialize]
def setupMultilinear [HolBase] (D : DeterminantsDeps) (BTrace : Trace)
    (BDetBasic : DetBasic) : ExceptT String IO Multilinear := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, GEN_BETA_CONV, INDUCT_TAC, MESON_TAC,
        REAL_ARITH_TAC, REAL_RING, SET_RULE, .. } := D
  let { ARITH, CART_EQ, CONJ_SYM, EQ_TRANS, EXTENSION, FINITE_IMAGE, FINITE_INDUCT_STRONG,
        FINITE_NUMSEG, FINITE_PRODUCT, FINITE_RULES, FORALL_IN_IMAGE, FUN_EQ_THM, IMP_CONJ,
        IN, IN_DELETE, IN_ELIM_PAIR_THM, IN_ELIM_THM, IN_IMAGE, IN_NUMSEG, LAMBDA_BETA, LE,
        LEFT_IMP_EXISTS_THM, LE_0, .. } := D.core1
  let { LE_REFL, MONO_EXISTS, NOT_FORALL_THM, NOT_IMP, REAL_ENTIRE, REAL_MUL_AC,
        REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_SYM, .. } := D.core2
  let { RIGHT_FORALL_IMP_THM, SUBSET, SUM_CLAUSES, SUM_EQ, SUM_EQ_GENERAL_INVERSES,
        SUM_LMUL, SUM_SING, SUM_SUM_PRODUCT, SUM_SUPERSET, SURJECTIVE_IFF_INJECTIVE, o_THM,
        .. } := D.core3
  let { FORALL_PAIR_THM, LEFT_AND_EXISTS_THM, PAIR_EQ, .. } := D.core4
  let { MATRIX_WORKS, ROWS_TRANSP, .. } := D.vec2
  let { SPAN_NEG, VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, VECTOR_NEG_COMPONENT,
        VEC_COMPONENT, VSUM_CLAUSES, VSUM_COMPONENT, dependent, matrix_mul,
        matrix_vector_mul, row, rows, transp, .. } := D.vec3
  let { FINITE_PERMUTATIONS, PERMUTATION_PERMUTES, PERMUTES_INVERSE, PERMUTES_INVERSES,
        PERMUTES_IN_IMAGE, PRODUCT_EQ_NUMSEG, PRODUCT_MUL, PRODUCT_MUL_NUMSEG, SIGN_COMPOSE,
        SIGN_IDEMPOTENT, SIGN_INVERSE, SUM_PERMUTATIONS_COMPOSE_R, permutes, .. } := D.lib
  let { LAMBDA_BETA_PERM, PRODUCT_PERMUTE_NUMSEG, REAL_MUL_SUM, det, .. } := BTrace
  let { DET_IDENTICAL_ROWS, DET_ROW_ADD, DET_ROW_SPAN, DET_TRANSP, DET_ZERO_ROW,
        .. } := BDetBasic
  -- @@SCOPE END

  let DET_DEPENDENT_ROWS ← prove
   r"!A:real^N^N. dependent(rows A) ==> det A = &0"
   (GEN_TAC THEN
    REWRITE_TAC [dependent, rows, IN_ELIM_THM, LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN GEN_TAC THEN X_GEN_TAC (← q r"i:num") THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_CASES_TAC
     (← q r"?i j. 1 <= i /\ i <= dimindex(:N) /\
          1 <= j /\ j <= dimindex(:N) /\ ~(i = j) /\
          row i (A:real^N^N) = row j A")
    THENL [ASM_MESON_TAC [DET_IDENTICAL_ROWS], ALL_TAC] THEN
    MP_TAC (← SPECL [← q r"A:real^N^N", ← q r"i:num", ← q r"--(row i (A:real^N^N))"]
      DET_ROW_SPAN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SPAN_NEG THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [IN]) THEN
      MATCH_MP_TAC (← TAUT (← q r"a = b ==> a ==> b")) THEN
      REWRITE_TAC [IN] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [EXTENSION, IN_DELETE, IN_ELIM_THM] THEN ASM_MESON_TAC [],
      DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC DET_ZERO_ROW THEN
      EXISTS_TAC (← q r"i:num") THEN
      ASM_SIMP_TAC [row, LAMBDA_BETA, CART_EQ, VECTOR_ADD_COMPONENT,
                    VECTOR_NEG_COMPONENT, VEC_COMPONENT] THEN
      REAL_ARITH_TAC])

  let DET_DEPENDENT_COLUMNS ← prove
   r"!A:real^N^N. dependent(columns A) ==> det A = &0"
   (MESON_TAC [DET_DEPENDENT_ROWS, ROWS_TRANSP, DET_TRANSP])

  let DET_LINEAR_ROW_VSUM ← prove
   r"!a c s k.
         FINITE s /\ 1 <= k /\ k <= dimindex(:N)
         ==> det((lambda i. if i = k then vsum s a else c i):real^N^N) =
             sum s
               (\j. det((lambda i. if i = k then a(j) else c i):real^N^N))"
   (GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC [IMP_CONJ] THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [VSUM_CLAUSES, SUM_CLAUSES, DET_ROW_ADD] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC DET_ZERO_ROW THEN EXISTS_TAC (← q r"k:num") THEN
    ASM_SIMP_TAC [row, LAMBDA_BETA, CART_EQ, VEC_COMPONENT])

  let BOUNDED_FUNCTIONS_BIJECTIONS_1 ← prove
   r"!p. p IN {(y,g) | y IN s /\
                     g IN {f | (!i. 1 <= i /\ i <= k ==> f i IN s) /\
                               (!i. ~(1 <= i /\ i <= k) ==> f i = i)}}
       ==> (\(y,g) i. if i = SUC k then y else g(i)) p IN
             {f | (!i. 1 <= i /\ i <= SUC k ==> f i IN s) /\
                  (!i. ~(1 <= i /\ i <= SUC k) ==> f i = i)} /\
           (\h. h(SUC k),(\i. if i = SUC k then i else h(i)))
            ((\(y,g) i. if i = SUC k then y else g(i)) p) = p"
   (REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
    CONV_TAC (REDEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC [IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"y:num", ← q r"h:num->num"] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC [LE],
      ASM_MESON_TAC [LE, ← ARITH_RULE (← q r"~(1 <= i /\ i <= SUC k) ==> ~(i = SUC k)")],
      REWRITE_TAC [PAIR_EQ, FUN_EQ_THM] THEN
      ASM_MESON_TAC [← ARITH_RULE (← q r"~(SUC k <= k)")]])

  let BOUNDED_FUNCTIONS_BIJECTIONS_2 ← prove
   r"!h. h IN {f | (!i. 1 <= i /\ i <= SUC k ==> f i IN s) /\
                 (!i. ~(1 <= i /\ i <= SUC k) ==> f i = i)}
       ==> (\h. h(SUC k),(\i. if i = SUC k then i else h(i))) h IN
           {(y,g) | y IN s /\
                     g IN {f | (!i. 1 <= i /\ i <= k ==> f i IN s) /\
                               (!i. ~(1 <= i /\ i <= k) ==> f i = i)}} /\
           (\(y,g) i. if i = SUC k then y else g(i))
              ((\h. h(SUC k),(\i. if i = SUC k then i else h(i))) h) = h"
   (REWRITE_TAC [IN_ELIM_PAIR_THM] THEN
    CONV_TAC (REDEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC [IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"h:num->num") THEN REPEAT STRIP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC,
      ASM_MESON_TAC [← ARITH_RULE (← q r"i <= k ==> i <= SUC k /\ ~(i = SUC k)")],
      ASM_MESON_TAC [← ARITH_RULE (← q r"i <= SUC k /\ ~(i = SUC k) ==> i <= k")],
      REWRITE_TAC [FUN_EQ_THM] THEN ASM_MESON_TAC [LE_REFL]])

  let FINITE_BOUNDED_FUNCTIONS ← prove
   r"!s k. FINITE s
         ==> FINITE {f | (!i. 1 <= i /\ i <= k ==> f(i) IN s) /\
                         (!i. ~(1 <= i /\ i <= k) ==> f(i) = i)}"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    INDUCT_TAC THENL
     [REWRITE_TAC [← ARITH_RULE (← q r"~(1 <= i /\ i <= 0)")] THEN
      SIMP_TAC [← GSYM FUN_EQ_THM, ← SET_RULE (← q r"{x | x = y} = {y}"), FINITE_RULES],
      ALL_TAC] THEN
    UNDISCH_TAC (← q r"FINITE(s:num->bool)") THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC [← TAUT (← q r"a ==> b ==> c <=> b /\ a ==> c")] THEN
    DISCH_THEN (MP_TAC o MATCH_MP FINITE_PRODUCT) THEN
    DISCH_THEN (MP_TAC o ISPEC (← q r"\(y:num,g) i. if i = SUC k then y else g(i)") o
                        MATCH_MP FINITE_IMAGE) THEN
    MATCH_MP_TAC (← TAUT (← q r"a = b ==> a ==> b")) THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, IN_IMAGE] THEN
    X_GEN_TAC (← q r"h:num->num") THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_SIMP_TAC [BOUNDED_FUNCTIONS_BIJECTIONS_1], ALL_TAC] THEN
    DISCH_TAC THEN EXISTS_TAC
      (← q r"(\h. h(SUC k),(\i. if i = SUC k then i else h(i))) h") THEN
    PURE_ONCE_REWRITE_TAC [CONJ_SYM] THEN CONV_TAC (RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC BOUNDED_FUNCTIONS_BIJECTIONS_2 THEN ASM_REWRITE_TAC [])

  let DET_LINEAR_ROWS_VSUM_LEMMA ← do
    let lemma ← prove
     r"(lambda i. if i <= 0 then x(i) else y(i)) = (lambda i. y i)"
     (SIMP_TAC [CART_EQ, ARITH, LAMBDA_BETA, ← ARITH_RULE (← q
                   r"1 <= k ==> ~(k <= 0)")])
    prove
     r"!s k a c.
         FINITE s /\ k <= dimindex(:N)
         ==> det((lambda i. if i <= k then vsum s (a i) else c i):real^N^N) =
             sum {f | (!i. 1 <= i /\ i <= k ==> f(i) IN s) /\
                      !i. ~(1 <= i /\ i <= k) ==> f(i) = i}
                 (\f. det((lambda i. if i <= k then a i (f i) else c i)
                          :real^N^N))"
     (ONCE_REWRITE_TAC [IMP_CONJ] THEN
      REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
      INDUCT_TAC THENL
       [REWRITE_TAC [lemma, LE_0] THEN GEN_TAC THEN
        REWRITE_TAC [← ARITH_RULE (← q r"~(1 <= i /\ i <= 0)")] THEN
        REWRITE_TAC [← GSYM FUN_EQ_THM, ← SET_RULE (← q r"{x | x = y} = {y}")] THEN
        REWRITE_TAC [SUM_SING],
        ALL_TAC] THEN
      DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o check (HolCore.Basics.is_imp o concl)) THEN
      ASM_SIMP_TAC [← ARITH_RULE (← q r"SUC k <= n ==> k <= n")] THEN REPEAT STRIP_TAC THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [LE] THEN
      REWRITE_TAC [← TAUT (← q
       r"(if a \/ b then c else d) = (if a then c else if b then c else d)")] THEN
      ASM_SIMP_TAC [DET_LINEAR_ROW_VSUM, ← ARITH_RULE (← q r"1 <= SUC k")] THEN
      ONCE_REWRITE_TAC [← TAUT (← q
        r"(if a then b else if c then d else e) =
     (if c then (if a then b else d) else (if a then b else e))")] THEN
      ASM_SIMP_TAC [← ARITH_RULE (← q r"i <= k ==> ~(i = SUC k)")] THEN
      ASM_SIMP_TAC [SUM_SUM_PRODUCT, FINITE_BOUNDED_FUNCTIONS] THEN
      MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
      EXISTS_TAC (← q r"\(y:num,g) i. if i = SUC k then y else g(i)") THEN
      EXISTS_TAC (← q r"\h. h(SUC k),(\i. if i = SUC k then i else h(i))") THEN
      CONJ_TAC THENL [ACCEPT_TAC BOUNDED_FUNCTIONS_BIJECTIONS_2, ALL_TAC] THEN
      X_GEN_TAC (← q r"p:num#(num->num)") THEN
      DISCH_THEN (STRIP_ASSUME_TAC o MATCH_MP BOUNDED_FUNCTIONS_BIJECTIONS_1) THEN
      ASM_REWRITE_TAC [] THEN
      SPEC_TAC (← q r"p:num#(num->num)", ← q r"q:num#(num->num)") THEN
      REWRITE_TAC [FORALL_PAIR_THM] THEN
      CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      MAP_EVERY X_GEN_TAC [← q r"y:num", ← q r"g:num->num"] THEN AP_TERM_TAC THEN
      SIMP_TAC [CART_EQ, LAMBDA_BETA] THEN
      REPEAT STRIP_TAC THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
      ASM_MESON_TAC [LE, ← ARITH_RULE (← q r"~(SUC k <= k)")])

  let DET_LINEAR_ROWS_VSUM ← do
    let lemma ← prove
     r"(lambda i. if i <= dimindex(:N) then x(i) else y(i)):real^N^N =
     (lambda i. x(i))"
     (SIMP_TAC [CART_EQ, LAMBDA_BETA])
    prove
     r"!s a.
         FINITE s
         ==> det((lambda i. vsum s (a i)):real^N^N) =
             sum {f | (!i. 1 <= i /\ i <= dimindex(:N) ==> f(i) IN s) /\
                      !i. ~(1 <= i /\ i <= dimindex(:N)) ==> f(i) = i}
                 (\f. det((lambda i. a i (f i)):real^N^N))"
     (REPEAT STRIP_TAC THEN
      MP_TAC (← SPECL [← q r"s:num->bool", ← q r"dimindex(:N)"]
        DET_LINEAR_ROWS_VSUM_LEMMA) THEN
      ASM_REWRITE_TAC [LE_REFL, lemma] THEN SIMP_TAC [])

  let MATRIX_MUL_VSUM_ALT ← prove
   r"!A:real^N^N B:real^N^N. A ** B =
                  lambda i. vsum (1..dimindex(:N)) (\k. A$i$k % B$k)"
   (SIMP_TAC [matrix_mul, CART_EQ, LAMBDA_BETA, VECTOR_MUL_COMPONENT,
              VSUM_COMPONENT])

  let DET_ROWS_MUL ← prove
   r"!a c. det((lambda i. c(i) % a(i)):real^N^N) =
         product(1..dimindex(:N)) (\i. c(i)) *
         det((lambda i. a(i)):real^N^N)"
   (REPEAT GEN_TAC THEN SIMP_TAC [det, LAMBDA_BETA] THEN
    SIMP_TAC [← GSYM SUM_LMUL, FINITE_PERMUTATIONS, FINITE_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ THEN SIMP_TAC [FINITE_PERMUTATIONS, FINITE_NUMSEG] THEN
    X_GEN_TAC (← q r"p:num->num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC (← REAL_RING (← q r"b = c * d ==> s * b = c * s * d")) THEN
    SIMP_TAC [← GSYM PRODUCT_MUL_NUMSEG] THEN
    MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
    ASM_MESON_TAC [PERMUTES_IN_IMAGE, IN_NUMSEG, VECTOR_MUL_COMPONENT])

  let DET_MUL ← prove
   r"!A B:real^N^N. det(A ** B) = det(A) * det(B)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [MATRIX_MUL_VSUM_ALT] THEN
    SIMP_TAC [DET_LINEAR_ROWS_VSUM, FINITE_NUMSEG] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"sum {p | p permutes 1..dimindex(:N)}
            (\f. det (lambda i. (A:real^N^N)$i$f i % (B:real^N^N)$f i))") THEN
    CONJ_TAC THENL
     [REWRITE_TAC [DET_ROWS_MUL] THEN
      MATCH_MP_TAC SUM_SUPERSET THEN
      SIMP_TAC [FINITE_PERMUTATIONS, FINITE_NUMSEG] THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN CONJ_TAC THENL
       [MESON_TAC [permutes, IN_NUMSEG], ALL_TAC] THEN
      X_GEN_TAC (← q r"f:num->num") THEN REWRITE_TAC [permutes, IN_NUMSEG] THEN
      DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
      REWRITE_TAC [REAL_ENTIRE] THEN DISJ2_TAC THEN
      MATCH_MP_TAC DET_IDENTICAL_ROWS THEN
      MP_TAC (← ISPECL [← q r"1..dimindex(:N)", ← q r"f:num->num"]
         SURJECTIVE_IFF_INJECTIVE) THEN
      ASM_REWRITE_TAC [SUBSET, IN_NUMSEG, FINITE_NUMSEG, FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC (← TAUT (← q r"(~b ==> c) /\ (b ==> ~a) ==> (a <=> b) ==> c")) THEN
      CONJ_TAC THENL
       [REWRITE_TAC [NOT_FORALL_THM] THEN
        REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
        SIMP_TAC [CART_EQ, LAMBDA_BETA, row, NOT_IMP],
        ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN (← q r"!x y. (f:num->num)(x) = f(y) ==> x = y") ASSUME_TAC THENL
       [REPEAT GEN_TAC THEN
        ASM_CASES_TAC (← q r"1 <= x /\ x <= dimindex(:N)") THEN
        ASM_CASES_TAC (← q r"1 <= y /\ y <= dimindex(:N)") THEN
        ASM_MESON_TAC [],
        ALL_TAC] THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    SIMP_TAC [det, REAL_MUL_SUM, FINITE_PERMUTATIONS, FINITE_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ THEN SIMP_TAC [FINITE_PERMUTATIONS, FINITE_NUMSEG] THEN
    X_GEN_TAC (← q r"p:num->num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (GEN_REWRITE_TAC RAND_CONV
        [← MATCH_MP SUM_PERMUTATIONS_COMPOSE_R (← MATCH_MP PERMUTES_INVERSE th)])) THEN
    MATCH_MP_TAC SUM_EQ THEN SIMP_TAC [FINITE_PERMUTATIONS, FINITE_NUMSEG] THEN
    X_GEN_TAC (← q r"q:num->num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN
    REWRITE_TAC [o_THM] THEN ONCE_REWRITE_TAC [← AC REAL_MUL_AC
     (← q r"(p * x) * (q * y) = (p * q) * (x * y)")] THEN
    BINOP_TAC THENL
     [SUBGOAL_THEN (← q r"sign(q o inverse p) = sign(p:num->num) * sign(q:num->num)")
       (fun t => SIMP_TAC [REAL_MUL_ASSOC, SIGN_IDEMPOTENT, REAL_MUL_LID, t]) THEN
      ASM_MESON_TAC [SIGN_COMPOSE, PERMUTES_INVERSE, PERMUTATION_PERMUTES,
                     FINITE_NUMSEG, SIGN_INVERSE, REAL_MUL_SYM],
      ALL_TAC] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
     [← MATCH_MP PRODUCT_PERMUTE_NUMSEG (← ASSUME (← q r"p permutes 1..dimindex(:N)"))] THEN
    SIMP_TAC [← GSYM PRODUCT_MUL, FINITE_NUMSEG] THEN
    MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
    ASM_SIMP_TAC [LAMBDA_BETA, LAMBDA_BETA_PERM, o_THM] THEN
    X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"(A:real^N^N)$i$p(i) * (B:real^N^N)$p(i)$q(i)") THEN CONJ_TAC THENL
     [ASM_MESON_TAC [VECTOR_MUL_COMPONENT, PERMUTES_IN_IMAGE, IN_NUMSEG],
      ASM_MESON_TAC [PERMUTES_INVERSES]])

  let DET_LINEAR_ROWS ← prove
   r"!f:real^N->real^N A:real^N^N.
        linear f ==> det(lambda i. f(A$i)) = det(matrix f) * det A"
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← GSYM DET_TRANSP] THEN
    REWRITE_TAC [← GSYM DET_MUL] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (REWRITE_TAC [← GSYM (← MATCH_MP MATRIX_WORKS th)])) THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM DET_TRANSP] THEN
    REWRITE_TAC [matrix_mul, matrix_vector_mul, transp] THEN
    AP_TERM_TAC THEN SIMP_TAC [CART_EQ, LAMBDA_BETA])

  return { DET_DEPENDENT_ROWS, DET_DEPENDENT_COLUMNS, DET_LINEAR_ROW_VSUM,
           BOUNDED_FUNCTIONS_BIJECTIONS_1, BOUNDED_FUNCTIONS_BIJECTIONS_2,
           FINITE_BOUNDED_FUNCTIONS, DET_LINEAR_ROWS_VSUM_LEMMA, DET_LINEAR_ROWS_VSUM,
           MATRIX_MUL_VSUM_ALT, DET_ROWS_MUL, DET_MUL, DET_LINEAR_ROWS }

/- ------------------------------------------------------------------------- -/
/- Relation to invertibility.  (determinants.ml 613-784)                     -/
/- ------------------------------------------------------------------------- -/

structure Invertibility where
  INVERTIBLE_DET_NZ : thm
  DET_EQ_0 : thm
  DET_MATRIX_INV : thm
  MATRIX_MUL_LINV : thm
  MATRIX_MUL_RINV : thm
  DET_MATRIX_EQ_0 : thm
  DET_MATRIX_EQ_0_LEFT : thm
  DET_MATRIX_EQ_0_RIGHT : thm
  DET_EQ_0_RANK : thm
  RANK_EQ_FULL_DET : thm
  INVERTIBLE_COVARIANCE_RANK : thm
  HOMOGENEOUS_LINEAR_EQUATIONS_DET : thm
  INVERTIBLE_MATRIX_MUL : thm
  MATRIX_INV_MUL : thm
  DET_SIMILAR : thm
  INVERTIBLE_NEARBY_ONORM : thm
  INVERTIBLE_NEARBY : thm
  deriving Inhabited

@[nospecialize]
def setupInvertibility [HolBase] (D : DeterminantsDeps) (BDetBasic : DetBasic)
    (BMultilinear : Multilinear) : ExceptT String IO Invertibility := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, MESON_TAC, REAL_FIELD, REAL_RING,
        VECTOR_ARITH, VECTOR_ARITH_TAC, .. } := D
  let { CART_EQ, FINITE_DELETE, FINITE_NUMSEG, IN_DELETE, IN_ELIM_THM, IN_NUMSEG,
        LAMBDA_BETA, LEFT_IMP_EXISTS_THM, .. } := D.core1
  let { LE_ANTISYM, NOT_FORALL_THM, NOT_IMP, NOT_LT, REAL_ENTIRE, REAL_INV_0,
        REAL_LE_RMUL_EQ, REAL_LTE_TRANS, REAL_LT_INV_EQ, REAL_LT_RDIV_EQ, REAL_MUL_LID,
        REAL_MUL_LINV, REAL_MUL_SYM, REAL_NOT_LE, .. } := D.core2
  let { o_DEF, real_div, .. } := D.core3
  let { CONTRAPOS_THM, DE_MORGAN_THM, RIGHT_AND_EXISTS_THM, .. } := D.core4
  let { FULL_RANK_INJECTIVE, INVERTIBLE_LEFT_INVERSE, INVERTIBLE_MAT, INVERTIBLE_MATRIX_INV,
        INVERTIBLE_RIGHT_INVERSE, LINEAR_INVERSE_LEFT, MATRIX_ADD_ASSOC, MATRIX_ADD_LID,
        MATRIX_ADD_RNEG, MATRIX_EQ_0, .. } := D.vec1
  let { MATRIX_INV, MATRIX_INVERTIBLE, MATRIX_INV_EQ_0, MATRIX_INV_UNIQUE,
        MATRIX_LEFT_INVERTIBLE_INJECTIVE, MATRIX_LEFT_INVERTIBLE_KER, MATRIX_MUL_ASSOC,
        MATRIX_MUL_LID, MATRIX_MUL_RID, MATRIX_NEG_ADD, MATRIX_NEG_NEG, MATRIX_NEG_SUB,
        MATRIX_NONFULL_LINEAR_EQUATIONS_EQ, MATRIX_RIGHT_INVERTIBLE_INDEPENDENT_ROWS,
        MATRIX_SUB, MATRIX_SUB_LDISTRIB, MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID,
        MATRIX_VECTOR_MUL_LINEAR, MATRIX_VECTOR_MUL_LNEG, MATRIX_VECTOR_MUL_SUB_RDISTRIB,
        NORM_POS_LT, ONORM, ONORM_COMPOSE, ONORM_NEG, ONORM_POS_LT, RANK_BOUND, RANK_GRAM,
        SPAN_CLAUSES, .. } := D.vec2
  let { SPAN_MUL, SPAN_VSUM, VECTOR_MUL_ASSOC, VECTOR_SUB_EQ, VEC_COMPONENT,
        VSUM_DELETE_CASES, VSUM_LMUL, row, .. } := D.vec3
  let { DET_I, DET_ROW_SPAN, DET_ZERO_ROW, .. } := BDetBasic
  let { DET_MUL, .. } := BMultilinear
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let INVERTIBLE_DET_NZ ← prove
   r"!A:real^N^N. invertible(A) <=> ~(det A = &0)"
   (GEN_TAC THEN EQ_TAC THENL
     [REWRITE_TAC [INVERTIBLE_RIGHT_INVERSE, LEFT_IMP_EXISTS_THM] THEN
      GEN_TAC THEN DISCH_THEN (MP_TAC o AP_TERM (← q r"det:real^N^N->real")) THEN
      REWRITE_TAC [DET_MUL, DET_I] THEN CONV_TAC (fun t => REAL_RING t),
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [INVERTIBLE_RIGHT_INVERSE] THEN
    REWRITE_TAC [MATRIX_RIGHT_INVERTIBLE_INDEPENDENT_ROWS] THEN
    REWRITE_TAC [NOT_FORALL_THM, NOT_IMP] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"c:num->real", ← q r"i:num"] THEN STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"A:real^N^N", ← q r"i:num", ← q r"--(row i (A:real^N^N))"]
      DET_ROW_SPAN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN
        (← q r"--(row i (A:real^N^N)) =
       vsum ((1..dimindex(:N)) DELETE i) (\j. inv(c i) % c j % row j A)")
      SUBST1_TAC THENL
       [ASM_SIMP_TAC [VSUM_DELETE_CASES, FINITE_NUMSEG, IN_NUMSEG, VSUM_LMUL] THEN
        ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV] THEN VECTOR_ARITH_TAC,
        ALL_TAC] THEN
      MATCH_MP_TAC SPAN_VSUM THEN
      REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG, FINITE_DELETE, IN_DELETE] THEN
      X_GEN_TAC (← q r"j:num") THEN STRIP_TAC THEN REPEAT (MATCH_MP_TAC SPAN_MUL) THEN
      MATCH_MP_TAC (← CONJUNCT1 SPAN_CLAUSES) THEN
      REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC DET_ZERO_ROW THEN
    EXISTS_TAC (← q r"i:num") THEN
    ASM_SIMP_TAC [row, CART_EQ, LAMBDA_BETA, VEC_COMPONENT,
                  ← va r"x + --x:real^N = vec 0"])

  let DET_EQ_0 ← prove
   r"!A:real^N^N. det(A) = &0 <=> ~invertible(A)"
   (REWRITE_TAC [INVERTIBLE_DET_NZ])

  let DET_MATRIX_INV ← prove
   r"!A:real^N^N. det(matrix_inv A) = inv(det A)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"invertible(A:real^N^N)") THENL
     [MATCH_MP_TAC (← REAL_FIELD (← q r"a * b = &1 ==> a = inv b")) THEN
      ASM_SIMP_TAC [← GSYM DET_MUL, MATRIX_INV, DET_I],
      ASM_MESON_TAC [DET_EQ_0, INVERTIBLE_MATRIX_INV, REAL_INV_0]])

  let MATRIX_MUL_LINV ← prove
   r"!A:real^N^N. ~(det A = &0) ==> matrix_inv A ** A = mat 1"
   (SIMP_TAC [MATRIX_INV, DET_EQ_0])

  let MATRIX_MUL_RINV ← prove
   r"!A:real^N^N. ~(det A = &0) ==> A ** matrix_inv A = mat 1"
   (SIMP_TAC [MATRIX_INV, DET_EQ_0])

  let DET_MATRIX_EQ_0 ← prove
   r"!f:real^N->real^N.
        linear f
        ==> (det(matrix f) = &0 <=>
             ~(?g. linear g /\ f o g = I /\ g o f = I))"
   (SIMP_TAC [DET_EQ_0, MATRIX_INVERTIBLE])

  let DET_MATRIX_EQ_0_LEFT ← prove
   r"!f:real^N->real^N.
        linear f
        ==> (det(matrix f) = &0 <=>
             ~(?g. linear g /\ g o f = I))"
   (SIMP_TAC [DET_MATRIX_EQ_0] THEN MESON_TAC [LINEAR_INVERSE_LEFT])

  let DET_MATRIX_EQ_0_RIGHT ← prove
   r"!f:real^N->real^N.
        linear f
        ==> (det(matrix f) = &0 <=>
             ~(?g. linear g /\ f o g = I))"
   (SIMP_TAC [DET_MATRIX_EQ_0] THEN MESON_TAC [LINEAR_INVERSE_LEFT])

  let DET_EQ_0_RANK ← prove
   r"!A:real^N^N. det A = &0 <=> rank A < dimindex(:N)"
   (REWRITE_TAC [DET_EQ_0, INVERTIBLE_LEFT_INVERSE, ← GSYM FULL_RANK_INJECTIVE,
                 MATRIX_LEFT_INVERTIBLE_INJECTIVE] THEN
    GEN_TAC THEN MP_TAC (← ISPEC (← q r"A:real^N^N") RANK_BOUND) THEN
    ARITH_TAC)

  let RANK_EQ_FULL_DET ← prove
   r"!A:real^N^N. rank A = dimindex(:N) <=> ~(det A = &0)"
   (GEN_TAC THEN MP_TAC (← ISPEC (← q r"A:real^N^N") RANK_BOUND) THEN
    SIMP_TAC [DET_EQ_0_RANK, NOT_LT, ← GSYM LE_ANTISYM,
              ← ARITH_RULE (← q r"MIN n n = n")])

  let INVERTIBLE_COVARIANCE_RANK ← prove
   r"!A:real^N^M. invertible(transp A ** A) <=> rank A = dimindex(:N)"
   (REWRITE_TAC [INVERTIBLE_DET_NZ, ← GSYM RANK_EQ_FULL_DET, RANK_GRAM])

  let HOMOGENEOUS_LINEAR_EQUATIONS_DET ← prove
   r"!A:real^N^N. (?x. ~(x = vec 0) /\ A ** x = vec 0) <=> det A = &0"
   (GEN_TAC THEN
    REWRITE_TAC [MATRIX_NONFULL_LINEAR_EQUATIONS_EQ, DET_EQ_0_RANK] THEN
    MATCH_MP_TAC (← ARITH_RULE (← q r"r <= MIN N N ==> (~(r = N) <=> r < N)")) THEN
    REWRITE_TAC [RANK_BOUND])

  let INVERTIBLE_MATRIX_MUL ← prove
   r"!A:real^N^N B:real^N^N.
        invertible(A ** B) <=> invertible A /\ invertible B"
   (REWRITE_TAC [INVERTIBLE_DET_NZ, DET_MUL, DE_MORGAN_THM, REAL_ENTIRE])

  let MATRIX_INV_MUL ← prove
   r"!A:real^N^N B:real^N^N.
        invertible A /\ invertible B
        ==> matrix_inv(A ** B) = matrix_inv B ** matrix_inv A"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE THEN
    ONCE_REWRITE_TAC [MATRIX_MUL_ASSOC] THEN
    GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o LAND_CONV)
     [← GSYM MATRIX_MUL_ASSOC] THEN
    ASM_SIMP_TAC [MATRIX_MUL_LINV, DET_EQ_0, MATRIX_MUL_RID, MATRIX_MUL_RINV])

  let DET_SIMILAR ← prove
   r"!S:real^N^N A. invertible S ==> det(matrix_inv S ** A ** S) = det A"
   (REWRITE_TAC [INVERTIBLE_DET_NZ, DET_MUL, DET_MATRIX_INV] THEN
    CONV_TAC (fun t => REAL_FIELD t))

  let INVERTIBLE_NEARBY_ONORM ← prove
   r"!A B:real^N^N.
        invertible A /\
        onorm(\x. (B - A) ** x) < inv(onorm(\x. matrix_inv A ** x))
        ==> invertible B"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [← GSYM ONORM_NEG] THEN
    REWRITE_TAC [← GSYM MATRIX_VECTOR_MUL_LNEG, MATRIX_NEG_SUB] THEN DISCH_TAC THEN
    ABBREV_TAC (← q r"S = matrix_inv(A:real^N^N) ** (A - B)") THEN
    SUBGOAL_THEN (← q r"B = (A:real^N^N) ** (mat 1 - S:real^N^N)") SUBST1_TAC THENL
     [EXPAND_TAC "S" THEN
      REWRITE_TAC [MATRIX_SUB_LDISTRIB, MATRIX_MUL_ASSOC] THEN
      ASM_SIMP_TAC [MATRIX_INV, MATRIX_MUL_RID, MATRIX_MUL_LID] THEN
      REWRITE_TAC [MATRIX_SUB, MATRIX_NEG_ADD] THEN
      REWRITE_TAC [MATRIX_ADD_RNEG, MATRIX_ADD_ASSOC, MATRIX_ADD_LID] THEN
      REWRITE_TAC [MATRIX_NEG_NEG],
      ASM_REWRITE_TAC [INVERTIBLE_MATRIX_MUL]] THEN
    REWRITE_TAC [INVERTIBLE_LEFT_INVERSE, MATRIX_LEFT_INVERTIBLE_KER] THEN
    X_GEN_TAC (← q r"x:real^N") THEN
    REWRITE_TAC [MATRIX_VECTOR_MUL_SUB_RDISTRIB, VECTOR_SUB_EQ] THEN
    CONV_TAC (LAND_CONV SYM_CONV) THEN REWRITE_TAC [MATRIX_VECTOR_MUL_LID] THEN
    DISCH_TAC THEN MATCH_MP_TAC (← TAUT (← q r"(~p ==> F) ==> p")) THEN DISCH_TAC THEN
    MP_TAC (← ISPECL
     [← q r"\x:real^N. matrix_inv(A:real^N^N) ** x",
      ← q r"\x:real^N. (A - B:real^N^N) ** x"]
     ONORM_COMPOSE) THEN
    ASM_SIMP_TAC [MATRIX_VECTOR_MUL_LINEAR, o_DEF, MATRIX_VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC [REAL_NOT_LE] THEN TRANS_TAC REAL_LTE_TRANS (← q r"&1") THEN
    CONJ_TAC THENL
      [ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
       W (MP_TAC o PART_MATCH (rand o rand) REAL_LT_RDIV_EQ o snd) THEN
       ASM_REWRITE_TAC [real_div, REAL_MUL_LID] THEN
       DISCH_THEN MATCH_MP_TAC THEN
       SIMP_TAC [ONORM_POS_LT, MATRIX_VECTOR_MUL_LINEAR] THEN
       REWRITE_TAC [← GSYM MATRIX_EQ_0, MATRIX_INV_EQ_0] THEN
       ASM_MESON_TAC [INVERTIBLE_MAT],
       MP_TAC (← ISPEC (← q r"\x:real^N. (S:real^N^N) ** x") ONORM) THEN
       REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR] THEN
       DISCH_THEN (MP_TAC o SPEC (← q r"x:real^N") o CONJUNCT1) THEN
       ASM_REWRITE_TAC [] THEN
       GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [← GSYM REAL_MUL_LID] THEN
       ASM_SIMP_TAC [REAL_LE_RMUL_EQ, NORM_POS_LT]])

  let INVERTIBLE_NEARBY ← prove
   r"!A:real^N^N.
        invertible A
        ==> ?e. &0 < e /\ !B. onorm(\x. (B - A) ** x) < e ==> invertible B"
   (REPEAT STRIP_TAC THEN
    EXISTS_TAC (← q r"inv(onorm(\x. matrix_inv(A:real^N^N) ** x))") THEN CONJ_TAC THENL
     [ALL_TAC, ASM_MESON_TAC [INVERTIBLE_NEARBY_ONORM]] THEN
    SIMP_TAC [REAL_LT_INV_EQ, ONORM_POS_LT, MATRIX_VECTOR_MUL_LINEAR] THEN
    REWRITE_TAC [← GSYM MATRIX_EQ_0, MATRIX_INV_EQ_0] THEN
    ASM_MESON_TAC [INVERTIBLE_MAT])

  return { INVERTIBLE_DET_NZ, DET_EQ_0, DET_MATRIX_INV, MATRIX_MUL_LINV, MATRIX_MUL_RINV,
           DET_MATRIX_EQ_0, DET_MATRIX_EQ_0_LEFT, DET_MATRIX_EQ_0_RIGHT, DET_EQ_0_RANK,
           RANK_EQ_FULL_DET, INVERTIBLE_COVARIANCE_RANK, HOMOGENEOUS_LINEAR_EQUATIONS_DET,
           INVERTIBLE_MATRIX_MUL, MATRIX_INV_MUL, DET_SIMILAR, INVERTIBLE_NEARBY_ONORM,
           INVERTIBLE_NEARBY }

/- ------------------------------------------------------------------------- -/
/- Cramer's rule, and its variants for matrix-matrix multiplication.        -/
/- (determinants.ml 786-917)                                                  -/
/- ------------------------------------------------------------------------- -/

structure Cramer where
  CRAMER_LEMMA_TRANSP : thm
  CRAMER_LEMMA : thm
  CRAMER : thm
  CRAMER_MATRIX_LEFT : thm
  CRAMER_MATRIX_RIGHT : thm
  CRAMER_MATRIX_RIGHT_INVERSE : thm
  CRAMER_MATRIX_LEFT_INVERSE : thm
  deriving Inhabited

@[nospecialize]
def setupCramer [HolBase] (D : DeterminantsDeps) (BDetBasic : DetBasic)
    (BMultilinear : Multilinear) (BInvertibility : Invertibility) :
    ExceptT String IO Cramer := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, REAL_ARITH_TAC, REAL_FIELD, REAL_RING,
        VECTOR_ARITH, .. } := D
  let { CART_EQ, FINITE_DELETE, FINITE_NUMSEG, INSERT_DELETE, IN_DELETE, IN_ELIM_THM,
        IN_NUMSEG, LAMBDA_BETA, .. } := D.core1
  let { RIGHT_FORALL_IMP_THM, SWAP_FORALL_THM, .. } := D.core3
  let { COND_COMPONENT, .. } := D.vec1
  let { MATRIX_MUL_COMPONENT, MATRIX_MUL_VSUM, MATRIX_TRANSP_MUL, MATRIX_VECTOR_MUL_ASSOC,
        MATRIX_VECTOR_MUL_LID, SPAN_CLAUSES, .. } := D.vec2
  let { SPAN_MUL, SPAN_VSUM, TRANSP_EQ, TRANSP_TRANSP, VECTOR_MUL_COMPONENT, VSUM_CLAUSES,
        VSUM_COMPONENT, column, invertible, mat, row, transp, .. } := D.vec3
  let { DET_I, DET_ROW_ADD, DET_ROW_MUL, DET_ROW_SPAN, DET_TRANSP, .. } := BDetBasic
  let { DET_MUL, .. } := BMultilinear
  let { INVERTIBLE_DET_NZ, .. } := BInvertibility
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let CRAMER_LEMMA_TRANSP ← prove
   r"!A:real^N^N x:real^N.
        1 <= k /\ k <= dimindex(:N)
        ==> det((lambda i. if i = k
                           then vsum(1..dimindex(:N)) (\i. x$i % row i A)
                           else row i A):real^N^N) =
            x$k * det A"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"1..dimindex(:N) = k INSERT ((1..dimindex(:N)) DELETE k)")
    SUBST1_TAC THENL [ASM_MESON_TAC [INSERT_DELETE, IN_NUMSEG], ALL_TAC] THEN
    SIMP_TAC [VSUM_CLAUSES, FINITE_NUMSEG, FINITE_DELETE, IN_DELETE] THEN
    REWRITE_TAC [← va
     r"(x:real^N)$k % row k (A:real^N^N) + s =
    (x$k - &1) % row k A + row k A + s"] THEN
    W (MP_TAC o PART_MATCH (lhs o rand) DET_ROW_ADD o lhand o snd) THEN
    ASM_SIMP_TAC [DET_ROW_MUL] THEN DISCH_THEN (K ALL_TAC) THEN
    MATCH_MP_TAC (← REAL_RING (← q r"d = d' /\ e = d' ==> (c - &1) * d + e = c * d'")) THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN ASM_SIMP_TAC [CART_EQ, LAMBDA_BETA] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [LAMBDA_BETA, row],
      MATCH_MP_TAC DET_ROW_SPAN THEN ASM_REWRITE_TAC [] THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SPAN_VSUM THEN
      REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG, FINITE_DELETE, IN_DELETE] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
      MATCH_MP_TAC (← CONJUNCT1 SPAN_CLAUSES) THEN
      REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC []])

  let CRAMER_LEMMA ← prove
   r"!A:real^N^N x:real^N.
        1 <= k /\ k <= dimindex(:N)
        ==> det((lambda i j. if j = k then (A**x)$i else A$i$j):real^N^N) =
            x$k * det(A)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [MATRIX_MUL_VSUM] THEN
    FIRST_ASSUM (MP_TAC o SYM o SPECL [← q r"transp(A:real^N^N)", ← q r"x:real^N"] o
                MATCH_MP CRAMER_LEMMA_TRANSP) THEN
    REWRITE_TAC [DET_TRANSP] THEN DISCH_THEN SUBST1_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM DET_TRANSP] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC [CART_EQ, transp, LAMBDA_BETA, MATRIX_MUL_VSUM, row, column,
          COND_COMPONENT, VECTOR_MUL_COMPONENT, VSUM_COMPONENT])

  let CRAMER ← prove
   r"!A:real^N^N x b.
        ~(det(A) = &0)
        ==> (A ** x = b <=>
             x = lambda k.
                   det((lambda i j. if j = k then b$i else A$i$j):real^N^N) /
                   det(A))"
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC (← MESON [] (← q
     r"(?x. p(x)) /\ (!x. p(x) ==> x = a) ==> !x. p(x) <=> x = a")) THEN
    CONJ_TAC THENL
     [MP_TAC (← SPEC (← q r"A:real^N^N") INVERTIBLE_DET_NZ) THEN
      ASM_MESON_TAC [invertible, MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID],
      GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC [CART_EQ, CRAMER_LEMMA, LAMBDA_BETA, ← REAL_FIELD (← q
      r"~(z = &0) ==> (x = y / z <=> x * z = y)")]])

  let CRAMER_MATRIX_LEFT ← prove
   r"!A:real^N^N X:real^N^N B:real^N^N.
        ~(det A = &0)
        ==> (X ** A = B <=>
             X = lambda k l.
                   det((lambda i j. if j = l then B$k$i else A$j$i):real^N^N) /
                   det A)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [CART_EQ] THEN
    ASM_SIMP_TAC [MATRIX_MUL_COMPONENT, CRAMER, DET_TRANSP] THEN
    SIMP_TAC [CART_EQ, LAMBDA_BETA] THEN
    REPLICATE_TAC 2 (AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC) THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC [CART_EQ, LAMBDA_BETA, transp])

  let CRAMER_MATRIX_RIGHT ← prove
   r"!A:real^N^N X:real^N^N B:real^N^N.
        ~(det A = &0)
        ==> (A ** X = B <=>
             X = lambda k l.
                   det((lambda i j. if j = k then B$i$l else A$i$j):real^N^N) /
                   det A)"
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM TRANSP_EQ] THEN
    REWRITE_TAC [MATRIX_TRANSP_MUL] THEN
    ASM_SIMP_TAC [CRAMER_MATRIX_LEFT, DET_TRANSP] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM TRANSP_EQ] THEN
    REWRITE_TAC [TRANSP_TRANSP] THEN AP_TERM_TAC THEN
    SIMP_TAC [CART_EQ, LAMBDA_BETA, transp] THEN
    REPEAT (GEN_TAC THEN STRIP_TAC) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC [CART_EQ, LAMBDA_BETA, transp])

  let CRAMER_MATRIX_RIGHT_INVERSE ← prove
   r"!A:real^N^N A':real^N^N.
        A ** A' = mat 1 <=>
        ~(det A = &0) /\
        A' = lambda k l.
                det((lambda i j. if j = k then if i = l then &1 else &0
                                 else A$i$j):real^N^N) /
                det A"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"det(A:real^N^N) = &0") THENL
     [ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o AP_TERM (← q r"det:real^N^N->real")) THEN
      ASM_REWRITE_TAC [DET_MUL, DET_I] THEN REAL_ARITH_TAC,
      ASM_SIMP_TAC [CRAMER_MATRIX_RIGHT] THEN AP_TERM_TAC THEN
      SIMP_TAC [CART_EQ, LAMBDA_BETA] THEN
      REPEAT (GEN_TAC THEN STRIP_TAC) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC [CART_EQ, LAMBDA_BETA, mat]])

  let CRAMER_MATRIX_LEFT_INVERSE ← prove
   r"!A:real^N^N A':real^N^N.
        A' ** A = mat 1 <=>
        ~(det A = &0) /\
        A' = lambda k l.
                det((lambda i j. if j = l then if i = k then &1 else &0
                                 else A$j$i):real^N^N) /
                det A"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"det(A:real^N^N) = &0") THENL
     [ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o AP_TERM (← q r"det:real^N^N->real")) THEN
      ASM_REWRITE_TAC [DET_MUL, DET_I] THEN REAL_ARITH_TAC,
      ASM_SIMP_TAC [CRAMER_MATRIX_LEFT] THEN AP_TERM_TAC THEN
      SIMP_TAC [CART_EQ, LAMBDA_BETA] THEN
      REPEAT (GEN_TAC THEN STRIP_TAC) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC [CART_EQ, LAMBDA_BETA, mat] THEN MESON_TAC []])

  return { CRAMER_LEMMA_TRANSP, CRAMER_LEMMA, CRAMER, CRAMER_MATRIX_LEFT,
           CRAMER_MATRIX_RIGHT, CRAMER_MATRIX_RIGHT_INVERSE, CRAMER_MATRIX_LEFT_INVERSE }

/- ------------------------------------------------------------------------- -/
/- Cofactors and their relationship to inverse matrices.                     -/
/- (determinants.ml 922-1145)                                                 -/
/- ------------------------------------------------------------------------- -/

structure Cofactor where
  cofactor : thm
  COFACTOR_TRANSP : thm
  COFACTOR_COLUMN : thm
  COFACTOR_ROW : thm
  MATRIX_RIGHT_INVERSE_COFACTOR : thm
  MATRIX_LEFT_INVERSE_COFACTOR : thm
  MATRIX_INV_COFACTOR : thm
  COFACTOR_MATRIX_INV : thm
  COFACTOR_I : thm
  DET_COFACTOR_EXPANSION : thm
  MATRIX_MUL_RIGHT_COFACTOR : thm
  MATRIX_MUL_LEFT_COFACTOR : thm
  COFACTOR_CMUL : thm
  COFACTOR_0 : thm
  deriving Inhabited

@[nospecialize]
def setupCofactor [HolBase] (D : DeterminantsDeps) (BTrace : Trace) (BDetBasic : DetBasic)
    (BInvertibility : Invertibility) (BCramer : Cramer) : ExceptT String IO Cofactor := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC, REAL_ARITH,
        REAL_ARITH_TAC, SET_RULE, SET_TAC, new_definition, .. } := D
  let { ARITH_EQ, CARD_DELETE, CARD_NUMSEG_1, CART_EQ, DIMINDEX_GE_1, EQ_TRANS, EXTENSION,
        FINITE_DELETE, FINITE_NUMSEG, FORALL_IN_GSPEC, IN_DELETE, IN_IMAGE, IN_INSERT,
        IN_NUMSEG, LAMBDA_BETA, .. } := D.core1
  let { PRODUCT_CLAUSES, REAL_MUL_LID, REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RINV,
        REAL_MUL_RZERO, REAL_MUL_SYM, REAL_OF_NUM_EQ, .. } := D.core2
  let { REAL_POW_ZERO, SUM_DELTA, SUM_EQ, SUM_EQ_NUMSEG, SUM_LMUL, SUM_SWAP, real_div,
        .. } := D.core3
  let { MATRIX_CMUL_ASSOC, MATRIX_CMUL_COMPONENT, MATRIX_CMUL_LID, MATRIX_CMUL_LZERO,
        .. } := D.vec1
  let { MATRIX_INV_I, MATRIX_LEFT_RIGHT_INVERSE, MATRIX_TRANSP_MUL, .. } := D.vec2
  let { TRANSP_EQ, TRANSP_MAT, TRANSP_MATRIX_CMUL, TRANSP_TRANSP, mat, matrix_mul, row,
        transp, .. } := D.vec3
  let { FINITE_PERMUTATIONS, PERMUTES_IMAGE, PERMUTES_INVERSE, PERMUTES_INVERSES,
        PERMUTES_INVERSE_EQ, PERMUTES_IN_IMAGE, PRODUCT_CONST, PRODUCT_EQ, PRODUCT_EQ_0,
        PRODUCT_MUL, .. } := D.lib
  let { det, .. } := BTrace
  let { DET_I, DET_IDENTICAL_ROWS, DET_TRANSP, .. } := BDetBasic
  let { MATRIX_MUL_LINV, .. } := BInvertibility
  let { CRAMER_MATRIX_RIGHT_INVERSE, .. } := BCramer
  -- @@SCOPE END

  let cofactor ← new_definition
   r"(cofactor:real^N^N->real^N^N) A =
        lambda i j. det((lambda k l. if k = i /\ l = j then &1
                                     else if k = i \/ l = j then &0
                                     else A$k$l):real^N^N)"

  let COFACTOR_TRANSP ← prove
   r"!A:real^N^N. cofactor(transp A) = transp(cofactor A)"
   (SIMP_TAC [cofactor, CART_EQ, LAMBDA_BETA, transp] THEN REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM DET_TRANSP] THEN
    AP_TERM_TAC THEN SIMP_TAC [cofactor, CART_EQ, LAMBDA_BETA, transp] THEN
    MESON_TAC [])

  let COFACTOR_COLUMN ← prove
   r"!A:real^N^N.
        cofactor A =
        lambda i j. det((lambda k l. if l = j then if k = i then &1 else &0
                                     else A$k$l):real^N^N)"
   (GEN_TAC THEN CONV_TAC SYM_CONV THEN
    SIMP_TAC [cofactor, CART_EQ, LAMBDA_BETA] THEN
    X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"j:num") THEN STRIP_TAC THEN
    REWRITE_TAC [det] THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC [FORALL_IN_GSPEC] THEN GEN_TAC THEN
    DISCH_TAC THEN AP_TERM_TAC THEN
    ASM_CASES_TAC (← q r"(p:num->num) i = j") THENL
     [MATCH_MP_TAC PRODUCT_EQ THEN
      X_GEN_TAC (← q r"k:num") THEN SIMP_TAC [IN_NUMSEG, LAMBDA_BETA] THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"(p:num->num) k IN 1..dimindex(:N)") MP_TAC THENL
       [ASM_MESON_TAC [PERMUTES_IN_IMAGE, IN_NUMSEG],
        SIMP_TAC [LAMBDA_BETA, IN_NUMSEG] THEN STRIP_TAC] THEN
      ASM_CASES_TAC (← q r"(p:num->num) k = j") THEN ASM_REWRITE_TAC [] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [],
      MATCH_MP_TAC (← REAL_ARITH (← q r"s = &0 /\ t = &0 ==> s = t")) THEN
      ASM_SIMP_TAC [PRODUCT_EQ_0, FINITE_NUMSEG] THEN CONJ_TAC THEN
      EXISTS_TAC (← q r"inverse (p:num->num) j") THEN
      ASM_SIMP_TAC [IN_NUMSEG, LAMBDA_BETA] THEN
      (SUBGOAL_THEN (← q r"inverse(p:num->num) j IN 1..dimindex(:N)") MP_TAC THENL
        [ASM_MESON_TAC [PERMUTES_IN_IMAGE, PERMUTES_INVERSE, IN_NUMSEG],
         SIMP_TAC [LAMBDA_BETA, IN_NUMSEG] THEN STRIP_TAC] THEN
       SUBGOAL_THEN (← q r"(p:num->num)(inverse p j) = j") SUBST1_TAC THENL
        [ASM_MESON_TAC [PERMUTES_INVERSES, IN_NUMSEG],
         ASM_SIMP_TAC [LAMBDA_BETA] THEN
          ASM_MESON_TAC [PERMUTES_INVERSE_EQ]])])

  let COFACTOR_ROW ← prove
   r"!A:real^N^N.
        cofactor A =
        lambda i j. det((lambda k l. if k = i then if l = j then &1 else &0
                                     else A$k$l):real^N^N)"
   (GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM TRANSP_EQ] THEN
    REWRITE_TAC [← GSYM COFACTOR_TRANSP] THEN
    SIMP_TAC [COFACTOR_COLUMN, CART_EQ, LAMBDA_BETA, transp] THEN
    REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM DET_TRANSP] THEN
    AP_TERM_TAC THEN SIMP_TAC [cofactor, CART_EQ, LAMBDA_BETA, transp])

  let MATRIX_RIGHT_INVERSE_COFACTOR ← prove
   r"!A:real^N^N A':real^N^N.
        A ** A' = mat 1 <=>
        ~(det A = &0) /\ A' = inv(det A) %% transp(cofactor A)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [CRAMER_MATRIX_RIGHT_INVERSE] THEN
    ASM_CASES_TAC (← q r"det(A:real^N^N) = &0") THEN ASM_REWRITE_TAC [] THEN
    AP_TERM_TAC THEN SIMP_TAC [CART_EQ, LAMBDA_BETA, MATRIX_CMUL_COMPONENT] THEN
    X_GEN_TAC (← q r"k:num") THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"l:num") THEN STRIP_TAC THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_MUL_SYM] real_div] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC [transp, COFACTOR_COLUMN, LAMBDA_BETA] THEN
    AP_TERM_TAC THEN SIMP_TAC [CART_EQ, LAMBDA_BETA])

  let MATRIX_LEFT_INVERSE_COFACTOR ← prove
   r"!A:real^N^N A':real^N^N.
        A' ** A = mat 1 <=>
        ~(det A = &0) /\ A' = inv(det A) %% transp(cofactor A)"
   (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [MATRIX_LEFT_RIGHT_INVERSE] THEN
    REWRITE_TAC [MATRIX_RIGHT_INVERSE_COFACTOR])

  let MATRIX_INV_COFACTOR ← prove
   r"!A. ~(det A = &0) ==> matrix_inv A = inv(det A) %% transp(cofactor A)"
   (GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP MATRIX_MUL_LINV) THEN
    SIMP_TAC [MATRIX_LEFT_INVERSE_COFACTOR])

  let COFACTOR_MATRIX_INV ← prove
   r"!A:real^N^N. ~(det A = &0) ==> cofactor A = det(A) %% transp(matrix_inv A)"
   (SIMP_TAC [MATRIX_INV_COFACTOR, TRANSP_MATRIX_CMUL, TRANSP_TRANSP] THEN
    SIMP_TAC [MATRIX_CMUL_ASSOC, REAL_MUL_RINV, MATRIX_CMUL_LID])

  let COFACTOR_I ← prove
   r"cofactor(mat 1:real^N^N) = mat 1"
   (SIMP_TAC [COFACTOR_MATRIX_INV, DET_I, REAL_OF_NUM_EQ, ARITH_EQ] THEN
    REWRITE_TAC [MATRIX_INV_I, MATRIX_CMUL_LID, TRANSP_MAT])

  let DET_COFACTOR_EXPANSION ← prove
   r"!A:real^N^N i.
        1 <= i /\ i <= dimindex(:N)
        ==> det A = sum (1..dimindex(:N))
                        (\j. A$i$j * (cofactor A)$i$j)"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [COFACTOR_COLUMN, LAMBDA_BETA, det] THEN
    REWRITE_TAC [← GSYM SUM_LMUL] THEN
    W (MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o rand o snd) THEN
    ANTS_TAC THENL [SIMP_TAC [FINITE_PERMUTATIONS, FINITE_NUMSEG], ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC [FORALL_IN_GSPEC] THEN
    GEN_TAC THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"a * s * p:real = s * a * p")] THEN
    REWRITE_TAC [SUM_LMUL] THEN AP_TERM_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     (← q r"sum (1..dimindex (:N))
        (\j. (A:real^N^N)$i$j *
             product
              (inverse p j INSERT ((1..dimindex(:N)) DELETE (inverse p j)))
              (\k. if k = inverse p j then if k = i then &1 else &0
                   else A$k$(p k)))") THEN
    CONJ_TAC THENL
     [SIMP_TAC [PRODUCT_CLAUSES, FINITE_DELETE, FINITE_PERMUTATIONS,
                FINITE_NUMSEG, IN_DELETE] THEN
      SUBGOAL_THEN (← q r"!j. inverse (p:num->num) j = i <=> j = p i")
       (fun th => REWRITE_TAC [th])
      THENL [ASM_MESON_TAC [PERMUTES_INVERSES, IN_NUMSEG], ALL_TAC] THEN
      REWRITE_TAC [← REAL_ARITH (← q
       r"x * (if p then &1 else &0) * y = if p then x * y else &0")] THEN
      SIMP_TAC [SUM_DELTA] THEN COND_CASES_TAC THENL
       [ALL_TAC, ASM_MESON_TAC [PERMUTES_IN_IMAGE, IN_NUMSEG]] THEN
      SUBGOAL_THEN
       (← q r"1..dimindex(:N) = i INSERT ((1..dimindex(:N)) DELETE i)")
       (fun th => GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
      THENL
       [ASM_SIMP_TAC [IN_NUMSEG, ← SET_RULE (← q r"s = x INSERT (s DELETE x) <=> x IN s")],
        SIMP_TAC [PRODUCT_CLAUSES, FINITE_DELETE, FINITE_NUMSEG, IN_DELETE] THEN
        AP_TERM_TAC THEN MATCH_MP_TAC (← MESON [PRODUCT_EQ] (← q
         r"s = t /\ (!x. x IN t ==> f x = g x) ==> product s f = product t g")) THEN
        SIMP_TAC [IN_DELETE] THEN ASM_MESON_TAC [PERMUTES_INVERSES, IN_NUMSEG]],
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC (← q r"j:num") THEN STRIP_TAC THEN
      REWRITE_TAC [] THEN AP_TERM_TAC THEN MATCH_MP_TAC (← MESON [PRODUCT_EQ] (← q
       r"s = t /\ (!x. x IN t ==> f x = g x) ==> product s f = product t g")) THEN
      CONJ_TAC THENL
       [REWRITE_TAC [← SET_RULE (← q r"x INSERT (s DELETE x) = s <=> x IN s")] THEN
        ASM_MESON_TAC [PERMUTES_IN_IMAGE, IN_NUMSEG, PERMUTES_INVERSE],
        X_GEN_TAC (← q r"k:num") THEN REWRITE_TAC [IN_NUMSEG] THEN STRIP_TAC THEN
        SUBGOAL_THEN (← q r"(p:num->num) k IN 1..dimindex(:N)") MP_TAC THENL
         [ASM_MESON_TAC [PERMUTES_IN_IMAGE, IN_NUMSEG], ALL_TAC] THEN
        SIMP_TAC [LAMBDA_BETA, IN_NUMSEG] THEN
        ASM_MESON_TAC [PERMUTES_INVERSES, IN_NUMSEG]]])

  let MATRIX_MUL_RIGHT_COFACTOR ← prove
   r"!A:real^N^N. A ** transp(cofactor A) = det(A) %% mat 1"
   (GEN_TAC THEN
    SIMP_TAC [CART_EQ, MATRIX_CMUL_COMPONENT, mat,
              matrix_mul, LAMBDA_BETA, transp] THEN
    X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"i':num") THEN STRIP_TAC THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC [← GSYM DET_COFACTOR_EXPANSION, REAL_MUL_RID] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"det((lambda k l. if k = i' then (A:real^N^N)$i$l
                               else A$k$l):real^N^N)") THEN
    CONJ_TAC THENL
     [MP_TAC (← GEN (← q r"A:real^N^N")
       (← ISPECL [← q r"A:real^N^N", ← q r"i':num"] DET_COFACTOR_EXPANSION)) THEN
      ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [] THEN DISCH_THEN (K ALL_TAC) THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q r"j:num") THEN
      REWRITE_TAC [IN_NUMSEG] THEN STRIP_TAC THEN
      ASM_SIMP_TAC [LAMBDA_BETA] THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC [cofactor, LAMBDA_BETA] THEN AP_TERM_TAC THEN
      SIMP_TAC [CART_EQ, LAMBDA_BETA] THEN ASM_MESON_TAC [],
      REWRITE_TAC [REAL_MUL_RZERO] THEN MATCH_MP_TAC DET_IDENTICAL_ROWS THEN
      MAP_EVERY EXISTS_TAC [← q r"i:num", ← q r" i':num"] THEN
      ASM_SIMP_TAC [CART_EQ, LAMBDA_BETA, row]])

  let MATRIX_MUL_LEFT_COFACTOR ← prove
   r"!A:real^N^N. transp(cofactor A) ** A = det(A) %% mat 1"
   (GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM TRANSP_EQ] THEN
    REWRITE_TAC [MATRIX_TRANSP_MUL] THEN
    ONCE_REWRITE_TAC [← GSYM COFACTOR_TRANSP] THEN
    REWRITE_TAC [MATRIX_MUL_RIGHT_COFACTOR, TRANSP_MATRIX_CMUL] THEN
    REWRITE_TAC [DET_TRANSP, TRANSP_MAT])

  let COFACTOR_CMUL ← prove
   r"!A:real^N^N c. cofactor(c %% A) = c pow (dimindex(:N) - 1) %% cofactor A"
   (REPEAT GEN_TAC THEN
    SIMP_TAC [CART_EQ, cofactor, LAMBDA_BETA, MATRIX_CMUL_COMPONENT] THEN
    X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"j:num") THEN STRIP_TAC THEN
    REWRITE_TAC [det, ← GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC [FORALL_IN_GSPEC] THEN
    X_GEN_TAC (← q r"p:num->num") THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"a * b * c:real = b * a * c")] THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN
     (← q r"1..dimindex (:N) = i INSERT ((1..dimindex (:N)) DELETE i)")
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_INSERT, IN_NUMSEG, IN_DELETE] THEN ASM_ARITH_TAC,
      SIMP_TAC [PRODUCT_CLAUSES, FINITE_DELETE, FINITE_NUMSEG, IN_DELETE]] THEN
    SUBGOAL_THEN
     (← q r"1 <= (p:num->num) i /\ p i <= dimindex(:N)")
    ASSUME_TAC THENL
     [FIRST_ASSUM (MP_TAC o MATCH_MP PERMUTES_IMAGE) THEN
      REWRITE_TAC [EXTENSION, IN_IMAGE, IN_NUMSEG] THEN ASM SET_TAC [],
      ASM_SIMP_TAC [LAMBDA_BETA]] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
    SUBGOAL_THEN
     (← q r"dimindex(:N) - 1 = CARD((1..dimindex(:N)) DELETE i)")
    SUBST1_TAC THENL
     [ASM_SIMP_TAC [CARD_DELETE, FINITE_NUMSEG, IN_NUMSEG, CARD_NUMSEG_1],
      ASM_SIMP_TAC [REAL_MUL_LID, ← GSYM PRODUCT_CONST, FINITE_NUMSEG,
                    FINITE_DELETE, ← GSYM PRODUCT_MUL]] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN
    X_GEN_TAC (← q r"k:num") THEN REWRITE_TAC [IN_DELETE, IN_NUMSEG] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"1 <= (p:num->num) k /\ p k <= dimindex(:N)")
    ASSUME_TAC THENL
     [FIRST_ASSUM (MP_TAC o MATCH_MP PERMUTES_IMAGE) THEN
      REWRITE_TAC [EXTENSION, IN_IMAGE, IN_NUMSEG] THEN ASM SET_TAC [],
      ASM_SIMP_TAC [LAMBDA_BETA] THEN REAL_ARITH_TAC])

  let COFACTOR_0 ← prove
   r"cofactor(mat 0:real^N^N) = if dimindex(:N) = 1 then mat 1 else mat 0"
   (MP_TAC (← ISPECL [← q r"mat 1:real^N^N", ← q r"&0"] COFACTOR_CMUL) THEN
    REWRITE_TAC [MATRIX_CMUL_LZERO, COFACTOR_I, REAL_POW_ZERO] THEN
    DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC [DIMINDEX_GE_1, ← ARITH_RULE (← q r"1 <= n ==> (n - 1 = 0 <=> n = 1)")] THEN
    COND_CASES_TAC THEN REWRITE_TAC [MATRIX_CMUL_LZERO, MATRIX_CMUL_LID])

  return { cofactor, COFACTOR_TRANSP, COFACTOR_COLUMN, COFACTOR_ROW,
           MATRIX_RIGHT_INVERSE_COFACTOR, MATRIX_LEFT_INVERSE_COFACTOR, MATRIX_INV_COFACTOR,
           COFACTOR_MATRIX_INV, COFACTOR_I, DET_COFACTOR_EXPANSION, MATRIX_MUL_RIGHT_COFACTOR,
           MATRIX_MUL_LEFT_COFACTOR, COFACTOR_CMUL, COFACTOR_0 }

/- ------------------------------------------------------------------------- -/
/- Explicit formulas for low dimensions.  (determinants.ml 1150-1268)        -/
/- ------------------------------------------------------------------------- -/

structure LowDim where
  PRODUCT_1 : thm
  PRODUCT_2 : thm
  PRODUCT_3 : thm
  PRODUCT_4 : thm
  DET_1_GEN : thm
  DET_1 : thm
  DET_2 : thm
  DET_3 : thm
  DET_4 : thm
  COFACTOR_1_GEN : thm
  COFACTOR_1 : thm
  deriving Inhabited

@[nospecialize]
def setupLowDim [HolBase] (D : DeterminantsDeps) (BTrace : Trace) (BCofactor : Cofactor) :
    ExceptT String IO LowDim := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, NUMSEG_CONV, REAL_ARITH_TAC, SET_RULE, num_CONV, .. } := D
  let { ARITH, ARITH_EQ, CART_EQ, DIMINDEX_1, DIMINDEX_2, DIMINDEX_3, DIMINDEX_4,
        FINITE_EMPTY, FINITE_INSERT, IN_INSERT, LAMBDA_BETA, .. } := D.core1
  let { LE_ANTISYM, NOT_IN_EMPTY, NUMSEG_SING, REAL_MUL_ASSOC, .. } := D.core2
  let { SUM_CLAUSES, SUM_SING, o_THM, .. } := D.core3
  let { I_O_ID, I_THM, .. } := D.core4
  let { SUM_2, SUM_3, SUM_4, mat, .. } := D.vec3
  let { PERMUTATION_COMPOSE, PERMUTATION_SWAP, PERMUTES_EMPTY, PERMUTES_SING,
        PRODUCT_CLAUSES_NUMSEG, PRODUCT_SING, PRODUCT_SING_NUMSEG, SIGN_COMPOSE, SIGN_I,
        SIGN_SWAP, SUM_OVER_PERMUTATIONS_INSERT, SWAP_REFL, swap, .. } := D.lib
  let { det, .. } := BTrace
  let { cofactor, .. } := BCofactor
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))
  let nsc (s : String) : ExceptT String IO thm := do ExceptT.mk (NUMSEG_CONV (← q s))

  let PRODUCT_1 ← prove
   r"product(1..1) f = f(1)"
   (REWRITE_TAC [PRODUCT_SING_NUMSEG])

  let PRODUCT_2 ← prove
   r"!t. product(1..2) t = t(1) * t(2)"
   (REWRITE_TAC [← numc "2", PRODUCT_CLAUSES_NUMSEG] THEN
    REWRITE_TAC [PRODUCT_SING_NUMSEG, ARITH, REAL_MUL_ASSOC])

  let PRODUCT_3 ← prove
   r"!t. product(1..3) t = t(1) * t(2) * t(3)"
   (REWRITE_TAC [← numc "3", ← numc "2", PRODUCT_CLAUSES_NUMSEG] THEN
    REWRITE_TAC [PRODUCT_SING_NUMSEG, ARITH, REAL_MUL_ASSOC])

  let PRODUCT_4 ← prove
   r"!t. product(1..4) t = t(1) * t(2) * t(3) * t(4)"
   (REWRITE_TAC [← numc "4", ← numc "3", ← numc "2",
                 PRODUCT_CLAUSES_NUMSEG] THEN
    REWRITE_TAC [PRODUCT_SING_NUMSEG, ARITH, REAL_MUL_ASSOC])

  let DET_1_GEN ← prove
   r"!A:real^N^N. dimindex(:N) = 1 ==> det A = A$1$1"
   (REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [det, PERMUTES_SING, NUMSEG_SING] THEN
    REWRITE_TAC [SUM_SING, ← SET_RULE (← q r"{x | x = a} = {a}"), PRODUCT_SING] THEN
    REWRITE_TAC [SIGN_I, I_THM] THEN REAL_ARITH_TAC)

  let DET_1 ← prove
   r"!A:real^1^1. det A = A$1$1"
   (SIMP_TAC [DET_1_GEN, DIMINDEX_1])

  let DET_2 ← prove
   r"!A:real^2^2. det A = A$1$1 * A$2$2 - A$1$2 * A$2$1"
   (GEN_TAC THEN REWRITE_TAC [det, DIMINDEX_2] THEN
    CONV_TAC (LAND_CONV (RATOR_CONV (ONCE_DEPTH_CONV NUMSEG_CONV))) THEN
    SIMP_TAC [SUM_OVER_PERMUTATIONS_INSERT, FINITE_INSERT, FINITE_EMPTY,
              ARITH_EQ, IN_INSERT, NOT_IN_EMPTY] THEN
    REWRITE_TAC [PERMUTES_EMPTY, SUM_SING, ← SET_RULE (← q r"{x | x = a} = {a}")] THEN
    REWRITE_TAC [SWAP_REFL, I_O_ID] THEN
    REWRITE_TAC [← GSYM (← nsc "1..2"), SUM_2] THEN
    SIMP_TAC [SUM_CLAUSES, FINITE_INSERT, FINITE_EMPTY,
              ARITH_EQ, IN_INSERT, NOT_IN_EMPTY] THEN
    SIMP_TAC [SIGN_COMPOSE, PERMUTATION_SWAP] THEN
    REWRITE_TAC [SIGN_SWAP, ARITH] THEN REWRITE_TAC [PRODUCT_2] THEN
    REWRITE_TAC [o_THM, swap, ARITH] THEN REAL_ARITH_TAC)

  let DET_3 ← prove
   r"!A:real^3^3.
        det(A) = A$1$1 * A$2$2 * A$3$3 +
                 A$1$2 * A$2$3 * A$3$1 +
                 A$1$3 * A$2$1 * A$3$2 -
                 A$1$1 * A$2$3 * A$3$2 -
                 A$1$2 * A$2$1 * A$3$3 -
                 A$1$3 * A$2$2 * A$3$1"
   (GEN_TAC THEN REWRITE_TAC [det, DIMINDEX_3] THEN
    CONV_TAC (LAND_CONV (RATOR_CONV (ONCE_DEPTH_CONV NUMSEG_CONV))) THEN
    SIMP_TAC [SUM_OVER_PERMUTATIONS_INSERT, FINITE_INSERT, FINITE_EMPTY,
              ARITH_EQ, IN_INSERT, NOT_IN_EMPTY] THEN
    REWRITE_TAC [PERMUTES_EMPTY, SUM_SING, ← SET_RULE (← q r"{x | x = a} = {a}")] THEN
    REWRITE_TAC [SWAP_REFL, I_O_ID] THEN
    REWRITE_TAC [← GSYM (← nsc "1..3"), SUM_3] THEN
    SIMP_TAC [SUM_CLAUSES, FINITE_INSERT, FINITE_EMPTY,
              ARITH_EQ, IN_INSERT, NOT_IN_EMPTY] THEN
    SIMP_TAC [SIGN_COMPOSE, PERMUTATION_SWAP] THEN
    REWRITE_TAC [SIGN_SWAP, ARITH] THEN REWRITE_TAC [PRODUCT_3] THEN
    REWRITE_TAC [o_THM, swap, ARITH] THEN REAL_ARITH_TAC)

  let DET_4 ← do
    let lemma ← prove
     r"(sum {3,4} f = f 3 + f 4) /\
     (sum {2,3,4} f = f 2 + f 3 + f 4)"
     (SIMP_TAC [SUM_CLAUSES, FINITE_INSERT, FINITE_EMPTY] THEN
      REWRITE_TAC [ARITH_EQ, IN_INSERT, NOT_IN_EMPTY] THEN REAL_ARITH_TAC)
    prove
     r"!A:real^4^4.
        det(A) = A$1$1 * A$2$2 * A$3$3 * A$4$4 +
                 A$1$1 * A$2$3 * A$3$4 * A$4$2 +
                 A$1$1 * A$2$4 * A$3$2 * A$4$3 +
                 A$1$2 * A$2$1 * A$3$4 * A$4$3 +
                 A$1$2 * A$2$3 * A$3$1 * A$4$4 +
                 A$1$2 * A$2$4 * A$3$3 * A$4$1 +
                 A$1$3 * A$2$1 * A$3$2 * A$4$4 +
                 A$1$3 * A$2$2 * A$3$4 * A$4$1 +
                 A$1$3 * A$2$4 * A$3$1 * A$4$2 +
                 A$1$4 * A$2$1 * A$3$3 * A$4$2 +
                 A$1$4 * A$2$2 * A$3$1 * A$4$3 +
                 A$1$4 * A$2$3 * A$3$2 * A$4$1 -
                 A$1$1 * A$2$2 * A$3$4 * A$4$3 -
                 A$1$1 * A$2$3 * A$3$2 * A$4$4 -
                 A$1$1 * A$2$4 * A$3$3 * A$4$2 -
                 A$1$2 * A$2$1 * A$3$3 * A$4$4 -
                 A$1$2 * A$2$3 * A$3$4 * A$4$1 -
                 A$1$2 * A$2$4 * A$3$1 * A$4$3 -
                 A$1$3 * A$2$1 * A$3$4 * A$4$2 -
                 A$1$3 * A$2$2 * A$3$1 * A$4$4 -
                 A$1$3 * A$2$4 * A$3$2 * A$4$1 -
                 A$1$4 * A$2$1 * A$3$2 * A$4$3 -
                 A$1$4 * A$2$2 * A$3$3 * A$4$1 -
                 A$1$4 * A$2$3 * A$3$1 * A$4$2"
     (GEN_TAC THEN REWRITE_TAC [det, DIMINDEX_4] THEN
      CONV_TAC (LAND_CONV (RATOR_CONV (ONCE_DEPTH_CONV NUMSEG_CONV))) THEN
      SIMP_TAC [SUM_OVER_PERMUTATIONS_INSERT, FINITE_INSERT, FINITE_EMPTY,
                ARITH_EQ, IN_INSERT, NOT_IN_EMPTY] THEN
      REWRITE_TAC [PERMUTES_EMPTY, SUM_SING, ← SET_RULE (← q r"{x | x = a} = {a}")] THEN
      REWRITE_TAC [SWAP_REFL, I_O_ID] THEN
      REWRITE_TAC [← GSYM (← nsc "1..4"), SUM_4, lemma] THEN
      SIMP_TAC [SIGN_COMPOSE, PERMUTATION_SWAP, PERMUTATION_COMPOSE] THEN
      REWRITE_TAC [SIGN_SWAP, ARITH] THEN REWRITE_TAC [PRODUCT_4] THEN
      REWRITE_TAC [o_THM, swap, ARITH] THEN REAL_ARITH_TAC)

  let COFACTOR_1_GEN ← prove
   r"!A:real^N^N. dimindex(:N) = 1 ==> cofactor A = mat 1"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [CART_EQ, mat, cofactor, LAMBDA_BETA, DET_1_GEN, ARITH] THEN
    REWRITE_TAC [LE_ANTISYM] THEN MESON_TAC [])

  let COFACTOR_1 ← prove
   r"!A:real^1^1. cofactor A = mat 1"
   (SIMP_TAC [COFACTOR_1_GEN, DIMINDEX_1])

  return { PRODUCT_1, PRODUCT_2, PRODUCT_3, PRODUCT_4, DET_1_GEN, DET_1, DET_2, DET_3, DET_4,
           COFACTOR_1_GEN, COFACTOR_1 }

/- ------------------------------------------------------------------------- -/
/- Disjoint or subset-related halfspaces and hyperplanes are parallel.       -/
/- (determinants.ml 1273-1514)                                                -/
/- ------------------------------------------------------------------------- -/

structure Parallel where
  DISJOINT_HYPERPLANES_IMP_COLLINEAR : thm
  DISJOINT_HALFSPACES_IMP_COLLINEAR : thm
  SUBSET_HALFSPACES_IMP_COLLINEAR : thm
  SUBSET_HYPERPLANES : thm
  deriving Inhabited

@[nospecialize]
def setupParallel [HolBase] (D : DeterminantsDeps) (BInvertibility : Invertibility)
    (BLowDim : LowDim) : ExceptT String IO Parallel := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, MESON, MESON_TAC, REAL_ARITH, REAL_FIELD, SET_RULE, SET_TAC,
        VECTOR_ARITH, .. } := D
  let { ARITH, CART_EQ, DIMINDEX_2, DISJOINT_SYM, EMPTY_SUBSET, IN_ELIM_THM, .. } := D.core1
  let { REAL_DIV_RMUL, REAL_LT_IMP_LE, REAL_MUL_SYM, REAL_NEG_NEG, .. } := D.core2
  let { SUBSET, SUBSET_ANTISYM_EQ, SUBSET_UNIV, .. } := D.core3
  let { CONTRAPOS_THM, DE_MORGAN_THM, MONO_IMP, .. } := D.core4
  let { COLLINEAR_LEMMA_ALT, DOT_2, DOT_CAUCHY_SCHWARZ_EQUAL, DOT_EQ_0, DOT_LMUL, DOT_LNEG,
        DOT_LZERO, DOT_RADD, DOT_RMUL, DOT_SYM, EXISTS_VECTOR_2, FORALL_2,
        HYPERPLANE_EQ_EMPTY, HYPERPLANE_EQ_UNIV, MATRIX_FULL_LINEAR_EQUATIONS, .. } := D.vec1
  let { MATRIX_VECTOR_MUL_COMPONENT, .. } := D.vec2
  let { VECTOR_2, VECTOR_MUL_EQ_0, VECTOR_NEG_EQ_0, .. } := D.vec3
  let { RANK_EQ_FULL_DET, .. } := BInvertibility
  let { DET_2, .. } := BLowDim
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)
  let ra (s : String) : ExceptT String IO thm := do REAL_ARITH (← q s)

  let DISJOINT_HYPERPLANES_IMP_COLLINEAR ← prove
   r"!a b:real^N c d.
        DISJOINT {x | a dot x = c} {x | b dot x = d}
        ==> collinear {vec 0, a, b}"
   (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o MATCH_MP (← SET_RULE (← q
     r"DISJOINT {x:real^N | a dot x = c} {x | b dot x = d}
    ==> !u v. a dot (u % a + v % b) = c /\
              b dot (u % a + v % b) = d ==> F"))) THEN
    REWRITE_TAC [DOT_RADD, DOT_RMUL] THEN
    GEN_REWRITE_TAC id [← GSYM CONTRAPOS_THM] THEN
    MP_TAC (← ISPECL
     [← q r"vector[vector[(a:real^N) dot a; a dot b];
            vector[a dot b; b dot b]]:real^2^2",
      ← q r"vector[c;d]:real^2"] MATRIX_FULL_LINEAR_EQUATIONS) THEN
    REWRITE_TAC [RANK_EQ_FULL_DET] THEN
    SIMP_TAC [CART_EQ, DIMINDEX_2, MATRIX_VECTOR_MUL_COMPONENT, ARITH,
              VECTOR_2, FORALL_2, DOT_2, EXISTS_VECTOR_2, DET_2] THEN
    MATCH_MP_TAC MONO_IMP THEN CONJ_TAC THENL
     [REWRITE_TAC [CONTRAPOS_THM], MESON_TAC [DOT_SYM, REAL_MUL_SYM]] THEN
    REWRITE_TAC [← ra r"a - b * b = &0 <=> b pow 2 = a"] THEN
    REWRITE_TAC [DOT_CAUCHY_SCHWARZ_EQUAL])

  let DISJOINT_HALFSPACES_IMP_COLLINEAR ← do
    let lemma ← prove
     r"(!a b:real^N. collinear {vec 0,--a,b} <=> collinear{vec 0,a,b}) /\
     (!a b:real^N. collinear {vec 0,a,--b} <=> collinear{vec 0,a,b})"
     (REWRITE_TAC [COLLINEAR_LEMMA_ALT, VECTOR_NEG_EQ_0] THEN
      REWRITE_TAC [← va r"b:real^N = c % --a <=> b = --c % a",
                   ← va r"--b:real^N = c % a <=> b = --c % a"] THEN
      REWRITE_TAC [← MESON [REAL_NEG_NEG] (← q r"(?x:real. P(--x)) <=> ?x. P x")])
    prove
     r"(!a b:real^N c d.
        DISJOINT {x | a dot x < c} {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x < c} {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x < c} {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x < c} {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x < c} {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x <= c} {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x <= c} {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x <= c} {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x <= c} {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x <= c} {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x = c} {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x = c} {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x = c} {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x = c} {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x = c} {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x >= c} {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x >= c} {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x >= c} {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x >= c} {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x >= c} {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x > c} {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x > c} {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x > c} {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x > c} {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x > c} {x | b dot x > d}
        ==> collinear {vec 0, a, b})"
     (REWRITE_TAC [← ra r"x >= d <=> --x <= --d",
                   ← ra r"x > d <=> --x < --d"] THEN
      REWRITE_TAC [← GSYM DOT_LNEG] THEN REPEAT STRIP_TAC THEN
      REPLICATE_TAC 2
      (TRY (FIRST_X_ASSUM (MP_TAC o MATCH_MP (← SET_RULE (← q
         r"DISJOINT {x | a dot x <= b} t
      ==> (!x y. x < y ==> x <= y) ==> DISJOINT {x | a dot x < b} t"))) THEN
        REWRITE_TAC [REAL_LT_IMP_LE] THEN DISCH_TAC) THEN
        RULE_ASSUM_TAC (ONCE_REWRITE_RULE [DISJOINT_SYM])) THEN
      REPLICATE_TAC 2
      (TRY (FIRST_X_ASSUM (MP_TAC o MATCH_MP (← SET_RULE (← q
          r"DISJOINT {x | a dot x < b} t
       ==> b - &1 < b ==> DISJOINT {x | a dot x = b - &1} t"))) THEN
         REWRITE_TAC [← ARITH_RULE (← q r"c - &1 < c")] THEN DISCH_TAC) THEN
       RULE_ASSUM_TAC (ONCE_REWRITE_RULE [DISJOINT_SYM])) THEN
      FIRST_X_ASSUM (MP_TAC o MATCH_MP DISJOINT_HYPERPLANES_IMP_COLLINEAR) THEN
      REWRITE_TAC [lemma])

  let SUBSET_HALFSPACES_IMP_COLLINEAR ← prove
   r"(!a b:real^N c d.
        {x | a dot x < c} SUBSET {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x < c} SUBSET {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x < c} SUBSET {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x < c} SUBSET {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x < c} SUBSET {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x <= c} SUBSET {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x <= c} SUBSET {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x <= c} SUBSET {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x <= c} SUBSET {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x <= c} SUBSET {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x = c} SUBSET {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x = c} SUBSET {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x = c} SUBSET {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x = c} SUBSET {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x = c} SUBSET {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x >= c} SUBSET {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x >= c} SUBSET {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x >= c} SUBSET {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x >= c} SUBSET {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x >= c} SUBSET {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x > c} SUBSET {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x > c} SUBSET {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x > c} SUBSET {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x > c} SUBSET {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x > c} SUBSET {x | b dot x > d}
        ==> collinear {vec 0, a, b})"
   (REWRITE_TAC [← SET_RULE (← q r"s SUBSET {x | P x} <=> DISJOINT s {x | ~P x}")] THEN
    REWRITE_TAC [← ra
      r"(~(x < a) <=> x >= a) /\ (~(x <= a) <=> x > a) /\
     (~(x = a) <=> x > a \/ x < a) /\
     (~(x > a) <=> x <= a) /\ (~(x >= a) <=> x < a)"] THEN
    REWRITE_TAC [← SET_RULE (← q
     r"DISJOINT s {x | P x \/ Q x} <=>
    DISJOINT s {x | P x} /\ DISJOINT s {x | Q x}")] THEN
    REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    TRY (DISCH_THEN (MP_TAC o CONJUNCT1)) THEN
    REWRITE_TAC [DISJOINT_HALFSPACES_IMP_COLLINEAR])

  let SUBSET_HYPERPLANES ← prove
   r"!a b a' b'.
        {x | a dot x = b} SUBSET {x | a' dot x = b'} <=>
        {x | a dot x = b} = {} \/ {x | a' dot x = b'} = (:real^N) \/
        {x | a dot x = b} = {x | a' dot x = b'}"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"{x:real^N | a dot x = b} = {}") THEN
    ASM_REWRITE_TAC [EMPTY_SUBSET] THEN
    ASM_CASES_TAC (← q r"{x | a' dot x = b'} = (:real^N)") THEN
    ASM_REWRITE_TAC [SUBSET_UNIV] THEN
    RULE_ASSUM_TAC (REWRITE_RULE
     [HYPERPLANE_EQ_EMPTY, HYPERPLANE_EQ_UNIV]) THEN
    REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN
    ASM_CASES_TAC (← q r"{x:real^N | a dot x = b} SUBSET {x | a' dot x = b'}") THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (← ISPECL [← q r"a:real^N", ← q r"a':real^N", ← q r"b:real", ← q r"b':real"]
     (CONJUNCTS SUBSET_HALFSPACES_IMP_COLLINEAR)[12]!) THEN
    ASM_REWRITE_TAC [COLLINEAR_LEMMA_ALT] THEN
    POP_ASSUM_LIST (fun ths => (MP_TAC o end_itlist CONJ) ths.reverse) THEN
    ASM_CASES_TAC (← q r"a:real^N = vec 0") THEN ASM_SIMP_TAC [DOT_LZERO] THENL
     [SET_TAC [], STRIP_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"c:real") SUBST_ALL_TAC) THEN
    POP_ASSUM_LIST (fun ths => (MP_TAC o end_itlist CONJ) ths.reverse) THEN
    ASM_CASES_TAC (← q r"c % a:real^N = vec 0") THEN ASM_SIMP_TAC [DOT_LZERO] THENL
     [SET_TAC [], POP_ASSUM MP_TAC] THEN
    SIMP_TAC [VECTOR_MUL_EQ_0, DE_MORGAN_THM, DOT_LMUL, ← REAL_FIELD (← q
     r"~(c = &0) ==> (c * a = b <=> a = b / c)")] THEN
    STRIP_TAC THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"(b / (a dot a)) % a:real^N")) THEN
    ASM_SIMP_TAC [DOT_RMUL, REAL_DIV_RMUL, DOT_EQ_0])

  return { DISJOINT_HYPERPLANES_IMP_COLLINEAR, DISJOINT_HALFSPACES_IMP_COLLINEAR,
           SUBSET_HALFSPACES_IMP_COLLINEAR, SUBSET_HYPERPLANES }

/- ------------------------------------------------------------------------- -/
/- Existence of the characteristic polynomial; Grassmann-Plucker relations  -/
/- for n = 2, 3, 4; determinants of integer matrices.                        -/
/- (determinants.ml 1519-1698)                                                -/
/- ------------------------------------------------------------------------- -/

structure CharPoly where
  EIGENVALUES_CHARACTERISTIC_ALT : thm
  EIGENVALUES_CHARACTERISTIC : thm
  INVERTIBLE_EIGENVALUES : thm
  CHARACTERISTIC_POLYNOMIAL : thm
  FINITE_EIGENVALUES : thm
  GRASSMANN_PLUCKER_2 : thm
  GRASSMANN_PLUCKER_3 : thm
  GRASSMANN_PLUCKER_4 : thm
  INTEGER_PRODUCT : thm
  INTEGER_SIGN : thm
  INTEGER_DET : thm
  deriving Inhabited

@[nospecialize]
def setupCharPoly [HolBase] (D : DeterminantsDeps) (BTrace : Trace) (BDetBasic : DetBasic)
    (BInvertibility : Invertibility) (BLowDim : LowDim) : ExceptT String IO CharPoly := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, REAL_ARITH, REAL_ARITH_TAC,
        REAL_RAT_REDUCE_CONV, .. } := D
  let { ADD1, ADD_SUB, ARITH_EQ, COND_ID, COND_RAND, CONJ_SYM, FINITE_NUMSEG,
        FORALL_IN_IMAGE, FUN_EQ_THM, IMAGE_I, IMP_CONJ, IN_DELETE, IN_ELIM_THM, IN_NUMSEG,
        LE, LEFT_FORALL_IMP_THM, LEFT_IMP_EXISTS_THM, LE_0, .. } := D.core1
  let { LE_REFL, NOT_SUC, REAL_ADD_LID, REAL_ADD_RID, REAL_ENTIRE, REAL_MUL_AC,
        REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RZERO,
        REAL_POLYFUN_FINITE_ROOTS, .. } := D.core2
  let { REAL_POW_1, REAL_POW_ADD, REAL_POW_EQ_0, REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB,
        REAL_SUB_RZERO, RIGHT_FORALL_IMP_THM, SKOLEM_THM, SUBSET, SUBSET_REFL, SUC_SUB1,
        SUM_CLAUSES_LEFT, SUM_CLAUSES_NUMSEG, SUM_DELETE, SUM_EQ, SUM_EQ_0, SUM_EQ_NUMSEG,
        SUM_LMUL, SUM_OFFSET, SUM_RMUL, SUM_SUB_NUMSEG, SUM_SWAP, SWAP_FORALL_THM, real_pow,
        .. } := D.core3
  let { CONTRAPOS_THM, FORALL_UNWIND_THM2, I_THM, RIGHT_IMP_EXISTS_THM, .. } := D.core4
  let { MATRIX_CMUL_COMPONENT, MATRIX_CMUL_LZERO, .. } := D.vec1
  let { MATRIX_NEG_SUB, MATRIX_SUB_COMPONENT, MATRIX_SUB_RZERO, MATRIX_VECTOR_LMUL,
        MATRIX_VECTOR_MUL_LID, MATRIX_VECTOR_MUL_SUB_RDISTRIB, MAT_COMPONENT, .. } := D.vec2
  let { VECTOR_2, VECTOR_3, VECTOR_4, VECTOR_SUB_EQ, .. } := D.vec3
  let { FINITE_PERMUTATIONS, INTEGER_CLOSED, INTEGER_MUL, INTEGER_SUM, PERMUTES_I,
        PERMUTES_IMAGE, PRODUCT_CLAUSES_NUMSEG, PRODUCT_CLOSED, SIGN_I, permutes, sign,
        .. } := D.lib
  let { det, .. } := BTrace
  let { DET_NEG, .. } := BDetBasic
  let { HOMOGENEOUS_LINEAR_EQUATIONS_DET, INVERTIBLE_DET_NZ, .. } := BInvertibility
  let { DET_2, DET_3, DET_4, .. } := BLowDim
  -- @@SCOPE END
  let ar (s : String) : ExceptT String IO thm := do ARITH_RULE (← q s)

  let EIGENVALUES_CHARACTERISTIC_ALT ← prove
   r"!A:real^N^N c.
        (?v. ~(v = vec 0) /\ A ** v = c % v) <=> det(A - c %% mat 1) = &0"
   (REWRITE_TAC [← GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
    REWRITE_TAC [MATRIX_VECTOR_MUL_SUB_RDISTRIB] THEN
    REWRITE_TAC [MATRIX_VECTOR_LMUL, VECTOR_SUB_EQ, MATRIX_VECTOR_MUL_LID])

  let EIGENVALUES_CHARACTERISTIC ← prove
   r"!A:real^N^N c.
        (?v. ~(v = vec 0) /\ A ** v = c % v) <=> det(c %% mat 1 - A) = &0"
   (ONCE_REWRITE_TAC [← GSYM MATRIX_NEG_SUB] THEN
    ASM_REWRITE_TAC [EIGENVALUES_CHARACTERISTIC_ALT, DET_NEG] THEN
    REWRITE_TAC [REAL_ENTIRE, REAL_POW_EQ_0] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV)

  let INVERTIBLE_EIGENVALUES ← prove
   r"!A:real^N^N.
        invertible(A) <=> !c v. A ** v = c % v /\ ~(v = vec 0) ==> ~(c = &0)"
   (GEN_TAC THEN REWRITE_TAC [LEFT_FORALL_IMP_THM] THEN
    ONCE_REWRITE_TAC [CONJ_SYM] THEN
    REWRITE_TAC [EIGENVALUES_CHARACTERISTIC_ALT, INVERTIBLE_DET_NZ] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [FORALL_UNWIND_THM2, MATRIX_CMUL_LZERO, MATRIX_SUB_RZERO])

  let CHARACTERISTIC_POLYNOMIAL ← prove
   r"!A:real^N^N.
        ?a. a(dimindex(:N)) = &1 /\
            !x. det(x %% mat 1 - A) =
                sum (0..dimindex(:N)) (\i. a i * x pow i)"
   (GEN_TAC THEN REWRITE_TAC [det] THEN
    SUBGOAL_THEN
     (← q r"!p n. IMAGE p (1..dimindex(:N)) SUBSET 1..dimindex(:N) /\
          n <= dimindex(:N)
          ==> ?a. a n = (if !i. 1 <= i /\ i <= n ==> p i = i then &1 else &0) /\
                  !x. product (1..n) (\i. (x %% mat 1 - A:real^N^N)$i$p i) =
                      sum (0..n) (\i. a i * x pow i)")
    MP_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
      DISCH_TAC THEN INDUCT_TAC THEN
      REWRITE_TAC [PRODUCT_CLAUSES_NUMSEG] THEN
      REWRITE_TAC [LE_0, ARITH_EQ, ← ar r"1 <= SUC n"] THENL
       [EXISTS_TAC (← q r"\i. if i = 0 then &1 else &0") THEN
        SIMP_TAC [real_pow, REAL_MUL_LID, ← ar r"1 <= i ==> ~(i <= 0)",
                  SUM_CLAUSES_NUMSEG],
        DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o check (HolCore.Basics.is_imp o concl)) THEN
        ASM_SIMP_TAC [← ar r"SUC n <= N ==> n <= N"] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"a:num->real") STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [MATRIX_SUB_COMPONENT, MATRIX_CMUL_COMPONENT] THEN
        ASSUME_TAC (← ar r"1 <= SUC n") THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [SUBSET]) THEN
        REWRITE_TAC [FORALL_IN_IMAGE, IN_NUMSEG] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"SUC n")) THEN ASM_REWRITE_TAC [] THEN
        STRIP_TAC THEN ASM_SIMP_TAC [MAT_COMPONENT] THEN
        ASM_CASES_TAC (← q r"p(SUC n) = SUC n") THEN ASM_REWRITE_TAC [] THENL
         [ALL_TAC,
          EXISTS_TAC (← q r"\i. if i <= n
                        then --((A:real^N^N)$(SUC n)$(p(SUC n))) * a i
                        else &0") THEN
          SIMP_TAC [SUM_CLAUSES_NUMSEG, LE_0, ← ar r"~(SUC n <= n)"] THEN
          CONJ_TAC THENL
           [COND_CASES_TAC THEN REWRITE_TAC [] THEN
            FIRST_X_ASSUM (MP_TAC o SPEC (← q r"SUC n")) THEN
            ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
            REWRITE_TAC [REAL_MUL_LZERO, REAL_ADD_RID, ← GSYM SUM_RMUL] THEN
            GEN_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN REWRITE_TAC [] THEN
            REAL_ARITH_TAC]] THEN
        REWRITE_TAC [REAL_SUB_LDISTRIB, REAL_MUL_RID] THEN
        REWRITE_TAC [← GSYM SUM_RMUL] THEN EXISTS_TAC
        (← q r"\i. (if i = 0 then &0 else a(i - 1)) -
           (if i = SUC n then &0 else (A:real^N^N)$(SUC n)$(SUC n) * a i)") THEN
        ASM_REWRITE_TAC [NOT_SUC, LE, SUC_SUB1, REAL_SUB_RZERO] THEN
        CONJ_TAC THENL [ASM_MESON_TAC [LE_REFL], ALL_TAC] THEN
        REWRITE_TAC [REAL_SUB_RDISTRIB, SUM_SUB_NUMSEG] THEN
        GEN_TAC THEN BINOP_TAC THENL
         [SIMP_TAC [SUM_CLAUSES_LEFT, ← ar r"0 <= SUC n"] THEN
          REWRITE_TAC [ADD1, SUM_OFFSET, ← ar r"~(i + 1 = 0)", ADD_SUB] THEN
          REWRITE_TAC [REAL_MUL_LZERO, REAL_POW_ADD, REAL_POW_1, REAL_ADD_LID],
          SIMP_TAC [SUM_CLAUSES_NUMSEG, LE_0, REAL_MUL_LZERO, REAL_ADD_RID] THEN
          SIMP_TAC [← ar r"i <= n ==> ~(i = SUC n)"]] THEN
        MATCH_MP_TAC SUM_EQ_NUMSEG THEN REWRITE_TAC [REAL_ADD_LID, REAL_MUL_AC]],
      GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"dimindex(:N)")) THEN REWRITE_TAC [LE_REFL] THEN
      GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
      REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"a:(num->num)->num->real") THEN DISCH_TAC] THEN
    EXISTS_TAC
     (← q r"\i:num. sum {p | p permutes 1..dimindex(:N)} (\p. sign p * a p i)") THEN
    REWRITE_TAC [] THEN CONJ_TAC THENL
     [MP_TAC (← ISPECL
       [← q r"\p:num->num. sign p * a p (dimindex(:N))",
        ← q r"{p | p permutes 1..dimindex(:N)}",
        ← q r"I:num->num"] SUM_DELETE) THEN
      SIMP_TAC [IN_ELIM_THM, PERMUTES_I, FINITE_PERMUTATIONS, FINITE_NUMSEG] THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"k = &1 /\ s' = &0 ==> s' = s - k ==> s = &1")) THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"I:num->num")) THEN
        SIMP_TAC [IMAGE_I, SUBSET_REFL, SIGN_I, I_THM, REAL_MUL_LID],
        MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC (← q r"p:num->num") THEN
        REWRITE_TAC [IN_ELIM_THM, IN_DELETE] THEN STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"p:num->num")) THEN ANTS_TAC THENL
         [ASM_MESON_TAC [PERMUTES_IMAGE, SUBSET_REFL], ALL_TAC] THEN
        COND_CASES_TAC THEN SIMP_TAC [REAL_MUL_RZERO] THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [permutes]) THEN
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [FUN_EQ_THM]) THEN
        REWRITE_TAC [IN_NUMSEG, I_THM] THEN ASM_MESON_TAC []],
      X_GEN_TAC (← q r"x:real") THEN REWRITE_TAC [← GSYM SUM_RMUL] THEN
      W (MP_TAC o PART_MATCH (lhs o rand) SUM_SWAP o rand o snd) THEN
      SIMP_TAC [FINITE_PERMUTATIONS, FINITE_NUMSEG] THEN
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ THEN
      X_GEN_TAC (← q r"p:num->num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN
      REWRITE_TAC [← GSYM REAL_MUL_ASSOC, SUM_LMUL] THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"p:num->num")) THEN ANTS_TAC THENL
       [ASM_MESON_TAC [PERMUTES_IMAGE, SUBSET_REFL], SIMP_TAC []]])

  let FINITE_EIGENVALUES ← prove
   r"!A:real^N^N. FINITE {c | ?v. ~(v = vec 0) /\ A ** v = c % v}"
   (GEN_TAC THEN REWRITE_TAC [EIGENVALUES_CHARACTERISTIC] THEN
    MP_TAC (← ISPEC (← q r"A:real^N^N") CHARACTERISTIC_POLYNOMIAL) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [REAL_POLYFUN_FINITE_ROOTS] THEN EXISTS_TAC (← q r"dimindex(:N)") THEN
    ASM_REWRITE_TAC [IN_NUMSEG, LE_0, LE_REFL] THEN REAL_ARITH_TAC)

  let GRASSMANN_PLUCKER_2 ← prove
   r"!x1 x2 y1 y2:real^2.
        det(vector[x1;x2]) * det(vector[y1;y2]) =
          det(vector[y1;x2]) * det(vector[x1;y2]) +
          det(vector[y2;x2]) * det(vector[y1;x1])"
   (REWRITE_TAC [DET_2, VECTOR_2] THEN REAL_ARITH_TAC)

  let GRASSMANN_PLUCKER_3 ← prove
   r"!x1 x2 x3 y1 y2 y3:real^3.
        det(vector[x1;x2;x3]) * det(vector[y1;y2;y3]) =
          det(vector[y1;x2;x3]) * det(vector[x1;y2;y3]) +
          det(vector[y2;x2;x3]) * det(vector[y1;x1;y3]) +
          det(vector[y3;x2;x3]) * det(vector[y1;y2;x1])"
   (REWRITE_TAC [DET_3, VECTOR_3] THEN REAL_ARITH_TAC)

  let GRASSMANN_PLUCKER_4 ← prove
   r"!x1 x2 x3 x4:real^4 y1 y2 y3 y4:real^4.
        det(vector[x1;x2;x3;x4]) * det(vector[y1;y2;y3;y4]) =
          det(vector[y1;x2;x3;x4]) * det(vector[x1;y2;y3;y4]) +
          det(vector[y2;x2;x3;x4]) * det(vector[y1;x1;y3;y4]) +
          det(vector[y3;x2;x3;x4]) * det(vector[y1;y2;x1;y4]) +
          det(vector[y4;x2;x3;x4]) * det(vector[y1;y2;y3;x1])"
   (REWRITE_TAC [DET_4, VECTOR_4] THEN REAL_ARITH_TAC)

  let INTEGER_PRODUCT ← prove
   r"!f s. (!x. x IN s ==> integer(f x)) ==> integer(product s f)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_CLOSED THEN
    ASM_REWRITE_TAC [INTEGER_CLOSED])

  let INTEGER_SIGN ← prove
   r"!p. integer(sign p)"
   (SIMP_TAC [sign, COND_RAND, INTEGER_CLOSED, COND_ID])

  let INTEGER_DET ← prove
   r"!M:real^N^N.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N)
               ==> integer(M$i$j))
        ==> integer(det M)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [det] THEN
    MATCH_MP_TAC INTEGER_SUM THEN X_GEN_TAC (← q r"p:num->num") THEN
    REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC INTEGER_MUL THEN REWRITE_TAC [INTEGER_SIGN] THEN
    MATCH_MP_TAC INTEGER_PRODUCT THEN REWRITE_TAC [IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC [IN_NUMSEG, permutes])

  return { EIGENVALUES_CHARACTERISTIC_ALT, EIGENVALUES_CHARACTERISTIC, INVERTIBLE_EIGENVALUES,
           CHARACTERISTIC_POLYNOMIAL, FINITE_EIGENVALUES, GRASSMANN_PLUCKER_2,
           GRASSMANN_PLUCKER_3, GRASSMANN_PLUCKER_4, INTEGER_PRODUCT, INTEGER_SIGN,
           INTEGER_DET }

/- ------------------------------------------------------------------------- -/
/- Diagonal matrices (for arbitrary rectangular matrix, not just square).    -/
/- (determinants.ml 1703-1933)                                                -/
/- ------------------------------------------------------------------------- -/

structure Diagonal where
  diagonal_matrix : thm
  DIAGONAL_MATRIX : thm
  DIAGONAL_MATRIX_MAT : thm
  TRANSP_DIAGONAL_MATRIX : thm
  DIAGONAL_IMP_SYMMETRIC_MATRIX : thm
  DIAGONAL_MATRIX_ADD : thm
  DIAGONAL_MATRIX_CMUL : thm
  MATRIX_MUL_DIAGONAL : thm
  DIAGONAL_MATRIX_MUL_COMPONENT : thm
  DIAGONAL_MATRIX_MUL : thm
  DIAGONAL_MATRIX_MUL_EQ : thm
  DIAGONAL_MATRIX_INV_EXPLICIT : thm
  DIAGONAL_MATRIX_INV_COMPONENT : thm
  DIAGONAL_MATRIX_INV : thm
  DET_DIAGONAL : thm
  INVERTIBLE_DIAGONAL_MATRIX : thm
  COMMUTING_WITH_DIAGONAL_MATRIX : thm
  RANK_DIAGONAL_MATRIX : thm
  ONORM_DIAGONAL_MATRIX : thm
  deriving Inhabited

@[nospecialize]
def setupDiagonal [HolBase] (D : DeterminantsDeps) (BDetBasic : DetBasic)
    (BInvertibility : Invertibility) : ExceptT String IO Diagonal := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD, REAL_RING,
        SET_RULE, SET_TAC, new_definition, .. } := D
  let { CARD_IMAGE_INJ, CART_EQ, COND_ID, COND_RAND, COND_RATOR, CONJ_ASSOC, DIMINDEX_GE_1,
        EQ_TRANS, FINITE_NUMSEG, FINITE_RESTRICT, FORALL_IN_GSPEC, IMAGE_o, IMP_CONJ,
        IN_ELIM_THM, IN_NUMSEG, LAMBDA_BETA, .. } := D.core1
  let { LE_REFL, LT_REFL, REAL_ABS_MUL, REAL_ABS_POS, REAL_ADD_LID, REAL_ADD_RID,
        REAL_EQ_MUL_RCANCEL, REAL_INV_0, REAL_INV_EQ_0, REAL_LE_RMUL, REAL_LE_TRANS,
        REAL_MUL_LINV, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_MUL_SYM, .. } := D.core2
  let { SIMPLE_IMAGE, SIMPLE_IMAGE_GEN, SUBSET, SUBSET_ANTISYM_EQ, SUM_0, SUM_DELTA, SUP_EQ,
        o_DEF, pairwise, .. } := D.core3
  let { BASIS_COMPONENT, BASIS_INJ_EQ, BASIS_NONZERO, COMPONENT_LE_NORM, DIM_EQ_CARD,
        DIM_INSERT_0, DIM_SPAN, INDEPENDENT_MONO, INDEPENDENT_STDBASIS,
        MATRIX_ADD_COMPONENT, MATRIX_CMUL_COMPONENT, .. } := D.vec1
  let { MATRIX_INV_INV, MATRIX_INV_UNIQUE_STRONG, MATRIX_VECTOR_MUL_BASIS,
        MATRIX_VECTOR_MUL_COMPONENT, MATRIX_VECTOR_MUL_LINEAR, NORM_BASIS,
        NORM_LE_COMPONENTWISE, NORM_MUL, RANK_DIM_IM, .. } := D.vec2
  let { SPAN_EQ_DIM, SPAN_LINEAR_IMAGE, SPAN_MUL, SPAN_STDBASIS, SPAN_SUBSET_SUBSPACE,
        SPAN_SUPERSET, SUBSPACE_SPAN, TRANSP_COMPONENT, VECTOR_MUL_ASSOC,
        VECTOR_MUL_COMPONENT, VECTOR_MUL_EQ_0, VECTOR_MUL_LID, column, dot, mat, matrix_mul,
        matrix_vector_mul, onorm, orthogonal, row, symmetric_matrix, .. } := D.vec3
  let { PRODUCT_EQ_0, .. } := D.lib
  let { DET_LOWERTRIANGULAR, .. } := BDetBasic
  let { INVERTIBLE_DET_NZ, .. } := BInvertibility
  -- @@SCOPE END

  let diagonal_matrix ← new_definition
   r"diagonal_matrix(A:real^N^M) <=>
        !i j. 1 <= i /\ i <= dimindex(:M) /\
              1 <= j /\ j <= dimindex(:N) /\
              ~(i = j)
              ==> A$i$j = &0"

  let DIAGONAL_MATRIX ← prove
   r"!A:real^N^N.
     diagonal_matrix A <=> A = (lambda i j. if i = j then A$i$j else &0)"
   (SIMP_TAC [CART_EQ, LAMBDA_BETA, diagonal_matrix] THEN MESON_TAC [])

  let DIAGONAL_MATRIX_MAT ← prove
   r"!m. diagonal_matrix(mat m:real^N^N)"
   (SIMP_TAC [mat, diagonal_matrix, LAMBDA_BETA])

  let TRANSP_DIAGONAL_MATRIX ← prove
   r"!A:real^N^N. diagonal_matrix A ==> transp A = A"
   (GEN_TAC THEN REWRITE_TAC [diagonal_matrix, CART_EQ, TRANSP_COMPONENT] THEN
    STRIP_TAC THEN X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN X_GEN_TAC (← q r"j:num") THEN
    STRIP_TAC THEN ASM_CASES_TAC (← q r"i:num = j") THEN ASM_SIMP_TAC [])

  let DIAGONAL_IMP_SYMMETRIC_MATRIX ← prove
   r"!A:real^N^N. diagonal_matrix A ==> symmetric_matrix A"
   (REWRITE_TAC [symmetric_matrix, TRANSP_DIAGONAL_MATRIX])

  let DIAGONAL_MATRIX_ADD ← prove
   r"!A B:real^N^M.
        diagonal_matrix A /\ diagonal_matrix B
        ==> diagonal_matrix(A + B)"
   (SIMP_TAC [diagonal_matrix, MATRIX_ADD_COMPONENT,
              REAL_ADD_LID, REAL_ADD_RID])

  let DIAGONAL_MATRIX_CMUL ← prove
   r"!A:real^N^M c.
        diagonal_matrix A ==> diagonal_matrix(c %% A)"
   (SIMP_TAC [diagonal_matrix, MATRIX_CMUL_COMPONENT, REAL_MUL_RZERO])

  let MATRIX_MUL_DIAGONAL ← prove
   r"!A:real^N^N B:real^N^N.
        diagonal_matrix A /\ diagonal_matrix B
        ==> A ** B = lambda i j. A$i$j * B$i$j"
   (REPEAT STRIP_TAC THEN
    REPEAT (FIRST_X_ASSUM (SUBST1_TAC o GEN_REWRITE_RULE id [DIAGONAL_MATRIX])) THEN
    SIMP_TAC [CART_EQ, matrix_mul, LAMBDA_BETA] THEN
    ONCE_REWRITE_TAC [← MESON [REAL_MUL_LZERO, REAL_MUL_RZERO] (← q
     r"(if p then a else &0) * (if q then b else &0) =
    if q then (if p then a * b else &0) else &0")] THEN
    SIMP_TAC [SUM_DELTA, IN_NUMSEG, COND_ID, SUM_0])

  let DIAGONAL_MATRIX_MUL_COMPONENT ← prove
   r"!A:real^N^N B:real^N^N i j.
        diagonal_matrix A /\ diagonal_matrix B /\
        1 <= i /\ i <= dimindex(:N) /\
        1 <= j /\ j <= dimindex(:N)
        ==> (A ** B)$i$j = A$i$j * B$i$j"
   (ASM_SIMP_TAC [MATRIX_MUL_DIAGONAL, LAMBDA_BETA])

  let DIAGONAL_MATRIX_MUL ← prove
   r"!A:real^N^N B:real^N^N.
        diagonal_matrix A /\ diagonal_matrix B
        ==> diagonal_matrix(A ** B)"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [diagonal_matrix] THEN
    SIMP_TAC [DIAGONAL_MATRIX_MUL_COMPONENT] THEN
    SIMP_TAC [diagonal_matrix, REAL_MUL_LZERO])

  let DIAGONAL_MATRIX_MUL_EQ ← prove
   r"!A:real^M^N B:real^N^M.
        diagonal_matrix (A ** B) <=>
        pairwise (\i j. orthogonal (row i A) (column j B)) (1..dimindex(:N))"
   (REWRITE_TAC [diagonal_matrix, matrix_mul, pairwise] THEN
    SIMP_TAC [LAMBDA_BETA, IN_NUMSEG, orthogonal, dot, row, column] THEN
    REWRITE_TAC [← GSYM CONJ_ASSOC])

  let DIAGONAL_MATRIX_INV_EXPLICIT ← prove
   r"!A:real^N^N. diagonal_matrix A ==> matrix_inv A = lambda i j. inv(A$i$j)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN
    REWRITE_TAC [symmetric_matrix] THEN
    SUBGOAL_THEN
     (← q r"diagonal_matrix((lambda i j. inv((A:real^N^N)$i$j)):real^N^N)")
    ASSUME_TAC THENL
     [RULE_ASSUM_TAC (REWRITE_RULE [diagonal_matrix]) THEN
      ASM_SIMP_TAC [diagonal_matrix, LAMBDA_BETA, REAL_INV_0],
      ASM_SIMP_TAC [DIAGONAL_MATRIX_MUL_COMPONENT, CART_EQ, LAMBDA_BETA,
                    TRANSP_COMPONENT, DIAGONAL_MATRIX_MUL]] THEN
    MP_TAC (← ISPEC (← q r"A:real^N^N") DIAGONAL_MATRIX) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN SIMP_TAC [LAMBDA_BETA] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"j:num") THEN STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [REAL_INV_0, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
    REWRITE_TAC [REAL_INV_EQ_0, ← REAL_RING (← q
      r"a * b * a = a <=> b * a = &1 \/ a = &0")] THEN
    CONV_TAC (fun t => REAL_FIELD t))

  let DIAGONAL_MATRIX_INV_COMPONENT ← prove
   r"!A:real^N^N i j.
        diagonal_matrix A /\
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> (matrix_inv A)$i$j = inv(A$i$j)"
   (ASM_SIMP_TAC [DIAGONAL_MATRIX_INV_EXPLICIT, LAMBDA_BETA])

  let DIAGONAL_MATRIX_INV ← prove
   r"!A:real^N^N. diagonal_matrix(matrix_inv A) <=> diagonal_matrix A"
   (SUBGOAL_THEN
     (← q r"!A:real^N^N. diagonal_matrix A ==> diagonal_matrix(matrix_inv A)")
    MP_TAC THENL [REPEAT STRIP_TAC, MESON_TAC [MATRIX_INV_INV]] THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP DIAGONAL_MATRIX_INV_EXPLICIT) THEN
    POP_ASSUM MP_TAC THEN SIMP_TAC [diagonal_matrix, LAMBDA_BETA] THEN
    REWRITE_TAC [REAL_INV_0])

  let DET_DIAGONAL ← prove
   r"!A:real^N^N.
        diagonal_matrix A
        ==> det(A) = product(1..dimindex(:N)) (\i. A$i$i)"
   (REWRITE_TAC [diagonal_matrix] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC DET_LOWERTRIANGULAR THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [LT_REFL])

  let INVERTIBLE_DIAGONAL_MATRIX ← prove
   r"!D:real^N^N.
        diagonal_matrix D
        ==> (invertible D <=>
             !i. 1 <= i /\ i <= dimindex(:N) ==> ~(D$i$i = &0))"
   (SIMP_TAC [INVERTIBLE_DET_NZ, DET_DIAGONAL] THEN
    SIMP_TAC [PRODUCT_EQ_0, FINITE_NUMSEG, IN_NUMSEG] THEN MESON_TAC [])

  let COMMUTING_WITH_DIAGONAL_MATRIX ← prove
   r"!A D:real^N^N.
        diagonal_matrix D
        ==> (A ** D = D ** A <=>
             !i j. 1 <= i /\ i <= dimindex(:N) /\
                   1 <= j /\ j <= dimindex(:N)
                   ==> A$i$j = &0 \/ D$i$i = D$j$j)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (SUBST1_TAC o REWRITE_RULE [DIAGONAL_MATRIX]) THEN
    SIMP_TAC [CART_EQ, matrix_mul, LAMBDA_BETA] THEN
    REWRITE_TAC [← MESON [REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_MUL_SYM] (← q
     r"(if a = b then x else &0) * y = (if b = a then x * y else &0) /\
    y * (if a = b then x else &0) = (if a = b then x * y else &0)")] THEN
    SIMP_TAC [SUM_DELTA, IN_NUMSEG, REAL_EQ_MUL_RCANCEL] THEN MESON_TAC [])

  let RANK_DIAGONAL_MATRIX ← prove
   r"!A:real^N^N.
        diagonal_matrix A
        ==> rank A = CARD {i | i IN 1..dimindex(:N) /\ ~(A$i$i = &0)}"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [RANK_DIM_IM, ← GSYM SPAN_STDBASIS] THEN
    SIMP_TAC [← GSYM SPAN_LINEAR_IMAGE, MATRIX_VECTOR_MUL_LINEAR, DIM_SPAN] THEN
    REWRITE_TAC [← GSYM IN_NUMSEG, SIMPLE_IMAGE, ← GSYM IMAGE_o, o_DEF] THEN
    TRANS_TAC EQ_TRANS
      (← q r"dim {(A:real^N^N)$i$i % basis i:real^N | i IN 1..dimindex(:N)}") THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC (← SET_RULE (← q
       r"(!x. x IN s ==> f x = g x) ==> IMAGE f s = {g x | x IN s}")) THEN
      FIRST_ASSUM (SUBST1_TAC o GEN_REWRITE_RULE id [DIAGONAL_MATRIX]) THEN
      SIMP_TAC [matrix_vector_mul, LAMBDA_BETA, IN_NUMSEG, CART_EQ] THEN
      ONCE_REWRITE_TAC [← MESON [REAL_MUL_LZERO] (← q
       r"(if i = j then a else &0) * b = if j = i then a * b else &0")] THEN
      SIMP_TAC [SUM_DELTA, IN_NUMSEG, BASIS_COMPONENT, VECTOR_MUL_COMPONENT] THEN
      MESON_TAC [REAL_MUL_RZERO],
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     (← q r"dim {(A:real^N^N)$i$i % basis i:real^N |i|
          i IN 1..dimindex(:N) /\ ~(A$i$i = &0)}") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC (← MESON [DIM_INSERT_0] (← q
      r"(vec 0:real^N) INSERT s = (vec 0:real^N) INSERT t ==> dim s = dim t")) THEN
      MATCH_MP_TAC (← SET_RULE (← q
       r"t SUBSET s /\ (!x. x IN s ==> ~(x IN t) ==> x = a)
      ==> a INSERT s = a INSERT t")) THEN
      CONJ_TAC THENL [SET_TAC [], REWRITE_TAC [FORALL_IN_GSPEC]] THEN
      SIMP_TAC [VECTOR_MUL_EQ_0, IN_ELIM_THM, BASIS_NONZERO, IN_NUMSEG] THEN
      SET_TAC [],
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
    (← q r"dim{basis i:real^N | i IN 1..dimindex(:N) /\ ~((A:real^N^N)$i$i = &0)}") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SPAN_EQ_DIM THEN REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN
      CONJ_TAC THEN MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
      REWRITE_TAC [SUBSPACE_SPAN] THEN
      REWRITE_TAC [FORALL_IN_GSPEC, SUBSET, IN_NUMSEG] THEN
      X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THENL
       [ALL_TAC,
        SUBGOAL_THEN
         (← q r"basis i:real^N = inv((A:real^N^N)$i$i) % A$i$i % basis i")
         (fun th => GEN_REWRITE_TAC LAND_CONV [th])
        THENL [ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, VECTOR_MUL_LID],
               ALL_TAC]] THEN
      MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN ASM SET_TAC [],
      ALL_TAC] THEN
    W (MP_TAC o PART_MATCH (lhs o rand) DIM_EQ_CARD o lhand o snd) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC (← MATCH_MP (← REWRITE_RULE [IMP_CONJ] INDEPENDENT_MONO)
          INDEPENDENT_STDBASIS) THEN
      REWRITE_TAC [IN_NUMSEG] THEN SET_TAC [],
      DISCH_THEN SUBST1_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SIMPLE_IMAGE_GEN] THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN
    SIMP_TAC [FINITE_RESTRICT, FINITE_NUMSEG, IN_ELIM_THM, IN_NUMSEG] THEN
    REWRITE_TAC [IMP_CONJ] THEN SIMP_TAC [BASIS_INJ_EQ])

  let ONORM_DIAGONAL_MATRIX ← prove
   r"!A:real^N^N.
       diagonal_matrix A
       ==> onorm(\x. A ** x) = sup {abs(A$i$i) | 1 <= i /\ i <= dimindex(:N)}"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [onorm] THEN MATCH_MP_TAC SUP_EQ THEN
    X_GEN_TAC (← q r"b:real") THEN REWRITE_TAC [FORALL_IN_GSPEC] THEN
    EQ_TAC THEN DISCH_TAC THENL
     [X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"basis i:real^N")) THEN
      ASM_SIMP_TAC [NORM_BASIS, MATRIX_VECTOR_MUL_BASIS] THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← MESON [COMPONENT_LE_NORM, REAL_LE_TRANS] (← q
       r"norm(x) <= b ==> !i. abs(x$i) <= b"))) THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"i:num")) THEN ASM_SIMP_TAC [column, LAMBDA_BETA],
      X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      TRANS_TAC REAL_LE_TRANS (← q r"norm(b % x:real^N)") THEN CONJ_TAC THENL
       [MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
        FIRST_X_ASSUM (SUBST_ALL_TAC o GEN_REWRITE_RULE id [DIAGONAL_MATRIX]) THEN
        FIRST_X_ASSUM (fun th => tactic_of do
          let _ ← SYM th
          pure ALL_TAC) THEN POP_ASSUM MP_TAC THEN
        SIMP_TAC [LAMBDA_BETA, MATRIX_VECTOR_MUL_COMPONENT, dot] THEN
        REWRITE_TAC [COND_RAND, COND_RATOR, REAL_MUL_LZERO] THEN
        CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
        SIMP_TAC [SUM_DELTA, IN_NUMSEG] THEN
        REWRITE_TAC [REAL_ABS_MUL, VECTOR_MUL_COMPONENT] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        REWRITE_TAC [REAL_ABS_POS] THEN
        MATCH_MP_TAC (← REAL_ARITH (← q r"x <= b ==> x <= abs b")) THEN
        ASM_SIMP_TAC [],
        ASM_REWRITE_TAC [NORM_MUL] THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"1")) THEN
        ASM_REWRITE_TAC [DIMINDEX_GE_1, LE_REFL] THEN REAL_ARITH_TAC]])

  return { diagonal_matrix, DIAGONAL_MATRIX, DIAGONAL_MATRIX_MAT, TRANSP_DIAGONAL_MATRIX,
           DIAGONAL_IMP_SYMMETRIC_MATRIX, DIAGONAL_MATRIX_ADD, DIAGONAL_MATRIX_CMUL,
           MATRIX_MUL_DIAGONAL, DIAGONAL_MATRIX_MUL_COMPONENT, DIAGONAL_MATRIX_MUL,
           DIAGONAL_MATRIX_MUL_EQ, DIAGONAL_MATRIX_INV_EXPLICIT, DIAGONAL_MATRIX_INV_COMPONENT,
           DIAGONAL_MATRIX_INV, DET_DIAGONAL, INVERTIBLE_DIAGONAL_MATRIX,
           COMMUTING_WITH_DIAGONAL_MATRIX, RANK_DIAGONAL_MATRIX, ONORM_DIAGONAL_MATRIX }

/- ------------------------------------------------------------------------- -/
/- Positive semidefinite matrices.  (determinants.ml 1939-2134)              -/
/- ------------------------------------------------------------------------- -/

structure Psd where
  positive_semidefinite : thm
  POSITIVE_SEMIDEFINITE_IMP_SYMMETRIC_MATRIX : thm
  POSITIVE_SEMIDEFINITE_IMP_SYMMETRIC : thm
  POSITIVE_SEMIDEFINITE_ADD : thm
  POSITIVE_SEMIDEFINITE_CMUL : thm
  POSITIVE_SEMIDEFINITE_TRANSP : thm
  POSITIVE_SEMIDEFINITE_COVARIANCE : thm
  POSITIVE_SEMIDEFINITE_SIMILAR : thm
  POSITIVE_SEMIDEFINITE_SIMILAR_EQ : thm
  POSITIVE_SEMIDEFINITE_DIAGONAL_MATRIX : thm
  POSITIVE_SEMIDEFINITE_DIAGONAL_MATRIX_EQ : thm
  DIAGONAL_POSITIVE_SEMIDEFINITE : thm
  TRACE_POSITIVE_SEMIDEFINITE : thm
  TRACE_LE_MUL_SQUARES : thm
  POSITIVE_SEMIDEFINITE_ZERO_FORM : thm
  POSITIVE_SEMIDEFINITE_ZERO_FORM_EQ : thm
  POSITIVE_SEMIDEFINITE_1_GEN : thm
  POSITIVE_SEMIDEFINITE_1 : thm
  POSITIVE_SEMIDEFINITE_SUBMATRIX_2 : thm
  deriving Inhabited

@[nospecialize]
def setupPsd [HolBase] (D : DeterminantsDeps) (BTrace : Trace) (BDiagonal : Diagonal) :
    ExceptT String IO Psd := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, SET_RULE, new_definition,
        .. } := D
  let { ARITH, ARITH_EQ, CART_EQ, COND_RAND, COND_RATOR, DIMINDEX_1, DIMINDEX_2,
        DIMINDEX_GE_1, FINITE_NUMSEG, IN_ELIM_THM, IN_NUMSEG, LAMBDA_BETA, .. } := D.core1
  let { LE_REFL, REAL_DIV_LMUL, REAL_ENTIRE, REAL_LE_ADD, REAL_LE_MUL, REAL_LE_POW_2,
        REAL_LE_SQUARE, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_MUL_SYM, REAL_OF_NUM_EQ,
        .. } := D.core2
  let { SUM_CASES, SUM_DELTA, SUM_POS_LE_NUMSEG, SUM_SING, .. } := D.core3
  let { CONTRAPOS_THM, .. } := D.core4
  let { BASIS_COMPONENT, DOT_2, DOT_BASIS, DOT_EQ_0, DOT_LADD, DOT_LMUL, DOT_LMUL_MATRIX,
        DOT_POS_LE, DOT_RADD, DOT_RMUL, DOT_RZERO, FORALL_1, FORALL_2, .. } := D.vec1
  let { MATRIX_INV, MATRIX_MUL_ASSOC, MATRIX_MUL_LID, MATRIX_MUL_RID, MATRIX_SUB_LDISTRIB,
        MATRIX_SUB_RDISTRIB, MATRIX_TRANSP_MUL, MATRIX_VECTOR_LMUL,
        MATRIX_VECTOR_MUL_ADD_LDISTRIB, MATRIX_VECTOR_MUL_ADD_RDISTRIB,
        MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_BASIS, MATRIX_VECTOR_MUL_COMPONENT,
        MATRIX_VECTOR_MUL_RMUL, MATRIX_VECTOR_MUL_TRANSP, .. } := D.vec2
  let { SUM_1, SUM_2, SYMMETRIC_MATRIX_ADD, SYMMETRIC_MATRIX_CMUL, TRANSP_MAT,
        TRANSP_MATRIX_SUB, TRANSP_TRANSP, VECTOR_2, VECTOR_MATRIX_MUL_TRANSP, column, dot,
        matrix_vector_mul, symmetric_matrix, transp, .. } := D.vec3
  let { TRACE_MUL_SYM, TRACE_SUB, trace, .. } := BTrace
  let { DIAGONAL_IMP_SYMMETRIC_MATRIX, DIAGONAL_MATRIX, .. } := BDiagonal
  -- @@SCOPE END
  let ra (s : String) : ExceptT String IO thm := do REAL_ARITH (← q s)

  let positive_semidefinite ← new_definition
   r"positive_semidefinite(A:real^N^N) <=>
    symmetric_matrix A /\ !x. &0 <= x dot (A ** x)"

  let POSITIVE_SEMIDEFINITE_IMP_SYMMETRIC_MATRIX ← prove
   r"!A:real^N^N. positive_semidefinite A ==> symmetric_matrix A"
   (SIMP_TAC [positive_semidefinite])

  let POSITIVE_SEMIDEFINITE_IMP_SYMMETRIC ← prove
   r"!A:real^N^N. positive_semidefinite A ==> transp A = A"
   (REWRITE_TAC [← GSYM symmetric_matrix,
                 POSITIVE_SEMIDEFINITE_IMP_SYMMETRIC_MATRIX])

  let POSITIVE_SEMIDEFINITE_ADD ← prove
   r"!A B:real^N^N.
        positive_semidefinite A /\ positive_semidefinite B
        ==> positive_semidefinite(A + B)"
   (SIMP_TAC [positive_semidefinite, SYMMETRIC_MATRIX_ADD] THEN
    SIMP_TAC [MATRIX_VECTOR_MUL_ADD_RDISTRIB, DOT_RADD, REAL_LE_ADD])

  let POSITIVE_SEMIDEFINITE_CMUL ← prove
   r"!c A:real^N^N.
        positive_semidefinite A /\ &0 <= c
        ==> positive_semidefinite(c %% A)"
   (SIMP_TAC [positive_semidefinite, SYMMETRIC_MATRIX_CMUL] THEN
    SIMP_TAC [MATRIX_VECTOR_LMUL, DOT_RMUL, REAL_LE_MUL])

  let POSITIVE_SEMIDEFINITE_TRANSP ← prove
   r"!A:real^N^N. positive_semidefinite(transp A) <=> positive_semidefinite A"
   (REWRITE_TAC [positive_semidefinite, symmetric_matrix] THEN
    MESON_TAC [TRANSP_TRANSP])

  let POSITIVE_SEMIDEFINITE_COVARIANCE ← prove
   r"!A:real^N^M. positive_semidefinite(transp A ** A)"
   (REWRITE_TAC [positive_semidefinite, symmetric_matrix,
                 MATRIX_TRANSP_MUL, TRANSP_TRANSP] THEN
    REWRITE_TAC [← GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC [← GSYM DOT_LMUL_MATRIX] THEN
    REWRITE_TAC [← GSYM MATRIX_VECTOR_MUL_TRANSP, DOT_POS_LE])

  let POSITIVE_SEMIDEFINITE_SIMILAR ← prove
   r"!A B:real^N^M.
        positive_semidefinite A
        ==> positive_semidefinite(transp B ** A ** B)"
   (REWRITE_TAC [positive_semidefinite, symmetric_matrix] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [MATRIX_TRANSP_MUL, TRANSP_TRANSP, ← GSYM MATRIX_MUL_ASSOC] THEN
    REWRITE_TAC [← GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC [← GSYM DOT_LMUL_MATRIX, ← GSYM MATRIX_VECTOR_MUL_TRANSP] THEN
    ASM_REWRITE_TAC [DOT_LMUL_MATRIX])

  let POSITIVE_SEMIDEFINITE_SIMILAR_EQ ← prove
   r"!A B:real^N^N.
        invertible B
        ==> (positive_semidefinite (transp B ** A ** B) <=>
             positive_semidefinite A)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN
    REWRITE_TAC [POSITIVE_SEMIDEFINITE_SIMILAR] THEN
    DISCH_THEN (MP_TAC o ISPEC (← q r"matrix_inv B:real^N^N") o MATCH_MP
      POSITIVE_SEMIDEFINITE_SIMILAR) THEN
    ASM_SIMP_TAC [← GSYM MATRIX_MUL_ASSOC, MATRIX_INV, MATRIX_MUL_RID] THEN
    REWRITE_TAC [MATRIX_MUL_ASSOC, ← GSYM MATRIX_TRANSP_MUL] THEN
    ASM_SIMP_TAC [MATRIX_INV, TRANSP_MAT, MATRIX_MUL_LID])

  let POSITIVE_SEMIDEFINITE_DIAGONAL_MATRIX ← prove
   r"!D:real^N^N.
        diagonal_matrix D /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= D$i$i)
        ==> positive_semidefinite D"
   (SIMP_TAC [positive_semidefinite, DIAGONAL_IMP_SYMMETRIC_MATRIX] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM (SUBST1_TAC o GEN_REWRITE_RULE id [DIAGONAL_MATRIX]) THEN
    SIMP_TAC [matrix_vector_mul, LAMBDA_BETA, dot] THEN
    SIMP_TAC [COND_RATOR, COND_RAND, REAL_MUL_LZERO] THEN
    CONV_TAC (RAND_CONV (ONCE_DEPTH_CONV SYM_CONV)) THEN
    SIMP_TAC [SUM_DELTA] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC [← ra r"x * d * x:real = d * x * x"] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC [REAL_LE_SQUARE])

  let POSITIVE_SEMIDEFINITE_DIAGONAL_MATRIX_EQ ← prove
   r"!D:real^N^N.
        diagonal_matrix D
        ==> (positive_semidefinite D <=>
             !i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= D$i$i)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN
    ASM_SIMP_TAC [POSITIVE_SEMIDEFINITE_DIAGONAL_MATRIX] THEN
    REWRITE_TAC [positive_semidefinite] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"basis i:real^N")) THEN
    ASM_SIMP_TAC [DOT_BASIS, MATRIX_VECTOR_MUL_BASIS, column, LAMBDA_BETA])

  let DIAGONAL_POSITIVE_SEMIDEFINITE ← prove
   r"!A:real^N^N i.
        positive_semidefinite A /\ 1 <= i /\ i <= dimindex(:N)
        ==> &0 <= A$i$i"
   (REWRITE_TAC [positive_semidefinite] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"basis i:real^N")) THEN
    ASM_SIMP_TAC [MATRIX_VECTOR_MUL_BASIS, column, DOT_BASIS, LAMBDA_BETA])

  let TRACE_POSITIVE_SEMIDEFINITE ← prove
   r"!A:real^N^N. positive_semidefinite A ==> &0 <= trace A"
   (SIMP_TAC [trace, SUM_POS_LE_NUMSEG, DIAGONAL_POSITIVE_SEMIDEFINITE])

  let TRACE_LE_MUL_SQUARES ← prove
   r"!A B:real^N^N.
        symmetric_matrix A /\ symmetric_matrix B
        ==> trace((A ** B) ** (A ** B)) <= trace((A ** A) ** (B ** B))"
   (REWRITE_TAC [symmetric_matrix] THEN REPEAT STRIP_TAC THEN MP_TAC
     (← ISPEC (← q r"A ** B - B ** A:real^N^N") POSITIVE_SEMIDEFINITE_COVARIANCE) THEN
    DISCH_THEN (MP_TAC o MATCH_MP TRACE_POSITIVE_SEMIDEFINITE) THEN
    REWRITE_TAC [MATRIX_TRANSP_MUL, TRANSP_MATRIX_SUB, MATRIX_SUB_LDISTRIB] THEN
    ASM_REWRITE_TAC [MATRIX_SUB_RDISTRIB, TRACE_SUB] THEN MATCH_MP_TAC (← REAL_ARITH (← q
    r"a = y /\ d = y /\ b = x /\ c = x ==> &0 <= a - b - (c - d) ==> x <= y")) THEN
    REWRITE_TAC [← GSYM MATRIX_MUL_ASSOC] THEN REPEAT CONJ_TAC THEN
    REPEAT (GEN_REWRITE_TAC LAND_CONV [TRACE_MUL_SYM] THEN
           REWRITE_TAC [← GSYM MATRIX_MUL_ASSOC]))

  let POSITIVE_SEMIDEFINITE_ZERO_FORM ← do
    let lemma ← prove
     r"(!t. &0 <= a + b * t) ==> b = &0"
     (ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"--(a + &1) / b")) THEN
      ASM_SIMP_TAC [REAL_DIV_LMUL] THEN REAL_ARITH_TAC)
    prove
     r"!A:real^N^N. positive_semidefinite A /\ x dot (A ** x) = &0
                ==> A ** x = vec 0"
     (REWRITE_TAC [positive_semidefinite, symmetric_matrix] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN (← q r"t:real") o SPEC (← q r"(A:real^N^N) ** x + t % x")) THEN
      REWRITE_TAC [MATRIX_VECTOR_MUL_ADD_LDISTRIB, DOT_RADD] THEN
      REWRITE_TAC [DOT_LADD, MATRIX_VECTOR_MUL_RMUL, DOT_LMUL] THEN
      REWRITE_TAC [DOT_RMUL] THEN
      SUBGOAL_THEN (← q r"x dot (A ** A ** x) = ((A:real^N^N) ** x) dot (A ** x)")
      SUBST1_TAC THENL
       [ASM_REWRITE_TAC [← GSYM DOT_LMUL_MATRIX, VECTOR_MATRIX_MUL_TRANSP],
        ASM_REWRITE_TAC [← ra r"(a + t * b) + t * b + t * t * &0 =
                                a + (&2 * b) * t"]] THEN
      DISCH_THEN (MP_TAC o MATCH_MP lemma) THEN
      REWRITE_TAC [REAL_ENTIRE, DOT_EQ_0, REAL_OF_NUM_EQ, ARITH_EQ])

  let POSITIVE_SEMIDEFINITE_ZERO_FORM_EQ ← prove
   r"!A:real^N^N. positive_semidefinite A
                ==> (x dot (A ** x) = &0 <=> A ** x = vec 0)"
   (REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
    ASM_SIMP_TAC [DOT_RZERO, POSITIVE_SEMIDEFINITE_ZERO_FORM])

  let POSITIVE_SEMIDEFINITE_1_GEN ← prove
   r"!A:real^N^N.
        dimindex(:N) = 1 ==> (positive_semidefinite A <=> &0 <= A$1$1)"
   (REPEAT STRIP_TAC THEN
    SIMP_TAC [positive_semidefinite, symmetric_matrix, transp, CART_EQ, dot] THEN
    ASM_SIMP_TAC [LAMBDA_BETA, ARITH, MATRIX_VECTOR_MUL_COMPONENT] THEN
    ASM_REWRITE_TAC [FORALL_1, SUM_1, dot] THEN
    REWRITE_TAC [← ra r"x * a * x:real = a * x pow 2"] THEN
    EQ_TAC THENL [ALL_TAC, MESON_TAC [REAL_LE_MUL, REAL_LE_POW_2]] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"basis 1:real^N")) THEN
    SIMP_TAC [BASIS_COMPONENT, ARITH, DIMINDEX_GE_1, LE_REFL] THEN
    REAL_ARITH_TAC)

  let POSITIVE_SEMIDEFINITE_1 ← prove
   r"!A:real^1^1. positive_semidefinite A <=> &0 <= A$1$1"
   (GEN_TAC THEN MATCH_MP_TAC POSITIVE_SEMIDEFINITE_1_GEN THEN
    REWRITE_TAC [DIMINDEX_1])

  let POSITIVE_SEMIDEFINITE_SUBMATRIX_2 ← prove
   r"!A:real^N^N i j.
        positive_semidefinite A /\
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> positive_semidefinite
              (vector[vector[A$i$i;A$i$j];
                      vector[A$j$i;A$j$j]]:real^2^2)"
   (REWRITE_TAC [positive_semidefinite, symmetric_matrix] THEN
    REPEAT STRIP_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [CART_EQ]) THEN
      SIMP_TAC [CART_EQ, transp, LAMBDA_BETA, DIMINDEX_2, VECTOR_2, ARITH,
                FORALL_2] THEN
      ASM_MESON_TAC [],
      SIMP_TAC [DOT_2, VECTOR_2, matrix_vector_mul, DIMINDEX_2, LAMBDA_BETA,
                ARITH, SUM_2]] THEN
    ASM_CASES_TAC (← q r"j:num = i") THENL
     [ASM_REWRITE_TAC [← ra
       r"x * (a * x + a * y) + y * (a * x + a * y):real =
      a * (x + y) pow 2"] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [REAL_LE_POW_2] THEN
      MATCH_MP_TAC DIAGONAL_POSITIVE_SEMIDEFINITE THEN
      ASM_REWRITE_TAC [positive_semidefinite, symmetric_matrix],
      FIRST_X_ASSUM (MP_TAC o SPEC
       (← q r"(lambda m. if m = i then (x:real^2)$1
                 else if m = j then (x:real^2)$2  else &0):real^N")) THEN
      SIMP_TAC [matrix_vector_mul, LAMBDA_BETA] THEN
      REPLICATE_TAC 2
       (REPLICATE_TAC 2 (ONCE_REWRITE_TAC [COND_RAND]) THEN
        SIMP_TAC [SUM_CASES, FINITE_NUMSEG, SUM_DELTA, REAL_MUL_RZERO] THEN
        ASM_SIMP_TAC [← SET_RULE (← q r"P a ==> {x | P x /\ x = a} = {a}"),
                      IN_NUMSEG, IN_ELIM_THM, SUM_SING] THEN
        SIMP_TAC [dot, LAMBDA_BETA] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM])])

  return { positive_semidefinite, POSITIVE_SEMIDEFINITE_IMP_SYMMETRIC_MATRIX,
           POSITIVE_SEMIDEFINITE_IMP_SYMMETRIC, POSITIVE_SEMIDEFINITE_ADD,
           POSITIVE_SEMIDEFINITE_CMUL, POSITIVE_SEMIDEFINITE_TRANSP,
           POSITIVE_SEMIDEFINITE_COVARIANCE, POSITIVE_SEMIDEFINITE_SIMILAR,
           POSITIVE_SEMIDEFINITE_SIMILAR_EQ, POSITIVE_SEMIDEFINITE_DIAGONAL_MATRIX,
           POSITIVE_SEMIDEFINITE_DIAGONAL_MATRIX_EQ, DIAGONAL_POSITIVE_SEMIDEFINITE,
           TRACE_POSITIVE_SEMIDEFINITE, TRACE_LE_MUL_SQUARES, POSITIVE_SEMIDEFINITE_ZERO_FORM,
           POSITIVE_SEMIDEFINITE_ZERO_FORM_EQ, POSITIVE_SEMIDEFINITE_1_GEN,
           POSITIVE_SEMIDEFINITE_1, POSITIVE_SEMIDEFINITE_SUBMATRIX_2 }

/- ------------------------------------------------------------------------- -/
/- The Frobenius norm and associated inner product, which turn out to be the -/
/- usual Euclidean versions modulo flattening.  (determinants.ml 2141-2273)  -/
/- ------------------------------------------------------------------------- -/

structure Frobenius where
  DOT_VECTORIZE : thm
  NORM_VECTORIZE_TRANSP : thm
  COMPATIBLE_NORM_VECTORIZE : thm
  ONORM_LE_NORM_VECTORIZE : thm
  NORM_VECTORIZE_POW_2 : thm
  NORM_VECTORIZE_MUL_LE : thm
  NORM_VECTORIZE_HADAMARD_LE : thm
  TRACE_COVARIANCE_POS_LE : thm
  TRACE_COVARIANCE_EQ_0 : thm
  TRACE_COVARIANCE_POS_LT : thm
  TRACE_COVARIANCE_CAUCHY_SCHWARZ : thm
  TRACE_COVARIANCE_CAUCHY_SCHWARZ_ABS : thm
  TRACE_COVARIANCE_CAUCHY_SCHWARZ_SQUARE : thm
  deriving Inhabited

@[nospecialize]
def setupFrobenius [HolBase] (D : DeterminantsDeps) (BTrace : Trace) (BPsd : Psd) :
    ExceptT String IO Frobenius := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, MESON_TAC, .. } := D
  let { ADD_SUB2, DIMINDEX_FINITE_PROD, DIMINDEX_GE_1, DIVISION, DIV_UNIQ, FINITE_NUMSEG,
        FINITE_PRODUCT_DEPENDENT, FORALL_IN_GSPEC, IMP_CONJ, IN_ELIM_PAIR_THM, IN_NUMSEG,
        LAMBDA_BETA, .. } := D.core1
  let { LE_1, LE_ADD, LE_ADD_LCANCEL, LE_MULT_RCANCEL, LE_TRANS, MOD_UNIQ, RDIV_LT_EQ,
        REAL_ABS_MUL, REAL_ABS_POS, REAL_EQ_IMP_LE, REAL_LE_MUL, REAL_LE_POW_2, REAL_LE_REFL,
        REAL_LE_RMUL, REAL_LE_SQUARE, REAL_LE_SQUARE_ABS, REAL_LE_TRANS, REAL_LT_LE,
        REAL_MUL_AC, REAL_MUL_SYM, .. } := D.core2
  let { REAL_POW2_ABS, REAL_POW_2, REAL_POW_MUL, REAL_RSQRT_LE, SQRT_MUL, SUB_ADD, SUM_EQ,
        SUM_EQ_GENERAL_INVERSES, SUM_LE_NUMSEG, SUM_MUL_BOUND, SUM_RMUL, SUM_SUM_PRODUCT,
        SUM_SWAP_NUMSEG, .. } := D.core3
  let { PAIR_EQ, .. } := D.core4
  let { DOT_EQ_0, .. } := D.vec1
  let { MATRIX_MUL_COMPONENT, MATRIX_MUL_DOT, MATRIX_VECTOR_MUL_LINEAR, NORM_CAUCHY_SCHWARZ,
        NORM_CAUCHY_SCHWARZ_ABS, NORM_EQ, NORM_LE_SQUARE, NORM_POS_LE, NORM_POW_2, ONORM,
        REAL_ABS_NORM, .. } := D.vec2
  let { TRANSP_TRANSP, VECTORIZE_EQ_0, dot, matrix_mul, transp, vector_norm,
        VECTORIZE_COMPONENT, .. } := D.vec3
  let { TRACE_MUL_SYM, trace, .. } := BTrace
  let { POSITIVE_SEMIDEFINITE_COVARIANCE, TRACE_POSITIVE_SEMIDEFINITE, .. } := BPsd
  -- @@SCOPE END
  let ar (s : String) : ExceptT String IO thm := do ARITH_RULE (← q s)

  let DOT_VECTORIZE ← prove
   r"!A B:real^N^M. vectorize A dot vectorize B = trace(transp A ** B)"
   (REPEAT GEN_TAC THEN
    SIMP_TAC [dot, trace, matrix_mul, transp, LAMBDA_BETA] THEN
    SIMP_TAC [SUM_SUM_PRODUCT, FINITE_NUMSEG] THEN
    SIMP_TAC [VECTORIZE_COMPONENT, DIMINDEX_FINITE_PROD] THEN
    MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
    REWRITE_TAC [FORALL_IN_GSPEC] THEN
    EXISTS_TAC
     (← q r"\k. (1 + (k - 1) MOD dimindex(:N)),(1 + (k - 1) DIV dimindex(:N))") THEN
    EXISTS_TAC (← q r"\(i,j). (j - 1) * dimindex(:N) + i") THEN
    REWRITE_TAC [IN_ELIM_PAIR_THM, PAIR_EQ, IN_NUMSEG] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"j:num"] THEN STRIP_TAC THEN CONJ_TAC THENL
       [CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
        TRANS_TAC LE_TRANS (← q r"(j - 1) * dimindex(:N) + dimindex(:N)") THEN
        ASM_REWRITE_TAC [LE_ADD_LCANCEL] THEN
        REWRITE_TAC [← ar r"x * n + n = (x + 1) * n"] THEN
        ASM_SIMP_TAC [SUB_ADD, LE_MULT_RCANCEL],
        CONJ_TAC THEN MATCH_MP_TAC (← ar
         r"1 <= i /\ j = i - 1 ==> 1 + j = i") THEN
        ASM_REWRITE_TAC [] THENL
         [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC (← q r"j - 1") THEN ASM_ARITH_TAC,
          MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC (← q r"i - 1") THEN ASM_ARITH_TAC]],
      X_GEN_TAC (← q r"k:num") THEN STRIP_TAC THEN REWRITE_TAC [LE_ADD] THEN
      SIMP_TAC [DIVISION, DIMINDEX_GE_1, LE_1, ADD_SUB2, RDIV_LT_EQ, ← ar
        r"1 <= n ==> (1 + m <= n <=> m < n)"] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      MATCH_MP_TAC (← ar
       r"1 <= x /\ x - 1 = q * n + r /\ r < n ==> q * n + 1 + r = x") THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC DIVISION THEN
      SIMP_TAC [DIMINDEX_GE_1, LE_1]])

  let NORM_VECTORIZE_TRANSP ← prove
   r"!A:real^N^M. norm(vectorize(transp A)) = norm(vectorize A)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [NORM_EQ, DOT_VECTORIZE, TRANSP_TRANSP] THEN
    MATCH_ACCEPT_TAC TRACE_MUL_SYM)

  let COMPATIBLE_NORM_VECTORIZE ← prove
   r"!A:real^N^M x. norm(A ** x) <= norm(vectorize A) * norm x"
   (REPEAT GEN_TAC THEN
    SIMP_TAC [NORM_LE_SQUARE, REAL_LE_MUL, NORM_POS_LE] THEN
    REWRITE_TAC [dot] THEN SIMP_TAC [MATRIX_MUL_DOT, LAMBDA_BETA] THEN
    TRANS_TAC REAL_LE_TRANS
     (← q r"sum (1..dimindex(:M))
        (\i. norm((A:real^N^M)$i) pow 2 * norm(x:real^N) pow 2)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
      REWRITE_TAC [← GSYM REAL_POW_MUL, ← GSYM REAL_POW_2] THEN
      REWRITE_TAC [← GSYM REAL_LE_SQUARE_ABS, REAL_ABS_MUL, REAL_ABS_NORM] THEN
      REWRITE_TAC [NORM_CAUCHY_SCHWARZ_ABS],
      REWRITE_TAC [SUM_RMUL, REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC [REAL_LE_POW_2, NORM_POW_2, DOT_VECTORIZE] THEN
      ONCE_REWRITE_TAC [TRACE_MUL_SYM] THEN
      REWRITE_TAC [trace] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      SIMP_TAC [transp, matrix_mul, LAMBDA_BETA, dot, REAL_LE_REFL]])

  let ONORM_LE_NORM_VECTORIZE ← prove
   r"!A:real^M^N. onorm(\x. A ** x) <= norm(vectorize A)"
   (GEN_TAC THEN MATCH_MP_TAC
     (← CONJUNCT2 (← MATCH_MP ONORM (← SPEC_ALL MATRIX_VECTOR_MUL_LINEAR))) THEN
    REWRITE_TAC [COMPATIBLE_NORM_VECTORIZE])

  let NORM_VECTORIZE_POW_2 ← prove
   r"!A:real^N^M.
    norm(vectorize A) pow 2 = sum(1..dimindex(:M)) (\i. norm(A$i) pow 2)"
   (GEN_TAC THEN
    REWRITE_TAC [NORM_POW_2, DOT_VECTORIZE] THEN
    SIMP_TAC [trace, transp, matrix_mul, dot, LAMBDA_BETA] THEN
    GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC [])

  let NORM_VECTORIZE_MUL_LE ← prove
   r"!A:real^N^P B:real^M^N.
    norm(vectorize(A ** B)) <= norm(vectorize A) * norm(vectorize B)"
   (REPEAT GEN_TAC THEN
    SIMP_TAC [NORM_LE_SQUARE, REAL_LE_MUL, NORM_POS_LE] THEN
    REWRITE_TAC [← GSYM NORM_POW_2, NORM_VECTORIZE_POW_2] THEN
    SIMP_TAC [MATRIX_MUL_COMPONENT, REAL_POW_MUL] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [NORM_VECTORIZE_POW_2] THEN
    REWRITE_TAC [← GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC (← q r"i:num") THEN
    STRIP_TAC THEN REWRITE_TAC [← GSYM REAL_POW_MUL] THEN
    REWRITE_TAC [← GSYM REAL_LE_SQUARE_ABS, REAL_ABS_MUL, REAL_ABS_NORM] THEN
    MESON_TAC [COMPATIBLE_NORM_VECTORIZE, NORM_VECTORIZE_TRANSP, REAL_MUL_SYM])

  let NORM_VECTORIZE_HADAMARD_LE ← prove
   r"!A:real^N^M B:real^N^M.
        norm(vectorize((lambda i j. A$i$j * B$i$j):real^N^M))
        <= norm(vectorize A) * norm(vectorize B)"
   (REPEAT GEN_TAC THEN
    SIMP_TAC [NORM_LE_SQUARE, REAL_LE_MUL, NORM_POS_LE] THEN
    REWRITE_TAC [DOT_VECTORIZE, REAL_POW_MUL, NORM_POW_2] THEN
    SIMP_TAC [transp, matrix_mul, trace, LAMBDA_BETA] THEN
    SIMP_TAC [SUM_SUM_PRODUCT, FINITE_NUMSEG] THEN
    W (MP_TAC o PART_MATCH (rand o rand) SUM_MUL_BOUND o rand o snd) THEN
    SIMP_TAC [FINITE_PRODUCT_DEPENDENT, FINITE_NUMSEG, FORALL_IN_GSPEC] THEN
    REWRITE_TAC [REAL_LE_SQUARE] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] REAL_LE_TRANS) THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC [FORALL_IN_GSPEC] THEN REWRITE_TAC [REAL_MUL_AC])

  let TRACE_COVARIANCE_POS_LE ← prove
   r"!A:real^M^N. &0 <= trace(transp A ** A)"
   (SIMP_TAC [POSITIVE_SEMIDEFINITE_COVARIANCE, TRACE_POSITIVE_SEMIDEFINITE])

  let TRACE_COVARIANCE_EQ_0 ← prove
   r"!A:real^M^N. trace(transp A ** A) = &0 <=> A = mat 0"
   (REWRITE_TAC [← GSYM DOT_VECTORIZE, DOT_EQ_0, VECTORIZE_EQ_0])

  let TRACE_COVARIANCE_POS_LT ← prove
   r"!A:real^M^N. &0 < trace(transp A ** A) <=> ~(A = mat 0)"
   (MESON_TAC [REAL_LT_LE, TRACE_COVARIANCE_POS_LE, TRACE_COVARIANCE_EQ_0])

  let TRACE_COVARIANCE_CAUCHY_SCHWARZ ← prove
   r"!A B:real^M^N.
        trace(transp A ** B)
         <= sqrt(trace(transp A ** A)) * sqrt(trace(transp B ** B))"
   (REWRITE_TAC [← GSYM DOT_VECTORIZE, ← GSYM vector_norm, NORM_CAUCHY_SCHWARZ])

  let TRACE_COVARIANCE_CAUCHY_SCHWARZ_ABS ← prove
   r"!A B:real^M^N.
        abs(trace(transp A ** B))
         <= sqrt(trace(transp A ** A)) * sqrt(trace(transp B ** B))"
   (REWRITE_TAC [← GSYM DOT_VECTORIZE, ← GSYM vector_norm, NORM_CAUCHY_SCHWARZ_ABS])

  let TRACE_COVARIANCE_CAUCHY_SCHWARZ_SQUARE ← prove
   r"!A B:real^M^N.
        trace(transp A ** B) pow 2
        <= trace(transp A ** A) * trace(transp B ** B)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_RSQRT_LE THEN
    SIMP_TAC [REAL_ABS_POS, REAL_LE_MUL, TRACE_COVARIANCE_POS_LE] THEN
    REWRITE_TAC [TRACE_COVARIANCE_CAUCHY_SCHWARZ_ABS, SQRT_MUL])

  return { DOT_VECTORIZE, NORM_VECTORIZE_TRANSP, COMPATIBLE_NORM_VECTORIZE,
           ONORM_LE_NORM_VECTORIZE, NORM_VECTORIZE_POW_2, NORM_VECTORIZE_MUL_LE,
           NORM_VECTORIZE_HADAMARD_LE, TRACE_COVARIANCE_POS_LE, TRACE_COVARIANCE_EQ_0,
           TRACE_COVARIANCE_POS_LT, TRACE_COVARIANCE_CAUCHY_SCHWARZ,
           TRACE_COVARIANCE_CAUCHY_SCHWARZ_ABS, TRACE_COVARIANCE_CAUCHY_SCHWARZ_SQUARE }

/- ------------------------------------------------------------------------- -/
/- Positive definite matrices.  (determinants.ml 2279-2481)                  -/
/- ------------------------------------------------------------------------- -/

structure PosDef where
  positive_definite : thm
  POSITIVE_DEFINITE_IMP_SYMMETRIC_MATRIX : thm
  POSITIVE_DEFINITE_IMP_SYMMETRIC : thm
  POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE : thm
  POSITIVE_DEFINITE_SIMILAR_EQ : thm
  POSITIVE_DEFINITE_1_GEN : thm
  POSITIVE_DEFINITE_1 : thm
  POSITIVE_DEFINITE_IMP_INVERTIBLE : thm
  POSITIVE_DEFINITE_IMP_POSITIVE_SEMIDEFINITE : thm
  POSITIVE_SEMIDEFINITE_POSITIVE_DEFINITE_ADD : thm
  POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE_ADD : thm
  POSITIVE_DEFINITE_ADD : thm
  POSITIVE_DEFINITE_CMUL : thm
  NEARBY_POSITIVE_DEFINITE_MATRIX_GEN : thm
  POSITIVE_DEFINITE_TRANSP : thm
  POSITIVE_DEFINITE_COVARIANCE : thm
  POSITIVE_DEFINITE_SIMILAR : thm
  POSITIVE_DEFINITE_DIAGONAL_MATRIX : thm
  POSITIVE_DEFINITE_DIAGONAL_MATRIX_EQ : thm
  DIAGONAL_POSITIVE_DEFINITE : thm
  TRACE_POSITIVE_DEFINITE : thm
  POSITIVE_DEFINITE_MAT : thm
  POSITIVE_DEFINITE_ID : thm
  POSITIVE_SEMIDEFINITE_MAT : thm
  NEARBY_POSITIVE_DEFINITE_MATRIX : thm
  POSITIVE_SEMIDEFINITE_ANTISYM : thm
  LOEWNER_ORDER_ANTISYM : thm
  deriving Inhabited

@[nospecialize]
def setupPosDef [HolBase] (D : DeterminantsDeps) (BTrace : Trace)
    (BInvertibility : Invertibility) (BDiagonal : Diagonal) (BPsd : Psd) :
    ExceptT String IO PosDef := do
  -- @@SCOPE BEGIN
  let { MATRIX_ARITH, MESON, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, new_definition,
        .. } := D
  let { AND_FORALL_THM, ARITH, CART_EQ, COND_RAND, COND_RATOR, CONJ_ASSOC, DIMINDEX_1,
        DIMINDEX_GE_1, FINITE_NUMSEG, IMP_IMP, IN_NUMSEG, LAMBDA_BETA, .. } := D.core1
  let { LE_REFL, MONO_EXISTS, MONO_FORALL, NOT_FORALL_THM, NOT_IMP, NOT_LT, NUMSEG_EMPTY,
        REAL_LET_ADD, REAL_LE_MUL, REAL_LE_REFL, REAL_LE_SQUARE, REAL_LTE_ADD, REAL_LT_ADD,
        REAL_LT_IMP_LE, REAL_LT_MUL, REAL_LT_POW_2, REAL_MUL_LZERO, REAL_OF_NUM_LT,
        .. } := D.core2
  let { REAL_POS, REAL_POW_2, SUM_DELTA, SUM_POS_LT, SUM_POS_LT_ALL, .. } := D.core3
  let { FORALL_AND_THM, .. } := D.core4
  let { BASIS_COMPONENT, BASIS_NONZERO, DOT_BASIS, DOT_LZERO, DOT_RADD, DOT_RMUL, DOT_RNEG,
        FORALL_1, INVERTIBLE_TRANSP, MATRIX_EQ_0, .. } := D.vec1
  let { MATRIX_NEG_0, MATRIX_SUB_EQ, MATRIX_VECTOR_LMUL, MATRIX_VECTOR_MUL_ADD_RDISTRIB,
        MATRIX_VECTOR_MUL_BASIS, MATRIX_VECTOR_MUL_COMPONENT, MATRIX_VECTOR_MUL_LNEG,
        .. } := D.vec2
  let { SUM_1, SYMMETRIC_MATRIX_ADD, SYMMETRIC_MATRIX_CMUL, TRANSP_TRANSP, VEC_COMPONENT,
        column, dot, mat, matrix_vector_mul, symmetric_matrix, transp, .. } := D.vec3
  let { trace, .. } := BTrace
  let { HOMOGENEOUS_LINEAR_EQUATIONS_DET, INVERTIBLE_DET_NZ, INVERTIBLE_MATRIX_MUL,
        .. } := BInvertibility
  let { DIAGONAL_IMP_SYMMETRIC_MATRIX, DIAGONAL_MATRIX, DIAGONAL_MATRIX_MAT, .. } := BDiagonal
  let { POSITIVE_SEMIDEFINITE_COVARIANCE, POSITIVE_SEMIDEFINITE_DIAGONAL_MATRIX_EQ,
        POSITIVE_SEMIDEFINITE_SIMILAR, POSITIVE_SEMIDEFINITE_SIMILAR_EQ,
        POSITIVE_SEMIDEFINITE_ZERO_FORM_EQ, positive_semidefinite, .. } := BPsd
  -- @@SCOPE END
  let ra (s : String) : ExceptT String IO thm := do REAL_ARITH (← q s)

  let positive_definite ← new_definition
   r"positive_definite(A:real^N^N) <=>
         symmetric_matrix A /\ !x. ~(x = vec 0) ==> &0 < x dot (A ** x)"

  let POSITIVE_DEFINITE_IMP_SYMMETRIC_MATRIX ← prove
   r"!A:real^N^N. positive_definite A ==> symmetric_matrix A"
   (SIMP_TAC [positive_definite])

  let POSITIVE_DEFINITE_IMP_SYMMETRIC ← prove
   r"!A:real^N^N. positive_definite A ==> transp A = A"
   (REWRITE_TAC [← GSYM symmetric_matrix, POSITIVE_DEFINITE_IMP_SYMMETRIC_MATRIX])

  let POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE ← prove
   r"!A:real^N^N.
        positive_definite A <=> positive_semidefinite A /\ invertible A"
   (GEN_TAC THEN
    REWRITE_TAC [← ra r"&0 < x <=> &0 <= x /\ ~(x = &0)", positive_definite,
          FORALL_AND_THM, ← TAUT (← q r"p ==> q /\ r <=> (p ==> q) /\ (p ==> r)")] THEN
    SIMP_TAC [← MESON [] (← q r"P a ==> ((!x:real^N. ~(x = a) ==> P x) <=> (!x. P x))"),
              DOT_LZERO, REAL_LE_REFL] THEN
    REWRITE_TAC [CONJ_ASSOC, ← GSYM positive_semidefinite] THEN
    ASM_CASES_TAC (← q r"positive_semidefinite(A:real^N^N)") THEN
    ASM_SIMP_TAC [POSITIVE_SEMIDEFINITE_ZERO_FORM_EQ] THEN
    REWRITE_TAC [← GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET, INVERTIBLE_DET_NZ] THEN
    MESON_TAC [])

  let POSITIVE_DEFINITE_SIMILAR_EQ ← prove
   r"!A B:real^N^N.
        positive_definite(transp B ** A ** B) <=>
        invertible B /\ positive_definite A"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE] THEN
    REWRITE_TAC [INVERTIBLE_MATRIX_MUL, INVERTIBLE_TRANSP] THEN
    MESON_TAC [POSITIVE_SEMIDEFINITE_SIMILAR_EQ])

  let POSITIVE_DEFINITE_1_GEN ← prove
   r"!A:real^N^N.
        dimindex(:N) = 1 ==> (positive_definite A <=> &0 < A$1$1)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [positive_definite, symmetric_matrix, transp, CART_EQ, dot] THEN
    ASM_SIMP_TAC [LAMBDA_BETA, ARITH, MATRIX_VECTOR_MUL_COMPONENT] THEN
    ASM_REWRITE_TAC [FORALL_1, SUM_1, dot, VEC_COMPONENT] THEN
    REWRITE_TAC [← ra r"x * a * x:real = a * x pow 2"] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ALL_TAC, MESON_TAC [REAL_LT_MUL, REAL_LT_POW_2]] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"basis 1:real^N")) THEN
    SIMP_TAC [BASIS_COMPONENT, ARITH, DIMINDEX_GE_1, LE_REFL] THEN
    REAL_ARITH_TAC)

  let POSITIVE_DEFINITE_1 ← prove
   r"!A:real^1^1. positive_definite A <=> &0 < A$1$1"
   (GEN_TAC THEN MATCH_MP_TAC POSITIVE_DEFINITE_1_GEN THEN
    REWRITE_TAC [DIMINDEX_1])

  let POSITIVE_DEFINITE_IMP_INVERTIBLE ← prove
   r"!A:real^N^N. positive_definite A ==> invertible A"
   (SIMP_TAC [POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE])

  let POSITIVE_DEFINITE_IMP_POSITIVE_SEMIDEFINITE ← prove
   r"!A:real^N^N. positive_definite A ==> positive_semidefinite A"
   (SIMP_TAC [POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE])

  let POSITIVE_SEMIDEFINITE_POSITIVE_DEFINITE_ADD ← prove
   r"!A B:real^N^N.
        positive_semidefinite A /\ positive_definite B
        ==> positive_definite(A + B)"
   (SIMP_TAC [positive_definite, positive_semidefinite, SYMMETRIC_MATRIX_ADD] THEN
    SIMP_TAC [MATRIX_VECTOR_MUL_ADD_RDISTRIB, DOT_RADD, REAL_LET_ADD])

  let POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE_ADD ← prove
   r"!A B:real^N^N.
        positive_definite A /\ positive_semidefinite B
        ==> positive_definite(A + B)"
   (SIMP_TAC [positive_definite, positive_semidefinite, SYMMETRIC_MATRIX_ADD] THEN
    SIMP_TAC [MATRIX_VECTOR_MUL_ADD_RDISTRIB, DOT_RADD, REAL_LTE_ADD])

  let POSITIVE_DEFINITE_ADD ← prove
   r"!A B:real^N^N.
        positive_definite A /\ positive_definite B
        ==> positive_definite(A + B)"
   (SIMP_TAC [positive_definite, SYMMETRIC_MATRIX_ADD] THEN
    SIMP_TAC [MATRIX_VECTOR_MUL_ADD_RDISTRIB, DOT_RADD, REAL_LT_ADD])

  let POSITIVE_DEFINITE_CMUL ← prove
   r"!c A:real^N^N.
        positive_definite A /\ &0 < c
        ==> positive_definite(c %% A)"
   (SIMP_TAC [positive_definite, SYMMETRIC_MATRIX_CMUL] THEN
    SIMP_TAC [MATRIX_VECTOR_LMUL, DOT_RMUL, REAL_LT_MUL])

  let NEARBY_POSITIVE_DEFINITE_MATRIX_GEN ← prove
   r"!A:real^N^N B x.
        positive_semidefinite A /\ positive_definite B /\ &0 < x
        ==> positive_definite(A + x %% B)"
   (SIMP_TAC [POSITIVE_SEMIDEFINITE_POSITIVE_DEFINITE_ADD,
              POSITIVE_DEFINITE_CMUL])

  let POSITIVE_DEFINITE_TRANSP ← prove
   r"!A:real^N^N. positive_definite(transp A) <=> positive_definite A"
   (REWRITE_TAC [positive_definite, symmetric_matrix] THEN
    MESON_TAC [TRANSP_TRANSP])

  let POSITIVE_DEFINITE_COVARIANCE ← prove
   r"!A:real^N^N. positive_definite(transp A ** A) <=> invertible A"
   (REWRITE_TAC [POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE,
                 POSITIVE_SEMIDEFINITE_COVARIANCE] THEN
    REWRITE_TAC [INVERTIBLE_MATRIX_MUL, INVERTIBLE_TRANSP])

  let POSITIVE_DEFINITE_SIMILAR ← prove
   r"!A B:real^N^N.
        positive_definite A /\ invertible B
        ==> positive_definite(transp B ** A ** B)"
   (SIMP_TAC [POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE,
              POSITIVE_SEMIDEFINITE_SIMILAR, INVERTIBLE_MATRIX_MUL,
              INVERTIBLE_TRANSP])

  let POSITIVE_DEFINITE_DIAGONAL_MATRIX ← prove
   r"!D:real^N^N.
        diagonal_matrix D /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 < D$i$i)
        ==> positive_definite D"
   (SIMP_TAC [positive_definite, DIAGONAL_IMP_SYMMETRIC_MATRIX] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM (SUBST1_TAC o GEN_REWRITE_RULE id [DIAGONAL_MATRIX]) THEN
    SIMP_TAC [matrix_vector_mul, LAMBDA_BETA, dot] THEN
    SIMP_TAC [COND_RATOR, COND_RAND, REAL_MUL_LZERO] THEN
    CONV_TAC (RAND_CONV (ONCE_DEPTH_CONV SYM_CONV)) THEN
    SIMP_TAC [SUM_DELTA] THEN MATCH_MP_TAC SUM_POS_LT THEN
    REWRITE_TAC [← ra r"x * d * x:real = d * x * x"] THEN
    ASM_SIMP_TAC [FINITE_NUMSEG, IN_NUMSEG, REAL_LE_MUL, REAL_LE_SQUARE,
                  REAL_LT_IMP_LE] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
    REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, VEC_COMPONENT] THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    ASM_SIMP_TAC [← GSYM REAL_POW_2, REAL_LT_MUL, REAL_LT_POW_2])

  let POSITIVE_DEFINITE_DIAGONAL_MATRIX_EQ ← prove
   r"!D:real^N^N.
        diagonal_matrix D
        ==> (positive_definite D <=>
             !i. 1 <= i /\ i <= dimindex(:N) ==> &0 < D$i$i)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN
    ASM_SIMP_TAC [POSITIVE_DEFINITE_DIAGONAL_MATRIX] THEN
    REWRITE_TAC [positive_definite] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"basis i:real^N")) THEN
    ASM_SIMP_TAC [DOT_BASIS, MATRIX_VECTOR_MUL_BASIS, column, LAMBDA_BETA,
                  BASIS_NONZERO])

  let DIAGONAL_POSITIVE_DEFINITE ← prove
   r"!A:real^N^N i.
        positive_definite A /\ 1 <= i /\ i <= dimindex(:N)
        ==> &0 < A$i$i"
   (REWRITE_TAC [positive_definite] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"basis i:real^N")) THEN
    ASM_SIMP_TAC [MATRIX_VECTOR_MUL_BASIS, column, DOT_BASIS, LAMBDA_BETA,
                  BASIS_NONZERO])

  let TRACE_POSITIVE_DEFINITE ← prove
   r"!A:real^N^N. positive_definite A ==> &0 < trace A"
   (SIMP_TAC [trace, SUM_POS_LT_ALL, DIAGONAL_POSITIVE_DEFINITE,
              IN_NUMSEG, FINITE_NUMSEG, NUMSEG_EMPTY, NOT_LT, DIMINDEX_GE_1])

  let POSITIVE_DEFINITE_MAT ← prove
   r"!m. positive_definite(mat m:real^N^N) <=> 0 < m"
   (SIMP_TAC [POSITIVE_DEFINITE_DIAGONAL_MATRIX_EQ, DIAGONAL_MATRIX_MAT] THEN
    SIMP_TAC [mat, LAMBDA_BETA, REAL_OF_NUM_LT] THEN
    MESON_TAC [LE_REFL, DIMINDEX_GE_1])

  let POSITIVE_DEFINITE_ID ← prove
   r"positive_definite(mat 1:real^N^N)"
   (REWRITE_TAC [POSITIVE_DEFINITE_MAT, ARITH])

  let POSITIVE_SEMIDEFINITE_MAT ← prove
   r"!m. positive_semidefinite(mat m:real^N^N)"
   (SIMP_TAC [POSITIVE_SEMIDEFINITE_DIAGONAL_MATRIX_EQ, DIAGONAL_MATRIX_MAT] THEN
    SIMP_TAC [mat, LAMBDA_BETA, REAL_POS] THEN
    MESON_TAC [LE_REFL, DIMINDEX_GE_1])

  let NEARBY_POSITIVE_DEFINITE_MATRIX ← prove
   r"!A:real^N^N x.
      positive_semidefinite A /\ &0 < x ==> positive_definite(A + x %% mat 1)"
   (SIMP_TAC [NEARBY_POSITIVE_DEFINITE_MATRIX_GEN, POSITIVE_DEFINITE_ID])

  let POSITIVE_SEMIDEFINITE_ANTISYM ← prove
   r"!A:real^N^N. positive_semidefinite A /\ positive_semidefinite(--A) <=>
                A = mat 0"
   (GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [POSITIVE_SEMIDEFINITE_MAT, MATRIX_NEG_0] THEN
    ASM_SIMP_TAC [MATRIX_EQ_0, ← GSYM POSITIVE_SEMIDEFINITE_ZERO_FORM_EQ] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    REWRITE_TAC [positive_semidefinite] THEN
    REWRITE_TAC [MATRIX_VECTOR_MUL_LNEG, DOT_RNEG, IMP_IMP] THEN
    DISCH_THEN (CONJUNCTS_THEN (MP_TAC o CONJUNCT2)) THEN
    REWRITE_TAC [IMP_IMP, AND_FORALL_THM] THEN
    MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC)

  let LOEWNER_ORDER_ANTISYM ← prove
   r"!(A:real^N^N) B.
        positive_semidefinite(A - B) /\ positive_semidefinite(B - A) <=>
        A = B"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [← GSYM MATRIX_SUB_EQ] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM POSITIVE_SEMIDEFINITE_ANTISYM] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC (fun t => MATRIX_ARITH t))

  return { positive_definite, POSITIVE_DEFINITE_IMP_SYMMETRIC_MATRIX,
           POSITIVE_DEFINITE_IMP_SYMMETRIC, POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE,
           POSITIVE_DEFINITE_SIMILAR_EQ, POSITIVE_DEFINITE_1_GEN, POSITIVE_DEFINITE_1,
           POSITIVE_DEFINITE_IMP_INVERTIBLE, POSITIVE_DEFINITE_IMP_POSITIVE_SEMIDEFINITE,
           POSITIVE_SEMIDEFINITE_POSITIVE_DEFINITE_ADD,
           POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE_ADD, POSITIVE_DEFINITE_ADD,
           POSITIVE_DEFINITE_CMUL, NEARBY_POSITIVE_DEFINITE_MATRIX_GEN,
           POSITIVE_DEFINITE_TRANSP, POSITIVE_DEFINITE_COVARIANCE, POSITIVE_DEFINITE_SIMILAR,
           POSITIVE_DEFINITE_DIAGONAL_MATRIX, POSITIVE_DEFINITE_DIAGONAL_MATRIX_EQ,
           DIAGONAL_POSITIVE_DEFINITE, TRACE_POSITIVE_DEFINITE, POSITIVE_DEFINITE_MAT,
           POSITIVE_DEFINITE_ID, POSITIVE_SEMIDEFINITE_MAT, NEARBY_POSITIVE_DEFINITE_MATRIX,
           POSITIVE_SEMIDEFINITE_ANTISYM, LOEWNER_ORDER_ANTISYM }

/- ------------------------------------------------------------------------- -/
/- Hadamard's inequality.  (determinants.ml 2487-2637)                       -/
/- ------------------------------------------------------------------------- -/

structure Hadamard where
  HADAMARD_INEQUALITY_ROW : thm
  HADAMARD_INEQUALITY_COLUMN : thm
  deriving Inhabited

@[nospecialize]
def setupHadamard [HolBase] (D : DeterminantsDeps) (BDetBasic : DetBasic)
    (BMultilinear : Multilinear) (BDiagonal : Diagonal) : ExceptT String IO Hadamard := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, MESON_TAC, NUM_REDUCE_CONV, REAL_ARITH, VECTOR_ARITH,
        instantiate_casewise_recursion, .. } := D
  let { ADMISSIBLE_IMP_SUPERADMISSIBLE, CART_EQ, COND_ID, CONJ_ASSOC, EQ_TRANS,
        FINITE_NUMSEG, IMP_IMP, IN_ELIM_THM, IN_NUMSEG, LAMBDA_BETA, LAMBDA_ETA, .. } := D.core1
  let { LE_REFL, REAL_DIV_RMUL, REAL_ENTIRE, REAL_EQ_IMP_LE, REAL_LE_DIV, REAL_LE_REFL,
        REAL_LE_SQUARE, REAL_LE_SQUARE_ABS, REAL_LE_TRANS, REAL_MUL_RZERO, .. } := D.core2
  let { REAL_POW_2, REAL_SUB_0, RIGHT_IMP_FORALL_THM, SUM_DELTA, SUM_EQ_NUMSEG,
        SUM_LE_NUMSEG, SUM_LMUL, SWAP_FORALL_THM, WF_num, WLOG_LT, num_INDUCTION, num_WF,
        pairwise, admissible, .. } := D.core3
  let { DOT_EQ_0, DOT_LMUL, DOT_LSUB, DOT_LSUM, DOT_POS_LE, DOT_RMUL, DOT_RSUM, DOT_RZERO,
        .. } := D.vec1
  let { NORM_LE, NORM_POS_LE, NORM_POW_2, ORTHOGONAL_SYM, ROW_TRANSP, .. } := D.vec2
  let { SPAN_MUL, SPAN_NEG, SPAN_SUPERSET, SPAN_VSUM, TRANSP_TRANSP, VECTOR_SUB, VSUM_EQ,
        dot, matrix_mul, orthogonal, row, transp, .. } := D.vec3
  let { PRODUCT_EQ_NUMSEG, PRODUCT_LE_NUMSEG, PRODUCT_MUL_NUMSEG, PRODUCT_POS_LE_NUMSEG,
        .. } := D.lib
  let { DET_ROW_SPAN, DET_TRANSP, .. } := BDetBasic
  let { DET_MUL, .. } := BMultilinear
  let { DET_DIAGONAL, DIAGONAL_MATRIX_MUL_EQ, .. } := BDiagonal
  -- @@SCOPE END
  let ar (s : String) : ExceptT String IO thm := do ARITH_RULE (← q s)
  let ra (s : String) : ExceptT String IO thm := do REAL_ARITH (← q s)

  let HADAMARD_INEQUALITY_ROW ← prove
   r"!A:real^N^N. abs(det A) <= product(1..dimindex(:N)) (\i. norm(row i A))"
   (GEN_TAC THEN
    ABBREV_TAC (← q r"a = \i. (A:real^N^N)$i") THEN
    MP_TAC (← DISCH_ALL (← ExceptT.mk (instantiate_casewise_recursion (← q
     r"?b. !j. b j :real^N =
            a j - vsum(1..j-1) (\i. (a j dot b i) / (b i dot b i) % b i)")))) THEN
    ANTS_TAC THENL
     [EXISTS_TAC (← q r"(<):num->num->bool") THEN REWRITE_TAC [WF_num] THEN
      MATCH_MP_TAC ADMISSIBLE_IMP_SUPERADMISSIBLE THEN
      REWRITE_TAC [admissible] THEN REPEAT STRIP_TAC THEN
      AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
      ASM_SIMP_TAC [IN_NUMSEG, ← ar r"1 <= x /\ x <= y - 1 ==> x < y"],
      DISCH_THEN (STRIP_ASSUME_TAC o GSYM)] THEN
    ABBREV_TAC (← q r"B:real^N^N = lambda i. b i") THEN
    TRANS_TAC REAL_LE_TRANS (← q r"abs(det(B:real^N^N))") THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       (← q r"!n. det((lambda i. if i <= n then b i else a i):real^N^N) =
          det(A:real^N^N)")
       (MP_TAC o SPEC (← q r"dimindex(:N)"))
      THENL
       [MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
         [AP_TERM_TAC THEN EXPAND_TAC "a" THEN SIMP_TAC [CART_EQ, LAMBDA_BETA] THEN
          SIMP_TAC [← ar r"1 <= n ==> ~(n <= 0)"],
          X_GEN_TAC (← q r"n:num") THEN DISCH_THEN (SUBST1_TAC o SYM)] THEN
        ASM_CASES_TAC (← q r"dimindex(:N) <= n") THENL
         [AP_TERM_TAC THEN SIMP_TAC [CART_EQ, LAMBDA_BETA] THEN
          REPEAT STRIP_TAC THEN
          REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN ASM_ARITH_TAC,
          FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP (← ar
           r"~(n <= k) ==> SUC k <= n"))] THEN
        MP_TAC (← ISPECL
         [← q r"(lambda i. if i <= n then b i else a i):real^N^N",
          ← q r"SUC n",
          ← q r"--vsum (1..SUC n - 1)
                (\i. (a (SUC n) dot b i) / (b i dot b i) % b i):real^N"]
          DET_ROW_SPAN) THEN
        ASM_REWRITE_TAC [row, LAMBDA_ETA, ← ar r"1 <= SUC n"] THEN
        ANTS_TAC THENL
         [MATCH_MP_TAC SPAN_NEG THEN MATCH_MP_TAC SPAN_VSUM THEN
          REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
          X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
          MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC [IN_ELIM_THM] THEN
          EXISTS_TAC (← q r"i:num") THEN
          MATCH_MP_TAC (← TAUT (← q r"(p ==> q) /\ p ==> p /\ q")) THEN
          SIMP_TAC [LAMBDA_BETA] THEN ASM_ARITH_TAC,
          DISCH_THEN (SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
          GEN_REWRITE_TAC id [CART_EQ] THEN X_GEN_TAC (← q r"k:num") THEN
          SIMP_TAC [LAMBDA_BETA] THEN STRIP_TAC THEN
          ASM_CASES_TAC (← q r"SUC n = k") THEN
          ASM_SIMP_TAC [LE_REFL, LAMBDA_BETA, ← GSYM VECTOR_SUB, ← ar
           r"SUC n = k ==> ~(k <= n)"] THEN
          REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN ASM_ARITH_TAC],
        DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN
        GEN_REWRITE_TAC id [CART_EQ] THEN EXPAND_TAC "B" THEN
        SIMP_TAC [LAMBDA_BETA]],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
          ~(i = j)
          ==> orthogonal (b i:real^N) (b j)")
    ASSUME_TAC THENL
     [ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
      MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC [] THEN
      CONJ_TAC THENL [MESON_TAC [ORTHOGONAL_SYM], ALL_TAC] THEN
      GEN_REWRITE_TAC id [SWAP_FORALL_THM] THEN REWRITE_TAC [IMP_IMP] THEN
      REWRITE_TAC [← ar
       r"j < n /\ 1 <= n /\ n <= N /\ 1 <= j /\ j <= N /\ ~(n = j) <=>
      (1 <= n /\ n <= N) /\ (1 <= j /\ j <= N /\ j < n)"] THEN
      MATCH_MP_TAC num_WF THEN CONV_TAC NUM_REDUCE_CONV THEN
      X_GEN_TAC (← q r"n:num") THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_FORALL_THM] THEN
      REWRITE_TAC [IMP_IMP] THEN DISCH_TAC THEN
      X_GEN_TAC (← q r"m:num") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (SUBST1_TAC o SYM o SPEC (← q r"n:num")) THEN
      REWRITE_TAC [orthogonal, DOT_LSUB, REAL_SUB_0] THEN
      SIMP_TAC [DOT_LSUM, FINITE_NUMSEG, DOT_LMUL] THEN TRANS_TAC EQ_TRANS
       (← q r"sum(1..n-1) (\j. if j = m then (a n:real^N) dot (b m) else &0)") THEN
      CONJ_TAC THENL
       [REWRITE_TAC [SUM_DELTA, IN_NUMSEG] THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
        MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC (← q r"j:num") THEN STRIP_TAC THEN
        ASM_REWRITE_TAC [] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
         [ASM_CASES_TAC (← q r"(b:num->real^N) m = vec 0") THEN
          ASM_REWRITE_TAC [DOT_RZERO, REAL_MUL_RZERO] THEN
          ASM_SIMP_TAC [DOT_EQ_0, REAL_DIV_RMUL],
          CONV_TAC SYM_CONV THEN REWRITE_TAC [REAL_ENTIRE] THEN
          DISJ2_TAC THEN REWRITE_TAC [← GSYM orthogonal] THEN
          FIRST_ASSUM (DISJ_CASES_TAC o MATCH_MP (← ar
           r"~(m:num = n) ==> n < m \/ m < n"))
          THENL [ALL_TAC, ONCE_REWRITE_TAC [ORTHOGONAL_SYM]] THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!i. 1 <= i /\ i <= dimindex(:N) ==> norm(b i:real^N) <= norm(a i:real^N)")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
      FIRST_ASSUM (SUBST1_TAC o SYM o SPEC (← q r"i:num")) THEN
      REWRITE_TAC [NORM_LE, ← VECTOR_ARITH (← q
       r"(x - y:real^N) dot (x - y) = (x dot x + y dot y) - &2 * x dot y")] THEN
      REWRITE_TAC [← ra r"(a + b) - x <= a <=> b <= x"] THEN
      SIMP_TAC [DOT_RSUM, FINITE_NUMSEG, DOT_RMUL, ← GSYM SUM_LMUL] THEN
      MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC (← q r"j:num") THEN STRIP_TAC THEN
      REWRITE_TAC [] THEN MATCH_MP_TAC (← ra
       r"&0 <= x /\ x = y ==> y <= &2 * x") THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC [← ra r"x / y * x:real = (x * x) / y"] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC [REAL_LE_SQUARE, DOT_POS_LE],
        AP_TERM_TAC] THEN
      TRANS_TAC EQ_TRANS
        (← q r"sum(1..i-1) (\k. if k = j then (a i:real^N) dot (b j) else &0)") THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC [SUM_DELTA, IN_NUMSEG], ALL_TAC] THEN
      SIMP_TAC [DOT_LSUM, FINITE_NUMSEG] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC (← q r"m:num") THEN STRIP_TAC THEN
      REWRITE_TAC [DOT_LMUL] THEN
      ASM_CASES_TAC (← q r"(b:num->real^N) j = vec 0") THEN
      ASM_REWRITE_TAC [DOT_RZERO, REAL_MUL_RZERO, COND_ID] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC [DOT_EQ_0, REAL_DIV_RMUL] THEN
      CONV_TAC SYM_CONV THEN REWRITE_TAC [REAL_ENTIRE] THEN
      DISJ2_TAC THEN REWRITE_TAC [← GSYM orthogonal] THEN
      FIRST_ASSUM (DISJ_CASES_TAC o MATCH_MP (← ar
       r"~(m:num = n) ==> n < m \/ m < n"))
      THENL [ALL_TAC, ONCE_REWRITE_TAC [ORTHOGONAL_SYM]] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     (← q r"product(1..dimindex(:N)) (\i. norm(b i:real^N))") THEN
    CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN
      REWRITE_TAC [NORM_POS_LE, row, LAMBDA_ETA] THEN
      X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
      TRANS_TAC REAL_LE_TRANS (← q r"norm((a:num->real^N) i)") THEN
      ASM_SIMP_TAC [] THEN EXPAND_TAC "a" THEN REWRITE_TAC [REAL_LE_REFL]] THEN
    MATCH_MP_TAC (← ra r"&0 <= y /\ abs x <= abs y ==> abs x <= y") THEN
    SIMP_TAC [PRODUCT_POS_LE_NUMSEG, NORM_POS_LE, REAL_LE_SQUARE_ABS] THEN
    REWRITE_TAC [REAL_POW_2, ← GSYM PRODUCT_MUL_NUMSEG] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM DET_TRANSP] THEN
    REWRITE_TAC [← GSYM DET_MUL] THEN
    W (MP_TAC o PART_MATCH (lhand o rand) DET_DIAGONAL o lhand o snd) THEN
    SIMP_TAC [DIAGONAL_MATRIX_MUL_EQ, pairwise, ← GSYM ROW_TRANSP, IN_NUMSEG] THEN
    EXPAND_TAC "B" THEN
    SIMP_TAC [TRANSP_TRANSP, row, LAMBDA_ETA, LAMBDA_BETA] THEN
    ASM_REWRITE_TAC [← GSYM CONJ_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
    EXPAND_TAC "B" THEN REWRITE_TAC [transp, ← GSYM REAL_POW_2] THEN
    SIMP_TAC [matrix_mul, NORM_POW_2, dot, LAMBDA_BETA, dot])

  let HADAMARD_INEQUALITY_COLUMN ← prove
   r"!A:real^N^N. abs(det A) <= product(1..dimindex(:N)) (\i. norm(column i A))"
   (GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM DET_TRANSP] THEN
    SIMP_TAC [← GSYM ROW_TRANSP, HADAMARD_INEQUALITY_ROW])

  return { HADAMARD_INEQUALITY_ROW, HADAMARD_INEQUALITY_COLUMN }

/- ------------------------------------------------------------------------- -/
/- Orthogonality of a transformation and matrix, first part.                 -/
/- (determinants.ml 2646-2852)                                                -/
/- ------------------------------------------------------------------------- -/

structure Orth1 where
  orthogonal_transformation : thm
  ORTHOGONAL_TRANSFORMATION : thm
  ORTHOGONAL_ORTHOGONAL_TRANSFORMATION : thm
  ORTHOGONAL_TRANSFORMATION_COMPOSE : thm
  ORTHOGONAL_TRANSFORMATION_NEG : thm
  ORTHOGONAL_TRANSFORMATION_LINEAR : thm
  ORTHOGONAL_TRANSFORMATION_INJECTIVE : thm
  ORTHOGONAL_TRANSFORMATION_SURJECTIVE : thm
  orthogonal_matrix : thm
  ORTHOGONAL_MATRIX : thm
  ORTHOGONAL_MATRIX_ALT : thm
  ORTHOGONAL_MATRIX_TRANSP : thm
  ORTHOGONAL_MATRIX_TRANSP_LMUL : thm
  ORTHOGONAL_MATRIX_TRANSP_RMUL : thm
  NORM_VECTORIZE_ORTHOGONAL_MATRIX_RMUL : thm
  NORM_VECTORIZE_ORTHOGONAL_MATRIX_LMUL : thm
  ORTHOGONAL_MATRIX_ID : thm
  ORTHOGONAL_MATRIX_MUL : thm
  ORTHOGONAL_TRANSFORMATION_MATRIX : thm
  ORTHOGONAL_MATRIX_TRANSFORMATION : thm
  ORTHOGONAL_MATRIX_MATRIX : thm
  ORTHOGONAL_MATRIX_NORM_EQ : thm
  ORTHOGONAL_MATRIX_NORM : thm
  DET_ORTHOGONAL_MATRIX : thm
  ORTHOGONAL_MATRIX_IMP_INVERTIBLE : thm
  MATRIX_MUL_LTRANSP_DOT_COLUMN : thm
  MATRIX_MUL_RTRANSP_DOT_ROW : thm
  ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS : thm
  ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS : thm
  ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_INDEXED : thm
  ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_PAIRWISE : thm
  deriving Inhabited

@[nospecialize]
def setupOrth1 [HolBase] (D : DeterminantsDeps) (BTrace : Trace) (BDetBasic : DetBasic)
    (BMultilinear : Multilinear) (BInvertibility : Invertibility) (BFrobenius : Frobenius) :
    ExceptT String IO Orth1 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, NORM_ARITH, REAL_ARITH_TAC, REAL_RAT_REDUCE_CONV,
        REAL_RING, new_definition, .. } := D
  let { CARD_IMAGE_EQ_INJ, CARD_NUMSEG_1, CART_EQ, CONJ_ACI, DIMINDEX_1, FINITE_NUMSEG,
        IN_NUMSEG, LAMBDA_BETA, .. } := D.core1
  let { LE_REFL, PAIRWISE_IMAGE, REAL_MUL_LID, REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RZERO,
        .. } := D.core2
  let { REAL_POS, SIMPLE_IMAGE_GEN, SUM_DELTA, numseg, o_THM, pairwise, .. } := D.core3
  let { COLUMN_TRANSP, DOT_MATRIX_PRODUCT, DOT_MATRIX_VECTOR_MUL, DOT_NORM, LINEAR_ADD,
        LINEAR_COMPOSE, LINEAR_COMPOSE_NEG_EQ, LINEAR_INJECTIVE_0,
        LINEAR_INJECTIVE_IMP_SURJECTIVE, .. } := D.vec1
  let { MATRIX_LEFT_RIGHT_INVERSE, MATRIX_MUL_ASSOC, MATRIX_MUL_LID, MATRIX_MUL_RID,
        MATRIX_OF_MATRIX_VECTOR_MUL, MATRIX_TRANSP_MUL, MATRIX_VECTOR_MUL_LINEAR, MATRIX_WORKS,
        MAT_COMPONENT, NORM_EQ, NORM_EQ_0, NORM_EQ_1, NORM_EQ_SQUARE, NORM_NEG,
        ORTHOGONAL_REFL, .. } := D.vec2
  let { TRANSP_MAT, TRANSP_TRANSP, basis, column, columnvector, dot, mat, matrix_mul,
        orthogonal, row, rows, rowvector, transp, vector_norm, .. } := D.vec3
  let { TRACE_MUL_SYM, .. } := BTrace
  let { DET_I, DET_TRANSP, .. } := BDetBasic
  let { DET_MUL, .. } := BMultilinear
  let { INVERTIBLE_DET_NZ, .. } := BInvertibility
  let { DOT_VECTORIZE, NORM_VECTORIZE_TRANSP, .. } := BFrobenius
  -- @@SCOPE END

  let orthogonal_transformation ← new_definition
   r"orthogonal_transformation(f:real^N->real^N) <=>
        linear f /\ !v w. f(v) dot f(w) = v dot w"

  let ORTHOGONAL_TRANSFORMATION ← prove
   r"!f. orthogonal_transformation f <=> linear f /\ !v. norm(f v) = norm(v)"
   (GEN_TAC THEN REWRITE_TAC [orthogonal_transformation] THEN EQ_TAC THENL
     [MESON_TAC [vector_norm], SIMP_TAC [DOT_NORM] THEN MESON_TAC [LINEAR_ADD]])

  let ORTHOGONAL_ORTHOGONAL_TRANSFORMATION ← prove
   r"!f x y:real^N.
        orthogonal_transformation f
        ==> (orthogonal (f x) (f y) <=> orthogonal x y)"
   (SIMP_TAC [orthogonal, orthogonal_transformation])

  let ORTHOGONAL_TRANSFORMATION_COMPOSE ← prove
   r"!f g. orthogonal_transformation f /\ orthogonal_transformation g
         ==> orthogonal_transformation(f o g)"
   (SIMP_TAC [orthogonal_transformation, LINEAR_COMPOSE, o_THM])

  let ORTHOGONAL_TRANSFORMATION_NEG ← prove
   r"!f:real^N->real^N.
     orthogonal_transformation(\x. --(f x)) <=> orthogonal_transformation f"
   (REWRITE_TAC [ORTHOGONAL_TRANSFORMATION, LINEAR_COMPOSE_NEG_EQ, NORM_NEG])

  let ORTHOGONAL_TRANSFORMATION_LINEAR ← prove
   r"!f:real^N->real^N. orthogonal_transformation f ==> linear f"
   (SIMP_TAC [orthogonal_transformation])

  let ORTHOGONAL_TRANSFORMATION_INJECTIVE ← prove
   r"!f:real^N->real^N.
        orthogonal_transformation f ==> !x y. f x = f y ==> x = y"
   (SIMP_TAC [LINEAR_INJECTIVE_0, ORTHOGONAL_TRANSFORMATION, ← GSYM NORM_EQ_0])

  let ORTHOGONAL_TRANSFORMATION_SURJECTIVE ← prove
   r"!f:real^N->real^N.
        orthogonal_transformation f ==> !y. ?x. f x = y"
   (MESON_TAC [LINEAR_INJECTIVE_IMP_SURJECTIVE,
               ORTHOGONAL_TRANSFORMATION_INJECTIVE, orthogonal_transformation])

  let orthogonal_matrix ← new_definition
   r"orthogonal_matrix(Q:real^N^N) <=>
      transp(Q) ** Q = mat 1 /\ Q ** transp(Q) = mat 1"

  let ORTHOGONAL_MATRIX ← prove
   r"orthogonal_matrix(Q:real^N^N) <=> transp(Q) ** Q = mat 1"
   (MESON_TAC [MATRIX_LEFT_RIGHT_INVERSE, orthogonal_matrix])

  let ORTHOGONAL_MATRIX_ALT ← prove
   r"!A:real^N^N. orthogonal_matrix A <=> A ** transp A = mat 1"
   (MESON_TAC [MATRIX_LEFT_RIGHT_INVERSE, orthogonal_matrix])

  let ORTHOGONAL_MATRIX_TRANSP ← prove
   r"!A:real^N^N. orthogonal_matrix(transp A) <=> orthogonal_matrix A"
   (REWRITE_TAC [orthogonal_matrix, TRANSP_TRANSP, CONJ_ACI])

  let ORTHOGONAL_MATRIX_TRANSP_LMUL ← prove
   r"!P:real^N^N. orthogonal_matrix P ==> transp P ** P = mat 1"
   (REWRITE_TAC [ORTHOGONAL_MATRIX])

  let ORTHOGONAL_MATRIX_TRANSP_RMUL ← prove
   r"!P:real^N^N. orthogonal_matrix P ==> P ** transp P = mat 1"
   (REWRITE_TAC [ORTHOGONAL_MATRIX_ALT])

  let NORM_VECTORIZE_ORTHOGONAL_MATRIX_RMUL ← prove
   r"!A:real^N^N P:real^N^N.
       orthogonal_matrix P ==> norm(vectorize(A ** P)) = norm(vectorize A)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [NORM_EQ, DOT_VECTORIZE, MATRIX_TRANSP_MUL] THEN
    GEN_REWRITE_TAC LAND_CONV [TRACE_MUL_SYM] THEN
    ONCE_REWRITE_TAC [MATRIX_MUL_ASSOC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV)
     [← GSYM MATRIX_MUL_ASSOC] THEN
    ASM_SIMP_TAC [ORTHOGONAL_MATRIX_TRANSP_RMUL, MATRIX_MUL_RID] THEN
    MATCH_ACCEPT_TAC TRACE_MUL_SYM)

  let NORM_VECTORIZE_ORTHOGONAL_MATRIX_LMUL ← prove
   r"!A:real^N^N P:real^N^N.
       orthogonal_matrix P ==> norm(vectorize(P ** A)) = norm(vectorize A)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM NORM_VECTORIZE_TRANSP] THEN
    REWRITE_TAC [MATRIX_TRANSP_MUL] THEN
    MATCH_MP_TAC NORM_VECTORIZE_ORTHOGONAL_MATRIX_RMUL THEN
    ASM_REWRITE_TAC [ORTHOGONAL_MATRIX_TRANSP])

  let ORTHOGONAL_MATRIX_ID ← prove
   r"orthogonal_matrix(mat 1)"
   (REWRITE_TAC [orthogonal_matrix, TRANSP_MAT, MATRIX_MUL_LID])

  let ORTHOGONAL_MATRIX_MUL ← prove
   r"!A B. orthogonal_matrix A /\ orthogonal_matrix B
         ==> orthogonal_matrix(A ** B)"
   (REWRITE_TAC [orthogonal_matrix, MATRIX_TRANSP_MUL] THEN
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM MATRIX_MUL_ASSOC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [MATRIX_MUL_ASSOC] THEN
    ASM_REWRITE_TAC [MATRIX_MUL_LID, MATRIX_MUL_RID])

  let ORTHOGONAL_TRANSFORMATION_MATRIX ← prove
   r"!f:real^N->real^N.
     orthogonal_transformation f <=> linear f /\ orthogonal_matrix(matrix f)"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [REWRITE_TAC [orthogonal_transformation, ORTHOGONAL_MATRIX] THEN
      STRIP_TAC THEN ASM_SIMP_TAC [CART_EQ, LAMBDA_BETA] THEN
      X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
      X_GEN_TAC (← q r"j:num") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"basis i:real^N", ← q r"basis j:real^N"]) THEN
      FIRST_ASSUM (fun th => tactic_of do
        pure (REWRITE_TAC [← GSYM (← MATCH_MP MATRIX_WORKS th)])) THEN
      REWRITE_TAC [DOT_MATRIX_VECTOR_MUL] THEN
      ABBREV_TAC (← q r"A = transp (matrix f) ** matrix(f:real^N->real^N)") THEN
      ASM_SIMP_TAC [matrix_mul, columnvector, rowvector, basis, LAMBDA_BETA,
               SUM_DELTA, DIMINDEX_1, LE_REFL, dot, IN_NUMSEG, mat,
               ← MESON [REAL_MUL_LID, REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RZERO] (← q
                r"(if b then &1 else &0) * x = (if b then x else &0) /\
               x * (if b then &1 else &0) = (if b then x else &0)")],
      REWRITE_TAC [orthogonal_matrix, ORTHOGONAL_TRANSFORMATION, NORM_EQ] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      FIRST_ASSUM (fun th => tactic_of do
        pure (REWRITE_TAC [← GSYM (← MATCH_MP MATRIX_WORKS th)])) THEN
      ASM_REWRITE_TAC [DOT_MATRIX_VECTOR_MUL] THEN
      SIMP_TAC [DOT_MATRIX_PRODUCT, MATRIX_MUL_LID]])

  let ORTHOGONAL_MATRIX_TRANSFORMATION ← prove
   r"!A:real^N^N. orthogonal_matrix A <=> orthogonal_transformation(\x. A ** x)"
   (REWRITE_TAC [ORTHOGONAL_TRANSFORMATION_MATRIX, MATRIX_VECTOR_MUL_LINEAR] THEN
    REWRITE_TAC [MATRIX_OF_MATRIX_VECTOR_MUL])

  let ORTHOGONAL_MATRIX_MATRIX ← prove
   r"!f:real^N->real^N.
    orthogonal_transformation f ==> orthogonal_matrix(matrix f)"
   (SIMP_TAC [ORTHOGONAL_TRANSFORMATION_MATRIX])

  let ORTHOGONAL_MATRIX_NORM_EQ ← prove
   r"!A. orthogonal_matrix A <=> !x. norm(A ** x) = norm x"
   (REWRITE_TAC [ORTHOGONAL_MATRIX_TRANSFORMATION, MATRIX_VECTOR_MUL_LINEAR,
                 ORTHOGONAL_TRANSFORMATION])

  let ORTHOGONAL_MATRIX_NORM ← prove
   r"!A x:real^N. orthogonal_matrix A ==> norm(A ** x) = norm x"
   (SIMP_TAC [ORTHOGONAL_MATRIX_TRANSFORMATION, ORTHOGONAL_TRANSFORMATION])

  let DET_ORTHOGONAL_MATRIX ← prove
   r"!Q. orthogonal_matrix Q ==> det(Q) = &1 \/ det(Q) = -- &1"
   (GEN_TAC THEN REWRITE_TAC [← REAL_RING (← q r"x = &1 \/ x = -- &1 <=> x * x = &1")] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [← GSYM DET_TRANSP] THEN
    SIMP_TAC [← GSYM DET_MUL, orthogonal_matrix, DET_I])

  let ORTHOGONAL_MATRIX_IMP_INVERTIBLE ← prove
   r"!A:real^N^N. orthogonal_matrix A ==> invertible A"
   (GEN_TAC THEN REWRITE_TAC [INVERTIBLE_DET_NZ] THEN
    DISCH_THEN (MP_TAC o MATCH_MP DET_ORTHOGONAL_MATRIX) THEN
    REAL_ARITH_TAC)

  let MATRIX_MUL_LTRANSP_DOT_COLUMN ← prove
   r"!A:real^N^M. transp A ** A = (lambda i j. (column i A) dot (column j A))"
   (SIMP_TAC [matrix_mul, CART_EQ, LAMBDA_BETA, transp, dot, column])

  let MATRIX_MUL_RTRANSP_DOT_ROW ← prove
   r"!A:real^N^M. A ** transp A = (lambda i j. (row i A) dot (row j A))"
   (SIMP_TAC [matrix_mul, CART_EQ, LAMBDA_BETA, transp, dot, row])

  let ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS ← prove
   r"!A:real^N^N.
        orthogonal_matrix A <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(column i A) = &1) /\
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
               ==> orthogonal (column i A) (column j A))"
   (REWRITE_TAC [ORTHOGONAL_MATRIX] THEN
    SIMP_TAC [MATRIX_MUL_LTRANSP_DOT_COLUMN, CART_EQ, mat, LAMBDA_BETA] THEN
    REWRITE_TAC [orthogonal, NORM_EQ_1] THEN MESON_TAC [])

  let ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS ← prove
   r"!A:real^N^N.
        orthogonal_matrix A <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(row i A) = &1) /\
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
               ==> orthogonal (row i A) (row j A))"
   (ONCE_REWRITE_TAC [← GSYM ORTHOGONAL_MATRIX_TRANSP] THEN
    SIMP_TAC [ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS, COLUMN_TRANSP])

  let ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_INDEXED ← prove
   r"!A:real^N^N.
        orthogonal_matrix A <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(row i A) = &1) /\
        pairwise (\i j. orthogonal (row i A) (row j A)) (1..dimindex(:N))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [ORTHOGONAL_MATRIX_ALT] THEN
    SIMP_TAC [CART_EQ, LAMBDA_BETA, pairwise, MAT_COMPONENT] THEN
    SIMP_TAC [MATRIX_MUL_RTRANSP_DOT_ROW, IN_NUMSEG, LAMBDA_BETA] THEN
    REWRITE_TAC [NORM_EQ_SQUARE, REAL_POS] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [orthogonal] THEN
    MESON_TAC [])

  let ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_PAIRWISE ← prove
   r"!A:real^N^N.
        orthogonal_matrix A <=>
        CARD(rows A) = dimindex(:N) /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(row i A) = &1) /\
        pairwise orthogonal (rows A)"
   (REWRITE_TAC [rows, ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_INDEXED] THEN
    GEN_TAC THEN ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC [PAIRWISE_IMAGE, ← GSYM numseg] THEN
    MATCH_MP_TAC (← TAUT (← q r"(p ==> (q <=> r /\ s)) ==> (p /\ q <=> r /\ p /\ s)")) THEN
    DISCH_TAC THEN GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV)
      [← GSYM CARD_NUMSEG_1] THEN
    SIMP_TAC [CARD_IMAGE_EQ_INJ, FINITE_NUMSEG] THEN
    REWRITE_TAC [pairwise, IN_NUMSEG] THEN
    ASM_MESON_TAC [ORTHOGONAL_REFL, ← NORM_ARITH (← q r"~(norm(vec 0:real^N) = &1)")])

  return { orthogonal_transformation, ORTHOGONAL_TRANSFORMATION,
           ORTHOGONAL_ORTHOGONAL_TRANSFORMATION, ORTHOGONAL_TRANSFORMATION_COMPOSE,
           ORTHOGONAL_TRANSFORMATION_NEG, ORTHOGONAL_TRANSFORMATION_LINEAR,
           ORTHOGONAL_TRANSFORMATION_INJECTIVE, ORTHOGONAL_TRANSFORMATION_SURJECTIVE,
           orthogonal_matrix, ORTHOGONAL_MATRIX, ORTHOGONAL_MATRIX_ALT,
           ORTHOGONAL_MATRIX_TRANSP, ORTHOGONAL_MATRIX_TRANSP_LMUL,
           ORTHOGONAL_MATRIX_TRANSP_RMUL, NORM_VECTORIZE_ORTHOGONAL_MATRIX_RMUL,
           NORM_VECTORIZE_ORTHOGONAL_MATRIX_LMUL, ORTHOGONAL_MATRIX_ID, ORTHOGONAL_MATRIX_MUL,
           ORTHOGONAL_TRANSFORMATION_MATRIX, ORTHOGONAL_MATRIX_TRANSFORMATION,
           ORTHOGONAL_MATRIX_MATRIX, ORTHOGONAL_MATRIX_NORM_EQ, ORTHOGONAL_MATRIX_NORM,
           DET_ORTHOGONAL_MATRIX, ORTHOGONAL_MATRIX_IMP_INVERTIBLE,
           MATRIX_MUL_LTRANSP_DOT_COLUMN, MATRIX_MUL_RTRANSP_DOT_ROW,
           ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS, ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS,
           ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_INDEXED,
           ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_PAIRWISE }

/- ------------------------------------------------------------------------- -/
/- Orthogonality of a transformation and matrix, second part.                -/
/- (determinants.ml 2853-3079)                                                -/
/- ------------------------------------------------------------------------- -/

structure Orth2 where
  ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_SPAN : thm
  ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS_INDEXED : thm
  ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS_PAIRWISE : thm
  ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS_SPAN : thm
  ORTHOGONAL_MATRIX_2 : thm
  ORTHOGONAL_MATRIX_2_ALT : thm
  ORTHOGONAL_MATRIX_INV : thm
  ORTHOGONAL_MATRIX_INV_EQ : thm
  ORTHOGONAL_TRANSFORMATION_ORTHOGONAL_EIGENVECTORS : thm
  ORTHOGONAL_MATRIX_ORTHOGONAL_EIGENVECTORS : thm
  ORTHOGONAL_TRANSFORMATION_ID : thm
  ORTHOGONAL_TRANSFORMATION_I : thm
  ORTHOGONAL_TRANSFORMATION_NEGATION : thm
  ORTHOGONAL_TRANSFORMATION_1_GEN : thm
  ORTHOGONAL_MATRIX_1 : thm
  MATRIX_INV_ORTHOGONAL_LMUL : thm
  MATRIX_INV_ORTHOGONAL_RMUL : thm
  ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT_LEFT : thm
  ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT_RIGHT : thm
  ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT : thm
  ORTHOGONAL_TRANSFORMATION_ADJOINT : thm
  /-- In HOL Light this is a (term, tactic) pair, not a theorem: the source
      omits `prove`. -/
  ORTHOGONAL_TRANSFORMATION_ADJOINT_EQ : term × tactic
  ONORM_ORTHOGONAL_TRANSFORMATION : thm
  ONORM_ORTHOGONAL_MATRIX : thm
  deriving Inhabited

@[nospecialize]
def setupOrth2 [HolBase] (D : DeterminantsDeps) (BOrth1 : Orth1) :
    ExceptT String IO Orth2 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, NORM_ARITH, NUM_REDUCE_CONV, REAL_ARITH, REAL_RING,
        SET_RULE, VECTOR_ARITH, .. } := D
  let { CART_EQ, DIMINDEX_1, DIMINDEX_2, DIMINDEX_GE_1, ETA_AX, FORALL_IN_GSPEC, FUN_EQ_THM,
        IN_ELIM_THM, IN_NUMSEG, I_DEF, LAMBDA_BETA, .. } := D.core1
  let { LE_REFL, REAL_MUL_ASSOC, REAL_NEG_NEG, .. } := D.core2
  let { SUBSET_UNIV, SUP_UNIQUE, SWAP_FORALL_THM, o_THM, pairwise, .. } := D.core3
  let { I_THM, MONO_OR, .. } := D.core4
  let { ADJOINT_ADJOINT, ADJOINT_LINEAR, ADJOINT_WORKS, CARD_GE_DIM_INDEPENDENT, DIM_EQ_CARD,
        DIM_SPAN, DIM_UNIV, DOT_EQ_0, DOT_LMUL, DOT_LNEG, DOT_LZERO, DOT_RMUL, DOT_RNEG,
        DOT_RZERO, FORALL_2, LINEAR_1_GEN, LINEAR_ID, LINEAR_INVERSE_LEFT, LINEAR_NEGATION,
        MATRIX_EQ, .. } := D.vec1
  let { MATRIX_INV_INV, MATRIX_INV_MUL_INNER, MATRIX_INV_MUL_OUTER, MATRIX_INV_UNIQUE,
        MATRIX_INV_UNIQUE_STRONG, MATRIX_MUL_ASSOC, MATRIX_MUL_LCANCEL, MATRIX_MUL_LID,
        MATRIX_MUL_RCANCEL, MATRIX_TRANSP_MUL, MATRIX_VECTOR_MUL_LID, MATRIX_VECTOR_MUL_LNEG,
        MAT_COMPONENT, NORM_BASIS, NORM_EQ, NORM_MUL, PAIRWISE_ORTHOGONAL_INDEPENDENT,
        ROWS_TRANSP, ROW_TRANSP, .. } := D.vec2
  let { SUM_2, SYMMETRIC_MATRIX_INV_LMUL, SYMMETRIC_MATRIX_INV_RMUL, TRANSP_COMPONENT,
        TRANSP_EQ, TRANSP_MATRIX_INV, TRANSP_TRANSP, VECTOR_EQ_LDOT, matrix_mul, onorm,
        orthogonal, rows, symmetric_matrix, .. } := D.vec3
  let { ORTHOGONAL_MATRIX_IMP_INVERTIBLE, ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_INDEXED,
        ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_PAIRWISE, ORTHOGONAL_MATRIX_TRANSFORMATION,
        ORTHOGONAL_MATRIX_TRANSP, ORTHOGONAL_TRANSFORMATION, ORTHOGONAL_TRANSFORMATION_NEG,
        orthogonal_matrix, orthogonal_transformation, .. } := BOrth1
  -- @@SCOPE END

  let ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_SPAN ← prove
   r"!A:real^N^N.
        orthogonal_matrix A <=>
        span(rows A) = (:real^N) /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(row i A) = &1) /\
        pairwise orthogonal (rows A)"
   (GEN_TAC THEN REWRITE_TAC [ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_PAIRWISE] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
     [MATCH_MP_TAC (← SET_RULE (← q r"UNIV SUBSET s ==> s = UNIV")) THEN
      MATCH_MP_TAC CARD_GE_DIM_INDEPENDENT THEN
      ASM_REWRITE_TAC [DIM_UNIV, SUBSET_UNIV, LE_REFL],
      CONV_TAC SYM_CONV THEN REWRITE_TAC [← GSYM DIM_UNIV] THEN
      FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [DIM_SPAN] THEN
      MATCH_MP_TAC DIM_EQ_CARD] THEN
    MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN
    ASM_REWRITE_TAC [rows, IN_ELIM_THM] THEN
    ASM_MESON_TAC [← NORM_ARITH (← q r"~(norm(vec 0:real^N) = &1)")])

  let ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS_INDEXED ← prove
   r"!A:real^N^N.
      orthogonal_matrix A <=>
      (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(column i A) = &1) /\
      pairwise (\i j. orthogonal (column i A) (column j A)) (1..dimindex(:N))"
   (ONCE_REWRITE_TAC [← GSYM ORTHOGONAL_MATRIX_TRANSP] THEN
    REWRITE_TAC [ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_INDEXED] THEN
    SIMP_TAC [ROW_TRANSP, ROWS_TRANSP, pairwise, IN_NUMSEG])

  let ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS_PAIRWISE ← prove
   r"!A:real^N^N.
        orthogonal_matrix A <=>
        CARD(columns A) = dimindex(:N) /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(column i A) = &1) /\
        pairwise orthogonal (columns A)"
   (ONCE_REWRITE_TAC [← GSYM ORTHOGONAL_MATRIX_TRANSP] THEN
    REWRITE_TAC [ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_PAIRWISE] THEN
    SIMP_TAC [ROW_TRANSP, ROWS_TRANSP])

  let ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS_SPAN ← prove
   r"!A:real^N^N.
        orthogonal_matrix A <=>
        span(columns A) = (:real^N) /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(column i A) = &1) /\
        pairwise orthogonal (columns A)"
   (ONCE_REWRITE_TAC [← GSYM ORTHOGONAL_MATRIX_TRANSP] THEN
    REWRITE_TAC [ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_SPAN] THEN
    SIMP_TAC [ROW_TRANSP, ROWS_TRANSP])

  let ORTHOGONAL_MATRIX_2 ← prove
   r"!A:real^2^2. orthogonal_matrix A <=>
                A$1$1 pow 2 + A$2$1 pow 2 = &1 /\
                A$1$2 pow 2 + A$2$2 pow 2 = &1 /\
                A$1$1 * A$1$2 + A$2$1 * A$2$2 = &0"
   (SIMP_TAC [orthogonal_matrix, CART_EQ, matrix_mul, LAMBDA_BETA,
              TRANSP_COMPONENT, MAT_COMPONENT] THEN
    REWRITE_TAC [DIMINDEX_2, FORALL_2, SUM_2] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC (fun t => REAL_RING t))

  let ORTHOGONAL_MATRIX_2_ALT ← prove
   r"!A:real^2^2. orthogonal_matrix A <=>
                A$1$1 pow 2 + A$2$1 pow 2 = &1 /\
                (A$1$1 = A$2$2 /\ A$1$2 = --(A$2$1) \/
                 A$1$1 = --(A$2$2) /\ A$1$2 = A$2$1)"
   (REWRITE_TAC [ORTHOGONAL_MATRIX_2] THEN CONV_TAC (fun t => REAL_RING t))

  let ORTHOGONAL_MATRIX_INV ← prove
   r"!A:real^N^N. orthogonal_matrix A ==> matrix_inv A = transp A"
   (MESON_TAC [orthogonal_matrix, MATRIX_INV_UNIQUE])

  let ORTHOGONAL_MATRIX_INV_EQ ← prove
   r"!A:real^N^N. orthogonal_matrix(matrix_inv A) <=> orthogonal_matrix A"
   (MATCH_MP_TAC (← MESON [] (← q
     r"(!x. f(f x) = x) /\ (!x. P x ==> P(f x)) ==> (!x. P(f x) <=> P x)")) THEN
    REWRITE_TAC [MATRIX_INV_INV] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP ORTHOGONAL_MATRIX_INV) THEN
    ASM_REWRITE_TAC [ORTHOGONAL_MATRIX_TRANSP])

  let ORTHOGONAL_TRANSFORMATION_ORTHOGONAL_EIGENVECTORS ← prove
   r"!f:real^N->real^N v w a b.
        orthogonal_transformation f /\ f v = a % v /\ f w = b % w /\ ~(a = b)
        ==> orthogonal v w"
   (REWRITE_TAC [orthogonal_transformation] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      pure (MP_TAC (← SPECL [← q r"v:real^N", ← q r"v:real^N"] th) THEN
            MP_TAC (← SPECL [← q r"v:real^N", ← q r"w:real^N"] th) THEN
            MP_TAC (← SPECL [← q r"w:real^N", ← q r"w:real^N"] th))) THEN
    ASM_REWRITE_TAC [DOT_LMUL, DOT_RMUL, orthogonal] THEN
    REWRITE_TAC [REAL_MUL_ASSOC, ← REAL_RING (← q r"x * y = y <=> x = &1 \/ y = &0")] THEN
    REWRITE_TAC [DOT_EQ_0] THEN
    ASM_CASES_TAC (← q r"v:real^N = vec 0") THEN ASM_REWRITE_TAC [DOT_LZERO] THEN
    ASM_CASES_TAC (← q r"w:real^N = vec 0") THEN ASM_REWRITE_TAC [DOT_RZERO] THEN
    ASM_CASES_TAC (← q r"(v:real^N) dot w = &0") THEN ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC (← q r"~(a:real = b)") THEN CONV_TAC (fun t => REAL_RING t))

  let ORTHOGONAL_MATRIX_ORTHOGONAL_EIGENVECTORS ← prove
   r"!A:real^N^N v w a b.
        orthogonal_matrix A /\ A ** v = a % v /\ A ** w = b % w /\ ~(a = b)
        ==> orthogonal v w"
   (REWRITE_TAC [ORTHOGONAL_MATRIX_TRANSFORMATION,
                 ORTHOGONAL_TRANSFORMATION_ORTHOGONAL_EIGENVECTORS])

  let ORTHOGONAL_TRANSFORMATION_ID ← prove
   r"orthogonal_transformation(\x. x)"
   (REWRITE_TAC [orthogonal_transformation, LINEAR_ID])

  let ORTHOGONAL_TRANSFORMATION_I ← prove
   r"orthogonal_transformation I"
   (REWRITE_TAC [I_DEF, ORTHOGONAL_TRANSFORMATION_ID])

  let ORTHOGONAL_TRANSFORMATION_NEGATION ← prove
   r"orthogonal_transformation(--)"
   (REWRITE_TAC [orthogonal_transformation, LINEAR_NEGATION, DOT_LNEG, DOT_RNEG,
                 REAL_NEG_NEG])

  let ORTHOGONAL_TRANSFORMATION_1_GEN ← prove
   r"!f:real^N->real^N.
        dimindex(:N) = 1
        ==> (orthogonal_transformation f <=> f = I \/ f = (--))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [I_DEF] THEN
    GEN_REWRITE_TAC (funpow 3 RAND_CONV) [← GSYM ETA_AX] THEN
    EQ_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [ORTHOGONAL_TRANSFORMATION_ID,
                     ORTHOGONAL_TRANSFORMATION_NEG] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [ORTHOGONAL_TRANSFORMATION]) THEN
    ASM_SIMP_TAC [LINEAR_1_GEN] THEN
    DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC [NORM_MUL] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"basis 1:real^N")) THEN
    SIMP_TAC [NORM_BASIS, DIMINDEX_GE_1, LE_REFL, DIMINDEX_1] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"abs x * &1 = &1 <=> x = &1 \/ x = -- &1")] THEN
    MATCH_MP_TAC MONO_OR THEN SIMP_TAC [FUN_EQ_THM] THEN
    REPEAT STRIP_TAC THEN CONV_TAC (fun t => VECTOR_ARITH t))

  let ORTHOGONAL_MATRIX_1 ← prove
   r"!m:real^N^N.
        dimindex(:N) = 1
        ==> (orthogonal_matrix m <=> m = mat 1 \/ m = --mat 1)"
   (REWRITE_TAC [ORTHOGONAL_MATRIX_TRANSFORMATION] THEN
    SIMP_TAC [ORTHOGONAL_TRANSFORMATION_1_GEN] THEN
    REWRITE_TAC [MATRIX_EQ, FUN_EQ_THM] THEN
    REWRITE_TAC [MATRIX_VECTOR_MUL_LID, MATRIX_VECTOR_MUL_LNEG] THEN
    REWRITE_TAC [I_THM])

  let MATRIX_INV_ORTHOGONAL_LMUL ← prove
   r"!U A:real^M^N.
        orthogonal_matrix U
        ==> matrix_inv(U ** A) = matrix_inv A ** matrix_inv U"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN
    REWRITE_TAC [symmetric_matrix] THEN
    REWRITE_TAC [MATRIX_TRANSP_MUL, ← GSYM MATRIX_MUL_ASSOC] THEN
    ASM_SIMP_TAC [ORTHOGONAL_MATRIX_INV, TRANSP_TRANSP] THEN
    REWRITE_TAC [← MESON [MATRIX_MUL_ASSOC] (← q
     r"(A:real^M^N) ** transp U ** U ** (B:real^P^M) =
    A ** (transp U ** U) ** B")] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [orthogonal_matrix]) THEN
    ASM_REWRITE_TAC [MATRIX_MUL_LID] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [← GSYM orthogonal_matrix]) THEN
    ASM_SIMP_TAC [MATRIX_MUL_LCANCEL, ORTHOGONAL_MATRIX_IMP_INVERTIBLE] THEN
    REWRITE_TAC [MATRIX_MUL_ASSOC] THEN
    ASM_SIMP_TAC [MATRIX_MUL_RCANCEL, ORTHOGONAL_MATRIX_IMP_INVERTIBLE,
                  ORTHOGONAL_MATRIX_TRANSP] THEN
    REWRITE_TAC [← GSYM MATRIX_TRANSP_MUL, ← GSYM MATRIX_MUL_ASSOC] THEN
    REWRITE_TAC [← REWRITE_RULE [symmetric_matrix] SYMMETRIC_MATRIX_INV_LMUL,
                 ← REWRITE_RULE [symmetric_matrix] SYMMETRIC_MATRIX_INV_RMUL,
                 MATRIX_INV_MUL_INNER, MATRIX_INV_MUL_OUTER])

  let MATRIX_INV_ORTHOGONAL_RMUL ← prove
   r"!U A:real^M^N.
        orthogonal_matrix U
        ==> matrix_inv(A ** U) = matrix_inv U ** matrix_inv A"
   (ONCE_REWRITE_TAC [← GSYM TRANSP_EQ, ← GSYM ORTHOGONAL_MATRIX_TRANSP] THEN
    SIMP_TAC [TRANSP_MATRIX_INV, MATRIX_TRANSP_MUL, MATRIX_INV_ORTHOGONAL_LMUL])

  let ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT_LEFT ← prove
   r"!f:real^N->real^N.
        orthogonal_transformation f <=> linear f /\ adjoint f o f = I"
   (GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM, I_THM, o_THM] THEN EQ_TAC THENL
     [REWRITE_TAC [orthogonal_transformation] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC [] THEN
      FIRST_ASSUM (fun th => tactic_of do
        pure (REWRITE_TAC [← MATCH_MP ADJOINT_WORKS th])) THEN
      ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN REWRITE_TAC [VECTOR_EQ_LDOT],
      STRIP_TAC THEN ASM_REWRITE_TAC [ORTHOGONAL_TRANSFORMATION] THEN
      REWRITE_TAC [NORM_EQ] THEN
      FIRST_ASSUM (fun th => tactic_of do
        pure (REWRITE_TAC [← MATCH_MP ADJOINT_WORKS th])) THEN
      ASM_REWRITE_TAC []])

  let ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT_RIGHT ← prove
   r"!f:real^N->real^N.
        orthogonal_transformation f <=> linear f /\ f o adjoint f = I"
   (GEN_TAC THEN REWRITE_TAC [ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT_LEFT] THEN
    MESON_TAC [ADJOINT_LINEAR, LINEAR_INVERSE_LEFT])

  let ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT ← prove
   r"!f:real^N->real^N.
        orthogonal_transformation f <=>
        linear f /\ adjoint f o f = I /\ f o adjoint f = I"
   (MESON_TAC [ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT_LEFT,
               ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT_RIGHT])

  let ORTHOGONAL_TRANSFORMATION_ADJOINT ← prove
   r"!f:real^N->real^N.
        orthogonal_transformation f ==> orthogonal_transformation(adjoint f)"
   (REWRITE_TAC [ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT_LEFT] THEN
    SIMP_TAC [ADJOINT_ADJOINT, ADJOINT_LINEAR] THEN
    MESON_TAC [ADJOINT_LINEAR, LINEAR_INVERSE_LEFT])

  let ORTHOGONAL_TRANSFORMATION_ADJOINT_EQ : term × tactic :=
   (← q r"!f:real^N->real^N.
        linear f
        ==> (orthogonal_transformation(adjoint f) <=>
             orthogonal_transformation f)",
    MESON_TAC [ORTHOGONAL_TRANSFORMATION_ADJOINT, ADJOINT_LINEAR,
               ADJOINT_ADJOINT])

  let ONORM_ORTHOGONAL_TRANSFORMATION ← prove
   r"!f:real^N->real^N. orthogonal_transformation f ==> onorm f = &1"
   (SIMP_TAC [ORTHOGONAL_TRANSFORMATION, onorm] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUP_UNIQUE THEN
    REWRITE_TAC [FORALL_IN_GSPEC] THEN
    X_GEN_TAC (← q r"c:real") THEN EQ_TAC THENL [ALL_TAC, MESON_TAC []] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"basis 1:real^N")) THEN
    SIMP_TAC [NORM_BASIS, DIMINDEX_GE_1, LE_REFL])

  let ONORM_ORTHOGONAL_MATRIX ← prove
   r"!A:real^N^N. orthogonal_matrix A ==> onorm(\x. A ** x) = &1"
   (REWRITE_TAC [ORTHOGONAL_MATRIX_TRANSFORMATION] THEN
    REWRITE_TAC [ONORM_ORTHOGONAL_TRANSFORMATION])

  return { ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_SPAN,
           ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS_INDEXED,
           ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS_PAIRWISE,
           ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS_SPAN, ORTHOGONAL_MATRIX_2,
           ORTHOGONAL_MATRIX_2_ALT, ORTHOGONAL_MATRIX_INV, ORTHOGONAL_MATRIX_INV_EQ,
           ORTHOGONAL_TRANSFORMATION_ORTHOGONAL_EIGENVECTORS,
           ORTHOGONAL_MATRIX_ORTHOGONAL_EIGENVECTORS, ORTHOGONAL_TRANSFORMATION_ID,
           ORTHOGONAL_TRANSFORMATION_I, ORTHOGONAL_TRANSFORMATION_NEGATION,
           ORTHOGONAL_TRANSFORMATION_1_GEN, ORTHOGONAL_MATRIX_1, MATRIX_INV_ORTHOGONAL_LMUL,
           MATRIX_INV_ORTHOGONAL_RMUL, ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT_LEFT,
           ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT_RIGHT, ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT,
           ORTHOGONAL_TRANSFORMATION_ADJOINT, ORTHOGONAL_TRANSFORMATION_ADJOINT_EQ,
           ONORM_ORTHOGONAL_TRANSFORMATION, ONORM_ORTHOGONAL_MATRIX }

/- ------------------------------------------------------------------------- -/
/- Linearity of scaling and isometry; orthogonality-preserving maps are      -/
/- similarities; orthogonal transformations as isometries; extending an      -/
/- isometry from the unit sphere.  (determinants.ml 3085-3295)               -/
/- ------------------------------------------------------------------------- -/

structure Iso where
  SCALING_LINEAR : thm
  ISOMETRY_LINEAR : thm
  ISOMETRY_IMP_AFFINITY : thm
  ORTHOGONALITY_PRESERVING_IMP_SCALING : thm
  ORTHOGONALITY_PRESERVING_EQ_SIMILARITY_ALT : thm
  ORTHOGONALITY_PRESERVING_EQ_SIMILARITY : thm
  ORTHOGONAL_TRANSFORMATION_ISOMETRY : thm
  ISOMETRY_SPHERE_EXTEND : thm
  ORTHOGONAL_TRANSFORMATION_INVERSE_o : thm
  ORTHOGONAL_TRANSFORMATION_INVERSE : thm
  ONORM_COMPOSE_ORTHOGONAL_TRANSFORMATION_LEFT : thm
  ONORM_COMPOSE_ORTHOGONAL_TRANSFORMATION_RIGHT : thm
  deriving Inhabited

@[nospecialize]
def setupIso [HolBase] (D : DeterminantsDeps) (BOrth1 : Orth1) (BOrth2 : Orth2) :
    ExceptT String IO Iso := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, NORM_ARITH, REAL_ARITH, REAL_ARITH_TAC, REAL_RING,
        SET_TAC, VECTOR_ARITH, .. } := D
  let { AND_FORALL_THM, DIMINDEX_GE_1, EQ_TRANS, FINITE_NUMSEG, FUN_EQ_THM, IN_NUMSEG,
        .. } := D.core1
  let { LE_REFL, MONO_EXISTS, REAL_ABS_INV, REAL_DIV_REFL, REAL_EQ_RDIV_EQ, REAL_INV_1,
        REAL_LE_MUL, REAL_LT_IMP_NZ, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LINV,
        REAL_MUL_LZERO, REAL_MUL_RINV, REAL_MUL_SYM, .. } := D.core2
  let { REAL_POW2_ABS, REAL_POW_2, REAL_POW_MUL, REAL_SUB_0, SUM_RMUL, o_DEF, o_THM,
        pairwise, real_abs, .. } := D.core3
  let { I_THM, .. } := D.core4
  let { BASIS_EXPANSION, DOT_LADD, DOT_LMUL, DOT_LSUB, DOT_NORM_SUB, DOT_RADD, DOT_RMUL,
        DOT_RSUB, DOT_SYM, LINEAR_0, LINEAR_ADD, LINEAR_CMUL, LINEAR_COMPOSE_CMUL,
        LINEAR_INJECTIVE_LEFT_INVERSE, LINEAR_INVERSE_LEFT, LINEAR_SUB, LINEAR_VSUM,
        .. } := D.vec1
  let { NORM_0, NORM_BASIS, NORM_EQ, NORM_EQ_0, NORM_EQ_1, NORM_EQ_SQUARE, NORM_MUL,
        NORM_NEG, NORM_POS_LE, NORM_POS_LT, NORM_POW_2, NORM_VSUM_PYTHAGOREAN,
        ORTHOGONAL_BASIS_BASIS, ORTHOGONAL_MUL, REAL_ABS_NORM, .. } := D.vec2
  let { VECTOR_EQ, VECTOR_MUL_ASSOC, VECTOR_MUL_LID, VECTOR_MUL_LZERO, VECTOR_SUB_LZERO,
        VECTOR_SUB_REFL, VECTOR_SUB_RZERO, dist, dot, linear, onorm, orthogonal, .. } := D.vec3
  let { ORTHOGONAL_ORTHOGONAL_TRANSFORMATION, ORTHOGONAL_TRANSFORMATION,
        ORTHOGONAL_TRANSFORMATION_INJECTIVE, ORTHOGONAL_TRANSFORMATION_LINEAR, .. } := BOrth1
  let { ORTHOGONAL_TRANSFORMATION_ID, .. } := BOrth2
  -- @@SCOPE END

  let SCALING_LINEAR ← prove
   r"!f:real^M->real^N c.
        (f(vec 0) = vec 0) /\ (!x y. dist(f x,f y) = c * dist(x,y))
        ==> linear(f)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"!v w. ((f:real^M->real^N) v) dot (f w) = c pow 2 * (v dot w)")
    ASSUME_TAC THENL
     [FIRST_ASSUM (MP_TAC o GEN (← q r"v:real^M") o
        SPECL [← q r"v:real^M", ← q r"vec 0 :real^M"]) THEN
      REWRITE_TAC [dist] THEN ASM_REWRITE_TAC [VECTOR_SUB_RZERO] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC [DOT_NORM_SUB, ← GSYM dist] THEN
      REAL_ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [linear, VECTOR_EQ] THEN
    ASM_REWRITE_TAC [DOT_LADD, DOT_RADD, DOT_LMUL, DOT_RMUL] THEN
    REAL_ARITH_TAC)

  let ISOMETRY_LINEAR ← prove
   r"!f:real^M->real^N.
        (f(vec 0) = vec 0) /\ (!x y. dist(f x,f y) = dist(x,y))
        ==> linear(f)"
   (MESON_TAC [SCALING_LINEAR, REAL_MUL_LID])

  let ISOMETRY_IMP_AFFINITY ← prove
   r"!f:real^M->real^N.
        (!x y. dist(f x,f y) = dist(x,y))
        ==> ?h. linear h /\ !x. f(x) = f(vec 0) + h(x)"
   (REPEAT STRIP_TAC THEN
    EXISTS_TAC (← q r"\x. (f:real^M->real^N) x - f(vec 0)") THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"a + (x - a):real^N = x")] THEN
    MATCH_MP_TAC ISOMETRY_LINEAR THEN REWRITE_TAC [VECTOR_SUB_REFL] THEN
    ASM_REWRITE_TAC [← NORM_ARITH (← q r"dist(x - a:real^N,y - a) = dist(x,y)")])

  let ORTHOGONALITY_PRESERVING_IMP_SCALING ← prove
   r"!f:real^M->real^N.
        linear f /\ (!x y. orthogonal x y ==> orthogonal (f x) (f y))
        ==> ?c. &0 <= c /\ !x. norm(f x) = c * norm(x)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"?c. &0 <= c /\
        !i. 1 <= i /\ i <= dimindex(:M)
            ==> norm((f:real^M->real^N)(basis i)) = c")
    MP_TAC THENL
     [MATCH_MP_TAC (← MESON [] (← q
       r"(!x. A(f x)) /\ (?x. P x) /\ (!i j. P i /\ P j ==> f i = f j)
      ==> ?c. A c /\ !x. P x ==> f x = c")) THEN
      REWRITE_TAC [NORM_POS_LE] THEN CONJ_TAC THENL
       [EXISTS_TAC (← q r"1") THEN REWRITE_TAC [LE_REFL, DIMINDEX_GE_1], ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"j:num"] THEN STRIP_TAC THEN
      ASM_CASES_TAC (← q r"i:num = j") THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o ISPECL
       [← q r"basis i + basis j:real^M", ← q r"basis i - basis j:real^M"]) THEN
      ASM_SIMP_TAC [orthogonal, LINEAR_ADD, LINEAR_SUB, ← VECTOR_ARITH (← q
       r"(x + y:real^M) dot (x - y) = x dot x - y dot y")] THEN

      ASM_SIMP_TAC [← GSYM NORM_POW_2, REAL_SUB_0, NORM_BASIS] THEN
      REWRITE_TAC [NORM_POW_2, ← GSYM NORM_EQ],
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"c:real") THEN STRIP_TAC THEN
      ASM_SIMP_TAC [NORM_EQ_SQUARE, NORM_POS_LE, REAL_LE_MUL]  THEN
      X_GEN_TAC (← q r"x:real^M") THEN REWRITE_TAC [← GSYM NORM_POW_2] THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV)
       [← GSYM BASIS_EXPANSION] THEN
      ASM_SIMP_TAC [LINEAR_VSUM, FINITE_NUMSEG, o_DEF, LINEAR_CMUL] THEN
      W (MP_TAC o PART_MATCH (lhand o rand)
        NORM_VSUM_PYTHAGOREAN o lhand o snd) THEN
      REWRITE_TAC [pairwise, IN_NUMSEG, ORTHOGONAL_MUL, FINITE_NUMSEG] THEN
      ASM_SIMP_TAC [ORTHOGONAL_BASIS_BASIS] THEN DISCH_THEN SUBST1_TAC THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      ASM_SIMP_TAC [NORM_MUL, REAL_POW_MUL, SUM_RMUL, REAL_POW2_ABS] THEN
      REWRITE_TAC [REAL_POW_2, ← GSYM dot, ← GSYM NORM_POW_2]])

  let (ORTHOGONALITY_PRESERVING_EQ_SIMILARITY_ALT,
       ORTHOGONALITY_PRESERVING_EQ_SIMILARITY) ← CONJ_PAIR (← prove
   r"(!f:real^N->real^N.
        linear f /\ (!x y. orthogonal x y ==> orthogonal (f x) (f y)) <=>
        ?c g. &0 <= c /\ orthogonal_transformation g /\ f = \z. c % g z) /\
   (!f:real^N->real^N.
        linear f /\ (!x y. orthogonal x y ==> orthogonal (f x) (f y)) <=>
        ?c g. orthogonal_transformation g /\ f = \z. c % g z)"
   (REWRITE_TAC [AND_FORALL_THM] THEN GEN_TAC THEN
    MATCH_MP_TAC (← TAUT (← q
     r"(q ==> r) /\ (r ==> p) /\ (p ==> q)
    ==> (p <=> q) /\ (p <=> r)")) THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [],
      STRIP_TAC THEN
      ASM_SIMP_TAC [ORTHOGONAL_TRANSFORMATION_LINEAR, LINEAR_COMPOSE_CMUL] THEN
      ASM_SIMP_TAC [ORTHOGONAL_MUL, ORTHOGONAL_ORTHOGONAL_TRANSFORMATION],
      DISCH_TAC THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP ORTHOGONALITY_PRESERVING_IMP_SCALING) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"c:real") THEN
      ASM_CASES_TAC (← q r"c = &0") THENL
       [ASM_SIMP_TAC [REAL_MUL_LZERO, FUN_EQ_THM, NORM_EQ_0] THEN
        DISCH_TAC THEN EXISTS_TAC (← q r"\x:real^N. x") THEN
        REWRITE_TAC [VECTOR_MUL_LZERO, ORTHOGONAL_TRANSFORMATION_ID],
        STRIP_TAC THEN EXISTS_TAC (← q r"\x. inv(c) % (f:real^N->real^N) x") THEN
        ASM_REWRITE_TAC [ORTHOGONAL_TRANSFORMATION, FUN_EQ_THM] THEN
        ASM_SIMP_TAC [LINEAR_COMPOSE_CMUL, NORM_MUL, VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC [REAL_MUL_RINV, VECTOR_MUL_LID, REAL_ABS_INV] THEN
        ASM_REWRITE_TAC [real_abs, REAL_MUL_ASSOC] THEN
        ASM_SIMP_TAC [REAL_MUL_LINV, REAL_MUL_LID]]]))

  let ORTHOGONAL_TRANSFORMATION_ISOMETRY ← prove
   r"!f:real^N->real^N.
        orthogonal_transformation f <=>
        (f(vec 0) = vec 0) /\ (!x y. dist(f x,f y) = dist(x,y))"
   (GEN_TAC THEN REWRITE_TAC [ORTHOGONAL_TRANSFORMATION] THEN EQ_TAC THENL
     [MESON_TAC [LINEAR_0, LINEAR_SUB, dist], STRIP_TAC] THEN
    ASM_SIMP_TAC [ISOMETRY_LINEAR] THEN X_GEN_TAC (← q r"x:real^N") THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"x:real^N", ← q r"vec 0:real^N"]) THEN
    ASM_REWRITE_TAC [dist, VECTOR_SUB_RZERO])

  let ISOMETRY_SPHERE_EXTEND ← do
    let lemma ← prove
     r"!x:real^N y:real^N x':real^N y':real^N x0 y0 x0' y0'.
          x = norm(x) % x0 /\ y = norm(y) % y0 /\
          x' = norm(x) % x0' /\ y' = norm(y) % y0' /\
          norm(x0) = &1 /\ norm(x0') = &1 /\ norm(y0) = &1 /\ norm(y0') = &1 /\
          norm(x0' - y0') = norm(x0 - y0)
          ==> norm(x' - y') = norm(x - y)"
     (REPEAT GEN_TAC THEN
      MAP_EVERY ABBREV_TAC [← q r"a = norm(x:real^N)", ← q r"b = norm(y:real^N)"] THEN
      REPLICATE_TAC 4 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [NORM_EQ, NORM_EQ_1] THEN
      REWRITE_TAC [DOT_LSUB, DOT_RSUB, DOT_LMUL, DOT_RMUL] THEN
      REWRITE_TAC [DOT_SYM] THEN CONV_TAC (fun t => REAL_RING t))
    prove
     r"!f:real^N->real^N.
        (!x. norm(x) = &1 ==> norm(f x) = &1) /\
        (!x y. norm(x) = &1 /\ norm(y) = &1 ==> dist(f x,f y) = dist(x,y))
        ==> ?g. orthogonal_transformation g /\
                (!x. norm(x) = &1 ==> g(x) = f(x))"
     (REPEAT STRIP_TAC THEN
      EXISTS_TAC (← q r"\x. if x = vec 0 then vec 0
                  else norm(x) % (f:real^N->real^N)(inv(norm x) % x)") THEN
      REWRITE_TAC [ORTHOGONAL_TRANSFORMATION_ISOMETRY] THEN
      SIMP_TAC [VECTOR_MUL_LID, REAL_INV_1] THEN CONJ_TAC THENL
       [ALL_TAC, MESON_TAC [NORM_0, ← REAL_ARITH (← q r"~(&1 = &0)")]] THEN
      REPEAT GEN_TAC THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
      REWRITE_TAC [dist, VECTOR_SUB_LZERO, VECTOR_SUB_RZERO, NORM_NEG, NORM_MUL,
                   REAL_ABS_NORM] THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      ASM_SIMP_TAC [← GSYM REAL_EQ_RDIV_EQ, NORM_POS_LT] THEN
      ASM_SIMP_TAC [REAL_DIV_REFL, REAL_LT_IMP_NZ, NORM_EQ_0] THEN
      TRY (FIRST_X_ASSUM MATCH_MP_TAC) THEN
      REWRITE_TAC [NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
      ASM_SIMP_TAC [REAL_MUL_LINV, NORM_EQ_0] THEN
      MATCH_MP_TAC lemma THEN MAP_EVERY EXISTS_TAC
       [← q r"inv(norm x) % x:real^N", ← q r"inv(norm y) % y:real^N",
        ← q r"(f:real^N->real^N) (inv (norm x) % x)",
        ← q r"(f:real^N->real^N) (inv (norm y) % y)"] THEN
      REWRITE_TAC [NORM_MUL, VECTOR_MUL_ASSOC, REAL_ABS_INV, REAL_ABS_NORM] THEN
      ASM_SIMP_TAC [REAL_MUL_LINV, REAL_MUL_RINV, NORM_EQ_0] THEN
      ASM_REWRITE_TAC [← GSYM dist, VECTOR_MUL_LID] THEN
      REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC [NORM_MUL, VECTOR_MUL_ASSOC, REAL_ABS_INV, REAL_ABS_NORM] THEN
      ASM_SIMP_TAC [REAL_MUL_LINV, REAL_MUL_RINV, NORM_EQ_0])

  let ORTHOGONAL_TRANSFORMATION_INVERSE_o ← prove
   r"!f:real^N->real^N.
        orthogonal_transformation f
        ==> ?g. orthogonal_transformation g /\ g o f = I /\ f o g = I"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_INJECTIVE) THEN
    MP_TAC (← ISPEC (← q r"f:real^N->real^N") LINEAR_INJECTIVE_LEFT_INVERSE) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"g:real^N->real^N") THEN  STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^N->real^N", ← q r"g:real^N->real^N"]
      LINEAR_INVERSE_LEFT) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_REWRITE_TAC [ORTHOGONAL_TRANSFORMATION] THEN X_GEN_TAC (← q r"v:real^N") THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"norm((f:real^N->real^N)((g:real^N->real^N) v))") THEN
    CONJ_TAC THENL [ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION], ALL_TAC] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [FUN_EQ_THM, o_THM, I_THM]) THEN
    ASM_REWRITE_TAC [])

  let ORTHOGONAL_TRANSFORMATION_INVERSE ← prove
   r"!f:real^N->real^N.
        orthogonal_transformation f
        ==> ?g. orthogonal_transformation g /\
                (!x. g(f x) = x) /\ (!y. f(g y) = y)"
   (GEN_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_INVERSE_o) THEN
    REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM])

  let ONORM_COMPOSE_ORTHOGONAL_TRANSFORMATION_LEFT ← prove
   r"!f g. orthogonal_transformation f ==> onorm(f o g) = onorm g"
   (SIMP_TAC [ORTHOGONAL_TRANSFORMATION, onorm, o_DEF])

  let ONORM_COMPOSE_ORTHOGONAL_TRANSFORMATION_RIGHT ← prove
   r"!f g. orthogonal_transformation g ==> onorm(f o g) = onorm f"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [onorm, o_DEF] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_INVERSE_o) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN
    REWRITE_TAC [ORTHOGONAL_TRANSFORMATION] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ASM SET_TAC [])

  return { SCALING_LINEAR, ISOMETRY_LINEAR, ISOMETRY_IMP_AFFINITY,
           ORTHOGONALITY_PRESERVING_IMP_SCALING, ORTHOGONALITY_PRESERVING_EQ_SIMILARITY_ALT,
           ORTHOGONALITY_PRESERVING_EQ_SIMILARITY, ORTHOGONAL_TRANSFORMATION_ISOMETRY,
           ISOMETRY_SPHERE_EXTEND, ORTHOGONAL_TRANSFORMATION_INVERSE_o,
           ORTHOGONAL_TRANSFORMATION_INVERSE, ONORM_COMPOSE_ORTHOGONAL_TRANSFORMATION_LEFT,
           ONORM_COMPOSE_ORTHOGONAL_TRANSFORMATION_RIGHT }

/- ------------------------------------------------------------------------- -/
/- Reading operator norms off eigenvalue bases or diagonalizations; an       -/
/- orthogonal matrix taking any unit vector to any other.                    -/
/- (determinants.ml 3300-3502)                                                -/
/- ------------------------------------------------------------------------- -/

structure OpNorm where
  SQNORM_LE_MAX_EIGENVECTOR_SPAN : thm
  NORM_LE_MAX_EIGENVECTOR_SPAN : thm
  ONORM_EQ_MAX_EIGENVECTOR : thm
  ONORM_ORTHOGONAL_MATRIX_MUL_LEFT : thm
  ONORM_ORTHOGONAL_MATRIX_MUL_RIGHT : thm
  ONORM_DIAGONALIZED_MATRIX : thm
  ONORM_DIAGONALIZED_COVARIANCE_MATRIX : thm
  ORTHOGONAL_MATRIX_EXISTS_BASIS : thm
  ORTHOGONAL_TRANSFORMATION_EXISTS_1 : thm
  ORTHOGONAL_TRANSFORMATION_EXISTS : thm
  deriving Inhabited

@[nospecialize]
def setupOpNorm [HolBase] (D : DeterminantsDeps) (BDiagonal : Diagonal) (BOrth1 : Orth1)
    (BOrth2 : Orth2) (BIso : Iso) : ExceptT String IO OpNorm := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC, SET_RULE, SET_TAC, VECTOR_ARITH,
        .. } := D
  let { ARITH_EQ, CART_EQ, COND_RAND, DIMINDEX_GE_1, EQ_TRANS, EXISTS_IN_IMAGE,
        FINITE_IMAGE, FORALL_IN_IMAGE, HAS_SIZE, IMAGE_EQ_EMPTY, IN_ELIM_THM, IN_IMAGE,
        IN_NUMSEG, IN_SING, IN_UNIV, LAMBDA_BETA, LEFT_IMP_EXISTS_THM, .. } := D.core1
  let { LE_REFL, MEMBER_NOT_EMPTY, MONO_EXISTS, REAL_ABS_ABS, REAL_ABS_INV, REAL_ABS_POS,
        REAL_INV_EQ_0, REAL_LE_ANTISYM, REAL_LE_MUL, REAL_LE_POW_2, REAL_LE_RCANCEL_IMP,
        REAL_LE_REFL, REAL_LE_RMUL, REAL_LE_SQUARE_ABS, REAL_LE_SUP_FINITE, REAL_LE_TRANS,
        REAL_MUL_LINV, REAL_MUL_RID, REAL_MUL_RZERO, REAL_MUL_SYM, .. } := D.core2
  let { REAL_POW2_ABS, REAL_POW_MUL, REAL_SUP_LE, SIMPLE_IMAGE, SQRT_UNIQUE, SUM_DELTA,
        SUM_LE, SUM_LMUL, o_DEF, pairwise, .. } := D.core3
  let { EQ_IMP, .. } := D.core4
  let { BASIS_COMPONENT, LINEAR_0, LINEAR_CMUL, LINEAR_VSUM, .. } := D.vec1
  let { MATRIX_OF_MATRIX_VECTOR_MUL, MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID,
        MATRIX_VECTOR_MUL_LINEAR, NORM_0, NORM_EQ_0, NORM_LE_SQUARE, NORM_MUL, NORM_POS_LE,
        NORM_POS_LT, NORM_POW_2, NORM_VSUM_PYTHAGOREAN, ONORM, ONORM_COVARIANCE, ONORM_LE_EQ,
        ONORM_POS_LE, ORTHOGONAL_MUL, PAIRWISE_ORTHOGONAL_IMP_FINITE, REAL_ABS_NORM,
        SPAN_EMPTY, .. } := D.vec2
  let { SPAN_FINITE, VECTOR_IN_ORTHONORMAL_BASIS, VECTOR_MUL_ASSOC, VECTOR_MUL_EQ_0,
        VECTOR_SUB_EQ, VEC_EQ, column, matrix_vector_mul, FINITE_INDEX_NUMSEG_SPECIAL,
        .. } := D.vec3
  let { ONORM_DIAGONAL_MATRIX, .. } := BDiagonal
  let { ORTHOGONAL_MATRIX, ORTHOGONAL_MATRIX_MUL, ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS,
        ORTHOGONAL_MATRIX_TRANSFORMATION, ORTHOGONAL_MATRIX_TRANSP,
        ORTHOGONAL_TRANSFORMATION_LINEAR, ORTHOGONAL_TRANSFORMATION_MATRIX, .. } := BOrth1
  let { ORTHOGONAL_TRANSFORMATION_ID, .. } := BOrth2
  let { ONORM_COMPOSE_ORTHOGONAL_TRANSFORMATION_LEFT,
        ONORM_COMPOSE_ORTHOGONAL_TRANSFORMATION_RIGHT, .. } := BIso
  -- @@SCOPE END

  let SQNORM_LE_MAX_EIGENVECTOR_SPAN ← prove
   r"!(f:real^N->real^N) b c x l.
        linear f /\
        pairwise orthogonal b /\
        (!x. x IN b ==> f x = c x % x /\ c x pow 2 <= l) /\
        x IN span b
        ==> norm(f x) pow 2 <= l * norm x pow 2"
   (REPEAT GEN_TAC THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP PAIRWISE_ORTHOGONAL_IMP_FINITE) THEN
    ASM_SIMP_TAC [SPAN_FINITE, IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"v:real^N->real") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC [LINEAR_VSUM, o_DEF, LINEAR_CMUL] THEN
    W (MP_TAC o PART_MATCH (lhand o rand) NORM_VSUM_PYTHAGOREAN o
      lhand o snd) THEN
    W (MP_TAC o PART_MATCH (lhand o rand) NORM_VSUM_PYTHAGOREAN o
      rand o rand o rand o snd) THEN
    ASM_REWRITE_TAC [] THEN
    REPEAT (ANTS_TAC THENL
     [RULE_ASSUM_TAC (REWRITE_RULE [pairwise]) THEN
      REWRITE_TAC [pairwise, ORTHOGONAL_MUL] THEN ASM_MESON_TAC [],
      DISCH_THEN SUBST1_TAC]) THEN
    REWRITE_TAC [← GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [REAL_MUL_SYM] VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC [← GSYM VECTOR_MUL_ASSOC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [NORM_MUL] THEN
    REWRITE_TAC [REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC [REAL_POW2_ABS, REAL_LE_POW_2])

  let NORM_LE_MAX_EIGENVECTOR_SPAN ← prove
   r"!(f:real^N->real^N) b c x l.
        linear f /\
        pairwise orthogonal b /\
        (!x. x IN b ==> f x = c x % x /\ abs(c x) <= l) /\
        x IN span b
        ==> norm(f x) <= l * norm x"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"b:real^N->bool = {}") THENL
     [ASM_REWRITE_TAC [SPAN_EMPTY, IN_SING] THEN
      MESON_TAC [LINEAR_0, NORM_0, REAL_MUL_RZERO, REAL_LE_REFL],
      STRIP_TAC] THEN
    GEN_REWRITE_TAC id [NORM_LE_SQUARE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC [NORM_POS_LE] THEN
      ASM_MESON_TAC [REAL_ABS_POS, REAL_LE_TRANS, MEMBER_NOT_EMPTY],
      REWRITE_TAC [REAL_POW_MUL, ← GSYM NORM_POW_2]] THEN
    MATCH_MP_TAC SQNORM_LE_MAX_EIGENVECTOR_SPAN THEN
    MAP_EVERY EXISTS_TAC [← q r"b:real^N->bool", ← q r"c:real^N->real"] THEN
    ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"y:real^N") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"y:real^N")) THEN ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [← GSYM REAL_LE_SQUARE_ABS, REAL_ABS_ABS] THEN ASM_REAL_ARITH_TAC)

  let ONORM_EQ_MAX_EIGENVECTOR ← prove
   r"!(f:real^N->real^N) b c.
        linear f /\
        pairwise orthogonal b /\
        span b = (:real^N) /\
        ~(vec 0 IN b) /\
        (!x. x IN b ==> f x = c x % x)
        ==> onorm f = sup {abs(c x) | x IN b}"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"b:real^N->bool = {}") THENL
     [ASM_REWRITE_TAC [SPAN_EMPTY] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE (← q
       r"s = UNIV ==> (?x. ~(x IN s)) ==> P"))) THEN
      EXISTS_TAC (← q r"vec 1:real^N") THEN REWRITE_TAC [VEC_EQ, IN_SING, ARITH_EQ],
      STRIP_TAC THEN REWRITE_TAC [← GSYM REAL_LE_ANTISYM]] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC [ONORM_LE_EQ] THEN GEN_TAC THEN
      MATCH_MP_TAC NORM_LE_MAX_EIGENVECTOR_SPAN THEN
      MAP_EVERY EXISTS_TAC [← q r"b:real^N->bool", ← q r"c:real^N->real"] THEN
      ASM_REWRITE_TAC [IN_UNIV] THEN X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      ASM_SIMP_TAC [REAL_LE_SUP_FINITE, SIMPLE_IMAGE, FINITE_IMAGE,
                    IMAGE_EQ_EMPTY, PAIRWISE_ORTHOGONAL_IMP_FINITE] THEN
      REWRITE_TAC [EXISTS_IN_IMAGE] THEN EXISTS_TAC (← q r"x:real^N") THEN
      ASM_REWRITE_TAC [REAL_LE_REFL],
      MATCH_MP_TAC REAL_SUP_LE THEN
      ASM_SIMP_TAC [SIMPLE_IMAGE, IMAGE_EQ_EMPTY, FORALL_IN_IMAGE] THEN
      X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC (← q r"norm(x:real^N)") THEN
      REWRITE_TAC [NORM_POS_LT] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      TRANS_TAC REAL_LE_TRANS (← q r"norm((f:real^N->real^N) x)") THEN
      ASM_SIMP_TAC [ONORM, NORM_MUL, REAL_LE_REFL]])

  let ONORM_ORTHOGONAL_MATRIX_MUL_LEFT ← prove
   r"!(A:real^N^N) (P:real^N^N).
        orthogonal_matrix P ==> onorm (\x. (P ** A) ** x) = onorm(\x. A ** x)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"(\x. ((P:real^N^N) ** (A:real^N^N)) ** x) = (\x. P ** x) o (\x. A ** x)")
    SUBST1_TAC THENL [REWRITE_TAC [o_DEF, MATRIX_VECTOR_MUL_ASSOC], ALL_TAC] THEN
    MATCH_MP_TAC ONORM_COMPOSE_ORTHOGONAL_TRANSFORMATION_LEFT THEN
    ASM_REWRITE_TAC [← GSYM ORTHOGONAL_MATRIX_TRANSFORMATION])

  let ONORM_ORTHOGONAL_MATRIX_MUL_RIGHT ← prove
   r"!(A:real^N^N) (P:real^N^N).
        orthogonal_matrix P ==> onorm (\x. (A ** P) ** x) = onorm(\x. A ** x)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"(\x. ((A:real^N^N) ** (P:real^N^N)) ** x) =
    (\x. A ** x) o (\x. P ** x)")
    SUBST1_TAC THENL [REWRITE_TAC [o_DEF, MATRIX_VECTOR_MUL_ASSOC], ALL_TAC] THEN
    MATCH_MP_TAC ONORM_COMPOSE_ORTHOGONAL_TRANSFORMATION_RIGHT THEN
    ASM_REWRITE_TAC [← GSYM ORTHOGONAL_MATRIX_TRANSFORMATION])

  let ONORM_DIAGONALIZED_MATRIX ← prove
   r"!(A:real^N^N) D P.
      orthogonal_matrix P /\
      diagonal_matrix D /\
      transp P ** D ** P = A
      ==> onorm(\x. A ** x) = sup {abs(D$i$i) | 1 <= i /\ i <= dimindex (:N)}"
   (REPEAT STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC [ONORM_ORTHOGONAL_MATRIX_MUL_LEFT, ORTHOGONAL_MATRIX_TRANSP,
                  ONORM_ORTHOGONAL_MATRIX_MUL_RIGHT] THEN
    ASM_SIMP_TAC [ONORM_DIAGONAL_MATRIX])

  let ONORM_DIAGONALIZED_COVARIANCE_MATRIX ← prove
   r"!(A:real^N^N) D P.
      orthogonal_matrix P /\
      diagonal_matrix D /\
      transp P ** D ** P = transp A ** A
      ==> onorm(\x. A ** x) =
          sqrt(sup {abs(D$i$i) | 1 <= i /\ i <= dimindex (:N)})"
   (REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SQRT_UNIQUE THEN
    SIMP_TAC [ONORM_POS_LE, MATRIX_VECTOR_MUL_LINEAR] THEN
    REWRITE_TAC [← GSYM ONORM_COVARIANCE] THEN
    MATCH_MP_TAC ONORM_DIAGONALIZED_MATRIX THEN ASM_MESON_TAC [])

  let ORTHOGONAL_MATRIX_EXISTS_BASIS ← prove
   r"!a:real^N.
        norm(a) = &1
        ==> ?A. orthogonal_matrix A /\ A**(basis 1) = a"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP VECTOR_IN_ORTHONORMAL_BASIS) THEN
    REWRITE_TAC [HAS_SIZE] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"s:real^N->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"a:real^N"]
     FINITE_INDEX_NUMSEG_SPECIAL) THEN ASM_REWRITE_TAC [IN_NUMSEG] THEN
    REWRITE_TAC [← TAUT (← q r"a /\ b ==> c <=> c \/ ~a \/ ~b")] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"f:num->real^N")
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
       ASSUME_TAC))) THEN
    EXISTS_TAC (← q r"(lambda i j. ((f j):real^N)$i):real^N^N") THEN
    SIMP_TAC [CART_EQ, LAMBDA_BETA, matrix_vector_mul, BASIS_COMPONENT,
              IN_NUMSEG] THEN
    ONCE_REWRITE_TAC [COND_RAND] THEN SIMP_TAC [REAL_MUL_RZERO, SUM_DELTA] THEN
    ASM_REWRITE_TAC [IN_NUMSEG, REAL_MUL_RID, LE_REFL, DIMINDEX_GE_1] THEN
    REWRITE_TAC [ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS] THEN
    SIMP_TAC [column, LAMBDA_BETA] THEN CONJ_TAC THENL
     [X_GEN_TAC (← q r"i:num") THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC (← q r"norm((f:num->real^N) i)") THEN CONJ_TAC THENL
       [AP_TERM_TAC THEN ASM_SIMP_TAC [CART_EQ, LAMBDA_BETA],
        ASM_MESON_TAC [IN_IMAGE, IN_NUMSEG]],
      MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"j:num"] THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"orthogonal ((f:num->real^N) i) (f j)") MP_TAC THENL
       [ASM_MESON_TAC [pairwise, IN_IMAGE, IN_NUMSEG], ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
      ASM_SIMP_TAC [CART_EQ, LAMBDA_BETA]])

  let ORTHOGONAL_TRANSFORMATION_EXISTS_1 ← prove
   r"!a b:real^N.
        norm(a) = &1 /\ norm(b) = &1
        ==> ?f. orthogonal_transformation f /\ f a = b"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"b:real^N") ORTHOGONAL_MATRIX_EXISTS_BASIS) THEN
    MP_TAC (← ISPEC (← q r"a:real^N") ORTHOGONAL_MATRIX_EXISTS_BASIS) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"A:real^N^N") (STRIP_ASSUME_TAC o GSYM)) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"B:real^N^N") (STRIP_ASSUME_TAC o GSYM)) THEN
    EXISTS_TAC (← q r"\x:real^N. ((B:real^N^N) ** transp(A:real^N^N)) ** x") THEN
    REWRITE_TAC [ORTHOGONAL_TRANSFORMATION_MATRIX, MATRIX_VECTOR_MUL_LINEAR,
                 MATRIX_OF_MATRIX_VECTOR_MUL] THEN
    ASM_SIMP_TAC [ORTHOGONAL_MATRIX_MUL, ORTHOGONAL_MATRIX_TRANSP] THEN
    REWRITE_TAC [← GSYM MATRIX_VECTOR_MUL_ASSOC] THEN AP_TERM_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ORTHOGONAL_MATRIX]) THEN
    ASM_REWRITE_TAC [MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID])

  let ORTHOGONAL_TRANSFORMATION_EXISTS ← prove
   r"!a b:real^N.
        norm(a) = norm(b) ==> ?f. orthogonal_transformation f /\ f a = b"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"b:real^N = vec 0") THEN
    ASM_SIMP_TAC [NORM_0, NORM_EQ_0] THENL
     [MESON_TAC [ORTHOGONAL_TRANSFORMATION_ID], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"a:real^N = vec 0") THENL
     [ASM_MESON_TAC [NORM_0, NORM_EQ_0], ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"inv(norm a) % a:real^N", ← q r"inv(norm b) % b:real^N"]
                  ORTHOGONAL_TRANSFORMATION_EXISTS_1) THEN
    REWRITE_TAC [NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
    ASM_SIMP_TAC [NORM_EQ_0, REAL_MUL_LINV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f:real^N->real^N") THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP LINEAR_CMUL o
                MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
    ASM_REWRITE_TAC [← VECTOR_ARITH (← q
      r"a % x:real^N = a % y <=> a % (x - y) = vec 0")] THEN
    ASM_REWRITE_TAC [VECTOR_MUL_EQ_0, REAL_INV_EQ_0, NORM_EQ_0, VECTOR_SUB_EQ])

  return { SQNORM_LE_MAX_EIGENVECTOR_SPAN, NORM_LE_MAX_EIGENVECTOR_SPAN,
           ONORM_EQ_MAX_EIGENVECTOR, ONORM_ORTHOGONAL_MATRIX_MUL_LEFT,
           ONORM_ORTHOGONAL_MATRIX_MUL_RIGHT, ONORM_DIAGONALIZED_MATRIX,
           ONORM_DIAGONALIZED_COVARIANCE_MATRIX, ORTHOGONAL_MATRIX_EXISTS_BASIS,
           ORTHOGONAL_TRANSFORMATION_EXISTS_1, ORTHOGONAL_TRANSFORMATION_EXISTS }

/- ------------------------------------------------------------------------- -/
/- Orthogonal maps taking a subspace to another of suitable dimension;       -/
/- rotation, reflection, rotoinversion.  (determinants.ml 3508-3659)         -/
/- ------------------------------------------------------------------------- -/

structure Rotation1 where
  ORTHOGONAL_TRANSFORMATION_INTO_SUBSPACE : thm
  ORTHOGONAL_TRANSFORMATION_ONTO_SUBSPACE : thm
  rotation_matrix : thm
  rotoinversion_matrix : thm
  ORTHOGONAL_ROTATION_OR_ROTOINVERSION : thm
  ROTATION_MATRIX_1 : thm
  ROTOINVERSION_MATRIX_1 : thm
  ROTATION_MATRIX_2 : thm
  deriving Inhabited

@[nospecialize]
def setupRotation1 [HolBase] (D : DeterminantsDeps) (BDetBasic : DetBasic)
    (BLowDim : LowDim) (BOrth1 : Orth1) (BOrth2 : Orth2) : ExceptT String IO Rotation1 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON, MESON_TAC, NORM_ARITH, REAL_RAT_REDUCE_CONV,
        REAL_RING, SET_TAC, new_definition, .. } := D
  let { CARD_DIFF, CARD_IMAGE_INJ, CARD_LE_INJ, CARD_UNION, FINITE_DIFF, FINITE_UNION,
        FORALL_IN_IMAGE, HAS_SIZE, INJECTIVE_ON_ALT, IN_ELIM_THM, IN_UNION, IN_UNIV,
        LEFT_IMP_EXISTS_THM, .. } := D.core1
  let { LE_ANTISYM, LE_REFL, MONO_EXISTS, .. } := D.core2
  let { REAL_POW_ONE, SUBSET, SUBSET_UNIV, SUM_EQ, UNION_COMM, UNION_UNIV, o_DEF, pairwise,
        .. } := D.core3
  let { DIM_EQ_SPAN, DIM_INJECTIVE_LINEAR_IMAGE, INDEPENDENT_SPAN_BOUND, LINEAR_CMUL,
        LINEAR_INDEPENDENT_EXTEND, LINEAR_VSUM, .. } := D.vec1
  let { NORM_EQ_SQUARE, NORM_MUL, NORM_POS_LE, NORM_POW_2, NORM_VSUM_PYTHAGOREAN,
        ORTHOGONAL_CLAUSES, ORTHOGONAL_MUL, ORTHONORMAL_BASIS_SUBSPACE, ORTHONORMAL_EXTENSION,
        PAIRWISE_ORTHOGONAL_IMP_FINITE, PAIRWISE_ORTHOGONAL_INDEPENDENT, .. } := D.vec2
  let { SPAN_FINITE, SPAN_LINEAR_IMAGE, SPAN_MONO, SPAN_OF_SUBSPACE, SPAN_UNIV, .. } := D.vec3
  let { DET_I, DET_NEG, .. } := BDetBasic
  let { DET_2, .. } := BLowDim
  let { DET_ORTHOGONAL_MATRIX, ORTHOGONAL_TRANSFORMATION, ORTHOGONAL_TRANSFORMATION_INJECTIVE,
        ORTHOGONAL_TRANSFORMATION_LINEAR, orthogonal_transformation, .. } := BOrth1
  let { ORTHOGONAL_MATRIX_1, ORTHOGONAL_MATRIX_2, .. } := BOrth2
  -- @@SCOPE END

  let ORTHOGONAL_TRANSFORMATION_INTO_SUBSPACE ← prove
   r"!s t:real^N->bool.
        subspace s /\ subspace t /\ dim s <= dim t
        ==> ?f. orthogonal_transformation f /\ IMAGE f s SUBSET t"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"t:real^N->bool") ORTHONORMAL_BASIS_SUBSPACE) THEN
    MP_TAC (← ISPEC (← q r"s:real^N->bool") ORTHONORMAL_BASIS_SUBSPACE) THEN
    ASM_REWRITE_TAC [HAS_SIZE] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:real^N->bool") STRIP_ASSUME_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"c:real^N->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"c:real^N->bool", ← q r"(:real^N)"] ORTHONORMAL_EXTENSION) THEN
    MP_TAC (← ISPECL [← q r"b:real^N->bool", ← q r"(:real^N)"] ORTHONORMAL_EXTENSION) THEN
    ASM_REWRITE_TAC [UNION_UNIV, SPAN_UNIV, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"b':real^N->bool") THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"c':real^N->bool") THEN STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"independent(b UNION b':real^N->bool) /\
    independent(c UNION c':real^N->bool)")
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN
      ASM_REWRITE_TAC [IN_UNION] THEN
      ASM_MESON_TAC [← NORM_ARITH (← q r"~(norm(vec 0:real^N) = &1)")],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"FINITE(b UNION b':real^N->bool) /\
                FINITE(c UNION c':real^N->bool)")
    MP_TAC THENL
     [ASM_SIMP_TAC [PAIRWISE_ORTHOGONAL_IMP_FINITE],
      REWRITE_TAC [FINITE_UNION] THEN STRIP_TAC] THEN
    SUBGOAL_THEN
     (← q r"?f:real^N->real^N.
        (!x y. x IN b UNION b' /\ y IN b UNION b' ==> (f x = f y <=> x = y)) /\
        IMAGE f b SUBSET c /\
        IMAGE f (b UNION b') SUBSET c UNION c'")
     (X_CHOOSE_THEN (← q r"fb:real^N->real^N") STRIP_ASSUME_TAC)
    THENL
     [MP_TAC (← ISPECL [← q r"b:real^N->bool", ← q r"c:real^N->bool"]
          CARD_LE_INJ) THEN
      ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM, INJECTIVE_ON_ALT] THEN
      X_GEN_TAC (← q r"f:real^N->real^N") THEN STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"b':real^N->bool",
                     ← q r"(c UNION c') DIFF IMAGE (f:real^N->real^N) b"]
          CARD_LE_INJ) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC [FINITE_UNION, FINITE_DIFF] THEN
        W (MP_TAC o PART_MATCH (lhs o rand) CARD_DIFF o rand o snd) THEN
        ASM_REWRITE_TAC [FINITE_UNION] THEN
        ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN SUBST1_TAC] THEN
        MATCH_MP_TAC (← ARITH_RULE (← q r"a + b:num = c ==> a <= c - b")) THEN
        W (MP_TAC o PART_MATCH (lhs o rand) CARD_IMAGE_INJ o
          rand o lhs o snd) THEN
        ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN
        W (MP_TAC o PART_MATCH (rhs o rand) CARD_UNION o lhs o snd) THEN
        ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [UNION_COMM] THEN
        MATCH_MP_TAC (← MESON [LE_ANTISYM] (← q
         r"(FINITE s /\ CARD s <= CARD t) /\
        (FINITE t /\ CARD t <= CARD s) ==> CARD s = CARD t")) THEN
        CONJ_TAC THEN MATCH_MP_TAC INDEPENDENT_SPAN_BOUND THEN
        ASM_REWRITE_TAC [FINITE_UNION, SUBSET_UNIV],
        DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->real^N") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"\x. if x IN b then (f:real^N->real^N) x else g x") THEN
        REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN ASM SET_TAC []],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"fb:real^N->real^N", ← q r"b UNION b':real^N->bool"]
      LINEAR_INDEPENDENT_EXTEND) THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f:real^N->real^N") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC [ORTHOGONAL_TRANSFORMATION],
      REWRITE_TAC [← SYM (← ASSUME (← q r"span b:real^N->bool = s"))] THEN
      ASM_SIMP_TAC [← GSYM SPAN_LINEAR_IMAGE] THEN
      REWRITE_TAC [← SYM (← ASSUME (← q r"span c:real^N->bool = t"))] THEN
      MATCH_MP_TAC SPAN_MONO THEN ASM SET_TAC []] THEN
    SUBGOAL_THEN
     (← q r"!v. v IN UNIV ==> norm((f:real^N->real^N) v) = norm v")
     (fun th => ASM_MESON_TAC [th, IN_UNIV]) THEN
    UNDISCH_THEN (← q r"span (b UNION b') = (:real^N)") (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC [SPAN_FINITE, FINITE_UNION, IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"z:real^N", ← q r"u:real^N->real"] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [LINEAR_VSUM, FINITE_UNION] THEN
    REWRITE_TAC [o_DEF, NORM_EQ_SQUARE, NORM_POS_LE, ← GSYM NORM_POW_2] THEN
    ASM_SIMP_TAC [LINEAR_CMUL] THEN
    W (MP_TAC o PART_MATCH (lhand o rand)
      NORM_VSUM_PYTHAGOREAN o rand o snd) THEN
    W (MP_TAC o PART_MATCH (lhand o rand)
      NORM_VSUM_PYTHAGOREAN o lhand o rand o snd) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [pairwise]) THEN
    ASM_SIMP_TAC [pairwise, ORTHOGONAL_CLAUSES, FINITE_UNION] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC [ORTHOGONAL_MUL] THEN
      REPEAT DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC [],
      REPEAT (DISCH_THEN SUBST1_TAC) THEN ASM_SIMP_TAC [NORM_MUL] THEN
      MATCH_MP_TAC SUM_EQ THEN ASM SET_TAC []])

  let ORTHOGONAL_TRANSFORMATION_ONTO_SUBSPACE ← prove
   r"!s t:real^N->bool.
        subspace s /\ subspace t /\ dim s = dim t
        ==> ?f. orthogonal_transformation f /\ IMAGE f s = t"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"t:real^N->bool"]
          ORTHOGONAL_TRANSFORMATION_INTO_SUBSPACE) THEN
    ASM_REWRITE_TAC [LE_REFL] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"f:real^N->real^N") THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"span(IMAGE (f:real^N->real^N) s) = span t") MP_TAC THENL
     [MATCH_MP_TAC DIM_EQ_SPAN THEN ASM_REWRITE_TAC [] THEN
      W (MP_TAC o PART_MATCH (lhs o rand) DIM_INJECTIVE_LINEAR_IMAGE o
        rand o snd) THEN
      ASM_MESON_TAC [LE_REFL, orthogonal_transformation,
                     ORTHOGONAL_TRANSFORMATION_INJECTIVE],
      ASM_SIMP_TAC [SPAN_LINEAR_IMAGE, ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
      ASM_SIMP_TAC [SPAN_OF_SUBSPACE]])

  let rotation_matrix ← new_definition
   r"rotation_matrix Q <=> orthogonal_matrix Q /\ det(Q) = &1"

  let rotoinversion_matrix ← new_definition
   r"rotoinversion_matrix Q <=> orthogonal_matrix Q /\ det(Q) = -- &1"

  let ORTHOGONAL_ROTATION_OR_ROTOINVERSION ← prove
   r"!Q. orthogonal_matrix Q <=> rotation_matrix Q \/ rotoinversion_matrix Q"
   (MESON_TAC [rotation_matrix, rotoinversion_matrix, DET_ORTHOGONAL_MATRIX])

  let ROTATION_MATRIX_1 ← prove
   r"!m:real^N^N.
        dimindex(:N) = 1 ==> (rotation_matrix m <=> m = mat 1)"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [ORTHOGONAL_MATRIX_1, rotation_matrix] THEN
    ASM_CASES_TAC (← q r"m:real^N^N = mat 1") THEN ASM_REWRITE_TAC [DET_I] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC [DET_NEG, REAL_POW_ONE, DET_I] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV)

  let ROTOINVERSION_MATRIX_1 ← prove
   r"!m:real^N^N.
        dimindex(:N) = 1 ==> (rotoinversion_matrix m <=> m = --mat 1)"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [ORTHOGONAL_MATRIX_1, rotoinversion_matrix] THEN
    ASM_CASES_TAC (← q r"m:real^N^N = --mat 1") THEN
    ASM_REWRITE_TAC [DET_NEG, DET_I, REAL_POW_ONE] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC [DET_I] THEN CONV_TAC REAL_RAT_REDUCE_CONV)

  let ROTATION_MATRIX_2 ← prove
   r"!A:real^2^2. rotation_matrix A <=>
                A$1$1 pow 2 + A$2$1 pow 2 = &1 /\
                A$1$1 = A$2$2 /\ A$1$2 = --(A$2$1)"
   (REWRITE_TAC [rotation_matrix, ORTHOGONAL_MATRIX_2, DET_2] THEN
    CONV_TAC (fun t => REAL_RING t))

  return { ORTHOGONAL_TRANSFORMATION_INTO_SUBSPACE, ORTHOGONAL_TRANSFORMATION_ONTO_SUBSPACE,
           rotation_matrix, rotoinversion_matrix, ORTHOGONAL_ROTATION_OR_ROTOINVERSION,
           ROTATION_MATRIX_1, ROTOINVERSION_MATRIX_1, ROTATION_MATRIX_2 }

/- ------------------------------------------------------------------------- -/
/- Slightly stronger results giving rotation, but only in >= 2 dimensions;   -/
/- in 3 dimensions, a rotation is about an axis.  (determinants.ml 3664-3795)-/
/- ------------------------------------------------------------------------- -/

structure Rotation2 where
  ROTATION_MATRIX_EXISTS_BASIS : thm
  ROTATION_EXISTS_1 : thm
  ROTATION_EXISTS : thm
  ROTATION_RIGHTWARD_LINE : thm
  EULER_ROTATION_THEOREM : thm
  EULER_ROTOINVERSION_THEOREM : thm
  deriving Inhabited

@[nospecialize]
def setupRotation2 [HolBase] (D : DeterminantsDeps) (BDetBasic : DetBasic)
    (BMultilinear : Multilinear) (BInvertibility : Invertibility) (BLowDim : LowDim)
    (BOrth1 : Orth1) (BOrth2 : Orth2) (BOpNorm : OpNorm) (BRotation1 : Rotation1) :
    ExceptT String IO Rotation2 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON_TAC, REAL_ARITH, REAL_RING, VECTOR_ARITH, .. } := D
  let { ARITH, CART_EQ, DIMINDEX_3, DIMINDEX_GE_1, LAMBDA_BETA, LAMBDA_ETA, .. } := D.core1
  let { LE_REFL, LTE_ANTISYM, LT_IMP_LE, MONO_EXISTS, REAL_ABS_INV, REAL_INV_EQ_0,
        REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_RID, .. } := D.core2
  let { BASIS_COMPONENT, FORALL_3, LINEAR_CMUL, MATRIX_ADD_COMPONENT, .. } := D.vec1
  let { MATRIX_ID, MATRIX_OF_MATRIX_VECTOR_MUL, MATRIX_SUB_COMPONENT,
        MATRIX_VECTOR_MUL_ADD_RDISTRIB, MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID,
        MATRIX_VECTOR_MUL_LINEAR, MATRIX_VECTOR_MUL_SUB_RDISTRIB, MAT_COMPONENT, NORM_0,
        NORM_BASIS, NORM_EQ_0, NORM_MUL, NORM_NEG, NORM_POS_LE, ORTHOGONAL_LNEG,
        ORTHOGONAL_RNEG, REAL_ABS_NORM, .. } := D.vec2
  let { SUM_3, VECTOR_MUL_COMPONENT, VECTOR_MUL_EQ_0, VECTOR_MUL_LID, VECTOR_MUL_LNEG,
        VECTOR_SUB_EQ, matrix_mul, matrix_vector_mul, row, transp, .. } := D.vec3
  let { DET_I, DET_ROW_MUL, DET_TRANSP, .. } := BDetBasic
  let { DET_MUL, .. } := BMultilinear
  let { HOMOGENEOUS_LINEAR_EQUATIONS_DET, .. } := BInvertibility
  let { DET_3, .. } := BLowDim
  let { ORTHOGONAL_MATRIX, ORTHOGONAL_MATRIX_MUL, ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS,
        ORTHOGONAL_MATRIX_TRANSP, ORTHOGONAL_TRANSFORMATION_LINEAR,
        ORTHOGONAL_TRANSFORMATION_MATRIX, orthogonal_matrix, .. } := BOrth1
  let { ORTHOGONAL_TRANSFORMATION_ID, .. } := BOrth2
  let { ORTHOGONAL_MATRIX_EXISTS_BASIS, ORTHOGONAL_TRANSFORMATION_EXISTS, .. } := BOpNorm
  let { ORTHOGONAL_ROTATION_OR_ROTOINVERSION, rotation_matrix, rotoinversion_matrix,
        .. } := BRotation1
  -- @@SCOPE END
  let ar (s : String) : ExceptT String IO thm := do ARITH_RULE (← q s)

  let ROTATION_MATRIX_EXISTS_BASIS ← prove
   r"!a:real^N.
        2 <= dimindex(:N) /\ norm(a) = &1
        ==> ?A. rotation_matrix A /\ A**(basis 1) = a"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"A:real^N^N") STRIP_ASSUME_TAC o
     MATCH_MP ORTHOGONAL_MATRIX_EXISTS_BASIS) THEN
    FIRST_ASSUM (DISJ_CASES_TAC o GEN_REWRITE_RULE id
     [ORTHOGONAL_ROTATION_OR_ROTOINVERSION])
    THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    EXISTS_TAC (← q r"transp(lambda i. if i = dimindex(:N) then -- &1 % transp A$i
                               else (transp A:real^N^N)$i):real^N^N") THEN
    REWRITE_TAC [rotation_matrix, DET_TRANSP] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC [ORTHOGONAL_MATRIX_TRANSP],
      SIMP_TAC [DET_ROW_MUL, DIMINDEX_GE_1, LE_REFL] THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"x = -- &1 ==> -- &1 * x = &1")) THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [rotoinversion_matrix]) THEN
      DISCH_THEN (SUBST1_TAC o SYM o CONJUNCT2) THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM DET_TRANSP] THEN
      AP_TERM_TAC THEN SIMP_TAC [CART_EQ, LAMBDA_BETA] THEN MESON_TAC [],
      FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
      SIMP_TAC [matrix_vector_mul, LAMBDA_BETA, CART_EQ, transp,
                BASIS_COMPONENT] THEN
      ONCE_REWRITE_TAC [← REAL_ARITH (← q
        r"x * (if p then &1 else &0) = if p then x else &0")] THEN
      ASM_SIMP_TAC [← ar r"2 <= n ==> ~(1 = n)", LAMBDA_BETA]] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id
     [← GSYM ORTHOGONAL_MATRIX_TRANSP]) THEN
    SPEC_TAC (← q r"transp(A:real^N^N)", ← q r"B:real^N^N") THEN GEN_TAC THEN
    SUBGOAL_THEN (← q r"!i. 1 <= i /\ i <= dimindex(:N)
                    ==> row i ((lambda i. if i = dimindex(:N) then -- &1 % B$i
                                else (B:real^N^N)$i):real^N^N) =
                        if i = dimindex(:N) then --(row i B) else row i B")
    ASSUME_TAC THENL
     [SIMP_TAC [row, LAMBDA_BETA, LAMBDA_ETA, VECTOR_MUL_LID, VECTOR_MUL_LNEG],
      ASM_SIMP_TAC [ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS] THEN
      ASM_MESON_TAC [ORTHOGONAL_LNEG, ORTHOGONAL_RNEG, NORM_NEG]])

  let ROTATION_EXISTS_1 ← prove
   r"!a b:real^N.
        2 <= dimindex(:N) /\ norm(a) = &1 /\ norm(b) = &1
        ==> ?f. orthogonal_transformation f /\ det(matrix f) = &1 /\ f a = b"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"b:real^N") ROTATION_MATRIX_EXISTS_BASIS) THEN
    MP_TAC (← ISPEC (← q r"a:real^N") ROTATION_MATRIX_EXISTS_BASIS) THEN
    ASM_REWRITE_TAC [rotation_matrix] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"A:real^N^N")
     (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (ASSUME_TAC o SYM))) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"B:real^N^N")
     (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (ASSUME_TAC o SYM))) THEN
    EXISTS_TAC (← q r"\x:real^N. ((B:real^N^N) ** transp(A:real^N^N)) ** x") THEN
    REWRITE_TAC [ORTHOGONAL_TRANSFORMATION_MATRIX, MATRIX_VECTOR_MUL_LINEAR,
                 MATRIX_OF_MATRIX_VECTOR_MUL, DET_MUL, DET_TRANSP] THEN
    ASM_SIMP_TAC [ORTHOGONAL_MATRIX_MUL, ORTHOGONAL_MATRIX_TRANSP] THEN
    REWRITE_TAC [← GSYM MATRIX_VECTOR_MUL_ASSOC, REAL_MUL_LID] THEN AP_TERM_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ORTHOGONAL_MATRIX]) THEN
    ASM_REWRITE_TAC [MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID])

  let ROTATION_EXISTS ← prove
   r"!a b:real^N.
        2 <= dimindex(:N) /\ norm(a) = norm(b)
        ==> ?f. orthogonal_transformation f /\ det(matrix f) = &1 /\ f a = b"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"b:real^N = vec 0") THEN
    ASM_SIMP_TAC [NORM_0, NORM_EQ_0] THENL
     [MESON_TAC [ORTHOGONAL_TRANSFORMATION_ID, MATRIX_ID, DET_I], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"a:real^N = vec 0") THENL
     [ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION_ID, MATRIX_ID, DET_I, NORM_0,
                     NORM_EQ_0], ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"inv(norm a) % a:real^N", ← q r"inv(norm b) % b:real^N"]
                  ROTATION_EXISTS_1) THEN
    REWRITE_TAC [NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
    ASM_SIMP_TAC [NORM_EQ_0, REAL_MUL_LINV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f:real^N->real^N") THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP LINEAR_CMUL o
                MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
    ASM_REWRITE_TAC [← VECTOR_ARITH (← q
     r"a % x:real^N = a % y <=> a % (x - y) = vec 0")] THEN
    ASM_REWRITE_TAC [VECTOR_MUL_EQ_0, REAL_INV_EQ_0, NORM_EQ_0, VECTOR_SUB_EQ])

  let ROTATION_RIGHTWARD_LINE ← prove
   r"!a:real^N k.
        1 <= k /\ k <= dimindex(:N)
        ==> ?b f. orthogonal_transformation f /\
                  (2 <= dimindex(:N) ==> det(matrix f) = &1) /\
                  f(b % basis k) = a /\
                  &0 <= b"
   (REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"norm(a:real^N)") THEN
    ASM_SIMP_TAC [VECTOR_MUL_COMPONENT, BASIS_COMPONENT, LE_REFL, DIMINDEX_GE_1,
                  REAL_MUL_RID, NORM_POS_LE, LT_IMP_LE, LTE_ANTISYM] THEN
    REWRITE_TAC [← ar r"2 <= n <=> 1 <= n /\ ~(n = 1)", DIMINDEX_GE_1] THEN
    ASM_CASES_TAC (← q r"dimindex(:N) = 1") THEN ASM_REWRITE_TAC [] THENL
     [MATCH_MP_TAC ORTHOGONAL_TRANSFORMATION_EXISTS,
      MATCH_MP_TAC ROTATION_EXISTS] THEN
     ASM_SIMP_TAC [NORM_MUL, NORM_BASIS, LE_REFL, DIMINDEX_GE_1] THEN
     REWRITE_TAC [REAL_ABS_NORM, REAL_MUL_RID] THEN
     MATCH_MP_TAC (← ar r"~(n = 1) /\ 1 <= n ==> 2 <= n") THEN
     ASM_REWRITE_TAC [DIMINDEX_GE_1])

  let EULER_ROTATION_THEOREM ← prove
   r"!A:real^3^3. rotation_matrix A ==> ?v:real^3. ~(v = vec 0) /\ A ** v = v"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"A - mat 1:real^3^3") HOMOGENEOUS_LINEAR_EQUATIONS_DET) THEN
    REWRITE_TAC [MATRIX_VECTOR_MUL_SUB_RDISTRIB,
                 VECTOR_SUB_EQ, MATRIX_VECTOR_MUL_LID] THEN
    DISCH_THEN SUBST1_TAC THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC [rotation_matrix, orthogonal_matrix, DET_3] THEN
    SIMP_TAC [CART_EQ, FORALL_3, MAT_COMPONENT, DIMINDEX_3, LAMBDA_BETA, ARITH,
              MATRIX_SUB_COMPONENT, MAT_COMPONENT, SUM_3,
              matrix_mul, transp, matrix_vector_mul] THEN
    CONV_TAC (fun t => REAL_RING t))

  let EULER_ROTOINVERSION_THEOREM ← prove
   r"!A:real^3^3.
     rotoinversion_matrix A ==> ?v:real^3. ~(v = vec 0) /\ A ** v = --v"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [← VECTOR_ARITH (← q r"a:real^N = --v <=> a + v = vec 0")] THEN
    MP_TAC (← ISPEC (← q r"A + mat 1:real^3^3") HOMOGENEOUS_LINEAR_EQUATIONS_DET) THEN
    REWRITE_TAC [MATRIX_VECTOR_MUL_ADD_RDISTRIB, MATRIX_VECTOR_MUL_LID] THEN
    DISCH_THEN SUBST1_TAC THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC [rotoinversion_matrix, orthogonal_matrix, DET_3] THEN
    SIMP_TAC [CART_EQ, FORALL_3, MAT_COMPONENT, DIMINDEX_3, LAMBDA_BETA, ARITH,
              MATRIX_ADD_COMPONENT, MAT_COMPONENT, SUM_3,
              matrix_mul, transp, matrix_vector_mul] THEN
    CONV_TAC (fun t => REAL_RING t))

  return { ROTATION_MATRIX_EXISTS_BASIS, ROTATION_EXISTS_1, ROTATION_EXISTS,
           ROTATION_RIGHTWARD_LINE, EULER_ROTATION_THEOREM, EULER_ROTOINVERSION_THEOREM }

/- ------------------------------------------------------------------------- -/
/- We can always rotate so that a hyperplane is "horizontal".                -/
/- (determinants.ml 3800-4033)                                                -/
/- ------------------------------------------------------------------------- -/

structure Horizontal where
  ROTATION_LOWDIM_HORIZONTAL : thm
  ORTHOGONAL_TRANSFORMATION_LOWDIM_HORIZONTAL : thm
  ORTHOGONAL_TRANSFORMATION_BETWEEN_ORTHOGONAL_SETS : thm
  deriving Inhabited

@[nospecialize]
def setupHorizontal [HolBase] (D : DeterminantsDeps) (BDetBasic : DetBasic) (BOrth1 : Orth1)
    (BOrth2 : Orth2) (BIso : Iso) (BRotation2 : Rotation2) : ExceptT String IO Horizontal := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC, REAL_ARITH,
        SET_RULE, SET_TAC, VECTOR_ARITH_TAC, .. } := D
  let { CARD_EQ_BIJECTION, CARD_IMAGE_INJ, CARD_NUMSEG, CARD_NUMSEG_1, CARD_UNION, COND_RAND,
        COND_RATOR, CONJ_ASSOC, DIMINDEX_GE_1, DISJOINT, EQ_TRANS, FINITE_IMAGE,
        FINITE_IMAGE_INJ_EQ, FINITE_INDEX_NUMSEG, FINITE_NUMSEG, FINITE_UNION,
        FORALL_IN_IMAGE, IMP_CONJ, IN_ELIM_THM, IN_IMAGE, IN_NUMSEG, IN_UNION, LAMBDA_BETA,
        LAMBDA_ETA, LEFT_IMP_EXISTS_THM, .. } := D.core1
  let { LE_REFL, LE_TRANS, MONO_EXISTS, PAIRWISE_IMAGE, PAIRWISE_MONO, REAL_ABS_INV,
        REAL_ENTIRE, REAL_MUL_LINV, REAL_MUL_RID, REAL_MUL_RINV, .. } := D.core2
  let { SUBSET, SUBSET_UNIV, SWAP_FORALL_THM, UNION_UNIV, WLOG_LT, o_THM, pairwise,
        .. } := D.core3
  let { DE_MORGAN_THM, EQ_IMP, .. } := D.core4
  let { BASIS_CARD_EQ_DIM, BASIS_COMPONENT, DIM_EQ_0, DIM_UNIV, DOT_BASIS, DOT_LMUL,
        DOT_RMUL, DOT_SYM, INDEPENDENT_BOUND, INDEPENDENT_IMP_FINITE, LINEAR_0, LINEAR_CMUL,
        LINEAR_COMPOSE_VSUM, LOWDIM_SUBSET_HYPERPLANE, .. } := D.vec1
  let { MATRIX_ID, NORM_0, NORM_BASIS, NORM_EQ_0, NORM_EQ_SQUARE, NORM_MUL, ORTHOGONAL_REFL,
        ORTHOGONAL_SYM, ORTHONORMAL_EXTENSION, PAIRWISE_ORTHOGONAL_INDEPENDENT,
        REAL_ABS_NORM, .. } := D.vec2
  let { SPAN_SUPERSET, SPAN_UNIV, VECTOR_ADD_COMPONENT, VECTOR_MUL_ASSOC,
        VECTOR_MUL_COMPONENT, VECTOR_MUL_LID, VECTOR_MUL_LZERO, VEC_COMPONENT, VSUM_DELTA,
        column, dot, linear, matrix, orthogonal, .. } := D.vec3
  let { DET_I, .. } := BDetBasic
  let { ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS, ORTHOGONAL_TRANSFORMATION_COMPOSE,
        ORTHOGONAL_TRANSFORMATION_MATRIX, orthogonal_transformation, .. } := BOrth1
  let { ORTHOGONAL_TRANSFORMATION_ID, .. } := BOrth2
  let { ORTHOGONAL_TRANSFORMATION_INVERSE, .. } := BIso
  let { ROTATION_EXISTS, .. } := BRotation2
  -- @@SCOPE END
  let ar (s : String) : ExceptT String IO thm := do ARITH_RULE (← q s)
  let sr (s : String) : ExceptT String IO thm := do SET_RULE (← q s)

  let ROTATION_LOWDIM_HORIZONTAL ← prove
   r"!s:real^N->bool.
        dim s < dimindex(:N)
        ==> ?f. orthogonal_transformation f /\ det(matrix f) = &1 /\
               (IMAGE f s) SUBSET {z | z$(dimindex(:N)) = &0}"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"dim(s:real^N->bool) = 0") THENL
     [RULE_ASSUM_TAC (REWRITE_RULE [DIM_EQ_0]) THEN DISCH_TAC THEN
      EXISTS_TAC (← q r"\x:real^N. x") THEN
      REWRITE_TAC [ORTHOGONAL_TRANSFORMATION_ID, MATRIX_ID, DET_I] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← sr
       r"s SUBSET {a} ==> a IN t ==> IMAGE (\x. x) s SUBSET t")) THEN
      SIMP_TAC [IN_ELIM_THM, VEC_COMPONENT, LE_REFL, DIMINDEX_GE_1],
      DISCH_TAC] THEN
    SUBGOAL_THEN (← q r"2 <= dimindex(:N)") ASSUME_TAC THENL
     [ASM_ARITH_TAC, ALL_TAC] THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"a:real^N") STRIP_ASSUME_TAC o MATCH_MP
      LOWDIM_SUBSET_HYPERPLANE) THEN
    MP_TAC (← ISPECL [← q r"a:real^N", ← q r"norm(a:real^N) % basis(dimindex(:N)):real^N"]
          ROTATION_EXISTS) THEN
    ASM_SIMP_TAC [NORM_MUL, NORM_BASIS, LE_REFL, DIMINDEX_GE_1] THEN
    REWRITE_TAC [REAL_ABS_NORM, REAL_MUL_RID] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f:real^N->real^N") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [FORALL_IN_IMAGE, SUBSET, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"(f:real^N->real^N) x dot (f a) = &0") MP_TAC THENL
     [RULE_ASSUM_TAC (REWRITE_RULE [orthogonal_transformation]) THEN
      ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [DOT_SYM] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [SUBSET]) THEN
      ASM_SIMP_TAC [SPAN_SUPERSET, IN_ELIM_THM],
      ASM_SIMP_TAC [DOT_BASIS, LE_REFL, DIMINDEX_GE_1, DOT_RMUL] THEN
      ASM_REWRITE_TAC [REAL_ENTIRE, NORM_EQ_0]])

  let ORTHOGONAL_TRANSFORMATION_LOWDIM_HORIZONTAL ← prove
   r"!s:real^N->bool.
        dim s < dimindex(:N)
        ==> ?f. orthogonal_transformation f /\
               (IMAGE f s) SUBSET {z | z$(dimindex(:N)) = &0}"
   (GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP ROTATION_LOWDIM_HORIZONTAL) THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [])

  let ORTHOGONAL_TRANSFORMATION_BETWEEN_ORTHOGONAL_SETS ← do
    let lemma1 ← prove
     r"!v:num->real^N n.
          pairwise (\i j. orthogonal (v i) (v j)) (1..n) /\
          (!i. 1 <= i /\ i <= n ==> norm(v i) = &1)
          ==> ?f. orthogonal_transformation f /\
                  (!i. 1 <= i /\ i <= n ==> f(basis i) = v i)"
     (REWRITE_TAC [pairwise, IN_NUMSEG, ← GSYM CONJ_ASSOC] THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"pairwise orthogonal (IMAGE (v:num->real^N) (1..n))")
      ASSUME_TAC THENL
       [REWRITE_TAC [PAIRWISE_IMAGE] THEN ASM_SIMP_TAC [pairwise, IN_NUMSEG],
        ALL_TAC] THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
            PAIRWISE_ORTHOGONAL_INDEPENDENT)) THEN
      REWRITE_TAC [← sr
       r"~(a IN IMAGE f s) <=> !x. x IN s ==> ~(f x = a)"] THEN
      ANTS_TAC THENL
       [REWRITE_TAC [IN_NUMSEG] THEN
        ASM_MESON_TAC [NORM_0, ← REAL_ARITH (← q r"~(&1 = &0)")],
        DISCH_THEN (MP_TAC o CONJUNCT2 o MATCH_MP INDEPENDENT_BOUND)] THEN
      SUBGOAL_THEN
       (← q r"!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n /\ ~(i = j)
            ==> ~(v i:real^N = v j)")
      ASSUME_TAC THENL
       [ASM_MESON_TAC [ORTHOGONAL_REFL, NORM_0, ← REAL_ARITH (← q r"~(&1 = &0)")],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"CARD(IMAGE (v:num->real^N) (1..n)) = n") ASSUME_TAC THENL
       [W (MP_TAC o PART_MATCH (lhs o rand) CARD_IMAGE_INJ o lhs o snd) THEN
        ASM_REWRITE_TAC [CARD_NUMSEG_1, IN_NUMSEG, FINITE_NUMSEG] THEN
        ASM_MESON_TAC [],
        ASM_REWRITE_TAC [] THEN DISCH_TAC] THEN
      SUBGOAL_THEN
       (← q r"?w:num->real^N.
          pairwise (\i j. orthogonal (w i) (w j)) (1..dimindex(:N)) /\
          (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(w i) = &1) /\
          (!i. 1 <= i /\ i <= n ==> w i = v i)")
      STRIP_ASSUME_TAC THENL
       [ALL_TAC,
        EXISTS_TAC
         (← q r"(\x. vsum(1..dimindex(:N)) (\i. x$i % w i)):real^N->real^N") THEN
        SIMP_TAC [BASIS_COMPONENT, IN_NUMSEG, COND_RATOR, COND_RAND] THEN
        REWRITE_TAC [VECTOR_MUL_LID, VECTOR_MUL_LZERO, VSUM_DELTA] THEN
        ASM_SIMP_TAC [IN_NUMSEG] THEN CONJ_TAC THENL
         [ALL_TAC, ASM_MESON_TAC [LE_TRANS]] THEN
        REWRITE_TAC [ORTHOGONAL_TRANSFORMATION_MATRIX] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC LINEAR_COMPOSE_VSUM THEN
          REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
          REWRITE_TAC [linear, VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
          REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC,
          ALL_TAC] THEN
        REWRITE_TAC [matrix, column, ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS] THEN
        SIMP_TAC [LAMBDA_BETA, LAMBDA_ETA, BASIS_COMPONENT, IN_NUMSEG] THEN
        SIMP_TAC [COND_RATOR, COND_RAND, VECTOR_MUL_LZERO, VSUM_DELTA] THEN
        SIMP_TAC [IN_NUMSEG, orthogonal, dot, LAMBDA_BETA, NORM_EQ_SQUARE] THEN
        REWRITE_TAC [VECTOR_MUL_LID, ← GSYM dot, ← GSYM NORM_EQ_SQUARE] THEN
        RULE_ASSUM_TAC (REWRITE_RULE [pairwise, IN_NUMSEG, orthogonal]) THEN
        ASM_SIMP_TAC []] THEN
      FIRST_ASSUM (MP_TAC o SPEC (← q r"(:real^N)") o MATCH_MP
       (← REWRITE_RULE [IMP_CONJ] ORTHONORMAL_EXTENSION)) THEN
      ASM_REWRITE_TAC [FORALL_IN_IMAGE, IN_NUMSEG, UNION_UNIV, SPAN_UNIV] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"t:real^N->bool") STRIP_ASSUME_TAC) THEN
      MP_TAC (← ISPECL [← q r"n+1..dimindex(:N)", ← q r"t:real^N->bool"]
            CARD_EQ_BIJECTION) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [FINITE_NUMSEG] THEN
        MP_TAC (← ISPECL [← q r"(:real^N)", ← q r"IMAGE v (1..n) UNION t:real^N->bool"]
            BASIS_CARD_EQ_DIM) THEN
        ASM_REWRITE_TAC [SUBSET_UNIV] THEN ANTS_TAC THENL
         [MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN
          ASM_REWRITE_TAC [IN_UNION, DE_MORGAN_THM, IN_NUMSEG] THEN
          ASM_REWRITE_TAC [FORALL_IN_IMAGE, IN_NUMSEG, ← sr
           r"~(x IN s) <=> !y. y IN s ==> ~(y = x)"] THEN
          ASM_MESON_TAC [NORM_0, ← REAL_ARITH (← q r"~(&1 = &0)")],
          ALL_TAC] THEN
        ASM_SIMP_TAC [FINITE_UNION, IMP_CONJ, FINITE_IMAGE, CARD_UNION,
                      ← sr r"t INTER s = {} <=> DISJOINT s t"] THEN
        DISCH_TAC THEN DISCH_TAC THEN REWRITE_TAC [CARD_NUMSEG, DIM_UNIV] THEN
        ARITH_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [CONJ_ASSOC, ← sr
       r"(!x. x IN s ==> f x IN t) /\ (!y. y IN t ==> ?x. x IN s /\ f x = y) <=>
      t = IMAGE f s"] THEN
      REWRITE_TAC [← GSYM CONJ_ASSOC, LEFT_IMP_EXISTS_THM, IN_NUMSEG] THEN
      X_GEN_TAC (← q r"w:num->real^N") THEN
      DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
      REWRITE_TAC [← ar r"n + 1 <= x <=> n < x", CONJ_ASSOC] THEN
      ONCE_REWRITE_TAC [← TAUT (← q r"p /\ q ==> r <=> p /\ ~r ==> ~q")] THEN
      REWRITE_TAC [← GSYM CONJ_ASSOC] THEN STRIP_TAC THEN
      REWRITE_TAC [← TAUT (← q r"p /\ ~r ==> ~q <=> p /\ q ==> r")] THEN
      EXISTS_TAC (← q r"\i. if i <= n then (v:num->real^N) i else w i") THEN
      SIMP_TAC [] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [FORALL_IN_IMAGE, IN_NUMSEG]) THEN
      CONJ_TAC THENL
       [ALL_TAC, ASM_MESON_TAC [← ar r"~(i <= n) ==> n + 1 <= i"]] THEN
      REWRITE_TAC [pairwise] THEN MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC [] THEN
      CONJ_TAC THENL [MESON_TAC [ORTHOGONAL_SYM], ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"j:num"] THEN DISCH_TAC THEN
      ASM_CASES_TAC (← q r"j:num <= n") THEN ASM_REWRITE_TAC [IN_NUMSEG] THENL
       [COND_CASES_TAC THEN ASM_SIMP_TAC [] THEN ASM_ARITH_TAC, ALL_TAC] THEN
      ASM_CASES_TAC (← q r"i:num <= n") THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
      UNDISCH_TAC
       (← q r"pairwise orthogonal
        (IMAGE (v:num->real^N) (1..n) UNION IMAGE w (n+1..dimindex (:N)))") THEN
      REWRITE_TAC [pairwise] THEN ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"(w:num->real^N) j")) THENL
       [DISCH_THEN (MP_TAC o SPEC (← q r"(v:num->real^N) i")),
        DISCH_THEN (MP_TAC o SPEC (← q r"(w:num->real^N) i"))] THEN
      ASM_REWRITE_TAC [IN_UNION, IN_IMAGE, IN_NUMSEG] THEN
      DISCH_THEN MATCH_MP_TAC THENL
       [CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        CONJ_TAC THENL
         [ASM_MESON_TAC [← ar r"~(x <= n) ==> n + 1 <= x"], ALL_TAC],
        ASM_MESON_TAC [← ar r"~(x <= n) ==> n + 1 <= x /\ n < x"]] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [DISJOINT]) THEN
      REWRITE_TAC [← sr r"IMAGE w t INTER IMAGE v s = {} <=>
      !i j. i IN s /\ j IN t ==> ~(v i = w j)"] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [IN_NUMSEG] THEN
      ASM_ARITH_TAC)
    let lemma2 ← prove
     r"!v:num->real^N w k.
          pairwise (\i j. orthogonal (v i) (v j)) k /\
          pairwise (\i j. orthogonal (w i) (w j)) k /\
          (!i. i IN k ==> norm(v i) = norm(w i)) /\
          (!i. i IN k ==> ~(v i = vec 0) /\ ~(w i = vec 0))
          ==> ?f. orthogonal_transformation f /\
                  (!i. i IN k ==> f(v i) = w i)"
     (REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"FINITE(k:num->bool)") MP_TAC THENL
       [SUBGOAL_THEN (← q r"pairwise orthogonal (IMAGE (v:num->real^N) k)")
        ASSUME_TAC THENL
         [REWRITE_TAC [PAIRWISE_IMAGE] THEN
          RULE_ASSUM_TAC (REWRITE_RULE [pairwise]) THEN ASM_SIMP_TAC [pairwise],
          ALL_TAC] THEN
        FIRST_ASSUM (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          PAIRWISE_ORTHOGONAL_INDEPENDENT)) THEN
        ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
        DISCH_THEN (MP_TAC o MATCH_MP INDEPENDENT_IMP_FINITE) THEN
        MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
        RULE_ASSUM_TAC (REWRITE_RULE [pairwise]) THEN
        ASM_MESON_TAC [ORTHOGONAL_REFL],
        ALL_TAC] THEN
      DISCH_THEN (MP_TAC o GEN_REWRITE_RULE id [FINITE_INDEX_NUMSEG]) THEN
      ONCE_REWRITE_TAC [← TAUT (← q r"p /\ q /\ r ==> s <=> p /\ q /\ ~s ==> ~r")] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"n:num->num") MP_TAC) THEN
      REWRITE_TAC [IN_NUMSEG] THEN GEN_REWRITE_TAC id [IMP_CONJ] THEN
      DISCH_THEN (fun th => DISCH_THEN SUBST_ALL_TAC THEN ASSUME_TAC th) THEN
      RULE_ASSUM_TAC (REWRITE_RULE
       [PAIRWISE_IMAGE, FORALL_IN_IMAGE, IN_NUMSEG]) THEN
      MP_TAC (← ISPECL
       [← q r"\i. inv(norm(w(n i))) % (w:num->real^N) ((n:num->num) i)",
        ← q r"CARD(k:num->bool)"] lemma1) THEN
      MP_TAC (← ISPECL
       [← q r"\i. inv(norm(v(n i))) % (v:num->real^N) ((n:num->num) i)",
        ← q r"CARD(k:num->bool)"] lemma1) THEN
      ASM_SIMP_TAC [NORM_MUL, REAL_MUL_LINV, NORM_EQ_0, REAL_ABS_INV,
                    REAL_ABS_NORM, pairwise, orthogonal, IN_NUMSEG] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [pairwise, orthogonal, IN_NUMSEG]) THEN
      ASM_SIMP_TAC [DOT_LMUL, DOT_RMUL, REAL_ENTIRE, FORALL_IN_IMAGE] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:real^N->real^N") STRIP_ASSUME_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->real^N") STRIP_ASSUME_TAC) THEN
      MP_TAC (← ISPEC (← q r"f:real^N->real^N") ORTHOGONAL_TRANSFORMATION_INVERSE) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f':real^N->real^N") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"(g:real^N->real^N) o (f':real^N->real^N)") THEN
      ASM_SIMP_TAC [ORTHOGONAL_TRANSFORMATION_COMPOSE, IN_NUMSEG] THEN
      X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN REWRITE_TAC [o_THM] THEN
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
       (← q r"(g:real^N->real^N) (norm((w:num->real^N)(n(i:num))) % basis i)") THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← MESON [] (← q
         r"(!x. f'(f x) = x) ==> f x = y ==> f' y = x"))),
        ALL_TAC] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [orthogonal_transformation]) THEN
      ASM_SIMP_TAC [LINEAR_CMUL, VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC [REAL_MUL_RINV, NORM_EQ_0, VECTOR_MUL_LID])
    prove
     r"!v:num->real^N w k.
        pairwise (\i j. orthogonal (v i) (v j)) k /\
        pairwise (\i j. orthogonal (w i) (w j)) k /\
        (!i. i IN k ==> norm(v i) = norm(w i))
        ==> ?f. orthogonal_transformation f /\
                (!i. i IN k ==> f(v i) = w i)"
     (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL
       [← q r"v:num->real^N", ← q r"w:num->real^N",
        ← q r"{i | i IN k /\ ~((v:num->real^N) i = vec 0)}"] lemma2) THEN
      ASM_SIMP_TAC [IN_ELIM_THM, CONJ_ASSOC] THEN ANTS_TAC THENL
       [CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [NORM_EQ_0]] THEN
        CONJ_TAC THEN MATCH_MP_TAC PAIRWISE_MONO THEN EXISTS_TAC (← q r"k:num->bool") THEN
        ASM_REWRITE_TAC [] THEN SET_TAC [],
        MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [orthogonal_transformation] THEN
        GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
        ASM_CASES_TAC (← q r"(v:num->real^N) i = vec 0") THEN ASM_SIMP_TAC [] THEN
        ASM_MESON_TAC [LINEAR_0, NORM_EQ_0]])

  return { ROTATION_LOWDIM_HORIZONTAL, ORTHOGONAL_TRANSFORMATION_LOWDIM_HORIZONTAL,
           ORTHOGONAL_TRANSFORMATION_BETWEEN_ORTHOGONAL_SETS }

/- ------------------------------------------------------------------------- -/
/- Induction on matrix structure via elementary row operations and           -/
/- elementary matrices (permutation, scaling, row addition).                 -/
/- (determinants.ml 4035-4286)                                               -/
/- ------------------------------------------------------------------------- -/

structure MatrixInduct where
  INDUCT_MATRIX_ROW_OPERATIONS : thm
  INDUCT_MATRIX_ELEMENTARY : thm
  INDUCT_MATRIX_ELEMENTARY_ALT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupMatrixInduct [HolBase] (D : DeterminantsDeps) (BTrace : Trace) :
    ExceptT String IO MatrixInduct := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, REAL_ARITH,
        REAL_ARITH_TAC, REAL_FIELD, REAL_RING, .. } := D
  let { AND_FORALL_THM, ARITH, CART_EQ, COND_ID, COND_RAND, COND_RATOR, CONJ_ASSOC, EQ_TRANS,
        FINITE_RULES, IMP_CONJ, IN_INSERT, IN_NUMSEG, LAMBDA_BETA, LEFT_IMP_EXISTS_THM, LE_0, .. } := D.core1
  let { MONO_FORALL, NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, REAL_MUL_LID, REAL_MUL_LINV,
        REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RZERO, .. } := D.core2
  let { SUBSET, SUM_CLAUSES, SUM_DELTA, SUM_SUPERSET, num_INDUCTION, .. } := D.core3
  let { DE_MORGAN_THM, EQ_IMP, EQ_SYM_EQ, IMP_CONJ_ALT, MONO_AND, .. } := D.core4
  let { COND_COMPONENT, .. } := D.vec1
  let { VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, VEC_COMPONENT, mat, matrix_mul, row, .. } := D.vec3
  let { swap, .. } := D.lib
  let { IN_DIMINDEX_SWAP, .. } := BTrace
  -- @@SCOPE END

  let INDUCT_MATRIX_ROW_OPERATIONS ← prove
   r"!P:real^N^N->bool.
        (!A i. 1 <= i /\ i <= dimindex(:N) /\ row i A = vec 0 ==> P A) /\
        (!A. (!i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
                    ==> A$i$j = &0) ==> P A) /\
        (!A m n. P A /\ 1 <= m /\ m <= dimindex(:N) /\
                 1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
                 ==> P(lambda i j. A$i$(swap(m,n) j))) /\
        (!A m n c. P A /\ 1 <= m /\ m <= dimindex(:N) /\
                   1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
                   ==> P(lambda i. if i = m then row m A + c % row n A
                                   else row i A))
        ==> !A. P A"
   (GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "zero_row") MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "diagonal") MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "swap_cols") (LABEL_TAC "row_op")) THEN
    SUBGOAL_THEN
     (← q r"!k A:real^N^N.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               k <= j /\ j <= dimindex(:N) /\ ~(i = j)
               ==> A$i$j = &0)
        ==> P A")
     (fun th => tactic_of do
        pure (GEN_TAC THEN MATCH_MP_TAC th THEN
              EXISTS_TAC (← q r"dimindex(:N) + 1") THEN ARITH_TAC)) THEN
    MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "diagonal" MATCH_MP_TAC THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [LE_0],
      ALL_TAC] THEN
    X_GEN_TAC (← q r"k:num") THEN DISCH_THEN (LABEL_TAC "ind_hyp") THEN
    DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC (← ARITH_RULE (← q r"k = 0 \/ 1 <= k")) THEN
    ASM_REWRITE_TAC [ARITH] THEN
    ASM_CASES_TAC (← q r"k <= dimindex(:N)") THENL
     [ALL_TAC,
      REPEAT STRIP_TAC THEN REMOVE_THEN "ind_hyp" MATCH_MP_TAC THEN
      ASM_ARITH_TAC] THEN
    SUBGOAL_THEN
     (← q r"!A:real^N^N.
        ~(A$k$k = &0) /\
        (!i j. 1 <= i /\ i <= dimindex (:N) /\
               SUC k <= j /\ j <= dimindex (:N) /\ ~(i = j)
               ==> A$i$j = &0)
        ==> P A")
    (LABEL_TAC "nonzero_hyp") THENL
     [ALL_TAC,
      X_GEN_TAC (← q r"A:real^N^N") THEN DISCH_TAC THEN
      ASM_CASES_TAC (← q r"row k (A:real^N^N) = vec 0") THENL
       [REMOVE_THEN "zero_row" MATCH_MP_TAC THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
      SIMP_TAC [VEC_COMPONENT, row, LAMBDA_BETA] THEN
      REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"l:num") THEN STRIP_TAC THEN
      ASM_CASES_TAC (← q r"l:num = k") THENL
       [REMOVE_THEN "nonzero_hyp" MATCH_MP_TAC THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      REMOVE_THEN "swap_cols" (MP_TAC o SPECL
       [← q r"(lambda i j. (A:real^N^N)$i$swap(k,l) j):real^N^N",
        ← q r"k:num", ← q r"l:num"]) THEN
      ASM_SIMP_TAC [LAMBDA_BETA] THEN ANTS_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
        SIMP_TAC [CART_EQ, LAMBDA_BETA] THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC [swap] THEN
        REPEAT (COND_CASES_TAC THEN ASM_SIMP_TAC [LAMBDA_BETA])] THEN
      REMOVE_THEN "nonzero_hyp" MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC [← ARITH_RULE (← q r"SUC k <= i <=> 1 <= i /\ SUC k <= i")] THEN
      ASM_SIMP_TAC [LAMBDA_BETA] THEN
      ASM_REWRITE_TAC [swap] THEN MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"j:num"] THEN
      STRIP_TAC THEN SUBGOAL_THEN (← q r"l:num <= k") ASSUME_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o SPECL [← q r"k:num", ← q r"l:num"]) THEN
        ASM_REWRITE_TAC [] THEN ARITH_TAC,
        ALL_TAC] THEN
      REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
      ASM_ARITH_TAC] THEN
     SUBGOAL_THEN
     (← q r"!l A:real^N^N.
        ~(A$k$k = &0) /\
        (!i j. 1 <= i /\ i <= dimindex (:N) /\
               SUC k <= j /\ j <= dimindex (:N) /\ ~(i = j)
               ==> A$i$j = &0) /\
        (!i. l <= i /\ i <= dimindex(:N) /\ ~(i = k) ==> A$i$k = &0)
        ==> P A")
     MP_TAC THENL
      [ALL_TAC,
       DISCH_THEN (MP_TAC o SPEC (← q r"dimindex(:N) + 1")) THEN
       REWRITE_TAC [CONJ_ASSOC, ← ARITH_RULE (← q r"~(n + 1 <= i /\ i <= n)")]] THEN
     MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
      [GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
       DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "main") (LABEL_TAC "aux")) THEN
       USE_THEN "ind_hyp" MATCH_MP_TAC THEN
       MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"j:num"] THEN STRIP_TAC THEN
       ASM_CASES_TAC (← q r"j:num = k") THENL
        [ASM_REWRITE_TAC [] THEN USE_THEN "aux" MATCH_MP_TAC THEN ASM_ARITH_TAC,
         REMOVE_THEN "main" MATCH_MP_TAC THEN ASM_ARITH_TAC],
      ALL_TAC] THEN
    X_GEN_TAC (← q r"l:num") THEN DISCH_THEN (LABEL_TAC "inner_hyp") THEN
    GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "main") (LABEL_TAC "aux")) THEN
    ASM_CASES_TAC (← q r"l:num = k") THENL
     [REMOVE_THEN "inner_hyp" MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN REMOVE_THEN "aux" MATCH_MP_TAC THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    DISJ_CASES_TAC (← ARITH_RULE (← q r"l = 0 \/ 1 <= l")) THENL
     [REMOVE_THEN "ind_hyp" MATCH_MP_TAC THEN
      MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"j:num"] THEN STRIP_TAC THEN
      ASM_CASES_TAC (← q r"j:num = k") THENL
       [ASM_REWRITE_TAC [] THEN REMOVE_THEN "aux" MATCH_MP_TAC THEN ASM_ARITH_TAC,
        REMOVE_THEN "main" MATCH_MP_TAC THEN ASM_ARITH_TAC],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"l <= dimindex(:N)") THENL
     [ALL_TAC,
      REMOVE_THEN "inner_hyp" MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
      ASM_ARITH_TAC] THEN
    REMOVE_THEN "inner_hyp" (MP_TAC o SPECL
     [← q r"(lambda i. if i = l then row l (A:real^N^N) + --(A$l$k/A$k$k) % row k A
                else row i A):real^N^N"]) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN (← q r"!i. l <= i ==> 1 <= i") ASSUME_TAC THENL
       [ASM_ARITH_TAC, ALL_TAC] THEN
      ONCE_REWRITE_TAC [← ARITH_RULE (← q r"SUC k <= j <=> 1 <= j /\ SUC k <= j")] THEN
      ASM_SIMP_TAC [LAMBDA_BETA, row, COND_COMPONENT,
                    VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
      ASM_SIMP_TAC [← REAL_FIELD (← q r"~(y = &0) ==> x + --(x / y) * y = &0")] THEN
      REWRITE_TAC [AND_FORALL_THM] THEN X_GEN_TAC (← q r"i:num") THEN
      ASM_CASES_TAC (← q r"i:num = l") THEN ASM_REWRITE_TAC [] THENL
       [REPEAT STRIP_TAC THEN
        MATCH_MP_TAC (← REAL_RING (← q r"x = &0 /\ y = &0 ==> x + z * y = &0")) THEN
        CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
        REPEAT STRIP_TAC THEN REMOVE_THEN "aux" MATCH_MP_TAC THEN ASM_ARITH_TAC],
      ALL_TAC] THEN
    DISCH_TAC THEN REMOVE_THEN "row_op" (MP_TAC o SPECL
     [← q r"(lambda i. if i = l then row l A + --(A$l$k / A$k$k) % row k A
                else row i (A:real^N^N)):real^N^N",
      ← q r"l:num", ← q r"k:num", ← q r"(A:real^N^N)$l$k / A$k$k"]) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC [CART_EQ, LAMBDA_BETA, VECTOR_ADD_COMPONENT,
                  VECTOR_MUL_COMPONENT, row, COND_COMPONENT] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    REAL_ARITH_TAC)

  let INDUCT_MATRIX_ELEMENTARY ← prove
   r"!P:real^N^N->bool.
        (!A B. P A /\ P B ==> P(A ** B)) /\
        (!A i. 1 <= i /\ i <= dimindex(:N) /\ row i A = vec 0 ==> P A) /\
        (!A. (!i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
                    ==> A$i$j = &0) ==> P A) /\
        (!m n. 1 <= m /\ m <= dimindex(:N) /\
               1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
               ==> P(lambda i j. (mat 1:real^N^N)$i$(swap(m,n) j))) /\
        (!m n c. 1 <= m /\ m <= dimindex(:N) /\
                 1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
                 ==> P(lambda i j. if i = m /\ j = n then c
                                   else if i = j then &1 else &0))
        ==> !A. P A"
   (GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (fun th =>
      MATCH_MP_TAC INDUCT_MATRIX_ROW_OPERATIONS THEN MP_TAC th) THEN
    REPEAT (MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN REWRITE_TAC [] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (X_GEN_TAC (← q r"A:real^N^N") THEN MP_TAC th)) THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC (← q r"(P:real^N^N->bool) A") THENL
     [REWRITE_TAC [← GSYM IMP_CONJ], REWRITE_TAC [← GSYM IMP_CONJ_ALT]] THEN
    DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN MATCH_MP_TAC EQ_IMP THEN
    AP_TERM_TAC THEN REWRITE_TAC [CART_EQ] THEN
    X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"j:num") THEN STRIP_TAC THEN
    ASM_SIMP_TAC [CART_EQ, LAMBDA_BETA, matrix_mul, row] THENL
     [ASM_SIMP_TAC [mat, IN_DIMINDEX_SWAP, LAMBDA_BETA] THEN
      ONCE_REWRITE_TAC [COND_RAND] THEN
      SIMP_TAC [SUM_DELTA, REAL_MUL_RZERO, REAL_MUL_RID] THEN
      COND_CASES_TAC THEN REWRITE_TAC [] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [swap, IN_NUMSEG]) THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"i:num = m") THEN ASM_REWRITE_TAC [] THENL
     [ALL_TAC,
      ONCE_REWRITE_TAC [COND_RAND] THEN ONCE_REWRITE_TAC [COND_RATOR] THEN
      REWRITE_TAC [REAL_MUL_LZERO] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
      ASM_SIMP_TAC [SUM_DELTA, LAMBDA_BETA, IN_NUMSEG, REAL_MUL_LID]] THEN
    ASM_SIMP_TAC [VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, LAMBDA_BETA] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
      (← q r"sum {m,n} (\k. (if k = n then c else if m = k then &1 else &0) *
                    (A:real^N^N)$k$j)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUPERSET THEN
      ASM_SIMP_TAC [SUBSET, IN_INSERT, NOT_IN_EMPTY, DE_MORGAN_THM,
                    IN_NUMSEG, REAL_MUL_LZERO] THEN
      ASM_ARITH_TAC,
      ASM_SIMP_TAC [SUM_CLAUSES, FINITE_RULES, IN_INSERT, NOT_IN_EMPTY] THEN
      REAL_ARITH_TAC])

  let INDUCT_MATRIX_ELEMENTARY_ALT ← prove
   r"!P:real^N^N->bool.
        (!A B. P A /\ P B ==> P(A ** B)) /\
        (!A i. 1 <= i /\ i <= dimindex(:N) /\ row i A = vec 0 ==> P A) /\
        (!A. (!i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
                    ==> A$i$j = &0) ==> P A) /\
        (!m n. 1 <= m /\ m <= dimindex(:N) /\
               1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
               ==> P(lambda i j. (mat 1:real^N^N)$i$(swap(m,n) j))) /\
        (!m n. 1 <= m /\ m <= dimindex(:N) /\
               1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
               ==> P(lambda i j. if i = m /\ j = n \/ i = j then &1 else &0))
        ==> !A. P A"
   (GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC INDUCT_MATRIX_ELEMENTARY THEN
    ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"c = &0") THENL
     [FIRST_X_ASSUM (fun th => tactic_of do
        pure (MATCH_MP_TAC th THEN
              MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"j:num"])) THEN
      ASM_SIMP_TAC [LAMBDA_BETA, COND_ID],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"(lambda i j. if i = m /\ j = n then c else if i = j then &1 else &0) =
  ((lambda i j. if i = j then if j = n then inv c else &1 else &0):real^N^N) **
    ((lambda i j. if i = m /\ j = n \/ i = j then &1 else &0):real^N^N) **
    ((lambda i j. if i = j then if j = n then c else &1 else &0):real^N^N)")
    SUBST1_TAC THENL
     [ALL_TAC,
      REPEAT (MATCH_MP_TAC (← ASSUME (← q r"!A B:real^N^N. P A /\ P B ==> P(A ** B)")) THEN
             CONJ_TAC) THEN
      ASM_SIMP_TAC [] THEN FIRST_X_ASSUM (fun th => tactic_of do
        pure (MATCH_MP_TAC th THEN
              MAP_EVERY X_GEN_TAC [← q r"i:num", ← q r"j:num"])) THEN
      ASM_SIMP_TAC [LAMBDA_BETA]] THEN
    SIMP_TAC [CART_EQ, matrix_mul, LAMBDA_BETA] THEN
    X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"j:num") THEN STRIP_TAC THEN
    ASM_SIMP_TAC [SUM_DELTA, IN_NUMSEG, ← REAL_ARITH
         (← q r"(if p then &1 else &0) * (if q then c else &0) =
        if q then if p then c else &0 else &0")] THEN
    REWRITE_TAC [← REAL_ARITH
     (← q r"(if p then x else &0) * y = (if p then x * y else &0)")] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC [SUM_DELTA, IN_NUMSEG] THEN
    ASM_CASES_TAC (← q r"i:num = m") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"j:num = n") THEN ASM_REWRITE_TAC [REAL_MUL_LID, EQ_SYM_EQ] THEN
    ASM_CASES_TAC (← q r"i:num = n") THEN
    ASM_SIMP_TAC [REAL_MUL_LINV, REAL_MUL_LID, REAL_MUL_RZERO])

  return { INDUCT_MATRIX_ROW_OPERATIONS, INDUCT_MATRIX_ELEMENTARY,
           INDUCT_MATRIX_ELEMENTARY_ALT }

/- ------------------------------------------------------------------------- -/
/- Reflection of a vector about 0 along a line, first part, ending with the  -/
/- load-time `add_linear_invariants [REFLECT_ALONG_LINEAR_IMAGE]`.           -/
/- (determinants.ml 4291-4376)                                                -/
/- ------------------------------------------------------------------------- -/

structure Reflect1 where
  reflect_along : thm
  REFLECT_ALONG_ADD : thm
  REFLECT_ALONG_MUL : thm
  LINEAR_REFLECT_ALONG : thm
  REFLECT_ALONG_0 : thm
  REFLECT_ALONG_NEG : thm
  REFLECT_ALONG_REFL : thm
  REFLECT_ALONG_INVOLUTION : thm
  REFLECT_ALONG_GALOIS : thm
  REFLECT_ALONG_EQ_0 : thm
  ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG : thm
  REFLECT_ALONG_EQ_SELF : thm
  REFLECT_ALONG_ZERO : thm
  REFLECT_ALONG_LINEAR_IMAGE : thm
  deriving Inhabited

@[nospecialize]
def setupReflect1 [HolBase] (D : DeterminantsDeps) (BOrth1 : Orth1) (BOrth2 : Orth2) :
    ExceptT String IO Reflect1 := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD, VECTOR_ARITH, VECTOR_ARITH_TAC,
        add_linear_invariants, new_definition, .. } := D
  let { ETA_AX, FUN_EQ_THM, .. } := D.core1
  let { REAL_DIV_REFL, .. } := D.core2
  let { I_THM, .. } := D.core4
  let { DOT_EQ_0, DOT_LADD, DOT_LMUL, DOT_LSUB, DOT_LZERO, DOT_RMUL, DOT_SYM, LINEAR_0,
        LINEAR_CMUL, LINEAR_NEG, LINEAR_SUB, .. } := D.vec1
  let { NORM_EQ, ORTHOGONAL_0, PRESERVES_NORM_PRESERVES_DOT, .. } := D.vec2
  let { VECTOR_MUL_ASSOC, VECTOR_MUL_EQ_0, VECTOR_MUL_RZERO, VECTOR_NEG_0,
        VECTOR_SUB_LDISTRIB, VECTOR_SUB_RZERO, linear, orthogonal, .. } := D.vec3
  let { ORTHOGONAL_TRANSFORMATION, .. } := BOrth1
  let { ORTHOGONAL_TRANSFORMATION_ID, .. } := BOrth2
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let reflect_along ← new_definition
   r"reflect_along v (x:real^N) = x - (&2 * (x dot v) / (v dot v)) % v"

  let REFLECT_ALONG_ADD ← prove
   r"!v x y:real^N.
      reflect_along v (x + y) = reflect_along v x + reflect_along v y"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [reflect_along, ← va
     r"x - a % v + y - b % v:real^N = (x + y) - (a + b) % v"] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [DOT_LADD] THEN REAL_ARITH_TAC)

  let REFLECT_ALONG_MUL ← prove
   r"!v a x:real^N. reflect_along v (a % x) = a % reflect_along v x"
   (REWRITE_TAC [reflect_along, DOT_LMUL, ← REAL_ARITH (← q
     r"&2 * (a * x) / y = a * &2 * x / y")] THEN
    REWRITE_TAC [VECTOR_SUB_LDISTRIB, VECTOR_MUL_ASSOC])

  let LINEAR_REFLECT_ALONG ← prove
   r"!v:real^N. linear(reflect_along v)"
   (REWRITE_TAC [linear, REFLECT_ALONG_ADD, REFLECT_ALONG_MUL])

  let REFLECT_ALONG_0 ← prove
   r"!v:real^N. reflect_along v (vec 0) = vec 0"
   (REWRITE_TAC [← MATCH_MP LINEAR_0 (← SPEC_ALL LINEAR_REFLECT_ALONG)])

  let REFLECT_ALONG_NEG ← prove
   r"!v x:real^N. reflect_along v (--x) = --(reflect_along v x)"
   (MESON_TAC [LINEAR_REFLECT_ALONG, LINEAR_NEG])

  let REFLECT_ALONG_REFL ← prove
   r"!v:real^N. reflect_along v v = --v"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"v:real^N = vec 0") THEN
    ASM_REWRITE_TAC [VECTOR_NEG_0, REFLECT_ALONG_0] THEN
    REWRITE_TAC [reflect_along] THEN
    ASM_SIMP_TAC [REAL_DIV_REFL, DOT_EQ_0] THEN VECTOR_ARITH_TAC)

  let REFLECT_ALONG_INVOLUTION ← prove
   r"!v x:real^N. reflect_along v (reflect_along v x) = x"
   (REWRITE_TAC [reflect_along, DOT_LSUB, VECTOR_MUL_EQ_0, ← va
     r"x - a % v - b % v:real^N = x <=> (a + b) % v = vec 0"] THEN
    REWRITE_TAC [DOT_LMUL, ← GSYM DOT_EQ_0] THEN CONV_TAC (fun t => REAL_FIELD t))

  let REFLECT_ALONG_GALOIS ← prove
   r"!v p q:real^N. reflect_along v p = q <=> p = reflect_along v q"
   (MESON_TAC [REFLECT_ALONG_INVOLUTION])

  let REFLECT_ALONG_EQ_0 ← prove
   r"!v x:real^N. reflect_along v x = vec 0 <=> x = vec 0"
   (MESON_TAC [REFLECT_ALONG_0, REFLECT_ALONG_INVOLUTION])

  let ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG ← prove
   r"!v:real^N. orthogonal_transformation(reflect_along v)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"v:real^N = vec 0") THENL
     [GEN_REWRITE_TAC RAND_CONV [← GSYM ETA_AX] THEN
      ASM_REWRITE_TAC [reflect_along, VECTOR_MUL_RZERO, VECTOR_SUB_RZERO,
                       ORTHOGONAL_TRANSFORMATION_ID],
      REWRITE_TAC [ORTHOGONAL_TRANSFORMATION] THEN
      REWRITE_TAC [LINEAR_REFLECT_ALONG, NORM_EQ] THEN
      REWRITE_TAC [reflect_along, ← va
        r"(a - b:real^N) dot (a - b) = (a dot a + b dot b) - &2 * a dot b"] THEN
      REWRITE_TAC [DOT_LMUL, DOT_RMUL] THEN X_GEN_TAC (← q r"w:real^N") THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [← GSYM DOT_EQ_0]) THEN
      CONV_TAC (fun t => REAL_FIELD t)])

  let REFLECT_ALONG_EQ_SELF ← prove
   r"!v x:real^N. reflect_along v x = x <=> orthogonal v x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [reflect_along, orthogonal] THEN
    REWRITE_TAC [← va r"x - a:real^N = x <=> a = vec 0"] THEN
    REWRITE_TAC [VECTOR_MUL_EQ_0] THEN
    ASM_CASES_TAC (← q r"v:real^N = vec 0") THEN ASM_SIMP_TAC [DOT_LZERO, DOT_SYM] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [← GSYM DOT_EQ_0]) THEN
    CONV_TAC (fun t => REAL_FIELD t))

  let REFLECT_ALONG_ZERO ← prove
   r"reflect_along (vec 0:real^N) = I"
   (REWRITE_TAC [FUN_EQ_THM, I_THM, REFLECT_ALONG_EQ_SELF, ORTHOGONAL_0])

  let REFLECT_ALONG_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N v x.
        linear f /\ (!x. norm(f x) = norm x)
        ==> reflect_along (f v) (f x) = f(reflect_along v x)"
   (REWRITE_TAC [reflect_along] THEN
    SIMP_TAC [PRESERVES_NORM_PRESERVES_DOT, LINEAR_SUB, LINEAR_CMUL])

  add_linear_invariants [REFLECT_ALONG_LINEAR_IMAGE]

  return { reflect_along, REFLECT_ALONG_ADD, REFLECT_ALONG_MUL, LINEAR_REFLECT_ALONG,
           REFLECT_ALONG_0, REFLECT_ALONG_NEG, REFLECT_ALONG_REFL, REFLECT_ALONG_INVOLUTION,
           REFLECT_ALONG_GALOIS, REFLECT_ALONG_EQ_0, ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG,
           REFLECT_ALONG_EQ_SELF, REFLECT_ALONG_ZERO, REFLECT_ALONG_LINEAR_IMAGE }

/- ------------------------------------------------------------------------- -/
/- Reflection of a vector about 0 along a line, second part.                 -/
/- (determinants.ml 4378-4570)                                                -/
/- ------------------------------------------------------------------------- -/

structure Reflect2 where
  REFLECT_ALONG_SCALE : thm
  REFLECT_ALONG_NEGATION : thm
  REFLECT_ALONG_1D : thm
  REFLECT_ALONG_BASIS : thm
  MATRIX_REFLECT_ALONG_BASIS : thm
  ROTOINVERSION_MATRIX_REFLECT_ALONG : thm
  DET_MATRIX_REFLECT_ALONG : thm
  REFLECT_ALONG_BASIS_COMPONENT : thm
  REFLECT_BASIS_ALONG_BASIS : thm
  NORM_REFLECT_ALONG : thm
  REFLECT_ALONG_EQ : thm
  REFLECT_ALONG_SURJECTIVE : thm
  REFLECT_ALONG_SWITCH : thm
  ROTOINVERSION_EXISTS_GEN : thm
  ORTHOGONAL_TRANSFORMATION_EXISTS_GEN : thm
  deriving Inhabited

@[nospecialize]
def setupReflect2 [HolBase] (D : DeterminantsDeps) (BDetBasic : DetBasic)
    (BMultilinear : Multilinear) (BOrth1 : Orth1) (BOrth2 : Orth2) (BOpNorm : OpNorm)
    (BRotation1 : Rotation1) (BReflect1 : Reflect1) : ExceptT String IO Reflect2 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON_TAC,
        REAL_ARITH_TAC, REAL_FIELD, REAL_RING, SET_RULE, VECTOR_ARITH, .. } := D
  let { ARITH_EQ, CART_EQ, COND_RAND, COND_RATOR, DIMINDEX_GE_1, EQ_TRANS, FUN_EQ_THM,
        IMAGE_ID, IN_NUMSEG, LAMBDA_BETA, .. } := D.core1
  let { LE_REFL, REAL_ABS_INV, REAL_DIV_1, REAL_INV_EQ_0, REAL_MUL_LINV, REAL_MUL_LZERO,
        REAL_MUL_RZERO, REAL_NEG_0, REAL_OF_NUM_EQ, .. } := D.core2
  let { REAL_SUB_REFL, real_div, .. } := D.core3
  let { BASIS_COMPONENT, DOT_BASIS, DOT_EQ_0, DOT_LMUL, DOT_LSUB, DOT_RMUL, DOT_RSUB,
        DOT_SYM, FORALL_1, MATRIX_EQ, MATRIX_I, .. } := D.vec1
  let { MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID, MATRIX_WORKS, NORM_0, NORM_BASIS,
        NORM_EQ_0, NORM_MUL, NORM_POW_2, REAL_ABS_NORM, .. } := D.vec2
  let { SUBSPACE_MUL, SUBSPACE_SUB, SUM_1, VECTOR_MUL_ASSOC, VECTOR_MUL_COMPONENT,
        VECTOR_MUL_EQ_0, VECTOR_MUL_RZERO, VECTOR_NEG_COMPONENT, VECTOR_NEG_MINUS1,
        VECTOR_SUB_COMPONENT, VECTOR_SUB_EQ, VEC_COMPONENT, dot, matrix, orthogonal,
        .. } := D.vec3
  let { PRODUCT_CLAUSES_LEFT, PRODUCT_EQ_1, .. } := D.lib
  let { DET_I, DET_TRANSP, DET_UPPERTRIANGULAR, .. } := BDetBasic
  let { DET_MUL, .. } := BMultilinear
  let { DET_ORTHOGONAL_MATRIX, ORTHOGONAL_MATRIX, ORTHOGONAL_TRANSFORMATION,
        ORTHOGONAL_TRANSFORMATION_INJECTIVE, ORTHOGONAL_TRANSFORMATION_LINEAR,
        ORTHOGONAL_TRANSFORMATION_MATRIX, .. } := BOrth1
  let { ORTHOGONAL_TRANSFORMATION_ID, .. } := BOrth2
  let { ORTHOGONAL_TRANSFORMATION_EXISTS, .. } := BOpNorm
  let { rotoinversion_matrix, .. } := BRotation1
  let { reflect_along, REFLECT_ALONG_INVOLUTION, REFLECT_ALONG_ZERO,
        REFLECT_ALONG_LINEAR_IMAGE, LINEAR_REFLECT_ALONG,
        ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG, .. } := BReflect1
  -- @@SCOPE END

  let REFLECT_ALONG_SCALE ← prove
   r"!c v x:real^N. ~(c = &0) ==> reflect_along (c % v) x = reflect_along v x"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"v:real^N = vec 0") THEN
    ASM_REWRITE_TAC [VECTOR_MUL_RZERO, REFLECT_ALONG_ZERO] THEN
    REWRITE_TAC [reflect_along, VECTOR_MUL_ASSOC] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [DOT_RMUL] THEN REWRITE_TAC [DOT_LMUL] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [← GSYM DOT_EQ_0]) THEN
    POP_ASSUM MP_TAC THEN CONV_TAC (fun t => REAL_FIELD t))

  let REFLECT_ALONG_NEGATION ← prove
   r"!v:real^N. reflect_along (--v) = reflect_along v"
   (REWRITE_TAC [FUN_EQ_THM, VECTOR_NEG_MINUS1] THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC REFLECT_ALONG_SCALE THEN REAL_ARITH_TAC)

  let REFLECT_ALONG_1D ← prove
   r"!v x:real^N.
        dimindex(:N) = 1 ==> reflect_along v x = if v = vec 0 then x else --x"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [reflect_along, dot, SUM_1, CART_EQ, FORALL_1] THEN
    REWRITE_TAC [VEC_COMPONENT, COND_RATOR, COND_RAND] THEN
    SIMP_TAC [VECTOR_NEG_COMPONENT, VECTOR_MUL_COMPONENT,
              VECTOR_SUB_COMPONENT, REAL_MUL_RZERO] THEN
    CONV_TAC (fun t => REAL_FIELD t))

  let REFLECT_ALONG_BASIS ← prove
   r"!x:real^N k.
        1 <= k /\ k <= dimindex(:N)
        ==> reflect_along (basis k) x = x - (&2 * x$k) % basis k"
   (SIMP_TAC [reflect_along, DOT_BASIS, BASIS_COMPONENT, REAL_DIV_1])

  let MATRIX_REFLECT_ALONG_BASIS ← prove
   r"!k. 1 <= k /\ k <= dimindex(:N)
       ==> matrix(reflect_along (basis k)):real^N^N =
           lambda i j. if i = k /\ j = k then --(&1)
                       else if i = j then &1
                       else &0"
   (SIMP_TAC [CART_EQ, LAMBDA_BETA, matrix, REFLECT_ALONG_BASIS,
              VECTOR_SUB_COMPONENT, BASIS_COMPONENT, VECTOR_MUL_COMPONENT] THEN
    X_GEN_TAC (← q r"k:num") THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"j:num") THEN STRIP_TAC THEN
    ASM_CASES_TAC (← q r"i:num = j") THEN ASM_REWRITE_TAC [] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN ASM_REAL_ARITH_TAC)

  let ROTOINVERSION_MATRIX_REFLECT_ALONG ← prove
   r"!v:real^N. ~(v = vec 0) ==> rotoinversion_matrix(matrix(reflect_along v))"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [rotoinversion_matrix] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION_MATRIX,
                     ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG],
      ALL_TAC] THEN
    ABBREV_TAC (← q r"w:real^N = inv(norm v) % v") THEN
    SUBGOAL_THEN (← q r"reflect_along (v:real^N) = reflect_along w") SUBST1_TAC THENL
     [EXPAND_TAC "w" THEN REWRITE_TAC [FUN_EQ_THM] THEN
      ASM_SIMP_TAC [REFLECT_ALONG_SCALE, REAL_INV_EQ_0, NORM_EQ_0],
      SUBGOAL_THEN (← q r"norm(w:real^N) = &1") MP_TAC THENL
       [EXPAND_TAC "w" THEN SIMP_TAC [NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
        MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC [NORM_EQ_0],
        POP_ASSUM_LIST (K ALL_TAC) THEN SPEC_TAC (← q r"w:real^N", ← q r"v:real^N")]] THEN
    X_GEN_TAC (← q r"v:real^N") THEN ASM_CASES_TAC (← q r"v:real^N = vec 0") THEN
    ASM_REWRITE_TAC [NORM_0, REAL_OF_NUM_EQ, ARITH_EQ] THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"v:real^N", ← q r"basis 1:real^N"]
          ORTHOGONAL_TRANSFORMATION_EXISTS) THEN
    ASM_SIMP_TAC [NORM_BASIS, DIMINDEX_GE_1, LE_REFL] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"f:real^N->real^N") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     (← q r"matrix(reflect_along v) =
    transp(matrix(f:real^N->real^N)) ** matrix(reflect_along (f v)) ** matrix f")
    SUBST1_TAC THENL
     [UNDISCH_THEN (← q r"(f:real^N->real^N) v = basis 1") (K ALL_TAC) THEN
      REWRITE_TAC [MATRIX_EQ, ← GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC [MATRIX_WORKS, LINEAR_REFLECT_ALONG,
                    ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
      X_GEN_TAC (← q r"x:real^N") THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC (← q r"(transp(matrix(f:real^N->real^N)) ** matrix f) **
                (reflect_along v x:real^N)") THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC [ORTHOGONAL_MATRIX, MATRIX_VECTOR_MUL_LID,
                       ORTHOGONAL_TRANSFORMATION_MATRIX],
        REWRITE_TAC [← GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC [MATRIX_WORKS, ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
        AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC REFLECT_ALONG_LINEAR_IMAGE THEN
        ASM_REWRITE_TAC [← GSYM ORTHOGONAL_TRANSFORMATION]],
      ASM_REWRITE_TAC [DET_MUL, DET_TRANSP] THEN
      MATCH_MP_TAC (← REAL_RING (← q
       r"(x = &1 \/ x = -- &1) /\ y = a ==> x * y * x = a")) THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC [DET_ORTHOGONAL_MATRIX, ORTHOGONAL_TRANSFORMATION_MATRIX],
        ALL_TAC] THEN
      W (MP_TAC o PART_MATCH (lhs o rand) DET_UPPERTRIANGULAR o lhand o snd) THEN
      SIMP_TAC [MATRIX_REFLECT_ALONG_BASIS, DIMINDEX_GE_1, LE_REFL] THEN
      SIMP_TAC [LAMBDA_BETA, ← ARITH_RULE (← q
       r"j < i ==> ~(i = j) /\ ~(i = 1 /\ j = 1)")] THEN
      DISCH_THEN (K ALL_TAC) THEN
      SIMP_TAC [PRODUCT_CLAUSES_LEFT, DIMINDEX_GE_1] THEN
      MATCH_MP_TAC (← REAL_RING (← q r"x = &1 ==> a * x = a")) THEN
      MATCH_MP_TAC PRODUCT_EQ_1 THEN
      REWRITE_TAC [IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC])

  let DET_MATRIX_REFLECT_ALONG ← prove
   r"!v:real^N. det(matrix(reflect_along v)) =
                if v = vec 0 then &1 else --(&1)"
   (GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [REFLECT_ALONG_ZERO] THEN
    REWRITE_TAC [MATRIX_I, DET_I] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP ROTOINVERSION_MATRIX_REFLECT_ALONG) THEN
    SIMP_TAC [rotoinversion_matrix])

  let REFLECT_ALONG_BASIS_COMPONENT ← prove
   r"!x:real^N i j.
       1 <= i /\ i <= dimindex(:N) /\
       1 <= j /\ j <= dimindex(:N)
       ==> reflect_along (basis i) x$j = if j = i then --(x$j) else x$j"
   (SIMP_TAC [REFLECT_ALONG_BASIS, VECTOR_SUB_COMPONENT] THEN
    SIMP_TAC [VECTOR_MUL_COMPONENT, BASIS_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC)

  let REFLECT_BASIS_ALONG_BASIS ← prove
   r"!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
         ==> reflect_along (basis i:real^N) (basis j) =
             if i = j then --(basis j) else basis j"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [CART_EQ, REFLECT_ALONG_BASIS_COMPONENT, BASIS_COMPONENT,
                  VECTOR_NEG_COMPONENT] THEN
    ASM_MESON_TAC [REAL_NEG_0])

  let NORM_REFLECT_ALONG ← prove
   r"!v x:real^N. norm(reflect_along v x) = norm x"
   (MESON_TAC [ORTHOGONAL_TRANSFORMATION,
               ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG])

  let REFLECT_ALONG_EQ ← prove
   r"!v x y:real^N. reflect_along v x = reflect_along v y <=> x = y"
   (MESON_TAC [ORTHOGONAL_TRANSFORMATION_INJECTIVE,
               ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG])

  let REFLECT_ALONG_SURJECTIVE ← prove
   r"!v y:real^N. ?x. reflect_along v x = y"
   (MESON_TAC [REFLECT_ALONG_INVOLUTION])

  let REFLECT_ALONG_SWITCH ← prove
   r"!a b:real^N.
        norm a = norm b /\ ~(a = b)
        ==> reflect_along (b - a) a = b /\ reflect_along (b - a) b = a"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SIMP_TAC [reflect_along, DOT_RSUB] THEN
    REWRITE_TAC [real_div, ← VECTOR_ARITH (← q
      r"(a - c % (b - a):real^N = b <=> (&1 + c) % (b - a) = vec 0) /\
     (b - c % (b - a):real^N = a <=> (&1 - c) % (b - a) = vec 0)")] THEN
    ASM_REWRITE_TAC [VECTOR_MUL_EQ_0, VECTOR_SUB_EQ] THEN
    MATCH_MP_TAC (← REAL_FIELD (← q
     r"~(d = &0) /\ x + y = &0 /\ y - x = d
    ==> &1 + &2 * x * inv d = &0 /\ &1 - &2 * y * inv d = &0")) THEN
    ASM_REWRITE_TAC [← GSYM DOT_RSUB, DOT_EQ_0, VECTOR_SUB_EQ] THEN
    ASM_REWRITE_TAC [DOT_RSUB, ← GSYM NORM_POW_2, DOT_LSUB] THEN
    REWRITE_TAC [DOT_SYM] THEN REAL_ARITH_TAC)

  let ROTOINVERSION_EXISTS_GEN ← prove
   r"!s a b:real^N.
        subspace s /\ a IN s /\ b IN s /\ ~(a = b) /\ norm a = norm b
         ==> ?f. orthogonal_transformation f /\ IMAGE f s = s /\
                 (!x. orthogonal a x /\ orthogonal b x ==> f x = x) /\
                 det (matrix f) = -- &1 /\
                 f a = b /\ f b = a"
   (REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"reflect_along (b - a:real^N)") THEN
    REWRITE_TAC [ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG] THEN
    ASM_REWRITE_TAC [DET_MATRIX_REFLECT_ALONG, VECTOR_SUB_EQ] THEN
    ASM_SIMP_TAC [REFLECT_ALONG_SWITCH] THEN CONJ_TAC THENL
     [MATCH_MP_TAC (← SET_RULE (← q
       r"(!x. f(f x) = x) /\ (!x. x IN s ==> f x IN s) ==> IMAGE f s = s")) THEN
      REWRITE_TAC [REFLECT_ALONG_INVOLUTION] THEN REWRITE_TAC [reflect_along] THEN
      ASM_SIMP_TAC [SUBSPACE_SUB, SUBSPACE_MUL],
      REWRITE_TAC [← ONCE_REWRITE_RULE [DOT_SYM] orthogonal] THEN
      SIMP_TAC [reflect_along, DOT_RSUB] THEN
      REWRITE_TAC [real_div, REAL_SUB_REFL, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
      REWRITE_TAC [← VECTOR_ARITH (← q r"x - &0 % y:real^N = x")]])

  let ORTHOGONAL_TRANSFORMATION_EXISTS_GEN ← prove
   r"!s a b:real^N.
        subspace s /\ a IN s /\ b IN s /\ norm a = norm b
         ==> ?f. orthogonal_transformation f /\ IMAGE f s = s /\
                 (!x. orthogonal a x /\ orthogonal b x ==> f x = x) /\
                 f a = b /\ f b = a"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"b:real^N = a") THENL
     [EXISTS_TAC (← q r"\x:real^N. x") THEN
      ASM_REWRITE_TAC [ORTHOGONAL_TRANSFORMATION_ID, IMAGE_ID],
      MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"a:real^N", ← q r"b:real^N"]
          ROTOINVERSION_EXISTS_GEN) THEN
      ASM_REWRITE_TAC [] THEN MESON_TAC []])

  return { REFLECT_ALONG_SCALE, REFLECT_ALONG_NEGATION, REFLECT_ALONG_1D, REFLECT_ALONG_BASIS,
           MATRIX_REFLECT_ALONG_BASIS, ROTOINVERSION_MATRIX_REFLECT_ALONG,
           DET_MATRIX_REFLECT_ALONG, REFLECT_ALONG_BASIS_COMPONENT, REFLECT_BASIS_ALONG_BASIS,
           NORM_REFLECT_ALONG, REFLECT_ALONG_EQ, REFLECT_ALONG_SURJECTIVE,
           REFLECT_ALONG_SWITCH, ROTOINVERSION_EXISTS_GEN,
           ORTHOGONAL_TRANSFORMATION_EXISTS_GEN }

/- ------------------------------------------------------------------------- -/
/- All orthogonal transformations are a composition of reflections.          -/
/- (determinants.ml 4576-4659)                                                -/
/- ------------------------------------------------------------------------- -/

structure GenRefl where
  ORTHOGONAL_TRANSFORMATION_GENERATED_BY_REFLECTIONS : thm
  ORTHOGONAL_TRANSFORMATION_REFLECT_INDUCT : thm
  deriving Inhabited

@[nospecialize]
def setupGenRefl [HolBase] (D : DeterminantsDeps) (BOrth1 : Orth1) (BOrth2 : Orth2)
    (BIso : Iso) (BReflect1 : Reflect1) : ExceptT String IO GenRefl := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, INDUCT_TAC, REAL_ARITH, REAL_RAT_REDUCE_CONV, VECTOR_ARITH,
        VECTOR_ARITH_TAC, .. } := D
  let { ADD_CLAUSES, ADD_SYM, EQ_TRANS, EXTENSION, FUN_EQ_THM, IMP_CONJ, IN_ELIM_THM, IN_UNIV,
        LE, LE_0, .. } := D.core1
  let { LE_ADD, LE_SUC, NOT_FORALL_THM, PSUBSET_ALT, REAL_MUL_LZERO, REAL_MUL_RZERO,
        .. } := D.core2
  let { REAL_SUB_REFL, SUBSET, SWAP_FORALL_THM, UNWIND_THM2, list_INDUCT, o_THM, real_div,
        ALL, ITLIST, LENGTH, LENGTH_EQ_NIL, .. } := D.core3
  let { I_THM, .. } := D.core4
  let { DIM_EQ_FULL, DIM_PSUBSET, DIM_SUBSET_UNIV, DIST_MIDPOINT, DOT_RMUL, DOT_RSUB,
        .. } := D.vec1
  let { NORM_EQ_SQUARE, NORM_POS_LE, NORM_POW_2, .. } := D.vec2
  let { SPAN_MONO, SPAN_OF_SUBSPACE, SPAN_SUPERSET, SUBSPACE_LINEAR_FIXED_POINTS,
        VECTOR_MUL_EQ_0, VECTOR_MUL_LZERO, VECTOR_SUB_EQ, VECTOR_SUB_RZERO, dist, midpoint,
        .. } := D.vec3
  let { ORTHOGONAL_TRANSFORMATION_COMPOSE, ORTHOGONAL_TRANSFORMATION_LINEAR,
        orthogonal_transformation, .. } := BOrth1
  let { ORTHOGONAL_TRANSFORMATION_I, .. } := BOrth2
  let { ORTHOGONAL_TRANSFORMATION_ISOMETRY, .. } := BIso
  let { ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG, REFLECT_ALONG_ADD, REFLECT_ALONG_INVOLUTION,
        REFLECT_ALONG_REFL, reflect_along, .. } := BReflect1
  -- @@SCOPE END

  let ORTHOGONAL_TRANSFORMATION_GENERATED_BY_REFLECTIONS ← prove
   r"!f:real^N->real^N n.
        orthogonal_transformation f /\
        dimindex(:N) <= dim {x | f x = x} + n
        ==> ?l. LENGTH l <= n /\ ALL (\v. ~(v = vec 0)) l /\
                f = ITLIST (\v h. reflect_along v o h) l I"
   (ONCE_REWRITE_TAC [← GSYM SWAP_FORALL_THM] THEN INDUCT_TAC THENL
     [REWRITE_TAC [← CONJUNCT1 LE, LENGTH_EQ_NIL, ADD_CLAUSES, UNWIND_THM2] THEN
      SIMP_TAC [DIM_SUBSET_UNIV, ← ARITH_RULE (← q r"a:num <= b ==> (b <= a <=> a = b)"),
                ITLIST, DIM_EQ_FULL, orthogonal_transformation] THEN
      SIMP_TAC [SPAN_OF_SUBSPACE, SUBSPACE_LINEAR_FIXED_POINTS, IMP_CONJ] THEN
      REWRITE_TAC [EXTENSION, IN_UNIV, IN_ELIM_THM] THEN
      SIMP_TAC [FUN_EQ_THM, I_THM, ALL],
      REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"!x:real^N. f x = x") THENL
       [EXISTS_TAC (← q r"[]:(real^N) list") THEN
        ASM_REWRITE_TAC [ITLIST, FUN_EQ_THM, I_THM, ALL, LENGTH, LE_0],
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [NOT_FORALL_THM])] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"a:real^N")) THEN
      ABBREV_TAC (← q r"v:real^N = inv(&2) % (f a - a)") THEN FIRST_X_ASSUM
        (MP_TAC o SPEC (← q r"reflect_along v o (f:real^N->real^N)")) THEN
      ASM_SIMP_TAC [ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG,
                    ORTHOGONAL_TRANSFORMATION_COMPOSE] THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← ARITH_RULE (← q
         r"a <= d + SUC n ==> d < d' ==> a <= d' + n"))) THEN
        MATCH_MP_TAC DIM_PSUBSET THEN REWRITE_TAC [PSUBSET_ALT] THEN
        SUBGOAL_THEN
         (← q r"!y:real^N. dist(y,f a) = dist(y,a) ==> reflect_along v y = y")
        ASSUME_TAC THENL
         [REWRITE_TAC [dist, NORM_EQ_SQUARE, NORM_POS_LE, NORM_POW_2] THEN
          REWRITE_TAC [← VECTOR_ARITH (← q
           r"(y - b:real^N) dot (y - b) =
          (y dot y + b dot b) - &2 * y dot b")] THEN
          REWRITE_TAC [← REAL_ARITH (← q r"(y + aa) - &2 * a = (y + bb) - &2 * b <=>
                                a - b = inv(&2) * (aa - bb)")] THEN
          RULE_ASSUM_TAC (REWRITE_RULE [orthogonal_transformation]) THEN
          ASM_REWRITE_TAC [REAL_SUB_REFL, REAL_MUL_RZERO] THEN
          EXPAND_TAC "v" THEN REWRITE_TAC [← GSYM DOT_RSUB, reflect_along] THEN
          SIMP_TAC [DOT_RMUL, real_div, REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
          REWRITE_TAC [VECTOR_MUL_LZERO, VECTOR_SUB_RZERO],
          ALL_TAC] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SPAN_MONO THEN SIMP_TAC [SUBSET, IN_ELIM_THM, o_THM] THEN
          ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION_ISOMETRY],
          ALL_TAC] THEN
        EXISTS_TAC (← q r"a:real^N") THEN
        ASM_SIMP_TAC [SUBSPACE_LINEAR_FIXED_POINTS, SPAN_OF_SUBSPACE,
                      ORTHOGONAL_TRANSFORMATION_LINEAR, IN_ELIM_THM] THEN
        MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC [IN_ELIM_THM, o_THM] THEN
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC (← q r"reflect_along (v:real^N) (midpoint(f a,a) + v)") THEN
        CONJ_TAC THENL
         [AP_TERM_TAC,
          REWRITE_TAC [REFLECT_ALONG_ADD] THEN
          ASM_SIMP_TAC [DIST_MIDPOINT, REFLECT_ALONG_REFL]] THEN
        EXPAND_TAC "v" THEN REWRITE_TAC [midpoint] THEN VECTOR_ARITH_TAC,
        DISCH_THEN (X_CHOOSE_THEN (← q r"l:(real^N)list") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"CONS (v:real^N) l") THEN
        ASM_REWRITE_TAC [ALL, LENGTH, LE_SUC, VECTOR_SUB_EQ, ITLIST] THEN
        EXPAND_TAC "v" THEN ASM_REWRITE_TAC [VECTOR_MUL_EQ_0] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC [VECTOR_SUB_EQ] THEN
        FIRST_X_ASSUM (MP_TAC o AP_TERM
         (← q r"(o)(reflect_along (v:real^N)):(real^N->real^N)->(real^N->real^N)")) THEN
        REWRITE_TAC [FUN_EQ_THM, o_THM, REFLECT_ALONG_INVOLUTION]]])

  let ORTHOGONAL_TRANSFORMATION_REFLECT_INDUCT ← prove
   r"!P:(real^N->real^N)->bool.
        P I /\
        (!f a. orthogonal_transformation f /\ ~(a = vec 0) /\ P f
               ==> P(reflect_along a o f))
        ==> !f. orthogonal_transformation f ==> P f"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^N->real^N", ← q r"dimindex(:N)"]
          ORTHOGONAL_TRANSFORMATION_GENERATED_BY_REFLECTIONS) THEN
    ASM_REWRITE_TAC [← ONCE_REWRITE_RULE [ADD_SYM] LE_ADD] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"l:(real^N)list") STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC (← q r"orthogonal_transformation(f:real^N->real^N)") THEN
    MATCH_MP_TAC (← TAUT (← q r"p /\ q ==> p ==> q")) THEN FIRST_X_ASSUM SUBST1_TAC THEN
    UNDISCH_TAC (← q r"ALL (\v:real^N. ~(v = vec 0)) l") THEN
    UNDISCH_THEN (← q r"LENGTH(l:(real^N)list) <= dimindex(:N)") (K ALL_TAC) THEN
    SPEC_TAC (← q r"l:(real^N)list", ← q r"l:(real^N)list") THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [ALL, ITLIST] THEN
    ASM_REWRITE_TAC [ORTHOGONAL_TRANSFORMATION_I] THEN
    ASM_SIMP_TAC [ORTHOGONAL_TRANSFORMATION_COMPOSE,
                  ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG])

  return { ORTHOGONAL_TRANSFORMATION_GENERATED_BY_REFLECTIONS,
           ORTHOGONAL_TRANSFORMATION_REFLECT_INDUCT }

/-- lib.ml's `itlist`, for a function with effects. -/
def itlistIO {α β : Type} (f : α → β → ExceptT String IO β) :
    List α → β → ExceptT String IO β
  | [], b => pure b
  | h :: t, b => do f h (← itlistIO f t b)

/-- lib.ml's `repeat`: apply `f` until it fails. -/
partial def repeatIO {α : Type} (f : α → ExceptT String IO α) (x : α) :
    ExceptT String IO α :=
  tryCatch (do repeatIO f (← f x)) (fun _ => pure x)

/- ------------------------------------------------------------------------- -/
/- Extract scaling, translation and linear invariance theorems.              -/
/- For the linear case, chain through some basic consequences automatically, -/
/- e.g. norm-preserving and linear implies injective.                        -/
/- (determinants.ml 4663-4704)                                                -/
/- ------------------------------------------------------------------------- -/

structure GeomInv where
  SCALING_THEOREMS : term → ExceptT String IO thm
  TRANSLATION_INVARIANTS : term → ExceptT String IO thm
  USABLE_CONCLUSION : term → List thm → thm → ExceptT String IO thm
  LINEAR_INVARIANTS : term → List thm → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupGeomInv [HolBase] (D : DeterminantsDeps) (BOrth1 : Orth1) :
    ExceptT String IO GeomInv := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, invariant_under_linear, invariant_under_translation, scaling_theorems,
        .. } := D
  let { RIGHT_FORALL_IMP_THM, .. } := D.core3
  let { LINEAR_SUB, LINEAR_SURJECTIVE_IFF_INJECTIVE, .. } := D.vec1
  let { NORM_EQ_0, NORM_POS_LT, .. } := D.vec2
  let { VECTOR_SUB_EQ, .. } := D.vec3
  let { ORTHOGONAL_TRANSFORMATION, ORTHOGONAL_TRANSFORMATION_INJECTIVE,
        ORTHOGONAL_TRANSFORMATION_SURJECTIVE, .. } := BOrth1
  -- @@SCOPE END

  let SCALING_THEOREMS (v : term) : ExceptT String IO thm := do
    let th1 ← UNDISCH (← EQ_IMP_RULE (← ISPEC v NORM_POS_LT)).2
    let t ← liftExcept (rand (concl th1))
    end_itlist CONJ (← (← scaling_theorems.get).mapM (fun th => do MP (← SPEC t th) th1))

  let TRANSLATION_INVARIANTS (x : term) : ExceptT String IO thm := do
    end_itlist CONJ
      (← HolMath.IndTypes.mapfilterM (ISPEC x) (← invariant_under_translation.get))

  let USABLE_CONCLUSION (f : term) (ths : List thm) (th : thm) : ExceptT String IO thm := do
    let ith ← PURE_REWRITE_RULE [RIGHT_FORALL_IMP_THM] (← ISPEC f th)
    let bod := concl ith
    let cjs := HolCore.Basics.conjuncts (← liftExcept (HolCore.Basics.dest_imp bod)).1
    let ths ← cjs.mapM (fun t =>
      liftExcept (HolCore.Lib.find (fun th => aconv (concl th) t) ths))
    GEN_ALL (← MP ith (← end_itlist CONJ ths))

  let LINEAR_INVARIANTS : term → List thm → ExceptT String IO thm ← do
    let sths := CONJUNCTS (← prove
     r"(!f:real^M->real^N.
         linear f /\ (!x. norm(f x) = norm x)
         ==> (!x y. f x = f y ==> x = y)) /\
     (!f:real^N->real^N.
         linear f /\ (!x. norm(f x) = norm x) ==> (!y. ?x. f x = y)) /\
     (!f:real^N->real^N. linear f /\ (!x y. f x = f y ==> x = y)
                         ==> (!y. ?x. f x = y)) /\
     (!f:real^N->real^N. linear f /\ (!y. ?x. f x = y)
                         ==> (!x y. f x = f y ==> x = y))"
     (CONJ_TAC THENL
       [ONCE_REWRITE_TAC [← GSYM VECTOR_SUB_EQ] THEN
        SIMP_TAC [← GSYM LINEAR_SUB, ← GSYM NORM_EQ_0],
        MESON_TAC [ORTHOGONAL_TRANSFORMATION_SURJECTIVE,
                   ORTHOGONAL_TRANSFORMATION_INJECTIVE, ORTHOGONAL_TRANSFORMATION,
                   LINEAR_SURJECTIVE_IFF_INJECTIVE]]))
    pure (fun f ths => do
      let ths' := ths ++ (← HolMath.IndTypes.mapfilterM (USABLE_CONCLUSION f ths) sths)
      end_itlist CONJ
       (← HolMath.IndTypes.mapfilterM (USABLE_CONCLUSION f ths')
            (← invariant_under_linear.get)))

  return { SCALING_THEOREMS, TRANSLATION_INVARIANTS, USABLE_CONCLUSION, LINEAR_INVARIANTS }

/- ------------------------------------------------------------------------- -/
/- Tactic to pick WLOG a particular point as the origin. The conversion form -/
/- assumes it's the outermost universal variable; the tactic is more general -/
/- and allows any free or outer universally quantified variable. The list    -/
/- "avoid" is the points not to translate. There is also a tactic to help in -/
/- proving new translation theorems, which uses similar machinery.           -/
/- Also: rename existential variables in conclusion to fresh genvars.        -/
/- (determinants.ml 4713-4801)                                                -/
/- ------------------------------------------------------------------------- -/

structure GeomOrigin where
  GEOM_ORIGIN_CONV : List String → ioconv
  GEOM_TRANSLATE_CONV : List String → term → ioconv
  GEN_GEOM_ORIGIN_TAC : term → List String → tactic
  GEOM_ORIGIN_TAC : term → tactic
  GEOM_TRANSLATE_TAC : List String → tactic
  EXISTS_GENVAR_RULE : thm → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupGeomOrigin [HolBase] (D : DeterminantsDeps) (BGeomInv : GeomInv) :
    ExceptT String IO GeomOrigin := do
  -- @@SCOPE BEGIN
  let { PARTIAL_EXPAND_QUANTS_CONV, SET_RULE, VECTOR_ARITH, VECTOR_ARITH_TAC, .. } := D
  let { EXISTS_REFL, IMAGE_CLAUSES, .. } := D.core1
  let { SURJECTIVE_IMAGE, MAP, .. } := D.core3
  let { BETA_THM, FORALL_SIMP, .. } := D.core4
  let { QUANTIFY_SURJECTION_HIGHER_THM, .. } := D.vec2
  let { VECTOR_ADD_RID, .. } := D.vec3
  let { TRANSLATION_INVARIANTS, .. } := BGeomInv
  -- @@SCOPE END

  let (GEOM_ORIGIN_CONV, GEOM_TRANSLATE_CONV) ← do
    let pth ← prove
     r"!a:real^N. a = a + vec 0 /\
                {} = IMAGE (\x. a + x) {} /\
                {} = IMAGE (IMAGE (\x. a + x)) {} /\
                (:real^N) = IMAGE (\x. a + x) (:real^N) /\
                (:real^N->bool) = IMAGE (IMAGE (\x. a + x)) (:real^N->bool) /\
                [] = MAP (\x. a + x) []"
     (REWRITE_TAC [IMAGE_CLAUSES, VECTOR_ADD_RID, MAP] THEN
      REWRITE_TAC [← SET_RULE (← q r"UNIV = IMAGE f UNIV <=> !y. ?x. f x = y")] THEN
      REWRITE_TAC [SURJECTIVE_IMAGE] THEN
      REWRITE_TAC [← VECTOR_ARITH (← q r"a + y:real^N = x <=> y = x - a"), EXISTS_REFL])
    let qth ← prove
     r"!a:real^N.
        ((!P. (!x. P x) <=> (!x. P (a + x))) /\
         (!P. (?x. P x) <=> (?x. P (a + x))) /\
         (!Q. (!s. Q s) <=> (!s. Q(IMAGE (\x. a + x) s))) /\
         (!Q. (?s. Q s) <=> (?s. Q(IMAGE (\x. a + x) s))) /\
         (!Q. (!s. Q s) <=> (!s. Q(IMAGE (IMAGE (\x. a + x)) s))) /\
         (!Q. (?s. Q s) <=> (?s. Q(IMAGE (IMAGE (\x. a + x)) s))) /\
         (!P. (!g:real^1->real^N. P g) <=> (!g. P ((\x. a + x) o g))) /\
         (!P. (?g:real^1->real^N. P g) <=> (?g. P ((\x. a + x) o g))) /\
         (!P. (!g:num->real^N. P g) <=> (!g. P ((\x. a + x) o g))) /\
         (!P. (?g:num->real^N. P g) <=> (?g. P ((\x. a + x) o g))) /\
         (!Q. (!l. Q l) <=> (!l. Q(MAP (\x. a + x) l))) /\
         (!Q. (?l. Q l) <=> (?l. Q(MAP (\x. a + x) l)))) /\
        ((!P. {x | P x} = IMAGE (\x. a + x) {x | P(a + x)}) /\
         (!Q. {s | Q s} =
              IMAGE (IMAGE (\x. a + x)) {s | Q(IMAGE (\x. a + x) s)}) /\
         (!R. {l | R l} = IMAGE (MAP (\x. a + x)) {l | R(MAP (\x. a + x) l)}))"
     (GEN_TAC THEN MATCH_MP_TAC QUANTIFY_SURJECTION_HIGHER_THM THEN
      X_GEN_TAC (← q r"y:real^N") THEN EXISTS_TAC (← q r"y - a:real^N") THEN
      VECTOR_ARITH_TAC)
    let GEOM_ORIGIN_CONV (avoid : List String) : ioconv := fun tm => (do
      let (x, tm0) ← liftExcept (HolCore.Basics.dest_forall tm)
      let th0 ← ISPEC x pth
      let x' ← HolCore.Basics.genvar (type_of x)
      let ith ← ISPEC x' qth
      let th1 ← ExceptT.mk
        ((← PARTIAL_EXPAND_QUANTS_CONV avoid (← ASSUME (concl ith))) tm0)
      let th2 ← CONV_RULE (RAND_CONV (SUBS_CONV (CONJUNCTS th0))) th1
      let th3 ← INST [(x, x')] (← PROVE_HYP ith th2)
      let ths ← TRANSLATION_INVARIANTS x
      let thr := REFL x
      let th4 ← GEN_REWRITE_RULE (RAND_CONV o REDEPTH_CONV)
        [BETA_THM, ← ADD_ASSUM (concl thr) ths] th3
      let th5 ← MK_FORALL x (← PROVE_HYP thr th4)
      GEN_REWRITE_RULE (RAND_CONV o TRY_CONV) [FORALL_SIMP] th5 :
        ExceptT String IO thm).run
    let GEOM_TRANSLATE_CONV (avoid : List String) (a : term) : ioconv := fun tm => (do
      let cth ← CONJUNCT2 (← ISPEC a pth)
      let vth ← ISPEC a qth
      let th1 ← ExceptT.mk
        ((← PARTIAL_EXPAND_QUANTS_CONV avoid (← ASSUME (concl vth))) tm)
      let th2 ← CONV_RULE (RAND_CONV (SUBS_CONV (CONJUNCTS cth))) th1
      let th3 ← PROVE_HYP vth th2
      let ths ← TRANSLATION_INVARIANTS a
      let thr := REFL a
      let th4 ← GEN_REWRITE_RULE (RAND_CONV o REDEPTH_CONV)
          [BETA_THM, ← ADD_ASSUM (concl thr) ths] th3
      PROVE_HYP thr th4 : ExceptT String IO thm).run
    pure (GEOM_ORIGIN_CONV, GEOM_TRANSLATE_CONV)

  let GEN_GEOM_ORIGIN_TAC (x : term) (avoid : List String) : tactic := fun gl =>
    let (asl, w) := gl
    let (avs, _bod) := HolCore.Basics.strip_forall w
    let avs' := subtract (frees w) (freesl (asl.map (fun (_, th) => concl th)))
    (MAP_EVERY X_GEN_TAC avs THEN
     MAP_EVERY (fun t => SPEC_TAC (t, t)) (subtract (avs ++ avs') [x]).reverse THEN
     SPEC_TAC (x, x) THEN CONV_TAC (GEOM_ORIGIN_CONV avoid)) gl

  let GEOM_ORIGIN_TAC (x : term) : tactic := GEN_GEOM_ORIGIN_TAC x []

  let GEOM_TRANSLATE_TAC (avoid : List String) : tactic := fun gl => ExceptT.run do
    let (a, bod) ← liftExcept (HolCore.Basics.dest_forall gl.2)
    let n := (HolCore.Basics.strip_forall bod).1.length
    ExceptT.mk ((X_GEN_TAC a THEN
     CONV_TAC (funpow n BINDER_CONV (LAND_CONV (GEOM_TRANSLATE_CONV avoid a))) THEN
     REWRITE_TAC []) gl)

  let EXISTS_GENVAR_RULE : thm → ExceptT String IO thm :=
    let rec rule (vs : List term) (th : thm) : ExceptT String IO thm :=
      match vs with
      | [] => pure th
      | v :: ovs => do
          let (x, bod) ← liftExcept (HolCore.Basics.dest_exists (concl th))
          let th1 ← rule ovs (← ASSUME bod)
          let th2 ← SIMPLE_CHOOSE x (← SIMPLE_EXISTS x th1)
          PROVE_HYP th (← CONV_RULE (fun t => pure (HolCore.Equal.GEN_ALPHA_CONV v t)) th2)
    fun th => do
      rule (← (HolCore.Basics.strip_exists (concl th)).1.mapM
        (fun v => HolCore.Basics.genvar (type_of v))) th

  return { GEOM_ORIGIN_CONV, GEOM_TRANSLATE_CONV, GEN_GEOM_ORIGIN_TAC, GEOM_ORIGIN_TAC,
           GEOM_TRANSLATE_TAC, EXISTS_GENVAR_RULE }

/- ------------------------------------------------------------------------- -/
/- Rotate so that WLOG some point is a +ve multiple of basis vector k.       -/
/- For general N, it's better to use k = 1 so the side-condition can be      -/
/- discharged. For dimensions 1, 2 and 3 anything will work automatically.   -/
/- Could generalize by asking the user to prove theorem 1 <= k <= N.         -/
/- (determinants.ml 4812-4900)                                                -/
/- ------------------------------------------------------------------------- -/

structure GeomBasis where
  GEOM_BASIS_MULTIPLE_RULE : Int → term → ExceptT String IO thm
  GEOM_BASIS_MULTIPLE_TAC : Int → term → tactic
  deriving Inhabited

@[nospecialize]
def setupGeomBasis [HolBase] (D : DeterminantsDeps) (BOrth1 : Orth1)
    (BRotation2 : Rotation2) (BGeomInv : GeomInv) (BGeomOrigin : GeomOrigin) :
    ExceptT String IO GeomBasis := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, EXPAND_QUANTS_CONV, NUM_REDUCE_CONV, SET_RULE,
        mk_small_numeral, .. } := D
  let { DIMINDEX_1, DIMINDEX_2, DIMINDEX_3, DIMINDEX_GE_1, IMAGE_CLAUSES, .. } := D.core1
  let { MONO_FORALL, .. } := D.core2
  let { SURJECTIVE_IMAGE, MAP, .. } := D.core3
  let { BETA_THM, .. } := D.core4
  let { LINEAR_0, .. } := D.vec1
  let { QUANTIFY_SURJECTION_HIGHER_THM, .. } := D.vec2
  let { ORTHOGONAL_TRANSFORMATION, ORTHOGONAL_TRANSFORMATION_INJECTIVE,
        ORTHOGONAL_TRANSFORMATION_LINEAR, ORTHOGONAL_TRANSFORMATION_SURJECTIVE, .. } := BOrth1
  let { ROTATION_RIGHTWARD_LINE, .. } := BRotation2
  let { LINEAR_INVARIANTS, .. } := BGeomInv
  let { EXISTS_GENVAR_RULE, .. } := BGeomOrigin
  -- @@SCOPE END

  let GEOM_BASIS_MULTIPLE_RULE : Int → term → ExceptT String IO thm ← do
    let pth ← prove
     r"!f. orthogonal_transformation (f:real^N->real^N)
         ==> (vec 0 = f(vec 0) /\
              {} = IMAGE f {} /\
              {} = IMAGE (IMAGE f) {} /\
              (:real^N) = IMAGE f (:real^N) /\
              (:real^N->bool) = IMAGE (IMAGE f) (:real^N->bool) /\
              [] = MAP f []) /\
             ((!P. (!x. P x) <=> (!x. P (f x))) /\
              (!P. (?x. P x) <=> (?x. P (f x))) /\
              (!Q. (!s. Q s) <=> (!s. Q (IMAGE f s))) /\
              (!Q. (?s. Q s) <=> (?s. Q (IMAGE f s))) /\
              (!Q. (!s. Q s) <=> (!s. Q (IMAGE (IMAGE f) s))) /\
              (!Q. (?s. Q s) <=> (?s. Q (IMAGE (IMAGE f) s))) /\
              (!P. (!g:real^1->real^N. P g) <=> (!g. P (f o g))) /\
              (!P. (?g:real^1->real^N. P g) <=> (?g. P (f o g))) /\
              (!P. (!g:num->real^N. P g) <=> (!g. P (f o g))) /\
              (!P. (?g:num->real^N. P g) <=> (?g. P (f o g))) /\
              (!Q. (!l. Q l) <=> (!l. Q(MAP f l))) /\
              (!Q. (?l. Q l) <=> (?l. Q(MAP f l)))) /\
             ((!P. {x | P x} = IMAGE f {x | P(f x)}) /\
              (!Q. {s | Q s} = IMAGE (IMAGE f) {s | Q(IMAGE f s)}) /\
              (!R. {l | R l} = IMAGE (MAP f) {l | R(MAP f l)}))"
     (REPEAT GEN_TAC THEN DISCH_TAC THEN
      FIRST_ASSUM (ASSUME_TAC o
            MATCH_MP ORTHOGONAL_TRANSFORMATION_SURJECTIVE) THEN
      CONJ_TAC THENL
       [REWRITE_TAC [IMAGE_CLAUSES, MAP] THEN
        FIRST_ASSUM (ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
        CONJ_TAC THENL [ASM_MESON_TAC [LINEAR_0], ALL_TAC] THEN
        REWRITE_TAC [← SET_RULE (← q r"UNIV = IMAGE f UNIV <=> !y. ?x. f x = y")] THEN
        ASM_REWRITE_TAC [SURJECTIVE_IMAGE],
        MATCH_MP_TAC QUANTIFY_SURJECTION_HIGHER_THM THEN ASM_REWRITE_TAC []])
    let oth ← prove
     r"!f:real^N->real^N.
        orthogonal_transformation f /\
        (2 <= dimindex(:N) ==> det(matrix f) = &1)
        ==> linear f /\
            (!x y. f x = f y ==> x = y) /\
            (!y. ?x. f x = y) /\
            (!x. norm(f x) = norm x) /\
            (2 <= dimindex(:N) ==> det(matrix f) = &1)"
     (GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC [ORTHOGONAL_TRANSFORMATION_LINEAR],
        ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION_INJECTIVE],
        ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION_SURJECTIVE],
        ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION]])
    let arithconv := REWRITE_CONV [DIMINDEX_1, DIMINDEX_2, DIMINDEX_3,
                                   ← ARITH_RULE (← q r"1 <= 1"), DIMINDEX_GE_1] THENC
                     NUM_REDUCE_CONV
    pure (fun k tm => do
      let (x, bod) ← liftExcept (HolCore.Basics.dest_forall tm)
      let th0 ← ISPECL [x, ← liftExcept (mk_small_numeral k)] ROTATION_RIGHTWARD_LINE
      let th1 ← EXISTS_GENVAR_RULE
       (← MP th0 (← EQT_ELIM (← ExceptT.mk (arithconv (← liftExcept (lhand (concl th0)))))))
      let (a, f, tm1) ← match HolCore.Basics.strip_exists (concl th1) with
        | ([a, f], tm1) => pure (a, f, tm1)
        | _ => throw "GEOM_BASIS_MULTIPLE_RULE: match failure"
      let (th_orth, th2) ← CONJ_PAIR (← ASSUME tm1)
      let (th_det, th2a) ← CONJ_PAIR th2
      let (th_works, th_zero) ← CONJ_PAIR th2a
      let (thc, thq) ← CONJ_PAIR (← PROVE_HYP th2 (← UNDISCH (← ISPEC f pth)))
      let th3 ← CONV_RULE (RAND_CONV (SUBS_CONV ((← GSYM th_works) :: CONJUNCTS thc)))
                 (← ExceptT.mk ((← EXPAND_QUANTS_CONV (← ASSUME (concl thq))) bod))
      let th4 ← PROVE_HYP thq th3
      let thps := CONJUNCTS (← MATCH_MP oth (← CONJ th_orth th_det))
      let th5 ← LINEAR_INVARIANTS f thps
      let th6 ← PROVE_HYP th_orth
       (← GEN_REWRITE_RULE (RAND_CONV o REDEPTH_CONV) [BETA_THM, th5] th4)
      let ntm ← liftExcept (HolCore.Bool.mk_forall a
        (← HolCore.Bool.mk_imp (concl th_zero) (← rand (concl th6))))
      let th7 ← MP (← SPEC a (← ASSUME ntm)) th_zero
      let th8 ← DISCH ntm (← HolLight.EQ_MP (← SYM th6) th7)
      if (intersect (frees (concl th8)) [a, f]).isEmpty then
        let th9 ← PROVE_HYP th1 (← itlistIO SIMPLE_CHOOSE [a, f] th8)
        let th10 ← DISCH ntm (← GEN x (← UNDISCH th9))
        let a' ← liftExcept (variant (frees (concl th10))
                  (mk_var (← dest_var x).1 (← dest_var a).2))
        CONV_RULE (LAND_CONV (fun t => pure (HolCore.Equal.GEN_ALPHA_CONV a' t))) th10
      else
        let h ← match hyp th8 with
          | h :: _ => pure h
          | [] => throw "hd"
        let mtm ← liftExcept (HolCore.Bool.list_mk_forall [a, f]
          (← HolCore.Bool.mk_imp h (← rand (concl th6))))
        let th9 ← HolLight.EQ_MP (← SYM th6) (← UNDISCH (← SPECL [a, f] (← ASSUME mtm)))
        let th10 ← itlistIO SIMPLE_CHOOSE [a, f] (← DISCH mtm th9)
        let th11 ← GEN x (← PROVE_HYP th1 th10)
        MATCH_MP MONO_FORALL th11)

  let GEOM_BASIS_MULTIPLE_TAC (k : Int) (l : term) : tactic := fun gl =>
    let (asl, w) := gl
    let (avs, _bod) := HolCore.Basics.strip_forall w
    let avs' := subtract (frees w) (freesl (asl.map (fun (_, th) => concl th)))
    (MAP_EVERY X_GEN_TAC avs THEN
     MAP_EVERY (fun t => SPEC_TAC (t, t)) (subtract (avs ++ avs') [l]).reverse THEN
     SPEC_TAC (l, l) THEN
     W (MATCH_MP_TAC o GEOM_BASIS_MULTIPLE_RULE k o snd)) gl

  return { GEOM_BASIS_MULTIPLE_RULE, GEOM_BASIS_MULTIPLE_TAC }

/- ------------------------------------------------------------------------- -/
/- Create invariance theorems automatically, in simple cases. If there are   -/
/- any nested quantifiers, this will need surjectivity. It's often possible  -/
/- to prove a stronger theorem by more delicate manual reasoning, so this    -/
/- isn't used nearly as often as GEOM_TRANSLATE_CONV / GEOM_TRANSLATE_TAC.   -/
/- As a small step, some ad-hoc rewrites analogous to FORALL_IN_IMAGE are    -/
/- tried if the first step doesn't finish the goal, but it's very ad hoc.    -/
/- (determinants.ml 4911-4968)                                                -/
/- ------------------------------------------------------------------------- -/

structure GeomTransform where
  GEOM_TRANSFORM_TAC : List String → tactic
  deriving Inhabited

@[nospecialize]
def setupGeomTransform [HolBase] (D : DeterminantsDeps) (BOrth1 : Orth1)
    (BGeomInv : GeomInv) : ExceptT String IO GeomTransform := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, PARTIAL_EXPAND_QUANTS_CONV, SET_RULE, SET_TAC, .. } := D
  let { IMAGE_CLAUSES, .. } := D.core1
  let { SURJECTIVE_IMAGE, .. } := D.core3
  let { LINEAR_0, LINEAR_SUB, LINEAR_SURJECTIVE_IFF_INJECTIVE, .. } := D.vec1
  let { NORM_EQ_0, QUANTIFY_SURJECTION_HIGHER_THM, .. } := D.vec2
  let { VECTOR_SUB_EQ, .. } := D.vec3
  let { ORTHOGONAL_TRANSFORMATION, ORTHOGONAL_TRANSFORMATION_INJECTIVE,
        ORTHOGONAL_TRANSFORMATION_SURJECTIVE, .. } := BOrth1
  let { USABLE_CONCLUSION, LINEAR_INVARIANTS, .. } := BGeomInv
  -- @@SCOPE END

  let GEOM_TRANSFORM_TAC : List String → tactic ← do
    let cth0 ← prove
     r"!f:real^M->real^N.
          linear f
          ==> vec 0 = f(vec 0) /\
              {} = IMAGE f {} /\
              {} = IMAGE (IMAGE f) {}"
     (REWRITE_TAC [IMAGE_CLAUSES] THEN MESON_TAC [LINEAR_0])
    let cth1 ← prove
     r"!f:real^M->real^N.
          (!y. ?x. f x = y)
          ==> (:real^N) = IMAGE f (:real^M) /\
              (:real^N->bool) = IMAGE (IMAGE f) (:real^M->bool)"
     (REWRITE_TAC [← SET_RULE (← q r"UNIV = IMAGE f UNIV <=> !y. ?x. f x = y")] THEN
      REWRITE_TAC [SURJECTIVE_IMAGE])
    let sths := CONJUNCTS (← prove
     r"(!f:real^M->real^N.
         linear f /\ (!x. norm(f x) = norm x)
         ==> (!x y. f x = f y ==> x = y)) /\
     (!f:real^N->real^N.
         linear f /\ (!x. norm(f x) = norm x) ==> (!y. ?x. f x = y)) /\
     (!f:real^N->real^N. linear f /\ (!x y. f x = f y ==> x = y)
                         ==> (!y. ?x. f x = y)) /\
     (!f:real^N->real^N. linear f /\ (!y. ?x. f x = y)
                         ==> (!x y. f x = f y ==> x = y))"
     (CONJ_TAC THENL
       [ONCE_REWRITE_TAC [← GSYM VECTOR_SUB_EQ] THEN
        SIMP_TAC [← GSYM LINEAR_SUB, ← GSYM NORM_EQ_0],
        MESON_TAC [ORTHOGONAL_TRANSFORMATION_SURJECTIVE,
                   ORTHOGONAL_TRANSFORMATION_INJECTIVE, ORTHOGONAL_TRANSFORMATION,
                   LINEAR_SURJECTIVE_IFF_INJECTIVE]]))
    let aths := CONJUNCTS (← prove
     r"(!f s P. (!y. y IN IMAGE f s ==> P y) <=> (!x. x IN s ==> P(f x))) /\
     (!f s P. (!u. u IN IMAGE (IMAGE f) s ==> P u) <=>
              (!t. t IN s ==> P(IMAGE f t))) /\
     (!f s P. (?y. y IN IMAGE f s /\ P y) <=> (?x. x IN s /\ P(f x))) /\
     (!f s P. (?u. u IN IMAGE (IMAGE f) s /\ P u) <=>
              (?t. t IN s /\ P(IMAGE f t)))"
     (SET_TAC []))
    pure (fun avoid gl => ExceptT.run do
      let (f, wff) ← liftExcept (HolCore.Basics.dest_forall gl.2)
      let (vs, bod) := HolCore.Basics.strip_forall wff
      let (ant, _cons) ← liftExcept (HolCore.Basics.dest_imp bod)
      let hths := CONJUNCTS (← ASSUME ant)
      let fths := hths ++ (← HolMath.IndTypes.mapfilterM (USABLE_CONCLUSION f hths) sths)
      let cths ← HolMath.IndTypes.mapfilterM (USABLE_CONCLUSION f fths) [cth0, cth1]
      let vconv : ioconv ← tryCatch (do
          let vth ← USABLE_CONCLUSION f fths QUANTIFY_SURJECTION_HIGHER_THM
          let c ← PARTIAL_EXPAND_QUANTS_CONV avoid (← ASSUME (concl vth))
          pure (fun t => (do PROVE_HYP vth (← ExceptT.mk (c t)) :
            ExceptT String IO thm).run))
        (fun _ => pure ALL_CONV)
      let bths ← LINEAR_INVARIANTS f fths
      let aths' ← HolMath.IndTypes.mapfilterM (fun th => do ADD_ASSUM ant (← ISPEC f th)) aths
      ExceptT.mk ((MAP_EVERY X_GEN_TAC (f :: vs) THEN DISCH_TAC THEN
       GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) cths THEN
       CONV_TAC (LAND_CONV vconv) THEN
       GEN_REWRITE_TAC (LAND_CONV o REDEPTH_CONV) [bths] THEN
       REWRITE_TAC [] THEN
       REWRITE_TAC aths' THEN
       GEN_REWRITE_TAC (LAND_CONV o REDEPTH_CONV) [bths] THEN
       REWRITE_TAC []) gl))

  return { GEOM_TRANSFORM_TAC }

/- ------------------------------------------------------------------------- -/
/- Scale so that a chosen vector has size 1. Generates a conjunction of      -/
/- two formulas, one for the zero case (which one hopes is trivial) and      -/
/- one just like the original goal but with a norm(...) = 1 assumption.      -/
/- (determinants.ml 4976-5069)                                                -/
/- ------------------------------------------------------------------------- -/

structure GeomNormalize where
  GEOM_NORMALIZE_RULE : List String → term → ExceptT String IO thm
  GEN_GEOM_NORMALIZE_TAC : term → List String → tactic
  GEOM_NORMALIZE_TAC : term → tactic
  deriving Inhabited

@[nospecialize]
def setupGeomNormalize [HolBase] (D : DeterminantsDeps) (BGeomInv : GeomInv) :
    ExceptT String IO GeomNormalize := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, PARTIAL_EXPAND_QUANTS_CONV, REAL_FIELD, SET_RULE, .. } := D
  let { IMAGE_CLAUSES, .. } := D.core1
  let { REAL_ABS_INV, REAL_MUL_LINV, REAL_MUL_RINV, .. } := D.core2
  let { SURJECTIVE_IMAGE, MAP, .. } := D.core3
  let { BETA_THM, .. } := D.core4
  let { NORM_EQ_0, NORM_MUL, QUANTIFY_SURJECTION_HIGHER_THM, REAL_ABS_NORM, .. } := D.vec2
  let { SURJECTIVE_SCALING, VECTOR_MUL_ASSOC, VECTOR_MUL_LID, VECTOR_MUL_RZERO,
        .. } := D.vec3
  let { SCALING_THEOREMS, .. } := BGeomInv
  -- @@SCOPE END

  let GEOM_NORMALIZE_RULE : List String → term → ExceptT String IO thm ← do
    let pth ← prove
     r"!a:real^N. ~(a = vec 0)
                ==> vec 0 = norm(a) % vec 0 /\
                    a = norm(a) % inv(norm a) % a /\
                    {} = IMAGE (\x. norm(a) % x) {} /\
                    {} = IMAGE (IMAGE (\x. norm(a) % x)) {} /\
                    (:real^N) = IMAGE (\x. norm(a) % x) (:real^N) /\
                    (:real^N->bool) =
                    IMAGE (IMAGE (\x. norm(a) % x)) (:real^N->bool) /\
                    [] = MAP (\x. norm(a) % x) []"
     (REWRITE_TAC [IMAGE_CLAUSES, VECTOR_MUL_ASSOC, VECTOR_MUL_RZERO, MAP] THEN
      SIMP_TAC [NORM_EQ_0, REAL_MUL_RINV, VECTOR_MUL_LID] THEN
      GEN_TAC THEN DISCH_TAC THEN
      REWRITE_TAC [← SET_RULE (← q r"UNIV = IMAGE f UNIV <=> !y. ?x. f x = y")] THEN
      ASM_REWRITE_TAC [SURJECTIVE_IMAGE] THEN
      X_GEN_TAC (← q r"y:real^N") THEN EXISTS_TAC (← q r"inv(norm(a:real^N)) % y:real^N") THEN
      ASM_SIMP_TAC [VECTOR_MUL_ASSOC, NORM_EQ_0, REAL_MUL_RINV, VECTOR_MUL_LID])
    let qth ← prove
     r"!a:real^N.
        ~(a = vec 0)
        ==> ((!P. (!r:real. P r) <=> (!r. P(norm a * r))) /\
             (!P. (?r:real. P r) <=> (?r. P(norm a * r))) /\
             (!P. (!x:real^N. P x) <=> (!x. P (norm(a) % x))) /\
             (!P. (?x:real^N. P x) <=> (?x. P (norm(a) % x))) /\
             (!Q. (!s:real^N->bool. Q s) <=>
                  (!s. Q(IMAGE (\x. norm(a) % x) s))) /\
             (!Q. (?s:real^N->bool. Q s) <=>
                  (?s. Q(IMAGE (\x. norm(a) % x) s))) /\
             (!Q. (!s:(real^N->bool)->bool. Q s) <=>
                  (!s. Q(IMAGE (IMAGE (\x. norm(a) % x)) s))) /\
             (!Q. (?s:(real^N->bool)->bool. Q s) <=>
                  (?s. Q(IMAGE (IMAGE (\x. norm(a) % x)) s))) /\
             (!P. (!g:real^1->real^N. P g) <=>
                  (!g. P ((\x. norm(a) % x) o g))) /\
             (!P. (?g:real^1->real^N. P g) <=>
                  (?g. P ((\x. norm(a) % x) o g))) /\
             (!P. (!g:num->real^N. P g) <=>
                  (!g. P ((\x. norm(a) % x) o g))) /\
             (!P. (?g:num->real^N. P g) <=>
                  (?g. P ((\x. norm(a) % x) o g))) /\
             (!Q. (!l. Q l) <=> (!l. Q(MAP (\x:real^N. norm(a) % x) l))) /\
             (!Q. (?l. Q l) <=> (?l. Q(MAP (\x:real^N. norm(a) % x) l)))) /\
            ((!P. {x:real^N | P x} =
                  IMAGE (\x. norm(a) % x) {x | P(norm(a) % x)}) /\
             (!Q. {s:real^N->bool | Q s} =
                  IMAGE (IMAGE (\x. norm(a) % x))
                       {s | Q(IMAGE (\x. norm(a) % x) s)}) /\
             (!R. {l:(real^N)list | R l} =
                  IMAGE (MAP (\x:real^N. norm(a) % x))
                        {l | R(MAP (\x:real^N. norm(a) % x) l)}))"
     (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC (← TAUT (← q
       r"(a /\ b) /\ c /\ d ==> (a /\ b /\ c) /\ d")) THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC [NORM_EQ_0, ← REAL_FIELD (← q r"~(x = &0) ==> x * inv x * a = a")],
        MP_TAC (← ISPEC (← q r"\x:real^N. norm(a:real^N) % x")
          (← HolLight.INST_TYPE [(← qty "real^1", ← qty "C")]
            QUANTIFY_SURJECTION_HIGHER_THM)) THEN
        ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_SIMP_TAC [SURJECTIVE_SCALING, NORM_EQ_0]])
    let lth ← prove
     r"(!b:real^N. ~(b = vec 0) ==> (P(b) <=> Q(inv(norm b) % b)))
     ==> P(vec 0) /\ (!b. norm(b) = &1 ==> Q b) ==> (!b. P b)"
     (REPEAT STRIP_TAC THEN
      ASM_CASES_TAC (← q r"b:real^N = vec 0") THEN ASM_SIMP_TAC [] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC [NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM,
                    REAL_MUL_LINV, NORM_EQ_0])
    pure (fun avoid tm => do
      let (x, tm0) ← liftExcept (HolCore.Basics.dest_forall tm)
      let cth ← UNDISCH (← ISPEC x pth)
      let vth ← UNDISCH (← ISPEC x qth)
      let th1 ← ExceptT.mk (ONCE_REWRITE_CONV [cth] tm0)
      let th2 ← CONV_RULE (RAND_CONV
       (← PARTIAL_EXPAND_QUANTS_CONV avoid vth)) th1
      let th3 ← SCALING_THEOREMS x
      let th3' ← end_itlist CONJ (← (CONJUNCTS th3).mapM
         (fun th => do
            let (avs, _) := HolCore.Basics.strip_forall (concl th)
            let gvs ← avs.mapM (fun v => HolCore.Basics.genvar (type_of v))
            GENL gvs (← SPECL gvs th)))
      let th4 ← GEN_REWRITE_RULE (RAND_CONV o REDEPTH_CONV)
                 [BETA_THM, th3'] th2
      MATCH_MP lth (← GEN x (← DISCH_ALL th4)))

  let GEN_GEOM_NORMALIZE_TAC (x : term) (avoid : List String) : tactic := fun gl =>
    let (asl, w) := gl
    let (avs, _bod) := HolCore.Basics.strip_forall w
    let avs' := subtract (frees w) (freesl (asl.map (fun (_, th) => concl th)))
    (MAP_EVERY X_GEN_TAC avs THEN
     MAP_EVERY (fun t => SPEC_TAC (t, t)) (subtract (avs ++ avs') [x]).reverse THEN
     SPEC_TAC (x, x) THEN
     W (MATCH_MP_TAC o GEOM_NORMALIZE_RULE avoid o snd)) gl

  let GEOM_NORMALIZE_TAC (x : term) : tactic := GEN_GEOM_NORMALIZE_TAC x []

  return { GEOM_NORMALIZE_RULE, GEN_GEOM_NORMALIZE_TAC, GEOM_NORMALIZE_TAC }

/- ------------------------------------------------------------------------- -/
/- Add invariance theorems for collinearity.  (determinants.ml 5076-5096)    -/
/- ------------------------------------------------------------------------- -/

structure Collinear where
  COLLINEAR_TRANSLATION_EQ : thm
  COLLINEAR_TRANSLATION : thm
  COLLINEAR_LINEAR_IMAGE : thm
  COLLINEAR_LINEAR_IMAGE_EQ : thm
  deriving Inhabited

@[nospecialize]
def setupCollinear [HolBase] (D : DeterminantsDeps) (BGeomOrigin : GeomOrigin) :
    ExceptT String IO Collinear := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, LINEAR_INVARIANT_RULE, add_linear_invariants,
        add_translation_invariants, .. } := D
  let { FORALL_IN_IMAGE, IMP_CONJ, .. } := D.core1
  let { RIGHT_FORALL_IMP_THM, .. } := D.core3
  let { LINEAR_CMUL, LINEAR_SUB, .. } := D.vec1
  let { collinear, .. } := D.vec3
  let { GEOM_TRANSLATE_TAC, .. } := BGeomOrigin
  -- @@SCOPE END

  let COLLINEAR_TRANSLATION_EQ ← prove
   r"!a s. collinear (IMAGE (\x. a + x) s) <=> collinear s"
   (REWRITE_TAC [collinear] THEN GEOM_TRANSLATE_TAC ["u"])

  add_translation_invariants [COLLINEAR_TRANSLATION_EQ]

  let COLLINEAR_TRANSLATION ← prove
   r"!s a. collinear s ==> collinear (IMAGE (\x. a + x) s)"
   (REWRITE_TAC [COLLINEAR_TRANSLATION_EQ])

  let COLLINEAR_LINEAR_IMAGE ← prove
   r"!f s. collinear s /\ linear f ==> collinear(IMAGE f s)"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC [collinear, IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC [LINEAR_SUB, LINEAR_CMUL])

  let COLLINEAR_LINEAR_IMAGE_EQ ← prove
   r"!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (collinear (IMAGE f s) <=> collinear s)"
   (MATCH_ACCEPT_TAC (← LINEAR_INVARIANT_RULE COLLINEAR_LINEAR_IMAGE))

  add_linear_invariants [COLLINEAR_LINEAR_IMAGE_EQ]

  return { COLLINEAR_TRANSLATION_EQ, COLLINEAR_TRANSLATION, COLLINEAR_LINEAR_IMAGE,
           COLLINEAR_LINEAR_IMAGE_EQ }

/- ------------------------------------------------------------------------- -/
/- Take a theorem "th" with outer universal quantifiers involving real^N     -/
/- and a theorem "dth" asserting |- dimindex(:M) <= dimindex(:N) and         -/
/- return a theorem replacing type :N by :M in th. Neither N or M need be a  -/
/- type variable.  Then transfer theorems automatically between              -/
/- same-dimension spaces: given dth = A |- dimindex(:M) = dimindex(:N) and a -/
/- theorem th involving variables of type real^N, return a corresponding     -/
/- theorem mapped to type real^M with assumptions A.                         -/
/- (determinants.ml 5105-5208)                                                -/
/- ------------------------------------------------------------------------- -/

structure GeomDim where
  GEOM_DROP_DIMENSION_RULE : thm → thm → ExceptT String IO thm
  GEOM_EQUAL_DIMENSION_RULE : thm → thm → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupGeomDim [HolBase] (D : DeterminantsDeps) (BGeomInv : GeomInv)
    (BGeomOrigin : GeomOrigin) : ExceptT String IO GeomDim := do
  -- @@SCOPE BEGIN
  let { EXPAND_QUANTS_CONV, MESON_TAC, SET_RULE, .. } := D
  let { CONJ_ASSOC, IMAGE_CLAUSES, LEFT_FORALL_IMP_THM, .. } := D.core1
  let { SURJECTIVE_IMAGE, MAP, .. } := D.core3
  let { BETA_THM, MONO_AND, .. } := D.core4
  let { DIM_UNIV, ISOMETRY_UNIV_SUBSPACE, ISOMETRY_UNIV_UNIV, LINEAR_0, .. } := D.vec1
  let { PRESERVES_NORM_INJECTIVE, QUANTIFY_SURJECTION_HIGHER_THM, .. } := D.vec2
  let { SUBSPACE_UNIV, .. } := D.vec3
  let { LINEAR_INVARIANTS, .. } := BGeomInv
  let { EXISTS_GENVAR_RULE, .. } := BGeomOrigin
  -- @@SCOPE END

  let GEOM_DROP_DIMENSION_RULE : thm → thm → ExceptT String IO thm ← do
    let oth ← prove
     r"!f:real^M->real^N.
          linear f /\ (!x. norm(f x) = norm x)
          ==> linear f /\
              (!x y. f x = f y ==> x = y) /\
              (!x. norm(f x) = norm x)"
     (MESON_TAC [PRESERVES_NORM_INJECTIVE])
    let cth ← prove
     r"linear(f:real^M->real^N)
     ==> vec 0 = f(vec 0) /\
         {} = IMAGE f {} /\
         {} = IMAGE (IMAGE f) {} /\
         [] = MAP f []"
     (REWRITE_TAC [IMAGE_CLAUSES, MAP, ← GSYM LINEAR_0])
    pure (fun dth th => do
      let ath ← GEN_ALL th
      let eth ← MATCH_MP ISOMETRY_UNIV_UNIV dth
      let avoid ← liftExcept (HolCore.Basics.variables (concl th))
      let (f, bod) ← liftExcept (HolCore.Basics.dest_exists (concl eth))
      let fimage ← ExceptT.mk (HolCore.Basics.list_mk_icomb "IMAGE" [f])
      let fmap ← ExceptT.mk (HolCore.Basics.list_mk_icomb "MAP" [f])
      let fcompose ← ExceptT.mk (HolCore.Basics.list_mk_icomb "o" [f])
      let fimage2 ← ExceptT.mk (HolCore.Basics.list_mk_icomb "IMAGE" [fimage])
      let (lin, _iso) ← CONJ_PAIR (← ASSUME bod)
      let olduniv ← liftExcept (do rand (← rand (concl dth)))
      let newuniv ← liftExcept (do rand (← lhand (concl dth)))
      let oldty := (← liftExcept (HolCore.Basics.dest_fun_ty (type_of olduniv))).1
      let newty := (← liftExcept (HolCore.Basics.dest_fun_ty (type_of newuniv))).1
      let newvar (v : term) : ExceptT String IO term := do
        let (n, t) ← liftExcept (dest_var v)
        liftExcept (variant avoid (mk_var n (← HolCore.Basics.tysubst [(newty, oldty)] t)))
      let newterm (v : term) : ExceptT String IO term :=
        tryCatch (do
          let v' ← newvar v
          liftExcept (tryfind (fun f => mk_comb f v') [f, fimage, fmap, fcompose, fimage2]))
          (fun _ => pure v)
      let specrule (th : thm) : ExceptT String IO thm := do
        let v := (← liftExcept (HolCore.Basics.dest_forall (concl th))).1
        SPEC (← newterm v) th
      let sth ← SUBS (CONJUNCTS (← MATCH_MP cth lin)) ath
      let fth ← SUBS [← SYM (← MATCH_MP LINEAR_0 lin)] (← repeatIO specrule sth)
      let thps := CONJUNCTS (← MATCH_MP oth (← ASSUME bod))
      let th5 ← LINEAR_INVARIANTS f thps
      let th6 ← GEN_REWRITE_RULE REDEPTH_CONV [th5] fth
      let th7 ← PROVE_HYP eth (← SIMPLE_CHOOSE f th6)
      GENL (← (HolCore.Basics.strip_forall (concl ath)).1.mapM newvar) th7)

  let GEOM_EQUAL_DIMENSION_RULE : thm → thm → ExceptT String IO thm ← do
    let bth ← prove
     r"dimindex(:M) = dimindex(:N)
     ==> ?f:real^M->real^N.
             (linear f /\ (!y. ?x. f x = y)) /\
             (!x. norm(f x) = norm x)"
     (REWRITE_TAC [← SET_RULE (← q r"(!y. ?x. f x = y) <=> IMAGE f UNIV = UNIV")] THEN
      DISCH_TAC THEN REWRITE_TAC [← GSYM CONJ_ASSOC] THEN
      MATCH_MP_TAC ISOMETRY_UNIV_SUBSPACE THEN
      REWRITE_TAC [SUBSPACE_UNIV, DIM_UNIV] THEN FIRST_ASSUM ACCEPT_TAC)
    let pth ← prove
     r"!f:real^M->real^N.
        linear f /\ (!y. ?x. f x = y)
         ==> (vec 0 = f(vec 0) /\
              {} = IMAGE f {} /\
              {} = IMAGE (IMAGE f) {} /\
              (:real^N) = IMAGE f (:real^M) /\
              (:real^N->bool) = IMAGE (IMAGE f) (:real^M->bool) /\
              [] = MAP f []) /\
             ((!P. (!x. P x) <=> (!x. P (f x))) /\
              (!P. (?x. P x) <=> (?x. P (f x))) /\
              (!Q. (!s. Q s) <=> (!s. Q (IMAGE f s))) /\
              (!Q. (?s. Q s) <=> (?s. Q (IMAGE f s))) /\
              (!Q. (!s. Q s) <=> (!s. Q (IMAGE (IMAGE f) s))) /\
              (!Q. (?s. Q s) <=> (?s. Q (IMAGE (IMAGE f) s))) /\
              (!P. (!g:real^1->real^N. P g) <=> (!g. P (f o g))) /\
              (!P. (?g:real^1->real^N. P g) <=> (?g. P (f o g))) /\
              (!P. (!g:num->real^N. P g) <=> (!g. P (f o g))) /\
              (!P. (?g:num->real^N. P g) <=> (?g. P (f o g))) /\
              (!Q. (!l. Q l) <=> (!l. Q(MAP f l))) /\
              (!Q. (?l. Q l) <=> (?l. Q(MAP f l)))) /\
             ((!P. {x | P x} = IMAGE f {x | P(f x)}) /\
              (!Q. {s | Q s} = IMAGE (IMAGE f) {s | Q(IMAGE f s)}) /\
              (!R. {l | R l} = IMAGE (MAP f) {l | R(MAP f l)}))"
     (GEN_TAC THEN
      SIMP_TAC [← SET_RULE (← q r"UNIV = IMAGE f UNIV <=> (!y. ?x. f x = y)"),
                SURJECTIVE_IMAGE] THEN
      MATCH_MP_TAC MONO_AND THEN
      REWRITE_TAC [QUANTIFY_SURJECTION_HIGHER_THM] THEN
      REWRITE_TAC [IMAGE_CLAUSES, MAP] THEN MESON_TAC [LINEAR_0])
    pure (fun dth th => do
      let eth ← EXISTS_GENVAR_RULE (← MATCH_MP bth dth)
      let (f, bod) ← liftExcept (HolCore.Basics.dest_exists (concl eth))
      let (lsth, neth) ← CONJ_PAIR (← ASSUME bod)
      let (cth, qth) ← CONJ_PAIR (← MATCH_MP pth lsth)
      let th1 ← CONV_RULE
       ((← EXPAND_QUANTS_CONV qth) THENC SUBS_CONV (CONJUNCTS cth)) th
      let ith ← LINEAR_INVARIANTS f (neth :: CONJUNCTS lsth)
      let th2 ← GEN_REWRITE_RULE (RAND_CONV o REDEPTH_CONV) [BETA_THM, ith] th1
      let th3 ← GEN f (← DISCH bod th2)
      MP (← CONV_RULE (REWR_CONV LEFT_FORALL_IMP_THM) th3) eth)

  return { GEOM_DROP_DIMENSION_RULE, GEOM_EQUAL_DIMENSION_RULE }

end HolMultiLib.Determinants
