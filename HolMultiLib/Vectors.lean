/- ========================================================================= -/
/- Real vectors in Euclidean space, and elementary linear algebra.           -/
/- ========================================================================= -/
/- File: HolMultiLib/Vectors.lean

  Original (c) Copyright, John Harrison 1998-2008
  Original (c) Copyright, Marco Maggesi 2014
  Original (c) Copyright, Andrea Gabrielli, Marco Maggesi 2016-2017
  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/vectors.ml`, in the style of
  HolMultiLib/Misc.lean: pure, the proofs translated by hand, one `let` per
  OCaml `let`, in file order.  What vectors.ml uses from the core library,
  from Multivariate/misc.ml, Library/matroids.ml, Library/card.ml and
  Library/floor.ml is passed in `VectorsDeps`; SessionMultiLib/Vectors.lean
  supplies it.

  vectors.ml's `needs "Library/matroids.ml"` and `needs "Multivariate/misc.ml"`
  are the wiring's imports.  Its load-time effects (overloads, infixes,
  `prioritize_real`, `extend_basic_congs`, the invariance tables) are made
  inside the bundles at their file positions.
-/

import HolMath

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolMultiLib.Vectors

set_option maxHeartbeats 4000000

/- ------------------------------------------------------------------------- -/
/- What vectors.ml uses from the core library (supplied by Session).         -/
/- (Five structures, each under 128 fields.)                                  -/
/- ------------------------------------------------------------------------- -/

/-- Core theorems, ADD1 to FORALL_IN_INSERT. -/
structure CoreThms1 where
  (ADD1 ADD_0 ADD_CLAUSES ADD_SUB ADD_SUC ADD_SYM AND_FORALL_THM ARITH ARITH_EQ
   BIJECTIVE_LEFT_RIGHT_INVERSE CARD_CLAUSES CARD_DELETE CARD_DIFF
   CARD_EQ_BIJECTIONS CARD_IMAGE_INJ CARD_IMAGE_LE CARD_LE_INJ CARD_NUMSEG
   CARD_NUMSEG_1 CARD_SUBSET CARD_UNION CARD_UNION_GEN CARD_UNION_LE CART_EQ
   CART_EQ_FULL COND_ID COND_RAND COND_RATOR CONJ_ACI CONJ_ASSOC CONJ_SYM
   CONTRAPOS_THM CROSS DECIMAL DELETE DELETE_INSERT DELETE_SUBSET DE_MORGAN_THM
   DIFF DIMINDEX_1 DIMINDEX_2 DIMINDEX_3 DIMINDEX_4 DIMINDEX_FINITE_PROD
   DIMINDEX_FINITE_SUM DIMINDEX_GE_1 DIMINDEX_NONZERO DISJOINT DISJOINT_NUMSEG
   EMPTY_SUBSET EQ_ADD_LCANCEL EQ_ADD_RCANCEL EQ_IMP EQ_IMP_LE EQ_SYM_EQ EQ_TRANS
   ETA_AX EXISTS_FINITE_SUBSET_IMAGE EXISTS_IN_IMAGE EXISTS_IN_INSERT
   EXISTS_PAIRED_THM EXISTS_PASTECART EXISTS_REFL EXISTS_UNIQUE_DEF EXTENSION
   FINITE_CROSS FINITE_DELETE FINITE_DIFF FINITE_EMPTY FINITE_IMAGE
   FINITE_IMAGE_INJ FINITE_IMAGE_INJ_EQ FINITE_INDEX_INRANGE
   FINITE_INDEX_INRANGE_2 FINITE_INDEX_WORKS FINITE_INDUCT_STRONG FINITE_INSERT
   FINITE_INTER FINITE_NUMSEG FINITE_PRODUCT_DEPENDENT FINITE_RESTRICT
   FINITE_RULES FINITE_SUBSET FINITE_SUBSET_IMAGE FINITE_UNION FINITE_UNIONS
   FORALL_AND_THM FORALL_IN_GSPEC FORALL_IN_IMAGE FORALL_IN_INSERT : thm)
  deriving Inhabited

/-- Core theorems, FORALL_IN_PCROSS to PAIRWISE_EMPTY. -/
structure CoreThms2 where
  (FORALL_IN_PCROSS FORALL_PAIRED_THM FORALL_PAIR_THM FST FSTCART_COMPONENT
   FSTCART_PASTECART FUN_EQ_THM FUN_IN_IMAGE GT HAS_SIZE HAS_SIZE_IMAGE_INJ
   HAS_SIZE_NUMSEG_1 IMAGE_CLAUSES IMAGE_EQ IMAGE_EQ_EMPTY IMAGE_ID
   IMAGE_INJECTIVE_IMAGE_OF_SUBSET IMAGE_SUBSET IMAGE_UNIONS IMAGE_o IMP_CONJ
   IMP_CONJ_ALT IMP_IMP IN INFINITE INJECTIVE_IMAGE INJECTIVE_LEFT_INVERSE
   INJECTIVE_ON_ALT INJECTIVE_ON_LEFT_INVERSE INSERT_AC INSERT_DELETE
   INSERT_SUBSET INTERSECTION_OF INTERS_IMAGE INTER_COMM INTER_SUBSET INTER_UNIV
   IN_CROSS IN_DELETE IN_DIFF IN_ELIM_PAIR_THM IN_ELIM_THM IN_IMAGE IN_INSERT
   IN_INTER IN_INTERS IN_NUMSEG IN_SING IN_UNION IN_UNIONS IN_UNIV
   ITERATE_CLAUSES ITERATE_REFLECT I_DEF I_O_ID I_THM LAMBDA_BETA LAMBDA_ETA LE
   LEFT_AND_EXISTS_THM LEFT_AND_FORALL_THM LEFT_FORALL_IMP_THM
   LEFT_IMP_EXISTS_THM LEFT_OR_DISTRIB LE_0 LE_1 LE_ADD2 LE_ANTISYM LE_REFL
   LE_TRANS LT_LE LT_REFL MEMBER_NOT_EMPTY MONO_AND MONO_EXISTS MONO_FORALL
   MONO_IMP NOT_EXISTS_THM NOT_FORALL_THM NOT_IMP NOT_IN_EMPTY NOT_LE NOT_LT
   NUMSEG_CLAUSES NUMSEG_EMPTY NUMSEG_OFFSET_IMAGE NUMSEG_REC NUMSEG_SING ONE
   PAIRWISE_EMPTY : thm)
  deriving Inhabited

/-- Core theorems, PAIRWISE_INSERT to REAL_MUL_RINV. -/
structure CoreThms3 where
  (PAIRWISE_INSERT PAIRWISE_MONO PAIRWISE_SING PAIR_EQ PASTECART_EQ
   PASTECART_FST_SND PASTECART_INJ PASTECART_IN_PCROSS PCROSS PCROSS_EMPTY
   PCROSS_MONO POW_2_SQRT_ABS PSUBSET PSUBSET_ALT REAL_ABS_0 REAL_ABS_DIV
   REAL_ABS_INV REAL_ABS_MUL REAL_ABS_NEG REAL_ABS_NUM REAL_ABS_NZ REAL_ABS_POS
   REAL_ABS_POW REAL_ABS_REFL REAL_ABS_SUB REAL_ABS_ZERO REAL_ADD_AC
   REAL_ADD_ASSOC REAL_ADD_LDISTRIB REAL_ADD_LID REAL_ADD_RDISTRIB REAL_ADD_RID
   REAL_DIV_LMUL REAL_DIV_RMUL REAL_ENTIRE REAL_EQ_ADD_LCANCEL_0
   REAL_EQ_LCANCEL_IMP REAL_EQ_MUL_RCANCEL REAL_EQ_SQUARE_ABS REAL_INV_0
   REAL_INV_1 REAL_INV_EQ_0 REAL_INV_EQ_1 REAL_LET_TRANS REAL_LE_ADD
   REAL_LE_ADD2 REAL_LE_ADDL REAL_LE_ADDR REAL_LE_ANTISYM REAL_LE_DIV
   REAL_LE_LADD REAL_LE_LDIV_EQ REAL_LE_LMUL REAL_LE_LMUL_EQ REAL_LE_LSQRT
   REAL_LE_MIN REAL_LE_MUL REAL_LE_MUL2 REAL_LE_NEG2 REAL_LE_POW_2
   REAL_LE_RDIV_EQ REAL_LE_REFL REAL_LE_RMUL REAL_LE_RSQRT REAL_LE_SQUARE
   REAL_LE_SQUARE_ABS REAL_LE_SUB_RADD REAL_LE_SUP_FINITE REAL_LE_TOTAL
   REAL_LE_TRANS REAL_LT_ANTISYM REAL_LT_DIV REAL_LT_IMP_LE REAL_LT_IMP_NZ
   REAL_LT_INV_EQ REAL_LT_LE REAL_LT_LMUL_EQ REAL_LT_MUL REAL_LT_NEG2
   REAL_LT_REFL REAL_LT_TRANS REAL_MAX_LE REAL_MUL_AC REAL_MUL_ASSOC
   REAL_MUL_LID REAL_MUL_LINV REAL_MUL_LNEG REAL_MUL_LZERO REAL_MUL_RID
   REAL_MUL_RINV : thm)
  deriving Inhabited

/-- Core theorems, REAL_MUL_RNEG to SUM_GROUP. -/
structure CoreThms4 where
  (REAL_MUL_RNEG REAL_MUL_RZERO REAL_MUL_SYM REAL_NEG_EQ_0 REAL_NEG_NEG
   REAL_NOT_LE REAL_NOT_LT REAL_OF_NUM_ADD REAL_OF_NUM_EQ REAL_OF_NUM_LT
   REAL_OF_NUM_SUC REAL_POS REAL_POW2_ABS REAL_POW_2 REAL_POW_LE2 REAL_POW_LT
   REAL_POW_MUL REAL_RSQRT_LE REAL_SQRT_POW_2 REAL_SUB_0 REAL_SUB_LDISTRIB
   REAL_SUB_LE REAL_SUB_RDISTRIB REAL_SUB_REFL REAL_SUB_RZERO
   REAL_SUP_LE_FINITE REAL_SUP_UNIQUE REAL_WLOG_LE RIGHT_AND_EXISTS_THM
   RIGHT_EXISTS_AND_THM RIGHT_FORALL_IMP_THM RIGHT_IMP_EXISTS_THM
   RIGHT_IMP_FORALL_THM SELECT_UNIQUE SIMPLE_IMAGE SIMPLE_IMAGE_GEN SING_SUBSET
   SKOLEM_THM SND SNDCART_COMPONENT SNDCART_PASTECART SQRT_0 SQRT_1 SQRT_EQ_0
   SQRT_INJ SQRT_LT_0 SQRT_MONO_LE_EQ SQRT_MONO_LT_EQ SQRT_MUL SQRT_POS_LE
   SQRT_POW2 SQRT_POW_2 SUBSET SUBSET_ANTISYM SUBSET_ANTISYM_EQ SUBSET_DIFF
   SUBSET_IMAGE SUBSET_INTER SUBSET_REFL SUBSET_TRANS SUBSET_UNION SUBSET_UNIV
   SUB_ADD SUC_INJ SUC_SUB1 SUM_0 SUM_ABS_NUMSEG SUM_ADD SUM_ADD_GEN
   SUM_ADD_NUMSEG SUM_ADD_SPLIT SUM_BOUND SUM_CASES SUM_CLAUSES SUM_CLAUSES_LEFT
   SUM_CLAUSES_NUMSEG SUM_COMBINE_L SUM_COMBINE_R SUM_CONST SUM_CONST_NUMSEG
   SUM_DELETE SUM_DELTA SUM_DIFF SUM_EQ SUM_EQ_0 SUM_EQ_0_NUMSEG SUM_EQ_GENERAL
   SUM_EQ_GENERAL_INVERSES SUM_EQ_NUMSEG SUM_GROUP : thm)
  deriving Inhabited

/-- Core theorems, SUM_GROUP_RELATION to vector, and the lists.ml theorems
    (held in Session's list bundles). -/
structure CoreThms5 where
  (SUM_GROUP_RELATION SUM_IMAGE SUM_IMAGE_GEN SUM_INCL_EXCL SUM_INJECTION
   SUM_LE SUM_LE_NUMSEG SUM_LMUL SUM_NEG SUM_OFFSET SUM_OFFSET_0 SUM_PAIR
   SUM_POS_EQ_0_NUMSEG SUM_POS_LE SUM_POS_LE_NUMSEG SUM_RESTRICT_SET SUM_RMUL
   SUM_SING_NUMSEG SUM_SUB SUM_SUB_NUMSEG SUM_SUM_PRODUCT SUM_SUPERSET SUM_SWAP
   SUM_SWAP_NUMSEG SUM_TRIV_NUMSEG SUM_UNION SUM_UNION_EQ SUM_UNION_NONZERO SUP
   SUP_EQ SUP_FINITE SUP_SING SURJECTIVE_EXISTS_THM SURJECTIVE_FORALL_THM
   SURJECTIVE_IFF_INJECTIVE_GEN SURJECTIVE_IMAGE SURJECTIVE_IMAGE_EQ
   SURJECTIVE_IMAGE_THM SURJECTIVE_RIGHT_INVERSE SWAP_EXISTS_THM
   SWAP_FORALL_THM UNIONS_0 UNIONS_IMAGE UNIONS_INSERT UNION_EMPTY UNION_OF
   UNION_SUBSET UNIV_NOT_EMPTY UNIV_SUBSET UNWIND_THM1 finite_index fstcart
   is_int monoidal neutral num_INFINITE numseg o_ASSOC o_DEF o_THM pairwise
   pastecart real_abs real_div real_ge real_gt real_min real_sub sndcart
   support vector
   EL HD LENGTH MAP TL LENGTH_MAP MAP_APPEND MAP_REVERSE MEM_MAP
   SURJECTIVE_MAP : thm)
  deriving Inhabited

/-- What vectors.ml uses from Multivariate/misc.ml. -/
structure MiscThms where
  (HULL_HULL HULL_MINIMAL HULL_MONO HULL_SUBSET HULL_UNION HULL_UNION_SUBSET
   HULL_UNIQUE LAMBDA_SKOLEM MATRIFY_VECTORIZE P_HULL REAL_HALF REAL_LE_BETWEEN
   REAL_LT_BETWEEN TRIANGLE_LEMMA VECTORIZE_COMPONENT VECTORIZE_MATRIFY matrify
   vectorize : thm)
  deriving Inhabited

/-- What vectors.ml uses from Library/matroids.ml, card.ml and floor.ml. -/
structure LibThms where
  (MATROID_BASIS_SUBMATROID MATROID_CHOOSE_SUBSPACE MATROID_DIMENSION_UNIQUE
   MATROID_DIM_ALT MATROID_DIM_EMPTY MATROID_DIM_EQ_SPAN
   MATROID_DIM_GE_FINITE_CARD_EQ MATROID_DIM_INSERT MATROID_DIM_SPAN
   MATROID_DIM_SPAN_EQ_GEN MATROID_FINITE_DIMENSIONAL
   MATROID_FINITE_DIMENSIONAL_DIM MATROID_INDEPENDENT_INSERT
   MATROID_INDEPENDENT_SUBMATROID MATROID_INTERMEDIATE_BASIS
   MATROID_LOWDIM_EXPAND_BASIS MATROID_LOWDIM_EXPAND_DIMENSION
   MATROID_SPANNING_SUBMATROID MATROID_SPANNING_SUBSET_INDEPENDENT
   MATROID_SPAN_EQ MATROID_SPAN_INSERT_EQ MATROID_STEINITZ_EXCHANGE_FINITE
   SUBMATROID_SUBSET matroid_basis matroid_independent matroid_set
   matroid_span matroid_spanning matroid_subspace matroid_tybij
   COUNTABLE_IMAGE COUNTABLE_IMAGE_INJ_EQ
   RATIONAL_APPROXIMATION RATIONAL_BETWEEN rational : thm)
  deriving Inhabited

/-- What vectors.ml uses from the core library's procedures and parser. -/
structure VectorsDeps where
  -- definitions and parser state
  new_definition : String → ExceptT String IO thm
  define : String → ExceptT String IO thm
  parse_as_infix : String × (Int × String) → IO Unit
  make_overloadable : String → hol_type → ExceptT String IO Unit
  overload_interface : String → term → ExceptT String IO Unit
  override_interface : String → term → ExceptT String IO Unit
  prioritize_overload : hol_type → IO Unit
  prioritize_real : IO Unit
  extend_basic_congs : List thm → IO Unit
  prove_inductive_relations_exist : term → ExceptT String IO thm
  -- decision procedures
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  ASM_MESON_TAC : List thm → tactic
  ASM_REAL_ARITH_TAC : tactic
  INDUCT_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  METIS_TAC : List thm → tactic
  REAL_ARITH : term → ExceptT String IO thm
  REAL_ARITH_TAC : tactic
  REAL_FIELD : term → ExceptT String IO thm
  REAL_RING : term → ExceptT String IO thm
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  -- the real-arithmetic kernel NORM_ARITH is built on
  GEN_REAL_ARITH : HolMath.RealArith.PsProver → term → ExceptT String IO thm
  REAL_LINEAR_PROVER : HolMath.RealArith.PsProver
  GEN_NNF_CONV : Bool → ioconv → HolCore.Canon.dconv → ioconv
  term_of_rat : Rat → Except String term
  -- simplifier
  GEN_SIMPLIFY_CONV : HolCore.Simp.strategy → HolCore.Simp.simpset → Int → List thm →
    IO (Except String ioconv)
  TOP_DEPTH_SQCONV : HolCore.Simp.strategy
  basic_ss : List thm → IO (Except String HolCore.Simp.simpset)
  -- conversions
  HAS_SIZE_CONV : ioconv
  NUM_ADD_CONV : ioconv
  NUM_LE_CONV : ioconv
  NUM_LT_CONV : ioconv
  NUM_REDUCE_CONV : ioconv
  REAL_POLY_CONV : ioconv
  REAL_POLY_NEG_CONV : ioconv
  REAL_RAT_ADD_CONV : ioconv
  REAL_RAT_MUL_CONV : ioconv
  REAL_RAT_REDUCE_CONV : ioconv
  SELECT_CONV : ioconv
  num_CONV : ioconv
  -- theorems
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3
  core4 : CoreThms4
  core5 : CoreThms5
  misc : MiscThms
  lib : LibThms

/- ------------------------------------------------------------------------- -/
/- Some common special cases; basic componentwise operations on vectors;    -/
/- scalar multiplication, `vec` and dot products.  (vectors.ml 16-117)       -/
/- ------------------------------------------------------------------------- -/

structure Basics where
  FORALL_1 : thm
  FORALL_2 : thm
  FORALL_3 : thm
  FORALL_4 : thm
  SUM_1 : thm
  SUM_2 : thm
  SUM_3 : thm
  SUM_4 : thm
  vector_add : thm
  vector_sub : thm
  vector_neg : thm
  prioritize_vector : IO Unit
  vector_mul : thm
  vec : thm
  dot : thm
  DOT_1 : thm
  DOT_2 : thm
  DOT_3 : thm
  DOT_4 : thm
  deriving Inhabited

@[nospecialize]
def setupBasics [HolBase] (D : VectorsDeps) : ExceptT String IO Basics := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, MESON_TAC, new_definition, num_CONV, overload_interface,
        parse_as_infix, prioritize_overload, prioritize_real, .. } := D
  let { ARITH, DIMINDEX_1, DIMINDEX_2, DIMINDEX_3, DIMINDEX_4, .. } := D.core1
  let { LE_ANTISYM, .. } := D.core2
  let { REAL_ADD_ASSOC, .. } := D.core3
  let { SUM_CLAUSES_NUMSEG, .. } := D.core4
  let { SUM_SING_NUMSEG, .. } := D.core5
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))

  let FORALL_1 ← prove
   r"(!i. 1 <= i /\ i <= 1 ==> P i) <=> P 1"
   (MESON_TAC [LE_ANTISYM])

  let FORALL_2 ← prove
   r"!P. (!i. 1 <= i /\ i <= 2 ==> P i) <=> P 1 /\ P 2"
   (MESON_TAC [← ARITH_RULE (← q r"1 <= i /\ i <= 2 <=> i = 1 \/ i = 2")])

  let FORALL_3 ← prove
   r"!P. (!i. 1 <= i /\ i <= 3 ==> P i) <=> P 1 /\ P 2 /\ P 3"
   (MESON_TAC [← ARITH_RULE (← q r"1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3")])

  let FORALL_4 ← prove
   r"!P. (!i. 1 <= i /\ i <= 4 ==> P i) <=> P 1 /\ P 2 /\ P 3 /\ P 4"
   (MESON_TAC [← ARITH_RULE (← q r"1 <= i /\ i <= 4 <=>
    i = 1 \/ i = 2 \/ i = 3 \/ i = 4")])

  let SUM_1 ← prove
   r"sum(1..1) f = f(1)"
   (REWRITE_TAC [SUM_SING_NUMSEG])

  let SUM_2 ← prove
   r"!t. sum(1..2) t = t(1) + t(2)"
   (REWRITE_TAC [← numc "2", SUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC [SUM_SING_NUMSEG, ARITH, REAL_ADD_ASSOC])

  let SUM_3 ← prove
   r"!t. sum(1..3) t = t(1) + t(2) + t(3)"
   (REWRITE_TAC [← numc "3", ← numc "2", SUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC [SUM_SING_NUMSEG, ARITH, REAL_ADD_ASSOC])

  let SUM_4 ← prove
   r"!t. sum(1..4) t = t(1) + t(2) + t(3) + t(4)"
   (SIMP_TAC [← numc "4", ← numc "3", ← numc "2", SUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC [SUM_SING_NUMSEG, ARITH, REAL_ADD_ASSOC])

  let vector_add ← new_definition
   r"(vector_add:real^N->real^N->real^N) x y = lambda i. x$i + y$i"

  let vector_sub ← new_definition
   r"(vector_sub:real^N->real^N->real^N) x y = lambda i. x$i - y$i"

  let vector_neg ← new_definition
   r"(vector_neg:real^N->real^N) x = lambda i. --(x$i)"

  overload_interface "+" (← q r"(vector_add):real^N->real^N->real^N")
  overload_interface "-" (← q r"(vector_sub):real^N->real^N->real^N")
  overload_interface "--" (← q r"(vector_neg):real^N->real^N")

  prioritize_real

  let prioritize_vector : IO Unit ← do
    let ty ← qty "real^N"
    pure (prioritize_overload ty)

  parse_as_infix ("%", (21, "right"))

  let vector_mul ← new_definition
   r"((%):real->real^N->real^N) c x = lambda i. c * x$i"

  let vec ← new_definition
   r"(vec:num->real^N) n = lambda i. &n"

  parse_as_infix ("dot", (20, "right"))

  let dot ← new_definition
   r"(x:real^N) dot (y:real^N) = sum(1..dimindex(:N)) (\i. x$i * y$i)"

  let DOT_1 ← prove
   r"(x:real^1) dot (y:real^1) = x$1 * y$1"
   (REWRITE_TAC [dot, DIMINDEX_1, SUM_1])

  let DOT_2 ← prove
   r"(x:real^2) dot (y:real^2) = x$1 * y$1 + x$2 * y$2"
   (REWRITE_TAC [dot, DIMINDEX_2, SUM_2])

  let DOT_3 ← prove
   r"(x:real^3) dot (y:real^3) = x$1 * y$1 + x$2 * y$2 + x$3 * y$3"
   (REWRITE_TAC [dot, DIMINDEX_3, SUM_3])

  let DOT_4 ← prove
   r"(x:real^4) dot (y:real^4) = x$1 * y$1 + x$2 * y$2 + x$3 * y$3 + x$4 * y$4"
   (REWRITE_TAC [dot, DIMINDEX_4, SUM_4])

  return { FORALL_1, FORALL_2, FORALL_3, FORALL_4, SUM_1, SUM_2, SUM_3, SUM_4,
           vector_add, vector_sub, vector_neg, prioritize_vector, vector_mul, vec,
           dot, DOT_1, DOT_2, DOT_3, DOT_4 }

/- ------------------------------------------------------------------------- -/
/- A naive proof procedure to lift really trivial arithmetic stuff from R,  -/
/- "component-pushing", and frequently useful arithmetic lemmas over        -/
/- vectors.  (vectors.ml 119-265)                                            -/
/- ------------------------------------------------------------------------- -/

structure VectorArith where
  VECTOR_ARITH_TAC : tactic
  VECTOR_ARITH : term → ExceptT String IO thm
  VEC_COMPONENT : thm
  VECTOR_ADD_COMPONENT : thm
  VECTOR_SUB_COMPONENT : thm
  VECTOR_NEG_COMPONENT : thm
  VECTOR_MUL_COMPONENT : thm
  COND_COMPONENT : thm
  VECTOR_ADD_SYM : thm
  VECTOR_ADD_LID : thm
  VECTOR_ADD_RID : thm
  VECTOR_SUB_REFL : thm
  VECTOR_ADD_LINV : thm
  VECTOR_ADD_RINV : thm
  VECTOR_SUB_RADD : thm
  VECTOR_NEG_SUB : thm
  VECTOR_SUB_EQ : thm
  VECTOR_MUL_ASSOC : thm
  VECTOR_MUL_LID : thm
  VECTOR_MUL_LZERO : thm
  VECTOR_SUB_ADD : thm
  VECTOR_SUB_ADD2 : thm
  VECTOR_ADD_LDISTRIB : thm
  VECTOR_SUB_LDISTRIB : thm
  VECTOR_ADD_RDISTRIB : thm
  VECTOR_SUB_RDISTRIB : thm
  VECTOR_ADD_SUB : thm
  VECTOR_EQ_ADDR : thm
  VECTOR_SUB : thm
  VECTOR_SUB_RZERO : thm
  VECTOR_MUL_RZERO : thm
  VECTOR_NEG_MINUS1 : thm
  VECTOR_ADD_ASSOC : thm
  VECTOR_SUB_LZERO : thm
  VECTOR_NEG_NEG : thm
  VECTOR_MUL_LNEG : thm
  VECTOR_MUL_RNEG : thm
  VECTOR_NEG_0 : thm
  VECTOR_NEG_EQ_0 : thm
  VECTOR_EQ_NEG2 : thm
  VECTOR_ADD_AC : thm
  VEC_EQ : thm
  deriving Inhabited

@[nospecialize]
def setupVectorArith [HolBase] (D : VectorsDeps) (BBasics : Basics) :
    ExceptT String IO VectorArith := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, REAL_ARITH_TAC, .. } := D
  let { AND_FORALL_THM, CART_EQ, CONJ_ASSOC, DIMINDEX_GE_1,
        FINITE_INDEX_INRANGE, .. } := D.core1
  let { IMP_IMP, LAMBDA_BETA, LE_REFL, MONO_FORALL, .. } := D.core2
  let { REAL_OF_NUM_EQ, SUM_ADD_NUMSEG, SUM_EQ_0_NUMSEG, SUM_EQ_NUMSEG, .. } := D.core4
  let { SUM_LMUL, SUM_NEG, SUM_RMUL, SUM_SUB_NUMSEG, .. } := D.core5
  let { dot, vec, vector_add, vector_mul, vector_neg, vector_sub, .. } := BBasics
  -- @@SCOPE END

  let VECTOR_ARITH_TAC : tactic ← do
    let RENAMED_LAMBDA_BETA (th : thm) : ExceptT String IO thm := do
      let t ← liftExcept (funpowM 3 rand (concl th))
      let (d, _) ← liftExcept (HolCore.Basics.dest_fun_ty (type_of t))
      if d == aty then HolLight.INST_TYPE [(aty, bty), (bty, aty)] LAMBDA_BETA
      else pure LAMBDA_BETA
    pure (POP_ASSUM_LIST (K ALL_TAC) THEN
      REPEAT (GEN_TAC ORELSE CONJ_TAC ORELSE DISCH_TAC ORELSE EQ_TAC) THEN
      REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [IMP_IMP, ← GSYM CONJ_ASSOC] THEN
      REWRITE_TAC [dot, ← GSYM SUM_ADD_NUMSEG, ← GSYM SUM_SUB_NUMSEG,
                   ← GSYM SUM_LMUL, ← GSYM SUM_RMUL, ← GSYM SUM_NEG] THEN
      (MATCH_MP_TAC SUM_EQ_NUMSEG ORELSE MATCH_MP_TAC SUM_EQ_0_NUMSEG ORELSE
       GEN_REWRITE_TAC ONCE_DEPTH_CONV [CART_EQ]) THEN
      REWRITE_TAC [AND_FORALL_THM] THEN TRY EQ_TAC THEN
      TRY (MATCH_MP_TAC MONO_FORALL) THEN GEN_TAC THEN
      REWRITE_TAC [← TAUT (← q r"(a ==> b) /\ (a ==> c) <=> a ==> b /\ c"),
                   ← TAUT (← q r"(a ==> b) \/ (a ==> c) <=> a ==> b \/ c")] THEN
      TRY (MATCH_MP_TAC (← TAUT (← q r"(a ==> b ==> c) ==> (a ==> b) ==> (a ==> c)"))) THEN
      REWRITE_TAC [vector_add, vector_sub, vector_neg, vector_mul, vec] THEN
      DISCH_THEN (fun th => tactic_of do
        pure (REWRITE_TAC [← MATCH_MP (← RENAMED_LAMBDA_BETA th) th])) THEN
      REAL_ARITH_TAC)

  let VECTOR_ARITH (tm : term) : ExceptT String IO thm :=
    ExceptT.mk (HolCore.Tactics.prove HolBase.B tm VECTOR_ARITH_TAC)
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let VEC_COMPONENT ← prove
   r"!k i. (vec k :real^N)$i = &k"
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN (← q r"?k. 1 <= k /\ k <= dimindex(:N) /\ !z:real^N. z$i = z$k")
    CHOOSE_TAC THENL
     [REWRITE_TAC [FINITE_INDEX_INRANGE],
      ASM_SIMP_TAC [vec, CART_EQ, LAMBDA_BETA]])

  let VECTOR_ADD_COMPONENT ← prove
   r"!x:real^N y i. (x + y)$i = x$i + y$i"
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN (← q r"?k. 1 <= k /\ k <= dimindex(:N) /\ !z:real^N. z$i = z$k")
    CHOOSE_TAC THENL
     [REWRITE_TAC [FINITE_INDEX_INRANGE],
      ASM_SIMP_TAC [vector_add, CART_EQ, LAMBDA_BETA]])

  let VECTOR_SUB_COMPONENT ← prove
   r"!x:real^N y i. (x - y)$i = x$i - y$i"
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN (← q r"?k. 1 <= k /\ k <= dimindex(:N) /\ !z:real^N. z$i = z$k")
    CHOOSE_TAC THENL
     [REWRITE_TAC [FINITE_INDEX_INRANGE],
      ASM_SIMP_TAC [vector_sub, CART_EQ, LAMBDA_BETA]])

  let VECTOR_NEG_COMPONENT ← prove
   r"!x:real^N i. (--x)$i = --(x$i)"
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN (← q r"?k. 1 <= k /\ k <= dimindex(:N) /\ !z:real^N. z$i = z$k")
    CHOOSE_TAC THENL
     [REWRITE_TAC [FINITE_INDEX_INRANGE],
      ASM_SIMP_TAC [vector_neg, CART_EQ, LAMBDA_BETA]])

  let VECTOR_MUL_COMPONENT ← prove
   r"!c x:real^N i. (c % x)$i = c * x$i"
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN (← q r"?k. 1 <= k /\ k <= dimindex(:N) /\ !z:real^N. z$i = z$k")
    CHOOSE_TAC THENL
     [REWRITE_TAC [FINITE_INDEX_INRANGE],
      ASM_SIMP_TAC [vector_mul, CART_EQ, LAMBDA_BETA]])

  let COND_COMPONENT ← prove
   r"(if b then x else y)$i = if b then x$i else y$i"
   (MESON_TAC [])

  let VECTOR_ADD_SYM ← va r"!x y:real^N. x + y = y + x"
  let VECTOR_ADD_LID ← va r"!x. vec 0 + x = x"
  let VECTOR_ADD_RID ← va r"!x. x + vec 0 = x"
  let VECTOR_SUB_REFL ← va r"!x. x - x = vec 0"
  let VECTOR_ADD_LINV ← va r"!x. --x + x = vec 0"
  let VECTOR_ADD_RINV ← va r"!x. x + --x = vec 0"
  let VECTOR_SUB_RADD ← va r"!x y. x - (x + y) = --y:real^N"
  let VECTOR_NEG_SUB ← va r"!x:real^N y. --(x - y) = y - x"
  let VECTOR_SUB_EQ ← va r"!x y. (x - y = vec 0) <=> (x = y)"
  let VECTOR_MUL_ASSOC ← va r"!a b x. a % (b % x) = (a * b) % x"
  let VECTOR_MUL_LID ← va r"!x. &1 % x = x"
  let VECTOR_MUL_LZERO ← va r"!x. &0 % x = vec 0"
  let VECTOR_SUB_ADD ← va r"(x - y) + y = x:real^N"
  let VECTOR_SUB_ADD2 ← va r"y + (x - y) = x:real^N"
  let VECTOR_ADD_LDISTRIB ← va r"c % (x + y) = c % x + c % y"
  let VECTOR_SUB_LDISTRIB ← va r"c % (x - y) = c % x - c % y"
  let VECTOR_ADD_RDISTRIB ← va r"(a + b) % x = a % x + b % x"
  let VECTOR_SUB_RDISTRIB ← va r"(a - b) % x = a % x - b % x"
  let VECTOR_ADD_SUB ← va r"(x + y:real^N) - x = y"
  let VECTOR_EQ_ADDR ← va r"(x + y = x) <=> (y = vec 0)"
  let VECTOR_SUB ← va r"x - y = x + --(y:real^N)"
  let VECTOR_SUB_RZERO ← va r"x - vec 0 = x"
  let VECTOR_MUL_RZERO ← va r"c % vec 0 = vec 0"
  let VECTOR_NEG_MINUS1 ← va r"--x = (--(&1)) % x"
  let VECTOR_ADD_ASSOC ← va r"(x:real^N) + y + z = (x + y) + z"
  let VECTOR_SUB_LZERO ← va r"vec 0 - x = --x"
  let VECTOR_NEG_NEG ← va r"--(--(x:real^N)) = x"
  let VECTOR_MUL_LNEG ← va r"--c % x = --(c % x)"
  let VECTOR_MUL_RNEG ← va r"c % --x = --(c % x)"
  let VECTOR_NEG_0 ← va r"--(vec 0) = vec 0"
  let VECTOR_NEG_EQ_0 ← va r"--x = vec 0 <=> x = vec 0"
  let VECTOR_EQ_NEG2 ← va r"!x y:real^N. --x = --y <=> x = y"
  let VECTOR_ADD_AC ← va
   r"(m + n = n + m:real^N) /\
   ((m + n) + p = m + n + p) /\
   (m + n + p = n + m + p)"

  let VEC_EQ ← prove
   r"!m n. (vec m = vec n) <=> (m = n)"
   (SIMP_TAC [CART_EQ, VEC_COMPONENT, REAL_OF_NUM_EQ] THEN
    MESON_TAC [LE_REFL, DIMINDEX_GE_1])

  return { VECTOR_ARITH_TAC, VECTOR_ARITH, VEC_COMPONENT, VECTOR_ADD_COMPONENT,
           VECTOR_SUB_COMPONENT, VECTOR_NEG_COMPONENT, VECTOR_MUL_COMPONENT,
           COND_COMPONENT, VECTOR_ADD_SYM, VECTOR_ADD_LID, VECTOR_ADD_RID,
           VECTOR_SUB_REFL, VECTOR_ADD_LINV, VECTOR_ADD_RINV, VECTOR_SUB_RADD,
           VECTOR_NEG_SUB, VECTOR_SUB_EQ, VECTOR_MUL_ASSOC, VECTOR_MUL_LID,
           VECTOR_MUL_LZERO, VECTOR_SUB_ADD, VECTOR_SUB_ADD2, VECTOR_ADD_LDISTRIB,
           VECTOR_SUB_LDISTRIB, VECTOR_ADD_RDISTRIB, VECTOR_SUB_RDISTRIB,
           VECTOR_ADD_SUB, VECTOR_EQ_ADDR, VECTOR_SUB, VECTOR_SUB_RZERO,
           VECTOR_MUL_RZERO, VECTOR_NEG_MINUS1, VECTOR_ADD_ASSOC, VECTOR_SUB_LZERO,
           VECTOR_NEG_NEG, VECTOR_MUL_LNEG, VECTOR_MUL_RNEG, VECTOR_NEG_0,
           VECTOR_NEG_EQ_0, VECTOR_EQ_NEG2, VECTOR_ADD_AC, VEC_EQ }

/- ------------------------------------------------------------------------- -/
/- Set-sums, infinitude of Euclidean space, properties of the dot product,  -/
/- trivial theorems about mapping R^n itself, and R^1.  (vectors.ml 267-404)  -/
/- ------------------------------------------------------------------------- -/

structure DotProps where
  SUMS_SYM : thm
  SUMS_ASSOC : thm
  EUCLIDEAN_SPACE_INFINITE : thm
  DOT_SYM : thm
  DOT_LADD : thm
  DOT_RADD : thm
  DOT_LSUB : thm
  DOT_RSUB : thm
  DOT_LMUL : thm
  DOT_RMUL : thm
  DOT_LNEG : thm
  DOT_RNEG : thm
  DOT_LZERO : thm
  DOT_RZERO : thm
  DOT_POS_LE : thm
  DOT_EQ_0 : thm
  DOT_POS_LT : thm
  FORALL_DOT_EQ_0 : thm
  REFLECT_UNIV : thm
  TRANSLATION_UNIV : thm
  TRANSLATION_SUBSET_GALOIS_RIGHT : thm
  TRANSLATION_SUBSET_GALOIS_LEFT : thm
  TRANSLATION_GALOIS : thm
  IN_TRANSLATION_GALOIS : thm
  IN_TRANSLATION_GALOIS_ALT : thm
  FORALL_DIMINDEX_1 : thm
  VECTOR_ONE : thm
  FORALL_REAL_ONE : thm
  deriving Inhabited

@[nospecialize]
def setupDotProps [HolBase] (D : VectorsDeps) (BBasics : Basics)
    (BVectorArith : VectorArith) : ExceptT String IO DotProps := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, SET_RULE, SET_TAC, .. } := D
  let { CART_EQ, CONJ_ACI, DIMINDEX_1, EXTENSION, FINITE_IMAGE_INJ, .. } := D.core1
  let { IMAGE_CLAUSES, IMP_CONJ_ALT, INFINITE, IN_ELIM_THM, LAMBDA_BETA,
        LE_ANTISYM, .. } := D.core2
  let { REAL_ENTIRE, REAL_LE_SQUARE, REAL_LT_LE, .. } := D.core3
  let { SING_SUBSET, SUBSET_ANTISYM_EQ, .. } := D.core4
  let { SUM_POS_EQ_0_NUMSEG, SUM_POS_LE_NUMSEG, num_INFINITE, .. } := D.core5
  let { dot, vec, .. } := BBasics
  let { VECTOR_ADD_ASSOC, VECTOR_ADD_SYM, VECTOR_ARITH, VECTOR_NEG_NEG,
        VEC_EQ, .. } := BVectorArith
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let SUMS_SYM ← prove
   r"!s t:real^N->bool.
        {x + y | x IN s /\ y IN t} = {y + x | y IN t /\ x IN s}"
   (REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN MESON_TAC [VECTOR_ADD_SYM])

  let SUMS_ASSOC ← prove
   r"!s t u:real^N->bool.
        {w + z | w IN {x + y | x IN s /\ y IN t} /\ z IN u} =
        {x + v | x IN s /\ v IN {y + z | y IN t /\ z IN u}}"
   (REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN MESON_TAC [VECTOR_ADD_ASSOC])

  let EUCLIDEAN_SPACE_INFINITE ← prove
   r"INFINITE(:real^N)"
   (REWRITE_TAC [INFINITE] THEN DISCH_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (MP_TAC (← ISPEC (← q r"vec:num->real^N")
        (← MATCH_MP (← REWRITE_RULE [IMP_CONJ_ALT] FINITE_IMAGE_INJ) th)))) THEN
    REWRITE_TAC [VEC_EQ, ← SET_RULE (← q r"{x | f x IN UNIV} = UNIV")] THEN
    REWRITE_TAC [← GSYM INFINITE, num_INFINITE])

  let DOT_SYM ← va r"!x y. x dot y = y dot x"
  let DOT_LADD ← va r"!x y z. (x + y) dot z = (x dot z) + (y dot z)"
  let DOT_RADD ← va r"!x y z. x dot (y + z) = (x dot y) + (x dot z)"
  let DOT_LSUB ← va r"!x y z. (x - y) dot z = (x dot z) - (y dot z)"
  let DOT_RSUB ← va r"!x y z. x dot (y - z) = (x dot y) - (x dot z)"
  let DOT_LMUL ← va r"!c x y. (c % x) dot y = c * (x dot y)"
  let DOT_RMUL ← va r"!c x y. x dot (c % y) = c * (x dot y)"
  let DOT_LNEG ← va r"!x y. (--x) dot y = --(x dot y)"
  let DOT_RNEG ← va r"!x y. x dot (--y) = --(x dot y)"
  let DOT_LZERO ← va r"!x. (vec 0) dot x = &0"
  let DOT_RZERO ← va r"!x. x dot (vec 0) = &0"

  let DOT_POS_LE ← prove
   r"!x. &0 <= x dot x"
   (SIMP_TAC [dot, SUM_POS_LE_NUMSEG, REAL_LE_SQUARE])

  let DOT_EQ_0 ← prove
   r"!x:real^N. ((x dot x = &0) <=> (x = vec 0))"
   (REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC, MESON_TAC [DOT_LZERO]] THEN
    SIMP_TAC [dot, CART_EQ, vec, LAMBDA_BETA] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC [← GSYM (← ExceptT.mk (REWRITE_CONV [REAL_ENTIRE] (← q r"x * x = &0")))] THEN
    MATCH_MP_TAC SUM_POS_EQ_0_NUMSEG THEN ASM_REWRITE_TAC [REAL_LE_SQUARE])

  let DOT_POS_LT ← prove
   r"!x. (&0 < x dot x) <=> ~(x = vec 0)"
   (REWRITE_TAC [REAL_LT_LE, DOT_POS_LE] THEN MESON_TAC [DOT_EQ_0])

  let FORALL_DOT_EQ_0 ← prove
   r"(!y. (!x. x dot y = &0) <=> y = vec 0) /\
   (!x. (!y. x dot y = &0) <=> x = vec 0)"
   (MESON_TAC [DOT_LZERO, DOT_RZERO, DOT_EQ_0])

  let REFLECT_UNIV ← prove
   r"IMAGE (--) (:real^N) = (:real^N)"
   (MP_TAC (← va r"!x:real^N. --(--x) = x") THEN SET_TAC [])

  let TRANSLATION_UNIV ← prove
   r"!a. IMAGE (\x. a + x) (:real^N) = (:real^N)"
   (GEN_TAC THEN MP_TAC (← va r"!x. a + (x - a):real^N = x") THEN
    SET_TAC [])

  let TRANSLATION_SUBSET_GALOIS_RIGHT ← prove
   r"!s t a:real^N.
    s SUBSET IMAGE (\x. a + x) t <=> IMAGE (\x. --a + x) s SUBSET t"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC (← SET_RULE (← q
     r"(!x. f(g x) = x) /\ (!y. g(f y) = y)
    ==> (s SUBSET IMAGE f t <=> IMAGE g s SUBSET t)")) THEN
    REWRITE_TAC [] THEN CONV_TAC (fun t => VECTOR_ARITH t))

  let TRANSLATION_SUBSET_GALOIS_LEFT ← prove
   r"!s t a:real^N.
     IMAGE (\x. a + x) s SUBSET t <=> s SUBSET IMAGE (\x. --a + x) t"
   (REWRITE_TAC [TRANSLATION_SUBSET_GALOIS_RIGHT, VECTOR_NEG_NEG])

  let TRANSLATION_GALOIS ← prove
   r"!s t a:real^N. s = IMAGE (\x. a + x) t <=> t = IMAGE (\x. --a + x) s"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN
    REWRITE_TAC [TRANSLATION_SUBSET_GALOIS_RIGHT, VECTOR_NEG_NEG] THEN
    REWRITE_TAC [CONJ_ACI])

  let IN_TRANSLATION_GALOIS ← prove
   r"!s a b:real^N. b IN IMAGE (\x. a + x) s <=> (b - a) IN s"
   (REWRITE_TAC [← GSYM SING_SUBSET, TRANSLATION_SUBSET_GALOIS_RIGHT] THEN
    REWRITE_TAC [← va r"b - a:real^N = --a + b"] THEN SET_TAC [])

  let IN_TRANSLATION_GALOIS_ALT ← prove
   r"!s a b:real^N. (a + b) IN s <=> b IN IMAGE (\x. --a + x) s"
   (REWRITE_TAC [← GSYM SING_SUBSET, TRANSLATION_SUBSET_GALOIS_RIGHT] THEN
    REWRITE_TAC [IMAGE_CLAUSES, VECTOR_NEG_NEG])

  let FORALL_DIMINDEX_1 ← prove
   r"(!i. 1 <= i /\ i <= dimindex(:1) ==> P i) <=> P 1"
   (MESON_TAC [DIMINDEX_1, LE_ANTISYM])

  let VECTOR_ONE ← prove
   r"!x:real^1. x = lambda i. x$1"
   (SIMP_TAC [CART_EQ, LAMBDA_BETA] THEN MESON_TAC [DIMINDEX_1, LE_ANTISYM])

  let FORALL_REAL_ONE ← prove
   r"(!x:real^1. P x) <=> (!x. P(lambda i. x))"
   (EQ_TAC THEN SIMP_TAC [] THEN DISCH_TAC THEN GEN_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(x:real^1)$1")) THEN
    REWRITE_TAC [← GSYM VECTOR_ONE])

  return { SUMS_SYM, SUMS_ASSOC, EUCLIDEAN_SPACE_INFINITE, DOT_SYM, DOT_LADD,
           DOT_RADD, DOT_LSUB, DOT_RSUB, DOT_LMUL, DOT_RMUL, DOT_LNEG, DOT_RNEG,
           DOT_LZERO, DOT_RZERO, DOT_POS_LE, DOT_EQ_0, DOT_POS_LT, FORALL_DOT_EQ_0,
           REFLECT_UNIV, TRANSLATION_UNIV, TRANSLATION_SUBSET_GALOIS_RIGHT,
           TRANSLATION_SUBSET_GALOIS_LEFT, TRANSLATION_GALOIS, IN_TRANSLATION_GALOIS,
           IN_TRANSLATION_GALOIS_ALT, FORALL_DIMINDEX_1, VECTOR_ONE, FORALL_REAL_ONE }

/- ------------------------------------------------------------------------- -/
/- The usual Euclidean norm and metric on R^n.  (vectors.ml 406-574)        -/
/- ------------------------------------------------------------------------- -/

structure Norm1 where
  vector_norm : thm
  dist : thm
  NORM_REAL : thm
  DIST_REAL : thm
  NORM_0 : thm
  NORM_POS_LE : thm
  NORM_NEG : thm
  NORM_SUB : thm
  NORM_MUL : thm
  NORM_EQ_0_DOT : thm
  NORM_EQ_0 : thm
  NORM_POS_LT : thm
  NORM_POW_2 : thm
  NORM_EQ_0_IMP : thm
  NORM_LE_0 : thm
  VECTOR_MUL_EQ_0 : thm
  VECTOR_MUL_LCANCEL : thm
  VECTOR_MUL_RCANCEL : thm
  VECTOR_MUL_LCANCEL_IMP : thm
  VECTOR_MUL_RCANCEL_IMP : thm
  NORM_CAUCHY_SCHWARZ : thm
  NORM_CAUCHY_SCHWARZ_ABS : thm
  REAL_ABS_NORM : thm
  NORM_CAUCHY_SCHWARZ_DIV : thm
  NORM_TRIANGLE : thm
  NORM_TRIANGLE_SUB : thm
  NORM_TRIANGLE_LE : thm
  NORM_TRIANGLE_LT : thm
  COMPONENT_LE_NORM : thm
  NORM_BOUND_COMPONENT_LE : thm
  NORM_BOUND_COMPONENT_LT : thm
  deriving Inhabited

@[nospecialize]
def setupNorm1 [HolBase] (D : VectorsDeps) (BBasics : Basics)
    (BVectorArith : VectorArith) (BDotProps : DotProps) : ExceptT String IO Norm1 := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, make_overloadable, new_definition,
        overload_interface, override_interface, .. } := D
  let { DIMINDEX_1, FINITE_INDEX_INRANGE, FINITE_NUMSEG, .. } := D.core1
  let { IN_NUMSEG, LAMBDA_BETA, LE_REFL, .. } := D.core2
  let { POW_2_SQRT_ABS, REAL_ABS_DIV, REAL_ABS_INV, REAL_ABS_MUL, REAL_ABS_NUM,
        REAL_ABS_POW, REAL_ABS_REFL, REAL_ABS_ZERO, REAL_ENTIRE, REAL_INV_1,
        REAL_LET_TRANS, REAL_LE_ADD, REAL_LE_LDIV_EQ, REAL_LE_LMUL_EQ,
        REAL_LE_LSQRT, REAL_LE_REFL, REAL_LE_RSQRT, REAL_LE_SQUARE, REAL_LE_TRANS,
        REAL_LT_LE, REAL_LT_MUL, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LZERO,
        REAL_LE_ANTISYM, .. } := D.core3
  let { REAL_MUL_RZERO, REAL_NEG_NEG, REAL_POS, REAL_POW_2, REAL_SQRT_POW_2,
        REAL_SUB_0, SQRT_0, SQRT_EQ_0, SQRT_MUL, SQRT_POS_LE, SQRT_POW_2,
        SUM_DELTA, .. } := D.core4
  let { SUM_LE, SUM_SING_NUMSEG, real_abs, real_div, .. } := D.core5
  let { dot, vector_sub, .. } := BBasics
  let { VECTOR_NEG_SUB, VECTOR_SUB_ADD2, VECTOR_SUB_EQ, VECTOR_SUB_LDISTRIB,
        VECTOR_SUB_RDISTRIB, .. } := BVectorArith
  let { DOT_EQ_0, DOT_LADD, DOT_LMUL, DOT_LNEG, DOT_LSUB, DOT_LZERO, DOT_POS_LE,
        DOT_RADD, DOT_RMUL, DOT_RNEG, DOT_RSUB, DOT_RZERO, DOT_SYM, .. } := BDotProps
  -- @@SCOPE END

  make_overloadable "norm" (← qty "A->real")
  overload_interface "norm" (← q r"vector_norm:real^N->real")

  let vector_norm ← new_definition
   r"norm x = sqrt(x dot x)"

  override_interface "dist" (← q r"distance:real^N#real^N->real")

  let dist ← new_definition
   r"dist(x,y) = norm(x - y)"

  let NORM_REAL ← prove
   r"!x:real^1. norm(x) = abs(x$1)"
   (REWRITE_TAC [vector_norm, dot, DIMINDEX_1, SUM_SING_NUMSEG,
                 ← GSYM REAL_POW_2, POW_2_SQRT_ABS])

  let DIST_REAL ← prove
   r"!x:real^1 y. dist(x,y) = abs(x$1 - y$1)"
   (SIMP_TAC [dist, NORM_REAL, vector_sub, LAMBDA_BETA, LE_REFL, DIMINDEX_1])

  let NORM_0 ← prove
   r"norm(vec 0) = &0"
   (REWRITE_TAC [vector_norm, DOT_LZERO, SQRT_0])

  let NORM_POS_LE ← prove
   r"!x. &0 <= norm x"
   (GEN_TAC THEN SIMP_TAC [DOT_POS_LE, vector_norm, SQRT_POS_LE])

  let NORM_NEG ← prove
   r"!x. norm(--x) = norm x"
   (REWRITE_TAC [vector_norm, DOT_LNEG, DOT_RNEG, REAL_NEG_NEG])

  let NORM_SUB ← prove
   r"!x y. norm(x - y) = norm(y - x)"
   (MESON_TAC [NORM_NEG, VECTOR_NEG_SUB])

  let NORM_MUL ← prove
   r"!a x. norm(a % x) = abs(a) * norm x"
   (REWRITE_TAC [vector_norm, DOT_LMUL, DOT_RMUL, REAL_MUL_ASSOC] THEN
    REWRITE_TAC [SQRT_MUL, ← GSYM REAL_POW_2, REAL_SQRT_POW_2])

  let NORM_EQ_0_DOT ← prove
   r"!x. (norm x = &0) <=> (x dot x = &0)"
   (SIMP_TAC [vector_norm, SQRT_EQ_0, DOT_POS_LE])

  let NORM_EQ_0 ← prove
   r"!x. (norm x = &0) <=> (x = vec 0)"
   (SIMP_TAC [vector_norm, DOT_EQ_0, SQRT_EQ_0, DOT_POS_LE])

  let NORM_POS_LT ← prove
   r"!x. &0 < norm x <=> ~(x = vec 0)"
   (MESON_TAC [REAL_LT_LE, NORM_POS_LE, NORM_EQ_0])

  let NORM_POW_2 ← prove
   r"!x. norm(x) pow 2 = x dot x"
   (SIMP_TAC [vector_norm, SQRT_POW_2, DOT_POS_LE])

  let NORM_EQ_0_IMP ← prove
   r"!x. (norm x = &0) ==> (x = vec 0)"
   (MESON_TAC [NORM_EQ_0])

  let NORM_LE_0 ← prove
   r"!x. norm x <= &0 <=> (x = vec 0)"
   (MESON_TAC [REAL_LE_ANTISYM, NORM_EQ_0, NORM_POS_LE])

  let VECTOR_MUL_EQ_0 ← prove
   r"!a x. (a % x = vec 0) <=> (a = &0) \/ (x = vec 0)"
   (REWRITE_TAC [← GSYM NORM_EQ_0, NORM_MUL, REAL_ABS_ZERO, REAL_ENTIRE])

  let VECTOR_MUL_LCANCEL ← prove
   r"!a x y. (a % x = a % y) <=> (a = &0) \/ (x = y)"
   (MESON_TAC [VECTOR_MUL_EQ_0, VECTOR_SUB_LDISTRIB, VECTOR_SUB_EQ])

  let VECTOR_MUL_RCANCEL ← prove
   r"!a b x. (a % x = b % x) <=> (a = b) \/ (x = vec 0)"
   (MESON_TAC [VECTOR_MUL_EQ_0, VECTOR_SUB_RDISTRIB, REAL_SUB_0, VECTOR_SUB_EQ])

  let VECTOR_MUL_LCANCEL_IMP ← prove
   r"!a x y. ~(a = &0) /\ (a % x = a % y) ==> (x = y)"
   (MESON_TAC [VECTOR_MUL_LCANCEL])

  let VECTOR_MUL_RCANCEL_IMP ← prove
   r"!a b x. ~(x = vec 0) /\ (a % x = b % x) ==> (a = b)"
   (MESON_TAC [VECTOR_MUL_RCANCEL])

  let NORM_CAUCHY_SCHWARZ ← prove
   r"!(x:real^N) y. x dot y <= norm(x) * norm(y)"
   (REPEAT STRIP_TAC THEN MAP_EVERY ASM_CASES_TAC
     [← q r"norm(x:real^N) = &0", ← q r"norm(y:real^N) = &0"] THEN
    ASM_SIMP_TAC [NORM_EQ_0_IMP, DOT_LZERO, DOT_RZERO,
                  REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
    MP_TAC (← ISPEC (← q r"norm(y:real^N) % x - norm(x:real^N) % y") DOT_POS_LE) THEN
    REWRITE_TAC [DOT_RSUB, DOT_LSUB, DOT_LMUL, DOT_RMUL, ← GSYM NORM_POW_2,
                 REAL_POW_2, REAL_LE_REFL] THEN
    REWRITE_TAC [DOT_SYM, ← REAL_ARITH (← q
     r"&0 <= y * (y * x * x - x * d) - x * (y * d - x * y * y) <=>
    x * y * d <= x * y * x * y")] THEN
    ASM_SIMP_TAC [REAL_LE_LMUL_EQ, REAL_LT_LE, NORM_POS_LE])

  let NORM_CAUCHY_SCHWARZ_ABS ← prove
   r"!x:real^N y. abs(x dot y) <= norm(x) * norm(y)"
   (REPEAT GEN_TAC THEN MP_TAC (← ISPEC (← q r"x:real^N") NORM_CAUCHY_SCHWARZ) THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← SPEC (← q r"y:real^N") th) THEN
            MP_TAC (← SPEC (← q r"--(y:real^N)") th))) THEN
    REWRITE_TAC [DOT_RNEG, NORM_NEG] THEN REAL_ARITH_TAC)

  let REAL_ABS_NORM ← prove
   r"!x. abs(norm x) = norm x"
   (REWRITE_TAC [NORM_POS_LE, REAL_ABS_REFL])

  let NORM_CAUCHY_SCHWARZ_DIV ← prove
   r"!x:real^N y. abs((x dot y) / (norm x * norm y)) <= &1"
   (REPEAT GEN_TAC THEN
    MAP_EVERY ASM_CASES_TAC [← q r"x:real^N = vec 0", ← q r"y:real^N = vec 0"] THEN
    ASM_REWRITE_TAC [NORM_0, REAL_MUL_LZERO, REAL_MUL_RZERO, real_div,
               REAL_INV_1, DOT_LZERO, DOT_RZERO, REAL_ABS_NUM, REAL_POS] THEN
    ASM_SIMP_TAC [← GSYM real_div, REAL_ABS_DIV, REAL_LE_LDIV_EQ, REAL_LT_MUL,
       REAL_ABS_INV, NORM_POS_LT, REAL_ABS_MUL, REAL_ABS_NORM] THEN
    REWRITE_TAC [REAL_MUL_LID, NORM_CAUCHY_SCHWARZ_ABS])

  let NORM_TRIANGLE ← prove
   r"!x y. norm(x + y) <= norm(x) + norm(y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [vector_norm] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN
    SIMP_TAC [← GSYM vector_norm, DOT_POS_LE, NORM_POS_LE, REAL_LE_ADD] THEN
    REWRITE_TAC [DOT_LADD, DOT_RADD, REAL_POW_2, ← GSYM NORM_POW_2] THEN
    SIMP_TAC [NORM_CAUCHY_SCHWARZ, DOT_SYM, ← REAL_ARITH (← q
     r"d <= x * y ==> (x * x + d) + (d + y * y) <= (x + y) * (x + y)")])

  let NORM_TRIANGLE_SUB ← prove
   r"!x y:real^N. norm(x) <= norm(y) + norm(x - y)"
   (MESON_TAC [NORM_TRIANGLE, VECTOR_SUB_ADD2])

  let NORM_TRIANGLE_LE ← prove
   r"!x y. norm(x) + norm(y) <= e ==> norm(x + y) <= e"
   (MESON_TAC [REAL_LE_TRANS, NORM_TRIANGLE])

  let NORM_TRIANGLE_LT ← prove
   r"!x y. norm(x) + norm(y) < e ==> norm(x + y) < e"
   (MESON_TAC [REAL_LET_TRANS, NORM_TRIANGLE])

  let COMPONENT_LE_NORM ← prove
   r"!x:real^N i. abs(x$i) <= norm x"
   (REPEAT GEN_TAC THEN SUBGOAL_THEN
    (← q r"?k. 1 <= k /\ k <= dimindex(:N) /\ !x:real^N. x$i = x$k")
    STRIP_ASSUME_TAC THENL [REWRITE_TAC [FINITE_INDEX_INRANGE], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [vector_norm] THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC [← GSYM REAL_ABS_POW] THEN
    REWRITE_TAC [real_abs, REAL_POW_2, REAL_LE_SQUARE] THEN
    SUBGOAL_THEN
     (← q r"x$k * (x:real^N)$k =
     sum(1..dimindex(:N)) (\i. if i = k then x$k * x$k else &0)")
    SUBST1_TAC THENL
     [REWRITE_TAC [SUM_DELTA] THEN ASM_REWRITE_TAC [IN_NUMSEG], ALL_TAC] THEN
    REWRITE_TAC [dot] THEN MATCH_MP_TAC SUM_LE THEN
    REWRITE_TAC [FINITE_NUMSEG] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [REAL_LE_REFL, REAL_LE_SQUARE])

  let NORM_BOUND_COMPONENT_LE ← prove
   r"!x:real^N e. norm(x) <= e
                ==> !i. 1 <= i /\ i <= dimindex(:N) ==> abs(x$i) <= e"
   (MESON_TAC [COMPONENT_LE_NORM, REAL_LE_TRANS])

  let NORM_BOUND_COMPONENT_LT ← prove
   r"!x:real^N e. norm(x) < e
                ==> !i. 1 <= i /\ i <= dimindex(:N) ==> abs(x$i) < e"
   (MESON_TAC [COMPONENT_LE_NORM, REAL_LET_TRANS])

  return { vector_norm, dist, NORM_REAL, DIST_REAL, NORM_0, NORM_POS_LE, NORM_NEG,
           NORM_SUB, NORM_MUL, NORM_EQ_0_DOT, NORM_EQ_0, NORM_POS_LT, NORM_POW_2,
           NORM_EQ_0_IMP, NORM_LE_0, VECTOR_MUL_EQ_0, VECTOR_MUL_LCANCEL,
           VECTOR_MUL_RCANCEL, VECTOR_MUL_LCANCEL_IMP, VECTOR_MUL_RCANCEL_IMP,
           NORM_CAUCHY_SCHWARZ, NORM_CAUCHY_SCHWARZ_ABS, REAL_ABS_NORM,
           NORM_CAUCHY_SCHWARZ_DIV, NORM_TRIANGLE, NORM_TRIANGLE_SUB,
           NORM_TRIANGLE_LE, NORM_TRIANGLE_LT, COMPONENT_LE_NORM,
           NORM_BOUND_COMPONENT_LE, NORM_BOUND_COMPONENT_LT }

/- ------------------------------------------------------------------------- -/
/- More norm inequalities; squaring equations and inequalities involving    -/
/- norms.  (vectors.ml 576-708)                                              -/
/- ------------------------------------------------------------------------- -/

structure Norm2 where
  NORM_LE_L1 : thm
  REAL_ABS_SUB_NORM : thm
  NORM_LE : thm
  NORM_LT : thm
  NORM_EQ : thm
  NORM_EQ_1 : thm
  NORM_LE_COMPONENTWISE : thm
  NORM_EQ_COMPONENTWISE : thm
  L1_LE_NORM : thm
  DIST_INCREASES_ONLINE : thm
  NORM_INCREASES_ONLINE : thm
  DOT_SQUARE_NORM : thm
  NORM_EQ_SQUARE : thm
  NORM_LE_SQUARE : thm
  NORM_GE_SQUARE : thm
  NORM_LT_SQUARE : thm
  NORM_GT_SQUARE : thm
  NORM_LT_SQUARE_ALT : thm
  deriving Inhabited

@[nospecialize]
def setupNorm2 [HolBase] (D : VectorsDeps) (BBasics : Basics)
    (BVectorArith : VectorArith) (BDotProps : DotProps) (BNorm1 : Norm1) :
    ExceptT String IO Norm2 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_REAL_ARITH_TAC, INDUCT_TAC, MESON_TAC, REAL_ARITH,
        REAL_ARITH_TAC, REAL_RING, REAL_RAT_REDUCE_CONV, .. } := D
  let { ADD_SUB, ARITH, ARITH_EQ, FINITE_NUMSEG, .. } := D.core1
  let { REAL_ABS_MUL, REAL_ABS_POS, REAL_ADD_RID, REAL_LE_ANTISYM, REAL_LE_LSQRT,
        REAL_LE_MUL, REAL_LE_POW_2, REAL_LE_REFL, REAL_LE_SQUARE,
        REAL_LE_SQUARE_ABS, REAL_MUL_LZERO, .. } := D.core3
  let { REAL_OF_NUM_SUC, REAL_POS, REAL_POW2_ABS, REAL_POW_2, REAL_POW_MUL,
        REAL_SUB_LE, SQRT_1, SQRT_INJ, SQRT_LT_0, SQRT_MONO_LE_EQ,
        SQRT_MONO_LT_EQ, SQRT_POS_LE, SQRT_POW_2, SUM_ADD_NUMSEG,
        SUM_CLAUSES_NUMSEG, SUM_CONST_NUMSEG, .. } := D.core4
  let { SUM_LE_NUMSEG, SUM_LMUL, SUM_POS_LE, SUM_POS_LE_NUMSEG, SUM_RMUL,
        SUM_SUB_NUMSEG, SUM_TRIV_NUMSEG, real_ge, real_gt, .. } := D.core5
  let { dot, .. } := BBasics
  let { VECTOR_SUB_LZERO, .. } := BVectorArith
  let { DOT_LADD, DOT_LSUB, DOT_POS_LE, DOT_RADD, DOT_RSUB, .. } := BDotProps
  let { NORM_NEG, NORM_POS_LE, NORM_POS_LT, NORM_POW_2, NORM_SUB,
        NORM_TRIANGLE_SUB, dist, vector_norm, .. } := BNorm1
  -- @@SCOPE END

  let NORM_LE_L1 ← prove
   r"!x:real^N. norm x <= sum(1..dimindex(:N)) (\i. abs(x$i))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [vector_norm, dot] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN REWRITE_TAC [REAL_POW_2] THEN
    SIMP_TAC [SUM_POS_LE, FINITE_NUMSEG, REAL_LE_SQUARE, REAL_ABS_POS] THEN
    SPEC_TAC (← q r"dimindex(:N)", ← q r"n:num") THEN INDUCT_TAC THEN
    REWRITE_TAC [SUM_CLAUSES_NUMSEG, ARITH_EQ, ← ARITH_RULE (← q r"1 <= SUC n")] THEN
    SIMP_TAC [REAL_MUL_LZERO, REAL_LE_REFL] THEN
    MATCH_MP_TAC (← REAL_ARITH (← q
     r"a2 <= a * a /\ &0 <= a * b /\ b2 <= b * b
    ==> a2 + b2 <= (a + b) * (a + b)")) THEN
    ASM_SIMP_TAC [SUM_POS_LE, REAL_LE_MUL, REAL_ABS_POS, FINITE_NUMSEG] THEN
    REWRITE_TAC [← GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC)

  let REAL_ABS_SUB_NORM ← prove
   r"abs(norm(x) - norm(y)) <= norm(x - y)"
   (REWRITE_TAC [← REAL_ARITH (← q r"abs(x - y) <= a <=> x <= y + a /\ y <= x + a")] THEN
    MESON_TAC [NORM_TRIANGLE_SUB, NORM_SUB])

  let NORM_LE ← prove
   r"!x y. norm(x) <= norm(y) <=> x dot x <= y dot y"
   (REWRITE_TAC [vector_norm] THEN MESON_TAC [SQRT_MONO_LE_EQ, DOT_POS_LE])

  let NORM_LT ← prove
   r"!x y. norm(x) < norm(y) <=> x dot x < y dot y"
   (REWRITE_TAC [vector_norm] THEN MESON_TAC [SQRT_MONO_LT_EQ, DOT_POS_LE])

  let NORM_EQ ← prove
   r"!x y. (norm x = norm y) <=> (x dot x = y dot y)"
   (REWRITE_TAC [← GSYM REAL_LE_ANTISYM, NORM_LE])

  let NORM_EQ_1 ← prove
   r"!x. norm(x) = &1 <=> x dot x = &1"
   (GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM SQRT_1] THEN
    SIMP_TAC [vector_norm, SQRT_INJ, DOT_POS_LE, REAL_POS])

  let NORM_LE_COMPONENTWISE ← prove
   r"!x:real^N y:real^N.
        (!i. 1 <= i /\ i <= dimindex(:N) ==> abs(x$i) <= abs(y$i))
        ==> norm(x) <= norm(y)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [NORM_LE, dot] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN
    ASM_SIMP_TAC [← GSYM REAL_POW_2, ← GSYM REAL_LE_SQUARE_ABS])

  let NORM_EQ_COMPONENTWISE ← prove
   r"!x:real^N y:real^N.
        (!i. 1 <= i /\ i <= dimindex (:N) ==> abs(x$i) = abs(y$i))
        ==> norm x = norm y"
   (SIMP_TAC [← GSYM REAL_LE_ANTISYM, NORM_LE_COMPONENTWISE])

  let L1_LE_NORM ← do
    let lemma ← prove
     r"!x n. &n * sum(1..n) (\i. x i pow 2) - (sum(1..n) x) pow 2 =
           sum(1..n) (\i. sum(i+1..n) (\j. (x i - x j) pow 2))"
     (GEN_TAC THEN CONV_TAC (BINDER_CONV SYM_CONV) THEN INDUCT_TAC THEN
      REWRITE_TAC [SUM_CLAUSES_NUMSEG, ARITH, ← ARITH_RULE (← q r"1 <= SUC n")] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      SIMP_TAC [← ARITH_RULE (← q r"i <= n ==> i + 1 <= SUC n"), SUM_TRIV_NUMSEG,
                ← ARITH_RULE (← q r"~(n + 1 <= n)"), ← ARITH_RULE (← q r"n < SUC n + 1")] THEN
      ASM_REWRITE_TAC [SUM_ADD_NUMSEG, REAL_ADD_RID] THEN
      REWRITE_TAC [← REAL_ARITH (← q
       r"(x - y) pow 2 = (x pow 2 + y pow 2) - &2 * x * y")] THEN
      REWRITE_TAC [SUM_ADD_NUMSEG, SUM_SUB_NUMSEG, SUM_LMUL, SUM_RMUL,
                   ← GSYM REAL_OF_NUM_SUC, SUM_CONST_NUMSEG, ADD_SUB] THEN
      REAL_ARITH_TAC)
    prove
     r"!x:real^N.
    sum(1..dimindex(:N)) (\i. abs(x$i)) <= sqrt(&(dimindex(:N))) * norm x"
     (GEN_TAC THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"&0 <= y /\ abs x <= abs y ==> x <= y")) THEN
      SIMP_TAC [REAL_LE_MUL, NORM_POS_LE, SQRT_POS_LE, REAL_POS] THEN
      REWRITE_TAC [REAL_LE_SQUARE_ABS, REAL_POW_MUL] THEN
      SIMP_TAC [SQRT_POW_2, REAL_POS, NORM_POW_2, dot] THEN
      REWRITE_TAC [← GSYM REAL_POW_2] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [← GSYM REAL_POW2_ABS] THEN
      ONCE_REWRITE_TAC [← GSYM REAL_SUB_LE] THEN REWRITE_TAC [lemma] THEN
      SIMP_TAC [SUM_POS_LE_NUMSEG, REAL_LE_POW_2])

  let DIST_INCREASES_ONLINE ← prove
   r"!a b d. ~(d = vec 0)
           ==> dist(a,b + d) > dist(a,b) \/ dist(a,b - d) > dist(a,b)"
   (REWRITE_TAC [dist, vector_norm, real_gt, ← GSYM NORM_POS_LT] THEN
    SIMP_TAC [SQRT_MONO_LT_EQ, DOT_POS_LE, SQRT_LT_0] THEN
    REWRITE_TAC [DOT_RSUB, DOT_RADD, DOT_LSUB, DOT_LADD] THEN REAL_ARITH_TAC)

  let NORM_INCREASES_ONLINE ← prove
   r"!a:real^N d. ~(d = vec 0)
                ==> norm(a + d) > norm(a) \/ norm(a - d) > norm(a)"
   (MP_TAC (← ISPEC (← q r"vec 0 :real^N") DIST_INCREASES_ONLINE) THEN
    REWRITE_TAC [dist, VECTOR_SUB_LZERO, NORM_NEG])

  let DOT_SQUARE_NORM ← prove
   r"!x. x dot x = norm(x) pow 2"
   (SIMP_TAC [vector_norm, SQRT_POW_2, DOT_POS_LE])

  let NORM_EQ_SQUARE ← prove
   r"!x:real^N. norm(x) = a <=> &0 <= a /\ x dot x = a pow 2"
   (REWRITE_TAC [DOT_SQUARE_NORM] THEN
    ONCE_REWRITE_TAC [← REAL_RING (← q r"x pow 2 = a pow 2 <=> x = a \/ x + a = &0")] THEN
    GEN_TAC THEN MP_TAC (← ISPEC (← q r"x:real^N") NORM_POS_LE) THEN REAL_ARITH_TAC)

  let NORM_LE_SQUARE ← prove
   r"!x:real^N. norm(x) <= a <=> &0 <= a /\ x dot x <= a pow 2"
   (REWRITE_TAC [DOT_SQUARE_NORM, ← GSYM REAL_LE_SQUARE_ABS] THEN
    GEN_TAC THEN MP_TAC (← ISPEC (← q r"x:real^N") NORM_POS_LE) THEN REAL_ARITH_TAC)

  let NORM_GE_SQUARE ← prove
   r"!x:real^N. norm(x) >= a <=> a <= &0 \/ x dot x >= a pow 2"
   (REWRITE_TAC [real_ge, DOT_SQUARE_NORM, ← GSYM REAL_LE_SQUARE_ABS] THEN
    GEN_TAC THEN MP_TAC (← ISPEC (← q r"x:real^N") NORM_POS_LE) THEN REAL_ARITH_TAC)

  let NORM_LT_SQUARE ← prove
   r"!x:real^N. norm(x) < a <=> &0 < a /\ x dot x < a pow 2"
   (REWRITE_TAC [← REAL_ARITH (← q r"x < a <=> ~(x >= a)"), NORM_GE_SQUARE] THEN
    REAL_ARITH_TAC)

  let NORM_GT_SQUARE ← prove
   r"!x:real^N. norm(x) > a <=> a < &0 \/ x dot x > a pow 2"
   (REWRITE_TAC [← REAL_ARITH (← q r"x > a <=> ~(x <= a)"), NORM_LE_SQUARE] THEN
    REAL_ARITH_TAC)

  let NORM_LT_SQUARE_ALT ← prove
   r"!x:real^N. norm(x) < a <=> &0 <= a /\ x dot x < a pow 2"
   (REWRITE_TAC [← REAL_ARITH (← q r"x < a <=> ~(x >= a)"), NORM_GE_SQUARE] THEN
    REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"a = &0") THENL
     [ASM_REWRITE_TAC [real_ge] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [DOT_POS_LE],
      ASM_REAL_ARITH_TAC])

  return { NORM_LE_L1, REAL_ABS_SUB_NORM, NORM_LE, NORM_LT, NORM_EQ, NORM_EQ_1,
           NORM_LE_COMPONENTWISE, NORM_EQ_COMPONENTWISE, L1_LE_NORM,
           DIST_INCREASES_ONLINE, NORM_INCREASES_ONLINE, DOT_SQUARE_NORM,
           NORM_EQ_SQUARE, NORM_LE_SQUARE, NORM_GE_SQUARE, NORM_LT_SQUARE,
           NORM_GT_SQUARE, NORM_LT_SQUARE_ALT }


/- ------------------------------------------------------------------------- -/
/- General linear decision procedure for normed spaces.  (vectors.ml 713-1005) -/
/- NORM_ARITH's local functions that do not close over theorems are defined  -/
/- here, at top level, under their OCaml names; the rest are built in         -/
/- `setupNormArith`.                                                          -/
/- ------------------------------------------------------------------------- -/

namespace NormArith

open HolMath.CalcInt (is_ratconst rat_of_term)

/-- `augment_norm` (vectors.ml 715). -/
def augment_norm (b : Bool) (tm : term) (acc : List (Bool × term)) : List (Bool × term) :=
  match tm with
  | .Comb (.Const "vector_norm" _) v => insert (b, v) acc
  | _ => acc

/-- `find_normedterms` (vectors.ml 714-726). -/
partial def find_normedterms (tm : term) (acc : List (Bool × term)) :
    Except String (List (Bool × term)) :=
  match tm with
  | .Comb (.Comb (.Const "real_add" _) l) r => do
      find_normedterms l (← find_normedterms r acc)
  | .Comb (.Comb (.Const "real_mul" _) c) n =>
      if !(is_ratconst c) then pure acc else do
        pure (augment_norm ((← rat_of_term c) >= 0) n acc)
  | _ => pure (augment_norm true tm acc)

/-- `lincomb_neg` (vectors.ml 727). -/
def lincomb_neg {α : Type} (t : Func α Rat) : Func α Rat := mapf (fun x => -x) t
/-- `lincomb_cmul` (vectors.ml 728). -/
def lincomb_cmul {α : Type} (c : Rat) (t : Func α Rat) : Func α Rat :=
  if c == 0 then undefined else mapf (fun x => c * x) t
/-- `lincomb_add` (vectors.ml 729). -/
def lincomb_add {α : Type} [Ord α] (l r : Func α Rat) : Func α Rat :=
  combine (· + ·) (fun x => x == 0) l r
/-- `lincomb_sub` (vectors.ml 730). -/
def lincomb_sub {α : Type} [Ord α] (l r : Func α Rat) : Func α Rat :=
  lincomb_add l (lincomb_neg r)
/-- `lincomb_eq` (vectors.ml 731). -/
def lincomb_eq {α : Type} [Ord α] (l r : Func α Rat) : Bool :=
  is_undefined (lincomb_sub l r)

/-- `vector_lincomb` (vectors.ml 732-745). -/
partial def vector_lincomb (tm : term) : Except String (Func term Rat) :=
  match tm with
  | .Comb (.Comb (.Const "vector_add" _) l) r => do
      pure (lincomb_add (← vector_lincomb l) (← vector_lincomb r))
  | .Comb (.Comb (.Const "vector_sub" _) l) r => do
      pure (lincomb_sub (← vector_lincomb l) (← vector_lincomb r))
  | .Comb (.Comb (.Const "%" _) l) r => do
      pure (lincomb_cmul (← rat_of_term l) (← vector_lincomb r))
  | .Comb (.Const "vector_neg" _) t => do
      pure (lincomb_neg (← vector_lincomb t))
  | .Comb (.Const "vec" _) n =>
      if HolMath.Nums.is_numeral n && (HolCore.Basics.dest_numeral n).toOption == some 0 then
        pure undefined
      else pure (tm |=> (1 : Rat))
  | _ => pure (tm |=> (1 : Rat))

/-- `vector_lincombs` (vectors.ml 746-752). -/
def vector_lincombs : List term → Except String (List (term × Func term Rat))
  | [] => pure []
  | t :: ts => do
      let fns ← vector_lincombs ts
      if (assoc t fns).toOption.isSome then pure fns else
      let f ← vector_lincomb t
      match find (fun (p : term × Func term Rat) => lincomb_eq f p.2) fns with
      | .ok (_, f') => pure ((t, f') :: fns)
      | .error _ => pure ((t, f) :: fns)

/-- `replacenegnorms` (vectors.ml 753-759). -/
partial def replacenegnorms [HolBase] (fn : ioconv) : ioconv := fun tm =>
  match tm with
  | .Comb (.Comb (.Const "real_add" _) _) _ => BINOP_CONV (replacenegnorms fn) tm
  | .Comb (.Comb (.Const "real_mul" _) c) _ =>
      match rat_of_term c with
      | .ok r => if r < 0 then RAND_CONV fn tm else pure (.ok (REFL tm))
      | .error e => pure (.error e)
  | _ => pure (.ok (REFL tm))

/-- `flip` (vectors.ml 760-761). -/
def flip (v : Int) (eq : Func Int Rat) : Func Int Rat :=
  if defined eq v then
    match apply eq v with
    | .ok x => (v |-> -x) eq
    | .error _ => eq
  else eq

/-- `allsubsets` (vectors.ml 762-766). -/
def allsubsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: t => let res := allsubsets t; res.map (fun b => a :: b) ++ res

/-- `evaluate` (vectors.ml 767-768). -/
def evaluate (env lin : Func Int Rat) : Except String Rat :=
  foldr (fun x c (s : Except String Rat) => do
    let s ← s; pure (s + c * (← apply env x))) lin (pure 0)

/-- `solve` (vectors.ml 769-780).  OCaml's match has no case for variables
    left with no equations (it would raise `Match_failure`); that case cannot
    arise from `vertices`, which passes as many equations as variables. -/
partial def solve : List Int × List (Func Int Rat) → Except String (Func Int Rat)
  | ([], []) => pure ((0 : Int) |=> (1 : Rat))
  | (vs, eq :: oeqs) => do
      let v ← hd (intersect vs (dom eq))
      let c ← apply eq v
      let vdef := lincomb_cmul ((-1 : Rat) / c) eq
      let eliminate (eqn : Func Int Rat) : Except String (Func Int Rat) :=
        if !(defined eqn v) then pure eqn else do
          pure (lincomb_add (lincomb_cmul (← apply eqn v) vdef) eqn)
      let soln ← solve (subtract vs [v], ← oeqs.mapM eliminate)
      pure ((v |-> (← evaluate soln (undefine v vdef))) soln)
  | (_ :: _, []) => throw "solve: Match_failure"

/-- `combinations` (vectors.ml 781-786). -/
def combinations {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, h :: t => (combinations k t).map (fun c => h :: c) ++ combinations (k + 1) t

/-- `vertices` (vectors.ml 787-793). -/
def vertices (vs : List Int) (eqs : List (Func Int Rat)) : List (List Rat) :=
  let vertex (cmb : List (Func Int Rat)) : Except String (List Rat) := do
    let soln ← solve (vs, cmb)
    pure (vs.map (fun v => tryapplyd soln v 0))
  let rawvs := mapfilter vertex (combinations vs.length eqs)
  let unset := rawvs.filter (fun l => l.all (fun c => c >= 0))
  itlist (insert' (forall2 (fun (x y : Rat) => x == y))) unset []

private def ratAbs (x : Rat) : Rat := if x < 0 then -x else x

/-- `subsumes` (vectors.ml 794). -/
def subsumes (l m : List Rat) : Bool := forall2 (fun x y => ratAbs x <= ratAbs y) l m

/-- `subsume` (vectors.ml 795-801). -/
def subsume : List (List Rat) → List (List Rat) → List (List Rat)
  | [], dun => dun
  | v :: ovs, dun =>
      let dun' := if dun.any (fun w => subsumes w v) then dun
                  else v :: dun.filter (fun w => !(subsumes v w))
      subsume ovs dun'

/-- The conversions of `NORM_CANON_CONV` (vectors.ml 819-860) that the
    recursive conversions below use. -/
structure NormCanonConvs where
  (APPLY_pth1 APPLY_pth2 APPLY_pth3 APPLY_pth4 APPLY_pth5 APPLY_pth6 APPLY_pth7
   APPLY_pth8 APPLY_pth9 APPLY_ptha APPLY_pthb APPLY_pthc APPLY_pthd : ioconv)

/-- `headvector` (vectors.ml 861-865). -/
def headvector (tm : term) : Except String term :=
  match tm with
  | .Comb (.Comb (.Const "vector_add" _) (.Comb (.Comb (.Const "%" _) _) v)) _ => pure v
  | .Comb (.Comb (.Const "%" _) _) v => pure v
  | _ => throw "headvector: non-canonical term"

/-- `VECTOR_CMUL_CONV` (vectors.ml 866-868). -/
partial def VECTOR_CMUL_CONV [HolBase] (P : NormCanonConvs) (REAL_RAT_MUL_CONV : ioconv) :
    ioconv := fun tm =>
  ((P.APPLY_pth5 THENC LAND_CONV REAL_RAT_MUL_CONV) ORELSEC
   (P.APPLY_pth6 THENC BINOP_CONV (VECTOR_CMUL_CONV P REAL_RAT_MUL_CONV))) tm

/-- `VECTOR_ADD_CONV` (vectors.ml 869-884). -/
partial def VECTOR_ADD_CONV [HolBase] (P : NormCanonConvs) : ioconv := fun tm => do
  match ← P.APPLY_pth7 tm with
  | .ok th => pure (.ok th)
  | .error _ =>
  match ← P.APPLY_pth8 tm with
  | .ok th => pure (.ok th)
  | .error _ =>
  match tm with
  | .Comb (.Comb (.Const "vector_add" _) lt) rt =>
      match headvector lt, headvector rt with
      | .ok l, .ok r =>
          if compare l r == .lt then
            (P.APPLY_pthb THENC RAND_CONV (VECTOR_ADD_CONV P) THENC P.APPLY_pthd) tm
          else if compare r l == .lt then
            (P.APPLY_pthc THENC RAND_CONV (VECTOR_ADD_CONV P) THENC P.APPLY_pthd) tm
          else
            (P.APPLY_pth9 THENC
              (((P.APPLY_ptha THENC VECTOR_ADD_CONV P) ORELSEC
                RAND_CONV (VECTOR_ADD_CONV P)) THENC
               P.APPLY_pthd)) tm
      | .error e, _ => pure (.error e)
      | _, .error e => pure (.error e)
  | _ => pure (.ok (REFL tm))

/-- `VECTOR_CANON_CONV` (vectors.ml 885-901). -/
partial def VECTOR_CANON_CONV [HolBase] (P : NormCanonConvs) (REAL_RAT_MUL_CONV : ioconv) :
    ioconv := fun tm =>
  match tm with
  | .Comb (.Comb (.Const "vector_add" _) l) r =>
      (do
        let lth ← ExceptT.mk (VECTOR_CANON_CONV P REAL_RAT_MUL_CONV l)
        let rth ← ExceptT.mk (VECTOR_CANON_CONV P REAL_RAT_MUL_CONV r)
        let th ← MK_COMB (← AP_TERM (← liftExcept (rator (← liftExcept (rator tm)))) lth, rth)
        CONV_RULE (RAND_CONV (VECTOR_ADD_CONV P)) th : ExceptT String IO thm).run
  | .Comb (.Comb (.Const "%" _) _) r =>
      (do
        let rth ← AP_TERM (← liftExcept (rator tm))
          (← ExceptT.mk (VECTOR_CANON_CONV P REAL_RAT_MUL_CONV r))
        CONV_RULE (RAND_CONV (P.APPLY_pth4 ORELSEC VECTOR_CMUL_CONV P REAL_RAT_MUL_CONV))
          rth : ExceptT String IO thm).run
  | .Comb (.Comb (.Const "vector_sub" _) _) _ =>
      (P.APPLY_pth2 THENC VECTOR_CANON_CONV P REAL_RAT_MUL_CONV) tm
  | .Comb (.Const "vector_neg" _) _ =>
      (P.APPLY_pth3 THENC VECTOR_CANON_CONV P REAL_RAT_MUL_CONV) tm
  | .Comb (.Const "vec" _) n =>
      if HolMath.Nums.is_numeral n && (HolCore.Basics.dest_numeral n).toOption == some 0 then
        pure (.ok (REFL tm))
      else P.APPLY_pth1 tm
  | _ => P.APPLY_pth1 tm

/-- OCaml's `mapfilter` for a function with effects: keep the results of the
    applications that succeed. -/
def mapfilterIO {α β : Type} (f : α → ExceptT String IO β) :
    List α → ExceptT String IO (List β)
  | [] => pure []
  | h :: t => do
      let rest ← mapfilterIO f t
      let r ← tryCatch (do let y ← f h; pure (some y)) (fun _ => pure none)
      match r with
      | some y => pure (y :: rest)
      | none => pure rest

/-- OCaml's `end_itlist` for a function with effects. -/
def end_itlistIO {α : Type} (f : α → α → ExceptT String IO α) :
    List α → ExceptT String IO α
  | [] => throw "end_itlist"
  | [x] => pure x
  | h :: t => do f h (← end_itlistIO f t)

/-- OCaml's `itlist` for a function with effects. -/
def itlistIO {α β : Type} (f : α → β → ExceptT String IO β) :
    List α → β → ExceptT String IO β
  | [], b => pure b
  | h :: t, b => do f h (← itlistIO f t b)

end NormArith

open NormArith

structure NormArithB where
  NORM_ARITH : term → ExceptT String IO thm
  NORM_ARITH_TAC : tactic
  ASM_NORM_ARITH_TAC : tactic
  deriving Inhabited

@[nospecialize]
def setupNormArith [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BNorm1 : Norm1) : ExceptT String IO NormArithB := do
  -- @@SCOPE BEGIN
  let { REAL_ARITH, REAL_ARITH_TAC, GEN_REAL_ARITH, REAL_LINEAR_PROVER, GEN_NNF_CONV,
        term_of_rat, REAL_POLY_CONV, REAL_POLY_NEG_CONV, REAL_RAT_ADD_CONV,
        REAL_RAT_MUL_CONV, REAL_RAT_REDUCE_CONV, .. } := D
  let { DECIMAL, .. } := D.core1
  let { REAL_ABS_POS, REAL_LE_ADD2, REAL_LE_LMUL, .. } := D.core3
  let { real_ge, .. } := D.core5
  let { VECTOR_ARITH, VECTOR_SUB_EQ, .. } := BVectorArith
  let { NORM_0, NORM_LE_0, NORM_MUL, NORM_POS_LE, NORM_TRIANGLE_LE, dist, .. } := BNorm1
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let NORM_CMUL_RULE : Rat → thm → ExceptT String IO thm ← do
    let pth ← prove
     r"!b x. b >= norm(x) ==> !c. abs(c) * b >= norm(c % x)"
     (SIMP_TAC [NORM_MUL, real_ge, REAL_LE_LMUL, REAL_ABS_POS])
    pure (fun c th => do ISPEC (← liftExcept (term_of_rat c)) (← MATCH_MP pth th))
  let NORM_ADD_RULE : thm → thm → ExceptT String IO thm ← do
    let pth ← prove
     r"!b1 b2 x1 x2. b1 >= norm(x1) /\ b2 >= norm(x2)
                     ==> b1 + b2 >= norm(x1 + x2)"
     (REWRITE_TAC [real_ge] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC NORM_TRIANGLE_LE THEN ASM_SIMP_TAC [REAL_LE_ADD2])
    pure (fun th1 th2 => do MATCH_MP pth (← CONJ th1 th2))
  let INEQUALITY_CANON_RULE : thm → ExceptT String IO thm ← do
    let c ← GEN_REWRITE_CONV_NET id [← REAL_ARITH (← q r"s >= t <=> s - t >= &0")]
    pure (fun th => do
      CONV_RULE (LAND_CONV REAL_POLY_CONV)
        (← CONV_RULE (LAND_CONV REAL_RAT_REDUCE_CONV) (← CONV_RULE c th)))
  let NORM_CANON_CONV : ioconv ← do
    let APPLY_pth1 ← GEN_REWRITE_CONV_NET id [← va r"x:real^N = &1 % x"]
    let APPLY_pth2 ← GEN_REWRITE_CONV_NET id [← va r"x - y:real^N = x + --y"]
    let APPLY_pth3 ← GEN_REWRITE_CONV_NET id [← va r"--x:real^N = -- &1 % x"]
    let APPLY_pth4 ← GEN_REWRITE_CONV_NET id
     [← va r"&0 % x:real^N = vec 0",
      ← va r"c % vec 0:real^N = vec 0"]
    let APPLY_pth5 ← GEN_REWRITE_CONV_NET id [← va r"c % (d % x) = (c * d) % x"]
    let APPLY_pth6 ← GEN_REWRITE_CONV_NET id [← va r"c % (x + y) = c % x + c % y"]
    let APPLY_pth7 ← GEN_REWRITE_CONV_NET id
     [← va r"vec 0 + x = x",
      ← va r"x + vec 0 = x"]
    let APPLY_pth8 :=
     (← GEN_REWRITE_CONV_NET id [← va r"c % x + d % x = (c + d) % x"]) THENC
     LAND_CONV REAL_RAT_ADD_CONV THENC
     (← GEN_REWRITE_CONV_NET TRY_CONV [← va r"&0 % x = vec 0"])
    let APPLY_pth9 :=
     (← GEN_REWRITE_CONV_NET id
      [← va r"(c % x + z) + d % x = (c + d) % x + z",
       ← va r"c % x + (d % x + z) = (c + d) % x + z",
       ← va r"(c % x + w) + (d % x + z) = (c + d) % x + (w + z)"]) THENC
     LAND_CONV (LAND_CONV REAL_RAT_ADD_CONV)
    let APPLY_ptha ← GEN_REWRITE_CONV_NET id [← va r"&0 % x + y = y"]
    let APPLY_pthb ← GEN_REWRITE_CONV_NET id
      [← va r"c % x + d % y = c % x + d % y",
       ← va r"(c % x + z) + d % y = c % x + (z + d % y)",
       ← va r"c % x + (d % y + z) = c % x + (d % y + z)",
       ← va r"(c % x + w) + (d % y + z) = c % x + (w + (d % y + z))"]
    let APPLY_pthc ← GEN_REWRITE_CONV_NET id
      [← va r"c % x + d % y = d % y + c % x",
       ← va r"(c % x + z) + d % y = d % y + (c % x + z)",
       ← va r"c % x + (d % y + z) = d % y + (c % x + z)",
       ← va r"(c % x + w) + (d % y + z) = d % y + ((c % x + w) + z)"]
    let APPLY_pthd ← GEN_REWRITE_CONV_NET TRY_CONV [← va r"x + vec 0 = x"]
    let P : NormCanonConvs :=
      { APPLY_pth1, APPLY_pth2, APPLY_pth3, APPLY_pth4, APPLY_pth5, APPLY_pth6,
        APPLY_pth7, APPLY_pth8, APPLY_pth9, APPLY_ptha, APPLY_pthb, APPLY_pthc,
        APPLY_pthd }
    pure (fun tm =>
      match tm with
      | .Comb (.Const "vector_norm" _) _ => RAND_CONV (VECTOR_CANON_CONV P REAL_RAT_MUL_CONV) tm
      | _ => pure (.error "NORM_CANON_CONV"))
  let REAL_VECTOR_COMBO_PROVER :
      HolMath.RealArith.PsTranslator → List thm × List thm × List thm →
      ExceptT String IO thm ← do
    let pth_zero ← prove r"norm(vec 0:real^N) = &0" (REWRITE_TAC [NORM_0])
    let tv_n := mk_vartype "N"
    pure (fun translator (nubs, ges, gts) => do
      let sources ← liftExcept (nubs.mapM (fun th => do rand (← rand (concl th))))
      let rawdests ← liftExcept ((ges ++ gts).foldrM
        (fun th acc => do find_normedterms (← lhand (concl th)) acc) [])
      if !(rawdests.all (fun p => p.1)) then throw "Sanity check"
      let dests := setify (rawdests.map (fun p => p.2))
      let srcfuns ← liftExcept (sources.mapM vector_lincomb)
      let destfuns ← liftExcept (dests.mapM vector_lincomb)
      let vvs := itlist (fun (f : Func term Rat) acc => union (dom f) acc) (srcfuns ++ destfuns) []
      let n := srcfuns.length
      let nvs := upto 1 n
      let srccombs ← liftExcept (zip srcfuns nvs)
      let consider (d : Func term Rat) : Except String (List (List Rat)) := do
        let coefficients (x : term) : Except String (Func Int Rat) := do
          let inp ← if defined d x then do pure ((0 : Int) |=> -(← apply d x))
                    else pure undefined
          srccombs.foldrM (fun (fv : Func term Rat × Int) g =>
            if defined fv.1 x then do pure ((fv.2 |-> (← apply fv.1 x)) g) else pure g) inp
        let equations ← vvs.mapM coefficients
        let inequalities := nvs.map (fun n => (n |=> (1 : Rat)))
        let plausiblevertices (f : List Int) : Except String (List (List Rat)) := do
          let flippedequations := equations.map (fun e => itlist flip f e)
          let constraints := flippedequations ++ inequalities
          let rawverts := vertices nvs constraints
          let check_solution (v : List Rat) : Except String Bool := do
            let f ← itlist2 (fun a b g => (a |-> b) g) nvs v ((0 : Int) |=> (1 : Rat))
            flippedequations.allM (fun e => do pure ((← evaluate f e) == 0))
          let goodverts ← rawverts.filterM check_solution
          let signfixups := nvs.map (fun n => if mem n f then (-1 : Int) else 1)
          goodverts.mapM (fun gv => map2 (fun (s : Int) c => (s : Rat) * c) signfixups gv)
        let allverts := itlist (· ++ ·) (← (allsubsets nvs).mapM plausiblevertices) []
        pure (subsume allverts [])
      let compute_ineq (v : List Rat) : ExceptT String IO thm := do
        let ths ← mapfilterIO (fun (p : Rat × thm) =>
          if p.1 == 0 then throw "fail" else NORM_CMUL_RULE p.1 p.2) (← liftExcept (zip v nubs))
        INEQUALITY_CANON_RULE (← end_itlistIO NORM_ADD_RULE ths)
      let considered := List.flatten (← liftExcept (destfuns.mapM consider))
      let ges' := (← mapfilterIO compute_ineq considered) ++
                  (← nubs.mapM INEQUALITY_CANON_RULE) ++ ges
      let zerodests ← liftExcept ((rawdests.map (fun p => p.2)).filterM
        (fun t => do pure (dom (← vector_lincomb t)).isEmpty))
      let canon := ONCE_DEPTH_CONV NORM_CANON_CONV THENC LAND_CONV REAL_POLY_CONV
      let zs ← zerodests.mapM (fun t => do
        let (_, args) ← liftExcept (dest_type (type_of t))
        HolLight.INST_TYPE [(← liftExcept (last args), tv_n)] pth_zero)
      let gs ← ges'.mapM (CONV_RULE canon)
      let ts ← gts.mapM (CONV_RULE canon)
      ExceptT.mk (REAL_LINEAR_PROVER translator (zs, gs, ts)))
  let REAL_VECTOR_INEQ_PROVER :
      HolMath.RealArith.PsTranslator → List thm × List thm → ExceptT String IO thm ← do
    let pth ← prove
     r"norm(x) = n ==> norm(x) >= &0 /\ n >= norm(x)"
     (DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
      REWRITE_TAC [real_ge, NORM_POS_LE] THEN REAL_ARITH_TAC)
    let NORM_MP (th : thm) : ExceptT String IO thm := MATCH_MP pth th
    pure (fun translator (ges, gts) => do
      let ntms ← liftExcept ((ges ++ gts).foldrM
        (fun th acc => do find_normedterms (← lhand (concl th)) acc) [])
      let lctab ← liftExcept (vector_lincombs ((ntms.filter (fun p => !p.1)).map (fun p => p.2)))
      let mkEq ← ExceptT.mk (mk_eq : IO _)
      let asl ← lctab.mapM (fun (p : term × Func term Rat) => do
        let nrm ← ExceptT.mk (mk_const "vector_norm" [])
        let lhs ← liftExcept (HolCore.Basics.mk_icomb nrm p.1)
        let v ← (HolCore.Basics.genvar (← qty "real") : IO term)
        ASSUME (← liftExcept (mkEq (lhs, v))))
      let replace_conv := GEN_REWRITE_CONV TRY_CONV asl
      let replace_rule (th : thm) : ExceptT String IO thm :=
        CONV_RULE (LAND_CONV (replacenegnorms replace_conv)) th
      let ges' ← itlistIO (fun th ths => do pure ((← CONJUNCT1 (← NORM_MP th)) :: ths))
                   asl (← ges.mapM replace_rule)
      let gts' ← gts.mapM replace_rule
      let nubs ← asl.mapM (fun th => do CONJUNCT2 (← NORM_MP th))
      let th1 ← REAL_VECTOR_COMBO_PROVER translator (nubs, ges', gts')
      let th2 ← INST (← liftExcept (asl.mapM (fun th => dest_eq (concl th)))) th1
      itlistIO PROVE_HYP (← liftExcept (asl.mapM (fun th => do pure (REFL (← lhand (concl th)))))) th2)
  let REAL_VECTOR_PROVER : HolMath.RealArith.PsProver ← do
    let rawrule ← GEN_REWRITE_CONV_NET id
      [← REAL_ARITH (← q r"x = &0 <=> x >= &0 /\ --x >= &0")]
    let splitequation (th : thm) (acc : List thm) : ExceptT String IO (List thm) := do
      let (th1, th2) ← CONJ_PAIR (← CONV_RULE rawrule th)
      pure (th1 :: (← CONV_RULE (LAND_CONV REAL_POLY_NEG_CONV) th2) :: acc)
    pure (fun translator (eqs, ges, gts) => (do
      REAL_VECTOR_INEQ_PROVER translator (← itlistIO splitequation eqs ges, gts)).run)
  let pth ← prove
   r"(!x y:real^N. x = y <=> norm(x - y) <= &0) /\
     (!x y:real^N. ~(x = y) <=> ~(norm(x - y) <= &0))"
   (REWRITE_TAC [NORM_LE_0, VECTOR_SUB_EQ])
  let conv1 ← GEN_REWRITE_CONV_NET TRY_CONV [pth]
  let conv2 : HolCore.Canon.dconv := fun tm => (do
    let a ← ExceptT.mk (conv1 tm)
    let b ← ExceptT.mk (conv1 (← liftExcept (HolCore.Bool.mk_neg tm)))
    pure (a, b) : ExceptT String IO (thm × thm)).run
  let init :=
    (← GEN_REWRITE_CONV_NET ONCE_DEPTH_CONV [DECIMAL]) THENC
    REAL_RAT_REDUCE_CONV THENC
    (← GEN_REWRITE_CONV_NET ONCE_DEPTH_CONV [dist]) THENC
    GEN_NNF_CONV true conv1 conv2
  let pure_ := GEN_REAL_ARITH REAL_VECTOR_PROVER
  let NORM_ARITH (tm : term) : ExceptT String IO thm := do
    let th ← ExceptT.mk (init tm)
    HolLight.EQ_MP (← SYM th) (← pure_ (← liftExcept (rand (concl th))))

  let NORM_ARITH_TAC := CONV_TAC (fun t => NORM_ARITH t)

  let ASM_NORM_ARITH_TAC :=
    REPEAT (FIRST_X_ASSUM (fun th => tactic_of do
      pure (MP_TAC (← liftExcept (check (fun (t : thm) => !(HolCore.Basics.is_forall (concl t))) th))))) THEN
    NORM_ARITH_TAC

  return { NORM_ARITH, NORM_ARITH_TAC, ASM_NORM_ARITH_TAC }

/- ------------------------------------------------------------------------- -/
/- No non-trivial homomorphisms R->R; the dot product via the norm;         -/
/- equality via dot products; more metric properties; rescaling.            -/
/- (vectors.ml 1007-1213)                                                     -/
/- ------------------------------------------------------------------------- -/

structure Metric where
  HOMOMORPHISM_REAL_TO_REAL : thm
  DOT_NORM : thm
  DOT_NORM_SUB : thm
  VECTOR_EQ : thm
  DIST_REFL : thm
  DIST_SYM : thm
  DIST_POS_LE : thm
  REAL_ABS_DIST : thm
  DIST_TRIANGLE : thm
  DIST_TRIANGLE_ALT : thm
  DIST_EQ_0 : thm
  DIST_POS_LT : thm
  DIST_NZ : thm
  DIST_TRIANGLE_LE : thm
  DIST_TRIANGLE_LT : thm
  DIST_TRIANGLE_HALF_L : thm
  DIST_TRIANGLE_HALF_R : thm
  DIST_TRIANGLE_ADD : thm
  DIST_MUL : thm
  DIST_TRIANGLE_ADD_HALF : thm
  DIST_LE_0 : thm
  DIST_EQ : thm
  DIST_0 : thm
  DIST_RESCALE : thm
  DIST_DESCALE : thm
  deriving Inhabited

@[nospecialize]
def setupMetric [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BDotProps : DotProps) (BNorm1 : Norm1) (BNorm2 : Norm2) (BNormArith : NormArithB) :
    ExceptT String IO Metric := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INDUCT_TAC, MESON_TAC, REAL_ARITH,
        REAL_ARITH_TAC, REAL_FIELD, REAL_RING, .. } := D
  let { ADD1, EQ_TRANS, .. } := D.core1
  let { FUN_EQ_THM, LEFT_IMP_EXISTS_THM, NOT_FORALL_THM, .. } := D.core2
  let { REAL_ABS_MUL, REAL_ABS_POS, REAL_ADD_LID, REAL_DIV_LMUL,
        REAL_EQ_ADD_LCANCEL_0, REAL_LE_ANTISYM, REAL_LE_LMUL, REAL_LE_MUL,
        REAL_LE_POW_2, REAL_LE_RMUL, REAL_LE_SQUARE, REAL_LE_TOTAL, REAL_LE_TRANS,
        REAL_LT_ANTISYM, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LINV,
        REAL_MUL_LZERO, .. } := D.core3
  let { REAL_NOT_LE, REAL_OF_NUM_ADD, REAL_POS, REAL_POW2_ABS, REAL_POW_2,
        REAL_POW_MUL, REAL_SUB_0, REAL_SUB_LE, REAL_SUB_RDISTRIB, REAL_WLOG_LE,
        SQRT_POW2, .. } := D.core4
  let { is_int, real_abs, real_ge, real_min, real_sub, .. } := D.core5
  let { RATIONAL_BETWEEN, rational, .. } := D.lib
  let { VECTOR_ARITH, VECTOR_SUB_EQ, VECTOR_SUB_LDISTRIB, .. } := BVectorArith
  let { DOT_EQ_0, DOT_LADD, DOT_LMUL, DOT_LSUB, DOT_RADD, DOT_RMUL, DOT_RSUB,
        DOT_SYM, .. } := BDotProps
  let { NORM_CAUCHY_SCHWARZ_ABS, NORM_MUL, NORM_POS_LE, NORM_POW_2, dist, .. } := BNorm1
  let { NORM_EQ, NORM_EQ_SQUARE, NORM_GE_SQUARE, .. } := BNorm2
  let { NORM_ARITH_TAC, .. } := BNormArith
  -- @@SCOPE END

  let HOMOMORPHISM_REAL_TO_REAL ← prove
   r"!f:real->real.
        (!x y. f(x + y) = f x + f y) /\ (!x y. f(x * y) = f x * f y) <=>
        (f = \x. &0) \/ (f = \x. x)"
   (GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [REAL_ADD_LID, REAL_MUL_LZERO] THEN
    REWRITE_TAC [FUN_EQ_THM, ← TAUT (← q r"p \/ q <=> ~p ==> q")] THEN
    REWRITE_TAC [NOT_FORALL_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"(f:real->real)(&0) = &0") ASSUME_TAC THENL
     [ASM_MESON_TAC [REAL_EQ_ADD_LCANCEL_0], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(f:real->real)(&1) = &1") ASSUME_TAC THENL
     [ASM_MESON_TAC [REAL_MUL_LID, ← REAL_RING (← q r"x = y * x <=> y = &1 \/ x = &0")],
      FIRST_X_ASSUM (CHOOSE_THEN (K ALL_TAC))] THEN
    SUBGOAL_THEN (← q r"!x. (f:real->real)(--x) = --(f x)") ASSUME_TAC THENL
     [ASM_MESON_TAC [← REAL_ARITH (← q r"x:real = --y <=> x + y = &0")], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x y. (f:real->real)(x - y) = f x - f y") ASSUME_TAC THENL
     [ASM_REWRITE_TAC [real_sub], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x. (f:real->real) x = &0 <=> x = &0") ASSUME_TAC THENL
     [GEN_TAC THEN EQ_TAC THEN ASM_SIMP_TAC [] THEN DISCH_TAC THEN
      ASM_CASES_TAC (← q r"x:real = &0") THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"(f:real->real)(inv x * x) = f(&1)") MP_TAC THENL
       [ASM_MESON_TAC [REAL_MUL_LINV], ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x y. (f:real->real) x = f y <=> x = y") ASSUME_TAC THENL
     [ASM_MESON_TAC [REAL_SUB_0], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x y. x <= y ==> (f:real->real) x <= f y") ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM REAL_SUB_LE] THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        pure (GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← GSYM th])) THEN
      SPEC_TAC (← q r"y - x:real", ← q r"z:real") THEN GEN_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM SQRT_POW2] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC [REAL_POW_2, REAL_LE_SQUARE],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x y. (f:real->real) x <= f y <=> x <= y") ASSUME_TAC THENL
     [ASM_MESON_TAC [REAL_LE_TOTAL, REAL_LE_ANTISYM], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x y. (f:real->real) x < f y <=> x < y") ASSUME_TAC THENL
     [ASM_REWRITE_TAC [← GSYM REAL_NOT_LE], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!n. (f:real->real)(&n) = &n") ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM_REWRITE_TAC [ADD1, ← GSYM REAL_OF_NUM_ADD], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x. integer x ==> f x = x") ASSUME_TAC THENL
     [REWRITE_TAC [is_int] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x. rational x ==> f x = x") ASSUME_TAC THENL
     [REWRITE_TAC [rational, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"z:real", ← q r"x:real", ← q r"y:real"] THEN
      STRIP_TAC THEN ASM_SIMP_TAC [← REAL_FIELD (← q
       r"~(y = &0) ==> (z = x / y <=> y * z = x)")] THEN
      TRANS_TAC EQ_TRANS (← q r"(f:real->real) y * f(x / y)") THEN CONJ_TAC THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [← GSYM th])) THEN
      ASM_SIMP_TAC [REAL_DIV_LMUL],
      ALL_TAC] THEN
    X_GEN_TAC (← q r"x:real") THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"~(x < y) /\ ~(y < x) ==> x:real = y")) THEN
    CONJ_TAC THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"q:real") MP_TAC o MATCH_MP RATIONAL_BETWEEN) THEN
    ASM_MESON_TAC [REAL_LT_ANTISYM])

  let DOT_NORM ← prove
   r"!x y. x dot y = (norm(x + y) pow 2 - norm(x) pow 2 - norm(y) pow 2) / &2"
   (REWRITE_TAC [NORM_POW_2, DOT_LADD, DOT_RADD, DOT_SYM] THEN REAL_ARITH_TAC)

  let DOT_NORM_SUB ← prove
   r"!x y. x dot y = ((norm(x) pow 2 + norm(y) pow 2) - norm(x - y) pow 2) / &2"
   (REWRITE_TAC [NORM_POW_2, DOT_LSUB, DOT_RSUB, DOT_SYM] THEN REAL_ARITH_TAC)

  let VECTOR_EQ ← prove
   r"!x y. (x = y) <=> (x dot x = x dot y) /\ (y dot y = x dot x)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL [SIMP_TAC [], ALL_TAC] THEN
    ONCE_REWRITE_TAC [← GSYM VECTOR_SUB_EQ] THEN
    REWRITE_TAC [← GSYM DOT_EQ_0] THEN
    SIMP_TAC [DOT_LSUB, DOT_RSUB, DOT_SYM] THEN REAL_ARITH_TAC)

  let DIST_REFL ← prove r"!x. dist(x,x) = &0" NORM_ARITH_TAC
  let DIST_SYM ← prove r"!x y. dist(x,y) = dist(y,x)" NORM_ARITH_TAC
  let DIST_POS_LE ← prove r"!x y. &0 <= dist(x,y)" NORM_ARITH_TAC
  let REAL_ABS_DIST ← prove r"!x y:real^N. abs(dist(x,y)) = dist(x,y)" NORM_ARITH_TAC
  let DIST_TRIANGLE ← prove r"!x:real^N y z. dist(x,z) <= dist(x,y) + dist(y,z)"
    NORM_ARITH_TAC
  let DIST_TRIANGLE_ALT ← prove r"!x y z. dist(y,z) <= dist(x,y) + dist(x,z)"
    NORM_ARITH_TAC
  let DIST_EQ_0 ← prove r"!x y. (dist(x,y) = &0) <=> (x = y)" NORM_ARITH_TAC
  let DIST_POS_LT ← prove r"!x y. ~(x = y) ==> &0 < dist(x,y)" NORM_ARITH_TAC
  let DIST_NZ ← prove r"!x y. ~(x = y) <=> &0 < dist(x,y)" NORM_ARITH_TAC
  let DIST_TRIANGLE_LE ← prove
   r"!x y z e. dist(x,z) + dist(y,z) <= e ==> dist(x,y) <= e" NORM_ARITH_TAC
  let DIST_TRIANGLE_LT ← prove
   r"!x y z e. dist(x,z) + dist(y,z) < e ==> dist(x,y) < e" NORM_ARITH_TAC
  let DIST_TRIANGLE_HALF_L ← prove
   r"!x1 x2 y. dist(x1,y) < e / &2 /\ dist(x2,y) < e / &2 ==> dist(x1,x2) < e"
   NORM_ARITH_TAC
  let DIST_TRIANGLE_HALF_R ← prove
   r"!x1 x2 y. dist(y,x1) < e / &2 /\ dist(y,x2) < e / &2 ==> dist(x1,x2) < e"
   NORM_ARITH_TAC
  let DIST_TRIANGLE_ADD ← prove
   r"!x x' y y'. dist(x + y,x' + y') <= dist(x,x') + dist(y,y')" NORM_ARITH_TAC

  let DIST_MUL ← prove
   r"!x y c. dist(c % x,c % y) = abs(c) * dist(x,y)"
   (REWRITE_TAC [dist, ← GSYM VECTOR_SUB_LDISTRIB, NORM_MUL])

  let DIST_TRIANGLE_ADD_HALF ← prove
   r"!x x' y y':real^N.
    dist(x,x') < e / &2 /\ dist(y,y') < e / &2 ==> dist(x + y,x' + y') < e"
   NORM_ARITH_TAC

  let DIST_LE_0 ← prove r"!x y. dist(x,y) <= &0 <=> x = y" NORM_ARITH_TAC

  let DIST_EQ ← prove
   r"!w x y z. dist(w,x) = dist(y,z) <=> dist(w,x) pow 2 = dist(y,z) pow 2"
   (REWRITE_TAC [dist, NORM_POW_2, NORM_EQ])

  let DIST_0 ← prove r"!x. dist(x,vec 0) = norm(x) /\ dist(vec 0,x) = norm(x)"
    NORM_ARITH_TAC

  let DIST_RESCALE ← prove
   r"!a x y:real^N. norm(x) = norm(y) ==> dist(a % x,y) = dist(x,a % y)"
   (SIMP_TAC [dist, NORM_EQ_SQUARE, NORM_POS_LE, NORM_POW_2] THEN
    REWRITE_TAC [DOT_LSUB, DOT_RSUB, DOT_LMUL, DOT_RMUL] THEN
    CONV_TAC (fun t => REAL_RING t))

  let DIST_DESCALE ← prove
   r"!a b x y:real^N.
        &0 <= a /\ &0 <= b /\ norm(x) = norm(y)
        ==> dist(a % x,b % y) >= min a b * dist(x,y)"
   (MATCH_MP_TAC REAL_WLOG_LE THEN CONJ_TAC THENL
     [MESON_TAC [DIST_SYM, ← REAL_ARITH (← q r"min a b:real = min b a")], ALL_TAC] THEN
    SIMP_TAC [real_min] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [dist, NORM_GE_SQUARE, REAL_POW_MUL, NORM_POW_2] THEN
    DISJ2_TAC THEN REWRITE_TAC [real_ge] THEN REWRITE_TAC [← VECTOR_ARITH (← q
     r"(x - y:real^N) dot (x - y) = (x dot x + y dot y) - &2 * x dot y")] THEN
    ASM_REWRITE_TAC [← GSYM NORM_POW_2, NORM_MUL, real_abs, ← REAL_ARITH (← q
     r"a pow 2 * ((y pow 2 + y pow 2) - &2 * d) <=
    ((a * y) pow 2 + (b * y) pow 2) - &2 * e <=>
    &2 * (e - a pow 2 * d) <= (b pow 2 - a pow 2) * y pow 2")] THEN
    REWRITE_TAC [DOT_LMUL] THEN REWRITE_TAC [DOT_RMUL] THEN
    REWRITE_TAC [REAL_POW2_ABS, REAL_MUL_ASSOC, ← GSYM REAL_SUB_RDISTRIB] THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"abs a <= b ==> a <= b")) THEN
    ONCE_REWRITE_TAC [REAL_ABS_MUL] THEN TRANS_TAC REAL_LE_TRANS
      (← q r"abs (&2 * (a * b - a pow 2)) * norm(x:real^N) * norm(y:real^N)") THEN
    SIMP_TAC [REAL_LE_LMUL, REAL_ABS_POS, NORM_CAUCHY_SCHWARZ_ABS] THEN
    ASM_REWRITE_TAC [← GSYM REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC [REAL_LE_POW_2] THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"&0 <= x /\ x <= y ==> abs x <= y")) THEN
    REWRITE_TAC [← REAL_ARITH (← q r"(a * b - a pow 2):real = a * (b - a)")] THEN
    ASM_SIMP_TAC [REAL_LE_MUL, REAL_POS, REAL_SUB_LE] THEN
    REWRITE_TAC [REAL_MUL_ASSOC, ← REAL_ARITH (← q
     r"(b pow 2 - a pow 2):real = (a + b) * (b - a)")] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC)

  return { HOMOMORPHISM_REAL_TO_REAL, DOT_NORM, DOT_NORM_SUB, VECTOR_EQ, DIST_REFL,
           DIST_SYM, DIST_POS_LE, REAL_ABS_DIST, DIST_TRIANGLE, DIST_TRIANGLE_ALT,
           DIST_EQ_0, DIST_POS_LT, DIST_NZ, DIST_TRIANGLE_LE, DIST_TRIANGLE_LT,
           DIST_TRIANGLE_HALF_L, DIST_TRIANGLE_HALF_R, DIST_TRIANGLE_ADD, DIST_MUL,
           DIST_TRIANGLE_ADD_HALF, DIST_LE_0, DIST_EQ, DIST_0, DIST_RESCALE,
           DIST_DESCALE }

/- ------------------------------------------------------------------------- -/
/- Sums of vectors.  (vectors.ml 1215-1457)                                  -/
/- ------------------------------------------------------------------------- -/

structure VSum1 where
  NEUTRAL_VECTOR_ADD : thm
  MONOIDAL_VECTOR_ADD : thm
  vsum : thm
  VSUM_CLAUSES : thm
  VSUM : thm
  VSUM_EQ_0 : thm
  VSUM_0 : thm
  VSUM_LMUL : thm
  VSUM_RMUL : thm
  VSUM_ADD : thm
  VSUM_SUB : thm
  VSUM_CONST : thm
  VSUM_COMPONENT : thm
  VSUM_IMAGE : thm
  VSUM_UNION : thm
  VSUM_DIFF : thm
  VSUM_DELETE : thm
  VSUM_INCL_EXCL : thm
  VSUM_NEG : thm
  VSUM_EQ : thm
  VSUM_SUPERSET : thm
  VSUM_SUPPORT : thm
  VSUM_UNIV : thm
  VSUM_EQ_SUPERSET : thm
  VSUM_UNION_RZERO : thm
  VSUM_UNION_LZERO : thm
  VSUM_RESTRICT : thm
  VSUM_RESTRICT_SET : thm
  VSUM_CASES : thm
  VSUM_SING : thm
  VSUM_NORM : thm
  VSUM_NORM_LE : thm
  VSUM_NORM_TRIANGLE : thm
  VSUM_NORM_BOUND : thm
  VSUM_CLAUSES_NUMSEG : thm
  VSUM_CLAUSES_RIGHT : thm
  VSUM_CMUL_NUMSEG : thm
  VSUM_EQ_NUMSEG : thm
  VSUM_IMAGE_GEN : thm
  VSUM_GROUP : thm
  VSUM_GROUP_RELATION : thm
  VSUM_VMUL : thm
  VSUM_DELTA : thm
  VSUM_ADD_NUMSEG : thm
  deriving Inhabited

@[nospecialize]
def setupVSum1 [HolBase] (D : VectorsDeps) (BBasics : Basics) (BVectorArith : VectorArith)
    (BNorm1 : Norm1) (BNormArith : NormArithB) : ExceptT String IO VSum1 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, INDUCT_TAC, MESON_TAC, SET_TAC, new_definition, .. } := D
  let { CART_EQ, FINITE_INDEX_INRANGE, FINITE_INDUCT_STRONG, FINITE_NUMSEG,
        FINITE_RULES, .. } := D.core1
  let { IN_NUMSEG, ITERATE_CLAUSES, LAMBDA_BETA, LT_REFL, NOT_IN_EMPTY,
        NUMSEG_CLAUSES, .. } := D.core2
  let { REAL_LE_REFL, REAL_LE_TRANS, .. } := D.core3
  let { SELECT_UNIQUE, SUC_SUB1, SUM_ADD, SUM_CASES, SUM_CLAUSES, SUM_CONST,
        SUM_DELETE, SUM_DELTA, SUM_DIFF, SUM_EQ, SUM_EQ_0, SUM_GROUP, .. } := D.core4
  let { SUM_GROUP_RELATION, SUM_IMAGE, SUM_IMAGE_GEN, SUM_INCL_EXCL, SUM_LE,
        SUM_LMUL, SUM_NEG, SUM_RESTRICT_SET, SUM_RMUL, SUM_SUB, SUM_SUPERSET,
        SUM_UNION, monoidal, neutral, o_DEF, support, .. } := D.core5
  let { vec, .. } := BBasics
  let { COND_COMPONENT, VECTOR_ADD_AC, VECTOR_ADD_COMPONENT, VECTOR_ADD_RID,
        VECTOR_ARITH, VECTOR_ARITH_TAC, VECTOR_MUL_COMPONENT, VECTOR_NEG_COMPONENT,
        VECTOR_SUB_COMPONENT, VEC_COMPONENT, .. } := BVectorArith
  let { NORM_0, .. } := BNorm1
  let { NORM_ARITH_TAC, .. } := BNormArith
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let NEUTRAL_VECTOR_ADD ← prove
   r"neutral(+) = vec 0:real^N"
   (REWRITE_TAC [neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    REWRITE_TAC [← va r"x + y = y <=> x = vec 0",
                 ← va r"x + y = x <=> y = vec 0"])

  let MONOIDAL_VECTOR_ADD ← prove
   r"monoidal((+):real^N->real^N->real^N)"
   (REWRITE_TAC [monoidal, NEUTRAL_VECTOR_ADD] THEN
    REPEAT CONJ_TAC THEN VECTOR_ARITH_TAC)

  let vsum ← new_definition
   r"(vsum:(A->bool)->(A->real^N)->real^N) s f = lambda i. sum s (\x. f(x)$i)"

  let VSUM_CLAUSES ← prove
   r"(!f. vsum {} f = vec 0) /\
   (!x f s. FINITE s
            ==> (vsum (x INSERT s) f =
                 if x IN s then vsum s f else f(x) + vsum s f))"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, VECTOR_ADD_COMPONENT, SUM_CLAUSES] THEN
    SIMP_TAC [VEC_COMPONENT] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [LAMBDA_BETA, VECTOR_ADD_COMPONENT])

  let VSUM ← prove
   r"!f s. FINITE s ==> vsum s f = iterate (+) s f"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [VSUM_CLAUSES, ITERATE_CLAUSES, MONOIDAL_VECTOR_ADD] THEN
    REWRITE_TAC [NEUTRAL_VECTOR_ADD])

  let VSUM_EQ_0 ← prove
   r"!f s. (!x:A. x IN s ==> (f(x) = vec 0)) ==> (vsum s f = vec 0)"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, vec, SUM_EQ_0])

  let VSUM_0 ← prove
   r"vsum s (\x. vec 0) = vec 0"
   (SIMP_TAC [VSUM_EQ_0])

  let VSUM_LMUL ← prove
   r"!f c s.  vsum s (\x. c % f(x)) = c % vsum s f"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, VECTOR_MUL_COMPONENT, SUM_LMUL])

  let VSUM_RMUL ← prove
   r"!c s v. vsum s (\x. c x % v) = (sum s c) % v"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, VECTOR_MUL_COMPONENT, SUM_RMUL])

  let VSUM_ADD ← prove
   r"!f g s. FINITE s ==> (vsum s (\x. f x + g x) = vsum s f + vsum s g)"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, VECTOR_ADD_COMPONENT, SUM_ADD])

  let VSUM_SUB ← prove
   r"!f g s. FINITE s ==> (vsum s (\x. f x - g x) = vsum s f - vsum s g)"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, VECTOR_SUB_COMPONENT, SUM_SUB])

  let VSUM_CONST ← prove
   r"!c s. FINITE s ==> (vsum s (\n. c) = &(CARD s) % c)"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, SUM_CONST, VECTOR_MUL_COMPONENT])

  let VSUM_COMPONENT ← prove
   r"!s f:A->real^N i. vsum s f$i = sum s (\x. f x$i)"
   (REPEAT GEN_TAC THEN SUBGOAL_THEN
      (← q r"?k. 1 <= k /\ k <= dimindex(:N) /\ !z:real^N. z$i = z$k") CHOOSE_TAC THENL
    [REWRITE_TAC [FINITE_INDEX_INRANGE],
     ASM_SIMP_TAC [vsum, LAMBDA_BETA]])

  let VSUM_IMAGE ← prove
   r"!f g s. FINITE s /\ (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> (vsum (IMAGE f s) g = vsum s (g o f))"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
    W (MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE o lhs o snd) THEN
    ASM_REWRITE_TAC [o_DEF])

  let VSUM_UNION ← prove
   r"!f s t. FINITE s /\ FINITE t /\ DISJOINT s t
           ==> (vsum (s UNION t) f = vsum s f + vsum t f)"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, SUM_UNION, VECTOR_ADD_COMPONENT])

  let VSUM_DIFF ← prove
   r"!f s t. FINITE s /\ t SUBSET s
           ==> (vsum (s DIFF t) f = vsum s f - vsum t f)"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, SUM_DIFF, VECTOR_SUB_COMPONENT])

  let VSUM_DELETE ← prove
   r"!f s a. FINITE s /\ a IN s
           ==> vsum (s DELETE a) f = vsum s f - f a"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, SUM_DELETE, VECTOR_SUB_COMPONENT])

  let VSUM_INCL_EXCL ← prove
   r"!s t (f:A->real^N).
        FINITE s /\ FINITE t
        ==> vsum s f + vsum t f = vsum (s UNION t) f + vsum (s INTER t) f"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, VECTOR_ADD_COMPONENT] THEN
    SIMP_TAC [SUM_INCL_EXCL])

  let VSUM_NEG ← prove
   r"!f s. vsum s (\x. --f x) = --vsum s f"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, SUM_NEG, VECTOR_NEG_COMPONENT])

  let VSUM_EQ ← prove
   r"!f g s. (!x. x IN s ==> (f x = g x)) ==> (vsum s f = vsum s g)"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC [])

  let VSUM_SUPERSET ← prove
   r"!f:A->real^N u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = vec 0))
        ==> (vsum v f = vsum u f)"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, VEC_COMPONENT, SUM_SUPERSET])

  let VSUM_SUPPORT ← prove
   r"!f:A->real^N s. vsum {x | x IN s /\ ~(f x = vec 0)} f = vsum s f"
   (REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
    SET_TAC [])

  let VSUM_UNIV ← prove
   r"!f:A->real^N s.
     support (+) f (:A) SUBSET s ==> vsum s f = vsum (:A) f"
   (REWRITE_TAC [support, NEUTRAL_VECTOR_ADD] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [← GSYM VSUM_SUPPORT] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC [])

  let VSUM_EQ_SUPERSET ← prove
   r"!f s t:A->bool.
        FINITE t /\ t SUBSET s /\
        (!x. x IN t ==> (f x = g x)) /\
        (!x. x IN s /\ ~(x IN t) ==> f(x) = vec 0)
        ==> vsum s f = vsum t g"
   (MESON_TAC [VSUM_SUPERSET, VSUM_EQ])

  let VSUM_UNION_RZERO ← prove
   r"!f:A->real^N u v.
        (!x. x IN v /\ ~(x IN u) ==> (f(x) = vec 0))
        ==> (vsum (u UNION v) f = vsum u f)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_SUPERSET THEN ASM SET_TAC [])

  let VSUM_UNION_LZERO ← prove
   r"!f:A->real^N u v.
        (!x. x IN u /\ ~(x IN v) ==> (f(x) = vec 0))
        ==> (vsum (u UNION v) f = vsum v f)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_SUPERSET THEN ASM SET_TAC [])

  let VSUM_RESTRICT ← prove
   r"!f s. vsum s (\x. if x IN s then f(x) else vec 0) = vsum s f"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC [])

  let VSUM_RESTRICT_SET ← prove
   r"!P s f. vsum {x | x IN s /\ P x} f =
           vsum s (\x. if P x then f x else vec 0)"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, VEC_COMPONENT, SUM_RESTRICT_SET,
              COND_COMPONENT])

  let VSUM_CASES ← prove
   r"!s P f g. FINITE s
             ==> vsum s (\x:A. if P x then (f x):real^N else g x) =
                 vsum {x | x IN s /\ P x} f + vsum {x | x IN s /\ ~P x} g"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, VECTOR_ADD_COMPONENT, SUM_CASES,
              COND_COMPONENT])

  let VSUM_SING ← prove
   r"!f x. vsum {x} f = f(x)"
   (SIMP_TAC [VSUM_CLAUSES, FINITE_RULES, NOT_IN_EMPTY, VECTOR_ADD_RID])

  let VSUM_NORM ← prove
   r"!f s. FINITE s ==> norm(vsum s f) <= sum s (\x. norm(f x))"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [SUM_CLAUSES, VSUM_CLAUSES, NORM_0, REAL_LE_REFL] THEN
    NORM_ARITH_TAC)

  let VSUM_NORM_LE ← prove
   r"!s f:A->real^N g.
        FINITE s /\ (!x. x IN s ==> norm(f x) <= g(x))
        ==> norm(vsum s f) <= sum s g"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"sum s (\x:A. norm(f x :real^N))") THEN
    ASM_SIMP_TAC [VSUM_NORM, SUM_LE])

  let VSUM_NORM_TRIANGLE ← prove
   r"!s f b. FINITE s /\ sum s (\a. norm(f a)) <= b ==> norm(vsum s f) <= b"
   (MESON_TAC [VSUM_NORM, REAL_LE_TRANS])

  let VSUM_NORM_BOUND ← prove
   r"!s f b. FINITE s /\ (!x:A. x IN s ==> norm(f(x)) <= b)
           ==> norm(vsum s f) <= &(CARD s) * b"
   (SIMP_TAC [← GSYM SUM_CONST, VSUM_NORM_LE])

  let VSUM_CLAUSES_NUMSEG ← prove
   r"(!m. vsum(m..0) f = if m = 0 then f(0) else vec 0) /\
   (!m n. vsum(m..SUC n) f = if m <= SUC n then vsum(m..n) f + f(SUC n)
                             else vsum(m..n) f)"
   (REWRITE_TAC [NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC [VSUM_SING, VSUM_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"~(SUC n <= n)"), VECTOR_ADD_AC])

  let VSUM_CLAUSES_RIGHT ← prove
   r"!f m n. 0 < n /\ m <= n ==> vsum(m..n) f = vsum(m..n-1) f + (f n):real^N"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    SIMP_TAC [LT_REFL, VSUM_CLAUSES_NUMSEG, SUC_SUB1])

  let VSUM_CMUL_NUMSEG ← prove
   r"!f c m n. vsum (m..n) (\x. c % f x) = c % vsum (m..n) f"
   (SIMP_TAC [VSUM_LMUL, FINITE_NUMSEG])

  let VSUM_EQ_NUMSEG ← prove
   r"!f g m n.
         (!x. m <= x /\ x <= n ==> (f x = g x))
         ==> (vsum(m .. n) f = vsum(m .. n) g)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
    ASM_SIMP_TAC [FINITE_NUMSEG, IN_NUMSEG])

  let VSUM_IMAGE_GEN ← prove
   r"!f:A->B g s.
        FINITE s
        ==> (vsum s g =
             vsum (IMAGE f s) (\y. vsum {x | x IN s /\ (f(x) = y)} g))"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, SUM_IMAGE_GEN])

  let VSUM_GROUP ← prove
   r"!f:A->B g s t.
        FINITE s /\ IMAGE f s SUBSET t
        ==> vsum t (\y. vsum {x | x IN s /\ f(x) = y} g) = vsum s g"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, SUM_GROUP])

  let VSUM_GROUP_RELATION ← prove
   r"!R:A->B->bool g s t.
         FINITE s /\
         (!x. x IN s ==> ?!y. y IN t /\ R x y)
         ==> vsum t (\y. vsum {x | x IN s /\ R x y} g) = vsum s g"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, SUM_GROUP_RELATION])

  let VSUM_VMUL ← prove
   r"!f v s. (sum s f) % v = vsum s (\x. f(x) % v)"
   (REWRITE_TAC [VSUM_RMUL])

  let VSUM_DELTA ← prove
   r"!s a. vsum s (\x. if x = a then b else vec 0) =
         if a IN s then b else vec 0"
   (SIMP_TAC [CART_EQ, LAMBDA_BETA, VSUM_COMPONENT, COND_COMPONENT] THEN
    SIMP_TAC [VEC_COMPONENT, SUM_DELTA])

  let VSUM_ADD_NUMSEG ← prove
   r"!f g m n. vsum(m..n) (\i. f i + g i) = vsum(m..n) f + vsum(m..n) g"
   (SIMP_TAC [VSUM_ADD, FINITE_NUMSEG])

  return { NEUTRAL_VECTOR_ADD, MONOIDAL_VECTOR_ADD, vsum, VSUM_CLAUSES, VSUM,
           VSUM_EQ_0, VSUM_0, VSUM_LMUL, VSUM_RMUL, VSUM_ADD, VSUM_SUB, VSUM_CONST,
           VSUM_COMPONENT, VSUM_IMAGE, VSUM_UNION, VSUM_DIFF, VSUM_DELETE,
           VSUM_INCL_EXCL, VSUM_NEG, VSUM_EQ, VSUM_SUPERSET, VSUM_SUPPORT, VSUM_UNIV,
           VSUM_EQ_SUPERSET, VSUM_UNION_RZERO, VSUM_UNION_LZERO, VSUM_RESTRICT,
           VSUM_RESTRICT_SET, VSUM_CASES, VSUM_SING, VSUM_NORM, VSUM_NORM_LE,
           VSUM_NORM_TRIANGLE, VSUM_NORM_BOUND, VSUM_CLAUSES_NUMSEG,
           VSUM_CLAUSES_RIGHT, VSUM_CMUL_NUMSEG, VSUM_EQ_NUMSEG, VSUM_IMAGE_GEN,
           VSUM_GROUP, VSUM_GROUP_RELATION, VSUM_VMUL, VSUM_DELTA, VSUM_ADD_NUMSEG }

/- ------------------------------------------------------------------------- -/
/- Sums of vectors, continued.  (vectors.ml 1459-1670)                       -/
/- ------------------------------------------------------------------------- -/

structure VSum2 where
  VSUM_SUB_NUMSEG : thm
  VSUM_ADD_SPLIT : thm
  VSUM_VSUM_PRODUCT : thm
  VSUM_IMAGE_NONZERO : thm
  VSUM_UNION_NONZERO : thm
  VSUM_UNIONS_NONZERO : thm
  VSUM_CLAUSES_LEFT : thm
  VSUM_DIFFS : thm
  VSUM_DIFFS_ALT : thm
  VSUM_DELETE_CASES : thm
  VSUM_EQ_GENERAL : thm
  VSUM_EQ_GENERAL_INVERSES : thm
  VSUM_NORM_ALLSUBSETS_BOUND : thm
  DOT_LSUM : thm
  DOT_RSUM : thm
  VSUM_OFFSET : thm
  VSUM_OFFSET_0 : thm
  VSUM_TRIV_NUMSEG : thm
  VSUM_CONST_NUMSEG : thm
  VSUM_SUC : thm
  VSUM_BIJECTION : thm
  VSUM_PARTIAL_SUC : thm
  deriving Inhabited

@[nospecialize]
def setupVSum2 [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BDotProps : DotProps) (BNorm1 : Norm1) (BNorm2 : Norm2) (BVSum1 : VSum1) :
    ExceptT String IO VSum2 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, REAL_ARITH,
        REAL_ARITH_TAC, SET_RULE, SET_TAC, .. } := D
  let { ADD1, ADD_0, ADD_CLAUSES, ADD_SUC, ARITH, CARD_NUMSEG, CARD_NUMSEG_1, CART_EQ,
        ETA_AX, EXTENSION, FINITE_DELETE, FINITE_IMAGE, FINITE_INDUCT_STRONG,
        FINITE_NUMSEG, FINITE_RESTRICT, FINITE_UNIONS, .. } := D.core1
  let { FORALL_PAIR_THM, FUN_EQ_THM, IMAGE_CLAUSES, IMP_CONJ, IN_DELETE,
        IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_INTER, IN_NUMSEG, IN_UNION, IN_UNIONS,
        LAMBDA_BETA, LE, NOT_IN_EMPTY, NOT_LE, NOT_LT, NUMSEG_EMPTY,
        NUMSEG_OFFSET_IMAGE, ONE, .. } := D.core2
  let { REAL_ABS_NEG, REAL_LE_TRANS, .. } := D.core3
  let { RIGHT_FORALL_IMP_THM, SUC_INJ, SUM_ADD_SPLIT, SUM_BOUND, SUM_CLAUSES,
        SUM_CLAUSES_LEFT, SUM_EQ, SUM_EQ_GENERAL, SUM_EQ_GENERAL_INVERSES, .. } := D.core4
  let { SUM_LE, SUM_NEG, SUM_OFFSET, SUM_OFFSET_0, SUM_SUM_PRODUCT, SUM_SWAP,
        SUM_UNION_EQ, SUM_UNION_NONZERO, UNIONS_0, UNIONS_INSERT, o_THM, .. } := D.core5
  let { COND_COMPONENT, VECTOR_ADD_COMPONENT, VECTOR_ADD_LID, VECTOR_ARITH,
        VECTOR_ARITH_TAC, VECTOR_NEG_0, VECTOR_NEG_SUB, VEC_COMPONENT, .. } := BVectorArith
  let { DOT_LADD, DOT_LZERO, DOT_RADD, DOT_RZERO, .. } := BDotProps
  let { COMPONENT_LE_NORM, .. } := BNorm1
  let { NORM_LE_L1, .. } := BNorm2
  let { VSUM_CLAUSES, VSUM_CLAUSES_NUMSEG, VSUM_COMPONENT, VSUM_CONST, VSUM_IMAGE,
        VSUM_NEG, VSUM_SUB, vsum, .. } := BVSum1
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let VSUM_SUB_NUMSEG ← prove
   r"!f g m n. vsum(m..n) (\i. f i - g i) = vsum(m..n) f - vsum(m..n) g"
   (SIMP_TAC [VSUM_SUB, FINITE_NUMSEG])

  let VSUM_ADD_SPLIT ← prove
   r"!f m n p.
       m <= n + 1 ==> vsum(m..n + p) f = vsum(m..n) f + vsum(n + 1..n + p) f"
   (SIMP_TAC [CART_EQ, LAMBDA_BETA, VSUM_COMPONENT, VECTOR_ADD_COMPONENT,
              SUM_ADD_SPLIT])

  let VSUM_VSUM_PRODUCT ← prove
   r"!s:A->bool t:A->B->bool x.
        FINITE s /\ (!i. i IN s ==> FINITE(t i))
        ==> vsum s (\i. vsum (t i) (x i)) =
            vsum {i,j | i IN s /\ j IN t i} (\(i,j). x i j)"
   (SIMP_TAC [CART_EQ, LAMBDA_BETA, VSUM_COMPONENT, COND_COMPONENT] THEN
    SIMP_TAC [SUM_SUM_PRODUCT] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [FUN_EQ_THM, FORALL_PAIR_THM])

  let VSUM_IMAGE_NONZERO ← prove
   r"!d:B->real^N i:A->B s.
    FINITE s /\
    (!x y. x IN s /\ y IN s /\ ~(x = y) /\ i x = i y ==> d(i x) = vec 0)
    ==> vsum (IMAGE i s) d = vsum s (d o i)"
   (GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [IMAGE_CLAUSES, VSUM_CLAUSES, FINITE_IMAGE] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:A", ← q r"s:A->bool"] THEN
    REWRITE_TAC [IN_INSERT] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"vsum s ((d:B->real^N) o (i:A->B)) = vsum (IMAGE i s) d")
    SUBST1_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [o_THM] THEN
    REWRITE_TAC [← va r"a = x + a <=> x = vec 0"] THEN
    ASM_MESON_TAC [IN_IMAGE])

  let VSUM_UNION_NONZERO ← prove
   r"!f s t. FINITE s /\ FINITE t /\ (!x. x IN s INTER t ==> f(x) = vec 0)
           ==> vsum (s UNION t) f = vsum s f + vsum t f"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, VECTOR_ADD_COMPONENT] THEN
    SIMP_TAC [VEC_COMPONENT, SUM_UNION_NONZERO])

  let VSUM_UNIONS_NONZERO ← prove
   r"!f s. FINITE s /\ (!t:A->bool. t IN s ==> FINITE t) /\
         (!t1 t2 x. t1 IN s /\ t2 IN s /\ ~(t1 = t2) /\ x IN t1 /\ x IN t2
                    ==> f x = vec 0)
         ==> vsum (UNIONS s) f = vsum s (\t. vsum t f)"
   (GEN_TAC THEN ONCE_REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [UNIONS_0, UNIONS_INSERT, VSUM_CLAUSES, IN_INSERT] THEN
    MAP_EVERY X_GEN_TAC [← q r"t:A->bool", ← q r"s:(A->bool)->bool"] THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
    ONCE_REWRITE_TAC [IMP_CONJ] THEN ASM_SIMP_TAC [VSUM_CLAUSES] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN (SUBST_ALL_TAC o SYM)] THEN
    STRIP_TAC THEN MATCH_MP_TAC VSUM_UNION_NONZERO THEN
    ASM_SIMP_TAC [FINITE_UNIONS, IN_INTER, IN_UNIONS] THEN ASM_MESON_TAC [])

  let VSUM_CLAUSES_LEFT ← prove
   r"!f m n. m <= n ==> vsum(m..n) f = f m + vsum(m + 1..n) f"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, VECTOR_ADD_COMPONENT] THEN
    SIMP_TAC [VEC_COMPONENT, SUM_CLAUSES_LEFT])

  let VSUM_DIFFS ← prove
   r"!m n. vsum(m..n) (\k. f(k) - f(k + 1)) =
          if m <= n then f(m) - f(n + 1) else vec 0"
   (GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC [VSUM_CLAUSES_NUMSEG, LE] THEN
    ASM_CASES_TAC (← q r"m = SUC n") THEN
    ASM_REWRITE_TAC [← ARITH_RULE (← q r"~(SUC n <= n)"), VECTOR_ADD_LID] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [← GSYM ADD1] THEN VECTOR_ARITH_TAC)

  let VSUM_DIFFS_ALT ← prove
   r"!m n. vsum(m..n) (\k. f(k + 1) - f(k)) =
          if m <= n then f(n + 1) - f(m) else vec 0"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM VECTOR_NEG_SUB] THEN
    SIMP_TAC [VSUM_NEG, VSUM_DIFFS] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [VECTOR_NEG_SUB, VECTOR_NEG_0])

  let VSUM_DELETE_CASES ← prove
   r"!x f s.
        FINITE(s:A->bool)
        ==> vsum(s DELETE x) f = if x IN s then vsum s f - f x else vsum s f"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [← SET_RULE (← q r"~(x IN s) ==> s DELETE x = s")] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
       [← MATCH_MP (← SET_RULE (← q r"x IN s ==> s = x INSERT (s DELETE x)")) th])) THEN
    ASM_SIMP_TAC [VSUM_CLAUSES, FINITE_DELETE, IN_DELETE] THEN VECTOR_ARITH_TAC)

  let VSUM_EQ_GENERAL ← prove
   r"!s:A->bool t:B->bool (f:A->real^N) g h.
        (!y. y IN t ==> ?!x. x IN s /\ h x = y) /\
        (!x. x IN s ==> h x IN t /\ g(h x) = f x)
        ==> vsum s f = vsum t g"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_GENERAL THEN
    EXISTS_TAC (← q r"h:A->B") THEN ASM_MESON_TAC [])

  let VSUM_EQ_GENERAL_INVERSES ← prove
   r"!s t (f:A->real^N) (g:B->real^N) h k.
        (!y. y IN t ==> k y IN s /\ h (k y) = y) /\
        (!x. x IN s ==> h x IN t /\ k (h x) = x /\ g (h x) = f x)
        ==> vsum s f = vsum t g"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
    MAP_EVERY EXISTS_TAC [← q r"h:A->B", ← q r"k:B->A"] THEN ASM_MESON_TAC [])

  let VSUM_NORM_ALLSUBSETS_BOUND ← prove
   r"!f:A->real^N p e.
        FINITE p /\
        (!q. q SUBSET p ==> norm(vsum q f) <= e)
        ==> sum p (\x. norm(f x)) <= &2 * &(dimindex(:N)) * e"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     (← q r"sum p (\x:A. sum (1..dimindex(:N)) (\i. abs((f x:real^N)$i)))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC [NORM_LE_L1], ALL_TAC] THEN
    W (MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
    ASM_REWRITE_TAC [FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"&2 * &n * e = &n * &2 * e")] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV)
     [← GSYM CARD_NUMSEG_1] THEN
    MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
    X_GEN_TAC (← q r"k:num") THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"sum {x:A | x IN p /\ &0 <= (f x:real^N)$k} (\x. abs((f x)$k)) +
              sum {x | x IN p /\ (f x)$k < &0} (\x. abs((f x)$k))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC (← REAL_ARITH (← q r"a = b ==> b <= a")) THEN
      MATCH_MP_TAC SUM_UNION_EQ THEN
      ASM_SIMP_TAC [EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_UNION, IN_ELIM_THM] THEN
      CONJ_TAC THEN X_GEN_TAC (← q r"x:A") THEN ASM_CASES_TAC (← q r"(x:A) IN p") THEN
      ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"x <= e /\ y <= e ==> x + y <= &2 * e")) THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [← GSYM REAL_ABS_NEG] THEN
    CONJ_TAC THEN MATCH_MP_TAC (← REAL_ARITH (← q
     r"!g. sum s g = sum s f /\ sum s g <= e ==> sum s f <= e"))
    THENL
     [EXISTS_TAC (← q r"\x. ((f:A->real^N) x)$k"),
      EXISTS_TAC (← q r"\x. --(((f:A->real^N) x)$k)")] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN REAL_ARITH_TAC,
       ALL_TAC]) THEN
    ASM_SIMP_TAC [← GSYM VSUM_COMPONENT, SUM_NEG, FINITE_RESTRICT] THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"abs(x) <= e ==> x <= e")) THEN
    REWRITE_TAC [REAL_ABS_NEG] THEN
    MATCH_MP_TAC (← REAL_ARITH (← q
     r"abs((vsum q f)$k) <= norm(vsum q f) /\
    norm(vsum q f) <= e
    ==> abs((vsum q f)$k) <= e")) THEN
    ASM_SIMP_TAC [COMPONENT_LE_NORM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN SET_TAC [])

  let DOT_LSUM ← prove
   r"!s f y. FINITE s ==> (vsum s f) dot y = sum s (\x. f(x) dot y)"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [VSUM_CLAUSES, SUM_CLAUSES, DOT_LZERO, DOT_LADD])

  let DOT_RSUM ← prove
   r"!s f x. FINITE s ==> x dot (vsum s f) = sum s (\y. x dot f(y))"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [VSUM_CLAUSES, SUM_CLAUSES, DOT_RZERO, DOT_RADD])

  let VSUM_OFFSET ← prove
   r"!p f m n. vsum(m + p..n + p) f = vsum(m..n) (\i. f (i + p))"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, VEC_COMPONENT, SUM_OFFSET])

  let VSUM_OFFSET_0 ← prove
   r"!f m n. m <= n ==> vsum(m..n) f = vsum(0..n - m) (\i. f (i + m))"
   (SIMP_TAC [vsum, CART_EQ, LAMBDA_BETA, VEC_COMPONENT, SUM_OFFSET_0])

  let VSUM_TRIV_NUMSEG ← prove
   r"!f m n. n < m ==> vsum(m..n) f = vec 0"
   (SIMP_TAC [← GSYM NUMSEG_EMPTY, VSUM_CLAUSES])

  let VSUM_CONST_NUMSEG ← prove
   r"!c m n. vsum(m..n) (\n. c) = &((n + 1) - m) % c"
   (SIMP_TAC [VSUM_CONST, FINITE_NUMSEG, CARD_NUMSEG])

  let VSUM_SUC ← prove
   r"!f m n. vsum (SUC n..SUC m) f = vsum (n..m) (f o SUC)"
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN (← q r"SUC n..SUC m = IMAGE SUC (n..m)") SUBST1_TAC THENL
     [REWRITE_TAC [ADD1, NUMSEG_OFFSET_IMAGE] THEN
      REWRITE_TAC [ONE, ADD_SUC, ADD_0, ETA_AX],
      SIMP_TAC [VSUM_IMAGE, FINITE_NUMSEG, SUC_INJ]])

  let VSUM_BIJECTION ← prove
   r"!f:A->real^N p s:A->bool.
                (!x. x IN s ==> p(x) IN s) /\
                (!y. y IN s ==> ?!x. x IN s /\ p(x) = y)
                ==> vsum s f = vsum s (f o p)"
   (REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC VSUM_EQ_GENERAL THEN EXISTS_TAC (← q r"p:A->A") THEN
    ASM_REWRITE_TAC [o_THM])

  let VSUM_PARTIAL_SUC ← prove
   r"!f g:num->real^N m n.
        vsum (m..n) (\k. f(k) % (g(k + 1) - g(k))) =
            if m <= n then f(n + 1) % g(n + 1) - f(m) % g(m) -
                           vsum (m..n) (\k. (f(k + 1) - f(k)) % g(k + 1))
            else vec 0"
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [VSUM_TRIV_NUMSEG, ← GSYM NOT_LE] THEN
    ASM_REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THENL
     [COND_CASES_TAC THEN ASM_SIMP_TAC [ARITH] THENL
       [VECTOR_ARITH_TAC, ASM_ARITH_TAC],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [LE]) THEN
    DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    ASM_SIMP_TAC [← GSYM NOT_LT, VSUM_TRIV_NUMSEG, ← ARITH_RULE (← q r"n < SUC n")] THEN
    ASM_SIMP_TAC [← GSYM ADD1, ADD_CLAUSES] THEN VECTOR_ARITH_TAC)

  return { VSUM_SUB_NUMSEG, VSUM_ADD_SPLIT, VSUM_VSUM_PRODUCT, VSUM_IMAGE_NONZERO,
           VSUM_UNION_NONZERO, VSUM_UNIONS_NONZERO, VSUM_CLAUSES_LEFT, VSUM_DIFFS,
           VSUM_DIFFS_ALT, VSUM_DELETE_CASES, VSUM_EQ_GENERAL,
           VSUM_EQ_GENERAL_INVERSES, VSUM_NORM_ALLSUBSETS_BOUND, DOT_LSUM, DOT_RSUM,
           VSUM_OFFSET, VSUM_OFFSET_0, VSUM_TRIV_NUMSEG, VSUM_CONST_NUMSEG, VSUM_SUC,
           VSUM_BIJECTION, VSUM_PARTIAL_SUC }

/- ------------------------------------------------------------------------- -/
/- Sums of vectors, concluded; congruences added to the simplifier; and a   -/
/- conversion for evaluation of `vsum(m..n) f` for numerals m and n.        -/
/- (vectors.ml 1672-1835)                                                     -/
/- ------------------------------------------------------------------------- -/

/-- The recursive `conv` of `EXPAND_VSUM_CONV` (vectors.ml 1812-1834). -/
partial def expandVsumGo [HolBase] (pth_0 pth_1 pth_2 : thm) (ns_tm f_tm m_tm n_tm : term)
    (n_ty : hol_type) (NUM_LT_CONV NUM_LE_CONV NUM_ADD_CONV : ioconv) : ioconv := fun tm =>
  (do
    let (smn, ftm) ← liftExcept (dest_comb tm)
    let (s, mn) ← liftExcept (dest_comb smn)
    let isVsum := is_const s &&
      (match dest_const s with | .ok (c, _) => c == "vsum" | .error _ => false)
    if !isVsum then throw "EXPAND_VSUM_CONV"
    let (mtm, ntm) ← liftExcept (HolCore.Basics.dest_binop ns_tm mn)
    let m ← liftExcept (HolCore.Basics.dest_numeral mtm)
    let n ← liftExcept (HolCore.Basics.dest_numeral ntm)
    let nty ← liftExcept (do
      let (_, r) ← HolCore.Basics.dest_fun_ty (type_of ftm)
      let (_, args) ← dest_type r
      hd (← tl args))
    let ilist := [(nty, n_ty)]
    let ifn := inst ilist
    let tfn := HolLight.INST_TYPE ilist
    if n < m then
      let th1 ← INST [(ftm, ifn f_tm), (mtm, m_tm), (ntm, n_tm)] (← tfn pth_0)
      MP th1 (← EQT_ELIM (← ExceptT.mk (NUM_LT_CONV (← liftExcept (lhand (concl th1))))))
    else if n == m then
      CONV_RULE (RAND_CONV (TRY_CONV BETA_CONV))
        (← INST [(ftm, ifn f_tm), (mtm, m_tm)] (← tfn pth_1))
    else
      let th1 ← INST [(ftm, ifn f_tm), (mtm, m_tm), (ntm, n_tm)] (← tfn pth_2)
      let th2 ← MP th1 (← EQT_ELIM (← ExceptT.mk (NUM_LE_CONV (← liftExcept (lhand (concl th1))))))
      CONV_RULE (RAND_CONV (COMB2_CONV (RAND_CONV (TRY_CONV BETA_CONV))
        (LAND_CONV (LAND_CONV NUM_ADD_CONV) THENC
         expandVsumGo pth_0 pth_1 pth_2 ns_tm f_tm m_tm n_tm n_ty
           NUM_LT_CONV NUM_LE_CONV NUM_ADD_CONV))) th2
    : ExceptT String IO thm).run

structure VSum3 where
  VSUM_PARTIAL_PRE : thm
  VSUM_COMBINE_L : thm
  VSUM_COMBINE_R : thm
  VSUM_INJECTION : thm
  VSUM_SWAP : thm
  VSUM_SWAP_NUMSEG : thm
  VSUM_ADD_GEN : thm
  VSUM_CASES_1 : thm
  VSUM_SING_NUMSEG : thm
  VSUM_1 : thm
  VSUM_2 : thm
  VSUM_3 : thm
  VSUM_4 : thm
  VSUM_PAIR : thm
  VSUM_PAIR_0 : thm
  VSUM_REFLECT : thm
  EXPAND_VSUM_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupVSum3 [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith) (BVSum1 : VSum1)
    (BVSum2 : VSum2) : ExceptT String IO VSum3 := do
  -- @@SCOPE BEGIN
  let { SET_RULE, NUM_ADD_CONV, NUM_LE_CONV, NUM_LT_CONV, extend_basic_congs,
        num_CONV, .. } := D
  let { ADD_SUB, ARITH, CART_EQ, CONTRAPOS_THM, DELETE, DE_MORGAN_THM, FINITE_NUMSEG,
        FINITE_SUBSET, .. } := D.core1
  let { IMP_CONJ_ALT, IN_ELIM_THM, IN_NUMSEG, ITERATE_REFLECT, LAMBDA_BETA, MONO_AND,
        NUMSEG_SING, .. } := D.core2
  let { REAL_ADD_ASSOC, .. } := D.core3
  let { SUBSET, SUM_ADD_GEN, SUM_COMBINE_L, SUM_COMBINE_R, .. } := D.core4
  let { SUM_INJECTION, SUM_PAIR, SUM_SWAP, o_DEF, .. } := D.core5
  let { VECTOR_ADD_ASSOC, VECTOR_ADD_COMPONENT, VECTOR_ARITH_TAC, VEC_COMPONENT, .. } :=
    BVectorArith
  let { MONOIDAL_VECTOR_ADD, NEUTRAL_VECTOR_ADD, VSUM, VSUM_CASES, VSUM_CLAUSES_NUMSEG,
        VSUM_COMPONENT, VSUM_DELETE, VSUM_EQ, VSUM_SING, vsum, .. } := BVSum1
  let { VSUM_CLAUSES_LEFT, VSUM_PARTIAL_SUC, VSUM_TRIV_NUMSEG, .. } := BVSum2
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))

  let VSUM_PARTIAL_PRE ← prove
   r"!f g:num->real^N m n.
        vsum (m..n) (\k. f(k) % (g(k) - g(k - 1))) =
            if m <= n then f(n + 1) % g(n) - f(m) % g(m - 1) -
                           vsum (m..n) (\k. (f(k + 1) - f(k)) % g(k))
            else vec 0"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"f:num->real", ← q r"\k. (g:num->real^N)(k - 1)",
                      ← q r"m:num", ← q r"n:num"] VSUM_PARTIAL_SUC) THEN
    REWRITE_TAC [ADD_SUB] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC [])

  let VSUM_COMBINE_L ← prove
   r"!f m n p.
        0 < n /\ m <= n /\ n <= p + 1
        ==> vsum(m..n - 1) f + vsum(n..p) f = vsum(m..p) f"
   (SIMP_TAC [CART_EQ, VECTOR_ADD_COMPONENT, VSUM_COMPONENT, SUM_COMBINE_L])

  let VSUM_COMBINE_R ← prove
   r"!f m n p.
        m <= n + 1 /\ n <= p
        ==> vsum(m..n) f + vsum(n + 1..p) f = vsum(m..p) f"
   (SIMP_TAC [CART_EQ, VECTOR_ADD_COMPONENT, VSUM_COMPONENT, SUM_COMBINE_R])

  let VSUM_INJECTION ← prove
   r"!f p s.
         FINITE s /\
         (!x. x IN s ==> p x IN s) /\
         (!x y. x IN s /\ y IN s /\ p x = p y ==> x = y)
         ==> vsum s (f o p) = vsum s f"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP SUM_INJECTION) THEN
    SIMP_TAC [CART_EQ, VSUM_COMPONENT, o_DEF])

  let VSUM_SWAP ← prove
   r"!f s t.
         FINITE s /\ FINITE t
         ==> vsum s (\i. vsum t (f i)) = vsum t (\j. vsum s (\i. f i j))"
   (SIMP_TAC [CART_EQ, VSUM_COMPONENT] THEN REPEAT STRIP_TAC THEN
    W (MP_TAC o PART_MATCH (lhs o rand) SUM_SWAP o lhs o snd) THEN
    ASM_REWRITE_TAC [])

  let VSUM_SWAP_NUMSEG ← prove
   r"!a b c d f.
         vsum (a..b) (\i. vsum (c..d) (f i)) =
         vsum (c..d) (\j. vsum (a..b) (\i. f i j))"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_SWAP THEN REWRITE_TAC [FINITE_NUMSEG])

  let VSUM_ADD_GEN ← prove
   r"!f g s.
       FINITE {x | x IN s /\ ~(f x = vec 0)} /\
       FINITE {x | x IN s /\ ~(g x = vec 0)}
       ==> vsum s (\x. f x + g x) = vsum s f + vsum s g"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    SIMP_TAC [CART_EQ, vsum, LAMBDA_BETA, VECTOR_ADD_COMPONENT] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (K ALL_TAC) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_ADD_GEN THEN
    POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_AND THEN
    CONJ_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] FINITE_SUBSET) THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN GEN_TAC THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN REWRITE_TAC [DE_MORGAN_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [VEC_COMPONENT])

  let VSUM_CASES_1 ← prove
   r"!s a. FINITE s /\ a IN s
         ==> vsum s (\x. if x = a then y else f(x)) = vsum s f + (y - f a)"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [VSUM_CASES] THEN
    ASM_SIMP_TAC [← GSYM DELETE, VSUM_DELETE] THEN
    ASM_SIMP_TAC [← SET_RULE (← q r"a IN s ==> {x | x IN s /\ x = a} = {a}")] THEN
    REWRITE_TAC [VSUM_SING] THEN VECTOR_ARITH_TAC)

  let VSUM_SING_NUMSEG ← prove
   r"vsum(n..n) f = f n"
   (REWRITE_TAC [NUMSEG_SING, VSUM_SING])

  let VSUM_1 ← prove
   r"vsum(1..1) f = f(1)"
   (REWRITE_TAC [VSUM_SING_NUMSEG])

  let VSUM_2 ← prove
   r"!t. vsum(1..2) t = t(1) + t(2)"
   (REWRITE_TAC [← numc "2", VSUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC [VSUM_SING_NUMSEG, ARITH, REAL_ADD_ASSOC])

  let VSUM_3 ← prove
   r"!t. vsum(1..3) t = t(1) + t(2) + t(3)"
   (REWRITE_TAC [← numc "3", ← numc "2", VSUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC [VSUM_SING_NUMSEG, ARITH, VECTOR_ADD_ASSOC])

  let VSUM_4 ← prove
   r"!t. vsum(1..4) t = t(1) + t(2) + t(3) + t(4)"
   (SIMP_TAC [← numc "4", ← numc "3", ← numc "2", VSUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC [VSUM_SING_NUMSEG, ARITH, VECTOR_ADD_ASSOC])

  let VSUM_PAIR ← prove
   r"!f:num->real^N m n.
        vsum(2*m..2*n+1) f = vsum(m..n) (\i. f(2*i) + f(2*i+1))"
   (SIMP_TAC [CART_EQ, VSUM_COMPONENT, VECTOR_ADD_COMPONENT, SUM_PAIR])

  let VSUM_PAIR_0 ← prove
   r"!f:num->real^N n. vsum(0..2*n+1) f = vsum(0..n) (\i. f(2*i) + f(2*i+1))"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"f:num->real^N", ← q r"0", ← q r"n:num"] VSUM_PAIR) THEN
    ASM_REWRITE_TAC [ARITH])

  let VSUM_REFLECT ← prove
   r"!x m n. vsum(m..n) x =
           if n < m then vec 0 else vsum(0..n-m) (\i. x(n - i))"
   (REPEAT GEN_TAC THEN SIMP_TAC [VSUM, FINITE_NUMSEG] THEN
    GEN_REWRITE_TAC LAND_CONV [← MATCH_MP ITERATE_REFLECT MONOIDAL_VECTOR_ADD] THEN
    REWRITE_TAC [NEUTRAL_VECTOR_ADD])

  -- Add useful congruences to the simplifier (vectors.ml 1787-1796).
  let th ← prove
   r"(!f g s.   (!x. x IN s ==> f(x) = g(x))
              ==> vsum s (\i. f(i)) = vsum s g) /\
   (!f g a b. (!i. a <= i /\ i <= b ==> f(i) = g(i))
              ==> vsum(a..b) (\i. f(i)) = vsum(a..b) g) /\
   (!f g p.   (!x. p x ==> f x = g x)
              ==> vsum {y | p y} (\i. f(i)) = vsum {y | p y} g)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
    ASM_SIMP_TAC [IN_ELIM_THM, IN_NUMSEG])
  extend_basic_congs (← (CONJUNCTS th).mapM SPEC_ALL)

  let EXPAND_VSUM_CONV : ioconv ← do
    let ths := CONJUNCTS (← prove
     r"(n < m ==> vsum(m..n) (f:num->real^N) = vec 0) /\
     vsum(m..m) (f:num->real^N) = f m /\
     (m <= n ==> vsum (m..n) (f:num->real^N) = f m + vsum (m + 1..n) f)"
     (REWRITE_TAC [VSUM_CLAUSES_LEFT, VSUM_SING_NUMSEG, VSUM_TRIV_NUMSEG]))
    let (pth_0, pth_1, pth_2) ← match ths with
      | [a, b, c] => pure (a, b, c)
      | _ => throw "EXPAND_VSUM_CONV: Match_failure"
    let ns_tm ← q r".."
    let f_tm ← q r"f:num->real^N"
    let m_tm ← q r"m:num"
    let n_tm ← q r"n:num"
    let n_ty ← qty "N"
    pure (expandVsumGo pth_0 pth_1 pth_2 ns_tm f_tm m_tm n_tm n_ty
            NUM_LT_CONV NUM_LE_CONV NUM_ADD_CONV)

  return { VSUM_PARTIAL_PRE, VSUM_COMBINE_L, VSUM_COMBINE_R, VSUM_INJECTION, VSUM_SWAP,
           VSUM_SWAP_NUMSEG, VSUM_ADD_GEN, VSUM_CASES_1, VSUM_SING_NUMSEG, VSUM_1,
           VSUM_2, VSUM_3, VSUM_4, VSUM_PAIR, VSUM_PAIR_0, VSUM_REFLECT,
           EXPAND_VSUM_CONV }

/- ------------------------------------------------------------------------- -/
/- Basis vectors in coordinate directions.  (vectors.ml 1836-1957)           -/
/- ------------------------------------------------------------------------- -/

structure Basis where
  basis : thm
  NORM_BASIS : thm
  NORM_BASIS_1 : thm
  VECTOR_CHOOSE_SIZE : thm
  VECTOR_CHOOSE_DIST : thm
  BASIS_INJ : thm
  BASIS_INJ_EQ : thm
  BASIS_NE : thm
  BASIS_COMPONENT : thm
  BASIS_EXPANSION : thm
  BASIS_EXPANSION_UNIQUE : thm
  DOT_BASIS : thm
  DOT_BASIS_BASIS : thm
  DOT_BASIS_BASIS_UNEQUAL : thm
  BASIS_EQ_0 : thm
  BASIS_NONZERO : thm
  VECTOR_EQ_LDOT : thm
  VECTOR_EQ_RDOT : thm
  deriving Inhabited

@[nospecialize]
def setupBasis [HolBase] (D : VectorsDeps) (BBasics : Basics) (BVectorArith : VectorArith)
    (BNorm1 : Norm1) (BVSum1 : VSum1) : ExceptT String IO Basis := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, new_definition, .. } := D
  let { ARITH_EQ, CART_EQ, COND_ID, COND_RAND, COND_RATOR, CONTRAPOS_THM,
        DIMINDEX_NONZERO, EQ_SYM_EQ, EQ_TRANS, .. } := D.core1
  let { IN_NUMSEG, LAMBDA_BETA, .. } := D.core2
  let { REAL_MUL_LID, REAL_MUL_LZERO, REAL_MUL_RID, .. } := D.core3
  let { REAL_MUL_RZERO, REAL_OF_NUM_EQ, SQRT_1, SUM_0, SUM_DELTA, SUM_EQ_NUMSEG, .. } :=
    D.core4
  let { real_abs, .. } := D.core5
  let { dot, .. } := BBasics
  let { VECTOR_ARITH, VECTOR_MUL_COMPONENT, VEC_COMPONENT, .. } := BVectorArith
  let { NORM_MUL, dist, vector_norm, .. } := BNorm1
  let { VSUM_COMPONENT, .. } := BVSum1
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let basis ← new_definition
   r"basis k = lambda i. if i = k then &1 else &0"

  let NORM_BASIS ← prove
   r"!k. 1 <= k /\ k <= dimindex(:N)
       ==> (norm(basis k :real^N) = &1)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [basis, dot, vector_norm] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM SQRT_1] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     (← q r"sum (1..dimindex(:N)) (\i. if i = k then &1 else &0)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      ASM_SIMP_TAC [LAMBDA_BETA, IN_NUMSEG, EQ_SYM_EQ] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC,
      ASM_REWRITE_TAC [SUM_DELTA, IN_NUMSEG]])

  let NORM_BASIS_1 ← prove
   r"norm(basis 1) = &1"
   (SIMP_TAC [NORM_BASIS, ARITH_EQ, ← ARITH_RULE (← q r"1 <= k <=> ~(k = 0)"),
              DIMINDEX_NONZERO])

  let VECTOR_CHOOSE_SIZE ← prove
   r"!c. &0 <= c ==> ?x:real^N. norm(x) = c"
   (REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"c % basis 1 :real^N") THEN
    ASM_REWRITE_TAC [NORM_MUL, real_abs, NORM_BASIS_1, REAL_MUL_RID])

  let VECTOR_CHOOSE_DIST ← prove
   r"!x e. &0 <= e ==> ?y:real^N. dist(x,y) = e"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"?c:real^N. norm(c) = e") CHOOSE_TAC THENL
     [ASM_SIMP_TAC [VECTOR_CHOOSE_SIZE], ALL_TAC] THEN
    EXISTS_TAC (← q r"x - c:real^N") THEN REWRITE_TAC [dist] THEN
    ASM_REWRITE_TAC [← va r"x - (x - c) = c:real^N"])

  let BASIS_INJ ← prove
   r"!i j. 1 <= i /\ i <= dimindex(:N) /\
         1 <= j /\ j <= dimindex(:N) /\
         (basis i :real^N = basis j)
         ==> (i = j)"
   (SIMP_TAC [basis, CART_EQ, LAMBDA_BETA] THEN REPEAT GEN_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"i:num")) THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    ASM_SIMP_TAC [REAL_OF_NUM_EQ, ARITH_EQ])

  let BASIS_INJ_EQ ← prove
   r"!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
         ==> (basis i:real^N = basis j <=> i = j)"
   (MESON_TAC [BASIS_INJ])

  let BASIS_NE ← prove
   r"!i j. 1 <= i /\ i <= dimindex(:N) /\
         1 <= j /\ j <= dimindex(:N) /\
         ~(i = j)
         ==> ~(basis i :real^N = basis j)"
   (MESON_TAC [BASIS_INJ])

  let BASIS_COMPONENT ← prove
   r"!k i. 1 <= i /\ i <= dimindex(:N)
         ==> ((basis k :real^N)$i = if i = k then &1 else &0)"
   (SIMP_TAC [basis, LAMBDA_BETA] THEN MESON_TAC [])

  let BASIS_EXPANSION ← prove
   r"!x:real^N. vsum(1..dimindex(:N)) (\i. x$i % basis i) = x"
   (SIMP_TAC [CART_EQ, VSUM_COMPONENT, VECTOR_MUL_COMPONENT, BASIS_COMPONENT] THEN
    ONCE_REWRITE_TAC [COND_RAND] THEN REWRITE_TAC [REAL_MUL_RZERO] THEN
    REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC [SUM_DELTA, IN_NUMSEG, REAL_MUL_RID])

  let BASIS_EXPANSION_UNIQUE ← prove
   r"!f x:real^N. (vsum(1..dimindex(:N)) (\i. f(i) % basis i) = x) <=>
                (!i. 1 <= i /\ i <= dimindex(:N) ==> f(i) = x$i)"
   (SIMP_TAC [CART_EQ, VSUM_COMPONENT, VECTOR_MUL_COMPONENT, BASIS_COMPONENT] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [COND_RAND, REAL_MUL_RZERO, REAL_MUL_RID] THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o RAND_CONV o LAND_CONV o
                     ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    SIMP_TAC [SUM_DELTA, IN_NUMSEG])

  let DOT_BASIS ← prove
   r"!x:real^N i.
        1 <= i /\ i <= dimindex(:N)
        ==> ((basis i) dot x = x$i) /\ (x dot (basis i) = x$i)"
   (SIMP_TAC [dot, basis, LAMBDA_BETA] THEN
    REWRITE_TAC [COND_RATOR, COND_RAND] THEN
    REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
    SIMP_TAC [SUM_DELTA, IN_NUMSEG, REAL_MUL_LID, REAL_MUL_RID])

  let DOT_BASIS_BASIS ← prove
   r"!i j. 1 <= i /\ i <= dimindex(:N) /\
         1 <= j /\ j <= dimindex(:N)
         ==> (basis i:real^N) dot (basis j) = if i = j then &1 else &0"
   (SIMP_TAC [DOT_BASIS, BASIS_COMPONENT])

  let DOT_BASIS_BASIS_UNEQUAL ← prove
   r"!i j. ~(i = j) ==> (basis i) dot (basis j) = &0"
   (SIMP_TAC [basis, dot, LAMBDA_BETA] THEN ONCE_REWRITE_TAC [COND_RAND] THEN
    SIMP_TAC [SUM_0, REAL_MUL_RZERO, REAL_MUL_LZERO, COND_ID])

  let BASIS_EQ_0 ← prove
   r"!i. (basis i :real^N = vec 0) <=> ~(i IN 1..dimindex(:N))"
   (SIMP_TAC [CART_EQ, BASIS_COMPONENT, VEC_COMPONENT, IN_NUMSEG] THEN
    MESON_TAC [← REAL_ARITH (← q r"~(&1 = &0)")])

  let BASIS_NONZERO ← prove
   r"!k. 1 <= k /\ k <= dimindex(:N)
       ==> ~(basis k :real^N = vec 0)"
   (REWRITE_TAC [BASIS_EQ_0, IN_NUMSEG])

  let VECTOR_EQ_LDOT ← prove
   r"!y z. (!x. x dot y = x dot z) <=> y = z"
   (REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC [] THEN
    REWRITE_TAC [CART_EQ] THEN MESON_TAC [DOT_BASIS])

  let VECTOR_EQ_RDOT ← prove
   r"!x y. (!z. x dot z = y dot z) <=> x = y"
   (REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC [] THEN
    REWRITE_TAC [CART_EQ] THEN MESON_TAC [DOT_BASIS])

  return { basis, NORM_BASIS, NORM_BASIS_1, VECTOR_CHOOSE_SIZE, VECTOR_CHOOSE_DIST,
           BASIS_INJ, BASIS_INJ_EQ, BASIS_NE, BASIS_COMPONENT, BASIS_EXPANSION,
           BASIS_EXPANSION_UNIQUE, DOT_BASIS, DOT_BASIS_BASIS, DOT_BASIS_BASIS_UNEQUAL,
           BASIS_EQ_0, BASIS_NONZERO, VECTOR_EQ_LDOT, VECTOR_EQ_RDOT }

/- ------------------------------------------------------------------------- -/
/- Orthogonality; explicit vector construction from lists.                  -/
/- (vectors.ml 1959-2149)                                                     -/
/- ------------------------------------------------------------------------- -/

structure Orth where
  orthogonal : thm
  ORTHOGONAL_0 : thm
  ORTHOGONAL_REFL : thm
  ORTHOGONAL_SYM : thm
  ORTHOGONAL_LNEG : thm
  ORTHOGONAL_RNEG : thm
  ORTHOGONAL_MUL : thm
  ORTHOGONAL_BASIS : thm
  ORTHOGONAL_BASIS_BASIS : thm
  ORTHOGONAL_CLAUSES : thm
  ORTHOGONAL_RVSUM : thm
  ORTHOGONAL_LVSUM : thm
  NORM_ADD_PYTHAGOREAN : thm
  NORM_VSUM_PYTHAGOREAN : thm
  VECTOR_1 : thm
  VECTOR_2 : thm
  VECTOR_3 : thm
  VECTOR_4 : thm
  FORALL_VECTOR_1 : thm
  FORALL_VECTOR_2 : thm
  FORALL_VECTOR_3 : thm
  FORALL_VECTOR_4 : thm
  EXISTS_VECTOR_1 : thm
  EXISTS_VECTOR_2 : thm
  EXISTS_VECTOR_3 : thm
  EXISTS_VECTOR_4 : thm
  VECTOR_EXPAND_1 : thm
  VECTOR_EXPAND_2 : thm
  VECTOR_EXPAND_3 : thm
  VECTOR_EXPAND_4 : thm
  deriving Inhabited

@[nospecialize]
def setupOrth [HolBase] (D : VectorsDeps) (BBasics : Basics) (BDotProps : DotProps)
    (BNorm1 : Norm1) (BVSum1 : VSum1) (BBasis : Basis) : ExceptT String IO Orth := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC,
        REAL_RAT_REDUCE_CONV, new_definition, num_CONV, .. } := D
  let { ARITH, CART_EQ, COND_RAND, COND_RATOR, DIMINDEX_1, DIMINDEX_2, DIMINDEX_3,
        DIMINDEX_4, EQ_IMP, FINITE_INDUCT_STRONG, FORALL_IN_INSERT, .. } := D.core1
  let { IMP_CONJ, IN_NUMSEG, LAMBDA_BETA, NOT_IN_EMPTY, .. } := D.core2
  let { PAIRWISE_INSERT, REAL_ENTIRE, REAL_MUL_LID, REAL_MUL_LZERO, .. } := D.core3
  let { REAL_NEG_EQ_0, RIGHT_FORALL_IMP_THM, SUM_CLAUSES, SUM_DELTA, .. } := D.core4
  let { SWAP_FORALL_THM, pairwise, vector, EL, HD, LENGTH, TL, .. } := D.core5
  let { FORALL_1, FORALL_2, FORALL_3, FORALL_4, dot, .. } := BBasics
  let { DOT_EQ_0, DOT_LADD, DOT_LMUL, DOT_LNEG, DOT_LSUB, DOT_LZERO, DOT_RADD,
        DOT_RMUL, DOT_RNEG, DOT_RSUB, DOT_RZERO, DOT_SYM, .. } := BDotProps
  let { NORM_0, NORM_POW_2, .. } := BNorm1
  let { VSUM_CLAUSES, .. } := BVSum1
  let { BASIS_COMPONENT, basis, .. } := BBasis
  -- @@SCOPE END
  let numc (s : String) : ExceptT String IO thm := do ExceptT.mk (num_CONV (← q s))

  let orthogonal ← new_definition
   r"orthogonal x y <=> (x dot y = &0)"

  let ORTHOGONAL_0 ← prove
   r"!x. orthogonal (vec 0) x /\ orthogonal x (vec 0)"
   (REWRITE_TAC [orthogonal, DOT_LZERO, DOT_RZERO])

  let ORTHOGONAL_REFL ← prove
   r"!x. orthogonal x x <=> x = vec 0"
   (REWRITE_TAC [orthogonal, DOT_EQ_0])

  let ORTHOGONAL_SYM ← prove
   r"!x y. orthogonal x y <=> orthogonal y x"
   (REWRITE_TAC [orthogonal, DOT_SYM])

  let ORTHOGONAL_LNEG ← prove
   r"!x y. orthogonal (--x) y <=> orthogonal x y"
   (REWRITE_TAC [orthogonal, DOT_LNEG, REAL_NEG_EQ_0])

  let ORTHOGONAL_RNEG ← prove
   r"!x y. orthogonal x (--y) <=> orthogonal x y"
   (REWRITE_TAC [orthogonal, DOT_RNEG, REAL_NEG_EQ_0])

  let ORTHOGONAL_MUL ← prove
   r"(!a x y:real^N. orthogonal (a % x) y <=> a = &0 \/ orthogonal x y) /\
   (!a x y:real^N. orthogonal x (a % y) <=> a = &0 \/ orthogonal x y)"
   (REWRITE_TAC [orthogonal, DOT_LMUL, DOT_RMUL, REAL_ENTIRE])

  let ORTHOGONAL_BASIS ← prove
   r"!x:real^N i. 1 <= i /\ i <= dimindex(:N)
                ==> (orthogonal (basis i) x <=> (x$i = &0))"
   (REPEAT STRIP_TAC THEN SIMP_TAC [orthogonal, dot, basis, LAMBDA_BETA] THEN
    REWRITE_TAC [COND_RAND, COND_RATOR, REAL_MUL_LZERO] THEN
    ASM_SIMP_TAC [SUM_DELTA, IN_NUMSEG, REAL_MUL_LID])

  let ORTHOGONAL_BASIS_BASIS ← prove
   r"!i j. 1 <= i /\ i <= dimindex(:N) /\
         1 <= j /\ j <= dimindex(:N)
         ==> (orthogonal (basis i :real^N) (basis j) <=> ~(i = j))"
   (ASM_SIMP_TAC [ORTHOGONAL_BASIS] THEN ASM_SIMP_TAC [BASIS_COMPONENT] THEN
    MESON_TAC [← REAL_ARITH (← q r"~(&1 = &0)")])

  let ORTHOGONAL_CLAUSES ← prove
   r"(!a. orthogonal a (vec 0)) /\
   (!a x c. orthogonal a x ==> orthogonal a (c % x)) /\
   (!a x. orthogonal a x ==> orthogonal a (--x)) /\
   (!a x y. orthogonal a x /\ orthogonal a y ==> orthogonal a (x + y)) /\
   (!a x y. orthogonal a x /\ orthogonal a y ==> orthogonal a (x - y)) /\
   (!a. orthogonal (vec 0) a) /\
   (!a x c. orthogonal x a ==> orthogonal (c % x) a) /\
   (!a x. orthogonal x a ==> orthogonal (--x) a) /\
   (!a x y. orthogonal x a /\ orthogonal y a ==> orthogonal (x + y) a) /\
   (!a x y. orthogonal x a /\ orthogonal y a ==> orthogonal (x - y) a)"
   (REWRITE_TAC [orthogonal, DOT_RNEG, DOT_RMUL, DOT_RADD, DOT_RSUB,
      DOT_LZERO, DOT_RZERO, DOT_LNEG, DOT_LMUL, DOT_LADD, DOT_LSUB] THEN
    SIMP_TAC [] THEN REAL_ARITH_TAC)

  let ORTHOGONAL_RVSUM ← prove
   r"!f:A->real^N s x.
        FINITE s /\
        (!y. y IN s ==> orthogonal x (f y))
        ==> orthogonal x (vsum s f)"
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM, IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [NOT_IN_EMPTY, FORALL_IN_INSERT, ORTHOGONAL_CLAUSES, VSUM_CLAUSES])

  let ORTHOGONAL_LVSUM ← prove
   r"!f:A->real^N s y.
        FINITE s /\
        (!x. x IN s ==> orthogonal (f x) y)
        ==> orthogonal (vsum s f) y"
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM, IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [NOT_IN_EMPTY, FORALL_IN_INSERT, ORTHOGONAL_CLAUSES, VSUM_CLAUSES])

  let NORM_ADD_PYTHAGOREAN ← prove
   r"!a b:real^N.
        orthogonal a b
        ==> norm(a + b) pow 2 = norm(a) pow 2 + norm(b) pow 2"
   (SIMP_TAC [NORM_POW_2, orthogonal, DOT_LADD, DOT_RADD, DOT_SYM] THEN
    REAL_ARITH_TAC)

  let NORM_VSUM_PYTHAGOREAN ← prove
   r"!k u:A->real^N.
        FINITE k /\ pairwise (\i j. orthogonal (u i) (u j)) k
        ==> norm(vsum k u) pow 2 = sum k (\i. norm(u i) pow 2)"
   (ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN GEN_TAC THEN SIMP_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [VSUM_CLAUSES, SUM_CLAUSES, NORM_0] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [PAIRWISE_INSERT] THEN
    REWRITE_TAC [pairwise] THEN REPEAT GEN_TAC THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC NORM_ADD_PYTHAGOREAN THEN MATCH_MP_TAC ORTHOGONAL_RVSUM THEN
    ASM_MESON_TAC [])

  let VECTOR_1 ← prove
   r"(vector[x]:A^1)$1 = x"
   (SIMP_TAC [vector, LAMBDA_BETA, DIMINDEX_1, ARITH, LENGTH, EL, HD, TL])

  let VECTOR_2 ← prove
   r"(vector[x;y]:A^2)$1 = x /\
   (vector[x;y]:A^2)$2 = y"
   (SIMP_TAC [vector, LAMBDA_BETA, DIMINDEX_2, ARITH, LENGTH, EL] THEN
    REWRITE_TAC [← numc "1", HD, TL, EL])

  let VECTOR_3 ← prove
   r"(vector[x;y;z]:A^3)$1 = x /\
   (vector[x;y;z]:A^3)$2 = y /\
   (vector[x;y;z]:A^3)$3 = z"
   (SIMP_TAC [vector, LAMBDA_BETA, DIMINDEX_3, ARITH, LENGTH, EL] THEN
    REWRITE_TAC [← numc "2", ← numc "1", HD, TL, EL])

  let VECTOR_4 ← prove
   r"(vector[w;x;y;z]:A^4)$1 = w /\
   (vector[w;x;y;z]:A^4)$2 = x /\
   (vector[w;x;y;z]:A^4)$3 = y /\
   (vector[w;x;y;z]:A^4)$4 = z"
   (SIMP_TAC [vector, LAMBDA_BETA, DIMINDEX_4, ARITH, LENGTH, EL] THEN
    REWRITE_TAC [← numc "3", ← numc "2", ← numc "1", HD, TL, EL])

  let FORALL_VECTOR_1 ← prove
   r"(!v:A^1. P v) <=> !x. P(vector[x])"
   (EQ_TAC THEN SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(v:A^1)$1")) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [CART_EQ, FORALL_1, VECTOR_1, DIMINDEX_1])

  let FORALL_VECTOR_2 ← prove
   r"(!v:A^2. P v) <=> !x y. P(vector[x;y])"
   (EQ_TAC THEN SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"(v:A^2)$1", ← q r"(v:A^2)$2"]) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [CART_EQ, FORALL_2, VECTOR_2, DIMINDEX_2])

  let FORALL_VECTOR_3 ← prove
   r"(!v:A^3. P v) <=> !x y z. P(vector[x;y;z])"
   (EQ_TAC THEN SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
      [← q r"(v:A^3)$1", ← q r"(v:A^3)$2", ← q r"(v:A^3)$3"]) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [CART_EQ, FORALL_3, VECTOR_3, DIMINDEX_3])

  let FORALL_VECTOR_4 ← prove
   r"(!v:A^4. P v) <=> !w x y z. P(vector[w;x;y;z])"
   (EQ_TAC THEN SIMP_TAC [] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
      [← q r"(v:A^4)$1", ← q r"(v:A^4)$2", ← q r"(v:A^4)$3", ← q r"(v:A^4)$4"]) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [CART_EQ, FORALL_4, VECTOR_4, DIMINDEX_4])

  let EXISTS_VECTOR_1 ← prove
   r"(?v:A^1. P v) <=> ?x. P(vector[x])"
   (REWRITE_TAC [← MESON [] (← q r"(?x. P x) <=> ~(!x. ~P x)")] THEN
    REWRITE_TAC [FORALL_VECTOR_1])

  let EXISTS_VECTOR_2 ← prove
   r"(?v:A^2. P v) <=> ?x y. P(vector[x;y])"
   (REWRITE_TAC [← MESON [] (← q r"(?x. P x) <=> ~(!x. ~P x)")] THEN
    REWRITE_TAC [FORALL_VECTOR_2])

  let EXISTS_VECTOR_3 ← prove
   r"(?v:A^3. P v) <=> ?x y z. P(vector[x;y;z])"
   (REWRITE_TAC [← MESON [] (← q r"(?x. P x) <=> ~(!x. ~P x)")] THEN
    REWRITE_TAC [FORALL_VECTOR_3])

  let EXISTS_VECTOR_4 ← prove
   r"(?v:A^4. P v) <=> ?w x y z. P(vector[w;x;y;z])"
   (REWRITE_TAC [← MESON [] (← q r"(?x. P x) <=> ~(!x. ~P x)")] THEN
    REWRITE_TAC [FORALL_VECTOR_4])

  let VECTOR_EXPAND_1 ← prove
   r"!x:real^1. x = vector[x$1]"
   (SIMP_TAC [CART_EQ, DIMINDEX_1, FORALL_1, VECTOR_1])

  let VECTOR_EXPAND_2 ← prove
   r"!x:real^2. x = vector[x$1;x$2]"
   (SIMP_TAC [CART_EQ, DIMINDEX_2, FORALL_2, VECTOR_2])

  let VECTOR_EXPAND_3 ← prove
   r"!x:real^3. x = vector[x$1;x$2;x$3]"
   (SIMP_TAC [CART_EQ, DIMINDEX_3, FORALL_3, VECTOR_3])

  let VECTOR_EXPAND_4 ← prove
   r"!x:real^4. x = vector[x$1;x$2;x$3;x$4]"
   (SIMP_TAC [CART_EQ, DIMINDEX_4, FORALL_4, VECTOR_4])

  return { orthogonal, ORTHOGONAL_0, ORTHOGONAL_REFL, ORTHOGONAL_SYM, ORTHOGONAL_LNEG,
           ORTHOGONAL_RNEG, ORTHOGONAL_MUL, ORTHOGONAL_BASIS, ORTHOGONAL_BASIS_BASIS,
           ORTHOGONAL_CLAUSES, ORTHOGONAL_RVSUM, ORTHOGONAL_LVSUM, NORM_ADD_PYTHAGOREAN,
           NORM_VSUM_PYTHAGOREAN, VECTOR_1, VECTOR_2, VECTOR_3, VECTOR_4,
           FORALL_VECTOR_1, FORALL_VECTOR_2, FORALL_VECTOR_3, FORALL_VECTOR_4,
           EXISTS_VECTOR_1, EXISTS_VECTOR_2, EXISTS_VECTOR_3, EXISTS_VECTOR_4,
           VECTOR_EXPAND_1, VECTOR_EXPAND_2, VECTOR_EXPAND_3, VECTOR_EXPAND_4 }

/- ------------------------------------------------------------------------- -/
/- Linear functions.  (vectors.ml 2151-2287)                                 -/
/- ------------------------------------------------------------------------- -/

structure Linear where
  linear : thm
  LINEAR_COMPOSE_CMUL : thm
  LINEAR_COMPOSE_NEG : thm
  LINEAR_COMPOSE_NEG_EQ : thm
  LINEAR_COMPOSE_ADD : thm
  LINEAR_COMPOSE_SUB : thm
  LINEAR_COMPOSE : thm
  LINEAR_ID : thm
  LINEAR_I : thm
  LINEAR_ZERO : thm
  LINEAR_NEGATION : thm
  LINEAR_COMPOSE_VSUM : thm
  LINEAR_VMUL_COMPONENT : thm
  LINEAR_0 : thm
  LINEAR_CMUL : thm
  LINEAR_NEG : thm
  LINEAR_ADD : thm
  LINEAR_SUB : thm
  LINEAR_VSUM : thm
  LINEAR_VSUM_MUL : thm
  LINEAR_INJECTIVE_0 : thm
  LINEAR_BOUNDED : thm
  LINEAR_BOUNDED_POS : thm
  SYMMETRIC_LINEAR_IMAGE : thm
  deriving Inhabited

@[nospecialize]
def setupLinear [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith) (BNorm1 : Norm1)
    (BVSum1 : VSum1) (BBasis : Basis) : ExceptT String IO Linear := do
  -- @@SCOPE BEGIN
  let { MESON, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, SET_TAC, new_definition, .. } := D
  let { ETA_AX, FINITE_CROSS, FINITE_INDUCT_STRONG, FINITE_NUMSEG, FORALL_IN_IMAGE, .. } :=
    D.core1
  let { IMP_CONJ, IN_INSERT, IN_NUMSEG, I_DEF, MONO_FORALL, .. } := D.core2
  let { REAL_LE_RMUL, .. } := D.core3
  let { REAL_MUL_SYM, RIGHT_FORALL_IMP_THM, .. } := D.core4
  let { SUM_LMUL, o_DEF, o_THM, .. } := D.core5
  let { VECTOR_ADD_COMPONENT, VECTOR_ARITH_TAC, VECTOR_MUL_COMPONENT, VECTOR_MUL_LZERO,
        VECTOR_NEG_MINUS1, VECTOR_NEG_NEG, VECTOR_SUB, VECTOR_SUB_EQ,
        VECTOR_SUB_RZERO, .. } := BVectorArith
  let { COMPONENT_LE_NORM, NORM_MUL, NORM_POS_LE, .. } := BNorm1
  let { VSUM_CLAUSES, VSUM_NORM_LE, .. } := BVSum1
  let { BASIS_EXPANSION, .. } := BBasis
  -- @@SCOPE END

  let linear ← new_definition
   r"linear (f:real^M->real^N) <=>
        (!x y. f(x + y) = f(x) + f(y)) /\
        (!c x. f(c % x) = c % f(x))"

  let LINEAR_COMPOSE_CMUL ← prove
   r"!f c. linear f ==> linear (\x. c % f(x))"
   (SIMP_TAC [linear] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC)

  let LINEAR_COMPOSE_NEG ← prove
   r"!f. linear f ==> linear (\x. --(f(x)))"
   (SIMP_TAC [linear] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC)

  let LINEAR_COMPOSE_NEG_EQ ← prove
   r"!f:real^M->real^N. linear(\x. --(f x)) <=> linear f"
   (MATCH_MP_TAC (← MESON [] (← q
     r"(!x. P x ==> P(f x)) /\ (!x. f(f x) = x)
    ==> (!x. P(f x) <=> P x)")) THEN
    REWRITE_TAC [LINEAR_COMPOSE_NEG, VECTOR_NEG_NEG, ETA_AX])

  let LINEAR_COMPOSE_ADD ← prove
   r"!f g. linear f /\ linear g ==> linear (\x. f(x) + g(x))"
   (SIMP_TAC [linear] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC)

  let LINEAR_COMPOSE_SUB ← prove
   r"!f g. linear f /\ linear g ==> linear (\x. f(x) - g(x))"
   (SIMP_TAC [linear] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC)

  let LINEAR_COMPOSE ← prove
   r"!f g. linear f /\ linear g ==> linear (g o f)"
   (SIMP_TAC [linear, o_THM])

  let LINEAR_ID ← prove
   r"linear (\x. x)"
   (REWRITE_TAC [linear])

  let LINEAR_I ← prove
   r"linear I"
   (REWRITE_TAC [I_DEF, LINEAR_ID])

  let LINEAR_ZERO ← prove
   r"linear (\x. vec 0)"
   (REWRITE_TAC [linear] THEN CONJ_TAC THEN VECTOR_ARITH_TAC)

  let LINEAR_NEGATION ← prove
   r"linear(--)"
   (REWRITE_TAC [linear] THEN VECTOR_ARITH_TAC)

  let LINEAR_COMPOSE_VSUM ← prove
   r"!f s. FINITE s /\ (!a. a IN s ==> linear(f a))
         ==> linear(\x. vsum s (\a. f a x))"
   (GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [VSUM_CLAUSES, LINEAR_ZERO] THEN
    ASM_SIMP_TAC [ETA_AX, IN_INSERT, LINEAR_COMPOSE_ADD])

  let LINEAR_VMUL_COMPONENT ← prove
   r"!f:real^M->real^N v k.
     linear f /\ 1 <= k /\ k <= dimindex(:N)
     ==> linear (\x. f(x)$k % v)"
   (SIMP_TAC [linear, VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC)

  let LINEAR_0 ← prove
   r"!f. linear f ==> (f(vec 0) = vec 0)"
   (MESON_TAC [VECTOR_MUL_LZERO, linear])

  let LINEAR_CMUL ← prove
   r"!f c x. linear f ==> (f(c % x) = c % f(x))"
   (SIMP_TAC [linear])

  let LINEAR_NEG ← prove
   r"!f x. linear f ==> (f(--x) = --(f x))"
   (ONCE_REWRITE_TAC [VECTOR_NEG_MINUS1] THEN SIMP_TAC [LINEAR_CMUL])

  let LINEAR_ADD ← prove
   r"!f x y. linear f ==> (f(x + y) = f(x) + f(y))"
   (SIMP_TAC [linear])

  let LINEAR_SUB ← prove
   r"!f x y. linear f ==> (f(x - y) = f(x) - f(y))"
   (SIMP_TAC [VECTOR_SUB, LINEAR_ADD, LINEAR_NEG])

  let LINEAR_VSUM ← prove
   r"!f g s. linear f /\ FINITE s ==> (f(vsum s g) = vsum s (f o g))"
   (GEN_TAC THEN GEN_TAC THEN SIMP_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [VSUM_CLAUSES] THEN FIRST_ASSUM (fun th => tactic_of do
      pure (SIMP_TAC [← MATCH_MP LINEAR_0 th, ← MATCH_MP LINEAR_ADD th, o_THM])))

  let LINEAR_VSUM_MUL ← prove
   r"!f s c v.
        linear f /\ FINITE s
        ==> f(vsum s (\i. c i % v i)) = vsum s (\i. c(i) % f(v i))"
   (SIMP_TAC [LINEAR_VSUM, o_DEF, LINEAR_CMUL])

  let LINEAR_INJECTIVE_0 ← prove
   r"!f. linear f
       ==> ((!x y. (f(x) = f(y)) ==> (x = y)) <=>
            (!x. (f(x) = vec 0) ==> (x = vec 0)))"
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [← GSYM VECTOR_SUB_EQ] THEN
    ASM_SIMP_TAC [← GSYM LINEAR_SUB] THEN MESON_TAC [VECTOR_SUB_RZERO])

  let LINEAR_BOUNDED ← prove
   r"!f:real^M->real^N. linear f ==> ?B. !x. norm(f x) <= B * norm(x)"
   (REPEAT STRIP_TAC THEN EXISTS_TAC
     (← q r"sum(1..dimindex(:M)) (\i. norm((f:real^M->real^N)(basis i)))") THEN
    GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV) [← GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC [LINEAR_VSUM, FINITE_NUMSEG] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [← GSYM SUM_LMUL] THEN
    MATCH_MP_TAC VSUM_NORM_LE THEN
    SIMP_TAC [FINITE_CROSS, FINITE_NUMSEG, IN_NUMSEG] THEN
    ASM_SIMP_TAC [o_DEF, NORM_MUL, LINEAR_CMUL] THEN
    ASM_SIMP_TAC [REAL_LE_RMUL, NORM_POS_LE, COMPONENT_LE_NORM])

  let LINEAR_BOUNDED_POS ← prove
   r"!f:real^M->real^N. linear f ==> ?B. &0 < B /\ !x. norm(f x) <= B * norm(x)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (X_CHOOSE_TAC (← q r"B:real") o MATCH_MP LINEAR_BOUNDED) THEN
    EXISTS_TAC (← q r"abs(B) + &1") THEN CONJ_TAC THENL [REAL_ARITH_TAC, ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"a <= b ==> x <= a ==> x <= b")) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [NORM_POS_LE] THEN
    REAL_ARITH_TAC)

  let SYMMETRIC_LINEAR_IMAGE ← prove
   r"!f s. (!x. x IN s ==> --x IN s) /\ linear f
          ==> !x. x IN (IMAGE f s) ==> --x IN (IMAGE f s)"
   (REWRITE_TAC [FORALL_IN_IMAGE] THEN
    SIMP_TAC [← GSYM LINEAR_NEG] THEN SET_TAC [])

  return { linear, LINEAR_COMPOSE_CMUL, LINEAR_COMPOSE_NEG, LINEAR_COMPOSE_NEG_EQ,
           LINEAR_COMPOSE_ADD, LINEAR_COMPOSE_SUB, LINEAR_COMPOSE, LINEAR_ID, LINEAR_I,
           LINEAR_ZERO, LINEAR_NEGATION, LINEAR_COMPOSE_VSUM, LINEAR_VMUL_COMPONENT,
           LINEAR_0, LINEAR_CMUL, LINEAR_NEG, LINEAR_ADD, LINEAR_SUB, LINEAR_VSUM,
           LINEAR_VSUM_MUL, LINEAR_INJECTIVE_0, LINEAR_BOUNDED, LINEAR_BOUNDED_POS,
           SYMMETRIC_LINEAR_IMAGE }

/- ------------------------------------------------------------------------- -/
/- Bilinear functions.  (vectors.ml 2289-2475)                               -/
/- ------------------------------------------------------------------------- -/

structure Bilinear where
  bilinear : thm
  BILINEAR_SWAP : thm
  BILINEAR_LADD : thm
  BILINEAR_RADD : thm
  BILINEAR_LMUL : thm
  BILINEAR_RMUL : thm
  BILINEAR_LNEG : thm
  BILINEAR_RNEG : thm
  BILINEAR_LZERO : thm
  BILINEAR_RZERO : thm
  BILINEAR_LSUB : thm
  BILINEAR_RSUB : thm
  BILINEAR_LSUM : thm
  BILINEAR_RSUM : thm
  BILINEAR_VSUM : thm
  BILINEAR_BOUNDED : thm
  BILINEAR_BOUNDED_POS : thm
  BILINEAR_VSUM_PARTIAL_SUC : thm
  BILINEAR_VSUM_PARTIAL_PRE : thm
  BILINEAR_VSUM_CONVOLUTION_1 : thm
  BILINEAR_VSUM_CONVOLUTION_2 : thm
  deriving Inhabited

@[nospecialize]
def setupBilinear [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BNorm1 : Norm1) (BVSum1 : VSum1) (BVSum2 : VSum2) (BBasis : Basis)
    (BLinear : Linear) : ExceptT String IO Bilinear := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, INDUCT_TAC, MESON_TAC, REAL_ARITH,
        REAL_ARITH_TAC, new_definition, .. } := D
  let { ADD1, ADD_CLAUSES, ADD_SUB, ARITH, CROSS, ETA_AX, FINITE_CROSS, FINITE_NUMSEG,
        FINITE_PRODUCT_DEPENDENT, FORALL_IN_GSPEC, .. } := D.core1
  let { FORALL_PAIR_THM, IMP_CONJ, IN_CROSS, IN_ELIM_PAIR_THM, IN_NUMSEG, LE,
        LEFT_AND_FORALL_THM, LE_0, MONO_FORALL, NOT_LE, NOT_LT, .. } := D.core2
  let { PAIR_EQ, REAL_ABS_POS, REAL_LE_MUL, REAL_LE_MUL2, REAL_LE_RMUL,
        REAL_MUL_ASSOC, .. } := D.core3
  let { REAL_MUL_SYM, RIGHT_FORALL_IMP_THM, .. } := D.core4
  let { SUM_LMUL, o_DEF, .. } := D.core5
  let { VECTOR_ADD_LID, VECTOR_ARITH, VECTOR_ARITH_TAC, VECTOR_NEG_MINUS1,
        VECTOR_SUB, .. } := BVectorArith
  let { COMPONENT_LE_NORM, NORM_MUL, NORM_POS_LE, .. } := BNorm1
  let { VSUM_CLAUSES_NUMSEG, VSUM_NORM_LE, .. } := BVSum1
  let { VSUM_EQ_GENERAL_INVERSES, VSUM_TRIV_NUMSEG, VSUM_VSUM_PRODUCT, .. } := BVSum2
  let { BASIS_EXPANSION, .. } := BBasis
  let { LINEAR_VSUM, linear, .. } := BLinear
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let bilinear ← new_definition
   r"bilinear f <=> (!x. linear(\y. f x y)) /\ (!y. linear(\x. f x y))"

  let BILINEAR_SWAP ← prove
   r"!op:real^M->real^N->real^P.
        bilinear(\x y. op y x) <=> bilinear op"
   (REWRITE_TAC [bilinear, ETA_AX] THEN MESON_TAC [])

  let BILINEAR_LADD ← prove
   r"!h x y z. bilinear h ==> h (x + y) z = (h x z) + (h y z)"
   (SIMP_TAC [bilinear, linear])

  let BILINEAR_RADD ← prove
   r"!h x y z. bilinear h ==> h x (y + z) = (h x y) + (h x z)"
   (SIMP_TAC [bilinear, linear])

  let BILINEAR_LMUL ← prove
   r"!h c x y. bilinear h ==> h (c % x) y = c % (h x y)"
   (SIMP_TAC [bilinear, linear])

  let BILINEAR_RMUL ← prove
   r"!h c x y. bilinear h ==> h x (c % y) = c % (h x y)"
   (SIMP_TAC [bilinear, linear])

  let BILINEAR_LNEG ← prove
   r"!h x y. bilinear h ==> h (--x) y = --(h x y)"
   (ONCE_REWRITE_TAC [VECTOR_NEG_MINUS1] THEN SIMP_TAC [BILINEAR_LMUL])

  let BILINEAR_RNEG ← prove
   r"!h x y. bilinear h ==> h x (--y) = --(h x y)"
   (ONCE_REWRITE_TAC [VECTOR_NEG_MINUS1] THEN SIMP_TAC [BILINEAR_RMUL])

  let BILINEAR_LZERO ← prove
   r"!h x. bilinear h ==> h (vec 0) x = vec 0"
   (ONCE_REWRITE_TAC [← va r"x = vec 0 <=> x + x = x"] THEN
    SIMP_TAC [← GSYM BILINEAR_LADD, VECTOR_ADD_LID])

  let BILINEAR_RZERO ← prove
   r"!h x. bilinear h ==> h x (vec 0) = vec 0"
   (ONCE_REWRITE_TAC [← va r"x = vec 0 <=> x + x = x"] THEN
    SIMP_TAC [← GSYM BILINEAR_RADD, VECTOR_ADD_LID])

  let BILINEAR_LSUB ← prove
   r"!h x y z. bilinear h ==> h (x - y) z = (h x z) - (h y z)"
   (SIMP_TAC [VECTOR_SUB, BILINEAR_LNEG, BILINEAR_LADD])

  let BILINEAR_RSUB ← prove
   r"!h x y z. bilinear h ==> h x (y - z) = (h x y) - (h x z)"
   (SIMP_TAC [VECTOR_SUB, BILINEAR_RNEG, BILINEAR_RADD])

  let BILINEAR_LSUM ← prove
   r"!bop:real^M->real^N->real^P f s:A->bool y.
        bilinear bop /\ FINITE s
        ==> bop(vsum s f) y = vsum s (\i. bop (f i) y)"
   (REWRITE_TAC [bilinear] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"y:real^N")) THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← ISPECL [← q r"f:A->real^M", ← q r"s:A->bool"]
        (← MATCH_MP (← REWRITE_RULE [IMP_CONJ] LINEAR_VSUM) th)))) THEN
    ASM_REWRITE_TAC [o_DEF])

  let BILINEAR_RSUM ← prove
   r"!bop:real^M->real^N->real^P f s:A->bool x.
        bilinear bop /\ FINITE s
        ==> bop x (vsum s f) = vsum s (\i. bop x (f i))"
   (REWRITE_TAC [bilinear] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"x:real^M")) THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← ISPECL [← q r"f:A->real^N", ← q r"s:A->bool"]
        (← MATCH_MP (← REWRITE_RULE [IMP_CONJ] LINEAR_VSUM) th)))) THEN
    ASM_REWRITE_TAC [o_DEF])

  let BILINEAR_VSUM ← prove
   r"!h:real^M->real^N->real^P.
       bilinear h /\ FINITE s /\ FINITE t
       ==> h (vsum s f) (vsum t g) = vsum (s CROSS t) (\(i,j). h (f i) (g j))"
   (REPEAT GEN_TAC THEN SIMP_TAC [bilinear, ETA_AX] THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"(a /\ b) /\ c /\ d <=> (a /\ d) /\ (b /\ c)")] THEN
    DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ONCE_REWRITE_TAC [LEFT_AND_FORALL_THM] THEN DISCH_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (MP_TAC (← GEN_ALL (← MATCH_MP LINEAR_VSUM (← SPEC_ALL th))))) THEN
    SIMP_TAC [] THEN ASM_SIMP_TAC [LINEAR_VSUM, o_DEF, VSUM_VSUM_PRODUCT] THEN
    REWRITE_TAC [← GSYM CROSS])

  let BILINEAR_BOUNDED ← prove
   r"!h:real^M->real^N->real^P.
        bilinear h ==> ?B. !x y. norm(h x y) <= B * norm(x) * norm(y)"
   (REPEAT STRIP_TAC THEN
    EXISTS_TAC (← q r"sum ((1..dimindex(:M)) CROSS (1..dimindex(:N)))
                  (\(i,j). norm((h:real^M->real^N->real^P)
                                (basis i) (basis j)))") THEN
    REPEAT GEN_TAC THEN GEN_REWRITE_TAC
     (LAND_CONV o RAND_CONV o BINOP_CONV) [← GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC [BILINEAR_VSUM, FINITE_NUMSEG] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [← GSYM SUM_LMUL] THEN
    MATCH_MP_TAC VSUM_NORM_LE THEN
    SIMP_TAC [FINITE_CROSS, FINITE_NUMSEG, FORALL_PAIR_THM, IN_CROSS] THEN
    REWRITE_TAC [IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [BILINEAR_LMUL, NORM_MUL] THEN
    ASM_SIMP_TAC [BILINEAR_RMUL, NORM_MUL, REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [NORM_POS_LE] THEN
    ASM_SIMP_TAC [COMPONENT_LE_NORM, REAL_ABS_POS, REAL_LE_MUL2])

  let BILINEAR_BOUNDED_POS ← prove
   r"!h. bilinear h
       ==> ?B. &0 < B /\ !x y. norm(h x y) <= B * norm(x) * norm(y)"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (X_CHOOSE_TAC (← q r"B:real") o MATCH_MP BILINEAR_BOUNDED) THEN
    EXISTS_TAC (← q r"abs(B) + &1") THEN CONJ_TAC THENL [REAL_ARITH_TAC, ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"a <= b ==> x <= a ==> x <= b")) THEN
    REPEAT (MATCH_MP_TAC REAL_LE_RMUL THEN
            SIMP_TAC [NORM_POS_LE, REAL_LE_MUL]) THEN
    REAL_ARITH_TAC)

  let BILINEAR_VSUM_PARTIAL_SUC ← prove
   r"!f g h:real^M->real^N->real^P m n.
        bilinear h
        ==> vsum (m..n) (\k. h (f k) (g(k + 1) - g(k))) =
                if m <= n then h (f(n + 1)) (g(n + 1)) - h (f m) (g m) -
                               vsum (m..n) (\k. h (f(k + 1) - f(k)) (g(k + 1)))
                else vec 0"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    GEN_TAC THEN INDUCT_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [VSUM_TRIV_NUMSEG, ← GSYM NOT_LE] THEN
    ASM_REWRITE_TAC [VSUM_CLAUSES_NUMSEG] THENL
     [COND_CASES_TAC THEN ASM_SIMP_TAC [ARITH] THENL
       [ASM_SIMP_TAC [BILINEAR_RSUB, BILINEAR_LSUB] THEN VECTOR_ARITH_TAC,
        ASM_ARITH_TAC],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [LE]) THEN
    DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    ASM_SIMP_TAC [← GSYM NOT_LT, VSUM_TRIV_NUMSEG, ← ARITH_RULE (← q r"n < SUC n")] THEN
    ASM_SIMP_TAC [← GSYM ADD1, ADD_CLAUSES] THEN
    ASM_SIMP_TAC [BILINEAR_RSUB, BILINEAR_LSUB] THEN VECTOR_ARITH_TAC)

  let BILINEAR_VSUM_PARTIAL_PRE ← prove
   r"!f g h:real^M->real^N->real^P m n.
        bilinear h
        ==> vsum (m..n) (\k. h (f k) (g(k) - g(k - 1))) =
                if m <= n then h (f(n + 1)) (g(n)) - h (f m) (g(m - 1)) -
                               vsum (m..n) (\k. h (f(k + 1) - f(k)) (g(k)))
                else vec 0"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (MP_TAC (← ISPECL [← q r"f:num->real^M", ← q r"\k. (g:num->real^N)(k - 1)",
                   ← q r"m:num", ← q r"n:num"] (← MATCH_MP BILINEAR_VSUM_PARTIAL_SUC th)))) THEN
    REWRITE_TAC [ADD_SUB] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC [])

  let BILINEAR_VSUM_CONVOLUTION_1 ← prove
   r"!bop:real^M->real^N->real^P a b n.
        bilinear bop
        ==> vsum(0..n) (\m. vsum (0..m) (\i. bop (a i) (b(m - i)))) =
            vsum(0..n) (\m. bop (a m) (vsum(0..n-m) b))"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [BILINEAR_RSUM, FINITE_NUMSEG] THEN
    SIMP_TAC [VSUM_VSUM_PRODUCT, FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ_GENERAL_INVERSES THEN
    EXISTS_TAC (← q r"(\(x,y). y,x - y):num#num->num#num") THEN
    EXISTS_TAC (← q r"(\(x,y). x + y,x):num#num->num#num") THEN
    REWRITE_TAC [FORALL_IN_GSPEC] THEN REWRITE_TAC [IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC [PAIR_EQ, IN_NUMSEG, LE_0] THEN ARITH_TAC)

  let BILINEAR_VSUM_CONVOLUTION_2 ← prove
   r"!bop:real^M->real^N->real^P a b n.
    bilinear bop
    ==> vsum(0..n) (\m. vsum(0..m) (\k. vsum(0..k) (\i. bop (a i) (b(k-i))))) =
        vsum(0..n) (\m. bop (vsum(0..m) a) (vsum(0..n-m) b))"
   (REPEAT STRIP_TAC THEN
    ABBREV_TAC (← q r"summery:(num->real^P)->real^P = vsum(0..n)") THEN
    ASM_SIMP_TAC [BILINEAR_LSUM, FINITE_NUMSEG] THEN
    ASM_SIMP_TAC [BILINEAR_RSUM, FINITE_NUMSEG] THEN
    SIMP_TAC [VSUM_VSUM_PRODUCT, FINITE_NUMSEG] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    SIMP_TAC [VSUM_VSUM_PRODUCT, FINITE_NUMSEG, FINITE_PRODUCT_DEPENDENT] THEN
    MATCH_MP_TAC VSUM_EQ_GENERAL_INVERSES THEN
    EXISTS_TAC
     (← q r"(\(m,k,i). (n-m)+i,i,k - i):num#num#num->num#num#num") THEN
    EXISTS_TAC
     (← q r"(\(a,b,c). n-(a-b),b+c,b):num#num#num->num#num#num") THEN
    REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC [IN_NUMSEG, LE_0, PAIR_EQ] THEN ARITH_TAC)

  return { bilinear, BILINEAR_SWAP, BILINEAR_LADD, BILINEAR_RADD, BILINEAR_LMUL,
           BILINEAR_RMUL, BILINEAR_LNEG, BILINEAR_RNEG, BILINEAR_LZERO, BILINEAR_RZERO,
           BILINEAR_LSUB, BILINEAR_RSUB, BILINEAR_LSUM, BILINEAR_RSUM, BILINEAR_VSUM,
           BILINEAR_BOUNDED, BILINEAR_BOUNDED_POS, BILINEAR_VSUM_PARTIAL_SUC,
           BILINEAR_VSUM_PARTIAL_PRE, BILINEAR_VSUM_CONVOLUTION_1,
           BILINEAR_VSUM_CONVOLUTION_2 }

/- ------------------------------------------------------------------------- -/
/- Adjoints; some basics about Lipschitz functions.  (vectors.ml 2477-2636)  -/
/- ------------------------------------------------------------------------- -/

structure Adjoint where
  adjoint : thm
  ADJOINT_WORKS : thm
  ADJOINT_LINEAR : thm
  ADJOINT_CLAUSES : thm
  ADJOINT_ADJOINT : thm
  ADJOINT_UNIQUE : thm
  ADJOINT_COMPOSE : thm
  SELF_ADJOINT_COMPOSE : thm
  SELF_ADJOINT_ORTHOGONAL_EIGENVECTORS : thm
  ORTHOGONAL_PROJECTION_ALT : thm
  ORTHOGONAL_PROJECTION_EQ_SELF_ADJOINT_IDEMPOTENT : thm
  LIPSCHITZ_ON_POS : thm
  LIPSCHITZ_POS : thm
  LIPSCHITZ_ON_COMPOSE : thm
  LINEAR_IMP_LIPSCHITZ : thm
  LIPSCHITZ_ON_COMPONENTWISE : thm
  deriving Inhabited

@[nospecialize]
def setupAdjoint [HolBase] (D : VectorsDeps) (BBasics : Basics) (BVectorArith : VectorArith)
    (BDotProps : DotProps) (BNorm1 : Norm1) (BNorm2 : Norm2) (BVSum1 : VSum1)
    (BBasis : Basis) (BOrth : Orth) (BLinear : Linear) : ExceptT String IO Adjoint := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, SELECT_CONV, new_definition, .. } := D
  let { CONJ_ASSOC, FINITE_NUMSEG, FORALL_IN_IMAGE, .. } := D.core1
  let { FUN_EQ_THM, IMP_CONJ_ALT, IMP_IMP, IN_UNIV, LAMBDA_BETA, LEFT_IMP_EXISTS_THM,
        MONO_FORALL, MONO_IMP, .. } := D.core2
  let { REAL_EQ_MUL_RCANCEL, REAL_LE_LMUL_EQ, REAL_LE_RMUL, REAL_LE_TRANS, REAL_LT_MUL,
        REAL_MUL_ASSOC, .. } := D.core3
  let { RIGHT_IMP_EXISTS_THM, RIGHT_IMP_FORALL_THM, SKOLEM_THM, SUBSET, .. } := D.core4
  let { SUM_LE_NUMSEG, SUM_LMUL, SUM_RMUL, SUM_SWAP_NUMSEG, SWAP_FORALL_THM, o_THM, .. } :=
    D.core5
  let { dot, .. } := BBasics
  let { VECTOR_ARITH, VECTOR_MUL_COMPONENT, VECTOR_SUB_COMPONENT, VECTOR_SUB_EQ,
        VECTOR_SUB_REFL, .. } := BVectorArith
  let { DOT_LMUL, DOT_LSUB, DOT_LZERO, DOT_RADD, DOT_RMUL, DOT_SYM, .. } := BDotProps
  let { COMPONENT_LE_NORM, NORM_POS_LE, .. } := BNorm1
  let { NORM_LE_L1, .. } := BNorm2
  let { VSUM_COMPONENT, .. } := BVSum1
  let { BASIS_EXPANSION, VECTOR_EQ_LDOT, VECTOR_EQ_RDOT, .. } := BBasis
  let { ORTHOGONAL_REFL, orthogonal, .. } := BOrth
  let { LINEAR_BOUNDED, LINEAR_CMUL, LINEAR_COMPOSE, LINEAR_SUB, LINEAR_VSUM, linear, .. } :=
    BLinear
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let adjoint ← new_definition
   r"adjoint(f:real^M->real^N) = @f'. !x y. f(x) dot y = x dot f'(y)"

  let ADJOINT_WORKS ← prove
   r"!f:real^M->real^N. linear f ==> !x y. f(x) dot y = x dot (adjoint f)(y)"
   (GEN_TAC THEN DISCH_TAC THEN SIMP_TAC [adjoint] THEN CONV_TAC SELECT_CONV THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN ONCE_REWRITE_TAC [← GSYM SKOLEM_THM] THEN
    X_GEN_TAC (← q r"y:real^N") THEN
    EXISTS_TAC (← q r"(lambda i. (f:real^M->real^N) (basis i) dot y):real^M") THEN
    X_GEN_TAC (← q r"x:real^M") THEN
    GEN_REWRITE_TAC (funpow 2 LAND_CONV o RAND_CONV) [← GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC [LINEAR_VSUM, FINITE_NUMSEG] THEN
    SIMP_TAC [dot, LAMBDA_BETA, VSUM_COMPONENT, ← GSYM SUM_LMUL, ← GSYM SUM_RMUL] THEN
    GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
    ASM_SIMP_TAC [o_THM, VECTOR_MUL_COMPONENT, LINEAR_CMUL, REAL_MUL_ASSOC])

  let ADJOINT_LINEAR ← prove
   r"!f:real^M->real^N. linear f ==> linear(adjoint f)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [linear, ← GSYM VECTOR_EQ_LDOT] THEN
    ASM_SIMP_TAC [DOT_RMUL, DOT_RADD, ← GSYM ADJOINT_WORKS])

  let ADJOINT_CLAUSES ← prove
   r"!f:real^M->real^N.
     linear f ==> (!x y. x dot (adjoint f)(y) = f(x) dot y) /\
                  (!x y. (adjoint f)(y) dot x = y dot f(x))"
   (MESON_TAC [ADJOINT_WORKS, DOT_SYM])

  let ADJOINT_ADJOINT ← prove
   r"!f:real^M->real^N. linear f ==> adjoint(adjoint f) = f"
   (SIMP_TAC [FUN_EQ_THM, ← GSYM VECTOR_EQ_LDOT, ADJOINT_CLAUSES, ADJOINT_LINEAR])

  let ADJOINT_UNIQUE ← prove
   r"!f f'. linear f /\ (!x y. f'(x) dot y = x dot f(y))
          ==> f' = adjoint f"
   (SIMP_TAC [FUN_EQ_THM, ← GSYM VECTOR_EQ_RDOT, ADJOINT_CLAUSES])

  let ADJOINT_COMPOSE ← prove
   r"!f g:real^N->real^N.
        linear f /\ linear g ==> adjoint(f o g) = adjoint g o adjoint f"
   (REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC ADJOINT_UNIQUE THEN
    ASM_SIMP_TAC [LINEAR_COMPOSE, o_THM, ADJOINT_CLAUSES])

  let SELF_ADJOINT_COMPOSE ← prove
   r"!f g:real^N->real^N.
        linear f /\ linear g /\ adjoint f = f /\ adjoint g = g
        ==> (adjoint(f o g) = f o g <=> f o g = g o f)"
   (SIMP_TAC [ADJOINT_COMPOSE] THEN MESON_TAC [])

  let SELF_ADJOINT_ORTHOGONAL_EIGENVECTORS ← prove
   r"!f:real^N->real^N v w a b.
        linear f /\ adjoint f = f /\ f v = a % v /\ f w = b % w /\ ~(a = b)
        ==> orthogonal v w"
   (REPEAT STRIP_TAC THEN FIRST_ASSUM (fun th => tactic_of do
      pure (MP_TAC (← SPECL [← q r"v:real^N", ← q r"w:real^N"]
        (← MATCH_MP ADJOINT_WORKS th)))) THEN
    ASM_REWRITE_TAC [DOT_LMUL, DOT_RMUL, orthogonal, REAL_EQ_MUL_RCANCEL])

  let ORTHOGONAL_PROJECTION_ALT ← prove
   r"!f:real^N->real^N.
        linear f
        ==> ((!x y. orthogonal (f x - x) (f x - f y)) <=>
             (!x y. orthogonal (f x - x) (f y)))"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN MATCH_MP_TAC MONO_FORALL THEN
    X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN X_GEN_TAC (← q r"y:real^N") THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"x - y:real^N")) THEN
    ASM_SIMP_TAC [LINEAR_SUB, ← va r"x - (x - y):real^N = y"])

  let ORTHOGONAL_PROJECTION_EQ_SELF_ADJOINT_IDEMPOTENT ← prove
   r"!f:real^N->real^N.
        linear f
        ==> ((!x y. orthogonal (f x - x) (f x - f y)) <=>
             adjoint f = f /\ f o f = f)"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [ORTHOGONAL_PROJECTION_ALT] THEN
    EQ_TAC THENL
     [REPEAT STRIP_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC ADJOINT_UNIQUE THEN
        ASM_REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [← q r"x:real^N", ← q r"y:real^N"] THEN
        FIRST_X_ASSUM (fun th => tactic_of do
          pure (MP_TAC (← ISPECL [← q r"x:real^N", ← q r"y:real^N"] th) THEN
                MP_TAC (← ISPECL [← q r"y:real^N", ← q r"x:real^N"] th))) THEN
        REWRITE_TAC [orthogonal, DOT_LSUB] THEN
        REWRITE_TAC [DOT_SYM] THEN REAL_ARITH_TAC,
        REWRITE_TAC [FUN_EQ_THM, o_THM] THEN X_GEN_TAC (← q r"x:real^N") THEN
        FIRST_X_ASSUM (MP_TAC o SPECL
         [← q r"(f:real^N->real^N) x", ← q r"f x - x:real^N"]) THEN
        ASM_SIMP_TAC [LINEAR_SUB, ORTHOGONAL_REFL, VECTOR_SUB_EQ]],
     REWRITE_TAC [FUN_EQ_THM, o_THM] THEN STRIP_TAC THEN
     FIRST_ASSUM (fun th => tactic_of do
       pure (MP_TAC (← GSYM (← MATCH_MP ADJOINT_WORKS th)))) THEN
     ASM_SIMP_TAC [orthogonal, LINEAR_SUB, VECTOR_SUB_REFL, DOT_LZERO]])

  let LIPSCHITZ_ON_POS ← prove
   r"!f:real^M->real^N s.
        (?B. !x y. x IN s /\ y IN s
                   ==> norm(f x - f y) <= B * norm(x - y)) <=>
        (?B. &0 < B /\
             !x y. x IN s /\ y IN s
                   ==> norm(f x - f y) <= B * norm(x - y))"
   (REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC, MESON_TAC []] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"B:real")
      (fun th => tactic_of do pure (EXISTS_TAC (← q r"abs B + &1") THEN MP_TAC th))) THEN
    REWRITE_TAC [← REAL_ARITH (← q r"&0 < abs B + &1")] THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC [] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [NORM_POS_LE] THEN
    REAL_ARITH_TAC)

  let LIPSCHITZ_POS ← prove
   r"!f:real^M->real^N.
        (?B. !x y. norm(f x - f y) <= B * norm(x - y)) <=>
        (?B. &0 < B /\ !x y. norm(f x - f y) <= B * norm(x - y))"
   (GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^M->real^N", ← q r"(:real^M)"] LIPSCHITZ_ON_POS) THEN
    REWRITE_TAC [IN_UNIV])

  let LIPSCHITZ_ON_COMPOSE ← prove
   r"!f:real^M->real^N g:real^N->real^P s t.
        (?B. !x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y)) /\
        (?B. !x y. x IN t /\ y IN t ==> norm(g x - g y) <= B * norm(x - y)) /\
        IMAGE f s SUBSET t
        ==> ?B. !x y. x IN s /\ y IN s
                      ==> norm(g(f x) - g(f y)) <= B * norm(x - y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [CONJ_ASSOC, SUBSET, FORALL_IN_IMAGE] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    ONCE_REWRITE_TAC [LIPSCHITZ_ON_POS] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"B:real"))
                                (X_CHOOSE_TAC (← q r"C:real"))) THEN
    EXISTS_TAC (← q r"B * C:real") THEN ASM_SIMP_TAC [REAL_LT_MUL] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:real^M", ← q r"y:real^M"] THEN STRIP_TAC THEN
    TRANS_TAC REAL_LE_TRANS (← q r"C * norm((f:real^M->real^N) x - f y)") THEN
    ASM_SIMP_TAC [← REAL_ARITH (← q r"(B * C) * d:real = C * B * d")] THEN
    ASM_SIMP_TAC [REAL_LE_LMUL_EQ])

  let LINEAR_IMP_LIPSCHITZ ← prove
   r"!f:real^M->real^N.
        linear f ==> ?B. !x y. norm(f x - f y) <= B * norm(x - y)"
   (SIMP_TAC [← GSYM LINEAR_SUB] THEN MESON_TAC [LINEAR_BOUNDED])

  let LIPSCHITZ_ON_COMPONENTWISE ← prove
   r"!f:real^M->real^N s.
      (?B. !x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y)) <=>
      !i. 1 <= i /\ i <= dimindex(:N)
          ==> ?B. !x y. x IN s /\ y IN s
                        ==> abs(f x$i - f y$i) <= B * norm(x - y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM VECTOR_SUB_COMPONENT] THEN EQ_TAC THENL
     [MESON_TAC [COMPONENT_LE_NORM, REAL_LE_TRANS], ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"B:num->real") THEN REWRITE_TAC [RIGHT_IMP_FORALL_THM, IMP_IMP] THEN
    DISCH_TAC THEN EXISTS_TAC (← q r"sum(1..dimindex(:N)) B") THEN
    MAP_EVERY X_GEN_TAC [← q r"x:real^M", ← q r"y:real^M"] THEN STRIP_TAC THEN
    W (MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    REWRITE_TAC [← GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    ASM_SIMP_TAC [])

  return { adjoint, ADJOINT_WORKS, ADJOINT_LINEAR, ADJOINT_CLAUSES, ADJOINT_ADJOINT,
           ADJOINT_UNIQUE, ADJOINT_COMPOSE, SELF_ADJOINT_COMPOSE,
           SELF_ADJOINT_ORTHOGONAL_EIGENVECTORS, ORTHOGONAL_PROJECTION_ALT,
           ORTHOGONAL_PROJECTION_EQ_SELF_ADJOINT_IDEMPOTENT, LIPSCHITZ_ON_POS,
           LIPSCHITZ_POS, LIPSCHITZ_ON_COMPOSE, LINEAR_IMP_LIPSCHITZ,
           LIPSCHITZ_ON_COMPONENTWISE }

/- ------------------------------------------------------------------------- -/
/- Matrix notation. NB: an MxN matrix is of type real^N^M, not real^M^N.     -/
/- Symmetric and normal matrices.  (vectors.ml 2638-2796)                    -/
/- ------------------------------------------------------------------------- -/

structure Matrix where
  matrix_cmul : thm
  matrix_neg : thm
  matrix_add : thm
  matrix_sub : thm
  matrix_mul : thm
  matrix_vector_mul : thm
  vector_matrix_mul : thm
  mat : thm
  transp : thm
  row : thm
  column : thm
  rows : thm
  columns : thm
  MATRIX_CMUL_COMPONENT : thm
  MATRIX_ADD_COMPONENT : thm
  MATRIX_SUB_COMPONENT : thm
  MATRIX_NEG_COMPONENT : thm
  TRANSP_COMPONENT : thm
  MAT_COMPONENT : thm
  MAT_0_COMPONENT : thm
  MATRIX_ADD_ROW : thm
  MATRIX_SUB_ROW : thm
  MATRIX_NEG_ROW : thm
  MATRIX_CMUL_ROW : thm
  MAT_0_ROW : thm
  symmetric_matrix : thm
  normal_matrix : thm
  SYMMETRIC_IMP_NORMAL_MATRIX : thm
  deriving Inhabited

@[nospecialize]
def setupMatrix [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith) :
    ExceptT String IO Matrix := do
  -- @@SCOPE BEGIN
  let { make_overloadable, new_definition, overload_interface, parse_as_infix,
        prioritize_real, .. } := D
  let { CART_EQ, CART_EQ_FULL, COND_ID, FINITE_INDEX_INRANGE, FINITE_INDEX_INRANGE_2, .. } :=
    D.core1
  let { LAMBDA_BETA, .. } := D.core2
  let { VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, VECTOR_NEG_COMPONENT,
        VECTOR_SUB_COMPONENT, VEC_COMPONENT, .. } := BVectorArith
  -- @@SCOPE END

  overload_interface "--" (← q r"(matrix_neg):real^N^M->real^N^M")
  overload_interface "+" (← q r"(matrix_add):real^N^M->real^N^M->real^N^M")
  overload_interface "-" (← q r"(matrix_sub):real^N^M->real^N^M->real^N^M")

  make_overloadable "**" (← qty "A->B->C")

  overload_interface "**" (← q r"(vector_matrix_mul):real^M->real^N^M->real^N")
  overload_interface "**" (← q r"(matrix_mul):real^N^M->real^P^N->real^P^M")
  overload_interface "**" (← q r"(matrix_vector_mul):real^N^M->real^N->real^M")

  parse_as_infix ("%%", (21, "right"))

  prioritize_real

  let matrix_cmul ← new_definition
   r"((%%):real->real^N^M->real^N^M) c A = lambda i j. c * A$i$j"

  let matrix_neg ← new_definition
   r"!A:real^N^M. --A = lambda i j. --(A$i$j)"

  let matrix_add ← new_definition
   r"!A:real^N^M B:real^N^M. A + B = lambda i j. A$i$j + B$i$j"

  let matrix_sub ← new_definition
   r"!A:real^N^M B:real^N^M. A - B = lambda i j. A$i$j - B$i$j"

  let matrix_mul ← new_definition
   r"!A:real^N^M B:real^P^N.
        A ** B =
          lambda i j. sum(1..dimindex(:N)) (\k. A$i$k * B$k$j)"

  let matrix_vector_mul ← new_definition
   r"!A:real^N^M x:real^N.
        A ** x = lambda i. sum(1..dimindex(:N)) (\j. A$i$j * x$j)"

  let vector_matrix_mul ← new_definition
   r"!A:real^N^M x:real^M.
        x ** A = lambda j. sum(1..dimindex(:M)) (\i. A$i$j * x$i)"

  let mat ← new_definition
   r"(mat:num->real^N^M) k = lambda i j. if i = j then &k else &0"

  let transp ← new_definition
   r"(transp:real^N^M->real^M^N) A = lambda i j. A$j$i"

  let row ← new_definition
   r"(row:num->real^N^M->real^N) i A = lambda j. A$i$j"

  let column ← new_definition
   r"(column:num->real^N^M->real^M) j A = lambda i. A$i$j"

  let rows ← new_definition
   r"rows(A:real^N^M) = { row i A | 1 <= i /\ i <= dimindex(:M)}"

  let columns ← new_definition
   r"columns(A:real^N^M) = { column i A | 1 <= i /\ i <= dimindex(:N)}"

  let MATRIX_CMUL_COMPONENT ← prove
   r"!c A:real^N^M i. (c %% A)$i$j = c * A$i$j"
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN (← q r"?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k")
    CHOOSE_TAC THENL [REWRITE_TAC [FINITE_INDEX_INRANGE], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l")
    CHOOSE_TAC THENL [REWRITE_TAC [FINITE_INDEX_INRANGE], ALL_TAC] THEN
    ASM_SIMP_TAC [matrix_cmul, CART_EQ, LAMBDA_BETA])

  let MATRIX_ADD_COMPONENT ← prove
   r"!A B:real^N^M i j. (A + B)$i$j = A$i$j + B$i$j"
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN (← q r"?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k")
    CHOOSE_TAC THENL [REWRITE_TAC [FINITE_INDEX_INRANGE], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l")
    CHOOSE_TAC THENL [REWRITE_TAC [FINITE_INDEX_INRANGE], ALL_TAC] THEN
    ASM_SIMP_TAC [matrix_add, LAMBDA_BETA])

  let MATRIX_SUB_COMPONENT ← prove
   r"!A B:real^N^M i j. (A - B)$i$j = A$i$j - B$i$j"
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN (← q r"?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k")
    CHOOSE_TAC THENL [REWRITE_TAC [FINITE_INDEX_INRANGE], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l")
    CHOOSE_TAC THENL [REWRITE_TAC [FINITE_INDEX_INRANGE], ALL_TAC] THEN
    ASM_SIMP_TAC [matrix_sub, LAMBDA_BETA])

  let MATRIX_NEG_COMPONENT ← prove
   r"!A:real^N^M i j. (--A)$i$j = --(A$i$j)"
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN (← q r"?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k")
    CHOOSE_TAC THENL [REWRITE_TAC [FINITE_INDEX_INRANGE], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l")
    CHOOSE_TAC THENL [REWRITE_TAC [FINITE_INDEX_INRANGE], ALL_TAC] THEN
    ASM_SIMP_TAC [matrix_neg, LAMBDA_BETA])

  let TRANSP_COMPONENT ← prove
   r"!A:real^N^M i j. (transp A)$i$j = A$j$i"
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN (← q r"?k. 1 <= k /\ k <= dimindex(:N) /\
                    (!A:real^M^N. A$i = A$k) /\ (!z:real^N. z$i = z$k)")
    CHOOSE_TAC THENL [REWRITE_TAC [FINITE_INDEX_INRANGE_2], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"?l. 1 <= l /\ l <= dimindex(:M) /\
                    (!A:real^N^M. A$j = A$l) /\ (!z:real^M. z$j = z$l)")
    CHOOSE_TAC THENL [REWRITE_TAC [FINITE_INDEX_INRANGE_2], ALL_TAC] THEN
    ASM_SIMP_TAC [transp, LAMBDA_BETA])

  let MAT_COMPONENT ← prove
   r"!n i j.
        1 <= i /\ i <= dimindex(:M) /\
        1 <= j /\ j <= dimindex(:N)
        ==> (mat n:real^N^M)$i$j = if i = j then &n else &0"
   (SIMP_TAC [mat, LAMBDA_BETA])

  let MAT_0_COMPONENT ← prove
   r"!i j. (mat 0:real^N^M)$i$j = &0"
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN (← q r"?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k")
    CHOOSE_TAC THENL [REWRITE_TAC [FINITE_INDEX_INRANGE], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l")
    CHOOSE_TAC THENL [REWRITE_TAC [FINITE_INDEX_INRANGE], ALL_TAC] THEN
    ASM_SIMP_TAC [mat, COND_ID, LAMBDA_BETA])

  let MATRIX_ADD_ROW ← prove
   r"!X Y:real^M^N i. (X + Y)$i = X$i + Y$i"
   (REWRITE_TAC [CART_EQ_FULL, VECTOR_ADD_COMPONENT, MATRIX_ADD_COMPONENT])

  let MATRIX_SUB_ROW ← prove
   r"!X Y:real^M^N i. (X - Y)$i = X$i - Y$i"
   (REWRITE_TAC [CART_EQ_FULL, VECTOR_SUB_COMPONENT, MATRIX_SUB_COMPONENT])

  let MATRIX_NEG_ROW ← prove
   r"!X:real^M^N i. (--X)$i = --(X$i)"
   (REWRITE_TAC [CART_EQ_FULL, VECTOR_NEG_COMPONENT, MATRIX_NEG_COMPONENT])

  let MATRIX_CMUL_ROW ← prove
   r"!c X:real^M^N i. (c %% X)$i = c % X$i"
   (REWRITE_TAC [CART_EQ_FULL, VECTOR_MUL_COMPONENT, MATRIX_CMUL_COMPONENT])

  let MAT_0_ROW ← prove
   r"mat 0:real^M^N$i = vec 0"
   (REWRITE_TAC [CART_EQ_FULL, MAT_0_COMPONENT, VEC_COMPONENT])

  let symmetric_matrix ← new_definition
   r"symmetric_matrix (A:real^N^N) <=> transp A = A"

  let normal_matrix ← new_definition
   r"normal_matrix (A:real^N^N) <=> transp A ** A = A ** transp A"

  let SYMMETRIC_IMP_NORMAL_MATRIX ← prove
   r"!A:real^N^N. symmetric_matrix A ==> normal_matrix A"
   (SIMP_TAC [symmetric_matrix, normal_matrix])

  return { matrix_cmul, matrix_neg, matrix_add, matrix_sub, matrix_mul,
           matrix_vector_mul, vector_matrix_mul, mat, transp, row, column, rows, columns,
           MATRIX_CMUL_COMPONENT, MATRIX_ADD_COMPONENT, MATRIX_SUB_COMPONENT,
           MATRIX_NEG_COMPONENT, TRANSP_COMPONENT, MAT_COMPONENT, MAT_0_COMPONENT,
           MATRIX_ADD_ROW, MATRIX_SUB_ROW, MATRIX_NEG_ROW, MATRIX_CMUL_ROW, MAT_0_ROW,
           symmetric_matrix, normal_matrix, SYMMETRIC_IMP_NORMAL_MATRIX }

/- ------------------------------------------------------------------------- -/
/- A decision procedure for matrices analogous to VECTOR_ARITH, and matrix  -/
/- algebra.  (vectors.ml 2800-3058)                                          -/
/- ------------------------------------------------------------------------- -/

structure MatArith where
  MATRIX_ARITH_TAC : tactic
  MATRIX_ARITH : term → ExceptT String IO thm
  MAT_CMUL : thm
  ROW_0 : thm
  COLUMN_0 : thm
  MATRIX_CMUL_ASSOC : thm
  MATRIX_CMUL_LID : thm
  MATRIX_ADD_SYM : thm
  MATRIX_ADD_ASSOC : thm
  MATRIX_ADD_LID : thm
  MATRIX_ADD_RID : thm
  MATRIX_ADD_LNEG : thm
  MATRIX_ADD_RNEG : thm
  MATRIX_SUB : thm
  MATRIX_SUB_REFL : thm
  MATRIX_SUB_EQ : thm
  MATRIX_SUB_ADD : thm
  MATRIX_SUB_ADD2 : thm
  MATRIX_ADD_LDISTRIB : thm
  MATRIX_MUL_LID : thm
  MATRIX_MUL_RID : thm
  MATRIX_MUL_ASSOC : thm
  MATRIX_MUL_LZERO : thm
  MATRIX_MUL_RZERO : thm
  MATRIX_ADD_RDISTRIB : thm
  MATRIX_SUB_LDISTRIB : thm
  MATRIX_SUB_RDISTRIB : thm
  MATRIX_MUL_LMUL : thm
  MATRIX_MUL_RMUL : thm
  MATRIX_CMUL_ADD_LDISTRIB : thm
  MATRIX_CMUL_SUB_LDISTRIB : thm
  MATRIX_CMUL_ADD_RDISTRIB : thm
  MATRIX_CMUL_SUB_RDISTRIB : thm
  MATRIX_CMUL_RZERO : thm
  MATRIX_CMUL_LZERO : thm
  MATRIX_NEG_MINUS1 : thm
  MATRIX_ADD_AC : thm
  MATRIX_NEG_ADD : thm
  MATRIX_NEG_SUB : thm
  MATRIX_NEG_0 : thm
  MATRIX_SUB_RZERO : thm
  MATRIX_SUB_LZERO : thm
  MATRIX_NEG_EQ_0 : thm
  MATRIX_VECTOR_MUL_ASSOC : thm
  MATRIX_VECTOR_MUL_LID : thm
  MATRIX_VECTOR_MUL_LZERO : thm
  MATRIX_VECTOR_MUL_RZERO : thm
  MATRIX_VECTOR_MUL_ADD_LDISTRIB : thm
  MATRIX_VECTOR_MUL_SUB_LDISTRIB : thm
  MATRIX_VECTOR_MUL_ADD_RDISTRIB : thm
  MATRIX_VECTOR_MUL_SUB_RDISTRIB : thm
  MATRIX_VECTOR_MUL_RMUL : thm
  MATRIX_MUL_LNEG : thm
  deriving Inhabited

@[nospecialize]
def setupMatArith [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BMatrix : Matrix) : ExceptT String IO MatArith := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, .. } := D
  let { AND_FORALL_THM, CART_EQ, CART_EQ_FULL, COND_ID, COND_RAND, COND_RATOR,
        CONJ_ASSOC, EQ_SYM_EQ, .. } := D.core1
  let { IMP_IMP, IN_NUMSEG, LAMBDA_BETA, MONO_FORALL, .. } := D.core2
  let { REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB, REAL_MUL_AC, REAL_MUL_ASSOC,
        REAL_MUL_LID, REAL_MUL_LZERO, REAL_MUL_RID, .. } := D.core3
  let { REAL_MUL_RZERO, REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB, SUM_0, SUM_ADD_NUMSEG,
        SUM_DELTA, SUM_EQ_NUMSEG, .. } := D.core4
  let { SUM_LMUL, SUM_RMUL, SUM_SUB_NUMSEG, SUM_SWAP_NUMSEG, .. } := D.core5
  let { VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, VECTOR_SUB_COMPONENT,
        VEC_COMPONENT, .. } := BVectorArith
  let { MATRIX_ADD_COMPONENT, MATRIX_CMUL_COMPONENT, MATRIX_NEG_COMPONENT,
        MATRIX_SUB_COMPONENT, MAT_0_COMPONENT, MAT_COMPONENT, column, mat, matrix_add,
        matrix_cmul, matrix_mul, matrix_sub, matrix_vector_mul, row, .. } := BMatrix
  -- @@SCOPE END

  let MATRIX_ARITH_TAC : tactic ← do
    let CART2_EQ_FULL ← prove
     r"!x y:A^M^N. x = y <=> (!i j. x$i$j = y$i$j)"
     (REWRITE_TAC [CART_EQ_FULL])
    pure (POP_ASSUM_LIST (K ALL_TAC) THEN
      REPEAT (GEN_TAC ORELSE CONJ_TAC ORELSE DISCH_TAC ORELSE EQ_TAC) THEN
      REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [IMP_IMP, ← GSYM CONJ_ASSOC] THEN
      GEN_REWRITE_TAC ONCE_DEPTH_CONV [CART2_EQ_FULL] THEN
      REWRITE_TAC [AND_FORALL_THM] THEN TRY EQ_TAC THEN
      REPEAT ((MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) ORELSE GEN_TAC) THEN
      REWRITE_TAC [← TAUT (← q r"(a ==> b) /\ (a ==> c) <=> a ==> b /\ c"),
                   ← TAUT (← q r"(a ==> b) \/ (a ==> c) <=> a ==> b \/ c")] THEN
      TRY (MATCH_MP_TAC (← TAUT (← q r"(a ==> b ==> c) ==> (a ==> b) ==> (a ==> c)"))) THEN
      REWRITE_TAC [MATRIX_ADD_COMPONENT, MATRIX_SUB_COMPONENT,
        MATRIX_NEG_COMPONENT, MATRIX_CMUL_COMPONENT, MAT_0_COMPONENT] THEN
      REAL_ARITH_TAC)

  let MATRIX_ARITH (tm : term) : ExceptT String IO thm :=
    ExceptT.mk (HolCore.Tactics.prove HolBase.B tm MATRIX_ARITH_TAC)

  let MAT_CMUL ← prove
   r"!a. mat a = &a %% mat 1"
   (SIMP_TAC [CART_EQ, MAT_COMPONENT, MATRIX_CMUL_COMPONENT] THEN
    MESON_TAC [REAL_MUL_RID, REAL_MUL_RZERO])

  let ROW_0 ← prove
   r"!i. row i (mat 0:real^N^N) = vec 0"
   (SIMP_TAC [MAT_0_COMPONENT, CART_EQ, row, VEC_COMPONENT, LAMBDA_BETA])

  let COLUMN_0 ← prove
   r"!i. column i (mat 0:real^N^N) = vec 0"
   (SIMP_TAC [MAT_0_COMPONENT, CART_EQ, column, VEC_COMPONENT, LAMBDA_BETA])

  let MATRIX_CMUL_ASSOC ← prove r"!a b X:real^M^N. a %% (b %% X) = (a * b) %% X"
    MATRIX_ARITH_TAC
  let MATRIX_CMUL_LID ← prove r"!X:real^M^N. &1 %% X = X" MATRIX_ARITH_TAC
  let MATRIX_ADD_SYM ← prove r"!A:real^N^M B. A + B = B + A" MATRIX_ARITH_TAC
  let MATRIX_ADD_ASSOC ← prove r"!A:real^N^M B C. A + (B + C) = (A + B) + C"
    MATRIX_ARITH_TAC
  let MATRIX_ADD_LID ← prove r"!A. mat 0 + A = A" MATRIX_ARITH_TAC
  let MATRIX_ADD_RID ← prove r"!A. A + mat 0 = A" MATRIX_ARITH_TAC
  let MATRIX_ADD_LNEG ← prove r"!A. --A + A = mat 0" MATRIX_ARITH_TAC
  let MATRIX_ADD_RNEG ← prove r"!A. A + --A = mat 0" MATRIX_ARITH_TAC
  let MATRIX_SUB ← prove r"!A:real^N^M B. A - B = A + --B" MATRIX_ARITH_TAC
  let MATRIX_SUB_REFL ← prove r"!A. A - A = mat 0" MATRIX_ARITH_TAC
  let MATRIX_SUB_EQ ← prove r"!A B:real^N^M. A - B = mat 0 <=> A = B" MATRIX_ARITH_TAC
  let MATRIX_SUB_ADD ← prove r"!A B:real^N^M. (A - B) + B = A" MATRIX_ARITH_TAC
  let MATRIX_SUB_ADD2 ← prove r"!A B:real^N^M. A + (B - A) = B" MATRIX_ARITH_TAC

  let MATRIX_ADD_LDISTRIB ← prove
   r"!A:real^N^M B:real^P^N C. A ** (B + C) = A ** B + A ** C"
   (SIMP_TAC [matrix_mul, matrix_add, CART_EQ, LAMBDA_BETA,
              ← GSYM SUM_ADD_NUMSEG] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    ASM_SIMP_TAC [LAMBDA_BETA, REAL_ADD_LDISTRIB])

  let MATRIX_MUL_LID ← prove
   r"!A:real^N^M. mat 1 ** A = A"
   (REWRITE_TAC [matrix_mul,
     ← GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ]
      (← SPEC_ALL mat)] THEN
    SIMP_TAC [CART_EQ, LAMBDA_BETA] THEN REWRITE_TAC [COND_RATOR, COND_RAND] THEN
    SIMP_TAC [SUM_DELTA, REAL_MUL_LZERO, IN_NUMSEG, REAL_MUL_LID])

  let MATRIX_MUL_RID ← prove
   r"!A:real^N^M. A ** mat 1 = A"
   (REWRITE_TAC [matrix_mul, mat] THEN
    SIMP_TAC [CART_EQ, LAMBDA_BETA] THEN REWRITE_TAC [COND_RATOR, COND_RAND] THEN
    SIMP_TAC [SUM_DELTA, REAL_MUL_RZERO, IN_NUMSEG, REAL_MUL_RID])

  let MATRIX_MUL_ASSOC ← prove
   r"!A:real^N^M B:real^P^N C:real^Q^P. A ** B ** C = (A ** B) ** C"
   (REPEAT GEN_TAC THEN
    SIMP_TAC [matrix_mul, CART_EQ, LAMBDA_BETA, ← GSYM SUM_LMUL, ← GSYM SUM_RMUL] THEN
    REWRITE_TAC [REAL_MUL_ASSOC] THEN REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC [])

  let MATRIX_MUL_LZERO ← prove
   r"!A. (mat 0:real^N^M) ** (A:real^P^N) = mat 0"
   (SIMP_TAC [matrix_mul, mat, CART_EQ, LAMBDA_BETA, COND_ID, REAL_MUL_LZERO] THEN
    REWRITE_TAC [SUM_0])

  let MATRIX_MUL_RZERO ← prove
   r"!A. (A:real^N^M) ** (mat 0:real^P^N) = mat 0"
   (SIMP_TAC [matrix_mul, mat, CART_EQ, LAMBDA_BETA, COND_ID, REAL_MUL_RZERO] THEN
    REWRITE_TAC [SUM_0])

  let MATRIX_ADD_RDISTRIB ← prove
   r"!A:real^N^M B C:real^P^N. (A + B) ** C = A ** C + B ** C"
   (SIMP_TAC [matrix_mul, matrix_add, CART_EQ, LAMBDA_BETA] THEN
    REWRITE_TAC [REAL_ADD_RDISTRIB, SUM_ADD_NUMSEG])

  let MATRIX_SUB_LDISTRIB ← prove
   r"!A:real^N^M B C:real^P^N. A ** (B - C) = A ** B - A ** C"
   (SIMP_TAC [matrix_mul, matrix_sub, CART_EQ, LAMBDA_BETA] THEN
    REWRITE_TAC [REAL_SUB_LDISTRIB, SUM_SUB_NUMSEG])

  let MATRIX_SUB_RDISTRIB ← prove
   r"!A:real^N^M B C:real^P^N. (A - B) ** C = A ** C - B ** C"
   (SIMP_TAC [matrix_mul, matrix_sub, CART_EQ, LAMBDA_BETA] THEN
    REWRITE_TAC [REAL_SUB_RDISTRIB, SUM_SUB_NUMSEG])

  let MATRIX_MUL_LMUL ← prove
   r"!A:real^N^M B:real^P^N c. (c %% A) ** B = c %% (A ** B)"
   (SIMP_TAC [matrix_mul, matrix_cmul, CART_EQ, LAMBDA_BETA] THEN
    REWRITE_TAC [← GSYM REAL_MUL_ASSOC, SUM_LMUL])

  let MATRIX_MUL_RMUL ← prove
   r"!A:real^N^M B:real^P^N c. A ** (c %% B) = c %% (A ** B)"
   (SIMP_TAC [matrix_mul, matrix_cmul, CART_EQ, LAMBDA_BETA] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"A * c * B:real = c * A * B")] THEN
    REWRITE_TAC [SUM_LMUL])

  let MATRIX_CMUL_ADD_LDISTRIB ← prove
   r"!A:real^N^M B c. c %% (A + B) = c %% A + c %% B" MATRIX_ARITH_TAC
  let MATRIX_CMUL_SUB_LDISTRIB ← prove
   r"!A:real^N^M B c. c %% (A - B) = c %% A - c %% B" MATRIX_ARITH_TAC
  let MATRIX_CMUL_ADD_RDISTRIB ← prove
   r"!A:real^N^M b c. (b + c) %% A = b %% A + c %% A" MATRIX_ARITH_TAC
  let MATRIX_CMUL_SUB_RDISTRIB ← prove
   r"!A:real^N^M b c. (b - c) %% A = b %% A - c %% A" MATRIX_ARITH_TAC

  let MATRIX_CMUL_RZERO ← prove
   r"!c. c %% mat 0 = mat 0"
   (SIMP_TAC [matrix_cmul, mat, CART_EQ, LAMBDA_BETA, COND_ID, REAL_MUL_RZERO])

  let MATRIX_CMUL_LZERO ← prove
   r"!A. &0 %% A = mat 0"
   (SIMP_TAC [matrix_cmul, mat, CART_EQ, LAMBDA_BETA, COND_ID, REAL_MUL_LZERO])

  let MATRIX_NEG_MINUS1 ← prove r"!A:real^N^M. --A = --(&1) %% A" MATRIX_ARITH_TAC

  let MATRIX_ADD_AC ← prove
   r"(A:real^N^M) + B = B + A /\
   (A + B) + C = A + (B + C) /\
   A + (B + C) = B + (A + C)"
   MATRIX_ARITH_TAC

  let MATRIX_NEG_ADD ← prove r"!A B:real^N^M. --(A + B) = --A + --B" MATRIX_ARITH_TAC
  let MATRIX_NEG_SUB ← prove r"!A B:real^N^M. --(A - B) = B - A" MATRIX_ARITH_TAC
  let MATRIX_NEG_0 ← prove r"--(mat 0) = mat 0" MATRIX_ARITH_TAC
  let MATRIX_SUB_RZERO ← prove r"!A:real^N^M. A - mat 0 = A" MATRIX_ARITH_TAC
  let MATRIX_SUB_LZERO ← prove r"!A:real^N^M. mat 0 - A = --A" MATRIX_ARITH_TAC
  let MATRIX_NEG_EQ_0 ← prove r"!A:real^N^M. --A = mat 0 <=> A = mat 0" MATRIX_ARITH_TAC

  let MATRIX_VECTOR_MUL_ASSOC ← prove
   r"!A:real^N^M B:real^P^N x:real^P. A ** B ** x = (A ** B) ** x"
   (REPEAT GEN_TAC THEN
    SIMP_TAC [matrix_mul, matrix_vector_mul,
              CART_EQ, LAMBDA_BETA, ← GSYM SUM_LMUL, ← GSYM SUM_RMUL] THEN
    REWRITE_TAC [REAL_MUL_ASSOC] THEN REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC [])

  let MATRIX_VECTOR_MUL_LID ← prove
   r"!x:real^N. mat 1 ** x = x"
   (REWRITE_TAC [matrix_vector_mul,
     ← GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ]
      (← SPEC_ALL mat)] THEN
    SIMP_TAC [CART_EQ, LAMBDA_BETA] THEN REWRITE_TAC [COND_RATOR, COND_RAND] THEN
    SIMP_TAC [SUM_DELTA, REAL_MUL_LZERO, IN_NUMSEG, REAL_MUL_LID])

  let MATRIX_VECTOR_MUL_LZERO ← prove
   r"!x:real^N. mat 0 ** x = vec 0"
   (SIMP_TAC [mat, matrix_vector_mul, CART_EQ, VEC_COMPONENT, LAMBDA_BETA,
              COND_ID, REAL_MUL_LZERO, SUM_0])

  let MATRIX_VECTOR_MUL_RZERO ← prove
   r"!A:real^M^N. A ** vec 0 = vec 0"
   (SIMP_TAC [mat, matrix_vector_mul, CART_EQ, VEC_COMPONENT, LAMBDA_BETA,
              COND_ID, REAL_MUL_RZERO, SUM_0])

  let MATRIX_VECTOR_MUL_ADD_LDISTRIB ← prove
   r"!A:real^M^N x:real^M y. A ** (x + y) = A ** x + A ** y"
   (SIMP_TAC [CART_EQ, matrix_vector_mul, VECTOR_ADD_COMPONENT, LAMBDA_BETA,
              SUM_ADD_NUMSEG, REAL_ADD_LDISTRIB])

  let MATRIX_VECTOR_MUL_SUB_LDISTRIB ← prove
   r"!A:real^M^N x:real^M y. A ** (x - y) = A ** x - A ** y"
   (SIMP_TAC [CART_EQ, matrix_vector_mul, VECTOR_SUB_COMPONENT, LAMBDA_BETA,
              SUM_SUB_NUMSEG, REAL_SUB_LDISTRIB])

  let MATRIX_VECTOR_MUL_ADD_RDISTRIB ← prove
   r"!A:real^M^N B x:real^M. (A + B) ** x = (A ** x) + (B ** x)"
   (SIMP_TAC [CART_EQ, matrix_vector_mul, matrix_add, LAMBDA_BETA,
              VECTOR_ADD_COMPONENT, REAL_ADD_RDISTRIB, SUM_ADD_NUMSEG])

  let MATRIX_VECTOR_MUL_SUB_RDISTRIB ← prove
   r"!A:real^M^N B x:real^M. (A - B) ** x = (A ** x) - (B ** x)"
   (SIMP_TAC [CART_EQ, matrix_vector_mul, matrix_sub, LAMBDA_BETA,
              VECTOR_SUB_COMPONENT, REAL_SUB_RDISTRIB, SUM_SUB_NUMSEG])

  let MATRIX_VECTOR_MUL_RMUL ← prove
   r"!A:real^M^N x:real^M c. A ** (c % x) = c % (A ** x)"
   (SIMP_TAC [CART_EQ, VECTOR_MUL_COMPONENT, matrix_vector_mul, LAMBDA_BETA] THEN
    REWRITE_TAC [← GSYM SUM_LMUL] THEN REWRITE_TAC [REAL_MUL_AC])

  let MATRIX_MUL_LNEG ← prove
   r"!A:real^N^M B:real^P^N. (--A) ** B = --(A ** B)"
   (REWRITE_TAC [MATRIX_NEG_MINUS1, MATRIX_MUL_LMUL])

  return { MATRIX_ARITH_TAC, MATRIX_ARITH, MAT_CMUL, ROW_0, COLUMN_0, MATRIX_CMUL_ASSOC,
           MATRIX_CMUL_LID, MATRIX_ADD_SYM, MATRIX_ADD_ASSOC, MATRIX_ADD_LID,
           MATRIX_ADD_RID, MATRIX_ADD_LNEG, MATRIX_ADD_RNEG, MATRIX_SUB, MATRIX_SUB_REFL,
           MATRIX_SUB_EQ, MATRIX_SUB_ADD, MATRIX_SUB_ADD2, MATRIX_ADD_LDISTRIB,
           MATRIX_MUL_LID, MATRIX_MUL_RID, MATRIX_MUL_ASSOC, MATRIX_MUL_LZERO,
           MATRIX_MUL_RZERO, MATRIX_ADD_RDISTRIB, MATRIX_SUB_LDISTRIB,
           MATRIX_SUB_RDISTRIB, MATRIX_MUL_LMUL, MATRIX_MUL_RMUL,
           MATRIX_CMUL_ADD_LDISTRIB, MATRIX_CMUL_SUB_LDISTRIB, MATRIX_CMUL_ADD_RDISTRIB,
           MATRIX_CMUL_SUB_RDISTRIB, MATRIX_CMUL_RZERO, MATRIX_CMUL_LZERO,
           MATRIX_NEG_MINUS1, MATRIX_ADD_AC, MATRIX_NEG_ADD, MATRIX_NEG_SUB, MATRIX_NEG_0,
           MATRIX_SUB_RZERO, MATRIX_SUB_LZERO, MATRIX_NEG_EQ_0, MATRIX_VECTOR_MUL_ASSOC,
           MATRIX_VECTOR_MUL_LID, MATRIX_VECTOR_MUL_LZERO, MATRIX_VECTOR_MUL_RZERO,
           MATRIX_VECTOR_MUL_ADD_LDISTRIB, MATRIX_VECTOR_MUL_SUB_LDISTRIB,
           MATRIX_VECTOR_MUL_ADD_RDISTRIB, MATRIX_VECTOR_MUL_SUB_RDISTRIB,
           MATRIX_VECTOR_MUL_RMUL, MATRIX_MUL_LNEG }

/- ------------------------------------------------------------------------- -/
/- More matrix algebra; rows and columns; two ways of looking at matrix-    -/
/- vector multiplication; componentwise expansions.  (vectors.ml 3061-3342)  -/
/- ------------------------------------------------------------------------- -/

structure MatProps where
  MATRIX_MUL_RNEG : thm
  MATRIX_NEG_NEG : thm
  MATRIX_TRANSP_MUL : thm
  TRANSP_EQ_0 : thm
  SYMMETRIC_MATRIX_MUL : thm
  MATRIX_EQ : thm
  MATRIX_EQ_0 : thm
  MATRIX_VECTOR_MUL_COMPONENT : thm
  DOT_LMUL_MATRIX : thm
  TRANSP_MATRIX_CMUL : thm
  SYMMETRIC_MATRIX_CMUL : thm
  TRANSP_MATRIX_ADD : thm
  SYMMETRIC_MATRIX_ADD : thm
  TRANSP_MATRIX_SUB : thm
  SYMMETRIC_MATRIX_SUB : thm
  TRANSP_MATRIX_NEG : thm
  SYMMETRIC_MATRIX_NEG : thm
  TRANSP_MAT : thm
  TRANSP_TRANSP : thm
  SYMMETRIC_MATRIX_MAT : thm
  SYMMETRIC_MATRIX_COVARIANCE : thm
  SYMMETRIC_MATRIX_SIMILAR : thm
  TRANSP_EQ : thm
  ROW_TRANSP : thm
  COLUMN_TRANSP : thm
  ROWS_TRANSP : thm
  COLUMNS_TRANSP : thm
  VECTOR_MATRIX_MUL_TRANSP : thm
  MATRIX_VECTOR_MUL_TRANSP : thm
  ROWS_NONEMPTY : thm
  COLUMNS_NONEMPTY : thm
  FINITE_ROWS : thm
  FINITE_COLUMNS : thm
  CARD_ROWS_LE : thm
  CARD_COLUMNS_LE : thm
  MATRIX_EQUAL_ROWS : thm
  MATRIX_EQUAL_COLUMNS : thm
  MATRIX_CMUL_EQ_0 : thm
  MAT_EQ : thm
  MATRIX_VECTOR_LMUL : thm
  MATRIX_VECTOR_MUL_LNEG : thm
  MATRIX_VECTOR_MUL_RNEG : thm
  COLUMN_MATRIX_MUL : thm
  ROW_MATRIX_MUL : thm
  MATRIX_MUL_DOT : thm
  MATRIX_MUL_VSUM : thm
  VECTOR_COMPONENTWISE : thm
  LINEAR_COMPONENTWISE_EXPANSION : thm
  deriving Inhabited

@[nospecialize]
def setupMatProps [HolBase] (D : VectorsDeps) (BBasics : Basics) (BVectorArith : VectorArith)
    (BVSum1 : VSum1) (BBasis : Basis) (BLinear : Linear) (BMatrix : Matrix)
    (BMatArith : MatArith) : ExceptT String IO MatProps := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, INDUCT_TAC, MESON_TAC, .. } := D
  let { ARITH, CARD_IMAGE_LE, CARD_NUMSEG_1, CART_EQ, COND_ID, COND_RAND, DIMINDEX_GE_1,
        EQ_SYM_EQ, EXTENSION, FINITE_IMAGE, FINITE_NUMSEG, .. } := D.core1
  let { IMAGE_EQ_EMPTY, IN_ELIM_THM, IN_NUMSEG, LAMBDA_BETA, LE_REFL, NOT_LT,
        NUMSEG_EMPTY, .. } := D.core2
  let { REAL_ENTIRE, REAL_MUL_AC, REAL_MUL_ASSOC, REAL_MUL_RID, .. } := D.core3
  let { REAL_MUL_RZERO, REAL_NEG_NEG, REAL_OF_NUM_EQ, SIMPLE_IMAGE_GEN,
        SUM_CLAUSES_NUMSEG, SUM_DELTA, .. } := D.core4
  let { SUM_LMUL, SUM_RMUL, SUM_SWAP_NUMSEG, numseg, .. } := D.core5
  let { dot, vec, .. } := BBasics
  let { VECTOR_ADD_COMPONENT, VECTOR_ARITH, VECTOR_MUL_COMPONENT, VECTOR_MUL_LZERO,
        VECTOR_NEG_MINUS1, .. } := BVectorArith
  let { VSUM_COMPONENT, .. } := BVSum1
  let { basis, .. } := BBasis
  let { linear, .. } := BLinear
  let { MATRIX_CMUL_COMPONENT, MATRIX_NEG_COMPONENT, MAT_0_COMPONENT, MAT_COMPONENT,
        TRANSP_COMPONENT, column, columns, mat, matrix_add, matrix_cmul, matrix_mul,
        matrix_neg, matrix_sub, matrix_vector_mul, row, rows, symmetric_matrix, transp,
        vector_matrix_mul, .. } := BMatrix
  let { MATRIX_ARITH, MATRIX_MUL_ASSOC, MATRIX_MUL_RMUL, MATRIX_NEG_MINUS1,
        MATRIX_VECTOR_MUL_LZERO, MATRIX_VECTOR_MUL_RMUL, .. } := BMatArith
  -- @@SCOPE END

  let MATRIX_MUL_RNEG ← prove
   r"!A:real^N^M B:real^P^N. A ** --B = --(A ** B)"
   (REWRITE_TAC [MATRIX_NEG_MINUS1, MATRIX_MUL_RMUL])

  let MATRIX_NEG_NEG ← prove
   r"!A:real^N^M. --(--A) = A"
   (SIMP_TAC [CART_EQ, MATRIX_NEG_COMPONENT, REAL_NEG_NEG])

  let MATRIX_TRANSP_MUL ← prove
   r"!A B. transp(A ** B) = transp(B) ** transp(A)"
   (SIMP_TAC [matrix_mul, transp, CART_EQ, LAMBDA_BETA] THEN
    REWRITE_TAC [REAL_MUL_AC])

  let TRANSP_EQ_0 ← prove
   r"!A:real^N^M. transp A = mat 0 <=> A = mat 0"
   (REWRITE_TAC [MAT_0_COMPONENT, CART_EQ, TRANSP_COMPONENT] THEN MESON_TAC [])

  let SYMMETRIC_MATRIX_MUL ← prove
   r"!A B:real^N^N.
        symmetric_matrix A /\ symmetric_matrix B
        ==> (symmetric_matrix(A ** B) <=> A ** B = B ** A)"
   (SIMP_TAC [symmetric_matrix, MATRIX_TRANSP_MUL] THEN MESON_TAC [])

  let MATRIX_EQ ← prove
   r"!A:real^N^M B. (A = B) = !x:real^N. A ** x = B ** x"
   (REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← GEN (← q r"i:num") (← SPEC (← q r"(basis i):real^N") th)))) THEN
    SIMP_TAC [CART_EQ, matrix_vector_mul, LAMBDA_BETA, basis] THEN
    SIMP_TAC [SUM_DELTA, COND_RAND, REAL_MUL_RZERO] THEN
    REWRITE_TAC [← TAUT (← q r"(if p then b else T) <=> p ==> b")] THEN
    SIMP_TAC [REAL_MUL_RID, IN_NUMSEG])

  let MATRIX_EQ_0 ← prove
   r"!A:real^N^N. A = mat 0 <=> !x. A ** x = vec 0"
   (REWRITE_TAC [MATRIX_EQ, MATRIX_VECTOR_MUL_LZERO])

  let MATRIX_VECTOR_MUL_COMPONENT ← prove
   r"!A:real^N^M x k.
    1 <= k /\ k <= dimindex(:M) ==> ((A ** x)$k = (A$k) dot x)"
   (SIMP_TAC [matrix_vector_mul, LAMBDA_BETA, dot])

  let DOT_LMUL_MATRIX ← prove
   r"!A:real^N^M x:real^M y:real^N. (x ** A) dot y = x dot (A ** y)"
   (SIMP_TAC [dot, matrix_vector_mul, vector_matrix_mul, dot, LAMBDA_BETA] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM SUM_LMUL] THEN
    REWRITE_TAC [← GSYM SUM_RMUL] THEN
    GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC [REAL_MUL_AC])

  let TRANSP_MATRIX_CMUL ← prove
   r"!A:real^M^N c. transp(c %% A) = c %% transp A"
   (SIMP_TAC [CART_EQ, transp, MATRIX_CMUL_COMPONENT, LAMBDA_BETA])

  let SYMMETRIC_MATRIX_CMUL ← prove
   r"!c A:real^N^N.
        symmetric_matrix A ==> symmetric_matrix(c %% A)"
   (SIMP_TAC [symmetric_matrix, TRANSP_MATRIX_CMUL])

  let TRANSP_MATRIX_ADD ← prove
   r"!A B:real^N^M. transp(A + B) = transp A + transp B"
   (SIMP_TAC [CART_EQ, transp, LAMBDA_BETA, matrix_add])

  let SYMMETRIC_MATRIX_ADD ← prove
   r"!A B:real^N^N.
        symmetric_matrix A /\ symmetric_matrix B
        ==> symmetric_matrix(A + B)"
   (SIMP_TAC [symmetric_matrix, TRANSP_MATRIX_ADD])

  let TRANSP_MATRIX_SUB ← prove
   r"!A B:real^N^M. transp(A - B) = transp A - transp B"
   (SIMP_TAC [CART_EQ, transp, LAMBDA_BETA, matrix_sub])

  let SYMMETRIC_MATRIX_SUB ← prove
   r"!A B:real^N^N.
        symmetric_matrix A /\ symmetric_matrix B
        ==> symmetric_matrix(A - B)"
   (SIMP_TAC [symmetric_matrix, TRANSP_MATRIX_SUB])

  let TRANSP_MATRIX_NEG ← prove
   r"!A:real^N^M. transp(--A) = --(transp A)"
   (SIMP_TAC [CART_EQ, transp, LAMBDA_BETA, matrix_neg])

  let SYMMETRIC_MATRIX_NEG ← prove
   r"!A:real^N^N. symmetric_matrix(--A) <=> symmetric_matrix A"
   (REWRITE_TAC [symmetric_matrix, TRANSP_MATRIX_NEG] THEN
    CONV_TAC (fun t => MATRIX_ARITH t))

  let TRANSP_MAT ← prove
   r"!n. transp(mat n) = mat n"
   (SIMP_TAC [transp, mat, LAMBDA_BETA, CART_EQ, EQ_SYM_EQ])

  let TRANSP_TRANSP ← prove
   r"!A:real^N^M. transp(transp A) = A"
   (SIMP_TAC [CART_EQ, transp, LAMBDA_BETA])

  let SYMMETRIC_MATRIX_MAT ← prove
   r"!n. symmetric_matrix(mat n)"
   (REWRITE_TAC [symmetric_matrix, TRANSP_MAT])

  let SYMMETRIC_MATRIX_COVARIANCE ← prove
   r"!A:real^N^M. symmetric_matrix(transp A ** A)"
   (REWRITE_TAC [symmetric_matrix, MATRIX_TRANSP_MUL, TRANSP_TRANSP])

  let SYMMETRIC_MATRIX_SIMILAR ← prove
   r"!A B:real^N^N.
        symmetric_matrix B ==> symmetric_matrix(transp A ** B ** A)"
   (REWRITE_TAC [symmetric_matrix] THEN
    SIMP_TAC [MATRIX_TRANSP_MUL, TRANSP_TRANSP, MATRIX_MUL_ASSOC])

  let TRANSP_EQ ← prove
   r"!A B:real^M^N. transp A = transp B <=> A = B"
   (MESON_TAC [TRANSP_TRANSP])

  let ROW_TRANSP ← prove
   r"!A:real^N^M i.
        1 <= i /\ i <= dimindex(:N) ==> row i (transp A) = column i A"
   (SIMP_TAC [row, column, transp, CART_EQ, LAMBDA_BETA])

  let COLUMN_TRANSP ← prove
   r"!A:real^N^M i.
        1 <= i /\ i <= dimindex(:M) ==> column i (transp A) = row i A"
   (SIMP_TAC [row, column, transp, CART_EQ, LAMBDA_BETA])

  let ROWS_TRANSP ← prove
   r"!A:real^N^M. rows(transp A) = columns A"
   (REWRITE_TAC [rows, columns, EXTENSION, IN_ELIM_THM] THEN
    MESON_TAC [ROW_TRANSP])

  let COLUMNS_TRANSP ← prove
   r"!A:real^N^M. columns(transp A) = rows A"
   (MESON_TAC [TRANSP_TRANSP, ROWS_TRANSP])

  let VECTOR_MATRIX_MUL_TRANSP ← prove
   r"!A:real^M^N x:real^N. x ** A = transp A ** x"
   (REWRITE_TAC [matrix_vector_mul, vector_matrix_mul, transp] THEN
    SIMP_TAC [LAMBDA_BETA, CART_EQ])

  let MATRIX_VECTOR_MUL_TRANSP ← prove
   r"!A:real^M^N x:real^M. A ** x = x ** transp A"
   (REWRITE_TAC [VECTOR_MATRIX_MUL_TRANSP, TRANSP_TRANSP])

  let ROWS_NONEMPTY ← prove
   r"!A:real^N^M. ~(rows A = {})"
   (REWRITE_TAC [rows] THEN ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC [IMAGE_EQ_EMPTY, ← GSYM numseg, NUMSEG_EMPTY] THEN
    REWRITE_TAC [NOT_LT, DIMINDEX_GE_1])

  let COLUMNS_NONEMPTY ← prove
   r"!A:real^N^M. ~(columns A = {})"
   (REWRITE_TAC [columns] THEN ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC [IMAGE_EQ_EMPTY, ← GSYM numseg, NUMSEG_EMPTY] THEN
    REWRITE_TAC [NOT_LT, DIMINDEX_GE_1])

  let FINITE_ROWS ← prove
   r"!A:real^N^M. FINITE(rows A)"
   (REWRITE_TAC [rows] THEN ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
    SIMP_TAC [← GSYM numseg, FINITE_IMAGE, FINITE_NUMSEG])

  let FINITE_COLUMNS ← prove
   r"!A:real^N^M. FINITE(columns A)"
   (REWRITE_TAC [columns] THEN ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
    SIMP_TAC [← GSYM numseg, FINITE_IMAGE, FINITE_NUMSEG])

  let CARD_ROWS_LE ← prove
   r"!A:real^M^N. CARD(rows A) <= dimindex(:N)"
   (GEN_TAC THEN REWRITE_TAC [rows] THEN
    ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC [← GSYM numseg] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM CARD_NUMSEG_1] THEN
    SIMP_TAC [CARD_IMAGE_LE, FINITE_NUMSEG])

  let CARD_COLUMNS_LE ← prove
   r"!A:real^M^N. CARD(columns A) <= dimindex(:M)"
   (GEN_TAC THEN REWRITE_TAC [columns] THEN
    ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC [← GSYM numseg] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM CARD_NUMSEG_1] THEN
    SIMP_TAC [CARD_IMAGE_LE, FINITE_NUMSEG])

  let MATRIX_EQUAL_ROWS ← prove
   r"!A B:real^N^M.
        A = B <=> !i. 1 <= i /\ i <= dimindex(:M) ==> row i A = row i B"
   (SIMP_TAC [row, CART_EQ, LAMBDA_BETA])

  let MATRIX_EQUAL_COLUMNS ← prove
   r"!A B:real^N^M.
        A = B <=> !i. 1 <= i /\ i <= dimindex(:N) ==> column i A = column i B"
   (SIMP_TAC [column, CART_EQ, LAMBDA_BETA] THEN MESON_TAC [])

  let MATRIX_CMUL_EQ_0 ← prove
   r"!A:real^M^N c. c %% A = mat 0 <=> c = &0 \/ A = mat 0"
   (SIMP_TAC [CART_EQ, MATRIX_CMUL_COMPONENT, MAT_COMPONENT, COND_ID] THEN
    REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"c = &0") THEN
    ASM_REWRITE_TAC [REAL_ENTIRE])

  let MAT_EQ ← prove
   r"!m n. mat m = mat n <=> m = n"
   (SIMP_TAC [CART_EQ, MAT_COMPONENT] THEN REPEAT STRIP_TAC THEN
    MESON_TAC [REAL_OF_NUM_EQ, DIMINDEX_GE_1, LE_REFL])

  let MATRIX_VECTOR_LMUL ← prove
   r"!A:real^M^N c x:real^M. (c %% A) ** x = c % (A ** x)"
   (SIMP_TAC [matrix_cmul, CART_EQ, LAMBDA_BETA, matrix_vector_mul,
              VECTOR_MUL_COMPONENT] THEN
    REWRITE_TAC [← GSYM REAL_MUL_ASSOC, SUM_LMUL])

  let MATRIX_VECTOR_MUL_LNEG ← prove
   r"!A:real^M^N x:real^M. --A ** x = --(A ** x)"
   (REWRITE_TAC [MATRIX_NEG_MINUS1, MATRIX_VECTOR_LMUL] THEN
    CONV_TAC (fun t => VECTOR_ARITH t))

  let MATRIX_VECTOR_MUL_RNEG ← prove
   r"!A:real^M^N x:real^M. A ** --x = --(A ** x)"
   (REWRITE_TAC [VECTOR_NEG_MINUS1, MATRIX_VECTOR_MUL_RMUL] THEN
    CONV_TAC (fun t => VECTOR_ARITH t))

  let COLUMN_MATRIX_MUL ← prove
   r"!A:real^N^M B:real^P^N.
      1 <= i /\ i <= dimindex(:P) ==> column i (A ** B) = A ** column i B"
   (SIMP_TAC [column, matrix_mul, matrix_vector_mul, LAMBDA_BETA, CART_EQ])

  let ROW_MATRIX_MUL ← prove
   r"!A:real^N^M B:real^P^N.
      1 <= i /\ i <= dimindex(:M) ==> row i (A ** B) = transp B ** row i A"
   (SIMP_TAC [← GSYM COLUMN_TRANSP] THEN
    SIMP_TAC [MATRIX_TRANSP_MUL, COLUMN_MATRIX_MUL])

  let MATRIX_MUL_DOT ← prove
   r"!A:real^N^M x. A ** x = lambda i. A$i dot x"
   (REWRITE_TAC [matrix_vector_mul, dot] THEN SIMP_TAC [CART_EQ, LAMBDA_BETA])

  let MATRIX_MUL_VSUM ← prove
   r"!A:real^N^M x. A ** x = vsum(1..dimindex(:N)) (\i. x$i % column i A)"
   (SIMP_TAC [matrix_vector_mul, CART_EQ, VSUM_COMPONENT, LAMBDA_BETA,
              VECTOR_MUL_COMPONENT, column, REAL_MUL_AC])

  let VECTOR_COMPONENTWISE ← prove
   r"!x:real^N.
    x = lambda j. sum(1..dimindex(:N))
                     (\i. x$i * (basis i :real^N)$j)"
   (SIMP_TAC [CART_EQ, LAMBDA_BETA, basis] THEN
    ONCE_REWRITE_TAC [← ARITH_RULE (← q r"(m:num = n) <=> (n = m)")] THEN
    SIMP_TAC [COND_RAND, REAL_MUL_RZERO, SUM_DELTA, IN_NUMSEG] THEN
    REWRITE_TAC [REAL_MUL_RID, COND_ID])

  let LINEAR_COMPONENTWISE_EXPANSION ← prove
   r"!f:real^M->real^N.
      linear(f)
      ==> !x j. 1 <= j /\ j <= dimindex(:N)
                ==> (f x $j =
                     sum(1..dimindex(:M)) (\i. x$i * f(basis i)$j))"
   (REWRITE_TAC [linear] THEN REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
     [VECTOR_COMPONENTWISE] THEN
    SPEC_TAC (← q r"dimindex(:M)", ← q r"n:num") THEN
    INDUCT_TAC THEN REWRITE_TAC [SUM_CLAUSES_NUMSEG, ARITH] THENL
     [REWRITE_TAC [← GSYM vec] THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
       [← GSYM VECTOR_MUL_LZERO] THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [VECTOR_MUL_LZERO] THEN
      ASM_SIMP_TAC [vec, LAMBDA_BETA],
      REWRITE_TAC [← ARITH_RULE (← q r"1 <= SUC n")] THEN
      ASSUM_LIST (fun thl => tactic_of do pure (REWRITE_TAC (← thl.mapM GSYM))) THEN
      SIMP_TAC [← GSYM VECTOR_MUL_COMPONENT,
                ← ASSUME (← q r"1 <= j"), ← ASSUME (← q r"j <= dimindex(:N)")] THEN
      ASSUM_LIST (fun thl => tactic_of do pure (REWRITE_TAC (← thl.mapM GSYM))) THEN
      SIMP_TAC [← GSYM VECTOR_ADD_COMPONENT,
                ← ASSUME (← q r"1 <= j"), ← ASSUME (← q r"j <= dimindex(:N)")] THEN
      ASSUM_LIST (fun thl => tactic_of do pure (REWRITE_TAC (← thl.mapM GSYM))) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC [CART_EQ, VECTOR_ADD_COMPONENT, LAMBDA_BETA] THEN
      SIMP_TAC [VECTOR_MUL_COMPONENT]])

  return { MATRIX_MUL_RNEG, MATRIX_NEG_NEG, MATRIX_TRANSP_MUL, TRANSP_EQ_0,
           SYMMETRIC_MATRIX_MUL, MATRIX_EQ, MATRIX_EQ_0, MATRIX_VECTOR_MUL_COMPONENT,
           DOT_LMUL_MATRIX, TRANSP_MATRIX_CMUL, SYMMETRIC_MATRIX_CMUL, TRANSP_MATRIX_ADD,
           SYMMETRIC_MATRIX_ADD, TRANSP_MATRIX_SUB, SYMMETRIC_MATRIX_SUB,
           TRANSP_MATRIX_NEG, SYMMETRIC_MATRIX_NEG, TRANSP_MAT, TRANSP_TRANSP,
           SYMMETRIC_MATRIX_MAT, SYMMETRIC_MATRIX_COVARIANCE, SYMMETRIC_MATRIX_SIMILAR,
           TRANSP_EQ, ROW_TRANSP, COLUMN_TRANSP, ROWS_TRANSP, COLUMNS_TRANSP,
           VECTOR_MATRIX_MUL_TRANSP, MATRIX_VECTOR_MUL_TRANSP, ROWS_NONEMPTY,
           COLUMNS_NONEMPTY, FINITE_ROWS, FINITE_COLUMNS, CARD_ROWS_LE, CARD_COLUMNS_LE,
           MATRIX_EQUAL_ROWS, MATRIX_EQUAL_COLUMNS, MATRIX_CMUL_EQ_0, MAT_EQ,
           MATRIX_VECTOR_LMUL, MATRIX_VECTOR_MUL_LNEG, MATRIX_VECTOR_MUL_RNEG,
           COLUMN_MATRIX_MUL, ROW_MATRIX_MUL, MATRIX_MUL_DOT, MATRIX_MUL_VSUM,
           VECTOR_COMPONENTWISE, LINEAR_COMPONENTWISE_EXPANSION }

/- ------------------------------------------------------------------------- -/
/- Invertible matrices; correspondence between matrices and linear          -/
/- operators.  (vectors.ml 3345-3565)                                        -/
/- ------------------------------------------------------------------------- -/

structure Invertible where
  invertible : thm
  INVERTIBLE_I : thm
  INVERTIBLE_NEG : thm
  INVERTIBLE_CMUL : thm
  INVERTIBLE_MAT : thm
  MATRIX_ENTIRE : thm
  matrix : thm
  MATRIX_COMPONENT : thm
  MATRIX_VECTOR_MUL_LINEAR : thm
  MATRIX_WORKS : thm
  MATRIX_VECTOR_MUL : thm
  MATRIX_OF_MATRIX_VECTOR_MUL : thm
  MATRIX_COMPOSE : thm
  MATRIX_0 : thm
  MATRIX_VECTOR_COLUMN : thm
  MATRIX_MUL_COMPONENT : thm
  ADJOINT_MATRIX : thm
  MATRIX_ADJOINT : thm
  MATRIX_ID : thm
  MATRIX_I : thm
  LINEAR_EQ_MATRIX : thm
  MATRIX_CMUL : thm
  MATRIX_NEG : thm
  MATRIX_ADD : thm
  MATRIX_SELF_ADJOINT : thm
  LINEAR_MATRIX_EXISTS : thm
  LINEAR_1_GEN : thm
  LINEAR_1 : thm
  SYMMETRIC_MATRIX : thm
  DOT_MATRIX_TRANSP_LMUL : thm
  DOT_MATRIX_TRANSP_RMUL : thm
  SYMMETRIC_MATRIX_ORTHOGONAL_EIGENVECTORS : thm
  MATRIX_INJECTIVE_0 : thm
  deriving Inhabited

@[nospecialize]
def setupInvertible [HolBase] (D : VectorsDeps) (BBasics : Basics)
    (BVectorArith : VectorArith) (BDotProps : DotProps) (BVSum1 : VSum1) (BBasis : Basis)
    (BLinear : Linear) (BAdjoint : Adjoint) (BMatrix : Matrix) (BMatArith : MatArith)
    (BMatProps : MatProps) : ExceptT String IO Invertible := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, NUM_REDUCE_CONV, new_definition, .. } := D
  let { ARITH, CART_EQ, COND_ID, DIMINDEX_1, FINITE_INDEX_WORKS, .. } := D.core1
  let { FUN_EQ_THM, IMP_CONJ_ALT, I_DEF, LAMBDA_BETA, LEFT_IMP_EXISTS_THM, .. } := D.core2
  let { REAL_ADD_AC, REAL_ADD_LDISTRIB, REAL_MUL_AC, REAL_MUL_RID, REAL_MUL_RINV, .. } :=
    D.core3
  let { REAL_MUL_SYM, REAL_OF_NUM_EQ, SUM_ADD_NUMSEG, SUM_EQ_NUMSEG, .. } := D.core4
  let { SUM_LMUL, SUM_RMUL, SUM_SWAP_NUMSEG, finite_index, o_THM, .. } := D.core5
  let { FORALL_1, dot, .. } := BBasics
  let { VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, VECTOR_NEG_MINUS1, VEC_COMPONENT, .. } :=
    BVectorArith
  let { DOT_SYM, .. } := BDotProps
  let { VSUM_COMPONENT, .. } := BVSum1
  let { BASIS_COMPONENT, .. } := BBasis
  let { LINEAR_COMPOSE, LINEAR_COMPOSE_ADD, LINEAR_COMPOSE_CMUL, LINEAR_ID,
        LINEAR_INJECTIVE_0, linear, .. } := BLinear
  let { ADJOINT_CLAUSES, ADJOINT_LINEAR, ADJOINT_UNIQUE,
        SELF_ADJOINT_ORTHOGONAL_EIGENVECTORS, .. } := BAdjoint
  let { MAT_COMPONENT, matrix_mul, matrix_vector_mul, symmetric_matrix, transp,
        vector_matrix_mul, .. } := BMatrix
  let { MATRIX_CMUL_ASSOC, MATRIX_CMUL_LID, MATRIX_CMUL_LZERO, MATRIX_MUL_ASSOC,
        MATRIX_MUL_LID, MATRIX_MUL_LMUL, MATRIX_MUL_LNEG, MATRIX_MUL_LZERO, MATRIX_MUL_RID,
        MATRIX_MUL_RMUL, MATRIX_MUL_RZERO, MATRIX_NEG_MINUS1,
        MATRIX_VECTOR_MUL_ADD_RDISTRIB, MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID,
        MAT_CMUL, .. } := BMatArith
  let { LINEAR_COMPONENTWISE_EXPANSION, MATRIX_EQ, MATRIX_MUL_RNEG, MATRIX_NEG_NEG,
        MATRIX_VECTOR_LMUL, MAT_EQ, .. } := BMatProps
  -- @@SCOPE END

  let invertible ← new_definition
   r"invertible(A:real^N^M) <=>
        ?A':real^M^N. (A ** A' = mat 1) /\ (A' ** A = mat 1)"

  let INVERTIBLE_I ← prove
   r"invertible(mat 1:real^N^N)"
   (REWRITE_TAC [invertible] THEN MESON_TAC [MATRIX_MUL_LID, MATRIX_MUL_RID])

  let INVERTIBLE_NEG ← prove
   r"!A:real^N^M. invertible(--A) <=> invertible A"
   (REWRITE_TAC [invertible] THEN
    MESON_TAC [MATRIX_MUL_LNEG, MATRIX_MUL_RNEG, MATRIX_NEG_NEG])

  let INVERTIBLE_CMUL ← prove
   r"!A:real^N^M c. invertible(c %% A) <=> ~(c = &0) /\ invertible(A)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"c = &0") THEN ASM_REWRITE_TAC [] THENL
     [REWRITE_TAC [invertible, MATRIX_MUL_LZERO, MATRIX_CMUL_LZERO, MAT_EQ] THEN
      CONV_TAC NUM_REDUCE_CONV,
      ALL_TAC] THEN
    REWRITE_TAC [invertible, MATRIX_MUL_LMUL, MATRIX_MUL_RMUL] THEN EQ_TAC THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"B:real^M^N") STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC (← q r"c %% B:real^M^N"),
      EXISTS_TAC (← q r"inv c %% B:real^M^N")] THEN
    ASM_REWRITE_TAC [MATRIX_MUL_LMUL, MATRIX_MUL_RMUL] THEN
    ASM_SIMP_TAC [MATRIX_CMUL_ASSOC, REAL_MUL_RINV, MATRIX_CMUL_LID])

  let INVERTIBLE_MAT ← prove
   r"!a. invertible(mat a:real^N^N) <=> ~(a = 0)"
   (ONCE_REWRITE_TAC [MAT_CMUL] THEN
    REWRITE_TAC [INVERTIBLE_CMUL, INVERTIBLE_I, REAL_OF_NUM_EQ])

  let MATRIX_ENTIRE ← prove
   r"(!A:real^N^M B:real^P^N. invertible A ==> (A ** B = mat 0 <=> B = mat 0)) /\
   (!A:real^N^M B:real^P^N. invertible B ==> (A ** B = mat 0 <=> A = mat 0))"
   (REWRITE_TAC [invertible] THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"A':real^M^N") STRIP_ASSUME_TAC),
      DISCH_THEN (X_CHOOSE_THEN (← q r"B':real^N^P") STRIP_ASSUME_TAC)] THEN
    EQ_TAC THEN SIMP_TAC [MATRIX_MUL_LZERO, MATRIX_MUL_RZERO] THENL
     [DISCH_THEN (MP_TAC o AP_TERM (← q r"(**) A':real^P^M->real^P^N")) THEN
      ASM_REWRITE_TAC [MATRIX_MUL_ASSOC, MATRIX_MUL_LID, MATRIX_MUL_RZERO],
      DISCH_THEN (MP_TAC o AP_TERM (← q r"\C:real^P^M. C ** (B':real^N^P)")) THEN
      ASM_REWRITE_TAC [← GSYM MATRIX_MUL_ASSOC, MATRIX_MUL_RID,
                       MATRIX_MUL_LZERO]])

  let matrix ← new_definition
   r"(matrix:(real^M->real^N)->real^M^N) f = lambda i j. f(basis j)$i"

  let MATRIX_COMPONENT ← prove
   r"!f:real^M->real^N i j.
        1 <= j /\ j <= dimindex(:M)
        ==> (matrix f)$i$j = f (basis j)$i"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"?k. 1 <= k /\ k <= dimindex(:N) /\
        (!A:real^M^N. A$i = A$k) /\ (!z:real^N. z$i = z$k)")
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [finite_index] THEN MESON_TAC [FINITE_INDEX_WORKS],
      ASM_SIMP_TAC [matrix, LAMBDA_BETA]])

  let MATRIX_VECTOR_MUL_LINEAR ← prove
   r"!A:real^N^M. linear(\x. A ** x)"
   (REWRITE_TAC [linear, matrix_vector_mul] THEN
    SIMP_TAC [CART_EQ, LAMBDA_BETA, VECTOR_ADD_COMPONENT,
      VECTOR_MUL_COMPONENT] THEN
    REWRITE_TAC [← GSYM SUM_ADD_NUMSEG, ← GSYM SUM_LMUL, REAL_ADD_LDISTRIB] THEN
    REWRITE_TAC [REAL_ADD_AC, REAL_MUL_AC])

  let MATRIX_WORKS ← prove
   r"!f:real^M->real^N. linear f ==> !x. matrix f ** x = f(x)"
   (REWRITE_TAC [matrix, matrix_vector_mul] THEN
    SIMP_TAC [CART_EQ, LAMBDA_BETA] THEN GEN_TAC THEN DISCH_TAC THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    ASM_SIMP_TAC [← GSYM LINEAR_COMPONENTWISE_EXPANSION])

  let MATRIX_VECTOR_MUL ← prove
   r"!f:real^M->real^N. linear f ==> f = \x. matrix f ** x"
   (SIMP_TAC [FUN_EQ_THM, MATRIX_WORKS])

  let MATRIX_OF_MATRIX_VECTOR_MUL ← prove
   r"!A:real^N^M. matrix(\x. A ** x) = A"
   (SIMP_TAC [MATRIX_EQ, MATRIX_VECTOR_MUL_LINEAR, MATRIX_WORKS])

  let MATRIX_COMPOSE ← prove
   r"!f g. linear f /\ linear g ==> (matrix(g o f) = matrix g ** matrix f)"
   (SIMP_TAC [MATRIX_EQ, MATRIX_WORKS, LINEAR_COMPOSE,
              ← GSYM MATRIX_VECTOR_MUL_ASSOC, o_THM])

  let MATRIX_0 ← prove
   r"matrix(\x. vec 0):real^M^N = mat 0"
   (SIMP_TAC [matrix, CART_EQ, MAT_COMPONENT, LAMBDA_BETA, COND_ID,
              VEC_COMPONENT])

  let MATRIX_VECTOR_COLUMN ← prove
   r"!A:real^N^M x.
        A ** x = vsum(1..dimindex(:N)) (\i. x$i % (transp A)$i)"
   (REWRITE_TAC [matrix_vector_mul, transp] THEN
    SIMP_TAC [CART_EQ, LAMBDA_BETA, VSUM_COMPONENT, VECTOR_MUL_COMPONENT] THEN
    REWRITE_TAC [REAL_MUL_AC])

  let MATRIX_MUL_COMPONENT ← prove
   r"!i. 1 <= i /\ i <= dimindex(:P)
       ==> ((A:real^N^P) ** (B:real^M^N))$i = transp B ** A$i"
   (SIMP_TAC [matrix_mul, LAMBDA_BETA, matrix_vector_mul, vector_matrix_mul,
         transp, CART_EQ] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REWRITE_TAC [REAL_MUL_AC])

  let ADJOINT_MATRIX ← prove
   r"!A:real^N^M. adjoint(\x. A ** x) = (\x. transp A ** x)"
   (GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC ADJOINT_UNIQUE THEN
    REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR] THEN REPEAT GEN_TAC THEN
    SIMP_TAC [transp, dot, LAMBDA_BETA, matrix_vector_mul,
              ← GSYM SUM_LMUL, ← GSYM SUM_RMUL] THEN
    GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC [REAL_MUL_AC])

  let MATRIX_ADJOINT ← prove
   r"!f. linear f ==> matrix(adjoint f) = transp(matrix f)"
   (GEN_TAC THEN DISCH_THEN
     (fun th => tactic_of do
        pure (GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV)
                [← MATCH_MP MATRIX_VECTOR_MUL th])) THEN
    REWRITE_TAC [ADJOINT_MATRIX, MATRIX_OF_MATRIX_VECTOR_MUL])

  let MATRIX_ID ← prove
   r"matrix(\x. x) = mat 1"
   (SIMP_TAC [MATRIX_EQ, LINEAR_ID, MATRIX_WORKS, MATRIX_VECTOR_MUL_LID])

  let MATRIX_I ← prove
   r"matrix I = mat 1"
   (REWRITE_TAC [I_DEF, MATRIX_ID])

  let LINEAR_EQ_MATRIX ← prove
   r"!f g. linear f /\ linear g /\ matrix f = matrix g ==> f = g"
   (REPEAT STRIP_TAC THEN
    REPEAT (FIRST_X_ASSUM (SUBST1_TAC o MATCH_MP MATRIX_VECTOR_MUL)) THEN
    ASM_REWRITE_TAC [])

  let MATRIX_CMUL ← prove
   r"!f:real^M->real^N c.
        linear f ==> matrix(\x. c % f x) = c %% matrix f"
   (SIMP_TAC [MATRIX_EQ, MATRIX_WORKS, LINEAR_COMPOSE_CMUL, MATRIX_VECTOR_LMUL])

  let MATRIX_NEG ← prove
   r"!f:real^M->real^N.
        linear f ==> matrix(\x. --(f x)) = --(matrix f)"
   (SIMP_TAC [← GSYM MATRIX_NEG_MINUS1, VECTOR_NEG_MINUS1, MATRIX_CMUL])

  let MATRIX_ADD ← prove
   r"!f g:real^M->real^N.
        linear f /\ linear g ==> matrix(\x. f x + g x) = matrix f + matrix g"
   (REWRITE_TAC [MATRIX_EQ, MATRIX_VECTOR_MUL_ADD_RDISTRIB] THEN
    SIMP_TAC [MATRIX_WORKS, LINEAR_COMPOSE_ADD])

  let MATRIX_SELF_ADJOINT ← prove
   r"!f. linear f ==> (adjoint f = f <=> symmetric_matrix(matrix f))"
   (SIMP_TAC [symmetric_matrix, ← GSYM MATRIX_ADJOINT] THEN
    MESON_TAC [LINEAR_EQ_MATRIX, ADJOINT_LINEAR])

  let LINEAR_MATRIX_EXISTS ← prove
   r"!f:real^M->real^N. linear f <=> ?A:real^M^N. f = \x. A ** x"
   (GEN_TAC THEN EQ_TAC THEN
    SIMP_TAC [MATRIX_VECTOR_MUL_LINEAR, LEFT_IMP_EXISTS_THM] THEN
    DISCH_TAC THEN EXISTS_TAC (← q r"matrix(f:real^M->real^N)") THEN
    ASM_SIMP_TAC [← GSYM MATRIX_VECTOR_MUL])

  let LINEAR_1_GEN ← prove
   r"!f:real^N->real^N.
        dimindex(:N) = 1 ==> (linear f <=> ?c. f = \x. c % x)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC [LINEAR_COMPOSE_CMUL, LINEAR_ID] THEN
    ASM_SIMP_TAC [FUN_EQ_THM, CART_EQ, FORALL_1] THEN
    EXISTS_TAC (← q r"(f:real^N->real^N)(basis 1)$1") THEN
    REWRITE_TAC [VECTOR_MUL_COMPONENT] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    REWRITE_TAC [← GSYM VECTOR_MUL_COMPONENT] THEN
    X_GEN_TAC (← q r"x:real^N") THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [linear]) THEN
    DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← GSYM th])) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC [CART_EQ, FORALL_1, VECTOR_MUL_COMPONENT, BASIS_COMPONENT,
                  ARITH, REAL_MUL_RID])

  let LINEAR_1 ← prove
   r"!f:real^1->real^1. linear f <=> ?c. f = \x. c % x"
   (SIMP_TAC [LINEAR_1_GEN, DIMINDEX_1])

  let SYMMETRIC_MATRIX ← prove
   r"!A:real^N^N. symmetric_matrix A <=> adjoint(\x. A ** x) = \x. A ** x"
   (SIMP_TAC [MATRIX_SELF_ADJOINT, MATRIX_VECTOR_MUL_LINEAR] THEN
    REWRITE_TAC [MATRIX_OF_MATRIX_VECTOR_MUL])

  let DOT_MATRIX_TRANSP_LMUL ← prove
   r"!A x y:real^N. (transp A ** x) dot y = x dot (A ** y)"
   (REWRITE_TAC [← REWRITE_RULE [FUN_EQ_THM] (← GSYM ADJOINT_MATRIX)] THEN
    SIMP_TAC [ADJOINT_CLAUSES, MATRIX_VECTOR_MUL_LINEAR])

  let DOT_MATRIX_TRANSP_RMUL ← prove
   r"!A x y:real^N. x dot (transp A ** y) = (A ** x) dot y"
   (ONCE_REWRITE_TAC [DOT_SYM] THEN REWRITE_TAC [DOT_MATRIX_TRANSP_LMUL])

  let SYMMETRIC_MATRIX_ORTHOGONAL_EIGENVECTORS ← prove
   r"!A:real^N^N v w a b.
        symmetric_matrix A /\ A ** v = a % v /\ A ** w = b % w /\ ~(a = b)
        ==> orthogonal v w"
   (REPEAT GEN_TAC THEN REWRITE_TAC [SYMMETRIC_MATRIX] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MATCH_MP_TAC (← MATCH_MP (← ONCE_REWRITE_RULE [IMP_CONJ_ALT]
        SELF_ADJOINT_ORTHOGONAL_EIGENVECTORS) th))) THEN
    REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR])

  let MATRIX_INJECTIVE_0 ← prove
   r"!m:real^M^N.
        (!x y:real^M. m ** x = m ** y ==> x = y) <=>
        (!x:real^M. m ** x = vec 0 ==> x = vec 0)"
   (GEN_TAC THEN MATCH_MP_TAC LINEAR_INJECTIVE_0 THEN
    REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR])

  return { invertible, INVERTIBLE_I, INVERTIBLE_NEG, INVERTIBLE_CMUL, INVERTIBLE_MAT,
           MATRIX_ENTIRE, matrix, MATRIX_COMPONENT, MATRIX_VECTOR_MUL_LINEAR, MATRIX_WORKS,
           MATRIX_VECTOR_MUL, MATRIX_OF_MATRIX_VECTOR_MUL, MATRIX_COMPOSE, MATRIX_0,
           MATRIX_VECTOR_COLUMN, MATRIX_MUL_COMPONENT, ADJOINT_MATRIX, MATRIX_ADJOINT,
           MATRIX_ID, MATRIX_I, LINEAR_EQ_MATRIX, MATRIX_CMUL, MATRIX_NEG, MATRIX_ADD,
           MATRIX_SELF_ADJOINT, LINEAR_MATRIX_EXISTS, LINEAR_1_GEN, LINEAR_1,
           SYMMETRIC_MATRIX, DOT_MATRIX_TRANSP_LMUL, DOT_MATRIX_TRANSP_RMUL,
           SYMMETRIC_MATRIX_ORTHOGONAL_EIGENVECTORS, MATRIX_INJECTIVE_0 }

/- ------------------------------------------------------------------------- -/
/- Operator norm.  (vectors.ml 3569-3815)                                    -/
/- ------------------------------------------------------------------------- -/

structure ONorm where
  onorm : thm
  NORM_BOUND_GENERALIZE : thm
  ONORM_DOT : thm
  ONORM : thm
  ONORM_LE_EQ : thm
  ONORM_POS_LE : thm
  ONORM_EQ_0 : thm
  ONORM_CONST : thm
  ONORM_POS_LT : thm
  ONORM_COMPOSE : thm
  ONORM_CMUL : thm
  ONORM_NEG : thm
  ONORM_TRIANGLE : thm
  ONORM_TRIANGLE_LE : thm
  ONORM_TRIANGLE_LT : thm
  ONORM_ID : thm
  ONORM_I : thm
  ONORM_INVERSE_FUNCTION_BOUND : thm
  ONORM_ADJOINT : thm
  ONORM_COMPOSE_ADJOINT_LEFT : thm
  ONORM_COMPOSE_ADJOINT_RIGHT : thm
  ONORM_TRANSP : thm
  ONORM_COVARIANCE : thm
  ONORM_COVARIANCE_ALT : thm
  ONORM_LE_EQ_2 : thm
  ONORM_LE_EQ_2_ABS : thm
  deriving Inhabited

@[nospecialize]
def setupONorm [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BDotProps : DotProps) (BNorm1 : Norm1) (BBasis : Basis) (BLinear : Linear)
    (BAdjoint : Adjoint) (BMatArith : MatArith) (BInvertible : Invertible) :
    ExceptT String IO ONorm := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD, SET_RULE,
        SET_TAC, new_definition, .. } := D
  let { AND_FORALL_THM, DIMINDEX_GE_1, EQ_TRANS, ETA_AX, EXISTS_REFL, FORALL_IN_GSPEC, .. } :=
    D.core1
  let { IMP_CONJ_ALT, IMP_IMP, IN_ELIM_THM, I_DEF, LEFT_FORALL_IMP_THM,
        LEFT_IMP_EXISTS_THM, LE_REFL, MEMBER_NOT_EMPTY, MONO_FORALL, .. } := D.core2
  let { REAL_ABS_INV, REAL_ABS_MUL, REAL_ABS_NUM, REAL_ABS_NZ, REAL_ABS_POS,
        REAL_ADD_RDISTRIB, REAL_LET_TRANS, REAL_LE_ADD2, REAL_LE_ANTISYM,
        REAL_LE_LDIV_EQ, REAL_LE_LMUL, REAL_LE_LMUL_EQ, REAL_LE_RDIV_EQ, REAL_LE_REFL,
        REAL_LE_RMUL, REAL_LE_RSQRT, REAL_LE_TRANS, REAL_MUL_ASSOC, REAL_MUL_LID,
        REAL_MUL_LINV, REAL_MUL_LZERO, REAL_MUL_RID, .. } := D.core3
  let { REAL_MUL_RZERO, REAL_MUL_SYM, REAL_POS, REAL_POW_2, REAL_RSQRT_LE,
        REAL_SUP_UNIQUE, RIGHT_EXISTS_AND_THM, SQRT_MUL, .. } := D.core4
  let { SUP, SUP_EQ, SUP_SING, SWAP_FORALL_THM, o_DEF, o_THM, real_div, .. } := D.core5
  let { VECTOR_MUL_ASSOC, VECTOR_MUL_LID, .. } := BVectorArith
  let { DOT_RMUL, DOT_RNEG, DOT_RZERO, DOT_SYM, .. } := BDotProps
  let { NORM_0, NORM_CAUCHY_SCHWARZ, NORM_CAUCHY_SCHWARZ_ABS, NORM_EQ_0, NORM_LE_0,
        NORM_MUL, NORM_NEG, NORM_POS_LE, NORM_POS_LT, NORM_POW_2, NORM_TRIANGLE,
        REAL_ABS_NORM, vector_norm, .. } := BNorm1
  let { NORM_BASIS, VECTOR_CHOOSE_SIZE, .. } := BBasis
  let { LINEAR_0, LINEAR_BOUNDED, LINEAR_CMUL, LINEAR_COMPOSE, LINEAR_COMPOSE_ADD,
        LINEAR_COMPOSE_CMUL, .. } := BLinear
  let { ADJOINT_ADJOINT, ADJOINT_LINEAR, ADJOINT_WORKS, .. } := BAdjoint
  let { MATRIX_VECTOR_MUL_ASSOC, .. } := BMatArith
  let { ADJOINT_MATRIX, MATRIX_VECTOR_MUL_LINEAR, .. } := BInvertible
  -- @@SCOPE END

  let onorm ← new_definition
   r"onorm (f:real^M->real^N) = sup { norm(f x) | norm(x) = &1 }"

  let NORM_BOUND_GENERALIZE ← prove
   r"!f:real^M->real^N b.
        linear f
        ==> ((!x. norm(x) = &1 ==> norm(f x) <= b) <=>
             (!x. norm(f x) <= b * norm(x)))"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [ALL_TAC, ASM_MESON_TAC [REAL_MUL_RID]] THEN
    X_GEN_TAC (← q r"x:real^M") THEN ASM_CASES_TAC (← q r"x:real^M = vec 0") THENL
     [ASM_REWRITE_TAC [NORM_0, REAL_MUL_RZERO] THEN
      ASM_MESON_TAC [LINEAR_0, NORM_0, REAL_LE_REFL],
      ALL_TAC] THEN
    ASM_SIMP_TAC [← GSYM REAL_LE_LDIV_EQ, NORM_POS_LT, real_div] THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"abs(a * b) <= c ==> b * a <= c")) THEN
    REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_NORM, ← GSYM NORM_MUL] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (REWRITE_TAC [← GSYM (← MATCH_MP LINEAR_CMUL th)])) THEN
    ASM_SIMP_TAC [NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM, REAL_MUL_LINV,
                  NORM_EQ_0])

  let ONORM_DOT ← prove
   r"!f:real^M->real^N. onorm f = sup {f x dot y | norm x = &1 /\ norm y = &1}"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [onorm] THEN MATCH_MP_TAC SUP_EQ THEN
    X_GEN_TAC (← q r"b:real") THEN REWRITE_TAC [FORALL_IN_GSPEC] THEN
    EQ_TAC THEN DISCH_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q r"x:real^M", ← q r"y:real^N"] THEN STRIP_TAC THEN
      TRANS_TAC REAL_LE_TRANS (← q r"norm((f:real^M->real^N) x) * norm(y:real^N)") THEN
      REWRITE_TAC [NORM_CAUCHY_SCHWARZ] THEN ASM_SIMP_TAC [REAL_MUL_RID],
      FIRST_ASSUM (fun th => tactic_of do
        pure (MP_TAC (← ISPECL [← q r"basis 1:real^M", ← q r"--basis 1:real^N"] th) THEN
              MP_TAC (← ISPECL [← q r"basis 1:real^M", ← q r"basis 1:real^N"] th))) THEN
      SIMP_TAC [NORM_BASIS, DIMINDEX_GE_1, LE_REFL, NORM_NEG] THEN
      REWRITE_TAC [DOT_RNEG, IMP_IMP] THEN DISCH_THEN (ASSUME_TAC o MATCH_MP
       (← REAL_ARITH (← q r"x <= b /\ --x <= b ==> &0 <= b"))) THEN
      X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN
      ASM_CASES_TAC (← q r"(f:real^M->real^N) x = vec 0") THEN
      ASM_REWRITE_TAC [NORM_0] THEN
      FIRST_X_ASSUM (MP_TAC o SPECL
       [← q r"x:real^M", ← q r"inv(norm((f:real^M->real^N) x)) % f x"]) THEN
      ASM_REWRITE_TAC [DOT_RMUL, NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
      ASM_SIMP_TAC [REAL_MUL_LINV, NORM_EQ_0, ← GSYM NORM_POW_2,
                    ← REAL_FIELD (← q r"~(x = &0) ==> inv x * x pow 2 = x")]])

  let ONORM ← prove
   r"!f:real^M->real^N.
        linear f
        ==> (!x. norm(f x) <= onorm f * norm(x)) /\
            (!b. (!x. norm(f x) <= b * norm(x)) ==> onorm f <= b)"
   (GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (← SPEC (← q r"{ norm((f:real^M->real^N) x) | norm(x) = &1 }") SUP) THEN
    SIMP_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    REWRITE_TAC [LEFT_FORALL_IMP_THM, RIGHT_EXISTS_AND_THM, EXISTS_REFL] THEN
    ASM_SIMP_TAC [NORM_BOUND_GENERALIZE, ← GSYM onorm, ← GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN
    ASM_MESON_TAC [VECTOR_CHOOSE_SIZE, LINEAR_BOUNDED, REAL_POS])

  let ONORM_LE_EQ ← prove
   r"!f:real^M->real^N b.
        linear f ==> (onorm f <= b <=> !x. norm(f x) <= b * norm x)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
     [TRANS_TAC REAL_LE_TRANS (← q r"onorm(f:real^M->real^N) * norm(x:real^M)") THEN
      ASM_SIMP_TAC [ONORM, REAL_LE_RMUL, NORM_POS_LE],
      ASM_MESON_TAC [ONORM]])

  let ONORM_POS_LE ← prove
   r"!f. linear f ==> &0 <= onorm f"
   (MESON_TAC [ONORM, VECTOR_CHOOSE_SIZE, REAL_POS, REAL_MUL_RID, NORM_POS_LE,
               REAL_LE_TRANS])

  let ONORM_EQ_0 ← prove
   r"!f:real^M->real^N. linear f ==> ((onorm f = &0) <=> (!x. f x = vec 0))"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
    MP_TAC (← SPEC (← q r"f:real^M->real^N") ONORM) THEN
    ASM_SIMP_TAC [← GSYM REAL_LE_ANTISYM, ONORM_POS_LE, NORM_0, REAL_MUL_LZERO,
                  NORM_LE_0, REAL_LE_REFL])

  let ONORM_CONST ← prove
   r"!y:real^N. onorm(\x:real^M. y) = norm(y)"
   (GEN_TAC THEN REWRITE_TAC [onorm] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"sup {norm(y:real^N)}") THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC (← SET_RULE (← q
       r"(?x. P x) ==> {f y | x | P x} = {f y}")) THEN
      EXISTS_TAC (← q r"basis 1 :real^M") THEN
      SIMP_TAC [NORM_BASIS, DIMINDEX_GE_1, LE_REFL],
      MATCH_MP_TAC REAL_SUP_UNIQUE THEN SET_TAC [REAL_LE_REFL]])

  let ONORM_POS_LT ← prove
   r"!f. linear f ==> (&0 < onorm f <=> ~(!x. f x = vec 0))"
   (SIMP_TAC [← GSYM ONORM_EQ_0, ONORM_POS_LE,
              ← REAL_ARITH (← q r"(&0 < x <=> ~(x = &0)) <=> &0 <= x")])

  let ONORM_COMPOSE ← prove
   r"!f g. linear f /\ linear g ==> onorm(f o g) <= onorm f * onorm g"
   (MESON_TAC [ONORM, LINEAR_COMPOSE, o_THM, REAL_MUL_ASSOC, REAL_LE_TRANS, ONORM,
               REAL_LE_LMUL, ONORM_POS_LE])

  let ONORM_CMUL ← prove
   r"!f:real^M->real^N c. linear f ==> onorm(\x. c % f x) = abs c * onorm f"
   (SUBGOAL_THEN
     (← q r"!f:real^M->real^N c. linear f ==> onorm(\x. c % f x) <= abs c * onorm f")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC [ONORM_LE_EQ, LINEAR_COMPOSE_CMUL] THEN
      GEN_TAC THEN REWRITE_TAC [NORM_MUL, ← GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC [REAL_ABS_POS, ONORM],
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC [← GSYM REAL_LE_ANTISYM] THEN
      ASM_CASES_TAC (← q r"c = &0") THEN
      ASM_SIMP_TAC [REAL_ABS_NUM, REAL_MUL_LZERO, ONORM_POS_LE,
                    LINEAR_COMPOSE_CMUL] THEN
      FIRST_X_ASSUM (MP_TAC o SPECL
       [← q r"\x. c % (f:real^M->real^N) x", ← q r"inv c:real"]) THEN
      ASM_SIMP_TAC [LINEAR_COMPOSE_CMUL, VECTOR_MUL_ASSOC, REAL_MUL_LINV] THEN
      REWRITE_TAC [REAL_ABS_INV, VECTOR_MUL_LID, ETA_AX] THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      ASM_SIMP_TAC [← GSYM real_div, REAL_LE_RDIV_EQ, ← GSYM REAL_ABS_NZ]])

  let ONORM_NEG ← prove
   r"!f:real^M->real^N. onorm(\x. --f x) = onorm f"
   (REWRITE_TAC [onorm, NORM_NEG])

  let ONORM_TRIANGLE ← prove
   r"!f:real^M->real^N g.
        linear f /\ linear g ==> onorm(\x. f x + g x) <= onorm f + onorm g"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (MATCH_MP_TAC (← CONJUNCT2 (← MATCH_MP ONORM
        (← MATCH_MP LINEAR_COMPOSE_ADD th))))) THEN
    REWRITE_TAC [REAL_ADD_RDISTRIB] THEN
    ASM_MESON_TAC [REAL_LE_ADD2, REAL_LE_TRANS, NORM_TRIANGLE, ONORM])

  let ONORM_TRIANGLE_LE ← prove
   r"!f g. linear f /\ linear g /\ onorm(f) + onorm(g) <= e
         ==> onorm(\x. f x + g x) <= e"
   (MESON_TAC [REAL_LE_TRANS, ONORM_TRIANGLE])

  let ONORM_TRIANGLE_LT ← prove
   r"!f g. linear f /\ linear g /\ onorm(f) + onorm(g) < e
         ==> onorm(\x. f x + g x) < e"
   (MESON_TAC [REAL_LET_TRANS, ONORM_TRIANGLE])

  let ONORM_ID ← prove
   r"onorm(\x:real^N. x) = &1"
   (REWRITE_TAC [onorm] THEN
    SUBGOAL_THEN (← q r"{norm(x:real^N) | norm x = &1} = {&1}")
     (fun th => REWRITE_TAC [th, SUP_SING]) THEN
    SUBGOAL_THEN (← q r"norm(basis 1:real^N) = &1") MP_TAC THENL
     [SIMP_TAC [NORM_BASIS, DIMINDEX_GE_1, LE_REFL], SET_TAC []])

  let ONORM_I ← prove
   r"onorm(I:real^N->real^N) = &1"
   (REWRITE_TAC [I_DEF, ONORM_ID])

  let ONORM_INVERSE_FUNCTION_BOUND ← prove
   r"!f g:real^M->real^N.
        linear f /\ linear g /\ f o g = I ==> &1 <= onorm f * onorm g"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o AP_TERM (← q r"onorm:(real^M->real^M)->real")) THEN
    REWRITE_TAC [ONORM_I] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC ONORM_COMPOSE THEN ASM_REWRITE_TAC [])

  let ONORM_ADJOINT ← prove
   r"!f:real^N->real^N. linear f ==> onorm(adjoint f) = onorm f"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [ONORM_DOT] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [DOT_SYM] THEN
    ASM_SIMP_TAC [← GSYM ADJOINT_WORKS] THEN AP_TERM_TAC THEN SET_TAC [])

  let ONORM_COMPOSE_ADJOINT_LEFT ← prove
   r"!f:real^N->real^N. linear f ==> onorm(adjoint f o f) = onorm f pow 2"
   (REWRITE_TAC [← GSYM REAL_LE_ANTISYM] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC [REAL_POW_2, ONORM_COMPOSE, ADJOINT_LINEAR, ONORM_ADJOINT],
      MATCH_MP_TAC REAL_RSQRT_LE THEN
      ASM_SIMP_TAC [LINEAR_COMPOSE, ADJOINT_LINEAR, ONORM_POS_LE] THEN
      ASM_SIMP_TAC [ONORM_LE_EQ] THEN X_GEN_TAC (← q r"x:real^N") THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [vector_norm] THEN
      REWRITE_TAC [← GSYM SQRT_MUL] THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
      REWRITE_TAC [NORM_POW_2] THEN
      FIRST_ASSUM (fun th => tactic_of do
        pure (REWRITE_TAC [← MATCH_MP ADJOINT_WORKS th])) THEN
      W (MP_TAC o PART_MATCH lhand NORM_CAUCHY_SCHWARZ o lhand o snd) THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      SIMP_TAC [← GSYM NORM_POW_2, ← REAL_ARITH (← q r"(x:real) * y pow 2 = y * x * y")] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [NORM_POS_LE] THEN
      MP_TAC (← ISPEC (← q r"adjoint f o (f:real^N->real^N)") ONORM) THEN
      ASM_SIMP_TAC [LINEAR_COMPOSE, ADJOINT_LINEAR, o_DEF]])

  let ONORM_COMPOSE_ADJOINT_RIGHT ← prove
   r"!f:real^N->real^N. linear f ==> onorm(f o adjoint f) = onorm f pow 2"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"adjoint f:real^N->real^N") ONORM_COMPOSE_ADJOINT_LEFT) THEN
    ASM_SIMP_TAC [ADJOINT_LINEAR, ADJOINT_ADJOINT, ONORM_ADJOINT])

  let ONORM_TRANSP ← prove
   r"!A:real^N^N. onorm(\x. transp A ** x) = onorm(\x. A ** x)"
   (REWRITE_TAC [← GSYM ADJOINT_MATRIX] THEN
    SIMP_TAC [ONORM_ADJOINT, MATRIX_VECTOR_MUL_LINEAR])

  let ONORM_COVARIANCE ← prove
   r"!A:real^N^N.
        onorm(\x. (transp A ** A) ** x) = onorm(\x. A ** x) pow 2"
   (GEN_TAC THEN
    MP_TAC (← ISPEC (← q r"\x:real^N. (A:real^N^N) ** x") ONORM_COMPOSE_ADJOINT_LEFT) THEN
    REWRITE_TAC [ADJOINT_MATRIX, MATRIX_VECTOR_MUL_LINEAR, o_DEF] THEN
    REWRITE_TAC [MATRIX_VECTOR_MUL_ASSOC])

  let ONORM_COVARIANCE_ALT ← prove
   r"!A:real^N^N.
        onorm(\x. (A ** transp A) ** x) = onorm(\x. A ** x) pow 2"
   (GEN_TAC THEN
    MP_TAC (← ISPEC (← q r"\x:real^N. (A:real^N^N) ** x") ONORM_COMPOSE_ADJOINT_RIGHT) THEN
    REWRITE_TAC [ADJOINT_MATRIX, MATRIX_VECTOR_MUL_LINEAR, o_DEF] THEN
    REWRITE_TAC [MATRIX_VECTOR_MUL_ASSOC])

  let (ONORM_LE_EQ_2, ONORM_LE_EQ_2_ABS) ← CONJ_PAIR (← prove
   r"(!f:real^M->real^N b.
        linear f
        ==> (onorm f <= b <=> !x y. x dot (f y) <= b * norm x * norm y)) /\
   (!f:real^M->real^N b.
        linear f
        ==> (onorm f <= b <=> !x y. abs(x dot (f y)) <= b * norm x * norm y))"
   (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"linear(f:real^M->real^N)") THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← TAUT (← q
     r"(r ==> q) /\ (p ==> r) /\ (q ==> p) ==> (p <=> q) /\ (p <=> r)")) THEN
    CONJ_TAC THENL
     [REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN REAL_ARITH_TAC,
      ASM_SIMP_TAC [ONORM_LE_EQ]] THEN
    CONJ_TAC THEN DISCH_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q r"x:real^N", ← q r"y:real^M"] THEN
      TRANS_TAC REAL_LE_TRANS (← q r"norm(x:real^N) * norm((f:real^M->real^N) y)") THEN
      REWRITE_TAC [NORM_CAUCHY_SCHWARZ_ABS] THEN
      GEN_REWRITE_TAC RAND_CONV [← REAL_ARITH (← q r"b * x * y:real = x * b * y")] THEN
      ASM_SIMP_TAC [REAL_LE_LMUL, NORM_POS_LE],
      X_GEN_TAC (← q r"x:real^M") THEN
      ASM_CASES_TAC (← q r"(f:real^M->real^N) x = vec 0") THENL
       [ASM_CASES_TAC (← q r"x:real^M = vec 0") THEN
        ASM_REWRITE_TAC [NORM_0, REAL_MUL_RZERO, REAL_LE_REFL] THEN
        FIRST_X_ASSUM (MP_TAC o SPECL [← q r"basis 1:real^N", ← q r"x:real^M"]) THEN
        ASM_SIMP_TAC [DOT_RZERO, NORM_BASIS, LE_REFL,
                      DIMINDEX_GE_1, REAL_MUL_LID],
        FIRST_ASSUM (MP_TAC o SPECL [← q r"(f:real^M->real^N) x", ← q r"x:real^M"]) THEN
        REWRITE_TAC [← GSYM NORM_POW_2, ← REAL_ARITH (← q
         r"y pow 2 <= b * y * x <=> y * y <= y * b * x")] THEN
        ASM_SIMP_TAC [REAL_LE_LMUL_EQ, NORM_POS_LT]]]))

  return { onorm, NORM_BOUND_GENERALIZE, ONORM_DOT, ONORM, ONORM_LE_EQ, ONORM_POS_LE,
           ONORM_EQ_0, ONORM_CONST, ONORM_POS_LT, ONORM_COMPOSE, ONORM_CMUL, ONORM_NEG,
           ONORM_TRIANGLE, ONORM_TRIANGLE_LE, ONORM_TRIANGLE_LT, ONORM_ID, ONORM_I,
           ONORM_INVERSE_FUNCTION_BOUND, ONORM_ADJOINT, ONORM_COMPOSE_ADJOINT_LEFT,
           ONORM_COMPOSE_ADJOINT_RIGHT, ONORM_TRANSP, ONORM_COVARIANCE,
           ONORM_COVARIANCE_ALT, ONORM_LE_EQ_2, ONORM_LE_EQ_2_ABS }

/- ------------------------------------------------------------------------- -/
/- It's handy to "lift" from R to R^1 and "drop" from R^1 to R.             -/
/- (vectors.ml 3819-3998)                                                     -/
/- ------------------------------------------------------------------------- -/

structure LiftDrop1 where
  lift : thm
  drop : thm
  LIFT_COMPONENT : thm
  LIFT_DROP : thm
  IMAGE_LIFT_DROP : thm
  IN_IMAGE_LIFT_DROP : thm
  FORALL_LIFT : thm
  EXISTS_LIFT : thm
  FORALL_DROP : thm
  EXISTS_DROP : thm
  FORALL_LIFT_FUN : thm
  FORALL_DROP_FUN : thm
  FORALL_FUN_LIFT : thm
  FORALL_FUN_DROP : thm
  EXISTS_LIFT_FUN : thm
  EXISTS_DROP_FUN : thm
  EXISTS_FUN_LIFT : thm
  EXISTS_FUN_DROP : thm
  LIFT_EQ : thm
  DROP_EQ : thm
  LIFT_IN_IMAGE_LIFT : thm
  FORALL_LIFT_IMAGE : thm
  EXISTS_LIFT_IMAGE : thm
  SUBSET_LIFT_IMAGE : thm
  FORALL_DROP_IMAGE : thm
  EXISTS_DROP_IMAGE : thm
  SUBSET_DROP_IMAGE : thm
  DROP_IN_IMAGE_DROP : thm
  LIFT_NUM : thm
  LIFT_ADD : thm
  LIFT_SUB : thm
  LIFT_CMUL : thm
  LIFT_NEG : thm
  LIFT_EQ_CMUL : thm
  SUM_VSUM : thm
  VSUM_REAL : thm
  LIFT_SUM : thm
  DROP_VSUM : thm
  DROP_LAMBDA : thm
  DROP_VEC : thm
  DROP_ADD : thm
  deriving Inhabited

@[nospecialize]
def setupLiftDrop1 [HolBase] (D : VectorsDeps) (BBasics : Basics)
    (BVectorArith : VectorArith) (BVSum1 : VSum1) : ExceptT String IO LiftDrop1 := do
  -- @@SCOPE BEGIN
  let { MESON, MESON_TAC, SET_TAC, new_definition, .. } := D
  let { ARITH, CART_EQ, DIMINDEX_1, ETA_AX, .. } := D.core1
  let { IMAGE_SUBSET, IMAGE_o, IN_IMAGE, LAMBDA_BETA, LE_ANTISYM, LE_REFL, .. } := D.core2
  let { REAL_MUL_RID, .. } := D.core3
  let { o_DEF, o_THM, .. } := D.core5
  let { vec, .. } := BBasics
  let { VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, VECTOR_NEG_COMPONENT,
        VECTOR_SUB_COMPONENT, .. } := BVectorArith
  let { vsum, .. } := BVSum1
  -- @@SCOPE END

  let lift ← new_definition
   r"(lift:real->real^1) x = lambda i. x"

  let drop ← new_definition
   r"(drop:real^1->real) x = x$1"

  let LIFT_COMPONENT ← prove
   r"!x. (lift x)$1 = x"
   (SIMP_TAC [lift, LAMBDA_BETA, DIMINDEX_1, LE_ANTISYM])

  let LIFT_DROP ← prove
   r"(!x. lift(drop x) = x) /\ (!x. drop(lift x) = x)"
   (SIMP_TAC [lift, drop, CART_EQ, LAMBDA_BETA, DIMINDEX_1, LE_ANTISYM])

  let IMAGE_LIFT_DROP ← prove
   r"(!s. IMAGE (lift o drop) s = s) /\ (!s. IMAGE (drop o lift) s = s)"
   (REWRITE_TAC [o_DEF, LIFT_DROP] THEN SET_TAC [])

  let IN_IMAGE_LIFT_DROP ← prove
   r"(!x s. x IN IMAGE lift s <=> drop x IN s) /\
   (!x s. x IN IMAGE drop s <=> lift x IN s)"
   (REWRITE_TAC [IN_IMAGE] THEN MESON_TAC [LIFT_DROP])

  let FORALL_LIFT ← prove r"(!x. P x) = (!x. P(lift x))" (MESON_TAC [LIFT_DROP])
  let EXISTS_LIFT ← prove r"(?x. P x) = (?x. P(lift x))" (MESON_TAC [LIFT_DROP])
  let FORALL_DROP ← prove r"(!x. P x) = (!x. P(drop x))" (MESON_TAC [LIFT_DROP])
  let EXISTS_DROP ← prove r"(?x. P x) = (?x. P(drop x))" (MESON_TAC [LIFT_DROP])

  let FORALL_LIFT_FUN ← prove
   r"!P:(A->real^1)->bool. (!f. P f) <=> (!f. P(lift o f))"
   (GEN_TAC THEN EQ_TAC THEN SIMP_TAC [] THEN DISCH_TAC THEN
    X_GEN_TAC (← q r"f:A->real^1") THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"drop o (f:A->real^1)")) THEN
    REWRITE_TAC [o_DEF, LIFT_DROP, ETA_AX])

  let FORALL_DROP_FUN ← prove
   r"!P:(A->real)->bool. (!f. P f) <=> (!f. P(drop o f))"
   (REWRITE_TAC [FORALL_LIFT_FUN, o_DEF, LIFT_DROP, ETA_AX])

  let FORALL_FUN_LIFT ← prove
   r"!P:(real->A)->bool. (!f. P f) <=> (!f. P(f o lift))"
   (GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"f:real->A") THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(f:real->A) o drop")) THEN
    REWRITE_TAC [o_DEF, LIFT_DROP, ETA_AX])

  let FORALL_FUN_DROP ← prove
   r"!P:(real^1->A)->bool. (!f. P f) <=> (!f. P(f o drop))"
   (GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"f:real^1->A") THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(f:real^1->A) o lift")) THEN
    REWRITE_TAC [o_DEF, LIFT_DROP, ETA_AX])

  let EXISTS_LIFT_FUN ← prove
   r"!P:(A->real^1)->bool. (?f. P f) <=> (?f. P(lift o f))"
   (ONCE_REWRITE_TAC [← MESON [] (← q r"(?x. P x) <=> ~(!x. ~P x)")] THEN
    REWRITE_TAC [FORALL_LIFT_FUN])

  let EXISTS_DROP_FUN ← prove
   r"!P:(A->real)->bool. (?f. P f) <=> (?f. P(drop o f))"
   (ONCE_REWRITE_TAC [← MESON [] (← q r"(?x. P x) <=> ~(!x. ~P x)")] THEN
    REWRITE_TAC [FORALL_DROP_FUN])

  let EXISTS_FUN_LIFT ← prove
   r"!P:(real->A)->bool. (?f. P f) <=> (?f. P(f o lift))"
   (GEN_TAC THEN ONCE_REWRITE_TAC [← MESON [] (← q r"(?x. P x) <=> ~(!x. ~P x)")] THEN
    REWRITE_TAC [FORALL_FUN_LIFT])

  let EXISTS_FUN_DROP ← prove
   r"!P:(real^1->A)->bool. (?f. P f) <=> (?f. P(f o drop))"
   (GEN_TAC THEN ONCE_REWRITE_TAC [← MESON [] (← q r"(?x. P x) <=> ~(!x. ~P x)")] THEN
    REWRITE_TAC [FORALL_FUN_DROP])

  let LIFT_EQ ← prove r"!x y. (lift x = lift y) <=> (x = y)" (MESON_TAC [LIFT_DROP])
  let DROP_EQ ← prove r"!x y. (drop x = drop y) <=> (x = y)" (MESON_TAC [LIFT_DROP])

  let LIFT_IN_IMAGE_LIFT ← prove
   r"!x s. (lift x) IN (IMAGE lift s) <=> x IN s"
   (REWRITE_TAC [IN_IMAGE] THEN MESON_TAC [LIFT_DROP])

  let FORALL_LIFT_IMAGE ← prove
   r"!P. (!s. P s) <=> (!s. P(IMAGE lift s))"
   (MESON_TAC [IMAGE_LIFT_DROP, IMAGE_o])

  let EXISTS_LIFT_IMAGE ← prove
   r"!P. (?s. P s) <=> (?s. P(IMAGE lift s))"
   (MESON_TAC [IMAGE_LIFT_DROP, IMAGE_o])

  let SUBSET_LIFT_IMAGE ← prove
   r"!s t. IMAGE lift s SUBSET IMAGE lift t <=> s SUBSET t"
   (REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [IMAGE_SUBSET] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← ISPEC (← q r"drop") (← MATCH_MP IMAGE_SUBSET th)))) THEN
    REWRITE_TAC [← GSYM IMAGE_o, IMAGE_LIFT_DROP])

  let FORALL_DROP_IMAGE ← prove
   r"!P. (!s. P s) <=> (!s. P(IMAGE drop s))"
   (MESON_TAC [IMAGE_LIFT_DROP, IMAGE_o])

  let EXISTS_DROP_IMAGE ← prove
   r"!P. (?s. P s) <=> (?s. P(IMAGE drop s))"
   (MESON_TAC [IMAGE_LIFT_DROP, IMAGE_o])

  let SUBSET_DROP_IMAGE ← prove
   r"!s t. IMAGE drop s SUBSET IMAGE drop t <=> s SUBSET t"
   (REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC [IMAGE_SUBSET] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← ISPEC (← q r"lift") (← MATCH_MP IMAGE_SUBSET th)))) THEN
    REWRITE_TAC [← GSYM IMAGE_o, IMAGE_LIFT_DROP])

  let DROP_IN_IMAGE_DROP ← prove
   r"!x s. (drop x) IN (IMAGE drop s) <=> x IN s"
   (REWRITE_TAC [IN_IMAGE] THEN MESON_TAC [LIFT_DROP])

  let LIFT_NUM ← prove
   r"!n. lift(&n) = vec n"
   (SIMP_TAC [CART_EQ, lift, vec, LAMBDA_BETA])

  let LIFT_ADD ← prove
   r"!x y. lift(x + y) = lift x + lift y"
   (SIMP_TAC [CART_EQ, lift, LAMBDA_BETA, VECTOR_ADD_COMPONENT])

  let LIFT_SUB ← prove
   r"!x y. lift(x - y) = lift x - lift y"
   (SIMP_TAC [CART_EQ, lift, LAMBDA_BETA, VECTOR_SUB_COMPONENT])

  let LIFT_CMUL ← prove
   r"!x c. lift(c * x) = c % lift(x)"
   (SIMP_TAC [CART_EQ, lift, LAMBDA_BETA, VECTOR_MUL_COMPONENT])

  let LIFT_NEG ← prove
   r"!x. lift(--x) = --(lift x)"
   (SIMP_TAC [CART_EQ, lift, LAMBDA_BETA, VECTOR_NEG_COMPONENT])

  let LIFT_EQ_CMUL ← prove
   r"!x. lift x = x % vec 1"
   (REWRITE_TAC [← GSYM LIFT_NUM, ← GSYM LIFT_CMUL, REAL_MUL_RID])

  let SUM_VSUM ← prove
   r"!f s. sum s f = drop(vsum s(lift o f))"
   (SIMP_TAC [vsum, drop, LAMBDA_BETA, DIMINDEX_1, ARITH] THEN
    REWRITE_TAC [o_THM, ← GSYM drop, LIFT_DROP, ETA_AX])

  let VSUM_REAL ← prove
   r"!f s. vsum s f = lift(sum s (drop o f))"
   (REWRITE_TAC [o_DEF, SUM_VSUM, LIFT_DROP, ETA_AX])

  let LIFT_SUM ← prove
   r"!k x. lift(sum k x) = vsum k (lift o x)"
   (REWRITE_TAC [SUM_VSUM, LIFT_DROP])

  let DROP_VSUM ← prove
   r"!k x. drop(vsum k x) = sum k (drop o x)"
   (REWRITE_TAC [VSUM_REAL, LIFT_DROP])

  let DROP_LAMBDA ← prove
   r"!x. drop(lambda i. x i) = x 1"
   (SIMP_TAC [drop, LAMBDA_BETA, DIMINDEX_1, LE_REFL])

  let DROP_VEC ← prove
   r"!n. drop(vec n) = &n"
   (MESON_TAC [LIFT_DROP, LIFT_NUM])

  let DROP_ADD ← prove
   r"!x y. drop(x + y) = drop x + drop y"
   (MESON_TAC [LIFT_DROP, LIFT_ADD])

  return { lift, drop, LIFT_COMPONENT, LIFT_DROP, IMAGE_LIFT_DROP, IN_IMAGE_LIFT_DROP,
           FORALL_LIFT, EXISTS_LIFT, FORALL_DROP, EXISTS_DROP, FORALL_LIFT_FUN,
           FORALL_DROP_FUN, FORALL_FUN_LIFT, FORALL_FUN_DROP, EXISTS_LIFT_FUN,
           EXISTS_DROP_FUN, EXISTS_FUN_LIFT, EXISTS_FUN_DROP, LIFT_EQ, DROP_EQ,
           LIFT_IN_IMAGE_LIFT, FORALL_LIFT_IMAGE, EXISTS_LIFT_IMAGE, SUBSET_LIFT_IMAGE,
           FORALL_DROP_IMAGE, EXISTS_DROP_IMAGE, SUBSET_DROP_IMAGE, DROP_IN_IMAGE_DROP,
           LIFT_NUM, LIFT_ADD, LIFT_SUB, LIFT_CMUL, LIFT_NEG, LIFT_EQ_CMUL, SUM_VSUM,
           VSUM_REAL, LIFT_SUM, DROP_VSUM, DROP_LAMBDA, DROP_VEC, DROP_ADD }

/- ------------------------------------------------------------------------- -/
/- Lift and drop, continued.  (vectors.ml 4000-4128)                         -/
/- ------------------------------------------------------------------------- -/

structure LiftDrop2 where
  DROP_SUB : thm
  DROP_CMUL : thm
  DROP_NEG : thm
  NORM_1 : thm
  DIST_1 : thm
  NORM_1_POS : thm
  NORM_LIFT : thm
  DIST_LIFT : thm
  ABS_DROP : thm
  LINEAR_VMUL_DROP : thm
  LINEAR_FROM_REALS : thm
  LINEAR_TO_REALS : thm
  LINEAR_FROM_1 : thm
  DROP_EQ_0 : thm
  DROP_WLOG_LE : thm
  IMAGE_LIFT_UNIV : thm
  IMAGE_DROP_UNIV : thm
  LINEAR_LIFT_DOT : thm
  LINEAR_TO_1 : thm
  LINEAR_LIFT_COMPONENT : thm
  BILINEAR_DROP_MUL : thm
  BILINEAR_MUL_DROP : thm
  BILINEAR_LIFT_MUL : thm
  LINEAR_COMPONENTWISE : thm
  DROP_BASIS : thm
  deriving Inhabited

@[nospecialize]
def setupLiftDrop2 [HolBase] (D : VectorsDeps) (BBasics : Basics)
    (BVectorArith : VectorArith) (BDotProps : DotProps) (BNorm1 : Norm1) (BBasis : Basis)
    (BLinear : Linear) (BBilinear : Bilinear) (BMatrix : Matrix) (BInvertible : Invertible)
    (BLiftDrop1 : LiftDrop1) : ExceptT String IO LiftDrop2 := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, REAL_ARITH_TAC, .. } := D
  let { CART_EQ, DIMINDEX_1, EXTENSION, FINITE_INDEX_INRANGE, .. } := D.core1
  let { FUN_EQ_THM, IN_IMAGE, IN_UNIV, LAMBDA_BETA, LE_ANTISYM, LE_REFL, .. } := D.core2
  let { REAL_LE_TOTAL, REAL_MUL_AC, .. } := D.core3
  let { SUM_SING_NUMSEG, real_abs, .. } := D.core5
  let { FORALL_1, dot, vector_mul, .. } := BBasics
  let { VECTOR_ADD_COMPONENT, VECTOR_ARITH_TAC, VECTOR_MUL_COMPONENT, .. } := BVectorArith
  let { DOT_RADD, DOT_RMUL, .. } := BDotProps
  let { DIST_REAL, NORM_REAL, dist, .. } := BNorm1
  let { DOT_BASIS, basis, .. } := BBasis
  let { LINEAR_ID, LINEAR_VMUL_COMPONENT, linear, .. } := BLinear
  let { BILINEAR_SWAP, bilinear, .. } := BBilinear
  let { column, matrix_vector_mul, row, .. } := BMatrix
  let { MATRIX_WORKS, .. } := BInvertible
  let { DROP_ADD, DROP_EQ, DROP_VEC, LIFT_ADD, LIFT_CMUL, LIFT_COMPONENT, LIFT_DROP,
        LIFT_EQ, LIFT_NEG, LIFT_SUB, drop, lift, .. } := BLiftDrop1
  -- @@SCOPE END

  let DROP_SUB ← prove
   r"!x y. drop(x - y) = drop x - drop y"
   (MESON_TAC [LIFT_DROP, LIFT_SUB])

  let DROP_CMUL ← prove
   r"!x c. drop(c % x) = c * drop(x)"
   (MESON_TAC [LIFT_DROP, LIFT_CMUL])

  let DROP_NEG ← prove
   r"!x. drop(--x) = --(drop x)"
   (MESON_TAC [LIFT_DROP, LIFT_NEG])

  let NORM_1 ← prove
   r"!x. norm x = abs(drop x)"
   (REWRITE_TAC [drop, NORM_REAL])

  let DIST_1 ← prove
   r"!x y. dist(x,y) = abs(drop x - drop y)"
   (REWRITE_TAC [dist, DROP_SUB, NORM_1])

  let NORM_1_POS ← prove
   r"!x. &0 <= drop x ==> norm x = drop x"
   (SIMP_TAC [NORM_1, real_abs])

  let NORM_LIFT ← prove
   r"!x. norm(lift x) = abs(x)"
   (SIMP_TAC [lift, NORM_REAL, LIFT_COMPONENT])

  let DIST_LIFT ← prove
   r"!x y. dist(lift x,lift y) = abs(x - y)"
   (REWRITE_TAC [DIST_REAL, LIFT_COMPONENT])

  let ABS_DROP ← prove
   r"!x. abs(drop x) = norm x"
   (REWRITE_TAC [NORM_1])

  let LINEAR_VMUL_DROP ← prove
   r"!f v. linear f ==> linear (\x. drop(f x) % v)"
   (SIMP_TAC [drop, LINEAR_VMUL_COMPONENT, DIMINDEX_1, LE_REFL])

  let LINEAR_FROM_REALS ← prove
   r"!f:real^1->real^N. linear f ==> f = \x. drop x % column 1 (matrix f)"
   (GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (REWRITE_TAC [← GSYM (← MATCH_MP MATRIX_WORKS th)])) THEN
    SIMP_TAC [CART_EQ, matrix_vector_mul, vector_mul, LAMBDA_BETA,
              DIMINDEX_1, SUM_SING_NUMSEG, drop, column] THEN
    REWRITE_TAC [REAL_MUL_AC])

  let LINEAR_TO_REALS ← prove
   r"!f:real^N->real^1. linear f ==> f = \x. lift(row 1 (matrix f) dot x)"
   (GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (REWRITE_TAC [← GSYM (← MATCH_MP MATRIX_WORKS th)])) THEN
    SIMP_TAC [CART_EQ, matrix_vector_mul, dot, LAMBDA_BETA,
              DIMINDEX_1, SUM_SING_NUMSEG, lift, row, LE_ANTISYM])

  let LINEAR_FROM_1 ← prove
   r"!f:real^1->real^N. linear f <=> ?c. f = \x. drop x % c"
   (GEN_TAC THEN EQ_TAC THENL [MESON_TAC [LINEAR_FROM_REALS], ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LINEAR_VMUL_DROP THEN
    REWRITE_TAC [LINEAR_ID])

  let DROP_EQ_0 ← prove
   r"!x. drop x = &0 <=> x = vec 0"
   (REWRITE_TAC [← GSYM DROP_EQ, DROP_VEC])

  let DROP_WLOG_LE ← prove
   r"(!x y. P x y <=> P y x) /\ (!x y. drop x <= drop y ==> P x y)
   ==> (!x y. P x y)"
   (MESON_TAC [REAL_LE_TOTAL])

  let IMAGE_LIFT_UNIV ← prove
   r"IMAGE lift (:real) = (:real^1)"
   (REWRITE_TAC [EXTENSION, IN_IMAGE, IN_UNIV] THEN MESON_TAC [LIFT_DROP])

  let IMAGE_DROP_UNIV ← prove
   r"IMAGE drop (:real^1) = (:real)"
   (REWRITE_TAC [EXTENSION, IN_IMAGE, IN_UNIV] THEN MESON_TAC [LIFT_DROP])

  let LINEAR_LIFT_DOT ← prove
   r"!a. linear(\x. lift(a dot x))"
   (REWRITE_TAC [linear, DOT_RMUL, DOT_RADD, LIFT_ADD, LIFT_CMUL])

  let LINEAR_TO_1 ← prove
   r"!f:real^N->real^1. linear f <=> ?a. f = \x. lift(a dot x)"
   (GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [LINEAR_LIFT_DOT] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP LINEAR_TO_REALS) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN MESON_TAC [])

  let LINEAR_LIFT_COMPONENT ← prove
   r"!k. linear(\x:real^N. lift(x$k))"
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN (← q r"?j. 1 <= j /\ j <= dimindex(:N) /\ !z:real^N. z$k = z$j")
    CHOOSE_TAC THENL
     [REWRITE_TAC [FINITE_INDEX_INRANGE],
      MP_TAC (← ISPEC (← q r"basis j:real^N") LINEAR_LIFT_DOT) THEN
      ASM_SIMP_TAC [DOT_BASIS]])

  let BILINEAR_DROP_MUL ← prove
   r"bilinear (\x y:real^N. drop x % y)"
   (REWRITE_TAC [bilinear, linear] THEN
    REWRITE_TAC [DROP_ADD, DROP_CMUL] THEN VECTOR_ARITH_TAC)

  let BILINEAR_MUL_DROP ← prove
   r"bilinear(\y:real^N x. drop x % y)"
   (GEN_REWRITE_TAC id [← GSYM BILINEAR_SWAP] THEN
    REWRITE_TAC [BILINEAR_DROP_MUL])

  let BILINEAR_LIFT_MUL ← prove
   r"bilinear (\x y. lift(drop x * drop y))"
   (REWRITE_TAC [linear, bilinear, ← GSYM DROP_EQ,
                 LIFT_DROP, DROP_ADD, DROP_CMUL] THEN
    REAL_ARITH_TAC)

  let LINEAR_COMPONENTWISE ← prove
   r"!f:real^M->real^N.
        linear f <=>
        !i. 1 <= i /\ i <= dimindex(:N) ==> linear(\x. lift(f(x)$i))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [linear] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [CART_EQ] THEN
    SIMP_TAC [← GSYM LIFT_CMUL, ← GSYM LIFT_ADD, LIFT_EQ] THEN
    REWRITE_TAC [VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
    MESON_TAC [])

  let DROP_BASIS ← prove
   r"!i. drop(basis i) = if i = 1 then &1 else &0"
   (REWRITE_TAC [← GSYM LIFT_EQ, LIFT_DROP] THEN
    SIMP_TAC [basis, lift, CART_EQ, LAMBDA_BETA, DIMINDEX_1, FORALL_1] THEN
    MESON_TAC [])

  return { DROP_SUB, DROP_CMUL, DROP_NEG, NORM_1, DIST_1, NORM_1_POS, NORM_LIFT,
           DIST_LIFT, ABS_DROP, LINEAR_VMUL_DROP, LINEAR_FROM_REALS, LINEAR_TO_REALS,
           LINEAR_FROM_1, DROP_EQ_0, DROP_WLOG_LE, IMAGE_LIFT_UNIV, IMAGE_DROP_UNIV,
           LINEAR_LIFT_DOT, LINEAR_TO_1, LINEAR_LIFT_COMPONENT, BILINEAR_DROP_MUL,
           BILINEAR_MUL_DROP, BILINEAR_LIFT_MUL, LINEAR_COMPONENTWISE, DROP_BASIS }

/- ------------------------------------------------------------------------- -/
/- Indicator functions into real^1; flattening and matrifying of arithmetic -/
/- operations; pasting vectors.  (vectors.ml 4130-4398)                      -/
/- ------------------------------------------------------------------------- -/

structure Paste1 where
  indicator : thm
  DROP_INDICATOR : thm
  DROP_INDICATOR_POS_LE : thm
  DROP_INDICATOR_LE_1 : thm
  DROP_INDICATOR_ABS_LE_1 : thm
  INDICATOR_COMPLEMENT : thm
  VECTORIZE_ADD : thm
  VECTORIZE_CMUL : thm
  VECTORIZE_SUB : thm
  VECTORIZE_0 : thm
  MATRIFY_0 : thm
  VECTORIZE_EQ_0 : thm
  MATRIFY_ADD : thm
  MATRIFY_CMUL : thm
  MATRIFY_SUB : thm
  MATRIFY_EQ_0 : thm
  BILINEAR_MATRIX_VECTOR_MUL : thm
  BILINEAR_MATRIX_MUL : thm
  LINEAR_FSTCART : thm
  LINEAR_SNDCART : thm
  FSTCART_VEC : thm
  FSTCART_ADD : thm
  FSTCART_CMUL : thm
  FSTCART_NEG : thm
  FSTCART_SUB : thm
  FSTCART_VSUM : thm
  SNDCART_VEC : thm
  SNDCART_ADD : thm
  SNDCART_CMUL : thm
  SNDCART_NEG : thm
  SNDCART_SUB : thm
  SNDCART_VSUM : thm
  PASTECART_VEC : thm
  PASTECART_ADD : thm
  PASTECART_CMUL : thm
  PASTECART_NEG : thm
  PASTECART_SUB : thm
  PASTECART_VSUM : thm
  PASTECART_EQ_VEC : thm
  FSTCART_SNDCART_MAT_ZERO : thm
  FSTCART_SNDCART_MATRIX_ADD : thm
  NORM_FSTCART : thm
  DIST_FSTCART : thm
  NORM_SNDCART : thm
  DIST_SNDCART : thm
  DOT_PASTECART : thm
  SQNORM_PASTECART : thm
  NORM_PASTECART : thm
  deriving Inhabited

@[nospecialize]
def setupPaste1 [HolBase] (D : VectorsDeps) (BBasics : Basics) (BVectorArith : VectorArith)
    (BDotProps : DotProps) (BNorm1 : Norm1) (BNorm2 : Norm2) (BVSum1 : VSum1)
    (BLinear : Linear) (BBilinear : Bilinear) (BMatrix : Matrix) (BMatArith : MatArith)
    (BMatProps : MatProps) (BLiftDrop1 : LiftDrop1) : ExceptT String IO Paste1 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, MESON_TAC, REAL_ARITH_TAC, new_definition, .. } := D
  let { ADD_SUB, ADD_SYM, CART_EQ, DIMINDEX_FINITE_PROD, DIMINDEX_FINITE_SUM,
        DIMINDEX_NONZERO, EQ_ADD_RCANCEL, ETA_AX, FINITE_INDUCT_STRONG, FINITE_NUMSEG,
        FINITE_RULES, .. } := D.core1
  let { FSTCART_COMPONENT, FSTCART_PASTECART, FUN_EQ_THM, IN_DIFF, IN_UNIV,
        LAMBDA_BETA, NUMSEG_OFFSET_IMAGE, .. } := D.core2
  let { PASTECART_EQ, PASTECART_FST_SND, REAL_LE_ADD, REAL_LE_ADDL, REAL_LE_ADDR,
        REAL_LE_LADD, REAL_LE_POW_2, REAL_LE_REFL, REAL_LE_SQUARE, .. } := D.core3
  let { RIGHT_FORALL_IMP_THM, SNDCART_COMPONENT, SNDCART_PASTECART, SQRT_MONO_LE_EQ,
        SQRT_POS_LE, SQRT_POW_2, SUM_ADD_SPLIT, .. } := D.core4
  let { SUM_IMAGE, SUM_POS_LE, fstcart, o_DEF, pastecart, sndcart, .. } := D.core5
  let { MATRIFY_VECTORIZE, VECTORIZE_COMPONENT, VECTORIZE_MATRIFY, matrify,
        vectorize, .. } := D.misc
  let { dot, vec, .. } := BBasics
  let { VECTOR_ADD_COMPONENT, VECTOR_ARITH, VECTOR_MUL_COMPONENT, VECTOR_SUB,
        VECTOR_SUB_COMPONENT, VECTOR_SUB_REFL, VECTOR_SUB_RZERO, VEC_COMPONENT, .. } :=
    BVectorArith
  let { DOT_POS_LE, .. } := BDotProps
  let { NORM_POW_2, dist, vector_norm, .. } := BNorm1
  let { NORM_EQ_SQUARE, .. } := BNorm2
  let { VSUM_CLAUSES, .. } := BVSum1
  let { linear, .. } := BLinear
  let { bilinear, .. } := BBilinear
  let { MATRIX_ADD_COMPONENT, MATRIX_CMUL_COMPONENT, MATRIX_SUB_COMPONENT,
        MAT_0_COMPONENT, MAT_0_ROW, .. } := BMatrix
  let { MATRIX_ADD_LDISTRIB, MATRIX_ADD_RDISTRIB, MATRIX_MUL_LMUL, MATRIX_MUL_RMUL,
        MATRIX_VECTOR_MUL_ADD_LDISTRIB, MATRIX_VECTOR_MUL_ADD_RDISTRIB,
        MATRIX_VECTOR_MUL_RMUL, .. } := BMatArith
  let { MATRIX_VECTOR_LMUL, .. } := BMatProps
  let { DROP_VEC, .. } := BLiftDrop1
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let indicator ← new_definition
   r"indicator s :real^M->real^1 = \x. if x IN s then vec 1 else vec 0"

  let DROP_INDICATOR ← prove
   r"!s x. drop(indicator s x) = if x IN s then &1 else &0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [indicator] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [DROP_VEC])

  let DROP_INDICATOR_POS_LE ← prove
   r"!s x. &0 <= drop(indicator s x)"
   (REWRITE_TAC [DROP_INDICATOR] THEN REAL_ARITH_TAC)

  let DROP_INDICATOR_LE_1 ← prove
   r"!s x. drop(indicator s x) <= &1"
   (REWRITE_TAC [DROP_INDICATOR] THEN REAL_ARITH_TAC)

  let DROP_INDICATOR_ABS_LE_1 ← prove
   r"!s x. abs(drop(indicator s x)) <= &1"
   (REWRITE_TAC [DROP_INDICATOR] THEN REAL_ARITH_TAC)

  let INDICATOR_COMPLEMENT ← prove
   r"!s. indicator((:real^N) DIFF s) = \x. vec 1 - indicator s x"
   (GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM, indicator] THEN
    X_GEN_TAC (← q r"x:real^N") THEN ASM_CASES_TAC (← q r"(x:real^N) IN s") THEN
    ASM_REWRITE_TAC [IN_UNIV, IN_DIFF, VECTOR_SUB_REFL, VECTOR_SUB_RZERO])

  let VECTORIZE_ADD ← prove
   r"!m1 m2:real^N^M. vectorize(m1 + m2) = vectorize m1 + vectorize m2"
   (SIMP_TAC [CART_EQ, vectorize, LAMBDA_BETA, VECTOR_ADD_COMPONENT] THEN
    REWRITE_TAC [MATRIX_ADD_COMPONENT])

  let VECTORIZE_CMUL ← prove
   r"!c m:real^N^M. vectorize(c %% m) = c % vectorize m"
   (SIMP_TAC [CART_EQ, vectorize, LAMBDA_BETA, VECTOR_MUL_COMPONENT] THEN
    REWRITE_TAC [MATRIX_CMUL_COMPONENT])

  let VECTORIZE_SUB ← prove
   r"!m1 m2:real^N^M. vectorize(m1 - m2) = vectorize m1 - vectorize m2"
   (SIMP_TAC [CART_EQ, vectorize, LAMBDA_BETA, VECTOR_SUB_COMPONENT] THEN
    REWRITE_TAC [MATRIX_SUB_COMPONENT])

  let VECTORIZE_0 ← prove
   r"vectorize(mat 0:real^N^M) = vec 0"
   (SIMP_TAC [CART_EQ, VECTORIZE_COMPONENT, DIMINDEX_FINITE_PROD] THEN
    REWRITE_TAC [VEC_COMPONENT, MAT_0_COMPONENT])

  let MATRIFY_0 ← prove
   r"matrify(vec 0) = mat 0"
   (MESON_TAC [VECTORIZE_0, VECTORIZE_MATRIFY, MATRIFY_VECTORIZE])

  let VECTORIZE_EQ_0 ← prove
   r"!m:real^N^M. vectorize m = vec 0 <=> m = mat 0"
   (MESON_TAC [VECTORIZE_0, MATRIFY_0, VECTORIZE_MATRIFY, MATRIFY_VECTORIZE])

  let MATRIFY_ADD ← prove
   r"!x y:real^(M,N)finite_prod. matrify(x + y) = matrify x + matrify y"
   (SIMP_TAC [CART_EQ, matrify, LAMBDA_BETA, MATRIX_ADD_COMPONENT,
              VECTOR_ADD_COMPONENT])

  let MATRIFY_CMUL ← prove
   r"!c x:real^(M,N)finite_prod. matrify(c % x) = c %% matrify x"
   (SIMP_TAC [CART_EQ, matrify, LAMBDA_BETA, MATRIX_CMUL_COMPONENT,
              VECTOR_MUL_COMPONENT])

  let MATRIFY_SUB ← prove
   r"!x y:real^(M,N)finite_prod. matrify(x - y) = matrify x - matrify y"
   (SIMP_TAC [CART_EQ, matrify, LAMBDA_BETA, MATRIX_SUB_COMPONENT,
              VECTOR_SUB_COMPONENT])

  let MATRIFY_EQ_0 ← prove
   r"!m:real^(M,N)finite_prod. matrify m = mat 0 <=> m = vec 0"
   (MESON_TAC [VECTORIZE_0, MATRIFY_0, VECTORIZE_MATRIFY, MATRIFY_VECTORIZE])

  let BILINEAR_MATRIX_VECTOR_MUL ← prove
   r"bilinear (\(m:real^(M,N)finite_prod) x:real^N. matrify m ** x)"
   (REWRITE_TAC [bilinear, linear] THEN
    REWRITE_TAC [MATRIFY_ADD, MATRIFY_CMUL] THEN
    REWRITE_TAC [MATRIX_VECTOR_MUL_ADD_LDISTRIB, MATRIX_VECTOR_MUL_ADD_RDISTRIB,
                 MATRIX_VECTOR_MUL_RMUL, MATRIX_VECTOR_LMUL])

  let BILINEAR_MATRIX_MUL ← prove
   r"bilinear (\(m1:real^(M,N)finite_prod) (m2:real^(N,P)finite_prod).
                   vectorize(matrify m1 ** matrify m2))"
   (REWRITE_TAC [bilinear, linear] THEN
    REWRITE_TAC [MATRIFY_ADD, MATRIFY_CMUL] THEN
    REWRITE_TAC [MATRIX_ADD_LDISTRIB, MATRIX_ADD_RDISTRIB,
                 MATRIX_MUL_RMUL, MATRIX_MUL_LMUL,
                 VECTORIZE_ADD, VECTORIZE_CMUL])

  let LINEAR_FSTCART ← prove
   r"linear fstcart"
   (SIMP_TAC [linear, fstcart, CART_EQ, LAMBDA_BETA, VECTOR_ADD_COMPONENT,
              VECTOR_MUL_COMPONENT, DIMINDEX_FINITE_SUM,
              ← ARITH_RULE (← q r"x <= a ==> x <= a + b:num")])

  let LINEAR_SNDCART ← prove
   r"linear sndcart"
   (SIMP_TAC [linear, sndcart, CART_EQ, LAMBDA_BETA, VECTOR_ADD_COMPONENT,
              VECTOR_MUL_COMPONENT, DIMINDEX_FINITE_SUM,
              ← ARITH_RULE (← q r"x <= a ==> x <= a + b:num"),
              ← ARITH_RULE (← q r"x <= b ==> x + a <= a + b:num")])

  let FSTCART_VEC ← prove
   r"!n. fstcart(vec n) = vec n"
   (SIMP_TAC [vec, fstcart, LAMBDA_BETA, CART_EQ, DIMINDEX_FINITE_SUM,
              ← ARITH_RULE (← q r"m <= n:num ==> m <= n + p")])

  let FSTCART_ADD ← prove
   r"!x:real^(M,N)finite_sum y. fstcart(x + y) = fstcart(x) + fstcart(y)"
   (REWRITE_TAC [← REWRITE_RULE [linear] LINEAR_FSTCART])

  let FSTCART_CMUL ← prove
   r"!x:real^(M,N)finite_sum c. fstcart(c % x) = c % fstcart(x)"
   (REWRITE_TAC [← REWRITE_RULE [linear] LINEAR_FSTCART])

  let FSTCART_NEG ← prove
   r"!x:real^(M,N)finite_sum. --(fstcart x) = fstcart(--x)"
   (ONCE_REWRITE_TAC [← va r"--x = --(&1) % x"] THEN
    REWRITE_TAC [FSTCART_CMUL])

  let FSTCART_SUB ← prove
   r"!x:real^(M,N)finite_sum y. fstcart(x - y) = fstcart(x) - fstcart(y)"
   (REWRITE_TAC [VECTOR_SUB, FSTCART_NEG, FSTCART_ADD])

  let FSTCART_VSUM ← prove
   r"!k x. FINITE k ==> (fstcart(vsum k x) = vsum k (\i. fstcart(x i)))"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [VSUM_CLAUSES, FINITE_RULES, FSTCART_ADD, FSTCART_VEC])

  let SNDCART_VEC ← prove
   r"!n. sndcart(vec n) = vec n"
   (SIMP_TAC [vec, sndcart, LAMBDA_BETA, CART_EQ, DIMINDEX_FINITE_SUM,
              ← ARITH_RULE (← q r"x <= a ==> x <= a + b:num"),
              ← ARITH_RULE (← q r"x <= b ==> x + a <= a + b:num")])

  let SNDCART_ADD ← prove
   r"!x:real^(M,N)finite_sum y. sndcart(x + y) = sndcart(x) + sndcart(y)"
   (REWRITE_TAC [← REWRITE_RULE [linear] LINEAR_SNDCART])

  let SNDCART_CMUL ← prove
   r"!x:real^(M,N)finite_sum c. sndcart(c % x) = c % sndcart(x)"
   (REWRITE_TAC [← REWRITE_RULE [linear] LINEAR_SNDCART])

  let SNDCART_NEG ← prove
   r"!x:real^(M,N)finite_sum. --(sndcart x) = sndcart(--x)"
   (ONCE_REWRITE_TAC [← va r"--x = --(&1) % x"] THEN
    REWRITE_TAC [SNDCART_CMUL])

  let SNDCART_SUB ← prove
   r"!x:real^(M,N)finite_sum y. sndcart(x - y) = sndcart(x) - sndcart(y)"
   (REWRITE_TAC [VECTOR_SUB, SNDCART_NEG, SNDCART_ADD])

  let SNDCART_VSUM ← prove
   r"!k x. FINITE k ==> (sndcart(vsum k x) = vsum k (\i. sndcart(x i)))"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [VSUM_CLAUSES, FINITE_RULES, SNDCART_ADD, SNDCART_VEC])

  let PASTECART_VEC ← prove
   r"!n. pastecart (vec n) (vec n) = vec n"
   (REWRITE_TAC [PASTECART_EQ, FSTCART_VEC, SNDCART_VEC,
                 FSTCART_PASTECART, SNDCART_PASTECART])

  let PASTECART_ADD ← prove
   r"!x1 y1 x2:real^M y2:real^N.
     pastecart x1 y1 + pastecart x2 y2 = pastecart (x1 + x2) (y1 + y2)"
   (REWRITE_TAC [PASTECART_EQ, FSTCART_ADD, SNDCART_ADD,
                 FSTCART_PASTECART, SNDCART_PASTECART])

  let PASTECART_CMUL ← prove
   r"!x1 y1 c. pastecart (c % x1) (c % y1) = c % pastecart x1 y1"
   (REWRITE_TAC [PASTECART_EQ, FSTCART_CMUL, SNDCART_CMUL,
                 FSTCART_PASTECART, SNDCART_PASTECART])

  let PASTECART_NEG ← prove
   r"!x:real^M y:real^N. pastecart (--x) (--y) = --(pastecart x y)"
   (ONCE_REWRITE_TAC [← va r"--x = --(&1) % x"] THEN
    REWRITE_TAC [PASTECART_CMUL])

  let PASTECART_SUB ← prove
   r"!x1 y1 x2:real^M y2:real^N.
     pastecart x1 y1 - pastecart x2 y2 = pastecart (x1 - x2) (y1 - y2)"
   (REWRITE_TAC [VECTOR_SUB, ← GSYM PASTECART_NEG, PASTECART_ADD])

  let PASTECART_VSUM ← prove
   r"!k x y. FINITE k ==> (pastecart (vsum k x) (vsum k y) =
                         vsum k (\i. pastecart (x i) (y i)))"
   (SIMP_TAC [PASTECART_EQ, FSTCART_VSUM, SNDCART_VSUM,
              FSTCART_PASTECART, SNDCART_PASTECART, ETA_AX])

  let PASTECART_EQ_VEC ← prove
   r"!x y n. pastecart x y = vec n <=> x = vec n /\ y = vec n"
   (REWRITE_TAC [PASTECART_EQ, FSTCART_VEC, SNDCART_VEC,
                 FSTCART_PASTECART, SNDCART_PASTECART])

  let FSTCART_SNDCART_MAT_ZERO ← prove
   r"fstcart(mat 0:real^M^(A,B)finite_sum) = mat 0 /\
   sndcart(mat 0:real^M^(A,B)finite_sum) = mat 0"
   (SIMP_TAC [CART_EQ, FSTCART_COMPONENT, SNDCART_COMPONENT, MAT_0_ROW])

  let FSTCART_SNDCART_MATRIX_ADD ← prove
   r"!x:real^K^(M,N)finite_sum y.
     fstcart(x + y) = fstcart(x) + fstcart(y) /\
     sndcart(x + y) = sndcart(x) + sndcart(y)"
   (SIMP_TAC [CART_EQ, FSTCART_COMPONENT, SNDCART_COMPONENT,
              MATRIX_ADD_COMPONENT])

  let NORM_FSTCART ← prove
   r"!x. norm(fstcart x) <= norm x"
   (GEN_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← GSYM PASTECART_FST_SND] THEN
    SIMP_TAC [SQRT_MONO_LE_EQ, DOT_POS_LE, vector_norm] THEN
    SIMP_TAC [pastecart, dot, DIMINDEX_FINITE_SUM, LAMBDA_BETA, DIMINDEX_NONZERO,
              SUM_ADD_SPLIT, REAL_LE_ADDR, SUM_POS_LE, FINITE_NUMSEG,
              REAL_LE_SQUARE, ← ARITH_RULE (← q r"x <= a ==> x <= a + b:num"),
              ← ARITH_RULE (← q r"~(d = 0) ==> 1 <= d + 1")])

  let DIST_FSTCART ← prove
   r"!x y. dist(fstcart x,fstcart y) <= dist(x,y)"
   (REWRITE_TAC [dist, ← GSYM FSTCART_SUB, NORM_FSTCART])

  let NORM_SNDCART ← prove
   r"!x. norm(sndcart x) <= norm x"
   (GEN_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← GSYM PASTECART_FST_SND] THEN
    SIMP_TAC [SQRT_MONO_LE_EQ, DOT_POS_LE, vector_norm] THEN
    SIMP_TAC [pastecart, dot, DIMINDEX_FINITE_SUM, LAMBDA_BETA, DIMINDEX_NONZERO,
              SUM_ADD_SPLIT, ← ARITH_RULE (← q r"x <= a ==> x <= a + b:num"),
              ← ARITH_RULE (← q r"~(d = 0) ==> 1 <= d + 1")] THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [NUMSEG_OFFSET_IMAGE] THEN
    SIMP_TAC [SUM_IMAGE, FINITE_NUMSEG, EQ_ADD_RCANCEL, o_DEF, ADD_SUB] THEN
    SIMP_TAC [← ARITH_RULE (← q r"1 <= x ==> ~(x + a <= a)"), SUM_POS_LE, FINITE_NUMSEG,
              REAL_LE_ADDL, REAL_LE_SQUARE])

  let DIST_SNDCART ← prove
   r"!x y. dist(sndcart x,sndcart y) <= dist(x,y)"
   (REWRITE_TAC [dist, ← GSYM SNDCART_SUB, NORM_SNDCART])

  let DOT_PASTECART ← prove
   r"!x1 x2 y1 y2. (pastecart x1 x2) dot (pastecart y1 y2) =
                x1 dot y1 + x2 dot y2"
   (SIMP_TAC [pastecart, dot, LAMBDA_BETA, DIMINDEX_FINITE_SUM] THEN
    SIMP_TAC [SUM_ADD_SPLIT, ← ARITH_RULE (← q r"~(d = 0) ==> 1 <= d + 1"),
              DIMINDEX_NONZERO, REAL_LE_LADD] THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [NUMSEG_OFFSET_IMAGE] THEN
    SIMP_TAC [SUM_IMAGE, FINITE_NUMSEG, EQ_ADD_RCANCEL, o_DEF, ADD_SUB] THEN
    SIMP_TAC [← ARITH_RULE (← q r"1 <= x ==> ~(x + a <= a)"), REAL_LE_REFL])

  let SQNORM_PASTECART ← prove
   r"!x y. norm(pastecart x y) pow 2 = norm(x) pow 2 + norm(y) pow 2"
   (REWRITE_TAC [NORM_POW_2, DOT_PASTECART])

  let NORM_PASTECART ← prove
   r"!x y. norm(pastecart x y) = sqrt(norm(x) pow 2 + norm(y) pow 2)"
   (REWRITE_TAC [NORM_EQ_SQUARE] THEN
    SIMP_TAC [SQRT_POS_LE, SQRT_POW_2, REAL_LE_ADD, REAL_LE_POW_2] THEN
    REWRITE_TAC [DOT_PASTECART, NORM_POW_2])

  return { indicator, DROP_INDICATOR, DROP_INDICATOR_POS_LE, DROP_INDICATOR_LE_1,
           DROP_INDICATOR_ABS_LE_1, INDICATOR_COMPLEMENT, VECTORIZE_ADD, VECTORIZE_CMUL,
           VECTORIZE_SUB, VECTORIZE_0, MATRIFY_0, VECTORIZE_EQ_0, MATRIFY_ADD, MATRIFY_CMUL,
           MATRIFY_SUB, MATRIFY_EQ_0, BILINEAR_MATRIX_VECTOR_MUL, BILINEAR_MATRIX_MUL,
           LINEAR_FSTCART, LINEAR_SNDCART, FSTCART_VEC, FSTCART_ADD, FSTCART_CMUL,
           FSTCART_NEG, FSTCART_SUB, FSTCART_VSUM, SNDCART_VEC, SNDCART_ADD, SNDCART_CMUL,
           SNDCART_NEG, SNDCART_SUB, SNDCART_VSUM, PASTECART_VEC, PASTECART_ADD,
           PASTECART_CMUL, PASTECART_NEG, PASTECART_SUB, PASTECART_VSUM, PASTECART_EQ_VEC,
           FSTCART_SNDCART_MAT_ZERO, FSTCART_SNDCART_MATRIX_ADD, NORM_FSTCART,
           DIST_FSTCART, NORM_SNDCART, DIST_SNDCART, DOT_PASTECART, SQNORM_PASTECART,
           NORM_PASTECART }

/- ------------------------------------------------------------------------- -/
/- Norms of pasted vectors; drop the k'th coordinate, or insert t at the    -/
/- k'th coordinate.  (vectors.ml 4400-4600)                                  -/
/- ------------------------------------------------------------------------- -/

structure Dropout where
  NORM_PASTECART_LE : thm
  DIST_PASTECART_LE : thm
  NORM_LE_PASTECART : thm
  DIST_LE_PASTECART : thm
  NORM_PASTECART_0 : thm
  DIST_PASTECART_CANCEL : thm
  LINEAR_PASTECART : thm
  LINEAR_PASTECART_EQ : thm
  dropout : thm
  pushin : thm
  DROPOUT_PUSHIN : thm
  PUSHIN_DROPOUT : thm
  DROPOUT_GALOIS : thm
  IN_IMAGE_DROPOUT : thm
  DROPOUT_EQ : thm
  DROPOUT_0 : thm
  DOT_DROPOUT : thm
  DOT_PUSHIN : thm
  DROPOUT_ADD : thm
  DROPOUT_SUB : thm
  DROPOUT_MUL : thm
  LINEAR_DROPOUT : thm
  LINEAR_PUSHIN : thm
  deriving Inhabited

@[nospecialize]
def setupDropout [HolBase] (D : VectorsDeps) (BBasics : Basics) (BVectorArith : VectorArith)
    (BDotProps : DotProps) (BNorm1 : Norm1) (BNorm2 : Norm2) (BLinear : Linear)
    (BPaste1 : Paste1) : ExceptT String IO Dropout := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, MESON_TAC, REAL_ARITH_TAC, REAL_RING,
        new_definition, .. } := D
  let { ADD_SUB, CART_EQ, COND_ID, DISJOINT_NUMSEG, EQ_TRANS, EXTENSION, FINITE_NUMSEG,
        FINITE_RESTRICT, .. } := D.core1
  let { IMAGE_ID, IN_DELETE, IN_ELIM_THM, IN_IMAGE, IN_NUMSEG, IN_UNION, LAMBDA_BETA,
        LT_REFL, .. } := D.core2
  let { PASTECART_INJ, REAL_ADD_LID, REAL_ADD_RID, REAL_LE_ADDL, REAL_LE_ADDR,
        REAL_LE_POW_2, REAL_LE_REFL, REAL_LE_RSQRT, REAL_MUL_LZERO, .. } := D.core3
  let { REAL_MUL_RZERO, REAL_SUB_RZERO, SIMPLE_IMAGE, SUB_ADD, SUM_0, SUM_CASES,
        SUM_DELETE, .. } := D.core4
  let { SUM_OFFSET, SUM_UNION, .. } := D.core5
  let { TRIANGLE_LEMMA, .. } := D.misc
  let { dot, .. } := BBasics
  let { VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, VECTOR_SUB_COMPONENT,
        VECTOR_SUB_REFL, VEC_COMPONENT, .. } := BVectorArith
  let { DOT_LZERO, .. } := BDotProps
  let { NORM_POS_LE, NORM_POW_2, dist, .. } := BNorm1
  let { NORM_EQ_SQUARE, .. } := BNorm2
  let { linear, .. } := BLinear
  let { DOT_PASTECART, NORM_PASTECART, PASTECART_ADD, PASTECART_CMUL,
        PASTECART_SUB, .. } := BPaste1
  -- @@SCOPE END

  let NORM_PASTECART_LE ← prove
   r"!x y. norm(pastecart x y) <= norm(x) + norm(y)"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC TRIANGLE_LEMMA THEN
    REWRITE_TAC [NORM_POS_LE, NORM_POW_2, DOT_PASTECART, REAL_LE_REFL])

  let DIST_PASTECART_LE ← prove
   r"!x1 y1 x2 y2.
        dist(pastecart x1 y1,pastecart x2 y2)
        <= dist(x1,x2) + dist(y1,y2)"
   (REWRITE_TAC [dist, PASTECART_SUB, NORM_PASTECART_LE])

  let NORM_LE_PASTECART ← prove
   r"!x:real^M y:real^N.
    norm(x) <= norm(pastecart x y) /\
    norm(y) <= norm(pastecart x y)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [NORM_PASTECART] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN
    REWRITE_TAC [REAL_LE_ADDL, REAL_LE_ADDR, REAL_LE_POW_2])

  let DIST_LE_PASTECART ← prove
   r"!x1 y1 x2 y2.
        dist(x1,x2) <= dist(pastecart x1 y1,pastecart x2 y2) /\
        dist(y1,y2) <= dist(pastecart x1 y1,pastecart x2 y2)"
   (REWRITE_TAC [dist, PASTECART_SUB, NORM_LE_PASTECART])

  let NORM_PASTECART_0 ← prove
   r"(!x. norm(pastecart x (vec 0)) = norm x) /\
   (!y. norm(pastecart (vec 0) y) = norm y)"
   (REWRITE_TAC [NORM_EQ_SQUARE, NORM_POW_2, NORM_POS_LE] THEN
    REWRITE_TAC [DOT_PASTECART, DOT_LZERO, REAL_ADD_LID, REAL_ADD_RID])

  let DIST_PASTECART_CANCEL ← prove
   r"(!x x' y. dist(pastecart x y,pastecart x' y) = dist(x,x')) /\
   (!x y y'. dist(pastecart x y,pastecart x y') = dist(y,y'))"
   (REWRITE_TAC [dist, PASTECART_SUB, VECTOR_SUB_REFL, NORM_PASTECART_0])

  let LINEAR_PASTECART ← prove
   r"!f:real^M->real^N g:real^M->real^P.
        linear f /\ linear g ==> linear (\x. pastecart (f x) (g x))"
   (SIMP_TAC [linear, PASTECART_ADD, ← GSYM PASTECART_CMUL])

  let LINEAR_PASTECART_EQ ← prove
   r"!f:real^M->real^N g:real^M->real^P.
        linear (\x. pastecart (f x) (g x)) <=> linear f /\ linear g"
   (REWRITE_TAC [linear, PASTECART_ADD, ← GSYM PASTECART_CMUL] THEN
    REWRITE_TAC [PASTECART_INJ] THEN MESON_TAC [])

  let dropout ← new_definition
   r"(dropout k:real^M->real^N) x =
        lambda i. if i < k /\ i <= dimindex(:M) then x$i
                  else if i + 1 <= dimindex(:M) then x$(i + 1)
                  else &0"

  let pushin ← new_definition
   r"pushin k t x = lambda i. if i < k then x$i
                           else if i = k then t
                           else x$(i - 1)"

  let DROPOUT_PUSHIN ← prove
   r"!k t x.
        dimindex(:M) + 1 = dimindex(:N)
        ==> (dropout k:real^N->real^M) (pushin k t x) = x"
   (REPEAT GEN_TAC THEN DISCH_THEN (ASSUME_TAC o SYM) THEN
    ASM_SIMP_TAC [CART_EQ, dropout, pushin, LAMBDA_BETA,
                  ← ARITH_RULE (← q r"1 <= n + 1"), ADD_SUB,
                  ← ARITH_RULE (← q r"m <= n ==> m <= n + 1 /\ m + 1 <= n + 1")] THEN
    ARITH_TAC)

  let PUSHIN_DROPOUT ← prove
   r"!k x.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> pushin k (x$k) ((dropout k:real^N->real^M) x) = x"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN (ASSUME_TAC o GSYM)) THEN
    ASM_SIMP_TAC [CART_EQ, dropout, pushin, LAMBDA_BETA,
                  ← ARITH_RULE (← q r"i <= n + 1 ==> i - 1 <= n")] THEN
    X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
    ASM_CASES_TAC (← q r"i:num = k") THEN ASM_REWRITE_TAC [LT_REFL] THEN
    FIRST_X_ASSUM (DISJ_CASES_TAC o MATCH_MP (← ARITH_RULE (← q
     r"~(i:num = k) ==> i < k \/ k < i"))) THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"i:num < k ==> ~(k < i)")] THEN
    W (MP_TAC o PART_MATCH (lhs o rand) LAMBDA_BETA o lhand o snd) THEN
    (ANTS_TAC THENL [ASM_ARITH_TAC, DISCH_THEN SUBST1_TAC]) THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"k < i ==> ~(i - 1 < k)")] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    TRY AP_TERM_TAC THEN ASM_ARITH_TAC)

  let DROPOUT_GALOIS ← prove
   r"!k x:real^N y:real^M.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (y = dropout k x <=> (?t. x = pushin k t y))"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_THEN SUBST1_TAC THEN
      EXISTS_TAC (← q r"(x:real^N)$k") THEN ASM_SIMP_TAC [PUSHIN_DROPOUT],
      DISCH_THEN (X_CHOOSE_THEN (← q r"t:real") SUBST1_TAC) THEN
      ASM_SIMP_TAC [DROPOUT_PUSHIN]])

  let IN_IMAGE_DROPOUT ← prove
   r"!x s.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (x IN IMAGE (dropout k:real^N->real^M) s <=>
             ?t. (pushin k t x) IN s)"
   (SIMP_TAC [IN_IMAGE, DROPOUT_GALOIS] THEN MESON_TAC [])

  let DROPOUT_EQ ← prove
   r"!x y k. dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N) /\
           x$k = y$k /\ (dropout k:real^N->real^M) x = dropout k y
           ==> x = y"
   (SIMP_TAC [CART_EQ, dropout, VEC_COMPONENT, LAMBDA_BETA, IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:real^N", ← q r"y:real^N", ← q r"k:num"] THEN
    STRIP_TAC THEN X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
    ASM_CASES_TAC (← q r"i:num = k") THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (DISJ_CASES_TAC o MATCH_MP (← ARITH_RULE (← q
     r"~(i:num = k) ==> i < k \/ k < i")))
    THENL
     [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"i:num")) THEN ASM_SIMP_TAC [],
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"i - 1")) THEN
      ASM_SIMP_TAC [SUB_ADD, ← ARITH_RULE (← q r"k < i ==> ~(i - 1 < k)")]] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC)

  let DROPOUT_0 ← prove
   r"dropout k (vec 0:real^N) = vec 0"
   (SIMP_TAC [dropout, VEC_COMPONENT, CART_EQ, COND_ID, LAMBDA_BETA])

  let DOT_DROPOUT ← prove
   r"!k x y:real^N.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (dropout k x:real^M) dot (dropout k y) = x dot y - x$k * y$k"
   (REPEAT STRIP_TAC THEN SIMP_TAC [dot, dropout, LAMBDA_BETA] THEN
    REWRITE_TAC [← TAUT (← q r"(if p then x else y:real) * (if p then a else b) =
                    (if p then x * a else y * b)")] THEN
    SIMP_TAC [SUM_CASES, FINITE_NUMSEG, FINITE_RESTRICT] THEN
    REWRITE_TAC [REAL_MUL_LZERO, SUM_0, REAL_ADD_RID, IN_ELIM_THM] THEN
    SUBGOAL_THEN
     (← q r"(!i. i IN 1..dimindex(:M) /\ i < k /\ i <= dimindex(:N) <=> i IN 1..k-1) /\
    (!i. (i IN 1..dimindex(:M) /\ ~(i < k /\ i <= dimindex(:N))) /\
          i + 1 <= dimindex(:N) <=>
          i IN k..dimindex(:M))")
    (fun th => REWRITE_TAC [th])
    THENL [REWRITE_TAC [IN_NUMSEG] THEN ASM_ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [SIMPLE_IMAGE, IMAGE_ID] THEN
    REWRITE_TAC [← GSYM (← SPEC (← q r"1") SUM_OFFSET)] THEN
    W (MP_TAC o PART_MATCH (rhs o rand) SUM_UNION o lhs o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [FINITE_NUMSEG, DISJOINT_NUMSEG] THEN ARITH_TAC,
      DISCH_THEN (SUBST1_TAC o SYM)] THEN
    MP_TAC (← ISPECL [← q r"\i. (x:real^N)$i * (y:real^N)$i",
                      ← q r"1..dimindex(:N)",
                      ← q r"k:num"] SUM_DELETE) THEN
    ASM_REWRITE_TAC [IN_NUMSEG, FINITE_NUMSEG] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, IN_NUMSEG, IN_UNION, IN_DELETE] THEN ASM_ARITH_TAC)

  let DOT_PUSHIN ← prove
   r"!k a b x y:real^M.
        dimindex(:M) + 1 = dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
        ==> (pushin k a x:real^N) dot (pushin k b y) = x dot y + a * b"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"(dropout k (pushin k a (x:real^M):real^N):real^M) dot
              (dropout k (pushin k b (y:real^M):real^N):real^M) +
              a * b") THEN
    CONJ_TAC THENL [ALL_TAC, ASM_SIMP_TAC [DROPOUT_PUSHIN]] THEN
    ASM_SIMP_TAC [DOT_DROPOUT] THEN
    MATCH_MP_TAC (← REAL_RING (← q
     r"a':real = a /\ b' = b ==> x = x - a' * b' + a * b")) THEN
    ASM_SIMP_TAC [pushin, LAMBDA_BETA, LT_REFL])

  let DROPOUT_ADD ← prove
   r"!k x y:real^N. dropout k (x + y) = dropout k x + dropout k y"
   (SIMP_TAC [dropout, VECTOR_ADD_COMPONENT, CART_EQ, LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_ADD_LID]))

  let DROPOUT_SUB ← prove
   r"!k x y:real^N. dropout k (x - y) = dropout k x - dropout k y"
   (SIMP_TAC [dropout, VECTOR_SUB_COMPONENT, CART_EQ, LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_SUB_RZERO]))

  let DROPOUT_MUL ← prove
   r"!k c x:real^N. dropout k (c % x) = c % dropout k x"
   (SIMP_TAC [dropout, VECTOR_MUL_COMPONENT, CART_EQ, LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_MUL_RZERO]))

  let LINEAR_DROPOUT ← prove
   r"!k. linear(dropout k :real^N->real^M)"
   (REWRITE_TAC [linear, DROPOUT_ADD, DROPOUT_MUL])

  let LINEAR_PUSHIN ← prove
   r"!k. linear(pushin k (&0))"
   (SIMP_TAC [linear, pushin, CART_EQ, LAMBDA_BETA, VECTOR_MUL_COMPONENT,
              VECTOR_ADD_COMPONENT] THEN
    REAL_ARITH_TAC)

  return { NORM_PASTECART_LE, DIST_PASTECART_LE, NORM_LE_PASTECART, DIST_LE_PASTECART,
           NORM_PASTECART_0, DIST_PASTECART_CANCEL, LINEAR_PASTECART, LINEAR_PASTECART_EQ,
           dropout, pushin, DROPOUT_PUSHIN, PUSHIN_DROPOUT, DROPOUT_GALOIS,
           IN_IMAGE_DROPOUT, DROPOUT_EQ, DROPOUT_0, DOT_DROPOUT, DOT_PUSHIN, DROPOUT_ADD,
           DROPOUT_SUB, DROPOUT_MUL, LINEAR_DROPOUT, LINEAR_PUSHIN }

/- ------------------------------------------------------------------------- -/
/- A bit of linear algebra: subspaces, span, independence; closure          -/
/- properties of subspaces; lemmas.  (vectors.ml 4604-4824)                  -/
/- ------------------------------------------------------------------------- -/

structure Subspace where
  subspace : thm
  span : thm
  dependent : thm
  independent : thm
  SUBSPACE_UNIV : thm
  SUBSPACE_IMP_NONEMPTY : thm
  SUBSPACE_0 : thm
  SUBSPACE_ADD : thm
  SUBSPACE_MUL : thm
  SUBSPACE_MUL_EQ : thm
  SUBSPACE_NEG : thm
  SUBSPACE_NEG_EQ : thm
  SUBSPACE_SUB : thm
  SUBSPACE_VSUM : thm
  SUBSPACE_LINEAR_IMAGE : thm
  SUBSPACE_LINEAR_PREIMAGE : thm
  SUBSPACE_TRIVIAL : thm
  SUBSPACE_INTER : thm
  SUBSPACE_INTERS : thm
  LINEAR_INJECTIVE_0_SUBSPACE : thm
  SUBSPACE_UNION_CHAIN : thm
  SUBSPACE_PCROSS : thm
  SUBSPACE_PCROSS_EQ : thm
  SPAN_SPAN : thm
  SPAN_MONO : thm
  SUBSPACE_SPAN : thm
  NONEMPTY_SPAN : thm
  SPAN_CLAUSES : thm
  SPAN_INDUCT : thm
  SPAN_EMPTY : thm
  INDEPENDENT_EMPTY : thm
  INDEPENDENT_NONZERO : thm
  INDEPENDENT_MONO : thm
  DEPENDENT_MONO : thm
  SPAN_SUBSPACE : thm
  SPAN_INDUCT_ALT : thm
  deriving Inhabited

@[nospecialize]
def setupSubspace [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith) (BVSum1 : VSum1)
    (BLinear : Linear) (BPaste1 : Paste1) : ExceptT String IO Subspace := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, new_definition,
        prove_inductive_relations_exist, .. } := D
  let { DE_MORGAN_THM, EQ_IMP, EXISTS_PASTECART, EXTENSION, FINITE_INDUCT_STRONG,
        FORALL_IN_IMAGE, .. } := D.core1
  let { FORALL_IN_PCROSS, FSTCART_PASTECART, IMP_CONJ, IN, IN_DELETE, IN_ELIM_THM,
        IN_IMAGE, IN_INSERT, IN_INTER, IN_INTERS, IN_SING, IN_UNION, IN_UNIV,
        NOT_IN_EMPTY, .. } := D.core2
  let { PASTECART_IN_PCROSS, PCROSS_EMPTY, REAL_MUL_LINV, .. } := D.core3
  let { RIGHT_FORALL_IMP_THM, SNDCART_PASTECART, SUBSET, SUBSET_ANTISYM, .. } := D.core4
  let { SWAP_FORALL_THM, .. } := D.core5
  let { HULL_HULL, HULL_MINIMAL, HULL_MONO, HULL_SUBSET, HULL_UNIQUE, P_HULL, .. } := D.misc
  let { VECTOR_ADD_ASSOC, VECTOR_ADD_LDISTRIB, VECTOR_ADD_LID, VECTOR_ADD_SYM,
        VECTOR_ARITH, VECTOR_ARITH_TAC, VECTOR_MUL_ASSOC, VECTOR_MUL_LID,
        VECTOR_MUL_LZERO, VECTOR_MUL_RZERO, VECTOR_NEG_NEG, VECTOR_SUB, VECTOR_SUB_EQ,
        VECTOR_SUB_RZERO, .. } := BVectorArith
  let { VSUM_CLAUSES, .. } := BVSum1
  let { LINEAR_0, LINEAR_SUB, linear, .. } := BLinear
  let { LINEAR_FSTCART, LINEAR_SNDCART, PASTECART_ADD, PASTECART_CMUL,
        PASTECART_VEC, .. } := BPaste1
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let subspace ← new_definition
   r"subspace s <=>
        vec(0) IN s /\
        (!x y. x IN s /\ y IN s ==> (x + y) IN s) /\
        (!c x. x IN s ==> (c % x) IN s)"

  let span ← new_definition
   r"span s = subspace hull s"

  let dependent ← new_definition
   r"dependent s <=> ?a. a IN s /\ a IN span(s DELETE a)"

  let independent ← new_definition
   r"independent s <=> ~(dependent s)"

  let SUBSPACE_UNIV ← prove
   r"subspace(UNIV:real^N->bool)"
   (REWRITE_TAC [subspace, IN_UNIV])

  let SUBSPACE_IMP_NONEMPTY ← prove
   r"!s. subspace s ==> ~(s = {})"
   (REWRITE_TAC [subspace] THEN SET_TAC [])

  let SUBSPACE_0 ← prove
   r"subspace s ==> vec(0) IN s"
   (SIMP_TAC [subspace])

  let SUBSPACE_ADD ← prove
   r"!x y s. subspace s /\ x IN s /\ y IN s ==> (x + y) IN s"
   (SIMP_TAC [subspace])

  let SUBSPACE_MUL ← prove
   r"!x c s. subspace s /\ x IN s ==> (c % x) IN s"
   (SIMP_TAC [subspace])

  let SUBSPACE_MUL_EQ ← prove
   r"!s c x:real^N. subspace s ==> ((c % x) IN s <=> c = &0 \/ x IN s)"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"c:real = &0") THEN
    ASM_SIMP_TAC [VECTOR_MUL_LZERO, SUBSPACE_0] THEN
    EQ_TAC THEN ASM_SIMP_TAC [SUBSPACE_MUL] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"x:real^N = inv c % (c % x)") SUBST1_TAC THENL
     [ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, VECTOR_MUL_LID],
      ASM_SIMP_TAC [SUBSPACE_MUL]])

  let SUBSPACE_NEG ← prove
   r"!x s. subspace s /\ x IN s ==> (--x) IN s"
   (SIMP_TAC [← va r"--x = --(&1) % x", SUBSPACE_MUL])

  let SUBSPACE_NEG_EQ ← prove
   r"!s x:real^N. subspace s ==> (--x IN s <=> x IN s)"
   (MESON_TAC [SUBSPACE_NEG, VECTOR_NEG_NEG])

  let SUBSPACE_SUB ← prove
   r"!x y s. subspace s /\ x IN s /\ y IN s ==> (x - y) IN s"
   (SIMP_TAC [VECTOR_SUB, SUBSPACE_ADD, SUBSPACE_NEG])

  let SUBSPACE_VSUM ← prove
   r"!s f t. subspace s /\ FINITE t /\ (!x. x IN t ==> f(x) IN s)
           ==> (vsum t f) IN s"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [VSUM_CLAUSES, SUBSPACE_0, IN_INSERT, SUBSPACE_ADD])

  let SUBSPACE_LINEAR_IMAGE ← prove
   r"!f s. linear f /\ subspace s ==> subspace(IMAGE f s)"
   (REWRITE_TAC [subspace, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC [FORALL_IN_IMAGE] THEN REWRITE_TAC [IN_IMAGE] THEN
    MESON_TAC [linear, LINEAR_0])

  let SUBSPACE_LINEAR_PREIMAGE ← prove
   r"!f s. linear f /\ subspace s ==> subspace {x | f(x) IN s}"
   (REWRITE_TAC [subspace, IN_ELIM_THM] THEN
    MESON_TAC [linear, LINEAR_0])

  let SUBSPACE_TRIVIAL ← prove
   r"subspace {vec 0}"
   (SIMP_TAC [subspace, IN_SING] THEN CONJ_TAC THEN VECTOR_ARITH_TAC)

  let SUBSPACE_INTER ← prove
   r"!s t. subspace s /\ subspace t ==> subspace (s INTER t)"
   (REWRITE_TAC [subspace, IN_INTER] THEN MESON_TAC [])

  let SUBSPACE_INTERS ← prove
   r"!f. (!s. s IN f ==> subspace s) ==> subspace(INTERS f)"
   (SIMP_TAC [subspace, IMP_CONJ, RIGHT_FORALL_IMP_THM, IN_INTERS])

  let LINEAR_INJECTIVE_0_SUBSPACE ← prove
   r"!f:real^M->real^N s.
        linear f /\ subspace s
         ==> ((!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) <=>
              (!x. x IN s /\ f x = vec 0 ==> x = vec 0))"
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [← GSYM VECTOR_SUB_EQ] THEN
    ASM_SIMP_TAC [← GSYM LINEAR_SUB] THEN
    ASM_MESON_TAC [VECTOR_SUB_RZERO, SUBSPACE_SUB, SUBSPACE_0])

  let SUBSPACE_UNION_CHAIN ← prove
   r"!s t:real^N->bool.
        subspace s /\ subspace t /\ subspace(s UNION t)
         ==> s SUBSET t \/ t SUBSET s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← SET_RULE (← q
     r"s SUBSET t \/ t SUBSET s <=>
    ~(?x y. x IN s /\ ~(x IN t) /\ y IN t /\ ~(y IN s))")] THEN
    STRIP_TAC THEN SUBGOAL_THEN (← q r"(x + y:real^N) IN s UNION t") MP_TAC THENL
     [MATCH_MP_TAC SUBSPACE_ADD THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC [],
      REWRITE_TAC [IN_UNION, DE_MORGAN_THM] THEN
      ASM_MESON_TAC [SUBSPACE_SUB, ← va
       r"(x + y) - x:real^N = y /\ (x + y) - y = x"]])

  let SUBSPACE_PCROSS ← prove
   r"!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t ==> subspace(s PCROSS t)"
   (REWRITE_TAC [subspace, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC [FORALL_IN_PCROSS, ← GSYM PASTECART_CMUL, PASTECART_ADD] THEN
    REWRITE_TAC [← GSYM PASTECART_VEC, PASTECART_IN_PCROSS] THEN SIMP_TAC [])

  let SUBSPACE_PCROSS_EQ ← prove
   r"!s:real^M->bool t:real^N->bool.
        subspace(s PCROSS t) <=> subspace s /\ subspace t"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"s:real^M->bool = {}") THENL
     [ASM_MESON_TAC [PCROSS_EMPTY, SUBSPACE_IMP_NONEMPTY], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"t:real^N->bool = {}") THENL
     [ASM_MESON_TAC [PCROSS_EMPTY, SUBSPACE_IMP_NONEMPTY], ALL_TAC] THEN
    EQ_TAC THEN REWRITE_TAC [SUBSPACE_PCROSS] THEN REPEAT STRIP_TAC THENL
     [MP_TAC (← ISPECL [← q r"fstcart:real^(M,N)finite_sum->real^M",
       ← q r"(s:real^M->bool) PCROSS (t:real^N->bool)"] SUBSPACE_LINEAR_IMAGE) THEN
      ASM_REWRITE_TAC [LINEAR_FSTCART],
      MP_TAC (← ISPECL [← q r"sndcart:real^(M,N)finite_sum->real^N",
       ← q r"(s:real^M->bool) PCROSS (t:real^N->bool)"] SUBSPACE_LINEAR_IMAGE) THEN
      ASM_REWRITE_TAC [LINEAR_SNDCART]] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, IN_IMAGE, EXISTS_PASTECART, PASTECART_IN_PCROSS,
                 FSTCART_PASTECART, SNDCART_PASTECART] THEN
    ASM SET_TAC [])

  let SPAN_SPAN ← prove
   r"!s. span(span s) = span s"
   (REWRITE_TAC [span, HULL_HULL])

  let SPAN_MONO ← prove
   r"!s t. s SUBSET t ==> span s SUBSET span t"
   (REWRITE_TAC [span, HULL_MONO])

  let SUBSPACE_SPAN ← prove
   r"!s. subspace(span s)"
   (GEN_TAC THEN REWRITE_TAC [span] THEN MATCH_MP_TAC P_HULL THEN
    SIMP_TAC [subspace, IN_INTERS])

  let NONEMPTY_SPAN ← prove
   r"!s:real^N->bool. ~(span s = {})"
   (SIMP_TAC [SUBSPACE_IMP_NONEMPTY, SUBSPACE_SPAN])

  let SPAN_CLAUSES ← prove
   r"(!a s. a IN s ==> a IN span s) /\
   (vec(0) IN span s) /\
   (!x y s. x IN span s /\ y IN span s ==> (x + y) IN span s) /\
   (!x c s. x IN span s ==> (c % x) IN span s)"
   (MESON_TAC [span, HULL_SUBSET, SUBSET, SUBSPACE_SPAN, subspace])

  let SPAN_INDUCT ← prove
   r"!s h. (!x. x IN s ==> x IN h) /\ subspace h ==> !x. x IN span(s) ==> h(x)"
   (REWRITE_TAC [span] THEN MESON_TAC [SUBSET, HULL_MINIMAL, IN])

  let SPAN_EMPTY ← prove
   r"span {} = {vec 0}"
   (REWRITE_TAC [span] THEN MATCH_MP_TAC HULL_UNIQUE THEN
    SIMP_TAC [subspace, SUBSET, IN_SING, NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC)

  let INDEPENDENT_EMPTY ← prove
   r"independent {}"
   (REWRITE_TAC [independent, dependent, NOT_IN_EMPTY])

  let INDEPENDENT_NONZERO ← prove
   r"!s. independent s ==> ~(vec 0 IN s)"
   (REWRITE_TAC [independent, dependent] THEN MESON_TAC [SPAN_CLAUSES])

  let INDEPENDENT_MONO ← prove
   r"!s t. independent t /\ s SUBSET t ==> independent s"
   (REWRITE_TAC [independent, dependent] THEN
    ASM_MESON_TAC [SPAN_MONO, SUBSET, IN_DELETE])

  let DEPENDENT_MONO ← prove
   r"!s t:real^N->bool. dependent s /\ s SUBSET t ==> dependent t"
   (ONCE_REWRITE_TAC [← TAUT (← q r"p /\ q ==> r <=> ~r /\ q ==> ~p")] THEN
    REWRITE_TAC [← GSYM independent, INDEPENDENT_MONO])

  let SPAN_SUBSPACE ← prove
   r"!b s. b SUBSET s /\ s SUBSET (span b) /\ subspace s ==> (span b = s)"
   (MESON_TAC [SUBSET_ANTISYM, span, HULL_MINIMAL])

  let SPAN_INDUCT_ALT ← prove
   r"!s h. h(vec 0) /\
         (!c x y. x IN s /\ h(y) ==> h(c % x + y))
          ==> !x:real^N. x IN span(s) ==> h(x)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (MP_TAC (← prove_inductive_relations_exist (concl th)))) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->bool") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"!x:real^N. x IN span(s) ==> g(x)")
     (fun th => ASM_MESON_TAC [th]) THEN
    MATCH_MP_TAC SPAN_INDUCT THEN REWRITE_TAC [subspace, IN_ELIM_THM] THEN
    REWRITE_TAC [IN, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    REPEAT CONJ_TAC THEN TRY (FIRST_X_ASSUM MATCH_MP_TAC) THEN
    REWRITE_TAC [VECTOR_ADD_LDISTRIB, VECTOR_MUL_ASSOC] THEN
    ASM_MESON_TAC [IN, VECTOR_ADD_LID, VECTOR_ADD_ASSOC, VECTOR_ADD_SYM,
                   VECTOR_MUL_LID, VECTOR_MUL_RZERO])

  return { subspace, span, dependent, independent, SUBSPACE_UNIV, SUBSPACE_IMP_NONEMPTY,
           SUBSPACE_0, SUBSPACE_ADD, SUBSPACE_MUL, SUBSPACE_MUL_EQ, SUBSPACE_NEG,
           SUBSPACE_NEG_EQ, SUBSPACE_SUB, SUBSPACE_VSUM, SUBSPACE_LINEAR_IMAGE,
           SUBSPACE_LINEAR_PREIMAGE, SUBSPACE_TRIVIAL, SUBSPACE_INTER, SUBSPACE_INTERS,
           LINEAR_INJECTIVE_0_SUBSPACE, SUBSPACE_UNION_CHAIN, SUBSPACE_PCROSS,
           SUBSPACE_PCROSS_EQ, SPAN_SPAN, SPAN_MONO, SUBSPACE_SPAN, NONEMPTY_SPAN,
           SPAN_CLAUSES, SPAN_INDUCT, SPAN_EMPTY, INDEPENDENT_EMPTY, INDEPENDENT_NONZERO,
           INDEPENDENT_MONO, DEPENDENT_MONO, SPAN_SUBSPACE, SPAN_INDUCT_ALT }

/- ------------------------------------------------------------------------- -/
/- Individual closure properties of span; mapping under linear image; the   -/
/- key breakdown property.  (vectors.ml 4826-5040)                           -/
/- ------------------------------------------------------------------------- -/

structure Span1 where
  SPAN_SUPERSET : thm
  SPAN_INC : thm
  SPAN_UNION_SUBSET : thm
  SPAN_UNIV : thm
  SPAN_0 : thm
  SPAN_ADD : thm
  SPAN_MUL : thm
  SPAN_MUL_EQ : thm
  SPAN_NEG : thm
  SPAN_NEG_EQ : thm
  SPAN_SUB : thm
  SPAN_VSUM : thm
  SPAN_ADD_EQ : thm
  SPAN_EQ_SELF : thm
  SPAN_OF_SUBSPACE : thm
  SPAN_SUBSET_SUBSPACE : thm
  SUBSPACE_TRANSLATION_SELF : thm
  SUBSPACE_TRANSLATION_SELF_EQ : thm
  SUBSPACE_SUMS : thm
  SPAN_UNION : thm
  SPAN_LINEAR_IMAGE : thm
  DEPENDENT_LINEAR_IMAGE_EQ : thm
  DEPENDENT_LINEAR_IMAGE : thm
  INDEPENDENT_LINEAR_IMAGE_EQ : thm
  SPAN_BREAKDOWN : thm
  SPAN_BREAKDOWN_EQ : thm
  SPAN_INSERT_0 : thm
  SPAN_SING : thm
  SPAN_2 : thm
  SPAN_3 : thm
  deriving Inhabited

@[nospecialize]
def setupSpan1 [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BSubspace : Subspace) : ExceptT String IO Span1 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, .. } := D
  let { EQ_TRANS, EXISTS_IN_IMAGE, EXISTS_REFL, EXTENSION, FORALL_IN_GSPEC,
        FORALL_IN_IMAGE, .. } := D.core1
  let { FUN_EQ_THM, FUN_IN_IMAGE, IMP_CONJ, IN_DELETE, IN_ELIM_THM, IN_IMAGE, IN_INSERT,
        IN_SING, IN_UNION, IN_UNIV, MONO_EXISTS, .. } := D.core2
  let { REAL_MUL_LINV, .. } := D.core3
  let { RIGHT_FORALL_IMP_THM, SUBSET, SUBSET_ANTISYM, SUBSET_REFL, SUBSET_UNION, .. } :=
    D.core4
  let { SURJECTIVE_IMAGE_EQ, .. } := D.core5
  let { HULL_UNION_SUBSET, .. } := D.misc
  let { VECTOR_ADD_LDISTRIB, VECTOR_ADD_LID, VECTOR_ADD_RID, VECTOR_ARITH,
        VECTOR_MUL_ASSOC, VECTOR_MUL_LID, VECTOR_MUL_RZERO, VECTOR_NEG_NEG,
        VECTOR_SUB_EQ, VECTOR_SUB_RZERO, .. } := BVectorArith
  let { SPAN_CLAUSES, SPAN_EMPTY, SPAN_INDUCT, SPAN_MONO, SPAN_SUBSPACE, SUBSPACE_0,
        SUBSPACE_ADD, SUBSPACE_LINEAR_IMAGE, SUBSPACE_LINEAR_PREIMAGE, SUBSPACE_MUL,
        SUBSPACE_NEG, SUBSPACE_SPAN, SUBSPACE_SUB, SUBSPACE_VSUM, dependent, independent,
        span, subspace, .. } := BSubspace
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let SPAN_SUPERSET ← prove
   r"!x. x IN s ==> x IN span s"
   (MESON_TAC [SPAN_CLAUSES])

  let SPAN_INC ← prove
   r"!s. s SUBSET span s"
   (REWRITE_TAC [SUBSET, SPAN_SUPERSET])

  let SPAN_UNION_SUBSET ← prove
   r"!s t. span s UNION span t SUBSET span(s UNION t)"
   (REWRITE_TAC [span, HULL_UNION_SUBSET])

  let SPAN_UNIV ← prove
   r"span(:real^N) = (:real^N)"
   (SIMP_TAC [SPAN_INC, ← SET_RULE (← q r"UNIV SUBSET s ==> s = UNIV")])

  let SPAN_0 ← prove
   r"vec(0) IN span s"
   (MESON_TAC [SUBSPACE_SPAN, SUBSPACE_0])

  let SPAN_ADD ← prove
   r"!x y s. x IN span s /\ y IN span s ==> (x + y) IN span s"
   (MESON_TAC [SUBSPACE_SPAN, SUBSPACE_ADD])

  let SPAN_MUL ← prove
   r"!x c s. x IN span s ==> (c % x) IN span s"
   (MESON_TAC [SUBSPACE_SPAN, SUBSPACE_MUL])

  let SPAN_MUL_EQ ← prove
   r"!x:real^N c s. ~(c = &0) ==> ((c % x) IN span s <=> x IN span s)"
   (REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN ASM_SIMP_TAC [SPAN_MUL] THEN
    SUBGOAL_THEN (← q r"(inv(c) % c % x:real^N) IN span s") MP_TAC THENL
     [ASM_SIMP_TAC [SPAN_MUL],
      ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, VECTOR_MUL_LID]])

  let SPAN_NEG ← prove
   r"!x s. x IN span s ==> (--x) IN span s"
   (MESON_TAC [SUBSPACE_SPAN, SUBSPACE_NEG])

  let SPAN_NEG_EQ ← prove
   r"!x s. --x IN span s <=> x IN span s"
   (MESON_TAC [SPAN_NEG, VECTOR_NEG_NEG])

  let SPAN_SUB ← prove
   r"!x y s. x IN span s /\ y IN span s ==> (x - y) IN span s"
   (MESON_TAC [SUBSPACE_SPAN, SUBSPACE_SUB])

  let SPAN_VSUM ← prove
   r"!s f t. FINITE t /\ (!x. x IN t ==> f(x) IN span(s))
           ==> (vsum t f) IN span(s)"
   (MESON_TAC [SUBSPACE_SPAN, SUBSPACE_VSUM])

  let SPAN_ADD_EQ ← prove
   r"!s x y. x IN span s ==> ((x + y) IN span s <=> y IN span s)"
   (MESON_TAC [SPAN_ADD, SPAN_SUB, ← va r"(x + y) - x:real^N = y"])

  let SPAN_EQ_SELF ← prove
   r"!s. span s = s <=> subspace s"
   (GEN_TAC THEN EQ_TAC THENL [MESON_TAC [SUBSPACE_SPAN], ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC SPAN_SUBSPACE THEN
    ASM_REWRITE_TAC [SUBSET_REFL, SPAN_INC])

  let SPAN_OF_SUBSPACE ← prove
   r"!s:real^N->bool. subspace s ==> span s = s"
   (REWRITE_TAC [SPAN_EQ_SELF])

  let SPAN_SUBSET_SUBSPACE ← prove
   r"!s t:real^N->bool. s SUBSET t /\ subspace t ==> span s SUBSET t"
   (MESON_TAC [SPAN_MONO, SPAN_EQ_SELF])

  let SUBSPACE_TRANSLATION_SELF ← prove
   r"!s a. subspace s /\ a IN s ==> IMAGE (\x. a + x) s = s"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (SUBST1_TAC (← SYM (← GEN_REWRITE_RULE id [← GSYM SPAN_EQ_SELF] th)))) THEN
    ASM_SIMP_TAC [SPAN_ADD_EQ, SPAN_CLAUSES] THEN
    REWRITE_TAC [← va r"a + x:real^N = y <=> x = y - a", EXISTS_REFL])

  let SUBSPACE_TRANSLATION_SELF_EQ ← prove
   r"!s a:real^N. subspace s ==> (IMAGE (\x. a + x) s = s <=> a IN s)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN
    ASM_SIMP_TAC [SUBSPACE_TRANSLATION_SELF] THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"\s. (a:real^N) IN s")) THEN
    REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"vec 0:real^N") THEN
    ASM_MESON_TAC [subspace, VECTOR_ADD_RID])

  let SUBSPACE_SUMS ← prove
   r"!s t. subspace s /\ subspace t
         ==> subspace {x + y | x IN s /\ y IN t}"
   (REWRITE_TAC [subspace, FORALL_IN_GSPEC, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC [VECTOR_ADD_LID],
      ONCE_REWRITE_TAC [← va
       r"(x + y) + (x' + y'):real^N = (x + x') + (y + y')"] THEN
      ASM_MESON_TAC [],
      REWRITE_TAC [VECTOR_ADD_LDISTRIB] THEN ASM_MESON_TAC []])

  let SPAN_UNION ← prove
   r"!s t. span(s UNION t) = {x + y:real^N | x IN span s /\ y IN span t}"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
      SIMP_TAC [SUBSPACE_SUMS, SUBSPACE_SPAN] THEN
      REWRITE_TAC [SUBSET, IN_UNION, IN_ELIM_THM] THEN
      X_GEN_TAC (← q r"x:real^N") THEN STRIP_TAC THENL
       [MAP_EVERY EXISTS_TAC [← q r"x:real^N", ← q r"vec 0:real^N"] THEN
        ASM_SIMP_TAC [SPAN_SUPERSET, SPAN_0, VECTOR_ADD_RID],
        MAP_EVERY EXISTS_TAC [← q r"vec 0:real^N", ← q r"x:real^N"] THEN
        ASM_SIMP_TAC [SPAN_SUPERSET, SPAN_0, VECTOR_ADD_LID]],
      REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_ADD THEN
      ASM_MESON_TAC [SPAN_MONO, SUBSET_UNION, SUBSET]])

  let SPAN_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N s. linear f ==> (span(IMAGE f s) = IMAGE f (span s))"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN
    X_GEN_TAC (← q r"x:real^N") THEN EQ_TAC THENL
     [SPEC_TAC (← q r"x:real^N", ← q r"x:real^N") THEN MATCH_MP_TAC SPAN_INDUCT THEN
      REWRITE_TAC [← SET_RULE (← q r"(\x. x IN s) = s")] THEN
      ASM_SIMP_TAC [SUBSPACE_SPAN, SUBSPACE_LINEAR_IMAGE] THEN
      REWRITE_TAC [FORALL_IN_IMAGE] THEN REWRITE_TAC [IN_IMAGE] THEN
      MESON_TAC [SPAN_SUPERSET, SUBSET],
      SPEC_TAC (← q r"x:real^N", ← q r"x:real^N") THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC SPAN_INDUCT THEN
      REWRITE_TAC [← SET_RULE (← q r"(\x. f x IN span(s)) = {x | f(x) IN span s}")] THEN
      ASM_SIMP_TAC [SUBSPACE_LINEAR_PREIMAGE, SUBSPACE_SPAN] THEN
      REWRITE_TAC [IN_ELIM_THM] THEN
      MESON_TAC [SPAN_SUPERSET, SUBSET, IN_IMAGE]])

  let DEPENDENT_LINEAR_IMAGE_EQ ← prove
   r"!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (dependent(IMAGE f s) <=> dependent s)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [dependent, EXISTS_IN_IMAGE] THEN
    AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"a:real^M") THEN
    ASM_CASES_TAC (← q r"(a:real^M) IN s") THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"(f:real^M->real^N) a IN span(IMAGE f (s DELETE a))") THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC [],
      ASM_SIMP_TAC [SPAN_LINEAR_IMAGE] THEN ASM SET_TAC []])

  let DEPENDENT_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N s.
        linear f /\ (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        dependent(s)
        ==> dependent(IMAGE f s)"
   (REPEAT GEN_TAC THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC [dependent, EXISTS_IN_IMAGE] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:real^M") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"IMAGE (f:real^M->real^N) s DELETE f a = IMAGE f (s DELETE a)")
     (fun th => ASM_SIMP_TAC [FUN_IN_IMAGE, SPAN_LINEAR_IMAGE, th]) THEN
    ASM SET_TAC [])

  let INDEPENDENT_LINEAR_IMAGE_EQ ← prove
   r"!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (independent(IMAGE f s) <=> independent s)"
   (REWRITE_TAC [independent, ← TAUT (← q r"(~p <=> ~q) <=> (p <=> q)")] THEN
    REWRITE_TAC [DEPENDENT_LINEAR_IMAGE_EQ])

  let SPAN_BREAKDOWN ← prove
   r"!b s a:real^N.
      b IN s /\ a IN span s ==> ?k. (a - k % b) IN span(s DELETE b)"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SPAN_INDUCT THEN
    REWRITE_TAC [subspace, IN_ELIM_THM] THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"a:real^N = b"), ALL_TAC] THEN
    ASM_MESON_TAC [SPAN_CLAUSES, IN_DELETE, ← va
     r"(a - &1 % a = vec 0) /\ (a - &0 % b = a) /\
    ((x + y) - (k1 + k2) % b = (x - k1 % b) + (y - k2 % b)) /\
    (c % x - (c * k) % y = c % (x - k % y))"])

  let SPAN_BREAKDOWN_EQ ← prove
   r"!a:real^N s. (x IN span(a INSERT s) <=> (?k. (x - k % a) IN span s))"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_THEN (fun th => tactic_of do
        pure (MP_TAC (← CONJ (← SET_RULE (← q r"(a:real^N) IN (a INSERT s)")) th))) THEN
      DISCH_THEN (MP_TAC o MATCH_MP SPAN_BREAKDOWN) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"k:real") THEN
      SPEC_TAC (← q r"x - k % a:real^N", ← q r"y:real^N") THEN
      REWRITE_TAC [← GSYM SUBSET] THEN MATCH_MP_TAC SPAN_MONO THEN SET_TAC [],
      DISCH_THEN (X_CHOOSE_TAC (← q r"k:real")) THEN
      SUBST1_TAC (← va r"x = (x - k % a) + k % a:real^N") THEN
      MATCH_MP_TAC SPAN_ADD THEN
      ASM_MESON_TAC [SPAN_MONO, SUBSET, IN_INSERT, SPAN_CLAUSES]])

  let SPAN_INSERT_0 ← prove
   r"!s. span(vec 0 INSERT s) = span s"
   (SIMP_TAC [EXTENSION, SPAN_BREAKDOWN_EQ, VECTOR_MUL_RZERO, VECTOR_SUB_RZERO])

  let SPAN_SING ← prove
   r"!a. span {a} = {u % a | u IN (:real)}"
   (REWRITE_TAC [EXTENSION, IN_ELIM_THM, SPAN_BREAKDOWN_EQ, SPAN_EMPTY] THEN
    REWRITE_TAC [IN_UNIV, IN_SING, VECTOR_SUB_EQ])

  let SPAN_2 ← prove
   r"!a b. span {a,b} = {u % a + v % b | u IN (:real) /\ v IN (:real)}"
   (REWRITE_TAC [EXTENSION, IN_ELIM_THM, SPAN_BREAKDOWN_EQ, SPAN_EMPTY] THEN
    REWRITE_TAC [IN_UNIV, IN_SING, VECTOR_SUB_EQ] THEN
    REWRITE_TAC [← va r"x - y:real^N = z <=> x = y + z"])

  let SPAN_3 ← prove
   r"!a b c. span {a,b,c} =
      {u % a + v % b + w % c | u IN (:real) /\ v IN (:real) /\ w IN (:real)}"
   (REWRITE_TAC [EXTENSION, IN_ELIM_THM, SPAN_BREAKDOWN_EQ, SPAN_EMPTY] THEN
    REWRITE_TAC [IN_UNIV, IN_SING, VECTOR_SUB_EQ] THEN
    REWRITE_TAC [← va r"x - y:real^N = z <=> x = y + z"])

  return { SPAN_SUPERSET, SPAN_INC, SPAN_UNION_SUBSET, SPAN_UNIV, SPAN_0, SPAN_ADD,
           SPAN_MUL, SPAN_MUL_EQ, SPAN_NEG, SPAN_NEG_EQ, SPAN_SUB, SPAN_VSUM, SPAN_ADD_EQ,
           SPAN_EQ_SELF, SPAN_OF_SUBSPACE, SPAN_SUBSET_SUBSPACE, SUBSPACE_TRANSLATION_SELF,
           SUBSPACE_TRANSLATION_SELF_EQ, SUBSPACE_SUMS, SPAN_UNION, SPAN_LINEAR_IMAGE,
           DEPENDENT_LINEAR_IMAGE_EQ, DEPENDENT_LINEAR_IMAGE, INDEPENDENT_LINEAR_IMAGE_EQ,
           SPAN_BREAKDOWN, SPAN_BREAKDOWN_EQ, SPAN_INSERT_0, SPAN_SING, SPAN_2, SPAN_3 }

/- ------------------------------------------------------------------------- -/
/- "Reversal" results; explicit expansion of span; standard bases.          -/
/- (vectors.ml 5045-5270)                                                     -/
/- ------------------------------------------------------------------------- -/

structure Span2 where
  IN_SPAN_INSERT : thm
  IN_SPAN_DELETE : thm
  EQ_SPAN_INSERT_EQ : thm
  SPAN_EXPLICIT : thm
  DEPENDENT_EXPLICIT : thm
  DEPENDENT_FINITE : thm
  SPAN_FINITE : thm
  SPAN_STDBASIS : thm
  HAS_SIZE_STDBASIS : thm
  FINITE_STDBASIS : thm
  CARD_STDBASIS : thm
  IN_SPAN_IMAGE_BASIS : thm
  INDEPENDENT_STDBASIS : thm
  INDEPENDENT_BASIS_IMAGE : thm
  deriving Inhabited

@[nospecialize]
def setupSpan2 [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith) (BVSum1 : VSum1)
    (BBasis : Basis) (BSubspace : Subspace) (BSpan1 : Span1) : ExceptT String IO Span2 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, SET_RULE, SET_TAC, REAL_RAT_REDUCE_CONV, .. } := D
  let { ARITH, CART_EQ, COND_RAND, COND_RATOR, DELETE_INSERT, DELETE_SUBSET,
        EMPTY_SUBSET, EXISTS_IN_IMAGE, EXTENSION, FINITE_DELETE, FINITE_IMAGE,
        FINITE_INSERT, FINITE_INTER, FINITE_NUMSEG, FINITE_RULES, FORALL_IN_IMAGE, .. } :=
    D.core1
  let { HAS_SIZE, HAS_SIZE_IMAGE_INJ, HAS_SIZE_NUMSEG_1, IMAGE_SUBSET, INSERT_SUBSET,
        IN_DELETE, IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_INTER, IN_NUMSEG, IN_UNIV,
        LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, NOT_IN_EMPTY, .. } := D.core2
  let { REAL_ADD_RID, REAL_MUL_LINV, REAL_MUL_RID, .. } := D.core3
  let { REAL_MUL_RZERO, REAL_MUL_SYM, REAL_OF_NUM_EQ, RIGHT_AND_EXISTS_THM,
        RIGHT_EXISTS_AND_THM, SIMPLE_IMAGE_GEN, SUBSET, SUBSET_ANTISYM, SUBSET_REFL,
        SUM_DELTA, .. } := D.core4
  let { numseg, o_DEF, real_div, .. } := D.core5
  let { VECTOR_ADD_COMPONENT, VECTOR_ARITH, VECTOR_ARITH_TAC, VECTOR_MUL_ASSOC,
        VECTOR_MUL_COMPONENT, VECTOR_MUL_LNEG, VECTOR_MUL_LZERO, VECTOR_MUL_RNEG,
        VECTOR_MUL_RZERO, VECTOR_SUB_LDISTRIB, VEC_COMPONENT, .. } := BVectorArith
  let { VSUM_CLAUSES, VSUM_COMPONENT, VSUM_DELETE, VSUM_EQ, VSUM_IMAGE, VSUM_LMUL,
        VSUM_NEG, VSUM_RESTRICT_SET, .. } := BVSum1
  let { BASIS_COMPONENT, BASIS_EQ_0, BASIS_EXPANSION, BASIS_INJ, DOT_BASIS, .. } := BBasis
  let { INDEPENDENT_MONO, INDEPENDENT_NONZERO, SPAN_CLAUSES, SPAN_INDUCT,
        SPAN_INDUCT_ALT, SPAN_MONO, dependent, independent, subspace, .. } := BSubspace
  let { SPAN_ADD, SPAN_BREAKDOWN, SPAN_BREAKDOWN_EQ, SPAN_MUL, SPAN_SUB, SPAN_SUPERSET,
        SPAN_VSUM, .. } := BSpan1
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let IN_SPAN_INSERT ← prove
   r"!a b:real^N s.
        a IN span(b INSERT s) /\ ~(a IN span s) ==> b IN span(a INSERT s)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"b:real^N", ← q r"(b:real^N) INSERT s", ← q r"a:real^N"]
      SPAN_BREAKDOWN) THEN ASM_REWRITE_TAC [IN_INSERT] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"k:real") MP_TAC) THEN
    ASM_CASES_TAC (← q r"k = &0") THEN
    ASM_REWRITE_TAC [← va r"a - &0 % b = a", DELETE_INSERT] THENL
     [ASM_MESON_TAC [SPAN_MONO, SUBSET, DELETE_SUBSET], ALL_TAC] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← SPEC (← q r"inv(k)") (← MATCH_MP SPAN_MUL th)))) THEN
    ASM_SIMP_TAC [VECTOR_SUB_LDISTRIB, VECTOR_MUL_ASSOC, REAL_MUL_LINV] THEN
    DISCH_TAC THEN SUBST1_TAC (← va
     r"b:real^N = inv(k) % a - (inv(k) % a - &1 % b)") THEN
    MATCH_MP_TAC SPAN_SUB THEN
    ASM_MESON_TAC [SPAN_CLAUSES, IN_INSERT, SUBSET, IN_DELETE, SPAN_MONO])

  let IN_SPAN_DELETE ← prove
   r"!a b s.
         a IN span s /\ ~(a IN span (s DELETE b))
         ==> b IN span (a INSERT (s DELETE b))"
   (ASM_MESON_TAC [IN_SPAN_INSERT, SPAN_MONO, SUBSET, IN_INSERT, IN_DELETE])

  let EQ_SPAN_INSERT_EQ ← prove
   r"!s x y:real^N. (x - y) IN span s ==> span(x INSERT s) = span(y INSERT s)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [SPAN_BREAKDOWN_EQ, EXTENSION] THEN
    ASM_MESON_TAC [SPAN_ADD, SPAN_SUB, SPAN_MUL,
                   ← va r"(z - k % y) - k % (x - y) = z - k % x",
                   ← va r"(z - k % x) + k % (x - y) = z - k % y"])

  let SPAN_EXPLICIT ← prove
   r"!(p:real^N -> bool).
        span p =
         {y | ?s u. FINITE s /\ s SUBSET p /\
                    vsum s (\v. u v % v) = y}"
   (GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC SPAN_VSUM THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [SPAN_SUPERSET, SPAN_MUL]] THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
    MATCH_MP_TAC SPAN_INDUCT_ALT THEN CONJ_TAC THENL
     [EXISTS_TAC (← q r"{}:real^N->bool") THEN
      REWRITE_TAC [FINITE_RULES, VSUM_CLAUSES, EMPTY_SUBSET, NOT_IN_EMPTY],
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q r"c:real", ← q r"x:real^N", ← q r"y:real^N"] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"s:real^N->bool", ← q r"u:real^N->real"] THEN
    STRIP_TAC THEN EXISTS_TAC (← q r"(x:real^N) INSERT s") THEN
    EXISTS_TAC (← q r"\y. if y = x then (if x IN s then (u:real^N->real) y + c else c)
                  else u y") THEN
    ASM_SIMP_TAC [FINITE_INSERT, IN_INSERT, VSUM_CLAUSES] THEN
    CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
     [FIRST_X_ASSUM (SUBST1_TAC o MATCH_MP (← SET_RULE (← q
       r"x IN s ==> s = x INSERT (s DELETE x)"))) THEN
      ASM_SIMP_TAC [VSUM_CLAUSES, FINITE_INSERT, FINITE_DELETE, IN_DELETE] THEN
      MATCH_MP_TAC (← va
        r"y = z ==> (c + d) % x + y = d % x + c % x + z"),
      AP_TERM_TAC] THEN
    MATCH_MP_TAC VSUM_EQ THEN ASM_MESON_TAC [IN_DELETE])

  let DEPENDENT_EXPLICIT ← prove
   r"!p. dependent (p:real^N -> bool) <=>
                ?s u. FINITE s /\ s SUBSET p /\
                      (?v. v IN s /\ ~(u v = &0)) /\
                      vsum s (\v. u v % v) = vec 0"
   (GEN_TAC THEN REWRITE_TAC [dependent, SPAN_EXPLICIT, IN_ELIM_THM] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM, LEFT_AND_EXISTS_THM] THEN
    EQ_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THENL
     [MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"s:real^N->bool", ← q r"u:real^N->real"] THEN
      STRIP_TAC THEN MAP_EVERY EXISTS_TAC
       [← q r"(a:real^N) INSERT s",
        ← q r"\y. if y = a then -- &1 else (u:real^N->real) y",
        ← q r"a:real^N"] THEN
      ASM_REWRITE_TAC [IN_INSERT, INSERT_SUBSET, FINITE_INSERT] THEN
      CONJ_TAC THENL [ASM SET_TAC [], CONV_TAC REAL_RAT_REDUCE_CONV] THEN
      ASM_SIMP_TAC [VSUM_CLAUSES] THEN
      COND_CASES_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      REWRITE_TAC [← va r"-- &1 % a + s = vec 0 <=> a = s"] THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        pure (GEN_REWRITE_TAC LAND_CONV [← SYM th])) THEN
      MATCH_MP_TAC VSUM_EQ THEN ASM SET_TAC [],
      MAP_EVERY X_GEN_TAC [← q r"s:real^N->bool", ← q r"u:real^N->real", ← q r"a:real^N"] THEN
      STRIP_TAC THEN MAP_EVERY EXISTS_TAC
       [← q r"a:real^N", ← q r"s DELETE (a:real^N)",
        ← q r"\i. --((u:real^N->real) i) / (u a)"] THEN
      ASM_SIMP_TAC [VSUM_DELETE, FINITE_DELETE] THEN
      REPEAT (CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN
      REWRITE_TAC [real_div] THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      ASM_REWRITE_TAC [VECTOR_MUL_LNEG, ← GSYM VECTOR_MUL_ASSOC, VSUM_LMUL,
                       VSUM_NEG, VECTOR_MUL_RNEG, VECTOR_MUL_RZERO] THEN
      ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV] THEN VECTOR_ARITH_TAC])

  let DEPENDENT_FINITE ← prove
   r"!s:real^N->bool.
        FINITE s
        ==> (dependent s <=> ?u. (?v. v IN s /\ ~(u v = &0)) /\
                                 vsum s (\v. u(v) % v) = vec 0)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [DEPENDENT_EXPLICIT] THEN EQ_TAC THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THENL
     [MAP_EVERY X_GEN_TAC [← q r"t:real^N->bool", ← q r"u:real^N->real"] THEN
      DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
      EXISTS_TAC (← q r"\v:real^N. if v IN t then u(v) else &0") THEN
      REWRITE_TAC [] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      ONCE_REWRITE_TAC [COND_RAND] THEN ONCE_REWRITE_TAC [COND_RATOR] THEN
      ASM_SIMP_TAC [VECTOR_MUL_LZERO, ← GSYM VSUM_RESTRICT_SET] THEN
      ASM_SIMP_TAC [← SET_RULE (← q r"t SUBSET s ==> {x | x IN s /\ x IN t} = t")],
      GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [← q r"s:real^N->bool", ← q r"u:real^N->real"] THEN
      ASM_REWRITE_TAC [SUBSET_REFL]])

  let SPAN_FINITE ← prove
   r"!s:real^N->bool.
        FINITE s ==> span s = {y | ?u. vsum s (\v. u v % v) = y}"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [SPAN_EXPLICIT, EXTENSION, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"y:real^N") THEN EQ_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THENL
     [MAP_EVERY X_GEN_TAC [← q r"t:real^N->bool", ← q r"u:real^N->real"] THEN
      STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
      EXISTS_TAC (← q r"\x:real^N. if x IN t then u(x) else &0") THEN
      REWRITE_TAC [COND_RAND, COND_RATOR, VECTOR_MUL_LZERO] THEN
      ASM_SIMP_TAC [← GSYM VSUM_RESTRICT_SET] THEN
      ASM_SIMP_TAC [← SET_RULE (← q r"t SUBSET s ==> {x | x IN s /\ x IN t} = t")],
      X_GEN_TAC (← q r"u:real^N->real") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      MAP_EVERY EXISTS_TAC [← q r"s:real^N->bool", ← q r"u:real^N->real"] THEN
      ASM_REWRITE_TAC [SUBSET_REFL]])

  let SPAN_STDBASIS ← prove
   r"span {basis i :real^N | 1 <= i /\ i <= dimindex(:N)} = UNIV"
   (REWRITE_TAC [EXTENSION, IN_UNIV] THEN X_GEN_TAC (← q r"x:real^N") THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM BASIS_EXPANSION] THEN
    MATCH_MP_TAC SPAN_VSUM THEN SIMP_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
    MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC [IN_ELIM_THM] THEN
    ASM_MESON_TAC [])

  let HAS_SIZE_STDBASIS ← prove
   r"{basis i :real^N | 1 <= i /\ i <= dimindex(:N)} HAS_SIZE
        dimindex(:N)"
   (ONCE_REWRITE_TAC [← SET_RULE (← q r"{f x | P x} = IMAGE f {x | P x}")] THEN
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    REWRITE_TAC [← GSYM numseg, HAS_SIZE_NUMSEG_1, IN_NUMSEG] THEN
    MESON_TAC [BASIS_INJ])

  let FINITE_STDBASIS ← prove
   r"FINITE {basis i :real^N | 1 <= i /\ i <= dimindex(:N)}"
   (MESON_TAC [HAS_SIZE_STDBASIS, HAS_SIZE])

  let CARD_STDBASIS ← prove
   r"CARD {basis i :real^N | 1 <= i /\ i <= dimindex(:N)} =
        dimindex(:N)"
   (MESON_TAC [HAS_SIZE_STDBASIS, HAS_SIZE])

  let IN_SPAN_IMAGE_BASIS ← prove
   r"!x:real^N s.
        x IN span(IMAGE basis s) <=>
          !i. 1 <= i /\ i <= dimindex(:N) /\ ~(i IN s) ==> x$i = &0"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [SPEC_TAC (← q r"x:real^N", ← q r"x:real^N") THEN MATCH_MP_TAC SPAN_INDUCT THEN
      SIMP_TAC [subspace, IN_ELIM_THM, VEC_COMPONENT, VECTOR_ADD_COMPONENT,
                VECTOR_MUL_COMPONENT, REAL_MUL_RZERO, REAL_ADD_RID] THEN
      SIMP_TAC [FORALL_IN_IMAGE, BASIS_COMPONENT] THEN MESON_TAC [],
      DISCH_TAC THEN REWRITE_TAC [SPAN_EXPLICIT, IN_ELIM_THM] THEN
      EXISTS_TAC (← q r"(IMAGE basis ((1..dimindex(:N)) INTER s)):real^N->bool") THEN
      SIMP_TAC [FINITE_IMAGE, FINITE_INTER, FINITE_NUMSEG] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM] THEN
      CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
      EXISTS_TAC (← q r"\v:real^N. x dot v") THEN
      W (MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhand o snd) THEN
      ANTS_TAC THENL
       [SIMP_TAC [FINITE_IMAGE, FINITE_INTER, FINITE_NUMSEG] THEN
        REWRITE_TAC [IN_INTER, IN_NUMSEG] THEN MESON_TAC [BASIS_INJ],
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC []] THEN
      REWRITE_TAC [o_DEF] THEN
      SIMP_TAC [CART_EQ, VSUM_COMPONENT, VECTOR_MUL_COMPONENT,
                BASIS_COMPONENT] THEN
      ONCE_REWRITE_TAC [COND_RAND] THEN
      ONCE_REWRITE_TAC [← MESON [] (← q
       r"(if x = y then p else q) = (if y = x then p else q)")] THEN
      SIMP_TAC [SUM_DELTA, REAL_MUL_RZERO, IN_INTER, IN_NUMSEG, DOT_BASIS] THEN
      ASM_MESON_TAC [REAL_MUL_RID]])

  let INDEPENDENT_STDBASIS ← prove
   r"independent {basis i :real^N | 1 <= i /\ i <= dimindex(:N)}"
   (REWRITE_TAC [independent, dependent] THEN
    ONCE_REWRITE_TAC [← SET_RULE (← q r"{f x | P x} = IMAGE f {x | P x}")] THEN
    REWRITE_TAC [EXISTS_IN_IMAGE] THEN REWRITE_TAC [IN_ELIM_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"k:num") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    SUBGOAL_THEN
     (← q r"IMAGE basis {i | 1 <= i /\ i <= dimindex(:N)} DELETE
           (basis k:real^N) =
    IMAGE basis ({i | 1 <= i /\ i <= dimindex(:N)} DELETE k)")
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_DELETE, IN_ELIM_THM] THEN
      GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [BASIS_INJ],
      ALL_TAC] THEN
    REWRITE_TAC [IN_SPAN_IMAGE_BASIS] THEN DISCH_THEN (MP_TAC o SPEC (← q r"k:num")) THEN
    ASM_SIMP_TAC [IN_DELETE, BASIS_COMPONENT, REAL_OF_NUM_EQ, ARITH])

  let INDEPENDENT_BASIS_IMAGE ← prove
   r"!k. independent(IMAGE basis k:real^N->bool) <=> k SUBSET 1..dimindex(:N) "
   (REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [FIRST_X_ASSUM (MP_TAC o MATCH_MP INDEPENDENT_NONZERO) THEN
      REWRITE_TAC [← SET_RULE (← q r"~(a IN IMAGE f s) <=> !x. x IN s ==> ~(f x = a)"),
                   BASIS_EQ_0, ← GSYM SUBSET],
      MATCH_MP_TAC INDEPENDENT_MONO THEN
      EXISTS_TAC (← q r"{basis i:real^N | 1 <= i /\ i <= dimindex(:N)}") THEN
      REWRITE_TAC [INDEPENDENT_STDBASIS] THEN
      ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      ASM_REWRITE_TAC [← GSYM numseg]])

  return { IN_SPAN_INSERT, IN_SPAN_DELETE, EQ_SPAN_INSERT_EQ, SPAN_EXPLICIT,
           DEPENDENT_EXPLICIT, DEPENDENT_FINITE, SPAN_FINITE, SPAN_STDBASIS,
           HAS_SIZE_STDBASIS, FINITE_STDBASIS, CARD_STDBASIS, IN_SPAN_IMAGE_BASIS,
           INDEPENDENT_STDBASIS, INDEPENDENT_BASIS_IMAGE }

/- ------------------------------------------------------------------------- -/
/- Definition of dimension, and setup of matroid for Euclidean span; some   -/
/- linear algebra basics, leaning on matroids.  (vectors.ml 5272-5478)       -/
/- ------------------------------------------------------------------------- -/

structure Dim1 where
  dim : thm
  euclidean_matroid : thm
  EUCLIDEAN_MATROID : thm
  EUCLIDEAN_MATROID_INDEPENDENT : thm
  EUCLIDEAN_MATROID_SPANNING : thm
  EUCLIDEAN_MATROID_SUBSPACE : thm
  EUCLIDEAN_MATROID_FINITE_DIMENSIONAL : thm
  EUCLIDEAN_MATROID_DIMENSION : thm
  EUCLIDEAN_MATROID_FINITE_DIM : thm
  EUCLIDEAN_SUBMATROID : thm
  EUCLIDEAN_MATROID_DIM : thm
  SPAN_EQ : thm
  SPAN_EQ_INSERT : thm
  INDEPENDENT_INSERT : thm
  SPAN_TRANS : thm
  SPANNING_SUBSET_INDEPENDENT : thm
  EXCHANGE_LEMMA : thm
  INDEPENDENT_SPAN_BOUND : thm
  INDEPENDENT_BOUND : thm
  DEPENDENT_BIGGERSET : thm
  INDEPENDENT_IMP_FINITE : thm
  MAXIMAL_INDEPENDENT_SUBSET_EXTEND : thm
  MAXIMAL_INDEPENDENT_SUBSET : thm
  BASIS_EXISTS : thm
  BASIS_EXISTS_FINITE : thm
  BASIS_SUBSPACE_EXISTS : thm
  INDEPENDENT_CARD_LE_DIM : thm
  SPAN_CARD_GE_DIM : thm
  BASIS_CARD_EQ_DIM : thm
  BASIS_HAS_SIZE_DIM : thm
  deriving Inhabited

@[nospecialize]
def setupDim1 [HolBase] (D : VectorsDeps) (BSubspace : Subspace) (BSpan1 : Span1)
    (BSpan2 : Span2) : ExceptT String IO Dim1 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SELECT_CONV, new_definition, .. } := D
  let { CARD_SUBSET, EMPTY_SUBSET, FINITE_SUBSET, .. } := D.core1
  let { FUN_EQ_THM, GT, HAS_SIZE, IN_ELIM_THM, IN_UNIV, LEFT_IMP_EXISTS_THM, LE_ANTISYM,
        MONO_EXISTS, MONO_FORALL, NOT_LE, .. } := D.core2
  let { PAIR_EQ, .. } := D.core3
  let { SUBSET_ANTISYM_EQ, SUBSET_REFL, SUBSET_TRANS, SUBSET_UNIV, .. } := D.core4
  let { MATROID_BASIS_SUBMATROID, MATROID_DIMENSION_UNIQUE, MATROID_DIM_ALT,
        MATROID_FINITE_DIMENSIONAL, MATROID_FINITE_DIMENSIONAL_DIM,
        MATROID_INDEPENDENT_INSERT, MATROID_INDEPENDENT_SUBMATROID,
        MATROID_INTERMEDIATE_BASIS, MATROID_SPANNING_SUBMATROID,
        MATROID_SPANNING_SUBSET_INDEPENDENT, MATROID_SPAN_EQ, MATROID_SPAN_INSERT_EQ,
        MATROID_STEINITZ_EXCHANGE_FINITE, SUBMATROID_SUBSET, matroid_basis,
        matroid_independent, matroid_set, matroid_span, matroid_spanning,
        matroid_subspace, matroid_tybij, .. } := D.lib
  let { INDEPENDENT_EMPTY, SPAN_MONO, SPAN_SPAN, dependent, independent, .. } := BSubspace
  let { SPAN_EQ_SELF, SPAN_INC, .. } := BSpan1
  let { CARD_STDBASIS, FINITE_STDBASIS, HAS_SIZE_STDBASIS, INDEPENDENT_STDBASIS,
        IN_SPAN_INSERT, SPAN_EXPLICIT, SPAN_FINITE, SPAN_STDBASIS, .. } := BSpan2
  -- @@SCOPE END

  let dim ← new_definition
   r"dim (v:real^N->bool) =
   @n. ?b. b SUBSET v /\ independent b /\ v SUBSET (span b) /\ b HAS_SIZE n"

  let euclidean_matroid ← new_definition
   r"euclidean_matroid = matroid((:real^N),span)"

  let EUCLIDEAN_MATROID ← prove
   r"matroid_set euclidean_matroid = (:real^N) /\
   matroid_span euclidean_matroid = (span:(real^N->bool)->(real^N->bool))"
   (ONCE_REWRITE_TAC [matroid_set, matroid_span] THEN
    REWRITE_TAC [← GSYM PAIR_EQ, euclidean_matroid] THEN
    REWRITE_TAC [← GSYM (← CONJUNCT2 matroid_tybij)] THEN
    REWRITE_TAC [SUBSET_UNIV, IN_UNIV] THEN
    REWRITE_TAC [SPAN_INC, SPAN_MONO, SPAN_SPAN, IN_SPAN_INSERT] THEN
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SPAN_EXPLICIT] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    SIMP_TAC [SPAN_FINITE, LEFT_IMP_EXISTS_THM, IN_ELIM_THM] THEN
    MESON_TAC [])

  let EUCLIDEAN_MATROID_INDEPENDENT ← prove
   r"matroid_independent (euclidean_matroid:(real^N)matroid) = independent"
   (SIMP_TAC [independent, dependent, matroid_independent, FUN_EQ_THM] THEN
    REWRITE_TAC [EUCLIDEAN_MATROID, SUBSET_UNIV] THEN MESON_TAC [])

  let EUCLIDEAN_MATROID_SPANNING ← prove
   r"!s. matroid_spanning euclidean_matroid s <=> span s = (:real^N)"
   (REWRITE_TAC [matroid_spanning, EUCLIDEAN_MATROID, SUBSET_UNIV])

  let EUCLIDEAN_MATROID_SUBSPACE ← prove
   r"matroid_subspace (euclidean_matroid:(real^N)matroid) = subspace"
   (GEN_REWRITE_TAC id [FUN_EQ_THM] THEN
    REWRITE_TAC [matroid_subspace, EUCLIDEAN_MATROID, SUBSET_UNIV] THEN
    REWRITE_TAC [SPAN_EQ_SELF])

  let EUCLIDEAN_MATROID_FINITE_DIMENSIONAL ← prove
   r"matroid_finite_dimensional (euclidean_matroid:(real^N)matroid)"
   (REWRITE_TAC [MATROID_FINITE_DIMENSIONAL, EUCLIDEAN_MATROID] THEN
    EXISTS_TAC (← q r"{basis i :real^N | 1 <= i /\ i <= dimindex(:N)}") THEN
    REWRITE_TAC [SPAN_STDBASIS, SUBSET_UNIV, FINITE_STDBASIS])

  let EUCLIDEAN_MATROID_DIMENSION ← prove
   r"matroid_dimension (euclidean_matroid:(real^N)matroid) = dimindex(:N)"
   (MATCH_MP_TAC MATROID_DIMENSION_UNIQUE THEN
    EXISTS_TAC (← q r"{basis i :real^N | 1 <= i /\ i <= dimindex(:N)}") THEN
    REWRITE_TAC [matroid_basis, EUCLIDEAN_MATROID_INDEPENDENT, SPAN_STDBASIS,
      EUCLIDEAN_MATROID_SPANNING, INDEPENDENT_STDBASIS, HAS_SIZE_STDBASIS])

  let EUCLIDEAN_MATROID_FINITE_DIM ← prove
   r"!s:real^N->bool. matroid_finite_dim euclidean_matroid s"
   (GEN_TAC THEN MATCH_MP_TAC MATROID_FINITE_DIMENSIONAL_DIM THEN
    REWRITE_TAC [EUCLIDEAN_MATROID_FINITE_DIMENSIONAL] THEN
    REWRITE_TAC [EUCLIDEAN_MATROID, SUBSET_UNIV])

  let EUCLIDEAN_SUBMATROID ← prove
   r"(!s:real^N->bool. matroid_set (submatroid euclidean_matroid s) = span s) /\
   (!s:real^N->bool. matroid_span (submatroid euclidean_matroid s) = span)"
   (SIMP_TAC [SUBMATROID_SUBSET, EUCLIDEAN_MATROID, SUBSET_UNIV])

  let EUCLIDEAN_MATROID_DIM ← prove
   r"matroid_dim (euclidean_matroid:(real^N)matroid) = dim"
   (REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"s:real^N->bool") THEN
    REWRITE_TAC [dim] THEN
    SIMP_TAC [MATROID_DIM_ALT, EUCLIDEAN_MATROID, SUBSET_UNIV] THEN
    REWRITE_TAC [EUCLIDEAN_MATROID_INDEPENDENT])

  let SPAN_EQ ← prove
   r"!s t:real^N->bool. span s = span t <=> s SUBSET span t /\ t SUBSET span s"
   (REPEAT GEN_TAC THEN MP_TAC (← ISPECL
     [← q r"euclidean_matroid:(real^N)matroid", ← q r"s:real^N->bool", ← q r"t:real^N->bool"]
      MATROID_SPAN_EQ) THEN
    REWRITE_TAC [EUCLIDEAN_MATROID, IN_UNIV, SUBSET_UNIV])

  let SPAN_EQ_INSERT ← prove
   r"!s x:real^N. span(x INSERT s) = span s <=> x IN span s"
   (REPEAT GEN_TAC THEN MP_TAC (← ISPECL
     [← q r"euclidean_matroid:(real^N)matroid", ← q r"s:real^N->bool", ← q r"x:real^N"]
      MATROID_SPAN_INSERT_EQ) THEN
    REWRITE_TAC [EUCLIDEAN_MATROID, IN_UNIV, SUBSET_UNIV])

  let INDEPENDENT_INSERT ← prove
   r"!a:real^N s. independent(a INSERT s) <=>
                  if a IN s then independent s
                  else independent s /\ ~(a IN span s)"
   (MESON_TAC [EUCLIDEAN_MATROID, EUCLIDEAN_MATROID_INDEPENDENT,
               MATROID_INDEPENDENT_INSERT, IN_UNIV])

  let SPAN_TRANS ← prove
   r"!x y:real^N s. x IN span(s) /\ y IN span(x INSERT s) ==> y IN span(s)"
   (REWRITE_TAC [← GSYM EUCLIDEAN_MATROID] THEN
    MESON_TAC [MATROID_SPAN_INSERT_EQ, EUCLIDEAN_MATROID, IN_UNIV, SUBSET_UNIV])

  let SPANNING_SUBSET_INDEPENDENT ← prove
   r"!s t:real^N->bool.
        t SUBSET s /\ independent s /\ s SUBSET span(t) ==> s = t"
   (MP_TAC (← ISPEC (← q r"euclidean_matroid:(real^N)matroid")
      MATROID_SPANNING_SUBSET_INDEPENDENT) THEN
    REWRITE_TAC [EUCLIDEAN_MATROID, EUCLIDEAN_MATROID_INDEPENDENT])

  let EXCHANGE_LEMMA ← prove
   r"!s t:real^N->bool.
        FINITE t /\ independent s /\ s SUBSET span t
        ==> ?t'. t' HAS_SIZE (CARD t) /\
                 s SUBSET t' /\ t' SUBSET (s UNION t) /\ s SUBSET (span t')"
   (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL
     [← q r"euclidean_matroid:(real^N)matroid", ← q r"s:real^N->bool", ← q r"t:real^N->bool"]
     MATROID_STEINITZ_EXCHANGE_FINITE) THEN
    ASM_REWRITE_TAC [EUCLIDEAN_MATROID, EUCLIDEAN_MATROID_INDEPENDENT] THEN
    REWRITE_TAC [SUBSET_UNIV] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC [])

  let INDEPENDENT_SPAN_BOUND ← prove
   r"!s t. FINITE t /\ independent s /\ s SUBSET span(t)
         ==> FINITE s /\ CARD(s) <= CARD(t)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP EXCHANGE_LEMMA) THEN
    ASM_MESON_TAC [HAS_SIZE, CARD_SUBSET, FINITE_SUBSET])

  let INDEPENDENT_BOUND ← prove
   r"!s:real^N->bool.
        independent s ==> FINITE s /\ CARD(s) <= dimindex(:N)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC [← GSYM CARD_STDBASIS] THEN
    MATCH_MP_TAC INDEPENDENT_SPAN_BOUND THEN
    ASM_REWRITE_TAC [FINITE_STDBASIS, SPAN_STDBASIS, SUBSET_UNIV])

  let DEPENDENT_BIGGERSET ← prove
   r"!s:real^N->bool. (FINITE s ==> CARD(s) > dimindex(:N)) ==> dependent s"
   (MP_TAC INDEPENDENT_BOUND THEN MATCH_MP_TAC MONO_FORALL THEN
    REWRITE_TAC [GT, ← GSYM NOT_LE, independent] THEN MESON_TAC [])

  let INDEPENDENT_IMP_FINITE ← prove
   r"!s:real^N->bool. independent s ==> FINITE s"
   (SIMP_TAC [INDEPENDENT_BOUND])

  let MAXIMAL_INDEPENDENT_SUBSET_EXTEND ← prove
   r"!s v:real^N->bool.
        s SUBSET v /\ independent s
        ==> ?b. s SUBSET b /\ b SUBSET v /\ independent b /\
                v SUBSET (span b)"
   (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL
     [← q r"submatroid euclidean_matroid (v:real^N->bool)",
      ← q r"s:real^N->bool", ← q r"v:real^N->bool"] MATROID_INTERMEDIATE_BASIS) THEN
    ASM_SIMP_TAC [MATROID_INDEPENDENT_SUBMATROID, EUCLIDEAN_MATROID, SUBSET_UNIV,
                  MATROID_SPANNING_SUBMATROID, EUCLIDEAN_MATROID_INDEPENDENT,
                  MATROID_BASIS_SUBMATROID,
                  ← SET_RULE (← q r"s SUBSET v ==> s UNION v = v")] THEN
    ASM_MESON_TAC [SPAN_INC, SUBSET_TRANS])

  let MAXIMAL_INDEPENDENT_SUBSET ← prove
   r"!v:real^N->bool. ?b. b SUBSET v /\ independent b /\ v SUBSET (span b)"
   (MP_TAC (← SPEC (← q r"EMPTY:real^N->bool") MAXIMAL_INDEPENDENT_SUBSET_EXTEND) THEN
    REWRITE_TAC [EMPTY_SUBSET, INDEPENDENT_EMPTY])

  let BASIS_EXISTS ← prove
   r"!v. ?b. b SUBSET v /\ independent b /\ v SUBSET (span b) /\
           b HAS_SIZE (dim v)"
   (GEN_TAC THEN REWRITE_TAC [dim] THEN CONV_TAC SELECT_CONV THEN
    MESON_TAC [MAXIMAL_INDEPENDENT_SUBSET, HAS_SIZE, INDEPENDENT_BOUND])

  let BASIS_EXISTS_FINITE ← prove
   r"!v. ?b. FINITE b /\
           b SUBSET v /\
           independent b /\
           v SUBSET (span b) /\
           b HAS_SIZE (dim v)"
   (MESON_TAC [BASIS_EXISTS, INDEPENDENT_IMP_FINITE])

  let BASIS_SUBSPACE_EXISTS ← prove
   r"!s:real^N->bool.
        subspace s
        ==> ?b. FINITE b /\
                b SUBSET s /\
                independent b /\
                span b = s /\
                b HAS_SIZE dim s"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"s:real^N->bool") BASIS_EXISTS) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN
    ASM_MESON_TAC [SPAN_EQ_SELF, SPAN_MONO, INDEPENDENT_IMP_FINITE])

  let INDEPENDENT_CARD_LE_DIM ← prove
   r"!v b:real^N->bool.
        b SUBSET v /\ independent b ==> FINITE b /\ CARD(b) <= dim v"
   (MESON_TAC [BASIS_EXISTS, INDEPENDENT_SPAN_BOUND, HAS_SIZE, SUBSET_TRANS])

  let SPAN_CARD_GE_DIM ← prove
   r"!v b:real^N->bool.
        v SUBSET (span b) /\ FINITE b ==> dim(v) <= CARD(b)"
   (MESON_TAC [BASIS_EXISTS, INDEPENDENT_SPAN_BOUND, HAS_SIZE, SUBSET_TRANS])

  let BASIS_CARD_EQ_DIM ← prove
   r"!v b. b SUBSET v /\ v SUBSET (span b) /\ independent b
         ==> FINITE b /\ (CARD b = dim v)"
   (MESON_TAC [LE_ANTISYM, INDEPENDENT_CARD_LE_DIM, SPAN_CARD_GE_DIM])

  let BASIS_HAS_SIZE_DIM ← prove
   r"!v b. independent b /\ span b = v ==> b HAS_SIZE (dim v)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [HAS_SIZE] THEN
    MATCH_MP_TAC BASIS_CARD_EQ_DIM THEN ASM_REWRITE_TAC [SUBSET_REFL] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [SPAN_INC])

  return { dim, euclidean_matroid, EUCLIDEAN_MATROID, EUCLIDEAN_MATROID_INDEPENDENT,
           EUCLIDEAN_MATROID_SPANNING, EUCLIDEAN_MATROID_SUBSPACE,
           EUCLIDEAN_MATROID_FINITE_DIMENSIONAL, EUCLIDEAN_MATROID_DIMENSION,
           EUCLIDEAN_MATROID_FINITE_DIM, EUCLIDEAN_SUBMATROID, EUCLIDEAN_MATROID_DIM,
           SPAN_EQ, SPAN_EQ_INSERT, INDEPENDENT_INSERT, SPAN_TRANS,
           SPANNING_SUBSET_INDEPENDENT, EXCHANGE_LEMMA, INDEPENDENT_SPAN_BOUND,
           INDEPENDENT_BOUND, DEPENDENT_BIGGERSET, INDEPENDENT_IMP_FINITE,
           MAXIMAL_INDEPENDENT_SUBSET_EXTEND, MAXIMAL_INDEPENDENT_SUBSET, BASIS_EXISTS,
           BASIS_EXISTS_FINITE, BASIS_SUBSPACE_EXISTS, INDEPENDENT_CARD_LE_DIM,
           SPAN_CARD_GE_DIM, BASIS_CARD_EQ_DIM, BASIS_HAS_SIZE_DIM }

/- ------------------------------------------------------------------------- -/
/- Dimension, continued.  (vectors.ml 5479-5672)                             -/
/- ------------------------------------------------------------------------- -/

structure Dim2 where
  DIM_SPAN : thm
  DIM_UNIQUE : thm
  DIM_LE_CARD : thm
  DIM_UNIV : thm
  DIM_SUBSET : thm
  DIM_SUBSET_UNIV : thm
  BASIS_HAS_SIZE_UNIV : thm
  CARD_GE_DIM_INDEPENDENT : thm
  CARD_LE_DIM_SPANNING : thm
  CARD_EQ_DIM : thm
  INDEPENDENT_BOUND_GENERAL : thm
  DEPENDENT_BIGGERSET_GENERAL : thm
  DIM_INSERT_0 : thm
  DIM_EQ_CARD : thm
  DEPENDENT_EQ_DIM_LT_CARD : thm
  INDEPENDENT_EQ_DIM_EQ_CARD : thm
  SUBSET_LE_DIM : thm
  SPAN_EQ_DIM : thm
  DIM_EMPTY : thm
  DIM_INSERT : thm
  CHOOSE_SUBSPACE_OF_SUBSPACE : thm
  SUBSPACE_EXISTS : thm
  DIM_EQ_SPAN : thm
  DIM_EQ_FULL : thm
  DIM_PSUBSET : thm
  LOWDIM_EXPAND_DIMENSION : thm
  LOWDIM_EXPAND_BASIS : thm
  deriving Inhabited

@[nospecialize]
def setupDim2 [HolBase] (D : VectorsDeps) (BSubspace : Subspace) (BSpan1 : Span1)
    (BSpan2 : Span2) (BDim1 : Dim1) : ExceptT String IO Dim2 := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, .. } := D
  let { CONTRAPOS_THM, EQ_IMP_LE, .. } := D.core1
  let { GT, HAS_SIZE, IN_UNIV, LE_ANTISYM, LE_REFL, LE_TRANS, LT_LE, LT_REFL,
        MONO_FORALL, NOT_IMP, NOT_LE, .. } := D.core2
  let { PSUBSET, .. } := D.core3
  let { SUBSET, SUBSET_REFL, SUBSET_UNIV, .. } := D.core4
  let { MATROID_CHOOSE_SUBSPACE, MATROID_DIM_EMPTY, MATROID_DIM_EQ_SPAN,
        MATROID_DIM_GE_FINITE_CARD_EQ, MATROID_DIM_INSERT, MATROID_DIM_SPAN,
        MATROID_DIM_SPAN_EQ_GEN, MATROID_LOWDIM_EXPAND_BASIS,
        MATROID_LOWDIM_EXPAND_DIMENSION, .. } := D.lib
  let { SPAN_MONO, SPAN_SPAN, independent, .. } := BSubspace
  let { SPAN_INC, SPAN_INSERT_0, SPAN_UNIV, .. } := BSpan1
  let { HAS_SIZE_STDBASIS, INDEPENDENT_STDBASIS, SPAN_STDBASIS, .. } := BSpan2
  let { BASIS_CARD_EQ_DIM, BASIS_EXISTS, BASIS_HAS_SIZE_DIM, EUCLIDEAN_MATROID,
        EUCLIDEAN_MATROID_DIM, EUCLIDEAN_MATROID_DIMENSION, EUCLIDEAN_MATROID_FINITE_DIM,
        EUCLIDEAN_MATROID_INDEPENDENT, EUCLIDEAN_MATROID_SUBSPACE, INDEPENDENT_BOUND,
        INDEPENDENT_CARD_LE_DIM, INDEPENDENT_IMP_FINITE, INDEPENDENT_SPAN_BOUND,
        SPAN_CARD_GE_DIM, .. } := BDim1
  -- @@SCOPE END

  let DIM_SPAN ← prove
   r"!s:real^N->bool. dim(span s) = dim s"
   (GEN_TAC THEN MP_TAC (← ISPECL
     [← q r"euclidean_matroid:(real^N)matroid", ← q r"s:real^N->bool"]
     MATROID_DIM_SPAN) THEN
    SIMP_TAC [EUCLIDEAN_MATROID_DIM, EUCLIDEAN_MATROID, SUBSET_UNIV])

  let DIM_UNIQUE ← prove
   r"!v b. b SUBSET v /\ v SUBSET (span b) /\ independent b /\ b HAS_SIZE n
         ==> dim v = n"
   (MESON_TAC [BASIS_CARD_EQ_DIM, HAS_SIZE])

  let DIM_LE_CARD ← prove
   r"!s. FINITE s ==> dim s <= CARD s"
   (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SPAN_CARD_GE_DIM THEN
    ASM_REWRITE_TAC [SPAN_INC, SUBSET_REFL])

  let DIM_UNIV ← prove
   r"dim(:real^N) = dimindex(:N)"
   (MATCH_MP_TAC DIM_UNIQUE THEN
    EXISTS_TAC (← q r"{basis i :real^N | 1 <= i /\ i <= dimindex(:N)}") THEN
    REWRITE_TAC [SUBSET_UNIV, SPAN_STDBASIS, HAS_SIZE_STDBASIS,
                 INDEPENDENT_STDBASIS])

  let DIM_SUBSET ← prove
   r"!s t:real^N->bool. s SUBSET t ==> dim(s) <= dim(t)"
   (MESON_TAC [BASIS_EXISTS, INDEPENDENT_SPAN_BOUND, SUBSET, HAS_SIZE])

  let DIM_SUBSET_UNIV ← prove
   r"!s:real^N->bool. dim(s) <= dimindex(:N)"
   (GEN_TAC THEN REWRITE_TAC [← GSYM DIM_UNIV] THEN
    MATCH_MP_TAC DIM_SUBSET THEN REWRITE_TAC [SUBSET_UNIV])

  let BASIS_HAS_SIZE_UNIV ← prove
   r"!b. independent b /\ span b = (:real^N) ==> b HAS_SIZE (dimindex(:N))"
   (REWRITE_TAC [← GSYM DIM_UNIV, BASIS_HAS_SIZE_DIM])

  let CARD_GE_DIM_INDEPENDENT ← prove
   r"!v b:real^N->bool.
        b SUBSET v /\ independent b /\ dim v <= CARD(b)
        ==> v SUBSET span b"
   (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL
     [← q r"euclidean_matroid:(real^N)matroid", ← q r"b:real^N->bool", ← q r"v:real^N->bool"]
     MATROID_DIM_SPAN_EQ_GEN) THEN
    MP_TAC (← ISPECL [← q r"euclidean_matroid:(real^N)matroid", ← q r"b:real^N->bool"]
          MATROID_DIM_GE_FINITE_CARD_EQ) THEN
    ASM_REWRITE_TAC [EUCLIDEAN_MATROID, EUCLIDEAN_MATROID_DIM, SUBSET_UNIV,
      EUCLIDEAN_MATROID_FINITE_DIM, EUCLIDEAN_MATROID_INDEPENDENT] THEN
    ASM_MESON_TAC [SPAN_INC, LE_TRANS, SPAN_MONO])

  let CARD_LE_DIM_SPANNING ← prove
   r"!v b:real^N->bool.
        v SUBSET span b /\ FINITE b /\ CARD(b) <= dim v ==> independent b"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"euclidean_matroid:(real^N)matroid", ← q r"b:real^N->bool"]
          MATROID_DIM_GE_FINITE_CARD_EQ) THEN
    REWRITE_TAC [EUCLIDEAN_MATROID, EUCLIDEAN_MATROID_DIM, SUBSET_UNIV,
                 EUCLIDEAN_MATROID_INDEPENDENT, EUCLIDEAN_MATROID_FINITE_DIM] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    ASM_MESON_TAC [DIM_SPAN, SPAN_SPAN, DIM_SUBSET, LE_TRANS])

  let CARD_EQ_DIM ← prove
   r"!v b. b SUBSET v /\ b HAS_SIZE (dim v)
         ==> (independent b <=> v SUBSET (span b))"
   (REWRITE_TAC [HAS_SIZE, ← GSYM LE_ANTISYM] THEN
    MESON_TAC [CARD_LE_DIM_SPANNING, CARD_GE_DIM_INDEPENDENT])

  let INDEPENDENT_BOUND_GENERAL ← prove
   r"!s:real^N->bool. independent s ==> FINITE s /\ CARD(s) <= dim(s)"
   (MESON_TAC [INDEPENDENT_CARD_LE_DIM, INDEPENDENT_BOUND, SUBSET_REFL])

  let DEPENDENT_BIGGERSET_GENERAL ← prove
   r"!s:real^N->bool. (FINITE s ==> CARD(s) > dim(s)) ==> dependent s"
   (MP_TAC INDEPENDENT_BOUND_GENERAL THEN MATCH_MP_TAC MONO_FORALL THEN
    REWRITE_TAC [GT, ← GSYM NOT_LE, independent] THEN MESON_TAC [])

  let DIM_INSERT_0 ← prove
   r"!s:real^N->bool. dim(vec 0 INSERT s) = dim s"
   (ONCE_REWRITE_TAC [← GSYM DIM_SPAN] THEN
    REWRITE_TAC [SPAN_INSERT_0])

  let DIM_EQ_CARD ← prove
   r"!s:real^N->bool. independent s ==> dim s = CARD s"
   (REPEAT STRIP_TAC THEN MP_TAC
     (← ISPECL [← q r"span s:real^N->bool", ← q r"s:real^N->bool"] BASIS_CARD_EQ_DIM) THEN
    ASM_SIMP_TAC [SUBSET_REFL, SPAN_INC, DIM_SPAN])

  let DEPENDENT_EQ_DIM_LT_CARD ← prove
   r"!s:real^N->bool. dependent s <=> FINITE s ==> dim s < CARD s"
   (GEN_TAC THEN EQ_TAC THEN
    REWRITE_TAC [← GSYM GT, DEPENDENT_BIGGERSET_GENERAL] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [← GSYM independent, NOT_IMP] THEN
    STRIP_TAC THEN MATCH_MP_TAC CARD_LE_DIM_SPANNING THEN
    EXISTS_TAC (← q r"s:real^N->bool") THEN ASM_REWRITE_TAC [SPAN_INC] THEN
    ASM_ARITH_TAC)

  let INDEPENDENT_EQ_DIM_EQ_CARD ← prove
   r"!s:real^N->bool. independent s <=> FINITE s /\ dim s = CARD s"
   (GEN_TAC THEN EQ_TAC THEN
    SIMP_TAC [DIM_EQ_CARD, INDEPENDENT_IMP_FINITE] THEN
    SIMP_TAC [DEPENDENT_EQ_DIM_LT_CARD, independent, LT_REFL])

  let SUBSET_LE_DIM ← prove
   r"!s t:real^N->bool. s SUBSET (span t) ==> dim s <= dim t"
   (MESON_TAC [DIM_SPAN, DIM_SUBSET])

  let SPAN_EQ_DIM ← prove
   r"!s t. span s = span t ==> dim s = dim t"
   (MESON_TAC [DIM_SPAN])

  let DIM_EMPTY ← prove
   r"dim({}:real^N->bool) = 0"
   (REWRITE_TAC [← GSYM EUCLIDEAN_MATROID_DIM, MATROID_DIM_EMPTY])

  let DIM_INSERT ← prove
   r"!x:real^N s. dim(x INSERT s) = if x IN span s then dim s else dim s + 1"
   (REWRITE_TAC [← GSYM EUCLIDEAN_MATROID_DIM] THEN
    SIMP_TAC [MATROID_DIM_INSERT, EUCLIDEAN_MATROID_FINITE_DIM, EUCLIDEAN_MATROID,
              IN_UNIV])

  let CHOOSE_SUBSPACE_OF_SUBSPACE ← prove
   r"!s:real^N->bool n.
        n <= dim s ==> ?t. subspace t /\ t SUBSET span s /\ dim t = n"
   (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL
     [← q r"euclidean_matroid:(real^N)matroid", ← q r"s:real^N->bool", ← q r"n:num"]
     MATROID_CHOOSE_SUBSPACE) THEN
    ASM_REWRITE_TAC [EUCLIDEAN_MATROID, SUBSET_UNIV, EUCLIDEAN_MATROID_DIM,
                     EUCLIDEAN_MATROID_SUBSPACE] THEN
    MESON_TAC [])

  let SUBSPACE_EXISTS ← prove
   r"!n. n <= dimindex(:N) ==> ?s:real^N->bool. subspace s /\ dim s = n"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM DIM_UNIV] THEN
    DISCH_THEN (MP_TAC o MATCH_MP CHOOSE_SUBSPACE_OF_SUBSPACE) THEN
    MESON_TAC [])

  let DIM_EQ_SPAN ← prove
   r"!s t:real^N->bool. s SUBSET t /\ dim t <= dim s ==> span s = span t"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL
     [← q r"euclidean_matroid:(real^N)matroid", ← q r"s:real^N->bool", ← q r"t:real^N->bool"]
     MATROID_DIM_EQ_SPAN) THEN
    ASM_REWRITE_TAC [EUCLIDEAN_MATROID, EUCLIDEAN_MATROID_FINITE_DIM,
                     EUCLIDEAN_MATROID_DIM, SUBSET_UNIV])

  let DIM_EQ_FULL ← prove
   r"!s:real^N->bool. dim s = dimindex(:N) <=> span s = (:real^N)"
   (GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM DIM_SPAN] THEN EQ_TAC THEN
    SIMP_TAC [DIM_UNIV] THEN DISCH_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM SPAN_UNIV] THEN MATCH_MP_TAC DIM_EQ_SPAN THEN
    ASM_REWRITE_TAC [SUBSET_UNIV, DIM_UNIV] THEN
    ASM_MESON_TAC [LE_REFL, DIM_SPAN])

  let DIM_PSUBSET ← prove
   r"!s t:real^N->bool. span s PSUBSET span t ==> dim s < dim t"
   (ONCE_REWRITE_TAC [← GSYM DIM_SPAN] THEN
    SIMP_TAC [PSUBSET, DIM_SUBSET, LT_LE] THEN
    MESON_TAC [EQ_IMP_LE, DIM_EQ_SPAN, SPAN_SPAN])

  let LOWDIM_EXPAND_DIMENSION ← prove
   r"!s:real^N->bool n.
        dim s <= n /\ n <= dimindex(:N)
        ==> ?t. dim(t) = n /\ span s SUBSET span t"
   (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL
      [← q r"euclidean_matroid:(real^N)matroid", ← q r"s:real^N->bool", ← q r"n:num"]
      MATROID_LOWDIM_EXPAND_DIMENSION) THEN
    ASM_SIMP_TAC [EUCLIDEAN_MATROID, EUCLIDEAN_MATROID_DIMENSION,
                  EUCLIDEAN_MATROID_FINITE_DIM, EUCLIDEAN_MATROID_DIM])

  let LOWDIM_EXPAND_BASIS ← prove
   r"!s:real^N->bool n.
        dim s <= n /\ n <= dimindex(:N)
        ==> ?b. b HAS_SIZE n /\ independent b /\ span s SUBSET span b"
   (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL
      [← q r"euclidean_matroid:(real^N)matroid", ← q r"s:real^N->bool", ← q r"n:num"]
      MATROID_LOWDIM_EXPAND_BASIS) THEN
    ASM_SIMP_TAC [EUCLIDEAN_MATROID, EUCLIDEAN_MATROID_INDEPENDENT,
                  EUCLIDEAN_MATROID_DIMENSION, EUCLIDEAN_MATROID_FINITE_DIM,
                  EUCLIDEAN_MATROID_DIM])

  return { DIM_SPAN, DIM_UNIQUE, DIM_LE_CARD, DIM_UNIV, DIM_SUBSET, DIM_SUBSET_UNIV,
           BASIS_HAS_SIZE_UNIV, CARD_GE_DIM_INDEPENDENT, CARD_LE_DIM_SPANNING, CARD_EQ_DIM,
           INDEPENDENT_BOUND_GENERAL, DEPENDENT_BIGGERSET_GENERAL, DIM_INSERT_0,
           DIM_EQ_CARD, DEPENDENT_EQ_DIM_LT_CARD, INDEPENDENT_EQ_DIM_EQ_CARD,
           SUBSET_LE_DIM, SPAN_EQ_DIM, DIM_EMPTY, DIM_INSERT, CHOOSE_SUBSPACE_OF_SUBSPACE,
           SUBSPACE_EXISTS, DIM_EQ_SPAN, DIM_EQ_FULL, DIM_PSUBSET, LOWDIM_EXPAND_DIMENSION,
           LOWDIM_EXPAND_BASIS }

/- ------------------------------------------------------------------------- -/
/- Explicit formulation of independence; a closed-graph property for        -/
/- linearity; stepping theorems; bases and injectivity/surjectivity.         -/
/- (vectors.ml 5674-5830)                                                     -/
/- ------------------------------------------------------------------------- -/

structure Explicit where
  INDEPENDENT_EXPLICIT : thm
  INDEPENDENT_SING : thm
  DEPENDENT_SING : thm
  DEPENDENT_2 : thm
  DEPENDENT_3 : thm
  INDEPENDENT_2 : thm
  INDEPENDENT_3 : thm
  LINEAR_SUBSPACE_GRAPH : thm
  SPANS_IMAGE : thm
  DIM_LINEAR_IMAGE_LE : thm
  DIM_SING : thm
  DIM_EQ_0 : thm
  SPANNING_SURJECTIVE_IMAGE : thm
  INDEPENDENT_INJECTIVE_IMAGE_GEN : thm
  INDEPENDENT_INJECTIVE_IMAGE : thm
  deriving Inhabited

@[nospecialize]
def setupExplicit [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BVSum1 : VSum1) (BLinear : Linear) (BPaste1 : Paste1) (BSubspace : Subspace)
    (BSpan1 : Span1) (BSpan2 : Span2) (BDim1 : Dim1) (BDim2 : Dim2) :
    ExceptT String IO Explicit := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON, MESON_TAC, SET_RULE, SET_TAC, .. } := D
  let { ARITH, CARD_IMAGE_LE, CONJ_ASSOC, CONTRAPOS_THM, EXISTS_IN_IMAGE,
        EXISTS_IN_INSERT, FINITE_EMPTY, FINITE_IMAGE, FINITE_INSERT, FINITE_SUBSET_IMAGE,
        FORALL_IN_GSPEC, .. } := D.core1
  let { HAS_SIZE, IMAGE_SUBSET, IMP_CONJ, IMP_CONJ_ALT, IN_ELIM_THM, IN_IMAGE, IN_INSERT,
        IN_SING, IN_UNIV, LEFT_IMP_EXISTS_THM, LE_TRANS, NOT_IN_EMPTY, .. } := D.core2
  let { PASTECART_INJ, .. } := D.core3
  let { RIGHT_FORALL_IMP_THM, SUBSET, SUBSET_IMAGE, SUBSET_TRANS, .. } := D.core4
  let { UNWIND_THM1, o_DEF, o_THM, .. } := D.core5
  let { VECTOR_ADD_LID, VECTOR_ADD_RID, VECTOR_MUL_LZERO, .. } := BVectorArith
  let { VSUM_CLAUSES, VSUM_IMAGE, .. } := BVSum1
  let { LINEAR_0, LINEAR_CMUL, LINEAR_VSUM, linear, .. } := BLinear
  let { PASTECART_ADD, PASTECART_CMUL, PASTECART_VEC, .. } := BPaste1
  let { INDEPENDENT_EMPTY, SPAN_EMPTY, independent, subspace, .. } := BSubspace
  let { SPAN_0, SPAN_LINEAR_IMAGE, SPAN_MUL, SPAN_SUPERSET, SPAN_VSUM, .. } := BSpan1
  let { DEPENDENT_EXPLICIT, DEPENDENT_FINITE, .. } := BSpan2
  let { BASIS_EXISTS, INDEPENDENT_BOUND, INDEPENDENT_INSERT, SPAN_CARD_GE_DIM, .. } := BDim1
  let { DIM_EMPTY, DIM_INSERT, DIM_SUBSET, .. } := BDim2
  -- @@SCOPE END

  let INDEPENDENT_EXPLICIT ← prove
   r"!b:real^N->bool.
        independent b <=>
            FINITE b /\
            !c. vsum b (\v. c(v) % v) = vec 0 ==> !v. v IN b ==> c(v) = &0"
   (GEN_TAC THEN
    ASM_CASES_TAC (← q r"FINITE(b:real^N->bool)") THENL
     [ALL_TAC, ASM_MESON_TAC [INDEPENDENT_BOUND]] THEN
    ASM_SIMP_TAC [independent, DEPENDENT_FINITE] THEN MESON_TAC [])

  let INDEPENDENT_SING ← prove
   r"!x. independent {x} <=> ~(x = vec 0)"
   (REWRITE_TAC [INDEPENDENT_INSERT, NOT_IN_EMPTY, SPAN_EMPTY] THEN
    REWRITE_TAC [INDEPENDENT_EMPTY] THEN SET_TAC [])

  let DEPENDENT_SING ← prove
   r"!x. dependent {x} <=> x = vec 0"
   (MESON_TAC [independent, INDEPENDENT_SING])

  let DEPENDENT_2 ← prove
   r"!a b:real^N.
        dependent {a,b} <=>
                if a = b then a = vec 0
                else ?x y. x % a + y % b = vec 0 /\ ~(x = &0 /\ y = &0)"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [DEPENDENT_SING, ← SET_RULE (← q r"{x,x} = {x}")] THEN
    SIMP_TAC [DEPENDENT_FINITE, VSUM_CLAUSES, FINITE_INSERT, FINITE_EMPTY] THEN
    ASM_REWRITE_TAC [IN_SING, NOT_IN_EMPTY, VECTOR_ADD_RID, EXISTS_IN_INSERT] THEN
    EQ_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THENL
     [X_GEN_TAC (← q r"u:real^N->real") THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [← q r"(u:real^N->real) a", ← q r"(u:real^N->real) b"] THEN
      ASM_REWRITE_TAC [],
      MAP_EVERY X_GEN_TAC [← q r"x:real", ← q r"y:real"] THEN DISCH_TAC THEN EXISTS_TAC
       (← q r"\v:real^N. if v = a then x else if v = b then y else z:real") THEN
      ASM_MESON_TAC []])

  let DEPENDENT_3 ← prove
   r"!a b c:real^N.
        ~(a = b) /\ ~(a = c) /\ ~(b = c)
        ==> (dependent {a,b,c} <=>
             ?x y z. x % a + y % b + z % c = vec 0 /\
                     ~(x = &0 /\ y = &0 /\ z = &0))"
   (REPEAT STRIP_TAC THEN
    SIMP_TAC [DEPENDENT_FINITE, VSUM_CLAUSES, FINITE_INSERT, FINITE_EMPTY] THEN
    ASM_REWRITE_TAC [IN_SING, NOT_IN_EMPTY, VECTOR_ADD_RID, IN_INSERT] THEN
    EQ_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THENL
     [X_GEN_TAC (← q r"u:real^N->real") THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC
       [← q r"(u:real^N->real) a", ← q r"(u:real^N->real) b", ← q r"(u:real^N->real) c"],
      MAP_EVERY X_GEN_TAC [← q r"x:real", ← q r"y:real", ← q r"z:real"] THEN DISCH_TAC THEN
      EXISTS_TAC
       (← q r"\v:real^N. if v = a then x else if v = b then y else z:real")] THEN
    ASM_MESON_TAC [])

  let INDEPENDENT_2 ← prove
   r"!a b:real^N x y.
        independent{a,b} /\ ~(a = b)
        ==> (x % a + y % b = vec 0 <=> x = &0 /\ y = &0)"
   (SIMP_TAC [IMP_CONJ_ALT, independent, DEPENDENT_2] THEN
    MESON_TAC [VECTOR_MUL_LZERO, VECTOR_ADD_LID])

  let INDEPENDENT_3 ← prove
   r"!a b c:real^N x y z.
        independent{a,b,c} /\ ~(a = b) /\ ~(a = c) /\ ~(b = c)
        ==> (x % a + y % b + z % c = vec 0 <=> x = &0 /\ y = &0 /\ z = &0)"
   (SIMP_TAC [IMP_CONJ_ALT, independent, DEPENDENT_3] THEN
    MESON_TAC [VECTOR_MUL_LZERO, VECTOR_ADD_LID])

  let LINEAR_SUBSPACE_GRAPH ← prove
   r"!f:real^M->real^N.
        linear f <=> subspace {pastecart x (f x) | x IN (:real^M)}"
   (REWRITE_TAC [linear, subspace, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC [FORALL_IN_GSPEC, ← GSYM (← SPEC (← q r"0") PASTECART_VEC), IN_UNIV] THEN
    REWRITE_TAC [IN_ELIM_THM, PASTECART_INJ, UNWIND_THM1, PASTECART_ADD,
                 ← GSYM PASTECART_CMUL] THEN
    MESON_TAC [VECTOR_MUL_LZERO])

  let SPANS_IMAGE ← prove
   r"!f b v. linear f /\ v SUBSET (span b)
           ==> (IMAGE f v) SUBSET span(IMAGE f b)"
   (SIMP_TAC [SPAN_LINEAR_IMAGE, IMAGE_SUBSET])

  let DIM_LINEAR_IMAGE_LE ← prove
   r"!f:real^M->real^N s. linear f ==> dim(IMAGE f s) <= dim s"
   (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"s:real^M->bool") BASIS_EXISTS) THEN
    REWRITE_TAC [HAS_SIZE] THEN STRIP_TAC THEN FIRST_ASSUM (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"CARD(IMAGE (f:real^M->real^N) b)") THEN
    ASM_SIMP_TAC [CARD_IMAGE_LE] THEN MATCH_MP_TAC SPAN_CARD_GE_DIM THEN
    ASM_MESON_TAC [SPAN_LINEAR_IMAGE, SPANS_IMAGE, SUBSET_IMAGE, FINITE_IMAGE])

  let DIM_SING ← prove
   r"!x. dim{x} = if x = vec 0 then 0 else 1"
   (REWRITE_TAC [DIM_INSERT, DIM_EMPTY, SPAN_EMPTY, IN_SING, ARITH])

  let DIM_EQ_0 ← prove
   r"!s:real^N->bool. dim s = 0 <=> s SUBSET {vec 0}"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [MATCH_MP_TAC (← SET_RULE (← q
       r"~(?b. ~(b = a) /\ {b} SUBSET s) ==> s SUBSET {a}")) THEN
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o MATCH_MP DIM_SUBSET),
      MATCH_MP_TAC (← ARITH_RULE (← q r"!m. m = 0 /\ n <= m ==> n = 0")) THEN
      EXISTS_TAC (← q r"dim{vec 0:real^N}") THEN ASM_SIMP_TAC [DIM_SUBSET]] THEN
    ASM_REWRITE_TAC [DIM_SING, ARITH])

  let SPANNING_SURJECTIVE_IMAGE ← prove
   r"!f:real^M->real^N s.
        UNIV SUBSET (span s) /\ linear f /\ (!y. ?x. f(x) = y)
        ==> UNIV SUBSET span(IMAGE f s)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC (← q r"IMAGE (f:real^M->real^N) UNIV") THEN
    ASM_SIMP_TAC [SPANS_IMAGE] THEN
    REWRITE_TAC [SUBSET, IN_UNIV, IN_IMAGE] THEN ASM_MESON_TAC [])

  let INDEPENDENT_INJECTIVE_IMAGE_GEN ← prove
   r"!f:real^M->real^N s.
        independent s /\ linear f /\
        (!x y. x IN span s /\ y IN span s /\ f(x) = f(y) ==> x = y)
        ==> independent (IMAGE f s)"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [independent, DEPENDENT_EXPLICIT] THEN
    REWRITE_TAC [CONJ_ASSOC, FINITE_SUBSET_IMAGE] THEN
    REWRITE_TAC [← MESON [] (← q
       r"(?s u. ((?t. p t /\ s = f t) /\ q s u) /\ r s u) <=>
      (?t u. p t /\ q (f t) u /\ r (f t) u)")] THEN
    REWRITE_TAC [EXISTS_IN_IMAGE, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"t:real^M->bool", ← q r"u:real^N->real"] THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC
     [← q r"t:real^M->bool", ← q r"(u:real^N->real) o (f:real^M->real^N)"] THEN
    ASM_REWRITE_TAC [o_THM] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SPAN_VSUM THEN ASM_REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
      MATCH_MP_TAC SPAN_SUPERSET THEN ASM SET_TAC [],
      REWRITE_TAC [SPAN_0],
      ASM_SIMP_TAC [LINEAR_VSUM] THEN
      FIRST_ASSUM (SUBST1_TAC o MATCH_MP LINEAR_0) THEN
      FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
      W (MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhand o snd) THEN
      ASM_SIMP_TAC [o_DEF, LINEAR_CMUL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC [SPAN_SUPERSET, SUBSET]])

  let INDEPENDENT_INJECTIVE_IMAGE ← prove
   r"!f:real^M->real^N s.
        independent s /\ linear f /\ (!x y. (f(x) = f(y)) ==> (x = y))
        ==> independent (IMAGE f s)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC INDEPENDENT_INJECTIVE_IMAGE_GEN THEN
    ASM_MESON_TAC [])

  return { INDEPENDENT_EXPLICIT, INDEPENDENT_SING, DEPENDENT_SING, DEPENDENT_2,
           DEPENDENT_3, INDEPENDENT_2, INDEPENDENT_3, LINEAR_SUBSPACE_GRAPH, SPANS_IMAGE,
           DIM_LINEAR_IMAGE_LE, DIM_SING, DIM_EQ_0, SPANNING_SURJECTIVE_IMAGE,
           INDEPENDENT_INJECTIVE_IMAGE_GEN, INDEPENDENT_INJECTIVE_IMAGE }

/- ------------------------------------------------------------------------- -/
/- Picking an orthogonal replacement for a spanning set; extending a linear -/
/- basis-basis injection and a linear map from a basis.                      -/
/- (vectors.ml 5830-6070)                                                     -/
/- ------------------------------------------------------------------------- -/

structure Extend where
  VECTOR_SUB_PROJECT_ORTHOGONAL : thm
  BASIS_ORTHOGONAL : thm
  ORTHOGONAL_BASIS_EXISTS : thm
  SPAN_SPECIAL_SCALE : thm
  LINEAR_INDEP_IMAGE_LEMMA : thm
  LINEAR_INDEPENDENT_EXTEND_LEMMA : thm
  LINEAR_INDEPENDENT_EXTEND : thm
  deriving Inhabited

@[nospecialize]
def setupExtend [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BDotProps : DotProps) (BVSum1 : VSum1) (BVSum2 : VSum2) (BOrth : Orth)
    (BLinear : Linear) (BSubspace : Subspace) (BSpan1 : Span1) (BDim1 : Dim1)
    (BDim2 : Dim2) : ExceptT String IO Extend := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, REAL_ARITH, SET_RULE, SELECT_CONV, .. } := D
  let { CARD_CLAUSES, DELETE_INSERT, EXTENSION, FINITE_DELETE, FINITE_INDUCT_STRONG,
        FINITE_RULES, FORALL_AND_THM, FORALL_IN_INSERT, .. } := D.core1
  let { HAS_SIZE, IMAGE_CLAUSES, IMP_CONJ, IMP_IMP, IN_DELETE, IN_IMAGE, IN_INSERT,
        IN_SING, IN_UNIV, LE_ANTISYM, LE_REFL, LE_TRANS, MONO_EXISTS, NOT_EXISTS_THM,
        NOT_IN_EMPTY, .. } := D.core2
  let { REAL_DIV_RMUL, REAL_MUL_LINV, REAL_MUL_LNEG, REAL_MUL_LZERO, .. } := D.core3
  let { REAL_MUL_RNEG, REAL_MUL_RZERO, REAL_NEG_NEG, REAL_SUB_0, REAL_SUB_REFL,
        RIGHT_FORALL_IMP_THM, RIGHT_IMP_FORALL_THM, SUBSET, SUBSET_TRANS, SUBSET_UNIV,
        SUM_EQ_0, .. } := D.core4
  let { UNIV_SUBSET, pairwise, .. } := D.core5
  let { VECTOR_ADD_LID, VECTOR_ARITH, VECTOR_ARITH_TAC, VECTOR_MUL_ASSOC, VECTOR_MUL_LID,
        VECTOR_MUL_LZERO, VECTOR_SUB_LDISTRIB, VECTOR_SUB_REFL, VECTOR_SUB_RZERO,
        .. } := BVectorArith
  let { DOT_EQ_0, DOT_LADD, DOT_LMUL, DOT_LSUB, DOT_LZERO, DOT_RADD, DOT_RMUL, DOT_RSUB,
        DOT_RZERO, DOT_SYM, .. } := BDotProps
  let { VSUM_CLAUSES, .. } := BVSum1
  let { DOT_LSUM, DOT_RSUM, .. } := BVSum2
  let { orthogonal, .. } := BOrth
  let { LINEAR_CMUL, LINEAR_SUB, linear, .. } := BLinear
  let { INDEPENDENT_MONO, SPAN_EMPTY, SPAN_MONO, SPAN_SPAN, dependent, independent,
        .. } := BSubspace
  let { SPAN_0, SPAN_ADD, SPAN_ADD_EQ, SPAN_BREAKDOWN, SPAN_BREAKDOWN_EQ, SPAN_INC,
        SPAN_INSERT_0, SPAN_LINEAR_IMAGE, SPAN_MUL, SPAN_SUB, SPAN_SUPERSET, SPAN_VSUM,
        .. } := BSpan1
  let { BASIS_EXISTS, INDEPENDENT_BOUND, INDEPENDENT_INSERT,
        MAXIMAL_INDEPENDENT_SUBSET_EXTEND, SPAN_CARD_GE_DIM, SPAN_EQ, .. } := BDim1
  let { CARD_LE_DIM_SPANNING, DIM_SPAN, .. } := BDim2
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let VECTOR_SUB_PROJECT_ORTHOGONAL ← prove
   r"!b:real^N x. b dot (x - ((b dot x) / (b dot b)) % b) = &0"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"b = vec 0 :real^N") THENL
     [ASM_REWRITE_TAC [DOT_LZERO], ALL_TAC] THEN
    ASM_SIMP_TAC [DOT_RSUB, DOT_RMUL] THEN
    ASM_SIMP_TAC [REAL_SUB_REFL, REAL_DIV_RMUL, DOT_EQ_0])

  let BASIS_ORTHOGONAL ← prove
   r"!b:real^N->bool.
        FINITE b
        ==> ?c. FINITE c /\ CARD c <= CARD b /\
                span c = span b /\ pairwise orthogonal c"
   (REWRITE_TAC [pairwise, orthogonal] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    CONJ_TAC THENL
     [EXISTS_TAC (← q r"{}:real^N->bool") THEN
      REWRITE_TAC [FINITE_RULES, NOT_IN_EMPTY, LE_REFL],
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"b:real^N->bool"] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"c:real^N->bool") STRIP_ASSUME_TAC)
          STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"(a - vsum c (\x. ((x dot a) / (x dot x)) % x):real^N)
              INSERT c") THEN
    ASM_SIMP_TAC [FINITE_RULES, CARD_CLAUSES] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC,
      REWRITE_TAC [EXTENSION, SPAN_BREAKDOWN_EQ] THEN
      FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN GEN_TAC THEN
      AP_TERM_TAC THEN ABS_TAC THEN REWRITE_TAC [VECTOR_SUB_LDISTRIB] THEN
      REWRITE_TAC [← va r"a - (x - y):real^N = y + (a - x)"] THEN
      MATCH_MP_TAC SPAN_ADD_EQ THEN MATCH_MP_TAC SPAN_MUL THEN
      MATCH_MP_TAC SPAN_VSUM THEN ASM_REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
      ASM_SIMP_TAC [SPAN_SUPERSET],
      REWRITE_TAC [IN_INSERT] THEN REPEAT STRIP_TAC THENL
       [ASM_MESON_TAC [],
        FIRST_X_ASSUM SUBST_ALL_TAC,
        FIRST_X_ASSUM SUBST_ALL_TAC,
        ASM_MESON_TAC []] THEN
      REWRITE_TAC [DOT_LSUB, DOT_RSUB, REAL_SUB_0] THEN
      FIRST_ASSUM (SUBST1_TAC o MATCH_MP (← SET_RULE (← q
       r"x IN s ==> s = x INSERT (s DELETE x)"))) THEN
      ASM_SIMP_TAC [VSUM_CLAUSES, FINITE_DELETE, IN_DELETE] THEN
      REWRITE_TAC [DOT_LADD, DOT_RADD, DOT_LMUL, DOT_RMUL] THEN
      MATCH_MP_TAC (← REAL_ARITH (← q r"s = &0 /\ a = b ==> b = a + s")) THEN
      ASM_SIMP_TAC [DOT_LSUM, DOT_RSUM, FINITE_DELETE] THEN
      (CONJ_TAC THENL
        [MATCH_MP_TAC SUM_EQ_0 THEN
         ASM_SIMP_TAC [DOT_LMUL, DOT_RMUL, IN_DELETE,
                       REAL_MUL_RZERO, REAL_MUL_LZERO],
         W (MP_TAC o PART_MATCH (lhand o rand) REAL_DIV_RMUL o lhand o snd) THEN
         REWRITE_TAC [DOT_SYM] THEN
         MATCH_MP_TAC (← TAUT (← q r"(p ==> q) ==> (~p ==> q) ==> q")) THEN
         SIMP_TAC [] THEN SIMP_TAC [DOT_EQ_0, DOT_RZERO, DOT_LZERO] THEN
         REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO]])])

  let ORTHOGONAL_BASIS_EXISTS ← prove
   r"!v:real^N->bool.
        ?b. independent b /\
            b SUBSET span v /\
            v SUBSET span b /\
            b HAS_SIZE dim v /\
            pairwise orthogonal b"
   (GEN_TAC THEN MP_TAC (← ISPEC (← q r"v:real^N->bool") BASIS_EXISTS) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:real^N->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← SPEC (← q r"b:real^N->bool") BASIS_ORTHOGONAL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [HAS_SIZE], ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"c:real^N->bool") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CARD_LE_DIM_SPANNING THEN ASM_REWRITE_TAC [] THEN
      EXISTS_TAC (← q r"span(v):real^N->bool") THEN CONJ_TAC THENL
       [ASM_MESON_TAC [SPAN_SPAN, SPAN_MONO],
        ASM_MESON_TAC [LE_TRANS, HAS_SIZE, DIM_SPAN]],
      ASM_MESON_TAC [SUBSET_TRANS, SPAN_INC, SPAN_SPAN, SPAN_MONO],
      RULE_ASSUM_TAC (REWRITE_RULE [HAS_SIZE]) THEN
      ASM_REWRITE_TAC [HAS_SIZE, ← GSYM LE_ANTISYM] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [LE_TRANS], ALL_TAC] THEN
      ONCE_REWRITE_TAC [← GSYM DIM_SPAN] THEN MATCH_MP_TAC SPAN_CARD_GE_DIM THEN
      ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [SPAN_SPAN, SPAN_MONO, SUBSET_TRANS, SPAN_INC]])

  let SPAN_SPECIAL_SCALE ← prove
   r"!s a x:real^N.
     span((a % x) INSERT s) = if a = &0 then span s else span(x INSERT s)"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [VECTOR_MUL_LZERO, SPAN_INSERT_0] THEN
    REWRITE_TAC [SPAN_EQ, SUBSET, FORALL_IN_INSERT] THEN
    SIMP_TAC [SPAN_MUL, SPAN_SUPERSET, IN_INSERT] THEN
    REWRITE_TAC [SPAN_BREAKDOWN_EQ] THEN EXISTS_TAC (← q r"inv a:real") THEN
    ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, VECTOR_MUL_LID] THEN
    REWRITE_TAC [SPAN_0, VECTOR_SUB_REFL])

  let LINEAR_INDEP_IMAGE_LEMMA ← prove
   r"!f b. linear(f:real^M->real^N) /\
         FINITE b /\
         independent (IMAGE f b) /\
         (!x y. x IN b /\ y IN b /\ (f x = f y) ==> (x = y))
         ==> !x. x IN span b ==> (f(x) = vec 0) ==> (x = vec 0)"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN DISCH_TAC THEN
    GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV) [IMP_IMP] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    CONJ_TAC THENL [SIMP_TAC [IN_SING, SPAN_EMPTY], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real^M", ← q r"b:real^M->bool"] THEN STRIP_TAC THEN
    STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o check (HolCore.Basics.is_imp o concl)) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC [INDEPENDENT_MONO, IMAGE_CLAUSES, SUBSET, IN_INSERT],
      ALL_TAC] THEN
    DISCH_TAC THEN X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"a:real^M", ← q r"(a:real^M) INSERT b", ← q r"x:real^M"]
      SPAN_BREAKDOWN) THEN
    ASM_REWRITE_TAC [IN_INSERT] THEN
    SIMP_TAC [← ASSUME (← q r"~((a:real^M) IN b)"), ← SET_RULE (← q
      r"~(a IN b) ==> ((a INSERT b) DELETE a = b)")] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"k:real") STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"(f:real^M->real^N)(x - k % a) IN span(IMAGE f b)") MP_TAC THENL
     [ASM_MESON_TAC [SPAN_LINEAR_IMAGE, IN_IMAGE], ALL_TAC] THEN
    FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP LINEAR_SUB th])) THEN
    FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP LINEAR_CMUL th])) THEN
    ASM_REWRITE_TAC [← va r"vec 0 - k % x = (--k) % x"] THEN
    ASM_CASES_TAC (← q r"k = &0") THENL
     [ASM_MESON_TAC [← va r"x - &0 % y = x"], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"--inv(k)") o MATCH_MP SPAN_MUL) THEN
    REWRITE_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LNEG, REAL_MUL_RNEG] THEN
    SIMP_TAC [REAL_NEG_NEG, REAL_MUL_LINV, ← ASSUME (← q r"~(k = &0)")] THEN
    REWRITE_TAC [VECTOR_MUL_LID] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [independent]) THEN
    REWRITE_TAC [dependent, NOT_EXISTS_THM] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"(f:real^M->real^N) a")) THEN
    SUBGOAL_THEN
     (← q r"IMAGE (f:real^M->real^N) (a INSERT b) DELETE f a =
    IMAGE f ((a INSERT b) DELETE a)")
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_DELETE, IN_INSERT] THEN
      ASM_MESON_TAC [IN_INSERT],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [DELETE_INSERT] THEN
    SIMP_TAC [← SET_RULE (← q r"~(a IN b) ==> (b DELETE a = b)"),
              ← ASSUME (← q r"~(a:real^M IN b)")] THEN
    SIMP_TAC [IMAGE_CLAUSES, IN_INSERT])

  let LINEAR_INDEPENDENT_EXTEND_LEMMA ← prove
   r"!f b. FINITE b
         ==> independent b
             ==> ?g:real^M->real^N.
                        (!x y. x IN span b /\ y IN span b
                                ==> (g(x + y) = g(x) + g(y))) /\
                        (!x c. x IN span b ==> (g(c % x) = c % g(x))) /\
                        (!x. x IN b ==> (g x = f x))"
   (GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [NOT_IN_EMPTY, INDEPENDENT_INSERT] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"(\x. vec 0):real^M->real^N") THEN
      SIMP_TAC [SPAN_EMPTY] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC,
      ALL_TAC] THEN
    SIMP_TAC [] THEN MAP_EVERY X_GEN_TAC [← q r"a:real^M", ← q r"b:real^M->bool"] THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^M->real^N") STRIP_ASSUME_TAC) THEN
    ABBREV_TAC (← q r"h = \z:real^M. @k. (z - k % a) IN span b") THEN
    SUBGOAL_THEN (← q r"!z:real^M. z IN span(a INSERT b)
                    ==> (z - h(z) % a) IN span(b) /\
                        !k. (z - k % a) IN span(b) ==> (k = h(z))")
    MP_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC (← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")) THEN CONJ_TAC THENL
       [EXPAND_TAC "h" THEN CONV_TAC SELECT_CONV THEN
        ASM_MESON_TAC [SPAN_BREAKDOWN_EQ],
        ALL_TAC] THEN
      REWRITE_TAC [RIGHT_IMP_FORALL_THM, IMP_IMP] THEN GEN_TAC THEN
      DISCH_THEN (MP_TAC o MATCH_MP SPAN_SUB) THEN
      REWRITE_TAC [← va r"(z - a % v) - (z - b % v) = (b - a) % v"] THEN
      ASM_CASES_TAC (← q r"k = (h:real^M->real) z") THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"inv(k - (h:real^M->real) z)") o
                 MATCH_MP SPAN_MUL) THEN
      ASM_SIMP_TAC [REAL_MUL_LINV, VECTOR_MUL_ASSOC, REAL_SUB_0] THEN
      ASM_REWRITE_TAC [VECTOR_MUL_LID],
      ALL_TAC] THEN
    REWRITE_TAC [← TAUT (← q r"(a ==> b /\ c) <=> (a ==> b) /\ (a ==> c)")] THEN
    REWRITE_TAC [RIGHT_IMP_FORALL_THM, IMP_IMP] THEN
    GEN_REWRITE_TAC LAND_CONV [FORALL_AND_THM] THEN STRIP_TAC THEN
    EXISTS_TAC (← q r"\z:real^M. h(z) % (f:real^M->real^N)(a) + g(z - h(z) % a)") THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q r"x:real^M", ← q r"y:real^M"] THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"(h:real^M->real)(x + y) = h(x) + h(y)") ASSUME_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC [← va
         r"(x + y) - (k + l) % a = (x - k % a) + (y - l % a)"] THEN
        CONJ_TAC THEN MATCH_MP_TAC SPAN_ADD THEN ASM_REWRITE_TAC [] THEN
        ASM_SIMP_TAC [],
        ALL_TAC] THEN
      ASM_REWRITE_TAC [← va
         r"(x + y) - (k + l) % a = (x - k % a) + (y - l % a)"] THEN
      ASM_SIMP_TAC [] THEN VECTOR_ARITH_TAC,
      MAP_EVERY X_GEN_TAC [← q r"x:real^M", ← q r"c:real"] THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"(h:real^M->real)(c % x) = c * h(x)") ASSUME_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC [← va
         r"c % x - (c * k) % a = c % (x - k % a)"] THEN
        CONJ_TAC THEN MATCH_MP_TAC SPAN_MUL THEN ASM_REWRITE_TAC [] THEN
        ASM_SIMP_TAC [],
        ALL_TAC] THEN
      ASM_REWRITE_TAC [← va
         r"c % x - (c * k) % a = c % (x - k % a)"] THEN
      ASM_SIMP_TAC [] THEN VECTOR_ARITH_TAC,
      ALL_TAC] THEN
    X_GEN_TAC (← q r"x:real^M") THEN REWRITE_TAC [IN_INSERT] THEN
    DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THENL
     [SUBGOAL_THEN (← q r"&1 = h(a:real^M)") (SUBST1_TAC o SYM) THENL
       [FIRST_X_ASSUM MATCH_MP_TAC, ALL_TAC] THEN
      REWRITE_TAC [← va r"a - &1 % a = vec 0", SPAN_0] THENL
       [ASM_MESON_TAC [SPAN_SUPERSET, SUBSET, IN_INSERT], ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"vec 0:real^M", ← q r"vec 0:real^M"]) THEN
      REWRITE_TAC [SPAN_0, VECTOR_ADD_LID] THEN
      REWRITE_TAC [← va r"(a = a + a) <=> (a = vec 0)"] THEN
      DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"&0 = h(x:real^M)") (SUBST1_TAC o SYM) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC, ALL_TAC] THEN
    REWRITE_TAC [VECTOR_ADD_LID, VECTOR_MUL_LZERO, VECTOR_SUB_RZERO] THEN
    ASM_MESON_TAC [SUBSET, IN_INSERT, SPAN_SUPERSET])

  let LINEAR_INDEPENDENT_EXTEND ← prove
   r"!f b. independent b
         ==> ?g:real^M->real^N. linear g /\ (!x. x IN b ==> (g x = f x))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"b:real^M->bool", ← q r"(:real^M)"]
             MAXIMAL_INDEPENDENT_SUBSET_EXTEND) THEN
    ASM_REWRITE_TAC [SUBSET_UNIV, UNIV_SUBSET] THEN
    REWRITE_TAC [EXTENSION, IN_UNIV] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"c:real^M->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"f:real^M->real^N", ← q r"c:real^M->bool"]
      LINEAR_INDEPENDENT_EXTEND_LEMMA) THEN
    ASM_SIMP_TAC [INDEPENDENT_BOUND, linear] THEN
    ASM_MESON_TAC [SUBSET])

  return { VECTOR_SUB_PROJECT_ORTHOGONAL, BASIS_ORTHOGONAL, ORTHOGONAL_BASIS_EXISTS,
           SPAN_SPECIAL_SCALE, LINEAR_INDEP_IMAGE_LEMMA, LINEAR_INDEPENDENT_EXTEND_LEMMA,
           LINEAR_INDEPENDENT_EXTEND }

/- ------------------------------------------------------------------------- -/
/- Linear (and bilinear) functions are equal on a subspace if they are on a -/
/- spanning set; left and right invertibility.  (vectors.ml 6075-6233)       -/
/- ------------------------------------------------------------------------- -/

structure LinEq where
  SUBSPACE_KERNEL : thm
  LINEAR_EQ_0_SPAN : thm
  LINEAR_EQ_0 : thm
  LINEAR_EQ : thm
  LINEAR_EQ_STDBASIS : thm
  SUBSPACE_LINEAR_FIXED_POINTS : thm
  BILINEAR_EQ : thm
  BILINEAR_EQ_STDBASIS : thm
  LEFT_INVERTIBLE_TRANSP : thm
  RIGHT_INVERTIBLE_TRANSP : thm
  INVERTIBLE_TRANSP : thm
  LINEAR_INJECTIVE_LEFT_INVERSE : thm
  LINEAR_INJECTIVE_LEFT_INVERSE_EQ : thm
  LINEAR_SURJECTIVE_RIGHT_INVERSE : thm
  LINEAR_SURJECTIVE_RIGHT_INVERSE_EQ : thm
  deriving Inhabited

@[nospecialize]
def setupLinEq [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BLinear : Linear) (BBilinear : Bilinear) (BInvertible : Invertible)
    (BMatProps : MatProps) (BSubspace : Subspace) (BSpan2 : Span2)
    (BExplicit : Explicit) (BExtend : Extend) : ExceptT String IO LinEq := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, .. } := D
  let { EQ_IMP, EXTENSION, FORALL_IN_IMAGE, .. } := D.core1
  let { FUN_EQ_THM, IN, INJECTIVE_LEFT_INVERSE, IN_ELIM_THM, IN_UNIV, I_DEF, I_THM,
        MONO_EXISTS, .. } := D.core2
  let { SUBSET, SUBSET_REFL, .. } := D.core4
  let { SURJECTIVE_RIGHT_INVERSE, o_THM, .. } := D.core5
  let { VECTOR_ADD_LID, VECTOR_MUL_RZERO, VECTOR_SUB_EQ, .. } := BVectorArith
  let { LINEAR_0, LINEAR_ADD, LINEAR_CMUL, LINEAR_COMPOSE, LINEAR_COMPOSE_SUB, LINEAR_ID,
        .. } := BLinear
  let { BILINEAR_LADD, BILINEAR_LMUL, BILINEAR_LZERO, BILINEAR_RADD, BILINEAR_RMUL,
        BILINEAR_RZERO, .. } := BBilinear
  let { invertible, .. } := BInvertible
  let { MATRIX_TRANSP_MUL, TRANSP_EQ, TRANSP_MAT, TRANSP_TRANSP, .. } := BMatProps
  let { SPAN_INDUCT, subspace, .. } := BSubspace
  let { INDEPENDENT_STDBASIS, SPAN_STDBASIS, .. } := BSpan2
  let { INDEPENDENT_INJECTIVE_IMAGE, .. } := BExplicit
  let { LINEAR_INDEPENDENT_EXTEND, .. } := BExtend
  -- @@SCOPE END

  let SUBSPACE_KERNEL ← prove
   r"!f. linear f ==> subspace {x | f(x) = vec 0}"
   (REWRITE_TAC [subspace, IN_ELIM_THM] THEN
    SIMP_TAC [LINEAR_ADD, LINEAR_CMUL, VECTOR_ADD_LID, VECTOR_MUL_RZERO] THEN
    MESON_TAC [LINEAR_0])

  let LINEAR_EQ_0_SPAN ← prove
   r"!f:real^M->real^N b.
        linear f /\ (!x. x IN b ==> f(x) = vec 0)
        ==> !x. x IN span(b) ==> f(x) = vec 0"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [IN]) THEN
    MATCH_MP_TAC SPAN_INDUCT THEN ASM_REWRITE_TAC [IN] THEN
    MP_TAC (← ISPEC (← q r"f:real^M->real^N") SUBSPACE_KERNEL) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM])

  let LINEAR_EQ_0 ← prove
   r"!f b s. linear f /\ s SUBSET (span b) /\ (!x. x IN b ==> f(x) = vec 0)
           ==> !x. x IN s ==> f(x) = vec 0"
   (MESON_TAC [LINEAR_EQ_0_SPAN, SUBSET])

  let LINEAR_EQ ← prove
   r"!f g b s. linear f /\ linear g /\ s SUBSET (span b) /\
             (!x. x IN b ==> f(x) = g(x))
              ==> !x. x IN s ==> f(x) = g(x)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM VECTOR_SUB_EQ] THEN
    STRIP_TAC THEN MATCH_MP_TAC LINEAR_EQ_0 THEN
    ASM_MESON_TAC [LINEAR_COMPOSE_SUB])

  let LINEAR_EQ_STDBASIS ← prove
   r"!f:real^M->real^N g.
        linear f /\ linear g /\
        (!i. 1 <= i /\ i <= dimindex(:M)
             ==> f(basis i) = g(basis i))
        ==> f = g"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"!x. x IN UNIV ==> (f:real^M->real^N) x = g x")
     (fun th => MP_TAC th THEN REWRITE_TAC [FUN_EQ_THM, IN_UNIV]) THEN
    MATCH_MP_TAC LINEAR_EQ THEN
    EXISTS_TAC (← q r"{basis i :real^M | 1 <= i /\ i <= dimindex(:M)}") THEN
    ASM_REWRITE_TAC [SPAN_STDBASIS, SUBSET_REFL, IN_ELIM_THM] THEN
    ASM_MESON_TAC [])

  let SUBSPACE_LINEAR_FIXED_POINTS ← prove
   r"!f:real^N->real^N. linear f ==> subspace {x | f(x) = x}"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM VECTOR_SUB_EQ] THEN
    MATCH_MP_TAC SUBSPACE_KERNEL THEN
    ASM_SIMP_TAC [LINEAR_COMPOSE_SUB, LINEAR_ID])

  let BILINEAR_EQ ← prove
   r"!f:real^M->real^N->real^P g b c s.
        bilinear f /\ bilinear g /\
        s SUBSET (span b) /\ t SUBSET (span c) /\
        (!x y. x IN b /\ y IN c ==> f x y = g x y)
         ==> !x y. x IN s /\ y IN t ==> f x y = g x y"
   (REPEAT STRIP_TAC THEN SUBGOAL_THEN
      (← q r"!x:real^M. x IN span b
                ==> !y:real^N. y IN span c ==> (f x y :real^P = g x y)")
      (fun th => ASM_MESON_TAC [th, SUBSET]) THEN
    MATCH_MP_TAC SPAN_INDUCT THEN REWRITE_TAC [subspace, IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC,
      ASM_SIMP_TAC [BILINEAR_LADD, BILINEAR_LMUL] THEN
      ASM_MESON_TAC [BILINEAR_LZERO]] THEN
    MATCH_MP_TAC SPAN_INDUCT THEN REWRITE_TAC [subspace, IN_ELIM_THM] THEN
    ASM_SIMP_TAC [BILINEAR_RADD, BILINEAR_RMUL] THEN
    ASM_MESON_TAC [BILINEAR_RZERO])

  let BILINEAR_EQ_STDBASIS ← prove
   r"!f:real^M->real^N->real^P g.
        bilinear f /\ bilinear g /\
        (!i j. 1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:N)
             ==> f (basis i) (basis j) = g (basis i) (basis j))
        ==> f = g"
   (REPEAT STRIP_TAC THEN SUBGOAL_THEN
     (← q r"!x y. x IN UNIV /\ y IN UNIV ==> (f:real^M->real^N->real^P) x y = g x y")
     (fun th => MP_TAC th THEN REWRITE_TAC [FUN_EQ_THM, IN_UNIV]) THEN
    MATCH_MP_TAC BILINEAR_EQ THEN
    EXISTS_TAC (← q r"{basis i :real^M | 1 <= i /\ i <= dimindex(:M)}") THEN
    EXISTS_TAC (← q r"{basis i :real^N | 1 <= i /\ i <= dimindex(:N)}") THEN
    ASM_REWRITE_TAC [SPAN_STDBASIS, SUBSET_REFL, IN_ELIM_THM] THEN
    ASM_MESON_TAC [])

  let LEFT_INVERTIBLE_TRANSP ← prove
   r"!A:real^N^M.
    (?B:real^N^M. B ** transp A = mat 1) <=> (?B:real^M^N. A ** B = mat 1)"
   (MESON_TAC [MATRIX_TRANSP_MUL, TRANSP_MAT, TRANSP_TRANSP])

  let RIGHT_INVERTIBLE_TRANSP ← prove
   r"!A:real^N^M.
    (?B:real^N^M. transp A ** B = mat 1) <=> (?B:real^M^N. B ** A = mat 1)"
   (MESON_TAC [MATRIX_TRANSP_MUL, TRANSP_MAT, TRANSP_TRANSP])

  let INVERTIBLE_TRANSP ← prove
   r"!A:real^N^M. invertible(transp A) <=> invertible A"
   (GEN_TAC THEN REWRITE_TAC [invertible] THEN
    GEN_REWRITE_TAC LAND_CONV [← MESON [TRANSP_TRANSP] (← q
      r"(?A:real^M^N. P A) <=> (?A:real^N^M. P(transp A))")] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [← GSYM TRANSP_MAT] THEN
    REWRITE_TAC [← GSYM MATRIX_TRANSP_MUL, TRANSP_EQ] THEN MESON_TAC [])

  let LINEAR_INJECTIVE_LEFT_INVERSE ← prove
   r"!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ?g. linear g /\ g o f = I"
   (REWRITE_TAC [INJECTIVE_LEFT_INVERSE] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN
     (← q r"?h. linear(h:real^N->real^M) /\
        !x. x IN IMAGE (f:real^M->real^N)
               {basis i | 1 <= i /\ i <= dimindex(:M)} ==> h x = g x")
    MP_TAC THENL
     [MATCH_MP_TAC LINEAR_INDEPENDENT_EXTEND THEN
      MATCH_MP_TAC INDEPENDENT_INJECTIVE_IMAGE THEN
      ASM_MESON_TAC [INJECTIVE_LEFT_INVERSE, INDEPENDENT_STDBASIS],
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"h:real^N->real^M") THEN
      ASM_REWRITE_TAC [FORALL_IN_IMAGE, IN_ELIM_THM] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LINEAR_EQ_STDBASIS THEN
      ASM_SIMP_TAC [I_DEF, LINEAR_COMPOSE, LINEAR_ID, o_THM] THEN
      ASM_MESON_TAC []])

  let LINEAR_INJECTIVE_LEFT_INVERSE_EQ ← prove
   r"!f:real^M->real^N.
        linear f
        ==> ((!x y. f x = f y ==> x = y) <=> ?g. linear g /\ g o f = I)"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ASM_MESON_TAC [LINEAR_INJECTIVE_LEFT_INVERSE],
      REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN MESON_TAC []])

  let LINEAR_SURJECTIVE_RIGHT_INVERSE ← prove
   r"!f:real^M->real^N.
        linear f /\ (!y. ?x. f x = y) ==> ?g. linear g /\ f o g = I"
   (REWRITE_TAC [SURJECTIVE_RIGHT_INVERSE] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN
     (← q r"?h. linear(h:real^N->real^M) /\
        !x. x IN {basis i | 1 <= i /\ i <= dimindex(:N)} ==> h x = g x")
    MP_TAC THENL
     [MATCH_MP_TAC LINEAR_INDEPENDENT_EXTEND THEN
      REWRITE_TAC [INDEPENDENT_STDBASIS],
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"h:real^N->real^M") THEN
      ASM_REWRITE_TAC [FORALL_IN_IMAGE, IN_ELIM_THM] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LINEAR_EQ_STDBASIS THEN
      ASM_SIMP_TAC [I_DEF, LINEAR_COMPOSE, LINEAR_ID, o_THM] THEN
      ASM_MESON_TAC []])

  let LINEAR_SURJECTIVE_RIGHT_INVERSE_EQ ← prove
   r"!f:real^M->real^N.
        linear f
        ==> ((!y. ?x. f x = y) <=> ?g. linear g /\ f o g = I)"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ASM_MESON_TAC [LINEAR_SURJECTIVE_RIGHT_INVERSE],
      REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN MESON_TAC []])

  return { SUBSPACE_KERNEL, LINEAR_EQ_0_SPAN, LINEAR_EQ_0, LINEAR_EQ, LINEAR_EQ_STDBASIS,
           SUBSPACE_LINEAR_FIXED_POINTS, BILINEAR_EQ, BILINEAR_EQ_STDBASIS,
           LEFT_INVERTIBLE_TRANSP, RIGHT_INVERTIBLE_TRANSP, INVERTIBLE_TRANSP,
           LINEAR_INJECTIVE_LEFT_INVERSE, LINEAR_INJECTIVE_LEFT_INVERSE_EQ,
           LINEAR_SURJECTIVE_RIGHT_INVERSE, LINEAR_SURJECTIVE_RIGHT_INVERSE_EQ }

/- ------------------------------------------------------------------------- -/
/- Matrix one-sided invertibility: injectivity, kernels, independent        -/
/- columns and rows, spanning columns and rows.  (vectors.ml 6234-6324)      -/
/- ------------------------------------------------------------------------- -/

structure MatInv where
  MATRIX_LEFT_INVERTIBLE_INJECTIVE : thm
  MATRIX_LEFT_INVERTIBLE_KER : thm
  MATRIX_RIGHT_INVERTIBLE_SURJECTIVE : thm
  MATRIX_LEFT_INVERTIBLE_INDEPENDENT_COLUMNS : thm
  MATRIX_RIGHT_INVERTIBLE_INDEPENDENT_ROWS : thm
  MATRIX_RIGHT_INVERTIBLE_SPAN_COLUMNS : thm
  MATRIX_LEFT_INVERTIBLE_SPAN_ROWS : thm
  deriving Inhabited

@[nospecialize]
def setupMatInv [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BVSum1 : VSum1) (BLinear : Linear) (BMatrix : Matrix) (BMatArith : MatArith)
    (BMatProps : MatProps) (BInvertible : Invertible) (BSubspace : Subspace)
    (BSpan1 : Span1) (BLinEq : LinEq) : ExceptT String IO MatInv := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, .. } := D
  let { CART_EQ, EXTENSION, FINITE_DELETE, FINITE_NUMSEG, .. } := D.core1
  let { FUN_EQ_THM, INSERT_DELETE, IN_DELETE, IN_ELIM_THM, IN_NUMSEG, IN_UNIV, I_THM,
        LAMBDA_BETA, .. } := D.core2
  let { o_THM, .. } := D.core5
  let { VECTOR_ADD_ASSOC, VECTOR_ADD_RDISTRIB, VECTOR_MUL_LZERO, VEC_COMPONENT,
        .. } := BVectorArith
  let { VSUM_0, VSUM_CLAUSES, VSUM_EQ, .. } := BVSum1
  let { LINEAR_INJECTIVE_0, .. } := BLinear
  let { columns, .. } := BMatrix
  let { MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID, .. } := BMatArith
  let { COLUMNS_TRANSP, COLUMN_TRANSP, MATRIX_EQ, MATRIX_MUL_VSUM, .. } := BMatProps
  let { MATRIX_VECTOR_MUL_LINEAR, MATRIX_WORKS, .. } := BInvertible
  let { SPAN_CLAUSES, SPAN_INDUCT_ALT, .. } := BSubspace
  let { SPAN_MUL, SPAN_VSUM, .. } := BSpan1
  let { LEFT_INVERTIBLE_TRANSP, LINEAR_INJECTIVE_LEFT_INVERSE,
        LINEAR_SURJECTIVE_RIGHT_INVERSE, RIGHT_INVERTIBLE_TRANSP, .. } := BLinEq
  -- @@SCOPE END

  let MATRIX_LEFT_INVERTIBLE_INJECTIVE ← prove
   r"!A:real^N^M.
        (?B:real^M^N. B ** A = mat 1) <=>
        !x y:real^N. A ** x = A ** y ==> x = y"
   (GEN_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN REPEAT GEN_TAC THEN
      DISCH_THEN (MP_TAC o AP_TERM (← q r"\x:real^M. (B:real^M^N) ** x")) THEN
      ASM_REWRITE_TAC [MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID],
      DISCH_TAC THEN MP_TAC (← ISPEC
       (← q r"\x:real^N. (A:real^N^M) ** x") LINEAR_INJECTIVE_LEFT_INVERSE) THEN
      ASM_REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR, FUN_EQ_THM, I_THM, o_THM] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^M->real^N") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"matrix(g):real^M^N") THEN
      REWRITE_TAC [MATRIX_EQ, MATRIX_VECTOR_MUL_LID] THEN
      ASM_MESON_TAC [MATRIX_VECTOR_MUL_ASSOC, MATRIX_WORKS]])

  let MATRIX_LEFT_INVERTIBLE_KER ← prove
   r"!A:real^N^M.
        (?B:real^M^N. B ** A = mat 1) <=> !x. A ** x = vec 0 ==> x = vec 0"
   (GEN_TAC THEN REWRITE_TAC [MATRIX_LEFT_INVERTIBLE_INJECTIVE] THEN
    MATCH_MP_TAC LINEAR_INJECTIVE_0 THEN REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR])

  let MATRIX_RIGHT_INVERTIBLE_SURJECTIVE ← prove
   r"!A:real^N^M.
        (?B:real^M^N. A ** B = mat 1) <=> !y:real^M. ?x. A ** x = y"
   (GEN_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN X_GEN_TAC (← q r"y:real^M") THEN
      EXISTS_TAC (← q r"(B:real^M^N) ** (y:real^M)") THEN
      ASM_REWRITE_TAC [MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID],
      DISCH_TAC THEN MP_TAC (← ISPEC
       (← q r"\x:real^N. (A:real^N^M) ** x") LINEAR_SURJECTIVE_RIGHT_INVERSE) THEN
      ASM_REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR, FUN_EQ_THM, I_THM, o_THM] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^M->real^N") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"matrix(g):real^M^N") THEN
      REWRITE_TAC [MATRIX_EQ, MATRIX_VECTOR_MUL_LID] THEN
      ASM_MESON_TAC [MATRIX_VECTOR_MUL_ASSOC, MATRIX_WORKS]])

  let MATRIX_LEFT_INVERTIBLE_INDEPENDENT_COLUMNS ← prove
   r"!A:real^N^M. (?B:real^M^N. B ** A = mat 1) <=>
                !c. vsum(1..dimindex(:N)) (\i. c(i) % column i A) = vec 0 ==>
                    !i. 1 <= i /\ i <= dimindex(:N) ==> c(i) = &0"
   (GEN_TAC THEN REWRITE_TAC [MATRIX_LEFT_INVERTIBLE_KER, MATRIX_MUL_VSUM] THEN
    EQ_TAC THEN DISCH_TAC THENL
     [X_GEN_TAC (← q r"c:num->real") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(lambda i. c(i)):real^N")),
      X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"\i. (x:real^N)$i"))] THEN
    ASM_SIMP_TAC [LAMBDA_BETA, CART_EQ, VEC_COMPONENT])

  let MATRIX_RIGHT_INVERTIBLE_INDEPENDENT_ROWS ← prove
   r"!A:real^N^M. (?B:real^M^N. A ** B = mat 1) <=>
                !c. vsum(1..dimindex(:M)) (\i. c(i) % row i A) = vec 0 ==>
                    !i. 1 <= i /\ i <= dimindex(:M) ==> c(i) = &0"
   (ONCE_REWRITE_TAC [← GSYM LEFT_INVERTIBLE_TRANSP] THEN
    REWRITE_TAC [MATRIX_LEFT_INVERTIBLE_INDEPENDENT_COLUMNS] THEN
    SIMP_TAC [COLUMN_TRANSP])

  let MATRIX_RIGHT_INVERTIBLE_SPAN_COLUMNS ← prove
   r"!A:real^N^M. (?B:real^M^N. A ** B = mat 1) <=> span(columns A) = (:real^M)"
   (GEN_TAC THEN REWRITE_TAC [MATRIX_RIGHT_INVERTIBLE_SURJECTIVE] THEN
    REWRITE_TAC [MATRIX_MUL_VSUM, EXTENSION, IN_UNIV] THEN
    AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"y:real^M") THEN
    EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"x:real^N") (SUBST1_TAC o SYM)) THEN
      MATCH_MP_TAC SPAN_VSUM THEN REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
      X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
      MATCH_MP_TAC (← CONJUNCT1 SPAN_CLAUSES) THEN
      REWRITE_TAC [columns, IN_ELIM_THM] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    SPEC_TAC (← q r"y:real^M", ← q r"y:real^M") THEN MATCH_MP_TAC SPAN_INDUCT_ALT THEN
    CONJ_TAC THENL
     [EXISTS_TAC (← q r"vec 0 :real^N") THEN
      SIMP_TAC [VEC_COMPONENT, VECTOR_MUL_LZERO, VSUM_0],
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q r"c:real", ← q r"y1:real^M", ← q r"y2:real^M"] THEN
    REWRITE_TAC [columns, IN_ELIM_THM] THEN DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_THEN (← q r"i:num") STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN (← q r"x:real^N") (SUBST1_TAC o SYM))) THEN
    EXISTS_TAC (← q r"(lambda j. if j = i then c + (x:real^N)$i else x$j):real^N") THEN
    SUBGOAL_THEN (← q r"1..dimindex(:N) = i INSERT ((1..dimindex(:N)) DELETE i)")
    SUBST1_TAC THENL [ASM_MESON_TAC [INSERT_DELETE, IN_NUMSEG], ALL_TAC] THEN
    SIMP_TAC [VSUM_CLAUSES, FINITE_DELETE, FINITE_NUMSEG, IN_DELETE] THEN
    ASM_SIMP_TAC [LAMBDA_BETA, VECTOR_ADD_RDISTRIB, VECTOR_ADD_ASSOC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
    SIMP_TAC [FINITE_DELETE, IN_DELETE, FINITE_NUMSEG, LAMBDA_BETA, IN_NUMSEG])

  let MATRIX_LEFT_INVERTIBLE_SPAN_ROWS ← prove
   r"!A:real^N^M. (?B:real^M^N. B ** A = mat 1) <=> span(rows A) = (:real^N)"
   (MESON_TAC [RIGHT_INVERTIBLE_TRANSP, COLUMNS_TRANSP,
               MATRIX_RIGHT_INVERTIBLE_SPAN_COLUMNS])

  return { MATRIX_LEFT_INVERTIBLE_INJECTIVE, MATRIX_LEFT_INVERTIBLE_KER,
           MATRIX_RIGHT_INVERTIBLE_SURJECTIVE, MATRIX_LEFT_INVERTIBLE_INDEPENDENT_COLUMNS,
           MATRIX_RIGHT_INVERTIBLE_INDEPENDENT_ROWS, MATRIX_RIGHT_INVERTIBLE_SPAN_COLUMNS,
           MATRIX_LEFT_INVERTIBLE_SPAN_ROWS }

/- ------------------------------------------------------------------------- -/
/- An injective map real^N->real^N is also surjective, and vice versa;     -/
/- isomorphisms; one-sided inverses are linear.  (vectors.ml 6329-6511)      -/
/- ------------------------------------------------------------------------- -/

structure Iso where
  LINEAR_INJECTIVE_IMP_SURJECTIVE : thm
  LINEAR_SURJECTIVE_IMP_INJECTIVE : thm
  LINEAR_SURJECTIVE_IFF_INJECTIVE : thm
  LEFT_RIGHT_INVERSE_EQ : thm
  ISOMORPHISM_EXPAND : thm
  LINEAR_INJECTIVE_ISOMORPHISM : thm
  LINEAR_SURJECTIVE_ISOMORPHISM : thm
  LINEAR_INVERSE_LEFT : thm
  LEFT_INVERSE_LINEAR : thm
  RIGHT_INVERSE_LINEAR : thm
  LEFT_RIGHT_INVERSE_LINEAR : thm
  LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE : thm
  LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE_EQ : thm
  LINEAR_INJECTIVE_LEFT_RIGHT_INVERSE_EQ : thm
  LINEAR_SURJECTIVE_LEFT_RIGHT_INVERSE_EQ : thm
  deriving Inhabited

@[nospecialize]
def setupIso [HolBase] (D : VectorsDeps) (BLinear : Linear) (BSpan1 : Span1)
    (BDim1 : Dim1) (BDim2 : Dim2) (BExplicit : Explicit) (BExtend : Extend)
    (BLinEq : LinEq) : ExceptT String IO Iso := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, METIS_TAC, .. } := D
  let { BIJECTIVE_LEFT_RIGHT_INVERSE, CARD_IMAGE_INJ, CARD_IMAGE_LE, FINITE_IMAGE,
        FORALL_IN_IMAGE, .. } := D.core1
  let { FUN_EQ_THM, HAS_SIZE, IMAGE_SUBSET, IMP_IMP, IN_IMAGE, IN_UNIV, I_O_ID, I_THM,
        LE_ANTISYM, LE_REFL, MONO_EXISTS, .. } := D.core2
  let { SUBSET, SUBSET_REFL, SUBSET_TRANS, SUBSET_UNIV, .. } := D.core4
  let { SURJECTIVE_IFF_INJECTIVE_GEN, o_ASSOC, o_THM, .. } := D.core5
  let { LINEAR_INJECTIVE_0, linear, .. } := BLinear
  let { SPAN_LINEAR_IMAGE, .. } := BSpan1
  let { BASIS_EXISTS, INDEPENDENT_BOUND, SPAN_CARD_GE_DIM, .. } := BDim1
  let { CARD_GE_DIM_INDEPENDENT, CARD_LE_DIM_SPANNING, .. } := BDim2
  let { INDEPENDENT_INJECTIVE_IMAGE, .. } := BExplicit
  let { LINEAR_INDEP_IMAGE_LEMMA, .. } := BExtend
  let { LINEAR_INJECTIVE_LEFT_INVERSE, LINEAR_SURJECTIVE_RIGHT_INVERSE, .. } := BLinEq
  -- @@SCOPE END

  let LINEAR_INJECTIVE_IMP_SURJECTIVE ← prove
   r"!f:real^N->real^N.
        linear f /\ (!x y. (f(x) = f(y)) ==> (x = y))
        ==> !y. ?x. f(x) = y"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"(:real^N)") BASIS_EXISTS) THEN
    REWRITE_TAC [SUBSET_UNIV, HAS_SIZE] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:real^N->bool") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"UNIV SUBSET span(IMAGE (f:real^N->real^N) b)") MP_TAC THENL
     [MATCH_MP_TAC CARD_GE_DIM_INDEPENDENT THEN
      ASM_MESON_TAC [INDEPENDENT_INJECTIVE_IMAGE, LE_REFL,
                     SUBSET_UNIV, CARD_IMAGE_INJ],
      ASM_SIMP_TAC [SPAN_LINEAR_IMAGE] THEN
      ASM_MESON_TAC [SUBSET, IN_IMAGE, IN_UNIV]])

  let LINEAR_SURJECTIVE_IMP_INJECTIVE ← prove
   r"!f:real^N->real^N.
        linear f /\ (!y. ?x. f(x) = y)
        ==> !x y. (f(x) = f(y)) ==> (x = y)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"(:real^N)") BASIS_EXISTS) THEN
    REWRITE_TAC [SUBSET_UNIV, HAS_SIZE] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:real^N->bool") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     (← q r"!x. x IN span b ==> (f:real^N->real^N) x = vec 0 ==> x = vec 0")
     (fun th => ASM_MESON_TAC [th, LINEAR_INJECTIVE_0, SUBSET, IN_UNIV]) THEN
    MATCH_MP_TAC LINEAR_INDEP_IMAGE_LEMMA THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_LE_DIM_SPANNING THEN
      EXISTS_TAC (← q r"(:real^N)") THEN
      ASM_SIMP_TAC [SUBSET_UNIV, FINITE_IMAGE, SPAN_LINEAR_IMAGE] THEN
      REWRITE_TAC [SUBSET, IN_UNIV, IN_IMAGE] THEN
      ASM_MESON_TAC [CARD_IMAGE_LE, SUBSET, IN_UNIV],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"dim(:real^N) <= CARD(IMAGE (f:real^N->real^N) b)")
    MP_TAC THENL
     [MATCH_MP_TAC SPAN_CARD_GE_DIM THEN
      ASM_SIMP_TAC [SUBSET_UNIV, FINITE_IMAGE] THEN
      ASM_SIMP_TAC [SPAN_LINEAR_IMAGE] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC (← q r"IMAGE (f:real^N->real^N) UNIV") THEN
      ASM_SIMP_TAC [IMAGE_SUBSET] THEN
      ASM_REWRITE_TAC [SUBSET, IN_IMAGE, IN_UNIV] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o ISPEC (← q r"f:real^N->real^N") o
                  MATCH_MP CARD_IMAGE_LE) THEN
    ASM_REWRITE_TAC [IMP_IMP, LE_ANTISYM] THEN DISCH_TAC THEN
    MP_TAC (← ISPECL
     [← q r"b:real^N->bool", ← q r"IMAGE (f:real^N->real^N) b", ← q r"f:real^N->real^N"]
     SURJECTIVE_IFF_INJECTIVE_GEN) THEN
    ASM_SIMP_TAC [FINITE_IMAGE, INDEPENDENT_BOUND, SUBSET_REFL] THEN
    REWRITE_TAC [FORALL_IN_IMAGE] THEN MESON_TAC [])

  let LINEAR_SURJECTIVE_IFF_INJECTIVE ← prove
   r"!f:real^N->real^N.
      linear f ==> ((!y. ?x. f x = y) <=> (!x y. f x = f y ==> x = y))"
   (MESON_TAC [LINEAR_INJECTIVE_IMP_SURJECTIVE,
               LINEAR_SURJECTIVE_IMP_INJECTIVE])

  let LEFT_RIGHT_INVERSE_EQ ← prove
   r"!f:A->A g h. f o g = I /\ g o h = I ==> f = h"
   (MESON_TAC [o_ASSOC, I_O_ID])

  let ISOMORPHISM_EXPAND ← prove
   r"!f g. f o g = I /\ g o f = I <=> (!x. f(g x) = x) /\ (!x. g(f x) = x)"
   (REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM])

  let LINEAR_INJECTIVE_ISOMORPHISM ← prove
   r"!f:real^N->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ?f'. linear f' /\ (!x. f'(f x) = x) /\ (!x. f(f' x) = x)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [← GSYM ISOMORPHISM_EXPAND] THEN
    MP_TAC (← ISPEC (← q r"f:real^N->real^N") LINEAR_SURJECTIVE_RIGHT_INVERSE) THEN
    MP_TAC (← ISPEC (← q r"f:real^N->real^N") LINEAR_INJECTIVE_LEFT_INVERSE) THEN
    MP_TAC (← ISPEC (← q r"f:real^N->real^N") LINEAR_INJECTIVE_IMP_SURJECTIVE) THEN
    ASM_REWRITE_TAC [] THEN SIMP_TAC [] THEN MESON_TAC [LEFT_RIGHT_INVERSE_EQ])

  let LINEAR_SURJECTIVE_ISOMORPHISM ← prove
   r"!f:real^N->real^N.
        linear f /\ (!y. ?x. f x = y)
        ==> ?f'. linear f' /\ (!x. f'(f x) = x) /\ (!x. f(f' x) = x)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [← GSYM ISOMORPHISM_EXPAND] THEN
    MP_TAC (← ISPEC (← q r"f:real^N->real^N") LINEAR_SURJECTIVE_RIGHT_INVERSE) THEN
    MP_TAC (← ISPEC (← q r"f:real^N->real^N") LINEAR_INJECTIVE_LEFT_INVERSE) THEN
    MP_TAC (← ISPEC (← q r"f:real^N->real^N") LINEAR_SURJECTIVE_IMP_INJECTIVE) THEN
    ASM_REWRITE_TAC [] THEN SIMP_TAC [] THEN MESON_TAC [LEFT_RIGHT_INVERSE_EQ])

  let LINEAR_INVERSE_LEFT ← prove
   r"!f:real^N->real^N f'.
        linear f /\ linear f' ==> ((f o f' = I) <=> (f' o f = I))"
   (SUBGOAL_THEN
     (← q r"!f:real^N->real^N f'.
        linear f /\ linear f' /\ (f o f' = I) ==> (f' o f = I)")
     (fun th => MESON_TAC [th]) THEN
    REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"f:real^N->real^N") LINEAR_SURJECTIVE_ISOMORPHISM) THEN
    ASM_MESON_TAC [])

  let LEFT_INVERSE_LINEAR ← prove
   r"!f g:real^N->real^N. linear f /\ (g o f = I) ==> linear g"
   (REPEAT GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN
    STRIP_TAC THEN SUBGOAL_THEN
     (← q r"?h:real^N->real^N. linear h /\ (!x. h(f x) = x) /\ (!x. f(h x) = x)")
    CHOOSE_TAC THENL
     [MATCH_MP_TAC LINEAR_INJECTIVE_ISOMORPHISM THEN ASM_MESON_TAC [],
      SUBGOAL_THEN (← q r"g:real^N->real^N = h") (fun th => ASM_REWRITE_TAC [th]) THEN
      REWRITE_TAC [FUN_EQ_THM] THEN ASM_MESON_TAC []])

  let RIGHT_INVERSE_LINEAR ← prove
   r"!f g:real^N->real^N. linear f /\ (f o g = I) ==> linear g"
   (REPEAT GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN
    STRIP_TAC THEN SUBGOAL_THEN
     (← q r"?h:real^N->real^N. linear h /\ (!x. h(f x) = x) /\ (!x. f(h x) = x)")
    CHOOSE_TAC THENL [ASM_MESON_TAC [LINEAR_SURJECTIVE_ISOMORPHISM], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"g:real^N->real^N = h") (fun th => ASM_REWRITE_TAC [th]) THEN
    REWRITE_TAC [FUN_EQ_THM] THEN ASM_MESON_TAC [])

  let LEFT_RIGHT_INVERSE_LINEAR ← prove
   r"!f g:real^M->real^N.
        linear f /\ g o f = I /\ f o g = I ==> linear g"
   (REWRITE_TAC [linear, FUN_EQ_THM, o_THM, I_THM] THEN MESON_TAC [])

  let LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE ← prove
   r"!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> ?g. linear g /\ (!x. g(f x) = x) /\ (!y. f(g y) = y)"
   (GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [BIJECTIVE_LEFT_RIGHT_INVERSE]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC LEFT_RIGHT_INVERSE_LINEAR THEN
    EXISTS_TAC (← q r"f:real^M->real^N") THEN
    ASM_REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM])

  let LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE_EQ ← prove
   r"!f:real^M->real^N.
        linear f
        ==> ((!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y) <=>
             ?g. linear g /\ f o g = I /\ g o f = I)"
   (REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THENL [REPEAT STRIP_TAC, MESON_TAC []] THEN
    ASM METIS_TAC [LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE])

  let LINEAR_INJECTIVE_LEFT_RIGHT_INVERSE_EQ ← prove
   r"!f:real^N->real^N.
        linear f
        ==> ((!x y. f x = f y ==> x = y) <=>
             (?g. linear g /\ f o g = I /\ g o f = I))"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (SUBST1_TAC o SYM o MATCH_MP
      LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE_EQ) THEN
    ASM_MESON_TAC [LINEAR_INJECTIVE_IMP_SURJECTIVE])

  let LINEAR_SURJECTIVE_LEFT_RIGHT_INVERSE_EQ ← prove
   r"!f:real^N->real^N.
        linear f
        ==> ((!y. ?x. f x = y) <=>
             (?g. linear g /\ f o g = I /\ g o f = I))"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (SUBST1_TAC o SYM o MATCH_MP
      LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE_EQ) THEN
    ASM_MESON_TAC [LINEAR_SURJECTIVE_IMP_INJECTIVE])

  return { LINEAR_INJECTIVE_IMP_SURJECTIVE, LINEAR_SURJECTIVE_IMP_INJECTIVE,
           LINEAR_SURJECTIVE_IFF_INJECTIVE, LEFT_RIGHT_INVERSE_EQ, ISOMORPHISM_EXPAND,
           LINEAR_INJECTIVE_ISOMORPHISM, LINEAR_SURJECTIVE_ISOMORPHISM, LINEAR_INVERSE_LEFT,
           LEFT_INVERSE_LINEAR, RIGHT_INVERSE_LINEAR, LEFT_RIGHT_INVERSE_LINEAR,
           LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE, LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE_EQ,
           LINEAR_INJECTIVE_LEFT_RIGHT_INVERSE_EQ, LINEAR_SURJECTIVE_LEFT_RIGHT_INVERSE_EQ }

/- ------------------------------------------------------------------------- -/
/- Square matrix inverses; invertibility of matrices and linear functions;  -/
/- lower bounds; preservation of dimension.  (vectors.ml 6516-6699)          -/
/- ------------------------------------------------------------------------- -/

structure MatInv2 where
  MATRIX_LEFT_RIGHT_INVERSE : thm
  MATRIX_LEFT_INVERTIBLE : thm
  MATRIX_RIGHT_INVERTIBLE : thm
  INVERTIBLE_LEFT_INVERSE : thm
  INVERTIBLE_RIGHT_INVERSE : thm
  MATRIX_INVERTIBLE : thm
  INVERTIBLE_EQ_INJECTIVE_AND_SURJECTIVE : thm
  LINEAR_INVERTIBLE_BOUNDED_BELOW_POS : thm
  LINEAR_INVERTIBLE_BOUNDED_BELOW : thm
  LINEAR_INJECTIVE_BOUNDED_BELOW_POS : thm
  DIM_INJECTIVE_LINEAR_IMAGE : thm
  LINEAR_INJECTIVE_DIMINDEX_LE : thm
  LINEAR_SURJECTIVE_DIMINDEX_LE : thm
  LINEAR_BIJECTIVE_DIMINDEX_EQ : thm
  INVERTIBLE_IMP_SQUARE_MATRIX : thm
  deriving Inhabited

@[nospecialize]
def setupMatInv2 [HolBase] (D : VectorsDeps) (BLinear : Linear) (BMatArith : MatArith)
    (BMatProps : MatProps) (BInvertible : Invertible) (BDim2 : Dim2)
    (BExplicit : Explicit) (BLinEq : LinEq) (BMatInv : MatInv) (BIso : Iso) :
    ExceptT String IO MatInv2 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, REAL_ARITH, SET_TAC, .. } := D
  let { FUN_EQ_THM, IMAGE_ID, IMAGE_o, I_THM, LEFT_IMP_EXISTS_THM, LE_ANTISYM, LE_REFL,
        LE_TRANS, .. } := D.core2
  let { REAL_LE_LDIV_EQ, REAL_LE_REFL, REAL_LE_TRANS, REAL_LT_INV_EQ, .. } := D.core3
  let { REAL_MUL_SYM, SUBSET_UNIV, .. } := D.core4
  let { o_DEF, o_THM, .. } := D.core5
  let { LINEAR_BOUNDED_POS, .. } := BLinear
  let { MATRIX_MUL_ASSOC, MATRIX_MUL_LID, MATRIX_MUL_RID, MATRIX_VECTOR_MUL_ASSOC,
        MATRIX_VECTOR_MUL_LID, .. } := BMatArith
  let { MATRIX_EQ, .. } := BMatProps
  let { MATRIX_COMPOSE, MATRIX_I, MATRIX_OF_MATRIX_VECTOR_MUL, MATRIX_VECTOR_MUL,
        MATRIX_VECTOR_MUL_LINEAR, MATRIX_WORKS, invertible, .. } := BInvertible
  let { DIM_SUBSET, DIM_UNIV, .. } := BDim2
  let { DIM_LINEAR_IMAGE_LE, .. } := BExplicit
  let { LINEAR_INJECTIVE_LEFT_INVERSE, LINEAR_SURJECTIVE_RIGHT_INVERSE, .. } := BLinEq
  let { MATRIX_LEFT_INVERTIBLE_INJECTIVE, MATRIX_RIGHT_INVERTIBLE_SURJECTIVE,
        .. } := BMatInv
  let { LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE_EQ, LINEAR_SURJECTIVE_ISOMORPHISM, .. } := BIso
  -- @@SCOPE END

  let MATRIX_LEFT_RIGHT_INVERSE ← prove
   r"!A:real^N^N A':real^N^N. (A ** A' = mat 1) <=> (A' ** A = mat 1)"
   (SUBGOAL_THEN
      (← q r"!A:real^N^N A':real^N^N. (A ** A' = mat 1) ==> (A' ** A = mat 1)")
      (fun th => MESON_TAC [th]) THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"\x:real^N. A:(real^N^N) ** x")
      LINEAR_SURJECTIVE_ISOMORPHISM) THEN
    REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR] THEN ANTS_TAC THENL
     [X_GEN_TAC (← q r"x:real^N") THEN EXISTS_TAC (← q r"(A':real^N^N) ** (x:real^N)") THEN
      ASM_REWRITE_TAC [MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"f':real^N->real^N") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"matrix (f':real^N->real^N) ** (A:real^N^N) = mat 1")
    MP_TAC THENL
     [ASM_SIMP_TAC [MATRIX_EQ, MATRIX_WORKS, ← GSYM MATRIX_VECTOR_MUL_ASSOC,
                    MATRIX_VECTOR_MUL_LID],
      ALL_TAC] THEN
    DISCH_THEN (fun th => ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"(\m:real^N^N. m ** (A':real^N^N))")) THEN
    REWRITE_TAC [← GSYM MATRIX_MUL_ASSOC] THEN
    ASM_REWRITE_TAC [MATRIX_MUL_RID, MATRIX_MUL_LID] THEN ASM_MESON_TAC [])

  let MATRIX_LEFT_INVERTIBLE ← prove
   r"!f:real^M->real^N.
    linear f ==> ((?B:real^N^M. B ** matrix f = mat 1) <=>
                  (?g. linear g /\ g o f = I))"
   (GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [EXISTS_TAC (← q r"\y:real^N. (B:real^N^M) ** y") THEN
      REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR] THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← MATCH_MP MATRIX_VECTOR_MUL th])) THEN
      ASM_REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM, MATRIX_VECTOR_MUL_ASSOC,
                       MATRIX_VECTOR_MUL_LID],
      EXISTS_TAC (← q r"matrix(g:real^N->real^M)") THEN
      ASM_SIMP_TAC [← GSYM MATRIX_COMPOSE, MATRIX_I]])

  let MATRIX_RIGHT_INVERTIBLE ← prove
   r"!f:real^M->real^N.
    linear f ==> ((?B:real^N^M. matrix f ** B = mat 1) <=>
                  (?g. linear g /\ f o g = I))"
   (GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [EXISTS_TAC (← q r"\y:real^N. (B:real^N^M) ** y") THEN
      REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR] THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        pure (GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [← MATCH_MP MATRIX_VECTOR_MUL th])) THEN
      ASM_REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM, MATRIX_VECTOR_MUL_ASSOC,
                       MATRIX_VECTOR_MUL_LID],
      EXISTS_TAC (← q r"matrix(g:real^N->real^M)") THEN
      ASM_SIMP_TAC [← GSYM MATRIX_COMPOSE, MATRIX_I]])

  let INVERTIBLE_LEFT_INVERSE ← prove
   r"!A:real^N^N. invertible(A) <=> ?B:real^N^N. B ** A = mat 1"
   (MESON_TAC [invertible, MATRIX_LEFT_RIGHT_INVERSE])

  let INVERTIBLE_RIGHT_INVERSE ← prove
   r"!A:real^N^N. invertible(A) <=> ?B:real^N^N. A ** B = mat 1"
   (MESON_TAC [invertible, MATRIX_LEFT_RIGHT_INVERSE])

  let MATRIX_INVERTIBLE ← prove
   r"!f:real^M->real^N.
        linear f
        ==> (invertible(matrix f) <=>
             ?g. linear g /\ f o g = I /\ g o f = I)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [invertible] THEN
    REWRITE_TAC [FUN_EQ_THM, MATRIX_EQ, MATRIX_VECTOR_MUL_LID, I_THM, o_THM] THEN
    ASM_SIMP_TAC [← GSYM MATRIX_VECTOR_MUL_ASSOC, MATRIX_WORKS] THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"A:real^N^M") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"\x:real^N. (A:real^N^M) ** x") THEN
      ASM_REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR],
      DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->real^M") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"matrix(g:real^N->real^M)") THEN
      ASM_SIMP_TAC [← GSYM MATRIX_VECTOR_MUL_ASSOC, MATRIX_WORKS]])

  let INVERTIBLE_EQ_INJECTIVE_AND_SURJECTIVE ← prove
   r"!m:real^M^N.
        invertible m <=>
        (!x y:real^M. m ** x = m ** y ==> x = y) /\
        IMAGE (\x. m ** x) (:real^M) = (:real^N)"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPEC (← q r"\x:real^M. (m:real^M^N) ** x") MATRIX_INVERTIBLE) THEN
    REWRITE_TAC [MATRIX_OF_MATRIX_VECTOR_MUL, MATRIX_VECTOR_MUL_LINEAR] THEN
    DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC [← GSYM LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE_EQ,
              MATRIX_VECTOR_MUL_LINEAR] THEN
    SET_TAC [])

  let LINEAR_INVERTIBLE_BOUNDED_BELOW_POS ← prove
   r"!f:real^M->real^N g.
        linear f /\ linear g /\ (g o f = I)
        ==> ?B. &0 < B /\ !x. B * norm(x) <= norm(f x)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"g:real^N->real^M") LINEAR_BOUNDED_POS) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"B:real") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"inv B:real") THEN ASM_REWRITE_TAC [REAL_LT_INV_EQ] THEN
    X_GEN_TAC (← q r"x:real^M") THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"inv(B) * norm(((g:real^N->real^M) o (f:real^M->real^N)) x)") THEN
    CONJ_TAC THENL [ASM_SIMP_TAC [I_THM, REAL_LE_REFL], ALL_TAC] THEN
    REWRITE_TAC [← REAL_ARITH (← q r"inv B * x = x / B")] THEN
    ASM_SIMP_TAC [o_THM, REAL_LE_LDIV_EQ] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN ASM_REWRITE_TAC [])

  let LINEAR_INVERTIBLE_BOUNDED_BELOW ← prove
   r"!f:real^M->real^N g.
        linear f /\ linear g /\ (g o f = I)
        ==> ?B. !x. B * norm(x) <= norm(f x)"
   (MESON_TAC [LINEAR_INVERTIBLE_BOUNDED_BELOW_POS])

  let LINEAR_INJECTIVE_BOUNDED_BELOW_POS ← prove
   r"!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ?B. &0 < B /\ !x. norm(x) * B <= norm(f x)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    MATCH_MP_TAC LINEAR_INVERTIBLE_BOUNDED_BELOW_POS THEN
    ASM_MESON_TAC [LINEAR_INJECTIVE_LEFT_INVERSE])

  let DIM_INJECTIVE_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y) ==> dim(IMAGE f s) = dim s"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM LE_ANTISYM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC [DIM_LINEAR_IMAGE_LE], ALL_TAC] THEN
    MP_TAC (← ISPEC (← q r"f:real^M->real^N") LINEAR_INJECTIVE_LEFT_INVERSE) THEN
    ASM_REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->real^M") STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC (← q r"dim(IMAGE (g:real^N->real^M) (IMAGE (f:real^M->real^N) s))") THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC [← GSYM IMAGE_o, o_DEF, IMAGE_ID, LE_REFL],
      MATCH_MP_TAC DIM_LINEAR_IMAGE_LE THEN ASM_REWRITE_TAC []])

  let LINEAR_INJECTIVE_DIMINDEX_LE ← prove
   r"!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> dimindex(:M) <= dimindex(:N)"
   (REWRITE_TAC [← GSYM DIM_UNIV] THEN REPEAT GEN_TAC THEN DISCH_THEN
     (SUBST1_TAC o SYM o SPEC (← q r"(:real^M)") o
      MATCH_MP DIM_INJECTIVE_LINEAR_IMAGE) THEN
    MATCH_MP_TAC DIM_SUBSET THEN REWRITE_TAC [SUBSET_UNIV])

  let LINEAR_SURJECTIVE_DIMINDEX_LE ← prove
   r"!f:real^M->real^N.
        linear f /\ (!y. ?x. f x = y)
        ==> dimindex(:N) <= dimindex(:M)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM
     (MP_TAC o MATCH_MP LINEAR_SURJECTIVE_RIGHT_INVERSE) THEN
    REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"g:real^N->real^M") THEN STRIP_TAC THEN
    MATCH_MP_TAC LINEAR_INJECTIVE_DIMINDEX_LE THEN
    EXISTS_TAC (← q r"g:real^N->real^M") THEN ASM_MESON_TAC [])

  let LINEAR_BIJECTIVE_DIMINDEX_EQ ← prove
   r"!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> dimindex(:M) = dimindex(:N)"
   (REWRITE_TAC [← GSYM LE_ANTISYM] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC LINEAR_INJECTIVE_DIMINDEX_LE,
      MATCH_MP_TAC LINEAR_SURJECTIVE_DIMINDEX_LE] THEN
    EXISTS_TAC (← q r"f:real^M->real^N") THEN ASM_REWRITE_TAC [])

  let INVERTIBLE_IMP_SQUARE_MATRIX ← prove
   r"!A:real^N^M. invertible A ==> dimindex(:M) = dimindex(:N)"
   (GEN_TAC THEN REWRITE_TAC [invertible, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"B:real^M^N") THEN STRIP_TAC THEN
    MATCH_MP_TAC LINEAR_BIJECTIVE_DIMINDEX_EQ THEN
    EXISTS_TAC (← q r"\x:real^M. (B:real^M^N) ** x") THEN
    ASM_REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR,
                     ← GSYM MATRIX_LEFT_INVERTIBLE_INJECTIVE,
                     ← GSYM MATRIX_RIGHT_INVERTIBLE_SURJECTIVE] THEN
    ASM_MESON_TAC [])

  return { MATRIX_LEFT_RIGHT_INVERSE, MATRIX_LEFT_INVERTIBLE, MATRIX_RIGHT_INVERTIBLE,
           INVERTIBLE_LEFT_INVERSE, INVERTIBLE_RIGHT_INVERSE, MATRIX_INVERTIBLE,
           INVERTIBLE_EQ_INJECTIVE_AND_SURJECTIVE, LINEAR_INVERTIBLE_BOUNDED_BELOW_POS,
           LINEAR_INVERTIBLE_BOUNDED_BELOW, LINEAR_INJECTIVE_BOUNDED_BELOW_POS,
           DIM_INJECTIVE_LINEAR_IMAGE, LINEAR_INJECTIVE_DIMINDEX_LE,
           LINEAR_SURJECTIVE_DIMINDEX_LE, LINEAR_BIJECTIVE_DIMINDEX_EQ,
           INVERTIBLE_IMP_SQUARE_MATRIX }

/- ------------------------------------------------------------------------- -/
/- Considering an n-element vector as an n-by-1 or 1-by-n matrix; column   -/
/- and row spaces, and the row rank bound.  (vectors.ml 6703-6828)           -/
/- ------------------------------------------------------------------------- -/

structure RowSpace where
  rowvector : thm
  columnvector : thm
  TRANSP_COLUMNVECTOR : thm
  TRANSP_ROWVECTOR : thm
  DOT_ROWVECTOR_COLUMNVECTOR : thm
  DOT_MATRIX_PRODUCT : thm
  DOT_MATRIX_VECTOR_MUL : thm
  MATRIX_VECTOR_MUL_IN_COLUMNSPACE : thm
  SUBSPACE_ORTHOGONAL_TO_VECTOR : thm
  SUBSPACE_ORTHOGONAL_TO_VECTORS : thm
  ORTHOGONAL_TO_SPAN : thm
  ORTHOGONAL_TO_SPAN_EQ : thm
  ORTHOGONAL_TO_SPANS_EQ : thm
  ORTHOGONAL_NULLSPACE_ROWSPACE : thm
  NULLSPACE_INTER_ROWSPACE : thm
  MATRIX_VECTOR_MUL_INJECTIVE_ON_ROWSPACE : thm
  DIM_ROWS_LE_DIM_COLUMNS : thm
  deriving Inhabited

@[nospecialize]
def setupRowSpace [HolBase] (D : VectorsDeps) (BBasics : Basics)
    (BVectorArith : VectorArith) (BOrth : Orth) (BMatrix : Matrix) (BMatArith : MatArith)
    (BMatProps : MatProps) (BInvertible : Invertible) (BSubspace : Subspace)
    (BSpan1 : Span1) (BDim1 : Dim1) (BDim2 : Dim2) (BExplicit : Explicit) :
    ExceptT String IO RowSpace := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, new_definition, .. } := D
  let { CARD_IMAGE_INJ, CART_EQ, DIMINDEX_1, EQ_IMP, FINITE_NUMSEG, FORALL_IN_GSPEC,
        FORALL_IN_IMAGE, .. } := D.core1
  let { HAS_SIZE, IMP_CONJ, IN_ELIM_THM, IN_NUMSEG, LAMBDA_BETA, LE_REFL, .. } := D.core2
  let { REAL_MUL_SYM, RIGHT_FORALL_IMP_THM, SUBSET, SUBSET_ANTISYM, .. } := D.core4
  let { dot, .. } := BBasics
  let { VECTOR_SUB_EQ, VEC_COMPONENT, .. } := BVectorArith
  let { ORTHOGONAL_CLAUSES, ORTHOGONAL_REFL, ORTHOGONAL_SYM, orthogonal, .. } := BOrth
  let { column, columns, matrix_mul, matrix_vector_mul, row, rows, transp, .. } := BMatrix
  let { MATRIX_MUL_ASSOC, MATRIX_VECTOR_MUL_RZERO, MATRIX_VECTOR_MUL_SUB_LDISTRIB,
        .. } := BMatArith
  let { MATRIX_TRANSP_MUL, MATRIX_VECTOR_MUL_COMPONENT, .. } := BMatProps
  let { MATRIX_VECTOR_COLUMN, MATRIX_VECTOR_MUL_LINEAR, .. } := BInvertible
  let { SPAN_INDUCT, SPAN_MONO, SPAN_SPAN, subspace, .. } := BSubspace
  let { SPAN_0, SPAN_MUL, SPAN_SUB, SPAN_SUPERSET, SPAN_VSUM, .. } := BSpan1
  let { BASIS_EXISTS, INDEPENDENT_CARD_LE_DIM, .. } := BDim1
  let { DIM_SPAN, .. } := BDim2
  let { INDEPENDENT_INJECTIVE_IMAGE_GEN, .. } := BExplicit
  -- @@SCOPE END

  let rowvector ← new_definition
   r"(rowvector:real^N->real^N^1) v = lambda i j. v$j"

  let columnvector ← new_definition
   r"(columnvector:real^N->real^1^N) v = lambda i j. v$i"

  let TRANSP_COLUMNVECTOR ← prove
   r"!v. transp(columnvector v) = rowvector v"
   (SIMP_TAC [transp, columnvector, rowvector, CART_EQ, LAMBDA_BETA])

  let TRANSP_ROWVECTOR ← prove
   r"!v. transp(rowvector v) = columnvector v"
   (SIMP_TAC [transp, columnvector, rowvector, CART_EQ, LAMBDA_BETA])

  let DOT_ROWVECTOR_COLUMNVECTOR ← prove
   r"!A:real^N^M v:real^N. columnvector(A ** v) = A ** columnvector v"
   (REWRITE_TAC [rowvector, columnvector, matrix_mul, matrix_vector_mul] THEN
    SIMP_TAC [CART_EQ, LAMBDA_BETA])

  let DOT_MATRIX_PRODUCT ← prove
   r"!x y:real^N. x dot y = (rowvector x ** columnvector y)$1$1"
   (REWRITE_TAC [matrix_mul, columnvector, rowvector, dot] THEN
    SIMP_TAC [LAMBDA_BETA, DIMINDEX_1, LE_REFL])

  let DOT_MATRIX_VECTOR_MUL ← prove
   r"!A:real^N^N B:real^N^N x:real^N y:real^N.
      (A ** x) dot (B ** y) =
      ((rowvector x) ** (transp(A) ** B) ** (columnvector y))$1$1"
   (REWRITE_TAC [DOT_MATRIX_PRODUCT] THEN
    ONCE_REWRITE_TAC [← GSYM TRANSP_COLUMNVECTOR] THEN
    REWRITE_TAC [DOT_ROWVECTOR_COLUMNVECTOR, MATRIX_TRANSP_MUL] THEN
    REWRITE_TAC [MATRIX_MUL_ASSOC])

  let MATRIX_VECTOR_MUL_IN_COLUMNSPACE ← prove
   r"!A:real^M^N x:real^M. (A ** x) IN span(columns A)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [MATRIX_VECTOR_COLUMN, columns] THEN
    MATCH_MP_TAC SPAN_VSUM THEN
    SIMP_TAC [FINITE_NUMSEG, IN_NUMSEG, transp, LAMBDA_BETA] THEN
    X_GEN_TAC (← q r"k:num") THEN STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
    MATCH_MP_TAC SPAN_SUPERSET THEN
    REWRITE_TAC [IN_ELIM_THM, column] THEN EXISTS_TAC (← q r"k:num") THEN
    ASM_REWRITE_TAC [])

  let SUBSPACE_ORTHOGONAL_TO_VECTOR ← prove
   r"!x. subspace {y | orthogonal x y}"
   (SIMP_TAC [subspace, IN_ELIM_THM, ORTHOGONAL_CLAUSES])

  let SUBSPACE_ORTHOGONAL_TO_VECTORS ← prove
   r"!s. subspace {y | (!x. x IN s ==> orthogonal x y)}"
   (SIMP_TAC [subspace, IN_ELIM_THM, ORTHOGONAL_CLAUSES])

  let ORTHOGONAL_TO_SPAN ← prove
   r"!s x. (!y. y IN s ==> orthogonal x y)
         ==> !y. y IN span(s) ==> orthogonal x y"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SPAN_INDUCT THEN
    REWRITE_TAC [← SET_RULE (← q r"(\y. orthogonal x y) = {y | orthogonal x y}")] THEN
    ASM_SIMP_TAC [SUBSPACE_ORTHOGONAL_TO_VECTOR, IN_ELIM_THM])

  let ORTHOGONAL_TO_SPAN_EQ ← prove
   r"!s x. (!y. y IN span(s) ==> orthogonal x y) <=>
         (!y. y IN s ==> orthogonal x y)"
   (MESON_TAC [SPAN_SUPERSET, ORTHOGONAL_TO_SPAN])

  let ORTHOGONAL_TO_SPANS_EQ ← prove
   r"!s t. (!x y. x IN span(s) /\ y IN span(t) ==> orthogonal x y) <=>
         (!x y. x IN s /\ y IN t ==> orthogonal x y)"
   (MESON_TAC [ORTHOGONAL_TO_SPAN_EQ, ORTHOGONAL_SYM])

  let ORTHOGONAL_NULLSPACE_ROWSPACE ← prove
   r"!A:real^M^N x y:real^M.
        A ** x = vec 0 /\ y IN span(rows A) ==> orthogonal x y"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SPAN_INDUCT THEN
    REWRITE_TAC [← SET_RULE (← q r"(\y. orthogonal x y) = {y | orthogonal x y}")] THEN
    REWRITE_TAC [SUBSPACE_ORTHOGONAL_TO_VECTOR, rows, FORALL_IN_GSPEC] THEN
    X_GEN_TAC (← q r"k:num") THEN STRIP_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN
    FIRST_X_ASSUM (MP_TAC o AP_TERM (← q r"\y:real^N. y$k")) THEN
    ASM_SIMP_TAC [MATRIX_VECTOR_MUL_COMPONENT, VEC_COMPONENT, row, dot,
                  orthogonal, LAMBDA_BETA] THEN
    REWRITE_TAC [REAL_MUL_SYM])

  let NULLSPACE_INTER_ROWSPACE ← prove
   r"!A:real^M^N x:real^M. A ** x = vec 0 /\ x IN span(rows A) <=> x = vec 0"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [MESON_TAC [ORTHOGONAL_NULLSPACE_ROWSPACE, ORTHOGONAL_REFL],
      SIMP_TAC [MATRIX_VECTOR_MUL_RZERO, SPAN_0]])

  let MATRIX_VECTOR_MUL_INJECTIVE_ON_ROWSPACE ← prove
   r"!A:real^M^N x y:real^M.
        x IN span(rows A) /\ y IN span(rows A) /\ A ** x = A ** y ==> x = y"
   (ONCE_REWRITE_TAC [← GSYM VECTOR_SUB_EQ] THEN
    REWRITE_TAC [← GSYM MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM NULLSPACE_INTER_ROWSPACE] THEN
    ASM_SIMP_TAC [SPAN_SUB])

  let DIM_ROWS_LE_DIM_COLUMNS ← prove
   r"!A:real^M^N. dim(rows A) <= dim(columns A)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM DIM_SPAN] THEN
    X_CHOOSE_THEN (← q r"b:real^M->bool") STRIP_ASSUME_TAC
     (← ISPEC (← q r"span(rows(A:real^M^N))") BASIS_EXISTS) THEN
    SUBGOAL_THEN (← q r"FINITE(IMAGE (\x:real^M. (A:real^M^N) ** x) b) /\
                CARD (IMAGE (\x:real^M. (A:real^M^N) ** x) b) <=
                dim(span(columns A))")
    MP_TAC THENL
     [MATCH_MP_TAC INDEPENDENT_CARD_LE_DIM THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, MATRIX_VECTOR_MUL_IN_COLUMNSPACE] THEN
      MATCH_MP_TAC INDEPENDENT_INJECTIVE_IMAGE_GEN THEN
      ASM_REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR] THEN
      SUBGOAL_THEN (← q r"span(b) = span(rows(A:real^M^N))") SUBST1_TAC THENL
       [ALL_TAC, ASM_MESON_TAC [MATRIX_VECTOR_MUL_INJECTIVE_ON_ROWSPACE]] THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC [] THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM SPAN_SPAN] THEN
      ASM_SIMP_TAC [SPAN_MONO],
      DISCH_THEN (MP_TAC o CONJUNCT2) THEN MATCH_MP_TAC EQ_IMP THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      FIRST_ASSUM (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM) o
        GEN_REWRITE_RULE id [HAS_SIZE]) THEN
      MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC
       (← ISPEC (← q r"A:real^M^N") MATRIX_VECTOR_MUL_INJECTIVE_ON_ROWSPACE) THEN
      ASM SET_TAC []])

  return { rowvector, columnvector, TRANSP_COLUMNVECTOR, TRANSP_ROWVECTOR,
           DOT_ROWVECTOR_COLUMNVECTOR, DOT_MATRIX_PRODUCT, DOT_MATRIX_VECTOR_MUL,
           MATRIX_VECTOR_MUL_IN_COLUMNSPACE, SUBSPACE_ORTHOGONAL_TO_VECTOR,
           SUBSPACE_ORTHOGONAL_TO_VECTORS, ORTHOGONAL_TO_SPAN, ORTHOGONAL_TO_SPAN_EQ,
           ORTHOGONAL_TO_SPANS_EQ, ORTHOGONAL_NULLSPACE_ROWSPACE, NULLSPACE_INTER_ROWSPACE,
           MATRIX_VECTOR_MUL_INJECTIVE_ON_ROWSPACE, DIM_ROWS_LE_DIM_COLUMNS }

/- ------------------------------------------------------------------------- -/
/- Rank of a matrix.  (vectors.ml 6830-6995)                                 -/
/- ------------------------------------------------------------------------- -/

structure Rank where
  rank : thm
  RANK_ROW : thm
  RANK_TRANSP : thm
  MATRIX_VECTOR_MUL_BASIS : thm
  COLUMNS_IMAGE_BASIS : thm
  RANK_DIM_IM : thm
  RANK_BOUND : thm
  FULL_RANK_INJECTIVE : thm
  FULL_RANK_SURJECTIVE : thm
  RANK_I : thm
  MATRIX_FULL_LINEAR_EQUATIONS : thm
  MATRIX_NONFULL_LINEAR_EQUATIONS_EQ : thm
  MATRIX_NONFULL_LINEAR_EQUATIONS : thm
  MATRIX_TRIVIAL_LINEAR_EQUATIONS : thm
  RANK_EQ_0 : thm
  RANK_0 : thm
  RANK_MUL_LE_RIGHT : thm
  RANK_MUL_LE_LEFT : thm
  SPAN_COLUMNSPACE : thm
  MATRIX_AUGMENTED_LINEAR_EQUATIONS : thm
  deriving Inhabited

@[nospecialize]
def setupRank [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BDotProps : DotProps) (BBasis : Basis) (BLinear : Linear) (BMatrix : Matrix)
    (BMatArith : MatArith) (BMatProps : MatProps) (BInvertible : Invertible)
    (BSubspace : Subspace) (BSpan1 : Span1) (BSpan2 : Span2) (BDim2 : Dim2)
    (BExplicit : Explicit) (BLinEq : LinEq) (BMatInv : MatInv) (BRowSpace : RowSpace) :
    ExceptT String IO Rank := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, MESON_TAC, SET_RULE, new_definition, .. } := D
  let { ADD1, ARITH, CART_EQ, COND_ID, DIMINDEX_1, DIMINDEX_FINITE_SUM, DIMINDEX_GE_1,
        ETA_AX, EXTENSION, FORALL_IN_GSPEC, FORALL_IN_IMAGE, .. } := D.core1
  let { IMAGE_CLAUSES, IMAGE_EQ, IMAGE_o, IN, IN_ELIM_THM, IN_NUMSEG, IN_SING, IN_UNIV,
        LAMBDA_BETA, LAMBDA_ETA, LE_REFL, LE_TRANS, NUMSEG_REC, .. } := D.core2
  let { RIGHT_FORALL_IMP_THM, SIMPLE_IMAGE, SIMPLE_IMAGE_GEN, SUBSET, .. } := D.core4
  let { SWAP_FORALL_THM, numseg, o_DEF, pastecart, .. } := D.core5
  let { VEC_COMPONENT, .. } := BVectorArith
  let { FORALL_DOT_EQ_0, .. } := BDotProps
  let { DOT_BASIS, .. } := BBasis
  let { LINEAR_INJECTIVE_0, .. } := BLinear
  let { column, columns, mat, row, rows, .. } := BMatrix
  let { MATRIX_VECTOR_MUL_ADD_LDISTRIB, MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID,
        MATRIX_VECTOR_MUL_RMUL, MATRIX_VECTOR_MUL_RZERO, .. } := BMatArith
  let { COLUMNS_TRANSP, MATRIX_MUL_DOT, MATRIX_TRANSP_MUL, MATRIX_VECTOR_MUL_COMPONENT,
        ROWS_TRANSP, .. } := BMatProps
  let { MATRIX_VECTOR_MUL_LINEAR, .. } := BInvertible
  let { SPAN_INDUCT, SPAN_SPAN, subspace, .. } := BSubspace
  let { SPAN_LINEAR_IMAGE, .. } := BSpan1
  let { SPAN_STDBASIS, .. } := BSpan2
  let { DIM_EQ_FULL, DIM_INSERT, DIM_SUBSET_UNIV, SPAN_EQ_DIM, .. } := BDim2
  let { DIM_EQ_0, DIM_LINEAR_IMAGE_LE, .. } := BExplicit
  let { LEFT_INVERTIBLE_TRANSP, .. } := BLinEq
  let { MATRIX_LEFT_INVERTIBLE_INJECTIVE, MATRIX_LEFT_INVERTIBLE_SPAN_ROWS,
        MATRIX_RIGHT_INVERTIBLE_SURJECTIVE, .. } := BMatInv
  let { DIM_ROWS_LE_DIM_COLUMNS, MATRIX_VECTOR_MUL_IN_COLUMNSPACE, rowvector,
        .. } := BRowSpace
  -- @@SCOPE END

  let rank ← new_definition
   r"rank(A:real^M^N) = dim(columns A)"

  let RANK_ROW ← prove
   r"!A:real^M^N. rank(A) = dim(rows A)"
   (GEN_TAC THEN REWRITE_TAC [rank] THEN
    MP_TAC (← ISPEC (← q r"A:real^M^N") DIM_ROWS_LE_DIM_COLUMNS) THEN
    MP_TAC (← ISPEC (← q r"transp(A:real^M^N)") DIM_ROWS_LE_DIM_COLUMNS) THEN
    REWRITE_TAC [ROWS_TRANSP, COLUMNS_TRANSP] THEN ARITH_TAC)

  let RANK_TRANSP ← prove
   r"!A:real^M^N. rank(transp A) = rank A"
   (GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [RANK_ROW] THEN
    REWRITE_TAC [rank, COLUMNS_TRANSP])

  let MATRIX_VECTOR_MUL_BASIS ← prove
   r"!A:real^M^N k. 1 <= k /\ k <= dimindex(:M)
                 ==> A ** (basis k) = column k A"
   (SIMP_TAC [CART_EQ, column, MATRIX_VECTOR_MUL_COMPONENT, DOT_BASIS,
              LAMBDA_BETA])

  let COLUMNS_IMAGE_BASIS ← prove
   r"!A:real^M^N.
     columns A = IMAGE (\x. A ** x) {basis i | 1 <= i /\ i <= dimindex(:M)}"
   (GEN_TAC THEN REWRITE_TAC [columns] THEN
    ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC [← GSYM IMAGE_o, o_DEF] THEN MATCH_MP_TAC IMAGE_EQ THEN
    SIMP_TAC [IN_ELIM_THM, MATRIX_VECTOR_MUL_BASIS])

  let RANK_DIM_IM ← prove
   r"!A:real^M^N. rank A = dim(IMAGE (\x. A ** x) (:real^M))"
   (GEN_TAC THEN REWRITE_TAC [rank] THEN
    MATCH_MP_TAC SPAN_EQ_DIM THEN REWRITE_TAC [COLUMNS_IMAGE_BASIS] THEN
    SIMP_TAC [SPAN_LINEAR_IMAGE, MATRIX_VECTOR_MUL_LINEAR] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM SPAN_SPAN] THEN
    REWRITE_TAC [SPAN_STDBASIS])

  let RANK_BOUND ← prove
   r"!A:real^M^N. rank(A) <= MIN (dimindex(:M)) (dimindex(:N))"
   (GEN_TAC THEN REWRITE_TAC [← ARITH_RULE (← q r"x <= MIN a b <=> x <= a /\ x <= b")] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [DIM_SUBSET_UNIV, RANK_ROW],
      REWRITE_TAC [DIM_SUBSET_UNIV, rank]])

  let FULL_RANK_INJECTIVE ← prove
   r"!A:real^M^N.
        rank A = dimindex(:M) <=>
        (!x y:real^M. A ** x = A ** y ==> x = y)"
   (REWRITE_TAC [← GSYM MATRIX_LEFT_INVERTIBLE_INJECTIVE] THEN
    REWRITE_TAC [MATRIX_LEFT_INVERTIBLE_SPAN_ROWS] THEN
    REWRITE_TAC [RANK_ROW, DIM_EQ_FULL])

  let FULL_RANK_SURJECTIVE ← prove
   r"!A:real^M^N.
        rank A = dimindex(:N) <=> (!y:real^N. ?x:real^M. A ** x = y)"
   (REWRITE_TAC [← GSYM MATRIX_RIGHT_INVERTIBLE_SURJECTIVE] THEN
    REWRITE_TAC [← GSYM LEFT_INVERTIBLE_TRANSP] THEN
    REWRITE_TAC [MATRIX_LEFT_INVERTIBLE_INJECTIVE] THEN
    REWRITE_TAC [← GSYM FULL_RANK_INJECTIVE, RANK_TRANSP])

  let RANK_I ← prove
   r"rank(mat 1:real^N^N) = dimindex(:N)"
   (REWRITE_TAC [FULL_RANK_INJECTIVE, MATRIX_VECTOR_MUL_LID])

  let MATRIX_FULL_LINEAR_EQUATIONS ← prove
   r"!A:real^M^N b:real^N.
        rank A = dimindex(:N) ==> ?x. A ** x = b"
   (SIMP_TAC [FULL_RANK_SURJECTIVE])

  let MATRIX_NONFULL_LINEAR_EQUATIONS_EQ ← prove
   r"!A:real^M^N.
        (?x. ~(x = vec 0) /\ A ** x = vec 0) <=> ~(rank A = dimindex(:M))"
   (REPEAT GEN_TAC THEN REWRITE_TAC [FULL_RANK_INJECTIVE] THEN
    SIMP_TAC [LINEAR_INJECTIVE_0, MATRIX_VECTOR_MUL_LINEAR] THEN
    MESON_TAC [])

  let MATRIX_NONFULL_LINEAR_EQUATIONS ← prove
   r"!A:real^M^N.
        ~(rank A = dimindex(:M)) ==> ?x. ~(x = vec 0) /\ A ** x = vec 0"
   (REWRITE_TAC [MATRIX_NONFULL_LINEAR_EQUATIONS_EQ])

  let MATRIX_TRIVIAL_LINEAR_EQUATIONS ← prove
   r"!A:real^M^N.
        dimindex(:N) < dimindex(:M)
        ==> ?x. ~(x = vec 0) /\ A ** x = vec 0"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_NONFULL_LINEAR_EQUATIONS THEN
    MATCH_MP_TAC (← ARITH_RULE (← q
     r"!a. x <= MIN b a /\ a < b ==> ~(x = b)")) THEN
    EXISTS_TAC (← q r"dimindex(:N)") THEN ASM_REWRITE_TAC [RANK_BOUND])

  let RANK_EQ_0 ← prove
   r"!A:real^M^N. rank A = 0 <=> A = mat 0"
   (REWRITE_TAC [RANK_DIM_IM, DIM_EQ_0, SUBSET, FORALL_IN_IMAGE, IN_SING,
                 IN_UNIV] THEN
    GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [CART_EQ] THEN
    SIMP_TAC [CART_EQ, MATRIX_MUL_DOT, VEC_COMPONENT, LAMBDA_BETA, mat] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM, FORALL_DOT_EQ_0, COND_ID] THEN
    REWRITE_TAC [CART_EQ, VEC_COMPONENT])

  let RANK_0 ← prove
   r"rank(mat 0) = 0"
   (REWRITE_TAC [RANK_EQ_0])

  let RANK_MUL_LE_RIGHT ← prove
   r"!A:real^N^M B:real^P^N. rank(A ** B) <= rank(B)"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC (← q r"dim(IMAGE (\y. (A:real^N^M) ** y)
                        (IMAGE (\x. (B:real^P^N) ** x) (:real^P)))") THEN
    REWRITE_TAC [RANK_DIM_IM] THEN CONJ_TAC THENL
     [REWRITE_TAC [← GSYM IMAGE_o, o_DEF, MATRIX_VECTOR_MUL_ASSOC, LE_REFL],
      MATCH_MP_TAC DIM_LINEAR_IMAGE_LE THEN
      REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR]])

  let RANK_MUL_LE_LEFT ← prove
   r"!A:real^N^M B:real^P^N. rank(A ** B) <= rank(A)"
   (ONCE_REWRITE_TAC [← GSYM RANK_TRANSP] THEN
    REWRITE_TAC [MATRIX_TRANSP_MUL] THEN
    REWRITE_TAC [RANK_MUL_LE_RIGHT])

  let SPAN_COLUMNSPACE ← prove
   r"!A:real^M^N. span(columns A) = {y | ?x. A ** x = y}"
   (GEN_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"y:real^N") THEN EQ_TAC THENL
     [ALL_TAC, MESON_TAC [MATRIX_VECTOR_MUL_IN_COLUMNSPACE]] THEN
    SPEC_TAC (← q r"y:real^N", ← q r"y:real^N") THEN
    MATCH_MP_TAC SPAN_INDUCT THEN REWRITE_TAC [] THEN CONJ_TAC THENL
     [REWRITE_TAC [columns, FORALL_IN_GSPEC] THEN
      X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN REWRITE_TAC [IN] THEN
      EXISTS_TAC (← q r"basis i:real^M") THEN ASM_SIMP_TAC [MATRIX_VECTOR_MUL_BASIS],
      REWRITE_TAC [subspace, IN] THEN
      MESON_TAC [MATRIX_VECTOR_MUL_RZERO, MATRIX_VECTOR_MUL_RMUL,
                 MATRIX_VECTOR_MUL_ADD_LDISTRIB]])

  let MATRIX_AUGMENTED_LINEAR_EQUATIONS ← prove
   r"!A:real^N^M y:real^N.
        (?x. transp A ** x = y) <=>
        rank(pastecart A (rowvector y)) = rank A"
   (REWRITE_TAC [RANK_ROW, rows] THEN ONCE_REWRITE_TAC [SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC [← GSYM numseg, DIMINDEX_FINITE_SUM, DIMINDEX_1] THEN
    SIMP_TAC [← GSYM ADD1, NUMSEG_REC, ← ARITH_RULE (← q r"1 <= SUC n")] THEN
    REWRITE_TAC [IMAGE_CLAUSES, DIM_INSERT] THEN REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [← SET_RULE (← q r"(?x. f x = y) <=> y IN {z | ?x. f x = z}")] THEN
    REWRITE_TAC [← GSYM SPAN_COLUMNSPACE, COLUMNS_TRANSP] THEN
    SUBGOAL_THEN
      (← q r"IMAGE (\i. row i (pastecart (A:real^N^M) (rowvector(y:real^N))))
           (1..dimindex (:M)) =
     rows A")
    SUBST1_TAC THENL
     [REWRITE_TAC [rows] THEN MATCH_MP_TAC (← SET_RULE (← q
       r"{x | P x} = s /\ (!x. x IN s ==> f x = g x)
      ==> IMAGE f s = {g x | P x}")) THEN
      SIMP_TAC [numseg, FORALL_IN_GSPEC, row, pastecart, LAMBDA_BETA, CART_EQ,
                LAMBDA_ETA, DIMINDEX_FINITE_SUM,
                ← ARITH_RULE (← q r"i:num <= n ==> i <= n + m")],
      REWRITE_TAC [ETA_AX, ← GSYM SIMPLE_IMAGE, IN_NUMSEG, ← GSYM rows]] THEN
    SUBGOAL_THEN
     (← q r"row (SUC(dimindex(:M))) (pastecart (A:real^N^M) (rowvector(y:real^N))) = y")
    SUBST1_TAC THENL
     [SIMP_TAC [row, pastecart, CART_EQ, LAMBDA_BETA, DIMINDEX_1, rowvector,
                DIMINDEX_FINITE_SUM, DIMINDEX_GE_1, ← ARITH_RULE (← q r"1 <= SUC m"),
                ← ARITH_RULE (← q r"1 <= m ==> SUC m <= m + 1"), LAMBDA_ETA,
                ← ARITH_RULE (← q r"~(SUC m <= m) /\ SUC m - m = 1"), DIMINDEX_1, ARITH],
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ARITH_TAC])

  return { rank, RANK_ROW, RANK_TRANSP, MATRIX_VECTOR_MUL_BASIS, COLUMNS_IMAGE_BASIS,
           RANK_DIM_IM, RANK_BOUND, FULL_RANK_INJECTIVE, FULL_RANK_SURJECTIVE, RANK_I,
           MATRIX_FULL_LINEAR_EQUATIONS, MATRIX_NONFULL_LINEAR_EQUATIONS_EQ,
           MATRIX_NONFULL_LINEAR_EQUATIONS, MATRIX_TRIVIAL_LINEAR_EQUATIONS, RANK_EQ_0,
           RANK_0, RANK_MUL_LE_RIGHT, RANK_MUL_LE_LEFT, SPAN_COLUMNSPACE,
           MATRIX_AUGMENTED_LINEAR_EQUATIONS }

/- ------------------------------------------------------------------------- -/
/- Some bounds on components etc. relative to operator norm.                -/
/- (vectors.ml 6999-7107)                                                     -/
/- ------------------------------------------------------------------------- -/

structure ONormMat where
  NORM_COLUMN_LE_ONORM : thm
  MATRIX_COMPONENT_LE_ONORM : thm
  COMPONENT_LE_ONORM : thm
  ONORM_LE_MATRIX_COMPONENT_SUM : thm
  ONORM_LE_MATRIX_COMPONENT : thm
  MATRIX_RATIONAL_APPROXIMATION : thm
  deriving Inhabited

@[nospecialize]
def setupONormMat [HolBase] (D : VectorsDeps) (BNorm1 : Norm1) (BNorm2 : Norm2)
    (BBasis : Basis) (BMatrix : Matrix) (BMatProps : MatProps) (BInvertible : Invertible)
    (BONorm : ONorm) (BRank : Rank) : ExceptT String IO ONormMat := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, .. } := D
  let { CARD_NUMSEG_1, CONJ_ASSOC, DIMINDEX_GE_1, DIMINDEX_NONZERO, FINITE_INDEX_INRANGE,
        FINITE_NUMSEG, .. } := D.core1
  let { IMP_CONJ, IMP_CONJ_ALT, IMP_IMP, LAMBDA_BETA, LE_1, MONO_EXISTS, .. } := D.core2
  let { REAL_ABS_MUL, REAL_ABS_POS, REAL_ABS_SUB, REAL_DIV_LMUL, REAL_LET_TRANS,
        REAL_LE_LMUL, REAL_LE_REFL, REAL_LE_RMUL, REAL_LE_TRANS, REAL_LT_DIV,
        REAL_LT_IMP_LE, REAL_MUL_ASSOC, REAL_MUL_RID, .. } := D.core3
  let { REAL_OF_NUM_EQ, REAL_OF_NUM_LT, REAL_POW_2, RIGHT_FORALL_IMP_THM,
        RIGHT_IMP_FORALL_THM, SUM_ABS_NUMSEG, SUM_CONST, .. } := D.core4
  let { SUM_LE_NUMSEG, SUM_RMUL, .. } := D.core5
  let { RATIONAL_APPROXIMATION, .. } := D.lib
  let { LAMBDA_SKOLEM, REAL_HALF, .. } := D.misc
  let { COMPONENT_LE_NORM, NORM_CAUCHY_SCHWARZ_ABS, NORM_POS_LE, .. } := BNorm1
  let { NORM_LE_L1, .. } := BNorm2
  let { NORM_BASIS, .. } := BBasis
  let { MATRIX_SUB_COMPONENT, column, matrix_vector_mul, .. } := BMatrix
  let { MATRIX_MUL_DOT, .. } := BMatProps
  let { MATRIX_VECTOR_MUL, MATRIX_VECTOR_MUL_LINEAR, .. } := BInvertible
  let { ONORM, .. } := BONorm
  let { MATRIX_VECTOR_MUL_BASIS, .. } := BRank
  -- @@SCOPE END

  let NORM_COLUMN_LE_ONORM ← prove
   r"!A:real^N^M i. norm(column i A) <= onorm(\x. A ** x)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [column] THEN
    SUBGOAL_THEN (← q r"?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$i = z$l")
    CHOOSE_TAC THENL [REWRITE_TAC [FINITE_INDEX_INRANGE], ALL_TAC] THEN
    MP_TAC (← ISPEC (← q r"\x:real^N. (A:real^N^M) ** x") ONORM) THEN
    REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"basis l:real^N") o CONJUNCT1) THEN
    ASM_SIMP_TAC [MATRIX_VECTOR_MUL_BASIS, NORM_BASIS, column, REAL_MUL_RID])

  let MATRIX_COMPONENT_LE_ONORM ← prove
   r"!A:real^N^M i j. abs(A$i$j) <= onorm(\x. A ** x)"
   (REPEAT GEN_TAC THEN
    SUBGOAL_THEN (← q r"?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k")
    CHOOSE_TAC THENL [REWRITE_TAC [FINITE_INDEX_INRANGE], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"?l. 1 <= l /\ l <= dimindex(:N) /\ !z:real^N. z$j = z$l")
    CHOOSE_TAC THENL [REWRITE_TAC [FINITE_INDEX_INRANGE], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"norm(column l (A:real^N^M))") THEN
    REWRITE_TAC [NORM_COLUMN_LE_ONORM] THEN
    MP_TAC (← ISPECL [← q r"column l (A:real^N^M)", ← q r"k:num"]
          COMPONENT_LE_NORM) THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] REAL_LE_TRANS) THEN
    ASM_SIMP_TAC [column, LAMBDA_BETA, REAL_LE_REFL])

  let COMPONENT_LE_ONORM ← prove
   r"!f:real^M->real^N i j. linear f ==> abs(matrix f$i$j) <= onorm f"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← MATCH_MP MATRIX_VECTOR_MUL th])) THEN
    REWRITE_TAC [MATRIX_COMPONENT_LE_ONORM])

  let ONORM_LE_MATRIX_COMPONENT_SUM ← prove
   r"!A:real^N^M.
        onorm(\x. A ** x) <=
        sum (1..dimindex(:M))
            (\i. sum(1..dimindex(:N)) (\j. abs(A$i$j)))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← CONJUNCT2
     (← MATCH_MP ONORM (← SPEC_ALL MATRIX_VECTOR_MUL_LINEAR))) THEN
    X_GEN_TAC (← q r"x:real^N") THEN
    W (MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    REWRITE_TAC [← GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
    ASM_SIMP_TAC [matrix_vector_mul, LAMBDA_BETA] THEN
    W (MP_TAC o PART_MATCH lhand SUM_ABS_NUMSEG o lhand o snd) THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC (← q r"j:num") THEN STRIP_TAC THEN
    SIMP_TAC [REAL_ABS_MUL, REAL_LE_LMUL, COMPONENT_LE_NORM, REAL_ABS_POS])

  let ONORM_LE_MATRIX_COMPONENT ← prove
   r"!A:real^N^M B.
        (!i j. 1 <= i /\ i <= dimindex(:M) /\
               1 <= j /\ j <= dimindex(:N)
               ==> abs(A$i$j) <= B)
        ==> onorm(\x. A ** x) <= &(dimindex(:M)) * &(dimindex(:N)) * B"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← CONJUNCT2
     (← MATCH_MP ONORM (← SPEC_ALL MATRIX_VECTOR_MUL_LINEAR))) THEN
    X_GEN_TAC (← q r"x:real^N") THEN
    W (MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    REWRITE_TAC [← GSYM REAL_MUL_ASSOC, REAL_POW_2] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV)
     [← GSYM CARD_NUMSEG_1] THEN
    SIMP_TAC [← GSYM SUM_CONST, FINITE_NUMSEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    SIMP_TAC [MATRIX_MUL_DOT, LAMBDA_BETA] THEN
    X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN
    W (MP_TAC o PART_MATCH lhand NORM_CAUCHY_SCHWARZ_ABS o lhand o snd) THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    REWRITE_TAC [REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC [NORM_POS_LE] THEN
    W (MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV)
     [← GSYM CARD_NUMSEG_1] THEN
    SIMP_TAC [← GSYM SUM_CONST, FINITE_NUMSEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    ASM_SIMP_TAC [])

  let MATRIX_RATIONAL_APPROXIMATION ← prove
   r"!A:real^N^M e.
        &0 < e
        ==> ?B. (!i j. 1 <= i /\ i <= dimindex(:M) /\
                       1 <= j /\ j <= dimindex(:N)
                       ==> rational(B$i$j)) /\
                onorm(\x. (A - B) ** x) < e"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"!i j. 1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:N)
          ==> ?q. rational(q) /\
                  abs(q - (A:real^N^M)$i$j) <
                  e / &2 / &(dimindex(:M)) / &(dimindex(:N))")
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC RATIONAL_APPROXIMATION THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, LE_1, DIMINDEX_GE_1, REAL_HALF],
      ONCE_REWRITE_TAC [← TAUT (← q r"p /\ q /\ r ==> s <=> p /\ q ==> r ==> s")] THEN
      REWRITE_TAC [RIGHT_FORALL_IMP_THM, LAMBDA_SKOLEM]] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"B:real^N^M") THEN
    GEN_REWRITE_TAC (BINOP_CONV o TOP_DEPTH_CONV)
     [RIGHT_IMP_FORALL_THM, IMP_IMP, ← GSYM CONJ_ASSOC] THEN
    REWRITE_TAC [← GSYM MATRIX_SUB_COMPONENT] THEN
    STRIP_TAC THEN ASM_SIMP_TAC [] THEN TRANS_TAC REAL_LET_TRANS
      (← q r"&(dimindex(:M)) * &(dimindex(:N)) *
     e / &2 / &(dimindex(:M)) / &(dimindex(:N))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ONORM_LE_MATRIX_COMPONENT THEN
      ASM_MESON_TAC [MATRIX_SUB_COMPONENT, REAL_ABS_SUB, REAL_LT_IMP_LE],
      SIMP_TAC [REAL_DIV_LMUL, REAL_OF_NUM_EQ, DIMINDEX_NONZERO] THEN
      ASM_REAL_ARITH_TAC])

  return { NORM_COLUMN_LE_ONORM, MATRIX_COMPONENT_LE_ONORM, COMPONENT_LE_ONORM,
           ONORM_LE_MATRIX_COMPONENT_SUM, ONORM_LE_MATRIX_COMPONENT,
           MATRIX_RATIONAL_APPROXIMATION }

/- ------------------------------------------------------------------------- -/
/- Basic lemmas about hyperplanes and halfspaces; a non-injective linear    -/
/- function maps into a hyperplane.  (vectors.ml 7113-7240)                  -/
/- ------------------------------------------------------------------------- -/

structure Hyperplane where
  HYPERPLANE_EQ_EMPTY : thm
  HYPERPLANE_EQ_UNIV : thm
  HALFSPACE_EQ_EMPTY_LT : thm
  HALFSPACE_EQ_EMPTY_GT : thm
  HALFSPACE_EQ_EMPTY_LE : thm
  HALFSPACE_EQ_EMPTY_GE : thm
  ADJOINT_INJECTIVE : thm
  ADJOINT_SURJECTIVE : thm
  ADJOINT_INJECTIVE_INJECTIVE : thm
  ADJOINT_INJECTIVE_INJECTIVE_0 : thm
  TRANSP_INJECTIVE : thm
  TRANSP_SURJECTIVE : thm
  LINEAR_SINGULAR_INTO_HYPERPLANE : thm
  LINEAR_SINGULAR_IMAGE_HYPERPLANE : thm
  deriving Inhabited

@[nospecialize]
def setupHyperplane [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BDotProps : DotProps) (BLinear : Linear) (BAdjoint : Adjoint) (BMatProps : MatProps)
    (BInvertible : Invertible) (BIso : Iso) (BRank : Rank) :
    ExceptT String IO Hyperplane := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, ASM_REAL_ARITH_TAC, MESON, MESON_TAC, REAL_ARITH_TAC, SET_RULE,
        SET_TAC, .. } := D
  let { EXTENSION, FORALL_IN_IMAGE, .. } := D.core1
  let { IN_ELIM_THM, IN_UNIV, MEMBER_NOT_EMPTY, NOT_IN_EMPTY, .. } := D.core2
  let { REAL_DIV_RMUL, REAL_LE_NEG2, REAL_LT_NEG2, .. } := D.core3
  let { SUBSET, .. } := D.core4
  let { UNIV_NOT_EMPTY, real_ge, real_gt, .. } := D.core5
  let { VECTOR_NEG_EQ_0, .. } := BVectorArith
  let { DOT_EQ_0, DOT_LNEG, DOT_LZERO, DOT_RMUL, DOT_SYM, FORALL_DOT_EQ_0, .. } := BDotProps
  let { LINEAR_INJECTIVE_0, .. } := BLinear
  let { ADJOINT_ADJOINT, ADJOINT_LINEAR, ADJOINT_WORKS, .. } := BAdjoint
  let { TRANSP_TRANSP, .. } := BMatProps
  let { ADJOINT_MATRIX, MATRIX_ADJOINT, MATRIX_VECTOR_MUL_LINEAR, MATRIX_WORKS,
        .. } := BInvertible
  let { LINEAR_INJECTIVE_IMP_SURJECTIVE, LINEAR_SURJECTIVE_IMP_INJECTIVE, .. } := BIso
  let { FULL_RANK_INJECTIVE, FULL_RANK_SURJECTIVE, RANK_TRANSP, .. } := BRank
  -- @@SCOPE END

  let HYPERPLANE_EQ_EMPTY ← prove
   r"!a:real^N b. {x | a dot x = b} = {} <=> a = vec 0 /\ ~(b = &0)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY] THEN
    ASM_CASES_TAC (← q r"a:real^N = vec 0") THEN ASM_REWRITE_TAC [DOT_LZERO] THENL
     [MESON_TAC [],
      DISCH_THEN (MP_TAC o SPEC (← q r"b / (a dot a) % a:real^N")) THEN
      ASM_SIMP_TAC [DOT_RMUL, REAL_DIV_RMUL, DOT_EQ_0]])

  let HYPERPLANE_EQ_UNIV ← prove
   r"!a b. {x | a dot x = b} = (:real^N) <=> a = vec 0 /\ b = &0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_UNIV] THEN
    ASM_CASES_TAC (← q r"a:real^N = vec 0") THEN ASM_REWRITE_TAC [DOT_LZERO] THENL
     [MESON_TAC [],
      DISCH_THEN (MP_TAC o SPEC (← q r"(b + &1) / (a dot a) % a:real^N")) THEN
      ASM_SIMP_TAC [DOT_RMUL, REAL_DIV_RMUL, DOT_EQ_0] THEN REAL_ARITH_TAC])

  let HALFSPACE_EQ_EMPTY_LT ← prove
   r"!a:real^N b. {x | a dot x < b} = {} <=> a = vec 0 /\ b <= &0"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"a:real^N = vec 0") THENL
     [ASM_SIMP_TAC [DOT_LZERO, ← SET_RULE (← q r"{x | p} = if p then UNIV else {}")] THEN
      COND_CASES_TAC THEN REWRITE_TAC [UNIV_NOT_EMPTY] THEN ASM_REAL_ARITH_TAC,
      ASM_REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM] THEN
      EXISTS_TAC (← q r"(b - &1) / (a dot a) % a:real^N") THEN
      ASM_SIMP_TAC [DOT_RMUL, REAL_DIV_RMUL, DOT_EQ_0] THEN
      REAL_ARITH_TAC])

  let HALFSPACE_EQ_EMPTY_GT ← prove
   r"!a:real^N b. {x | a dot x > b} = {} <=> a = vec 0 /\ b >= &0"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"--a:real^N", ← q r"--b:real"] HALFSPACE_EQ_EMPTY_LT) THEN
    SIMP_TAC [real_gt, DOT_LNEG, REAL_LT_NEG2, VECTOR_NEG_EQ_0] THEN
    DISCH_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC)

  let HALFSPACE_EQ_EMPTY_LE ← prove
   r"!a:real^N b. {x | a dot x <= b} = {} <=> a = vec 0 /\ b < &0"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"a:real^N = vec 0") THENL
     [ASM_SIMP_TAC [DOT_LZERO, ← SET_RULE (← q r"{x | p} = if p then UNIV else {}")] THEN
      COND_CASES_TAC THEN REWRITE_TAC [UNIV_NOT_EMPTY] THEN ASM_REAL_ARITH_TAC,
      ASM_REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM] THEN
      EXISTS_TAC (← q r"(b - &1) / (a dot a) % a:real^N") THEN
      ASM_SIMP_TAC [DOT_RMUL, REAL_DIV_RMUL, DOT_EQ_0] THEN
      REAL_ARITH_TAC])

  let HALFSPACE_EQ_EMPTY_GE ← prove
   r"!a:real^N b. {x | a dot x >= b} = {} <=> a = vec 0 /\ b > &0"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"--a:real^N", ← q r"--b:real"] HALFSPACE_EQ_EMPTY_LE) THEN
    SIMP_TAC [real_ge, DOT_LNEG, REAL_LE_NEG2, VECTOR_NEG_EQ_0] THEN
    DISCH_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC)

  let ADJOINT_INJECTIVE ← prove
   r"!f:real^M->real^N.
        linear f
        ==> ((!x y. adjoint f x = adjoint f y ==> x = y) <=>
             (!y. ?x. f x = y))"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o GSYM o MATCH_MP MATRIX_WORKS o MATCH_MP
     ADJOINT_LINEAR) THEN
    FIRST_ASSUM (ASSUME_TAC o GSYM o MATCH_MP MATRIX_WORKS) THEN
    ASM_REWRITE_TAC [← GSYM FULL_RANK_INJECTIVE, ← GSYM FULL_RANK_SURJECTIVE] THEN
    ASM_SIMP_TAC [MATRIX_ADJOINT, RANK_TRANSP])

  let ADJOINT_SURJECTIVE ← prove
   r"!f:real^M->real^N.
        linear f
        ==> ((!y. ?x. adjoint f x = y) <=> (!x y. f x = f y ==> x = y))"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
        [← GSYM (← MATCH_MP ADJOINT_ADJOINT th)])) THEN
    ASM_SIMP_TAC [ADJOINT_INJECTIVE, ADJOINT_LINEAR])

  let ADJOINT_INJECTIVE_INJECTIVE ← prove
   r"!f:real^N->real^N.
        linear f
        ==> ((!x y. adjoint f x = adjoint f y ==> x = y) <=>
             (!x y. f x = f y ==> x = y))"
   (SIMP_TAC [ADJOINT_INJECTIVE] THEN
    MESON_TAC [LINEAR_INJECTIVE_IMP_SURJECTIVE,
               LINEAR_SURJECTIVE_IMP_INJECTIVE])

  let ADJOINT_INJECTIVE_INJECTIVE_0 ← prove
   r"!f:real^N->real^N.
        linear f
        ==> ((!x. adjoint f x = vec 0 ==> x = vec 0) <=>
             (!x. f x = vec 0 ==> x = vec 0))"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP ADJOINT_INJECTIVE_INJECTIVE) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP ADJOINT_LINEAR) THEN
    ASM_MESON_TAC [LINEAR_INJECTIVE_0])

  let TRANSP_INJECTIVE ← prove
   r"!m:real^M^N.
        (!x y:real^N. transp m ** x = transp m ** y ==> x = y) <=>
        IMAGE (\x. m ** x) (:real^M) = (:real^N)"
   (GEN_TAC THEN
    MP_TAC (← ISPEC (← q r"\x:real^M. (m:real^M^N) ** x") ADJOINT_INJECTIVE) THEN
    REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR, ADJOINT_MATRIX] THEN SET_TAC [])

  let TRANSP_SURJECTIVE ← prove
   r"!m:real^M^N.
        IMAGE (\x. transp m ** x) (:real^N) = (:real^M) <=>
        (!x y:real^M. m ** x = m ** y ==> x = y)"
   (REWRITE_TAC [← GSYM TRANSP_INJECTIVE, TRANSP_TRANSP])

  let LINEAR_SINGULAR_INTO_HYPERPLANE ← prove
   r"!f:real^N->real^N.
        linear f
        ==> (~(!x y. f(x) = f(y) ==> x = y) <=>
             ?a. ~(a = vec 0) /\ !x. a dot f(x) = &0)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [DOT_SYM] THEN
    ASM_SIMP_TAC [ADJOINT_WORKS, FORALL_DOT_EQ_0] THEN
    REWRITE_TAC [← MESON [] (← q r"(?a. ~p a /\ q a) <=> ~(!a. q a ==> p a)")] THEN
    ASM_SIMP_TAC [ADJOINT_INJECTIVE_INJECTIVE_0, LINEAR_INJECTIVE_0])

  let LINEAR_SINGULAR_IMAGE_HYPERPLANE ← prove
   r"!f:real^N->real^N.
        linear f /\ ~(!x y. f(x) = f(y) ==> x = y)
        ==> ?a. ~(a = vec 0) /\ !s. IMAGE f s SUBSET {x | a dot x = &0}"
   (GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC [LINEAR_SINGULAR_INTO_HYPERPLANE] THEN
    SIMP_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN MESON_TAC [])

  return { HYPERPLANE_EQ_EMPTY, HYPERPLANE_EQ_UNIV, HALFSPACE_EQ_EMPTY_LT,
           HALFSPACE_EQ_EMPTY_GT, HALFSPACE_EQ_EMPTY_LE, HALFSPACE_EQ_EMPTY_GE,
           ADJOINT_INJECTIVE, ADJOINT_SURJECTIVE, ADJOINT_INJECTIVE_INJECTIVE,
           ADJOINT_INJECTIVE_INJECTIVE_0, TRANSP_INJECTIVE, TRANSP_SURJECTIVE,
           LINEAR_SINGULAR_INTO_HYPERPLANE, LINEAR_SINGULAR_IMAGE_HYPERPLANE }

/- ------------------------------------------------------------------------- -/
/- Orthogonal bases, Gram-Schmidt process, and related theorems.            -/
/- (vectors.ml 7243-7435)                                                     -/
/- ------------------------------------------------------------------------- -/

structure Gram1 where
  SPAN_DELETE_0 : thm
  DIM_BASIS_IMAGE : thm
  SPAN_IMAGE_SCALE : thm
  DIM_IMAGE_SCALE : thm
  PAIRWISE_ORTHOGONAL_INDEPENDENT : thm
  PAIRWISE_ORTHOGONAL_IMP_FINITE : thm
  GRAM_SCHMIDT_STEP : thm
  ORTHOGONAL_EXTENSION : thm
  ORTHOGONAL_EXTENSION_STRONG : thm
  ORTHONORMAL_EXTENSION : thm
  deriving Inhabited

@[nospecialize]
def setupGram1 [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BDotProps : DotProps) (BNorm1 : Norm1) (BVSum2 : VSum2) (BBasis : Basis)
    (BOrth : Orth) (BSubspace : Subspace) (BSpan1 : Span1) (BSpan2 : Span2)
    (BDim1 : Dim1) (BDim2 : Dim2) (BRowSpace : RowSpace) : ExceptT String IO Gram1 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, .. } := D
  let { CARD_IMAGE_INJ, DELETE_SUBSET, DE_MORGAN_THM, EQ_TRANS, FINITE_DELETE,
        FINITE_INDUCT_STRONG, FINITE_INSERT, FINITE_INTER, FINITE_NUMSEG,
        FORALL_IN_IMAGE, .. } := D.core1
  let { HAS_SIZE, IMP_CONJ, INTER_SUBSET, IN_DELETE, IN_ELIM_THM, IN_IMAGE, IN_INSERT,
        IN_INTER, IN_NUMSEG, IN_UNION, LEFT_IMP_EXISTS_THM, MONO_EXISTS, NOT_EXISTS_THM,
        .. } := D.core2
  let { PAIRWISE_MONO, REAL_ABS_INV, REAL_DIV_RMUL, REAL_ENTIRE, REAL_INV_1,
        REAL_INV_EQ_0, REAL_INV_EQ_1, REAL_MUL_LINV, REAL_MUL_RINV, .. } := D.core3
  let { REAL_MUL_RZERO, REAL_SUB_0, RIGHT_FORALL_IMP_THM, SUBSET, SUBSET_ANTISYM,
        SUBSET_TRANS, SUM_0, SUM_DELTA, SUM_EQ, .. } := D.core4
  let { UNION_EMPTY, UNION_SUBSET, pairwise, .. } := D.core5
  let { VECTOR_ARITH, VECTOR_MUL_ASSOC, VECTOR_MUL_LID, VECTOR_MUL_RZERO, VECTOR_SUB_RZERO,
        .. } := BVectorArith
  let { DOT_EQ_0, DOT_LMUL, DOT_LZERO, DOT_RMUL, DOT_RSUB, DOT_SYM, .. } := BDotProps
  let { NORM_EQ_0, NORM_MUL, REAL_ABS_NORM, VECTOR_MUL_EQ_0, .. } := BNorm1
  let { DOT_RSUM, .. } := BVSum2
  let { BASIS_EQ_0, BASIS_INJ, .. } := BBasis
  let { ORTHOGONAL_SYM, orthogonal, .. } := BOrth
  let { SPAN_CLAUSES, SPAN_MONO, SUBSPACE_SPAN, dependent, independent, .. } := BSubspace
  let { SPAN_BREAKDOWN_EQ, SPAN_MUL, SPAN_NEG, SPAN_SUBSET_SUBSPACE, SPAN_SUPERSET,
        SPAN_UNION, SPAN_VSUM, .. } := BSpan1
  let { EQ_SPAN_INSERT_EQ, INDEPENDENT_BASIS_IMAGE, SPAN_EXPLICIT, .. } := BSpan2
  let { BASIS_SUBSPACE_EXISTS, INDEPENDENT_IMP_FINITE, SPAN_EQ, .. } := BDim1
  let { DIM_EQ_CARD, DIM_SPAN, .. } := BDim2
  let { ORTHOGONAL_TO_SPAN_EQ, .. } := BRowSpace
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let SPAN_DELETE_0 ← prove
   r"!s:real^N->bool. span(s DELETE vec 0) = span s"
   (GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    SIMP_TAC [DELETE_SUBSET, SPAN_MONO] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC (← q r"span((vec 0:real^N) INSERT (s DELETE vec 0))") THEN CONJ_TAC THENL
     [MATCH_MP_TAC SPAN_MONO THEN SET_TAC [],
      SIMP_TAC [SUBSET, SPAN_BREAKDOWN_EQ, VECTOR_MUL_RZERO, VECTOR_SUB_RZERO]])

  let DIM_BASIS_IMAGE ← prove
   r"!k. dim(IMAGE basis k:real^N->bool) = CARD((1..dimindex(:N)) INTER k)"
   (GEN_TAC THEN TRANS_TAC EQ_TRANS
     (← q r"dim(IMAGE basis ((1..dimindex(:N)) INTER k):real^N->bool)") THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC [← GSYM DIM_SPAN] THEN
      ONCE_REWRITE_TAC [← GSYM SPAN_DELETE_0] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC (← SET_RULE (← q
       r"(!x. ~(f x = a) <=> x IN k)
      ==> IMAGE f s DELETE a = IMAGE f (k INTER s) DELETE a")) THEN
      REWRITE_TAC [BASIS_EQ_0],
      W (MP_TAC o PART_MATCH (lhand o rand) DIM_EQ_CARD o lhand o snd) THEN
      REWRITE_TAC [INDEPENDENT_BASIS_IMAGE, INTER_SUBSET] THEN
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
      SIMP_TAC [FINITE_INTER, FINITE_NUMSEG, IN_INTER, IN_NUMSEG] THEN
      MESON_TAC [BASIS_INJ]])

  let SPAN_IMAGE_SCALE ← prove
   r"!c s. (!x. x IN s ==> ~(c x = &0))
         ==> span (IMAGE (\x:real^N. c(x) % x) s) = span s"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    CONJ_TAC THEN MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
    REWRITE_TAC [SUBSPACE_SPAN, SUBSET, FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC [SPAN_MUL, SPAN_SUPERSET] THEN
    X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"x:real^N = inv(c x) % c x % x") SUBST1_TAC THENL
     [ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, VECTOR_MUL_LID],
      MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN
      ASM SET_TAC []])

  let DIM_IMAGE_SCALE ← prove
   r"!c s:real^N->bool.
        (!x. x IN s ==> ~(c x = &0)) ==> dim(IMAGE (\x. c x % x) s) = dim s"
   (ONCE_REWRITE_TAC [← GSYM DIM_SPAN] THEN SIMP_TAC [SPAN_IMAGE_SCALE])

  let PAIRWISE_ORTHOGONAL_INDEPENDENT ← prove
   r"!s:real^N->bool.
        pairwise orthogonal s /\ ~(vec 0 IN s) ==> independent s"
   (REWRITE_TAC [pairwise, orthogonal] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [independent, dependent] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"a:real^N") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC [SPAN_EXPLICIT, IN_ELIM_THM, NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"t:real^N->bool", ← q r"u:real^N->real"] THEN
    REWRITE_TAC [SUBSET, IN_DELETE] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o AP_TERM (← q r"\x:real^N. a dot x")) THEN
    ASM_SIMP_TAC [DOT_RSUM, DOT_RMUL, REAL_MUL_RZERO, SUM_0] THEN
    ASM_MESON_TAC [DOT_EQ_0])

  let PAIRWISE_ORTHOGONAL_IMP_FINITE ← prove
   r"!s:real^N->bool. pairwise orthogonal s ==> FINITE s"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"independent (s DELETE (vec 0:real^N))") MP_TAC THENL
     [MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN
      REWRITE_TAC [IN_DELETE] THEN MATCH_MP_TAC PAIRWISE_MONO THEN
      EXISTS_TAC (← q r"s:real^N->bool") THEN
      ASM_SIMP_TAC [SUBSET, IN_DELETE],
      DISCH_THEN (MP_TAC o MATCH_MP INDEPENDENT_IMP_FINITE) THEN
      REWRITE_TAC [FINITE_DELETE]])

  let GRAM_SCHMIDT_STEP ← prove
   r"!s a x.
        pairwise orthogonal s /\ x IN span s
        ==> orthogonal x (a - vsum s (\b:real^N. (b dot a) / (b dot b) % b))"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [ORTHOGONAL_SYM] ORTHOGONAL_TO_SPAN_EQ] THEN
    X_GEN_TAC (← q r"s:real^N->bool") THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"x:real^N"] THEN DISCH_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP PAIRWISE_ORTHOGONAL_IMP_FINITE) THEN
    REWRITE_TAC [orthogonal, DOT_RSUB] THEN ASM_SIMP_TAC [DOT_RSUM] THEN
    REWRITE_TAC [REAL_SUB_0, DOT_RMUL] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"sum s (\y:real^N. if y = x then y dot a else &0)") THEN
    CONJ_TAC THENL [ASM_SIMP_TAC [SUM_DELTA, DOT_SYM], ALL_TAC] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q r"y:real^N") THEN DISCH_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [pairwise, orthogonal]) THEN
    ASM_CASES_TAC (← q r"x:real^N = y") THEN ASM_SIMP_TAC [DOT_LMUL, REAL_MUL_RZERO] THEN
    ASM_CASES_TAC (← q r"y:real^N = vec 0") THEN
    ASM_SIMP_TAC [REAL_DIV_RMUL, DOT_EQ_0, DOT_LZERO, REAL_MUL_RZERO])

  let ORTHOGONAL_EXTENSION ← do
    let lemma ← prove
     r"!t s:real^N->bool.
        FINITE t /\ FINITE s /\ pairwise orthogonal s
        ==> ?u. pairwise orthogonal (s UNION u) /\
                span (s UNION u) = span (s UNION t)"
     (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"{}:real^N->bool") THEN
        ASM_REWRITE_TAC [UNION_EMPTY],
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [← q r"a:real^N", ← q r"t:real^N->bool"] THEN
      REWRITE_TAC [pairwise, orthogonal] THEN REPEAT STRIP_TAC THEN
      ABBREV_TAC (← q r"a' = a - vsum s (\b:real^N. (b dot a) / (b dot b) % b)") THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(a':real^N) INSERT s")) THEN
      ASM_REWRITE_TAC [FINITE_INSERT] THEN ANTS_TAC THENL
       [SUBGOAL_THEN (← q r"!x:real^N. x IN s ==> a' dot x = &0")
         (fun th => REWRITE_TAC [IN_INSERT] THEN ASM_MESON_TAC [DOT_SYM, th]) THEN
        REPEAT STRIP_TAC THEN EXPAND_TAC "a'" THEN
        REWRITE_TAC [← GSYM orthogonal] THEN ONCE_REWRITE_TAC [ORTHOGONAL_SYM] THEN
        MATCH_MP_TAC GRAM_SCHMIDT_STEP THEN
        ASM_SIMP_TAC [pairwise, orthogonal, SPAN_CLAUSES],
        DISCH_THEN (X_CHOOSE_THEN (← q r"u:real^N->bool") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"(a':real^N) INSERT u") THEN
        ASM_REWRITE_TAC [← SET_RULE (← q r"s UNION a INSERT u = a INSERT s UNION u")] THEN
        REWRITE_TAC [← SET_RULE (← q r"(x INSERT s) UNION t = x INSERT (s UNION t)")] THEN
        MATCH_MP_TAC EQ_SPAN_INSERT_EQ THEN EXPAND_TAC "a'" THEN
        REWRITE_TAC [← va r"a - x - a:real^N = --x"] THEN
        MATCH_MP_TAC SPAN_NEG THEN MATCH_MP_TAC SPAN_VSUM THEN
        ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC SPAN_MUL THEN ASM_SIMP_TAC [SPAN_SUPERSET, IN_UNION]])
    prove
     r"!s t:real^N->bool.
        pairwise orthogonal s
        ==> ?u. pairwise orthogonal (s UNION u) /\
                span (s UNION u) = span (s UNION t)"
     (REPEAT STRIP_TAC THEN
      MP_TAC (← ISPEC (← q r"span t:real^N->bool") BASIS_SUBSPACE_EXISTS) THEN
      REWRITE_TAC [SUBSPACE_SPAN, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"b:real^N->bool") THEN STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"b:real^N->bool", ← q r"s:real^N->bool"] lemma) THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC [HAS_SIZE, PAIRWISE_ORTHOGONAL_IMP_FINITE],
        MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
        ASM_REWRITE_TAC [SPAN_UNION]])

  let ORTHOGONAL_EXTENSION_STRONG ← prove
   r"!s t:real^N->bool.
        pairwise orthogonal s
        ==> ?u. DISJOINT u (vec 0 INSERT s) /\
                pairwise orthogonal (s UNION u) /\
                span (s UNION u) = span (s UNION t)"
   (REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o
      SPEC (← q r"t:real^N->bool") o MATCH_MP ORTHOGONAL_EXTENSION) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:real^N->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"u DIFF ((vec 0:real^N) INSERT s)") THEN REPEAT CONJ_TAC THENL
     [SET_TAC [],
      FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
          PAIRWISE_MONO)) THEN SET_TAC [],
      FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
      GEN_REWRITE_TAC BINOP_CONV [← GSYM SPAN_DELETE_0] THEN
      AP_TERM_TAC THEN SET_TAC []])

  let ORTHONORMAL_EXTENSION ← prove
   r"!s t:real^N->bool.
        pairwise orthogonal s /\ (!x. x IN s ==> norm x = &1)
        ==> ?u. DISJOINT u s /\
                pairwise orthogonal (s UNION u) /\
                (!x. x IN u ==> norm x = &1) /\
                span(s UNION u) = span(s UNION t)"
   (REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o
      SPEC (← q r"t:real^N->bool") o MATCH_MP ORTHOGONAL_EXTENSION_STRONG) THEN
    REWRITE_TAC [← SET_RULE (← q r"DISJOINT u s <=> !x. x IN u ==> ~(x IN s)")] THEN
    REWRITE_TAC [IN_INSERT, DE_MORGAN_THM, pairwise] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:real^N->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"IMAGE (\x:real^N. inv(norm x) % x) u") THEN
    REWRITE_TAC [FORALL_IN_IMAGE, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      ASM_CASES_TAC (← q r"norm(x:real^N) = &1") THEN
      ASM_SIMP_TAC [REAL_INV_1, VECTOR_MUL_LID] THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"x:real^N", ← q r"inv(norm x) % x:real^N"]) THEN
      ASM_REWRITE_TAC [IN_UNION, VECTOR_MUL_EQ_0, REAL_SUB_0, REAL_INV_EQ_1,
        ← va r"x:real^N = a % x <=> (a - &1) % x = vec 0"] THEN
      ASM_CASES_TAC (← q r"x:real^N = vec 0") THENL
       [ASM_MESON_TAC [VECTOR_MUL_RZERO],
        ASM_REWRITE_TAC [orthogonal, DOT_RMUL, REAL_ENTIRE, DOT_EQ_0] THEN
        ASM_REWRITE_TAC [REAL_INV_EQ_0, NORM_EQ_0]],
      REWRITE_TAC [IN_UNION, IN_IMAGE] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC [orthogonal, DOT_LMUL, DOT_RMUL, REAL_ENTIRE, DOT_EQ_0,
                    REAL_INV_EQ_0, NORM_EQ_0] THEN
      REWRITE_TAC [← GSYM orthogonal] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [IN_UNION] THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
      ASM SET_TAC [],
      ASM_SIMP_TAC [NORM_MUL, REAL_MUL_LINV, NORM_EQ_0, REAL_ABS_INV,
                    REAL_ABS_NORM],
      FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
      REWRITE_TAC [SPAN_EQ, UNION_SUBSET] THEN
      SIMP_TAC [SUBSET, FORALL_IN_IMAGE, SPAN_SUPERSET, SPAN_MUL, IN_UNION] THEN
      X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"x:real^N = norm(x) % inv(norm x) % x")
       (fun th => GEN_REWRITE_TAC LAND_CONV [th])
      THENL
       [ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_RINV, NORM_EQ_0, VECTOR_MUL_LID],
        MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN
        REWRITE_TAC [IN_UNION, IN_IMAGE] THEN ASM_MESON_TAC []]])

  return { SPAN_DELETE_0, DIM_BASIS_IMAGE, SPAN_IMAGE_SCALE, DIM_IMAGE_SCALE,
           PAIRWISE_ORTHOGONAL_INDEPENDENT, PAIRWISE_ORTHOGONAL_IMP_FINITE,
           GRAM_SCHMIDT_STEP, ORTHOGONAL_EXTENSION, ORTHOGONAL_EXTENSION_STRONG,
           ORTHONORMAL_EXTENSION }

/- ------------------------------------------------------------------------- -/
/- Orthogonal and orthonormal bases containing a given vector; Bessel's     -/
/- inequality.  (vectors.ml 7436-7532)                                       -/
/- ------------------------------------------------------------------------- -/

structure Gram2 where
  VECTOR_IN_ORTHOGONAL_SPANNINGSET : thm
  VECTOR_IN_ORTHOGONAL_BASIS : thm
  VECTOR_IN_ORTHONORMAL_BASIS : thm
  BESSEL_INEQUALITY : thm
  deriving Inhabited

@[nospecialize]
def setupGram2 [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BDotProps : DotProps) (BNorm1 : Norm1) (BNorm2 : Norm2) (BVSum2 : VSum2)
    (BOrth : Orth) (BSubspace : Subspace) (BSpan2 : Span2) (BDim2 : Dim2)
    (BGram1 : Gram1) : ExceptT String IO Gram2 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_RING, SET_RULE, SET_TAC, .. } := D
  let { ARITH_EQ, EQ_SYM_EQ, EQ_TRANS, FORALL_IN_GSPEC, FORALL_IN_IMAGE, .. } := D.core1
  let { HAS_SIZE, IMP_CONJ, IN_DELETE, IN_IMAGE, IN_NUMSEG, IN_SING, IN_UNION,
        .. } := D.core2
  let { PAIRWISE_SING, REAL_ABS_INV, REAL_ENTIRE, REAL_INV_1, REAL_INV_EQ_0,
        REAL_MUL_LINV, .. } := D.core3
  let { REAL_OF_NUM_EQ, REAL_POW_2, RIGHT_FORALL_IMP_THM, SUBSET, SUM_DELTA, SUM_EQ,
        .. } := D.core4
  let { pairwise, .. } := D.core5
  let { VECTOR_ARITH, VECTOR_MUL_LID, .. } := BVectorArith
  let { DOT_LMUL, DOT_POS_LE, DOT_RMUL, .. } := BDotProps
  let { NORM_0, NORM_EQ_0, NORM_MUL, NORM_POW_2, REAL_ABS_NORM, VECTOR_MUL_EQ_0,
        .. } := BNorm1
  let { NORM_EQ_SQUARE, .. } := BNorm2
  let { DOT_LSUM, DOT_RSUM, .. } := BVSum2
  let { ORTHOGONAL_CLAUSES, orthogonal, .. } := BOrth
  let { SPAN_MONO, .. } := BSubspace
  let { SPAN_STDBASIS, .. } := BSpan2
  let { BASIS_HAS_SIZE_UNIV, .. } := BDim2
  let { ORTHOGONAL_EXTENSION, PAIRWISE_ORTHOGONAL_IMP_FINITE,
        PAIRWISE_ORTHOGONAL_INDEPENDENT, SPAN_DELETE_0, SPAN_IMAGE_SCALE, .. } := BGram1
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let VECTOR_IN_ORTHOGONAL_SPANNINGSET ← prove
   r"!a. ?s. a IN s /\ pairwise orthogonal s /\ span s = (:real^N)"
   (GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"{a:real^N}",
                      ← q r"(IMAGE basis (1..dimindex(:N))):real^N->bool"]
                   ORTHOGONAL_EXTENSION) THEN
    REWRITE_TAC [PAIRWISE_SING] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"u:real^N->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"{a:real^N} UNION u") THEN ASM_REWRITE_TAC [IN_UNION, IN_SING] THEN
    MATCH_MP_TAC (← SET_RULE (← q r"!s. s = UNIV /\ s SUBSET t ==> t = UNIV")) THEN
    EXISTS_TAC (← q r"span {basis i:real^N | 1 <= i /\ i <= dimindex (:N)}") THEN
    CONJ_TAC THENL [REWRITE_TAC [SPAN_STDBASIS], MATCH_MP_TAC SPAN_MONO] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, ← GSYM IN_NUMSEG] THEN SET_TAC [])

  let VECTOR_IN_ORTHOGONAL_BASIS ← prove
   r"!a. ~(a = vec 0)
       ==> ?s. a IN s /\ ~(vec 0 IN s) /\
               pairwise orthogonal s /\
               independent s /\
               s HAS_SIZE (dimindex(:N)) /\
               span s = (:real^N)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"a:real^N") VECTOR_IN_ORTHOGONAL_SPANNINGSET) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"s:real^N->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"s DELETE (vec 0:real^N)") THEN ASM_REWRITE_TAC [IN_DELETE] THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")) THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC (REWRITE_RULE [pairwise]) THEN
      ASM_SIMP_TAC [pairwise, IN_DELETE],
      DISCH_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")) THEN CONJ_TAC THENL
     [MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN ASM_SIMP_TAC [IN_DELETE],
      DISCH_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"b /\ (b ==> a) ==> a /\ b")) THEN CONJ_TAC THENL
     [ASM_MESON_TAC [SPAN_DELETE_0],
      DISCH_TAC THEN ASM_SIMP_TAC [BASIS_HAS_SIZE_UNIV]])

  let VECTOR_IN_ORTHONORMAL_BASIS ← prove
   r"!a. norm a = &1
       ==> ?s. a IN s /\
               pairwise orthogonal s /\
               (!x. x IN s ==> norm x = &1) /\
               independent s /\
               s HAS_SIZE (dimindex(:N)) /\
               span s = (:real^N)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"a:real^N = vec 0") THEN
    ASM_REWRITE_TAC [NORM_0, REAL_OF_NUM_EQ, ARITH_EQ] THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP VECTOR_IN_ORTHOGONAL_BASIS) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"s:real^N->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"IMAGE (\x:real^N. inv(norm x) % x) s") THEN
    CONJ_TAC THENL
     [REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"a:real^N") THEN
      ASM_REWRITE_TAC [REAL_INV_1, VECTOR_MUL_LID],
      ALL_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")) THEN CONJ_TAC THENL
     [REWRITE_TAC [pairwise, IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [pairwise]) THEN
      ASM_MESON_TAC [ORTHOGONAL_CLAUSES],
      DISCH_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")) THEN CONJ_TAC THENL
     [REWRITE_TAC [FORALL_IN_IMAGE, NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
      ASM_MESON_TAC [REAL_MUL_LINV, NORM_EQ_0],
      DISCH_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")) THEN CONJ_TAC THENL
     [MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [IN_IMAGE] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
      SIMP_TAC [VECTOR_MUL_EQ_0, REAL_INV_EQ_0, NORM_EQ_0] THEN ASM_MESON_TAC [],
      DISCH_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"b /\ (b ==> a) ==> a /\ b")) THEN CONJ_TAC THENL
     [ALL_TAC, ASM_SIMP_TAC [BASIS_HAS_SIZE_UNIV]] THEN
    UNDISCH_THEN (← q r"span s = (:real^N)") (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SPAN_IMAGE_SCALE THEN
    REWRITE_TAC [REAL_INV_EQ_0, NORM_EQ_0] THEN
    ASM_MESON_TAC [HAS_SIZE])

  let BESSEL_INEQUALITY ← prove
   r"!s x:real^N.
        pairwise orthogonal s /\ (!x. x IN s ==> norm x = &1)
        ==> sum s (\e. (e dot x) pow 2) <= norm(x) pow 2"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP PAIRWISE_ORTHOGONAL_IMP_FINITE) THEN
    MP_TAC (← ISPEC (← q r"x - vsum s (\e. (e dot x) % e):real^N") DOT_POS_LE) THEN
    REWRITE_TAC [NORM_POW_2, ← va
     r"(a - b:real^N) dot (a - b) = a dot a + b dot b - &2 * b dot a"] THEN
    ASM_SIMP_TAC [DOT_LSUM, REAL_POW_2, DOT_LMUL] THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"t = s ==> &0 <= x + t - &2 * s ==> s <= x")) THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q r"e:real^N") THEN DISCH_TAC THEN
    ASM_SIMP_TAC [DOT_RSUM] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"sum s (\k:real^N. if k = e then e dot x else &0)") THEN
    CONJ_TAC THENL [ALL_TAC, ASM_SIMP_TAC [SUM_DELTA]] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC (← q r"k:real^N") THEN DISCH_TAC THEN
    REWRITE_TAC [DOT_RMUL] THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC [← REAL_RING (← q r"a * x = a <=> a = &0 \/ x = &1")] THEN
      DISJ2_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e:real^N")) THEN
      ASM_REWRITE_TAC [NORM_EQ_SQUARE] THEN REAL_ARITH_TAC,
      RULE_ASSUM_TAC (REWRITE_RULE [pairwise, orthogonal]) THEN
      ASM_SIMP_TAC [REAL_ENTIRE]])

  return { VECTOR_IN_ORTHOGONAL_SPANNINGSET, VECTOR_IN_ORTHOGONAL_BASIS,
           VECTOR_IN_ORTHONORMAL_BASIS, BESSEL_INEQUALITY }

/- ------------------------------------------------------------------------- -/
/- Analogous theorems for existence of orthonormal basis for a subspace;    -/
/- orthogonal vectors to subspaces; orthonormal expansions.                  -/
/- (vectors.ml 7537-7745)                                                     -/
/- ------------------------------------------------------------------------- -/

structure Gram3 where
  ORTHOGONAL_SPANNINGSET_SUBSPACE : thm
  ORTHOGONAL_BASIS_SUBSPACE : thm
  ORTHONORMAL_BASIS_SUBSPACE : thm
  ORTHOGONAL_TO_SUBSPACE_EXISTS_GEN : thm
  ORTHOGONAL_TO_SUBSPACE_EXISTS : thm
  ORTHOGONAL_TO_VECTOR_EXISTS : thm
  SPAN_NOT_UNIV_ORTHOGONAL : thm
  SPAN_NOT_UNIV_SUBSET_HYPERPLANE : thm
  LOWDIM_SUBSET_HYPERPLANE : thm
  VECTOR_EQ_DOT_SPAN : thm
  ORTHONORMAL_BASIS_EXPAND : thm
  ORTHONORMAL_BASIS_EXPAND_DOT : thm
  ORTHONORMAL_BASIS_EXPAND_NORM : thm
  deriving Inhabited

@[nospecialize]
def setupGram3 [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BDotProps : DotProps) (BNorm1 : Norm1) (BNorm2 : Norm2) (BVSum2 : VSum2)
    (BOrth : Orth) (BSubspace : Subspace) (BSpan1 : Span1) (BDim1 : Dim1) (BDim2 : Dim2)
    (BExplicit : Explicit) (BRowSpace : RowSpace) (BGram1 : Gram1) :
    ExceptT String IO Gram3 := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, .. } := D
  let { DE_MORGAN_THM, EQ_SYM_EQ, EQ_TRANS, EXISTS_REFL, FORALL_IN_IMAGE, .. } := D.core1
  let { HAS_SIZE, IMP_CONJ, IMP_IMP, IN_DELETE, IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_SING,
        IN_UNION, LEFT_FORALL_IMP_THM, LEFT_IMP_EXISTS_THM, LE_ANTISYM, LT_REFL,
        MONO_EXISTS, NOT_LE, PAIRWISE_EMPTY, .. } := D.core2
  let { PSUBSET, PSUBSET_ALT, REAL_ABS_INV, REAL_INV_EQ_0, REAL_MUL_LINV, REAL_MUL_RID,
        .. } := D.core3
  let { REAL_MUL_RZERO, REAL_MUL_SYM, REAL_POW_2, REAL_SUB_0, RIGHT_FORALL_IMP_THM, SUBSET,
        SUBSET_ANTISYM_EQ, SUBSET_TRANS, SUBSET_UNIV, SUM_DELTA, SUM_EQ, .. } := D.core4
  let { UNION_EMPTY, pairwise, .. } := D.core5
  let { VECTOR_SUB_EQ, .. } := BVectorArith
  let { DOT_LMUL, DOT_RMUL, DOT_RSUB, DOT_SYM, .. } := BDotProps
  let { NORM_EQ_0, NORM_MUL, NORM_POW_2, REAL_ABS_NORM, VECTOR_MUL_EQ_0, .. } := BNorm1
  let { NORM_EQ_1, .. } := BNorm2
  let { DOT_LSUM, DOT_RSUM, .. } := BVSum2
  let { ORTHOGONAL_CLAUSES, ORTHOGONAL_REFL, ORTHOGONAL_SYM, orthogonal, .. } := BOrth
  let { SPAN_INDUCT, SPAN_MONO, SPAN_SUBSPACE, SUBSPACE_SPAN, .. } := BSubspace
  let { SPAN_INC, SPAN_INSERT_0, SPAN_MUL, SPAN_SUB, SPAN_SUBSET_SUBSPACE, SPAN_SUPERSET,
        SPAN_UNIV, SPAN_VSUM, .. } := BSpan1
  let { BASIS_EXISTS, BASIS_HAS_SIZE_DIM, .. } := BDim1
  let { DIM_EQ_FULL, DIM_SPAN, DIM_SUBSET, DIM_SUBSET_UNIV, DIM_UNIV, .. } := BDim2
  let { DIM_SING, .. } := BExplicit
  let { ORTHOGONAL_TO_SPAN, SUBSPACE_ORTHOGONAL_TO_VECTOR, .. } := BRowSpace
  let { ORTHOGONAL_EXTENSION, PAIRWISE_ORTHOGONAL_IMP_FINITE,
        PAIRWISE_ORTHOGONAL_INDEPENDENT, SPAN_DELETE_0, SPAN_IMAGE_SCALE, .. } := BGram1
  -- @@SCOPE END

  let ORTHOGONAL_SPANNINGSET_SUBSPACE ← prove
   r"!s:real^N->bool.
        subspace s
        ==> ?b. b SUBSET s /\ pairwise orthogonal b /\ span b = s"
   (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"s:real^N->bool") BASIS_EXISTS) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:real^N->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"{}:real^N->bool", ← q r"b:real^N->bool"]
      ORTHOGONAL_EXTENSION) THEN
    REWRITE_TAC [PAIRWISE_EMPTY, UNION_EMPTY] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"c:real^N->bool") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← TAUT (← q r"b /\ (b ==> a) ==> a /\ b")) THEN CONJ_TAC THENL
     [MATCH_MP_TAC SPAN_SUBSPACE THEN ASM_REWRITE_TAC [],
      DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_MESON_TAC [SPAN_INC]])

  let ORTHOGONAL_BASIS_SUBSPACE ← prove
   r"!s:real^N->bool.
        subspace s
        ==> ?b. ~(vec 0 IN b) /\
                b SUBSET s /\
                pairwise orthogonal b /\
                independent b /\
                b HAS_SIZE (dim s) /\
                span b = s"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP ORTHOGONAL_SPANNINGSET_SUBSPACE) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:real^N->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"b DELETE (vec 0:real^N)") THEN ASM_REWRITE_TAC [IN_DELETE] THEN
    CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")) THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC (REWRITE_RULE [pairwise]) THEN
      ASM_SIMP_TAC [pairwise, IN_DELETE],
      DISCH_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")) THEN CONJ_TAC THENL
     [MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN ASM_SIMP_TAC [IN_DELETE],
      DISCH_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"b /\ (b ==> a) ==> a /\ b")) THEN CONJ_TAC THENL
     [ASM_MESON_TAC [SPAN_DELETE_0],
      DISCH_TAC THEN ASM_SIMP_TAC [BASIS_HAS_SIZE_DIM]])

  let ORTHONORMAL_BASIS_SUBSPACE ← prove
   r"!s:real^N->bool.
        subspace s
        ==> ?b. b SUBSET s /\
                pairwise orthogonal b /\
                (!x. x IN b ==> norm x = &1) /\
                independent b /\
                b HAS_SIZE (dim s) /\
                span b = s"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP ORTHOGONAL_BASIS_SUBSPACE) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:real^N->bool") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"IMAGE (\x:real^N. inv(norm x) % x) b") THEN
    CONJ_TAC THENL
     [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC [SPAN_MUL, SPAN_INC, SUBSET],
      ALL_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")) THEN CONJ_TAC THENL
     [REWRITE_TAC [pairwise, IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [pairwise]) THEN
      ASM_MESON_TAC [ORTHOGONAL_CLAUSES],
      DISCH_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")) THEN CONJ_TAC THENL
     [REWRITE_TAC [FORALL_IN_IMAGE, NORM_MUL, REAL_ABS_INV, REAL_ABS_NORM] THEN
      ASM_MESON_TAC [REAL_MUL_LINV, NORM_EQ_0],
      DISCH_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")) THEN CONJ_TAC THENL
     [MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [IN_IMAGE] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
      SIMP_TAC [VECTOR_MUL_EQ_0, REAL_INV_EQ_0, NORM_EQ_0] THEN ASM_MESON_TAC [],
      DISCH_TAC] THEN
    MATCH_MP_TAC (← TAUT (← q r"b /\ (b ==> a) ==> a /\ b")) THEN CONJ_TAC THENL
     [ALL_TAC, ASM_SIMP_TAC [BASIS_HAS_SIZE_DIM]] THEN
    UNDISCH_THEN (← q r"span b = (s:real^N->bool)") (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SPAN_IMAGE_SCALE THEN
    REWRITE_TAC [REAL_INV_EQ_0, NORM_EQ_0] THEN
    ASM_MESON_TAC [HAS_SIZE])

  let ORTHOGONAL_TO_SUBSPACE_EXISTS_GEN ← prove
   r"!s t:real^N->bool.
        span s PSUBSET span t
        ==> ?x. ~(x = vec 0) /\ x IN span t /\
                (!y. y IN span s ==> orthogonal x y)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"span s:real^N->bool") ORTHOGONAL_BASIS_SUBSPACE) THEN
    REWRITE_TAC [SUBSPACE_SPAN] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:real^N->bool") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [PSUBSET_ALT]) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN (← q r"u:real^N") STRIP_ASSUME_TAC)) THEN
    MP_TAC (← ISPECL [← q r"b:real^N->bool", ← q r"{u:real^N}"] ORTHOGONAL_EXTENSION) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"ns:real^N->bool") MP_TAC) THEN
    ASM_CASES_TAC (← q r"ns SUBSET (vec 0:real^N) INSERT b") THENL
     [DISCH_THEN (MP_TAC o AP_TERM (← q r"(IN) (u:real^N)") o CONJUNCT2) THEN
      SIMP_TAC [SPAN_SUPERSET, IN_UNION, IN_SING] THEN
      MATCH_MP_TAC (← TAUT (← q r"~p ==> p ==> q")) THEN
      SUBGOAL_THEN (← q r"~(u IN span (b UNION {vec 0:real^N}))") MP_TAC THENL
       [ASM_REWRITE_TAC [← SET_RULE (← q r"s UNION {a} = a INSERT s"), SPAN_INSERT_0],
        MATCH_MP_TAC (← SET_RULE (← q r"s SUBSET t ==> ~(x IN t) ==> ~(x IN s)")) THEN
        MATCH_MP_TAC SPAN_MONO THEN ASM SET_TAC []],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP (← SET_RULE (← q
     r"~(s SUBSET t) ==> ?z. z IN s /\ ~(z IN t)"))) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM, IN_INSERT, DE_MORGAN_THM] THEN
    X_GEN_TAC (← q r"n:real^N") THEN STRIP_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC [pairwise, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"n:real^N")) THEN ASM_REWRITE_TAC [IN_UNION] THEN
    REWRITE_TAC [IMP_IMP] THEN DISCH_TAC THEN EXISTS_TAC (← q r"n:real^N") THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [SUBGOAL_THEN (← q r"(n:real^N) IN span (b UNION ns)") MP_TAC THENL
       [MATCH_MP_TAC SPAN_SUPERSET THEN ASM SET_TAC [],
        ASM_REWRITE_TAC [] THEN SPEC_TAC (← q r"n:real^N", ← q r"n:real^N") THEN
        REWRITE_TAC [← GSYM SUBSET] THEN
        MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN REWRITE_TAC [SUBSPACE_SPAN] THEN
        ASM_REWRITE_TAC [← SET_RULE (← q
         r"s UNION {a} SUBSET t <=> s SUBSET t /\ a IN t")] THEN
        ASM_MESON_TAC [SPAN_INC, SUBSET_TRANS]],
      MATCH_MP_TAC SPAN_INDUCT THEN
      REWRITE_TAC [← SET_RULE (← q r"(\y. orthogonal n y) = {y | orthogonal n y}")] THEN
      REWRITE_TAC [SUBSPACE_ORTHOGONAL_TO_VECTOR] THEN ASM SET_TAC []])

  let ORTHOGONAL_TO_SUBSPACE_EXISTS ← prove
   r"!s:real^N->bool. dim s < dimindex(:N)
                    ==> ?x. ~(x = vec 0) /\ !y. y IN s ==> orthogonal x y"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"(:real^N)"]
          ORTHOGONAL_TO_SUBSPACE_EXISTS_GEN) THEN
    ANTS_TAC THENL [REWRITE_TAC [PSUBSET], MESON_TAC [SPAN_SUPERSET]] THEN
    REWRITE_TAC [SPAN_UNIV, SUBSET_UNIV] THEN
    ASM_MESON_TAC [DIM_SPAN, DIM_UNIV, LT_REFL])

  let ORTHOGONAL_TO_VECTOR_EXISTS ← prove
   r"!x:real^N. 2 <= dimindex(:N) ==> ?y. ~(y = vec 0) /\ orthogonal x y"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"{x:real^N}") ORTHOGONAL_TO_SUBSPACE_EXISTS) THEN
    SIMP_TAC [DIM_SING, IN_SING, LEFT_FORALL_IMP_THM, EXISTS_REFL] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC, MESON_TAC [ORTHOGONAL_SYM]])

  let SPAN_NOT_UNIV_ORTHOGONAL ← prove
   r"!s. ~(span s = (:real^N))
         ==> ?a. ~(a = vec 0) /\ !x. x IN span s ==> a dot x = &0"
   (REWRITE_TAC [← GSYM DIM_EQ_FULL, ← GSYM LE_ANTISYM, DIM_SUBSET_UNIV,
                 NOT_LE] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM orthogonal] THEN
    MATCH_MP_TAC ORTHOGONAL_TO_SUBSPACE_EXISTS THEN ASM_REWRITE_TAC [DIM_SPAN])

  let SPAN_NOT_UNIV_SUBSET_HYPERPLANE ← prove
   r"!s. ~(span s = (:real^N))
       ==> ?a. ~(a = vec 0) /\ span s SUBSET {x | a dot x = &0}"
   (REWRITE_TAC [SUBSET, IN_ELIM_THM, SPAN_NOT_UNIV_ORTHOGONAL])

  let LOWDIM_SUBSET_HYPERPLANE ← prove
   r"!s. dim s < dimindex(:N)
       ==> ?a:real^N. ~(a = vec 0) /\ span s SUBSET {x | a dot x = &0}"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_NOT_UNIV_SUBSET_HYPERPLANE THEN
    REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, SUBSET_UNIV] THEN
    DISCH_THEN (MP_TAC o MATCH_MP DIM_SUBSET) THEN
    ASM_REWRITE_TAC [NOT_LE, DIM_SPAN, DIM_UNIV])

  let VECTOR_EQ_DOT_SPAN ← prove
   r"!b x y:real^N.
        (!v. v IN b ==> v dot x = v dot y) /\ x IN span b /\ y IN span b
        ==> x = y"
   (ONCE_REWRITE_TAC [← GSYM REAL_SUB_0, ← GSYM VECTOR_SUB_EQ] THEN
    REWRITE_TAC [← GSYM DOT_RSUB, ← GSYM ORTHOGONAL_REFL, ← GSYM orthogonal] THEN
    MESON_TAC [ORTHOGONAL_TO_SPAN, SPAN_SUB, ORTHOGONAL_SYM])

  let ORTHONORMAL_BASIS_EXPAND ← prove
   r"!b x:real^N.
        pairwise orthogonal b /\ (!v. v IN b ==> norm v = &1) /\ x IN span b
   ==> vsum b (\v. (v dot x) % v) = x"
   (REWRITE_TAC [NORM_EQ_1] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC VECTOR_EQ_DOT_SPAN THEN EXISTS_TAC (← q r"b:real^N->bool") THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP PAIRWISE_ORTHOGONAL_IMP_FINITE) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [pairwise, orthogonal]) THEN
    ASM_SIMP_TAC [SPAN_VSUM, SPAN_MUL, DOT_RSUM, DOT_RMUL, SPAN_SUPERSET] THEN
    X_GEN_TAC (← q r"v:real^N") THEN DISCH_TAC THEN
    TRANS_TAC EQ_TRANS (← q r"sum b (\w:real^N. if w = v then v dot x else &0)") THEN
    CONJ_TAC THENL [ALL_TAC, ASM_SIMP_TAC [SUM_DELTA]] THEN
    MATCH_MP_TAC SUM_EQ THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"w:real^N") THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [REAL_MUL_RID, REAL_MUL_RZERO])

  let ORTHONORMAL_BASIS_EXPAND_DOT ← prove
   r"!b x y:real^N.
        pairwise orthogonal b /\
        (!v. v IN b ==> norm v = &1) /\
        (x IN span b \/ y IN span b)
        ==> sum b (\v. (v dot x) * (v dot y)) = x dot y"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"b:real^N->bool") ORTHONORMAL_BASIS_EXPAND) THENL
     [DISCH_THEN (MP_TAC o SPEC (← q r"x:real^N")),
      DISCH_THEN (MP_TAC o SPEC (← q r"y:real^N"))] THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do
      pure (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [← SYM th])) THEN
    ASM_SIMP_TAC [DOT_LSUM, DOT_RSUM, PAIRWISE_ORTHOGONAL_IMP_FINITE] THEN
    REWRITE_TAC [DOT_LMUL, DOT_RMUL] THEN
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC [REAL_MUL_SYM, DOT_SYM])

  let ORTHONORMAL_BASIS_EXPAND_NORM ← prove
   r"!b x:real^N.
        pairwise orthogonal b /\
        (!v. v IN b ==> norm v = &1) /\
        x IN span b
        ==> sum b (\v. (v dot x) pow 2) = norm x pow 2"
   (ASM_SIMP_TAC [REAL_POW_2, ORTHONORMAL_BASIS_EXPAND_DOT, NORM_POW_2])

  return { ORTHOGONAL_SPANNINGSET_SUBSPACE, ORTHOGONAL_BASIS_SUBSPACE,
           ORTHONORMAL_BASIS_SUBSPACE, ORTHOGONAL_TO_SUBSPACE_EXISTS_GEN,
           ORTHOGONAL_TO_SUBSPACE_EXISTS, ORTHOGONAL_TO_VECTOR_EXISTS,
           SPAN_NOT_UNIV_ORTHOGONAL, SPAN_NOT_UNIV_SUBSET_HYPERPLANE,
           LOWDIM_SUBSET_HYPERPLANE, VECTOR_EQ_DOT_SPAN, ORTHONORMAL_BASIS_EXPAND,
           ORTHONORMAL_BASIS_EXPAND_DOT, ORTHONORMAL_BASIS_EXPAND_NORM }

/- ------------------------------------------------------------------------- -/
/- Independent and orthogonal subspaces.  (vectors.ml 7750-7839)             -/
/- ------------------------------------------------------------------------- -/

structure IndepSub where
  ORTHOGONAL_IMP_INDEPENDENT_SUBSPACES : thm
  INDEPENDENT_SUBSPACES_ALT : thm
  INDEPENDENT_SUBSPACES_0 : thm
  INDEPENDENT_SUBSPACES : thm
  ORTHOGONAL_SUBSPACE_DECOMP_UNIQUE : thm
  ORTHOGONAL_SUBSPACE_DECOMP_EXISTS : thm
  ORTHOGONAL_SUBSPACE_DECOMP : thm
  deriving Inhabited

@[nospecialize]
def setupIndepSub [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BOrth : Orth) (BSubspace : Subspace) (BSpan1 : Span1) (BDim1 : Dim1)
    (BRowSpace : RowSpace) (BGram1 : Gram1) (BGram3 : Gram3) :
    ExceptT String IO IndepSub := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, .. } := D
  let { EXISTS_PAIRED_THM, EXISTS_UNIQUE_DEF, .. } := D.core1
  let { FORALL_PAIRED_THM, FORALL_PAIR_THM, IN_ELIM_THM, IN_INTER, IN_SING,
        LEFT_IMP_EXISTS_THM, .. } := D.core2
  let { PAIR_EQ, .. } := D.core3
  let { SING_SUBSET, SUBSET, SUBSET_ANTISYM_EQ, .. } := D.core4
  let { VECTOR_ADD_RID, VECTOR_ARITH, VECTOR_ARITH_TAC, VECTOR_NEG_EQ_0, VECTOR_NEG_NEG,
        VECTOR_SUB_EQ, .. } := BVectorArith
  let { ORTHOGONAL_CLAUSES, ORTHOGONAL_REFL, ORTHOGONAL_SYM, .. } := BOrth
  let { SPAN_CLAUSES, SUBSPACE_0, SUBSPACE_NEG, SUBSPACE_SPAN, SUBSPACE_SUB, .. } := BSubspace
  let { SPAN_VSUM, .. } := BSpan1
  let { INDEPENDENT_IMP_FINITE, .. } := BDim1
  let { ORTHOGONAL_TO_SPANS_EQ, .. } := BRowSpace
  let { GRAM_SCHMIDT_STEP, .. } := BGram1
  let { ORTHOGONAL_BASIS_SUBSPACE, .. } := BGram3
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let ORTHOGONAL_IMP_INDEPENDENT_SUBSPACES ← prove
   r"!s t:real^N->bool.
        (!a b. a IN s /\ b IN t ==> orthogonal a b)
        ==> s INTER t SUBSET {vec 0}"
   (REWRITE_TAC [SUBSET, IN_INTER, IN_SING] THEN
    MESON_TAC [ORTHOGONAL_REFL])

  let INDEPENDENT_SUBSPACES_ALT ← prove
   r"!s t:real^N->bool.
        subspace s /\ subspace t
        ==> (s INTER t SUBSET {vec 0} <=> s INTER t = {vec 0})"
   (REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN
    SIMP_TAC [SING_SUBSET, IN_INTER, SUBSPACE_0])

  let INDEPENDENT_SUBSPACES_0 ← prove
   r"!s t:real^N->bool.
        subspace s /\ subspace t
        ==> (s INTER t SUBSET {vec 0} <=>
             !x y. x IN s /\ y IN t /\ x + y = vec 0
                   ==> x = vec 0 /\ y = vec 0)"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [SUBSET, IN_INTER, IN_SING] THEN
    ONCE_REWRITE_TAC [← MESON [VECTOR_NEG_NEG] (← q
     r"(!x y:real^N. P x y) <=> (!x y. P x (--y))")] THEN
    ASM_SIMP_TAC [← MESON [SUBSPACE_NEG, VECTOR_NEG_NEG] (← q
     r"subspace t ==> ((--x:real^N) IN t <=> x IN t)")] THEN
    REWRITE_TAC [VECTOR_NEG_EQ_0, ← va
     r"x + --y:real^N = vec 0 <=> x = y"] THEN
    MESON_TAC [])

  let INDEPENDENT_SUBSPACES ← prove
   r"!s t:real^N->bool.
        subspace s /\ subspace t
        ==> (s INTER t SUBSET {vec 0} <=>
             !x y x' y'. x IN s /\ x' IN s /\ y IN t /\ y' IN t /\
                         x + y = x' + y'
                         ==> x = x' /\ y = y')"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [INDEPENDENT_SUBSPACES_0] THEN
    EQ_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
     [ONCE_REWRITE_TAC [← GSYM VECTOR_SUB_EQ] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [SUBSPACE_SUB] THEN
      FIRST_X_ASSUM (MP_TAC o SYM) THEN CONV_TAC (fun t => VECTOR_ARITH t),
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC [SUBSPACE_0, VECTOR_ADD_RID]])

  let ORTHOGONAL_SUBSPACE_DECOMP_UNIQUE ← prove
   r"!s t x y x' y':real^N.
        (!a b. a IN s /\ b IN t ==> orthogonal a b) /\
        x IN span s /\ x' IN span s /\ y IN span t /\ y' IN span t /\
        x + y = x' + y'
        ==> x = x' /\ y = y'"
   (REWRITE_TAC [← va r"x + y:real^N = x' + y' <=> x - x' = y' - y"] THEN
    ONCE_REWRITE_TAC [← GSYM ORTHOGONAL_TO_SPANS_EQ] THEN
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [← va
     r"x:real^N = x' /\ y:real^N = y' <=> x - x' = vec 0 /\ y' - y = vec 0"] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [← GSYM ORTHOGONAL_REFL] THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      pure (GEN_REWRITE_TAC RAND_CONV [← SYM th])) THEN
    ASM_MESON_TAC [ORTHOGONAL_CLAUSES, ORTHOGONAL_SYM])

  let ORTHOGONAL_SUBSPACE_DECOMP_EXISTS ← prove
   r"!s x:real^N. ?y z. y IN span s /\ (!w. w IN span s ==> orthogonal z w) /\
                      x = y + z"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"span s:real^N->bool") ORTHOGONAL_BASIS_SUBSPACE) THEN
    REWRITE_TAC [SUBSPACE_SPAN, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"t:real^N->bool") THEN STRIP_TAC THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    EXISTS_TAC (← q r"vsum t (\b:real^N. (b dot x) / (b dot b) % b)") THEN
    EXISTS_TAC (← q r"x - vsum t (\b:real^N. (b dot x) / (b dot b) % b)") THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SPAN_VSUM THEN
      ASM_SIMP_TAC [INDEPENDENT_IMP_FINITE, SPAN_CLAUSES],
      REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [ORTHOGONAL_SYM] THEN
      MATCH_MP_TAC GRAM_SCHMIDT_STEP THEN ASM_SIMP_TAC [],
      VECTOR_ARITH_TAC])

  let ORTHOGONAL_SUBSPACE_DECOMP ← prove
   r"!s x. ?!(y,z). y IN span s /\
                  z IN {z:real^N | !x. x IN span s ==> orthogonal z x} /\
                  x = y + z"
   (REWRITE_TAC [EXISTS_UNIQUE_DEF, IN_ELIM_THM] THEN
    REWRITE_TAC [EXISTS_PAIRED_THM, FORALL_PAIRED_THM] THEN
    REWRITE_TAC [FORALL_PAIR_THM, ORTHOGONAL_SUBSPACE_DECOMP_EXISTS] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [PAIR_EQ] THEN
    MATCH_MP_TAC ORTHOGONAL_SUBSPACE_DECOMP_UNIQUE THEN
    MAP_EVERY EXISTS_TAC
     [← q r"s:real^N->bool", ← q r"{z:real^N | !x. x IN span s ==> orthogonal z x}"] THEN
    ASM_SIMP_TAC [SPAN_CLAUSES, IN_ELIM_THM] THEN
    ASM_MESON_TAC [SPAN_CLAUSES, ORTHOGONAL_SYM])

  return { ORTHOGONAL_IMP_INDEPENDENT_SUBSPACES, INDEPENDENT_SUBSPACES_ALT,
           INDEPENDENT_SUBSPACES_0, INDEPENDENT_SUBSPACES, ORTHOGONAL_SUBSPACE_DECOMP_UNIQUE,
           ORTHOGONAL_SUBSPACE_DECOMP_EXISTS, ORTHOGONAL_SUBSPACE_DECOMP }

/- ------------------------------------------------------------------------- -/
/- Existence of isometry between subspaces of same dimension.               -/
/- (vectors.ml 7844-8027)                                                     -/
/- ------------------------------------------------------------------------- -/

structure Isometry where
  ISOMETRY_SUBSET_SUBSPACE : thm
  ISOMETRIES_SUBSPACES : thm
  ISOMETRY_SUBSPACES : thm
  ISOMETRY_UNIV_SUBSPACE : thm
  ISOMETRY_UNIV_SUPERSET_SUBSPACE : thm
  ISOMETRY_UNIV_UNIV : thm
  SUBSPACE_ISOMORPHISM : thm
  ISOMORPHISMS_UNIV_UNIV : thm
  deriving Inhabited

@[nospecialize]
def setupIsometry [HolBase] (D : VectorsDeps) (BBasics : Basics)
    (BVectorArith : VectorArith) (BNorm1 : Norm1) (BNorm2 : Norm2) (BOrth : Orth)
    (BLinear : Linear) (BSubspace : Subspace) (BSpan1 : Span1) (BSpan2 : Span2)
    (BDim2 : Dim2) (BExplicit : Explicit) (BExtend : Extend) (BGram3 : Gram3) :
    ExceptT String IO Isometry := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON_TAC, SET_TAC, .. } := D
  let { CARD_EQ_BIJECTIONS, CARD_LE_INJ, CART_EQ, DIMINDEX_GE_1, .. } := D.core1
  let { HAS_SIZE, IMP_IMP, IN, INJECTIVE_ON_ALT, IN_ELIM_THM, IN_UNIV, LAMBDA_BETA,
        LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, MONO_EXISTS, .. } := D.core2
  let { RIGHT_AND_EXISTS_THM, SUBSET, SUM_EQ, .. } := D.core4
  let { o_DEF, pairwise, .. } := D.core5
  let { dot, .. } := BBasics
  let { VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, .. } := BVectorArith
  let { NORM_EQ_0, NORM_MUL, NORM_POS_LE, NORM_POW_2, vector_norm, .. } := BNorm1
  let { NORM_EQ_SQUARE, .. } := BNorm2
  let { NORM_VSUM_PYTHAGOREAN, ORTHOGONAL_CLAUSES, ORTHOGONAL_MUL, .. } := BOrth
  let { LINEAR_0, LINEAR_CMUL, LINEAR_VSUM, linear, .. } := BLinear
  let { LINEAR_INJECTIVE_0_SUBSPACE, SPAN_INDUCT, SPAN_MONO, SUBSPACE_SPAN,
        SUBSPACE_TRIVIAL, SUBSPACE_UNIV, subspace, .. } := BSubspace
  let { SPAN_INC, SPAN_LINEAR_IMAGE, .. } := BSpan1
  let { SPAN_FINITE, .. } := BSpan2
  let { DIM_SPAN, DIM_UNIV, LOWDIM_EXPAND_DIMENSION, .. } := BDim2
  let { DIM_EQ_0, .. } := BExplicit
  let { LINEAR_INDEPENDENT_EXTEND, .. } := BExtend
  let { ORTHONORMAL_BASIS_SUBSPACE, .. } := BGram3
  -- @@SCOPE END

  let ISOMETRY_SUBSET_SUBSPACE ← prove
   r"!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t /\ dim s <= dim t
        ==> ?f. linear f /\ IMAGE f s SUBSET t /\
                (!x. x IN s ==> norm(f x) = norm(x))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"t:real^N->bool") ORTHONORMAL_BASIS_SUBSPACE) THEN
    MP_TAC (← ISPEC (← q r"s:real^M->bool") ORTHONORMAL_BASIS_SUBSPACE) THEN
    ASM_REWRITE_TAC [HAS_SIZE] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:real^M->bool") STRIP_ASSUME_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"c:real^N->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"b:real^M->bool", ← q r"c:real^N->bool"] CARD_LE_INJ) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM, INJECTIVE_ON_ALT] THEN
    X_GEN_TAC (← q r"fb:real^M->real^N") THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"fb:real^M->real^N", ← q r"b:real^M->bool"]
      LINEAR_INDEPENDENT_EXTEND) THEN
    ASM_REWRITE_TAC [IMP_IMP, LEFT_AND_EXISTS_THM, INJECTIVE_ON_ALT] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f:real^M->real^N") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [REWRITE_TAC [← SYM (← ASSUME (← q r"span b:real^M->bool = s"))] THEN
      ASM_SIMP_TAC [← GSYM SPAN_LINEAR_IMAGE] THEN
      REWRITE_TAC [← SYM (← ASSUME (← q r"span c:real^N->bool = t"))] THEN
      MATCH_MP_TAC SPAN_MONO THEN ASM SET_TAC [],
      UNDISCH_THEN (← q r"span b:real^M->bool = s") (SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC [SPAN_FINITE] THEN
      REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"z:real^M", ← q r"u:real^M->real"] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [LINEAR_VSUM] THEN
      REWRITE_TAC [o_DEF, NORM_EQ_SQUARE, NORM_POS_LE, ← GSYM NORM_POW_2] THEN
      ASM_SIMP_TAC [LINEAR_CMUL] THEN
      W (MP_TAC o PART_MATCH (lhand o rand)
        NORM_VSUM_PYTHAGOREAN o rand o snd) THEN
      W (MP_TAC o PART_MATCH (lhand o rand)
        NORM_VSUM_PYTHAGOREAN o lhand o rand o snd) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [pairwise]) THEN
      ASM_SIMP_TAC [pairwise, ORTHOGONAL_CLAUSES] THEN ANTS_TAC THENL
       [REPEAT STRIP_TAC THEN REWRITE_TAC [ORTHOGONAL_MUL] THEN ASM SET_TAC [],
        REPEAT (DISCH_THEN SUBST1_TAC) THEN ASM_SIMP_TAC [NORM_MUL] THEN
        MATCH_MP_TAC SUM_EQ THEN ASM SET_TAC []]])

  let ISOMETRIES_SUBSPACES ← prove
   r"!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t /\ dim s = dim t
        ==> ?f g. linear f /\ linear g /\
                  IMAGE f s = t /\ IMAGE g t = s /\
                  (!x. x IN s ==> norm(f x) = norm x) /\
                  (!y. y IN t ==> norm(g y) = norm y) /\
                  (!x. x IN s ==> g(f x) = x) /\
                  (!y. y IN t ==> f(g y) = y)"
   (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"n = dim(t:real^N->bool)") THEN
    MP_TAC (← ISPEC (← q r"t:real^N->bool") ORTHONORMAL_BASIS_SUBSPACE) THEN
    MP_TAC (← ISPEC (← q r"s:real^M->bool") ORTHONORMAL_BASIS_SUBSPACE) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:real^M->bool") STRIP_ASSUME_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"c:real^N->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"b:real^M->bool", ← q r"c:real^N->bool"] CARD_EQ_BIJECTIONS) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [HAS_SIZE]) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"fb:real^M->real^N", ← q r"gb:real^N->real^M"] THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"gb:real^N->real^M", ← q r"c:real^N->bool"]
      LINEAR_INDEPENDENT_EXTEND) THEN
    MP_TAC (← ISPECL [← q r"fb:real^M->real^N", ← q r"b:real^M->bool"]
      LINEAR_INDEPENDENT_EXTEND) THEN
    ASM_REWRITE_TAC [IMP_IMP, LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f:real^M->real^N") THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"g:real^N->real^M") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC [← SYM (← ASSUME (← q r"span b:real^M->bool = s"))] THEN
      ASM_SIMP_TAC [← GSYM SPAN_LINEAR_IMAGE] THEN
      REWRITE_TAC [← SYM (← ASSUME (← q r"span c:real^N->bool = t"))] THEN
      AP_TERM_TAC THEN ASM SET_TAC [],
      REWRITE_TAC [← SYM (← ASSUME (← q r"span c:real^N->bool = t"))] THEN
      ASM_SIMP_TAC [← GSYM SPAN_LINEAR_IMAGE] THEN
      REWRITE_TAC [← SYM (← ASSUME (← q r"span b:real^M->bool = s"))] THEN
      AP_TERM_TAC THEN ASM SET_TAC [],
      UNDISCH_THEN (← q r"span b:real^M->bool = s") (SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC [SPAN_FINITE] THEN
      REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"z:real^M", ← q r"u:real^M->real"] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [LINEAR_VSUM] THEN
      REWRITE_TAC [o_DEF, NORM_EQ_SQUARE, NORM_POS_LE, ← GSYM NORM_POW_2] THEN
      ASM_SIMP_TAC [LINEAR_CMUL] THEN
      W (MP_TAC o PART_MATCH (lhand o rand)
        NORM_VSUM_PYTHAGOREAN o rand o snd) THEN
      W (MP_TAC o PART_MATCH (lhand o rand)
        NORM_VSUM_PYTHAGOREAN o lhand o rand o snd) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [pairwise]) THEN
      ASM_SIMP_TAC [pairwise, ORTHOGONAL_CLAUSES] THEN ANTS_TAC THENL
       [REPEAT STRIP_TAC THEN REWRITE_TAC [ORTHOGONAL_MUL] THEN ASM SET_TAC [],
        REPEAT (DISCH_THEN SUBST1_TAC) THEN
        ASM_SIMP_TAC [NORM_MUL]],
      UNDISCH_THEN (← q r"span c:real^N->bool = t") (SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC [SPAN_FINITE] THEN
      REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"z:real^N", ← q r"u:real^N->real"] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [LINEAR_VSUM] THEN
      REWRITE_TAC [o_DEF, NORM_EQ_SQUARE, NORM_POS_LE, ← GSYM NORM_POW_2] THEN
      ASM_SIMP_TAC [LINEAR_CMUL] THEN
      W (MP_TAC o PART_MATCH (lhand o rand)
        NORM_VSUM_PYTHAGOREAN o rand o snd) THEN
      W (MP_TAC o PART_MATCH (lhand o rand)
        NORM_VSUM_PYTHAGOREAN o lhand o rand o snd) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [pairwise]) THEN
      ASM_SIMP_TAC [pairwise, ORTHOGONAL_CLAUSES] THEN ANTS_TAC THENL
       [REPEAT STRIP_TAC THEN REWRITE_TAC [ORTHOGONAL_MUL] THEN ASM SET_TAC [],
        REPEAT (DISCH_THEN SUBST1_TAC) THEN
        ASM_SIMP_TAC [NORM_MUL]],
      REWRITE_TAC [← SYM (← ASSUME (← q r"span b:real^M->bool = s"))] THEN
      MATCH_MP_TAC SPAN_INDUCT THEN
      CONJ_TAC THENL [ASM_MESON_TAC [SUBSET, IN], ALL_TAC] THEN
      REWRITE_TAC [subspace, IN] THEN ASM_MESON_TAC [linear, LINEAR_0],
      REWRITE_TAC [← SYM (← ASSUME (← q r"span c:real^N->bool = t"))] THEN
      MATCH_MP_TAC SPAN_INDUCT THEN
      CONJ_TAC THENL [ASM_MESON_TAC [SUBSET, IN], ALL_TAC] THEN
      REWRITE_TAC [subspace, IN] THEN ASM_MESON_TAC [linear, LINEAR_0]])

  let ISOMETRY_SUBSPACES ← prove
   r"!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t /\ dim s = dim t
        ==> ?f:real^M->real^N. linear f /\ IMAGE f s = t /\
                               (!x. x IN s ==> norm(f x) = norm(x))"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP ISOMETRIES_SUBSPACES) THEN
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC [])

  let ISOMETRY_UNIV_SUBSPACE ← prove
   r"!s. subspace s /\ dimindex(:M) = dim s
       ==> ?f:real^M->real^N.
                linear f /\ IMAGE f (:real^M) = s /\
                (!x. norm(f x) = norm(x))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"(:real^M)", ← q r"s:real^N->bool"] ISOMETRY_SUBSPACES) THEN
    ASM_REWRITE_TAC [SUBSPACE_UNIV, IN_UNIV, DIM_UNIV])

  let ISOMETRY_UNIV_SUPERSET_SUBSPACE ← prove
   r"!s. subspace s /\ dim s <= dimindex(:M) /\ dimindex(:M) <= dimindex(:N)
       ==> ?f:real^M->real^N.
                linear f /\ s SUBSET (IMAGE f (:real^M)) /\
                (!x. norm(f x) = norm(x))"
   (GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP LOWDIM_EXPAND_DIMENSION) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:real^N->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"(:real^M)", ← q r"span t:real^N->bool"] ISOMETRY_SUBSPACES) THEN
    ASM_REWRITE_TAC [SUBSPACE_SPAN, SUBSPACE_UNIV, DIM_UNIV, DIM_SPAN] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [IN_UNIV] THEN
    ASM_MESON_TAC [SUBSET, SPAN_INC])

  let ISOMETRY_UNIV_UNIV ← prove
   r"dimindex(:M) <= dimindex(:N)
   ==> ?f:real^M->real^N. linear f /\ (!x. norm(f x) = norm(x))"
   (DISCH_TAC THEN
    MP_TAC (← ISPEC (← q r"{vec 0:real^N}") ISOMETRY_UNIV_SUPERSET_SUBSPACE) THEN
    ASM_REWRITE_TAC [SUBSPACE_TRIVIAL] THEN
    ANTS_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
    MATCH_MP_TAC (← ARITH_RULE (← q r"x = 0 /\ 1 <= y ==> x <= y")) THEN
    ASM_REWRITE_TAC [DIM_EQ_0, DIMINDEX_GE_1] THEN SET_TAC [])

  let SUBSPACE_ISOMORPHISM ← prove
   r"!s t. subspace s /\ subspace t /\ dim(s) = dim(t)
         ==> ?f:real^M->real^N.
                linear f /\ (IMAGE f s = t) /\
                (!x y. x IN s /\ y IN s /\ f x = f y ==> (x = y))"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP ISOMETRY_SUBSPACES) THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    ASM_SIMP_TAC [LINEAR_INJECTIVE_0_SUBSPACE] THEN MESON_TAC [NORM_EQ_0])

  let ISOMORPHISMS_UNIV_UNIV ← prove
   r"dimindex(:M) = dimindex(:N)
   ==> ?f:real^M->real^N g.
            linear f /\ linear g /\
            (!x. norm(f x) = norm x) /\ (!y. norm(g y) = norm y) /\
            (!x. g(f x) = x) /\ (!y. f(g y) = y)"
   (REPEAT STRIP_TAC THEN
    EXISTS_TAC (← q r"(\x. lambda i. x$i):real^M->real^N") THEN
    EXISTS_TAC (← q r"(\x. lambda i. x$i):real^N->real^M") THEN
    SIMP_TAC [vector_norm, dot, LAMBDA_BETA] THEN
    SIMP_TAC [linear, CART_EQ, VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT,
              LAMBDA_BETA] THEN
    FIRST_ASSUM SUBST1_TAC THEN SIMP_TAC [LAMBDA_BETA] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN SIMP_TAC [LAMBDA_BETA])

  return { ISOMETRY_SUBSET_SUBSPACE, ISOMETRIES_SUBSPACES, ISOMETRY_SUBSPACES,
           ISOMETRY_UNIV_SUBSPACE, ISOMETRY_UNIV_SUPERSET_SUBSPACE, ISOMETRY_UNIV_UNIV,
           SUBSPACE_ISOMORPHISM, ISOMORPHISMS_UNIV_UNIV }

/- ------------------------------------------------------------------------- -/
/- Properties of special hyperplanes.  (vectors.ml 8032-8143)                -/
/- ------------------------------------------------------------------------- -/

structure SpecHyper where
  SUBSPACE_HYPERPLANE : thm
  SUBSPACE_SPECIAL_HYPERPLANE : thm
  SPECIAL_HYPERPLANE_SPAN : thm
  DIM_SPECIAL_HYPERPLANE : thm
  LOWDIM_EQ_INTER_HYPERPLANE : thm
  LOWDIM_EQ_HYPERPLANE : thm
  deriving Inhabited

@[nospecialize]
def setupSpecHyper [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BDotProps : DotProps) (BNormArith : NormArithB) (BVSum1 : VSum1) (BBasis : Basis)
    (BOrth : Orth) (BSubspace : Subspace) (BSpan1 : Span1) (BSpan2 : Span2)
    (BDim2 : Dim2) (BRowSpace : RowSpace) (BGram1 : Gram1) (BGram3 : Gram3) :
    ExceptT String IO SpecHyper := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, HAS_SIZE_CONV, MESON_TAC, REAL_ARITH_TAC, SET_RULE, SET_TAC,
        .. } := D
  let { CARD_DELETE, CARD_NUMSEG_1, CARD_UNION, DE_MORGAN_THM, DIMINDEX_GE_1, DISJOINT,
        EQ_ADD_LCANCEL, EQ_TRANS, FINITE_DELETE, FINITE_IMAGE, FINITE_NUMSEG, FINITE_UNION,
        FORALL_IN_IMAGE, .. } := D.core1
  let { HAS_SIZE, HAS_SIZE_IMAGE_INJ, IMP_CONJ, INTER_COMM, INTER_UNIV, IN_DELETE,
        IN_ELIM_THM, IN_NUMSEG, IN_SING, IN_UNION, LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM,
        MONO_EXISTS, .. } := D.core2
  let { PAIRWISE_INSERT, REAL_ADD_LID, REAL_ENTIRE, .. } := D.core3
  let { REAL_MUL_RZERO, REAL_SUB_0, SUBSET, SUBSET_REFL, SUBSET_UNIV, SUB_ADD, .. } := D.core4
  let { o_DEF, .. } := D.core5
  let { VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, VECTOR_MUL_LZERO, VECTOR_SUB_RZERO,
        VEC_COMPONENT, .. } := BVectorArith
  let { DOT_EQ_0, DOT_RADD, DOT_RMUL, DOT_RSUB, DOT_RZERO, .. } := BDotProps
  let { NORM_ARITH, .. } := BNormArith
  let { VSUM_DELETE, VSUM_IMAGE, .. } := BVSum1
  let { BASIS_COMPONENT, BASIS_EXPANSION, BASIS_INJ, DOT_BASIS, .. } := BBasis
  let { orthogonal, .. } := BOrth
  let { INDEPENDENT_MONO, SPAN_SUBSPACE, SUBSPACE_SPAN, SUBSPACE_UNIV, subspace,
        .. } := BSubspace
  let { SPAN_BREAKDOWN_EQ, SPAN_INC, SPAN_OF_SUBSPACE, .. } := BSpan1
  let { INDEPENDENT_STDBASIS, SPAN_FINITE, .. } := BSpan2
  let { DIM_EQ_CARD, DIM_SPAN, DIM_UNIQUE, DIM_UNIV, .. } := BDim2
  let { ORTHOGONAL_TO_SPAN, .. } := BRowSpace
  let { ORTHONORMAL_EXTENSION, PAIRWISE_ORTHOGONAL_IMP_FINITE,
        PAIRWISE_ORTHOGONAL_INDEPENDENT, .. } := BGram1
  let { ORTHONORMAL_BASIS_SUBSPACE, .. } := BGram3
  -- @@SCOPE END

  let SUBSPACE_HYPERPLANE ← prove
   r"!a. subspace {x:real^N | a dot x = &0}"
   (SIMP_TAC [subspace, DOT_RADD, DOT_RMUL, IN_ELIM_THM, REAL_ADD_LID,
              REAL_MUL_RZERO, DOT_RZERO])

  let SUBSPACE_SPECIAL_HYPERPLANE ← prove
   r"!k. subspace {x:real^N | x$k = &0}"
   (SIMP_TAC [subspace, IN_ELIM_THM, VEC_COMPONENT,
              VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC)

  let SPECIAL_HYPERPLANE_SPAN ← prove
   r"!k. 1 <= k /\ k <= dimindex(:N)
       ==> {x:real^N | x$k = &0} =
           span(IMAGE basis ((1..dimindex(:N)) DELETE k))"
   (REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SPAN_SUBSPACE THEN
    ASM_SIMP_TAC [SUBSPACE_SPECIAL_HYPERPLANE] THEN CONJ_TAC THENL
     [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
      ASM_SIMP_TAC [BASIS_COMPONENT, IN_DELETE],
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
      X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [← GSYM BASIS_EXPANSION] THEN
      SIMP_TAC [SPAN_FINITE, FINITE_IMAGE, FINITE_DELETE, FINITE_NUMSEG] THEN
      REWRITE_TAC [IN_ELIM_THM] THEN
      EXISTS_TAC (← q r"\v:real^N. x dot v") THEN
      W (MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhs o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [FINITE_DELETE, FINITE_NUMSEG, IN_NUMSEG, IN_DELETE] THEN
        MESON_TAC [BASIS_INJ],
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [o_DEF] THEN
        ASM_SIMP_TAC [VSUM_DELETE, FINITE_NUMSEG, IN_NUMSEG, DOT_BASIS] THEN
        REWRITE_TAC [VECTOR_MUL_LZERO, VECTOR_SUB_RZERO]]])

  let DIM_SPECIAL_HYPERPLANE ← prove
   r"!k. 1 <= k /\ k <= dimindex(:N)
       ==> dim {x:real^N | x$k = &0} = dimindex(:N) - 1"
   (SIMP_TAC [SPECIAL_HYPERPLANE_SPAN] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC DIM_UNIQUE THEN
    EXISTS_TAC (← q r"IMAGE (basis:num->real^N) ((1..dimindex(:N)) DELETE k)") THEN
    REWRITE_TAC [SUBSET_REFL, SPAN_INC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INDEPENDENT_MONO THEN
      EXISTS_TAC (← q r"{basis i:real^N | 1 <= i /\ i <= dimindex(:N)}") THEN
      REWRITE_TAC [INDEPENDENT_STDBASIS, SUBSET, FORALL_IN_IMAGE] THEN
      REWRITE_TAC [IN_DELETE, IN_NUMSEG, IN_ELIM_THM] THEN MESON_TAC [],
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
       [REWRITE_TAC [FINITE_DELETE, FINITE_NUMSEG, IN_NUMSEG, IN_DELETE] THEN
        MESON_TAC [BASIS_INJ],
        ASM_SIMP_TAC [HAS_SIZE, FINITE_DELETE, FINITE_NUMSEG, CARD_DELETE,
                      FINITE_IMAGE, IN_NUMSEG, CARD_NUMSEG_1]]])

  let LOWDIM_EQ_INTER_HYPERPLANE ← prove
   r"!s t:real^N->bool.
        subspace s /\ subspace t /\ t SUBSET s /\ dim t + 1 = dim s
        ==> ?a. ~(a = vec 0) /\ {x | a dot x = &0} INTER s = t"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"t:real^N->bool") ORTHONORMAL_BASIS_SUBSPACE) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:real^N->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"b:real^N->bool", ← q r"s:real^N->bool"]
          ORTHONORMAL_EXTENSION) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"c:real^N->bool") THEN
    SUBGOAL_THEN (← q r"span(b UNION s):real^N->bool = s") SUBST1_TAC THENL
     [TRANS_TAC EQ_TRANS (← q r"span(s:real^N->bool)") THEN CONJ_TAC THENL
       [AP_TERM_TAC THEN ASM SET_TAC [], ASM_MESON_TAC [SPAN_OF_SUBSPACE]],
      STRIP_TAC] THEN
    UNDISCH_TAC (← q r"dim(t:real^N->bool) + 1 = dim(s:real^N->bool)") THEN
    MAP_EVERY EXPAND_TAC ["s", "t"] THEN REWRITE_TAC [DIM_SPAN] THEN
    SUBGOAL_THEN (← q r"~((vec 0:real^N) IN b UNION c)") MP_TAC THENL
     [ASM_MESON_TAC [IN_UNION, ← NORM_ARITH (← q r"~(norm(vec 0:real^N) = &1)")],
      ASM_SIMP_TAC [DIM_EQ_CARD, PAIRWISE_ORTHOGONAL_INDEPENDENT, IN_UNION,
                    DE_MORGAN_THM]] THEN
    SUBGOAL_THEN (← q r"FINITE(b UNION c:real^N->bool)") MP_TAC THENL
     [ASM_MESON_TAC [PAIRWISE_ORTHOGONAL_IMP_FINITE],
      ASM_SIMP_TAC [FINITE_UNION, CARD_UNION,
                    ← GSYM (← ONCE_REWRITE_RULE [INTER_COMM] DISJOINT)]] THEN
    STRIP_TAC THEN STRIP_TAC THEN REWRITE_TAC [EQ_ADD_LCANCEL] THEN
    DISCH_THEN (ASSUME_TAC o SYM) THEN
    MP_TAC (← HAS_SIZE_CONV (← q r"(c:real^N->bool) HAS_SIZE 1")) THEN
    ASM_REWRITE_TAC [HAS_SIZE] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"a:real^N") THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [IN_SING]) THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← SET_RULE (← q
     r"t SUBSET s /\
    (!x. x IN t ==> x IN h) /\
    (!x. x IN s /\ ~(x IN t) ==> ~(x IN h))
    ==> h INTER s = t")) THEN
    ASM_REWRITE_TAC [] THEN MAP_EVERY EXPAND_TAC ["s", "t"] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
     [REWRITE_TAC [IN_ELIM_THM, ← GSYM orthogonal] THEN
      MATCH_MP_TAC ORTHOGONAL_TO_SPAN THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV
       [← SET_RULE (← q r"s UNION {a} = a INSERT s")]) THEN
      REWRITE_TAC [PAIRWISE_INSERT] THEN ASM SET_TAC [],
      DISCH_TAC] THEN
    REWRITE_TAC [SPAN_BREAKDOWN_EQ, ← SET_RULE (← q r"s UNION {a} = a INSERT s")] THEN
    REWRITE_TAC [LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:real^N", ← q r"c:real"] THEN
    ASM_CASES_TAC (← q r"c = &0") THEN
    ASM_SIMP_TAC [VECTOR_MUL_LZERO, VECTOR_SUB_RZERO, IMP_CONJ] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"a dot (x - c % a:real^N) = &0") MP_TAC THENL
     [ASM_MESON_TAC [], REWRITE_TAC [DOT_RSUB, DOT_RMUL]] THEN
    ASM_SIMP_TAC [REAL_SUB_0, REAL_ENTIRE, DOT_EQ_0])

  let LOWDIM_EQ_HYPERPLANE ← prove
   r"!s. dim s = dimindex(:N) - 1
       ==> ?a:real^N. ~(a = vec 0) /\ span s = {x | a dot x = &0}"
   (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL
     [← q r"(:real^N)", ← q r"span s:real^N->bool"] LOWDIM_EQ_INTER_HYPERPLANE) THEN
    ASM_REWRITE_TAC [SUBSPACE_SPAN, SUBSPACE_UNIV, SUBSET_UNIV, INTER_UNIV] THEN
    ASM_SIMP_TAC [DIM_SPAN, SUB_ADD, DIMINDEX_GE_1, DIM_UNIV] THEN
    MESON_TAC [])

  return { SUBSPACE_HYPERPLANE, SUBSPACE_SPECIAL_HYPERPLANE, SPECIAL_HYPERPLANE_SPAN,
           DIM_SPECIAL_HYPERPLANE, LOWDIM_EQ_INTER_HYPERPLANE, LOWDIM_EQ_HYPERPLANE }

/- ------------------------------------------------------------------------- -/
/- More theorems about dimensions of different subspaces: image and kernel. -/
/- (vectors.ml 8149-8259)                                                     -/
/- ------------------------------------------------------------------------- -/

structure DimKernel where
  DIM_IMAGE_KERNEL_GEN : thm
  DIM_IMAGE_KERNEL : thm
  deriving Inhabited

@[nospecialize]
def setupDimKernel [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BNorm1 : Norm1) (BVSum1 : VSum1) (BLinear : Linear) (BSubspace : Subspace)
    (BSpan1 : Span1) (BSpan2 : Span2) (BDim1 : Dim1) (BDim2 : Dim2)
    (BExplicit : Explicit) (BLinEq : LinEq) : ExceptT String IO DimKernel := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, GEN_SIMPLIFY_CONV, MESON_TAC, SET_RULE, SET_TAC, TOP_DEPTH_SQCONV,
        basic_ss, .. } := D
  let { CARD_DIFF, CARD_IMAGE_INJ, CARD_SUBSET, COND_RAND, COND_RATOR, EXTENSION,
        FINITE_DIFF, FINITE_IMAGE, FORALL_IN_IMAGE, .. } := D.core1
  let { IMAGE_SUBSET, IMP_CONJ, IMP_IMP, INJECTIVE_ON_LEFT_INVERSE, IN_DIFF, IN_ELIM_THM,
        IN_UNIV, LEFT_IMP_EXISTS_THM, .. } := D.core2
  let { REAL_NEG_EQ_0, SUBSET, SUBSET_ANTISYM, SUBSET_DIFF, SUBSET_TRANS, SUB_ADD,
        .. } := D.core4
  let { o_DEF, .. } := D.core5
  let { VECTOR_ADD_LINV, VECTOR_MUL_LNEG, .. } := BVectorArith
  let { VECTOR_MUL_EQ_0, .. } := BNorm1
  let { VSUM_CASES, VSUM_EQ_0, VSUM_EQ_SUPERSET, VSUM_IMAGE, VSUM_NEG, .. } := BVSum1
  let { LINEAR_CMUL, LINEAR_VSUM, .. } := BLinear
  let { INDEPENDENT_MONO, LINEAR_INJECTIVE_0_SUBSPACE, SPAN_MONO, SPAN_SUBSPACE,
        SUBSPACE_INTER, SUBSPACE_LINEAR_IMAGE, SUBSPACE_SPAN, SUBSPACE_UNIV, .. } := BSubspace
  let { SPAN_EQ_SELF, SPAN_INC, SPAN_SUBSET_SUBSPACE, .. } := BSpan1
  let { SPAN_FINITE, .. } := BSpan2
  let { BASIS_EXISTS, INDEPENDENT_IMP_FINITE, MAXIMAL_INDEPENDENT_SUBSET_EXTEND,
        .. } := BDim1
  let { DIM_EQ_CARD, DIM_SPAN, DIM_UNIV, .. } := BDim2
  let { INDEPENDENT_EXPLICIT, INDEPENDENT_INJECTIVE_IMAGE_GEN, .. } := BExplicit
  let { SUBSPACE_KERNEL, .. } := BLinEq
  -- @@SCOPE END

  let DIM_IMAGE_KERNEL_GEN ← prove
   r"!f:real^M->real^N s.
        linear f /\ subspace s
        ==> dim(IMAGE f s) + dim {x | x IN s /\  f x = vec 0} = dim(s)"
   (REPEAT STRIP_TAC THEN MP_TAC
     (← ISPEC (← q r"{x | x IN s /\ (f:real^M->real^N) x = vec 0}") BASIS_EXISTS) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"v:real^M->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"v:real^M->bool", ← q r"s:real^M->bool"]
      MAXIMAL_INDEPENDENT_SUBSET_EXTEND) THEN
    ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"w:real^M->bool") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"span(w:real^M->bool) = s")
     (fun th => tactic_of do
        pure (GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← SYM th] THEN
              ASSUME_TAC th))
    THENL [ASM_SIMP_TAC [SPAN_SUBSPACE], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"subspace {x | x IN s /\ (f:real^M->real^N) x = vec 0}")
    ASSUME_TAC THENL
     [REWRITE_TAC [← SET_RULE (← q r"{x | x IN s /\ P x} = s INTER {x | P x}")] THEN
      ASM_SIMP_TAC [SUBSPACE_INTER, SUBSPACE_KERNEL],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"{x | x IN s /\ (f:real^M->real^N) x = vec 0} = span v")
    ASSUME_TAC THENL
     [ASM_MESON_TAC [SUBSET_ANTISYM, SPAN_SUBSET_SUBSPACE, SUBSPACE_KERNEL],
      ALL_TAC] THEN
    ASM_SIMP_TAC [DIM_SPAN, DIM_EQ_CARD] THEN
    SUBGOAL_THEN
     (← q r"!x. x IN span(w DIFF v) /\ (f:real^M->real^N) x = vec 0 ==> x = vec 0")
    (LABEL_TAC "*") THENL
     [MATCH_MP_TAC (← SET_RULE (← q
       r"!t. s SUBSET t /\ (!x. x IN s /\ x IN t /\ P x ==> Q x)
          ==> (!x. x IN s /\ P x ==> Q x)")) THEN
      EXISTS_TAC (← q r"s:real^M->bool") THEN CONJ_TAC THENL
       [ASM_MESON_TAC [SPAN_MONO, SUBSET_DIFF], ALL_TAC] THEN
      ASM_SIMP_TAC [SPAN_FINITE, IN_ELIM_THM, IMP_CONJ, FINITE_DIFF,
                    INDEPENDENT_IMP_FINITE, LEFT_IMP_EXISTS_THM] THEN
      GEN_TAC THEN X_GEN_TAC (← q r"u:real^M->real") THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [IMP_IMP] THEN
      ONCE_REWRITE_TAC [← SET_RULE (← q
       r"y IN s /\ f y = a <=> y IN {x | x IN s /\ f x = a}")] THEN
      ASM_REWRITE_TAC [] THEN
      ASM_SIMP_TAC [SPAN_FINITE, INDEPENDENT_IMP_FINITE, IN_ELIM_THM] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"t:real^M->real")) THEN
      MP_TAC (← ISPEC (← q r"w:real^M->bool") INDEPENDENT_EXPLICIT) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN (MP_TAC o SPEC
       (← q r"(\x. if x IN w DIFF v then --u x else t x):real^M->real")) THEN
      ASM_REWRITE_TAC [COND_RAND] THEN ONCE_REWRITE_TAC [COND_RATOR] THEN
      ASM_SIMP_TAC [VSUM_CASES, INDEPENDENT_IMP_FINITE] THEN
      REWRITE_TAC [← SET_RULE (← q r"{x | x IN w /\ x IN (w DIFF v)} = w DIFF v")] THEN
      SIMP_TAC [← ASSUME (← q r"(v:real^M->bool) SUBSET w"), ← SET_RULE (← q
       r"v SUBSET w ==> {x | x IN w /\ ~(x IN (w DIFF v))} = v")] THEN
      ASM_REWRITE_TAC [VECTOR_MUL_LNEG, VSUM_NEG, VECTOR_ADD_LINV] THEN
      DISCH_THEN (fun th => MATCH_MP_TAC VSUM_EQ_0 THEN MP_TAC th) THEN
      REWRITE_TAC [REAL_NEG_EQ_0, VECTOR_MUL_EQ_0, IN_DIFF] THEN MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x y. x IN (w DIFF v) /\ y IN (w DIFF v) /\
                      (f:real^M->real^N) x = f y ==> x = y")
    ASSUME_TAC THENL
     [REMOVE_THEN "*" MP_TAC THEN
      ASM_SIMP_TAC [← GSYM LINEAR_INJECTIVE_0_SUBSPACE, SUBSPACE_SPAN] THEN
      MP_TAC (← ISPEC (← q r"w DIFF v:real^M->bool") SPAN_INC) THEN SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"IMAGE (f:real^M->real^N) s = span(IMAGE f (w DIFF v))")
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [ALL_TAC,
        ASM_MESON_TAC [SUBSPACE_LINEAR_IMAGE, SPAN_MONO, IMAGE_SUBSET,
                       SUBSET_TRANS, SUBSET_DIFF, SPAN_EQ_SELF]] THEN
      SIMP_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"x:real^M") THEN
      DISCH_TAC THEN UNDISCH_TAC (← q r"span w:real^M->bool = s") THEN
      REWRITE_TAC [EXTENSION] THEN DISCH_THEN (MP_TAC o SPEC (← q r"x:real^M")) THEN
      ASM_REWRITE_TAC [] THEN
      REMOVE_THEN "*" (MP_TAC o SPEC (← q r"x:real^M")) THEN
      CONV_TAC (← ExceptT.mk (GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV
        (← ExceptT.mk (basic_ss [])) 4
       [IN_UNIV, SPAN_FINITE, INDEPENDENT_IMP_FINITE, IN_ELIM_THM,
        FINITE_IMAGE, FINITE_DIFF, ← ASSUME (← q r"independent(w:real^M->bool)")])) THEN
      REWRITE_TAC [IMP_CONJ, LEFT_IMP_EXISTS_THM] THEN DISCH_TAC THEN
      X_GEN_TAC (← q r"u:real^M->real") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
      FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [INJECTIVE_ON_LEFT_INVERSE]) THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"g:real^N->real^M")) THEN
      EXISTS_TAC (← q r"(u:real^M->real) o (g:real^N->real^M)") THEN
      W (MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhand o snd) THEN
      ASM_REWRITE_TAC [] THEN
      ASM_SIMP_TAC [FINITE_DIFF, INDEPENDENT_IMP_FINITE, LINEAR_VSUM] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [o_DEF] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_EQ_SUPERSET THEN
      SIMP_TAC [SUBSET_DIFF, FINITE_DIFF, INDEPENDENT_IMP_FINITE,
                LINEAR_CMUL, IN_DIFF, ← TAUT (← q r"a /\ ~(a /\ ~b) <=> a /\ b"),
                ← ASSUME (← q r"independent(w:real^M->bool)"),
                ← ASSUME (← q r"linear(f:real^M->real^N)")] THEN
      REWRITE_TAC [VECTOR_MUL_EQ_0] THEN ASM SET_TAC [],
      SUBGOAL_THEN (← q r"independent(IMAGE (f:real^M->real^N) (w DIFF v))")
      ASSUME_TAC THENL
       [MATCH_MP_TAC INDEPENDENT_INJECTIVE_IMAGE_GEN THEN
        ASM_SIMP_TAC [LINEAR_INJECTIVE_0_SUBSPACE, SUBSPACE_SPAN] THEN
        ASM_MESON_TAC [INDEPENDENT_MONO, SUBSET_DIFF],
        ASM_SIMP_TAC [DIM_SPAN, DIM_EQ_CARD] THEN
        W (MP_TAC o PART_MATCH (lhs o rand) CARD_IMAGE_INJ o
          lhand o lhand o snd) THEN
        ASM_REWRITE_TAC [] THEN
        ASM_SIMP_TAC [FINITE_DIFF, CARD_DIFF, INDEPENDENT_IMP_FINITE] THEN
        DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUB_ADD THEN
        ASM_MESON_TAC [CARD_SUBSET, INDEPENDENT_IMP_FINITE]]])

  let DIM_IMAGE_KERNEL ← prove
   r"!f:real^M->real^N.
        linear f
        ==> dim(IMAGE f (:real^M)) + dim {x | f x = vec 0} = dimindex(:M)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^M->real^N", ← q r"(:real^M)"] DIM_IMAGE_KERNEL_GEN) THEN
    ASM_REWRITE_TAC [SUBSPACE_UNIV, IN_UNIV, DIM_UNIV])

  return { DIM_IMAGE_KERNEL_GEN, DIM_IMAGE_KERNEL }

/- ------------------------------------------------------------------------- -/
/- Dimensions of sums and intersections, kernels of compositions,           -/
/- orthogonal sums and special subspaces.  (vectors.ml 8261-8516)            -/
/- ------------------------------------------------------------------------- -/

structure DimSums where
  DIM_SUMS_INTER : thm
  DIM_UNION_INTER : thm
  DIM_KERNEL_COMPOSE : thm
  DIM_ORTHOGONAL_SUM : thm
  DIM_SUBSPACE_ORTHOGONAL_TO_VECTORS : thm
  DIM_SPECIAL_SUBSPACE : thm
  deriving Inhabited

@[nospecialize]
def setupDimSums [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BDotProps : DotProps) (BNorm1 : Norm1) (BVSum1 : VSum1) (BBasis : Basis)
    (BOrth : Orth) (BLinear : Linear) (BSubspace : Subspace) (BSpan1 : Span1)
    (BSpan2 : Span2) (BDim1 : Dim1) (BDim2 : Dim2) (BExplicit : Explicit)
    (BGram1 : Gram1) (BIndepSub : IndepSub) : ExceptT String IO DimSums := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON_TAC, REAL_ARITH_TAC, SET_RULE, SET_TAC, .. } := D
  let { CARD_IMAGE_INJ, CARD_SUBSET, CARD_UNION_GEN, CARD_UNION_LE, COND_RAND, COND_RATOR,
        CONJ_ASSOC, CONTRAPOS_THM, DIFF, EXISTS_FINITE_SUBSET_IMAGE, FINITE_DIFF,
        FINITE_IMAGE, FINITE_NUMSEG, FINITE_SUBSET, FINITE_UNION, FORALL_IN_GSPEC,
        FORALL_IN_IMAGE, .. } := D.core1
  let { HAS_SIZE, IMAGE_INJECTIVE_IMAGE_OF_SUBSET, IMP_CONJ, IN_DIFF, IN_ELIM_THM, IN_IMAGE,
        IN_INTER, IN_NUMSEG, IN_SING, LEFT_IMP_EXISTS_THM, LE_ADD2, LE_REFL, LE_TRANS,
        MONO_EXISTS, NOT_EXISTS_THM, .. } := D.core2
  let { RIGHT_FORALL_IMP_THM, SUBSET, SUBSET_ANTISYM, SUBSET_INTER, SUBSET_TRANS,
        SUBSET_UNION, .. } := D.core4
  let { SWAP_EXISTS_THM, UNION_SUBSET, o_THM, pairwise, .. } := D.core5
  let { VECTOR_ADD_LID, VECTOR_ADD_RDISTRIB, VECTOR_ADD_RID, VECTOR_ADD_SYM, VECTOR_ARITH,
        VECTOR_MUL_LZERO, VECTOR_SUB_EQ, .. } := BVectorArith
  let { DOT_EQ_0, DOT_LADD, DOT_LMUL, DOT_LZERO, DOT_RADD, DOT_RMUL, DOT_RZERO, DOT_SYM,
        .. } := BDotProps
  let { VECTOR_MUL_EQ_0, .. } := BNorm1
  let { VSUM_ADD, VSUM_CASES, VSUM_SUPERSET, VSUM_UNION, .. } := BVSum1
  let { BASIS_COMPONENT, BASIS_EXPANSION, BASIS_INJ_EQ, BASIS_NONZERO, .. } := BBasis
  let { ORTHOGONAL_BASIS_BASIS, ORTHOGONAL_SYM, orthogonal, .. } := BOrth
  let { LINEAR_SUB, .. } := BLinear
  let { SPAN_INDUCT, SPAN_MONO, SUBSPACE_0, SUBSPACE_MUL, SUBSPACE_NEG, SUBSPACE_SPAN,
        SUBSPACE_SUB, SUBSPACE_VSUM, dependent, independent, subspace, .. } := BSubspace
  let { SPAN_0, SPAN_ADD, SPAN_EQ_SELF, SPAN_INC, SPAN_LINEAR_IMAGE, SPAN_MUL,
        SPAN_OF_SUBSPACE, SPAN_SUBSET_SUBSPACE, SPAN_SUPERSET, SPAN_UNION, SPAN_VSUM,
        .. } := BSpan1
  let { SPAN_FINITE, .. } := BSpan2
  let { BASIS_EXISTS, BASIS_EXISTS_FINITE, INDEPENDENT_IMP_FINITE,
        MAXIMAL_INDEPENDENT_SUBSET_EXTEND, .. } := BDim1
  let { DIM_EQ_CARD, DIM_LE_CARD, DIM_SPAN, DIM_SUBSET, DIM_UNIQUE, .. } := BDim2
  let { DIM_EQ_0, INDEPENDENT_EXPLICIT, .. } := BExplicit
  let { PAIRWISE_ORTHOGONAL_INDEPENDENT, .. } := BGram1
  let { ORTHOGONAL_SUBSPACE_DECOMP_EXISTS, .. } := BIndepSub
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let DIM_SUMS_INTER ← prove
   r"!s t:real^N->bool.
    subspace s /\ subspace t
    ==> dim {x + y | x IN s /\ y IN t} + dim(s INTER t) = dim(s) + dim(t)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"s INTER t:real^N->bool") BASIS_EXISTS) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:real^N->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"b:real^N->bool", ← q r"s:real^N->bool"]
      MAXIMAL_INDEPENDENT_SUBSET_EXTEND) THEN
    ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"c:real^N->bool") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q r"b:real^N->bool", ← q r"t:real^N->bool"]
      MAXIMAL_INDEPENDENT_SUBSET_EXTEND) THEN
    ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:real^N->bool") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"(c:real^N->bool) INTER d = b") ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC [SUBSET_INTER] THEN
      REWRITE_TAC [SUBSET, IN_INTER] THEN X_GEN_TAC (← q r"x:real^N") THEN
      STRIP_TAC THEN MP_TAC (← ISPEC (← q r"c:real^N->bool") independent) THEN
      ASM_REWRITE_TAC [dependent, NOT_EXISTS_THM] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"x:real^N")) THEN ASM_REWRITE_TAC [] THEN
      ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN STRIP_TAC THEN
      REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"(x:real^N) IN span b") MP_TAC THENL
       [ASM_MESON_TAC [SUBSET, IN_INTER, SPAN_INC],
        MP_TAC (← ISPECL [← q r"b:real^N->bool", ← q r"c DELETE (x:real^N)"] SPAN_MONO) THEN
        ASM SET_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"dim (s INTER t:real^N->bool) = CARD(b:real^N->bool) /\
    dim s = CARD c /\ dim t = CARD d /\
    dim {x + y:real^N | x IN s /\ y IN t} = CARD(c UNION d:real^N->bool)")
    (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
     [ALL_TAC,
      ASM_SIMP_TAC [CARD_UNION_GEN, INDEPENDENT_IMP_FINITE] THEN
      MATCH_MP_TAC (← ARITH_RULE (← q r"b:num <= c ==> (c + d) - b + b = c + d")) THEN
      ASM_SIMP_TAC [CARD_SUBSET, INDEPENDENT_IMP_FINITE]] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC DIM_UNIQUE THENL
     [EXISTS_TAC (← q r"b:real^N->bool"),
      EXISTS_TAC (← q r"c:real^N->bool"),
      EXISTS_TAC (← q r"d:real^N->bool"),
      EXISTS_TAC (← q r"c UNION d:real^N->bool")] THEN
    ASM_SIMP_TAC [HAS_SIZE, INDEPENDENT_IMP_FINITE, FINITE_UNION] THEN
    REWRITE_TAC [UNION_SUBSET, ← GSYM CONJ_ASSOC] THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM, FORALL_IN_GSPEC] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [← q r"x:real^N", ← q r"vec 0:real^N"] THEN
      ASM_SIMP_TAC [SUBSPACE_0, VECTOR_ADD_RID] THEN ASM SET_TAC [],
      X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [← q r"vec 0:real^N", ← q r"x:real^N"] THEN
      ASM_SIMP_TAC [SUBSPACE_0, VECTOR_ADD_LID] THEN ASM SET_TAC [],
      MAP_EVERY X_GEN_TAC [← q r"x:real^N", ← q r"y:real^N"] THEN STRIP_TAC THEN
      MATCH_MP_TAC SPAN_ADD THEN CONJ_TAC THENL
       [MP_TAC (← ISPECL [← q r"c:real^N->bool", ← q r"c UNION d:real^N->bool"] SPAN_MONO),
        MP_TAC (← ISPECL [← q r"d:real^N->bool", ← q r"c UNION d:real^N->bool"] SPAN_MONO)] THEN
      REWRITE_TAC [SUBSET_UNION] THEN REWRITE_TAC [SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC [],
      ALL_TAC] THEN
    ASM_SIMP_TAC [INDEPENDENT_EXPLICIT, FINITE_UNION, INDEPENDENT_IMP_FINITE] THEN
    X_GEN_TAC (← q r"a:real^N->real") THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [← SET_RULE (← q r"s UNION t = s UNION (t DIFF s)")] THEN
    ASM_SIMP_TAC [VSUM_UNION, ← SET_RULE (← q r"DISJOINT c (d DIFF c)"),
                  INDEPENDENT_IMP_FINITE, FINITE_DIFF, FINITE_UNION] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"(vsum (d DIFF c) (\v:real^N. a v % v)) IN span b")
    MP_TAC THENL
     [FIRST_ASSUM (MATCH_MP_TAC o GEN_REWRITE_RULE id [SUBSET]) THEN
      REWRITE_TAC [IN_INTER] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM (SUBST1_TAC o MATCH_MP (← va
         r"a + b = vec 0 ==> b = --a")) THEN
        MATCH_MP_TAC SUBSPACE_NEG THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      MATCH_MP_TAC SUBSPACE_VSUM THEN
      ASM_SIMP_TAC [FINITE_DIFF, INDEPENDENT_IMP_FINITE] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSPACE_MUL THEN
      ASM_REWRITE_TAC [] THEN ASM SET_TAC [],
      ALL_TAC] THEN
    ASM_SIMP_TAC [SPAN_FINITE, INDEPENDENT_IMP_FINITE, IN_ELIM_THM] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"e:real^N->real")) THEN
    MP_TAC (← ISPEC (← q r"c:real^N->bool") INDEPENDENT_EXPLICIT) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o SPEC (← q r"(\x. if x IN b then a x + e x else a x):real^N->real"))) THEN
    REWRITE_TAC [] THEN ONCE_REWRITE_TAC [COND_RAND] THEN
    ONCE_REWRITE_TAC [COND_RATOR] THEN ASM_SIMP_TAC [VSUM_CASES] THEN
    REWRITE_TAC [VECTOR_ADD_RDISTRIB, ← GSYM DIFF] THEN
    ASM_SIMP_TAC [← SET_RULE (← q r"b SUBSET c ==> {x | x IN c /\ x IN b} = b")] THEN
    ASM_SIMP_TAC [VSUM_ADD, INDEPENDENT_IMP_FINITE] THEN
    ONCE_REWRITE_TAC [← va r"(a + b) + c:real^N = (a + c) + b"] THEN
    ASM_SIMP_TAC [← GSYM VSUM_UNION, FINITE_DIFF, INDEPENDENT_IMP_FINITE,
                  ← SET_RULE (← q r"DISJOINT b (c DIFF b)")] THEN
    ASM_SIMP_TAC [← SET_RULE (← q r"b SUBSET c ==> b UNION (c DIFF b) = c")] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN (← q r"!v:real^N. v IN (c DIFF b) ==> a v = &0") ASSUME_TAC THENL
     [ASM SET_TAC [], ALL_TAC] THEN
    MP_TAC (← ISPEC (← q r"d:real^N->bool") INDEPENDENT_EXPLICIT) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o SPEC (← q r"a:real^N->real"))) THEN
    SUBGOAL_THEN (← q r"d:real^N->bool = b UNION (d DIFF c)")
     (fun th => GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [th])
    THENL [ASM SET_TAC [], ALL_TAC] THEN
    ANTS_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
    ASM_SIMP_TAC [VSUM_UNION, FINITE_DIFF, INDEPENDENT_IMP_FINITE,
                  ← SET_RULE (← q r"c INTER d = b ==> DISJOINT b (d DIFF c)")] THEN
    SUBGOAL_THEN (← q r"vsum b (\x:real^N. a x % x) = vsum c (\x. a x % x)")
     (fun th => ASM_REWRITE_TAC [th]) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
    ASM_SIMP_TAC [VECTOR_MUL_EQ_0] THEN ASM_MESON_TAC [])

  let DIM_UNION_INTER ← prove
   r"!s t:real^N->bool.
        subspace s /\ subspace t
        ==> dim(s UNION t) + dim(s INTER t) = dim s + dim t"
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [← GSYM DIM_SPAN] THEN
    MP_TAC (← ISPECL [← q r"span s:real^N->bool", ← q r"span t:real^N->bool"]
          DIM_SUMS_INTER) THEN
    ASM_SIMP_TAC [SPAN_UNION, SUBSPACE_SPAN, SPAN_OF_SUBSPACE])

  let DIM_KERNEL_COMPOSE ← prove
   r"!f:real^M->real^N g:real^N->real^P.
        linear f /\ linear g
        ==> dim {x | (g o f) x = vec 0} <=
                dim {x | f(x) = vec 0} +
                dim {y | g(y) = vec 0}"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q r"{x | (f:real^M->real^N) x = vec 0}") BASIS_EXISTS_FINITE) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:real^M->bool") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     (← q r"?c. FINITE c /\
        IMAGE f c SUBSET {y | g(y):real^P = vec 0} /\
        independent (IMAGE (f:real^M->real^N) c) /\
        IMAGE f (:real^M) INTER {y | g(y) = vec 0} SUBSET span(IMAGE f c) /\
        (!x y. x IN c /\ y IN c ==> (f x = f y <=> x = y)) /\
        (IMAGE f c) HAS_SIZE dim (IMAGE f (:real^M) INTER {y | g(y) = vec 0})")
    STRIP_ASSUME_TAC THENL
     [MP_TAC (← ISPEC (← q r"IMAGE (f:real^M->real^N) (:real^M) INTER
                 {x | (g:real^N->real^P) x = vec 0}") BASIS_EXISTS_FINITE) THEN
      REWRITE_TAC [SUBSET_INTER, ← GSYM CONJ_ASSOC, EXISTS_FINITE_SUBSET_IMAGE] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"c:real^M->bool") STRIP_ASSUME_TAC) THEN
      MP_TAC (← ISPECL [← q r"f:real^M->real^N", ← q r"c:real^M->bool"]
          IMAGE_INJECTIVE_IMAGE_OF_SUBSET) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"d:real^M->bool") THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
      ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [FINITE_SUBSET],
      ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC (← q r"dim(span(b UNION c:real^M->bool))") THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIM_SUBSET THEN
      REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, o_THM] THEN
      X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"(f:real^M->real^N) x IN span(IMAGE f c)") MP_TAC THENL
       [ASM SET_TAC [], ALL_TAC] THEN
      ASM_SIMP_TAC [SPAN_LINEAR_IMAGE, IN_IMAGE, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q r"y:real^M") THEN STRIP_TAC THEN
      SUBST1_TAC (← va r"x:real^M = y + (x - y)") THEN
      MATCH_MP_TAC SPAN_ADD THEN CONJ_TAC THENL
       [ASM_MESON_TAC [SUBSET_UNION, SPAN_MONO, SUBSET], ALL_TAC] THEN
      MATCH_MP_TAC (← SET_RULE (← q
       r"!t. x IN t /\ t SUBSET s ==> x IN s")) THEN
      EXISTS_TAC (← q r"{x | (f:real^M->real^N) x = vec 0}") THEN CONJ_TAC THENL
       [REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [LINEAR_SUB, VECTOR_SUB_EQ],
        ASM_MESON_TAC [SUBSET_TRANS, SUBSET_UNION, SPAN_MONO]],
      REWRITE_TAC [DIM_SPAN] THEN MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC (← q r"CARD(b UNION c:real^M->bool)") THEN
      ASM_SIMP_TAC [DIM_LE_CARD, FINITE_UNION, INDEPENDENT_IMP_FINITE] THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC (← q r"CARD(b:real^M->bool) + CARD(c:real^M->bool)") THEN
      ASM_SIMP_TAC [CARD_UNION_LE] THEN MATCH_MP_TAC LE_ADD2 THEN CONJ_TAC THENL
       [ASM_SIMP_TAC [← GSYM DIM_EQ_CARD, DIM_SUBSET], ALL_TAC] THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC (← q r"dim(IMAGE (f:real^M->real^N) c)") THEN CONJ_TAC THENL
       [ASM_SIMP_TAC [DIM_EQ_CARD] THEN
        ASM_MESON_TAC [CARD_IMAGE_INJ, LE_REFL],
        ASM_SIMP_TAC [← GSYM DIM_EQ_CARD, DIM_SUBSET]]])

  let DIM_ORTHOGONAL_SUM ← prove
   r"!s t:real^N->bool.
        (!x y. x IN s /\ y IN t ==> x dot y = &0)
        ==> dim(s UNION t) = dim(s) + dim(t)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM DIM_SPAN] THEN
    REWRITE_TAC [SPAN_UNION] THEN
    SIMP_TAC [← GSYM DIM_SUMS_INTER, SUBSPACE_SPAN] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"x = x + y <=> y = 0")] THEN
    REWRITE_TAC [DIM_EQ_0, SUBSET, IN_INTER] THEN
    SUBGOAL_THEN
     (← q r"!x:real^N. x IN span s ==> !y:real^N. y IN span t ==> x dot y = &0")
    MP_TAC THENL
     [MATCH_MP_TAC SPAN_INDUCT THEN CONJ_TAC THENL
       [X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN
        MATCH_MP_TAC SPAN_INDUCT THEN ASM_SIMP_TAC [IN_ELIM_THM] THEN
        SIMP_TAC [subspace, IN_ELIM_THM, DOT_RMUL, DOT_RADD, DOT_RZERO] THEN
        REAL_ARITH_TAC,
        SIMP_TAC [subspace, IN_ELIM_THM, DOT_LMUL, DOT_LADD, DOT_LZERO] THEN
        REAL_ARITH_TAC],
      REWRITE_TAC [IN_SING] THEN MESON_TAC [DOT_EQ_0]])

  let DIM_SUBSPACE_ORTHOGONAL_TO_VECTORS ← prove
   r"!s t:real^N->bool.
        subspace s /\ subspace t /\ s SUBSET t
        ==> dim {y | y IN t /\ !x. x IN s ==> orthogonal x y} + dim s = dim t"
   (REPEAT STRIP_TAC THEN
    W (MP_TAC o PART_MATCH (rand o rand) DIM_ORTHOGONAL_SUM o lhand o snd) THEN
    ANTS_TAC THENL
     [SIMP_TAC [IN_ELIM_THM, orthogonal] THEN MESON_TAC [DOT_SYM],
      DISCH_THEN (SUBST1_TAC o SYM)] THEN
    ONCE_REWRITE_TAC [← GSYM DIM_SPAN] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC SPAN_MONO THEN ASM SET_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN REWRITE_TAC [SUBSPACE_SPAN] THEN
    REWRITE_TAC [SPAN_UNION, SUBSET, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"x:real^N") THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
    MP_TAC (← ISPECL [← q r"s:real^N->bool", ← q r"x:real^N"]
          ORTHOGONAL_SUBSPACE_DECOMP_EXISTS) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"y:real^N") THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"z:real^N") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [VECTOR_ADD_SYM] THEN
    MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC [IN_ELIM_THM] THEN CONJ_TAC THENL
     [FIRST_ASSUM (SUBST1_TAC o MATCH_MP (← va
       r"x:real^N = y + z ==> z = x - y")) THEN
      MATCH_MP_TAC SUBSPACE_SUB THEN
      ASM_MESON_TAC [SUBSET, SPAN_EQ_SELF],
      ASM_MESON_TAC [SPAN_SUPERSET, ORTHOGONAL_SYM]])

  let DIM_SPECIAL_SUBSPACE ← prove
   r"!k. dim {x:real^N |
            !i. 1 <= i /\ i <= dimindex(:N) /\ i IN k ==> x$i = &0} =
       CARD((1..dimindex(:N)) DIFF k)"
   (GEN_TAC THEN MATCH_MP_TAC DIM_UNIQUE THEN
    EXISTS_TAC (← q r"IMAGE (basis:num->real^N) ((1..dimindex(:N)) DIFF k)") THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
      SIMP_TAC [BASIS_COMPONENT, IN_DIFF, IN_NUMSEG] THEN MESON_TAC [],
      REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"x:real^N") THEN
      DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM BASIS_EXPANSION] THEN
      MATCH_MP_TAC SPAN_VSUM THEN REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
      X_GEN_TAC (← q r"j:num") THEN STRIP_TAC THEN
      ASM_CASES_TAC (← q r"(x:real^N)$j = &0") THEN
      ASM_REWRITE_TAC [SPAN_0, VECTOR_MUL_LZERO] THEN
      MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN
      REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"j:num") THEN
      REWRITE_TAC [IN_NUMSEG, IN_DIFF] THEN ASM_MESON_TAC [],
      MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN
      REWRITE_TAC [pairwise, IMP_CONJ, RIGHT_FORALL_IMP_THM,
        ← SET_RULE (← q r"~(a IN IMAGE f s) <=> (!x. x IN s ==> ~(f x = a))")] THEN
      SIMP_TAC [FORALL_IN_IMAGE, ORTHOGONAL_BASIS_BASIS, BASIS_INJ_EQ,
                IN_DIFF, IN_NUMSEG, BASIS_NONZERO],
      SIMP_TAC [HAS_SIZE, FINITE_IMAGE, FINITE_DIFF, FINITE_NUMSEG] THEN
      MATCH_MP_TAC CARD_IMAGE_INJ THEN
      SIMP_TAC [FINITE_DIFF, FINITE_NUMSEG, IMP_CONJ, RIGHT_FORALL_IMP_THM,
        ← SET_RULE (← q r"~(a IN IMAGE f s) <=> (!x. x IN s ==> ~(f x = a))")] THEN
      SIMP_TAC [FORALL_IN_IMAGE, ORTHOGONAL_BASIS_BASIS, BASIS_INJ_EQ,
                IN_DIFF, IN_NUMSEG, BASIS_NONZERO]])

  return { DIM_SUMS_INTER, DIM_UNION_INTER, DIM_KERNEL_COMPOSE, DIM_ORTHOGONAL_SUM,
           DIM_SUBSPACE_ORTHOGONAL_TO_VECTORS, DIM_SPECIAL_SUBSPACE }

/- ------------------------------------------------------------------------- -/
/- Independence of unions; more injective/surjective versus dimension       -/
/- variants.  (vectors.ml 8518-8667)                                         -/
/- ------------------------------------------------------------------------- -/

structure InjDim where
  INDEPENDENT_UNION : thm
  LINEAR_INJECTIVE_ON_IFF_DIM : thm
  DIM_INJECTIVE_ON_LINEAR_IMAGE : thm
  DIM_EQ_SUBSPACES : thm
  DIM_EQ_SUBSPACE : thm
  LINEAR_SURJECTIVE_ON_IFF_DIM : thm
  LINEAR_INJECTIVE_IMP_SURJECTIVE_ON : thm
  LINEAR_SURJECTIVE_IFF_INJECTIVE_ON : thm
  LINEAR_INJECTIVE_IFF_DIM : thm
  LINEAR_SURJECTIVE_IFF_DIM : thm
  LINEAR_SURJECTIVE_IFF_INJECTIVE_GEN : thm
  MATRIX_INVERTIBLE_LEFT_GEN : thm
  MATRIX_INVERTIBLE_LEFT : thm
  MATRIX_INVERTIBLE_RIGHT_GEN : thm
  MATRIX_INVERTIBLE_RIGHT : thm
  deriving Inhabited

@[nospecialize]
def setupInjDim [HolBase] (D : VectorsDeps) (BSubspace : Subspace) (BSpan1 : Span1)
    (BDim2 : Dim2) (BExplicit : Explicit) (BLinEq : LinEq) (BIso : Iso)
    (BMatInv2 : MatInv2) (BDimKernel : DimKernel) (BDimSums : DimSums) :
    ExceptT String IO InjDim := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, .. } := D
  let { ADD_CLAUSES, CARD_UNION, FINITE_UNION, .. } := D.core1
  let { INJECTIVE_ON_ALT, IN_UNIV, LE, LE_ANTISYM, LE_REFL, .. } := D.core2
  let { HULL_UNION, .. } := D.misc
  let { INDEPENDENT_NONZERO, LINEAR_INJECTIVE_0_SUBSPACE, SUBSPACE_LINEAR_IMAGE,
        SUBSPACE_SPAN, SUBSPACE_UNIV, span, .. } := BSubspace
  let { SPAN_EQ_SELF, SPAN_INC, SPAN_LINEAR_IMAGE, SPAN_UNIV, .. } := BSpan1
  let { DIM_EQ_FULL, DIM_EQ_SPAN, DIM_SPAN, DIM_SUBSET, DIM_UNIV,
        INDEPENDENT_EQ_DIM_EQ_CARD, .. } := BDim2
  let { DIM_EQ_0, DIM_SING, .. } := BExplicit
  let { LINEAR_INJECTIVE_LEFT_INVERSE_EQ, LINEAR_SURJECTIVE_RIGHT_INVERSE_EQ, .. } := BLinEq
  let { LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE_EQ, .. } := BIso
  let { LINEAR_INJECTIVE_DIMINDEX_LE, LINEAR_SURJECTIVE_DIMINDEX_LE, MATRIX_INVERTIBLE,
        .. } := BMatInv2
  let { DIM_IMAGE_KERNEL_GEN, .. } := BDimKernel
  let { DIM_UNION_INTER, .. } := BDimSums
  -- @@SCOPE END

  let INDEPENDENT_UNION ← prove
   r"!s t:real^N->bool.
        independent s /\ independent t /\
        (span s) INTER (span t) SUBSET {vec 0}
        ==> independent(s UNION t)"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"(vec 0:real^N) IN s") THENL
     [ASM_MESON_TAC [INDEPENDENT_NONZERO], ALL_TAC] THEN
    SIMP_TAC [INDEPENDENT_EQ_DIM_EQ_CARD, FINITE_UNION] THEN
    ONCE_REWRITE_TAC [← GSYM DIM_SPAN] THEN
    REWRITE_TAC [span] THEN ONCE_REWRITE_TAC [HULL_UNION] THEN
    REWRITE_TAC [← GSYM span, DIM_SPAN] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"span s:real^N->bool", ← q r"span t:real^N->bool"]
          DIM_UNION_INTER) THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP DIM_SUBSET) THEN
    SIMP_TAC [DIM_SING, SUBSPACE_SPAN, LE, ADD_CLAUSES] THEN
    REPEAT (DISCH_THEN (K ALL_TAC)) THEN CONV_TAC SYM_CONV THEN
    ASM_REWRITE_TAC [DIM_SPAN] THEN MATCH_MP_TAC CARD_UNION THEN
    ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP (← SET_RULE (← q
     r"s' INTER t' SUBSET {z}
    ==> s SUBSET s' /\ t SUBSET t' /\ ~(z IN s) ==> s INTER t = {}"))) THEN
    ASM_REWRITE_TAC [SPAN_INC])

  let LINEAR_INJECTIVE_ON_IFF_DIM ← prove
   r"!f:real^M->real^N s.
        linear f /\ subspace s
        ==> ((!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) <=>
             dim(IMAGE f s) = dim s)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^M->real^N", ← q r"s:real^M->bool"]
          DIM_IMAGE_KERNEL_GEN) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [← ARITH_RULE (← q r"m:num = m + n <=> n = 0")] THEN
    ASM_SIMP_TAC [LINEAR_INJECTIVE_0_SUBSPACE, DIM_EQ_0] THEN SET_TAC [])

  let DIM_INJECTIVE_ON_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N s.
        linear f /\ subspace s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> dim(IMAGE f s) = dim s"
   (MESON_TAC [LINEAR_INJECTIVE_ON_IFF_DIM])

  let DIM_EQ_SUBSPACES ← prove
   r"!s t:real^N->bool.
        subspace s /\ subspace t /\ s SUBSET t /\ dim t <= dim s
        ==> s = t"
   (MESON_TAC [DIM_EQ_SPAN, SPAN_EQ_SELF])

  let DIM_EQ_SUBSPACE ← prove
   r"!s t:real^N->bool.
        subspace s /\ subspace t /\ s SUBSET t
        ==> (dim s = dim t <=> s = t)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC [] THEN
    DISCH_TAC THEN MATCH_MP_TAC DIM_EQ_SUBSPACES THEN
    ASM_REWRITE_TAC [LE_REFL])

  let LINEAR_SURJECTIVE_ON_IFF_DIM ← prove
   r"!f:real^M->real^N s t.
        linear f /\ subspace s /\ subspace t /\ IMAGE f s SUBSET t
        ==> (IMAGE f s = t <=> dim(IMAGE f s) = dim t)"
   (REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC DIM_EQ_SUBSPACE THEN ASM_SIMP_TAC [SUBSPACE_LINEAR_IMAGE])

  let LINEAR_INJECTIVE_IMP_SURJECTIVE_ON ← prove
   r"!f:real^M->real^N s t.
        linear f /\ subspace s /\ subspace t /\
        IMAGE f s SUBSET t /\ dim t <= dim s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> IMAGE f s = t"
   (REWRITE_TAC [INJECTIVE_ON_ALT] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [LINEAR_SURJECTIVE_ON_IFF_DIM] THEN
    ASM_SIMP_TAC [DIM_SUBSET, ← GSYM LE_ANTISYM] THEN
    ASM_SIMP_TAC [LINEAR_INJECTIVE_ON_IFF_DIM] THEN
    ASM_SIMP_TAC [DIM_INJECTIVE_ON_LINEAR_IMAGE, INJECTIVE_ON_ALT])

  let LINEAR_SURJECTIVE_IFF_INJECTIVE_ON ← prove
   r"!f:real^M->real^N s t.
        linear f /\ subspace s /\ subspace t /\
        IMAGE f s SUBSET t /\ dim s = dim t
        ==> (IMAGE f s = t <=>
             !x y. x IN s /\ y IN s /\ f x = f y ==> x = y)"
   (SIMP_TAC [LINEAR_SURJECTIVE_ON_IFF_DIM, LINEAR_INJECTIVE_ON_IFF_DIM])

  let LINEAR_INJECTIVE_IFF_DIM ← prove
   r"!f:real^M->real^N.
        linear f
        ==> ((!x y. f x = f y ==> x = y) <=>
             dim(IMAGE f (:real^M)) = dimindex(:M))"
   (SIMP_TAC [← GSYM LINEAR_INJECTIVE_ON_IFF_DIM, ← GSYM DIM_UNIV, SUBSPACE_UNIV] THEN
    REWRITE_TAC [IN_UNIV])

  let LINEAR_SURJECTIVE_IFF_DIM ← prove
   r"!f:real^M->real^N.
        linear f
        ==> ((!y. ?x. f x = y) <=>
             dim(IMAGE f (:real^M)) = dimindex(:N))"
   (SIMP_TAC [DIM_EQ_FULL, SPAN_LINEAR_IMAGE, SPAN_UNIV] THEN SET_TAC [])

  let LINEAR_SURJECTIVE_IFF_INJECTIVE_GEN ← prove
   r"!f:real^M->real^N.
      dimindex(:M) = dimindex(:N) /\ linear f
      ==> ((!y. ?x. f x = y) <=> (!x y. f x = f y ==> x = y))"
   (SIMP_TAC [LINEAR_INJECTIVE_IFF_DIM, LINEAR_SURJECTIVE_IFF_DIM] THEN
    MESON_TAC [])

  let MATRIX_INVERTIBLE_LEFT_GEN ← prove
   r"!f:real^M->real^N.
        linear f /\ dimindex(:N) <= dimindex(:M)
        ==> (invertible(matrix f) <=> ?g. linear g /\ g o f = I)"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [MATRIX_INVERTIBLE] THEN
    ASM_SIMP_TAC [← GSYM LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE_EQ,
                  ← GSYM LINEAR_INJECTIVE_LEFT_INVERSE_EQ] THEN
    REWRITE_TAC [← TAUT (← q r"(p /\ q <=> p) <=> p ==> (q <=> p)")] THEN
    DISCH_TAC THEN MATCH_MP_TAC LINEAR_SURJECTIVE_IFF_INJECTIVE_GEN THEN
    ASM_REWRITE_TAC [← GSYM LE_ANTISYM] THEN
    MATCH_MP_TAC LINEAR_INJECTIVE_DIMINDEX_LE THEN
    ASM_MESON_TAC [])

  let MATRIX_INVERTIBLE_LEFT ← prove
   r"!f:real^N->real^N.
        linear f
        ==> (invertible(matrix f) <=> ?g. linear g /\ g o f = I)"
   (SIMP_TAC [MATRIX_INVERTIBLE_LEFT_GEN, LE_REFL])

  let MATRIX_INVERTIBLE_RIGHT_GEN ← prove
   r"!f:real^M->real^N.
        linear f /\ dimindex(:M) <= dimindex(:N)
        ==> (invertible(matrix f) <=> ?g. linear g /\ f o g = I)"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [MATRIX_INVERTIBLE] THEN
    ASM_SIMP_TAC [← GSYM LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE_EQ,
                  ← GSYM LINEAR_SURJECTIVE_RIGHT_INVERSE_EQ] THEN
    REWRITE_TAC [← TAUT (← q r"(q /\ p <=> p) <=> p ==> (p <=> q)")] THEN
    DISCH_TAC THEN MATCH_MP_TAC LINEAR_SURJECTIVE_IFF_INJECTIVE_GEN THEN
    ASM_REWRITE_TAC [← GSYM LE_ANTISYM] THEN
    MATCH_MP_TAC LINEAR_SURJECTIVE_DIMINDEX_LE THEN
    ASM_MESON_TAC [])

  let MATRIX_INVERTIBLE_RIGHT ← prove
   r"!f:real^N->real^N.
        linear f
        ==> (invertible(matrix f) <=> ?g. linear g /\ f o g = I)"
   (SIMP_TAC [MATRIX_INVERTIBLE_RIGHT_GEN, LE_REFL])

  return { INDEPENDENT_UNION, LINEAR_INJECTIVE_ON_IFF_DIM, DIM_INJECTIVE_ON_LINEAR_IMAGE,
           DIM_EQ_SUBSPACES, DIM_EQ_SUBSPACE, LINEAR_SURJECTIVE_ON_IFF_DIM,
           LINEAR_INJECTIVE_IMP_SURJECTIVE_ON, LINEAR_SURJECTIVE_IFF_INJECTIVE_ON,
           LINEAR_INJECTIVE_IFF_DIM, LINEAR_SURJECTIVE_IFF_DIM,
           LINEAR_SURJECTIVE_IFF_INJECTIVE_GEN, MATRIX_INVERTIBLE_LEFT_GEN,
           MATRIX_INVERTIBLE_LEFT, MATRIX_INVERTIBLE_RIGHT_GEN, MATRIX_INVERTIBLE_RIGHT }

/- ------------------------------------------------------------------------- -/
/- More about product spaces.  (vectors.ml 8672-8793)                        -/
/- ------------------------------------------------------------------------- -/

structure PCrossDim where
  PASTECART_AS_ORTHOGONAL_SUM : thm
  PCROSS_AS_ORTHOGONAL_SUM : thm
  DIM_PCROSS : thm
  SPAN_PCROSS_SUBSET : thm
  SPAN_PCROSS : thm
  DIM_PCROSS_STRONG : thm
  SPAN_SUMS : thm
  deriving Inhabited

@[nospecialize]
def setupPCrossDim [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BLinear : Linear) (BPaste1 : Paste1) (BSubspace : Subspace) (BSpan1 : Span1)
    (BDim2 : Dim2) (BExplicit : Explicit) (BMatInv2 : MatInv2) (BDimSums : DimSums) :
    ExceptT String IO PCrossDim := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON_TAC, SET_TAC, .. } := D
  let { FORALL_IN_GSPEC, .. } := D.core1
  let { FORALL_IN_PCROSS, FSTCART_PASTECART, IN_ELIM_THM, IN_IMAGE, IN_INTER, IN_SING,
        IN_UNION, MEMBER_NOT_EMPTY, .. } := D.core2
  let { PASTECART_EQ, PASTECART_INJ, PASTECART_IN_PCROSS, PCROSS, PCROSS_MONO, .. } := D.core3
  let { SNDCART_PASTECART, SUBSET, SUBSET_ANTISYM, .. } := D.core4
  let { VECTOR_ADD_LID, VECTOR_ADD_RID, VECTOR_ARITH, VECTOR_ARITH_TAC, VECTOR_MUL_RZERO,
        .. } := BVectorArith
  let { linear, .. } := BLinear
  let { FSTCART_VEC, PASTECART_ADD, PASTECART_CMUL, PASTECART_SUB, PASTECART_VEC,
        SNDCART_VEC, .. } := BPaste1
  let { SPAN_INDUCT, SUBSPACE_LINEAR_IMAGE, SUBSPACE_PCROSS, SUBSPACE_SPAN, subspace,
        .. } := BSubspace
  let { SPAN_0, SPAN_ADD, SPAN_INC, SPAN_MUL, SPAN_SUB, SPAN_SUBSET_SUBSPACE, SPAN_SUPERSET,
        SPAN_UNION, .. } := BSpan1
  let { DIM_SPAN, .. } := BDim2
  let { DIM_EQ_0, .. } := BExplicit
  let { DIM_INJECTIVE_LINEAR_IMAGE, .. } := BMatInv2
  let { DIM_SUMS_INTER, .. } := BDimSums
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let PASTECART_AS_ORTHOGONAL_SUM ← prove
   r"!x:real^M y:real^N.
        pastecart x y = pastecart x (vec 0) + pastecart (vec 0) y"
   (REWRITE_TAC [PASTECART_ADD, VECTOR_ADD_LID, VECTOR_ADD_RID])

  let PCROSS_AS_ORTHOGONAL_SUM ← prove
   r"!s:real^M->bool t:real^N->bool.
        s PCROSS t =
        {u + v | u IN IMAGE (\x. pastecart x (vec 0)) s /\
                 v IN IMAGE (\y. pastecart (vec 0) y) t}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [PCROSS] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [PASTECART_AS_ORTHOGONAL_SUM] THEN
    SET_TAC [])

  let DIM_PCROSS ← prove
   r"!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t ==> dim(s PCROSS t) = dim s + dim t"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [PCROSS_AS_ORTHOGONAL_SUM] THEN
    W (MP_TAC o PART_MATCH (lhand o lhand o rand) DIM_SUMS_INTER o
          lhand o snd) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SUBSPACE_LINEAR_IMAGE,
      MATCH_MP_TAC (← ARITH_RULE (← q r"c = d /\ b = 0 ==> a + b = c ==> a = d")) THEN
      CONJ_TAC THENL
       [BINOP_TAC THEN MATCH_MP_TAC DIM_INJECTIVE_LINEAR_IMAGE THEN
        SIMP_TAC [PASTECART_INJ],
        REWRITE_TAC [DIM_EQ_0, SUBSET, IN_INTER, IN_IMAGE, IN_SING] THEN
        REWRITE_TAC [PASTECART_EQ, FSTCART_PASTECART, SNDCART_PASTECART] THEN
        MESON_TAC [FSTCART_VEC, SNDCART_VEC]]] THEN
    ASM_REWRITE_TAC [linear, ← GSYM PASTECART_VEC] THEN
    REWRITE_TAC [PASTECART_ADD, ← GSYM PASTECART_CMUL, PASTECART_INJ] THEN
    VECTOR_ARITH_TAC)

  let SPAN_PCROSS_SUBSET ← prove
   r"!s:real^M->bool t:real^N->bool.
        span(s PCROSS t) SUBSET (span s) PCROSS (span t)"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
    SIMP_TAC [SUBSPACE_PCROSS, SUBSPACE_SPAN, PCROSS_MONO, SPAN_INC])

  let SPAN_PCROSS ← prove
   r"!s:real^M->bool t:real^N->bool.
        ~(s = {}) /\ ~(t = {}) /\ (vec 0 IN s \/ vec 0 IN t)
        ==> span(s PCROSS t) = (span s) PCROSS (span t)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC [SPAN_PCROSS_SUBSET] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_PCROSS] THEN
    ONCE_REWRITE_TAC [PASTECART_AS_ORTHOGONAL_SUM] THEN
    SUBGOAL_THEN
     (← q r"(!x:real^M. x IN span s ==> pastecart x (vec 0) IN span(s PCROSS t)) /\
    (!y:real^N. y IN span t ==> pastecart (vec 0) y IN span(s PCROSS t))")
     (fun th => ASM_MESON_TAC [th, SPAN_ADD]) THEN
    CONJ_TAC THEN MATCH_MP_TAC SPAN_INDUCT THEN REWRITE_TAC [IN_ELIM_THM] THEN
    (CONJ_TAC THENL
      [REWRITE_TAC [IN_ELIM_THM] THEN
       ASM_SIMP_TAC [SPAN_SUPERSET, PASTECART_IN_PCROSS],
       REWRITE_TAC [subspace, IN_ELIM_THM, PASTECART_VEC, SPAN_0] THEN
       CONJ_TAC THEN REPEAT GEN_TAC THENL
        [DISCH_THEN (MP_TAC o MATCH_MP SPAN_ADD) THEN
         REWRITE_TAC [PASTECART_ADD, VECTOR_ADD_LID],
         DISCH_THEN (MP_TAC o MATCH_MP SPAN_MUL) THEN
         SIMP_TAC [← GSYM PASTECART_CMUL, VECTOR_MUL_RZERO]]])
    THENL
     [X_GEN_TAC (← q r"x:real^M") THEN DISCH_TAC THEN
      UNDISCH_TAC (← q r"~(t:real^N->bool = {})") THEN
      REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"y:real^N")) THEN
      SUBGOAL_THEN
       (← q r"pastecart x (vec 0) =
      pastecart (x:real^M) (y:real^N) - pastecart (vec 0) y")
      SUBST1_TAC THENL
       [REWRITE_TAC [PASTECART_SUB, PASTECART_INJ] THEN VECTOR_ARITH_TAC,
        MATCH_MP_TAC SPAN_SUB THEN
        ASM_SIMP_TAC [SPAN_SUPERSET, PASTECART_IN_PCROSS]],
      X_GEN_TAC (← q r"y:real^N") THEN DISCH_TAC THEN
      UNDISCH_TAC (← q r"~(s:real^M->bool = {})") THEN
      REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"x:real^M")) THEN
      SUBGOAL_THEN
       (← q r"pastecart (vec 0) y =
      pastecart (x:real^M) (y:real^N) - pastecart x (vec 0)")
      SUBST1_TAC THENL
       [REWRITE_TAC [PASTECART_SUB, PASTECART_INJ] THEN VECTOR_ARITH_TAC,
        MATCH_MP_TAC SPAN_SUB THEN
        ASM_SIMP_TAC [SPAN_SUPERSET, PASTECART_IN_PCROSS]]])

  let DIM_PCROSS_STRONG ← prove
   r"!s:real^M->bool t:real^N->bool.
        ~(s = {}) /\ ~(t = {}) /\ (vec 0 IN s \/ vec 0 IN t)
        ==> dim(s PCROSS t) = dim s + dim t"
   (ONCE_REWRITE_TAC [← GSYM DIM_SPAN] THEN
    SIMP_TAC [SPAN_PCROSS, DIM_PCROSS, SUBSPACE_SPAN])

  let SPAN_SUMS ← prove
   r"!s t:real^N->bool.
        ~(s = {}) /\ ~(t = {}) /\ vec 0 IN (s UNION t)
        ==> span {x + y | x IN s /\ y IN t} =
            {x + y | x IN span s /\ y IN span t}"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM SPAN_UNION] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    CONJ_TAC THEN MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
    REWRITE_TAC [SUBSPACE_SPAN, SUBSET, FORALL_IN_GSPEC] THEN
    SIMP_TAC [SPAN_ADD, IN_UNION, SPAN_SUPERSET] THEN
    X_GEN_TAC (← q r"x:real^N") THEN STRIP_TAC THEN
    FIRST_X_ASSUM (DISJ_CASES_TAC o GEN_REWRITE_RULE id [IN_UNION]) THENL
     [UNDISCH_TAC (← q r"~(t:real^N->bool = {})") THEN
      REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"y:real^N")) THEN
      SUBST1_TAC (← va r"x:real^N = (x + y) - (vec 0 + y)") THEN
      MATCH_MP_TAC SPAN_SUB THEN CONJ_TAC THEN MATCH_MP_TAC SPAN_SUPERSET THEN
      ASM SET_TAC [],
      MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC [IN_ELIM_THM] THEN
      ASM_MESON_TAC [VECTOR_ADD_RID],
      MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC [IN_ELIM_THM] THEN
      ASM_MESON_TAC [VECTOR_ADD_LID],
      UNDISCH_TAC (← q r"~(s:real^N->bool = {})") THEN
      REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"y:real^N")) THEN
      SUBST1_TAC (← va r"x:real^N = (y + x) - (y + vec 0)") THEN
      MATCH_MP_TAC SPAN_SUB THEN CONJ_TAC THEN MATCH_MP_TAC SPAN_SUPERSET THEN
      ASM SET_TAC []])

  return { PASTECART_AS_ORTHOGONAL_SUM, PCROSS_AS_ORTHOGONAL_SUM, DIM_PCROSS,
           SPAN_PCROSS_SUBSET, SPAN_PCROSS, DIM_PCROSS_STRONG, SPAN_SUMS }

/- ------------------------------------------------------------------------- -/
/- More about rank from the rank/nullspace formula.  (vectors.ml 8798-8890)  -/
/- ------------------------------------------------------------------------- -/

structure RankNull where
  RANK_NULLSPACE : thm
  RANK_SYLVESTER : thm
  RANK_GRAM : thm
  RANK_TRIANGLE : thm
  COVARIANCE_MATRIX_EQ_0 : thm
  MATRIX_MUL_COVARIANCE_LCANCEL : thm
  MATRIX_MUL_COVARIANCE_RCANCEL : thm
  MATRIX_VECTOR_MUL_COVARIANCE_EQ_0 : thm
  deriving Inhabited

@[nospecialize]
def setupRankNull [HolBase] (D : VectorsDeps) (BDotProps : DotProps)
    (BMatArith : MatArith) (BMatProps : MatProps) (BInvertible : Invertible)
    (BSubspace : Subspace) (BDim2 : Dim2) (BRank : Rank) (BDimKernel : DimKernel)
    (BDimSums : DimSums) : ExceptT String IO RankNull := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, MESON, MESON_TAC, .. } := D
  let { ADD_SYM, ETA_AX, FORALL_IN_IMAGE, .. } := D.core1
  let { IN_ELIM_THM, IN_IMAGE, IN_UNIV, .. } := D.core2
  let { SUBSET, SUBSET_ANTISYM, .. } := D.core4
  let { o_DEF, .. } := D.core5
  let { DOT_EQ_0, DOT_RZERO, .. } := BDotProps
  let { MATRIX_MUL_ASSOC, MATRIX_MUL_RZERO, MATRIX_SUB_EQ, MATRIX_SUB_LDISTRIB,
        MATRIX_SUB_RDISTRIB, MATRIX_VECTOR_MUL_ADD_RDISTRIB, MATRIX_VECTOR_MUL_ASSOC,
        MATRIX_VECTOR_MUL_RZERO, .. } := BMatArith
  let { DOT_LMUL_MATRIX, MATRIX_TRANSP_MUL, TRANSP_EQ, TRANSP_MATRIX_SUB, TRANSP_TRANSP,
        VECTOR_MATRIX_MUL_TRANSP, .. } := BMatProps
  let { DOT_MATRIX_TRANSP_RMUL, MATRIX_VECTOR_MUL_LINEAR, .. } := BInvertible
  let { SUBSPACE_LINEAR_IMAGE, SUBSPACE_UNIV, .. } := BSubspace
  let { DIM_SUBSET, .. } := BDim2
  let { RANK_DIM_IM, RANK_EQ_0, .. } := BRank
  let { DIM_IMAGE_KERNEL, .. } := BDimKernel
  let { DIM_KERNEL_COMPOSE, DIM_SUMS_INTER, .. } := BDimSums
  -- @@SCOPE END

  let RANK_NULLSPACE ← prove
   r"!A:real^M^N. rank A + dim {x | A ** x = vec 0} = dimindex(:M)"
   (GEN_TAC THEN REWRITE_TAC [RANK_DIM_IM] THEN
    MATCH_MP_TAC DIM_IMAGE_KERNEL THEN
    REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR])

  let RANK_SYLVESTER ← prove
   r"!A:real^N^M B:real^P^N.
        rank(A) + rank(B) <= rank(A ** B) + dimindex(:N)"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC (← ARITH_RULE (← q
      r"!ia ib iab p:num.
        ra + ia = n /\
        rb + ib = p /\
        rab + iab = p /\
        iab <= ia + ib
        ==> ra + rb <= rab + n")) THEN
    MAP_EVERY EXISTS_TAC
     [← q r"dim {x | (A:real^N^M) ** x = vec 0}",
      ← q r"dim {x | (B:real^P^N) ** x = vec 0}",
      ← q r"dim {x | ((A:real^N^M) ** (B:real^P^N)) ** x = vec 0}",
      ← q r"dimindex(:P)"] THEN
    REWRITE_TAC [RANK_NULLSPACE] THEN
    REWRITE_TAC [← GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    MATCH_MP_TAC (← REWRITE_RULE [o_DEF] DIM_KERNEL_COMPOSE) THEN
    CONJ_TAC THEN GEN_REWRITE_TAC RAND_CONV [← GSYM ETA_AX] THEN
    REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR])

  let RANK_GRAM ← prove
   r"!A:real^M^N. rank(transp A ** A) = rank A"
   (GEN_TAC THEN MATCH_MP_TAC (← ARITH_RULE (← q
     r"!n n' k. r + n:num = k /\ r' + n' = k /\ n = n' ==> r = r'")) THEN
    MAP_EVERY EXISTS_TAC
     [← q r"dim {x | (transp A ** (A:real^M^N)) ** x = vec 0}",
      ← q r"dim {x | (A:real^M^N) ** x = vec 0}",
      ← q r"dimindex(:M)"] THEN
    REWRITE_TAC [RANK_NULLSPACE] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM, ← GSYM MATRIX_VECTOR_MUL_ASSOC,
              MATRIX_VECTOR_MUL_RZERO] THEN
    X_GEN_TAC (← q r"x:real^M") THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"(dot) (x:real^M)")) THEN
    ONCE_REWRITE_TAC [← GSYM DOT_LMUL_MATRIX] THEN
    REWRITE_TAC [VECTOR_MATRIX_MUL_TRANSP, TRANSP_TRANSP, DOT_RZERO] THEN
    REWRITE_TAC [DOT_EQ_0])

  let RANK_TRIANGLE ← prove
   r"!A B:real^M^N. rank(A + B) <= rank(A) + rank(B)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [RANK_DIM_IM] THEN
    MP_TAC (← ISPECL [← q r"IMAGE (\x. (A:real^M^N) ** x) (:real^M)",
                      ← q r"IMAGE (\x. (B:real^M^N) ** x) (:real^M)"]
                  DIM_SUMS_INTER) THEN
    ASM_SIMP_TAC [SUBSPACE_LINEAR_IMAGE, SUBSPACE_UNIV,
                  MATRIX_VECTOR_MUL_LINEAR] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC (← ARITH_RULE (← q r"x:num <= y ==> x <= y + z")) THEN
    MATCH_MP_TAC DIM_SUBSET THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_UNIV,
                 MATRIX_VECTOR_MUL_ADD_RDISTRIB] THEN
    REWRITE_TAC [IN_ELIM_THM, IN_IMAGE, IN_UNIV] THEN MESON_TAC [])

  let COVARIANCE_MATRIX_EQ_0 ← prove
   r"!A:real^N^M. transp A ** A = mat 0 <=> A = mat 0"
   (REWRITE_TAC [← GSYM RANK_EQ_0, RANK_GRAM])

  let MATRIX_MUL_COVARIANCE_LCANCEL ← prove
   r"!A:real^N^P B C:real^M^N.
        (transp A ** A) ** B = (transp A ** A) ** C <=> A ** B = A ** C"
   (REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC [← GSYM MATRIX_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC [← GSYM MATRIX_SUB_EQ] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM COVARIANCE_MATRIX_EQ_0] THEN
    MATCH_MP_TAC (← MESON [MATRIX_MUL_RZERO] (← q
     r"(?C:real^M^N. C ** A = B) ==> A = mat 0 ==> B = mat 0")) THEN
    EXISTS_TAC (← q r"transp(B - C:real^M^N)") THEN
    REWRITE_TAC [TRANSP_MATRIX_SUB, MATRIX_TRANSP_MUL] THEN
    REWRITE_TAC [MATRIX_SUB_LDISTRIB, MATRIX_SUB_RDISTRIB] THEN
    REWRITE_TAC [← GSYM MATRIX_MUL_ASSOC])

  let MATRIX_MUL_COVARIANCE_RCANCEL ← prove
   r"!A:real^P^N B C:real^N^M.
        B ** (A ** transp A) = C ** (A ** transp A) <=> B ** A = C ** A"
   (ONCE_REWRITE_TAC [← GSYM TRANSP_EQ] THEN
    REWRITE_TAC [MATRIX_TRANSP_MUL] THEN
    REWRITE_TAC [MATRIX_MUL_COVARIANCE_LCANCEL])

  let MATRIX_VECTOR_MUL_COVARIANCE_EQ_0 ← prove
   r"!A:real^M^N x. (transp A ** A) ** x = vec 0 <=> A ** x = vec 0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    EQ_TAC THEN SIMP_TAC [MATRIX_VECTOR_MUL_RZERO] THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"(dot) (x:real^M)")) THEN
    REWRITE_TAC [DOT_MATRIX_TRANSP_RMUL, DOT_RZERO] THEN
    REWRITE_TAC [DOT_EQ_0])

  return { RANK_NULLSPACE, RANK_SYLVESTER, RANK_GRAM, RANK_TRIANGLE,
           COVARIANCE_MATRIX_EQ_0, MATRIX_MUL_COVARIANCE_LCANCEL,
           MATRIX_MUL_COVARIANCE_RCANCEL, MATRIX_VECTOR_MUL_COVARIANCE_EQ_0 }

/- ------------------------------------------------------------------------- -/
/- Inverse matrices, in general Moore-Penrose pseudoinverses.                -/
/- (vectors.ml 8898-9073)                                                     -/
/- ------------------------------------------------------------------------- -/

structure MatPinv where
  matrix_inv : thm
  MOORE_PENROSE_PSEUDOINVERSE : thm
  MOORE_PENROSE_PSEUDOINVERSE_UNIQUE : thm
  MATRIX_INV_MUL_INNER : thm
  SYMMETRIC_MATRIX_INV_RMUL : thm
  MATRIX_INV_INV : thm
  MATRIX_INV_EQ : thm
  MATRIX_INV_MUL_OUTER : thm
  SYMMETRIC_MATRIX_INV_LMUL : thm
  MATRIX_INV_UNIQUE_STRONG : thm
  MATRIX_INV_TRANSP : thm
  TRANSP_MATRIX_INV : thm
  SYMMETRIC_MATRIX_INV : thm
  deriving Inhabited

@[nospecialize]
def setupMatPinv [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BOrth : Orth) (BLinear : Linear) (BAdjoint : Adjoint) (BMatrix : Matrix)
    (BMatArith : MatArith) (BMatProps : MatProps) (BInvertible : Invertible)
    (BSubspace : Subspace) (BSpan1 : Span1) (BLinEq : LinEq) (BIndepSub : IndepSub) :
    ExceptT String IO MatPinv := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, new_definition, .. } := D
  let { EQ_TRANS, ETA_AX, EXISTS_IN_IMAGE, FORALL_AND_THM, FORALL_IN_IMAGE, .. } := D.core1
  let { FUN_EQ_THM, IN_ELIM_THM, IN_UNIV, MONO_EXISTS, .. } := D.core2
  let { RIGHT_EXISTS_AND_THM, .. } := D.core4
  let { SWAP_EXISTS_THM, o_DEF, .. } := D.core5
  let { VECTOR_ARITH, VECTOR_NEG_SUB, VECTOR_SUB_EQ, VECTOR_SUB_LDISTRIB, VECTOR_SUB_RZERO,
        .. } := BVectorArith
  let { ORTHOGONAL_CLAUSES, ORTHOGONAL_LNEG, ORTHOGONAL_REFL, ORTHOGONAL_SYM, .. } := BOrth
  let { LINEAR_SUB, linear, .. } := BLinear
  let { ORTHOGONAL_PROJECTION_ALT, ORTHOGONAL_PROJECTION_EQ_SELF_ADJOINT_IDEMPOTENT,
        .. } := BAdjoint
  let { symmetric_matrix, .. } := BMatrix
  let { MATRIX_MUL_ASSOC, MATRIX_VECTOR_MUL_ADD_LDISTRIB, MATRIX_VECTOR_MUL_ASSOC,
        MATRIX_VECTOR_MUL_RMUL, MATRIX_VECTOR_MUL_RZERO, MATRIX_VECTOR_MUL_SUB_LDISTRIB,
        .. } := BMatArith
  let { MATRIX_EQ, MATRIX_TRANSP_MUL, TRANSP_EQ, TRANSP_TRANSP, .. } := BMatProps
  let { ADJOINT_MATRIX, MATRIX_VECTOR_MUL_LINEAR, MATRIX_WORKS, .. } := BInvertible
  let { SUBSPACE_LINEAR_IMAGE, SUBSPACE_UNIV, .. } := BSubspace
  let { SPAN_OF_SUBSPACE, .. } := BSpan1
  let { SUBSPACE_KERNEL, .. } := BLinEq
  let { ORTHOGONAL_SUBSPACE_DECOMP_EXISTS, .. } := BIndepSub
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let matrix_inv ← new_definition
   r"matrix_inv (A:real^M^N) =
    matrix(\y. @x. (!w. A ** w = vec 0 ==> orthogonal x w) /\
                   (!z. orthogonal (y - A ** x) (A ** z)))"

  let (MOORE_PENROSE_PSEUDOINVERSE, MOORE_PENROSE_PSEUDOINVERSE_UNIQUE) ← do
    let lemma_existence ← prove
     r"!f:real^M->real^N y.
          linear f
          ==> ?x. (!w. f w = vec 0 ==> orthogonal x w) /\
                  (!z. orthogonal (y - f x) (f z))"
     (REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"?u. !z. orthogonal (y - (f:real^M->real^N) u) (f z)")
      STRIP_ASSUME_TAC THENL
       [MP_TAC (← ISPECL [← q r"IMAGE (f:real^M->real^N) UNIV", ← q r"y:real^N"]
            ORTHOGONAL_SUBSPACE_DECOMP_EXISTS) THEN
        ASM_SIMP_TAC [SPAN_OF_SUBSPACE, SUBSPACE_LINEAR_IMAGE, SUBSPACE_UNIV] THEN
        REWRITE_TAC [RIGHT_EXISTS_AND_THM, EXISTS_IN_IMAGE, FORALL_IN_IMAGE] THEN
        MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC [IN_UNIV] THEN
        MESON_TAC [← va r"y:real^N = x + z <=> y - x = z"],
        MP_TAC (← ISPECL [← q r"{v | (f:real^M->real^N) v = vec 0}", ← q r"u:real^M"]
            ORTHOGONAL_SUBSPACE_DECOMP_EXISTS) THEN
        ASM_SIMP_TAC [SPAN_OF_SUBSPACE, SUBSPACE_KERNEL] THEN
        ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
        X_GEN_TAC (← q r"w:real^M") THEN REWRITE_TAC [IN_ELIM_THM] THEN
        ONCE_REWRITE_TAC [← va r"y:real^N = x + z <=> y - x = z"] THEN
        DISCH_THEN (X_CHOOSE_THEN (← q r"v:real^M") STRIP_ASSUME_TAC) THEN
        EXPAND_TAC "w" THEN ASM_SIMP_TAC [LINEAR_SUB, VECTOR_SUB_RZERO]])
    let lemma_uniqueness ← prove
     r"!A:real^M^N u v y.
        (!w. A ** w = vec 0 ==> orthogonal u w) /\
        (!z. orthogonal (y - A ** u) (A ** z)) /\
        (!w. A ** w = vec 0 ==> orthogonal v w) /\
        (!z. orthogonal (y - A ** v) (A ** z))
        ==> u = v"
     (REPEAT STRIP_TAC THEN
      ONCE_REWRITE_TAC [← GSYM VECTOR_SUB_EQ] THEN
      REWRITE_TAC [← GSYM ORTHOGONAL_REFL] THEN
      MATCH_MP_TAC (CONJUNCTS ORTHOGONAL_CLAUSES).getLast! THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC [← GSYM ORTHOGONAL_REFL] THEN
      (SUBGOAL_THEN
       (← q r"(A:real^M^N) ** (u - v:real^M) = (y - A ** v) - (y - A ** u)") MP_TAC
       THENL
        [SIMP_TAC [MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN CONV_TAC (fun t => VECTOR_ARITH t),
         DISCH_THEN (fun th => GEN_REWRITE_TAC LAND_CONV [th])]) THEN
      ASM_MESON_TAC [ORTHOGONAL_CLAUSES])
    let MOORE_PENROSE_PSEUDOINVERSE ← prove
     r"!A:real^M^N y.
           (!w. A ** w = vec 0 ==> orthogonal (matrix_inv A ** y) w) /\
           (!z. orthogonal (y - A ** (matrix_inv A ** y)) (A ** z))"
     (REPEAT GEN_TAC THEN REWRITE_TAC [matrix_inv] THEN
      MP_TAC (← ISPEC (← q r"\x:real^M. (A:real^M^N) ** x") lemma_existence) THEN
      REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR] THEN
      DISCH_THEN (MP_TAC o GEN (← q r"y:real^N") o SELECT_RULE o SPEC (← q r"y:real^N")) THEN
      ABBREV_TAC
       (← q r"f y = @x. (!w. (A:real^M^N) ** w = vec 0 ==> orthogonal x w) /\
                (!z. orthogonal (y - A ** x) (A ** z))") THEN
      REWRITE_TAC [FORALL_AND_THM, ETA_AX] THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"linear(f:real^N->real^M)") ASSUME_TAC THENL
       [ALL_TAC, ASM_SIMP_TAC [MATRIX_WORKS]] THEN
      REWRITE_TAC [linear] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC lemma_uniqueness THEN EXISTS_TAC (← q r"A:real^M^N") THENL
       [EXISTS_TAC (← q r"x + y:real^N"), EXISTS_TAC (← q r"c % x:real^N")] THEN
      ASM_REWRITE_TAC [] THEN
      ASM_SIMP_TAC [ORTHOGONAL_CLAUSES, MATRIX_VECTOR_MUL_RMUL,
        ← GSYM VECTOR_SUB_LDISTRIB, MATRIX_VECTOR_MUL_ADD_LDISTRIB,
        ← va r"(x + y) - (u + v):real^N = (x - u) + (y - v)"])
    let MOORE_PENROSE_PSEUDOINVERSE_UNIQUE ← prove
     r"!A:real^M^N x y.
           (!w. A ** w = vec 0 ==> orthogonal x w) /\
           (!z. orthogonal (y - A ** x) (A ** z))
           ==> matrix_inv A ** y = x"
     (REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma_uniqueness THEN
      EXISTS_TAC (← q r"A:real^M^N") THEN EXISTS_TAC (← q r"y:real^N") THEN
      ASM_REWRITE_TAC [MOORE_PENROSE_PSEUDOINVERSE])
    pure (MOORE_PENROSE_PSEUDOINVERSE, MOORE_PENROSE_PSEUDOINVERSE_UNIQUE)

  let MATRIX_INV_MUL_INNER ← prove
   r"!A:real^M^N. A ** matrix_inv A ** A = A"
   (SIMP_TAC [MATRIX_EQ, MATRIX_MUL_ASSOC, ← GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
    ONCE_REWRITE_TAC [← GSYM VECTOR_SUB_EQ] THEN
    REWRITE_TAC [← GSYM ORTHOGONAL_REFL] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN
    REWRITE_TAC [MOORE_PENROSE_PSEUDOINVERSE])

  let SYMMETRIC_MATRIX_INV_RMUL ← prove
   r"!A:real^M^N. symmetric_matrix(A ** matrix_inv A)"
   (GEN_TAC THEN REWRITE_TAC [symmetric_matrix] THEN
    MP_TAC (← ISPEC (← q r"\x:real^N. ((A:real^M^N) ** matrix_inv A) ** x")
      ORTHOGONAL_PROJECTION_EQ_SELF_ADJOINT_IDEMPOTENT) THEN
    SIMP_TAC [ADJOINT_MATRIX, ORTHOGONAL_PROJECTION_ALT, MATRIX_VECTOR_MUL_ASSOC,
              MATRIX_VECTOR_MUL_LINEAR, o_DEF, FUN_EQ_THM, ← GSYM MATRIX_EQ] THEN
    MATCH_MP_TAC (← TAUT (← q r"p ==> (p <=> q /\ r) ==> q")) THEN
    ONCE_REWRITE_TAC [← GSYM ORTHOGONAL_LNEG] THEN
    REWRITE_TAC [VECTOR_NEG_SUB, ← GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC [MOORE_PENROSE_PSEUDOINVERSE])

  let MATRIX_INV_INV ← prove
   r"!A:real^M^N. matrix_inv (matrix_inv A) = A"
   (REWRITE_TAC [MATRIX_EQ] THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC MOORE_PENROSE_PSEUDOINVERSE_UNIQUE THEN
    MP_TAC (← ISPEC (← q r"A:real^M^N") MOORE_PENROSE_PSEUDOINVERSE) THEN
    REWRITE_TAC [FORALL_AND_THM] THEN REPEAT STRIP_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o SPECL [← q r"w:real^N", ← q r"x:real^M"]) THEN
      ASM_REWRITE_TAC [VECTOR_SUB_RZERO, ORTHOGONAL_SYM,
                       MATRIX_VECTOR_MUL_RZERO],
      ONCE_REWRITE_TAC [ORTHOGONAL_SYM] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC [MATRIX_VECTOR_MUL_SUB_LDISTRIB, VECTOR_SUB_EQ] THEN
      REWRITE_TAC [MATRIX_VECTOR_MUL_ASSOC, ← GSYM MATRIX_MUL_ASSOC] THEN
      REWRITE_TAC [MATRIX_INV_MUL_INNER]])

  let MATRIX_INV_EQ ← prove
   r"!A B:real^M^N. matrix_inv A = matrix_inv B <=> A = B"
   (MESON_TAC [MATRIX_INV_INV])

  let MATRIX_INV_MUL_OUTER ← prove
   r"!A:real^M^N. matrix_inv A ** A ** matrix_inv A = matrix_inv A"
   (GEN_TAC THEN
    MP_TAC (← ISPEC (← q r"matrix_inv(A:real^M^N)") MATRIX_INV_MUL_INNER) THEN
    REWRITE_TAC [MATRIX_INV_INV])

  let SYMMETRIC_MATRIX_INV_LMUL ← prove
   r"!A:real^M^N. symmetric_matrix(matrix_inv A ** A)"
   (GEN_TAC THEN
    MP_TAC (← ISPEC (← q r"matrix_inv(A:real^M^N)") SYMMETRIC_MATRIX_INV_RMUL) THEN
    REWRITE_TAC [MATRIX_INV_INV])

  let MATRIX_INV_UNIQUE_STRONG ← prove
   r"!A:real^M^N X.
        A ** X ** A = A /\ X ** A ** X = X /\
        symmetric_matrix(A ** X) /\ symmetric_matrix(X ** A)
        ==> matrix_inv A = X"
   (REWRITE_TAC [symmetric_matrix] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY (fun th => tactic_of do
        pure (ASSUME_TAC (← REWRITE_RULE [symmetric_matrix]
          (← ISPEC (← q r"A:real^M^N") th))))
     [MATRIX_INV_MUL_OUTER, SYMMETRIC_MATRIX_INV_RMUL, MATRIX_INV_MUL_INNER,
      SYMMETRIC_MATRIX_INV_LMUL] THEN
    ABBREV_TAC (← q r"Y = matrix_inv(A:real^M^N)") THEN
    POP_ASSUM (K ALL_TAC) THEN CONV_TAC SYM_CONV THEN
    SUBGOAL_THEN
     (← q r"(X:real^N^M) ** (A:real^M^N) ** X = Y ** A ** Y")
    MP_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
    TRANS_TAC EQ_TRANS (← q r"(X:real^N^M) ** (A:real^M^N) ** (Y:real^N^M)") THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN TRANS_TAC EQ_TRANS
       (← q r"transp(X:real^N^M) ** transp(A ** (Y:real^N^M) ** A)") THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC [← GSYM MATRIX_TRANSP_MUL], ALL_TAC] THEN
      REWRITE_TAC [MATRIX_MUL_ASSOC] THEN ONCE_REWRITE_TAC [MATRIX_TRANSP_MUL] THEN
      ASM_REWRITE_TAC [MATRIX_MUL_ASSOC, ← GSYM MATRIX_TRANSP_MUL] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC [← GSYM MATRIX_MUL_ASSOC],
      REWRITE_TAC [MATRIX_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      TRANS_TAC EQ_TRANS
       (← q r"transp(A ** (Y:real^N^M) ** A) ** transp(X:real^N^M)") THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC [← GSYM MATRIX_TRANSP_MUL], ALL_TAC] THEN
      ONCE_REWRITE_TAC [MATRIX_TRANSP_MUL] THEN
      REWRITE_TAC [← GSYM MATRIX_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC [← GSYM MATRIX_TRANSP_MUL] THEN
      ASM_REWRITE_TAC [← GSYM MATRIX_MUL_ASSOC]])

  let MATRIX_INV_TRANSP ← prove
   r"!A:real^M^N. matrix_inv (transp A) = transp(matrix_inv A)"
   (GEN_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN
    REWRITE_TAC [symmetric_matrix, ← GSYM MATRIX_TRANSP_MUL, TRANSP_TRANSP] THEN
    REWRITE_TAC [TRANSP_EQ, ← GSYM MATRIX_MUL_ASSOC] THEN
    REWRITE_TAC [MATRIX_INV_MUL_INNER, MATRIX_INV_MUL_OUTER,
                 ← REWRITE_RULE [symmetric_matrix] SYMMETRIC_MATRIX_INV_RMUL,
                 ← REWRITE_RULE [symmetric_matrix] SYMMETRIC_MATRIX_INV_LMUL])

  let TRANSP_MATRIX_INV ← prove
   r"!A:real^M^N. transp(matrix_inv A) = matrix_inv(transp A)"
   (REWRITE_TAC [MATRIX_INV_TRANSP])

  let SYMMETRIC_MATRIX_INV ← prove
   r"!A:real^N^N. symmetric_matrix(matrix_inv A) <=> symmetric_matrix A"
   (REWRITE_TAC [symmetric_matrix, TRANSP_MATRIX_INV, MATRIX_INV_EQ])

  return { matrix_inv, MOORE_PENROSE_PSEUDOINVERSE, MOORE_PENROSE_PSEUDOINVERSE_UNIQUE,
           MATRIX_INV_MUL_INNER, SYMMETRIC_MATRIX_INV_RMUL, MATRIX_INV_INV, MATRIX_INV_EQ,
           MATRIX_INV_MUL_OUTER, SYMMETRIC_MATRIX_INV_LMUL, MATRIX_INV_UNIQUE_STRONG,
           MATRIX_INV_TRANSP, TRANSP_MATRIX_INV, SYMMETRIC_MATRIX_INV }

/- ------------------------------------------------------------------------- -/
/- matrix_inv for invertible matrices; cancellation; rank; covariances.     -/
/- (vectors.ml 9075-9236)                                                     -/
/- ------------------------------------------------------------------------- -/

structure MatPinv2 where
  MATRIX_INV_0 : thm
  MATRIX_INV_EQ_0 : thm
  MATRIX_INV_CMUL : thm
  MATRIX_INV : thm
  MATRIX_INV_LEFT : thm
  MATRIX_INV_RIGHT : thm
  MATRIX_MUL_LCANCEL : thm
  MATRIX_MUL_RCANCEL : thm
  RANK_INVERTIBLE_RMUL : thm
  RANK_INVERTIBLE_LMUL : thm
  RANK_CMUL : thm
  RANK_NEG : thm
  MATRIX_INV_UNIQUE : thm
  MATRIX_INV_I : thm
  INVERTIBLE_MATRIX_INV : thm
  MATRIX_INV_UNIQUE_LEFT : thm
  MATRIX_INV_UNIQUE_RIGHT : thm
  MATRIX_INV_COVARIANCE : thm
  COVARIANCE_MATRIX_INV : thm
  NORMAL_MATRIX_INV : thm
  MATRIX_INV_COVARIANCE_RMUL : thm
  MATRIX_INV_COVARIANCE_LMUL : thm
  deriving Inhabited

@[nospecialize]
def setupMatPinv2 [HolBase] (D : VectorsDeps) (BMatrix : Matrix) (BMatArith : MatArith)
    (BMatProps : MatProps) (BInvertible : Invertible) (BLinEq : LinEq)
    (BMatInv2 : MatInv2) (BRank : Rank) (BMatPinv : MatPinv) :
    ExceptT String IO MatPinv2 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, REAL_RAT_REDUCE_CONV, .. } := D
  let { LE_ANTISYM, LE_REFL, LE_TRANS, .. } := D.core2
  let { REAL_INV_0, REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_RINV, .. } := D.core3
  let { REAL_MUL_RZERO, .. } := D.core4
  let { normal_matrix, symmetric_matrix, .. } := BMatrix
  let { MATRIX_CMUL_ASSOC, MATRIX_CMUL_LZERO, MATRIX_MUL_ASSOC, MATRIX_MUL_LID,
        MATRIX_MUL_LMUL, MATRIX_MUL_LZERO, MATRIX_MUL_RID, MATRIX_MUL_RMUL, MATRIX_MUL_RZERO,
        MATRIX_NEG_MINUS1, .. } := BMatArith
  let { MATRIX_TRANSP_MUL, SYMMETRIC_MATRIX_MAT, TRANSP_MATRIX_CMUL, TRANSP_TRANSP,
        .. } := BMatProps
  let { INVERTIBLE_CMUL, INVERTIBLE_I, invertible, .. } := BInvertible
  let { INVERTIBLE_TRANSP, .. } := BLinEq
  let { INVERTIBLE_LEFT_INVERSE, INVERTIBLE_RIGHT_INVERSE, MATRIX_LEFT_RIGHT_INVERSE,
        .. } := BMatInv2
  let { RANK_0, RANK_MUL_LE_LEFT, RANK_TRANSP, .. } := BRank
  let { MATRIX_INV_EQ, MATRIX_INV_INV, MATRIX_INV_MUL_INNER, MATRIX_INV_MUL_OUTER,
        MATRIX_INV_UNIQUE_STRONG, SYMMETRIC_MATRIX_INV_LMUL, SYMMETRIC_MATRIX_INV_RMUL,
        .. } := BMatPinv
  -- @@SCOPE END

  let MATRIX_INV_0 ← prove
   r"matrix_inv(mat 0:real^M^N) = mat 0"
   (MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN
    REWRITE_TAC [MATRIX_MUL_LZERO, MATRIX_MUL_RZERO, SYMMETRIC_MATRIX_MAT])

  let MATRIX_INV_EQ_0 ← prove
   r"!A:real^M^N. matrix_inv A = mat 0 <=> A = mat 0"
   (MESON_TAC [MATRIX_INV_0, MATRIX_INV_INV])

  let MATRIX_INV_CMUL ← prove
   r"!c A:real^M^N. matrix_inv (c %% A) = inv(c) %% matrix_inv A"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN
    REWRITE_TAC [symmetric_matrix] THEN
    REWRITE_TAC [MATRIX_MUL_LMUL, MATRIX_MUL_RMUL, TRANSP_MATRIX_CMUL] THEN
    REWRITE_TAC [MATRIX_CMUL_ASSOC, MATRIX_INV_MUL_INNER, MATRIX_INV_MUL_OUTER,
                 ← REWRITE_RULE [symmetric_matrix] SYMMETRIC_MATRIX_INV_RMUL,
                 ← REWRITE_RULE [symmetric_matrix] SYMMETRIC_MATRIX_INV_LMUL] THEN
    ASM_CASES_TAC (← q r"c = &0") THEN
    ASM_REWRITE_TAC [REAL_INV_0, MATRIX_CMUL_LZERO, REAL_MUL_RZERO] THEN
    ASM_SIMP_TAC [REAL_MUL_LINV, REAL_MUL_RINV, REAL_MUL_LID])

  let MATRIX_INV ← prove
   r"!A:real^N^M.
    invertible A ==> A ** matrix_inv A = mat 1 /\ matrix_inv A ** A = mat 1"
   (GEN_TAC THEN REWRITE_TAC [invertible] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"B:real^M^N") STRIP_ASSUME_TAC) THEN
    MP_TAC (← AP_TERM (← q r"\A:real^N^M. (B:real^M^N) ** A")
     (← ISPEC (← q r"A:real^N^M") MATRIX_INV_MUL_INNER)) THEN
    MP_TAC (← AP_TERM (← q r"\A:real^N^M. A ** (B:real^M^N)")
         (← ISPEC (← q r"A:real^N^M") MATRIX_INV_MUL_INNER)) THEN
    ASM_REWRITE_TAC [MATRIX_MUL_ASSOC, MATRIX_MUL_LID] THEN
    ASM_REWRITE_TAC [← GSYM MATRIX_MUL_ASSOC, MATRIX_MUL_RID] THEN
    SIMP_TAC [MATRIX_MUL_LID])

  let MATRIX_INV_LEFT ← prove
   r"!A:real^N^N. matrix_inv A ** A = mat 1 <=> invertible A"
   (MESON_TAC [INVERTIBLE_LEFT_INVERSE, MATRIX_INV])

  let MATRIX_INV_RIGHT ← prove
   r"!A:real^N^N. A ** matrix_inv A = mat 1 <=> invertible A"
   (MESON_TAC [INVERTIBLE_RIGHT_INVERSE, MATRIX_INV])

  let MATRIX_MUL_LCANCEL ← prove
   r"!A:real^M^N B:real^P^M C.
        invertible A ==> (A ** B = A ** C <=> B = C)"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
    EQ_TAC THEN SIMP_TAC [] THEN
    DISCH_THEN (MP_TAC o AP_TERM
     (← q r"matrix_mul (matrix_inv(A:real^M^N)):real^P^N->real^P^M")) THEN
    ASM_SIMP_TAC [MATRIX_MUL_ASSOC, MATRIX_MUL_LID])

  let MATRIX_MUL_RCANCEL ← prove
   r"!A B:real^M^N C:real^P^M.
        invertible C ==> (A ** C = B ** C <=> A = B)"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
    EQ_TAC THEN SIMP_TAC [] THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"\A:real^P^N. A ** matrix_inv(C:real^P^M)")) THEN
    ASM_SIMP_TAC [← GSYM MATRIX_MUL_ASSOC, MATRIX_MUL_RID])

  let RANK_INVERTIBLE_RMUL ← prove
   r"!A:real^M^N B:real^P^M. invertible B ==> rank(A ** B) = rank A"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM LE_ANTISYM, RANK_MUL_LE_LEFT] THEN
    TRANS_TAC LE_TRANS
      (← q r"rank(((A:real^M^N) ** (B:real^P^M)) ** matrix_inv B)") THEN
    REWRITE_TAC [RANK_MUL_LE_LEFT] THEN
    ASM_SIMP_TAC [← GSYM MATRIX_MUL_ASSOC, MATRIX_INV] THEN
    REWRITE_TAC [LE_REFL, MATRIX_MUL_RID])

  let RANK_INVERTIBLE_LMUL ← prove
   r"!A:real^M^N B:real^P^M. invertible A ==> rank(A ** B) = rank B"
   (ONCE_REWRITE_TAC [← GSYM RANK_TRANSP] THEN
    SIMP_TAC [MATRIX_TRANSP_MUL, RANK_INVERTIBLE_RMUL, INVERTIBLE_TRANSP])

  let RANK_CMUL ← prove
   r"!A:real^N^M c. rank(c %% A) = if c = &0 then 0 else rank A"
   (REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [MATRIX_CMUL_LZERO, RANK_0] THEN
    GEN_REWRITE_TAC
     (LAND_CONV o RAND_CONV o RAND_CONV) [← GSYM MATRIX_MUL_LID] THEN
    REWRITE_TAC [← GSYM MATRIX_MUL_LMUL] THEN
    MATCH_MP_TAC RANK_INVERTIBLE_LMUL THEN
    ASM_REWRITE_TAC [INVERTIBLE_CMUL, INVERTIBLE_I])

  let RANK_NEG ← prove
   r"!A:real^N^M. rank(--A) = rank A"
   (REWRITE_TAC [MATRIX_NEG_MINUS1, RANK_CMUL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV)

  let MATRIX_INV_UNIQUE ← prove
   r"!A:real^N^M B. A ** B = mat 1 /\ B ** A = mat 1 ==> matrix_inv A = B"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN
    ASM_REWRITE_TAC [SYMMETRIC_MATRIX_MAT, MATRIX_MUL_RID])

  let MATRIX_INV_I ← prove
   r"matrix_inv(mat 1:real^N^N) = mat 1"
   (MATCH_MP_TAC MATRIX_INV_UNIQUE THEN
    REWRITE_TAC [MATRIX_MUL_LID])

  let INVERTIBLE_MATRIX_INV ← prove
   r"!A:real^M^N. invertible(matrix_inv A) <=> invertible A"
   (MESON_TAC [MATRIX_INV_INV, MATRIX_INV, invertible])

  let MATRIX_INV_UNIQUE_LEFT ← prove
   r"!A:real^N^N B. A ** B = mat 1 ==> matrix_inv B = A"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE THEN
    ASM_MESON_TAC [MATRIX_LEFT_RIGHT_INVERSE])

  let MATRIX_INV_UNIQUE_RIGHT ← prove
   r"!A:real^N^N B. A ** B = mat 1 ==> matrix_inv A = B"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE THEN
    ASM_MESON_TAC [MATRIX_LEFT_RIGHT_INVERSE])

  let MATRIX_INV_COVARIANCE ← prove
   r"!A:real^M^N.
     matrix_inv(transp A ** A) = matrix_inv(A) ** transp(matrix_inv A)"
   (GEN_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN
    REWRITE_TAC [symmetric_matrix, MATRIX_TRANSP_MUL, TRANSP_TRANSP] THEN
    REWRITE_TAC [← GSYM MATRIX_MUL_ASSOC, ← MESON [MATRIX_MUL_ASSOC, MATRIX_TRANSP_MUL] (← q
     r"(A:real^M^N) ** transp B ** transp C ** (D:real^P^Q) =
    A ** transp(C ** B) ** D")] THEN
    REWRITE_TAC [← REWRITE_RULE [symmetric_matrix] SYMMETRIC_MATRIX_INV_LMUL,
                 ← REWRITE_RULE [symmetric_matrix] SYMMETRIC_MATRIX_INV_RMUL] THEN
    REWRITE_TAC [← GSYM MATRIX_MUL_ASSOC, MATRIX_INV_MUL_INNER] THEN
    REWRITE_TAC [← EQT_ELIM (← REWRITE_CONV [MATRIX_MUL_ASSOC] (← q
     r"(A:real^M^N) ** B ** C ** (D:real^P^Q) = (A ** B ** C) ** D"))] THEN
    REWRITE_TAC [MATRIX_INV_MUL_OUTER] THEN
    MATCH_MP_TAC (← MESON [] (← q r"y = x ==> x = y /\ y = x")) THEN
    ONCE_REWRITE_TAC [← GSYM (← REWRITE_RULE [symmetric_matrix]
          SYMMETRIC_MATRIX_INV_RMUL)] THEN
    REWRITE_TAC [← GSYM MATRIX_TRANSP_MUL] THEN
    REWRITE_TAC [← GSYM MATRIX_MUL_ASSOC, MATRIX_INV_MUL_INNER] THEN
    REWRITE_TAC [← REWRITE_RULE [symmetric_matrix] SYMMETRIC_MATRIX_INV_LMUL])

  let COVARIANCE_MATRIX_INV ← prove
   r"!A:real^M^N.
        transp(matrix_inv A) ** matrix_inv A = matrix_inv(A ** transp A)"
   (ONCE_REWRITE_TAC [← GSYM MATRIX_INV_EQ] THEN
    REWRITE_TAC [MATRIX_INV_INV, MATRIX_INV_COVARIANCE])

  let NORMAL_MATRIX_INV ← prove
   r"!A:real^N^N. normal_matrix(matrix_inv A) <=> normal_matrix A"
   (REWRITE_TAC [normal_matrix] THEN
    REWRITE_TAC [← GSYM MATRIX_INV_COVARIANCE, COVARIANCE_MATRIX_INV] THEN
    REWRITE_TAC [MATRIX_INV_EQ] THEN MESON_TAC [])

  let MATRIX_INV_COVARIANCE_RMUL ← prove
   r"!A:real^M^N. matrix_inv(transp A ** A) ** transp A = matrix_inv A"
   (REWRITE_TAC [MATRIX_INV_COVARIANCE] THEN
    REWRITE_TAC [← GSYM MATRIX_MUL_ASSOC, ← GSYM MATRIX_TRANSP_MUL] THEN
    REWRITE_TAC [← REWRITE_RULE [symmetric_matrix] SYMMETRIC_MATRIX_INV_RMUL,
                 MATRIX_INV_MUL_OUTER])

  let MATRIX_INV_COVARIANCE_LMUL ← prove
   r"!A:real^M^N. transp(A) ** matrix_inv(A ** transp A) = matrix_inv A"
   (REWRITE_TAC [← GSYM COVARIANCE_MATRIX_INV] THEN
    REWRITE_TAC [← GSYM MATRIX_TRANSP_MUL, MATRIX_MUL_ASSOC] THEN
    REWRITE_TAC [← REWRITE_RULE [symmetric_matrix] SYMMETRIC_MATRIX_INV_LMUL,
                 ← GSYM MATRIX_MUL_ASSOC] THEN
    REWRITE_TAC [MATRIX_INV_MUL_OUTER])

  return { MATRIX_INV_0, MATRIX_INV_EQ_0, MATRIX_INV_CMUL, MATRIX_INV, MATRIX_INV_LEFT,
           MATRIX_INV_RIGHT, MATRIX_MUL_LCANCEL, MATRIX_MUL_RCANCEL, RANK_INVERTIBLE_RMUL,
           RANK_INVERTIBLE_LMUL, RANK_CMUL, RANK_NEG, MATRIX_INV_UNIQUE, MATRIX_INV_I,
           INVERTIBLE_MATRIX_INV, MATRIX_INV_UNIQUE_LEFT, MATRIX_INV_UNIQUE_RIGHT,
           MATRIX_INV_COVARIANCE, COVARIANCE_MATRIX_INV, NORMAL_MATRIX_INV,
           MATRIX_INV_COVARIANCE_RMUL, MATRIX_INV_COVARIANCE_LMUL }

/- ------------------------------------------------------------------------- -/
/- More properties of matrix_inv: rank, kernels and images, idempotents.     -/
/- (vectors.ml 9238-9396)                                                     -/
/- ------------------------------------------------------------------------- -/

structure MatPinv3 where
  RANK_SIMILAR : thm
  RANK_MATRIX_INV : thm
  RANK_MATRIX_INV_RMUL : thm
  RANK_MATRIX_INV_LMUL : thm
  MATRIX_INV_MULTIPLE_TRANP_RIGHT : thm
  MATRIX_TRANSP_MULTIPLE_INV_RIGHT : thm
  MATRIX_INV_MULTIPLE_TRANP_LEFT : thm
  MATRIX_TRANSP_MULTIPLE_INV_LEFT : thm
  MATRIX_VECTOR_MUL_INV_EQ_0 : thm
  KERNEL_MATRIX_INV : thm
  IMAGE_MATRIX_INV : thm
  COMMUTING_MATRIX_INV_COVARIANCE : thm
  COMMUTING_MATRIX_INV_NORMAL : thm
  MATRIX_MUL_INV_EQ_0 : thm
  MATRIX_INV_IDEMPOTENT : thm
  IDEMPOTENT_MATRIX_MUL_LINV : thm
  IDEMPOTENT_MATRIX_MUL_RINV : thm
  MATRIX_INV_MUL_LINV : thm
  MATRIX_INV_MUL_RINV : thm
  deriving Inhabited

@[nospecialize]
def setupMatPinv3 [HolBase] (D : VectorsDeps) (BMatrix : Matrix) (BMatArith : MatArith)
    (BMatProps : MatProps) (BRank : Rank) (BMatPinv : MatPinv) (BMatPinv2 : MatPinv2) :
    ExceptT String IO MatPinv3 := do
  -- @@SCOPE BEGIN
  let { MESON, MESON_TAC, .. } := D
  let { FORALL_IN_IMAGE, .. } := D.core1
  let { IN_IMAGE, IN_UNIV, LE_ANTISYM, LE_TRANS, .. } := D.core2
  let { SUBSET, SUBSET_ANTISYM_EQ, .. } := D.core4
  let { normal_matrix, symmetric_matrix, .. } := BMatrix
  let { MATRIX_MUL_ASSOC, MATRIX_MUL_LZERO, MATRIX_MUL_RZERO, MATRIX_VECTOR_MUL_ASSOC,
        MATRIX_VECTOR_MUL_RZERO, .. } := BMatArith
  let { MATRIX_TRANSP_MUL, TRANSP_MAT, TRANSP_TRANSP, .. } := BMatProps
  let { RANK_MUL_LE_LEFT, RANK_MUL_LE_RIGHT, RANK_TRANSP, .. } := BRank
  let { MATRIX_INV_INV, MATRIX_INV_MUL_INNER, MATRIX_INV_MUL_OUTER, MATRIX_INV_UNIQUE_STRONG,
        SYMMETRIC_MATRIX_INV_LMUL, SYMMETRIC_MATRIX_INV_RMUL, TRANSP_MATRIX_INV,
        .. } := BMatPinv
  let { INVERTIBLE_MATRIX_INV, MATRIX_INV_COVARIANCE_LMUL, MATRIX_INV_COVARIANCE_RMUL,
        RANK_INVERTIBLE_LMUL, RANK_INVERTIBLE_RMUL, .. } := BMatPinv2
  -- @@SCOPE END

  let RANK_SIMILAR ← prove
   r"!A:real^N^N U:real^M^N.
        invertible U ==> rank(matrix_inv U ** A ** U) = rank A"
   (SIMP_TAC [RANK_INVERTIBLE_RMUL, RANK_INVERTIBLE_LMUL,
              INVERTIBLE_MATRIX_INV])

  let RANK_MATRIX_INV ← prove
   r"!A:real^M^N. rank(matrix_inv A) = rank A"
   (GEN_TAC THEN REWRITE_TAC [← GSYM LE_ANTISYM] THEN CONJ_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM MATRIX_INV_MUL_INNER] THEN
    REWRITE_TAC [MATRIX_INV_INV] THEN MATCH_MP_TAC (← MESON [LE_TRANS] (← q
     r"rank(A ** B ** C) <= rank(B ** C) /\ rank(B ** C) <= rank B
    ==> rank(A ** B ** C) <= rank B")) THEN
    REWRITE_TAC [RANK_MUL_LE_RIGHT, RANK_MUL_LE_LEFT])

  let RANK_MATRIX_INV_RMUL ← prove
   r"!A:real^M^N. rank(A ** matrix_inv A) = rank A"
   (GEN_TAC THEN REWRITE_TAC [← GSYM LE_ANTISYM] THEN
    REWRITE_TAC [RANK_MUL_LE_LEFT] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM RANK_MATRIX_INV] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM MATRIX_INV_MUL_OUTER] THEN
    REWRITE_TAC [RANK_MUL_LE_RIGHT])

  let RANK_MATRIX_INV_LMUL ← prove
   r"!A:real^M^N. rank(matrix_inv A ** A) = rank A"
   (GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM RANK_TRANSP] THEN
    REWRITE_TAC [MATRIX_TRANSP_MUL, TRANSP_MATRIX_INV, RANK_MATRIX_INV_RMUL])

  let MATRIX_INV_MULTIPLE_TRANP_RIGHT ← prove
   r"!A:real^M^N.
       matrix_inv A = matrix_inv A ** transp(matrix_inv A) ** transp A"
   (REWRITE_TAC [← GSYM MATRIX_TRANSP_MUL,
                 ← REWRITE_RULE [symmetric_matrix] SYMMETRIC_MATRIX_INV_RMUL] THEN
    REWRITE_TAC [MATRIX_INV_MUL_OUTER])

  let MATRIX_TRANSP_MULTIPLE_INV_RIGHT ← prove
   r"!A:real^M^N. transp A = transp A ** A ** matrix_inv A"
   (GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM MATRIX_INV_MUL_INNER] THEN
    REWRITE_TAC [MATRIX_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC [MATRIX_TRANSP_MUL] THEN
    REWRITE_TAC [← REWRITE_RULE [symmetric_matrix] SYMMETRIC_MATRIX_INV_RMUL] THEN
    REWRITE_TAC [MATRIX_MUL_ASSOC])

  let MATRIX_INV_MULTIPLE_TRANP_LEFT ← prove
   r"!A:real^M^N.
       matrix_inv A = transp A ** transp(matrix_inv A) ** matrix_inv A"
   (GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM MATRIX_INV_MUL_OUTER] THEN
    REWRITE_TAC [MATRIX_MUL_ASSOC, ← GSYM MATRIX_TRANSP_MUL] THEN
    REWRITE_TAC [← REWRITE_RULE [symmetric_matrix] SYMMETRIC_MATRIX_INV_LMUL])

  let MATRIX_TRANSP_MULTIPLE_INV_LEFT ← prove
   r"!A:real^M^N. transp A = matrix_inv A ** A ** transp A"
   (GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM MATRIX_INV_MUL_INNER] THEN
    ONCE_REWRITE_TAC [MATRIX_TRANSP_MUL] THEN
    REWRITE_TAC [← REWRITE_RULE [symmetric_matrix] SYMMETRIC_MATRIX_INV_LMUL] THEN
    REWRITE_TAC [MATRIX_MUL_ASSOC])

  let MATRIX_VECTOR_MUL_INV_EQ_0 ← prove
   r"!A:real^M^N. matrix_inv A ** x = vec 0 <=> transp A ** x = vec 0"
   (GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [ONCE_REWRITE_TAC [MATRIX_TRANSP_MULTIPLE_INV_RIGHT],
      ONCE_REWRITE_TAC [MATRIX_INV_MULTIPLE_TRANP_RIGHT]] THEN
    ASM_REWRITE_TAC [← GSYM MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_RZERO])

  let KERNEL_MATRIX_INV ← prove
   r"!A:real^M^N.
        {x | matrix_inv A ** x = vec 0} = {x | transp A ** x = vec 0}"
   (REWRITE_TAC [MATRIX_VECTOR_MUL_INV_EQ_0])

  let IMAGE_MATRIX_INV ← prove
   r"!A:real^M^N.
        IMAGE (\x:real^N. matrix_inv A ** x) UNIV =
        IMAGE (\x. transp A ** x) UNIV"
   (GEN_TAC THEN REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THENL
     [ONCE_REWRITE_TAC [MATRIX_INV_MULTIPLE_TRANP_LEFT],
      ONCE_REWRITE_TAC [MATRIX_TRANSP_MULTIPLE_INV_LEFT]] THEN
    REWRITE_TAC [IN_UNIV, IN_IMAGE, ← GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    MESON_TAC [])

  let COMMUTING_MATRIX_INV_COVARIANCE ← prove
   r"!A:real^M^N.
        matrix_inv(transp A ** A) ** (transp A ** A) =
        (transp A ** A) ** matrix_inv(transp A ** A)"
   (GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV
     [← GSYM (← REWRITE_RULE [symmetric_matrix] SYMMETRIC_MATRIX_INV_RMUL)] THEN
    REWRITE_TAC [MATRIX_TRANSP_MUL, TRANSP_MATRIX_INV, TRANSP_TRANSP])

  let COMMUTING_MATRIX_INV_NORMAL ← prove
   r"!A:real^N^N.
      normal_matrix A ==> matrix_inv A ** A = A ** matrix_inv A"
   (REWRITE_TAC [normal_matrix] THEN REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [← GSYM MATRIX_INV_COVARIANCE_RMUL] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
     [← GSYM MATRIX_INV_COVARIANCE_LMUL] THEN
    REWRITE_TAC [← GSYM MATRIX_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC [COMMUTING_MATRIX_INV_COVARIANCE] THEN
    ASM_REWRITE_TAC [MATRIX_MUL_ASSOC])

  let MATRIX_MUL_INV_EQ_0 ← do
    let lemma ← prove
     r"!A:real^P^N B:real^N^M.
        B ** A = mat 0 ==> matrix_inv A ** matrix_inv B = mat 0"
     (REPEAT STRIP_TAC THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
       [MATRIX_INV_MULTIPLE_TRANP_RIGHT] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
       [MATRIX_INV_MULTIPLE_TRANP_LEFT] THEN
      ONCE_REWRITE_TAC [MATRIX_MUL_ASSOC] THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o TOP_DEPTH_CONV)
       [← GSYM MATRIX_MUL_ASSOC] THEN
      ASM_REWRITE_TAC [← GSYM MATRIX_TRANSP_MUL] THEN
      REWRITE_TAC [MATRIX_MUL_LZERO, MATRIX_MUL_RZERO, TRANSP_MAT])
    prove
     r"!A:real^P^N B:real^N^M.
        matrix_inv A ** matrix_inv B = mat 0 <=> B ** A = mat 0"
     (REPEAT GEN_TAC THEN EQ_TAC THEN
      DISCH_THEN (MP_TAC o MATCH_MP lemma) THEN
      REWRITE_TAC [MATRIX_INV_INV])

  let MATRIX_INV_IDEMPOTENT ← prove
   r"!A:real^N^N. symmetric_matrix A /\ A ** A = A ==> matrix_inv A = A"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN
    ASM_REWRITE_TAC [MATRIX_TRANSP_MUL])

  let IDEMPOTENT_MATRIX_MUL_LINV ← prove
   r"!A:real^N^M.
        (matrix_inv A ** A) ** (matrix_inv A ** A) = matrix_inv A ** A"
   (GEN_TAC THEN REWRITE_TAC [MATRIX_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [← GSYM MATRIX_MUL_ASSOC, MATRIX_INV_MUL_OUTER])

  let IDEMPOTENT_MATRIX_MUL_RINV ← prove
   r"!A:real^N^M.
        (A ** matrix_inv A) ** (A ** matrix_inv A) = A ** matrix_inv A"
   (GEN_TAC THEN REWRITE_TAC [MATRIX_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [← GSYM MATRIX_MUL_ASSOC, MATRIX_INV_MUL_INNER])

  let MATRIX_INV_MUL_LINV ← prove
   r"!A:real^N^M. matrix_inv(matrix_inv A ** A) = matrix_inv A ** A"
   (GEN_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN
    REWRITE_TAC [symmetric_matrix] THEN
    REWRITE_TAC [← GSYM MATRIX_MUL_ASSOC, MATRIX_TRANSP_MUL, TRANSP_MATRIX_INV] THEN
    REWRITE_TAC [MATRIX_INV_MUL_INNER, MATRIX_INV_MUL_OUTER] THEN
    REWRITE_TAC [← GSYM TRANSP_MATRIX_INV, ← GSYM MATRIX_TRANSP_MUL] THEN
    REWRITE_TAC [← REWRITE_RULE [symmetric_matrix] SYMMETRIC_MATRIX_INV_LMUL])

  let MATRIX_INV_MUL_RINV ← prove
   r"!A:real^N^M. matrix_inv(A ** matrix_inv A) = A ** matrix_inv A"
   (GEN_TAC THEN MATCH_MP_TAC MATRIX_INV_UNIQUE_STRONG THEN
    REWRITE_TAC [symmetric_matrix] THEN
    REWRITE_TAC [← GSYM MATRIX_MUL_ASSOC, MATRIX_TRANSP_MUL, TRANSP_MATRIX_INV] THEN
    REWRITE_TAC [MATRIX_INV_MUL_INNER, MATRIX_INV_MUL_OUTER] THEN
    REWRITE_TAC [← GSYM TRANSP_MATRIX_INV, ← GSYM MATRIX_TRANSP_MUL] THEN
    REWRITE_TAC [← REWRITE_RULE [symmetric_matrix] SYMMETRIC_MATRIX_INV_RMUL])

  return { RANK_SIMILAR, RANK_MATRIX_INV, RANK_MATRIX_INV_RMUL, RANK_MATRIX_INV_LMUL,
           MATRIX_INV_MULTIPLE_TRANP_RIGHT, MATRIX_TRANSP_MULTIPLE_INV_RIGHT,
           MATRIX_INV_MULTIPLE_TRANP_LEFT, MATRIX_TRANSP_MULTIPLE_INV_LEFT,
           MATRIX_VECTOR_MUL_INV_EQ_0, KERNEL_MATRIX_INV, IMAGE_MATRIX_INV,
           COMMUTING_MATRIX_INV_COVARIANCE, COMMUTING_MATRIX_INV_NORMAL, MATRIX_MUL_INV_EQ_0,
           MATRIX_INV_IDEMPOTENT, IDEMPOTENT_MATRIX_MUL_LINV, IDEMPOTENT_MATRIX_MUL_RINV,
           MATRIX_INV_MUL_LINV, MATRIX_INV_MUL_RINV }

/- ------------------------------------------------------------------------- -/
/- Infinity norm; its bounds against the Euclidean norm; equality in        -/
/- Cauchy-Schwarz and triangle inequalities.  (vectors.ml 9402-9590)         -/
/- ------------------------------------------------------------------------- -/

structure Infnorm where
  infnorm : thm
  NUMSEG_DIMINDEX_NONEMPTY : thm
  INFNORM_SET_IMAGE : thm
  INFNORM_SET_LEMMA : thm
  INFNORM_POS_LE : thm
  INFNORM_TRIANGLE : thm
  INFNORM_EQ_0 : thm
  INFNORM_0 : thm
  INFNORM_NEG : thm
  INFNORM_SUB : thm
  REAL_ABS_SUB_INFNORM : thm
  REAL_ABS_INFNORM : thm
  COMPONENT_LE_INFNORM : thm
  INFNORM_MUL_LEMMA : thm
  INFNORM_MUL : thm
  INFNORM_POS_LT : thm
  INFNORM_LE_NORM : thm
  NORM_LE_INFNORM : thm
  NORM_CAUCHY_SCHWARZ_EQ : thm
  NORM_CAUCHY_SCHWARZ_ABS_EQ : thm
  NORM_TRIANGLE_EQ : thm
  DIST_TRIANGLE_EQ : thm
  NORM_CROSS_MULTIPLY : thm
  deriving Inhabited

@[nospecialize]
def setupInfnorm [HolBase] (D : VectorsDeps) (BBasics : Basics)
    (BVectorArith : VectorArith) (BDotProps : DotProps) (BNorm1 : Norm1)
    (BNormArith : NormArithB) : ExceptT String IO Infnorm := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_RING, SET_TAC, define,
        .. } := D
  let { ARITH, CARD_NUMSEG_1, CART_EQ, DIMINDEX_GE_1, EQ_SYM_EQ, EQ_TRANS, EXISTS_IN_IMAGE,
        EXTENSION, FINITE_IMAGE, FINITE_NUMSEG, FORALL_IN_IMAGE, .. } := D.core1
  let { IMAGE_EQ_EMPTY, IN_ELIM_THM, IN_NUMSEG, MEMBER_NOT_EMPTY, NOT_LT, NUMSEG_EMPTY,
        .. } := D.core2
  let { REAL_ABS_0, REAL_ABS_INV, REAL_ABS_MUL, REAL_ABS_NEG, REAL_ABS_POS, REAL_ENTIRE,
        REAL_LE_ANTISYM, REAL_LE_LMUL, REAL_LE_LSQRT, REAL_LE_MUL, REAL_LE_REFL,
        REAL_LE_SUB_RADD, REAL_LE_SUP_FINITE, REAL_LE_TRANS, REAL_LT_IMP_LE, REAL_LT_IMP_NZ,
        REAL_LT_LE, REAL_MUL_AC, REAL_MUL_ASSOC, REAL_MUL_LINV, REAL_MUL_LZERO,
        REAL_MUL_RINV, .. } := D.core3
  let { REAL_MUL_RZERO, REAL_OF_NUM_EQ, REAL_POS, REAL_POW2_ABS, REAL_POW_2, REAL_POW_LE2,
        REAL_POW_MUL, REAL_SUB_0, REAL_SUP_LE_FINITE, SQRT_POS_LE, SQRT_POW_2, SUM_BOUND,
        .. } := D.core4
  let { SUP_FINITE, numseg, real_abs, .. } := D.core5
  let { dot, .. } := BBasics
  let { VECTOR_ADD_COMPONENT, VECTOR_ADD_SYM, VECTOR_ARITH_TAC, VECTOR_MUL_ASSOC,
        VECTOR_MUL_COMPONENT, VECTOR_MUL_LID, VECTOR_MUL_LZERO, VECTOR_MUL_RZERO,
        VECTOR_NEG_COMPONENT, VECTOR_NEG_SUB, VECTOR_SUB_ADD2, VECTOR_SUB_EQ, VEC_COMPONENT,
        .. } := BVectorArith
  let { DOT_EQ_0, DOT_LADD, DOT_LMUL, DOT_LSUB, DOT_LZERO, DOT_POS_LE, DOT_RADD, DOT_RMUL,
        DOT_RNEG, DOT_RSUB, DOT_RZERO, DOT_SYM, .. } := BDotProps
  let { COMPONENT_LE_NORM, NORM_0, NORM_EQ_0, NORM_MUL, NORM_NEG, NORM_POS_LE, NORM_POW_2,
        VECTOR_MUL_EQ_0, vector_norm, .. } := BNorm1
  let { NORM_ARITH_TAC, .. } := BNormArith
  -- @@SCOPE END

  let infnorm ← define
   r"infnorm (x:real^N) = sup { abs(x$i) | 1 <= i /\ i <= dimindex(:N) }"

  let NUMSEG_DIMINDEX_NONEMPTY ← prove
   r"?i. i IN 1..dimindex(:N)"
   (REWRITE_TAC [MEMBER_NOT_EMPTY, NUMSEG_EMPTY, NOT_LT, DIMINDEX_GE_1])

  let INFNORM_SET_IMAGE ← prove
   r"{abs(x$i) | 1 <= i /\ i <= dimindex(:N)} =
   IMAGE (\i. abs(x$i)) (1..dimindex(:N))"
   (REWRITE_TAC [numseg] THEN SET_TAC [])

  let INFNORM_SET_LEMMA ← prove
   r"FINITE {abs((x:real^N)$i) | 1 <= i /\ i <= dimindex(:N)} /\
   ~({abs(x$i) | 1 <= i /\ i <= dimindex(:N)} = {})"
   (SIMP_TAC [INFNORM_SET_IMAGE, FINITE_NUMSEG, FINITE_IMAGE, IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC [NUMSEG_EMPTY, NOT_LT, DIMINDEX_GE_1])

  let INFNORM_POS_LE ← prove
   r"!x. &0 <= infnorm x"
   (REWRITE_TAC [infnorm] THEN
    SIMP_TAC [REAL_LE_SUP_FINITE, INFNORM_SET_LEMMA] THEN
    REWRITE_TAC [INFNORM_SET_IMAGE, NUMSEG_DIMINDEX_NONEMPTY,
                 EXISTS_IN_IMAGE, REAL_ABS_POS])

  let INFNORM_TRIANGLE ← prove
   r"!x y. infnorm(x + y) <= infnorm x + infnorm y"
   (REWRITE_TAC [infnorm] THEN
    SIMP_TAC [REAL_SUP_LE_FINITE, INFNORM_SET_LEMMA] THEN
    ONCE_REWRITE_TAC [← GSYM REAL_LE_SUB_RADD] THEN
    SIMP_TAC [REAL_LE_SUP_FINITE, INFNORM_SET_LEMMA] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"x - y <= z <=> x - z <= y")] THEN
    SIMP_TAC [REAL_LE_SUP_FINITE, INFNORM_SET_LEMMA] THEN
    REWRITE_TAC [INFNORM_SET_IMAGE, FORALL_IN_IMAGE, EXISTS_IN_IMAGE] THEN
    SIMP_TAC [VECTOR_ADD_COMPONENT, ← GSYM IN_NUMSEG] THEN
    MESON_TAC [NUMSEG_DIMINDEX_NONEMPTY,
               ← REAL_ARITH (← q r"abs(x + y) - abs(x) <= abs(y)")])

  let INFNORM_EQ_0 ← prove
   r"!x. infnorm x = &0 <=> x = vec 0"
   (REWRITE_TAC [← GSYM REAL_LE_ANTISYM, INFNORM_POS_LE] THEN
    SIMP_TAC [infnorm, REAL_SUP_LE_FINITE, INFNORM_SET_LEMMA] THEN
    SIMP_TAC [FORALL_IN_IMAGE, INFNORM_SET_IMAGE, CART_EQ, VEC_COMPONENT] THEN
    REWRITE_TAC [IN_NUMSEG, ← REAL_ARITH (← q r"abs(x) <= &0 <=> x = &0")])

  let INFNORM_0 ← prove
   r"infnorm(vec 0) = &0"
   (REWRITE_TAC [INFNORM_EQ_0])

  let INFNORM_NEG ← prove
   r"!x. infnorm(--x) = infnorm x"
   (GEN_TAC THEN REWRITE_TAC [infnorm] THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
    MESON_TAC [REAL_ABS_NEG, VECTOR_NEG_COMPONENT])

  let INFNORM_SUB ← prove
   r"!x y. infnorm(x - y) = infnorm(y - x)"
   (MESON_TAC [INFNORM_NEG, VECTOR_NEG_SUB])

  let REAL_ABS_SUB_INFNORM ← prove
   r"abs(infnorm x - infnorm y) <= infnorm(x - y)"
   (MATCH_MP_TAC (← REAL_ARITH (← q
      r"nx <= n + ny /\ ny <= n + nx ==> abs(nx - ny) <= n")) THEN
    MESON_TAC [INFNORM_SUB, VECTOR_SUB_ADD2, INFNORM_TRIANGLE, VECTOR_ADD_SYM])

  let REAL_ABS_INFNORM ← prove
   r"!x. abs(infnorm x) = infnorm x"
   (REWRITE_TAC [real_abs, INFNORM_POS_LE])

  let COMPONENT_LE_INFNORM ← prove
   r"!x:real^N i. 1 <= i /\ i <= dimindex (:N) ==> abs(x$i) <= infnorm x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [infnorm] THEN
    MP_TAC (← SPEC (← q r"{ abs((x:real^N)$i) | 1 <= i /\ i <= dimindex(:N) }")
                SUP_FINITE) THEN
    REWRITE_TAC [INFNORM_SET_LEMMA] THEN
    SIMP_TAC [INFNORM_SET_IMAGE, FORALL_IN_IMAGE, IN_NUMSEG])

  let INFNORM_MUL_LEMMA ← prove
   r"!a x. infnorm(a % x) <= abs a * infnorm x"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [infnorm] THEN
    SIMP_TAC [REAL_SUP_LE_FINITE, INFNORM_SET_LEMMA] THEN
    REWRITE_TAC [FORALL_IN_IMAGE, INFNORM_SET_IMAGE] THEN
    SIMP_TAC [REAL_ABS_MUL, VECTOR_MUL_COMPONENT, IN_NUMSEG] THEN
    SIMP_TAC [COMPONENT_LE_INFNORM, REAL_LE_LMUL, REAL_ABS_POS])

  let INFNORM_MUL ← prove
   r"!a x:real^N. infnorm(a % x) = abs a * infnorm x"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"a = &0") THEN
    ASM_REWRITE_TAC [VECTOR_MUL_LZERO, INFNORM_0, REAL_ABS_0, REAL_MUL_LZERO] THEN
    REWRITE_TAC [← GSYM REAL_LE_ANTISYM, INFNORM_MUL_LEMMA] THEN
    GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV) [← GSYM VECTOR_MUL_LID] THEN
    FIRST_ASSUM (SUBST1_TAC o SYM o MATCH_MP REAL_MUL_LINV) THEN
    REWRITE_TAC [← GSYM VECTOR_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (← q r"abs(a) * abs(inv a) * infnorm(a % x:real^N)") THEN
    ASM_SIMP_TAC [INFNORM_MUL_LEMMA, REAL_LE_LMUL, REAL_ABS_POS] THEN
    ASM_SIMP_TAC [REAL_MUL_ASSOC, ← GSYM REAL_ABS_MUL, REAL_MUL_RINV] THEN
    REAL_ARITH_TAC)

  let INFNORM_POS_LT ← prove
   r"!x. &0 < infnorm x <=> ~(x = vec 0)"
   (MESON_TAC [REAL_LT_LE, INFNORM_POS_LE, INFNORM_EQ_0])

  let INFNORM_LE_NORM ← prove
   r"!x. infnorm(x) <= norm(x)"
   (SIMP_TAC [infnorm, REAL_SUP_LE_FINITE, INFNORM_SET_LEMMA] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [COMPONENT_LE_NORM])

  let NORM_LE_INFNORM ← prove
   r"!x:real^N. norm(x) <= sqrt(&(dimindex(:N))) * infnorm(x)"
   (GEN_TAC THEN GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o funpow 2 RAND_CONV)
     [← GSYM CARD_NUMSEG_1] THEN
    REWRITE_TAC [vector_norm] THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
    SIMP_TAC [DOT_POS_LE, SQRT_POS_LE, REAL_POS, REAL_LE_MUL, INFNORM_POS_LE,
              SQRT_POW_2, REAL_POW_MUL] THEN
    REWRITE_TAC [dot] THEN MATCH_MP_TAC SUM_BOUND THEN
    REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [← GSYM REAL_POW_2] THEN ONCE_REWRITE_TAC [← GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC [REAL_ABS_POS] THEN
    MATCH_MP_TAC (← REAL_ARITH (← q r"x <= y ==> x <= abs(y)")) THEN
    SIMP_TAC [infnorm, REAL_LE_SUP_FINITE, INFNORM_SET_LEMMA] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [REAL_LE_REFL])

  let NORM_CAUCHY_SCHWARZ_EQ ← prove
   r"!x:real^N y. x dot y = norm(x) * norm(y) <=> norm(x) % y = norm(y) % x"
   (REPEAT STRIP_TAC THEN
    MAP_EVERY ASM_CASES_TAC [← q r"x:real^N = vec 0", ← q r"y:real^N = vec 0"] THEN
    ASM_REWRITE_TAC [NORM_0, REAL_MUL_LZERO, REAL_MUL_RZERO,
      DOT_LZERO, DOT_RZERO, VECTOR_MUL_LZERO, VECTOR_MUL_RZERO] THEN
    MP_TAC (← ISPEC (← q r"norm(y:real^N) % x - norm(x:real^N) % y") DOT_EQ_0) THEN
    REWRITE_TAC [DOT_RSUB, DOT_LSUB, DOT_LMUL, DOT_RMUL, ← GSYM NORM_POW_2,
                 REAL_POW_2, VECTOR_SUB_EQ] THEN
    REWRITE_TAC [DOT_SYM, ← REAL_ARITH (← q
     r"y * (y * x * x - x * d) - x * (y * d - x * y * y) =
    &2 * x * y * (x * y - d)")] THEN
    ASM_SIMP_TAC [REAL_ENTIRE, NORM_EQ_0, REAL_SUB_0, REAL_OF_NUM_EQ, ARITH] THEN
    REWRITE_TAC [EQ_SYM_EQ])

  let NORM_CAUCHY_SCHWARZ_ABS_EQ ← prove
   r"!x:real^N y. abs(x dot y) = norm(x) * norm(y) <=>
                norm(x) % y = norm(y) % x \/ norm(x) % y = --norm(y) % x"
   (SIMP_TAC [← REAL_ARITH (← q r"&0 <= a ==> (abs x = a <=> x = a \/ --x = a)"),
              REAL_LE_MUL, NORM_POS_LE, ← GSYM DOT_RNEG] THEN
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o funpow 3 RAND_CONV) [← GSYM NORM_NEG] THEN
    REWRITE_TAC [NORM_CAUCHY_SCHWARZ_EQ] THEN REWRITE_TAC [NORM_NEG] THEN
    BINOP_TAC THEN VECTOR_ARITH_TAC)

  let NORM_TRIANGLE_EQ ← prove
   r"!x y:real^N. norm(x + y) = norm(x) + norm(y) <=> norm(x) % y = norm(y) % x"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM NORM_CAUCHY_SCHWARZ_EQ] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"norm(x + y:real^N) pow 2 = (norm(x) + norm(y)) pow 2") THEN
    CONJ_TAC THENL
     [REWRITE_TAC [← REAL_RING (← q r"x pow 2 = y pow 2 <=> x = y \/ x + y = &0")] THEN
      MAP_EVERY (fun t => tactic_of do pure (MP_TAC (← ISPEC t NORM_POS_LE)))
       [← q r"x + y:real^N", ← q r"x:real^N", ← q r"y:real^N"] THEN
      REAL_ARITH_TAC,
      REWRITE_TAC [NORM_POW_2, DOT_LADD, DOT_RADD, ← REAL_ARITH (← q
       r"(x + y) pow 2 = x pow 2 + y pow 2 + &2 * x * y")] THEN
      REWRITE_TAC [DOT_SYM] THEN REAL_ARITH_TAC])

  let DIST_TRIANGLE_EQ ← prove
   r"!x y z. dist(x,z) = dist(x,y) + dist(y,z) <=>
                norm (x - y) % (y - z) = norm (y - z) % (x - y)"
   (REWRITE_TAC [← GSYM NORM_TRIANGLE_EQ] THEN NORM_ARITH_TAC)

  let NORM_CROSS_MULTIPLY ← prove
   r"!a b x y:real^N.
        a % x = b % y /\ &0 < a /\ &0 < b
        ==> norm y % x = norm x % y"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC (← q r"y:real^N = vec 0") THEN
    ASM_SIMP_TAC [VECTOR_MUL_EQ_0, REAL_LT_IMP_NZ, VECTOR_MUL_RZERO] THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"\x:real^N. inv(a) % x")) THEN
    ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, REAL_LT_IMP_NZ, VECTOR_MUL_LID,
                  NORM_MUL, REAL_ABS_MUL, REAL_ABS_INV] THEN
    ASM_SIMP_TAC [real_abs, REAL_LT_IMP_LE, REAL_MUL_AC])

  return { infnorm, NUMSEG_DIMINDEX_NONEMPTY, INFNORM_SET_IMAGE, INFNORM_SET_LEMMA,
           INFNORM_POS_LE, INFNORM_TRIANGLE, INFNORM_EQ_0, INFNORM_0, INFNORM_NEG,
           INFNORM_SUB, REAL_ABS_SUB_INFNORM, REAL_ABS_INFNORM, COMPONENT_LE_INFNORM,
           INFNORM_MUL_LEMMA, INFNORM_MUL, INFNORM_POS_LT, INFNORM_LE_NORM, NORM_LE_INFNORM,
           NORM_CAUCHY_SCHWARZ_EQ, NORM_CAUCHY_SCHWARZ_ABS_EQ, NORM_TRIANGLE_EQ,
           DIST_TRIANGLE_EQ, NORM_CROSS_MULTIPLY }

/- ------------------------------------------------------------------------- -/
/- Collinearity.  (vectors.ml 9593-9808)                                     -/
/- ------------------------------------------------------------------------- -/

structure Collinear where
  collinear : thm
  COLLINEAR_ALT2 : thm
  COLLINEAR_ALT : thm
  COLLINEAR_SUBSET : thm
  COLLINEAR_EMPTY : thm
  COLLINEAR_SING : thm
  COLLINEAR_2 : thm
  COLLINEAR_SMALL : thm
  COLLINEAR_3 : thm
  COLLINEAR_LEMMA : thm
  COLLINEAR_LEMMA_ALT : thm
  COLLINEAR_SPAN : thm
  NORM_CAUCHY_SCHWARZ_EQUAL : thm
  DOT_CAUCHY_SCHWARZ_EQUAL : thm
  COLLINEAR_3_EXPAND : thm
  COLLINEAR_TRIPLES : thm
  COLLINEAR_4_3 : thm
  COLLINEAR_3_TRANS : thm
  ORTHOGONAL_TO_ORTHOGONAL_2D : thm
  COLLINEAR_3_2D : thm
  COLLINEAR_3_DOT_MULTIPLES : thm
  ORTHOGONAL_AND_COLLINEAR : thm
  deriving Inhabited

@[nospecialize]
def setupCollinear [HolBase] (D : VectorsDeps) (BBasics : Basics)
    (BVectorArith : VectorArith) (BDotProps : DotProps) (BNorm1 : Norm1) (BOrth : Orth)
    (BSpan1 : Span1) (BInfnorm : Infnorm) : ExceptT String IO Collinear := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, HAS_SIZE_CONV, MESON, MESON_TAC, REAL_ARITH,
        REAL_ARITH_TAC, REAL_RING, SET_RULE, SET_TAC, new_definition, .. } := D
  let { DE_MORGAN_THM, FORALL_IN_INSERT, .. } := D.core1
  let { HAS_SIZE, IMP_CONJ, INSERT_AC, IN_INSERT, IN_SING, LEFT_IMP_EXISTS_THM,
        LEFT_OR_DISTRIB, NOT_IN_EMPTY, .. } := D.core2
  let { REAL_DIV_RMUL, REAL_ENTIRE, REAL_EQ_SQUARE_ABS, REAL_LE_MUL, REAL_MUL_LINV,
        REAL_MUL_LNEG, .. } := D.core3
  let { REAL_POW_MUL, RIGHT_FORALL_IMP_THM, .. } := D.core4
  let { DOT_2, .. } := BBasics
  let { VECTOR_ARITH, VECTOR_ARITH_TAC, VECTOR_MUL_ASSOC, VECTOR_MUL_LID, VECTOR_MUL_LNEG,
        VECTOR_MUL_LZERO, VECTOR_MUL_RZERO, VECTOR_SUB_COMPONENT, VECTOR_SUB_EQ,
        VECTOR_SUB_REFL, VECTOR_SUB_RZERO, .. } := BVectorArith
  let { DOT_EQ_0, DOT_LMUL, DOT_LSUB, DOT_RMUL, DOT_RSUB, DOT_RZERO, DOT_SYM, .. } := BDotProps
  let { NORM_0, NORM_EQ_0, NORM_MUL, NORM_POS_LE, NORM_POW_2, VECTOR_MUL_EQ_0, .. } := BNorm1
  let { ORTHOGONAL_0, ORTHOGONAL_MUL, ORTHOGONAL_REFL, orthogonal, .. } := BOrth
  let { SPAN_SING, .. } := BSpan1
  let { NORM_CAUCHY_SCHWARZ_ABS_EQ, .. } := BInfnorm
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let collinear ← new_definition
   r"collinear s <=> ?u. !x y. x IN s /\ y IN s ==> ?c. x - y = c % u"

  let COLLINEAR_ALT2 ← prove
   r"!s:real^N->bool. collinear s <=> ?u v. !x. x IN s ==> ?c. x - u = c % v"
   (GEN_TAC THEN REWRITE_TAC [collinear] THEN EQ_TAC THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THENL [SET_TAC [], ALL_TAC] THEN
    MESON_TAC [← va
      r"x - u:real^N = c % v /\ y - u = d % v ==> x - y = (c - d) % v"])

  let COLLINEAR_ALT ← prove
   r"!s:real^N->bool. collinear s <=> ?u v. !x. x IN s ==> ?c. x = u + c % v"
   (REWRITE_TAC [COLLINEAR_ALT2] THEN MESON_TAC [← va
     r"x - u:real^N = c % v <=> x = u + c % v"])

  let COLLINEAR_SUBSET ← prove
   r"!s t. collinear t /\ s SUBSET t ==> collinear s"
   (REWRITE_TAC [collinear] THEN SET_TAC [])

  let COLLINEAR_EMPTY ← prove
   r"collinear {}"
   (REWRITE_TAC [collinear, NOT_IN_EMPTY])

  let COLLINEAR_SING ← prove
   r"!x. collinear {x}"
   (SIMP_TAC [collinear, IN_SING, VECTOR_SUB_REFL] THEN
    MESON_TAC [VECTOR_MUL_LZERO])

  let COLLINEAR_2 ← prove
   r"!x y:real^N. collinear {x,y}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [collinear, IN_INSERT, NOT_IN_EMPTY] THEN
    EXISTS_TAC (← q r"x - y:real^N") THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
     [EXISTS_TAC (← q r"&0"), EXISTS_TAC (← q r"&1"), EXISTS_TAC (← q r"-- &1"),
      EXISTS_TAC (← q r"&0")] THEN
    VECTOR_ARITH_TAC)

  let COLLINEAR_SMALL ← prove
   r"!s. FINITE s /\ CARD s <= 2 ==> collinear s"
   (REWRITE_TAC [← ARITH_RULE (← q r"s <= 2 <=> s = 0 \/ s = 1 \/ s = 2")] THEN
    REWRITE_TAC [LEFT_OR_DISTRIB, ← GSYM HAS_SIZE] THEN
    CONV_TAC (ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [COLLINEAR_EMPTY, COLLINEAR_SING, COLLINEAR_2])

  let COLLINEAR_3 ← prove
   r"!x y z. collinear {x,y,z} <=> collinear {vec 0,x - y,z - y}"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [collinear, FORALL_IN_INSERT, IMP_CONJ, RIGHT_FORALL_IMP_THM,
                 NOT_IN_EMPTY] THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    MESON_TAC [← va r"x - y = (x - y) - vec 0",
               ← va r"y - x = vec 0 - (x - y)",
               ← va r"x - z:real^N = (x - y) - (z - y)"])

  let COLLINEAR_LEMMA ← prove
   r"!x y:real^N. collinear {vec 0,x,y} <=>
                   x = vec 0 \/ y = vec 0 \/ ?c. y = c % x"
   (REPEAT GEN_TAC THEN
    MAP_EVERY ASM_CASES_TAC [← q r"x:real^N = vec 0", ← q r"y:real^N = vec 0"] THEN
    TRY (ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_SING, COLLINEAR_2] THEN HolCore.Tactics.NO_TAC) THEN
    ASM_REWRITE_TAC [collinear] THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"u:real^N")
       (fun th => tactic_of do
          pure (MP_TAC (← SPECL [← q r"x:real^N", ← q r"vec 0:real^N"] th) THEN
                MP_TAC (← SPECL [← q r"y:real^N", ← q r"vec 0:real^N"] th)))) THEN
      REWRITE_TAC [IN_INSERT, VECTOR_SUB_RZERO] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"e:real") SUBST_ALL_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"d:real") SUBST_ALL_TAC) THEN
      EXISTS_TAC (← q r"e / d") THEN REWRITE_TAC [VECTOR_MUL_ASSOC] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [VECTOR_MUL_EQ_0, DE_MORGAN_THM]) THEN
      ASM_SIMP_TAC [REAL_DIV_RMUL],
      STRIP_TAC THEN EXISTS_TAC (← q r"x:real^N") THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [] THENL
       [EXISTS_TAC (← q r"&0"), EXISTS_TAC (← q r"-- &1"), EXISTS_TAC (← q r"--c"),
        EXISTS_TAC (← q r"&1"), EXISTS_TAC (← q r"&0"), EXISTS_TAC (← q r"&1 - c"),
        EXISTS_TAC (← q r"c:real"), EXISTS_TAC (← q r"c - &1"), EXISTS_TAC (← q r"&0")] THEN
      VECTOR_ARITH_TAC])

  let COLLINEAR_LEMMA_ALT ← prove
   r"!x y. collinear {vec 0,x,y} <=> x = vec 0 \/ ?c. y = c % x"
   (REWRITE_TAC [COLLINEAR_LEMMA] THEN MESON_TAC [VECTOR_MUL_LZERO])

  let COLLINEAR_SPAN ← prove
   r"!a b:real^N. collinear{vec 0,a,b} <=> a = vec 0 \/ b IN span {a}"
   (REWRITE_TAC [SPAN_SING, COLLINEAR_LEMMA_ALT] THEN SET_TAC [])

  let NORM_CAUCHY_SCHWARZ_EQUAL ← prove
   r"!x y:real^N. abs(x dot y) = norm(x) * norm(y) <=> collinear {vec 0,x,y}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [NORM_CAUCHY_SCHWARZ_ABS_EQ] THEN
    MAP_EVERY ASM_CASES_TAC [← q r"x:real^N = vec 0", ← q r"y:real^N = vec 0"] THEN
    TRY (ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_SING, COLLINEAR_2, NORM_0,
                          VECTOR_MUL_LZERO, VECTOR_MUL_RZERO] THEN HolCore.Tactics.NO_TAC) THEN
    ASM_REWRITE_TAC [COLLINEAR_LEMMA] THEN EQ_TAC THENL
     [STRIP_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o AP_TERM
         (← q r"(%) (inv(norm(x:real^N))):real^N->real^N")),
        FIRST_X_ASSUM (MP_TAC o AP_TERM
         (← q r"(%) (--inv(norm(x:real^N))):real^N->real^N"))] THEN
      ASM_REWRITE_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LNEG] THEN
      ASM_SIMP_TAC [REAL_MUL_LINV, NORM_EQ_0, VECTOR_MUL_LNEG, VECTOR_MUL_LID,
                    ← va r"--x = --y <=> x:real^N = y"] THEN
      MESON_TAC [],
      STRIP_TAC THEN ASM_REWRITE_TAC [NORM_MUL, VECTOR_MUL_ASSOC] THEN
      MATCH_MP_TAC (← MESON [] (← q
        r"t = a \/ t = b ==> t % x = a % x \/ t % x = b % x")) THEN
      REWRITE_TAC [← GSYM REAL_MUL_LNEG,
                   ← REAL_ARITH (← q r"x * c = d * x <=> x * (c - d) = &0")] THEN
      ASM_REWRITE_TAC [REAL_ENTIRE, NORM_EQ_0] THEN REAL_ARITH_TAC])

  let DOT_CAUCHY_SCHWARZ_EQUAL ← prove
   r"!x y:real^N.
        (x dot y) pow 2 = (x dot x) * (y dot y) <=>
        collinear {vec 0,x,y}"
   (REWRITE_TAC [← GSYM NORM_CAUCHY_SCHWARZ_EQUAL] THEN
    REPEAT GEN_TAC THEN MATCH_MP_TAC (← REAL_ARITH (← q
     r"&0 <= y /\ (u:real = v <=> x = abs y) ==> (u = v <=> x = y)")) THEN
    SIMP_TAC [NORM_POS_LE, REAL_LE_MUL] THEN
    REWRITE_TAC [REAL_EQ_SQUARE_ABS] THEN REWRITE_TAC [REAL_POW_MUL, NORM_POW_2])

  let COLLINEAR_3_EXPAND ← prove
   r"!a b c:real^N. collinear{a,b,c} <=> a = c \/ ?u. b = u % a + (&1 - u) % c"
   (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [← SET_RULE (← q r"{a,b,c} = {a,c,b}")] THEN
    ONCE_REWRITE_TAC [COLLINEAR_3] THEN
    REWRITE_TAC [COLLINEAR_LEMMA, VECTOR_SUB_EQ] THEN
    ASM_CASES_TAC (← q r"a:real^N = c") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"b:real^N = c") THEN
    ASM_REWRITE_TAC [← va r"u % c + (&1 - u) % c = c"] THENL
     [EXISTS_TAC (← q r"&0") THEN VECTOR_ARITH_TAC,
      AP_TERM_TAC THEN ABS_TAC THEN VECTOR_ARITH_TAC])

  let COLLINEAR_TRIPLES ← prove
   r"!s a b:real^N.
        ~(a = b)
        ==> (collinear(a INSERT b INSERT s) <=>
             !x. x IN s ==> collinear{a,b,x})"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP
       (← REWRITE_RULE [IMP_CONJ] COLLINEAR_SUBSET)) THEN
      ASM SET_TAC [],
      ONCE_REWRITE_TAC [← SET_RULE (← q r"{a,b,x} = {a,x,b}")] THEN
      ASM_REWRITE_TAC [COLLINEAR_3_EXPAND] THEN DISCH_TAC THEN
      SUBGOAL_THEN
       (← q r"!x:real^N. x IN (a INSERT b INSERT s) ==> ?u. x = u % a + (&1 - u) % b")
      MP_TAC THENL
       [ASM_REWRITE_TAC [FORALL_IN_INSERT] THEN CONJ_TAC THENL
         [EXISTS_TAC (← q r"&1") THEN VECTOR_ARITH_TAC,
          EXISTS_TAC (← q r"&0") THEN VECTOR_ARITH_TAC],
        POP_ASSUM_LIST (K ALL_TAC) THEN DISCH_TAC THEN
        REWRITE_TAC [collinear] THEN EXISTS_TAC (← q r"b - a:real^N") THEN
        MAP_EVERY X_GEN_TAC [← q r"x:real^N", ← q r"y:real^N"] THEN STRIP_TAC THEN
        FIRST_X_ASSUM (fun th => tactic_of do
          pure (MP_TAC (← SPEC (← q r"x:real^N") th) THEN
                MP_TAC (← SPEC (← q r"y:real^N") th))) THEN
        ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC [← va
         r"(u % a + (&1 - u) % b) - (v % a + (&1 - v) % b):real^N =
        (v - u) % (b - a)"] THEN
        MESON_TAC []]])

  let COLLINEAR_4_3 ← prove
   r"!a b c d:real^N.
        ~(a = b)
        ==> (collinear {a,b,c,d} <=> collinear{a,b,c} /\ collinear{a,b,d})"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"{c:real^N,d}", ← q r"a:real^N", ← q r"b:real^N"]
      COLLINEAR_TRIPLES) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY])

  let COLLINEAR_3_TRANS ← prove
   r"!a b c d:real^N.
        collinear{a,b,c} /\ collinear{b,c,d} /\ ~(b = c) ==> collinear{a,b,d}"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC COLLINEAR_SUBSET THEN
    EXISTS_TAC (← q r"{b:real^N,c,a,d}") THEN ASM_SIMP_TAC [COLLINEAR_4_3] THEN
    CONJ_TAC THENL [ALL_TAC, SET_TAC []] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN SIMP_TAC [INSERT_AC])

  let ORTHOGONAL_TO_ORTHOGONAL_2D ← prove
   r"!x y z:real^2.
     ~(x = vec 0) /\ orthogonal x y /\ orthogonal x z
     ==> collinear {vec 0,y,z}"
   (REWRITE_TAC [orthogonal, ← GSYM DOT_CAUCHY_SCHWARZ_EQUAL, ← GSYM DOT_EQ_0] THEN
    REWRITE_TAC [DOT_2] THEN CONV_TAC (fun t => REAL_RING t))

  let COLLINEAR_3_2D ← prove
   r"!x y z:real^2. collinear{x,y,z} <=>
                  (z$1 - x$1) * (y$2 - x$2) = (y$1 - x$1) * (z$2 - x$2)"
   (ONCE_REWRITE_TAC [COLLINEAR_3] THEN
    REWRITE_TAC [← GSYM DOT_CAUCHY_SCHWARZ_EQUAL] THEN
    REWRITE_TAC [DOT_2, VECTOR_SUB_COMPONENT] THEN CONV_TAC (fun t => REAL_RING t))

  let COLLINEAR_3_DOT_MULTIPLES ← prove
   r"!a b c:real^N.
        collinear {a,b,c} <=>
        ((b - a) dot (b - a)) % (c - a) = ((c - a) dot (b - a)) % (b - a)"
   (REWRITE_TAC [VECTOR_SUB_RZERO] THEN
    REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"b:real^N = a") THENL
     [ASM_REWRITE_TAC [COLLINEAR_2, INSERT_AC, DOT_RZERO, VECTOR_MUL_LZERO,
                       VECTOR_SUB_REFL],
      ONCE_REWRITE_TAC [COLLINEAR_3] THEN
      POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [← GSYM VECTOR_SUB_EQ] THEN
      REWRITE_TAC [← GSYM DOT_CAUCHY_SCHWARZ_EQUAL, ← GSYM DOT_EQ_0] THEN
      REWRITE_TAC [← GSYM DOT_EQ_0, DOT_RSUB, DOT_LSUB, DOT_RMUL, DOT_LMUL] THEN
      REWRITE_TAC [DOT_SYM] THEN CONV_TAC (fun t => REAL_RING t)])

  let ORTHOGONAL_AND_COLLINEAR ← prove
   r"!x y:real^N.
        orthogonal x y /\ collinear{vec 0,x,y} <=> x = vec 0 \/ y = vec 0"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"x:real^N = vec 0") THEN
    ASM_REWRITE_TAC [ORTHOGONAL_0, COLLINEAR_2, ← SET_RULE (← q r"{a,a,b} = {a,b}")] THEN
    ASM_CASES_TAC (← q r"y:real^N = vec 0") THEN
    ASM_REWRITE_TAC [ORTHOGONAL_0, COLLINEAR_2, ← SET_RULE (← q r"{a,b,a} = {a,b}")] THEN
    DISCH_THEN (CONJUNCTS_THEN MP_TAC) THEN
    ASM_SIMP_TAC [COLLINEAR_LEMMA_ALT, LEFT_IMP_EXISTS_THM] THEN
    ASM_REWRITE_TAC [ORTHOGONAL_MUL, ORTHOGONAL_REFL] THEN
    ASM_MESON_TAC [VECTOR_MUL_LZERO])

  return { collinear, COLLINEAR_ALT2, COLLINEAR_ALT, COLLINEAR_SUBSET, COLLINEAR_EMPTY,
           COLLINEAR_SING, COLLINEAR_2, COLLINEAR_SMALL, COLLINEAR_3, COLLINEAR_LEMMA,
           COLLINEAR_LEMMA_ALT, COLLINEAR_SPAN, NORM_CAUCHY_SCHWARZ_EQUAL,
           DOT_CAUCHY_SCHWARZ_EQUAL, COLLINEAR_3_EXPAND, COLLINEAR_TRIPLES, COLLINEAR_4_3,
           COLLINEAR_3_TRANS, ORTHOGONAL_TO_ORTHOGONAL_2D, COLLINEAR_3_2D,
           COLLINEAR_3_DOT_MULTIPLES, ORTHOGONAL_AND_COLLINEAR }

/- ------------------------------------------------------------------------- -/
/- Between-ness; midpoint between two points.  (vectors.ml 9813-10043)       -/
/- ------------------------------------------------------------------------- -/

structure Between where
  between : thm
  BETWEEN_REFL : thm
  BETWEEN_REFL_EQ : thm
  BETWEEN_SYM : thm
  BETWEEN_ANTISYM : thm
  BETWEEN_TRANS : thm
  BETWEEN_TRANS_2 : thm
  BETWEEN_TRANSLATION : thm
  BETWEEN_NORM : thm
  BETWEEN_DOT : thm
  BETWEEN_EXISTS_EXTENSION : thm
  BETWEEN_IMP_COLLINEAR : thm
  BETWEEN_CMUL_LIFT : thm
  BETWEEN_1 : thm
  COLLINEAR_BETWEEN_CASES : thm
  COLLINEAR_BETWEEN_CASES_2 : thm
  BETWEEN_RESTRICTED_CASES : thm
  COLLINEAR_DIST_BETWEEN : thm
  BETWEEN_COLLINEAR_DIST_EQ : thm
  COLLINEAR_1 : thm
  midpoint : thm
  MIDPOINT_REFL : thm
  MIDPOINT_SYM : thm
  DIST_MIDPOINT : thm
  MIDPOINT_EQ_ENDPOINT : thm
  BETWEEN_MIDPOINT : thm
  MIDPOINT_LINEAR_IMAGE : thm
  COLLINEAR_MIDPOINT : thm
  MIDPOINT_COLLINEAR : thm
  MIDPOINT_BETWEEN : thm
  DROP_MIDPOINT : thm
  deriving Inhabited

@[nospecialize]
def setupBetween [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BNorm1 : Norm1) (BNormArith : NormArithB) (BMetric : Metric) (BLinear : Linear)
    (BLiftDrop1 : LiftDrop1) (BLiftDrop2 : LiftDrop2) (BInfnorm : Infnorm)
    (BCollinear : Collinear) : ExceptT String IO Between := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, REAL_ARITH_TAC, REAL_RING, SET_TAC, new_definition,
        .. } := D
  let { ARITH_EQ, FORALL_IN_INSERT, .. } := D.core1
  let { INSERT_AC, LEFT_IMP_EXISTS_THM, NOT_IN_EMPTY, .. } := D.core2
  let { REAL_ABS_NUM, REAL_ADD_RDISTRIB, REAL_DIV_LMUL, REAL_EQ_MUL_RCANCEL, REAL_LE_DIV,
        REAL_MUL_LINV, .. } := D.core3
  let { REAL_MUL_RNEG, .. } := D.core4
  let { VECTOR_ADD_SYM, VECTOR_ARITH, VECTOR_ARITH_TAC, VECTOR_MUL_ASSOC, VECTOR_SUB_EQ,
        VECTOR_SUB_RDISTRIB, VECTOR_SUB_RZERO, VEC_EQ, .. } := BVectorArith
  let { DIST_REAL, NORM_EQ_0, NORM_MUL, NORM_POS_LE, NORM_SUB, VECTOR_MUL_EQ_0,
        VECTOR_MUL_LCANCEL_IMP, VECTOR_MUL_RCANCEL, dist, .. } := BNorm1
  let { NORM_ARITH_TAC, .. } := BNormArith
  let { DIST_SYM, .. } := BMetric
  let { LINEAR_ADD, LINEAR_CMUL, .. } := BLinear
  let { DROP_ADD, DROP_VEC, LIFT_DROP, LIFT_SUB, drop, .. } := BLiftDrop1
  let { DROP_CMUL, NORM_LIFT, .. } := BLiftDrop2
  let { DIST_TRIANGLE_EQ, NORM_CAUCHY_SCHWARZ_EQ, .. } := BInfnorm
  let { COLLINEAR_2, COLLINEAR_3, COLLINEAR_3_EXPAND, COLLINEAR_ALT, COLLINEAR_LEMMA,
        COLLINEAR_SUBSET, COLLINEAR_TRIPLES, .. } := BCollinear
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let between ← new_definition
   r"between x (a,b) <=> dist(a,b) = dist(a,x) + dist(x,b)"

  let BETWEEN_REFL ← prove
   r"!a b. between a (a,b) /\ between b (a,b) /\ between a (a,a)"
   (REWRITE_TAC [between] THEN NORM_ARITH_TAC)

  let BETWEEN_REFL_EQ ← prove
   r"!a x. between x (a,a) <=> x = a"
   (REWRITE_TAC [between] THEN NORM_ARITH_TAC)

  let BETWEEN_SYM ← prove
   r"!a b x. between x (a,b) <=> between x (b,a)"
   (REWRITE_TAC [between] THEN NORM_ARITH_TAC)

  let BETWEEN_ANTISYM ← prove
   r"!a b c. between a (b,c) /\ between b (a,c) ==> a = b"
   (REWRITE_TAC [between, DIST_SYM] THEN NORM_ARITH_TAC)

  let BETWEEN_TRANS ← prove
   r"!a b c d. between a (b,c) /\ between d (a,c) ==> between d (b,c)"
   (REWRITE_TAC [between, DIST_SYM] THEN NORM_ARITH_TAC)

  let BETWEEN_TRANS_2 ← prove
   r"!a b c d. between a (b,c) /\ between d (a,b) ==> between a (c,d)"
   (REWRITE_TAC [between, DIST_SYM] THEN NORM_ARITH_TAC)

  let BETWEEN_TRANSLATION ← prove
   r"!a x y. between (a + x) (a + y,a + z) <=> between x (y,z)"
   (REWRITE_TAC [between] THEN NORM_ARITH_TAC)

  let BETWEEN_NORM ← prove
   r"!a b x:real^N.
     between x (a,b) <=> norm(x - a) % (b - x) = norm(b - x) % (x - a)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [between, DIST_TRIANGLE_EQ] THEN
    REWRITE_TAC [NORM_SUB] THEN VECTOR_ARITH_TAC)

  let BETWEEN_DOT ← prove
   r"!a b x:real^N.
     between x (a,b) <=> (x - a) dot (b - x) = norm(x - a) * norm(b - x)"
   (REWRITE_TAC [BETWEEN_NORM, NORM_CAUCHY_SCHWARZ_EQ])

  let BETWEEN_EXISTS_EXTENSION ← prove
   r"!a b x:real^N.
        between b (a,x) /\ ~(b = a) ==> ?d. &0 <= d /\ x = b + d % (b - a)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [BETWEEN_NORM] THEN STRIP_TAC THEN
    EXISTS_TAC (← q r"norm(x - b:real^N) / norm(b - a)") THEN
    SIMP_TAC [REAL_LE_DIV, NORM_POS_LE] THEN FIRST_X_ASSUM
     (MP_TAC o AP_TERM (← q r"(%) (inv(norm(b - a:real^N))):real^N->real^N")) THEN
    ASM_SIMP_TAC [VECTOR_MUL_ASSOC, REAL_MUL_LINV, NORM_EQ_0, VECTOR_SUB_EQ] THEN
    VECTOR_ARITH_TAC)

  let BETWEEN_IMP_COLLINEAR ← prove
   r"!a b x:real^N. between x (a,b) ==> collinear {a,x,b}"
   (REPEAT GEN_TAC THEN MAP_EVERY
     (fun t => ASM_CASES_TAC t THEN
               TRY (ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_2] THEN HolCore.Tactics.NO_TAC))
     [← q r"x:real^N = a", ← q r"x:real^N = b", ← q r"a:real^N = b"] THEN
    ONCE_REWRITE_TAC [COLLINEAR_3, BETWEEN_NORM] THEN
    DISCH_TAC THEN REWRITE_TAC [COLLINEAR_LEMMA] THEN
    REPEAT DISJ2_TAC THEN EXISTS_TAC (← q r"--(norm(b - x:real^N) / norm(x - a))") THEN
    MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN EXISTS_TAC (← q r"norm(x - a:real^N)") THEN
    ASM_REWRITE_TAC [VECTOR_MUL_ASSOC, REAL_MUL_RNEG] THEN
    ASM_SIMP_TAC [REAL_DIV_LMUL, NORM_EQ_0, VECTOR_SUB_EQ] THEN
    VECTOR_ARITH_TAC)

  let BETWEEN_CMUL_LIFT ← prove
   r"!a b c v:real^N.
        between (c % v) (a % v,b % v) <=>
        v = vec 0 \/ between (lift c) (lift a,lift b)"
   (REWRITE_TAC [between, dist, ← GSYM VECTOR_SUB_RDISTRIB, ← GSYM LIFT_SUB,
                 NORM_MUL, ← GSYM REAL_ADD_RDISTRIB, NORM_LIFT] THEN
    REWRITE_TAC [← GSYM NORM_EQ_0] THEN CONV_TAC (fun t => REAL_RING t))

  let BETWEEN_1 ← prove
   r"!a b x. between x (a,b) <=>
           drop a <= drop x /\ drop x <= drop b \/
           drop b <= drop x /\ drop x <= drop a"
   (REWRITE_TAC [between, DIST_REAL, ← GSYM drop] THEN REAL_ARITH_TAC)

  let COLLINEAR_BETWEEN_CASES ← prove
   r"!a b c:real^N.
        collinear {a,b,c} <=>
        between a (b,c) \/ between b (c,a) \/ between c (a,b)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [ALL_TAC, MESON_TAC [BETWEEN_IMP_COLLINEAR, INSERT_AC]] THEN
    REWRITE_TAC [COLLINEAR_ALT, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"z:real^N", ← q r"v:real^N"] THEN
    REWRITE_TAC [VECTOR_SUB_RZERO, FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [BETWEEN_TRANSLATION, BETWEEN_CMUL_LIFT] THEN
    ASM_CASES_TAC (← q r"v:real^N = vec 0") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [BETWEEN_1, LIFT_DROP] THEN REAL_ARITH_TAC)

  let COLLINEAR_BETWEEN_CASES_2 ← prove
   r"!a b c d:real^N.
        between c (a,b) /\ between d (a,b)
        ==> between d (a,c) \/ between d (c,b)"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"b:real^N = a") THEN
    ASM_SIMP_TAC [BETWEEN_REFL_EQ] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"collinear {a:real^N,b,c,d}") MP_TAC THENL
     [W (MP_TAC o PART_MATCH (lhand o rand) COLLINEAR_TRIPLES o snd) THEN
      ASM_REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
      ASM_MESON_TAC [BETWEEN_IMP_COLLINEAR, INSERT_AC],
      REWRITE_TAC [COLLINEAR_ALT, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"z:real^N", ← q r"v:real^N"] THEN
      DISCH_THEN (fun th => REPEAT (POP_ASSUM MP_TAC) THEN MP_TAC th) THEN
      REWRITE_TAC [VECTOR_SUB_RZERO, FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
      STRIP_TAC THEN DISCH_THEN (K ALL_TAC) THEN
      ASM_REWRITE_TAC [BETWEEN_TRANSLATION, BETWEEN_CMUL_LIFT] THEN
      ASM_CASES_TAC (← q r"v:real^N = vec 0") THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [BETWEEN_1, LIFT_DROP] THEN REAL_ARITH_TAC])

  let BETWEEN_RESTRICTED_CASES ← prove
   r"!a b c x:real^N.
        between x (a,b) /\ between x (a,c) /\ ~(x = a)
        ==> between b (a,c) \/ between c (a,b)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"collinear{a:real^N,x,b,c}") MP_TAC THENL
     [W (MP_TAC o PART_MATCH (lhand o rand) COLLINEAR_TRIPLES o snd) THEN
      ASM_REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
      ASM_MESON_TAC [BETWEEN_IMP_COLLINEAR, INSERT_AC],
      REWRITE_TAC [COLLINEAR_ALT, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"z:real^N", ← q r"v:real^N"] THEN
      DISCH_THEN (fun th => REPEAT (POP_ASSUM MP_TAC) THEN MP_TAC th) THEN
      REWRITE_TAC [VECTOR_SUB_RZERO, FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [BETWEEN_TRANSLATION] THEN
      ASM_REWRITE_TAC [BETWEEN_CMUL_LIFT, VECTOR_MUL_RCANCEL,
          ← va r"a + x:real^N = a + y <=> x = y"] THEN
      ASM_CASES_TAC (← q r"v:real^N = vec 0") THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [BETWEEN_1, LIFT_DROP] THEN REAL_ARITH_TAC])

  let COLLINEAR_DIST_BETWEEN ← prove
   r"!a b x. collinear {x,a,b} /\
           dist(x,a) <= dist(a,b) /\ dist(x,b) <= dist(a,b)
           ==> between x (a,b)"
   (SIMP_TAC [COLLINEAR_BETWEEN_CASES, between, DIST_SYM] THEN NORM_ARITH_TAC)

  let BETWEEN_COLLINEAR_DIST_EQ ← prove
   r"!a b x:real^N.
        between x (a,b) <=>
        collinear {a, x, b} /\
        dist(x,a) <= dist(a,b) /\ dist(x,b) <= dist(a,b)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [SIMP_TAC [BETWEEN_IMP_COLLINEAR] THEN REWRITE_TAC [between] THEN
      NORM_ARITH_TAC,
      MESON_TAC [COLLINEAR_DIST_BETWEEN, INSERT_AC]])

  let COLLINEAR_1 ← prove
   r"!s:real^1->bool. collinear s"
   (GEN_TAC THEN MATCH_MP_TAC COLLINEAR_SUBSET THEN
    EXISTS_TAC (← q r"(vec 0:real^1) INSERT (vec 1) INSERT s") THEN
    CONJ_TAC THENL [ALL_TAC, SET_TAC []] THEN
    W (MP_TAC o PART_MATCH (lhs o rand) COLLINEAR_TRIPLES o snd) THEN
    REWRITE_TAC [VEC_EQ, ARITH_EQ] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [COLLINEAR_BETWEEN_CASES] THEN
    REWRITE_TAC [between, DIST_REAL, ← GSYM drop, DROP_VEC, REAL_ABS_NUM] THEN
    REAL_ARITH_TAC)

  let midpoint ← new_definition
   r"midpoint(a,b) = inv(&2) % (a + b)"

  let MIDPOINT_REFL ← prove
   r"!x. midpoint(x,x) = x"
   (REWRITE_TAC [midpoint] THEN VECTOR_ARITH_TAC)

  let MIDPOINT_SYM ← prove
   r"!a b. midpoint(a,b) = midpoint(b,a)"
   (REWRITE_TAC [midpoint, VECTOR_ADD_SYM])

  let DIST_MIDPOINT ← prove
   r"!a b. dist(a,midpoint(a,b)) = dist(a,b) / &2 /\
         dist(b,midpoint(a,b)) = dist(a,b) / &2 /\
         dist(midpoint(a,b),a) = dist(a,b) / &2 /\
         dist(midpoint(a,b),b) = dist(a,b) / &2"
   (REWRITE_TAC [midpoint] THEN NORM_ARITH_TAC)

  let MIDPOINT_EQ_ENDPOINT ← prove
   r"!a b. (midpoint(a,b) = a <=> a = b) /\
         (midpoint(a,b) = b <=> a = b) /\
         (a = midpoint(a,b) <=> a = b) /\
         (b = midpoint(a,b) <=> a = b)"
   (REWRITE_TAC [midpoint] THEN NORM_ARITH_TAC)

  let BETWEEN_MIDPOINT ← prove
   r"!a b. between (midpoint(a,b)) (a,b) /\ between (midpoint(a,b)) (b,a)"
   (REWRITE_TAC [between, midpoint] THEN NORM_ARITH_TAC)

  let MIDPOINT_LINEAR_IMAGE ← prove
   r"!f a b. linear f ==> midpoint(f a,f b) = f(midpoint(a,b))"
   (SIMP_TAC [midpoint, LINEAR_ADD, LINEAR_CMUL])

  let COLLINEAR_MIDPOINT ← prove
   r"!a b. collinear{a,midpoint(a,b),b}"
   (REPEAT GEN_TAC THEN REWRITE_TAC [COLLINEAR_3_EXPAND, midpoint] THEN
    DISJ2_TAC THEN EXISTS_TAC (← q r"&1 / &2") THEN VECTOR_ARITH_TAC)

  let MIDPOINT_COLLINEAR ← prove
   r"!a b c:real^N.
        ~(a = c)
        ==> (b = midpoint(a,c) <=> collinear{a,b,c} /\ dist(a,b) = dist(b,c))"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← TAUT (← q r"(a ==> b) /\ (b ==> (a <=> c)) ==> (a <=> b /\ c)")) THEN
    SIMP_TAC [COLLINEAR_MIDPOINT] THEN ASM_REWRITE_TAC [COLLINEAR_3_EXPAND] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [midpoint, dist] THEN
    REWRITE_TAC
     [← va r"a - (u % a + (&1 - u) % c) = (&1 - u) % (a - c)",
      ← va r"(u % a + (&1 - u) % c) - c = u % (a - c)",
      ← va r"u % a + (&1 - u) % c = inv (&2) % (a + c) <=>
                  (u - &1 / &2) % (a - c) = vec 0"] THEN
    ASM_SIMP_TAC [NORM_MUL, REAL_EQ_MUL_RCANCEL, NORM_EQ_0, VECTOR_SUB_EQ,
                  VECTOR_MUL_EQ_0] THEN
    REAL_ARITH_TAC)

  let MIDPOINT_BETWEEN ← prove
   r"!a b c:real^N.
        b = midpoint (a,c) <=> between b (a,c) /\ dist (a,b) = dist (b,c)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"a:real^N = c") THENL
     [ASM_SIMP_TAC [BETWEEN_REFL_EQ, MIDPOINT_REFL, DIST_SYM], ALL_TAC] THEN
    EQ_TAC THEN SIMP_TAC [BETWEEN_MIDPOINT, DIST_MIDPOINT] THEN
    ASM_MESON_TAC [MIDPOINT_COLLINEAR, BETWEEN_IMP_COLLINEAR])

  let DROP_MIDPOINT ← prove
   r"!x y. drop(midpoint(x,y)) = (drop x + drop y) / &2"
   (REWRITE_TAC [midpoint, DROP_ADD, DROP_CMUL] THEN REAL_ARITH_TAC)

  return { between, BETWEEN_REFL, BETWEEN_REFL_EQ, BETWEEN_SYM, BETWEEN_ANTISYM,
           BETWEEN_TRANS, BETWEEN_TRANS_2, BETWEEN_TRANSLATION, BETWEEN_NORM, BETWEEN_DOT,
           BETWEEN_EXISTS_EXTENSION, BETWEEN_IMP_COLLINEAR, BETWEEN_CMUL_LIFT, BETWEEN_1,
           COLLINEAR_BETWEEN_CASES, COLLINEAR_BETWEEN_CASES_2, BETWEEN_RESTRICTED_CASES,
           COLLINEAR_DIST_BETWEEN, BETWEEN_COLLINEAR_DIST_EQ, COLLINEAR_1, midpoint,
           MIDPOINT_REFL, MIDPOINT_SYM, DIST_MIDPOINT, MIDPOINT_EQ_ENDPOINT, BETWEEN_MIDPOINT,
           MIDPOINT_LINEAR_IMAGE, COLLINEAR_MIDPOINT, MIDPOINT_COLLINEAR, MIDPOINT_BETWEEN,
           DROP_MIDPOINT }

/- ------------------------------------------------------------------------- -/
/- Intervals, overloaded for standard-ish notation [a,b] and (a,b).          -/
/- (vectors.ml 10048-10248)                                                   -/
/- ------------------------------------------------------------------------- -/

structure Interval where
  open_interval : thm
  closed_interval : thm
  interval : thm
  IN_INTERVAL : thm
  IN_INTERVAL_REFLECT : thm
  REFLECT_INTERVAL : thm
  INTERVAL_EQ_EMPTY : thm
  INTERVAL_NE_EMPTY : thm
  SUBSET_INTERVAL_IMP : thm
  INTERVAL_SING : thm
  SUBSET_INTERVAL : thm
  DISJOINT_INTERVAL : thm
  ENDS_IN_INTERVAL : thm
  ENDS_IN_UNIT_INTERVAL : thm
  INTER_INTERVAL : thm
  INTERVAL_OPEN_SUBSET_CLOSED : thm
  deriving Inhabited

@[nospecialize]
def setupInterval [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith) :
    ExceptT String IO Interval := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, REAL_ARITH_TAC, SET_RULE, make_overloadable,
        new_definition, overload_interface, .. } := D
  let { AND_FORALL_THM, CART_EQ, CONJ_ASSOC, DE_MORGAN_THM, DIMINDEX_GE_1, EQ_SYM_EQ,
        EXTENSION, .. } := D.core1
  let { FST, IMP_IMP, IN_ELIM_THM, IN_INTER, IN_SING, LAMBDA_BETA, LE_REFL, MONO_EXISTS,
        MONO_FORALL, NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, .. } := D.core2
  let { REAL_LE_ANTISYM, REAL_LE_MIN, REAL_LE_NEG2, REAL_LE_REFL, REAL_LE_TRANS,
        REAL_LT_ANTISYM, REAL_LT_IMP_LE, REAL_LT_NEG2, REAL_LT_REFL, REAL_LT_TRANS,
        REAL_MAX_LE, .. } := D.core3
  let { REAL_NOT_LE, REAL_NOT_LT, REAL_POS, RIGHT_IMP_EXISTS_THM, SKOLEM_THM, SND,
        SUBSET, .. } := D.core4
  let { HD, SURJECTIVE_IMAGE_EQ, .. } := D.core5
  let { REAL_LE_BETWEEN, REAL_LT_BETWEEN, .. } := D.misc
  let { VECTOR_NEG_COMPONENT, VECTOR_NEG_NEG, VEC_COMPONENT, .. } := BVectorArith
  -- @@SCOPE END

  let open_interval ← new_definition
   r"open_interval(a:real^N,b:real^N) =
        {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                        ==> a$i < x$i /\ x$i < b$i}"

  let closed_interval ← new_definition
   r"closed_interval(l:(real^N#real^N)list) =
         {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                         ==> FST(HD l)$i <= x$i /\ x$i <= SND(HD l)$i}"

  make_overloadable "interval" (← qty "A")

  overload_interface "interval" (← q r"open_interval")
  overload_interface "interval" (← q r"closed_interval")

  let interval ← prove
   r"(interval (a,b) = {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                                     ==> a$i < x$i /\ x$i < b$i}) /\
   (interval [a,b] = {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                                     ==> a$i <= x$i /\ x$i <= b$i})"
   (REWRITE_TAC [open_interval, closed_interval, HD, FST, SND])

  let IN_INTERVAL ← prove
   r"(!x:real^N.
        x IN interval (a,b) <=>
                !i. 1 <= i /\ i <= dimindex(:N)
                    ==> a$i < x$i /\ x$i < b$i) /\
   (!x:real^N.
        x IN interval [a,b] <=>
                !i. 1 <= i /\ i <= dimindex(:N)
                    ==> a$i <= x$i /\ x$i <= b$i)"
   (REWRITE_TAC [interval, IN_ELIM_THM])

  let IN_INTERVAL_REFLECT ← prove
   r"(!a b x. (--x) IN interval[--b,--a] <=> x IN interval[a,b]) /\
   (!a b x. (--x) IN interval(--b,--a) <=> x IN interval(a,b))"
   (SIMP_TAC [IN_INTERVAL, REAL_LT_NEG2, REAL_LE_NEG2, VECTOR_NEG_COMPONENT] THEN
    MESON_TAC [])

  let REFLECT_INTERVAL ← prove
   r"(!a b:real^N. IMAGE (--) (interval[a,b]) = interval[--b,--a]) /\
   (!a b:real^N. IMAGE (--) (interval(a,b)) = interval(--b,--a))"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    REWRITE_TAC [IN_INTERVAL_REFLECT] THEN MESON_TAC [VECTOR_NEG_NEG])

  let INTERVAL_EQ_EMPTY ← prove
   r"((interval [a:real^N,b] = {}) <=>
    ?i. 1 <= i /\ i <= dimindex(:N) /\ b$i < a$i) /\
   ((interval (a:real^N,b) = {}) <=>
    ?i. 1 <= i /\ i <= dimindex(:N) /\ b$i <= a$i)"
   (REWRITE_TAC [EXTENSION, IN_INTERVAL, NOT_IN_EMPTY] THEN
    REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, ← GSYM CONJ_ASSOC] THEN
    CONJ_TAC THEN EQ_TAC THENL
     [MESON_TAC [REAL_LE_REFL, REAL_NOT_LE],
      MESON_TAC [REAL_LE_TRANS, REAL_NOT_LE],
      ALL_TAC,
      MESON_TAC [REAL_LT_TRANS, REAL_NOT_LT]] THEN
    SUBGOAL_THEN (← q r"!a b. ?c. a < b ==> a < c /\ c < b")
    (MP_TAC o REWRITE_RULE [SKOLEM_THM]) THENL
     [MESON_TAC [REAL_LT_BETWEEN], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"mid:real->real->real")) THEN
    DISCH_THEN (MP_TAC o SPEC
     (← q r"(lambda i. mid ((a:real^N)$i) ((b:real^N)$i)):real^N")) THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"a /\ b /\ c <=> ~(a /\ b ==> ~c)")] THEN
    SIMP_TAC [LAMBDA_BETA] THEN ASM_MESON_TAC [REAL_NOT_LT])

  let INTERVAL_NE_EMPTY ← prove
   r"(~(interval [a:real^N,b] = {}) <=>
    !i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= b$i) /\
   (~(interval (a:real^N,b) = {}) <=>
    !i. 1 <= i /\ i <= dimindex(:N) ==> a$i < b$i)"
   (REWRITE_TAC [INTERVAL_EQ_EMPTY] THEN MESON_TAC [REAL_NOT_LE])

  let SUBSET_INTERVAL_IMP ← prove
   r"((!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i)
    ==> interval[c,d] SUBSET interval[a:real^N,b]) /\
   ((!i. 1 <= i /\ i <= dimindex(:N) ==> a$i < c$i /\ d$i < b$i)
    ==> interval[c,d] SUBSET interval(a:real^N,b)) /\
   ((!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i)
    ==> interval(c,d) SUBSET interval[a:real^N,b]) /\
   ((!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i)
    ==> interval(c,d) SUBSET interval(a:real^N,b))"
   (REWRITE_TAC [SUBSET, IN_INTERVAL] THEN REPEAT CONJ_TAC THEN
    DISCH_TAC THEN GEN_TAC THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC [IMP_IMP, AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
    GEN_TAC THEN DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC)

  let INTERVAL_SING ← prove
   r"interval[a,a] = {a} /\ interval(a,a) = {}"
   (REWRITE_TAC [EXTENSION, IN_SING, NOT_IN_EMPTY, IN_INTERVAL] THEN
    REWRITE_TAC [REAL_LE_ANTISYM, REAL_LT_ANTISYM, CART_EQ, EQ_SYM_EQ] THEN
    MESON_TAC [DIMINDEX_GE_1, LE_REFL])

  let SUBSET_INTERVAL ← do
    let lemma ← prove
     r"(!x:real^N. (!i. 1 <= i /\ i <= dimindex(:N) ==> Q i (x$i))
                 ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> R i (x$i)))
     ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> ?y. Q i y)
         ==> !i y. 1 <= i /\ i <= dimindex(:N) /\ Q i y ==> R i y"
     (DISCH_TAC THEN REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"f:num->real") STRIP_ASSUME_TAC) THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o
       SPEC (← q r"(lambda j. if j = i then y else f j):real^N")) THEN
      SIMP_TAC [LAMBDA_BETA] THEN ASM_MESON_TAC [])
    prove
     r"(interval[c,d] SUBSET interval[a:real^N,b] <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> c$i <= d$i)
        ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i)) /\
   (interval[c,d] SUBSET interval(a:real^N,b) <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> c$i <= d$i)
        ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i < c$i /\ d$i < b$i)) /\
   (interval(c,d) SUBSET interval[a:real^N,b] <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> c$i < d$i)
        ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i)) /\
   (interval(c,d) SUBSET interval(a:real^N,b) <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> c$i < d$i)
        ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i))"
     (REPEAT STRIP_TAC THEN
      (MATCH_MP_TAC (← TAUT (← q
        r"(~q ==> p) /\ (q ==> (p <=> r)) ==> (p <=> q ==> r)")) THEN
       CONJ_TAC THENL
        [DISCH_TAC THEN MATCH_MP_TAC (← SET_RULE (← q r"s = {} ==> s SUBSET t")) THEN
         REWRITE_TAC [INTERVAL_EQ_EMPTY] THEN ASM_MESON_TAC [REAL_NOT_LT],
         ALL_TAC] THEN
       DISCH_TAC THEN EQ_TAC THEN REWRITE_TAC [SUBSET_INTERVAL_IMP] THEN
       REWRITE_TAC [SUBSET, IN_INTERVAL] THEN
       DISCH_THEN (MP_TAC o MATCH_MP lemma) THEN ANTS_TAC THENL
        [ASM_MESON_TAC [REAL_LT_BETWEEN, REAL_LE_BETWEEN], ALL_TAC] THEN
       MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC (← q r"i:num") THEN
       DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC [] THEN
       FIRST_X_ASSUM (MP_TAC o SPEC (← q r"i:num")) THEN
       ASM_REWRITE_TAC [] THEN POP_ASSUM_LIST (K ALL_TAC) THEN STRIP_TAC)
      THENL
       [ASM_MESON_TAC [REAL_LE_TRANS, REAL_LE_REFL],
        ASM_MESON_TAC [REAL_LE_TRANS, REAL_LE_REFL],
        ALL_TAC, ALL_TAC] THEN
      (REPEAT STRIP_TAC THENL
        [FIRST_X_ASSUM (MP_TAC o SPEC
          (← q r"((c:real^N)$i + min ((a:real^N)$i) ((d:real^N)$i)) / &2")) THEN
         POP_ASSUM MP_TAC THEN REAL_ARITH_TAC,
         FIRST_X_ASSUM (MP_TAC o SPEC
          (← q r"(max ((b:real^N)$i) ((c:real^N)$i) + (d:real^N)$i) / &2")) THEN
         POP_ASSUM MP_TAC THEN REAL_ARITH_TAC]))

  let DISJOINT_INTERVAL ← prove
   r"!a b c d:real^N.
        (interval[a,b] INTER interval[c,d] = {} <=>
          ?i. 1 <= i /\ i <= dimindex(:N) /\
              (b$i < a$i \/ d$i < c$i \/ b$i < c$i \/ d$i < a$i)) /\
        (interval[a,b] INTER interval(c,d) = {} <=>
          ?i. 1 <= i /\ i <= dimindex(:N) /\
              (b$i < a$i \/ d$i <= c$i \/ b$i <= c$i \/ d$i <= a$i)) /\
        (interval(a,b) INTER interval[c,d] = {} <=>
          ?i. 1 <= i /\ i <= dimindex(:N) /\
              (b$i <= a$i \/ d$i < c$i \/ b$i <= c$i \/ d$i <= a$i)) /\
        (interval(a,b) INTER interval(c,d) = {} <=>
          ?i. 1 <= i /\ i <= dimindex(:N) /\
              (b$i <= a$i \/ d$i <= c$i \/ b$i <= c$i \/ d$i <= a$i))"
   (REWRITE_TAC [EXTENSION, IN_INTER, IN_INTERVAL, NOT_IN_EMPTY] THEN
    REWRITE_TAC [AND_FORALL_THM, NOT_FORALL_THM] THEN
    REWRITE_TAC [← TAUT (← q r"~((p ==> q) /\ (p ==> r)) <=> p /\ (~q \/ ~r)")] THEN
    REWRITE_TAC [DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
    (EQ_TAC THENL
      [DISCH_THEN (MP_TAC o SPEC
        (← q r"(lambda i. (max ((a:real^N)$i) ((c:real^N)$i) +
                   min ((b:real^N)$i) ((d:real^N)$i)) / &2):real^N")) THEN
       MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
       DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
       ASM_SIMP_TAC [LAMBDA_BETA] THEN REAL_ARITH_TAC,
       DISCH_THEN (fun th => GEN_TAC THEN MP_TAC th) THEN
       MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN SIMP_TAC [] THEN
       REAL_ARITH_TAC]))

  let ENDS_IN_INTERVAL ← prove
   r"(!a b. a IN interval[a,b] <=> ~(interval[a,b] = {})) /\
   (!a b. b IN interval[a,b] <=> ~(interval[a,b] = {})) /\
   (!a b. ~(a IN interval(a,b))) /\
   (!a b. ~(b IN interval(a,b)))"
   (REWRITE_TAC [IN_INTERVAL, INTERVAL_NE_EMPTY] THEN
    REWRITE_TAC [REAL_LE_REFL, REAL_LT_REFL] THEN
    MESON_TAC [DIMINDEX_GE_1, LE_REFL])

  let ENDS_IN_UNIT_INTERVAL ← prove
   r"vec 0 IN interval[vec 0,vec 1] /\
   vec 1 IN interval[vec 0,vec 1] /\
   ~(vec 0 IN interval(vec 0,vec 1)) /\
   ~(vec 1 IN interval(vec 0,vec 1))"
   (REWRITE_TAC [ENDS_IN_INTERVAL, INTERVAL_NE_EMPTY, VEC_COMPONENT] THEN
    REWRITE_TAC [REAL_POS])

  let INTER_INTERVAL ← prove
   r"interval[a,b] INTER interval[c,d] =
        interval[(lambda i. max (a$i) (c$i)),(lambda i. min (b$i) (d$i))]"
   (REWRITE_TAC [EXTENSION, IN_INTER, IN_INTERVAL] THEN
    SIMP_TAC [LAMBDA_BETA, REAL_MAX_LE, REAL_LE_MIN] THEN MESON_TAC [])

  let INTERVAL_OPEN_SUBSET_CLOSED ← prove
   r"!a b. interval(a,b) SUBSET interval[a,b]"
   (REWRITE_TAC [SUBSET, IN_INTERVAL] THEN MESON_TAC [REAL_LT_IMP_LE])

  return { open_interval, closed_interval, interval, IN_INTERVAL, IN_INTERVAL_REFLECT,
           REFLECT_INTERVAL, INTERVAL_EQ_EMPTY, INTERVAL_NE_EMPTY, SUBSET_INTERVAL_IMP,
           INTERVAL_SING, SUBSET_INTERVAL, DISJOINT_INTERVAL, ENDS_IN_INTERVAL,
           ENDS_IN_UNIT_INTERVAL, INTER_INTERVAL, INTERVAL_OPEN_SUBSET_CLOSED }

/- ------------------------------------------------------------------------- -/
/- General "one way" lemma for properties preserved by injective map; the   -/
/- inference rule to apply it; storage of invariance theorems; scaling;      -/
/- the basic set equivalences.  (vectors.ml 10250-10475)                     -/
/- ------------------------------------------------------------------------- -/

structure Invariance1 where
  WLOG_LINEAR_INJECTIVE_IMAGE_2 : thm
  WLOG_LINEAR_INJECTIVE_IMAGE_2_ALT : thm
  WLOG_LINEAR_INJECTIVE_IMAGE : thm
  WLOG_LINEAR_INJECTIVE_IMAGE_ALT : thm
  LINEAR_INVARIANT_RULE : thm → ExceptT String IO thm
  SUBSPACE_LINEAR_IMAGE_EQ : thm
  invariant_under_linear : IO.Ref (List thm)
  invariant_under_translation : IO.Ref (List thm)
  scaling_theorems : IO.Ref (List thm)
  COUNTABLE_UNION_OF_BIJECTIVE_IMAGE : thm
  COUNTABLE_INTERSECTION_OF_BIJECTIVE_IMAGE : thm
  AFFINITY_SCALING_TRANSLATION : thm
  LINEAR_SCALING : thm
  INJECTIVE_SCALING : thm
  SURJECTIVE_SCALING : thm
  SCALING_INVARIANT : thm → ExceptT String IO thm
  add_scaling_theorems : List thm → ExceptT String IO Unit
  add_linear_invariants : List thm → ExceptT String IO Unit
  add_translation_invariants : List thm → ExceptT String IO Unit
  deriving Nonempty

@[nospecialize]
def setupInvariance1 [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BNorm1 : Norm1) (BLinear : Linear) (BSubspace : Subspace) (BLinEq : LinEq)
    (BIso : Iso) : ExceptT String IO Invariance1 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, SET_TAC, .. } := D
  let { ARITH, CARD_IMAGE_INJ, CONJ_SYM, EQ_IMP, EXISTS_REFL, FINITE_IMAGE_INJ_EQ, FORALL_IN_IMAGE,
        .. } := D.core1
  let { FUN_EQ_THM, HAS_SIZE, IMAGE_ID, IMAGE_UNIONS, IMAGE_o, IMP_IMP, IN, INFINITE,
        INJECTIVE_IMAGE, INTERSECTION_OF, INTERS_IMAGE, I_THM, .. } := D.core2
  let { REAL_LT_IMP_NZ, .. } := D.core3
  let { RIGHT_IMP_FORALL_THM, .. } := D.core4
  let { UNIONS_IMAGE, UNION_OF, o_DEF, o_THM, .. } := D.core5
  let { COUNTABLE_IMAGE, COUNTABLE_IMAGE_INJ_EQ, .. } := D.lib
  let { VECTOR_ADD_SYM, VECTOR_ARITH, VECTOR_ARITH_TAC, VEC_EQ, .. } := BVectorArith
  let { VECTOR_MUL_LCANCEL, .. } := BNorm1
  let { linear, .. } := BLinear
  let { SUBSPACE_LINEAR_IMAGE, .. } := BSubspace
  let { LINEAR_INJECTIVE_LEFT_INVERSE, .. } := BLinEq
  let { LINEAR_SURJECTIVE_IFF_INJECTIVE, .. } := BIso
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)

  let WLOG_LINEAR_INJECTIVE_IMAGE_2 ← prove
   r"!P Q. (!f s. P s /\ linear f ==> Q(IMAGE f s)) /\
         (!g t. Q t /\ linear g ==> P(IMAGE g t))
         ==> !f:real^M->real^N.
                linear f /\ (!x y. f x = f y ==> x = y)
                ==> !s. Q(IMAGE f s) <=> P s"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC [] THEN DISCH_TAC THEN
    MP_TAC (← ISPEC (← q r"f:real^M->real^N") LINEAR_INJECTIVE_LEFT_INVERSE) THEN
    ASM_REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"g:real^N->real^M") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
     [← q r"g:real^N->real^M", ← q r"IMAGE (f:real^M->real^N) s"]) THEN
    ASM_REWRITE_TAC [← GSYM IMAGE_o, o_DEF, IMAGE_ID])

  let WLOG_LINEAR_INJECTIVE_IMAGE_2_ALT ← prove
   r"!P Q f s. (!h u. P u /\ linear h ==> Q(IMAGE h u)) /\
             (!g t. Q t /\ linear g ==> P(IMAGE g t)) /\
             linear f /\ (!x y. f x = f y ==> x = y)
             ==> (Q(IMAGE f s) <=> P s)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC (← REWRITE_RULE [RIGHT_IMP_FORALL_THM, IMP_IMP]
       WLOG_LINEAR_INJECTIVE_IMAGE_2) THEN
    ASM_REWRITE_TAC [])

  let WLOG_LINEAR_INJECTIVE_IMAGE ← prove
   r"!P. (!f s. P s /\ linear f ==> P(IMAGE f s))
       ==> !f:real^N->real^N. linear f /\ (!x y. f x = f y ==> x = y)
                              ==> !s. P(IMAGE f s) <=> P s"
   (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC WLOG_LINEAR_INJECTIVE_IMAGE_2 THEN
    ASM_REWRITE_TAC [])

  let WLOG_LINEAR_INJECTIVE_IMAGE_ALT ← prove
   r"!P f s. (!g t. P t /\ linear g ==> P(IMAGE g t)) /\
           linear f /\ (!x y. f x = f y ==> x = y)
           ==> (P(IMAGE f s) <=> P s)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC (← REWRITE_RULE [RIGHT_IMP_FORALL_THM, IMP_IMP]
       WLOG_LINEAR_INJECTIVE_IMAGE) THEN
    ASM_REWRITE_TAC [])

  let LINEAR_INVARIANT_RULE (th : thm) : ExceptT String IO thm := do
    let (vs, _) := HolCore.Basics.strip_forall (concl th)
    let (f, _s) ← match vs with
      | [f, s] => pure (f, s)
      | _ => throw "LINEAR_INVARIANT_RULE: match failure"
    let (rm, rn) ← liftExcept (HolCore.Basics.dest_fun_ty (type_of f))
    let m ← match (← liftExcept (dest_type rm)).2.getLast? with
      | some m => pure m
      | none => throw "last"
    let n ← match (← liftExcept (dest_type rn)).2.getLast? with
      | some n => pure n
      | none => throw "last"
    let th' ← HolLight.INST_TYPE [(m, n), (n, m)] th
    let th0 ← CONJ th th'
    let th1 ← tryCatch (MATCH_MP WLOG_LINEAR_INJECTIVE_IMAGE_2 th0)
      (fun _ => do
        MATCH_MP WLOG_LINEAR_INJECTIVE_IMAGE_2
          (← GEN_REWRITE_RULE (BINOP_CONV o ONCE_DEPTH_CONV) [CONJ_SYM] th0))
    GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_FORALL_THM] th1

  let SUBSPACE_LINEAR_IMAGE_EQ ← prove
   r"!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (subspace (IMAGE f s) <=> subspace s)"
   (MATCH_ACCEPT_TAC (← LINEAR_INVARIANT_RULE SUBSPACE_LINEAR_IMAGE))

  let invariant_under_linear ← IO.mkRef ([] : List thm)

  let invariant_under_translation ← IO.mkRef ([] : List thm)

  let scaling_theorems ← IO.mkRef ([] : List thm)

  let COUNTABLE_UNION_OF_BIJECTIVE_IMAGE ← prove
   r"!(f:A->B) P P'.
        (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y) /\
        (!s. P' (IMAGE f s) <=> P s)
        ==> (!s. (COUNTABLE UNION_OF P') (IMAGE f s) <=>
                 (COUNTABLE UNION_OF P) s)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [UNION_OF] THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"u:(B->bool)->bool") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"IMAGE (\s. {x | (f:A->B) x IN s}) u") THEN
      ASM_SIMP_TAC [UNIONS_IMAGE, COUNTABLE_IMAGE, FORALL_IN_IMAGE] THEN
      CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      GEN_TAC THEN DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
      FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [← GSYM th])) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC [],
      DISCH_THEN (X_CHOOSE_THEN (← q r"u:(A->bool)->bool") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"IMAGE (IMAGE (f:A->B)) u") THEN
      ASM_SIMP_TAC [UNIONS_IMAGE, COUNTABLE_IMAGE, FORALL_IN_IMAGE] THEN
      ASM SET_TAC []])

  let COUNTABLE_INTERSECTION_OF_BIJECTIVE_IMAGE ← prove
   r"!(f:A->B) P P'.
        (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y) /\
        (!s. P' (IMAGE f s) <=> P s)
        ==> (!s. (COUNTABLE INTERSECTION_OF P') (IMAGE f s) <=>
                 (COUNTABLE INTERSECTION_OF P) s)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [INTERSECTION_OF] THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN (← q r"u:(B->bool)->bool") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"IMAGE (\s. {x | (f:A->B) x IN s}) u") THEN
      ASM_SIMP_TAC [INTERS_IMAGE, COUNTABLE_IMAGE, FORALL_IN_IMAGE] THEN
      CONJ_TAC THENL [ALL_TAC, ASM SET_TAC []] THEN
      GEN_TAC THEN DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
      FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [← GSYM th])) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC [],
      DISCH_THEN (X_CHOOSE_THEN (← q r"u:(A->bool)->bool") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"IMAGE (IMAGE (f:A->B)) u") THEN
      ASM_SIMP_TAC [INTERS_IMAGE, COUNTABLE_IMAGE, FORALL_IN_IMAGE] THEN
      ASM SET_TAC []])

  let AFFINITY_SCALING_TRANSLATION ← prove
   r"!m c:real^N. (\x. m % x + c) = (\x. c + x) o (\x. m % x)"
   (REWRITE_TAC [o_DEF, VECTOR_ADD_SYM])

  let LINEAR_SCALING ← prove
   r"!c. linear(\x:real^N. c % x)"
   (REWRITE_TAC [linear] THEN VECTOR_ARITH_TAC)

  let INJECTIVE_SCALING ← prove
   r"!c. (!x y:real^N. c % x = c % y ==> x = y) <=> ~(c = &0)"
   (GEN_TAC THEN REWRITE_TAC [VECTOR_MUL_LCANCEL] THEN
    ASM_CASES_TAC (← q r"c:real = &0") THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o SPECL [← q r"vec 0:real^N", ← q r"vec 1:real^N"]) THEN
    REWRITE_TAC [VEC_EQ, ARITH])

  let SURJECTIVE_SCALING ← prove
   r"!c. (!y:real^N. ?x. c % x = y) <=> ~(c = &0)"
   (ASM_SIMP_TAC [LINEAR_SURJECTIVE_IFF_INJECTIVE, LINEAR_SCALING] THEN
    REWRITE_TAC [INJECTIVE_SCALING])

  let SCALING_INVARIANT ← do
    let pths := CONJUNCTS (← UNDISCH (← prove
     r"&0 < c
     ==> linear(\x:real^N. c % x) /\
         (!x y:real^N. c % x = c % y ==> x = y) /\
         (!y:real^N. ?x. c % x = y)"
     (SIMP_TAC [REAL_LT_IMP_NZ, LINEAR_SCALING,
                INJECTIVE_SCALING, SURJECTIVE_SCALING])))
    let sc_tm ← q r"\x:real^N. c % x"
    let sa_tm ← q r"&0:real < c"
    let c_tm ← q r"c:real"
    pure (fun (th : thm) => (do
      let ith ← BETA_RULE (← ISPEC sc_tm th)
      let (avs, bod) := HolCore.Basics.strip_forall (concl ith)
      let cjs := HolCore.Basics.conjuncts (← liftExcept (lhand bod))
      let cths ← cjs.mapM (fun t =>
        liftExcept (HolCore.Lib.find (fun th => aconv (concl th) t) pths))
      let oth ← MP (← SPECL avs ith) (← end_itlistIO CONJ cths)
      GEN c_tm (← DISCH sa_tm (← GENL avs oth)) : ExceptT String IO thm))

  let add_scaling_theorems (thl : List thm) : ExceptT String IO Unit :=
    scaling_theorems.modify (fun l => l ++ thl)

  let add_linear_invariants (thl : List thm) : ExceptT String IO Unit := do
    let _ ← mapfilterIO (fun th => do add_scaling_theorems [← SCALING_INVARIANT th]) thl
    invariant_under_linear.modify (fun l => l ++ thl)

  let add_translation_invariants (thl : List thm) : ExceptT String IO Unit :=
    invariant_under_translation.modify (fun l => l ++ thl)

  -- (vectors.ml 10389-10461) the basic set equivalences
  do
    let th_sets ← prove
     r"!f. (!x y. f x = f y ==> x = y)
       ==> (if p then f x else f y) = f(if p then x else y) /\
           (if p then IMAGE f s else IMAGE f t) =
           IMAGE f (if p then s else t) /\
           (f x) INSERT (IMAGE f s) = IMAGE f (x INSERT s) /\
           (IMAGE f s) DELETE (f x) = IMAGE f (s DELETE x) /\
           (IMAGE f s) INTER (IMAGE f t) = IMAGE f (s INTER t) /\
           (IMAGE f s) UNION (IMAGE f t) = IMAGE f (s UNION t) /\
           UNIONS(IMAGE (IMAGE f) u) = IMAGE f (UNIONS u) /\
           (IMAGE f s) DIFF (IMAGE f t) = IMAGE f (s DIFF t) /\
           (IMAGE f s (f x) <=> s x) /\
           ((f x) IN (IMAGE f s) <=> x IN s) /\
           ((f o xs) (n:num) = f(xs n)) /\
           ((f o pt) (tt:real^1) = f(pt tt)) /\
           (IMAGE (f o g) k = IMAGE f (IMAGE g k)) /\
           (DISJOINT (IMAGE f s) (IMAGE f t) <=> DISJOINT s t) /\
           ((IMAGE f s) SUBSET (IMAGE f t) <=> s SUBSET t) /\
           ((IMAGE f s) PSUBSET (IMAGE f t) <=> s PSUBSET t) /\
           (IMAGE f s = IMAGE f t <=> s = t) /\
           ((IMAGE f s) HAS_SIZE n <=> s HAS_SIZE n) /\
           (FINITE(IMAGE f s) <=> FINITE s) /\
           (INFINITE(IMAGE f s) <=> INFINITE s) /\
           (COUNTABLE(IMAGE f s) <=> COUNTABLE s)"
     (REPEAT GEN_TAC THEN DISCH_TAC THEN
      REWRITE_TAC [IMAGE_UNIONS, IMAGE_o] THEN
      REWRITE_TAC [o_THM, ← MESON [IN] (← q r"IMAGE f s y <=> y IN IMAGE f s")] THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [MESON_TAC [], ALL_TAC]) THEN
      REWRITE_TAC [INFINITE, ← TAUT (← q r"(~p <=> ~q) <=> (p <=> q)")] THEN
      REPLICATE_TAC 11 (CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC]) THEN
      REWRITE_TAC [HAS_SIZE] THEN
      ASM_MESON_TAC [COUNTABLE_IMAGE_INJ_EQ,
                     FINITE_IMAGE_INJ_EQ, CARD_IMAGE_INJ])
    let f ← q r"f:real^M->real^N"
    let imf ← q r"IMAGE (f:real^M->real^N)"
    let a ← q r"a:real^N"
    let ima ← q r"IMAGE (\x:real^N. a + x)"
    let vth ← va r"!x y. a + x:real^N = a + y ==> x = y"
    let th1 ← UNDISCH (← ISPEC f th_sets)
    let th1' ← UNDISCH
     (← GEN_REWRITE_RULE LAND_CONV [INJECTIVE_IMAGE] (← ISPEC imf th_sets))
    let th2 ← MATCH_MP th_sets vth
    let th2' ← MATCH_MP
      (← BETA_RULE (← GEN_REWRITE_RULE LAND_CONV [INJECTIVE_IMAGE] (← ISPEC ima th_sets)))
      vth
    let fn (a : term) (th : thm) : ExceptT String IO thm :=
      GENL (a :: subtract (frees (concl th)) [a]) th
    add_linear_invariants
      (← (CONJUNCTS th1 ++ CONJUNCTS th1').mapM (fun th => do fn f (← DISCH_ALL th)))
    add_translation_invariants (← (CONJUNCTS th2 ++ CONJUNCTS th2').mapM (fn a))

  -- (vectors.ml 10463-10475)
  do
    let th_set ← prove
     r"!f:A->B s. (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
              ==> INTERS (IMAGE (IMAGE f) s) = IMAGE f (INTERS s)"
     (REWRITE_TAC [INTERS_IMAGE] THEN SET_TAC [])
    let th_vec ← prove
     r"!a:real^N s.
    INTERS (IMAGE (IMAGE (\x. a + x)) s) = IMAGE (\x. a + x) (INTERS s)"
     (REPEAT GEN_TAC THEN MATCH_MP_TAC th_set THEN
      REWRITE_TAC [← va r"a + x:real^N = a + y <=> x = y"] THEN
      REWRITE_TAC [← va r"a + x:real^N = y <=> x = y - a", EXISTS_REFL])
    add_linear_invariants [th_set]
    add_translation_invariants [th_vec]

  return { WLOG_LINEAR_INJECTIVE_IMAGE_2, WLOG_LINEAR_INJECTIVE_IMAGE_2_ALT,
           WLOG_LINEAR_INJECTIVE_IMAGE, WLOG_LINEAR_INJECTIVE_IMAGE_ALT,
           LINEAR_INVARIANT_RULE, SUBSPACE_LINEAR_IMAGE_EQ, invariant_under_linear,
           invariant_under_translation, scaling_theorems, COUNTABLE_UNION_OF_BIJECTIVE_IMAGE,
           COUNTABLE_INTERSECTION_OF_BIJECTIVE_IMAGE, AFFINITY_SCALING_TRANSLATION,
           LINEAR_SCALING, INJECTIVE_SCALING, SURJECTIVE_SCALING, SCALING_INVARIANT,
           add_scaling_theorems, add_linear_invariants, add_translation_invariants }

/- ------------------------------------------------------------------------- -/
/- Now add arithmetical equivalences.  (vectors.ml 10505-10617)              -/
/- ------------------------------------------------------------------------- -/

structure Invariance2 where
  SAME_NORM_SAME_DOT : thm
  PRESERVES_NORM_PRESERVES_DOT : thm
  PRESEVES_NORM_PRESERVES_DIST : thm
  PRESERVES_NORM_INJECTIVE : thm
  ORTHOGONAL_LINEAR_IMAGE_EQ : thm
  NORMAL_MATRIX_IFF_SAME_NORM_TRANSP : thm
  NORMAL_MATRIX_IFF_SAME_DOT_TRANSP : thm
  NORMAL_MATRIX_KERNEL_TRANSP_EXPLICIT : thm
  NORMAL_MATRIX_KERNEL_TRANSP : thm
  deriving Inhabited

@[nospecialize]
def setupInvariance2 [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BDotProps : DotProps) (BNorm1 : Norm1) (BNorm2 : Norm2) (BNormArith : NormArithB)
    (BOrth : Orth) (BLinear : Linear) (BMatrix : Matrix) (BMatArith : MatArith)
    (BMatProps : MatProps) (BInvertible : Invertible) (BSpan1 : Span1)
    (BMatInv2 : MatInv2) (BBetween : Between) (BInvariance1 : Invariance1) :
    ExceptT String IO Invariance2 := do
  -- @@SCOPE BEGIN
  let { MESON, MESON_TAC, REAL_ARITH_TAC, .. } := D
  let { AND_FORALL_THM, ETA_AX, EXTENSION, .. } := D.core1
  let { IN_ELIM_THM, IN_IMAGE, .. } := D.core2
  let { REAL_SUB_0, .. } := D.core4
  let { VECTOR_ARITH, .. } := BVectorArith
  let { DOT_LADD, DOT_LSUB, DOT_RADD, DOT_SYM, FORALL_DOT_EQ_0, .. } := BDotProps
  let { NORM_EQ_0, dist, .. } := BNorm1
  let { NORM_EQ, .. } := BNorm2
  let { NORM_ARITH, .. } := BNormArith
  let { orthogonal, .. } := BOrth
  let { LINEAR_ADD, LINEAR_CMUL, LINEAR_ID, LINEAR_INJECTIVE_0, LINEAR_NEG, LINEAR_SUB,
        .. } := BLinear
  let { normal_matrix, .. } := BMatrix
  let { MATRIX_SUB_EQ, MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_SUB_RDISTRIB, .. } := BMatArith
  let { MATRIX_EQ_0, .. } := BMatProps
  let { DOT_MATRIX_TRANSP_LMUL, DOT_MATRIX_TRANSP_RMUL, MATRIX_VECTOR_MUL_LINEAR,
        .. } := BInvertible
  let { DEPENDENT_LINEAR_IMAGE_EQ, INDEPENDENT_LINEAR_IMAGE_EQ, SPAN_LINEAR_IMAGE,
        .. } := BSpan1
  let { DIM_INJECTIVE_LINEAR_IMAGE, .. } := BMatInv2
  let { MIDPOINT_LINEAR_IMAGE, between, midpoint, .. } := BBetween
  let { SUBSPACE_LINEAR_IMAGE_EQ, add_linear_invariants, add_translation_invariants,
        .. } := BInvariance1
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)
  let na (s : String) : ExceptT String IO thm := do NORM_ARITH (← q s)

  let SAME_NORM_SAME_DOT ← prove
   r"!f:real^M->real^N g:real^M->real^P x y.
     linear f /\ linear g /\ (!x. norm(f x) = norm(g x))
     ==> (f x) dot (f y) = (g x) dot (g y)"
   (REWRITE_TAC [NORM_EQ] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"x + y:real^M")) THEN
    REPEAT (FIRST_X_ASSUM (fun th => tactic_of do
      pure (REWRITE_TAC [← MATCH_MP LINEAR_ADD th]))) THEN
    ASM_REWRITE_TAC [DOT_LADD, DOT_RADD] THEN
    REWRITE_TAC [DOT_SYM] THEN REAL_ARITH_TAC)

  let PRESERVES_NORM_PRESERVES_DOT ← prove
   r"!f:real^M->real^N x y.
     linear f /\ (!x. norm(f x) = norm x)
     ==> (f x) dot (f y) = x dot y"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:real^M->real^N", ← q r"\x:real^M. x"]
          SAME_NORM_SAME_DOT) THEN
    ASM_SIMP_TAC [LINEAR_ID])

  let PRESEVES_NORM_PRESERVES_DIST ← prove
   r"!f:real^M->real^N.
        linear f /\ (!x. norm(f x) = norm x)
        ==> !x y. dist(f x,f y) = dist(x,y)"
   (REWRITE_TAC [dist] THEN MESON_TAC [LINEAR_SUB])

  let PRESERVES_NORM_INJECTIVE ← prove
   r"!f:real^M->real^N.
     linear f /\ (!x. norm(f x) = norm x)
     ==> !x y. f x = f y ==> x = y"
   (SIMP_TAC [LINEAR_INJECTIVE_0, ← GSYM NORM_EQ_0])

  let ORTHOGONAL_LINEAR_IMAGE_EQ ← prove
   r"!f:real^M->real^N x y.
     linear f /\ (!x. norm(f x) = norm x)
     ==> (orthogonal (f x) (f y) <=> orthogonal x y)"
   (SIMP_TAC [orthogonal, PRESERVES_NORM_PRESERVES_DOT])

  let (NORMAL_MATRIX_IFF_SAME_NORM_TRANSP, NORMAL_MATRIX_IFF_SAME_DOT_TRANSP) ←
    CONJ_PAIR (← prove
   r"(!A:real^N^N.
         normal_matrix A <=>
         !x. norm(transp A ** x) = norm(A ** x)) /\
   (!A:real^N^N.
         normal_matrix A <=>
         !x y. (transp A ** x) dot (transp A ** y) = (A ** x) dot (A ** y))"
   (REWRITE_TAC [normal_matrix, AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC
     (← TAUT (← q r"(q <=> r) /\ (p <=> r) ==> (p <=> q) /\ (p <=> r)")) THEN
    CONJ_TAC THENL
     [EQ_TAC THENL [ALL_TAC, SIMP_TAC [NORM_EQ]] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SAME_NORM_SAME_DOT THEN
      ASM_REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR] THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM ETA_AX] THEN
      REWRITE_TAC [MATRIX_VECTOR_MUL_LINEAR],
      REWRITE_TAC [DOT_MATRIX_TRANSP_RMUL] THEN
      GEN_REWRITE_TAC (RAND_CONV o funpow 2 BINDER_CONV o RAND_CONV)
       [← GSYM DOT_MATRIX_TRANSP_LMUL] THEN
      ONCE_REWRITE_TAC [← GSYM REAL_SUB_0] THEN REWRITE_TAC [← GSYM DOT_LSUB] THEN
      REWRITE_TAC [FORALL_DOT_EQ_0, MATRIX_VECTOR_MUL_ASSOC] THEN
      REWRITE_TAC [← GSYM MATRIX_EQ_0, ← GSYM MATRIX_VECTOR_MUL_SUB_RDISTRIB] THEN
      REWRITE_TAC [MATRIX_SUB_EQ] THEN MESON_TAC []]))

  let NORMAL_MATRIX_KERNEL_TRANSP_EXPLICIT ← prove
   r"!A x:real^N.
        normal_matrix A
        ==> (transp A ** x = vec 0 <=> A ** x = vec 0)"
   (REWRITE_TAC [← GSYM NORM_EQ_0] THEN
    MESON_TAC [NORMAL_MATRIX_IFF_SAME_NORM_TRANSP])

  let NORMAL_MATRIX_KERNEL_TRANSP ← prove
   r"!A:real^N^N.
        normal_matrix A
        ==> {x | transp A ** x = vec 0} = {x | A ** x = vec 0}"
   (SIMP_TAC [EXTENSION, IN_ELIM_THM, NORMAL_MATRIX_KERNEL_TRANSP_EXPLICIT])

  add_linear_invariants
   [← GSYM LINEAR_ADD,
    ← GSYM LINEAR_CMUL,
    ← GSYM LINEAR_SUB,
    ← GSYM LINEAR_NEG,
    MIDPOINT_LINEAR_IMAGE,
    ← MESON [] (← q r"!f:real^M->real^N x.
                (!x. norm(f x) = norm x) ==> norm(f x) = norm x"),
    PRESERVES_NORM_PRESERVES_DOT,
    ← MESON [dist, LINEAR_SUB] (← q
      r"!f:real^M->real^N x y.
        linear f /\ (!x. norm(f x) = norm x)
        ==> dist(f x,f y) = dist(x,y)"),
    ← MESON [] (← q r"!f:real^M->real^N x y.
                (!x y. f x = f y ==> x = y) ==> (f x = f y <=> x = y)"),
    SUBSPACE_LINEAR_IMAGE_EQ,
    ORTHOGONAL_LINEAR_IMAGE_EQ,
    SPAN_LINEAR_IMAGE,
    DEPENDENT_LINEAR_IMAGE_EQ,
    INDEPENDENT_LINEAR_IMAGE_EQ,
    DIM_INJECTIVE_LINEAR_IMAGE]

  add_translation_invariants
   [← va r"!a x y. a + x:real^N = a + y <=> x = y",
    ← na r"!a x y. dist(a + x,a + y) = dist(x,y)",
    ← va r"!a x y. &1 / &2 % ((a + x) + (a + y)) = a + &1 / &2 % (x + y)",
    ← va r"!a x y. inv(&2) % ((a + x) + (a + y)) = a + inv(&2) % (x + y)",
    ← va r"!a x y. (a + x) - (a + y):real^N = x - y",
    ← EQT_ELIM (← (REWRITE_CONV [midpoint] THENC
                     (fun t => (do EQT_INTRO (← NORM_ARITH t) : ExceptT String IO thm).run))
                 (← q r"!a x y. midpoint(a + x,a + y) = a + midpoint(x,y)")),
    ← EQT_ELIM (← (REWRITE_CONV [between] THENC
                     (fun t => (do EQT_INTRO (← NORM_ARITH t) : ExceptT String IO thm).run))
                 (← q r"!a x y z. between (a + x) (a + y,a + z) <=> between x (y,z)"))]

  -- (vectors.ml 10612-10617)
  do
    let th ← prove
     r"!a s b c:real^N. (a + b) + c IN IMAGE (\x. a + x) s <=> (b + c) IN s"
     (REWRITE_TAC [IN_IMAGE, ← va
       r"(a + b) + c:real^N = a + x <=> x = b + c"] THEN
      MESON_TAC [])
    add_translation_invariants [th]

  return { SAME_NORM_SAME_DOT, PRESERVES_NORM_PRESERVES_DOT, PRESEVES_NORM_PRESERVES_DIST,
           PRESERVES_NORM_INJECTIVE, ORTHOGONAL_LINEAR_IMAGE_EQ,
           NORMAL_MATRIX_IFF_SAME_NORM_TRANSP, NORMAL_MATRIX_IFF_SAME_DOT_TRANSP,
           NORMAL_MATRIX_KERNEL_TRANSP_EXPLICIT, NORMAL_MATRIX_KERNEL_TRANSP }

/- ------------------------------------------------------------------------- -/
/- The recursive `conv` of `PARTIAL_EXPAND_QUANTS_CONV` (vectors.ml 10791-  -/
/- 10795), over the two rewrite conversions built from the theorem.          -/
/- ------------------------------------------------------------------------- -/

partial def expandQuantsGo [HolBase] (conv1' conv2 : ioconv) : ioconv := fun tm =>
  ((conv1' THENC BINDER_CONV (expandQuantsGo conv1' conv2)) ORELSEC
   (conv2 THENC
    RAND_CONV (RAND_CONV (ABS_CONV (BINDER_CONV (LAND_CONV (expandQuantsGo conv1' conv2)))))) ORELSEC
   SUB_CONV (expandQuantsGo conv1' conv2)) tm

/- ------------------------------------------------------------------------- -/
/- A few invariants for lists; scaling theorems that don't come from        -/
/- invariance theorems; quantifier mappings from surjectivity; expansion of  -/
/- quantifiers and sets.  (vectors.ml 10623-10797)                           -/
/- ------------------------------------------------------------------------- -/

structure Invariance3 where
  MEM_TRANSLATION : thm
  MEM_LINEAR_IMAGE : thm
  QUANTIFY_SURJECTION_THM : thm
  QUANTIFY_SURJECTION_HIGHER_THM : thm
  PARTIAL_EXPAND_QUANTS_CONV : List String → thm → ExceptT String IO ioconv
  EXPAND_QUANTS_CONV : thm → ExceptT String IO ioconv
  deriving Inhabited

@[nospecialize]
def setupInvariance3 [HolBase] (D : VectorsDeps) (BVectorArith : VectorArith)
    (BDotProps : DotProps) (BNorm1 : Norm1) (BMetric : Metric) (BOrth : Orth)
    (BInvariance1 : Invariance1) : ExceptT String IO Invariance3 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON, MESON_TAC, REAL_ARITH, REAL_ARITH_TAC, REAL_FIELD, SET_TAC,
        .. } := D
  let { FUN_EQ_THM, .. } := D.core2
  let { REAL_EQ_LCANCEL_IMP, REAL_LE_LMUL_EQ, REAL_LT_IMP_NZ, REAL_LT_LMUL_EQ, .. } := D.core3
  let { REAL_POW_LT, REAL_POW_MUL, SKOLEM_THM, .. } := D.core4
  let { LENGTH_MAP, MAP, MAP_APPEND, MAP_REVERSE, MEM_MAP, SURJECTIVE_EXISTS_THM,
        SURJECTIVE_FORALL_THM, SURJECTIVE_IMAGE, SURJECTIVE_IMAGE_THM, SURJECTIVE_MAP,
        SURJECTIVE_RIGHT_INVERSE, o_THM, real_ge, real_gt, .. } := D.core5
  let { VECTOR_ARITH, .. } := BVectorArith
  let { DOT_LMUL, DOT_RMUL, .. } := BDotProps
  let { NORM_MUL, .. } := BNorm1
  let { DIST_MUL, .. } := BMetric
  let { orthogonal, .. } := BOrth
  let { add_linear_invariants, add_scaling_theorems, add_translation_invariants,
        .. } := BInvariance1
  -- @@SCOPE END
  let va (s : String) : ExceptT String IO thm := do VECTOR_ARITH (← q s)
  let ra (s : String) : ExceptT String IO thm := do REAL_ARITH (← q s)

  let MEM_TRANSLATION ← prove
   r"!a:real^N x l. MEM (a + x) (MAP (\x. a + x) l) <=> MEM x l"
   (REWRITE_TAC [MEM_MAP, ← va r"a + x:real^N = a + y <=> x = y"] THEN
    MESON_TAC [])

  add_translation_invariants [MEM_TRANSLATION]

  let MEM_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N x l.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (MEM (f x) (MAP f l) <=> MEM x l)"
   (REWRITE_TAC [MEM_MAP] THEN MESON_TAC [])

  add_linear_invariants [MEM_LINEAR_IMAGE]

  do
    let LENGTH_TRANSLATION ← prove
     r"!a:real^N l. LENGTH(MAP (\x. a + x) l) = LENGTH l"
     (REWRITE_TAC [LENGTH_MAP])
    add_translation_invariants [LENGTH_TRANSLATION]

  do
    let LENGTH_LINEAR_IMAGE ← prove
     r"!f:real^M->real^N l. linear f ==> LENGTH(MAP f l) = LENGTH l"
     (REWRITE_TAC [LENGTH_MAP])
    add_linear_invariants [LENGTH_LINEAR_IMAGE]

  do
    let CONS_TRANSLATION ← prove
     r"!a:real^N h t.
     CONS ((\x. a + x) h) (MAP (\x. a + x) t) = MAP (\x. a + x) (CONS h t)"
     (REWRITE_TAC [MAP])
    add_translation_invariants [CONS_TRANSLATION]

  do
    let CONS_LINEAR_IMAGE ← prove
     r"!f:real^M->real^N h t.
     linear f ==> CONS (f h) (MAP f t) = MAP f (CONS h t)"
     (REWRITE_TAC [MAP])
    add_linear_invariants [CONS_LINEAR_IMAGE]

  do
    let APPEND_TRANSLATION ← prove
     r"!a:real^N l1 l2.
     APPEND (MAP (\x. a + x) l1) (MAP (\x. a + x) l2) =
     MAP (\x. a + x) (APPEND l1 l2)"
     (REWRITE_TAC [MAP_APPEND])
    add_translation_invariants [APPEND_TRANSLATION]

  do
    let APPEND_LINEAR_IMAGE ← prove
     r"!f:real^M->real^N l1 l2.
     linear f ==> APPEND (MAP f l1) (MAP f l2) = MAP f (APPEND l1 l2)"
     (REWRITE_TAC [MAP_APPEND])
    add_linear_invariants [APPEND_LINEAR_IMAGE]

  do
    let REVERSE_TRANSLATION ← prove
     r"!a:real^N l. REVERSE(MAP (\x. a + x) l) = MAP (\x. a + x) (REVERSE l)"
     (REWRITE_TAC [MAP_REVERSE])
    add_translation_invariants [REVERSE_TRANSLATION]

  do
    let REVERSE_LINEAR_IMAGE ← prove
     r"!f:real^M->real^N l. linear f ==> REVERSE(MAP f l) = MAP f (REVERSE l)"
     (REWRITE_TAC [MAP_REVERSE])
    add_linear_invariants [REVERSE_LINEAR_IMAGE]

  do
    let DOT_SCALING ← prove
     r"!c. &0 < c ==> !x y. (c % x) dot (c % y) = c pow 2 * (x dot y)"
     (REWRITE_TAC [DOT_LMUL, DOT_RMUL] THEN REAL_ARITH_TAC)
    add_scaling_theorems [DOT_SCALING]

  do
    let DIST_SCALING ← prove
     r"!c. &0 < c ==> !x y. dist(c % x,c % y) = c * dist(x,y)"
     (SIMP_TAC [DIST_MUL, ← ra r"&0 < c ==> abs c = c"])
    add_scaling_theorems [DIST_SCALING]

  do
    let ORTHOGONAL_SCALING ← prove
     r"!c. &0 < c ==> !x y. orthogonal (c % x) (c % y) <=> orthogonal x y"
     (REWRITE_TAC [orthogonal, DOT_LMUL, DOT_RMUL] THEN CONV_TAC (fun t => REAL_FIELD t))
    add_scaling_theorems [ORTHOGONAL_SCALING]

  do
    let NORM_SCALING ← prove
     r"!c. &0 < c ==> !x. norm(c % x) = c * norm x"
     (SIMP_TAC [NORM_MUL, ← ra r"&0 < c ==> abs c = c"])
    add_scaling_theorems [NORM_SCALING]

  add_scaling_theorems
    [← ra r"!c. &0 < c ==> !a b. a * c * b = c * a * b",
     ← ra r"!c. &0 < c ==> !a b. c * a + c * b = c * (a + b)",
     ← ra r"!c. &0 < c ==> !a b. c * a - c * b = c * (a - b)",
     ← REAL_FIELD (← q r"!c. &0 < c ==> !a b. c * a = c * b <=> a = b"),
     ← MESON [REAL_LT_LMUL_EQ] (← q r"!c. &0 < c ==> !a b. c * a < c * b <=> a < b"),
     ← MESON [REAL_LE_LMUL_EQ] (← q r"!c. &0 < c ==> !a b. c * a <= c * b <=> a <= b"),
     ← MESON [REAL_LT_LMUL_EQ, real_gt]
       (← q r"!c. &0 < c ==> !a b. c * a > c * b <=> a > b"),
     ← MESON [REAL_LE_LMUL_EQ, real_ge]
       (← q r"!c. &0 < c ==> !a b. c * a >= c * b <=> a >= b"),
     ← MESON [REAL_POW_MUL]
      (← q r"!c. &0 < c ==> !a n. (c * a) pow n = c pow n * a pow n"),
     ← ra r"!c. &0 < c ==> !a b n. a * c pow n * b = c pow n * a * b",
     ← ra
      r"!c. &0 < c ==> !a b n. c pow n * a + c pow n * b = c pow n * (a + b)",
     ← ra
      r"!c. &0 < c ==> !a b n. c pow n * a - c pow n * b = c pow n * (a - b)",
     ← MESON [REAL_POW_LT, REAL_EQ_LCANCEL_IMP, REAL_LT_IMP_NZ]
      (← q r"!c. &0 < c ==> !a b n. c pow n * a = c pow n * b <=> a = b"),
     ← MESON [REAL_LT_LMUL_EQ, REAL_POW_LT]
       (← q r"!c. &0 < c ==> !a b n. c pow n * a < c pow n * b <=> a < b"),
     ← MESON [REAL_LE_LMUL_EQ, REAL_POW_LT]
       (← q r"!c. &0 < c ==> !a b n. c pow n * a <= c pow n * b <=> a <= b"),
     ← MESON [REAL_LT_LMUL_EQ, real_gt, REAL_POW_LT]
       (← q r"!c. &0 < c ==> !a b n. c pow n * a > c pow n * b <=> a > b"),
     ← MESON [REAL_LE_LMUL_EQ, real_ge, REAL_POW_LT]
       (← q r"!c. &0 < c ==> !a b n. c pow n * a >= c pow n * b <=> a >= b")]

  let QUANTIFY_SURJECTION_THM ← prove
   r"!f:A->B.
        (!y. ?x. f x = y)
        ==> ((!P. (!x. P x) <=> (!x. P (f x))) /\
             (!P. (?x. P x) <=> (?x. P (f x))) /\
             (!Q. (!s. Q s) <=> (!s. Q(IMAGE f s))) /\
             (!Q. (?s. Q s) <=> (?s. Q(IMAGE f s)))) /\
            (!P. {x | P x} = IMAGE f {x | P(f x)})"
   (GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [SURJECTIVE_RIGHT_INVERSE] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"g:B->A")) THEN
    SUBGOAL_THEN (← q r"!s. IMAGE (f:A->B) (IMAGE g s) = s") ASSUME_TAC THENL
     [ASM SET_TAC [], CONJ_TAC THENL [ASM MESON_TAC [], ASM SET_TAC []]])

  let QUANTIFY_SURJECTION_HIGHER_THM ← prove
   r"!f:A->B.
        (!y. ?x. f x = y)
        ==> ((!P. (!x. P x) <=> (!x. P (f x))) /\
             (!P. (?x. P x) <=> (?x. P (f x))) /\
             (!Q. (!s. Q s) <=> (!s. Q(IMAGE f s))) /\
             (!Q. (?s. Q s) <=> (?s. Q(IMAGE f s))) /\
             (!Q. (!s. Q s) <=> (!s. Q(IMAGE (IMAGE f) s))) /\
             (!Q. (?s. Q s) <=> (?s. Q(IMAGE (IMAGE f) s))) /\
             (!P. (!g:real^1->B. P g) <=> (!g. P(f o g))) /\
             (!P. (?g:real^1->B. P g) <=> (?g. P(f o g))) /\
             (!P. (!g:num->B. P g) <=> (!g. P(f o g))) /\
             (!P. (?g:num->B. P g) <=> (?g. P(f o g))) /\
             (!Q. (!l. Q l) <=> (!l. Q(MAP f l))) /\
             (!Q. (?l. Q l) <=> (?l. Q(MAP f l)))) /\
            ((!P. {x | P x} = IMAGE f {x | P(f x)}) /\
             (!Q. {s | Q s} = IMAGE (IMAGE f) {s | Q(IMAGE f s)}) /\
             (!R. {l | R l} = IMAGE (MAP f) {l | R(MAP f l)}))"
   (GEN_TAC THEN DISCH_TAC THEN CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
    ASM_REWRITE_TAC [← GSYM SURJECTIVE_FORALL_THM, ← GSYM SURJECTIVE_EXISTS_THM,
              ← GSYM SURJECTIVE_IMAGE_THM, SURJECTIVE_IMAGE, SURJECTIVE_MAP] THEN
    REWRITE_TAC [FUN_EQ_THM, o_THM, ← GSYM SKOLEM_THM] THEN ASM_MESON_TAC [])

  let PARTIAL_EXPAND_QUANTS_CONV (avoid : List String) (th : thm) :
      ExceptT String IO ioconv := do
    let (ath, sth) ← CONJ_PAIR th
    let conv1 := GEN_REWRITE_CONV id [ath]
    let conv2 := GEN_REWRITE_CONV id [sth]
    let conv1' : ioconv := fun tm => (do
      let th ← ExceptT.mk (conv1 tm)
      let v ← liftExcept (do
        let (bv, _) ← dest_abs (← rand tm)
        let (n, _) ← dest_var bv
        pure n)
      if avoid.contains v then throw "Not going to expand this variable" else pure th :
        ExceptT String IO thm).run
    pure (expandQuantsGo conv1' conv2)

  let EXPAND_QUANTS_CONV := PARTIAL_EXPAND_QUANTS_CONV []

  return { MEM_TRANSLATION, MEM_LINEAR_IMAGE, QUANTIFY_SURJECTION_THM,
           QUANTIFY_SURJECTION_HIGHER_THM, PARTIAL_EXPAND_QUANTS_CONV, EXPAND_QUANTS_CONV }
end HolMultiLib.Vectors
