/- ---------------------------------------------------------------------- -/
/- Session wiring for Multivariate/vectors.ml.                            -/
/- ---------------------------------------------------------------------- -/
/- File: SessionMultiLib/Vectors.lean

  The session half of the vectors.ml translation: it supplies
  HolMultiLib.Vectors's dependencies from Session, SessionMultiLib.Misc and
  SessionLibrary.Matroids (with Card and Floor), and exports every theorem by
  name.  Importing this module is `needs "Multivariate/vectors.ml"`: its own
  `needs` of Library/matroids.ml and Multivariate/misc.ml are the imports
  below, and each bundle is built by `initialize` when the module is loaded,
  in file order.
-/

import Session
import SessionLibrary.Matroids
import SessionMultiLib.Misc
import HolMultiLib.Vectors

open HolCore HolCore.Kernel

namespace SessionMultiLib.Vectors

open Session in
/-- The core theorems vectors.ml uses, ADD1 to FORALL_IN_INSERT. -/
def core1 : HolMultiLib.Vectors.CoreThms1 :=
  { ADD1, ADD_0, ADD_CLAUSES, ADD_SUB, ADD_SUC, ADD_SYM, AND_FORALL_THM, ARITH, ARITH_EQ,
    BIJECTIVE_LEFT_RIGHT_INVERSE, CARD_CLAUSES, CARD_DELETE, CARD_DIFF,
    CARD_EQ_BIJECTIONS, CARD_IMAGE_INJ, CARD_IMAGE_LE, CARD_LE_INJ, CARD_NUMSEG,
    CARD_NUMSEG_1, CARD_SUBSET, CARD_UNION, CARD_UNION_GEN, CARD_UNION_LE, CART_EQ,
    CART_EQ_FULL, COND_ID, COND_RAND, COND_RATOR, CONJ_ACI, CONJ_ASSOC, CONJ_SYM,
    CONTRAPOS_THM, CROSS, DECIMAL, DELETE, DELETE_INSERT, DELETE_SUBSET, DE_MORGAN_THM,
    DIFF, DIMINDEX_1, DIMINDEX_2, DIMINDEX_3, DIMINDEX_4, DIMINDEX_FINITE_PROD,
    DIMINDEX_FINITE_SUM, DIMINDEX_GE_1, DIMINDEX_NONZERO, DISJOINT, DISJOINT_NUMSEG,
    EMPTY_SUBSET, EQ_ADD_LCANCEL, EQ_ADD_RCANCEL, EQ_IMP, EQ_IMP_LE, EQ_SYM_EQ, EQ_TRANS,
    ETA_AX, EXISTS_FINITE_SUBSET_IMAGE, EXISTS_IN_IMAGE, EXISTS_IN_INSERT,
    EXISTS_PAIRED_THM, EXISTS_PASTECART, EXISTS_REFL, EXISTS_UNIQUE_DEF, EXTENSION,
    FINITE_CROSS, FINITE_DELETE, FINITE_DIFF, FINITE_EMPTY, FINITE_IMAGE,
    FINITE_IMAGE_INJ, FINITE_IMAGE_INJ_EQ, FINITE_INDEX_INRANGE,
    FINITE_INDEX_INRANGE_2, FINITE_INDEX_WORKS, FINITE_INDUCT_STRONG, FINITE_INSERT,
    FINITE_INTER, FINITE_NUMSEG, FINITE_PRODUCT_DEPENDENT, FINITE_RESTRICT,
    FINITE_RULES, FINITE_SUBSET, FINITE_SUBSET_IMAGE, FINITE_UNION, FINITE_UNIONS,
    FORALL_AND_THM, FORALL_IN_GSPEC, FORALL_IN_IMAGE, FORALL_IN_INSERT }

open Session in
/-- The core theorems vectors.ml uses, FORALL_IN_PCROSS to PAIRWISE_EMPTY. -/
def core2 : HolMultiLib.Vectors.CoreThms2 :=
  { FORALL_IN_PCROSS, FORALL_PAIRED_THM, FORALL_PAIR_THM, FST, FSTCART_COMPONENT,
    FSTCART_PASTECART, FUN_EQ_THM, FUN_IN_IMAGE, GT, HAS_SIZE, HAS_SIZE_IMAGE_INJ,
    HAS_SIZE_NUMSEG_1, IMAGE_CLAUSES, IMAGE_EQ, IMAGE_EQ_EMPTY, IMAGE_ID,
    IMAGE_INJECTIVE_IMAGE_OF_SUBSET, IMAGE_SUBSET, IMAGE_UNIONS, IMAGE_o, IMP_CONJ,
    IMP_CONJ_ALT, IMP_IMP, IN, INFINITE, INJECTIVE_IMAGE, INJECTIVE_LEFT_INVERSE,
    INJECTIVE_ON_ALT, INJECTIVE_ON_LEFT_INVERSE, INSERT_AC, INSERT_DELETE,
    INSERT_SUBSET, INTERSECTION_OF, INTERS_IMAGE, INTER_COMM, INTER_SUBSET, INTER_UNIV,
    IN_CROSS, IN_DELETE, IN_DIFF, IN_ELIM_PAIR_THM, IN_ELIM_THM, IN_IMAGE, IN_INSERT,
    IN_INTER, IN_INTERS, IN_NUMSEG, IN_SING, IN_UNION, IN_UNIONS, IN_UNIV,
    ITERATE_CLAUSES, ITERATE_REFLECT, I_DEF, I_O_ID, I_THM, LAMBDA_BETA, LAMBDA_ETA, LE,
    LEFT_AND_EXISTS_THM, LEFT_AND_FORALL_THM, LEFT_FORALL_IMP_THM,
    LEFT_IMP_EXISTS_THM, LEFT_OR_DISTRIB, LE_0, LE_1, LE_ADD2, LE_ANTISYM, LE_REFL,
    LE_TRANS, LT_LE, LT_REFL, MEMBER_NOT_EMPTY, MONO_AND, MONO_EXISTS, MONO_FORALL,
    MONO_IMP, NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, NOT_LE, NOT_LT,
    NUMSEG_CLAUSES, NUMSEG_EMPTY, NUMSEG_OFFSET_IMAGE, NUMSEG_REC, NUMSEG_SING, ONE,
    PAIRWISE_EMPTY }

open Session in
/-- The core theorems vectors.ml uses, PAIRWISE_INSERT to REAL_MUL_RINV. -/
def core3 : HolMultiLib.Vectors.CoreThms3 :=
  { PAIRWISE_INSERT, PAIRWISE_MONO, PAIRWISE_SING, PAIR_EQ, PASTECART_EQ,
    PASTECART_FST_SND, PASTECART_INJ, PASTECART_IN_PCROSS, PCROSS, PCROSS_EMPTY,
    PCROSS_MONO, POW_2_SQRT_ABS, PSUBSET, PSUBSET_ALT, REAL_ABS_0, REAL_ABS_DIV,
    REAL_ABS_INV, REAL_ABS_MUL, REAL_ABS_NEG, REAL_ABS_NUM, REAL_ABS_NZ, REAL_ABS_POS,
    REAL_ABS_POW, REAL_ABS_REFL, REAL_ABS_SUB, REAL_ABS_ZERO, REAL_ADD_AC,
    REAL_ADD_ASSOC, REAL_ADD_LDISTRIB, REAL_ADD_LID, REAL_ADD_RDISTRIB, REAL_ADD_RID,
    REAL_DIV_LMUL, REAL_DIV_RMUL, REAL_ENTIRE, REAL_EQ_ADD_LCANCEL_0,
    REAL_EQ_LCANCEL_IMP, REAL_EQ_MUL_RCANCEL, REAL_EQ_SQUARE_ABS, REAL_INV_0,
    REAL_INV_1, REAL_INV_EQ_0, REAL_INV_EQ_1, REAL_LET_TRANS, REAL_LE_ADD,
    REAL_LE_ADD2, REAL_LE_ADDL, REAL_LE_ADDR, REAL_LE_ANTISYM, REAL_LE_DIV,
    REAL_LE_LADD, REAL_LE_LDIV_EQ, REAL_LE_LMUL, REAL_LE_LMUL_EQ, REAL_LE_LSQRT,
    REAL_LE_MIN, REAL_LE_MUL, REAL_LE_MUL2, REAL_LE_NEG2, REAL_LE_POW_2,
    REAL_LE_RDIV_EQ, REAL_LE_REFL, REAL_LE_RMUL, REAL_LE_RSQRT, REAL_LE_SQUARE,
    REAL_LE_SQUARE_ABS, REAL_LE_SUB_RADD, REAL_LE_SUP_FINITE, REAL_LE_TOTAL,
    REAL_LE_TRANS, REAL_LT_ANTISYM, REAL_LT_DIV, REAL_LT_IMP_LE, REAL_LT_IMP_NZ,
    REAL_LT_INV_EQ, REAL_LT_LE, REAL_LT_LMUL_EQ, REAL_LT_MUL, REAL_LT_NEG2,
    REAL_LT_REFL, REAL_LT_TRANS, REAL_MAX_LE, REAL_MUL_AC, REAL_MUL_ASSOC,
    REAL_MUL_LID, REAL_MUL_LINV, REAL_MUL_LNEG, REAL_MUL_LZERO, REAL_MUL_RID,
    REAL_MUL_RINV }

open Session in
/-- The core theorems vectors.ml uses, REAL_MUL_RNEG to SUM_GROUP. -/
def core4 : HolMultiLib.Vectors.CoreThms4 :=
  { REAL_MUL_RNEG, REAL_MUL_RZERO, REAL_MUL_SYM, REAL_NEG_EQ_0, REAL_NEG_NEG,
    REAL_NOT_LE, REAL_NOT_LT, REAL_OF_NUM_ADD, REAL_OF_NUM_EQ, REAL_OF_NUM_LT,
    REAL_OF_NUM_SUC, REAL_POS, REAL_POW2_ABS, REAL_POW_2, REAL_POW_LE2, REAL_POW_LT,
    REAL_POW_MUL, REAL_RSQRT_LE, REAL_SQRT_POW_2, REAL_SUB_0, REAL_SUB_LDISTRIB,
    REAL_SUB_LE, REAL_SUB_RDISTRIB, REAL_SUB_REFL, REAL_SUB_RZERO,
    REAL_SUP_LE_FINITE, REAL_SUP_UNIQUE, REAL_WLOG_LE, RIGHT_AND_EXISTS_THM,
    RIGHT_EXISTS_AND_THM, RIGHT_FORALL_IMP_THM, RIGHT_IMP_EXISTS_THM,
    RIGHT_IMP_FORALL_THM, SELECT_UNIQUE, SIMPLE_IMAGE, SIMPLE_IMAGE_GEN, SING_SUBSET,
    SKOLEM_THM, SND, SNDCART_COMPONENT, SNDCART_PASTECART, SQRT_0, SQRT_1, SQRT_EQ_0,
    SQRT_INJ, SQRT_LT_0, SQRT_MONO_LE_EQ, SQRT_MONO_LT_EQ, SQRT_MUL, SQRT_POS_LE,
    SQRT_POW2, SQRT_POW_2, SUBSET, SUBSET_ANTISYM, SUBSET_ANTISYM_EQ, SUBSET_DIFF,
    SUBSET_IMAGE, SUBSET_INTER, SUBSET_REFL, SUBSET_TRANS, SUBSET_UNION, SUBSET_UNIV,
    SUB_ADD, SUC_INJ, SUC_SUB1, SUM_0, SUM_ABS_NUMSEG, SUM_ADD, SUM_ADD_GEN,
    SUM_ADD_NUMSEG, SUM_ADD_SPLIT, SUM_BOUND, SUM_CASES, SUM_CLAUSES, SUM_CLAUSES_LEFT,
    SUM_CLAUSES_NUMSEG, SUM_COMBINE_L, SUM_COMBINE_R, SUM_CONST, SUM_CONST_NUMSEG,
    SUM_DELETE, SUM_DELTA, SUM_DIFF, SUM_EQ, SUM_EQ_0, SUM_EQ_0_NUMSEG, SUM_EQ_GENERAL,
    SUM_EQ_GENERAL_INVERSES, SUM_EQ_NUMSEG, SUM_GROUP }

open Session in
/-- The core theorems vectors.ml uses, SUM_GROUP_RELATION to vector, and the
    lists.ml theorems (held in Session's list bundles). -/
def core5 : HolMultiLib.Vectors.CoreThms5 :=
  { SUM_GROUP_RELATION, SUM_IMAGE, SUM_IMAGE_GEN, SUM_INCL_EXCL, SUM_INJECTION,
    SUM_LE, SUM_LE_NUMSEG, SUM_LMUL, SUM_NEG, SUM_OFFSET, SUM_OFFSET_0, SUM_PAIR,
    SUM_POS_EQ_0_NUMSEG, SUM_POS_LE, SUM_POS_LE_NUMSEG, SUM_RESTRICT_SET, SUM_RMUL,
    SUM_SING_NUMSEG, SUM_SUB, SUM_SUB_NUMSEG, SUM_SUM_PRODUCT, SUM_SUPERSET, SUM_SWAP,
    SUM_SWAP_NUMSEG, SUM_TRIV_NUMSEG, SUM_UNION, SUM_UNION_EQ, SUM_UNION_NONZERO, SUP,
    SUP_EQ, SUP_FINITE, SUP_SING, SURJECTIVE_EXISTS_THM, SURJECTIVE_FORALL_THM,
    SURJECTIVE_IFF_INJECTIVE_GEN, SURJECTIVE_IMAGE, SURJECTIVE_IMAGE_EQ,
    SURJECTIVE_IMAGE_THM, SURJECTIVE_RIGHT_INVERSE, SWAP_EXISTS_THM,
    SWAP_FORALL_THM, UNIONS_0, UNIONS_IMAGE, UNIONS_INSERT, UNION_EMPTY, UNION_OF,
    UNION_SUBSET, UNIV_NOT_EMPTY, UNIV_SUBSET, UNWIND_THM1, finite_index, fstcart,
    is_int, monoidal, neutral, num_INFINITE, numseg, o_ASSOC, o_DEF, o_THM, pairwise,
    pastecart, real_abs, real_div, real_ge, real_gt, real_min, real_sub, sndcart,
    support, vector,
    EL := listDefs.EL, HD := listDefs.HD, LENGTH := listDefs.LENGTH,
    MAP := listDefs.MAP, TL := listDefs.TL,
    LENGTH_MAP := listThms1.LENGTH_MAP, MAP_APPEND := listThms1.MAP_APPEND,
    MAP_REVERSE := listThms2.MAP_REVERSE, MEM_MAP := listThms1.MEM_MAP,
    SURJECTIVE_MAP := listThms2.SURJECTIVE_MAP }

open SessionMultiLib.Misc in
/-- The theorems vectors.ml uses from Multivariate/misc.ml. -/
def misc : HolMultiLib.Vectors.MiscThms :=
  { HULL_HULL, HULL_MINIMAL, HULL_MONO, HULL_SUBSET, HULL_UNION, HULL_UNION_SUBSET,
    HULL_UNIQUE, LAMBDA_SKOLEM, MATRIFY_VECTORIZE, P_HULL, REAL_HALF, REAL_LE_BETWEEN,
    REAL_LT_BETWEEN, TRIANGLE_LEMMA, VECTORIZE_COMPONENT, VECTORIZE_MATRIFY, matrify,
    vectorize }

open SessionLibrary.Matroids in
/-- The theorems vectors.ml uses from Library/matroids.ml, card.ml and floor.ml. -/
def lib : HolMultiLib.Vectors.LibThms :=
  { MATROID_BASIS_SUBMATROID, MATROID_CHOOSE_SUBSPACE, MATROID_DIMENSION_UNIQUE,
    MATROID_DIM_ALT, MATROID_DIM_EMPTY, MATROID_DIM_EQ_SPAN,
    MATROID_DIM_GE_FINITE_CARD_EQ, MATROID_DIM_INSERT, MATROID_DIM_SPAN,
    MATROID_DIM_SPAN_EQ_GEN, MATROID_FINITE_DIMENSIONAL,
    MATROID_FINITE_DIMENSIONAL_DIM, MATROID_INDEPENDENT_INSERT,
    MATROID_INDEPENDENT_SUBMATROID, MATROID_INTERMEDIATE_BASIS,
    MATROID_LOWDIM_EXPAND_BASIS, MATROID_LOWDIM_EXPAND_DIMENSION,
    MATROID_SPANNING_SUBMATROID, MATROID_SPANNING_SUBSET_INDEPENDENT,
    MATROID_SPAN_EQ, MATROID_SPAN_INSERT_EQ, MATROID_STEINITZ_EXCHANGE_FINITE,
    SUBMATROID_SUBSET, matroid_basis, matroid_independent, matroid_set,
    matroid_span, matroid_spanning, matroid_subspace, matroid_tybij,
    COUNTABLE_IMAGE := SessionLibrary.Card.COUNTABLE_IMAGE,
    COUNTABLE_IMAGE_INJ_EQ := SessionLibrary.Card.COUNTABLE_IMAGE_INJ_EQ,
    RATIONAL_APPROXIMATION := SessionLibrary.Floor.RATIONAL_APPROXIMATION,
    RATIONAL_BETWEEN := SessionLibrary.Floor.RATIONAL_BETWEEN,
    rational := SessionLibrary.Floor.rational }

/-- What vectors.ml uses from hol.ml's library. -/
def deps : HolMultiLib.Vectors.VectorsDeps where
  new_definition s := do
    let t ← ExceptT.mk (HolCore.Parser.parse_term s)
    ExceptT.mk (Session.new_definition t)
  define s := do
    let t ← ExceptT.mk (HolCore.Parser.parse_term s)
    ExceptT.mk (Session.define t)
  parse_as_infix := Session.parse_as_infix
  make_overloadable s ty := ExceptT.mk (Session.make_overloadable s ty)
  overload_interface s t := ExceptT.mk (Session.overload_interface s t)
  override_interface s t := ExceptT.mk (Session.override_interface s t)
  prioritize_overload := Session.prioritize_overload
  prioritize_real := Session.prioritize_real
  extend_basic_congs := Session.extend_basic_congs
  prove_inductive_relations_exist t := ExceptT.mk (Session.prove_inductive_relations_exist t)
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  ASM_REAL_ARITH_TAC := Session.ASM_REAL_ARITH_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  METIS_TAC := Session.METIS_TAC
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH3 t)
  REAL_ARITH_TAC := Session.REAL_ARITH_TAC2
  REAL_FIELD t := ExceptT.mk (Session.REAL_FIELD t)
  REAL_RING t := ExceptT.mk (Session.REAL_RING t)
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  GEN_REAL_ARITH prover t := ExceptT.mk (Session.GEN_REAL_ARITH3 prover t)
  REAL_LINEAR_PROVER := Session.REAL_LINEAR_PROVER
  GEN_NNF_CONV cf c1 c2 := HolCore.Canon.GEN_NNF_CONV Session.B Session.nnfPths cf c1 c2
  term_of_rat x := HolMath.CalcInt.term_of_rat Session.RSyn x
  GEN_SIMPLIFY_CONV := HolCore.Simp.GEN_SIMPLIFY_CONV Session.B
  TOP_DEPTH_SQCONV := HolCore.Simp.TOP_DEPTH_SQCONV Session.B
  basic_ss := Session.basic_ss
  HAS_SIZE_CONV := Session.HAS_SIZE_CONV
  NUM_ADD_CONV := Session.NUM_ADD_CONV
  NUM_LE_CONV := Session.NUM_LE_CONV
  NUM_LT_CONV := Session.NUM_LT_CONV
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  REAL_POLY_CONV := Session.REAL_POLY_CONV
  REAL_POLY_NEG_CONV := Session.REAL_POLY_NEG_CONV
  REAL_RAT_ADD_CONV := Session.REAL_RAT_ADD_CONV
  REAL_RAT_MUL_CONV := Session.REAL_RAT_MUL_CONV
  REAL_RAT_REDUCE_CONV := Session.REAL_RAT_REDUCE_CONV
  SELECT_CONV t := pure (Session.SELECT_CONV t)
  num_CONV := Session.num_CONV
  core1 := core1
  core2 := core2
  core3 := core3
  core4 := core4
  core5 := core5
  misc := misc
  lib := lib

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} (name : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in vectors.ml order. -/
initialize BBasics : HolMultiLib.Vectors.Basics ←
  ioB "setupBasics" (HolMultiLib.Vectors.setupBasics deps).run
initialize BVectorArith : HolMultiLib.Vectors.VectorArith ←
  ioB "setupVectorArith" (HolMultiLib.Vectors.setupVectorArith deps BBasics).run
initialize BDotProps : HolMultiLib.Vectors.DotProps ←
  ioB "setupDotProps" (HolMultiLib.Vectors.setupDotProps deps BBasics BVectorArith).run
initialize BNorm1 : HolMultiLib.Vectors.Norm1 ←
  ioB "setupNorm1" (HolMultiLib.Vectors.setupNorm1 deps BBasics BVectorArith BDotProps).run
initialize BNorm2 : HolMultiLib.Vectors.Norm2 ←
  ioB "setupNorm2"
    (HolMultiLib.Vectors.setupNorm2 deps BBasics BVectorArith BDotProps BNorm1).run
initialize BNormArith : HolMultiLib.Vectors.NormArithB ←
  ioB "setupNormArith" (HolMultiLib.Vectors.setupNormArith deps BVectorArith BNorm1).run
initialize BMetric : HolMultiLib.Vectors.Metric ←
  ioB "setupMetric"
    (HolMultiLib.Vectors.setupMetric deps BVectorArith BDotProps BNorm1 BNorm2 BNormArith).run
initialize BVSum1 : HolMultiLib.Vectors.VSum1 ←
  ioB "setupVSum1"
    (HolMultiLib.Vectors.setupVSum1 deps BBasics BVectorArith BNorm1 BNormArith).run
initialize BVSum2 : HolMultiLib.Vectors.VSum2 ←
  ioB "setupVSum2"
    (HolMultiLib.Vectors.setupVSum2 deps BVectorArith BDotProps BNorm1 BNorm2 BVSum1).run
initialize BVSum3 : HolMultiLib.Vectors.VSum3 ←
  ioB "setupVSum3" (HolMultiLib.Vectors.setupVSum3 deps BVectorArith BVSum1 BVSum2).run
initialize BBasis : HolMultiLib.Vectors.Basis ←
  ioB "setupBasis" (HolMultiLib.Vectors.setupBasis deps BBasics BVectorArith BNorm1 BVSum1).run
initialize BOrth : HolMultiLib.Vectors.Orth ←
  ioB "setupOrth"
    (HolMultiLib.Vectors.setupOrth deps BBasics BDotProps BNorm1 BVSum1 BBasis).run
initialize BLinear : HolMultiLib.Vectors.Linear ←
  ioB "setupLinear"
    (HolMultiLib.Vectors.setupLinear deps BVectorArith BNorm1 BVSum1 BBasis).run
initialize BBilinear : HolMultiLib.Vectors.Bilinear ←
  ioB "setupBilinear"
    (HolMultiLib.Vectors.setupBilinear deps BVectorArith BNorm1 BVSum1 BVSum2 BBasis
      BLinear).run
initialize BAdjoint : HolMultiLib.Vectors.Adjoint ←
  ioB "setupAdjoint"
    (HolMultiLib.Vectors.setupAdjoint deps BBasics BVectorArith BDotProps BNorm1 BNorm2
      BVSum1 BBasis BOrth BLinear).run
initialize BMatrix : HolMultiLib.Vectors.Matrix ←
  ioB "setupMatrix" (HolMultiLib.Vectors.setupMatrix deps BVectorArith).run
initialize BMatArith : HolMultiLib.Vectors.MatArith ←
  ioB "setupMatArith" (HolMultiLib.Vectors.setupMatArith deps BVectorArith BMatrix).run
initialize BMatProps : HolMultiLib.Vectors.MatProps ←
  ioB "setupMatProps"
    (HolMultiLib.Vectors.setupMatProps deps BBasics BVectorArith BVSum1 BBasis BLinear
      BMatrix BMatArith).run
initialize BInvertible : HolMultiLib.Vectors.Invertible ←
  ioB "setupInvertible"
    (HolMultiLib.Vectors.setupInvertible deps BBasics BVectorArith BDotProps BVSum1 BBasis
      BLinear BAdjoint BMatrix BMatArith BMatProps).run
initialize BONorm : HolMultiLib.Vectors.ONorm ←
  ioB "setupONorm"
    (HolMultiLib.Vectors.setupONorm deps BVectorArith BDotProps BNorm1 BBasis BLinear
      BAdjoint BMatArith BInvertible).run
initialize BLiftDrop1 : HolMultiLib.Vectors.LiftDrop1 ←
  ioB "setupLiftDrop1" (HolMultiLib.Vectors.setupLiftDrop1 deps BBasics BVectorArith BVSum1).run
initialize BLiftDrop2 : HolMultiLib.Vectors.LiftDrop2 ←
  ioB "setupLiftDrop2"
    (HolMultiLib.Vectors.setupLiftDrop2 deps BBasics BVectorArith BDotProps BNorm1 BBasis
      BLinear BBilinear BMatrix BInvertible BLiftDrop1).run
initialize BPaste1 : HolMultiLib.Vectors.Paste1 ←
  ioB "setupPaste1"
    (HolMultiLib.Vectors.setupPaste1 deps BBasics BVectorArith BDotProps BNorm1 BNorm2
      BVSum1 BLinear BBilinear BMatrix BMatArith BMatProps BLiftDrop1).run
initialize BDropout : HolMultiLib.Vectors.Dropout ←
  ioB "setupDropout"
    (HolMultiLib.Vectors.setupDropout deps BBasics BVectorArith BDotProps BNorm1 BNorm2
      BLinear BPaste1).run
initialize BSubspace : HolMultiLib.Vectors.Subspace ←
  ioB "setupSubspace"
    (HolMultiLib.Vectors.setupSubspace deps BVectorArith BVSum1 BLinear BPaste1).run
initialize BSpan1 : HolMultiLib.Vectors.Span1 ←
  ioB "setupSpan1" (HolMultiLib.Vectors.setupSpan1 deps BVectorArith BSubspace).run
initialize BSpan2 : HolMultiLib.Vectors.Span2 ←
  ioB "setupSpan2"
    (HolMultiLib.Vectors.setupSpan2 deps BVectorArith BVSum1 BBasis BSubspace BSpan1).run
initialize BDim1 : HolMultiLib.Vectors.Dim1 ←
  ioB "setupDim1" (HolMultiLib.Vectors.setupDim1 deps BSubspace BSpan1 BSpan2).run
initialize BDim2 : HolMultiLib.Vectors.Dim2 ←
  ioB "setupDim2" (HolMultiLib.Vectors.setupDim2 deps BSubspace BSpan1 BSpan2 BDim1).run
initialize BExplicit : HolMultiLib.Vectors.Explicit ←
  ioB "setupExplicit"
    (HolMultiLib.Vectors.setupExplicit deps BVectorArith BVSum1 BLinear BPaste1 BSubspace
      BSpan1 BSpan2 BDim1 BDim2).run
initialize BExtend : HolMultiLib.Vectors.Extend ←
  ioB "setupExtend"
    (HolMultiLib.Vectors.setupExtend deps BVectorArith BDotProps BVSum1 BVSum2 BOrth BLinear
      BSubspace BSpan1 BDim1 BDim2).run
initialize BLinEq : HolMultiLib.Vectors.LinEq ←
  ioB "setupLinEq"
    (HolMultiLib.Vectors.setupLinEq deps BVectorArith BLinear BBilinear BInvertible BMatProps
      BSubspace BSpan2 BExplicit BExtend).run
initialize BMatInv : HolMultiLib.Vectors.MatInv ←
  ioB "setupMatInv"
    (HolMultiLib.Vectors.setupMatInv deps BVectorArith BVSum1 BLinear BMatrix BMatArith
      BMatProps BInvertible BSubspace BSpan1 BLinEq).run
initialize BIso : HolMultiLib.Vectors.Iso ←
  ioB "setupIso"
    (HolMultiLib.Vectors.setupIso deps BLinear BSpan1 BDim1 BDim2 BExplicit BExtend
      BLinEq).run
initialize BMatInv2 : HolMultiLib.Vectors.MatInv2 ←
  ioB "setupMatInv2"
    (HolMultiLib.Vectors.setupMatInv2 deps BLinear BMatArith BMatProps BInvertible BDim2
      BExplicit BLinEq BMatInv BIso).run
initialize BRowSpace : HolMultiLib.Vectors.RowSpace ←
  ioB "setupRowSpace"
    (HolMultiLib.Vectors.setupRowSpace deps BBasics BVectorArith BOrth BMatrix BMatArith
      BMatProps BInvertible BSubspace BSpan1 BDim1 BDim2 BExplicit).run
initialize BRank : HolMultiLib.Vectors.Rank ←
  ioB "setupRank"
    (HolMultiLib.Vectors.setupRank deps BVectorArith BDotProps BBasis BLinear BMatrix BMatArith
      BMatProps BInvertible BSubspace BSpan1 BSpan2 BDim2 BExplicit BLinEq BMatInv
      BRowSpace).run
initialize BONormMat : HolMultiLib.Vectors.ONormMat ←
  ioB "setupONormMat"
    (HolMultiLib.Vectors.setupONormMat deps BNorm1 BNorm2 BBasis BMatrix BMatProps
      BInvertible BONorm BRank).run
initialize BHyperplane : HolMultiLib.Vectors.Hyperplane ←
  ioB "setupHyperplane"
    (HolMultiLib.Vectors.setupHyperplane deps BVectorArith BDotProps BLinear BAdjoint BMatProps
      BInvertible BIso BRank).run
initialize BGram1 : HolMultiLib.Vectors.Gram1 ←
  ioB "setupGram1"
    (HolMultiLib.Vectors.setupGram1 deps BVectorArith BDotProps BNorm1 BVSum2 BBasis BOrth
      BSubspace BSpan1 BSpan2 BDim1 BDim2 BRowSpace).run
initialize BGram2 : HolMultiLib.Vectors.Gram2 ←
  ioB "setupGram2"
    (HolMultiLib.Vectors.setupGram2 deps BVectorArith BDotProps BNorm1 BNorm2 BVSum2 BOrth
      BSubspace BSpan2 BDim2 BGram1).run
initialize BGram3 : HolMultiLib.Vectors.Gram3 ←
  ioB "setupGram3"
    (HolMultiLib.Vectors.setupGram3 deps BVectorArith BDotProps BNorm1 BNorm2 BVSum2 BOrth
      BSubspace BSpan1 BDim1 BDim2 BExplicit BRowSpace BGram1).run
initialize BIndepSub : HolMultiLib.Vectors.IndepSub ←
  ioB "setupIndepSub"
    (HolMultiLib.Vectors.setupIndepSub deps BVectorArith BOrth BSubspace BSpan1 BDim1
      BRowSpace BGram1 BGram3).run
initialize BIsometry : HolMultiLib.Vectors.Isometry ←
  ioB "setupIsometry"
    (HolMultiLib.Vectors.setupIsometry deps BBasics BVectorArith BNorm1 BNorm2 BOrth BLinear
      BSubspace BSpan1 BSpan2 BDim2 BExplicit BExtend BGram3).run
initialize BSpecHyper : HolMultiLib.Vectors.SpecHyper ←
  ioB "setupSpecHyper"
    (HolMultiLib.Vectors.setupSpecHyper deps BVectorArith BDotProps BNormArith BVSum1 BBasis
      BOrth BSubspace BSpan1 BSpan2 BDim2 BRowSpace BGram1 BGram3).run
initialize BDimKernel : HolMultiLib.Vectors.DimKernel ←
  ioB "setupDimKernel"
    (HolMultiLib.Vectors.setupDimKernel deps BVectorArith BNorm1 BVSum1 BLinear BSubspace
      BSpan1 BSpan2 BDim1 BDim2 BExplicit BLinEq).run
initialize BDimSums : HolMultiLib.Vectors.DimSums ←
  ioB "setupDimSums"
    (HolMultiLib.Vectors.setupDimSums deps BVectorArith BDotProps BNorm1 BVSum1 BBasis BOrth
      BLinear BSubspace BSpan1 BSpan2 BDim1 BDim2 BExplicit BGram1 BIndepSub).run
initialize BInjDim : HolMultiLib.Vectors.InjDim ←
  ioB "setupInjDim"
    (HolMultiLib.Vectors.setupInjDim deps BSubspace BSpan1 BDim2 BExplicit BLinEq BIso
      BMatInv2 BDimKernel BDimSums).run
initialize BPCrossDim : HolMultiLib.Vectors.PCrossDim ←
  ioB "setupPCrossDim"
    (HolMultiLib.Vectors.setupPCrossDim deps BVectorArith BLinear BPaste1 BSubspace BSpan1
      BDim2 BExplicit BMatInv2 BDimSums).run
initialize BRankNull : HolMultiLib.Vectors.RankNull ←
  ioB "setupRankNull"
    (HolMultiLib.Vectors.setupRankNull deps BDotProps BMatArith BMatProps BInvertible
      BSubspace BDim2 BRank BDimKernel BDimSums).run
initialize BMatPinv : HolMultiLib.Vectors.MatPinv ←
  ioB "setupMatPinv"
    (HolMultiLib.Vectors.setupMatPinv deps BVectorArith BOrth BLinear BAdjoint BMatrix
      BMatArith BMatProps BInvertible BSubspace BSpan1 BLinEq BIndepSub).run
initialize BMatPinv2 : HolMultiLib.Vectors.MatPinv2 ←
  ioB "setupMatPinv2"
    (HolMultiLib.Vectors.setupMatPinv2 deps BMatrix BMatArith BMatProps BInvertible BLinEq
      BMatInv2 BRank BMatPinv).run
initialize BMatPinv3 : HolMultiLib.Vectors.MatPinv3 ←
  ioB "setupMatPinv3"
    (HolMultiLib.Vectors.setupMatPinv3 deps BMatrix BMatArith BMatProps BRank BMatPinv
      BMatPinv2).run
initialize BInfnorm : HolMultiLib.Vectors.Infnorm ←
  ioB "setupInfnorm"
    (HolMultiLib.Vectors.setupInfnorm deps BBasics BVectorArith BDotProps BNorm1
      BNormArith).run
initialize BCollinear : HolMultiLib.Vectors.Collinear ←
  ioB "setupCollinear"
    (HolMultiLib.Vectors.setupCollinear deps BBasics BVectorArith BDotProps BNorm1 BOrth
      BSpan1 BInfnorm).run
initialize BBetween : HolMultiLib.Vectors.Between ←
  ioB "setupBetween"
    (HolMultiLib.Vectors.setupBetween deps BVectorArith BNorm1 BNormArith BMetric BLinear
      BLiftDrop1 BLiftDrop2 BInfnorm BCollinear).run
initialize BInterval : HolMultiLib.Vectors.Interval ←
  ioB "setupInterval" (HolMultiLib.Vectors.setupInterval deps BVectorArith).run
initialize BInvariance1 : HolMultiLib.Vectors.Invariance1 ←
  ioB "setupInvariance1"
    (HolMultiLib.Vectors.setupInvariance1 deps BVectorArith BNorm1 BLinear BSubspace BLinEq
      BIso).run
initialize BInvariance2 : HolMultiLib.Vectors.Invariance2 ←
  ioB "setupInvariance2"
    (HolMultiLib.Vectors.setupInvariance2 deps BVectorArith BDotProps BNorm1 BNorm2 BNormArith
      BOrth BLinear BMatrix BMatArith BMatProps BInvertible BSpan1 BMatInv2 BBetween
      BInvariance1).run
initialize BInvariance3 : HolMultiLib.Vectors.Invariance3 ←
  ioB "setupInvariance3"
    (HolMultiLib.Vectors.setupInvariance3 deps BVectorArith BDotProps BNorm1 BMetric BOrth
      BInvariance1).run

/- The theorems, by name. -/
-- Basics (vectors.ml 16-117)
def FORALL_1 : thm := BBasics.FORALL_1
def FORALL_2 : thm := BBasics.FORALL_2
def FORALL_3 : thm := BBasics.FORALL_3
def FORALL_4 : thm := BBasics.FORALL_4
def SUM_1 : thm := BBasics.SUM_1
def SUM_2 : thm := BBasics.SUM_2
def SUM_3 : thm := BBasics.SUM_3
def SUM_4 : thm := BBasics.SUM_4
def vector_add : thm := BBasics.vector_add
def vector_sub : thm := BBasics.vector_sub
def vector_neg : thm := BBasics.vector_neg
/-- `prioritize_vector()` (vectors.ml 71). -/
def prioritize_vector : IO Unit := BBasics.prioritize_vector
def vector_mul : thm := BBasics.vector_mul
def vec : thm := BBasics.vec
def dot : thm := BBasics.dot
def DOT_1 : thm := BBasics.DOT_1
def DOT_2 : thm := BBasics.DOT_2
def DOT_3 : thm := BBasics.DOT_3
def DOT_4 : thm := BBasics.DOT_4
-- VectorArith (vectors.ml 119-265)
/-- `VECTOR_ARITH_TAC` (vectors.ml 119). -/
def VECTOR_ARITH_TAC : HolCore.Tactics.tactic := fun g => BVectorArith.VECTOR_ARITH_TAC g
/-- `VECTOR_ARITH tm` (vectors.ml 140). -/
def VECTOR_ARITH : HolCore.Equal.ioconv := fun t => BVectorArith.VECTOR_ARITH t
def VEC_COMPONENT : thm := BVectorArith.VEC_COMPONENT
def VECTOR_ADD_COMPONENT : thm := BVectorArith.VECTOR_ADD_COMPONENT
def VECTOR_SUB_COMPONENT : thm := BVectorArith.VECTOR_SUB_COMPONENT
def VECTOR_NEG_COMPONENT : thm := BVectorArith.VECTOR_NEG_COMPONENT
def VECTOR_MUL_COMPONENT : thm := BVectorArith.VECTOR_MUL_COMPONENT
def COND_COMPONENT : thm := BVectorArith.COND_COMPONENT
def VECTOR_ADD_SYM : thm := BVectorArith.VECTOR_ADD_SYM
def VECTOR_ADD_LID : thm := BVectorArith.VECTOR_ADD_LID
def VECTOR_ADD_RID : thm := BVectorArith.VECTOR_ADD_RID
def VECTOR_SUB_REFL : thm := BVectorArith.VECTOR_SUB_REFL
def VECTOR_ADD_LINV : thm := BVectorArith.VECTOR_ADD_LINV
def VECTOR_ADD_RINV : thm := BVectorArith.VECTOR_ADD_RINV
def VECTOR_SUB_RADD : thm := BVectorArith.VECTOR_SUB_RADD
def VECTOR_NEG_SUB : thm := BVectorArith.VECTOR_NEG_SUB
def VECTOR_SUB_EQ : thm := BVectorArith.VECTOR_SUB_EQ
def VECTOR_MUL_ASSOC : thm := BVectorArith.VECTOR_MUL_ASSOC
def VECTOR_MUL_LID : thm := BVectorArith.VECTOR_MUL_LID
def VECTOR_MUL_LZERO : thm := BVectorArith.VECTOR_MUL_LZERO
def VECTOR_SUB_ADD : thm := BVectorArith.VECTOR_SUB_ADD
def VECTOR_SUB_ADD2 : thm := BVectorArith.VECTOR_SUB_ADD2
def VECTOR_ADD_LDISTRIB : thm := BVectorArith.VECTOR_ADD_LDISTRIB
def VECTOR_SUB_LDISTRIB : thm := BVectorArith.VECTOR_SUB_LDISTRIB
def VECTOR_ADD_RDISTRIB : thm := BVectorArith.VECTOR_ADD_RDISTRIB
def VECTOR_SUB_RDISTRIB : thm := BVectorArith.VECTOR_SUB_RDISTRIB
def VECTOR_ADD_SUB : thm := BVectorArith.VECTOR_ADD_SUB
def VECTOR_EQ_ADDR : thm := BVectorArith.VECTOR_EQ_ADDR
def VECTOR_SUB : thm := BVectorArith.VECTOR_SUB
def VECTOR_SUB_RZERO : thm := BVectorArith.VECTOR_SUB_RZERO
def VECTOR_MUL_RZERO : thm := BVectorArith.VECTOR_MUL_RZERO
def VECTOR_NEG_MINUS1 : thm := BVectorArith.VECTOR_NEG_MINUS1
def VECTOR_ADD_ASSOC : thm := BVectorArith.VECTOR_ADD_ASSOC
def VECTOR_SUB_LZERO : thm := BVectorArith.VECTOR_SUB_LZERO
def VECTOR_NEG_NEG : thm := BVectorArith.VECTOR_NEG_NEG
def VECTOR_MUL_LNEG : thm := BVectorArith.VECTOR_MUL_LNEG
def VECTOR_MUL_RNEG : thm := BVectorArith.VECTOR_MUL_RNEG
def VECTOR_NEG_0 : thm := BVectorArith.VECTOR_NEG_0
def VECTOR_NEG_EQ_0 : thm := BVectorArith.VECTOR_NEG_EQ_0
def VECTOR_EQ_NEG2 : thm := BVectorArith.VECTOR_EQ_NEG2
def VECTOR_ADD_AC : thm := BVectorArith.VECTOR_ADD_AC
def VEC_EQ : thm := BVectorArith.VEC_EQ
-- DotProps (vectors.ml 267-404)
def SUMS_SYM : thm := BDotProps.SUMS_SYM
def SUMS_ASSOC : thm := BDotProps.SUMS_ASSOC
def EUCLIDEAN_SPACE_INFINITE : thm := BDotProps.EUCLIDEAN_SPACE_INFINITE
def DOT_SYM : thm := BDotProps.DOT_SYM
def DOT_LADD : thm := BDotProps.DOT_LADD
def DOT_RADD : thm := BDotProps.DOT_RADD
def DOT_LSUB : thm := BDotProps.DOT_LSUB
def DOT_RSUB : thm := BDotProps.DOT_RSUB
def DOT_LMUL : thm := BDotProps.DOT_LMUL
def DOT_RMUL : thm := BDotProps.DOT_RMUL
def DOT_LNEG : thm := BDotProps.DOT_LNEG
def DOT_RNEG : thm := BDotProps.DOT_RNEG
def DOT_LZERO : thm := BDotProps.DOT_LZERO
def DOT_RZERO : thm := BDotProps.DOT_RZERO
def DOT_POS_LE : thm := BDotProps.DOT_POS_LE
def DOT_EQ_0 : thm := BDotProps.DOT_EQ_0
def DOT_POS_LT : thm := BDotProps.DOT_POS_LT
def FORALL_DOT_EQ_0 : thm := BDotProps.FORALL_DOT_EQ_0
def REFLECT_UNIV : thm := BDotProps.REFLECT_UNIV
def TRANSLATION_UNIV : thm := BDotProps.TRANSLATION_UNIV
def TRANSLATION_SUBSET_GALOIS_RIGHT : thm := BDotProps.TRANSLATION_SUBSET_GALOIS_RIGHT
def TRANSLATION_SUBSET_GALOIS_LEFT : thm := BDotProps.TRANSLATION_SUBSET_GALOIS_LEFT
def TRANSLATION_GALOIS : thm := BDotProps.TRANSLATION_GALOIS
def IN_TRANSLATION_GALOIS : thm := BDotProps.IN_TRANSLATION_GALOIS
def IN_TRANSLATION_GALOIS_ALT : thm := BDotProps.IN_TRANSLATION_GALOIS_ALT
def FORALL_DIMINDEX_1 : thm := BDotProps.FORALL_DIMINDEX_1
def VECTOR_ONE : thm := BDotProps.VECTOR_ONE
def FORALL_REAL_ONE : thm := BDotProps.FORALL_REAL_ONE
-- Norm1 (vectors.ml 406-574)
def vector_norm : thm := BNorm1.vector_norm
def dist : thm := BNorm1.dist
def NORM_REAL : thm := BNorm1.NORM_REAL
def DIST_REAL : thm := BNorm1.DIST_REAL
def NORM_0 : thm := BNorm1.NORM_0
def NORM_POS_LE : thm := BNorm1.NORM_POS_LE
def NORM_NEG : thm := BNorm1.NORM_NEG
def NORM_SUB : thm := BNorm1.NORM_SUB
def NORM_MUL : thm := BNorm1.NORM_MUL
def NORM_EQ_0_DOT : thm := BNorm1.NORM_EQ_0_DOT
def NORM_EQ_0 : thm := BNorm1.NORM_EQ_0
def NORM_POS_LT : thm := BNorm1.NORM_POS_LT
def NORM_POW_2 : thm := BNorm1.NORM_POW_2
def NORM_EQ_0_IMP : thm := BNorm1.NORM_EQ_0_IMP
def NORM_LE_0 : thm := BNorm1.NORM_LE_0
def VECTOR_MUL_EQ_0 : thm := BNorm1.VECTOR_MUL_EQ_0
def VECTOR_MUL_LCANCEL : thm := BNorm1.VECTOR_MUL_LCANCEL
def VECTOR_MUL_RCANCEL : thm := BNorm1.VECTOR_MUL_RCANCEL
def VECTOR_MUL_LCANCEL_IMP : thm := BNorm1.VECTOR_MUL_LCANCEL_IMP
def VECTOR_MUL_RCANCEL_IMP : thm := BNorm1.VECTOR_MUL_RCANCEL_IMP
def NORM_CAUCHY_SCHWARZ : thm := BNorm1.NORM_CAUCHY_SCHWARZ
def NORM_CAUCHY_SCHWARZ_ABS : thm := BNorm1.NORM_CAUCHY_SCHWARZ_ABS
def REAL_ABS_NORM : thm := BNorm1.REAL_ABS_NORM
def NORM_CAUCHY_SCHWARZ_DIV : thm := BNorm1.NORM_CAUCHY_SCHWARZ_DIV
def NORM_TRIANGLE : thm := BNorm1.NORM_TRIANGLE
def NORM_TRIANGLE_SUB : thm := BNorm1.NORM_TRIANGLE_SUB
def NORM_TRIANGLE_LE : thm := BNorm1.NORM_TRIANGLE_LE
def NORM_TRIANGLE_LT : thm := BNorm1.NORM_TRIANGLE_LT
def COMPONENT_LE_NORM : thm := BNorm1.COMPONENT_LE_NORM
def NORM_BOUND_COMPONENT_LE : thm := BNorm1.NORM_BOUND_COMPONENT_LE
def NORM_BOUND_COMPONENT_LT : thm := BNorm1.NORM_BOUND_COMPONENT_LT
-- Norm2 (vectors.ml 576-708)
def NORM_LE_L1 : thm := BNorm2.NORM_LE_L1
def REAL_ABS_SUB_NORM : thm := BNorm2.REAL_ABS_SUB_NORM
def NORM_LE : thm := BNorm2.NORM_LE
def NORM_LT : thm := BNorm2.NORM_LT
def NORM_EQ : thm := BNorm2.NORM_EQ
def NORM_EQ_1 : thm := BNorm2.NORM_EQ_1
def NORM_LE_COMPONENTWISE : thm := BNorm2.NORM_LE_COMPONENTWISE
def NORM_EQ_COMPONENTWISE : thm := BNorm2.NORM_EQ_COMPONENTWISE
def L1_LE_NORM : thm := BNorm2.L1_LE_NORM
def DIST_INCREASES_ONLINE : thm := BNorm2.DIST_INCREASES_ONLINE
def NORM_INCREASES_ONLINE : thm := BNorm2.NORM_INCREASES_ONLINE
def DOT_SQUARE_NORM : thm := BNorm2.DOT_SQUARE_NORM
def NORM_EQ_SQUARE : thm := BNorm2.NORM_EQ_SQUARE
def NORM_LE_SQUARE : thm := BNorm2.NORM_LE_SQUARE
def NORM_GE_SQUARE : thm := BNorm2.NORM_GE_SQUARE
def NORM_LT_SQUARE : thm := BNorm2.NORM_LT_SQUARE
def NORM_GT_SQUARE : thm := BNorm2.NORM_GT_SQUARE
def NORM_LT_SQUARE_ALT : thm := BNorm2.NORM_LT_SQUARE_ALT
-- NormArith (vectors.ml 713-1005)
/-- `NORM_ARITH tm` (vectors.ml 713). -/
def NORM_ARITH : HolCore.Equal.ioconv := fun t => BNormArith.NORM_ARITH t
/-- `NORM_ARITH_TAC` (vectors.ml 1001). -/
def NORM_ARITH_TAC : HolCore.Tactics.tactic := fun g => BNormArith.NORM_ARITH_TAC g
/-- `ASM_NORM_ARITH_TAC` (vectors.ml 1003). -/
def ASM_NORM_ARITH_TAC : HolCore.Tactics.tactic := fun g => BNormArith.ASM_NORM_ARITH_TAC g
-- Metric (vectors.ml 1007-1213)
def HOMOMORPHISM_REAL_TO_REAL : thm := BMetric.HOMOMORPHISM_REAL_TO_REAL
def DOT_NORM : thm := BMetric.DOT_NORM
def DOT_NORM_SUB : thm := BMetric.DOT_NORM_SUB
def VECTOR_EQ : thm := BMetric.VECTOR_EQ
def DIST_REFL : thm := BMetric.DIST_REFL
def DIST_SYM : thm := BMetric.DIST_SYM
def DIST_POS_LE : thm := BMetric.DIST_POS_LE
def REAL_ABS_DIST : thm := BMetric.REAL_ABS_DIST
def DIST_TRIANGLE : thm := BMetric.DIST_TRIANGLE
def DIST_TRIANGLE_ALT : thm := BMetric.DIST_TRIANGLE_ALT
def DIST_EQ_0 : thm := BMetric.DIST_EQ_0
def DIST_POS_LT : thm := BMetric.DIST_POS_LT
def DIST_NZ : thm := BMetric.DIST_NZ
def DIST_TRIANGLE_LE : thm := BMetric.DIST_TRIANGLE_LE
def DIST_TRIANGLE_LT : thm := BMetric.DIST_TRIANGLE_LT
def DIST_TRIANGLE_HALF_L : thm := BMetric.DIST_TRIANGLE_HALF_L
def DIST_TRIANGLE_HALF_R : thm := BMetric.DIST_TRIANGLE_HALF_R
def DIST_TRIANGLE_ADD : thm := BMetric.DIST_TRIANGLE_ADD
def DIST_MUL : thm := BMetric.DIST_MUL
def DIST_TRIANGLE_ADD_HALF : thm := BMetric.DIST_TRIANGLE_ADD_HALF
def DIST_LE_0 : thm := BMetric.DIST_LE_0
def DIST_EQ : thm := BMetric.DIST_EQ
def DIST_0 : thm := BMetric.DIST_0
def DIST_RESCALE : thm := BMetric.DIST_RESCALE
def DIST_DESCALE : thm := BMetric.DIST_DESCALE
-- VSum1 (vectors.ml 1215-1457)
def NEUTRAL_VECTOR_ADD : thm := BVSum1.NEUTRAL_VECTOR_ADD
def MONOIDAL_VECTOR_ADD : thm := BVSum1.MONOIDAL_VECTOR_ADD
def vsum : thm := BVSum1.vsum
def VSUM_CLAUSES : thm := BVSum1.VSUM_CLAUSES
def VSUM : thm := BVSum1.VSUM
def VSUM_EQ_0 : thm := BVSum1.VSUM_EQ_0
def VSUM_0 : thm := BVSum1.VSUM_0
def VSUM_LMUL : thm := BVSum1.VSUM_LMUL
def VSUM_RMUL : thm := BVSum1.VSUM_RMUL
def VSUM_ADD : thm := BVSum1.VSUM_ADD
def VSUM_SUB : thm := BVSum1.VSUM_SUB
def VSUM_CONST : thm := BVSum1.VSUM_CONST
def VSUM_COMPONENT : thm := BVSum1.VSUM_COMPONENT
def VSUM_IMAGE : thm := BVSum1.VSUM_IMAGE
def VSUM_UNION : thm := BVSum1.VSUM_UNION
def VSUM_DIFF : thm := BVSum1.VSUM_DIFF
def VSUM_DELETE : thm := BVSum1.VSUM_DELETE
def VSUM_INCL_EXCL : thm := BVSum1.VSUM_INCL_EXCL
def VSUM_NEG : thm := BVSum1.VSUM_NEG
def VSUM_EQ : thm := BVSum1.VSUM_EQ
def VSUM_SUPERSET : thm := BVSum1.VSUM_SUPERSET
def VSUM_SUPPORT : thm := BVSum1.VSUM_SUPPORT
def VSUM_UNIV : thm := BVSum1.VSUM_UNIV
def VSUM_EQ_SUPERSET : thm := BVSum1.VSUM_EQ_SUPERSET
def VSUM_UNION_RZERO : thm := BVSum1.VSUM_UNION_RZERO
def VSUM_UNION_LZERO : thm := BVSum1.VSUM_UNION_LZERO
def VSUM_RESTRICT : thm := BVSum1.VSUM_RESTRICT
def VSUM_RESTRICT_SET : thm := BVSum1.VSUM_RESTRICT_SET
def VSUM_CASES : thm := BVSum1.VSUM_CASES
def VSUM_SING : thm := BVSum1.VSUM_SING
def VSUM_NORM : thm := BVSum1.VSUM_NORM
def VSUM_NORM_LE : thm := BVSum1.VSUM_NORM_LE
def VSUM_NORM_TRIANGLE : thm := BVSum1.VSUM_NORM_TRIANGLE
def VSUM_NORM_BOUND : thm := BVSum1.VSUM_NORM_BOUND
def VSUM_CLAUSES_NUMSEG : thm := BVSum1.VSUM_CLAUSES_NUMSEG
def VSUM_CLAUSES_RIGHT : thm := BVSum1.VSUM_CLAUSES_RIGHT
def VSUM_CMUL_NUMSEG : thm := BVSum1.VSUM_CMUL_NUMSEG
def VSUM_EQ_NUMSEG : thm := BVSum1.VSUM_EQ_NUMSEG
def VSUM_IMAGE_GEN : thm := BVSum1.VSUM_IMAGE_GEN
def VSUM_GROUP : thm := BVSum1.VSUM_GROUP
def VSUM_GROUP_RELATION : thm := BVSum1.VSUM_GROUP_RELATION
def VSUM_VMUL : thm := BVSum1.VSUM_VMUL
def VSUM_DELTA : thm := BVSum1.VSUM_DELTA
def VSUM_ADD_NUMSEG : thm := BVSum1.VSUM_ADD_NUMSEG
-- VSum2 (vectors.ml 1459-1670)
def VSUM_SUB_NUMSEG : thm := BVSum2.VSUM_SUB_NUMSEG
def VSUM_ADD_SPLIT : thm := BVSum2.VSUM_ADD_SPLIT
def VSUM_VSUM_PRODUCT : thm := BVSum2.VSUM_VSUM_PRODUCT
def VSUM_IMAGE_NONZERO : thm := BVSum2.VSUM_IMAGE_NONZERO
def VSUM_UNION_NONZERO : thm := BVSum2.VSUM_UNION_NONZERO
def VSUM_UNIONS_NONZERO : thm := BVSum2.VSUM_UNIONS_NONZERO
def VSUM_CLAUSES_LEFT : thm := BVSum2.VSUM_CLAUSES_LEFT
def VSUM_DIFFS : thm := BVSum2.VSUM_DIFFS
def VSUM_DIFFS_ALT : thm := BVSum2.VSUM_DIFFS_ALT
def VSUM_DELETE_CASES : thm := BVSum2.VSUM_DELETE_CASES
def VSUM_EQ_GENERAL : thm := BVSum2.VSUM_EQ_GENERAL
def VSUM_EQ_GENERAL_INVERSES : thm := BVSum2.VSUM_EQ_GENERAL_INVERSES
def VSUM_NORM_ALLSUBSETS_BOUND : thm := BVSum2.VSUM_NORM_ALLSUBSETS_BOUND
def DOT_LSUM : thm := BVSum2.DOT_LSUM
def DOT_RSUM : thm := BVSum2.DOT_RSUM
def VSUM_OFFSET : thm := BVSum2.VSUM_OFFSET
def VSUM_OFFSET_0 : thm := BVSum2.VSUM_OFFSET_0
def VSUM_TRIV_NUMSEG : thm := BVSum2.VSUM_TRIV_NUMSEG
def VSUM_CONST_NUMSEG : thm := BVSum2.VSUM_CONST_NUMSEG
def VSUM_SUC : thm := BVSum2.VSUM_SUC
def VSUM_BIJECTION : thm := BVSum2.VSUM_BIJECTION
def VSUM_PARTIAL_SUC : thm := BVSum2.VSUM_PARTIAL_SUC
-- VSum3 (vectors.ml 1672-1835)
def VSUM_PARTIAL_PRE : thm := BVSum3.VSUM_PARTIAL_PRE
def VSUM_COMBINE_L : thm := BVSum3.VSUM_COMBINE_L
def VSUM_COMBINE_R : thm := BVSum3.VSUM_COMBINE_R
def VSUM_INJECTION : thm := BVSum3.VSUM_INJECTION
def VSUM_SWAP : thm := BVSum3.VSUM_SWAP
def VSUM_SWAP_NUMSEG : thm := BVSum3.VSUM_SWAP_NUMSEG
def VSUM_ADD_GEN : thm := BVSum3.VSUM_ADD_GEN
def VSUM_CASES_1 : thm := BVSum3.VSUM_CASES_1
def VSUM_SING_NUMSEG : thm := BVSum3.VSUM_SING_NUMSEG
def VSUM_1 : thm := BVSum3.VSUM_1
def VSUM_2 : thm := BVSum3.VSUM_2
def VSUM_3 : thm := BVSum3.VSUM_3
def VSUM_4 : thm := BVSum3.VSUM_4
def VSUM_PAIR : thm := BVSum3.VSUM_PAIR
def VSUM_PAIR_0 : thm := BVSum3.VSUM_PAIR_0
def VSUM_REFLECT : thm := BVSum3.VSUM_REFLECT
/-- `EXPAND_VSUM_CONV` (vectors.ml 1802). -/
def EXPAND_VSUM_CONV : HolCore.Equal.ioconv := fun t => BVSum3.EXPAND_VSUM_CONV t
-- Basis (vectors.ml 1836-1957)
def basis : thm := BBasis.basis
def NORM_BASIS : thm := BBasis.NORM_BASIS
def NORM_BASIS_1 : thm := BBasis.NORM_BASIS_1
def VECTOR_CHOOSE_SIZE : thm := BBasis.VECTOR_CHOOSE_SIZE
def VECTOR_CHOOSE_DIST : thm := BBasis.VECTOR_CHOOSE_DIST
def BASIS_INJ : thm := BBasis.BASIS_INJ
def BASIS_INJ_EQ : thm := BBasis.BASIS_INJ_EQ
def BASIS_NE : thm := BBasis.BASIS_NE
def BASIS_COMPONENT : thm := BBasis.BASIS_COMPONENT
def BASIS_EXPANSION : thm := BBasis.BASIS_EXPANSION
def BASIS_EXPANSION_UNIQUE : thm := BBasis.BASIS_EXPANSION_UNIQUE
def DOT_BASIS : thm := BBasis.DOT_BASIS
def DOT_BASIS_BASIS : thm := BBasis.DOT_BASIS_BASIS
def DOT_BASIS_BASIS_UNEQUAL : thm := BBasis.DOT_BASIS_BASIS_UNEQUAL
def BASIS_EQ_0 : thm := BBasis.BASIS_EQ_0
def BASIS_NONZERO : thm := BBasis.BASIS_NONZERO
def VECTOR_EQ_LDOT : thm := BBasis.VECTOR_EQ_LDOT
def VECTOR_EQ_RDOT : thm := BBasis.VECTOR_EQ_RDOT
-- Orth (vectors.ml 1959-2149)
def orthogonal : thm := BOrth.orthogonal
def ORTHOGONAL_0 : thm := BOrth.ORTHOGONAL_0
def ORTHOGONAL_REFL : thm := BOrth.ORTHOGONAL_REFL
def ORTHOGONAL_SYM : thm := BOrth.ORTHOGONAL_SYM
def ORTHOGONAL_LNEG : thm := BOrth.ORTHOGONAL_LNEG
def ORTHOGONAL_RNEG : thm := BOrth.ORTHOGONAL_RNEG
def ORTHOGONAL_MUL : thm := BOrth.ORTHOGONAL_MUL
def ORTHOGONAL_BASIS : thm := BOrth.ORTHOGONAL_BASIS
def ORTHOGONAL_BASIS_BASIS : thm := BOrth.ORTHOGONAL_BASIS_BASIS
def ORTHOGONAL_CLAUSES : thm := BOrth.ORTHOGONAL_CLAUSES
def ORTHOGONAL_RVSUM : thm := BOrth.ORTHOGONAL_RVSUM
def ORTHOGONAL_LVSUM : thm := BOrth.ORTHOGONAL_LVSUM
def NORM_ADD_PYTHAGOREAN : thm := BOrth.NORM_ADD_PYTHAGOREAN
def NORM_VSUM_PYTHAGOREAN : thm := BOrth.NORM_VSUM_PYTHAGOREAN
def VECTOR_1 : thm := BOrth.VECTOR_1
def VECTOR_2 : thm := BOrth.VECTOR_2
def VECTOR_3 : thm := BOrth.VECTOR_3
def VECTOR_4 : thm := BOrth.VECTOR_4
def FORALL_VECTOR_1 : thm := BOrth.FORALL_VECTOR_1
def FORALL_VECTOR_2 : thm := BOrth.FORALL_VECTOR_2
def FORALL_VECTOR_3 : thm := BOrth.FORALL_VECTOR_3
def FORALL_VECTOR_4 : thm := BOrth.FORALL_VECTOR_4
def EXISTS_VECTOR_1 : thm := BOrth.EXISTS_VECTOR_1
def EXISTS_VECTOR_2 : thm := BOrth.EXISTS_VECTOR_2
def EXISTS_VECTOR_3 : thm := BOrth.EXISTS_VECTOR_3
def EXISTS_VECTOR_4 : thm := BOrth.EXISTS_VECTOR_4
def VECTOR_EXPAND_1 : thm := BOrth.VECTOR_EXPAND_1
def VECTOR_EXPAND_2 : thm := BOrth.VECTOR_EXPAND_2
def VECTOR_EXPAND_3 : thm := BOrth.VECTOR_EXPAND_3
def VECTOR_EXPAND_4 : thm := BOrth.VECTOR_EXPAND_4
-- Linear (vectors.ml 2151-2287)
def linear : thm := BLinear.linear
def LINEAR_COMPOSE_CMUL : thm := BLinear.LINEAR_COMPOSE_CMUL
def LINEAR_COMPOSE_NEG : thm := BLinear.LINEAR_COMPOSE_NEG
def LINEAR_COMPOSE_NEG_EQ : thm := BLinear.LINEAR_COMPOSE_NEG_EQ
def LINEAR_COMPOSE_ADD : thm := BLinear.LINEAR_COMPOSE_ADD
def LINEAR_COMPOSE_SUB : thm := BLinear.LINEAR_COMPOSE_SUB
def LINEAR_COMPOSE : thm := BLinear.LINEAR_COMPOSE
def LINEAR_ID : thm := BLinear.LINEAR_ID
def LINEAR_I : thm := BLinear.LINEAR_I
def LINEAR_ZERO : thm := BLinear.LINEAR_ZERO
def LINEAR_NEGATION : thm := BLinear.LINEAR_NEGATION
def LINEAR_COMPOSE_VSUM : thm := BLinear.LINEAR_COMPOSE_VSUM
def LINEAR_VMUL_COMPONENT : thm := BLinear.LINEAR_VMUL_COMPONENT
def LINEAR_0 : thm := BLinear.LINEAR_0
def LINEAR_CMUL : thm := BLinear.LINEAR_CMUL
def LINEAR_NEG : thm := BLinear.LINEAR_NEG
def LINEAR_ADD : thm := BLinear.LINEAR_ADD
def LINEAR_SUB : thm := BLinear.LINEAR_SUB
def LINEAR_VSUM : thm := BLinear.LINEAR_VSUM
def LINEAR_VSUM_MUL : thm := BLinear.LINEAR_VSUM_MUL
def LINEAR_INJECTIVE_0 : thm := BLinear.LINEAR_INJECTIVE_0
def LINEAR_BOUNDED : thm := BLinear.LINEAR_BOUNDED
def LINEAR_BOUNDED_POS : thm := BLinear.LINEAR_BOUNDED_POS
def SYMMETRIC_LINEAR_IMAGE : thm := BLinear.SYMMETRIC_LINEAR_IMAGE
-- Bilinear (vectors.ml 2289-2475)
def bilinear : thm := BBilinear.bilinear
def BILINEAR_SWAP : thm := BBilinear.BILINEAR_SWAP
def BILINEAR_LADD : thm := BBilinear.BILINEAR_LADD
def BILINEAR_RADD : thm := BBilinear.BILINEAR_RADD
def BILINEAR_LMUL : thm := BBilinear.BILINEAR_LMUL
def BILINEAR_RMUL : thm := BBilinear.BILINEAR_RMUL
def BILINEAR_LNEG : thm := BBilinear.BILINEAR_LNEG
def BILINEAR_RNEG : thm := BBilinear.BILINEAR_RNEG
def BILINEAR_LZERO : thm := BBilinear.BILINEAR_LZERO
def BILINEAR_RZERO : thm := BBilinear.BILINEAR_RZERO
def BILINEAR_LSUB : thm := BBilinear.BILINEAR_LSUB
def BILINEAR_RSUB : thm := BBilinear.BILINEAR_RSUB
def BILINEAR_LSUM : thm := BBilinear.BILINEAR_LSUM
def BILINEAR_RSUM : thm := BBilinear.BILINEAR_RSUM
def BILINEAR_VSUM : thm := BBilinear.BILINEAR_VSUM
def BILINEAR_BOUNDED : thm := BBilinear.BILINEAR_BOUNDED
def BILINEAR_BOUNDED_POS : thm := BBilinear.BILINEAR_BOUNDED_POS
def BILINEAR_VSUM_PARTIAL_SUC : thm := BBilinear.BILINEAR_VSUM_PARTIAL_SUC
def BILINEAR_VSUM_PARTIAL_PRE : thm := BBilinear.BILINEAR_VSUM_PARTIAL_PRE
def BILINEAR_VSUM_CONVOLUTION_1 : thm := BBilinear.BILINEAR_VSUM_CONVOLUTION_1
def BILINEAR_VSUM_CONVOLUTION_2 : thm := BBilinear.BILINEAR_VSUM_CONVOLUTION_2
-- Adjoint (vectors.ml 2477-2636)
def adjoint : thm := BAdjoint.adjoint
def ADJOINT_WORKS : thm := BAdjoint.ADJOINT_WORKS
def ADJOINT_LINEAR : thm := BAdjoint.ADJOINT_LINEAR
def ADJOINT_CLAUSES : thm := BAdjoint.ADJOINT_CLAUSES
def ADJOINT_ADJOINT : thm := BAdjoint.ADJOINT_ADJOINT
def ADJOINT_UNIQUE : thm := BAdjoint.ADJOINT_UNIQUE
def ADJOINT_COMPOSE : thm := BAdjoint.ADJOINT_COMPOSE
def SELF_ADJOINT_COMPOSE : thm := BAdjoint.SELF_ADJOINT_COMPOSE
def SELF_ADJOINT_ORTHOGONAL_EIGENVECTORS : thm := BAdjoint.SELF_ADJOINT_ORTHOGONAL_EIGENVECTORS
def ORTHOGONAL_PROJECTION_ALT : thm := BAdjoint.ORTHOGONAL_PROJECTION_ALT
def ORTHOGONAL_PROJECTION_EQ_SELF_ADJOINT_IDEMPOTENT : thm :=
  BAdjoint.ORTHOGONAL_PROJECTION_EQ_SELF_ADJOINT_IDEMPOTENT
def LIPSCHITZ_ON_POS : thm := BAdjoint.LIPSCHITZ_ON_POS
def LIPSCHITZ_POS : thm := BAdjoint.LIPSCHITZ_POS
def LIPSCHITZ_ON_COMPOSE : thm := BAdjoint.LIPSCHITZ_ON_COMPOSE
def LINEAR_IMP_LIPSCHITZ : thm := BAdjoint.LINEAR_IMP_LIPSCHITZ
def LIPSCHITZ_ON_COMPONENTWISE : thm := BAdjoint.LIPSCHITZ_ON_COMPONENTWISE
-- Matrix (vectors.ml 2638-2796)
def matrix_cmul : thm := BMatrix.matrix_cmul
def matrix_neg : thm := BMatrix.matrix_neg
def matrix_add : thm := BMatrix.matrix_add
def matrix_sub : thm := BMatrix.matrix_sub
def matrix_mul : thm := BMatrix.matrix_mul
def matrix_vector_mul : thm := BMatrix.matrix_vector_mul
def vector_matrix_mul : thm := BMatrix.vector_matrix_mul
def mat : thm := BMatrix.mat
def transp : thm := BMatrix.transp
def row : thm := BMatrix.row
def column : thm := BMatrix.column
def rows : thm := BMatrix.rows
def columns : thm := BMatrix.columns
def MATRIX_CMUL_COMPONENT : thm := BMatrix.MATRIX_CMUL_COMPONENT
def MATRIX_ADD_COMPONENT : thm := BMatrix.MATRIX_ADD_COMPONENT
def MATRIX_SUB_COMPONENT : thm := BMatrix.MATRIX_SUB_COMPONENT
def MATRIX_NEG_COMPONENT : thm := BMatrix.MATRIX_NEG_COMPONENT
def TRANSP_COMPONENT : thm := BMatrix.TRANSP_COMPONENT
def MAT_COMPONENT : thm := BMatrix.MAT_COMPONENT
def MAT_0_COMPONENT : thm := BMatrix.MAT_0_COMPONENT
def MATRIX_ADD_ROW : thm := BMatrix.MATRIX_ADD_ROW
def MATRIX_SUB_ROW : thm := BMatrix.MATRIX_SUB_ROW
def MATRIX_NEG_ROW : thm := BMatrix.MATRIX_NEG_ROW
def MATRIX_CMUL_ROW : thm := BMatrix.MATRIX_CMUL_ROW
def MAT_0_ROW : thm := BMatrix.MAT_0_ROW
def symmetric_matrix : thm := BMatrix.symmetric_matrix
def normal_matrix : thm := BMatrix.normal_matrix
def SYMMETRIC_IMP_NORMAL_MATRIX : thm := BMatrix.SYMMETRIC_IMP_NORMAL_MATRIX
-- MatArith (vectors.ml 2800-3058)
/-- `MATRIX_ARITH_TAC` (vectors.ml 2800). -/
def MATRIX_ARITH_TAC : HolCore.Tactics.tactic := fun g => BMatArith.MATRIX_ARITH_TAC g
/-- `MATRIX_ARITH tm` (vectors.ml 2822). -/
def MATRIX_ARITH : HolCore.Equal.ioconv := fun t => BMatArith.MATRIX_ARITH t
def MAT_CMUL : thm := BMatArith.MAT_CMUL
def ROW_0 : thm := BMatArith.ROW_0
def COLUMN_0 : thm := BMatArith.COLUMN_0
def MATRIX_CMUL_ASSOC : thm := BMatArith.MATRIX_CMUL_ASSOC
def MATRIX_CMUL_LID : thm := BMatArith.MATRIX_CMUL_LID
def MATRIX_ADD_SYM : thm := BMatArith.MATRIX_ADD_SYM
def MATRIX_ADD_ASSOC : thm := BMatArith.MATRIX_ADD_ASSOC
def MATRIX_ADD_LID : thm := BMatArith.MATRIX_ADD_LID
def MATRIX_ADD_RID : thm := BMatArith.MATRIX_ADD_RID
def MATRIX_ADD_LNEG : thm := BMatArith.MATRIX_ADD_LNEG
def MATRIX_ADD_RNEG : thm := BMatArith.MATRIX_ADD_RNEG
def MATRIX_SUB : thm := BMatArith.MATRIX_SUB
def MATRIX_SUB_REFL : thm := BMatArith.MATRIX_SUB_REFL
def MATRIX_SUB_EQ : thm := BMatArith.MATRIX_SUB_EQ
def MATRIX_SUB_ADD : thm := BMatArith.MATRIX_SUB_ADD
def MATRIX_SUB_ADD2 : thm := BMatArith.MATRIX_SUB_ADD2
def MATRIX_ADD_LDISTRIB : thm := BMatArith.MATRIX_ADD_LDISTRIB
def MATRIX_MUL_LID : thm := BMatArith.MATRIX_MUL_LID
def MATRIX_MUL_RID : thm := BMatArith.MATRIX_MUL_RID
def MATRIX_MUL_ASSOC : thm := BMatArith.MATRIX_MUL_ASSOC
def MATRIX_MUL_LZERO : thm := BMatArith.MATRIX_MUL_LZERO
def MATRIX_MUL_RZERO : thm := BMatArith.MATRIX_MUL_RZERO
def MATRIX_ADD_RDISTRIB : thm := BMatArith.MATRIX_ADD_RDISTRIB
def MATRIX_SUB_LDISTRIB : thm := BMatArith.MATRIX_SUB_LDISTRIB
def MATRIX_SUB_RDISTRIB : thm := BMatArith.MATRIX_SUB_RDISTRIB
def MATRIX_MUL_LMUL : thm := BMatArith.MATRIX_MUL_LMUL
def MATRIX_MUL_RMUL : thm := BMatArith.MATRIX_MUL_RMUL
def MATRIX_CMUL_ADD_LDISTRIB : thm := BMatArith.MATRIX_CMUL_ADD_LDISTRIB
def MATRIX_CMUL_SUB_LDISTRIB : thm := BMatArith.MATRIX_CMUL_SUB_LDISTRIB
def MATRIX_CMUL_ADD_RDISTRIB : thm := BMatArith.MATRIX_CMUL_ADD_RDISTRIB
def MATRIX_CMUL_SUB_RDISTRIB : thm := BMatArith.MATRIX_CMUL_SUB_RDISTRIB
def MATRIX_CMUL_RZERO : thm := BMatArith.MATRIX_CMUL_RZERO
def MATRIX_CMUL_LZERO : thm := BMatArith.MATRIX_CMUL_LZERO
def MATRIX_NEG_MINUS1 : thm := BMatArith.MATRIX_NEG_MINUS1
def MATRIX_ADD_AC : thm := BMatArith.MATRIX_ADD_AC
def MATRIX_NEG_ADD : thm := BMatArith.MATRIX_NEG_ADD
def MATRIX_NEG_SUB : thm := BMatArith.MATRIX_NEG_SUB
def MATRIX_NEG_0 : thm := BMatArith.MATRIX_NEG_0
def MATRIX_SUB_RZERO : thm := BMatArith.MATRIX_SUB_RZERO
def MATRIX_SUB_LZERO : thm := BMatArith.MATRIX_SUB_LZERO
def MATRIX_NEG_EQ_0 : thm := BMatArith.MATRIX_NEG_EQ_0
def MATRIX_VECTOR_MUL_ASSOC : thm := BMatArith.MATRIX_VECTOR_MUL_ASSOC
def MATRIX_VECTOR_MUL_LID : thm := BMatArith.MATRIX_VECTOR_MUL_LID
def MATRIX_VECTOR_MUL_LZERO : thm := BMatArith.MATRIX_VECTOR_MUL_LZERO
def MATRIX_VECTOR_MUL_RZERO : thm := BMatArith.MATRIX_VECTOR_MUL_RZERO
def MATRIX_VECTOR_MUL_ADD_LDISTRIB : thm := BMatArith.MATRIX_VECTOR_MUL_ADD_LDISTRIB
def MATRIX_VECTOR_MUL_SUB_LDISTRIB : thm := BMatArith.MATRIX_VECTOR_MUL_SUB_LDISTRIB
def MATRIX_VECTOR_MUL_ADD_RDISTRIB : thm := BMatArith.MATRIX_VECTOR_MUL_ADD_RDISTRIB
def MATRIX_VECTOR_MUL_SUB_RDISTRIB : thm := BMatArith.MATRIX_VECTOR_MUL_SUB_RDISTRIB
def MATRIX_VECTOR_MUL_RMUL : thm := BMatArith.MATRIX_VECTOR_MUL_RMUL
def MATRIX_MUL_LNEG : thm := BMatArith.MATRIX_MUL_LNEG
-- MatProps (vectors.ml 3061-3342)
def MATRIX_MUL_RNEG : thm := BMatProps.MATRIX_MUL_RNEG
def MATRIX_NEG_NEG : thm := BMatProps.MATRIX_NEG_NEG
def MATRIX_TRANSP_MUL : thm := BMatProps.MATRIX_TRANSP_MUL
def TRANSP_EQ_0 : thm := BMatProps.TRANSP_EQ_0
def SYMMETRIC_MATRIX_MUL : thm := BMatProps.SYMMETRIC_MATRIX_MUL
def MATRIX_EQ : thm := BMatProps.MATRIX_EQ
def MATRIX_EQ_0 : thm := BMatProps.MATRIX_EQ_0
def MATRIX_VECTOR_MUL_COMPONENT : thm := BMatProps.MATRIX_VECTOR_MUL_COMPONENT
def DOT_LMUL_MATRIX : thm := BMatProps.DOT_LMUL_MATRIX
def TRANSP_MATRIX_CMUL : thm := BMatProps.TRANSP_MATRIX_CMUL
def SYMMETRIC_MATRIX_CMUL : thm := BMatProps.SYMMETRIC_MATRIX_CMUL
def TRANSP_MATRIX_ADD : thm := BMatProps.TRANSP_MATRIX_ADD
def SYMMETRIC_MATRIX_ADD : thm := BMatProps.SYMMETRIC_MATRIX_ADD
def TRANSP_MATRIX_SUB : thm := BMatProps.TRANSP_MATRIX_SUB
def SYMMETRIC_MATRIX_SUB : thm := BMatProps.SYMMETRIC_MATRIX_SUB
def TRANSP_MATRIX_NEG : thm := BMatProps.TRANSP_MATRIX_NEG
def SYMMETRIC_MATRIX_NEG : thm := BMatProps.SYMMETRIC_MATRIX_NEG
def TRANSP_MAT : thm := BMatProps.TRANSP_MAT
def TRANSP_TRANSP : thm := BMatProps.TRANSP_TRANSP
def SYMMETRIC_MATRIX_MAT : thm := BMatProps.SYMMETRIC_MATRIX_MAT
def SYMMETRIC_MATRIX_COVARIANCE : thm := BMatProps.SYMMETRIC_MATRIX_COVARIANCE
def SYMMETRIC_MATRIX_SIMILAR : thm := BMatProps.SYMMETRIC_MATRIX_SIMILAR
def TRANSP_EQ : thm := BMatProps.TRANSP_EQ
def ROW_TRANSP : thm := BMatProps.ROW_TRANSP
def COLUMN_TRANSP : thm := BMatProps.COLUMN_TRANSP
def ROWS_TRANSP : thm := BMatProps.ROWS_TRANSP
def COLUMNS_TRANSP : thm := BMatProps.COLUMNS_TRANSP
def VECTOR_MATRIX_MUL_TRANSP : thm := BMatProps.VECTOR_MATRIX_MUL_TRANSP
def MATRIX_VECTOR_MUL_TRANSP : thm := BMatProps.MATRIX_VECTOR_MUL_TRANSP
def ROWS_NONEMPTY : thm := BMatProps.ROWS_NONEMPTY
def COLUMNS_NONEMPTY : thm := BMatProps.COLUMNS_NONEMPTY
def FINITE_ROWS : thm := BMatProps.FINITE_ROWS
def FINITE_COLUMNS : thm := BMatProps.FINITE_COLUMNS
def CARD_ROWS_LE : thm := BMatProps.CARD_ROWS_LE
def CARD_COLUMNS_LE : thm := BMatProps.CARD_COLUMNS_LE
def MATRIX_EQUAL_ROWS : thm := BMatProps.MATRIX_EQUAL_ROWS
def MATRIX_EQUAL_COLUMNS : thm := BMatProps.MATRIX_EQUAL_COLUMNS
def MATRIX_CMUL_EQ_0 : thm := BMatProps.MATRIX_CMUL_EQ_0
def MAT_EQ : thm := BMatProps.MAT_EQ
def MATRIX_VECTOR_LMUL : thm := BMatProps.MATRIX_VECTOR_LMUL
def MATRIX_VECTOR_MUL_LNEG : thm := BMatProps.MATRIX_VECTOR_MUL_LNEG
def MATRIX_VECTOR_MUL_RNEG : thm := BMatProps.MATRIX_VECTOR_MUL_RNEG
def COLUMN_MATRIX_MUL : thm := BMatProps.COLUMN_MATRIX_MUL
def ROW_MATRIX_MUL : thm := BMatProps.ROW_MATRIX_MUL
def MATRIX_MUL_DOT : thm := BMatProps.MATRIX_MUL_DOT
def MATRIX_MUL_VSUM : thm := BMatProps.MATRIX_MUL_VSUM
def VECTOR_COMPONENTWISE : thm := BMatProps.VECTOR_COMPONENTWISE
def LINEAR_COMPONENTWISE_EXPANSION : thm := BMatProps.LINEAR_COMPONENTWISE_EXPANSION
-- Invertible (vectors.ml 3345-3565)
def invertible : thm := BInvertible.invertible
def INVERTIBLE_I : thm := BInvertible.INVERTIBLE_I
def INVERTIBLE_NEG : thm := BInvertible.INVERTIBLE_NEG
def INVERTIBLE_CMUL : thm := BInvertible.INVERTIBLE_CMUL
def INVERTIBLE_MAT : thm := BInvertible.INVERTIBLE_MAT
def MATRIX_ENTIRE : thm := BInvertible.MATRIX_ENTIRE
def matrix : thm := BInvertible.matrix
def MATRIX_COMPONENT : thm := BInvertible.MATRIX_COMPONENT
def MATRIX_VECTOR_MUL_LINEAR : thm := BInvertible.MATRIX_VECTOR_MUL_LINEAR
def MATRIX_WORKS : thm := BInvertible.MATRIX_WORKS
def MATRIX_VECTOR_MUL : thm := BInvertible.MATRIX_VECTOR_MUL
def MATRIX_OF_MATRIX_VECTOR_MUL : thm := BInvertible.MATRIX_OF_MATRIX_VECTOR_MUL
def MATRIX_COMPOSE : thm := BInvertible.MATRIX_COMPOSE
def MATRIX_0 : thm := BInvertible.MATRIX_0
def MATRIX_VECTOR_COLUMN : thm := BInvertible.MATRIX_VECTOR_COLUMN
def MATRIX_MUL_COMPONENT : thm := BInvertible.MATRIX_MUL_COMPONENT
def ADJOINT_MATRIX : thm := BInvertible.ADJOINT_MATRIX
def MATRIX_ADJOINT : thm := BInvertible.MATRIX_ADJOINT
def MATRIX_ID : thm := BInvertible.MATRIX_ID
def MATRIX_I : thm := BInvertible.MATRIX_I
def LINEAR_EQ_MATRIX : thm := BInvertible.LINEAR_EQ_MATRIX
def MATRIX_CMUL : thm := BInvertible.MATRIX_CMUL
def MATRIX_NEG : thm := BInvertible.MATRIX_NEG
def MATRIX_ADD : thm := BInvertible.MATRIX_ADD
def MATRIX_SELF_ADJOINT : thm := BInvertible.MATRIX_SELF_ADJOINT
def LINEAR_MATRIX_EXISTS : thm := BInvertible.LINEAR_MATRIX_EXISTS
def LINEAR_1_GEN : thm := BInvertible.LINEAR_1_GEN
def LINEAR_1 : thm := BInvertible.LINEAR_1
def SYMMETRIC_MATRIX : thm := BInvertible.SYMMETRIC_MATRIX
def DOT_MATRIX_TRANSP_LMUL : thm := BInvertible.DOT_MATRIX_TRANSP_LMUL
def DOT_MATRIX_TRANSP_RMUL : thm := BInvertible.DOT_MATRIX_TRANSP_RMUL
def SYMMETRIC_MATRIX_ORTHOGONAL_EIGENVECTORS : thm :=
  BInvertible.SYMMETRIC_MATRIX_ORTHOGONAL_EIGENVECTORS
def MATRIX_INJECTIVE_0 : thm := BInvertible.MATRIX_INJECTIVE_0
-- ONorm (vectors.ml 3569-3815)
def onorm : thm := BONorm.onorm
def NORM_BOUND_GENERALIZE : thm := BONorm.NORM_BOUND_GENERALIZE
def ONORM_DOT : thm := BONorm.ONORM_DOT
def ONORM : thm := BONorm.ONORM
def ONORM_LE_EQ : thm := BONorm.ONORM_LE_EQ
def ONORM_POS_LE : thm := BONorm.ONORM_POS_LE
def ONORM_EQ_0 : thm := BONorm.ONORM_EQ_0
def ONORM_CONST : thm := BONorm.ONORM_CONST
def ONORM_POS_LT : thm := BONorm.ONORM_POS_LT
def ONORM_COMPOSE : thm := BONorm.ONORM_COMPOSE
def ONORM_CMUL : thm := BONorm.ONORM_CMUL
def ONORM_NEG : thm := BONorm.ONORM_NEG
def ONORM_TRIANGLE : thm := BONorm.ONORM_TRIANGLE
def ONORM_TRIANGLE_LE : thm := BONorm.ONORM_TRIANGLE_LE
def ONORM_TRIANGLE_LT : thm := BONorm.ONORM_TRIANGLE_LT
def ONORM_ID : thm := BONorm.ONORM_ID
def ONORM_I : thm := BONorm.ONORM_I
def ONORM_INVERSE_FUNCTION_BOUND : thm := BONorm.ONORM_INVERSE_FUNCTION_BOUND
def ONORM_ADJOINT : thm := BONorm.ONORM_ADJOINT
def ONORM_COMPOSE_ADJOINT_LEFT : thm := BONorm.ONORM_COMPOSE_ADJOINT_LEFT
def ONORM_COMPOSE_ADJOINT_RIGHT : thm := BONorm.ONORM_COMPOSE_ADJOINT_RIGHT
def ONORM_TRANSP : thm := BONorm.ONORM_TRANSP
def ONORM_COVARIANCE : thm := BONorm.ONORM_COVARIANCE
def ONORM_COVARIANCE_ALT : thm := BONorm.ONORM_COVARIANCE_ALT
def ONORM_LE_EQ_2 : thm := BONorm.ONORM_LE_EQ_2
def ONORM_LE_EQ_2_ABS : thm := BONorm.ONORM_LE_EQ_2_ABS
-- LiftDrop1 (vectors.ml 3819-3998)
def lift : thm := BLiftDrop1.lift
def drop : thm := BLiftDrop1.drop
def LIFT_COMPONENT : thm := BLiftDrop1.LIFT_COMPONENT
def LIFT_DROP : thm := BLiftDrop1.LIFT_DROP
def IMAGE_LIFT_DROP : thm := BLiftDrop1.IMAGE_LIFT_DROP
def IN_IMAGE_LIFT_DROP : thm := BLiftDrop1.IN_IMAGE_LIFT_DROP
def FORALL_LIFT : thm := BLiftDrop1.FORALL_LIFT
def EXISTS_LIFT : thm := BLiftDrop1.EXISTS_LIFT
def FORALL_DROP : thm := BLiftDrop1.FORALL_DROP
def EXISTS_DROP : thm := BLiftDrop1.EXISTS_DROP
def FORALL_LIFT_FUN : thm := BLiftDrop1.FORALL_LIFT_FUN
def FORALL_DROP_FUN : thm := BLiftDrop1.FORALL_DROP_FUN
def FORALL_FUN_LIFT : thm := BLiftDrop1.FORALL_FUN_LIFT
def FORALL_FUN_DROP : thm := BLiftDrop1.FORALL_FUN_DROP
def EXISTS_LIFT_FUN : thm := BLiftDrop1.EXISTS_LIFT_FUN
def EXISTS_DROP_FUN : thm := BLiftDrop1.EXISTS_DROP_FUN
def EXISTS_FUN_LIFT : thm := BLiftDrop1.EXISTS_FUN_LIFT
def EXISTS_FUN_DROP : thm := BLiftDrop1.EXISTS_FUN_DROP
def LIFT_EQ : thm := BLiftDrop1.LIFT_EQ
def DROP_EQ : thm := BLiftDrop1.DROP_EQ
def LIFT_IN_IMAGE_LIFT : thm := BLiftDrop1.LIFT_IN_IMAGE_LIFT
def FORALL_LIFT_IMAGE : thm := BLiftDrop1.FORALL_LIFT_IMAGE
def EXISTS_LIFT_IMAGE : thm := BLiftDrop1.EXISTS_LIFT_IMAGE
def SUBSET_LIFT_IMAGE : thm := BLiftDrop1.SUBSET_LIFT_IMAGE
def FORALL_DROP_IMAGE : thm := BLiftDrop1.FORALL_DROP_IMAGE
def EXISTS_DROP_IMAGE : thm := BLiftDrop1.EXISTS_DROP_IMAGE
def SUBSET_DROP_IMAGE : thm := BLiftDrop1.SUBSET_DROP_IMAGE
def DROP_IN_IMAGE_DROP : thm := BLiftDrop1.DROP_IN_IMAGE_DROP
def LIFT_NUM : thm := BLiftDrop1.LIFT_NUM
def LIFT_ADD : thm := BLiftDrop1.LIFT_ADD
def LIFT_SUB : thm := BLiftDrop1.LIFT_SUB
def LIFT_CMUL : thm := BLiftDrop1.LIFT_CMUL
def LIFT_NEG : thm := BLiftDrop1.LIFT_NEG
def LIFT_EQ_CMUL : thm := BLiftDrop1.LIFT_EQ_CMUL
def SUM_VSUM : thm := BLiftDrop1.SUM_VSUM
def VSUM_REAL : thm := BLiftDrop1.VSUM_REAL
def LIFT_SUM : thm := BLiftDrop1.LIFT_SUM
def DROP_VSUM : thm := BLiftDrop1.DROP_VSUM
def DROP_LAMBDA : thm := BLiftDrop1.DROP_LAMBDA
def DROP_VEC : thm := BLiftDrop1.DROP_VEC
def DROP_ADD : thm := BLiftDrop1.DROP_ADD
-- LiftDrop2 (vectors.ml 4000-4128)
def DROP_SUB : thm := BLiftDrop2.DROP_SUB
def DROP_CMUL : thm := BLiftDrop2.DROP_CMUL
def DROP_NEG : thm := BLiftDrop2.DROP_NEG
def NORM_1 : thm := BLiftDrop2.NORM_1
def DIST_1 : thm := BLiftDrop2.DIST_1
def NORM_1_POS : thm := BLiftDrop2.NORM_1_POS
def NORM_LIFT : thm := BLiftDrop2.NORM_LIFT
def DIST_LIFT : thm := BLiftDrop2.DIST_LIFT
def ABS_DROP : thm := BLiftDrop2.ABS_DROP
def LINEAR_VMUL_DROP : thm := BLiftDrop2.LINEAR_VMUL_DROP
def LINEAR_FROM_REALS : thm := BLiftDrop2.LINEAR_FROM_REALS
def LINEAR_TO_REALS : thm := BLiftDrop2.LINEAR_TO_REALS
def LINEAR_FROM_1 : thm := BLiftDrop2.LINEAR_FROM_1
def DROP_EQ_0 : thm := BLiftDrop2.DROP_EQ_0
def DROP_WLOG_LE : thm := BLiftDrop2.DROP_WLOG_LE
def IMAGE_LIFT_UNIV : thm := BLiftDrop2.IMAGE_LIFT_UNIV
def IMAGE_DROP_UNIV : thm := BLiftDrop2.IMAGE_DROP_UNIV
def LINEAR_LIFT_DOT : thm := BLiftDrop2.LINEAR_LIFT_DOT
def LINEAR_TO_1 : thm := BLiftDrop2.LINEAR_TO_1
def LINEAR_LIFT_COMPONENT : thm := BLiftDrop2.LINEAR_LIFT_COMPONENT
def BILINEAR_DROP_MUL : thm := BLiftDrop2.BILINEAR_DROP_MUL
def BILINEAR_MUL_DROP : thm := BLiftDrop2.BILINEAR_MUL_DROP
def BILINEAR_LIFT_MUL : thm := BLiftDrop2.BILINEAR_LIFT_MUL
def LINEAR_COMPONENTWISE : thm := BLiftDrop2.LINEAR_COMPONENTWISE
def DROP_BASIS : thm := BLiftDrop2.DROP_BASIS
-- Paste1 (vectors.ml 4130-4398)
def indicator : thm := BPaste1.indicator
def DROP_INDICATOR : thm := BPaste1.DROP_INDICATOR
def DROP_INDICATOR_POS_LE : thm := BPaste1.DROP_INDICATOR_POS_LE
def DROP_INDICATOR_LE_1 : thm := BPaste1.DROP_INDICATOR_LE_1
def DROP_INDICATOR_ABS_LE_1 : thm := BPaste1.DROP_INDICATOR_ABS_LE_1
def INDICATOR_COMPLEMENT : thm := BPaste1.INDICATOR_COMPLEMENT
def VECTORIZE_ADD : thm := BPaste1.VECTORIZE_ADD
def VECTORIZE_CMUL : thm := BPaste1.VECTORIZE_CMUL
def VECTORIZE_SUB : thm := BPaste1.VECTORIZE_SUB
def VECTORIZE_0 : thm := BPaste1.VECTORIZE_0
def MATRIFY_0 : thm := BPaste1.MATRIFY_0
def VECTORIZE_EQ_0 : thm := BPaste1.VECTORIZE_EQ_0
def MATRIFY_ADD : thm := BPaste1.MATRIFY_ADD
def MATRIFY_CMUL : thm := BPaste1.MATRIFY_CMUL
def MATRIFY_SUB : thm := BPaste1.MATRIFY_SUB
def MATRIFY_EQ_0 : thm := BPaste1.MATRIFY_EQ_0
def BILINEAR_MATRIX_VECTOR_MUL : thm := BPaste1.BILINEAR_MATRIX_VECTOR_MUL
def BILINEAR_MATRIX_MUL : thm := BPaste1.BILINEAR_MATRIX_MUL
def LINEAR_FSTCART : thm := BPaste1.LINEAR_FSTCART
def LINEAR_SNDCART : thm := BPaste1.LINEAR_SNDCART
def FSTCART_VEC : thm := BPaste1.FSTCART_VEC
def FSTCART_ADD : thm := BPaste1.FSTCART_ADD
def FSTCART_CMUL : thm := BPaste1.FSTCART_CMUL
def FSTCART_NEG : thm := BPaste1.FSTCART_NEG
def FSTCART_SUB : thm := BPaste1.FSTCART_SUB
def FSTCART_VSUM : thm := BPaste1.FSTCART_VSUM
def SNDCART_VEC : thm := BPaste1.SNDCART_VEC
def SNDCART_ADD : thm := BPaste1.SNDCART_ADD
def SNDCART_CMUL : thm := BPaste1.SNDCART_CMUL
def SNDCART_NEG : thm := BPaste1.SNDCART_NEG
def SNDCART_SUB : thm := BPaste1.SNDCART_SUB
def SNDCART_VSUM : thm := BPaste1.SNDCART_VSUM
def PASTECART_VEC : thm := BPaste1.PASTECART_VEC
def PASTECART_ADD : thm := BPaste1.PASTECART_ADD
def PASTECART_CMUL : thm := BPaste1.PASTECART_CMUL
def PASTECART_NEG : thm := BPaste1.PASTECART_NEG
def PASTECART_SUB : thm := BPaste1.PASTECART_SUB
def PASTECART_VSUM : thm := BPaste1.PASTECART_VSUM
def PASTECART_EQ_VEC : thm := BPaste1.PASTECART_EQ_VEC
def FSTCART_SNDCART_MAT_ZERO : thm := BPaste1.FSTCART_SNDCART_MAT_ZERO
def FSTCART_SNDCART_MATRIX_ADD : thm := BPaste1.FSTCART_SNDCART_MATRIX_ADD
def NORM_FSTCART : thm := BPaste1.NORM_FSTCART
def DIST_FSTCART : thm := BPaste1.DIST_FSTCART
def NORM_SNDCART : thm := BPaste1.NORM_SNDCART
def DIST_SNDCART : thm := BPaste1.DIST_SNDCART
def DOT_PASTECART : thm := BPaste1.DOT_PASTECART
def SQNORM_PASTECART : thm := BPaste1.SQNORM_PASTECART
def NORM_PASTECART : thm := BPaste1.NORM_PASTECART
-- Dropout (vectors.ml 4400-4600)
def NORM_PASTECART_LE : thm := BDropout.NORM_PASTECART_LE
def DIST_PASTECART_LE : thm := BDropout.DIST_PASTECART_LE
def NORM_LE_PASTECART : thm := BDropout.NORM_LE_PASTECART
def DIST_LE_PASTECART : thm := BDropout.DIST_LE_PASTECART
def NORM_PASTECART_0 : thm := BDropout.NORM_PASTECART_0
def DIST_PASTECART_CANCEL : thm := BDropout.DIST_PASTECART_CANCEL
def LINEAR_PASTECART : thm := BDropout.LINEAR_PASTECART
def LINEAR_PASTECART_EQ : thm := BDropout.LINEAR_PASTECART_EQ
def dropout : thm := BDropout.dropout
def pushin : thm := BDropout.pushin
def DROPOUT_PUSHIN : thm := BDropout.DROPOUT_PUSHIN
def PUSHIN_DROPOUT : thm := BDropout.PUSHIN_DROPOUT
def DROPOUT_GALOIS : thm := BDropout.DROPOUT_GALOIS
def IN_IMAGE_DROPOUT : thm := BDropout.IN_IMAGE_DROPOUT
def DROPOUT_EQ : thm := BDropout.DROPOUT_EQ
def DROPOUT_0 : thm := BDropout.DROPOUT_0
def DOT_DROPOUT : thm := BDropout.DOT_DROPOUT
def DOT_PUSHIN : thm := BDropout.DOT_PUSHIN
def DROPOUT_ADD : thm := BDropout.DROPOUT_ADD
def DROPOUT_SUB : thm := BDropout.DROPOUT_SUB
def DROPOUT_MUL : thm := BDropout.DROPOUT_MUL
def LINEAR_DROPOUT : thm := BDropout.LINEAR_DROPOUT
def LINEAR_PUSHIN : thm := BDropout.LINEAR_PUSHIN
-- Subspace (vectors.ml 4604-4824)
def subspace : thm := BSubspace.subspace
def span : thm := BSubspace.span
def dependent : thm := BSubspace.dependent
def independent : thm := BSubspace.independent
def SUBSPACE_UNIV : thm := BSubspace.SUBSPACE_UNIV
def SUBSPACE_IMP_NONEMPTY : thm := BSubspace.SUBSPACE_IMP_NONEMPTY
def SUBSPACE_0 : thm := BSubspace.SUBSPACE_0
def SUBSPACE_ADD : thm := BSubspace.SUBSPACE_ADD
def SUBSPACE_MUL : thm := BSubspace.SUBSPACE_MUL
def SUBSPACE_MUL_EQ : thm := BSubspace.SUBSPACE_MUL_EQ
def SUBSPACE_NEG : thm := BSubspace.SUBSPACE_NEG
def SUBSPACE_NEG_EQ : thm := BSubspace.SUBSPACE_NEG_EQ
def SUBSPACE_SUB : thm := BSubspace.SUBSPACE_SUB
def SUBSPACE_VSUM : thm := BSubspace.SUBSPACE_VSUM
def SUBSPACE_LINEAR_IMAGE : thm := BSubspace.SUBSPACE_LINEAR_IMAGE
def SUBSPACE_LINEAR_PREIMAGE : thm := BSubspace.SUBSPACE_LINEAR_PREIMAGE
def SUBSPACE_TRIVIAL : thm := BSubspace.SUBSPACE_TRIVIAL
def SUBSPACE_INTER : thm := BSubspace.SUBSPACE_INTER
def SUBSPACE_INTERS : thm := BSubspace.SUBSPACE_INTERS
def LINEAR_INJECTIVE_0_SUBSPACE : thm := BSubspace.LINEAR_INJECTIVE_0_SUBSPACE
def SUBSPACE_UNION_CHAIN : thm := BSubspace.SUBSPACE_UNION_CHAIN
def SUBSPACE_PCROSS : thm := BSubspace.SUBSPACE_PCROSS
def SUBSPACE_PCROSS_EQ : thm := BSubspace.SUBSPACE_PCROSS_EQ
def SPAN_SPAN : thm := BSubspace.SPAN_SPAN
def SPAN_MONO : thm := BSubspace.SPAN_MONO
def SUBSPACE_SPAN : thm := BSubspace.SUBSPACE_SPAN
def NONEMPTY_SPAN : thm := BSubspace.NONEMPTY_SPAN
def SPAN_CLAUSES : thm := BSubspace.SPAN_CLAUSES
def SPAN_INDUCT : thm := BSubspace.SPAN_INDUCT
def SPAN_EMPTY : thm := BSubspace.SPAN_EMPTY
def INDEPENDENT_EMPTY : thm := BSubspace.INDEPENDENT_EMPTY
def INDEPENDENT_NONZERO : thm := BSubspace.INDEPENDENT_NONZERO
def INDEPENDENT_MONO : thm := BSubspace.INDEPENDENT_MONO
def DEPENDENT_MONO : thm := BSubspace.DEPENDENT_MONO
def SPAN_SUBSPACE : thm := BSubspace.SPAN_SUBSPACE
def SPAN_INDUCT_ALT : thm := BSubspace.SPAN_INDUCT_ALT
-- Span1 (vectors.ml 4826-5040)
def SPAN_SUPERSET : thm := BSpan1.SPAN_SUPERSET
def SPAN_INC : thm := BSpan1.SPAN_INC
def SPAN_UNION_SUBSET : thm := BSpan1.SPAN_UNION_SUBSET
def SPAN_UNIV : thm := BSpan1.SPAN_UNIV
def SPAN_0 : thm := BSpan1.SPAN_0
def SPAN_ADD : thm := BSpan1.SPAN_ADD
def SPAN_MUL : thm := BSpan1.SPAN_MUL
def SPAN_MUL_EQ : thm := BSpan1.SPAN_MUL_EQ
def SPAN_NEG : thm := BSpan1.SPAN_NEG
def SPAN_NEG_EQ : thm := BSpan1.SPAN_NEG_EQ
def SPAN_SUB : thm := BSpan1.SPAN_SUB
def SPAN_VSUM : thm := BSpan1.SPAN_VSUM
def SPAN_ADD_EQ : thm := BSpan1.SPAN_ADD_EQ
def SPAN_EQ_SELF : thm := BSpan1.SPAN_EQ_SELF
def SPAN_OF_SUBSPACE : thm := BSpan1.SPAN_OF_SUBSPACE
def SPAN_SUBSET_SUBSPACE : thm := BSpan1.SPAN_SUBSET_SUBSPACE
def SUBSPACE_TRANSLATION_SELF : thm := BSpan1.SUBSPACE_TRANSLATION_SELF
def SUBSPACE_TRANSLATION_SELF_EQ : thm := BSpan1.SUBSPACE_TRANSLATION_SELF_EQ
def SUBSPACE_SUMS : thm := BSpan1.SUBSPACE_SUMS
def SPAN_UNION : thm := BSpan1.SPAN_UNION
def SPAN_LINEAR_IMAGE : thm := BSpan1.SPAN_LINEAR_IMAGE
def DEPENDENT_LINEAR_IMAGE_EQ : thm := BSpan1.DEPENDENT_LINEAR_IMAGE_EQ
def DEPENDENT_LINEAR_IMAGE : thm := BSpan1.DEPENDENT_LINEAR_IMAGE
def INDEPENDENT_LINEAR_IMAGE_EQ : thm := BSpan1.INDEPENDENT_LINEAR_IMAGE_EQ
def SPAN_BREAKDOWN : thm := BSpan1.SPAN_BREAKDOWN
def SPAN_BREAKDOWN_EQ : thm := BSpan1.SPAN_BREAKDOWN_EQ
def SPAN_INSERT_0 : thm := BSpan1.SPAN_INSERT_0
def SPAN_SING : thm := BSpan1.SPAN_SING
def SPAN_2 : thm := BSpan1.SPAN_2
def SPAN_3 : thm := BSpan1.SPAN_3
-- Span2 (vectors.ml 5045-5270)
def IN_SPAN_INSERT : thm := BSpan2.IN_SPAN_INSERT
def IN_SPAN_DELETE : thm := BSpan2.IN_SPAN_DELETE
def EQ_SPAN_INSERT_EQ : thm := BSpan2.EQ_SPAN_INSERT_EQ
def SPAN_EXPLICIT : thm := BSpan2.SPAN_EXPLICIT
def DEPENDENT_EXPLICIT : thm := BSpan2.DEPENDENT_EXPLICIT
def DEPENDENT_FINITE : thm := BSpan2.DEPENDENT_FINITE
def SPAN_FINITE : thm := BSpan2.SPAN_FINITE
def SPAN_STDBASIS : thm := BSpan2.SPAN_STDBASIS
def HAS_SIZE_STDBASIS : thm := BSpan2.HAS_SIZE_STDBASIS
def FINITE_STDBASIS : thm := BSpan2.FINITE_STDBASIS
def CARD_STDBASIS : thm := BSpan2.CARD_STDBASIS
def IN_SPAN_IMAGE_BASIS : thm := BSpan2.IN_SPAN_IMAGE_BASIS
def INDEPENDENT_STDBASIS : thm := BSpan2.INDEPENDENT_STDBASIS
def INDEPENDENT_BASIS_IMAGE : thm := BSpan2.INDEPENDENT_BASIS_IMAGE
-- Dim1 (vectors.ml 5272-5478)
def dim : thm := BDim1.dim
def euclidean_matroid : thm := BDim1.euclidean_matroid
def EUCLIDEAN_MATROID : thm := BDim1.EUCLIDEAN_MATROID
def EUCLIDEAN_MATROID_INDEPENDENT : thm := BDim1.EUCLIDEAN_MATROID_INDEPENDENT
def EUCLIDEAN_MATROID_SPANNING : thm := BDim1.EUCLIDEAN_MATROID_SPANNING
def EUCLIDEAN_MATROID_SUBSPACE : thm := BDim1.EUCLIDEAN_MATROID_SUBSPACE
def EUCLIDEAN_MATROID_FINITE_DIMENSIONAL : thm := BDim1.EUCLIDEAN_MATROID_FINITE_DIMENSIONAL
def EUCLIDEAN_MATROID_DIMENSION : thm := BDim1.EUCLIDEAN_MATROID_DIMENSION
def EUCLIDEAN_MATROID_FINITE_DIM : thm := BDim1.EUCLIDEAN_MATROID_FINITE_DIM
def EUCLIDEAN_SUBMATROID : thm := BDim1.EUCLIDEAN_SUBMATROID
def EUCLIDEAN_MATROID_DIM : thm := BDim1.EUCLIDEAN_MATROID_DIM
def SPAN_EQ : thm := BDim1.SPAN_EQ
def SPAN_EQ_INSERT : thm := BDim1.SPAN_EQ_INSERT
def INDEPENDENT_INSERT : thm := BDim1.INDEPENDENT_INSERT
def SPAN_TRANS : thm := BDim1.SPAN_TRANS
def SPANNING_SUBSET_INDEPENDENT : thm := BDim1.SPANNING_SUBSET_INDEPENDENT
def EXCHANGE_LEMMA : thm := BDim1.EXCHANGE_LEMMA
def INDEPENDENT_SPAN_BOUND : thm := BDim1.INDEPENDENT_SPAN_BOUND
def INDEPENDENT_BOUND : thm := BDim1.INDEPENDENT_BOUND
def DEPENDENT_BIGGERSET : thm := BDim1.DEPENDENT_BIGGERSET
def INDEPENDENT_IMP_FINITE : thm := BDim1.INDEPENDENT_IMP_FINITE
def MAXIMAL_INDEPENDENT_SUBSET_EXTEND : thm := BDim1.MAXIMAL_INDEPENDENT_SUBSET_EXTEND
def MAXIMAL_INDEPENDENT_SUBSET : thm := BDim1.MAXIMAL_INDEPENDENT_SUBSET
def BASIS_EXISTS : thm := BDim1.BASIS_EXISTS
def BASIS_EXISTS_FINITE : thm := BDim1.BASIS_EXISTS_FINITE
def BASIS_SUBSPACE_EXISTS : thm := BDim1.BASIS_SUBSPACE_EXISTS
def INDEPENDENT_CARD_LE_DIM : thm := BDim1.INDEPENDENT_CARD_LE_DIM
def SPAN_CARD_GE_DIM : thm := BDim1.SPAN_CARD_GE_DIM
def BASIS_CARD_EQ_DIM : thm := BDim1.BASIS_CARD_EQ_DIM
def BASIS_HAS_SIZE_DIM : thm := BDim1.BASIS_HAS_SIZE_DIM
-- Dim2 (vectors.ml 5479-5672)
def DIM_SPAN : thm := BDim2.DIM_SPAN
def DIM_UNIQUE : thm := BDim2.DIM_UNIQUE
def DIM_LE_CARD : thm := BDim2.DIM_LE_CARD
def DIM_UNIV : thm := BDim2.DIM_UNIV
def DIM_SUBSET : thm := BDim2.DIM_SUBSET
def DIM_SUBSET_UNIV : thm := BDim2.DIM_SUBSET_UNIV
def BASIS_HAS_SIZE_UNIV : thm := BDim2.BASIS_HAS_SIZE_UNIV
def CARD_GE_DIM_INDEPENDENT : thm := BDim2.CARD_GE_DIM_INDEPENDENT
def CARD_LE_DIM_SPANNING : thm := BDim2.CARD_LE_DIM_SPANNING
def CARD_EQ_DIM : thm := BDim2.CARD_EQ_DIM
def INDEPENDENT_BOUND_GENERAL : thm := BDim2.INDEPENDENT_BOUND_GENERAL
def DEPENDENT_BIGGERSET_GENERAL : thm := BDim2.DEPENDENT_BIGGERSET_GENERAL
def DIM_INSERT_0 : thm := BDim2.DIM_INSERT_0
def DIM_EQ_CARD : thm := BDim2.DIM_EQ_CARD
def DEPENDENT_EQ_DIM_LT_CARD : thm := BDim2.DEPENDENT_EQ_DIM_LT_CARD
def INDEPENDENT_EQ_DIM_EQ_CARD : thm := BDim2.INDEPENDENT_EQ_DIM_EQ_CARD
def SUBSET_LE_DIM : thm := BDim2.SUBSET_LE_DIM
def SPAN_EQ_DIM : thm := BDim2.SPAN_EQ_DIM
def DIM_EMPTY : thm := BDim2.DIM_EMPTY
def DIM_INSERT : thm := BDim2.DIM_INSERT
def CHOOSE_SUBSPACE_OF_SUBSPACE : thm := BDim2.CHOOSE_SUBSPACE_OF_SUBSPACE
def SUBSPACE_EXISTS : thm := BDim2.SUBSPACE_EXISTS
def DIM_EQ_SPAN : thm := BDim2.DIM_EQ_SPAN
def DIM_EQ_FULL : thm := BDim2.DIM_EQ_FULL
def DIM_PSUBSET : thm := BDim2.DIM_PSUBSET
def LOWDIM_EXPAND_DIMENSION : thm := BDim2.LOWDIM_EXPAND_DIMENSION
def LOWDIM_EXPAND_BASIS : thm := BDim2.LOWDIM_EXPAND_BASIS
-- Explicit (vectors.ml 5674-5830)
def INDEPENDENT_EXPLICIT : thm := BExplicit.INDEPENDENT_EXPLICIT
def INDEPENDENT_SING : thm := BExplicit.INDEPENDENT_SING
def DEPENDENT_SING : thm := BExplicit.DEPENDENT_SING
def DEPENDENT_2 : thm := BExplicit.DEPENDENT_2
def DEPENDENT_3 : thm := BExplicit.DEPENDENT_3
def INDEPENDENT_2 : thm := BExplicit.INDEPENDENT_2
def INDEPENDENT_3 : thm := BExplicit.INDEPENDENT_3
def LINEAR_SUBSPACE_GRAPH : thm := BExplicit.LINEAR_SUBSPACE_GRAPH
def SPANS_IMAGE : thm := BExplicit.SPANS_IMAGE
def DIM_LINEAR_IMAGE_LE : thm := BExplicit.DIM_LINEAR_IMAGE_LE
def DIM_SING : thm := BExplicit.DIM_SING
def DIM_EQ_0 : thm := BExplicit.DIM_EQ_0
def SPANNING_SURJECTIVE_IMAGE : thm := BExplicit.SPANNING_SURJECTIVE_IMAGE
def INDEPENDENT_INJECTIVE_IMAGE_GEN : thm := BExplicit.INDEPENDENT_INJECTIVE_IMAGE_GEN
def INDEPENDENT_INJECTIVE_IMAGE : thm := BExplicit.INDEPENDENT_INJECTIVE_IMAGE
-- Extend (vectors.ml 5830-6070)
def VECTOR_SUB_PROJECT_ORTHOGONAL : thm := BExtend.VECTOR_SUB_PROJECT_ORTHOGONAL
def BASIS_ORTHOGONAL : thm := BExtend.BASIS_ORTHOGONAL
def ORTHOGONAL_BASIS_EXISTS : thm := BExtend.ORTHOGONAL_BASIS_EXISTS
def SPAN_SPECIAL_SCALE : thm := BExtend.SPAN_SPECIAL_SCALE
def LINEAR_INDEP_IMAGE_LEMMA : thm := BExtend.LINEAR_INDEP_IMAGE_LEMMA
def LINEAR_INDEPENDENT_EXTEND_LEMMA : thm := BExtend.LINEAR_INDEPENDENT_EXTEND_LEMMA
def LINEAR_INDEPENDENT_EXTEND : thm := BExtend.LINEAR_INDEPENDENT_EXTEND
-- LinEq (vectors.ml 6075-6233)
def SUBSPACE_KERNEL : thm := BLinEq.SUBSPACE_KERNEL
def LINEAR_EQ_0_SPAN : thm := BLinEq.LINEAR_EQ_0_SPAN
def LINEAR_EQ_0 : thm := BLinEq.LINEAR_EQ_0
def LINEAR_EQ : thm := BLinEq.LINEAR_EQ
def LINEAR_EQ_STDBASIS : thm := BLinEq.LINEAR_EQ_STDBASIS
def SUBSPACE_LINEAR_FIXED_POINTS : thm := BLinEq.SUBSPACE_LINEAR_FIXED_POINTS
def BILINEAR_EQ : thm := BLinEq.BILINEAR_EQ
def BILINEAR_EQ_STDBASIS : thm := BLinEq.BILINEAR_EQ_STDBASIS
def LEFT_INVERTIBLE_TRANSP : thm := BLinEq.LEFT_INVERTIBLE_TRANSP
def RIGHT_INVERTIBLE_TRANSP : thm := BLinEq.RIGHT_INVERTIBLE_TRANSP
def INVERTIBLE_TRANSP : thm := BLinEq.INVERTIBLE_TRANSP
def LINEAR_INJECTIVE_LEFT_INVERSE : thm := BLinEq.LINEAR_INJECTIVE_LEFT_INVERSE
def LINEAR_INJECTIVE_LEFT_INVERSE_EQ : thm := BLinEq.LINEAR_INJECTIVE_LEFT_INVERSE_EQ
def LINEAR_SURJECTIVE_RIGHT_INVERSE : thm := BLinEq.LINEAR_SURJECTIVE_RIGHT_INVERSE
def LINEAR_SURJECTIVE_RIGHT_INVERSE_EQ : thm := BLinEq.LINEAR_SURJECTIVE_RIGHT_INVERSE_EQ
-- MatInv (vectors.ml 6234-6324)
def MATRIX_LEFT_INVERTIBLE_INJECTIVE : thm := BMatInv.MATRIX_LEFT_INVERTIBLE_INJECTIVE
def MATRIX_LEFT_INVERTIBLE_KER : thm := BMatInv.MATRIX_LEFT_INVERTIBLE_KER
def MATRIX_RIGHT_INVERTIBLE_SURJECTIVE : thm := BMatInv.MATRIX_RIGHT_INVERTIBLE_SURJECTIVE
def MATRIX_LEFT_INVERTIBLE_INDEPENDENT_COLUMNS : thm :=
  BMatInv.MATRIX_LEFT_INVERTIBLE_INDEPENDENT_COLUMNS
def MATRIX_RIGHT_INVERTIBLE_INDEPENDENT_ROWS : thm :=
  BMatInv.MATRIX_RIGHT_INVERTIBLE_INDEPENDENT_ROWS
def MATRIX_RIGHT_INVERTIBLE_SPAN_COLUMNS : thm := BMatInv.MATRIX_RIGHT_INVERTIBLE_SPAN_COLUMNS
def MATRIX_LEFT_INVERTIBLE_SPAN_ROWS : thm := BMatInv.MATRIX_LEFT_INVERTIBLE_SPAN_ROWS
-- Iso (vectors.ml 6329-6511)
def LINEAR_INJECTIVE_IMP_SURJECTIVE : thm := BIso.LINEAR_INJECTIVE_IMP_SURJECTIVE
def LINEAR_SURJECTIVE_IMP_INJECTIVE : thm := BIso.LINEAR_SURJECTIVE_IMP_INJECTIVE
def LINEAR_SURJECTIVE_IFF_INJECTIVE : thm := BIso.LINEAR_SURJECTIVE_IFF_INJECTIVE
def LEFT_RIGHT_INVERSE_EQ : thm := BIso.LEFT_RIGHT_INVERSE_EQ
def ISOMORPHISM_EXPAND : thm := BIso.ISOMORPHISM_EXPAND
def LINEAR_INJECTIVE_ISOMORPHISM : thm := BIso.LINEAR_INJECTIVE_ISOMORPHISM
def LINEAR_SURJECTIVE_ISOMORPHISM : thm := BIso.LINEAR_SURJECTIVE_ISOMORPHISM
def LINEAR_INVERSE_LEFT : thm := BIso.LINEAR_INVERSE_LEFT
def LEFT_INVERSE_LINEAR : thm := BIso.LEFT_INVERSE_LINEAR
def RIGHT_INVERSE_LINEAR : thm := BIso.RIGHT_INVERSE_LINEAR
def LEFT_RIGHT_INVERSE_LINEAR : thm := BIso.LEFT_RIGHT_INVERSE_LINEAR
def LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE : thm := BIso.LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE
def LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE_EQ : thm := BIso.LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE_EQ
def LINEAR_INJECTIVE_LEFT_RIGHT_INVERSE_EQ : thm := BIso.LINEAR_INJECTIVE_LEFT_RIGHT_INVERSE_EQ
def LINEAR_SURJECTIVE_LEFT_RIGHT_INVERSE_EQ : thm :=
  BIso.LINEAR_SURJECTIVE_LEFT_RIGHT_INVERSE_EQ
-- MatInv2 (vectors.ml 6516-6699)
def MATRIX_LEFT_RIGHT_INVERSE : thm := BMatInv2.MATRIX_LEFT_RIGHT_INVERSE
def MATRIX_LEFT_INVERTIBLE : thm := BMatInv2.MATRIX_LEFT_INVERTIBLE
def MATRIX_RIGHT_INVERTIBLE : thm := BMatInv2.MATRIX_RIGHT_INVERTIBLE
def INVERTIBLE_LEFT_INVERSE : thm := BMatInv2.INVERTIBLE_LEFT_INVERSE
def INVERTIBLE_RIGHT_INVERSE : thm := BMatInv2.INVERTIBLE_RIGHT_INVERSE
def MATRIX_INVERTIBLE : thm := BMatInv2.MATRIX_INVERTIBLE
def INVERTIBLE_EQ_INJECTIVE_AND_SURJECTIVE : thm :=
  BMatInv2.INVERTIBLE_EQ_INJECTIVE_AND_SURJECTIVE
def LINEAR_INVERTIBLE_BOUNDED_BELOW_POS : thm := BMatInv2.LINEAR_INVERTIBLE_BOUNDED_BELOW_POS
def LINEAR_INVERTIBLE_BOUNDED_BELOW : thm := BMatInv2.LINEAR_INVERTIBLE_BOUNDED_BELOW
def LINEAR_INJECTIVE_BOUNDED_BELOW_POS : thm := BMatInv2.LINEAR_INJECTIVE_BOUNDED_BELOW_POS
def DIM_INJECTIVE_LINEAR_IMAGE : thm := BMatInv2.DIM_INJECTIVE_LINEAR_IMAGE
def LINEAR_INJECTIVE_DIMINDEX_LE : thm := BMatInv2.LINEAR_INJECTIVE_DIMINDEX_LE
def LINEAR_SURJECTIVE_DIMINDEX_LE : thm := BMatInv2.LINEAR_SURJECTIVE_DIMINDEX_LE
def LINEAR_BIJECTIVE_DIMINDEX_EQ : thm := BMatInv2.LINEAR_BIJECTIVE_DIMINDEX_EQ
def INVERTIBLE_IMP_SQUARE_MATRIX : thm := BMatInv2.INVERTIBLE_IMP_SQUARE_MATRIX
-- RowSpace (vectors.ml 6703-6828)
def rowvector : thm := BRowSpace.rowvector
def columnvector : thm := BRowSpace.columnvector
def TRANSP_COLUMNVECTOR : thm := BRowSpace.TRANSP_COLUMNVECTOR
def TRANSP_ROWVECTOR : thm := BRowSpace.TRANSP_ROWVECTOR
def DOT_ROWVECTOR_COLUMNVECTOR : thm := BRowSpace.DOT_ROWVECTOR_COLUMNVECTOR
def DOT_MATRIX_PRODUCT : thm := BRowSpace.DOT_MATRIX_PRODUCT
def DOT_MATRIX_VECTOR_MUL : thm := BRowSpace.DOT_MATRIX_VECTOR_MUL
def MATRIX_VECTOR_MUL_IN_COLUMNSPACE : thm := BRowSpace.MATRIX_VECTOR_MUL_IN_COLUMNSPACE
def SUBSPACE_ORTHOGONAL_TO_VECTOR : thm := BRowSpace.SUBSPACE_ORTHOGONAL_TO_VECTOR
def SUBSPACE_ORTHOGONAL_TO_VECTORS : thm := BRowSpace.SUBSPACE_ORTHOGONAL_TO_VECTORS
def ORTHOGONAL_TO_SPAN : thm := BRowSpace.ORTHOGONAL_TO_SPAN
def ORTHOGONAL_TO_SPAN_EQ : thm := BRowSpace.ORTHOGONAL_TO_SPAN_EQ
def ORTHOGONAL_TO_SPANS_EQ : thm := BRowSpace.ORTHOGONAL_TO_SPANS_EQ
def ORTHOGONAL_NULLSPACE_ROWSPACE : thm := BRowSpace.ORTHOGONAL_NULLSPACE_ROWSPACE
def NULLSPACE_INTER_ROWSPACE : thm := BRowSpace.NULLSPACE_INTER_ROWSPACE
def MATRIX_VECTOR_MUL_INJECTIVE_ON_ROWSPACE : thm :=
  BRowSpace.MATRIX_VECTOR_MUL_INJECTIVE_ON_ROWSPACE
def DIM_ROWS_LE_DIM_COLUMNS : thm := BRowSpace.DIM_ROWS_LE_DIM_COLUMNS
-- Rank (vectors.ml 6830-6995)
def rank : thm := BRank.rank
def RANK_ROW : thm := BRank.RANK_ROW
def RANK_TRANSP : thm := BRank.RANK_TRANSP
def MATRIX_VECTOR_MUL_BASIS : thm := BRank.MATRIX_VECTOR_MUL_BASIS
def COLUMNS_IMAGE_BASIS : thm := BRank.COLUMNS_IMAGE_BASIS
def RANK_DIM_IM : thm := BRank.RANK_DIM_IM
def RANK_BOUND : thm := BRank.RANK_BOUND
def FULL_RANK_INJECTIVE : thm := BRank.FULL_RANK_INJECTIVE
def FULL_RANK_SURJECTIVE : thm := BRank.FULL_RANK_SURJECTIVE
def RANK_I : thm := BRank.RANK_I
def MATRIX_FULL_LINEAR_EQUATIONS : thm := BRank.MATRIX_FULL_LINEAR_EQUATIONS
def MATRIX_NONFULL_LINEAR_EQUATIONS_EQ : thm := BRank.MATRIX_NONFULL_LINEAR_EQUATIONS_EQ
def MATRIX_NONFULL_LINEAR_EQUATIONS : thm := BRank.MATRIX_NONFULL_LINEAR_EQUATIONS
def MATRIX_TRIVIAL_LINEAR_EQUATIONS : thm := BRank.MATRIX_TRIVIAL_LINEAR_EQUATIONS
def RANK_EQ_0 : thm := BRank.RANK_EQ_0
def RANK_0 : thm := BRank.RANK_0
def RANK_MUL_LE_RIGHT : thm := BRank.RANK_MUL_LE_RIGHT
def RANK_MUL_LE_LEFT : thm := BRank.RANK_MUL_LE_LEFT
def SPAN_COLUMNSPACE : thm := BRank.SPAN_COLUMNSPACE
def MATRIX_AUGMENTED_LINEAR_EQUATIONS : thm := BRank.MATRIX_AUGMENTED_LINEAR_EQUATIONS
-- ONormMat (vectors.ml 6999-7107)
def NORM_COLUMN_LE_ONORM : thm := BONormMat.NORM_COLUMN_LE_ONORM
def MATRIX_COMPONENT_LE_ONORM : thm := BONormMat.MATRIX_COMPONENT_LE_ONORM
def COMPONENT_LE_ONORM : thm := BONormMat.COMPONENT_LE_ONORM
def ONORM_LE_MATRIX_COMPONENT_SUM : thm := BONormMat.ONORM_LE_MATRIX_COMPONENT_SUM
def ONORM_LE_MATRIX_COMPONENT : thm := BONormMat.ONORM_LE_MATRIX_COMPONENT
def MATRIX_RATIONAL_APPROXIMATION : thm := BONormMat.MATRIX_RATIONAL_APPROXIMATION
-- Hyperplane (vectors.ml 7113-7240)
def HYPERPLANE_EQ_EMPTY : thm := BHyperplane.HYPERPLANE_EQ_EMPTY
def HYPERPLANE_EQ_UNIV : thm := BHyperplane.HYPERPLANE_EQ_UNIV
def HALFSPACE_EQ_EMPTY_LT : thm := BHyperplane.HALFSPACE_EQ_EMPTY_LT
def HALFSPACE_EQ_EMPTY_GT : thm := BHyperplane.HALFSPACE_EQ_EMPTY_GT
def HALFSPACE_EQ_EMPTY_LE : thm := BHyperplane.HALFSPACE_EQ_EMPTY_LE
def HALFSPACE_EQ_EMPTY_GE : thm := BHyperplane.HALFSPACE_EQ_EMPTY_GE
def ADJOINT_INJECTIVE : thm := BHyperplane.ADJOINT_INJECTIVE
def ADJOINT_SURJECTIVE : thm := BHyperplane.ADJOINT_SURJECTIVE
def ADJOINT_INJECTIVE_INJECTIVE : thm := BHyperplane.ADJOINT_INJECTIVE_INJECTIVE
def ADJOINT_INJECTIVE_INJECTIVE_0 : thm := BHyperplane.ADJOINT_INJECTIVE_INJECTIVE_0
def TRANSP_INJECTIVE : thm := BHyperplane.TRANSP_INJECTIVE
def TRANSP_SURJECTIVE : thm := BHyperplane.TRANSP_SURJECTIVE
def LINEAR_SINGULAR_INTO_HYPERPLANE : thm := BHyperplane.LINEAR_SINGULAR_INTO_HYPERPLANE
def LINEAR_SINGULAR_IMAGE_HYPERPLANE : thm := BHyperplane.LINEAR_SINGULAR_IMAGE_HYPERPLANE
-- Gram1 (vectors.ml 7243-7435)
def SPAN_DELETE_0 : thm := BGram1.SPAN_DELETE_0
def DIM_BASIS_IMAGE : thm := BGram1.DIM_BASIS_IMAGE
def SPAN_IMAGE_SCALE : thm := BGram1.SPAN_IMAGE_SCALE
def DIM_IMAGE_SCALE : thm := BGram1.DIM_IMAGE_SCALE
def PAIRWISE_ORTHOGONAL_INDEPENDENT : thm := BGram1.PAIRWISE_ORTHOGONAL_INDEPENDENT
def PAIRWISE_ORTHOGONAL_IMP_FINITE : thm := BGram1.PAIRWISE_ORTHOGONAL_IMP_FINITE
def GRAM_SCHMIDT_STEP : thm := BGram1.GRAM_SCHMIDT_STEP
def ORTHOGONAL_EXTENSION : thm := BGram1.ORTHOGONAL_EXTENSION
def ORTHOGONAL_EXTENSION_STRONG : thm := BGram1.ORTHOGONAL_EXTENSION_STRONG
def ORTHONORMAL_EXTENSION : thm := BGram1.ORTHONORMAL_EXTENSION
-- Gram2 (vectors.ml 7436-7532)
def VECTOR_IN_ORTHOGONAL_SPANNINGSET : thm := BGram2.VECTOR_IN_ORTHOGONAL_SPANNINGSET
def VECTOR_IN_ORTHOGONAL_BASIS : thm := BGram2.VECTOR_IN_ORTHOGONAL_BASIS
def VECTOR_IN_ORTHONORMAL_BASIS : thm := BGram2.VECTOR_IN_ORTHONORMAL_BASIS
def BESSEL_INEQUALITY : thm := BGram2.BESSEL_INEQUALITY
-- Gram3 (vectors.ml 7537-7745)
def ORTHOGONAL_SPANNINGSET_SUBSPACE : thm := BGram3.ORTHOGONAL_SPANNINGSET_SUBSPACE
def ORTHOGONAL_BASIS_SUBSPACE : thm := BGram3.ORTHOGONAL_BASIS_SUBSPACE
def ORTHONORMAL_BASIS_SUBSPACE : thm := BGram3.ORTHONORMAL_BASIS_SUBSPACE
def ORTHOGONAL_TO_SUBSPACE_EXISTS_GEN : thm := BGram3.ORTHOGONAL_TO_SUBSPACE_EXISTS_GEN
def ORTHOGONAL_TO_SUBSPACE_EXISTS : thm := BGram3.ORTHOGONAL_TO_SUBSPACE_EXISTS
def ORTHOGONAL_TO_VECTOR_EXISTS : thm := BGram3.ORTHOGONAL_TO_VECTOR_EXISTS
def SPAN_NOT_UNIV_ORTHOGONAL : thm := BGram3.SPAN_NOT_UNIV_ORTHOGONAL
def SPAN_NOT_UNIV_SUBSET_HYPERPLANE : thm := BGram3.SPAN_NOT_UNIV_SUBSET_HYPERPLANE
def LOWDIM_SUBSET_HYPERPLANE : thm := BGram3.LOWDIM_SUBSET_HYPERPLANE
def VECTOR_EQ_DOT_SPAN : thm := BGram3.VECTOR_EQ_DOT_SPAN
def ORTHONORMAL_BASIS_EXPAND : thm := BGram3.ORTHONORMAL_BASIS_EXPAND
def ORTHONORMAL_BASIS_EXPAND_DOT : thm := BGram3.ORTHONORMAL_BASIS_EXPAND_DOT
def ORTHONORMAL_BASIS_EXPAND_NORM : thm := BGram3.ORTHONORMAL_BASIS_EXPAND_NORM
-- IndepSub (vectors.ml 7750-7839)
def ORTHOGONAL_IMP_INDEPENDENT_SUBSPACES : thm := BIndepSub.ORTHOGONAL_IMP_INDEPENDENT_SUBSPACES
def INDEPENDENT_SUBSPACES_ALT : thm := BIndepSub.INDEPENDENT_SUBSPACES_ALT
def INDEPENDENT_SUBSPACES_0 : thm := BIndepSub.INDEPENDENT_SUBSPACES_0
def INDEPENDENT_SUBSPACES : thm := BIndepSub.INDEPENDENT_SUBSPACES
def ORTHOGONAL_SUBSPACE_DECOMP_UNIQUE : thm := BIndepSub.ORTHOGONAL_SUBSPACE_DECOMP_UNIQUE
def ORTHOGONAL_SUBSPACE_DECOMP_EXISTS : thm := BIndepSub.ORTHOGONAL_SUBSPACE_DECOMP_EXISTS
def ORTHOGONAL_SUBSPACE_DECOMP : thm := BIndepSub.ORTHOGONAL_SUBSPACE_DECOMP
-- Isometry (vectors.ml 7844-8027)
def ISOMETRY_SUBSET_SUBSPACE : thm := BIsometry.ISOMETRY_SUBSET_SUBSPACE
def ISOMETRIES_SUBSPACES : thm := BIsometry.ISOMETRIES_SUBSPACES
def ISOMETRY_SUBSPACES : thm := BIsometry.ISOMETRY_SUBSPACES
def ISOMETRY_UNIV_SUBSPACE : thm := BIsometry.ISOMETRY_UNIV_SUBSPACE
def ISOMETRY_UNIV_SUPERSET_SUBSPACE : thm := BIsometry.ISOMETRY_UNIV_SUPERSET_SUBSPACE
def ISOMETRY_UNIV_UNIV : thm := BIsometry.ISOMETRY_UNIV_UNIV
def SUBSPACE_ISOMORPHISM : thm := BIsometry.SUBSPACE_ISOMORPHISM
def ISOMORPHISMS_UNIV_UNIV : thm := BIsometry.ISOMORPHISMS_UNIV_UNIV
-- SpecHyper (vectors.ml 8032-8143)
def SUBSPACE_HYPERPLANE : thm := BSpecHyper.SUBSPACE_HYPERPLANE
def SUBSPACE_SPECIAL_HYPERPLANE : thm := BSpecHyper.SUBSPACE_SPECIAL_HYPERPLANE
def SPECIAL_HYPERPLANE_SPAN : thm := BSpecHyper.SPECIAL_HYPERPLANE_SPAN
def DIM_SPECIAL_HYPERPLANE : thm := BSpecHyper.DIM_SPECIAL_HYPERPLANE
def LOWDIM_EQ_INTER_HYPERPLANE : thm := BSpecHyper.LOWDIM_EQ_INTER_HYPERPLANE
def LOWDIM_EQ_HYPERPLANE : thm := BSpecHyper.LOWDIM_EQ_HYPERPLANE
-- DimKernel (vectors.ml 8149-8259)
def DIM_IMAGE_KERNEL_GEN : thm := BDimKernel.DIM_IMAGE_KERNEL_GEN
def DIM_IMAGE_KERNEL : thm := BDimKernel.DIM_IMAGE_KERNEL
-- DimSums (vectors.ml 8261-8516)
def DIM_SUMS_INTER : thm := BDimSums.DIM_SUMS_INTER
def DIM_UNION_INTER : thm := BDimSums.DIM_UNION_INTER
def DIM_KERNEL_COMPOSE : thm := BDimSums.DIM_KERNEL_COMPOSE
def DIM_ORTHOGONAL_SUM : thm := BDimSums.DIM_ORTHOGONAL_SUM
def DIM_SUBSPACE_ORTHOGONAL_TO_VECTORS : thm := BDimSums.DIM_SUBSPACE_ORTHOGONAL_TO_VECTORS
def DIM_SPECIAL_SUBSPACE : thm := BDimSums.DIM_SPECIAL_SUBSPACE
-- InjDim (vectors.ml 8518-8667)
def INDEPENDENT_UNION : thm := BInjDim.INDEPENDENT_UNION
def LINEAR_INJECTIVE_ON_IFF_DIM : thm := BInjDim.LINEAR_INJECTIVE_ON_IFF_DIM
def DIM_INJECTIVE_ON_LINEAR_IMAGE : thm := BInjDim.DIM_INJECTIVE_ON_LINEAR_IMAGE
def DIM_EQ_SUBSPACES : thm := BInjDim.DIM_EQ_SUBSPACES
def DIM_EQ_SUBSPACE : thm := BInjDim.DIM_EQ_SUBSPACE
def LINEAR_SURJECTIVE_ON_IFF_DIM : thm := BInjDim.LINEAR_SURJECTIVE_ON_IFF_DIM
def LINEAR_INJECTIVE_IMP_SURJECTIVE_ON : thm := BInjDim.LINEAR_INJECTIVE_IMP_SURJECTIVE_ON
def LINEAR_SURJECTIVE_IFF_INJECTIVE_ON : thm := BInjDim.LINEAR_SURJECTIVE_IFF_INJECTIVE_ON
def LINEAR_INJECTIVE_IFF_DIM : thm := BInjDim.LINEAR_INJECTIVE_IFF_DIM
def LINEAR_SURJECTIVE_IFF_DIM : thm := BInjDim.LINEAR_SURJECTIVE_IFF_DIM
def LINEAR_SURJECTIVE_IFF_INJECTIVE_GEN : thm := BInjDim.LINEAR_SURJECTIVE_IFF_INJECTIVE_GEN
def MATRIX_INVERTIBLE_LEFT_GEN : thm := BInjDim.MATRIX_INVERTIBLE_LEFT_GEN
def MATRIX_INVERTIBLE_LEFT : thm := BInjDim.MATRIX_INVERTIBLE_LEFT
def MATRIX_INVERTIBLE_RIGHT_GEN : thm := BInjDim.MATRIX_INVERTIBLE_RIGHT_GEN
def MATRIX_INVERTIBLE_RIGHT : thm := BInjDim.MATRIX_INVERTIBLE_RIGHT
-- PCrossDim (vectors.ml 8672-8793)
def PASTECART_AS_ORTHOGONAL_SUM : thm := BPCrossDim.PASTECART_AS_ORTHOGONAL_SUM
def PCROSS_AS_ORTHOGONAL_SUM : thm := BPCrossDim.PCROSS_AS_ORTHOGONAL_SUM
def DIM_PCROSS : thm := BPCrossDim.DIM_PCROSS
def SPAN_PCROSS_SUBSET : thm := BPCrossDim.SPAN_PCROSS_SUBSET
def SPAN_PCROSS : thm := BPCrossDim.SPAN_PCROSS
def DIM_PCROSS_STRONG : thm := BPCrossDim.DIM_PCROSS_STRONG
def SPAN_SUMS : thm := BPCrossDim.SPAN_SUMS
-- RankNull (vectors.ml 8798-8890)
def RANK_NULLSPACE : thm := BRankNull.RANK_NULLSPACE
def RANK_SYLVESTER : thm := BRankNull.RANK_SYLVESTER
def RANK_GRAM : thm := BRankNull.RANK_GRAM
def RANK_TRIANGLE : thm := BRankNull.RANK_TRIANGLE
def COVARIANCE_MATRIX_EQ_0 : thm := BRankNull.COVARIANCE_MATRIX_EQ_0
def MATRIX_MUL_COVARIANCE_LCANCEL : thm := BRankNull.MATRIX_MUL_COVARIANCE_LCANCEL
def MATRIX_MUL_COVARIANCE_RCANCEL : thm := BRankNull.MATRIX_MUL_COVARIANCE_RCANCEL
def MATRIX_VECTOR_MUL_COVARIANCE_EQ_0 : thm := BRankNull.MATRIX_VECTOR_MUL_COVARIANCE_EQ_0
-- MatPinv (vectors.ml 8898-9073)
def matrix_inv : thm := BMatPinv.matrix_inv
def MOORE_PENROSE_PSEUDOINVERSE : thm := BMatPinv.MOORE_PENROSE_PSEUDOINVERSE
def MOORE_PENROSE_PSEUDOINVERSE_UNIQUE : thm := BMatPinv.MOORE_PENROSE_PSEUDOINVERSE_UNIQUE
def MATRIX_INV_MUL_INNER : thm := BMatPinv.MATRIX_INV_MUL_INNER
def SYMMETRIC_MATRIX_INV_RMUL : thm := BMatPinv.SYMMETRIC_MATRIX_INV_RMUL
def MATRIX_INV_INV : thm := BMatPinv.MATRIX_INV_INV
def MATRIX_INV_EQ : thm := BMatPinv.MATRIX_INV_EQ
def MATRIX_INV_MUL_OUTER : thm := BMatPinv.MATRIX_INV_MUL_OUTER
def SYMMETRIC_MATRIX_INV_LMUL : thm := BMatPinv.SYMMETRIC_MATRIX_INV_LMUL
def MATRIX_INV_UNIQUE_STRONG : thm := BMatPinv.MATRIX_INV_UNIQUE_STRONG
def MATRIX_INV_TRANSP : thm := BMatPinv.MATRIX_INV_TRANSP
def TRANSP_MATRIX_INV : thm := BMatPinv.TRANSP_MATRIX_INV
def SYMMETRIC_MATRIX_INV : thm := BMatPinv.SYMMETRIC_MATRIX_INV
-- MatPinv2 (vectors.ml 9075-9236)
def MATRIX_INV_0 : thm := BMatPinv2.MATRIX_INV_0
def MATRIX_INV_EQ_0 : thm := BMatPinv2.MATRIX_INV_EQ_0
def MATRIX_INV_CMUL : thm := BMatPinv2.MATRIX_INV_CMUL
def MATRIX_INV : thm := BMatPinv2.MATRIX_INV
def MATRIX_INV_LEFT : thm := BMatPinv2.MATRIX_INV_LEFT
def MATRIX_INV_RIGHT : thm := BMatPinv2.MATRIX_INV_RIGHT
def MATRIX_MUL_LCANCEL : thm := BMatPinv2.MATRIX_MUL_LCANCEL
def MATRIX_MUL_RCANCEL : thm := BMatPinv2.MATRIX_MUL_RCANCEL
def RANK_INVERTIBLE_RMUL : thm := BMatPinv2.RANK_INVERTIBLE_RMUL
def RANK_INVERTIBLE_LMUL : thm := BMatPinv2.RANK_INVERTIBLE_LMUL
def RANK_CMUL : thm := BMatPinv2.RANK_CMUL
def RANK_NEG : thm := BMatPinv2.RANK_NEG
def MATRIX_INV_UNIQUE : thm := BMatPinv2.MATRIX_INV_UNIQUE
def MATRIX_INV_I : thm := BMatPinv2.MATRIX_INV_I
def INVERTIBLE_MATRIX_INV : thm := BMatPinv2.INVERTIBLE_MATRIX_INV
def MATRIX_INV_UNIQUE_LEFT : thm := BMatPinv2.MATRIX_INV_UNIQUE_LEFT
def MATRIX_INV_UNIQUE_RIGHT : thm := BMatPinv2.MATRIX_INV_UNIQUE_RIGHT
def MATRIX_INV_COVARIANCE : thm := BMatPinv2.MATRIX_INV_COVARIANCE
def COVARIANCE_MATRIX_INV : thm := BMatPinv2.COVARIANCE_MATRIX_INV
def NORMAL_MATRIX_INV : thm := BMatPinv2.NORMAL_MATRIX_INV
def MATRIX_INV_COVARIANCE_RMUL : thm := BMatPinv2.MATRIX_INV_COVARIANCE_RMUL
def MATRIX_INV_COVARIANCE_LMUL : thm := BMatPinv2.MATRIX_INV_COVARIANCE_LMUL
-- MatPinv3 (vectors.ml 9238-9396)
def RANK_SIMILAR : thm := BMatPinv3.RANK_SIMILAR
def RANK_MATRIX_INV : thm := BMatPinv3.RANK_MATRIX_INV
def RANK_MATRIX_INV_RMUL : thm := BMatPinv3.RANK_MATRIX_INV_RMUL
def RANK_MATRIX_INV_LMUL : thm := BMatPinv3.RANK_MATRIX_INV_LMUL
def MATRIX_INV_MULTIPLE_TRANP_RIGHT : thm := BMatPinv3.MATRIX_INV_MULTIPLE_TRANP_RIGHT
def MATRIX_TRANSP_MULTIPLE_INV_RIGHT : thm := BMatPinv3.MATRIX_TRANSP_MULTIPLE_INV_RIGHT
def MATRIX_INV_MULTIPLE_TRANP_LEFT : thm := BMatPinv3.MATRIX_INV_MULTIPLE_TRANP_LEFT
def MATRIX_TRANSP_MULTIPLE_INV_LEFT : thm := BMatPinv3.MATRIX_TRANSP_MULTIPLE_INV_LEFT
def MATRIX_VECTOR_MUL_INV_EQ_0 : thm := BMatPinv3.MATRIX_VECTOR_MUL_INV_EQ_0
def KERNEL_MATRIX_INV : thm := BMatPinv3.KERNEL_MATRIX_INV
def IMAGE_MATRIX_INV : thm := BMatPinv3.IMAGE_MATRIX_INV
def COMMUTING_MATRIX_INV_COVARIANCE : thm := BMatPinv3.COMMUTING_MATRIX_INV_COVARIANCE
def COMMUTING_MATRIX_INV_NORMAL : thm := BMatPinv3.COMMUTING_MATRIX_INV_NORMAL
def MATRIX_MUL_INV_EQ_0 : thm := BMatPinv3.MATRIX_MUL_INV_EQ_0
def MATRIX_INV_IDEMPOTENT : thm := BMatPinv3.MATRIX_INV_IDEMPOTENT
def IDEMPOTENT_MATRIX_MUL_LINV : thm := BMatPinv3.IDEMPOTENT_MATRIX_MUL_LINV
def IDEMPOTENT_MATRIX_MUL_RINV : thm := BMatPinv3.IDEMPOTENT_MATRIX_MUL_RINV
def MATRIX_INV_MUL_LINV : thm := BMatPinv3.MATRIX_INV_MUL_LINV
def MATRIX_INV_MUL_RINV : thm := BMatPinv3.MATRIX_INV_MUL_RINV
-- Infnorm (vectors.ml 9402-9590)
def infnorm : thm := BInfnorm.infnorm
def NUMSEG_DIMINDEX_NONEMPTY : thm := BInfnorm.NUMSEG_DIMINDEX_NONEMPTY
def INFNORM_SET_IMAGE : thm := BInfnorm.INFNORM_SET_IMAGE
def INFNORM_SET_LEMMA : thm := BInfnorm.INFNORM_SET_LEMMA
def INFNORM_POS_LE : thm := BInfnorm.INFNORM_POS_LE
def INFNORM_TRIANGLE : thm := BInfnorm.INFNORM_TRIANGLE
def INFNORM_EQ_0 : thm := BInfnorm.INFNORM_EQ_0
def INFNORM_0 : thm := BInfnorm.INFNORM_0
def INFNORM_NEG : thm := BInfnorm.INFNORM_NEG
def INFNORM_SUB : thm := BInfnorm.INFNORM_SUB
def REAL_ABS_SUB_INFNORM : thm := BInfnorm.REAL_ABS_SUB_INFNORM
def REAL_ABS_INFNORM : thm := BInfnorm.REAL_ABS_INFNORM
def COMPONENT_LE_INFNORM : thm := BInfnorm.COMPONENT_LE_INFNORM
def INFNORM_MUL_LEMMA : thm := BInfnorm.INFNORM_MUL_LEMMA
def INFNORM_MUL : thm := BInfnorm.INFNORM_MUL
def INFNORM_POS_LT : thm := BInfnorm.INFNORM_POS_LT
def INFNORM_LE_NORM : thm := BInfnorm.INFNORM_LE_NORM
def NORM_LE_INFNORM : thm := BInfnorm.NORM_LE_INFNORM
def NORM_CAUCHY_SCHWARZ_EQ : thm := BInfnorm.NORM_CAUCHY_SCHWARZ_EQ
def NORM_CAUCHY_SCHWARZ_ABS_EQ : thm := BInfnorm.NORM_CAUCHY_SCHWARZ_ABS_EQ
def NORM_TRIANGLE_EQ : thm := BInfnorm.NORM_TRIANGLE_EQ
def DIST_TRIANGLE_EQ : thm := BInfnorm.DIST_TRIANGLE_EQ
def NORM_CROSS_MULTIPLY : thm := BInfnorm.NORM_CROSS_MULTIPLY
-- Collinear (vectors.ml 9593-9808)
def collinear : thm := BCollinear.collinear
def COLLINEAR_ALT2 : thm := BCollinear.COLLINEAR_ALT2
def COLLINEAR_ALT : thm := BCollinear.COLLINEAR_ALT
def COLLINEAR_SUBSET : thm := BCollinear.COLLINEAR_SUBSET
def COLLINEAR_EMPTY : thm := BCollinear.COLLINEAR_EMPTY
def COLLINEAR_SING : thm := BCollinear.COLLINEAR_SING
def COLLINEAR_2 : thm := BCollinear.COLLINEAR_2
def COLLINEAR_SMALL : thm := BCollinear.COLLINEAR_SMALL
def COLLINEAR_3 : thm := BCollinear.COLLINEAR_3
def COLLINEAR_LEMMA : thm := BCollinear.COLLINEAR_LEMMA
def COLLINEAR_LEMMA_ALT : thm := BCollinear.COLLINEAR_LEMMA_ALT
def COLLINEAR_SPAN : thm := BCollinear.COLLINEAR_SPAN
def NORM_CAUCHY_SCHWARZ_EQUAL : thm := BCollinear.NORM_CAUCHY_SCHWARZ_EQUAL
def DOT_CAUCHY_SCHWARZ_EQUAL : thm := BCollinear.DOT_CAUCHY_SCHWARZ_EQUAL
def COLLINEAR_3_EXPAND : thm := BCollinear.COLLINEAR_3_EXPAND
def COLLINEAR_TRIPLES : thm := BCollinear.COLLINEAR_TRIPLES
def COLLINEAR_4_3 : thm := BCollinear.COLLINEAR_4_3
def COLLINEAR_3_TRANS : thm := BCollinear.COLLINEAR_3_TRANS
def ORTHOGONAL_TO_ORTHOGONAL_2D : thm := BCollinear.ORTHOGONAL_TO_ORTHOGONAL_2D
def COLLINEAR_3_2D : thm := BCollinear.COLLINEAR_3_2D
def COLLINEAR_3_DOT_MULTIPLES : thm := BCollinear.COLLINEAR_3_DOT_MULTIPLES
def ORTHOGONAL_AND_COLLINEAR : thm := BCollinear.ORTHOGONAL_AND_COLLINEAR
-- Between (vectors.ml 9813-10043)
def between : thm := BBetween.between
def BETWEEN_REFL : thm := BBetween.BETWEEN_REFL
def BETWEEN_REFL_EQ : thm := BBetween.BETWEEN_REFL_EQ
def BETWEEN_SYM : thm := BBetween.BETWEEN_SYM
def BETWEEN_ANTISYM : thm := BBetween.BETWEEN_ANTISYM
def BETWEEN_TRANS : thm := BBetween.BETWEEN_TRANS
def BETWEEN_TRANS_2 : thm := BBetween.BETWEEN_TRANS_2
def BETWEEN_TRANSLATION : thm := BBetween.BETWEEN_TRANSLATION
def BETWEEN_NORM : thm := BBetween.BETWEEN_NORM
def BETWEEN_DOT : thm := BBetween.BETWEEN_DOT
def BETWEEN_EXISTS_EXTENSION : thm := BBetween.BETWEEN_EXISTS_EXTENSION
def BETWEEN_IMP_COLLINEAR : thm := BBetween.BETWEEN_IMP_COLLINEAR
def BETWEEN_CMUL_LIFT : thm := BBetween.BETWEEN_CMUL_LIFT
def BETWEEN_1 : thm := BBetween.BETWEEN_1
def COLLINEAR_BETWEEN_CASES : thm := BBetween.COLLINEAR_BETWEEN_CASES
def COLLINEAR_BETWEEN_CASES_2 : thm := BBetween.COLLINEAR_BETWEEN_CASES_2
def BETWEEN_RESTRICTED_CASES : thm := BBetween.BETWEEN_RESTRICTED_CASES
def COLLINEAR_DIST_BETWEEN : thm := BBetween.COLLINEAR_DIST_BETWEEN
def BETWEEN_COLLINEAR_DIST_EQ : thm := BBetween.BETWEEN_COLLINEAR_DIST_EQ
def COLLINEAR_1 : thm := BBetween.COLLINEAR_1
def midpoint : thm := BBetween.midpoint
def MIDPOINT_REFL : thm := BBetween.MIDPOINT_REFL
def MIDPOINT_SYM : thm := BBetween.MIDPOINT_SYM
def DIST_MIDPOINT : thm := BBetween.DIST_MIDPOINT
def MIDPOINT_EQ_ENDPOINT : thm := BBetween.MIDPOINT_EQ_ENDPOINT
def BETWEEN_MIDPOINT : thm := BBetween.BETWEEN_MIDPOINT
def MIDPOINT_LINEAR_IMAGE : thm := BBetween.MIDPOINT_LINEAR_IMAGE
def COLLINEAR_MIDPOINT : thm := BBetween.COLLINEAR_MIDPOINT
def MIDPOINT_COLLINEAR : thm := BBetween.MIDPOINT_COLLINEAR
def MIDPOINT_BETWEEN : thm := BBetween.MIDPOINT_BETWEEN
def DROP_MIDPOINT : thm := BBetween.DROP_MIDPOINT
-- Interval (vectors.ml 10048-10248)
def open_interval : thm := BInterval.open_interval
def closed_interval : thm := BInterval.closed_interval
def interval : thm := BInterval.interval
def IN_INTERVAL : thm := BInterval.IN_INTERVAL
def IN_INTERVAL_REFLECT : thm := BInterval.IN_INTERVAL_REFLECT
def REFLECT_INTERVAL : thm := BInterval.REFLECT_INTERVAL
def INTERVAL_EQ_EMPTY : thm := BInterval.INTERVAL_EQ_EMPTY
def INTERVAL_NE_EMPTY : thm := BInterval.INTERVAL_NE_EMPTY
def SUBSET_INTERVAL_IMP : thm := BInterval.SUBSET_INTERVAL_IMP
def INTERVAL_SING : thm := BInterval.INTERVAL_SING
def SUBSET_INTERVAL : thm := BInterval.SUBSET_INTERVAL
def DISJOINT_INTERVAL : thm := BInterval.DISJOINT_INTERVAL
def ENDS_IN_INTERVAL : thm := BInterval.ENDS_IN_INTERVAL
def ENDS_IN_UNIT_INTERVAL : thm := BInterval.ENDS_IN_UNIT_INTERVAL
def INTER_INTERVAL : thm := BInterval.INTER_INTERVAL
def INTERVAL_OPEN_SUBSET_CLOSED : thm := BInterval.INTERVAL_OPEN_SUBSET_CLOSED
-- Invariance1 (vectors.ml 10250-10475)
def WLOG_LINEAR_INJECTIVE_IMAGE_2 : thm := BInvariance1.WLOG_LINEAR_INJECTIVE_IMAGE_2
def WLOG_LINEAR_INJECTIVE_IMAGE_2_ALT : thm := BInvariance1.WLOG_LINEAR_INJECTIVE_IMAGE_2_ALT
def WLOG_LINEAR_INJECTIVE_IMAGE : thm := BInvariance1.WLOG_LINEAR_INJECTIVE_IMAGE
def WLOG_LINEAR_INJECTIVE_IMAGE_ALT : thm := BInvariance1.WLOG_LINEAR_INJECTIVE_IMAGE_ALT
def LINEAR_INVARIANT_RULE (th : thm) : ExceptT String IO thm :=
  BInvariance1.LINEAR_INVARIANT_RULE th
def SUBSPACE_LINEAR_IMAGE_EQ : thm := BInvariance1.SUBSPACE_LINEAR_IMAGE_EQ
def invariant_under_linear : IO.Ref (List thm) := BInvariance1.invariant_under_linear
def invariant_under_translation : IO.Ref (List thm) := BInvariance1.invariant_under_translation
def scaling_theorems : IO.Ref (List thm) := BInvariance1.scaling_theorems
def COUNTABLE_UNION_OF_BIJECTIVE_IMAGE : thm := BInvariance1.COUNTABLE_UNION_OF_BIJECTIVE_IMAGE
def COUNTABLE_INTERSECTION_OF_BIJECTIVE_IMAGE : thm :=
  BInvariance1.COUNTABLE_INTERSECTION_OF_BIJECTIVE_IMAGE
def AFFINITY_SCALING_TRANSLATION : thm := BInvariance1.AFFINITY_SCALING_TRANSLATION
def LINEAR_SCALING : thm := BInvariance1.LINEAR_SCALING
def INJECTIVE_SCALING : thm := BInvariance1.INJECTIVE_SCALING
def SURJECTIVE_SCALING : thm := BInvariance1.SURJECTIVE_SCALING
def SCALING_INVARIANT (th : thm) : ExceptT String IO thm := BInvariance1.SCALING_INVARIANT th
def add_scaling_theorems (thl : List thm) : ExceptT String IO Unit :=
  BInvariance1.add_scaling_theorems thl
def add_linear_invariants (thl : List thm) : ExceptT String IO Unit :=
  BInvariance1.add_linear_invariants thl
def add_translation_invariants (thl : List thm) : ExceptT String IO Unit :=
  BInvariance1.add_translation_invariants thl
-- Invariance2 (vectors.ml 10505-10617)
def SAME_NORM_SAME_DOT : thm := BInvariance2.SAME_NORM_SAME_DOT
def PRESERVES_NORM_PRESERVES_DOT : thm := BInvariance2.PRESERVES_NORM_PRESERVES_DOT
def PRESEVES_NORM_PRESERVES_DIST : thm := BInvariance2.PRESEVES_NORM_PRESERVES_DIST
def PRESERVES_NORM_INJECTIVE : thm := BInvariance2.PRESERVES_NORM_INJECTIVE
def ORTHOGONAL_LINEAR_IMAGE_EQ : thm := BInvariance2.ORTHOGONAL_LINEAR_IMAGE_EQ
def NORMAL_MATRIX_IFF_SAME_NORM_TRANSP : thm := BInvariance2.NORMAL_MATRIX_IFF_SAME_NORM_TRANSP
def NORMAL_MATRIX_IFF_SAME_DOT_TRANSP : thm := BInvariance2.NORMAL_MATRIX_IFF_SAME_DOT_TRANSP
def NORMAL_MATRIX_KERNEL_TRANSP_EXPLICIT : thm :=
  BInvariance2.NORMAL_MATRIX_KERNEL_TRANSP_EXPLICIT
def NORMAL_MATRIX_KERNEL_TRANSP : thm := BInvariance2.NORMAL_MATRIX_KERNEL_TRANSP
-- Invariance3 (vectors.ml 10623-10797)
def MEM_TRANSLATION : thm := BInvariance3.MEM_TRANSLATION
def MEM_LINEAR_IMAGE : thm := BInvariance3.MEM_LINEAR_IMAGE
def QUANTIFY_SURJECTION_THM : thm := BInvariance3.QUANTIFY_SURJECTION_THM
def QUANTIFY_SURJECTION_HIGHER_THM : thm := BInvariance3.QUANTIFY_SURJECTION_HIGHER_THM
def PARTIAL_EXPAND_QUANTS_CONV (avoid : List String) (th : thm) :
    ExceptT String IO HolCore.Equal.ioconv :=
  BInvariance3.PARTIAL_EXPAND_QUANTS_CONV avoid th
def EXPAND_QUANTS_CONV (th : thm) : ExceptT String IO HolCore.Equal.ioconv :=
  BInvariance3.EXPAND_QUANTS_CONV th

/-- `needs "Multivariate/vectors.ml"`: already done by importing this module. -/
def ensureVectors : IO Unit := pure ()

end SessionMultiLib.Vectors
