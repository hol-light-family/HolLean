/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/infinite_places.ml                            . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/InfinitePlaces.lean

  The session half of the infinite_places.ml translation: it supplies HolANT.InfinitePlaces's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/infinite_places.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.InfinitePlaces
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Matroids
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionLibrary.FieldTheory
import SessionLibrary.Products
import SessionANT.IdealArith
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionANT.PowerBasis
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.NfValuation
import SessionANT.PrimeSplit
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.Integrality
import SessionLibrary.RingGroups
import SessionANT.FingenGroup
import SessionMultiLib.Misc
import SessionMultiLib.Metric
import SessionMultiLib.Homology
import SessionMultiLib.Vectors
import SessionMultiLib.Determinants
import SessionMultiLib.Topology
import SessionMultiLib.Convex
import SessionMultiLib.Paths
import SessionMultiLib.Polytope
import SessionMultiLib.Degree
import SessionMultiLib.Derivatives
import SessionMultiLib.Integration
import SessionMultiLib.Measure
import SessionMultiLib.ComplexAlgebra
import SessionMultiLib.Complexes
import SessionMultiLib.Canal
import SessionMultiLib.Transcendentals
import SessionMultiLib.RealAnalysis
import SessionMultiLib.MoreTop
import SessionMultiLib.Cauchy
import SessionMultiLib.ComplexRing
import SessionMultiLib.ComplexField
import SessionANT.ComplexEmbeddings

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.InfinitePlaces

/-- The core theorems infinite_places.ml uses. -/
def core1 : HolANT.InfinitePlaces.CoreThms1 where
  AND_FORALL_THM := Session.AND_FORALL_THM
  ARITH_EQ := Session.ARITH_EQ
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_DIFF := Session.CARD_DIFF
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_EQ_NSUM := Session.CARD_EQ_NSUM
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  CARD_SUBSET := Session.CARD_SUBSET
  CARD_SUBSET_EQ := Session.CARD_SUBSET_EQ
  CNJ_ADD := SessionMultiLib.ComplexAlgebra.«CNJ_ADD»
  CNJ_CNJ := SessionMultiLib.ComplexAlgebra.«CNJ_CNJ»
  CNJ_CX := SessionMultiLib.ComplexAlgebra.«CNJ_CX»
  CNJ_MUL := SessionMultiLib.ComplexAlgebra.«CNJ_MUL»
  CNJ_NEG := SessionMultiLib.ComplexAlgebra.«CNJ_NEG»
  CNJ_VSUM := SessionMultiLib.ComplexAlgebra.«CNJ_VSUM»
  COMPLEX_EMBEDDINGS_HAS_SIZE := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_HAS_SIZE»
  COMPLEX_EMBEDDINGS_MONOMORPHISM := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_MONOMORPHISM»
  COMPLEX_EMBEDDINGS_NONEMPTY := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_NONEMPTY»
  COMPLEX_EMBEDDINGS_ROOT_OF_UNITY := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_ROOT_OF_UNITY»
  COMPLEX_EQ := SessionMultiLib.ComplexAlgebra.«COMPLEX_EQ»
  COMPLEX_MUL_CNJ := SessionMultiLib.ComplexAlgebra.«COMPLEX_MUL_CNJ»
  COMPLEX_MUL_LID := SessionMultiLib.ComplexAlgebra.«COMPLEX_MUL_LID»
  COMPLEX_MUL_LNEG := SessionMultiLib.ComplexAlgebra.«COMPLEX_MUL_LNEG»
  COMPLEX_MUL_SYM := SessionMultiLib.ComplexAlgebra.«COMPLEX_MUL_SYM»
  COMPLEX_NORM_CNJ := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_CNJ»
  COMPLEX_NORM_CX := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_CX»
  COMPLEX_NORM_MUL := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_MUL»
  COMPLEX_NORM_NZ := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_NZ»
  COMPLEX_NORM_POW := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_POW»
  COMPLEX_NORM_ZERO := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_ZERO»
  COMPLEX_POW_2 := SessionMultiLib.ComplexAlgebra.«COMPLEX_POW_2»
  COMPLEX_RING_CLAUSES := SessionMultiLib.ComplexRing.«COMPLEX_RING_CLAUSES»
  COMPLEX_RING_OF_INT := SessionMultiLib.ComplexRing.«COMPLEX_RING_OF_INT»
  COMPLEX_RING_POW := SessionMultiLib.ComplexRing.«COMPLEX_RING_POW»
  COMPLEX_RING_PRODUCT := SessionMultiLib.ComplexRing.«COMPLEX_RING_PRODUCT»
  COMPLEX_RING_SUM := SessionMultiLib.ComplexRing.«COMPLEX_RING_SUM»
  COMPLEX_SQNORM := SessionMultiLib.ComplexAlgebra.«COMPLEX_SQNORM»
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  CX_ADD := SessionMultiLib.ComplexAlgebra.«CX_ADD»
  CX_INJ := SessionMultiLib.ComplexAlgebra.«CX_INJ»
  CX_MUL := SessionMultiLib.ComplexAlgebra.«CX_MUL»
  CX_NEG := SessionMultiLib.ComplexAlgebra.«CX_NEG»
  CX_POW := SessionMultiLib.ComplexAlgebra.«CX_POW»
  DIV_MULT := Session.DIV_MULT
  EQ_TRANS := Session.EQ_TRANS
  ETA_AX := Session.ETA_AX
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSION := Session.EXTENSION
  EXTENSIONAL := Session.EXTENSIONAL
  EXTENSIONAL_EQ := Session.EXTENSIONAL_EQ
  FIELD_COMPLEX_RING := SessionMultiLib.ComplexRing.«FIELD_COMPLEX_RING»
  FINITE_COMPLEX_EMBEDDINGS := SessionANT.ComplexEmbeddings.«FINITE_COMPLEX_EMBEDDINGS»
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FREE_BASIS_IN_CARRIER := SessionLibrary.RingDet.«FREE_BASIS_IN_CARRIER»
  FUN_EQ_THM := Session.FUN_EQ_THM
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_INDEX := Session.HAS_SIZE_INDEX
  IDEAL_GENERATED_INC_GEN := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC_GEN»
  IDEAL_GENERATED_SING_EQ_CARRIER := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING_EQ_CARRIER»
  IDEAL_NORM_CARRIER := SessionANT.IdealNorm.«IDEAL_NORM_CARRIER»
  IDEAL_NORM_GT_1 := SessionANT.IdealNorm.«IDEAL_NORM_GT_1»
  IM := SessionMultiLib.ComplexAlgebra.«IM»
  IMP_CONJ := Session.IMP_CONJ
  IM_ADD := SessionMultiLib.ComplexAlgebra.«IM_ADD»
  IM_CNJ := SessionMultiLib.ComplexAlgebra.«IM_CNJ»
  IM_CX := SessionMultiLib.ComplexAlgebra.«IM_CX»
  IM_NEG := SessionMultiLib.ComplexAlgebra.«IM_NEG»
  IN := Session.IN
  INJECTIVE_ON_LEFT_INVERSE := Session.INJECTIVE_ON_LEFT_INVERSE
  INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING»
  INTEGRAL_DOMAIN_RING_OF_INTEGERS := SessionANT.Numfield.«INTEGRAL_DOMAIN_RING_OF_INTEGERS»
  IN_DIFF := Session.IN_DIFF
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_EXTENSIONAL := Session.IN_EXTENSIONAL
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_SING := Session.IN_SING
  IN_UNIV := Session.IN_UNIV
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONO_AND := Session.MONO_AND
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_SYM := Session.MULT_SYM
  NORM_CPRODUCT := SessionMultiLib.ComplexAlgebra.«NORM_CPRODUCT»
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
/-- The core theorems infinite_places.ml uses. -/
def core2 : HolANT.InfinitePlaces.CoreThms2 where
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NSUM_ADD := Session.NSUM_ADD
  NSUM_CLAUSES := Session.NSUM_CLAUSES
  NSUM_CONST := Session.NSUM_CONST
  NSUM_EQ := Session.NSUM_EQ
  NSUM_IMAGE_GEN := Session.NSUM_IMAGE_GEN
  NSUM_RESTRICT_SET := Session.NSUM_RESTRICT_SET
  NSUM_SING := Session.NSUM_SING
  NUMBER_FIELD_DEGREE_POS := SessionANT.Numfield.«NUMBER_FIELD_DEGREE_POS»
  NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD := SessionANT.Discriminant.«NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD»
  NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS := SessionANT.PowerBasis.«NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS»
  NUMBER_FIELD_DISCRIMINANT_NONZERO := SessionANT.Discriminant.«NUMBER_FIELD_DISCRIMINANT_NONZERO»
  NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q := SessionANT.NormIndex.«NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_NORM_HOMOMORPHISMS := SessionANT.PowerBasis.«NUMBER_FIELD_NORM_HOMOMORPHISMS»
  NUMBER_FIELD_TRACE_HOMOMORPHISMS := SessionANT.PowerBasis.«NUMBER_FIELD_TRACE_HOMOMORPHISMS»
  PERMUTES_INVOLUTION := SessionLibrary.Permutations.«PERMUTES_INVOLUTION»
  PRODUCT_EQ_0 := SessionLibrary.Products.«PRODUCT_EQ_0»
  RE := SessionMultiLib.ComplexAlgebra.«RE»
  REAL := SessionMultiLib.ComplexAlgebra.«REAL»
  REAL_CNJ := SessionMultiLib.ComplexAlgebra.«REAL_CNJ»
  REAL_LE_SQUARE := Session.REAL_LE_SQUARE
  REAL_MUL_LZERO := Session.REAL_MUL_LZERO
  REAL_MUL_RZERO := Session.REAL_MUL_RZERO
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_POW2_ABS := Session.REAL_POW2_ABS
  REAL_POW_NEG := Session.REAL_POW_NEG
  REAL_POW_ONE := Session.REAL_POW_ONE
  REAL_RING_CLAUSES := SessionLibrary.RingTheory.«REAL_RING_CLAUSES»
  REAL_SUB_RZERO := Session.REAL_SUB_RZERO
  RESTRICTION := Session.RESTRICTION
  RESTRICTION_COMPOSE_RIGHT := Session.RESTRICTION_COMPOSE_RIGHT
  RESTRICTION_FIXPOINT := Session.RESTRICTION_FIXPOINT
  RESTRICTION_IN_EXTENSIONAL := Session.RESTRICTION_IN_EXTENSIONAL
  RESTRICTION_UNIQUE := Session.RESTRICTION_UNIQUE
  RESTRICTION_UNIQUE_ALT := Session.RESTRICTION_UNIQUE_ALT
  RE_ADD := SessionMultiLib.ComplexAlgebra.«RE_ADD»
  RE_CNJ := SessionMultiLib.ComplexAlgebra.«RE_CNJ»
  RE_CX := SessionMultiLib.ComplexAlgebra.«RE_CX»
  RE_NEG := SessionMultiLib.ComplexAlgebra.«RE_NEG»
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_CARRIER_SUBFIELD_GENERATED_SUBSET := SessionLibrary.FieldTheory.«RING_CARRIER_SUBFIELD_GENERATED_SUBSET»
  RING_DET_EQ := SessionLibrary.RingDet.«RING_DET_EQ»
  RING_DET_HOMOMORPHISM := SessionLibrary.RingDet.«RING_DET_HOMOMORPHISM»
  RING_DET_MUL := SessionLibrary.RingDet.«RING_DET_MUL»
  RING_DET_PERMUTE_ROWS := SessionLibrary.RingDet.«RING_DET_PERMUTE_ROWS»
  RING_DET_REINDEX := SessionLibrary.RingDet.«RING_DET_REINDEX»
  RING_DET_TRANSP := SessionLibrary.RingDet.«RING_DET_TRANSP»
  RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_CNJ := SessionMultiLib.ComplexRing.«RING_HOMOMORPHISM_CNJ»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_MONOMORPHISM_ALT_EQ := SessionLibrary.RingTheory.«RING_MONOMORPHISM_ALT_EQ»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_FREE := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE»
  RING_OF_INTEGERS_FREE_BASIS_FIELD := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE_BASIS_FIELD»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INTEGERS_UNIT_NONZERO := SessionANT.Numfield.«RING_OF_INTEGERS_UNIT_NONZERO»
  RING_UNIT_0 := SessionLibrary.RingTheory.«RING_UNIT_0»
  RING_UNIT_IN_CARRIER := SessionLibrary.RingTheory.«RING_UNIT_IN_CARRIER»
  SIGN_INVOLUTION := SessionLibrary.Permutations.«SIGN_INVOLUTION»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_RESTRICT := Session.SUBSET_RESTRICT
  SUBSET_UNIV := Session.SUBSET_UNIV
  SUM_CONST := Session.SUM_CONST
  SUM_EQ := Session.SUM_EQ
  SUM_IMAGE_GEN := Session.SUM_IMAGE_GEN
  UNIT_GROUP := SessionLibrary.RingGroups.«UNIT_GROUP»
  VSUM_EQ := SessionMultiLib.Vectors.«VSUM_EQ»
  VSUM_IMAGE := SessionMultiLib.Vectors.«VSUM_IMAGE»
  complex_embeddings := SessionANT.ComplexEmbeddings.«complex_embeddings»
  complex_mul := SessionMultiLib.ComplexAlgebra.«complex_mul»
  int_abs_th := Session.int_abs_th
  int_eq := Session.int_eq
  int_lt := Session.int_lt
  int_of_num_th := Session.int_of_num_th
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM
  real := SessionMultiLib.ComplexAlgebra.«real»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  ring_sign := SessionLibrary.RingDet.«ring_sign»
  sign := SessionLibrary.Permutations.«sign»

/-- What infinite_places.ml uses from Session. -/
def deps : HolANT.InfinitePlaces.InfinitePlacesDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  new_recursive_definition ax s := do
    ExceptT.mk (Session.new_recursive_definition ax (← HolLight.q s))
  LIST_INDUCT_TAC := Session.LIST_INDUCT_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  METIS_TAC := Session.METIS_TAC
  ASM_METIS_TAC := Session.ASM_METIS_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  TAUT t := ExceptT.mk (Session.TAUT t)
  ITAUT t := ExceptT.mk (Session.ITAUT t)
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH t)
  REAL_FIELD t := ExceptT.mk (Session.REAL_FIELD t)
  REAL_ARITH_TAC := Session.REAL_ARITH_TAC
  ASM_REAL_ARITH_TAC := Session.ASM_REAL_ARITH_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  INT_ARITH t := ExceptT.mk (Session.INT_ARITH t)
  INT_ARITH_TAC := Session.INT_ARITH_TAC
  ASM_INT_ARITH_TAC := Session.ASM_INT_ARITH_TAC
  INTEGER_RULE t := ExceptT.mk (Session.INTEGER_RULE t)
  INTEGER_TAC := Session.INTEGER_TAC
  NUMBER_RULE := Session.NUMBER_RULE
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  INT_REDUCE_CONV := Session.INT_REDUCE_CONV
  INT_RED_CONV := Session.INT_RED_CONV
  INT_REM_DOWN_CONV := Session.INT_REM_DOWN_CONV
  HAS_SIZE_CONV := Session.HAS_SIZE_CONV
  let_CONV := Session.let_CONV
  num_CONV := Session.num_CONV
  mk_numeral := Session.mk_numeral
  PRIME_CONV t := ExceptT.mk (SessionLibrary.Pocklington.PRIME_CONV t)
  PRIME_RULE := SessionLibrary.Pocklington.PRIME_RULE
  RING_RULE t := ExceptT.mk (SessionLibrary.RingTheory.RING_RULE t)
  INTEGRAL_DOMAIN_RULE t := ExceptT.mk (SessionLibrary.RingTheory.INTEGRAL_DOMAIN_RULE t)
  FIELD_TAC := SessionLibrary.RingTheory.FIELD_TAC
  RING_CARRIER_TAC := SessionLibrary.RingTheory.RING_CARRIER_TAC
  RING_TAC := SessionLibrary.RingTheory.RING_TAC
  RING_PULL_DIV_TAC := SessionLibrary.RingTheory.RING_PULL_DIV_TAC
  LET_TAC := Session.LET_TAC
  GROUP_RULE t := ExceptT.mk (SessionLibrary.GroupTheory.GROUP_RULE t)
  basic_ss := Session.basic_ss
  INTEGER_MOD_RING_RED_CONV := SessionLibrary.RingTheory.INTEGER_MOD_RING_RED_CONV
  NUM_SUB_CONV := Session.NUM_SUB_CONV
  REAL_RAT_REDUCE_CONV := Session.REAL_RAT_REDUCE_CONV
  NUM_EQ_CONV := Session.NUM_EQ_CONV
  NUM_DIV_CONV := Session.NUM_DIV_CONV
  EXP_MOD_CONV := Session.EXP_MOD_CONV
  EXPAND_CASES_CONV := Session.EXPAND_CASES_CONV
  DIVIDES_CONV := SessionLibrary.Prime.DIVIDES_CONV
  COPRIME_CONV := SessionLibrary.Prime.COPRIME_CONV
  REAL_RING t := ExceptT.mk (Session.REAL_RING t)
  COMPLEX_RING t := ExceptT.mk (SessionMultiLib.ComplexAlgebra.COMPLEX_RING t)
  core1 := core1
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in infinite_places.ml order. -/
initialize BInfinitePlaces01 : HolANT.InfinitePlaces.InfinitePlaces01 ←
  ioB "setupInfinitePlaces01" (HolANT.InfinitePlaces.setupInfinitePlaces01 deps).run
initialize BInfinitePlaces02 : HolANT.InfinitePlaces.InfinitePlaces02 ←
  ioB "setupInfinitePlaces02" (HolANT.InfinitePlaces.setupInfinitePlaces02 deps BInfinitePlaces01).run

-- InfinitePlaces01
def real_embeddings : thm := BInfinitePlaces01.real_embeddings
def infinite_places : thm := BInfinitePlaces01.infinite_places
def COMPLEX_EMBEDDINGS_CNJ : thm := BInfinitePlaces01.COMPLEX_EMBEDDINGS_CNJ
def COMPLEX_EMBEDDINGS_CNJ_CNJ : thm := BInfinitePlaces01.COMPLEX_EMBEDDINGS_CNJ_CNJ
def REAL_EMBEDDINGS_CNJ : thm := BInfinitePlaces01.REAL_EMBEDDINGS_CNJ
def COMPLEX_EMBEDDINGS_NORM_POS : thm := BInfinitePlaces01.COMPLEX_EMBEDDINGS_NORM_POS
def COMPLEX_EMBEDDINGS_NORM_MUL : thm := BInfinitePlaces01.COMPLEX_EMBEDDINGS_NORM_MUL
def COMPLEX_EMBEDDINGS_NORM_EQ : thm := BInfinitePlaces01.COMPLEX_EMBEDDINGS_NORM_EQ
def FINITE_INFINITE_PLACES : thm := BInfinitePlaces01.FINITE_INFINITE_PLACES
def CARD_INFINITE_PLACES : thm := BInfinitePlaces01.CARD_INFINITE_PLACES
def CARD_INFINITE_PLACES_EQ_1 : thm := BInfinitePlaces01.CARD_INFINITE_PLACES_EQ_1
def REAL_EMBEDDINGS_MONOMORPHISM : thm := BInfinitePlaces01.REAL_EMBEDDINGS_MONOMORPHISM
def COMPLEX_EMBEDDINGS_PRIME_SUBFIELD_REAL : thm := BInfinitePlaces01.COMPLEX_EMBEDDINGS_PRIME_SUBFIELD_REAL
def COMPLEX_EMBEDDINGS_NORM_FUN_EQ : thm := BInfinitePlaces01.COMPLEX_EMBEDDINGS_NORM_FUN_EQ
def INFINITE_PLACE_EMBEDDINGS : thm := BInfinitePlaces01.INFINITE_PLACE_EMBEDDINGS
def CARD_INFINITE_PLACE_EMBEDDINGS : thm := BInfinitePlaces01.CARD_INFINITE_PLACE_EMBEDDINGS
def INFINITE_PLACES_SUM : thm := BInfinitePlaces01.INFINITE_PLACES_SUM
def INFINITE_PLACES_DEGREE : thm := BInfinitePlaces01.INFINITE_PLACES_DEGREE
def INFINITE_PLACES_POS : thm := BInfinitePlaces01.INFINITE_PLACES_POS
def INFINITE_PLACES_MUL : thm := BInfinitePlaces01.INFINITE_PLACES_MUL
def INFINITE_PLACES_ROOT_OF_UNITY : thm := BInfinitePlaces01.INFINITE_PLACES_ROOT_OF_UNITY
def INFINITE_PLACES_UNIT_GROUP : thm := BInfinitePlaces01.INFINITE_PLACES_UNIT_GROUP
def NUMBER_FIELD_TRACE_COMPLEX_EMBEDDINGS : thm := BInfinitePlaces01.NUMBER_FIELD_TRACE_COMPLEX_EMBEDDINGS
def NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS : thm := BInfinitePlaces01.NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS
def NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS : thm := BInfinitePlaces01.NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS
def RING_OF_INTEGERS_UNIT_NORM_PRODUCT : thm := BInfinitePlaces01.RING_OF_INTEGERS_UNIT_NORM_PRODUCT
def NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS : thm := BInfinitePlaces01.NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS
def COMPLEX_EMBEDDINGS_VSUM_CNJ_REAL : thm := BInfinitePlaces01.COMPLEX_EMBEDDINGS_VSUM_CNJ_REAL
def NUMBER_FIELD_EMBEDDING_GRAM_DET : thm := BInfinitePlaces01.NUMBER_FIELD_EMBEDDING_GRAM_DET

-- InfinitePlaces02
def NUMBER_FIELD_DISCRIMINANT_SIGN : thm := BInfinitePlaces02.NUMBER_FIELD_DISCRIMINANT_SIGN

/-- `needs "ANT/infinite_places.ml"`: already done by importing this module. -/
def ensureInfinitePlaces : IO Unit := pure ()

end SessionANT.InfinitePlaces
