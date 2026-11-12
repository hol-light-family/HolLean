/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/hermite.ml                                    . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/Hermite.lean

  The session half of the hermite.ml translation: it supplies HolANT.Hermite's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/hermite.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.Hermite
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
import SessionLibrary.Isum
import SessionLibrary.Products
import SessionANT.IdealArith
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionLibrary.Floor
import SessionANT.Zlattice
import SessionANT.LinearForms
import SessionANT.HermiteInequality
import SessionANT.Numfield
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.Discriminant
import SessionANT.PrimeSplit
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.RelativeDegree
import SessionANT.NfValuation
import SessionANT.Integrality
import SessionANT.DedekindKummer
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
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
import SessionANT.PowerBasis
import SessionANT.InfinitePlaces
import SessionANT.ClassgroupGroup
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.Quadratic
import SessionANT.MinkowskiTheory

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.Hermite

/-- The core theorems hermite.ml uses. -/
def core1 : HolANT.Hermite.CoreThms1 where
  AGM_ROOT := SessionMultiLib.RealAnalysis.«AGM_ROOT»
  ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING := SessionMultiLib.ComplexField.«ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING»
  CARD_DELETE := Session.CARD_DELETE
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  CARD_SING := Session.CARD_SING
  CARD_SUBSET := Session.CARD_SUBSET
  CARD_SUBSET_EQ := Session.CARD_SUBSET_EQ
  CARRIER_SUBFIELD_GENERATED_SUBFIELD := SessionLibrary.FieldTheory.«CARRIER_SUBFIELD_GENERATED_SUBFIELD»
  CNJ_CNJ := SessionMultiLib.ComplexAlgebra.«CNJ_CNJ»
  CNJ_MUL := SessionMultiLib.ComplexAlgebra.«CNJ_MUL»
  CNJ_VSUM := SessionMultiLib.ComplexAlgebra.«CNJ_VSUM»
  COEFF_ABOVE_DEG := SessionLibrary.RingTheory.«COEFF_ABOVE_DEG»
  COMPLEX_EMBEDDINGS_CNJ := SessionANT.InfinitePlaces.«COMPLEX_EMBEDDINGS_CNJ»
  COMPLEX_EMBEDDINGS_CNJ_CNJ := SessionANT.InfinitePlaces.«COMPLEX_EMBEDDINGS_CNJ_CNJ»
  COMPLEX_EMBEDDINGS_HAS_SIZE := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_HAS_SIZE»
  COMPLEX_EMBEDDINGS_MONOMORPHISM := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_MONOMORPHISM»
  COMPLEX_EMBEDDINGS_NONEMPTY := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_NONEMPTY»
  COMPLEX_EQ := SessionMultiLib.ComplexAlgebra.«COMPLEX_EQ»
  COMPLEX_MUL_SYM := SessionMultiLib.ComplexAlgebra.«COMPLEX_MUL_SYM»
  COMPLEX_NORM_CNJ := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_CNJ»
  COMPLEX_NORM_CX := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_CX»
  COMPLEX_NORM_LE_RE_IM := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_LE_RE_IM»
  COMPLEX_NORM_POW_2_VSUM_FORM := SessionANT.MinkowskiTheory.«COMPLEX_NORM_POW_2_VSUM_FORM»
  COMPLEX_NORM_ZERO := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_ZERO»
  COMPLEX_POLYFUN_MONIC_COEFF_BOUND := SessionANT.ComplexEmbeddings.«COMPLEX_POLYFUN_MONIC_COEFF_BOUND»
  COMPLEX_POLYFUN_ROOTBOUND := SessionMultiLib.ComplexAlgebra.«COMPLEX_POLYFUN_ROOTBOUND»
  COMPLEX_POW_ZERO := SessionMultiLib.ComplexAlgebra.«COMPLEX_POW_ZERO»
  COMPLEX_RING_CLAUSES := SessionMultiLib.ComplexRing.«COMPLEX_RING_CLAUSES»
  COMPLEX_RING_OF_INT := SessionMultiLib.ComplexRing.«COMPLEX_RING_OF_INT»
  COMPLEX_RING_POW := SessionMultiLib.ComplexRing.«COMPLEX_RING_POW»
  COMPLEX_RING_SUM := SessionMultiLib.ComplexRing.«COMPLEX_RING_SUM»
  CX_INJ := SessionMultiLib.ComplexAlgebra.«CX_INJ»
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_IN_IMAGE := Session.EXISTS_IN_IMAGE
  EXTENSION := Session.EXTENSION
  EXTENSIONAL_EQ := Session.EXTENSIONAL_EQ
  EXTENSION_DEGREE_EQ_1 := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_EQ_1»
  FIELD_COMPLEX_RING := SessionMultiLib.ComplexRing.«FIELD_COMPLEX_RING»
  FIELD_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FINITE_COMPLEX_EMBEDDINGS := SessionANT.ComplexEmbeddings.«FINITE_COMPLEX_EMBEDDINGS»
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FINITE_EXTENSION_SUBFIELD_GENERATED»
  FINITE_FUNSPACE := Session.FINITE_FUNSPACE
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_IMP_ALGEBRAIC_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_ALGEBRAIC_EXTENSION»
  FINITE_INT_SEG := Session.FINITE_INT_SEG
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNIONS := Session.FINITE_UNIONS
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FREE_BASIS_IN_CARRIER := SessionLibrary.RingDet.«FREE_BASIS_IN_CARRIER»
  FUN_EQ_COEFF := SessionLibrary.RingTheory.«FUN_EQ_COEFF»
  FUN_EQ_THM := Session.FUN_EQ_THM
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_INDEX := Session.HAS_SIZE_INDEX
  HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS := SessionLibrary.FieldTheory.«HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS»
  HERMITE_INEQUALITY := SessionANT.HermiteInequality.«HERMITE_INEQUALITY»
  IDEAL_NORM_CARRIER := SessionANT.IdealNorm.«IDEAL_NORM_CARRIER»
  IDEAL_NORM_POS := SessionANT.IdealNorm.«IDEAL_NORM_POS»
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMAGE_I := Session.IMAGE_I
  IM_CNJ := SessionMultiLib.ComplexAlgebra.«IM_CNJ»
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING»
  INTEGRAL_DOMAIN_RING_OF_INTEGERS := SessionANT.Numfield.«INTEGRAL_DOMAIN_RING_OF_INTEGERS»
  INTEGRAL_DOMAIN_UNIT_IDEAL := SessionANT.Classgroup.«INTEGRAL_DOMAIN_UNIT_IDEAL»
  INT_ABS_BOUNDS := Session.INT_ABS_BOUNDS
  IN_DELETE := Session.IN_DELETE
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_NUMSEG := Session.IN_NUMSEG
  IN_RING_POLYNOMIAL_CARRIER_COMPOSE := SessionLibrary.RingTheory.«IN_RING_POLYNOMIAL_CARRIER_COMPOSE»
  IN_SING := Session.IN_SING
  IN_UNIONS := Session.IN_UNIONS
  IN_UNIV := Session.IN_UNIV
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LE_0 := Session.LE_0
  LE_1 := Session.LE_1
  LE_REFL := Session.LE_REFL
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE»
  MONIC_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«MONIC_HOMOMORPHIC_IMAGE»
  MONIC_IMP_NONZERO := SessionLibrary.RingTheory.«MONIC_IMP_NONZERO»
  NORM_POS_LE := SessionMultiLib.Vectors.«NORM_POS_LE»
  NOT_LE := Session.NOT_LE
  NUMBER_FIELD_DEGREE_POS := SessionANT.Numfield.«NUMBER_FIELD_DEGREE_POS»
  NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS := SessionANT.InfinitePlaces.«NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS»
  NUMBER_FIELD_DISCRIMINANT_NONZERO := SessionANT.Discriminant.«NUMBER_FIELD_DISCRIMINANT_NONZERO»
  NUMBER_FIELD_EMBEDDING_GRAM_DET := SessionANT.InfinitePlaces.«NUMBER_FIELD_EMBEDDING_GRAM_DET»
  NUMBER_FIELD_IDEAL_MINKOWSKI_LINEAR_FORMS := SessionANT.MinkowskiTheory.«NUMBER_FIELD_IDEAL_MINKOWSKI_LINEAR_FORMS»
  NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS := SessionANT.InfinitePlaces.«NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  POLY_EXTEND_COMPOSE_COEFFS := SessionLibrary.RingTheory.«POLY_EXTEND_COMPOSE_COEFFS»
/-- The core theorems hermite.ml uses. -/
def core2 : HolANT.Hermite.CoreThms2 where
  POLY_EXTEND_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_EXTEND_HOMOMORPHIC_IMAGE»
  POLY_EXTEND_INTO_SUBRING_GENERATED := SessionLibrary.RingTheory.«POLY_EXTEND_INTO_SUBRING_GENERATED»
  POLY_EXTEND_UNIVARIATE := SessionLibrary.RingTheory.«POLY_EXTEND_UNIVARIATE»
  POLY_RING_CLAUSES := SessionLibrary.RingTheory.«POLY_RING_CLAUSES»
  POLY_ROOT_BOUND := SessionLibrary.RingTheory.«POLY_ROOT_BOUND»
  PRIME_SUBFIELD_MINIMAL := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_MINIMAL»
  PRIME_SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_SUBFIELD_GENERATED»
  PRODUCT_CONST := SessionLibrary.Products.«PRODUCT_CONST»
  PRODUCT_DELETE := SessionLibrary.Products.«PRODUCT_DELETE»
  PRODUCT_EQ := SessionLibrary.Products.«PRODUCT_EQ»
  PRODUCT_LE := SessionLibrary.Products.«PRODUCT_LE»
  PRODUCT_MUL := SessionLibrary.Products.«PRODUCT_MUL»
  REAL_ABS_0 := Session.REAL_ABS_0
  REAL_ABS_POS := Session.REAL_ABS_POS
  REAL_ARCH_SIMPLE := Session.REAL_ARCH_SIMPLE
  REAL_LET_TRANS := Session.REAL_LET_TRANS
  REAL_LE_LADD := Session.REAL_LE_LADD
  REAL_LE_LMUL := Session.REAL_LE_LMUL
  REAL_LE_MUL := Session.REAL_LE_MUL
  REAL_LE_MUL2 := Session.REAL_LE_MUL2
  REAL_LE_POW_2 := Session.REAL_LE_POW_2
  REAL_LE_RDIV_EQ := Session.REAL_LE_RDIV_EQ
  REAL_LE_REFL := Session.REAL_LE_REFL
  REAL_LE_RSQRT := Session.REAL_LE_RSQRT
  REAL_LE_TRANS := Session.REAL_LE_TRANS
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_RID := Session.REAL_MUL_RID
  REAL_NOT_LE := Session.REAL_NOT_LE
  REAL_OF_NUM_LE := Session.REAL_OF_NUM_LE
  REAL_OF_NUM_LT := Session.REAL_OF_NUM_LT
  REAL_POS := Session.REAL_POS
  REAL_POW_1_LT := Session.REAL_POW_1_LT
  REAL_POW_2 := Session.REAL_POW_2
  REAL_POW_EQ_0 := Session.REAL_POW_EQ_0
  REAL_POW_LE := Session.REAL_POW_LE
  REAL_POW_LE2 := Session.REAL_POW_LE2
  REAL_POW_LE_1 := Session.REAL_POW_LE_1
  REAL_POW_MUL := Session.REAL_POW_MUL
  REAL_POW_ONE := Session.REAL_POW_ONE
  RESTRICTION := Session.RESTRICTION
  RE_CNJ := SessionMultiLib.ComplexAlgebra.«RE_CNJ»
  RING_CHAR_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_CHAR_SUBFIELD_GENERATED»
  RING_DET_DEPENDENT_COLUMNS := SessionLibrary.RingDet.«RING_DET_DEPENDENT_COLUMNS»
  RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED»
  RING_HOMOMORPHISM_FROM_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_FROM_SUBRING_GENERATED»
  RING_HOMOMORPHISM_I := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_I»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_SUM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM_MUL»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE := SessionLibrary.FieldTheory.«RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_FREE := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE»
  RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL := SessionANT.DedekindKummer.«RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_SUBFIELD_GENERATED»
  RING_POLYNOMIAL := SessionLibrary.RingTheory.«RING_POLYNOMIAL»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  ROOT_1 := SessionMultiLib.Transcendentals.«ROOT_1»
  ROOT_MONO_LE := SessionMultiLib.Transcendentals.«ROOT_MONO_LE»
  SEPARABLE_EXTENSION_CHAR0 := SessionLibrary.FieldTheory.«SEPARABLE_EXTENSION_CHAR0»
  SING_SUBSET := Session.SING_SUBSET
  SQRT_MONO_LE := Session.SQRT_MONO_LE
  SQRT_POS_LE := Session.SQRT_POS_LE
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE»
  SUBFIELD_GENERATED_INC_GEN := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_INC_GEN»
  SUBFIELD_GENERATED_MINIMAL := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_MINIMAL»
  SUBFIELD_GENERATED_SUPERSET := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_SUPERSET»
  SUBFIELD_OF_IMP_SUBSET := SessionLibrary.FieldTheory.«SUBFIELD_OF_IMP_SUBSET»
  SUBFIELD_OF_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_OF_SUBFIELD_GENERATED»
  SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_SUBFIELD_GENERATED»
  SUBFIELD_SUBFIELD_GENERATED_ALT := SessionLibrary.FieldTheory.«SUBFIELD_SUBFIELD_GENERATED_ALT»
  SUBRING_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBRING_GENERATED_BY_SUBFIELD_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUM_EQ := Session.SUM_EQ
  SUM_IMAGE := Session.SUM_IMAGE
  SUM_POS_EQ_0 := Session.SUM_POS_EQ_0
  SUM_POS_LE := Session.SUM_POS_LE
  VSUM_EQ := SessionMultiLib.Vectors.«VSUM_EQ»
  coeff := SessionLibrary.RingTheory.«coeff»
  complex_embeddings := SessionANT.ComplexEmbeddings.«complex_embeddings»
  free_basis := SessionLibrary.RingDet.«free_basis»
  int_abs_th := Session.int_abs_th
  int_eq := Session.int_eq
  int_le := Session.int_le
  int_of_num_th := Session.int_of_num_th
  isomorphic_ring := SessionLibrary.RingTheory.«isomorphic_ring»
  monic := SessionLibrary.RingTheory.«monic»
  number_field := SessionANT.Numfield.«number_field»
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM
  poly_eval := SessionLibrary.RingTheory.«poly_eval»
  poly_evaluate := SessionLibrary.RingTheory.«poly_evaluate»
  ring_homomorphism_extensions := SessionLibrary.FieldTheory.«ring_homomorphism_extensions»
  ring_of_integers := SessionANT.Numfield.«ring_of_integers»

/-- What hermite.ml uses from Session. -/
def deps : HolANT.Hermite.HermiteDeps where
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
  core1 := core1
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in hermite.ml order. -/
initialize BHermite01 : HolANT.Hermite.Hermite01 ←
  ioB "setupHermite01" (HolANT.Hermite.setupHermite01 deps).run
initialize BHermite02 : HolANT.Hermite.Hermite02 ←
  ioB "setupHermite02" (HolANT.Hermite.setupHermite02 deps BHermite01).run

-- Hermite01
def RING_OF_INTEGERS_NORM_PRODUCT_GE_1 : thm := BHermite01.RING_OF_INTEGERS_NORM_PRODUCT_GE_1
def RING_OF_INTEGERS_SUM_NORM_POW_2 : thm := BHermite01.RING_OF_INTEGERS_SUM_NORM_POW_2
def NUMBER_FIELD_DISCRIMINANT_HERMITE_BOUND : thm := BHermite01.NUMBER_FIELD_DISCRIMINANT_HERMITE_BOUND
def NUMBER_FIELD_GENERATOR_CONJUGATES : thm := BHermite01.NUMBER_FIELD_GENERATOR_CONJUGATES
def NUMBER_FIELD_HERMITE_GENERATOR : thm := BHermite01.NUMBER_FIELD_HERMITE_GENERATOR
def NUMBER_FIELD_HERMITE_POLYNOMIAL : thm := BHermite01.NUMBER_FIELD_HERMITE_POLYNOMIAL

-- Hermite02
def NUMBER_FIELD_HERMITE_POLYNOMIALS : thm := BHermite02.NUMBER_FIELD_HERMITE_POLYNOMIALS
def NUMBER_FIELD_HERMITE : thm := BHermite02.NUMBER_FIELD_HERMITE
def NUMBER_FIELD_HERMITE_ISOMORPHIC : thm := BHermite02.NUMBER_FIELD_HERMITE_ISOMORPHIC

/-- `needs "ANT/hermite.ml"`: already done by importing this module. -/
def ensureHermite : IO Unit := pure ()

end SessionANT.Hermite
