/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/discriminant_compositum.ml                    . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/DiscriminantCompositum.lean

  The session half of the discriminant_compositum.ml translation: it supplies HolANT.DiscriminantCompositum's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/discriminant_compositum.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.DiscriminantCompositum
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
import SessionLibrary.Integer
import SessionLibrary.Isum
import SessionLibrary.Products
import SessionLibrary.Multiplicative
import SessionLibrary.Primitive
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionANT.Integral
import SessionANT.Algmisc
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionANT.PrimeSplit
import SessionANT.TraceForm
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.RelativeSplit
import SessionANT.PowerBasis
import SessionANT.RelativeDegree
import SessionANT.SplittingTypes
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionANT.Decomposition
import SessionANT.NfValuation
import SessionANT.NfDecomposition
import SessionANT.DecompositionField
import SessionANT.Integrality
import SessionANT.DedekindKummer
import SessionANT.SplitPrimes
import SessionLibrary.ModmulGroup
import SessionANT.CyclotomicPoly
import SessionANT.CyclotomicField
import SessionANT.CyclotomicIntegers
import SessionLibrary.Cyclotomic
import SessionANT.CyclotomicGalois
import SessionANT.CyclotomicSubfields
import SessionANT.LinearForms
import SessionANT.ClassgroupGroup
import SessionANT.Quadratic
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
import SessionANT.InfinitePlaces
import SessionANT.MinkowskiTheory
import SessionANT.InertiaGenerators

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.DiscriminantCompositum

/-- The core theorems discriminant_compositum.ml uses. -/
def core1 : HolANT.DiscriminantCompositum.CoreThms1 where
  ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD := SessionLibrary.FieldTheory.«ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD»
  ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH := SessionLibrary.FieldTheory.«ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH»
  ALGEBRA_TRACE_NORM_IN_CARRIER := SessionLibrary.RingDet.«ALGEBRA_TRACE_NORM_IN_CARRIER»
  ALGEBRA_TRACE_PRODUCT_BASIS := SessionANT.PowerBasis.«ALGEBRA_TRACE_PRODUCT_BASIS»
  BASIS_COORDINATES := SessionLibrary.RingDet.«BASIS_COORDINATES»
  BASIS_COORDINATES_UNIQUE := SessionLibrary.RingDet.«BASIS_COORDINATES_UNIQUE»
  CARD_IMAGE_LE := Session.CARD_IMAGE_LE
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIVISION := Session.DIVISION
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EQ_MULT_RCANCEL := Session.EQ_MULT_RCANCEL
  EQ_TRANS := Session.EQ_TRANS
  ETA_AX := Session.ETA_AX
  EXISTS_IN_GSPEC := Session.EXISTS_IN_GSPEC
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSIONAL_EQ := Session.EXTENSIONAL_EQ
  EXTENSION_DEGREE_LE_INDEPENDENT_BOUND := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_LE_INDEPENDENT_BOUND»
  EXTENSION_DEGREE_REFL := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_REFL»
  EXTENSION_DEGREE_SUBFIELD_TOWER := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_SUBFIELD_TOWER»
  FIELD_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED»
  FIELD_EXTENSION_SUBFIELD_GENERATED_SUBSET := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED_SUBSET»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_IMP_ALGEBRAIC_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_ALGEBRAIC_EXTENSION»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FREE_BASIS_EXTENSION_DEGREE := SessionLibrary.FieldTheory.«FREE_BASIS_EXTENSION_DEGREE»
  FREE_BASIS_INDEPENDENT := SessionLibrary.RingDet.«FREE_BASIS_INDEPENDENT»
  FREE_BASIS_IN_CARRIER := SessionLibrary.RingDet.«FREE_BASIS_IN_CARRIER»
  FREE_BASIS_SPANNING_DEGREE := SessionLibrary.FieldTheory.«FREE_BASIS_SPANNING_DEGREE»
  FUN_EQ_THM := Session.FUN_EQ_THM
  GALOIS_COMPOSITUM_DEGREE := SessionLibrary.Galois.«GALOIS_COMPOSITUM_DEGREE»
  GALOIS_EXTENSION_GENERATED_CONJUGATES := SessionLibrary.Galois.«GALOIS_EXTENSION_GENERATED_CONJUGATES»
  GALOIS_GROUP_I := SessionLibrary.Galois.«GALOIS_GROUP_I»
  HAS_SIZE_INDEX := Session.HAS_SIZE_INDEX
  HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS := SessionLibrary.FieldTheory.«HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS»
  IMAGE_I := Session.IMAGE_I
  IMAGE_UNION := Session.IMAGE_UNION
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGRAL_CLOSURE_SUBRING := SessionANT.Integral.«INTEGRAL_CLOSURE_SUBRING»
  INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE := SessionANT.Integral.«INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE»
  INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE := SessionANT.Integral.«INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE»
  INTER_SUBSET := Session.INTER_SUBSET
  INT_COPRIME_BEZOUT := SessionLibrary.Integer.«INT_COPRIME_BEZOUT»
  INT_COPRIME_PRIME := SessionLibrary.Integer.«INT_COPRIME_PRIME»
  INT_DIVIDES_RPOW := SessionLibrary.Integer.«INT_DIVIDES_RPOW»
  INT_PRIME := SessionLibrary.Primitive.«INT_PRIME»
  INT_PRIME_DIVPOW := SessionLibrary.Integer.«INT_PRIME_DIVPOW»
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_INTER := Session.IN_INTER
  IN_SUBFIELD_0 := SessionLibrary.FieldTheory.«IN_SUBFIELD_0»
  IN_SUBFIELD_1 := SessionLibrary.FieldTheory.«IN_SUBFIELD_1»
  IN_SUBFIELD_ADD := SessionLibrary.FieldTheory.«IN_SUBFIELD_ADD»
  IN_SUBFIELD_INV := SessionLibrary.FieldTheory.«IN_SUBFIELD_INV»
  IN_SUBFIELD_MUL := SessionLibrary.FieldTheory.«IN_SUBFIELD_MUL»
  IN_SUBFIELD_NEG := SessionLibrary.FieldTheory.«IN_SUBFIELD_NEG»
  IN_SUBFIELD_SUM := SessionLibrary.FieldTheory.«IN_SUBFIELD_SUM»
  IN_SUBRING_INT := SessionLibrary.RingTheory.«IN_SUBRING_INT»
  IN_SUBRING_MUL := SessionLibrary.RingTheory.«IN_SUBRING_MUL»
  IN_SUBRING_SUM := SessionLibrary.RingTheory.«IN_SUBRING_SUM»
  IN_UNION := Session.IN_UNION
  IN_UNIONS := Session.IN_UNIONS
  IN_UNIV := Session.IN_UNIV
  I_THM := Session.I_THM
  LE_1 := Session.LE_1
  LE_ANTISYM := Session.LE_ANTISYM
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  LT := Session.LT
  MOD_LT_EQ := Session.MOD_LT_EQ
  MULT_ASSOC := Session.MULT_ASSOC
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_SYM := Session.MULT_SYM
  NUMBER_FIELD_ALGEBRAIC := SessionANT.Numfield.«NUMBER_FIELD_ALGEBRAIC»
  NUMBER_FIELD_DEGREE_POS := SessionANT.Numfield.«NUMBER_FIELD_DEGREE_POS»
  NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD := SessionANT.Discriminant.«NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD»
  NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS := SessionANT.PowerBasis.«NUMBER_FIELD_DISCRIMINANT_HOMOMORPHISMS»
  NUMBER_FIELD_GALOIS_CLOSURE_Q := SessionANT.SplitPrimes.«NUMBER_FIELD_GALOIS_CLOSURE_Q»
  NUMBER_FIELD_GALOIS_UNRAMIFIED_MONO := SessionANT.DecompositionField.«NUMBER_FIELD_GALOIS_UNRAMIFIED_MONO»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_NORMAL_CLOSURE_SPLITTING_TYPES := SessionANT.DecompositionField.«NUMBER_FIELD_NORMAL_CLOSURE_SPLITTING_TYPES»
  NUMBER_FIELD_RAMIFIED_DISCRIMINANT := SessionANT.Ramification.«NUMBER_FIELD_RAMIFIED_DISCRIMINANT»
  NUMBER_FIELD_SUBFIELD_DEGREE_POS := SessionANT.RelativeSplit.«NUMBER_FIELD_SUBFIELD_DEGREE_POS»
  NUMBER_FIELD_SUBFIELD_GENERATED := SessionANT.RelativeSplit.«NUMBER_FIELD_SUBFIELD_GENERATED»
  NUMBER_FIELD_SUBFIELD_HOMOMORPHIC_IMAGE := SessionANT.RelativeSplit.«NUMBER_FIELD_SUBFIELD_HOMOMORPHIC_IMAGE»
  NUMBER_FIELD_SUBFIELD_UNRAMIFIED_DISCRIMINANT := SessionANT.SplittingTypes.«NUMBER_FIELD_SUBFIELD_UNRAMIFIED_DISCRIMINANT»
  NUMBER_FIELD_TOWER_LAW := SessionANT.RelativeSplit.«NUMBER_FIELD_TOWER_LAW»
  NUMBER_FIELD_UNRAMIFIED_RATIONAL := SessionANT.InertiaGenerators.«NUMBER_FIELD_UNRAMIFIED_RATIONAL»
  PRIME_INT_DIVPROD_EQ := SessionLibrary.Prime.«PRIME_INT_DIVPROD_EQ»
  PRIME_SUBFIELD_MINIMAL := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_MINIMAL»
  PRIME_SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_SUBFIELD_GENERATED»
  RDIV_LT_EQ := Session.RDIV_LT_EQ
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
/-- The core theorems discriminant_compositum.ml uses. -/
def core2 : HolANT.DiscriminantCompositum.CoreThms2 where
  RING_0_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_0_IN_SUBFIELD_GENERATED»
  RING_ADD_RDISTRIB := SessionLibrary.RingTheory.«RING_ADD_RDISTRIB»
  RING_CARRIER_SUBFIELD_GENERATED_SUBSET := SessionLibrary.FieldTheory.«RING_CARRIER_SUBFIELD_GENERATED_SUBSET»
  RING_CHAR_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_CHAR_SUBFIELD_GENERATED»
  RING_DET := SessionLibrary.RingDet.«RING_DET»
  RING_DET_CRAMER_SUBRING := SessionLibrary.RingDet.«RING_DET_CRAMER_SUBRING»
  RING_DET_EQ := SessionLibrary.RingDet.«RING_DET_EQ»
  RING_DET_KRONECKER_MOD_DIV := SessionLibrary.RingDet.«RING_DET_KRONECKER_MOD_DIV»
  RING_DET_SUBRING := SessionLibrary.RingDet.«RING_DET_SUBRING»
  RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED»
  RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_HOMOMORPHISM_SUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM»
  RING_INDEPENDENT_IMP_SUBSET := SessionLibrary.FieldTheory.«RING_INDEPENDENT_IMP_SUBSET»
  RING_INDEPENDENT_LE_SPAN := SessionLibrary.FieldTheory.«RING_INDEPENDENT_LE_SPAN»
  RING_INV_0 := SessionLibrary.RingTheory.«RING_INV_0»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_CARRIER := SessionANT.Numfield.«RING_OF_INTEGERS_CARRIER»
  RING_OF_INTEGERS_FREE := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE»
  RING_OF_INTEGERS_FREE_BASIS_FIELD := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE_BASIS_FIELD»
  RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL := SessionANT.RelativeSplit.«RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL»
  RING_OF_INTEGERS_SUBFIELD_GENERATED := SessionANT.RelativeSplit.«RING_OF_INTEGERS_SUBFIELD_GENERATED»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_1 := SessionLibrary.RingTheory.«RING_OF_INT_1»
  RING_OF_INT_ADD := SessionLibrary.RingTheory.«RING_OF_INT_ADD»
  RING_OF_INT_EQ_0_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0_CHAR_0»
  RING_OF_INT_EQ_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_CHAR_0»
  RING_OF_INT_IN_RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INT_IN_RING_OF_INTEGERS»
  RING_OF_INT_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_IN_SUBFIELD_GENERATED»
  RING_OF_INT_MUL := SessionLibrary.RingTheory.«RING_OF_INT_MUL»
  RING_OF_INT_POW := SessionLibrary.RingTheory.«RING_OF_INT_POW»
  RING_OF_INT_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_SUBFIELD_GENERATED»
  RING_POW_2 := SessionLibrary.RingTheory.«RING_POW_2»
  RING_POW_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_POW_SUBFIELD_GENERATED»
  RING_SPAN_INC := SessionLibrary.FieldTheory.«RING_SPAN_INC»
  RING_SPAN_MUL := SessionLibrary.FieldTheory.«RING_SPAN_MUL»
  RING_SPAN_SUM := SessionLibrary.FieldTheory.«RING_SPAN_SUM»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_ADD := SessionLibrary.RingTheory.«RING_SUM_ADD»
  RING_SUM_CLOSED := SessionLibrary.RingTheory.«RING_SUM_CLOSED»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_EQ_0 := SessionLibrary.RingTheory.«RING_SUM_EQ_0»
  RING_SUM_LMUL := SessionLibrary.RingTheory.«RING_SUM_LMUL»
  RING_SUM_MOD_DIV := SessionLibrary.RingDet.«RING_SUM_MOD_DIV»
  RING_SUM_PRODUCT_INDEX := SessionLibrary.RingDet.«RING_SUM_PRODUCT_INDEX»
  RING_SUM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_SUM_RING_OF_INTEGERS»
  RING_SUM_RMUL := SessionLibrary.RingTheory.«RING_SUM_RMUL»
  RING_SUM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_SUM_SUBFIELD_GENERATED»
  RING_SUM_SWAP := SessionLibrary.RingTheory.«RING_SUM_SWAP»
  SEPARABLE_EXTENSION_CHAR0 := SessionLibrary.FieldTheory.«SEPARABLE_EXTENSION_CHAR0»
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_IDEMPOT := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_IDEMPOT»
  SUBFIELD_GENERATED_IDEMPOT_GEN := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_IDEMPOT_GEN»
  SUBFIELD_GENERATED_INC_GEN := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_INC_GEN»
  SUBFIELD_GENERATED_MINIMAL := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_MINIMAL»
  SUBFIELD_GENERATED_MONO := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_MONO»
  SUBFIELD_GENERATED_RESTRICT := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_RESTRICT»
  SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC»
  SUBFIELD_GENERATED_SUBSET_EQ := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_SUBSET_EQ»
  SUBFIELD_GENERATED_UNION := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_UNION»
  SUBFIELD_OF_FIELD_INV := SessionLibrary.FieldTheory.«SUBFIELD_OF_FIELD_INV»
  SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_SUBFIELD_GENERATED»
  SUBRING_GENERATED_INC := SessionLibrary.RingTheory.«SUBRING_GENERATED_INC»
  SUBRING_GENERATED_MINIMAL := SessionLibrary.RingTheory.«SUBRING_GENERATED_MINIMAL»
  SUBRING_SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_SUBRING_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_CARRIER_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBSET_CARRIER_SUBFIELD_GENERATED»
  SUBSET_TRANS := Session.SUBSET_TRANS
  UNION_COMM := Session.UNION_COMM
  UNION_OVER_INTER := Session.UNION_OVER_INTER
  UNION_SUBSET := Session.UNION_SUBSET
  algebraic_extension := SessionLibrary.FieldTheory.«algebraic_extension»
  basis_discriminant := SessionLibrary.RingDet.«basis_discriminant»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  free_basis := SessionLibrary.RingDet.«free_basis»
  number_field := SessionANT.Numfield.«number_field»
  o_THM := Session.o_THM
  ring_homomorphism_extensions := SessionLibrary.FieldTheory.«ring_homomorphism_extensions»
  subring_of := SessionLibrary.RingTheory.«subring_of»

/-- What discriminant_compositum.ml uses from Session. -/
def deps : HolANT.DiscriminantCompositum.DiscriminantCompositumDeps where
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

/- The bundles, in discriminant_compositum.ml order. -/
initialize BDiscriminantCompositum01 : HolANT.DiscriminantCompositum.DiscriminantCompositum01 ←
  ioB "setupDiscriminantCompositum01" (HolANT.DiscriminantCompositum.setupDiscriminantCompositum01 deps).run
initialize BDiscriminantCompositum02 : HolANT.DiscriminantCompositum.DiscriminantCompositum02 ←
  ioB "setupDiscriminantCompositum02" (HolANT.DiscriminantCompositum.setupDiscriminantCompositum02 deps BDiscriminantCompositum01).run
initialize BDiscriminantCompositum03 : HolANT.DiscriminantCompositum.DiscriminantCompositum03 ←
  ioB "setupDiscriminantCompositum03" (HolANT.DiscriminantCompositum.setupDiscriminantCompositum03 deps BDiscriminantCompositum01 BDiscriminantCompositum02).run
initialize BDiscriminantCompositum04 : HolANT.DiscriminantCompositum.DiscriminantCompositum04 ←
  ioB "setupDiscriminantCompositum04" (HolANT.DiscriminantCompositum.setupDiscriminantCompositum04 deps BDiscriminantCompositum03).run

-- DiscriminantCompositum01
def NUMBER_FIELD_SUBFIELD_INTEGRAL_BASIS : thm := BDiscriminantCompositum01.NUMBER_FIELD_SUBFIELD_INTEGRAL_BASIS
def NUMBER_FIELD_SUBFIELD_INTEGRAL_COORDINATES : thm := BDiscriminantCompositum01.NUMBER_FIELD_SUBFIELD_INTEGRAL_COORDINATES
def NUMBER_FIELD_COMPOSITUM_PRODUCT_SPAN : thm := BDiscriminantCompositum01.NUMBER_FIELD_COMPOSITUM_PRODUCT_SPAN
def NUMBER_FIELD_COMPOSITUM_PRODUCT_BASIS : thm := BDiscriminantCompositum01.NUMBER_FIELD_COMPOSITUM_PRODUCT_BASIS
def NUMBER_FIELD_COMPOSITUM_DEGREE_LE : thm := BDiscriminantCompositum01.NUMBER_FIELD_COMPOSITUM_DEGREE_LE

-- DiscriminantCompositum02
def BASIS_DISCRIMINANT_PRODUCT_BASIS : thm := BDiscriminantCompositum02.BASIS_DISCRIMINANT_PRODUCT_BASIS
def NUMBER_FIELD_COMPOSITUM_HOMOMORPHISMS : thm := BDiscriminantCompositum02.NUMBER_FIELD_COMPOSITUM_HOMOMORPHISMS
def NUMBER_FIELD_COMPOSITUM_COORDINATES : thm := BDiscriminantCompositum02.NUMBER_FIELD_COMPOSITUM_COORDINATES

-- DiscriminantCompositum03
def NUMBER_FIELD_COMPOSITUM_DEGREE_GALOIS : thm := BDiscriminantCompositum03.NUMBER_FIELD_COMPOSITUM_DEGREE_GALOIS
def NUMBER_FIELD_COMPOSITUM_DEGREE_COPRIME : thm := BDiscriminantCompositum03.NUMBER_FIELD_COMPOSITUM_DEGREE_COPRIME
def NUMBER_FIELD_COMPOSITUM_INTEGRAL_BASIS : thm := BDiscriminantCompositum03.NUMBER_FIELD_COMPOSITUM_INTEGRAL_BASIS
def NUMBER_FIELD_COMPOSITUM_DISCRIMINANT : thm := BDiscriminantCompositum03.NUMBER_FIELD_COMPOSITUM_DISCRIMINANT
def NUMBER_FIELD_COMPOSITUM_RING_OF_INTEGERS : thm := BDiscriminantCompositum03.NUMBER_FIELD_COMPOSITUM_RING_OF_INTEGERS

-- DiscriminantCompositum04
def NUMBER_FIELD_COMPOSITUM_RAMIFIED : thm := BDiscriminantCompositum04.NUMBER_FIELD_COMPOSITUM_RAMIFIED

/-- `needs "ANT/discriminant_compositum.ml"`: already done by importing this module. -/
def ensureDiscriminantCompositum : IO Unit := pure ()

end SessionANT.DiscriminantCompositum
