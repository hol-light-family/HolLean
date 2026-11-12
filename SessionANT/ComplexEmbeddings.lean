/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/complex_embeddings.ml                         . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/ComplexEmbeddings.lean

  The session half of the complex_embeddings.ml translation: it supplies HolANT.ComplexEmbeddings's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/complex_embeddings.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.ComplexEmbeddings
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
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.Integral
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.NfValuation
import SessionANT.PrimeSplit
import SessionANT.Discriminant
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.ComplexEmbeddings

/-- The core theorems complex_embeddings.ml uses. -/
def core1 : HolANT.ComplexEmbeddings.CoreThms1 where
  ABELIAN_UNIT_GROUP := SessionLibrary.RingGroups.«ABELIAN_UNIT_GROUP»
  ADD1 := Session.ADD1
  ADD_EQ_0 := Session.ADD_EQ_0
  ADD_SUB := Session.ADD_SUB
  ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING := SessionMultiLib.ComplexField.«ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING»
  ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM_ROOT := SessionLibrary.FieldTheory.«ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM_ROOT»
  ARITH_EQ := Session.ARITH_EQ
  COEFF_COMPOSE := SessionLibrary.RingTheory.«COEFF_COMPOSE»
  COMPLEX_ADD_LID := SessionMultiLib.ComplexAlgebra.«COMPLEX_ADD_LID»
  COMPLEX_ADD_RID := SessionMultiLib.ComplexAlgebra.«COMPLEX_ADD_RID»
  COMPLEX_MUL_ASSOC := SessionMultiLib.ComplexAlgebra.«COMPLEX_MUL_ASSOC»
  COMPLEX_MUL_LZERO := SessionMultiLib.ComplexAlgebra.«COMPLEX_MUL_LZERO»
  COMPLEX_MUL_RZERO := SessionMultiLib.ComplexAlgebra.«COMPLEX_MUL_RZERO»
  COMPLEX_NORM_0 := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_0»
  COMPLEX_NORM_CX := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_CX»
  COMPLEX_NORM_MUL := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_MUL»
  COMPLEX_NORM_NZ := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_NZ»
  COMPLEX_NORM_POW := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_POW»
  COMPLEX_POLYFUN_EQ_0 := SessionMultiLib.ComplexAlgebra.«COMPLEX_POLYFUN_EQ_0»
  COMPLEX_POLYFUN_FINITE_ROOTS := SessionMultiLib.ComplexAlgebra.«COMPLEX_POLYFUN_FINITE_ROOTS»
  COMPLEX_POLYFUN_LINEAR_FACTOR_ROOT := SessionMultiLib.ComplexAlgebra.«COMPLEX_POLYFUN_LINEAR_FACTOR_ROOT»
  COMPLEX_POW_ADD := SessionMultiLib.ComplexAlgebra.«COMPLEX_POW_ADD»
  COMPLEX_RING_CLAUSES := SessionMultiLib.ComplexRing.«COMPLEX_RING_CLAUSES»
  COMPLEX_RING_DIV := SessionMultiLib.ComplexRing.«COMPLEX_RING_DIV»
  COMPLEX_RING_OF_INT := SessionMultiLib.ComplexRing.«COMPLEX_RING_OF_INT»
  COMPLEX_RING_POW := SessionMultiLib.ComplexRing.«COMPLEX_RING_POW»
  COMPLEX_RING_SUM := SessionMultiLib.ComplexRing.«COMPLEX_RING_SUM»
  COMPLEX_SUB_0 := SessionMultiLib.ComplexAlgebra.«COMPLEX_SUB_0»
  COMPLEX_SUB_RDISTRIB := SessionMultiLib.ComplexAlgebra.«COMPLEX_SUB_RDISTRIB»
  COMPLEX_SUB_REFL := SessionMultiLib.ComplexAlgebra.«COMPLEX_SUB_REFL»
  COMPLEX_SUB_RZERO := SessionMultiLib.ComplexAlgebra.«COMPLEX_SUB_RZERO»
  CX_DIV := SessionMultiLib.ComplexAlgebra.«CX_DIV»
  CX_INJ := SessionMultiLib.ComplexAlgebra.«CX_INJ»
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EXTENSION := Session.EXTENSION
  FIELD_COMPLEX_RING := SessionMultiLib.ComplexRing.«FIELD_COMPLEX_RING»
  FIELD_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_RING_HOMOMORPHISM_MONOMORPHISM := SessionLibrary.RingTheory.«FIELD_RING_HOMOMORPHISM_MONOMORPHISM»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FIELD_UNIT := SessionLibrary.RingTheory.«FIELD_UNIT»
  FINITELY_GENERATED_ABELIAN_GROUP_DISCRETE := SessionANT.FingenGroup.«FINITELY_GENERATED_ABELIAN_GROUP_DISCRETE»
  FINITELY_GENERATED_UNIT_GROUP := SessionLibrary.RingGroups.«FINITELY_GENERATED_UNIT_GROUP»
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_FUNSPACE := Session.FINITE_FUNSPACE
  FINITE_IMAGE_INJ_GENERAL := Session.FINITE_IMAGE_INJ_GENERAL
  FINITE_IMP_ALGEBRAIC_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_ALGEBRAIC_EXTENSION»
  FINITE_INTSEG := SessionLibrary.Floor.«FINITE_INTSEG»
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_PRODUCT_DEPENDENT := Session.FINITE_PRODUCT_DEPENDENT
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNIONS := Session.FINITE_UNIONS
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FTA := SessionMultiLib.Cauchy.«FTA»
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS := SessionLibrary.FieldTheory.«HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS»
  INTEGER_CLOSED := SessionLibrary.Floor.«INTEGER_CLOSED»
  INTEGER_REAL_OF_INT := Session.INTEGER_REAL_OF_INT
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING»
  INTEGRAL_DOMAIN_REGULAR := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_REGULAR»
  INTEGRAL_DOMAIN_RING_OF_INTEGERS := SessionANT.Numfield.«INTEGRAL_DOMAIN_RING_OF_INTEGERS»
  INTEGRAL_ELEMENT_FROM_RELATION := SessionANT.Integral.«INTEGRAL_ELEMENT_FROM_RELATION»
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_NUMSEG := Session.IN_NUMSEG
  IN_RING_POLYNOMIAL_CARRIER_COMPOSE := SessionLibrary.RingTheory.«IN_RING_POLYNOMIAL_CARRIER_COMPOSE»
  IN_SING := Session.IN_SING
  IN_UNIV := Session.IN_UNIV
  IRREDUCIBLE_IMP_POLY_DEG_NZ := SessionLibrary.RingTheory.«IRREDUCIBLE_IMP_POLY_DEG_NZ»
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LE := Session.LE
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_0 := Session.LE_0
  LE_1 := Session.LE_1
  LE_REFL := Session.LE_REFL
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MINIMAL_POLYNOMIAL := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL»
  MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE»
  MONO_EXISTS := Session.MONO_EXISTS
  NORM_POS_LE := SessionMultiLib.Vectors.«NORM_POS_LE»
  NOT_SUC := Session.NOT_SUC
  NUMBER_FIELD_ALGEBRAIC := SessionANT.Numfield.«NUMBER_FIELD_ALGEBRAIC»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
/-- The core theorems complex_embeddings.ml uses. -/
def core2 : HolANT.ComplexEmbeddings.CoreThms2 where
  POLY_DEG_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_DEG_MONOMORPHIC_IMAGE»
  POLY_EVAL_COMPLEX_RING := SessionMultiLib.ComplexRing.«POLY_EVAL_COMPLEX_RING»
  PRIME_SUBFIELD_CHAR_0 := SessionANT.Numfield.«PRIME_SUBFIELD_CHAR_0»
  PRIME_SUBFIELD_HOMOMORPHISM_EXISTS := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_HOMOMORPHISM_EXISTS»
  PRIME_SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_SUBFIELD_GENERATED»
  REAL_ABS_BOUNDS := Session.REAL_ABS_BOUNDS
  REAL_ABS_NUM := Session.REAL_ABS_NUM
  REAL_LE_MUL2 := Session.REAL_LE_MUL2
  REAL_LE_REFL := Session.REAL_LE_REFL
  REAL_LE_TRANS := Session.REAL_LE_TRANS
  REAL_POW_EQ_1 := Session.REAL_POW_EQ_1
  REAL_POW_LE := Session.REAL_POW_LE
  REAL_POW_MONO := Session.REAL_POW_MONO
  REAL_POW_ONE := Session.REAL_POW_ONE
  RESTRICTION := Session.RESTRICTION
  RESTRICTION_IN_EXTENSIONAL := Session.RESTRICTION_IN_EXTENSIONAL
  RESTRICTION_IN_RING_HOMOMORPHISM_EXTENSIONS := SessionLibrary.FieldTheory.«RESTRICTION_IN_RING_HOMOMORPHISM_EXTENSIONS»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD_RNEG := SessionLibrary.RingTheory.«RING_ADD_RNEG»
  RING_CHAR_COMPLEX_RING := SessionMultiLib.ComplexRing.«RING_CHAR_COMPLEX_RING»
  RING_CHAR_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_CHAR_SUBFIELD_GENERATED»
  RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_EQ := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_EQ»
  RING_HOMOMORPHISM_EXTENSIONS_NONEMPTY := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_EXTENSIONS_NONEMPTY»
  RING_HOMOMORPHISM_EXTENSIONS_ROOT := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_EXTENSIONS_ROOT»
  RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_MATRIX_SOLVE := SessionLibrary.RingDet.«RING_MATRIX_SOLVE»
  RING_MONOMORPHISM_ALT := SessionLibrary.RingTheory.«RING_MONOMORPHISM_ALT»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_CARRIER := SessionANT.Numfield.«RING_OF_INTEGERS_CARRIER»
  RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q := SessionANT.Integrality.«RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_0 := SessionLibrary.RingTheory.«RING_OF_INT_0»
  RING_OF_INT_1 := SessionLibrary.RingTheory.«RING_OF_INT_1»
  RING_OF_INT_CASES := SessionLibrary.RingTheory.«RING_OF_INT_CASES»
  RING_OF_INT_EQ_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_CHAR_0»
  RING_OF_NUM_1 := SessionLibrary.RingTheory.«RING_OF_NUM_1»
  RING_ORDER_NONZERO_MULTSYS := SessionLibrary.RingTheory.«RING_ORDER_NONZERO_MULTSYS»
  RING_POLYNOMIAL := SessionLibrary.RingTheory.«RING_POLYNOMIAL»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_1 := SessionLibrary.RingTheory.«RING_POW_1»
  RING_POW_ADD := SessionLibrary.RingTheory.«RING_POW_ADD»
  RING_POW_RING_ORDER := SessionLibrary.RingTheory.«RING_POW_RING_ORDER»
  RING_PRODUCT_SUBRING_GENERATED_GEN := SessionLibrary.RingTheory.«RING_PRODUCT_SUBRING_GENERATED_GEN»
  RING_SUM_DELTA := SessionLibrary.RingTheory.«RING_SUM_DELTA»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_UNIT_0 := SessionLibrary.RingTheory.«RING_UNIT_0»
  RING_UNIT_IN_CARRIER := SessionLibrary.RingTheory.«RING_UNIT_IN_CARRIER»
  SEPARABLE_EXTENSION_CHAR0 := SessionLibrary.FieldTheory.«SEPARABLE_EXTENSION_CHAR0»
  SKOLEM_THM := Session.SKOLEM_THM
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBSET := Session.SUBSET
  SUC_SUB1 := Session.SUC_SUB1
  UNIONS_GSPEC := Session.UNIONS_GSPEC
  UNIT_GROUP := SessionLibrary.RingGroups.«UNIT_GROUP»
  VSUM_CLAUSES_LEFT := SessionMultiLib.Vectors.«VSUM_CLAUSES_LEFT»
  VSUM_CLAUSES_NUMSEG := SessionMultiLib.Vectors.«VSUM_CLAUSES_NUMSEG»
  VSUM_COMPLEX_LMUL := SessionMultiLib.ComplexAlgebra.«VSUM_COMPLEX_LMUL»
  VSUM_EQ_NUMSEG := SessionMultiLib.Vectors.«VSUM_EQ_NUMSEG»
  VSUM_OFFSET := SessionMultiLib.Vectors.«VSUM_OFFSET»
  VSUM_SUB_NUMSEG := SessionMultiLib.Vectors.«VSUM_SUB_NUMSEG»
  int_eq := Session.int_eq
  int_of_num_th := Session.int_of_num_th
  int_tybij := Session.int_tybij
  lemma := SessionMultiLib.Integration.«lemma»
  monic := SessionLibrary.RingTheory.«monic»
  number_field := SessionANT.Numfield.«number_field»
  rational := SessionLibrary.Floor.«rational»
  real_pow := Session.real_pow
  ring_homomorphism_extensions := SessionLibrary.FieldTheory.«ring_homomorphism_extensions»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  ring_multsys := SessionLibrary.RingTheory.«ring_multsys»
  ring_of_integers := SessionANT.Numfield.«ring_of_integers»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»

/-- What complex_embeddings.ml uses from Session. -/
def deps : HolANT.ComplexEmbeddings.ComplexEmbeddingsDeps where
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
  NORM_ARITH t := ExceptT.mk (SessionMultiLib.Vectors.NORM_ARITH t)
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

/- The bundles, in complex_embeddings.ml order. -/
initialize BComplexEmbeddings : HolANT.ComplexEmbeddings.ComplexEmbeddings ←
  ioB "setupComplexEmbeddings" (HolANT.ComplexEmbeddings.setupComplexEmbeddings deps).run

-- ComplexEmbeddings
def complex_embeddings : thm := BComplexEmbeddings.complex_embeddings
def COMPLEX_MATRIX_SOLVE : thm := BComplexEmbeddings.COMPLEX_MATRIX_SOLVE
def COMPLEX_PRIME_SUBFIELD : thm := BComplexEmbeddings.COMPLEX_PRIME_SUBFIELD
def COMPLEX_POLYFUN_MONIC_COEFF_BOUND : thm := BComplexEmbeddings.COMPLEX_POLYFUN_MONIC_COEFF_BOUND
def COMPLEX_POLYFUN_MONIC_INTEGER_ROOTS_FINITE : thm := BComplexEmbeddings.COMPLEX_POLYFUN_MONIC_INTEGER_ROOTS_FINITE
def COMPLEX_EMBEDDINGS_RESTRICTION : thm := BComplexEmbeddings.COMPLEX_EMBEDDINGS_RESTRICTION
def COMPLEX_EMBEDDINGS_MONOMORPHISM : thm := BComplexEmbeddings.COMPLEX_EMBEDDINGS_MONOMORPHISM
def COMPLEX_EMBEDDINGS_EXTENSIONS : thm := BComplexEmbeddings.COMPLEX_EMBEDDINGS_EXTENSIONS
def COMPLEX_EMBEDDINGS_NONEMPTY : thm := BComplexEmbeddings.COMPLEX_EMBEDDINGS_NONEMPTY
def COMPLEX_EMBEDDINGS_HAS_SIZE : thm := BComplexEmbeddings.COMPLEX_EMBEDDINGS_HAS_SIZE
def FINITE_COMPLEX_EMBEDDINGS : thm := BComplexEmbeddings.FINITE_COMPLEX_EMBEDDINGS
def COMPLEX_EMBEDDINGS_CONJUGATES : thm := BComplexEmbeddings.COMPLEX_EMBEDDINGS_CONJUGATES
def RING_OF_INTEGERS_CONJUGATES_POLYFUN : thm := BComplexEmbeddings.RING_OF_INTEGERS_CONJUGATES_POLYFUN
def RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE : thm := BComplexEmbeddings.RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE
def COMPLEX_EMBEDDINGS_ROOT_OF_UNITY : thm := BComplexEmbeddings.COMPLEX_EMBEDDINGS_ROOT_OF_UNITY
def RING_OF_INTEGERS_ROOT_OF_UNITY : thm := BComplexEmbeddings.RING_OF_INTEGERS_ROOT_OF_UNITY
def NUMBER_FIELD_ROOTS_OF_UNITY_FINITE : thm := BComplexEmbeddings.NUMBER_FIELD_ROOTS_OF_UNITY_FINITE
def NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED : thm := BComplexEmbeddings.NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED
def NUMBER_FIELD_UNITS_GENERATORS : thm := BComplexEmbeddings.NUMBER_FIELD_UNITS_GENERATORS

/-- `needs "ANT/complex_embeddings.ml"`: already done by importing this module. -/
def ensureComplexEmbeddings : IO Unit := pure ()

end SessionANT.ComplexEmbeddings
