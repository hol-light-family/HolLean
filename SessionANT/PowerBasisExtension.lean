/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/power_basis_extension.ml                      . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/PowerBasisExtension.lean

  The session half of the power_basis_extension.ml translation: it supplies HolANT.PowerBasisExtension's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/power_basis_extension.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.PowerBasisExtension
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.Matroids
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.RingTheory
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionLibrary.FieldTheory
import SessionANT.IdealArith
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.Dedekind
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.RingGroups
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionLibrary.FiniteFields
import SessionANT.Hensel
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.IdealEuler
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.RingOfIntegers
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.PrimeSplit
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.NfValuation
import SessionANT.Integrality
import SessionANT.Different
import SessionANT.RelativeDegree
import SessionANT.DedekindKummer
import SessionANT.PowerBasis
import SessionANT.PowerBasisIndex
import SessionANT.FiniteFieldTrace
import SessionANT.DifferentExtension

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.PowerBasisExtension

/-- The core theorems power_basis_extension.ml uses. -/
def core1 : HolANT.PowerBasisExtension.CoreThms1 where
  ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD := SessionLibrary.FieldTheory.«ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD»
  ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH := SessionLibrary.FieldTheory.«ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH»
  ALGEBRA_TRACE_MUL_LINCOMB := SessionLibrary.RingDet.«ALGEBRA_TRACE_MUL_LINCOMB»
  ALGEBRA_TRACE_NORM_EMBEDDINGS_SEPARABLE := SessionLibrary.FieldTheory.«ALGEBRA_TRACE_NORM_EMBEDDINGS_SEPARABLE»
  ALGEBRA_TRACE_NORM_IN_CARRIER := SessionLibrary.RingDet.«ALGEBRA_TRACE_NORM_IN_CARRIER»
  ALGEBRA_TRACE_SUB := SessionLibrary.RingDet.«ALGEBRA_TRACE_SUB»
  ALGEBRA_TRACE_SURJECTIVE := SessionLibrary.FieldTheory.«ALGEBRA_TRACE_SURJECTIVE»
  BASIS_COORDINATES_EXPAND := SessionLibrary.RingDet.«BASIS_COORDINATES_EXPAND»
  BASIS_COORDINATES_IN_CARRIER := SessionLibrary.RingDet.«BASIS_COORDINATES_IN_CARRIER»
  BASIS_DISCRIMINANT_TIMES_COORD := SessionLibrary.RingDet.«BASIS_DISCRIMINANT_TIMES_COORD»
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  COEFF_COMPOSE := SessionLibrary.RingTheory.«COEFF_COMPOSE»
  COEFF_IN_CARRIER_ALT := SessionLibrary.RingTheory.«COEFF_IN_CARRIER_ALT»
  DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT := SessionANT.Dedekind.«DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT»
  DEDEKIND_IDEAL_SUBSET_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_POW_VALUATION»
  DEDEKIND_IMP_INTEGRAL_DOMAIN := SessionANT.Dedekind.«DEDEKIND_IMP_INTEGRAL_DOMAIN»
  DEDEKIND_IN_IDEAL_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IN_IDEAL_POW_VALUATION»
  DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL := SessionANT.Dedekind.«DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL»
  DEDEKIND_RESIDUE_GENERATOR_UNIFORMIZER := SessionANT.IdealEuler.«DEDEKIND_RESIDUE_GENERATOR_UNIFORMIZER»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DEDEKIND_SUBRING_DENSE := SessionANT.Dedekind.«DEDEKIND_SUBRING_DENSE»
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  EQ_IMP := Session.EQ_IMP
  EQ_SYM_EQ := Session.EQ_SYM_EQ
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSION := Session.EXTENSION
  EXTENSION_DEGREE_EQ_0 := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_EQ_0»
  EXTENSION_DEGREE_LE_SPANNING := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_LE_SPANNING»
  EXTENSION_LINCOMB_ADD := SessionLibrary.RingDet.«EXTENSION_LINCOMB_ADD»
  EXTENSION_LINCOMB_LMUL := SessionLibrary.RingDet.«EXTENSION_LINCOMB_LMUL»
  FIELD_HOMOMORPHISM_INV := SessionLibrary.RingTheory.«FIELD_HOMOMORPHISM_INV»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_MUL_EQ_0 := SessionLibrary.RingTheory.«FIELD_MUL_EQ_0»
  FIELD_MUL_LINV := SessionLibrary.RingTheory.«FIELD_MUL_LINV»
  FIELD_MUL_RINV := SessionLibrary.RingTheory.«FIELD_MUL_RINV»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FIELD_POLY_COFACTOR_COEFFS := SessionLibrary.RingTheory.«FIELD_POLY_COFACTOR_COEFFS»
  FIELD_QUOTIENT_RING := SessionLibrary.RingTheory.«FIELD_QUOTIENT_RING»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_EXTENSION_SIMPLE_EQ := SessionLibrary.FieldTheory.«FINITE_EXTENSION_SIMPLE_EQ»
  FINITE_IMP_ALGEBRAIC_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_ALGEBRAIC_EXTENSION»
  FINITE_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_FIELD_EXTENSION»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FREE_BASIS_EXTENSION_DEGREE := SessionLibrary.FieldTheory.«FREE_BASIS_EXTENSION_DEGREE»
  FREE_BASIS_IN_CARRIER := SessionLibrary.RingDet.«FREE_BASIS_IN_CARRIER»
  FREE_BASIS_SIMPLE_EXTENSION := SessionLibrary.FieldTheory.«FREE_BASIS_SIMPLE_EXTENSION»
  FUN_EQ_THM := Session.FUN_EQ_THM
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  HAS_SIZE_INDEX := Session.HAS_SIZE_INDEX
  HAS_SIZE_SEPARABLE_DEGREE := SessionLibrary.FieldTheory.«HAS_SIZE_SEPARABLE_DEGREE»
  IDEAL_EXTENSION_POW_SUPPLEMENT := SessionANT.IdealArith.«IDEAL_EXTENSION_POW_SUPPLEMENT»
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_GENERATED_IMAGE_IDEAL_GENERATED := SessionANT.IdealArith.«IDEAL_GENERATED_IMAGE_IDEAL_GENERATED»
  IDEAL_GENERATED_INC := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_GENERATED_SING_ALT := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING_ALT»
  IDEAL_POW_1 := SessionANT.IdealArith.«IDEAL_POW_1»
  IDEAL_POW_SUC := SessionANT.IdealArith.«IDEAL_POW_SUC»
  IDEAL_PRODUCT_SING := SessionANT.IdealArith.«IDEAL_PRODUCT_SING»
  IDEAL_PROD_COMM := SessionANT.IdealArith.«IDEAL_PROD_COMM»
  IDEAL_PROD_HOMOMORPHIC_IMAGE := SessionANT.IdealArith.«IDEAL_PROD_HOMOMORPHIC_IMAGE»
  IDEAL_PROD_MONO := SessionANT.IdealArith.«IDEAL_PROD_MONO»
  IDEAL_VALUATION_PRINCIPAL_MUL := SessionANT.Dedekind.«IDEAL_VALUATION_PRINCIPAL_MUL»
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMAGE_I := Session.IMAGE_I
  IMAGE_POLY_EXTEND_1 := SessionLibrary.RingTheory.«IMAGE_POLY_EXTEND_1»
  IMP_CONJ := Session.IMP_CONJ
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_MUL_LCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_LCANCEL»
  INTEGRAL_DOMAIN_POLY_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_POLY_RING»
  INTEGRAL_DOMAIN_PRODUCT_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_PRODUCT_EQ_0»
  IN_DELETE := Session.IN_DELETE
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_INTER := Session.IN_INTER
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_SING := Session.IN_SING
  IN_SUBRING_0 := SessionLibrary.RingTheory.«IN_SUBRING_0»
  IN_SUBRING_1 := SessionLibrary.RingTheory.«IN_SUBRING_1»
  IN_SUBRING_ADD := SessionLibrary.RingTheory.«IN_SUBRING_ADD»
  IN_SUBRING_MUL := SessionLibrary.RingTheory.«IN_SUBRING_MUL»
  IN_SUBRING_POW := SessionLibrary.RingTheory.«IN_SUBRING_POW»
  IN_SUBRING_SUB := SessionLibrary.RingTheory.«IN_SUBRING_SUB»
  IN_SUBRING_SUM := SessionLibrary.RingTheory.«IN_SUBRING_SUM»
  LEFT_AND_EXISTS_THM := Session.LEFT_AND_EXISTS_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_ANTISYM := Session.LE_ANTISYM
  LE_REFL := Session.LE_REFL
  MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE»
  MINIMAL_POLYNOMIAL_IN_CARRIER := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_IN_CARRIER»
  MINIMAL_POLYNOMIAL_MONIC := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_MONIC»
  MINIMAL_POLYNOMIAL_VANISHES := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_VANISHES»
  MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE»
  MONIC_IMP_NONZERO := SessionLibrary.RingTheory.«MONIC_IMP_NONZERO»
  MONIC_POLY_EQ_ROOTS_PRODUCT := SessionLibrary.RingTheory.«MONIC_POLY_EQ_ROOTS_PRODUCT»
  MONIC_SUBRING_GENERATED := SessionLibrary.RingTheory.«MONIC_SUBRING_GENERATED»
  MONIC_X_MINUS_A := SessionLibrary.RingTheory.«MONIC_X_MINUS_A»
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT := SessionANT.Different.«NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT»
  NUMBER_FIELD_DIFFERENT_NONZERO := SessionANT.Different.«NUMBER_FIELD_DIFFERENT_NONZERO»
  NUMBER_FIELD_HOMOMORPHIC_PREIMAGE := SessionANT.RelativeSplit.«NUMBER_FIELD_HOMOMORPHIC_PREIMAGE»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_INTEGRAL_MULTIPLE := SessionANT.Numfield.«NUMBER_FIELD_INTEGRAL_MULTIPLE»
  NUMBER_FIELD_PRIME_FACTORIZATION := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_FACTORIZATION»
  NUMBER_FIELD_PRIME_IDEAL_ABOVE := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_IDEAL_ABOVE»
  NUMBER_FIELD_TOWER_LAW := SessionANT.RelativeSplit.«NUMBER_FIELD_TOWER_LAW»
  NUMBER_FIELD_TRACE_INTEGRAL := SessionANT.Integrality.«NUMBER_FIELD_TRACE_INTEGRAL»
  POLY_COMPOSE_HOMOMORPHISM_CONST := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_CONST»
  POLY_COMPOSE_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_MUL»
  POLY_COMPOSE_HOMOMORPHISM_SUB := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_SUB»
  POLY_COMPOSE_HOMOMORPHISM_VAR := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_VAR»
  POLY_DEG_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_DEG_MONOMORPHIC_IMAGE»
/-- The core theorems power_basis_extension.ml uses. -/
def core2 : HolANT.PowerBasisExtension.CoreThms2 where
  POLY_DEG_SUBRING_GENERATED := SessionLibrary.RingTheory.«POLY_DEG_SUBRING_GENERATED»
  POLY_DERIV_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_DERIV_HOMOMORPHIC_IMAGE»
  POLY_DERIV_IN_CARRIER := SessionLibrary.RingTheory.«POLY_DERIV_IN_CARRIER»
  POLY_DERIV_SUBRING_GENERATED := SessionLibrary.RingTheory.«POLY_DERIV_SUBRING_GENERATED»
  POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS := SessionLibrary.RingDet.«POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS»
  POLY_EXTEND := SessionLibrary.RingTheory.«POLY_EXTEND»
  POLY_EXTEND_EVALUATE := SessionLibrary.RingTheory.«POLY_EXTEND_EVALUATE»
  POLY_EXTEND_FROM_SUBRING_GENERATED := SessionLibrary.RingTheory.«POLY_EXTEND_FROM_SUBRING_GENERATED»
  POLY_EXTEND_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_EXTEND_HOMOMORPHIC_IMAGE»
  POLY_RING_CLAUSES := SessionLibrary.RingTheory.«POLY_RING_CLAUSES»
  POLY_ROOT_DECOMPOSE := SessionLibrary.RingTheory.«POLY_ROOT_DECOMPOSE»
  PRIME_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_SUBSET»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRIME_SUBRING_MINIMAL := SessionLibrary.RingTheory.«PRIME_SUBRING_MINIMAL»
  QUOTIENT_RING := SessionLibrary.RingTheory.«QUOTIENT_RING»
  RINGS_EQ := SessionLibrary.RingTheory.«RINGS_EQ»
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_EXTENSIONS_SIMPLE_EQ := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_EXTENSIONS_SIMPLE_EQ»
  RING_HOMOMORPHISM_FROM_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_FROM_SUBRING_GENERATED»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_HOMOMORPHISM_RING_OF_INTEGERS»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_HOMOMORPHISM_SUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IDEAL_QUOTIENT := SessionANT.IdealArith.«RING_IDEAL_IDEAL_QUOTIENT»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_IDEAL_NUMBER_FIELD_DIFFERENT := SessionANT.Different.«RING_IDEAL_NUMBER_FIELD_DIFFERENT»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_MONOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_MONOMORPHISM_COMPOSE»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_IN_IDEAL_PROD := SessionANT.IdealArith.«RING_MUL_IN_IDEAL_PROD»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0 := SessionANT.Numfield.«RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0»
  RING_OF_INTEGERS_MINIMAL_POLYNOMIAL := SessionANT.Integrality.«RING_OF_INTEGERS_MINIMAL_POLYNOMIAL»
  RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER := SessionANT.RelativeSplit.«RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER»
  RING_OF_INTEGERS_QUOTIENT_TRACE := SessionANT.DifferentExtension.«RING_OF_INTEGERS_QUOTIENT_TRACE»
  RING_OF_INTEGERS_SUBFIELD_GENERATED := SessionANT.RelativeSplit.«RING_OF_INTEGERS_SUBFIELD_GENERATED»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INTEGERS_SUBSET_CODIFFERENT := SessionANT.Different.«RING_OF_INTEGERS_SUBSET_CODIFFERENT»
  RING_OF_INT_EQ_0_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0_CHAR_0»
  RING_POLYNOMIAL := SessionLibrary.RingTheory.«RING_POLYNOMIAL»
  RING_POLYNOMIAL_COMPOSE := SessionLibrary.RingTheory.«RING_POLYNOMIAL_COMPOSE»
  RING_POLYNOMIAL_CONST := SessionLibrary.RingTheory.«RING_POLYNOMIAL_CONST»
  RING_POLYNOMIAL_IMP_POWERSERIES := SessionLibrary.RingTheory.«RING_POLYNOMIAL_IMP_POWERSERIES»
  RING_POLYNOMIAL_SUB := SessionLibrary.RingTheory.«RING_POLYNOMIAL_SUB»
  RING_POLYNOMIAL_SUBRING_COEFF := SessionLibrary.RingTheory.«RING_POLYNOMIAL_SUBRING_COEFF»
  RING_POLYNOMIAL_VAR := SessionLibrary.RingTheory.«RING_POLYNOMIAL_VAR»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POWERSERIES_CONST := SessionLibrary.RingTheory.«RING_POWERSERIES_CONST»
  RING_POWERSERIES_VAR := SessionLibrary.RingTheory.«RING_POWERSERIES_VAR»
  RING_PRODUCT := SessionLibrary.RingTheory.«RING_PRODUCT»
  RING_PRODUCT_DELETE := SessionLibrary.RingDet.«RING_PRODUCT_DELETE»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_LDISTRIB := SessionLibrary.RingTheory.«RING_SUB_LDISTRIB»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_SUB_RZERO := SessionLibrary.RingTheory.«RING_SUB_RZERO»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_DELTA := SessionLibrary.RingTheory.«RING_SUM_DELTA»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_EQ_0 := SessionLibrary.RingTheory.«RING_SUM_EQ_0»
  RING_SUM_IMAGE := SessionLibrary.RingTheory.«RING_SUM_IMAGE»
  RING_SUM_LAGRANGE_COEFF := SessionLibrary.RingTheory.«RING_SUM_LAGRANGE_COEFF»
  RING_SUM_LMUL := SessionLibrary.RingTheory.«RING_SUM_LMUL»
  RING_SUM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_SUM_RING_OF_INTEGERS»
  SEPARABLE_DEGREE_EQ_EXTENSION_DEGREE := SessionLibrary.FieldTheory.«SEPARABLE_DEGREE_EQ_EXTENSION_DEGREE»
  SEPARABLE_EXTENSION_CHAR0 := SessionLibrary.FieldTheory.«SEPARABLE_EXTENSION_CHAR0»
  SING_SUBSET := Session.SING_SUBSET
  SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC»
  SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_GENERATED»
  SUBRING_GENERATED_INC := SessionLibrary.RingTheory.«SUBRING_GENERATED_INC»
  SUBRING_GENERATED_INC_GEN := SessionLibrary.RingTheory.«SUBRING_GENERATED_INC_GEN»
  SUBRING_GENERATED_MINIMAL := SessionLibrary.RingTheory.«SUBRING_GENERATED_MINIMAL»
  SUBRING_GENERATED_MONIC_ROOT_SPAN := SessionLibrary.RingTheory.«SUBRING_GENERATED_MONIC_ROOT_SPAN»
  SUBRING_GENERATED_MONO := SessionLibrary.RingTheory.«SUBRING_GENERATED_MONO»
  SUBRING_GENERATED_SUPERSET := SessionLibrary.RingTheory.«SUBRING_GENERATED_SUPERSET»
  SUBRING_SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_SUBRING_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_ANTISYM_EQ := Session.SUBSET_ANTISYM_EQ
  SUBSET_REFL := Session.SUBSET_REFL
  SUBSET_TRANS := Session.SUBSET_TRANS
  algebraic_extension := SessionLibrary.FieldTheory.«algebraic_extension»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  free_basis := SessionLibrary.RingDet.«free_basis»
  monic := SessionLibrary.RingTheory.«monic»
  number_field := SessionANT.Numfield.«number_field»
  number_field_codifferent := SessionANT.Different.«number_field_codifferent»
  number_field_different := SessionANT.Different.«number_field_different»
  o_ASSOC := Session.o_ASSOC
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM
  poly_eval := SessionLibrary.RingTheory.«poly_eval»
  ring_div := SessionLibrary.RingTheory.«ring_div»
  ring_homomorphism_extensions := SessionLibrary.FieldTheory.«ring_homomorphism_extensions»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  ring_of_integers := SessionANT.Numfield.«ring_of_integers»
  ring_polynomial := SessionLibrary.RingTheory.«ring_polynomial»
  ring_powerseries := SessionLibrary.RingTheory.«ring_powerseries»
  ring_setadd := SessionLibrary.RingTheory.«ring_setadd»
  subring_of := SessionLibrary.RingTheory.«subring_of»

/-- What power_basis_extension.ml uses from Session. -/
def deps : HolANT.PowerBasisExtension.PowerBasisExtensionDeps where
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

/- The bundles, in power_basis_extension.ml order. -/
initialize BPowerBasisExtension01 : HolANT.PowerBasisExtension.PowerBasisExtension01 ←
  ioB "setupPowerBasisExtension01" (HolANT.PowerBasisExtension.setupPowerBasisExtension01 deps).run
initialize BPowerBasisExtension02 : HolANT.PowerBasisExtension.PowerBasisExtension02 ←
  ioB "setupPowerBasisExtension02" (HolANT.PowerBasisExtension.setupPowerBasisExtension02 deps BPowerBasisExtension01).run
initialize BPowerBasisExtension03 : HolANT.PowerBasisExtension.PowerBasisExtension03 ←
  ioB "setupPowerBasisExtension03" (HolANT.PowerBasisExtension.setupPowerBasisExtension03 deps BPowerBasisExtension02).run
initialize BPowerBasisExtension04 : HolANT.PowerBasisExtension.PowerBasisExtension04 ←
  ioB "setupPowerBasisExtension04" (HolANT.PowerBasisExtension.setupPowerBasisExtension04 deps BPowerBasisExtension01 BPowerBasisExtension03).run

-- PowerBasisExtension01
def FIELD_POWER_BASIS_EMBEDDINGS : thm := BPowerBasisExtension01.FIELD_POWER_BASIS_EMBEDDINGS
def ALGEBRA_TRACE_POWER_BASIS_DUAL : thm := BPowerBasisExtension01.ALGEBRA_TRACE_POWER_BASIS_DUAL
def ALGEBRA_TRACE_FORM_INJECTIVE : thm := BPowerBasisExtension01.ALGEBRA_TRACE_FORM_INJECTIVE
def NUMBER_FIELD_SEPARABLE_EXTENSION : thm := BPowerBasisExtension01.NUMBER_FIELD_SEPARABLE_EXTENSION
def ALGEBRA_TRACE_DUAL_BASIS_EXPANSION : thm := BPowerBasisExtension01.ALGEBRA_TRACE_DUAL_BASIS_EXPANSION

-- PowerBasisExtension02
def NUMBER_FIELD_POWER_BASIS_DATA : thm := BPowerBasisExtension02.NUMBER_FIELD_POWER_BASIS_DATA
def NUMBER_FIELD_CODIFFERENT_POWER_BASIS : thm := BPowerBasisExtension02.NUMBER_FIELD_CODIFFERENT_POWER_BASIS
def NUMBER_FIELD_POWER_BASIS_GENERATOR : thm := BPowerBasisExtension02.NUMBER_FIELD_POWER_BASIS_GENERATOR
def NUMBER_FIELD_DERIVATIVE_IN_DIFFERENT : thm := BPowerBasisExtension02.NUMBER_FIELD_DERIVATIVE_IN_DIFFERENT
def NUMBER_FIELD_DIFFERENT_POWER_BASIS : thm := BPowerBasisExtension02.NUMBER_FIELD_DIFFERENT_POWER_BASIS
def NUMBER_FIELD_CODIFFERENT_POWER_BASIS_Q : thm := BPowerBasisExtension02.NUMBER_FIELD_CODIFFERENT_POWER_BASIS_Q
def NUMBER_FIELD_DERIVATIVE_IN_DIFFERENT_Q : thm := BPowerBasisExtension02.NUMBER_FIELD_DERIVATIVE_IN_DIFFERENT_Q
def NUMBER_FIELD_DIFFERENT_POWER_BASIS_Q : thm := BPowerBasisExtension02.NUMBER_FIELD_DIFFERENT_POWER_BASIS_Q

-- PowerBasisExtension03
def NUMBER_FIELD_DIFFERENT_LOCAL_POWER_BASIS : thm := BPowerBasisExtension03.NUMBER_FIELD_DIFFERENT_LOCAL_POWER_BASIS
def RING_OF_INTEGERS_LOCAL_SPAN : thm := BPowerBasisExtension03.RING_OF_INTEGERS_LOCAL_SPAN
def RING_OF_INTEGERS_SPAN_MOD_PRIME_DEGREE : thm := BPowerBasisExtension03.RING_OF_INTEGERS_SPAN_MOD_PRIME_DEGREE

-- PowerBasisExtension04
def RING_OF_INTEGERS_ADJOIN_SPAN : thm := BPowerBasisExtension04.RING_OF_INTEGERS_ADJOIN_SPAN
def NUMBER_FIELD_POWER_BASIS_MOD_PRIME : thm := BPowerBasisExtension04.NUMBER_FIELD_POWER_BASIS_MOD_PRIME
def NUMBER_FIELD_ONE_PRIME_GENERATOR : thm := BPowerBasisExtension04.NUMBER_FIELD_ONE_PRIME_GENERATOR
def NUMBER_FIELD_LOCAL_POWER_BASIS : thm := BPowerBasisExtension04.NUMBER_FIELD_LOCAL_POWER_BASIS

/-- `needs "ANT/power_basis_extension.ml"`: already done by importing this module. -/
def ensurePowerBasisExtension : IO Unit := pure ()

end SessionANT.PowerBasisExtension
