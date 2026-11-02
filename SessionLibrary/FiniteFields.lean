/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/finite_fields.ml.                           -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/FiniteFields.lean

  The session half of the finite_fields.ml translation: it supplies
  HolLibrary.FiniteFields's dependencies from Session,
  SessionLibrary.Galois and SessionLibrary.RingGroups, and exports every
  name under its HOL Light name.  Importing this module is
  `needs "Library/finite_fields.ml"`; its `needs` of galois.ml and
  ring_groups.ml are the imports of those modules.  The bundles are built by
  `initialize` when the module is loaded, in file order.
-/

import Session
import HolLibrary.FiniteFields
import SessionLibrary.Galois
import SessionLibrary.RingGroups

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.FiniteFields

/-- The core theorems finite_fields.ml uses. -/
def core1 : HolLibrary.FiniteFields.CoreThms1 where
  ALGEBRAICALLY_CLOSED_FIELD_FINITE_SUBFIELD := SessionLibrary.FieldTheory.«ALGEBRAICALLY_CLOSED_FIELD_FINITE_SUBFIELD»
  ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH := SessionLibrary.FieldTheory.«ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH»
  ALGEBRAIC_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«ALGEBRAIC_IMP_FIELD_EXTENSION»
  ALGEBRA_NORM_EQ_0 := SessionLibrary.FieldTheory.«ALGEBRA_NORM_EQ_0»
  ALGEBRA_NORM_INV := SessionLibrary.RingDet.«ALGEBRA_NORM_INV»
  ALGEBRA_NORM_MUL := SessionLibrary.RingDet.«ALGEBRA_NORM_MUL»
  ALGEBRA_NORM_POW := SessionLibrary.RingDet.«ALGEBRA_NORM_POW»
  ALGEBRA_TRACE_ADD := SessionLibrary.RingDet.«ALGEBRA_TRACE_ADD»
  ALGEBRA_TRACE_NEG := SessionLibrary.RingDet.«ALGEBRA_TRACE_NEG»
  ALGEBRA_TRACE_NORM_FINITE_FIELD := SessionLibrary.Galois.«ALGEBRA_TRACE_NORM_FINITE_FIELD»
  ALGEBRA_TRACE_NORM_GALOIS := SessionLibrary.Galois.«ALGEBRA_TRACE_NORM_GALOIS»
  ALGEBRA_TRACE_NORM_IN_CARRIER := SessionLibrary.RingDet.«ALGEBRA_TRACE_NORM_IN_CARRIER»
  ALGEBRA_TRACE_SUB := SessionLibrary.RingDet.«ALGEBRA_TRACE_SUB»
  ALGEBRA_TRACE_SURJECTIVE := SessionLibrary.FieldTheory.«ALGEBRA_TRACE_SURJECTIVE»
  CARD_DELETE := Session.CARD_DELETE
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_EQ_FIBRES_HAS_SIZE := SessionLibrary.Card.«CARD_EQ_FIBRES_HAS_SIZE»
  CARD_EQ_IMAGE := SessionLibrary.Card.«CARD_EQ_IMAGE»
  CARD_EXTENSION_DEGREE := SessionLibrary.FieldTheory.«CARD_EXTENSION_DEGREE»
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARRIER_SUBFIELD_GENERATED_SUBFIELD := SessionLibrary.FieldTheory.«CARRIER_SUBFIELD_GENERATED_SUBFIELD»
  CARRIER_SUBFIELD_OF := SessionLibrary.FieldTheory.«CARRIER_SUBFIELD_OF»
  CARRIER_SUBGROUP_GENERATED_BY_SING := SessionLibrary.GroupTheory.«CARRIER_SUBGROUP_GENERATED_BY_SING»
  CONG_IMP_EQ := SessionLibrary.Pocklington.«CONG_IMP_EQ»
  CYCLIC_GALOIS_GROUP_FINITE_FIELD := SessionLibrary.Galois.«CYCLIC_GALOIS_GROUP_FINITE_FIELD»
  CYCLIC_GROUP_ELEMENT_ORDER := SessionLibrary.GroupTheory.«CYCLIC_GROUP_ELEMENT_ORDER»
  CYCLIC_IMP_ABELIAN_GROUP := SessionLibrary.GroupTheory.«CYCLIC_IMP_ABELIAN_GROUP»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIVIDES_DIV_MULT := Session.DIVIDES_DIV_MULT
  DIVIDES_EXP_MINUS1 := SessionLibrary.Prime.«DIVIDES_EXP_MINUS1»
  DIVIDES_GCD_LEFT := SessionLibrary.Prime.«DIVIDES_GCD_LEFT»
  DIVIDES_LE := Session.DIVIDES_LE
  DIVIDES_PRIME_PRIME := SessionLibrary.Prime.«DIVIDES_PRIME_PRIME»
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  DIVIDES_REXP := SessionLibrary.Prime.«DIVIDES_REXP»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  DIVISION := Session.DIVISION
  DIV_MULT := Session.DIV_MULT
  EQ_EXP := Session.EQ_EXP
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXP := Session.EXP
  EXP_1 := Session.EXP_1
  EXP_ADD := Session.EXP_ADD
  EXP_EQ_0 := Session.EXP_EQ_0
  EXP_EXP := Session.EXP_EXP
  EXP_ZERO := Session.EXP_ZERO
  EXTENSION := Session.EXTENSION
  EXTENSION_DEGREE_SIMPLE := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_SIMPLE»
  FIELD_DIV_EQ_0 := SessionLibrary.RingTheory.«FIELD_DIV_EQ_0»
  FIELD_EXTENSION_IMP_HOMOMORPHISM := SessionLibrary.FieldTheory.«FIELD_EXTENSION_IMP_HOMOMORPHISM»
  FIELD_EXTENSION_INTO_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_INTO_SUBFIELD_GENERATED»
  FIELD_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_INV_EQ_0 := SessionLibrary.RingTheory.«FIELD_INV_EQ_0»
  FIELD_MONIC_IRREDUCIBLE_ASSOCIATE := SessionLibrary.RingTheory.«FIELD_MONIC_IRREDUCIBLE_ASSOCIATE»
  FIELD_MUL_EQ_0 := SessionLibrary.RingTheory.«FIELD_MUL_EQ_0»
  FIELD_MUL_RINV := SessionLibrary.RingTheory.«FIELD_MUL_RINV»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FIELD_POW_EQ_0 := SessionLibrary.RingTheory.«FIELD_POW_EQ_0»
  FIELD_RING_HOMOMORPHISM_MONOMORPHISM := SessionLibrary.RingTheory.«FIELD_RING_HOMOMORPHISM_MONOMORPHISM»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FIELD_UNIT := SessionLibrary.RingTheory.«FIELD_UNIT»
  FIELD_UNIT_GROUP := SessionLibrary.RingGroups.«FIELD_UNIT_GROUP»
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_DIFF := Session.FINITE_DIFF
  FINITE_FIELD_CARD_GE_2 := SessionLibrary.RingTheory.«FINITE_FIELD_CARD_GE_2»
  FINITE_FIELD_CARD_ROOTS_OF_UNITY := SessionLibrary.RingTheory.«FINITE_FIELD_CARD_ROOTS_OF_UNITY»
  FINITE_FIELD_GALOIS_EXTENSION := SessionLibrary.Galois.«FINITE_FIELD_GALOIS_EXTENSION»
  FINITE_FIELD_IMP_PERFECT := SessionLibrary.FieldTheory.«FINITE_FIELD_IMP_PERFECT»
  FINITE_FIELD_INTERMEDIATE_FIELDS := SessionLibrary.Galois.«FINITE_FIELD_INTERMEDIATE_FIELDS»
  FINITE_FIELD_PRIMITIVE_ELEMENT := SessionLibrary.FieldTheory.«FINITE_FIELD_PRIMITIVE_ELEMENT»
  FINITE_FINITE_FIELD_EXTENSION := SessionLibrary.FieldTheory.«FINITE_FINITE_FIELD_EXTENSION»
  FINITE_GALOIS_SUBFIELDS_ELEMENT := SessionLibrary.Galois.«FINITE_GALOIS_SUBFIELDS_ELEMENT»
  FINITE_GALOIS_SUBFIELDS_FINITE := SessionLibrary.Galois.«FINITE_GALOIS_SUBFIELDS_FINITE»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_IMP_ALGEBRAIC_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_ALGEBRAIC_EXTENSION»
  FINITE_INTEGRAL_DOMAIN_CHAR := SessionLibrary.RingTheory.«FINITE_INTEGRAL_DOMAIN_CHAR»
  FINITE_INTEGRAL_DOMAIN_IMP_FIELD := SessionLibrary.RingTheory.«FINITE_INTEGRAL_DOMAIN_IMP_FIELD»
  FINITE_INTEGRAL_DOMAIN_POW_CARD := SessionLibrary.FieldTheory.«FINITE_INTEGRAL_DOMAIN_POW_CARD»
  FINITE_INTEGRAL_DOMAIN_SIZE := SessionLibrary.FieldTheory.«FINITE_INTEGRAL_DOMAIN_SIZE»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_POLY_DEG_LE := SessionLibrary.RingTheory.«FINITE_POLY_DEG_LE»
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_RING_MONOMORPHIC_PREIMAGE := SessionLibrary.RingTheory.«FINITE_RING_MONOMORPHIC_PREIMAGE»
  FINITE_SIMPLE_ALGEBRAIC_EXTENSION := SessionLibrary.FieldTheory.«FINITE_SIMPLE_ALGEBRAIC_EXTENSION»
  FINITE_SUBFIELD_EXPLICIT := SessionLibrary.FieldTheory.«FINITE_SUBFIELD_EXPLICIT»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FUN_EQ_THM := Session.FUN_EQ_THM
  GALOIS_GROUP := SessionLibrary.Galois.«GALOIS_GROUP»
  GALOIS_GROUP_FINITE_FIELD := SessionLibrary.Galois.«GALOIS_GROUP_FINITE_FIELD»
  GALOIS_GROUP_FROBENIUS := SessionLibrary.Galois.«GALOIS_GROUP_FROBENIUS»
  GALOIS_GROUP_PERMUTES := SessionLibrary.Galois.«GALOIS_GROUP_PERMUTES»
  GALOIS_GROUP_POW_RING_POW := SessionLibrary.Galois.«GALOIS_GROUP_POW_RING_POW»
  GALOIS_GROUP_RESTRICTION_NORMAL := SessionLibrary.Galois.«GALOIS_GROUP_RESTRICTION_NORMAL»
  GALOIS_IMP_NORMAL_EXTENSION := SessionLibrary.Galois.«GALOIS_IMP_NORMAL_EXTENSION»
  GALOIS_IMP_SEPARABLE_EXTENSION := SessionLibrary.Galois.«GALOIS_IMP_SEPARABLE_EXTENSION»
  GROUP_ELEMENT_ORDER_UNIQUE := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_UNIQUE»
  GROUP_HOMOMORPHISM := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM»
  GROUP_NPOW := SessionLibrary.GroupTheory.«GROUP_NPOW»
  GROUP_POW_EQ := SessionLibrary.GroupTheory.«GROUP_POW_EQ»
  GROUP_POW_EQ_ID := SessionLibrary.GroupTheory.«GROUP_POW_EQ_ID»
  GROUP_ZPOW_REM_ELEMENT_ORDER := SessionLibrary.GroupTheory.«GROUP_ZPOW_REM_ELEMENT_ORDER»
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_IMAGE_INJ := Session.HAS_SIZE_IMAGE_INJ
  HAS_SIZE_NUMSEG_LT := Session.HAS_SIZE_NUMSEG_LT
  HILBERT_90_ADDITIVE_CYCLIC_EQ := SessionLibrary.Galois.«HILBERT_90_ADDITIVE_CYCLIC_EQ»
  HILBERT_90_CYCLIC_EQ := SessionLibrary.Galois.«HILBERT_90_CYCLIC_EQ»
  IMP_CONJ := Session.IMP_CONJ
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING»
  INTEGRAL_DOMAIN_MUL_LCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_LCANCEL»
  INTEGRAL_DOMAIN_MUL_RCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_RCANCEL»
  INTEGRAL_DOMAIN_NONTRIVIAL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_NONTRIVIAL»
  INTEGRAL_DOMAIN_POLY_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_POLY_RING»
  INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE»
  INT_LT_REM := Session.INT_LT_REM
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_REM_POS := Session.INT_REM_POS
  IN_DELETE := Session.IN_DELETE
  IN_DIFF := Session.IN_DIFF
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_FINITE_GALOIS_SUBFIELDS := SessionLibrary.Galois.«IN_FINITE_GALOIS_SUBFIELDS»
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_RING_POLYNOMIAL_CARRIER_COMPOSE := SessionLibrary.RingTheory.«IN_RING_POLYNOMIAL_CARRIER_COMPOSE»
  IN_SING := Session.IN_SING
  IN_UNIV := Session.IN_UNIV
  IRREDUCIBLE_IMP_POLY_DEG_NZ := SessionLibrary.RingTheory.«IRREDUCIBLE_IMP_POLY_DEG_NZ»
  ISOMORPHIC_FINITE_FIELDS := SessionLibrary.FieldTheory.«ISOMORPHIC_FINITE_FIELDS»
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LEFT_ADD_DISTRIB := Session.LEFT_ADD_DISTRIB
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_1 := Session.LE_1
  LE_EXP := Session.LE_EXP
  LE_TRANS := Session.LE_TRANS
  LT_REFL := Session.LT_REFL
  MINIMAL_POLYNOMIAL := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL»
  MINIMAL_POLYNOMIAL_ASSOCIATES_IRREDUCIBLE := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_ASSOCIATES_IRREDUCIBLE»
  MONIC_ASSOCIATES_EQ := SessionLibrary.RingTheory.«MONIC_ASSOCIATES_EQ»
/-- The core theorems finite_fields.ml uses. -/
def core2 : HolLibrary.FiniteFields.CoreThms2 where
  MONIC_POLY_PRODUCT := SessionLibrary.RingTheory.«MONIC_POLY_PRODUCT»
  MONIC_VAR_POW_SUB_VAR := SessionLibrary.FieldTheory.«MONIC_VAR_POW_SUB_VAR»
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_EQ_1 := Session.MULT_EQ_1
  MULT_SYM := Session.MULT_SYM
  NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS := SessionLibrary.RingTheory.«NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS»
  NORMAL_IMP_ALGEBRAIC_EXTENSION := SessionLibrary.FieldTheory.«NORMAL_IMP_ALGEBRAIC_EXTENSION»
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_SUC := Session.NOT_SUC
  NSUM_CLAUSES := Session.NSUM_CLAUSES
  NSUM_CONST := Session.NSUM_CONST
  NSUM_EQ := Session.NSUM_EQ
  NSUM_GROUP := Session.NSUM_GROUP
  NUMSEG_CLAUSES_LT := Session.NUMSEG_CLAUSES_LT
  PERFECT_FIELD_IMP_SEPARABLE_EXTENSION := SessionLibrary.FieldTheory.«PERFECT_FIELD_IMP_SEPARABLE_EXTENSION»
  PID_IMP_UFD := SessionLibrary.RingTheory.«PID_IMP_UFD»
  PID_POLY_RING := SessionLibrary.RingTheory.«PID_POLY_RING»
  POLY_CLAUSES := SessionLibrary.RingTheory.«POLY_CLAUSES»
  POLY_DEG_CONST := SessionLibrary.RingTheory.«POLY_DEG_CONST»
  POLY_DEG_DIVIDES_LE := SessionLibrary.RingTheory.«POLY_DEG_DIVIDES_LE»
  POLY_DEG_EQ_0_UNIT := SessionLibrary.RingTheory.«POLY_DEG_EQ_0_UNIT»
  POLY_DEG_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_DEG_MONOMORPHIC_IMAGE»
  POLY_DEG_MUL := SessionLibrary.RingTheory.«POLY_DEG_MUL»
  POLY_DEG_PRODUCT_MONIC := SessionLibrary.RingTheory.«POLY_DEG_PRODUCT_MONIC»
  POLY_EQ_0_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_EQ_0_MONOMORPHIC_IMAGE»
  POLY_EVAL_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_EVAL_HOMOMORPHIC_IMAGE»
  POLY_EVAL_VAR_POW_SUB_VAR := SessionLibrary.FieldTheory.«POLY_EVAL_VAR_POW_SUB_VAR»
  POLY_MONOMIAL_IN_CARRIER := SessionLibrary.RingTheory.«POLY_MONOMIAL_IN_CARRIER»
  POLY_RING_CLAUSES := SessionLibrary.RingTheory.«POLY_RING_CLAUSES»
  POLY_ROOT_BOUND_EXTENSION := SessionLibrary.FieldTheory.«POLY_ROOT_BOUND_EXTENSION»
  POLY_SEPARABLE_IMP_SQUAREFREE := SessionLibrary.RingTheory.«POLY_SEPARABLE_IMP_SQUAREFREE»
  POLY_SEPARABLE_VAR_POW_SUB_VAR := SessionLibrary.FieldTheory.«POLY_SEPARABLE_VAR_POW_SUB_VAR»
  POLY_SPLITS_DIVISOR := SessionLibrary.RingTheory.«POLY_SPLITS_DIVISOR»
  POLY_SPLITS_HAS_ROOT := SessionLibrary.RingTheory.«POLY_SPLITS_HAS_ROOT»
  POLY_SPLITS_OVER_DISTINCT_ROOTS := SessionLibrary.FieldTheory.«POLY_SPLITS_OVER_DISTINCT_ROOTS»
  POLY_SPLITS_OVER_SEPARABLE_ROOT_COUNT := SessionLibrary.FieldTheory.«POLY_SPLITS_OVER_SEPARABLE_ROOT_COUNT»
  POLY_VAR_POW_SUB_VAR := SessionLibrary.FieldTheory.«POLY_VAR_POW_SUB_VAR»
  PRIME_1 := SessionLibrary.Prime.«PRIME_1»
  PRIME_DIVEXP := SessionLibrary.Prime.«PRIME_DIVEXP»
  PRIME_FACTOR := SessionLibrary.Prime.«PRIME_FACTOR»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_SUBFIELD_HOMOMORPHISM_EXISTS := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_HOMOMORPHISM_EXISTS»
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RCANCEL := SessionLibrary.RingTheory.«RING_ADD_RCANCEL»
  RING_ASSOCIATES_DIVIDES := SessionLibrary.RingTheory.«RING_ASSOCIATES_DIVIDES»
  RING_ASSOCIATES_IRREDUCIBLE := SessionLibrary.RingTheory.«RING_ASSOCIATES_IRREDUCIBLE»
  RING_ASSOCIATES_REFL := SessionLibrary.RingTheory.«RING_ASSOCIATES_REFL»
  RING_ASSOCIATES_RMUL := SessionLibrary.RingTheory.«RING_ASSOCIATES_RMUL»
  RING_CARRIER_NONEMPTY := SessionLibrary.RingTheory.«RING_CARRIER_NONEMPTY»
  RING_CARRIER_SUBFIELD_GENERATED_SUBSET := SessionLibrary.FieldTheory.«RING_CARRIER_SUBFIELD_GENERATED_SUBSET»
  RING_CHAR_DIVIDES_ORDER := SessionLibrary.RingTheory.«RING_CHAR_DIVIDES_ORDER»
  RING_CHAR_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_CHAR_MONOMORPHIC_IMAGE»
  RING_COPRIME_DISTINCT_MONIC_IRREDUCIBLES := SessionLibrary.RingTheory.«RING_COPRIME_DISTINCT_MONIC_IRREDUCIBLES»
  RING_COPRIME_PRODUCT_DIVIDES := SessionLibrary.RingTheory.«RING_COPRIME_PRODUCT_DIVIDES»
  RING_DIV := SessionLibrary.RingTheory.«RING_DIV»
  RING_DIVIDES_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_DIVIDES_HOMOMORPHIC_IMAGE»
  RING_DIVIDES_IN_CARRIER := SessionLibrary.RingTheory.«RING_DIVIDES_IN_CARRIER»
  RING_DIVIDES_IRREDUCIBLE_ROOT := SessionLibrary.FieldTheory.«RING_DIVIDES_IRREDUCIBLE_ROOT»
  RING_DIVIDES_PRODUCT_SUBSET := SessionLibrary.RingTheory.«RING_DIVIDES_PRODUCT_SUBSET»
  RING_DIVIDES_TRANS := SessionLibrary.RingTheory.«RING_DIVIDES_TRANS»
  RING_ENDOMORPHISM_POW_CARD := SessionLibrary.FieldTheory.«RING_ENDOMORPHISM_POW_CARD»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_POLY_RINGS := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_RINGS»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_INV_INV := SessionLibrary.RingTheory.«RING_INV_INV»
  RING_IRREDUCIBLE_COPRIME_EQ := SessionLibrary.RingTheory.«RING_IRREDUCIBLE_COPRIME_EQ»
  RING_IRREDUCIBLE_IN_CARRIER := SessionLibrary.RingTheory.«RING_IRREDUCIBLE_IN_CARRIER»
  RING_ISOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_EQ_0 := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EQ_0»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_INJECTIVE_EQ := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INJECTIVE_EQ»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_NEG_EQ_0 := SessionLibrary.RingTheory.«RING_NEG_EQ_0»
  RING_ORDER_0 := SessionLibrary.RingTheory.«RING_ORDER_0»
  RING_ORDER_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_ORDER_MONOMORPHIC_IMAGE»
  RING_ORDER_POW := SessionLibrary.RingTheory.«RING_ORDER_POW»
  RING_POLYNOMIAL := SessionLibrary.RingTheory.«RING_POLYNOMIAL»
  RING_POLYNOMIAL_POW := SessionLibrary.RingTheory.«RING_POLYNOMIAL_POW»
  RING_POLYNOMIAL_SUB := SessionLibrary.RingTheory.«RING_POLYNOMIAL_SUB»
  RING_POLYNOMIAL_VAR := SessionLibrary.RingTheory.«RING_POLYNOMIAL_VAR»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_1 := SessionLibrary.RingTheory.«RING_POW_1»
  RING_POW_EQ_1 := SessionLibrary.RingTheory.«RING_POW_EQ_1»
  RING_POW_INV := SessionLibrary.RingTheory.«RING_POW_INV»
  RING_POW_POW := SessionLibrary.RingTheory.«RING_POW_POW»
  RING_POW_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_POW_SUBFIELD_GENERATED»
  RING_POW_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_POW_SUBRING_GENERATED»
  RING_POW_ZERO := SessionLibrary.RingTheory.«RING_POW_ZERO»
  RING_PRODUCT := SessionLibrary.RingTheory.«RING_PRODUCT»
  RING_PRODUCT_NSUM := SessionLibrary.RingTheory.«RING_PRODUCT_NSUM»
  RING_PRODUCT_SING := SessionLibrary.RingTheory.«RING_PRODUCT_SING»
  RING_SQUAREFREE_DIVIDES := SessionLibrary.RingTheory.«RING_SQUAREFREE_DIVIDES»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_UNIT_POLY_DOMAIN := SessionLibrary.RingTheory.«RING_UNIT_POLY_DOMAIN»
  ROOTS_OF_UNITY_HAS_SIZE_PRIMITIVE := SessionLibrary.RingTheory.«ROOTS_OF_UNITY_HAS_SIZE_PRIMITIVE»
  ROOTS_OF_UNITY_RING_ORDER := SessionLibrary.RingTheory.«ROOTS_OF_UNITY_RING_ORDER»
  SING_SUBSET := Session.SING_SUBSET
  SPLITTING_EXTENSION_EXISTS_BIGENOUGH := SessionLibrary.FieldTheory.«SPLITTING_EXTENSION_EXISTS_BIGENOUGH»
  SUBFIELD_IMP_SUBRING_OF := SessionLibrary.FieldTheory.«SUBFIELD_IMP_SUBRING_OF»
  SUBFIELD_OF_FIXPOINTS := SessionLibrary.FieldTheory.«SUBFIELD_OF_FIXPOINTS»
  SUBFIELD_OF_MONOMORPHIC_IMAGE := SessionLibrary.FieldTheory.«SUBFIELD_OF_MONOMORPHIC_IMAGE»
  SUBRING_GENERATED_INC_GEN := SessionLibrary.RingTheory.«SUBRING_GENERATED_INC_GEN»
  SUBRING_GENERATED_MINIMAL := SessionLibrary.RingTheory.«SUBRING_GENERATED_MINIMAL»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUB_0 := Session.SUB_0
  SUC_SUB1 := Session.SUC_SUB1
  TRIVIAL_RING_HAS_SIZE_1 := SessionLibrary.RingTheory.«TRIVIAL_RING_HAS_SIZE_1»
  UNIT_GROUP := SessionLibrary.RingGroups.«UNIT_GROUP»
  UNIT_GROUP_POW := SessionLibrary.RingGroups.«UNIT_GROUP_POW»
  WLOG_LE := Session.WLOG_LE
  abelian_group := SessionLibrary.GroupTheory.«abelian_group»
  algebraic_extension := SessionLibrary.FieldTheory.«algebraic_extension»
  algebraically_closed_field := SessionLibrary.FieldTheory.«algebraically_closed_field»
  divides := Session.divides
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  galois_extension := SessionLibrary.Galois.«galois_extension»
  group_homomorphism := SessionLibrary.GroupTheory.«group_homomorphism»
  isomorphic_ring := SessionLibrary.RingTheory.«isomorphic_ring»
  o_THM := Session.o_THM
  pairwise := Session.pairwise
  permutes := SessionLibrary.Permutations.«permutes»
  poly_splits_over := SessionLibrary.FieldTheory.«poly_splits_over»
  ring_associates := SessionLibrary.RingTheory.«ring_associates»
  ring_coprime := SessionLibrary.RingTheory.«ring_coprime»
  ring_div := SessionLibrary.RingTheory.«ring_div»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_endomorphism := SessionLibrary.RingTheory.«ring_endomorphism»
  ring_irreducible := SessionLibrary.RingTheory.«ring_irreducible»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  splitting_extension := SessionLibrary.FieldTheory.«splitting_extension»

/-- What finite_fields.ml uses from Session. -/
def deps : HolLibrary.FiniteFields.FiniteFieldsDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  TAUT t := ExceptT.mk (Session.TAUT t)
  INDUCT_TAC := Session.INDUCT_TAC
  RING_RULE t := ExceptT.mk (SessionLibrary.RingTheory.RING_RULE t)
  FIELD_TAC := SessionLibrary.RingTheory.FIELD_TAC
  GROUP_TAC := SessionLibrary.GroupTheory.GROUP_TAC
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  HAS_SIZE_CONV := Session.HAS_SIZE_CONV
  EXPAND_CASES_CONV := Session.EXPAND_CASES_CONV
  DIVIDES_CONV := SessionLibrary.Prime.DIVIDES_CONV
  prioritize_num := do
    match ← HolCore.Kernel.mk_type "num" [] with
    | .ok ty => Session.prioritize_overload ty
    | .error e => throw (IO.userError e)
  num_CONV := Session.num_CONV
  core1 := core1
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} (name : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in finite_fields.ml order. -/
initialize BBasicFacts : HolLibrary.FiniteFields.BasicFacts ←
  ioB "setupBasicFacts" (HolLibrary.FiniteFields.setupBasicFacts deps).run
initialize BMultiplicativeGroup : HolLibrary.FiniteFields.MultiplicativeGroup ←
  ioB "setupMultiplicativeGroup" (HolLibrary.FiniteFields.setupMultiplicativeGroup deps).run
initialize BSubfieldsHomomorphisms : HolLibrary.FiniteFields.SubfieldsHomomorphisms ←
  ioB "setupSubfieldsHomomorphisms" (HolLibrary.FiniteFields.setupSubfieldsHomomorphisms deps).run
initialize BNormTrace : HolLibrary.FiniteFields.NormTrace ←
  ioB "setupNormTrace" (HolLibrary.FiniteFields.setupNormTrace deps BMultiplicativeGroup).run
initialize BIrreducibleXPow : HolLibrary.FiniteFields.IrreducibleXPow ←
  ioB "setupIrreducibleXPow" (HolLibrary.FiniteFields.setupIrreducibleXPow deps).run
initialize BEveryDegree : HolLibrary.FiniteFields.EveryDegree ←
  ioB "setupEveryDegree" (HolLibrary.FiniteFields.setupEveryDegree deps BIrreducibleXPow).run
initialize BLayers : HolLibrary.FiniteFields.Layers ←
  ioB "setupLayers" (HolLibrary.FiniteFields.setupLayers deps BBasicFacts BIrreducibleXPow).run
initialize BRabinTest : HolLibrary.FiniteFields.RabinTest ←
  ioB "setupRabinTest" (HolLibrary.FiniteFields.setupRabinTest deps BIrreducibleXPow).run

-- BasicFacts
def FINITE_FIELD_ELEMENT_POW : thm := BBasicFacts.FINITE_FIELD_ELEMENT_POW
def FINITE_FIELD_CARD_CHAR_POWER : thm := BBasicFacts.FINITE_FIELD_CARD_CHAR_POWER

-- MultiplicativeGroup
def FINITE_INTEGRAL_DOMAIN_POW_CARD_SUB_1 : thm := BMultiplicativeGroup.FINITE_INTEGRAL_DOMAIN_POW_CARD_SUB_1
def FINITE_FIELD_ROOTS_OF_UNITY : thm := BMultiplicativeGroup.FINITE_FIELD_ROOTS_OF_UNITY
def FINITE_FIELD_PRIMITIVE_ROOT : thm := BMultiplicativeGroup.FINITE_FIELD_PRIMITIVE_ROOT
def FINITE_FIELD_CYCLIC_UNIT_GROUP : thm := BMultiplicativeGroup.FINITE_FIELD_CYCLIC_UNIT_GROUP

-- SubfieldsHomomorphisms
def FINITE_FIELD_SUBFIELD_CARD : thm := BSubfieldsHomomorphisms.FINITE_FIELD_SUBFIELD_CARD
def FINITE_FIELD_HOMOMORPHISM_IMAGE : thm := BSubfieldsHomomorphisms.FINITE_FIELD_HOMOMORPHISM_IMAGE
def FINITE_FIELD_HOMOMORPHISM_EXISTS : thm := BSubfieldsHomomorphisms.FINITE_FIELD_HOMOMORPHISM_EXISTS

-- NormTrace
def ALGEBRA_NORM_FINITE_FIELD_POW : thm := BNormTrace.ALGEBRA_NORM_FINITE_FIELD_POW
def ALGEBRA_TRACE_SURJECTIVE_FINITE : thm := BNormTrace.ALGEBRA_TRACE_SURJECTIVE_FINITE
def ALGEBRA_NORM_SURJECTIVE_FINITE : thm := BNormTrace.ALGEBRA_NORM_SURJECTIVE_FINITE
def ALGEBRA_TRACE_FIBRE_FINITE : thm := BNormTrace.ALGEBRA_TRACE_FIBRE_FINITE
def ALGEBRA_NORM_FIBRE_FINITE : thm := BNormTrace.ALGEBRA_NORM_FIBRE_FINITE
def HILBERT_90_FINITE_FIELD : thm := BNormTrace.HILBERT_90_FINITE_FIELD
def HILBERT_90_ADDITIVE_FINITE_FIELD : thm := BNormTrace.HILBERT_90_ADDITIVE_FINITE_FIELD

-- IrreducibleXPow
def FINITE_FIELD_POW_CARD_EXP : thm := BIrreducibleXPow.FINITE_FIELD_POW_CARD_EXP
def FINITE_FIELD_IRREDUCIBLE_ROOT_POW : thm := BIrreducibleXPow.FINITE_FIELD_IRREDUCIBLE_ROOT_POW
def FINITE_FIELD_IRREDUCIBLE_ROOTS : thm := BIrreducibleXPow.FINITE_FIELD_IRREDUCIBLE_ROOTS
def IRREDUCIBLE_DIVIDES_X_POW_SUB_X : thm := BIrreducibleXPow.IRREDUCIBLE_DIVIDES_X_POW_SUB_X
def X_POW_SUB_X_FINITE_FIELD : thm := BIrreducibleXPow.X_POW_SUB_X_FINITE_FIELD
def X_POW_SUB_X_EQ_PRODUCT_IRREDUCIBLES : thm := BIrreducibleXPow.X_POW_SUB_X_EQ_PRODUCT_IRREDUCIBLES
def FINITE_FIELD_IRREDUCIBLE_COUNT : thm := BIrreducibleXPow.FINITE_FIELD_IRREDUCIBLE_COUNT

-- EveryDegree
def FINITE_FIELD_EXTENSION_EXISTS : thm := BEveryDegree.FINITE_FIELD_EXTENSION_EXISTS
def FINITE_FIELD_IRREDUCIBLE_EXISTS : thm := BEveryDegree.FINITE_FIELD_IRREDUCIBLE_EXISTS

-- Layers
def FINITE_FIELD_POW_ITERATE : thm := BLayers.FINITE_FIELD_POW_ITERATE
def FINITE_FIELD_ALGEBRAIC_CLOSURE_LAYER : thm := BLayers.FINITE_FIELD_ALGEBRAIC_CLOSURE_LAYER
def FINITE_FIELD_IRREDUCIBLE_ROOT_EXISTS : thm := BLayers.FINITE_FIELD_IRREDUCIBLE_ROOT_EXISTS
def FINITE_FIELD_NORMAL_IMP_GALOIS : thm := BLayers.FINITE_FIELD_NORMAL_IMP_GALOIS
def FINITE_GALOIS_SUBFIELDS_FINITE_FIELD : thm := BLayers.FINITE_GALOIS_SUBFIELDS_FINITE_FIELD
def FINITE_FIELD_LAYERS_COVER : thm := BLayers.FINITE_FIELD_LAYERS_COVER
def FINITE_FIELD_LAYER_POW : thm := BLayers.FINITE_FIELD_LAYER_POW
def ABELIAN_GALOIS_GROUP_FINITE_FIELD : thm := BLayers.ABELIAN_GALOIS_GROUP_FINITE_FIELD
def GALOIS_GROUP_FINITE_FIELD_EXPONENT : thm := BLayers.GALOIS_GROUP_FINITE_FIELD_EXPONENT

-- RabinTest
def RABIN_IRREDUCIBILITY_NECESSARY : thm := BRabinTest.RABIN_IRREDUCIBILITY_NECESSARY
def RABIN_IRREDUCIBILITY_SUFFICIENT : thm := BRabinTest.RABIN_IRREDUCIBILITY_SUFFICIENT
def RABIN_IRREDUCIBILITY_TEST : thm := BRabinTest.RABIN_IRREDUCIBILITY_TEST
/-- `needs "Library/finite_fields.ml"`: already done by importing this module. -/
def ensureFiniteFields : IO Unit := pure ()

end SessionLibrary.FiniteFields
