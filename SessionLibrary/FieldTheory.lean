/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/fieldtheory.ml.                       -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/FieldTheory.lean

  The session half of the fieldtheory.ml translation: it supplies
  HolLibrary.FieldTheory's dependencies from Session, SessionLibrary.Matroids
  and SessionLibrary.RingTheory, and exports every name under its HOL Light
  name.  Importing this module is `needs "Library/fieldtheory.ml"`; its
  `needs` of matroids.ml and ringtheory.ml are the imports of those modules.
  The bundles are built by `initialize` when the module is loaded, in file
  order.
-/

import Session
import HolLibrary.FieldTheory
import SessionLibrary.Matroids
import SessionLibrary.RingTheory

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.FieldTheory

/-- The core theorems fieldtheory.ml uses. -/
def core1 : HolLibrary.FieldTheory.CoreThms1 where
  AND_FORALL_THM := Session.AND_FORALL_THM
  ARITH_EQ := Session.ARITH_EQ
  CANTOR_THM_UNIV := SessionLibrary.Card.«CANTOR_THM_UNIV»
  CARD_ADD_CONG := SessionLibrary.Card.«CARD_ADD_CONG»
  CARD_DIFF_ABSORB := SessionLibrary.Card.«CARD_DIFF_ABSORB»
  CARD_DISJOINT_UNION := SessionLibrary.Card.«CARD_DISJOINT_UNION»
  CARD_EQ_IMAGE := SessionLibrary.Card.«CARD_EQ_IMAGE»
  CARD_EQ_IMP_LE := SessionLibrary.Card.«CARD_EQ_IMP_LE»
  CARD_EQ_POLY_RING_FINITE := SessionLibrary.RingTheory.«CARD_EQ_POLY_RING_FINITE»
  CARD_EQ_REFL := SessionLibrary.Card.«CARD_EQ_REFL»
  CARD_EQ_REFL_IMP := SessionLibrary.Card.«CARD_EQ_REFL_IMP»
  CARD_EQ_SYM := SessionLibrary.Card.«CARD_EQ_SYM»
  CARD_EQ_TRANS := SessionLibrary.Card.«CARD_EQ_TRANS»
  CARD_FINITE_CONG := SessionLibrary.Card.«CARD_FINITE_CONG»
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_LET_TRANS := SessionLibrary.Card.«CARD_LET_TRANS»
  CARD_LE_ADDL := SessionLibrary.Card.«CARD_LE_ADDL»
  CARD_LE_ADDR := SessionLibrary.Card.«CARD_LE_ADDR»
  CARD_LE_ANTISYM := SessionLibrary.Card.«CARD_LE_ANTISYM»
  CARD_LE_FINITE := SessionLibrary.Card.«CARD_LE_FINITE»
  CARD_LE_FINITE_INFINITE := SessionLibrary.Card.«CARD_LE_FINITE_INFINITE»
  CARD_LE_IMAGE := SessionLibrary.Card.«CARD_LE_IMAGE»
  CARD_LE_MUL := SessionLibrary.Card.«CARD_LE_MUL»
  CARD_LE_REFL := SessionLibrary.Card.«CARD_LE_REFL»
  CARD_LE_SUBSET := SessionLibrary.Card.«CARD_LE_SUBSET»
  CARD_LE_TRANS := SessionLibrary.Card.«CARD_LE_TRANS»
  CARD_LE_UNIONS := SessionLibrary.Card.«CARD_LE_UNIONS»
  CARD_LE_UNIV := SessionLibrary.Card.«CARD_LE_UNIV»
  CARD_LT_IMP_LE := SessionLibrary.Card.«CARD_LT_IMP_LE»
  CARD_MUL2_ABSORB_LE := SessionLibrary.Card.«CARD_MUL2_ABSORB_LE»
  CARD_MUL_FINITE := SessionLibrary.Card.«CARD_MUL_FINITE»
  CARD_MUL_FINITE_EQ := SessionLibrary.Card.«CARD_MUL_FINITE_EQ»
  CARD_MUL_LID := SessionLibrary.Card.«CARD_MUL_LID»
  CARD_MUL_LT_INFINITE := SessionLibrary.Card.«CARD_MUL_LT_INFINITE»
  CARD_MUL_RID := SessionLibrary.Card.«CARD_MUL_RID»
  CARD_NUMSEG := Session.CARD_NUMSEG
  CARD_NUMSEG_1 := Session.CARD_NUMSEG_1
  CARD_PRIME_SUBRING := SessionLibrary.RingTheory.«CARD_PRIME_SUBRING»
  CARD_PSUBSET := Session.CARD_PSUBSET
  CARD_SING_LE := SessionLibrary.Card.«CARD_SING_LE»
  CARRIER_SUBRING_GENERATED_SUBRING := SessionLibrary.RingTheory.«CARRIER_SUBRING_GENERATED_SUBRING»
  CARRIER_SUBRING_OF := SessionLibrary.RingTheory.«CARRIER_SUBRING_OF»
  COND_ID := Session.COND_ID
  COND_RAND := Session.COND_RAND
  COND_RATOR := Session.COND_RATOR
  CONJ_ACI := Session.CONJ_ACI
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONJ_SYM := Session.CONJ_SYM
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  CROSS := Session.CROSS
  DELETE := Session.DELETE
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DISJOINT := Session.DISJOINT
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  EMPTY_UNION := Session.EMPTY_UNION
  EQ_IMP := Session.EQ_IMP
  EQ_SYM_EQ := Session.EQ_SYM_EQ
  ETA_AX := Session.ETA_AX
  ETA_ONE := Session.ETA_ONE
  EXISTS_FINITE_SUBSET_IMAGE := Session.EXISTS_FINITE_SUBSET_IMAGE
  EXISTS_IN_GSPEC := Session.EXISTS_IN_GSPEC
  EXISTS_IN_IMAGE := Session.EXISTS_IN_IMAGE
  EXISTS_IN_INSERT := Session.EXISTS_IN_INSERT
  EXISTS_IN_UNIONS := Session.EXISTS_IN_UNIONS
  EXISTS_PAIR_THM := Session.EXISTS_PAIR_THM
  EXISTS_SUBSET_UNION := Session.EXISTS_SUBSET_UNION
  EXP := Session.EXP
  EXTENSION := Session.EXTENSION
  FIELD_EQ_ALL_UNITS := SessionLibrary.RingTheory.«FIELD_EQ_ALL_UNITS»
  FIELD_HOMOMORPHISM_DIV := SessionLibrary.RingTheory.«FIELD_HOMOMORPHISM_DIV»
/-- The core theorems fieldtheory.ml uses. -/
def core10 : HolLibrary.FieldTheory.CoreThms10 where
/-- The core theorems fieldtheory.ml uses. -/
def core11 : HolLibrary.FieldTheory.CoreThms11 where
/-- The core theorems fieldtheory.ml uses. -/
def core12 : HolLibrary.FieldTheory.CoreThms12 where
/-- The core theorems fieldtheory.ml uses. -/
def core13 : HolLibrary.FieldTheory.CoreThms13 where
/-- The core theorems fieldtheory.ml uses. -/
def core14 : HolLibrary.FieldTheory.CoreThms14 where
/-- The core theorems fieldtheory.ml uses. -/
def core15 : HolLibrary.FieldTheory.CoreThms15 where
/-- The core theorems fieldtheory.ml uses. -/
def core16 : HolLibrary.FieldTheory.CoreThms16 where
/-- The core theorems fieldtheory.ml uses. -/
def core2 : HolLibrary.FieldTheory.CoreThms2 where
  FIELD_HOMOMORPHISM_INV := SessionLibrary.RingTheory.«FIELD_HOMOMORPHISM_INV»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_MUL_EQ_0 := SessionLibrary.RingTheory.«FIELD_MUL_EQ_0»
  FIELD_MUL_LINV := SessionLibrary.RingTheory.«FIELD_MUL_LINV»
  FIELD_MUL_RINV := SessionLibrary.RingTheory.«FIELD_MUL_RINV»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FIELD_POLY_RING := SessionLibrary.RingTheory.«FIELD_POLY_RING»
  FIELD_PRIME_SUBRING := SessionLibrary.RingTheory.«FIELD_PRIME_SUBRING»
  FIELD_QUOTIENT_RING := SessionLibrary.RingTheory.«FIELD_QUOTIENT_RING»
  FIELD_RING_HOMOMORPHISM_MONOMORPHISM := SessionLibrary.RingTheory.«FIELD_RING_HOMOMORPHISM_MONOMORPHISM»
  FIELD_UNIT := SessionLibrary.RingTheory.«FIELD_UNIT»
  FINITE_1 := Session.FINITE_1
  FINITE_CROSS_EQ := Session.FINITE_CROSS_EQ
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_DIFF := Session.FINITE_DIFF
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_HAS_SIZE := Session.FINITE_HAS_SIZE
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_IMAGE_INJ_EQ := Session.FINITE_IMAGE_INJ_EQ
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_INTEGRAL_DOMAIN_EQ_FIELD := SessionLibrary.RingTheory.«FINITE_INTEGRAL_DOMAIN_EQ_FIELD»
  FINITE_INTER := Session.FINITE_INTER
  FINITE_MONOMIAL_VARS_1 := SessionLibrary.RingTheory.«FINITE_MONOMIAL_VARS_1»
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_NUMSEG_LE := Session.FINITE_NUMSEG_LE
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_PRIME_SUBRING := SessionLibrary.RingTheory.«FINITE_PRIME_SUBRING»
  FINITE_PRODUCT_DEPENDENT := Session.FINITE_PRODUCT_DEPENDENT
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_SUBSET_NUMSEG := Session.FINITE_SUBSET_NUMSEG
  FINITE_UNION := Session.FINITE_UNION
  FINITE_UNIONS := Session.FINITE_UNIONS
  FIRST_RING_ISOMORPHISM_THEOREM := SessionLibrary.RingTheory.«FIRST_RING_ISOMORPHISM_THEOREM»
  FORALL_AND_THM := Session.FORALL_AND_THM
  FORALL_FINITE_SUBSET_IMAGE := Session.FORALL_FINITE_SUBSET_IMAGE
  FORALL_FUN_FROM_1 := SessionLibrary.RingTheory.«FORALL_FUN_FROM_1»
  FORALL_IN_CROSS := Session.FORALL_IN_CROSS
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FORALL_IN_UNION := Session.FORALL_IN_UNION
  FORALL_IN_UNIONS := Session.FORALL_IN_UNIONS
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FORALL_UNWIND_THM1 := Session.FORALL_UNWIND_THM1
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  FROBENIUS_FIXED := SessionLibrary.RingTheory.«FROBENIUS_FIXED»
  FST := Session.FST
  FUN_EQ_THM := Session.FUN_EQ_THM
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_FUNSPACE := Session.HAS_SIZE_FUNSPACE
  HAS_SIZE_IMAGE_INJ := Session.HAS_SIZE_IMAGE_INJ
  IDEAL_GENERATED_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_0»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_GENERATED_SING_EQ_CARRIER := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING_EQ_CARRIER»
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMAGE_EQ_EMPTY := Session.IMAGE_EQ_EMPTY
  IMAGE_I := Session.IMAGE_I
  IMAGE_ID := Session.IMAGE_ID
  IMAGE_POLY_EVAL := SessionLibrary.RingTheory.«IMAGE_POLY_EVAL»
  IMAGE_POLY_EXTEND := SessionLibrary.RingTheory.«IMAGE_POLY_EXTEND»
  IMAGE_POLY_EXTEND_1 := SessionLibrary.RingTheory.«IMAGE_POLY_EXTEND_1»
  IMAGE_SUBSET := Session.IMAGE_SUBSET
  IMAGE_UNION := Session.IMAGE_UNION
  IMAGE_UNIONS := Session.IMAGE_UNIONS
  IMAGE_o := Session.IMAGE_o
/-- The core theorems fieldtheory.ml uses. -/
def core3 : HolLibrary.FieldTheory.CoreThms3 where
  IMP_CONJ := Session.IMP_CONJ
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  IMP_IMP := Session.IMP_IMP
  INFINITE := Session.INFINITE
  INFINITE_CARD_LE := SessionLibrary.Card.«INFINITE_CARD_LE»
  INJECTIVE_ON_ALT := Session.INJECTIVE_ON_ALT
  INJECTIVE_ON_LEFT_INVERSE := Session.INJECTIVE_ON_LEFT_INVERSE
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTEGRAL_DOMAIN_CHAR := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_CHAR»
  INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING»
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_MUL_LCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_LCANCEL»
  INTEGRAL_DOMAIN_MUL_RCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_RCANCEL»
  INTEGRAL_DOMAIN_NONTRIVIAL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_NONTRIVIAL»
  INTEGRAL_DOMAIN_POLY_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_POLY_RING»
  INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE»
  INTEGRAL_DOMAIN_PRODUCT_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_PRODUCT_EQ_0»
  INTERS_2 := Session.INTERS_2
  INTERS_ANTIMONO := Session.INTERS_ANTIMONO
  INTERS_ANTIMONO_GEN := Session.INTERS_ANTIMONO_GEN
  INTERS_GSPEC := Session.INTERS_GSPEC
  INTER_SUBSET := Session.INTER_SUBSET
  IN_CROSS := Session.IN_CROSS
  IN_DELETE := Session.IN_DELETE
  IN_DIFF := Session.IN_DIFF
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_FLD := SessionLibrary.Wo.«IN_FLD»
  IN_IDEAL_GENERATED_SING := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SING»
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_INTER := Session.IN_INTER
  IN_INTERS := Session.IN_INTERS
  IN_NUMSEG := Session.IN_NUMSEG
  IN_POLY_RING_CARRIER := SessionLibrary.RingTheory.«IN_POLY_RING_CARRIER»
  IN_POLY_RING_SUBRING_GENERATED_FINITARY := SessionLibrary.RingTheory.«IN_POLY_RING_SUBRING_GENERATED_FINITARY»
  IN_RING_POLYNOMIAL_CARRIER_COMPOSE := SessionLibrary.RingTheory.«IN_RING_POLYNOMIAL_CARRIER_COMPOSE»
  IN_SING := Session.IN_SING
  IN_SUBRING_0 := SessionLibrary.RingTheory.«IN_SUBRING_0»
  IN_SUBRING_1 := SessionLibrary.RingTheory.«IN_SUBRING_1»
  IN_SUBRING_ADD := SessionLibrary.RingTheory.«IN_SUBRING_ADD»
  IN_SUBRING_GENERATED_FINITARY := SessionLibrary.RingTheory.«IN_SUBRING_GENERATED_FINITARY»
  IN_SUBRING_MUL := SessionLibrary.RingTheory.«IN_SUBRING_MUL»
  IN_SUBRING_NEG := SessionLibrary.RingTheory.«IN_SUBRING_NEG»
  IN_SUBRING_POW := SessionLibrary.RingTheory.«IN_SUBRING_POW»
  IN_SUBRING_PRODUCT := SessionLibrary.RingTheory.«IN_SUBRING_PRODUCT»
  IN_SUBRING_SUB := SessionLibrary.RingTheory.«IN_SUBRING_SUB»
  IN_SUBRING_SUM := SessionLibrary.RingTheory.«IN_SUBRING_SUM»
  IN_UNION := Session.IN_UNION
  IN_UNIONS := Session.IN_UNIONS
  IN_UNIV := Session.IN_UNIV
  ISOMORPHIC_RING_CARD_EQ := SessionLibrary.RingTheory.«ISOMORPHIC_RING_CARD_EQ»
  ISOMORPHIC_RING_FIELDNESS := SessionLibrary.RingTheory.«ISOMORPHIC_RING_FIELDNESS»
  ISOMORPHIC_SUBCOPY_OF_RING := SessionLibrary.RingTheory.«ISOMORPHIC_SUBCOPY_OF_RING»
  ISOMORPHIC_TRANSPORT_OF_RING := SessionLibrary.RingTheory.«ISOMORPHIC_TRANSPORT_OF_RING»
  I_DEF := Session.I_DEF
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LAMBDA_PAIR_THM := Session.LAMBDA_PAIR_THM
  LEFT_AND_EXISTS_THM := Session.LEFT_AND_EXISTS_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_0 := Session.LE_0
  LE_REFL := Session.LE_REFL
  LE_SUC_LT := Session.LE_SUC_LT
  LT := Session.LT
  LT_CASES := Session.LT_CASES
  MATROID_BASES_CARD_EQ := SessionLibrary.Matroids.«MATROID_BASES_CARD_EQ»
  MATROID_BASIS_EXISTS := SessionLibrary.Matroids.«MATROID_BASIS_EXISTS»
  MATROID_DIMENSION_GE_FINITE_CARD := SessionLibrary.Matroids.«MATROID_DIMENSION_GE_FINITE_CARD»
  MATROID_FINITE_DIMENSIONAL_ANY := SessionLibrary.Matroids.«MATROID_FINITE_DIMENSIONAL_ANY»
  MATROID_INDEPENDENT_CARD_LE_SPANNING := SessionLibrary.Matroids.«MATROID_INDEPENDENT_CARD_LE_SPANNING»
/-- The core theorems fieldtheory.ml uses. -/
def core4 : HolLibrary.FieldTheory.CoreThms4 where
  MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE := SessionLibrary.Matroids.«MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE»
  MATROID_INDEPENDENT_FINITARY := SessionLibrary.Matroids.«MATROID_INDEPENDENT_FINITARY»
  MATROID_INDEPENDENT_INSERT := SessionLibrary.Matroids.«MATROID_INDEPENDENT_INSERT»
  MATROID_INDEPENDENT_MONO := SessionLibrary.Matroids.«MATROID_INDEPENDENT_MONO»
  MATROID_MINIMALLY_DEPENDENT_SUBSET := SessionLibrary.Matroids.«MATROID_MINIMALLY_DEPENDENT_SUBSET»
  MATROID_SPANNING_ALT := SessionLibrary.Matroids.«MATROID_SPANNING_ALT»
  MATROID_SPANNING_CONTAINS_BASIS := SessionLibrary.Matroids.«MATROID_SPANNING_CONTAINS_BASIS»
  MATROID_SPAN_UNION_LEFT := SessionLibrary.Matroids.«MATROID_SPAN_UNION_LEFT»
  MAXIMAL_IDEAL_SING := SessionLibrary.RingTheory.«MAXIMAL_IDEAL_SING»
  MAXIMAL_IMP_PRIME_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PRIME_IDEAL»
  MAXIMAL_IMP_RING_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_RING_IDEAL»
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONOMIAL_DEG_LE_POLY_DEG := SessionLibrary.RingTheory.«MONOMIAL_DEG_LE_POLY_DEG»
  MONOMIAL_DEG_UNIVARIATE := SessionLibrary.RingTheory.«MONOMIAL_DEG_UNIVARIATE»
  MONOMIAL_VARS_UNIVARIATE := SessionLibrary.RingTheory.«MONOMIAL_VARS_UNIVARIATE»
  MONO_AND := Session.MONO_AND
  MONO_EXISTS := Session.MONO_EXISTS
  MONO_FORALL := Session.MONO_FORALL
  MONO_OR := Session.MONO_OR
  MUL_C_UNIV := SessionLibrary.Card.«MUL_C_UNIV»
  NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS := SessionLibrary.RingTheory.«NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS»
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_INSERT_EMPTY := Session.NOT_INSERT_EMPTY
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LE := Session.NOT_LE
  NOT_LT := Session.NOT_LT
  NUMSEG_CLAUSES_LT := Session.NUMSEG_CLAUSES_LT
  PAIR_EQ := Session.PAIR_EQ
  PID := SessionLibrary.RingTheory.«PID»
  PID_IMP_BEZOUT_RING := SessionLibrary.RingTheory.«PID_IMP_BEZOUT_RING»
  PID_IMP_UFD := SessionLibrary.RingTheory.«PID_IMP_UFD»
  PID_MAXIMAL_EQ_PRIME_IDEAL := SessionLibrary.RingTheory.«PID_MAXIMAL_EQ_PRIME_IDEAL»
  PID_POLY_RING := SessionLibrary.RingTheory.«PID_POLY_RING»
  POLY_0 := SessionLibrary.RingTheory.«POLY_0»
  POLY_CLAUSES := SessionLibrary.RingTheory.«POLY_CLAUSES»
  POLY_COMPOSE_HOMOMORPHISM_CONST := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_CONST»
  POLY_COMPOSE_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_MUL»
  POLY_COMPOSE_HOMOMORPHISM_SUB := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_SUB»
  POLY_COMPOSE_HOMOMORPHISM_VAR := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_VAR»
  POLY_CONST := SessionLibrary.RingTheory.«POLY_CONST»
  POLY_CONST_0 := SessionLibrary.RingTheory.«POLY_CONST_0»
  POLY_CONST_1 := SessionLibrary.RingTheory.«POLY_CONST_1»
  POLY_CONST_EQ := SessionLibrary.RingTheory.«POLY_CONST_EQ»
  POLY_CONST_EQ_0 := SessionLibrary.RingTheory.«POLY_CONST_EQ_0»
  POLY_CONST_SUBRING_GENERATED := SessionLibrary.RingTheory.«POLY_CONST_SUBRING_GENERATED»
  POLY_DEG_0 := SessionLibrary.RingTheory.«POLY_DEG_0»
  POLY_DEG_1 := SessionLibrary.RingTheory.«POLY_DEG_1»
  POLY_DEG_1_IMP_IRREDUCIBLE := SessionLibrary.RingTheory.«POLY_DEG_1_IMP_IRREDUCIBLE»
  POLY_DEG_1_ROOT := SessionLibrary.RingTheory.«POLY_DEG_1_ROOT»
  POLY_DEG_ADD := SessionLibrary.RingTheory.«POLY_DEG_ADD»
  POLY_DEG_CONST := SessionLibrary.RingTheory.«POLY_DEG_CONST»
  POLY_DEG_EQ_0 := SessionLibrary.RingTheory.«POLY_DEG_EQ_0»
  POLY_DEG_GE_EQ := SessionLibrary.RingTheory.«POLY_DEG_GE_EQ»
  POLY_DEG_LE_EQ := SessionLibrary.RingTheory.«POLY_DEG_LE_EQ»
  POLY_DEG_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_DEG_MONOMORPHIC_IMAGE»
  POLY_DEG_MUL_X_MINUS_A := SessionLibrary.RingTheory.«POLY_DEG_MUL_X_MINUS_A»
  POLY_DEG_UNIT := SessionLibrary.RingTheory.«POLY_DEG_UNIT»
  POLY_DEG_X_MINUS_A := SessionLibrary.RingTheory.«POLY_DEG_X_MINUS_A»
  POLY_DIVIDES_X_MINUS_ROOT := SessionLibrary.RingTheory.«POLY_DIVIDES_X_MINUS_ROOT»
  POLY_DIVISION := SessionLibrary.RingTheory.«POLY_DIVISION»
  POLY_EQ_0_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_EQ_0_MONOMORPHIC_IMAGE»
  POLY_EVAL := SessionLibrary.RingTheory.«POLY_EVAL»
  POLY_EVAL_0 := SessionLibrary.RingTheory.«POLY_EVAL_0»
  POLY_EVAL_1 := SessionLibrary.RingTheory.«POLY_EVAL_1»
  POLY_EVAL_ADD := SessionLibrary.RingTheory.«POLY_EVAL_ADD»
  POLY_EVAL_CONST := SessionLibrary.RingTheory.«POLY_EVAL_CONST»
  POLY_EVAL_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_EVAL_HOMOMORPHIC_IMAGE»
  POLY_EVAL_MUL := SessionLibrary.RingTheory.«POLY_EVAL_MUL»
/-- The core theorems fieldtheory.ml uses. -/
def core5 : HolLibrary.FieldTheory.CoreThms5 where
  POLY_EVAL_RING_PRODUCT := SessionLibrary.RingTheory.«POLY_EVAL_RING_PRODUCT»
  POLY_EVAL_SUB := SessionLibrary.RingTheory.«POLY_EVAL_SUB»
  POLY_EVAL_VAR := SessionLibrary.RingTheory.«POLY_EVAL_VAR»
  POLY_EXTEND := SessionLibrary.RingTheory.«POLY_EXTEND»
  POLY_EXTEND_1 := SessionLibrary.RingTheory.«POLY_EXTEND_1»
  POLY_EXTEND_ADD := SessionLibrary.RingTheory.«POLY_EXTEND_ADD»
  POLY_EXTEND_CONST := SessionLibrary.RingTheory.«POLY_EXTEND_CONST»
  POLY_EXTEND_EQ := SessionLibrary.RingTheory.«POLY_EXTEND_EQ»
  POLY_EXTEND_EVALUATE := SessionLibrary.RingTheory.«POLY_EXTEND_EVALUATE»
  POLY_EXTEND_EXTEND := SessionLibrary.RingTheory.«POLY_EXTEND_EXTEND»
  POLY_EXTEND_FROM_SUBRING_GENERATED := SessionLibrary.RingTheory.«POLY_EXTEND_FROM_SUBRING_GENERATED»
  POLY_EXTEND_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_EXTEND_HOMOMORPHIC_IMAGE»
  POLY_EXTEND_ID := SessionLibrary.RingTheory.«POLY_EXTEND_ID»
  POLY_EXTEND_INTO_SUBRING_GENERATED := SessionLibrary.RingTheory.«POLY_EXTEND_INTO_SUBRING_GENERATED»
  POLY_EXTEND_MUL := SessionLibrary.RingTheory.«POLY_EXTEND_MUL»
  POLY_EXTEND_REINDEX := SessionLibrary.RingTheory.«POLY_EXTEND_REINDEX»
  POLY_EXTEND_SUB := SessionLibrary.RingTheory.«POLY_EXTEND_SUB»
  POLY_EXTEND_UNIVARIATE := SessionLibrary.RingTheory.«POLY_EXTEND_UNIVARIATE»
  POLY_EXTEND_VAR := SessionLibrary.RingTheory.«POLY_EXTEND_VAR»
  POLY_MONOMIAL_IN_CARRIER := SessionLibrary.RingTheory.«POLY_MONOMIAL_IN_CARRIER»
  POLY_MUL_0 := SessionLibrary.RingTheory.«POLY_MUL_0»
  POLY_MUL_CONST := SessionLibrary.RingTheory.«POLY_MUL_CONST»
  POLY_MUL_RID := SessionLibrary.RingTheory.«POLY_MUL_RID»
  POLY_RING := SessionLibrary.RingTheory.«POLY_RING»
  POLY_RING_CLAUSES := SessionLibrary.RingTheory.«POLY_RING_CLAUSES»
  POLY_RING_IN_FINITE_VARIABLES := SessionLibrary.RingTheory.«POLY_RING_IN_FINITE_VARIABLES»
  POLY_RING_MONO := SessionLibrary.RingTheory.«POLY_RING_MONO»
  POLY_ROOT_BOUND := SessionLibrary.RingTheory.«POLY_ROOT_BOUND»
  POLY_ROOT_COUNT_IMP_SQUAREFREE := SessionLibrary.RingTheory.«POLY_ROOT_COUNT_IMP_SQUAREFREE»
  POLY_SUBRING_GENERATED_1 := SessionLibrary.RingTheory.«POLY_SUBRING_GENERATED_1»
  POLY_SUBRING_GENERATED_CLAUSES := SessionLibrary.RingTheory.«POLY_SUBRING_GENERATED_CLAUSES»
  POLY_VAR_EQ_CONST := SessionLibrary.RingTheory.«POLY_VAR_EQ_CONST»
  POLY_VAR_UNIV := SessionLibrary.RingTheory.«POLY_VAR_UNIV»
  POLY_X_MINUS_A_IN_CARRIER := SessionLibrary.RingTheory.«POLY_X_MINUS_A_IN_CARRIER»
  POLY_X_MINUS_A_NONZERO := SessionLibrary.RingTheory.«POLY_X_MINUS_A_NONZERO»
  PRIME_SUBRING := SessionLibrary.RingTheory.«PRIME_SUBRING»
  PSUBSET := Session.PSUBSET
  PSUBSET_ALT := Session.PSUBSET_ALT
  PSUBSET_TRANS := Session.PSUBSET_TRANS
  QOSET_FLD := SessionLibrary.Wo.«QOSET_FLD»
  QOSET_RESTRICT := SessionLibrary.Wo.«QOSET_RESTRICT»
  QUOTIENT_RING := SessionLibrary.RingTheory.«QUOTIENT_RING»
  QUOTIENT_RING_0 := SessionLibrary.RingTheory.«QUOTIENT_RING_0»
  RESTRICTION := Session.RESTRICTION
  RIGHT_AND_EXISTS_THM := Session.RIGHT_AND_EXISTS_THM
  RIGHT_AND_FORALL_THM := Session.RIGHT_AND_FORALL_THM
  RIGHT_EXISTS_AND_THM := Session.RIGHT_EXISTS_AND_THM
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_IMP_FORALL_THM := Session.RIGHT_IMP_FORALL_THM
  RINGS_EQ := SessionLibrary.RingTheory.«RINGS_EQ»
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_0_IN_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_0_IN_SUBRING_GENERATED»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_1_IN_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_1_IN_SUBRING_GENERATED»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_ASSOC := SessionLibrary.RingTheory.«RING_ADD_ASSOC»
  RING_ADD_IN_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_ADD_IN_SUBRING_GENERATED»
  RING_ADD_LDISTRIB := SessionLibrary.RingTheory.«RING_ADD_LDISTRIB»
  RING_ADD_LNEG := SessionLibrary.RingTheory.«RING_ADD_LNEG»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RNEG := SessionLibrary.RingTheory.«RING_ADD_RNEG»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_ADD_SYM := SessionLibrary.RingTheory.«RING_ADD_SYM»
  RING_CARRIER_NONEMPTY := SessionLibrary.RingTheory.«RING_CARRIER_NONEMPTY»
  RING_CARRIER_POLY_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_CARRIER_POLY_SUBRING_GENERATED»
  RING_CARRIER_POLY_SUBRING_GENERATED_MONO := SessionLibrary.RingTheory.«RING_CARRIER_POLY_SUBRING_GENERATED_MONO»
  RING_CARRIER_SUBRING_GENERATED_0 := SessionLibrary.RingTheory.«RING_CARRIER_SUBRING_GENERATED_0»
  RING_CARRIER_SUBRING_GENERATED_SUBSET := SessionLibrary.RingTheory.«RING_CARRIER_SUBRING_GENERATED_SUBSET»
  RING_CHAR_FINITE := SessionLibrary.RingTheory.«RING_CHAR_FINITE»
  RING_CHAR_UNIQUE := SessionLibrary.RingTheory.«RING_CHAR_UNIQUE»
/-- The core theorems fieldtheory.ml uses. -/
def core6 : HolLibrary.FieldTheory.CoreThms6 where
  RING_COPRIME_00 := SessionLibrary.RingTheory.«RING_COPRIME_00»
  RING_COPRIME_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_COPRIME_HOMOMORPHIC_IMAGE»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_COSET_EQ_IDEAL := SessionLibrary.RingTheory.«RING_COSET_EQ_IDEAL»
  RING_DIRECT_LIMIT := SessionLibrary.RingTheory.«RING_DIRECT_LIMIT»
  RING_DIV := SessionLibrary.RingTheory.«RING_DIV»
  RING_DIVIDES_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_DIVIDES_HOMOMORPHIC_IMAGE»
  RING_DIVIDES_LMUL := SessionLibrary.RingTheory.«RING_DIVIDES_LMUL»
  RING_DIVIDES_LMUL2 := SessionLibrary.RingTheory.«RING_DIVIDES_LMUL2»
  RING_DIVIDES_REFL := SessionLibrary.RingTheory.«RING_DIVIDES_REFL»
  RING_DIVIDES_RMUL := SessionLibrary.RingTheory.«RING_DIVIDES_RMUL»
  RING_DIVIDES_ZERO := SessionLibrary.RingTheory.«RING_DIVIDES_ZERO»
  RING_DIV_1 := SessionLibrary.RingTheory.«RING_DIV_1»
  RING_EPIMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_EPIMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_BETWEEN_SUBRINGS := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_BETWEEN_SUBRINGS»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_EPIMORPHISM_FACTOR := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_EPIMORPHISM_FACTOR»
  RING_HOMOMORPHISM_EQ := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_EQ»
  RING_HOMOMORPHISM_ID := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ID»
  RING_HOMOMORPHISM_IMAGE_PREIMAGE_EQ := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IMAGE_PREIMAGE_EQ»
  RING_HOMOMORPHISM_INCLUSION := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INCLUSION»
  RING_HOMOMORPHISM_INTO_SUBRING := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTO_SUBRING»
  RING_HOMOMORPHISM_INTO_SUBRING_EQ_GEN := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTO_SUBRING_EQ_GEN»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_NEG := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_NEG»
  RING_HOMOMORPHISM_POLY_CONST := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_CONST»
  RING_HOMOMORPHISM_POLY_EVAL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_EVAL»
  RING_HOMOMORPHISM_POLY_EXTEND := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_EXTEND»
  RING_HOMOMORPHISM_POLY_RINGS := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_RINGS»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_SUB := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUB»
  RING_HOMOMORPHISM_SUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM»
  RING_IDEAL_RING_KERNEL := SessionLibrary.RingTheory.«RING_IDEAL_RING_KERNEL»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_INV_0 := SessionLibrary.RingTheory.«RING_INV_0»
  RING_INV_MUL := SessionLibrary.RingTheory.«RING_INV_MUL»
  RING_IRREDUCIBLE_IN_CARRIER := SessionLibrary.RingTheory.«RING_IRREDUCIBLE_IN_CARRIER»
  RING_ISOMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISM»
  RING_ISOMORPHISMS_ISOMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISMS_ISOMORPHISM»
  RING_ISOMORPHISMS_POLY_POLY_RING := SessionLibrary.RingTheory.«RING_ISOMORPHISMS_POLY_POLY_RING»
  RING_ISOMORPHISMS_POLY_REINDEX := SessionLibrary.RingTheory.«RING_ISOMORPHISMS_POLY_REINDEX»
  RING_ISOMORPHISM_I := SessionLibrary.RingTheory.«RING_ISOMORPHISM_I»
  RING_ISOMORPHISM_IMP_EPIMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISM_IMP_EPIMORPHISM»
  RING_ISOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISM_IMP_HOMOMORPHISM»
  RING_ISOMORPHISM_IMP_ISOMORPHIC := SessionLibrary.RingTheory.«RING_ISOMORPHISM_IMP_ISOMORPHIC»
  RING_ISOMORPHISM_IMP_MONOMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISM_IMP_MONOMORPHISM»
  RING_ISOMORPHISM_MONOMORPHISM_ALT := SessionLibrary.RingTheory.«RING_ISOMORPHISM_MONOMORPHISM_ALT»
  RING_ISOMORPHISM_ONTO_IMAGE := SessionLibrary.RingTheory.«RING_ISOMORPHISM_ONTO_IMAGE»
  RING_ISOMORPHISM_POLY_RING_TRIVIAL := SessionLibrary.RingTheory.«RING_ISOMORPHISM_POLY_RING_TRIVIAL»
  RING_KERNEL_0 := SessionLibrary.RingTheory.«RING_KERNEL_0»
  RING_KERNEL_TO_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_KERNEL_TO_SUBRING_GENERATED»
  RING_LINV_UNIQUE := SessionLibrary.RingTheory.«RING_LINV_UNIQUE»
  RING_MONOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM»
  RING_MONOMORPHISM_ALT := SessionLibrary.RingTheory.«RING_MONOMORPHISM_ALT»
  RING_MONOMORPHISM_ALT_EQ := SessionLibrary.RingTheory.«RING_MONOMORPHISM_ALT_EQ»
  RING_MONOMORPHISM_BETWEEN_SUBRINGS := SessionLibrary.RingTheory.«RING_MONOMORPHISM_BETWEEN_SUBRINGS»
  RING_MONOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_MONOMORPHISM_COMPOSE»
  RING_MONOMORPHISM_EQ := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EQ»
  RING_MONOMORPHISM_EQ_0 := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EQ_0»
  RING_MONOMORPHISM_FROBENIUS := SessionLibrary.RingTheory.«RING_MONOMORPHISM_FROBENIUS»
  RING_MONOMORPHISM_FROM_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_MONOMORPHISM_FROM_SUBRING_GENERATED»
  RING_MONOMORPHISM_I := SessionLibrary.RingTheory.«RING_MONOMORPHISM_I»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_INCLUSION := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INCLUSION»
  RING_MONOMORPHISM_INTO_SUBRING := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INTO_SUBRING»
  RING_MONOMORPHISM_POLY_RINGS := SessionLibrary.RingTheory.«RING_MONOMORPHISM_POLY_RINGS»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
/-- The core theorems fieldtheory.ml uses. -/
def core7 : HolLibrary.FieldTheory.CoreThms7 where
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_IN_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_MUL_IN_SUBRING_GENERATED»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LNEG := SessionLibrary.RingTheory.«RING_MUL_LNEG»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RINV := SessionLibrary.RingTheory.«RING_MUL_RINV»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_NEG_EQ_0 := SessionLibrary.RingTheory.«RING_NEG_EQ_0»
  RING_NEG_IN_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_NEG_IN_SUBRING_GENERATED»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_POLYNOMIAL := SessionLibrary.RingTheory.«RING_POLYNOMIAL»
  RING_POLYNOMIAL_1 := SessionLibrary.RingTheory.«RING_POLYNOMIAL_1»
  RING_POLYNOMIAL_ADD := SessionLibrary.RingTheory.«RING_POLYNOMIAL_ADD»
  RING_POLYNOMIAL_COMPOSE := SessionLibrary.RingTheory.«RING_POLYNOMIAL_COMPOSE»
  RING_POLYNOMIAL_CONST := SessionLibrary.RingTheory.«RING_POLYNOMIAL_CONST»
  RING_POLYNOMIAL_IMP_POWERSERIES := SessionLibrary.RingTheory.«RING_POLYNOMIAL_IMP_POWERSERIES»
  RING_POLYNOMIAL_MUL := SessionLibrary.RingTheory.«RING_POLYNOMIAL_MUL»
  RING_POLYNOMIAL_SUB := SessionLibrary.RingTheory.«RING_POLYNOMIAL_SUB»
  RING_POLYNOMIAL_VAR := SessionLibrary.RingTheory.«RING_POLYNOMIAL_VAR»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POWERSERIES_CONST := SessionLibrary.RingTheory.«RING_POWERSERIES_CONST»
  RING_POWERSERIES_SUB := SessionLibrary.RingTheory.«RING_POWERSERIES_SUB»
  RING_POWERSERIES_VAR := SessionLibrary.RingTheory.«RING_POWERSERIES_VAR»
  RING_POW_2 := SessionLibrary.RingTheory.«RING_POW_2»
  RING_POW_IN_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_POW_IN_SUBRING_GENERATED»
  RING_POW_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_POW_SUBRING_GENERATED»
  RING_PRODUCT := SessionLibrary.RingTheory.«RING_PRODUCT»
  RING_PRODUCT_CLAUSES := SessionLibrary.RingTheory.«RING_PRODUCT_CLAUSES»
  RING_PRODUCT_CLAUSES_NUMSEG := SessionLibrary.RingTheory.«RING_PRODUCT_CLAUSES_NUMSEG»
  RING_PRODUCT_CLAUSES_NUMSEG_ALT := SessionLibrary.RingTheory.«RING_PRODUCT_CLAUSES_NUMSEG_ALT»
  RING_PRODUCT_EQ := SessionLibrary.RingTheory.«RING_PRODUCT_EQ»
  RING_RINV_UNIQUE := SessionLibrary.RingTheory.«RING_RINV_UNIQUE»
  RING_SQUAREFREE_IMP_NONZERO := SessionLibrary.RingTheory.«RING_SQUAREFREE_IMP_NONZERO»
  RING_SQUAREFREE_IN_CARRIER := SessionLibrary.RingTheory.«RING_SQUAREFREE_IN_CARRIER»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_RDISTRIB := SessionLibrary.RingTheory.«RING_SUB_RDISTRIB»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_SUB_RZERO := SessionLibrary.RingTheory.«RING_SUB_RZERO»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_CASES := SessionLibrary.RingTheory.«RING_SUM_CASES»
  RING_SUM_CLAUSES := SessionLibrary.RingTheory.«RING_SUM_CLAUSES»
  RING_SUM_CLOSED := SessionLibrary.RingTheory.«RING_SUM_CLOSED»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_EQ_0 := SessionLibrary.RingTheory.«RING_SUM_EQ_0»
  RING_SUM_IMAGE := SessionLibrary.RingTheory.«RING_SUM_IMAGE»
  RING_SUM_LMUL := SessionLibrary.RingTheory.«RING_SUM_LMUL»
  RING_SUM_RESTRICT_SET := SessionLibrary.RingTheory.«RING_SUM_RESTRICT_SET»
  RING_SUM_RMUL := SessionLibrary.RingTheory.«RING_SUM_RMUL»
  RING_SUM_SING := SessionLibrary.RingTheory.«RING_SUM_SING»
  RING_SUM_SUB := SessionLibrary.RingTheory.«RING_SUM_SUB»
  RING_SUM_SUM_PRODUCT := SessionLibrary.RingTheory.«RING_SUM_SUM_PRODUCT»
  RING_SUM_SUPERSET := SessionLibrary.RingTheory.«RING_SUM_SUPERSET»
  RING_UNIT_0 := SessionLibrary.RingTheory.«RING_UNIT_0»
  RING_UNIT_NOT_IN_PRIME_IDEAL := SessionLibrary.RingTheory.«RING_UNIT_NOT_IN_PRIME_IDEAL»
  RING_UNIT_POLY_CONST := SessionLibrary.RingTheory.«RING_UNIT_POLY_CONST»
  RING_UNIT_POLY_DOMAIN := SessionLibrary.RingTheory.«RING_UNIT_POLY_DOMAIN»
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SIMPLE_IMAGE := Session.SIMPLE_IMAGE
  SIMPLE_IMAGE_GEN := Session.SIMPLE_IMAGE_GEN
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SND := Session.SND
  SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_GENERATED»
  SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE»
  SUBRING_GENERATED_BY_SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_GENERATED_BY_SUBRING_GENERATED»
  SUBRING_GENERATED_EQ := SessionLibrary.RingTheory.«SUBRING_GENERATED_EQ»
/-- The core theorems fieldtheory.ml uses. -/
def core8 : HolLibrary.FieldTheory.CoreThms8 where
  SUBRING_GENERATED_IDEMPOT := SessionLibrary.RingTheory.«SUBRING_GENERATED_IDEMPOT»
  SUBRING_GENERATED_INC := SessionLibrary.RingTheory.«SUBRING_GENERATED_INC»
  SUBRING_GENERATED_INC_GEN := SessionLibrary.RingTheory.«SUBRING_GENERATED_INC_GEN»
  SUBRING_GENERATED_MINIMAL := SessionLibrary.RingTheory.«SUBRING_GENERATED_MINIMAL»
  SUBRING_GENERATED_MONO := SessionLibrary.RingTheory.«SUBRING_GENERATED_MONO»
  SUBRING_GENERATED_RESTRICT := SessionLibrary.RingTheory.«SUBRING_GENERATED_RESTRICT»
  SUBRING_GENERATED_RING_CARRIER := SessionLibrary.RingTheory.«SUBRING_GENERATED_RING_CARRIER»
  SUBRING_GENERATED_SUBSET_CARRIER := SessionLibrary.RingTheory.«SUBRING_GENERATED_SUBSET_CARRIER»
  SUBRING_GENERATED_SUBSET_CARRIER_SUBSET := SessionLibrary.RingTheory.«SUBRING_GENERATED_SUBSET_CARRIER_SUBSET»
  SUBRING_GENERATED_UNION_LEFT := SessionLibrary.RingTheory.«SUBRING_GENERATED_UNION_LEFT»
  SUBRING_GENERATED_UNION_RIGHT := SessionLibrary.RingTheory.«SUBRING_GENERATED_UNION_RIGHT»
  SUBRING_OF_HOMOMORPHIC_EQUALITIES := SessionLibrary.RingTheory.«SUBRING_OF_HOMOMORPHIC_EQUALITIES»
  SUBRING_OF_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«SUBRING_OF_HOMOMORPHIC_IMAGE»
  SUBRING_OF_HOMOMORPHIC_PREIMAGE := SessionLibrary.RingTheory.«SUBRING_OF_HOMOMORPHIC_PREIMAGE»
  SUBRING_OF_IMP_SUBSET := SessionLibrary.RingTheory.«SUBRING_OF_IMP_SUBSET»
  SUBRING_OF_INTER := SessionLibrary.RingTheory.«SUBRING_OF_INTER»
  SUBRING_OF_INTERS := SessionLibrary.RingTheory.«SUBRING_OF_INTERS»
  SUBRING_OF_UNIONS := SessionLibrary.RingTheory.«SUBRING_OF_UNIONS»
  SUBRING_SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_SUBRING_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_ANTISYM_EQ := Session.SUBSET_ANTISYM_EQ
  SUBSET_INTER := Session.SUBSET_INTER
  SUBSET_REFL := Session.SUBSET_REFL
  SUBSET_RESTRICT := Session.SUBSET_RESTRICT
  SUBSET_TRANS := Session.SUBSET_TRANS
  SUBSET_UNION := Session.SUBSET_UNION
  SUBSET_UNIV := Session.SUBSET_UNIV
  SURJECTIVE_IFF_INJECTIVE := Session.SURJECTIVE_IFF_INJECTIVE
  SWAP_EXISTS_THM := Session.SWAP_EXISTS_THM
  SWAP_FORALL_THM := Session.SWAP_FORALL_THM
  TRANSITIVE_STEPWISE_LT := Session.TRANSITIVE_STEPWISE_LT
  TRIVIAL_POLY_RING := SessionLibrary.RingTheory.«TRIVIAL_POLY_RING»
  TRIVIAL_RING_10 := SessionLibrary.RingTheory.«TRIVIAL_RING_10»
  TRIVIAL_RING_HAS_SIZE_1 := SessionLibrary.RingTheory.«TRIVIAL_RING_HAS_SIZE_1»
  TRIVIAL_RING_MONOMORPHIC_IMAGE_EQ := SessionLibrary.RingTheory.«TRIVIAL_RING_MONOMORPHIC_IMAGE_EQ»
  TRIVIAL_RING_SUBRING_GENERATED := SessionLibrary.RingTheory.«TRIVIAL_RING_SUBRING_GENERATED»
  UFD_PRIME_FACTOR_EXISTS := SessionLibrary.RingTheory.«UFD_PRIME_FACTOR_EXISTS»
  UNIONS_GSPEC := Session.UNIONS_GSPEC
  UNIONS_SUBSET := Session.UNIONS_SUBSET
  UNION_ASSOC := Session.UNION_ASSOC
  UNION_COMM := Session.UNION_COMM
  UNION_EMPTY := Session.UNION_EMPTY
  UNION_OVER_INTER := Session.UNION_OVER_INTER
  UNION_SUBSET := Session.UNION_SUBSET
  UNIV_1 := Session.UNIV_1
  UNIV_NOT_EMPTY := Session.UNIV_NOT_EMPTY
  WF_REC := Session.WF_REC
  WF_num := Session.WF_num
  WLOG_LT := Session.WLOG_LT
  ZL_STRONG := SessionLibrary.Wo.«ZL_STRONG»
  ZL_SUBSETS_UNIONS_NONEMPTY := SessionLibrary.Wo.«ZL_SUBSETS_UNIONS_NONEMPTY»
  chain := SessionLibrary.Wo.«chain»
  coeff := SessionLibrary.RingTheory.«coeff»
  field := SessionLibrary.RingTheory.«field»
  integral_domain := SessionLibrary.RingTheory.«integral_domain»
  isomorphic_ring := SessionLibrary.RingTheory.«isomorphic_ring»
  le_c := Session.le_c
  matroid_basis := SessionLibrary.Matroids.«matroid_basis»
  matroid_dependent := SessionLibrary.Matroids.«matroid_dependent»
  matroid_finite_dimensional := SessionLibrary.Matroids.«matroid_finite_dimensional»
  matroid_independent := SessionLibrary.Matroids.«matroid_independent»
  matroid_set := SessionLibrary.Matroids.«matroid_set»
  matroid_span := SessionLibrary.Matroids.«matroid_span»
  matroid_spanning := SessionLibrary.Matroids.«matroid_spanning»
  matroid_tybij := SessionLibrary.Matroids.«matroid_tybij»
  mul_c := SessionLibrary.Card.«mul_c»
  num_INDUCTION := Session.num_INDUCTION
  num_INFINITE := Session.num_INFINITE
  num_WF := Session.num_WF
/-- The core theorems fieldtheory.ml uses. -/
def core9 : HolLibrary.FieldTheory.CoreThms9 where
  num_WOP := Session.num_WOP
  o_ASSOC := Session.o_ASSOC
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM
  one := Session.one
  poly_0 := SessionLibrary.RingTheory.«poly_0»
  poly_const := SessionLibrary.RingTheory.«poly_const»
  poly_eval := SessionLibrary.RingTheory.«poly_eval»
  poly_evaluate := SessionLibrary.RingTheory.«poly_evaluate»
  poly_vars := SessionLibrary.RingTheory.«poly_vars»
  prime_ideal := SessionLibrary.RingTheory.«prime_ideal»
  principal_ideal := SessionLibrary.RingTheory.«principal_ideal»
  proper_ideal := SessionLibrary.RingTheory.«proper_ideal»
  qoset := SessionLibrary.Wo.«qoset»
  ring_0 := SessionLibrary.RingTheory.«ring_0»
  ring_1 := SessionLibrary.RingTheory.«ring_1»
  ring_add := SessionLibrary.RingTheory.«ring_add»
  ring_automorphism := SessionLibrary.RingTheory.«ring_automorphism»
  ring_carrier := SessionLibrary.RingTheory.«ring_carrier»
  ring_div := SessionLibrary.RingTheory.«ring_div»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_endomorphism := SessionLibrary.RingTheory.«ring_endomorphism»
  ring_epimorphism := SessionLibrary.RingTheory.«ring_epimorphism»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_image := SessionLibrary.RingTheory.«ring_image»
  ring_irreducible := SessionLibrary.RingTheory.«ring_irreducible»
  ring_isomorphism := SessionLibrary.RingTheory.«ring_isomorphism»
  ring_isomorphisms := SessionLibrary.RingTheory.«ring_isomorphisms»
  ring_kernel := SessionLibrary.RingTheory.«ring_kernel»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  ring_mul := SessionLibrary.RingTheory.«ring_mul»
  ring_neg := SessionLibrary.RingTheory.«ring_neg»
  ring_of_int := SessionLibrary.RingTheory.«ring_of_int»
  ring_of_num := SessionLibrary.RingTheory.«ring_of_num»
  ring_polynomial := SessionLibrary.RingTheory.«ring_polynomial»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_powerseries := SessionLibrary.RingTheory.«ring_powerseries»
  ring_prime := SessionLibrary.RingTheory.«ring_prime»
  ring_squarefree := SessionLibrary.RingTheory.«ring_squarefree»
  ring_sub := SessionLibrary.RingTheory.«ring_sub»
  ring_tybij := SessionLibrary.RingTheory.«ring_tybij»
  ring_unit := SessionLibrary.RingTheory.«ring_unit»
  subring_of := SessionLibrary.RingTheory.«subring_of»
  trivial_ring := SessionLibrary.RingTheory.«trivial_ring»

/-- What fieldtheory.ml uses from Session. -/
def deps : HolLibrary.FieldTheory.FieldTheoryDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  parse_as_infix := Session.parse_as_infix
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  ASM_METIS_TAC := Session.ASM_METIS_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  RING_TAC := SessionLibrary.RingTheory.RING_TAC
  FIELD_TAC := SessionLibrary.RingTheory.FIELD_TAC
  new_inductive_set := Session.new_inductive_set
  RING_RULE t := ExceptT.mk (SessionLibrary.RingTheory.RING_RULE t)
  basic_ss := Session.basic_ss
  TAUT t := ExceptT.mk (Session.TAUT t)
  core1 := core1
  core2 := core2
  core3 := core3
  core4 := core4
  core5 := core5
  core6 := core6
  core7 := core7
  core8 := core8
  core9 := core9
  core10 := core10
  core11 := core11
  core12 := core12
  core13 := core13
  core14 := core14
  core15 := core15
  core16 := core16

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} (name : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in fieldtheory.ml order. -/

initialize BSubfields : HolLibrary.FieldTheory.Subfields ←
  ioB "setupSubfields" <|
    (HolLibrary.FieldTheory.setupSubfields deps).run

initialize BSubfieldGenerated : HolLibrary.FieldTheory.SubfieldGenerated ←
  ioB "setupSubfieldGenerated" <|
    (HolLibrary.FieldTheory.setupSubfieldGenerated deps BSubfields).run

initialize BSubfieldGenerated1 : HolLibrary.FieldTheory.SubfieldGenerated1 ←
  ioB "setupSubfieldGenerated1" <|
    (HolLibrary.FieldTheory.setupSubfieldGenerated1 deps BSubfields BSubfieldGenerated).run

initialize BSubfieldGenerated2 : HolLibrary.FieldTheory.SubfieldGenerated2 ←
  ioB "setupSubfieldGenerated2" <|
    (HolLibrary.FieldTheory.setupSubfieldGenerated2 deps BSubfields BSubfieldGenerated BSubfieldGenerated1).run

initialize BSubfieldQuotients : HolLibrary.FieldTheory.SubfieldQuotients ←
  ioB "setupSubfieldQuotients" <|
    (HolLibrary.FieldTheory.setupSubfieldQuotients deps BSubfields BSubfieldGenerated BSubfieldGenerated1 BSubfieldGenerated2).run

initialize BFieldExtension : HolLibrary.FieldTheory.FieldExtension ←
  ioB "setupFieldExtension" <|
    (HolLibrary.FieldTheory.setupFieldExtension deps BSubfields BSubfieldGenerated).run

initialize BRingSpan : HolLibrary.FieldTheory.RingSpan ←
  ioB "setupRingSpan" <|
    (HolLibrary.FieldTheory.setupRingSpan deps).run

initialize BRingMatroid : HolLibrary.FieldTheory.RingMatroid ←
  ioB "setupRingMatroid" <|
    (HolLibrary.FieldTheory.setupRingMatroid deps BRingSpan).run

initialize BLinearAlgebra : HolLibrary.FieldTheory.LinearAlgebra ←
  ioB "setupLinearAlgebra" <|
    (HolLibrary.FieldTheory.setupLinearAlgebra deps BFieldExtension BRingSpan BRingMatroid).run

initialize BFinitary : HolLibrary.FieldTheory.Finitary ←
  ioB "setupFinitary" <|
    (HolLibrary.FieldTheory.setupFinitary deps BSubfields BSubfieldGenerated BRingSpan BRingMatroid BLinearAlgebra).run

initialize BTowerLaw : HolLibrary.FieldTheory.TowerLaw ←
  ioB "setupTowerLaw" <|
    (HolLibrary.FieldTheory.setupTowerLaw deps BFieldExtension BRingSpan BLinearAlgebra BFinitary).run

initialize BFiniteExtension : HolLibrary.FieldTheory.FiniteExtension ←
  ioB "setupFiniteExtension" <|
    (HolLibrary.FieldTheory.setupFiniteExtension deps BSubfieldGenerated BSubfieldGenerated1 BSubfieldGenerated2 BFieldExtension BRingSpan BRingMatroid BLinearAlgebra BFinitary BTowerLaw).run

initialize BAlgebraicExtension : HolLibrary.FieldTheory.AlgebraicExtension ←
  ioB "setupAlgebraicExtension" <|
    (HolLibrary.FieldTheory.setupAlgebraicExtension deps BSubfieldGenerated BSubfieldGenerated1 BSubfieldGenerated2 BSubfieldQuotients BFieldExtension).run

initialize BAlgebraicOverBasics : HolLibrary.FieldTheory.AlgebraicOverBasics ←
  ioB "setupAlgebraicOverBasics" <|
    (HolLibrary.FieldTheory.setupAlgebraicOverBasics deps BFieldExtension BRingSpan BFinitary BFiniteExtension BAlgebraicExtension).run

initialize BAlgebraicExtensionProps : HolLibrary.FieldTheory.AlgebraicExtensionProps ←
  ioB "setupAlgebraicExtensionProps" <|
    (HolLibrary.FieldTheory.setupAlgebraicExtensionProps deps BSubfieldGenerated BFieldExtension BFiniteExtension BAlgebraicExtension BAlgebraicOverBasics).run

initialize BAlgebraicExtMisc : HolLibrary.FieldTheory.AlgebraicExtMisc ←
  ioB "setupAlgebraicExtMisc" <|
    (HolLibrary.FieldTheory.setupAlgebraicExtMisc deps BSubfieldQuotients BFieldExtension BFiniteExtension BAlgebraicExtension BAlgebraicOverBasics BAlgebraicExtensionProps).run

initialize BAlgebraicField : HolLibrary.FieldTheory.AlgebraicField ←
  ioB "setupAlgebraicField" <|
    (HolLibrary.FieldTheory.setupAlgebraicField deps BSubfields BSubfieldGenerated BFieldExtension BAlgebraicExtension BAlgebraicOverBasics BAlgebraicExtensionProps BAlgebraicExtMisc).run

initialize BFiniteExt : HolLibrary.FieldTheory.FiniteExt ←
  ioB "setupFiniteExt" <|
    (HolLibrary.FieldTheory.setupFiniteExt deps BFieldExtension BRingSpan BLinearAlgebra BFinitary BFiniteExtension).run

initialize BAlgDepDefs : HolLibrary.FieldTheory.AlgDepDefs ←
  ioB "setupAlgDepDefs" <|
    (HolLibrary.FieldTheory.setupAlgDepDefs deps BSubfieldGenerated BFieldExtension BRingSpan BFinitary BAlgebraicExtension BAlgebraicField).run

initialize BAlgDepSpan : HolLibrary.FieldTheory.AlgDepSpan ←
  ioB "setupAlgDepSpan" <|
    (HolLibrary.FieldTheory.setupAlgDepSpan deps BSubfieldGenerated BSubfieldGenerated1 BFieldExtension BAlgebraicExtension BAlgebraicExtensionProps BAlgebraicField BAlgDepDefs).run

initialize BAlgSpanDepIndep : HolLibrary.FieldTheory.AlgSpanDepIndep ←
  ioB "setupAlgSpanDepIndep" <|
    (HolLibrary.FieldTheory.setupAlgSpanDepIndep deps BSubfields BSubfieldGenerated BFieldExtension BAlgebraicExtension BAlgebraicExtensionProps BAlgDepDefs BAlgDepSpan).run

initialize BAlgebraicMatroid : HolLibrary.FieldTheory.AlgebraicMatroid ←
  ioB "setupAlgebraicMatroid" <|
    (HolLibrary.FieldTheory.setupAlgebraicMatroid deps BFieldExtension BAlgDepDefs BAlgDepSpan BAlgSpanDepIndep).run

initialize BAlgebraicTrans : HolLibrary.FieldTheory.AlgebraicTrans ←
  ioB "setupAlgebraicTrans" <|
    (HolLibrary.FieldTheory.setupAlgebraicTrans deps BSubfieldGenerated BSubfieldGenerated1 BFieldExtension BAlgebraicExtension BAlgebraicExtensionProps BAlgebraicField BAlgDepDefs BAlgDepSpan BAlgSpanDepIndep BAlgebraicMatroid).run

initialize BAlgebraicOverExt : HolLibrary.FieldTheory.AlgebraicOverExt ←
  ioB "setupAlgebraicOverExt" <|
    (HolLibrary.FieldTheory.setupAlgebraicOverExt deps BSubfieldGenerated BFieldExtension BFiniteExtension BAlgebraicExtension BAlgebraicExtMisc BAlgebraicField BAlgDepDefs BAlgSpanDepIndep BAlgebraicMatroid BAlgebraicTrans).run

initialize BTotallyTranscendental : HolLibrary.FieldTheory.TotallyTranscendental ←
  ioB "setupTotallyTranscendental" <|
    (HolLibrary.FieldTheory.setupTotallyTranscendental deps BSubfields BSubfieldGenerated BSubfieldGenerated1 BSubfieldGenerated2 BSubfieldQuotients BFieldExtension BAlgebraicExtension BAlgebraicExtensionProps BAlgebraicField BAlgDepDefs BAlgDepSpan BAlgSpanDepIndep).run

initialize BFinitelyGeneratedTransEq : HolLibrary.FieldTheory.FinitelyGeneratedTransEq ←
  ioB "setupFinitelyGeneratedTransEq" <|
    (HolLibrary.FieldTheory.setupFinitelyGeneratedTransEq deps BSubfields BSubfieldGenerated BSubfieldGenerated1 BFieldExtension BRingMatroid BLinearAlgebra BFinitary BFiniteExtension BAlgebraicExtension BAlgebraicExtensionProps BAlgebraicExtMisc BAlgDepDefs BAlgDepSpan BAlgSpanDepIndep BAlgebraicMatroid BAlgebraicTrans BAlgebraicOverExt BTotallyTranscendental).run

initialize BAcfBasic : HolLibrary.FieldTheory.AcfBasic ←
  ioB "setupAcfBasic" <|
    (HolLibrary.FieldTheory.setupAcfBasic deps BFieldExtension BAlgebraicOverBasics).run

initialize BAcfSplit : HolLibrary.FieldTheory.AcfSplit ←
  ioB "setupAcfSplit" <|
    (HolLibrary.FieldTheory.setupAcfSplit deps BAcfBasic).run

initialize BClosedFieldSplits : HolLibrary.FieldTheory.ClosedFieldSplits ←
  ioB "setupClosedFieldSplits" <|
    (HolLibrary.FieldTheory.setupClosedFieldSplits deps BAcfBasic BAcfSplit).run

initialize BSimpleExtendHom : HolLibrary.FieldTheory.SimpleExtendHom ←
  ioB "setupSimpleExtendHom" <|
    (HolLibrary.FieldTheory.setupSimpleExtendHom deps BAcfBasic).run

initialize BClosureExtendHom : HolLibrary.FieldTheory.ClosureExtendHom ←
  ioB "setupClosureExtendHom" <|
    (HolLibrary.FieldTheory.setupClosureExtendHom deps BSubfields BSubfieldGenerated2 BFieldExtension BAlgebraicExtension BAlgebraicExtensionProps BAcfBasic BSimpleExtendHom).run

initialize BPolySquarefree : HolLibrary.FieldTheory.PolySquarefree ←
  ioB "setupPolySquarefree" <|
    (HolLibrary.FieldTheory.setupPolySquarefree deps BAcfBasic BAcfSplit).run

initialize BAlgebraicClosureExistsId : HolLibrary.FieldTheory.AlgebraicClosureExistsId ←
  ioB "setupAlgebraicClosureExistsId" <|
    (HolLibrary.FieldTheory.setupAlgebraicClosureExistsId deps BFieldExtension BFiniteExtension BAlgebraicExtension BAlgebraicOverBasics BAlgebraicExtensionProps BAlgebraicExtMisc BAcfBasic).run

initialize BAlgebraicClosure : HolLibrary.FieldTheory.AlgebraicClosure ←
  ioB "setupAlgebraicClosure" <|
    (HolLibrary.FieldTheory.setupAlgebraicClosure deps BFieldExtension BAlgebraicExtension BAlgebraicOverBasics BAlgebraicExtMisc BAlgebraicField BAcfBasic BClosureExtendHom BAlgebraicClosureExistsId).run


-- Subfields
def subfield_of : thm := BSubfields.subfield_of
def SUBFIELD_IMP_SUBRING_OF : thm := BSubfields.SUBFIELD_IMP_SUBRING_OF
def SUBFIELD_OF_IMP_SUBSET : thm := BSubfields.SUBFIELD_OF_IMP_SUBSET
def SUBFIELD_OF_IMP_10 : thm := BSubfields.SUBFIELD_OF_IMP_10
def SUBFIELD_OF_IMP_NONTRIVIAL : thm := BSubfields.SUBFIELD_OF_IMP_NONTRIVIAL
def IN_SUBFIELD_LINV : thm := BSubfields.IN_SUBFIELD_LINV
def IN_SUBFIELD_RINV : thm := BSubfields.IN_SUBFIELD_RINV
def IN_SUBFIELD_INV : thm := BSubfields.IN_SUBFIELD_INV
def RING_INV_SUBRING_GENERATED : thm := BSubfields.RING_INV_SUBRING_GENERATED
def SUBFIELD_OF_FIELD_INV : thm := BSubfields.SUBFIELD_OF_FIELD_INV
def SUBFIELD_OF_INTERS : thm := BSubfields.SUBFIELD_OF_INTERS
def SUBFIELD_OF_INTER : thm := BSubfields.SUBFIELD_OF_INTER
def CARRIER_SUBFIELD_OF : thm := BSubfields.CARRIER_SUBFIELD_OF
def IN_SUBFIELD_0 : thm := BSubfields.IN_SUBFIELD_0
def IN_SUBFIELD_1 : thm := BSubfields.IN_SUBFIELD_1
def IN_SUBFIELD_NEG : thm := BSubfields.IN_SUBFIELD_NEG
def IN_SUBFIELD_ADD : thm := BSubfields.IN_SUBFIELD_ADD
def IN_SUBFIELD_MUL : thm := BSubfields.IN_SUBFIELD_MUL
def IN_SUBFIELD_SUB : thm := BSubfields.IN_SUBFIELD_SUB
def IN_SUBFIELD_POW : thm := BSubfields.IN_SUBFIELD_POW
def IN_SUBFIELD_SUM : thm := BSubfields.IN_SUBFIELD_SUM
def IN_SUBFIELD_PRODUCT : thm := BSubfields.IN_SUBFIELD_PRODUCT
def SUBFIELD_OF_HOMOMORPHIC_EQUALITIES : thm := BSubfields.SUBFIELD_OF_HOMOMORPHIC_EQUALITIES
def SUBFIELD_OF_FIXPOINTS : thm := BSubfields.SUBFIELD_OF_FIXPOINTS
def SUBFIELD_OF_SUBRING_QUOTIENTS : thm := BSubfields.SUBFIELD_OF_SUBRING_QUOTIENTS

-- SubfieldGenerated
def subfield_generated : thm := BSubfieldGenerated.subfield_generated
def SUBFIELD_GENERATED : thm := BSubfieldGenerated.SUBFIELD_GENERATED
def CARRIER_SUBFIELD_GENERATED_FIELD : thm := BSubfieldGenerated.CARRIER_SUBFIELD_GENERATED_FIELD
def CARRIER_SUBFIELD_GENERATED_SUBFIELD : thm := BSubfieldGenerated.CARRIER_SUBFIELD_GENERATED_SUBFIELD
def RING_CARRIER_SUBFIELD_GENERATED_SUBSET : thm := BSubfieldGenerated.RING_CARRIER_SUBFIELD_GENERATED_SUBSET
def SUBFIELD_GENERATED_RESTRICT : thm := BSubfieldGenerated.SUBFIELD_GENERATED_RESTRICT
def SUBFIELD_GENERATED_MONO : thm := BSubfieldGenerated.SUBFIELD_GENERATED_MONO
def SUBFIELD_GENERATED_MINIMAL : thm := BSubfieldGenerated.SUBFIELD_GENERATED_MINIMAL
def SUBRING_SUBSET_SUBFIELD_GENERATED : thm := BSubfieldGenerated.SUBRING_SUBSET_SUBFIELD_GENERATED
def SUBRING_SUBFIELD_GENERATED : thm := BSubfieldGenerated.SUBRING_SUBFIELD_GENERATED
def SUBFIELD_GENERATED_TRIVIAL : thm := BSubfieldGenerated.SUBFIELD_GENERATED_TRIVIAL
def SUBRING_EQ_SUBFIELD_GENERATED : thm := BSubfieldGenerated.SUBRING_EQ_SUBFIELD_GENERATED
def SUBRING_GENERATED_BY_SUBFIELD_GENERATED : thm := BSubfieldGenerated.SUBRING_GENERATED_BY_SUBFIELD_GENERATED
def SUBFIELD_GENERATED_SUBSET_CARRIER : thm := BSubfieldGenerated.SUBFIELD_GENERATED_SUBSET_CARRIER
def SUBFIELD_SUBFIELD_GENERATED_ALT : thm := BSubfieldGenerated.SUBFIELD_SUBFIELD_GENERATED_ALT
def SUBFIELD_SUBFIELD_GENERATED : thm := BSubfieldGenerated.SUBFIELD_SUBFIELD_GENERATED
def FIELD_SUBFIELD_GENERATED_ALT : thm := BSubfieldGenerated.FIELD_SUBFIELD_GENERATED_ALT
def FIELD_SUBFIELD_GENERATED_EQ : thm := BSubfieldGenerated.FIELD_SUBFIELD_GENERATED_EQ
def SUBFIELD_SUBFIELD_GENERATED_EQ : thm := BSubfieldGenerated.SUBFIELD_SUBFIELD_GENERATED_EQ
def FIELD_SUBFIELD_GENERATED : thm := BSubfieldGenerated.FIELD_SUBFIELD_GENERATED
def FIELD_SUBFIELD_GENERATED_MONO : thm := BSubfieldGenerated.FIELD_SUBFIELD_GENERATED_MONO
def SUBFIELD_GENERATED_EQ : thm := BSubfieldGenerated.SUBFIELD_GENERATED_EQ
def SUBFIELDS_GENERATED_EQ : thm := BSubfieldGenerated.SUBFIELDS_GENERATED_EQ
def SUBFIELD_GENERATED_SUPERSET : thm := BSubfieldGenerated.SUBFIELD_GENERATED_SUPERSET
def FINITE_SUBFIELD_GENERATED : thm := BSubfieldGenerated.FINITE_SUBFIELD_GENERATED

-- SubfieldGenerated1
def SUBSET_CARRIER_SUBFIELD_GENERATED : thm := BSubfieldGenerated1.SUBSET_CARRIER_SUBFIELD_GENERATED
def SUBFIELD_GENERATED_MINIMAL_EQ : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_MINIMAL_EQ
def SUBFIELD_GENERATED_RING_CARRIER : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_RING_CARRIER
def SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET
def SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED
def SUBFIELD_GENERATED_REFL : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_REFL
def SUBFIELD_GENERATED_INC : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_INC
def SUBFIELD_GENERATED_INC_GEN : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_INC_GEN
def SUBRING_OF_SUBFIELD_GENERATED_EQ : thm := BSubfieldGenerated1.SUBRING_OF_SUBFIELD_GENERATED_EQ
def SUBFIELD_OF_SUBFIELD_GENERATED_EQ : thm := BSubfieldGenerated1.SUBFIELD_OF_SUBFIELD_GENERATED_EQ
def SUBFIELD_OF_SUBFIELD_GENERATED_SUBFIELD_EQ : thm := BSubfieldGenerated1.SUBFIELD_OF_SUBFIELD_GENERATED_SUBFIELD_EQ
def SUBFIELD_OF_SUBFIELD_GENERATED : thm := BSubfieldGenerated1.SUBFIELD_OF_SUBFIELD_GENERATED
def SUBFIELD_OF_SUBFIELD_GENERATED_REV : thm := BSubfieldGenerated1.SUBFIELD_OF_SUBFIELD_GENERATED_REV
def SUBFIELD_GENERATED_IDEMPOT : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_IDEMPOT
def SUBFIELD_GENERATED_SUBFIELD_GENERATED : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_SUBFIELD_GENERATED
def SUBRING_GENERATED_SUBFIELD_GENERATED : thm := BSubfieldGenerated1.SUBRING_GENERATED_SUBFIELD_GENERATED
def TRIVIAL_RING_SUBFIELD_GENERATED : thm := BSubfieldGenerated1.TRIVIAL_RING_SUBFIELD_GENERATED
def SUBFIELD_GENERATED_UNION_LEFT : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_UNION_LEFT
def SUBFIELD_GENERATED_UNION_RIGHT : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_UNION_RIGHT
def SUBFIELD_GENERATED_UNION : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_UNION

-- SubfieldGenerated2
def SUBFIELD_OF_MONOMORPHIC_IMAGE : thm := BSubfieldGenerated2.SUBFIELD_OF_MONOMORPHIC_IMAGE
def SUBFIELD_OF_MONOMORPHIC_PREIMAGE : thm := BSubfieldGenerated2.SUBFIELD_OF_MONOMORPHIC_PREIMAGE
def SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE : thm := BSubfieldGenerated2.SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE
def RING_SUB_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_SUB_SUBFIELD_GENERATED
def RING_POW_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_POW_SUBFIELD_GENERATED
def RING_OF_NUM_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_OF_NUM_SUBFIELD_GENERATED
def RING_OF_INT_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_OF_INT_SUBFIELD_GENERATED
def RING_CHAR_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_CHAR_SUBFIELD_GENERATED
def RING_0_IN_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_0_IN_SUBFIELD_GENERATED
def RING_1_IN_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_1_IN_SUBFIELD_GENERATED
def RING_NEG_IN_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_NEG_IN_SUBFIELD_GENERATED
def RING_ADD_IN_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_ADD_IN_SUBFIELD_GENERATED
def RING_MUL_IN_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_MUL_IN_SUBFIELD_GENERATED
def RING_POW_IN_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_POW_IN_SUBFIELD_GENERATED
def RING_INV_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_INV_SUBFIELD_GENERATED
def RING_INV_IN_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_INV_IN_SUBFIELD_GENERATED
def RING_DIV_IN_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_DIV_IN_SUBFIELD_GENERATED
def SUBFIELD_GENERATED_INDUCT : thm := BSubfieldGenerated2.SUBFIELD_GENERATED_INDUCT
def POLY_CONST_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.POLY_CONST_SUBFIELD_GENERATED
def POLY_SUBFIELD_GENERATED_CLAUSES : thm := BSubfieldGenerated2.POLY_SUBFIELD_GENERATED_CLAUSES

-- SubfieldQuotients
def FIELD_SUBFIELD_GENERATED_UNITS : thm := BSubfieldQuotients.FIELD_SUBFIELD_GENERATED_UNITS
def SUBFIELD_GENERATED_SUBRING_QUOTIENTS : thm := BSubfieldQuotients.SUBFIELD_GENERATED_SUBRING_QUOTIENTS
def RING_CARRIER_SUBFIELD_GENERATED_SUBRING_QUOTIENTS : thm := BSubfieldQuotients.RING_CARRIER_SUBFIELD_GENERATED_SUBRING_QUOTIENTS
def SUBFIELD_GENERATED_QUOTIENTS : thm := BSubfieldQuotients.SUBFIELD_GENERATED_QUOTIENTS
def FINITE_SUBSET_SUBFIELD_GENERATED_DENOMINATOR : thm := BSubfieldQuotients.FINITE_SUBSET_SUBFIELD_GENERATED_DENOMINATOR
def POLY_OVER_SUBFIELD_GENERATED_DENOMINATOR : thm := BSubfieldQuotients.POLY_OVER_SUBFIELD_GENERATED_DENOMINATOR
def IN_SUBFIELD_GENERATED_FINITARY : thm := BSubfieldQuotients.IN_SUBFIELD_GENERATED_FINITARY
def PRIME_SUBFIELD_MINIMAL : thm := BSubfieldQuotients.PRIME_SUBFIELD_MINIMAL
def PRIME_SUBFIELD_EQ_SUBRING : thm := BSubfieldQuotients.PRIME_SUBFIELD_EQ_SUBRING
def FROBENIUS_FIXED_FIELD : thm := BSubfieldQuotients.FROBENIUS_FIXED_FIELD

-- FieldExtension
def field_extension : thm := BFieldExtension.field_extension
def FIELD_EXTENSION_IMP_MONOMORPHISM : thm := BFieldExtension.FIELD_EXTENSION_IMP_MONOMORPHISM
def FIELD_EXTENSION_IMP_HOMOMORPHISM : thm := BFieldExtension.FIELD_EXTENSION_IMP_HOMOMORPHISM
def FIELD_EXTENSION_IMP_SUBSET : thm := BFieldExtension.FIELD_EXTENSION_IMP_SUBSET
def FIELD_EXTENSION_CARRIER : thm := BFieldExtension.FIELD_EXTENSION_CARRIER
def FIELD_EXTENSION_FROM_SUBRING_GENERATED : thm := BFieldExtension.FIELD_EXTENSION_FROM_SUBRING_GENERATED
def FIELD_EXTENSION_EQ : thm := BFieldExtension.FIELD_EXTENSION_EQ
def FIELD_EXTENSION_REFL : thm := BFieldExtension.FIELD_EXTENSION_REFL
def FIELD_EXTENSION_TRANS : thm := BFieldExtension.FIELD_EXTENSION_TRANS
def FIELD_EXTENSION_TRANS_I : thm := BFieldExtension.FIELD_EXTENSION_TRANS_I
def FIELD_EXTENSION_ISOMORPHISM : thm := BFieldExtension.FIELD_EXTENSION_ISOMORPHISM
def FIELD_EXTENSION_SUBRING_GENERATED : thm := BFieldExtension.FIELD_EXTENSION_SUBRING_GENERATED
def FIELD_EXTENSION_INTO_SUBRING_GENERATED : thm := BFieldExtension.FIELD_EXTENSION_INTO_SUBRING_GENERATED
def FIELD_EXTENSION_INTO_SUBFIELD_GENERATED : thm := BFieldExtension.FIELD_EXTENSION_INTO_SUBFIELD_GENERATED
def KRONECKER_FIELD_EXTENSION : thm := BFieldExtension.KRONECKER_FIELD_EXTENSION
def KRONECKER_SIMPLE_FIELD_EXTENSION : thm := BFieldExtension.KRONECKER_SIMPLE_FIELD_EXTENSION
def COPRIME_POLY_NO_COMMON_ROOT : thm := BFieldExtension.COPRIME_POLY_NO_COMMON_ROOT
def COPRIME_POLY_NO_COMMON_ROOT_I : thm := BFieldExtension.COPRIME_POLY_NO_COMMON_ROOT_I

-- RingSpan
def ring_span_RULES : thm := BRingSpan.ring_span_RULES
def ring_span_INDUCT : thm := BRingSpan.ring_span_INDUCT
def ring_span_CASES : thm := BRingSpan.ring_span_CASES
def RING_SPAN_0 : thm := BRingSpan.RING_SPAN_0
def RING_SPAN_INC : thm := BRingSpan.RING_SPAN_INC
def RING_SPAN_ADD : thm := BRingSpan.RING_SPAN_ADD
def RING_SPAN_MUL : thm := BRingSpan.RING_SPAN_MUL
def RING_SPAN_SUBSET : thm := BRingSpan.RING_SPAN_SUBSET
def RING_SPAN_SUPERSET_GEN : thm := BRingSpan.RING_SPAN_SUPERSET_GEN
def RING_SPAN_SUPERSET : thm := BRingSpan.RING_SPAN_SUPERSET
def RING_SPAN_SUPERSET_EQ : thm := BRingSpan.RING_SPAN_SUPERSET_EQ
def RING_SPAN_MONO : thm := BRingSpan.RING_SPAN_MONO
def SUBSET_RING_SPAN : thm := BRingSpan.SUBSET_RING_SPAN
def RING_SPAN_RESTRICT : thm := BRingSpan.RING_SPAN_RESTRICT
def RING_SPAN_SPAN : thm := BRingSpan.RING_SPAN_SPAN
def RING_SPAN_FINITARY : thm := BRingSpan.RING_SPAN_FINITARY
def RING_SPAN_NONEMPTY : thm := BRingSpan.RING_SPAN_NONEMPTY
def RING_SPAN_SELF : thm := BRingSpan.RING_SPAN_SELF
def RING_SPAN_EMPTY : thm := BRingSpan.RING_SPAN_EMPTY
def RING_SPAN_NEG : thm := BRingSpan.RING_SPAN_NEG
def RING_SPAN_SUB : thm := BRingSpan.RING_SPAN_SUB
def RING_SPAN_SUM : thm := BRingSpan.RING_SPAN_SUM
def RING_SPAN_UNION : thm := BRingSpan.RING_SPAN_UNION
def RING_SPAN_SING : thm := BRingSpan.RING_SPAN_SING
def RING_SPAN_EXCHANGE : thm := BRingSpan.RING_SPAN_EXCHANGE
def RING_SPAN_FINITE : thm := BRingSpan.RING_SPAN_FINITE
def RING_SPAN_HOMOMORPHIC_IMAGE : thm := BRingSpan.RING_SPAN_HOMOMORPHIC_IMAGE

-- RingMatroid
def ring_matroid : thm := BRingMatroid.ring_matroid
def RING_MATROID : thm := BRingMatroid.RING_MATROID

-- LinearAlgebra
def ring_dependent : thm := BLinearAlgebra.ring_dependent
def ring_independent : thm := BLinearAlgebra.ring_independent
def ring_spanning : thm := BLinearAlgebra.ring_spanning
def ring_basis : thm := BLinearAlgebra.ring_basis
def RING_DEPENDENT_IMP_SUBSET : thm := BLinearAlgebra.RING_DEPENDENT_IMP_SUBSET
def RING_INDEPENDENT_IMP_SUBSET : thm := BLinearAlgebra.RING_INDEPENDENT_IMP_SUBSET
def RING_SPANNING_IMP_SUBSET : thm := BLinearAlgebra.RING_SPANNING_IMP_SUBSET
def RING_BASIS_IMP_SUBSET : thm := BLinearAlgebra.RING_BASIS_IMP_SUBSET
def RING_MATROID_INDEPENDENT : thm := BLinearAlgebra.RING_MATROID_INDEPENDENT
def RING_MATROID_SPANNING : thm := BLinearAlgebra.RING_MATROID_SPANNING
def RING_MATROID_BASIS : thm := BLinearAlgebra.RING_MATROID_BASIS
def RING_BASIS_EXISTS : thm := BLinearAlgebra.RING_BASIS_EXISTS
def RING_SPANNING_CONTAINS_BASIS : thm := BLinearAlgebra.RING_SPANNING_CONTAINS_BASIS
def RING_BASES_CARD_EQ : thm := BLinearAlgebra.RING_BASES_CARD_EQ
def RING_SPANNING_ALT : thm := BLinearAlgebra.RING_SPANNING_ALT
def RING_SPANNING_IMP_NONEMPTY : thm := BLinearAlgebra.RING_SPANNING_IMP_NONEMPTY
def RING_INDEPENDENT_EMPTY : thm := BLinearAlgebra.RING_INDEPENDENT_EMPTY
def RING_INDEPENDENT_NONZERO : thm := BLinearAlgebra.RING_INDEPENDENT_NONZERO
def RING_DEPENDENT_MONO : thm := BLinearAlgebra.RING_DEPENDENT_MONO
def RING_INDEPENDENT_MONO : thm := BLinearAlgebra.RING_INDEPENDENT_MONO

-- Finitary
def RING_DEPENDENT_FINITARY : thm := BFinitary.RING_DEPENDENT_FINITARY
def RING_INDEPENDENT_FINITARY : thm := BFinitary.RING_INDEPENDENT_FINITARY
def RING_INDEPENDENT_LE_SPAN : thm := BFinitary.RING_INDEPENDENT_LE_SPAN
def RING_DEPENDENT_FINITE : thm := BFinitary.RING_DEPENDENT_FINITE
def RING_INDEPENDENT_FINITE : thm := BFinitary.RING_INDEPENDENT_FINITE
def RING_INDEPENDENT_FINITE_EQ : thm := BFinitary.RING_INDEPENDENT_FINITE_EQ
def RING_DEPENDENT_SPAN_IMAGE : thm := BFinitary.RING_DEPENDENT_SPAN_IMAGE
def RING_SPAN_SUBSET_SUBRING_GENERATED : thm := BFinitary.RING_SPAN_SUBSET_SUBRING_GENERATED
def RING_SPAN_SUBSET_SUBFIELD_GENERATED : thm := BFinitary.RING_SPAN_SUBSET_SUBFIELD_GENERATED
def RING_INDEPENDENT_INSERT : thm := BFinitary.RING_INDEPENDENT_INSERT
def RING_INDEPENDENT_CARD_LE_SPANNING : thm := BFinitary.RING_INDEPENDENT_CARD_LE_SPANNING

-- TowerLaw
def RING_SPANNING_TRANS : thm := BTowerLaw.RING_SPANNING_TRANS
def RING_INDEPENDENT_PRODUCTS : thm := BTowerLaw.RING_INDEPENDENT_PRODUCTS
def RING_INDEPENDENT_TRANS : thm := BTowerLaw.RING_INDEPENDENT_TRANS
def RING_BASIS_TRANS : thm := BTowerLaw.RING_BASIS_TRANS
def FIELD_EXTENSION_TOWER_LAW : thm := BTowerLaw.FIELD_EXTENSION_TOWER_LAW

-- FiniteExtension
def finite_extension : thm := BFiniteExtension.finite_extension
def RING_MATROID_FINITE_DIMENSIONAL : thm := BFiniteExtension.RING_MATROID_FINITE_DIMENSIONAL
def FINITE_IMP_FIELD_EXTENSION : thm := BFiniteExtension.FINITE_IMP_FIELD_EXTENSION
def FINITE_EXTENSION_RING_MATROID : thm := BFiniteExtension.FINITE_EXTENSION_RING_MATROID
def FINITE_EXTENSION : thm := BFiniteExtension.FINITE_EXTENSION
def FINITE_EXTENSION_SPANNING : thm := BFiniteExtension.FINITE_EXTENSION_SPANNING
def FINITE_EXTENSION_BASIS : thm := BFiniteExtension.FINITE_EXTENSION_BASIS
def FINITE_EXTENSION_ANY : thm := BFiniteExtension.FINITE_EXTENSION_ANY
def FINITE_EXTENSION_ISOMORPHISM : thm := BFiniteExtension.FINITE_EXTENSION_ISOMORPHISM
def FINITE_EXTENSION_TRANS : thm := BFiniteExtension.FINITE_EXTENSION_TRANS
def FINITE_EXTENSION_TRANS_EQ : thm := BFiniteExtension.FINITE_EXTENSION_TRANS_EQ
def finitely_generated_extension : thm := BFiniteExtension.finitely_generated_extension
def FINITELY_GENERATED_IMP_FIELD_EXTENSION : thm := BFiniteExtension.FINITELY_GENERATED_IMP_FIELD_EXTENSION
def FINITE_IMP_FINITELY_GENERATED_EXTENSION : thm := BFiniteExtension.FINITE_IMP_FINITELY_GENERATED_EXTENSION
def FINITELY_GENERATED_EXTENSION : thm := BFiniteExtension.FINITELY_GENERATED_EXTENSION
def FINITELY_GENERATED_EXTENSION_TRANS : thm := BFiniteExtension.FINITELY_GENERATED_EXTENSION_TRANS

-- AlgebraicExtension
def algebraic_over : thm := BAlgebraicExtension.algebraic_over
def transcendental_over : thm := BAlgebraicExtension.transcendental_over
def algebraic_extension : thm := BAlgebraicExtension.algebraic_extension
def ALGEBRAIC_OVER : thm := BAlgebraicExtension.ALGEBRAIC_OVER
def ALGEBRAIC_IMP_FIELD_EXTENSION : thm := BAlgebraicExtension.ALGEBRAIC_IMP_FIELD_EXTENSION
def ALGEBRAIC_OVER_ALT : thm := BAlgebraicExtension.ALGEBRAIC_OVER_ALT
def ALGEBRAIC_OVER_IN_CARRIER : thm := BAlgebraicExtension.ALGEBRAIC_OVER_IN_CARRIER
def TRANSCENDENTAL_OVER_IN_CARRIER : thm := BAlgebraicExtension.TRANSCENDENTAL_OVER_IN_CARRIER
def ALGEBRAIC_OVER_IMAGE_GEN : thm := BAlgebraicExtension.ALGEBRAIC_OVER_IMAGE_GEN
def ALGEBRAIC_OVER_IMAGE : thm := BAlgebraicExtension.ALGEBRAIC_OVER_IMAGE
def ALGEBRAIC_OVER_IMAGE_SUBSET : thm := BAlgebraicExtension.ALGEBRAIC_OVER_IMAGE_SUBSET
def ALGEBRAIC_OVER_REFL : thm := BAlgebraicExtension.ALGEBRAIC_OVER_REFL
def ALGEBRAIC_OVER_SUBRING_GENERATED : thm := BAlgebraicExtension.ALGEBRAIC_OVER_SUBRING_GENERATED
def ALGEBRAIC_OVER_SUBFIELD_GENERATED : thm := BAlgebraicExtension.ALGEBRAIC_OVER_SUBFIELD_GENERATED
def ALGEBRAIC_OVER_SUBRING_GENERATED_MONO : thm := BAlgebraicExtension.ALGEBRAIC_OVER_SUBRING_GENERATED_MONO
def ALGEBRAIC_OVER_SUBFIELD_SUBRING_GENERATED : thm := BAlgebraicExtension.ALGEBRAIC_OVER_SUBFIELD_SUBRING_GENERATED

-- AlgebraicOverBasics
def ALGEBRAIC_OVER_NONMONOMORPHISM : thm := BAlgebraicOverBasics.ALGEBRAIC_OVER_NONMONOMORPHISM
def ALGEBRAIC_EXTENSION : thm := BAlgebraicOverBasics.ALGEBRAIC_EXTENSION
def ALGEBRAIC_EXTENSION_ALT : thm := BAlgebraicOverBasics.ALGEBRAIC_EXTENSION_ALT
def ALGEBRAIC_OVER_EQ : thm := BAlgebraicOverBasics.ALGEBRAIC_OVER_EQ
def ALGEBRAIC_OVER_EQ_EQ : thm := BAlgebraicOverBasics.ALGEBRAIC_OVER_EQ_EQ
def ALGEBRAIC_EXTENSION_EQ : thm := BAlgebraicOverBasics.ALGEBRAIC_EXTENSION_EQ
def FINITE_IMP_ALGEBRAIC_EXTENSION_EXPLICIT : thm := BAlgebraicOverBasics.FINITE_IMP_ALGEBRAIC_EXTENSION_EXPLICIT
def FINITE_IMP_ALGEBRAIC_EXTENSION : thm := BAlgebraicOverBasics.FINITE_IMP_ALGEBRAIC_EXTENSION
def RING_SIMPLE_EXTENSION_SPAN : thm := BAlgebraicOverBasics.RING_SIMPLE_EXTENSION_SPAN
def RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN : thm := BAlgebraicOverBasics.RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN

-- AlgebraicExtensionProps
def FIELD_SIMPLE_ALGEBRAIC_EXTENSION_GEN : thm := BAlgebraicExtensionProps.FIELD_SIMPLE_ALGEBRAIC_EXTENSION_GEN
def FIELD_SIMPLE_ALGEBRAIC_EXTENSION_EQ : thm := BAlgebraicExtensionProps.FIELD_SIMPLE_ALGEBRAIC_EXTENSION_EQ
def FIELD_SIMPLE_ALGEBRAIC_EXTENSION : thm := BAlgebraicExtensionProps.FIELD_SIMPLE_ALGEBRAIC_EXTENSION
def FINITE_SIMPLE_ALGEBRAIC_EXTENSION : thm := BAlgebraicExtensionProps.FINITE_SIMPLE_ALGEBRAIC_EXTENSION
def ALGEBRAIC_OVER_FROM_MONOMORPHIC_IMAGE : thm := BAlgebraicExtensionProps.ALGEBRAIC_OVER_FROM_MONOMORPHIC_IMAGE
def ALGEBRAIC_OVER_ISOMORPHIC_IMAGE : thm := BAlgebraicExtensionProps.ALGEBRAIC_OVER_ISOMORPHIC_IMAGE
def ALGEBRAIC_OVER_RANGE : thm := BAlgebraicExtensionProps.ALGEBRAIC_OVER_RANGE
def ALGEBRAIC_OVER_FIELD_EXTENSION : thm := BAlgebraicExtensionProps.ALGEBRAIC_OVER_FIELD_EXTENSION
def FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION : thm := BAlgebraicExtensionProps.FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION
def FINITE_EQ_FINITELY_GENERATED_ALGEBRAIC_EXTENSION : thm := BAlgebraicExtensionProps.FINITE_EQ_FINITELY_GENERATED_ALGEBRAIC_EXTENSION

-- AlgebraicExtMisc
def ALGEBRAIC_FROM_SUBRING_GENERATED : thm := BAlgebraicExtMisc.ALGEBRAIC_FROM_SUBRING_GENERATED
def ALGEBRAIC_EXTENSION_ISOMORPHISM : thm := BAlgebraicExtMisc.ALGEBRAIC_EXTENSION_ISOMORPHISM
def ALGEBRAIC_EXTENSION_REFL : thm := BAlgebraicExtMisc.ALGEBRAIC_EXTENSION_REFL
def ALGEBRAIC_EXTENSION_TRANS : thm := BAlgebraicExtMisc.ALGEBRAIC_EXTENSION_TRANS
def ALGEBRAIC_EXTENSION_TRANS_EQ : thm := BAlgebraicExtMisc.ALGEBRAIC_EXTENSION_TRANS_EQ
def CARD_LE_ALGEBRAIC_EXTENSION : thm := BAlgebraicExtMisc.CARD_LE_ALGEBRAIC_EXTENSION
def CARD_EQ_ALGEBRAIC_EXTENSION : thm := BAlgebraicExtMisc.CARD_EQ_ALGEBRAIC_EXTENSION
def RING_AUTOMORPHISM_OF_ALGEBRAIC_EXTENSION : thm := BAlgebraicExtMisc.RING_AUTOMORPHISM_OF_ALGEBRAIC_EXTENSION
def RING_AUTOMORPHISM_FROBENIUS_GEN : thm := BAlgebraicExtMisc.RING_AUTOMORPHISM_FROBENIUS_GEN

-- AlgebraicField
def ALGEBRAIC_OVER_0 : thm := BAlgebraicField.ALGEBRAIC_OVER_0
def ALGEBRAIC_OVER_1 : thm := BAlgebraicField.ALGEBRAIC_OVER_1
def ALGEBRAIC_OVER_NEG : thm := BAlgebraicField.ALGEBRAIC_OVER_NEG
def ALGEBRAIC_OVER_INV : thm := BAlgebraicField.ALGEBRAIC_OVER_INV
def ALGEBRAIC_OVER_ADD : thm := BAlgebraicField.ALGEBRAIC_OVER_ADD
def ALGEBRAIC_OVER_MUL : thm := BAlgebraicField.ALGEBRAIC_OVER_MUL
def ALGEBRAIC_OVER_SUB : thm := BAlgebraicField.ALGEBRAIC_OVER_SUB
def ALGEBRAIC_OVER_DIV : thm := BAlgebraicField.ALGEBRAIC_OVER_DIV
def ALGEBRAIC_OVER_POW : thm := BAlgebraicField.ALGEBRAIC_OVER_POW
def SUBRING_OF_ALGEBRAIC_OVER : thm := BAlgebraicField.SUBRING_OF_ALGEBRAIC_OVER
def SUBFIELD_OF_ALGEBRAIC_OVER : thm := BAlgebraicField.SUBFIELD_OF_ALGEBRAIC_OVER
def ALGEBRAIC_OVER_SUBFIELD_GENERATED_ALGEBRAIC : thm := BAlgebraicField.ALGEBRAIC_OVER_SUBFIELD_GENERATED_ALGEBRAIC
def FIELD_ALGEBRAIC_EXTENSION : thm := BAlgebraicField.FIELD_ALGEBRAIC_EXTENSION
def SUBFIELD_OF_ALGEBRAIC_EXTENSION : thm := BAlgebraicField.SUBFIELD_OF_ALGEBRAIC_EXTENSION
def FIELD_ALGEBRAIC_OVER : thm := BAlgebraicField.FIELD_ALGEBRAIC_OVER
def SUBRING_SUBFIELD_ALGEBRAIC_OVER : thm := BAlgebraicField.SUBRING_SUBFIELD_ALGEBRAIC_OVER
def ALGEBRAIC_OVER_TRANS : thm := BAlgebraicField.ALGEBRAIC_OVER_TRANS
def ALGEBRAIC_OVER_ALGEBRAIC_EXTENSION : thm := BAlgebraicField.ALGEBRAIC_OVER_ALGEBRAIC_EXTENSION

-- FiniteExt
def FINITE_EQ_FIELD_EXTENSION : thm := BFiniteExt.FINITE_EQ_FIELD_EXTENSION
def HAS_SIZE_FINITE_EXTENSION : thm := BFiniteExt.HAS_SIZE_FINITE_EXTENSION
def FINITE_FINITE_FIELD_EXTENSION : thm := BFiniteExt.FINITE_FINITE_FIELD_EXTENSION
def CARD_FINITE_EXTENSION : thm := BFiniteExt.CARD_FINITE_EXTENSION
def FIELD_EXTENSION_FROM_PRIME_SUBRING : thm := BFiniteExt.FIELD_EXTENSION_FROM_PRIME_SUBRING
def FINITE_INTEGRAL_DOMAIN_SIZE : thm := BFiniteExt.FINITE_INTEGRAL_DOMAIN_SIZE

-- AlgDepDefs
def algebraically_dependent : thm := BAlgDepDefs.algebraically_dependent
def algebraically_independent : thm := BAlgDepDefs.algebraically_independent
def algebraic_span : thm := BAlgDepDefs.algebraic_span
def algebraically_spanning : thm := BAlgDepDefs.algebraically_spanning
def transcendence_basis : thm := BAlgDepDefs.transcendence_basis
def ALGEBRAICALLY_DEPENDENT_IMP_SUBSET : thm := BAlgDepDefs.ALGEBRAICALLY_DEPENDENT_IMP_SUBSET
def ALGEBRAICALLY_INDEPENDENT_IMP_SUBSET : thm := BAlgDepDefs.ALGEBRAICALLY_INDEPENDENT_IMP_SUBSET
def TRANSCENDENCE_BASIS_IMP_SUBSET : thm := BAlgDepDefs.TRANSCENDENCE_BASIS_IMP_SUBSET
def ALGEBRAICALLY_DEPENDENT_ALT : thm := BAlgDepDefs.ALGEBRAICALLY_DEPENDENT_ALT
def ALGEBRAIC_SPAN : thm := BAlgDepDefs.ALGEBRAIC_SPAN
def ALGEBRAIC_SPAN_FIELD : thm := BAlgDepDefs.ALGEBRAIC_SPAN_FIELD
def ALGEBRAIC_SPAN_RANGE : thm := BAlgDepDefs.ALGEBRAIC_SPAN_RANGE
def ALGEBRAIC_SPAN_RESTRICT : thm := BAlgDepDefs.ALGEBRAIC_SPAN_RESTRICT
def ALGEBRAIC_SPAN_SUBSET : thm := BAlgDepDefs.ALGEBRAIC_SPAN_SUBSET
def RING_SPAN_SUBSET_ALGEBRAIC_SPAN : thm := BAlgDepDefs.RING_SPAN_SUBSET_ALGEBRAIC_SPAN
def ALGEBRAIC_SPAN_SUPERSET : thm := BAlgDepDefs.ALGEBRAIC_SPAN_SUPERSET
def ALGEBRAIC_SPAN_MONO : thm := BAlgDepDefs.ALGEBRAIC_SPAN_MONO
def ALGEBRAIC_EXTENSION_SUBFIELD_GENERATED_ALGEBRAIC : thm := BAlgDepDefs.ALGEBRAIC_EXTENSION_SUBFIELD_GENERATED_ALGEBRAIC
def ALGEBRAIC_EXTENSION_SUBRING_GENERATED_ALGEBRAIC : thm := BAlgDepDefs.ALGEBRAIC_EXTENSION_SUBRING_GENERATED_ALGEBRAIC

-- AlgDepSpan
def ALGEBRAIC_SPAN_SPAN : thm := BAlgDepSpan.ALGEBRAIC_SPAN_SPAN
def ALGEBRAIC_SPAN_FINITARY : thm := BAlgDepSpan.ALGEBRAIC_SPAN_FINITARY
def ALGEBRAIC_SPAN_EMPTY : thm := BAlgDepSpan.ALGEBRAIC_SPAN_EMPTY
def ALGEBRAICALLY_INDEPENDENT_EMPTY : thm := BAlgDepSpan.ALGEBRAICALLY_INDEPENDENT_EMPTY
def ALGEBRAICALLY_DEPENDENT_SING : thm := BAlgDepSpan.ALGEBRAICALLY_DEPENDENT_SING
def ALGEBRAICALLY_INDEPENDENT_SING : thm := BAlgDepSpan.ALGEBRAICALLY_INDEPENDENT_SING
def ALGEBRAICALLY_DEPENDENT_MONO : thm := BAlgDepSpan.ALGEBRAICALLY_DEPENDENT_MONO
def ALGEBRAICALLY_DEPENDENT_OVER_SUBRING_GENERATED_MONO : thm := BAlgDepSpan.ALGEBRAICALLY_DEPENDENT_OVER_SUBRING_GENERATED_MONO
def ALGEBRAICALLY_INDEPENDENT_MONO : thm := BAlgDepSpan.ALGEBRAICALLY_INDEPENDENT_MONO
def ALGEBRAICALLY_INDEPENDENT_OVER_SUBRING_GENERATED_MONO : thm := BAlgDepSpan.ALGEBRAICALLY_INDEPENDENT_OVER_SUBRING_GENERATED_MONO
def ALGEBRAICALLY_INDEPENDENT_IMP_TRANSCENDENTAL : thm := BAlgDepSpan.ALGEBRAICALLY_INDEPENDENT_IMP_TRANSCENDENTAL
def ALGEBRAICALLY_INDEPENDENT_IMP_DISJOINT : thm := BAlgDepSpan.ALGEBRAICALLY_INDEPENDENT_IMP_DISJOINT

-- AlgSpanDepIndep
def ALGEBRAICALLY_DEPENDENT_FINITARY : thm := BAlgSpanDepIndep.ALGEBRAICALLY_DEPENDENT_FINITARY
def RING_MONOMORPHISM_POLY_EXTEND : thm := BAlgSpanDepIndep.RING_MONOMORPHISM_POLY_EXTEND
def ALGEBRAICALLY_DEPENDENT_FROM_INSERT : thm := BAlgSpanDepIndep.ALGEBRAICALLY_DEPENDENT_FROM_INSERT
def ALGEBRAICALLY_DEPENDENT_INSERT : thm := BAlgSpanDepIndep.ALGEBRAICALLY_DEPENDENT_INSERT
def ALGEBRAICALLY_INDEPENDENT_INSERT : thm := BAlgSpanDepIndep.ALGEBRAICALLY_INDEPENDENT_INSERT
def ALGEBRAICALLY_DEPENDENT_SPAN : thm := BAlgSpanDepIndep.ALGEBRAICALLY_DEPENDENT_SPAN
def ALGEBRAICALLY_INDEPENDENT_SPAN : thm := BAlgSpanDepIndep.ALGEBRAICALLY_INDEPENDENT_SPAN
def ALGEBRAIC_SPAN_EXCHANGE : thm := BAlgSpanDepIndep.ALGEBRAIC_SPAN_EXCHANGE
def ALGEBRAICALLY_SPANNING : thm := BAlgSpanDepIndep.ALGEBRAICALLY_SPANNING

-- AlgebraicMatroid
def algebraic_matroid : thm := BAlgebraicMatroid.algebraic_matroid
def ALGEBRAIC_MATROID : thm := BAlgebraicMatroid.ALGEBRAIC_MATROID
def ALGEBRAIC_MATROID_INDEPENDENT : thm := BAlgebraicMatroid.ALGEBRAIC_MATROID_INDEPENDENT
def ALGEBRAIC_MATROID_DEPENDENT : thm := BAlgebraicMatroid.ALGEBRAIC_MATROID_DEPENDENT
def ALGEBRAIC_MATROID_SPANNING : thm := BAlgebraicMatroid.ALGEBRAIC_MATROID_SPANNING
def ALGEBRAIC_MATROID_BASIS : thm := BAlgebraicMatroid.ALGEBRAIC_MATROID_BASIS
def TRANSCENDENCE_BASIS_EXISTS : thm := BAlgebraicMatroid.TRANSCENDENCE_BASIS_EXISTS
def ALGEBRAICALLY_SPANNING_CONTAINS_TRANSCENDENCE_BASIS : thm := BAlgebraicMatroid.ALGEBRAICALLY_SPANNING_CONTAINS_TRANSCENDENCE_BASIS
def TRANSCENDENCE_BASES_CARD_EQ : thm := BAlgebraicMatroid.TRANSCENDENCE_BASES_CARD_EQ
def ALGEBRAICALLY_DEPENDENT_MONOMORPHIC_IMAGE : thm := BAlgebraicMatroid.ALGEBRAICALLY_DEPENDENT_MONOMORPHIC_IMAGE

-- AlgebraicTrans
def ALGEBRAIC_OVER_MONOMORPHIC_IMAGE : thm := BAlgebraicTrans.ALGEBRAIC_OVER_MONOMORPHIC_IMAGE
def ALGEBRAIC_SPAN_MONOMORPHIC_IMAGE : thm := BAlgebraicTrans.ALGEBRAIC_SPAN_MONOMORPHIC_IMAGE
def ALGEBRAICALLY_INDEPENDENT_TRANS : thm := BAlgebraicTrans.ALGEBRAICALLY_INDEPENDENT_TRANS
def ALGEBRAICALLY_SPANNING_TRANS : thm := BAlgebraicTrans.ALGEBRAICALLY_SPANNING_TRANS
def TRANSCENDENCE_BASIS_TRANS : thm := BAlgebraicTrans.TRANSCENDENCE_BASIS_TRANS
def TRANSCENDENCE_BASIS_TOWER_LAW : thm := BAlgebraicTrans.TRANSCENDENCE_BASIS_TOWER_LAW
def TRANSCENDENCE_BASIS_CARD_LE_LEFT : thm := BAlgebraicTrans.TRANSCENDENCE_BASIS_CARD_LE_LEFT
def TRANSCENDENCE_BASIS_CARD_LE_RIGHT : thm := BAlgebraicTrans.TRANSCENDENCE_BASIS_CARD_LE_RIGHT
def ALGEBRAIC_EXTENSION_SUBFIELDS_GENERATED : thm := BAlgebraicTrans.ALGEBRAIC_EXTENSION_SUBFIELDS_GENERATED

-- AlgebraicOverExt
def ALGEBRAIC_SPAN_OVER_ALGEBRAIC_EXTENSION : thm := BAlgebraicOverExt.ALGEBRAIC_SPAN_OVER_ALGEBRAIC_EXTENSION
def ALGEBRAICALLY_DEPENDENT_OVER_ALGEBRAIC_EXTENSION : thm := BAlgebraicOverExt.ALGEBRAICALLY_DEPENDENT_OVER_ALGEBRAIC_EXTENSION
def ALGEBRAICALLY_INDEPENDENT_OVER_ALGEBRAIC_EXTENSION : thm := BAlgebraicOverExt.ALGEBRAICALLY_INDEPENDENT_OVER_ALGEBRAIC_EXTENSION
def ALGEBRAICALLY_SPANNING_SPAN : thm := BAlgebraicOverExt.ALGEBRAICALLY_SPANNING_SPAN
def ALGEBRAICALLY_SPANNING_OVER_ALGEBRAIC_EXTENSION : thm := BAlgebraicOverExt.ALGEBRAICALLY_SPANNING_OVER_ALGEBRAIC_EXTENSION
def TRANSCENDENCE_BASIS_OVER_ALGEBRAIC_EXTENSION : thm := BAlgebraicOverExt.TRANSCENDENCE_BASIS_OVER_ALGEBRAIC_EXTENSION
def ALGEBRAICALLY_INDEPENDENT_CARD_LE_SPANNING : thm := BAlgebraicOverExt.ALGEBRAICALLY_INDEPENDENT_CARD_LE_SPANNING
def FINITELY_GENERATED_ALGEBRAICALLY_INDEPENDENT_IMP_FINITE : thm := BAlgebraicOverExt.FINITELY_GENERATED_ALGEBRAICALLY_INDEPENDENT_IMP_FINITE
def TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_SPANNING : thm := BAlgebraicOverExt.TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_SPANNING
def TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_INDEPENDENT : thm := BAlgebraicOverExt.TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_INDEPENDENT

-- TotallyTranscendental
def TOTALLY_TRANSCENDENTAL_EXTENSION : thm := BTotallyTranscendental.TOTALLY_TRANSCENDENTAL_EXTENSION
def TOTALLY_TRANSCENDENTAL_EXTENSION_ALT : thm := BTotallyTranscendental.TOTALLY_TRANSCENDENTAL_EXTENSION_ALT

-- FinitelyGeneratedTransEq
def FINITELY_GENERATED_EXTENSION_TRANS_EQ : thm := BFinitelyGeneratedTransEq.FINITELY_GENERATED_EXTENSION_TRANS_EQ

-- AcfBasic
def algebraically_closed_field : thm := BAcfBasic.algebraically_closed_field
def ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD : thm := BAcfBasic.ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD
def ALGEBRAICALLY_CLOSED_FIELD_ISOMORPHIC_IMAGE : thm := BAcfBasic.ALGEBRAICALLY_CLOSED_FIELD_ISOMORPHIC_IMAGE
def ISOMORPHIC_RING_ALGEBRAICALLY_CLOSED_FIELD : thm := BAcfBasic.ISOMORPHIC_RING_ALGEBRAICALLY_CLOSED_FIELD
def ALGEBRAICALLY_CLOSED_FIELD_IMP_INFINITE : thm := BAcfBasic.ALGEBRAICALLY_CLOSED_FIELD_IMP_INFINITE
def ALGEBRAICALLY_CLOSED_FIELD_NO_PROPER_ALGEBRAIC_EXTENSION : thm := BAcfBasic.ALGEBRAICALLY_CLOSED_FIELD_NO_PROPER_ALGEBRAIC_EXTENSION

-- AcfSplit
def ALGEBRAICALLY_CLOSED_FIELD_EQ_IRREDUCIBLES : thm := BAcfSplit.ALGEBRAICALLY_CLOSED_FIELD_EQ_IRREDUCIBLES
def IRREDUCIBLE_ALGEBRAICALLY_CLOSED_FIELD : thm := BAcfSplit.IRREDUCIBLE_ALGEBRAICALLY_CLOSED_FIELD
def ALGEBRAICALLY_CLOSED_FIELD_DECOMPOSE : thm := BAcfSplit.ALGEBRAICALLY_CLOSED_FIELD_DECOMPOSE
def ALGEBRAICALLY_CLOSED_FIELD_SPLITS : thm := BAcfSplit.ALGEBRAICALLY_CLOSED_FIELD_SPLITS

-- ClosedFieldSplits
def ALGEBRAICALLY_CLOSED_FIELD_EQ_SPLITS_ALT : thm := BClosedFieldSplits.ALGEBRAICALLY_CLOSED_FIELD_EQ_SPLITS_ALT
def ALGEBRAICALLY_CLOSED_FIELD_EQ_SPLITS : thm := BClosedFieldSplits.ALGEBRAICALLY_CLOSED_FIELD_EQ_SPLITS

-- SimpleExtendHom
def SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM : thm := BSimpleExtendHom.SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM

-- ClosureExtendHom
def ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM : thm := BClosureExtendHom.ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM

-- PolySquarefree
def POLY_SQUAREFREE_ROOT_COUNT_EXPLICIT : thm := BPolySquarefree.POLY_SQUAREFREE_ROOT_COUNT_EXPLICIT
def POLY_SQUAREFREE_ROOT_COUNT : thm := BPolySquarefree.POLY_SQUAREFREE_ROOT_COUNT
def POLY_SQUAREFREE_ROOT_COUNT_EQ : thm := BPolySquarefree.POLY_SQUAREFREE_ROOT_COUNT_EQ
def POLY_SQUAREFREE_EXPLICIT_EQ : thm := BPolySquarefree.POLY_SQUAREFREE_EXPLICIT_EQ

-- AlgebraicClosureExistsId
def ALGEBRAIC_CLOSURE_EXISTS_ID : thm := BAlgebraicClosureExistsId.ALGEBRAIC_CLOSURE_EXISTS_ID

-- AlgebraicClosure
def ALGEBRAIC_CLOSURE_EXISTS : thm := BAlgebraicClosure.ALGEBRAIC_CLOSURE_EXISTS
def ALGEBRAIC_CLOSURE_UNIQUE_EXPLICIT : thm := BAlgebraicClosure.ALGEBRAIC_CLOSURE_UNIQUE_EXPLICIT
def ALGEBRAIC_CLOSURE_UNIQUE : thm := BAlgebraicClosure.ALGEBRAIC_CLOSURE_UNIQUE
/-- `needs "Library/fieldtheory.ml"`: already done by importing this module. -/
def ensureFieldTheory : IO Unit := pure ()

end SessionLibrary.FieldTheory
