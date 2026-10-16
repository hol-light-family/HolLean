/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/fieldtheory.ml.                       -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/FieldTheory.lean

  The `unsafe` half of the fieldtheory.ml translation: it supplies HolLibrary.FieldTheory's
  dependencies from Session and SessionLibrary.Matroids, SessionLibrary.RingTheory, builds the bundles once, in order,
  and exports every name under its HOL Light name.  `ensureFieldTheory` is
  `needs "Library/fieldtheory.ml"` (which first does `needs "Library/matroids.ml"`, `needs "Library/ringtheory.ml"`).

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/FieldTheory.lean by tools/fieldtheorydiff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.FieldTheory
import SessionLibrary.Matroids
import SessionLibrary.RingTheory

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.FieldTheory

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems fieldtheory.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.FieldTheory.CoreThms1 where
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
unsafe def core10 (_ : Unit) : HolLibrary.FieldTheory.CoreThms10 where
/-- The core theorems fieldtheory.ml uses. -/
unsafe def core11 (_ : Unit) : HolLibrary.FieldTheory.CoreThms11 where
/-- The core theorems fieldtheory.ml uses. -/
unsafe def core12 (_ : Unit) : HolLibrary.FieldTheory.CoreThms12 where
/-- The core theorems fieldtheory.ml uses. -/
unsafe def core13 (_ : Unit) : HolLibrary.FieldTheory.CoreThms13 where
/-- The core theorems fieldtheory.ml uses. -/
unsafe def core14 (_ : Unit) : HolLibrary.FieldTheory.CoreThms14 where
/-- The core theorems fieldtheory.ml uses. -/
unsafe def core15 (_ : Unit) : HolLibrary.FieldTheory.CoreThms15 where
/-- The core theorems fieldtheory.ml uses. -/
unsafe def core16 (_ : Unit) : HolLibrary.FieldTheory.CoreThms16 where
/-- The core theorems fieldtheory.ml uses. -/
unsafe def core2 (_ : Unit) : HolLibrary.FieldTheory.CoreThms2 where
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
unsafe def core3 (_ : Unit) : HolLibrary.FieldTheory.CoreThms3 where
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
unsafe def core4 (_ : Unit) : HolLibrary.FieldTheory.CoreThms4 where
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
unsafe def core5 (_ : Unit) : HolLibrary.FieldTheory.CoreThms5 where
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
unsafe def core6 (_ : Unit) : HolLibrary.FieldTheory.CoreThms6 where
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
unsafe def core7 (_ : Unit) : HolLibrary.FieldTheory.CoreThms7 where
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
unsafe def core8 (_ : Unit) : HolLibrary.FieldTheory.CoreThms8 where
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
unsafe def core9 (_ : Unit) : HolLibrary.FieldTheory.CoreThms9 where
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
-- @@CORE END

/-- What fieldtheory.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.FieldTheory.FieldTheoryDeps where
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
  core1 := core1 ()
  core2 := core2 ()
  core3 := core3 ()
  core4 := core4 ()
  core5 := core5 ()
  core6 := core6 ()
  core7 := core7 ()
  core8 := core8 ()
  core9 := core9 ()
  core10 := core10 ()
  core11 := core11 ()
  core12 := core12 ()
  core13 := core13 ()
  core14 := core14 ()
  core15 := core15 ()
  core16 := core16 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`, and MATCH_CONV's basic conversions, which HOL
    Light adds loading ind_types.ml), then matroids.ml, ringtheory.ml, which fieldtheory.ml needs. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      let _ ← Session.MATCH_CONV (HolCore.Kernel.mk_var "p" HolCore.Kernel.bool_ty)
      SessionLibrary.Matroids.ensureMatroids
      SessionLibrary.RingTheory.ensureRingTheory
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.FieldTheory: {name}"

/- The bundles, in file order; each forces the one before it. -/

-- @@BUNDLES BEGIN
initialize theSubfields : IO.Ref (Option HolLibrary.FieldTheory.Subfields) ← IO.mkRef none
unsafe def BSubfields : HolLibrary.FieldTheory.Subfields :=
  cached theSubfields "setupSubfields" fun _ => do
    (HolLibrary.FieldTheory.setupSubfields (deps ())).run

initialize theSubfieldGenerated : IO.Ref (Option HolLibrary.FieldTheory.SubfieldGenerated) ← IO.mkRef none
unsafe def BSubfieldGenerated : HolLibrary.FieldTheory.SubfieldGenerated :=
  cached theSubfieldGenerated "setupSubfieldGenerated" fun _ => do
    let _ ← IO.mkRef BSubfields.subfield_of
    (HolLibrary.FieldTheory.setupSubfieldGenerated (deps ()) BSubfields).run

initialize theSubfieldGenerated1 : IO.Ref (Option HolLibrary.FieldTheory.SubfieldGenerated1) ← IO.mkRef none
unsafe def BSubfieldGenerated1 : HolLibrary.FieldTheory.SubfieldGenerated1 :=
  cached theSubfieldGenerated1 "setupSubfieldGenerated1" fun _ => do
    let _ ← IO.mkRef BSubfieldGenerated.subfield_generated
    (HolLibrary.FieldTheory.setupSubfieldGenerated1 (deps ()) BSubfields BSubfieldGenerated).run

initialize theSubfieldGenerated2 : IO.Ref (Option HolLibrary.FieldTheory.SubfieldGenerated2) ← IO.mkRef none
unsafe def BSubfieldGenerated2 : HolLibrary.FieldTheory.SubfieldGenerated2 :=
  cached theSubfieldGenerated2 "setupSubfieldGenerated2" fun _ => do
    let _ ← IO.mkRef BSubfieldGenerated1.SUBSET_CARRIER_SUBFIELD_GENERATED
    (HolLibrary.FieldTheory.setupSubfieldGenerated2 (deps ()) BSubfields BSubfieldGenerated BSubfieldGenerated1).run

initialize theSubfieldQuotients : IO.Ref (Option HolLibrary.FieldTheory.SubfieldQuotients) ← IO.mkRef none
unsafe def BSubfieldQuotients : HolLibrary.FieldTheory.SubfieldQuotients :=
  cached theSubfieldQuotients "setupSubfieldQuotients" fun _ => do
    let _ ← IO.mkRef BSubfieldGenerated2.SUBFIELD_OF_MONOMORPHIC_IMAGE
    (HolLibrary.FieldTheory.setupSubfieldQuotients (deps ()) BSubfields BSubfieldGenerated BSubfieldGenerated1 BSubfieldGenerated2).run

initialize theFieldExtension : IO.Ref (Option HolLibrary.FieldTheory.FieldExtension) ← IO.mkRef none
unsafe def BFieldExtension : HolLibrary.FieldTheory.FieldExtension :=
  cached theFieldExtension "setupFieldExtension" fun _ => do
    let _ ← IO.mkRef BSubfieldQuotients.FIELD_SUBFIELD_GENERATED_UNITS
    (HolLibrary.FieldTheory.setupFieldExtension (deps ()) BSubfields BSubfieldGenerated).run

initialize theRingSpan : IO.Ref (Option HolLibrary.FieldTheory.RingSpan) ← IO.mkRef none
unsafe def BRingSpan : HolLibrary.FieldTheory.RingSpan :=
  cached theRingSpan "setupRingSpan" fun _ => do
    let _ ← IO.mkRef BFieldExtension.field_extension
    (HolLibrary.FieldTheory.setupRingSpan (deps ())).run

initialize theRingMatroid : IO.Ref (Option HolLibrary.FieldTheory.RingMatroid) ← IO.mkRef none
unsafe def BRingMatroid : HolLibrary.FieldTheory.RingMatroid :=
  cached theRingMatroid "setupRingMatroid" fun _ => do
    let _ ← IO.mkRef BRingSpan.ring_span_RULES
    (HolLibrary.FieldTheory.setupRingMatroid (deps ()) BRingSpan).run

initialize theLinearAlgebra : IO.Ref (Option HolLibrary.FieldTheory.LinearAlgebra) ← IO.mkRef none
unsafe def BLinearAlgebra : HolLibrary.FieldTheory.LinearAlgebra :=
  cached theLinearAlgebra "setupLinearAlgebra" fun _ => do
    let _ ← IO.mkRef BRingMatroid.ring_matroid
    (HolLibrary.FieldTheory.setupLinearAlgebra (deps ()) BFieldExtension BRingSpan BRingMatroid).run

initialize theFinitary : IO.Ref (Option HolLibrary.FieldTheory.Finitary) ← IO.mkRef none
unsafe def BFinitary : HolLibrary.FieldTheory.Finitary :=
  cached theFinitary "setupFinitary" fun _ => do
    let _ ← IO.mkRef BLinearAlgebra.ring_dependent
    (HolLibrary.FieldTheory.setupFinitary (deps ()) BSubfields BSubfieldGenerated BRingSpan BRingMatroid BLinearAlgebra).run

initialize theTowerLaw : IO.Ref (Option HolLibrary.FieldTheory.TowerLaw) ← IO.mkRef none
unsafe def BTowerLaw : HolLibrary.FieldTheory.TowerLaw :=
  cached theTowerLaw "setupTowerLaw" fun _ => do
    let _ ← IO.mkRef BFinitary.RING_DEPENDENT_FINITARY
    (HolLibrary.FieldTheory.setupTowerLaw (deps ()) BFieldExtension BRingSpan BLinearAlgebra BFinitary).run

initialize theFiniteExtension : IO.Ref (Option HolLibrary.FieldTheory.FiniteExtension) ← IO.mkRef none
unsafe def BFiniteExtension : HolLibrary.FieldTheory.FiniteExtension :=
  cached theFiniteExtension "setupFiniteExtension" fun _ => do
    let _ ← IO.mkRef BTowerLaw.RING_SPANNING_TRANS
    (HolLibrary.FieldTheory.setupFiniteExtension (deps ()) BSubfieldGenerated BSubfieldGenerated1 BSubfieldGenerated2 BFieldExtension BRingSpan BRingMatroid BLinearAlgebra BFinitary BTowerLaw).run

initialize theAlgebraicExtension : IO.Ref (Option HolLibrary.FieldTheory.AlgebraicExtension) ← IO.mkRef none
unsafe def BAlgebraicExtension : HolLibrary.FieldTheory.AlgebraicExtension :=
  cached theAlgebraicExtension "setupAlgebraicExtension" fun _ => do
    let _ ← IO.mkRef BFiniteExtension.finite_extension
    (HolLibrary.FieldTheory.setupAlgebraicExtension (deps ()) BSubfieldGenerated BSubfieldGenerated1 BSubfieldGenerated2 BSubfieldQuotients BFieldExtension).run

initialize theAlgebraicOverBasics : IO.Ref (Option HolLibrary.FieldTheory.AlgebraicOverBasics) ← IO.mkRef none
unsafe def BAlgebraicOverBasics : HolLibrary.FieldTheory.AlgebraicOverBasics :=
  cached theAlgebraicOverBasics "setupAlgebraicOverBasics" fun _ => do
    let _ ← IO.mkRef BAlgebraicExtension.algebraic_over
    (HolLibrary.FieldTheory.setupAlgebraicOverBasics (deps ()) BFieldExtension BRingSpan BFinitary BFiniteExtension BAlgebraicExtension).run

initialize theAlgebraicExtensionProps : IO.Ref (Option HolLibrary.FieldTheory.AlgebraicExtensionProps) ← IO.mkRef none
unsafe def BAlgebraicExtensionProps : HolLibrary.FieldTheory.AlgebraicExtensionProps :=
  cached theAlgebraicExtensionProps "setupAlgebraicExtensionProps" fun _ => do
    let _ ← IO.mkRef BAlgebraicOverBasics.ALGEBRAIC_OVER_NONMONOMORPHISM
    (HolLibrary.FieldTheory.setupAlgebraicExtensionProps (deps ()) BSubfieldGenerated BFieldExtension BFiniteExtension BAlgebraicExtension BAlgebraicOverBasics).run

initialize theAlgebraicExtMisc : IO.Ref (Option HolLibrary.FieldTheory.AlgebraicExtMisc) ← IO.mkRef none
unsafe def BAlgebraicExtMisc : HolLibrary.FieldTheory.AlgebraicExtMisc :=
  cached theAlgebraicExtMisc "setupAlgebraicExtMisc" fun _ => do
    let _ ← IO.mkRef BAlgebraicExtensionProps.FIELD_SIMPLE_ALGEBRAIC_EXTENSION_GEN
    (HolLibrary.FieldTheory.setupAlgebraicExtMisc (deps ()) BSubfieldQuotients BFieldExtension BFiniteExtension BAlgebraicExtension BAlgebraicOverBasics BAlgebraicExtensionProps).run

initialize theAlgebraicField : IO.Ref (Option HolLibrary.FieldTheory.AlgebraicField) ← IO.mkRef none
unsafe def BAlgebraicField : HolLibrary.FieldTheory.AlgebraicField :=
  cached theAlgebraicField "setupAlgebraicField" fun _ => do
    let _ ← IO.mkRef BAlgebraicExtMisc.ALGEBRAIC_FROM_SUBRING_GENERATED
    (HolLibrary.FieldTheory.setupAlgebraicField (deps ()) BSubfields BSubfieldGenerated BFieldExtension BAlgebraicExtension BAlgebraicOverBasics BAlgebraicExtensionProps BAlgebraicExtMisc).run

initialize theFiniteExt : IO.Ref (Option HolLibrary.FieldTheory.FiniteExt) ← IO.mkRef none
unsafe def BFiniteExt : HolLibrary.FieldTheory.FiniteExt :=
  cached theFiniteExt "setupFiniteExt" fun _ => do
    let _ ← IO.mkRef BAlgebraicField.ALGEBRAIC_OVER_0
    (HolLibrary.FieldTheory.setupFiniteExt (deps ()) BFieldExtension BRingSpan BLinearAlgebra BFinitary BFiniteExtension).run

initialize theAlgDepDefs : IO.Ref (Option HolLibrary.FieldTheory.AlgDepDefs) ← IO.mkRef none
unsafe def BAlgDepDefs : HolLibrary.FieldTheory.AlgDepDefs :=
  cached theAlgDepDefs "setupAlgDepDefs" fun _ => do
    let _ ← IO.mkRef BFiniteExt.FINITE_EQ_FIELD_EXTENSION
    (HolLibrary.FieldTheory.setupAlgDepDefs (deps ()) BSubfieldGenerated BFieldExtension BRingSpan BFinitary BAlgebraicExtension BAlgebraicField).run

initialize theAlgDepSpan : IO.Ref (Option HolLibrary.FieldTheory.AlgDepSpan) ← IO.mkRef none
unsafe def BAlgDepSpan : HolLibrary.FieldTheory.AlgDepSpan :=
  cached theAlgDepSpan "setupAlgDepSpan" fun _ => do
    let _ ← IO.mkRef BAlgDepDefs.algebraically_dependent
    (HolLibrary.FieldTheory.setupAlgDepSpan (deps ()) BSubfieldGenerated BSubfieldGenerated1 BFieldExtension BAlgebraicExtension BAlgebraicExtensionProps BAlgebraicField BAlgDepDefs).run

initialize theAlgSpanDepIndep : IO.Ref (Option HolLibrary.FieldTheory.AlgSpanDepIndep) ← IO.mkRef none
unsafe def BAlgSpanDepIndep : HolLibrary.FieldTheory.AlgSpanDepIndep :=
  cached theAlgSpanDepIndep "setupAlgSpanDepIndep" fun _ => do
    let _ ← IO.mkRef BAlgDepSpan.ALGEBRAIC_SPAN_SPAN
    (HolLibrary.FieldTheory.setupAlgSpanDepIndep (deps ()) BSubfields BSubfieldGenerated BFieldExtension BAlgebraicExtension BAlgebraicExtensionProps BAlgDepDefs BAlgDepSpan).run

initialize theAlgebraicMatroid : IO.Ref (Option HolLibrary.FieldTheory.AlgebraicMatroid) ← IO.mkRef none
unsafe def BAlgebraicMatroid : HolLibrary.FieldTheory.AlgebraicMatroid :=
  cached theAlgebraicMatroid "setupAlgebraicMatroid" fun _ => do
    let _ ← IO.mkRef BAlgSpanDepIndep.ALGEBRAICALLY_DEPENDENT_FINITARY
    (HolLibrary.FieldTheory.setupAlgebraicMatroid (deps ()) BFieldExtension BAlgDepDefs BAlgDepSpan BAlgSpanDepIndep).run

initialize theAlgebraicTrans : IO.Ref (Option HolLibrary.FieldTheory.AlgebraicTrans) ← IO.mkRef none
unsafe def BAlgebraicTrans : HolLibrary.FieldTheory.AlgebraicTrans :=
  cached theAlgebraicTrans "setupAlgebraicTrans" fun _ => do
    let _ ← IO.mkRef BAlgebraicMatroid.algebraic_matroid
    (HolLibrary.FieldTheory.setupAlgebraicTrans (deps ()) BSubfieldGenerated BSubfieldGenerated1 BFieldExtension BAlgebraicExtension BAlgebraicExtensionProps BAlgebraicField BAlgDepDefs BAlgDepSpan BAlgSpanDepIndep BAlgebraicMatroid).run

initialize theAlgebraicOverExt : IO.Ref (Option HolLibrary.FieldTheory.AlgebraicOverExt) ← IO.mkRef none
unsafe def BAlgebraicOverExt : HolLibrary.FieldTheory.AlgebraicOverExt :=
  cached theAlgebraicOverExt "setupAlgebraicOverExt" fun _ => do
    let _ ← IO.mkRef BAlgebraicTrans.ALGEBRAIC_OVER_MONOMORPHIC_IMAGE
    (HolLibrary.FieldTheory.setupAlgebraicOverExt (deps ()) BSubfieldGenerated BFieldExtension BFiniteExtension BAlgebraicExtension BAlgebraicExtMisc BAlgebraicField BAlgDepDefs BAlgSpanDepIndep BAlgebraicMatroid BAlgebraicTrans).run

initialize theTotallyTranscendental : IO.Ref (Option HolLibrary.FieldTheory.TotallyTranscendental) ← IO.mkRef none
unsafe def BTotallyTranscendental : HolLibrary.FieldTheory.TotallyTranscendental :=
  cached theTotallyTranscendental "setupTotallyTranscendental" fun _ => do
    let _ ← IO.mkRef BAlgebraicOverExt.ALGEBRAIC_SPAN_OVER_ALGEBRAIC_EXTENSION
    (HolLibrary.FieldTheory.setupTotallyTranscendental (deps ()) BSubfields BSubfieldGenerated BSubfieldGenerated1 BSubfieldGenerated2 BSubfieldQuotients BFieldExtension BAlgebraicExtension BAlgebraicExtensionProps BAlgebraicField BAlgDepDefs BAlgDepSpan BAlgSpanDepIndep).run

initialize theFinitelyGeneratedTransEq : IO.Ref (Option HolLibrary.FieldTheory.FinitelyGeneratedTransEq) ← IO.mkRef none
unsafe def BFinitelyGeneratedTransEq : HolLibrary.FieldTheory.FinitelyGeneratedTransEq :=
  cached theFinitelyGeneratedTransEq "setupFinitelyGeneratedTransEq" fun _ => do
    let _ ← IO.mkRef BTotallyTranscendental.TOTALLY_TRANSCENDENTAL_EXTENSION
    (HolLibrary.FieldTheory.setupFinitelyGeneratedTransEq (deps ()) BSubfields BSubfieldGenerated BSubfieldGenerated1 BFieldExtension BRingMatroid BLinearAlgebra BFinitary BFiniteExtension BAlgebraicExtension BAlgebraicExtensionProps BAlgebraicExtMisc BAlgDepDefs BAlgDepSpan BAlgSpanDepIndep BAlgebraicMatroid BAlgebraicTrans BAlgebraicOverExt BTotallyTranscendental).run

initialize theAcfBasic : IO.Ref (Option HolLibrary.FieldTheory.AcfBasic) ← IO.mkRef none
unsafe def BAcfBasic : HolLibrary.FieldTheory.AcfBasic :=
  cached theAcfBasic "setupAcfBasic" fun _ => do
    let _ ← IO.mkRef BFinitelyGeneratedTransEq.FINITELY_GENERATED_EXTENSION_TRANS_EQ
    (HolLibrary.FieldTheory.setupAcfBasic (deps ()) BFieldExtension BAlgebraicOverBasics).run

initialize theAcfSplit : IO.Ref (Option HolLibrary.FieldTheory.AcfSplit) ← IO.mkRef none
unsafe def BAcfSplit : HolLibrary.FieldTheory.AcfSplit :=
  cached theAcfSplit "setupAcfSplit" fun _ => do
    let _ ← IO.mkRef BAcfBasic.algebraically_closed_field
    (HolLibrary.FieldTheory.setupAcfSplit (deps ()) BAcfBasic).run

initialize theClosedFieldSplits : IO.Ref (Option HolLibrary.FieldTheory.ClosedFieldSplits) ← IO.mkRef none
unsafe def BClosedFieldSplits : HolLibrary.FieldTheory.ClosedFieldSplits :=
  cached theClosedFieldSplits "setupClosedFieldSplits" fun _ => do
    let _ ← IO.mkRef BAcfSplit.ALGEBRAICALLY_CLOSED_FIELD_EQ_IRREDUCIBLES
    (HolLibrary.FieldTheory.setupClosedFieldSplits (deps ()) BAcfBasic BAcfSplit).run

initialize theSimpleExtendHom : IO.Ref (Option HolLibrary.FieldTheory.SimpleExtendHom) ← IO.mkRef none
unsafe def BSimpleExtendHom : HolLibrary.FieldTheory.SimpleExtendHom :=
  cached theSimpleExtendHom "setupSimpleExtendHom" fun _ => do
    let _ ← IO.mkRef BClosedFieldSplits.ALGEBRAICALLY_CLOSED_FIELD_EQ_SPLITS_ALT
    (HolLibrary.FieldTheory.setupSimpleExtendHom (deps ()) BAcfBasic).run

initialize theClosureExtendHom : IO.Ref (Option HolLibrary.FieldTheory.ClosureExtendHom) ← IO.mkRef none
unsafe def BClosureExtendHom : HolLibrary.FieldTheory.ClosureExtendHom :=
  cached theClosureExtendHom "setupClosureExtendHom" fun _ => do
    let _ ← IO.mkRef BSimpleExtendHom.SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM
    (HolLibrary.FieldTheory.setupClosureExtendHom (deps ()) BSubfields BSubfieldGenerated2 BFieldExtension BAlgebraicExtension BAlgebraicExtensionProps BAcfBasic BSimpleExtendHom).run

initialize thePolySquarefree : IO.Ref (Option HolLibrary.FieldTheory.PolySquarefree) ← IO.mkRef none
unsafe def BPolySquarefree : HolLibrary.FieldTheory.PolySquarefree :=
  cached thePolySquarefree "setupPolySquarefree" fun _ => do
    let _ ← IO.mkRef BClosureExtendHom.ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM
    (HolLibrary.FieldTheory.setupPolySquarefree (deps ()) BAcfBasic BAcfSplit).run

initialize theAlgebraicClosureExistsId : IO.Ref (Option HolLibrary.FieldTheory.AlgebraicClosureExistsId) ← IO.mkRef none
unsafe def BAlgebraicClosureExistsId : HolLibrary.FieldTheory.AlgebraicClosureExistsId :=
  cached theAlgebraicClosureExistsId "setupAlgebraicClosureExistsId" fun _ => do
    let _ ← IO.mkRef BPolySquarefree.POLY_SQUAREFREE_ROOT_COUNT_EXPLICIT
    (HolLibrary.FieldTheory.setupAlgebraicClosureExistsId (deps ()) BFieldExtension BFiniteExtension BAlgebraicExtension BAlgebraicOverBasics BAlgebraicExtensionProps BAlgebraicExtMisc BAcfBasic).run

initialize theAlgebraicClosure : IO.Ref (Option HolLibrary.FieldTheory.AlgebraicClosure) ← IO.mkRef none
unsafe def BAlgebraicClosure : HolLibrary.FieldTheory.AlgebraicClosure :=
  cached theAlgebraicClosure "setupAlgebraicClosure" fun _ => do
    let _ ← IO.mkRef BAlgebraicClosureExistsId.ALGEBRAIC_CLOSURE_EXISTS_ID
    (HolLibrary.FieldTheory.setupAlgebraicClosure (deps ()) BFieldExtension BAlgebraicExtension BAlgebraicOverBasics BAlgebraicExtMisc BAlgebraicField BAcfBasic BClosureExtendHom BAlgebraicClosureExistsId).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Subfields
unsafe def subfield_of : thm := BSubfields.subfield_of
unsafe def SUBFIELD_IMP_SUBRING_OF : thm := BSubfields.SUBFIELD_IMP_SUBRING_OF
unsafe def SUBFIELD_OF_IMP_SUBSET : thm := BSubfields.SUBFIELD_OF_IMP_SUBSET
unsafe def SUBFIELD_OF_IMP_10 : thm := BSubfields.SUBFIELD_OF_IMP_10
unsafe def SUBFIELD_OF_IMP_NONTRIVIAL : thm := BSubfields.SUBFIELD_OF_IMP_NONTRIVIAL
unsafe def IN_SUBFIELD_LINV : thm := BSubfields.IN_SUBFIELD_LINV
unsafe def IN_SUBFIELD_RINV : thm := BSubfields.IN_SUBFIELD_RINV
unsafe def IN_SUBFIELD_INV : thm := BSubfields.IN_SUBFIELD_INV
unsafe def RING_INV_SUBRING_GENERATED : thm := BSubfields.RING_INV_SUBRING_GENERATED
unsafe def SUBFIELD_OF_FIELD_INV : thm := BSubfields.SUBFIELD_OF_FIELD_INV
unsafe def SUBFIELD_OF_INTERS : thm := BSubfields.SUBFIELD_OF_INTERS
unsafe def SUBFIELD_OF_INTER : thm := BSubfields.SUBFIELD_OF_INTER
unsafe def CARRIER_SUBFIELD_OF : thm := BSubfields.CARRIER_SUBFIELD_OF
unsafe def IN_SUBFIELD_0 : thm := BSubfields.IN_SUBFIELD_0
unsafe def IN_SUBFIELD_1 : thm := BSubfields.IN_SUBFIELD_1
unsafe def IN_SUBFIELD_NEG : thm := BSubfields.IN_SUBFIELD_NEG
unsafe def IN_SUBFIELD_ADD : thm := BSubfields.IN_SUBFIELD_ADD
unsafe def IN_SUBFIELD_MUL : thm := BSubfields.IN_SUBFIELD_MUL
unsafe def IN_SUBFIELD_SUB : thm := BSubfields.IN_SUBFIELD_SUB
unsafe def IN_SUBFIELD_POW : thm := BSubfields.IN_SUBFIELD_POW
unsafe def IN_SUBFIELD_SUM : thm := BSubfields.IN_SUBFIELD_SUM
unsafe def IN_SUBFIELD_PRODUCT : thm := BSubfields.IN_SUBFIELD_PRODUCT
unsafe def SUBFIELD_OF_HOMOMORPHIC_EQUALITIES : thm := BSubfields.SUBFIELD_OF_HOMOMORPHIC_EQUALITIES
unsafe def SUBFIELD_OF_FIXPOINTS : thm := BSubfields.SUBFIELD_OF_FIXPOINTS
unsafe def SUBFIELD_OF_SUBRING_QUOTIENTS : thm := BSubfields.SUBFIELD_OF_SUBRING_QUOTIENTS

-- SubfieldGenerated
unsafe def subfield_generated : thm := BSubfieldGenerated.subfield_generated
unsafe def SUBFIELD_GENERATED : thm := BSubfieldGenerated.SUBFIELD_GENERATED
unsafe def CARRIER_SUBFIELD_GENERATED_FIELD : thm := BSubfieldGenerated.CARRIER_SUBFIELD_GENERATED_FIELD
unsafe def CARRIER_SUBFIELD_GENERATED_SUBFIELD : thm := BSubfieldGenerated.CARRIER_SUBFIELD_GENERATED_SUBFIELD
unsafe def RING_CARRIER_SUBFIELD_GENERATED_SUBSET : thm := BSubfieldGenerated.RING_CARRIER_SUBFIELD_GENERATED_SUBSET
unsafe def SUBFIELD_GENERATED_RESTRICT : thm := BSubfieldGenerated.SUBFIELD_GENERATED_RESTRICT
unsafe def SUBFIELD_GENERATED_MONO : thm := BSubfieldGenerated.SUBFIELD_GENERATED_MONO
unsafe def SUBFIELD_GENERATED_MINIMAL : thm := BSubfieldGenerated.SUBFIELD_GENERATED_MINIMAL
unsafe def SUBRING_SUBSET_SUBFIELD_GENERATED : thm := BSubfieldGenerated.SUBRING_SUBSET_SUBFIELD_GENERATED
unsafe def SUBRING_SUBFIELD_GENERATED : thm := BSubfieldGenerated.SUBRING_SUBFIELD_GENERATED
unsafe def SUBFIELD_GENERATED_TRIVIAL : thm := BSubfieldGenerated.SUBFIELD_GENERATED_TRIVIAL
unsafe def SUBRING_EQ_SUBFIELD_GENERATED : thm := BSubfieldGenerated.SUBRING_EQ_SUBFIELD_GENERATED
unsafe def SUBRING_GENERATED_BY_SUBFIELD_GENERATED : thm := BSubfieldGenerated.SUBRING_GENERATED_BY_SUBFIELD_GENERATED
unsafe def SUBFIELD_GENERATED_SUBSET_CARRIER : thm := BSubfieldGenerated.SUBFIELD_GENERATED_SUBSET_CARRIER
unsafe def SUBFIELD_SUBFIELD_GENERATED_ALT : thm := BSubfieldGenerated.SUBFIELD_SUBFIELD_GENERATED_ALT
unsafe def SUBFIELD_SUBFIELD_GENERATED : thm := BSubfieldGenerated.SUBFIELD_SUBFIELD_GENERATED
unsafe def FIELD_SUBFIELD_GENERATED_ALT : thm := BSubfieldGenerated.FIELD_SUBFIELD_GENERATED_ALT
unsafe def FIELD_SUBFIELD_GENERATED_EQ : thm := BSubfieldGenerated.FIELD_SUBFIELD_GENERATED_EQ
unsafe def SUBFIELD_SUBFIELD_GENERATED_EQ : thm := BSubfieldGenerated.SUBFIELD_SUBFIELD_GENERATED_EQ
unsafe def FIELD_SUBFIELD_GENERATED : thm := BSubfieldGenerated.FIELD_SUBFIELD_GENERATED
unsafe def FIELD_SUBFIELD_GENERATED_MONO : thm := BSubfieldGenerated.FIELD_SUBFIELD_GENERATED_MONO
unsafe def SUBFIELD_GENERATED_EQ : thm := BSubfieldGenerated.SUBFIELD_GENERATED_EQ
unsafe def SUBFIELDS_GENERATED_EQ : thm := BSubfieldGenerated.SUBFIELDS_GENERATED_EQ
unsafe def SUBFIELD_GENERATED_SUPERSET : thm := BSubfieldGenerated.SUBFIELD_GENERATED_SUPERSET
unsafe def FINITE_SUBFIELD_GENERATED : thm := BSubfieldGenerated.FINITE_SUBFIELD_GENERATED

-- SubfieldGenerated1
unsafe def SUBSET_CARRIER_SUBFIELD_GENERATED : thm := BSubfieldGenerated1.SUBSET_CARRIER_SUBFIELD_GENERATED
unsafe def SUBFIELD_GENERATED_MINIMAL_EQ : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_MINIMAL_EQ
unsafe def SUBFIELD_GENERATED_RING_CARRIER : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_RING_CARRIER
unsafe def SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET
unsafe def SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED
unsafe def SUBFIELD_GENERATED_REFL : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_REFL
unsafe def SUBFIELD_GENERATED_INC : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_INC
unsafe def SUBFIELD_GENERATED_INC_GEN : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_INC_GEN
unsafe def SUBRING_OF_SUBFIELD_GENERATED_EQ : thm := BSubfieldGenerated1.SUBRING_OF_SUBFIELD_GENERATED_EQ
unsafe def SUBFIELD_OF_SUBFIELD_GENERATED_EQ : thm := BSubfieldGenerated1.SUBFIELD_OF_SUBFIELD_GENERATED_EQ
unsafe def SUBFIELD_OF_SUBFIELD_GENERATED_SUBFIELD_EQ : thm := BSubfieldGenerated1.SUBFIELD_OF_SUBFIELD_GENERATED_SUBFIELD_EQ
unsafe def SUBFIELD_OF_SUBFIELD_GENERATED : thm := BSubfieldGenerated1.SUBFIELD_OF_SUBFIELD_GENERATED
unsafe def SUBFIELD_OF_SUBFIELD_GENERATED_REV : thm := BSubfieldGenerated1.SUBFIELD_OF_SUBFIELD_GENERATED_REV
unsafe def SUBFIELD_GENERATED_IDEMPOT : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_IDEMPOT
unsafe def SUBFIELD_GENERATED_SUBFIELD_GENERATED : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_SUBFIELD_GENERATED
unsafe def SUBRING_GENERATED_SUBFIELD_GENERATED : thm := BSubfieldGenerated1.SUBRING_GENERATED_SUBFIELD_GENERATED
unsafe def TRIVIAL_RING_SUBFIELD_GENERATED : thm := BSubfieldGenerated1.TRIVIAL_RING_SUBFIELD_GENERATED
unsafe def SUBFIELD_GENERATED_UNION_LEFT : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_UNION_LEFT
unsafe def SUBFIELD_GENERATED_UNION_RIGHT : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_UNION_RIGHT
unsafe def SUBFIELD_GENERATED_UNION : thm := BSubfieldGenerated1.SUBFIELD_GENERATED_UNION

-- SubfieldGenerated2
unsafe def SUBFIELD_OF_MONOMORPHIC_IMAGE : thm := BSubfieldGenerated2.SUBFIELD_OF_MONOMORPHIC_IMAGE
unsafe def SUBFIELD_OF_MONOMORPHIC_PREIMAGE : thm := BSubfieldGenerated2.SUBFIELD_OF_MONOMORPHIC_PREIMAGE
unsafe def SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE : thm := BSubfieldGenerated2.SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE
unsafe def RING_SUB_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_SUB_SUBFIELD_GENERATED
unsafe def RING_POW_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_POW_SUBFIELD_GENERATED
unsafe def RING_OF_NUM_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_OF_NUM_SUBFIELD_GENERATED
unsafe def RING_OF_INT_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_OF_INT_SUBFIELD_GENERATED
unsafe def RING_CHAR_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_CHAR_SUBFIELD_GENERATED
unsafe def RING_0_IN_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_0_IN_SUBFIELD_GENERATED
unsafe def RING_1_IN_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_1_IN_SUBFIELD_GENERATED
unsafe def RING_NEG_IN_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_NEG_IN_SUBFIELD_GENERATED
unsafe def RING_ADD_IN_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_ADD_IN_SUBFIELD_GENERATED
unsafe def RING_MUL_IN_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_MUL_IN_SUBFIELD_GENERATED
unsafe def RING_POW_IN_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_POW_IN_SUBFIELD_GENERATED
unsafe def RING_INV_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_INV_SUBFIELD_GENERATED
unsafe def RING_INV_IN_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_INV_IN_SUBFIELD_GENERATED
unsafe def RING_DIV_IN_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.RING_DIV_IN_SUBFIELD_GENERATED
unsafe def SUBFIELD_GENERATED_INDUCT : thm := BSubfieldGenerated2.SUBFIELD_GENERATED_INDUCT
unsafe def POLY_CONST_SUBFIELD_GENERATED : thm := BSubfieldGenerated2.POLY_CONST_SUBFIELD_GENERATED
unsafe def POLY_SUBFIELD_GENERATED_CLAUSES : thm := BSubfieldGenerated2.POLY_SUBFIELD_GENERATED_CLAUSES

-- SubfieldQuotients
unsafe def FIELD_SUBFIELD_GENERATED_UNITS : thm := BSubfieldQuotients.FIELD_SUBFIELD_GENERATED_UNITS
unsafe def SUBFIELD_GENERATED_SUBRING_QUOTIENTS : thm := BSubfieldQuotients.SUBFIELD_GENERATED_SUBRING_QUOTIENTS
unsafe def RING_CARRIER_SUBFIELD_GENERATED_SUBRING_QUOTIENTS : thm := BSubfieldQuotients.RING_CARRIER_SUBFIELD_GENERATED_SUBRING_QUOTIENTS
unsafe def SUBFIELD_GENERATED_QUOTIENTS : thm := BSubfieldQuotients.SUBFIELD_GENERATED_QUOTIENTS
unsafe def FINITE_SUBSET_SUBFIELD_GENERATED_DENOMINATOR : thm := BSubfieldQuotients.FINITE_SUBSET_SUBFIELD_GENERATED_DENOMINATOR
unsafe def POLY_OVER_SUBFIELD_GENERATED_DENOMINATOR : thm := BSubfieldQuotients.POLY_OVER_SUBFIELD_GENERATED_DENOMINATOR
unsafe def IN_SUBFIELD_GENERATED_FINITARY : thm := BSubfieldQuotients.IN_SUBFIELD_GENERATED_FINITARY
unsafe def PRIME_SUBFIELD_MINIMAL : thm := BSubfieldQuotients.PRIME_SUBFIELD_MINIMAL
unsafe def PRIME_SUBFIELD_EQ_SUBRING : thm := BSubfieldQuotients.PRIME_SUBFIELD_EQ_SUBRING
unsafe def FROBENIUS_FIXED_FIELD : thm := BSubfieldQuotients.FROBENIUS_FIXED_FIELD

-- FieldExtension
unsafe def field_extension : thm := BFieldExtension.field_extension
unsafe def FIELD_EXTENSION_IMP_MONOMORPHISM : thm := BFieldExtension.FIELD_EXTENSION_IMP_MONOMORPHISM
unsafe def FIELD_EXTENSION_IMP_HOMOMORPHISM : thm := BFieldExtension.FIELD_EXTENSION_IMP_HOMOMORPHISM
unsafe def FIELD_EXTENSION_IMP_SUBSET : thm := BFieldExtension.FIELD_EXTENSION_IMP_SUBSET
unsafe def FIELD_EXTENSION_CARRIER : thm := BFieldExtension.FIELD_EXTENSION_CARRIER
unsafe def FIELD_EXTENSION_FROM_SUBRING_GENERATED : thm := BFieldExtension.FIELD_EXTENSION_FROM_SUBRING_GENERATED
unsafe def FIELD_EXTENSION_EQ : thm := BFieldExtension.FIELD_EXTENSION_EQ
unsafe def FIELD_EXTENSION_REFL : thm := BFieldExtension.FIELD_EXTENSION_REFL
unsafe def FIELD_EXTENSION_TRANS : thm := BFieldExtension.FIELD_EXTENSION_TRANS
unsafe def FIELD_EXTENSION_TRANS_I : thm := BFieldExtension.FIELD_EXTENSION_TRANS_I
unsafe def FIELD_EXTENSION_ISOMORPHISM : thm := BFieldExtension.FIELD_EXTENSION_ISOMORPHISM
unsafe def FIELD_EXTENSION_SUBRING_GENERATED : thm := BFieldExtension.FIELD_EXTENSION_SUBRING_GENERATED
unsafe def FIELD_EXTENSION_INTO_SUBRING_GENERATED : thm := BFieldExtension.FIELD_EXTENSION_INTO_SUBRING_GENERATED
unsafe def FIELD_EXTENSION_INTO_SUBFIELD_GENERATED : thm := BFieldExtension.FIELD_EXTENSION_INTO_SUBFIELD_GENERATED
unsafe def KRONECKER_FIELD_EXTENSION : thm := BFieldExtension.KRONECKER_FIELD_EXTENSION
unsafe def KRONECKER_SIMPLE_FIELD_EXTENSION : thm := BFieldExtension.KRONECKER_SIMPLE_FIELD_EXTENSION
unsafe def COPRIME_POLY_NO_COMMON_ROOT : thm := BFieldExtension.COPRIME_POLY_NO_COMMON_ROOT
unsafe def COPRIME_POLY_NO_COMMON_ROOT_I : thm := BFieldExtension.COPRIME_POLY_NO_COMMON_ROOT_I

-- RingSpan
unsafe def ring_span_RULES : thm := BRingSpan.ring_span_RULES
unsafe def ring_span_INDUCT : thm := BRingSpan.ring_span_INDUCT
unsafe def ring_span_CASES : thm := BRingSpan.ring_span_CASES
unsafe def RING_SPAN_0 : thm := BRingSpan.RING_SPAN_0
unsafe def RING_SPAN_INC : thm := BRingSpan.RING_SPAN_INC
unsafe def RING_SPAN_ADD : thm := BRingSpan.RING_SPAN_ADD
unsafe def RING_SPAN_MUL : thm := BRingSpan.RING_SPAN_MUL
unsafe def RING_SPAN_SUBSET : thm := BRingSpan.RING_SPAN_SUBSET
unsafe def RING_SPAN_SUPERSET_GEN : thm := BRingSpan.RING_SPAN_SUPERSET_GEN
unsafe def RING_SPAN_SUPERSET : thm := BRingSpan.RING_SPAN_SUPERSET
unsafe def RING_SPAN_SUPERSET_EQ : thm := BRingSpan.RING_SPAN_SUPERSET_EQ
unsafe def RING_SPAN_MONO : thm := BRingSpan.RING_SPAN_MONO
unsafe def SUBSET_RING_SPAN : thm := BRingSpan.SUBSET_RING_SPAN
unsafe def RING_SPAN_RESTRICT : thm := BRingSpan.RING_SPAN_RESTRICT
unsafe def RING_SPAN_SPAN : thm := BRingSpan.RING_SPAN_SPAN
unsafe def RING_SPAN_FINITARY : thm := BRingSpan.RING_SPAN_FINITARY
unsafe def RING_SPAN_NONEMPTY : thm := BRingSpan.RING_SPAN_NONEMPTY
unsafe def RING_SPAN_SELF : thm := BRingSpan.RING_SPAN_SELF
unsafe def RING_SPAN_EMPTY : thm := BRingSpan.RING_SPAN_EMPTY
unsafe def RING_SPAN_NEG : thm := BRingSpan.RING_SPAN_NEG
unsafe def RING_SPAN_SUB : thm := BRingSpan.RING_SPAN_SUB
unsafe def RING_SPAN_SUM : thm := BRingSpan.RING_SPAN_SUM
unsafe def RING_SPAN_UNION : thm := BRingSpan.RING_SPAN_UNION
unsafe def RING_SPAN_SING : thm := BRingSpan.RING_SPAN_SING
unsafe def RING_SPAN_EXCHANGE : thm := BRingSpan.RING_SPAN_EXCHANGE
unsafe def RING_SPAN_FINITE : thm := BRingSpan.RING_SPAN_FINITE
unsafe def RING_SPAN_HOMOMORPHIC_IMAGE : thm := BRingSpan.RING_SPAN_HOMOMORPHIC_IMAGE

-- RingMatroid
unsafe def ring_matroid : thm := BRingMatroid.ring_matroid
unsafe def RING_MATROID : thm := BRingMatroid.RING_MATROID

-- LinearAlgebra
unsafe def ring_dependent : thm := BLinearAlgebra.ring_dependent
unsafe def ring_independent : thm := BLinearAlgebra.ring_independent
unsafe def ring_spanning : thm := BLinearAlgebra.ring_spanning
unsafe def ring_basis : thm := BLinearAlgebra.ring_basis
unsafe def RING_DEPENDENT_IMP_SUBSET : thm := BLinearAlgebra.RING_DEPENDENT_IMP_SUBSET
unsafe def RING_INDEPENDENT_IMP_SUBSET : thm := BLinearAlgebra.RING_INDEPENDENT_IMP_SUBSET
unsafe def RING_SPANNING_IMP_SUBSET : thm := BLinearAlgebra.RING_SPANNING_IMP_SUBSET
unsafe def RING_BASIS_IMP_SUBSET : thm := BLinearAlgebra.RING_BASIS_IMP_SUBSET
unsafe def RING_MATROID_INDEPENDENT : thm := BLinearAlgebra.RING_MATROID_INDEPENDENT
unsafe def RING_MATROID_SPANNING : thm := BLinearAlgebra.RING_MATROID_SPANNING
unsafe def RING_MATROID_BASIS : thm := BLinearAlgebra.RING_MATROID_BASIS
unsafe def RING_BASIS_EXISTS : thm := BLinearAlgebra.RING_BASIS_EXISTS
unsafe def RING_SPANNING_CONTAINS_BASIS : thm := BLinearAlgebra.RING_SPANNING_CONTAINS_BASIS
unsafe def RING_BASES_CARD_EQ : thm := BLinearAlgebra.RING_BASES_CARD_EQ
unsafe def RING_SPANNING_ALT : thm := BLinearAlgebra.RING_SPANNING_ALT
unsafe def RING_SPANNING_IMP_NONEMPTY : thm := BLinearAlgebra.RING_SPANNING_IMP_NONEMPTY
unsafe def RING_INDEPENDENT_EMPTY : thm := BLinearAlgebra.RING_INDEPENDENT_EMPTY
unsafe def RING_INDEPENDENT_NONZERO : thm := BLinearAlgebra.RING_INDEPENDENT_NONZERO
unsafe def RING_DEPENDENT_MONO : thm := BLinearAlgebra.RING_DEPENDENT_MONO
unsafe def RING_INDEPENDENT_MONO : thm := BLinearAlgebra.RING_INDEPENDENT_MONO

-- Finitary
unsafe def RING_DEPENDENT_FINITARY : thm := BFinitary.RING_DEPENDENT_FINITARY
unsafe def RING_INDEPENDENT_FINITARY : thm := BFinitary.RING_INDEPENDENT_FINITARY
unsafe def RING_INDEPENDENT_LE_SPAN : thm := BFinitary.RING_INDEPENDENT_LE_SPAN
unsafe def RING_DEPENDENT_FINITE : thm := BFinitary.RING_DEPENDENT_FINITE
unsafe def RING_INDEPENDENT_FINITE : thm := BFinitary.RING_INDEPENDENT_FINITE
unsafe def RING_INDEPENDENT_FINITE_EQ : thm := BFinitary.RING_INDEPENDENT_FINITE_EQ
unsafe def RING_DEPENDENT_SPAN_IMAGE : thm := BFinitary.RING_DEPENDENT_SPAN_IMAGE
unsafe def RING_SPAN_SUBSET_SUBRING_GENERATED : thm := BFinitary.RING_SPAN_SUBSET_SUBRING_GENERATED
unsafe def RING_SPAN_SUBSET_SUBFIELD_GENERATED : thm := BFinitary.RING_SPAN_SUBSET_SUBFIELD_GENERATED
unsafe def RING_INDEPENDENT_INSERT : thm := BFinitary.RING_INDEPENDENT_INSERT
unsafe def RING_INDEPENDENT_CARD_LE_SPANNING : thm := BFinitary.RING_INDEPENDENT_CARD_LE_SPANNING

-- TowerLaw
unsafe def RING_SPANNING_TRANS : thm := BTowerLaw.RING_SPANNING_TRANS
unsafe def RING_INDEPENDENT_PRODUCTS : thm := BTowerLaw.RING_INDEPENDENT_PRODUCTS
unsafe def RING_INDEPENDENT_TRANS : thm := BTowerLaw.RING_INDEPENDENT_TRANS
unsafe def RING_BASIS_TRANS : thm := BTowerLaw.RING_BASIS_TRANS
unsafe def FIELD_EXTENSION_TOWER_LAW : thm := BTowerLaw.FIELD_EXTENSION_TOWER_LAW

-- FiniteExtension
unsafe def finite_extension : thm := BFiniteExtension.finite_extension
unsafe def RING_MATROID_FINITE_DIMENSIONAL : thm := BFiniteExtension.RING_MATROID_FINITE_DIMENSIONAL
unsafe def FINITE_IMP_FIELD_EXTENSION : thm := BFiniteExtension.FINITE_IMP_FIELD_EXTENSION
unsafe def FINITE_EXTENSION_RING_MATROID : thm := BFiniteExtension.FINITE_EXTENSION_RING_MATROID
unsafe def FINITE_EXTENSION : thm := BFiniteExtension.FINITE_EXTENSION
unsafe def FINITE_EXTENSION_SPANNING : thm := BFiniteExtension.FINITE_EXTENSION_SPANNING
unsafe def FINITE_EXTENSION_BASIS : thm := BFiniteExtension.FINITE_EXTENSION_BASIS
unsafe def FINITE_EXTENSION_ANY : thm := BFiniteExtension.FINITE_EXTENSION_ANY
unsafe def FINITE_EXTENSION_ISOMORPHISM : thm := BFiniteExtension.FINITE_EXTENSION_ISOMORPHISM
unsafe def FINITE_EXTENSION_TRANS : thm := BFiniteExtension.FINITE_EXTENSION_TRANS
unsafe def FINITE_EXTENSION_TRANS_EQ : thm := BFiniteExtension.FINITE_EXTENSION_TRANS_EQ
unsafe def finitely_generated_extension : thm := BFiniteExtension.finitely_generated_extension
unsafe def FINITELY_GENERATED_IMP_FIELD_EXTENSION : thm := BFiniteExtension.FINITELY_GENERATED_IMP_FIELD_EXTENSION
unsafe def FINITE_IMP_FINITELY_GENERATED_EXTENSION : thm := BFiniteExtension.FINITE_IMP_FINITELY_GENERATED_EXTENSION
unsafe def FINITELY_GENERATED_EXTENSION : thm := BFiniteExtension.FINITELY_GENERATED_EXTENSION
unsafe def FINITELY_GENERATED_EXTENSION_TRANS : thm := BFiniteExtension.FINITELY_GENERATED_EXTENSION_TRANS

-- AlgebraicExtension
unsafe def algebraic_over : thm := BAlgebraicExtension.algebraic_over
unsafe def transcendental_over : thm := BAlgebraicExtension.transcendental_over
unsafe def algebraic_extension : thm := BAlgebraicExtension.algebraic_extension
unsafe def ALGEBRAIC_OVER : thm := BAlgebraicExtension.ALGEBRAIC_OVER
unsafe def ALGEBRAIC_IMP_FIELD_EXTENSION : thm := BAlgebraicExtension.ALGEBRAIC_IMP_FIELD_EXTENSION
unsafe def ALGEBRAIC_OVER_ALT : thm := BAlgebraicExtension.ALGEBRAIC_OVER_ALT
unsafe def ALGEBRAIC_OVER_IN_CARRIER : thm := BAlgebraicExtension.ALGEBRAIC_OVER_IN_CARRIER
unsafe def TRANSCENDENTAL_OVER_IN_CARRIER : thm := BAlgebraicExtension.TRANSCENDENTAL_OVER_IN_CARRIER
unsafe def ALGEBRAIC_OVER_IMAGE_GEN : thm := BAlgebraicExtension.ALGEBRAIC_OVER_IMAGE_GEN
unsafe def ALGEBRAIC_OVER_IMAGE : thm := BAlgebraicExtension.ALGEBRAIC_OVER_IMAGE
unsafe def ALGEBRAIC_OVER_IMAGE_SUBSET : thm := BAlgebraicExtension.ALGEBRAIC_OVER_IMAGE_SUBSET
unsafe def ALGEBRAIC_OVER_REFL : thm := BAlgebraicExtension.ALGEBRAIC_OVER_REFL
unsafe def ALGEBRAIC_OVER_SUBRING_GENERATED : thm := BAlgebraicExtension.ALGEBRAIC_OVER_SUBRING_GENERATED
unsafe def ALGEBRAIC_OVER_SUBFIELD_GENERATED : thm := BAlgebraicExtension.ALGEBRAIC_OVER_SUBFIELD_GENERATED
unsafe def ALGEBRAIC_OVER_SUBRING_GENERATED_MONO : thm := BAlgebraicExtension.ALGEBRAIC_OVER_SUBRING_GENERATED_MONO
unsafe def ALGEBRAIC_OVER_SUBFIELD_SUBRING_GENERATED : thm := BAlgebraicExtension.ALGEBRAIC_OVER_SUBFIELD_SUBRING_GENERATED

-- AlgebraicOverBasics
unsafe def ALGEBRAIC_OVER_NONMONOMORPHISM : thm := BAlgebraicOverBasics.ALGEBRAIC_OVER_NONMONOMORPHISM
unsafe def ALGEBRAIC_EXTENSION : thm := BAlgebraicOverBasics.ALGEBRAIC_EXTENSION
unsafe def ALGEBRAIC_EXTENSION_ALT : thm := BAlgebraicOverBasics.ALGEBRAIC_EXTENSION_ALT
unsafe def ALGEBRAIC_OVER_EQ : thm := BAlgebraicOverBasics.ALGEBRAIC_OVER_EQ
unsafe def ALGEBRAIC_OVER_EQ_EQ : thm := BAlgebraicOverBasics.ALGEBRAIC_OVER_EQ_EQ
unsafe def ALGEBRAIC_EXTENSION_EQ : thm := BAlgebraicOverBasics.ALGEBRAIC_EXTENSION_EQ
unsafe def FINITE_IMP_ALGEBRAIC_EXTENSION_EXPLICIT : thm := BAlgebraicOverBasics.FINITE_IMP_ALGEBRAIC_EXTENSION_EXPLICIT
unsafe def FINITE_IMP_ALGEBRAIC_EXTENSION : thm := BAlgebraicOverBasics.FINITE_IMP_ALGEBRAIC_EXTENSION
unsafe def RING_SIMPLE_EXTENSION_SPAN : thm := BAlgebraicOverBasics.RING_SIMPLE_EXTENSION_SPAN
unsafe def RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN : thm := BAlgebraicOverBasics.RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN

-- AlgebraicExtensionProps
unsafe def FIELD_SIMPLE_ALGEBRAIC_EXTENSION_GEN : thm := BAlgebraicExtensionProps.FIELD_SIMPLE_ALGEBRAIC_EXTENSION_GEN
unsafe def FIELD_SIMPLE_ALGEBRAIC_EXTENSION_EQ : thm := BAlgebraicExtensionProps.FIELD_SIMPLE_ALGEBRAIC_EXTENSION_EQ
unsafe def FIELD_SIMPLE_ALGEBRAIC_EXTENSION : thm := BAlgebraicExtensionProps.FIELD_SIMPLE_ALGEBRAIC_EXTENSION
unsafe def FINITE_SIMPLE_ALGEBRAIC_EXTENSION : thm := BAlgebraicExtensionProps.FINITE_SIMPLE_ALGEBRAIC_EXTENSION
unsafe def ALGEBRAIC_OVER_FROM_MONOMORPHIC_IMAGE : thm := BAlgebraicExtensionProps.ALGEBRAIC_OVER_FROM_MONOMORPHIC_IMAGE
unsafe def ALGEBRAIC_OVER_ISOMORPHIC_IMAGE : thm := BAlgebraicExtensionProps.ALGEBRAIC_OVER_ISOMORPHIC_IMAGE
unsafe def ALGEBRAIC_OVER_RANGE : thm := BAlgebraicExtensionProps.ALGEBRAIC_OVER_RANGE
unsafe def ALGEBRAIC_OVER_FIELD_EXTENSION : thm := BAlgebraicExtensionProps.ALGEBRAIC_OVER_FIELD_EXTENSION
unsafe def FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION : thm := BAlgebraicExtensionProps.FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION
unsafe def FINITE_EQ_FINITELY_GENERATED_ALGEBRAIC_EXTENSION : thm := BAlgebraicExtensionProps.FINITE_EQ_FINITELY_GENERATED_ALGEBRAIC_EXTENSION

-- AlgebraicExtMisc
unsafe def ALGEBRAIC_FROM_SUBRING_GENERATED : thm := BAlgebraicExtMisc.ALGEBRAIC_FROM_SUBRING_GENERATED
unsafe def ALGEBRAIC_EXTENSION_ISOMORPHISM : thm := BAlgebraicExtMisc.ALGEBRAIC_EXTENSION_ISOMORPHISM
unsafe def ALGEBRAIC_EXTENSION_REFL : thm := BAlgebraicExtMisc.ALGEBRAIC_EXTENSION_REFL
unsafe def ALGEBRAIC_EXTENSION_TRANS : thm := BAlgebraicExtMisc.ALGEBRAIC_EXTENSION_TRANS
unsafe def ALGEBRAIC_EXTENSION_TRANS_EQ : thm := BAlgebraicExtMisc.ALGEBRAIC_EXTENSION_TRANS_EQ
unsafe def CARD_LE_ALGEBRAIC_EXTENSION : thm := BAlgebraicExtMisc.CARD_LE_ALGEBRAIC_EXTENSION
unsafe def CARD_EQ_ALGEBRAIC_EXTENSION : thm := BAlgebraicExtMisc.CARD_EQ_ALGEBRAIC_EXTENSION
unsafe def RING_AUTOMORPHISM_OF_ALGEBRAIC_EXTENSION : thm := BAlgebraicExtMisc.RING_AUTOMORPHISM_OF_ALGEBRAIC_EXTENSION
unsafe def RING_AUTOMORPHISM_FROBENIUS_GEN : thm := BAlgebraicExtMisc.RING_AUTOMORPHISM_FROBENIUS_GEN

-- AlgebraicField
unsafe def ALGEBRAIC_OVER_0 : thm := BAlgebraicField.ALGEBRAIC_OVER_0
unsafe def ALGEBRAIC_OVER_1 : thm := BAlgebraicField.ALGEBRAIC_OVER_1
unsafe def ALGEBRAIC_OVER_NEG : thm := BAlgebraicField.ALGEBRAIC_OVER_NEG
unsafe def ALGEBRAIC_OVER_INV : thm := BAlgebraicField.ALGEBRAIC_OVER_INV
unsafe def ALGEBRAIC_OVER_ADD : thm := BAlgebraicField.ALGEBRAIC_OVER_ADD
unsafe def ALGEBRAIC_OVER_MUL : thm := BAlgebraicField.ALGEBRAIC_OVER_MUL
unsafe def ALGEBRAIC_OVER_SUB : thm := BAlgebraicField.ALGEBRAIC_OVER_SUB
unsafe def ALGEBRAIC_OVER_DIV : thm := BAlgebraicField.ALGEBRAIC_OVER_DIV
unsafe def ALGEBRAIC_OVER_POW : thm := BAlgebraicField.ALGEBRAIC_OVER_POW
unsafe def SUBRING_OF_ALGEBRAIC_OVER : thm := BAlgebraicField.SUBRING_OF_ALGEBRAIC_OVER
unsafe def SUBFIELD_OF_ALGEBRAIC_OVER : thm := BAlgebraicField.SUBFIELD_OF_ALGEBRAIC_OVER
unsafe def ALGEBRAIC_OVER_SUBFIELD_GENERATED_ALGEBRAIC : thm := BAlgebraicField.ALGEBRAIC_OVER_SUBFIELD_GENERATED_ALGEBRAIC
unsafe def FIELD_ALGEBRAIC_EXTENSION : thm := BAlgebraicField.FIELD_ALGEBRAIC_EXTENSION
unsafe def SUBFIELD_OF_ALGEBRAIC_EXTENSION : thm := BAlgebraicField.SUBFIELD_OF_ALGEBRAIC_EXTENSION
unsafe def FIELD_ALGEBRAIC_OVER : thm := BAlgebraicField.FIELD_ALGEBRAIC_OVER
unsafe def SUBRING_SUBFIELD_ALGEBRAIC_OVER : thm := BAlgebraicField.SUBRING_SUBFIELD_ALGEBRAIC_OVER
unsafe def ALGEBRAIC_OVER_TRANS : thm := BAlgebraicField.ALGEBRAIC_OVER_TRANS
unsafe def ALGEBRAIC_OVER_ALGEBRAIC_EXTENSION : thm := BAlgebraicField.ALGEBRAIC_OVER_ALGEBRAIC_EXTENSION

-- FiniteExt
unsafe def FINITE_EQ_FIELD_EXTENSION : thm := BFiniteExt.FINITE_EQ_FIELD_EXTENSION
unsafe def HAS_SIZE_FINITE_EXTENSION : thm := BFiniteExt.HAS_SIZE_FINITE_EXTENSION
unsafe def FINITE_FINITE_FIELD_EXTENSION : thm := BFiniteExt.FINITE_FINITE_FIELD_EXTENSION
unsafe def CARD_FINITE_EXTENSION : thm := BFiniteExt.CARD_FINITE_EXTENSION
unsafe def FIELD_EXTENSION_FROM_PRIME_SUBRING : thm := BFiniteExt.FIELD_EXTENSION_FROM_PRIME_SUBRING
unsafe def FINITE_INTEGRAL_DOMAIN_SIZE : thm := BFiniteExt.FINITE_INTEGRAL_DOMAIN_SIZE

-- AlgDepDefs
unsafe def algebraically_dependent : thm := BAlgDepDefs.algebraically_dependent
unsafe def algebraically_independent : thm := BAlgDepDefs.algebraically_independent
unsafe def algebraic_span : thm := BAlgDepDefs.algebraic_span
unsafe def algebraically_spanning : thm := BAlgDepDefs.algebraically_spanning
unsafe def transcendence_basis : thm := BAlgDepDefs.transcendence_basis
unsafe def ALGEBRAICALLY_DEPENDENT_IMP_SUBSET : thm := BAlgDepDefs.ALGEBRAICALLY_DEPENDENT_IMP_SUBSET
unsafe def ALGEBRAICALLY_INDEPENDENT_IMP_SUBSET : thm := BAlgDepDefs.ALGEBRAICALLY_INDEPENDENT_IMP_SUBSET
unsafe def TRANSCENDENCE_BASIS_IMP_SUBSET : thm := BAlgDepDefs.TRANSCENDENCE_BASIS_IMP_SUBSET
unsafe def ALGEBRAICALLY_DEPENDENT_ALT : thm := BAlgDepDefs.ALGEBRAICALLY_DEPENDENT_ALT
unsafe def ALGEBRAIC_SPAN : thm := BAlgDepDefs.ALGEBRAIC_SPAN
unsafe def ALGEBRAIC_SPAN_FIELD : thm := BAlgDepDefs.ALGEBRAIC_SPAN_FIELD
unsafe def ALGEBRAIC_SPAN_RANGE : thm := BAlgDepDefs.ALGEBRAIC_SPAN_RANGE
unsafe def ALGEBRAIC_SPAN_RESTRICT : thm := BAlgDepDefs.ALGEBRAIC_SPAN_RESTRICT
unsafe def ALGEBRAIC_SPAN_SUBSET : thm := BAlgDepDefs.ALGEBRAIC_SPAN_SUBSET
unsafe def RING_SPAN_SUBSET_ALGEBRAIC_SPAN : thm := BAlgDepDefs.RING_SPAN_SUBSET_ALGEBRAIC_SPAN
unsafe def ALGEBRAIC_SPAN_SUPERSET : thm := BAlgDepDefs.ALGEBRAIC_SPAN_SUPERSET
unsafe def ALGEBRAIC_SPAN_MONO : thm := BAlgDepDefs.ALGEBRAIC_SPAN_MONO
unsafe def ALGEBRAIC_EXTENSION_SUBFIELD_GENERATED_ALGEBRAIC : thm := BAlgDepDefs.ALGEBRAIC_EXTENSION_SUBFIELD_GENERATED_ALGEBRAIC
unsafe def ALGEBRAIC_EXTENSION_SUBRING_GENERATED_ALGEBRAIC : thm := BAlgDepDefs.ALGEBRAIC_EXTENSION_SUBRING_GENERATED_ALGEBRAIC

-- AlgDepSpan
unsafe def ALGEBRAIC_SPAN_SPAN : thm := BAlgDepSpan.ALGEBRAIC_SPAN_SPAN
unsafe def ALGEBRAIC_SPAN_FINITARY : thm := BAlgDepSpan.ALGEBRAIC_SPAN_FINITARY
unsafe def ALGEBRAIC_SPAN_EMPTY : thm := BAlgDepSpan.ALGEBRAIC_SPAN_EMPTY
unsafe def ALGEBRAICALLY_INDEPENDENT_EMPTY : thm := BAlgDepSpan.ALGEBRAICALLY_INDEPENDENT_EMPTY
unsafe def ALGEBRAICALLY_DEPENDENT_SING : thm := BAlgDepSpan.ALGEBRAICALLY_DEPENDENT_SING
unsafe def ALGEBRAICALLY_INDEPENDENT_SING : thm := BAlgDepSpan.ALGEBRAICALLY_INDEPENDENT_SING
unsafe def ALGEBRAICALLY_DEPENDENT_MONO : thm := BAlgDepSpan.ALGEBRAICALLY_DEPENDENT_MONO
unsafe def ALGEBRAICALLY_DEPENDENT_OVER_SUBRING_GENERATED_MONO : thm := BAlgDepSpan.ALGEBRAICALLY_DEPENDENT_OVER_SUBRING_GENERATED_MONO
unsafe def ALGEBRAICALLY_INDEPENDENT_MONO : thm := BAlgDepSpan.ALGEBRAICALLY_INDEPENDENT_MONO
unsafe def ALGEBRAICALLY_INDEPENDENT_OVER_SUBRING_GENERATED_MONO : thm := BAlgDepSpan.ALGEBRAICALLY_INDEPENDENT_OVER_SUBRING_GENERATED_MONO
unsafe def ALGEBRAICALLY_INDEPENDENT_IMP_TRANSCENDENTAL : thm := BAlgDepSpan.ALGEBRAICALLY_INDEPENDENT_IMP_TRANSCENDENTAL
unsafe def ALGEBRAICALLY_INDEPENDENT_IMP_DISJOINT : thm := BAlgDepSpan.ALGEBRAICALLY_INDEPENDENT_IMP_DISJOINT

-- AlgSpanDepIndep
unsafe def ALGEBRAICALLY_DEPENDENT_FINITARY : thm := BAlgSpanDepIndep.ALGEBRAICALLY_DEPENDENT_FINITARY
unsafe def RING_MONOMORPHISM_POLY_EXTEND : thm := BAlgSpanDepIndep.RING_MONOMORPHISM_POLY_EXTEND
unsafe def ALGEBRAICALLY_DEPENDENT_FROM_INSERT : thm := BAlgSpanDepIndep.ALGEBRAICALLY_DEPENDENT_FROM_INSERT
unsafe def ALGEBRAICALLY_DEPENDENT_INSERT : thm := BAlgSpanDepIndep.ALGEBRAICALLY_DEPENDENT_INSERT
unsafe def ALGEBRAICALLY_INDEPENDENT_INSERT : thm := BAlgSpanDepIndep.ALGEBRAICALLY_INDEPENDENT_INSERT
unsafe def ALGEBRAICALLY_DEPENDENT_SPAN : thm := BAlgSpanDepIndep.ALGEBRAICALLY_DEPENDENT_SPAN
unsafe def ALGEBRAICALLY_INDEPENDENT_SPAN : thm := BAlgSpanDepIndep.ALGEBRAICALLY_INDEPENDENT_SPAN
unsafe def ALGEBRAIC_SPAN_EXCHANGE : thm := BAlgSpanDepIndep.ALGEBRAIC_SPAN_EXCHANGE
unsafe def ALGEBRAICALLY_SPANNING : thm := BAlgSpanDepIndep.ALGEBRAICALLY_SPANNING

-- AlgebraicMatroid
unsafe def algebraic_matroid : thm := BAlgebraicMatroid.algebraic_matroid
unsafe def ALGEBRAIC_MATROID : thm := BAlgebraicMatroid.ALGEBRAIC_MATROID
unsafe def ALGEBRAIC_MATROID_INDEPENDENT : thm := BAlgebraicMatroid.ALGEBRAIC_MATROID_INDEPENDENT
unsafe def ALGEBRAIC_MATROID_DEPENDENT : thm := BAlgebraicMatroid.ALGEBRAIC_MATROID_DEPENDENT
unsafe def ALGEBRAIC_MATROID_SPANNING : thm := BAlgebraicMatroid.ALGEBRAIC_MATROID_SPANNING
unsafe def ALGEBRAIC_MATROID_BASIS : thm := BAlgebraicMatroid.ALGEBRAIC_MATROID_BASIS
unsafe def TRANSCENDENCE_BASIS_EXISTS : thm := BAlgebraicMatroid.TRANSCENDENCE_BASIS_EXISTS
unsafe def ALGEBRAICALLY_SPANNING_CONTAINS_TRANSCENDENCE_BASIS : thm := BAlgebraicMatroid.ALGEBRAICALLY_SPANNING_CONTAINS_TRANSCENDENCE_BASIS
unsafe def TRANSCENDENCE_BASES_CARD_EQ : thm := BAlgebraicMatroid.TRANSCENDENCE_BASES_CARD_EQ
unsafe def ALGEBRAICALLY_DEPENDENT_MONOMORPHIC_IMAGE : thm := BAlgebraicMatroid.ALGEBRAICALLY_DEPENDENT_MONOMORPHIC_IMAGE

-- AlgebraicTrans
unsafe def ALGEBRAIC_OVER_MONOMORPHIC_IMAGE : thm := BAlgebraicTrans.ALGEBRAIC_OVER_MONOMORPHIC_IMAGE
unsafe def ALGEBRAIC_SPAN_MONOMORPHIC_IMAGE : thm := BAlgebraicTrans.ALGEBRAIC_SPAN_MONOMORPHIC_IMAGE
unsafe def ALGEBRAICALLY_INDEPENDENT_TRANS : thm := BAlgebraicTrans.ALGEBRAICALLY_INDEPENDENT_TRANS
unsafe def ALGEBRAICALLY_SPANNING_TRANS : thm := BAlgebraicTrans.ALGEBRAICALLY_SPANNING_TRANS
unsafe def TRANSCENDENCE_BASIS_TRANS : thm := BAlgebraicTrans.TRANSCENDENCE_BASIS_TRANS
unsafe def TRANSCENDENCE_BASIS_TOWER_LAW : thm := BAlgebraicTrans.TRANSCENDENCE_BASIS_TOWER_LAW
unsafe def TRANSCENDENCE_BASIS_CARD_LE_LEFT : thm := BAlgebraicTrans.TRANSCENDENCE_BASIS_CARD_LE_LEFT
unsafe def TRANSCENDENCE_BASIS_CARD_LE_RIGHT : thm := BAlgebraicTrans.TRANSCENDENCE_BASIS_CARD_LE_RIGHT
unsafe def ALGEBRAIC_EXTENSION_SUBFIELDS_GENERATED : thm := BAlgebraicTrans.ALGEBRAIC_EXTENSION_SUBFIELDS_GENERATED

-- AlgebraicOverExt
unsafe def ALGEBRAIC_SPAN_OVER_ALGEBRAIC_EXTENSION : thm := BAlgebraicOverExt.ALGEBRAIC_SPAN_OVER_ALGEBRAIC_EXTENSION
unsafe def ALGEBRAICALLY_DEPENDENT_OVER_ALGEBRAIC_EXTENSION : thm := BAlgebraicOverExt.ALGEBRAICALLY_DEPENDENT_OVER_ALGEBRAIC_EXTENSION
unsafe def ALGEBRAICALLY_INDEPENDENT_OVER_ALGEBRAIC_EXTENSION : thm := BAlgebraicOverExt.ALGEBRAICALLY_INDEPENDENT_OVER_ALGEBRAIC_EXTENSION
unsafe def ALGEBRAICALLY_SPANNING_SPAN : thm := BAlgebraicOverExt.ALGEBRAICALLY_SPANNING_SPAN
unsafe def ALGEBRAICALLY_SPANNING_OVER_ALGEBRAIC_EXTENSION : thm := BAlgebraicOverExt.ALGEBRAICALLY_SPANNING_OVER_ALGEBRAIC_EXTENSION
unsafe def TRANSCENDENCE_BASIS_OVER_ALGEBRAIC_EXTENSION : thm := BAlgebraicOverExt.TRANSCENDENCE_BASIS_OVER_ALGEBRAIC_EXTENSION
unsafe def ALGEBRAICALLY_INDEPENDENT_CARD_LE_SPANNING : thm := BAlgebraicOverExt.ALGEBRAICALLY_INDEPENDENT_CARD_LE_SPANNING
unsafe def FINITELY_GENERATED_ALGEBRAICALLY_INDEPENDENT_IMP_FINITE : thm := BAlgebraicOverExt.FINITELY_GENERATED_ALGEBRAICALLY_INDEPENDENT_IMP_FINITE
unsafe def TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_SPANNING : thm := BAlgebraicOverExt.TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_SPANNING
unsafe def TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_INDEPENDENT : thm := BAlgebraicOverExt.TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_INDEPENDENT

-- TotallyTranscendental
unsafe def TOTALLY_TRANSCENDENTAL_EXTENSION : thm := BTotallyTranscendental.TOTALLY_TRANSCENDENTAL_EXTENSION
unsafe def TOTALLY_TRANSCENDENTAL_EXTENSION_ALT : thm := BTotallyTranscendental.TOTALLY_TRANSCENDENTAL_EXTENSION_ALT

-- FinitelyGeneratedTransEq
unsafe def FINITELY_GENERATED_EXTENSION_TRANS_EQ : thm := BFinitelyGeneratedTransEq.FINITELY_GENERATED_EXTENSION_TRANS_EQ

-- AcfBasic
unsafe def algebraically_closed_field : thm := BAcfBasic.algebraically_closed_field
unsafe def ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD : thm := BAcfBasic.ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD
unsafe def ALGEBRAICALLY_CLOSED_FIELD_ISOMORPHIC_IMAGE : thm := BAcfBasic.ALGEBRAICALLY_CLOSED_FIELD_ISOMORPHIC_IMAGE
unsafe def ISOMORPHIC_RING_ALGEBRAICALLY_CLOSED_FIELD : thm := BAcfBasic.ISOMORPHIC_RING_ALGEBRAICALLY_CLOSED_FIELD
unsafe def ALGEBRAICALLY_CLOSED_FIELD_IMP_INFINITE : thm := BAcfBasic.ALGEBRAICALLY_CLOSED_FIELD_IMP_INFINITE
unsafe def ALGEBRAICALLY_CLOSED_FIELD_NO_PROPER_ALGEBRAIC_EXTENSION : thm := BAcfBasic.ALGEBRAICALLY_CLOSED_FIELD_NO_PROPER_ALGEBRAIC_EXTENSION

-- AcfSplit
unsafe def ALGEBRAICALLY_CLOSED_FIELD_EQ_IRREDUCIBLES : thm := BAcfSplit.ALGEBRAICALLY_CLOSED_FIELD_EQ_IRREDUCIBLES
unsafe def IRREDUCIBLE_ALGEBRAICALLY_CLOSED_FIELD : thm := BAcfSplit.IRREDUCIBLE_ALGEBRAICALLY_CLOSED_FIELD
unsafe def ALGEBRAICALLY_CLOSED_FIELD_DECOMPOSE : thm := BAcfSplit.ALGEBRAICALLY_CLOSED_FIELD_DECOMPOSE
unsafe def ALGEBRAICALLY_CLOSED_FIELD_SPLITS : thm := BAcfSplit.ALGEBRAICALLY_CLOSED_FIELD_SPLITS

-- ClosedFieldSplits
unsafe def ALGEBRAICALLY_CLOSED_FIELD_EQ_SPLITS_ALT : thm := BClosedFieldSplits.ALGEBRAICALLY_CLOSED_FIELD_EQ_SPLITS_ALT
unsafe def ALGEBRAICALLY_CLOSED_FIELD_EQ_SPLITS : thm := BClosedFieldSplits.ALGEBRAICALLY_CLOSED_FIELD_EQ_SPLITS

-- SimpleExtendHom
unsafe def SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM : thm := BSimpleExtendHom.SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM

-- ClosureExtendHom
unsafe def ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM : thm := BClosureExtendHom.ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM

-- PolySquarefree
unsafe def POLY_SQUAREFREE_ROOT_COUNT_EXPLICIT : thm := BPolySquarefree.POLY_SQUAREFREE_ROOT_COUNT_EXPLICIT
unsafe def POLY_SQUAREFREE_ROOT_COUNT : thm := BPolySquarefree.POLY_SQUAREFREE_ROOT_COUNT
unsafe def POLY_SQUAREFREE_ROOT_COUNT_EQ : thm := BPolySquarefree.POLY_SQUAREFREE_ROOT_COUNT_EQ
unsafe def POLY_SQUAREFREE_EXPLICIT_EQ : thm := BPolySquarefree.POLY_SQUAREFREE_EXPLICIT_EQ

-- AlgebraicClosureExistsId
unsafe def ALGEBRAIC_CLOSURE_EXISTS_ID : thm := BAlgebraicClosureExistsId.ALGEBRAIC_CLOSURE_EXISTS_ID

-- AlgebraicClosure
unsafe def ALGEBRAIC_CLOSURE_EXISTS : thm := BAlgebraicClosure.ALGEBRAIC_CLOSURE_EXISTS
unsafe def ALGEBRAIC_CLOSURE_UNIQUE_EXPLICIT : thm := BAlgebraicClosure.ALGEBRAIC_CLOSURE_UNIQUE_EXPLICIT
unsafe def ALGEBRAIC_CLOSURE_UNIQUE : thm := BAlgebraicClosure.ALGEBRAIC_CLOSURE_UNIQUE
-- @@EXPORTS END

/-- `needs "Library/fieldtheory.ml"`: build the bundles, in order. -/
unsafe def ensureFieldTheory : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BSubfields.subfield_of
  let _ ← IO.mkRef BSubfieldGenerated.subfield_generated
  let _ ← IO.mkRef BSubfieldGenerated1.SUBSET_CARRIER_SUBFIELD_GENERATED
  let _ ← IO.mkRef BSubfieldGenerated2.SUBFIELD_OF_MONOMORPHIC_IMAGE
  let _ ← IO.mkRef BSubfieldQuotients.FIELD_SUBFIELD_GENERATED_UNITS
  let _ ← IO.mkRef BFieldExtension.field_extension
  let _ ← IO.mkRef BRingSpan.ring_span_RULES
  let _ ← IO.mkRef BRingMatroid.ring_matroid
  let _ ← IO.mkRef BLinearAlgebra.ring_dependent
  let _ ← IO.mkRef BFinitary.RING_DEPENDENT_FINITARY
  let _ ← IO.mkRef BTowerLaw.RING_SPANNING_TRANS
  let _ ← IO.mkRef BFiniteExtension.finite_extension
  let _ ← IO.mkRef BAlgebraicExtension.algebraic_over
  let _ ← IO.mkRef BAlgebraicOverBasics.ALGEBRAIC_OVER_NONMONOMORPHISM
  let _ ← IO.mkRef BAlgebraicExtensionProps.FIELD_SIMPLE_ALGEBRAIC_EXTENSION_GEN
  let _ ← IO.mkRef BAlgebraicExtMisc.ALGEBRAIC_FROM_SUBRING_GENERATED
  let _ ← IO.mkRef BAlgebraicField.ALGEBRAIC_OVER_0
  let _ ← IO.mkRef BFiniteExt.FINITE_EQ_FIELD_EXTENSION
  let _ ← IO.mkRef BAlgDepDefs.algebraically_dependent
  let _ ← IO.mkRef BAlgDepSpan.ALGEBRAIC_SPAN_SPAN
  let _ ← IO.mkRef BAlgSpanDepIndep.ALGEBRAICALLY_DEPENDENT_FINITARY
  let _ ← IO.mkRef BAlgebraicMatroid.algebraic_matroid
  let _ ← IO.mkRef BAlgebraicTrans.ALGEBRAIC_OVER_MONOMORPHIC_IMAGE
  let _ ← IO.mkRef BAlgebraicOverExt.ALGEBRAIC_SPAN_OVER_ALGEBRAIC_EXTENSION
  let _ ← IO.mkRef BTotallyTranscendental.TOTALLY_TRANSCENDENTAL_EXTENSION
  let _ ← IO.mkRef BFinitelyGeneratedTransEq.FINITELY_GENERATED_EXTENSION_TRANS_EQ
  let _ ← IO.mkRef BAcfBasic.algebraically_closed_field
  let _ ← IO.mkRef BAcfSplit.ALGEBRAICALLY_CLOSED_FIELD_EQ_IRREDUCIBLES
  let _ ← IO.mkRef BClosedFieldSplits.ALGEBRAICALLY_CLOSED_FIELD_EQ_SPLITS_ALT
  let _ ← IO.mkRef BSimpleExtendHom.SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM
  let _ ← IO.mkRef BClosureExtendHom.ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM
  let _ ← IO.mkRef BPolySquarefree.POLY_SQUAREFREE_ROOT_COUNT_EXPLICIT
  let _ ← IO.mkRef BAlgebraicClosureExistsId.ALGEBRAIC_CLOSURE_EXISTS_ID
  let _ ← IO.mkRef BAlgebraicClosure.ALGEBRAIC_CLOSURE_EXISTS
  -- @@ENSURE END
  pure ()

end SessionLibrary.FieldTheory
