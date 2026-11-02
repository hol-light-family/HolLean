/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/ring_det.ml.                                -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/RingDet.lean

  The session half of the ring_det.ml translation: it supplies
  HolLibrary.RingDet's dependencies from Session, SessionLibrary.RingTheory
  and SessionLibrary.Permutations, and exports every name under its HOL
  Light name.  Importing this module is `needs "Library/ring_det.ml"`; its
  `needs` of ringtheory.ml and permutations.ml are the imports of those
  modules.  The bundles are built by `initialize` when the module is loaded,
  in file order.
-/

import Session
import HolLibrary.RingDet
import SessionLibrary.RingTheory
import SessionLibrary.Permutations

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.RingDet

/-- The core theorems ring_det.ml uses. -/
def core1 : HolLibrary.RingDet.CoreThms1 where
  ADD1 := Session.ADD1
  ADD_CLAUSES := Session.ADD_CLAUSES
  ADD_EQ_0 := Session.ADD_EQ_0
  ADD_SUB := Session.ADD_SUB
  ADD_SUB2 := Session.ADD_SUB2
  AND_FORALL_THM := Session.AND_FORALL_THM
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_DELETE := Session.CARD_DELETE
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  CARTESIAN_PRODUCT_EMPTY := Session.CARTESIAN_PRODUCT_EMPTY
  COEFF_ABOVE_DEG := SessionLibrary.RingTheory.«COEFF_ABOVE_DEG»
  COEFF_COMPOSE := SessionLibrary.RingTheory.«COEFF_COMPOSE»
  COEFF_IN_CARRIER_ALT := SessionLibrary.RingTheory.«COEFF_IN_CARRIER_ALT»
  COEFF_NONZERO_LE_DEG := SessionLibrary.RingTheory.«COEFF_NONZERO_LE_DEG»
  COEFF_POLY_0 := SessionLibrary.RingTheory.«COEFF_POLY_0»
  COEFF_POLY_1 := SessionLibrary.RingTheory.«COEFF_POLY_1»
  COEFF_POLY_ADD := SessionLibrary.RingTheory.«COEFF_POLY_ADD»
  COEFF_POLY_CONST := SessionLibrary.RingTheory.«COEFF_POLY_CONST»
  COEFF_POLY_DERIV := SessionLibrary.RingTheory.«COEFF_POLY_DERIV»
  COEFF_POLY_LMUL := SessionLibrary.RingTheory.«COEFF_POLY_LMUL»
  COEFF_POLY_MUL := SessionLibrary.RingTheory.«COEFF_POLY_MUL»
  COEFF_POLY_MUL_VARPOW := SessionLibrary.RingTheory.«COEFF_POLY_MUL_VARPOW»
  COEFF_POLY_SUB := SessionLibrary.RingTheory.«COEFF_POLY_SUB»
  COEFF_POLY_SUM := SessionLibrary.RingTheory.«COEFF_POLY_SUM»
  COEFF_POLY_VAR := SessionLibrary.RingTheory.«COEFF_POLY_VAR»
  COEFF_POLY_VARPOW_MUL := SessionLibrary.RingTheory.«COEFF_POLY_VARPOW_MUL»
  COEFF_POLY_VAR_MUL := SessionLibrary.RingTheory.«COEFF_POLY_VAR_MUL»
  COEFF_RING_PRODUCT_MONIC_SUBLEADING := SessionLibrary.RingTheory.«COEFF_RING_PRODUCT_MONIC_SUBLEADING»
  COEFF_RING_SUM_VARPOW_REV := SessionLibrary.RingTheory.«COEFF_RING_SUM_VARPOW_REV»
  COMPONENT := Session.COMPONENT
  COND_ID := Session.COND_ID
  COND_RAND := Session.COND_RAND
  COND_RATOR := Session.COND_RATOR
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  CROSS := Session.CROSS
  CROSS_EMPTY := Session.CROSS_EMPTY
  DISJOINT := Session.DISJOINT
  DISJOINT_INSERT := Session.DISJOINT_INSERT
  DISJOINT_SYM := Session.DISJOINT_SYM
  DIVISION := Session.DIVISION
  DIVISION_SIMP := Session.DIVISION_SIMP
  DIV_LT := Session.DIV_LT
  DIV_MULT_ADD := Session.DIV_MULT_ADD
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EQ_ADD_RCANCEL := Session.EQ_ADD_RCANCEL
  EQ_SYM_EQ := Session.EQ_SYM_EQ
  EQ_TRANS := Session.EQ_TRANS
  ETA_AX := Session.ETA_AX
  EVEN := Session.EVEN
  EVENPERM_COMPOSE := SessionLibrary.Permutations.«EVENPERM_COMPOSE»
  EVENPERM_CYCLIC_N := SessionLibrary.Permutations.«EVENPERM_CYCLIC_N»
  EVENPERM_I := SessionLibrary.Permutations.«EVENPERM_I»

/-- The core theorems ring_det.ml uses. -/
def core2 : HolLibrary.RingDet.CoreThms2 where
  EVENPERM_ID := SessionLibrary.Permutations.«EVENPERM_ID»
  EVENPERM_INVERSE := SessionLibrary.Permutations.«EVENPERM_INVERSE»
  EVENPERM_SWAP := SessionLibrary.Permutations.«EVENPERM_SWAP»
  EVENPERM_TRANSFER := SessionLibrary.Permutations.«EVENPERM_TRANSFER»
  EVEN_ADD := Session.EVEN_ADD
  EVEN_MULT := Session.EVEN_MULT
  EXISTS_PAIR_THM := Session.EXISTS_PAIR_THM
  EXTENSION := Session.EXTENSION
  EXTENSIONAL := Session.EXTENSIONAL
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_MUL_RINV := SessionLibrary.RingTheory.«FIELD_MUL_RINV»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FINITE_CARTESIAN_PRODUCT := SessionLibrary.Card.«FINITE_CARTESIAN_PRODUCT»
  FINITE_CROSS := Session.FINITE_CROSS
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_HAS_SIZE := Session.FINITE_HAS_SIZE
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_PERMUTATIONS := SessionLibrary.Permutations.«FINITE_PERMUTATIONS»
  FINITE_POWERSET := Session.FINITE_POWERSET
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNION := Session.FINITE_UNION
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FUN_EQ_COEFF := SessionLibrary.RingTheory.«FUN_EQ_COEFF»
  FUN_EQ_THM := Session.FUN_EQ_THM
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  HAS_SIZE_FUNSPACE := Session.HAS_SIZE_FUNSPACE
  HAS_SIZE_IMAGE_INJ := Session.HAS_SIZE_IMAGE_INJ
  HAS_SIZE_NUMSEG_LT := Session.HAS_SIZE_NUMSEG_LT
  IMAGE_COMPOSE_PERMUTATIONS_L := SessionLibrary.Permutations.«IMAGE_COMPOSE_PERMUTATIONS_L»
  IMAGE_COMPOSE_PERMUTATIONS_R := SessionLibrary.Permutations.«IMAGE_COMPOSE_PERMUTATIONS_R»
  IMAGE_INVERSE_PERMUTATIONS := SessionLibrary.Permutations.«IMAGE_INVERSE_PERMUTATIONS»
  IMAGE_RESTRICTION := Session.IMAGE_RESTRICTION
  IMP_CONJ := Session.IMP_CONJ
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  IMP_IMP := Session.IMP_IMP
  INJECTIVE_ON_LEFT_INVERSE := Session.INJECTIVE_ON_LEFT_INVERSE
  INSERT_UNION_EQ := Session.INSERT_UNION_EQ
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_MUL_LCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_LCANCEL»
  INTEGRAL_DOMAIN_POLY_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_POLY_RING»
  INTEGRAL_DOMAIN_POW_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_POW_EQ_0»
  IN_CARTESIAN_PRODUCT := Session.IN_CARTESIAN_PRODUCT
  IN_CROSS := Session.IN_CROSS
  IN_DELETE := Session.IN_DELETE
  IN_DIFF := Session.IN_DIFF
  IN_ELIM_PAIR_THM := Session.IN_ELIM_PAIR_THM
  IN_ELIM_THM := Session.IN_ELIM_THM

/-- The core theorems ring_det.ml uses. -/
def core3 : HolLibrary.RingDet.CoreThms3 where
  IN_IDEAL_GENERATED_SING_EQ := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SING_EQ»
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_INTER := Session.IN_INTER
  IN_NUMSEG := Session.IN_NUMSEG
  IN_SING := Session.IN_SING
  IN_SUBRING_0 := SessionLibrary.RingTheory.«IN_SUBRING_0»
  IN_SUBRING_1 := SessionLibrary.RingTheory.«IN_SUBRING_1»
  IN_SUBRING_MUL := SessionLibrary.RingTheory.«IN_SUBRING_MUL»
  IN_SUBRING_SUM := SessionLibrary.RingTheory.«IN_SUBRING_SUM»
  IN_UNION := Session.IN_UNION
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LAMBDA_PAIR_THM := Session.LAMBDA_PAIR_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LET_TRANS := Session.LET_TRANS
  LE_0 := Session.LE_0
  LE_ADD := Session.LE_ADD
  LE_ADD2 := Session.LE_ADD2
  LE_ANTISYM := Session.LE_ANTISYM
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  LE_REFL := Session.LE_REFL
  LE_TRANS := Session.LE_TRANS
  LT := Session.LT
  LTE_TRANS := Session.LTE_TRANS
  LT_ADD_RCANCEL := Session.LT_ADD_RCANCEL
  LT_NZ := Session.LT_NZ
  LT_REFL := Session.LT_REFL
  LT_TRANS := Session.LT_TRANS
  MOD_LT := Session.MOD_LT
  MOD_LT_EQ := Session.MOD_LT_EQ
  MOD_MULT_ADD := Session.MOD_MULT_ADD
  MOD_UNIQ := Session.MOD_UNIQ
  MONIC_IN_TRIVIAL_RING := SessionLibrary.RingTheory.«MONIC_IN_TRIVIAL_RING»
  MONIC_POLY_PRODUCT := SessionLibrary.RingTheory.«MONIC_POLY_PRODUCT»
  MONIC_X_MINUS_A := SessionLibrary.RingTheory.«MONIC_X_MINUS_A»
  MONO_EXISTS := Session.MONO_EXISTS
  MONO_FORALL := Session.MONO_FORALL
  MULT_2 := Session.MULT_2
  MULT_CLAUSES := Session.MULT_CLAUSES
  NOT_EVEN := Session.NOT_EVEN
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LE := Session.NOT_LE
  NSUM_BOUND := Session.NSUM_BOUND
  NSUM_CLAUSES := Session.NSUM_CLAUSES
  NSUM_CONST := Session.NSUM_CONST
  NSUM_DELETE := Session.NSUM_DELETE
  NSUM_EQ := Session.NSUM_EQ
  NSUM_LE := Session.NSUM_LE
  NUMSEG_CLAUSES := Session.NUMSEG_CLAUSES
  NUMSEG_LT := Session.NUMSEG_LT
  NUMSEG_SING := Session.NUMSEG_SING
  OUTL := Session.raw3Ctx.D2.OUTL

/-- The core theorems ring_det.ml uses. -/
def core4 : HolLibrary.RingDet.CoreThms4 where
  OUTR := Session.raw3Ctx.D2.OUTR
  PAIR_EQ := Session.PAIR_EQ
  PERMUTATION_PERMUTES := SessionLibrary.Permutations.«PERMUTATION_PERMUTES»
  PERMUTATION_SWAP := SessionLibrary.Permutations.«PERMUTATION_SWAP»
  PERMUTES_COMPOSE := SessionLibrary.Permutations.«PERMUTES_COMPOSE»
  PERMUTES_CYCLIC_N := SessionLibrary.Permutations.«PERMUTES_CYCLIC_N»
  PERMUTES_EMPTY := SessionLibrary.Permutations.«PERMUTES_EMPTY»
  PERMUTES_FINITE_INJECTIVE := SessionLibrary.Permutations.«PERMUTES_FINITE_INJECTIVE»
  PERMUTES_FINITE_SURJECTIVE := SessionLibrary.Permutations.«PERMUTES_FINITE_SURJECTIVE»
  PERMUTES_I := SessionLibrary.Permutations.«PERMUTES_I»
  PERMUTES_IMAGE := SessionLibrary.Permutations.«PERMUTES_IMAGE»
  PERMUTES_INJECTIVE := SessionLibrary.Permutations.«PERMUTES_INJECTIVE»
  PERMUTES_INVERSE := SessionLibrary.Permutations.«PERMUTES_INVERSE»
  PERMUTES_INVERSES := SessionLibrary.Permutations.«PERMUTES_INVERSES»
  PERMUTES_INVERSES_o := SessionLibrary.Permutations.«PERMUTES_INVERSES_o»
  PERMUTES_INVERSE_INVERSE := SessionLibrary.Permutations.«PERMUTES_INVERSE_INVERSE»
  PERMUTES_IN_IMAGE := SessionLibrary.Permutations.«PERMUTES_IN_IMAGE»
  PERMUTES_NUMSET_LE := SessionLibrary.Permutations.«PERMUTES_NUMSET_LE»
  PERMUTES_SUBSET := SessionLibrary.Permutations.«PERMUTES_SUBSET»
  PERMUTES_SUPERSET := SessionLibrary.Permutations.«PERMUTES_SUPERSET»
  PERMUTES_SWAP := SessionLibrary.Permutations.«PERMUTES_SWAP»
  PERMUTES_TRANSFER := SessionLibrary.Permutations.«PERMUTES_TRANSFER»
  PID_IMP_UFD := SessionLibrary.RingTheory.«PID_IMP_UFD»
  PID_POLY_RING := SessionLibrary.RingTheory.«PID_POLY_RING»
  POLY_0 := SessionLibrary.RingTheory.«POLY_0»
  POLY_ADD_RZERO := SessionLibrary.RingTheory.«POLY_ADD_RZERO»
  POLY_CLAUSES := SessionLibrary.RingTheory.«POLY_CLAUSES»
  POLY_COMPOSE_HOMOMORPHISM_CONST := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_CONST»
  POLY_COMPOSE_HOMOMORPHISM_SUB := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_SUB»
  POLY_COMPOSE_HOMOMORPHISM_VAR := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_VAR»
  POLY_CONST_0 := SessionLibrary.RingTheory.«POLY_CONST_0»
  POLY_CONST_1 := SessionLibrary.RingTheory.«POLY_CONST_1»
  POLY_CONST_EQ_0 := SessionLibrary.RingTheory.«POLY_CONST_EQ_0»
  POLY_DEG_0 := SessionLibrary.RingTheory.«POLY_DEG_0»
  POLY_DEG_1 := SessionLibrary.RingTheory.«POLY_DEG_1»
  POLY_DEG_CMUL_LE := SessionLibrary.RingTheory.«POLY_DEG_CMUL_LE»
  POLY_DEG_CONST := SessionLibrary.RingTheory.«POLY_DEG_CONST»
  POLY_DEG_DERIV_LE := SessionLibrary.RingTheory.«POLY_DEG_DERIV_LE»
  POLY_DEG_DIVIDES_LE := SessionLibrary.RingTheory.«POLY_DEG_DIVIDES_LE»
  POLY_DEG_EQ_0_UNIT := SessionLibrary.RingTheory.«POLY_DEG_EQ_0_UNIT»
  POLY_DEG_MUL := SessionLibrary.RingTheory.«POLY_DEG_MUL»
  POLY_DEG_MUL_LE := SessionLibrary.RingTheory.«POLY_DEG_MUL_LE»
  POLY_DEG_MUL_X_MINUS_A := SessionLibrary.RingTheory.«POLY_DEG_MUL_X_MINUS_A»
  POLY_DEG_NEG := SessionLibrary.RingTheory.«POLY_DEG_NEG»
  POLY_DEG_PRODUCT_MONIC := SessionLibrary.RingTheory.«POLY_DEG_PRODUCT_MONIC»
  POLY_DEG_RING_SUM_LE := SessionLibrary.RingTheory.«POLY_DEG_RING_SUM_LE»
  POLY_DEG_RING_SUM_VARPOW_REV := SessionLibrary.RingTheory.«POLY_DEG_RING_SUM_VARPOW_REV»
  POLY_DEG_SUB_CONST := SessionLibrary.RingTheory.«POLY_DEG_SUB_CONST»
  POLY_DEG_VAR := SessionLibrary.RingTheory.«POLY_DEG_VAR»
  POLY_DEG_VARPOW_MUL := SessionLibrary.RingTheory.«POLY_DEG_VARPOW_MUL»
  POLY_DEG_VAR_POW := SessionLibrary.RingTheory.«POLY_DEG_VAR_POW»
  POLY_DEG_X_MINUS_A := SessionLibrary.RingTheory.«POLY_DEG_X_MINUS_A»
  POLY_DERIV_CMUL := SessionLibrary.RingTheory.«POLY_DERIV_CMUL»
  POLY_DERIV_CONST := SessionLibrary.RingTheory.«POLY_DERIV_CONST»
  POLY_DERIV_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_DERIV_HOMOMORPHIC_IMAGE»
  POLY_DERIV_IN_CARRIER := SessionLibrary.RingTheory.«POLY_DERIV_IN_CARRIER»

/-- The core theorems ring_det.ml uses. -/
def core5 : HolLibrary.RingDet.CoreThms5 where
  POLY_DERIV_MUL := SessionLibrary.RingTheory.«POLY_DERIV_MUL»
  POLY_DERIV_SUB := SessionLibrary.RingTheory.«POLY_DERIV_SUB»
  POLY_DERIV_VAR := SessionLibrary.RingTheory.«POLY_DERIV_VAR»
  POLY_DIVIDES_X_MINUS_A := SessionLibrary.RingTheory.«POLY_DIVIDES_X_MINUS_A»
  POLY_EVAL := SessionLibrary.RingTheory.«POLY_EVAL»
  POLY_EVAL_0 := SessionLibrary.RingTheory.«POLY_EVAL_0»
  POLY_EVAL_ADD := SessionLibrary.RingTheory.«POLY_EVAL_ADD»
  POLY_EVAL_AT_0 := SessionLibrary.RingTheory.«POLY_EVAL_AT_0»
  POLY_EVAL_COEFF := SessionLibrary.RingTheory.«POLY_EVAL_COEFF»
  POLY_EVAL_CONST := SessionLibrary.RingTheory.«POLY_EVAL_CONST»
  POLY_EVAL_MUL := SessionLibrary.RingTheory.«POLY_EVAL_MUL»
  POLY_EVAL_RING_PRODUCT := SessionLibrary.RingTheory.«POLY_EVAL_RING_PRODUCT»
  POLY_EVAL_SUB := SessionLibrary.RingTheory.«POLY_EVAL_SUB»
  POLY_EVAL_VAR := SessionLibrary.RingTheory.«POLY_EVAL_VAR»
  POLY_EXPAND_REV := SessionLibrary.RingTheory.«POLY_EXPAND_REV»
  POLY_EXTEND_0 := SessionLibrary.RingTheory.«POLY_EXTEND_0»
  POLY_EXTEND_CONST := SessionLibrary.RingTheory.«POLY_EXTEND_CONST»
  POLY_EXTEND_SUB := SessionLibrary.RingTheory.«POLY_EXTEND_SUB»
  POLY_EXTEND_VAR := SessionLibrary.RingTheory.«POLY_EXTEND_VAR»
  POLY_MUL_0 := SessionLibrary.RingTheory.«POLY_MUL_0»
  POLY_MUL_LID := SessionLibrary.RingTheory.«POLY_MUL_LID»
  POLY_MUL_RID := SessionLibrary.RingTheory.«POLY_MUL_RID»
  POLY_POW := SessionLibrary.RingTheory.«POLY_POW»
  POLY_RING := SessionLibrary.RingTheory.«POLY_RING»
  POLY_RING_CLAUSES := SessionLibrary.RingTheory.«POLY_RING_CLAUSES»
  POLY_TOP_EQ_0 := SessionLibrary.RingTheory.«POLY_TOP_EQ_0»
  POLY_X_MINUS_A_IN_CARRIER := SessionLibrary.RingTheory.«POLY_X_MINUS_A_IN_CARRIER»
  PROD_RING := SessionLibrary.RingTheory.«PROD_RING»
  QUOTIENT_RING := SessionLibrary.RingTheory.«QUOTIENT_RING»
  QUOTIENT_RING_0 := SessionLibrary.RingTheory.«QUOTIENT_RING_0»
  QUOTIENT_RING_HOMOMORPHISM_EXISTS := SessionLibrary.RingTheory.«QUOTIENT_RING_HOMOMORPHISM_EXISTS»
  QUOTIENT_RING_MUL := SessionLibrary.RingTheory.«QUOTIENT_RING_MUL»
  RDIV_LT_EQ := Session.RDIV_LT_EQ
  RESTRICTION := Session.RESTRICTION
  RESTRICTION_DEFINED := Session.RESTRICTION_DEFINED
  RESTRICTION_IN_CARTESIAN_PRODUCT := Session.RESTRICTION_IN_CARTESIAN_PRODUCT
  RESTRICTION_UNIQUE := Session.RESTRICTION_UNIQUE
  RIGHT_AND_EXISTS_THM := Session.RIGHT_AND_EXISTS_THM
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RIGHT_IMP_FORALL_THM := Session.RIGHT_IMP_FORALL_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_ASSOC := SessionLibrary.RingTheory.«RING_ADD_ASSOC»
  RING_ADD_LDISTRIB := SessionLibrary.RingTheory.«RING_ADD_LDISTRIB»
  RING_ADD_LNEG := SessionLibrary.RingTheory.«RING_ADD_LNEG»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RDISTRIB := SessionLibrary.RingTheory.«RING_ADD_RDISTRIB»
  RING_ADD_RNEG := SessionLibrary.RingTheory.«RING_ADD_RNEG»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_ADD_SYM := SessionLibrary.RingTheory.«RING_ADD_SYM»
  RING_COPRIME_0 := SessionLibrary.RingTheory.«RING_COPRIME_0»
  RING_COPRIME_DIVPROD_RIGHT := SessionLibrary.RingTheory.«RING_COPRIME_DIVPROD_RIGHT»
  RING_COPRIME_SYM := SessionLibrary.RingTheory.«RING_COPRIME_SYM»
  RING_COSET_EQ_IDEAL := SessionLibrary.RingTheory.«RING_COSET_EQ_IDEAL»

/-- The core theorems ring_det.ml uses. -/
def core6 : HolLibrary.RingDet.CoreThms6 where
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_I := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_I»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_NEG := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_NEG»
  RING_HOMOMORPHISM_PAIRED := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_PAIRED»
  RING_HOMOMORPHISM_POLY_CONST := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_CONST»
  RING_HOMOMORPHISM_POLY_EXTEND := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_EXTEND»
  RING_HOMOMORPHISM_POLY_RINGS := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_RINGS»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_PRODUCT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_PRODUCT»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_RING_OF_NUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_NUM»
  RING_HOMOMORPHISM_SUB := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUB»
  RING_HOMOMORPHISM_SUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_INV_1 := SessionLibrary.RingTheory.«RING_INV_1»
  RING_LNEG_UNIQUE := SessionLibrary.RingTheory.«RING_LNEG_UNIQUE»
  RING_MONOMORPHISM_ALT := SessionLibrary.RingTheory.«RING_MONOMORPHISM_ALT»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_INJECTIVE_EQ := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INJECTIVE_EQ»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_AC := SessionLibrary.RingTheory.«RING_MUL_AC»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_LCANCEL := SessionLibrary.RingTheory.«RING_MUL_LCANCEL»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LINV := SessionLibrary.RingTheory.«RING_MUL_LINV»
  RING_MUL_LNEG := SessionLibrary.RingTheory.«RING_MUL_LNEG»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_POW := SessionLibrary.RingTheory.«RING_MUL_POW»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RINV := SessionLibrary.RingTheory.«RING_MUL_RINV»
  RING_MUL_RNEG := SessionLibrary.RingTheory.«RING_MUL_RNEG»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_NEG_EQ := SessionLibrary.RingTheory.«RING_NEG_EQ»
  RING_NEG_EQ_0 := SessionLibrary.RingTheory.«RING_NEG_EQ_0»
  RING_NEG_NEG := SessionLibrary.RingTheory.«RING_NEG_NEG»
  RING_NILPOTENT_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_NILPOTENT_HOMOMORPHIC_IMAGE»
  RING_NILPOTENT_IN_CARRIER := SessionLibrary.RingTheory.«RING_NILPOTENT_IN_CARRIER»
  RING_NILPOTENT_LMUL := SessionLibrary.RingTheory.«RING_NILPOTENT_LMUL»
  RING_NILPOTENT_RMUL := SessionLibrary.RingTheory.«RING_NILPOTENT_RMUL»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_1 := SessionLibrary.RingTheory.«RING_OF_NUM_1»
  RING_POLYNOMIAL := SessionLibrary.RingTheory.«RING_POLYNOMIAL»
  RING_POLYNOMIAL_0 := SessionLibrary.RingTheory.«RING_POLYNOMIAL_0»
  RING_POLYNOMIAL_1 := SessionLibrary.RingTheory.«RING_POLYNOMIAL_1»
  RING_POLYNOMIAL_COEFF := SessionLibrary.RingTheory.«RING_POLYNOMIAL_COEFF»
  RING_POLYNOMIAL_CONST := SessionLibrary.RingTheory.«RING_POLYNOMIAL_CONST»
  RING_POLYNOMIAL_IMP_POWERSERIES := SessionLibrary.RingTheory.«RING_POLYNOMIAL_IMP_POWERSERIES»

/-- The core theorems ring_det.ml uses. -/
def core7 : HolLibrary.RingDet.CoreThms7 where
  RING_POLYNOMIAL_MUL := SessionLibrary.RingTheory.«RING_POLYNOMIAL_MUL»
  RING_POLYNOMIAL_NEG := SessionLibrary.RingTheory.«RING_POLYNOMIAL_NEG»
  RING_POLYNOMIAL_POLY_DERIV := SessionLibrary.RingTheory.«RING_POLYNOMIAL_POLY_DERIV»
  RING_POLYNOMIAL_POW := SessionLibrary.RingTheory.«RING_POLYNOMIAL_POW»
  RING_POLYNOMIAL_SUB := SessionLibrary.RingTheory.«RING_POLYNOMIAL_SUB»
  RING_POLYNOMIAL_VAR := SessionLibrary.RingTheory.«RING_POLYNOMIAL_VAR»
  RING_POLYNOMIAL_X_MINUS_A := SessionLibrary.RingTheory.«RING_POLYNOMIAL_X_MINUS_A»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POWERSERIES_0 := SessionLibrary.RingTheory.«RING_POWERSERIES_0»
  RING_POWERSERIES_CONST := SessionLibrary.RingTheory.«RING_POWERSERIES_CONST»
  RING_POWERSERIES_VAR := SessionLibrary.RingTheory.«RING_POWERSERIES_VAR»
  RING_POW_ADD := SessionLibrary.RingTheory.«RING_POW_ADD»
  RING_POW_MUL := SessionLibrary.RingTheory.«RING_POW_MUL»
  RING_POW_NEG := SessionLibrary.RingTheory.«RING_POW_NEG»
  RING_POW_ONE := SessionLibrary.RingTheory.«RING_POW_ONE»
  RING_POW_POW := SessionLibrary.RingTheory.«RING_POW_POW»
  RING_POW_ZERO := SessionLibrary.RingTheory.«RING_POW_ZERO»
  RING_PRODUCT := SessionLibrary.RingTheory.«RING_PRODUCT»
  RING_PRODUCT_1 := SessionLibrary.RingTheory.«RING_PRODUCT_1»
  RING_PRODUCT_CLAUSES := SessionLibrary.RingTheory.«RING_PRODUCT_CLAUSES»
  RING_PRODUCT_CLOSED := SessionLibrary.RingTheory.«RING_PRODUCT_CLOSED»
  RING_PRODUCT_CONST := SessionLibrary.RingTheory.«RING_PRODUCT_CONST»
  RING_PRODUCT_DELTA := SessionLibrary.RingTheory.«RING_PRODUCT_DELTA»
  RING_PRODUCT_EQ := SessionLibrary.RingTheory.«RING_PRODUCT_EQ»
  RING_PRODUCT_EQ_1 := SessionLibrary.RingTheory.«RING_PRODUCT_EQ_1»
  RING_PRODUCT_IMAGE := SessionLibrary.RingTheory.«RING_PRODUCT_IMAGE»
  RING_PRODUCT_MUL := SessionLibrary.RingTheory.«RING_PRODUCT_MUL»
  RING_PRODUCT_PAIRS_LT := SessionLibrary.RingTheory.«RING_PRODUCT_PAIRS_LT»
  RING_PRODUCT_POW := SessionLibrary.RingTheory.«RING_PRODUCT_POW»
  RING_PRODUCT_SING := SessionLibrary.RingTheory.«RING_PRODUCT_SING»
  RING_PRODUCT_SUPERSET := SessionLibrary.RingTheory.«RING_PRODUCT_SUPERSET»
  RING_PRODUCT_UNION := SessionLibrary.RingTheory.«RING_PRODUCT_UNION»
  RING_PRODUCT_ZERO := SessionLibrary.RingTheory.«RING_PRODUCT_ZERO»
  RING_RINV_UNIQUE := SessionLibrary.RingTheory.«RING_RINV_UNIQUE»
  RING_RZERO_UNIQUE := SessionLibrary.RingTheory.«RING_RZERO_UNIQUE»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_LDISTRIB := SessionLibrary.RingTheory.«RING_SUB_LDISTRIB»
  RING_SUB_LZERO := SessionLibrary.RingTheory.«RING_SUB_LZERO»
  RING_SUB_RDISTRIB := SessionLibrary.RingTheory.«RING_SUB_RDISTRIB»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_SUB_RZERO := SessionLibrary.RingTheory.«RING_SUB_RZERO»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_0 := SessionLibrary.RingTheory.«RING_SUM_0»
  RING_SUM_ADD := SessionLibrary.RingTheory.«RING_SUM_ADD»
  RING_SUM_CASES := SessionLibrary.RingTheory.«RING_SUM_CASES»
  RING_SUM_CLAUSES := SessionLibrary.RingTheory.«RING_SUM_CLAUSES»
  RING_SUM_CLAUSES_NUMSEG := SessionLibrary.RingTheory.«RING_SUM_CLAUSES_NUMSEG»
  RING_SUM_CLOSED := SessionLibrary.RingTheory.«RING_SUM_CLOSED»
  RING_SUM_CONST := SessionLibrary.RingTheory.«RING_SUM_CONST»
  RING_SUM_DELTA := SessionLibrary.RingTheory.«RING_SUM_DELTA»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_EQ_0 := SessionLibrary.RingTheory.«RING_SUM_EQ_0»
  RING_SUM_EQ_GENERAL_INVERSES := SessionLibrary.RingTheory.«RING_SUM_EQ_GENERAL_INVERSES»
  RING_SUM_IMAGE := SessionLibrary.RingTheory.«RING_SUM_IMAGE»
  RING_SUM_LMUL := SessionLibrary.RingTheory.«RING_SUM_LMUL»

/-- The core theorems ring_det.ml uses. -/
def core8 : HolLibrary.RingDet.CoreThms8 where
  RING_SUM_NEG := SessionLibrary.RingTheory.«RING_SUM_NEG»
  RING_SUM_RESTRICT_SET := SessionLibrary.RingTheory.«RING_SUM_RESTRICT_SET»
  RING_SUM_RMUL := SessionLibrary.RingTheory.«RING_SUM_RMUL»
  RING_SUM_SING := SessionLibrary.RingTheory.«RING_SUM_SING»
  RING_SUM_SUB := SessionLibrary.RingTheory.«RING_SUM_SUB»
  RING_SUM_SUM_PRODUCT := SessionLibrary.RingTheory.«RING_SUM_SUM_PRODUCT»
  RING_SUM_SUPERSET := SessionLibrary.RingTheory.«RING_SUM_SUPERSET»
  RING_SUM_SWAP := SessionLibrary.RingTheory.«RING_SUM_SWAP»
  RING_SUM_UNION := SessionLibrary.RingTheory.«RING_SUM_UNION»
  RING_UNIT_IMP_REGULAR := SessionLibrary.RingTheory.«RING_UNIT_IMP_REGULAR»
  RING_UNIT_NILPOTENT_CLAUSES_1 := SessionLibrary.RingTheory.«RING_UNIT_NILPOTENT_CLAUSES_1»
  RING_UNIT_POLY_DOMAIN := SessionLibrary.RingTheory.«RING_UNIT_POLY_DOMAIN»
  SELECT_AX := Session.SELECT_AX
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SING_GSPEC := Session.SING_GSPEC
  SKOLEM_THM := Session.SKOLEM_THM
  SUBRING_OF_IMP_SUBSET := SessionLibrary.RingTheory.«SUBRING_OF_IMP_SUBSET»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_ANTISYM_EQ := Session.SUBSET_ANTISYM_EQ
  SUBSET_REFL := Session.SUBSET_REFL
  SUBSET_UNIV := Session.SUBSET_UNIV
  SUB_0 := Session.SUB_0
  SUB_REFL := Session.SUB_REFL
  SUC_SUB1 := Session.SUC_SUB1
  SWAP_IDEMPOTENT := SessionLibrary.Permutations.«SWAP_IDEMPOTENT»
  TRIVIAL_POLY_RING := SessionLibrary.RingTheory.«TRIVIAL_POLY_RING»
  TRIVIAL_RING_10 := SessionLibrary.RingTheory.«TRIVIAL_RING_10»
  TRIVIAL_RING_SUBSET := SessionLibrary.RingTheory.«TRIVIAL_RING_SUBSET»
  UNION_EMPTY := Session.UNION_EMPTY
  field := SessionLibrary.RingTheory.«field»
  monic := SessionLibrary.RingTheory.«monic»
  o_ASSOC := Session.o_ASSOC
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM
  permutes := SessionLibrary.Permutations.«permutes»
  poly_eval := SessionLibrary.RingTheory.«poly_eval»
  poly_evaluate := SessionLibrary.RingTheory.«poly_evaluate»
  poly_separable := SessionLibrary.RingTheory.«poly_separable»
  poly_sub := SessionLibrary.RingTheory.«poly_sub»
  ring_coprime := SessionLibrary.RingTheory.«ring_coprime»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_inv := SessionLibrary.RingTheory.«ring_inv»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_sub := SessionLibrary.RingTheory.«ring_sub»
  ring_unit := SessionLibrary.RingTheory.«ring_unit»
  subring_of := SessionLibrary.RingTheory.«subring_of»
  swap := SessionLibrary.Permutations.«swap»
  trivial_ring := SessionLibrary.RingTheory.«trivial_ring»

def deps : HolLibrary.RingDet.RingDetDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  TAUT t := ExceptT.mk (Session.TAUT t)
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  SELECT_CONV t := pure (Session.SELECT_CONV t)
  num_CONV := Session.num_CONV
  RING_RULE t := ExceptT.mk (SessionLibrary.RingTheory.RING_RULE t)
  distinctness s := ExceptT.mk (Session.distinctness s)
  injectivity s := ExceptT.mk (Session.injectivity s)
  core1 := core1
  core2 := core2
  core3 := core3
  core4 := core4
  core5 := core5
  core6 := core6
  core7 := core7
  core8 := core8

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} (name : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in ring_det.ml order. -/

initialize BDet : HolLibrary.RingDet.Det ←
  ioB "setupDet" <|
    (HolLibrary.RingDet.setupDet deps).run

initialize BDetRows : HolLibrary.RingDet.DetRows ←
  ioB "setupDetRows" <|
    (HolLibrary.RingDet.setupDetRows deps BDet).run

initialize BCofactors : HolLibrary.RingDet.Cofactors ←
  ioB "setupCofactors" <|
    (HolLibrary.RingDet.setupCofactors deps BDet BDetRows).run

initialize BFieldDet : HolLibrary.RingDet.FieldDet ←
  ioB "setupFieldDet" <|
    (HolLibrary.RingDet.setupFieldDet deps BDet BDetRows BCofactors).run

initialize BTrace : HolLibrary.RingDet.Trace ←
  ioB "setupTrace" <|
    (HolLibrary.RingDet.setupTrace deps BDet BDetRows BCofactors BFieldDet).run

initialize BBlocks : HolLibrary.RingDet.Blocks ←
  ioB "setupBlocks" <|
    (HolLibrary.RingDet.setupBlocks deps BDet BCofactors BFieldDet BTrace).run

initialize BTriangular : HolLibrary.RingDet.Triangular ←
  ioB "setupTriangular" <|
    (HolLibrary.RingDet.setupTriangular deps BDet BFieldDet).run

initialize BCharpoly : HolLibrary.RingDet.Charpoly ←
  ioB "setupCharpoly" <|
    (HolLibrary.RingDet.setupCharpoly deps BDet BDetRows BCofactors BFieldDet).run

initialize BCharpolySimilar : HolLibrary.RingDet.CharpolySimilar ←
  ioB "setupCharpolySimilar" <|
    (HolLibrary.RingDet.setupCharpolySimilar deps BDet BFieldDet BTrace BCharpoly).run

initialize BCharpolyCoeffs : HolLibrary.RingDet.CharpolyCoeffs ←
  ioB "setupCharpolyCoeffs" <|
    (HolLibrary.RingDet.setupCharpolyCoeffs deps BDet BTrace BCharpoly).run

initialize BVandermonde : HolLibrary.RingDet.Vandermonde ←
  ioB "setupVandermonde" <|
    (HolLibrary.RingDet.setupVandermonde deps BDet BTriangular BCharpoly).run

initialize BFreeBases : HolLibrary.RingDet.FreeBases ←
  ioB "setupFreeBases" <|
    (HolLibrary.RingDet.setupFreeBases deps).run

initialize BMulMatrix : HolLibrary.RingDet.MulMatrix ←
  ioB "setupMulMatrix" <|
    (HolLibrary.RingDet.setupMulMatrix deps BFreeBases).run

initialize BChangeOfBasis : HolLibrary.RingDet.ChangeOfBasis ←
  ioB "setupChangeOfBasis" <|
    (HolLibrary.RingDet.setupChangeOfBasis deps BDet BDetRows BCofactors BFieldDet BCharpoly BCharpolySimilar BFreeBases BMulMatrix).run

initialize BProjectiveBases : HolLibrary.RingDet.ProjectiveBases ←
  ioB "setupProjectiveBases" <|
    (HolLibrary.RingDet.setupProjectiveBases deps BFreeBases).run

initialize BTraceNormBasis : HolLibrary.RingDet.TraceNormBasis ←
  ioB "setupTraceNormBasis" <|
    (HolLibrary.RingDet.setupTraceNormBasis deps BDet BBlocks BFreeBases BProjectiveBases).run

initialize BTraceNormAlgebra : HolLibrary.RingDet.TraceNormAlgebra ←
  ioB "setupTraceNormAlgebra" <|
    (HolLibrary.RingDet.setupTraceNormAlgebra deps BDet BCofactors BFieldDet BBlocks BFreeBases BMulMatrix BProjectiveBases BTraceNormBasis).run

initialize BTraceNormMisc : HolLibrary.RingDet.TraceNormMisc ←
  ioB "setupTraceNormMisc" <|
    (HolLibrary.RingDet.setupTraceNormMisc deps BDet BDetRows BCofactors BCharpoly BFreeBases BMulMatrix BProjectiveBases BTraceNormBasis BTraceNormAlgebra).run

initialize BUnits : HolLibrary.RingDet.Units ←
  ioB "setupUnits" <|
    (HolLibrary.RingDet.setupUnits deps BDet BDetRows BCofactors BBlocks BFreeBases BMulMatrix BProjectiveBases BTraceNormBasis BTraceNormAlgebra).run

initialize BBaseChange : HolLibrary.RingDet.BaseChange ←
  ioB "setupBaseChange" <|
    (HolLibrary.RingDet.setupBaseChange deps BDet BDetRows BCofactors BCharpoly BFreeBases BMulMatrix BProjectiveBases BTraceNormBasis).run

initialize BFreeTowers : HolLibrary.RingDet.FreeTowers ←
  ioB "setupFreeTowers" <|
    (HolLibrary.RingDet.setupFreeTowers deps BDet BCofactors BBlocks BCharpoly BFreeBases BMulMatrix BTraceNormAlgebra).run

initialize BProjectiveTowers : HolLibrary.RingDet.ProjectiveTowers ←
  ioB "setupProjectiveTowers" <|
    (HolLibrary.RingDet.setupProjectiveTowers deps BFreeBases BProjectiveBases BTraceNormBasis BTraceNormAlgebra BFreeTowers).run

initialize BProdAlgebras : HolLibrary.RingDet.ProdAlgebras ←
  ioB "setupProdAlgebras" <|
    (HolLibrary.RingDet.setupProdAlgebras deps BDet BTrace BBlocks BFreeBases BProjectiveBases BTraceNormBasis).run

initialize BBasisDiscriminant : HolLibrary.RingDet.BasisDiscriminant ←
  ioB "setupBasisDiscriminant" <|
    (HolLibrary.RingDet.setupBasisDiscriminant deps BDet BDetRows BCofactors BFieldDet BTrace BFreeBases BTraceNormAlgebra BTraceNormMisc BBaseChange).run

initialize BNilpotent : HolLibrary.RingDet.Nilpotent ←
  ioB "setupNilpotent" <|
    (HolLibrary.RingDet.setupNilpotent deps BDet BCofactors BFieldDet BVandermonde BMulMatrix BTraceNormAlgebra BBasisDiscriminant).run

initialize BCoeffArrays : HolLibrary.RingDet.CoeffArrays ←
  ioB "setupCoeffArrays" <|
    (HolLibrary.RingDet.setupCoeffArrays deps BDet BFieldDet BTrace BBlocks BTriangular).run

initialize BSylvester : HolLibrary.RingDet.Sylvester ←
  ioB "setupSylvester" <|
    (HolLibrary.RingDet.setupSylvester deps BDet BCofactors BCharpoly BCoeffArrays).run

initialize BResultantBasics : HolLibrary.RingDet.ResultantBasics ←
  ioB "setupResultantBasics" <|
    (HolLibrary.RingDet.setupResultantBasics deps BDet BDetRows BCofactors BNilpotent BSylvester).run

initialize BResultantCombination : HolLibrary.RingDet.ResultantCombination ←
  ioB "setupResultantCombination" <|
    (HolLibrary.RingDet.setupResultantCombination deps BCofactors BNilpotent BSylvester).run

initialize BDiscriminantBasics : HolLibrary.RingDet.DiscriminantBasics ←
  ioB "setupDiscriminantBasics" <|
    (HolLibrary.RingDet.setupDiscriminantBasics deps BDet BDetRows BNilpotent).run

initialize BDiscriminantRoots : HolLibrary.RingDet.DiscriminantRoots ←
  ioB "setupDiscriminantRoots" <|
    (HolLibrary.RingDet.setupDiscriminantRoots deps BDet BDetRows BVandermonde BNilpotent BSylvester BDiscriminantBasics).run

initialize BDiscriminantField : HolLibrary.RingDet.DiscriminantField ←
  ioB "setupDiscriminantField" <|
    (HolLibrary.RingDet.setupDiscriminantField deps BDet BSylvester BDiscriminantBasics).run

/- The exports, under their HOL Light names. -/

-- Det
def ring_sign : thm := BDet.ring_sign
def ring_det : thm := BDet.ring_det
def RING_SIGN : thm := BDet.RING_SIGN
def RING_SIGN_I : thm := BDet.RING_SIGN_I
def RING_SIGN_ID : thm := BDet.RING_SIGN_ID
def RING_SIGN_SWAP : thm := BDet.RING_SIGN_SWAP
def RING_SIGN_COMPOSE : thm := BDet.RING_SIGN_COMPOSE
def RING_SIGN_INVERSE : thm := BDet.RING_SIGN_INVERSE
def RING_SIGN_IDEMPOTENT : thm := BDet.RING_SIGN_IDEMPOTENT
def RING_HOMOMORPHISM_SIGN : thm := BDet.RING_HOMOMORPHISM_SIGN
def RING_PRODUCT_PERMUTE : thm := BDet.RING_PRODUCT_PERMUTE
def RING_SUM_PERMUTE : thm := BDet.RING_SUM_PERMUTE
def RING_SUM_PERMUTATIONS_INVERSE : thm := BDet.RING_SUM_PERMUTATIONS_INVERSE
def RING_SUM_PERMUTATIONS_COMPOSE_L : thm := BDet.RING_SUM_PERMUTATIONS_COMPOSE_L
def RING_SUM_PERMUTATIONS_COMPOSE_R : thm := BDet.RING_SUM_PERMUTATIONS_COMPOSE_R
def PERMUTES_INJECTIVE_RESTRICT : thm := BDet.PERMUTES_INJECTIVE_RESTRICT
def RING_DET : thm := BDet.RING_DET
def RING_DET_EQ : thm := BDet.RING_DET_EQ
def RING_DET_EMPTY : thm := BDet.RING_DET_EMPTY
def RING_DET_TRANSP : thm := BDet.RING_DET_TRANSP
def RING_DET_PERMUTE_ROWS : thm := BDet.RING_DET_PERMUTE_ROWS
def RING_DET_PERMUTE_COLUMNS : thm := BDet.RING_DET_PERMUTE_COLUMNS
def RING_DET_SWAP_ROWS : thm := BDet.RING_DET_SWAP_ROWS
def RING_DET_SWAP_COLUMNS : thm := BDet.RING_DET_SWAP_COLUMNS

-- DetRows
def RING_DET_IDENTICAL_ROWS : thm := BDetRows.RING_DET_IDENTICAL_ROWS
def RING_DET_IDENTICAL_COLUMNS : thm := BDetRows.RING_DET_IDENTICAL_COLUMNS
def RING_PRODUCT_DELETE : thm := BDetRows.RING_PRODUCT_DELETE
def RING_DET_ROW_EXPANSION : thm := BDetRows.RING_DET_ROW_EXPANSION
def RING_DET_ROW_CMUL : thm := BDetRows.RING_DET_ROW_CMUL
def RING_DET_ROW_ADD : thm := BDetRows.RING_DET_ROW_ADD
def RING_DET_ROW_SUM : thm := BDetRows.RING_DET_ROW_SUM
def RING_DET_ROW_0 : thm := BDetRows.RING_DET_ROW_0
def RING_DET_ROWS_MUL : thm := BDetRows.RING_DET_ROWS_MUL
def RING_DET_COLUMNS_MUL : thm := BDetRows.RING_DET_COLUMNS_MUL
def RING_DET_ROW_OPERATION : thm := BDetRows.RING_DET_ROW_OPERATION
def RING_SUM_PRODUCT_CARTESIAN_PRODUCT : thm := BDetRows.RING_SUM_PRODUCT_CARTESIAN_PRODUCT
def RING_DET_MULTILINEAR : thm := BDetRows.RING_DET_MULTILINEAR
def RING_DET_HOMOMORPHISM : thm := BDetRows.RING_DET_HOMOMORPHISM

-- Cofactors
def RING_DET_DIAGONAL : thm := BCofactors.RING_DET_DIAGONAL
def RING_DET_I : thm := BCofactors.RING_DET_I
def ring_cofactor : thm := BCofactors.ring_cofactor
def RING_COFACTOR : thm := BCofactors.RING_COFACTOR
def RING_COFACTOR_EQ : thm := BCofactors.RING_COFACTOR_EQ
def RING_DET_ROW_COFACTOR_EXPANSION : thm := BCofactors.RING_DET_ROW_COFACTOR_EXPANSION
def RING_DET_COFACTOR_EXPANSION : thm := BCofactors.RING_DET_COFACTOR_EXPANSION
def RING_DET_ADJUGATE_ROWS : thm := BCofactors.RING_DET_ADJUGATE_ROWS
def RING_COFACTOR_TRANSP : thm := BCofactors.RING_COFACTOR_TRANSP
def RING_DET_ADJUGATE_COLUMNS : thm := BCofactors.RING_DET_ADJUGATE_COLUMNS
def RING_DET_CLOSED : thm := BCofactors.RING_DET_CLOSED
def RING_DET_SUBRING : thm := BCofactors.RING_DET_SUBRING
def RING_COFACTOR_EQ_GEN : thm := BCofactors.RING_COFACTOR_EQ_GEN
def RING_COFACTOR_INSERT : thm := BCofactors.RING_COFACTOR_INSERT
def RING_DET_DEPENDENT_ROWS_MUL : thm := BCofactors.RING_DET_DEPENDENT_ROWS_MUL
def RING_DET_DEPENDENT_ROWS : thm := BCofactors.RING_DET_DEPENDENT_ROWS

-- FieldDet
def RING_DET_MINOR_SELECTION : thm := BFieldDet.RING_DET_MINOR_SELECTION
def RING_DET_INDEPENDENT_ROWS : thm := BFieldDet.RING_DET_INDEPENDENT_ROWS
def RING_DET_EQ_0_ROWS : thm := BFieldDet.RING_DET_EQ_0_ROWS
def RING_DET_DEPENDENT_COLUMNS_MUL : thm := BFieldDet.RING_DET_DEPENDENT_COLUMNS_MUL
def RING_DET_DEPENDENT_COLUMNS_MUL_IDEAL : thm := BFieldDet.RING_DET_DEPENDENT_COLUMNS_MUL_IDEAL
def RING_DET_DEPENDENT_COLUMNS : thm := BFieldDet.RING_DET_DEPENDENT_COLUMNS
def RING_DET_INDEPENDENT_COLUMNS : thm := BFieldDet.RING_DET_INDEPENDENT_COLUMNS
def RING_DET_EQ_0_COLUMNS : thm := BFieldDet.RING_DET_EQ_0_COLUMNS
def RING_COFACTOR_INSERT_SWAP : thm := BFieldDet.RING_COFACTOR_INSERT_SWAP
def RING_DET_LAPLACE_INSERT : thm := BFieldDet.RING_DET_LAPLACE_INSERT
def RING_DET_MUL : thm := BFieldDet.RING_DET_MUL
def RING_DET_SIMILAR : thm := BFieldDet.RING_DET_SIMILAR
def RING_DET_COFACTOR : thm := BFieldDet.RING_DET_COFACTOR

-- Trace
def RING_SUM_TRACE_SIMILAR : thm := BTrace.RING_SUM_TRACE_SIMILAR
def RING_SUM_MUL_SWAP : thm := BTrace.RING_SUM_MUL_SWAP
def RING_SUM_TRACE_SIMILAR_UNIT : thm := BTrace.RING_SUM_TRACE_SIMILAR_UNIT
def RING_TRACE_DET_SIMILAR_DIAGONAL : thm := BTrace.RING_TRACE_DET_SIMILAR_DIAGONAL
def RING_SUM_ALTERNATING_SUBSETS : thm := BTrace.RING_SUM_ALTERNATING_SUBSETS
def RING_SUM_PERMUTATIONS_RYSER : thm := BTrace.RING_SUM_PERMUTATIONS_RYSER
def RING_DET_REINDEX : thm := BTrace.RING_DET_REINDEX
def RING_DET_SING : thm := BTrace.RING_DET_SING
def RING_DET_CMUL : thm := BTrace.RING_DET_CMUL

-- Blocks
def RING_DET_BLOCK_TRIANGULAR : thm := BBlocks.RING_DET_BLOCK_TRIANGULAR
def RING_DET_KRONECKER : thm := BBlocks.RING_DET_KRONECKER
def RING_DET_KRONECKER_MOD_DIV : thm := BBlocks.RING_DET_KRONECKER_MOD_DIV
def RING_SUM_DELTA_MUL : thm := BBlocks.RING_SUM_DELTA_MUL
def RING_DET_WEINSTEIN_ARONSZAJN : thm := BBlocks.RING_DET_WEINSTEIN_ARONSZAJN

-- Triangular
def RING_DET_LOWERTRIANGULAR : thm := BTriangular.RING_DET_LOWERTRIANGULAR
def RING_DET_UPPERTRIANGULAR : thm := BTriangular.RING_DET_UPPERTRIANGULAR
def RING_DET_LOWERTRIANGULAR_MUL : thm := BTriangular.RING_DET_LOWERTRIANGULAR_MUL
def RING_SUM_SWAP_DELTA : thm := BTriangular.RING_SUM_SWAP_DELTA
def RING_DET_TRIANGULAR_ROWS : thm := BTriangular.RING_DET_TRIANGULAR_ROWS

-- Charpoly
def POLY_DEG_RING_PRODUCT_LE : thm := BCharpoly.POLY_DEG_RING_PRODUCT_LE
def COEFF_POLY_MUL_LE : thm := BCharpoly.COEFF_POLY_MUL_LE
def COEFF_RING_PRODUCT_LE : thm := BCharpoly.COEFF_RING_PRODUCT_LE
def NSUM_LE_CARD_DELETE : thm := BCharpoly.NSUM_LE_CARD_DELETE
def ring_charpoly : thm := BCharpoly.ring_charpoly
def RING_CHARPOLY : thm := BCharpoly.RING_CHARPOLY
def RING_CHARPOLY_EQ : thm := BCharpoly.RING_CHARPOLY_EQ
def RING_CHARPOLY_TRANSP : thm := BCharpoly.RING_CHARPOLY_TRANSP
def RING_CHARPOLY_ENTRY : thm := BCharpoly.RING_CHARPOLY_ENTRY
def RING_CHARPOLY_EXTEND : thm := BCharpoly.RING_CHARPOLY_EXTEND
def RING_CHARPOLY_HOMOMORPHISM : thm := BCharpoly.RING_CHARPOLY_HOMOMORPHISM
def RING_CHARPOLY_ID : thm := BCharpoly.RING_CHARPOLY_ID
def RING_CHARPOLY_EVAL : thm := BCharpoly.RING_CHARPOLY_EVAL
def RING_CHARPOLY_DEG_COEFF : thm := BCharpoly.RING_CHARPOLY_DEG_COEFF
def RING_CHARPOLY_MONIC : thm := BCharpoly.RING_CHARPOLY_MONIC
def RING_CHARPOLY_EIGENVECTOR : thm := BCharpoly.RING_CHARPOLY_EIGENVECTOR

-- CharpolySimilar
def RING_CHARPOLY_REINDEX : thm := BCharpolySimilar.RING_CHARPOLY_REINDEX
def RING_CHARPOLY_SIMILAR : thm := BCharpolySimilar.RING_CHARPOLY_SIMILAR

-- CharpolyCoeffs
def RING_CHARPOLY_COEFF_0 : thm := BCharpolyCoeffs.RING_CHARPOLY_COEFF_0
def COEFF_RING_PRODUCT_X_MINUS : thm := BCharpolyCoeffs.COEFF_RING_PRODUCT_X_MINUS
def RING_CHARPOLY_COEFF_TRACE : thm := BCharpolyCoeffs.RING_CHARPOLY_COEFF_TRACE
def RING_CHARPOLY_EQ_CARD_2 : thm := BCharpolyCoeffs.RING_CHARPOLY_EQ_CARD_2

-- Vandermonde
def COEFF_0_1_RING_PRODUCT : thm := BVandermonde.COEFF_0_1_RING_PRODUCT
def COEFF_1_RING_PRODUCT_PERMUTES : thm := BVandermonde.COEFF_1_RING_PRODUCT_PERMUTES
def COEFF_1_RING_DET : thm := BVandermonde.COEFF_1_RING_DET
def RING_DET_VANDERMONDE : thm := BVandermonde.RING_DET_VANDERMONDE

-- FreeBases
def free_basis : thm := BFreeBases.free_basis
def basis_coordinates : thm := BFreeBases.basis_coordinates
def mul_matrix : thm := BFreeBases.mul_matrix
def projective_basis : thm := BFreeBases.projective_basis
def algebra_trace : thm := BFreeBases.algebra_trace
def algebra_norm : thm := BFreeBases.algebra_norm
def FREE_BASIS_IN_CARRIER : thm := BFreeBases.FREE_BASIS_IN_CARRIER
def FREE_BASIS_INDEPENDENT : thm := BFreeBases.FREE_BASIS_INDEPENDENT
def FREE_BASIS_MONOMORPHISM : thm := BFreeBases.FREE_BASIS_MONOMORPHISM
def FREE_BASIS_UNIQUE : thm := BFreeBases.FREE_BASIS_UNIQUE
def FREE_BASIS_DELTA : thm := BFreeBases.FREE_BASIS_DELTA
def FREE_BASIS_HAS_SIZE : thm := BFreeBases.FREE_BASIS_HAS_SIZE
def FREE_BASIS_RING_DIVIDES : thm := BFreeBases.FREE_BASIS_RING_DIVIDES
def FREE_BASIS_QUOTIENT_RING_PRINCIPAL : thm := BFreeBases.FREE_BASIS_QUOTIENT_RING_PRINCIPAL
def FREE_BASIS_RING_SUM_IMAGE : thm := BFreeBases.FREE_BASIS_RING_SUM_IMAGE
def BASIS_COORDINATES : thm := BFreeBases.BASIS_COORDINATES
def BASIS_COORDINATES_OUTSIDE : thm := BFreeBases.BASIS_COORDINATES_OUTSIDE
def BASIS_COORDINATES_IN_CARRIER : thm := BFreeBases.BASIS_COORDINATES_IN_CARRIER
def BASIS_COORDINATES_EXPAND : thm := BFreeBases.BASIS_COORDINATES_EXPAND
def BASIS_COORDINATES_UNIQUE : thm := BFreeBases.BASIS_COORDINATES_UNIQUE
def BASIS_COORDINATES_EQ : thm := BFreeBases.BASIS_COORDINATES_EQ
def BASIS_COORDINATES_LINCOMB : thm := BFreeBases.BASIS_COORDINATES_LINCOMB
def BASIS_COORDINATES_BASIS : thm := BFreeBases.BASIS_COORDINATES_BASIS
def BASIS_COORDINATES_ADD : thm := BFreeBases.BASIS_COORDINATES_ADD
def BASIS_COORDINATES_LMUL : thm := BFreeBases.BASIS_COORDINATES_LMUL
def BASIS_COORDINATES_0 : thm := BFreeBases.BASIS_COORDINATES_0
def BASIS_COORDINATES_SUM : thm := BFreeBases.BASIS_COORDINATES_SUM
def BASIS_COORDINATES_MUL : thm := BFreeBases.BASIS_COORDINATES_MUL

-- MulMatrix
def EXTENSION_LINCOMB_SUM : thm := BMulMatrix.EXTENSION_LINCOMB_SUM
def EXTENSION_LINCOMB_ADD : thm := BMulMatrix.EXTENSION_LINCOMB_ADD
def EXTENSION_LINCOMB_LMUL : thm := BMulMatrix.EXTENSION_LINCOMB_LMUL
def EXTENSION_MUL_LINCOMB : thm := BMulMatrix.EXTENSION_MUL_LINCOMB
def EXTENSION_LINCOMB_MUL : thm := BMulMatrix.EXTENSION_LINCOMB_MUL
def MUL_MATRIX_IN_CARRIER : thm := BMulMatrix.MUL_MATRIX_IN_CARRIER
def MUL_MATRIX_EXPAND : thm := BMulMatrix.MUL_MATRIX_EXPAND
def MUL_MATRIX_ADD : thm := BMulMatrix.MUL_MATRIX_ADD
def MUL_MATRIX_LMUL : thm := BMulMatrix.MUL_MATRIX_LMUL
def MUL_MATRIX_SCALAR : thm := BMulMatrix.MUL_MATRIX_SCALAR
def MUL_MATRIX_1 : thm := BMulMatrix.MUL_MATRIX_1
def MUL_MATRIX_0 : thm := BMulMatrix.MUL_MATRIX_0
def MUL_MATRIX_MUL : thm := BMulMatrix.MUL_MATRIX_MUL
def MUL_MATRIX_RING_SUM : thm := BMulMatrix.MUL_MATRIX_RING_SUM
def MUL_MATRIX_SUBRING : thm := BMulMatrix.MUL_MATRIX_SUBRING

-- ChangeOfBasis
def BASIS_COORDINATES_CHANGE_OF_BASIS : thm := BChangeOfBasis.BASIS_COORDINATES_CHANGE_OF_BASIS
def BASIS_COORDINATES_CHANGE_OF_BASIS_INVERSE : thm := BChangeOfBasis.BASIS_COORDINATES_CHANGE_OF_BASIS_INVERSE
def MUL_MATRIX_CHANGE_OF_BASIS : thm := BChangeOfBasis.MUL_MATRIX_CHANGE_OF_BASIS
def FREE_BASES_SIZE_EQ : thm := BChangeOfBasis.FREE_BASES_SIZE_EQ
def MUL_MATRIX_CHARPOLY_BASIS : thm := BChangeOfBasis.MUL_MATRIX_CHARPOLY_BASIS

-- ProjectiveBases
def PROJECTIVE_BASIS_IN_CARRIER : thm := BProjectiveBases.PROJECTIVE_BASIS_IN_CARRIER
def PROJECTIVE_BASIS_EXPAND : thm := BProjectiveBases.PROJECTIVE_BASIS_EXPAND
def PROJECTIVE_BASIS_ADD : thm := BProjectiveBases.PROJECTIVE_BASIS_ADD
def PROJECTIVE_BASIS_LMUL : thm := BProjectiveBases.PROJECTIVE_BASIS_LMUL
def PROJECTIVE_BASIS_0 : thm := BProjectiveBases.PROJECTIVE_BASIS_0
def PROJECTIVE_BASIS_NEG : thm := BProjectiveBases.PROJECTIVE_BASIS_NEG
def PROJECTIVE_BASIS_SUB : thm := BProjectiveBases.PROJECTIVE_BASIS_SUB
def PROJECTIVE_BASIS_SUM : thm := BProjectiveBases.PROJECTIVE_BASIS_SUM
def PROJECTIVE_BASIS_RING_SUM : thm := BProjectiveBases.PROJECTIVE_BASIS_RING_SUM
def PROJECTIVE_BASIS_LINEAR : thm := BProjectiveBases.PROJECTIVE_BASIS_LINEAR
def PROJECTIVE_BASIS_MUL : thm := BProjectiveBases.PROJECTIVE_BASIS_MUL
def PROJECTIVE_BASIS_CHANGE : thm := BProjectiveBases.PROJECTIVE_BASIS_CHANGE
def FREE_BASIS_PROJECTIVE : thm := BProjectiveBases.FREE_BASIS_PROJECTIVE

-- TraceNormBasis
def ALGEBRA_TRACE_PROJECTIVE_BASIS : thm := BTraceNormBasis.ALGEBRA_TRACE_PROJECTIVE_BASIS
def ALGEBRA_NORM_PROJECTIVE_BASIS : thm := BTraceNormBasis.ALGEBRA_NORM_PROJECTIVE_BASIS
def ALGEBRA_NORM_PROJECTIVE_BASIS_ALT : thm := BTraceNormBasis.ALGEBRA_NORM_PROJECTIVE_BASIS_ALT

-- TraceNormAlgebra
def ALGEBRA_TRACE_FREE_BASIS : thm := BTraceNormAlgebra.ALGEBRA_TRACE_FREE_BASIS
def ALGEBRA_NORM_FREE_BASIS : thm := BTraceNormAlgebra.ALGEBRA_NORM_FREE_BASIS
def ALGEBRA_TRACE_NORM_NO_PROJECTIVE_BASIS : thm := BTraceNormAlgebra.ALGEBRA_TRACE_NORM_NO_PROJECTIVE_BASIS
def ALGEBRA_TRACE_NORM_IN_CARRIER : thm := BTraceNormAlgebra.ALGEBRA_TRACE_NORM_IN_CARRIER
def ALGEBRA_TRACE_ADD : thm := BTraceNormAlgebra.ALGEBRA_TRACE_ADD
def ALGEBRA_TRACE_SCALAR : thm := BTraceNormAlgebra.ALGEBRA_TRACE_SCALAR
def ALGEBRA_NORM_MUL : thm := BTraceNormAlgebra.ALGEBRA_NORM_MUL
def ALGEBRA_TRACE_NORM_BASE_FREE_BASIS : thm := BTraceNormAlgebra.ALGEBRA_TRACE_NORM_BASE_FREE_BASIS
def ALGEBRA_TRACE_0 : thm := BTraceNormAlgebra.ALGEBRA_TRACE_0
def ALGEBRA_NORM_1 : thm := BTraceNormAlgebra.ALGEBRA_NORM_1
def ALGEBRA_TRACE_NEG : thm := BTraceNormAlgebra.ALGEBRA_TRACE_NEG
def ALGEBRA_TRACE_SUB : thm := BTraceNormAlgebra.ALGEBRA_TRACE_SUB
def ALGEBRA_NORM_POW : thm := BTraceNormAlgebra.ALGEBRA_NORM_POW
def ALGEBRA_TRACE_SUM : thm := BTraceNormAlgebra.ALGEBRA_TRACE_SUM
def ALGEBRA_NORM_PRODUCT : thm := BTraceNormAlgebra.ALGEBRA_NORM_PRODUCT

-- TraceNormMisc
def ALGEBRA_TRACE_SUBRING : thm := BTraceNormMisc.ALGEBRA_TRACE_SUBRING
def ALGEBRA_NORM_SUBRING : thm := BTraceNormMisc.ALGEBRA_NORM_SUBRING
def ALGEBRA_TRACE_RING_SUM : thm := BTraceNormMisc.ALGEBRA_TRACE_RING_SUM
def ALGEBRA_TRACE_LINCOMB_MUL : thm := BTraceNormMisc.ALGEBRA_TRACE_LINCOMB_MUL
def ALGEBRA_TRACE_MUL_LINCOMB : thm := BTraceNormMisc.ALGEBRA_TRACE_MUL_LINCOMB
def ALGEBRA_NORM_SUB_CHARPOLY : thm := BTraceNormMisc.ALGEBRA_NORM_SUB_CHARPOLY
def FREE_BASIS_EQ_IMAGE : thm := BTraceNormMisc.FREE_BASIS_EQ_IMAGE
def PROJECTIVE_BASIS_EQ_IMAGE : thm := BTraceNormMisc.PROJECTIVE_BASIS_EQ_IMAGE
def ALGEBRA_TRACE_NORM_EQ_IMAGE : thm := BTraceNormMisc.ALGEBRA_TRACE_NORM_EQ_IMAGE

-- Units
def ALGEBRA_NORM_UNIT_PROJECTIVE : thm := BUnits.ALGEBRA_NORM_UNIT_PROJECTIVE
def ALGEBRA_NORM_UNIT : thm := BUnits.ALGEBRA_NORM_UNIT
def ALGEBRA_NORM_0_FREE_BASIS : thm := BUnits.ALGEBRA_NORM_0_FREE_BASIS
def ALGEBRA_NORM_0 : thm := BUnits.ALGEBRA_NORM_0
def ALGEBRA_NORM_0_PROJECTIVE : thm := BUnits.ALGEBRA_NORM_0_PROJECTIVE
def ALGEBRA_NORM_INV : thm := BUnits.ALGEBRA_NORM_INV
def ALGEBRA_NORM_EQ_0_FREE_BASIS : thm := BUnits.ALGEBRA_NORM_EQ_0_FREE_BASIS

-- BaseChange
def BASIS_COORDINATES_HOMOMORPHIC_IMAGE : thm := BBaseChange.BASIS_COORDINATES_HOMOMORPHIC_IMAGE
def MUL_MATRIX_HOMOMORPHIC_IMAGE : thm := BBaseChange.MUL_MATRIX_HOMOMORPHIC_IMAGE
def ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE_PROJECTIVE : thm := BBaseChange.ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE_PROJECTIVE
def ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE : thm := BBaseChange.ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE
def MUL_MATRIX_CHARPOLY_ROOT : thm := BBaseChange.MUL_MATRIX_CHARPOLY_ROOT

-- FreeTowers
def RING_SUM_MOD_DIV : thm := BFreeTowers.RING_SUM_MOD_DIV
def FREE_BASIS_TRANS : thm := BFreeTowers.FREE_BASIS_TRANS
def BASIS_COORDINATES_TRANS : thm := BFreeTowers.BASIS_COORDINATES_TRANS
def MUL_MATRIX_TRANS : thm := BFreeTowers.MUL_MATRIX_TRANS
def ALGEBRA_TRACE_NORM_INTERMEDIATE_FREE_BASIS : thm := BFreeTowers.ALGEBRA_TRACE_NORM_INTERMEDIATE_FREE_BASIS
def MUL_MATRIX_CHARPOLY_INTERMEDIATE : thm := BFreeTowers.MUL_MATRIX_CHARPOLY_INTERMEDIATE

-- ProjectiveTowers
def PROJECTIVE_BASIS_TRANS : thm := BProjectiveTowers.PROJECTIVE_BASIS_TRANS
def ALGEBRA_TRACE_TOWER_PROJECTIVE : thm := BProjectiveTowers.ALGEBRA_TRACE_TOWER_PROJECTIVE

-- ProdAlgebras
def PROJECTIVE_BASIS_PROD_RING : thm := BProdAlgebras.PROJECTIVE_BASIS_PROD_RING
def ALGEBRA_TRACE_NORM_PROD_RING : thm := BProdAlgebras.ALGEBRA_TRACE_NORM_PROD_RING

-- BasisDiscriminant
def basis_discriminant : thm := BBasisDiscriminant.basis_discriminant
def BASIS_DISCRIMINANT_HOMOMORPHIC_IMAGE : thm := BBasisDiscriminant.BASIS_DISCRIMINANT_HOMOMORPHIC_IMAGE
def BASIS_DISCRIMINANT_CHANGE_OF_BASIS : thm := BBasisDiscriminant.BASIS_DISCRIMINANT_CHANGE_OF_BASIS
def TRACE_FORM_NONDEGENERATE : thm := BBasisDiscriminant.TRACE_FORM_NONDEGENERATE
def BASIS_DISCRIMINANT_DEGENERATE : thm := BBasisDiscriminant.BASIS_DISCRIMINANT_DEGENERATE
def BASIS_DISCRIMINANT_EQ_0 : thm := BBasisDiscriminant.BASIS_DISCRIMINANT_EQ_0
def BASIS_DISCRIMINANT_NONZERO : thm := BBasisDiscriminant.BASIS_DISCRIMINANT_NONZERO
def BASIS_DISCRIMINANT_TIMES_COORD : thm := BBasisDiscriminant.BASIS_DISCRIMINANT_TIMES_COORD

-- Nilpotent
def RING_POLYNOMIAL_MUL_MATRIX : thm := BNilpotent.RING_POLYNOMIAL_MUL_MATRIX
def MUL_MATRIX_POLY_MUL : thm := BNilpotent.MUL_MATRIX_POLY_MUL
def RING_UNIT_MUL_MATRIX_POLY : thm := BNilpotent.RING_UNIT_MUL_MATRIX_POLY
def ALGEBRA_TRACE_NILPOTENT : thm := BNilpotent.ALGEBRA_TRACE_NILPOTENT
def BASIS_DISCRIMINANT_NILPOTENT : thm := BNilpotent.BASIS_DISCRIMINANT_NILPOTENT
def poly_resultant : thm := BNilpotent.poly_resultant
def poly_discriminant : thm := BNilpotent.poly_discriminant

-- CoeffArrays
def RING_DET_COEFF_RING_SUM : thm := BCoeffArrays.RING_DET_COEFF_RING_SUM
def RING_DET_COEFF_MONIC_REV : thm := BCoeffArrays.RING_DET_COEFF_MONIC_REV
def RING_DET_COEFF_BASIS : thm := BCoeffArrays.RING_DET_COEFF_BASIS
def RING_DET_ROW_OPERATIONS_SUCC : thm := BCoeffArrays.RING_DET_ROW_OPERATIONS_SUCC
def RING_DET_COEFF_X_MINUS : thm := BCoeffArrays.RING_DET_COEFF_X_MINUS
def RING_DET_COEFF_EQ_0 : thm := BCoeffArrays.RING_DET_COEFF_EQ_0

-- Sylvester
def RING_DET_SYLVESTER : thm := BSylvester.RING_DET_SYLVESTER
def RING_SUM_SYLVESTER_ROWS : thm := BSylvester.RING_SUM_SYLVESTER_ROWS
def RING_DET_SYLVESTER_X_MINUS : thm := BSylvester.RING_DET_SYLVESTER_X_MINUS
def POLY_DEG_RING_PRODUCT_X_MINUS_LE : thm := BSylvester.POLY_DEG_RING_PRODUCT_X_MINUS_LE
def RING_DET_SYLVESTER_ROOTS : thm := BSylvester.RING_DET_SYLVESTER_ROOTS
def RING_DET_SYLVESTER_EQ_0 : thm := BSylvester.RING_DET_SYLVESTER_EQ_0

-- ResultantBasics
def POLY_RESULTANT_IN_CARRIER : thm := BResultantBasics.POLY_RESULTANT_IN_CARRIER
def POLY_RESULTANT_HOMOMORPHISM : thm := BResultantBasics.POLY_RESULTANT_HOMOMORPHISM
def POLY_RESULTANT_SYM : thm := BResultantBasics.POLY_RESULTANT_SYM
def POLY_RESULTANT_LCONST : thm := BResultantBasics.POLY_RESULTANT_LCONST
def POLY_RESULTANT_RCONST : thm := BResultantBasics.POLY_RESULTANT_RCONST
def POLY_RESULTANT_ROOTS : thm := BResultantBasics.POLY_RESULTANT_ROOTS
def POLY_RESULTANT_X_MINUS_MUL : thm := BResultantBasics.POLY_RESULTANT_X_MINUS_MUL
def POLY_RESULTANT_X_MINUS : thm := BResultantBasics.POLY_RESULTANT_X_MINUS

-- ResultantCombination
def POLY_RESULTANT_COMBINATION : thm := BResultantCombination.POLY_RESULTANT_COMBINATION
def POLY_RESULTANT_EQ_0 : thm := BResultantCombination.POLY_RESULTANT_EQ_0

-- DiscriminantBasics
def POLY_DISCRIMINANT_IN_CARRIER : thm := BDiscriminantBasics.POLY_DISCRIMINANT_IN_CARRIER
def POLY_DISCRIMINANT_HOMOMORPHISM : thm := BDiscriminantBasics.POLY_DISCRIMINANT_HOMOMORPHISM
def POLY_DISCRIMINANT_SYLVESTER : thm := BDiscriminantBasics.POLY_DISCRIMINANT_SYLVESTER
def POLY_DISCRIMINANT_RESULTANT : thm := BDiscriminantBasics.POLY_DISCRIMINANT_RESULTANT
def POLY_DISCRIMINANT_CMUL : thm := BDiscriminantBasics.POLY_DISCRIMINANT_CMUL

-- DiscriminantRoots
def POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS : thm := BDiscriminantRoots.POLY_EVAL_DERIV_RING_PRODUCT_X_MINUS
def RING_PRODUCT_DIFFERENCES : thm := BDiscriminantRoots.RING_PRODUCT_DIFFERENCES
def RING_PRODUCT_DIFFERENCES_SQUARE : thm := BDiscriminantRoots.RING_PRODUCT_DIFFERENCES_SQUARE
def POLY_DISCRIMINANT_ROOTS : thm := BDiscriminantRoots.POLY_DISCRIMINANT_ROOTS
def POLY_DISCRIMINANT_VANDERMONDE : thm := BDiscriminantRoots.POLY_DISCRIMINANT_VANDERMONDE

-- DiscriminantField
def POLY_DISCRIMINANT_EQ_0 : thm := BDiscriminantField.POLY_DISCRIMINANT_EQ_0

/-- `needs "Library/ring_det.ml"`: already done by importing this module. -/
def ensureRingDet : IO Unit := pure ()

end SessionLibrary.RingDet
