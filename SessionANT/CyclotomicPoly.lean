/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/cyclotomic_poly.ml                            . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/CyclotomicPoly.lean

  The session half of the cyclotomic_poly.ml translation: it supplies HolANT.CyclotomicPoly's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/cyclotomic_poly.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.CyclotomicPoly
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
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionLibrary.Integer
import SessionLibrary.Isum
import SessionLibrary.Products
import SessionLibrary.Multiplicative
import SessionLibrary.Primitive

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.CyclotomicPoly

/-- The core theorems cyclotomic_poly.ml uses. -/
def core1 : HolANT.CyclotomicPoly.CoreThms1 where
  ADD1 := Session.ADD1
  ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH := SessionLibrary.FieldTheory.«ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH»
  ARITH_EQ := Session.ARITH_EQ
  BEZOUT_GCD_STRONG := SessionLibrary.Prime.«BEZOUT_GCD_STRONG»
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  COEFF := SessionLibrary.RingTheory.«COEFF»
  COEFF_IN_CARRIER_ALT := SessionLibrary.RingTheory.«COEFF_IN_CARRIER_ALT»
  COEFF_POLY_0 := SessionLibrary.RingTheory.«COEFF_POLY_0»
  COEFF_POLY_1 := SessionLibrary.RingTheory.«COEFF_POLY_1»
  COEFF_POLY_SUB := SessionLibrary.RingTheory.«COEFF_POLY_SUB»
  COEFF_POLY_VARPOW := SessionLibrary.RingTheory.«COEFF_POLY_VARPOW»
  COPRIME_0 := SessionLibrary.Prime.«COPRIME_0»
  COPRIME_GCD := SessionLibrary.Prime.«COPRIME_GCD»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DISJOINT := Session.DISJOINT
  DISJ_SYM := Session.DISJ_SYM
  DIVIDES_0 := SessionLibrary.Prime.«DIVIDES_0»
  DIVIDES_1 := SessionLibrary.Prime.«DIVIDES_1»
  DIVIDES_ANTISYM := Session.DIVIDES_ANTISYM
  DIVIDES_EXP_LE_IMP := SessionLibrary.Prime.«DIVIDES_EXP_LE_IMP»
  DIVIDES_LE := Session.DIVIDES_LE
  DIVIDES_LMUL := SessionLibrary.Prime.«DIVIDES_LMUL»
  DIVIDES_LMUL2_EQ := SessionLibrary.Prime.«DIVIDES_LMUL2_EQ»
  DIVIDES_MUL2 := SessionLibrary.Prime.«DIVIDES_MUL2»
  DIVIDES_ONE := Session.DIVIDES_ONE
  DIVIDES_PRIMEPOW := SessionLibrary.Prime.«DIVIDES_PRIMEPOW»
  DIVIDES_PRIME_PRIME := SessionLibrary.Prime.«DIVIDES_PRIME_PRIME»
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  DIVIDES_REXP := SessionLibrary.Prime.«DIVIDES_REXP»
  DIVIDES_RMUL := SessionLibrary.Prime.«DIVIDES_RMUL»
  DIVIDES_TRANS := SessionLibrary.Prime.«DIVIDES_TRANS»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  DIVISION_DECOMP := SessionLibrary.Prime.«DIVISION_DECOMP»
  DIV_1 := Session.DIV_1
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EQ_PRIMEPOW := SessionLibrary.Prime.«EQ_PRIMEPOW»
  EQ_TRANS := Session.EQ_TRANS
  EXP := Session.EXP
  EXP_EQ_0 := Session.EXP_EQ_0
  EXTENSION := Session.EXTENSION
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_MONIC_IRREDUCIBLE_ASSOCIATE := SessionLibrary.RingTheory.«FIELD_MONIC_IRREDUCIBLE_ASSOCIATE»
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_DIVISORS := SessionLibrary.Prime.«FINITE_DIVISORS»
  FINITE_FIELD_IRREDUCIBLE_ROOT_POW := SessionLibrary.FiniteFields.«FINITE_FIELD_IRREDUCIBLE_ROOT_POW»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FUN_EQ_THM := Session.FUN_EQ_THM
  GCD := Session.GCD
  GCD_SYM := SessionLibrary.Prime.«GCD_SYM»
  GCD_ZERO := SessionLibrary.Prime.«GCD_ZERO»
  IMP_CONJ := Session.IMP_CONJ
  IMP_IMP := Session.IMP_IMP
  INDEX_DECOMPOSITION_PRIME := SessionLibrary.Prime.«INDEX_DECOMPOSITION_PRIME»
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGER_RING_OF_NUM := SessionLibrary.RingTheory.«INTEGER_RING_OF_NUM»
  INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING»
  INTEGRAL_DOMAIN_INTEGER_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_INTEGER_RING»
  INTEGRAL_DOMAIN_NONTRIVIAL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_NONTRIVIAL»
  INTEGRAL_DOMAIN_POLY_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_POLY_RING»
  INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE»
  INTEGRAL_DOMAIN_PRODUCT_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_PRODUCT_EQ_0»
  INTEGRAL_DOMAIN_REGULAR := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_REGULAR»
  INT_EQ_MUL_RCANCEL := Session.INT_EQ_MUL_RCANCEL
  INT_MUL_LID := Session.INT_MUL_LID
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  IN_DELETE := Session.IN_DELETE
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_INTER := Session.IN_INTER
  IN_NUMSEG := Session.IN_NUMSEG
  IN_RING_POLYNOMIAL_CARRIER_COMPOSE := SessionLibrary.RingTheory.«IN_RING_POLYNOMIAL_CARRIER_COMPOSE»
  IN_SING := Session.IN_SING
  IN_UNION := Session.IN_UNION
  IRREDUCIBLE_IMP_POLY_DEG_NZ := SessionLibrary.RingTheory.«IRREDUCIBLE_IMP_POLY_DEG_NZ»
  LE := Session.LE
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LET_TRANS := Session.LET_TRANS
  LE_ANTISYM := Session.LE_ANTISYM
  LE_EXP := Session.LE_EXP
  LE_REFL := Session.LE_REFL
  LT_LE := Session.LT_LE
  LT_MULT_LCANCEL := Session.LT_MULT_LCANCEL
  LT_REFL := Session.LT_REFL
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONIC_ASSOCIATES_EQ := SessionLibrary.RingTheory.«MONIC_ASSOCIATES_EQ»
  MONIC_IMP_NONZERO := SessionLibrary.RingTheory.«MONIC_IMP_NONZERO»
  MONIC_IN_TRIVIAL_RING := SessionLibrary.RingTheory.«MONIC_IN_TRIVIAL_RING»
  MONIC_POLY_1 := SessionLibrary.RingTheory.«MONIC_POLY_1»
  MONIC_POLY_EQ_ROOTS_PRODUCT := SessionLibrary.RingTheory.«MONIC_POLY_EQ_ROOTS_PRODUCT»
  MONIC_POLY_POW := SessionLibrary.RingTheory.«MONIC_POLY_POW»
  MONIC_POLY_PRODUCT := SessionLibrary.RingTheory.«MONIC_POLY_PRODUCT»
  MULT_ASSOC := Session.MULT_ASSOC
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_SYM := Session.MULT_SYM
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LT := Session.NOT_LT
  NSUM_CLAUSES := Session.NSUM_CLAUSES
  NSUM_CONST := Session.NSUM_CONST
  NSUM_EQ := Session.NSUM_EQ
  NUMSEG_LT := Session.NUMSEG_LT
  ORDER_DIVIDES := SessionLibrary.Pocklington.«ORDER_DIVIDES»
  PHI_0 := SessionLibrary.Pocklington.«PHI_0»
  PHI_1 := SessionLibrary.Pocklington.«PHI_1»
  PHI_ALT := SessionLibrary.Pocklington.«PHI_ALT»
  PHI_DIVISORSUM := SessionLibrary.Multiplicative.«PHI_DIVISORSUM»
  PHI_PRIMEPOW_SUC := SessionLibrary.Pocklington.«PHI_PRIMEPOW_SUC»
  PID_IMP_UFD := SessionLibrary.RingTheory.«PID_IMP_UFD»
  PID_POLY_RING := SessionLibrary.RingTheory.«PID_POLY_RING»
  POLY_CLAUSES := SessionLibrary.RingTheory.«POLY_CLAUSES»
  POLY_COMPOSE_HOMOMORPHISM_CONST := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_CONST»
  POLY_COMPOSE_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_POW»
  POLY_COMPOSE_HOMOMORPHISM_SUB := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_SUB»
  POLY_COMPOSE_HOMOMORPHISM_VAR := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_VAR»
  POLY_CONST := SessionLibrary.RingTheory.«POLY_CONST»
  POLY_CONST_DIVIDES_COEFFS_EQ := SessionLibrary.RingTheory.«POLY_CONST_DIVIDES_COEFFS_EQ»
  POLY_CONST_EQ_0 := SessionLibrary.RingTheory.«POLY_CONST_EQ_0»
  POLY_DEG_0 := SessionLibrary.RingTheory.«POLY_DEG_0»
  POLY_DEG_1 := SessionLibrary.RingTheory.«POLY_DEG_1»
  POLY_DEG_CONST := SessionLibrary.RingTheory.«POLY_DEG_CONST»
  POLY_DEG_DIVIDES_LE := SessionLibrary.RingTheory.«POLY_DEG_DIVIDES_LE»
  POLY_DEG_EQ_0 := SessionLibrary.RingTheory.«POLY_DEG_EQ_0»
  POLY_DEG_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_DEG_MONOMORPHIC_IMAGE»
  POLY_DEG_PRODUCT_MONIC := SessionLibrary.RingTheory.«POLY_DEG_PRODUCT_MONIC»
  POLY_DEG_RMUL_MONIC := SessionLibrary.RingTheory.«POLY_DEG_RMUL_MONIC»
  POLY_DEG_SUB_CONST := SessionLibrary.RingTheory.«POLY_DEG_SUB_CONST»
  POLY_DEG_VAR_POW := SessionLibrary.RingTheory.«POLY_DEG_VAR_POW»
  POLY_DERIV_1 := SessionLibrary.RingTheory.«POLY_DERIV_1»
  POLY_DERIV_SUB := SessionLibrary.RingTheory.«POLY_DERIV_SUB»
  POLY_DERIV_VAR_POW := SessionLibrary.RingTheory.«POLY_DERIV_VAR_POW»
  POLY_DIV := SessionLibrary.RingTheory.«POLY_DIV»
  POLY_DIVIDES_X_MINUS_ROOT := SessionLibrary.RingTheory.«POLY_DIVIDES_X_MINUS_ROOT»
  POLY_DIVIDES_X_MINUS_ROOT_EQ := SessionLibrary.RingTheory.«POLY_DIVIDES_X_MINUS_ROOT_EQ»
  POLY_DIV_REM_SIMP := SessionLibrary.RingTheory.«POLY_DIV_REM_SIMP»
/-- The core theorems cyclotomic_poly.ml uses. -/
def core2 : HolANT.CyclotomicPoly.CoreThms2 where
  POLY_EVAL := SessionLibrary.RingTheory.«POLY_EVAL»
  POLY_EVAL_1 := SessionLibrary.RingTheory.«POLY_EVAL_1»
  POLY_EVAL_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_EVAL_HOMOMORPHIC_IMAGE»
  POLY_EVAL_MUL := SessionLibrary.RingTheory.«POLY_EVAL_MUL»
  POLY_EVAL_POW := SessionLibrary.RingTheory.«POLY_EVAL_POW»
  POLY_EVAL_RING_PRODUCT := SessionLibrary.RingTheory.«POLY_EVAL_RING_PRODUCT»
  POLY_EVAL_RING_SUM := SessionLibrary.RingTheory.«POLY_EVAL_RING_SUM»
  POLY_EVAL_SUB := SessionLibrary.RingTheory.«POLY_EVAL_SUB»
  POLY_EVAL_VAR := SessionLibrary.RingTheory.«POLY_EVAL_VAR»
  POLY_MUL_0 := SessionLibrary.RingTheory.«POLY_MUL_0»
  POLY_MUL_LEADING_COEFF := SessionLibrary.RingTheory.«POLY_MUL_LEADING_COEFF»
  POLY_REM_UNIQUE := SessionLibrary.RingTheory.«POLY_REM_UNIQUE»
  POLY_RING_CLAUSES := SessionLibrary.RingTheory.«POLY_RING_CLAUSES»
  POLY_SEPARABLE_IMP_SQUAREFREE := SessionLibrary.RingTheory.«POLY_SEPARABLE_IMP_SQUAREFREE»
  POLY_TOP_NONZERO := SessionLibrary.RingTheory.«POLY_TOP_NONZERO»
  POLY_VAR_UNIV := SessionLibrary.RingTheory.«POLY_VAR_UNIV»
  POLY_X_MINUS_A_IN_CARRIER := SessionLibrary.RingTheory.«POLY_X_MINUS_A_IN_CARRIER»
  PRIME_COPRIME_EQ := SessionLibrary.Prime.«PRIME_COPRIME_EQ»
  PRIME_DIVEXP := SessionLibrary.Prime.«PRIME_DIVEXP»
  PRIME_FACTOR := SessionLibrary.Prime.«PRIME_FACTOR»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  RIGHT_EXISTS_IMP_THM := Session.RIGHT_EXISTS_IMP_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_ASSOCIATES_PRODUCT := SessionLibrary.RingTheory.«RING_ASSOCIATES_PRODUCT»
  RING_ASSOCIATES_SYM := SessionLibrary.RingTheory.«RING_ASSOCIATES_SYM»
  RING_ASSOCIATES_TRANS := SessionLibrary.RingTheory.«RING_ASSOCIATES_TRANS»
  RING_CHAR_DIVIDES_ORDER := SessionLibrary.RingTheory.«RING_CHAR_DIVIDES_ORDER»
  RING_CHAR_EQ_1 := SessionLibrary.RingTheory.«RING_CHAR_EQ_1»
  RING_CHAR_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_CHAR_MONOMORPHIC_IMAGE»
  RING_CHAR_POLY_RING := SessionLibrary.RingTheory.«RING_CHAR_POLY_RING»
  RING_COPRIME_PRODUCT_DIVIDES := SessionLibrary.RingTheory.«RING_COPRIME_PRODUCT_DIVIDES»
  RING_COPRIME_SYM := SessionLibrary.RingTheory.«RING_COPRIME_SYM»
  RING_DIVIDES_0 := SessionLibrary.RingTheory.«RING_DIVIDES_0»
  RING_DIVIDES_IN_CARRIER := SessionLibrary.RingTheory.«RING_DIVIDES_IN_CARRIER»
  RING_DIVIDES_IRREDUCIBLE_ROOT := SessionLibrary.FieldTheory.«RING_DIVIDES_IRREDUCIBLE_ROOT»
  RING_DIVIDES_LMUL := SessionLibrary.RingTheory.«RING_DIVIDES_LMUL»
  RING_DIVIDES_MUL2 := SessionLibrary.RingTheory.«RING_DIVIDES_MUL2»
  RING_DIVIDES_PRODUCT_SUBSET := SessionLibrary.RingTheory.«RING_DIVIDES_PRODUCT_SUBSET»
  RING_DIVIDES_REFL := SessionLibrary.RingTheory.«RING_DIVIDES_REFL»
  RING_DIVIDES_RMUL := SessionLibrary.RingTheory.«RING_DIVIDES_RMUL»
  RING_DIVIDES_SUB := SessionLibrary.RingTheory.«RING_DIVIDES_SUB»
  RING_DIVIDES_SUB_POW := SessionLibrary.RingTheory.«RING_DIVIDES_SUB_POW»
  RING_DIVIDES_TRANS := SessionLibrary.RingTheory.«RING_DIVIDES_TRANS»
  RING_ENDOMORPHISM_FROBENIUS_ITERATE := SessionLibrary.RingTheory.«RING_ENDOMORPHISM_FROBENIUS_ITERATE»
  RING_GEOM_SERIES := SessionLibrary.RingTheory.«RING_GEOM_SERIES»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_POLY_RINGS := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_RINGS»
  RING_HOMOMORPHISM_PRODUCT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_PRODUCT»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_SUB := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUB»
  RING_IRREDUCIBLE_IN_CARRIER := SessionLibrary.RingTheory.«RING_IRREDUCIBLE_IN_CARRIER»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_LCANCEL := SessionLibrary.RingTheory.«RING_MUL_LCANCEL»
  RING_MUL_RCANCEL := SessionLibrary.RingTheory.«RING_MUL_RCANCEL»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_0 := SessionLibrary.RingTheory.«RING_OF_NUM_0»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_ORDER_0 := SessionLibrary.RingTheory.«RING_ORDER_0»
  RING_ORDER_POW_GEN := SessionLibrary.RingTheory.«RING_ORDER_POW_GEN»
  RING_POLYNOMIAL := SessionLibrary.RingTheory.«RING_POLYNOMIAL»
  RING_POLYNOMIAL_1 := SessionLibrary.RingTheory.«RING_POLYNOMIAL_1»
  RING_POLYNOMIAL_IMP_POWERSERIES := SessionLibrary.RingTheory.«RING_POLYNOMIAL_IMP_POWERSERIES»
  RING_POLYNOMIAL_POW := SessionLibrary.RingTheory.«RING_POLYNOMIAL_POW»
  RING_POLYNOMIAL_SUB := SessionLibrary.RingTheory.«RING_POLYNOMIAL_SUB»
  RING_POLYNOMIAL_VAR := SessionLibrary.RingTheory.«RING_POLYNOMIAL_VAR»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POWERSERIES_CONST := SessionLibrary.RingTheory.«RING_POWERSERIES_CONST»
  RING_POWERSERIES_POW := SessionLibrary.RingTheory.«RING_POWERSERIES_POW»
  RING_POWERSERIES_VAR := SessionLibrary.RingTheory.«RING_POWERSERIES_VAR»
  RING_POW_1 := SessionLibrary.RingTheory.«RING_POW_1»
  RING_POW_2 := SessionLibrary.RingTheory.«RING_POW_2»
  RING_POW_ADD := SessionLibrary.RingTheory.«RING_POW_ADD»
  RING_POW_EQ := SessionLibrary.RingTheory.«RING_POW_EQ»
  RING_POW_EQ_1 := SessionLibrary.RingTheory.«RING_POW_EQ_1»
  RING_POW_EQ_LT_EQ := SessionLibrary.RingTheory.«RING_POW_EQ_LT_EQ»
  RING_POW_ONE := SessionLibrary.RingTheory.«RING_POW_ONE»
  RING_POW_POW := SessionLibrary.RingTheory.«RING_POW_POW»
  RING_POW_ZERO := SessionLibrary.RingTheory.«RING_POW_ZERO»
  RING_PRODUCT := SessionLibrary.RingTheory.«RING_PRODUCT»
  RING_PRODUCT_CLAUSES := SessionLibrary.RingTheory.«RING_PRODUCT_CLAUSES»
  RING_PRODUCT_CONST := SessionLibrary.RingTheory.«RING_PRODUCT_CONST»
  RING_PRODUCT_DELTA := SessionLibrary.RingTheory.«RING_PRODUCT_DELTA»
  RING_PRODUCT_EQ := SessionLibrary.RingTheory.«RING_PRODUCT_EQ»
  RING_PRODUCT_IMAGE := SessionLibrary.RingTheory.«RING_PRODUCT_IMAGE»
  RING_PRODUCT_IMAGE_GEN := SessionLibrary.RingTheory.«RING_PRODUCT_IMAGE_GEN»
  RING_PRODUCT_POW := SessionLibrary.RingTheory.«RING_PRODUCT_POW»
  RING_PRODUCT_SING := SessionLibrary.RingTheory.«RING_PRODUCT_SING»
  RING_PRODUCT_UNION := SessionLibrary.RingTheory.«RING_PRODUCT_UNION»
  RING_PRODUCT_ZERO := SessionLibrary.RingTheory.«RING_PRODUCT_ZERO»
  RING_SQUAREFREE_DIVISOR := SessionLibrary.RingTheory.«RING_SQUAREFREE_DIVISOR»
  RING_SQUAREFREE_POW := SessionLibrary.RingTheory.«RING_SQUAREFREE_POW»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_LZERO := SessionLibrary.RingTheory.«RING_SUB_LZERO»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_SUB_RZERO := SessionLibrary.RingTheory.«RING_SUB_RZERO»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_CONST := SessionLibrary.RingTheory.«RING_SUM_CONST»
  RING_UNIT_1 := SessionLibrary.RingTheory.«RING_UNIT_1»
  RING_UNIT_DIVIDES := SessionLibrary.RingTheory.«RING_UNIT_DIVIDES»
  RING_UNIT_IMP_REGULAR := SessionLibrary.RingTheory.«RING_UNIT_IMP_REGULAR»
  RING_UNIT_POLY_CONST := SessionLibrary.RingTheory.«RING_UNIT_POLY_CONST»
  RING_UNIT_X_MINUS_A := SessionLibrary.RingTheory.«RING_UNIT_X_MINUS_A»
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  TRIVIAL_RING_10 := SessionLibrary.RingTheory.«TRIVIAL_RING_10»
  TRIVIAL_RING_POLY_0 := SessionLibrary.RingTheory.«TRIVIAL_RING_POLY_0»
  UFD_EQ_PRIMEFACT := SessionLibrary.RingTheory.«UFD_EQ_PRIMEFACT»
  UFD_INTEGER_RING := SessionLibrary.RingTheory.«UFD_INTEGER_RING»
  UFD_POLY_RING := SessionLibrary.RingTheory.«UFD_POLY_RING»
  WF_REC := Session.WF_REC
  WF_num := Session.WF_num
  algebraic_extension := SessionLibrary.FieldTheory.«algebraic_extension»
  algebraically_closed_field := SessionLibrary.FieldTheory.«algebraically_closed_field»
  divides := Session.divides
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  monic := SessionLibrary.RingTheory.«monic»
  num_CASES := Session.num_CASES
  num_WF := Session.num_WF
  o_ASSOC := Session.o_ASSOC
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM
  pairwise := Session.pairwise
  poly_1 := SessionLibrary.RingTheory.«poly_1»
  poly_separable := SessionLibrary.RingTheory.«poly_separable»
  ring_coprime := SessionLibrary.RingTheory.«ring_coprime»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_endomorphism := SessionLibrary.RingTheory.«ring_endomorphism»
  ring_irreducible := SessionLibrary.RingTheory.«ring_irreducible»
  ring_of_num := SessionLibrary.RingTheory.«ring_of_num»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_regular := SessionLibrary.RingTheory.«ring_regular»
  ring_squarefree := SessionLibrary.RingTheory.«ring_squarefree»
  ring_zerodivisor := SessionLibrary.RingTheory.«ring_zerodivisor»

/-- What cyclotomic_poly.ml uses from Session. -/
def deps : HolANT.CyclotomicPoly.CyclotomicPolyDeps where
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
  new_specification names th := ExceptT.mk (Session.new_specification names th)
  core1 := core1
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in cyclotomic_poly.ml order. -/
initialize BCyclotomicPoly01 : HolANT.CyclotomicPoly.CyclotomicPoly01 ←
  ioB "setupCyclotomicPoly01" (HolANT.CyclotomicPoly.setupCyclotomicPoly01 deps).run
initialize BCyclotomicPoly02 : HolANT.CyclotomicPoly.CyclotomicPoly02 ←
  ioB "setupCyclotomicPoly02" (HolANT.CyclotomicPoly.setupCyclotomicPoly02 deps BCyclotomicPoly01).run

-- CyclotomicPoly01
def cyclotomic_poly : thm := BCyclotomicPoly01.cyclotomic_poly
def RING_REGULAR_POLY_UNIT_LEADING : thm := BCyclotomicPoly01.RING_REGULAR_POLY_UNIT_LEADING
def POLY_DIV_MUL : thm := BCyclotomicPoly01.POLY_DIV_MUL
def MONIC_POLY_MUL_EQ : thm := BCyclotomicPoly01.MONIC_POLY_MUL_EQ
def POLY_DEG_VAR_POW_SUB_1 : thm := BCyclotomicPoly01.POLY_DEG_VAR_POW_SUB_1
def MONIC_POLY_VAR_POW_SUB_1 : thm := BCyclotomicPoly01.MONIC_POLY_VAR_POW_SUB_1
def POLY_DERIV_VAR_POW_SUB_1 : thm := BCyclotomicPoly01.POLY_DERIV_VAR_POW_SUB_1
def POLY_SEPARABLE_VAR_POW_SUB_1 : thm := BCyclotomicPoly01.POLY_SEPARABLE_VAR_POW_SUB_1
def RING_DIVIDES_POW_SUB_1 : thm := BCyclotomicPoly01.RING_DIVIDES_POW_SUB_1
def POLY_VAR_POW_SUB_1_HOMOMORPHIC_IMAGE : thm := BCyclotomicPoly01.POLY_VAR_POW_SUB_1_HOMOMORPHIC_IMAGE
def FINITE_DIVISORS_LT : thm := BCyclotomicPoly01.FINITE_DIVISORS_LT
def DIVISORS_INSERT_LT : thm := BCyclotomicPoly01.DIVISORS_INSERT_LT
def RING_PRODUCT_DIVISORS : thm := BCyclotomicPoly01.RING_PRODUCT_DIVISORS
def CYCLOTOMIC_POLY_0 : thm := BCyclotomicPoly01.CYCLOTOMIC_POLY_0
def CYCLOTOMIC_POLY_IN_CARRIER : thm := BCyclotomicPoly01.CYCLOTOMIC_POLY_IN_CARRIER
def CYCLOTOMIC_POLY_1 : thm := BCyclotomicPoly01.CYCLOTOMIC_POLY_1
def CYCLOTOMIC_POLY_UNIQUE : thm := BCyclotomicPoly01.CYCLOTOMIC_POLY_UNIQUE
def CYCLOTOMIC_POLY_INTEGER_PRODUCT : thm := BCyclotomicPoly01.CYCLOTOMIC_POLY_INTEGER_PRODUCT
def CYCLOTOMIC_POLY_RING_OF_INT : thm := BCyclotomicPoly01.CYCLOTOMIC_POLY_RING_OF_INT
def CYCLOTOMIC_POLY_MONIC : thm := BCyclotomicPoly01.CYCLOTOMIC_POLY_MONIC
def CYCLOTOMIC_POLY_PRODUCT : thm := BCyclotomicPoly01.CYCLOTOMIC_POLY_PRODUCT
def CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE : thm := BCyclotomicPoly01.CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE
def CYCLOTOMIC_POLY_DEG : thm := BCyclotomicPoly01.CYCLOTOMIC_POLY_DEG
def CYCLOTOMIC_POLY_ROOT : thm := BCyclotomicPoly01.CYCLOTOMIC_POLY_ROOT
def CYCLOTOMIC_POLY_ROOT_EQ : thm := BCyclotomicPoly01.CYCLOTOMIC_POLY_ROOT_EQ
def POLY_VAR_POW_SUB_1_PRODUCT : thm := BCyclotomicPoly01.POLY_VAR_POW_SUB_1_PRODUCT
def CYCLOTOMIC_POLY_SPLITS : thm := BCyclotomicPoly01.CYCLOTOMIC_POLY_SPLITS

-- CyclotomicPoly02
def CYCLOTOMIC_POLY_PRODUCT_NONDIVISORS : thm := BCyclotomicPoly02.CYCLOTOMIC_POLY_PRODUCT_NONDIVISORS
def CYCLOTOMIC_POLY_PRIME_POWER : thm := BCyclotomicPoly02.CYCLOTOMIC_POLY_PRIME_POWER
def CYCLOTOMIC_POLY_EVAL_1_PRIME_POWER : thm := BCyclotomicPoly02.CYCLOTOMIC_POLY_EVAL_1_PRIME_POWER
def CYCLOTOMIC_POLY_EVAL_1 : thm := BCyclotomicPoly02.CYCLOTOMIC_POLY_EVAL_1
def CYCLOTOMIC_POLY_EVAL_0 : thm := BCyclotomicPoly02.CYCLOTOMIC_POLY_EVAL_0
def CYCLOTOMIC_POLY_SQUAREFREE : thm := BCyclotomicPoly02.CYCLOTOMIC_POLY_SQUAREFREE
def CYCLOTOMIC_POLY_RING_CHAR : thm := BCyclotomicPoly02.CYCLOTOMIC_POLY_RING_CHAR
def CYCLOTOMIC_POLY_IRREDUCIBLE_FACTOR_DEG : thm := BCyclotomicPoly02.CYCLOTOMIC_POLY_IRREDUCIBLE_FACTOR_DEG
def MONIC_POLY_IRREDUCIBLE_FACTORIZATION : thm := BCyclotomicPoly02.MONIC_POLY_IRREDUCIBLE_FACTORIZATION
def CYCLOTOMIC_POLY_IRREDUCIBLE_FACTORIZATION : thm := BCyclotomicPoly02.CYCLOTOMIC_POLY_IRREDUCIBLE_FACTORIZATION

/-- `needs "ANT/cyclotomic_poly.ml"`: already done by importing this module. -/
def ensureCyclotomicPoly : IO Unit := pure ()

end SessionANT.CyclotomicPoly
