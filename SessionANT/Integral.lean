/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/integral.ml                                   . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/Integral.lean

  The session half of the integral.ml translation: it supplies HolANT.Integral's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/integral.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.Integral
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.Integral

/-- The core theorems integral.ml uses. -/
def core1 : HolANT.Integral.CoreThms1 where
  ALGEBRAIC_OVER_IN_CARRIER := SessionLibrary.FieldTheory.«ALGEBRAIC_OVER_IN_CARRIER»
  ALGEBRA_NORM_1 := SessionLibrary.RingDet.«ALGEBRA_NORM_1»
  ALGEBRA_NORM_MINIMAL_POLYNOMIAL := SessionLibrary.FieldTheory.«ALGEBRA_NORM_MINIMAL_POLYNOMIAL»
  ALGEBRA_NORM_MUL := SessionLibrary.RingDet.«ALGEBRA_NORM_MUL»
  ALGEBRA_TRACE_MINIMAL_POLYNOMIAL := SessionLibrary.FieldTheory.«ALGEBRA_TRACE_MINIMAL_POLYNOMIAL»
  ARITH := Session.ARITH
  CARRIER_SUBRING_GENERATED_SUBRING := SessionLibrary.RingTheory.«CARRIER_SUBRING_GENERATED_SUBRING»
  COEFF := SessionLibrary.RingTheory.«COEFF»
  COEFF_COMPOSE := SessionLibrary.RingTheory.«COEFF_COMPOSE»
  COEFF_IN_CARRIER_ALT := SessionLibrary.RingTheory.«COEFF_IN_CARRIER_ALT»
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EQ_IMP := Session.EQ_IMP
  EQ_TRANS := Session.EQ_TRANS
  EXTENSION_DEGREE_EQ_0 := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_EQ_0»
  FIELD_EXTENSION_IMP_HOMOMORPHISM := SessionLibrary.FieldTheory.«FIELD_EXTENSION_IMP_HOMOMORPHISM»
  FIELD_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_IMP_PID := SessionLibrary.RingTheory.«FIELD_IMP_PID»
  FIELD_MUL_LINV := SessionLibrary.RingTheory.«FIELD_MUL_LINV»
  FIELD_MUL_RINV := SessionLibrary.RingTheory.«FIELD_MUL_RINV»
  FIELD_OF_FRACTIONS_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_OF_FRACTIONS_IMP_INTEGRAL_DOMAIN»
  FIELD_REGULAR := SessionLibrary.RingTheory.«FIELD_REGULAR»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FIELD_UNIT := SessionLibrary.RingTheory.«FIELD_UNIT»
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FINITE_EXTENSION_SUBFIELD_GENERATED»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_FIELD_EXTENSION»
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_PRODUCT_DEPENDENT := Session.FINITE_PRODUCT_DEPENDENT
  FINITE_SING := Session.FINITE_SING
  FORALL_AND_THM := Session.FORALL_AND_THM
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FUN_EQ_THM := Session.FUN_EQ_THM
  IDEAL_GENERATED_ADJOIN_EXPLICIT := SessionLibrary.RingTheory.«IDEAL_GENERATED_ADJOIN_EXPLICIT»
  IDEAL_GENERATED_INC := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC»
  IMP_CONJ := Session.IMP_CONJ
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGRAL_DOMAIN_LOCALIZATION := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_LOCALIZATION»
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_POW_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_POW_EQ_0»
  INTEGRAL_DOMAIN_REGULAR := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_REGULAR»
  INTEGRAL_DOMAIN_SUBRING_GENERATED := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_SUBRING_GENERATED»
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_NUMSEG := Session.IN_NUMSEG
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_RING_POLYNOMIAL_CARRIER_COMPOSE := SessionLibrary.RingTheory.«IN_RING_POLYNOMIAL_CARRIER_COMPOSE»
  IN_SING := Session.IN_SING
  IN_SUBRING_1 := SessionLibrary.RingTheory.«IN_SUBRING_1»
  IN_SUBRING_ADD := SessionLibrary.RingTheory.«IN_SUBRING_ADD»
  IN_SUBRING_MUL := SessionLibrary.RingTheory.«IN_SUBRING_MUL»
  IN_SUBRING_NEG := SessionLibrary.RingTheory.«IN_SUBRING_NEG»
  IN_SUBRING_NUM := SessionLibrary.RingTheory.«IN_SUBRING_NUM»
  IN_SUBRING_POW := SessionLibrary.RingTheory.«IN_SUBRING_POW»
  IN_SUBRING_SUM := SessionLibrary.RingTheory.«IN_SUBRING_SUM»
  IN_UNIV := Session.IN_UNIV
  IRREDUCIBLE_IMP_POLY_DEG_NZ := SessionLibrary.RingTheory.«IRREDUCIBLE_IMP_POLY_DEG_NZ»
  I_DEF := Session.I_DEF
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LEFT_AND_EXISTS_THM := Session.LEFT_AND_EXISTS_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_1 := Session.LE_1
  LOCALEQUIV_MUL_LCANCEL := SessionLibrary.RingTheory.«LOCALEQUIV_MUL_LCANCEL»
  LOCALEQUIV_MUL_RCANCEL := SessionLibrary.RingTheory.«LOCALEQUIV_MUL_RCANCEL»
  LT := Session.LT
  LT_0 := Session.LT_0
  MINIMAL_POLYNOMIAL := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL»
  MINIMAL_POLYNOMIAL_DIVIDES := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_DIVIDES»
  MINIMAL_POLYNOMIAL_IN_CARRIER := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_IN_CARRIER»
  MINIMAL_POLYNOMIAL_MONIC := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_MONIC»
  MONIC_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«MONIC_HOMOMORPHIC_IMAGE»
  MONIC_IMP_NONZERO := SessionLibrary.RingTheory.«MONIC_IMP_NONZERO»
  MONIC_X_MINUS_A := SessionLibrary.RingTheory.«MONIC_X_MINUS_A»
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_SUC := Session.NOT_SUC
  NUMSEG_LT := Session.NUMSEG_LT
  PID_IMP_UFD := SessionLibrary.RingTheory.«PID_IMP_UFD»
  POLY_DEG_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_DEG_MONOMORPHIC_IMAGE»
  POLY_EVAL := SessionLibrary.RingTheory.«POLY_EVAL»
  POLY_EVAL_MUL := SessionLibrary.RingTheory.«POLY_EVAL_MUL»
  POLY_EXTEND := SessionLibrary.RingTheory.«POLY_EXTEND»
  POLY_EXTEND_CONST := SessionLibrary.RingTheory.«POLY_EXTEND_CONST»
  POLY_EXTEND_EVALUATE := SessionLibrary.RingTheory.«POLY_EXTEND_EVALUATE»
  POLY_EXTEND_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_EXTEND_HOMOMORPHIC_IMAGE»
  POLY_EXTEND_INTO_SUBRING_GENERATED := SessionLibrary.RingTheory.«POLY_EXTEND_INTO_SUBRING_GENERATED»
  POLY_EXTEND_MONIC_UNIVARIATE := SessionLibrary.RingTheory.«POLY_EXTEND_MONIC_UNIVARIATE»
  POLY_EXTEND_SUB := SessionLibrary.RingTheory.«POLY_EXTEND_SUB»
  POLY_EXTEND_VAR := SessionLibrary.RingTheory.«POLY_EXTEND_VAR»
  POLY_MONOMIAL_IN_CARRIER := SessionLibrary.RingTheory.«POLY_MONOMIAL_IN_CARRIER»
  POLY_RING_CLAUSES := SessionLibrary.RingTheory.«POLY_RING_CLAUSES»
  POLY_SPLITS_IN_CARRIER := SessionLibrary.RingTheory.«POLY_SPLITS_IN_CARRIER»
  POLY_SPLITS_IN_SUBRING_MONIC := SessionLibrary.RingTheory.«POLY_SPLITS_IN_SUBRING_MONIC»
  RIGHT_AND_EXISTS_THM := Session.RIGHT_AND_EXISTS_THM
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_LDISTRIB := SessionLibrary.RingTheory.«RING_ADD_LDISTRIB»
  RING_ADD_RDISTRIB := SessionLibrary.RingTheory.«RING_ADD_RDISTRIB»
  RING_ADD_RNEG := SessionLibrary.RingTheory.«RING_ADD_RNEG»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_ASSOCIATES_DIVIDES := SessionLibrary.RingTheory.«RING_ASSOCIATES_DIVIDES»
  RING_ASSOCIATES_EQ_0 := SessionLibrary.RingTheory.«RING_ASSOCIATES_EQ_0»
  RING_ASSOCIATES_LMUL := SessionLibrary.RingTheory.«RING_ASSOCIATES_LMUL»
  RING_ASSOCIATES_SYM := SessionLibrary.RingTheory.«RING_ASSOCIATES_SYM»
  RING_ASSOCIATES_TRANS := SessionLibrary.RingTheory.«RING_ASSOCIATES_TRANS»
  RING_CARRIER_SUBRING_GENERATED_0 := SessionLibrary.RingTheory.«RING_CARRIER_SUBRING_GENERATED_0»
  RING_CHARPOLY := SessionLibrary.RingDet.«RING_CHARPOLY»
  RING_CHARPOLY_EXTEND := SessionLibrary.RingDet.«RING_CHARPOLY_EXTEND»
  RING_CHARPOLY_MONIC := SessionLibrary.RingDet.«RING_CHARPOLY_MONIC»
  RING_DET := SessionLibrary.RingDet.«RING_DET»
  RING_DET_DEPENDENT_COLUMNS_MUL := SessionLibrary.RingDet.«RING_DET_DEPENDENT_COLUMNS_MUL»
  RING_DIVIDES_0 := SessionLibrary.RingTheory.«RING_DIVIDES_0»
  RING_DIVIDES_ADD := SessionLibrary.RingTheory.«RING_DIVIDES_ADD»
  RING_DIVIDES_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_DIVIDES_HOMOMORPHIC_IMAGE»
  RING_DIVIDES_LMUL := SessionLibrary.RingTheory.«RING_DIVIDES_LMUL»
/-- The core theorems integral.ml uses. -/
def core2 : HolANT.Integral.CoreThms2 where
  RING_DIVIDES_LMUL2 := SessionLibrary.RingTheory.«RING_DIVIDES_LMUL2»
  RING_DIVIDES_NEG := SessionLibrary.RingTheory.«RING_DIVIDES_NEG»
  RING_DIVIDES_REFL := SessionLibrary.RingTheory.«RING_DIVIDES_REFL»
  RING_DIVIDES_RMUL := SessionLibrary.RingTheory.«RING_DIVIDES_RMUL»
  RING_DIVIDES_ZERO := SessionLibrary.RingTheory.«RING_DIVIDES_ZERO»
  RING_FRACTIONATE_IN_CARRIER := SessionLibrary.RingTheory.«RING_FRACTIONATE_IN_CARRIER»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_FRACTIONATE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_FRACTIONATE»
  RING_HOMOMORPHISM_INCLUSION := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INCLUSION»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_INTO_SUBRING_EQ := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTO_SUBRING_EQ»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_NEG := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_NEG»
  RING_HOMOMORPHISM_POLY_RINGS := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_RINGS»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_SUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM»
  RING_IDEAL_CARRIER := SessionLibrary.RingTheory.«RING_IDEAL_CARRIER»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_LOCALEQUIV_IN_CARRIER := SessionLibrary.RingTheory.«RING_LOCALEQUIV_IN_CARRIER»
  RING_LOCALIZATION_CARRIER := SessionLibrary.RingTheory.«RING_LOCALIZATION_CARRIER»
  RING_MONIC_RELATION_FACTOR := SessionLibrary.RingTheory.«RING_MONIC_RELATION_FACTOR»
  RING_MONOMORPHISM_ALT := SessionLibrary.RingTheory.«RING_MONOMORPHISM_ALT»
  RING_MONOMORPHISM_EQ_0 := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EQ_0»
  RING_MONOMORPHISM_FRACTIONATE := SessionLibrary.RingTheory.«RING_MONOMORPHISM_FRACTIONATE»
  RING_MONOMORPHISM_FRACTIONATE_GEN := SessionLibrary.RingTheory.«RING_MONOMORPHISM_FRACTIONATE_GEN»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INTEGER_RING_OF_INT»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MULTSYS := SessionLibrary.RingTheory.«RING_MULTSYS»
  RING_MULTSYS_REGULAR := SessionLibrary.RingTheory.«RING_MULTSYS_REGULAR»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LINV := SessionLibrary.RingTheory.«RING_MUL_LINV»
  RING_MUL_LNEG := SessionLibrary.RingTheory.«RING_MUL_LNEG»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_POW := SessionLibrary.RingTheory.«RING_MUL_POW»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RNEG := SessionLibrary.RingTheory.«RING_MUL_RNEG»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_NEG_IN_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_NEG_IN_SUBRING_GENERATED»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_POLYNOMIAL := SessionLibrary.RingTheory.«RING_POLYNOMIAL»
  RING_POLYNOMIAL_CONST := SessionLibrary.RingTheory.«RING_POLYNOMIAL_CONST»
  RING_POLYNOMIAL_SUB := SessionLibrary.RingTheory.«RING_POLYNOMIAL_SUB»
  RING_POLYNOMIAL_VAR := SessionLibrary.RingTheory.«RING_POLYNOMIAL_VAR»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_ADD := SessionLibrary.RingTheory.«RING_POW_ADD»
  RING_POW_ONE := SessionLibrary.RingTheory.«RING_POW_ONE»
  RING_POW_ZERO := SessionLibrary.RingTheory.«RING_POW_ZERO»
  RING_PRIME_DIVIDES_POW := SessionLibrary.RingTheory.«RING_PRIME_DIVIDES_POW»
  RING_REGULAR_IN_CARRIER := SessionLibrary.RingTheory.«RING_REGULAR_IN_CARRIER»
  RING_REGULAR_POW := SessionLibrary.RingTheory.«RING_REGULAR_POW»
  RING_RNEG_UNIQUE := SessionLibrary.RingTheory.«RING_RNEG_UNIQUE»
  RING_SPAN_0 := SessionLibrary.FieldTheory.«RING_SPAN_0»
  RING_SPAN_ADD := SessionLibrary.FieldTheory.«RING_SPAN_ADD»
  RING_SPAN_FINITE := SessionLibrary.FieldTheory.«RING_SPAN_FINITE»
  RING_SPAN_INC := SessionLibrary.FieldTheory.«RING_SPAN_INC»
  RING_SPAN_MUL := SessionLibrary.FieldTheory.«RING_SPAN_MUL»
  RING_SPAN_NEG := SessionLibrary.FieldTheory.«RING_SPAN_NEG»
  RING_SPAN_SUBSET := SessionLibrary.FieldTheory.«RING_SPAN_SUBSET»
  RING_SPAN_SUM := SessionLibrary.FieldTheory.«RING_SPAN_SUM»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_LDISTRIB := SessionLibrary.RingTheory.«RING_SUB_LDISTRIB»
  RING_SUB_RDISTRIB := SessionLibrary.RingTheory.«RING_SUB_RDISTRIB»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_CLAUSES := SessionLibrary.RingTheory.«RING_SUM_CLAUSES»
  RING_SUM_CLOSED := SessionLibrary.RingTheory.«RING_SUM_CLOSED»
  RING_SUM_DELTA := SessionLibrary.RingTheory.«RING_SUM_DELTA»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_EQ_0 := SessionLibrary.RingTheory.«RING_SUM_EQ_0»
  RING_SUM_LMUL := SessionLibrary.RingTheory.«RING_SUM_LMUL»
  RING_SUM_NEG := SessionLibrary.RingTheory.«RING_SUM_NEG»
  RING_SUM_REFLECT := SessionLibrary.RingTheory.«RING_SUM_REFLECT»
  RING_SUM_SUB := SessionLibrary.RingTheory.«RING_SUM_SUB»
  RING_UNIT_1 := SessionLibrary.RingTheory.«RING_UNIT_1»
  RING_UNIT_DIVIDES_ANY := SessionLibrary.RingTheory.«RING_UNIT_DIVIDES_ANY»
  RING_UNIT_FRACTIONATE := SessionLibrary.RingTheory.«RING_UNIT_FRACTIONATE»
  RING_UNIT_IMP_REGULAR := SessionLibrary.RingTheory.«RING_UNIT_IMP_REGULAR»
  RING_UNIT_IN_CARRIER := SessionLibrary.RingTheory.«RING_UNIT_IN_CARRIER»
  RING_UNIT_MUL_EQ := SessionLibrary.RingTheory.«RING_UNIT_MUL_EQ»
  RING_UNIT_NEG := SessionLibrary.RingTheory.«RING_UNIT_NEG»
  RING_UNIT_POW := SessionLibrary.RingTheory.«RING_UNIT_POW»
  RING_UNIT_POW_EQ := SessionLibrary.RingTheory.«RING_UNIT_POW_EQ»
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SPLITTING_EXTENSION_EXISTS_BIGENOUGH := SessionLibrary.FieldTheory.«SPLITTING_EXTENSION_EXISTS_BIGENOUGH»
  SPLITTING_EXTENSION_SPLITS := SessionLibrary.FieldTheory.«SPLITTING_EXTENSION_SPLITS»
  SPLITTING_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«SPLITTING_IMP_FIELD_EXTENSION»
  SUBFIELD_GENERATED_QUOTIENTS := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_QUOTIENTS»
  SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_GENERATED»
  SUBRING_GENERATED_INC_GEN := SessionLibrary.RingTheory.«SUBRING_GENERATED_INC_GEN»
  SUBSET := Session.SUBSET
  SUB_0 := Session.SUB_0
  SUC_SUB1 := Session.SUC_SUB1
  UFD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«UFD_IMP_INTEGRAL_DOMAIN»
  UFD_INTEGER_RING := SessionLibrary.RingTheory.«UFD_INTEGER_RING»
  UFD_PRIME_FACTOR_INDUCT := SessionLibrary.RingTheory.«UFD_PRIME_FACTOR_INDUCT»
  algebraic_over := SessionLibrary.FieldTheory.«algebraic_over»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  field_of_fractions := SessionLibrary.RingTheory.«field_of_fractions»
  fraction_ring := SessionLibrary.RingTheory.«fraction_ring»
  monic := SessionLibrary.RingTheory.«monic»
  o_ASSOC := Session.o_ASSOC
  o_THM := Session.o_THM
  poly_eval := SessionLibrary.RingTheory.«poly_eval»
  poly_splits_over := SessionLibrary.FieldTheory.«poly_splits_over»
  ring_div := SessionLibrary.RingTheory.«ring_div»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  ring_multsys := SessionLibrary.RingTheory.«ring_multsys»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_prime := SessionLibrary.RingTheory.«ring_prime»
  ring_regular := SessionLibrary.RingTheory.«ring_regular»
  ring_span_INDUCT := SessionLibrary.FieldTheory.«ring_span_INDUCT»
  ring_sub := SessionLibrary.RingTheory.«ring_sub»
  ring_unit := SessionLibrary.RingTheory.«ring_unit»
  ring_zerodivisor := SessionLibrary.RingTheory.«ring_zerodivisor»
  subring_of := SessionLibrary.RingTheory.«subring_of»

/-- What integral.ml uses from Session. -/
def deps : HolANT.Integral.IntegralDeps where
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

/- The bundles, in integral.ml order. -/
initialize BIntegral01 : HolANT.Integral.Integral01 ←
  ioB "setupIntegral01" (HolANT.Integral.setupIntegral01 deps).run
initialize BIntegral02 : HolANT.Integral.Integral02 ←
  ioB "setupIntegral02" (HolANT.Integral.setupIntegral02 deps BIntegral01).run
initialize BIntegral03 : HolANT.Integral.Integral03 ←
  ioB "setupIntegral03" (HolANT.Integral.setupIntegral03 deps BIntegral01 BIntegral02).run
initialize BIntegral04 : HolANT.Integral.Integral04 ←
  ioB "setupIntegral04" (HolANT.Integral.setupIntegral04 deps BIntegral01 BIntegral03).run

-- Integral01
def integral_element : thm := BIntegral01.integral_element
def integrally_closed : thm := BIntegral01.integrally_closed
def INTEGRAL_ELEMENT_IN_CARRIER : thm := BIntegral01.INTEGRAL_ELEMENT_IN_CARRIER
def INTEGRAL_ELEMENT_IMAGE : thm := BIntegral01.INTEGRAL_ELEMENT_IMAGE
def INTEGRAL_ELEMENT_0 : thm := BIntegral01.INTEGRAL_ELEMENT_0
def INTEGRAL_ELEMENT_1 : thm := BIntegral01.INTEGRAL_ELEMENT_1
def INTEGRAL_ELEMENT_RELATION : thm := BIntegral01.INTEGRAL_ELEMENT_RELATION
def INTEGRAL_ELEMENT_FINITE_MODULE : thm := BIntegral01.INTEGRAL_ELEMENT_FINITE_MODULE
def INTEGRAL_ELEMENT_MODULE : thm := BIntegral01.INTEGRAL_ELEMENT_MODULE
def INTEGRAL_SPAN_LMUL : thm := BIntegral01.INTEGRAL_SPAN_LMUL
def INTEGRAL_ELEMENT_SPAN : thm := BIntegral01.INTEGRAL_ELEMENT_SPAN
def INTEGRAL_SPAN_ADJOIN : thm := BIntegral01.INTEGRAL_SPAN_ADJOIN
def INTEGRAL_ELEMENT_FROM_RELATION : thm := BIntegral01.INTEGRAL_ELEMENT_FROM_RELATION
def INTEGRAL_ELEMENT_OVER_SUBRING : thm := BIntegral01.INTEGRAL_ELEMENT_OVER_SUBRING
def INTEGRAL_SPAN_FINITE_SET : thm := BIntegral01.INTEGRAL_SPAN_FINITE_SET
def INTEGRAL_ELEMENT_EXPLICIT : thm := BIntegral01.INTEGRAL_ELEMENT_EXPLICIT
def INTEGRAL_ELEMENT_ADD : thm := BIntegral01.INTEGRAL_ELEMENT_ADD
def INTEGRAL_ELEMENT_MUL : thm := BIntegral01.INTEGRAL_ELEMENT_MUL
def INTEGRAL_ELEMENT_NEG : thm := BIntegral01.INTEGRAL_ELEMENT_NEG
def INTEGRAL_ELEMENT_SUB : thm := BIntegral01.INTEGRAL_ELEMENT_SUB
def INTEGRAL_ELEMENT_POW : thm := BIntegral01.INTEGRAL_ELEMENT_POW
def INTEGRAL_CLOSURE_SUBRING : thm := BIntegral01.INTEGRAL_CLOSURE_SUBRING
def INTEGRAL_CLOSURE_SUPSET_IMAGE : thm := BIntegral01.INTEGRAL_CLOSURE_SUPSET_IMAGE
def INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE : thm := BIntegral01.INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE
def INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE : thm := BIntegral01.INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE
def INTEGRAL_ELEMENT_SUBRING_GENERATED : thm := BIntegral01.INTEGRAL_ELEMENT_SUBRING_GENERATED
def INTEGRAL_ELEMENT_TRANS : thm := BIntegral01.INTEGRAL_ELEMENT_TRANS
def INTEGRAL_CLOSURE_IDEMPOT : thm := BIntegral01.INTEGRAL_CLOSURE_IDEMPOT
def INTEGRAL_OVER_FIELD_EQ_ALGEBRAIC : thm := BIntegral01.INTEGRAL_OVER_FIELD_EQ_ALGEBRAIC

-- Integral02
def INTEGRAL_ELEMENT_IN_ADJOIN_INV : thm := BIntegral02.INTEGRAL_ELEMENT_IN_ADJOIN_INV
def INTEGRAL_HOMOGENEOUS_SCALE : thm := BIntegral02.INTEGRAL_HOMOGENEOUS_SCALE
def INTEGRAL_HOMOGENEOUS_HOMOMORPHIC_IMAGE : thm := BIntegral02.INTEGRAL_HOMOGENEOUS_HOMOMORPHIC_IMAGE
def RING_REGULAR_MUL_EQ_0 : thm := BIntegral02.RING_REGULAR_MUL_EQ_0
def INTEGRAL_HOMOGENEOUS_CLEAR : thm := BIntegral02.INTEGRAL_HOMOGENEOUS_CLEAR
def INTEGRAL_UFD_HOMOGENEOUS_DIVIDES : thm := BIntegral02.INTEGRAL_UFD_HOMOGENEOUS_DIVIDES
def INTEGRAL_HOMOGENEOUS_RELATION : thm := BIntegral02.INTEGRAL_HOMOGENEOUS_RELATION
def INTEGRAL_MONOMORPHISM_IN_IMAGE : thm := BIntegral02.INTEGRAL_MONOMORPHISM_IN_IMAGE
def INTEGRAL_FRACTION_RING_DENOMINATOR : thm := BIntegral02.INTEGRAL_FRACTION_RING_DENOMINATOR
def INTEGRAL_FRACTION_RING_RELATION : thm := BIntegral02.INTEGRAL_FRACTION_RING_RELATION
def INTEGRALLY_CLOSED_ALT : thm := BIntegral02.INTEGRALLY_CLOSED_ALT
def UFD_IMP_INTEGRALLY_CLOSED : thm := BIntegral02.UFD_IMP_INTEGRALLY_CLOSED
def PID_IMP_INTEGRALLY_CLOSED : thm := BIntegral02.PID_IMP_INTEGRALLY_CLOSED
def FIELD_IMP_INTEGRALLY_CLOSED : thm := BIntegral02.FIELD_IMP_INTEGRALLY_CLOSED
def INTEGRALLY_CLOSED_INTEGER_RING : thm := BIntegral02.INTEGRALLY_CLOSED_INTEGER_RING
def INTEGRAL_ELEMENT_PRIME_SUBFIELD : thm := BIntegral02.INTEGRAL_ELEMENT_PRIME_SUBFIELD
def INTEGRALLY_CLOSED_INTEGRAL_CLOSURE : thm := BIntegral02.INTEGRALLY_CLOSED_INTEGRAL_CLOSURE
def INTEGRALLY_CLOSED_DIVIDES : thm := BIntegral02.INTEGRALLY_CLOSED_DIVIDES
def INTEGRAL_ELEMENT_FRACTION_IN_IMAGE : thm := BIntegral02.INTEGRAL_ELEMENT_FRACTION_IN_IMAGE
def INTEGRALLY_CLOSED_INTEGRAL_IMAGE : thm := BIntegral02.INTEGRALLY_CLOSED_INTEGRAL_IMAGE

-- Integral03
def RING_LOCALIZATION_COMMON_DENOMINATOR : thm := BIntegral03.RING_LOCALIZATION_COMMON_DENOMINATOR
def INTEGRALLY_CLOSED_LOCALIZATION : thm := BIntegral03.INTEGRALLY_CLOSED_LOCALIZATION
def INTEGRAL_ELEMENT_INTERMEDIATE : thm := BIntegral03.INTEGRAL_ELEMENT_INTERMEDIATE
def INTEGRAL_ELEMENT_MONIC_DIVISOR : thm := BIntegral03.INTEGRAL_ELEMENT_MONIC_DIVISOR
def INTEGRAL_ELEMENT_MINIMAL_POLYNOMIAL : thm := BIntegral03.INTEGRAL_ELEMENT_MINIMAL_POLYNOMIAL
def ALGEBRA_TRACE_NORM_INTEGRAL : thm := BIntegral03.ALGEBRA_TRACE_NORM_INTEGRAL
def INTEGRALLY_CLOSED_FIELD_OF_FRACTIONS : thm := BIntegral03.INTEGRALLY_CLOSED_FIELD_OF_FRACTIONS
def INTEGRALLY_CLOSED_MINIMAL_POLYNOMIAL : thm := BIntegral03.INTEGRALLY_CLOSED_MINIMAL_POLYNOMIAL
def INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM : thm := BIntegral03.INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM

-- Integral04
def INTEGRALLY_CLOSED_UNIT_NORM : thm := BIntegral04.INTEGRALLY_CLOSED_UNIT_NORM
def INTEGRAL_CLOSURE_UNIT_NORM : thm := BIntegral04.INTEGRAL_CLOSURE_UNIT_NORM

/-- `needs "ANT/integral.ml"`: already done by importing this module. -/
def ensureIntegral : IO Unit := pure ()

end SessionANT.Integral
