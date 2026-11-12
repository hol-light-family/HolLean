/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/relative_split.ml                             . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/RelativeSplit.lean

  The session half of the relative_split.ml translation: it supplies HolANT.RelativeSplit's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/relative_split.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.RelativeSplit
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
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.IdealNorm
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.PrimeSplit
import SessionANT.Discriminant
import SessionANT.TraceForm

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.RelativeSplit

/-- The core theorems relative_split.ml uses. -/
def core1 : HolANT.RelativeSplit.CoreThms1 where
  ADD1 := Session.ADD1
  ADD_CLAUSES := Session.ADD_CLAUSES
  AND_FORALL_THM := Session.AND_FORALL_THM
  CARD_EQ_NSUM := Session.CARD_EQ_NSUM
  CARD_EXTENSION_DEGREE := SessionLibrary.FieldTheory.«CARD_EXTENSION_DEGREE»
  CARRIER_SUBRING_GENERATED_SUBRING := SessionLibrary.RingTheory.«CARRIER_SUBRING_GENERATED_SUBRING»
  CARRIER_SUBRING_OF := SessionLibrary.RingTheory.«CARRIER_SUBRING_OF»
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DEDEKIND_FINITE_MAXIMAL_IDEALS_ABOVE := SessionANT.Dedekind.«DEDEKIND_FINITE_MAXIMAL_IDEALS_ABOVE»
  DEDEKIND_IDEAL_FACTORIZATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_FACTORIZATION»
  DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE := SessionANT.Dedekind.«DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE»
  DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES»
  DEDEKIND_IDEAL_SUBSET_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_POW_VALUATION»
  DEDEKIND_IDEAL_SUBSET_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_VALUATION»
  DEDEKIND_IMP_INTEGRAL_DOMAIN := SessionANT.Dedekind.«DEDEKIND_IMP_INTEGRAL_DOMAIN»
  DEDEKIND_IN_IDEAL_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IN_IDEAL_POW_VALUATION»
  DEDEKIND_KRULL_DIMENSION_ONE := SessionANT.Dedekind.«DEDEKIND_KRULL_DIMENSION_ONE»
  DEDEKIND_MAXIMAL_IDEAL_INVERSE := SessionANT.Dedekind.«DEDEKIND_MAXIMAL_IDEAL_INVERSE»
  DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL := SessionANT.Dedekind.«DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DEDEKIND_UNIFORMIZER_CRITERION := SessionANT.DedekindValuation.«DEDEKIND_UNIFORMIZER_CRITERION»
  DEDEKIND_VALUATION := SessionANT.DedekindValuation.«DEDEKIND_VALUATION»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EQ_EXP := Session.EQ_EXP
  EQ_TRANS := Session.EQ_TRANS
  ETA_AX := Session.ETA_AX
  EXISTS_UNIQUE := Session.EXISTS_UNIQUE
  EXISTS_UNIQUE_DEF := Session.EXISTS_UNIQUE_DEF
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXP_1 := Session.EXP_1
  EXP_EXP := Session.EXP_EXP
  EXTENSION := Session.EXTENSION
  EXTENSION_DEGREE_EQ_IMAGE := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_EQ_IMAGE»
  EXTENSION_DEGREE_SUBFIELD_TOWER := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_SUBFIELD_TOWER»
  FIELD_DIVIDES := SessionLibrary.RingTheory.«FIELD_DIVIDES»
  FIELD_FRACTION_NONZERO := SessionANT.DedekindValuation.«FIELD_FRACTION_NONZERO»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FIELD_QUOTIENT_RING := SessionLibrary.RingTheory.«FIELD_QUOTIENT_RING»
  FIELD_REAL_RING := SessionLibrary.RingTheory.«FIELD_REAL_RING»
  FIELD_RING_HOMOMORPHISM_MONOMORPHISM := SessionLibrary.RingTheory.«FIELD_RING_HOMOMORPHISM_MONOMORPHISM»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_FIELD_EXTENSION»
  FINITE_INTEGRAL_DOMAIN_IMP_FIELD := SessionLibrary.RingTheory.«FINITE_INTEGRAL_DOMAIN_IMP_FIELD»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_RING_MONOMORPHIC_PREIMAGE := SessionLibrary.RingTheory.«FINITE_RING_MONOMORPHIC_PREIMAGE»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FREE_BASIS_EXISTS := SessionLibrary.FieldTheory.«FREE_BASIS_EXISTS»
  FREE_BASIS_IN_CARRIER := SessionLibrary.RingDet.«FREE_BASIS_IN_CARRIER»
  FUN_EQ_THM := Session.FUN_EQ_THM
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_GENERATED_IMAGE_IDEAL_GENERATED := SessionANT.IdealArith.«IDEAL_GENERATED_IMAGE_IDEAL_GENERATED»
  IDEAL_GENERATED_INC := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC»
  IDEAL_GENERATED_INC_GEN := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC_GEN»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_GENERATED_MINIMAL_EQ := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL_EQ»
  IDEAL_GENERATED_MONO := SessionLibrary.RingTheory.«IDEAL_GENERATED_MONO»
  IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0 := SessionANT.IdealArith.«IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0»
  IDEAL_GENERATED_SUBSET := SessionLibrary.RingTheory.«IDEAL_GENERATED_SUBSET»
  IDEAL_NORM_GT_1 := SessionANT.IdealNorm.«IDEAL_NORM_GT_1»
  IDEAL_POW_0 := SessionANT.IdealArith.«IDEAL_POW_0»
  IDEAL_POW_1 := SessionANT.IdealArith.«IDEAL_POW_1»
  IDEAL_POW_ANTIMONO := SessionANT.IdealArith.«IDEAL_POW_ANTIMONO»
  IDEAL_POW_EQ_ZERO := SessionANT.IdealArith.«IDEAL_POW_EQ_ZERO»
  IDEAL_POW_HOMOMORPHIC_IMAGE := SessionANT.IdealArith.«IDEAL_POW_HOMOMORPHIC_IMAGE»
  IDEAL_POW_HOMOMORPHIC_IMAGE_SUBSET := SessionANT.IdealArith.«IDEAL_POW_HOMOMORPHIC_IMAGE_SUBSET»
  IDEAL_POW_MUL := SessionANT.IdealArith.«IDEAL_POW_MUL»
  IDEAL_POW_PRINCIPAL := SessionANT.IdealArith.«IDEAL_POW_PRINCIPAL»
  IDEAL_POW_SUC := SessionANT.IdealArith.«IDEAL_POW_SUC»
  IDEAL_POW_SUC_SUBSET := SessionANT.IdealArith.«IDEAL_POW_SUC_SUBSET»
  IDEAL_PRODUCT_EQ := SessionANT.IdealArith.«IDEAL_PRODUCT_EQ»
  IDEAL_PROD_CARRIER := SessionANT.IdealArith.«IDEAL_PROD_CARRIER»
  IDEAL_PROD_CARRIER_LEFT := SessionANT.IdealArith.«IDEAL_PROD_CARRIER_LEFT»
  IDEAL_PROD_COMM := SessionANT.IdealArith.«IDEAL_PROD_COMM»
  IDEAL_PROD_HOMOMORPHIC_IMAGE := SessionANT.IdealArith.«IDEAL_PROD_HOMOMORPHIC_IMAGE»
  IDEAL_PROD_MONO := SessionANT.IdealArith.«IDEAL_PROD_MONO»
  IDEAL_PROD_RZERO := SessionANT.IdealArith.«IDEAL_PROD_RZERO»
  IDEAL_VALUATION_EQ_0 := SessionANT.Dedekind.«IDEAL_VALUATION_EQ_0»
  IDEAL_VALUATION_IDEAL_POW := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_POW»
  IDEAL_VALUATION_IDEAL_PROD := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_PROD»
  IDEAL_VALUATION_PRIME := SessionANT.Dedekind.«IDEAL_VALUATION_PRIME»
  IDEAL_VALUATION_PRINCIPAL_MUL := SessionANT.Dedekind.«IDEAL_VALUATION_PRINCIPAL_MUL»
  IDEAL_VALUATION_SETADD := SessionANT.Dedekind.«IDEAL_VALUATION_SETADD»
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMAGE_EQ := Session.IMAGE_EQ
  IMAGE_I := Session.IMAGE_I
  IMAGE_SUBSET := Session.IMAGE_SUBSET
  IMAGE_o := Session.IMAGE_o
  IMP_CONJ := Session.IMP_CONJ
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGRAL_DOMAIN_CHAR := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_CHAR»
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_MUL_LCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_LCANCEL»
  INTEGRAL_DOMAIN_POW_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_POW_EQ_0»
  INTEGRAL_DOMAIN_QUOTIENT_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_QUOTIENT_RING»
  INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE := SessionANT.Integral.«INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE»
  INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE := SessionANT.Integral.«INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE»
  INTEGRAL_ELEMENT_SUBRING_GENERATED := SessionANT.Integral.«INTEGRAL_ELEMENT_SUBRING_GENERATED»
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SING := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SING»
  IN_IDEAL_GENERATED_SING_EQ := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SING_EQ»
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_ADD := SessionLibrary.RingTheory.«IN_RING_IDEAL_ADD»
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_RING_IDEAL_RMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_RMUL»
  IN_RING_IDEAL_SUB := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUB»
  IN_RING_IDEAL_SUM := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUM»
  IN_SING := Session.IN_SING
  IN_UNIV := Session.IN_UNIV
  I_DEF := Session.I_DEF
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  LE_REFL := Session.LE_REFL
  LT := Session.LT
  LT_REFL := Session.LT_REFL
  MAXIMAL_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«MAXIMAL_IDEAL_IMP_SUBSET»
  MAXIMAL_IMP_PRIME_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PRIME_IDEAL»
  MAXIMAL_IMP_RING_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_RING_IDEAL»
  MAXIMAL_SUPERIDEAL_EXISTS := SessionLibrary.RingTheory.«MAXIMAL_SUPERIDEAL_EXISTS»
/-- The core theorems relative_split.ml uses. -/
def core2 : HolANT.RelativeSplit.CoreThms2 where
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MIN := Session.MIN
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_SYM := Session.MULT_SYM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NSUM_EQ := Session.NSUM_EQ
  NSUM_GROUP := Session.NSUM_GROUP
  NUMBER_FIELD_DEGREE_POS := SessionANT.Numfield.«NUMBER_FIELD_DEGREE_POS»
  NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM := SessionANT.Classgroup.«NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_ISOMORPHIC_IMAGE := SessionANT.TraceForm.«NUMBER_FIELD_ISOMORPHIC_IMAGE»
  NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q := SessionANT.PrimeSplit.«NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q»
  NUMBER_FIELD_PRIME_SUBFIELD := SessionANT.Numfield.«NUMBER_FIELD_PRIME_SUBFIELD»
  PRIME_EXP := SessionLibrary.Prime.«PRIME_EXP»
  PRIME_IDEAL_HOMOMORPHIC_PREIMAGE := SessionLibrary.RingTheory.«PRIME_IDEAL_HOMOMORPHIC_PREIMAGE»
  PRIME_IDEAL_IMP_PSUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_PSUBSET»
  PRIME_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_SUBSET»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRIME_SUBFIELD_EQ_SUBRING := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_EQ_SUBRING»
  PRIME_SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_SUBFIELD_GENERATED»
  PRIME_SUBFIELD_TOWER_LAW := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_TOWER_LAW»
  PSUBSET := Session.PSUBSET
  QUOTIENT_RING_0 := SessionLibrary.RingTheory.«QUOTIENT_RING_0»
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
  QUOTIENT_RING_UNIVERSAL_EXPLICIT := SessionLibrary.RingTheory.«QUOTIENT_RING_UNIVERSAL_EXPLICIT»
  REAL_RING_CLAUSES := SessionLibrary.RingTheory.«REAL_RING_CLAUSES»
  REAL_RING_OF_INT := SessionLibrary.RingTheory.«REAL_RING_OF_INT»
  RIGHT_EXISTS_IMP_THM := Session.RIGHT_EXISTS_IMP_THM
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_COSET_EQ_IDEAL := SessionLibrary.RingTheory.«RING_COSET_EQ_IDEAL»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_HOMOMORPHISM_RING_OF_INTEGERS»
  RING_HOMOMORPHISM_SUB := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUB»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_HOMOMORPHISM_SUM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM_MUL»
  RING_IDEAL_0 := SessionLibrary.RingTheory.«RING_IDEAL_0»
  RING_IDEAL_CARRIER := SessionLibrary.RingTheory.«RING_IDEAL_CARRIER»
  RING_IDEAL_HOMOMORPHIC_PREIMAGE := SessionLibrary.RingTheory.«RING_IDEAL_HOMOMORPHIC_PREIMAGE»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IDEAL_PROD := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PROD»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_IDEAL_SETADD := SessionLibrary.RingTheory.«RING_IDEAL_SETADD»
  RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE := SessionLibrary.FieldTheory.«RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE»
  RING_MATROID_SPANNING := SessionLibrary.FieldTheory.«RING_MATROID_SPANNING»
  RING_MONOMORPHISM_EQ_0 := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EQ_0»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_INCLUSION := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INCLUSION»
  RING_MONOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_MONOMORPHISM_RING_OF_INTEGERS»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_IN_IDEAL_POW := SessionANT.IdealArith.«RING_MUL_IN_IDEAL_POW»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_CARRIER := SessionANT.Numfield.«RING_OF_INTEGERS_CARRIER»
  RING_OF_INTEGERS_DENOMINATOR := SessionANT.Numfield.«RING_OF_INTEGERS_DENOMINATOR»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_IDEAL_INTEGER := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_IDEAL_INTEGER»
  RING_OF_INTEGERS_PRIME_IDEAL_ABOVE := SessionANT.PrimeSplit.«RING_OF_INTEGERS_PRIME_IDEAL_ABOVE»
  RING_OF_INTEGERS_PRIME_SUBFIELD := SessionANT.Numfield.«RING_OF_INTEGERS_PRIME_SUBFIELD»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_EQ_0_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0_CHAR_0»
  RING_OF_INT_IN_PRIME_IDEAL := SessionANT.PrimeSplit.«RING_OF_INT_IN_PRIME_IDEAL»
  RING_OF_INT_IN_RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INT_IN_RING_OF_INTEGERS»
  RING_OF_INT_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_IN_SUBFIELD_GENERATED»
  RING_OF_INT_MUL := SessionLibrary.RingTheory.«RING_OF_INT_MUL»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_INT_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_SUBFIELD_GENERATED»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_OF_NUM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_NUM_SUBFIELD_GENERATED»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_IN_IDEAL_POW := SessionANT.IdealArith.«RING_POW_IN_IDEAL_POW»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_RZERO := SessionLibrary.RingTheory.«RING_SUB_RZERO»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_ADD := SessionLibrary.RingTheory.«RING_SUM_ADD»
  RING_SUM_CLAUSES := SessionLibrary.RingTheory.«RING_SUM_CLAUSES»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_LMUL := SessionLibrary.RingTheory.«RING_SUM_LMUL»
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SIMPLE_IMAGE := Session.SIMPLE_IMAGE
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE»
  SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_MINIMAL := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_MINIMAL»
  SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_SUBFIELD_GENERATED»
  SUBRING_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBRING_GENERATED_BY_SUBFIELD_GENERATED»
  SUBRING_OF_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«SUBRING_OF_HOMOMORPHIC_IMAGE»
  SUBRING_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBRING_SUBFIELD_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_REFL := Session.SUBSET_REFL
  SUBSET_TRANS := Session.SUBSET_TRANS
  extension_degree := SessionLibrary.FieldTheory.«extension_degree»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  field_of_fractions := SessionLibrary.RingTheory.«field_of_fractions»
  finite_extension := SessionLibrary.FieldTheory.«finite_extension»
  free_basis := SessionLibrary.RingDet.«free_basis»
  ideal_norm := SessionANT.IdealNorm.«ideal_norm»
  int_divides := Session.int_divides
  int_tybij := Session.int_tybij
  matroid_finite_dimensional := SessionLibrary.Matroids.«matroid_finite_dimensional»
  number_field := SessionANT.Numfield.«number_field»
  o_THM := Session.o_THM
  proper_ideal := SessionLibrary.RingTheory.«proper_ideal»
  ramification_index := SessionANT.PrimeSplit.«ramification_index»
  residue_degree := SessionANT.PrimeSplit.«residue_degree»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  ring_of_integers := SessionANT.Numfield.«ring_of_integers»
  ring_setadd := SessionLibrary.RingTheory.«ring_setadd»

/-- What relative_split.ml uses from Session. -/
def deps : HolANT.RelativeSplit.RelativeSplitDeps where
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

/- The bundles, in relative_split.ml order. -/
initialize BRelativeSplit01 : HolANT.RelativeSplit.RelativeSplit01 ←
  ioB "setupRelativeSplit01" (HolANT.RelativeSplit.setupRelativeSplit01 deps).run
initialize BRelativeSplit02 : HolANT.RelativeSplit.RelativeSplit02 ←
  ioB "setupRelativeSplit02" (HolANT.RelativeSplit.setupRelativeSplit02 deps BRelativeSplit01).run
initialize BRelativeSplit03 : HolANT.RelativeSplit.RelativeSplit03 ←
  ioB "setupRelativeSplit03" (HolANT.RelativeSplit.setupRelativeSplit03 deps BRelativeSplit01 BRelativeSplit02).run
initialize BRelativeSplit04 : HolANT.RelativeSplit.RelativeSplit04 ←
  ioB "setupRelativeSplit04" (HolANT.RelativeSplit.setupRelativeSplit04 deps BRelativeSplit01 BRelativeSplit02 BRelativeSplit03).run

-- RelativeSplit01
def RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE : thm := BRelativeSplit01.RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE
def RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ : thm := BRelativeSplit01.RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ
def RING_OF_INTEGERS_SUBFIELD_GENERATED : thm := BRelativeSplit01.RING_OF_INTEGERS_SUBFIELD_GENERATED
def NUMBER_FIELD_HOMOMORPHIC_PREIMAGE : thm := BRelativeSplit01.NUMBER_FIELD_HOMOMORPHIC_PREIMAGE
def NUMBER_FIELD_SUBFIELD_GENERATED : thm := BRelativeSplit01.NUMBER_FIELD_SUBFIELD_GENERATED
def NUMBER_FIELD_TOWER_LAW : thm := BRelativeSplit01.NUMBER_FIELD_TOWER_LAW
def NUMBER_FIELD_SUBFIELD_DEGREE_POS : thm := BRelativeSplit01.NUMBER_FIELD_SUBFIELD_DEGREE_POS
def NUMBER_FIELD_SUBFIELD_HOMOMORPHIC_IMAGE : thm := BRelativeSplit01.NUMBER_FIELD_SUBFIELD_HOMOMORPHIC_IMAGE
def RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION : thm := BRelativeSplit01.RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION
def RING_OF_INTEGERS_PRIME_IDEAL_BELOW : thm := BRelativeSplit01.RING_OF_INTEGERS_PRIME_IDEAL_BELOW
def RING_OF_INTEGERS_IDEAL_EXTENSION : thm := BRelativeSplit01.RING_OF_INTEGERS_IDEAL_EXTENSION
def RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME : thm := BRelativeSplit01.RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME
def NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO : thm := BRelativeSplit01.NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO
def NUMBER_FIELD_PRIME_IDEAL_ABOVE : thm := BRelativeSplit01.NUMBER_FIELD_PRIME_IDEAL_ABOVE
def NUMBER_FIELD_PRIME_IDEALS_ABOVE : thm := BRelativeSplit01.NUMBER_FIELD_PRIME_IDEALS_ABOVE
def NUMBER_FIELD_PRIME_FACTORIZATION : thm := BRelativeSplit01.NUMBER_FIELD_PRIME_FACTORIZATION
def NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE : thm := BRelativeSplit01.NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE
def RESIDUE_DEGREE_QUOTIENT_RING : thm := BRelativeSplit01.RESIDUE_DEGREE_QUOTIENT_RING
def FINITE_QUOTIENT_RING_HOMOMORPHIC_PREIMAGE : thm := BRelativeSplit01.FINITE_QUOTIENT_RING_HOMOMORPHIC_PREIMAGE
def IDEAL_NORM_RESIDUE_DEGREE : thm := BRelativeSplit01.IDEAL_NORM_RESIDUE_DEGREE
def RING_OF_INTEGERS_IDEAL_NORM_PRIME : thm := BRelativeSplit01.RING_OF_INTEGERS_IDEAL_NORM_PRIME

-- RelativeSplit02
def NUMBER_FIELD_PRIME_NORM_CARD : thm := BRelativeSplit02.NUMBER_FIELD_PRIME_NORM_CARD
def IDEAL_VALUATION_HOMOMORPHIC_IMAGE : thm := BRelativeSplit02.IDEAL_VALUATION_HOMOMORPHIC_IMAGE
def IDEAL_VALUATION_HOMOMORPHIC_IMAGE_SING : thm := BRelativeSplit02.IDEAL_VALUATION_HOMOMORPHIC_IMAGE_SING
def DEDEKIND_VALUATION_RAMIFICATION_INDEX : thm := BRelativeSplit02.DEDEKIND_VALUATION_RAMIFICATION_INDEX
def DEDEKIND_RAMIFICATION_INDEX_NONZERO : thm := BRelativeSplit02.DEDEKIND_RAMIFICATION_INDEX_NONZERO
def NUMBER_FIELD_VALUATION_RAMIFICATION_INDEX : thm := BRelativeSplit02.NUMBER_FIELD_VALUATION_RAMIFICATION_INDEX
def NUMBER_FIELD_IDEAL_VALUATION_EXTENSION : thm := BRelativeSplit02.NUMBER_FIELD_IDEAL_VALUATION_EXTENSION
def RESIDUE_DEGREE_TOWER : thm := BRelativeSplit02.RESIDUE_DEGREE_TOWER
def RAMIFICATION_INDEX_TOWER : thm := BRelativeSplit02.RAMIFICATION_INDEX_TOWER
def NUMBER_FIELD_RAMIFICATION_INDEX_TOWER : thm := BRelativeSplit02.NUMBER_FIELD_RAMIFICATION_INDEX_TOWER
def NUMBER_FIELD_RESIDUE_DEGREE_TOWER : thm := BRelativeSplit02.NUMBER_FIELD_RESIDUE_DEGREE_TOWER

-- RelativeSplit03
def DEDEKIND_VALUATION_LIFT_CANCEL : thm := BRelativeSplit03.DEDEKIND_VALUATION_LIFT_CANCEL
def RAMIFICATION_INDEX_IMAGE_SUBSET : thm := BRelativeSplit03.RAMIFICATION_INDEX_IMAGE_SUBSET
def RAMIFICATION_INDEX_IMAGE_POW_SUBSET : thm := BRelativeSplit03.RAMIFICATION_INDEX_IMAGE_POW_SUBSET
def DEDEKIND_EXTENSION_UNIFORMIZER_CRITERION : thm := BRelativeSplit03.DEDEKIND_EXTENSION_UNIFORMIZER_CRITERION
def RESIDUE_DEGREE_LIFTED_BASIS : thm := BRelativeSplit03.RESIDUE_DEGREE_LIFTED_BASIS
def DEDEKIND_UNIFORMIZER_DIGITS_SPAN : thm := BRelativeSplit03.DEDEKIND_UNIFORMIZER_DIGITS_SPAN
def DEDEKIND_UNIFORMIZER_DIGITS_INDEPENDENT : thm := BRelativeSplit03.DEDEKIND_UNIFORMIZER_DIGITS_INDEPENDENT
def DEDEKIND_EXTENSION_DIGITS_LINEAR : thm := BRelativeSplit03.DEDEKIND_EXTENSION_DIGITS_LINEAR

-- RelativeSplit04
def DEDEKIND_EXTENSION_DIGITS_IN_IDEAL_POW : thm := BRelativeSplit04.DEDEKIND_EXTENSION_DIGITS_IN_IDEAL_POW
def DEDEKIND_EXTENSION_DIGITS_SPAN : thm := BRelativeSplit04.DEDEKIND_EXTENSION_DIGITS_SPAN
def DEDEKIND_EXTENSION_DIGITS_INDEPENDENT : thm := BRelativeSplit04.DEDEKIND_EXTENSION_DIGITS_INDEPENDENT
def DEDEKIND_EXTENSION_DIGITS : thm := BRelativeSplit04.DEDEKIND_EXTENSION_DIGITS
def RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER : thm := BRelativeSplit04.RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER
def RING_OF_INTEGERS_RATIONAL_FIELD : thm := BRelativeSplit04.RING_OF_INTEGERS_RATIONAL_FIELD
def RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL : thm := BRelativeSplit04.RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL
def RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL : thm := BRelativeSplit04.RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL
def RAMIFICATION_INDEX_PRIME_SUBFIELD : thm := BRelativeSplit04.RAMIFICATION_INDEX_PRIME_SUBFIELD
def RESIDUE_DEGREE_PRIME_SUBFIELD : thm := BRelativeSplit04.RESIDUE_DEGREE_PRIME_SUBFIELD
def NUMBER_FIELD_RAMIFICATION_INDEX_TOWER_Q : thm := BRelativeSplit04.NUMBER_FIELD_RAMIFICATION_INDEX_TOWER_Q
def NUMBER_FIELD_RESIDUE_DEGREE_TOWER_Q : thm := BRelativeSplit04.NUMBER_FIELD_RESIDUE_DEGREE_TOWER_Q

/-- `needs "ANT/relative_split.ml"`: already done by importing this module. -/
def ensureRelativeSplit : IO Unit := pure ()

end SessionANT.RelativeSplit
