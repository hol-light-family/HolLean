/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/dedekind_kummer.ml                            . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/DedekindKummer.lean

  The session half of the dedekind_kummer.ml translation: it supplies HolANT.DedekindKummer's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/dedekind_kummer.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.DedekindKummer
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
import SessionANT.IdealNorm
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.RingOfIntegers
import SessionANT.PrimeSplit
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.RelativeDegree
import SessionANT.NfValuation
import SessionANT.Integrality

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.DedekindKummer

/-- The core theorems dedekind_kummer.ml uses. -/
def core1 : HolANT.DedekindKummer.CoreThms1 where
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_INTEGER_MOD_RING := SessionLibrary.RingTheory.«CARD_INTEGER_MOD_RING»
  CARD_SUBSET := Session.CARD_SUBSET
  COEFF_ABOVE_DEG := SessionLibrary.RingTheory.«COEFF_ABOVE_DEG»
  COEFF_COMPOSE := SessionLibrary.RingTheory.«COEFF_COMPOSE»
  DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE := SessionANT.Dedekind.«DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE»
  DEDEKIND_IMP_INTEGRAL_DOMAIN := SessionANT.Dedekind.«DEDEKIND_IMP_INTEGRAL_DOMAIN»
  DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL := SessionANT.Dedekind.«DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  EQ_EXP := Session.EQ_EXP
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_IN_IMAGE := Session.EXISTS_IN_IMAGE
  EXP_EXP := Session.EXP_EXP
  EXP_NSUM := SessionLibrary.Products.«EXP_NSUM»
  EXTENSION := Session.EXTENSION
  FIELD_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_INTEGER_MOD_RING := SessionLibrary.RingTheory.«FIELD_INTEGER_MOD_RING»
  FIELD_QUOTIENT_RING := SessionLibrary.RingTheory.«FIELD_QUOTIENT_RING»
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_IMAGE_INJ_EQ := Session.FINITE_IMAGE_INJ_EQ
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_INTEGER_MOD_RING := SessionLibrary.RingTheory.«FINITE_INTEGER_MOD_RING»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_QUOTIENT_RING_MONO := SessionANT.IdealNorm.«FINITE_QUOTIENT_RING_MONO»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FIRST_RING_EPIMORPHISM_THEOREM := SessionLibrary.RingTheory.«FIRST_RING_EPIMORPHISM_THEOREM»
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FREE_BASIS_PRIME_SUBFIELD_INT_LINCOMB := SessionANT.Numfield.«FREE_BASIS_PRIME_SUBFIELD_INT_LINCOMB»
  FUN_EQ_COEFF := SessionLibrary.RingTheory.«FUN_EQ_COEFF»
  FUN_EQ_THM := Session.FUN_EQ_THM
  HAS_SIZE := Session.HAS_SIZE
  IDEAL_GENERATED_IMAGE_IDEAL_GENERATED := SessionANT.IdealArith.«IDEAL_GENERATED_IMAGE_IDEAL_GENERATED»
  IDEAL_GENERATED_INC := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC»
  IDEAL_GENERATED_INSERT := SessionLibrary.RingTheory.«IDEAL_GENERATED_INSERT»
  IDEAL_GENERATED_INSERT_EQ := SessionLibrary.RingTheory.«IDEAL_GENERATED_INSERT_EQ»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_GENERATED_MINIMAL_EQ := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL_EQ»
  IDEAL_GENERATED_MONO := SessionLibrary.RingTheory.«IDEAL_GENERATED_MONO»
  IDEAL_GENERATED_PAIR_EQ := SessionLibrary.RingTheory.«IDEAL_GENERATED_PAIR_EQ»
  IDEAL_GENERATED_SING := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING»
  IDEAL_NORM_IDEAL_POW := SessionANT.IdealNorm.«IDEAL_NORM_IDEAL_POW»
  IDEAL_NORM_IDEAL_PRODUCT := SessionANT.IdealNorm.«IDEAL_NORM_IDEAL_PRODUCT»
  IDEAL_NORM_RESIDUE_DEGREE := SessionANT.RelativeSplit.«IDEAL_NORM_RESIDUE_DEGREE»
  IDEAL_NORM_SUBSET_EQ := SessionANT.IdealNorm.«IDEAL_NORM_SUBSET_EQ»
  IDEAL_POW_EQ_ZERO := SessionANT.IdealArith.«IDEAL_POW_EQ_ZERO»
  IDEAL_PRODUCT_EQ := SessionANT.IdealArith.«IDEAL_PRODUCT_EQ»
  IDEAL_PRODUCT_IMAGE := SessionANT.IdealArith.«IDEAL_PRODUCT_IMAGE»
  IDEAL_PRODUCT_POW_SETADD_SUBSET := SessionANT.IdealArith.«IDEAL_PRODUCT_POW_SETADD_SUBSET»
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMAGE_POLY_EXTEND_1 := SessionLibrary.RingTheory.«IMAGE_POLY_EXTEND_1»
  IMP_CONJ := Session.IMP_CONJ
  INFINITE := Session.INFINITE
  INSERT_COMM := Session.INSERT_COMM
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTEGER_MOD_RING_CLAUSES := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CLAUSES»
  INTEGER_MOD_RING_OF_INT := SessionLibrary.RingTheory.«INTEGER_MOD_RING_OF_INT»
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_ENTIRE := Session.INT_ENTIRE
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_REM_ZERO := Session.INT_REM_ZERO
  INT_SUB_0 := Session.INT_SUB_0
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_NUMSEG := Session.IN_NUMSEG
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_POLYNOMIAL_CARRIER_COMPOSE := SessionLibrary.RingTheory.«IN_RING_POLYNOMIAL_CARRIER_COMPOSE»
  IN_SING := Session.IN_SING
  IN_UNIV := Session.IN_UNIV
  ISOMORPHIC_RING_CARD := SessionLibrary.RingTheory.«ISOMORPHIC_RING_CARD»
  ISOMORPHIC_RING_SYM := SessionLibrary.RingTheory.«ISOMORPHIC_RING_SYM»
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_0 := Session.LE_0
  LE_TRANS := Session.LE_TRANS
  MAXIMAL_IDEAL_EPIMORPHISM_KERNEL := SessionLibrary.RingTheory.«MAXIMAL_IDEAL_EPIMORPHISM_KERNEL»
  MAXIMAL_IDEAL_POLY_RING_EPIMORPHISM := SessionLibrary.RingTheory.«MAXIMAL_IDEAL_POLY_RING_EPIMORPHISM»
  MAXIMAL_IMP_PRIME_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PRIME_IDEAL»
  MAXIMAL_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PROPER_IDEAL»
  MINIMAL_POLYNOMIAL := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL»
  MINIMAL_POLYNOMIAL_POWERS_INDEPENDENT := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL_POWERS_INDEPENDENT»
  MONIC_ASSOCIATES_EQ := SessionLibrary.RingTheory.«MONIC_ASSOCIATES_EQ»
  MONIC_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«MONIC_HOMOMORPHIC_IMAGE»
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_SYM := Session.MULT_SYM
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NPRODUCT_EQ := SessionLibrary.Products.«NPRODUCT_EQ»
  NSUM_EQ := Session.NSUM_EQ
  NUMBER_FIELD_ALGEBRAIC := SessionANT.Numfield.«NUMBER_FIELD_ALGEBRAIC»
  NUMBER_FIELD_HOMOMORPHIC_PREIMAGE := SessionANT.RelativeSplit.«NUMBER_FIELD_HOMOMORPHIC_PREIMAGE»
  NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q := SessionANT.RelativeDegree.«NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_INDEX_COPRIME := SessionANT.Discriminant.«NUMBER_FIELD_INDEX_COPRIME»
  NUMBER_FIELD_INTEGRAL_MULTIPLE := SessionANT.Numfield.«NUMBER_FIELD_INTEGRAL_MULTIPLE»
  NUM_OF_INT_OF_NUM := Session.NUM_OF_INT_OF_NUM
  POLY_0 := SessionLibrary.RingTheory.«POLY_0»
  POLY_COMPOSE_HOMOMORPHISM_CONST := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_CONST»
  POLY_COMPOSE_HOMOMORPHISM_VAR := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_VAR»
  POLY_CONST := SessionLibrary.RingTheory.«POLY_CONST»
  POLY_DEG_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_DEG_MONOMORPHIC_IMAGE»
  POLY_DEG_PRODUCT_POW_MONIC := SessionLibrary.RingTheory.«POLY_DEG_PRODUCT_POW_MONIC»
  POLY_DEG_REM := SessionLibrary.RingTheory.«POLY_DEG_REM»
  POLY_DIV := SessionLibrary.RingTheory.«POLY_DIV»
  POLY_DIV_REM_SIMP := SessionLibrary.RingTheory.«POLY_DIV_REM_SIMP»
  POLY_EXTEND := SessionLibrary.RingTheory.«POLY_EXTEND»
  POLY_EXTEND_COMPOSE_COEFFS := SessionLibrary.RingTheory.«POLY_EXTEND_COMPOSE_COEFFS»
  POLY_EXTEND_CONST := SessionLibrary.RingTheory.«POLY_EXTEND_CONST»
  POLY_EXTEND_EQ := SessionLibrary.RingTheory.«POLY_EXTEND_EQ»
  POLY_EXTEND_EVALUATE := SessionLibrary.RingTheory.«POLY_EXTEND_EVALUATE»
  POLY_EXTEND_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_EXTEND_HOMOMORPHIC_IMAGE»
  POLY_EXTEND_INTO_SUBRING_GENERATED := SessionLibrary.RingTheory.«POLY_EXTEND_INTO_SUBRING_GENERATED»
  POLY_EXTEND_SUB := SessionLibrary.RingTheory.«POLY_EXTEND_SUB»
  POLY_EXTEND_SUPERSET := SessionLibrary.RingTheory.«POLY_EXTEND_SUPERSET»
  POLY_EXTEND_UNIVARIATE := SessionLibrary.RingTheory.«POLY_EXTEND_UNIVARIATE»
  POLY_EXTEND_VAR := SessionLibrary.RingTheory.«POLY_EXTEND_VAR»
  POLY_REM := SessionLibrary.RingTheory.«POLY_REM»
  POLY_RING_CLAUSES := SessionLibrary.RingTheory.«POLY_RING_CLAUSES»
  POLY_RING_INTEGER_MOD_RING_OF_INT := SessionLibrary.RingTheory.«POLY_RING_INTEGER_MOD_RING_OF_INT»
  POLY_VAR_UNIV := SessionLibrary.RingTheory.«POLY_VAR_UNIV»
/-- The core theorems dedekind_kummer.ml uses. -/
def core2 : HolANT.DedekindKummer.CoreThms2 where
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PROPER_IDEAL_HOMOMORPHIC_PREIMAGE := SessionLibrary.RingTheory.«PROPER_IDEAL_HOMOMORPHIC_PREIMAGE»
  PSUBSET := Session.PSUBSET
  QUOTIENT_POLY_RING_HAS_SIZE := SessionLibrary.RingTheory.«QUOTIENT_POLY_RING_HAS_SIZE»
  QUOTIENT_RING_0 := SessionLibrary.RingTheory.«QUOTIENT_RING_0»
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
  QUOTIENT_RING_PREIMAGE_IDEAL_GENERATED := SessionLibrary.RingTheory.«QUOTIENT_RING_PREIMAGE_IDEAL_GENERATED»
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_CARRIER_POLY_RING := SessionLibrary.RingTheory.«RING_CARRIER_POLY_RING»
  RING_CARRIER_SUBRING_GENERATED_0 := SessionLibrary.RingTheory.«RING_CARRIER_SUBRING_GENERATED_0»
  RING_CARRIER_SUBRING_GENERATED_SUBSET := SessionLibrary.RingTheory.«RING_CARRIER_SUBRING_GENERATED_SUBSET»
  RING_CHAR_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_CHAR_SUBFIELD_GENERATED»
  RING_COSET := SessionLibrary.RingTheory.«RING_COSET»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_COSET_EQ_IDEAL := SessionLibrary.RingTheory.«RING_COSET_EQ_IDEAL»
  RING_DIVIDES_PRODUCT_POW := SessionLibrary.RingTheory.«RING_DIVIDES_PRODUCT_POW»
  RING_DIVIDES_REFL := SessionLibrary.RingTheory.«RING_DIVIDES_REFL»
  RING_EPIMORPHISM_EQ := SessionLibrary.RingTheory.«RING_EPIMORPHISM_EQ»
  RING_EPIMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_EPIMORPHISM_IMP_HOMOMORPHISM»
  RING_EPIMORPHISM_INTEGER_MOD_RING := SessionLibrary.RingTheory.«RING_EPIMORPHISM_INTEGER_MOD_RING»
  RING_EPIMORPHISM_POLY_RINGS := SessionLibrary.RingTheory.«RING_EPIMORPHISM_POLY_RINGS»
  RING_EPIMORPHISM_PREIMAGE_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_EPIMORPHISM_PREIMAGE_IDEAL_GENERATED»
  RING_EPIMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_EPIMORPHISM_RING_COSET»
  RING_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_EPIMORPHISM_FACTOR := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_EPIMORPHISM_FACTOR»
  RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_POLY_EXTEND := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_EXTEND»
  RING_HOMOMORPHISM_POLY_RINGS := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_RINGS»
  RING_HOMOMORPHISM_PRODUCT_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_PRODUCT_POW»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_HOMOMORPHISM_RING_OF_INTEGERS»
  RING_HOMOMORPHISM_RING_OF_NUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_NUM»
  RING_HOMOMORPHISM_SUB := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUB»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_IDEAL_0 := SessionLibrary.RingTheory.«RING_IDEAL_0»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IDEAL_PRODUCT := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PRODUCT»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_IDEAL_RING_KERNEL := SessionLibrary.RingTheory.«RING_IDEAL_RING_KERNEL»
  RING_KERNEL_INTEGER_MOD_RING := SessionLibrary.RingTheory.«RING_KERNEL_INTEGER_MOD_RING»
  RING_KERNEL_RING_COSET := SessionLibrary.RingTheory.«RING_KERNEL_RING_COSET»
  RING_MONOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INTEGER_RING_OF_INT»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_CARRIER := SessionANT.Numfield.«RING_OF_INTEGERS_CARRIER»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_IDEAL_EXTENSION := SessionANT.RelativeSplit.«RING_OF_INTEGERS_IDEAL_EXTENSION»
  RING_OF_INTEGERS_IDEAL_NORM_INTEGER := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_IDEAL_NORM_INTEGER»
  RING_OF_INTEGERS_INTEGRAL_ELEMENT := SessionANT.Integrality.«RING_OF_INTEGERS_INTEGRAL_ELEMENT»
  RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q := SessionANT.Integrality.«RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_1 := SessionLibrary.RingTheory.«RING_OF_INT_1»
  RING_OF_INT_EQ_0_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0_CHAR_0»
  RING_OF_INT_EQ_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_CHAR_0»
  RING_OF_INT_IN_RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INT_IN_RING_OF_INTEGERS»
  RING_OF_INT_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_IN_SUBFIELD_GENERATED»
  RING_OF_INT_MUL := SessionLibrary.RingTheory.«RING_OF_INT_MUL»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_INT_SUB := SessionLibrary.RingTheory.«RING_OF_INT_SUB»
  RING_OF_INT_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_SUBFIELD_GENERATED»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_POLYNOMIAL := SessionLibrary.RingTheory.«RING_POLYNOMIAL»
  RING_POLYNOMIAL_COEFF := SessionLibrary.RingTheory.«RING_POLYNOMIAL_COEFF»
  RING_POLYNOMIAL_CONST := SessionLibrary.RingTheory.«RING_POLYNOMIAL_CONST»
  RING_POLYNOMIAL_VAR := SessionLibrary.RingTheory.«RING_POLYNOMIAL_VAR»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_PRODUCT := SessionLibrary.RingTheory.«RING_PRODUCT»
  RING_SETADD := SessionLibrary.RingTheory.«RING_SETADD»
  RING_SETADD_MONO := SessionLibrary.RingTheory.«RING_SETADD_MONO»
  RING_SETADD_SYM := SessionLibrary.RingTheory.«RING_SETADD_SYM»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_RDISTRIB := SessionLibrary.RingTheory.«RING_SUB_RDISTRIB»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_SUPERSET := SessionLibrary.RingTheory.«RING_SUM_SUPERSET»
  RING_UNIT_1 := SessionLibrary.RingTheory.«RING_UNIT_1»
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SIMPLE_IMAGE := Session.SIMPLE_IMAGE
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBRING_GENERATED_IDEMPOT_GEN := SessionLibrary.RingTheory.«SUBRING_GENERATED_IDEMPOT_GEN»
  SUBRING_GENERATED_INSERT := SessionLibrary.RingTheory.«SUBRING_GENERATED_INSERT»
  SUBRING_GENERATED_INSERT_ZERO := SessionLibrary.RingTheory.«SUBRING_GENERATED_INSERT_ZERO»
  SUBRING_GENERATED_MINIMAL := SessionLibrary.RingTheory.«SUBRING_GENERATED_MINIMAL»
  SUBRING_SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_SUBRING_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_REFL := Session.SUBSET_REFL
  SUBSET_UNIV := Session.SUBSET_UNIV
  TRIVIAL_RING_10 := SessionLibrary.RingTheory.«TRIVIAL_RING_10»
  coeff := SessionLibrary.RingTheory.«coeff»
  ideal_norm := SessionANT.IdealNorm.«ideal_norm»
  integral_element := SessionANT.Integral.«integral_element»
  maximal_ideal := SessionLibrary.RingTheory.«maximal_ideal»
  monic := SessionLibrary.RingTheory.«monic»
  num_INFINITE := Session.num_INFINITE
  number_field := SessionANT.Numfield.«number_field»
  o_THM := Session.o_THM
  one := Session.one
  poly_extend := SessionLibrary.RingTheory.«poly_extend»
  ramification_index := SessionANT.PrimeSplit.«ramification_index»
  ring_associates := SessionLibrary.RingTheory.«ring_associates»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_epimorphism := SessionLibrary.RingTheory.«ring_epimorphism»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_kernel := SessionLibrary.RingTheory.«ring_kernel»
  ring_of_integers := SessionANT.Numfield.«ring_of_integers»
  ring_setadd := SessionLibrary.RingTheory.«ring_setadd»
  subring_of := SessionLibrary.RingTheory.«subring_of»

/-- What dedekind_kummer.ml uses from Session. -/
def deps : HolANT.DedekindKummer.DedekindKummerDeps where
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

/- The bundles, in dedekind_kummer.ml order. -/
initialize BDedekindKummer01 : HolANT.DedekindKummer.DedekindKummer01 ←
  ioB "setupDedekindKummer01" (HolANT.DedekindKummer.setupDedekindKummer01 deps).run
initialize BDedekindKummer02 : HolANT.DedekindKummer.DedekindKummer02 ←
  ioB "setupDedekindKummer02" (HolANT.DedekindKummer.setupDedekindKummer02 deps BDedekindKummer01).run
initialize BDedekindKummer03 : HolANT.DedekindKummer.DedekindKummer03 ←
  ioB "setupDedekindKummer03" (HolANT.DedekindKummer.setupDedekindKummer03 deps BDedekindKummer01 BDedekindKummer02).run

-- DedekindKummer01
def RING_EPIMORPHISM_KERNEL_EQ : thm := BDedekindKummer01.RING_EPIMORPHISM_KERNEL_EQ
def POLY_RING_INTEGER_MOD_RING_SUBSET : thm := BDedekindKummer01.POLY_RING_INTEGER_MOD_RING_SUBSET
def POLY_EXTEND_INTEGER_MOD_RING : thm := BDedekindKummer01.POLY_EXTEND_INTEGER_MOD_RING
def RING_HOMOMORPHISM_POLY_EXTEND_INTEGER_MOD_RING : thm := BDedekindKummer01.RING_HOMOMORPHISM_POLY_EXTEND_INTEGER_MOD_RING
def POLY_EXTEND_INTEGER_MOD_RING_OF_INT : thm := BDedekindKummer01.POLY_EXTEND_INTEGER_MOD_RING_OF_INT
def POLY_EXTEND_FROM_COEFFS : thm := BDedekindKummer01.POLY_EXTEND_FROM_COEFFS
def IMAGE_POLY_EXTEND_INTEGER_RING : thm := BDedekindKummer01.IMAGE_POLY_EXTEND_INTEGER_RING
def SUBRING_GENERATED_INT_LINCOMB : thm := BDedekindKummer01.SUBRING_GENERATED_INT_LINCOMB
def RING_EPIMORPHISM_POLY_EXTEND_QUOTIENT_RING : thm := BDedekindKummer01.RING_EPIMORPHISM_POLY_EXTEND_QUOTIENT_RING
def POLY_EXTEND_RING_OF_INTEGERS : thm := BDedekindKummer01.POLY_EXTEND_RING_OF_INTEGERS
def RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL : thm := BDedekindKummer01.RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL
def NUMBER_FIELD_FINITE_INDEX_MULTIPLE : thm := BDedekindKummer01.NUMBER_FIELD_FINITE_INDEX_MULTIPLE
def SUBRING_GENERATED_INDEX_COPRIME : thm := BDedekindKummer01.SUBRING_GENERATED_INDEX_COPRIME
def DEDEKIND_KUMMER_EPIMORPHISM : thm := BDedekindKummer01.DEDEKIND_KUMMER_EPIMORPHISM
def DEDEKIND_KUMMER_KERNEL : thm := BDedekindKummer01.DEDEKIND_KUMMER_KERNEL
def DEDEKIND_KUMMER_QUOTIENT_RING : thm := BDedekindKummer01.DEDEKIND_KUMMER_QUOTIENT_RING

-- DedekindKummer02
def DEDEKIND_KUMMER_FACTOR : thm := BDedekindKummer02.DEDEKIND_KUMMER_FACTOR
def DEDEKIND_KUMMER : thm := BDedekindKummer02.DEDEKIND_KUMMER
def NUMBER_FIELD_DEDEKIND_KUMMER_DATA : thm := BDedekindKummer02.NUMBER_FIELD_DEDEKIND_KUMMER_DATA
def NUMBER_FIELD_DEDEKIND_KUMMER_QUOTIENT_RING : thm := BDedekindKummer02.NUMBER_FIELD_DEDEKIND_KUMMER_QUOTIENT_RING

-- DedekindKummer03
def NUMBER_FIELD_DEDEKIND_KUMMER_FACTOR : thm := BDedekindKummer03.NUMBER_FIELD_DEDEKIND_KUMMER_FACTOR
def NUMBER_FIELD_DEDEKIND_KUMMER : thm := BDedekindKummer03.NUMBER_FIELD_DEDEKIND_KUMMER
def DEDEKIND_KUMMER_EPIMORPHISM_Q : thm := BDedekindKummer03.DEDEKIND_KUMMER_EPIMORPHISM_Q
def DEDEKIND_KUMMER_INTEGER_DATA : thm := BDedekindKummer03.DEDEKIND_KUMMER_INTEGER_DATA
def DEDEKIND_KUMMER_QUOTIENT_RING_Q : thm := BDedekindKummer03.DEDEKIND_KUMMER_QUOTIENT_RING_Q
def DEDEKIND_KUMMER_FACTOR_Q : thm := BDedekindKummer03.DEDEKIND_KUMMER_FACTOR_Q
def DEDEKIND_KUMMER_Q : thm := BDedekindKummer03.DEDEKIND_KUMMER_Q
def DEDEKIND_KUMMER_LINEAR_IDEAL : thm := BDedekindKummer03.DEDEKIND_KUMMER_LINEAR_IDEAL

/-- `needs "ANT/dedekind_kummer.ml"`: already done by importing this module. -/
def ensureDedekindKummer : IO Unit := pure ()

end SessionANT.DedekindKummer
