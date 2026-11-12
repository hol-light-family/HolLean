/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/cyclotomic_integers.ml                        . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/CyclotomicIntegers.lean

  The session half of the cyclotomic_integers.ml translation: it supplies HolANT.CyclotomicIntegers's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/cyclotomic_integers.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.CyclotomicIntegers
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
import SessionLibrary.Integer
import SessionLibrary.Isum
import SessionLibrary.Multiplicative
import SessionLibrary.Primitive
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionANT.PrimeSplit
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.RelativeDegree
import SessionANT.NfValuation
import SessionANT.Integrality
import SessionANT.DedekindKummer
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionANT.CyclotomicPoly
import SessionANT.PowerBasis
import SessionANT.CyclotomicField

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.CyclotomicIntegers

/-- The core theorems cyclotomic_integers.ml uses. -/
def core1 : HolANT.CyclotomicIntegers.CoreThms1 where
  ADD_CLAUSES := Session.ADD_CLAUSES
  ADD_EQ_0 := Session.ADD_EQ_0
  ADD_SUB := Session.ADD_SUB
  ALGEBRA_TRACE_NORM_IN_CARRIER := SessionLibrary.RingDet.«ALGEBRA_TRACE_NORM_IN_CARRIER»
  ALGEBRA_TRACE_PRODUCT_BASIS := SessionANT.PowerBasis.«ALGEBRA_TRACE_PRODUCT_BASIS»
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  CONG_SOLVE := SessionLibrary.Pocklington.«CONG_SOLVE»
  COPRIME_0 := SessionLibrary.Prime.«COPRIME_0»
  COPRIME_1 := SessionLibrary.Prime.«COPRIME_1»
  COPRIME_BEZOUT_STRONG := SessionLibrary.Prime.«COPRIME_BEZOUT_STRONG»
  COPRIME_LEXP := SessionLibrary.Prime.«COPRIME_LEXP»
  COPRIME_PRIMEPOW := SessionLibrary.Prime.«COPRIME_PRIMEPOW»
  COPRIME_SYM := SessionLibrary.Prime.«COPRIME_SYM»
  CYCLOTOMIC_FIELD_DEGREE := SessionANT.CyclotomicField.«CYCLOTOMIC_FIELD_DEGREE»
  CYCLOTOMIC_FIELD_FREE_BASIS := SessionANT.CyclotomicField.«CYCLOTOMIC_FIELD_FREE_BASIS»
  CYCLOTOMIC_POLY_DEG := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_DEG»
  CYCLOTOMIC_POLY_EVAL_0 := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_EVAL_0»
  CYCLOTOMIC_POLY_EVAL_1_PRIME_POWER := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_EVAL_1_PRIME_POWER»
  CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE»
  CYCLOTOMIC_POLY_IN_CARRIER := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_IN_CARRIER»
  CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL := SessionANT.CyclotomicField.«CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL»
  CYCLOTOMIC_POLY_MONIC := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_MONIC»
  CYCLOTOMIC_POLY_PRODUCT := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_PRODUCT»
  CYCLOTOMIC_POLY_ROOT := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_ROOT»
  CYCLOTOMIC_POLY_SPLITS := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_SPLITS»
  CYCLOTOMIC_POLY_SQUAREFREE := SessionANT.CyclotomicPoly.«CYCLOTOMIC_POLY_SQUAREFREE»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DISJOINT := Session.DISJOINT
  DIVIDES_0 := SessionLibrary.Prime.«DIVIDES_0»
  DIVIDES_LMUL := SessionLibrary.Prime.«DIVIDES_LMUL»
  DIVIDES_ONE := Session.DIVIDES_ONE
  DIVIDES_PRIMEPOW := SessionLibrary.Prime.«DIVIDES_PRIMEPOW»
  DIVIDES_PRIME_PRIME := SessionLibrary.Prime.«DIVIDES_PRIME_PRIME»
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  DIVIDES_RMUL := SessionLibrary.Prime.«DIVIDES_RMUL»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  DIV_MULT := Session.DIV_MULT
  DIV_UNIQ := Session.DIV_UNIQ
  EQ_EXP := Session.EQ_EXP
  EVEN := Session.EVEN
  EVEN_ADD := Session.EVEN_ADD
  EVEN_EXISTS := Session.EVEN_EXISTS
  EVEN_MULT := Session.EVEN_MULT
  EVEN_OR_ODD := Session.EVEN_OR_ODD
  EVEN_SUB := Session.EVEN_SUB
  EXISTS_IN_IMAGE := Session.EXISTS_IN_IMAGE
  EXP := Session.EXP
  EXP_1 := Session.EXP_1
  EXP_ADD := Session.EXP_ADD
  EXP_EQ_0 := Session.EXP_EQ_0
  EXP_EQ_1 := Session.EXP_EQ_1
  EXP_MULT := Session.EXP_MULT
  EXP_ONE := Session.EXP_ONE
  EXTENSION := Session.EXTENSION
  EXTENSION_LINCOMB_SUM := SessionLibrary.RingDet.«EXTENSION_LINCOMB_SUM»
  FIELD_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_INTEGER_MOD_RING := SessionLibrary.RingTheory.«FIELD_INTEGER_MOD_RING»
  FIELD_MUL_LINV := SessionLibrary.RingTheory.«FIELD_MUL_LINV»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_DIVISORS := SessionLibrary.Prime.«FINITE_DIVISORS»
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_SING := Session.FINITE_SING
  FINITE_SPECIAL_DIVISORS := SessionLibrary.Prime.«FINITE_SPECIAL_DIVISORS»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FREE_BASIS_INDEPENDENT := SessionLibrary.RingDet.«FREE_BASIS_INDEPENDENT»
  FREE_BASIS_INTEGER_RING_SUBRING_GENERATED := SessionANT.RingOfIntegers.«FREE_BASIS_INTEGER_RING_SUBRING_GENERATED»
  FREE_BASIS_PRIME_SUBFIELD_DENOMINATOR := SessionANT.Numfield.«FREE_BASIS_PRIME_SUBFIELD_DENOMINATOR»
  FREE_BASIS_SPANNING_DEGREE := SessionLibrary.FieldTheory.«FREE_BASIS_SPANNING_DEGREE»
  FUN_EQ_THM := Session.FUN_EQ_THM
  IMAGE_POLY_EXTEND_INTEGER_RING := SessionANT.DedekindKummer.«IMAGE_POLY_EXTEND_INTEGER_RING»
  IMP_CONJ := Session.IMP_CONJ
  IMP_IMP := Session.IMP_IMP
  INDEX_DECOMPOSITION := SessionLibrary.Prime.«INDEX_DECOMPOSITION»
  INDEX_DECOMPOSITION_PRIME := SessionLibrary.Prime.«INDEX_DECOMPOSITION_PRIME»
  INTEGER_MOD_RING_CHAR := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CHAR»
  INTEGER_MOD_RING_CLAUSES := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CLAUSES»
  INTEGER_MOD_RING_OF_INT := SessionLibrary.RingTheory.«INTEGER_MOD_RING_OF_INT»
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGER_RING_DIVIDES := SessionLibrary.RingTheory.«INTEGER_RING_DIVIDES»
  INTEGER_RING_OF_NUM := SessionLibrary.RingTheory.«INTEGER_RING_OF_NUM»
  INTEGRAL_DOMAIN_MUL_LCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_LCANCEL»
  INTEGRAL_DOMAIN_POW_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_POW_EQ_0»
  INTEGRAL_DOMAIN_SUBRING_GENERATED := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_SUBRING_GENERATED»
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_ENTIRE := Session.INT_ENTIRE
  INT_EQ_MUL_RCANCEL := Session.INT_EQ_MUL_RCANCEL
  INT_LE_SQUARE := Session.INT_LE_SQUARE
  INT_MUL_ASSOC := Session.INT_MUL_ASSOC
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_OF_NUM_POW := Session.INT_OF_NUM_POW
  INT_POW_1 := Session.INT_POW_1
  INT_POW_ADD := Session.INT_POW_ADD
  INT_POW_MUL := Session.INT_POW_MUL
  INT_POW_NEG := Session.INT_POW_NEG
  INT_POW_ONE := Session.INT_POW_ONE
  INT_POW_POW := Session.INT_POW_POW
  INT_REM_EQ_0 := Session.INT_REM_EQ_0
  INT_REM_EQ_SELF := Session.INT_REM_EQ_SELF
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_INTEGER_MOD_RING_CARRIER := SessionLibrary.RingTheory.«IN_INTEGER_MOD_RING_CARRIER»
  IN_INTER := Session.IN_INTER
  IN_POLY_RING_CARRIER := SessionLibrary.RingTheory.«IN_POLY_RING_CARRIER»
/-- The core theorems cyclotomic_integers.ml uses. -/
def core2 : HolANT.CyclotomicIntegers.CoreThms2 where
  IN_RING_POLYNOMIAL_CARRIER_COMPOSE := SessionLibrary.RingTheory.«IN_RING_POLYNOMIAL_CARRIER_COMPOSE»
  IN_SING := Session.IN_SING
  IN_SUBRING_0 := SessionLibrary.RingTheory.«IN_SUBRING_0»
  IN_SUBRING_1 := SessionLibrary.RingTheory.«IN_SUBRING_1»
  IN_SUBRING_ADD := SessionLibrary.RingTheory.«IN_SUBRING_ADD»
  IN_SUBRING_INT := SessionLibrary.RingTheory.«IN_SUBRING_INT»
  IN_SUBRING_MUL := SessionLibrary.RingTheory.«IN_SUBRING_MUL»
  IN_SUBRING_NEG := SessionLibrary.RingTheory.«IN_SUBRING_NEG»
  IN_SUBRING_NUM := SessionLibrary.RingTheory.«IN_SUBRING_NUM»
  IN_SUBRING_POW := SessionLibrary.RingTheory.«IN_SUBRING_POW»
  IN_SUBRING_SUB := SessionLibrary.RingTheory.«IN_SUBRING_SUB»
  IN_UNION := Session.IN_UNION
  IN_UNIV := Session.IN_UNIV
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LEFT_ADD_DISTRIB := Session.LEFT_ADD_DISTRIB
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_1 := Session.LE_1
  LE_EXP := Session.LE_EXP
  LE_REFL := Session.LE_REFL
  LE_TRANS := Session.LE_TRANS
  LT_MULT_LCANCEL := Session.LT_MULT_LCANCEL
  LT_MULT_RCANCEL := Session.LT_MULT_RCANCEL
  MULT_AC := Session.MULT_AC
  MULT_ASSOC := Session.MULT_ASSOC
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_EXP := Session.MULT_EXP
  MULT_SYM := Session.MULT_SYM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_ODD := Session.NOT_ODD
  NPRODUCT_CLAUSES := Session.NPRODUCT_CLAUSES
  NPRODUCT_DELETE := SessionLibrary.Products.«NPRODUCT_DELETE»
  NPRODUCT_EQ := SessionLibrary.Products.«NPRODUCT_EQ»
  NPRODUCT_SING := SessionLibrary.Products.«NPRODUCT_SING»
  NPRODUCT_UNION := SessionLibrary.Products.«NPRODUCT_UNION»
  NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD := SessionANT.Discriminant.«NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD»
  NUMBER_FIELD_DISCRIMINANT_NONZERO := SessionANT.Discriminant.«NUMBER_FIELD_DISCRIMINANT_NONZERO»
  NUMBER_FIELD_DISCRIMINANT_POWER_BASIS := SessionANT.PowerBasis.«NUMBER_FIELD_DISCRIMINANT_POWER_BASIS»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_INTEGER_MINIMAL_POLYNOMIAL_DIVIDES := SessionANT.CyclotomicField.«NUMBER_FIELD_INTEGER_MINIMAL_POLYNOMIAL_DIVIDES»
  NUMBER_FIELD_NORM_MUL := SessionANT.Numfield.«NUMBER_FIELD_NORM_MUL»
  NUMBER_FIELD_NORM_RATIONAL := SessionANT.Numfield.«NUMBER_FIELD_NORM_RATIONAL»
  NUMBER_FIELD_NORM_SUB_MINIMAL_POLYNOMIAL := SessionANT.Numfield.«NUMBER_FIELD_NORM_SUB_MINIMAL_POLYNOMIAL»
  NUMBER_FIELD_NORM_TOWER := SessionANT.PowerBasis.«NUMBER_FIELD_NORM_TOWER»
  NUMBER_FIELD_SUBFIELD_GENERATED := SessionANT.RelativeSplit.«NUMBER_FIELD_SUBFIELD_GENERATED»
  NUMBER_FIELD_TOWER_LAW := SessionANT.RelativeSplit.«NUMBER_FIELD_TOWER_LAW»
  ODD_EXISTS := Session.ODD_EXISTS
  ODD_PHI_EQ := SessionLibrary.Pocklington.«ODD_PHI_EQ»
  PHI_1 := SessionLibrary.Pocklington.«PHI_1»
  PHI_2 := SessionLibrary.Pocklington.«PHI_2»
  PHI_ALT := SessionLibrary.Pocklington.«PHI_ALT»
  PHI_EQ_0 := SessionLibrary.Pocklington.«PHI_EQ_0»
  PHI_EXPAND := SessionLibrary.Multiplicative.«PHI_EXPAND»
  PHI_MULTIPLICATIVE := SessionLibrary.Pocklington.«PHI_MULTIPLICATIVE»
  PHI_PRIME := SessionLibrary.Pocklington.«PHI_PRIME»
  PHI_PRIMEPOW_ALT := SessionLibrary.Pocklington.«PHI_PRIMEPOW_ALT»
  PID_IMP_UFD := SessionLibrary.RingTheory.«PID_IMP_UFD»
  PID_POLY_RING := SessionLibrary.RingTheory.«PID_POLY_RING»
  POLY_0 := SessionLibrary.RingTheory.«POLY_0»
  POLY_CONST_DIVIDES_COEFFS := SessionLibrary.RingTheory.«POLY_CONST_DIVIDES_COEFFS»
  POLY_DERIV_1 := SessionLibrary.RingTheory.«POLY_DERIV_1»
  POLY_DERIV_MUL := SessionLibrary.RingTheory.«POLY_DERIV_MUL»
  POLY_DERIV_SUB := SessionLibrary.RingTheory.«POLY_DERIV_SUB»
  POLY_DERIV_VAR_POW := SessionLibrary.RingTheory.«POLY_DERIV_VAR_POW»
  POLY_EVAL := SessionLibrary.RingTheory.«POLY_EVAL»
  POLY_EVAL_0 := SessionLibrary.RingTheory.«POLY_EVAL_0»
  POLY_EVAL_1 := SessionLibrary.RingTheory.«POLY_EVAL_1»
  POLY_EVAL_ADD := SessionLibrary.RingTheory.«POLY_EVAL_ADD»
  POLY_EVAL_CONST := SessionLibrary.RingTheory.«POLY_EVAL_CONST»
  POLY_EVAL_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_EVAL_HOMOMORPHIC_IMAGE»
  POLY_EVAL_MUL := SessionLibrary.RingTheory.«POLY_EVAL_MUL»
  POLY_EVAL_POW := SessionLibrary.RingTheory.«POLY_EVAL_POW»
  POLY_EVAL_RING_PRODUCT := SessionLibrary.RingTheory.«POLY_EVAL_RING_PRODUCT»
  POLY_EVAL_SUB := SessionLibrary.RingTheory.«POLY_EVAL_SUB»
  POLY_EVAL_VAR := SessionLibrary.RingTheory.«POLY_EVAL_VAR»
  POLY_EXTEND := SessionLibrary.RingTheory.«POLY_EXTEND»
  POLY_EXTEND_EVALUATE := SessionLibrary.RingTheory.«POLY_EXTEND_EVALUATE»
  POLY_RING_CLAUSES := SessionLibrary.RingTheory.«POLY_RING_CLAUSES»
  POLY_RING_INTEGER_MOD_RING_SUBSET := SessionANT.DedekindKummer.«POLY_RING_INTEGER_MOD_RING_SUBSET»
  PRIME_1 := SessionLibrary.Prime.«PRIME_1»
  PRIME_COPRIME_EQ := SessionLibrary.Prime.«PRIME_COPRIME_EQ»
  PRIME_DIVEXP := SessionLibrary.Prime.«PRIME_DIVEXP»
  PRIME_DIVPROD_EQ := SessionLibrary.Prime.«PRIME_DIVPROD_EQ»
  PRIME_FACTOR := SessionLibrary.Prime.«PRIME_FACTOR»
  PRIME_GE_2 := SessionLibrary.Prime.«PRIME_GE_2»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_SUBFIELD_GENERATED»
  RIGHT_ADD_DISTRIB := Session.RIGHT_ADD_DISTRIB
  RINGS_EQ := SessionLibrary.RingTheory.«RINGS_EQ»
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_CARRIER_SUBFIELD_GENERATED_SUBSET := SessionLibrary.FieldTheory.«RING_CARRIER_SUBFIELD_GENERATED_SUBSET»
  RING_CARRIER_SUBRING_GENERATED_SUBSET := SessionLibrary.RingTheory.«RING_CARRIER_SUBRING_GENERATED_SUBSET»
  RING_CHAR_POLY_RING := SessionLibrary.RingTheory.«RING_CHAR_POLY_RING»
  RING_DET_EQ := SessionLibrary.RingDet.«RING_DET_EQ»
  RING_DET_KRONECKER_MOD_DIV := SessionLibrary.RingDet.«RING_DET_KRONECKER_MOD_DIV»
  RING_DIVIDES_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_DIVIDES_HOMOMORPHIC_IMAGE»
  RING_DIVIDES_PRODUCTS := SessionLibrary.RingTheory.«RING_DIVIDES_PRODUCTS»
  RING_DIVIDES_SUB_POW := SessionLibrary.RingTheory.«RING_DIVIDES_SUB_POW»
  RING_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_POLY_EXTEND := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_EXTEND»
  RING_HOMOMORPHISM_POLY_RINGS := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_RINGS»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_RING_OF_NUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_NUM»
  RING_HOMOMORPHISM_SUB := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUB»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
/-- The core theorems cyclotomic_integers.ml uses. -/
def core3 : HolANT.CyclotomicIntegers.CoreThms3 where
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_INV_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_INV_IN_SUBFIELD_GENERATED»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_MUL_IN_SUBFIELD_GENERATED»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_POW := SessionLibrary.RingTheory.«RING_MUL_POW»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_CARRIER := SessionANT.Numfield.«RING_OF_INTEGERS_CARRIER»
  RING_OF_INTEGERS_DISCRIMINANT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_DISCRIMINANT»
  RING_OF_INTEGERS_FREE_BASIS_FIELD := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE_BASIS_FIELD»
  RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE := SessionANT.RelativeSplit.«RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_0 := SessionLibrary.RingTheory.«RING_OF_INT_0»
  RING_OF_INT_1 := SessionLibrary.RingTheory.«RING_OF_INT_1»
  RING_OF_INT_ADD := SessionLibrary.RingTheory.«RING_OF_INT_ADD»
  RING_OF_INT_EQ := SessionLibrary.RingTheory.«RING_OF_INT_EQ»
  RING_OF_INT_EQ_0_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0_CHAR_0»
  RING_OF_INT_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_IN_SUBFIELD_GENERATED»
  RING_OF_INT_MUL := SessionLibrary.RingTheory.«RING_OF_INT_MUL»
  RING_OF_INT_NEG := SessionLibrary.RingTheory.«RING_OF_INT_NEG»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_INT_POW := SessionLibrary.RingTheory.«RING_OF_INT_POW»
  RING_OF_INT_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_SUBFIELD_GENERATED»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_1 := SessionLibrary.RingTheory.«RING_OF_NUM_1»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_OF_NUM_EXP := SessionLibrary.RingTheory.«RING_OF_NUM_EXP»
  RING_OF_NUM_MUL := SessionLibrary.RingTheory.«RING_OF_NUM_MUL»
  RING_OF_NUM_POLY_RING := SessionLibrary.RingTheory.«RING_OF_NUM_POLY_RING»
  RING_OF_NUM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_NUM_SUBFIELD_GENERATED»
  RING_OF_NUM_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_OF_NUM_SUBRING_GENERATED»
  RING_ORDER_1 := SessionLibrary.RingTheory.«RING_ORDER_1»
  RING_ORDER_POW := SessionLibrary.RingTheory.«RING_ORDER_POW»
  RING_ORDER_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_ORDER_SUBFIELD_GENERATED»
  RING_ORDER_UNIQUE := SessionLibrary.RingTheory.«RING_ORDER_UNIQUE»
  RING_POLYNOMIAL := SessionLibrary.RingTheory.«RING_POLYNOMIAL»
  RING_POLYNOMIAL_0 := SessionLibrary.RingTheory.«RING_POLYNOMIAL_0»
  RING_POLYNOMIAL_1 := SessionLibrary.RingTheory.«RING_POLYNOMIAL_1»
  RING_POLYNOMIAL_CONST := SessionLibrary.RingTheory.«RING_POLYNOMIAL_CONST»
  RING_POLYNOMIAL_IMP_POWERSERIES := SessionLibrary.RingTheory.«RING_POLYNOMIAL_IMP_POWERSERIES»
  RING_POLYNOMIAL_MUL := SessionLibrary.RingTheory.«RING_POLYNOMIAL_MUL»
  RING_POLYNOMIAL_POLY_DERIV := SessionLibrary.RingTheory.«RING_POLYNOMIAL_POLY_DERIV»
  RING_POLYNOMIAL_POW := SessionLibrary.RingTheory.«RING_POLYNOMIAL_POW»
  RING_POLYNOMIAL_SUB := SessionLibrary.RingTheory.«RING_POLYNOMIAL_SUB»
  RING_POLYNOMIAL_VAR := SessionLibrary.RingTheory.«RING_POLYNOMIAL_VAR»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_1 := SessionLibrary.RingTheory.«RING_POW_1»
  RING_POW_ADD := SessionLibrary.RingTheory.«RING_POW_ADD»
  RING_POW_EQ_1 := SessionLibrary.RingTheory.«RING_POW_EQ_1»
  RING_POW_EQ_GEN := SessionLibrary.RingTheory.«RING_POW_EQ_GEN»
  RING_POW_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_POW_IN_SUBFIELD_GENERATED»
  RING_POW_MUL := SessionLibrary.RingTheory.«RING_POW_MUL»
  RING_POW_ONE := SessionLibrary.RingTheory.«RING_POW_ONE»
  RING_POW_POW := SessionLibrary.RingTheory.«RING_POW_POW»
  RING_POW_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_POW_SUBFIELD_GENERATED»
  RING_POW_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_POW_SUBRING_GENERATED»
  RING_PRODUCT_CLAUSES := SessionLibrary.RingTheory.«RING_PRODUCT_CLAUSES»
  RING_PRODUCT_CONST := SessionLibrary.RingTheory.«RING_PRODUCT_CONST»
  RING_PRODUCT_EQ := SessionLibrary.RingTheory.«RING_PRODUCT_EQ»
  RING_SQUAREFREE_DIVPOW := SessionLibrary.RingTheory.«RING_SQUAREFREE_DIVPOW»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_SUB_RZERO := SessionLibrary.RingTheory.«RING_SUB_RZERO»
  RING_SUB_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_SUB_SUBFIELD_GENERATED»
  RING_SUB_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_SUB_SUBRING_GENERATED»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_MUL_MOD_DIV := SessionLibrary.RingTheory.«RING_SUM_MUL_MOD_DIV»
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_IDEMPOT := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_IDEMPOT»
  SUBFIELD_GENERATED_INC := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_INC»
  SUBFIELD_GENERATED_SUBSET_CARRIER := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_SUBSET_CARRIER»
  SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_GENERATED»
  SUBRING_GENERATED_BY_SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_GENERATED_BY_SUBRING_GENERATED»
  SUBRING_GENERATED_INC := SessionLibrary.RingTheory.«SUBRING_GENERATED_INC»
  SUBRING_GENERATED_INT_LINCOMB := SessionANT.DedekindKummer.«SUBRING_GENERATED_INT_LINCOMB»
  SUBRING_GENERATED_MINIMAL := SessionLibrary.RingTheory.«SUBRING_GENERATED_MINIMAL»
  SUBRING_GENERATED_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBRING_GENERATED_SUBFIELD_GENERATED»
  SUBRING_SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_SUBRING_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUC_SUB1 := Session.SUC_SUB1
  basis_discriminant := SessionLibrary.RingDet.«basis_discriminant»
  divides := Session.divides
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  free_basis := SessionLibrary.RingDet.«free_basis»
  integral_element := SessionANT.Integral.«integral_element»
  num_CASES := Session.num_CASES
  num_WF := Session.num_WF
  num_coprime := Session.num_coprime
  number_field := SessionANT.Numfield.«number_field»
  o_THM := Session.o_THM
  poly_deriv := SessionLibrary.RingTheory.«poly_deriv»
  poly_eval := SessionLibrary.RingTheory.«poly_eval»
  ring_associates := SessionLibrary.RingTheory.«ring_associates»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_polynomial := SessionLibrary.RingTheory.«ring_polynomial»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_powerseries := SessionLibrary.RingTheory.«ring_powerseries»
  subring_of := SessionLibrary.RingTheory.«subring_of»

/-- What cyclotomic_integers.ml uses from Session. -/
def deps : HolANT.CyclotomicIntegers.CyclotomicIntegersDeps where
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
  INT_RING t := ExceptT.mk (Session.INT_RING t)
  NUMBER_TAC := Session.NUMBER_TAC
  NUM_RING := Session.NUM_RING
  core1 := core1
  core2 := core2
  core3 := core3

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in cyclotomic_integers.ml order. -/
initialize BCyclotomicIntegers01 : HolANT.CyclotomicIntegers.CyclotomicIntegers01 ←
  ioB "setupCyclotomicIntegers01" (HolANT.CyclotomicIntegers.setupCyclotomicIntegers01 deps).run
initialize BCyclotomicIntegers02 : HolANT.CyclotomicIntegers.CyclotomicIntegers02 ←
  ioB "setupCyclotomicIntegers02" (HolANT.CyclotomicIntegers.setupCyclotomicIntegers02 deps BCyclotomicIntegers01).run
initialize BCyclotomicIntegers03 : HolANT.CyclotomicIntegers.CyclotomicIntegers03 ←
  ioB "setupCyclotomicIntegers03" (HolANT.CyclotomicIntegers.setupCyclotomicIntegers03 deps BCyclotomicIntegers01 BCyclotomicIntegers02).run
initialize BCyclotomicIntegers04 : HolANT.CyclotomicIntegers.CyclotomicIntegers04 ←
  ioB "setupCyclotomicIntegers04" (HolANT.CyclotomicIntegers.setupCyclotomicIntegers04 deps BCyclotomicIntegers02 BCyclotomicIntegers03).run

-- CyclotomicIntegers01
def CYCLOTOMIC_POLY_INTEGER_ROOT : thm := BCyclotomicIntegers01.CYCLOTOMIC_POLY_INTEGER_ROOT
def SUBRING_GENERATED_ROOT_OF_UNITY_LINCOMB : thm := BCyclotomicIntegers01.SUBRING_GENERATED_ROOT_OF_UNITY_LINCOMB
def CYCLOTOMIC_POLY_DIVIDES_INTEGER_POLY : thm := BCyclotomicIntegers01.CYCLOTOMIC_POLY_DIVIDES_INTEGER_POLY
def POLY_RING_INTEGER_MOD_RING_DIVIDES_LIFT : thm := BCyclotomicIntegers01.POLY_RING_INTEGER_MOD_RING_DIVIDES_LIFT
def SUBRING_GENERATED_ROOT_OF_UNITY_REDUCED : thm := BCyclotomicIntegers01.SUBRING_GENERATED_ROOT_OF_UNITY_REDUCED
def SUBRING_GENERATED_ROOT_OF_UNITY_DENOMINATOR : thm := BCyclotomicIntegers01.SUBRING_GENERATED_ROOT_OF_UNITY_DENOMINATOR
def SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_COPRIME : thm := BCyclotomicIntegers01.SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_COPRIME
def SUBRING_GENERATED_ROOT_OF_UNITY_RADICAL : thm := BCyclotomicIntegers01.SUBRING_GENERATED_ROOT_OF_UNITY_RADICAL
def RING_ASSOCIATES_PRIME_POWER_ORDER : thm := BCyclotomicIntegers01.RING_ASSOCIATES_PRIME_POWER_ORDER
def SUBRING_GENERATED_POW_DECOMPOSE : thm := BCyclotomicIntegers01.SUBRING_GENERATED_POW_DECOMPOSE

-- CyclotomicIntegers02
def SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_DIVIDES : thm := BCyclotomicIntegers02.SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_DIVIDES
def SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL : thm := BCyclotomicIntegers02.SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL
def CYCLOTOMIC_FIELD_RING_OF_INTEGERS : thm := BCyclotomicIntegers02.CYCLOTOMIC_FIELD_RING_OF_INTEGERS
def CYCLOTOMIC_FIELD_INTEGRAL_BASIS : thm := BCyclotomicIntegers02.CYCLOTOMIC_FIELD_INTEGRAL_BASIS
def CYCLOTOMIC_FIELD_SUBFIELD_POW : thm := BCyclotomicIntegers02.CYCLOTOMIC_FIELD_SUBFIELD_POW
def CYCLOTOMIC_FIELD_NORM_SUB : thm := BCyclotomicIntegers02.CYCLOTOMIC_FIELD_NORM_SUB
def CYCLOTOMIC_FIELD_NORM_SUB_POW : thm := BCyclotomicIntegers02.CYCLOTOMIC_FIELD_NORM_SUB_POW
def CYCLOTOMIC_FIELD_DISCRIMINANT_DERIV : thm := BCyclotomicIntegers02.CYCLOTOMIC_FIELD_DISCRIMINANT_DERIV

-- CyclotomicIntegers03
def CYCLOTOMIC_FIELD_DISCRIMINANT_PRIME_POWER : thm := BCyclotomicIntegers03.CYCLOTOMIC_FIELD_DISCRIMINANT_PRIME_POWER
def CYCLOTOMIC_FIELD_PRODUCT_BASIS : thm := BCyclotomicIntegers03.CYCLOTOMIC_FIELD_PRODUCT_BASIS
def CYCLOTOMIC_FIELD_DISCRIMINANT_COMPOSITUM : thm := BCyclotomicIntegers03.CYCLOTOMIC_FIELD_DISCRIMINANT_COMPOSITUM

-- CyclotomicIntegers04
def CYCLOTOMIC_FIELD_DISCRIMINANT : thm := BCyclotomicIntegers04.CYCLOTOMIC_FIELD_DISCRIMINANT

/-- `needs "ANT/cyclotomic_integers.ml"`: already done by importing this module. -/
def ensureCyclotomicIntegers : IO Unit := pure ()

end SessionANT.CyclotomicIntegers
