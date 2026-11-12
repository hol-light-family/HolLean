/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/split_primes.ml                               . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/SplitPrimes.lean

  The session half of the split_primes.ml translation: it supplies HolANT.SplitPrimes's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/split_primes.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.SplitPrimes
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
import SessionLibrary.Integer
import SessionLibrary.Isum
import SessionLibrary.Products
import SessionLibrary.Multiplicative
import SessionLibrary.Primitive
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
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
import SessionANT.DedekindKummer
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.SplittingTypes
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionANT.Decomposition
import SessionANT.NfDecomposition
import SessionANT.DecompositionField

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.SplitPrimes

/-- The core theorems split_primes.ml uses. -/
def core1 : HolANT.SplitPrimes.CoreThms1 where
  ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH := SessionLibrary.FieldTheory.«ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH»
  DECOMPOSITION_GROUP := SessionANT.Decomposition.«DECOMPOSITION_GROUP»
  DEDEKIND_IDEAL_FACTORIZATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_FACTORIZATION»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  EQ_IMP := Session.EQ_IMP
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EXISTS_IN_GSPEC := Session.EXISTS_IN_GSPEC
  EXTENSION := Session.EXTENSION
  EXTENSION_DEGREE_EQ_IMAGE := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_EQ_IMAGE»
  EXTENSION_DEGREE_SIMPLE := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_SIMPLE»
  FIELD_EXTENSION_FROM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_FROM_SUBFIELD_GENERATED»
  FIELD_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_RING_HOMOMORPHISM_MONOMORPHISM := SessionLibrary.RingTheory.«FIELD_RING_HOMOMORPHISM_MONOMORPHISM»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_EXTENSION_EQ_IMAGE := SessionLibrary.FieldTheory.«FINITE_EXTENSION_EQ_IMAGE»
  FINITE_EXTENSION_NORMAL_CLOSURE := SessionLibrary.FieldTheory.«FINITE_EXTENSION_NORMAL_CLOSURE»
  FINITE_GALOIS_GROUP := SessionLibrary.Galois.«FINITE_GALOIS_GROUP»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_IMAGE_INJ := Session.FINITE_IMAGE_INJ
  FINITE_IMP_ALGEBRAIC_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_ALGEBRAIC_EXTENSION»
  FINITE_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_FIELD_EXTENSION»
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNION := Session.FINITE_UNION
  FINITE_UNIONS := Session.FINITE_UNIONS
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FUN_EQ_THM := Session.FUN_EQ_THM
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  GALOIS_EXTENSION_EQ_CARD := SessionLibrary.Galois.«GALOIS_EXTENSION_EQ_CARD»
  GALOIS_EXTENSION_INTERMEDIATE := SessionLibrary.Galois.«GALOIS_EXTENSION_INTERMEDIATE»
  GALOIS_GROUP_EQ_IMAGE := SessionLibrary.Galois.«GALOIS_GROUP_EQ_IMAGE»
  GALOIS_GROUP_EQ_ON_GENERATORS := SessionLibrary.Galois.«GALOIS_GROUP_EQ_ON_GENERATORS»
  GALOIS_GROUP_I := SessionLibrary.Galois.«GALOIS_GROUP_I»
  GALOIS_GROUP_INVERSE := SessionLibrary.Galois.«GALOIS_GROUP_INVERSE»
  GALOIS_GROUP_PERMUTES := SessionLibrary.Galois.«GALOIS_GROUP_PERMUTES»
  GALOIS_GROUP_PRIME_IDEAL_IMAGE := SessionANT.Decomposition.«GALOIS_GROUP_PRIME_IDEAL_IMAGE»
  GALOIS_GROUP_RING_HOMOMORPHISM := SessionLibrary.Galois.«GALOIS_GROUP_RING_HOMOMORPHISM»
  GALOIS_GROUP_RING_OF_INTEGERS := SessionANT.NfDecomposition.«GALOIS_GROUP_RING_OF_INTEGERS»
  GROUP_ID := SessionLibrary.GroupTheory.«GROUP_ID»
  IDEAL_GENERATED_INC := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IMAGE_I := Session.IMAGE_I
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  INFINITE := Session.INFINITE
  INFINITE_DIFF_FINITE := Session.INFINITE_DIFF_FINITE
  INFINITE_IMAGE := Session.INFINITE_IMAGE
  INFINITE_NONEMPTY := Session.INFINITE_NONEMPTY
  INFINITE_SUPERSET := Session.INFINITE_SUPERSET
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGER_RING_DIVIDES := SessionLibrary.RingTheory.«INTEGER_RING_DIVIDES»
  INTEGRAL_DOMAIN_INTEGER_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_INTEGER_RING»
  INT_ABS := Session.INT_ABS
  INT_ABS_POS := Session.INT_ABS_POS
  INT_ABS_ZERO := Session.INT_ABS_ZERO
  INT_DIVIDES_LABS := Session.INT_DIVIDES_LABS
  INT_DIVIDES_LMUL := SessionLibrary.Integer.«INT_DIVIDES_LMUL»
  INT_DIVIDES_ONE := SessionLibrary.Integer.«INT_DIVIDES_ONE»
  INT_DIVIDES_REFL := SessionLibrary.Integer.«INT_DIVIDES_REFL»
  INT_DIVIDES_SUB := SessionLibrary.Integer.«INT_DIVIDES_SUB»
  INT_ENTIRE := Session.INT_ENTIRE
  INT_MUL_RID := Session.INT_MUL_RID
  INT_MUL_RNEG := Session.INT_MUL_RNEG
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_PRIME := SessionLibrary.Primitive.«INT_PRIME»
  INT_PRIME_1 := SessionLibrary.Integer.«INT_PRIME_1»
  INT_PRIME_ABS := SessionLibrary.Integer.«INT_PRIME_ABS»
  INT_PRIME_FACTOR := SessionLibrary.Integer.«INT_PRIME_FACTOR»
  INT_PRIME_NEG := SessionLibrary.Integer.«INT_PRIME_NEG»
  INT_SUB_RZERO := Session.INT_SUB_RZERO
  IN_DIFF := Session.IN_DIFF
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SING_EQ := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SING_EQ»
  IN_IMAGE := Session.IN_IMAGE
  IN_RING_IDEAL_SUB := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUB»
  IN_RING_POLYNOMIAL_CARRIER_COMPOSE := SessionLibrary.RingTheory.«IN_RING_POLYNOMIAL_CARRIER_COMPOSE»
  IN_SING := Session.IN_SING
  IN_UNION := Session.IN_UNION
  IN_UNIONS := Session.IN_UNIONS
  IN_UNIV := Session.IN_UNIV
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LT_NZ := Session.LT_NZ
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONIC_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«MONIC_HOMOMORPHIC_IMAGE»
  MONIC_POLY_EQ_ROOTS_PRODUCT := SessionLibrary.RingTheory.«MONIC_POLY_EQ_ROOTS_PRODUCT»
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_EQ_1 := Session.MULT_EQ_1
/-- The core theorems split_primes.ml uses. -/
def core2 : HolANT.SplitPrimes.CoreThms2 where
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NPRODUCT_DELETE := SessionLibrary.Products.«NPRODUCT_DELETE»
  NPRODUCT_POS_LT := SessionLibrary.Products.«NPRODUCT_POS_LT»
  NUMBER_FIELD_DEGREE_POS := SessionANT.Numfield.«NUMBER_FIELD_DEGREE_POS»
  NUMBER_FIELD_GALOIS_SPLITTING_TYPES := SessionANT.DecompositionField.«NUMBER_FIELD_GALOIS_SPLITTING_TYPES»
  NUMBER_FIELD_HOMOMORPHIC_PREIMAGE := SessionANT.RelativeSplit.«NUMBER_FIELD_HOMOMORPHIC_PREIMAGE»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT := SessionANT.Integrality.«NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT»
  NUMBER_FIELD_PRIME_IDEALS_ABOVE := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_IDEALS_ABOVE»
  NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q := SessionANT.PrimeSplit.«NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q»
  NUMBER_FIELD_PRIME_SUBFIELD := SessionANT.Numfield.«NUMBER_FIELD_PRIME_SUBFIELD»
  NUMBER_FIELD_RAMIFICATION_INDEX_TOWER_Q := SessionANT.RelativeSplit.«NUMBER_FIELD_RAMIFICATION_INDEX_TOWER_Q»
  NUMBER_FIELD_RESIDUE_DEGREE_TOWER_Q := SessionANT.RelativeSplit.«NUMBER_FIELD_RESIDUE_DEGREE_TOWER_Q»
  NUMBER_FIELD_TOWER_LAW := SessionANT.RelativeSplit.«NUMBER_FIELD_TOWER_LAW»
  PERFECT_FIELD_CHAR_0 := SessionLibrary.FieldTheory.«PERFECT_FIELD_CHAR_0»
  PERFECT_FIELD_IMP_SEPARABLE_EXTENSION := SessionLibrary.FieldTheory.«PERFECT_FIELD_IMP_SEPARABLE_EXTENSION»
  PERMUTES_INVERSES := SessionLibrary.Permutations.«PERMUTES_INVERSES»
  POLY_CONST := SessionLibrary.RingTheory.«POLY_CONST»
  POLY_DEG_CONST := SessionLibrary.RingTheory.«POLY_DEG_CONST»
  POLY_EVALUATE_SUB_IN_IDEAL := SessionLibrary.RingTheory.«POLY_EVALUATE_SUB_IN_IDEAL»
  POLY_EVAL_CONST := SessionLibrary.RingTheory.«POLY_EVAL_CONST»
  POLY_EVAL_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_EVAL_HOMOMORPHIC_IMAGE»
  POLY_EVAL_RING_PRODUCT := SessionLibrary.RingTheory.«POLY_EVAL_RING_PRODUCT»
  POLY_EVAL_SUB := SessionLibrary.RingTheory.«POLY_EVAL_SUB»
  POLY_EVAL_VAR := SessionLibrary.RingTheory.«POLY_EVAL_VAR»
  POLY_EXTEND_EVALUATE := SessionLibrary.RingTheory.«POLY_EXTEND_EVALUATE»
  POLY_EXTEND_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«POLY_EXTEND_HOMOMORPHIC_IMAGE»
  POLY_RING_CLAUSES := SessionLibrary.RingTheory.«POLY_RING_CLAUSES»
  POLY_ROOT_BOUND := SessionLibrary.RingTheory.«POLY_ROOT_BOUND»
  POLY_X_MINUS_A_IN_CARRIER := SessionLibrary.RingTheory.«POLY_X_MINUS_A_IN_CARRIER»
  PRIMES_INFINITE := SessionLibrary.Prime.«PRIMES_INFINITE»
  PRIME_0 := SessionLibrary.Prime.«PRIME_0»
  PRIME_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_SUBSET»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRIME_SUBFIELD_MONOMORPHIC_IMAGE := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_MONOMORPHIC_IMAGE»
  PRIME_SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_SUBFIELD_GENERATED»
  PRIME_SUBFIELD_TOWER_LAW := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_TOWER_LAW»
  RING_CARRIER_SUBFIELD_GENERATED_SUBSET := SessionLibrary.FieldTheory.«RING_CARRIER_SUBFIELD_GENERATED_SUBSET»
  RING_CHAR_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_CHAR_SUBFIELD_GENERATED»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_INTO_SUBRING := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTO_SUBRING»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_HOMOMORPHISM_RING_OF_INTEGERS»
  RING_HOMOMORPHISM_RING_OF_NUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_NUM»
  RING_HOMOMORPHISM_SUB := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUB»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL := SessionANT.DedekindKummer.«RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL»
  RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL := SessionANT.RelativeSplit.«RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_IN_PRIME_IDEAL := SessionANT.PrimeSplit.«RING_OF_INT_IN_PRIME_IDEAL»
  RING_OF_INT_IN_RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INT_IN_RING_OF_INTEGERS»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_OF_NUM_IN_PRIME_IDEAL := SessionANT.PrimeSplit.«RING_OF_NUM_IN_PRIME_IDEAL»
  RING_POLYNOMIAL := SessionLibrary.RingTheory.«RING_POLYNOMIAL»
  RING_POLYNOMIAL_CONST := SessionLibrary.RingTheory.«RING_POLYNOMIAL_CONST»
  RING_POLYNOMIAL_VAR := SessionLibrary.RingTheory.«RING_POLYNOMIAL_VAR»
  RING_PRODUCT_EQ := SessionLibrary.RingTheory.«RING_PRODUCT_EQ»
  RING_PRODUCT_IN_PRIME_IDEAL := SessionLibrary.RingTheory.«RING_PRODUCT_IN_PRIME_IDEAL»
  RING_PRODUCT_SUBRING_GENERATED_GEN := SessionLibrary.RingTheory.«RING_PRODUCT_SUBRING_GENERATED_GEN»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  SIMPLE_IMAGE := Session.SIMPLE_IMAGE
  SING_SUBSET := Session.SING_SUBSET
  SPLITTING_TYPES_INTEGER_RING := SessionANT.SplittingTypes.«SPLITTING_TYPES_INTEGER_RING»
  SPLITTING_TYPES_PRIME_SUBFIELD := SessionANT.SplittingTypes.«SPLITTING_TYPES_PRIME_SUBFIELD»
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_EQ := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_EQ»
  SUBRING_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBRING_GENERATED_BY_SUBFIELD_GENERATED»
  SUBRING_SUBSET_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBRING_SUBSET_SUBFIELD_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  algebraic_extension := SessionLibrary.FieldTheory.«algebraic_extension»
  divides := Session.divides
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  finite_extension := SessionLibrary.FieldTheory.«finite_extension»
  galois_extension := SessionLibrary.Galois.«galois_extension»
  int_divides := Session.int_divides
  num_INFINITE := Session.num_INFINITE
  num_divides := Session.num_divides
  number_field := SessionANT.Numfield.«number_field»
  o_THM := Session.o_THM
  poly_eval := SessionLibrary.RingTheory.«poly_eval»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_sub := SessionLibrary.RingTheory.«ring_sub»
  totally_split := SessionANT.SplittingTypes.«totally_split»

/-- What split_primes.ml uses from Session. -/
def deps : HolANT.SplitPrimes.SplitPrimesDeps where
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
  SELECT_CONV t := pure (Session.SELECT_CONV t)
  core1 := core1
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in split_primes.ml order. -/
initialize BSplitPrimes01 : HolANT.SplitPrimes.SplitPrimes01 ←
  ioB "setupSplitPrimes01" (HolANT.SplitPrimes.setupSplitPrimes01 deps).run
initialize BSplitPrimes02 : HolANT.SplitPrimes.SplitPrimes02 ←
  ioB "setupSplitPrimes02" (HolANT.SplitPrimes.setupSplitPrimes02 deps BSplitPrimes01).run

-- SplitPrimes01
def INTEGER_POLY_CONGRUENCE : thm := BSplitPrimes01.INTEGER_POLY_CONGRUENCE
def INTEGER_POLY_FIBRE_FINITE : thm := BSplitPrimes01.INTEGER_POLY_FIBRE_FINITE
def INTEGER_POLY_PRIME_DIVISORS_INFINITE : thm := BSplitPrimes01.INTEGER_POLY_PRIME_DIVISORS_INFINITE
def NUMBER_FIELD_GALOIS_CONJUGATES_POLY : thm := BSplitPrimes01.NUMBER_FIELD_GALOIS_CONJUGATES_POLY
def NUMBER_FIELD_GALOIS_RATIONAL_TOTALLY_SPLIT : thm := BSplitPrimes01.NUMBER_FIELD_GALOIS_RATIONAL_TOTALLY_SPLIT
def NUMBER_FIELD_RATIONAL_PRIMES_CONTAINING_FINITE : thm := BSplitPrimes01.NUMBER_FIELD_RATIONAL_PRIMES_CONTAINING_FINITE
def NUMBER_FIELD_GALOIS_TOTALLY_SPLIT_INFINITE : thm := BSplitPrimes01.NUMBER_FIELD_GALOIS_TOTALLY_SPLIT_INFINITE

-- SplitPrimes02
def NUMBER_FIELD_GALOIS_CLOSURE_Q : thm := BSplitPrimes02.NUMBER_FIELD_GALOIS_CLOSURE_Q
def NUMBER_FIELD_GALOIS_CLOSURE : thm := BSplitPrimes02.NUMBER_FIELD_GALOIS_CLOSURE
def NUMBER_FIELD_TOTALLY_SPLIT_HOMOMORPHIC_PREIMAGE : thm := BSplitPrimes02.NUMBER_FIELD_TOTALLY_SPLIT_HOMOMORPHIC_PREIMAGE
def NUMBER_FIELD_TOTALLY_SPLIT_INFINITE_Q : thm := BSplitPrimes02.NUMBER_FIELD_TOTALLY_SPLIT_INFINITE_Q
def NUMBER_FIELD_TOTALLY_SPLIT_INFINITE : thm := BSplitPrimes02.NUMBER_FIELD_TOTALLY_SPLIT_INFINITE
def NUMBER_FIELD_DEGREE_ONE_PRIMES_INFINITE : thm := BSplitPrimes02.NUMBER_FIELD_DEGREE_ONE_PRIMES_INFINITE

/-- `needs "ANT/split_primes.ml"`: already done by importing this module. -/
def ensureSplitPrimes : IO Unit := pure ()

end SessionANT.SplitPrimes
