/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/quadratic_split.ml                            . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/QuadraticSplit.lean

  The session half of the quadratic_split.ml translation: it supplies HolANT.QuadraticSplit's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/quadratic_split.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.QuadraticSplit
import SessionLibrary.Integer
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
import SessionANT.IdealArith
import SessionANT.Integral
import SessionANT.Dedekind
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.PrimeSplit
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.RelativeSplit
import SessionANT.RelativeDegree
import SessionANT.NfValuation
import SessionANT.Integrality
import SessionANT.DedekindKummer
import SessionANT.Quadratic

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.QuadraticSplit

/-- The core theorems quadratic_split.ml uses. -/
def core1 : HolANT.QuadraticSplit.CoreThms1 where
  ARITH_EQ := Session.ARITH_EQ
  COEFF_POLY_ADD := SessionLibrary.RingTheory.«COEFF_POLY_ADD»
  COEFF_POLY_CONST := SessionLibrary.RingTheory.«COEFF_POLY_CONST»
  COEFF_POLY_LMUL := SessionLibrary.RingTheory.«COEFF_POLY_LMUL»
  COEFF_POLY_SUB := SessionLibrary.RingTheory.«COEFF_POLY_SUB»
  COEFF_POLY_VAR := SessionLibrary.RingTheory.«COEFF_POLY_VAR»
  COEFF_POLY_VARPOW := SessionLibrary.RingTheory.«COEFF_POLY_VARPOW»
  COPRIME_PRIME_PRIME := SessionLibrary.Prime.«COPRIME_PRIME_PRIME»
  DEDEKIND_KUMMER_LINEAR_IDEAL := SessionANT.DedekindKummer.«DEDEKIND_KUMMER_LINEAR_IDEAL»
  DEDEKIND_KUMMER_Q := SessionANT.DedekindKummer.«DEDEKIND_KUMMER_Q»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  EXP_1 := Session.EXP_1
  EXTENSION := Session.EXTENSION
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_INTEGER_MOD_RING := SessionLibrary.RingTheory.«FIELD_INTEGER_MOD_RING»
  FIELD_MUL_RINV := SessionLibrary.RingTheory.«FIELD_MUL_RINV»
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_SING := Session.FINITE_SING
  FORALL_AND_THM := Session.FORALL_AND_THM
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  IDEAL_GENERATED_INC_GEN := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC_GEN»
  IDEAL_GENERATED_PAIR_EQ := SessionLibrary.RingTheory.«IDEAL_GENERATED_PAIR_EQ»
  IDEAL_GENERATED_SING := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING»
  IDEAL_POW_1 := SessionANT.IdealArith.«IDEAL_POW_1»
  IDEAL_POW_SUBSET_PRIME_IDEAL := SessionANT.IdealArith.«IDEAL_POW_SUBSET_PRIME_IDEAL»
  IDEAL_PRODUCT_INSERT := SessionANT.IdealArith.«IDEAL_PRODUCT_INSERT»
  IDEAL_PRODUCT_SING := SessionANT.IdealArith.«IDEAL_PRODUCT_SING»
  IDEAL_VALUATION_IDEAL_POW := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_POW»
  IDEAL_VALUATION_PRIME := SessionANT.Dedekind.«IDEAL_VALUATION_PRIME»
  IMP_CONJ := Session.IMP_CONJ
  INTEGER_MOD_RING_CHAR := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CHAR»
  INTEGER_MOD_RING_OF_INT := SessionLibrary.RingTheory.«INTEGER_MOD_RING_OF_INT»
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGRAL_DOMAIN_MUL_LCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_LCANCEL»
  INTEGRAL_ELEMENT_QUADRATIC := SessionANT.Quadratic.«INTEGRAL_ELEMENT_QUADRATIC»
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_ADD_LID := Session.INT_ADD_LID
  INT_CONG_REFL := SessionLibrary.Integer.«INT_CONG_REFL»
  INT_DIVIDES_ONE := SessionLibrary.Integer.«INT_DIVIDES_ONE»
  INT_DIVISION := Session.INT_DIVISION
  INT_DIV_MUL := Session.INT_DIV_MUL
  INT_MUL_LZERO := Session.INT_MUL_LZERO
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_POW_2 := Session.INT_POW_2
  INT_REM_EQ := Session.INT_REM_EQ
  INT_REM_EQ_0 := Session.INT_REM_EQ_0
  INT_REM_LT := Session.INT_REM_LT
  IN_DELETE := Session.IN_DELETE
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_INSERT := Session.IN_INSERT
  IN_INTEGER_MOD_RING_CARRIER := SessionLibrary.RingTheory.«IN_INTEGER_MOD_RING_CARRIER»
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_NEG := SessionLibrary.RingTheory.«IN_RING_IDEAL_NEG»
  IN_SING := Session.IN_SING
  IN_SUBRING_1 := SessionLibrary.RingTheory.«IN_SUBRING_1»
  IN_SUBRING_ADD := SessionLibrary.RingTheory.«IN_SUBRING_ADD»
  IN_SUBRING_INT := SessionLibrary.RingTheory.«IN_SUBRING_INT»
  IN_SUBRING_MUL := SessionLibrary.RingTheory.«IN_SUBRING_MUL»
  IN_SUBRING_NEG := SessionLibrary.RingTheory.«IN_SUBRING_NEG»
  IN_SUBRING_NUM := SessionLibrary.RingTheory.«IN_SUBRING_NUM»
  IN_SUBRING_SUB := SessionLibrary.RingTheory.«IN_SUBRING_SUB»
  IN_UNIV := Session.IN_UNIV
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_MULT2 := Session.LE_MULT2
  MONIC_X_MINUS_A := SessionLibrary.RingTheory.«MONIC_X_MINUS_A»
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_TRIVIAL_INTEGER_RING := SessionLibrary.RingTheory.«NOT_TRIVIAL_INTEGER_RING»
  NSUM_DELETE := Session.NSUM_DELETE
  NSUM_EQ_0_IFF := Session.NSUM_EQ_0_IFF
  NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q := SessionANT.PrimeSplit.«NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_PRIME_FACTORIZATION_Q := SessionANT.PrimeSplit.«NUMBER_FIELD_PRIME_FACTORIZATION_Q»
  NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q := SessionANT.PrimeSplit.«NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q»
  NUMBER_FIELD_PRIME_IDEAL_PROD_EQ := SessionANT.PrimeSplit.«NUMBER_FIELD_PRIME_IDEAL_PROD_EQ»
  NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q := SessionANT.PrimeSplit.«NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q»
  NUMBER_FIELD_RAMIFIED_DISCRIMINANT := SessionANT.Ramification.«NUMBER_FIELD_RAMIFIED_DISCRIMINANT»
  NUMBER_FIELD_RING_OF_NUM_EQ_0 := SessionANT.Numfield.«NUMBER_FIELD_RING_OF_NUM_EQ_0»
  ODD_EXISTS := Session.ODD_EXISTS
  POLY_COMPOSE_HOMOMORPHISM_CONST := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_CONST»
  POLY_COMPOSE_HOMOMORPHISM_VAR := SessionLibrary.RingTheory.«POLY_COMPOSE_HOMOMORPHISM_VAR»
  POLY_CONST := SessionLibrary.RingTheory.«POLY_CONST»
  POLY_DEG_2_IRREDUCIBLE := SessionLibrary.RingTheory.«POLY_DEG_2_IRREDUCIBLE»
  POLY_DEG_EQ_COEFF := SessionLibrary.RingTheory.«POLY_DEG_EQ_COEFF»
  POLY_DEG_X_MINUS_A := SessionLibrary.RingTheory.«POLY_DEG_X_MINUS_A»
/-- The core theorems quadratic_split.ml uses. -/
def core2 : HolANT.QuadraticSplit.CoreThms2 where
  POLY_EXTEND_CONST := SessionLibrary.RingTheory.«POLY_EXTEND_CONST»
  POLY_EXTEND_EVALUATE := SessionLibrary.RingTheory.«POLY_EXTEND_EVALUATE»
  POLY_EXTEND_VAR := SessionLibrary.RingTheory.«POLY_EXTEND_VAR»
  POLY_RING_CLAUSES := SessionLibrary.RingTheory.«POLY_RING_CLAUSES»
  POLY_VAR_UNIV := SessionLibrary.RingTheory.«POLY_VAR_UNIV»
  PRIME_2 := SessionLibrary.Prime.«PRIME_2»
  PRIME_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_SUBSET»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRIME_ODD := SessionLibrary.Prime.«PRIME_ODD»
  QUADRATIC_FIELD_INTEGRAL_BASIS := SessionANT.Quadratic.«QUADRATIC_FIELD_INTEGRAL_BASIS»
  RAMIFICATION_INDEX_PRIME := SessionANT.PrimeSplit.«RAMIFICATION_INDEX_PRIME»
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_I := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_I»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_NEG := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_NEG»
  RING_HOMOMORPHISM_POLY_CONST := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_CONST»
  RING_HOMOMORPHISM_POLY_EXTEND := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_EXTEND»
  RING_HOMOMORPHISM_POLY_RINGS := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_RINGS»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_SUB := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUB»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_IRREDUCIBLE_X_MINUS_A := SessionLibrary.RingTheory.«RING_IRREDUCIBLE_X_MINUS_A»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_NEG_0 := SessionLibrary.RingTheory.«RING_NEG_0»
  RING_NEG_EQ := SessionLibrary.RingTheory.«RING_NEG_EQ»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_CARRIER := SessionANT.Numfield.«RING_OF_INTEGERS_CARRIER»
  RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q := SessionANT.PrimeSplit.«RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_0 := SessionLibrary.RingTheory.«RING_OF_INT_0»
  RING_OF_INT_1 := SessionLibrary.RingTheory.«RING_OF_INT_1»
  RING_OF_INT_ADD := SessionLibrary.RingTheory.«RING_OF_INT_ADD»
  RING_OF_INT_EQ_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0»
  RING_OF_INT_IN_RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INT_IN_RING_OF_INTEGERS»
  RING_OF_INT_MUL := SessionLibrary.RingTheory.«RING_OF_INT_MUL»
  RING_OF_INT_NEG := SessionLibrary.RingTheory.«RING_OF_INT_NEG»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_INT_POW := SessionLibrary.RingTheory.«RING_OF_INT_POW»
  RING_OF_INT_SUB := SessionLibrary.RingTheory.«RING_OF_INT_SUB»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_1 := SessionLibrary.RingTheory.«RING_OF_NUM_1»
  RING_OF_NUM_ADD := SessionLibrary.RingTheory.«RING_OF_NUM_ADD»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_OF_NUM_MUL := SessionLibrary.RingTheory.«RING_OF_NUM_MUL»
  RING_POLYNOMIAL_IMP_POWERSERIES := SessionLibrary.RingTheory.«RING_POLYNOMIAL_IMP_POWERSERIES»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POWERSERIES_VAR := SessionLibrary.RingTheory.«RING_POWERSERIES_VAR»
  RING_POW_1 := SessionLibrary.RingTheory.«RING_POW_1»
  RING_POW_2 := SessionLibrary.RingTheory.«RING_POW_2»
  RING_PRODUCT_CLAUSES := SessionLibrary.RingTheory.«RING_PRODUCT_CLAUSES»
  RING_PRODUCT_SING := SessionLibrary.RingTheory.«RING_PRODUCT_SING»
  RING_SETADD := SessionLibrary.RingTheory.«RING_SETADD»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_LZERO := SessionLibrary.RingTheory.«RING_SUB_LZERO»
  RING_SUB_RZERO := SessionLibrary.RingTheory.«RING_SUB_RZERO»
  RING_SUM_CLAUSES := SessionLibrary.RingTheory.«RING_SUM_CLAUSES»
  RING_SUM_SING := SessionLibrary.RingTheory.«RING_SUM_SING»
  SING_SUBSET := Session.SING_SUBSET
  SUBRING_GENERATED_INC_GEN := SessionLibrary.RingTheory.«SUBRING_GENERATED_INC_GEN»
  SUBRING_GENERATED_MINIMAL := SessionLibrary.RingTheory.«SUBRING_GENERATED_MINIMAL»
  SUBRING_SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_SUBRING_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_REFL := Session.SUBSET_REFL
  TRIVIAL_RING_10 := SessionLibrary.RingTheory.«TRIVIAL_RING_10»
  free_basis := SessionLibrary.RingDet.«free_basis»
  int_congruent := Session.int_congruent
  int_divides := Session.int_divides
  monic := SessionLibrary.RingTheory.«monic»
  num_coprime := Session.num_coprime
  number_field := SessionANT.Numfield.«number_field»
  poly_eval := SessionLibrary.RingTheory.«poly_eval»
  ring_div := SessionLibrary.RingTheory.«ring_div»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_setadd := SessionLibrary.RingTheory.«ring_setadd»
  ring_sub := SessionLibrary.RingTheory.«ring_sub»

/-- What quadratic_split.ml uses from Session. -/
def deps : HolANT.QuadraticSplit.QuadraticSplitDeps where
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

/- The bundles, in quadratic_split.ml order. -/
initialize BQuadraticSplit01 : HolANT.QuadraticSplit.QuadraticSplit01 ←
  ioB "setupQuadraticSplit01" (HolANT.QuadraticSplit.setupQuadraticSplit01 deps).run
initialize BQuadraticSplit02 : HolANT.QuadraticSplit.QuadraticSplit02 ←
  ioB "setupQuadraticSplit02" (HolANT.QuadraticSplit.setupQuadraticSplit02 deps BQuadraticSplit01).run
initialize BQuadraticSplit03 : HolANT.QuadraticSplit.QuadraticSplit03 ←
  ioB "setupQuadraticSplit03" (HolANT.QuadraticSplit.setupQuadraticSplit03 deps BQuadraticSplit01).run

-- QuadraticSplit01
def QUADRATIC_POLY_IN_CARRIER : thm := BQuadraticSplit01.QUADRATIC_POLY_IN_CARRIER
def QUADRATIC_POLY_DEG : thm := BQuadraticSplit01.QUADRATIC_POLY_DEG
def QUADRATIC_POLY_EXTEND : thm := BQuadraticSplit01.QUADRATIC_POLY_EXTEND
def QUADRATIC_POLY_HOMOMORPHIC_IMAGE : thm := BQuadraticSplit01.QUADRATIC_POLY_HOMOMORPHIC_IMAGE
def QUADRATIC_POLY_FACTOR : thm := BQuadraticSplit01.QUADRATIC_POLY_FACTOR
def QUADRATIC_POLY_INTEGER_ROOT : thm := BQuadraticSplit01.QUADRATIC_POLY_INTEGER_ROOT
def QUADRATIC_DEDEKIND_KUMMER_SPLIT_PRIMES : thm := BQuadraticSplit01.QUADRATIC_DEDEKIND_KUMMER_SPLIT_PRIMES
def QUADRATIC_DEDEKIND_KUMMER_RAMIFIED_PRIME : thm := BQuadraticSplit01.QUADRATIC_DEDEKIND_KUMMER_RAMIFIED_PRIME
def QUADRATIC_DEDEKIND_KUMMER_SPLIT : thm := BQuadraticSplit01.QUADRATIC_DEDEKIND_KUMMER_SPLIT
def QUADRATIC_DEDEKIND_KUMMER_INERT : thm := BQuadraticSplit01.QUADRATIC_DEDEKIND_KUMMER_INERT
def QUADRATIC_FIELD_RING_OF_INTEGERS : thm := BQuadraticSplit01.QUADRATIC_FIELD_RING_OF_INTEGERS
def RING_OF_INTEGERS_SETADD_SUBRING_GENERATED : thm := BQuadraticSplit01.RING_OF_INTEGERS_SETADD_SUBRING_GENERATED
def RING_OF_INTEGERS_SETADD_SUBRING_GENERATED_LINEAR : thm := BQuadraticSplit01.RING_OF_INTEGERS_SETADD_SUBRING_GENERATED_LINEAR

-- QuadraticSplit02
def QUADRATIC_FIELD_SETADD_ODD : thm := BQuadraticSplit02.QUADRATIC_FIELD_SETADD_ODD
def QUADRATIC_FIELD_RAMIFIED_PRIME : thm := BQuadraticSplit02.QUADRATIC_FIELD_RAMIFIED_PRIME
def QUADRATIC_FIELD_RAMIFIED : thm := BQuadraticSplit02.QUADRATIC_FIELD_RAMIFIED
def QUADRATIC_FIELD_ODD_PRIME : thm := BQuadraticSplit02.QUADRATIC_FIELD_ODD_PRIME
def QUADRATIC_FIELD_PRIME_TWO : thm := BQuadraticSplit02.QUADRATIC_FIELD_PRIME_TWO
def QUADRATIC_FIELD_SPLIT_ODD_PRIME : thm := BQuadraticSplit02.QUADRATIC_FIELD_SPLIT_ODD_PRIME
def QUADRATIC_FIELD_RAMIFIED_ODD_PRIME : thm := BQuadraticSplit02.QUADRATIC_FIELD_RAMIFIED_ODD_PRIME
def QUADRATIC_FIELD_RAMIFIED_TWO : thm := BQuadraticSplit02.QUADRATIC_FIELD_RAMIFIED_TWO

-- QuadraticSplit03
def QUADRATIC_FIELD_SPLIT_TWO : thm := BQuadraticSplit03.QUADRATIC_FIELD_SPLIT_TWO

/-- `needs "ANT/quadratic_split.ml"`: already done by importing this module. -/
def ensureQuadraticSplit : IO Unit := pure ()

end SessionANT.QuadraticSplit
