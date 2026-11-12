/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/different_exponent.ml                         . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/DifferentExponent.lean

  The session half of the different_exponent.ml translation: it supplies HolANT.DifferentExponent's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/different_exponent.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.DifferentExponent
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
import SessionANT.IdealArith
import SessionANT.Algmisc
import SessionANT.Integral
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
import SessionANT.PrimeSplit
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.Classgroup
import SessionANT.RelativeSplit
import SessionANT.NfValuation
import SessionANT.Integrality
import SessionANT.Different
import SessionANT.RelativeDegree
import SessionANT.DifferentExtension

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.DifferentExponent

/-- The core theorems different_exponent.ml uses. -/
def core1 : HolANT.DifferentExponent.CoreThms1 where
  ADD_CLAUSES := Session.ADD_CLAUSES
  ADD_MULT_LT_MULT := SessionLibrary.RingDet.«ADD_MULT_LT_MULT»
  ALGEBRA_TRACE_0 := SessionLibrary.RingDet.«ALGEBRA_TRACE_0»
  ALGEBRA_TRACE_FINITE_FIELD_NONZERO := SessionANT.FiniteFieldTrace.«ALGEBRA_TRACE_FINITE_FIELD_NONZERO»
  ALGEBRA_TRACE_FREE_BASIS := SessionLibrary.RingDet.«ALGEBRA_TRACE_FREE_BASIS»
  ALGEBRA_TRACE_ISOMORPHIC_IMAGE := SessionANT.TraceForm.«ALGEBRA_TRACE_ISOMORPHIC_IMAGE»
  ALGEBRA_TRACE_NILPOTENT_INTEGER_MOD := SessionANT.Ramification.«ALGEBRA_TRACE_NILPOTENT_INTEGER_MOD»
  ALGEBRA_TRACE_NORM_IN_CARRIER := SessionLibrary.RingDet.«ALGEBRA_TRACE_NORM_IN_CARRIER»
  ALGEBRA_TRACE_PROD_RING := SessionANT.TraceForm.«ALGEBRA_TRACE_PROD_RING»
  ALGEBRA_TRACE_QUOTIENT_RING_INTEGER_MOD := SessionANT.Ramification.«ALGEBRA_TRACE_QUOTIENT_RING_INTEGER_MOD»
  AND_FORALL_THM := Session.AND_FORALL_THM
  ARITH_EQ := Session.ARITH_EQ
  BASIS_COORDINATES := SessionLibrary.RingDet.«BASIS_COORDINATES»
  BASIS_COORDINATES_UNIQUE := SessionLibrary.RingDet.«BASIS_COORDINATES_UNIQUE»
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  COMAXIMAL_IDEAL_POW := SessionANT.IdealArith.«COMAXIMAL_IDEAL_POW»
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DEDEKIND_IDEAL_FACTORIZATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_FACTORIZATION»
  DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT := SessionANT.Dedekind.«DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT»
  DEDEKIND_IDEAL_PROD_SUBSET_CANCEL := SessionANT.Dedekind.«DEDEKIND_IDEAL_PROD_SUBSET_CANCEL»
  DEDEKIND_IDEAL_SUBSET_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_POW_VALUATION»
  DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL := SessionANT.Dedekind.«DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL»
  DEDEKIND_PRIME_IDEAL_UNIFORMIZER := SessionANT.Dedekind.«DEDEKIND_PRIME_IDEAL_UNIFORMIZER»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DEDEKIND_UNIFORMIZER_CRITERION := SessionANT.DedekindValuation.«DEDEKIND_UNIFORMIZER_CRITERION»
  DIVIDES_0 := SessionLibrary.Prime.«DIVIDES_0»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  DIVISION := Session.DIVISION
  DIV_LT := Session.DIV_LT
  DIV_MULT_ADD := Session.DIV_MULT_ADD
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_IN_GSPEC := Session.EXISTS_IN_GSPEC
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXP_EQ_0 := Session.EXP_EQ_0
  EXTENSION := Session.EXTENSION
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_INTEGER_MOD_RING := SessionLibrary.RingTheory.«FIELD_INTEGER_MOD_RING»
  FIELD_QUOTIENT_RING := SessionLibrary.RingTheory.«FIELD_QUOTIENT_RING»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_INTEGER_MOD_RING := SessionLibrary.RingTheory.«FINITE_INTEGER_MOD_RING»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_QUOTIENT_RING_MONO := SessionANT.IdealNorm.«FINITE_QUOTIENT_RING_MONO»
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FORALL_AND_THM := Session.FORALL_AND_THM
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FREE_BASIS_EXISTS := SessionLibrary.FieldTheory.«FREE_BASIS_EXISTS»
  FREE_BASIS_HAS_SIZE := SessionLibrary.RingDet.«FREE_BASIS_HAS_SIZE»
  FREE_BASIS_QUOTIENT_RING_INTEGER_MOD := SessionANT.Ramification.«FREE_BASIS_QUOTIENT_RING_INTEGER_MOD»
  FUN_EQ_THM := Session.FUN_EQ_THM
  HAS_SIZE := Session.HAS_SIZE
  IDEAL_GENERATED_INC := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_NORM_FACTORIZATION := SessionANT.IdealNorm.«IDEAL_NORM_FACTORIZATION»
  IDEAL_POW_0 := SessionANT.IdealArith.«IDEAL_POW_0»
  IDEAL_POW_1 := SessionANT.IdealArith.«IDEAL_POW_1»
  IDEAL_POW_ANTIMONO := SessionANT.IdealArith.«IDEAL_POW_ANTIMONO»
  IDEAL_POW_SUC := SessionANT.IdealArith.«IDEAL_POW_SUC»
  IDEAL_PROD_COMAXIMAL := SessionANT.IdealArith.«IDEAL_PROD_COMAXIMAL»
  IDEAL_PROD_COMM := SessionANT.IdealArith.«IDEAL_PROD_COMM»
  IDEAL_PROD_MINIMAL := SessionANT.IdealArith.«IDEAL_PROD_MINIMAL»
  IDEAL_PROD_MONO := SessionANT.IdealArith.«IDEAL_PROD_MONO»
  IDEAL_VALUATION_EQ_0 := SessionANT.Dedekind.«IDEAL_VALUATION_EQ_0»
  INDEX_EXP := SessionLibrary.Prime.«INDEX_EXP»
  INDEX_NPRODUCT := SessionLibrary.Prime.«INDEX_NPRODUCT»
  INDEX_PRIME := SessionLibrary.Prime.«INDEX_PRIME»
  INTEGER_MOD_RING_CARRIER_REM := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CARRIER_REM»
  INTEGER_MOD_RING_CHAR := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CHAR»
  INTEGER_MOD_RING_CLAUSES := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CLAUSES»
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INT_ADD_LID := Session.INT_ADD_LID
  INT_REM_EQ_0 := Session.INT_REM_EQ_0
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_ADD := SessionLibrary.RingTheory.«IN_RING_IDEAL_ADD»
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_RING_IDEAL_NEG := SessionLibrary.RingTheory.«IN_RING_IDEAL_NEG»
  IN_RING_IDEAL_RMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_RMUL»
  IN_RING_IDEAL_SUB := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUB»
  IN_RING_IDEAL_SUB_SUM_RESTRICT := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUB_SUM_RESTRICT»
  IN_SING := Session.IN_SING
  IN_SUBRING_1 := SessionLibrary.RingTheory.«IN_SUBRING_1»
  IN_SUBRING_NUM := SessionLibrary.RingTheory.«IN_SUBRING_NUM»
  LE_0 := Session.LE_0
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  LE_REFL := Session.LE_REFL
  LT := Session.LT
  LT_IMP_LE := Session.LT_IMP_LE
  LT_MULT_LCANCEL := Session.LT_MULT_LCANCEL
  MAXIMAL_IDEAL_COMAXIMAL := SessionANT.IdealArith.«MAXIMAL_IDEAL_COMAXIMAL»
  MOD_LT := Session.MOD_LT
  MOD_LT_EQ := Session.MOD_LT_EQ
  MOD_MULT_ADD := Session.MOD_MULT_ADD
  MULT_CLAUSES := Session.MULT_CLAUSES
/-- The core theorems different_exponent.ml uses. -/
def core2 : HolANT.DifferentExponent.CoreThms2 where
  MULT_EQ_0 := Session.MULT_EQ_0
  MUL_MATRIX_IN_CARRIER := SessionLibrary.RingDet.«MUL_MATRIX_IN_CARRIER»
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NSUM_EQ := Session.NSUM_EQ
  NSUM_EQ_SUPERSET := Session.NSUM_EQ_SUPERSET
  NSUM_LE := Session.NSUM_LE
  NSUM_LT := Session.NSUM_LT
  NSUM_SUPERSET := Session.NSUM_SUPERSET
  NUMBER_FIELD_CODIFFERENT_DIV := SessionANT.Different.«NUMBER_FIELD_CODIFFERENT_DIV»
  NUMBER_FIELD_CODIFFERENT_DIV_NUM := SessionANT.Different.«NUMBER_FIELD_CODIFFERENT_DIV_NUM»
  NUMBER_FIELD_DIFFERENT_NONZERO := SessionANT.Different.«NUMBER_FIELD_DIFFERENT_NONZERO»
  NUMBER_FIELD_DIFFERENT_SUBSET_RAMIFICATION := SessionANT.DifferentExtension.«NUMBER_FIELD_DIFFERENT_SUBSET_RAMIFICATION»
  NUMBER_FIELD_IDEAL_NORM_DIFFERENT := SessionANT.Different.«NUMBER_FIELD_IDEAL_NORM_DIFFERENT»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q := SessionANT.PrimeSplit.«NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q»
  PAIR_EQ := Session.PAIR_EQ
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  QUOTIENT_RING_0 := SessionLibrary.RingTheory.«QUOTIENT_RING_0»
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
  QUOTIENT_RING_LINCOMB_LIFT := SessionLibrary.RingTheory.«QUOTIENT_RING_LINCOMB_LIFT»
  QUOTIENT_RING_MUL := SessionLibrary.RingTheory.«QUOTIENT_RING_MUL»
  RAMIFICATION_INDEX_PRIME := SessionANT.PrimeSplit.«RAMIFICATION_INDEX_PRIME»
  RAMIFICATION_INDEX_PRIME_SUBFIELD := SessionANT.RelativeSplit.«RAMIFICATION_INDEX_PRIME_SUBFIELD»
  RDIV_LT_EQ := Session.RDIV_LT_EQ
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD_RDISTRIB := SessionLibrary.RingTheory.«RING_ADD_RDISTRIB»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_CHAR_QUOTIENT_RING_DIVIDES := SessionLibrary.RingTheory.«RING_CHAR_QUOTIENT_RING_DIVIDES»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_COSET_EQ_IDEAL := SessionLibrary.RingTheory.«RING_COSET_EQ_IDEAL»
  RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING := SessionANT.Ramification.«RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING»
  RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IDEAL_QUOTIENT := SessionANT.IdealArith.«RING_IDEAL_IDEAL_QUOTIENT»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_IDEAL_NUMBER_FIELD_DIFFERENT := SessionANT.Different.«RING_IDEAL_NUMBER_FIELD_DIFFERENT»
  RING_ISOMORPHISM_QUOTIENT_RING_INTER := SessionANT.IdealArith.«RING_ISOMORPHISM_QUOTIENT_RING_INTER»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_IN_IDEAL_POW := SessionANT.IdealArith.«RING_MUL_IN_IDEAL_POW»
  RING_MUL_IN_IDEAL_PROD := SessionANT.IdealArith.«RING_MUL_IN_IDEAL_PROD»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_FREE := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE»
  RING_OF_INTEGERS_IDEAL_GENERATED_PRIME := SessionANT.PrimeSplit.«RING_OF_INTEGERS_IDEAL_GENERATED_PRIME»
  RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q := SessionANT.PrimeSplit.«RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q»
  RING_OF_INTEGERS_PRIME_IDEAL_ABOVE := SessionANT.PrimeSplit.«RING_OF_INTEGERS_PRIME_IDEAL_ABOVE»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_ADD := SessionLibrary.RingTheory.«RING_OF_INT_ADD»
  RING_OF_INT_CLAUSES := SessionLibrary.RingTheory.«RING_OF_INT_CLAUSES»
  RING_OF_INT_REM_CHAR_DIVIDES := SessionLibrary.RingTheory.«RING_OF_INT_REM_CHAR_DIVIDES»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_1 := SessionLibrary.RingTheory.«RING_POW_1»
  RING_POW_IN_IDEAL_POW := SessionANT.IdealArith.«RING_POW_IN_IDEAL_POW»
  RING_SPAN_SELF := SessionLibrary.FieldTheory.«RING_SPAN_SELF»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_LDISTRIB := SessionLibrary.RingTheory.«RING_SUB_LDISTRIB»
  RING_SUB_LZERO := SessionLibrary.RingTheory.«RING_SUB_LZERO»
  RING_SUB_RZERO := SessionLibrary.RingTheory.«RING_SUB_RZERO»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_0 := SessionLibrary.RingTheory.«RING_SUM_0»
  RING_SUM_ADD := SessionLibrary.RingTheory.«RING_SUM_ADD»
  RING_SUM_CLAUSES := SessionLibrary.RingTheory.«RING_SUM_CLAUSES»
  RING_SUM_CONST := SessionLibrary.RingTheory.«RING_SUM_CONST»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_LMUL := SessionLibrary.RingTheory.«RING_SUM_LMUL»
  RING_SUM_MOD_DIV := SessionLibrary.RingDet.«RING_SUM_MOD_DIV»
  RING_SUM_NUMSEG_DIV_SLICE := SessionLibrary.RingDet.«RING_SUM_NUMSEG_DIV_SLICE»
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  SUBSET_REFL := Session.SUBSET_REFL
  SUBSET_TRANS := Session.SUBSET_TRANS
  free_basis := SessionLibrary.RingDet.«free_basis»
  mul_matrix := SessionLibrary.RingDet.«mul_matrix»
  num_WF := Session.num_WF
  number_field := SessionANT.Numfield.«number_field»
  o_THM := Session.o_THM
  ring_setadd := SessionLibrary.RingTheory.«ring_setadd»
  ring_spanning := SessionLibrary.FieldTheory.«ring_spanning»

/-- What different_exponent.ml uses from Session. -/
def deps : HolANT.DifferentExponent.DifferentExponentDeps where
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

/- The bundles, in different_exponent.ml order. -/
initialize BDifferentExponent01 : HolANT.DifferentExponent.DifferentExponent01 ←
  ioB "setupDifferentExponent01" (HolANT.DifferentExponent.setupDifferentExponent01 deps).run
initialize BDifferentExponent02 : HolANT.DifferentExponent.DifferentExponent02 ←
  ioB "setupDifferentExponent02" (HolANT.DifferentExponent.setupDifferentExponent02 deps BDifferentExponent01).run

-- DifferentExponent01
def DEDEKIND_IDEAL_POW_LEVEL_SPAN : thm := BDifferentExponent01.DEDEKIND_IDEAL_POW_LEVEL_SPAN
def DEDEKIND_IDEAL_POW_LEVEL_COEFFS : thm := BDifferentExponent01.DEDEKIND_IDEAL_POW_LEVEL_COEFFS
def DEDEKIND_IDEAL_POW_LEVEL_INDEPENDENT : thm := BDifferentExponent01.DEDEKIND_IDEAL_POW_LEVEL_INDEPENDENT
def DEDEKIND_QUOTIENT_POW_FREE_BASIS : thm := BDifferentExponent01.DEDEKIND_QUOTIENT_POW_FREE_BASIS
def DEDEKIND_ALGEBRA_TRACE_QUOTIENT_POW : thm := BDifferentExponent01.DEDEKIND_ALGEBRA_TRACE_QUOTIENT_POW
def FREE_BASIS_QUOTIENT_RING_PRIME_EXISTS : thm := BDifferentExponent01.FREE_BASIS_QUOTIENT_RING_PRIME_EXISTS

-- DifferentExponent02
def ALGEBRA_TRACE_INTEGER_MOD_SPLIT : thm := BDifferentExponent02.ALGEBRA_TRACE_INTEGER_MOD_SPLIT
def ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL_POW_DIVIDES : thm := BDifferentExponent02.ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL_POW_DIVIDES
def ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL_POW : thm := BDifferentExponent02.ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL_POW
def NUMBER_FIELD_DIFFERENT_WILD : thm := BDifferentExponent02.NUMBER_FIELD_DIFFERENT_WILD
def NUMBER_FIELD_DIFFERENT_TAME : thm := BDifferentExponent02.NUMBER_FIELD_DIFFERENT_TAME
def NUMBER_FIELD_DIFFERENT_VALUATION_TAME_Q : thm := BDifferentExponent02.NUMBER_FIELD_DIFFERENT_VALUATION_TAME_Q
def NUMBER_FIELD_DIFFERENT_VALUATION_WILD_Q : thm := BDifferentExponent02.NUMBER_FIELD_DIFFERENT_VALUATION_WILD_Q
def NUMBER_FIELD_IDEAL_NORM_PRIME_EXPONENT : thm := BDifferentExponent02.NUMBER_FIELD_IDEAL_NORM_PRIME_EXPONENT
def NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT : thm := BDifferentExponent02.NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT
def NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT_TAME : thm := BDifferentExponent02.NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT_TAME
def NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT_GE : thm := BDifferentExponent02.NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT_GE

/-- `needs "ANT/different_exponent.ml"`: already done by importing this module. -/
def ensureDifferentExponent : IO Unit := pure ()

end SessionANT.DifferentExponent
