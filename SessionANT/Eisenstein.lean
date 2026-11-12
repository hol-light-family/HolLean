/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/eisenstein.ml                                 . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/Eisenstein.lean

  The session half of the eisenstein.ml translation: it supplies HolANT.Eisenstein's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/eisenstein.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.Eisenstein
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionLibrary.Matroids
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionLibrary.FieldTheory
import SessionANT.Integral
import SessionANT.IdealArith
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
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.RelativeDegree
import SessionANT.NfValuation
import SessionANT.Integrality
import SessionANT.DedekindKummer

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.Eisenstein

/-- The core theorems eisenstein.ml uses. -/
def core1 : HolANT.Eisenstein.CoreThms1 where
  ADD1 := Session.ADD1
  COEFF_ABOVE_DEG := SessionLibrary.RingTheory.«COEFF_ABOVE_DEG»
  COEFF_COMPOSE := SessionLibrary.RingTheory.«COEFF_COMPOSE»
  COEFF_POLY_VARPOW := SessionLibrary.RingTheory.«COEFF_POLY_VARPOW»
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DEDEKIND_IDEAL_SUBSET_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_POW_VALUATION»
  DEDEKIND_IMP_INTEGRAL_DOMAIN := SessionANT.Dedekind.«DEDEKIND_IMP_INTEGRAL_DOMAIN»
  DEDEKIND_IN_IDEAL_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IN_IDEAL_POW_VALUATION»
  DEDEKIND_KUMMER_Q := SessionANT.DedekindKummer.«DEDEKIND_KUMMER_Q»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EXTENSION := Session.EXTENSION
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_INTEGER_MOD_RING := SessionLibrary.RingTheory.«FIELD_INTEGER_MOD_RING»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_SING := Session.FINITE_SING
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FUN_EQ_COEFF := SessionLibrary.RingTheory.«FUN_EQ_COEFF»
  FUN_EQ_THM := Session.FUN_EQ_THM
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_FUNSPACE := Session.HAS_SIZE_FUNSPACE
  HAS_SIZE_IMAGE_INJ := Session.HAS_SIZE_IMAGE_INJ
  HAS_SIZE_NUMSEG_LT := Session.HAS_SIZE_NUMSEG_LT
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_POW_1 := SessionANT.IdealArith.«IDEAL_POW_1»
  IDEAL_POW_ANTIMONO := SessionANT.IdealArith.«IDEAL_POW_ANTIMONO»
  IDEAL_POW_SUC := SessionANT.IdealArith.«IDEAL_POW_SUC»
  IDEAL_PRODUCT_SING := SessionANT.IdealArith.«IDEAL_PRODUCT_SING»
  IDEAL_VALUATION_EQ_0 := SessionANT.Dedekind.«IDEAL_VALUATION_EQ_0»
  IDEAL_VALUATION_PRINCIPAL_MUL := SessionANT.Dedekind.«IDEAL_VALUATION_PRINCIPAL_MUL»
  IDEAL_VALUATION_PRINCIPAL_POW := SessionANT.Dedekind.«IDEAL_VALUATION_PRINCIPAL_POW»
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  INTEGER_MOD_RING_CHAR := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CHAR»
  INTEGER_MOD_RING_CLAUSES := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CLAUSES»
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_POW_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_POW_EQ_0»
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_DIVIDES_LE := Session.INT_DIVIDES_LE
  INT_ENTIRE := Session.INT_ENTIRE
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_POS := Session.INT_POS
  INT_POW_2 := Session.INT_POW_2
  INT_REM_EQ_SELF := Session.INT_REM_EQ_SELF
  IN_DELETE := Session.IN_DELETE
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_IDEAL_GENERATED_SING := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SING»
  IN_IMAGE := Session.IN_IMAGE
  IN_RING_IDEAL_ADD := SessionLibrary.RingTheory.«IN_RING_IDEAL_ADD»
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_RING_IDEAL_NEG := SessionLibrary.RingTheory.«IN_RING_IDEAL_NEG»
  IN_RING_IDEAL_RMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_RMUL»
  IN_RING_IDEAL_SUB := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUB»
  IN_RING_IDEAL_SUM := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUM»
  IN_SING := Session.IN_SING
  IN_SUBRING_MUL := SessionLibrary.RingTheory.«IN_SUBRING_MUL»
  IN_SUBRING_POW := SessionLibrary.RingTheory.«IN_SUBRING_POW»
  IN_SUBRING_SUM := SessionLibrary.RingTheory.«IN_SUBRING_SUM»
  IN_UNIV := Session.IN_UNIV
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_ANTISYM := Session.LE_ANTISYM
  LE_REFL := Session.LE_REFL
  LT := Session.LT
  LT_NZ := Session.LT_NZ
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONIC_POLY_VAR := SessionLibrary.RingTheory.«MONIC_POLY_VAR»
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_CLAUSES := Session.MULT_CLAUSES
  NOT_IMP := Session.NOT_IMP
  NOT_LT := Session.NOT_LT
  NUMBER_FIELD_DEGREE_POS := SessionANT.Numfield.«NUMBER_FIELD_DEGREE_POS»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q := SessionANT.PrimeSplit.«NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q»
  NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q := SessionANT.PrimeSplit.«NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q»
/-- The core theorems eisenstein.ml uses. -/
def core2 : HolANT.Eisenstein.CoreThms2 where
  NUM_OF_INT_OF_NUM := Session.NUM_OF_INT_OF_NUM
  POLY_DEG_VAR := SessionLibrary.RingTheory.«POLY_DEG_VAR»
  POLY_EXTEND_MONIC_UNIVARIATE := SessionLibrary.RingTheory.«POLY_EXTEND_MONIC_UNIVARIATE»
  POLY_EXTEND_VAR := SessionLibrary.RingTheory.«POLY_EXTEND_VAR»
  POLY_RING_CLAUSES := SessionLibrary.RingTheory.«POLY_RING_CLAUSES»
  PRIME_GE_2 := SessionLibrary.Prime.«PRIME_GE_2»
  PRIME_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_SUBSET»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
  RAMIFICATION_INDEX_INTEGER_RING := SessionANT.PrimeSplit.«RAMIFICATION_INDEX_INTEGER_RING»
  RAMIFICATION_INDEX_PRIME := SessionANT.PrimeSplit.«RAMIFICATION_INDEX_PRIME»
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_IRREDUCIBLE_POLY_VAR := SessionLibrary.RingTheory.«RING_IRREDUCIBLE_POLY_VAR»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_IN_IDEAL_PROD := SessionANT.IdealArith.«RING_MUL_IN_IDEAL_PROD»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_CARRIER := SessionANT.Numfield.«RING_OF_INTEGERS_CARRIER»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_IDEAL_NORM_INTEGER := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_IDEAL_NORM_INTEGER»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_0 := SessionLibrary.RingTheory.«RING_OF_INT_0»
  RING_OF_INT_1 := SessionLibrary.RingTheory.«RING_OF_INT_1»
  RING_OF_INT_EQ_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0»
  RING_OF_INT_EQ_0_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0_CHAR_0»
  RING_OF_INT_IN_PRIME_IDEAL := SessionANT.PrimeSplit.«RING_OF_INT_IN_PRIME_IDEAL»
  RING_OF_INT_IN_RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INT_IN_RING_OF_INTEGERS»
  RING_OF_INT_MUL := SessionLibrary.RingTheory.«RING_OF_INT_MUL»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_INT_SUB := SessionLibrary.RingTheory.«RING_OF_INT_SUB»
  RING_OF_NUM_IN_PRIME_IDEAL := SessionANT.PrimeSplit.«RING_OF_NUM_IN_PRIME_IDEAL»
  RING_POLYNOMIAL := SessionLibrary.RingTheory.«RING_POLYNOMIAL»
  RING_POLYNOMIAL_VAR := SessionLibrary.RingTheory.«RING_POLYNOMIAL_VAR»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_ADD := SessionLibrary.RingTheory.«RING_POW_ADD»
  RING_POW_IN_PRIME_IDEAL := SessionLibrary.RingTheory.«RING_POW_IN_PRIME_IDEAL»
  RING_POW_ZERO := SessionLibrary.RingTheory.«RING_POW_ZERO»
  RING_PRODUCT_SING := SessionLibrary.RingTheory.«RING_PRODUCT_SING»
  RING_SUB_RDISTRIB := SessionLibrary.RingTheory.«RING_SUB_RDISTRIB»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_CLAUSES := SessionLibrary.RingTheory.«RING_SUM_CLAUSES»
  RING_SUM_DELETE := SessionLibrary.RingTheory.«RING_SUM_DELETE»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_EQ_0 := SessionLibrary.RingTheory.«RING_SUM_EQ_0»
  RING_SUM_LMUL := SessionLibrary.RingTheory.«RING_SUM_LMUL»
  RING_SUM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_SUM_RING_OF_INTEGERS»
  RING_SUM_SUB := SessionLibrary.RingTheory.«RING_SUM_SUB»
  SING_SUBSET := Session.SING_SUBSET
  SUBRING_GENERATED_INDEX_COPRIME := SessionANT.DedekindKummer.«SUBRING_GENERATED_INDEX_COPRIME»
  SUBRING_GENERATED_INT_LINCOMB := SessionANT.DedekindKummer.«SUBRING_GENERATED_INT_LINCOMB»
  SUBSET := Session.SUBSET
  SUC_SUB1 := Session.SUC_SUB1
  SURJECTIVE_IFF_INJECTIVE_GEN := Session.SURJECTIVE_IFF_INJECTIVE_GEN
  TRIVIAL_RING_10 := SessionLibrary.RingTheory.«TRIVIAL_RING_10»
  ideal_norm := SessionANT.IdealNorm.«ideal_norm»
  int_divides := Session.int_divides
  integral_element := SessionANT.Integral.«integral_element»
  monic := SessionLibrary.RingTheory.«monic»
  num_WOP := Session.num_WOP
  number_field := SessionANT.Numfield.«number_field»
  poly_var := SessionLibrary.RingTheory.«poly_var»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_setadd := SessionLibrary.RingTheory.«ring_setadd»

/-- What eisenstein.ml uses from Session. -/
def deps : HolANT.Eisenstein.EisensteinDeps where
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

/- The bundles, in eisenstein.ml order. -/
initialize BEisenstein01 : HolANT.Eisenstein.Eisenstein01 ←
  ioB "setupEisenstein01" (HolANT.Eisenstein.setupEisenstein01 deps).run
initialize BEisenstein02 : HolANT.Eisenstein.Eisenstein02 ←
  ioB "setupEisenstein02" (HolANT.Eisenstein.setupEisenstein02 deps BEisenstein01).run

-- Eisenstein01
def NUMBER_FIELD_EISENSTEIN_VALUATION : thm := BEisenstein01.NUMBER_FIELD_EISENSTEIN_VALUATION
def NUMBER_FIELD_EISENSTEIN_POW : thm := BEisenstein01.NUMBER_FIELD_EISENSTEIN_POW
def IDEAL_VALUATION_RING_OF_INT_COPRIME : thm := BEisenstein01.IDEAL_VALUATION_RING_OF_INT_COPRIME

-- Eisenstein02
def NUMBER_FIELD_EISENSTEIN_INDEPENDENT : thm := BEisenstein02.NUMBER_FIELD_EISENSTEIN_INDEPENDENT
def NUMBER_FIELD_EISENSTEIN_INDEX_COPRIME : thm := BEisenstein02.NUMBER_FIELD_EISENSTEIN_INDEX_COPRIME
def NUMBER_FIELD_EISENSTEIN : thm := BEisenstein02.NUMBER_FIELD_EISENSTEIN
def NUMBER_FIELD_EISENSTEIN_INDEX : thm := BEisenstein02.NUMBER_FIELD_EISENSTEIN_INDEX

/-- `needs "ANT/eisenstein.ml"`: already done by importing this module. -/
def ensureEisenstein : IO Unit := pure ()

end SessionANT.Eisenstein
