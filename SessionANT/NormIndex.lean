/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/norm_index.ml                                 . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/NormIndex.lean

  The session half of the norm_index.ml translation: it supplies HolANT.NormIndex's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/norm_index.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.NormIndex
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
import SessionLibrary.Isum
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.IdealArith
import SessionANT.Integral
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.RingOfIntegers

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.NormIndex

/-- The core theorems norm_index.ml uses. -/
def core1 : HolANT.NormIndex.CoreThms1 where
  ALGEBRA_NORM_FREE_BASIS := SessionLibrary.RingDet.«ALGEBRA_NORM_FREE_BASIS»
  ALGEBRA_TRACE_FREE_BASIS := SessionLibrary.RingDet.«ALGEBRA_TRACE_FREE_BASIS»
  BASIS_COORDINATES := SessionLibrary.RingDet.«BASIS_COORDINATES»
  BASIS_COORDINATES_EXPAND := SessionLibrary.RingDet.«BASIS_COORDINATES_EXPAND»
  BASIS_COORDINATES_LINCOMB := SessionLibrary.RingDet.«BASIS_COORDINATES_LINCOMB»
  BASIS_COORDINATES_MUL := SessionLibrary.RingDet.«BASIS_COORDINATES_MUL»
  BASIS_COORDINATES_UNIQUE := SessionLibrary.RingDet.«BASIS_COORDINATES_UNIQUE»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  EQ_SYM_EQ := Session.EQ_SYM_EQ
  EQ_TRANS := Session.EQ_TRANS
  EXTENSION := Session.EXTENSION
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FREE_BASIS_IN_CARRIER := SessionLibrary.RingDet.«FREE_BASIS_IN_CARRIER»
  FREE_BASIS_QUOTIENT_RING_HAS_SIZE := SessionANT.RingOfIntegers.«FREE_BASIS_QUOTIENT_RING_HAS_SIZE»
  FUN_EQ_THM := Session.FUN_EQ_THM
  HAS_SIZE := Session.HAS_SIZE
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_GENERATED_SING_ALT := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING_ALT»
  IDEAL_GENERATED_SUBSET := SessionLibrary.RingTheory.«IDEAL_GENERATED_SUBSET»
  IDEAL_NORM_MUL := SessionANT.IdealNorm.«IDEAL_NORM_MUL»
  IDEAL_NORM_PRIME_IMP_MAXIMAL := SessionANT.IdealNorm.«IDEAL_NORM_PRIME_IMP_MAXIMAL»
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGER_RING_SUM := SessionLibrary.RingTheory.«INTEGER_RING_SUM»
  INT_ABS_POS := Session.INT_ABS_POS
  INT_COSETS_MATRIX_IMAGE := SessionANT.Zlattice.«INT_COSETS_MATRIX_IMAGE»
  INT_NEG_EQ_0 := Session.INT_NEG_EQ_0
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_UNIV := Session.IN_UNIV
  ISUM_EQ := SessionLibrary.Isum.«ISUM_EQ»
  I_THM := Session.I_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  MAXIMAL_IMP_PRIME_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PRIME_IDEAL»
  NUMBER_FIELD_NORM_EQ_0 := SessionANT.Numfield.«NUMBER_FIELD_NORM_EQ_0»
  PRIME_0 := SessionLibrary.Prime.«PRIME_0»
  PRIME_IDEAL_SING := SessionLibrary.RingTheory.«PRIME_IDEAL_SING»
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_DET_EQ := SessionLibrary.RingDet.«RING_DET_EQ»
  RING_DET_HOMOMORPHISM := SessionLibrary.RingDet.«RING_DET_HOMOMORPHISM»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_HOMOMORPHISM_SUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_FREE := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE»
  RING_OF_INTEGERS_FREE_BASIS_FIELD := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE_BASIS_FIELD»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_0 := SessionLibrary.RingTheory.«RING_OF_INT_0»
  RING_OF_INT_EQ_0_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0_CHAR_0»
  RING_OF_INT_EQ_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_CHAR_0»
  RING_OF_INT_IN_RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INT_IN_RING_OF_INTEGERS»
  RING_OF_INT_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_IN_SUBFIELD_GENERATED»
  RING_OF_INT_NEG := SessionLibrary.RingTheory.«RING_OF_INT_NEG»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_INT_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_SUBFIELD_GENERATED»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_SUM_RING_OF_INTEGERS»
  SUBSET := Session.SUBSET
  ideal_norm := SessionANT.IdealNorm.«ideal_norm»
  int_matrix_image := SessionANT.Zlattice.«int_matrix_image»
  mul_matrix := SessionLibrary.RingDet.«mul_matrix»
  number_field := SessionANT.Numfield.«number_field»
  o_THM := Session.o_THM

/-- What norm_index.ml uses from Session. -/
def deps : HolANT.NormIndex.NormIndexDeps where
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

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in norm_index.ml order. -/
initialize BNormIndex : HolANT.NormIndex.NormIndex ←
  ioB "setupNormIndex" (HolANT.NormIndex.setupNormIndex deps).run

-- NormIndex
def FREE_BASIS_IDEAL_NORM_COORD_MUL : thm := BNormIndex.FREE_BASIS_IDEAL_NORM_COORD_MUL
def FREE_BASIS_IDEAL_NORM_IMAGE : thm := BNormIndex.FREE_BASIS_IDEAL_NORM_IMAGE
def FREE_BASIS_IDEAL_NORM_PRINCIPAL : thm := BNormIndex.FREE_BASIS_IDEAL_NORM_PRINCIPAL
def MUL_MATRIX_RING_OF_INTEGERS : thm := BNormIndex.MUL_MATRIX_RING_OF_INTEGERS
def NUMBER_FIELD_NORM_INTEGRAL_BASIS : thm := BNormIndex.NUMBER_FIELD_NORM_INTEGRAL_BASIS
def NUMBER_FIELD_TRACE_INTEGRAL_BASIS : thm := BNormIndex.NUMBER_FIELD_TRACE_INTEGRAL_BASIS
def NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q : thm := BNormIndex.NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q
def NUMBER_FIELD_IDEAL_NORM_MUL_Q : thm := BNormIndex.NUMBER_FIELD_IDEAL_NORM_MUL_Q
def NUMBER_FIELD_IDEAL_NORM_PRIME_IMP_PRIME : thm := BNormIndex.NUMBER_FIELD_IDEAL_NORM_PRIME_IMP_PRIME
def NUMBER_FIELD_NORM_PRIME_IMP_RING_PRIME : thm := BNormIndex.NUMBER_FIELD_NORM_PRIME_IMP_RING_PRIME

/-- `needs "ANT/norm_index.ml"`: already done by importing this module. -/
def ensureNormIndex : IO Unit := pure ()

end SessionANT.NormIndex
