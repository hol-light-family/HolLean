/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/ramification.ml                               . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/Ramification.lean

  The session half of the ramification.ml translation: it supplies HolANT.Ramification's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/ramification.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.Ramification
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.Ramification

/-- The core theorems ramification.ml uses. -/
def core1 : HolANT.Ramification.CoreThms1 where
  ALGEBRA_TRACE_NILPOTENT := SessionLibrary.RingDet.«ALGEBRA_TRACE_NILPOTENT»
  ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE := SessionLibrary.RingDet.«ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE»
  ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO := SessionANT.FiniteFieldTrace.«ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO»
  BASIS_COORDINATES_EXPAND := SessionLibrary.RingDet.«BASIS_COORDINATES_EXPAND»
  BASIS_COORDINATES_LINCOMB := SessionLibrary.RingDet.«BASIS_COORDINATES_LINCOMB»
  BASIS_COORDINATES_LMUL := SessionLibrary.RingDet.«BASIS_COORDINATES_LMUL»
  BASIS_DISCRIMINANT_EQ_0_FINITE := SessionANT.FiniteFieldTrace.«BASIS_DISCRIMINANT_EQ_0_FINITE»
  BASIS_DISCRIMINANT_HOMOMORPHIC_IMAGE := SessionLibrary.RingDet.«BASIS_DISCRIMINANT_HOMOMORPHIC_IMAGE»
  DEDEKIND_QUOTIENT_RING_REDUCED := SessionANT.Dedekind.«DEDEKIND_QUOTIENT_RING_REDUCED»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  EXTENSION_LINCOMB_LMUL := SessionLibrary.RingDet.«EXTENSION_LINCOMB_LMUL»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_INTEGER_MOD_RING := SessionLibrary.RingTheory.«FIELD_INTEGER_MOD_RING»
  FINITE_INTEGER_MOD_RING := SessionLibrary.RingTheory.«FINITE_INTEGER_MOD_RING»
  FINITE_NUMSEG_LE := Session.FINITE_NUMSEG_LE
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FREE_BASIS_IN_CARRIER := SessionLibrary.RingDet.«FREE_BASIS_IN_CARRIER»
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_GENERATED_INC := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_GENERATED_SING := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING»
  IDEAL_VALUATION_EQ_0 := SessionANT.Dedekind.«IDEAL_VALUATION_EQ_0»
  INTEGER_MOD_RING_CARRIER_REM := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CARRIER_REM»
  INTEGER_MOD_RING_CLAUSES := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CLAUSES»
  INTEGER_MOD_RING_OF_INT := SessionLibrary.RingTheory.«INTEGER_MOD_RING_OF_INT»
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_ABS_POS := Session.INT_ABS_POS
  INT_DIVIDES_LE := Session.INT_DIVIDES_LE
  INT_OF_NUM_LE := Session.INT_OF_NUM_LE
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_REM_EQ_0 := Session.INT_REM_EQ_0
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_INTEGER_MOD_RING_CARRIER := SessionLibrary.RingTheory.«IN_INTEGER_MOD_RING_CARRIER»
  IN_SING := Session.IN_SING
  IN_UNIV := Session.IN_UNIV
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_LE := Session.NOT_LE
  NUMBER_FIELD_DISCRIMINANT_BASIS := SessionANT.Discriminant.«NUMBER_FIELD_DISCRIMINANT_BASIS»
  NUMBER_FIELD_DISCRIMINANT_NONZERO := SessionANT.Discriminant.«NUMBER_FIELD_DISCRIMINANT_NONZERO»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  QUOTIENT_RING_0 := SessionLibrary.RingTheory.«QUOTIENT_RING_0»
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
  RAMIFICATION_INDEX_PRIME := SessionANT.PrimeSplit.«RAMIFICATION_INDEX_PRIME»
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RING_COSET_EQ_IDEAL := SessionLibrary.RingTheory.«RING_COSET_EQ_IDEAL»
  RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_RING_OF_NUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_NUM»
  RING_HOMOMORPHISM_SUM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM_MUL»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_NILPOTENT := SessionLibrary.RingTheory.«RING_NILPOTENT»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_FREE := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  free_basis := SessionLibrary.RingDet.«free_basis»
  int_divides := Session.int_divides
  number_field := SessionANT.Numfield.«number_field»
  o_DEF := Session.o_DEF
  ring_divides := SessionLibrary.RingTheory.«ring_divides»

/-- What ramification.ml uses from Session. -/
def deps : HolANT.Ramification.RamificationDeps where
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

/- The bundles, in ramification.ml order. -/
initialize BRamification : HolANT.Ramification.Ramification ←
  ioB "setupRamification" (HolANT.Ramification.setupRamification deps).run

-- Ramification
def RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING : thm := BRamification.RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING
def FREE_BASIS_IDEAL_GENERATED_NUM : thm := BRamification.FREE_BASIS_IDEAL_GENERATED_NUM
def FREE_BASIS_QUOTIENT_RING_INTEGER_MOD : thm := BRamification.FREE_BASIS_QUOTIENT_RING_INTEGER_MOD
def ALGEBRA_TRACE_QUOTIENT_RING_INTEGER_MOD : thm := BRamification.ALGEBRA_TRACE_QUOTIENT_RING_INTEGER_MOD
def BASIS_DISCRIMINANT_QUOTIENT_RING_INTEGER_MOD : thm := BRamification.BASIS_DISCRIMINANT_QUOTIENT_RING_INTEGER_MOD
def ALGEBRA_TRACE_NILPOTENT_INTEGER_MOD : thm := BRamification.ALGEBRA_TRACE_NILPOTENT_INTEGER_MOD
def ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL : thm := BRamification.ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL
def NUMBER_FIELD_DISCRIMINANT_DIVIDES : thm := BRamification.NUMBER_FIELD_DISCRIMINANT_DIVIDES
def NUMBER_FIELD_RAMIFIED_DISCRIMINANT : thm := BRamification.NUMBER_FIELD_RAMIFIED_DISCRIMINANT
def NUMBER_FIELD_FINITE_RAMIFIED_PRIMES : thm := BRamification.NUMBER_FIELD_FINITE_RAMIFIED_PRIMES

/-- `needs "ANT/ramification.ml"`: already done by importing this module. -/
def ensureRamification : IO Unit := pure ()

end SessionANT.Ramification
