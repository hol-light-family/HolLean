/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/valuation_rank_one.ml                         . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/ValuationRankOne.lean

  The session half of the valuation_rank_one.ml translation: it supplies HolANT.ValuationRankOne's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/valuation_rank_one.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.ValuationRankOne
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.Matroids
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.RingTheory
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionLibrary.FieldTheory
import SessionANT.IdealArith
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.IdealNorm
import SessionANT.ValuationRing
import SessionANT.DedekindAbsolute
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.NfValuation
import SessionANT.PrimeSplit
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionANT.Decomposition
import SessionANT.RelativeDegree
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.SplittingTypes
import SessionANT.NfDecomposition
import SessionANT.ValuationResidue
import SessionMultiLib.Misc
import SessionMultiLib.Metric
import SessionMultiLib.Homology
import SessionMultiLib.Vectors
import SessionMultiLib.Determinants
import SessionMultiLib.Topology
import SessionMultiLib.Convex
import SessionMultiLib.Paths
import SessionMultiLib.Polytope
import SessionMultiLib.Degree
import SessionMultiLib.Derivatives
import SessionMultiLib.Integration
import SessionMultiLib.Measure
import SessionMultiLib.ComplexAlgebra
import SessionMultiLib.Complexes
import SessionMultiLib.Canal
import SessionMultiLib.Transcendentals

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.ValuationRankOne

/-- The core theorems valuation_rank_one.ml uses. -/
def core1 : HolANT.ValuationRankOne.CoreThms1 where
  CARRIER_SUBFIELD_GENERATED_SUBFIELD := SessionLibrary.FieldTheory.«CARRIER_SUBFIELD_GENERATED_SUBFIELD»
  CONJ_ASSOC := Session.CONJ_ASSOC
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DEDEKIND_VALUATION_ADD := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_ADD»
  DEDEKIND_VALUATION_IMAGE := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_IMAGE»
  DEDEKIND_VALUATION_MUL := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_MUL»
  DEDEKIND_VALUATION_PRIME_IDEAL := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_PRIME_IDEAL»
  DEDEKIND_VALUATION_RAMIFICATION_INDEX := SessionANT.RelativeSplit.«DEDEKIND_VALUATION_RAMIFICATION_INDEX»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_SING := Session.FINITE_SING
  IMAGE_I := Session.IMAGE_I
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INT_MIN_LE := Session.INT_MIN_LE
  INT_MUL_LZERO := Session.INT_MUL_LZERO
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  IN_INSERT := Session.IN_INSERT
  IN_SING := Session.IN_SING
  IN_SUBFIELD_ADD := SessionLibrary.FieldTheory.«IN_SUBFIELD_ADD»
  IN_SUBFIELD_MUL := SessionLibrary.FieldTheory.«IN_SUBFIELD_MUL»
  IN_SUBRING_0 := SessionLibrary.RingTheory.«IN_SUBRING_0»
  I_THM := Session.I_THM
  MONO_OR := Session.MONO_OR
  NONARCHIMEDEAN_ABSOLUTE_VALUE := SessionANT.DedekindAbsolute.«NONARCHIMEDEAN_ABSOLUTE_VALUE»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC := SessionANT.Numfield.«NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC»
  PRIME_0 := SessionLibrary.Prime.«PRIME_0»
  PRIME_GE_2 := SessionLibrary.Prime.«PRIME_GE_2»
  RAMIFICATION_INDEX_PRIME := SessionANT.PrimeSplit.«RAMIFICATION_INDEX_PRIME»
  REAL_ADD_RDISTRIB := Session.REAL_ADD_RDISTRIB
  REAL_DIV_REFL := Session.REAL_DIV_REFL
  REAL_LE_DIV2_EQ := Session.REAL_LE_DIV2_EQ
  REAL_LE_MAX := Session.REAL_LE_MAX
  REAL_LE_RDIV_EQ := Session.REAL_LE_RDIV_EQ
  REAL_LE_REFL := Session.REAL_LE_REFL
  REAL_LT_IMP_LE := Session.REAL_LT_IMP_LE
  REAL_LT_IMP_NZ := Session.REAL_LT_IMP_NZ
  REAL_MIN_LE := Session.REAL_MIN_LE
  REAL_MUL_LZERO := Session.REAL_MUL_LZERO
  REAL_MUL_RZERO := Session.REAL_MUL_RZERO
  REAL_NEG_ADD := Session.REAL_NEG_ADD
  REAL_OF_INT_CLAUSES := Session.REAL_OF_INT_CLAUSES
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_OF_NUM_LT := Session.REAL_OF_NUM_LT
  REAL_POS := Session.REAL_POS
  REAL_POW_1 := Session.REAL_POW_1
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_CHAR_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_CHAR_SUBFIELD_GENERATED»
  RING_CHAR_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_CHAR_SUBRING_GENERATED»
  RING_MONOMORPHISM_BETWEEN_SUBRINGS := SessionLibrary.RingTheory.«RING_MONOMORPHISM_BETWEEN_SUBRINGS»
  RING_MONOMORPHISM_I := SessionLibrary.RingTheory.«RING_MONOMORPHISM_I»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_MONOMORPHISM_RING_OF_INTEGERS»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_FRACTION_FIELD := SessionANT.NfValuation.«RING_OF_INTEGERS_FRACTION_FIELD»
  RING_OF_INTEGERS_SUBFIELD_GENERATED := SessionANT.RelativeSplit.«RING_OF_INTEGERS_SUBFIELD_GENERATED»
  RING_OF_INT_EQ_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_INT_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_SUBFIELD_GENERATED»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_OF_NUM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_NUM_SUBFIELD_GENERATED»
  RPOW_0 := SessionMultiLib.Transcendentals.«RPOW_0»
  RPOW_ADD := SessionMultiLib.Transcendentals.«RPOW_ADD»
  RPOW_MONO_LE := SessionMultiLib.Transcendentals.«RPOW_MONO_LE»
  RPOW_MONO_LE_EQ := SessionMultiLib.Transcendentals.«RPOW_MONO_LE_EQ»
  RPOW_NEG := SessionMultiLib.Transcendentals.«RPOW_NEG»
  RPOW_POS_LT := SessionMultiLib.Transcendentals.«RPOW_POS_LT»
  RPOW_POW := SessionMultiLib.Transcendentals.«RPOW_POW»
  SING_SUBSET := Session.SING_SUBSET
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_INC_GEN := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_INC_GEN»
  SUBFIELD_GENERATED_MINIMAL := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_MINIMAL»
  SUBFIELD_OF_IMP_SUBSET := SessionLibrary.FieldTheory.«SUBFIELD_OF_IMP_SUBSET»
  SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_SUBFIELD_GENERATED»
  SUBRING_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBRING_GENERATED_BY_SUBFIELD_GENERATED»
  SUBSET := Session.SUBSET
  VALUATION_SUBRING_NUMBER_SUBFIELD := SessionANT.ValuationResidue.«VALUATION_SUBRING_NUMBER_SUBFIELD»
  VALUATION_SUBRING_NUMBER_SUBFIELD_VALUATION := SessionANT.ValuationResidue.«VALUATION_SUBRING_NUMBER_SUBFIELD_VALUATION»
  algebraic_extension := SessionLibrary.FieldTheory.«algebraic_extension»
  int_add_th := Session.int_add_th
  int_le := Session.int_le
  int_mul_th := Session.int_mul_th
  int_of_num_th := Session.int_of_num_th
  number_field := SessionANT.Numfield.«number_field»
  real_div := Session.real_div
  ring_of_integers := SessionANT.Numfield.«ring_of_integers»
  valuation_subring := SessionANT.ValuationRing.«valuation_subring»

/-- What valuation_rank_one.ml uses from Session. -/
def deps : HolANT.ValuationRankOne.ValuationRankOneDeps where
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
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in valuation_rank_one.ml order. -/
initialize BValuationRankOne : HolANT.ValuationRankOne.ValuationRankOne ←
  ioB "setupValuationRankOne" (HolANT.ValuationRankOne.setupValuationRankOne deps).run

-- ValuationRankOne
def VALUATION_SUBRING_NUMBER_SUBFIELD_RAMIFICATION : thm := BValuationRankOne.VALUATION_SUBRING_NUMBER_SUBFIELD_RAMIFICATION
def VALUATION_SUBRING_NUMBER_SUBFIELD_TOWER : thm := BValuationRankOne.VALUATION_SUBRING_NUMBER_SUBFIELD_TOWER
def VALUATION_SUBRING_NUMBER_SUBFIELD_RATIO : thm := BValuationRankOne.VALUATION_SUBRING_NUMBER_SUBFIELD_RATIO
def ALGEBRAIC_VALUATION_SUBRING_RANK_ONE : thm := BValuationRankOne.ALGEBRAIC_VALUATION_SUBRING_RANK_ONE
def ALGEBRAIC_VALUATION_SUBRING_ABSOLUTE_VALUE : thm := BValuationRankOne.ALGEBRAIC_VALUATION_SUBRING_ABSOLUTE_VALUE

/-- `needs "ANT/valuation_rank_one.ml"`: already done by importing this module. -/
def ensureValuationRankOne : IO Unit := pure ()

end SessionANT.ValuationRankOne
