/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/absolute_values.ml                            . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/AbsoluteValues.lean

  The session half of the absolute_values.ml translation: it supplies HolANT.AbsoluteValues's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/absolute_values.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.AbsoluteValues
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
import SessionLibrary.Floor
import SessionANT.Integral
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.IdealNorm
import SessionANT.ValuationRing
import SessionANT.DedekindAbsolute
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
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
import SessionMultiLib.RealAnalysis

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.AbsoluteValues

/-- The core theorems absolute_values.ml uses. -/
def core1 : HolANT.AbsoluteValues.CoreThms1 where
  ABSOLUTE_VALUE_0 := SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_0»
  ABSOLUTE_VALUE_1 := SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_1»
  ABSOLUTE_VALUE_ABS_SUB_LE := SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_ABS_SUB_LE»
  ABSOLUTE_VALUE_DIV := SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_DIV»
  ABSOLUTE_VALUE_INV := SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_INV»
  ABSOLUTE_VALUE_MUL := SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_MUL»
  ABSOLUTE_VALUE_NEG := SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_NEG»
  ABSOLUTE_VALUE_NONTRIVIAL := SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_NONTRIVIAL»
  ABSOLUTE_VALUE_POS := SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_POS»
  ABSOLUTE_VALUE_POS_LT := SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_POS_LT»
  ABSOLUTE_VALUE_POW := SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_POW»
  ABSOLUTE_VALUE_RING_SUM := SessionANT.DedekindAbsolute.«ABSOLUTE_VALUE_RING_SUM»
  ARCH_EVENTUALLY_POW := SessionMultiLib.Metric.«ARCH_EVENTUALLY_POW»
  CARD_EQ_0 := Session.CARD_EQ_0
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DEDEKIND_IMP_INTEGRAL_DOMAIN := SessionANT.Dedekind.«DEDEKIND_IMP_INTEGRAL_DOMAIN»
  DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL := SessionANT.Dedekind.«DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL»
  DEDEKIND_VALUATION_ABSOLUTE_VALUE := SessionANT.DedekindAbsolute.«DEDEKIND_VALUATION_ABSOLUTE_VALUE»
  DEDEKIND_VALUATION_IMAGE := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_IMAGE»
  DEDEKIND_VALUATION_POS := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_POS»
  DEDEKIND_VALUATION_PRIME_IDEAL := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_PRIME_IDEAL»
  DEDEKIND_VALUATION_WEAK_APPROXIMATION := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_WEAK_APPROXIMATION»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  EVENTUALLY_AND := SessionMultiLib.Metric.«EVENTUALLY_AND»
  EVENTUALLY_FORALL := SessionMultiLib.Metric.«EVENTUALLY_FORALL»
  EVENTUALLY_HAPPENS_SEQUENTIALLY := SessionMultiLib.Metric.«EVENTUALLY_HAPPENS_SEQUENTIALLY»
  EVENTUALLY_MONO := SessionMultiLib.Metric.«EVENTUALLY_MONO»
  EVENTUALLY_TRUE := SessionMultiLib.Metric.«EVENTUALLY_TRUE»
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXP_LOG := SessionMultiLib.Transcendentals.«EXP_LOG»
  EXTENSION := Session.EXTENSION
  FIELD_FRACTION_NONZERO := SessionANT.DedekindValuation.«FIELD_FRACTION_NONZERO»
  FIELD_MUL_RINV := SessionLibrary.RingTheory.«FIELD_MUL_RINV»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_SING := Session.FINITE_SING
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  IMP_CONJ := Session.IMP_CONJ
  INSERT_DELETE := Session.INSERT_DELETE
  INSERT_SUBSET := Session.INSERT_SUBSET
  INT_NEG_0 := Session.INT_NEG_0
  INT_NEG_NEG := Session.INT_NEG_NEG
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  IN_DELETE := Session.IN_DELETE
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_SING := Session.IN_SING
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_1 := Session.LE_1
  LOG_MONO_LT := SessionMultiLib.Transcendentals.«LOG_MONO_LT»
  LOG_MUL := SessionMultiLib.Transcendentals.«LOG_MUL»
  LOG_POS_LT := SessionMultiLib.Transcendentals.«LOG_POS_LT»
  LOG_POW := SessionMultiLib.Transcendentals.«LOG_POW»
  NONARCHIMEDEAN_ABSOLUTE_VALUE := SessionANT.DedekindAbsolute.«NONARCHIMEDEAN_ABSOLUTE_VALUE»
  NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE := SessionANT.DedekindAbsolute.«NONARCHIMEDEAN_IMP_ABSOLUTE_VALUE»
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  PRIME_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_SUBSET»
  PRIME_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_PROPER_IDEAL»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PROPER_IDEAL_ALT := SessionLibrary.RingTheory.«PROPER_IDEAL_ALT»
  PSUBSET := Session.PSUBSET
  REAL_ARCH_POW := Session.REAL_ARCH_POW
  REAL_ARCH_POW_INV := Session.REAL_ARCH_POW_INV
  REAL_INV_1_LT := Session.REAL_INV_1_LT
  REAL_INV_INV := Session.REAL_INV_INV
  REAL_INV_LT_1 := Session.REAL_INV_LT_1
  REAL_LET_TRANS := Session.REAL_LET_TRANS
  REAL_LE_INV_EQ := Session.REAL_LE_INV_EQ
  REAL_LE_LMUL := Session.REAL_LE_LMUL
  REAL_LE_MAX := Session.REAL_LE_MAX
  REAL_LE_MUL2 := Session.REAL_LE_MUL2
  REAL_LE_RMUL := Session.REAL_LE_RMUL
  REAL_LE_TRANS := Session.REAL_LE_TRANS
  REAL_LTE_TRANS := Session.REAL_LTE_TRANS
  REAL_LT_01 := Session.REAL_LT_01
/-- The core theorems absolute_values.ml uses. -/
def core2 : HolANT.AbsoluteValues.CoreThms2 where
  REAL_LT_DIV := Session.REAL_LT_DIV
  REAL_LT_IMP_LE := Session.REAL_LT_IMP_LE
  REAL_LT_IMP_NE := Session.REAL_LT_IMP_NE
  REAL_LT_IMP_NZ := Session.REAL_LT_IMP_NZ
  REAL_LT_INV2 := Session.REAL_LT_INV2
  REAL_LT_INV_EQ := Session.REAL_LT_INV_EQ
  REAL_LT_LDIV_EQ := Session.REAL_LT_LDIV_EQ
  REAL_LT_LE := Session.REAL_LT_LE
  REAL_LT_LMUL := Session.REAL_LT_LMUL
  REAL_LT_RDIV_EQ := Session.REAL_LT_RDIV_EQ
  REAL_LT_REFL := Session.REAL_LT_REFL
  REAL_LT_TRANS := Session.REAL_LT_TRANS
  REAL_MAX_LT := Session.REAL_MAX_LT
  REAL_MAX_RPOW := SessionMultiLib.Transcendentals.«REAL_MAX_RPOW»
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_RID := Session.REAL_MUL_RID
  REAL_MUL_RINV := Session.REAL_MUL_RINV
  REAL_MUL_SYM := Session.REAL_MUL_SYM
  REAL_NOT_LT := Session.REAL_NOT_LT
  REAL_NUM_FRACTIONS_EQ := SessionLibrary.Floor.«REAL_NUM_FRACTIONS_EQ»
  REAL_OF_NUM_LT := Session.REAL_OF_NUM_LT
  REAL_POS := Session.REAL_POS
  REAL_POW_1 := Session.REAL_POW_1
  REAL_POW_1_LE := Session.REAL_POW_1_LE
  REAL_POW_EVENTUALLY_LT := SessionMultiLib.RealAnalysis.«REAL_POW_EVENTUALLY_LT»
  REAL_POW_LE := Session.REAL_POW_LE
  REAL_POW_LE_1 := Session.REAL_POW_LE_1
  REAL_POW_LT := Session.REAL_POW_LT
  REAL_POW_ONE := Session.REAL_POW_ONE
  REAL_SUB_LT := Session.REAL_SUB_LT
  REAL_ZPOW_0 := Session.REAL_ZPOW_0
  REAL_ZPOW_1 := Session.REAL_ZPOW_1
  REAL_ZPOW_MONO_LT := Session.REAL_ZPOW_MONO_LT
  REAL_ZPOW_RPOW := SessionMultiLib.Transcendentals.«REAL_ZPOW_RPOW»
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_DIV := SessionLibrary.RingTheory.«RING_DIV»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_NEG := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_NEG»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_MONOMORPHISM_EQ_0 := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EQ_0»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_CLAUSES := SessionLibrary.RingTheory.«RING_SUM_CLAUSES»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RPOW_1_LE := SessionMultiLib.Transcendentals.«RPOW_1_LE»
  RPOW_ADD_LE := SessionMultiLib.Transcendentals.«RPOW_ADD_LE»
  RPOW_EQ_0 := SessionMultiLib.Transcendentals.«RPOW_EQ_0»
  RPOW_LE2 := SessionMultiLib.Transcendentals.«RPOW_LE2»
  RPOW_LT2 := SessionMultiLib.Transcendentals.«RPOW_LT2»
  RPOW_LT_1 := SessionMultiLib.Transcendentals.«RPOW_LT_1»
  RPOW_MUL := SessionMultiLib.Transcendentals.«RPOW_MUL»
  RPOW_ONE := SessionMultiLib.Transcendentals.«RPOW_ONE»
  RPOW_POS_LE := SessionMultiLib.Transcendentals.«RPOW_POS_LE»
  RPOW_POW := SessionMultiLib.Transcendentals.«RPOW_POW»
  RPOW_RPOW := SessionMultiLib.Transcendentals.«RPOW_RPOW»
  RPOW_ZERO := SessionMultiLib.Transcendentals.«RPOW_ZERO»
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  SUBSET_REFL := Session.SUBSET_REFL
  SUM_BOUND_LT := Session.SUM_BOUND_LT
  absolute_value := SessionANT.DedekindAbsolute.«absolute_value»
  field_of_fractions := SessionLibrary.RingTheory.«field_of_fractions»
  lemma := SessionMultiLib.Integration.«lemma»
  maximal_ideal := SessionLibrary.RingTheory.«maximal_ideal»
  nonarchimedean_absolute_value := SessionANT.DedekindAbsolute.«nonarchimedean_absolute_value»
  prime_ideal := SessionLibrary.RingTheory.«prime_ideal»
  real_div := Session.real_div
  ring_div := SessionLibrary.RingTheory.«ring_div»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_ideal := SessionLibrary.RingTheory.«ring_ideal»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  rpow := SessionMultiLib.Transcendentals.«rpow»

/-- What absolute_values.ml uses from Session. -/
def deps : HolANT.AbsoluteValues.AbsoluteValuesDeps where
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
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in absolute_values.ml order. -/
initialize BAbsoluteValues01 : HolANT.AbsoluteValues.AbsoluteValues01 ←
  ioB "setupAbsoluteValues01" (HolANT.AbsoluteValues.setupAbsoluteValues01 deps).run
initialize BAbsoluteValues02 : HolANT.AbsoluteValues.AbsoluteValues02 ←
  ioB "setupAbsoluteValues02" (HolANT.AbsoluteValues.setupAbsoluteValues02 deps BAbsoluteValues01).run

-- AbsoluteValues01
def ABSOLUTE_VALUE_EQUIVALENT : thm := BAbsoluteValues01.ABSOLUTE_VALUE_EQUIVALENT
def ABSOLUTE_VALUE_EQUIVALENT_LE : thm := BAbsoluteValues01.ABSOLUTE_VALUE_EQUIVALENT_LE
def ABSOLUTE_VALUE_EQUIVALENT_SYM : thm := BAbsoluteValues01.ABSOLUTE_VALUE_EQUIVALENT_SYM
def ABSOLUTE_VALUE_RPOW : thm := BAbsoluteValues01.ABSOLUTE_VALUE_RPOW
def NONARCHIMEDEAN_ABSOLUTE_VALUE_RPOW : thm := BAbsoluteValues01.NONARCHIMEDEAN_ABSOLUTE_VALUE_RPOW
def ABSOLUTE_VALUE_POW_QUOTIENT : thm := BAbsoluteValues01.ABSOLUTE_VALUE_POW_QUOTIENT
def ABSOLUTE_VALUE_INEQUIVALENT_SEPARATE : thm := BAbsoluteValues01.ABSOLUTE_VALUE_INEQUIVALENT_SEPARATE
def ABSOLUTE_VALUE_INEQUIVALENT_DOMINANT : thm := BAbsoluteValues01.ABSOLUTE_VALUE_INEQUIVALENT_DOMINANT
def ABSOLUTE_VALUE_WEAK_APPROXIMATION : thm := BAbsoluteValues01.ABSOLUTE_VALUE_WEAK_APPROXIMATION

-- AbsoluteValues02
def DEDEKIND_VALUATION_ABSOLUTE_VALUE_NONTRIVIAL : thm := BAbsoluteValues02.DEDEKIND_VALUATION_ABSOLUTE_VALUE_NONTRIVIAL
def DEDEKIND_ABSOLUTE_VALUE_PRIME : thm := BAbsoluteValues02.DEDEKIND_ABSOLUTE_VALUE_PRIME
def DEDEKIND_VALUATION_ABSOLUTE_VALUE_UNIQUE : thm := BAbsoluteValues02.DEDEKIND_VALUATION_ABSOLUTE_VALUE_UNIQUE
def DEDEKIND_NONARCHIMEDEAN_ABSOLUTE_VALUE : thm := BAbsoluteValues02.DEDEKIND_NONARCHIMEDEAN_ABSOLUTE_VALUE

/-- `needs "ANT/absolute_values.ml"`: already done by importing this module. -/
def ensureAbsoluteValues : IO Unit := pure ()

end SessionANT.AbsoluteValues
