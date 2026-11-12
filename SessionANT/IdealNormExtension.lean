/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/ideal_norm_extension.ml                       . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/IdealNormExtension.lean

  The session half of the ideal_norm_extension.ml translation: it supplies HolANT.IdealNormExtension's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/ideal_norm_extension.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.IdealNormExtension
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
import SessionANT.IdealArith
import SessionLibrary.Products
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
import SessionANT.NormIndex
import SessionANT.PrimeSplit
import SessionANT.Classgroup
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.RelativeDegree
import SessionANT.NfValuation
import SessionANT.Integrality
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionANT.Decomposition
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.SplittingTypes
import SessionANT.NfDecomposition
import SessionANT.ConjugateIdeals
import SessionLibrary.Integer
import SessionLibrary.Multiplicative
import SessionLibrary.Primitive
import SessionANT.DedekindKummer
import SessionANT.DecompositionField
import SessionANT.SplitPrimes

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.IdealNormExtension

/-- The core theorems ideal_norm_extension.ml uses. -/
def core1 : HolANT.IdealNormExtension.CoreThms1 where
  ALGEBRA_NORM_EQ_0 := SessionLibrary.FieldTheory.«ALGEBRA_NORM_EQ_0»
  ALGEBRA_NORM_MUL := SessionLibrary.RingDet.«ALGEBRA_NORM_MUL»
  ALGEBRA_TRACE_NORM_GALOIS := SessionLibrary.Galois.«ALGEBRA_TRACE_NORM_GALOIS»
  ALGEBRA_TRACE_NORM_INTERMEDIATE := SessionLibrary.FieldTheory.«ALGEBRA_TRACE_NORM_INTERMEDIATE»
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DEDEKIND_IDEAL_EQ_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_EQ_VALUATION»
  DEDEKIND_IDEAL_INDUCT := SessionANT.Dedekind.«DEDEKIND_IDEAL_INDUCT»
  DEDEKIND_IDEAL_SUBSET_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_POW_VALUATION»
  DEDEKIND_IDEAL_SUBSET_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_VALUATION»
  DEDEKIND_IDEAL_WEAK_APPROXIMATION := SessionANT.DedekindStruct.«DEDEKIND_IDEAL_WEAK_APPROXIMATION»
  DEDEKIND_IMP_INTEGRAL_DOMAIN := SessionANT.Dedekind.«DEDEKIND_IMP_INTEGRAL_DOMAIN»
  DEDEKIND_IN_IDEAL_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IN_IDEAL_POW_VALUATION»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSION := Session.EXTENSION
  EXTENSION_DEGREE_EQ_0 := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_EQ_0»
  FINITE_GALOIS_GROUP := SessionLibrary.Galois.«FINITE_GALOIS_GROUP»
  FINITE_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_FIELD_EXTENSION»
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  GALOIS_GROUP_IMAGE_IDEAL_GENERATED := SessionANT.NfDecomposition.«GALOIS_GROUP_IMAGE_IDEAL_GENERATED»
  GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM := SessionANT.NfDecomposition.«GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM»
  GALOIS_GROUP_RING_OF_INTEGERS_IDEAL := SessionANT.NfDecomposition.«GALOIS_GROUP_RING_OF_INTEGERS_IDEAL»
  GALOIS_IMP_FIELD_EXTENSION := SessionLibrary.Galois.«GALOIS_IMP_FIELD_EXTENSION»
  IDEAL_GENERATED_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_0»
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_GENERATED_IMAGE_IDEAL_GENERATED := SessionANT.IdealArith.«IDEAL_GENERATED_IMAGE_IDEAL_GENERATED»
  IDEAL_GENERATED_INC := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_NORM_CARRIER := SessionANT.IdealNorm.«IDEAL_NORM_CARRIER»
  IDEAL_NORM_IDEAL_POW := SessionANT.IdealNorm.«IDEAL_NORM_IDEAL_POW»
  IDEAL_OF_VALUATIONS_UNIQUE := SessionANT.DedekindValuation.«IDEAL_OF_VALUATIONS_UNIQUE»
  IDEAL_POW_0 := SessionANT.IdealArith.«IDEAL_POW_0»
  IDEAL_POW_CARRIER := SessionANT.IdealArith.«IDEAL_POW_CARRIER»
  IDEAL_POW_EQ_ZERO := SessionANT.IdealArith.«IDEAL_POW_EQ_ZERO»
  IDEAL_POW_SUC := SessionANT.IdealArith.«IDEAL_POW_SUC»
  IDEAL_PRODUCT_EQ := SessionANT.IdealArith.«IDEAL_PRODUCT_EQ»
  IDEAL_PRODUCT_EQ_ZERO := SessionANT.IdealArith.«IDEAL_PRODUCT_EQ_ZERO»
  IDEAL_PRODUCT_PRINCIPAL := SessionANT.IdealArith.«IDEAL_PRODUCT_PRINCIPAL»
  IDEAL_PROD_EQ_ZERO := SessionANT.IdealArith.«IDEAL_PROD_EQ_ZERO»
  IDEAL_PROD_LZERO := SessionANT.IdealArith.«IDEAL_PROD_LZERO»
  IDEAL_PROD_RZERO := SessionANT.IdealArith.«IDEAL_PROD_RZERO»
  IDEAL_VALUATION_CARRIER := SessionANT.Dedekind.«IDEAL_VALUATION_CARRIER»
  IDEAL_VALUATION_IDEAL_POW := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_POW»
  IDEAL_VALUATION_IDEAL_PROD := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_PROD»
  IDEAL_VALUATION_IDEAL_PRODUCT := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_PRODUCT»
  IDEAL_VALUATION_PRIME := SessionANT.Dedekind.«IDEAL_VALUATION_PRIME»
  IDEAL_VALUATION_PRINCIPAL_POW := SessionANT.Dedekind.«IDEAL_VALUATION_PRINCIPAL_POW»
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMAGE_o := Session.IMAGE_o
  IMP_CONJ := Session.IMP_CONJ
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_IDEAL_GENERATED_SING_EQ := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SING_EQ»
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_SING := Session.IN_SING
  LEFT_ADD_DISTRIB := Session.LEFT_ADD_DISTRIB
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_ANTISYM := Session.LE_ANTISYM
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MULT_CLAUSES := Session.MULT_CLAUSES
  NSUM_ADD := Session.NSUM_ADD
  NSUM_DELTA := Session.NSUM_DELTA
  NSUM_EQ := Session.NSUM_EQ
  NSUM_EQ_0 := Session.NSUM_EQ_0
  NSUM_GROUP := Session.NSUM_GROUP
  NSUM_LE := Session.NSUM_LE
  NSUM_LMUL := Session.NSUM_LMUL
  NSUM_RMUL := Session.NSUM_RMUL
  NUMBER_FIELD_FUNDAMENTAL_IDENTITY := SessionANT.RelativeDegree.«NUMBER_FIELD_FUNDAMENTAL_IDENTITY»
  NUMBER_FIELD_GALOIS_CLOSURE := SessionANT.SplitPrimes.«NUMBER_FIELD_GALOIS_CLOSURE»
  NUMBER_FIELD_GALOIS_PRODUCT_PRIME := SessionANT.ConjugateIdeals.«NUMBER_FIELD_GALOIS_PRODUCT_PRIME»
  NUMBER_FIELD_HOMOMORPHIC_PREIMAGE := SessionANT.RelativeSplit.«NUMBER_FIELD_HOMOMORPHIC_PREIMAGE»
  NUMBER_FIELD_IDEAL_NORM_MUL_Q := SessionANT.NormIndex.«NUMBER_FIELD_IDEAL_NORM_MUL_Q»
  NUMBER_FIELD_IDEAL_VALUATION_EXTENSION := SessionANT.RelativeSplit.«NUMBER_FIELD_IDEAL_VALUATION_EXTENSION»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_NORM_INTEGRAL := SessionANT.Integrality.«NUMBER_FIELD_NORM_INTEGRAL»
  NUMBER_FIELD_NORM_MULTIPLE := SessionANT.Integrality.«NUMBER_FIELD_NORM_MULTIPLE»
  NUMBER_FIELD_PRIME_IDEALS_ABOVE := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_IDEALS_ABOVE»
  NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO»
  NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS := SessionANT.RelativeDegree.«NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS»
  NUMBER_FIELD_RESIDUE_DEGREE_TOWER := SessionANT.RelativeSplit.«NUMBER_FIELD_RESIDUE_DEGREE_TOWER»
  NUMBER_FIELD_TOWER_LAW := SessionANT.RelativeSplit.«NUMBER_FIELD_TOWER_LAW»
  PRIME_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_SUBSET»
  PRIME_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_PROPER_IDEAL»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PROPER_IDEAL_ALT := SessionLibrary.RingTheory.«PROPER_IDEAL_ALT»
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_HOMOMORPHISM_RING_OF_INTEGERS»
  RING_IDEAL_CARRIER := SessionLibrary.RingTheory.«RING_IDEAL_CARRIER»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IDEAL_PROD := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PROD»
  RING_IDEAL_IDEAL_PRODUCT := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PRODUCT»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_MONOMORPHISM_EQ_0 := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EQ_0»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_MONOMORPHISM_RING_OF_INTEGERS»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_IDEAL_EXTENSION := SessionANT.RelativeSplit.«RING_OF_INTEGERS_IDEAL_EXTENSION»
  RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME := SessionANT.RelativeSplit.«RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME»
  RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0 := SessionANT.Numfield.«RING_OF_INTEGERS_IDEAL_GENERATED_SING_EQ_0»
  RING_OF_INTEGERS_IDEAL_NORM_PRIME := SessionANT.RelativeSplit.«RING_OF_INTEGERS_IDEAL_NORM_PRIME»
  RING_OF_INTEGERS_PRIME_IDEAL_BELOW := SessionANT.RelativeSplit.«RING_OF_INTEGERS_PRIME_IDEAL_BELOW»
  RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION := SessionANT.RelativeSplit.«RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_PRODUCT_RING_OF_INTEGERS := SessionANT.Numfield.«RING_PRODUCT_RING_OF_INTEGERS»
  SING_SUBSET := Session.SING_SUBSET
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM_EQ := Session.SUBSET_ANTISYM_EQ
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  o_THM := Session.o_THM
  ring_divides := SessionLibrary.RingTheory.«ring_divides»

/-- What ideal_norm_extension.ml uses from Session. -/
def deps : HolANT.IdealNormExtension.IdealNormExtensionDeps where
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

/- The bundles, in ideal_norm_extension.ml order. -/
initialize BIdealNormExtension01 : HolANT.IdealNormExtension.IdealNormExtension01 ←
  ioB "setupIdealNormExtension01" (HolANT.IdealNormExtension.setupIdealNormExtension01 deps).run
initialize BIdealNormExtension02 : HolANT.IdealNormExtension.IdealNormExtension02 ←
  ioB "setupIdealNormExtension02" (HolANT.IdealNormExtension.setupIdealNormExtension02 deps BIdealNormExtension01).run
initialize BIdealNormExtension03 : HolANT.IdealNormExtension.IdealNormExtension03 ←
  ioB "setupIdealNormExtension03" (HolANT.IdealNormExtension.setupIdealNormExtension03 deps BIdealNormExtension01 BIdealNormExtension02).run

-- IdealNormExtension01
def RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION : thm := BIdealNormExtension01.RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION
def NUMBER_FIELD_NORM_EXPONENT_ADD : thm := BIdealNormExtension01.NUMBER_FIELD_NORM_EXPONENT_ADD
def NUMBER_FIELD_NORM_EXPONENT_PRIME : thm := BIdealNormExtension01.NUMBER_FIELD_NORM_EXPONENT_PRIME
def NUMBER_FIELD_NORM_EXPONENT_EXTENSION : thm := BIdealNormExtension01.NUMBER_FIELD_NORM_EXPONENT_EXTENSION
def NUMBER_FIELD_NORM_EXPONENT_MONO : thm := BIdealNormExtension01.NUMBER_FIELD_NORM_EXPONENT_MONO
def NUMBER_FIELD_NORM_EXPONENT_TOWER : thm := BIdealNormExtension01.NUMBER_FIELD_NORM_EXPONENT_TOWER
def NUMBER_FIELD_GALOIS_PRODUCT_VALUATION : thm := BIdealNormExtension01.NUMBER_FIELD_GALOIS_PRODUCT_VALUATION
def NUMBER_FIELD_GALOIS_NORM_VALUATION : thm := BIdealNormExtension01.NUMBER_FIELD_GALOIS_NORM_VALUATION

-- IdealNormExtension02
def NUMBER_FIELD_NORM_VALUATION : thm := BIdealNormExtension02.NUMBER_FIELD_NORM_VALUATION
def number_field_ideal_norm : thm := BIdealNormExtension02.number_field_ideal_norm
def NUMBER_FIELD_IDEAL_NORM_IDEAL : thm := BIdealNormExtension02.NUMBER_FIELD_IDEAL_NORM_IDEAL
def NUMBER_FIELD_IDEAL_NORM_PRINCIPAL : thm := BIdealNormExtension02.NUMBER_FIELD_IDEAL_NORM_PRINCIPAL
def NUMBER_FIELD_IDEAL_NORM_EXTENSION_SUBSET : thm := BIdealNormExtension02.NUMBER_FIELD_IDEAL_NORM_EXTENSION_SUBSET
def NUMBER_FIELD_IDEAL_NORM_VALUATION : thm := BIdealNormExtension02.NUMBER_FIELD_IDEAL_NORM_VALUATION
def NUMBER_FIELD_IDEAL_NORM_0 : thm := BIdealNormExtension02.NUMBER_FIELD_IDEAL_NORM_0
def NUMBER_FIELD_IDEAL_NORM_EQ_0 : thm := BIdealNormExtension02.NUMBER_FIELD_IDEAL_NORM_EQ_0
def NUMBER_FIELD_IDEAL_NORM_VALUATIONS : thm := BIdealNormExtension02.NUMBER_FIELD_IDEAL_NORM_VALUATIONS
def NUMBER_FIELD_IDEAL_NORM_MUL : thm := BIdealNormExtension02.NUMBER_FIELD_IDEAL_NORM_MUL
def NUMBER_FIELD_IDEAL_NORM_PRIME : thm := BIdealNormExtension02.NUMBER_FIELD_IDEAL_NORM_PRIME
def NUMBER_FIELD_IDEAL_NORM_EXTENSION : thm := BIdealNormExtension02.NUMBER_FIELD_IDEAL_NORM_EXTENSION
def NUMBER_FIELD_IDEAL_NORM_CARRIER : thm := BIdealNormExtension02.NUMBER_FIELD_IDEAL_NORM_CARRIER
def NUMBER_FIELD_IDEAL_NORM_POW : thm := BIdealNormExtension02.NUMBER_FIELD_IDEAL_NORM_POW
def NUMBER_FIELD_IDEAL_NORM_TOWER : thm := BIdealNormExtension02.NUMBER_FIELD_IDEAL_NORM_TOWER

-- IdealNormExtension03
def NUMBER_FIELD_IDEAL_NORM_IDEAL_NORM : thm := BIdealNormExtension03.NUMBER_FIELD_IDEAL_NORM_IDEAL_NORM
def NUMBER_FIELD_GALOIS_PRODUCT_IDEAL_NORM : thm := BIdealNormExtension03.NUMBER_FIELD_GALOIS_PRODUCT_IDEAL_NORM

/-- `needs "ANT/ideal_norm_extension.ml"`: already done by importing this module. -/
def ensureIdealNormExtension : IO Unit := pure ()

end SessionANT.IdealNormExtension
