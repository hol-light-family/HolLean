/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/relative_degree.ml                            . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/RelativeDegree.lean

  The session half of the relative_degree.ml translation: it supplies HolANT.RelativeDegree's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/relative_degree.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.RelativeDegree
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
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.PrimeSplit
import SessionANT.RelativeSplit

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.RelativeDegree

/-- The core theorems relative_degree.ml uses. -/
def core1 : HolANT.RelativeDegree.CoreThms1 where
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_EQ_NSUM := Session.CARD_EQ_NSUM
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES»
  DEDEKIND_IDEAL_SUBSET_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_POW_VALUATION»
  DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL := SessionANT.Dedekind.«DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL»
  DEDEKIND_PRIMITIVE_MULTIPLE := SessionANT.Dedekind.«DEDEKIND_PRIMITIVE_MULTIPLE»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  EQ_EXP := Session.EQ_EXP
  EQ_IMP_LE := Session.EQ_IMP_LE
  EQ_TRANS := Session.EQ_TRANS
  EXP := Session.EXP
  EXP_EXP := Session.EXP_EXP
  EXP_NSUM := SessionLibrary.Products.«EXP_NSUM»
  EXP_ONE := Session.EXP_ONE
  EXTENSION := Session.EXTENSION
  EXTENSION_LINCOMB_LMUL := SessionLibrary.RingDet.«EXTENSION_LINCOMB_LMUL»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_MUL_LINV := SessionLibrary.RingTheory.«FIELD_MUL_LINV»
  FIELD_QUOTIENT_RING := SessionLibrary.RingTheory.«FIELD_QUOTIENT_RING»
  FINITE_EXTENSION_RING_MATROID := SessionLibrary.FieldTheory.«FINITE_EXTENSION_RING_MATROID»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FREE_BASIS_EXISTS := SessionLibrary.FieldTheory.«FREE_BASIS_EXISTS»
  FREE_BASIS_FIELD := SessionLibrary.FieldTheory.«FREE_BASIS_FIELD»
  FREE_BASIS_HAS_SIZE := SessionLibrary.RingDet.«FREE_BASIS_HAS_SIZE»
  FREE_BASIS_INDEPENDENT := SessionLibrary.RingDet.«FREE_BASIS_INDEPENDENT»
  FREE_BASIS_INDEPENDENT_EQ := SessionLibrary.FieldTheory.«FREE_BASIS_INDEPENDENT_EQ»
  FREE_BASIS_IN_CARRIER := SessionLibrary.RingDet.«FREE_BASIS_IN_CARRIER»
  HAS_SIZE := Session.HAS_SIZE
  IDEAL_GENERATED_IMAGE_IDEAL_GENERATED := SessionANT.IdealArith.«IDEAL_GENERATED_IMAGE_IDEAL_GENERATED»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_GENERATED_SUBSET_CARRIER := SessionLibrary.RingTheory.«IDEAL_GENERATED_SUBSET_CARRIER»
  IDEAL_NORM_CARRIER := SessionANT.IdealNorm.«IDEAL_NORM_CARRIER»
  IDEAL_NORM_GT_1 := SessionANT.IdealNorm.«IDEAL_NORM_GT_1»
  IDEAL_NORM_IDEAL_POW := SessionANT.IdealNorm.«IDEAL_NORM_IDEAL_POW»
  IDEAL_NORM_IDEAL_PRODUCT := SessionANT.IdealNorm.«IDEAL_NORM_IDEAL_PRODUCT»
  IDEAL_NORM_POS := SessionANT.IdealNorm.«IDEAL_NORM_POS»
  IDEAL_POW_1 := SessionANT.IdealArith.«IDEAL_POW_1»
  IDEAL_POW_EQ_ZERO := SessionANT.IdealArith.«IDEAL_POW_EQ_ZERO»
  IDEAL_PROD_HOMOMORPHIC_IMAGE := SessionANT.IdealArith.«IDEAL_PROD_HOMOMORPHIC_IMAGE»
  IDEAL_PROD_RZERO := SessionANT.IdealArith.«IDEAL_PROD_RZERO»
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMP_CONJ := Session.IMP_CONJ
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_RING_OF_INTEGERS := SessionANT.Numfield.«INTEGRAL_DOMAIN_RING_OF_INTEGERS»
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_SING := Session.IN_SING
  LE_ANTISYM := Session.LE_ANTISYM
  LE_EXP := Session.LE_EXP
  LE_MULT2 := Session.LE_MULT2
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  LE_MULT_RCANCEL := Session.LE_MULT_RCANCEL
  LE_REFL := Session.LE_REFL
  LT_MULT_RCANCEL := Session.LT_MULT_RCANCEL
  MATROID_DIMENSION_GE_FINITE_CARD := SessionLibrary.Matroids.«MATROID_DIMENSION_GE_FINITE_CARD»
  MAXIMAL_IDEAL_IMP_PSUBSET := SessionLibrary.RingTheory.«MAXIMAL_IDEAL_IMP_PSUBSET»
  MAXIMAL_IMP_PRIME_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PRIME_IDEAL»
  MAXIMAL_IMP_RING_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_RING_IDEAL»
  MAXIMAL_SUPERIDEAL_EXISTS := SessionLibrary.RingTheory.«MAXIMAL_SUPERIDEAL_EXISTS»
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONO_EXISTS := Session.MONO_EXISTS
  MONO_FORALL := Session.MONO_FORALL
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_EXP := Session.MULT_EXP
  MULT_SYM := Session.MULT_SYM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NPRODUCT_EQ := SessionLibrary.Products.«NPRODUCT_EQ»
  NSUM_LE := Session.NSUM_LE
  NSUM_POS_BOUND := Session.NSUM_POS_BOUND
  NUMBER_FIELD_HOMOMORPHIC_PREIMAGE := SessionANT.RelativeSplit.«NUMBER_FIELD_HOMOMORPHIC_PREIMAGE»
  NUMBER_FIELD_IDEAL_NORM_MUL_Q := SessionANT.NormIndex.«NUMBER_FIELD_IDEAL_NORM_MUL_Q»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_PRIME_FACTORIZATION := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_FACTORIZATION»
  NUMBER_FIELD_PRIME_IDEALS_ABOVE := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_IDEALS_ABOVE»
  NUMBER_FIELD_TOWER_LAW := SessionANT.RelativeSplit.«NUMBER_FIELD_TOWER_LAW»
  PRIME_IDEAL_IMP_PSUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_PSUBSET»
  PRIME_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_SUBSET»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PSUBSET := Session.PSUBSET
  QUOTIENT_RING_0 := SessionLibrary.RingTheory.«QUOTIENT_RING_0»
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
  RESIDUE_DEGREE_QUOTIENT_RING := SessionANT.RelativeSplit.«RESIDUE_DEGREE_QUOTIENT_RING»
  RIGHT_EXISTS_IMP_THM := Session.RIGHT_EXISTS_IMP_THM
  RING_COSET_0 := SessionLibrary.RingTheory.«RING_COSET_0»
  RING_COSET_EQ_IDEAL := SessionLibrary.RingTheory.«RING_COSET_EQ_IDEAL»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_HOMOMORPHISM_RING_OF_INTEGERS»
  RING_HOMOMORPHISM_SUM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM_MUL»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IMP_NONEMPTY := SessionLibrary.RingTheory.«RING_IDEAL_IMP_NONEMPTY»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_MATROID_INDEPENDENT := SessionLibrary.FieldTheory.«RING_MATROID_INDEPENDENT»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_COMMON_DENOMINATOR := SessionANT.Numfield.«RING_OF_INTEGERS_COMMON_DENOMINATOR»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_IDEAL_EXTENSION := SessionANT.RelativeSplit.«RING_OF_INTEGERS_IDEAL_EXTENSION»
  RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME := SessionANT.RelativeSplit.«RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME»
  RING_OF_INTEGERS_IDEAL_INTEGER := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_IDEAL_INTEGER»
  RING_OF_INTEGERS_IDEAL_NORM_INTEGER := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_IDEAL_NORM_INTEGER»
  RING_OF_INTEGERS_IDEAL_NORM_PRIME := SessionANT.RelativeSplit.«RING_OF_INTEGERS_IDEAL_NORM_PRIME»
  RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION := SessionANT.RelativeSplit.«RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_EQ_0_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0_CHAR_0»
  RING_OF_INT_IN_RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INT_IN_RING_OF_INTEGERS»
  RING_SPAN_SELF := SessionLibrary.FieldTheory.«RING_SPAN_SELF»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_SUM_RING_OF_INTEGERS»
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  SUBSET_REFL := Session.SUBSET_REFL
  extension_degree := SessionLibrary.FieldTheory.«extension_degree»
  ideal_norm := SessionANT.IdealNorm.«ideal_norm»
  number_field := SessionANT.Numfield.«number_field»
  proper_ideal := SessionLibrary.RingTheory.«proper_ideal»
  ramification_index := SessionANT.PrimeSplit.«ramification_index»
  ring_spanning := SessionLibrary.FieldTheory.«ring_spanning»

/-- What relative_degree.ml uses from Session. -/
def deps : HolANT.RelativeDegree.RelativeDegreeDeps where
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
  WF_INDUCT_TAC := Session.WF_INDUCT_TAC
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in relative_degree.ml order. -/
initialize BRelativeDegree : HolANT.RelativeDegree.RelativeDegree ←
  ioB "setupRelativeDegree" (HolANT.RelativeDegree.setupRelativeDegree deps).run

-- RelativeDegree
def NUMBER_FIELD_INDEPENDENT_MOD_IDEAL : thm := BRelativeDegree.NUMBER_FIELD_INDEPENDENT_MOD_IDEAL
def RING_OF_INTEGERS_QUOTIENT_FREE_BASIS_LE : thm := BRelativeDegree.RING_OF_INTEGERS_QUOTIENT_FREE_BASIS_LE
def RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION_PRIME : thm := BRelativeDegree.RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION_PRIME
def NUMBER_FIELD_IDEAL_NORM_EXTENSION_PRIME_LE : thm := BRelativeDegree.NUMBER_FIELD_IDEAL_NORM_EXTENSION_PRIME_LE
def NUMBER_FIELD_IDEAL_NORM_EXTENSION_LE : thm := BRelativeDegree.NUMBER_FIELD_IDEAL_NORM_EXTENSION_LE
def NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q : thm := BRelativeDegree.NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q
def NUMBER_FIELD_FUNDAMENTAL_IDENTITY : thm := BRelativeDegree.NUMBER_FIELD_FUNDAMENTAL_IDENTITY
def NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS : thm := BRelativeDegree.NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS
def NUMBER_FIELD_CARD_PRIME_IDEALS_ABOVE : thm := BRelativeDegree.NUMBER_FIELD_CARD_PRIME_IDEALS_ABOVE

/-- `needs "ANT/relative_degree.ml"`: already done by importing this module. -/
def ensureRelativeDegree : IO Unit := pure ()

end SessionANT.RelativeDegree
