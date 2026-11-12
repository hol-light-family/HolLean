/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/conjugate_ideals.ml                           . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/ConjugateIdeals.lean

  The session half of the conjugate_ideals.ml translation: it supplies HolANT.ConjugateIdeals's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/conjugate_ideals.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.ConjugateIdeals
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
import SessionANT.IdealNorm
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.PrimeSplit
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionANT.Decomposition
import SessionANT.NfValuation
import SessionANT.RelativeDegree
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.SplittingTypes
import SessionANT.NfDecomposition

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.ConjugateIdeals

/-- The core theorems conjugate_ideals.ml uses. -/
def core1 : HolANT.ConjugateIdeals.CoreThms1 where
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_EQ_NSUM := Session.CARD_EQ_NSUM
  CARD_GALOIS_GROUP_IMAGE_FIBER := SessionANT.NfDecomposition.«CARD_GALOIS_GROUP_IMAGE_FIBER»
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DEDEKIND_IDEAL_EQ_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_EQ_VALUATION»
  DEDEKIND_IDEAL_INDUCT := SessionANT.Dedekind.«DEDEKIND_IDEAL_INDUCT»
  DEDEKIND_IMP_INTEGRAL_DOMAIN := SessionANT.Dedekind.«DEDEKIND_IMP_INTEGRAL_DOMAIN»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSION := Session.EXTENSION
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_GALOIS_GROUP := SessionLibrary.Galois.«FINITE_GALOIS_GROUP»
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  GALOIS_GROUP_FIXES := SessionLibrary.Galois.«GALOIS_GROUP_FIXES»
  GALOIS_GROUP_PRIME_IDEAL_IMAGE := SessionANT.Decomposition.«GALOIS_GROUP_PRIME_IDEAL_IMAGE»
  GALOIS_GROUP_RING_OF_INTEGERS := SessionANT.NfDecomposition.«GALOIS_GROUP_RING_OF_INTEGERS»
  GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM := SessionANT.NfDecomposition.«GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM»
  GALOIS_GROUP_RING_OF_INTEGERS_IDEAL := SessionANT.NfDecomposition.«GALOIS_GROUP_RING_OF_INTEGERS_IDEAL»
  GALOIS_IMP_FIELD_EXTENSION := SessionLibrary.Galois.«GALOIS_IMP_FIELD_EXTENSION»
  IDEAL_GENERATED_IMAGE_IDEAL_GENERATED := SessionANT.IdealArith.«IDEAL_GENERATED_IMAGE_IDEAL_GENERATED»
  IDEAL_GENERATED_INC := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC»
  IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0 := SessionANT.IdealArith.«IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0»
  IDEAL_GENERATED_SING_EQ_CARRIER := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING_EQ_CARRIER»
  IDEAL_NORM_CARRIER := SessionANT.IdealNorm.«IDEAL_NORM_CARRIER»
  IDEAL_POW_EQ_ZERO := SessionANT.IdealArith.«IDEAL_POW_EQ_ZERO»
  IDEAL_POW_PRINCIPAL := SessionANT.IdealArith.«IDEAL_POW_PRINCIPAL»
  IDEAL_PRODUCT_EQ := SessionANT.IdealArith.«IDEAL_PRODUCT_EQ»
  IDEAL_PRODUCT_EQ_ZERO := SessionANT.IdealArith.«IDEAL_PRODUCT_EQ_ZERO»
  IDEAL_PRODUCT_MUL := SessionANT.IdealArith.«IDEAL_PRODUCT_MUL»
  IDEAL_PRODUCT_PRINCIPAL := SessionANT.IdealArith.«IDEAL_PRODUCT_PRINCIPAL»
  IDEAL_PROD_PRINCIPAL := SessionANT.IdealArith.«IDEAL_PROD_PRINCIPAL»
  IDEAL_VALUATION_EQ_0 := SessionANT.Dedekind.«IDEAL_VALUATION_EQ_0»
  IDEAL_VALUATION_IDEAL_POW := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_POW»
  IDEAL_VALUATION_IDEAL_PRODUCT := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_PRODUCT»
  IDEAL_VALUATION_PRIME := SessionANT.Dedekind.«IDEAL_VALUATION_PRIME»
  IMAGE_I := Session.IMAGE_I
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_SYM := Session.MULT_SYM
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NSUM_EQ := Session.NSUM_EQ
  NSUM_RESTRICT_SET := Session.NSUM_RESTRICT_SET
  NUMBER_FIELD_DECOMPOSITION_GROUP := SessionANT.NfDecomposition.«NUMBER_FIELD_DECOMPOSITION_GROUP»
  NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE := SessionANT.NfDecomposition.«NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE»
  NUMBER_FIELD_IDEAL_NORM_MUL_Q := SessionANT.NormIndex.«NUMBER_FIELD_IDEAL_NORM_MUL_Q»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_PRIME_IDEAL_ABOVE := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_IDEAL_ABOVE»
  NUMBER_FIELD_RAMIFICATION_INDEX_CONJUGATE := SessionANT.NfDecomposition.«NUMBER_FIELD_RAMIFICATION_INDEX_CONJUGATE»
  NUMBER_FIELD_TOWER_LAW := SessionANT.RelativeSplit.«NUMBER_FIELD_TOWER_LAW»
  PRIME_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_SUBSET»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  RESIDUE_DEGREE_PRIME_SUBFIELD := SessionANT.RelativeSplit.«RESIDUE_DEGREE_PRIME_SUBFIELD»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_HOMOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_HOMOMORPHISM_RING_OF_INTEGERS»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IDEAL_PRODUCT := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PRODUCT»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_MONOMORPHISM_RING_OF_INTEGERS»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q := SessionANT.PrimeSplit.«RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q»
  RING_OF_INTEGERS_PRIME_IDEAL_ABOVE := SessionANT.PrimeSplit.«RING_OF_INTEGERS_PRIME_IDEAL_ABOVE»
  RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL := SessionANT.RelativeSplit.«RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_1 := SessionLibrary.RingTheory.«RING_OF_NUM_1»
  RING_OF_NUM_EXP := SessionLibrary.RingTheory.«RING_OF_NUM_EXP»
  RING_OF_NUM_MUL := SessionLibrary.RingTheory.«RING_OF_NUM_MUL»
  RING_OF_NUM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_NUM_SUBFIELD_GENERATED»
  RING_PRODUCT_1 := SessionLibrary.RingTheory.«RING_PRODUCT_1»
  RING_UNIT_1 := SessionLibrary.RingTheory.«RING_UNIT_1»
  SING_SUBSET := Session.SING_SUBSET
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_TRANS := Session.SUBSET_TRANS
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  finite_extension := SessionLibrary.FieldTheory.«finite_extension»
  number_field := SessionANT.Numfield.«number_field»
  ramification_index := SessionANT.PrimeSplit.«ramification_index»

/-- What conjugate_ideals.ml uses from Session. -/
def deps : HolANT.ConjugateIdeals.ConjugateIdealsDeps where
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

/- The bundles, in conjugate_ideals.ml order. -/
initialize BConjugateIdeals : HolANT.ConjugateIdeals.ConjugateIdeals ←
  ioB "setupConjugateIdeals" (HolANT.ConjugateIdeals.setupConjugateIdeals deps).run

-- ConjugateIdeals
def NUMBER_FIELD_GALOIS_PRODUCT_PRIME : thm := BConjugateIdeals.NUMBER_FIELD_GALOIS_PRODUCT_PRIME
def NUMBER_FIELD_GALOIS_PRODUCT_IDEAL : thm := BConjugateIdeals.NUMBER_FIELD_GALOIS_PRODUCT_IDEAL

/-- `needs "ANT/conjugate_ideals.ml"`: already done by importing this module. -/
def ensureConjugateIdeals : IO Unit := pure ()

end SessionANT.ConjugateIdeals
