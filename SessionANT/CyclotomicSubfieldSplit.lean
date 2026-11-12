/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/cyclotomic_subfield_split.ml                  . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/CyclotomicSubfieldSplit.lean

  The session half of the cyclotomic_subfield_split.ml translation: it supplies HolANT.CyclotomicSubfieldSplit's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/cyclotomic_subfield_split.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.CyclotomicSubfieldSplit
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
import SessionLibrary.Integer
import SessionLibrary.Isum
import SessionLibrary.Products
import SessionLibrary.Multiplicative
import SessionLibrary.Primitive
import SessionLibrary.ModmulGroup
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.PrimeSplit
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.RelativeDegree
import SessionANT.SplittingTypes
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionANT.Decomposition
import SessionANT.NfValuation
import SessionANT.NfDecomposition
import SessionANT.DecompositionField
import SessionLibrary.Cyclotomic
import SessionANT.Integrality
import SessionANT.DedekindKummer
import SessionANT.CyclotomicPoly
import SessionANT.PowerBasis
import SessionANT.CyclotomicField
import SessionANT.CyclotomicGalois
import SessionANT.CyclotomicFrobenius

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.CyclotomicSubfieldSplit

/-- The core theorems cyclotomic_subfield_split.ml uses. -/
def core1 : HolANT.CyclotomicSubfieldSplit.CoreThms1 where
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CONG_REFL := SessionLibrary.Pocklington.«CONG_REFL»
  COPRIME_LEXP := SessionLibrary.Prime.«COPRIME_LEXP»
  CYCLOTOMIC_FIELD_FROBENIUS_ELEMENT := SessionANT.CyclotomicFrobenius.«CYCLOTOMIC_FIELD_FROBENIUS_ELEMENT»
  CYCLOTOMIC_FIELD_GALOIS_EXTENSION := SessionANT.CyclotomicGalois.«CYCLOTOMIC_FIELD_GALOIS_EXTENSION»
  CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ := SessionANT.CyclotomicGalois.«CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ»
  CYCLOTOMIC_FIELD_GALOIS_GROUP_EXISTS := SessionANT.CyclotomicGalois.«CYCLOTOMIC_FIELD_GALOIS_GROUP_EXISTS»
  CYCLOTOMIC_FIELD_GALOIS_GROUP_HAS_SIZE := SessionANT.CyclotomicGalois.«CYCLOTOMIC_FIELD_GALOIS_GROUP_HAS_SIZE»
  CYCLOTOMIC_FIELD_GALOIS_GROUP_MODMUL := SessionANT.CyclotomicGalois.«CYCLOTOMIC_FIELD_GALOIS_GROUP_MODMUL»
  CYCLOTOMIC_FIELD_INERTIA_GROUP := SessionANT.CyclotomicFrobenius.«CYCLOTOMIC_FIELD_INERTIA_GROUP»
  DECOMPOSITION_GROUP := SessionANT.Decomposition.«DECOMPOSITION_GROUP»
  DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL := SessionANT.Dedekind.«DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DIVIDES_ANTISYM := Session.DIVIDES_ANTISYM
  DIVIDES_ONE := Session.DIVIDES_ONE
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  EQ_TRANS := Session.EQ_TRANS
  EXP_1 := Session.EXP_1
  EXTENSION := Session.EXTENSION
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  GALOIS_CORRESPONDENCE_DEGREE := SessionLibrary.Galois.«GALOIS_CORRESPONDENCE_DEGREE»
  GALOIS_GROUP_FIXED_FIELD := SessionLibrary.Galois.«GALOIS_GROUP_FIXED_FIELD»
  GALOIS_GROUP_POW_ROOT := SessionLibrary.Galois.«GALOIS_GROUP_POW_ROOT»
  GROUP_ISOMORPHISM := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISM»
  GROUP_ISOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISM_IMP_HOMOMORPHISM»
  GROUP_POW := SessionLibrary.GroupTheory.«GROUP_POW»
  HAS_SIZE := Session.HAS_SIZE
  IMAGE_I := Session.IMAGE_I
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_FIXED_FIELD := SessionLibrary.Galois.«IN_FIXED_FIELD»
  IN_GALOIS_GROUP := SessionLibrary.Galois.«IN_GALOIS_GROUP»
  IN_GALOIS_GROUP_INTERMEDIATE := SessionLibrary.Galois.«IN_GALOIS_GROUP_INTERMEDIATE»
  IN_GALOIS_GROUP_SUBFIELD_GENERATED := SessionLibrary.Galois.«IN_GALOIS_GROUP_SUBFIELD_GENERATED»
  IN_INTER := Session.IN_INTER
  IN_SING := Session.IN_SING
  MAXIMAL_IMP_PRIME_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PRIME_IDEAL»
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MODMUL_GROUP_CONG_EQ := SessionLibrary.ModmulGroup.«MODMUL_GROUP_CONG_EQ»
  MULT_CLAUSES := Session.MULT_CLAUSES
  NSUM_CONST := Session.NSUM_CONST
  NSUM_EQ := Session.NSUM_EQ
  NUMBER_FIELD_FROBENIUS_ELEMENT := SessionANT.NfDecomposition.«NUMBER_FIELD_FROBENIUS_ELEMENT»
  NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q := SessionANT.PrimeSplit.«NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_INTERMEDIATE_FROBENIUS_ORDER := SessionANT.DecompositionField.«NUMBER_FIELD_INTERMEDIATE_FROBENIUS_ORDER»
  NUMBER_FIELD_PRIME_DECOMPOSITION_Q := SessionANT.SplittingTypes.«NUMBER_FIELD_PRIME_DECOMPOSITION_Q»
  NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE := SessionANT.DecompositionField.«NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE»
  NUMBER_FIELD_SUBFIELD_GENERATED := SessionANT.RelativeSplit.«NUMBER_FIELD_SUBFIELD_GENERATED»
  NUMBER_FIELD_SUBFIELD_PRIME_IDEALS_ABOVE := SessionANT.DecompositionField.«NUMBER_FIELD_SUBFIELD_PRIME_IDEALS_ABOVE»
  NUMBER_FIELD_TOWER_LAW := SessionANT.RelativeSplit.«NUMBER_FIELD_TOWER_LAW»
  NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_Q := SessionANT.SplittingTypes.«NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_Q»
  NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP := SessionANT.NfDecomposition.«NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP»
  PRIME_COPRIME_EQ := SessionLibrary.Prime.«PRIME_COPRIME_EQ»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRIME_SUBFIELD_MINIMAL := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_MINIMAL»
  PRIME_SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_SUBFIELD_GENERATED»
  RAMIFICATION_INDEX_PRIME_SUBFIELD := SessionANT.RelativeSplit.«RAMIFICATION_INDEX_PRIME_SUBFIELD»
  RESIDUE_DEGREE_PRIME_SUBFIELD := SessionANT.RelativeSplit.«RESIDUE_DEGREE_PRIME_SUBFIELD»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL := SessionANT.RelativeSplit.«RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_OF_NUM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_NUM_SUBFIELD_GENERATED»
  RING_POW_EQ_GEN := SessionLibrary.RingTheory.«RING_POW_EQ_GEN»
  SPLITTING_TYPES_INTEGER_RING := SessionANT.SplittingTypes.«SPLITTING_TYPES_INTEGER_RING»
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED»
  SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_SUBFIELD_GENERATED»
  SUBGROUP_OF_HOMOMORPHIC_PREIMAGE := SessionLibrary.GroupTheory.«SUBGROUP_OF_HOMOMORPHIC_PREIMAGE»
  SUBGROUP_OF_IMP_SUBSET := SessionLibrary.GroupTheory.«SUBGROUP_OF_IMP_SUBSET»
  SUBSET := Session.SUBSET
  group_homomorphism := SessionLibrary.GroupTheory.«group_homomorphism»
  number_field := SessionANT.Numfield.«number_field»
  subgroup_of := SessionLibrary.GroupTheory.«subgroup_of»

/-- What cyclotomic_subfield_split.ml uses from Session. -/
def deps : HolANT.CyclotomicSubfieldSplit.CyclotomicSubfieldSplitDeps where
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

/- The bundles, in cyclotomic_subfield_split.ml order. -/
initialize BCyclotomicSubfieldSplit : HolANT.CyclotomicSubfieldSplit.CyclotomicSubfieldSplit ←
  ioB "setupCyclotomicSubfieldSplit" (HolANT.CyclotomicSubfieldSplit.setupCyclotomicSubfieldSplit deps).run

-- CyclotomicSubfieldSplit
def CYCLOTOMIC_SUBFIELD_RESIDUE_DEGREE : thm := BCyclotomicSubfieldSplit.CYCLOTOMIC_SUBFIELD_RESIDUE_DEGREE
def CYCLOTOMIC_SUBFIELD_PRIME_DECOMPOSITION : thm := BCyclotomicSubfieldSplit.CYCLOTOMIC_SUBFIELD_PRIME_DECOMPOSITION
def CYCLOTOMIC_SUBFIELD_SPLITTING_TYPES : thm := BCyclotomicSubfieldSplit.CYCLOTOMIC_SUBFIELD_SPLITTING_TYPES
def CYCLOTOMIC_FIXED_FIELD_PRIME_DECOMPOSITION : thm := BCyclotomicSubfieldSplit.CYCLOTOMIC_FIXED_FIELD_PRIME_DECOMPOSITION
def CYCLOTOMIC_FIXED_FIELD_TOTALLY_SPLIT : thm := BCyclotomicSubfieldSplit.CYCLOTOMIC_FIXED_FIELD_TOTALLY_SPLIT

/-- `needs "ANT/cyclotomic_subfield_split.ml"`: already done by importing this module. -/
def ensureCyclotomicSubfieldSplit : IO Unit := pure ()

end SessionANT.CyclotomicSubfieldSplit
