/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/class_group_maps.ml                           . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/ClassGroupMaps.lean

  The session half of the class_group_maps.ml translation: it supplies HolANT.ClassGroupMaps's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/class_group_maps.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.ClassGroupMaps
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionLibrary.Matroids
import SessionLibrary.FieldTheory
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionANT.IdealArith
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.ClassgroupGroup
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.PrimeSplit
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.NfValuation
import SessionANT.Integrality
import SessionANT.RelativeDegree
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
import SessionANT.IdealNormExtension

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.ClassGroupMaps

/-- The core theorems class_group_maps.ml uses. -/
def core1 : HolANT.ClassGroupMaps.CoreThms1 where
  CARD_DIVIDES_GROUP_EPIMORPHIC_IMAGE := SessionLibrary.GroupTheory.«CARD_DIVIDES_GROUP_EPIMORPHIC_IMAGE»
  CLASS_GROUP := SessionANT.ClassgroupGroup.«CLASS_GROUP»
  CLASS_GROUP_HOMOMORPHISM_IDEAL_MAP := SessionANT.ClassgroupGroup.«CLASS_GROUP_HOMOMORPHISM_IDEAL_MAP»
  CLASS_GROUP_POW := SessionANT.ClassgroupGroup.«CLASS_GROUP_POW»
  CONG_DIVIDES_MODULUS := SessionLibrary.Pocklington.«CONG_DIVIDES_MODULUS»
  CONG_SOLVE := SessionLibrary.Pocklington.«CONG_SOLVE»
  CONG_SYM := SessionLibrary.Pocklington.«CONG_SYM»
  DEDEKIND_CLASS_GROUP_EXTENSION := SessionANT.ClassgroupGroup.«DEDEKIND_CLASS_GROUP_EXTENSION»
  DEDEKIND_PRINCIPAL_IDEAL_POW_COPRIME := SessionANT.ClassgroupGroup.«DEDEKIND_PRINCIPAL_IDEAL_POW_COPRIME»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  EQ_TRANS := Session.EQ_TRANS
  EXTENSION := Session.EXTENSION
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_RING_HOMOMORPHISM_MONOMORPHISM := SessionLibrary.RingTheory.«FIELD_RING_HOMOMORPHISM_MONOMORPHISM»
  FINITE_CLASS_GROUP := SessionANT.ClassgroupGroup.«FINITE_CLASS_GROUP»
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  GALOIS_IMP_FIELD_EXTENSION := SessionLibrary.Galois.«GALOIS_IMP_FIELD_EXTENSION»
  GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER»
  GROUP_HOMOMORPHISM_OF_ID := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM_OF_ID»
  GROUP_ID := SessionLibrary.GroupTheory.«GROUP_ID»
  GROUP_MONOMORPHISM := SessionLibrary.GroupTheory.«GROUP_MONOMORPHISM»
  GROUP_POW := SessionLibrary.GroupTheory.«GROUP_POW»
  GROUP_POW_1 := SessionLibrary.GroupTheory.«GROUP_POW_1»
  GROUP_POW_EQ := SessionLibrary.GroupTheory.«GROUP_POW_EQ»
  GROUP_POW_MUL := SessionLibrary.GroupTheory.«GROUP_POW_MUL»
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_CLASS_GROUP := SessionANT.ClassgroupGroup.«HAS_SIZE_CLASS_GROUP»
  IDEAL_CLASS_EQ_ID := SessionANT.ClassgroupGroup.«IDEAL_CLASS_EQ_ID»
  IDEAL_GENERATED_IMAGE_IDEAL_GENERATED := SessionANT.IdealArith.«IDEAL_GENERATED_IMAGE_IDEAL_GENERATED»
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMP_CONJ := Session.IMP_CONJ
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_SING := Session.IN_SING
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_SYM := Session.MULT_SYM
  NUMBER_FIELD_CLASS_GROUP_FINITE := SessionANT.Classgroup.«NUMBER_FIELD_CLASS_GROUP_FINITE»
  NUMBER_FIELD_GALOIS_PRODUCT_IDEAL_NORM := SessionANT.IdealNormExtension.«NUMBER_FIELD_GALOIS_PRODUCT_IDEAL_NORM»
  NUMBER_FIELD_HOMOMORPHIC_PREIMAGE := SessionANT.RelativeSplit.«NUMBER_FIELD_HOMOMORPHIC_PREIMAGE»
  NUMBER_FIELD_IDEAL_NORM_EQ_0 := SessionANT.IdealNormExtension.«NUMBER_FIELD_IDEAL_NORM_EQ_0»
  NUMBER_FIELD_IDEAL_NORM_EXTENSION := SessionANT.IdealNormExtension.«NUMBER_FIELD_IDEAL_NORM_EXTENSION»
  NUMBER_FIELD_IDEAL_NORM_IDEAL := SessionANT.IdealNormExtension.«NUMBER_FIELD_IDEAL_NORM_IDEAL»
  NUMBER_FIELD_IDEAL_NORM_MUL := SessionANT.IdealNormExtension.«NUMBER_FIELD_IDEAL_NORM_MUL»
  NUMBER_FIELD_IDEAL_NORM_PRINCIPAL := SessionANT.IdealNormExtension.«NUMBER_FIELD_IDEAL_NORM_PRINCIPAL»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_NORM_INTEGRAL := SessionANT.Integrality.«NUMBER_FIELD_NORM_INTEGRAL»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_HOMOMORPHISM_RING_OF_INTEGERS»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_MONOMORPHISM_RING_OF_INTEGERS»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_IDEAL_EXTENSION := SessionANT.RelativeSplit.«RING_OF_INTEGERS_IDEAL_EXTENSION»
  SING_SUBSET := Session.SING_SUBSET
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  class_number := SessionANT.Classgroup.«class_number»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  group_epimorphism := SessionLibrary.GroupTheory.«group_epimorphism»
  group_homomorphism := SessionLibrary.GroupTheory.«group_homomorphism»
  group_kernel := SessionLibrary.GroupTheory.«group_kernel»
  ideal_classes := SessionANT.Classgroup.«ideal_classes»
  principal_ideal := SessionLibrary.RingTheory.«principal_ideal»

/-- What class_group_maps.ml uses from Session. -/
def deps : HolANT.ClassGroupMaps.ClassGroupMapsDeps where
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

/- The bundles, in class_group_maps.ml order. -/
initialize BClassGroupMaps : HolANT.ClassGroupMaps.ClassGroupMaps ←
  ioB "setupClassGroupMaps" (HolANT.ClassGroupMaps.setupClassGroupMaps deps).run

-- ClassGroupMaps
def NUMBER_FIELD_CLASS_GROUP_EXTENSION : thm := BClassGroupMaps.NUMBER_FIELD_CLASS_GROUP_EXTENSION
def NUMBER_FIELD_CLASS_GROUP_NORM : thm := BClassGroupMaps.NUMBER_FIELD_CLASS_GROUP_NORM
def NUMBER_FIELD_CLASS_GROUP_NORM_EXTENSION : thm := BClassGroupMaps.NUMBER_FIELD_CLASS_GROUP_NORM_EXTENSION
def NUMBER_FIELD_CLASS_GROUP_EXTENSION_NORM_GALOIS : thm := BClassGroupMaps.NUMBER_FIELD_CLASS_GROUP_EXTENSION_NORM_GALOIS
def NUMBER_FIELD_IDEAL_EXTENSION_PRINCIPAL_POW : thm := BClassGroupMaps.NUMBER_FIELD_IDEAL_EXTENSION_PRINCIPAL_POW
def NUMBER_FIELD_IDEAL_EXTENSION_PRINCIPAL_COPRIME : thm := BClassGroupMaps.NUMBER_FIELD_IDEAL_EXTENSION_PRINCIPAL_COPRIME
def NUMBER_FIELD_CLASS_GROUP_EXTENSION_MONOMORPHISM : thm := BClassGroupMaps.NUMBER_FIELD_CLASS_GROUP_EXTENSION_MONOMORPHISM
def NUMBER_FIELD_CLASS_GROUP_NORM_EPIMORPHISM : thm := BClassGroupMaps.NUMBER_FIELD_CLASS_GROUP_NORM_EPIMORPHISM
def NUMBER_FIELD_CLASS_NUMBER_DIVIDES : thm := BClassGroupMaps.NUMBER_FIELD_CLASS_NUMBER_DIVIDES

/-- `needs "ANT/class_group_maps.ml"`: already done by importing this module. -/
def ensureClassGroupMaps : IO Unit := pure ()

end SessionANT.ClassGroupMaps
