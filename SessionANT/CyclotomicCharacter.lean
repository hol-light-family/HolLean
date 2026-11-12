/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/cyclotomic_character.ml                       . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/CyclotomicCharacter.lean

  The session half of the cyclotomic_character.ml translation: it supplies HolANT.CyclotomicCharacter's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/cyclotomic_character.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.CyclotomicCharacter
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
import SessionLibrary.RingGroups
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionLibrary.Integer
import SessionLibrary.Isum
import SessionLibrary.Products
import SessionLibrary.Multiplicative
import SessionLibrary.Primitive
import SessionLibrary.ModmulGroup
import SessionLibrary.Cyclotomic
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.IdealArith
import SessionANT.Dedekind
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
import SessionLibrary.FiniteFields
import SessionANT.CyclotomicPoly
import SessionANT.PowerBasis
import SessionANT.CyclotomicField
import SessionANT.CyclotomicGalois
import SessionMultiLib.Misc
import SessionMultiLib.Metric

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.CyclotomicCharacter

/-- The core theorems cyclotomic_character.ml uses. -/
def core1 : HolANT.CyclotomicCharacter.CoreThms1 where
  ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD := SessionLibrary.FieldTheory.«ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD»
  ALGEBRAICALLY_CLOSED_FIELD_PRIMITIVE_ROOT_OF_UNITY := SessionLibrary.FieldTheory.«ALGEBRAICALLY_CLOSED_FIELD_PRIMITIVE_ROOT_OF_UNITY»
  ALGEBRAICALLY_CLOSED_IMP_NORMAL_EXTENSION := SessionLibrary.FieldTheory.«ALGEBRAICALLY_CLOSED_IMP_NORMAL_EXTENSION»
  CONG := Session.CONG
  CONG_IMP_EQ := SessionLibrary.Pocklington.«CONG_IMP_EQ»
  CONTINUOUS_MAP_INTO_DISCRETE_TOPOLOGY_FIBRES := SessionMultiLib.Metric.«CONTINUOUS_MAP_INTO_DISCRETE_TOPOLOGY_FIBRES»
  COPRIME_LMOD := Session.COPRIME_LMOD
  CYCLOTOMIC_EXTENSION_ABELIAN := SessionLibrary.Galois.«CYCLOTOMIC_EXTENSION_ABELIAN»
  CYCLOTOMIC_FIELD_DEGREE := SessionANT.CyclotomicField.«CYCLOTOMIC_FIELD_DEGREE»
  CYCLOTOMIC_GALOIS_GROUP_MODMUL := SessionLibrary.Cyclotomic.«CYCLOTOMIC_GALOIS_GROUP_MODMUL»
  CYCLOTOMIC_GALOIS_GROUP_MODMUL_ISOMORPHISM := SessionLibrary.Cyclotomic.«CYCLOTOMIC_GALOIS_GROUP_MODMUL_ISOMORPHISM»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  DIV_MULT := Session.DIV_MULT
  EQ_TRANS := Session.EQ_TRANS
  EXTENSION := Session.EXTENSION
  FIELD_EXTENSION_INTO_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_INTO_SUBFIELD_GENERATED»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_SING := Session.FINITE_SING
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  GALOIS_GROUP := SessionLibrary.Galois.«GALOIS_GROUP»
  GALOIS_GROUP_COMPOSE := SessionLibrary.Galois.«GALOIS_GROUP_COMPOSE»
  GALOIS_GROUP_RESTRICTION := SessionLibrary.Galois.«GALOIS_GROUP_RESTRICTION»
  GALOIS_GROUP_RING_AUTOMORPHISM := SessionLibrary.Galois.«GALOIS_GROUP_RING_AUTOMORPHISM»
  GALOIS_GROUP_RING_HOMOMORPHISM := SessionLibrary.Galois.«GALOIS_GROUP_RING_HOMOMORPHISM»
  GALOIS_IMP_NORMAL_EXTENSION := SessionLibrary.Galois.«GALOIS_IMP_NORMAL_EXTENSION»
  GROUP_EPIMORPHISM_ALT := SessionLibrary.GroupTheory.«GROUP_EPIMORPHISM_ALT»
  GROUP_HOMOMORPHISM := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM»
  GROUP_ID := SessionLibrary.GroupTheory.«GROUP_ID»
  GROUP_ISOMORPHISM := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISM»
  GROUP_ISOMORPHISM_MODMUL_UNIT_GROUP := SessionANT.CyclotomicGalois.«GROUP_ISOMORPHISM_MODMUL_UNIT_GROUP»
  GROUP_MONOMORPHISM_EPIMORPHISM := SessionLibrary.GroupTheory.«GROUP_MONOMORPHISM_EPIMORPHISM»
  GROUP_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.GroupTheory.«GROUP_MONOMORPHISM_IMP_HOMOMORPHISM»
  GROUP_MUL := SessionLibrary.GroupTheory.«GROUP_MUL»
  INTEGER_MOD_RING := SessionLibrary.RingTheory.«INTEGER_MOD_RING»
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  INT_OF_NUM_REM := Session.INT_OF_NUM_REM
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_GALOIS_GROUP := SessionLibrary.Galois.«IN_GALOIS_GROUP»
  IN_GALOIS_GROUP_SUBFIELD_GENERATED := SessionLibrary.Galois.«IN_GALOIS_GROUP_SUBFIELD_GENERATED»
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_SING := Session.IN_SING
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  MODMUL_GROUP := SessionLibrary.ModmulGroup.«MODMUL_GROUP»
  MOD_LT := Session.MOD_LT
  MOD_LT_EQ := Session.MOD_LT_EQ
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_SYM := Session.MULT_SYM
  NORMAL_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«NORMAL_IMP_FIELD_EXTENSION»
  NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC := SessionANT.Numfield.«NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC»
  NUM_OF_INT_OF_NUM := Session.NUM_OF_INT_OF_NUM
  OPEN_IN_POINTWISE_TOPOLOGY_POINT := SessionMultiLib.Metric.«OPEN_IN_POINTWISE_TOPOLOGY_POINT»
  PRIME_SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_SUBFIELD_GENERATED»
  RING_ENDOMORPHISM_ROOT_OF_UNITY := SessionLibrary.RingTheory.«RING_ENDOMORPHISM_ROOT_OF_UNITY»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_OF_INTEGERS_ALGEBRAIC := SessionANT.Numfield.«RING_OF_INTEGERS_ALGEBRAIC»
  RING_ORDER_POW := SessionLibrary.RingTheory.«RING_ORDER_POW»
  RING_ORDER_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_ORDER_SUBFIELD_GENERATED»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_1 := SessionLibrary.RingTheory.«RING_POW_1»
  RING_POW_EQ_GEN := SessionLibrary.RingTheory.«RING_POW_EQ_GEN»
  RING_POW_MOD_ORDER := SessionLibrary.RingTheory.«RING_POW_MOD_ORDER»
  RING_POW_ONE := SessionLibrary.RingTheory.«RING_POW_ONE»
  RING_POW_POW := SessionLibrary.RingTheory.«RING_POW_POW»
  RING_POW_RING_ORDER := SessionLibrary.RingTheory.«RING_POW_RING_ORDER»
  RING_POW_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_POW_SUBFIELD_GENERATED»
  ROOTS_OF_UNITY_RING_ORDER := SessionLibrary.RingTheory.«ROOTS_OF_UNITY_RING_ORDER»
  ROOT_OF_UNITY_IN_RING_OF_INTEGERS := SessionANT.Numfield.«ROOT_OF_UNITY_IN_RING_OF_INTEGERS»
  SING_SUBSET := Session.SING_SUBSET
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED»
  SUBFIELD_GENERATED_IDEMPOT_GEN := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_IDEMPOT_GEN»
  SUBFIELD_GENERATED_INC_GEN := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_INC_GEN»
  SUBFIELD_GENERATED_INSERT_PRIME_SUBFIELD := SessionANT.CyclotomicGalois.«SUBFIELD_GENERATED_INSERT_PRIME_SUBFIELD»
  SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_SUBFIELD_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  TOPSPACE_POINTWISE_TOPOLOGY := SessionMultiLib.Metric.«TOPSPACE_POINTWISE_TOPOLOGY»
  UNIT_GROUP := SessionLibrary.RingGroups.«UNIT_GROUP»
  UNIT_GROUP_INTEGER_MOD_RING := SessionANT.CyclotomicGalois.«UNIT_GROUP_INTEGER_MOD_RING»
  divides := Session.divides
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  group_epimorphism := SessionLibrary.GroupTheory.«group_epimorphism»
  group_homomorphism := SessionLibrary.GroupTheory.«group_homomorphism»
  group_image := SessionLibrary.GroupTheory.«group_image»
  group_kernel := SessionLibrary.GroupTheory.«group_kernel»
  group_monomorphism := SessionLibrary.GroupTheory.«group_monomorphism»
  o_THM := Session.o_THM
  ring_automorphism := SessionLibrary.RingTheory.«ring_automorphism»
  ring_endomorphism := SessionLibrary.RingTheory.«ring_endomorphism»
  ring_isomorphism := SessionLibrary.RingTheory.«ring_isomorphism»
  ring_isomorphisms := SessionLibrary.RingTheory.«ring_isomorphisms»

/-- What cyclotomic_character.ml uses from Session. -/
def deps : HolANT.CyclotomicCharacter.CyclotomicCharacterDeps where
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
  MOD_DOWN_CONV := Session.MOD_DOWN_CONV
  SELECT_CONV t := pure (Session.SELECT_CONV t)
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in cyclotomic_character.ml order. -/
initialize BCyclotomicCharacter : HolANT.CyclotomicCharacter.CyclotomicCharacter ←
  ioB "setupCyclotomicCharacter" (HolANT.CyclotomicCharacter.setupCyclotomicCharacter deps).run

-- CyclotomicCharacter
def cyclotomic_character : thm := BCyclotomicCharacter.cyclotomic_character
def CYCLOTOMIC_CHARACTER : thm := BCyclotomicCharacter.CYCLOTOMIC_CHARACTER
def CYCLOTOMIC_CHARACTER_UNIQUE : thm := BCyclotomicCharacter.CYCLOTOMIC_CHARACTER_UNIQUE
def CYCLOTOMIC_CHARACTER_DIVIDES : thm := BCyclotomicCharacter.CYCLOTOMIC_CHARACTER_DIVIDES
def CYCLOTOMIC_CHARACTER_HOMOMORPHISM : thm := BCyclotomicCharacter.CYCLOTOMIC_CHARACTER_HOMOMORPHISM
def CYCLOTOMIC_CHARACTER_KERNEL : thm := BCyclotomicCharacter.CYCLOTOMIC_CHARACTER_KERNEL
def CYCLOTOMIC_CHARACTER_CONTINUOUS : thm := BCyclotomicCharacter.CYCLOTOMIC_CHARACTER_CONTINUOUS
def CYCLOTOMIC_CHARACTER_EPIMORPHISM_EQ : thm := BCyclotomicCharacter.CYCLOTOMIC_CHARACTER_EPIMORPHISM_EQ
def CYCLOTOMIC_CHARACTER_EPIMORPHISM : thm := BCyclotomicCharacter.CYCLOTOMIC_CHARACTER_EPIMORPHISM
def ALGEBRAIC_CLOSURE_CYCLOTOMIC_CHARACTER : thm := BCyclotomicCharacter.ALGEBRAIC_CLOSURE_CYCLOTOMIC_CHARACTER

/-- `needs "ANT/cyclotomic_character.ml"`: already done by importing this module. -/
def ensureCyclotomicCharacter : IO Unit := pure ()

end SessionANT.CyclotomicCharacter
