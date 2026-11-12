/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/cyclotomic_galois.ml                          . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/CyclotomicGalois.lean

  The session half of the cyclotomic_galois.ml translation: it supplies HolANT.CyclotomicGalois's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/cyclotomic_galois.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.CyclotomicGalois
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
import SessionLibrary.Cyclotomic
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionLibrary.RingGroups
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.CyclotomicGalois

/-- The core theorems cyclotomic_galois.ml uses. -/
def core1 : HolANT.CyclotomicGalois.CoreThms1 where
  ABELIAN_UNIT_GROUP := SessionLibrary.RingGroups.«ABELIAN_UNIT_GROUP»
  COPRIME_1 := SessionLibrary.Prime.«COPRIME_1»
  COPRIME_LMOD := Session.COPRIME_LMOD
  CYCLOTOMIC_EXTENSION_ABELIAN := SessionLibrary.Galois.«CYCLOTOMIC_EXTENSION_ABELIAN»
  CYCLOTOMIC_FIELD_DEGREE := SessionANT.CyclotomicField.«CYCLOTOMIC_FIELD_DEGREE»
  CYCLOTOMIC_GALOIS_GROUP_MODMUL_ISOMORPHISM := SessionLibrary.Cyclotomic.«CYCLOTOMIC_GALOIS_GROUP_MODMUL_ISOMORPHISM»
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  EXTENSION := Session.EXTENSION
  FIELD_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED»
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  GALOIS_GROUP_EQ_ON_GENERATORS := SessionLibrary.Galois.«GALOIS_GROUP_EQ_ON_GENERATORS»
  GROUP_HOMOMORPHISM := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM»
  GROUP_ISOMORPHISM := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISM»
  GROUP_ISOMORPHISMS_SYM := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISMS_SYM»
  GROUP_ISOMORPHISM_COMPOSE := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISM_COMPOSE»
  GROUP_ISOMORPHISM_IMP_ISOMORPHIC := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISM_IMP_ISOMORPHIC»
  HAS_SIZE_MODMUL_GROUP := SessionLibrary.ModmulGroup.«HAS_SIZE_MODMUL_GROUP»
  IMAGE_I := Session.IMAGE_I
  INTEGER_MOD_RING_CLAUSES := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CLAUSES»
  INTEGER_MOD_RING_UNIT := SessionLibrary.RingTheory.«INTEGER_MOD_RING_UNIT»
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_OF_NUM_REM := Session.INT_OF_NUM_REM
  INT_POS := Session.INT_POS
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_INTEGER_MOD_RING_CARRIER := SessionLibrary.RingTheory.«IN_INTEGER_MOD_RING_CARRIER»
  IN_INTER := Session.IN_INTER
  IN_SING := Session.IN_SING
  IN_SUBFIELD_0 := SessionLibrary.FieldTheory.«IN_SUBFIELD_0»
  ISOMORPHIC_GROUP_ABELIANNESS := SessionLibrary.GroupTheory.«ISOMORPHIC_GROUP_ABELIANNESS»
  ISOMORPHIC_GROUP_HAS_ORDER := SessionLibrary.GroupTheory.«ISOMORPHIC_GROUP_HAS_ORDER»
  ISOMORPHIC_GROUP_SYM := SessionLibrary.GroupTheory.«ISOMORPHIC_GROUP_SYM»
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  MODMUL_GROUP := SessionLibrary.ModmulGroup.«MODMUL_GROUP»
  MOD_1 := Session.MOD_1
  MOD_LT := Session.MOD_LT
  MOD_LT_EQ := Session.MOD_LT_EQ
  MOD_MOD_REFL := Session.MOD_MOD_REFL
  MOD_MULT_MOD2 := Session.MOD_MULT_MOD2
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUM_OF_INT_OF_NUM := Session.NUM_OF_INT_OF_NUM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_POW_EQ_1 := SessionLibrary.RingTheory.«RING_POW_EQ_1»
  RING_POW_MOD_ORDER := SessionLibrary.RingTheory.«RING_POW_MOD_ORDER»
  SUBFIELDS_GENERATED_EQ := SessionLibrary.FieldTheory.«SUBFIELDS_GENERATED_EQ»
  SUBFIELD_GENERATED_INSERT := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_INSERT»
  SUBSET := Session.SUBSET
  SUBSET_REFL := Session.SUBSET_REFL
  UNIT_GROUP := SessionLibrary.RingGroups.«UNIT_GROUP»
  group_isomorphism := SessionLibrary.GroupTheory.«group_isomorphism»
  group_isomorphisms := SessionLibrary.GroupTheory.«group_isomorphisms»
  num_coprime := Session.num_coprime
  o_THM := Session.o_THM

/-- What cyclotomic_galois.ml uses from Session. -/
def deps : HolANT.CyclotomicGalois.CyclotomicGaloisDeps where
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

/- The bundles, in cyclotomic_galois.ml order. -/
initialize BCyclotomicGalois : HolANT.CyclotomicGalois.CyclotomicGalois ←
  ioB "setupCyclotomicGalois" (HolANT.CyclotomicGalois.setupCyclotomicGalois deps).run

-- CyclotomicGalois
def UNIT_GROUP_INTEGER_MOD_RING : thm := BCyclotomicGalois.UNIT_GROUP_INTEGER_MOD_RING
def GROUP_ISOMORPHISM_MODMUL_UNIT_GROUP : thm := BCyclotomicGalois.GROUP_ISOMORPHISM_MODMUL_UNIT_GROUP
def SUBFIELD_GENERATED_INSERT_PRIME_SUBFIELD : thm := BCyclotomicGalois.SUBFIELD_GENERATED_INSERT_PRIME_SUBFIELD
def CYCLOTOMIC_FIELD_GALOIS_EXTENSION : thm := BCyclotomicGalois.CYCLOTOMIC_FIELD_GALOIS_EXTENSION
def CYCLOTOMIC_FIELD_GALOIS_GROUP_MODMUL : thm := BCyclotomicGalois.CYCLOTOMIC_FIELD_GALOIS_GROUP_MODMUL
def CYCLOTOMIC_FIELD_GALOIS_GROUP_HAS_SIZE : thm := BCyclotomicGalois.CYCLOTOMIC_FIELD_GALOIS_GROUP_HAS_SIZE
def CYCLOTOMIC_FIELD_GALOIS_GROUP : thm := BCyclotomicGalois.CYCLOTOMIC_FIELD_GALOIS_GROUP
def CYCLOTOMIC_FIELD_GALOIS_GROUP_EXISTS : thm := BCyclotomicGalois.CYCLOTOMIC_FIELD_GALOIS_GROUP_EXISTS
def CYCLOTOMIC_FIELD_GALOIS_GROUP_ROOT : thm := BCyclotomicGalois.CYCLOTOMIC_FIELD_GALOIS_GROUP_ROOT
def CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ : thm := BCyclotomicGalois.CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ
def CYCLOTOMIC_FIELD_GALOIS_GROUP_ISOMORPHIC : thm := BCyclotomicGalois.CYCLOTOMIC_FIELD_GALOIS_GROUP_ISOMORPHIC
def CYCLOTOMIC_FIELD_GALOIS_GROUP_ABELIAN : thm := BCyclotomicGalois.CYCLOTOMIC_FIELD_GALOIS_GROUP_ABELIAN

/-- `needs "ANT/cyclotomic_galois.ml"`: already done by importing this module. -/
def ensureCyclotomicGalois : IO Unit := pure ()

end SessionANT.CyclotomicGalois
