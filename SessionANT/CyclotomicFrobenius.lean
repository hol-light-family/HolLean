/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/cyclotomic_frobenius.ml                       . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/CyclotomicFrobenius.lean

  The session half of the cyclotomic_frobenius.ml translation: it supplies HolANT.CyclotomicFrobenius's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/cyclotomic_frobenius.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.CyclotomicFrobenius
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
import SessionANT.CyclotomicGalois
import SessionANT.Decomposition
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.SplittingTypes
import SessionANT.NfDecomposition

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.CyclotomicFrobenius

/-- The core theorems cyclotomic_frobenius.ml uses. -/
def core1 : HolANT.CyclotomicFrobenius.CoreThms1 where
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  CYCLOTOMIC_FIELD_GALOIS_EXTENSION := SessionANT.CyclotomicGalois.«CYCLOTOMIC_FIELD_GALOIS_EXTENSION»
  CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ := SessionANT.CyclotomicGalois.«CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ»
  DECOMPOSITION_GROUP_RING_OF_INTEGERS := SessionANT.NfDecomposition.«DECOMPOSITION_GROUP_RING_OF_INTEGERS»
  EXTENSION := Session.EXTENSION
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FROBENIUS_ELEMENT := SessionANT.Decomposition.«FROBENIUS_ELEMENT»
  GALOIS_GROUP_I := SessionLibrary.Galois.«GALOIS_GROUP_I»
  GALOIS_GROUP_RING_HOMOMORPHISM := SessionLibrary.Galois.«GALOIS_GROUP_RING_HOMOMORPHISM»
  GALOIS_GROUP_RING_OF_INTEGERS := SessionANT.NfDecomposition.«GALOIS_GROUP_RING_OF_INTEGERS»
  IMAGE_I := Session.IMAGE_I
  INERTIA_GROUP := SessionANT.Decomposition.«INERTIA_GROUP»
  INTEGRAL_DOMAIN_RING_OF_INTEGERS := SessionANT.Numfield.«INTEGRAL_DOMAIN_RING_OF_INTEGERS»
  INT_CONG_IMP_EQ := SessionLibrary.Integer.«INT_CONG_IMP_EQ»
  INT_LT_REM := Session.INT_LT_REM
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_REM_DIV := Session.INT_REM_DIV
  INT_REM_POS := Session.INT_REM_POS
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INTER := Session.IN_INTER
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_SING := Session.IN_SING
  IN_UNIV := Session.IN_UNIV
  I_THM := Session.I_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LT_NZ := Session.LT_NZ
  MAXIMAL_IMP_PRIME_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PRIME_IDEAL»
  MAXIMAL_IMP_RING_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_RING_IDEAL»
  MULT_SYM := Session.MULT_SYM
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  PRIME_0 := SessionLibrary.Prime.«PRIME_0»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_PRIME_SUBFIELD := SessionANT.Numfield.«RING_OF_INTEGERS_PRIME_SUBFIELD»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_IN_PRIME_IDEAL := SessionANT.PrimeSplit.«RING_OF_INT_IN_PRIME_IDEAL»
  RING_OF_INT_IN_RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INT_IN_RING_OF_INTEGERS»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_INT_SUB := SessionLibrary.RingTheory.«RING_OF_INT_SUB»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_MUL := SessionLibrary.RingTheory.«RING_POW_MUL»
  RING_POW_ONE := SessionLibrary.RingTheory.«RING_POW_ONE»
  RING_POW_POW := SessionLibrary.RingTheory.«RING_POW_POW»
  RING_POW_RING_ORDER := SessionLibrary.RingTheory.«RING_POW_RING_ORDER»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  ROOTS_OF_UNITY_EQ_MOD_IDEAL := SessionLibrary.RingTheory.«ROOTS_OF_UNITY_EQ_MOD_IDEAL»
  ROOT_OF_UNITY_IN_RING_OF_INTEGERS := SessionANT.Numfield.«ROOT_OF_UNITY_IN_RING_OF_INTEGERS»
  SUBSET := Session.SUBSET
  int_congruent := Session.int_congruent
  int_divides := Session.int_divides
  num_divides := Session.num_divides
  number_field := SessionANT.Numfield.«number_field»

/-- What cyclotomic_frobenius.ml uses from Session. -/
def deps : HolANT.CyclotomicFrobenius.CyclotomicFrobeniusDeps where
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

/- The bundles, in cyclotomic_frobenius.ml order. -/
initialize BCyclotomicFrobenius : HolANT.CyclotomicFrobenius.CyclotomicFrobenius ←
  ioB "setupCyclotomicFrobenius" (HolANT.CyclotomicFrobenius.setupCyclotomicFrobenius deps).run

-- CyclotomicFrobenius
def NUMBER_FIELD_RESIDUE_PRIME_FIELD_CARD : thm := BCyclotomicFrobenius.NUMBER_FIELD_RESIDUE_PRIME_FIELD_CARD
def CYCLOTOMIC_FIELD_INERTIA_GROUP : thm := BCyclotomicFrobenius.CYCLOTOMIC_FIELD_INERTIA_GROUP
def CYCLOTOMIC_FIELD_FROBENIUS_ELEMENT : thm := BCyclotomicFrobenius.CYCLOTOMIC_FIELD_FROBENIUS_ELEMENT

/-- `needs "ANT/cyclotomic_frobenius.ml"`: already done by importing this module. -/
def ensureCyclotomicFrobenius : IO Unit := pure ()

end SessionANT.CyclotomicFrobenius
