/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/cyclotomic.ml.                              -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Cyclotomic.lean

  The session half of the cyclotomic.ml translation: it supplies
  HolLibrary.Cyclotomic's dependencies from Session, SessionLibrary.Galois
  and SessionLibrary.ModmulGroup, and exports every name under its HOL Light
  name.  Importing this module is `needs "Library/cyclotomic.ml"`; its
  `needs` of galois.ml and modmul_group.ml are the imports of those
  modules.  The bundle is built by `initialize` when the module is loaded.
-/

import Session
import HolLibrary.Cyclotomic
import SessionLibrary.Galois
import SessionLibrary.ModmulGroup

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Cyclotomic

/-- The core theorems cyclotomic.ml uses. -/
def core1 : HolLibrary.Cyclotomic.CoreThms1 where
  COPRIME_LMOD := Session.COPRIME_LMOD
  CYCLOTOMIC_EXTENSION_ABELIAN := SessionLibrary.Galois.«CYCLOTOMIC_EXTENSION_ABELIAN»
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FINITE_GALOIS_GROUP := SessionLibrary.Galois.«FINITE_GALOIS_GROUP»
  FINITE_MODMUL_GROUP := SessionLibrary.ModmulGroup.«FINITE_MODMUL_GROUP»
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  GALOIS_EXTENSION_EQ_CARD := SessionLibrary.Galois.«GALOIS_EXTENSION_EQ_CARD»
  GALOIS_GROUP := SessionLibrary.Galois.«GALOIS_GROUP»
  GALOIS_GROUP_COMPOSE := SessionLibrary.Galois.«GALOIS_GROUP_COMPOSE»
  GALOIS_GROUP_EQ_ON_GENERATORS := SessionLibrary.Galois.«GALOIS_GROUP_EQ_ON_GENERATORS»
  GALOIS_GROUP_INVERSE := SessionLibrary.Galois.«GALOIS_GROUP_INVERSE»
  GALOIS_GROUP_PERMUTES := SessionLibrary.Galois.«GALOIS_GROUP_PERMUTES»
  GALOIS_GROUP_RING_HOMOMORPHISM := SessionLibrary.Galois.«GALOIS_GROUP_RING_HOMOMORPHISM»
  GROUP_HOMOMORPHISM := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM»
  GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE»
  GROUP_ISOMORPHISM_IMP_ISOMORPHIC := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISM_IMP_ISOMORPHIC»
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_MODMUL_GROUP := SessionLibrary.ModmulGroup.«HAS_SIZE_MODMUL_GROUP»
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_SING := Session.IN_SING
  ISOMORPHIC_GROUP_ORDER := SessionLibrary.GroupTheory.«ISOMORPHIC_GROUP_ORDER»
  MODMUL_GROUP := SessionLibrary.ModmulGroup.«MODMUL_GROUP»
  MOD_LT_EQ := Session.MOD_LT_EQ
  MONO_EXISTS := Session.MONO_EXISTS
  PERMUTES_INVERSES := SessionLibrary.Permutations.«PERMUTES_INVERSES»
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ENDOMORPHISM_ROOT_OF_UNITY := SessionLibrary.RingTheory.«RING_ENDOMORPHISM_ROOT_OF_UNITY»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_ORDER_EQ_1 := SessionLibrary.RingTheory.«RING_ORDER_EQ_1»
  RING_POW_1 := SessionLibrary.RingTheory.«RING_POW_1»
  RING_POW_EQ_1 := SessionLibrary.RingTheory.«RING_POW_EQ_1»
  RING_POW_EQ_GEN := SessionLibrary.RingTheory.«RING_POW_EQ_GEN»
  RING_POW_EQ_LT := SessionLibrary.RingTheory.«RING_POW_EQ_LT»
  RING_POW_MOD_ORDER := SessionLibrary.RingTheory.«RING_POW_MOD_ORDER»
  RING_POW_POW := SessionLibrary.RingTheory.«RING_POW_POW»
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  group_monomorphism := SessionLibrary.GroupTheory.«group_monomorphism»
  o_THM := Session.o_THM
  ring_endomorphism := SessionLibrary.RingTheory.«ring_endomorphism»

/-- What cyclotomic.ml uses from Session. -/
def deps : HolLibrary.Cyclotomic.CyclotomicDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  TAUT t := ExceptT.mk (Session.TAUT t)
  INDUCT_TAC := Session.INDUCT_TAC
  RING_RULE t := ExceptT.mk (SessionLibrary.RingTheory.RING_RULE t)
  FIELD_TAC := SessionLibrary.RingTheory.FIELD_TAC
  GROUP_TAC := SessionLibrary.GroupTheory.GROUP_TAC
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  HAS_SIZE_CONV := Session.HAS_SIZE_CONV
  EXPAND_CASES_CONV := Session.EXPAND_CASES_CONV
  DIVIDES_CONV := SessionLibrary.Prime.DIVIDES_CONV
  prioritize_num := do
    match ← HolCore.Kernel.mk_type "num" [] with
    | .ok ty => Session.prioritize_overload ty
    | .error e => throw (IO.userError e)
  NUMBER_RULE := Session.NUMBER_RULE
  num_CONV := Session.num_CONV
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in cyclotomic.ml order. -/
initialize BCyclotomicGalois : HolLibrary.Cyclotomic.CyclotomicGalois ←
  ioB "setupCyclotomicGalois" (HolLibrary.Cyclotomic.setupCyclotomicGalois deps).run

-- CyclotomicGalois
def CYCLOTOMIC_GALOIS_GROUP_MODMUL : thm := BCyclotomicGalois.CYCLOTOMIC_GALOIS_GROUP_MODMUL
def CYCLOTOMIC_GALOIS_GROUP_MODMUL_ISOMORPHISM : thm := BCyclotomicGalois.CYCLOTOMIC_GALOIS_GROUP_MODMUL_ISOMORPHISM
/-- `needs "Library/cyclotomic.ml"`: already done by importing this module. -/
def ensureCyclotomic : IO Unit := pure ()

end SessionLibrary.Cyclotomic
