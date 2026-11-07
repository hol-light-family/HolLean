/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/modmulgroup.ml.                       -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/ModmulGroup.lean

  The session half of the modmul_group.ml translation: it supplies
  HolLibrary.ModmulGroup's dependencies from Session, SessionLibrary.GroupTheory
  and SessionLibrary.Primitive, and exports every name under its HOL Light
  name.  Importing this module is `needs "Library/modmul_group.ml"`; its
  `needs` of grouptheory.ml and primitive.ml are the imports of those
  modules.  The bundles are built by `initialize` when the module is loaded,
  in file order.
-/

import Session
import HolLibrary.ModmulGroup
import SessionLibrary.GroupTheory
import SessionLibrary.Primitive

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.ModmulGroup

/-- The core theorems modmul_group.ml uses. -/
def core1 : HolLibrary.ModmulGroup.CoreThms1 where
  AND_FORALL_THM := Session.AND_FORALL_THM
  ARITH := Session.ARITH
  CARD_CROSS := Session.CARD_CROSS
  CARD_SING := Session.CARD_SING
  CONG := Session.CONG
  CONG_IMP_EQ := SessionLibrary.Pocklington.«CONG_IMP_EQ»
  CONG_LMOD := Session.CONG_LMOD
  CONG_REFL := SessionLibrary.Pocklington.«CONG_REFL»
  CONJ_SYM := Session.CONJ_SYM
  COPRIME_0 := SessionLibrary.Prime.«COPRIME_0»
  COPRIME_LMOD := Session.COPRIME_LMOD
  COPRIME_LMUL := SessionLibrary.Prime.«COPRIME_LMUL»
  COPRIME_REFL := SessionLibrary.Prime.«COPRIME_REFL»
  COPRIME_RMUL := SessionLibrary.Prime.«COPRIME_RMUL»
  COPRIME_SYM := SessionLibrary.Prime.«COPRIME_SYM»
  CYCLIC_GROUP_ELEMENT_ORDER := SessionLibrary.GroupTheory.«CYCLIC_GROUP_ELEMENT_ORDER»
  EQ_SYM_EQ := Session.EQ_SYM_EQ
  EXP := Session.EXP
  EXP_ONE := Session.EXP_ONE
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_PROD_GROUP := SessionLibrary.GroupTheory.«FINITE_PROD_GROUP»
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FUN_EQ_THM := Session.FUN_EQ_THM
  GROUP_ELEMENT_ORDER_UNIQUE := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_UNIQUE»
  GROUP_HOMOMORPHISM := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM»
  GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE»
  HAS_SIZE := Session.HAS_SIZE
  INVERSE_MOD_BOUND := SessionLibrary.Pocklington.«INVERSE_MOD_BOUND»
  INVERSE_MOD_LMUL_EQ := SessionLibrary.Pocklington.«INVERSE_MOD_LMUL_EQ»
  INVERSE_MOD_RMUL_EQ := SessionLibrary.Pocklington.«INVERSE_MOD_RMUL_EQ»
  IN_CROSS := Session.IN_CROSS
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_NUMSEG := Session.IN_NUMSEG
  IN_SING := Session.IN_SING
  ISOMORPHIC_GROUP_SYM := SessionLibrary.GroupTheory.«ISOMORPHIC_GROUP_SYM»
  ISOMORPHIC_PROD_TRIVIAL_GROUP := SessionLibrary.GroupTheory.«ISOMORPHIC_PROD_TRIVIAL_GROUP»
  ISOMORPHIC_TRIVIAL_GROUPS := SessionLibrary.GroupTheory.«ISOMORPHIC_TRIVIAL_GROUPS»
  LE_0 := Session.LE_0
  LE_MULT2 := Session.LE_MULT2
  LE_REFL := Session.LE_REFL
  MOD_EXP_MOD := Session.MOD_EXP_MOD
  MOD_LT := Session.MOD_LT
  MOD_LT_EQ := Session.MOD_LT_EQ
  MOD_MOD := Session.MOD_MOD
  MOD_MOD_REFL := Session.MOD_MOD_REFL
  MOD_MULT_MOD2 := Session.MOD_MULT_MOD2
  MOD_UNIQUE := SessionLibrary.Pocklington.«MOD_UNIQUE»
  MULT_ASSOC := Session.MULT_ASSOC
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_EQ_1 := Session.MULT_EQ_1
  MULT_SYM := Session.MULT_SYM
  NOT_IMP := Session.NOT_IMP
  NOT_LE := Session.NOT_LE
  ORDER_CONG := SessionLibrary.Pocklington.«ORDER_CONG»
  ORDER_DIVIDES := SessionLibrary.Pocklington.«ORDER_DIVIDES»
  ORDER_EQ_0 := SessionLibrary.Pocklington.«ORDER_EQ_0»
  PAIR_EQ := Session.PAIR_EQ
  PHI_1 := SessionLibrary.Pocklington.«PHI_1»
  PHI_2 := SessionLibrary.Pocklington.«PHI_2»
  PHI_ALT := SessionLibrary.Pocklington.«PHI_ALT»
  PHI_EQ_0 := SessionLibrary.Pocklington.«PHI_EQ_0»
  PHI_LOWERBOUND_2 := SessionLibrary.Pocklington.«PHI_LOWERBOUND_2»
  PHI_MULTIPLICATIVE := SessionLibrary.Pocklington.«PHI_MULTIPLICATIVE»
  PRIMITIVE_ROOT_EXISTS := SessionLibrary.Primitive.«PRIMITIVE_ROOT_EXISTS»
  PROD_GROUP := SessionLibrary.GroupTheory.«PROD_GROUP»
  SINGLETON_GROUP := SessionLibrary.GroupTheory.«SINGLETON_GROUP»
/-- The core theorems modmul_group.ml uses. -/
def core2 : HolLibrary.ModmulGroup.CoreThms2 where
  SUBSET := Session.SUBSET
  TRIVIAL_GROUP_HAS_SIZE_1 := SessionLibrary.GroupTheory.«TRIVIAL_GROUP_HAS_SIZE_1»
  TRIVIAL_IMP_CYCLIC_GROUP := SessionLibrary.GroupTheory.«TRIVIAL_IMP_CYCLIC_GROUP»
  TRIVIAL_PROD_GROUP := SessionLibrary.GroupTheory.«TRIVIAL_PROD_GROUP»
  abelian_group := SessionLibrary.GroupTheory.«abelian_group»
  group_carrier := SessionLibrary.GroupTheory.«group_carrier»
  group_id := SessionLibrary.GroupTheory.«group_id»
  group_inv := SessionLibrary.GroupTheory.«group_inv»
  group_monomorphism := SessionLibrary.GroupTheory.«group_monomorphism»
  group_mul := SessionLibrary.GroupTheory.«group_mul»
  group_pow := SessionLibrary.GroupTheory.«group_pow»
  group_tybij := SessionLibrary.GroupTheory.«group_tybij»
  inverse_mod := SessionLibrary.Pocklington.«inverse_mod»
  isomorphic_group := SessionLibrary.GroupTheory.«isomorphic_group»
/-- The core theorems modmul_group.ml uses. -/
def core3 : HolLibrary.ModmulGroup.CoreThms3 where
/-- The core theorems modmul_group.ml uses. -/
def core4 : HolLibrary.ModmulGroup.CoreThms4 where

/-- What modmulgroup.ml uses from Session. -/
def deps : HolLibrary.ModmulGroup.ModmulGroupDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  NUMBER_RULE t := ExceptT.mk (Session.NUMBER_RULE t)
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  core1 := core1
  core2 := core2
  core3 := core3
  core4 := core4

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in modmul_group.ml order. -/
initialize BGen : HolLibrary.ModmulGroup.Gen ←
  ioB "setupGen" (HolLibrary.ModmulGroup.setupGen deps).run
initialize BModmul : HolLibrary.ModmulGroup.Modmul ←
  ioB "setupModmul" (HolLibrary.ModmulGroup.setupModmul deps).run
initialize BCrt : HolLibrary.ModmulGroup.Crt ←
  ioB "setupCrt" (HolLibrary.ModmulGroup.setupCrt deps BGen BModmul).run
initialize BPrimroot : HolLibrary.ModmulGroup.Primroot ←
  ioB "setupPrimroot" (HolLibrary.ModmulGroup.setupPrimroot deps BModmul BCrt).run

-- Gen
def MULT_EQ_2 : thm := BGen.MULT_EQ_2

-- Modmul
def modmul_group : thm := BModmul.modmul_group
def MODMUL_GROUP : thm := BModmul.MODMUL_GROUP
def FINITE_MODMUL_GROUP : thm := BModmul.FINITE_MODMUL_GROUP
def ORDER_MODMUL_GROUP : thm := BModmul.ORDER_MODMUL_GROUP
def HAS_SIZE_MODMUL_GROUP : thm := BModmul.HAS_SIZE_MODMUL_GROUP
def ABELIAN_MODMUL_GROUP : thm := BModmul.ABELIAN_MODMUL_GROUP
def TRIVIAL_MODMUL_GROUP : thm := BModmul.TRIVIAL_MODMUL_GROUP

-- Crt
def GROUP_HOMOMORPHISM_PROD_MODMUL_GROUP : thm := BCrt.GROUP_HOMOMORPHISM_PROD_MODMUL_GROUP
def GROUP_ISOMORPHISM_PROD_MODMUL_GROUP : thm := BCrt.GROUP_ISOMORPHISM_PROD_MODMUL_GROUP
def ISOMORPHIC_GROUP_MODMUL_GROUP : thm := BCrt.ISOMORPHIC_GROUP_MODMUL_GROUP
def GROUP_POW_MODMUL_GROUP : thm := BCrt.GROUP_POW_MODMUL_GROUP
def GROUP_ELEMENT_ORDER_MODMUL_GROUP : thm := BCrt.GROUP_ELEMENT_ORDER_MODMUL_GROUP

-- Primroot
def CYCLIC_MODMUL_GROUP : thm := BPrimroot.CYCLIC_MODMUL_GROUP
/-- `needs "Library/modmul_group.ml"`: already done by importing this module. -/
def ensureModmulGroup : IO Unit := pure ()

end SessionLibrary.ModmulGroup
