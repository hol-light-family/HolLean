/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/ring_groups.ml.                             -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/RingGroups.lean

  The session half of the ring_groups.ml translation: it supplies
  HolLibrary.RingGroups's dependencies from Session, SessionLibrary.RingTheory
  and SessionLibrary.GroupTheory, and exports every name under its HOL Light
  name.  Importing this module is `needs "Library/ring_groups.ml"`; its
  `needs` of ringtheory.ml and grouptheory.ml are the imports of those
  modules.  The bundles are built by `initialize` when the module is loaded,
  in file order.
-/

import Session
import HolLibrary.RingGroups
import SessionLibrary.RingTheory
import SessionLibrary.GroupTheory

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.RingGroups

/-- The core theorems ring_groups.ml uses. -/
def core1 : HolLibrary.RingGroups.CoreThms1 where
  ABELIAN_GROUP_MUL_ZPOW := SessionLibrary.GroupTheory.«ABELIAN_GROUP_MUL_ZPOW»
  ABELIAN_GROUP_SUM_CLAUSES := SessionLibrary.GroupTheory.«ABELIAN_GROUP_SUM_CLAUSES»
  AND_FORALL_THM := Session.AND_FORALL_THM
  CARD_CROSS := Session.CARD_CROSS
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARRIER_SUBGROUP_GENERATED_SUBGROUP := SessionLibrary.GroupTheory.«CARRIER_SUBGROUP_GENERATED_SUBGROUP»
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_PAIR_THM := Session.EXISTS_PAIR_THM
  EXTENSION := Session.EXTENSION
  FIELD_REAL_RING := SessionLibrary.RingTheory.«FIELD_REAL_RING»
  FIELD_UNIT := SessionLibrary.RingTheory.«FIELD_UNIT»
  FINITELY_GENERATED_ABELIAN_GROUP_POW := SessionLibrary.GroupTheory.«FINITELY_GENERATED_ABELIAN_GROUP_POW»
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_INT_CASES := Session.FORALL_INT_CASES
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  GROUPS_EQ := SessionLibrary.GroupTheory.«GROUPS_EQ»
  GROUP_HOMOMORPHISM := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM»
  GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ»
  GROUP_HOMOMORPHISM_MUL := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM_MUL»
  GROUP_HOMOMORPHISM_OF_ID := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM_OF_ID»
  GROUP_ID := SessionLibrary.GroupTheory.«GROUP_ID»
  GROUP_INV := SessionLibrary.GroupTheory.«GROUP_INV»
  GROUP_ISOMORPHISM := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISM»
  GROUP_MUL := SessionLibrary.GroupTheory.«GROUP_MUL»
  GROUP_MUL_LID := SessionLibrary.GroupTheory.«GROUP_MUL_LID»
  GROUP_MUL_RINV := SessionLibrary.GroupTheory.«GROUP_MUL_RINV»
  GROUP_POW := SessionLibrary.GroupTheory.«GROUP_POW»
  GROUP_SUM := SessionLibrary.GroupTheory.«GROUP_SUM»
  GROUP_SUM_CLAUSES_EXISTS := SessionLibrary.GroupTheory.«GROUP_SUM_CLAUSES_EXISTS»
  GROUP_ZPOW := SessionLibrary.GroupTheory.«GROUP_ZPOW»
  GROUP_ZPOW_POW := SessionLibrary.GroupTheory.«GROUP_ZPOW_POW»
  IMAGE_I := Session.IMAGE_I
  IMAGE_ID := Session.IMAGE_ID
  IMP_CONJ := Session.IMP_CONJ
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  IN_CROSS := Session.IN_CROSS
  IN_DIFF := Session.IN_DIFF
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_SING := Session.IN_SING
  IN_SUBGROUP_POW := SessionLibrary.GroupTheory.«IN_SUBGROUP_POW»
  IN_SUBGROUP_SUM := SessionLibrary.GroupTheory.«IN_SUBGROUP_SUM»
  IN_UNIV := Session.IN_UNIV
  I_DEF := Session.I_DEF
  I_THM := Session.I_THM
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  PAIR_EQ := Session.PAIR_EQ
  PRODUCT_CLAUSES := Session.PRODUCT_CLAUSES
  PRODUCT_GROUP := SessionLibrary.GroupTheory.«PRODUCT_GROUP»
  PRODUCT_RING := SessionLibrary.RingTheory.«PRODUCT_RING»
  PROD_GROUP := SessionLibrary.GroupTheory.«PROD_GROUP»
  PROD_RING := SessionLibrary.RingTheory.«PROD_RING»
  REAL_LT_01 := Session.REAL_LT_01
  REAL_LT_IMP_NZ := Session.REAL_LT_IMP_NZ
  REAL_LT_INV := Session.REAL_LT_INV
  REAL_LT_MUL := Session.REAL_LT_MUL
  REAL_RING_CLAUSES := SessionLibrary.RingTheory.«REAL_RING_CLAUSES»
  REAL_RING_INV := SessionLibrary.RingTheory.«REAL_RING_INV»
  REAL_ZPOW_POW := Session.REAL_ZPOW_POW
  RESTRICTED_PRODUCT_GROUP := SessionLibrary.GroupTheory.«RESTRICTED_PRODUCT_GROUP»
  RESTRICTED_PRODUCT_RING := SessionLibrary.RingTheory.«RESTRICTED_PRODUCT_RING»
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_ASSOC := SessionLibrary.RingTheory.«RING_ADD_ASSOC»
  RING_ADD_LNEG := SessionLibrary.RingTheory.«RING_ADD_LNEG»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RNEG := SessionLibrary.RingTheory.«RING_ADD_RNEG»
/-- The core theorems ring_groups.ml uses. -/
def core2 : HolLibrary.RingGroups.CoreThms2 where
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_ADD_SYM := SessionLibrary.RingTheory.«RING_ADD_SYM»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_INCLUSION := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INCLUSION»
  RING_HOMOMORPHISM_INV := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INV»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_INV_1 := SessionLibrary.RingTheory.«RING_INV_1»
  RING_ISOMORPHISM_IMP_MONOMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISM_IMP_MONOMORPHISM»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_INJECTIVE_EQ := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INJECTIVE_EQ»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LINV := SessionLibrary.RingTheory.«RING_MUL_LINV»
  RING_MUL_LNEG := SessionLibrary.RingTheory.«RING_MUL_LNEG»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RINV := SessionLibrary.RingTheory.«RING_MUL_RINV»
  RING_MUL_RNEG := SessionLibrary.RingTheory.«RING_MUL_RNEG»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_NEG_NEG := SessionLibrary.RingTheory.«RING_NEG_NEG»
  RING_POW_NEG := SessionLibrary.RingTheory.«RING_POW_NEG»
  RING_POW_ONE := SessionLibrary.RingTheory.«RING_POW_ONE»
  RING_PRODUCT_CLAUSES := SessionLibrary.RingTheory.«RING_PRODUCT_CLAUSES»
  RING_RINV_UNIQUE := SessionLibrary.RingTheory.«RING_RINV_UNIQUE»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_0 := SessionLibrary.RingTheory.«RING_SUM_0»
  RING_SUM_CLAUSES := SessionLibrary.RingTheory.«RING_SUM_CLAUSES»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_EQ_0 := SessionLibrary.RingTheory.«RING_SUM_EQ_0»
  RING_SUM_LMUL := SessionLibrary.RingTheory.«RING_SUM_LMUL»
  RING_SUM_SUB := SessionLibrary.RingTheory.«RING_SUM_SUB»
  RING_UNIT_1 := SessionLibrary.RingTheory.«RING_UNIT_1»
  RING_UNIT_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_UNIT_HOMOMORPHIC_IMAGE»
  RING_UNIT_INV := SessionLibrary.RingTheory.«RING_UNIT_INV»
  RING_UNIT_IN_CARRIER := SessionLibrary.RingTheory.«RING_UNIT_IN_CARRIER»
  RING_UNIT_MUL := SessionLibrary.RingTheory.«RING_UNIT_MUL»
  RING_UNIT_NEG := SessionLibrary.RingTheory.«RING_UNIT_NEG»
  RING_UNIT_POW := SessionLibrary.RingTheory.«RING_UNIT_POW»
  RING_UNIT_PRODUCT_RING := SessionLibrary.RingTheory.«RING_UNIT_PRODUCT_RING»
  RING_UNIT_RESTRICTED_PRODUCT_RING := SessionLibrary.RingTheory.«RING_UNIT_RESTRICTED_PRODUCT_RING»
  RING_UNIT_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_UNIT_SUBRING_GENERATED»
  SUBGROUP_GENERATED_INC_GEN := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_INC_GEN»
  SUBGROUP_GENERATED_SUPERSET := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_SUPERSET»
  SUBGROUP_GROUP_IMAGE := SessionLibrary.GroupTheory.«SUBGROUP_GROUP_IMAGE»
  SUBGROUP_SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«SUBGROUP_SUBGROUP_GENERATED»
  SUBRING_RING_IMAGE := SessionLibrary.RingTheory.«SUBRING_RING_IMAGE»
  SUBSET := Session.SUBSET
  SUBSET_REFL := Session.SUBSET_REFL
  SWAP_FORALL_THM := Session.SWAP_FORALL_THM
  abelian_group := SessionLibrary.GroupTheory.«abelian_group»
  finitely_generated_group := SessionLibrary.GroupTheory.«finitely_generated_group»
  group_carrier := SessionLibrary.GroupTheory.«group_carrier»
  group_homomorphism := SessionLibrary.GroupTheory.«group_homomorphism»
  group_id := SessionLibrary.GroupTheory.«group_id»
  group_image := SessionLibrary.GroupTheory.«group_image»
  group_inv := SessionLibrary.GroupTheory.«group_inv»
  group_mul := SessionLibrary.GroupTheory.«group_mul»
  group_pow := SessionLibrary.GroupTheory.«group_pow»
  group_tybij := SessionLibrary.GroupTheory.«group_tybij»
  isomorphic_ring := SessionLibrary.RingTheory.«isomorphic_ring»
  real_pow := Session.real_pow
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_ideal := SessionLibrary.RingTheory.«ring_ideal»
  ring_image := SessionLibrary.RingTheory.«ring_image»
  ring_isomorphism := SessionLibrary.RingTheory.«ring_isomorphism»
  ring_isomorphisms := SessionLibrary.RingTheory.«ring_isomorphisms»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_unit := SessionLibrary.RingTheory.«ring_unit»
  subgroup_of := SessionLibrary.GroupTheory.«subgroup_of»
  subring_of := SessionLibrary.RingTheory.«subring_of»

/-- What ring_groups.ml uses from Session. -/
def deps : HolLibrary.RingGroups.RingGroupsDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  RING_RULE t := ExceptT.mk (SessionLibrary.RingTheory.RING_RULE t)
  REAL_FIELD t := ExceptT.mk (Session.REAL_FIELD t)
  TAUT t := ExceptT.mk (Session.TAUT t)
  core1 := core1
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in ring_groups.ml order. -/
initialize BAdditiveGroup : HolLibrary.RingGroups.AdditiveGroup ←
  ioB "setupAdditiveGroup" (HolLibrary.RingGroups.setupAdditiveGroup deps).run
initialize BUnitGroup : HolLibrary.RingGroups.UnitGroup ←
  ioB "setupUnitGroup" (HolLibrary.RingGroups.setupUnitGroup deps).run
initialize BUnitHomomorphisms : HolLibrary.RingGroups.UnitHomomorphisms ←
  ioB "setupUnitHomomorphisms" (HolLibrary.RingGroups.setupUnitHomomorphisms deps BUnitGroup).run
initialize BUnitsIndependent : HolLibrary.RingGroups.UnitsIndependent ←
  ioB "setupUnitsIndependent" (HolLibrary.RingGroups.setupUnitsIndependent deps BUnitGroup).run

-- AdditiveGroup
def ring_additive_group : thm := BAdditiveGroup.ring_additive_group
def RING_ADDITIVE_GROUP : thm := BAdditiveGroup.RING_ADDITIVE_GROUP
def ABELIAN_RING_ADDITIVE_GROUP : thm := BAdditiveGroup.ABELIAN_RING_ADDITIVE_GROUP
def GROUP_HOMOMORPHISM_RING_ADDITIVE_GROUP : thm := BAdditiveGroup.GROUP_HOMOMORPHISM_RING_ADDITIVE_GROUP
def GROUP_SUM_RING_ADDITIVE_GROUP : thm := BAdditiveGroup.GROUP_SUM_RING_ADDITIVE_GROUP
def RING_IDEAL_IMP_SUBGROUP : thm := BAdditiveGroup.RING_IDEAL_IMP_SUBGROUP
def SUBRING_IMP_SUBGROUP_ADDITIVE : thm := BAdditiveGroup.SUBRING_IMP_SUBGROUP_ADDITIVE
def RING_ADDITIVE_GROUP_PRODUCT_RING : thm := BAdditiveGroup.RING_ADDITIVE_GROUP_PRODUCT_RING
def RING_ADDITIVE_GROUP_RESTRICTED_PRODUCT_RING : thm := BAdditiveGroup.RING_ADDITIVE_GROUP_RESTRICTED_PRODUCT_RING

-- UnitGroup
def unit_group : thm := BUnitGroup.unit_group
def UNIT_GROUP : thm := BUnitGroup.UNIT_GROUP
def ABELIAN_UNIT_GROUP : thm := BUnitGroup.ABELIAN_UNIT_GROUP
def UNIT_GROUP_POW : thm := BUnitGroup.UNIT_GROUP_POW
def UNIT_GROUP_SUM : thm := BUnitGroup.UNIT_GROUP_SUM
def UNIT_GROUP_ZPOW_RING_NEG : thm := BUnitGroup.UNIT_GROUP_ZPOW_RING_NEG
def FINITELY_GENERATED_UNIT_GROUP : thm := BUnitGroup.FINITELY_GENERATED_UNIT_GROUP
def FIELD_UNIT_GROUP : thm := BUnitGroup.FIELD_UNIT_GROUP
def SUBGROUP_POSITIVE_REALS : thm := BUnitGroup.SUBGROUP_POSITIVE_REALS
def GROUP_REAL_MULTIPLICATIVE_ID_INV_POW : thm := BUnitGroup.GROUP_REAL_MULTIPLICATIVE_ID_INV_POW
def GROUP_REAL_MULTIPLICATIVE_ZPOW : thm := BUnitGroup.GROUP_REAL_MULTIPLICATIVE_ZPOW
def GROUP_REAL_MULTIPLICATIVE_SUM : thm := BUnitGroup.GROUP_REAL_MULTIPLICATIVE_SUM

-- UnitHomomorphisms
def GROUP_HOMOMORPHISM_UNIT_GROUP : thm := BUnitHomomorphisms.GROUP_HOMOMORPHISM_UNIT_GROUP
def UNIT_GROUP_SUBRING_GENERATED : thm := BUnitHomomorphisms.UNIT_GROUP_SUBRING_GENERATED
def RING_MONOMORPHISM_UNITS_IMAGE : thm := BUnitHomomorphisms.RING_MONOMORPHISM_UNITS_IMAGE
def RING_ISOMORPHISM_IMAGE_UNITS : thm := BUnitHomomorphisms.RING_ISOMORPHISM_IMAGE_UNITS
def ISOMORPHIC_RING_CARD_UNITS : thm := BUnitHomomorphisms.ISOMORPHIC_RING_CARD_UNITS
def RING_UNIT_PROD_RING : thm := BUnitHomomorphisms.RING_UNIT_PROD_RING
def UNIT_GROUP_PROD_RING : thm := BUnitHomomorphisms.UNIT_GROUP_PROD_RING
def CARD_UNITS_PROD_RING : thm := BUnitHomomorphisms.CARD_UNITS_PROD_RING
def UNIT_GROUP_PRODUCT_RING : thm := BUnitHomomorphisms.UNIT_GROUP_PRODUCT_RING
def UNIT_GROUP_RESTRICTED_PRODUCT_RING : thm := BUnitHomomorphisms.UNIT_GROUP_RESTRICTED_PRODUCT_RING

-- UnitsIndependent
def GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT_LEMMA : thm := BUnitsIndependent.GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT_LEMMA
def GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT : thm := BUnitsIndependent.GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT
def GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT_SET : thm := BUnitsIndependent.GROUP_HOMOMORPHISMS_UNITS_INDEPENDENT_SET
/-- `needs "Library/ring_groups.ml"`: already done by importing this module. -/
def ensureRingGroups : IO Unit := pure ()

end SessionLibrary.RingGroups
