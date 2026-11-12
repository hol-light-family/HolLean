/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/fingen_group.ml                               . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/FingenGroup.lean

  The session half of the fingen_group.ml translation: it supplies HolANT.FingenGroup's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/fingen_group.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.FingenGroup
import SessionLibrary.Products
import SessionLibrary.Frag
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.Prime
import SessionLibrary.GroupTheory
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Pocklington
import SessionLibrary.RingTheory
import SessionLibrary.RingGroups

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.FingenGroup

/-- The core theorems fingen_group.ml uses. -/
def core1 : HolANT.FingenGroup.CoreThms1 where
  ABELIAN_GROUP_MUL_POW := SessionLibrary.GroupTheory.«ABELIAN_GROUP_MUL_POW»
  ABELIAN_GROUP_SUM_CLAUSES := SessionLibrary.GroupTheory.«ABELIAN_GROUP_SUM_CLAUSES»
  ABELIAN_GROUP_SUM_INV := SessionLibrary.GroupTheory.«ABELIAN_GROUP_SUM_INV»
  ABELIAN_GROUP_SUM_MUL := SessionLibrary.GroupTheory.«ABELIAN_GROUP_SUM_MUL»
  ABELIAN_GROUP_SUM_POW := SessionLibrary.GroupTheory.«ABELIAN_GROUP_SUM_POW»
  ADD1 := Session.ADD1
  ADD_EQ_0 := Session.ADD_EQ_0
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_IMAGE_LE := Session.CARD_IMAGE_LE
  CARD_NUMSEG := Session.CARD_NUMSEG
  CARD_SUBSET := Session.CARD_SUBSET
  CARD_UNIONS_LE := Session.CARD_UNIONS_LE
  CARRIER_SUBGROUP_GENERATED_SUBGROUP := SessionLibrary.GroupTheory.«CARRIER_SUBGROUP_GENERATED_SUBGROUP»
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DIVISION := Session.DIVISION
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  EQ_IMP_LE := Session.EQ_IMP_LE
  EQ_TRANS := Session.EQ_TRANS
  EXP := Session.EXP
  EXP_EQ_0 := Session.EXP_EQ_0
  EXP_MONO_LE_IMP := Session.EXP_MONO_LE_IMP
  FINITELY_GENERATED_ABELIAN_GROUP_EXPONENTS := SessionLibrary.GroupTheory.«FINITELY_GENERATED_ABELIAN_GROUP_EXPONENTS»
  FINITELY_GENERATED_ABELIAN_GROUP_POW := SessionLibrary.GroupTheory.«FINITELY_GENERATED_ABELIAN_GROUP_POW»
  FINITELY_GENERATED_GROUP := SessionLibrary.GroupTheory.«FINITELY_GENERATED_GROUP»
  FINITE_CARTESIAN_PRODUCT := SessionLibrary.Card.«FINITE_CARTESIAN_PRODUCT»
  FINITE_CYCLIC_SUBGROUP_ORDER := SessionLibrary.GroupTheory.«FINITE_CYCLIC_SUBGROUP_ORDER»
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_FUNSPACE := Session.FINITE_FUNSPACE
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_INT_SEG := Session.FINITE_INT_SEG
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_PRODUCT_DEPENDENT := Session.FINITE_PRODUCT_DEPENDENT
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_SUBSET_IMAGE := Session.FINITE_SUBSET_IMAGE
  FINITE_UNION := Session.FINITE_UNION
  FINITE_UNIONS := Session.FINITE_UNIONS
  FORALL_INT_CASES := Session.FORALL_INT_CASES
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FUN_EQ_THM := Session.FUN_EQ_THM
  GROUP_HOMOMORPHISM_PREIMAGE_IMAGE := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM_PREIMAGE_IMAGE»
  GROUP_ID := SessionLibrary.GroupTheory.«GROUP_ID»
  GROUP_INV := SessionLibrary.GroupTheory.«GROUP_INV»
  GROUP_INV_INV := SessionLibrary.GroupTheory.«GROUP_INV_INV»
  GROUP_KERNEL_SUBSET_CARRIER := SessionLibrary.GroupTheory.«GROUP_KERNEL_SUBSET_CARRIER»
  GROUP_LINV_UNIQUE := SessionLibrary.GroupTheory.«GROUP_LINV_UNIQUE»
  GROUP_MUL := SessionLibrary.GroupTheory.«GROUP_MUL»
  GROUP_MUL_ASSOC := SessionLibrary.GroupTheory.«GROUP_MUL_ASSOC»
  GROUP_MUL_LID := SessionLibrary.GroupTheory.«GROUP_MUL_LID»
  GROUP_MUL_LINV := SessionLibrary.GroupTheory.«GROUP_MUL_LINV»
  GROUP_MUL_RID := SessionLibrary.GroupTheory.«GROUP_MUL_RID»
  GROUP_MUL_RINV := SessionLibrary.GroupTheory.«GROUP_MUL_RINV»
  GROUP_NPOW := SessionLibrary.GroupTheory.«GROUP_NPOW»
  GROUP_POW := SessionLibrary.GroupTheory.«GROUP_POW»
  GROUP_POW_ADD := SessionLibrary.GroupTheory.«GROUP_POW_ADD»
  GROUP_POW_POW := SessionLibrary.GroupTheory.«GROUP_POW_POW»
  GROUP_REAL_MULTIPLICATIVE_ID_INV_POW := SessionLibrary.RingGroups.«GROUP_REAL_MULTIPLICATIVE_ID_INV_POW»
  GROUP_RINV_UNIQUE := SessionLibrary.GroupTheory.«GROUP_RINV_UNIQUE»
  GROUP_SUM := SessionLibrary.GroupTheory.«GROUP_SUM»
  GROUP_SUM_CLAUSES_EXISTS := SessionLibrary.GroupTheory.«GROUP_SUM_CLAUSES_EXISTS»
  GROUP_SUM_EQ := SessionLibrary.GroupTheory.«GROUP_SUM_EQ»
  GROUP_SUM_RESTRICT_SET := SessionLibrary.GroupTheory.«GROUP_SUM_RESTRICT_SET»
  GROUP_ZPOW := SessionLibrary.GroupTheory.«GROUP_ZPOW»
  GROUP_ZPOW_0 := SessionLibrary.GroupTheory.«GROUP_ZPOW_0»
  GROUP_ZPOW_ADD := SessionLibrary.GroupTheory.«GROUP_ZPOW_ADD»
  GROUP_ZPOW_EQ_ID := SessionLibrary.GroupTheory.«GROUP_ZPOW_EQ_ID»
  GROUP_ZPOW_MUL := SessionLibrary.GroupTheory.«GROUP_ZPOW_MUL»
  GROUP_ZPOW_NEG := SessionLibrary.GroupTheory.«GROUP_ZPOW_NEG»
  GROUP_ZPOW_SUB := SessionLibrary.GroupTheory.«GROUP_ZPOW_SUB»
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_FUNSPACE := Session.HAS_SIZE_FUNSPACE
  IMP_CONJ := Session.IMP_CONJ
  INSERT_SUBSET := Session.INSERT_SUBSET
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_DIVISION := Session.INT_DIVISION
  INT_IMAGE := Session.INT_IMAGE
  INT_LE_NEG2 := Session.INT_LE_NEG2
  INT_LT_IMP_LE := Session.INT_LT_IMP_LE
  INT_NEG_EQ_0 := Session.INT_NEG_EQ_0
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LE := Session.INT_OF_NUM_LE
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_SUB_0 := Session.INT_SUB_0
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_NUMSEG := Session.IN_NUMSEG
  IN_SING := Session.IN_SING
  IN_SUBGROUP_INV := SessionLibrary.GroupTheory.«IN_SUBGROUP_INV»
  IN_SUBGROUP_MUL := SessionLibrary.GroupTheory.«IN_SUBGROUP_MUL»
/-- The core theorems fingen_group.ml uses. -/
def core2 : HolANT.FingenGroup.CoreThms2 where
  IN_SUBGROUP_SUM := SessionLibrary.GroupTheory.«IN_SUBGROUP_SUM»
  IN_SUBGROUP_ZPOW := SessionLibrary.GroupTheory.«IN_SUBGROUP_ZPOW»
  IN_UNION := Session.IN_UNION
  LEFT_AND_EXISTS_THM := Session.LEFT_AND_EXISTS_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LET_TRANS := Session.LET_TRANS
  LE_0 := Session.LE_0
  LE_ADD := Session.LE_ADD
  LE_ADDR := Session.LE_ADDR
  LE_EXP := Session.LE_EXP
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  LE_TRANS := Session.LE_TRANS
  LTE_TRANS := Session.LTE_TRANS
  LT_IMP_LE := Session.LT_IMP_LE
  LT_MULT_RCANCEL := Session.LT_MULT_RCANCEL
  LT_POW2_REFL := Session.LT_POW2_REFL
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MOD_LT_EQ := Session.MOD_LT_EQ
  MONO_EXISTS := Session.MONO_EXISTS
  MONO_FORALL := Session.MONO_FORALL
  MULT_2 := Session.MULT_2
  MULT_ASSOC := Session.MULT_ASSOC
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EXP := Session.MULT_EXP
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LE := Session.NOT_LE
  NOT_LT := Session.NOT_LT
  REAL_ARCH_POW2 := Session.REAL_ARCH_POW2
  REAL_ARCH_SIMPLE := Session.REAL_ARCH_SIMPLE
  REAL_INV_1 := Session.REAL_INV_1
  REAL_INV_1_LT := Session.REAL_INV_1_LT
  REAL_INV_INV := Session.REAL_INV_INV
  REAL_INV_LE_1 := Session.REAL_INV_LE_1
  REAL_INV_MUL := Session.REAL_INV_MUL
  REAL_LET_TRANS := Session.REAL_LET_TRANS
  REAL_LE_INV2 := Session.REAL_LE_INV2
  REAL_LE_INV_EQ := Session.REAL_LE_INV_EQ
  REAL_LE_LDIV_EQ := Session.REAL_LE_LDIV_EQ
  REAL_LE_LMUL := Session.REAL_LE_LMUL
  REAL_LE_MUL2 := Session.REAL_LE_MUL2
  REAL_LE_RDIV_EQ := Session.REAL_LE_RDIV_EQ
  REAL_LE_REFL := Session.REAL_LE_REFL
  REAL_LE_TRANS := Session.REAL_LE_TRANS
  REAL_LTE_TRANS := Session.REAL_LTE_TRANS
  REAL_LT_IMP_LE := Session.REAL_LT_IMP_LE
  REAL_LT_IMP_NZ := Session.REAL_LT_IMP_NZ
  REAL_LT_INV_EQ := Session.REAL_LT_INV_EQ
  REAL_LT_LMUL_EQ := Session.REAL_LT_LMUL_EQ
  REAL_LT_MUL := Session.REAL_LT_MUL
  REAL_LT_POW2 := Session.REAL_LT_POW2
  REAL_MAX_LE := Session.REAL_MAX_LE
  REAL_MUL_RINV := Session.REAL_MUL_RINV
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_OF_NUM_LE := Session.REAL_OF_NUM_LE
  REAL_OF_NUM_LT := Session.REAL_OF_NUM_LT
  REAL_OF_NUM_POW := Session.REAL_OF_NUM_POW
  REAL_POS := Session.REAL_POS
  REAL_POW_ADD := Session.REAL_POW_ADD
  REAL_POW_INV := Session.REAL_POW_INV
  REAL_POW_LE := Session.REAL_POW_LE
  REAL_POW_LE2 := Session.REAL_POW_LE2
  REAL_POW_LE2_REV := Session.REAL_POW_LE2_REV
  REAL_POW_LT := Session.REAL_POW_LT
  REAL_POW_MONO := Session.REAL_POW_MONO
  REAL_POW_MONO_INV := Session.REAL_POW_MONO_INV
  REAL_POW_POW := Session.REAL_POW_POW
  REAL_ZPOW_ADD := Session.REAL_ZPOW_ADD
  REAL_ZPOW_LT := Session.REAL_ZPOW_LT
  REAL_ZPOW_NEG := Session.REAL_ZPOW_NEG
  REAL_ZPOW_NUM := Session.REAL_ZPOW_NUM
  RESTRICTION := Session.RESTRICTION
  RESTRICTION_IN_CARTESIAN_PRODUCT := Session.RESTRICTION_IN_CARTESIAN_PRODUCT
  RIGHT_EXISTS_IMP_THM := Session.RIGHT_EXISTS_IMP_THM
  SIMPLE_IMAGE := Session.SIMPLE_IMAGE
  SKOLEM_THM := Session.SKOLEM_THM
  SUBGROUP_GENERATED_BY_HOMOMORPHIC_IMAGE := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_BY_HOMOMORPHIC_IMAGE»
  SUBGROUP_GENERATED_IDEMPOT_GEN := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_IDEMPOT_GEN»
  SUBGROUP_GENERATED_INC_GEN := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_INC_GEN»
  SUBGROUP_GENERATED_MONO := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_MONO»
  SUBGROUP_GENERATED_SUPERSET := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_SUPERSET»
  SUBGROUP_GROUP_IMAGE := SessionLibrary.GroupTheory.«SUBGROUP_GROUP_IMAGE»
  SUBGROUP_GROUP_KERNEL := SessionLibrary.GroupTheory.«SUBGROUP_GROUP_KERNEL»
  SUBGROUP_OF_TORSION := SessionLibrary.GroupTheory.«SUBGROUP_OF_TORSION»
  SUBGROUP_SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«SUBGROUP_SUBGROUP_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_RESTRICT := Session.SUBSET_RESTRICT
  SUBSET_TRANS := Session.SUBSET_TRANS
  SUBSET_UNION := Session.SUBSET_UNION
  UNIONS_IMAGE := Session.UNIONS_IMAGE
  UNION_SUBSET := Session.UNION_SUBSET
  group_div := SessionLibrary.GroupTheory.«group_div»
  group_image := SessionLibrary.GroupTheory.«group_image»
  num_MAX := Session.num_MAX
  num_WOP := Session.num_WOP
  real_div := Session.real_div
  real_pow := Session.real_pow

/-- What fingen_group.ml uses from Session. -/
def deps : HolANT.FingenGroup.FingenGroupDeps where
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
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in fingen_group.ml order. -/
initialize BFingenGroup01 : HolANT.FingenGroup.FingenGroup01 ←
  ioB "setupFingenGroup01" (HolANT.FingenGroup.setupFingenGroup01 deps).run
initialize BFingenGroup02 : HolANT.FingenGroup.FingenGroup02 ←
  ioB "setupFingenGroup02" (HolANT.FingenGroup.setupFingenGroup02 deps BFingenGroup01).run

-- FingenGroup01
def FINITELY_GENERATED_GROUP_EXTENSION : thm := BFingenGroup01.FINITELY_GENERATED_GROUP_EXTENSION
def FINITELY_GENERATED_ABELIAN_GROUP_MOD_POW : thm := BFingenGroup01.FINITELY_GENERATED_ABELIAN_GROUP_MOD_POW
def GROUP_SUM_POW_REAL_MULTIPLICATIVE_BOUND : thm := BFingenGroup01.GROUP_SUM_POW_REAL_MULTIPLICATIVE_BOUND
def GROUP_REAL_MULTIPLICATIVE_BOX_COUNT : thm := BFingenGroup01.GROUP_REAL_MULTIPLICATIVE_BOX_COUNT
def ABELIAN_GROUP_DISCRETE_DEPENDENT : thm := BFingenGroup01.ABELIAN_GROUP_DISCRETE_DEPENDENT
def FINITELY_GENERATED_ABELIAN_GROUP_DISCRETE : thm := BFingenGroup01.FINITELY_GENERATED_ABELIAN_GROUP_DISCRETE

-- FingenGroup02
def FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS : thm := BFingenGroup02.FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS

/-- `needs "ANT/fingen_group.ml"`: already done by importing this module. -/
def ensureFingenGroup : IO Unit := pure ()

end SessionANT.FingenGroup
