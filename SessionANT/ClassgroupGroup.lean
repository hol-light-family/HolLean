/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/classgroup_group.ml                           . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/ClassgroupGroup.lean

  The session half of the classgroup_group.ml translation: it supplies HolANT.ClassgroupGroup's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/classgroup_group.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.ClassgroupGroup
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
import SessionANT.IdealArith
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionLibrary.Matroids
import SessionLibrary.FieldTheory
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.ClassgroupGroup

/-- The core theorems classgroup_group.ml uses. -/
def core1 : HolANT.ClassgroupGroup.CoreThms1 where
  AND_FORALL_THM := Session.AND_FORALL_THM
  DEDEKIND_IDEAL_CLASS_INVERSE := SessionANT.DedekindStruct.«DEDEKIND_IDEAL_CLASS_INVERSE»
  DEDEKIND_IDEAL_COPRIME_PROD_POW := SessionANT.Dedekind.«DEDEKIND_IDEAL_COPRIME_PROD_POW»
  DEDEKIND_IMP_INTEGRAL_DOMAIN := SessionANT.Dedekind.«DEDEKIND_IMP_INTEGRAL_DOMAIN»
  DEDEKIND_PID_EQ_CLASS_NUMBER_1 := SessionANT.Classgroup.«DEDEKIND_PID_EQ_CLASS_NUMBER_1»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  EXTENSION := Session.EXTENSION
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  GROUP_ELEMENT_ORDER_EQ_1 := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_EQ_1»
  GROUP_HOMOMORPHISM := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM»
  GROUP_LINV_EQ := SessionLibrary.GroupTheory.«GROUP_LINV_EQ»
  GROUP_POW_EQ_ID := SessionLibrary.GroupTheory.«GROUP_POW_EQ_ID»
  GROUP_POW_GROUP_ORDER := SessionLibrary.GroupTheory.«GROUP_POW_GROUP_ORDER»
  HAS_SIZE := Session.HAS_SIZE
  IDEALS_GENERATED_SING_EQ := SessionLibrary.RingTheory.«IDEALS_GENERATED_SING_EQ»
  IDEAL_CLASS_EQ := SessionANT.Classgroup.«IDEAL_CLASS_EQ»
  IDEAL_CLASS_MUL := SessionANT.DedekindStruct.«IDEAL_CLASS_MUL»
  IDEAL_CLASS_PRINCIPAL := SessionANT.DedekindStruct.«IDEAL_CLASS_PRINCIPAL»
  IDEAL_CLASS_REFL := SessionANT.DedekindStruct.«IDEAL_CLASS_REFL»
  IDEAL_CLASS_SYM := SessionANT.DedekindStruct.«IDEAL_CLASS_SYM»
  IDEAL_CLASS_TRANS := SessionANT.DedekindStruct.«IDEAL_CLASS_TRANS»
  IDEAL_GENERATED_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_0»
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_GENERATED_IMAGE_IDEAL_GENERATED := SessionANT.IdealArith.«IDEAL_GENERATED_IMAGE_IDEAL_GENERATED»
  IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0 := SessionANT.IdealArith.«IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0»
  IDEAL_POW_0 := SessionANT.IdealArith.«IDEAL_POW_0»
  IDEAL_POW_EQ_ZERO := SessionANT.IdealArith.«IDEAL_POW_EQ_ZERO»
  IDEAL_POW_PRINCIPAL := SessionANT.IdealArith.«IDEAL_POW_PRINCIPAL»
  IDEAL_PROD_AC := SessionANT.IdealArith.«IDEAL_PROD_AC»
  IDEAL_PROD_ASSOC := SessionANT.IdealArith.«IDEAL_PROD_ASSOC»
  IDEAL_PROD_CARRIER := SessionANT.IdealArith.«IDEAL_PROD_CARRIER»
  IDEAL_PROD_CARRIER_LEFT := SessionANT.IdealArith.«IDEAL_PROD_CARRIER_LEFT»
  IDEAL_PROD_COMM := SessionANT.IdealArith.«IDEAL_PROD_COMM»
  IDEAL_PROD_EQ_ZERO := SessionANT.IdealArith.«IDEAL_PROD_EQ_ZERO»
  IDEAL_PROD_HOMOMORPHIC_IMAGE := SessionANT.IdealArith.«IDEAL_PROD_HOMOMORPHIC_IMAGE»
  IDEAL_PROD_PRINCIPAL := SessionANT.IdealArith.«IDEAL_PROD_PRINCIPAL»
  IDEAL_PROD_RZERO := SessionANT.IdealArith.«IDEAL_PROD_RZERO»
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMP_CONJ := Session.IMP_CONJ
  INTEGRAL_DOMAIN_ASSOCIATES := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_ASSOCIATES»
  INTEGRAL_DOMAIN_UNIT_IDEAL := SessionANT.Classgroup.«INTEGRAL_DOMAIN_UNIT_IDEAL»
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_CLASS := SessionANT.DedekindStruct.«IN_IDEAL_CLASS»
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  MONO_EXISTS := Session.MONO_EXISTS
  NUMBER_FIELD_CLASS_GROUP_FINITE := SessionANT.Classgroup.«NUMBER_FIELD_CLASS_GROUP_FINITE»
  PRINCIPAL_IDEAL_0 := SessionLibrary.RingTheory.«PRINCIPAL_IDEAL_0»
  PRINCIPAL_IDEAL_CARRIER := SessionLibrary.RingTheory.«PRINCIPAL_IDEAL_CARRIER»
  PRINCIPAL_IDEAL_CLASS := SessionANT.DedekindStruct.«PRINCIPAL_IDEAL_CLASS»
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IDEAL_PROD := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PROD»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_UNIT_IN_CARRIER := SessionLibrary.RingTheory.«RING_UNIT_IN_CARRIER»
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  TRIVIAL_GROUP_HAS_SIZE_1 := SessionLibrary.GroupTheory.«TRIVIAL_GROUP_HAS_SIZE_1»
  abelian_group := SessionLibrary.GroupTheory.«abelian_group»
  class_number := SessionANT.Classgroup.«class_number»
  coprime := Session.coprime
  group_carrier := SessionLibrary.GroupTheory.«group_carrier»
  group_id := SessionLibrary.GroupTheory.«group_id»
  group_inv := SessionLibrary.GroupTheory.«group_inv»
  group_mul := SessionLibrary.GroupTheory.«group_mul»
  group_pow := SessionLibrary.GroupTheory.«group_pow»
  group_tybij := SessionLibrary.GroupTheory.«group_tybij»
  ideal_classes := SessionANT.Classgroup.«ideal_classes»
  ideal_pow := SessionANT.IdealArith.«ideal_pow»
  principal_ideal := SessionLibrary.RingTheory.«principal_ideal»

/-- What classgroup_group.ml uses from Session. -/
def deps : HolANT.ClassgroupGroup.ClassgroupGroupDeps where
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
  SELECT_CONV t := pure (Session.SELECT_CONV t)
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in classgroup_group.ml order. -/
initialize BClassgroupGroup : HolANT.ClassgroupGroup.ClassgroupGroup ←
  ioB "setupClassgroupGroup" (HolANT.ClassgroupGroup.setupClassgroupGroup deps).run

-- ClassgroupGroup
def class_group : thm := BClassgroupGroup.class_group
def CLASS_GROUP : thm := BClassgroupGroup.CLASS_GROUP
def IDEAL_CLASS_IN_CLASS_GROUP : thm := BClassgroupGroup.IDEAL_CLASS_IN_CLASS_GROUP
def CLASS_GROUP_MUL : thm := BClassgroupGroup.CLASS_GROUP_MUL
def IDEAL_CLASS_EQ_ID : thm := BClassgroupGroup.IDEAL_CLASS_EQ_ID
def CLASS_GROUP_INV : thm := BClassgroupGroup.CLASS_GROUP_INV
def CLASS_GROUP_POW : thm := BClassgroupGroup.CLASS_GROUP_POW
def CLASS_GROUP_POW_EQ_ID : thm := BClassgroupGroup.CLASS_GROUP_POW_EQ_ID
def ABELIAN_CLASS_GROUP : thm := BClassgroupGroup.ABELIAN_CLASS_GROUP
def TRIVIAL_CLASS_GROUP : thm := BClassgroupGroup.TRIVIAL_CLASS_GROUP
def DEDEKIND_PRINCIPAL_IDEAL_POW_CLASS_NUMBER : thm := BClassgroupGroup.DEDEKIND_PRINCIPAL_IDEAL_POW_CLASS_NUMBER
def FINITE_CLASS_GROUP : thm := BClassgroupGroup.FINITE_CLASS_GROUP
def HAS_SIZE_CLASS_GROUP : thm := BClassgroupGroup.HAS_SIZE_CLASS_GROUP
def NUMBER_FIELD_PRINCIPAL_IDEAL_POW_CLASS_NUMBER : thm := BClassgroupGroup.NUMBER_FIELD_PRINCIPAL_IDEAL_POW_CLASS_NUMBER
def DEDEKIND_PRINCIPAL_IDEAL_POW_COPRIME : thm := BClassgroupGroup.DEDEKIND_PRINCIPAL_IDEAL_POW_COPRIME
def NUMBER_FIELD_PRINCIPAL_IDEAL_POW_COPRIME : thm := BClassgroupGroup.NUMBER_FIELD_PRINCIPAL_IDEAL_POW_COPRIME
def DEDEKIND_COPRIME_MUL_POW : thm := BClassgroupGroup.DEDEKIND_COPRIME_MUL_POW
def NUMBER_FIELD_COPRIME_MUL_POW : thm := BClassgroupGroup.NUMBER_FIELD_COPRIME_MUL_POW
def CLASS_GROUP_HOMOMORPHISM_IDEAL_MAP : thm := BClassgroupGroup.CLASS_GROUP_HOMOMORPHISM_IDEAL_MAP
def DEDEKIND_CLASS_GROUP_EXTENSION : thm := BClassgroupGroup.DEDEKIND_CLASS_GROUP_EXTENSION

/-- `needs "ANT/classgroup_group.ml"`: already done by importing this module. -/
def ensureClassgroupGroup : IO Unit := pure ()

end SessionANT.ClassgroupGroup
