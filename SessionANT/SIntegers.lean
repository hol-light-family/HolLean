/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/s_integers.ml                                 . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/SIntegers.lean

  The session half of the s_integers.ml translation: it supplies HolANT.SIntegers's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/s_integers.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.SIntegers
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionLibrary.RingGroups
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
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionLibrary.Isum
import SessionANT.IdealNorm
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.ClassgroupGroup
import SessionANT.FractionalIdeals
import SessionANT.DedekindCriteria
import SessionANT.NfValuation

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.SIntegers

/-- The core theorems s_integers.ml uses. -/
def core1 : HolANT.SIntegers.CoreThms1 where
  ABELIAN_CLASS_GROUP := SessionANT.ClassgroupGroup.«ABELIAN_CLASS_GROUP»
  ABELIAN_GROUP_SUM_MUL := SessionLibrary.GroupTheory.«ABELIAN_GROUP_SUM_MUL»
  CARD_DIVIDES_GROUP_EPIMORPHIC_IMAGE := SessionLibrary.GroupTheory.«CARD_DIVIDES_GROUP_EPIMORPHIC_IMAGE»
  CARRIER_SUBRING_GENERATED_SUBRING := SessionLibrary.RingTheory.«CARRIER_SUBRING_GENERATED_SUBRING»
  CLASS_GROUP := SessionANT.ClassgroupGroup.«CLASS_GROUP»
  CLASS_GROUP_SUM_PRIME_CLASSES_EQ_ID := SessionANT.FractionalIdeals.«CLASS_GROUP_SUM_PRIME_CLASSES_EQ_ID»
  DEDEKIND_CLASS_GROUP_EXTENSION := SessionANT.ClassgroupGroup.«DEDEKIND_CLASS_GROUP_EXTENSION»
  DEDEKIND_EQ_IDEALS_INVERTIBLE := SessionANT.DedekindCriteria.«DEDEKIND_EQ_IDEALS_INVERTIBLE»
  DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE := SessionANT.Dedekind.«DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE»
  DEDEKIND_IDEAL_SUBSET_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_POW_VALUATION»
  DEDEKIND_IDEAL_SUBSET_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_VALUATION»
  DEDEKIND_IN_IDEAL_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IN_IDEAL_POW_VALUATION»
  DEDEKIND_KRULL_DIMENSION_ONE := SessionANT.Dedekind.«DEDEKIND_KRULL_DIMENSION_ONE»
  DEDEKIND_VALUATION := SessionANT.DedekindValuation.«DEDEKIND_VALUATION»
  DEDEKIND_VALUATION_1 := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_1»
  DEDEKIND_VALUATION_ADD := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_ADD»
  DEDEKIND_VALUATION_FINITE := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_FINITE»
  DEDEKIND_VALUATION_IMAGE := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_IMAGE»
  DEDEKIND_VALUATION_INTEGRAL := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_INTEGRAL»
  DEDEKIND_VALUATION_INV := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_INV»
  DEDEKIND_VALUATION_MUL := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_MUL»
  DEDEKIND_VALUATION_NEG := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_NEG»
  DEDEKIND_VALUATION_POS := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_POS»
  DEDEKIND_VALUATION_PRIME_IDEAL := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_PRIME_IDEAL»
  DEDEKIND_VALUATION_RING_DVR := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_RING_DVR»
  DEDEKIND_VALUATION_UNIT := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_UNIT»
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_IN_IMAGE := Session.EXISTS_IN_IMAGE
  EXTENSION := Session.EXTENSION
  EXTENSIONAL := Session.EXTENSIONAL
  FIELD_FRACTION_NONZERO := SessionANT.DedekindValuation.«FIELD_FRACTION_NONZERO»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_INV_EQ_0 := SessionLibrary.RingTheory.«FIELD_INV_EQ_0»
  FIELD_MUL_EQ_0 := SessionLibrary.RingTheory.«FIELD_MUL_EQ_0»
  FIELD_MUL_RINV := SessionLibrary.RingTheory.«FIELD_MUL_RINV»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FIELD_OF_FRACTIONS_IMP_MONOMORPHISM := SessionLibrary.RingTheory.«FIELD_OF_FRACTIONS_IMP_MONOMORPHISM»
  FIELD_UNIT := SessionLibrary.RingTheory.«FIELD_UNIT»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNION := Session.FINITE_UNION
  FINITE_UNIONS := Session.FINITE_UNIONS
  FIRST_GROUP_EPIMORPHISM_THEOREM := SessionLibrary.GroupTheory.«FIRST_GROUP_EPIMORPHISM_THEOREM»
  FORALL_AND_THM := Session.FORALL_AND_THM
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_UNIONS := Session.FORALL_IN_UNIONS
  FUN_EQ_THM := Session.FUN_EQ_THM
  GROUP_HOMOMORPHISM := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM»
  GROUP_HOMOMORPHISM_UNIT_GROUP := SessionLibrary.RingGroups.«GROUP_HOMOMORPHISM_UNIT_GROUP»
  GROUP_ID := SessionLibrary.GroupTheory.«GROUP_ID»
  GROUP_SUM := SessionLibrary.GroupTheory.«GROUP_SUM»
  GROUP_SUM_EQ := SessionLibrary.GroupTheory.«GROUP_SUM_EQ»
  GROUP_ZPOW := SessionLibrary.GroupTheory.«GROUP_ZPOW»
  GROUP_ZPOW_ADD := SessionLibrary.GroupTheory.«GROUP_ZPOW_ADD»
  IDEAL_CLASS_EQ_ID := SessionANT.ClassgroupGroup.«IDEAL_CLASS_EQ_ID»
  IDEAL_CLASS_EQ_SUM_PRIME_CLASSES := SessionANT.FractionalIdeals.«IDEAL_CLASS_EQ_SUM_PRIME_CLASSES»
  IDEAL_CLASS_IN_CLASS_GROUP := SessionANT.ClassgroupGroup.«IDEAL_CLASS_IN_CLASS_GROUP»
  IDEAL_GENERATED_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_0»
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_GENERATED_IMAGE_IDEAL_GENERATED := SessionANT.IdealArith.«IDEAL_GENERATED_IMAGE_IDEAL_GENERATED»
  IDEAL_GENERATED_INC := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_GENERATED_MINIMAL_EQ := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL_EQ»
  IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0 := SessionANT.IdealArith.«IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0»
  IDEAL_POW_EQ_ZERO := SessionANT.IdealArith.«IDEAL_POW_EQ_ZERO»
  IDEAL_POW_HOMOMORPHIC_IMAGE := SessionANT.IdealArith.«IDEAL_POW_HOMOMORPHIC_IMAGE»
  IDEAL_PROD_HOMOMORPHIC_IMAGE := SessionANT.IdealArith.«IDEAL_PROD_HOMOMORPHIC_IMAGE»
  IDEAL_VALUATION_EQ_0 := SessionANT.Dedekind.«IDEAL_VALUATION_EQ_0»
  IDEAL_VALUATION_FINITE_SUPPORT := SessionANT.Dedekind.«IDEAL_VALUATION_FINITE_SUPPORT»
  IDEAL_VALUATION_IDEAL_POW := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_POW»
  IDEAL_VALUATION_IDEAL_PROD := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_PROD»
  IDEAL_VALUATION_PRIME := SessionANT.Dedekind.«IDEAL_VALUATION_PRIME»
  IDEAL_VALUATION_UNIQUE := SessionANT.Dedekind.«IDEAL_VALUATION_UNIQUE»
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMAGE_I := Session.IMAGE_I
  IMP_CONJ := Session.IMP_CONJ
  INTEGER_GROUP := SessionLibrary.GroupTheory.«INTEGER_GROUP»
  INTEGRAL_DOMAIN_SUBRING_GENERATED := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_SUBRING_GENERATED»
  INT_LE_REFL := Session.INT_LE_REFL
  INT_OF_NUM_ADD := Session.INT_OF_NUM_ADD
  INT_OF_NUM_LE := Session.INT_OF_NUM_LE
  INT_OF_NUM_SUC := Session.INT_OF_NUM_SUC
  INT_POS := Session.INT_POS
  INT_SUB_RZERO := Session.INT_SUB_RZERO
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_IDEAL_GENERATED_SING_EQ := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SING_EQ»
  IN_IMAGE := Session.IN_IMAGE
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_SING := Session.IN_SING
  IN_SUBGROUP_SUM := SessionLibrary.GroupTheory.«IN_SUBGROUP_SUM»
  IN_SUBGROUP_ZPOW := SessionLibrary.GroupTheory.«IN_SUBGROUP_ZPOW»
  IN_UNION := Session.IN_UNION
/-- The core theorems s_integers.ml uses. -/
def core2 : HolANT.SIntegers.CoreThms2 where
  IN_UNIONS := Session.IN_UNIONS
  IN_UNIV := Session.IN_UNIV
  ISOMORPHIC_GROUP_SYM := SessionLibrary.GroupTheory.«ISOMORPHIC_GROUP_SYM»
  I_DEF := Session.I_DEF
  I_THM := Session.I_THM
  LE := Session.LE
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_REFL := Session.LE_REFL
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_CLAUSES := Session.MULT_CLAUSES
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NUMBER_FIELD_CLASS_GROUP_FINITE := SessionANT.Classgroup.«NUMBER_FIELD_CLASS_GROUP_FINITE»
  PRIME_IDEAL_HOMOMORPHIC_PREIMAGE := SessionLibrary.RingTheory.«PRIME_IDEAL_HOMOMORPHIC_PREIMAGE»
  PRIME_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_PROPER_IDEAL»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRODUCT_GROUP := SessionLibrary.GroupTheory.«PRODUCT_GROUP»
  PSUBSET := Session.PSUBSET
  PSUBSET_ALT := Session.PSUBSET_ALT
  RESTRICTION := Session.RESTRICTION
  RESTRICTION_EXTENSION := Session.RESTRICTION_EXTENSION
  RESTRICTION_IN_CARTESIAN_PRODUCT := Session.RESTRICTION_IN_CARTESIAN_PRODUCT
  RIGHT_EXISTS_IMP_THM := Session.RIGHT_EXISTS_IMP_THM
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RDISTRIB := SessionLibrary.RingTheory.«RING_ADD_RDISTRIB»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_CARRIER_SUBRING_GENERATED_SUBSET := SessionLibrary.RingTheory.«RING_CARRIER_SUBRING_GENERATED_SUBSET»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_NEG := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_NEG»
  RING_IDEAL_0 := SessionLibrary.RingTheory.«RING_IDEAL_0»
  RING_IDEAL_HOMOMORPHIC_PREIMAGE := SessionLibrary.RingTheory.«RING_IDEAL_HOMOMORPHIC_PREIMAGE»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_MONOMORPHISM_EQ_0 := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EQ_0»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_INCLUSION := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INCLUSION»
  RING_MONOMORPHISM_INJECTIVE_EQ := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INJECTIVE_EQ»
  RING_MONOMORPHISM_INTO_SUBRING := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INTO_SUBRING»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_LNEG := SessionLibrary.RingTheory.«RING_MUL_LNEG»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_NEG_EQ_0 := SessionLibrary.RingTheory.«RING_NEG_EQ_0»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_FRACTION_FIELD := SessionANT.NfValuation.«RING_OF_INTEGERS_FRACTION_FIELD»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INT_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_OF_INT_SUBRING_GENERATED»
  RING_OF_NUM_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_OF_NUM_SUBRING_GENERATED»
  RING_POW_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_POW_SUBRING_GENERATED»
  RING_SUB_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_SUB_SUBRING_GENERATED»
  RING_UNIT_IN_CARRIER := SessionLibrary.RingTheory.«RING_UNIT_IN_CARRIER»
  RING_UNIT_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_UNIT_SUBRING_GENERATED»
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBGROUP_GENERATED_INC := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_INC»
  SUBGROUP_GENERATED_MINIMAL := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_MINIMAL»
  SUBGROUP_GROUP_KERNEL := SessionLibrary.GroupTheory.«SUBGROUP_GROUP_KERNEL»
  SUBGROUP_SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«SUBGROUP_SUBGROUP_GENERATED»
  SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_GENERATED»
  SUBRING_GENERATED_MONO := SessionLibrary.RingTheory.«SUBRING_GENERATED_MONO»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  TRIVIAL_CLASS_GROUP := SessionANT.ClassgroupGroup.«TRIVIAL_CLASS_GROUP»
  UNIT_GROUP := SessionLibrary.RingGroups.«UNIT_GROUP»
  cartesian_product := Session.cartesian_product
  class_number := SessionANT.Classgroup.«class_number»
  field_of_fractions := SessionLibrary.RingTheory.«field_of_fractions»
  group_epimorphism := SessionLibrary.GroupTheory.«group_epimorphism»
  group_exactness := SessionLibrary.GroupTheory.«group_exactness»
  group_homomorphism := SessionLibrary.GroupTheory.«group_homomorphism»
  group_image := SessionLibrary.GroupTheory.«group_image»
  group_kernel := SessionLibrary.GroupTheory.«group_kernel»
  group_monomorphism := SessionLibrary.GroupTheory.«group_monomorphism»
  ideal_classes := SessionANT.Classgroup.«ideal_classes»
  ideal_prod := SessionANT.IdealArith.«ideal_prod»
  prime_ideal := SessionLibrary.RingTheory.«prime_ideal»
  principal_ideal := SessionLibrary.RingTheory.«principal_ideal»
  proper_ideal := SessionLibrary.RingTheory.«proper_ideal»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_ideal := SessionLibrary.RingTheory.«ring_ideal»
  ring_setmul := SessionLibrary.RingTheory.«ring_setmul»
  subring_of := SessionLibrary.RingTheory.«subring_of»
  trivial_group := SessionLibrary.GroupTheory.«trivial_group»

/-- What s_integers.ml uses from Session. -/
def deps : HolANT.SIntegers.SIntegersDeps where
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

/- The bundles, in s_integers.ml order. -/
initialize BSIntegers01 : HolANT.SIntegers.SIntegers01 ←
  ioB "setupSIntegers01" (HolANT.SIntegers.setupSIntegers01 deps).run
initialize BSIntegers02 : HolANT.SIntegers.SIntegers02 ←
  ioB "setupSIntegers02" (HolANT.SIntegers.setupSIntegers02 deps BSIntegers01).run
initialize BSIntegers03 : HolANT.SIntegers.SIntegers03 ←
  ioB "setupSIntegers03" (HolANT.SIntegers.setupSIntegers03 deps BSIntegers01 BSIntegers02).run

-- SIntegers01
def ring_of_s_integers : thm := BSIntegers01.ring_of_s_integers
def RING_OF_S_INTEGERS : thm := BSIntegers01.RING_OF_S_INTEGERS
def RING_OF_S_INTEGERS_SUBSET : thm := BSIntegers01.RING_OF_S_INTEGERS_SUBSET
def RING_OF_S_INTEGERS_SUBRING_OF : thm := BSIntegers01.RING_OF_S_INTEGERS_SUBRING_OF
def RING_OF_S_INTEGERS_CARRIER : thm := BSIntegers01.RING_OF_S_INTEGERS_CARRIER
def RING_OF_S_INTEGERS_SUBRING : thm := BSIntegers01.RING_OF_S_INTEGERS_SUBRING
def INTEGRAL_DOMAIN_RING_OF_S_INTEGERS : thm := BSIntegers01.INTEGRAL_DOMAIN_RING_OF_S_INTEGERS
def RING_OF_S_INTEGERS_MONO : thm := BSIntegers01.RING_OF_S_INTEGERS_MONO
def RING_OF_S_INTEGERS_IMAGE : thm := BSIntegers01.RING_OF_S_INTEGERS_IMAGE
def RING_MONOMORPHISM_RING_OF_S_INTEGERS : thm := BSIntegers01.RING_MONOMORPHISM_RING_OF_S_INTEGERS
def FIELD_OF_FRACTIONS_RING_OF_S_INTEGERS : thm := BSIntegers01.FIELD_OF_FRACTIONS_RING_OF_S_INTEGERS
def RING_OF_S_INTEGERS_EMPTY : thm := BSIntegers01.RING_OF_S_INTEGERS_EMPTY
def RING_UNIT_RING_OF_S_INTEGERS : thm := BSIntegers01.RING_UNIT_RING_OF_S_INTEGERS
def RING_OF_S_INTEGERS_COMPLEMENT_SING : thm := BSIntegers01.RING_OF_S_INTEGERS_COMPLEMENT_SING
def RING_OF_S_INTEGERS_VALUATION_IDEAL : thm := BSIntegers01.RING_OF_S_INTEGERS_VALUATION_IDEAL
def RING_OF_S_INTEGERS_IDEAL_EXTENSION : thm := BSIntegers01.RING_OF_S_INTEGERS_IDEAL_EXTENSION
def RING_OF_S_INTEGERS_IDEAL_CONTRACTION : thm := BSIntegers01.RING_OF_S_INTEGERS_IDEAL_CONTRACTION
def RING_OF_S_INTEGERS_IDEAL_EXTENSION_EQ_CARRIER : thm := BSIntegers01.RING_OF_S_INTEGERS_IDEAL_EXTENSION_EQ_CARRIER
def RING_OF_S_INTEGERS_IDEAL_EXTENSION_PRIME : thm := BSIntegers01.RING_OF_S_INTEGERS_IDEAL_EXTENSION_PRIME

-- SIntegers02
def PRIME_IDEAL_RING_OF_S_INTEGERS_EXTENSION : thm := BSIntegers02.PRIME_IDEAL_RING_OF_S_INTEGERS_EXTENSION
def DEDEKIND_RING_OF_S_INTEGERS : thm := BSIntegers02.DEDEKIND_RING_OF_S_INTEGERS
def RING_OF_S_INTEGERS_PRIME_IDEALS : thm := BSIntegers02.RING_OF_S_INTEGERS_PRIME_IDEALS
def IDEAL_VALUATION_RING_OF_S_INTEGERS : thm := BSIntegers02.IDEAL_VALUATION_RING_OF_S_INTEGERS
def DEDEKIND_VALUATION_RING_OF_S_INTEGERS : thm := BSIntegers02.DEDEKIND_VALUATION_RING_OF_S_INTEGERS
def RING_OF_S_INTEGERS_EXTENSION_GENERATOR_VALUATION : thm := BSIntegers02.RING_OF_S_INTEGERS_EXTENSION_GENERATOR_VALUATION
def RING_OF_S_INTEGERS_CLASS_GROUP : thm := BSIntegers02.RING_OF_S_INTEGERS_CLASS_GROUP
def RING_OF_S_INTEGERS_CLASS_GROUP_QUOTIENT : thm := BSIntegers02.RING_OF_S_INTEGERS_CLASS_GROUP_QUOTIENT
def RING_OF_S_INTEGERS_PID_EQ : thm := BSIntegers02.RING_OF_S_INTEGERS_PID_EQ
def RING_OF_S_INTEGERS_EXTENSION_PRINCIPAL : thm := BSIntegers02.RING_OF_S_INTEGERS_EXTENSION_PRINCIPAL
def GROUP_HOMOMORPHISM_RING_OF_S_INTEGERS_VALUATIONS : thm := BSIntegers02.GROUP_HOMOMORPHISM_RING_OF_S_INTEGERS_VALUATIONS
def GROUP_HOMOMORPHISM_CLASS_GROUP_SUM_PRIME_CLASSES : thm := BSIntegers02.GROUP_HOMOMORPHISM_CLASS_GROUP_SUM_PRIME_CLASSES

-- SIntegers03
def RING_OF_S_INTEGERS_CLASS_GROUP_EXACT : thm := BSIntegers03.RING_OF_S_INTEGERS_CLASS_GROUP_EXACT
def RING_OF_S_INTEGERS_CLASS_NUMBER_DIVIDES : thm := BSIntegers03.RING_OF_S_INTEGERS_CLASS_NUMBER_DIVIDES
def RING_OF_S_INTEGERS_PID : thm := BSIntegers03.RING_OF_S_INTEGERS_PID
def NUMBER_FIELD_RING_OF_S_INTEGERS_EMPTY : thm := BSIntegers03.NUMBER_FIELD_RING_OF_S_INTEGERS_EMPTY
def NUMBER_FIELD_CLASS_GROUP_RING_OF_S_INTEGERS : thm := BSIntegers03.NUMBER_FIELD_CLASS_GROUP_RING_OF_S_INTEGERS
def NUMBER_FIELD_RING_OF_S_INTEGERS_PID : thm := BSIntegers03.NUMBER_FIELD_RING_OF_S_INTEGERS_PID

/-- `needs "ANT/s_integers.ml"`: already done by importing this module. -/
def ensureSIntegers : IO Unit := pure ()

end SessionANT.SIntegers
