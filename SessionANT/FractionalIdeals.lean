/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/fractional_ideals.ml                          . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/FractionalIdeals.lean

  The session half of the fractional_ideals.ml translation: it supplies HolANT.FractionalIdeals's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/fractional_ideals.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.FractionalIdeals
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
import SessionANT.IdealArith
import SessionLibrary.Products
import SessionANT.Algmisc
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.FractionalIdeals

/-- The core theorems fractional_ideals.ml uses. -/
def core1 : HolANT.FractionalIdeals.CoreThms1 where
  ABELIAN_CLASS_GROUP := SessionANT.ClassgroupGroup.«ABELIAN_CLASS_GROUP»
  ABELIAN_INTEGER_GROUP := SessionLibrary.GroupTheory.«ABELIAN_INTEGER_GROUP»
  CLASS_GROUP := SessionANT.ClassgroupGroup.«CLASS_GROUP»
  CLASS_GROUP_MUL := SessionANT.ClassgroupGroup.«CLASS_GROUP_MUL»
  DEDEKIND_IDEAL_INVERTIBLE := SessionANT.Dedekind.«DEDEKIND_IDEAL_INVERTIBLE»
  DEDEKIND_IDEAL_SUBSET_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_VALUATION»
  DEDEKIND_IMP_INTEGRAL_DOMAIN := SessionANT.Dedekind.«DEDEKIND_IMP_INTEGRAL_DOMAIN»
  DEDEKIND_VALUATION := SessionANT.DedekindValuation.«DEDEKIND_VALUATION»
  DEDEKIND_VALUATION_UNIT := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_UNIT»
  DEST_FRAG_ADD := SessionLibrary.Frag.«DEST_FRAG_ADD»
  EQ_SYM_EQ := Session.EQ_SYM_EQ
  EQ_TRANS := Session.EQ_TRANS
  EXTENSION := Session.EXTENSION
  FIELD_FRACTION_NONZERO := SessionANT.DedekindValuation.«FIELD_FRACTION_NONZERO»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_INV_EQ_0 := SessionLibrary.RingTheory.«FIELD_INV_EQ_0»
  FIELD_MUL_LINV := SessionLibrary.RingTheory.«FIELD_MUL_LINV»
  FIELD_MUL_RINV := SessionLibrary.RingTheory.«FIELD_MUL_RINV»
  FIELD_OF_FRACTIONS_IMP_MONOMORPHISM := SessionLibrary.RingTheory.«FIELD_OF_FRACTIONS_IMP_MONOMORPHISM»
  FIELD_UNIT := SessionLibrary.RingTheory.«FIELD_UNIT»
  FIELD_UNIT_GROUP := SessionLibrary.RingGroups.«FIELD_UNIT_GROUP»
  FINITE_FRAG_SUPPORT := SessionLibrary.Frag.«FINITE_FRAG_SUPPORT»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNION := Session.FINITE_UNION
  FIRST_GROUP_EPIMORPHISM_THEOREM := SessionLibrary.GroupTheory.«FIRST_GROUP_EPIMORPHISM_THEOREM»
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FRAG_EQ := SessionLibrary.Frag.«FRAG_EQ»
  FREE_ABELIAN_GROUP := SessionLibrary.GroupTheory.«FREE_ABELIAN_GROUP»
  FUN_EQ_THM := Session.FUN_EQ_THM
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  GROUP_DIV := SessionLibrary.GroupTheory.«GROUP_DIV»
  GROUP_EPIMORPHISM := SessionLibrary.GroupTheory.«GROUP_EPIMORPHISM»
  GROUP_HOMOMORPHISM := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM»
  GROUP_HOMOMORPHISM_DIV := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM_DIV»
  GROUP_HOMOMORPHISM_UNIT_GROUP := SessionLibrary.RingGroups.«GROUP_HOMOMORPHISM_UNIT_GROUP»
  GROUP_HOMOMORPHISM_ZPOW := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM_ZPOW»
  GROUP_INV_ID := SessionLibrary.GroupTheory.«GROUP_INV_ID»
  GROUP_ISOMORPHISM := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISM»
  GROUP_MUL_RID := SessionLibrary.GroupTheory.«GROUP_MUL_RID»
  GROUP_SUM := SessionLibrary.GroupTheory.«GROUP_SUM»
  GROUP_SUM_CLAUSES_EXISTS := SessionLibrary.GroupTheory.«GROUP_SUM_CLAUSES_EXISTS»
  GROUP_SUM_EQ := SessionLibrary.GroupTheory.«GROUP_SUM_EQ»
  GROUP_SUM_HOMOMORPHIC_IMAGE := SessionLibrary.GroupTheory.«GROUP_SUM_HOMOMORPHIC_IMAGE»
  GROUP_SUM_SING := SessionLibrary.GroupTheory.«GROUP_SUM_SING»
  GROUP_SUM_SUPERSET := SessionLibrary.GroupTheory.«GROUP_SUM_SUPERSET»
  GROUP_ZPOW := SessionLibrary.GroupTheory.«GROUP_ZPOW»
  GROUP_ZPOW_INTEGER_GROUP := SessionLibrary.GroupTheory.«GROUP_ZPOW_INTEGER_GROUP»
  IDEAL_CLASS_EQ := SessionANT.Classgroup.«IDEAL_CLASS_EQ»
  IDEAL_CLASS_EQ_ID := SessionANT.ClassgroupGroup.«IDEAL_CLASS_EQ_ID»
  IDEAL_CLASS_IN_CLASS_GROUP := SessionANT.ClassgroupGroup.«IDEAL_CLASS_IN_CLASS_GROUP»
  IDEAL_GENERATED_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_0»
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_GENERATED_SING_EQ_CARRIER := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING_EQ_CARRIER»
  IDEAL_OF_VALUATIONS := SessionANT.DedekindValuation.«IDEAL_OF_VALUATIONS»
  IDEAL_PROD_EQ_ZERO := SessionANT.IdealArith.«IDEAL_PROD_EQ_ZERO»
  IDEAL_PROD_EXPLICIT := SessionANT.IdealArith.«IDEAL_PROD_EXPLICIT»
  IDEAL_PROD_SCALE := SessionANT.IdealArith.«IDEAL_PROD_SCALE»
  IDEAL_VALUATION_CARRIER := SessionANT.Dedekind.«IDEAL_VALUATION_CARRIER»
  IDEAL_VALUATION_FINITE_SUPPORT := SessionANT.Dedekind.«IDEAL_VALUATION_FINITE_SUPPORT»
  IDEAL_VALUATION_IDEAL_PROD := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_PROD»
  IDEAL_VALUATION_PRIME := SessionANT.Dedekind.«IDEAL_VALUATION_PRIME»
  IDEAL_VALUATION_PRINCIPAL_MUL := SessionANT.Dedekind.«IDEAL_VALUATION_PRINCIPAL_MUL»
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMAGE_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«IMAGE_HOMOMORPHISM_MUL»
  IMAGE_SUBSET := Session.IMAGE_SUBSET
  IMAGE_o := Session.IMAGE_o
  IMP_CONJ := Session.IMP_CONJ
  IMP_IMP := Session.IMP_IMP
  INTEGER_GROUP := SessionLibrary.GroupTheory.«INTEGER_GROUP»
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_MUL_LCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_LCANCEL»
  INTEGRAL_DOMAIN_NONTRIVIAL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_NONTRIVIAL»
  INTER_SUBSET := Session.INTER_SUBSET
  INT_ADD_LID := Session.INT_ADD_LID
  INT_LE_REFL := Session.INT_LE_REFL
  INT_MUL_RID := Session.INT_MUL_RID
  INT_MUL_RZERO := Session.INT_MUL_RZERO
  INT_OF_NUM_ADD := Session.INT_OF_NUM_ADD
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LE := Session.INT_OF_NUM_LE
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_SUB_RZERO := Session.INT_SUB_RZERO
  IN_DIFF := Session.IN_DIFF
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_CLASS := SessionANT.DedekindStruct.«IN_IDEAL_CLASS»
  IN_IMAGE := Session.IN_IMAGE
  IN_INTER := Session.IN_INTER
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_ADD := SessionLibrary.RingTheory.«IN_RING_IDEAL_ADD»
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_SING := Session.IN_SING
  IN_SUBRING_0 := SessionLibrary.RingTheory.«IN_SUBRING_0»
  IN_SUBRING_ADD := SessionLibrary.RingTheory.«IN_SUBRING_ADD»
  IN_SUBRING_MUL := SessionLibrary.RingTheory.«IN_SUBRING_MUL»
/-- The core theorems fractional_ideals.ml uses. -/
def core2 : HolANT.FractionalIdeals.CoreThms2 where
  IN_UNION := Session.IN_UNION
  IN_UNIV := Session.IN_UNIV
  ISOMORPHIC_GROUP_SYM := SessionLibrary.GroupTheory.«ISOMORPHIC_GROUP_SYM»
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  PRIME_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_PROPER_IDEAL»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRINCIPAL_IDEAL_IDEAL_GENERATED_SING := SessionLibrary.RingTheory.«PRINCIPAL_IDEAL_IDEAL_GENERATED_SING»
  PROPER_IDEAL_ALT := SessionLibrary.RingTheory.«PROPER_IDEAL_ALT»
  RIGHT_EXISTS_IMP_THM := Session.RIGHT_EXISTS_IMP_THM
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_LDISTRIB := SessionLibrary.RingTheory.«RING_ADD_LDISTRIB»
  RING_ADD_RDISTRIB := SessionLibrary.RingTheory.«RING_ADD_RDISTRIB»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_NEG := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_NEG»
  RING_HOMOMORPHISM_SUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM»
  RING_IDEAL := SessionLibrary.RingTheory.«RING_IDEAL»
  RING_IDEAL_CARRIER := SessionLibrary.RingTheory.«RING_IDEAL_CARRIER»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_PROD := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PROD»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_MONOMORPHISM_EQ_0 := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EQ_0»
  RING_MONOMORPHISM_INJECTIVE_EQ := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INJECTIVE_EQ»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_IN_IDEAL_PROD := SessionANT.IdealArith.«RING_MUL_IN_IDEAL_PROD»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LNEG := SessionLibrary.RingTheory.«RING_MUL_LNEG»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_SETMUL := SessionLibrary.RingTheory.«RING_SETMUL»
  RING_SETMUL_IMAGE_MUL := SessionLibrary.FieldTheory.«RING_SETMUL_IMAGE_MUL»
  RING_SETMUL_SING := SessionLibrary.RingTheory.«RING_SETMUL_SING»
  RING_SPAN_0 := SessionLibrary.FieldTheory.«RING_SPAN_0»
  RING_SPAN_ADD := SessionLibrary.FieldTheory.«RING_SPAN_ADD»
  RING_SPAN_EQ_SELF := SessionLibrary.FieldTheory.«RING_SPAN_EQ_SELF»
  RING_SPAN_IMAGE_IDEAL_GENERATED := SessionLibrary.FieldTheory.«RING_SPAN_IMAGE_IDEAL_GENERATED»
  RING_SPAN_IMAGE_MUL := SessionLibrary.FieldTheory.«RING_SPAN_IMAGE_MUL»
  RING_SPAN_INC := SessionLibrary.FieldTheory.«RING_SPAN_INC»
  RING_SPAN_MINIMAL := SessionLibrary.FieldTheory.«RING_SPAN_MINIMAL»
  RING_SPAN_MONO := SessionLibrary.FieldTheory.«RING_SPAN_MONO»
  RING_SPAN_MUL := SessionLibrary.FieldTheory.«RING_SPAN_MUL»
  RING_SPAN_SETMUL_ASSOC := SessionLibrary.FieldTheory.«RING_SPAN_SETMUL_ASSOC»
  RING_SPAN_SETMUL_SPAN := SessionLibrary.FieldTheory.«RING_SPAN_SETMUL_SPAN»
  RING_SPAN_SETMUL_SYM := SessionLibrary.FieldTheory.«RING_SPAN_SETMUL_SYM»
  RING_SPAN_SING_IMAGE := SessionLibrary.FieldTheory.«RING_SPAN_SING_IMAGE»
  RING_SPAN_SUBSET := SessionLibrary.FieldTheory.«RING_SPAN_SUBSET»
  RING_SPAN_SUM := SessionLibrary.FieldTheory.«RING_SPAN_SUM»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_RMUL := SessionLibrary.RingTheory.«RING_SUM_RMUL»
  RING_UNIT_1 := SessionLibrary.RingTheory.«RING_UNIT_1»
  RING_UNIT_IN_CARRIER := SessionLibrary.RingTheory.«RING_UNIT_IN_CARRIER»
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBRING_RING_IMAGE := SessionLibrary.RingTheory.«SUBRING_RING_IMAGE»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_ANTISYM_EQ := Session.SUBSET_ANTISYM_EQ
  SUBSET_UNIV := Session.SUBSET_UNIV
  UNIT_GROUP := SessionLibrary.RingGroups.«UNIT_GROUP»
  abelian_group := SessionLibrary.GroupTheory.«abelian_group»
  frag_support := SessionLibrary.Frag.«frag_support»
  frag_tybij := SessionLibrary.Frag.«frag_tybij»
  group_carrier := SessionLibrary.GroupTheory.«group_carrier»
  group_div := SessionLibrary.GroupTheory.«group_div»
  group_epimorphism := SessionLibrary.GroupTheory.«group_epimorphism»
  group_exactness := SessionLibrary.GroupTheory.«group_exactness»
  group_id := SessionLibrary.GroupTheory.«group_id»
  group_image := SessionLibrary.GroupTheory.«group_image»
  group_inv := SessionLibrary.GroupTheory.«group_inv»
  group_kernel := SessionLibrary.GroupTheory.«group_kernel»
  group_monomorphism := SessionLibrary.GroupTheory.«group_monomorphism»
  group_mul := SessionLibrary.GroupTheory.«group_mul»
  group_tybij := SessionLibrary.GroupTheory.«group_tybij»
  ideal_classes := SessionANT.Classgroup.«ideal_classes»
  isomorphic_group := SessionLibrary.GroupTheory.«isomorphic_group»
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM
  principal_ideal := SessionLibrary.RingTheory.«principal_ideal»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_image := SessionLibrary.RingTheory.«ring_image»
  ring_setmul := SessionLibrary.RingTheory.«ring_setmul»
  ring_sub := SessionLibrary.RingTheory.«ring_sub»

/-- What fractional_ideals.ml uses from Session. -/
def deps : HolANT.FractionalIdeals.FractionalIdealsDeps where
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

/- The bundles, in fractional_ideals.ml order. -/
initialize BFractionalIdeals01 : HolANT.FractionalIdeals.FractionalIdeals01 ←
  ioB "setupFractionalIdeals01" (HolANT.FractionalIdeals.setupFractionalIdeals01 deps).run
initialize BFractionalIdeals02 : HolANT.FractionalIdeals.FractionalIdeals02 ←
  ioB "setupFractionalIdeals02" (HolANT.FractionalIdeals.setupFractionalIdeals02 deps BFractionalIdeals01).run
initialize BFractionalIdeals03 : HolANT.FractionalIdeals.FractionalIdeals03 ←
  ioB "setupFractionalIdeals03" (HolANT.FractionalIdeals.setupFractionalIdeals03 deps BFractionalIdeals01 BFractionalIdeals02).run

-- FractionalIdeals01
def fractional_ideal : thm := BFractionalIdeals01.fractional_ideal
def fractional_ideal_inv : thm := BFractionalIdeals01.fractional_ideal_inv
def FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS : thm := BFractionalIdeals01.FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS
def FRACTIONAL_IDEAL_IMP_SUBSET : thm := BFractionalIdeals01.FRACTIONAL_IDEAL_IMP_SUBSET
def FRACTIONAL_IDEAL_IMP_NONZERO : thm := BFractionalIdeals01.FRACTIONAL_IDEAL_IMP_NONZERO
def IN_FRACTIONAL_IDEAL_0 : thm := BFractionalIdeals01.IN_FRACTIONAL_IDEAL_0
def IN_FRACTIONAL_IDEAL_ADD : thm := BFractionalIdeals01.IN_FRACTIONAL_IDEAL_ADD
def IN_FRACTIONAL_IDEAL_LMUL : thm := BFractionalIdeals01.IN_FRACTIONAL_IDEAL_LMUL
def IN_FRACTIONAL_IDEAL_NEG : thm := BFractionalIdeals01.IN_FRACTIONAL_IDEAL_NEG
def IN_FRACTIONAL_IDEAL_SUB : thm := BFractionalIdeals01.IN_FRACTIONAL_IDEAL_SUB
def FRACTIONAL_IDEAL_RING_SPAN : thm := BFractionalIdeals01.FRACTIONAL_IDEAL_RING_SPAN
def RING_IDEAL_IMP_FRACTIONAL_IDEAL : thm := BFractionalIdeals01.RING_IDEAL_IMP_FRACTIONAL_IDEAL
def FRACTIONAL_IDEAL_CARRIER : thm := BFractionalIdeals01.FRACTIONAL_IDEAL_CARRIER
def FRACTIONAL_IDEAL_IMAGE_MUL : thm := BFractionalIdeals01.FRACTIONAL_IDEAL_IMAGE_MUL
def FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV : thm := BFractionalIdeals01.FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV
def FRACTIONAL_IDEAL_DENOMINATOR : thm := BFractionalIdeals01.FRACTIONAL_IDEAL_DENOMINATOR
def RING_SPAN_SETMUL_IMAGE_IDEAL_PROD : thm := BFractionalIdeals01.RING_SPAN_SETMUL_IMAGE_IDEAL_PROD
def FRACTIONAL_IDEAL_INTEGRAL : thm := BFractionalIdeals01.FRACTIONAL_IDEAL_INTEGRAL
def FRACTIONAL_IDEAL_SCALED_IDEAL : thm := BFractionalIdeals01.FRACTIONAL_IDEAL_SCALED_IDEAL
def FRACTIONAL_IDEAL_SCALED_IDEAL_EQ : thm := BFractionalIdeals01.FRACTIONAL_IDEAL_SCALED_IDEAL_EQ
def FRACTIONAL_IDEAL_MUL : thm := BFractionalIdeals01.FRACTIONAL_IDEAL_MUL
def FRACTIONAL_IDEAL_MUL_LID : thm := BFractionalIdeals01.FRACTIONAL_IDEAL_MUL_LID
def DEDEKIND_FRACTIONAL_IDEAL_INVERTIBLE : thm := BFractionalIdeals01.DEDEKIND_FRACTIONAL_IDEAL_INVERTIBLE
def DEDEKIND_FRACTIONAL_IDEAL_MUL_INV : thm := BFractionalIdeals01.DEDEKIND_FRACTIONAL_IDEAL_MUL_INV
def fractional_ideal_group : thm := BFractionalIdeals01.fractional_ideal_group

-- FractionalIdeals02
def FRACTIONAL_IDEAL_GROUP : thm := BFractionalIdeals02.FRACTIONAL_IDEAL_GROUP
def ABELIAN_FRACTIONAL_IDEAL_GROUP : thm := BFractionalIdeals02.ABELIAN_FRACTIONAL_IDEAL_GROUP
def FRACTIONAL_IDEAL_SCALED_IDEAL_COMPARE : thm := BFractionalIdeals02.FRACTIONAL_IDEAL_SCALED_IDEAL_COMPARE
def fractional_ideal_valuation : thm := BFractionalIdeals02.fractional_ideal_valuation
def FRACTIONAL_IDEAL_VALUATION : thm := BFractionalIdeals02.FRACTIONAL_IDEAL_VALUATION
def FRACTIONAL_IDEAL_VALUATION_IMAGE : thm := BFractionalIdeals02.FRACTIONAL_IDEAL_VALUATION_IMAGE
def FRACTIONAL_IDEAL_VALUATION_CARRIER : thm := BFractionalIdeals02.FRACTIONAL_IDEAL_VALUATION_CARRIER
def FRACTIONAL_IDEAL_SCALED_IDEAL_MUL : thm := BFractionalIdeals02.FRACTIONAL_IDEAL_SCALED_IDEAL_MUL
def FRACTIONAL_IDEAL_COMMON_DENOMINATOR : thm := BFractionalIdeals02.FRACTIONAL_IDEAL_COMMON_DENOMINATOR
def FRACTIONAL_IDEAL_PRINCIPAL : thm := BFractionalIdeals02.FRACTIONAL_IDEAL_PRINCIPAL
def FRACTIONAL_IDEAL_VALUATION_MUL : thm := BFractionalIdeals02.FRACTIONAL_IDEAL_VALUATION_MUL
def FRACTIONAL_IDEAL_VALUATION_INV : thm := BFractionalIdeals02.FRACTIONAL_IDEAL_VALUATION_INV
def FRACTIONAL_IDEAL_VALUATION_PRINCIPAL : thm := BFractionalIdeals02.FRACTIONAL_IDEAL_VALUATION_PRINCIPAL
def FRACTIONAL_IDEAL_VALUATION_FINITE : thm := BFractionalIdeals02.FRACTIONAL_IDEAL_VALUATION_FINITE
def FRACTIONAL_IDEAL_SUBSET_VALUATION : thm := BFractionalIdeals02.FRACTIONAL_IDEAL_SUBSET_VALUATION
def FRACTIONAL_IDEAL_EQ_VALUATION : thm := BFractionalIdeals02.FRACTIONAL_IDEAL_EQ_VALUATION
def IN_FRACTIONAL_IDEAL_VALUATION : thm := BFractionalIdeals02.IN_FRACTIONAL_IDEAL_VALUATION
def FRACTIONAL_IDEAL_INTEGRAL_VALUATION : thm := BFractionalIdeals02.FRACTIONAL_IDEAL_INTEGRAL_VALUATION
def FRACTIONAL_IDEAL_PRESCRIBED_VALUATIONS : thm := BFractionalIdeals02.FRACTIONAL_IDEAL_PRESCRIBED_VALUATIONS
def GROUP_HOMOMORPHISM_FRACTIONAL_IDEAL_VALUATION : thm := BFractionalIdeals02.GROUP_HOMOMORPHISM_FRACTIONAL_IDEAL_VALUATION
def FRACTIONAL_IDEAL_VALUATION_PRIME : thm := BFractionalIdeals02.FRACTIONAL_IDEAL_VALUATION_PRIME
def FRACTIONAL_IDEAL_VALUATION_ZPOW : thm := BFractionalIdeals02.FRACTIONAL_IDEAL_VALUATION_ZPOW
def FRACTIONAL_IDEAL_VALUATION_PRIME_PRODUCT : thm := BFractionalIdeals02.FRACTIONAL_IDEAL_VALUATION_PRIME_PRODUCT
def DEDEKIND_FRACTIONAL_IDEAL_FACTORIZATION : thm := BFractionalIdeals02.DEDEKIND_FRACTIONAL_IDEAL_FACTORIZATION

-- FractionalIdeals03
def FRACTIONAL_IDEAL_GROUP_FREE_ABELIAN_EXPLICIT : thm := BFractionalIdeals03.FRACTIONAL_IDEAL_GROUP_FREE_ABELIAN_EXPLICIT
def FRACTIONAL_IDEAL_GROUP_FREE_ABELIAN : thm := BFractionalIdeals03.FRACTIONAL_IDEAL_GROUP_FREE_ABELIAN
def GROUP_HOMOMORPHISM_PRINCIPAL_FRACTIONAL_IDEAL : thm := BFractionalIdeals03.GROUP_HOMOMORPHISM_PRINCIPAL_FRACTIONAL_IDEAL
def GROUP_KERNEL_PRINCIPAL_FRACTIONAL_IDEAL : thm := BFractionalIdeals03.GROUP_KERNEL_PRINCIPAL_FRACTIONAL_IDEAL
def FRACTIONAL_IDEAL_PRINCIPAL_SCALED : thm := BFractionalIdeals03.FRACTIONAL_IDEAL_PRINCIPAL_SCALED
def FRACTIONAL_IDEAL_CLASS_EXISTS : thm := BFractionalIdeals03.FRACTIONAL_IDEAL_CLASS_EXISTS
def FRACTIONAL_IDEAL_CLASS_GROUP_EXACT : thm := BFractionalIdeals03.FRACTIONAL_IDEAL_CLASS_GROUP_EXACT
def FRACTIONAL_IDEAL_CLASS_GROUP : thm := BFractionalIdeals03.FRACTIONAL_IDEAL_CLASS_GROUP
def FRACTIONAL_IDEAL_CLASS_PRIME_SUM : thm := BFractionalIdeals03.FRACTIONAL_IDEAL_CLASS_PRIME_SUM
def CLASS_GROUP_SUM_PRIME_CLASSES_EQ_ID : thm := BFractionalIdeals03.CLASS_GROUP_SUM_PRIME_CLASSES_EQ_ID
def IDEAL_CLASS_EQ_SUM_PRIME_CLASSES : thm := BFractionalIdeals03.IDEAL_CLASS_EQ_SUM_PRIME_CLASSES

/-- `needs "ANT/fractional_ideals.ml"`: already done by importing this module. -/
def ensureFractionalIdeals : IO Unit := pure ()

end SessionANT.FractionalIdeals
