/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/classgroup.ml                                 . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/Classgroup.lean

  The session half of the classgroup.ml translation: it supplies HolANT.Classgroup's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/classgroup.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.Classgroup
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
import SessionLibrary.Isum
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.IdealArith
import SessionANT.Integral
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.RingOfIntegers
import SessionANT.NormIndex

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.Classgroup

/-- The core theorems classgroup.ml uses. -/
def core1 : HolANT.Classgroup.CoreThms1 where
  ALGEBRA_NORM_FREE_BASIS := SessionLibrary.RingDet.«ALGEBRA_NORM_FREE_BASIS»
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_EQ_CARD_IMP := SessionLibrary.Card.«CARD_EQ_CARD_IMP»
  CARD_FINITE_CONG := SessionLibrary.Card.«CARD_FINITE_CONG»
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  CARD_SUBSET := Session.CARD_SUBSET
  DEDEKIND_IDEAL_CLASS_COPRIME := SessionANT.DedekindStruct.«DEDEKIND_IDEAL_CLASS_COPRIME»
  DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE := SessionANT.Dedekind.«DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE»
  DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES»
  DEDEKIND_IMP_INTEGRAL_DOMAIN := SessionANT.Dedekind.«DEDEKIND_IMP_INTEGRAL_DOMAIN»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  EQ_C_BIJECTIONS := SessionLibrary.Card.«EQ_C_BIJECTIONS»
  EQ_IMP := Session.EQ_IMP
  EXISTS_IN_IMAGE := Session.EXISTS_IN_IMAGE
  EXTENSION := Session.EXTENSION
  FINITE_CROSS := Session.FINITE_CROSS
  FINITE_IDEALS_SUPERSET := SessionLibrary.RingTheory.«FINITE_IDEALS_SUPERSET»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNIONS := Session.FINITE_UNIONS
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FREE_BASIS_IN_CARRIER := SessionLibrary.RingDet.«FREE_BASIS_IN_CARRIER»
  FUN_EQ_THM := Session.FUN_EQ_THM
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_FUNSPACE := Session.HAS_SIZE_FUNSPACE
  HAS_SIZE_IMAGE_INJ := Session.HAS_SIZE_IMAGE_INJ
  HAS_SIZE_NUMSEG_LE := Session.HAS_SIZE_NUMSEG_LE
  HAS_SIZE_NUMSEG_LT := Session.HAS_SIZE_NUMSEG_LT
  IDEAL_CLASS_PRINCIPAL := SessionANT.DedekindStruct.«IDEAL_CLASS_PRINCIPAL»
  IDEAL_CLASS_REFL := SessionANT.DedekindStruct.«IDEAL_CLASS_REFL»
  IDEAL_CLASS_SYM := SessionANT.DedekindStruct.«IDEAL_CLASS_SYM»
  IDEAL_CLASS_TRANS := SessionANT.DedekindStruct.«IDEAL_CLASS_TRANS»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_NORM_GT_1 := SessionANT.IdealNorm.«IDEAL_NORM_GT_1»
  IDEAL_NORM_IN_IDEAL := SessionANT.IdealNorm.«IDEAL_NORM_IN_IDEAL»
  IDEAL_NORM_POS := SessionANT.IdealNorm.«IDEAL_NORM_POS»
  IDEAL_PROD_ASSOC := SessionANT.IdealArith.«IDEAL_PROD_ASSOC»
  IDEAL_PROD_COMM := SessionANT.IdealArith.«IDEAL_PROD_COMM»
  IDEAL_PROD_EQ_ZERO := SessionANT.IdealArith.«IDEAL_PROD_EQ_ZERO»
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGER_RING_SUM := SessionLibrary.RingTheory.«INTEGER_RING_SUM»
  INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING»
  INTEGRAL_DOMAIN_RING_OF_INTEGERS := SessionANT.Numfield.«INTEGRAL_DOMAIN_RING_OF_INTEGERS»
  INT_ABS_MUL := Session.INT_ABS_MUL
  INT_ABS_POS := Session.INT_ABS_POS
  INT_DET_BOUND := SessionANT.Zlattice.«INT_DET_BOUND»
  INT_LE_LMUL := Session.INT_LE_LMUL
  INT_LE_LMUL_EQ := Session.INT_LE_LMUL_EQ
  INT_LE_MUL := Session.INT_LE_MUL
  INT_LE_MUL2 := Session.INT_LE_MUL2
  INT_LE_TRANS := Session.INT_LE_TRANS
  INT_MUL_ASSOC := Session.INT_MUL_ASSOC
  INT_MUL_SYM := Session.INT_MUL_SYM
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LE := Session.INT_OF_NUM_LE
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_OF_NUM_POW := Session.INT_OF_NUM_POW
  INT_POS := Session.INT_POS
  INT_POW_LE := Session.INT_POW_LE
  INT_POW_MUL := Session.INT_POW_MUL
  INT_SUB_0 := Session.INT_SUB_0
  IN_CROSS := Session.IN_CROSS
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_CLASS := SessionANT.DedekindStruct.«IN_IDEAL_CLASS»
  IN_IDEAL_CLASS_ISOMORPHIC_IMAGE := SessionANT.DedekindStruct.«IN_IDEAL_CLASS_ISOMORPHIC_IMAGE»
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_IMAGE := Session.IN_IMAGE
  IN_NUMSEG := Session.IN_NUMSEG
  IN_SING := Session.IN_SING
  IN_UNIONS := Session.IN_UNIONS
  IN_UNIV := Session.IN_UNIV
  ISOMORPHIC_RING_RING_OF_INTEGERS := SessionANT.Numfield.«ISOMORPHIC_RING_RING_OF_INTEGERS»
  ISUM_ABS_BOUND := SessionLibrary.Isum.«ISUM_ABS_BOUND»
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONO_EXISTS := Session.MONO_EXISTS
  MUL_MATRIX_RING_SUM := SessionLibrary.RingDet.«MUL_MATRIX_RING_SUM»
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NUMBER_FIELD_DEGREE_POS := SessionANT.Numfield.«NUMBER_FIELD_DEGREE_POS»
  NUMBER_FIELD_IDEAL_NORM_MUL_Q := SessionANT.NormIndex.«NUMBER_FIELD_IDEAL_NORM_MUL_Q»
  NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q := SessionANT.NormIndex.«NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_NORM_INTEGRAL_BASIS := SessionANT.NormIndex.«NUMBER_FIELD_NORM_INTEGRAL_BASIS»
  NUM_ROOT_FLOOR := SessionANT.Algmisc.«NUM_ROOT_FLOOR»
  PID := SessionLibrary.RingTheory.«PID»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRINCIPAL_IDEAL_0 := SessionLibrary.RingTheory.«PRINCIPAL_IDEAL_0»
  PRINCIPAL_IDEAL_CLASS := SessionANT.DedekindStruct.«PRINCIPAL_IDEAL_CLASS»
  PSUBSET := Session.PSUBSET
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
  RING_CHAR_EQ_0 := SessionLibrary.RingTheory.«RING_CHAR_EQ_0»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_IDEAL_CARRIER := SessionLibrary.RingTheory.«RING_IDEAL_CARRIER»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_PROD := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PROD»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_INT_LINCOMB := SessionANT.Numfield.«RING_INT_LINCOMB»
  RING_ISOMORPHISMS_ISOMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISMS_ISOMORPHISM»
  RING_ISOMORPHISMS_SYM := SessionLibrary.RingTheory.«RING_ISOMORPHISMS_SYM»
  RING_MONOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INTEGER_RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_FREE := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE»
  RING_OF_INTEGERS_FREE_BASIS_FIELD := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE_BASIS_FIELD»
  RING_OF_INT_IN_RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INT_IN_RING_OF_INTEGERS»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  SING_SUBSET := Session.SING_SUBSET
  SUBSET := Session.SUBSET
  UPPER_BOUND_FINITE_SET_INT := SessionANT.Algmisc.«UPPER_BOUND_FINITE_SET_INT»
  free_basis := SessionLibrary.RingDet.«free_basis»
  ideal_norm := SessionANT.IdealNorm.«ideal_norm»
  isomorphic_ring := SessionLibrary.RingTheory.«isomorphic_ring»
  number_field := SessionANT.Numfield.«number_field»
  prime_ideal := SessionLibrary.RingTheory.«prime_ideal»
  proper_ideal := SessionLibrary.RingTheory.«proper_ideal»
  ring_isomorphism := SessionLibrary.RingTheory.«ring_isomorphism»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»
  trivial_ring := SessionLibrary.RingTheory.«trivial_ring»

/-- What classgroup.ml uses from Session. -/
def deps : HolANT.Classgroup.ClassgroupDeps where
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

/- The bundles, in classgroup.ml order. -/
initialize BClassgroup : HolANT.Classgroup.Classgroup ←
  ioB "setupClassgroup" (HolANT.Classgroup.setupClassgroup deps).run

-- Classgroup
def ideal_classes : thm := BClassgroup.ideal_classes
def class_number : thm := BClassgroup.class_number
def IDEAL_CLASS_EQ : thm := BClassgroup.IDEAL_CLASS_EQ
def INTEGRAL_DOMAIN_UNIT_IDEAL : thm := BClassgroup.INTEGRAL_DOMAIN_UNIT_IDEAL
def DEDEKIND_PID_EQ_CLASS_NUMBER_1 : thm := BClassgroup.DEDEKIND_PID_EQ_CLASS_NUMBER_1
def FREE_BASIS_IDEAL_BOX_PRINCIPLE : thm := BClassgroup.FREE_BASIS_IDEAL_BOX_PRINCIPLE
def NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM : thm := BClassgroup.NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM
def NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM : thm := BClassgroup.NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM
def NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2 : thm := BClassgroup.NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2
def FREE_BASIS_NORM_BOUND : thm := BClassgroup.FREE_BASIS_NORM_BOUND
def NUMBER_FIELD_IDEAL_SMALL_ELEMENT : thm := BClassgroup.NUMBER_FIELD_IDEAL_SMALL_ELEMENT
def NUMBER_FIELD_IDEAL_CLASS_BOUND_EXPLICIT : thm := BClassgroup.NUMBER_FIELD_IDEAL_CLASS_BOUND_EXPLICIT
def NUMBER_FIELD_IDEAL_CLASS_BOUND : thm := BClassgroup.NUMBER_FIELD_IDEAL_CLASS_BOUND
def NUMBER_FIELD_CLASS_GROUP_FINITE : thm := BClassgroup.NUMBER_FIELD_CLASS_GROUP_FINITE
def NUMBER_FIELD_CLASS_NUMBER_POS : thm := BClassgroup.NUMBER_FIELD_CLASS_NUMBER_POS
def NUMBER_FIELD_PID_EQ_CLASS_NUMBER_1 : thm := BClassgroup.NUMBER_FIELD_PID_EQ_CLASS_NUMBER_1
def NUMBER_FIELD_IDEAL_CLASS_COPRIME : thm := BClassgroup.NUMBER_FIELD_IDEAL_CLASS_COPRIME
def IDEAL_CLASS_ISOMORPHIC_IMAGE : thm := BClassgroup.IDEAL_CLASS_ISOMORPHIC_IMAGE
def ISOMORPHIC_RING_IDEAL_CLASSES : thm := BClassgroup.ISOMORPHIC_RING_IDEAL_CLASSES
def ISOMORPHIC_RING_CLASS_NUMBER : thm := BClassgroup.ISOMORPHIC_RING_CLASS_NUMBER
def NUMBER_FIELD_CLASS_NUMBER_ISOMORPHIC : thm := BClassgroup.NUMBER_FIELD_CLASS_NUMBER_ISOMORPHIC

/-- `needs "ANT/classgroup.ml"`: already done by importing this module. -/
def ensureClassgroup : IO Unit := pure ()

end SessionANT.Classgroup
