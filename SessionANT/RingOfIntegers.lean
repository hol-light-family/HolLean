/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/ring_of_integers.ml                           . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/RingOfIntegers.lean

  The session half of the ring_of_integers.ml translation: it supplies HolANT.RingOfIntegers's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/ring_of_integers.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.RingOfIntegers
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
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.RingOfIntegers

/-- The core theorems ring_of_integers.ml uses. -/
def core1 : HolANT.RingOfIntegers.CoreThms1 where
  BASIS_COORDINATES := SessionLibrary.RingDet.«BASIS_COORDINATES»
  BASIS_DISCRIMINANT_NONZERO := SessionLibrary.RingDet.«BASIS_DISCRIMINANT_NONZERO»
  BASIS_DISCRIMINANT_TIMES_COORD := SessionLibrary.RingDet.«BASIS_DISCRIMINANT_TIMES_COORD»
  CARD_EQ_IMAGES := SessionLibrary.Card.«CARD_EQ_IMAGES»
  CARD_HAS_SIZE_CONG := SessionLibrary.Card.«CARD_HAS_SIZE_CONG»
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  CARRIER_SUBRING_GENERATED_SUBRING := SessionLibrary.RingTheory.«CARRIER_SUBRING_GENERATED_SUBRING»
  COND_RAND := Session.COND_RAND
  COUNTABLE_IMAGE := SessionLibrary.Card.«COUNTABLE_IMAGE»
  COUNTABLE_RESTRICTED_FUNSPACE := SessionLibrary.Card.«COUNTABLE_RESTRICTED_FUNSPACE»
  COUNTABLE_SUBSET := SessionLibrary.Card.«COUNTABLE_SUBSET»
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EQ_IMP := Session.EQ_IMP
  EQ_TRANS := Session.EQ_TRANS
  EXTENSION := Session.EXTENSION
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FIELD_QUOTIENT_RING := SessionLibrary.RingTheory.«FIELD_QUOTIENT_RING»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_IMP_COUNTABLE := SessionLibrary.Card.«FINITE_IMP_COUNTABLE»
  FINITE_INTEGRAL_DOMAIN_IMP_FIELD := SessionLibrary.RingTheory.«FINITE_INTEGRAL_DOMAIN_IMP_FIELD»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_QUOTIENT_RING_MONO := SessionANT.IdealNorm.«FINITE_QUOTIENT_RING_MONO»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FREE_BASIS_PRIME_SUBFIELD_INT_LINCOMB := SessionANT.Numfield.«FREE_BASIS_PRIME_SUBFIELD_INT_LINCOMB»
  FUN_EQ_THM := Session.FUN_EQ_THM
  HAS_SIZE := Session.HAS_SIZE
  IDEAL_GENERATED_INC := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_GENERATED_SING_ALT := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING_ALT»
  IMAGE_EQ := Session.IMAGE_EQ
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGER_RING_POW := SessionLibrary.RingTheory.«INTEGER_RING_POW»
  INTEGRALLY_CLOSED_INTEGRAL_CLOSURE := SessionANT.Integral.«INTEGRALLY_CLOSED_INTEGRAL_CLOSURE»
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_QUOTIENT_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_QUOTIENT_RING»
  INTEGRAL_DOMAIN_RING_OF_INTEGERS := SessionANT.Numfield.«INTEGRAL_DOMAIN_RING_OF_INTEGERS»
  INTEGRAL_ELEMENT_EXPLICIT := SessionANT.Integral.«INTEGRAL_ELEMENT_EXPLICIT»
  INT_ABS_POS := Session.INT_ABS_POS
  INT_ABS_POW := Session.INT_ABS_POW
  INT_COSETS_MATRIX_IMAGE := SessionANT.Zlattice.«INT_COSETS_MATRIX_IMAGE»
  INT_COUNTABLE := SessionLibrary.Card.«INT_COUNTABLE»
  INT_LATTICE_MATRIX_IMAGE := SessionANT.Zlattice.«INT_LATTICE_MATRIX_IMAGE»
  INT_MUL_LZERO := Session.INT_MUL_LZERO
  INT_MUL_RID := Session.INT_MUL_RID
  INT_MUL_RZERO := Session.INT_MUL_RZERO
  INT_POW_EQ_0 := Session.INT_POW_EQ_0
  INT_SUB_REFL := Session.INT_SUB_REFL
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_ADD := SessionLibrary.RingTheory.«IN_RING_IDEAL_ADD»
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_RING_IDEAL_RMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_RMUL»
  IN_RING_IDEAL_SUB := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUB»
  IN_RING_IDEAL_SUM := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUM»
  IN_SUBRING_ADD := SessionLibrary.RingTheory.«IN_SUBRING_ADD»
  IN_SUBRING_INT := SessionLibrary.RingTheory.«IN_SUBRING_INT»
  IN_SUBRING_MUL := SessionLibrary.RingTheory.«IN_SUBRING_MUL»
  IN_SUBRING_NEG := SessionLibrary.RingTheory.«IN_SUBRING_NEG»
  IN_SUBRING_POW := SessionLibrary.RingTheory.«IN_SUBRING_POW»
  IN_SUBRING_SUB := SessionLibrary.RingTheory.«IN_SUBRING_SUB»
  IN_SUBRING_SUM := SessionLibrary.RingTheory.«IN_SUBRING_SUM»
  IN_UNIV := Session.IN_UNIV
  ISUM_DELTA_GEN := SessionLibrary.Isum.«ISUM_DELTA_GEN»
  I_THM := Session.I_THM
  LT := Session.LT
  LT_0 := Session.LT_0
  LT_REFL := Session.LT_REFL
  LT_SUC := Session.LT_SUC
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_SUC := Session.NOT_SUC
  NUMBER_FIELD_DEGREE_POS := SessionANT.Numfield.«NUMBER_FIELD_DEGREE_POS»
  NUMBER_FIELD_FREE_BASIS_DEGREE := SessionANT.Numfield.«NUMBER_FIELD_FREE_BASIS_DEGREE»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_INTEGRAL_FREE_BASIS := SessionANT.Numfield.«NUMBER_FIELD_INTEGRAL_FREE_BASIS»
  NUMBER_FIELD_INTEGRAL_MULTIPLE := SessionANT.Numfield.«NUMBER_FIELD_INTEGRAL_MULTIPLE»
  NUMBER_FIELD_TRACE_INTEGRAL_Q := SessionANT.Numfield.«NUMBER_FIELD_TRACE_INTEGRAL_Q»
  NUM_OF_INT_POW := Session.NUM_OF_INT_POW
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRIME_SUBRING := SessionLibrary.RingTheory.«PRIME_SUBRING»
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_CARRIER_SUBFIELD_GENERATED_SUBSET := SessionLibrary.FieldTheory.«RING_CARRIER_SUBFIELD_GENERATED_SUBSET»
  RING_CHAR_EQ_0 := SessionLibrary.RingTheory.«RING_CHAR_EQ_0»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_DET_DIAGONAL := SessionLibrary.RingDet.«RING_DET_DIAGONAL»
  RING_DET_SUBRING := SessionLibrary.RingDet.«RING_DET_SUBRING»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_INT_LINCOMB := SessionANT.Numfield.«RING_INT_LINCOMB»
  RING_INT_LINCOMB_SANDWICH := SessionANT.Numfield.«RING_INT_LINCOMB_SANDWICH»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_CARRIER := SessionANT.Numfield.«RING_OF_INTEGERS_CARRIER»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_0 := SessionLibrary.RingTheory.«RING_OF_INT_0»
  RING_OF_INT_EQ_0_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0_CHAR_0»
  RING_OF_INT_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_IN_SUBFIELD_GENERATED»
  RING_OF_INT_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_SUBFIELD_GENERATED»
  RING_OF_NUM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_NUM_SUBFIELD_GENERATED»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_PRODUCT_CONST := SessionLibrary.RingTheory.«RING_PRODUCT_CONST»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_CLAUSES := SessionLibrary.RingTheory.«RING_SUM_CLAUSES»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_IMAGE := SessionLibrary.RingTheory.«RING_SUM_IMAGE»
  RING_SUM_LMUL := SessionLibrary.RingTheory.«RING_SUM_LMUL»
  RING_SUM_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_SUM_SUBRING_GENERATED»
  SIMPLE_IMAGE_GEN := Session.SIMPLE_IMAGE_GEN
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_UNIV := Session.SUBSET_UNIV
  SUC_INJ := Session.SUC_INJ
  basis_discriminant := SessionLibrary.RingDet.«basis_discriminant»
  dedekind_domain := SessionANT.Dedekind.«dedekind_domain»
  finitely_generated_ideal := SessionLibrary.RingTheory.«finitely_generated_ideal»
  free_basis := SessionLibrary.RingDet.«free_basis»
  ideal_norm := SessionANT.IdealNorm.«ideal_norm»
  int_cosets := SessionANT.Zlattice.«int_cosets»
  int_lattice := SessionANT.Zlattice.«int_lattice»
  int_matrix_image := SessionANT.Zlattice.«int_matrix_image»
  noetherian_ring := SessionLibrary.RingTheory.«noetherian_ring»
  number_field := SessionANT.Numfield.«number_field»
  o_DEF := Session.o_DEF
  ring_of_integers := SessionANT.Numfield.«ring_of_integers»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  subring_of := SessionLibrary.RingTheory.«subring_of»

/-- What ring_of_integers.ml uses from Session. -/
def deps : HolANT.RingOfIntegers.RingOfIntegersDeps where
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

/- The bundles, in ring_of_integers.ml order. -/
initialize BRingOfIntegers01 : HolANT.RingOfIntegers.RingOfIntegers01 ←
  ioB "setupRingOfIntegers01" (HolANT.RingOfIntegers.setupRingOfIntegers01 deps).run
initialize BRingOfIntegers02 : HolANT.RingOfIntegers.RingOfIntegers02 ←
  ioB "setupRingOfIntegers02" (HolANT.RingOfIntegers.setupRingOfIntegers02 deps BRingOfIntegers01).run

-- RingOfIntegers01
def QUOTIENT_RING_HAS_SIZE_INT_LINEAR : thm := BRingOfIntegers01.QUOTIENT_RING_HAS_SIZE_INT_LINEAR
def NOETHERIAN_RING_INT_LINEAR : thm := BRingOfIntegers01.NOETHERIAN_RING_INT_LINEAR
def QUOTIENT_RING_INTEGER_INT_LINEAR : thm := BRingOfIntegers01.QUOTIENT_RING_INTEGER_INT_LINEAR
def FREE_BASIS_INTEGER_RING_SUBRING_GENERATED : thm := BRingOfIntegers01.FREE_BASIS_INTEGER_RING_SUBRING_GENERATED
def FREE_BASIS_QUOTIENT_RING_HAS_SIZE : thm := BRingOfIntegers01.FREE_BASIS_QUOTIENT_RING_HAS_SIZE
def FREE_BASIS_INTEGER_RING_COORDINATES : thm := BRingOfIntegers01.FREE_BASIS_INTEGER_RING_COORDINATES
def FREE_BASIS_IMP_NOETHERIAN_RING : thm := BRingOfIntegers01.FREE_BASIS_IMP_NOETHERIAN_RING
def FREE_BASIS_QUOTIENT_RING_INTEGER : thm := BRingOfIntegers01.FREE_BASIS_QUOTIENT_RING_INTEGER
def RING_OF_INTEGERS_DISCRIMINANT : thm := BRingOfIntegers01.RING_OF_INTEGERS_DISCRIMINANT
def RING_OF_INTEGERS_FREE : thm := BRingOfIntegers01.RING_OF_INTEGERS_FREE
def COUNTABLE_RING_OF_INTEGERS : thm := BRingOfIntegers01.COUNTABLE_RING_OF_INTEGERS
def RING_OF_INTEGERS_FREE_BASIS_FIELD : thm := BRingOfIntegers01.RING_OF_INTEGERS_FREE_BASIS_FIELD
def NOETHERIAN_RING_OF_INTEGERS : thm := BRingOfIntegers01.NOETHERIAN_RING_OF_INTEGERS
def INTEGRALLY_CLOSED_RING_OF_INTEGERS : thm := BRingOfIntegers01.INTEGRALLY_CLOSED_RING_OF_INTEGERS
def RING_OF_INTEGERS_IDEAL_INTEGER : thm := BRingOfIntegers01.RING_OF_INTEGERS_IDEAL_INTEGER
def RING_OF_INTEGERS_FINITE_QUOTIENT : thm := BRingOfIntegers01.RING_OF_INTEGERS_FINITE_QUOTIENT
def RING_OF_INTEGERS_FINITE_RESIDUE_FIELDS : thm := BRingOfIntegers01.RING_OF_INTEGERS_FINITE_RESIDUE_FIELDS
def RING_OF_INTEGERS_IDEAL_NORM_INTEGER : thm := BRingOfIntegers01.RING_OF_INTEGERS_IDEAL_NORM_INTEGER

-- RingOfIntegers02
def DEDEKIND_RING_OF_INTEGERS : thm := BRingOfIntegers02.DEDEKIND_RING_OF_INTEGERS

/-- `needs "ANT/ring_of_integers.ml"`: already done by importing this module. -/
def ensureRingOfIntegers : IO Unit := pure ()

end SessionANT.RingOfIntegers
