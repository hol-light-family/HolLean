/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/discriminant.ml                               . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/Discriminant.lean

  The session half of the discriminant.ml translation: it supplies HolANT.Discriminant's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/discriminant.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.Discriminant
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
import SessionANT.Zlattice
import SessionANT.Integral
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.NormIndex

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.Discriminant

/-- The core theorems discriminant.ml uses. -/
def core1 : HolANT.Discriminant.CoreThms1 where
  ARITH_EQ := Session.ARITH_EQ
  BASIS_COORDINATES_CHANGE_OF_BASIS_INVERSE := SessionLibrary.RingDet.«BASIS_COORDINATES_CHANGE_OF_BASIS_INVERSE»
  BASIS_COORDINATES_EXPAND := SessionLibrary.RingDet.«BASIS_COORDINATES_EXPAND»
  BASIS_COORDINATES_UNIQUE := SessionLibrary.RingDet.«BASIS_COORDINATES_UNIQUE»
  BASIS_DISCRIMINANT_CHANGE_OF_BASIS := SessionLibrary.RingDet.«BASIS_DISCRIMINANT_CHANGE_OF_BASIS»
  BASIS_DISCRIMINANT_NONZERO := SessionLibrary.RingDet.«BASIS_DISCRIMINANT_NONZERO»
  CARD_IMAGE_EQ_INJ := Session.CARD_IMAGE_EQ_INJ
  COND_RAND := Session.COND_RAND
  COND_RATOR := Session.COND_RATOR
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DIVIDES_ONE := Session.DIVIDES_ONE
  EQ_TRANS := Session.EQ_TRANS
  EXP_MONO_EQ := Session.EXP_MONO_EQ
  EXTENSION := Session.EXTENSION
  EXTENSION_LINCOMB_ADD := SessionLibrary.RingDet.«EXTENSION_LINCOMB_ADD»
  EXTENSION_LINCOMB_LMUL := SessionLibrary.RingDet.«EXTENSION_LINCOMB_LMUL»
  EXTENSION_LINCOMB_SUM := SessionLibrary.RingDet.«EXTENSION_LINCOMB_SUM»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FORALL_INT_CASES := Session.FORALL_INT_CASES
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FREE_BASIS_INTEGER_RING_COORDINATES := SessionANT.RingOfIntegers.«FREE_BASIS_INTEGER_RING_COORDINATES»
  FREE_BASIS_INTEGER_RING_SUBRING_GENERATED := SessionANT.RingOfIntegers.«FREE_BASIS_INTEGER_RING_SUBRING_GENERATED»
  FREE_BASIS_IN_CARRIER := SessionLibrary.RingDet.«FREE_BASIS_IN_CARRIER»
  FREE_BASIS_SCALE := SessionLibrary.RingDet.«FREE_BASIS_SCALE»
  FUN_EQ_THM := Session.FUN_EQ_THM
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_0 := Session.HAS_SIZE_0
  HAS_SIZE_CLAUSES := Session.HAS_SIZE_CLAUSES
  HAS_SIZE_IMAGE_INJ := Session.HAS_SIZE_IMAGE_INJ
  IDEAL_GENERATED_SING_ALT := SessionLibrary.RingTheory.«IDEAL_GENERATED_SING_ALT»
  IDEAL_GENERATED_SUBSET := SessionLibrary.RingTheory.«IDEAL_GENERATED_SUBSET»
  IMAGE_EQ := Session.IMAGE_EQ
  IMAGE_o := Session.IMAGE_o
  INTEGER_MOD_RING_CHAR := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CHAR»
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGER_RING_POW := SessionLibrary.RingTheory.«INTEGER_RING_POW»
  INTEGER_RING_SUM := SessionLibrary.RingTheory.«INTEGER_RING_SUM»
  INT_ABS_POS := Session.INT_ABS_POS
  INT_ADD_SUB := Session.INT_ADD_SUB
  INT_COSETS_MATRIX_IMAGE := SessionANT.Zlattice.«INT_COSETS_MATRIX_IMAGE»
  INT_DET_MUL := SessionANT.Zlattice.«INT_DET_MUL»
  INT_DIVIDES_RABS := Session.INT_DIVIDES_RABS
  INT_EQ_MUL_RCANCEL := Session.INT_EQ_MUL_RCANCEL
  INT_MATRIX_IMAGE_IN := SessionANT.Zlattice.«INT_MATRIX_IMAGE_IN»
  INT_MATRIX_MUL_ASSOC := SessionANT.Zlattice.«INT_MATRIX_MUL_ASSOC»
  INT_MUL_EQ_1 := Session.INT_MUL_EQ_1
  INT_MUL_LZERO := Session.INT_MUL_LZERO
  INT_MUL_SYM := Session.INT_MUL_SYM
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_OF_NUM_POW := Session.INT_OF_NUM_POW
  INT_POW2_ABS := Session.INT_POW2_ABS
  INT_POW_EQ_1_IMP := Session.INT_POW_EQ_1_IMP
  INT_SUB_REFL := Session.INT_SUB_REFL
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_RING_IDEAL_RMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_RMUL»
  IN_RING_IDEAL_SUB := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUB»
  IN_RING_IDEAL_SUM := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUM»
  IN_SING := Session.IN_SING
  IN_UNIV := Session.IN_UNIV
  ISUM_DELTA_GEN := SessionLibrary.Isum.«ISUM_DELTA_GEN»
  ISUM_EQ := SessionLibrary.Isum.«ISUM_EQ»
  I_THM := Session.I_THM
  LEFT_AND_EXISTS_THM := Session.LEFT_AND_EXISTS_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_1 := Session.LE_1
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NUMBER_FIELD_DEGREE_POS := SessionANT.Numfield.«NUMBER_FIELD_DEGREE_POS»
  NUMBER_FIELD_FREE_BASIS_DEGREE := SessionANT.Numfield.«NUMBER_FIELD_FREE_BASIS_DEGREE»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_INT_LINCOMB_SANDWICH := SessionANT.Numfield.«NUMBER_FIELD_INT_LINCOMB_SANDWICH»
  NUMBER_FIELD_TRACE_INTEGRAL_BASIS := SessionANT.NormIndex.«NUMBER_FIELD_TRACE_INTEGRAL_BASIS»
  ONE := Session.ONE
  PRIME_1 := SessionLibrary.Prime.«PRIME_1»
  PRIME_COPRIME_EQ := SessionLibrary.Prime.«PRIME_COPRIME_EQ»
  QUOTIENT_RING := SessionLibrary.RingTheory.«QUOTIENT_RING»
  RIGHT_AND_EXISTS_THM := Session.RIGHT_AND_EXISTS_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_COSET_0 := SessionLibrary.RingTheory.«RING_COSET_0»
  RING_COSET_EQ_IDEAL := SessionLibrary.RingTheory.«RING_COSET_EQ_IDEAL»
  RING_COSET_SETADD := SessionLibrary.RingTheory.«RING_COSET_SETADD»
  RING_DET_ADJUGATE_ROWS := SessionLibrary.RingDet.«RING_DET_ADJUGATE_ROWS»
  RING_DET_EQ := SessionLibrary.RingDet.«RING_DET_EQ»
  RING_DET_HOMOMORPHISM := SessionLibrary.RingDet.«RING_DET_HOMOMORPHISM»
  RING_DET_I := SessionLibrary.RingDet.«RING_DET_I»
  RING_DET_MUL := SessionLibrary.RingDet.«RING_DET_MUL»
  RING_DET_TRANSP := SessionLibrary.RingDet.«RING_DET_TRANSP»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_FREE := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE»
  RING_OF_INTEGERS_FREE_BASIS_FIELD := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE_BASIS_FIELD»
  RING_OF_INTEGERS_IDEAL_INTEGER := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_IDEAL_INTEGER»
  RING_OF_INTEGERS_RING_OF_INT_MUL := SessionANT.Numfield.«RING_OF_INTEGERS_RING_OF_INT_MUL»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_0 := SessionLibrary.RingTheory.«RING_OF_INT_0»
  RING_OF_INT_1 := SessionLibrary.RingTheory.«RING_OF_INT_1»
  RING_OF_INT_EQ := SessionLibrary.RingTheory.«RING_OF_INT_EQ»
  RING_OF_INT_EQ_0_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0_CHAR_0»
  RING_OF_INT_EQ_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_CHAR_0»
  RING_OF_INT_IN_RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INT_IN_RING_OF_INTEGERS»
  RING_OF_INT_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_IN_SUBFIELD_GENERATED»
  RING_OF_INT_MUL := SessionLibrary.RingTheory.«RING_OF_INT_MUL»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_INT_POW := SessionLibrary.RingTheory.«RING_OF_INT_POW»
  RING_OF_INT_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_SUBFIELD_GENERATED»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_POW_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_POW_SUBFIELD_GENERATED»
  RING_SETADD := SessionLibrary.RingTheory.«RING_SETADD»
  RING_SETADD_ASSOC := SessionLibrary.RingTheory.«RING_SETADD_ASSOC»
  RING_SETADD_LSUBSET := SessionLibrary.RingTheory.«RING_SETADD_LSUBSET»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_0 := SessionLibrary.RingTheory.«RING_SUM_0»
  RING_SUM_DELTA := SessionLibrary.RingTheory.«RING_SUM_DELTA»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_EQ_0 := SessionLibrary.RingTheory.«RING_SUM_EQ_0»
  RING_SUM_LMUL := SessionLibrary.RingTheory.«RING_SUM_LMUL»
  RING_SUM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_SUM_RING_OF_INTEGERS»
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SIMPLE_IMAGE := Session.SIMPLE_IMAGE
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_ANTISYM_EQ := Session.SUBSET_ANTISYM_EQ
  SUBSET_TRANS := Session.SUBSET_TRANS
  UNWIND_THM2 := Session.UNWIND_THM2
  basis_discriminant := SessionLibrary.RingDet.«basis_discriminant»
  free_basis := SessionLibrary.RingDet.«free_basis»
  ideal_norm := SessionANT.IdealNorm.«ideal_norm»
  int_coprime := Session.int_coprime
  int_cosets := SessionANT.Zlattice.«int_cosets»
  num_coprime := Session.num_coprime
  num_divides := Session.num_divides
  number_field := SessionANT.Numfield.«number_field»
  o_THM := Session.o_THM
  ring_coset := SessionLibrary.RingTheory.«ring_coset»
  ring_setadd := SessionLibrary.RingTheory.«ring_setadd»

/-- What discriminant.ml uses from Session. -/
def deps : HolANT.Discriminant.DiscriminantDeps where
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
  INT_RING t := ExceptT.mk (Session.INT_RING t)
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in discriminant.ml order. -/
initialize BDiscriminant01 : HolANT.Discriminant.Discriminant01 ←
  ioB "setupDiscriminant01" (HolANT.Discriminant.setupDiscriminant01 deps).run
initialize BDiscriminant02 : HolANT.Discriminant.Discriminant02 ←
  ioB "setupDiscriminant02" (HolANT.Discriminant.setupDiscriminant02 deps BDiscriminant01).run

-- Discriminant01
def number_field_discriminant : thm := BDiscriminant01.number_field_discriminant
def NUMBER_FIELD_DISCRIMINANT_BASIS : thm := BDiscriminant01.NUMBER_FIELD_DISCRIMINANT_BASIS
def NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD : thm := BDiscriminant01.NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD
def NUMBER_FIELD_DISCRIMINANT_NONZERO : thm := BDiscriminant01.NUMBER_FIELD_DISCRIMINANT_NONZERO
def FREE_BASIS_INTEGER_RING_LINCOMB : thm := BDiscriminant01.FREE_BASIS_INTEGER_RING_LINCOMB
def INT_MATRIX_SURJECTIVE_MOD_PRIME : thm := BDiscriminant01.INT_MATRIX_SURJECTIVE_MOD_PRIME
def FREE_BASIS_INTEGER_RING_SPAN_INDEX : thm := BDiscriminant01.FREE_BASIS_INTEGER_RING_SPAN_INDEX
def FREE_BASIS_INTEGER_RING_SPAN_COPRIME : thm := BDiscriminant01.FREE_BASIS_INTEGER_RING_SPAN_COPRIME
def NUMBER_FIELD_DISCRIMINANT_CHANGE_OF_BASIS : thm := BDiscriminant01.NUMBER_FIELD_DISCRIMINANT_CHANGE_OF_BASIS
def NUMBER_FIELD_INDEX_DETERMINANT : thm := BDiscriminant01.NUMBER_FIELD_INDEX_DETERMINANT
def NUMBER_FIELD_DISCRIMINANT_INDEX : thm := BDiscriminant01.NUMBER_FIELD_DISCRIMINANT_INDEX

-- Discriminant02
def NUMBER_FIELD_INTEGRAL_BASIS_DISCRIMINANT : thm := BDiscriminant02.NUMBER_FIELD_INTEGRAL_BASIS_DISCRIMINANT
def NUMBER_FIELD_INDEX_COPRIME : thm := BDiscriminant02.NUMBER_FIELD_INDEX_COPRIME
def NUMBER_FIELD_INDEX_COPRIME_DISCRIMINANT : thm := BDiscriminant02.NUMBER_FIELD_INDEX_COPRIME_DISCRIMINANT
def RING_OF_INTEGERS_IDEAL_INT_LINCOMB : thm := BDiscriminant02.RING_OF_INTEGERS_IDEAL_INT_LINCOMB
def NUMBER_FIELD_IDEAL_INTEGRAL_BASIS : thm := BDiscriminant02.NUMBER_FIELD_IDEAL_INTEGRAL_BASIS
def NUMBER_FIELD_IDEAL_DISCRIMINANT : thm := BDiscriminant02.NUMBER_FIELD_IDEAL_DISCRIMINANT
def NUMBER_FIELD_IDEAL_INTEGRAL_BASIS_DISCRIMINANT : thm := BDiscriminant02.NUMBER_FIELD_IDEAL_INTEGRAL_BASIS_DISCRIMINANT

/-- `needs "ANT/discriminant.ml"`: already done by importing this module. -/
def ensureDiscriminant : IO Unit := pure ()

end SessionANT.Discriminant
