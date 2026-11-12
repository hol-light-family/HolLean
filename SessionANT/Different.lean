/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/different.ml                                  . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/Different.lean

  The session half of the different.ml translation: it supplies HolANT.Different's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/different.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.Different
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
import SessionANT.IdealArith
import SessionANT.Integral
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.PrimeSplit
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.NfValuation
import SessionANT.Integrality

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.Different

/-- The core theorems different.ml uses. -/
def core1 : HolANT.Different.CoreThms1 where
  ALGEBRA_TRACE_ADD := SessionLibrary.RingDet.«ALGEBRA_TRACE_ADD»
  ALGEBRA_TRACE_NORM_EQ_IMAGE := SessionLibrary.RingDet.«ALGEBRA_TRACE_NORM_EQ_IMAGE»
  ALGEBRA_TRACE_NORM_IN_CARRIER := SessionLibrary.RingDet.«ALGEBRA_TRACE_NORM_IN_CARRIER»
  BASIS_COORDINATES_EXPAND := SessionLibrary.RingDet.«BASIS_COORDINATES_EXPAND»
  BASIS_COORDINATES_IN_CARRIER := SessionLibrary.RingDet.«BASIS_COORDINATES_IN_CARRIER»
  BASIS_DISCRIMINANT_NONZERO := SessionLibrary.RingDet.«BASIS_DISCRIMINANT_NONZERO»
  BASIS_DISCRIMINANT_TIMES_COORD := SessionLibrary.RingDet.«BASIS_DISCRIMINANT_TIMES_COORD»
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT := SessionANT.Dedekind.«DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  EQ_MULT_RCANCEL := Session.EQ_MULT_RCANCEL
  EQ_TRANS := Session.EQ_TRANS
  EXP := Session.EXP
  EXP_EQ_0 := Session.EXP_EQ_0
  EXTENSION := Session.EXTENSION
  EXTENSION_DEGREE_EQ_0 := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_EQ_0»
  EXTENSION_LINCOMB_LMUL := SessionLibrary.RingDet.«EXTENSION_LINCOMB_LMUL»
  FIELD_EXTENSION_IMP_MONOMORPHISM := SessionLibrary.FieldTheory.«FIELD_EXTENSION_IMP_MONOMORPHISM»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FIELD_UNIT := SessionLibrary.RingTheory.«FIELD_UNIT»
  FINITE_EXTENSION_FREE_BASIS := SessionLibrary.FieldTheory.«FINITE_EXTENSION_FREE_BASIS»
  FINITE_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_FIELD_EXTENSION»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FREE_BASIS_EXTENSION_DEGREE := SessionLibrary.FieldTheory.«FREE_BASIS_EXTENSION_DEGREE»
  FREE_BASIS_INTEGER_RING_SPAN_INDEX := SessionANT.Discriminant.«FREE_BASIS_INTEGER_RING_SPAN_INDEX»
  FREE_BASIS_IN_CARRIER := SessionLibrary.RingDet.«FREE_BASIS_IN_CARRIER»
  FREE_BASIS_SCALE := SessionLibrary.RingDet.«FREE_BASIS_SCALE»
  HAS_SIZE := Session.HAS_SIZE
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_NORM_CARRIER := SessionANT.IdealNorm.«IDEAL_NORM_CARRIER»
  IDEAL_NORM_GT_1 := SessionANT.IdealNorm.«IDEAL_NORM_GT_1»
  IDEAL_PROD_COMM := SessionANT.IdealArith.«IDEAL_PROD_COMM»
  IDEAL_PROD_MINIMAL := SessionANT.IdealArith.«IDEAL_PROD_MINIMAL»
  IMP_CONJ := Session.IMP_CONJ
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGER_RING_POW := SessionLibrary.RingTheory.«INTEGER_RING_POW»
  INTEGER_RING_SUM := SessionLibrary.RingTheory.«INTEGER_RING_SUM»
  INTEGRAL_DOMAIN_INTEGER_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_INTEGER_RING»
  INTEGRAL_DOMAIN_MUL_LCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_LCANCEL»
  INT_ABS_POS := Session.INT_ABS_POS
  INT_ABS_POW := Session.INT_ABS_POW
  INT_ABS_ZERO := Session.INT_ABS_ZERO
  INT_MUL_SYM := Session.INT_MUL_SYM
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_POW_EQ_0 := Session.INT_POW_EQ_0
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_IMAGE := Session.IN_IMAGE
  IN_INTER := Session.IN_INTER
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_SING := Session.IN_SING
  IN_SUBRING_0 := SessionLibrary.RingTheory.«IN_SUBRING_0»
  IN_SUBRING_1 := SessionLibrary.RingTheory.«IN_SUBRING_1»
  IN_SUBRING_ADD := SessionLibrary.RingTheory.«IN_SUBRING_ADD»
  IN_SUBRING_MUL := SessionLibrary.RingTheory.«IN_SUBRING_MUL»
  IN_SUBRING_NEG := SessionLibrary.RingTheory.«IN_SUBRING_NEG»
  IN_SUBRING_SUM := SessionLibrary.RingTheory.«IN_SUBRING_SUM»
  IN_UNIV := Session.IN_UNIV
  I_THM := Session.I_THM
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NUMBER_FIELD_DEGREE_POS := SessionANT.Numfield.«NUMBER_FIELD_DEGREE_POS»
  NUMBER_FIELD_DISCRIMINANT_BASIS := SessionANT.Discriminant.«NUMBER_FIELD_DISCRIMINANT_BASIS»
  NUMBER_FIELD_DISCRIMINANT_NONZERO := SessionANT.Discriminant.«NUMBER_FIELD_DISCRIMINANT_NONZERO»
  NUMBER_FIELD_HOMOMORPHIC_PREIMAGE := SessionANT.RelativeSplit.«NUMBER_FIELD_HOMOMORPHIC_PREIMAGE»
  NUMBER_FIELD_IDEAL_NORM_MUL_Q := SessionANT.NormIndex.«NUMBER_FIELD_IDEAL_NORM_MUL_Q»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_INTEGRAL_MULTIPLE := SessionANT.Numfield.«NUMBER_FIELD_INTEGRAL_MULTIPLE»
  NUMBER_FIELD_TOWER_LAW := SessionANT.RelativeSplit.«NUMBER_FIELD_TOWER_LAW»
  NUMBER_FIELD_TRACE_FORM_INJECTIVE := SessionANT.Numfield.«NUMBER_FIELD_TRACE_FORM_INJECTIVE»
  NUMBER_FIELD_TRACE_INTEGRAL := SessionANT.Integrality.«NUMBER_FIELD_TRACE_INTEGRAL»
  NUMBER_FIELD_TRACE_INTEGRAL_BASIS := SessionANT.NormIndex.«NUMBER_FIELD_TRACE_INTEGRAL_BASIS»
  NUMBER_FIELD_TRACE_IN_RING_OF_INTEGERS := SessionANT.Numfield.«NUMBER_FIELD_TRACE_IN_RING_OF_INTEGERS»
  NUMBER_FIELD_TRACE_MUL_LINCOMB := SessionANT.Numfield.«NUMBER_FIELD_TRACE_MUL_LINCOMB»
  NUMBER_FIELD_TRACE_SCALAR_MUL := SessionANT.Numfield.«NUMBER_FIELD_TRACE_SCALAR_MUL»
  NUM_OF_INT_ABS_POW := SessionANT.Algmisc.«NUM_OF_INT_ABS_POW»
  NUM_OF_INT_OF_NUM := Session.NUM_OF_INT_OF_NUM
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
  RIGHT_EXISTS_IMP_THM := Session.RIGHT_EXISTS_IMP_THM
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_LDISTRIB := SessionLibrary.RingTheory.«RING_ADD_LDISTRIB»
  RING_ADD_RDISTRIB := SessionLibrary.RingTheory.«RING_ADD_RDISTRIB»
  RING_CARRIER_SUBFIELD_GENERATED_SUBSET := SessionLibrary.FieldTheory.«RING_CARRIER_SUBFIELD_GENERATED_SUBSET»
  RING_DET_ADJUGATE_ROWS := SessionLibrary.RingDet.«RING_DET_ADJUGATE_ROWS»
  RING_DET_COFACTOR := SessionLibrary.RingDet.«RING_DET_COFACTOR»
  RING_DET_SUBRING := SessionLibrary.RingDet.«RING_DET_SUBRING»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_HOMOMORPHISM_RING_OF_INTEGERS»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_INV_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_INV_IN_SUBFIELD_GENERATED»
  RING_MONOMORPHISM_EQ_0 := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EQ_0»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LINV := SessionLibrary.RingTheory.«RING_MUL_LINV»
  RING_MUL_LNEG := SessionLibrary.RingTheory.«RING_MUL_LNEG»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RNEG := SessionLibrary.RingTheory.«RING_MUL_RNEG»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_FREE := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE»
  RING_OF_INTEGERS_FREE_BASIS_FIELD := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE_BASIS_FIELD»
  RING_OF_INTEGERS_IDEAL_NORM_INTEGER := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_IDEAL_NORM_INTEGER»
  RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING := SessionANT.Numfield.«RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING»
  RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE := SessionANT.RelativeSplit.«RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE»
  RING_OF_INTEGERS_SUBFIELD_GENERATED := SessionANT.RelativeSplit.«RING_OF_INTEGERS_SUBFIELD_GENERATED»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_0 := SessionLibrary.RingTheory.«RING_OF_INT_0»
  RING_OF_INT_EQ_0_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0_CHAR_0»
  RING_OF_INT_EQ_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_CHAR_0»
  RING_OF_INT_IN_RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INT_IN_RING_OF_INTEGERS»
  RING_OF_INT_IN_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_INT_IN_SUBFIELD_GENERATED»
  RING_OF_INT_ISUM := SessionLibrary.RingTheory.«RING_OF_INT_ISUM»
  RING_OF_INT_MUL := SessionLibrary.RingTheory.«RING_OF_INT_MUL»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_DELTA := SessionLibrary.RingTheory.«RING_SUM_DELTA»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_SUM_RING_OF_INTEGERS»
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBSET := Session.SUBSET
  basis_discriminant := SessionLibrary.RingDet.«basis_discriminant»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  free_basis := SessionLibrary.RingDet.«free_basis»
  ideal_norm := SessionANT.IdealNorm.«ideal_norm»
  ideal_quotient := SessionANT.IdealArith.«ideal_quotient»
  int_divides := Session.int_divides
  number_field := SessionANT.Numfield.«number_field»
  ring_ideal := SessionLibrary.RingTheory.«ring_ideal»
  subring_of := SessionLibrary.RingTheory.«subring_of»

/-- What different.ml uses from Session. -/
def deps : HolANT.Different.DifferentDeps where
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

/- The bundles, in different.ml order. -/
initialize BDifferent01 : HolANT.Different.Different01 ←
  ioB "setupDifferent01" (HolANT.Different.setupDifferent01 deps).run
initialize BDifferent02 : HolANT.Different.Different02 ←
  ioB "setupDifferent02" (HolANT.Different.setupDifferent02 deps BDifferent01).run

-- Different01
def number_field_codifferent : thm := BDifferent01.number_field_codifferent
def number_field_different : thm := BDifferent01.number_field_different
def RING_IDEAL_NUMBER_FIELD_DIFFERENT : thm := BDifferent01.RING_IDEAL_NUMBER_FIELD_DIFFERENT
def NUMBER_FIELD_CODIFFERENT_PRIME_SUBFIELD : thm := BDifferent01.NUMBER_FIELD_CODIFFERENT_PRIME_SUBFIELD
def RING_OF_INTEGERS_SUBSET_CODIFFERENT : thm := BDifferent01.RING_OF_INTEGERS_SUBSET_CODIFFERENT
def NUMBER_FIELD_CODIFFERENT_MUL : thm := BDifferent01.NUMBER_FIELD_CODIFFERENT_MUL
def NUMBER_FIELD_CODIFFERENT_ADD : thm := BDifferent01.NUMBER_FIELD_CODIFFERENT_ADD
def NUMBER_FIELD_FREE_BASIS_INTEGRAL : thm := BDifferent01.NUMBER_FIELD_FREE_BASIS_INTEGRAL
def NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT : thm := BDifferent01.NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT
def NUMBER_FIELD_CODIFFERENT_FRACTIONAL : thm := BDifferent01.NUMBER_FIELD_CODIFFERENT_FRACTIONAL
def NUMBER_FIELD_DIFFERENT_CODIFFERENT : thm := BDifferent01.NUMBER_FIELD_DIFFERENT_CODIFFERENT
def NUMBER_FIELD_DIFFERENT_NONZERO : thm := BDifferent01.NUMBER_FIELD_DIFFERENT_NONZERO
def NUMBER_FIELD_CODIFFERENT_DIFFERENT : thm := BDifferent01.NUMBER_FIELD_CODIFFERENT_DIFFERENT
def NUMBER_FIELD_CODIFFERENT_DIV : thm := BDifferent01.NUMBER_FIELD_CODIFFERENT_DIV
def NUMBER_FIELD_CODIFFERENT_EQ_IMAGE : thm := BDifferent01.NUMBER_FIELD_CODIFFERENT_EQ_IMAGE
def NUMBER_FIELD_CODIFFERENT_INTEGRAL_BASIS : thm := BDifferent01.NUMBER_FIELD_CODIFFERENT_INTEGRAL_BASIS
def NUMBER_FIELD_CODIFFERENT_DUAL_SPAN : thm := BDifferent01.NUMBER_FIELD_CODIFFERENT_DUAL_SPAN

-- Different02
def NUMBER_FIELD_CODIFFERENT_ADJUGATE : thm := BDifferent02.NUMBER_FIELD_CODIFFERENT_ADJUGATE
def NUMBER_FIELD_CODIFFERENT_DUAL_BASIS : thm := BDifferent02.NUMBER_FIELD_CODIFFERENT_DUAL_BASIS
def NUMBER_FIELD_CODIFFERENT_IDEAL : thm := BDifferent02.NUMBER_FIELD_CODIFFERENT_IDEAL
def NUMBER_FIELD_DISCRIMINANT_IN_DIFFERENT : thm := BDifferent02.NUMBER_FIELD_DISCRIMINANT_IN_DIFFERENT
def NUMBER_FIELD_DIFFERENT_CODIFFERENT_Q : thm := BDifferent02.NUMBER_FIELD_DIFFERENT_CODIFFERENT_Q
def NUMBER_FIELD_IDEAL_NORM_DIFFERENT : thm := BDifferent02.NUMBER_FIELD_IDEAL_NORM_DIFFERENT
def NUMBER_FIELD_DIFFERENT_EQ_CARRIER : thm := BDifferent02.NUMBER_FIELD_DIFFERENT_EQ_CARRIER
def NUMBER_FIELD_CODIFFERENT_DIV_NUM : thm := BDifferent02.NUMBER_FIELD_CODIFFERENT_DIV_NUM

/-- `needs "ANT/different.ml"`: already done by importing this module. -/
def ensureDifferent : IO Unit := pure ()

end SessionANT.Different
