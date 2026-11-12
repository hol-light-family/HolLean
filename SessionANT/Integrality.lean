/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/integrality.ml                                . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/Integrality.lean

  The session half of the integrality.ml translation: it supplies HolANT.Integrality's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/integrality.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.Integrality
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
import SessionANT.Integral
import SessionLibrary.Isum
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.NfValuation
import SessionANT.PrimeSplit
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.RelativeSplit

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.Integrality

/-- The core theorems integrality.ml uses. -/
def core1 : HolANT.Integrality.CoreThms1 where
  ADD_CLAUSES := Session.ADD_CLAUSES
  ALGEBRA_NORM_MINIMAL_POLYNOMIAL := SessionLibrary.FieldTheory.«ALGEBRA_NORM_MINIMAL_POLYNOMIAL»
  ALGEBRA_NORM_UNIT := SessionLibrary.RingDet.«ALGEBRA_NORM_UNIT»
  AND_FORALL_THM := Session.AND_FORALL_THM
  EQ_TRANS := Session.EQ_TRANS
  EXTENSION_DEGREE_EQ_0 := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_EQ_0»
  FIELD_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBFIELD_GENERATED»
  FIELD_MUL_LINV := SessionLibrary.RingTheory.«FIELD_MUL_LINV»
  FIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FIELD_SUBFIELD_GENERATED»
  FINITE_EXTENSION_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«FINITE_EXTENSION_SUBFIELD_GENERATED»
  FINITE_IMP_ALGEBRAIC_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_ALGEBRAIC_EXTENSION»
  FINITE_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_FIELD_EXTENSION»
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FUN_EQ_THM := Session.FUN_EQ_THM
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  IMAGE_I := Session.IMAGE_I
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTEGER_RING_UNIT := SessionLibrary.RingTheory.«INTEGER_RING_UNIT»
  INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM := SessionANT.Integral.«INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM»
  INTEGRALLY_CLOSED_MINIMAL_POLYNOMIAL := SessionANT.Integral.«INTEGRALLY_CLOSED_MINIMAL_POLYNOMIAL»
  INTEGRALLY_CLOSED_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«INTEGRALLY_CLOSED_RING_OF_INTEGERS»
  INTEGRALLY_CLOSED_UNIT_NORM := SessionANT.Integral.«INTEGRALLY_CLOSED_UNIT_NORM»
  INTEGRAL_CLOSURE_SUBRING := SessionANT.Integral.«INTEGRAL_CLOSURE_SUBRING»
  INTEGRAL_CLOSURE_SUPSET_IMAGE := SessionANT.Integral.«INTEGRAL_CLOSURE_SUPSET_IMAGE»
  INTEGRAL_ELEMENT_INTERMEDIATE := SessionANT.Integral.«INTEGRAL_ELEMENT_INTERMEDIATE»
  INTEGRAL_ELEMENT_SUBRING_GENERATED := SessionANT.Integral.«INTEGRAL_ELEMENT_SUBRING_GENERATED»
  INTEGRAL_ELEMENT_TRANS := SessionANT.Integral.«INTEGRAL_ELEMENT_TRANS»
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_INSERT := Session.IN_INSERT
  IN_NUMSEG := Session.IN_NUMSEG
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_RING_IDEAL_NEG := SessionLibrary.RingTheory.«IN_RING_IDEAL_NEG»
  IN_RING_IDEAL_RMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_RMUL»
  IN_RING_IDEAL_SUM := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUM»
  IN_SING := Session.IN_SING
  IN_SUBRING_0 := SessionLibrary.RingTheory.«IN_SUBRING_0»
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_0 := Session.LE_0
  MINIMAL_POLYNOMIAL := SessionLibrary.FieldTheory.«MINIMAL_POLYNOMIAL»
  MONO_EXISTS := Session.MONO_EXISTS
  NUMBER_FIELD_HOMOMORPHIC_PREIMAGE := SessionANT.RelativeSplit.«NUMBER_FIELD_HOMOMORPHIC_PREIMAGE»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_INTEGRAL_MULTIPLE := SessionANT.Numfield.«NUMBER_FIELD_INTEGRAL_MULTIPLE»
  NUMBER_FIELD_NORM_INTEGRAL_BASIS := SessionANT.NormIndex.«NUMBER_FIELD_NORM_INTEGRAL_BASIS»
  NUMBER_FIELD_TOWER_LAW := SessionANT.RelativeSplit.«NUMBER_FIELD_TOWER_LAW»
  POLY_EXTEND_UNIVARIATE := SessionLibrary.RingTheory.«POLY_EXTEND_UNIVARIATE»
  PRIMITIVE_ELEMENT_THEOREM := SessionLibrary.FieldTheory.«PRIMITIVE_ELEMENT_THEOREM»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_FROM_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_FROM_SUBRING_GENERATED»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_NEG := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_NEG»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_HOMOMORPHISM_RING_OF_INTEGERS»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_IN_SUBRING_GENERATED := SessionLibrary.RingTheory.«RING_MUL_IN_SUBRING_GENERATED»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_CARRIER := SessionANT.Numfield.«RING_OF_INTEGERS_CARRIER»
  RING_OF_INTEGERS_FRACTION_FIELD := SessionANT.NfValuation.«RING_OF_INTEGERS_FRACTION_FIELD»
  RING_OF_INTEGERS_FREE := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE»
  RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER := SessionANT.RelativeSplit.«RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_1 := SessionLibrary.RingTheory.«RING_OF_INT_1»
  RING_OF_INT_EQ_0_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0_CHAR_0»
  RING_OF_INT_EQ_CHAR_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_CHAR_0»
  RING_OF_INT_NEG := SessionLibrary.RingTheory.«RING_OF_INT_NEG»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_RNEG_UNIQUE := SessionLibrary.RingTheory.«RING_RNEG_UNIQUE»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_CLAUSES_LEFT := SessionLibrary.RingTheory.«RING_SUM_CLAUSES_LEFT»
  RING_SUM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_SUM_RING_OF_INTEGERS»
  RING_UNIT_IN_CARRIER := SessionLibrary.RingTheory.«RING_UNIT_IN_CARRIER»
  SEPARABLE_EXTENSION_CHAR0 := SessionLibrary.FieldTheory.«SEPARABLE_EXTENSION_CHAR0»
  SING_SUBSET := Session.SING_SUBSET
  SUBFIELD_GENERATED_INC_GEN := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_INC_GEN»
  SUBFIELD_GENERATED_MINIMAL := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_MINIMAL»
  SUBFIELD_GENERATED_SUPERSET := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED_SUPERSET»
  SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_SUBFIELD_GENERATED»
  SUBRING_GENERATED_INC_GEN := SessionLibrary.RingTheory.«SUBRING_GENERATED_INC_GEN»
  SUBRING_GENERATED_MINIMAL := SessionLibrary.RingTheory.«SUBRING_GENERATED_MINIMAL»
  SUBRING_GENERATED_SUPERSET := SessionLibrary.RingTheory.«SUBRING_GENERATED_SUPERSET»
  SUBRING_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBRING_SUBFIELD_GENERATED»
  SUBRING_SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_SUBRING_GENERATED»
  SUBSET := Session.SUBSET
  algebraic_extension := SessionLibrary.FieldTheory.«algebraic_extension»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  number_field := SessionANT.Numfield.«number_field»
  o_THM := Session.o_THM
  ring_of_integers := SessionANT.Numfield.«ring_of_integers»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_unit := SessionLibrary.RingTheory.«ring_unit»

/-- What integrality.ml uses from Session. -/
def deps : HolANT.Integrality.IntegralityDeps where
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

/- The bundles, in integrality.ml order. -/
initialize BIntegrality : HolANT.Integrality.Integrality ←
  ioB "setupIntegrality" (HolANT.Integrality.setupIntegrality deps).run

-- Integrality
def RING_OF_INTEGERS_INTEGRAL_ELEMENT : thm := BIntegrality.RING_OF_INTEGERS_INTEGRAL_ELEMENT
def RING_OF_INTEGERS_MINIMAL_POLYNOMIAL : thm := BIntegrality.RING_OF_INTEGERS_MINIMAL_POLYNOMIAL
def RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q : thm := BIntegrality.RING_OF_INTEGERS_MINIMAL_POLYNOMIAL_Q
def NUMBER_FIELD_TRACE_INTEGRAL : thm := BIntegrality.NUMBER_FIELD_TRACE_INTEGRAL
def NUMBER_FIELD_NORM_INTEGRAL : thm := BIntegrality.NUMBER_FIELD_NORM_INTEGRAL
def RING_OF_INTEGERS_UNIT_NORM : thm := BIntegrality.RING_OF_INTEGERS_UNIT_NORM
def RING_OF_INTEGERS_UNIT_NORM_Q : thm := BIntegrality.RING_OF_INTEGERS_UNIT_NORM_Q
def NUMBER_FIELD_NORM_MULTIPLE : thm := BIntegrality.NUMBER_FIELD_NORM_MULTIPLE
def NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT : thm := BIntegrality.NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT
def NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT_Q : thm := BIntegrality.NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT_Q

/-- `needs "ANT/integrality.ml"`: already done by importing this module. -/
def ensureIntegrality : IO Unit := pure ()

end SessionANT.Integrality
