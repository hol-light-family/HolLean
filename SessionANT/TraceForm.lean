/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/trace_form.ml                                 . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/TraceForm.lean

  The session half of the trace_form.ml translation: it supplies HolANT.TraceForm's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/trace_form.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.TraceForm
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
import SessionLibrary.Isum
import SessionANT.Integral
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Discriminant

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.TraceForm

/-- The core theorems trace_form.ml uses. -/
def core1 : HolANT.TraceForm.CoreThms1 where
  ADD_SUB2 := Session.ADD_SUB2
  ALGEBRA_TRACE_FREE_BASIS := SessionLibrary.RingDet.«ALGEBRA_TRACE_FREE_BASIS»
  ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE := SessionLibrary.RingDet.«ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE»
  BASIS_COORDINATES := SessionLibrary.RingDet.«BASIS_COORDINATES»
  BASIS_COORDINATES_EXPAND := SessionLibrary.RingDet.«BASIS_COORDINATES_EXPAND»
  BASIS_COORDINATES_IN_CARRIER := SessionLibrary.RingDet.«BASIS_COORDINATES_IN_CARRIER»
  BASIS_COORDINATES_UNIQUE := SessionLibrary.RingDet.«BASIS_COORDINATES_UNIQUE»
  COND_RAND := Session.COND_RAND
  EQ_TRANS := Session.EQ_TRANS
  EXTENSION_DEGREE_ISOMORPHISM := SessionLibrary.FieldTheory.«EXTENSION_DEGREE_ISOMORPHISM»
  FINITE_EXTENSION_ISOMORPHISM := SessionLibrary.FieldTheory.«FINITE_EXTENSION_ISOMORPHISM»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FREE_BASIS_INDEPENDENT := SessionLibrary.RingDet.«FREE_BASIS_INDEPENDENT»
  FREE_BASIS_IN_CARRIER := SessionLibrary.RingDet.«FREE_BASIS_IN_CARRIER»
  FUN_EQ_THM := Session.FUN_EQ_THM
  IN_CROSS := Session.IN_CROSS
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  ISOMORPHIC_RING_FIELDNESS := SessionLibrary.RingTheory.«ISOMORPHIC_RING_FIELDNESS»
  I_THM := Session.I_THM
  MULT_CLAUSES := Session.MULT_CLAUSES
  NUMBER_FIELD_DISCRIMINANT_BASIS := SessionANT.Discriminant.«NUMBER_FIELD_DISCRIMINANT_BASIS»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  PAIR_EQ := Session.PAIR_EQ
  PRIME_SUBFIELD_TOWER_LAW := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_TOWER_LAW»
  PROD_RING := SessionLibrary.RingTheory.«PROD_RING»
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_DET_EQ := SessionLibrary.RingDet.«RING_DET_EQ»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_I := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_I»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_PAIRED := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_PAIRED»
  RING_HOMOMORPHISM_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_INT»
  RING_HOMOMORPHISM_SUM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUM_MUL»
  RING_ISOMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISM»
  RING_ISOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_ISOMORPHISM_IMP_HOMOMORPHISM»
  RING_ISOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_ISOMORPHISM_RING_OF_INTEGERS»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_FREE := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FREE»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_EQ_0 := SessionLibrary.RingTheory.«RING_SUM_EQ_0»
  RING_SUM_NUMSEG_LT_ADD := SessionLibrary.RingTheory.«RING_SUM_NUMSEG_LT_ADD»
  RING_SUM_PROD_RING := SessionLibrary.RingTheory.«RING_SUM_PROD_RING»
  basis_discriminant := SessionLibrary.RingDet.«basis_discriminant»
  free_basis := SessionLibrary.RingDet.«free_basis»
  isomorphic_ring := SessionLibrary.RingTheory.«isomorphic_ring»
  mul_matrix := SessionLibrary.RingDet.«mul_matrix»
  number_field := SessionANT.Numfield.«number_field»
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM

/-- What trace_form.ml uses from Session. -/
def deps : HolANT.TraceForm.TraceFormDeps where
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

/- The bundles, in trace_form.ml order. -/
initialize BTraceForm : HolANT.TraceForm.TraceForm ←
  ioB "setupTraceForm" (HolANT.TraceForm.setupTraceForm deps).run

-- TraceForm
def EXTENSION_LINCOMB_PROD_RING : thm := BTraceForm.EXTENSION_LINCOMB_PROD_RING
def FREE_BASIS_PROD_RING : thm := BTraceForm.FREE_BASIS_PROD_RING
def BASIS_COORDINATES_PROD_RING : thm := BTraceForm.BASIS_COORDINATES_PROD_RING
def ALGEBRA_TRACE_PROD_RING : thm := BTraceForm.ALGEBRA_TRACE_PROD_RING
def FREE_BASIS_ISOMORPHIC_IMAGE : thm := BTraceForm.FREE_BASIS_ISOMORPHIC_IMAGE
def ALGEBRA_TRACE_ISOMORPHIC_IMAGE : thm := BTraceForm.ALGEBRA_TRACE_ISOMORPHIC_IMAGE
def NUMBER_FIELD_ISOMORPHIC_IMAGE : thm := BTraceForm.NUMBER_FIELD_ISOMORPHIC_IMAGE

/-- `needs "ANT/trace_form.ml"`: already done by importing this module. -/
def ensureTraceForm : IO Unit := pure ()

end SessionANT.TraceForm
