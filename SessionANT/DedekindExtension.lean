/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/dedekind_extension.ml                         . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/DedekindExtension.lean

  The session half of the dedekind_extension.ml translation: it supplies HolANT.DedekindExtension's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/dedekind_extension.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.DedekindExtension
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
import SessionANT.IntegralPrimes
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.DedekindExtension

/-- The core theorems dedekind_extension.ml uses. -/
def core1 : HolANT.DedekindExtension.CoreThms1 where
  ALGEBRA_TRACE_SURJECTIVE := SessionLibrary.FieldTheory.«ALGEBRA_TRACE_SURJECTIVE»
  BASIS_COORDINATES_EXPAND := SessionLibrary.RingDet.«BASIS_COORDINATES_EXPAND»
  BASIS_COORDINATES_IN_CARRIER := SessionLibrary.RingDet.«BASIS_COORDINATES_IN_CARRIER»
  BASIS_DISCRIMINANT_EQ_0 := SessionLibrary.RingDet.«BASIS_DISCRIMINANT_EQ_0»
  BASIS_DISCRIMINANT_TIMES_COORD := SessionLibrary.RingDet.«BASIS_DISCRIMINANT_TIMES_COORD»
  CARRIER_SUBRING_GENERATED_SUBRING := SessionLibrary.RingTheory.«CARRIER_SUBRING_GENERATED_SUBRING»
  DEDEKIND_IMP_NOETHERIAN := SessionANT.Dedekind.«DEDEKIND_IMP_NOETHERIAN»
  ETA_AX := Session.ETA_AX
  EXTENSION := Session.EXTENSION
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_MUL_LINV := SessionLibrary.RingTheory.«FIELD_MUL_LINV»
  FIELD_MUL_RINV := SessionLibrary.RingTheory.«FIELD_MUL_RINV»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FINITE_EXTENSION_FREE_BASIS := SessionLibrary.FieldTheory.«FINITE_EXTENSION_FREE_BASIS»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_IMP_ALGEBRAIC_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_ALGEBRAIC_EXTENSION»
  FINITE_IMP_FIELD_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_FIELD_EXTENSION»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FRACTION_FIELD_COMMON_DENOMINATOR := SessionLibrary.RingTheory.«FRACTION_FIELD_COMMON_DENOMINATOR»
  FREE_BASIS_IN_CARRIER := SessionLibrary.RingDet.«FREE_BASIS_IN_CARRIER»
  FREE_BASIS_SCALE := SessionLibrary.RingDet.«FREE_BASIS_SCALE»
  IDEAL_GENERATED_MINIMAL := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL»
  IDEAL_GENERATED_SUBSET_CARRIER_SUBSET := SessionLibrary.RingTheory.«IDEAL_GENERATED_SUBSET_CARRIER_SUBSET»
  IMP_IMP := Session.IMP_IMP
  INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM := SessionANT.Integral.«INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM»
  INTEGRALLY_CLOSED_INTEGRAL_CLOSURE := SessionANT.Integral.«INTEGRALLY_CLOSED_INTEGRAL_CLOSURE»
  INTEGRAL_CLOSURE_SUBRING := SessionANT.Integral.«INTEGRAL_CLOSURE_SUBRING»
  INTEGRAL_CLOSURE_SUPSET_IMAGE := SessionANT.Integral.«INTEGRAL_CLOSURE_SUPSET_IMAGE»
  INTEGRAL_DOMAIN_SUBRING_GENERATED := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_SUBRING_GENERATED»
  INTEGRAL_ELEMENT_FROM_RELATION := SessionANT.Integral.«INTEGRAL_ELEMENT_FROM_RELATION»
  INTEGRAL_ELEMENT_IMAGE := SessionANT.Integral.«INTEGRAL_ELEMENT_IMAGE»
  INTEGRAL_ELEMENT_IN_CARRIER := SessionANT.Integral.«INTEGRAL_ELEMENT_IN_CARRIER»
  INTEGRAL_ELEMENT_MUL := SessionANT.Integral.«INTEGRAL_ELEMENT_MUL»
  INTEGRAL_ELEMENT_RELATION := SessionANT.Integral.«INTEGRAL_ELEMENT_RELATION»
  INTEGRAL_ELEMENT_SUBRING_GENERATED := SessionANT.Integral.«INTEGRAL_ELEMENT_SUBRING_GENERATED»
  INTEGRAL_EXTENSION_MAXIMAL_IDEAL := SessionANT.IntegralPrimes.«INTEGRAL_EXTENSION_MAXIMAL_IDEAL»
  INTEGRAL_EXTENSION_PRIME_NONZERO := SessionANT.IntegralPrimes.«INTEGRAL_EXTENSION_PRIME_NONZERO»
  INTEGRAL_OVER_FIELD_EQ_ALGEBRAIC := SessionANT.Integral.«INTEGRAL_OVER_FIELD_EQ_ALGEBRAIC»
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_ADD := SessionLibrary.RingTheory.«IN_RING_IDEAL_ADD»
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  I_DEF := Session.I_DEF
  I_THM := Session.I_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  MONO_EXISTS := Session.MONO_EXISTS
  NOETHERIAN_RING_SPAN_SUBMODULE := SessionLibrary.FieldTheory.«NOETHERIAN_RING_SPAN_SUBMODULE»
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  PRIME_IDEAL_HOMOMORPHIC_PREIMAGE := SessionLibrary.RingTheory.«PRIME_IDEAL_HOMOMORPHIC_PREIMAGE»
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD_LDISTRIB := SessionLibrary.RingTheory.«RING_ADD_LDISTRIB»
  RING_DET := SessionLibrary.RingDet.«RING_DET»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_INTO_SUBRING_EQ := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTO_SUBRING_EQ»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_MONOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_MONOMORPHISM_COMPOSE»
  RING_MONOMORPHISM_EQ_0 := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EQ_0»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_INCLUSION := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INCLUSION»
  RING_MONOMORPHISM_INTO_SUBRING := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INTO_SUBRING»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_POW := SessionLibrary.RingTheory.«RING_MUL_POW»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_1 := SessionLibrary.RingTheory.«RING_POW_1»
  RING_POW_ADD := SessionLibrary.RingTheory.«RING_POW_ADD»
  RING_SPAN_INC := SessionLibrary.FieldTheory.«RING_SPAN_INC»
  RING_SPAN_MUL := SessionLibrary.FieldTheory.«RING_SPAN_MUL»
  RING_SPAN_SUM := SessionLibrary.FieldTheory.«RING_SPAN_SUM»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_LMUL := SessionLibrary.RingTheory.«RING_SUM_LMUL»
  SKOLEM_THM := Session.SKOLEM_THM
  SUBRING_GENERATED := SessionLibrary.RingTheory.«SUBRING_GENERATED»
  SUBRING_RING_IMAGE := SessionLibrary.RingTheory.«SUBRING_RING_IMAGE»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  algebraic_extension := SessionLibrary.FieldTheory.«algebraic_extension»
  basis_discriminant := SessionLibrary.RingDet.«basis_discriminant»
  dedekind_domain := SessionANT.Dedekind.«dedekind_domain»
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  field_of_fractions := SessionLibrary.RingTheory.«field_of_fractions»
  finitely_generated_ideal := SessionLibrary.RingTheory.«finitely_generated_ideal»
  noetherian_ring := SessionLibrary.RingTheory.«noetherian_ring»
  o_THM := Session.o_THM
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_image := SessionLibrary.RingTheory.«ring_image»
  ring_span_INDUCT := SessionLibrary.FieldTheory.«ring_span_INDUCT»

/-- What dedekind_extension.ml uses from Session. -/
def deps : HolANT.DedekindExtension.DedekindExtensionDeps where
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

/- The bundles, in dedekind_extension.ml order. -/
initialize BDedekindExtension : HolANT.DedekindExtension.DedekindExtension ←
  ioB "setupDedekindExtension" (HolANT.DedekindExtension.setupDedekindExtension deps).run

-- DedekindExtension
def INTEGRAL_ELEMENT_DENOMINATOR : thm := BDedekindExtension.INTEGRAL_ELEMENT_DENOMINATOR
def INTEGRAL_CLOSURE_SUBSET_SPAN : thm := BDedekindExtension.INTEGRAL_CLOSURE_SUBSET_SPAN
def FIELD_OF_FRACTIONS_INTEGRAL_CLOSURE : thm := BDedekindExtension.FIELD_OF_FRACTIONS_INTEGRAL_CLOSURE
def DEDEKIND_INTEGRAL_CLOSURE : thm := BDedekindExtension.DEDEKIND_INTEGRAL_CLOSURE

/-- `needs "ANT/dedekind_extension.ml"`: already done by importing this module. -/
def ensureDedekindExtension : IO Unit := pure ()

end SessionANT.DedekindExtension
