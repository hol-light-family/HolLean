/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/finite_field_trace.ml                         . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/FiniteFieldTrace.lean

  The session half of the finite_field_trace.ml translation: it supplies HolANT.FiniteFieldTrace's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/finite_field_trace.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.FiniteFieldTrace
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
import SessionANT.IdealArith
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionLibrary.Isum
import SessionANT.Integral
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionANT.TraceForm

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.FiniteFieldTrace

/-- The core theorems finite_field_trace.ml uses. -/
def core1 : HolANT.FiniteFieldTrace.CoreThms1 where
  ALGEBRA_TRACE_0 := SessionLibrary.RingDet.«ALGEBRA_TRACE_0»
  ALGEBRA_TRACE_ISOMORPHIC_IMAGE := SessionANT.TraceForm.«ALGEBRA_TRACE_ISOMORPHIC_IMAGE»
  ALGEBRA_TRACE_NORM_IN_CARRIER := SessionLibrary.RingDet.«ALGEBRA_TRACE_NORM_IN_CARRIER»
  ALGEBRA_TRACE_PROD_RING := SessionANT.TraceForm.«ALGEBRA_TRACE_PROD_RING»
  ALGEBRA_TRACE_SURJECTIVE := SessionLibrary.FieldTheory.«ALGEBRA_TRACE_SURJECTIVE»
  BASIS_DISCRIMINANT_EQ_0 := SessionLibrary.RingDet.«BASIS_DISCRIMINANT_EQ_0»
  BASIS_DISCRIMINANT_NILPOTENT := SessionLibrary.RingDet.«BASIS_DISCRIMINANT_NILPOTENT»
  COMAXIMAL_IDEAL_PRODUCT := SessionANT.IdealArith.«COMAXIMAL_IDEAL_PRODUCT»
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  EQ_TRANS := Session.EQ_TRANS
  ETA_AX := Session.ETA_AX
  EXISTS_IN_IMAGE := Session.EXISTS_IN_IMAGE
  EXTENSION := Session.EXTENSION
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FIELD_QUOTIENT_RING := SessionLibrary.RingTheory.«FIELD_QUOTIENT_RING»
  FIELD_RING_HOMOMORPHISM_MONOMORPHISM := SessionLibrary.RingTheory.«FIELD_RING_HOMOMORPHISM_MONOMORPHISM»
  FINITE_FIELD_IMP_PERFECT := SessionLibrary.FieldTheory.«FINITE_FIELD_IMP_PERFECT»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_IMP_ALGEBRAIC_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_ALGEBRAIC_EXTENSION»
  FINITE_INTEGRAL_DOMAIN_IMP_FIELD := SessionLibrary.RingTheory.«FINITE_INTEGRAL_DOMAIN_IMP_FIELD»
  FINITE_POWERSET := Session.FINITE_POWERSET
  FINITE_RING_MONOMORPHIC_PREIMAGE := SessionLibrary.RingTheory.«FINITE_RING_MONOMORPHIC_PREIMAGE»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FREE_BASIS_EXISTS := SessionLibrary.FieldTheory.«FREE_BASIS_EXISTS»
  FREE_BASIS_EXTENSION_DEGREE := SessionLibrary.FieldTheory.«FREE_BASIS_EXTENSION_DEGREE»
  FREE_BASIS_HAS_SIZE := SessionLibrary.RingDet.«FREE_BASIS_HAS_SIZE»
  FREE_BASIS_IMP_FINITE_EXTENSION := SessionLibrary.FieldTheory.«FREE_BASIS_IMP_FINITE_EXTENSION»
  FREE_BASIS_ISOMORPHIC_IMAGE := SessionANT.TraceForm.«FREE_BASIS_ISOMORPHIC_IMAGE»
  FREE_BASIS_PROD_RING := SessionANT.TraceForm.«FREE_BASIS_PROD_RING»
  FUN_EQ_THM := Session.FUN_EQ_THM
  HAS_SIZE := Session.HAS_SIZE
  IDEAL_PRODUCT_SUBSET := SessionANT.IdealArith.«IDEAL_PRODUCT_SUBSET»
  INTEGRAL_DOMAIN_QUOTIENT_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_QUOTIENT_RING»
  INTER_SUBSET := Session.INTER_SUBSET
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INTER := Session.IN_INTER
  IN_INTERS := Session.IN_INTERS
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_ADD := SessionLibrary.RingTheory.«IN_RING_IDEAL_ADD»
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_SING := Session.IN_SING
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  MAXIMAL_IDEAL_COMAXIMAL := SessionANT.IdealArith.«MAXIMAL_IDEAL_COMAXIMAL»
  MAXIMAL_IDEAL_COMAXIMAL_MUL := SessionANT.IdealArith.«MAXIMAL_IDEAL_COMAXIMAL_MUL»
  MAXIMAL_IDEAL_CORRESPONDENCE := SessionLibrary.RingTheory.«MAXIMAL_IDEAL_CORRESPONDENCE»
  MAXIMAL_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«MAXIMAL_IDEAL_IMP_SUBSET»
  MAXIMAL_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PROPER_IDEAL»
  MAXIMAL_IMP_RING_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_RING_IDEAL»
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  PERFECT_FIELD_IMP_SEPARABLE_EXTENSION := SessionLibrary.FieldTheory.«PERFECT_FIELD_IMP_SEPARABLE_EXTENSION»
  PRIME_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_PROPER_IDEAL»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PROPER_IDEAL := SessionLibrary.RingTheory.«PROPER_IDEAL»
  PSUBSET := Session.PSUBSET
  QUOTIENT_RING_0 := SessionLibrary.RingTheory.«QUOTIENT_RING_0»
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
  RIGHT_AND_EXISTS_THM := Session.RIGHT_AND_EXISTS_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_COSET_EQ_IDEAL := SessionLibrary.RingTheory.«RING_COSET_EQ_IDEAL»
  RING_EPIMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_EPIMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_PAIRED := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_PAIRED»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_IDEAL_EPIMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_IDEAL_EPIMORPHIC_IMAGE»
  RING_IDEAL_IDEAL_PRODUCT := SessionANT.IdealArith.«RING_IDEAL_IDEAL_PRODUCT»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_IDEAL_INTER := SessionLibrary.RingTheory.«RING_IDEAL_INTER»
  RING_ISOMORPHISM_PROD_QUOTIENT_RING := SessionANT.IdealArith.«RING_ISOMORPHISM_PROD_QUOTIENT_RING»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_NILRADICAL := SessionLibrary.RingTheory.«RING_NILRADICAL»
  RING_SPAN_SELF := SessionLibrary.FieldTheory.«RING_SPAN_SELF»
  SIMPLE_IMAGE := Session.SIMPLE_IMAGE
  SUBSET := Session.SUBSET
  SUBSET_REFL := Session.SUBSET_REFL
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  maximal_ideal := SessionLibrary.RingTheory.«maximal_ideal»
  o_THM := Session.o_THM
  radical := SessionLibrary.RingTheory.«radical»
  ring_nilpotent := SessionLibrary.RingTheory.«ring_nilpotent»
  ring_spanning := SessionLibrary.FieldTheory.«ring_spanning»
  trivial_ring := SessionLibrary.RingTheory.«trivial_ring»

/-- What finite_field_trace.ml uses from Session. -/
def deps : HolANT.FiniteFieldTrace.FiniteFieldTraceDeps where
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

/- The bundles, in finite_field_trace.ml order. -/
initialize BFiniteFieldTrace : HolANT.FiniteFieldTrace.FiniteFieldTrace ←
  ioB "setupFiniteFieldTrace" (HolANT.FiniteFieldTrace.setupFiniteFieldTrace deps).run

-- FiniteFieldTrace
def ALGEBRA_TRACE_FINITE_FIELD_NONZERO : thm := BFiniteFieldTrace.ALGEBRA_TRACE_FINITE_FIELD_NONZERO
def ALGEBRA_TRACE_CHINESE_REMAINDER : thm := BFiniteFieldTrace.ALGEBRA_TRACE_CHINESE_REMAINDER
def ALGEBRA_TRACE_COMAXIMAL_NONZERO : thm := BFiniteFieldTrace.ALGEBRA_TRACE_COMAXIMAL_NONZERO
def ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO : thm := BFiniteFieldTrace.ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO
def FINITE_REDUCED_RING_SPLIT : thm := BFiniteFieldTrace.FINITE_REDUCED_RING_SPLIT
def TRACE_FORM_NONDEGENERATE_FINITE : thm := BFiniteFieldTrace.TRACE_FORM_NONDEGENERATE_FINITE
def BASIS_DISCRIMINANT_EQ_0_FINITE : thm := BFiniteFieldTrace.BASIS_DISCRIMINANT_EQ_0_FINITE

/-- `needs "ANT/finite_field_trace.ml"`: already done by importing this module. -/
def ensureFiniteFieldTrace : IO Unit := pure ()

end SessionANT.FiniteFieldTrace
