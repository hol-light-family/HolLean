/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/integral_primes.ml                            . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/IntegralPrimes.lean

  The session half of the integral_primes.ml translation: it supplies HolANT.IntegralPrimes's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/integral_primes.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.IntegralPrimes
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.IntegralPrimes

/-- The core theorems integral_primes.ml uses. -/
def core1 : HolANT.IntegralPrimes.CoreThms1 where
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EQ_TRANS := Session.EQ_TRANS
  EXTENSION := Session.EXTENSION
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_SUBSET_IMAGE := Session.FINITE_SUBSET_IMAGE
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  IDEAL_GENERATED_FINITARY := SessionLibrary.RingTheory.«IDEAL_GENERATED_FINITARY»
  IDEAL_GENERATED_FINITE_IMAGE := SessionLibrary.RingTheory.«IDEAL_GENERATED_FINITE_IMAGE»
  IDEAL_GENERATED_INC := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC»
  IDEAL_GENERATED_SUBSET := SessionLibrary.RingTheory.«IDEAL_GENERATED_SUBSET»
  IMP_IMP := Session.IMP_IMP
  INTEGRAL_ELEMENT_RELATION := SessionANT.Integral.«INTEGRAL_ELEMENT_RELATION»
  INTEGRAL_SPAN_FINITE_SET := SessionANT.Integral.«INTEGRAL_SPAN_FINITE_SET»
  IN_DIFF := Session.IN_DIFF
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_ADD := SessionLibrary.RingTheory.«IN_RING_IDEAL_ADD»
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_RING_IDEAL_NEG := SessionLibrary.RingTheory.«IN_RING_IDEAL_NEG»
  IN_RING_IDEAL_RMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_RMUL»
  IN_RING_IDEAL_SUB := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUB»
  IN_RING_IDEAL_SUM := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUM»
  IN_SING := Session.IN_SING
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LT := Session.LT
  MAXIMAL_IMP_PRIME_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PRIME_IDEAL»
  MAXIMAL_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PROPER_IDEAL»
  MAXIMAL_IMP_RING_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_RING_IDEAL»
  MAXIMAL_SUPERIDEAL_EXISTS := SessionLibrary.RingTheory.«MAXIMAL_SUPERIDEAL_EXISTS»
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  PRIME_IDEAL_0 := SessionLibrary.RingTheory.«PRIME_IDEAL_0»
  PRIME_IDEAL_HOMOMORPHIC_PREIMAGE := SessionLibrary.RingTheory.«PRIME_IDEAL_HOMOMORPHIC_PREIMAGE»
  PRIME_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_PROPER_IDEAL»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRIME_SUPERIDEAL_EXCLUDING_EXISTS := SessionLibrary.RingTheory.«PRIME_SUPERIDEAL_EXCLUDING_EXISTS»
  PROPER_IDEAL_HOMOMORPHIC_PREIMAGE := SessionLibrary.RingTheory.«PROPER_IDEAL_HOMOMORPHIC_PREIMAGE»
  PSUBSET := Session.PSUBSET
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  RIGHT_IMP_FORALL_THM := Session.RIGHT_IMP_FORALL_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_1_NOT_IN_PRIME_IDEAL := SessionLibrary.RingTheory.«RING_1_NOT_IN_PRIME_IDEAL»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_RDISTRIB := SessionLibrary.RingTheory.«RING_ADD_RDISTRIB»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_DET := SessionLibrary.RingDet.«RING_DET»
  RING_DET_DEPENDENT_COLUMNS_MUL_IDEAL := SessionLibrary.RingDet.«RING_DET_DEPENDENT_COLUMNS_MUL_IDEAL»
  RING_DET_DIAGONAL_CONGRUENCE := SessionLibrary.RingDet.«RING_DET_DIAGONAL_CONGRUENCE»
  RING_DET_HOMOMORPHISM := SessionLibrary.RingDet.«RING_DET_HOMOMORPHISM»
  RING_HOMOMORPHISM_SUB := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUB»
  RING_IDEAL_0 := SessionLibrary.RingTheory.«RING_IDEAL_0»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_IDEAL_SETADD := SessionLibrary.RingTheory.«RING_IDEAL_SETADD»
  RING_MONIC_RELATION_FACTOR := SessionLibrary.RingTheory.«RING_MONIC_RELATION_FACTOR»
  RING_MONOMORPHISM_EQ_0 := SessionLibrary.RingTheory.«RING_MONOMORPHISM_EQ_0»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MULTSYS_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_MULTSYS_HOMOMORPHIC_IMAGE»
  RING_MULTSYS_NONPRIME := SessionLibrary.RingTheory.«RING_MULTSYS_NONPRIME»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_IN_PRIME_IDEAL := SessionLibrary.RingTheory.«RING_MUL_IN_PRIME_IDEAL»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_IN_PRIME_IDEAL := SessionLibrary.RingTheory.«RING_POW_IN_PRIME_IDEAL»
  RING_SETADD_SUPERSET_LEFT := SessionLibrary.RingTheory.«RING_SETADD_SUPERSET_LEFT»
  RING_SETADD_SUPERSET_RIGHT := SessionLibrary.RingTheory.«RING_SETADD_SUPERSET_RIGHT»
  RING_SPAN_FINITE := SessionLibrary.FieldTheory.«RING_SPAN_FINITE»
  RING_SPAN_INC := SessionLibrary.FieldTheory.«RING_SPAN_INC»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_RDISTRIB := SessionLibrary.RingTheory.«RING_SUB_RDISTRIB»
  RING_SUM := SessionLibrary.RingTheory.«RING_SUM»
  RING_SUM_ADD := SessionLibrary.RingTheory.«RING_SUM_ADD»
  RING_SUM_CLAUSES := SessionLibrary.RingTheory.«RING_SUM_CLAUSES»
  RING_SUM_CLOSED := SessionLibrary.RingTheory.«RING_SUM_CLOSED»
  RING_SUM_DELTA := SessionLibrary.RingTheory.«RING_SUM_DELTA»
  RING_SUM_EQ := SessionLibrary.RingTheory.«RING_SUM_EQ»
  RING_SUM_EQ_0 := SessionLibrary.RingTheory.«RING_SUM_EQ_0»
  RING_SUM_LMUL := SessionLibrary.RingTheory.«RING_SUM_LMUL»
  RING_SUM_RMUL := SessionLibrary.RingTheory.«RING_SUM_RMUL»
  RING_SUM_SUB := SessionLibrary.RingTheory.«RING_SUM_SUB»
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM_EQ := Session.SUBSET_ANTISYM_EQ
  SUBSET_TRANS := Session.SUBSET_TRANS
  UNIONS_GSPEC := Session.UNIONS_GSPEC
  maximal_ideal := SessionLibrary.RingTheory.«maximal_ideal»
  num_WOP := Session.num_WOP
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_setadd := SessionLibrary.RingTheory.«ring_setadd»

/-- What integral_primes.ml uses from Session. -/
def deps : HolANT.IntegralPrimes.IntegralPrimesDeps where
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

/- The bundles, in integral_primes.ml order. -/
initialize BIntegralPrimes : HolANT.IntegralPrimes.IntegralPrimes ←
  ioB "setupIntegralPrimes" (HolANT.IntegralPrimes.setupIntegralPrimes deps).run

-- IntegralPrimes
def INTEGRAL_DETERMINANT_TRICK_IDEAL : thm := BIntegralPrimes.INTEGRAL_DETERMINANT_TRICK_IDEAL
def RING_SPAN_IDEAL_COMBINATION : thm := BIntegralPrimes.RING_SPAN_IDEAL_COMBINATION
def INTEGRAL_EXTENSION_PRIME_ABOVE : thm := BIntegralPrimes.INTEGRAL_EXTENSION_PRIME_ABOVE
def INTEGRAL_EXTENSION_LYING_OVER : thm := BIntegralPrimes.INTEGRAL_EXTENSION_LYING_OVER
def INTEGRAL_EXTENSION_GOING_UP : thm := BIntegralPrimes.INTEGRAL_EXTENSION_GOING_UP
def INTEGRAL_EXTENSION_INCOMPARABLE : thm := BIntegralPrimes.INTEGRAL_EXTENSION_INCOMPARABLE
def INTEGRAL_EXTENSION_MAXIMAL_IDEAL : thm := BIntegralPrimes.INTEGRAL_EXTENSION_MAXIMAL_IDEAL
def INTEGRAL_EXTENSION_PRIME_NONZERO : thm := BIntegralPrimes.INTEGRAL_EXTENSION_PRIME_NONZERO

/-- `needs "ANT/integral_primes.ml"`: already done by importing this module. -/
def ensureIntegralPrimes : IO Unit := pure ()

end SessionANT.IntegralPrimes
