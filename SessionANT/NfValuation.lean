/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/nf_valuation.ml                               . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/NfValuation.lean

  The session half of the nf_valuation.ml translation: it supplies HolANT.NfValuation's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/nf_valuation.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.NfValuation
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionANT.IdealArith
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionLibrary.Matroids
import SessionLibrary.FieldTheory
import SessionANT.Integral
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.IdealNorm
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.RingOfIntegers
import SessionANT.NormIndex
import SessionANT.Classgroup

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.NfValuation

/-- The core theorems nf_valuation.ml uses. -/
def core1 : HolANT.NfValuation.CoreThms1 where
  DEDEKIND_DENOMINATOR_IDEAL := SessionANT.DedekindValuation.«DEDEKIND_DENOMINATOR_IDEAL»
  DEDEKIND_IDEAL_FACTORIZATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_FACTORIZATION»
  DEDEKIND_IDEAL_MUL_INTEGRAL := SessionANT.DedekindValuation.«DEDEKIND_IDEAL_MUL_INTEGRAL»
  DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS := SessionANT.DedekindValuation.«DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS»
  DEDEKIND_IDEAL_SUBSET_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_VALUATION»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  DEDEKIND_VALUATION := SessionANT.DedekindValuation.«DEDEKIND_VALUATION»
  DEDEKIND_VALUATION_1 := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_1»
  DEDEKIND_VALUATION_ADD := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_ADD»
  DEDEKIND_VALUATION_ADD_STRICT := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_ADD_STRICT»
  DEDEKIND_VALUATION_APPROXIMATION := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_APPROXIMATION»
  DEDEKIND_VALUATION_DIV := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_DIV»
  DEDEKIND_VALUATION_EQ := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_EQ»
  DEDEKIND_VALUATION_FINITE := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_FINITE»
  DEDEKIND_VALUATION_IMAGE := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_IMAGE»
  DEDEKIND_VALUATION_INTEGRAL := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_INTEGRAL»
  DEDEKIND_VALUATION_INV := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_INV»
  DEDEKIND_VALUATION_MUL := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_MUL»
  DEDEKIND_VALUATION_NEG := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_NEG»
  DEDEKIND_VALUATION_POW := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_POW»
  DEDEKIND_VALUATION_PRIME_IDEAL := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_PRIME_IDEAL»
  DEDEKIND_VALUATION_UNIT := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_UNIT»
  DIVIDES_LE_IMP := Session.DIVIDES_LE_IMP
  EXISTS_IN_IMAGE := Session.EXISTS_IN_IMAGE
  EXP_ONE := Session.EXP_ONE
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_INV_EQ_0 := SessionLibrary.RingTheory.«FIELD_INV_EQ_0»
  FIELD_MUL_RINV := SessionLibrary.RingTheory.«FIELD_MUL_RINV»
  FINITE_FINITE_UNIONS := Session.FINITE_FINITE_UNIONS
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_NORM_IDEAL_POW := SessionANT.IdealNorm.«IDEAL_NORM_IDEAL_POW»
  IDEAL_NORM_IN_IDEAL := SessionANT.IdealNorm.«IDEAL_NORM_IN_IDEAL»
  IDEAL_NORM_POS := SessionANT.IdealNorm.«IDEAL_NORM_POS»
  IDEAL_NORM_SUBSET_DIVIDES := SessionANT.IdealNorm.«IDEAL_NORM_SUBSET_DIVIDES»
  IDEAL_POW_EQ_ZERO := SessionANT.IdealArith.«IDEAL_POW_EQ_ZERO»
  IDEAL_VALUATION_EQ_0 := SessionANT.Dedekind.«IDEAL_VALUATION_EQ_0»
  IDEAL_VALUATION_IDEAL_POW := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_POW»
  IDEAL_VALUATION_IDEAL_PROD := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_PROD»
  IMAGE_I := Session.IMAGE_I
  IMP_CONJ := Session.IMP_CONJ
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_POW_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_POW_EQ_0»
  INTEGRAL_DOMAIN_RING_OF_INTEGERS := SessionANT.Numfield.«INTEGRAL_DOMAIN_RING_OF_INTEGERS»
  INT_MAX := Session.INT_MAX
  INT_MUL_RNEG := Session.INT_MUL_RNEG
  INT_MUL_RZERO := Session.INT_MUL_RZERO
  INT_OF_NUM_ADD := Session.INT_OF_NUM_ADD
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LE := Session.INT_OF_NUM_LE
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_POS := Session.INT_POS
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_CLASS := SessionANT.DedekindStruct.«IN_IDEAL_CLASS»
  IN_UNIONS := Session.IN_UNIONS
  I_DEF := Session.I_DEF
  I_THM := Session.I_THM
  LE_REFL := Session.LE_REFL
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM := SessionANT.Classgroup.«NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM»
  NUMBER_FIELD_IDEAL_CLASS_BOUND := SessionANT.Classgroup.«NUMBER_FIELD_IDEAL_CLASS_BOUND»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_DIV := SessionLibrary.RingTheory.«RING_DIV»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_INCLUSION := SessionLibrary.RingTheory.«RING_MONOMORPHISM_INCLUSION»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_DENOMINATOR := SessionANT.Numfield.«RING_OF_INTEGERS_DENOMINATOR»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_NUM_1 := SessionLibrary.RingTheory.«RING_OF_NUM_1»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  SUBSET := Session.SUBSET
  field_of_fractions := SessionLibrary.RingTheory.«field_of_fractions»
  ring_div := SessionLibrary.RingTheory.«ring_div»
  ring_of_integers := SessionANT.Numfield.«ring_of_integers»

/-- What nf_valuation.ml uses from Session. -/
def deps : HolANT.NfValuation.NfValuationDeps where
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

/- The bundles, in nf_valuation.ml order. -/
initialize BNfValuation : HolANT.NfValuation.NfValuation ←
  ioB "setupNfValuation" (HolANT.NfValuation.setupNfValuation deps).run

-- NfValuation
def RING_OF_INTEGERS_FRACTION_FIELD : thm := BNfValuation.RING_OF_INTEGERS_FRACTION_FIELD
def NUMBER_FIELD_VALUATION : thm := BNfValuation.NUMBER_FIELD_VALUATION
def NUMBER_FIELD_VALUATION_RING_OF_INTEGERS : thm := BNfValuation.NUMBER_FIELD_VALUATION_RING_OF_INTEGERS
def NUMBER_FIELD_VALUATION_1 : thm := BNfValuation.NUMBER_FIELD_VALUATION_1
def NUMBER_FIELD_VALUATION_MUL : thm := BNfValuation.NUMBER_FIELD_VALUATION_MUL
def NUMBER_FIELD_VALUATION_INV : thm := BNfValuation.NUMBER_FIELD_VALUATION_INV
def NUMBER_FIELD_VALUATION_DIV : thm := BNfValuation.NUMBER_FIELD_VALUATION_DIV
def NUMBER_FIELD_VALUATION_POW : thm := BNfValuation.NUMBER_FIELD_VALUATION_POW
def NUMBER_FIELD_VALUATION_NEG : thm := BNfValuation.NUMBER_FIELD_VALUATION_NEG
def NUMBER_FIELD_VALUATION_ADD : thm := BNfValuation.NUMBER_FIELD_VALUATION_ADD
def NUMBER_FIELD_VALUATION_ADD_STRICT : thm := BNfValuation.NUMBER_FIELD_VALUATION_ADD_STRICT
def NUMBER_FIELD_VALUATION_FINITE : thm := BNfValuation.NUMBER_FIELD_VALUATION_FINITE
def NUMBER_FIELD_VALUATION_INTEGRAL : thm := BNfValuation.NUMBER_FIELD_VALUATION_INTEGRAL
def NUMBER_FIELD_VALUATION_UNIT : thm := BNfValuation.NUMBER_FIELD_VALUATION_UNIT
def NUMBER_FIELD_VALUATION_PRIME_IDEAL : thm := BNfValuation.NUMBER_FIELD_VALUATION_PRIME_IDEAL
def NUMBER_FIELD_VALUATION_EQ : thm := BNfValuation.NUMBER_FIELD_VALUATION_EQ
def NUMBER_FIELD_VALUATION_APPROXIMATION : thm := BNfValuation.NUMBER_FIELD_VALUATION_APPROXIMATION
def NUMBER_FIELD_VALUATION_PRINCIPAL_OUTSIDE : thm := BNfValuation.NUMBER_FIELD_VALUATION_PRINCIPAL_OUTSIDE
def NUMBER_FIELD_DENOMINATOR_IDEAL : thm := BNfValuation.NUMBER_FIELD_DENOMINATOR_IDEAL
def NUMBER_FIELD_IDEAL_MUL_INTEGRAL : thm := BNfValuation.NUMBER_FIELD_IDEAL_MUL_INTEGRAL
def NUMBER_FIELD_ROOT_DENOMINATOR : thm := BNfValuation.NUMBER_FIELD_ROOT_DENOMINATOR

/-- `needs "ANT/nf_valuation.ml"`: already done by importing this module. -/
def ensureNfValuation : IO Unit := pure ()

end SessionANT.NfValuation
