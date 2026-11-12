/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/ufd.ml                                        . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/Ufd.lean

  The session half of the ufd.ml translation: it supplies HolANT.Ufd's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/ufd.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.Ufd
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.Ufd

/-- The core theorems ufd.ml uses. -/
def core1 : HolANT.Ufd.CoreThms1 where
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INTEGRAL_DOMAIN_MUL_LCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_LCANCEL»
  INTEGRAL_DOMAIN_POW_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_POW_EQ_0»
  INTEGRAL_DOMAIN_PRIME_COPRIME_EQ := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_PRIME_COPRIME_EQ»
  MONO_EXISTS := Session.MONO_EXISTS
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ASSOCIATES_LMUL := SessionLibrary.RingTheory.«RING_ASSOCIATES_LMUL»
  RING_ASSOCIATES_SYM := SessionLibrary.RingTheory.«RING_ASSOCIATES_SYM»
  RING_COPRIME_0 := SessionLibrary.RingTheory.«RING_COPRIME_0»
  RING_COPRIME_DIVPROD_RIGHT := SessionLibrary.RingTheory.«RING_COPRIME_DIVPROD_RIGHT»
  RING_COPRIME_LMUL := SessionLibrary.RingTheory.«RING_COPRIME_LMUL»
  RING_COPRIME_RPOW := SessionLibrary.RingTheory.«RING_COPRIME_RPOW»
  RING_COPRIME_SYM := SessionLibrary.RingTheory.«RING_COPRIME_SYM»
  RING_DIVIDES_REFL := SessionLibrary.RingTheory.«RING_DIVIDES_REFL»
  RING_DIVIDES_RMUL := SessionLibrary.RingTheory.«RING_DIVIDES_RMUL»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_POW := SessionLibrary.RingTheory.«RING_MUL_POW»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_SYM := SessionLibrary.RingTheory.«RING_MUL_SYM»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_ONE := SessionLibrary.RingTheory.«RING_POW_ONE»
  RING_POW_ZERO := SessionLibrary.RingTheory.«RING_POW_ZERO»
  RING_PRIME_DIVIDES_MUL := SessionLibrary.RingTheory.«RING_PRIME_DIVIDES_MUL»
  RING_UNIT_1 := SessionLibrary.RingTheory.«RING_UNIT_1»
  RING_UNIT_IN_CARRIER := SessionLibrary.RingTheory.«RING_UNIT_IN_CARRIER»
  RING_UNIT_MUL_EQ := SessionLibrary.RingTheory.«RING_UNIT_MUL_EQ»
  RING_UNIT_POW := SessionLibrary.RingTheory.«RING_UNIT_POW»
  UFD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«UFD_IMP_INTEGRAL_DOMAIN»
  UFD_PRIME_FACTOR_INDUCT := SessionLibrary.RingTheory.«UFD_PRIME_FACTOR_INDUCT»
  ring_coprime := SessionLibrary.RingTheory.«ring_coprime»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_prime := SessionLibrary.RingTheory.«ring_prime»
  ring_unit := SessionLibrary.RingTheory.«ring_unit»

/-- What ufd.ml uses from Session. -/
def deps : HolANT.Ufd.UfdDeps where
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

/- The bundles, in ufd.ml order. -/
initialize BUfd : HolANT.Ufd.Ufd ←
  ioB "setupUfd" (HolANT.Ufd.setupUfd deps).run

-- Ufd
def UFD_COPRIME_MUL_POW : thm := BUfd.UFD_COPRIME_MUL_POW
def UFD_COPRIME_MUL_POW_ASSOCIATES : thm := BUfd.UFD_COPRIME_MUL_POW_ASSOCIATES

/-- `needs "ANT/ufd.ml"`: already done by importing this module. -/
def ensureUfd : IO Unit := pure ()

end SessionANT.Ufd
