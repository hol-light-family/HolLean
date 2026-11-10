/- ---------------------------------------------------------------------- -/
/- Session wiring for EC/formulary_xzprojective.ml                     . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionEC/FormularyXZProjective.lean

  The session half of the formulary_xzprojective.ml translation: it supplies HolEC.FormularyXZProjective's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "EC/formulary_xzprojective.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolEC.FormularyXZProjective
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Integer
import SessionLibrary.Isum
import SessionLibrary.Binomial
import SessionLibrary.Products
import SessionLibrary.Multiplicative
import SessionLibrary.Primitive
import SessionLibrary.Frag
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.GroupTheory
import SessionLibrary.RingTheory
import SessionEC.Misc
import SessionEC.Montgomery
import SessionEC.XZProjective

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionEC.FormularyXZProjective

/-- The core theorems formulary_xzprojective.ml uses. -/
def core1 : HolEC.FormularyXZProjective.CoreThms1 where
  CONJ_ASSOC := Session.CONJ_ASSOC
  FIELD_CHAR_NOT2 := SessionEC.Misc.«FIELD_CHAR_NOT2»
  FIELD_MUL_EQ_0 := SessionLibrary.RingTheory.«FIELD_MUL_EQ_0»
  FORALL_OPTION_THM := Session.FORALL_OPTION_THM
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  LET_DEF := Session.LET_DEF
  LET_END_DEF := Session.LET_END_DEF
  PAIR_EQ := Session.PAIR_EQ
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  montgomery_add := SessionEC.Montgomery.«montgomery_add»
  montgomery_curve := SessionEC.Montgomery.«montgomery_curve»
  montgomery_xz := SessionEC.XZProjective.«montgomery_xz»
  montgomery_xzdiffadd := SessionEC.XZProjective.«montgomery_xzdiffadd»
  montgomery_xzdouble := SessionEC.XZProjective.«montgomery_xzdouble»
  option_DISTINCT := Session.indTypesBoot.option_DISTINCT
  option_INJ := Session.indTypesBoot.option_INJ

/-- What formulary_xzprojective.ml uses from Session. -/
def deps : HolEC.FormularyXZProjective.FormularyXZProjectiveDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  METIS_TAC := Session.METIS_TAC
  ASM_METIS_TAC := Session.ASM_METIS_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  TAUT t := ExceptT.mk (Session.TAUT t)
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
  RING_RULE t := ExceptT.mk (SessionLibrary.RingTheory.RING_RULE t)
  INTEGRAL_DOMAIN_RULE t := ExceptT.mk (SessionLibrary.RingTheory.INTEGRAL_DOMAIN_RULE t)
  FIELD_TAC := SessionLibrary.RingTheory.FIELD_TAC
  RING_CARRIER_TAC := SessionLibrary.RingTheory.RING_CARRIER_TAC
  RING_TAC := SessionLibrary.RingTheory.RING_TAC
  RING_PULL_DIV_TAC := SessionLibrary.RingTheory.RING_PULL_DIV_TAC
  LET_TAC := Session.LET_TAC
  GROUP_RULE t := ExceptT.mk (SessionLibrary.GroupTheory.GROUP_RULE t)
  basic_ss := Session.basic_ss
  INTEGER_MOD_RING_RED_CONV := SessionLibrary.RingTheory.INTEGER_MOD_RING_RED_CONV
  NOT_RING_CHAR_DIVIDES_TAC := SessionEC.Misc.NOT_RING_CHAR_DIVIDES_TAC
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in formulary_xzprojective.ml order. -/
initialize BFormularyXZProjectiveThms : HolEC.FormularyXZProjective.FormularyXZProjectiveThms ←
  ioB "setupFormularyXZProjectiveThms" (HolEC.FormularyXZProjective.setupFormularyXZProjectiveThms deps).run

-- FormularyXZProjectiveThms
def mladd_1987_m : thm := BFormularyXZProjectiveThms.mladd_1987_m
def MLADD_1987_M : thm := BFormularyXZProjectiveThms.MLADD_1987_M
def okeya_sakurai_1 : thm := BFormularyXZProjectiveThms.okeya_sakurai_1
def OKEYA_SAKURAI_1 : thm := BFormularyXZProjectiveThms.OKEYA_SAKURAI_1

/-- `needs "EC/formulary_xzprojective.ml"`: already done by importing this module. -/
def ensureFormularyXZProjective : IO Unit := pure ()

end SessionEC.FormularyXZProjective
