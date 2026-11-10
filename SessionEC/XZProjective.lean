/- ---------------------------------------------------------------------- -/
/- Session wiring for EC/xzprojective.ml                               . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionEC/XZProjective.lean

  The session half of the xzprojective.ml translation: it supplies HolEC.XZProjective's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "EC/xzprojective.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolEC.XZProjective
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionEC.XZProjective

/-- The core theorems xzprojective.ml uses. -/
def core1 : HolEC.XZProjective.CoreThms1 where
  ADD1 := Session.ADD1
  COND_SWAP := Session.COND_SWAP
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  FIELD_CHAR_NOT2 := SessionEC.Misc.«FIELD_CHAR_NOT2»
  FIELD_CHAR_NOT23 := SessionEC.Misc.«FIELD_CHAR_NOT23»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FORALL_OPTION_THM := Session.FORALL_OPTION_THM
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  GROUP_POW := SessionLibrary.GroupTheory.«GROUP_POW»
  GROUP_POW_1 := SessionLibrary.GroupTheory.«GROUP_POW_1»
  GROUP_POW_ADD := SessionLibrary.GroupTheory.«GROUP_POW_ADD»
  GROUP_POW_ID := SessionLibrary.GroupTheory.«GROUP_POW_ID»
  GROUP_POW_MONTGOMERY_TORSION := SessionEC.Montgomery.«GROUP_POW_MONTGOMERY_TORSION»
  IMP_CONJ := Session.IMP_CONJ
  IN := Session.IN
  LET_DEF := Session.LET_DEF
  LET_END_DEF := Session.LET_END_DEF
  MONTGOMERY_GROUP := SessionEC.Montgomery.«MONTGOMERY_GROUP»
  MULT_2 := Session.MULT_2
  PAIR_EQ := Session.PAIR_EQ
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_INV_1 := SessionLibrary.RingTheory.«RING_INV_1»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  montgomery_add := SessionEC.Montgomery.«montgomery_add»
  montgomery_curve := SessionEC.Montgomery.«montgomery_curve»
  montgomery_neg := SessionEC.Montgomery.«montgomery_neg»
  montgomery_nonsingular := SessionEC.Montgomery.«montgomery_nonsingular»
  option_DISTINCT := Session.indTypesBoot.option_DISTINCT
  option_INJ := Session.indTypesBoot.option_INJ
  ring_div := SessionLibrary.RingTheory.«ring_div»

/-- What xzprojective.ml uses from Session. -/
def deps : HolEC.XZProjective.XZProjectiveDeps where
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

/- The bundles, in xzprojective.ml order. -/
initialize BXZProjectiveThms : HolEC.XZProjective.XZProjectiveThms ←
  ioB "setupXZProjectiveThms" (HolEC.XZProjective.setupXZProjectiveThms deps).run

-- XZProjectiveThms
def montgomery_xz : thm := BXZProjectiveThms.montgomery_xz
def MONTGOMERY_XZ_IN_CARRIER : thm := BXZProjectiveThms.MONTGOMERY_XZ_IN_CARRIER
def montgomery_xzdouble : thm := BXZProjectiveThms.montgomery_xzdouble
def montgomery_xzdiffadd : thm := BXZProjectiveThms.montgomery_xzdiffadd
def MONTGOMERY_XZDOUBLE : thm := BXZProjectiveThms.MONTGOMERY_XZDOUBLE
def MONTGOMERY_XZDIFFADD : thm := BXZProjectiveThms.MONTGOMERY_XZDIFFADD
def MONTGOMERY_XZDOUBLE_GROUP : thm := BXZProjectiveThms.MONTGOMERY_XZDOUBLE_GROUP
def MONTGOMERY_XZDIFFADD_GROUP : thm := BXZProjectiveThms.MONTGOMERY_XZDIFFADD_GROUP
def montgomery_xmap : thm := BXZProjectiveThms.montgomery_xmap
def MONTGOMERY_XZ_XMAP : thm := BXZProjectiveThms.MONTGOMERY_XZ_XMAP
def MONTGOMERY_XMAP_EQ_0 : thm := BXZProjectiveThms.MONTGOMERY_XMAP_EQ_0
def MONTGOMERY_XMAP_EQ_0_POW : thm := BXZProjectiveThms.MONTGOMERY_XMAP_EQ_0_POW
def MONTGOMERY_ADD_YRECOVERY : thm := BXZProjectiveThms.MONTGOMERY_ADD_YRECOVERY

/-- `needs "EC/xzprojective.ml"`: already done by importing this module. -/
def ensureXZProjective : IO Unit := pure ()

end SessionEC.XZProjective
