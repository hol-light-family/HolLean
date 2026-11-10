/- ---------------------------------------------------------------------- -/
/- Session wiring for EC/jacobian.ml                                   . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionEC/Jacobian.lean

  The session half of the jacobian.ml translation: it supplies HolEC.Jacobian's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "EC/jacobian.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolEC.Jacobian
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
import SessionEC.Weierstrass

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionEC.Jacobian

/-- The core theorems jacobian.ml uses. -/
def core1 : HolEC.Jacobian.CoreThms1 where
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  FIELD_CHAR_NOT23 := SessionEC.Misc.«FIELD_CHAR_NOT23»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FORALL_OPTION_THM := Session.FORALL_OPTION_THM
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  LET_DEF := Session.LET_DEF
  LET_END_DEF := Session.LET_END_DEF
  PAIR_EQ := Session.PAIR_EQ
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_DIV := SessionLibrary.RingTheory.«RING_DIV»
  RING_DIV_1 := SessionLibrary.RingTheory.«RING_DIV_1»
  RING_INV_POW := SessionLibrary.RingTheory.«RING_INV_POW»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_ONE := SessionLibrary.RingTheory.«RING_POW_ONE»
  WEIERSTRASS_CURVE_IMP_POINT := SessionEC.Weierstrass.«WEIERSTRASS_CURVE_IMP_POINT»
  WEIERSTRASS_POINT_ADD := SessionEC.Weierstrass.«WEIERSTRASS_POINT_ADD»
  WEIERSTRASS_POINT_NEG := SessionEC.Weierstrass.«WEIERSTRASS_POINT_NEG»
  field := SessionLibrary.RingTheory.«field»
  option_DISTINCT := Session.indTypesBoot.option_DISTINCT
  option_INJ := Session.indTypesBoot.option_INJ
  ring_div := SessionLibrary.RingTheory.«ring_div»
  weierstrass_add := SessionEC.Weierstrass.«weierstrass_add»
  weierstrass_curve := SessionEC.Weierstrass.«weierstrass_curve»
  weierstrass_neg := SessionEC.Weierstrass.«weierstrass_neg»
  weierstrass_point := SessionEC.Weierstrass.«weierstrass_point»

/-- What jacobian.ml uses from Session. -/
def deps : HolEC.Jacobian.JacobianDeps where
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

/- The bundles, in jacobian.ml order. -/
initialize BJacobianDefs : HolEC.Jacobian.JacobianDefs ←
  ioB "setupJacobianDefs" (HolEC.Jacobian.setupJacobianDefs deps).run
initialize BJacobianOps : HolEC.Jacobian.JacobianOps ←
  ioB "setupJacobianOps" (HolEC.Jacobian.setupJacobianOps deps BJacobianDefs).run
initialize BJacobianUnexc : HolEC.Jacobian.JacobianUnexc ←
  ioB "setupJacobianUnexc" (HolEC.Jacobian.setupJacobianUnexc deps BJacobianDefs).run

-- JacobianDefs
def jacobian_point : thm := BJacobianDefs.jacobian_point
def jacobian_curve : thm := BJacobianDefs.jacobian_curve
def weierstrass_of_jacobian : thm := BJacobianDefs.weierstrass_of_jacobian
def jacobian_of_weierstrass : thm := BJacobianDefs.jacobian_of_weierstrass
def jacobian_eq : thm := BJacobianDefs.jacobian_eq
def jacobian_0 : thm := BJacobianDefs.jacobian_0
def jacobian_neg : thm := BJacobianDefs.jacobian_neg
def jacobian_add : thm := BJacobianDefs.jacobian_add
def JACOBIAN_CURVE_IMP_POINT : thm := BJacobianDefs.JACOBIAN_CURVE_IMP_POINT
def JACOBIAN_OF_WEIERSTRASS_POINT_EQ : thm := BJacobianDefs.JACOBIAN_OF_WEIERSTRASS_POINT_EQ
def JACOBIAN_OF_WEIERSTRASS_POINT : thm := BJacobianDefs.JACOBIAN_OF_WEIERSTRASS_POINT
def WEIERSTRASS_OF_JACOBIAN_POINT : thm := BJacobianDefs.WEIERSTRASS_OF_JACOBIAN_POINT
def JACOBIAN_OF_WEIERSTRASS_EQ : thm := BJacobianDefs.JACOBIAN_OF_WEIERSTRASS_EQ
def WEIERSTRASS_OF_JACOBIAN_EQ : thm := BJacobianDefs.WEIERSTRASS_OF_JACOBIAN_EQ
def WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS : thm := BJacobianDefs.WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS
def JACOBIAN_OF_WEIERSTRASS_OF_JACOBIAN : thm := BJacobianDefs.JACOBIAN_OF_WEIERSTRASS_OF_JACOBIAN
def JACOBIAN_OF_WEIERSTRASS_CURVE_EQ : thm := BJacobianDefs.JACOBIAN_OF_WEIERSTRASS_CURVE_EQ
def JACOBIAN_OF_WEIERSTRASS_CURVE : thm := BJacobianDefs.JACOBIAN_OF_WEIERSTRASS_CURVE
def WEIERSTRASS_OF_JACOBIAN_CURVE : thm := BJacobianDefs.WEIERSTRASS_OF_JACOBIAN_CURVE

-- JacobianOps
def JACOBIAN_POINT_NEG : thm := BJacobianOps.JACOBIAN_POINT_NEG
def JACOBIAN_CURVE_NEG : thm := BJacobianOps.JACOBIAN_CURVE_NEG
def WEIERSTRASS_OF_JACOBIAN_NEG : thm := BJacobianOps.WEIERSTRASS_OF_JACOBIAN_NEG
def JACOBIAN_EQ_NEG : thm := BJacobianOps.JACOBIAN_EQ_NEG
def WEIERSTRASS_OF_JACOBIAN_NEG_OF_WEIERSTRASS : thm := BJacobianOps.WEIERSTRASS_OF_JACOBIAN_NEG_OF_WEIERSTRASS
def JACOBIAN_OF_WEIERSTRASS_NEG : thm := BJacobianOps.JACOBIAN_OF_WEIERSTRASS_NEG
def JACOBIAN_POINT_ADD : thm := BJacobianOps.JACOBIAN_POINT_ADD
def JACOBIAN_CURVE_ADD : thm := BJacobianOps.JACOBIAN_CURVE_ADD
def WEIERSTRASS_OF_JACOBIAN_ADD : thm := BJacobianOps.WEIERSTRASS_OF_JACOBIAN_ADD
def JACOBIAN_EQ_ADD : thm := BJacobianOps.JACOBIAN_EQ_ADD
def WEIERSTRASS_OF_JACOBIAN_ADD_OF_WEIERSTRASS : thm := BJacobianOps.WEIERSTRASS_OF_JACOBIAN_ADD_OF_WEIERSTRASS
def JACOBIAN_OF_WEIERSTRASS_ADD : thm := BJacobianOps.JACOBIAN_OF_WEIERSTRASS_ADD

-- JacobianUnexc
def jacobian_add_unexceptional : thm := BJacobianUnexc.jacobian_add_unexceptional
def WEIERSTRASS_OF_JACOBIAN_ADD_UNEXCEPTIONAL : thm := BJacobianUnexc.WEIERSTRASS_OF_JACOBIAN_ADD_UNEXCEPTIONAL
def jacobian_double_unexceptional : thm := BJacobianUnexc.jacobian_double_unexceptional
def WEIERSTRASS_OF_JACOBIAN_DOUBLE_UNEXCEPTIONAL : thm := BJacobianUnexc.WEIERSTRASS_OF_JACOBIAN_DOUBLE_UNEXCEPTIONAL

/-- `needs "EC/jacobian.ml"`: already done by importing this module. -/
def ensureJacobian : IO Unit := pure ()

end SessionEC.Jacobian
