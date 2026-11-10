/- ---------------------------------------------------------------------- -/
/- Session wiring for EC/formulary_jacobian.ml                         . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionEC/FormularyJacobian.lean

  The session half of the formulary_jacobian.ml translation: it supplies HolEC.FormularyJacobian's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "EC/formulary_jacobian.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolEC.FormularyJacobian
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
import SessionEC.Jacobian

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionEC.FormularyJacobian

/-- The core theorems formulary_jacobian.ml uses. -/
def core1 : HolEC.FormularyJacobian.CoreThms1 where
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  LET_DEF := Session.LET_DEF
  LET_END_DEF := Session.LET_END_DEF
  PAIR_EQ := Session.PAIR_EQ
  PRIME_2 := SessionLibrary.Prime.«PRIME_2»
  RING_CHAR_DIVIDES_PRIME := SessionLibrary.RingTheory.«RING_CHAR_DIVIDES_PRIME»
  jacobian_0 := SessionEC.Jacobian.«jacobian_0»
  jacobian_add := SessionEC.Jacobian.«jacobian_add»
  jacobian_eq := SessionEC.Jacobian.«jacobian_eq»
  jacobian_neg := SessionEC.Jacobian.«jacobian_neg»
  jacobian_point := SessionEC.Jacobian.«jacobian_point»

/-- What formulary_jacobian.ml uses from Session. -/
def deps : HolEC.FormularyJacobian.FormularyJacobianDeps where
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

/- The bundles, in formulary_jacobian.ml order. -/
initialize BFormularyJacobianThms : HolEC.FormularyJacobian.FormularyJacobianThms ←
  ioB "setupFormularyJacobianThms" (HolEC.FormularyJacobian.setupFormularyJacobianThms deps).run

-- FormularyJacobianThms
def ja_dbl_2007_bl : thm := BFormularyJacobianThms.ja_dbl_2007_bl
def JA_DBL_2007_BL : thm := BFormularyJacobianThms.JA_DBL_2007_BL
def JA_DBL_2007_BL' : thm := BFormularyJacobianThms.JA_DBL_2007_BL'
def j3_dbl_2001_b : thm := BFormularyJacobianThms.j3_dbl_2001_b
def J3_DBL_2001_B : thm := BFormularyJacobianThms.J3_DBL_2001_B
def J3_DBL_2001_B' : thm := BFormularyJacobianThms.J3_DBL_2001_B'
def j0_dbl_2009_l : thm := BFormularyJacobianThms.j0_dbl_2009_l
def J0_DBL_2009_L : thm := BFormularyJacobianThms.J0_DBL_2009_L
def J0_DBL_2009_L' : thm := BFormularyJacobianThms.J0_DBL_2009_L'
def ja_add_2007_bl : thm := BFormularyJacobianThms.ja_add_2007_bl
def JA_ADD_2007_BL : thm := BFormularyJacobianThms.JA_ADD_2007_BL
def ja_madd_2007_bl : thm := BFormularyJacobianThms.ja_madd_2007_bl
def JA_MADD_2007_BL : thm := BFormularyJacobianThms.JA_MADD_2007_BL

/-- `needs "EC/formulary_jacobian.ml"`: already done by importing this module. -/
def ensureFormularyJacobian : IO Unit := pure ()

end SessionEC.FormularyJacobian
