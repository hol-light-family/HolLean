/- ---------------------------------------------------------------------- -/
/- Session wiring for EC/wei25519.ml                                   . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionEC/Wei25519.lean

  The session half of the wei25519.ml translation: it supplies HolEC.Wei25519's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "EC/wei25519.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolEC.Wei25519
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
import SessionEC.ExcludeRoots
import SessionEC.ComputeGroup

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionEC.Wei25519

/-- The core theorems wei25519.ml uses. -/
def core1 : HolEC.Wei25519.CoreThms1 where
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  CARD_BOUND_WEIERSTRASS_CURVE := SessionEC.Weierstrass.«CARD_BOUND_WEIERSTRASS_CURVE»
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_INTEGER_MOD_RING := SessionLibrary.RingTheory.«CARD_INTEGER_MOD_RING»
  CYCLIC_GROUP_ALT := SessionLibrary.GroupTheory.«CYCLIC_GROUP_ALT»
  CYCLIC_IMP_ABELIAN_GROUP := SessionLibrary.GroupTheory.«CYCLIC_IMP_ABELIAN_GROUP»
  FIELD_INTEGER_MOD_RING := SessionLibrary.RingTheory.«FIELD_INTEGER_MOD_RING»
  FINITE_INTEGER_MOD_RING := SessionLibrary.RingTheory.«FINITE_INTEGER_MOD_RING»
  FINITE_WEIERSTRASS_CURVE := SessionEC.Weierstrass.«FINITE_WEIERSTRASS_CURVE»
  GROUP_CARRIER_NONEMPTY := SessionLibrary.GroupTheory.«GROUP_CARRIER_NONEMPTY»
  GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER»
  GROUP_ELEMENT_ORDER_MUL_EQ := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_MUL_EQ»
  GROUP_ELEMENT_ORDER_UNIQUE_ALT := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_UNIQUE_ALT»
  GROUP_ELEMENT_ORDER_UNIQUE_PRIME := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_UNIQUE_PRIME»
  HAS_SIZE := Session.HAS_SIZE
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  INTEGER_MOD_RING_CHAR := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CHAR»
  INTEGER_MOD_RING_CLAUSES := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CLAUSES»
  IN_ELIM_THM := Session.IN_ELIM_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_MULT_RCANCEL := Session.LE_MULT_RCANCEL
  MULT_CLAUSES := Session.MULT_CLAUSES
  SUBGROUP_GENERATED_ELEMENT_ORDER := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_ELEMENT_ORDER»
  WEIERSTRASS_GROUP := SessionEC.Weierstrass.«WEIERSTRASS_GROUP»
  divides := Session.divides
  option_DISTINCT := Session.indTypesBoot.option_DISTINCT
  weierstrass_add := SessionEC.Weierstrass.«weierstrass_add»
  weierstrass_curve := SessionEC.Weierstrass.«weierstrass_curve»
  weierstrass_neg := SessionEC.Weierstrass.«weierstrass_neg»
  weierstrass_nonsingular := SessionEC.Weierstrass.«weierstrass_nonsingular»

/-- What wei25519.ml uses from Session. -/
def deps : HolEC.Wei25519.Wei25519Deps where
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
  PRIME_RULE := SessionLibrary.Pocklington.PRIME_RULE
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
  NUM_SUB_CONV := Session.NUM_SUB_CONV
  NUM_DIV_CONV := Session.NUM_DIV_CONV
  EXP_MOD_CONV := Session.EXP_MOD_CONV
  EXPAND_CASES_CONV := Session.EXPAND_CASES_CONV
  DIVIDES_CONV := SessionLibrary.Prime.DIVIDES_CONV
  COPRIME_CONV := SessionLibrary.Prime.COPRIME_CONV
  NOT_RING_CHAR_DIVIDES_TAC := SessionEC.Misc.NOT_RING_CHAR_DIVIDES_TAC
  EXCLUDE_MODULAR_CUBIC_ROOTS_TAC := SessionEC.ExcludeRoots.EXCLUDE_MODULAR_CUBIC_ROOTS_TAC
  add_curve := SessionEC.ComputeGroup.add_curve
  add_curvezero := SessionEC.ComputeGroup.add_curvezero
  add_curveneg := SessionEC.ComputeGroup.add_curveneg
  add_curveadd := SessionEC.ComputeGroup.add_curveadd
  add_ecgroup := SessionEC.ComputeGroup.add_ecgroup
  ECGROUP_CARRIER_CONV := SessionEC.ComputeGroup.ECGROUP_CARRIER_CONV
  ECGROUP_ID_CONV := SessionEC.ComputeGroup.ECGROUP_ID_CONV
  ECGROUP_INV_CONV := SessionEC.ComputeGroup.ECGROUP_INV_CONV
  ECGROUP_MUL_CONV := SessionEC.ComputeGroup.ECGROUP_MUL_CONV
  ECGROUP_POW_CONV := SessionEC.ComputeGroup.ECGROUP_POW_CONV
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in wei25519.ml order. -/
initialize BWei25519Defs : HolEC.Wei25519.Wei25519Defs ←
  ioB "setupWei25519Defs" (HolEC.Wei25519.setupWei25519Defs deps).run
initialize BWei25519Group : HolEC.Wei25519.Wei25519Group ←
  ioB "setupWei25519Group" (HolEC.Wei25519.setupWei25519Group deps BWei25519Defs).run

-- Wei25519Defs
def p_25519 : thm := BWei25519Defs.p_25519
def n_25519 : thm := BWei25519Defs.n_25519
def a_25519 : thm := BWei25519Defs.a_25519
def b_25519 : thm := BWei25519Defs.b_25519
def G_25519 : thm := BWei25519Defs.G_25519
def GG_25519 : thm := BWei25519Defs.GG_25519
def P_25519 : thm := BWei25519Defs.P_25519
def N_25519 : thm := BWei25519Defs.N_25519
def PRIME_P25519 : thm := BWei25519Defs.PRIME_P25519
def PRIME_N25519 : thm := BWei25519Defs.PRIME_N25519
def wei25519_group : thm := BWei25519Defs.wei25519_group
def WEI25519_GROUP : thm := BWei25519Defs.WEI25519_GROUP

-- Wei25519Group
def FINITE_GROUP_CARRIER_WEI25519 : thm := BWei25519Group.FINITE_GROUP_CARRIER_WEI25519
def GENERATOR_IN_GROUP_CARRIER_WEI25519 : thm := BWei25519Group.GENERATOR_IN_GROUP_CARRIER_WEI25519
def GROUP_ELEMENT_ORDER_WEI25519_G25519 : thm := BWei25519Group.GROUP_ELEMENT_ORDER_WEI25519_G25519
def FULLGENERATOR_IN_GROUP_CARRIER_WEI25519 : thm := BWei25519Group.FULLGENERATOR_IN_GROUP_CARRIER_WEI25519
def GROUP_ELEMENT_ORDER_WEI25519_GG25519 : thm := BWei25519Group.GROUP_ELEMENT_ORDER_WEI25519_GG25519
def SIZE_WEI25519_GROUP : thm := BWei25519Group.SIZE_WEI25519_GROUP
def GENERATED_WEI25519_GROUP : thm := BWei25519Group.GENERATED_WEI25519_GROUP
def CYCLIC_WEI25519_GROUP : thm := BWei25519Group.CYCLIC_WEI25519_GROUP
def ABELIAN_WEI25519_GROUP : thm := BWei25519Group.ABELIAN_WEI25519_GROUP

/-- `needs "EC/wei25519.ml"`: already done by importing this module. -/
def ensureWei25519 : IO Unit := pure ()

end SessionEC.Wei25519
