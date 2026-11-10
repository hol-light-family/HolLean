/- ---------------------------------------------------------------------- -/
/- Session wiring for EC/family25519.ml                                . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionEC/Family25519.lean

  The session half of the family25519.ml translation: it supplies HolEC.Family25519's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "EC/family25519.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolEC.Family25519
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
import SessionEC.Edwards
import SessionEC.Montgomery
import SessionEC.Edmont
import SessionEC.Weierstrass
import SessionEC.Montwe
import SessionEC.ExcludeRoots
import SessionEC.ComputeGroup
import SessionEC.Edwards25519
import SessionEC.Curve25519
import SessionEC.Wei25519

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionEC.Family25519

/-- The core theorems family25519.ml uses. -/
def core1 : HolEC.Family25519.CoreThms1 where
  A_25519 := SessionEC.Curve25519.«A_25519»
  CC_25519 := SessionEC.Curve25519.«CC_25519»
  C_25519 := SessionEC.Curve25519.«C_25519»
  EDWARDS_NONSINGULAR_25519 := SessionEC.Edwards25519.«EDWARDS_NONSINGULAR_25519»
  EE_25519 := SessionEC.Edwards25519.«EE_25519»
  E_25519 := SessionEC.Edwards25519.«E_25519»
  FIELD_INTEGER_MOD_RING := SessionLibrary.RingTheory.«FIELD_INTEGER_MOD_RING»
  GG_25519 := SessionEC.Wei25519.«GG_25519»
  GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP := SessionEC.Edmont.«GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP»
  GROUP_ISOMORPHISMS_IMP_ISOMORPHISM := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISMS_IMP_ISOMORPHISM»
  GROUP_ISOMORPHISMS_MONTGOMERY_WEIERSTRASS_GROUP := SessionEC.Montwe.«GROUP_ISOMORPHISMS_MONTGOMERY_WEIERSTRASS_GROUP»
  G_25519 := SessionEC.Wei25519.«G_25519»
  INTEGER_MOD_RING := SessionLibrary.RingTheory.«INTEGER_MOD_RING»
  INTEGER_MOD_RING_CHAR := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CHAR»
  INTEGER_MOD_RING_CLAUSES := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CLAUSES»
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  IN_INTEGER_MOD_RING_CARRIER := SessionLibrary.RingTheory.«IN_INTEGER_MOD_RING_CARRIER»
  ISOMORPHIC_GROUP_SYM := SessionLibrary.GroupTheory.«ISOMORPHIC_GROUP_SYM»
  PAIR_EQ := Session.PAIR_EQ
  PRIME_P25519 := SessionEC.Wei25519.«PRIME_P25519»
  a_25519 := SessionEC.Wei25519.«a_25519»
  b_25519 := SessionEC.Wei25519.«b_25519»
  curve25519_group := SessionEC.Curve25519.«curve25519_group»
  d_25519 := SessionEC.Edwards25519.«d_25519»
  e_25519 := SessionEC.Edwards25519.«e_25519»
  edwards25519_group := SessionEC.Edwards25519.«edwards25519_group»
  edwards_of_montgomery := SessionEC.Edmont.«edwards_of_montgomery»
  isomorphic_group := SessionLibrary.GroupTheory.«isomorphic_group»
  mcurve_of_ecurve := SessionEC.Edmont.«mcurve_of_ecurve»
  montgomery_nonsingular := SessionEC.Montgomery.«montgomery_nonsingular»
  montgomery_of_edwards := SessionEC.Edmont.«montgomery_of_edwards»
  montgomery_of_weierstrass := SessionEC.Montwe.«montgomery_of_weierstrass»
  p_25519 := SessionEC.Wei25519.«p_25519»
  wcurve_of_mcurve := SessionEC.Montwe.«wcurve_of_mcurve»
  wei25519_group := SessionEC.Wei25519.«wei25519_group»
  weierstrass_of_montgomery := SessionEC.Montwe.«weierstrass_of_montgomery»

/-- What family25519.ml uses from Session. -/
def deps : HolEC.Family25519.Family25519Deps where
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

/- The bundles, in family25519.ml order. -/
initialize BFamily25519Maps : HolEC.Family25519.Family25519Maps ←
  ioB "setupFamily25519Maps" (HolEC.Family25519.setupFamily25519Maps deps).run

-- Family25519Maps
def c_25519 : thm := BFamily25519Maps.c_25519
def curve25519_of_edwards25519 : thm := BFamily25519Maps.curve25519_of_edwards25519
def edwards25519_of_curve25519 : thm := BFamily25519Maps.edwards25519_of_curve25519
def MCURVE_OF_ECURVE_25519 : thm := BFamily25519Maps.MCURVE_OF_ECURVE_25519
def GROUP_ISOMORPHISMS_EDWARDS25519_CURVE25519 : thm := BFamily25519Maps.GROUP_ISOMORPHISMS_EDWARDS25519_CURVE25519
def ISOMORPHIC_GROUPS_EDWARDS25519_CURVE25519 : thm := BFamily25519Maps.ISOMORPHIC_GROUPS_EDWARDS25519_CURVE25519
def ISOMORPHIC_GROUPS_CURVE25519_EDWARDS25519 : thm := BFamily25519Maps.ISOMORPHIC_GROUPS_CURVE25519_EDWARDS25519
def CURVE25519_OF_EDWARDS25519_E25519 : thm := BFamily25519Maps.CURVE25519_OF_EDWARDS25519_E25519
def CURVE25519_OF_EDWARDS25519_EE25519 : thm := BFamily25519Maps.CURVE25519_OF_EDWARDS25519_EE25519
def EDWARDS25519_OF_CURVE25519_C25519 : thm := BFamily25519Maps.EDWARDS25519_OF_CURVE25519_C25519
def EDWARDS25519_OF_CURVE25519_CC25519 : thm := BFamily25519Maps.EDWARDS25519_OF_CURVE25519_CC25519
def wei25519_of_curve25519 : thm := BFamily25519Maps.wei25519_of_curve25519
def curve25519_of_wei25519 : thm := BFamily25519Maps.curve25519_of_wei25519
def WCURVE_OF_MCURVE_25519 : thm := BFamily25519Maps.WCURVE_OF_MCURVE_25519
def GROUP_ISOMORPHISMS_CURVE25519_WEI25519 : thm := BFamily25519Maps.GROUP_ISOMORPHISMS_CURVE25519_WEI25519
def ISOMORPHIC_GROUPS_CURVE25519_WEI25519 : thm := BFamily25519Maps.ISOMORPHIC_GROUPS_CURVE25519_WEI25519
def ISOMORPHIC_GROUPS_WEI25519_CURVE25519 : thm := BFamily25519Maps.ISOMORPHIC_GROUPS_WEI25519_CURVE25519
def WEI25519_OF_CURVE25519_C25519 : thm := BFamily25519Maps.WEI25519_OF_CURVE25519_C25519
def WEI25519_OF_CURVE25519_CC25519 : thm := BFamily25519Maps.WEI25519_OF_CURVE25519_CC25519
def CURVE25519_OF_WEI25519_G25519 : thm := BFamily25519Maps.CURVE25519_OF_WEI25519_G25519
def CURVE25519_OF_WEI25519_GG25519 : thm := BFamily25519Maps.CURVE25519_OF_WEI25519_GG25519

/-- `needs "EC/family25519.ml"`: already done by importing this module. -/
def ensureFamily25519 : IO Unit := pure ()

end SessionEC.Family25519
