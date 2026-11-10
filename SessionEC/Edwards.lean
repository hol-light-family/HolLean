/- ---------------------------------------------------------------------- -/
/- Session wiring for EC/edwards.ml                                    . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionEC/Edwards.lean

  The session half of the edwards.ml translation: it supplies HolEC.Edwards's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "EC/edwards.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolEC.Edwards
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionEC.Edwards

/-- The core theorems edwards.ml uses. -/
def core1 : HolEC.Edwards.CoreThms1 where
  ARITH_EQ := Session.ARITH_EQ
  ARITH_EVEN := Session.ARITH_EVEN
  CARD_SUBSET := Session.CARD_SUBSET
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIVIDES_2 := SessionLibrary.Prime.«DIVIDES_2»
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  FIELD_CHAR_NOT2 := SessionEC.Misc.«FIELD_CHAR_NOT2»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FINITE_PRODUCT := Session.FINITE_PRODUCT
  FINITE_QUADRATIC_CURVE := SessionEC.Misc.«FINITE_QUADRATIC_CURVE»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FORALL_UNPAIR_THM := Session.FORALL_UNPAIR_THM
  GROUP_ELEMENT_ORDER_EQ_2_ALT := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_EQ_2_ALT»
  GROUP_ELEMENT_ORDER_EQ_MUL := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_EQ_MUL»
  GROUP_POW := SessionLibrary.GroupTheory.«GROUP_POW»
  GROUP_POW_2 := SessionLibrary.GroupTheory.«GROUP_POW_2»
  IMP_CONJ := Session.IMP_CONJ
  IN := Session.IN
  IN_ELIM_PAIR_THM := Session.IN_ELIM_PAIR_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LET_DEF := Session.LET_DEF
  LET_END_DEF := Session.LET_END_DEF
  LE_TRANS := Session.LE_TRANS
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  PAIR := Session.PAIR
  PAIR_EQ := Session.PAIR_EQ
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_OR_FORALL_THM := Session.RIGHT_OR_FORALL_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  SUBSET := Session.SUBSET
  abelian_group := SessionLibrary.GroupTheory.«abelian_group»
  group_carrier := SessionLibrary.GroupTheory.«group_carrier»
  group_id := SessionLibrary.GroupTheory.«group_id»
  group_inv := SessionLibrary.GroupTheory.«group_inv»
  group_mul := SessionLibrary.GroupTheory.«group_mul»
  group_tybij := SessionLibrary.GroupTheory.«group_tybij»

/-- What edwards.ml uses from Session. -/
def deps : HolEC.Edwards.EdwardsDeps where
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

/- The bundles, in edwards.ml order. -/
initialize BEdwardsDefs : HolEC.Edwards.EdwardsDefs ←
  ioB "setupEdwardsDefs" (HolEC.Edwards.setupEdwardsDefs deps).run
initialize BEdwardsGroup : HolEC.Edwards.EdwardsGroup ←
  ioB "setupEdwardsGroup" (HolEC.Edwards.setupEdwardsGroup deps BEdwardsDefs).run
initialize BEdwardsOrders : HolEC.Edwards.EdwardsOrders ←
  ioB "setupEdwardsOrders" (HolEC.Edwards.setupEdwardsOrders deps BEdwardsDefs BEdwardsGroup).run

-- EdwardsDefs
def edwards_point : thm := BEdwardsDefs.edwards_point
def edwards_curve : thm := BEdwardsDefs.edwards_curve
def edwards_nonsingular : thm := BEdwardsDefs.edwards_nonsingular
def edwards_0 : thm := BEdwardsDefs.edwards_0
def edwards_neg : thm := BEdwardsDefs.edwards_neg
def edwards_add : thm := BEdwardsDefs.edwards_add
def edwards_group : thm := BEdwardsDefs.edwards_group
def EDWARDS_NONSINGULAR_ALT : thm := BEdwardsDefs.EDWARDS_NONSINGULAR_ALT
def FINITE_EDWARDS_CURVE : thm := BEdwardsDefs.FINITE_EDWARDS_CURVE
def CARD_BOUND_EDWARDS_CURVE : thm := BEdwardsDefs.CARD_BOUND_EDWARDS_CURVE

-- EdwardsGroup
def EDWARDS_NONSINGULAR_DENOMINATORS : thm := BEdwardsGroup.EDWARDS_NONSINGULAR_DENOMINATORS
def EDWARDS_NONSINGULAR_DENOMINATORS_POINTS : thm := BEdwardsGroup.EDWARDS_NONSINGULAR_DENOMINATORS_POINTS
def EDWARDS_CURVE_IMP_POINT : thm := BEdwardsGroup.EDWARDS_CURVE_IMP_POINT
def EDWARDS_POINT_NEG : thm := BEdwardsGroup.EDWARDS_POINT_NEG
def EDWARDS_POINT_ADD : thm := BEdwardsGroup.EDWARDS_POINT_ADD
def EDWARDS_CURVE_0 : thm := BEdwardsGroup.EDWARDS_CURVE_0
def EDWARDS_CURVE_NEG : thm := BEdwardsGroup.EDWARDS_CURVE_NEG
def EDWARDS_CURVE_ADD : thm := BEdwardsGroup.EDWARDS_CURVE_ADD
def EDWARDS_ADD_LID : thm := BEdwardsGroup.EDWARDS_ADD_LID
def EDWARDS_ADD_LNEG : thm := BEdwardsGroup.EDWARDS_ADD_LNEG
def EDWARDS_ADD_SYM : thm := BEdwardsGroup.EDWARDS_ADD_SYM
def EDWARDS_ADD_ASSOC : thm := BEdwardsGroup.EDWARDS_ADD_ASSOC
def EDWARDS_GROUP : thm := BEdwardsGroup.EDWARDS_GROUP
def ABELIAN_EDWARDS_GROUP : thm := BEdwardsGroup.ABELIAN_EDWARDS_GROUP

-- EdwardsOrders
def EDWARDS_GROUP_ELEMENT_ORDER_EQ_2 : thm := BEdwardsOrders.EDWARDS_GROUP_ELEMENT_ORDER_EQ_2
def EDWARDS_GROUP_ELEMENT_ORDER_EQ_4_EQUIV : thm := BEdwardsOrders.EDWARDS_GROUP_ELEMENT_ORDER_EQ_4_EQUIV
def EDWARDS_GROUP_ELEMENT_ORDER_EQ_4 : thm := BEdwardsOrders.EDWARDS_GROUP_ELEMENT_ORDER_EQ_4
def EDWARDS_GROUP_ELEMENT_ORDER_EQ_8_EQUIV : thm := BEdwardsOrders.EDWARDS_GROUP_ELEMENT_ORDER_EQ_8_EQUIV

/-- `needs "EC/edwards.ml"`: already done by importing this module. -/
def ensureEdwards : IO Unit := pure ()

end SessionEC.Edwards
