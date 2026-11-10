/- ---------------------------------------------------------------------- -/
/- Session wiring for EC/weierstrass.ml                                . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionEC/Weierstrass.lean

  The session half of the weierstrass.ml translation: it supplies HolEC.Weierstrass's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "EC/weierstrass.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolEC.Weierstrass
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

namespace SessionEC.Weierstrass

/-- The core theorems weierstrass.ml uses. -/
def core1 : HolEC.Weierstrass.CoreThms1 where
  AND_FORALL_THM := Session.AND_FORALL_THM
  ASSOCIATIVITY_LEMMA := SessionEC.Misc.«ASSOCIATIVITY_LEMMA»
  CARD_SING := Session.CARD_SING
  CONJ_ASSOC := Session.CONJ_ASSOC
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  FIELD_CHAR_NOT2 := SessionEC.Misc.«FIELD_CHAR_NOT2»
  FIELD_CHAR_NOT23 := SessionEC.Misc.«FIELD_CHAR_NOT23»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FINITE_CARD_LE_IMAGE := Session.FINITE_CARD_LE_IMAGE
  FINITE_CARD_LE_SUBSET := Session.FINITE_CARD_LE_SUBSET
  FINITE_CARD_LE_UNION := Session.FINITE_CARD_LE_UNION
  FINITE_QUADRATIC_CURVE := SessionEC.Misc.«FINITE_QUADRATIC_CURVE»
  FINITE_SING := Session.FINITE_SING
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_OPTION_THM := Session.FORALL_OPTION_THM
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  GROUP_HOMOMORPHISM := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM»
  GROUP_ID := SessionLibrary.GroupTheory.«GROUP_ID»
  IMP_CONJ := Session.IMP_CONJ
  IMP_IMP := Session.IMP_IMP
  IN := Session.IN
  IN_CROSS := Session.IN_CROSS
  IN_ELIM_PAIR_THM := Session.IN_ELIM_PAIR_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_SING := Session.IN_SING
  IN_UNION := Session.IN_UNION
  LET_DEF := Session.LET_DEF
  LET_END_DEF := Session.LET_END_DEF
  LE_REFL := Session.LE_REFL
  PAIR_EQ := Session.PAIR_EQ
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_IMP_FORALL_THM := Session.RIGHT_IMP_FORALL_THM
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  SUBSET := Session.SUBSET
  UNWIND_THM1 := Session.UNWIND_THM1
  group_carrier := SessionLibrary.GroupTheory.«group_carrier»
  group_endomorphism := SessionLibrary.GroupTheory.«group_endomorphism»
  group_id := SessionLibrary.GroupTheory.«group_id»
  group_inv := SessionLibrary.GroupTheory.«group_inv»
  group_mul := SessionLibrary.GroupTheory.«group_mul»
  group_tybij := SessionLibrary.GroupTheory.«group_tybij»
  option_DISTINCT := Session.indTypesBoot.option_DISTINCT
  option_INJ := Session.indTypesBoot.option_INJ

/-- What weierstrass.ml uses from Session. -/
def deps : HolEC.Weierstrass.WeierstrassDeps where
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

/- The bundles, in weierstrass.ml order. -/
initialize BWeierstrassDefs : HolEC.Weierstrass.WeierstrassDefs ←
  ioB "setupWeierstrassDefs" (HolEC.Weierstrass.setupWeierstrassDefs deps).run
initialize BWeierstrassGroup : HolEC.Weierstrass.WeierstrassGroup ←
  ioB "setupWeierstrassGroup" (HolEC.Weierstrass.setupWeierstrassGroup deps BWeierstrassDefs).run
initialize BWeierstrassEndo : HolEC.Weierstrass.WeierstrassEndo ←
  ioB "setupWeierstrassEndo" (HolEC.Weierstrass.setupWeierstrassEndo deps BWeierstrassDefs BWeierstrassGroup).run

-- WeierstrassDefs
def weierstrass_point : thm := BWeierstrassDefs.weierstrass_point
def weierstrass_curve : thm := BWeierstrassDefs.weierstrass_curve
def weierstrass_neg : thm := BWeierstrassDefs.weierstrass_neg
def weierstrass_add : thm := BWeierstrassDefs.weierstrass_add
def weierstrass_nonsingular : thm := BWeierstrassDefs.weierstrass_nonsingular
def weierstrass_group : thm := BWeierstrassDefs.weierstrass_group
def FINITE_WEIERSTRASS_CURVE : thm := BWeierstrassDefs.FINITE_WEIERSTRASS_CURVE
def CARD_BOUND_WEIERSTRASS_CURVE : thm := BWeierstrassDefs.CARD_BOUND_WEIERSTRASS_CURVE

-- WeierstrassGroup
def WEIERSTRASS_CURVE_IMP_POINT : thm := BWeierstrassGroup.WEIERSTRASS_CURVE_IMP_POINT
def WEIERSTRASS_POINT_NEG : thm := BWeierstrassGroup.WEIERSTRASS_POINT_NEG
def WEIERSTRASS_POINT_ADD : thm := BWeierstrassGroup.WEIERSTRASS_POINT_ADD
def WEIERSTRASS_CURVE_0 : thm := BWeierstrassGroup.WEIERSTRASS_CURVE_0
def WEIERSTRASS_CURVE_NEG : thm := BWeierstrassGroup.WEIERSTRASS_CURVE_NEG
def WEIERSTRASS_CURVE_ADD : thm := BWeierstrassGroup.WEIERSTRASS_CURVE_ADD
def WEIERSTRASS_ADD_LNEG : thm := BWeierstrassGroup.WEIERSTRASS_ADD_LNEG
def WEIERSTRASS_ADD_SYM : thm := BWeierstrassGroup.WEIERSTRASS_ADD_SYM
def WEIERSTRASS_ADD_ASSOC : thm := BWeierstrassGroup.WEIERSTRASS_ADD_ASSOC
def WEIERSTRASS_GROUP : thm := BWeierstrassGroup.WEIERSTRASS_GROUP

-- WeierstrassEndo
def weierstrass_triplex : thm := BWeierstrassEndo.weierstrass_triplex
def GROUP_ENDOMORPHISM_TRIPLEX : thm := BWeierstrassEndo.GROUP_ENDOMORPHISM_TRIPLEX
def weierstrass_quady : thm := BWeierstrassEndo.weierstrass_quady
def GROUP_ENDOMORPHISM_QUADY : thm := BWeierstrassEndo.GROUP_ENDOMORPHISM_QUADY

/-- `needs "EC/weierstrass.ml"`: already done by importing this module. -/
def ensureWeierstrass : IO Unit := pure ()

end SessionEC.Weierstrass
