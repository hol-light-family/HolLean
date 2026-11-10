/- ---------------------------------------------------------------------- -/
/- Session wiring for EC/montgomery.ml                                 . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionEC/Montgomery.lean

  The session half of the montgomery.ml translation: it supplies HolEC.Montgomery's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "EC/montgomery.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolEC.Montgomery
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

namespace SessionEC.Montgomery

/-- The core theorems montgomery.ml uses. -/
def core1 : HolEC.Montgomery.CoreThms1 where
  ASSOCIATIVITY_LEMMA := SessionEC.Misc.«ASSOCIATIVITY_LEMMA»
  CARD_SING := Session.CARD_SING
  CARD_SUBSET := Session.CARD_SUBSET
  COND_SWAP := Session.COND_SWAP
  CONJ_ASSOC := Session.CONJ_ASSOC
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  EVEN := Session.EVEN
  FIELD_CHAR_NOT2 := SessionEC.Misc.«FIELD_CHAR_NOT2»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FINITE_CARD_LE_IMAGE := Session.FINITE_CARD_LE_IMAGE
  FINITE_CARD_LE_UNION := Session.FINITE_CARD_LE_UNION
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_PRODUCT := Session.FINITE_PRODUCT
  FINITE_QUADRATIC_CURVE := SessionEC.Misc.«FINITE_QUADRATIC_CURVE»
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNION := Session.FINITE_UNION
  FORALL_AND_THM := Session.FORALL_AND_THM
  FORALL_OPTION_THM := Session.FORALL_OPTION_THM
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
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
  LE_TRANS := Session.LE_TRANS
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_IMP := Session.NOT_IMP
  PAIR_EQ := Session.PAIR_EQ
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_IMP_FORALL_THM := Session.RIGHT_IMP_FORALL_THM
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  SUBSET := Session.SUBSET
  UNWIND_THM1 := Session.UNWIND_THM1
  abelian_group := SessionLibrary.GroupTheory.«abelian_group»
  group_carrier := SessionLibrary.GroupTheory.«group_carrier»
  group_id := SessionLibrary.GroupTheory.«group_id»
  group_inv := SessionLibrary.GroupTheory.«group_inv»
  group_mul := SessionLibrary.GroupTheory.«group_mul»
  group_pow := SessionLibrary.GroupTheory.«group_pow»
  group_tybij := SessionLibrary.GroupTheory.«group_tybij»
  option_DISTINCT := Session.indTypesBoot.option_DISTINCT
  option_INJ := Session.indTypesBoot.option_INJ

/-- What montgomery.ml uses from Session. -/
def deps : HolEC.Montgomery.MontgomeryDeps where
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

/- The bundles, in montgomery.ml order. -/
initialize BMontgomeryDefs : HolEC.Montgomery.MontgomeryDefs ←
  ioB "setupMontgomeryDefs" (HolEC.Montgomery.setupMontgomeryDefs deps).run
initialize BMontgomeryGroup : HolEC.Montgomery.MontgomeryGroup ←
  ioB "setupMontgomeryGroup" (HolEC.Montgomery.setupMontgomeryGroup deps BMontgomeryDefs).run

-- MontgomeryDefs
def montgomery_point : thm := BMontgomeryDefs.montgomery_point
def montgomery_curve : thm := BMontgomeryDefs.montgomery_curve
def montgomery_nonsingular : thm := BMontgomeryDefs.montgomery_nonsingular
def montgomery_neg : thm := BMontgomeryDefs.montgomery_neg
def montgomery_add : thm := BMontgomeryDefs.montgomery_add
def montgomery_group : thm := BMontgomeryDefs.montgomery_group
def FINITE_MONTGOMERY_CURVE : thm := BMontgomeryDefs.FINITE_MONTGOMERY_CURVE
def CARD_BOUND_MONTGOMERY_CURVE : thm := BMontgomeryDefs.CARD_BOUND_MONTGOMERY_CURVE
def montgomery_strongly_nonsingular : thm := BMontgomeryDefs.montgomery_strongly_nonsingular
def MONTGOMERY_STRONGLY_NONSINGULAR : thm := BMontgomeryDefs.MONTGOMERY_STRONGLY_NONSINGULAR
def MONTGOMERY_STRONGLY_NONSINGULAR_IMP_NONSINGULAR : thm := BMontgomeryDefs.MONTGOMERY_STRONGLY_NONSINGULAR_IMP_NONSINGULAR

-- MontgomeryGroup
def MONTGOMERY_CURVE_IMP_POINT : thm := BMontgomeryGroup.MONTGOMERY_CURVE_IMP_POINT
def MONTGOMERY_POINT_NEG : thm := BMontgomeryGroup.MONTGOMERY_POINT_NEG
def MONTGOMERY_POINT_ADD : thm := BMontgomeryGroup.MONTGOMERY_POINT_ADD
def MONTGOMERY_CURVE_0 : thm := BMontgomeryGroup.MONTGOMERY_CURVE_0
def MONTGOMERY_CURVE_NEG : thm := BMontgomeryGroup.MONTGOMERY_CURVE_NEG
def MONTGOMERY_CURVE_ADD : thm := BMontgomeryGroup.MONTGOMERY_CURVE_ADD
def MONTGOMERY_ADD_LNEG : thm := BMontgomeryGroup.MONTGOMERY_ADD_LNEG
def MONTGOMERY_ADD_SYM : thm := BMontgomeryGroup.MONTGOMERY_ADD_SYM
def MONTGOMERY_ADD_ASSOC : thm := BMontgomeryGroup.MONTGOMERY_ADD_ASSOC
def MONTGOMERY_GROUP : thm := BMontgomeryGroup.MONTGOMERY_GROUP
def ABELIAN_MONTGOMERY_GROUP : thm := BMontgomeryGroup.ABELIAN_MONTGOMERY_GROUP
def GROUP_POW_MONTGOMERY_TORSION : thm := BMontgomeryGroup.GROUP_POW_MONTGOMERY_TORSION

/-- `needs "EC/montgomery.ml"`: already done by importing this module. -/
def ensureMontgomery : IO Unit := pure ()

end SessionEC.Montgomery
