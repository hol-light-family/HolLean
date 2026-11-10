/- ---------------------------------------------------------------------- -/
/- Session wiring for EC/secp224k1.ml                                  . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionEC/Secp224k1.lean

  The session half of the secp224k1.ml translation: it supplies HolEC.Secp224k1's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "EC/secp224k1.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolEC.Secp224k1
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

namespace SessionEC.Secp224k1

/-- The core theorems secp224k1.ml uses. -/
def core1 : HolEC.Secp224k1.CoreThms1 where
  ARITH := Session.ARITH
  CARD_BOUND_WEIERSTRASS_CURVE := SessionEC.Weierstrass.«CARD_BOUND_WEIERSTRASS_CURVE»
  CARD_INTEGER_MOD_RING := SessionLibrary.RingTheory.«CARD_INTEGER_MOD_RING»
  COPRIME_2 := SessionLibrary.Prime.«COPRIME_2»
  CYCLIC_GROUP_ALT := SessionLibrary.GroupTheory.«CYCLIC_GROUP_ALT»
  CYCLIC_IMP_ABELIAN_GROUP := SessionLibrary.GroupTheory.«CYCLIC_IMP_ABELIAN_GROUP»
  FIELD_INTEGER_MOD_RING := SessionLibrary.RingTheory.«FIELD_INTEGER_MOD_RING»
  FINITE_INTEGER_MOD_RING := SessionLibrary.RingTheory.«FINITE_INTEGER_MOD_RING»
  FINITE_WEIERSTRASS_CURVE := SessionEC.Weierstrass.«FINITE_WEIERSTRASS_CURVE»
  FORALL_OPTION_THM := Session.FORALL_OPTION_THM
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  GROUP_ADHOC_ORDER_UNIQUE_LEMMA := SessionEC.Misc.«GROUP_ADHOC_ORDER_UNIQUE_LEMMA»
  GROUP_ELEMENT_ORDER_PRIME := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_PRIME»
  GROUP_ELEMENT_ORDER_UNIQUE_PRIME := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_UNIQUE_PRIME»
  HAS_SIZE := Session.HAS_SIZE
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  IN := Session.IN
  INTEGER_MOD_RING_CHAR := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CHAR»
  INTEGER_MOD_RING_CLAUSES := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CLAUSES»
  INT_ADD_LID := Session.INT_ADD_LID
  INT_DIVIDES_LE := SessionLibrary.Integer.«INT_DIVIDES_LE»
  INT_MUL_LZERO := Session.INT_MUL_LZERO
  INT_REM_EQ := Session.INT_REM_EQ
  INT_REM_LT := Session.INT_REM_LT
  INT_REM_ZERO := Session.INT_REM_ZERO
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_INTEGER_MOD_RING_CARRIER := SessionLibrary.RingTheory.«IN_INTEGER_MOD_RING_CARRIER»
  LET_TRANS := Session.LET_TRANS
  PAIR_EQ := Session.PAIR_EQ
  SUBGROUP_GENERATED_ELEMENT_ORDER := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_ELEMENT_ORDER»
  WEIERSTRASS_GROUP := SessionEC.Weierstrass.«WEIERSTRASS_GROUP»
  num_coprime := Session.num_coprime
  option_DISTINCT := Session.indTypesBoot.option_DISTINCT
  option_INJ := Session.indTypesBoot.option_INJ
  weierstrass_add := SessionEC.Weierstrass.«weierstrass_add»
  weierstrass_curve := SessionEC.Weierstrass.«weierstrass_curve»
  weierstrass_neg := SessionEC.Weierstrass.«weierstrass_neg»
  weierstrass_nonsingular := SessionEC.Weierstrass.«weierstrass_nonsingular»

/-- What secp224k1.ml uses from Session. -/
def deps : HolEC.Secp224k1.Secp224k1Deps where
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

/- The bundles, in secp224k1.ml order. -/
initialize BSecp224k1Defs : HolEC.Secp224k1.Secp224k1Defs ←
  ioB "setupSecp224k1Defs" (HolEC.Secp224k1.setupSecp224k1Defs deps).run
initialize BSecp224k1Group : HolEC.Secp224k1.Secp224k1Group ←
  ioB "setupSecp224k1Group" (HolEC.Secp224k1.setupSecp224k1Group deps BSecp224k1Defs).run

-- Secp224k1Defs
def p_224k1 : thm := BSecp224k1Defs.p_224k1
def n_224k1 : thm := BSecp224k1Defs.n_224k1
def G_224K1 : thm := BSecp224k1Defs.G_224K1
def P_224K1 : thm := BSecp224k1Defs.P_224K1
def P_224K1_ALT : thm := BSecp224k1Defs.P_224K1_ALT
def PRIME_P224K1 : thm := BSecp224k1Defs.PRIME_P224K1
def PRIME_N224K1 : thm := BSecp224k1Defs.PRIME_N224K1
def p224k1_group : thm := BSecp224k1Defs.p224k1_group
def P224K1_GROUP : thm := BSecp224k1Defs.P224K1_GROUP

-- Secp224k1Group
def NO_ROOTS_224K1 : thm := BSecp224k1Group.NO_ROOTS_224K1
def GENERATOR_IN_GROUP_CARRIER_224K1 : thm := BSecp224k1Group.GENERATOR_IN_GROUP_CARRIER_224K1
def GROUP_ELEMENT_ORDER_G224K1 : thm := BSecp224k1Group.GROUP_ELEMENT_ORDER_G224K1
def FINITE_GROUP_CARRIER_P224K1 : thm := BSecp224k1Group.FINITE_GROUP_CARRIER_P224K1
def SIZE_P224K1_GROUP : thm := BSecp224k1Group.SIZE_P224K1_GROUP
def P224K1_GROUP_ORDER : thm := BSecp224k1Group.P224K1_GROUP_ORDER
def P224K1_GROUP_ELEMENT_ORDER : thm := BSecp224k1Group.P224K1_GROUP_ELEMENT_ORDER
def GENERATED_P224K1_GROUP : thm := BSecp224k1Group.GENERATED_P224K1_GROUP
def CYCLIC_P224K1_GROUP : thm := BSecp224k1Group.CYCLIC_P224K1_GROUP
def ABELIAN_P224K1_GROUP : thm := BSecp224k1Group.ABELIAN_P224K1_GROUP

/-- `needs "EC/secp224k1.ml"`: already done by importing this module. -/
def ensureSecp224k1 : IO Unit := pure ()

end SessionEC.Secp224k1
