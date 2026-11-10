/- ---------------------------------------------------------------------- -/
/- Session wiring for EC/montwe.ml                                     . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionEC/Montwe.lean

  The session half of the montwe.ml translation: it supplies HolEC.Montwe's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "EC/montwe.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolEC.Montwe
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
import SessionEC.Weierstrass

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionEC.Montwe

/-- The core theorems montwe.ml uses. -/
def core1 : HolEC.Montwe.CoreThms1 where
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  FIELD_CHAR_NOT23 := SessionEC.Misc.«FIELD_CHAR_NOT23»
  FIELD_CHAR_NOT3 := SessionEC.Misc.«FIELD_CHAR_NOT3»
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_OPTION_THM := Session.FORALL_OPTION_THM
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  GROUP_HOMOMORPHISM := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM»
  GROUP_ISOMORPHISMS := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISMS»
  GROUP_ISOMORPHISMS_IMP_ISOMORPHISM := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISMS_IMP_ISOMORPHISM»
  GROUP_ISOMORPHISMS_SYM := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISMS_SYM»
  IN := Session.IN
  ISOMORPHIC_GROUP_SYM := SessionLibrary.GroupTheory.«ISOMORPHIC_GROUP_SYM»
  MONTGOMERY_GROUP := SessionEC.Montgomery.«MONTGOMERY_GROUP»
  PAIR_EQ := Session.PAIR_EQ
  SUBSET := Session.SUBSET
  WEIERSTRASS_GROUP := SessionEC.Weierstrass.«WEIERSTRASS_GROUP»
  isomorphic_group := SessionLibrary.GroupTheory.«isomorphic_group»
  montgomery_add := SessionEC.Montgomery.«montgomery_add»
  montgomery_curve := SessionEC.Montgomery.«montgomery_curve»
  montgomery_neg := SessionEC.Montgomery.«montgomery_neg»
  montgomery_nonsingular := SessionEC.Montgomery.«montgomery_nonsingular»
  montgomery_point := SessionEC.Montgomery.«montgomery_point»
  option_DISTINCT := Session.indTypesBoot.option_DISTINCT
  option_INJ := Session.indTypesBoot.option_INJ
  weierstrass_add := SessionEC.Weierstrass.«weierstrass_add»
  weierstrass_curve := SessionEC.Weierstrass.«weierstrass_curve»
  weierstrass_neg := SessionEC.Weierstrass.«weierstrass_neg»
  weierstrass_nonsingular := SessionEC.Weierstrass.«weierstrass_nonsingular»
  weierstrass_point := SessionEC.Weierstrass.«weierstrass_point»

/-- What montwe.ml uses from Session. -/
def deps : HolEC.Montwe.MontweDeps where
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

/- The bundles, in montwe.ml order. -/
initialize BMontweMaps : HolEC.Montwe.MontweMaps ←
  ioB "setupMontweMaps" (HolEC.Montwe.setupMontweMaps deps).run
initialize BMontweIso : HolEC.Montwe.MontweIso ←
  ioB "setupMontweIso" (HolEC.Montwe.setupMontweIso deps BMontweMaps).run

-- MontweMaps
def wcurve_of_mcurve : thm := BMontweMaps.wcurve_of_mcurve
def WCURVE_OF_MCURVE_NONSINGULAR_EQ : thm := BMontweMaps.WCURVE_OF_MCURVE_NONSINGULAR_EQ
def WCURVE_OF_MCURVE_NONSINGULAR : thm := BMontweMaps.WCURVE_OF_MCURVE_NONSINGULAR
def weierstrass_of_montgomery : thm := BMontweMaps.weierstrass_of_montgomery
def montgomery_of_weierstrass : thm := BMontweMaps.montgomery_of_weierstrass
def MONTGOMERY_OF_WEIERSTRASS_OF_MONTGOMERY : thm := BMontweMaps.MONTGOMERY_OF_WEIERSTRASS_OF_MONTGOMERY
def WEIERSTRASS_OF_MONTGOMERY_OF_WEIERSTRASS : thm := BMontweMaps.WEIERSTRASS_OF_MONTGOMERY_OF_WEIERSTRASS
def WEIERSTRASS_OF_MONTGOMERY : thm := BMontweMaps.WEIERSTRASS_OF_MONTGOMERY
def MONTGOMERY_OF_WEIERSTRASS : thm := BMontweMaps.MONTGOMERY_OF_WEIERSTRASS

-- MontweIso
def WEIERSTRASS_OF_MONTGOMERY_NEG : thm := BMontweIso.WEIERSTRASS_OF_MONTGOMERY_NEG
def WEIERSTRASS_OF_MONTGOMERY_ADD : thm := BMontweIso.WEIERSTRASS_OF_MONTGOMERY_ADD
def GROUP_ISOMORPHISMS_MONTGOMERY_WEIERSTRASS_GROUP : thm := BMontweIso.GROUP_ISOMORPHISMS_MONTGOMERY_WEIERSTRASS_GROUP
def GROUP_ISOMORPHISMS_WEIERSTRASS_MONTGOMERY_GROUP : thm := BMontweIso.GROUP_ISOMORPHISMS_WEIERSTRASS_MONTGOMERY_GROUP
def ISOMORPHIC_MONTGOMERY_WEIERSTRASS_GROUP : thm := BMontweIso.ISOMORPHIC_MONTGOMERY_WEIERSTRASS_GROUP
def ISOMORPHIC_WEIERSTRASS_MONTGOMERY_GROUP : thm := BMontweIso.ISOMORPHIC_WEIERSTRASS_MONTGOMERY_GROUP

/-- `needs "EC/montwe.ml"`: already done by importing this module. -/
def ensureMontwe : IO Unit := pure ()

end SessionEC.Montwe
