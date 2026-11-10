/- ---------------------------------------------------------------------- -/
/- Session wiring for EC/projective.ml                                 . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionEC/Projective.lean

  The session half of the projective.ml translation: it supplies HolEC.Projective's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "EC/projective.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolEC.Projective
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

namespace SessionEC.Projective

/-- The core theorems projective.ml uses. -/
def core1 : HolEC.Projective.CoreThms1 where
  CONJ_ASSOC := Session.CONJ_ASSOC
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  FIELD_CHAR_NOT23 := SessionEC.Misc.«FIELD_CHAR_NOT23»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_MUL_LINV := SessionLibrary.RingTheory.«FIELD_MUL_LINV»
  FORALL_OPTION_THM := Session.FORALL_OPTION_THM
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  LET_DEF := Session.LET_DEF
  LET_END_DEF := Session.LET_END_DEF
  PAIR_EQ := Session.PAIR_EQ
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_DIV := SessionLibrary.RingTheory.«RING_DIV»
  RING_DIV_1 := SessionLibrary.RingTheory.«RING_DIV_1»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
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

/-- What projective.ml uses from Session. -/
def deps : HolEC.Projective.ProjectiveDeps where
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

/- The bundles, in projective.ml order. -/
initialize BProjectiveDefs : HolEC.Projective.ProjectiveDefs ←
  ioB "setupProjectiveDefs" (HolEC.Projective.setupProjectiveDefs deps).run
initialize BProjectiveOps : HolEC.Projective.ProjectiveOps ←
  ioB "setupProjectiveOps" (HolEC.Projective.setupProjectiveOps deps BProjectiveDefs).run

-- ProjectiveDefs
def projective_point : thm := BProjectiveDefs.projective_point
def projective_curve : thm := BProjectiveDefs.projective_curve
def weierstrass_of_projective : thm := BProjectiveDefs.weierstrass_of_projective
def projective_of_weierstrass : thm := BProjectiveDefs.projective_of_weierstrass
def projective_eq : thm := BProjectiveDefs.projective_eq
def projective_0 : thm := BProjectiveDefs.projective_0
def projective_neg : thm := BProjectiveDefs.projective_neg
def projective_add : thm := BProjectiveDefs.projective_add
def PROJECTIVE_CURVE_IMP_POINT : thm := BProjectiveDefs.PROJECTIVE_CURVE_IMP_POINT
def PROJECTIVE_OF_WEIERSTRASS_POINT_EQ : thm := BProjectiveDefs.PROJECTIVE_OF_WEIERSTRASS_POINT_EQ
def PROJECTIVE_OF_WEIERSTRASS_POINT : thm := BProjectiveDefs.PROJECTIVE_OF_WEIERSTRASS_POINT
def WEIERSTRASS_OF_PROJECTIVE_POINT : thm := BProjectiveDefs.WEIERSTRASS_OF_PROJECTIVE_POINT
def PROJECTIVE_OF_WEIERSTRASS_EQ : thm := BProjectiveDefs.PROJECTIVE_OF_WEIERSTRASS_EQ
def WEIERSTRASS_OF_PROJECTIVE_EQ : thm := BProjectiveDefs.WEIERSTRASS_OF_PROJECTIVE_EQ
def WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS : thm := BProjectiveDefs.WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS
def PROJECTIVE_OF_WEIERSTRASS_OF_PROJECTIVE : thm := BProjectiveDefs.PROJECTIVE_OF_WEIERSTRASS_OF_PROJECTIVE
def PROJECTIVE_OF_WEIERSTRASS_CURVE_EQ : thm := BProjectiveDefs.PROJECTIVE_OF_WEIERSTRASS_CURVE_EQ
def PROJECTIVE_OF_WEIERSTRASS_CURVE : thm := BProjectiveDefs.PROJECTIVE_OF_WEIERSTRASS_CURVE
def WEIERSTRASS_OF_PROJECTIVE_CURVE : thm := BProjectiveDefs.WEIERSTRASS_OF_PROJECTIVE_CURVE

-- ProjectiveOps
def PROJECTIVE_POINT_NEG : thm := BProjectiveOps.PROJECTIVE_POINT_NEG
def PROJECTIVE_CURVE_NEG : thm := BProjectiveOps.PROJECTIVE_CURVE_NEG
def WEIERSTRASS_OF_PROJECTIVE_NEG : thm := BProjectiveOps.WEIERSTRASS_OF_PROJECTIVE_NEG
def PROJECTIVE_EQ_NEG : thm := BProjectiveOps.PROJECTIVE_EQ_NEG
def WEIERSTRASS_OF_PROJECTIVE_NEG_OF_WEIERSTRASS : thm := BProjectiveOps.WEIERSTRASS_OF_PROJECTIVE_NEG_OF_WEIERSTRASS
def PROJECTIVE_OF_WEIERSTRASS_NEG : thm := BProjectiveOps.PROJECTIVE_OF_WEIERSTRASS_NEG
def PROJECTIVE_POINT_ADD : thm := BProjectiveOps.PROJECTIVE_POINT_ADD
def PROJECTIVE_CURVE_ADD : thm := BProjectiveOps.PROJECTIVE_CURVE_ADD
def WEIERSTRASS_OF_PROJECTIVE_ADD : thm := BProjectiveOps.WEIERSTRASS_OF_PROJECTIVE_ADD
def PROJECTIVE_EQ_ADD : thm := BProjectiveOps.PROJECTIVE_EQ_ADD
def WEIERSTRASS_OF_PROJECTIVE_ADD_OF_WEIERSTRASS : thm := BProjectiveOps.WEIERSTRASS_OF_PROJECTIVE_ADD_OF_WEIERSTRASS
def PROJECTIVE_OF_WEIERSTRASS_ADD : thm := BProjectiveOps.PROJECTIVE_OF_WEIERSTRASS_ADD

/-- `needs "EC/projective.ml"`: already done by importing this module. -/
def ensureProjective : IO Unit := pure ()

end SessionEC.Projective
