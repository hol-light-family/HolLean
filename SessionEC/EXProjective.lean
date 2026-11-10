/- ---------------------------------------------------------------------- -/
/- Session wiring for EC/exprojective.ml                               . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionEC/EXProjective.lean

  The session half of the exprojective.ml translation: it supplies HolEC.EXProjective's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "EC/exprojective.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolEC.EXProjective
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionEC.EXProjective

/-- The core theorems exprojective.ml uses. -/
def core1 : HolEC.EXProjective.CoreThms1 where
  EDWARDS_NONSINGULAR_DENOMINATORS := SessionEC.Edwards.«EDWARDS_NONSINGULAR_DENOMINATORS»
  FIELD_CHAR_NOT2 := SessionEC.Misc.«FIELD_CHAR_NOT2»
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  IMP_CONJ := Session.IMP_CONJ
  LET_DEF := Session.LET_DEF
  LET_END_DEF := Session.LET_END_DEF
  PAIR_EQ := Session.PAIR_EQ
  edwards_add := SessionEC.Edwards.«edwards_add»
  edwards_curve := SessionEC.Edwards.«edwards_curve»

/-- What exprojective.ml uses from Session. -/
def deps : HolEC.EXProjective.EXProjectiveDeps where
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

/- The bundles, in exprojective.ml order. -/
initialize BEXProjectiveDefs : HolEC.EXProjective.EXProjectiveDefs ←
  ioB "setupEXProjectiveDefs" (HolEC.EXProjective.setupEXProjectiveDefs deps).run
initialize BEXProjectiveOps : HolEC.EXProjective.EXProjectiveOps ←
  ioB "setupEXProjectiveOps" (HolEC.EXProjective.setupEXProjectiveOps deps BEXProjectiveDefs).run

-- EXProjectiveDefs
def exprojective : thm := BEXProjectiveDefs.exprojective
def EXPROJECTIVE_ALT : thm := BEXProjectiveDefs.EXPROJECTIVE_ALT
def projective : thm := BEXProjectiveDefs.projective
def PROJECTIVE_ALT : thm := BEXProjectiveDefs.PROJECTIVE_ALT
def PROJECTIVE_EXPROJECTIVE : thm := BEXProjectiveDefs.PROJECTIVE_EXPROJECTIVE
def EXPROJECTIVE_PROJECTIVE : thm := BEXProjectiveDefs.EXPROJECTIVE_PROJECTIVE
def EXPROJECTIVE_PROJECTIVE_ALT : thm := BEXProjectiveDefs.EXPROJECTIVE_PROJECTIVE_ALT
def edwards_excurve : thm := BEXProjectiveDefs.edwards_excurve
def EDWARDS_EXCURVE : thm := BEXProjectiveDefs.EDWARDS_EXCURVE
def edwards_pcurve : thm := BEXProjectiveDefs.edwards_pcurve
def EDWARDS_PCURVE : thm := BEXProjectiveDefs.EDWARDS_PCURVE

-- EXProjectiveOps
def edwards_exprojadd : thm := BEXProjectiveOps.edwards_exprojadd
def EDWARDS_EXPROJADD : thm := BEXProjectiveOps.EDWARDS_EXPROJADD
def edwards_exprojadd4 : thm := BEXProjectiveOps.edwards_exprojadd4
def EDWARDS_EXPROJADD4 : thm := BEXProjectiveOps.EDWARDS_EXPROJADD4
def edwards_exprojaddn : thm := BEXProjectiveOps.edwards_exprojaddn
def EDWARDS_EXPROJADDN : thm := BEXProjectiveOps.EDWARDS_EXPROJADDN
def edwards_prexprojdouble : thm := BEXProjectiveOps.edwards_prexprojdouble
def EDWARDS_PREXPROJDOUBLE_EXPROJADD : thm := BEXProjectiveOps.EDWARDS_PREXPROJDOUBLE_EXPROJADD
def EDWARDS_PREXPROJDOUBLE : thm := BEXProjectiveOps.EDWARDS_PREXPROJDOUBLE
def edwards_exprojdouble : thm := BEXProjectiveOps.edwards_exprojdouble
def EDWARDS_EXPROJDOUBLE_EXPROJADD : thm := BEXProjectiveOps.EDWARDS_EXPROJDOUBLE_EXPROJADD
def EDWARDS_EXPROJDOUBLE : thm := BEXProjectiveOps.EDWARDS_EXPROJDOUBLE
def edwards_projdouble : thm := BEXProjectiveOps.edwards_projdouble
def EDWARDS_PROJDOUBLE : thm := BEXProjectiveOps.EDWARDS_PROJDOUBLE
def edwards_prexprojdoublen : thm := BEXProjectiveOps.edwards_prexprojdoublen
def EDWARDS_PREXPROJDOUBLEN_EXPROJADDN : thm := BEXProjectiveOps.EDWARDS_PREXPROJDOUBLEN_EXPROJADDN
def EDWARDS_PREXPROJDOUBLEN : thm := BEXProjectiveOps.EDWARDS_PREXPROJDOUBLEN

/-- `needs "EC/exprojective.ml"`: already done by importing this module. -/
def ensureEXProjective : IO Unit := pure ()

end SessionEC.EXProjective
