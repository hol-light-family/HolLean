/- ---------------------------------------------------------------------- -/
/- Session wiring for EC/misc.ml                                       . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionEC/Misc.lean

  The session half of the misc.ml translation: it supplies HolEC.Misc's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "EC/misc.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolEC.Misc
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

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionEC.Misc

/-- The core theorems misc.ml uses. -/
def core1 : HolEC.Misc.CoreThms1 where
  ARITH := Session.ARITH
  CARD_EQ_0 := Session.CARD_EQ_0
  CAUCHY_GROUP_THEOREM := SessionLibrary.GroupTheory.«CAUCHY_GROUP_THEOREM»
  CHOOSE_SUBSET_EQ := Session.CHOOSE_SUBSET_EQ
  CONG := Session.CONG
  CONJ_ASSOC := Session.CONJ_ASSOC
  DIVIDES_2 := SessionLibrary.Prime.«DIVIDES_2»
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  EQ_TRANS := Session.EQ_TRANS
  EVEN_MULT := Session.EVEN_MULT
  FINITE_CARD_LE_IMAGE := Session.FINITE_CARD_LE_IMAGE
  FINITE_CARD_LE_SUBSET := Session.FINITE_CARD_LE_SUBSET
  FINITE_CARD_LE_UNIONS := Session.FINITE_CARD_LE_UNIONS
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FORALL_UNWIND_THM1 := Session.FORALL_UNWIND_THM1
  GROUP_CARRIER_NONEMPTY := SessionLibrary.GroupTheory.«GROUP_CARRIER_NONEMPTY»
  GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER»
  GROUP_ELEMENT_ORDER_EQ_2_ALT := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_EQ_2_ALT»
  HAS_SIZE := Session.HAS_SIZE
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTEGER_MOD_RING_CLAUSES := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CLAUSES»
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_ABS_POS := Session.INT_ABS_POS
  INT_ABS_POW := Session.INT_ABS_POW
  INT_CONG_MOD_0 := SessionLibrary.Integer.«INT_CONG_MOD_0»
  INT_EXISTS_POS := Session.INT_EXISTS_POS
  INT_OF_NUM_CLAUSES := Session.INT_OF_NUM_CLAUSES
  INT_OF_NUM_POW := Session.INT_OF_NUM_POW
  INT_OF_NUM_REM := Session.INT_OF_NUM_REM
  INT_REM_0 := Session.INT_REM_0
  IN_ELIM_PAIR_THM := Session.IN_ELIM_PAIR_THM
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_UNIV := Session.IN_UNIV
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_1 := Session.LE_1
  LE_MULT_RCANCEL := Session.LE_MULT_RCANCEL
  LE_REFL := Session.LE_REFL
  MOD_EXP_MOD := Session.MOD_EXP_MOD
  MOD_LT := Session.MOD_LT
  MOD_LT_EQ := Session.MOD_LT_EQ
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_SYM := Session.MULT_SYM
  NOT_LT := Session.NOT_LT
  PRIME_2 := SessionLibrary.Prime.«PRIME_2»
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RING_CHAR_DIVIDES_MUL := SessionLibrary.RingTheory.«RING_CHAR_DIVIDES_MUL»
  RING_CHAR_DIVIDES_PRIME := SessionLibrary.RingTheory.«RING_CHAR_DIVIDES_PRIME»
  SIMPLE_IMAGE_GEN := Session.SIMPLE_IMAGE_GEN
  SUBSET := Session.SUBSET
  UNIONS_GSPEC := Session.UNIONS_GSPEC
  divides := Session.divides
  num_congruent := Session.num_congruent

/-- What misc.ml uses from Session. -/
def deps : HolEC.Misc.MiscDeps where
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
  INTEGER_MOD_RING_RED_CONV := SessionLibrary.RingTheory.INTEGER_MOD_RING_RED_CONV
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in misc.ml order. -/
initialize BMiscThms : HolEC.Misc.MiscThms ←
  ioB "setupMiscThms" (HolEC.Misc.setupMiscThms deps).run

-- MiscThms
def FINITE_QUADRATIC_CURVE : thm := BMiscThms.FINITE_QUADRATIC_CURVE
def NOT_RING_CHAR_DIVIDES_TAC : HolCore.Tactics.tactic := BMiscThms.NOT_RING_CHAR_DIVIDES_TAC
def FIELD_CHAR_NOT2 : thm := BMiscThms.FIELD_CHAR_NOT2
def FIELD_CHAR_NOT3 : thm := BMiscThms.FIELD_CHAR_NOT3
def FIELD_CHAR_NOT23 : thm := BMiscThms.FIELD_CHAR_NOT23
def CAUCHY_GROUP_THEOREM_2 : thm := BMiscThms.CAUCHY_GROUP_THEOREM_2
def GROUP_ADHOC_ORDER_UNIQUE_LEMMA : thm := BMiscThms.GROUP_ADHOC_ORDER_UNIQUE_LEMMA
def SYMMETRY_LEMMA : thm := BMiscThms.SYMMETRY_LEMMA
def ASSOCIATIVITY_LEMMA : thm := BMiscThms.ASSOCIATIVITY_LEMMA
def INTEGER_MOD_RING_ROOT_EXISTS : thm := BMiscThms.INTEGER_MOD_RING_ROOT_EXISTS

/-- `needs "EC/misc.ml"`: already done by importing this module. -/
def ensureMisc : IO Unit := pure ()

end SessionEC.Misc
