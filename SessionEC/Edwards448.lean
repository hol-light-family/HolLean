/- ---------------------------------------------------------------------- -/
/- Session wiring for EC/edwards448.ml                                 . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionEC/Edwards448.lean

  The session half of the edwards448.ml translation: it supplies HolEC.Edwards448's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "EC/edwards448.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolEC.Edwards448
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
import SessionEC.ExcludeRoots
import SessionEC.ComputeGroup

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionEC.Edwards448

/-- The core theorems edwards448.ml uses. -/
def core1 : HolEC.Edwards448.CoreThms1 where
  ARITH_EQ := Session.ARITH_EQ
  CARD_BOUND_EDWARDS_CURVE := SessionEC.Edwards.«CARD_BOUND_EDWARDS_CURVE»
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_INTEGER_MOD_RING := SessionLibrary.RingTheory.«CARD_INTEGER_MOD_RING»
  CARD_SUBSET := Session.CARD_SUBSET
  CARRIER_SUBGROUP_GENERATED_SUBGROUP := SessionLibrary.GroupTheory.«CARRIER_SUBGROUP_GENERATED_SUBGROUP»
  CONG := Session.CONG
  CYCLIC_GROUP_ALT := SessionLibrary.GroupTheory.«CYCLIC_GROUP_ALT»
  CYCLIC_IMP_ABELIAN_GROUP := SessionLibrary.GroupTheory.«CYCLIC_IMP_ABELIAN_GROUP»
  DIVIDES_PRIMEPOW := SessionLibrary.Prime.«DIVIDES_PRIMEPOW»
  EDWARDS_GROUP := SessionEC.Edwards.«EDWARDS_GROUP»
  EDWARDS_GROUP_ELEMENT_ORDER_EQ_2 := SessionEC.Edwards.«EDWARDS_GROUP_ELEMENT_ORDER_EQ_2»
  EDWARDS_GROUP_ELEMENT_ORDER_EQ_4 := SessionEC.Edwards.«EDWARDS_GROUP_ELEMENT_ORDER_EQ_4»
  EDWARDS_GROUP_ELEMENT_ORDER_EQ_8_EQUIV := SessionEC.Edwards.«EDWARDS_GROUP_ELEMENT_ORDER_EQ_8_EQUIV»
  EULER_CRITERION := SessionLibrary.Primitive.«EULER_CRITERION»
  EXTENSION := Session.EXTENSION
  FIELD_INTEGER_MOD_RING := SessionLibrary.RingTheory.«FIELD_INTEGER_MOD_RING»
  FINITE_EDWARDS_CURVE := SessionEC.Edwards.«FINITE_EDWARDS_CURVE»
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_INTEGER_MOD_RING := SessionLibrary.RingTheory.«FINITE_INTEGER_MOD_RING»
  FINITE_SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«FINITE_SUBGROUP_GENERATED»
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  GROUP_CARRIER_NONEMPTY := SessionLibrary.GroupTheory.«GROUP_CARRIER_NONEMPTY»
  GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER»
  GROUP_ELEMENT_ORDER_EQ_1 := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_EQ_1»
  GROUP_ELEMENT_ORDER_MUL_EQ := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_MUL_EQ»
  GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED»
  GROUP_ELEMENT_ORDER_UNIQUE_PRIME := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_UNIQUE_PRIME»
  GROUP_ID := SessionLibrary.GroupTheory.«GROUP_ID»
  HAS_SIZE := Session.HAS_SIZE
  IMP_CONJ := Session.IMP_CONJ
  IN := Session.IN
  INTEGER_MOD_RING := SessionLibrary.RingTheory.«INTEGER_MOD_RING»
  INTEGER_MOD_RING_CHAR := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CHAR»
  INTEGER_MOD_RING_CLAUSES := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CLAUSES»
  INTEGER_MOD_RING_ROOT_EXISTS := SessionEC.Misc.«INTEGER_MOD_RING_ROOT_EXISTS»
  INT_FORALL_ABS := Session.INT_FORALL_ABS
  INT_MUL_ASSOC := Session.INT_MUL_ASSOC
  INT_OF_NUM_CLAUSES := Session.INT_OF_NUM_CLAUSES
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_POW2_ABS := Session.INT_POW2_ABS
  INT_REM_EQ := Session.INT_REM_EQ
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_INSERT := Session.IN_INSERT
  IN_INTEGER_MOD_RING_CARRIER := SessionLibrary.RingTheory.«IN_INTEGER_MOD_RING_CARRIER»
  IN_SING := Session.IN_SING
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_TRANS := Session.LE_TRANS
  MULT_CLAUSES := Session.MULT_CLAUSES
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_IMP := Session.NOT_IMP
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  PAIR_EQ := Session.PAIR_EQ
  PRIME_2 := SessionLibrary.Prime.«PRIME_2»
  SUBGROUP_GENERATED_ELEMENT_ORDER := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED_ELEMENT_ORDER»
  SUBGROUP_OF_IMP_SUBSET := SessionLibrary.GroupTheory.«SUBGROUP_OF_IMP_SUBSET»
  SUBSET := Session.SUBSET
  SYLOW_THEOREM := SessionLibrary.GroupTheory.«SYLOW_THEOREM»
  divides := Session.divides
  edwards_0 := SessionEC.Edwards.«edwards_0»
  edwards_add := SessionEC.Edwards.«edwards_add»
  edwards_curve := SessionEC.Edwards.«edwards_curve»
  edwards_neg := SessionEC.Edwards.«edwards_neg»
  edwards_nonsingular := SessionEC.Edwards.«edwards_nonsingular»
  num_congruent := Session.num_congruent

/-- What edwards448.ml uses from Session. -/
def deps : HolEC.Edwards448.Edwards448Deps where
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
  NUM_EQ_CONV := Session.NUM_EQ_CONV
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

/- The bundles, in edwards448.ml order. -/
initialize BEdwards448Defs : HolEC.Edwards448.Edwards448Defs ←
  ioB "setupEdwards448Defs" (HolEC.Edwards448.setupEdwards448Defs deps).run
initialize BEdwards448Group : HolEC.Edwards448.Edwards448Group ←
  ioB "setupEdwards448Group" (HolEC.Edwards448.setupEdwards448Group deps BEdwards448Defs).run

-- Edwards448Defs
def p_448 : thm := BEdwards448Defs.p_448
def n_448 : thm := BEdwards448Defs.n_448
def e_448 : thm := BEdwards448Defs.e_448
def d_448 : thm := BEdwards448Defs.d_448
def E_448 : thm := BEdwards448Defs.E_448
def EE_448 : thm := BEdwards448Defs.EE_448
def F_448 : thm := BEdwards448Defs.F_448
def H_448 : thm := BEdwards448Defs.H_448
def P_448 : thm := BEdwards448Defs.P_448
def N_448 : thm := BEdwards448Defs.N_448
def PRIME_P448 : thm := BEdwards448Defs.PRIME_P448
def PRIME_N448 : thm := BEdwards448Defs.PRIME_N448
def edwards448_group : thm := BEdwards448Defs.edwards448_group
def EDWARDS_NONSINGULAR_448 : thm := BEdwards448Defs.EDWARDS_NONSINGULAR_448
def EDWARDS448_GROUP : thm := BEdwards448Defs.EDWARDS448_GROUP

-- Edwards448Group
def FINITE_GROUP_CARRIER_EDWARDS448 : thm := BEdwards448Group.FINITE_GROUP_CARRIER_EDWARDS448
def GENERATOR_IN_GROUP_CARRIER_EDWARDS448 : thm := BEdwards448Group.GENERATOR_IN_GROUP_CARRIER_EDWARDS448
def GROUP_ELEMENT_ORDER_EDWARDS448_E448 : thm := BEdwards448Group.GROUP_ELEMENT_ORDER_EDWARDS448_E448
def GENERATOR_IN_GROUP_CARRIER_F448 : thm := BEdwards448Group.GENERATOR_IN_GROUP_CARRIER_F448
def GROUP_ELEMENT_ORDER_EDWARDS448_F448 : thm := BEdwards448Group.GROUP_ELEMENT_ORDER_EDWARDS448_F448
def GENERATOR_IN_GROUP_CARRIER_H448 : thm := BEdwards448Group.GENERATOR_IN_GROUP_CARRIER_H448
def GROUP_ELEMENT_ORDER_EDWARDS448_H448 : thm := BEdwards448Group.GROUP_ELEMENT_ORDER_EDWARDS448_H448
def EDWARDS448_ORDER_1 : thm := BEdwards448Group.EDWARDS448_ORDER_1
def EDWARDS448_ORDER_2 : thm := BEdwards448Group.EDWARDS448_ORDER_2
def EDWARDS448_ORDER_4 : thm := BEdwards448Group.EDWARDS448_ORDER_4
def EDWARDS448_ORDER_8 : thm := BEdwards448Group.EDWARDS448_ORDER_8
def FULLGENERATOR_IN_GROUP_CARRIER_EDWARDS448 : thm := BEdwards448Group.FULLGENERATOR_IN_GROUP_CARRIER_EDWARDS448
def GROUP_ELEMENT_ORDER_EDWARDS448_EE448 : thm := BEdwards448Group.GROUP_ELEMENT_ORDER_EDWARDS448_EE448
def SIZE_EDWARDS448_GROUP : thm := BEdwards448Group.SIZE_EDWARDS448_GROUP
def GENERATED_EDWARDS448_GROUP : thm := BEdwards448Group.GENERATED_EDWARDS448_GROUP
def CYCLIC_EDWARDS448_GROUP : thm := BEdwards448Group.CYCLIC_EDWARDS448_GROUP
def ABELIAN_EDWARDS448_GROUP : thm := BEdwards448Group.ABELIAN_EDWARDS448_GROUP

/-- `needs "EC/edwards448.ml"`: already done by importing this module. -/
def ensureEdwards448 : IO Unit := pure ()

end SessionEC.Edwards448
