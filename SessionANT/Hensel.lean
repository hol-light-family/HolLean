/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/hensel.ml                                     . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/Hensel.lean

  The session half of the hensel.ml translation: it supplies HolANT.Hensel's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/hensel.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.Hensel
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionANT.IdealArith

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.Hensel

/-- The core theorems hensel.ml uses. -/
def core1 : HolANT.Hensel.CoreThms1 where
  ADD_CLAUSES := Session.ADD_CLAUSES
  ADD_EQ_0 := Session.ADD_EQ_0
  ADD_SYM := Session.ADD_SYM
  ARITH_EQ := Session.ARITH_EQ
  COEFF_ABOVE_DEG := SessionLibrary.RingTheory.«COEFF_ABOVE_DEG»
  COEFF_IN_CARRIER_ALT := SessionLibrary.RingTheory.«COEFF_IN_CARRIER_ALT»
  COEFF_POLY_0 := SessionLibrary.RingTheory.«COEFF_POLY_0»
  COEFF_POLY_ADD := SessionLibrary.RingTheory.«COEFF_POLY_ADD»
  COEFF_POLY_MUL := SessionLibrary.RingTheory.«COEFF_POLY_MUL»
  COEFF_POLY_NEG := SessionLibrary.RingTheory.«COEFF_POLY_NEG»
  COEFF_POLY_SUB := SessionLibrary.RingTheory.«COEFF_POLY_SUB»
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  IDEAL_POW_0 := SessionANT.IdealArith.«IDEAL_POW_0»
  IDEAL_POW_1 := SessionANT.IdealArith.«IDEAL_POW_1»
  IDEAL_POW_ANTIMONO := SessionANT.IdealArith.«IDEAL_POW_ANTIMONO»
  IDEAL_POW_PRINCIPAL := SessionANT.IdealArith.«IDEAL_POW_PRINCIPAL»
  IMP_IMP := Session.IMP_IMP
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGER_RING_IDEAL_GENERATED_SING := SessionLibrary.RingTheory.«INTEGER_RING_IDEAL_GENERATED_SING»
  INTEGER_RING_OF_NUM := SessionLibrary.RingTheory.«INTEGER_RING_OF_NUM»
  INTEGER_RING_POW := SessionLibrary.RingTheory.«INTEGER_RING_POW»
  INTEGER_RING_SUB := SessionLibrary.RingTheory.«INTEGER_RING_SUB»
  INT_SUB_RZERO := Session.INT_SUB_RZERO
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_ADD := SessionLibrary.RingTheory.«IN_RING_IDEAL_ADD»
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_RING_IDEAL_NEG := SessionLibrary.RingTheory.«IN_RING_IDEAL_NEG»
  IN_RING_IDEAL_RMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_RMUL»
  IN_RING_IDEAL_SUB := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUB»
  IN_RING_IDEAL_SUM := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUM»
  IN_UNIV := Session.IN_UNIV
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_1 := Session.LE_1
  LE_ADD := Session.LE_ADD
  LE_ADDR := Session.LE_ADDR
  LE_REFL := Session.LE_REFL
  LT_IMP_LE := Session.LT_IMP_LE
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_LT := Session.NOT_LT
  ONE := Session.ONE
  POLY_CLAUSES := SessionLibrary.RingTheory.«POLY_CLAUSES»
  POLY_DEG_0 := SessionLibrary.RingTheory.«POLY_DEG_0»
  POLY_DEG_EQ_FROM_LE := SessionLibrary.RingTheory.«POLY_DEG_EQ_FROM_LE»
  POLY_DEG_LE_COEFF_EQ := SessionLibrary.RingTheory.«POLY_DEG_LE_COEFF_EQ»
  POLY_DERIV_CONST := SessionLibrary.RingTheory.«POLY_DERIV_CONST»
  POLY_DERIV_IN_CARRIER := SessionLibrary.RingTheory.«POLY_DERIV_IN_CARRIER»
  POLY_DERIV_SUB := SessionLibrary.RingTheory.«POLY_DERIV_SUB»
  POLY_DERIV_VAR_POW := SessionLibrary.RingTheory.«POLY_DERIV_VAR_POW»
  POLY_DIVISION_COEFF_IDEAL := SessionLibrary.RingTheory.«POLY_DIVISION_COEFF_IDEAL»
  POLY_EVAL := SessionLibrary.RingTheory.«POLY_EVAL»
  POLY_EVAL_0 := SessionLibrary.RingTheory.«POLY_EVAL_0»
  POLY_EVAL_CONST := SessionLibrary.RingTheory.«POLY_EVAL_CONST»
  POLY_EVAL_MUL := SessionLibrary.RingTheory.«POLY_EVAL_MUL»
  POLY_EVAL_POW := SessionLibrary.RingTheory.«POLY_EVAL_POW»
  POLY_EVAL_SUB := SessionLibrary.RingTheory.«POLY_EVAL_SUB»
  POLY_EVAL_SUB_IN_IDEAL := SessionLibrary.RingTheory.«POLY_EVAL_SUB_IN_IDEAL»
  POLY_EVAL_TAYLOR := SessionLibrary.RingTheory.«POLY_EVAL_TAYLOR»
  POLY_EVAL_VAR := SessionLibrary.RingTheory.«POLY_EVAL_VAR»
  POLY_RING_CLAUSES := SessionLibrary.RingTheory.«POLY_RING_CLAUSES»
  POLY_TOP_EQ_0 := SessionLibrary.RingTheory.«POLY_TOP_EQ_0»
  RADICAL_IDEAL_POW := SessionANT.IdealArith.«RADICAL_IDEAL_POW»
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD := SessionLibrary.RingTheory.«RING_ADD»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_IDEAL_POLY_COEFF := SessionLibrary.RingTheory.«RING_IDEAL_POLY_COEFF»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_IN_IDEAL_POW := SessionANT.IdealArith.«RING_MUL_IN_IDEAL_POW»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_POLYNOMIAL := SessionLibrary.RingTheory.«RING_POLYNOMIAL»
  RING_POLYNOMIAL_0 := SessionLibrary.RingTheory.«RING_POLYNOMIAL_0»
  RING_POLYNOMIAL_CONST := SessionLibrary.RingTheory.«RING_POLYNOMIAL_CONST»
  RING_POLYNOMIAL_IMP_POWERSERIES := SessionLibrary.RingTheory.«RING_POLYNOMIAL_IMP_POWERSERIES»
  RING_POLYNOMIAL_MUL := SessionLibrary.RingTheory.«RING_POLYNOMIAL_MUL»
  RING_POLYNOMIAL_POW := SessionLibrary.RingTheory.«RING_POLYNOMIAL_POW»
  RING_POLYNOMIAL_SUB := SessionLibrary.RingTheory.«RING_POLYNOMIAL_SUB»
  RING_POLYNOMIAL_VAR := SessionLibrary.RingTheory.«RING_POLYNOMIAL_VAR»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_ONE := SessionLibrary.RingTheory.«RING_POW_ONE»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_SUB_RZERO := SessionLibrary.RingTheory.«RING_SUB_RZERO»
  RING_UNIT_QUOTIENT_RING_COSET := SessionLibrary.RingTheory.«RING_UNIT_QUOTIENT_RING_COSET»
  RING_UNIT_QUOTIENT_RING_COSET_EQ := SessionLibrary.RingTheory.«RING_UNIT_QUOTIENT_RING_COSET_EQ»
  RING_UNIT_QUOTIENT_RING_COSET_MUL := SessionLibrary.RingTheory.«RING_UNIT_QUOTIENT_RING_COSET_MUL»
  RING_UNIT_QUOTIENT_RING_COSET_POW := SessionLibrary.RingTheory.«RING_UNIT_QUOTIENT_RING_COSET_POW»
  RING_UNIT_QUOTIENT_RING_RADICAL := SessionLibrary.RingTheory.«RING_UNIT_QUOTIENT_RING_RADICAL»
  SUBSET := Session.SUBSET
  cong := Session.cong
  int_mod := Session.int_mod

/-- What hensel.ml uses from Session. -/
def deps : HolANT.Hensel.HenselDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  new_recursive_definition ax s := do
    ExceptT.mk (Session.new_recursive_definition ax (← HolLight.q s))
  LIST_INDUCT_TAC := Session.LIST_INDUCT_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  METIS_TAC := Session.METIS_TAC
  ASM_METIS_TAC := Session.ASM_METIS_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  TAUT t := ExceptT.mk (Session.TAUT t)
  ITAUT t := ExceptT.mk (Session.ITAUT t)
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH t)
  REAL_FIELD t := ExceptT.mk (Session.REAL_FIELD t)
  REAL_ARITH_TAC := Session.REAL_ARITH_TAC
  ASM_REAL_ARITH_TAC := Session.ASM_REAL_ARITH_TAC
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
  basic_ss := Session.basic_ss
  INTEGER_MOD_RING_RED_CONV := SessionLibrary.RingTheory.INTEGER_MOD_RING_RED_CONV
  NUM_SUB_CONV := Session.NUM_SUB_CONV
  REAL_RAT_REDUCE_CONV := Session.REAL_RAT_REDUCE_CONV
  NUM_EQ_CONV := Session.NUM_EQ_CONV
  NUM_DIV_CONV := Session.NUM_DIV_CONV
  EXP_MOD_CONV := Session.EXP_MOD_CONV
  EXPAND_CASES_CONV := Session.EXPAND_CASES_CONV
  DIVIDES_CONV := SessionLibrary.Prime.DIVIDES_CONV
  COPRIME_CONV := SessionLibrary.Prime.COPRIME_CONV
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in hensel.ml order. -/
initialize BHensel01 : HolANT.Hensel.Hensel01 ←
  ioB "setupHensel01" (HolANT.Hensel.setupHensel01 deps).run
initialize BHensel02 : HolANT.Hensel.Hensel02 ←
  ioB "setupHensel02" (HolANT.Hensel.setupHensel02 deps BHensel01).run

-- Hensel01
def RING_UNIT_QUOTIENT_RING_IDEAL_POW : thm := BHensel01.RING_UNIT_QUOTIENT_RING_IDEAL_POW
def HENSEL_NEWTON_STEP : thm := BHensel01.HENSEL_NEWTON_STEP
def HENSEL_LEMMA : thm := BHensel01.HENSEL_LEMMA
def HENSEL_NEWTON_STEP_SIMPLE : thm := BHensel01.HENSEL_NEWTON_STEP_SIMPLE
def HENSEL_LEMMA_POW : thm := BHensel01.HENSEL_LEMMA_POW
def HENSEL_LEMMA_UNIQUE : thm := BHensel01.HENSEL_LEMMA_UNIQUE
def HENSEL_LEMMA_SIMPLE : thm := BHensel01.HENSEL_LEMMA_SIMPLE
def HENSEL_LEMMA_NEWTON : thm := BHensel01.HENSEL_LEMMA_NEWTON
def HENSEL_ROOT_UNIQUE : thm := BHensel01.HENSEL_ROOT_UNIQUE
def POLY_EVAL_DERIV_VAR_POW_SUB_CONST : thm := BHensel01.POLY_EVAL_DERIV_VAR_POW_SUB_CONST
def POWER_RESIDUE_MODULO_IDEAL_POW : thm := BHensel01.POWER_RESIDUE_MODULO_IDEAL_POW
def INTEGER_RING_IDEAL_POW_SING : thm := BHensel01.INTEGER_RING_IDEAL_POW_SING
def RING_UNIT_QUOTIENT_INTEGER_RING : thm := BHensel01.RING_UNIT_QUOTIENT_INTEGER_RING
def HENSEL_LEMMA_INTEGER : thm := BHensel01.HENSEL_LEMMA_INTEGER
def INT_POWER_RESIDUE_MODULO_POWER : thm := BHensel01.INT_POWER_RESIDUE_MODULO_POWER
def COEFF_POLY_MUL_IN_IDEAL_POW : thm := BHensel01.COEFF_POLY_MUL_IN_IDEAL_POW
def HENSEL_FACTORIZATION_STEP : thm := BHensel01.HENSEL_FACTORIZATION_STEP

-- Hensel02
def HENSEL_LEMMA_FACTORIZATION : thm := BHensel02.HENSEL_LEMMA_FACTORIZATION

/-- `needs "ANT/hensel.ml"`: already done by importing this module. -/
def ensureHensel : IO Unit := pure ()

end SessionANT.Hensel
