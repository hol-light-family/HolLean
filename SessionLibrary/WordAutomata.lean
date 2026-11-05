/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/wordautomata.ml.                      -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/WordAutomata.lean

  The session half of the wordautomata.ml translation: it supplies
  HolLibrary.WordAutomata's dependencies from Session and
  SessionLibrary.RSTC, BDD and Words, and exports every name under its HOL
  Light name.  Importing this module is `needs "Library/wordautomata.ml"`;
  its `needs` of rstc.ml, bdd.ml and words.ml are the imports of those
  modules.  The bundles are built by `initialize` when the module is loaded,
  in file order.
-/

import Session
import HolLibrary.WordAutomata
import SessionLibrary.RSTC
import SessionLibrary.BDD
import SessionLibrary.Words

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.WordAutomata

/-- The core theorems word_automata.ml uses. -/
def core1 : HolLibrary.WordAutomata.CoreThms1 where
  ADD1 := Session.ADD1
  ADD_EQ_0 := Session.ADD_EQ_0
  ADD_SUB := Session.ADD_SUB
  ADD_SYM := Session.ADD_SYM
  AND_FORALL_THM := Session.AND_FORALL_THM
  ARITH_EQ := Session.ARITH_EQ
  ARITH_LE := Session.ARITH_LE
  ARITH_LT := Session.ARITH_LT
  BIT0 := Session.BIT0
  BIT1 := Session.BIT1
  BITVAL_CLAUSES := SessionLibrary.Words.«BITVAL_CLAUSES»
  BIT_GUARD := SessionLibrary.Words.«BIT_GUARD»
  BIT_WORD_0 := SessionLibrary.Words.«BIT_WORD_0»
  BIT_WORD_ADD := SessionLibrary.Words.«BIT_WORD_ADD»
  BIT_WORD_AND := SessionLibrary.Words.«BIT_WORD_AND»
  BIT_WORD_BITVAL := SessionLibrary.Words.«BIT_WORD_BITVAL»
  BIT_WORD_INT_MIN := SessionLibrary.Words.«BIT_WORD_INT_MIN»
  BIT_WORD_ISHR := SessionLibrary.Words.«BIT_WORD_ISHR»
  BIT_WORD_NEG := SessionLibrary.Words.«BIT_WORD_NEG»
  BIT_WORD_NOT := SessionLibrary.Words.«BIT_WORD_NOT»
  BIT_WORD_OR := SessionLibrary.Words.«BIT_WORD_OR»
  BIT_WORD_OR_NEG := SessionLibrary.Words.«BIT_WORD_OR_NEG»
  BIT_WORD_SHL := SessionLibrary.Words.«BIT_WORD_SHL»
  BIT_WORD_SUB := SessionLibrary.Words.«BIT_WORD_SUB»
  BIT_WORD_USHR := SessionLibrary.Words.«BIT_WORD_USHR»
  BIT_WORD_XOR := SessionLibrary.Words.«BIT_WORD_XOR»
  CONJ_ACI := Session.CONJ_ACI
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIMINDEX_NONZERO := Session.DIMINDEX_NONZERO
  DIVIDES_LE := Session.DIVIDES_LE
  EXP_EQ_0 := Session.EXP_EQ_0
  FORALL_AND_THM := Session.FORALL_AND_THM
  FORALL_PAIR_FUN_THM := Session.FORALL_PAIR_FUN_THM
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  GE := Session.GE
  GT := Session.GT
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  INT_GE := Session.INT_GE
  INT_GT := Session.INT_GT
  INT_MUL_RNEG := Session.INT_MUL_RNEG
  INT_NOT_LT := Session.INT_NOT_LT
  INT_OF_NUM_CLAUSES := Session.INT_OF_NUM_CLAUSES
  INT_POW := Session.INT_POW
  IWORD_EQ := SessionLibrary.Words.«IWORD_EQ»
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LET_TRANS := Session.LET_TRANS
  LE_1 := Session.LE_1
  LE_CASES := Session.LE_CASES
  LE_EXP := Session.LE_EXP
  LT_IMP_NE := Session.LT_IMP_NE
  MSB_IVAL := SessionLibrary.Words.«MSB_IVAL»
  NOT_LT := Session.NOT_LT
  NOT_SUC := Session.NOT_SUC
  NUMERAL := Session.NUMERAL
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RTC_INDUCT_L := SessionLibrary.RSTC.«RTC_INDUCT_L»
  RTC_RULES := SessionLibrary.RSTC.«RTC_RULES»
  SUC_SUB1 := Session.SUC_SUB1
  WORD_ADD_OR := SessionLibrary.Words.«WORD_ADD_OR»
  WORD_AND_0 := SessionLibrary.Words.«WORD_AND_0»
  WORD_AND_1 := SessionLibrary.Words.«WORD_AND_1»
  WORD_EQ_BITS := SessionLibrary.Words.«WORD_EQ_BITS»
  WORD_EQ_BITS_ALT := SessionLibrary.Words.«WORD_EQ_BITS_ALT»
  WORD_ISHR_COMPOSE := SessionLibrary.Words.«WORD_ISHR_COMPOSE»
  WORD_ISHR_ZERO := SessionLibrary.Words.«WORD_ISHR_ZERO»
  WORD_IWORD := SessionLibrary.Words.«WORD_IWORD»
  WORD_MUL_0 := SessionLibrary.Words.«WORD_MUL_0»
  WORD_OR_0 := SessionLibrary.Words.«WORD_OR_0»
  WORD_OR_EQ_0 := SessionLibrary.Words.«WORD_OR_EQ_0»
/-- The core theorems word_automata.ml uses. -/
def core2 : HolLibrary.WordAutomata.CoreThms2 where
  WORD_SHL_COMPOSE := SessionLibrary.Words.«WORD_SHL_COMPOSE»
  WORD_SHL_ZERO := SessionLibrary.Words.«WORD_SHL_ZERO»
  WORD_USHR_COMPOSE := SessionLibrary.Words.«WORD_USHR_COMPOSE»
  WORD_USHR_ZERO := SessionLibrary.Words.«WORD_USHR_ZERO»
  WORD_XOR_0 := SessionLibrary.Words.«WORD_XOR_0»
  WORD_XOR_EQ_0 := SessionLibrary.Words.«WORD_XOR_EQ_0»
  bitval := SessionLibrary.Words.«bitval»
  irelational2 := SessionLibrary.Words.«irelational2»
  num_CASES := Session.num_CASES
  num_INDUCTION := Session.num_INDUCTION
  num_divides := Session.num_divides
  relational2 := SessionLibrary.Words.«relational2»
  word_INT_MIN := SessionLibrary.Words.«word_INT_MIN»
  word_ige := SessionLibrary.Words.«word_ige»
  word_igt := SessionLibrary.Words.«word_igt»
  word_ile := SessionLibrary.Words.«word_ile»
  word_ilt := SessionLibrary.Words.«word_ilt»
  word_ugt := SessionLibrary.Words.«word_ugt»
  word_ule := SessionLibrary.Words.«word_ule»
  word_ult := SessionLibrary.Words.«word_ult»
/-- The core theorems word_automata.ml uses. -/
def core3 : HolLibrary.WordAutomata.CoreThms3 where
/-- The core theorems word_automata.ml uses. -/
def core4 : HolLibrary.WordAutomata.CoreThms4 where

/-- What wordautomata.ml uses from Session. -/
def deps : HolLibrary.WordAutomata.WordAutomataDeps where
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  INTEGER_RULE t := ExceptT.mk (Session.INTEGER_RULE t)
  NUMBER_RULE t := ExceptT.mk (Session.NUMBER_RULE t)
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  NUM_RED_CONV := Session.NUM_RED_CONV
  NNFC_CONV := Session.NNFC_CONV
  CNF_CONV := Session.CNF_CONV
  PRENEX_CONV := Session.PRENEX_CONV
  GEN_BETA_CONV := Session.GEN_BETA_CONV
  num_CONV := Session.num_CONV
  TAUT t := ExceptT.mk (Session.TAUT t)
  DISJ_ACI_RULE t := liftExcept (Session.DISJ_ACI_RULE t)
  mk_vtable := HolLibrary.BDD.mk_vtable
  mk_utable := (SessionLibrary.BDD.mk_utable : IO _)
  mk_ctable := (HolLibrary.BDD.mk_ctable : IO _)
  BDD_VAR tt tm := ExceptT.mk (SessionLibrary.BDD.BDD_VAR tt tm)
  BDD_OF_TERM defs tt tm := ExceptT.mk (SessionLibrary.BDD.BDD_OF_TERM defs tt tm)
  BDD_AND tt bs := ExceptT.mk (SessionLibrary.BDD.BDD_AND tt bs)
  BDD_OR tt bs := ExceptT.mk (SessionLibrary.BDD.BDD_OR tt bs)
  BDD_IMP tt bs := ExceptT.mk (SessionLibrary.BDD.BDD_IMP tt bs)
  BDD_EXISTS tt x := do
    let f ← ExceptT.mk (SessionLibrary.BDD.BDD_EXISTS tt x)
    pure (fun b => ExceptT.mk (f b))
  BITBLAST_TAC := SessionLibrary.Words.BITBLAST_TAC
  BITBLAST_RULE t := ExceptT.mk (SessionLibrary.Words.BITBLAST_RULE t)
  WORD_RED_CONV := SessionLibrary.Words.WORD_RED_CONV
  WORD_RULE t := ExceptT.mk (SessionLibrary.Words.WORD_RULE t)
  WORD_ARITH t := ExceptT.mk (SessionLibrary.Words.WORD_ARITH t)
  core1 := core1
  core2 := core2
  core3 := core3
  core4 := core4

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in wordautomata.ml order. -/
initialize BReachable : HolLibrary.WordAutomata.Reachable ←
  ioB "setupReachable" (HolLibrary.WordAutomata.setupReachable deps).run
initialize BShifts : HolLibrary.WordAutomata.Shifts ←
  ioB "setupShifts" (HolLibrary.WordAutomata.setupShifts deps).run
initialize BIneq : HolLibrary.WordAutomata.Ineq ←
  ioB "setupIneq" (HolLibrary.WordAutomata.setupIneq deps).run
initialize BHorn : HolLibrary.WordAutomata.Horn ←
  ioB "setupHorn" (HolLibrary.WordAutomata.setupHorn deps BReachable BShifts BIneq).run
initialize BOverall : HolLibrary.WordAutomata.Overall ←
  ioB "setupOverall" (HolLibrary.WordAutomata.setupOverall deps BShifts BIneq BHorn).run

-- Reachable
def OVERAPPROXIMATE_REACHABLE : thm := BReachable.OVERAPPROXIMATE_REACHABLE
def REACHABLE_STATE_TAC : HolCore.Tactics.tactic := fun g => BReachable.REACHABLE_STATE_TAC g

-- Shifts
def EXPAND_SHIFT_CONV : HolCore.Equal.ioconv := fun t => BShifts.EXPAND_SHIFT_CONV t
def word_shladd : thm := BShifts.word_shladd
def WORD_SHLADD : thm := BShifts.WORD_SHLADD
def BIT_WORD_SHLADD : thm := BShifts.BIT_WORD_SHLADD
def WORD_SHLADD_0 : thm := BShifts.WORD_SHLADD_0
def WORD_NUMERAL_SHLADD : thm := BShifts.WORD_NUMERAL_SHLADD
def WORD_USHR_SHLADD : thm := BShifts.WORD_USHR_SHLADD
def WORD_ISHR_SHLADD : thm := BShifts.WORD_ISHR_SHLADD
def DEFINE_WORD_INT_MIN : thm := BShifts.DEFINE_WORD_INT_MIN

-- Ineq
def VAL_LT_ELIM_THM : thm := BIneq.VAL_LT_ELIM_THM
def IVAL_LT_ELIM_THM : thm := BIneq.IVAL_LT_ELIM_THM
def IVAL_LT_0_ELIM_THM : thm := BIneq.IVAL_LT_0_ELIM_THM
def CONJ_WORD_EQ_0 : thm := BIneq.CONJ_WORD_EQ_0
def DISJ_WORD_EQ_0 : thm := BIneq.DISJ_WORD_EQ_0

-- Horn
def WORD_AUTO_TRANSIFY_TAC : HolCore.Tactics.tactic := fun g => BHorn.WORD_AUTO_TRANSIFY_TAC g
def LSB_CARRYING : thm := BHorn.LSB_CARRYING
def XSB_CARRYING : thm := BHorn.XSB_CARRYING
def ABBREVIATE_SHR_TAC : HolCore.Tactics.tactic := fun g => BHorn.ABBREVIATE_SHR_TAC g
def ABBREVIATE_CARRYING_TAC : HolCore.Tactics.tactic := fun g => BHorn.ABBREVIATE_CARRYING_TAC g
def LSB_CARRY_RULE := BHorn.LSB_CARRY_RULE
def XSB_CARRY_RULE := BHorn.XSB_CARRY_RULE
def BIT_PUSH_CONV : HolCore.Equal.ioconv := fun t => BHorn.BIT_PUSH_CONV t
def LSB_SIMP_CONV : HolCore.Equal.ioconv := fun t => BHorn.LSB_SIMP_CONV t
def MSB_SIMP_CONV : HolCore.Equal.ioconv := fun t => BHorn.MSB_SIMP_CONV t
def HORN_WORD_AUTO_TAC : HolCore.Tactics.tactic := fun g => BHorn.HORN_WORD_AUTO_TAC g
def CORE_WORD_AUTO_TAC : HolCore.Tactics.tactic := fun g => BHorn.CORE_WORD_AUTO_TAC g

-- Overall
def WORD_MUL_SHLADD : thm := BOverall.WORD_MUL_SHLADD
def CHARACTERIZE_INT_MIN_TAC : HolCore.Tactics.tactic := fun g => BOverall.CHARACTERIZE_INT_MIN_TAC g
def PURE_WORD_AUTO_TAC : HolCore.Tactics.tactic := fun g => BOverall.PURE_WORD_AUTO_TAC g
def PURE_WORD_AUTO_RULE : term → IO (Except String thm) := fun t => (BOverall.PURE_WORD_AUTO_RULE t).run
def WORD_AUTO_TAC : HolCore.Tactics.tactic := fun g => BOverall.WORD_AUTO_TAC g
def WORD_AUTO_RULE : term → IO (Except String thm) := fun t => (BOverall.WORD_AUTO_RULE t).run
/-- `needs "Library/wordautomata.ml"`: already done by importing this module. -/
def ensureWordAutomata : IO Unit := pure ()

end SessionLibrary.WordAutomata
