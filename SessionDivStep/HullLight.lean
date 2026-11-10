/- ---------------------------------------------------------------------- -/
/- Session wiring for Divstep/hull_light.ml                                 . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionDivStep/HullLight.lean

  The session half of the hull_light.ml translation: it supplies HolDivStep.HullLight's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "Divstep/hull_light.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolDivStep.HullLight

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionDivStep.HullLight

/-- The core theorems hull_light.ml uses. -/
def core1 : HolDivStep.HullLight.CoreThms1 where
  EQ_IMP := Session.EQ_IMP
  IMP_CONJ := Session.IMP_CONJ
  INT_IMAGE := Session.INT_IMAGE
  INT_NEG_NEG := Session.INT_NEG_NEG
  INT_OF_NUM_ADD := Session.INT_OF_NUM_ADD
  INT_OF_NUM_EXISTS := Session.INT_OF_NUM_EXISTS
  INT_OF_NUM_LE := Session.INT_OF_NUM_LE
  MULT_SYM := Session.MULT_SYM
  REAL_BOUNDS_LT := Session.REAL_BOUNDS_LT
  REAL_DIV_RMUL := Session.REAL_DIV_RMUL
  REAL_INV_INV := Session.REAL_INV_INV
  REAL_LET_TRANS := Session.REAL_LET_TRANS
  REAL_LE_ADD2 := Session.REAL_LE_ADD2
  REAL_LE_DIV2_EQ := Session.REAL_LE_DIV2_EQ
  REAL_LE_INV2 := Session.REAL_LE_INV2
  REAL_LE_LMUL := Session.REAL_LE_LMUL
  REAL_LE_LMUL_EQ := Session.REAL_LE_LMUL_EQ
  REAL_LE_MUL := Session.REAL_LE_MUL
  REAL_LE_MUL2 := Session.REAL_LE_MUL2
  REAL_LE_RMUL_EQ := Session.REAL_LE_RMUL_EQ
  REAL_LE_TRANS := Session.REAL_LE_TRANS
  REAL_LTE_TRANS := Session.REAL_LTE_TRANS
  REAL_LT_DIV := Session.REAL_LT_DIV
  REAL_LT_IMP_LE := Session.REAL_LT_IMP_LE
  REAL_LT_IMP_NE := Session.REAL_LT_IMP_NE
  REAL_LT_INV := Session.REAL_LT_INV
  REAL_LT_MUL := Session.REAL_LT_MUL
  REAL_LT_NEG2 := Session.REAL_LT_NEG2
  REAL_LT_RMUL := Session.REAL_LT_RMUL
  REAL_LT_TRANS := Session.REAL_LT_TRANS
  REAL_MUL_RINV := Session.REAL_MUL_RINV
  REAL_NEG_0 := Session.REAL_NEG_0
  REAL_NEG_NEG := Session.REAL_NEG_NEG
  REAL_OF_NUM_LT := Session.REAL_OF_NUM_LT
  REAL_POW_2 := Session.REAL_POW_2
  REAL_POW_ADD := Session.REAL_POW_ADD
  REAL_POW_LE := Session.REAL_POW_LE
  REAL_POW_LE2 := Session.REAL_POW_LE2
  REAL_POW_LE2_REV := Session.REAL_POW_LE2_REV
  REAL_POW_LE_1 := Session.REAL_POW_LE_1
  REAL_POW_LT := Session.REAL_POW_LT
  REAL_POW_LT2 := Session.REAL_POW_LT2
  REAL_POW_MONO := Session.REAL_POW_MONO
  REAL_POW_MUL := Session.REAL_POW_MUL
  REAL_POW_ONE := Session.REAL_POW_ONE
  REAL_POW_POW := Session.REAL_POW_POW
  REAL_ZPOW_0 := Session.REAL_ZPOW_0
  REAL_ZPOW_1 := Session.REAL_ZPOW_1
  REAL_ZPOW_ADD := Session.REAL_ZPOW_ADD
  REAL_ZPOW_NEG := Session.REAL_ZPOW_NEG
  REAL_ZPOW_NUM := Session.REAL_ZPOW_NUM
  REAL_ZPOW_POW := Session.REAL_ZPOW_POW
  integer := Session.integer
  num_CASES := Session.num_CASES
  real_abs := Session.real_abs

/-- What hull_light.ml uses from Session. -/
def deps : HolDivStep.HullLight.HullLightDeps where
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
  LET_TAC := Session.LET_TAC
  basic_ss := Session.basic_ss
  NUM_SUB_CONV := Session.NUM_SUB_CONV
  REAL_RAT_REDUCE_CONV := Session.REAL_RAT_REDUCE_CONV
  NUM_EQ_CONV := Session.NUM_EQ_CONV
  NUM_DIV_CONV := Session.NUM_DIV_CONV
  EXP_MOD_CONV := Session.EXP_MOD_CONV
  EXPAND_CASES_CONV := Session.EXPAND_CASES_CONV
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in hull_light.ml order. -/
initialize BHullLightTactics : HolDivStep.HullLight.HullLightTactics ←
  ioB "setupHullLightTactics" (HolDivStep.HullLight.setupHullLightTactics deps).run
initialize BHullLight02 : HolDivStep.HullLight.HullLight02 ←
  ioB "setupHullLight02" (HolDivStep.HullLight.setupHullLight02 deps BHullLightTactics).run
initialize BHullLightRdiv : HolDivStep.HullLight.HullLightRdiv ←
  ioB "setupHullLightRdiv" (HolDivStep.HullLight.setupHullLightRdiv deps).run
initialize BHullLight04 : HolDivStep.HullLight.HullLight04 ←
  ioB "setupHullLight04" (HolDivStep.HullLight.setupHullLight04 deps).run
initialize BHullLight05 : HolDivStep.HullLight.HullLight05 ←
  ioB "setupHullLight05" (HolDivStep.HullLight.setupHullLight05 deps BHullLightTactics BHullLight02 BHullLight04).run
initialize BHullLight06 : HolDivStep.HullLight.HullLight06 ←
  ioB "setupHullLight06" (HolDivStep.HullLight.setupHullLight06 deps BHullLightTactics BHullLight04 BHullLight05).run
initialize BHullLight07 : HolDivStep.HullLight.HullLight07 ←
  ioB "setupHullLight07" (HolDivStep.HullLight.setupHullLight07 deps BHullLightTactics BHullLight02 BHullLight04).run
initialize BHullLight08 : HolDivStep.HullLight.HullLight08 ←
  ioB "setupHullLight08" (HolDivStep.HullLight.setupHullLight08 deps BHullLightTactics BHullLight02 BHullLight04).run
initialize BHullLight09 : HolDivStep.HullLight.HullLight09 ←
  ioB "setupHullLight09" (HolDivStep.HullLight.setupHullLight09 deps BHullLightTactics BHullLight02 BHullLight04).run
initialize BHullLight10 : HolDivStep.HullLight.HullLight10 ←
  ioB "setupHullLight10" (HolDivStep.HullLight.setupHullLight10 deps BHullLightTactics BHullLight02 BHullLight04).run
initialize BHullLight11 : HolDivStep.HullLight.HullLight11 ←
  ioB "setupHullLight11" (HolDivStep.HullLight.setupHullLight11 deps BHullLightTactics BHullLight02 BHullLight04).run
initialize BHullLight12 : HolDivStep.HullLight.HullLight12 ←
  ioB "setupHullLight12" (HolDivStep.HullLight.setupHullLight12 deps BHullLightTactics BHullLight02 BHullLight04).run
initialize BHullLight13 : HolDivStep.HullLight.HullLight13 ←
  ioB "setupHullLight13" (HolDivStep.HullLight.setupHullLight13 deps BHullLightTactics BHullLight02 BHullLight04).run
initialize BHullLight14 : HolDivStep.HullLight.HullLight14 ←
  ioB "setupHullLight14" (HolDivStep.HullLight.setupHullLight14 deps BHullLightTactics BHullLight02 BHullLight04).run
initialize BHullLight15 : HolDivStep.HullLight.HullLight15 ←
  ioB "setupHullLight15" (HolDivStep.HullLight.setupHullLight15 deps BHullLightTactics BHullLight02 BHullLightRdiv BHullLight04 BHullLight06).run
initialize BHullLight16 : HolDivStep.HullLight.HullLight16 ←
  ioB "setupHullLight16" (HolDivStep.HullLight.setupHullLight16 deps BHullLightTactics BHullLight02 BHullLight04 BHullLight06 BHullLight07 BHullLight08 BHullLight09 BHullLight10 BHullLight11 BHullLight12 BHullLight13 BHullLight14 BHullLight15).run

-- HullLightTactics
def def' : term → term → ExceptT String IO HolCore.Tactics.tactic := BHullLightTactics.def'
def notetac : term → HolCore.Tactics.tactic → HolCore.Tactics.tactic := BHullLightTactics.notetac
def note : term → List thm → HolCore.Tactics.tactic := BHullLightTactics.note
def choosevar : term → term → List thm → ExceptT String IO HolCore.Tactics.tactic := BHullLightTactics.choosevar
def num_linear : term → ExceptT String IO HolCore.Tactics.tactic := BHullLightTactics.num_linear
def int_linear : term → ExceptT String IO HolCore.Tactics.tactic := BHullLightTactics.int_linear
def real_linear : term → ExceptT String IO HolCore.Tactics.tactic := BHullLightTactics.real_linear
def real_cancel : term → ExceptT String IO HolCore.Tactics.tactic := BHullLightTactics.real_cancel
def specialize : List term → thm → ExceptT String IO HolCore.Tactics.tactic := BHullLightTactics.specialize
def twocases : term → List thm → ExceptT String IO HolCore.Tactics.tactic := BHullLightTactics.twocases

-- HullLight02
def int_neg_as_minusnum1 : thm := BHullLight02.int_neg_as_minusnum1
def real_lt_ldiv : thm := BHullLight02.real_lt_ldiv
def real_lt_rdiv_one_extra : thm := BHullLight02.real_lt_rdiv_one_extra
def real_lt_extra2 : thm := BHullLight02.real_lt_extra2
def generic_1_Ppos : thm := BHullLight02.generic_1_Ppos
def generic_1_P0 : thm := BHullLight02.generic_1_P0
def generic_2 : thm := BHullLight02.generic_2
def divsteps_s_definition : thm := BHullLight02.divsteps_s_definition
def divsteps_s : thm := BHullLight02.divsteps_s

-- HullLightRdiv
def REAL_LE_RDIV : thm := BHullLightRdiv.REAL_LE_RDIV

-- HullLight04
def divsteps_hinit_0_1 : thm := BHullLight04.divsteps_hinit_0_1
def divsteps_H0 : thm := BHullLight04.divsteps_H0
def divsteps_H1 : thm := BHullLight04.divsteps_H1

-- HullLight05
def init2stable : thm := BHullLight05.init2stable

-- HullLight06
def init2stable_simple : thm := BHullLight06.init2stable_simple
def h1_contains0 : thm := BHullLight06.h1_contains0

-- HullLight07
def theorem0 : thm := BHullLight07.theorem0

-- HullLight08
def theorem1 : thm := BHullLight08.theorem1

-- HullLight09
def theorem3 : thm := BHullLight09.theorem3

-- HullLight10
def theorem5 : thm := BHullLight10.theorem5

-- HullLight11
def theorem_2 : thm := BHullLight11.theorem_2

-- HullLight12
def theorem_1 : thm := BHullLight12.theorem_1

-- HullLight13
def theorem_4scale : thm := BHullLight13.theorem_4scale

-- HullLight14
def theorem_3scale : thm := BHullLight14.theorem_3scale

-- HullLight15
def ineq_convex : thm := BHullLight15.ineq_convex
def h1_convex : thm := BHullLight15.h1_convex
def h1_convex_horizontal : thm := BHullLight15.h1_convex_horizontal
def h1_shrink : thm := BHullLight15.h1_shrink
def h1_shrink32 : thm := BHullLight15.h1_shrink32
def unscale_4 : thm := BHullLight15.unscale_4
def unscale_3 : thm := BHullLight15.unscale_3
def h1_16_lemma1 : thm := BHullLight15.h1_16_lemma1
def h1_16_lemma1neg : thm := BHullLight15.h1_16_lemma1neg
def h1_16_lemma2 : thm := BHullLight15.h1_16_lemma2
def h1_16_lemma2neg : thm := BHullLight15.h1_16_lemma2neg
def h1_16_lemma3 : thm := BHullLight15.h1_16_lemma3
def h1_16_lemma3neg : thm := BHullLight15.h1_16_lemma3neg
def divsteps_W : thm := BHullLight15.divsteps_W
def w_transition0 : thm := BHullLight15.w_transition0
def w_transition1 : thm := BHullLight15.w_transition1
def divsteps_Houter : thm := BHullLight15.divsteps_Houter
def theoremouter : thm := BHullLight15.theoremouter
def theoremouter_simple : thm := BHullLight15.theoremouter_simple
def latticetheorem : thm := BHullLight15.latticetheorem
def iteration_stability : thm := BHullLight15.iteration_stability
def iteration_sizebound : thm := BHullLight15.iteration_sizebound
def iteration_sizebound_simple : thm := BHullLight15.iteration_sizebound_simple

-- HullLight16
def upow_bound : thm := BHullLight16.upow_bound
def spow_bound : thm := BHullLight16.spow_bound
def endtoend : thm := BHullLight16.endtoend
def endtoend_simple : thm := BHullLight16.endtoend_simple
def endtoend_bits_simple : thm := BHullLight16.endtoend_bits_simple
def endtoend_255_simple : thm := BHullLight16.endtoend_255_simple
def endtoend_256_simple : thm := BHullLight16.endtoend_256_simple
def endtoend_512_simple : thm := BHullLight16.endtoend_512_simple
def endtoend_16384_simple : thm := BHullLight16.endtoend_16384_simple

/-- `needs "Divstep/hull_light.ml"`: already done by importing this module. -/
def ensureHullLight : IO Unit := pure ()

end SessionDivStep.HullLight
