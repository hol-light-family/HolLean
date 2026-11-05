/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/calcreal.ml.                          -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/CalcReal.lean

  The session half of the calcreal.ml translation: it supplies
  HolLibrary.CalcReal's dependencies from Session, SessionLibrary.Analysis
  and SessionLibrary.Transc, and exports every name under its HOL Light
  name.  Importing this module is `needs "Library/calcreal.ml"`; its `needs`
  of analysis.ml and transc.ml are the imports of those modules.  The
  bundles are built by `initialize` when the module is loaded, in file
  order.
-/

import Session
import HolLibrary.CalcReal
import SessionLibrary.Analysis
import SessionLibrary.Transc

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.CalcReal

/-- The core theorems calc_real.ml uses. -/
def core1 : HolLibrary.CalcReal.CoreThms1 where
  ABS_N := SessionLibrary.Analysis.«ABS_N»
  ABS_NZ := SessionLibrary.Analysis.«ABS_NZ»
  ADD1 := Session.ADD1
  ADD_ASSOC := Session.ADD_ASSOC
  ADD_CLAUSES := Session.ADD_CLAUSES
  ADD_SYM := Session.ADD_SYM
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  ARITH_SUC := Session.ARITH_SUC
  BETA_THM := Session.BETA_THM
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONJ_SYM := Session.CONJ_SYM
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_OR_THM := Session.EXISTS_OR_THM
  EXISTS_REFL := Session.EXISTS_REFL
  FACT := Session.FACT
  FACT_LE := Session.FACT_LE
  FACT_LT := Session.FACT_LT
  FACT_MONO := Session.FACT_MONO
  LE := Session.LE
  LET_CASES := Session.LET_CASES
  LE_0 := Session.LE_0
  LE_ADD := Session.LE_ADD
  LE_CASES := Session.LE_CASES
  LE_EXISTS := Session.LE_EXISTS
  LE_LT := Session.LE_LT
  LE_MULT2 := Session.LE_MULT2
  LE_SUC := Session.LE_SUC
  LE_SUC_LT := Session.LE_SUC_LT
  LN_1 := SessionLibrary.Transc.«LN_1»
  LT := Session.LT
  LT_0 := Session.LT_0
  LT_CASES := Session.LT_CASES
  LT_EXISTS := Session.LT_EXISTS
  LT_SUC := Session.LT_SUC
  LT_TRANS := Session.LT_TRANS
  MCLAURIN_EXP_LE := SessionLibrary.Transc.«MCLAURIN_EXP_LE»
  MCLAURIN_LN_POS := SessionLibrary.Transc.«MCLAURIN_LN_POS»
  MULT_2 := Session.MULT_2
  MULT_AC := Session.MULT_AC
  MULT_CLAUSES := Session.MULT_CLAUSES
  NOT_LT := Session.NOT_LT
  NOT_SUC := Session.NOT_SUC
  POW_0 := SessionLibrary.Analysis.«POW_0»
  POW_2 := SessionLibrary.Analysis.«POW_2»
  REAL_ABS_0 := Session.REAL_ABS_0
  REAL_ABS_INV := Session.REAL_ABS_INV
  REAL_ABS_MUL := Session.REAL_ABS_MUL
  REAL_ABS_NEG := Session.REAL_ABS_NEG
  REAL_ABS_NUM := Session.REAL_ABS_NUM
  REAL_ABS_NZ := Session.REAL_ABS_NZ
  REAL_ABS_POS := Session.REAL_ABS_POS
  REAL_ABS_POW := Session.REAL_ABS_POW
  REAL_ABS_SUB := Session.REAL_ABS_SUB
  REAL_ABS_SUB_ABS := Session.REAL_ABS_SUB_ABS
  REAL_ABS_TRIANGLE := Session.REAL_ABS_TRIANGLE
  REAL_ADD_AC := Session.REAL_ADD_AC
  REAL_ADD_ASSOC := Session.REAL_ADD_ASSOC
  REAL_ADD_LDISTRIB := Session.REAL_ADD_LDISTRIB
  REAL_ADD_RDISTRIB := Session.REAL_ADD_RDISTRIB
  REAL_ADD_RID := Session.REAL_ADD_RID
  REAL_ADD_SYM := Session.REAL_ADD_SYM
  REAL_DIV_1 := Session.REAL_DIV_1
  REAL_ENTIRE := Session.REAL_ENTIRE
  REAL_EQ_IMP_LE := Session.REAL_EQ_IMP_LE
  REAL_EQ_NEG2 := Session.REAL_EQ_NEG2
  REAL_EXP_ADD := SessionLibrary.Transc.«REAL_EXP_ADD»
  REAL_EXP_BOUND_LEMMA := SessionLibrary.Transc.«REAL_EXP_BOUND_LEMMA»
  REAL_EXP_MONO_LE := SessionLibrary.Transc.«REAL_EXP_MONO_LE»
/-- The core theorems calc_real.ml uses. -/
def core2 : HolLibrary.CalcReal.CoreThms2 where
  REAL_EXP_POS_LE := SessionLibrary.Transc.«REAL_EXP_POS_LE»
  REAL_INV_0 := Session.REAL_INV_0
  REAL_INV_1 := Session.REAL_INV_1
  REAL_INV_EQ_0 := Session.REAL_INV_EQ_0
  REAL_INV_INV := Session.REAL_INV_INV
  REAL_INV_LE_1 := Session.REAL_INV_LE_1
  REAL_INV_MUL := Session.REAL_INV_MUL
  REAL_INV_POS := SessionLibrary.Analysis.«REAL_INV_POS»
  REAL_LET_ADD2 := Session.REAL_LET_ADD2
  REAL_LET_TRANS := Session.REAL_LET_TRANS
  REAL_LE_ADD := Session.REAL_LE_ADD
  REAL_LE_ADD2 := Session.REAL_LE_ADD2
  REAL_LE_ADDL := Session.REAL_LE_ADDL
  REAL_LE_ADDR := Session.REAL_LE_ADDR
  REAL_LE_INV := Session.REAL_LE_INV
  REAL_LE_INV2 := Session.REAL_LE_INV2
  REAL_LE_INV_EQ := Session.REAL_LE_INV_EQ
  REAL_LE_LADD := SessionLibrary.Analysis.«REAL_LE_LADD»
  REAL_LE_LCANCEL_IMP := Session.REAL_LE_LCANCEL_IMP
  REAL_LE_LMUL := Session.REAL_LE_LMUL
  REAL_LE_LMUL_EQ := Session.REAL_LE_LMUL_EQ
  REAL_LE_LMUL_IMP := SessionLibrary.Analysis.«REAL_LE_LMUL_IMP»
  REAL_LE_LT := SessionLibrary.Analysis.«REAL_LE_LT»
  REAL_LE_MUL := SessionLibrary.Analysis.«REAL_LE_MUL»
  REAL_LE_MUL2 := Session.REAL_LE_MUL2
  REAL_LE_POW2 := Session.REAL_LE_POW2
  REAL_LE_RADD := SessionLibrary.Analysis.«REAL_LE_RADD»
  REAL_LE_RCANCEL_IMP := Session.REAL_LE_RCANCEL_IMP
  REAL_LE_REFL := SessionLibrary.Analysis.«REAL_LE_REFL»
  REAL_LE_RMUL := Session.REAL_LE_RMUL
  REAL_LE_SUB_LADD := SessionLibrary.Analysis.«REAL_LE_SUB_LADD»
  REAL_LE_SUB_RADD := SessionLibrary.Analysis.«REAL_LE_SUB_RADD»
  REAL_LE_TRANS := SessionLibrary.Analysis.«REAL_LE_TRANS»
  REAL_LTE_ADD2 := SessionLibrary.Analysis.«REAL_LTE_ADD2»
  REAL_LTE_TRANS := SessionLibrary.Analysis.«REAL_LTE_TRANS»
  REAL_LT_01 := SessionLibrary.Analysis.«REAL_LT_01»
  REAL_LT_ADD2 := SessionLibrary.Analysis.«REAL_LT_ADD2»
  REAL_LT_ADDL := Session.REAL_LT_ADDL
  REAL_LT_ADDR := Session.REAL_LT_ADDR
  REAL_LT_IMP_LE := SessionLibrary.Analysis.«REAL_LT_IMP_LE»
  REAL_LT_IMP_NZ := SessionLibrary.Analysis.«REAL_LT_IMP_NZ»
  REAL_LT_INV2 := Session.REAL_LT_INV2
  REAL_LT_INV_EQ := Session.REAL_LT_INV_EQ
  REAL_LT_LCANCEL_IMP := Session.REAL_LT_LCANCEL_IMP
  REAL_LT_LMUL := Session.REAL_LT_LMUL
  REAL_LT_LMUL_EQ := SessionLibrary.Analysis.«REAL_LT_LMUL_EQ»
  REAL_LT_MUL := Session.REAL_LT_MUL
  REAL_LT_MUL2 := Session.REAL_LT_MUL2
  REAL_LT_NEGTOTAL := SessionLibrary.Analysis.«REAL_LT_NEGTOTAL»
  REAL_LT_POW2 := Session.REAL_LT_POW2
  REAL_LT_RCANCEL_IMP := Session.REAL_LT_RCANCEL_IMP
  REAL_LT_REFL := Session.REAL_LT_REFL
  REAL_LT_RMUL_IMP := SessionLibrary.Analysis.«REAL_LT_RMUL_IMP»
  REAL_LT_SQUARE := Session.REAL_LT_SQUARE
  REAL_LT_SUB_RADD := SessionLibrary.Analysis.«REAL_LT_SUB_RADD»
  REAL_MUL_2 := Session.REAL_MUL_2
  REAL_MUL_AC := Session.REAL_MUL_AC
  REAL_MUL_ASSOC := Session.REAL_MUL_ASSOC
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_LINV := Session.REAL_MUL_LINV
  REAL_MUL_LNEG := Session.REAL_MUL_LNEG
  REAL_MUL_LZERO := SessionLibrary.Analysis.«REAL_MUL_LZERO»
  REAL_MUL_RID := SessionLibrary.Analysis.«REAL_MUL_RID»
  REAL_MUL_RINV := SessionLibrary.Analysis.«REAL_MUL_RINV»
  REAL_MUL_RNEG := Session.REAL_MUL_RNEG
  REAL_MUL_RZERO := SessionLibrary.Analysis.«REAL_MUL_RZERO»
  REAL_MUL_SYM := Session.REAL_MUL_SYM
  REAL_NEG_ADD := SessionLibrary.Analysis.«REAL_NEG_ADD»
  REAL_NEG_NEG := SessionLibrary.Analysis.«REAL_NEG_NEG»
  REAL_NOT_LE := SessionLibrary.Analysis.«REAL_NOT_LE»
/-- The core theorems calc_real.ml uses. -/
def core3 : HolLibrary.CalcReal.CoreThms3 where
  REAL_NOT_LT := SessionLibrary.Analysis.«REAL_NOT_LT»
  REAL_OF_NUM_ADD := Session.REAL_OF_NUM_ADD
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_OF_NUM_LE := Session.REAL_OF_NUM_LE
  REAL_OF_NUM_LT := Session.REAL_OF_NUM_LT
  REAL_OF_NUM_MUL := Session.REAL_OF_NUM_MUL
  REAL_OF_NUM_POW := Session.REAL_OF_NUM_POW
  REAL_OF_NUM_SUC := Session.REAL_OF_NUM_SUC
  REAL_POS := SessionLibrary.Analysis.«REAL_POS»
  REAL_POW_1 := Session.REAL_POW_1
  REAL_POW_1_LE := Session.REAL_POW_1_LE
  REAL_POW_2 := Session.REAL_POW_2
  REAL_POW_ADD := Session.REAL_POW_ADD
  REAL_POW_EQ_0 := Session.REAL_POW_EQ_0
  REAL_POW_INV := Session.REAL_POW_INV
  REAL_POW_LE := Session.REAL_POW_LE
  REAL_POW_LE2 := Session.REAL_POW_LE2
  REAL_POW_LT := Session.REAL_POW_LT
  REAL_POW_LT2 := Session.REAL_POW_LT2
  REAL_POW_MONO := Session.REAL_POW_MONO
  REAL_POW_ONE := Session.REAL_POW_ONE
  REAL_POW_POW := Session.REAL_POW_POW
  REAL_SUB_LDISTRIB := SessionLibrary.Analysis.«REAL_SUB_LDISTRIB»
  REAL_SUB_LZERO := SessionLibrary.Analysis.«REAL_SUB_LZERO»
  REAL_SUB_RDISTRIB := SessionLibrary.Analysis.«REAL_SUB_RDISTRIB»
  REAL_SUB_REFL := SessionLibrary.Analysis.«REAL_SUB_REFL»
  REAL_SUB_RZERO := SessionLibrary.Analysis.«REAL_SUB_RZERO»
  SQRT_POS_LE := Session.SQRT_POS_LE
  SQRT_POS_LT := Session.SQRT_POS_LT
  SQRT_POW2 := Session.SQRT_POW2
  SQRT_POW_2 := Session.SQRT_POW_2
  SUC_INJ := Session.SUC_INJ
  SUM_0 := SessionLibrary.Analysis.«SUM_0»
  SUM_ABS_LE := SessionLibrary.Analysis.«SUM_ABS_LE»
  SUM_BOUND := SessionLibrary.Analysis.«SUM_BOUND»
  SUM_DIFF := SessionLibrary.Analysis.«SUM_DIFF»
  SUM_REINDEX := SessionLibrary.Analysis.«SUM_REINDEX»
  TRUTH := Session.TRUTH
  real_abs := Session.real_abs
  real_div := Session.real_div
  real_ge := Session.real_ge
  real_gt := Session.real_gt
  real_pow := Session.real_pow
  real_sub := Session.real_sub
  sum := SessionLibrary.Analysis.«sum»
/-- The core theorems calc_real.ml uses. -/
def core4 : HolLibrary.CalcReal.CoreThms4 where

/-- What calcreal.ml uses from Session. -/
def deps : HolLibrary.CalcReal.CalcRealDeps where
  prioritize_real := Session.prioritize_real
  ARITH_TAC := Session.ARITH_TAC
  MESON_TAC := Session.MESON_TAC
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH3 t)
  REAL_ARITH_TAC := Session.REAL_ARITH_TAC2
  INDUCT_TAC := Session.INDUCT_TAC
  REAL_INT_REDUCE_CONV := Session.REAL_INT_REDUCE_CONV
  REAL_INT_EQ_CONV := Session.REAL_INT_EQ_CONV
  REAL_LET_IMP t := ExceptT.mk (Session.REAL_LET_IMP t)
  REAL_LE_IMP t := ExceptT.mk (Session.REAL_LE_IMP t)
  num_CONV := Session.num_CONV
  NUM_FACT_CONV := Session.NUM_FACT_CONV
  REAL_RAT_REDUCE_CONV := Session.REAL_RAT_REDUCE_CONV
  REAL_SUM_CONV := SessionLibrary.Analysis.REAL_SUM_CONV
  mk_numeral := Session.mk_numeral
  mk_small_numeral := Session.mk_small_numeral
  mk_realintconst := Session.mk_realintconst
  NUM_SUC_CONV := Session.NUM_SUC_CONV
  NUM_ADD_CONV := Session.NUM_ADD_CONV
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  REAL_INT_NEG_CONV := Session.REAL_INT_NEG_CONV
  REAL_INT_ABS_CONV := Session.REAL_INT_ABS_CONV
  REAL_INT_MUL_CONV := Session.REAL_INT_MUL_CONV
  REAL_INT_SUB_CONV := Session.REAL_INT_SUB_CONV
  REAL_INT_POW_CONV := Session.REAL_INT_POW_CONV
  REAL_INT_LE_CONV := Session.REAL_INT_LE_CONV
  REAL_RAT_LE_CONV := Session.REAL_RAT_LE_CONV
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

/- The bundles, in calcreal.ml order. -/

initialize BLemmas : HolLibrary.CalcReal.Lemmas ←
  ioB "setupLemmas" <|
    (HolLibrary.CalcReal.setupLemmas deps).run

initialize BStepsDown : HolLibrary.CalcReal.StepsDown ←
  ioB "setupStepsDown" <|
    (HolLibrary.CalcReal.setupStepsDown deps BLemmas).run

initialize BStepsInv : HolLibrary.CalcReal.StepsInv ←
  ioB "setupStepsInv" <|
    (HolLibrary.CalcReal.setupStepsInv deps BLemmas).run

initialize BStepsAddMul : HolLibrary.CalcReal.StepsAddMul ←
  ioB "setupStepsAddMul" <|
    (HolLibrary.CalcReal.setupStepsAddMul deps BLemmas).run

initialize BSqrt : HolLibrary.CalcReal.Sqrt ←
  ioB "setupSqrt" <|
    (HolLibrary.CalcReal.setupSqrt deps).run

initialize BStepLemmas : HolLibrary.CalcReal.StepLemmas ←
  ioB "setupStepLemmas" <|
    (HolLibrary.CalcReal.setupStepLemmas deps BLemmas).run

initialize BStepInstances : HolLibrary.CalcReal.StepInstances ←
  ioB "setupStepInstances" <|
    (HolLibrary.CalcReal.setupStepInstances deps BLemmas BStepLemmas).run

initialize BExpandRange : HolLibrary.CalcReal.ExpandRange ←
  ioB "setupExpandRange" <|
    (HolLibrary.CalcReal.setupExpandRange deps).run

initialize BIterExp : HolLibrary.CalcReal.IterExp ←
  ioB "setupIterExp" <|
    (HolLibrary.CalcReal.setupIterExp deps BStepInstances BExpandRange).run

initialize BStepsIter : HolLibrary.CalcReal.StepsIter ←
  ioB "setupStepsIter" <|
    (HolLibrary.CalcReal.setupStepsIter deps BLemmas BIterExp).run

initialize BTaylorExp : HolLibrary.CalcReal.TaylorExp ←
  ioB "setupTaylorExp" <|
    (HolLibrary.CalcReal.setupTaylorExp deps).run

initialize BApprox : HolLibrary.CalcReal.Approx ←
  ioB "setupApprox" <|
    (HolLibrary.CalcReal.setupApprox deps BLemmas BStepsIter BTaylorExp).run

initialize BOverall : HolLibrary.CalcReal.Overall ←
  ioB "setupOverall" <|
    (HolLibrary.CalcReal.setupOverall deps BStepsDown BStepsInv BStepsAddMul BSqrt BExpandRange BApprox).run


-- Lemmas
def REAL_SUB_SUM0 : thm := BLemmas.REAL_SUB_SUM0
def REAL_MUL_RSUM0 : thm := BLemmas.REAL_MUL_RSUM0
def REAL_ABS_LEMMA : thm := BLemmas.REAL_ABS_LEMMA
def REAL_ABS_LEMMA1 : thm := BLemmas.REAL_ABS_LEMMA1
def REAL_ABS_TRIANGLE_LEMMA : thm := BLemmas.REAL_ABS_TRIANGLE_LEMMA
def REAL_MONO_POW2 : thm := BLemmas.REAL_MONO_POW2
def REAL_LE_SUC_POW2 : thm := BLemmas.REAL_LE_SUC_POW2
def REAL_OPPSIGN_LEMMA : thm := BLemmas.REAL_OPPSIGN_LEMMA
def REAL_OPPSIGN : thm := BLemmas.REAL_OPPSIGN
def REAL_NDIV_LEMMA1a : thm := BLemmas.REAL_NDIV_LEMMA1a
def REAL_NDIV_LEMMA1b : thm := BLemmas.REAL_NDIV_LEMMA1b
def REAL_NDIV_LEMMA2 : thm := BLemmas.REAL_NDIV_LEMMA2
def REAL_NDIV_LEMMA3 : thm := BLemmas.REAL_NDIV_LEMMA3

-- StepsDown
def REALCALC_DOWNGRADE : thm := BStepsDown.REALCALC_DOWNGRADE
def REALCALC_INT : thm := BStepsDown.REALCALC_INT
def REALCALC_NEG : thm := BStepsDown.REALCALC_NEG
def REALCALC_ABS : thm := BStepsDown.REALCALC_ABS

-- StepsInv
def REALCALC_INV_LEMMA : thm := BStepsInv.REALCALC_INV_LEMMA
def REALCALC_INV : thm := BStepsInv.REALCALC_INV

-- StepsAddMul
def REALCALC_ADD : thm := BStepsAddMul.REALCALC_ADD
def REALCALC_MUL : thm := BStepsAddMul.REALCALC_MUL

-- Sqrt
def REALCALC_SQRT : thm := BSqrt.REALCALC_SQRT

-- StepLemmas
def STEP_LEMMA1 : thm := BStepLemmas.STEP_LEMMA1
def STEP_LEMMA2 : thm := BStepLemmas.STEP_LEMMA2

-- StepInstances
def STEP_EXP : thm := BStepInstances.STEP_EXP
def STEP_SIN : thm := BStepInstances.STEP_SIN
def STEP_COS : thm := BStepInstances.STEP_COS
def STEP_LN : thm := BStepInstances.STEP_LN

-- ExpandRange
def EXPAND_RANGE_CONV : HolCore.Equal.ioconv := fun t => BExpandRange.EXPAND_RANGE_CONV t

-- IterExp
def STEP_EXP_THM : thm := BIterExp.STEP_EXP_THM
def STEP_EXP_RULE := BIterExp.STEP_EXP_RULE
def STEP_EXP_0 : thm := BIterExp.STEP_EXP_0
def STEP_EXP_1 : thm := BIterExp.STEP_EXP_1
def STEP_EXP_2 : thm := BIterExp.STEP_EXP_2
def STEP_EXP_3 : thm := BIterExp.STEP_EXP_3
def STEP_EXP_4 : thm := BIterExp.STEP_EXP_4
def STEP_EXP_5 : thm := BIterExp.STEP_EXP_5
def STEP_EXP_4_PLUS : thm := BIterExp.STEP_EXP_4_PLUS
def STEPS_EXP_0 : thm := BIterExp.STEPS_EXP_0
def STEPS_EXP_1 : thm := BIterExp.STEPS_EXP_1
def STEPS_EXP_2 : thm := BIterExp.STEPS_EXP_2
def STEPS_EXP_3 : thm := BIterExp.STEPS_EXP_3
def STEPS_EXP_4 : thm := BIterExp.STEPS_EXP_4

-- StepsIter
def STEPS_EXP_LEMMA : thm := BStepsIter.STEPS_EXP_LEMMA
def STEPS_EXP : thm := BStepsIter.STEPS_EXP
def STEPS_LN : thm := BStepsIter.STEPS_LN

-- TaylorExp
def MCLAURIN_EXP_LE1 : thm := BTaylorExp.MCLAURIN_EXP_LE1
def REAL_EXP_15 : thm := BTaylorExp.REAL_EXP_15
def TAYLOR_EXP_WEAK : thm := BTaylorExp.TAYLOR_EXP_WEAK
def REAL_EXP_13 : thm := BTaylorExp.REAL_EXP_13
def TAYLOR_EXP : thm := BTaylorExp.TAYLOR_EXP
def TAYLOR_LN : thm := BTaylorExp.TAYLOR_LN

-- Approx
def APPROX_LEMMA1 : thm := BApprox.APPROX_LEMMA1
def APPROX_EXP : thm := BApprox.APPROX_EXP
def APPROX_LN : thm := BApprox.APPROX_LN
def ELIMINATE_DEF := BApprox.ELIMINATE_DEF

-- Overall
def realcalc_cache := BOverall.realcalc_cache
def REALCALC_CONV := BOverall.REALCALC_CONV
def thm_eval := BOverall.thm_eval
def raw_eval := BOverall.raw_eval
def thm_wrap := BOverall.thm_wrap
def REALCALC_PRECONV := BOverall.REALCALC_PRECONV
def REALCALC_LT : thm := BOverall.REALCALC_LT
def REALCALC_LE : thm := BOverall.REALCALC_LE
def REALCALC_GT : thm := BOverall.REALCALC_GT
def REALCALC_GE : thm := BOverall.REALCALC_GE
def REALCALC_EQ : thm := BOverall.REALCALC_EQ
def realcalc_rel_conv := BOverall.realcalc_rel_conv
def REALCALC_REL_CONV : term → IO (Except String thm) := fun t => (BOverall.REALCALC_REL_CONV t).run

/-- `needs "Library/calcreal.ml"`: already done by importing this module. -/
def ensureCalcReal : IO Unit := pure ()

end SessionLibrary.CalcReal
