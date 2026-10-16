/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/calcreal.ml.                          -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/CalcReal.lean

  The `unsafe` half of the calcreal.ml translation: it supplies HolLibrary.CalcReal's
  dependencies from Session and SessionLibrary.Analysis, SessionLibrary.Transc, builds the bundles once, in order,
  and exports every name under its HOL Light name.  `ensureCalcReal` is
  `needs "Library/calcreal.ml"` (which first does `needs "Library/analysis.ml"`, `needs "Library/transc.ml"`).

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/CalcReal.lean by tools/calcrealdiff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.CalcReal
import SessionLibrary.Analysis
import SessionLibrary.Transc

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.CalcReal

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems calc_real.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.CalcReal.CoreThms1 where
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
unsafe def core2 (_ : Unit) : HolLibrary.CalcReal.CoreThms2 where
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
unsafe def core3 (_ : Unit) : HolLibrary.CalcReal.CoreThms3 where
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
unsafe def core4 (_ : Unit) : HolLibrary.CalcReal.CoreThms4 where
-- @@CORE END

/-- What calcreal.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.CalcReal.CalcRealDeps where
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
  core1 := core1 ()
  core2 := core2 ()
  core3 := core3 ()
  core4 := core4 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`, and MATCH_CONV's basic conversions, which HOL
    Light adds loading ind_types.ml), then analysis.ml, transc.ml, which calcreal.ml needs. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      let _ ← Session.MATCH_CONV (HolCore.Kernel.mk_var "p" HolCore.Kernel.bool_ty)
      SessionLibrary.Analysis.ensureAnalysis
      SessionLibrary.Transc.ensureTransc
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.CalcReal: {name}"

/- The bundles, in file order; each forces the one before it. -/

-- @@BUNDLES BEGIN
initialize theLemmas : IO.Ref (Option HolLibrary.CalcReal.Lemmas) ← IO.mkRef none
unsafe def BLemmas : HolLibrary.CalcReal.Lemmas :=
  cached theLemmas "setupLemmas" fun _ => do
    (HolLibrary.CalcReal.setupLemmas (deps ())).run

initialize theStepsDown : IO.Ref (Option HolLibrary.CalcReal.StepsDown) ← IO.mkRef none
unsafe def BStepsDown : HolLibrary.CalcReal.StepsDown :=
  cached theStepsDown "setupStepsDown" fun _ => do
    let _ ← IO.mkRef BLemmas.REAL_SUB_SUM0
    (HolLibrary.CalcReal.setupStepsDown (deps ()) BLemmas).run

initialize theStepsInv : IO.Ref (Option HolLibrary.CalcReal.StepsInv) ← IO.mkRef none
unsafe def BStepsInv : HolLibrary.CalcReal.StepsInv :=
  cached theStepsInv "setupStepsInv" fun _ => do
    let _ ← IO.mkRef BStepsDown.REALCALC_DOWNGRADE
    (HolLibrary.CalcReal.setupStepsInv (deps ()) BLemmas).run

initialize theStepsAddMul : IO.Ref (Option HolLibrary.CalcReal.StepsAddMul) ← IO.mkRef none
unsafe def BStepsAddMul : HolLibrary.CalcReal.StepsAddMul :=
  cached theStepsAddMul "setupStepsAddMul" fun _ => do
    let _ ← IO.mkRef BStepsInv.REALCALC_INV_LEMMA
    (HolLibrary.CalcReal.setupStepsAddMul (deps ()) BLemmas).run

initialize theSqrt : IO.Ref (Option HolLibrary.CalcReal.Sqrt) ← IO.mkRef none
unsafe def BSqrt : HolLibrary.CalcReal.Sqrt :=
  cached theSqrt "setupSqrt" fun _ => do
    let _ ← IO.mkRef BStepsAddMul.REALCALC_ADD
    (HolLibrary.CalcReal.setupSqrt (deps ())).run

initialize theStepLemmas : IO.Ref (Option HolLibrary.CalcReal.StepLemmas) ← IO.mkRef none
unsafe def BStepLemmas : HolLibrary.CalcReal.StepLemmas :=
  cached theStepLemmas "setupStepLemmas" fun _ => do
    let _ ← IO.mkRef BSqrt.REALCALC_SQRT
    (HolLibrary.CalcReal.setupStepLemmas (deps ()) BLemmas).run

initialize theStepInstances : IO.Ref (Option HolLibrary.CalcReal.StepInstances) ← IO.mkRef none
unsafe def BStepInstances : HolLibrary.CalcReal.StepInstances :=
  cached theStepInstances "setupStepInstances" fun _ => do
    let _ ← IO.mkRef BStepLemmas.STEP_LEMMA1
    (HolLibrary.CalcReal.setupStepInstances (deps ()) BLemmas BStepLemmas).run

initialize theExpandRange : IO.Ref (Option HolLibrary.CalcReal.ExpandRange) ← IO.mkRef none
unsafe def BExpandRange : HolLibrary.CalcReal.ExpandRange :=
  cached theExpandRange "setupExpandRange" fun _ => do
    let _ ← IO.mkRef BStepInstances.STEP_EXP
    (HolLibrary.CalcReal.setupExpandRange (deps ())).run

initialize theIterExp : IO.Ref (Option HolLibrary.CalcReal.IterExp) ← IO.mkRef none
unsafe def BIterExp : HolLibrary.CalcReal.IterExp :=
  cached theIterExp "setupIterExp" fun _ => do
    let _ ← IO.mkRef BExpandRange.EXPAND_RANGE_CONV
    (HolLibrary.CalcReal.setupIterExp (deps ()) BStepInstances BExpandRange).run

initialize theStepsIter : IO.Ref (Option HolLibrary.CalcReal.StepsIter) ← IO.mkRef none
unsafe def BStepsIter : HolLibrary.CalcReal.StepsIter :=
  cached theStepsIter "setupStepsIter" fun _ => do
    let _ ← IO.mkRef BIterExp.STEP_EXP_THM
    (HolLibrary.CalcReal.setupStepsIter (deps ()) BLemmas BIterExp).run

initialize theTaylorExp : IO.Ref (Option HolLibrary.CalcReal.TaylorExp) ← IO.mkRef none
unsafe def BTaylorExp : HolLibrary.CalcReal.TaylorExp :=
  cached theTaylorExp "setupTaylorExp" fun _ => do
    let _ ← IO.mkRef BStepsIter.STEPS_EXP_LEMMA
    (HolLibrary.CalcReal.setupTaylorExp (deps ())).run

initialize theApprox : IO.Ref (Option HolLibrary.CalcReal.Approx) ← IO.mkRef none
unsafe def BApprox : HolLibrary.CalcReal.Approx :=
  cached theApprox "setupApprox" fun _ => do
    let _ ← IO.mkRef BTaylorExp.MCLAURIN_EXP_LE1
    (HolLibrary.CalcReal.setupApprox (deps ()) BLemmas BStepsIter BTaylorExp).run

initialize theOverall : IO.Ref (Option HolLibrary.CalcReal.Overall) ← IO.mkRef none
unsafe def BOverall : HolLibrary.CalcReal.Overall :=
  cached theOverall "setupOverall" fun _ => do
    let _ ← IO.mkRef BApprox.APPROX_LEMMA1
    (HolLibrary.CalcReal.setupOverall (deps ()) BStepsDown BStepsInv BStepsAddMul BSqrt BExpandRange BApprox).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Lemmas
unsafe def REAL_SUB_SUM0 : thm := BLemmas.REAL_SUB_SUM0
unsafe def REAL_MUL_RSUM0 : thm := BLemmas.REAL_MUL_RSUM0
unsafe def REAL_ABS_LEMMA : thm := BLemmas.REAL_ABS_LEMMA
unsafe def REAL_ABS_LEMMA1 : thm := BLemmas.REAL_ABS_LEMMA1
unsafe def REAL_ABS_TRIANGLE_LEMMA : thm := BLemmas.REAL_ABS_TRIANGLE_LEMMA
unsafe def REAL_MONO_POW2 : thm := BLemmas.REAL_MONO_POW2
unsafe def REAL_LE_SUC_POW2 : thm := BLemmas.REAL_LE_SUC_POW2
unsafe def REAL_OPPSIGN_LEMMA : thm := BLemmas.REAL_OPPSIGN_LEMMA
unsafe def REAL_OPPSIGN : thm := BLemmas.REAL_OPPSIGN
unsafe def REAL_NDIV_LEMMA1a : thm := BLemmas.REAL_NDIV_LEMMA1a
unsafe def REAL_NDIV_LEMMA1b : thm := BLemmas.REAL_NDIV_LEMMA1b
unsafe def REAL_NDIV_LEMMA2 : thm := BLemmas.REAL_NDIV_LEMMA2
unsafe def REAL_NDIV_LEMMA3 : thm := BLemmas.REAL_NDIV_LEMMA3

-- StepsDown
unsafe def REALCALC_DOWNGRADE : thm := BStepsDown.REALCALC_DOWNGRADE
unsafe def REALCALC_INT : thm := BStepsDown.REALCALC_INT
unsafe def REALCALC_NEG : thm := BStepsDown.REALCALC_NEG
unsafe def REALCALC_ABS : thm := BStepsDown.REALCALC_ABS

-- StepsInv
unsafe def REALCALC_INV_LEMMA : thm := BStepsInv.REALCALC_INV_LEMMA
unsafe def REALCALC_INV : thm := BStepsInv.REALCALC_INV

-- StepsAddMul
unsafe def REALCALC_ADD : thm := BStepsAddMul.REALCALC_ADD
unsafe def REALCALC_MUL : thm := BStepsAddMul.REALCALC_MUL

-- Sqrt
unsafe def REALCALC_SQRT : thm := BSqrt.REALCALC_SQRT

-- StepLemmas
unsafe def STEP_LEMMA1 : thm := BStepLemmas.STEP_LEMMA1
unsafe def STEP_LEMMA2 : thm := BStepLemmas.STEP_LEMMA2

-- StepInstances
unsafe def STEP_EXP : thm := BStepInstances.STEP_EXP
unsafe def STEP_SIN : thm := BStepInstances.STEP_SIN
unsafe def STEP_COS : thm := BStepInstances.STEP_COS
unsafe def STEP_LN : thm := BStepInstances.STEP_LN

-- ExpandRange
unsafe def EXPAND_RANGE_CONV : HolCore.Equal.ioconv := fun t => BExpandRange.EXPAND_RANGE_CONV t

-- IterExp
unsafe def STEP_EXP_THM : thm := BIterExp.STEP_EXP_THM
unsafe def STEP_EXP_RULE := BIterExp.STEP_EXP_RULE
unsafe def STEP_EXP_0 : thm := BIterExp.STEP_EXP_0
unsafe def STEP_EXP_1 : thm := BIterExp.STEP_EXP_1
unsafe def STEP_EXP_2 : thm := BIterExp.STEP_EXP_2
unsafe def STEP_EXP_3 : thm := BIterExp.STEP_EXP_3
unsafe def STEP_EXP_4 : thm := BIterExp.STEP_EXP_4
unsafe def STEP_EXP_5 : thm := BIterExp.STEP_EXP_5
unsafe def STEP_EXP_4_PLUS : thm := BIterExp.STEP_EXP_4_PLUS
unsafe def STEPS_EXP_0 : thm := BIterExp.STEPS_EXP_0
unsafe def STEPS_EXP_1 : thm := BIterExp.STEPS_EXP_1
unsafe def STEPS_EXP_2 : thm := BIterExp.STEPS_EXP_2
unsafe def STEPS_EXP_3 : thm := BIterExp.STEPS_EXP_3
unsafe def STEPS_EXP_4 : thm := BIterExp.STEPS_EXP_4

-- StepsIter
unsafe def STEPS_EXP_LEMMA : thm := BStepsIter.STEPS_EXP_LEMMA
unsafe def STEPS_EXP : thm := BStepsIter.STEPS_EXP
unsafe def STEPS_LN : thm := BStepsIter.STEPS_LN

-- TaylorExp
unsafe def MCLAURIN_EXP_LE1 : thm := BTaylorExp.MCLAURIN_EXP_LE1
unsafe def REAL_EXP_15 : thm := BTaylorExp.REAL_EXP_15
unsafe def TAYLOR_EXP_WEAK : thm := BTaylorExp.TAYLOR_EXP_WEAK
unsafe def REAL_EXP_13 : thm := BTaylorExp.REAL_EXP_13
unsafe def TAYLOR_EXP : thm := BTaylorExp.TAYLOR_EXP
unsafe def TAYLOR_LN : thm := BTaylorExp.TAYLOR_LN

-- Approx
unsafe def APPROX_LEMMA1 : thm := BApprox.APPROX_LEMMA1
unsafe def APPROX_EXP : thm := BApprox.APPROX_EXP
unsafe def APPROX_LN : thm := BApprox.APPROX_LN
unsafe def ELIMINATE_DEF := BApprox.ELIMINATE_DEF

-- Overall
unsafe def realcalc_cache := BOverall.realcalc_cache
unsafe def REALCALC_CONV := BOverall.REALCALC_CONV
unsafe def thm_eval := BOverall.thm_eval
unsafe def raw_eval := BOverall.raw_eval
unsafe def thm_wrap := BOverall.thm_wrap
unsafe def REALCALC_PRECONV := BOverall.REALCALC_PRECONV
unsafe def REALCALC_LT : thm := BOverall.REALCALC_LT
unsafe def REALCALC_LE : thm := BOverall.REALCALC_LE
unsafe def REALCALC_GT : thm := BOverall.REALCALC_GT
unsafe def REALCALC_GE : thm := BOverall.REALCALC_GE
unsafe def REALCALC_EQ : thm := BOverall.REALCALC_EQ
unsafe def realcalc_rel_conv := BOverall.realcalc_rel_conv
unsafe def REALCALC_REL_CONV : term → IO (Except String thm) := fun t => (BOverall.REALCALC_REL_CONV t).run
-- @@EXPORTS END

/-- `needs "Library/calcreal.ml"`: build the bundles, in order. -/
unsafe def ensureCalcReal : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BLemmas.REAL_SUB_SUM0
  let _ ← IO.mkRef BStepsDown.REALCALC_DOWNGRADE
  let _ ← IO.mkRef BStepsInv.REALCALC_INV_LEMMA
  let _ ← IO.mkRef BStepsAddMul.REALCALC_ADD
  let _ ← IO.mkRef BSqrt.REALCALC_SQRT
  let _ ← IO.mkRef BStepLemmas.STEP_LEMMA1
  let _ ← IO.mkRef BStepInstances.STEP_EXP
  let _ ← IO.mkRef BExpandRange.EXPAND_RANGE_CONV
  let _ ← IO.mkRef BIterExp.STEP_EXP_THM
  let _ ← IO.mkRef BStepsIter.STEPS_EXP_LEMMA
  let _ ← IO.mkRef BTaylorExp.MCLAURIN_EXP_LE1
  let _ ← IO.mkRef BApprox.APPROX_LEMMA1
  let _ ← IO.mkRef BOverall.REALCALC_LT
  -- @@ENSURE END
  pure ()

end SessionLibrary.CalcReal
