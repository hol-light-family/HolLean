/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/transc.ml.                                  -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Transc.lean

  The session half of the transc.ml translation: it supplies
  HolLibrary.Transc's dependencies from Session (and analysis.ml's bundles
  from SessionLibrary.Analysis), and exports every name under its HOL Light
  name.  Importing this module is `needs "Library/transc.ml"`; its
  `needs "Library/analysis.ml"` is the import of SessionLibrary.Analysis.
  Each bundle is built by `initialize` when the module is loaded, in file
  order.

  transc.ml rebinds SYM_CANON_CONV and EXT_CONV (analysis.ml) and
  REAL_DIV_SQRT and SQRT_EVEN_POW2 (core); the
  versions here are transc.ml's, so with `Session` or
  `SessionLibrary.Analysis` also open, qualify them.
-/

import Session
import SessionLibrary.Analysis
import HolLibrary.Transc

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Transc

/-- The core theorems transc.ml uses. -/
def core1 : HolLibrary.Transc.CoreThms1 where
  ADD1 := Session.«ADD1»
  ADD_AC := Session.«ADD_AC»
  ADD_ASSOC := Session.«ADD_ASSOC»
  ADD_CLAUSES := Session.«ADD_CLAUSES»
  ADD_EQ_0 := Session.«ADD_EQ_0»
  ADD_SUB := Session.«ADD_SUB»
  ADD_SYM := Session.«ADD_SYM»
  AND_FORALL_THM := Session.«AND_FORALL_THM»
  ARITH := Session.«ARITH»
  ARITH_EQ := Session.«ARITH_EQ»
  ARITH_EVEN := Session.«ARITH_EVEN»
  BETA_THM := Session.«BETA_THM»
  COND_ID := Session.«COND_ID»
  CONJ_ACI := Session.«CONJ_ACI»
  CONJ_ASSOC := Session.«CONJ_ASSOC»
  CONJ_SYM := Session.«CONJ_SYM»
  CONTRAPOS_THM := Session.«CONTRAPOS_THM»
  DE_MORGAN_THM := Session.«DE_MORGAN_THM»
  DIVISION := Session.«DIVISION»
  DIV_MULT := Session.«DIV_MULT»
  DIV_UNIQ := Session.«DIV_UNIQ»
  EQ_IMP := Session.«EQ_IMP»
  EQ_TRANS := Session.«EQ_TRANS»
  ETA_AX := Session.«ETA_AX»
  EVEN := Session.«EVEN»
  EVEN_ADD := Session.«EVEN_ADD»
  EVEN_DOUBLE := Session.«EVEN_DOUBLE»
  EVEN_EXISTS := Session.«EVEN_EXISTS»
  EVEN_MOD := Session.«EVEN_MOD»
  EVEN_MULT := Session.«EVEN_MULT»
  EXISTS_REFL := Session.«EXISTS_REFL»
  FACT := Session.«FACT»
  FACT_LT := Session.«FACT_LT»
  FINITE_INDUCT_STRONG := Session.«FINITE_INDUCT_STRONG»
  FORALL_AND_THM := Session.«FORALL_AND_THM»
  FORALL_SIMP := Session.«FORALL_SIMP»
  FUN_EQ_THM := Session.«FUN_EQ_THM»
  GE := Session.«GE»
  IMP_CONJ := Session.«IMP_CONJ»
  IMP_IMP := Session.«IMP_IMP»
  IN_INSERT := Session.«IN_INSERT»
  LE := Session.«LE»
  LEFT_ADD_DISTRIB := Session.«LEFT_ADD_DISTRIB»
  LEFT_AND_EXISTS_THM := Session.«LEFT_AND_EXISTS_THM»
  LEFT_FORALL_IMP_THM := Session.«LEFT_FORALL_IMP_THM»
  LEFT_IMP_EXISTS_THM := Session.«LEFT_IMP_EXISTS_THM»
  LET_CASES := Session.«LET_CASES»
  LET_TRANS := Session.«LET_TRANS»
  LE_0 := Session.«LE_0»
  LE_ADD := Session.«LE_ADD»
  LE_ANTISYM := Session.«LE_ANTISYM»
  LE_EXISTS := Session.«LE_EXISTS»
  LE_LT := Session.«LE_LT»
  LE_REFL := Session.«LE_REFL»
  LE_SUC := Session.«LE_SUC»
  LE_SUC_LT := Session.«LE_SUC_LT»
  LE_TRANS := Session.«LE_TRANS»
  LT := Session.«LT»
  LTE_CASES := Session.«LTE_CASES»
  LTE_TRANS := Session.«LTE_TRANS»
  LT_0 := Session.«LT_0»
  LT_ADD_RCANCEL := Session.«LT_ADD_RCANCEL»
  LT_IMP_LE := Session.«LT_IMP_LE»
  LT_LE := Session.«LT_LE»
  LT_NZ := Session.«LT_NZ»
  LT_REFL := Session.«LT_REFL»
  LT_SUC := Session.«LT_SUC»
  LT_TRANS := Session.«LT_TRANS»
  MOD_0 := Session.«MOD_0»
  MOD_MULT_ADD := Session.«MOD_MULT_ADD»
  MONO_AND := Session.«MONO_AND»
  MONO_EXISTS := Session.«MONO_EXISTS»
  MONO_FORALL := Session.«MONO_FORALL»
  MONO_IMP := Session.«MONO_IMP»
  MULT_CLAUSES := Session.«MULT_CLAUSES»
  MULT_SYM := Session.«MULT_SYM»
  NOT_EVEN := Session.«NOT_EVEN»
  NOT_EXISTS_THM := Session.«NOT_EXISTS_THM»
  NOT_FORALL_THM := Session.«NOT_FORALL_THM»
  NOT_IMP := Session.«NOT_IMP»
  NOT_IN_EMPTY := Session.«NOT_IN_EMPTY»
  NOT_LE := Session.«NOT_LE»
  NOT_LT := Session.«NOT_LT»
  NOT_ODD := Session.«NOT_ODD»
  NOT_SUC := Session.«NOT_SUC»
  num_CASES := Session.«num_CASES»
  num_MAX := Session.«num_MAX»
  num_WOP := Session.«num_WOP»
  ODD_DOUBLE := Session.«ODD_DOUBLE»
  ODD_EXISTS := Session.«ODD_EXISTS»
  POW_2_SQRT := Session.«POW_2_SQRT»
  POW_2_SQRT_ABS := Session.«POW_2_SQRT_ABS»
  PRE := Session.«PRE»
  real_abs := Session.«real_abs»
  REAL_ABS_0 := Session.«REAL_ABS_0»
  REAL_ABS_ABS := Session.«REAL_ABS_ABS»
  REAL_ABS_DIV := Session.«REAL_ABS_DIV»
  REAL_ABS_INV := Session.«REAL_ABS_INV»
  REAL_ABS_MUL := Session.«REAL_ABS_MUL»
  REAL_ABS_NEG := Session.«REAL_ABS_NEG»
  REAL_ABS_NUM := Session.«REAL_ABS_NUM»
  REAL_ABS_NZ := Session.«REAL_ABS_NZ»
  REAL_ABS_POS := Session.«REAL_ABS_POS»
  REAL_ABS_POW := Session.«REAL_ABS_POW»
  REAL_ADD2_SUB2 := Session.«REAL_ADD2_SUB2»
  REAL_ADD_AC := Session.«REAL_ADD_AC»
  REAL_ADD_ASSOC := Session.«REAL_ADD_ASSOC»
  REAL_ADD_LDISTRIB := Session.«REAL_ADD_LDISTRIB»
  REAL_ADD_LID := Session.«REAL_ADD_LID»
  REAL_ADD_LINV := Session.«REAL_ADD_LINV»
  REAL_ADD_RDISTRIB := Session.«REAL_ADD_RDISTRIB»
  REAL_ADD_RID := Session.«REAL_ADD_RID»
/-- The core theorems transc.ml uses. -/
def core2 : HolLibrary.Transc.CoreThms2 where
  REAL_ADD_RINV := Session.«REAL_ADD_RINV»
  REAL_ADD_SUB := Session.«REAL_ADD_SUB»
  REAL_ADD_SYM := Session.«REAL_ADD_SYM»
  REAL_DIFFSQ := Session.«REAL_DIFFSQ»
  real_div := Session.«real_div»
  REAL_DIV_1 := Session.«REAL_DIV_1»
  REAL_DIV_LMUL := Session.«REAL_DIV_LMUL»
  REAL_DIV_REFL := Session.«REAL_DIV_REFL»
  REAL_DIV_RMUL := Session.«REAL_DIV_RMUL»
  REAL_DOWN := Session.«REAL_DOWN»
  REAL_DOWN2 := Session.«REAL_DOWN2»
  REAL_ENTIRE := Session.«REAL_ENTIRE»
  REAL_EQ_IMP_LE := Session.«REAL_EQ_IMP_LE»
  REAL_EQ_LDIV_EQ := Session.«REAL_EQ_LDIV_EQ»
  REAL_EQ_MUL_LCANCEL := Session.«REAL_EQ_MUL_LCANCEL»
  REAL_EQ_MUL_RCANCEL := Session.«REAL_EQ_MUL_RCANCEL»
  REAL_EQ_NEG2 := Session.«REAL_EQ_NEG2»
  REAL_EQ_RDIV_EQ := Session.«REAL_EQ_RDIV_EQ»
  REAL_EQ_SUB_LADD := Session.«REAL_EQ_SUB_LADD»
  REAL_EQ_SUB_RADD := Session.«REAL_EQ_SUB_RADD»
  REAL_INV_0 := Session.«REAL_INV_0»
  REAL_INV_1 := Session.«REAL_INV_1»
  REAL_INV_1_LE := Session.«REAL_INV_1_LE»
  REAL_INV_DIV := Session.«REAL_INV_DIV»
  REAL_INV_LE_1 := Session.«REAL_INV_LE_1»
  REAL_INV_MUL := Session.«REAL_INV_MUL»
  REAL_INV_NEG := Session.«REAL_INV_NEG»
  REAL_LET_ADD := Session.«REAL_LET_ADD»
  REAL_LET_TOTAL := Session.«REAL_LET_TOTAL»
  REAL_LET_TRANS := Session.«REAL_LET_TRANS»
  REAL_LE_01 := Session.«REAL_LE_01»
  REAL_LE_ADD2 := Session.«REAL_LE_ADD2»
  REAL_LE_ADDL := Session.«REAL_LE_ADDL»
  REAL_LE_ADDR := Session.«REAL_LE_ADDR»
  REAL_LE_ANTISYM := Session.«REAL_LE_ANTISYM»
  REAL_LE_DIV := Session.«REAL_LE_DIV»
  REAL_LE_INV := Session.«REAL_LE_INV»
  REAL_LE_INV2 := Session.«REAL_LE_INV2»
  REAL_LE_INV_EQ := Session.«REAL_LE_INV_EQ»
  REAL_LE_LCANCEL_IMP := Session.«REAL_LE_LCANCEL_IMP»
  REAL_LE_LDIV_EQ := Session.«REAL_LE_LDIV_EQ»
  REAL_LE_LMUL := Session.«REAL_LE_LMUL»
  REAL_LE_MUL2 := Session.«REAL_LE_MUL2»
  REAL_LE_RDIV_EQ := Session.«REAL_LE_RDIV_EQ»
  REAL_LE_RMUL := Session.«REAL_LE_RMUL»
  REAL_LT_ADDL := Session.«REAL_LT_ADDL»
  REAL_LT_ADDR := Session.«REAL_LT_ADDR»
  REAL_LT_DIV := Session.«REAL_LT_DIV»
  REAL_LT_INV := Session.«REAL_LT_INV»
  REAL_LT_INV2 := Session.«REAL_LT_INV2»
  REAL_LT_INV_EQ := Session.«REAL_LT_INV_EQ»
  REAL_LT_LDIV_EQ := Session.«REAL_LT_LDIV_EQ»
  REAL_LT_MIN := Session.«REAL_LT_MIN»
  REAL_LT_MUL := Session.«REAL_LT_MUL»
  REAL_LT_MUL2 := Session.«REAL_LT_MUL2»
  REAL_LT_RDIV_EQ := Session.«REAL_LT_RDIV_EQ»
  REAL_LT_REFL := Session.«REAL_LT_REFL»
  REAL_LT_TOTAL := Session.«REAL_LT_TOTAL»
  REAL_LT_TRANS := Session.«REAL_LT_TRANS»
  REAL_MUL_2 := Session.«REAL_MUL_2»
  REAL_MUL_AC := Session.«REAL_MUL_AC»
  REAL_MUL_ASSOC := Session.«REAL_MUL_ASSOC»
  REAL_MUL_LID := Session.«REAL_MUL_LID»
  REAL_MUL_LINV := Session.«REAL_MUL_LINV»
  REAL_MUL_LNEG := Session.«REAL_MUL_LNEG»
  REAL_MUL_RNEG := Session.«REAL_MUL_RNEG»
  REAL_MUL_SYM := Session.«REAL_MUL_SYM»
  REAL_OF_NUM_ADD := Session.«REAL_OF_NUM_ADD»
  REAL_OF_NUM_EQ := Session.«REAL_OF_NUM_EQ»
  REAL_OF_NUM_LE := Session.«REAL_OF_NUM_LE»
  REAL_OF_NUM_LT := Session.«REAL_OF_NUM_LT»
  REAL_OF_NUM_MUL := Session.«REAL_OF_NUM_MUL»
  REAL_OF_NUM_SUC := Session.«REAL_OF_NUM_SUC»
  real_pow := Session.«real_pow»
  REAL_POW2_ABS := Session.«REAL_POW2_ABS»
  REAL_POW_1 := Session.«REAL_POW_1»
  REAL_POW_1_LE := Session.«REAL_POW_1_LE»
  REAL_POW_2 := Session.«REAL_POW_2»
  REAL_POW_ADD := Session.«REAL_POW_ADD»
  REAL_POW_DIV := Session.«REAL_POW_DIV»
  REAL_POW_EQ_0 := Session.«REAL_POW_EQ_0»
  REAL_POW_INV := Session.«REAL_POW_INV»
  REAL_POW_LE := Session.«REAL_POW_LE»
  REAL_POW_LE2 := Session.«REAL_POW_LE2»
  REAL_POW_LT := Session.«REAL_POW_LT»
  REAL_POW_MONO := Session.«REAL_POW_MONO»
  REAL_POW_MUL := Session.«REAL_POW_MUL»
  REAL_POW_NEG := Session.«REAL_POW_NEG»
  REAL_POW_ONE := Session.«REAL_POW_ONE»
  REAL_POW_POW := Session.«REAL_POW_POW»
  real_sub := Session.«real_sub»
  RIGHT_AND_EXISTS_THM := Session.«RIGHT_AND_EXISTS_THM»
  RIGHT_FORALL_IMP_THM := Session.«RIGHT_FORALL_IMP_THM»
  RIGHT_IMP_EXISTS_THM := Session.«RIGHT_IMP_EXISTS_THM»
  RIGHT_IMP_FORALL_THM := Session.«RIGHT_IMP_FORALL_THM»
  SELECT_AX := Session.«SELECT_AX»
  SELECT_UNIQUE := Session.«SELECT_UNIQUE»
  SKOLEM_THM := Session.«SKOLEM_THM»
  SQRT_0 := Session.«SQRT_0»
  SQRT_POS_LE := Session.«SQRT_POS_LE»
  SQRT_POS_LT := Session.«SQRT_POS_LT»
  SQRT_POW_2 := Session.«SQRT_POW_2»
  SQRT_UNIQUE := Session.«SQRT_UNIQUE»
  SUB_0 := Session.«SUB_0»
  SUB_ADD := Session.«SUB_ADD»
  SUB_EQ_0 := Session.«SUB_EQ_0»
  SUB_REFL := Session.«SUB_REFL»
  SUB_SUC := Session.«SUB_SUC»
  SUC_INJ := Session.«SUC_INJ»
  SWAP_EXISTS_THM := Session.«SWAP_EXISTS_THM»
  SWAP_FORALL_THM := Session.«SWAP_FORALL_THM»
  UNWIND_THM2 := Session.«UNWIND_THM2»

/-- What transc.ml uses from Session. -/
def deps : HolLibrary.Transc.TranscDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  prioritize_num := do
    match ← HolCore.Kernel.mk_type "num" [] with
    | .ok ty => Session.prioritize_overload ty
    | .error e => throw (IO.userError e)
  prioritize_real := Session.prioritize_real
  basic_rewrites := Session.basic_rewrites
  set_basic_rewrites ths := ExceptT.mk (Session.set_basic_rewrites ths)
  extend_basic_rewrites ths := ExceptT.mk (Session.extend_basic_rewrites ths)
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  ASM_REAL_ARITH_TAC := Session.ASM_REAL_ARITH_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  MESON_TAC := Session.MESON_TAC
  NUM_REDUCE_TAC := Session.NUM_REDUCE_TAC
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH3 t)
  REAL_ARITH_TAC := Session.REAL_ARITH_TAC2
  EXPAND_CASES_CONV := Session.EXPAND_CASES_CONV
  GEN_BETA_CONV := Session.GEN_BETA_CONV
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  REAL_RAT_REDUCE_CONV := Session.REAL_RAT_REDUCE_CONV
  num_CONV := Session.num_CONV
  core1 := core1
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in transc.ml order, after the whole of analysis.ml (the
   import of SessionLibrary.Analysis), so its quotations parse with the
   parser state analysis.ml leaves, as in HOL Light. -/

initialize BPowSer : HolLibrary.Transc.PowSer ←
  ioB "setupPowSer" <|
    (HolLibrary.Transc.setupPowSer deps SessionLibrary.Analysis.BCompat SessionLibrary.Analysis.BNames SessionLibrary.Analysis.BTactics SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BAbs SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BSeqs SessionLibrary.Analysis.BSeqs2 SessionLibrary.Analysis.BSeqLim SessionLibrary.Analysis.BSeries1 SessionLibrary.Analysis.BSeries2).run

initialize BTermDiff : HolLibrary.Transc.TermDiff ←
  ioB "setupTermDiff" <|
    (HolLibrary.Transc.setupTermDiff deps BPowSer SessionLibrary.Analysis.BCompat SessionLibrary.Analysis.BNames SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BAbs SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BSeries1 SessionLibrary.Analysis.BSeries2 SessionLibrary.Analysis.BLims).run

initialize BPowSerEq : HolLibrary.Transc.PowSerEq ←
  ioB "setupPowSerEq" <|
    (HolLibrary.Transc.setupPowSerEq deps BPowSer BTermDiff SessionLibrary.Analysis.BTactics SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BSumConv SessionLibrary.Analysis.BSeqs SessionLibrary.Analysis.BSeries1 SessionLibrary.Analysis.BSeries2 SessionLibrary.Analysis.BLims).run

initialize BDefs : HolLibrary.Transc.Defs ←
  ioB "setupDefs" <|
    (HolLibrary.Transc.setupDefs deps BPowSer BTermDiff SessionLibrary.Analysis.BCompat SessionLibrary.Analysis.BNames SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BAbs SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSeries1 SessionLibrary.Analysis.BSeries2).run

initialize BDiffConv : HolLibrary.Transc.DiffConv ←
  ioB "setupDiffConv" <|
    (HolLibrary.Transc.setupDiffConv deps BDefs SessionLibrary.Analysis.BLims SessionLibrary.Analysis.BDiffs).run

initialize BExp : HolLibrary.Transc.Exp ←
  ioB "setupExp" <|
    (HolLibrary.Transc.setupExp deps BDefs BDiffConv SessionLibrary.Analysis.BNames SessionLibrary.Analysis.BTactics SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BSeries1 SessionLibrary.Analysis.BSeries2 SessionLibrary.Analysis.BLims SessionLibrary.Analysis.BDiffs SessionLibrary.Analysis.BMvt).run

initialize BLnRoot : HolLibrary.Transc.LnRoot ←
  ioB "setupLnRoot" <|
    (HolLibrary.Transc.setupLnRoot deps BDefs BDiffConv BExp SessionLibrary.Analysis.BTactics SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BLims SessionLibrary.Analysis.BDiffs SessionLibrary.Analysis.BInverse).run

initialize BTrig1 : HolLibrary.Transc.Trig1 ←
  ioB "setupTrig1" <|
    (HolLibrary.Transc.setupTrig1 deps BDefs BDiffConv SessionLibrary.Analysis.BNames SessionLibrary.Analysis.BTactics SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BAbs SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BSeries1 SessionLibrary.Analysis.BSeries2 SessionLibrary.Analysis.BLims SessionLibrary.Analysis.BDiffs SessionLibrary.Analysis.BMvt).run

initialize BTrig2 : HolLibrary.Transc.Trig2 ←
  ioB "setupTrig2" <|
    (HolLibrary.Transc.setupTrig2 deps BDefs BTrig1 SessionLibrary.Analysis.BCompat SessionLibrary.Analysis.BTactics SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BLims SessionLibrary.Analysis.BDiffs SessionLibrary.Analysis.BMvt).run

initialize BTan : HolLibrary.Transc.Tan ←
  ioB "setupTan" <|
    (HolLibrary.Transc.setupTan deps BDefs BDiffConv BTrig1 BTrig2 SessionLibrary.Analysis.BCompat SessionLibrary.Analysis.BTactics SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BAbs SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BLims SessionLibrary.Analysis.BDiffs SessionLibrary.Analysis.BMvt).run

initialize BInvTrig : HolLibrary.Transc.InvTrig ←
  ioB "setupInvTrig" <|
    (HolLibrary.Transc.setupInvTrig deps BDefs BTrig1 BTrig2 BTan SessionLibrary.Analysis.BCompat SessionLibrary.Analysis.BTactics SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BAbs SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BLims SessionLibrary.Analysis.BDiffs SessionLibrary.Analysis.BMvt SessionLibrary.Analysis.BInverse).run

initialize BArcSinCos : HolLibrary.Transc.ArcSinCos ←
  ioB "setupArcSinCos" <|
    (HolLibrary.Transc.setupArcSinCos deps BDefs BTrig1 BTrig2 BInvTrig SessionLibrary.Analysis.BCompat SessionLibrary.Analysis.BTactics SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BAbs SessionLibrary.Analysis.BLims SessionLibrary.Analysis.BDiffs SessionLibrary.Analysis.BMvt SessionLibrary.Analysis.BInverse).run

initialize BDivision : HolLibrary.Transc.Division ←
  ioB "setupDivision" <|
    (HolLibrary.Transc.setupDivision deps BArcSinCos SessionLibrary.Analysis.BNames SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2).run

initialize BDivAppend : HolLibrary.Transc.DivAppend ←
  ioB "setupDivAppend" <|
    (HolLibrary.Transc.setupDivAppend deps BArcSinCos BDivision SessionLibrary.Analysis.BNames SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BSeries1).run

initialize BGauge : HolLibrary.Transc.Gauge ←
  ioB "setupGauge" <|
    (HolLibrary.Transc.setupGauge deps BArcSinCos BDivision BDivAppend SessionLibrary.Analysis.BCompat SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BAbs SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BLims).run

initialize BIntegral : HolLibrary.Transc.Integral ←
  ioB "setupIntegral" <|
    (HolLibrary.Transc.setupIntegral deps BDiffConv BArcSinCos BDivision BDivAppend BGauge SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BDiffs).run

initialize BCombine : HolLibrary.Transc.Combine ←
  ioB "setupCombine" <|
    (HolLibrary.Transc.setupCombine deps BArcSinCos BDivision BGauge BIntegral SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BSums).run

initialize BSpike : HolLibrary.Transc.Spike ←
  ioB "setupSpike" <|
    (HolLibrary.Transc.setupSpike deps BArcSinCos BDivision BDivAppend BGauge BIntegral BCombine SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BSeqs SessionLibrary.Analysis.BSeqs2).run

initialize BLimit : HolLibrary.Transc.Limit ←
  ioB "setupLimit" <|
    (HolLibrary.Transc.setupLimit deps BArcSinCos BDivision BDivAppend BGauge BIntegral BCombine BSpike SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BSeqs SessionLibrary.Analysis.BSeqs2 SessionLibrary.Analysis.BSeries1 SessionLibrary.Analysis.BUniform).run

initialize BIntRule : HolLibrary.Transc.IntRule ←
  ioB "setupIntRule" <|
    (HolLibrary.Transc.setupIntRule deps BDiffConv BIntegral BLimit SessionLibrary.Analysis.BCompat).run

initialize BMclaurin : HolLibrary.Transc.Mclaurin ←
  ioB "setupMclaurin" <|
    (HolLibrary.Transc.setupMclaurin deps BDiffConv SessionLibrary.Analysis.BCompat SessionLibrary.Analysis.BNames SessionLibrary.Analysis.BTactics SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BSumConv SessionLibrary.Analysis.BLims SessionLibrary.Analysis.BDiffs SessionLibrary.Analysis.BMvt).run

initialize BMcLnExp : HolLibrary.Transc.McLnExp ←
  ioB "setupMcLnExp" <|
    (HolLibrary.Transc.setupMcLnExp deps BDefs BDiffConv BExp BLnRoot BMclaurin SessionLibrary.Analysis.BNames SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BDiffs).run

initialize BSinCosMcl : HolLibrary.Transc.SinCosMcl ←
  ioB "setupSinCosMcl" <|
    (HolLibrary.Transc.setupSinCosMcl deps BDiffConv BTrig1 BMcLnExp SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BSums).run

initialize BAtnSer : HolLibrary.Transc.AtnSer ←
  ioB "setupAtnSer" <|
    (HolLibrary.Transc.setupAtnSer deps BPowSer BTermDiff BTrig2 BTan BInvTrig SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BSeries1 SessionLibrary.Analysis.BSeries2 SessionLibrary.Analysis.BDiffs SessionLibrary.Analysis.BMvt).run


-- PowSer
def POWDIFF_LEMMA : thm := BPowSer.POWDIFF_LEMMA
def POWDIFF : thm := BPowSer.POWDIFF
def POWREV : thm := BPowSer.POWREV
def POWSER_INSIDEA : thm := BPowSer.POWSER_INSIDEA
def POWSER_INSIDE : thm := BPowSer.POWSER_INSIDE
def diffs : thm := BPowSer.diffs
def DIFFS_NEG : thm := BPowSer.DIFFS_NEG
def DIFFS_LEMMA : thm := BPowSer.DIFFS_LEMMA
def DIFFS_LEMMA2 : thm := BPowSer.DIFFS_LEMMA2
def DIFFS_EQUIV : thm := BPowSer.DIFFS_EQUIV

-- TermDiff
def TERMDIFF_LEMMA1 : thm := BTermDiff.TERMDIFF_LEMMA1
def TERMDIFF_LEMMA2 : thm := BTermDiff.TERMDIFF_LEMMA2
def TERMDIFF_LEMMA3 : thm := BTermDiff.TERMDIFF_LEMMA3
def TERMDIFF_LEMMA4 : thm := BTermDiff.TERMDIFF_LEMMA4
def TERMDIFF_LEMMA5 : thm := BTermDiff.TERMDIFF_LEMMA5
def TERMDIFF : thm := BTermDiff.TERMDIFF

-- PowSerEq
def SEQ_NPOW : thm := BPowSerEq.SEQ_NPOW
def TERMDIFF_CONVERGES : thm := BPowSerEq.TERMDIFF_CONVERGES
def TERMDIFF_STRONG : thm := BPowSerEq.TERMDIFF_STRONG
def POWSER_0 : thm := BPowSerEq.POWSER_0
def POWSER_LIMIT_0 : thm := BPowSerEq.POWSER_LIMIT_0
def POWSER_LIMIT_0_STRONG : thm := BPowSerEq.POWSER_LIMIT_0_STRONG
def POWSER_EQUAL_0 : thm := BPowSerEq.POWSER_EQUAL_0
def POWSER_EQUAL : thm := BPowSerEq.POWSER_EQUAL

-- Defs
def MULT_DIV_2 : thm := BDefs.MULT_DIV_2
def EVEN_DIV2 : thm := BDefs.EVEN_DIV2
def POW_ZERO : thm := BDefs.POW_ZERO
def POW_ZERO_EQ : thm := BDefs.POW_ZERO_EQ
def POW_LT : thm := BDefs.POW_LT
def POW_EQ : thm := BDefs.POW_EQ
def diff_net := BDefs.diff_net
def add_to_diff_net := BDefs.add_to_diff_net
def exp : thm := BDefs.exp
def sin : thm := BDefs.sin
def cos : thm := BDefs.cos
def REAL_EXP_CONVERGES : thm := BDefs.REAL_EXP_CONVERGES
def SIN_CONVERGES : thm := BDefs.SIN_CONVERGES
def COS_CONVERGES : thm := BDefs.COS_CONVERGES
def REAL_EXP_FDIFF : thm := BDefs.REAL_EXP_FDIFF
def SIN_FDIFF : thm := BDefs.SIN_FDIFF
def COS_FDIFF : thm := BDefs.COS_FDIFF
def SIN_NEGLEMMA : thm := BDefs.SIN_NEGLEMMA
def DIFF_EXP : thm := BDefs.DIFF_EXP
def DIFF_SIN : thm := BDefs.DIFF_SIN
def DIFF_COS : thm := BDefs.DIFF_COS

-- DiffConv
def DIFF_CONV : HolCore.Equal.ioconv := fun t => BDiffConv.DIFF_CONV t
def DIFF_COMPOSITE : thm := BDiffConv.DIFF_COMPOSITE
def DIFF_TAC : HolCore.Tactics.tactic := fun g => BDiffConv.DIFF_TAC g
def DIFFERENTIABLE_RULE : term → IO (Except String thm) := fun t => (BDiffConv.DIFFERENTIABLE_RULE t).run
def DIFFERENTIABLE_CONV : HolCore.Equal.ioconv := fun t => BDiffConv.DIFFERENTIABLE_CONV t
def CONTINUOUS_RULE : term → IO (Except String thm) := fun t => (BDiffConv.CONTINUOUS_RULE t).run
def CONTINUOUS_CONV : HolCore.Equal.ioconv := fun t => BDiffConv.CONTINUOUS_CONV t

-- Exp
def REAL_EXP_0 : thm := BExp.REAL_EXP_0
def REAL_EXP_LE_X : thm := BExp.REAL_EXP_LE_X
def REAL_EXP_LT_1 : thm := BExp.REAL_EXP_LT_1
def REAL_EXP_ADD_MUL : thm := BExp.REAL_EXP_ADD_MUL
def REAL_EXP_NEG_MUL : thm := BExp.REAL_EXP_NEG_MUL
def REAL_EXP_NEG_MUL2 : thm := BExp.REAL_EXP_NEG_MUL2
def REAL_EXP_NEG : thm := BExp.REAL_EXP_NEG
def REAL_EXP_ADD : thm := BExp.REAL_EXP_ADD
def REAL_EXP_POS_LE : thm := BExp.REAL_EXP_POS_LE
def REAL_EXP_NZ : thm := BExp.REAL_EXP_NZ
def REAL_EXP_POS_LT : thm := BExp.REAL_EXP_POS_LT
def REAL_EXP_N : thm := BExp.REAL_EXP_N
def REAL_EXP_SUB : thm := BExp.REAL_EXP_SUB
def REAL_EXP_MONO_IMP : thm := BExp.REAL_EXP_MONO_IMP
def REAL_EXP_MONO_LT : thm := BExp.REAL_EXP_MONO_LT
def REAL_EXP_MONO_LE : thm := BExp.REAL_EXP_MONO_LE
def REAL_EXP_INJ : thm := BExp.REAL_EXP_INJ
def REAL_EXP_TOTAL_LEMMA : thm := BExp.REAL_EXP_TOTAL_LEMMA
def REAL_EXP_TOTAL : thm := BExp.REAL_EXP_TOTAL
def REAL_EXP_BOUND_LEMMA : thm := BExp.REAL_EXP_BOUND_LEMMA

-- LnRoot
def ln : thm := BLnRoot.ln
def LN_EXP : thm := BLnRoot.LN_EXP
def REAL_EXP_LN : thm := BLnRoot.REAL_EXP_LN
def EXP_LN : thm := BLnRoot.EXP_LN
def LN_MUL : thm := BLnRoot.LN_MUL
def LN_INJ : thm := BLnRoot.LN_INJ
def LN_1 : thm := BLnRoot.LN_1
def LN_INV : thm := BLnRoot.LN_INV
def LN_DIV : thm := BLnRoot.LN_DIV
def LN_MONO_LT : thm := BLnRoot.LN_MONO_LT
def LN_MONO_LE : thm := BLnRoot.LN_MONO_LE
def LN_POW : thm := BLnRoot.LN_POW
def LN_LE : thm := BLnRoot.LN_LE
def LN_LT_X : thm := BLnRoot.LN_LT_X
def LN_POS : thm := BLnRoot.LN_POS
def LN_POS_LT : thm := BLnRoot.LN_POS_LT
def DIFF_LN : thm := BLnRoot.DIFF_LN
def root : thm := BLnRoot.root
def ROOT_LT_LEMMA : thm := BLnRoot.ROOT_LT_LEMMA
def ROOT_LN : thm := BLnRoot.ROOT_LN
def ROOT_0 : thm := BLnRoot.ROOT_0
def ROOT_1 : thm := BLnRoot.ROOT_1
def ROOT_POW_POS : thm := BLnRoot.ROOT_POW_POS
def POW_ROOT_POS : thm := BLnRoot.POW_ROOT_POS
def ROOT_POS_POSITIVE : thm := BLnRoot.ROOT_POS_POSITIVE
def ROOT_POS_UNIQ : thm := BLnRoot.ROOT_POS_UNIQ
def ROOT_MUL : thm := BLnRoot.ROOT_MUL
def ROOT_INV : thm := BLnRoot.ROOT_INV
def ROOT_DIV : thm := BLnRoot.ROOT_DIV
def ROOT_MONO_LT : thm := BLnRoot.ROOT_MONO_LT
def ROOT_MONO_LE : thm := BLnRoot.ROOT_MONO_LE
def ROOT_MONO_LT_EQ : thm := BLnRoot.ROOT_MONO_LT_EQ
def ROOT_MONO_LE_EQ : thm := BLnRoot.ROOT_MONO_LE_EQ
def ROOT_INJ : thm := BLnRoot.ROOT_INJ
def SQRT_EVEN_POW2 : thm := BLnRoot.SQRT_EVEN_POW2
def REAL_DIV_SQRT : thm := BLnRoot.REAL_DIV_SQRT
def DIFF_SQRT : thm := BLnRoot.DIFF_SQRT

-- Trig1
def SIN_0 : thm := BTrig1.SIN_0
def COS_0 : thm := BTrig1.COS_0
def SIN_CIRCLE : thm := BTrig1.SIN_CIRCLE
def SIN_BOUND : thm := BTrig1.SIN_BOUND
def SIN_BOUNDS : thm := BTrig1.SIN_BOUNDS
def COS_BOUND : thm := BTrig1.COS_BOUND
def COS_BOUNDS : thm := BTrig1.COS_BOUNDS
def SIN_COS_ADD : thm := BTrig1.SIN_COS_ADD
def SIN_COS_NEG : thm := BTrig1.SIN_COS_NEG
def SIN_ADD : thm := BTrig1.SIN_ADD
def COS_ADD : thm := BTrig1.COS_ADD
def SIN_NEG : thm := BTrig1.SIN_NEG
def COS_NEG : thm := BTrig1.COS_NEG
def SIN_DOUBLE : thm := BTrig1.SIN_DOUBLE
def COS_DOUBLE : thm := BTrig1.COS_DOUBLE
def COS_ABS : thm := BTrig1.COS_ABS
def SIN_PAIRED : thm := BTrig1.SIN_PAIRED
def SIN_POS : thm := BTrig1.SIN_POS
def COS_PAIRED : thm := BTrig1.COS_PAIRED
def COS_2 : thm := BTrig1.COS_2
def COS_ISZERO : thm := BTrig1.COS_ISZERO
def pi : thm := BTrig1.pi

-- Trig2
def PI2 : thm := BTrig2.PI2
def COS_PI2 : thm := BTrig2.COS_PI2
def PI2_BOUNDS : thm := BTrig2.PI2_BOUNDS
def PI_POS : thm := BTrig2.PI_POS
def SIN_PI2 : thm := BTrig2.SIN_PI2
def COS_PI : thm := BTrig2.COS_PI
def SIN_PI : thm := BTrig2.SIN_PI
def SIN_COS : thm := BTrig2.SIN_COS
def COS_SIN : thm := BTrig2.COS_SIN
def SIN_PERIODIC_PI : thm := BTrig2.SIN_PERIODIC_PI
def COS_PERIODIC_PI : thm := BTrig2.COS_PERIODIC_PI
def SIN_PERIODIC : thm := BTrig2.SIN_PERIODIC
def COS_PERIODIC : thm := BTrig2.COS_PERIODIC
def COS_NPI : thm := BTrig2.COS_NPI
def SIN_NPI : thm := BTrig2.SIN_NPI
def SIN_POS_PI2 : thm := BTrig2.SIN_POS_PI2
def COS_POS_PI2 : thm := BTrig2.COS_POS_PI2
def COS_POS_PI : thm := BTrig2.COS_POS_PI
def SIN_POS_PI : thm := BTrig2.SIN_POS_PI
def SIN_POS_PI_LE : thm := BTrig2.SIN_POS_PI_LE
def COS_TOTAL : thm := BTrig2.COS_TOTAL
def SIN_TOTAL : thm := BTrig2.SIN_TOTAL
def COS_ZERO_LEMMA : thm := BTrig2.COS_ZERO_LEMMA
def SIN_ZERO_LEMMA : thm := BTrig2.SIN_ZERO_LEMMA
def COS_ZERO : thm := BTrig2.COS_ZERO
def SIN_ZERO : thm := BTrig2.SIN_ZERO
def SIN_ZERO_PI : thm := BTrig2.SIN_ZERO_PI
def COS_ONE_2PI : thm := BTrig2.COS_ONE_2PI

-- Tan
def tan : thm := BTan.tan
def TAN_0 : thm := BTan.TAN_0
def TAN_PI : thm := BTan.TAN_PI
def TAN_NPI : thm := BTan.TAN_NPI
def TAN_NEG : thm := BTan.TAN_NEG
def TAN_PERIODIC : thm := BTan.TAN_PERIODIC
def TAN_PERIODIC_PI : thm := BTan.TAN_PERIODIC_PI
def TAN_PERIODIC_NPI : thm := BTan.TAN_PERIODIC_NPI
def TAN_ADD : thm := BTan.TAN_ADD
def TAN_DOUBLE : thm := BTan.TAN_DOUBLE
def TAN_POS_PI2 : thm := BTan.TAN_POS_PI2
def DIFF_TAN : thm := BTan.DIFF_TAN
def TAN_TOTAL_LEMMA : thm := BTan.TAN_TOTAL_LEMMA
def TAN_TOTAL_POS : thm := BTan.TAN_TOTAL_POS
def TAN_TOTAL : thm := BTan.TAN_TOTAL
def PI2_PI4 : thm := BTan.PI2_PI4
def TAN_PI4 : thm := BTan.TAN_PI4
def TAN_COT : thm := BTan.TAN_COT
def TAN_BOUND_PI2 : thm := BTan.TAN_BOUND_PI2
def TAN_ABS_GE_X : thm := BTan.TAN_ABS_GE_X

-- InvTrig
def asn : thm := BInvTrig.asn
def acs : thm := BInvTrig.acs
def atn : thm := BInvTrig.atn
def ASN : thm := BInvTrig.ASN
def ASN_SIN : thm := BInvTrig.ASN_SIN
def ASN_BOUNDS : thm := BInvTrig.ASN_BOUNDS
def ASN_BOUNDS_LT : thm := BInvTrig.ASN_BOUNDS_LT
def SIN_ASN : thm := BInvTrig.SIN_ASN
def ACS : thm := BInvTrig.ACS
def ACS_COS : thm := BInvTrig.ACS_COS
def ACS_BOUNDS : thm := BInvTrig.ACS_BOUNDS
def ACS_BOUNDS_LT : thm := BInvTrig.ACS_BOUNDS_LT
def COS_ACS : thm := BInvTrig.COS_ACS
def ATN : thm := BInvTrig.ATN
def ATN_TAN : thm := BInvTrig.ATN_TAN
def ATN_BOUNDS : thm := BInvTrig.ATN_BOUNDS
def TAN_ATN : thm := BInvTrig.TAN_ATN
def ATN_0 : thm := BInvTrig.ATN_0
def ATN_1 : thm := BInvTrig.ATN_1
def ATN_NEG : thm := BInvTrig.ATN_NEG
def COS_ATN_NZ : thm := BInvTrig.COS_ATN_NZ
def TAN_SEC : thm := BInvTrig.TAN_SEC
def DIFF_ATN : thm := BInvTrig.DIFF_ATN
def ATN_MONO_LT : thm := BInvTrig.ATN_MONO_LT
def ATN_MONO_LT_EQ : thm := BInvTrig.ATN_MONO_LT_EQ
def ATN_MONO_LE_EQ : thm := BInvTrig.ATN_MONO_LE_EQ
def ATN_INJ : thm := BInvTrig.ATN_INJ
def ATN_POS_LT : thm := BInvTrig.ATN_POS_LT
def ATN_POS_LE : thm := BInvTrig.ATN_POS_LE
def ATN_LT_PI4_POS : thm := BInvTrig.ATN_LT_PI4_POS
def ATN_LT_PI4_NEG : thm := BInvTrig.ATN_LT_PI4_NEG
def ATN_LT_PI4 : thm := BInvTrig.ATN_LT_PI4
def ATN_LE_PI4 : thm := BInvTrig.ATN_LE_PI4

-- ArcSinCos
def COS_SIN_SQRT : thm := BArcSinCos.COS_SIN_SQRT
def COS_ASN_NZ : thm := BArcSinCos.COS_ASN_NZ
def DIFF_ASN_COS : thm := BArcSinCos.DIFF_ASN_COS
def DIFF_ASN : thm := BArcSinCos.DIFF_ASN
def SIN_COS_SQRT : thm := BArcSinCos.SIN_COS_SQRT
def SIN_ACS_NZ : thm := BArcSinCos.SIN_ACS_NZ
def DIFF_ACS_SIN : thm := BArcSinCos.DIFF_ACS_SIN
def DIFF_ACS : thm := BArcSinCos.DIFF_ACS
def CIRCLE_SINCOS : thm := BArcSinCos.CIRCLE_SINCOS
def ACS_MONO_LT : thm := BArcSinCos.ACS_MONO_LT
def LE_MATCH_TAC := BArcSinCos.LE_MATCH_TAC
def LESS_SUC_EQ : thm := BArcSinCos.LESS_SUC_EQ
def LESS_1 : thm := BArcSinCos.LESS_1
def division : thm := BArcSinCos.division
def dsize : thm := BArcSinCos.dsize
def tdiv : thm := BArcSinCos.tdiv
def gauge : thm := BArcSinCos.gauge
def fine : thm := BArcSinCos.fine
def rsum : thm := BArcSinCos.rsum
def defint : thm := BArcSinCos.defint

-- Division
def DIVISION_0_DSIZE : thm := BDivision.DIVISION_0_DSIZE
def DIVISION_1 : thm := BDivision.DIVISION_1
def DIVISION_SINGLE : thm := BDivision.DIVISION_SINGLE
def DIVISION_LHS : thm := BDivision.DIVISION_LHS
def DIVISION_THM : thm := BDivision.DIVISION_THM
def DIVISION_RHS : thm := BDivision.DIVISION_RHS
def DIVISION_LT_GEN : thm := BDivision.DIVISION_LT_GEN
def DIVISION_LT : thm := BDivision.DIVISION_LT
def DIVISION_LE : thm := BDivision.DIVISION_LE
def DIVISION_GT : thm := BDivision.DIVISION_GT
def DIVISION_EQ : thm := BDivision.DIVISION_EQ
def DIVISION_LBOUND : thm := BDivision.DIVISION_LBOUND
def DIVISION_LBOUND_LT : thm := BDivision.DIVISION_LBOUND_LT
def DIVISION_UBOUND : thm := BDivision.DIVISION_UBOUND
def DIVISION_UBOUND_LT : thm := BDivision.DIVISION_UBOUND_LT

-- DivAppend
def DIVISION_APPEND_LEMMA1 : thm := BDivAppend.DIVISION_APPEND_LEMMA1
def DIVISION_APPEND_LEMMA2 : thm := BDivAppend.DIVISION_APPEND_LEMMA2
def DIVISION_APPEND_EXPLICIT : thm := BDivAppend.DIVISION_APPEND_EXPLICIT
def DIVISION_APPEND_STRONG : thm := BDivAppend.DIVISION_APPEND_STRONG
def DIVISION_APPEND : thm := BDivAppend.DIVISION_APPEND
def DIVISION_EXISTS : thm := BDivAppend.DIVISION_EXISTS

-- Gauge
def GAUGE_MIN : thm := BGauge.GAUGE_MIN
def FINE_MIN : thm := BGauge.FINE_MIN
def DINT_UNIQ : thm := BGauge.DINT_UNIQ
def INTEGRAL_NULL : thm := BGauge.INTEGRAL_NULL
def STRADDLE_LEMMA : thm := BGauge.STRADDLE_LEMMA
def FTC1 : thm := BGauge.FTC1

-- Integral
def integrable : thm := BIntegral.integrable
def integral : thm := BIntegral.integral
def INTEGRABLE_DEFINT : thm := BIntegral.INTEGRABLE_DEFINT
def DIVISION_BOUNDS : thm := BIntegral.DIVISION_BOUNDS
def TDIV_BOUNDS : thm := BIntegral.TDIV_BOUNDS
def TDIV_LE : thm := BIntegral.TDIV_LE
def DEFINT_WRONG : thm := BIntegral.DEFINT_WRONG
def DEFINT_INTEGRAL : thm := BIntegral.DEFINT_INTEGRAL
def DEFINT_CONST : thm := BIntegral.DEFINT_CONST
def DEFINT_0 : thm := BIntegral.DEFINT_0
def DEFINT_NEG : thm := BIntegral.DEFINT_NEG
def DEFINT_CMUL : thm := BIntegral.DEFINT_CMUL
def DEFINT_ADD : thm := BIntegral.DEFINT_ADD
def DEFINT_SUB : thm := BIntegral.DEFINT_SUB
def INTEGRAL_LE : thm := BIntegral.INTEGRAL_LE
def DEFINT_LE : thm := BIntegral.DEFINT_LE
def DEFINT_TRIANGLE : thm := BIntegral.DEFINT_TRIANGLE
def DEFINT_EQ : thm := BIntegral.DEFINT_EQ
def INTEGRAL_EQ : thm := BIntegral.INTEGRAL_EQ
def INTEGRATION_BY_PARTS : thm := BIntegral.INTEGRATION_BY_PARTS
def DIVISION_LE_SUC : thm := BIntegral.DIVISION_LE_SUC
def DIVISION_MONO_LE : thm := BIntegral.DIVISION_MONO_LE
def DIVISION_MONO_LE_SUC : thm := BIntegral.DIVISION_MONO_LE_SUC
def DIVISION_INTERMEDIATE : thm := BIntegral.DIVISION_INTERMEDIATE
def DIVISION_DSIZE_LE : thm := BIntegral.DIVISION_DSIZE_LE
def DIVISION_DSIZE_GE : thm := BIntegral.DIVISION_DSIZE_GE
def DIVISION_DSIZE_EQ : thm := BIntegral.DIVISION_DSIZE_EQ
def DIVISION_DSIZE_EQ_ALT : thm := BIntegral.DIVISION_DSIZE_EQ_ALT

-- Combine
def DEFINT_COMBINE : thm := BCombine.DEFINT_COMBINE

-- Spike
def DEFINT_DELTA_LEFT : thm := BSpike.DEFINT_DELTA_LEFT
def DEFINT_DELTA_RIGHT : thm := BSpike.DEFINT_DELTA_RIGHT
def DEFINT_DELTA : thm := BSpike.DEFINT_DELTA
def DEFINT_POINT_SPIKE : thm := BSpike.DEFINT_POINT_SPIKE
def DEFINT_FINITE_SPIKE : thm := BSpike.DEFINT_FINITE_SPIKE
def GAUGE_MIN_FINITE : thm := BSpike.GAUGE_MIN_FINITE
def INTEGRABLE_CAUCHY : thm := BSpike.INTEGRABLE_CAUCHY

-- Limit
def PSUM_DIFFS : thm := BLimit.PSUM_DIFFS
def RSUM_BOUND : thm := BLimit.RSUM_BOUND
def RSUM_DIFF_BOUND : thm := BLimit.RSUM_DIFF_BOUND
def INTEGRABLE_LIMIT : thm := BLimit.INTEGRABLE_LIMIT
def INTEGRABLE_CONST : thm := BLimit.INTEGRABLE_CONST
def INTEGRABLE_COMBINE : thm := BLimit.INTEGRABLE_COMBINE
def INTEGRABLE_POINT_SPIKE : thm := BLimit.INTEGRABLE_POINT_SPIKE
def INTEGRABLE_CONTINUOUS : thm := BLimit.INTEGRABLE_CONTINUOUS
def INTEGRABLE_SPLIT_SIDES : thm := BLimit.INTEGRABLE_SPLIT_SIDES
def INTEGRABLE_SUBINTERVAL_LEFT : thm := BLimit.INTEGRABLE_SUBINTERVAL_LEFT
def INTEGRABLE_SUBINTERVAL_RIGHT : thm := BLimit.INTEGRABLE_SUBINTERVAL_RIGHT
def INTEGRABLE_SUBINTERVAL : thm := BLimit.INTEGRABLE_SUBINTERVAL

-- IntRule
def INTEGRABLE_RULE : term → IO (Except String thm) := fun t => (BIntRule.INTEGRABLE_RULE t).run
def INTEGRABLE_CONV : HolCore.Equal.ioconv := fun t => BIntRule.INTEGRABLE_CONV t
def INTEGRAL_CONST : thm := BIntRule.INTEGRAL_CONST
def INTEGRAL_CMUL : thm := BIntRule.INTEGRAL_CMUL
def INTEGRAL_ADD : thm := BIntRule.INTEGRAL_ADD
def INTEGRAL_SUB : thm := BIntRule.INTEGRAL_SUB
def INTEGRAL_BY_PARTS : thm := BIntRule.INTEGRAL_BY_PARTS
def SYM_CANON_CONV := BIntRule.SYM_CANON_CONV
def EXT_CONV : term → IO (Except String thm) := fun t => (BIntRule.EXT_CONV t).run

-- Mclaurin
def MCLAURIN : thm := BMclaurin.MCLAURIN
def MCLAURIN_NEG : thm := BMclaurin.MCLAURIN_NEG
def MCLAURIN_BI_LE : thm := BMclaurin.MCLAURIN_BI_LE

-- McLnExp
def MCLAURIN_ALL_LT : thm := BMcLnExp.MCLAURIN_ALL_LT
def MCLAURIN_ZERO : thm := BMcLnExp.MCLAURIN_ZERO
def MCLAURIN_ALL_LE : thm := BMcLnExp.MCLAURIN_ALL_LE
def MCLAURIN_EXP_LEMMA : thm := BMcLnExp.MCLAURIN_EXP_LEMMA
def MCLAURIN_EXP_LT : thm := BMcLnExp.MCLAURIN_EXP_LT
def MCLAURIN_EXP_LE : thm := BMcLnExp.MCLAURIN_EXP_LE
def MCLAURIN_LN_POS : thm := BMcLnExp.MCLAURIN_LN_POS
def MCLAURIN_LN_NEG : thm := BMcLnExp.MCLAURIN_LN_NEG

-- SinCosMcl
def MCLAURIN_SIN : thm := BSinCosMcl.MCLAURIN_SIN
def MCLAURIN_COS : thm := BSinCosMcl.MCLAURIN_COS

-- AtnSer
def REAL_ATN_POWSER_SUMMABLE : thm := BAtnSer.REAL_ATN_POWSER_SUMMABLE
def REAL_ATN_POWSER_DIFFS_SUMMABLE : thm := BAtnSer.REAL_ATN_POWSER_DIFFS_SUMMABLE
def REAL_ATN_POWSER_DIFFS_SUM : thm := BAtnSer.REAL_ATN_POWSER_DIFFS_SUM
def REAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE : thm := BAtnSer.REAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE
def REAL_ATN_POWSER_DIFFL : thm := BAtnSer.REAL_ATN_POWSER_DIFFL
def REAL_ATN_POWSER : thm := BAtnSer.REAL_ATN_POWSER
def MCLAURIN_ATN : thm := BAtnSer.MCLAURIN_ATN































/-- `needs "Library/transc.ml"`: already done by importing this module. -/
def ensureTransc : IO Unit := pure ()

end SessionLibrary.Transc
