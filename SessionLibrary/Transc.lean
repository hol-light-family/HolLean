/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/transc.ml.                                  -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Transc.lean

  The `unsafe` half of the transc.ml translation: it supplies
  HolLibrary.Transc's dependencies from Session (and analysis.ml's bundles
  from SessionLibrary.Analysis), builds each bundle once, in file order, and
  exports every name under its HOL Light name.  `ensureTransc` is `needs
  "Library/transc.ml"`.

  transc.ml rebinds SYM_CANON_CONV and EXT_CONV (analysis.ml) and
  DIVISION_0, REAL_DIV_SQRT, SQRT_EVEN_POW2 and SUM_DIFFS (core); the
  versions here are transc.ml's, so with `Session` or
  `SessionLibrary.Analysis` also open, qualify them.

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/Transc.lean by tools/transcdiff/gen_session.py (bookkeeping
  only: field-by-field copies and accessors).
-/

import Session
import SessionLibrary.Analysis
import HolLibrary.Transc

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Transc

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems transc.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.Transc.CoreThms1 where
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
unsafe def core2 (_ : Unit) : HolLibrary.Transc.CoreThms2 where
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
  UNWIND_THM2 := Session.«UNWIND_THM2»-- @@CORE END

/-- What transc.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Transc.TranscDeps where
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
  core1 := core1 ()
  core2 := core2 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library and all of
    analysis.ml are built first: HOL Light has loaded hol_lib.ml before any
    `needs`, and transc.ml begins with `needs "Library/analysis.ml"`, so its
    quotations parse with the parser state analysis.ml leaves. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      SessionLibrary.Analysis.ensureAnalysis
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.Transc: {name}"

/- The bundles, in transc.ml order.  Each forces the one before it, so that
   any bundle builds every earlier one first, as HOL Light's load does. -/

-- @@BUNDLES BEGIN
initialize thePowSer : IO.Ref (Option HolLibrary.Transc.PowSer) ← IO.mkRef none
unsafe def BPowSer : HolLibrary.Transc.PowSer :=
  cached thePowSer "setupPowSer" fun _ => do
    (HolLibrary.Transc.setupPowSer (deps ()) SessionLibrary.Analysis.BCompat SessionLibrary.Analysis.BNames SessionLibrary.Analysis.BTactics SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BAbs SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BSeqs SessionLibrary.Analysis.BSeqs2 SessionLibrary.Analysis.BSeqLim SessionLibrary.Analysis.BSeries1 SessionLibrary.Analysis.BSeries2).run

initialize theTermDiff : IO.Ref (Option HolLibrary.Transc.TermDiff) ← IO.mkRef none
unsafe def BTermDiff : HolLibrary.Transc.TermDiff :=
  cached theTermDiff "setupTermDiff" fun _ => do
    let _ ← IO.mkRef BPowSer.POWDIFF_LEMMA
    (HolLibrary.Transc.setupTermDiff (deps ()) BPowSer SessionLibrary.Analysis.BCompat SessionLibrary.Analysis.BNames SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BAbs SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BSeries1 SessionLibrary.Analysis.BSeries2 SessionLibrary.Analysis.BLims).run

initialize thePowSerEq : IO.Ref (Option HolLibrary.Transc.PowSerEq) ← IO.mkRef none
unsafe def BPowSerEq : HolLibrary.Transc.PowSerEq :=
  cached thePowSerEq "setupPowSerEq" fun _ => do
    let _ ← IO.mkRef BTermDiff.TERMDIFF_LEMMA1
    (HolLibrary.Transc.setupPowSerEq (deps ()) BPowSer BTermDiff SessionLibrary.Analysis.BTactics SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BSumConv SessionLibrary.Analysis.BSeqs SessionLibrary.Analysis.BSeries1 SessionLibrary.Analysis.BSeries2 SessionLibrary.Analysis.BLims).run

initialize theDefs : IO.Ref (Option HolLibrary.Transc.Defs) ← IO.mkRef none
unsafe def BDefs : HolLibrary.Transc.Defs :=
  cached theDefs "setupDefs" fun _ => do
    let _ ← IO.mkRef BPowSerEq.SEQ_NPOW
    (HolLibrary.Transc.setupDefs (deps ()) BPowSer BTermDiff SessionLibrary.Analysis.BCompat SessionLibrary.Analysis.BNames SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BAbs SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSeries1 SessionLibrary.Analysis.BSeries2).run

initialize theDiffConv : IO.Ref (Option HolLibrary.Transc.DiffConv) ← IO.mkRef none
unsafe def BDiffConv : HolLibrary.Transc.DiffConv :=
  cached theDiffConv "setupDiffConv" fun _ => do
    let _ ← IO.mkRef BDefs.MULT_DIV_2
    (HolLibrary.Transc.setupDiffConv (deps ()) BDefs SessionLibrary.Analysis.BLims SessionLibrary.Analysis.BDiffs).run

initialize theExp : IO.Ref (Option HolLibrary.Transc.Exp) ← IO.mkRef none
unsafe def BExp : HolLibrary.Transc.Exp :=
  cached theExp "setupExp" fun _ => do
    let _ ← IO.mkRef BDiffConv.DIFF_CONV
    (HolLibrary.Transc.setupExp (deps ()) BDefs BDiffConv SessionLibrary.Analysis.BNames SessionLibrary.Analysis.BTactics SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BSeries1 SessionLibrary.Analysis.BSeries2 SessionLibrary.Analysis.BLims SessionLibrary.Analysis.BDiffs SessionLibrary.Analysis.BMvt).run

initialize theLnRoot : IO.Ref (Option HolLibrary.Transc.LnRoot) ← IO.mkRef none
unsafe def BLnRoot : HolLibrary.Transc.LnRoot :=
  cached theLnRoot "setupLnRoot" fun _ => do
    let _ ← IO.mkRef BExp.REAL_EXP_0
    (HolLibrary.Transc.setupLnRoot (deps ()) BDefs BDiffConv BExp SessionLibrary.Analysis.BTactics SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BLims SessionLibrary.Analysis.BDiffs SessionLibrary.Analysis.BInverse).run

initialize theTrig1 : IO.Ref (Option HolLibrary.Transc.Trig1) ← IO.mkRef none
unsafe def BTrig1 : HolLibrary.Transc.Trig1 :=
  cached theTrig1 "setupTrig1" fun _ => do
    let _ ← IO.mkRef BLnRoot.ln
    (HolLibrary.Transc.setupTrig1 (deps ()) BDefs BDiffConv SessionLibrary.Analysis.BNames SessionLibrary.Analysis.BTactics SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BAbs SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BSeries1 SessionLibrary.Analysis.BSeries2 SessionLibrary.Analysis.BLims SessionLibrary.Analysis.BDiffs SessionLibrary.Analysis.BMvt).run

initialize theTrig2 : IO.Ref (Option HolLibrary.Transc.Trig2) ← IO.mkRef none
unsafe def BTrig2 : HolLibrary.Transc.Trig2 :=
  cached theTrig2 "setupTrig2" fun _ => do
    let _ ← IO.mkRef BTrig1.SIN_0
    (HolLibrary.Transc.setupTrig2 (deps ()) BDefs BTrig1 SessionLibrary.Analysis.BCompat SessionLibrary.Analysis.BTactics SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BLims SessionLibrary.Analysis.BDiffs SessionLibrary.Analysis.BMvt).run

initialize theTan : IO.Ref (Option HolLibrary.Transc.Tan) ← IO.mkRef none
unsafe def BTan : HolLibrary.Transc.Tan :=
  cached theTan "setupTan" fun _ => do
    let _ ← IO.mkRef BTrig2.PI2
    (HolLibrary.Transc.setupTan (deps ()) BDefs BDiffConv BTrig1 BTrig2 SessionLibrary.Analysis.BCompat SessionLibrary.Analysis.BTactics SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BAbs SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BLims SessionLibrary.Analysis.BDiffs SessionLibrary.Analysis.BMvt).run

initialize theInvTrig : IO.Ref (Option HolLibrary.Transc.InvTrig) ← IO.mkRef none
unsafe def BInvTrig : HolLibrary.Transc.InvTrig :=
  cached theInvTrig "setupInvTrig" fun _ => do
    let _ ← IO.mkRef BTan.tan
    (HolLibrary.Transc.setupInvTrig (deps ()) BDefs BTrig1 BTrig2 BTan SessionLibrary.Analysis.BCompat SessionLibrary.Analysis.BTactics SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BAbs SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BLims SessionLibrary.Analysis.BDiffs SessionLibrary.Analysis.BMvt SessionLibrary.Analysis.BInverse).run

initialize theArcSinCos : IO.Ref (Option HolLibrary.Transc.ArcSinCos) ← IO.mkRef none
unsafe def BArcSinCos : HolLibrary.Transc.ArcSinCos :=
  cached theArcSinCos "setupArcSinCos" fun _ => do
    let _ ← IO.mkRef BInvTrig.asn
    (HolLibrary.Transc.setupArcSinCos (deps ()) BDefs BTrig1 BTrig2 BInvTrig SessionLibrary.Analysis.BCompat SessionLibrary.Analysis.BTactics SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BAbs SessionLibrary.Analysis.BLims SessionLibrary.Analysis.BDiffs SessionLibrary.Analysis.BMvt SessionLibrary.Analysis.BInverse).run

initialize theDivision : IO.Ref (Option HolLibrary.Transc.Division) ← IO.mkRef none
unsafe def BDivision : HolLibrary.Transc.Division :=
  cached theDivision "setupDivision" fun _ => do
    let _ ← IO.mkRef BArcSinCos.COS_SIN_SQRT
    (HolLibrary.Transc.setupDivision (deps ()) BArcSinCos SessionLibrary.Analysis.BNames SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2).run

initialize theDivAppend : IO.Ref (Option HolLibrary.Transc.DivAppend) ← IO.mkRef none
unsafe def BDivAppend : HolLibrary.Transc.DivAppend :=
  cached theDivAppend "setupDivAppend" fun _ => do
    let _ ← IO.mkRef BDivision.DIVISION_0
    (HolLibrary.Transc.setupDivAppend (deps ()) BArcSinCos BDivision SessionLibrary.Analysis.BNames SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BSeries1).run

initialize theGauge : IO.Ref (Option HolLibrary.Transc.Gauge) ← IO.mkRef none
unsafe def BGauge : HolLibrary.Transc.Gauge :=
  cached theGauge "setupGauge" fun _ => do
    let _ ← IO.mkRef BDivAppend.DIVISION_APPEND_LEMMA1
    (HolLibrary.Transc.setupGauge (deps ()) BArcSinCos BDivision BDivAppend SessionLibrary.Analysis.BCompat SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BAbs SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BLims).run

initialize theIntegral : IO.Ref (Option HolLibrary.Transc.Integral) ← IO.mkRef none
unsafe def BIntegral : HolLibrary.Transc.Integral :=
  cached theIntegral "setupIntegral" fun _ => do
    let _ ← IO.mkRef BGauge.GAUGE_MIN
    (HolLibrary.Transc.setupIntegral (deps ()) BDiffConv BArcSinCos BDivision BDivAppend BGauge SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BDiffs).run

initialize theCombine : IO.Ref (Option HolLibrary.Transc.Combine) ← IO.mkRef none
unsafe def BCombine : HolLibrary.Transc.Combine :=
  cached theCombine "setupCombine" fun _ => do
    let _ ← IO.mkRef BIntegral.integrable
    (HolLibrary.Transc.setupCombine (deps ()) BArcSinCos BDivision BGauge BIntegral SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BSums).run

initialize theSpike : IO.Ref (Option HolLibrary.Transc.Spike) ← IO.mkRef none
unsafe def BSpike : HolLibrary.Transc.Spike :=
  cached theSpike "setupSpike" fun _ => do
    let _ ← IO.mkRef BCombine.DEFINT_COMBINE
    (HolLibrary.Transc.setupSpike (deps ()) BArcSinCos BDivision BDivAppend BGauge BIntegral BCombine SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BSeqs SessionLibrary.Analysis.BSeqs2).run

initialize theLimit : IO.Ref (Option HolLibrary.Transc.Limit) ← IO.mkRef none
unsafe def BLimit : HolLibrary.Transc.Limit :=
  cached theLimit "setupLimit" fun _ => do
    let _ ← IO.mkRef BSpike.DEFINT_DELTA_LEFT
    (HolLibrary.Transc.setupLimit (deps ()) BArcSinCos BDivision BDivAppend BGauge BIntegral BCombine BSpike SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BSeqs SessionLibrary.Analysis.BSeqs2 SessionLibrary.Analysis.BSeries1 SessionLibrary.Analysis.BUniform).run

initialize theIntRule : IO.Ref (Option HolLibrary.Transc.IntRule) ← IO.mkRef none
unsafe def BIntRule : HolLibrary.Transc.IntRule :=
  cached theIntRule "setupIntRule" fun _ => do
    let _ ← IO.mkRef BLimit.SUM_DIFFS
    (HolLibrary.Transc.setupIntRule (deps ()) BDiffConv BIntegral BLimit SessionLibrary.Analysis.BCompat).run

initialize theMclaurin : IO.Ref (Option HolLibrary.Transc.Mclaurin) ← IO.mkRef none
unsafe def BMclaurin : HolLibrary.Transc.Mclaurin :=
  cached theMclaurin "setupMclaurin" fun _ => do
    let _ ← IO.mkRef BIntRule.INTEGRABLE_RULE
    (HolLibrary.Transc.setupMclaurin (deps ()) BDiffConv SessionLibrary.Analysis.BCompat SessionLibrary.Analysis.BNames SessionLibrary.Analysis.BTactics SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BSumConv SessionLibrary.Analysis.BLims SessionLibrary.Analysis.BDiffs SessionLibrary.Analysis.BMvt).run

initialize theMcLnExp : IO.Ref (Option HolLibrary.Transc.McLnExp) ← IO.mkRef none
unsafe def BMcLnExp : HolLibrary.Transc.McLnExp :=
  cached theMcLnExp "setupMcLnExp" fun _ => do
    let _ ← IO.mkRef BMclaurin.MCLAURIN
    (HolLibrary.Transc.setupMcLnExp (deps ()) BDefs BDiffConv BExp BLnRoot BMclaurin SessionLibrary.Analysis.BNames SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BDiffs).run

initialize theSinCosMcl : IO.Ref (Option HolLibrary.Transc.SinCosMcl) ← IO.mkRef none
unsafe def BSinCosMcl : HolLibrary.Transc.SinCosMcl :=
  cached theSinCosMcl "setupSinCosMcl" fun _ => do
    let _ ← IO.mkRef BMcLnExp.MCLAURIN_ALL_LT
    (HolLibrary.Transc.setupSinCosMcl (deps ()) BDiffConv BTrig1 BMcLnExp SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BSums).run

initialize theAtnSer : IO.Ref (Option HolLibrary.Transc.AtnSer) ← IO.mkRef none
unsafe def BAtnSer : HolLibrary.Transc.AtnSer :=
  cached theAtnSer "setupAtnSer" fun _ => do
    let _ ← IO.mkRef BSinCosMcl.MCLAURIN_SIN
    (HolLibrary.Transc.setupAtnSer (deps ()) BPowSer BTermDiff BTrig2 BTan BInvTrig SessionLibrary.Analysis.BReals1 SessionLibrary.Analysis.BReals2 SessionLibrary.Analysis.BReals3 SessionLibrary.Analysis.BPow SessionLibrary.Analysis.BSums SessionLibrary.Analysis.BSeries1 SessionLibrary.Analysis.BSeries2 SessionLibrary.Analysis.BDiffs SessionLibrary.Analysis.BMvt).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- PowSer
unsafe def POWDIFF_LEMMA : thm := BPowSer.POWDIFF_LEMMA
unsafe def POWDIFF : thm := BPowSer.POWDIFF
unsafe def POWREV : thm := BPowSer.POWREV
unsafe def POWSER_INSIDEA : thm := BPowSer.POWSER_INSIDEA
unsafe def POWSER_INSIDE : thm := BPowSer.POWSER_INSIDE
unsafe def diffs : thm := BPowSer.diffs
unsafe def DIFFS_NEG : thm := BPowSer.DIFFS_NEG
unsafe def DIFFS_LEMMA : thm := BPowSer.DIFFS_LEMMA
unsafe def DIFFS_LEMMA2 : thm := BPowSer.DIFFS_LEMMA2
unsafe def DIFFS_EQUIV : thm := BPowSer.DIFFS_EQUIV

-- TermDiff
unsafe def TERMDIFF_LEMMA1 : thm := BTermDiff.TERMDIFF_LEMMA1
unsafe def TERMDIFF_LEMMA2 : thm := BTermDiff.TERMDIFF_LEMMA2
unsafe def TERMDIFF_LEMMA3 : thm := BTermDiff.TERMDIFF_LEMMA3
unsafe def TERMDIFF_LEMMA4 : thm := BTermDiff.TERMDIFF_LEMMA4
unsafe def TERMDIFF_LEMMA5 : thm := BTermDiff.TERMDIFF_LEMMA5
unsafe def TERMDIFF : thm := BTermDiff.TERMDIFF

-- PowSerEq
unsafe def SEQ_NPOW : thm := BPowSerEq.SEQ_NPOW
unsafe def TERMDIFF_CONVERGES : thm := BPowSerEq.TERMDIFF_CONVERGES
unsafe def TERMDIFF_STRONG : thm := BPowSerEq.TERMDIFF_STRONG
unsafe def POWSER_0 : thm := BPowSerEq.POWSER_0
unsafe def POWSER_LIMIT_0 : thm := BPowSerEq.POWSER_LIMIT_0
unsafe def POWSER_LIMIT_0_STRONG : thm := BPowSerEq.POWSER_LIMIT_0_STRONG
unsafe def POWSER_EQUAL_0 : thm := BPowSerEq.POWSER_EQUAL_0
unsafe def POWSER_EQUAL : thm := BPowSerEq.POWSER_EQUAL

-- Defs
unsafe def MULT_DIV_2 : thm := BDefs.MULT_DIV_2
unsafe def EVEN_DIV2 : thm := BDefs.EVEN_DIV2
unsafe def POW_ZERO : thm := BDefs.POW_ZERO
unsafe def POW_ZERO_EQ : thm := BDefs.POW_ZERO_EQ
unsafe def POW_LT : thm := BDefs.POW_LT
unsafe def POW_EQ : thm := BDefs.POW_EQ
unsafe def diff_net := BDefs.diff_net
unsafe def add_to_diff_net := BDefs.add_to_diff_net
unsafe def exp : thm := BDefs.exp
unsafe def sin : thm := BDefs.sin
unsafe def cos : thm := BDefs.cos
unsafe def REAL_EXP_CONVERGES : thm := BDefs.REAL_EXP_CONVERGES
unsafe def SIN_CONVERGES : thm := BDefs.SIN_CONVERGES
unsafe def COS_CONVERGES : thm := BDefs.COS_CONVERGES
unsafe def REAL_EXP_FDIFF : thm := BDefs.REAL_EXP_FDIFF
unsafe def SIN_FDIFF : thm := BDefs.SIN_FDIFF
unsafe def COS_FDIFF : thm := BDefs.COS_FDIFF
unsafe def SIN_NEGLEMMA : thm := BDefs.SIN_NEGLEMMA
unsafe def DIFF_EXP : thm := BDefs.DIFF_EXP
unsafe def DIFF_SIN : thm := BDefs.DIFF_SIN
unsafe def DIFF_COS : thm := BDefs.DIFF_COS

-- DiffConv
unsafe def DIFF_CONV : HolCore.Equal.ioconv := fun t => BDiffConv.DIFF_CONV t
unsafe def DIFF_COMPOSITE : thm := BDiffConv.DIFF_COMPOSITE
unsafe def DIFF_TAC : HolCore.Tactics.tactic := fun g => BDiffConv.DIFF_TAC g
unsafe def DIFFERENTIABLE_RULE : term → IO (Except String thm) := fun t => (BDiffConv.DIFFERENTIABLE_RULE t).run
unsafe def DIFFERENTIABLE_CONV : HolCore.Equal.ioconv := fun t => BDiffConv.DIFFERENTIABLE_CONV t
unsafe def CONTINUOUS_RULE : term → IO (Except String thm) := fun t => (BDiffConv.CONTINUOUS_RULE t).run
unsafe def CONTINUOUS_CONV : HolCore.Equal.ioconv := fun t => BDiffConv.CONTINUOUS_CONV t

-- Exp
unsafe def REAL_EXP_0 : thm := BExp.REAL_EXP_0
unsafe def REAL_EXP_LE_X : thm := BExp.REAL_EXP_LE_X
unsafe def REAL_EXP_LT_1 : thm := BExp.REAL_EXP_LT_1
unsafe def REAL_EXP_ADD_MUL : thm := BExp.REAL_EXP_ADD_MUL
unsafe def REAL_EXP_NEG_MUL : thm := BExp.REAL_EXP_NEG_MUL
unsafe def REAL_EXP_NEG_MUL2 : thm := BExp.REAL_EXP_NEG_MUL2
unsafe def REAL_EXP_NEG : thm := BExp.REAL_EXP_NEG
unsafe def REAL_EXP_ADD : thm := BExp.REAL_EXP_ADD
unsafe def REAL_EXP_POS_LE : thm := BExp.REAL_EXP_POS_LE
unsafe def REAL_EXP_NZ : thm := BExp.REAL_EXP_NZ
unsafe def REAL_EXP_POS_LT : thm := BExp.REAL_EXP_POS_LT
unsafe def REAL_EXP_N : thm := BExp.REAL_EXP_N
unsafe def REAL_EXP_SUB : thm := BExp.REAL_EXP_SUB
unsafe def REAL_EXP_MONO_IMP : thm := BExp.REAL_EXP_MONO_IMP
unsafe def REAL_EXP_MONO_LT : thm := BExp.REAL_EXP_MONO_LT
unsafe def REAL_EXP_MONO_LE : thm := BExp.REAL_EXP_MONO_LE
unsafe def REAL_EXP_INJ : thm := BExp.REAL_EXP_INJ
unsafe def REAL_EXP_TOTAL_LEMMA : thm := BExp.REAL_EXP_TOTAL_LEMMA
unsafe def REAL_EXP_TOTAL : thm := BExp.REAL_EXP_TOTAL
unsafe def REAL_EXP_BOUND_LEMMA : thm := BExp.REAL_EXP_BOUND_LEMMA

-- LnRoot
unsafe def ln : thm := BLnRoot.ln
unsafe def LN_EXP : thm := BLnRoot.LN_EXP
unsafe def REAL_EXP_LN : thm := BLnRoot.REAL_EXP_LN
unsafe def EXP_LN : thm := BLnRoot.EXP_LN
unsafe def LN_MUL : thm := BLnRoot.LN_MUL
unsafe def LN_INJ : thm := BLnRoot.LN_INJ
unsafe def LN_1 : thm := BLnRoot.LN_1
unsafe def LN_INV : thm := BLnRoot.LN_INV
unsafe def LN_DIV : thm := BLnRoot.LN_DIV
unsafe def LN_MONO_LT : thm := BLnRoot.LN_MONO_LT
unsafe def LN_MONO_LE : thm := BLnRoot.LN_MONO_LE
unsafe def LN_POW : thm := BLnRoot.LN_POW
unsafe def LN_LE : thm := BLnRoot.LN_LE
unsafe def LN_LT_X : thm := BLnRoot.LN_LT_X
unsafe def LN_POS : thm := BLnRoot.LN_POS
unsafe def LN_POS_LT : thm := BLnRoot.LN_POS_LT
unsafe def DIFF_LN : thm := BLnRoot.DIFF_LN
unsafe def root : thm := BLnRoot.root
unsafe def ROOT_LT_LEMMA : thm := BLnRoot.ROOT_LT_LEMMA
unsafe def ROOT_LN : thm := BLnRoot.ROOT_LN
unsafe def ROOT_0 : thm := BLnRoot.ROOT_0
unsafe def ROOT_1 : thm := BLnRoot.ROOT_1
unsafe def ROOT_POW_POS : thm := BLnRoot.ROOT_POW_POS
unsafe def POW_ROOT_POS : thm := BLnRoot.POW_ROOT_POS
unsafe def ROOT_POS_POSITIVE : thm := BLnRoot.ROOT_POS_POSITIVE
unsafe def ROOT_POS_UNIQ : thm := BLnRoot.ROOT_POS_UNIQ
unsafe def ROOT_MUL : thm := BLnRoot.ROOT_MUL
unsafe def ROOT_INV : thm := BLnRoot.ROOT_INV
unsafe def ROOT_DIV : thm := BLnRoot.ROOT_DIV
unsafe def ROOT_MONO_LT : thm := BLnRoot.ROOT_MONO_LT
unsafe def ROOT_MONO_LE : thm := BLnRoot.ROOT_MONO_LE
unsafe def ROOT_MONO_LT_EQ : thm := BLnRoot.ROOT_MONO_LT_EQ
unsafe def ROOT_MONO_LE_EQ : thm := BLnRoot.ROOT_MONO_LE_EQ
unsafe def ROOT_INJ : thm := BLnRoot.ROOT_INJ
unsafe def SQRT_EVEN_POW2 : thm := BLnRoot.SQRT_EVEN_POW2
unsafe def REAL_DIV_SQRT : thm := BLnRoot.REAL_DIV_SQRT
unsafe def DIFF_SQRT : thm := BLnRoot.DIFF_SQRT

-- Trig1
unsafe def SIN_0 : thm := BTrig1.SIN_0
unsafe def COS_0 : thm := BTrig1.COS_0
unsafe def SIN_CIRCLE : thm := BTrig1.SIN_CIRCLE
unsafe def SIN_BOUND : thm := BTrig1.SIN_BOUND
unsafe def SIN_BOUNDS : thm := BTrig1.SIN_BOUNDS
unsafe def COS_BOUND : thm := BTrig1.COS_BOUND
unsafe def COS_BOUNDS : thm := BTrig1.COS_BOUNDS
unsafe def SIN_COS_ADD : thm := BTrig1.SIN_COS_ADD
unsafe def SIN_COS_NEG : thm := BTrig1.SIN_COS_NEG
unsafe def SIN_ADD : thm := BTrig1.SIN_ADD
unsafe def COS_ADD : thm := BTrig1.COS_ADD
unsafe def SIN_NEG : thm := BTrig1.SIN_NEG
unsafe def COS_NEG : thm := BTrig1.COS_NEG
unsafe def SIN_DOUBLE : thm := BTrig1.SIN_DOUBLE
unsafe def COS_DOUBLE : thm := BTrig1.COS_DOUBLE
unsafe def COS_ABS : thm := BTrig1.COS_ABS
unsafe def SIN_PAIRED : thm := BTrig1.SIN_PAIRED
unsafe def SIN_POS : thm := BTrig1.SIN_POS
unsafe def COS_PAIRED : thm := BTrig1.COS_PAIRED
unsafe def COS_2 : thm := BTrig1.COS_2
unsafe def COS_ISZERO : thm := BTrig1.COS_ISZERO
unsafe def pi : thm := BTrig1.pi

-- Trig2
unsafe def PI2 : thm := BTrig2.PI2
unsafe def COS_PI2 : thm := BTrig2.COS_PI2
unsafe def PI2_BOUNDS : thm := BTrig2.PI2_BOUNDS
unsafe def PI_POS : thm := BTrig2.PI_POS
unsafe def SIN_PI2 : thm := BTrig2.SIN_PI2
unsafe def COS_PI : thm := BTrig2.COS_PI
unsafe def SIN_PI : thm := BTrig2.SIN_PI
unsafe def SIN_COS : thm := BTrig2.SIN_COS
unsafe def COS_SIN : thm := BTrig2.COS_SIN
unsafe def SIN_PERIODIC_PI : thm := BTrig2.SIN_PERIODIC_PI
unsafe def COS_PERIODIC_PI : thm := BTrig2.COS_PERIODIC_PI
unsafe def SIN_PERIODIC : thm := BTrig2.SIN_PERIODIC
unsafe def COS_PERIODIC : thm := BTrig2.COS_PERIODIC
unsafe def COS_NPI : thm := BTrig2.COS_NPI
unsafe def SIN_NPI : thm := BTrig2.SIN_NPI
unsafe def SIN_POS_PI2 : thm := BTrig2.SIN_POS_PI2
unsafe def COS_POS_PI2 : thm := BTrig2.COS_POS_PI2
unsafe def COS_POS_PI : thm := BTrig2.COS_POS_PI
unsafe def SIN_POS_PI : thm := BTrig2.SIN_POS_PI
unsafe def SIN_POS_PI_LE : thm := BTrig2.SIN_POS_PI_LE
unsafe def COS_TOTAL : thm := BTrig2.COS_TOTAL
unsafe def SIN_TOTAL : thm := BTrig2.SIN_TOTAL
unsafe def COS_ZERO_LEMMA : thm := BTrig2.COS_ZERO_LEMMA
unsafe def SIN_ZERO_LEMMA : thm := BTrig2.SIN_ZERO_LEMMA
unsafe def COS_ZERO : thm := BTrig2.COS_ZERO
unsafe def SIN_ZERO : thm := BTrig2.SIN_ZERO
unsafe def SIN_ZERO_PI : thm := BTrig2.SIN_ZERO_PI
unsafe def COS_ONE_2PI : thm := BTrig2.COS_ONE_2PI

-- Tan
unsafe def tan : thm := BTan.tan
unsafe def TAN_0 : thm := BTan.TAN_0
unsafe def TAN_PI : thm := BTan.TAN_PI
unsafe def TAN_NPI : thm := BTan.TAN_NPI
unsafe def TAN_NEG : thm := BTan.TAN_NEG
unsafe def TAN_PERIODIC : thm := BTan.TAN_PERIODIC
unsafe def TAN_PERIODIC_PI : thm := BTan.TAN_PERIODIC_PI
unsafe def TAN_PERIODIC_NPI : thm := BTan.TAN_PERIODIC_NPI
unsafe def TAN_ADD : thm := BTan.TAN_ADD
unsafe def TAN_DOUBLE : thm := BTan.TAN_DOUBLE
unsafe def TAN_POS_PI2 : thm := BTan.TAN_POS_PI2
unsafe def DIFF_TAN : thm := BTan.DIFF_TAN
unsafe def TAN_TOTAL_LEMMA : thm := BTan.TAN_TOTAL_LEMMA
unsafe def TAN_TOTAL_POS : thm := BTan.TAN_TOTAL_POS
unsafe def TAN_TOTAL : thm := BTan.TAN_TOTAL
unsafe def PI2_PI4 : thm := BTan.PI2_PI4
unsafe def TAN_PI4 : thm := BTan.TAN_PI4
unsafe def TAN_COT : thm := BTan.TAN_COT
unsafe def TAN_BOUND_PI2 : thm := BTan.TAN_BOUND_PI2
unsafe def TAN_ABS_GE_X : thm := BTan.TAN_ABS_GE_X

-- InvTrig
unsafe def asn : thm := BInvTrig.asn
unsafe def acs : thm := BInvTrig.acs
unsafe def atn : thm := BInvTrig.atn
unsafe def ASN : thm := BInvTrig.ASN
unsafe def ASN_SIN : thm := BInvTrig.ASN_SIN
unsafe def ASN_BOUNDS : thm := BInvTrig.ASN_BOUNDS
unsafe def ASN_BOUNDS_LT : thm := BInvTrig.ASN_BOUNDS_LT
unsafe def SIN_ASN : thm := BInvTrig.SIN_ASN
unsafe def ACS : thm := BInvTrig.ACS
unsafe def ACS_COS : thm := BInvTrig.ACS_COS
unsafe def ACS_BOUNDS : thm := BInvTrig.ACS_BOUNDS
unsafe def ACS_BOUNDS_LT : thm := BInvTrig.ACS_BOUNDS_LT
unsafe def COS_ACS : thm := BInvTrig.COS_ACS
unsafe def ATN : thm := BInvTrig.ATN
unsafe def ATN_TAN : thm := BInvTrig.ATN_TAN
unsafe def ATN_BOUNDS : thm := BInvTrig.ATN_BOUNDS
unsafe def TAN_ATN : thm := BInvTrig.TAN_ATN
unsafe def ATN_0 : thm := BInvTrig.ATN_0
unsafe def ATN_1 : thm := BInvTrig.ATN_1
unsafe def ATN_NEG : thm := BInvTrig.ATN_NEG
unsafe def COS_ATN_NZ : thm := BInvTrig.COS_ATN_NZ
unsafe def TAN_SEC : thm := BInvTrig.TAN_SEC
unsafe def DIFF_ATN : thm := BInvTrig.DIFF_ATN
unsafe def ATN_MONO_LT : thm := BInvTrig.ATN_MONO_LT
unsafe def ATN_MONO_LT_EQ : thm := BInvTrig.ATN_MONO_LT_EQ
unsafe def ATN_MONO_LE_EQ : thm := BInvTrig.ATN_MONO_LE_EQ
unsafe def ATN_INJ : thm := BInvTrig.ATN_INJ
unsafe def ATN_POS_LT : thm := BInvTrig.ATN_POS_LT
unsafe def ATN_POS_LE : thm := BInvTrig.ATN_POS_LE
unsafe def ATN_LT_PI4_POS : thm := BInvTrig.ATN_LT_PI4_POS
unsafe def ATN_LT_PI4_NEG : thm := BInvTrig.ATN_LT_PI4_NEG
unsafe def ATN_LT_PI4 : thm := BInvTrig.ATN_LT_PI4
unsafe def ATN_LE_PI4 : thm := BInvTrig.ATN_LE_PI4

-- ArcSinCos
unsafe def COS_SIN_SQRT : thm := BArcSinCos.COS_SIN_SQRT
unsafe def COS_ASN_NZ : thm := BArcSinCos.COS_ASN_NZ
unsafe def DIFF_ASN_COS : thm := BArcSinCos.DIFF_ASN_COS
unsafe def DIFF_ASN : thm := BArcSinCos.DIFF_ASN
unsafe def SIN_COS_SQRT : thm := BArcSinCos.SIN_COS_SQRT
unsafe def SIN_ACS_NZ : thm := BArcSinCos.SIN_ACS_NZ
unsafe def DIFF_ACS_SIN : thm := BArcSinCos.DIFF_ACS_SIN
unsafe def DIFF_ACS : thm := BArcSinCos.DIFF_ACS
unsafe def CIRCLE_SINCOS : thm := BArcSinCos.CIRCLE_SINCOS
unsafe def ACS_MONO_LT : thm := BArcSinCos.ACS_MONO_LT
unsafe def LE_MATCH_TAC := BArcSinCos.LE_MATCH_TAC
unsafe def LESS_SUC_EQ : thm := BArcSinCos.LESS_SUC_EQ
unsafe def LESS_1 : thm := BArcSinCos.LESS_1
unsafe def division : thm := BArcSinCos.division
unsafe def dsize : thm := BArcSinCos.dsize
unsafe def tdiv : thm := BArcSinCos.tdiv
unsafe def gauge : thm := BArcSinCos.gauge
unsafe def fine : thm := BArcSinCos.fine
unsafe def rsum : thm := BArcSinCos.rsum
unsafe def defint : thm := BArcSinCos.defint

-- Division
unsafe def DIVISION_0 : thm := BDivision.DIVISION_0
unsafe def DIVISION_1 : thm := BDivision.DIVISION_1
unsafe def DIVISION_SINGLE : thm := BDivision.DIVISION_SINGLE
unsafe def DIVISION_LHS : thm := BDivision.DIVISION_LHS
unsafe def DIVISION_THM : thm := BDivision.DIVISION_THM
unsafe def DIVISION_RHS : thm := BDivision.DIVISION_RHS
unsafe def DIVISION_LT_GEN : thm := BDivision.DIVISION_LT_GEN
unsafe def DIVISION_LT : thm := BDivision.DIVISION_LT
unsafe def DIVISION_LE : thm := BDivision.DIVISION_LE
unsafe def DIVISION_GT : thm := BDivision.DIVISION_GT
unsafe def DIVISION_EQ : thm := BDivision.DIVISION_EQ
unsafe def DIVISION_LBOUND : thm := BDivision.DIVISION_LBOUND
unsafe def DIVISION_LBOUND_LT : thm := BDivision.DIVISION_LBOUND_LT
unsafe def DIVISION_UBOUND : thm := BDivision.DIVISION_UBOUND
unsafe def DIVISION_UBOUND_LT : thm := BDivision.DIVISION_UBOUND_LT

-- DivAppend
unsafe def DIVISION_APPEND_LEMMA1 : thm := BDivAppend.DIVISION_APPEND_LEMMA1
unsafe def DIVISION_APPEND_LEMMA2 : thm := BDivAppend.DIVISION_APPEND_LEMMA2
unsafe def DIVISION_APPEND_EXPLICIT : thm := BDivAppend.DIVISION_APPEND_EXPLICIT
unsafe def DIVISION_APPEND_STRONG : thm := BDivAppend.DIVISION_APPEND_STRONG
unsafe def DIVISION_APPEND : thm := BDivAppend.DIVISION_APPEND
unsafe def DIVISION_EXISTS : thm := BDivAppend.DIVISION_EXISTS

-- Gauge
unsafe def GAUGE_MIN : thm := BGauge.GAUGE_MIN
unsafe def FINE_MIN : thm := BGauge.FINE_MIN
unsafe def DINT_UNIQ : thm := BGauge.DINT_UNIQ
unsafe def INTEGRAL_NULL : thm := BGauge.INTEGRAL_NULL
unsafe def STRADDLE_LEMMA : thm := BGauge.STRADDLE_LEMMA
unsafe def FTC1 : thm := BGauge.FTC1

-- Integral
unsafe def integrable : thm := BIntegral.integrable
unsafe def integral : thm := BIntegral.integral
unsafe def INTEGRABLE_DEFINT : thm := BIntegral.INTEGRABLE_DEFINT
unsafe def DIVISION_BOUNDS : thm := BIntegral.DIVISION_BOUNDS
unsafe def TDIV_BOUNDS : thm := BIntegral.TDIV_BOUNDS
unsafe def TDIV_LE : thm := BIntegral.TDIV_LE
unsafe def DEFINT_WRONG : thm := BIntegral.DEFINT_WRONG
unsafe def DEFINT_INTEGRAL : thm := BIntegral.DEFINT_INTEGRAL
unsafe def DEFINT_CONST : thm := BIntegral.DEFINT_CONST
unsafe def DEFINT_0 : thm := BIntegral.DEFINT_0
unsafe def DEFINT_NEG : thm := BIntegral.DEFINT_NEG
unsafe def DEFINT_CMUL : thm := BIntegral.DEFINT_CMUL
unsafe def DEFINT_ADD : thm := BIntegral.DEFINT_ADD
unsafe def DEFINT_SUB : thm := BIntegral.DEFINT_SUB
unsafe def INTEGRAL_LE : thm := BIntegral.INTEGRAL_LE
unsafe def DEFINT_LE : thm := BIntegral.DEFINT_LE
unsafe def DEFINT_TRIANGLE : thm := BIntegral.DEFINT_TRIANGLE
unsafe def DEFINT_EQ : thm := BIntegral.DEFINT_EQ
unsafe def INTEGRAL_EQ : thm := BIntegral.INTEGRAL_EQ
unsafe def INTEGRATION_BY_PARTS : thm := BIntegral.INTEGRATION_BY_PARTS
unsafe def DIVISION_LE_SUC : thm := BIntegral.DIVISION_LE_SUC
unsafe def DIVISION_MONO_LE : thm := BIntegral.DIVISION_MONO_LE
unsafe def DIVISION_MONO_LE_SUC : thm := BIntegral.DIVISION_MONO_LE_SUC
unsafe def DIVISION_INTERMEDIATE : thm := BIntegral.DIVISION_INTERMEDIATE
unsafe def DIVISION_DSIZE_LE : thm := BIntegral.DIVISION_DSIZE_LE
unsafe def DIVISION_DSIZE_GE : thm := BIntegral.DIVISION_DSIZE_GE
unsafe def DIVISION_DSIZE_EQ : thm := BIntegral.DIVISION_DSIZE_EQ
unsafe def DIVISION_DSIZE_EQ_ALT : thm := BIntegral.DIVISION_DSIZE_EQ_ALT

-- Combine
unsafe def DEFINT_COMBINE : thm := BCombine.DEFINT_COMBINE

-- Spike
unsafe def DEFINT_DELTA_LEFT : thm := BSpike.DEFINT_DELTA_LEFT
unsafe def DEFINT_DELTA_RIGHT : thm := BSpike.DEFINT_DELTA_RIGHT
unsafe def DEFINT_DELTA : thm := BSpike.DEFINT_DELTA
unsafe def DEFINT_POINT_SPIKE : thm := BSpike.DEFINT_POINT_SPIKE
unsafe def DEFINT_FINITE_SPIKE : thm := BSpike.DEFINT_FINITE_SPIKE
unsafe def GAUGE_MIN_FINITE : thm := BSpike.GAUGE_MIN_FINITE
unsafe def INTEGRABLE_CAUCHY : thm := BSpike.INTEGRABLE_CAUCHY

-- Limit
unsafe def SUM_DIFFS : thm := BLimit.SUM_DIFFS
unsafe def RSUM_BOUND : thm := BLimit.RSUM_BOUND
unsafe def RSUM_DIFF_BOUND : thm := BLimit.RSUM_DIFF_BOUND
unsafe def INTEGRABLE_LIMIT : thm := BLimit.INTEGRABLE_LIMIT
unsafe def INTEGRABLE_CONST : thm := BLimit.INTEGRABLE_CONST
unsafe def INTEGRABLE_COMBINE : thm := BLimit.INTEGRABLE_COMBINE
unsafe def INTEGRABLE_POINT_SPIKE : thm := BLimit.INTEGRABLE_POINT_SPIKE
unsafe def INTEGRABLE_CONTINUOUS : thm := BLimit.INTEGRABLE_CONTINUOUS
unsafe def INTEGRABLE_SPLIT_SIDES : thm := BLimit.INTEGRABLE_SPLIT_SIDES
unsafe def INTEGRABLE_SUBINTERVAL_LEFT : thm := BLimit.INTEGRABLE_SUBINTERVAL_LEFT
unsafe def INTEGRABLE_SUBINTERVAL_RIGHT : thm := BLimit.INTEGRABLE_SUBINTERVAL_RIGHT
unsafe def INTEGRABLE_SUBINTERVAL : thm := BLimit.INTEGRABLE_SUBINTERVAL

-- IntRule
unsafe def INTEGRABLE_RULE : term → IO (Except String thm) := fun t => (BIntRule.INTEGRABLE_RULE t).run
unsafe def INTEGRABLE_CONV : HolCore.Equal.ioconv := fun t => BIntRule.INTEGRABLE_CONV t
unsafe def INTEGRAL_CONST : thm := BIntRule.INTEGRAL_CONST
unsafe def INTEGRAL_CMUL : thm := BIntRule.INTEGRAL_CMUL
unsafe def INTEGRAL_ADD : thm := BIntRule.INTEGRAL_ADD
unsafe def INTEGRAL_SUB : thm := BIntRule.INTEGRAL_SUB
unsafe def INTEGRAL_BY_PARTS : thm := BIntRule.INTEGRAL_BY_PARTS
unsafe def SYM_CANON_CONV := BIntRule.SYM_CANON_CONV
unsafe def EXT_CONV : term → IO (Except String thm) := fun t => (BIntRule.EXT_CONV t).run

-- Mclaurin
unsafe def MCLAURIN : thm := BMclaurin.MCLAURIN
unsafe def MCLAURIN_NEG : thm := BMclaurin.MCLAURIN_NEG
unsafe def MCLAURIN_BI_LE : thm := BMclaurin.MCLAURIN_BI_LE

-- McLnExp
unsafe def MCLAURIN_ALL_LT : thm := BMcLnExp.MCLAURIN_ALL_LT
unsafe def MCLAURIN_ZERO : thm := BMcLnExp.MCLAURIN_ZERO
unsafe def MCLAURIN_ALL_LE : thm := BMcLnExp.MCLAURIN_ALL_LE
unsafe def MCLAURIN_EXP_LEMMA : thm := BMcLnExp.MCLAURIN_EXP_LEMMA
unsafe def MCLAURIN_EXP_LT : thm := BMcLnExp.MCLAURIN_EXP_LT
unsafe def MCLAURIN_EXP_LE : thm := BMcLnExp.MCLAURIN_EXP_LE
unsafe def MCLAURIN_LN_POS : thm := BMcLnExp.MCLAURIN_LN_POS
unsafe def MCLAURIN_LN_NEG : thm := BMcLnExp.MCLAURIN_LN_NEG

-- SinCosMcl
unsafe def MCLAURIN_SIN : thm := BSinCosMcl.MCLAURIN_SIN
unsafe def MCLAURIN_COS : thm := BSinCosMcl.MCLAURIN_COS

-- AtnSer
unsafe def REAL_ATN_POWSER_SUMMABLE : thm := BAtnSer.REAL_ATN_POWSER_SUMMABLE
unsafe def REAL_ATN_POWSER_DIFFS_SUMMABLE : thm := BAtnSer.REAL_ATN_POWSER_DIFFS_SUMMABLE
unsafe def REAL_ATN_POWSER_DIFFS_SUM : thm := BAtnSer.REAL_ATN_POWSER_DIFFS_SUM
unsafe def REAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE : thm := BAtnSer.REAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE
unsafe def REAL_ATN_POWSER_DIFFL : thm := BAtnSer.REAL_ATN_POWSER_DIFFL
unsafe def REAL_ATN_POWSER : thm := BAtnSer.REAL_ATN_POWSER
unsafe def MCLAURIN_ATN : thm := BAtnSer.MCLAURIN_ATN































-- @@EXPORTS END

/-- `needs "Library/transc.ml"`: build every bundle, in file order. -/
unsafe def ensureTransc : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BPowSer.POWDIFF_LEMMA
  let _ ← IO.mkRef BTermDiff.TERMDIFF_LEMMA1
  let _ ← IO.mkRef BPowSerEq.SEQ_NPOW
  let _ ← IO.mkRef BDefs.MULT_DIV_2
  let _ ← IO.mkRef BDiffConv.DIFF_COMPOSITE
  let _ ← IO.mkRef BExp.REAL_EXP_0
  let _ ← IO.mkRef BLnRoot.ln
  let _ ← IO.mkRef BTrig1.SIN_0
  let _ ← IO.mkRef BTrig2.PI2
  let _ ← IO.mkRef BTan.tan
  let _ ← IO.mkRef BInvTrig.asn
  let _ ← IO.mkRef BArcSinCos.COS_SIN_SQRT
  let _ ← IO.mkRef BDivision.DIVISION_0
  let _ ← IO.mkRef BDivAppend.DIVISION_APPEND_LEMMA1
  let _ ← IO.mkRef BGauge.GAUGE_MIN
  let _ ← IO.mkRef BIntegral.integrable
  let _ ← IO.mkRef BCombine.DEFINT_COMBINE
  let _ ← IO.mkRef BSpike.DEFINT_DELTA_LEFT
  let _ ← IO.mkRef BLimit.SUM_DIFFS
  let _ ← IO.mkRef BIntRule.INTEGRAL_CONST
  let _ ← IO.mkRef BMclaurin.MCLAURIN
  let _ ← IO.mkRef BMcLnExp.MCLAURIN_ALL_LT
  let _ ← IO.mkRef BSinCosMcl.MCLAURIN_SIN
  let _ ← IO.mkRef BAtnSer.REAL_ATN_POWSER_SUMMABLE  -- @@ENSURE END
  pure ()

end SessionLibrary.Transc
