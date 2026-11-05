/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/analysis.ml.                                -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Analysis.lean

  The session half of the analysis.ml translation: it supplies
  HolLibrary.Analysis' dependencies from Session and exports every name
  under its HOL Light name.  Importing this module is
  `needs "Library/analysis.ml"`: each bundle is built by `initialize` when
  the module is loaded, in file order.

  analysis.ml rebinds about a hundred core names (REAL_LE_TRANS, SUM_LE,
  sum, sup, EXPAND_TAC, ...); the versions here are analysis.ml's, so with
  both `Session` and `SessionLibrary.Analysis` open, qualify them.
-/

import Session
import HolLibrary.Analysis

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Analysis

/-- The core theorems analysis.ml uses, ADD to REAL_ADD_SYM. -/
def core1 : HolLibrary.Analysis.CoreThms1 where
  ADD := Session.«ADD»
  ADD1 := Session.«ADD1»
  ADD_AC := Session.«ADD_AC»
  ADD_ASSOC := Session.«ADD_ASSOC»
  ADD_CLAUSES := Session.«ADD_CLAUSES»
  ADD_SUB := Session.«ADD_SUB»
  ADD_SYM := Session.«ADD_SYM»
  AND_FORALL_THM := Session.«AND_FORALL_THM»
  ARITH := Session.«ARITH»
  ARITH_EQ := Session.«ARITH_EQ»
  BETA_THM := Session.«BETA_THM»
  CONJ_ASSOC := Session.«CONJ_ASSOC»
  CONJ_SYM := Session.«CONJ_SYM»
  CONTRAPOS_THM := Session.«CONTRAPOS_THM»
  DE_MORGAN_THM := Session.«DE_MORGAN_THM»
  EQ_IMP := Session.«EQ_IMP»
  EQ_IMP_LE := Session.«EQ_IMP_LE»
  EQ_TRANS := Session.«EQ_TRANS»
  EXISTS_UNIQUE_THM := Session.«EXISTS_UNIQUE_THM»
  EXTENSION := Session.«EXTENSION»
  FACT_LT := Session.«FACT_LT»
  FINITE_NUMSEG := Session.«FINITE_NUMSEG»
  FINITE_SUBSET := Session.«FINITE_SUBSET»
  FUN_EQ_THM := Session.«FUN_EQ_THM»
  GE := Session.«GE»
  GT := Session.«GT»
  IMP_CLAUSES := Session.«IMP_CLAUSES»
  IMP_IMP := Session.«IMP_IMP»
  IN := Session.«IN»
  IN_ELIM_THM := Session.«IN_ELIM_THM»
  IN_INSERT := Session.«IN_INSERT»
  IN_NUMSEG := Session.«IN_NUMSEG»
  LE := Session.«LE»
  LEFT_AND_EXISTS_THM := Session.«LEFT_AND_EXISTS_THM»
  LEFT_EXISTS_AND_THM := Session.«LEFT_EXISTS_AND_THM»
  LEFT_FORALL_IMP_THM := Session.«LEFT_FORALL_IMP_THM»
  LEFT_IMP_EXISTS_THM := Session.«LEFT_IMP_EXISTS_THM»
  LE_0 := Session.«LE_0»
  LE_ADD := Session.«LE_ADD»
  LE_ADD_LCANCEL := Session.«LE_ADD_LCANCEL»
  LE_ANTISYM := Session.«LE_ANTISYM»
  LE_CASES := Session.«LE_CASES»
  LE_EXISTS := Session.«LE_EXISTS»
  LE_LT := Session.«LE_LT»
  LE_MULT_RCANCEL := Session.«LE_MULT_RCANCEL»
  LE_REFL := Session.«LE_REFL»
  LE_SUC := Session.«LE_SUC»
  LE_SUC_LT := Session.«LE_SUC_LT»
  LE_TRANS := Session.«LE_TRANS»
  LT := Session.«LT»
  LTE_CASES := Session.«LTE_CASES»
  LTE_TRANS := Session.«LTE_TRANS»
  LT_0 := Session.«LT_0»
  LT_ADD_RCANCEL := Session.«LT_ADD_RCANCEL»
  LT_EXISTS := Session.«LT_EXISTS»
  LT_IMP_LE := Session.«LT_IMP_LE»
  LT_REFL := Session.«LT_REFL»
  LT_SUC_LE := Session.«LT_SUC_LE»
  LT_TRANS := Session.«LT_TRANS»
  MONO_EXISTS := Session.«MONO_EXISTS»
  MONO_FORALL := Session.«MONO_FORALL»
  MULT_CLAUSES := Session.«MULT_CLAUSES»
  MULT_SYM := Session.«MULT_SYM»
  NOT_CLAUSES := Session.«NOT_CLAUSES»
  NOT_EXISTS_THM := Session.«NOT_EXISTS_THM»
  NOT_FORALL_THM := Session.«NOT_FORALL_THM»
  NOT_IMP := Session.«NOT_IMP»
  NOT_IN_EMPTY := Session.«NOT_IN_EMPTY»
  NOT_LT := Session.«NOT_LT»
  NOT_SUC := Session.«NOT_SUC»
  PRE := Session.«PRE»
  REAL_ABS_0 := Session.«REAL_ABS_0»
  REAL_ABS_DIV := Session.«REAL_ABS_DIV»
  REAL_ABS_NUM := Session.«REAL_ABS_NUM»
  REAL_ABS_POS := Session.«REAL_ABS_POS»
  REAL_ABS_REFL := Session.«REAL_ABS_REFL»
  REAL_ABS_SUB := Session.«REAL_ABS_SUB»
  REAL_ABS_TRIANGLE := Session.«REAL_ABS_TRIANGLE»
  REAL_ADD2_SUB2 := Session.«REAL_ADD2_SUB2»
  REAL_ADD_AC := Session.«REAL_ADD_AC»
  REAL_ADD_ASSOC := Session.«REAL_ADD_ASSOC»
  REAL_ADD_LDISTRIB := Session.«REAL_ADD_LDISTRIB»
  REAL_ADD_LID := Session.«REAL_ADD_LID»
  REAL_ADD_LINV := Session.«REAL_ADD_LINV»
  REAL_ADD_RDISTRIB := Session.«REAL_ADD_RDISTRIB»
  REAL_ADD_RID := Session.«REAL_ADD_RID»
  REAL_ADD_RINV := Session.«REAL_ADD_RINV»
  REAL_ADD_SUB := Session.«REAL_ADD_SUB»
  REAL_ADD_SUB2 := Session.«REAL_ADD_SUB2»
  REAL_ADD_SYM := Session.«REAL_ADD_SYM»
/-- The core theorems analysis.ml uses, REAL_ARCH to REAL_MUL_RINV. -/
def core2 : HolLibrary.Analysis.CoreThms2 where
  REAL_ARCH := Session.«REAL_ARCH»
  REAL_ARCH_POW := Session.«REAL_ARCH_POW»
  REAL_ARCH_POW2 := Session.«REAL_ARCH_POW2»
  REAL_ARCH_SIMPLE := Session.«REAL_ARCH_SIMPLE»
  REAL_COMPLETE := Session.«REAL_COMPLETE»
  REAL_DIV_LMUL := Session.«REAL_DIV_LMUL»
  REAL_DIV_REFL := Session.«REAL_DIV_REFL»
  REAL_DIV_RMUL := Session.«REAL_DIV_RMUL»
  REAL_DOWN := Session.«REAL_DOWN»
  REAL_DOWN2 := Session.«REAL_DOWN2»
  REAL_ENTIRE := Session.«REAL_ENTIRE»
  REAL_EQ_ADD_LCANCEL := Session.«REAL_EQ_ADD_LCANCEL»
  REAL_EQ_IMP_LE := Session.«REAL_EQ_IMP_LE»
  REAL_EQ_NEG2 := Session.«REAL_EQ_NEG2»
  REAL_EQ_SUB_LADD := Session.«REAL_EQ_SUB_LADD»
  REAL_EQ_SUB_RADD := Session.«REAL_EQ_SUB_RADD»
  REAL_INV_MUL := Session.«REAL_INV_MUL»
  REAL_LET_ADD := Session.«REAL_LET_ADD»
  REAL_LET_ADD2 := Session.«REAL_LET_ADD2»
  REAL_LET_TOTAL := Session.«REAL_LET_TOTAL»
  REAL_LET_TRANS := Session.«REAL_LET_TRANS»
  REAL_LE_01 := Session.«REAL_LE_01»
  REAL_LE_ADD := Session.«REAL_LE_ADD»
  REAL_LE_ADD2 := Session.«REAL_LE_ADD2»
  REAL_LE_ADDL := Session.«REAL_LE_ADDL»
  REAL_LE_ADDR := Session.«REAL_LE_ADDR»
  REAL_LE_ANTISYM := Session.«REAL_LE_ANTISYM»
  REAL_LE_DOUBLE := Session.«REAL_LE_DOUBLE»
  REAL_LE_LADD := Session.«REAL_LE_LADD»
  REAL_LE_LDIV_EQ := Session.«REAL_LE_LDIV_EQ»
  REAL_LE_LMUL := Session.«REAL_LE_LMUL»
  REAL_LE_LT := Session.«REAL_LE_LT»
  REAL_LE_MUL := Session.«REAL_LE_MUL»
  REAL_LE_NEG2 := Session.«REAL_LE_NEG2»
  REAL_LE_NEGL := Session.«REAL_LE_NEGL»
  REAL_LE_NEGR := Session.«REAL_LE_NEGR»
  REAL_LE_NEGTOTAL := Session.«REAL_LE_NEGTOTAL»
  REAL_LE_RADD := Session.«REAL_LE_RADD»
  REAL_LE_REFL := Session.«REAL_LE_REFL»
  REAL_LE_RMUL := Session.«REAL_LE_RMUL»
  REAL_LE_RMUL_EQ := Session.«REAL_LE_RMUL_EQ»
  REAL_LE_SQUARE := Session.«REAL_LE_SQUARE»
  REAL_LE_SUB_LADD := Session.«REAL_LE_SUB_LADD»
  REAL_LE_SUB_RADD := Session.«REAL_LE_SUB_RADD»
  REAL_LE_TOTAL := Session.«REAL_LE_TOTAL»
  REAL_LE_TRANS := Session.«REAL_LE_TRANS»
  REAL_LNEG_UNIQ := Session.«REAL_LNEG_UNIQ»
  REAL_LTE_ADD := Session.«REAL_LTE_ADD»
  REAL_LTE_ADD2 := Session.«REAL_LTE_ADD2»
  REAL_LTE_TRANS := Session.«REAL_LTE_TRANS»
  REAL_LT_01 := Session.«REAL_LT_01»
  REAL_LT_ADD := Session.«REAL_LT_ADD»
  REAL_LT_ADD1 := Session.«REAL_LT_ADD1»
  REAL_LT_ADD2 := Session.«REAL_LT_ADD2»
  REAL_LT_ADDL := Session.«REAL_LT_ADDL»
  REAL_LT_ADDNEG := Session.«REAL_LT_ADDNEG»
  REAL_LT_ADDNEG2 := Session.«REAL_LT_ADDNEG2»
  REAL_LT_ADDR := Session.«REAL_LT_ADDR»
  REAL_LT_ADD_SUB := Session.«REAL_LT_ADD_SUB»
  REAL_LT_ANTISYM := Session.«REAL_LT_ANTISYM»
  REAL_LT_DIV := Session.«REAL_LT_DIV»
  REAL_LT_GT := Session.«REAL_LT_GT»
  REAL_LT_IMP_LE := Session.«REAL_LT_IMP_LE»
  REAL_LT_IMP_NE := Session.«REAL_LT_IMP_NE»
  REAL_LT_IMP_NZ := Session.«REAL_LT_IMP_NZ»
  REAL_LT_INV2 := Session.«REAL_LT_INV2»
  REAL_LT_LADD := Session.«REAL_LT_LADD»
  REAL_LT_LDIV_EQ := Session.«REAL_LT_LDIV_EQ»
  REAL_LT_LE := Session.«REAL_LT_LE»
  REAL_LT_LMUL_EQ := Session.«REAL_LT_LMUL_EQ»
  REAL_LT_MUL := Session.«REAL_LT_MUL»
  REAL_LT_NEG2 := Session.«REAL_LT_NEG2»
  REAL_LT_NEGTOTAL := Session.«REAL_LT_NEGTOTAL»
  REAL_LT_NZ := Session.«REAL_LT_NZ»
  REAL_LT_RADD := Session.«REAL_LT_RADD»
  REAL_LT_RDIV_EQ := Session.«REAL_LT_RDIV_EQ»
  REAL_LT_REFL := Session.«REAL_LT_REFL»
  REAL_LT_RMUL_EQ := Session.«REAL_LT_RMUL_EQ»
  REAL_LT_SUB_LADD := Session.«REAL_LT_SUB_LADD»
  REAL_LT_SUB_RADD := Session.«REAL_LT_SUB_RADD»
  REAL_LT_TOTAL := Session.«REAL_LT_TOTAL»
  REAL_LT_TRANS := Session.«REAL_LT_TRANS»
  REAL_MUL_AC := Session.«REAL_MUL_AC»
  REAL_MUL_ASSOC := Session.«REAL_MUL_ASSOC»
  REAL_MUL_LID := Session.«REAL_MUL_LID»
  REAL_MUL_LINV := Session.«REAL_MUL_LINV»
  REAL_MUL_LZERO := Session.«REAL_MUL_LZERO»
  REAL_MUL_RID := Session.«REAL_MUL_RID»
  REAL_MUL_RINV := Session.«REAL_MUL_RINV»
/-- The core theorems analysis.ml uses, REAL_MUL_RZERO to sup. -/
def core3 : HolLibrary.Analysis.CoreThms3 where
  REAL_MUL_RZERO := Session.«REAL_MUL_RZERO»
  REAL_MUL_SYM := Session.«REAL_MUL_SYM»
  REAL_NEG_0 := Session.«REAL_NEG_0»
  REAL_NEG_ADD := Session.«REAL_NEG_ADD»
  REAL_NEG_EQ := Session.«REAL_NEG_EQ»
  REAL_NEG_GE0 := Session.«REAL_NEG_GE0»
  REAL_NEG_GT0 := Session.«REAL_NEG_GT0»
  REAL_NEG_LE0 := Session.«REAL_NEG_LE0»
  REAL_NEG_LMUL := Session.«REAL_NEG_LMUL»
  REAL_NEG_LT0 := Session.«REAL_NEG_LT0»
  REAL_NEG_MINUS1 := Session.«REAL_NEG_MINUS1»
  REAL_NEG_MUL2 := Session.«REAL_NEG_MUL2»
  REAL_NEG_NEG := Session.«REAL_NEG_NEG»
  REAL_NEG_RMUL := Session.«REAL_NEG_RMUL»
  REAL_NEG_SUB := Session.«REAL_NEG_SUB»
  REAL_NOT_LE := Session.«REAL_NOT_LE»
  REAL_NOT_LT := Session.«REAL_NOT_LT»
  REAL_OF_NUM_ADD := Session.«REAL_OF_NUM_ADD»
  REAL_OF_NUM_EQ := Session.«REAL_OF_NUM_EQ»
  REAL_OF_NUM_LE := Session.«REAL_OF_NUM_LE»
  REAL_OF_NUM_LT := Session.«REAL_OF_NUM_LT»
  REAL_OF_NUM_SUC := Session.«REAL_OF_NUM_SUC»
  REAL_POS := Session.«REAL_POS»
  REAL_POW_LBOUND := Session.«REAL_POW_LBOUND»
  REAL_RNEG_UNIQ := Session.«REAL_RNEG_UNIQ»
  REAL_SUB_0 := Session.«REAL_SUB_0»
  REAL_SUB_ABS := Session.«REAL_SUB_ABS»
  REAL_SUB_ADD := Session.«REAL_SUB_ADD»
  REAL_SUB_ADD2 := Session.«REAL_SUB_ADD2»
  REAL_SUB_LDISTRIB := Session.«REAL_SUB_LDISTRIB»
  REAL_SUB_LE := Session.«REAL_SUB_LE»
  REAL_SUB_LNEG := Session.«REAL_SUB_LNEG»
  REAL_SUB_LT := Session.«REAL_SUB_LT»
  REAL_SUB_LZERO := Session.«REAL_SUB_LZERO»
  REAL_SUB_NEG2 := Session.«REAL_SUB_NEG2»
  REAL_SUB_RDISTRIB := Session.«REAL_SUB_RDISTRIB»
  REAL_SUB_REFL := Session.«REAL_SUB_REFL»
  REAL_SUB_RNEG := Session.«REAL_SUB_RNEG»
  REAL_SUB_RZERO := Session.«REAL_SUB_RZERO»
  REAL_SUB_SUB := Session.«REAL_SUB_SUB»
  REAL_SUB_SUB2 := Session.«REAL_SUB_SUB2»
  REAL_SUB_TRIANGLE := Session.«REAL_SUB_TRIANGLE»
  REAL_SUP_LE := Session.«REAL_SUP_LE»
  REAL_WLOG_LE := Session.«REAL_WLOG_LE»
  RIGHT_AND_EXISTS_THM := Session.«RIGHT_AND_EXISTS_THM»
  RIGHT_AND_FORALL_THM := Session.«RIGHT_AND_FORALL_THM»
  RIGHT_EXISTS_AND_THM := Session.«RIGHT_EXISTS_AND_THM»
  RIGHT_FORALL_IMP_THM := Session.«RIGHT_FORALL_IMP_THM»
  RIGHT_IMP_EXISTS_THM := Session.«RIGHT_IMP_EXISTS_THM»
  RIGHT_IMP_FORALL_THM := Session.«RIGHT_IMP_FORALL_THM»
  SELECT_AX := Session.«SELECT_AX»
  SKOLEM_THM := Session.«SKOLEM_THM»
  SUBSET := Session.«SUBSET»
  SUB_ADD := Session.«SUB_ADD»
  SUC_SUB1 := Session.«SUC_SUB1»
  SUM_0 := Session.«SUM_0»
  SUM_ABS := Session.«SUM_ABS»
  SUM_ABS_LE := Session.«SUM_ABS_LE»
  SUM_ADD := Session.«SUM_ADD»
  SUM_BOUND := Session.«SUM_BOUND»
  SUM_CLAUSES := Session.«SUM_CLAUSES»
  SUM_CONST := Session.«SUM_CONST»
  SUM_DIFF := Session.«SUM_DIFF»
  SUM_EQ := Session.«SUM_EQ»
  SUM_EQ_0 := Session.«SUM_EQ_0»
  SUM_GROUP := Session.«SUM_GROUP»
  SUM_LE := Session.«SUM_LE»
  SUM_NEG := Session.«SUM_NEG»
  SUM_OFFSET := Session.«SUM_OFFSET»
  SUM_SUB := Session.«SUM_SUB»
  SUM_SWAP := Session.«SUM_SWAP»
  SWAP_EXISTS_THM := Session.«SWAP_EXISTS_THM»
  SWAP_FORALL_THM := Session.«SWAP_FORALL_THM»
  TRIV_EXISTS_AND_THM := Session.«TRIV_EXISTS_AND_THM»
  TRIV_FORALL_IMP_THM := Session.«TRIV_FORALL_IMP_THM»
  num_Axiom := Session.«num_Axiom»
  num_CASES := Session.«num_CASES»
  num_RECURSION := Session.«num_RECURSION»
  num_WOP := Session.«num_WOP»
  real_abs := Session.«real_abs»
  real_div := Session.«real_div»
  real_ge := Session.«real_ge»
  real_gt := Session.«real_gt»
  real_le := Session.«real_le»
  real_pow := Session.«real_pow»
  real_sub := Session.«real_sub»
  sum := Session.«sum»
  sup := Session.«sup»

/-- What analysis.ml uses from Session. -/
def deps : HolLibrary.Analysis.AnalysisDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  new_specification names th := ExceptT.mk (Session.new_specification names th)
  new_type_definition ty names th :=
    ExceptT.mk (Session.new_type_definition ty names.1 names.2 th)
  prove_recursive_functions_exist ax t :=
    ExceptT.mk (Session.prove_recursive_functions_exist ax t)
  prioritize_num := do
    match ← HolCore.Kernel.mk_type "num" [] with
    | .ok ty => Session.prioritize_overload ty
    | .error e => throw (IO.userError e)
  prioritize_real := Session.prioritize_real
  parse_as_infix := Session.parse_as_infix
  make_overloadable s ty := ExceptT.mk (Session.make_overloadable s ty)
  overload_interface s t := ExceptT.mk (Session.overload_interface s t)
  override_interface s t := ExceptT.mk (Session.override_interface s t)
  remove_interface := Session.remove_interface
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH3 t)
  REAL_ARITH_TAC := Session.REAL_ARITH_TAC2
  GEN_BETA_CONV := Session.GEN_BETA_CONV
  num_CONV := Session.num_CONV
  core1 := core1
  core2 := core2
  core3 := core3

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in analysis.ml order, after the whole of Session (as HOL
   Light has loaded all of hol_lib.ml before analysis.ml's parser changes:
   priorities, infixes, `sum` overloading). -/
initialize BCompat : HolLibrary.Analysis.Compat ←
  ioB "setupCompat" (HolLibrary.Analysis.setupCompat deps).run
initialize BNames : HolLibrary.Analysis.Names ←
  ioB "setupNames" (HolLibrary.Analysis.setupNames deps).run
initialize BTactics : HolLibrary.Analysis.Tactics ←
  ioB "setupTactics" (HolLibrary.Analysis.setupTactics deps BCompat).run
initialize BReals1 : HolLibrary.Analysis.Reals1 ←
  ioB "setupReals1" (HolLibrary.Analysis.setupReals1 deps BCompat).run
initialize BReals2 : HolLibrary.Analysis.Reals2 ←
  ioB "setupReals2" (HolLibrary.Analysis.setupReals2 deps BNames BReals1).run
initialize BReals3 : HolLibrary.Analysis.Reals3 ←
  ioB "setupReals3" (HolLibrary.Analysis.setupReals3 deps BTactics BReals1 BReals2).run
initialize BAbs : HolLibrary.Analysis.Abs ←
  ioB "setupAbs" (HolLibrary.Analysis.setupAbs deps BNames BReals1 BReals2 BReals3).run
initialize BPow : HolLibrary.Analysis.Pow ←
  ioB "setupPow"
    (HolLibrary.Analysis.setupPow deps BCompat BNames BReals1 BReals2 BReals3 BAbs).run
initialize BSums : HolLibrary.Analysis.Sums ←
  ioB "setupSums" (HolLibrary.Analysis.setupSums deps BReals1 BReals2).run
initialize BSumConv : HolLibrary.Analysis.SumConv ←
  ioB "setupSumConv" (HolLibrary.Analysis.setupSumConv deps BSums).run

initialize BTopology : HolLibrary.Analysis.Topology ←
  ioB "setupTopology" (HolLibrary.Analysis.setupTopology deps BCompat BTactics BReals1).run
initialize BMetricTop : HolLibrary.Analysis.MetricTop ←
  ioB "setupMetricTop" (HolLibrary.Analysis.setupMetricTop deps BReals1 BReals2 BReals3 BAbs
    BTopology).run
initialize BNets : HolLibrary.Analysis.Nets ←
  ioB "setupNets" (HolLibrary.Analysis.setupNets deps BCompat BTactics BReals1 BReals2
    BReals3 BAbs BTopology BMetricTop).run
initialize BNetArith : HolLibrary.Analysis.NetArith ←
  ioB "setupNetArith" (HolLibrary.Analysis.setupNetArith deps BCompat BNames BTactics BReals1
    BReals2 BReals3 BAbs BSums BMetricTop BNets).run
initialize BSeqs : HolLibrary.Analysis.Seqs ←
  ioB "setupSeqs" (HolLibrary.Analysis.setupSeqs deps BCompat BNames BReals1 BReals2 BReals3
    BAbs BPow BMetricTop BNets BNetArith).run
initialize BSeqs2 : HolLibrary.Analysis.Seqs2 ←
  ioB "setupSeqs2" (HolLibrary.Analysis.setupSeqs2 deps BCompat BNames BReals1 BReals2
    BReals3 BAbs BNets BNetArith BSeqs).run

initialize BSeqLim : HolLibrary.Analysis.SeqLim ←
  ioB "setupSeqLim" (HolLibrary.Analysis.setupSeqLim deps BNames BTactics BReals1 BReals2
    BReals3 BAbs BPow BNetArith BSeqs BSeqs2).run
initialize BSeries1 : HolLibrary.Analysis.Series1 ←
  ioB "setupSeries1" (HolLibrary.Analysis.setupSeries1 deps BNames BReals1 BReals2 BReals3
    BAbs BPow BSums BSeqs BSeqs2 BSeqLim).run
initialize BSeries2 : HolLibrary.Analysis.Series2 ←
  ioB "setupSeries2" (HolLibrary.Analysis.setupSeries2 deps BNames BTactics BReals1 BReals2
    BReals3 BAbs BPow BSums BSeqs BSeqs2 BSeqLim BSeries1).run
initialize BLims : HolLibrary.Analysis.Lims ←
  ioB "setupLims" (HolLibrary.Analysis.setupLims deps BTactics BReals1 BReals2 BReals3 BAbs
    BTopology BMetricTop BNets BNetArith).run
initialize BDiffs : HolLibrary.Analysis.Diffs ←
  ioB "setupDiffs" (HolLibrary.Analysis.setupDiffs deps BCompat BNames BTactics BReals1
    BReals2 BReals3 BAbs BPow BSums BSeries1 BLims).run
initialize BCont : HolLibrary.Analysis.Cont ←
  ioB "setupCont" (HolLibrary.Analysis.setupCont deps BCompat BTactics BReals1 BReals2
    BReals3 BAbs BPow BSeries1 BLims BDiffs).run
initialize BMvt : HolLibrary.Analysis.Mvt ←
  ioB "setupMvt" (HolLibrary.Analysis.setupMvt deps BCompat BTactics BReals1 BReals2 BReals3
    BAbs BLims BDiffs BCont).run
initialize BInverse : HolLibrary.Analysis.Inverse ←
  ioB "setupInverse" (HolLibrary.Analysis.setupInverse deps BReals1 BReals2 BReals3 BAbs
    BLims BDiffs BCont BMvt).run
initialize BUniform : HolLibrary.Analysis.Uniform ←
  ioB "setupUniform" (HolLibrary.Analysis.setupUniform deps BReals1 BReals2 BReals3 BPow
    BSums BSeqs BSeries1 BSeries2 BLims BDiffs BCont BMvt).run

-- Compat
def dest_neg_imp := BCompat.dest_neg_imp
def CONV_OF_RCONV := BCompat.CONV_OF_RCONV
def CONV_OF_THM := BCompat.CONV_OF_THM
def X_FUN_EQ_CONV := BCompat.X_FUN_EQ_CONV
def FUN_EQ_CONV : HolCore.Equal.ioconv := fun t => BCompat.FUN_EQ_CONV t
def SINGLE_DEPTH_CONV := BCompat.SINGLE_DEPTH_CONV
def OLD_SKOLEM_CONV : HolCore.Equal.ioconv := fun t => BCompat.OLD_SKOLEM_CONV t
def X_SKOLEM_CONV := BCompat.X_SKOLEM_CONV
def EXISTS_UNIQUE_CONV : HolCore.Equal.ioconv := fun t => BCompat.EXISTS_UNIQUE_CONV t
def NOT_FORALL_CONV : HolCore.Equal.ioconv := fun t => BCompat.NOT_FORALL_CONV t
def NOT_EXISTS_CONV : HolCore.Equal.ioconv := fun t => BCompat.NOT_EXISTS_CONV t
def RIGHT_IMP_EXISTS_CONV : HolCore.Equal.ioconv := fun t => BCompat.RIGHT_IMP_EXISTS_CONV t
def FORALL_IMP_CONV : HolCore.Equal.ioconv := fun t => BCompat.FORALL_IMP_CONV t
def EXISTS_AND_CONV : HolCore.Equal.ioconv := fun t => BCompat.EXISTS_AND_CONV t
def LEFT_IMP_EXISTS_CONV : HolCore.Equal.ioconv := fun t => BCompat.LEFT_IMP_EXISTS_CONV t
def LEFT_AND_EXISTS_CONV : HolCore.Equal.ioconv := fun t => BCompat.LEFT_AND_EXISTS_CONV t
def RIGHT_AND_EXISTS_CONV : HolCore.Equal.ioconv := fun t => BCompat.RIGHT_AND_EXISTS_CONV t
def AND_FORALL_CONV : HolCore.Equal.ioconv := fun t => BCompat.AND_FORALL_CONV t
def F_IMP : thm := BCompat.F_IMP
def LEFT_AND_OVER_OR : thm := BCompat.LEFT_AND_OVER_OR
def RIGHT_AND_OVER_OR : thm := BCompat.RIGHT_AND_OVER_OR
def INST_TY_TERM := BCompat.INST_TY_TERM
def NOT_MP := BCompat.NOT_MP
def MK_ABS := BCompat.MK_ABS
def HALF_MK_ABS := BCompat.HALF_MK_ABS
def SUBST := BCompat.SUBST

-- Names
def LESS_EQUAL_ANTISYM : thm := BNames.LESS_EQUAL_ANTISYM
def NOT_LESS_0 : thm := BNames.NOT_LESS_0
def LESS_LEMMA1 : thm := BNames.LESS_LEMMA1
def LESS_SUC_REFL : thm := BNames.LESS_SUC_REFL
def LESS_EQ_SUC_REFL : thm := BNames.LESS_EQ_SUC_REFL
def LESS_EQUAL_ADD : thm := BNames.LESS_EQUAL_ADD
def LESS_EQ_IMP_LESS_SUC : thm := BNames.LESS_EQ_IMP_LESS_SUC
def LESS_MONO_ADD : thm := BNames.LESS_MONO_ADD
def LESS_SUC : thm := BNames.LESS_SUC
def LESS_ADD_1 : thm := BNames.LESS_ADD_1
def SUC_SUB1 : thm := BNames.SUC_SUB1
def LESS_ADD_SUC : thm := BNames.LESS_ADD_SUC
def OR_LESS : thm := BNames.OR_LESS
def NOT_SUC_LESS_EQ : thm := BNames.NOT_SUC_LESS_EQ
def LESS_LESS_CASES : thm := BNames.LESS_LESS_CASES
def SUB_SUB : thm := BNames.SUB_SUB
def LESS_CASES_IMP : thm := BNames.LESS_CASES_IMP
def SUB_LESS_EQ : thm := BNames.SUB_LESS_EQ
def SUB_EQ_EQ_0 : thm := BNames.SUB_EQ_EQ_0
def SUB_LEFT_LESS_EQ : thm := BNames.SUB_LEFT_LESS_EQ
def SUB_LEFT_GREATER_EQ : thm := BNames.SUB_LEFT_GREATER_EQ
def LESS_0_CASES : thm := BNames.LESS_0_CASES
def LESS_OR : thm := BNames.LESS_OR
def SUB_OLD : thm := BNames.SUB_OLD

-- Tactics
def SYM_CANON_CONV := BTactics.SYM_CANON_CONV
def IMP_SUBST_TAC := BTactics.IMP_SUBST_TAC
def EXT_CONV : term → IO (Except String thm) := fun t => (BTactics.EXT_CONV t).run
def EQUAL_TAC : HolCore.Tactics.tactic := fun g => BTactics.EQUAL_TAC g
def X_BETA_CONV := BTactics.X_BETA_CONV
def EXACT_CONV := BTactics.EXACT_CONV
def HABS_CONV : HolCore.Equal.ioconv := fun t => BTactics.HABS_CONV t
def EXPAND_TAC := BTactics.EXPAND_TAC

-- Reals1
def real_le : thm := BReals1.real_le
def REAL_10 : thm := BReals1.REAL_10
def REAL_LDISTRIB : thm := BReals1.REAL_LDISTRIB
def REAL_LT_IADD : thm := BReals1.REAL_LT_IADD
def REAL_MUL_RID : thm := BReals1.REAL_MUL_RID
def REAL_MUL_RINV : thm := BReals1.REAL_MUL_RINV
def REAL_RDISTRIB : thm := BReals1.REAL_RDISTRIB
def REAL_EQ_LADD : thm := BReals1.REAL_EQ_LADD
def REAL_EQ_RADD : thm := BReals1.REAL_EQ_RADD
def REAL_ADD_LID_UNIQ : thm := BReals1.REAL_ADD_LID_UNIQ
def REAL_ADD_RID_UNIQ : thm := BReals1.REAL_ADD_RID_UNIQ
def REAL_LNEG_UNIQ : thm := BReals1.REAL_LNEG_UNIQ
def REAL_RNEG_UNIQ : thm := BReals1.REAL_RNEG_UNIQ
def REAL_NEG_ADD : thm := BReals1.REAL_NEG_ADD
def REAL_MUL_LZERO : thm := BReals1.REAL_MUL_LZERO
def REAL_MUL_RZERO : thm := BReals1.REAL_MUL_RZERO
def REAL_NEG_LMUL : thm := BReals1.REAL_NEG_LMUL
def REAL_NEG_RMUL : thm := BReals1.REAL_NEG_RMUL
def REAL_NEG_NEG : thm := BReals1.REAL_NEG_NEG
def REAL_NEG_MUL2 : thm := BReals1.REAL_NEG_MUL2
def REAL_LT_LADD : thm := BReals1.REAL_LT_LADD
def REAL_LT_RADD : thm := BReals1.REAL_LT_RADD
def REAL_NOT_LT : thm := BReals1.REAL_NOT_LT
def REAL_LT_ANTISYM : thm := BReals1.REAL_LT_ANTISYM
def REAL_LT_GT : thm := BReals1.REAL_LT_GT
def REAL_NOT_LE : thm := BReals1.REAL_NOT_LE
def REAL_LE_TOTAL : thm := BReals1.REAL_LE_TOTAL
def REAL_LE_REFL : thm := BReals1.REAL_LE_REFL
def REAL_LE_LT : thm := BReals1.REAL_LE_LT
def REAL_LT_LE : thm := BReals1.REAL_LT_LE
def REAL_LT_IMP_LE : thm := BReals1.REAL_LT_IMP_LE
def REAL_LTE_TRANS : thm := BReals1.REAL_LTE_TRANS
def REAL_LE_TRANS : thm := BReals1.REAL_LE_TRANS
def REAL_NEG_LT0 : thm := BReals1.REAL_NEG_LT0
def REAL_NEG_GT0 : thm := BReals1.REAL_NEG_GT0
def REAL_NEG_LE0 : thm := BReals1.REAL_NEG_LE0
def REAL_NEG_GE0 : thm := BReals1.REAL_NEG_GE0
def REAL_LT_NEGTOTAL : thm := BReals1.REAL_LT_NEGTOTAL
def REAL_LE_NEGTOTAL : thm := BReals1.REAL_LE_NEGTOTAL
def REAL_LE_MUL : thm := BReals1.REAL_LE_MUL
def REAL_LE_SQUARE : thm := BReals1.REAL_LE_SQUARE
def REAL_LT_01 : thm := BReals1.REAL_LT_01
def REAL_LE_LADD : thm := BReals1.REAL_LE_LADD
def REAL_LE_RADD : thm := BReals1.REAL_LE_RADD
def REAL_LT_ADD2 : thm := BReals1.REAL_LT_ADD2
def REAL_LT_ADD : thm := BReals1.REAL_LT_ADD
def REAL_LT_ADDNEG : thm := BReals1.REAL_LT_ADDNEG
def REAL_LT_ADDNEG2 : thm := BReals1.REAL_LT_ADDNEG2
def REAL_LT_ADD1 : thm := BReals1.REAL_LT_ADD1
def REAL_SUB_ADD : thm := BReals1.REAL_SUB_ADD
def REAL_SUB_ADD2 : thm := BReals1.REAL_SUB_ADD2

-- Reals2
def REAL_SUB_REFL : thm := BReals2.REAL_SUB_REFL
def REAL_SUB_0 : thm := BReals2.REAL_SUB_0
def REAL_LE_DOUBLE : thm := BReals2.REAL_LE_DOUBLE
def REAL_LE_NEGL : thm := BReals2.REAL_LE_NEGL
def REAL_LE_NEGR : thm := BReals2.REAL_LE_NEGR
def REAL_NEG_EQ0 : thm := BReals2.REAL_NEG_EQ0
def REAL_NEG_0 : thm := BReals2.REAL_NEG_0
def REAL_NEG_SUB : thm := BReals2.REAL_NEG_SUB
def REAL_SUB_LT : thm := BReals2.REAL_SUB_LT
def REAL_SUB_LE : thm := BReals2.REAL_SUB_LE
def REAL_EQ_LMUL : thm := BReals2.REAL_EQ_LMUL
def REAL_EQ_RMUL : thm := BReals2.REAL_EQ_RMUL
def REAL_SUB_LDISTRIB : thm := BReals2.REAL_SUB_LDISTRIB
def REAL_SUB_RDISTRIB : thm := BReals2.REAL_SUB_RDISTRIB
def REAL_NEG_EQ : thm := BReals2.REAL_NEG_EQ
def REAL_NEG_MINUS1 : thm := BReals2.REAL_NEG_MINUS1
def REAL_INV_NZ : thm := BReals2.REAL_INV_NZ
def REAL_INVINV : thm := BReals2.REAL_INVINV
def REAL_LT_IMP_NE : thm := BReals2.REAL_LT_IMP_NE
def REAL_INV_POS : thm := BReals2.REAL_INV_POS
def REAL_LT_LMUL_0 : thm := BReals2.REAL_LT_LMUL_0
def REAL_LT_RMUL_0 : thm := BReals2.REAL_LT_RMUL_0
def REAL_LT_LMUL_EQ : thm := BReals2.REAL_LT_LMUL_EQ
def REAL_LT_RMUL_EQ : thm := BReals2.REAL_LT_RMUL_EQ
def REAL_LT_RMUL_IMP : thm := BReals2.REAL_LT_RMUL_IMP
def REAL_LT_LMUL_IMP : thm := BReals2.REAL_LT_LMUL_IMP
def REAL_LINV_UNIQ : thm := BReals2.REAL_LINV_UNIQ
def REAL_RINV_UNIQ : thm := BReals2.REAL_RINV_UNIQ
def REAL_NEG_INV : thm := BReals2.REAL_NEG_INV
def REAL_INV_1OVER : thm := BReals2.REAL_INV_1OVER
def REAL : thm := BReals2.REAL
def REAL_POS : thm := BReals2.REAL_POS
def REAL_LE : thm := BReals2.REAL_LE
def REAL_LT : thm := BReals2.REAL_LT
def REAL_INJ : thm := BReals2.REAL_INJ
def REAL_ADD : thm := BReals2.REAL_ADD
def REAL_MUL : thm := BReals2.REAL_MUL
def REAL_INV1 : thm := BReals2.REAL_INV1
def REAL_DIV_LZERO : thm := BReals2.REAL_DIV_LZERO
def REAL_LT_NZ : thm := BReals2.REAL_LT_NZ
def REAL_NZ_IMP_LT : thm := BReals2.REAL_NZ_IMP_LT
def REAL_LT_RDIV_0 : thm := BReals2.REAL_LT_RDIV_0
def REAL_LT_RDIV : thm := BReals2.REAL_LT_RDIV
def REAL_LT_FRACTION_0 : thm := BReals2.REAL_LT_FRACTION_0
def REAL_LT_MULTIPLE : thm := BReals2.REAL_LT_MULTIPLE
def REAL_LT_FRACTION : thm := BReals2.REAL_LT_FRACTION
def REAL_LT_HALF1 : thm := BReals2.REAL_LT_HALF1
def REAL_LT_HALF2 : thm := BReals2.REAL_LT_HALF2
def REAL_DOUBLE : thm := BReals2.REAL_DOUBLE

-- Reals3
def REAL_HALF_DOUBLE : thm := BReals3.REAL_HALF_DOUBLE
def REAL_SUB_SUB : thm := BReals3.REAL_SUB_SUB
def REAL_LT_ADD_SUB : thm := BReals3.REAL_LT_ADD_SUB
def REAL_LT_SUB_RADD : thm := BReals3.REAL_LT_SUB_RADD
def REAL_LT_SUB_LADD : thm := BReals3.REAL_LT_SUB_LADD
def REAL_LE_SUB_LADD : thm := BReals3.REAL_LE_SUB_LADD
def REAL_LE_SUB_RADD : thm := BReals3.REAL_LE_SUB_RADD
def REAL_LT_NEG2 : thm := BReals3.REAL_LT_NEG2
def REAL_LE_NEG2 : thm := BReals3.REAL_LE_NEG2
def REAL_SUB_LZERO : thm := BReals3.REAL_SUB_LZERO
def REAL_SUB_RZERO : thm := BReals3.REAL_SUB_RZERO
def REAL_LTE_ADD2 : thm := BReals3.REAL_LTE_ADD2
def REAL_LTE_ADD : thm := BReals3.REAL_LTE_ADD
def REAL_LT_MUL2_ALT : thm := BReals3.REAL_LT_MUL2_ALT
def REAL_SUB_LNEG : thm := BReals3.REAL_SUB_LNEG
def REAL_SUB_RNEG : thm := BReals3.REAL_SUB_RNEG
def REAL_SUB_NEG2 : thm := BReals3.REAL_SUB_NEG2
def REAL_SUB_TRIANGLE : thm := BReals3.REAL_SUB_TRIANGLE
def REAL_INV_MUL_WEAK : thm := BReals3.REAL_INV_MUL_WEAK
def REAL_LE_LMUL_LOCAL : thm := BReals3.REAL_LE_LMUL_LOCAL
def REAL_LE_RMUL_EQ : thm := BReals3.REAL_LE_RMUL_EQ
def REAL_SUB_INV2 : thm := BReals3.REAL_SUB_INV2
def REAL_SUB_SUB2 : thm := BReals3.REAL_SUB_SUB2
def REAL_MEAN : thm := BReals3.REAL_MEAN
def REAL_EQ_LMUL2 : thm := BReals3.REAL_EQ_LMUL2
def REAL_LE_MUL2V : thm := BReals3.REAL_LE_MUL2V
def REAL_LE_LDIV : thm := BReals3.REAL_LE_LDIV
def REAL_LE_RDIV : thm := BReals3.REAL_LE_RDIV
def REAL_LT_1 : thm := BReals3.REAL_LT_1
def REAL_LE_LMUL_IMP : thm := BReals3.REAL_LE_LMUL_IMP
def REAL_LE_RMUL_IMP : thm := BReals3.REAL_LE_RMUL_IMP
def REAL_INV_LT1 : thm := BReals3.REAL_INV_LT1
def REAL_LT_IMP_NZ : thm := BReals3.REAL_LT_IMP_NZ
def REAL_EQ_RMUL_IMP : thm := BReals3.REAL_EQ_RMUL_IMP
def REAL_EQ_LMUL_IMP : thm := BReals3.REAL_EQ_LMUL_IMP
def REAL_FACT_NZ : thm := BReals3.REAL_FACT_NZ
def REAL_POSSQ : thm := BReals3.REAL_POSSQ
def REAL_SUMSQ : thm := BReals3.REAL_SUMSQ
def REAL_EQ_NEG : thm := BReals3.REAL_EQ_NEG
def REAL_DIV_MUL2 : thm := BReals3.REAL_DIV_MUL2
def REAL_MIDDLE1 : thm := BReals3.REAL_MIDDLE1
def REAL_MIDDLE2 : thm := BReals3.REAL_MIDDLE2

-- Abs
def ABS_ZERO : thm := BAbs.ABS_ZERO
def ABS_0 : thm := BAbs.ABS_0
def ABS_1 : thm := BAbs.ABS_1
def ABS_NEG : thm := BAbs.ABS_NEG
def ABS_TRIANGLE : thm := BAbs.ABS_TRIANGLE
def ABS_POS : thm := BAbs.ABS_POS
def ABS_MUL : thm := BAbs.ABS_MUL
def ABS_LT_MUL2 : thm := BAbs.ABS_LT_MUL2
def ABS_SUB : thm := BAbs.ABS_SUB
def ABS_NZ : thm := BAbs.ABS_NZ
def ABS_INV : thm := BAbs.ABS_INV
def ABS_ABS : thm := BAbs.ABS_ABS
def ABS_LE : thm := BAbs.ABS_LE
def ABS_REFL : thm := BAbs.ABS_REFL
def ABS_N : thm := BAbs.ABS_N
def ABS_BETWEEN : thm := BAbs.ABS_BETWEEN
def ABS_BOUND : thm := BAbs.ABS_BOUND
def ABS_STILLNZ : thm := BAbs.ABS_STILLNZ
def ABS_CASES : thm := BAbs.ABS_CASES
def ABS_BETWEEN1 : thm := BAbs.ABS_BETWEEN1
def ABS_SIGN : thm := BAbs.ABS_SIGN
def ABS_SIGN2 : thm := BAbs.ABS_SIGN2
def ABS_DIV : thm := BAbs.ABS_DIV
def ABS_CIRCLE : thm := BAbs.ABS_CIRCLE
def REAL_SUB_ABS : thm := BAbs.REAL_SUB_ABS
def ABS_SUB_ABS : thm := BAbs.ABS_SUB_ABS
def ABS_BETWEEN2 : thm := BAbs.ABS_BETWEEN2
def ABS_BOUNDS : thm := BAbs.ABS_BOUNDS

-- Pow
def pow : thm := BPow.pow
def POW_0 : thm := BPow.POW_0
def POW_NZ : thm := BPow.POW_NZ
def POW_INV : thm := BPow.POW_INV
def POW_ABS : thm := BPow.POW_ABS
def POW_PLUS1 : thm := BPow.POW_PLUS1
def POW_ADD : thm := BPow.POW_ADD
def POW_1 : thm := BPow.POW_1
def POW_2 : thm := BPow.POW_2
def POW_POS : thm := BPow.POW_POS
def POW_LE : thm := BPow.POW_LE
def POW_M1 : thm := BPow.POW_M1
def POW_MUL : thm := BPow.POW_MUL
def REAL_LE_SQUARE_POW : thm := BPow.REAL_LE_SQUARE_POW
def ABS_POW2 : thm := BPow.ABS_POW2
def REAL_LE1_POW2 : thm := BPow.REAL_LE1_POW2
def REAL_LT1_POW2 : thm := BPow.REAL_LT1_POW2
def POW_POS_LT : thm := BPow.POW_POS_LT
def POW_2_LE1 : thm := BPow.POW_2_LE1
def POW_2_LT : thm := BPow.POW_2_LT
def POW_MINUS1 : thm := BPow.POW_MINUS1
def REAL_SUP_EXISTS : thm := BPow.REAL_SUP_EXISTS
def sup_def : thm := BPow.sup_def
def sup : thm := BPow.sup
def REAL_SUP : thm := BPow.REAL_SUP
def REAL_SUP_UBOUND : thm := BPow.REAL_SUP_UBOUND
def SETOK_LE_LT : thm := BPow.SETOK_LE_LT
def REAL_SUP_LE : thm := BPow.REAL_SUP_LE
def REAL_SUP_UBOUND_LE : thm := BPow.REAL_SUP_UBOUND_LE
def REAL_ARCH_SIMPLE : thm := BPow.REAL_ARCH_SIMPLE
def REAL_ARCH : thm := BPow.REAL_ARCH
def REAL_ARCH_LEAST : thm := BPow.REAL_ARCH_LEAST
def REAL_POW_LBOUND : thm := BPow.REAL_POW_LBOUND
def REAL_ARCH_POW : thm := BPow.REAL_ARCH_POW
def REAL_ARCH_POW2 : thm := BPow.REAL_ARCH_POW2

-- Sums
def sum_EXISTS : thm := BSums.sum_EXISTS
def sum_DEF : thm := BSums.sum_DEF
def sum : thm := BSums.sum
def PSUM_SUM : thm := BSums.PSUM_SUM
def PSUM_SUM_NUMSEG : thm := BSums.PSUM_SUM_NUMSEG
def SUM_TWO : thm := BSums.SUM_TWO
def SUM_DIFF : thm := BSums.SUM_DIFF
def ABS_SUM : thm := BSums.ABS_SUM
def SUM_LE : thm := BSums.SUM_LE
def SUM_EQ : thm := BSums.SUM_EQ
def SUM_POS : thm := BSums.SUM_POS
def SUM_POS_GEN : thm := BSums.SUM_POS_GEN
def SUM_ABS : thm := BSums.SUM_ABS
def SUM_ABS_LE : thm := BSums.SUM_ABS_LE
def SUM_ZERO : thm := BSums.SUM_ZERO
def SUM_ADD : thm := BSums.SUM_ADD
def SUM_CMUL : thm := BSums.SUM_CMUL
def SUM_NEG : thm := BSums.SUM_NEG
def SUM_SUB : thm := BSums.SUM_SUB
def SUM_SUBST : thm := BSums.SUM_SUBST
def SUM_NSUB : thm := BSums.SUM_NSUB
def SUM_BOUND : thm := BSums.SUM_BOUND
def SUM_GROUP : thm := BSums.SUM_GROUP
def SUM_1 : thm := BSums.SUM_1
def SUM_2 : thm := BSums.SUM_2
def SUM_OFFSET : thm := BSums.SUM_OFFSET
def SUM_REINDEX : thm := BSums.SUM_REINDEX
def SUM_0 : thm := BSums.SUM_0
def SUM_CANCEL : thm := BSums.SUM_CANCEL
def SUM_HORNER : thm := BSums.SUM_HORNER
def SUM_CONST : thm := BSums.SUM_CONST
def SUM_SPLIT : thm := BSums.SUM_SPLIT
def SUM_SWAP : thm := BSums.SUM_SWAP
def SUM_EQ_0 : thm := BSums.SUM_EQ_0
def SUM_MORETERMS_EQ : thm := BSums.SUM_MORETERMS_EQ
def SUM_DIFFERENCES_EQ : thm := BSums.SUM_DIFFERENCES_EQ

-- SumConv
def REAL_SUM_CONV : HolCore.Equal.ioconv := fun t => BSumConv.REAL_SUM_CONV t
def REAL_HORNER_SUM_CONV : HolCore.Equal.ioconv := fun t => BSumConv.REAL_HORNER_SUM_CONV t

-- Topology
def re_Union : thm := BTopology.re_Union
def re_union : thm := BTopology.re_union
def re_intersect : thm := BTopology.re_intersect
def re_null : thm := BTopology.re_null
def re_universe : thm := BTopology.re_universe
def re_subset : thm := BTopology.re_subset
def re_compl : thm := BTopology.re_compl
def SUBSETA_REFL : thm := BTopology.SUBSETA_REFL
def COMPL_MEM : thm := BTopology.COMPL_MEM
def SUBSETA_ANTISYM : thm := BTopology.SUBSETA_ANTISYM
def SUBSETA_TRANS : thm := BTopology.SUBSETA_TRANS
def istopology : thm := BTopology.istopology
def topology_tybij : thm := BTopology.topology_tybij
def TOPOLOGY : thm := BTopology.TOPOLOGY
def TOPOLOGY_UNION : thm := BTopology.TOPOLOGY_UNION
def neigh : thm := BTopology.neigh
def OPEN_OWN_NEIGH : thm := BTopology.OPEN_OWN_NEIGH
def OPEN_UNOPEN : thm := BTopology.OPEN_UNOPEN
def OPEN_SUBOPEN : thm := BTopology.OPEN_SUBOPEN
def OPEN_NEIGH : thm := BTopology.OPEN_NEIGH
def closed : thm := BTopology.closed
def limpt : thm := BTopology.limpt
def CLOSED_LIMPT : thm := BTopology.CLOSED_LIMPT
def ismet : thm := BTopology.ismet
def metric_tybij : thm := BTopology.metric_tybij
def METRIC_ISMET : thm := BTopology.METRIC_ISMET
def METRIC_ZERO : thm := BTopology.METRIC_ZERO
def METRIC_SAME : thm := BTopology.METRIC_SAME
def METRIC_POS : thm := BTopology.METRIC_POS
def METRIC_SYM : thm := BTopology.METRIC_SYM
def METRIC_TRIANGLE : thm := BTopology.METRIC_TRIANGLE
def METRIC_NZ : thm := BTopology.METRIC_NZ

-- MetricTop
def mtop : thm := BMetricTop.mtop
def mtop_istopology : thm := BMetricTop.mtop_istopology
def MTOP_OPEN : thm := BMetricTop.MTOP_OPEN
def ball : thm := BMetricTop.ball
def BALL_OPEN : thm := BMetricTop.BALL_OPEN
def BALL_NEIGH : thm := BMetricTop.BALL_NEIGH
def MTOP_LIMPT : thm := BMetricTop.MTOP_LIMPT
def ISMET_R1 : thm := BMetricTop.ISMET_R1
def mr1 : thm := BMetricTop.mr1
def MR1_DEF : thm := BMetricTop.MR1_DEF
def MR1_ADD : thm := BMetricTop.MR1_ADD
def MR1_SUB : thm := BMetricTop.MR1_SUB
def MR1_ADD_LE : thm := BMetricTop.MR1_ADD_LE
def MR1_SUB_LE : thm := BMetricTop.MR1_SUB_LE
def MR1_ADD_LT : thm := BMetricTop.MR1_ADD_LT
def MR1_SUB_LT : thm := BMetricTop.MR1_SUB_LT
def MR1_BETWEEN1 : thm := BMetricTop.MR1_BETWEEN1
def MR1_LIMPT : thm := BMetricTop.MR1_LIMPT

-- Nets
def dorder : thm := BNets.dorder
def tends : thm := BNets.tends
def bounded : thm := BNets.bounded
def tendsto : thm := BNets.tendsto
def DORDER_LEMMA : thm := BNets.DORDER_LEMMA
def DORDER_THEN := BNets.DORDER_THEN
def DORDER_NGE : thm := BNets.DORDER_NGE
def DORDER_TENDSTO : thm := BNets.DORDER_TENDSTO
def MTOP_TENDS : thm := BNets.MTOP_TENDS
def MTOP_TENDS_UNIQ : thm := BNets.MTOP_TENDS_UNIQ
def SEQ_TENDS : thm := BNets.SEQ_TENDS
def LIM_TENDS : thm := BNets.LIM_TENDS
def LIM_TENDS2 : thm := BNets.LIM_TENDS2
def MR1_BOUNDED : thm := BNets.MR1_BOUNDED
def NET_NULL : thm := BNets.NET_NULL
def NET_CONV_BOUNDED : thm := BNets.NET_CONV_BOUNDED
def NET_CONV_NZ : thm := BNets.NET_CONV_NZ
def NET_CONV_IBOUNDED : thm := BNets.NET_CONV_IBOUNDED

-- NetArith
def NET_NULL_ADD : thm := BNetArith.NET_NULL_ADD
def NET_NULL_MUL : thm := BNetArith.NET_NULL_MUL
def NET_NULL_CMUL : thm := BNetArith.NET_NULL_CMUL
def NET_ADD : thm := BNetArith.NET_ADD
def NET_NEG : thm := BNetArith.NET_NEG
def NET_SUB : thm := BNetArith.NET_SUB
def NET_MUL : thm := BNetArith.NET_MUL
def NET_INV : thm := BNetArith.NET_INV
def NET_DIV : thm := BNetArith.NET_DIV
def NET_ABS : thm := BNetArith.NET_ABS
def NET_SUM : thm := BNetArith.NET_SUM
def NET_LE : thm := BNetArith.NET_LE

-- Seqs
def tends_num_real : thm := BSeqs.tends_num_real
def SEQ : thm := BSeqs.SEQ
def SEQ_CONST : thm := BSeqs.SEQ_CONST
def SEQ_ADD : thm := BSeqs.SEQ_ADD
def SEQ_MUL : thm := BSeqs.SEQ_MUL
def SEQ_NEG : thm := BSeqs.SEQ_NEG
def SEQ_INV : thm := BSeqs.SEQ_INV
def SEQ_SUB : thm := BSeqs.SEQ_SUB
def SEQ_DIV : thm := BSeqs.SEQ_DIV
def SEQ_UNIQ : thm := BSeqs.SEQ_UNIQ
def SEQ_NULL : thm := BSeqs.SEQ_NULL
def SEQ_SUM : thm := BSeqs.SEQ_SUM
def SEQ_TRANSFORM : thm := BSeqs.SEQ_TRANSFORM
def convergent : thm := BSeqs.convergent
def cauchy : thm := BSeqs.cauchy
def lim : thm := BSeqs.lim
def SEQ_LIM : thm := BSeqs.SEQ_LIM
def subseq : thm := BSeqs.subseq
def SUBSEQ_SUC : thm := BSeqs.SUBSEQ_SUC
def mono : thm := BSeqs.mono
def MONO_SUC : thm := BSeqs.MONO_SUC
def MAX_LEMMA : thm := BSeqs.MAX_LEMMA
def SEQ_BOUNDED : thm := BSeqs.SEQ_BOUNDED
def SEQ_BOUNDED_2 : thm := BSeqs.SEQ_BOUNDED_2
def SEQ_CBOUNDED : thm := BSeqs.SEQ_CBOUNDED
def SEQ_ICONV : thm := BSeqs.SEQ_ICONV

-- Seqs2
def SEQ_NEG_CONV : thm := BSeqs2.SEQ_NEG_CONV
def SEQ_NEG_BOUNDED : thm := BSeqs2.SEQ_NEG_BOUNDED
def SEQ_BCONV : thm := BSeqs2.SEQ_BCONV
def SEQ_MONOSUB : thm := BSeqs2.SEQ_MONOSUB
def SEQ_SBOUNDED : thm := BSeqs2.SEQ_SBOUNDED
def SEQ_SUBLE : thm := BSeqs2.SEQ_SUBLE
def SEQ_DIRECT : thm := BSeqs2.SEQ_DIRECT
def SEQ_CAUCHY : thm := BSeqs2.SEQ_CAUCHY
def SEQ_LE : thm := BSeqs2.SEQ_LE
def SEQ_LE_0 : thm := BSeqs2.SEQ_LE_0

-- SeqLim
def SEQ_SUC : thm := BSeqLim.SEQ_SUC
def SEQ_ABS : thm := BSeqLim.SEQ_ABS
def SEQ_ABS_IMP : thm := BSeqLim.SEQ_ABS_IMP
def SEQ_INV0 : thm := BSeqLim.SEQ_INV0
def SEQ_POWER_ABS : thm := BSeqLim.SEQ_POWER_ABS
def SEQ_POWER : thm := BSeqLim.SEQ_POWER
def SEQ_HARMONIC : thm := BSeqLim.SEQ_HARMONIC
def SEQ_SUBSEQ : thm := BSeqLim.SEQ_SUBSEQ
def SEQ_POW : thm := BSeqLim.SEQ_POW
def NEST_LEMMA : thm := BSeqLim.NEST_LEMMA
def NEST_LEMMA_UNIQ : thm := BSeqLim.NEST_LEMMA_UNIQ

-- Series1
def BOLZANO_LEMMA : thm := BSeries1.BOLZANO_LEMMA
def BOLZANO_LEMMA_ALT : thm := BSeries1.BOLZANO_LEMMA_ALT
def sums : thm := BSeries1.sums
def summable : thm := BSeries1.summable
def suminf : thm := BSeries1.suminf
def SUM_SUMMABLE : thm := BSeries1.SUM_SUMMABLE
def SUMMABLE_SUM : thm := BSeries1.SUMMABLE_SUM
def SUM_UNIQ : thm := BSeries1.SUM_UNIQ
def SER_UNIQ : thm := BSeries1.SER_UNIQ
def SER_0 : thm := BSeries1.SER_0
def SER_POS_LE : thm := BSeries1.SER_POS_LE
def SER_POS_LT : thm := BSeries1.SER_POS_LT
def SER_GROUP : thm := BSeries1.SER_GROUP
def SER_PAIR : thm := BSeries1.SER_PAIR
def SER_OFFSET : thm := BSeries1.SER_OFFSET
def SER_OFFSET_REV : thm := BSeries1.SER_OFFSET_REV

-- Series2
def SER_POS_LT_PAIR : thm := BSeries2.SER_POS_LT_PAIR
def SER_ADD : thm := BSeries2.SER_ADD
def SER_CMUL : thm := BSeries2.SER_CMUL
def SER_NEG : thm := BSeries2.SER_NEG
def SER_SUB : thm := BSeries2.SER_SUB
def SER_CDIV : thm := BSeries2.SER_CDIV
def SER_CAUCHY : thm := BSeries2.SER_CAUCHY
def SER_ZERO : thm := BSeries2.SER_ZERO
def SER_COMPAR : thm := BSeries2.SER_COMPAR
def SER_COMPARA : thm := BSeries2.SER_COMPARA
def SER_LE : thm := BSeries2.SER_LE
def SER_LE2 : thm := BSeries2.SER_LE2
def SER_ACONV : thm := BSeries2.SER_ACONV
def SER_ABS : thm := BSeries2.SER_ABS
def GP_FINITE : thm := BSeries2.GP_FINITE
def GP : thm := BSeries2.GP
def ABS_NEG_LEMMA : thm := BSeries2.ABS_NEG_LEMMA
def SER_RATIO : thm := BSeries2.SER_RATIO
def SEQ_TRUNCATION : thm := BSeries2.SEQ_TRUNCATION

-- Lims
def tends_real_real : thm := BLims.tends_real_real
def LIM : thm := BLims.LIM
def LIM_CONST : thm := BLims.LIM_CONST
def LIM_ADD : thm := BLims.LIM_ADD
def LIM_MUL : thm := BLims.LIM_MUL
def LIM_NEG : thm := BLims.LIM_NEG
def LIM_INV : thm := BLims.LIM_INV
def LIM_SUB : thm := BLims.LIM_SUB
def LIM_DIV : thm := BLims.LIM_DIV
def LIM_NULL : thm := BLims.LIM_NULL
def LIM_SUM : thm := BLims.LIM_SUM
def LIM_X : thm := BLims.LIM_X
def LIM_UNIQ : thm := BLims.LIM_UNIQ
def LIM_EQUAL : thm := BLims.LIM_EQUAL
def LIM_TRANSFORM : thm := BLims.LIM_TRANSFORM
def diffl : thm := BLims.diffl
def contl : thm := BLims.contl
def differentiable : thm := BLims.differentiable
def DIFF_UNIQ : thm := BLims.DIFF_UNIQ
def DIFF_CONT : thm := BLims.DIFF_CONT
def CONTL_LIM : thm := BLims.CONTL_LIM
def CONT_X : thm := BLims.CONT_X
def CONT_CONST : thm := BLims.CONT_CONST
def CONT_ADD : thm := BLims.CONT_ADD
def CONT_MUL : thm := BLims.CONT_MUL
def CONT_NEG : thm := BLims.CONT_NEG
def CONT_INV : thm := BLims.CONT_INV
def CONT_SUB : thm := BLims.CONT_SUB
def CONT_DIV : thm := BLims.CONT_DIV
def CONT_ABS : thm := BLims.CONT_ABS
def CONT_COMPOSE : thm := BLims.CONT_COMPOSE

-- Diffs
def IVT : thm := BDiffs.IVT
def IVT2 : thm := BDiffs.IVT2
def DIFF_CONST : thm := BDiffs.DIFF_CONST
def DIFF_ADD : thm := BDiffs.DIFF_ADD
def DIFF_MUL : thm := BDiffs.DIFF_MUL
def DIFF_CMUL : thm := BDiffs.DIFF_CMUL
def DIFF_NEG : thm := BDiffs.DIFF_NEG
def DIFF_SUB : thm := BDiffs.DIFF_SUB
def DIFF_CARAT : thm := BDiffs.DIFF_CARAT
def DIFF_CHAIN : thm := BDiffs.DIFF_CHAIN
def DIFF_X : thm := BDiffs.DIFF_X
def DIFF_POW : thm := BDiffs.DIFF_POW
def DIFF_XM1 : thm := BDiffs.DIFF_XM1
def DIFF_INV : thm := BDiffs.DIFF_INV
def DIFF_DIV : thm := BDiffs.DIFF_DIV
def DIFF_SUM : thm := BDiffs.DIFF_SUM

-- Cont
def CONT_BOUNDED : thm := BCont.CONT_BOUNDED
def CONT_BOUNDED_ABS : thm := BCont.CONT_BOUNDED_ABS
def CONT_HASSUP : thm := BCont.CONT_HASSUP
def CONT_ATTAINS : thm := BCont.CONT_ATTAINS
def CONT_ATTAINS2 : thm := BCont.CONT_ATTAINS2
def CONT_ATTAINS_ALL : thm := BCont.CONT_ATTAINS_ALL

-- Mvt
def DIFF_LINC : thm := BMvt.DIFF_LINC
def DIFF_LDEC : thm := BMvt.DIFF_LDEC
def DIFF_LMAX : thm := BMvt.DIFF_LMAX
def DIFF_LMIN : thm := BMvt.DIFF_LMIN
def DIFF_LCONST : thm := BMvt.DIFF_LCONST
def INTERVAL_LEMMA_LT : thm := BMvt.INTERVAL_LEMMA_LT
def INTERVAL_LEMMA : thm := BMvt.INTERVAL_LEMMA
def ROLLE : thm := BMvt.ROLLE
def MVT_LEMMA : thm := BMvt.MVT_LEMMA
def MVT : thm := BMvt.MVT
def MVT_ALT : thm := BMvt.MVT_ALT
def DIFF_ISCONST_END : thm := BMvt.DIFF_ISCONST_END
def DIFF_ISCONST : thm := BMvt.DIFF_ISCONST
def DIFF_ISCONST_END_SIMPLE : thm := BMvt.DIFF_ISCONST_END_SIMPLE
def DIFF_ISCONST_ALL : thm := BMvt.DIFF_ISCONST_ALL
def INTERVAL_ABS : thm := BMvt.INTERVAL_ABS

-- Inverse
def CONT_INJ_LEMMA : thm := BInverse.CONT_INJ_LEMMA
def CONT_INJ_LEMMA2 : thm := BInverse.CONT_INJ_LEMMA2
def CONT_INJ_RANGE : thm := BInverse.CONT_INJ_RANGE
def CONT_INVERSE : thm := BInverse.CONT_INVERSE
def DIFF_INVERSE : thm := BInverse.DIFF_INVERSE
def DIFF_INVERSE_LT : thm := BInverse.DIFF_INVERSE_LT

-- Uniform
def IVT_DERIVATIVE_0 : thm := BUniform.IVT_DERIVATIVE_0
def IVT_DERIVATIVE_POS : thm := BUniform.IVT_DERIVATIVE_POS
def IVT_DERIVATIVE_NEG : thm := BUniform.IVT_DERIVATIVE_NEG
def SEQ_CONT_UNIFORM : thm := BUniform.SEQ_CONT_UNIFORM
def SER_COMPARA_UNIFORM : thm := BUniform.SER_COMPARA_UNIFORM
def SER_COMPARA_UNIFORM_WEAK : thm := BUniform.SER_COMPARA_UNIFORM_WEAK
def CONTL : thm := BUniform.CONTL
def CONTL_SEQ : thm := BUniform.CONTL_SEQ
def SUP_INTERVAL : thm := BUniform.SUP_INTERVAL
def CONT_UNIFORM : thm := BUniform.CONT_UNIFORM
def CONT_UNIFORM_STRONG : thm := BUniform.CONT_UNIFORM_STRONG












































/-- `needs "Library/analysis.ml"`: already done by importing this module. -/
def ensureAnalysis : IO Unit := pure ()

end SessionLibrary.Analysis
