/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/analysis.ml.                                -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Analysis.lean

  The `unsafe` half of the analysis.ml translation: it supplies
  HolLibrary.Analysis' dependencies from Session, builds each bundle once,
  in file order, and exports every name under its HOL Light name.
  `ensureAnalysis` is `needs "Library/analysis.ml"`.

  analysis.ml rebinds about a hundred core names (REAL_LE_TRANS, SUM_LE,
  sum, sup, EXPAND_TAC, ...); the versions here are analysis.ml's, so with
  both `Session` and `SessionLibrary.Analysis` open, qualify them.

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/Analysis.lean by tools/analysisdiff/gen_session.py (bookkeeping
  only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.Analysis

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Analysis

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems analysis.ml uses, ADD to REAL_ADD_SYM. -/
unsafe def core1 (_ : Unit) : HolLibrary.Analysis.CoreThms1 where
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
unsafe def core2 (_ : Unit) : HolLibrary.Analysis.CoreThms2 where
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
unsafe def core3 (_ : Unit) : HolLibrary.Analysis.CoreThms3 where
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
  sup := Session.«sup»-- @@CORE END

/-- What analysis.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Analysis.AnalysisDeps where
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
  core1 := core1 ()
  core2 := core2 ()
  core3 := core3 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`): HOL Light has loaded all of hol_lib.ml before
    `needs "Library/analysis.ml"`, and analysis.ml's parser changes
    (priorities, infixes, `sum` overloading) must not apply to core layers
    that Session would otherwise build later, on first use. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.Analysis: {name}"

/- The bundles, in analysis.ml order.  Each forces the one before it, so that
   any bundle builds every earlier one first, as HOL Light's load does. -/

-- @@BUNDLES BEGIN
initialize theCompat : IO.Ref (Option HolLibrary.Analysis.Compat) ← IO.mkRef none
unsafe def BCompat : HolLibrary.Analysis.Compat :=
  cached theCompat "setupCompat" fun _ => do
    (HolLibrary.Analysis.setupCompat (deps ())).run

initialize theNames : IO.Ref (Option HolLibrary.Analysis.Names) ← IO.mkRef none
unsafe def BNames : HolLibrary.Analysis.Names :=
  cached theNames "setupNames" fun _ => do
    let _ ← IO.mkRef BCompat.dest_neg_imp
    (HolLibrary.Analysis.setupNames (deps ())).run

initialize theTactics : IO.Ref (Option HolLibrary.Analysis.Tactics) ← IO.mkRef none
unsafe def BTactics : HolLibrary.Analysis.Tactics :=
  cached theTactics "setupTactics" fun _ => do
    let _ ← IO.mkRef BNames.LESS_EQUAL_ANTISYM
    (HolLibrary.Analysis.setupTactics (deps ()) BCompat).run

initialize theReals1 : IO.Ref (Option HolLibrary.Analysis.Reals1) ← IO.mkRef none
unsafe def BReals1 : HolLibrary.Analysis.Reals1 :=
  cached theReals1 "setupReals1" fun _ => do
    let _ ← IO.mkRef BTactics.SYM_CANON_CONV
    (HolLibrary.Analysis.setupReals1 (deps ()) BCompat).run

initialize theReals2 : IO.Ref (Option HolLibrary.Analysis.Reals2) ← IO.mkRef none
unsafe def BReals2 : HolLibrary.Analysis.Reals2 :=
  cached theReals2 "setupReals2" fun _ => do
    let _ ← IO.mkRef BReals1.real_le
    (HolLibrary.Analysis.setupReals2 (deps ()) BNames BReals1).run

initialize theReals3 : IO.Ref (Option HolLibrary.Analysis.Reals3) ← IO.mkRef none
unsafe def BReals3 : HolLibrary.Analysis.Reals3 :=
  cached theReals3 "setupReals3" fun _ => do
    let _ ← IO.mkRef BReals2.REAL_SUB_REFL
    (HolLibrary.Analysis.setupReals3 (deps ()) BTactics BReals1 BReals2).run

initialize theAbs : IO.Ref (Option HolLibrary.Analysis.Abs) ← IO.mkRef none
unsafe def BAbs : HolLibrary.Analysis.Abs :=
  cached theAbs "setupAbs" fun _ => do
    let _ ← IO.mkRef BReals3.REAL_HALF_DOUBLE
    (HolLibrary.Analysis.setupAbs (deps ()) BNames BReals1 BReals2 BReals3).run

initialize thePow : IO.Ref (Option HolLibrary.Analysis.Pow) ← IO.mkRef none
unsafe def BPow : HolLibrary.Analysis.Pow :=
  cached thePow "setupPow" fun _ => do
    let _ ← IO.mkRef BAbs.ABS_ZERO
    (HolLibrary.Analysis.setupPow (deps ()) BCompat BNames BReals1 BReals2 BReals3 BAbs).run

initialize theSums : IO.Ref (Option HolLibrary.Analysis.Sums) ← IO.mkRef none
unsafe def BSums : HolLibrary.Analysis.Sums :=
  cached theSums "setupSums" fun _ => do
    let _ ← IO.mkRef BPow.pow
    (HolLibrary.Analysis.setupSums (deps ()) BReals1 BReals2).run

initialize theSumConv : IO.Ref (Option HolLibrary.Analysis.SumConv) ← IO.mkRef none
unsafe def BSumConv : HolLibrary.Analysis.SumConv :=
  cached theSumConv "setupSumConv" fun _ => do
    let _ ← IO.mkRef BSums.sum_EXISTS
    (HolLibrary.Analysis.setupSumConv (deps ()) BSums).run

initialize theTopology : IO.Ref (Option HolLibrary.Analysis.Topology) ← IO.mkRef none
unsafe def BTopology : HolLibrary.Analysis.Topology :=
  cached theTopology "setupTopology" fun _ => do
    let _ ← IO.mkRef BSumConv.REAL_SUM_CONV
    (HolLibrary.Analysis.setupTopology (deps ()) BCompat BTactics BReals1).run

initialize theMetricTop : IO.Ref (Option HolLibrary.Analysis.MetricTop) ← IO.mkRef none
unsafe def BMetricTop : HolLibrary.Analysis.MetricTop :=
  cached theMetricTop "setupMetricTop" fun _ => do
    let _ ← IO.mkRef BTopology.re_Union
    (HolLibrary.Analysis.setupMetricTop (deps ()) BReals1 BReals2 BReals3 BAbs BTopology).run

initialize theNets : IO.Ref (Option HolLibrary.Analysis.Nets) ← IO.mkRef none
unsafe def BNets : HolLibrary.Analysis.Nets :=
  cached theNets "setupNets" fun _ => do
    let _ ← IO.mkRef BMetricTop.mtop
    (HolLibrary.Analysis.setupNets (deps ()) BCompat BTactics BReals1 BReals2 BReals3 BAbs BTopology BMetricTop).run

initialize theNetArith : IO.Ref (Option HolLibrary.Analysis.NetArith) ← IO.mkRef none
unsafe def BNetArith : HolLibrary.Analysis.NetArith :=
  cached theNetArith "setupNetArith" fun _ => do
    let _ ← IO.mkRef BNets.dorder
    (HolLibrary.Analysis.setupNetArith (deps ()) BCompat BNames BTactics BReals1 BReals2 BReals3 BAbs BSums BMetricTop BNets).run

initialize theSeqs : IO.Ref (Option HolLibrary.Analysis.Seqs) ← IO.mkRef none
unsafe def BSeqs : HolLibrary.Analysis.Seqs :=
  cached theSeqs "setupSeqs" fun _ => do
    let _ ← IO.mkRef BNetArith.NET_NULL_ADD
    (HolLibrary.Analysis.setupSeqs (deps ()) BCompat BNames BReals1 BReals2 BReals3 BAbs BPow BMetricTop BNets BNetArith).run

initialize theSeqs2 : IO.Ref (Option HolLibrary.Analysis.Seqs2) ← IO.mkRef none
unsafe def BSeqs2 : HolLibrary.Analysis.Seqs2 :=
  cached theSeqs2 "setupSeqs2" fun _ => do
    let _ ← IO.mkRef BSeqs.tends_num_real
    (HolLibrary.Analysis.setupSeqs2 (deps ()) BCompat BNames BReals1 BReals2 BReals3 BAbs BNets BNetArith BSeqs).run

initialize theSeqLim : IO.Ref (Option HolLibrary.Analysis.SeqLim) ← IO.mkRef none
unsafe def BSeqLim : HolLibrary.Analysis.SeqLim :=
  cached theSeqLim "setupSeqLim" fun _ => do
    let _ ← IO.mkRef BSeqs2.SEQ_NEG_CONV
    (HolLibrary.Analysis.setupSeqLim (deps ()) BNames BTactics BReals1 BReals2 BReals3 BAbs BPow BNetArith BSeqs BSeqs2).run

initialize theSeries1 : IO.Ref (Option HolLibrary.Analysis.Series1) ← IO.mkRef none
unsafe def BSeries1 : HolLibrary.Analysis.Series1 :=
  cached theSeries1 "setupSeries1" fun _ => do
    let _ ← IO.mkRef BSeqLim.SEQ_SUC
    (HolLibrary.Analysis.setupSeries1 (deps ()) BNames BReals1 BReals2 BReals3 BAbs BPow BSums BSeqs BSeqs2 BSeqLim).run

initialize theSeries2 : IO.Ref (Option HolLibrary.Analysis.Series2) ← IO.mkRef none
unsafe def BSeries2 : HolLibrary.Analysis.Series2 :=
  cached theSeries2 "setupSeries2" fun _ => do
    let _ ← IO.mkRef BSeries1.BOLZANO_LEMMA
    (HolLibrary.Analysis.setupSeries2 (deps ()) BNames BTactics BReals1 BReals2 BReals3 BAbs BPow BSums BSeqs BSeqs2 BSeqLim BSeries1).run

initialize theLims : IO.Ref (Option HolLibrary.Analysis.Lims) ← IO.mkRef none
unsafe def BLims : HolLibrary.Analysis.Lims :=
  cached theLims "setupLims" fun _ => do
    let _ ← IO.mkRef BSeries2.SER_POS_LT_PAIR
    (HolLibrary.Analysis.setupLims (deps ()) BTactics BReals1 BReals2 BReals3 BAbs BTopology BMetricTop BNets BNetArith).run

initialize theDiffs : IO.Ref (Option HolLibrary.Analysis.Diffs) ← IO.mkRef none
unsafe def BDiffs : HolLibrary.Analysis.Diffs :=
  cached theDiffs "setupDiffs" fun _ => do
    let _ ← IO.mkRef BLims.tends_real_real
    (HolLibrary.Analysis.setupDiffs (deps ()) BCompat BNames BTactics BReals1 BReals2 BReals3 BAbs BPow BSums BSeries1 BLims).run

initialize theCont : IO.Ref (Option HolLibrary.Analysis.Cont) ← IO.mkRef none
unsafe def BCont : HolLibrary.Analysis.Cont :=
  cached theCont "setupCont" fun _ => do
    let _ ← IO.mkRef BDiffs.IVT
    (HolLibrary.Analysis.setupCont (deps ()) BCompat BTactics BReals1 BReals2 BReals3 BAbs BPow BSeries1 BLims BDiffs).run

initialize theMvt : IO.Ref (Option HolLibrary.Analysis.Mvt) ← IO.mkRef none
unsafe def BMvt : HolLibrary.Analysis.Mvt :=
  cached theMvt "setupMvt" fun _ => do
    let _ ← IO.mkRef BCont.CONT_BOUNDED
    (HolLibrary.Analysis.setupMvt (deps ()) BCompat BTactics BReals1 BReals2 BReals3 BAbs BLims BDiffs BCont).run

initialize theInverse : IO.Ref (Option HolLibrary.Analysis.Inverse) ← IO.mkRef none
unsafe def BInverse : HolLibrary.Analysis.Inverse :=
  cached theInverse "setupInverse" fun _ => do
    let _ ← IO.mkRef BMvt.DIFF_LINC
    (HolLibrary.Analysis.setupInverse (deps ()) BReals1 BReals2 BReals3 BAbs BLims BDiffs BCont BMvt).run

initialize theUniform : IO.Ref (Option HolLibrary.Analysis.Uniform) ← IO.mkRef none
unsafe def BUniform : HolLibrary.Analysis.Uniform :=
  cached theUniform "setupUniform" fun _ => do
    let _ ← IO.mkRef BInverse.CONT_INJ_LEMMA
    (HolLibrary.Analysis.setupUniform (deps ()) BReals1 BReals2 BReals3 BPow BSums BSeqs BSeries1 BSeries2 BLims BDiffs BCont BMvt).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Compat
unsafe def dest_neg_imp := BCompat.dest_neg_imp
unsafe def CONV_OF_RCONV := BCompat.CONV_OF_RCONV
unsafe def CONV_OF_THM := BCompat.CONV_OF_THM
unsafe def X_FUN_EQ_CONV := BCompat.X_FUN_EQ_CONV
unsafe def FUN_EQ_CONV : HolCore.Equal.ioconv := fun t => BCompat.FUN_EQ_CONV t
unsafe def SINGLE_DEPTH_CONV := BCompat.SINGLE_DEPTH_CONV
unsafe def OLD_SKOLEM_CONV : HolCore.Equal.ioconv := fun t => BCompat.OLD_SKOLEM_CONV t
unsafe def X_SKOLEM_CONV := BCompat.X_SKOLEM_CONV
unsafe def EXISTS_UNIQUE_CONV : HolCore.Equal.ioconv := fun t => BCompat.EXISTS_UNIQUE_CONV t
unsafe def NOT_FORALL_CONV : HolCore.Equal.ioconv := fun t => BCompat.NOT_FORALL_CONV t
unsafe def NOT_EXISTS_CONV : HolCore.Equal.ioconv := fun t => BCompat.NOT_EXISTS_CONV t
unsafe def RIGHT_IMP_EXISTS_CONV : HolCore.Equal.ioconv := fun t => BCompat.RIGHT_IMP_EXISTS_CONV t
unsafe def FORALL_IMP_CONV : HolCore.Equal.ioconv := fun t => BCompat.FORALL_IMP_CONV t
unsafe def EXISTS_AND_CONV : HolCore.Equal.ioconv := fun t => BCompat.EXISTS_AND_CONV t
unsafe def LEFT_IMP_EXISTS_CONV : HolCore.Equal.ioconv := fun t => BCompat.LEFT_IMP_EXISTS_CONV t
unsafe def LEFT_AND_EXISTS_CONV : HolCore.Equal.ioconv := fun t => BCompat.LEFT_AND_EXISTS_CONV t
unsafe def RIGHT_AND_EXISTS_CONV : HolCore.Equal.ioconv := fun t => BCompat.RIGHT_AND_EXISTS_CONV t
unsafe def AND_FORALL_CONV : HolCore.Equal.ioconv := fun t => BCompat.AND_FORALL_CONV t
unsafe def F_IMP : thm := BCompat.F_IMP
unsafe def LEFT_AND_OVER_OR : thm := BCompat.LEFT_AND_OVER_OR
unsafe def RIGHT_AND_OVER_OR : thm := BCompat.RIGHT_AND_OVER_OR
unsafe def INST_TY_TERM := BCompat.INST_TY_TERM
unsafe def NOT_MP := BCompat.NOT_MP
unsafe def MK_ABS := BCompat.MK_ABS
unsafe def HALF_MK_ABS := BCompat.HALF_MK_ABS
unsafe def SUBST := BCompat.SUBST

-- Names
unsafe def LESS_EQUAL_ANTISYM : thm := BNames.LESS_EQUAL_ANTISYM
unsafe def NOT_LESS_0 : thm := BNames.NOT_LESS_0
unsafe def LESS_LEMMA1 : thm := BNames.LESS_LEMMA1
unsafe def LESS_SUC_REFL : thm := BNames.LESS_SUC_REFL
unsafe def LESS_EQ_SUC_REFL : thm := BNames.LESS_EQ_SUC_REFL
unsafe def LESS_EQUAL_ADD : thm := BNames.LESS_EQUAL_ADD
unsafe def LESS_EQ_IMP_LESS_SUC : thm := BNames.LESS_EQ_IMP_LESS_SUC
unsafe def LESS_MONO_ADD : thm := BNames.LESS_MONO_ADD
unsafe def LESS_SUC : thm := BNames.LESS_SUC
unsafe def LESS_ADD_1 : thm := BNames.LESS_ADD_1
unsafe def SUC_SUB1 : thm := BNames.SUC_SUB1
unsafe def LESS_ADD_SUC : thm := BNames.LESS_ADD_SUC
unsafe def OR_LESS : thm := BNames.OR_LESS
unsafe def NOT_SUC_LESS_EQ : thm := BNames.NOT_SUC_LESS_EQ
unsafe def LESS_LESS_CASES : thm := BNames.LESS_LESS_CASES
unsafe def SUB_SUB : thm := BNames.SUB_SUB
unsafe def LESS_CASES_IMP : thm := BNames.LESS_CASES_IMP
unsafe def SUB_LESS_EQ : thm := BNames.SUB_LESS_EQ
unsafe def SUB_EQ_EQ_0 : thm := BNames.SUB_EQ_EQ_0
unsafe def SUB_LEFT_LESS_EQ : thm := BNames.SUB_LEFT_LESS_EQ
unsafe def SUB_LEFT_GREATER_EQ : thm := BNames.SUB_LEFT_GREATER_EQ
unsafe def LESS_0_CASES : thm := BNames.LESS_0_CASES
unsafe def LESS_OR : thm := BNames.LESS_OR
unsafe def SUB_OLD : thm := BNames.SUB_OLD

-- Tactics
unsafe def SYM_CANON_CONV := BTactics.SYM_CANON_CONV
unsafe def IMP_SUBST_TAC := BTactics.IMP_SUBST_TAC
unsafe def EXT_CONV : term → IO (Except String thm) := fun t => (BTactics.EXT_CONV t).run
unsafe def EQUAL_TAC : HolCore.Tactics.tactic := fun g => BTactics.EQUAL_TAC g
unsafe def X_BETA_CONV := BTactics.X_BETA_CONV
unsafe def EXACT_CONV := BTactics.EXACT_CONV
unsafe def HABS_CONV : HolCore.Equal.ioconv := fun t => BTactics.HABS_CONV t
unsafe def EXPAND_TAC := BTactics.EXPAND_TAC

-- Reals1
unsafe def real_le : thm := BReals1.real_le
unsafe def REAL_10 : thm := BReals1.REAL_10
unsafe def REAL_LDISTRIB : thm := BReals1.REAL_LDISTRIB
unsafe def REAL_LT_IADD : thm := BReals1.REAL_LT_IADD
unsafe def REAL_MUL_RID : thm := BReals1.REAL_MUL_RID
unsafe def REAL_MUL_RINV : thm := BReals1.REAL_MUL_RINV
unsafe def REAL_RDISTRIB : thm := BReals1.REAL_RDISTRIB
unsafe def REAL_EQ_LADD : thm := BReals1.REAL_EQ_LADD
unsafe def REAL_EQ_RADD : thm := BReals1.REAL_EQ_RADD
unsafe def REAL_ADD_LID_UNIQ : thm := BReals1.REAL_ADD_LID_UNIQ
unsafe def REAL_ADD_RID_UNIQ : thm := BReals1.REAL_ADD_RID_UNIQ
unsafe def REAL_LNEG_UNIQ : thm := BReals1.REAL_LNEG_UNIQ
unsafe def REAL_RNEG_UNIQ : thm := BReals1.REAL_RNEG_UNIQ
unsafe def REAL_NEG_ADD : thm := BReals1.REAL_NEG_ADD
unsafe def REAL_MUL_LZERO : thm := BReals1.REAL_MUL_LZERO
unsafe def REAL_MUL_RZERO : thm := BReals1.REAL_MUL_RZERO
unsafe def REAL_NEG_LMUL : thm := BReals1.REAL_NEG_LMUL
unsafe def REAL_NEG_RMUL : thm := BReals1.REAL_NEG_RMUL
unsafe def REAL_NEG_NEG : thm := BReals1.REAL_NEG_NEG
unsafe def REAL_NEG_MUL2 : thm := BReals1.REAL_NEG_MUL2
unsafe def REAL_LT_LADD : thm := BReals1.REAL_LT_LADD
unsafe def REAL_LT_RADD : thm := BReals1.REAL_LT_RADD
unsafe def REAL_NOT_LT : thm := BReals1.REAL_NOT_LT
unsafe def REAL_LT_ANTISYM : thm := BReals1.REAL_LT_ANTISYM
unsafe def REAL_LT_GT : thm := BReals1.REAL_LT_GT
unsafe def REAL_NOT_LE : thm := BReals1.REAL_NOT_LE
unsafe def REAL_LE_TOTAL : thm := BReals1.REAL_LE_TOTAL
unsafe def REAL_LE_REFL : thm := BReals1.REAL_LE_REFL
unsafe def REAL_LE_LT : thm := BReals1.REAL_LE_LT
unsafe def REAL_LT_LE : thm := BReals1.REAL_LT_LE
unsafe def REAL_LT_IMP_LE : thm := BReals1.REAL_LT_IMP_LE
unsafe def REAL_LTE_TRANS : thm := BReals1.REAL_LTE_TRANS
unsafe def REAL_LE_TRANS : thm := BReals1.REAL_LE_TRANS
unsafe def REAL_NEG_LT0 : thm := BReals1.REAL_NEG_LT0
unsafe def REAL_NEG_GT0 : thm := BReals1.REAL_NEG_GT0
unsafe def REAL_NEG_LE0 : thm := BReals1.REAL_NEG_LE0
unsafe def REAL_NEG_GE0 : thm := BReals1.REAL_NEG_GE0
unsafe def REAL_LT_NEGTOTAL : thm := BReals1.REAL_LT_NEGTOTAL
unsafe def REAL_LE_NEGTOTAL : thm := BReals1.REAL_LE_NEGTOTAL
unsafe def REAL_LE_MUL : thm := BReals1.REAL_LE_MUL
unsafe def REAL_LE_SQUARE : thm := BReals1.REAL_LE_SQUARE
unsafe def REAL_LT_01 : thm := BReals1.REAL_LT_01
unsafe def REAL_LE_LADD : thm := BReals1.REAL_LE_LADD
unsafe def REAL_LE_RADD : thm := BReals1.REAL_LE_RADD
unsafe def REAL_LT_ADD2 : thm := BReals1.REAL_LT_ADD2
unsafe def REAL_LT_ADD : thm := BReals1.REAL_LT_ADD
unsafe def REAL_LT_ADDNEG : thm := BReals1.REAL_LT_ADDNEG
unsafe def REAL_LT_ADDNEG2 : thm := BReals1.REAL_LT_ADDNEG2
unsafe def REAL_LT_ADD1 : thm := BReals1.REAL_LT_ADD1
unsafe def REAL_SUB_ADD : thm := BReals1.REAL_SUB_ADD
unsafe def REAL_SUB_ADD2 : thm := BReals1.REAL_SUB_ADD2

-- Reals2
unsafe def REAL_SUB_REFL : thm := BReals2.REAL_SUB_REFL
unsafe def REAL_SUB_0 : thm := BReals2.REAL_SUB_0
unsafe def REAL_LE_DOUBLE : thm := BReals2.REAL_LE_DOUBLE
unsafe def REAL_LE_NEGL : thm := BReals2.REAL_LE_NEGL
unsafe def REAL_LE_NEGR : thm := BReals2.REAL_LE_NEGR
unsafe def REAL_NEG_EQ0 : thm := BReals2.REAL_NEG_EQ0
unsafe def REAL_NEG_0 : thm := BReals2.REAL_NEG_0
unsafe def REAL_NEG_SUB : thm := BReals2.REAL_NEG_SUB
unsafe def REAL_SUB_LT : thm := BReals2.REAL_SUB_LT
unsafe def REAL_SUB_LE : thm := BReals2.REAL_SUB_LE
unsafe def REAL_EQ_LMUL : thm := BReals2.REAL_EQ_LMUL
unsafe def REAL_EQ_RMUL : thm := BReals2.REAL_EQ_RMUL
unsafe def REAL_SUB_LDISTRIB : thm := BReals2.REAL_SUB_LDISTRIB
unsafe def REAL_SUB_RDISTRIB : thm := BReals2.REAL_SUB_RDISTRIB
unsafe def REAL_NEG_EQ : thm := BReals2.REAL_NEG_EQ
unsafe def REAL_NEG_MINUS1 : thm := BReals2.REAL_NEG_MINUS1
unsafe def REAL_INV_NZ : thm := BReals2.REAL_INV_NZ
unsafe def REAL_INVINV : thm := BReals2.REAL_INVINV
unsafe def REAL_LT_IMP_NE : thm := BReals2.REAL_LT_IMP_NE
unsafe def REAL_INV_POS : thm := BReals2.REAL_INV_POS
unsafe def REAL_LT_LMUL_0 : thm := BReals2.REAL_LT_LMUL_0
unsafe def REAL_LT_RMUL_0 : thm := BReals2.REAL_LT_RMUL_0
unsafe def REAL_LT_LMUL_EQ : thm := BReals2.REAL_LT_LMUL_EQ
unsafe def REAL_LT_RMUL_EQ : thm := BReals2.REAL_LT_RMUL_EQ
unsafe def REAL_LT_RMUL_IMP : thm := BReals2.REAL_LT_RMUL_IMP
unsafe def REAL_LT_LMUL_IMP : thm := BReals2.REAL_LT_LMUL_IMP
unsafe def REAL_LINV_UNIQ : thm := BReals2.REAL_LINV_UNIQ
unsafe def REAL_RINV_UNIQ : thm := BReals2.REAL_RINV_UNIQ
unsafe def REAL_NEG_INV : thm := BReals2.REAL_NEG_INV
unsafe def REAL_INV_1OVER : thm := BReals2.REAL_INV_1OVER
unsafe def REAL : thm := BReals2.REAL
unsafe def REAL_POS : thm := BReals2.REAL_POS
unsafe def REAL_LE : thm := BReals2.REAL_LE
unsafe def REAL_LT : thm := BReals2.REAL_LT
unsafe def REAL_INJ : thm := BReals2.REAL_INJ
unsafe def REAL_ADD : thm := BReals2.REAL_ADD
unsafe def REAL_MUL : thm := BReals2.REAL_MUL
unsafe def REAL_INV1 : thm := BReals2.REAL_INV1
unsafe def REAL_DIV_LZERO : thm := BReals2.REAL_DIV_LZERO
unsafe def REAL_LT_NZ : thm := BReals2.REAL_LT_NZ
unsafe def REAL_NZ_IMP_LT : thm := BReals2.REAL_NZ_IMP_LT
unsafe def REAL_LT_RDIV_0 : thm := BReals2.REAL_LT_RDIV_0
unsafe def REAL_LT_RDIV : thm := BReals2.REAL_LT_RDIV
unsafe def REAL_LT_FRACTION_0 : thm := BReals2.REAL_LT_FRACTION_0
unsafe def REAL_LT_MULTIPLE : thm := BReals2.REAL_LT_MULTIPLE
unsafe def REAL_LT_FRACTION : thm := BReals2.REAL_LT_FRACTION
unsafe def REAL_LT_HALF1 : thm := BReals2.REAL_LT_HALF1
unsafe def REAL_LT_HALF2 : thm := BReals2.REAL_LT_HALF2
unsafe def REAL_DOUBLE : thm := BReals2.REAL_DOUBLE

-- Reals3
unsafe def REAL_HALF_DOUBLE : thm := BReals3.REAL_HALF_DOUBLE
unsafe def REAL_SUB_SUB : thm := BReals3.REAL_SUB_SUB
unsafe def REAL_LT_ADD_SUB : thm := BReals3.REAL_LT_ADD_SUB
unsafe def REAL_LT_SUB_RADD : thm := BReals3.REAL_LT_SUB_RADD
unsafe def REAL_LT_SUB_LADD : thm := BReals3.REAL_LT_SUB_LADD
unsafe def REAL_LE_SUB_LADD : thm := BReals3.REAL_LE_SUB_LADD
unsafe def REAL_LE_SUB_RADD : thm := BReals3.REAL_LE_SUB_RADD
unsafe def REAL_LT_NEG2 : thm := BReals3.REAL_LT_NEG2
unsafe def REAL_LE_NEG2 : thm := BReals3.REAL_LE_NEG2
unsafe def REAL_SUB_LZERO : thm := BReals3.REAL_SUB_LZERO
unsafe def REAL_SUB_RZERO : thm := BReals3.REAL_SUB_RZERO
unsafe def REAL_LTE_ADD2 : thm := BReals3.REAL_LTE_ADD2
unsafe def REAL_LTE_ADD : thm := BReals3.REAL_LTE_ADD
unsafe def REAL_LT_MUL2_ALT : thm := BReals3.REAL_LT_MUL2_ALT
unsafe def REAL_SUB_LNEG : thm := BReals3.REAL_SUB_LNEG
unsafe def REAL_SUB_RNEG : thm := BReals3.REAL_SUB_RNEG
unsafe def REAL_SUB_NEG2 : thm := BReals3.REAL_SUB_NEG2
unsafe def REAL_SUB_TRIANGLE : thm := BReals3.REAL_SUB_TRIANGLE
unsafe def REAL_INV_MUL_WEAK : thm := BReals3.REAL_INV_MUL_WEAK
unsafe def REAL_LE_LMUL_LOCAL : thm := BReals3.REAL_LE_LMUL_LOCAL
unsafe def REAL_LE_RMUL_EQ : thm := BReals3.REAL_LE_RMUL_EQ
unsafe def REAL_SUB_INV2 : thm := BReals3.REAL_SUB_INV2
unsafe def REAL_SUB_SUB2 : thm := BReals3.REAL_SUB_SUB2
unsafe def REAL_MEAN : thm := BReals3.REAL_MEAN
unsafe def REAL_EQ_LMUL2 : thm := BReals3.REAL_EQ_LMUL2
unsafe def REAL_LE_MUL2V : thm := BReals3.REAL_LE_MUL2V
unsafe def REAL_LE_LDIV : thm := BReals3.REAL_LE_LDIV
unsafe def REAL_LE_RDIV : thm := BReals3.REAL_LE_RDIV
unsafe def REAL_LT_1 : thm := BReals3.REAL_LT_1
unsafe def REAL_LE_LMUL_IMP : thm := BReals3.REAL_LE_LMUL_IMP
unsafe def REAL_LE_RMUL_IMP : thm := BReals3.REAL_LE_RMUL_IMP
unsafe def REAL_INV_LT1 : thm := BReals3.REAL_INV_LT1
unsafe def REAL_LT_IMP_NZ : thm := BReals3.REAL_LT_IMP_NZ
unsafe def REAL_EQ_RMUL_IMP : thm := BReals3.REAL_EQ_RMUL_IMP
unsafe def REAL_EQ_LMUL_IMP : thm := BReals3.REAL_EQ_LMUL_IMP
unsafe def REAL_FACT_NZ : thm := BReals3.REAL_FACT_NZ
unsafe def REAL_POSSQ : thm := BReals3.REAL_POSSQ
unsafe def REAL_SUMSQ : thm := BReals3.REAL_SUMSQ
unsafe def REAL_EQ_NEG : thm := BReals3.REAL_EQ_NEG
unsafe def REAL_DIV_MUL2 : thm := BReals3.REAL_DIV_MUL2
unsafe def REAL_MIDDLE1 : thm := BReals3.REAL_MIDDLE1
unsafe def REAL_MIDDLE2 : thm := BReals3.REAL_MIDDLE2

-- Abs
unsafe def ABS_ZERO : thm := BAbs.ABS_ZERO
unsafe def ABS_0 : thm := BAbs.ABS_0
unsafe def ABS_1 : thm := BAbs.ABS_1
unsafe def ABS_NEG : thm := BAbs.ABS_NEG
unsafe def ABS_TRIANGLE : thm := BAbs.ABS_TRIANGLE
unsafe def ABS_POS : thm := BAbs.ABS_POS
unsafe def ABS_MUL : thm := BAbs.ABS_MUL
unsafe def ABS_LT_MUL2 : thm := BAbs.ABS_LT_MUL2
unsafe def ABS_SUB : thm := BAbs.ABS_SUB
unsafe def ABS_NZ : thm := BAbs.ABS_NZ
unsafe def ABS_INV : thm := BAbs.ABS_INV
unsafe def ABS_ABS : thm := BAbs.ABS_ABS
unsafe def ABS_LE : thm := BAbs.ABS_LE
unsafe def ABS_REFL : thm := BAbs.ABS_REFL
unsafe def ABS_N : thm := BAbs.ABS_N
unsafe def ABS_BETWEEN : thm := BAbs.ABS_BETWEEN
unsafe def ABS_BOUND : thm := BAbs.ABS_BOUND
unsafe def ABS_STILLNZ : thm := BAbs.ABS_STILLNZ
unsafe def ABS_CASES : thm := BAbs.ABS_CASES
unsafe def ABS_BETWEEN1 : thm := BAbs.ABS_BETWEEN1
unsafe def ABS_SIGN : thm := BAbs.ABS_SIGN
unsafe def ABS_SIGN2 : thm := BAbs.ABS_SIGN2
unsafe def ABS_DIV : thm := BAbs.ABS_DIV
unsafe def ABS_CIRCLE : thm := BAbs.ABS_CIRCLE
unsafe def REAL_SUB_ABS : thm := BAbs.REAL_SUB_ABS
unsafe def ABS_SUB_ABS : thm := BAbs.ABS_SUB_ABS
unsafe def ABS_BETWEEN2 : thm := BAbs.ABS_BETWEEN2
unsafe def ABS_BOUNDS : thm := BAbs.ABS_BOUNDS

-- Pow
unsafe def pow : thm := BPow.pow
unsafe def POW_0 : thm := BPow.POW_0
unsafe def POW_NZ : thm := BPow.POW_NZ
unsafe def POW_INV : thm := BPow.POW_INV
unsafe def POW_ABS : thm := BPow.POW_ABS
unsafe def POW_PLUS1 : thm := BPow.POW_PLUS1
unsafe def POW_ADD : thm := BPow.POW_ADD
unsafe def POW_1 : thm := BPow.POW_1
unsafe def POW_2 : thm := BPow.POW_2
unsafe def POW_POS : thm := BPow.POW_POS
unsafe def POW_LE : thm := BPow.POW_LE
unsafe def POW_M1 : thm := BPow.POW_M1
unsafe def POW_MUL : thm := BPow.POW_MUL
unsafe def REAL_LE_SQUARE_POW : thm := BPow.REAL_LE_SQUARE_POW
unsafe def ABS_POW2 : thm := BPow.ABS_POW2
unsafe def REAL_LE1_POW2 : thm := BPow.REAL_LE1_POW2
unsafe def REAL_LT1_POW2 : thm := BPow.REAL_LT1_POW2
unsafe def POW_POS_LT : thm := BPow.POW_POS_LT
unsafe def POW_2_LE1 : thm := BPow.POW_2_LE1
unsafe def POW_2_LT : thm := BPow.POW_2_LT
unsafe def POW_MINUS1 : thm := BPow.POW_MINUS1
unsafe def REAL_SUP_EXISTS : thm := BPow.REAL_SUP_EXISTS
unsafe def sup_def : thm := BPow.sup_def
unsafe def sup : thm := BPow.sup
unsafe def REAL_SUP : thm := BPow.REAL_SUP
unsafe def REAL_SUP_UBOUND : thm := BPow.REAL_SUP_UBOUND
unsafe def SETOK_LE_LT : thm := BPow.SETOK_LE_LT
unsafe def REAL_SUP_LE : thm := BPow.REAL_SUP_LE
unsafe def REAL_SUP_UBOUND_LE : thm := BPow.REAL_SUP_UBOUND_LE
unsafe def REAL_ARCH_SIMPLE : thm := BPow.REAL_ARCH_SIMPLE
unsafe def REAL_ARCH : thm := BPow.REAL_ARCH
unsafe def REAL_ARCH_LEAST : thm := BPow.REAL_ARCH_LEAST
unsafe def REAL_POW_LBOUND : thm := BPow.REAL_POW_LBOUND
unsafe def REAL_ARCH_POW : thm := BPow.REAL_ARCH_POW
unsafe def REAL_ARCH_POW2 : thm := BPow.REAL_ARCH_POW2

-- Sums
unsafe def sum_EXISTS : thm := BSums.sum_EXISTS
unsafe def sum_DEF : thm := BSums.sum_DEF
unsafe def sum : thm := BSums.sum
unsafe def PSUM_SUM : thm := BSums.PSUM_SUM
unsafe def PSUM_SUM_NUMSEG : thm := BSums.PSUM_SUM_NUMSEG
unsafe def SUM_TWO : thm := BSums.SUM_TWO
unsafe def SUM_DIFF : thm := BSums.SUM_DIFF
unsafe def ABS_SUM : thm := BSums.ABS_SUM
unsafe def SUM_LE : thm := BSums.SUM_LE
unsafe def SUM_EQ : thm := BSums.SUM_EQ
unsafe def SUM_POS : thm := BSums.SUM_POS
unsafe def SUM_POS_GEN : thm := BSums.SUM_POS_GEN
unsafe def SUM_ABS : thm := BSums.SUM_ABS
unsafe def SUM_ABS_LE : thm := BSums.SUM_ABS_LE
unsafe def SUM_ZERO : thm := BSums.SUM_ZERO
unsafe def SUM_ADD : thm := BSums.SUM_ADD
unsafe def SUM_CMUL : thm := BSums.SUM_CMUL
unsafe def SUM_NEG : thm := BSums.SUM_NEG
unsafe def SUM_SUB : thm := BSums.SUM_SUB
unsafe def SUM_SUBST : thm := BSums.SUM_SUBST
unsafe def SUM_NSUB : thm := BSums.SUM_NSUB
unsafe def SUM_BOUND : thm := BSums.SUM_BOUND
unsafe def SUM_GROUP : thm := BSums.SUM_GROUP
unsafe def SUM_1 : thm := BSums.SUM_1
unsafe def SUM_2 : thm := BSums.SUM_2
unsafe def SUM_OFFSET : thm := BSums.SUM_OFFSET
unsafe def SUM_REINDEX : thm := BSums.SUM_REINDEX
unsafe def SUM_0 : thm := BSums.SUM_0
unsafe def SUM_CANCEL : thm := BSums.SUM_CANCEL
unsafe def SUM_HORNER : thm := BSums.SUM_HORNER
unsafe def SUM_CONST : thm := BSums.SUM_CONST
unsafe def SUM_SPLIT : thm := BSums.SUM_SPLIT
unsafe def SUM_SWAP : thm := BSums.SUM_SWAP
unsafe def SUM_EQ_0 : thm := BSums.SUM_EQ_0
unsafe def SUM_MORETERMS_EQ : thm := BSums.SUM_MORETERMS_EQ
unsafe def SUM_DIFFERENCES_EQ : thm := BSums.SUM_DIFFERENCES_EQ

-- SumConv
unsafe def REAL_SUM_CONV : HolCore.Equal.ioconv := fun t => BSumConv.REAL_SUM_CONV t
unsafe def REAL_HORNER_SUM_CONV : HolCore.Equal.ioconv := fun t => BSumConv.REAL_HORNER_SUM_CONV t

-- Topology
unsafe def re_Union : thm := BTopology.re_Union
unsafe def re_union : thm := BTopology.re_union
unsafe def re_intersect : thm := BTopology.re_intersect
unsafe def re_null : thm := BTopology.re_null
unsafe def re_universe : thm := BTopology.re_universe
unsafe def re_subset : thm := BTopology.re_subset
unsafe def re_compl : thm := BTopology.re_compl
unsafe def SUBSETA_REFL : thm := BTopology.SUBSETA_REFL
unsafe def COMPL_MEM : thm := BTopology.COMPL_MEM
unsafe def SUBSETA_ANTISYM : thm := BTopology.SUBSETA_ANTISYM
unsafe def SUBSETA_TRANS : thm := BTopology.SUBSETA_TRANS
unsafe def istopology : thm := BTopology.istopology
unsafe def topology_tybij : thm := BTopology.topology_tybij
unsafe def TOPOLOGY : thm := BTopology.TOPOLOGY
unsafe def TOPOLOGY_UNION : thm := BTopology.TOPOLOGY_UNION
unsafe def neigh : thm := BTopology.neigh
unsafe def OPEN_OWN_NEIGH : thm := BTopology.OPEN_OWN_NEIGH
unsafe def OPEN_UNOPEN : thm := BTopology.OPEN_UNOPEN
unsafe def OPEN_SUBOPEN : thm := BTopology.OPEN_SUBOPEN
unsafe def OPEN_NEIGH : thm := BTopology.OPEN_NEIGH
unsafe def closed : thm := BTopology.closed
unsafe def limpt : thm := BTopology.limpt
unsafe def CLOSED_LIMPT : thm := BTopology.CLOSED_LIMPT
unsafe def ismet : thm := BTopology.ismet
unsafe def metric_tybij : thm := BTopology.metric_tybij
unsafe def METRIC_ISMET : thm := BTopology.METRIC_ISMET
unsafe def METRIC_ZERO : thm := BTopology.METRIC_ZERO
unsafe def METRIC_SAME : thm := BTopology.METRIC_SAME
unsafe def METRIC_POS : thm := BTopology.METRIC_POS
unsafe def METRIC_SYM : thm := BTopology.METRIC_SYM
unsafe def METRIC_TRIANGLE : thm := BTopology.METRIC_TRIANGLE
unsafe def METRIC_NZ : thm := BTopology.METRIC_NZ

-- MetricTop
unsafe def mtop : thm := BMetricTop.mtop
unsafe def mtop_istopology : thm := BMetricTop.mtop_istopology
unsafe def MTOP_OPEN : thm := BMetricTop.MTOP_OPEN
unsafe def ball : thm := BMetricTop.ball
unsafe def BALL_OPEN : thm := BMetricTop.BALL_OPEN
unsafe def BALL_NEIGH : thm := BMetricTop.BALL_NEIGH
unsafe def MTOP_LIMPT : thm := BMetricTop.MTOP_LIMPT
unsafe def ISMET_R1 : thm := BMetricTop.ISMET_R1
unsafe def mr1 : thm := BMetricTop.mr1
unsafe def MR1_DEF : thm := BMetricTop.MR1_DEF
unsafe def MR1_ADD : thm := BMetricTop.MR1_ADD
unsafe def MR1_SUB : thm := BMetricTop.MR1_SUB
unsafe def MR1_ADD_LE : thm := BMetricTop.MR1_ADD_LE
unsafe def MR1_SUB_LE : thm := BMetricTop.MR1_SUB_LE
unsafe def MR1_ADD_LT : thm := BMetricTop.MR1_ADD_LT
unsafe def MR1_SUB_LT : thm := BMetricTop.MR1_SUB_LT
unsafe def MR1_BETWEEN1 : thm := BMetricTop.MR1_BETWEEN1
unsafe def MR1_LIMPT : thm := BMetricTop.MR1_LIMPT

-- Nets
unsafe def dorder : thm := BNets.dorder
unsafe def tends : thm := BNets.tends
unsafe def bounded : thm := BNets.bounded
unsafe def tendsto : thm := BNets.tendsto
unsafe def DORDER_LEMMA : thm := BNets.DORDER_LEMMA
unsafe def DORDER_THEN := BNets.DORDER_THEN
unsafe def DORDER_NGE : thm := BNets.DORDER_NGE
unsafe def DORDER_TENDSTO : thm := BNets.DORDER_TENDSTO
unsafe def MTOP_TENDS : thm := BNets.MTOP_TENDS
unsafe def MTOP_TENDS_UNIQ : thm := BNets.MTOP_TENDS_UNIQ
unsafe def SEQ_TENDS : thm := BNets.SEQ_TENDS
unsafe def LIM_TENDS : thm := BNets.LIM_TENDS
unsafe def LIM_TENDS2 : thm := BNets.LIM_TENDS2
unsafe def MR1_BOUNDED : thm := BNets.MR1_BOUNDED
unsafe def NET_NULL : thm := BNets.NET_NULL
unsafe def NET_CONV_BOUNDED : thm := BNets.NET_CONV_BOUNDED
unsafe def NET_CONV_NZ : thm := BNets.NET_CONV_NZ
unsafe def NET_CONV_IBOUNDED : thm := BNets.NET_CONV_IBOUNDED

-- NetArith
unsafe def NET_NULL_ADD : thm := BNetArith.NET_NULL_ADD
unsafe def NET_NULL_MUL : thm := BNetArith.NET_NULL_MUL
unsafe def NET_NULL_CMUL : thm := BNetArith.NET_NULL_CMUL
unsafe def NET_ADD : thm := BNetArith.NET_ADD
unsafe def NET_NEG : thm := BNetArith.NET_NEG
unsafe def NET_SUB : thm := BNetArith.NET_SUB
unsafe def NET_MUL : thm := BNetArith.NET_MUL
unsafe def NET_INV : thm := BNetArith.NET_INV
unsafe def NET_DIV : thm := BNetArith.NET_DIV
unsafe def NET_ABS : thm := BNetArith.NET_ABS
unsafe def NET_SUM : thm := BNetArith.NET_SUM
unsafe def NET_LE : thm := BNetArith.NET_LE

-- Seqs
unsafe def tends_num_real : thm := BSeqs.tends_num_real
unsafe def SEQ : thm := BSeqs.SEQ
unsafe def SEQ_CONST : thm := BSeqs.SEQ_CONST
unsafe def SEQ_ADD : thm := BSeqs.SEQ_ADD
unsafe def SEQ_MUL : thm := BSeqs.SEQ_MUL
unsafe def SEQ_NEG : thm := BSeqs.SEQ_NEG
unsafe def SEQ_INV : thm := BSeqs.SEQ_INV
unsafe def SEQ_SUB : thm := BSeqs.SEQ_SUB
unsafe def SEQ_DIV : thm := BSeqs.SEQ_DIV
unsafe def SEQ_UNIQ : thm := BSeqs.SEQ_UNIQ
unsafe def SEQ_NULL : thm := BSeqs.SEQ_NULL
unsafe def SEQ_SUM : thm := BSeqs.SEQ_SUM
unsafe def SEQ_TRANSFORM : thm := BSeqs.SEQ_TRANSFORM
unsafe def convergent : thm := BSeqs.convergent
unsafe def cauchy : thm := BSeqs.cauchy
unsafe def lim : thm := BSeqs.lim
unsafe def SEQ_LIM : thm := BSeqs.SEQ_LIM
unsafe def subseq : thm := BSeqs.subseq
unsafe def SUBSEQ_SUC : thm := BSeqs.SUBSEQ_SUC
unsafe def mono : thm := BSeqs.mono
unsafe def MONO_SUC : thm := BSeqs.MONO_SUC
unsafe def MAX_LEMMA : thm := BSeqs.MAX_LEMMA
unsafe def SEQ_BOUNDED : thm := BSeqs.SEQ_BOUNDED
unsafe def SEQ_BOUNDED_2 : thm := BSeqs.SEQ_BOUNDED_2
unsafe def SEQ_CBOUNDED : thm := BSeqs.SEQ_CBOUNDED
unsafe def SEQ_ICONV : thm := BSeqs.SEQ_ICONV

-- Seqs2
unsafe def SEQ_NEG_CONV : thm := BSeqs2.SEQ_NEG_CONV
unsafe def SEQ_NEG_BOUNDED : thm := BSeqs2.SEQ_NEG_BOUNDED
unsafe def SEQ_BCONV : thm := BSeqs2.SEQ_BCONV
unsafe def SEQ_MONOSUB : thm := BSeqs2.SEQ_MONOSUB
unsafe def SEQ_SBOUNDED : thm := BSeqs2.SEQ_SBOUNDED
unsafe def SEQ_SUBLE : thm := BSeqs2.SEQ_SUBLE
unsafe def SEQ_DIRECT : thm := BSeqs2.SEQ_DIRECT
unsafe def SEQ_CAUCHY : thm := BSeqs2.SEQ_CAUCHY
unsafe def SEQ_LE : thm := BSeqs2.SEQ_LE
unsafe def SEQ_LE_0 : thm := BSeqs2.SEQ_LE_0

-- SeqLim
unsafe def SEQ_SUC : thm := BSeqLim.SEQ_SUC
unsafe def SEQ_ABS : thm := BSeqLim.SEQ_ABS
unsafe def SEQ_ABS_IMP : thm := BSeqLim.SEQ_ABS_IMP
unsafe def SEQ_INV0 : thm := BSeqLim.SEQ_INV0
unsafe def SEQ_POWER_ABS : thm := BSeqLim.SEQ_POWER_ABS
unsafe def SEQ_POWER : thm := BSeqLim.SEQ_POWER
unsafe def SEQ_HARMONIC : thm := BSeqLim.SEQ_HARMONIC
unsafe def SEQ_SUBSEQ : thm := BSeqLim.SEQ_SUBSEQ
unsafe def SEQ_POW : thm := BSeqLim.SEQ_POW
unsafe def NEST_LEMMA : thm := BSeqLim.NEST_LEMMA
unsafe def NEST_LEMMA_UNIQ : thm := BSeqLim.NEST_LEMMA_UNIQ

-- Series1
unsafe def BOLZANO_LEMMA : thm := BSeries1.BOLZANO_LEMMA
unsafe def BOLZANO_LEMMA_ALT : thm := BSeries1.BOLZANO_LEMMA_ALT
unsafe def sums : thm := BSeries1.sums
unsafe def summable : thm := BSeries1.summable
unsafe def suminf : thm := BSeries1.suminf
unsafe def SUM_SUMMABLE : thm := BSeries1.SUM_SUMMABLE
unsafe def SUMMABLE_SUM : thm := BSeries1.SUMMABLE_SUM
unsafe def SUM_UNIQ : thm := BSeries1.SUM_UNIQ
unsafe def SER_UNIQ : thm := BSeries1.SER_UNIQ
unsafe def SER_0 : thm := BSeries1.SER_0
unsafe def SER_POS_LE : thm := BSeries1.SER_POS_LE
unsafe def SER_POS_LT : thm := BSeries1.SER_POS_LT
unsafe def SER_GROUP : thm := BSeries1.SER_GROUP
unsafe def SER_PAIR : thm := BSeries1.SER_PAIR
unsafe def SER_OFFSET : thm := BSeries1.SER_OFFSET
unsafe def SER_OFFSET_REV : thm := BSeries1.SER_OFFSET_REV

-- Series2
unsafe def SER_POS_LT_PAIR : thm := BSeries2.SER_POS_LT_PAIR
unsafe def SER_ADD : thm := BSeries2.SER_ADD
unsafe def SER_CMUL : thm := BSeries2.SER_CMUL
unsafe def SER_NEG : thm := BSeries2.SER_NEG
unsafe def SER_SUB : thm := BSeries2.SER_SUB
unsafe def SER_CDIV : thm := BSeries2.SER_CDIV
unsafe def SER_CAUCHY : thm := BSeries2.SER_CAUCHY
unsafe def SER_ZERO : thm := BSeries2.SER_ZERO
unsafe def SER_COMPAR : thm := BSeries2.SER_COMPAR
unsafe def SER_COMPARA : thm := BSeries2.SER_COMPARA
unsafe def SER_LE : thm := BSeries2.SER_LE
unsafe def SER_LE2 : thm := BSeries2.SER_LE2
unsafe def SER_ACONV : thm := BSeries2.SER_ACONV
unsafe def SER_ABS : thm := BSeries2.SER_ABS
unsafe def GP_FINITE : thm := BSeries2.GP_FINITE
unsafe def GP : thm := BSeries2.GP
unsafe def ABS_NEG_LEMMA : thm := BSeries2.ABS_NEG_LEMMA
unsafe def SER_RATIO : thm := BSeries2.SER_RATIO
unsafe def SEQ_TRUNCATION : thm := BSeries2.SEQ_TRUNCATION

-- Lims
unsafe def tends_real_real : thm := BLims.tends_real_real
unsafe def LIM : thm := BLims.LIM
unsafe def LIM_CONST : thm := BLims.LIM_CONST
unsafe def LIM_ADD : thm := BLims.LIM_ADD
unsafe def LIM_MUL : thm := BLims.LIM_MUL
unsafe def LIM_NEG : thm := BLims.LIM_NEG
unsafe def LIM_INV : thm := BLims.LIM_INV
unsafe def LIM_SUB : thm := BLims.LIM_SUB
unsafe def LIM_DIV : thm := BLims.LIM_DIV
unsafe def LIM_NULL : thm := BLims.LIM_NULL
unsafe def LIM_SUM : thm := BLims.LIM_SUM
unsafe def LIM_X : thm := BLims.LIM_X
unsafe def LIM_UNIQ : thm := BLims.LIM_UNIQ
unsafe def LIM_EQUAL : thm := BLims.LIM_EQUAL
unsafe def LIM_TRANSFORM : thm := BLims.LIM_TRANSFORM
unsafe def diffl : thm := BLims.diffl
unsafe def contl : thm := BLims.contl
unsafe def differentiable : thm := BLims.differentiable
unsafe def DIFF_UNIQ : thm := BLims.DIFF_UNIQ
unsafe def DIFF_CONT : thm := BLims.DIFF_CONT
unsafe def CONTL_LIM : thm := BLims.CONTL_LIM
unsafe def CONT_X : thm := BLims.CONT_X
unsafe def CONT_CONST : thm := BLims.CONT_CONST
unsafe def CONT_ADD : thm := BLims.CONT_ADD
unsafe def CONT_MUL : thm := BLims.CONT_MUL
unsafe def CONT_NEG : thm := BLims.CONT_NEG
unsafe def CONT_INV : thm := BLims.CONT_INV
unsafe def CONT_SUB : thm := BLims.CONT_SUB
unsafe def CONT_DIV : thm := BLims.CONT_DIV
unsafe def CONT_ABS : thm := BLims.CONT_ABS
unsafe def CONT_COMPOSE : thm := BLims.CONT_COMPOSE

-- Diffs
unsafe def IVT : thm := BDiffs.IVT
unsafe def IVT2 : thm := BDiffs.IVT2
unsafe def DIFF_CONST : thm := BDiffs.DIFF_CONST
unsafe def DIFF_ADD : thm := BDiffs.DIFF_ADD
unsafe def DIFF_MUL : thm := BDiffs.DIFF_MUL
unsafe def DIFF_CMUL : thm := BDiffs.DIFF_CMUL
unsafe def DIFF_NEG : thm := BDiffs.DIFF_NEG
unsafe def DIFF_SUB : thm := BDiffs.DIFF_SUB
unsafe def DIFF_CARAT : thm := BDiffs.DIFF_CARAT
unsafe def DIFF_CHAIN : thm := BDiffs.DIFF_CHAIN
unsafe def DIFF_X : thm := BDiffs.DIFF_X
unsafe def DIFF_POW : thm := BDiffs.DIFF_POW
unsafe def DIFF_XM1 : thm := BDiffs.DIFF_XM1
unsafe def DIFF_INV : thm := BDiffs.DIFF_INV
unsafe def DIFF_DIV : thm := BDiffs.DIFF_DIV
unsafe def DIFF_SUM : thm := BDiffs.DIFF_SUM

-- Cont
unsafe def CONT_BOUNDED : thm := BCont.CONT_BOUNDED
unsafe def CONT_BOUNDED_ABS : thm := BCont.CONT_BOUNDED_ABS
unsafe def CONT_HASSUP : thm := BCont.CONT_HASSUP
unsafe def CONT_ATTAINS : thm := BCont.CONT_ATTAINS
unsafe def CONT_ATTAINS2 : thm := BCont.CONT_ATTAINS2
unsafe def CONT_ATTAINS_ALL : thm := BCont.CONT_ATTAINS_ALL

-- Mvt
unsafe def DIFF_LINC : thm := BMvt.DIFF_LINC
unsafe def DIFF_LDEC : thm := BMvt.DIFF_LDEC
unsafe def DIFF_LMAX : thm := BMvt.DIFF_LMAX
unsafe def DIFF_LMIN : thm := BMvt.DIFF_LMIN
unsafe def DIFF_LCONST : thm := BMvt.DIFF_LCONST
unsafe def INTERVAL_LEMMA_LT : thm := BMvt.INTERVAL_LEMMA_LT
unsafe def INTERVAL_LEMMA : thm := BMvt.INTERVAL_LEMMA
unsafe def ROLLE : thm := BMvt.ROLLE
unsafe def MVT_LEMMA : thm := BMvt.MVT_LEMMA
unsafe def MVT : thm := BMvt.MVT
unsafe def MVT_ALT : thm := BMvt.MVT_ALT
unsafe def DIFF_ISCONST_END : thm := BMvt.DIFF_ISCONST_END
unsafe def DIFF_ISCONST : thm := BMvt.DIFF_ISCONST
unsafe def DIFF_ISCONST_END_SIMPLE : thm := BMvt.DIFF_ISCONST_END_SIMPLE
unsafe def DIFF_ISCONST_ALL : thm := BMvt.DIFF_ISCONST_ALL
unsafe def INTERVAL_ABS : thm := BMvt.INTERVAL_ABS

-- Inverse
unsafe def CONT_INJ_LEMMA : thm := BInverse.CONT_INJ_LEMMA
unsafe def CONT_INJ_LEMMA2 : thm := BInverse.CONT_INJ_LEMMA2
unsafe def CONT_INJ_RANGE : thm := BInverse.CONT_INJ_RANGE
unsafe def CONT_INVERSE : thm := BInverse.CONT_INVERSE
unsafe def DIFF_INVERSE : thm := BInverse.DIFF_INVERSE
unsafe def DIFF_INVERSE_LT : thm := BInverse.DIFF_INVERSE_LT

-- Uniform
unsafe def IVT_DERIVATIVE_0 : thm := BUniform.IVT_DERIVATIVE_0
unsafe def IVT_DERIVATIVE_POS : thm := BUniform.IVT_DERIVATIVE_POS
unsafe def IVT_DERIVATIVE_NEG : thm := BUniform.IVT_DERIVATIVE_NEG
unsafe def SEQ_CONT_UNIFORM : thm := BUniform.SEQ_CONT_UNIFORM
unsafe def SER_COMPARA_UNIFORM : thm := BUniform.SER_COMPARA_UNIFORM
unsafe def SER_COMPARA_UNIFORM_WEAK : thm := BUniform.SER_COMPARA_UNIFORM_WEAK
unsafe def CONTL : thm := BUniform.CONTL
unsafe def CONTL_SEQ : thm := BUniform.CONTL_SEQ
unsafe def SUP_INTERVAL : thm := BUniform.SUP_INTERVAL
unsafe def CONT_UNIFORM : thm := BUniform.CONT_UNIFORM
unsafe def CONT_UNIFORM_STRONG : thm := BUniform.CONT_UNIFORM_STRONG












































-- @@EXPORTS END

/-- `needs "Library/analysis.ml"`: build every bundle, in file order. -/
unsafe def ensureAnalysis : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BCompat.F_IMP
  let _ ← IO.mkRef BNames.LESS_EQUAL_ANTISYM
  let _ ← IO.mkRef BTactics.SYM_CANON_CONV
  let _ ← IO.mkRef BReals1.real_le
  let _ ← IO.mkRef BReals2.REAL_SUB_REFL
  let _ ← IO.mkRef BReals3.REAL_HALF_DOUBLE
  let _ ← IO.mkRef BAbs.ABS_ZERO
  let _ ← IO.mkRef BPow.pow
  let _ ← IO.mkRef BSums.sum_EXISTS
  let _ ← IO.mkRef BSumConv.REAL_SUM_CONV
  let _ ← IO.mkRef BTopology.re_Union
  let _ ← IO.mkRef BMetricTop.mtop
  let _ ← IO.mkRef BNets.dorder
  let _ ← IO.mkRef BNetArith.NET_NULL_ADD
  let _ ← IO.mkRef BSeqs.tends_num_real
  let _ ← IO.mkRef BSeqs2.SEQ_NEG_CONV
  let _ ← IO.mkRef BSeqLim.SEQ_SUC
  let _ ← IO.mkRef BSeries1.BOLZANO_LEMMA
  let _ ← IO.mkRef BSeries2.SER_POS_LT_PAIR
  let _ ← IO.mkRef BLims.tends_real_real
  let _ ← IO.mkRef BDiffs.IVT
  let _ ← IO.mkRef BCont.CONT_BOUNDED
  let _ ← IO.mkRef BMvt.DIFF_LINC
  let _ ← IO.mkRef BInverse.CONT_INJ_LEMMA
  let _ ← IO.mkRef BUniform.IVT_DERIVATIVE_0  -- @@ENSURE END
  pure ()

end SessionLibrary.Analysis
